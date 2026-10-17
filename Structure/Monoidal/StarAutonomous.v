Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Remove Hints Sets_Product_Monoidal : typeclass_instances.

(* * * Star-autonomous 范畴 (定义 level) （已译） *)

(*
   nLab:      https://ncatlab.org/nlab/show/star-autonomous+category
   nLab:      https://ncatlab.org/nlab/show/dualizing+object
   Wikipedia: https://en.wikipedia.org/wiki/Star-autonomous_category

   本节说明幺半结构、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半结构、伴随、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SMClosed.

Context {C : Category}.

Reserved Infix "⇒" (at level 30, right associativity).

Class SymMonClosed := {
  smc_is_symmetric : @SymmetricMonoidal C;   (* the underlying ⨂-structure *)

  exponent_obj : obj → obj → obj    (* internal hom; x ⇒ y = exponent_obj x y *)
    where "x ⇒ y" := (exponent_obj x y);

  exp_iso {x y z} : x ⨂ y ~> z ≊ x ~> y ⇒ z;

  curry'   {x y z} : x ⨂ y ~> z → x ~> y ⇒ z := to (@exp_iso x y z);
  uncurry' {x y z} : x ~> y ⇒ z → x ⨂ y ~> z := from (@exp_iso x y z);

  eval' {x y} : (x ⇒ y) ⨂ x ~> y := @uncurry' _ _ _ id;

  ump_exponents' {x y z} (f : x ⨂ y ~> z) :
    ∃! h : x ~> y ⇒ z, f ≈ eval' ∘ (h ⨂ id)
}.
#[export] Existing Instance smc_is_symmetric.

Coercion smc_is_symmetric : SymMonClosed >-> SymmetricMonoidal.

Notation "x ⇒ y" := (exponent_obj x y)
  (at level 30, right associativity) : object_scope.

Context `{SymMonClosed}.

Definition ump_exponents {x y z} (f : x ⨂ y ~> z) :
  ∃! h : x ~> y ⇒ z, f ≈ eval' ∘ (h ⨂ id) := @ump_exponents' _ x y z f.

Arguments eval' {_ _ _} /.

End SMClosed.

Notation "x ⇒ y" := (exponent_obj x y)
  (at level 30, right associativity) : category_scope.

Section StarAutonomous.

Context {C : Category}.
Context `{@SymMonClosed C}.

#[local] Obligation Tactic := idtac.

(*
   本节说明 StarAutonomous 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition dcur {x y z : C} (f : x ⨂ y ~> z) : x ~> y ⇒ z :=
  unique_obj (ump_exponents f).

Lemma dcur_beta {x y z : C} (f : x ⨂ y ~> z) :
  f ≈ eval' ∘ (dcur f ⨂ id).
Proof. exact (unique_property (ump_exponents f)). Qed.

Lemma dcur_uniq {x y z : C} (f : x ⨂ y ~> z) (v : x ~> y ⇒ z) :
  f ≈ eval' ∘ (v ⨂ id) -> dcur f ≈ v.
Proof. exact (uniqueness (ump_exponents f) v). Qed.

#[local] Program Instance dcur_respects {x y z : C} :
  Proper (equiv ==> equiv) (@dcur x y z).
Next Obligation.
  proper.
  apply dcur_uniq.
  match goal with [ Heq : _ ≈ _ |- _ ] => rewrite Heq end.
  apply dcur_beta.
Qed.

(** 本节：Two bookkeeping slides tensor bifunctor, factoring joint action
 `u ⨂ v` through two one-sided actions either order. （已译） *)

Lemma bimap_slide_l {a a' b b' : C} (u : a ~> a') (v : b ~> b') :
  u ⨂ v ≈ (u ⨂ id) ∘ (id ⨂ v).
Proof.
  rewrite <- bimap_comp.
  rewrite id_left, id_right.
  reflexivity.
Qed.

Lemma bimap_slide_r {a a' b b' : C} (u : a ~> a') (v : b ~> b') :
  u ⨂ v ≈ (id ⨂ v) ∘ (u ⨂ id).
Proof.
  rewrite <- bimap_comp.
  rewrite id_left, id_right.
  reflexivity.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma dual_hom_comp (d : C) {x y z : C} (f : z ~> y) (g : y ~> x) :
  dcur (eval' ∘ (@id _ (x ⇒ d) ⨂ (g ∘ f)))
    ≈ dcur (eval' ∘ (@id _ (y ⇒ d) ⨂ f))
        ∘ dcur (eval' ∘ (@id _ (x ⇒ d) ⨂ g)).
Proof.
  apply dcur_uniq.
  transitivity (eval' ∘ (dcur (eval' ∘ (@id _ (x ⇒ d) ⨂ g)) ⨂ f)).
  - (* left leg: fold `g`'s beta law back into `id ⨂ (g ∘ f)` *)
    symmetry.
    rewrite (bimap_slide_l (dcur (eval' ∘ (@id _ (x ⇒ d) ⨂ g))) f).
    rewrite comp_assoc.
    rewrite <- (dcur_beta (eval' ∘ (@id _ (x ⇒ d) ⨂ g))).
    rewrite <- comp_assoc.
    rewrite <- bimap_comp_id_left.
    reflexivity.
  - (* right leg: fold `f`'s beta law back into `dcur (…g…) ⨂ f` *)
    rewrite (bimap_comp_id_right
               (dcur (eval' ∘ (@id _ (y ⇒ d) ⨂ f)))
               (dcur (eval' ∘ (@id _ (x ⇒ d) ⨂ g)))).
    rewrite comp_assoc.
    rewrite <- (dcur_beta (eval' ∘ (@id _ (y ⇒ d) ⨂ f))).
    rewrite <- comp_assoc.
    rewrite <- (bimap_slide_r (dcur (eval' ∘ (@id _ (x ⇒ d) ⨂ g))) f).
    reflexivity.
Qed.

Program Definition dual (d : C) : C^op ⟶ C := {|
  fobj := fun x => @exponent_obj C _ x d;
  fmap := fun x y f => dcur (eval' ∘ (id ⨂ (f : y ~{C}~> x)))
|}.
Next Obligation.
  (* fmap respects ≈ *)
  proper.
  apply dcur_respects.
  match goal with [ Heq : _ ≈ _ |- _ ] => now rewrite Heq end.
Qed.
Next Obligation.
  (* fmap preserves identities *)
  intros.
  apply dcur_uniq.
  reflexivity.
Qed.
Next Obligation.
  (* fmap preserves composition *)
  intros.
  apply dual_hom_comp.
Qed.

(** The double-dual endofunctor `(-)^*^* : C ⟶ C`. *)
Definition double_dual (d : C) : C ⟶ C := dual d ◯ (dual d)^op.

(*
   本节说明幺半结构、幺半群、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class StarAutonomous : Type := {
  dualizer : C;

  (* 相关说明。 （已译） *)
  star_transpose {x y : C} :
    (x ⨂ y ~> dualizer) ≊ (x ~> dual dualizer y);

  (* the double-dual isomorphism `x ≅ x^*^*` *)
  star_double_dual {x : C} :
    x ≅ double_dual dualizer x;

  (* naturality of the double-dual isomorphism *)
  star_natural {a b : C} (f : a ~> b) :
    to (star_double_dual (x:=b)) ∘ f
      << a ~~> double_dual dualizer b >>
    fmap[double_dual dualizer] f ∘ to (star_double_dual (x:=a))
}.

End StarAutonomous.

Arguments dcur {C _ x y z} f.
Arguments dual {C _} d.
Arguments double_dual {C _} d.
Arguments StarAutonomous C {_}.
Arguments dualizer {C _ _}.
