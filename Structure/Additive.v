Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Preadditive.

Generalizable All Variables.

(** * Additive categories *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Additive_category

   本文件给出加性相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Additive (C : Category) := {
  additive_zero : @ZeroObject C;
  additive_preadditive : @Preadditive C;
  additive_biproducts : @HasBiproducts C additive_zero;

  (* Each hom-setoid upgrades from a commutative monoid to an abelian
     group: every morphism has an additive inverse. *)
  pneg {x y : C} : (x ~> y) -> (x ~> y);

  pneg_respects {x y : C} :
    Proper (equiv ==> equiv) (@pneg x y);

  padd_pneg {x y : C} (f : x ~> y) :
    padd f (pneg f) ≈ pzero
}.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Existing Instance additive_zero.
#[export] Existing Instance additive_preadditive.
#[export] Existing Instance additive_biproducts.
#[export] Existing Instance pneg_respects.

Section AdditiveLaws.

Context {C : Category}.
Context `{A : @Additive C}.

(* Negation is a left inverse as well, by commutativity of addition. *)
Lemma pneg_padd {x y : C} (f : x ~> y) :
  padd (pneg f) f ≈ pzero.
Proof.
  rewrite padd_comm.
  apply padd_pneg.
Qed.

(* 相关说明。 （已译） *)
Lemma padd_cancel_right {x y : C} (f g h : x ~> y) :
  padd f h ≈ padd g h -> f ≈ g.
Proof.
  intros H.
  rewrite <- (padd_zero_right f).
  rewrite <- (padd_pneg h).
  rewrite <- padd_assoc.
  rewrite H.
  rewrite padd_assoc.
  rewrite padd_pneg.
  apply padd_zero_right.
Qed.

(* Inverses are unique: any right inverse of f is [pneg f]. *)
Lemma pneg_unique {x y : C} (f g : x ~> y) :
  padd f g ≈ pzero -> g ≈ pneg f.
Proof.
  intros H.
  apply (padd_cancel_right _ _ f).
  rewrite pneg_padd.
  rewrite padd_comm.
  exact H.
Qed.

(* Negation is involutive, by uniqueness of inverses. *)
Lemma pneg_pneg {x y : C} (f : x ~> y) :
  pneg (pneg f) ≈ f.
Proof.
  symmetry.
  apply pneg_unique.
  apply pneg_padd.
Qed.

(* The zero morphism is its own inverse. *)
Lemma pneg_pzero {x y : C} :
  pneg (@pzero C _ x y) ≈ pzero.
Proof.
  symmetry.
  apply pneg_unique.
  apply padd_zero_left.
Qed.

(* Postcomposition commutes negation: h ∘ pneg f additive
 inverse h ∘ f, since 复合 distributes over addition and
 absorbs zero. （已译） *)
Lemma compose_pneg_left {x y z : C} (h : y ~> z) (f : x ~> y) :
  h ∘ pneg f ≈ pneg (h ∘ f).
Proof.
  apply pneg_unique.
  rewrite <- compose_padd_left.
  rewrite padd_pneg.
  apply compose_pzero_right.
Qed.

(* Precomposition commutes with negation, dually. *)
Lemma compose_pneg_right {x y z : C} (f : y ~> z) (h : x ~> y) :
  pneg f ∘ h ≈ pneg (f ∘ h).
Proof.
  apply pneg_unique.
  rewrite <- compose_padd_right.
  rewrite padd_pneg.
  apply compose_pzero_left.
Qed.

End AdditiveLaws.

(* Subtraction parallel 态射, notation alongside `+` and
 `0` addition_scope. （已译） *)
Definition psub {C : Category} `{A : @Additive C} {x y : C}
  (f g : x ~> y) : x ~> y := padd f (pneg g).

Infix "-" := psub : addition_scope.

#[export] Instance psub_respects {C : Category} `{A : @Additive C} {x y : C} :
  Proper (equiv ==> equiv ==> equiv) (@psub C A x y).
Proof.
  intros f1 f2 Hf g1 g2 Hg.
  unfold psub.
  now rewrite Hf, Hg.
Qed.
