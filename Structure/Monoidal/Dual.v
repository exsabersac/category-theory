(* * * Dualization fixed 对象, self-adjointness right （已译） *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.StarAutonomous.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.Right.

(*
   本文件给出对偶形式。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Remove Hints Sets_Product_Monoidal : typeclass_instances.

(*
   本节说明伴随、函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Open Scope category_scope.

Generalizable All Variables.

(*
   Book:  Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Book:  Mac Lane, op. cit., §IV.2 Definition 2, printed p. 89, where
   Book:  Riehl, "Category Theory in Context", §4.4
   nLab:  https://ncatlab.org/nlab/show/star-autonomous+category
   nLab:  https://ncatlab.org/nlab/show/dualizing+object
   nLab:  https://ncatlab.org/nlab/show/mutually+left+adjoint+functors

   本节说明幺半结构、伴随、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section DualSelfAdjoint.

Context {C : Category}.
Context `{@SymMonClosed C}.
Context (d : C).

(*
   本节说明 Dual 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Instance dcur_Proper {x y z : C} :
  Proper (equiv ==> equiv) (@dcur C _ x y z).
Proof.
  intros f g Hfg; apply dcur_uniq; rewrite Hfg; apply dcur_beta.
Qed.

Definition dual_uncur {a x : C} (f : a ~> x ⇒ d) : a ⨂ x ~> d :=
  eval' ∘ (f ⨂ id).

#[local] Instance dual_uncur_Proper {a x : C} :
  Proper (equiv ==> equiv) (@dual_uncur a x).
Proof. intros f g Hfg; unfold dual_uncur; now rewrite Hfg. Qed.

Lemma dual_uncur_dcur {a x : C} (g : a ⨂ x ~> d) :
  dual_uncur (dcur g) ≈ g.
Proof. symmetry; apply dcur_beta. Qed.

Lemma dcur_dual_uncur {a x : C} (f : a ~> x ⇒ d) :
  dcur (dual_uncur f) ≈ f.
Proof. apply dcur_uniq; reflexivity. Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma dual_fmap_unfold {x x' : C} (k : x ~{C}~> x') :
  @fmap _ _ (dual d) x' x k ≈ dcur (eval' ∘ (id ⨂ k)).
Proof. reflexivity. Qed.

Lemma dual_uncur_comp {a a' x : C} (f : a ~> x ⇒ d) (g : a' ~> a) :
  dual_uncur (f ∘ g) ≈ dual_uncur f ∘ (g ⨂ id[x]).
Proof.
  unfold dual_uncur.
  rewrite bimap_comp_id_right; now rewrite comp_assoc.
Qed.

Lemma dual_uncur_dual {a x x' : C} (f : a ~> x' ⇒ d) (k : x ~{C}~> x') :
  dual_uncur (@fmap _ _ (dual d) x' x k ∘ f)
    ≈ dual_uncur f ∘ (id[a] ⨂ k).
Proof.
  unfold dual_uncur.
  transitivity (eval' ∘ (f ⨂ k)).
  - rewrite dual_fmap_unfold, bimap_comp_id_right, comp_assoc.
    rewrite <- (dcur_beta (eval' ∘ (id[x' ⇒ d] ⨂ k))).
    rewrite <- comp_assoc.
    now rewrite bimap_id_left_right.
  - rewrite <- comp_assoc. now rewrite bimap_id_right_left.
Qed.

(*
   本节说明 Dual 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition dual_transpose {a x : C} (f : a ~> x ⇒ d) : x ~> a ⇒ d :=
  dcur (dual_uncur f ∘ braid).

#[local] Instance dual_transpose_Proper {a x : C} :
  Proper (equiv ==> equiv) (@dual_transpose a x).
Proof. intros f g Hfg; unfold dual_transpose; now rewrite Hfg. Qed.

Lemma dual_uncur_transpose {a x : C} (f : a ~> x ⇒ d) :
  dual_uncur (dual_transpose f) ≈ dual_uncur f ∘ braid.
Proof. unfold dual_transpose; apply dual_uncur_dcur. Qed.

(*
   本节说明幺半结构、幺半群、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem dual_transpose_invol {a x : C} (f : a ~> x ⇒ d) :
  dual_transpose (dual_transpose f) ≈ f.
Proof.
  unfold dual_transpose at 1.
  rewrite dual_uncur_transpose, <- comp_assoc, braid_invol, id_right.
  apply dcur_dual_uncur.
Qed.

Theorem dual_transpose_nat_dom {a a' x : C}
  (f : a ~> x ⇒ d) (g : a' ~> a) :
  dual_transpose (f ∘ g)
    ≈ @fmap _ _ (dual d) a a' g ∘ dual_transpose f.
Proof.
  apply dcur_uniq.
  transitivity
    (dual_uncur (@fmap _ _ (dual d) a a' g ∘ dual_transpose f));
    [| unfold dual_uncur; reflexivity ].
  rewrite dual_uncur_dual, dual_uncur_transpose, dual_uncur_comp,
          <- !comp_assoc.
  now rewrite bimap_braid.
Qed.

Theorem dual_transpose_nat_cod {a x x' : C}
  (f : a ~> x' ⇒ d) (k : x ~{C}~> x') :
  dual_transpose (@fmap _ _ (dual d) x' x k ∘ f)
    ≈ dual_transpose f ∘ k.
Proof.
  apply dcur_uniq.
  transitivity (dual_uncur (dual_transpose f ∘ k));
    [| unfold dual_uncur; reflexivity ].
  rewrite dual_uncur_comp, dual_uncur_transpose, dual_uncur_dual,
          <- !comp_assoc.
  now rewrite bimap_braid.
Qed.

(*
   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition dual_transpose_morphism (a x : C) :
  SetoidMorphism {| carrier   := @hom C a (dual d x)
                  ; is_setoid := @homset C a (dual d x) |}
                 {| carrier   := @hom C x (dual d a)
                  ; is_setoid := @homset C x (dual d a) |} :=
  {| morphism       := @dual_transpose a x
   ; proper_morphism := @dual_transpose_Proper a x |}.

Program Definition dual_self_adjoint_on_the_right :
  @AdjointOnTheRight C C (dual d) (dual d) := {|
  aor := fun a x => {| to   := dual_transpose_morphism a x
                     ; from := dual_transpose_morphism x a |}
|}.
Next Obligation. simpl; apply dual_transpose_invol. Qed.
Next Obligation. simpl; apply dual_transpose_invol. Qed.
Next Obligation. apply dual_transpose_nat_dom. Qed.
Next Obligation. apply dual_transpose_nat_cod. Qed.
Next Obligation. apply dual_transpose_nat_cod. Qed.
Next Obligation. apply dual_transpose_nat_dom. Qed.

Notation "'DSA'" := dual_self_adjoint_on_the_right (only parsing).

(*
   本节说明 Dual 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example aor_to_is_from_swapped (a x : C) :
  to (@aor C C (dual d) (dual d) DSA a x)
    = from (@aor C C (dual d) (dual d) DSA x a) := eq_refl.

Example aor_from_is_to_swapped (a x : C) :
  from (@aor C C (dual d) (dual d) DSA a x)
    = to (@aor C C (dual d) (dual d) DSA x a) := eq_refl.

(*
   本节说明 Dual 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition dd_unit (x : C) : x ~> double_dual d x :=
  dual_transpose (@id C (x ⇒ d)).

Example double_dual_obj (x : C) :
  fobj[double_dual d] x = ((x ⇒ d) ⇒ d) := eq_refl.

Example double_dual_fmap {a b : C} (f : a ~{C}~> b) :
  @fmap _ _ (double_dual d) a b f
    = @fmap _ _ (dual d) (a ⇒ d) (b ⇒ d) (@fmap _ _ (dual d) b a f)
  := eq_refl.

Example dd_unit_is_to_at_id (x : C) :
  to (@aor C C (dual d) (dual d) DSA (x ⇒ d) x) (@id C (x ⇒ d))
    = dd_unit x := eq_refl.

Example dd_unit_is_from_at_id (x : C) :
  from (@aor C C (dual d) (dual d) DSA x (x ⇒ d)) (@id C (x ⇒ d))
    = dd_unit x := eq_refl.

(*
   本节说明 Dual 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma dd_unit_is_braid_transpose (x : C) :
  dd_unit x ≈ dcur (eval' ∘ braid).
Proof.
  unfold dd_unit, dual_transpose, dual_uncur.
  apply dcur_Proper.
  rewrite bimap_id_id, id_right.
  reflexivity.
Qed.

Theorem dd_unit_natural {a b : C} (f : a ~{C}~> b) :
  @fmap _ _ (double_dual d) a b f ∘ dd_unit a ≈ dd_unit b ∘ f.
Proof.
  unfold dd_unit.
  transitivity (dual_transpose (@fmap _ _ (dual d) b a f)).
  - rewrite <- (id_left (@fmap _ _ (dual d) b a f)) at 1.
    rewrite dual_transpose_nat_dom. reflexivity.
  - rewrite <- (id_right (@fmap _ _ (dual d) b a f)) at 1.
    rewrite dual_transpose_nat_cod. reflexivity.
Qed.

Program Definition double_dual_unit : Id[C] ⟹ double_dual d := {|
  transform := dd_unit
|}.
Next Obligation. apply dd_unit_natural. Qed.
Next Obligation. symmetry; apply dd_unit_natural. Qed.

Example double_dual_unit_component (x : C) :
  transform[double_dual_unit] x = dd_unit x := eq_refl.

(* * ** The ordinary 伴随, Mac Lane's unit counit

 Read off class Adjunction/Right.v rather than rebuilt.
 `Check` displays result `(dual d)^op ⊣ dual d`. （已译） *)

Definition dual_adjunction :
  @Adjunction (C^op) C (Opposite_Functor (dual d)) (dual d) :=
  Adjunction_of_AdjointOnTheRight DSA.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example unit_is_dd_unit (x : C) :
  @unit (C^op) C (Opposite_Functor (dual d)) (dual d) dual_adjunction x
    = dd_unit x := eq_refl.

Example counit_is_dd_unit (x : C) :
  @counit (C^op) C (Opposite_Functor (dual d)) (dual d) dual_adjunction x
    = dd_unit x := eq_refl.

(*
   本节说明伴随、等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition StarAutonomous_of_dd_unit
  (Hiso : forall x : C, IsIsomorphism (dd_unit x)) : @StarAutonomous C _.
Proof.
  refine (@Build_StarAutonomous C _ d
            (fun x y => @exp_iso C _ x y d)
            (fun x => IsIsoToIso (dd_unit x) (Hiso x)) _).
  intros a b f. simpl. symmetry. apply dd_unit_natural.
Defined.

Example star_autonomous_dualizer
  (Hiso : forall x : C, IsIsomorphism (dd_unit x)) :
  @dualizer C _ (StarAutonomous_of_dd_unit Hiso) = d := eq_refl.

Example star_double_dual_is_dd_unit
  (Hiso : forall x : C, IsIsomorphism (dd_unit x)) (x : C) :
  to (@star_double_dual C _ (StarAutonomous_of_dd_unit Hiso) x)
    = dd_unit x := eq_refl.

(*
   本节说明伴随、等价、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition dual_AdjointEquivalence
  (Hiso : forall x : C, IsIsomorphism (dd_unit x)) :
  @AdjointEquivalence C (C^op) (Opposite_Functor (dual d)) (dual d).
Proof.
  unshelve econstructor.
  - exact dual_adjunction.
  - intro x; exact (Hiso x).
  - intro y.
    exact (@Build_IsIsomorphism (C^op) _ _ _
             (@two_sided_inverse C _ _ (dd_unit y) (Hiso y))
             (@is_left_inverse   C _ _ (dd_unit y) (Hiso y))
             (@is_right_inverse  C _ _ (dd_unit y) (Hiso y))).
Defined.

End DualSelfAdjoint.

(*
   本节说明（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export] Instance dcur_Proper_ex {C : Category} `{@SymMonClosed C}
  {x y z : C} : Proper (equiv ==> equiv) (@dcur C _ x y z).
Proof.
  intros f g Hfg; apply dcur_uniq; rewrite Hfg; apply dcur_beta.
Qed.

#[export] Instance dual_uncur_Proper_ex {C : Category}
  `{@SymMonClosed C} {d a x : C} :
  Proper (equiv ==> equiv) (@dual_uncur C _ d a x).
Proof. intros f g Hfg; unfold dual_uncur; now rewrite Hfg. Qed.

#[export] Instance dual_transpose_Proper_ex {C : Category}
  `{@SymMonClosed C} {d a x : C} :
  Proper (equiv ==> equiv) (@dual_transpose C _ d a x).
Proof. intros f g Hfg; unfold dual_transpose; now rewrite Hfg. Qed.

(*
   本节说明 Dual 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Dual 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example dual_probe_instrument : (true = false) := eq_refl.

Section DualProbeFormabilityControl.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Universes cco cch.
Context (Cv : Category@{cco cch cch}).
Context (u v : Cv).

Check (u ~{Cv}~> v).
Check (@id Cv u).
Check (@Opposite Cv).
Check (@Monoidal Cv).
Check (@SymmetricMonoidal Cv).
Check (@SymMonClosed Cv).

End DualProbeFormabilityControl.

Section DualProbeFormability.

(*
   本节说明幺半结构、hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Universes co ch cp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}).
Context (a b : Cu).

(* 相关说明。 （已译） *)
Check (a ~{Cu}~> b).
Check (@id Cu a).

(* FORMABILITY negative 1: the opposite category. *)
Fail Check (@Opposite Cu).
(* FORMABILITY negative 2: the monoidal structure. *)
Fail Check (@Monoidal Cu).
(* FORMABILITY negative 3: its symmetric refinement. *)
Fail Check (@SymmetricMonoidal Cu).
(* 相关说明。 （已译） *)
Fail Check (@SymMonClosed Cu).

End DualProbeFormability.

Section DualProbeConversion.

Context {C : Category}.
Context `{@SymMonClosed C}.
Context (d : C).

(* 相关说明。 （已译） *)
Fail Example dual_neg_braid_strict (x : C) :
  dd_unit d x = dcur (eval' ∘ braid) := eq_refl.

(* 相关说明。 （已译） *)
Example dual_ctrl_braid_residue (x : C) :
  dd_unit d x = dcur (eval' ∘ (id[x ⇒ d] ⨂ id[x]) ∘ braid) := eq_refl.

(* 相关说明。 （已译） *)
Example dual_ctrl_braid_equiv (x : C) :
  dd_unit d x ≈ dcur (eval' ∘ braid).
Proof. apply dd_unit_is_braid_transpose. Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example dual_neg_arbitrary_star (SA : @StarAutonomous C _) (x : C) :
  to (@star_double_dual C _ SA x) = dd_unit (@dualizer C _ SA) x
  := eq_refl.

(* 相关说明。 （已译） *)
Example dual_ctrl_produced_star
  (Hiso : forall x : C, IsIsomorphism (dd_unit d x)) (x : C) :
  to (@star_double_dual C _ (StarAutonomous_of_dd_unit d Hiso) x)
    = dd_unit d x := eq_refl.

End DualProbeConversion.

Section DualProbeTyping.

Context {C : Category}.
Context `{@SymMonClosed C}.
Context (d : C).

Notation "'DSA'" :=
  (dual_self_adjoint_on_the_right d) (only parsing).

(* 相关说明。 （已译） *)
Fail Example dual_neg_offdiagonal (a x : C) :
  to (@aor C C (dual d) (dual d) DSA a x)
    = from (@aor C C (dual d) (dual d) DSA a x) := eq_refl.

(* 相关说明。 （已译） *)
Example dual_ctrl_diagonal (a : C) :
  to (@aor C C (dual d) (dual d) DSA a a)
    = from (@aor C C (dual d) (dual d) DSA a a) := eq_refl.

(* 相关说明。 （已译） *)
Example dual_ctrl_swapped (a x : C) :
  to (@aor C C (dual d) (dual d) DSA a x)
    = from (@aor C C (dual d) (dual d) DSA x a) := eq_refl.

End DualProbeTyping.
