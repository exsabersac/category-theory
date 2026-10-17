(*
   本文件为测试：ProbeYonedaNatural。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Sheaf.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Deloop.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Construction.Product.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Functor.Hom.Yoneda.Natural.

Generalizable All Variables.

(** ** (1) The inherited universe restriction

    A category whose object universe is declared STRICTLY BELOW its hom
    universe.  The two bifunctors reach it; the theorem does not. *)

Section ObjectsBelowHoms.

Universes uo uh.
Constraint uo < uh.

Context (C : Category@{uo uh uh}).

(* Positive controls: both bifunctors are formable here, and so is the
   partially applied evaluation functor... *)
Check (YoEval C).
Check (YoNat C).
Check (fun c : C => @YoEvalAt C c).

(* ...and so is an isomorphism between them in the functor category the
   theorem is stated in, so the packaging is not what is rejected. *)
Definition probe_iso_id_control :
  @Isomorphism ([([C, Sets] ∏ C), Sets]) (YoEval C) (YoEval C) := iso_id.

(* Negative 1: the theorem itself is not formable at this category. *)
Fail Check (yoneda_natural C).

(* Negatives 2 and 3: neither is its donor, in either variance — so the
   restriction is inherited and not introduced by this development. *)
Fail Check (fun (F : C ⟶ Sets) (A : C) => Covariant_Yoneda_Lemma C F A).
Fail Check (fun (F : C^op ⟶ Sets) (A : C) => Yoneda_Lemma C F A).

(* Negative 4: the representability instance is restricted too, though the
   functor it represents is not — the boundary runs exactly where
   [Covariant_Yoneda_Lemma] is consumed, and [YoEvalAt] above does not
   consume it. *)
Fail Check (fun c : C => YoEvalAt_Representable C c).

End ObjectsBelowHoms.

(** ** (2) The conversion boundaries *)

Section Conversion.

Context (C : Category).
Context (x y : [C, Sets] ∏ C).
Context (tf : x ~> y).
Context (F : C^op ⟶ Sets).
Context (A : C).
Context (yv : F A).
Context (z : C).
Context (phi : z ~{C}~> A).

(* Negative 5.  The assembled [YoNat]'s arrow action and the hand-written
   [yo_nat_map] are not the same [SetoidMorphism] RECORD: their
   [proper_morphism] fields are different proof terms, one a fresh
   obligation of the target file and one assembled from [Hom]'s and
   [Swap]'s.  Control: pointwise they ARE the same term. *)
Fail Definition probe_nat_map_record :
  @fmap _ _ (YoNat C) x y tf = yo_nat_map tf := eq_refl.

Definition probe_nat_map_pointwise_control (a : fobj[YoNat C] x) :
  @fmap _ _ (YoNat C) x y tf a = yo_nat_map tf a := eq_refl.

(* Negative 6.  The derived contravariant lemma and the in-tree one are not
   the same [Isomorphism] record: all four fields differ as proof terms.
   Control: the forward legs agree once applied. *)
Fail Definition probe_derived_iso_record :
  Yoneda_Lemma_derived C F A = Yoneda_Lemma C F A := eq_refl.

Definition probe_derived_to_control (w : Presheaves [Hom ─,A] F) :
  to (Yoneda_Lemma_derived C F A) w = to (Yoneda_Lemma C F A) w := eq_refl.

(* Negative 7.  Nor are the two forward MORPHISMS equal as records, though
   they agree on every argument — the [proper_morphism] fields differ. *)
Fail Definition probe_derived_to_record :
  to (Yoneda_Lemma_derived C F A) = to (Yoneda_Lemma C F A) := eq_refl.

(* Negative 8.  The backward legs do not even agree on an argument: the
   VALUE is a whole [Transform] record whose [naturality] and
   [naturality_sym] fields are different opaque constants.  Control: the
   agreement holds one level further in, at the components. *)
Fail Definition probe_derived_from_value :
  from (Yoneda_Lemma_derived C F A) yv = from (Yoneda_Lemma C F A) yv
  := eq_refl.

Definition probe_derived_from_component_control :
  transform[from (Yoneda_Lemma_derived C F A) yv] z phi
    = transform[from (Yoneda_Lemma C F A) yv] z phi := eq_refl.

End Conversion.
