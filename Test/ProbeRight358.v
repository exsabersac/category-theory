(*
   本文件为测试：ProbeRight358。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Opposite.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Adjunction.Right.

Open Scope category_scope.

Generalizable All Variables.

Section ProbeRight358.

Context {A X : Category}.
Context {S : (A^op) ⟶ X}.
Context {T : (X^op) ⟶ A}.

(* Controls.  Every constant a negative names is also named OUTSIDE a
   [Fail] and APPLIED, never left bare -- an unapplied polymorphic
   constant elaborates for reasons unrelated to the negative and so
   certifies nothing. *)
Check (AdjointOnTheRight S T).
Check (AdjointOnTheLeft S T).
Check (@Adjunction (A^op) X (Opposite_Functor T) S).
Check @Adjunction_of_AdjointOnTheRight.
Check @AdjointOnTheRight_of_Adjunction.
Check (MutuallyRightAdjoint S T).
Check (fun H : AdjointOnTheRight S T =>
         MutuallyRightAdjoint_of_AdjointOnTheRight S T H).
Check (fun H : MutuallyRightAdjoint S T =>
         AdjointOnTheRight_of_MutuallyRightAdjoint S T H).
Check @AdjointOnTheRight_sym.
Check @right_does_not_imply_left.
Check @Chain3_not_AdjointOnTheLeft.
Check @Chain3_AdjointOnTheRight.
Check @Powerset_not_AdjointOnTheLeft.
Check @right_does_not_imply_left_in_Sets.

(* TYPING 1 -- the reviewer's bar: the class is not an abbreviation. *)
Fail Definition probe358_not_an_abbreviation
  (H : @Adjunction (A^op) X (Opposite_Functor T) S) :
  AdjointOnTheRight S T := H.

(* TYPING 2 -- and not in the other direction either. *)
Fail Definition probe358_not_an_abbreviation_rev
  (H : AdjointOnTheRight S T) :
  @Adjunction (A^op) X (Opposite_Functor T) S := H.

(* TYPING 3 -- right and left are different classes, not one class
   spelled two ways.  The MATHEMATICAL separation is the target's
   [right_does_not_imply_left], a theorem over all categories; this
   negative only records that they are not definitionally equal. *)
Fail Definition probe358_right_is_not_left
  (H : AdjointOnTheRight S T) : AdjointOnTheLeft S T := H.

(* CONVERSION 4-5 -- the hom-set presentation and the unit/counit
   presentation are interderivable but their round trips are NOT
   [eq_refl]: the classes are rebuilt rather than returned.  Contrast
   the FOUR round trips against the ordinary adjunction, which the
   target pins at [eq_refl]. *)
Fail Example probe358_MRA_round_strict (H : MutuallyRightAdjoint S T) :
  MutuallyRightAdjoint_of_AdjointOnTheRight S T
    (AdjointOnTheRight_of_MutuallyRightAdjoint S T H) = H := eq_refl.

Fail Example probe358_aor_MRA_round_strict (H : AdjointOnTheRight S T) :
  AdjointOnTheRight_of_MutuallyRightAdjoint S T
    (MutuallyRightAdjoint_of_AdjointOnTheRight S T H) = H := eq_refl.

End ProbeRight358.

(* Instrument check.  [Fail] is live in this build and does notice a
   conversion failure.  Scope-free deliberately, so that it cannot fail
   on a missing scope delimiter instead of on the proposition. *)
Fail Example probe358_instrument : (true = false) := eq_refl.
