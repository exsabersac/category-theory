(*
   本文件为测试：ProbePowersetUniversal。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.SubobjectClassifier.Natural.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Powerset.
Require Import Category.Theory.Universal.Element.

Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(* ------------------------------------------------------------------------ *)
(** ** (1) The Yoneda route at [Sets] *)

(* NEGATIVE.  Stripped, this reports a universe inconsistency between the
   object universe of [Sets] and its hom universe. *)
Fail Check @universal_element_yoneda (Sets^op) Powerset_Prop_op Powerset_Omega.

(* NEGATIVE, the composed form. *)
Fail Check
  @universal_element_representation (Sets^op) Powerset_Prop_op Powerset_Omega.

(* POSITIVE CONTROL: the Yoneda-free route at the same three arguments. *)
Check ue_representation Powerset_Prop_op Powerset_Omega
        Powerset_Prop_universal_element.

(* POSITIVE CONTROL: and the whole representation the target file builds. *)
Check Powerset_representation.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section YonedaIsUsableElsewhere.
  Universe u.
  Context (K : Category@{u u u}) (F : K ⟶ Sets) (r : K).
  Check @universal_element_yoneda K F r.
End YonedaIsUsableElsewhere.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section PowersetAtTwoSizes.
  Universe u1 u2 u3 u4.
  Constraint Set < u1.
  Constraint u1 < u2.
  Constraint u2 < u3.
  Constraint u3 < u4.
  Check Powerset_Prop_op@{u1 u2}.
  Check Powerset_Prop_op@{u3 u4}.
  Check Powerset_Prop_universal_element@{u1 u2}.
  Check Powerset_Prop_universal_element@{u3 u4}.
End PowersetAtTwoSizes.

(* ------------------------------------------------------------------------ *)
(** ** (2) The element is not the point *)

(* NEGATIVE, over [Sets].  Stripped: "The term Powerset_truth_point has type
   carrier Powerset_Omega while it is expected to have type ...". *)
Fail Example point_is_not_an_element :
  carrier (Powerset_Prop_obj Powerset_Omega) := Powerset_truth_point.

(* POSITIVE CONTROL. *)
Example subset_is_an_element :
  carrier (Powerset_Prop_obj Powerset_Omega) := Powerset_truth_subset.

(* NEGATIVE, over [FinSet]: [Fin.t 2] is not [Fin.t 4]. *)
Fail Example fin_point_is_not_an_element :
  Fin.t (finpow 2) := finpow_truth_point.

(* POSITIVE CONTROL. *)
Example fin_subset_is_an_element :
  Fin.t (finpow 2) := finpow_truth_subset.

(* ------------------------------------------------------------------------ *)
(** ** (3) The [Sets] round trip is [≈] only; the [FinSet] one is Leibniz *)

(* NEGATIVE.  Stripped: "cannot unify
   Powerset_preimage_of_truth (Powerset_char S) and S". *)
Fail Example sets_round_trip_strict
  (A : SetoidObject) (S : carrier (Powerset_Prop_obj A)) :
  Powerset_preimage_of_truth (Powerset_char S) = S := eq_refl.

(* POSITIVE CONTROL: the [≈] form, which is what the target proves. *)
Check (fun (A : SetoidObject) (S : carrier (Powerset_Prop_obj A)) =>
         powerset_preimage_char S
         : Powerset_preimage_of_truth (Powerset_char S) ≈ S).

(* POSITIVE CONTROL, and the CONTRAST: over [FinSet] the same round trip is
   a Leibniz equation, with no setoid step anywhere. *)
Check (fun (n : nat) (S : Fin.t (finpow n)) =>
         fin_tabulate_apply S : fin_tabulate (fin_apply S) = S).

(* ------------------------------------------------------------------------ *)
(** ** (4) The two readings of {⊤} *)

(* NEGATIVE.  Stripped: "cannot unify Powerset_truth_subset and
   Powerset_holds". *)
Fail Example truth_readings_strict :
  Powerset_truth_subset = Powerset_holds := eq_refl.

(* POSITIVE CONTROL. *)
Check (powerset_truth_subset_holds
       : Powerset_truth_subset ≈ Powerset_holds).

(* ------------------------------------------------------------------------ *)
(** ** (5) The functor laws are not definitional *)

(* NEGATIVE.  Stripped: "cannot unify fmap[Powerset_Prop_op] id{Sets^op} and
   id{Sets}".  CORRECTION (#1347): a POSITIVE CONTROL now; the command
   holds at [eq_refl]. *)
Example powerset_fmap_id_strict (X : SetoidObject) :
  fmap[Powerset_Prop_op] (id{Sets^op} : X ~{Sets^op}~> X) = id{Sets}
  := eq_refl.

(* POSITIVE CONTROL (#1347): the composition law at [eq_refl] as well. *)
Example powerset_fmap_comp_strict (X Y Z : SetoidObject)
  (f : X ~{Sets^op}~> Y) (g : Y ~{Sets^op}~> Z) :
  fmap[Powerset_Prop_op] (g ∘ f)
    = fmap[Powerset_Prop_op] g ∘ fmap[Powerset_Prop_op] f := eq_refl.

(* POSITIVE CONTROL: the [≈] form. *)
Check (fun X : SetoidObject => @Powerset_Prop_comap_id X).

(* POSITIVE CONTROL, and the CONTRAST once more: over [FinSet] the identity
   law of the same functor IS a Leibniz equation on codes. *)
Check (fun (n : nat) (S : Fin.t (finpow n)) =>
         finpow_map_id S : finpow_map (fun i : Fin.t n => i) S = S).

(* ------------------------------------------------------------------------ *)
(** ** Positive controls that are strength claims in their own right *)

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example sets_subsets_are_maps (A : SetoidObject) :
  carrier (Powerset_Prop_obj A) = (A ~{Sets}~> Powerset_Omega) := eq_refl.

(*
   本节说明 ProbePowersetUniversal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example fin_subsets_are_maps (n : nat) :
  Fin.t (finpow n) = (Fin.t n → Fin.t 2) := eq_refl.

(* The classifier of [FinSet] and the power-set functor built over it share
   their truth-value object, on the nose. *)
Example finset_omega_is_two :
  @Ω FinSet FinSet_Terminal FinSet_Classifier = 2%nat := eq_refl.
