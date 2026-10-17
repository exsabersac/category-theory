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
(* 相关说明。 （已译） *)

(* NEGATIVE. Stripped, reports universe inconsistency between the
 对象 universe [Sets] hom universe. （已译） *)
Fail Check @universal_element_yoneda (Sets^op) Powerset_Prop_op Powerset_Omega.

(* NEGATIVE, the composed form. *)
Fail Check
  @universal_element_representation (Sets^op) Powerset_Prop_op Powerset_Omega.

(* 相关说明。 （已译） *)
Check ue_representation Powerset_Prop_op Powerset_Omega
        Powerset_Prop_universal_element.

(* 相关说明。 （已译） *)
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
(* 相关说明。 （已译） *)

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
(* 相关说明。 （已译） *)

(* NEGATIVE.  Stripped: "cannot unify
   Powerset_preimage_of_truth (Powerset_char S) and S". *)
Fail Example sets_round_trip_strict
  (A : SetoidObject) (S : carrier (Powerset_Prop_obj A)) :
  Powerset_preimage_of_truth (Powerset_char S) = S := eq_refl.

(* 相关说明。 （已译） *)
Check (fun (A : SetoidObject) (S : carrier (Powerset_Prop_obj A)) =>
         powerset_preimage_char S
         : Powerset_preimage_of_truth (Powerset_char S) ≈ S).

(* 相关说明。 （已译） *)
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
(* * ** (5) The 函子 laws not definitional （已译） *)

(* 相关说明。 （已译） *)
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

(* POSITIVE CONTROL, CONTRAST once more: over [FinSet] 恒等
 law same 函子 IS Leibniz equation codes. （已译） *)
Check (fun (n : nat) (S : Fin.t (finpow n)) =>
         finpow_map_id S : finpow_map (fun i : Fin.t n => i) S = S).

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

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

(* The classifier [FinSet] power-set 函子 built over it share
 truth-value 对象, nose. （已译） *)
Example finset_omega_is_two :
  @Ω FinSet FinSet_Terminal FinSet_Classifier = 2%nat := eq_refl.
