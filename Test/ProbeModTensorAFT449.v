Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Universal.Element.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Construction.Elements.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Adjunction.SpanningArrow.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Ab.DirectedColimit.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Mod.Bimodule.
Require Import Category.Instance.Mod.Limit.
Require Import Category.Instance.Mod.Spanning.
Require Import Category.Instance.Mod.TensorAFT.
Require Import Category.Theory.Algebra.Rig.
(*
   本文件为测试：ProbeModTensorAFT449。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.GAFT.Resize.
Require Import Category.Instance.Rng.

(*
   本节说明伴随、函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check *)

(* A refusal expected around a name that is not there.  If the instrument
   were inert this line would pass silently and so would everything below
   it. *)
Fail Check zzz_no_such_constant_449.

(** ** Positive controls: every library constant a negative names *)

Section Controls.

Context {R : RingObject}.
Context (V V' : RModObject R).

Check (RMod_Complete R).
Check (Bilin_continuous V V').
Check (Bilin_PreservesImageLimit V V').
Check (tensor_esols_direct V V').
Check (tensor_esols_from_tensor V V').
Check (Bilin_PreservesWidePullbacks V V').
Check (RMod_HasWidePullbacks R).
Check (TensorMod V V').
Check (@tensor_gen R V V').
Check (tensor_repr_of_UE V V').
Check (preserves_image_of_representable (tensor_repr_of_UE V V')).
Check (@SpanningArrowsOutOf (RMod R) Sets (Bilin V V') SetsOne).

(* The three [eq_refl] readbacks of the direct solution set, as controls. *)
Example c_esol_index :
  esol_index (tensor_esols_direct V V')
    = SpanningArrowsOutOf (Bilin V V') SetsOne := eq_refl.

Example c_esol_obj (i : SpanningArrowsOutOf (Bilin V V') SetsOne) :
  esol_obj (tensor_esols_direct V V') i = `1 i := eq_refl.

Example c_esol_elem (i : SpanningArrowsOutOf (Bilin V V') SetsOne) :
  esol_elem (tensor_esols_direct V V') i = `1 (`2 i) ttt := eq_refl.

(*
   本节说明 ProbeModTensorAFT449 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example c_same_index (HWP : @HasWidePullbacks (RMod R)) :
  esol_index (@tensor_esols R V V' HWP)
    = esol_index (tensor_esols_direct V V') := eq_refl.

(* The representation read off the explicit tensor keeps [TensorMod] as its
   representing object at [eq_refl] -- the control the CONVERSION negative
   below is measured against. *)
Example c_repr_of_UE_obj :
  @repr_obj (RMod R) (Bilin V V') (tensor_repr_of_UE V V') = TensorMod V V'
  := eq_refl.

End Controls.

Section AbControls.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

Check (BalBiadd N M).
Check (BalBiadd_continuous N M).
Check (BalBiadd_PreservesImageLimit N M).
Check (bal_esols_direct N M).
Check (bal_esols_from_tensor N M).
Check Ab_Complete.
Check (BalTensor N M).
Check (@bal_gen X N M).

Example c_bal_ue_obj :
  @ue_obj Ab (BalBiadd N M) (bal_UniversalElement N M) = BalTensor N M
  := eq_refl.

Example c_bal_ue_elem :
  @ue_elem Ab (BalBiadd N M) (bal_UniversalElement N M) = @bal_gen X N M
  := eq_refl.

Example c_bal_esol_index :
  esol_index (bal_esols_direct N M)
    = SpanningArrowsOutOf (BalBiadd N M) SetsOne := eq_refl.

End AbControls.

(* The two applications the negatives below sit beside, at an unconstrained
   ring: these ARE accepted, so the negatives are about the argument, not
   about the theorem being unusable. *)
Check (fun (R : RingObject) (V V' : RModObject R) => tensor_via_AFT V V').
Check (fun (R : RingObject) (V V' : RModObject R) =>
         module_tensor_universal V V').
(* the issue's verification name IS the AFT universal element, by definition *)
Example c_alias_is_ue : @module_tensor_universal = @tensor_AFT_ue := eq_refl.
Check (fun (R : RingObject) (V V' : RModObject R) =>
         tensor_via_AFT_from_tensor V V').
Check (fun (X : RingObject) (N : RModObject (Ring_op X))
           (M : RModObject X) => bal_tensor_via_AFT N M).

(*
   本节说明 ProbeModTensorAFT449 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UnconditionalPayoff.

(* The tensor product of the integers with themselves as a Z-module,
   obtained from the adjoint functor theorem with NO hypothesis. *)
Check (tensor_via_AFT Int_RMod Int_RMod).
Check (module_tensor_universal Int_RMod Int_RMod).
Check (tensor_AFT_iso Int_RMod Int_RMod).
Check (tensor_AFT_ue Int_RMod Int_RMod).

(* Mac Lane's OWN p. 128 family, resized by his Lemma 2 (section 10 of the
   target), at the same ring: the second, book-faithful route. *)
Check (tensor_via_AFT_maclane Int_RMod Int_RMod).
Check (tensor_spanning_SmallUpToIso Int_RMod Int_RMod).
Check (tensor_esols_resized Int_RMod Int_RMod).

(* A SECOND ring, and a genuinely different one: the rationals. *)
Definition p449_QMod : RModObject Q_Ring := Ring_RMod Q_Ring.
Check (tensor_via_AFT p449_QMod p449_QMod).
Check (tensor_via_AFT_maclane p449_QMod p449_QMod).

(* A THIRD: the opposite ring of the integers, which is what Exercise 3's
   balanced tensor needs on the left. *)
Definition p449_OpMod : RModObject (Ring_op Int_Ring) :=
  Ring_RMod (Ring_op Int_Ring).
Check (tensor_via_AFT p449_OpMod p449_OpMod).

(* Exercise 3 at the integers, also unconditional. *)
Check (bal_tensor_via_AFT p449_OpMod Int_RMod).
Check (bal_AFT_iso p449_OpMod Int_RMod).
Check (bal_AFT_ue p449_OpMod Int_RMod).
Check (bal_esols_prop p449_OpMod Int_RMod).

End UnconditionalPayoff.

(*
   本节说明 ProbeModTensorAFT449 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section IndexReadbacks.

Context {R : RingObject}.
Context (V V' : obj[RMod R]).

Example p449_prop_index :
  esol_index (tensor_esols_prop V V') = CongIdx V V' := eq_refl.

Example p449_prop_obj (i : CongIdx V V') :
  esol_obj (tensor_esols_prop V V') i = QMod (`1 i) (`2 i) := eq_refl.

Example p449_prop_elem (i : CongIdx V V') :
  esol_elem (tensor_esols_prop V V') i = QMod_gen (`1 i) (`2 i) := eq_refl.

(* Mac Lane's Lemma 2: the SMALL index of the resized family is the same
   congruence type. *)
Example p449_maclane_small_index :
  si_carrier (tensor_spanning_SmallUpToIso V V') = CongIdx V V' := eq_refl.

Example p449_resized_index :
  esol_index (tensor_esols_resized V V') = CongIdx V V' := eq_refl.

(* And the direct family's index is still the sigma over objects -- the
   one NEGATIVE 1 refuses. *)
Example p449_direct_index :
  esol_index (tensor_esols_direct V V')
    = SpanningArrowsOutOf (Bilin V V') SetsOne := eq_refl.

End IndexReadbacks.

Section BalIndexReadbacks.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

Example p449_bal_prop_index :
  esol_index (bal_esols_prop N M) = BalCongIdx N M := eq_refl.

Example p449_bal_prop_obj (i : BalCongIdx N M) :
  esol_obj (bal_esols_prop N M) i = QBal (`1 i) (`2 i) := eq_refl.

End BalIndexReadbacks.

(*
   本节说明 ProbeModTensorAFT449 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition n1_direct_esols_refused {R : RingObject}
  (V V' : RModObject R) : Representable (Bilin V V') :=
  representability_theorem (Bilin V V') (RMod_Complete R)
    (Bilin_PreservesImageLimit V V') (tensor_esols_direct V V').

(*
   本节说明 ProbeModTensorAFT449 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition n2_gaft_from_spanning_refused {R : RingObject}
  (V V' : RModObject R) (HWP : @HasWidePullbacks (RMod R)) :=
  @GAFT_from_spanning (RMod R) Sets (Bilin V V') HWP
    (Bilin_PreservesWidePullbacks V V') (RMod_Complete R)
    (Bilin_PreservesImageLimit V V').

(*
   本节说明 ProbeModTensorAFT449 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition n3_bal_direct_esols_refused {X : RingObject}
  (N : RModObject (Ring_op X)) (M : RModObject X) :
  Representable (BalBiadd N M) :=
  bal_tensor_via_AFT_of_esols N M (bal_esols_direct N M).

(*
   本节说明 ProbeModTensorAFT449 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SetPin.

Universes pra prb prc.

(*
   本节说明 ProbeModTensorAFT449 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Constraint Set < prb.

Context (Ru : RingObject@{pra prb prc}).
Context (Vu Vu' : RModObject Ru).

Check (tensor_via_AFT Vu Vu').

End SetPin.

Check (fun (Ru : RingObject) (V V' : RModObject Ru) => tensor_via_AFT V V').

(*
   本节说明伴随、函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example n5_aft_object_not_definitional {R : RingObject}
  (V V' : RModObject R) (E : ElementSolutionSet (Bilin V V')) :
  @repr_obj (RMod R) (Bilin V V') (tensor_via_AFT_of_esols V V' E)
    = TensorMod V V' := eq_refl.

(*
   本节说明伴随、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example n6_circular_route_is_a_different_term {R : RingObject}
  (V V' : RModObject R) :
  @Bilin_PreservesImageLimit R V V'
    = preserves_image_of_representable (tensor_repr_of_UE V V') := eq_refl.

(** ** NEGATIVE 7 (ARGUMENT NAME): [MGen]'s predicate is positional

    Instance/Mod/Spanning.v's [MGen] takes its predicate as an EXPLICIT
    section variable, so the constructors do not answer to it by name.  The
    control is the same application written positionally. *)

Section GenArgumentName.

Context {R : RingObject}.
Context (V V' : RModObject R).

Check (fun (a : carrier (cmon_setoid (TensorMod V V')))
           (Ha : rbl_image (@tensor_gen R V V') a) =>
         mgen_base (rbl_image (@tensor_gen R V V')) a Ha).

Fail Check (fun (a : carrier (cmon_setoid (TensorMod V V')))
                (Ha : rbl_image (@tensor_gen R V V') a) =>
              mgen_base (P := rbl_image (@tensor_gen R V V')) a Ha).

End GenArgumentName.

(*
   本节说明 ProbeModTensorAFT449 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SetCarrierPin.

Universes pa pb pc.
Constraint pb = Set.

Context (Rs : RingObject@{pa pb pc}).
Context (Vs Vs' : RModObject Rs).

(* THE CONTROL: the conditional form elaborates at this very ring. *)
Definition p449_cond_at_set_carrier
  (E : ElementSolutionSet (Bilin Vs Vs')) : Representable (Bilin Vs Vs') :=
  tensor_via_AFT_of_esols Vs Vs' E.

(* THE NEGATIVE: the unconditional one does not. *)
Fail Definition p449_uncond_at_set_carrier :
  Representable (Bilin Vs Vs') := tensor_via_AFT Vs Vs'.

End SetCarrierPin.
