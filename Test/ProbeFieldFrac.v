Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Frac.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Field.
Require Import Category.Instance.Field.Frac.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.

(*
   本文件为测试：ProbeFieldFrac。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

(* Positive control: the claim itself. *)
Example frac_extend_half_control :
  rig_map (frac_extend Int_Dom Q_Field ZtoQ_Dom)
    (mk_frac Int_Dom 1%Z 2%Z two_nonzero) = (1 # 2)%Q := eq_refl.

(* 相关说明。 （已译） *)
Fail Example frac_extend_half_wrong :
  rig_map (frac_extend Int_Dom Q_Field ZtoQ_Dom)
    (mk_frac Int_Dom 1%Z 2%Z two_nonzero) = (1 # 3)%Q := eq_refl.

(* 相关说明。 （已译） *)
Example q_probe_qeq : ((2 # 4) == (1 # 2))%Q := eq_refl.

Example q_probe_not_leibniz : (2 # 4)%Q = (1 # 2)%Q → False.
Proof. discriminate. Qed.

(* 相关说明。 （已译） *)
Fail Example frac_extend_half_only_up_to_Qeq :
  rig_map (frac_extend Int_Dom Q_Field ZtoQ_Dom)
    (mk_frac Int_Dom 1%Z 2%Z two_nonzero) = (2 # 4)%Q := eq_refl.

(* * ** The two forgetful 函子 [IntDom] （已译） *)

(* Positive control: agreement up to ≈ on morphisms. *)
Example field_intdom_agrees_up_to_equiv
  (stab : ∀ F : FieldObject, FieldStableAtZero F) (F K : StableField)
  (f : F ~{StableField}~> K) :
  fmap[Field_IntDom stab] (fmap[Incl Field StableField_Sub] f)
    ≈ fmap[StableField_IntDom] f.
Proof. intro a; simpl; reflexivity. Qed.

(*
   本节说明 ProbeFieldFrac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example field_intdom_agrees_strictly
  (stab : ∀ F : FieldObject, FieldStableAtZero F) (F K : StableField)
  (f : F ~{StableField}~> K) :
  fmap[Field_IntDom stab] (fmap[Incl Field StableField_Sub] f)
    = fmap[StableField_IntDom] f := eq_refl.

(* Positive control: SAME shape comparison, one 函子 along,
 IS strict — so negative above not generic fact about
 证明-carrying records. （已译） *)
Example intdom_dom_agrees_strictly (F K : StableField)
  (f : F ~{StableField}~> K) :
  fmap[IntDom_Dom] (fmap[StableField_IntDom] f) = fmap[StableField_Dom] f
  := eq_refl.

(* 相关说明。 （已译） *)

(* Positive control. *)
Example ZtoF2_is_a_Dom_morphism :
  Int_Dom ~{Dom}~> Field_Dom F2_Field := ZtoF2.

(*
   本节说明 ProbeFieldFrac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition ZtoF2_is_not_an_IntDom_morphism :
  Int_Dom ~{IntDom}~> field_dom F2_Field := ZtoF2.
