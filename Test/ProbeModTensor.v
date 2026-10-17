(*
   本文件为测试：ProbeModTensor。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Coq.QArith.QArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Universal.Element.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Vect.Tensor.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(* Index arguments supplied once, as NOTATIONS (so each unfolds to the
   constructor itself) — the device Instance/Mod/Free.v uses for its own
   witnesses; [Local Notation] does not cross files. *)
Local Notation zgen  := (@mt_gen Int_Ring Int_RMod Int_RMod).
Local Notation zplus := (@mt_plus Int_Ring Int_RMod Int_RMod).
Local Notation qgen  := (@mt_gen (field_ring Q_Field) Q_Vct Q_Vct).

(** ** Positive control: the mediator computes over ℤ

    [tensor_med] is a [Fixpoint] on formal expressions, so its value on a
    closed expression reduces all the way to a value of the target
    module's carrier. *)
Example probe_med_computes :
  cmon_map (rm_hom (tensor_med Int_mul_bilinear)) (zgen 2%Z 3%Z) = 6%Z
  := eq_refl.

(*
   本节说明 ProbeModTensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example probe_factor_is_med :
  tensor_factor Int_mul_bilinear = tensor_med Int_mul_bilinear := eq_refl.

(** ** Positive control: the universal element's element IS ⊗ *)
Example probe_universal_element_is_gen :
  @aue_elem (RMod Int_Ring) (Bilin Int_RMod Int_RMod)
    (TensorMod Int_RMod Int_RMod)
    (tensor_universal_element Int_RMod Int_RMod) = tensor_gen := eq_refl.

(*
   本节说明 ProbeModTensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example probe_triangle_value (v w : carrier (cmon_setoid Int_RMod)) :
  rbl_map (fmap[Bilin Int_RMod Int_RMod]
             (tensor_med Int_mul_bilinear) tensor_gen) v w
    = rbl_map Int_mul_bilinear v w := eq_refl.

(** ** Negative: commutativity of a formal sum is not definitional

    The carrier is a plain inductive; commutativity is a constructor of
    the quotienting relation, which is the positive control. *)
Fail Example probe_plus_comm_definitional :
  zplus (zgen 1%Z 1%Z) (zgen 2%Z 2%Z)
    = zplus (zgen 2%Z 2%Z) (zgen 1%Z 1%Z) := eq_refl.

Example probe_plus_comm_up_to_equiv :
  mt_eq (zplus (zgen 1%Z 1%Z) (zgen 2%Z 2%Z))
        (zplus (zgen 2%Z 2%Z) (zgen 1%Z 1%Z)) :=
  mte_comm _ _.

(*
   本节说明 ProbeModTensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example probe_balanced_definitional :
  zgen 6%Z 1%Z = zgen 2%Z 3%Z := eq_refl.

Example probe_balanced_up_to_equiv :
  mt_eq (zgen 6%Z 1%Z) (zgen 2%Z 3%Z) :=
  @tensor_balanced Int_Ring Int_RMod Int_RMod 3%Z 2%Z 1%Z.

(*
   本节说明 ProbeModTensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example probe_q_med_definitional :
  cmon_map (rm_hom (tensor_med Q_mul_bilinear)) (qgen (1#2) (4#1)) = 2
  := eq_refl.

Example probe_q_med_up_to_equiv :
  cmon_map (rm_hom (tensor_med Q_mul_bilinear)) (qgen (1#2) (4#1)) ≈ 2.
Proof. exact q_tensor_med_computes. Qed.

(*
   本节说明 ProbeModTensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example probe_triangle_definitional :
  fmap[Bilin Int_RMod Int_RMod] (tensor_med Int_mul_bilinear) tensor_gen
    = Int_mul_bilinear := eq_refl.

Example probe_triangle_up_to_equiv :
  fmap[Bilin Int_RMod Int_RMod] (tensor_med Int_mul_bilinear) tensor_gen
    ≈ Int_mul_bilinear.
Proof.
  exact (unique_property
           (@aue_universal (RMod Int_Ring) (Bilin Int_RMod Int_RMod)
              (TensorMod Int_RMod Int_RMod)
              (tensor_universal_element Int_RMod Int_RMod)
              Int_RMod Int_mul_bilinear)).
Qed.
