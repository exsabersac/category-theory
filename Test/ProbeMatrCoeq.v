Require Import Coq.QArith.QArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Matr.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Field.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Instance.Parallel.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Instance.Matr.Elimination.
Require Import Category.Instance.Matr.Coequalizer.
Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(** * Probe: strength boundaries of the matrix coequalizer *)

(*
   本文件为测试：ProbeMatrCoeq。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 ProbeMatrCoeq 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(*
   本节说明 ProbeMatrCoeq 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition probe_qed_decider_blocks :
  matr_coeq_obj F2_Field F2_Field_dec coeq_f2_A coeq_f2_B = 1%nat
  := eq_refl.

Definition probe_pos_transparent_decider_computes :
  matr_coeq_obj F2_Field f2_dec coeq_f2_A coeq_f2_B = 1%nat
  := eq_refl.

(*
   本节说明 ProbeMatrCoeq 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition probe_map_is_identity :
  matr_coeq_map F2_Field f2_dec coeq_f2_A coeq_f2_A
    = mat_id F2_Field 2 := eq_refl.

Fail Definition probe_map_is_h :
  coeq_f2_map = coeq_f2_h := eq_refl.

Fail Definition probe_map_is_const :
  coeq_f2_map = ((fun _ _ => true) : 2%nat ~{Matr F2_Field}~> 1%nat)
  := eq_refl.

(*
   本节说明 ProbeMatrCoeq 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition probe_pos_map_agrees_at :
  coeq_f2_map F1 F1 = coeq_f2_h F1 F1 := eq_refl.

(*
   本节说明 ProbeMatrCoeq 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition probe_op_record_identity :
  IsCoequalizer coeq_f2_A coeq_f2_B coeq_f2_obj coeq_f2_map
    = @IsEqualizer ((Matr F2_Field)^op) 2%nat 1%nat
        coeq_f2_A coeq_f2_B coeq_f2_obj coeq_f2_map := eq_refl.

(* Positive control naming the bridge constant itself. *)
Definition probe_pos_op_bridge :
  @IsEqualizer ((Matr F2_Field)^op) 2%nat 1%nat
    coeq_f2_A coeq_f2_B coeq_f2_obj coeq_f2_map
  := IsEqualizer_op_of_IsCoequalizer coeq_f2.

(** ** Elimination.v: the engine's own boundaries *)

Section EliminationNegatives.

Context (K : FieldObject).
Context (a b : nat).
Context (A : Matrix K a b).

(* The identity acts as a unit only up to [≈]; [mat_mul] does not
   reduce a Kronecker [delta] against a free matrix. *)
Fail Definition probe_mat_id_l_strict :
  mat_mul K (mat_id K a) A = A := eq_refl.

Fail Definition probe_mat_sub_self_strict :
  mat_sub K A A = mat_zero K := eq_refl.

End EliminationNegatives.

(* Positive controls naming Elimination.v's own constants, so a rename or
   a statement change in the engine breaks this file loudly. *)
Definition probe_pos_mat_id_l (K : FieldObject)
  (Kdec : forall a b : carrier (rig_setoid K), (a ≈ b) + (a ≈ b -> False))
  (a b : nat) (A : Matrix K a b) :
  mat_mul K (mat_id K a) A ≈ A := mat_mul_id_l K Kdec A.

(*
   本节说明 ProbeMatrCoeq 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check F2_Field_dec.

Check (matr_coeq_map F2_Field f2_dec coeq_f2_A coeq_f2_B).

Check (IsCoequalizer coeq_f2_A coeq_f2_B coeq_f2_obj coeq_f2_map).

Check (fun (K : FieldObject) (a b : nat) (A : Matrix K a b) =>
         mat_sub K A A).

Check (fun (K : FieldObject) (a b : nat) => @mat_zero K a b).

(** ** Positive controls for the headline artifacts

    These name the two principal constants directly, so that neither can
    be renamed or restated without this file failing. *)

Check (matr_IsCoequalizer F2_Field f2_dec coeq_f2_A coeq_f2_B).

Check (Matr_HasCoequalizers F2_Field f2_dec).

Check (left_null_basis F2_Field f2_dec).

Check (left_null_basis_diff F2_Field f2_dec).

(* Non-degeneracy, named so the witness cannot silently become trivial:
   the coequalizing map is epic but NOT monic, so it is a proper
   quotient rather than an isomorphism in disguise. *)

Check coeq_f2_map_epic.

Check coeq_f2_map_not_monic.

Check coeq_f2_obj_not_zero.

Check coeq_f2_obj_not_two.
