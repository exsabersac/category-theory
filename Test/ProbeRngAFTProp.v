Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.GAFT.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Limit.
Require Import Category.Instance.Rng.Free.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.AFT.

Generalizable All Variables.

(*
   本文件为测试：ProbeRngAFTProp。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check *)

Fail Check zzz_no_such_constant_rng_aft.

(** ** Positive controls *)

Check @RngCongIdx.
Check @IsRngCongruence.
Check @QRng.
Check @QRng_insert.
Check @rng_ker.
Check @rng_ker_med.
Check @Rng_Forget_Ab_solution_set_prop.
Check @Rng_Forget_solution_set_prop.
Check @free_rng_ab_via_GAFT.
Check @free_ring_via_GAFT.

(* The circular readings are KEPT and are still checkable; they are the
   comparison, not the delivery. *)
Check @Rng_Forget_Ab_solution_set_from_adjunction.
Check @Rng_Forget_solution_set_from_adjunction.
Check @free_rng_ab_via_GAFT_from_adjunction.
Check @free_ring_via_GAFT_from_adjunction.

(** ** The index readbacks: WHICH solution set each application consumes *)

Section IndexReadbacks.

Context (A : Ab).
Context (X : Sets).

(* The [Ab] half: the index is the congruence type on the free-ring terms
   over [A], and the objects are the quotients. *)
Example prng_ab_index :
  sol_index (Rng_Forget_Ab_solution_set_prop A) = RngCongIdx A := eq_refl.

Example prng_ab_obj (i : RngCongIdx A) :
  sol_obj (Rng_Forget_Ab_solution_set_prop A) i = QRng (`1 i) (`2 i)
  := eq_refl.

(* The [Sets] half takes the SAME index, over the free abelian group on
   [X] -- the direct route, not a composite of two adjunctions. *)
Example prng_sets_index :
  sol_index (Rng_Forget_solution_set_prop X)
    = RngCongIdx (FreeAbObject X) := eq_refl.

Example prng_sets_obj (i : RngCongIdx (FreeAbObject X)) :
  sol_obj (Rng_Forget_solution_set_prop X) i = QRng (`1 i) (`2 i)
  := eq_refl.

(* And the circular ones are still the singleton, which is the contrast. *)
Example prng_circular_index :
  sol_index (Rng_Forget_Ab_solution_set_from_adjunction A) = poly_unit
  := eq_refl.

End IndexReadbacks.

(*
   本节说明 ProbeRngAFTProp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example prng_n1_prop_index_is_not_singleton (A : Ab) :
  sol_index (Rng_Forget_Ab_solution_set_prop A) = poly_unit := eq_refl.

(*
   本节说明 ProbeRngAFTProp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example prng_n2_applications_differ :
  free_rng_ab_via_GAFT = free_rng_ab_via_GAFT_from_adjunction := eq_refl.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ConcreteWitnesses.

Definition prng_ZAb : Ab := ring_ab Int_Ring.

(* The free ring on the integers as an abelian group. *)
Check (`1 free_rng_ab_via_GAFT prng_ZAb).
Check (Rng_Forget_Ab_solution_set_prop prng_ZAb).
Check (free_rng_ab_via_GAFT_comparison prng_ZAb).
Check (free_rng_ab_via_GAFT_unit prng_ZAb).

(* The free ring on a named set, twice. *)
Check (`1 free_ring_via_GAFT nat_setoid_object).
Check (`1 free_ring_via_GAFT bool_setoid_object).
Check (Rng_Forget_solution_set_prop nat_setoid_object).
Check (free_ring_via_GAFT_comparison nat_setoid_object).
Check (free_ring_via_GAFT_unit nat_setoid_object).

(* And the congruence index at a named object, which is the thing that
   made the whole construction fit. *)
Check (RngCongIdx prng_ZAb).
Check (RngCongIdx (FreeAbObject nat_setoid_object)).

End ConcreteWitnesses.
