(*
   本文件为测试：ProbeRingLattice340。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Group.
Require Import Category.Structure.Ring.
Require Import Category.Structure.Lattice.

Generalizable All Variables.

(** ** Instrument check

    A [Fail] that never fails would make every negative below vacuous. *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** Negatives 1-3 (FORMABILITY): three INDEPENDENT donors identify hom
       with proof

    Each is rejected under `Constraint uh < up` while the control shows a
    hom-set of such a category is perfectly formable at those levels. *)

Section Donors.

Universe uo uh up.
Constraint uh < up.

(* Control: a hom-set of such a category exists. *)
Check (fun (C : Category@{uo uh up}) (x y : C) => x ~> y).

(* Controls: all three donors exist at UNCONSTRAINED levels.  Without
   these, a rename of any of them would leave its negative succeeding on a
   reference-not-found error rather than on the universe boundary. *)
Check @Cartesian.
Check @Terminal.
Check @MonoidObject.
Check @Monoidal.

(* NEGATIVE 1. *)
Fail Check (fun (C : Category@{uo uh up}) => @Cartesian C).

(* NEGATIVE 2. *)
Fail Check (fun (C : Category@{uo uh up}) => @Terminal C).

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (fun (C : Category@{uo uh up}) => @Monoidal C).

End Donors.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check @dup_left.
Check @dup_right.

(** ** Positive controls for the headline artifacts *)

Check @InternalSemiring.
Check @InternalRing.
Check @InternalSemilattice.
Check @InternalLattice.

(** The two derivations that are the mathematical content: annihilation is
    a THEOREM for a ring, and idempotence is DERIVED from absorption. *)

Check @ring_annihilate_l.
Check @ring_annihilate_r.
Check @ring_cancel_idem.
Check @InternalRing_InternalSemiring.
Check @InternalRing_GroupObject.
Check @lattice_join_idem.
Check @lattice_meet_idem.
Check @lattice_bot_meet.
Check @lattice_top_join.

(** The Sets passages, both directions, in both files. *)

Check @Sets_InternalSemiring.
Check @Rig_of_InternalSemiring.
Check @Sets_InternalRing.
Check @Ring_of_InternalRing.
Check @Sets_InternalLattice.
Check @SetoidLattice_of_InternalLattice.
Check @SetoidLattice.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check @nat_plus_not_distributive.
Check @bool_or_not_annihilating.
Check @bool_join_not_absorbing.
Check @bool_xor_not_idempotent.

(** Computing witnesses. *)

Check @Nat_ISemiring.
Check @Int_IRing.
Check @Bool_Lattice.
Check @Bool_Semilattice.

(*
   本节说明幺半结构、幺半群、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
