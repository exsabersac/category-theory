Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Quotient.
Require Import Category.Instance.Rng.Polynomial.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Omega.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.InverseLimit.
Require Import Category.Instance.Rng.Zp.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.
Open Scope category_scope.

(*
   本文件为测试：ProbeZp409。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument: a refutation command must be able to fail *)

Fail Check probe_zp409_no_such_name.

(** ** Guard block: every constant the negatives name, named outside them *)

Check @dsum.
Check @dadd.
Check @d7.
Check @d5.
Check @ResRing.
Check @ZComm.
Check @dpow.
Check @Int_Ring.
Check @zpd.
Check @zp_const.
Check @mraw.
Check @Zp_digits_iso.
Check @Zp.
Check @DigitSeq.
Check @Isomorphism.
Check @Rng.
Check @Sets.
Check @rig_setoid.
Check @carrier.
Check @mraw_1.
Check @RKills.
Check @ResIdeal.
Check @PrincipalIdeal.
(* [ResTower] is named by negative 7 and nowhere else; without this
   line a rename of it would turn that guard vacuously green, which
   the rename simulation caught. *)
Check @ResTower.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example probe_carry_leibniz :
  dsum 10%Z (dadd 10%Z d7 d5) 1%nat
    = (dsum 10%Z d7 1%nat + dsum 10%Z d5 1%nat)%Z := eq_refl.

Example probe_carry_control_n1_lhs :
  dsum 10%Z (dadd 10%Z d7 d5) 1%nat = 2%Z := eq_refl.

Example probe_carry_control_n1_rhs :
  (dsum 10%Z d7 1%nat + dsum 10%Z d5 1%nat)%Z = 12%Z := eq_refl.

Example probe_carry_control_n2 :
  dsum 10%Z (dadd 10%Z d7 d5) 2%nat
    = (dsum 10%Z d7 2%nat + dsum 10%Z d5 2%nat)%Z := eq_refl.

(*
   本节说明 ProbeZp409 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example probe_residue_leibniz :
  (2%Z : carrier (rig_setoid (ResRing ZComm 2%Z 1%nat))) = 0%Z := eq_refl.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example probe_residue_control :
  @equiv _ (rig_setoid (ResRing ZComm 2%Z 1%nat)) 2%Z 0%Z
  := inhabits (existT _ 1%Z eq_refl).

(*
   本节说明 ProbeZp409 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example probe_zpd_without_mod :
  ((-1)%Z / (@dpow Int_Ring 10%Z 0%nat))%Z = 9%Z := eq_refl.

Example probe_zpd_without_mod_value :
  ((-1)%Z / (@dpow Int_Ring 10%Z 0%nat))%Z = (-1)%Z := eq_refl.

Example probe_zpd_control :
  zpd 10%Z (zp_const 10%Z (-1)%Z) 0%nat = 9%Z := eq_refl.

(** ** Negative 4 (CONVERSION): [mraw] is the convolution, not the
       pointwise product *)

Fail Example probe_mraw_pointwise (a b : nat -> Z) :
  mraw a b 1%nat = (a 1%nat * b 1%nat)%Z := eq_refl.

(*
   本节说明 ProbeZp409 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Check (fun (p : Z) (Hp : (1 < p)%Z) =>
  (Zp_digits_iso p Hp : @Isomorphism Rng (Zp ZComm p) (DigitSeq p))).

Check (fun (p : Z) (Hp : (1 < p)%Z) =>
  (Zp_digits_iso p Hp
     : @Isomorphism Sets (rig_setoid (Zp ZComm p)) (DigitSeq p))).

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UniverseBoundary.

Universes ro rr rp.
Constraint ro < rr.
Constraint rr < rp.

(*
   本节说明 ProbeZp409 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Context (R : RingObject@{rp ro rr}) (Rc : RingComm R)
        (d : carrier (rig_setoid R)) (n : nat).

(* Controls: accepted at those very levels. *)
Check (PrincipalIdeal Rc d).
Check (ResIdeal Rc d n).
Check (ResRing Rc d n).

Fail Check (@RKills R (ResIdeal Rc d (S n)) (ResRing Rc d n)).

Fail Check (ResTower Rc d).

(*
   本节说明 ProbeZp409 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (R : obj[Rng]).

End UniverseBoundary.
