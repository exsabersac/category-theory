Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Compose.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Mon.Free.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.MonoidRing.
Require Import Category.Instance.Rng.Free.

Generalizable All Variables.

(*
   本文件为测试：ProbeFreeRing400。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Positive controls

    Every constant named in a negative below is also named here, outside
    any [Fail], so a rename cannot silently vacate a guard. *)

Check @free_ring_via_ab.
Check @free_ring_via_mon.
Check @free_ring_composites_agree.
Check @RngUnderlyingAb.
Check @RngUnderlyingMon.
Check @free_ring_via_mon_adjunction.
Check @free_ring_via_mon_adjunction_ab.
Check @FreeAb.
Check @free_ab_adjunction.
Check @FreeMonSets.
Check @free_mon_sets_adjunction.
Check @FreeRngAb.
Check @free_rng_ab_adjunction.
Check @MonoidRingFunctor.
Check @zmring_adjunction.
Check @Rng_Forget_Ab.
Check @Rng_Forget_Mon.
Check @Rig_Forget_Mon.
Check (Rng_Forget_Mon : Rng ⟶ MonSets).

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example probe_fobj_agree (R : Rng) :
  fobj[RngUnderlyingAb] R = fobj[RngUnderlyingMon] R := eq_refl.

Example probe_fmap_agree (R S : Rng) (f : R ~{Rng}~> S) :
  fmap[RngUnderlyingAb] f = fmap[RngUnderlyingMon] f := eq_refl.

(** ** CONVERSION negatives

    Agreement on [fobj] and [fmap] does NOT extend to the functor
    records, nor to the [Adjunction] record built over them. *)

(* The two right adjoints are not the same record: the law fields are
   [Compose]'s obligations at different arguments. *)
Fail Example probe_underlying_records_agree :
  RngUnderlyingAb = RngUnderlyingMon := eq_refl.

(*
   本节说明伴随、幺半群、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe_ascribe_mon_at_ab
  : free_ring_via_mon ⊣ RngUnderlyingAb
  := free_ring_via_mon_adjunction.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ProbeMonRouteSetPin.

Universe puo puh.
Constraint Set < puh.

Check (Rng_Forget_Ab : Rng@{puo puh} ⟶ Ab).

Fail Check (Rng_Forget_Mon : Rng@{puo puh} ⟶ MonSets).

End ProbeMonRouteSetPin.

(*
   本节说明 ProbeFreeRing400 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example probe_free_ring_instrument : (true = false) := eq_refl.
