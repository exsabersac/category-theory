Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.
Require Import Category.Instance.Top.Discrete.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Sets.Pointed.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Abelianization.
Require Import Category.Instance.Grp.Abelianize.
Require Import Category.Instance.Grp.Completion.
Require Import Category.Instance.CMon.Grothendieck.
Require Import Category.Instance.Sets.Pointed.Free.
Require Import Category.Instance.Rng.Free.

Generalizable All Variables.

(*
   本文件为测试：ProbeUniversalArrows312。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Positive controls

    Every constant named in a negative below is also named here outside
    any [Fail], so a rename cannot silently vacate a guard. *)

Check @Top_Discrete.
Check @Top_Forget.
Check @discrete_universal.
Check @disc_unit.
Check @abelianize_left.
Check @Abelianization_Functor.
Check @abelianize_adjunction.
Check @abelianize_adjunction_via_transform.
Check @completion_adjunction.
Check @grothendieck_adjunction.
Check @free_pointed_adjunction.
Check @free_rng_ab_universal_arrow.

(** ** Positive controls: the four rows of Mac Lane §III.1 Exercise 3

    Row (b) is discharged by #400's Instance/Rng/Free.v and is CITED
    here rather than rebuilt, which is what that issue's dependency note
    on #312 requires. *)

Example row_a_abelianization : Grp ⟶ Ab := abelianize_left.
Example row_b_free_ring (A : Ab) : UniversalArrow A Rng_Forget_Ab :=
  free_rng_ab_universal_arrow A.
Example row_d_basepoint : Sets ⟶ PointedSets := FreePointed.

(*
   本节说明伴随、函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Check (Top_Discrete ⊣ Top_Forget).

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example probe_left_is_pre_existing :
  abelianize_left = Abelianization_Functor := eq_refl.

(*
   本节说明 ProbeUniversalArrows312 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example probe_312_instrument : (true = false) := eq_refl.
