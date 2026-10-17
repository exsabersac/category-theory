Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Limit.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本文件为测试：ProbeGrpLimit411。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check *)

(* 相关说明。 （已译） *)

Fail Check probe411_no_such_constant.

(* * ** Guards: every 常值 negative names, named outside every [Fail] （已译） *)

Check @IsALimit.
Check @Cone.
Check @sets_limit_ext.
Check @StrictlyCreatesLimits.
Check @CreatesAllLimits.
Check @Grp_Forget_creates_limits.
Check @Grp_Forget_StrictlyCreatesLimits.
Check @Grp_Forget.
Check @Grp_Complete.
Check @grp_setoid.
Check @vertex_obj.
Check @Sets_limit_obj.
Check @cone_apex.
Check @ConeSet_Complete.
Check @Sets_Complete.
Check @creates_limits_Complete.

(* 相关说明。 （已译） *)

Section UniverseBoundary.

Universes jo jh so sso.
Constraint jh < so.
Constraint so < sso.

Context (Ju : Category@{jo jh jh}).
Context (Fj : Ju ⟶ Sets@{so sso}).
Context (cu : obj[Sets@{so sso}]).

(* 相关说明。 （已译） *)
Check Ju.
Check Fj.
Check (@Cone Ju Sets@{so sso} Fj).

(* N1: UNIVERSE -- the donor. *)
Fail Check (@IsALimit Ju Sets@{so sso} Fj cu).

(* N2: UNIVERSE -- inherited; fires at the functor argument. *)
Fail Check (@sets_limit_ext Ju Fj cu).

End UniverseBoundary.

(* 相关说明。 （已译） *)

Check (Grp_Forget_creates_limits : CreatesAllLimits Grp_Forget).
Check (Grp_Forget_StrictlyCreatesLimits : StrictlyCreatesLimits Grp_Forget).

Fail Definition probe411_n3 : StrictlyCreatesLimits Grp_Forget :=
  Grp_Forget_creates_limits.

(* 相关说明。 （已译） *)

(*
   本节说明 ProbeGrpLimit411 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Grp_ConeSet_Complete : @Complete Grp :=
  creates_limits_Complete Grp_Forget ConeSet_Complete Grp_Forget_creates_limits.

Section Oracle.

Context {J : Category}.
Context (K : J ⟶ Grp).

(* 相关说明。 （已译） *)
Example probe411_ctrl_coneset :
  grp_setoid (vertex_obj[Grp_ConeSet_Complete J K]) = cone_apex (Grp_Forget ◯ K)
  := eq_refl.

(* N4: CONVERSION. *)
Fail Example probe411_n4 :
  grp_setoid (vertex_obj[Grp_ConeSet_Complete J K])
    = Sets_limit_obj (Grp_Forget ◯ K) := eq_refl.

(* 相关说明。 （已译） *)
Example probe411_ctrl_sets :
  grp_setoid (vertex_obj[Grp_Complete J K]) = Sets_limit_obj (Grp_Forget ◯ K)
  := eq_refl.

End Oracle.
