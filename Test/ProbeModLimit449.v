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
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Limit.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.

Generalizable All Variables.

(*
   本文件为测试：ProbeModLimit449。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check *)

(* "The reference rmod_limit_449_no_such_常值 was not found the
 current environment." （已译） *)
Fail Check rmod_limit_449_no_such_constant.

(** ** Positive controls *)

Check @RingObject.
Check @RMod.
Check @RMod_Complete.
Check @RMod_Forget_Ab.
Check @RMod_Forget.
Check @Ab_Forget.
Check @Ab_Complete.
Check @RMod_Forget_Ab_StrictlyCreatesLimit.
Check @RMod_Forget_Ab_CreatesLimit.
Check @RMod_Forget_Ab_StrictlyCreatesLimits.
Check @RMod_Forget_Ab_creates_limits.
Check @RMod_Forget_Ab_reflects_limits.
Check @RMod_Forget_Ab_creates_continuous.
Check @RMod_Forget_Ab_PreservesAllLimits.
Check @RMod_Forget_Ab_lifts_limits.
Check @RMod_Forget_composite_continuous.
Check @RMod_Forget_creates_continuous.
Check @RMod_Forget_PreservesAllLimits.
Check @RMod_lift_cone_unique.
Check @LimitMod.
Check @mlim_cone.
Check @mlim_leg.
Check @mlim_smul.
Check @mlim_smul_triangle.
Check @mlim_smul_unique.
Check @mlim_created.
Check @rmod_reflects.
Check @rmod_abcone_of.
Check @ContinuousFunctor.
Check @PreservesImageLimit.
Check @Continuous_PreservesImageLimit.
Check @Complete.
Check @Cone.
Check @FCone.
Check @cone_leg.
Check @vertex_obj.
Check @Limit.
Check @limit_cone.
Check @limit_leg.
Check @limit_is_alimit.
Check @IsLimitCone.
Check @Sets_limit_obj.
Check @Sets_limit_leg.
Check @rm_ab.
Check @rm_hom.
Check @rm_smul.
Check @cmon_setoid.
Check @cmon_map.
Check @cmon_plus.
Check @cmon_zero.
Check @ab_cmon.
Check @ab_neg.
Check @carrier.

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)
Example p449_r1 {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (L : Limit (RMod_Forget_Ab R ◯ K)) :
  RMod_Forget_Ab R (LimitMod K L) = vertex_obj[L] := eq_refl.

(* 相关说明。 （已译） *)
Example p449_r2 {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (L : Limit (RMod_Forget_Ab R ◯ K)) (j : J) :
  fmap[RMod_Forget_Ab R] (cone_leg (mlim_cone K L) j) = mlim_leg K L j
  := eq_refl.

(* R3 = [rmod_fcone_apex]. *)
Example p449_r3 {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (N : Cone K) :
  vertex_obj[FCone (RMod_Forget_Ab R) N] = rm_ab vertex_obj[N] := eq_refl.

(* R4 = [rmod_fcone_leg]. *)
Example p449_r4 {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (N : Cone K) (j : J) :
  cone_leg (FCone (RMod_Forget_Ab R) N) j = rm_hom (cone_leg N j) := eq_refl.

(* 相关说明。 （已译） *)
Example p449_r5 {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (L : Limit (RMod_Forget_Ab R ◯ K)) :
  RMod_Forget_Ab R (vertex_obj[RMod_Forget_Ab_lifts_limits K L])
    = vertex_obj[L] := eq_refl.

(* R6 = [rmod_lift_legs]. *)
Example p449_r6 {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (L : Limit (RMod_Forget_Ab R ◯ K)) (j : J) :
  fmap[RMod_Forget_Ab R]
    (cone_leg (@limit_cone _ _ _ (RMod_Forget_Ab_lifts_limits K L)) j)
    = limit_leg (limit_is_alimit L) j := eq_refl.

(* R7 = [rmod_forget_obj_agrees]: two forgetful 函子 agree on
 对象 -- positive half bridge whose negative half F1
 below. （已译） *)
Example p449_r7 {R : RingObject} (M : RMod R) :
  RMod_Forget R M = (Ab_Forget ◯ RMod_Forget_Ab R) M := eq_refl.

(* R8 = [rmod_forget_map_agrees]: and on morphisms. *)
Example p449_r8 {R : RingObject} {M N : RMod R} (f : M ~{RMod R}~> N) :
  fmap[RMod_Forget R] f = fmap[Ab_Forget ◯ RMod_Forget_Ab R] f := eq_refl.

Section RModComputed449.

Context {R : RingObject}.
Context {J : Category}.
Context (K : J ⟶ RMod R).

(* 相关说明。 （已译） *)
Example p449_r9 :
  cmon_setoid (ab_cmon (rm_ab (vertex_obj[RMod_Complete R J K])))
    = Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K)) := eq_refl.

(* R10 = [rmod_complete_plus]. *)
Example p449_r10
  (a b : carrier (Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K))))
  (d : J) :
  `1 (cmon_plus (rm_ab (vertex_obj[RMod_Complete R J K])) a b) d
    = cmon_plus (rm_ab (K d)) (`1 a d) (`1 b d) := eq_refl.

(* R11 = [rmod_complete_zero]. *)
Example p449_r11 (d : J) :
  `1 (cmon_zero (rm_ab (vertex_obj[RMod_Complete R J K]))) d
    = cmon_zero (rm_ab (K d)) := eq_refl.

(* R12 = [rmod_complete_neg]. *)
Example p449_r12
  (a : carrier (Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K))))
  (d : J) :
  `1 (ab_neg (rm_ab (vertex_obj[RMod_Complete R J K])) a) d
    = ab_neg (rm_ab (K d)) (`1 a d) := eq_refl.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example p449_r13 (r : R)
  (a : carrier (Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K))))
  (d : J) :
  `1 (rm_smul (vertex_obj[RMod_Complete R J K]) r a) d
    = rm_smul (K d) r (`1 a d) := eq_refl.

(* R14 = [rmod_complete_leg]. *)
Example p449_r14 (d : J) :
  cmon_map (rm_hom (cone_leg (@limit_cone _ _ _ (RMod_Complete R J K)) d))
    = Sets_limit_leg (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K)) d := eq_refl.

End RModComputed449.

(* 相关说明。 （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition p449_f1 (R : RingObject) :
  RMod_Forget R = Ab_Forget ◯ RMod_Forget_Ab R := eq_refl.

(*
   本节说明 ProbeModLimit449 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition p449_f2 (R : RingObject) : ContinuousFunctor (RMod_Forget R) :=
  RMod_Forget_composite_continuous R.

Example p449_f2_repair (R : RingObject) : ContinuousFunctor (RMod_Forget R) :=
  RMod_Forget_creates_continuous R.

(*
   本节说明（余）极限、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition p449_f3 (R : RingObject) :
  @PreservesImageLimit (RMod R) Ab (RMod_Forget_Ab R) :=
  RMod_Forget_Ab_creates_continuous R.

Example p449_f3_repair (R : RingObject) :
  @PreservesImageLimit (RMod R) Ab (RMod_Forget_Ab R) :=
  Continuous_PreservesImageLimit (RMod_Forget_Ab_creates_continuous R).

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition p449_f4 {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (L : Limit (RMod_Forget_Ab R ◯ K)) (r : R) (j : J) (a : vertex_obj[L]) :
  mlim_leg K L j (mlim_smul K L r a) = rm_smul (K j) r (mlim_leg K L j a)
  := eq_refl.

Example p449_f4_weak {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (L : Limit (RMod_Forget_Ab R ◯ K)) (r : R) (j : J) (a : vertex_obj[L]) :
  mlim_leg K L j (mlim_smul K L r a) ≈ rm_smul (K j) r (mlim_leg K L j a)
  := mlim_smul_triangle K L r j a.
