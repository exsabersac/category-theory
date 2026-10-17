(*
   本文件为测试：ProbeAlgLimit443。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.Continuity.
Require Import Category.Adjunction.GAFT.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Free.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Rng.Limit.
Require Import Category.Instance.Ab.FreeNotContinuous.

Generalizable All Variables.

(** ** Instruments *)

(* I1 NAME-ABSENCE: the refutation keyword is live.  If the harness were
   reporting refusals as successes, or the reverse, this line would say
   so. *)

Fail Check p443_absent_name.

(*
   本节说明 ProbeAlgLimit443 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example p443_i2 {J : Category} (K : J ⟶ Ab) (d : J) :
  cone_leg (@limit_cone _ _ _ (Ab_Complete J K)) d
    = Sets_limit_leg (Ab_Forget ◯ K) d := eq_refl.

(*
   本节说明 ProbeAlgLimit443 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example p443_i3 {J : Category} (K : J ⟶ Rng) :
  vertex_obj[Rng_Complete J K] = Sets_limit_obj (Rng_Forget ◯ K) := eq_refl.

(*
   本节说明 ProbeAlgLimit443 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section AbPointwise.

Context {J : Category}.
Context (K : J ⟶ Ab).

(* control: the carrier *)
Example p443_ab_carrier :
  cmon_setoid (ab_cmon (vertex_obj[Ab_Complete J K]))
    = Sets_limit_obj (Ab_Forget ◯ K) := eq_refl.

(* control: the leg, with the coercion I2 removes *)
Example p443_ab_leg (d : J) :
  cmon_map (cone_leg (@limit_cone _ _ _ (Ab_Complete J K)) d)
    = Sets_limit_leg (Ab_Forget ◯ K) d := eq_refl.

(* control: the addition *)
Example p443_ab_plus
  (a b : carrier (Sets_limit_obj (Ab_Forget ◯ K))) (d : J) :
  `1 (cmon_plus (vertex_obj[Ab_Complete J K]) a b) d
    = cmon_plus (K d) (`1 a d) (`1 b d) := eq_refl.

(*
   本节说明 ProbeAlgLimit443 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example p443_n1
  (a b : carrier (Sets_limit_obj (Ab_Forget ◯ K))) (d : J) :
  `1 (cmon_plus (vertex_obj[Ab_Complete J K]) a b) d
    = cmon_plus (K d) (`1 b d) (`1 a d) := eq_refl.

(* control: the zero *)
Example p443_ab_zero (d : J) :
  `1 (cmon_zero (vertex_obj[Ab_Complete J K])) d = cmon_zero (K d) := eq_refl.

(* N3 CONVERSION: the created zero is the coordinatewise zero and not its
   negation.  [ab_neg (K d) (cmon_zero (K d)) ≈ cmon_zero (K d)] is an
   ordinary consequence of [ab_neg_left]; it is not a conversion, so one
   operation cannot be read back as another even where they agree. *)

Fail Example p443_n3 (d : J) :
  `1 (cmon_zero (vertex_obj[Ab_Complete J K])) d
    = ab_neg (K d) (cmon_zero (K d)) := eq_refl.

(* control: the negation *)
Example p443_ab_neg
  (a : carrier (Sets_limit_obj (Ab_Forget ◯ K))) (d : J) :
  `1 (ab_neg (vertex_obj[Ab_Complete J K]) a) d
    = ab_neg (K d) (`1 a d) := eq_refl.

(*
   本节说明 ProbeAlgLimit443 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example p443_n2
  (a : carrier (Sets_limit_obj (Ab_Forget ◯ K))) (d : J) :
  `1 (ab_neg (vertex_obj[Ab_Complete J K]) a) d = `1 a d := eq_refl.

End AbPointwise.

(** ** B: at [Rng] the same, over five operations *)

Section RngPointwise.

Context {J : Category}.
Context (K : J ⟶ Rng).

(* control: the carrier, with the coercion I3 removes *)
Example p443_rng_carrier :
  rig_setoid (vertex_obj[Rng_Complete J K]) = Sets_limit_obj (Rng_Forget ◯ K)
  := eq_refl.

(* control: the leg *)
Example p443_rng_leg (d : J) :
  rig_map (cone_leg (@limit_cone _ _ _ (Rng_Complete J K)) d)
    = Sets_limit_leg (Rng_Forget ◯ K) d := eq_refl.

(* control: the addition *)
Example p443_rng_add
  (a b : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (rig_add (vertex_obj[Rng_Complete J K]) a b) d
    = rig_add (K d) (`1 a d) (`1 b d) := eq_refl.

(* control: the multiplication *)
Example p443_rng_mul
  (a b : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (rig_mul (vertex_obj[Rng_Complete J K]) a b) d
    = rig_mul (K d) (`1 a d) (`1 b d) := eq_refl.

(*
   本节说明 ProbeAlgLimit443 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example p443_n4
  (a b : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (rig_add (vertex_obj[Rng_Complete J K]) a b) d
    = rig_mul (K d) (`1 a d) (`1 b d) := eq_refl.

(*
   本节说明 ProbeAlgLimit443 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example p443_n6
  (a b : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (rig_mul (vertex_obj[Rng_Complete J K]) a b) d
    = rig_mul (K d) (`1 b d) (`1 a d) := eq_refl.

(* control: the additive unit *)
Example p443_rng_zero (d : J) :
  `1 (rig_zero (vertex_obj[Rng_Complete J K])) d = rig_zero (K d) := eq_refl.

(* control: the multiplicative unit *)
Example p443_rng_one (d : J) :
  `1 (rig_one (vertex_obj[Rng_Complete J K])) d = rig_one (K d) := eq_refl.

(*
   本节说明 ProbeAlgLimit443 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example p443_n5 (d : J) :
  `1 (rig_one (vertex_obj[Rng_Complete J K])) d = rig_zero (K d) := eq_refl.

(* control: the negation *)
Example p443_rng_neg
  (a : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (ring_neg (vertex_obj[Rng_Complete J K]) a) d
    = ring_neg (K d) (`1 a d) := eq_refl.

(*
   本节说明 ProbeAlgLimit443 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example p443_n7
  (a : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (ring_neg (vertex_obj[Rng_Complete J K]) a) d = `1 a d := eq_refl.

End RngPointwise.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example p443_ab_strict {J : Category} (K : J ⟶ Ab)
  (N : Cone (Ab_Forget ◯ K)) (HN : IsLimitCone N) :
  slift_eq (@screates _ _ _ _ _ (Ab_Forget_StrictlyCreatesLimit K) N HN)
    = eq_refl := eq_refl.

Example p443_rng_strict {J : Category} (K : J ⟶ Rng)
  (N : Cone (Rng_Forget ◯ K)) (HN : IsLimitCone N) :
  slift_eq (@screates _ _ _ _ _ (Rng_Forget_StrictlyCreatesLimit K) N HN)
    = eq_refl := eq_refl.

(* control: what the lift IS — a cone of abelian groups *)
Check (fun (J : Category) (K : J ⟶ Ab) N HN =>
         (slift_cone (@screates _ _ _ _ _ (Ab_Forget_StrictlyCreatesLimit K)
                        N HN) : Cone K)).

(*
   本节说明 ProbeAlgLimit443 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Check (fun (J : Category) (K : J ⟶ Ab) N HN =>
              (slift_cone (@screates _ _ _ _ _
                             (Ab_Forget_StrictlyCreatesLimit K) N HN)
                 : Cone (Ab_Forget ◯ K))).

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Ab_ConeSet_Complete : @Complete Ab :=
  creates_limits_Complete Ab_Forget ConeSet_Complete Ab_Forget_creates_limits.

Definition Rng_ConeSet_Complete : @Complete Rng :=
  creates_limits_Complete Rng_Forget ConeSet_Complete Rng_Forget_creates_limits.

Section Oracle.

Context {J : Category}.
Context (KA : J ⟶ Ab).
Context (KR : J ⟶ Rng).

(* control: over the cone-set oracle the carrier IS [cone_apex] *)
Example p443_ab_coneset :
  cmon_setoid (ab_cmon (vertex_obj[Ab_ConeSet_Complete J KA]))
    = cone_apex (Ab_Forget ◯ KA) := eq_refl.

(* N9 CONVERSION *)
Fail Example p443_n9 :
  cmon_setoid (ab_cmon (vertex_obj[Ab_ConeSet_Complete J KA]))
    = Sets_limit_obj (Ab_Forget ◯ KA) := eq_refl.

(* control *)
Example p443_rng_coneset :
  rig_setoid (vertex_obj[Rng_ConeSet_Complete J KR])
    = cone_apex (Rng_Forget ◯ KR) := eq_refl.

(* N10 CONVERSION *)
Fail Example p443_n10 :
  rig_setoid (vertex_obj[Rng_ConeSet_Complete J KR])
    = Sets_limit_obj (Rng_Forget ◯ KR) := eq_refl.

End Oracle.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* controls: the bridged hypothesis is accepted at both *)
Check (GAFT Ab_Forget Ab_Complete
            (Continuous_PreservesImageLimit Ab_Forget_creates_continuous)).
Check (GAFT Rng_Forget Rng_Complete
            (Continuous_PreservesImageLimit Rng_Forget_continuous)).

(*
   本节说明（余）极限、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (GAFT Ab_Forget Ab_Complete Ab_Forget_creates_continuous).

(*
   本节说明 ProbeAlgLimit443 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (GAFT Ab_Forget Ab_Complete Ab_Forget_PreservesAllLimits).

(* N13 CONVERSION *)
Fail Check (GAFT Rng_Forget Rng_Complete Rng_Forget_continuous).

(* N14 CONVERSION *)
Fail Check (GAFT Rng_Forget Rng_Complete Rng_Forget_PreservesAllLimits).

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* controls: the same type, twice *)
Check (Ab_Forget_creates_continuous : ContinuousFunctor Ab_Forget).
Check (Ab_Forget_Continuous : ContinuousFunctor Ab_Forget).

(* control: the new one IS creation applied, on the nose *)
Example p443_creates_continuous_term :
  Ab_Forget_creates_continuous
    = creates_limits_continuous Ab_Forget Sets_Complete Ab_Forget_creates_limits
  := eq_refl.

(* control: the old one IS RAPL applied, on the nose *)
Example p443_rapl_continuous_term :
  Ab_Forget_Continuous = right_adjoint_Continuous free_ab_adjunction
  := eq_refl.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example p443_n15 :
  Ab_Forget_creates_continuous = Ab_Forget_Continuous := eq_refl.

(* control: the apex-only corollary descends from the CREATION one *)
Example p443_ab_apex_descends :
  Ab_Forget_PreservesAllLimits
    = Continuous_PreservesAllLimits Ab_Forget_creates_continuous := eq_refl.

(* N16 CONVERSION: and not from the RAPL one, which would have been
   available and is not what the target used. *)

Fail Example p443_n16 :
  Ab_Forget_PreservesAllLimits
    = Continuous_PreservesAllLimits Ab_Forget_Continuous := eq_refl.

(* control: at [Rng] there is only one, and it descends the same way *)
Example p443_rng_apex_descends :
  Rng_Forget_PreservesAllLimits
    = Continuous_PreservesAllLimits Rng_Forget_continuous := eq_refl.

(*
   本节说明 ProbeAlgLimit443 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Check Ab_Forget_continuous.

(* N18 NAME-ABSENCE: the mirror.  There is no RAPL-style continuity
   constant at [Rng], and the [Rng] header's reason is measured there: no
   adjunction in tree has [Rng_Forget] as its right adjoint, so
   [right_adjoint_Continuous] does not reach it. *)

Fail Check Rng_Forget_Continuous.

(** ** G: reflection is not preservation, and the two creation classes are
        two types *)

(* control: what the target delivers *)
Check (fun (J : Category) (K : J ⟶ Ab) =>
         (Ab_Forget_reflects_limits K : ReflectsLimitCone K Ab_Forget)).

(*
   本节说明 ProbeAlgLimit443 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Check (fun (J : Category) (K : J ⟶ Ab) =>
              (Ab_Forget_reflects_limits K : PreservesLimitCone K Ab_Forget)).

(* controls: each target ships an inhabitant of both creation classes *)
Check (Ab_Forget_creates_limits : CreatesAllLimits Ab_Forget).
Check (Ab_Forget_StrictlyCreatesLimits : StrictlyCreatesLimits Ab_Forget).
Check (Rng_Forget_creates_limits : CreatesAllLimits Rng_Forget).
Check (Rng_Forget_StrictlyCreatesLimits : StrictlyCreatesLimits Rng_Forget).

(*
   本节说明 ProbeAlgLimit443 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition p443_n19 : StrictlyCreatesLimits Ab_Forget :=
  Ab_Forget_creates_limits.

Fail Definition p443_n20 : StrictlyCreatesLimits Rng_Forget :=
  Rng_Forget_creates_limits.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* N21 NAME-ABSENCE *)
Fail Check CMon_Complete.

(** ** I: guard block — every constant a refutation names, named outside
        every refutation *)

Check @carrier.
Check @Cone.
Check @cone_leg.
Check @cone_apex.
Check @limit_cone.
Check @IsLimitCone.
Check @vertex_obj.
Check @Sets_limit_obj.
Check @Sets_limit_leg.
Check @Sets_Complete.
Check @ConeSet_Complete.
Check @screates.
Check @slift_eq.
Check @slift_cone.
Check @CreatesAllLimits.
Check @StrictlyCreatesLimits.
Check @ReflectsLimitCone.
Check @PreservesLimitCone.
Check @ContinuousFunctor.
Check @Continuous_PreservesAllLimits.
Check @Continuous_PreservesImageLimit.
Check @creates_limits_Complete.
Check @creates_limits_continuous.
Check @right_adjoint_Continuous.
Check @GAFT.

Check @Ab.
Check @Ab_Forget.
Check @ab_cmon.
Check @ab_neg.
Check @cmon_setoid.
Check @cmon_map.
Check @cmon_plus.
Check @cmon_zero.
Check @Ab_Complete.
Check @Ab_ConeSet_Complete.
Check @Ab_Forget_StrictlyCreatesLimit.
Check @Ab_Forget_StrictlyCreatesLimits.
Check @Ab_Forget_creates_limits.
Check @Ab_Forget_creates_continuous.
Check @Ab_Forget_PreservesAllLimits.
Check @Ab_Forget_reflects_limits.
Check @Ab_Forget_Continuous.
Check @free_ab_adjunction.

Check @Rng.
Check @Rng_Forget.
Check @rig_setoid.
Check @rig_map.
Check @rig_add.
Check @rig_mul.
Check @rig_zero.
Check @rig_one.
Check @ring_neg.
Check @Rng_Complete.
Check @Rng_ConeSet_Complete.
Check @Rng_Forget_StrictlyCreatesLimit.
Check @Rng_Forget_StrictlyCreatesLimits.
Check @Rng_Forget_creates_limits.
Check @Rng_Forget_continuous.
Check @Rng_Forget_PreservesAllLimits.
Check @Rng_Forget_reflects_limits.
