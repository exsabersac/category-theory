(*
   本文件为测试：ProbeLimitInitial334。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Cones.
Require Import Category.Instance.Cones.Limit.
Require Import Category.Instance.One.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Ordinal.
Require Import Category.Structure.Limit.Initial.

(** ** Instrument check

    A [Fail] that never fails would make every negative below vacuous. *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** Negative 1 (CONVERSION): the leg at the initial object is not [id] *)

Section LegAtInitial.

Context (J C : Category) (I : @Initial J) (F : J ⟶ C).

Fail Definition probe_initial_leg_is_id :
  initial_leg I F (@initial_obj J I) = id := eq_refl.

(* Positive controls naming the negative's own constants.  The [≈] form IS
   proved in the target, and every constant in the rejected equation is
   independently well-formed here. *)
Check (initial_leg_id I F).
Check (initial_leg I F).
Check (@initial_obj J I).

End LegAtInitial.

(** ** Negative 2 (CONVERSION, different cause): the whole-record identity *)

Section WholeRecord.

Context (J C : Category) (I : @Initial J) (F : J ⟶ C).

Fail Definition probe_limit_cones_record :
  @Limit_Cones J C F (initial_Cones_Terminal I F)
    = initial_Limit I F := eq_refl.

(* Positive controls.  The CONE components DO agree by [eq_refl] -- that is
   the target's own Example -- so what fails is the rebuilt universal
   property, not the data. *)
Check initial_Cones_strict.
Check (@Limit_Cones J C F).
Check (initial_Limit I F).
Check (initial_Cones_Terminal I F).

End WholeRecord.

(** ** Negative 3 (FORMABILITY, universe): IsALimit identifies J's levels

    A DIFFERENT KIND from 1 and 2. *)

Section UniverseIdentification.

Universe jo jh jp co ch cp.
Constraint jh < jp.

Context (J : Category@{jo jh jp}) (C : Category@{co ch cp})
        (F : J ⟶ C) (c : C) (x : J) (N : Cone F).

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (ACone c F).
Check (Cone F).

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Check (cone_leg N x).

(** ** Negative 5 (FORMABILITY, universe): IsLimitCone likewise *)

Fail Check (IsLimitCone N).

End UniverseIdentification.

(* Controls naming the two constants of negatives 4 and 5. *)
Check @cone_leg.
Check @IsLimitCone.

(*
   本节说明 ProbeLimitInitial334 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check @IsALimit.

Section UniverseIdentification2.

Universe jo2 jh2 jp2 co2 ch2 cp2.
Constraint jh2 < jp2.

Context (J : Category@{jo2 jh2 jp2}) (C : Category@{co2 ch2 cp2})
        (F : J ⟶ C) (c : C).

Fail Check (IsALimit F c).

End UniverseIdentification2.

(*
   本节说明 ProbeLimitInitial334 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UniverseControl.

Universe jo3 jh3 jp3 co3 ch3 cp3.

Context (J : Category@{jo3 jh3 jp3}) (C : Category@{co3 ch3 cp3})
        (F : J ⟶ C) (c : C) (x : J) (N : Cone F).

Check (IsALimit F c).
Check (cone_leg N x).
Check (IsLimitCone N).

End UniverseControl.

(** ** Controls for the delivered results *)

Check initial_leg.
Check initial_cone.
Check initial_med.
Check initial_med_commutes.
Check initial_med_unique.
Check initial_IsLimitCone.
Check initial_IsALimit.
Check limiting_iff_initial_leg_iso.
Check terminal_inj.
Check terminal_cocone.
Check terminal_IsColimitCocone.
Check terminal_IsAColimit.
Check colimiting_iff_terminal_inj_iso.
Check One_Initial.
Check point_IsALimit.
Check point_Cones_strict.
Check Ordinal_Succ_Terminal.
Check ordinal_succ_IsAColimit.
Check Omega_Initial.
Check Omega_no_Terminal.

(** ** Non-vacuity controls *)

Check point_Sets_med.
Check point_Sets_separates.
Check ordinal_omega_nonconstant.
Check ord_top_neq_bot.

(*
   本节说明（余）极限、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
