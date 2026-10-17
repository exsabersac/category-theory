Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Shapes.
Require Import Category.Theory.Skeleton.
Require Import Category.Theory.Equivalence.Strict.
Require Import Category.Theory.Connected.Components.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Limit.Constant.
Require Import Category.Structure.Limit.Initial.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Coq.
Require Import Category.Instance.One.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Ordinal.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Monoidal.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Adjunction.LeftInverse.
Require Import Category.Adjunction.FullFaithful.
Require Import Category.Adjunction.Diagonal.Connected.

Generalizable All Variables.

(*
   本文件为测试：ProbeConnected378。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------ *)
(** ** Instrument check *)

Fail Check probe378_no_such_constant_anywhere.

(* ------------------------------------------------------------------ *)
(** ** Controls: every guarded constant named outside a [Fail] *)

Check @diagonal_counit.
Check @diagonal_counit_strict.
Check @diagonal_counit_commutes.
Check @diagonal_counit_iso.
Check @diagonal_counit_Isomorphism.
Check @diagonal_counit_inverse.
Check @colim_const_inj_agree.
Check @colim_delta_nat.
Check @colim_diagonal_iso_Id.
Check @Diagonal_InjectiveOnObjects.
Check @diagonal_FFI.
Check @diagonal_RI.
Check @diagonal_fully_faithful_of_counit.
Check @ConstantColimits.
Check @cc_colim.
Check @cc_obj.
Check @cc_inj.
Check @constant_colimits_counit.
Check @colimit_is_lali_of_diagonal.
Check @colimit_lali_ffi.
Check @colimit_lali_ri.
Check @colim_diagonal_strict_Id.
Check @terminal_colimits.
Check @terminal_ConstantColimits.
Check @terminal_lali_of_diagonal.
Check @terminal_shape_connected.
Check @EvalAt.
Check @EvalAt_retracts.
Check @colimit_is_EvalAt.
Check @ordinal_ConstantColimits.
Check @ordinal_lali.
Check @two_ConstantColimits.
Check @two_lali.
Check @TwoGap.
Check @eval_not_left_adjoint.
Check @diagonal_limit_unit.
Check @diagonal_unit_commutes.
Check @lim_const_leg_agree.
Check @diagonal_unit_limit_iso.
Check @ConstantLimits.
Check @cl_limit.
Check @cl_obj.
Check @cl_leg.
Check @constant_limits_unit.
Check @diagonal_is_lari_of_limit.
Check @initial_limits.
Check @initial_ConstantLimits.
Check @initial_lari_of_limit.
Check @one_ConstantLimits.
Check @omega_ConstantLimits.
Check @omega_lari.
Check @two_discrete_counit_not_iso.
Check @two_discrete_no_ffi.
Check @two_discrete_no_lali.
Check @two_discrete_no_constant_colimits.
Check @two_discrete_objects_distinct.
Check @ordinal_two_not_degenerate.
Check @diagonal_counit_Isomorphism_to.
Check @lali_left_strict.
Check @lali_obj_strict.
Check @terminal_colimit_obj_strict.
Check @terminal_colimit_inj_strict.
Check @TwoGap_X.
Check @TwoGap_Y.
Check @lari_left_strict.
Check @lari_obj_strict.
Check @initial_limit_obj_strict.
Check @initial_limit_leg_strict.
Check @colim_diagonal_iso_Id_component.
Check @colim_diagonal_strict_Id_obj.

(* Donor constants the negatives below name. *)

Check @HasColimitsOfShape.
Check @colim_obj.
Check @colim_inj.
Check @LeftAdjointLeftInverse.
Check @colimit_unique_iso.
Check @const_IsAColimit.
Check @colim_acolimit.
Check @Diagonal.
Check @Two_Terminal.
Check @Fun.
Check @to.
Check @from.

(* ------------------------------------------------------------------ *)
(*
   本节说明（余）极限、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section StrictClauses.

Context {J C : Category}.
Context (L : HasColimitsOfShape J C).
Context (K : ConnectedNonempty J).
Context (P : ConstantColimits J C).

(* Negative 2 (CONVERSION). *)
Fail Example probe_apex_strict (c : C) :
  colim_obj L Δ[J](c) = c := eq_refl.

(* Control: with the record in hand the SAME equation is available, and
   under the terminal choice it holds by [eq_refl]. *)
Definition probe_apex_control (c : C) : colim_obj (cc_colim P) Δ[J](c) = c
  := cc_obj P c.

Example probe_apex_terminal (T : @Terminal J) (c : C) :
  colim_obj (@terminal_colimits J C T) Δ[J](c) = c := eq_refl.

(*
   本节说明始/终对象、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example probe_inj_strict (c : C) (j : J) :
  colim_inj L Δ[J](c) j = id[c] := eq_refl.

Example probe_inj_terminal (T : @Terminal J) (c : C) (j : J) :
  colim_inj (@terminal_colimits J C T) Δ[J](c) j = id[c] := eq_refl.

(*
   本节说明（余）极限、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example probe_counit_is_unique_iso (c : C) :
  diagonal_counit L c
    = to (@colimit_unique_iso J C Δ[J](c) _ _
            (colim_acolimit L Δ[J](c)) (const_IsAColimit c K))
  := eq_refl.

(* Control: the same statement at [≈] is what section (A) delivers, and
   the counit's own triangle is what proves it. *)
Definition probe_counit_control (c : C) (j : J) :
  diagonal_counit L c ∘ colim_inj L Δ[J](c) j ≈ id
  := diagonal_counit_commutes L c j.

(* Controls: both legs of the isomorphism read back on the nose. *)
Example probe_to_strict (c : C) :
  to (diagonal_counit_Isomorphism L K c) = diagonal_counit L c := eq_refl.

Example probe_inverse_strict (c : C) :
  from (diagonal_counit_Isomorphism L K c)
    = colim_inj L Δ[J](c) (cn_obj K) := eq_refl.

End StrictClauses.

(* ------------------------------------------------------------------ *)
(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Arity.

Context {J C : Category}.
Context (j0 : J).
Context (L : HasColimitsOfShape J C).
Context (P : ConstantColimits J C).

Fail Definition probe_lali_from_bare :
  LeftAdjointLeftInverse (@Diagonal C J) :=
  colimit_is_lali_of_diagonal j0 L.

(* Control: with the record it is exactly the headline. *)
Definition probe_lali_control :
  LeftAdjointLeftInverse (@Diagonal C J) :=
  colimit_is_lali_of_diagonal j0 P.

Example probe_lali_left_strict :
  lali_left probe_lali_control = ColimitFunctor (cc_colim P) := eq_refl.

End Arity.

(* ------------------------------------------------------------------ *)
(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ShapeAmbientHom.

Universes jo jh co ch.
Constraint jh < ch.

Context (Ju : Category@{jo jh jh}).
Context (Cu : Category@{co ch ch}).

(* Discriminating controls, accepted at the declared levels. *)
Check (obj[Ju]).
Check (obj[Cu]).
Check (Ju ⟶ Cu).

(* Negative 6 (FORMABILITY): the functor category itself. *)
Fail Check ([Ju, Cu]).

(* Negative 7 (FORMABILITY): the colimit hypothesis. *)
Fail Check (HasColimitsOfShape Ju Cu).

(* Negative 8 (FORMABILITY): the diagonal. *)
Fail Check (@Diagonal Cu Ju).

End ShapeAmbientHom.

(* ------------------------------------------------------------------ *)
(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section HomProof.

Universes ao ah ap xo xh xp.
Constraint ah < ap.

Context (Au : Category@{ao ah ap}).
Context (Xu : Category@{xo xh xp}).

Check (obj[Au]).
Check (Au ⟶ Xu).

Fail Check (@LeftAdjointLeftInverse Au Xu).

End HomProof.

(* ------------------------------------------------------------------ *)
(** ** (5) Readbacks the target's header claims, and the one it
       withdraws *)

Example probe_eval_retracts {J C : Category} (j : J) (c : C) :
  fobj[@EvalAt J C j] Δ[J](c) = c := eq_refl.

Example probe_colimit_is_EvalAt {J C : Category} (T : @Terminal J)
  (F : [J, C]) :
  fobj[ColimitFunctor (@terminal_colimits J C T)] F
    = fobj[@EvalAt J C (@terminal_obj J T)] F := eq_refl.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example probe_colimit_is_EvalAt_arrow {J C : Category}
  (T : @Terminal J) (F G : [J, C]) (t : F ~{[J, C]}~> G) :
  fmap[ColimitFunctor (@terminal_colimits J C T)] t
    = fmap[@EvalAt J C (@terminal_obj J T)] t := eq_refl.

Example probe_two_lali_left (C : Category) :
  lali_left (two_lali C)
    = ColimitFunctor (@terminal_colimits _2 C Two_Terminal) := eq_refl.

Example probe_lari_left {J C : Category} (I : @Initial J) :
  lari_left (@initial_lari_of_limit J C I) = @Diagonal C J := eq_refl.
