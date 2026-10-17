(*
   本文件为测试：ProbeConstant356。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Fun.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Cone.Const.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Limit.Components.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Theory.Connected.Components.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Instance.Zero.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Instance.Coq.
Require Import Category.Structure.Limit.Absolute.
Require Import Category.Structure.Limit.Constant.

(* 相关说明。 （已译） *)
Fail Fail Check Category.

Section OppositeConstant.
Context {J C : Category}.
Context (c : C).

(* 相关说明。 （已译） *)
Example probe_op_diag_fobj (x : J) :
  fobj[Opposite_Functor Δ[J](c)] x
    = fobj[@Diagonal (C^op) (J^op) c] x := eq_refl.

Example probe_op_diag_fmap {x y : J^op} (f : x ~{J^op}~> y) :
  fmap[Opposite_Functor Δ[J](c)] f
    = fmap[@Diagonal (C^op) (J^op) c] f := eq_refl.

(* N1. *)
Fail Example probe_op_diag_strict :
  Opposite_Functor Δ[J](c) = @Diagonal (C^op) (J^op) c := eq_refl.

(* 相关说明。 （已译） *)
Check @const_image_fmap_equiv.

(* N2. *)
Fail Example probe_const_image_fmap {D : Category} (F : C ⟶ D)
  {x y : J} (f : x ~{J}~> y) :
  fmap[F ◯ Δ[J](c)] f = fmap[Δ[J](F c)] f := eq_refl.

End OppositeConstant.

(* 相关说明。 （已译） *)

Check @const_acone.
Check @const_cone.
Check @const_IsALimit.
Check @const_IsLimitCone.
Check @const_Limit.
Check @const_acocone.
Check @const_cocone.
Check @const_IsAColimit.
Check @const_IsColimitCocone.
Check @leg_zigzag.
Check @const_cone_step.
Check @const_cone_zigzag.
Check @const_cocone_step.
Check @const_cocone_zigzag.
Check @Diagonal_Faithful.
Check @Diagonal_Full.
Check @Diagonal_Full_via_limit.
Check @const_AbsoluteLimit.
Check @const_AbsoluteColimit.
Check @TwoX_not_terminal.
Check @zero_const_limit_IsTerminalObj.
Check @const_limit_not_from_bare_connected.
Check @two_discrete_const_not_limit.
Check @const_limit_not_from_point_alone.
Check @td_const_IsALimit_product.
Check @Diagonal_Zero_not_Faithful.
Check @Diagonal_Two_Discrete_not_Full.
(* 相关说明。 （已译） *)
Check @Diagonal.
Check @Opposite_Functor.
Check @ConnectedNonempty.
