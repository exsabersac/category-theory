(*
   本文件为测试：ProbeFunCreation426。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Eval.
Require Import Category.Instance.Fun.Limit.
Require Import Category.Instance.Fun.Creation.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe426_absent_name.

(* 相关说明。 （已译） *)

Section JointLift.

Context {J P X : Category} (D : J ⟶ [P, X])
  (N : ∀ p : obj[P], Cone (Eval p ◯ D)) (HN : ∀ p : obj[P], IsLimitCone (N p)).

(* controls: apex and every leg convert *)
Check (fun p : obj[P] => ev_lift_apex D N HN p).
Check (fun (p : obj[P]) (x : J) => ev_lift_leg D N HN p x).

(* N1 CONVERSION: whole cone record does not — coherence field a
 rebuilt opaque 证明 （已译） *)
Fail Example p426_ev_lift_record (p : obj[P]) :
  FCone (Eval p) (ev_lift D N HN) = N p := eq_refl.

(* readback: the family of evaluations jointly creates *)
Check (Fun_Eval_JointlyCreateLimit D).

End JointLift.

(* * ** B: strictness — restriction 恒等 对象 but not
 rebuild 函子 records （已译） *)

Section Strict.

Context {P X : Category}.

(* control: object action of the restriction *)
Example p426_res_obj_at (H : [P, X]) (p : P) :
  fobj[fobj[@Res P X] H] p = fobj[H] p := eq_refl.

(* N2 CONVERSION: restricted 函子 not discrete 函子 the
 same 对象 map — arrow fields differ （已译） *)
Fail Example p426_res_is_disc (H : [P, X]) :
  fobj[@Res P X] H = DiscreteCat_Functor' (fobj[H]) := eq_refl.

Section StrictLimit.

Context {J : Category} (D : J ⟶ [P, X]) (L : ∀ p : P, Limit (Eval p ◯ D)).

(* 相关说明。 （已译） *)
Example p426_strict_obj_ok (p : P) :
  fobj[fobj[@Res P X] (PointwiseLimit D L)] p = plim_obj D L p := eq_refl.

(* N3 CONVERSION: Riehl's strict clause — image canonical lift
 EQUAL given cone's apex downstairs — [eq] between 函子
 records refused （已译） *)
Fail Example p426_strict_record (N : Cone (@Res P X ◯ D)) :
  fobj[@Res P X] (PointwiseLimit D L) = vertex_obj[N] := eq_refl.

(* control: cones already in the image lift strictly *)
Check (fun M : Cone D => strict_self D M).

End StrictLimit.

End Strict.

(* * ** C: restriction 函子 more universe-general than 定理
 it serves （已译） *)

Section Wide.

Universe bigo smallh.
Constraint smallh < bigo.

(* a shape whose OBJECT universe sits strictly ABOVE its hom universe *)
Context (Pw : Category@{bigo smallh smallh}).
Context (Xw : Category@{bigo smallh smallh}).

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check ([Pw, Xw]).
Check (@ObjCat Pw).
Check (@Res Pw Xw).
Check ([Pw, Xw] ⟶ [Pw, Xw]).

(* N4 UNIVERSE: #425's corollary carries [jo <= jh] and is refused *)
Fail Check (fun HX : @Complete Xw => @Functor_Category_Complete Pw Xw HX).

(*
   本节说明自然变换、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check ([Pw, Xw] ⟶ Xw).

(* N6 UNIVERSE: hence #424's [Eval] itself, it 假设
 [∀ p, Limit (Eval p ◯ D)] [Res_CreatesLimit], cannot stated at
 shape, while [Res] can (control above) （已译） *)
Fail Check (@Eval Pw Xw).

End Wide.

(** ** D: readbacks *)

Check (@res_obj).
Check (@res_obj_at).
Check (@res_map).
Check (@eval_res_obj).
Check (@eval_res_map).
Check (@ptw_apex_readback).
Check (@ptw_leg_readback).
Check (@creation_apex).
Check (@creation_leg).
Check (@Res_Complete).
Check (@Res_continuous).

(** ** Guard block *)

Check @ObjCat.
Check @DiscInc.
Check @Res.
Check @ev_lift.
Check @ev_lift_apex.
Check @ev_lift_leg.
Check @Fun_pointwise_reflect.
Check @Fun_Eval_JointlyCreateLimit.
Check @Res_preserves.
Check @Res_CreatesLimit.
Check @Res_CreatesAllLimits.
Check @res_obj_at.
Check @strict_self.
Check @self_lift.
Check @PointwiseLimit.
Check @plim_obj.
Check @Functor_Category_Complete.
Check @DiscreteCat_Functor'.
Check @FCone.
Check @Cone.
Check @Complete.
Check @Limit.
Check @Eval.
Check @vertex_obj.
Check @fobj.
