(**
* Probe for Instance/Fun/Creation.v (issue #426)

    Pins the measured boundaries of the creation development: three
    CONVERSION refusals (N1 the lifted cone's record against the given
    cone; N2 a restricted functor against the discrete functor on its
    object map; N3 Riehl's strict clause, an [eq] between functor records)
    beside their accepted apex and leg controls, and three UNIVERSE
    refusals (N4 #425's [Functor_Category_Complete]; N5 the type
    [[Pw, Xw] ⟶ Xw]; N6 #424's [Eval]) at a shape whose objects sit
    strictly above its homs, beside the accepted [ObjCat], [Res] and
    [[Pw, Xw] ⟶ [Pw, Xw]] — the restriction functor is more
    universe-general than the theorem it serves, and the bound [jo <= jh]
    enters through [Functor] over [Fun], not through this development.
    Each refutation was stripped one at a time in a copy of the whole
    file; the import list mirrors the target's.  Section D's readbacks and
    the guard block are positive controls.

--------
* 探测实例/趣味/创作.v（问题 #426）

固定创作开发的测量边界：三个转换拒绝（N1 提升圆锥的记录与给定圆锥的对比；N2 对象映射上的离散函子与受限函子的对比；N3 Riehl 的严格条款，是函子记录之间的 [eq]）旁边是它们被接受的顶点和边控制，以及三个宇宙拒绝（N4 #425 的 [Functor_Category_Complete]；N5 类型 [[Pw, Xw] ⟶ Xw；N6 #424 的 [Eval]），位于其对象严格高于它的同态的形状旁边，以及被接受的 [ObjCat]、[Res] 和 [[Pw, Xw] ⟶ [Pw, Xw] —— 限制函子比它所服务的定理具有更一般的宇宙，而绑定的 [jo <= jh] 是通过 [Functor] 经过 [Fun] 进入的，而不是通过此开发进入。每个反驳都是在整个文件的副本中一次逐个剥离的；导入列表与目标的相同。D 部分的回读和保护块是正控件。
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

(* instrument: the refutation keyword is live / instrument：反驳关键词是 live *)
Fail Check probe426_absent_name.

(**
** A: the lifted cone's image is the given cone in apex and legs, not
       as a record

--------
** A：被提升的圆锥的图像是给定的圆锥在顶点和侧边上，而不是作为记录
*)

Section JointLift.

Context {J P X : Category} (D : J ⟶ [P, X])
  (N : ∀ p : obj[P], Cone (Eval p ◯ D)) (HN : ∀ p : obj[P], IsLimitCone (N p)).

(* controls: apex and every leg convert / 控制：顶点和每条腿转换 *)
Check (fun p : obj[P] => ev_lift_apex D N HN p).
Check (fun (p : obj[P]) (x : J) => ev_lift_leg D N HN p x).

(*
N1 CONVERSION: the whole cone record does not — its coherence field is a
   rebuilt opaque proof

--------
N1 转换：整个圆锥记录没有——它的相干场是一个重建的不透明证明
*)
Fail Example p426_ev_lift_record (p : obj[P]) :
  FCone (Eval p) (ev_lift D N HN) = N p := eq_refl.

(* readback: the family of evaluations jointly creates / 回读：这一系列评估共同创建 *)
Check (Fun_Eval_JointlyCreateLimit D).

End JointLift.

(**
** B: strictness — the restriction is the identity on objects but not
       a rebuild of functor records

--------
** B：严格性——限制是在对象上的恒等，但不是函子记录的重建
*)

Section Strict.

Context {P X : Category}.

(* control: object action of the restriction / 控制：对限制的操作对象 *)
Example p426_res_obj_at (H : [P, X]) (p : P) :
  fobj[fobj[@Res P X] H] p = fobj[H] p := eq_refl.

(*
N2 CONVERSION: the restricted functor is not the discrete functor on the
   same object map — the arrow fields differ

--------
N2 转换：受限函子不是在相同对象映射上的离散函子——箭头域不同
*)
Fail Example p426_res_is_disc (H : [P, X]) :
  fobj[@Res P X] H = DiscreteCat_Functor' (fobj[H]) := eq_refl.

Section StrictLimit.

Context {J : Category} (D : J ⟶ [P, X]) (L : ∀ p : P, Limit (Eval p ◯ D)).

(* control: the canonical lift's image has the pointwise apexes on the nose / 控制：规范升力的图像在鼻子上有逐点的顶点 *)
Example p426_strict_obj_ok (p : P) :
  fobj[fobj[@Res P X] (PointwiseLimit D L)] p = plim_obj D L p := eq_refl.

(*
N3 CONVERSION: Riehl's strict clause — the image of the canonical lift
   EQUAL to a given cone's apex downstairs — is an [eq] between functor
   records and is refused

--------
N3 转换：Riehl 的严格条款——与下层给定锥顶相等的标准提升的图像——是在函子记录之间的 [eq] 并被拒绝
*)
Fail Example p426_strict_record (N : Cone (@Res P X ◯ D)) :
  fobj[@Res P X] (PointwiseLimit D L) = vertex_obj[N] := eq_refl.

(* control: cones already in the image lift strictly / 控制：图像中的圆锥严格抬起 *)
Check (fun M : Cone D => strict_self D M).

End StrictLimit.

End Strict.

(**
** C: the restriction functor is more universe-general than the theorem
       it serves

--------
** C：限制函子比它所服务的定理更具普适性
*)

Section Wide.

Universe bigo smallh.
Constraint smallh < bigo.

(* a shape whose OBJECT universe sits strictly ABOVE its hom universe / 一个其 OBJECT 宇宙严格位于其 hom 宇宙之上的形状 *)
Context (Pw : Category@{bigo smallh smallh}).
Context (Xw : Category@{bigo smallh smallh}).

(*
controls: the functor category, the discrete category on the objects,
   the restriction functor and the type of an endofunctor of [Pw, Xw] all
   form here — [DiscreteCat]'s homs are Prop-valued equalities, so the shape
   imposes no object ≤ hom, and a functor BETWEEN functor categories
   identifies two hom universes that both sit above [bigo]

--------
控制：函子范畴、对象上的离散范畴、限制函子以及 [Pw, Xw] 的一个自函子的类型都在这里形成 —— [DiscreteCat] 的态射是取值为 Prop 的等式，所以该形状对对象 ≤ 态射没有限制，并且函子范畴之间的函子会识别两个都位于 [bigo] 之上的态射宇宙
*)
Check ([Pw, Xw]).
Check (@ObjCat Pw).
Check (@Res Pw Xw).
Check ([Pw, Xw] ⟶ [Pw, Xw]).

(* N4 UNIVERSE: #425's corollary carries [jo <= jh] and is refused / N4 宇宙：#425 的推论带有 [jo <= jh] 并被拒绝 *)
Fail Check (fun HX : @Complete Xw => @Functor_Category_Complete Pw Xw HX).

(*
N5 UNIVERSE: the TYPE of an evaluation functor is refused — [Fun]'s hom
   universe (natural transformations quantify over P's objects) sits above
   [bigo], and [Functor] identifies it with [Xw]'s hom universe [smallh].
   This, not anything in Instance/Fun/Creation.v, is where [jo <= jh]
   enters: every constant below that mentions [Eval] inherits it

--------
N5 宇宙：评估函子的类型被拒绝 — [Fun] 的 hom 宇宙（自然变换对 P 的对象进行量化）位于 [bigo] 之上，而 [Functor] 将其与 [Xw] 的 hom 宇宙 [smallh] 关联起来。这就是 [jo <= jh] 的所在，而不是 Instance/Fun/Creation.v 中的任何内容：每个在此之下提到 [Eval] 的常量都会继承它
*)
Fail Check ([Pw, Xw] ⟶ Xw).

(*
N6 UNIVERSE: hence #424's [Eval] itself, and with it the hypothesis
   [∀ p, Limit (Eval p ◯ D)] of [Res_CreatesLimit], cannot be stated at
   this shape, while [Res] can (control above)

--------
N6 宇宙：因此 #424 的 [Eval] 本身，以及随之而来的 [Res_CreatesLimit] 的 [∀ p, Limit (Eval p ◯ D)] 假设，无法以这种形式陈述，而 [Res] 可以（上方控制）
*)
Fail Check (@Eval Pw Xw).

End Wide.

(** ** D: readbacks / ** D：复读 *)

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

(** ** Guard block / ** 防守格挡 *)

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
