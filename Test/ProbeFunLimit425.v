(**
* Probe for Instance/Fun/Limit.v (issue #425)

    Pins the measured boundaries of pointwise limits in a functor category:
    the image of the pointwise cone under evaluation is the chosen limit
    cone in apex and legs but not as a record, the packaged corollaries
    must be universe-annotated at the definition, and [Limit] identifies
    the shape's hom level with the ambient's.  Every refutation command
    below was stripped ONE AT A TIME in a copy of the whole file and
    compiled alone with its error read, so each refusal is of the kind its
    label says.

    Numbering:
     instrument      an absent name, refused — the refutation keyword is
                     live in this file.
     N1 CONVERSION   [FCone (Eval p) (PointwiseLimitCone D L) = limit_cone
                     (L p)] is refused at [eq_refl] ("cannot unify"): the
                     coherence field is a rebuilt proof and [≈] is
                     Type-valued.  Controls: the apex and every leg convert
                     ([p425_fcone_apex], [p425_fcone_leg]), as do the diagram
                     at p, the object action, the leg components, the
                     mediator's components and the packaged limit's cone.
     N2 UNIVERSE     the corollary's body written BARE at top level
                     ([p425_bare_complete]) is refused at a category whose
                     object level sits strictly below its hom level
                     ("Cannot enforce jh = jo because jo < jh"): universe
                     minimization identifies the two.  Control: the
                     definition-annotated [Functor_Category_Complete] is
                     accepted at the same levels.
     N3 UNIVERSE     at a shape whose homs sit strictly below X's, [Limit F]
                     is refused ("Cannot enforce ch = ih because ih < ch") —
                     Structure/Limit.v's [Limit] is stated at [{J :
                     Category@{u0 u1 u1}} {C : Category@{u2 u1 u1}}] — while
                     the diagram F and [Cone F] are accepted (controls;
                     Structure/Cone.v's record is innocent).

    Positive controls, deliberately NOT written as refutations: the
    unfolded [Fun_HasLimitsOfShape] ascribes at Adjunction/Diagonal/
    Limit.v's [HasLimitsOfShape] ([p425_hlos]) and yields [LimitFunctor] on
    [P, X] ([p425_LimitFunctor]) — so the library file need not pay that
    import; and the presheaf corollaries.  No refutation is written for the
    absence of a colimit dual or of creation: those are #715's and #426's,
    metatheoretic here.

    Guard coverage: every constant a refutation names is also named
    outside a refutation command (the guard block at the end) — the
    exceptions, under the plain identifier tokenization with comments
    stripped, being the keyword itself, the name the refuted declaration
    would introduce and the instrument's absent name — so a renamed or
    removed constant breaks the build on a positive line rather than
    letting a refutation pass for the wrong reason.

--------
* 探测实例/函数/限制.v（问题 #425）

在函子范畴中固定逐点极限的测定边界：在顶点和箭头上，经过评估的逐点圆锥的像是选择的极限圆锥，但不是以记录的形式，打包的推论必须在定义时进行宇宙注释，并且 [Limit] 将形状的同态层级与环境的同态层级对应。下面的每个否定命令都是在整个文件的副本中一次去掉，然后单独编译并读取其错误的，因此每个拒绝都是其标签所说的类型。

编号：
     工具      一个缺失的名称，被拒绝——反驳关键字是
                     存在于此文件中。N1 转换   [FCone (Eval p) (PointwiseLimitCone D L) = limit_cone
                     (L p)] 在 [eq_refl] 处被拒绝（"无法统一"）：
                     一致性字段是重建的证明，并且 [≈]
                     是类型值。控制：顶点和每条边都转换
                     ([p425_fcone_apex], [p425_fcone_leg])，图表在 p 处，
                     对象操作，边组件，中介者组件以及打包的极限锥亦如此。
N2 宇宙     在顶层写有 BARE 的 corollary 的主体
                     ([p425_bare_complete]) 在对象层严格低于其 hom 层的类别中被拒绝
                     （“无法强制 jh = jo 因为 jo < jh”）：宇宙最小化识别了二者。控制：带定义注释的 [Functor_Category_Complete] 在相同层级被接受。N3 宇宙     在 shape 其 hom 层严格低于 X 的情况下，[Limit F] 被拒绝（“无法强制 ch = ih 因为 ih < ch”）——
                     Structure/Limit.v 的 [Limit] 在 [{J :
                     Category@{u0 u1 u1}} {C : Category@{u2 u1 u1}}] 上声明 — 而 diagram F 和 [Cone F] 被接受（控制；Structure/Cone.v 的记录是无害的）。

正向对照，故意不写作反驳：展开的 [Fun_HasLimitsOfShape] 归因于 Adjunction/Diagonal/Limit.v 的 [HasLimitsOfShape]（[p425_hlos]），并在 [P, X]（[p425_LimitFunctor]）上生成 [LimitFunctor] —— 因此库文件无需承担该导入；以及预层射影的推论。对于余极限对偶或创造的缺失没有写任何反驳：那些是 #715 和 #426 的问题，此处为元理论性。

守卫覆盖：每个常量如果在反驳中被命名，也会在反驳命令之外被命名（在末尾的守卫块中）——在去掉注释后的普通标识符标记下，例外情况是关键字本身、被反驳声明会引入的名称以及工具的缺失名称——因此，重命名或删除常量会在正向行上造成构建失败，而不是让反驳因错误的原因而通过。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Eval.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Fun.Limit.
Require Import Category.Adjunction.Diagonal.Limit.

Generalizable All Variables.

(* instrument: the refutation keyword is live / instrument：反驳关键词是 live *)
Fail Check probe425_absent_name.

(**
** A: the image of the pointwise cone under evaluation IS the chosen
       limit cone in apex and legs, but not as a record

--------
** A：在顶点和边上，点态锥在求值下的像确实是所选择的极限锥，但不是作为记录
*)

Section ImageCone.

Context {J P X : Category} (D : J ⟶ [P, X]) (L : ∀ p : P, Limit (Eval p ◯ D)).

(* readbacks: the diagram at p, the object action, the leg components / 回读：第 p 页的图表，物体动作，腿部组件 *)
Example p425_diagram_obj (p : P) (j : J) :
  fobj[Eval p ◯ D] j = fobj[fobj[D] j] p := eq_refl.

Example p425_plim_obj (p : P) :
  fobj[PointwiseLimit D L] p = vertex_obj[@limit_cone _ _ _ (L p)] := eq_refl.

Example p425_leg_component (j : J) (p : P) :
  transform[cone_leg (PointwiseLimitCone D L) j] p
  = limit_leg (limit_is_alimit (L p)) j := eq_refl.

(* controls: apex and every leg of the image cone convert / 控制：图像锥的顶点和每条边转换 *)
Example p425_fcone_apex (p : P) :
  vertex_obj[FCone (Eval p) (PointwiseLimitCone D L)]
  = vertex_obj[@limit_cone _ _ _ (L p)] := eq_refl.

Example p425_fcone_leg (p : P) (j : J) :
  cone_leg (FCone (Eval p) (PointwiseLimitCone D L)) j
  = cone_leg (@limit_cone _ _ _ (L p)) j := eq_refl.

(*
N1 CONVERSION: the whole record does not — its coherence field is a
   rebuilt proof and ≈ is Type-valued

--------
N1 转换：整个记录不是——它的连贯字段是一个重建的证明，并且 ≈ 是类型值
*)
Fail Example p425_fcone_record (p : P) :
  FCone (Eval p) (PointwiseLimitCone D L) = @limit_cone _ _ _ (L p) := eq_refl.

(* readbacks: the mediator and the packaged limit / 回读：调解人和包装限制 *)
Example p425_mediator (M : Cone D) (p : P) :
  transform[unique_obj (PointwiseIsLimitCone D L M)] p
  = plim_ump_map D L M p := eq_refl.

Example p425_limit_cone :
  @limit_cone _ _ _ (Functor_Category_pointwise_limit D L)
  = PointwiseLimitCone D L := eq_refl.

End ImageCone.

(** ** B: the packaged corollary must be annotated at the definition / ** B: 必须在定义处对打包的推论进行注释 *)

(*
The same body as [Functor_Category_Complete], written BARE at top level:
   universe minimization identifies P's object level with its hom level.

--------
与 [Functor_Category_Complete] 相同的主体，在顶层以 BARE 编写：
   宇宙最小化将 P 的对象级别与其同质级别对应起来。
*)
Definition p425_bare_complete {P X : Category} (HX : @Complete X) :
  @Complete ([P, X]) :=
  fun J D => Functor_Category_pointwise_limit D (fun p => HX J (Eval p ◯ D)).

Section Annotation.

Universe jo jh co ch.
Constraint jo < jh.

Context {P : Category@{jo jh jh}} {X : Category@{co ch ch}}.

(*
control: the annotated corollary is formable at a category whose object
   level sits strictly below its hom level

--------
控制：注释的推论可以在其对象层次严格低于其同态层次的范畴上形成
*)
Check (@Functor_Category_Complete P X).

(* N2 UNIVERSE: the bare one is refused there ("Cannot enforce jh = jo") / N2 宇宙：裸元在那里被拒绝（“无法强制 jh = jo”） *)
Fail Check (@p425_bare_complete P X).

End Annotation.

(** ** C: [Limit] identifies the shape's hom level with the ambient's / ** C: [Limit] 确认形状的同质层级与环境的同质层级 *)

Section ShapeHom.

Universe io ih co ch.
Constraint ih < ch.

Context {I : Category@{io ih ih}} {X : Category@{co ch ch}} (F : I ⟶ X).

(* controls: the diagram and a cone over it are accepted / 控件：图表及其上的圆锥被接受 *)
Check F.
Check (Cone F).

(*
N3 UNIVERSE: its limit is not — Structure/Limit.v's [Limit] is stated
   at [{J : Category@{u0 u1 u1}} {C : Category@{u2 u1 u1}}]

--------
N3 宇宙：它的极限不是——Structure/Limit.v 的 [Limit] 在 [{J : Category@{u0 u1 u1}} {C : Category@{u2 u1 u1}}] 被声明
*)
Fail Check (Limit F).

End ShapeHom.

(** ** D: the shape-level statement ascribes at the class downstream / ** D：形状级声明将属性归于下游类 *)

Definition p425_hlos {J P X : Category} (LX : HasLimitsOfShape J X) :
  HasLimitsOfShape J ([P, X]) := Fun_HasLimitsOfShape LX.

Definition p425_LimitFunctor {J P X : Category} (LX : HasLimitsOfShape J X) :
  [J, [P, X]] ⟶ [P, X] := LimitFunctor (p425_hlos (P:=P) LX).

(** ** E: the concrete corollaries / ** E：具体推论 *)

Check (@Presheaf_Complete).
Check (@Presheaf_Eval_PreservesAllLimits).
Check (@Fun_Sets_Complete).
Check (@Eval_PreservesLimitCone).
Check (@Eval_PreservesAllLimits).

(** ** Guard block / ** 防守格挡 *)

Check @plim_obj.
Check @plim_leg.
Check @plim_map.
Check @plim_map_unique.
Check @PointwiseLimit.
Check @PointwiseLimitCone.
Check @PointwiseIsLimitCone.
Check @plim_ump_map.
Check @Functor_Category_pointwise_limit.
Check @Functor_Category_Complete.
Check @Fun_HasLimitsOfShape.
Check @Eval.
Check @FCone.
Check @Cone.
Check @Limit.
Check @limit_cone.
Check @Complete.
Check @unique_obj.
Check @cone_leg.
Check @vertex_obj.
Check @transform.
Check @fobj.
