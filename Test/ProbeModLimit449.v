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

(**
* Probe for Instance/Mod/Limit.v

    Mac Lane, Categories for the Working Mathematician, 2nd ed., §V.1
    Theorems 2 and 3 and §V.7 Construction 1, printed pp. 111-112 and
    p. 128.  Issue #449.  The target creates every limit of [RMod R]
    from [Ab] along [RMod_Forget_Ab] and reads [RMod_Complete] off
    [Ab_Complete].

    The first fifteen requires above are the target file's own import
    list, unabbreviated, and the sixteenth is the target.  A short
    prefix is what makes a probe pass vacuously, so nothing is trimmed
    even where a require is redundant.  The last two are the probe's
    own, and are the only additions: the adjoint-functor-theorem
    boundary below names [PreservesImageLimit]
    (Construction/Comma/Limit.v) and its repair
    [Continuous_PreservesImageLimit] (Construction/Comma/Creation.v),
    neither of which the target imports.

    Every statement asserted to be refuted below has been STRIPPED of its
    refutation keyword in a copy of this WHOLE file, compiled alone, and
    its complete error read; a refutation that holds prints nothing under
    this repo's coqc.  Kinds, under THIS import list, the rubric being
    Test/ProbeSpanningArrow448.v's:

      CONVERSION  - "cannot unify A and B" parenthetical present.
      TYPING      - the "has type X while it is expected to have type Y"
                    opener with NO such parenthetical.
      INSTANCE    - "(no type class instance found)": such a negative
                    must be a [Definition], since a [Check] tolerates the
                    open evar and is then vacuously green.
      UNIVERSE    - "universe inconsistency".

    MEASURED, AND WORTH SAYING PLAINLY: all four negatives here open with
    the "has type ... while it is expected to have type ..." line AND
    carry the "cannot unify" parenthetical, so by that rubric all four
    are CONVERSION, not TYPING.  The issue brief anticipated TYPING for
    F2 and F3; the parenthetical decides it, and the exact text of each
    is quoted at the command.  F3's parenthetical is also not the one
    anticipated -- it reads "cannot unify "Cone (RMod_Forget_Ab R ◯ K)"
    and "IsLimitCone N"", the short names being those this import list
    puts in scope.

    The instrument check comes first; every library constant a negative
    names has a positive control outside any refutation command, and
    each negative is followed by the term that DOES ascribe there.

--------
* 探针用于实例/模块/限制.v

Mac Lane，《工作数学家的范畴论》，第2版，第V.1节 定理2和定理3，第V.7节 构造1，印刷页111-112和第128页。问题#449。目标沿着[RMod_Forget_Ab]从[Ab]生成[RMod R]的每一个极限，并从[Ab_Complete]上读取[RMod_Complete]。

前面列出的十五个 require 是目标文件自身的导入列表，未缩写，第十六个是目标。短前缀会使探针无条件通过，因此即使某个 require 冗余，也不会被剪裁。最后两个是探针自身的，这是唯一的补充：下面的伴随定理边界命名为 [PreservesImageLimit]（Construction/Comma/Limit.v）及其修复 [Continuous_PreservesImageLimit]（Construction/Comma/Creation.v），目标文件都未导入它们。

下面声称被驳斥的每个陈述都已在本文件的副本中被剥去其驳斥关键字，单独编译，并读取其完整错误；一个成立的驳斥在此仓库的 coqc 下不会打印任何内容。在这个导入列表下的类型，其标准是 Test/ProbeSpanningArrow448.v 的：

转换  - “无法统一 A 和 B”的括号内容存在。  类型检查  - “具有类型 X，但期望具有类型 Y”的提示，没有这样的括号内容。  实例  - “（未找到类型类实例）”：这样的否定必须是 [Definition]，因为 [Check] 可以容忍开放的 evar 并且随后在形式上为绿色。  宇宙  - “宇宙不一致”。

经过测量，并值得明确指出：这里的所有四个否定都以 “has type ... while it is expected to have type ...” 这一行开头，并带有 “cannot unify” 的括号说明，因此按照这个标准，四个都是转换（CONVERSION），而不是类型（TYPING）。问题简报预期 F2 和 F3 会是类型问题；括号说明决定了它，而每个具体文本都在指令中引用了。F3 的括号说明也不是预期的那一个——它写着 “cannot unify 'Cone (RMod_Forget_Ab R ◯ K)' 和 'IsLimitCone N'”，这些短名称是这个导入列表引入的作用域。

仪器检查排在首位；每个库常数为负，名称在任何反驳命令之外都有一个阳性对照，并且每个负数后面都跟着确实在那儿赋值的术语。
*)

(** ** Instrument check / ** 仪表检查 *)

(*
"The reference rmod_limit_449_no_such_constant was not found in the
   current environment."

--------
在当前环境中未找到引用 rmod_limit_449_no_such_constant。
*)
Fail Check rmod_limit_449_no_such_constant.

(** ** Positive controls / ** 阳性对照 *)

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

(**
** The fourteen [eq_refl] readbacks, restated

    Each is the statement of one of the target's fourteen [:= eq_refl]
    lines, re-elaborated here from library constants alone, at exactly
    the strength the target claims for it and no more.  Five compare
    morphisms, five objects, four elements; every witness is [eq_refl],
    so each of these is a positive control on a definitional identity,
    not a proof.  Two of them rest on transparency measured in the
    target: R5 and R6 stop if [RMod_Forget_Ab_StrictlyCreatesLimit] is
    closed opaquely, and that in turn rests on [mlim_created].

--------
** 十四个 [eq_refl] 的重述读回  

每一个都是目标的十四条 [:= eq_refl] 线路中的一条声明，这里仅从库常量重新阐述，且恰好以目标所声称的强度呈现，不多也不少。五个比较同态，五个对象，四个元素；每一个见证都是 [eq_refl]，因此其中每一个都是对定义性恒等式的阳性对照，而非证明。其中两个基于目标中测量的透明度：R5 和 R6 如果 [RMod_Forget_Ab_StrictlyCreatesLimit] 不透明关闭就会停止，而这又依赖于 [mlim_created]。
*)

(* R1 = [mlim_over_obj]: the lifted module's group IS the apex of [L]. / R1 = [mlim_over_obj]：提升模块的组是 [L] 的顶点。 *)
Example p449_r1 {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (L : Limit (RMod_Forget_Ab R ◯ K)) :
  RMod_Forget_Ab R (LimitMod K L) = vertex_obj[L] := eq_refl.

(* R2 = [mlim_over_legs]: and its legs ARE the legs of [L]. / R2 = [mlim_over_legs]：它的腿是[L]的腿。 *)
Example p449_r2 {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (L : Limit (RMod_Forget_Ab R ◯ K)) (j : J) :
  fmap[RMod_Forget_Ab R] (cone_leg (mlim_cone K L) j) = mlim_leg K L j
  := eq_refl.

(* R3 = [rmod_fcone_apex]. / R3 = [rmod_fcone_apex]. *)
Example p449_r3 {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (N : Cone K) :
  vertex_obj[FCone (RMod_Forget_Ab R) N] = rm_ab vertex_obj[N] := eq_refl.

(* R4 = [rmod_fcone_leg]. / R4 = [rmod_fcone_leg]. *)
Example p449_r4 {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (N : Cone K) (j : J) :
  cone_leg (FCone (RMod_Forget_Ab R) N) j = rm_hom (cone_leg N j) := eq_refl.

(* R5 = [rmod_lift_apex]: the lifted limit lies over [L] on the nose. / R5 = [rmod_lift_apex]：提升的限制位于[L]的正上方。 *)
Example p449_r5 {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (L : Limit (RMod_Forget_Ab R ◯ K)) :
  RMod_Forget_Ab R (vertex_obj[RMod_Forget_Ab_lifts_limits K L])
    = vertex_obj[L] := eq_refl.

(* R6 = [rmod_lift_legs]. / R6 = [rmod_lift_legs]. *)
Example p449_r6 {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (L : Limit (RMod_Forget_Ab R ◯ K)) (j : J) :
  fmap[RMod_Forget_Ab R]
    (cone_leg (@limit_cone _ _ _ (RMod_Forget_Ab_lifts_limits K L)) j)
    = limit_leg (limit_is_alimit L) j := eq_refl.

(*
R7 = [rmod_forget_obj_agrees]: the two forgetful functors agree on
   objects -- the positive half of the bridge whose negative half is F1
   below.

--------
R7 = [rmod_forget_obj_agrees]：这两个遗忘函子在对象上是一致的——桥的正半部分，其负半部分是下面的 F1。
*)
Example p449_r7 {R : RingObject} (M : RMod R) :
  RMod_Forget R M = (Ab_Forget ◯ RMod_Forget_Ab R) M := eq_refl.

(* R8 = [rmod_forget_map_agrees]: and on morphisms. / R8 = [rmod_forget_map_agrees]：以及在态射上。 *)
Example p449_r8 {R : RingObject} {M N : RMod R} (f : M ~{RMod R}~> N) :
  fmap[RMod_Forget R] f = fmap[Ab_Forget ◯ RMod_Forget_Ab R] f := eq_refl.

Section RModComputed449.

Context {R : RingObject}.
Context {J : Category}.
Context (K : J ⟶ RMod R).

(*
R9 = [rmod_complete_carrier]: the chosen limit's carrier IS the
   compatible-families setoid of Instance/Sets/Complete.v.

--------
R9 = [rmod_complete_carrier]：所选限制的承载体是 Instance/Sets/Complete.v 的兼容族等价类。
*)
Example p449_r9 :
  cmon_setoid (ab_cmon (rm_ab (vertex_obj[RMod_Complete R J K])))
    = Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K)) := eq_refl.

(* R10 = [rmod_complete_plus]. / R10 = [rmod_complete_plus]. *)
Example p449_r10
  (a b : carrier (Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K))))
  (d : J) :
  `1 (cmon_plus (rm_ab (vertex_obj[RMod_Complete R J K])) a b) d
    = cmon_plus (rm_ab (K d)) (`1 a d) (`1 b d) := eq_refl.

(* R11 = [rmod_complete_zero]. / R11 = [rmod_complete_zero]. *)
Example p449_r11 (d : J) :
  `1 (cmon_zero (rm_ab (vertex_obj[RMod_Complete R J K]))) d
    = cmon_zero (rm_ab (K d)) := eq_refl.

(* R12 = [rmod_complete_neg]. / R12 = [rmod_complete_neg]. *)
Example p449_r12
  (a : carrier (Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K))))
  (d : J) :
  `1 (ab_neg (rm_ab (vertex_obj[RMod_Complete R J K])) a) d
    = ab_neg (rm_ab (K d)) (`1 a d) := eq_refl.

(*
R13 = [rmod_complete_smul]: the ONE readback with no counterpart in
   Instance/Ab/Limit.v -- the created ACTION is componentwise at the
   chosen limit, even though that limit reaches its mediator through
   [creates_limiting].  F4 below pins what this does NOT say.

--------
R13 = [rmod_complete_smul]：唯一的回读在 Instance/Ab/Limit.v 中没有对应项——创建的 ACTION 在所选极限下是逐组件的，即使该极限是通过 [creates_limiting] 达到其中介的。下面的 F4 指明了这并没有说明的内容。
*)
Example p449_r13 (r : R)
  (a : carrier (Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K))))
  (d : J) :
  `1 (rm_smul (vertex_obj[RMod_Complete R J K]) r a) d
    = rm_smul (K d) r (`1 a d) := eq_refl.

(* R14 = [rmod_complete_leg]. / R14 = [rmod_complete_leg]. *)
Example p449_r14 (d : J) :
  cmon_map (rm_hom (cone_leg (@limit_cone _ _ _ (RMod_Complete R J K)) d))
    = Sets_limit_leg (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K)) d := eq_refl.

End RModComputed449.

(**
** The measured boundaries

    Four, each followed by the term that does stand there.

--------
** 测量的边界

    四个，每个后面都跟着确实存在的术语。
*)

(*
F1 -- CONVERSION: the two forgetful functors of Instance/Mod.v are not
   the same record, the three law fields being opaque.  "The term
   "eq_refl" has type "RMod_Forget R = RMod_Forget R" while it is
   expected to have type "RMod_Forget R = Ab_Forget ◯ RMod_Forget_Ab R"
   (cannot unify "RMod_Forget R" and "Ab_Forget ◯ RMod_Forget_Ab R")".
   R7 and R8 above are the positive halves: fobj and fmap DO agree.

--------
F1 -- 转换：Instance/Mod.v 中的两个遗忘函子不是相同的记录，这三个律字段是不可见的。术语“eq_refl”的类型是“RMod_Forget R = RMod_Forget R”，而期望类型为“RMod_Forget R = Ab_Forget ◯ RMod_Forget_Ab R”（无法统一“RMod_Forget R”和“Ab_Forget ◯ RMod_Forget_Ab R”）。上述的 R7 和 R8 是正半部分：fobj 和 fmap 确实一致。
*)
Fail Definition p449_f1 (R : RingObject) :
  RMod_Forget R = Ab_Forget ◯ RMod_Forget_Ab R := eq_refl.

(*
F2 -- CONVERSION, the consequence of F1 for continuity: "The term
   "RMod_Forget_composite_continuous R" has type "ContinuousFunctor
   (Ab_Forget ◯ RMod_Forget_Ab R)" while it is expected to have type
   "ContinuousFunctor (RMod_Forget R)" (cannot unify "Cone (RMod_Forget R
   ◯ K)" and "Cone (Ab_Forget ◯ RMod_Forget_Ab R ◯ K)")".  This is why
   the target carries the [rmod_abcone_of] bridge; the repaired term is
   next.

--------
F2 -- 转换，F1 对连续性的结果："术语 \"RMod_Forget_composite_continuous R\" 的类型是 \"ContinuousFunctor (Ab_Forget ◯ RMod_Forget_Ab R)\"，而预期类型是 \"ContinuousFunctor (RMod_Forget R)\"（无法统一 \"Cone (RMod_Forget R ◯ K)\" 和 \"Cone (Ab_Forget ◯ RMod_Forget_Ab R ◯ K)\"）"。这就是为什么目标携带 [rmod_abcone_of] 桥；修复后的术语如下。
*)
Fail Definition p449_f2 (R : RingObject) : ContinuousFunctor (RMod_Forget R) :=
  RMod_Forget_composite_continuous R.

Example p449_f2_repair (R : RingObject) : ContinuousFunctor (RMod_Forget R) :=
  RMod_Forget_creates_continuous R.

(*
F3 -- CONVERSION: continuity does NOT ascribe where Freyd's theorem
   and [representability_theorem] ask for [PreservesImageLimit], so
   [Continuous_PreservesImageLimit] must stand in the term.  "The term
   "RMod_Forget_Ab_creates_continuous R" has type "ContinuousFunctor
   (RMod_Forget_Ab R)" while it is expected to have type
   "PreservesImageLimit" (cannot unify "Cone (RMod_Forget_Ab R ◯ K)" and
   "IsLimitCone N")": the two types quantify over a cone and over a
   limit in different positions.  Consumers of [RMod_Complete] meet this
   at the application.

--------
F3 -- 转换：连续性并没有归因于 Freyd 定理和 [representability_theorem] 需要 [PreservesImageLimit]，因此 [Continuous_PreservesImageLimit] 必须出现在该项中。“RMod_Forget_Ab_creates_continuous R” 这个项的类型是 “ContinuousFunctor (RMod_Forget_Ab R)”，而期望的类型是 “PreservesImageLimit”（无法统一 “Cone (RMod_Forget_Ab R ◯ K)” 和 “IsLimitCone N”）：这两种类型在不同位置对圆锥和极限进行了量化。[RMod_Complete] 的使用者在应用中遇到这一点。
*)
Fail Definition p449_f3 (R : RingObject) :
  @PreservesImageLimit (RMod R) Ab (RMod_Forget_Ab R) :=
  RMod_Forget_Ab_creates_continuous R.

Example p449_f3_repair (R : RingObject) :
  @PreservesImageLimit (RMod R) Ab (RMod_Forget_Ab R) :=
  Continuous_PreservesImageLimit (RMod_Forget_Ab_creates_continuous R).

(*
F4 -- CONVERSION, the boundary of R13: componentwise computation of
   the action is a fact about the CHOSEN limit, not about the lifted
   action in general.  At an arbitrary [L] the defining triangle holds
   only up to [≈]: "The term "eq_refl" has type "mlim_leg K L j
   (mlim_smul K L r a) = mlim_leg K L j (mlim_smul K L r a)" while it is
   expected to have type "mlim_leg K L j (mlim_smul K L r a) = rm_smul
   (fobj[K] j) r (mlim_leg K L j a)" (cannot unify "mlim_leg K L j
   (mlim_smul K L r a)" and "rm_smul (fobj[K] j) r (mlim_leg K L j a)")"
   -- the action being a mediator of the abstract limit there.  The
   available strength is the [≈] of [mlim_smul_triangle], next.

--------
F4 -- 转换，R13的边界：按分量计算作用是关于所选择极限的事实，而不是关于一般提升作用的。在任意[L]处，定义三角形只成立到[≈]：“术语 'eq_refl' 的类型是 'mlim_leg K L j (mlim_smul K L r a) = mlim_leg K L j (mlim_smul K L r a)'，而期望的类型是 'mlim_leg K L j (mlim_smul K L r a) = rm_smul (fobj[K] j) r (mlim_leg K L j a)'（无法统一 'mlim_leg K L j (mlim_smul K L r a)' 和 'rm_smul (fobj[K] j) r (mlim_leg K L j a)')”——这里的作用充当抽象极限的中介。可用的强度是[≈]的[mlim_smul_triangle]，下一步。
*)
Fail Definition p449_f4 {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (L : Limit (RMod_Forget_Ab R ◯ K)) (r : R) (j : J) (a : vertex_obj[L]) :
  mlim_leg K L j (mlim_smul K L r a) = rm_smul (K j) r (mlim_leg K L j a)
  := eq_refl.

Example p449_f4_weak {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (L : Limit (RMod_Forget_Ab R ◯ K)) (r : R) (j : J) (a : vertex_obj[L]) :
  mlim_leg K L j (mlim_smul K L r a) ≈ rm_smul (K j) r (mlim_leg K L j a)
  := mlim_smul_triangle K L r j a.
