Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Comp.
Require Import Category.Instance.Variety.
Require Import Category.Instance.Variety.Free.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.SpanningArrow.
Require Import Category.Instance.Variety.Spanning.

Generalizable All Variables.

(**
* Probe for Instance/Variety/Spanning.v

    Mac Lane §V.7 Remark 1 (pp. 127-128): the underlying-set functor of
    a variety has a solution set, the spanning arrows.  Issue #448.  The
    general theory has its own probe, Test/ProbeSpanningArrow448.v.

    The import list above is the target file's own import list,
    unabbreviated, plus the target.  Every negative was STRIPPED of its
    refutation keyword in a copy of this WHOLE file and its error read (a
    preamble-only scratch would drop the Section variables and
    misclassify).  Kinds: INSTANCE by the "(no type class instance
    found)" parenthetical; CONVERSION by "cannot unify".  The instrument
    check comes first; every library constant a negative names has a
    positive control.

--------
* 用于实例/类型/Spanning.v 的探测器

    Mac Lane 第 V.7 节 备注 1（第 127-128 页）：一个代数多样性的底层集合函子有一个解集，即跨射。问题 #448。一般理论有它自己的探测器，Test/ProbeSpanningArrow448.v。

    上面的导入列表是目标文件自己的导入列表，未缩写，加上目标文件。每个否定在该完整文件的副本中都被剥去了其反驳关键词，并读取其错误（仅前言的草稿会删除 Section 变量并错误分类）。种类：通过“(no type class instance found)”的括号判断为 INSTANCE；通过“cannot unify”判断为 CONVERSION。仪器检查优先；每个库常数的否定名称都有正控制。
*)

(** ** Instrument check / ** 仪表检查 *)

Fail Check variety_spanning_448_no_such_constant.

(** ** Positive controls / ** 阳性对照 *)

Check @Spanning.
Check @SubFactorsThrough.
Check @SpanningArrowsOutOf.
Check @SolutionSet.
Check @sol_index.
Check @HasWidePullbacks.
Check @SVariety.
Check @SVariety_Forget.
Check @CommEq.
Check @variety_spanning.
Check @variety_spanning_arrow.
Check @variety_solution_set.
Check @sgen_alg.
Check @sgen_corestrict.
Check @sgen_subobj.
Check @sgen_factors.
Check @SubAlg.
Check @sa_subobj.
Check @svariety_monic_iff_injective.
Check @svariety_iso.

Section Probes.

Context {S : UA.OpSignature} (E : UA.EqSignature S) (A : SVariety E).
Context (X : Sets) (h : X ~{Sets}~> SVariety_Forget E A).

(*
P4 -- positive control: the solution set's index IS the spanning
   arrows, on the nose.

--------
P4 -- 阳性对照：解集的指标正是张成箭头，完全符合。
*)
Example p448v_control :
  sol_index (variety_solution_set E X)
  = SpanningArrowsOutOf (SVariety_Forget E) X := eq_refl.

(*
P2 -- CONVERSION: the spanning arrow is the CORESTRICTION of h, not h
   itself; "cannot unify "SubObj A" and "SubObj (sgen_alg h)"".

--------
P2 -- 转换：延伸箭头是 h 的余限制，而不是 h 本身；“无法统一“SubObj A”和“SubObj (sgen_alg h)”。”
*)
Fail Definition p448v_h_not_spanning : Spanning (SVariety_Forget E) h :=
  variety_spanning E A X h.

(*
P3 -- CONVERSION: the generated subalgebra is a different object from
   A; "cannot unify "sgen_alg h" and "A"".

--------
P3 -- 转换：生成的子代数是与 A 不同的对象；“无法统一 'sgen_alg h' 和 'A'”。
*)
Fail Example p448v_gen_not_all : sgen_alg h = A := eq_refl.

(*
P5 -- CONVERSION: the index is not the generating set (the header's
   NOT-DELIVERED smallness claim); "cannot unify
   "sol_index (variety_solution_set E X)" and "carrier X"" -- the
   expected type prints "= X" through the coercion while the message
   names "carrier X".

--------
P5 -- 转换：该指标不是生成集（标题的未交付小性主张）；“无法统一‘sol_index (variety_solution_set E X)’和‘carrier X’” -- 期望的类型通过强制转换显示“= X”，而消息中指出“carrier X”.
*)
Fail Example p448v_index_not_X :
  sol_index (variety_solution_set E X) = carrier X := eq_refl.

End Probes.

(*
P1 -- INSTANCE: the general Lemma's route is not available in tree,
   there being no wide pullbacks of [SVariety]; "Cannot infer this
   placeholder of type "HasWidePullbacks (SVariety CommEq)" (no type
   class instance found)".  A [Definition] with a hole, never a [Check],
   which tolerates the open evar.  (CORRECTION, #451: "there being no
   wide pullbacks of [SVariety]" is no longer true.  Structure/Pullback/
   Wide/Complete.v's [Complete_HasWidePullbacks] applied to Instance/
   Variety/Limit.v's [SVariety_Complete] builds them.  The refusal below
   still stands, because class search registers neither of the two;
   Test/ProbeWellPowered451.v's N22 and its control pin exactly that.)

--------
P1 -- 实例：通用引理的路径在树中不可用，因为没有 [SVariety] 的广拉回；“无法推断这种类型为 'HasWidePullbacks (SVariety CommEq)' 的占位符（未找到类型类实例）”。一个带有空位的 [Definition]，从未是 [Check]，它容忍开放的 evar。（更正，#451：“不存在 [SVariety] 的广拉回”已不再成立。Structure/Pullback/Wide/Complete.v 中的 [Complete_HasWidePullbacks] 应用于 Instance/Variety/Limit.v 的 [SVariety_Complete] 可以构建它们。下面的拒绝仍然有效，因为类搜索没有注册这两者；Test/ProbeWellPowered451.v 的 N22 及其控制引脚正是这种情况。）
*)
Fail Definition p448v_no_wide_pullbacks :
  @HasWidePullbacks (SVariety CommEq) := _.
