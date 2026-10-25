(**
* Boundary probes for Instance/Ab/DirectedColimit.v (issue #330)

    Mac Lane CWM 2nd ed. §III.3 Exercise 7, book p. 68.

    This file pins the two measurements the target's header states, so that
    a later edit which quietly makes either one FALSE breaks the build
    instead of silently invalidating the prose.

    The two negatives are of DIFFERENT KINDS and are kept lexically apart:

      * CONVERSION -- [fg_med_commutes] is stated at [≈] and NOT at Leibniz
        equality of whole morphisms.  The cause is the mediator's design:
        it evaluates the competing cocone at the CYCLIC object [cyc a],
        while the triangle's right-hand side evaluates it at [X].  Those
        are different objects of the index, so no amount of reduction
        identifies the two morphisms.

      * FORMABILITY (universe) -- [Instance/Proset.v]'s [Proset] cannot
        host THIS index.  [Proset] takes a stdlib [relation A], which is
        [A -> A -> Prop], while [FGHom] is [Type]-valued because
        [absub_mem] is.  Squashing the hom to [Prop] is formable (the
        positive control below) and is exactly what would break [fmap],
        which must APPLY an inclusion to transport a membership witness.

        READ THAT SCOPE EXACTLY.  It does NOT show the index cannot be
        hosted by [Proset] at all, and an earlier revision of this header
        said so ("[Proset] cannot host this index", full stop), which was
        wrong: with membership itself made [Prop]-valued, [FGHom] is
        natively a [relation], nothing is squashed, and [fmap] only applies
        a [Prop -> Prop] function -- a variant that compiles and yields the
        same colimit.  What this negative measures is a consequence of the
        target's [Type]-valued membership CONVENTION, not an impossibility.
        [Structure/Thin.v] records the [relation]-is-Prop-valued fact
        independently.

    PROBE HYGIENE.  This file carries the target's import list in the
    target's order, plus the target itself and [Relation_Definitions] (for
    [relation], named in Negative 2), and minus [Coq.micromega.Lia], which
    is a tactic library the probe has no use for.  It is therefore NOT
    literally "the target's full list" -- an earlier revision of this
    header said that, and it was wrong in both directions.  The point of
    the discipline stands: a short prefix leaves names like [cocone_inj]
    unresolved, and a [Fail] that succeeds because a reference is missing
    measures NOTHING.  Exactly that false pass was hit and discarded while
    these measurements were being made.

    Every negative is paired with a positive control NAMING ITS OWN
    CONSTANTS, and the pairing was verified by RENAME SIMULATION over the
    constants appearing in the NEGATIVES -- re-run after each control was
    added.  The measured score is recorded at the end of this file.

--------
* Instance/Ab/DirectedColimit.v 的边界探针（问题 #330）

Mac Lane 《CWM》第2版 §III.3 练习7，第68页。

该文件固定了目标头部声明的两个测量值，这样之后如果有编辑悄悄将其中任何一个设为 FALSE，就会导致构建失败，而不是默默地使文本无效。

这两个否定词属于不同类型，并在词汇上保持分开：

* 转换 —— [fg_med_commutes] 在 [≈] 上被陈述，而不是在 Leibniz 完整态射相等性下。原因在于中介者的设计：它在循环对象 [cyc a] 上评估竞争的上锥，而三角形的右侧在 [X] 上评估它。这些是指数中的不同对象，因此无论如何简化也无法将这两个态射认同。

* 可成形性（宇宙）——[Instance/Proset.v] 的 [Proset] 无法承载此索引。[Proset] 采用标准库 [relation A]，它是 [A -> A -> Prop]，而 [FGHom] 的值是 [Type]，因为 [absub_mem] 是。将同构压缩到 [Prop] 是可成形的（如下的阳性对照），这正是会破坏 [fmap] 的操作，因为它必须应用一个包含以传输成员证明。

仔细阅读该范围。它并没有显示该索引完全不能由 [Proset] 托管，而且该标题的早期版本确实这么说过（“[Proset] 无法托管此索引”，句号），这是错误的：由于成员本身被设为 [Prop] 值，[FGHom] 本质上是一个 [relation]，没有任何东西被压缩，而且 [fmap] 只是应用了一个 [Prop -> Prop] 函数——一个可以编译并产生相同余极限的变体。这个负面度量的结果是目标的 [Type] 值成员约定的后果，而不是不可能实现。[Structure/Thin.v] 独立记录了 [relation] 是 Prop 值的事实。

探针卫生。该文件包含目标的导入列表，顺序与目标一致，此外还包括目标本身和 [Relation_Definitions]（对于 [relation]，在负例 2 中提及），但不包括 [Coq.micromega.Lia]，这是一个探针无法使用的战术库。因此，它并不完全是“目标的完整列表”——该头文件的早期版本曾这样描述，但两方面都是错误的。该学科的重点仍然成立：一个短前缀会导致像 [cocone_inj] 这样的名称无法解析，而一个由于缺少引用而成功的 [Fail] 并不能测量任何东西。正是在进行这些测量时，正好遇到了并丢弃了这种错误的通过情况。

每个阴性都与一个阳性对照配对，并为其命名自己的常数，并通过重命名模拟对出现在阴性中的常数进行了配对验证——在每添加一个对照后重新运行。测量分数记录在此文件的末尾。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Thin.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Instance.Ab.DirectedColimit.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Relations.Relation_Definitions.

(**
** Instrument check

    A [Fail] that never fails would make every negative below vacuous.
    This one must fail for a reason that has nothing to do with the
    development.

--------
** 仪器检查

一个从不出错的 [Fail] 会使下面的每一个否定变得无效。这个必须失败的原因与开发无关。
*)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** Negative 1 (CONVERSION): the factorization triangle is not Leibniz / ** 负 1（转换）：因式分解三角形不是莱布尼茨 *)

Section TriangleNegative.

Context (A : AbObject) (N : Cocone (FGDiagram A)) (X : FGSub A).

Fail Definition probe_triangle_strict :
  fg_med N ∘ cocone_inj (FGCocone A) X = cocone_inj N X := eq_refl.

(*
Positive controls naming the negative's own constants.  The [≈] form IS
   proved in the target, and every constant in the rejected equation is
   independently well-formed here.

--------
正控命名负控自身的常量。[≈] 形式在目标中被证明，而被拒绝方程中的每个常量在这里都是独立良构的。
*)
Check (fg_med_commutes N X).
Check (fg_med N).
Check (cocone_inj (FGCocone A) X).
Check (FGCocone A).
Check (FGDiagram A).
Check (FGSub A).

End TriangleNegative.

(**
** Negative 2 (FORMABILITY): Proset cannot host THIS index

    [FGHom] is [Type]-valued -- because [absub_mem] is -- and so cannot be
    read as a stdlib [relation], which is [Prop]-valued.  This is a universe
    inconsistency, not a conversion failure: a different KIND from Negative
    1.  It measures the consequence of a CONVENTION, not an impossibility;
    see the scope paragraph in this file's header.

--------
** 负 2（可成形性）：Proset 无法承载此索引

[FGHom] 是 [Type] 值——因为 [absub_mem] 是——因此不能被读取为 stdlib [relation]，后者是 [Prop] 值。这是一个宇宙不一致性，而不是转换失败：与负 1 不同的 KIND。它衡量的是约定的后果，而不是不可能性；参见本文件头部的范围段落。
*)

Fail Check (FGHom ab_Z : relation (FGObj ab_Z)).

(*
Positive controls.  The squashed variant IS formable, which is what
   makes the negative a statement about [Prop] rather than about a
   malformed application; and every constant named in the negative is
   independently well-formed.

--------
阳性对照。压扁的变体是可形成的，这就是为什么阴性结果是关于 [Prop] 的声明，而不是关于一个格式错误的应用程序；并且阴性中提到的每个常量都是独立良构的。
*)
Check (fun X Y : FGObj ab_Z => inhabited (FGHom ab_Z X Y) : Prop).
Check FGHom.
Check FGObj.
Check ab_Z.
Check (relation (FGObj ab_Z)).

(**
** Controls for the delivered results

    These name the principal artifacts, so a rename anywhere in the target
    breaks this file loudly.

--------
** 已交付结果的控制

    这些命名了主要的工件，因此在目标中的任何重命名
    都会导致此文件严重出错。
*)

Check ab_fg_colimit.
Check ab_fg_isacolimit.
Check ab_fg_Colimit.
Check FGSub_directed.
Check FGSub_Thin.
Check AbSubgroup.
Check AbSubgroupAb.
Check absub_incl.
Check gen_sub.
Check gen_least.
Check InGen.
Check FinGen.
Check fg_join.
Check fg_of_list.
Check cyc.

(** ** Non-vacuity controls / ** 非空性控制 *)

Check Ztwo.
Check Zthree.
Check Ztwo_proper.
Check Zthree_proper.
Check Zsub_incomparable.
Check Zjoin_strictly_larger.
Check Ztwo_dup_iso.

(**
** MEASURED RENAME-SIMULATION SCORE

    The two negatives name these constants:

      Negative 1: [fg_med], [cocone_inj], [FGCocone]
      Negative 2: [FGHom], [FGObj], [ab_Z], [relation]

    All SEVEN are named by a positive control above, so renaming any one
    of them breaks this file rather than turning its negative vacuously
    green.  Score: 7/7, counted rather than recalled.

--------
** 测量的重命名模拟评分

    这两个负例命名了这些常量：

      负例 1: [fg_med], [cocone_inj], [FGCocone]
      负例 2: [FGHom], [FGObj], [ab_Z], [relation]

    上方的正控命名了全部七个，因此重命名其中任何一个
    都会破坏此文件，而不是使其负例徒然变为绿色。评分：7/7，计数而非回忆。
*)
