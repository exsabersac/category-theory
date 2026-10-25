(**
* Boundary probes for Construction/Free/Quiver/Limit.v (issue #332)

    Mac Lane CWM 2nd ed. §III.4, book p. 71 (def 8, remark 6).

    This file pins two measurements the target's header rests on, so that a
    later edit which quietly makes either FALSE breaks the build rather
    than silently invalidating the prose.

    The two negatives are of DIFFERENT KINDS and are kept lexically apart:

      * CONVERSION -- [dpath D p] and [fmap[FunctorOfDiagram D] p] are NOT
        convertible at a VARIABLE path.  [dpath] is a [Fixpoint] over the
        path while [InducedFunctor]'s arrow action elaborates as a
        [tlist'_rect], so neither reduces against the other until the path
        is a literal.  At a ONE-EDGE path they DO agree, and that is the
        positive control [dpath_singleton_is_fmap] shipped in the target.

      * FORMABILITY (universe) -- [Diagram G C] identifies C's hom and
        proof universes.  This is why [AGraphCone] displays
        [C : Category@{u u0 u0}] where the [ACone] it mirrors displays them
        apart, and it is INHERITED from the donor, not introduced by the
        target.  The controls below localize that: under
        [Constraint uh < up], [QuiverOfCat C] and [ACone c F] are BOTH
        formable and only [Diagram G C] is rejected, with
          "universe inconsistency: Cannot enforce up = uh because uh < up".
        The target's header declined to measure this and said so; the
        measurement is recorded here and the attribution is to
        Theory/Diagram.v's [Diagram], NOT to anything this issue added.
        SHARPER, AND IT CHANGES WHAT THE PIN MEANS: [Diagram] opens its
        section with an unannotated [Context {C : Category}]
        (Theory/Diagram.v), so the identification is a universe
        MINIMIZATION artifact -- the family
        Construction/Free/Quiver/Examples.v's header records -- and is
        repairable upstream with explicit binders.  It is not inherent
        content, and nothing here claims it is unavoidable.

    NOT PINNED HERE, and said plainly: the target also measures that the
    three WHOLE-RECORD round trips are refuted at [eq_refl] (the records
    have primitive projections with eta, so record equality is field
    equality, and the coherence fields are rebuilt proofs).  Those are
    stated in its header and are guarded nowhere -- they are not pinned
    below either, so a later edit could make them silently true.

    Every negative is paired with a positive control NAMING ITS OWN
    CONSTANTS, and the pairing was verified by RENAME SIMULATION over the
    constants appearing in the NEGATIVES.  The measured score is at the
    end of this file.

--------
* 用于 Construction/Free/Quiver/Limit.v 的边界探针（问题 #332）

Mac Lane 《CWM》第2版 §III.4，书页71（定义8，注释6）。

此文件固定了目标头部依赖的两个测量值，这样之后如果有编辑悄悄将任意一个设为 FALSE，就会导致构建失败，而不是默默地使文本无效。

这两个否定词属于不同类型，并在词汇上保持分开：

* 转换 -- [dpath D p] 和 [fmap[FunctorOfDiagram D] p] 在可变路径上不可转换。[dpath] 是路径上的 [Fixpoint]，而 [InducedFunctor] 的箭头操作展开为 [tlist'_rect]，因此在路径为字面值之前，它们都不会相互约简。在单边路径上，它们确实一致，这就是目标中附带的正控制 [dpath_singleton_is_fmap]。

* 可成型性（宇宙）——[Diagram G C] 识别 C 的同类和证明宇宙。这就是为什么 [AGraphCone] 显示 [C : Category@{u u0 u0}]，而 [ACone] 它所镜像的显示为分开，并且这是从捐赠方继承的，而不是由目标引入的。下面的控件对此进行了本地化：在 [Constraint uh < up] 下，[QuiverOfCat C] 和 [ACone c F] 都是可成型的，只有 [Diagram G C] 被拒绝，并显示“宇宙不一致：无法强制 up = uh，因为 uh < up”。目标的头部拒绝对此进行测量并明确表示如此；测量结果记录在此，并且归因于 Theory/Diagram.v 的 [Diagram]，而不是本问题中添加的任何内容。更清晰，并且它改变了引脚的含义：[Diagram] 以未注释的 [Context {C : Category}]（Theory/Diagram.v）开始其部分，因此该识别是一个宇宙最小化的人工产物——Family Construction/Free/Quiver/Examples.v 的头部记录——并且可以通过显式绑定在上游修复。这并非固有内容，此处也没有声称它是不可避免的。

这里没有固定，并且直言不讳地说：目标还测量到，三个完整记录的往返在 [eq_refl] 上被驳斥（记录具有带 eta 的原始投影，所以记录相等是字段相等，并且一致性字段是重建的证明）。这些在其头部中声明，并且没有任何保护——它们在下面也没有被固定，因此后来的编辑可能会使它们默默地成立。

每个阴性样本都与一个阳性对照配对，并为其命名自己的常量，并且通过在阴性样本中出现的常量上进行重新命名模拟验证了这种配对。测量的得分在此文件的末尾。
*)

Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Theory.Diagram.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Coq.
Require Import Category.Construction.Free.Quiver.Limit.

(**
** Instrument check

    A [Fail] that never fails would make every negative below vacuous.

--------
** 仪器检查

    一个永不失败的 [Fail] 会使下面的每个负面都变得无效。
*)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** Negative 1 (CONVERSION): dpath is not fmap at a variable path / ** 负 1（转换）：dpath 在变量路径上不是 fmap *)

Section PathNegative.

Context (G : Quiver) (C : Category) (D : Diagram G C) (x y : G)
        (p : @hom (FreeOnQuiver G) x y).

Fail Definition probe_dpath_is_fmap :
  dpath D p = fmap[FunctorOfDiagram D] p := eq_refl.

(*
Positive controls naming the negative's own constants.  At a ONE-EDGE
   path the two DO agree -- that is the target's own Example.

--------
阳性对照命名负面的自身常数。在单边路径上，这两个DO确实一致——也就是说，这是目标自身的示例。
*)
Check dpath_singleton_is_fmap.
Check (dpath D p).
Check (fmap[FunctorOfDiagram D] p).
Check (FunctorOfDiagram D).
Check (@FreeOnQuiver G).

End PathNegative.

(**
** Negative 2 (FORMABILITY, universe): Diagram identifies hom and proof

    Different KIND from Negative 1.

--------
** 负二（可成形性，宇宙）：图表识别同态和证明

与负一不同的类型。
*)

Section HomProofApart.

Universe uo uh up.
Constraint uh < up.

Context (G : Quiver) (C : Category@{uo uh up}) (c : obj[C])
        (J : Category) (F : J ⟶ C).

(*
Control (a): the underlying quiver of C is formable with hom and proof
   DECLARED APART, so the identification is not the quiver's doing.

--------
控制 (a)：C 的底层箭袋可以通过 hom 和 proof 单独声明来形成，因此这种识别不是箭袋自身的作用。
*)
Check (QuiverOfCat C).

(*
Control (b): the ordinary cone -- the thing [AGraphCone] mirrors -- is
   likewise formable here.

--------
控制 (b)：普通圆锥——[AGraphCone] 镜像的东西——在这里同样可以成型。
*)
Check (ACone c F).

(*
Control (c): THE ONE THAT ACTUALLY LOCALIZES.  [Diagram] is BY
   DEFINITION [QuiverHomomorphism G (QuiverOfCat C)], so ruling out the
   quiver and the cone does not rule out the homomorphism -- the obvious
   alternative culprit.  It IS formable here, so the identification is
   [Diagram]'s own.  An earlier revision of this file claimed the two
   controls above "localize" the cause; they do not, and this one does.

--------
控制 (c)：真正实现本地化的那个。[Diagram] 按定义就是 [QuiverHomomorphism G (QuiverOfCat C)]，因此排除振动和圆锥并不排除同态——明显的可疑对象。它在这里是可形成的，因此该识别归 [Diagram] 自身。该文件的早期版本声称上面两个控件“本地化”了原因；实际上并没有，而这个控件确实做到了。
*)
Check (QuiverHomomorphism G (QuiverOfCat C)).

(* The negative. / 否定 *)
Fail Check (Diagram G C).

End HomProofApart.

(** ** Controls for the delivered results / ** 已交付结果的控制 *)

Check AGraphCone.
Check GraphCone.
Check gcone_leg.
Check gcone_dpath.
Check ACone_of_AGraphCone.
Check AGraphCone_of_ACone.
Check Cone_of_GraphCone.
Check GraphCone_of_Cone.
Check Cone_of_GraphCone_round.
Check IsLimitGraphCone.
Check graph_limitcone.
Check limitcone_graph_limit.
Check graph_limit_iff_limitcone.
Check graph_limit_IsALimit.
Check GraphLimit.
Check graph_limit_med.
Check gcone_leg_fwd.
Check gcone_leg_bwd.

(** ** Non-vacuity controls / ** 非空性控制 *)

Check TriangleGraphCone.
Check triangle_graph_limit.
Check tri_gcone_of_arrow.
Check loop_gcone.
Check loop_paths_distinct.

(**
** MEASURED RENAME-SIMULATION SCORE

    The constants at risk are the ones the NEGATIVES name:

      Negative 1: [dpath], [fmap], [FunctorOfDiagram], [FreeOnQuiver]
      Negative 2: [Diagram]

    That is FIVE, and all five are named by a positive control above, so
    renaming any one breaks this file rather than turning its negative
    vacuously green.  An earlier revision counted SEVEN by folding in
    [QuiverOfCat] and [ACone]; those occur only in the controls, so their
    guarding is vacuously satisfied and they padded the denominator.  The
    simulation was run over all seven anyway and all seven are caught --
    the score is reproducible, but 5/5 is the honest accounting of what
    the negatives put at risk.

--------
** 测量的重命名模拟得分

冒险的常量是NEGATIVES所命名的那些：

  Negative 1: [dpath], [fmap], [FunctorOfDiagram], [FreeOnQuiver]
  Negative 2: [Diagram]

那是五个，并且这五个都被上面的正控制命名，因此重命名其中任何一个都会破坏此文件，而不是让它的负值形式自动变为绿色。早期修订通过将[QuiverOfCat]和[ACone]加入计算，总数为七；它们只出现在控制中，因此其保护条件被自动满足，并且它们使分母增加了。无论如何，模拟在所有七个上运行，并且全部七个都被捕获——得分是可重复的，但5/5是负值冒险情况的真实统计。
*)
