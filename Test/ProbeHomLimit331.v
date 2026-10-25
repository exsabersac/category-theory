(**
* Boundary probes for Functor/Hom/Limit.v (issue #331)

    Mac Lane CWM 2nd ed. §III.4, book p. 70.

    This file pins the two measurements the target's header rests on, so
    that a later edit which quietly makes either FALSE breaks the build
    rather than silently invalidating the prose.

    One negative remains, and the section that used to hold a second is
    now a positive control.  They are of DIFFERENT KINDS and are kept
    lexically apart:

      * FORMABILITY (universe) -- REPAIRED, and recorded as a correction.
        An earlier revision stated this as Negative 2.  The target proves
        its product corollaries DIRECTLY rather than deriving them from
        the cone-level headline, and the header's stated reason was that
        routing them through the discrete-diagram presentation would pin
        the ambient category's hom and proof universes to [Set].  The
        negative pinned exactly that, and localized the cause:
        [DiscreteCat_Functor] ALONE was formable over a category whose hom
        universe is strictly above [Set], and what was refused was the
        COMBINATION -- [IsLimitCone] identifies the shape's hom-and-proof
        universe with the ambient category's, while
        [DiscreteCat_Functor]'s UNANNOTATED declaration instantiated
        [DiscreteCat@{u Set Set}].  Stripped, the error read
          "universe inconsistency: Cannot enforce Set = uh",
        displaying [Cone@{_ Set Set uo uh uh}] against a [Cone] whose
        shape and ambient levels are one and the same.

        THE ATTRIBUTION WAS RIGHT AND THE DEFECT IS NOW FIXED.
        [DiscreteCat] itself is
        [DiscreteCat@{o h p} (A : Type@{o}) : Category@{o h p}] with hom
        and proof FREE, and [DiscreteCat@{Set uh uh} bool] elaborates
        under [Constraint Set < uh]; the header said so, and added that a
        re-annotated discrete-diagram functor would LIFT the blocking step
        entirely, so that what the negative pinned was a donor ANNOTATION
        defect and not a structural obstruction.  In the PR "algebraic
        carriers are sets" (2026-09-17) that annotation was applied in
        place -- [DiscreteCat_Functor@{o h p uo uh up +}] at
        Instance/Discrete.v -- and the prediction held: the command is
        now ACCEPTED, and it is kept below as a positive control at
        exactly the levels that used to refuse it.  Dropping the
        annotation would refuse it again and break this file.

        An earlier draft of this probe aimed the negative at
        [DiscreteCat_Functor] by itself and it did NOT refuse -- the guard
        was pointed at the wrong constant.  Recorded because a negative
        aimed at the wrong constant is a false guard, not a small slip;
        and an earlier draft ALSO mis-attributed the [Set] to the shape.

      * TYPING -- written [FCone (HomFrom unit) (…)] elaboration reports
          "HomFrom  has type Coq ⟶ Sets while it is expected to have
           type Coq ⟶ Coq".
        THE CAUSE IS [HomFrom]'s IMPLICIT [{C : Category}], undeterminable
        from a bare [unit : Type] -- NOT [FCone]'s category arguments.
        Those may be left implicit: [FCone (HomFrom (unit : obj[Coq])) (…)]
        and [fun u : Coq => FCone (HomFrom u) (…)] both elaborate, and the
        target's own [coq_hom_limit_cone] writes them implicitly.  An
        earlier revision of this header said the three category arguments
        "cannot be implicit" and that an ascription does not repair it;
        both were wrong, and the controls below now name the object
        ascription that does repair it.

    NOT PINNED HERE, and said plainly: the header's claim that the direct
    product statements carry no [Set] at all is exercised as a positive
    CONTROL below (they elaborate over a category with hom universe above
    [Set]), not as a negative -- there is nothing to refute.

    Every negative is paired with a positive control NAMING ITS OWN
    CONSTANTS, and the pairing was verified by RENAME SIMULATION over the
    constants appearing in the NEGATIVES.  The measured score is recorded
    at the end of this file.

--------
* Functor/Hom/Limit.v 的边界探针（问题 #331）

Mac Lane《CWM》第2版 §III.4，第70页。

该文件固定了目标头部所在的两个测量值，这样之后如果有编辑悄悄将任意一个设为 FALSE，就会导致构建失败，而不是默默地使文本无效。

仍然存在一个阴性对照，而原本用来放第二个的部分现在是阳性对照。它们是不同类型的，并且在词汇上保持分开：

* 可成形性（宇宙）——已修复，并记录为更正。早期的修订将其表示为负2。该目标直接证明其积的推论，而不是从锥级标题推导它们，标题中说明的原因是，将它们通过离散图演示进行处理会将环境类别的同构和证明宇宙固定到 [Set]。负面正好固定了这一点，并定位了原因：[DiscreteCat_Functor] 仅能在其同构宇宙严格高于 [Set] 的类别上形成，而被拒绝的是组合——[IsLimitCone] 将形状的同构与证明宇宙与环境类别的宇宙识别起来，而 [DiscreteCat_Functor] 的未注释声明实例化了 [DiscreteCat@{u Set Set}]。剥离后，错误显示为“宇宙不一致：无法强制执行 Set = uh”，显示 [Cone@{_ Set Set uo uh uh}] 与其形状和环境层级相同的 [Cone]。

归属是正确的，缺陷现在已经修复。[DiscreteCat] 本身是 [DiscreteCat@{o h p} (A : Type@{o}) : Category@{o h p}]，带有 hom 并且是无 proof 的，[DiscreteCat@{Set uh uh} bool] 在 [Constraint Set < uh] 下进行了详细说明；头部是这么写的，并补充说，重新注释的离散图示函子将完全提升阻塞步骤，因此被标记为负的实际上是一个捐赠者注释缺陷，而不是结构性障碍。在 PR “代数载体是集合”（2026-09-17）中，该注解被应用在本地 —— [DiscreteCat_Functor@{o h p uo uh up +}] 位于 Instance/Discrete.v —— 并且预测得以验证：该命令现在已被接受，并且它在下面保持作为正向控制，正好处于以前拒绝它的级别。移除该注解将再次导致拒绝并破坏此文件。

该探针的早期草稿仅将负向指向 [DiscreteCat_Functor]，并且它并未拒绝——守卫指向了错误的常量。记录此情况是因为指向错误常量的负向是一个错误的守卫，而不是一个小错误；早期草稿还错误地将 [Set] 归因于该形状。

* 输入 -- 编写 [FCone (HomFrom unit) (…)] 展开报告
          “HomFrom 的类型是 Coq ⟶ 集合，而预期类型是 Coq ⟶ Coq”。原因是 [HomFrom] 的隐式 [{C : Category}]，无法通过一个裸 [unit : Type] 确定 —— 不是 [FCone] 的类别参数。那些可以保持隐式：[FCone (HomFrom (unit : obj[Coq])) (…)]
        并且 [fun u : Coq => FCone (HomFrom u) (…)] 都会展开，目标自身的 [coq_hom_limit_cone] 也会隐式地编写它们。这个标题的早期版本说三个类别参数“不能是隐式的”，并且赋型（ascription）无法修复它；两者都是错误的，下面的控件现在指出了可以修复它的对象赋型。

这里没有置顶，并且明确表示：标题声称直接产品声明完全不包含 [Set] 的说法在下面被用作正向控制（他们在 [Set] 之上的同类宇宙中对一个类别进行了详细说明），而不是作为负向——没有什么可反驳的。

每个阴性都与一个阳性对照配对，并命名其自身的常数，并且通过对阴性中出现的常数进行重命名模拟来验证配对。测量得分记录在此文件的末尾。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Functor.Hom.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Limit.Cartesian.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Instance.Coq.
Require Import Category.Functor.Hom.Limit.

(**
** Instrument check

    A [Fail] that never fails would make every negative below vacuous.

--------
** 仪器检查

    一个永不失败的 [Fail] 会使下面的每个负面都变得无效。
*)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** Negative 1 (TYPING): HomFrom's implicit category is undeterminable / ** 负 1（打字）：HomFrom 的隐式类别无法确定 *)

Fail Check (FCone (HomFrom unit) (coq_two_limit (Pick_Two bool nat))).

(*
Positive controls naming the negative's own constants.  The EXPLICIT
   spelling is what the target ships, and every constant in the rejected
   expression is independently well-formed here.

--------
正向控制命名负向自身的常量。明确拼写是目标提供的，每个被拒绝表达式中的常量在此处都是独立的良构。
*)
Check coq_hom_bool_nat_limit.
Check (@FCone Two_Discrete Coq Sets (HomFrom unit)).
Check (HomFrom unit).
Check coq_two_limit.
Check (Pick_Two bool nat).
(*
The repair, named: ascribing the object determines [HomFrom]'s implicit
   category, and then FCone's own arguments may stay implicit.

--------
修复，即：将对象归类确定 [HomFrom] 的隐含类别，然后 FCone 自身的参数可以保持隐含。
*)
Check (FCone (HomFrom (unit : obj[Coq])) (coq_two_limit (Pick_Two bool nat))).

(**
** Former Negative 2 (FORMABILITY, universe): the discrete route no
    longer pins Set

    RECORDED CORRECTION: this section used to hold the file's second
    negative, refused because [DiscreteCat_Functor] was unannotated and
    instantiated [DiscreteCat@{u Set Set}].  Annotated in the PR
    "algebraic carriers are sets" (2026-09-17) it is accepted, and the
    line is retained as a positive control at the same levels.

--------
** 前负数 2（可形成性，宇宙）：离散路径不再固定集合

记录的更正：本节曾经保存文件的第二个负数，因 [DiscreteCat_Functor] 未标注且实例化了 [DiscreteCat@{u Set Set}] 而被拒绝。在 PR “代数载体是集合”（2026-09-17）中已标注，现被接受，该行在相同级别保持为正控制。
*)

Section AboveSet.

Universe uo uh.
Constraint Set < uh.

Context (C : Category@{uo uh uh}) (c : obj[C]) (fam : bool -> obj[C]).

(*
Control (a): the DIRECT product statements carry no [Set] -- they
   elaborate over this category, whose hom universe is strictly above it.
   This is the header's positive claim, exercised rather than asserted.

--------
控制 (a)：直接产品声明不包含 [Set] —— 它们详细说明了这个类别，其同类宇宙严格高于它。这是标题的正面声明，是被执行而非被主张的。
*)
Check (@hom_IsIndexedProduct C c).
Check (@hom_IsCartesianProduct C c).

(*
Control (b): the discrete-diagram functor ALONE is formable here.  It
   always was; what used to be refused was the COMBINATION below.

--------
控制（b）：这里只能形成离散图示函子。它一直都是如此；以前被拒绝的是下面的组合。
*)
Check (@DiscreteCat_Functor bool C fam).

(* The repaired combination, kept as a positive control. / 修复后的组合，作为阳性对照保存。 *)
Check (fun N : Cone (@DiscreteCat_Functor bool C fam) => IsLimitCone N).

(*
Control (c): [IsLimitCone] itself is fine at this ambient category when
   the SHAPE is not the Set-pinned discrete one.

--------
控制 (c)：当 SHAPE 不是固定集合的离散形状时，[IsLimitCone] 本身在此环境类别下是可以的。
*)
Check (fun (J : Category@{uo uh uh}) (K : J ⟶ C) (N : Cone K) =>
         IsLimitCone N).

End AboveSet.

(** ** Controls for the delivered results / ** 已交付结果的控制 *)

Check hom_PreservesLimitCone.
Check hom_ContinuousFunctor.
Check hom_PreservesLimit.
Check hom_PreservesAllLimits.
Check hom_preserved_leg.
Check hom_preserved_mediator.
Check hom_med_commutes.
Check hom_med_unique.
Check hom_IsIndexedProduct.
Check hom_IsCartesianProduct.
Check HomFrom.
Check HomTo.
Check hom_to_is_op_hom_from.
Check cohom_ContinuousFunctor.
Check cohom_PreservesLimitCone.
Check cohom_colimit_to_limit.
Check cohom_IsIndexedProduct.
Check cohom_IsCartesianProduct.
Check cartesian_IsCartesianProduct.
Check coq_hom_product.
Check coq_hom_limit_cone.

(**
** MEASURED RENAME-SIMULATION SCORE

    The one remaining negative names [FCone], [HomFrom], [coq_two_limit]
    and [Pick_Two]; the repaired section names [DiscreteCat_Functor],
    [Cone] and [IsLimitCone].

    All SEVEN are named by a positive control above, so renaming any one
    of them breaks this file rather than turning a negative vacuously
    green or a positive control vacuously absent.  Score: 7/7, counted
    rather than recalled.

    RECORDED CORRECTION: an earlier revision counted "two negatives" here
    and assigned the second group to Negative 2.  That negative was
    repaired by annotating [DiscreteCat_Functor]; the constants and the
    score are unchanged, only the KIND of the line they guard.

--------
** 测量的重命名模拟分数

剩下的负面名称 [FCone]、[HomFrom]、[coq_two_limit] 和 [Pick_Two]；修复后的部分名称 [DiscreteCat_Functor]、[Cone] 和 [IsLimitCone]。

这七个名称都是由上述正控制命名的，因此重命名其中任何一个都会破坏此文件，而不会使负面名称徒然变为绿色，或使正控制徒然消失。 分数：7/7，计数而非回忆。

记录的修改：早期版本在此处计数为“两个负面”，并将第二组分配给负面 2。通过注释 [DiscreteCat_Functor] 修复了那一个负面；常量和分数保持不变，仅其所保护行的类型有所改变。
*)
