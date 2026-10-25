(**
* Probe for the free group read through Freyd (issue #442)

    Pins the measured boundaries of Instance/Grp/FreeAFT.v, whose header
    makes two negative claims of its own — the solution set fed to Freyd's
    theorem is circular, and Mac Lane's own index cannot be written at this
    instance IN THE TREE AS IT STANDS — beside the issue's QA claim.  All
    three are pinned below, but not all by refutations: the circularity is
    pinned by a POSITIVE [eq_refl], since what it asserts is an identity
    and not an absence.  CORRECTION, PR "algebraic carriers are sets"
    (2026-09-17): BOTH of those negative claims have since moved.  The
    circularity claim is now about a constant that is kept but no longer
    consumed (section A); the index claim turned over when
    Instance/Discrete.v was annotated, so what stood as N5 is now a
    positive control (section D).  An earlier revision of this paragraph
    ended "The second is pinned by N5, and N5 is expected to turn over —
    see the comment there", and the prediction held.

    THE HEADLINE BOUNDARY IS N1: [free_group_via_GAFT_agrees] is `≈` and
    NOTHING STRONGER.  [GAFT] is [Qed]-opaque, so the functor Freyd's
    theorem returns does not reduce to [FreeGrp] — not as a functor (N1),
    not at a single object (N2), and its adjunction is not even of the same
    TYPE as [free_group_adjunction] (N3).  The `≈` that does hold is
    [left_adjoint_iso], and the readback beside N1 shows that it is that
    generic lemma applied and nothing instance-specific.

    THE CIRCULARITY IS LITERAL, not rhetorical, and the readback that says
    so is positive: [Grp_Forget_solution_set_from_adjunction X] IS
    [solution_set_of_adjunction free_group_adjunction X] by [eq_refl], its
    member IS [FreeGrpObject X], and its arrow IS the unit of the very
    adjunction the theorem is meant to produce.  N4 sharpens the last one:
    the arrow is the UNIT, which agrees with [fg_insert] only pointwise (a
    different record), so even the circular solution set is not the
    insertion of generators on the nose.
    CORRECTION (#1347): N4 now holds at [eq_refl], since Instance/Sets.v
    gives its identity's and composite's properness fields as terms; it
    is a control, and even the circular solution set's arrow IS
    [fg_insert] on the nose.  "A different record" was argued, not
    measured: the unit is [fmap[U] id ∘ arrow], and the measurement shows
    the residue was the standard library's, the opaque lemmas instance
    resolution had put in the two properness fields, the identity's and that
    composite's.

    N5 is the universe claim, measured: at this application the solution
    set's index is squeezed onto [Set], and Mac Lane's own index
    [Subgroup G] (Instance/Grp/Quotient.v) is never there.  The control
    beside it is the same builder at a [Set]-level index ([bool]), which IS
    accepted — so the refusal is about the universe and not about the shape
    of the hypothetical.  N5 pins the REFUSAL, which is real; it does not
    pin a cause, and the cause is not [Grp_Complete] or [GAFT] — see the
    comment at N5 itself, and the target's header, which record what the
    [Set] actually comes from and what removing it would cost.  N5 is one
    of the eleven boundaries that a three-line annotation in
    Instance/Discrete.v would turn over.

    N6 and N7 pin which preservation hypothesis this instance owes: neither
    [Grp_Forget_continuous] ([ContinuousFunctor]) nor
    [Grp_Forget_PreservesAllLimits] (the apex-only class) ascribes where
    [GAFT] asks for the cone-level [PreservesImageLimit], which is why the
    [Continuous_PreservesImageLimit] bridge stands in the term.  N8 records
    that the induced monad's multiplication inherits the counit's opacity:
    [Grp_Forget]'s image of the counit does not reduce to word evaluation,
    which Instance/Grp/Free.v proves only up to `≈`.

    NON-VACUITY IS CARRIED BY TWO THEOREMS, not by refutations.
    [p442_repr_separates] shows the representation distinguishes the two
    elements of [Z2] — a constant or otherwise degenerate transformation
    could not, since the round trip [grp_repr_to ∘ grp_repr_from] is the
    identity — and [p442_repr_obj_not_trivial] upgrades that to: the
    representing object is not isomorphic to the trivial group.  Without
    these the representability clause would be satisfied by the one-element
    group and would say nothing.

    SECTION H, added after the rest, covers the target's injectivity clause:
    that the general result's statement IS the tree's own two-letter one
    (Instance/Grp/Free.v) on the nose, while the two proofs are separate
    terms (N9) and the decision procedure is a real argument (N10).

    SECTION I, added by the PR "algebraic carriers are sets" (2026-09-17),
    covers what [free_group_via_GAFT] consumes SINCE that PR: the
    non-circular [Grp_Forget_solution_set_prop], indexed by the [Prop]
    congruences on [FGWord X].  The first paragraph of this header is
    therefore no longer the whole story, and section A carries the recorded
    correction: the circularity claims are now about
    [free_group_via_GAFT_from_adjunction], which is kept.  N13 there pins
    the one thing the unconditional reading costs, [Set < carrier], at a
    named in-tree object.

    KINDS, kept lexically apart: NAME-ABSENCE (the instrument), TYPE (I1,
    N3, N6, N7, N10), CONVERSION (N1, N2, N4, N8, N9, N11, N12), UNIVERSE
    (N13, twice).  CORRECTION: an earlier revision of this line read
    "UNIVERSE (N5) — twelve refutations in all", and both halves were
    stale.  N5 became a positive control when Instance/Discrete.v's
    annotation landed (see section D), and the count was never
    re-measured: the file carried ELEVEN [Fail] commands at that point and
    carries FIFTEEN now, by [grep -c '^Fail'].  Each was stripped one at a
    time in a copy of the WHOLE file and its exact refusal text recorded.
    The import list is the target's in full — including
    Lib/Setoid/Propositional.v, which section I names — plus
    Instance/Grp/Quotient.v for [Subgroup], which section D names.
    CORRECTION (#1347): N4 is a control now, so CONVERSION is N1, N2, N8,
    N9, N11 and N12, and the file carries FOURTEEN refutation lines by
    the same count.  N4, wrapped in the refutation keyword in a copy of
    the WHOLE file, stops the build at that command; each of the
    fourteen, stripped in such a copy, stops inside its command with the
    error it printed before #1347 (compared by script, universe serial
    names aside).

--------
* 通过 Freyd（第442期）探讨自由群

固定 Instance/Grp/FreeAFT.v 的测量边界，其头部自带两个否定性声明——传入 Freyd 定理的解集是循环的，而且 Mac Lane 自身的索引在当前树结构下无法写入该实例——在该问题的 QA 声明旁边。三者都已固定在下面，但并非全部通过反驳来固定：循环性是通过一个正向 [eq_refl] 固定的，因为它断言的是恒等式而不是缺失。更正，PR “代数载体是集合”（2026-09-17）：这两个否定声明都已移动。循环性声明现在关于一个保持但不再被消耗的常量（A 节）；索引声明在 Instance/Discrete.v 被标注后发生变化，所以原本作为 N5 的现在是一个正向控制（D 节）。该段早期修改版本以“第二个通过 N5 固定，并且预期 N5 会发生变化——见那里的评论”结束，预测得到了验证。

标题界限是 N1：[free_group_via_GAFT_agrees] 是 `≈`，而没有更强的。[GAFT] 是 [Qed]-不透明的，所以 Freyd 定理返回的函子不能约化为 [FreeGrp]——无论作为函子（N1），还是在单个对象上（N2），并且它的伴随甚至不是与 [free_group_adjunction] 相同的类型（N3）。成立的 `≈` 是 [left_adjoint_iso]，而 N1 旁边的回读显示，它是应用了那个通用引理，而不是任何特定实例。

循环性是字面上的，而不是修辞上的，并且回读显示这一点是积极的：[Grp_Forget_solution_set_from_adjunction X] 通过 [eq_refl] 是 [solution_set_of_adjunction free_group_adjunction X]，其成员是 [FreeGrpObject X]，并且它的箭头是定理旨在生成的那个陪伴的单位。N4 使最后一个更加明确：该箭头是单位，它仅在点上与 [fg_insert] 一致（一个不同的记录），所以即使循环解集也不是生成器的直接插入。更正 (#1347)：N4 现在在 [eq_refl] 上成立，因为 Instance/Sets.v 给出了它的身份和复合的适当性字段作为项；它是一个控制，甚至循环解集的箭头确实是 [fg_insert]。‘一个不同的记录’是被论证的，而不是被测量的：单位是 [fmap[U] 身份 ∘ 箭头，而测量显示残余部分是标准库的，不透明引理实例解析已经放入了两个适当性字段，即身份和那个复合的字段。

N5 是宇宙声明，测量结果：在此应用中，解集的索引被压缩到 [Set]，而 Mac Lane 自己的索引 [Subgroup G]（Instance/Grp/Quotient.v）从未存在。其旁边的控件是在 [Set] 级别索引（[bool]）的同一构建器，而且被接受——所以拒绝是关于宇宙的，而不是关于假设的形状。N5 固定了拒绝，这是实际存在的；它并未固定原因，而原因也不是 [Grp_Complete] 或 [GAFT]——参见 N5 本身的注释，以及目标的头部，它们记录了 [Set] 实际来自哪里以及移除它的代价。N5 是 Instance/Discrete.v 中三行注释会翻转的十一条边界之一。

N6 和 N7 钉下了这个实例归属于哪个保持假设：既不是 [Grp_Forget_continuous]（[ContinuousFunctor]），也不是 [Grp_Forget_PreservesAllLimits]（仅顶点类），因为 [GAFT] 需要圆锥级别的 [PreservesImageLimit]，这就是为什么 [Continuous_PreservesImageLimit] 桥出现在该项中。N8 记录了诱导单子的乘法继承了辅单位的不透明性：[Grp_Forget] 的辅单位映像不会简化为词求值，而 Instance/Grp/Free.v 仅证明了 `≈` 的情况。

非空性是由两个定理支撑的，而不是通过反驳来证明的。[p442_repr_separates] 表明该表示区分了 [Z2] 的两个元素——一个恒定的或其他退化的变换无法做到这一点，因为往返的 [grp_repr_to ∘ grp_repr_from] 是恒等变换——而 [p442_repr_obj_not_trivial] 将其升级为：表示对象不是平凡群同构。没有这些，表示性条款将会被单元素群满足，并且不会说明任何问题。

第 H 节，在其他部分之后添加，涵盖目标的单射性条款：
    即一般结果的陈述正是该树自身的两个字母的陈述
    （Instance/Grp/Free.v）本身，而两个证明是独立的
    项（N9），决策程序是真实的论证（N10）。

第一部分，由 PR "代数载体是集合"（2026-09-17）添加，涵盖了自该 PR 以来 [free_group_via_GAFT] 消耗的内容：非循环的 [Grp_Forget_solution_set_prop]，由 [FGWord X] 上的 [Prop] 同余索引。因此，此标题的第一段不再是全部内容，A 节包含了记录的更正：循环性声明现在关于 [free_group_via_GAFT_from_adjunction]，该对象已保留。其 N13 固定了无条件读取所花费的唯一内容 [Set < carrier]，在一个命名的树内对象中。

种类，在词汇上保持分开：名称缺失（工具）、类型（I1, N3, N6, N7, N10）、转换（N1, N2, N4, N8, N9, N11, N12）、宇宙（N13，两次）。更正：该行的早期修订版本写的是“宇宙（N5）——总共十二次反驳”，而这两部分都已过时。当 Instance/Discrete.v 的注释出现时（参见 D 节），N5 成为正对照，并且计数从未重新测量：当时文件包含 ELEVEN [Fail] 命令，现在通过 [grep -c '^Fail'] 包含 FIFTEEN 个。每个都在整个文件的副本中逐一移除，并记录其确切的拒绝文本。导入列表是目标的完整列表——包括 Lib/Setoid/Propositional.v（由 I 节命名）——以及 Instance/Grp/Quotient.v 用于 [Subgroup]（由 D 节命名）。
修正 (#1347)：N4 现在是一个控制，因此转换是 N1、N2、N8、N9、N11 和 N12，并且该文件包含相同数量的十四行反驳。将 N4 包裹在一份完整文件的反驳关键字中，在该命令处会停止构建；在这种复制中去掉十四行中的每一行，会在其命令内部停止，并显示它们在 #1347 之前打印的错误（通过脚本比较，宇宙序列名称除外）。
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.GAFT.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Comparison.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Fun.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.Grp.Limit.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.FreeAFT.

Generalizable All Variables.

(* instrument: the refutation keyword is live / instrument：反驳关键词是 live *)
Fail Check probe442_absent_name.

(*
I1 instrument, second kind: elaboration is really happening.  This is
   the deliberately ill-typed variant of [p442_repr_obj] below, which DOES
   hold — the representing object is an object of [Grp], and asking for it
   to be the singleton SETOID is a type error, not a conversion one.

--------
I1 仪器，第二类： elaboration 确实正在发生。这是下面 [p442_repr_obj] 的故意类型错误的变体，它确实成立——表示对象是 [Grp] 的一个对象，要求它是单例 SETOID 是一个类型错误，而不是转换错误。
*)
Fail Example p442_instrument :
  @repr_obj Grp Grp_Forget Grp_Forget_Representable = SetOne := eq_refl.

(**
** A: the CIRCULAR application, and the circularity read back

    RECORDED CORRECTION, PR "algebraic carriers are sets" (2026-09-17).
    Every statement in this section used to be about [free_group_via_GAFT],
    which consumed [Grp_Forget_solution_set_from_adjunction].  That constant
    is kept and is still circular, but the application built from it is now
    named [free_group_via_GAFT_from_adjunction], and this section is
    retargeted onto that name.  ONE LINE of the section changed, the
    four-argument readback below; the other five are statements about the
    solution set itself and compile verbatim.  Section I covers what
    [free_group_via_GAFT] consumes now.

--------
** A：循环应用，以及循环性回读

记录更正，PR “代数载体是集合”（2026-09-17）。
本节中的每个陈述过去都是关于 [free_group_via_GAFT] 的，它使用了 [Grp_Forget_solution_set_from_adjunction]。该常量仍然保留，并且仍然是循环的，但由它构建的应用现在命名为 [free_group_via_GAFT_from_adjunction]，本节也重新指向该名称。本节有一行改变，即下面的四参数回读；其余五行是关于解集本身的陈述，可以逐字编译。I 节涵盖了 [free_group_via_GAFT] 现在消耗的内容。
*)

(* The theorem is applied to exactly these four arguments. / 该定理正好应用于这四个论点。 *)
Example p442_via_GAFT_is_GAFT :
  free_group_via_GAFT_from_adjunction
    = GAFT Grp_Forget Grp_Complete
           (Continuous_PreservesImageLimit Grp_Forget_continuous)
           Grp_Forget_solution_set_from_adjunction := eq_refl.

(*
THE CIRCULARITY, as an [eq_refl].  The third hypothesis fed to Freyd's
   theorem is the singleton family at the unit of the adjunction the
   theorem is meant to produce.

--------
循环性，作为一个 [eq_refl]。送入 Freyd 定理的第三个假设是伴随单位处的单例族，该定理旨在产生该伴随。
*)
Example p442_solution_set_is_circular (X : Sets) :
  Grp_Forget_solution_set_from_adjunction X
    = solution_set_of_adjunction free_group_adjunction X := eq_refl.

Example p442_sol_index (X : Sets) :
  sol_index (Grp_Forget_solution_set_from_adjunction X) = poly_unit := eq_refl.

(* ...and the single member is the word group already in tree. / ...而这个单一成员是已经在树中的词组。 *)
Example p442_sol_obj (X : Sets) (i : poly_unit) :
  sol_obj (Grp_Forget_solution_set_from_adjunction X) i = FreeGrpObject X
  := eq_refl.

Example p442_sol_arr (X : Sets) (i : poly_unit) :
  sol_arr (Grp_Forget_solution_set_from_adjunction X) i = free_group_unit X
  := eq_refl.

(*
control for N4: the arrow and the insertion of generators agree at every
   point, which is Instance/Grp/Free.v's [free_group_unit_is_insert].

--------
N4 控制：箭头与发电机的插入在每一点上都一致，这是 Instance/Grp/Free.v 的 [free_group_unit_is_insert]。
*)
Example p442_sol_arr_pointwise (X : Sets) (i : poly_unit) (a : carrier X) :
  sol_arr (Grp_Forget_solution_set_from_adjunction X) i a = fg_insert X a
  := eq_refl.

(*
N4 CONVERSION: but they are not the same MORPHISM.  The unit is
   [fmap[U] id ∘ arrow] and carries its own respectfulness proof; the
   solution set is built from the unit, not from [fg_insert].
   CORRECTION (#1347): they are the same morphism at [eq_refl] now that
   Instance/Sets.v gives its identity's and composite's properness fields
   as terms, and this is a control; the cause above was argued, not
   measured.

--------
N4 转换：但是它们不是相同的态射。单元是 [fmap[U] id ∘ arrow] 并且携带它自身的遵守性证明；解集是从单元构建的，而不是从 [fg_insert] 构建的。修正 (#1347)：现在在 [eq_refl] 上它们是相同的态射，因为 Instance/Sets.v 将其恒等和复合的正确性字段作为项给出，这是一个控制；上述原因是论证得出的，而非测量得出的。
*)
Example p442_sol_arr_is_insert (X : Sets) (i : poly_unit) :
  sol_arr (Grp_Forget_solution_set_from_adjunction X) i = fg_insert X
  := eq_refl.

(** ** B: the QA clause is `≈`, and only `≈` / ** B：QA 条款是 `≈`，仅为 `≈` *)

(* control: the agreement that IS delivered... / 控制：已交付的协议... *)
Check (free_group_via_GAFT_agrees : `1 free_group_via_GAFT ≈ FreeGrp).

(* ...and it is [left_adjoint_iso] applied, nothing instance-specific. / ...并且它是应用了 [left_adjoint_iso]，没有特定实例。 *)
Example p442_agrees_is_generic :
  free_group_via_GAFT_agrees
    = left_adjoint_iso Grp_Forget _ FreeGrp (`2 free_group_via_GAFT)
                       free_group_adjunction := eq_refl.

(*
N1 CONVERSION: the two functors are NOT convertible.  [GAFT] is
   [Qed]-opaque, so its output does not reduce at all.

--------
N1 转换：这两个函子不可转换。[GAFT] 是 [Qed]-不透明的，所以它的输出根本不会被简化。
*)
Fail Example p442_gaft_output_is_FreeGrp :
  `1 free_group_via_GAFT = FreeGrp := eq_refl.

(*
N2 CONVERSION: nor at a single object — not even at the singleton, where
   the free group is the one-generator group the representation uses.

--------
N2 转换：也不针对单个对象——即使是单元素对象，其中自由群是表示使用的单生成元群。
*)
Fail Example p442_gaft_output_obj :
  `1 free_group_via_GAFT SetOne = FreeGrpObject SetOne := eq_refl.

(*
N3 TYPE: and the two adjunctions are not comparable by [=] at all, their
   left legs being different terms.

--------
N3 类型：并且这两个附加结构通过 [=] 根本不可比较，它们的左边部分是不同的项。
*)
Fail Example p442_gaft_adjunction_is_free :
  `2 free_group_via_GAFT = free_group_adjunction := eq_refl.

(** ** C: which hypotheses this instance owes / ** C：这个实例所依赖的假设 *)

(* control: the application, again, as a [Check] / 控制：该应用程序，再次，作为 [Check] *)
Check (GAFT Grp_Forget Grp_Complete
            (Continuous_PreservesImageLimit Grp_Forget_continuous)
            Grp_Forget_solution_set_from_adjunction).

(*
N6 TYPE: [ContinuousFunctor] is not [PreservesImageLimit] — the bridge
   in the target's term is load-bearing.

--------
N6 类型：[ContinuousFunctor] 不是 [PreservesImageLimit]——在目标术语中，这座桥是承重的。
*)
Fail Check (GAFT Grp_Forget Grp_Complete Grp_Forget_continuous
                 Grp_Forget_solution_set_from_adjunction).

(*
N7 TYPE: neither is the apex-only class, which Instance/Grp/Limit.v also
   supplies and which is the tempting wrong choice.

--------
N7 类型：都不是仅顶点类，Instance/Grp/Limit.v 也提供了该类，它也是容易令人误选的错误选项。
*)
Fail Check (GAFT Grp_Forget Grp_Complete Grp_Forget_PreservesAllLimits
                 Grp_Forget_solution_set_from_adjunction).

(**
** D: UNIVERSE — why Mac Lane's own solution set cannot be written here

    The header's second reason for not using the subgroups generated by the
    image.  [SolutionSet]'s index is [Type@{u}] with [u] free — the record
    carries an empty constraint set — but at this application it is
    squeezed onto the literal [Set], and [Subgroup G] is never there.

--------
** D：宇宙 — 为什么这里不能写出 Mac Lane 自己的解集

    标题中不使用由图像生成的子群的第二个原因。[SolutionSet] 的索引是 [Type@{u}]，[u] 是自由的——记录携带一个空的约束集——但是在这个应用中，它被压缩到字面量 [Set] 上，而且 [Subgroup G] 从未出现过。
*)

Definition p442_GAFT_at_Grp :=
  GAFT Grp_Forget Grp_Complete
       (Continuous_PreservesImageLimit Grp_Forget_continuous).

(*
A solution-set builder over an arbitrary index, so that the pair below
   differs in the index type and in nothing else.

--------
在任意索引上的解集构建器，使得下面的对在索引类型上有所不同，而其他方面都相同。
*)
Definition p442_sols_indexed_by (I : Type)
  (o : ∀ X : Sets, I → Grp)
  (a : ∀ (X : Sets) (i : I), X ~{Sets}~> Grp_Forget (o X i))
  (cov : ∀ (X : Sets) (c : Grp) (h : X ~{Sets}~> Grp_Forget c),
      { i : I & { t : o X i ~{Grp}~> c & fmap[Grp_Forget] t ∘ a X i ≈ h } })
  (X : Sets) : SolutionSet Grp_Forget X :=
  {| sol_index := I
   ; sol_obj := o X
   ; sol_arr := a X
   ; sol_covers := fun c h => cov X c h |}.

(*
control: at a [Set]-level index the builder's output IS what [GAFT]
   consumes at this instance.

--------
控制：在 [Set] 级别的索引上，构建器的输出就是 [GAFT] 在此实例中消耗的内容。
*)
Check (fun o a cov =>
         p442_GAFT_at_Grp (p442_sols_indexed_by bool o a cov)).

(*
Former N5, now a positive control: Mac Lane's index is accepted.

   RECORDED CORRECTION.  An earlier revision read: "N5 UNIVERSE: at Mac
   Lane's index it is refused.  WHAT THIS DOES AND DOES NOT PIN.  It pins
   the refusal, in the tree as it stands.  It does NOT pin a cause, and an
   earlier revision of the target's header attributed the cause to [GAFT]
   and [Grp_Complete], which is wrong: the [Set] is a universe-
   minimization artifact of Instance/Discrete.v's unannotated
   [DiscreteCat_Functor], reaching GAFT's statement through GAFT.v,
   and [Grp_Complete] only transmits it.  Annotating that one donor —
   three lines, no [Qed]-opaque term touched — makes this very [Check]
   succeed, so THIS REFUTATION IS EXPECTED TO TURN OVER when
   Instance/Discrete.v's follow-on lands.  It is one of eleven such
   boundaries in the tree (Instance/Cat/Objects.v,
   Structure/Limit/Components.v and nine Test/Probe* lines); measured
   2026-09-12 in a full copy of this worktree, that annotation breaks no
   proof anywhere in the 977-file build set and turns over exactly those
   eleven and nothing else."

   The cause was diagnosed correctly and the prediction held.  The
   annotation landed in the PR "algebraic carriers are sets"
   (2026-09-17): [DiscreteCat_Functor@{o h p uo uh up +}], now
   Instance/Discrete.v, and this line is ACCEPTED.  It is kept at Mac
   Lane's own index [Subgroup G] as a positive control, so dropping the
   annotation refuses it again and breaks this file.

   TWO FIGURES IN THAT PARAGRAPH WERE STALE AND ARE CORRECTED HERE.  The
   build set was 977 files when the prediction was measured; it was 1018
   when the annotation landed.  And the boundary count "eleven" was never
   enumerated: the flip set measured by building the annotated tree is
   TWENTY-TWO commands in FIFTEEN files.  Seven of them are outside
   [Test/] — two in Instance/Cat/Objects.v, two in
   Structure/Limit/Components.v and three in Instance/Indiscrete.v — and
   fifteen are in twelve [Test/Probe*] files: ProbeCommaCreation438,
   ProbeComparison419 (2), ProbeComponents355 (2), ProbeConeSets407 (2),
   ProbeDualNoRightAdjoint433, ProbeFreyd423, ProbeFromProducts416,
   ProbeGAFTCharacterization436, ProbeHomLimit331, ProbeModTensorAFT449,
   ProbeSpanningArrow448, and this file.

   TWO OF THE TWENTY-TWO WOULD HAVE GONE ON PASSING VACUOUSLY, and that is
   worth recording separately.  Instance/Cat/Objects.v and
   Instance/Indiscrete.v each wrote their [Indiscrete] negative as
   [Indiscrete@{uo}], a ONE-universe instance.  Annotating [Indiscrete] as
   [Indiscrete@{o h p}] makes that an arity error — "Universe instance
   length for Indiscrete is 1 but should be 3", measured — so the [Fail]
   would have stayed green while the boundary it guarded was gone.  Both
   were rewritten with all three levels before being turned over.

   The remaining claim held exactly: no proof anywhere in the tree broke,
   and the full build is rc=0.

--------
前 N5，现在是阳性对照：麦克莱恩指数被接受。

已记录的更正。之前的修订版本写道：“N5 宇宙：在 Mac Lane 的索引中被拒绝。这做了什么以及没有做什么。它固定了拒绝，在当前树中。它不会固定原因，并且目标头的早期修订将原因归因于 [GAFT] 和 [Grp_Complete]，这是错误的：[Set] 是 Instance/Discrete.v 未注释的 [DiscreteCat_Functor] 的宇宙最小化伪影，通过 GAFT.v 到达 GAFT 的语句，而 [Grp_Complete] 仅传递它。”注释那个捐赠者 —— 三行，没有触及 [Qed] 不透明术语 —— 使这个非常 [Check] 成功，因此当 Instance/Discrete.v 的后续内容到达时，这个反驳预期会翻转。它是树中十一条这样的边界之一（Instance/Cat/Objects.v, Structure/Limit/Components.v 以及九条 Test/Probe* 行）；在完整工作树的副本中测量于 2026-09-12，该注释在 977 个文件的构建集中没有破坏任何证明，并且恰好翻转了那十一条，没有其他。

原因被正确诊断，预测得以成立。注释出现在 PR “代数载体是集合” (2026-09-17)：[DiscreteCat_Functor@{o h p uo uh up +}]，现在为 Instance/Discrete.v，这一行已被接受。它被保存在 Mac Lane 自己的索引 [Subgroup G] 中，作为一个阳性控制，因此删除注释会再次拒绝它，并导致该文件出错。

那一段中的两个数字已经过时，并在这里进行了更正。测量预测时，构建集是977个文件；注释完成时为1018个文件。而边界数量“十一”从未被列出：通过构建注释树测量的翻转集是在15个文件中有22条命令。其中七个在外部
   [Test/] —— 两个位于 Instance/Cat/Objects.v，两个位于
   Structure/Limit/Components.v，三个位于 Instance/Indiscrete.v —— 还有
   十五个在十二个 [Test/Probe*] 文件中：ProbeCommaCreation438，
   ProbeComparison419（2），ProbeComponents355（2），ProbeConeSets407（2），
   ProbeDualNoRightAdjoint433，ProbeFreyd423，ProbeFromProducts416，
   ProbeGAFTCharacterization436，ProbeHomLimit331，ProbeModTensorAFT449，
   ProbeSpanningArrow448，以及这个文件。

二十二个中有两个本该继续空洞地通过，这一点值得单独记录。Instance/Cat/Objects.v 和 Instance/Indiscrete.v 各自将它们的 [Indiscrete] 否定写成了 [Indiscrete@{uo}]，一个单一宇宙实例。将 [Indiscrete] 注释为 [Indiscrete@{o h p}] 会造成元数错误——“Indiscrete 的宇宙实例长度为 1，但应为 3”，由此衡量——因此 [Fail] 会保持绿色，而它所保护的边界已消失。在交付之前，这两个都被用所有三个层级重写。

剩下的断言完全成立：树中的任何地方都没有破坏证明，完整构建的返回码为 rc=0。
*)
Check (fun (G : Grp) o a cov =>
         p442_GAFT_at_Grp (p442_sols_indexed_by (Subgroup G) o a cov)).

(** ** E: the induced monad / ** E：诱导单子 *)

Example p442_ret_is_unit (X : Sets) :
  @ret Sets _ free_group_monad X = free_group_unit X := eq_refl.

Example p442_ret_generator (X : Sets) (a : carrier X) :
  @ret Sets _ free_group_monad X a = fg_insert X a := eq_refl.

Example p442_join_is_counit (X : Sets) :
  @join Sets _ free_group_monad X
    = fmap[Grp_Forget] (free_group_counit (FreeGrp X)) := eq_refl.

Example p442_monad_functor_obj (X : Sets) :
  fobj[Grp_Forget ◯ FreeGrp] X = grp_setoid (FreeGrpObject X) := eq_refl.

(*
N8 CONVERSION: the multiplication inherits the counit's opacity.
   Instance/Grp/Free.v records that the counit is [unique_obj] of
   [ump_universal_arrows], which is [Qed]-sealed (Theory/Universal/Arrow.v,
   closed), so nothing on this side reduces; the agreement with word
   evaluation is [free_group_counit_evaluates], up to `≈` and no more.

--------
N8 转换：乘法继承了余单位的不透明性。Instance/Grp/Free.v 记录了余单位是 [unique_obj] 的 [ump_universal_arrows]，而 [ump_universal_arrows] 是 [Qed] 封闭的（Theory/Universal/Arrow.v，封闭），所以这一侧没有任何可约；与字的求值的一致性是 [free_group_counit_evaluates]，最多到 `≈`，没有更多。
*)
Fail Example p442_join_is_word_evaluation (X : Sets) :
  @join Sets _ free_group_monad X
    = fmap[Grp_Forget]
        (free_grp_extend (@id Sets (Grp_Forget (FreeGrp X)))) := eq_refl.

(** ** F: the representation, and that it is not degenerate / ** F：表示，并且它不是退化的 *)

Example p442_repr_obj :
  @repr_obj Grp Grp_Forget Grp_Forget_Representable = FreeGrp SetOne
  := eq_refl.

Example p442_repr_obj_word :
  @repr_obj Grp Grp_Forget Grp_Forget_Representable
    = FreeGrpObject unit_setoid_object := eq_refl.

Example p442_repr_to_component (G : Grp) (f : FreeGrp SetOne ~{Grp}~> G) :
  transform[to (@represented Grp Grp_Forget Grp_Forget_Representable)] G f
    = grp_repr_to G f := eq_refl.

Example p442_repr_from_component (G : Grp) (a : carrier (Grp_Forget G)) :
  transform[from (@represented Grp Grp_Forget Grp_Forget_Representable)] G a
    = grp_repr_from G a := eq_refl.

Example p442_repr_to_is_transpose (G : Grp) (f : FreeGrp SetOne ~{Grp}~> G) :
  grp_repr_to G f = to (grp_adj G) f ttt := eq_refl.

(*
The round trip, which is what a degenerate transformation could not
   supply: reading an element back off the homomorphism it names returns
   that element.

--------
往返，这是一个退化变换无法提供的：从它所命名的同态中读回一个元素会返回该元素。
*)
Lemma p442_repr_to_from (G : Grp) (a : carrier (Grp_Forget G)) :
  grp_repr_to G (grp_repr_from G a) ≈ a.
Proof. exact (iso_to_from (grp_adj G) (grp_repr_const G a) ttt). Qed.

(*
NON-VACUITY, first theorem: the representation SEPARATES the two
   elements of [Z2].  A constant transformation into [Hom(FreeGrp 1, Z2)]
   would give one homomorphism for both, so this is a statement no
   degenerate representation could carry.

--------
非空性，第一个定理：表示将 [Z2] 的两个元素分开。恒定地转变为 [Hom(FreeGrp 1, Z2)] 会为两者提供一个同态，所以这是没有任何退化表示能够承载的陈述。
*)
Theorem p442_repr_separates :
  grp_repr_from Z2 true ≈ grp_repr_from Z2 false → False.
Proof.
  intro H.
  apply Z2_nontrivial.
  transitivity (grp_repr_to Z2 (grp_repr_from Z2 true)).
  - symmetry; exact (p442_repr_to_from Z2 true).
  - transitivity (grp_repr_to Z2 (grp_repr_from Z2 false)).
    + exact (proper_morphism (to (grp_adj Z2)) _ _ H ttt).
    + exact (p442_repr_to_from Z2 false).
Qed.

(*
NON-VACUITY, second theorem: hence the representing object is not the
   trivial group.  Every pair of homomorphisms out of [Grp_trivial] is
   identified ([Grp_zero_hom_unique]), so an isomorphism with it would
   collapse the two homomorphisms the previous theorem keeps apart.

--------
非空性，第二定理：因此表示对象不是平凡群。从 [Grp_trivial] 出发的每一对同态都会被识别（[Grp_zero_hom_unique]），所以与它的同构会使前一个定理保持分开的两个同态合并。
*)
Theorem p442_repr_obj_not_trivial :
  @repr_obj Grp Grp_Forget Grp_Forget_Representable ≅[Grp] Grp_trivial
    → False.
Proof.
  intro i.
  apply p442_repr_separates.
  transitivity (grp_repr_from Z2 true ∘ (from i ∘ to i)).
  - rewrite iso_from_to; rewrite id_right; reflexivity.
  - transitivity (grp_repr_from Z2 false ∘ (from i ∘ to i)).
    + rewrite !comp_assoc.
      rewrite (Grp_zero_hom_unique Z2
                 (grp_repr_from Z2 true ∘ from i)
                 (grp_repr_from Z2 false ∘ from i)).
      reflexivity.
    + rewrite iso_from_to; rewrite id_right; reflexivity.
Qed.

(** ** G: guard block / ** G：守卫模块 *)

Check @Grp_Forget_solution_set_from_adjunction.
Check @free_group_via_GAFT.
Check @free_group_via_GAFT_agrees.
Check @free_group_monad.
Check @grp_repr_const.
Check @grp_repr_to.
Check @grp_repr_from.
Check @grp_repr_to_natural.
Check @grp_repr_from_natural.
Check @Grp_Forget_Representable.
Check @GAFT.
Check @SolutionSet.
Check @sol_index.
Check @sol_obj.
Check @sol_arr.
Check @sol_covers.
Check @solution_set_of_adjunction.
Check @Continuous_PreservesImageLimit.
Check @Adjunction_Induced_Monad.
Check @left_adjoint_iso.
Check @Representable.
Check @repr_obj.
Check @represented.
Check @Grp.
Check @Grp_Forget.
Check @Grp_Complete.
Check @Grp_Forget_continuous.
Check @Grp_Forget_PreservesAllLimits.
Check @Grp_trivial.
Check @Grp_zero_hom_unique.
Check @Z2.
Check @Z2_nontrivial.
Check @Subgroup.
Check @FreeGrp.
Check @FreeGrpObject.
Check @free_group_adjunction.
Check @free_group_unit.
Check @free_group_counit.
Check @free_grp_extend.
Check @fg_insert.
Check @unit_setoid_object.

Check @p442_GAFT_at_Grp.
Check @p442_sols_indexed_by.
Check @p442_repr_to_from.
Check @p442_repr_separates.
Check @p442_repr_obj_not_trivial.

(**
** H: the injectivity clause

    Added after the sections above: the target grew Mac Lane's injectivity
    clause, and the tree already had its two-letter case.  What is pinned
    here is that the general statement really does COVER the special one —
    same statement, on the nose — while remaining a separate proof.

--------
** H: 注入性条款

在上述部分之后添加：目标增加了 Mac Lane 的注入性条款，且树已经有了它的两个字母情况。这里强调的是，一般性陈述实际上确实涵盖了特殊情况——完全相同的陈述——同时仍然是一个独立的证明。
*)

(*
The corollary's statement is the tree's own, converted: [free_group_unit]
   IS [fg_insert] at a generator, so the general result is not a weaker
   restatement of Instance/Grp/Free.v.

--------
推论的陈述是树本身的陈述，已转换：[free_group_unit] 在生成器中是 [fg_insert]，所以一般结果不是 Instance/Grp/Free.v 的较弱重述。
*)
Example p442_two_letters_same_statement :
  (free_group_unit TwoLetters true ≈ free_group_unit TwoLetters false → False)
  = (fg_insert TwoLetters true ≈ fg_insert TwoLetters false → False)
  := eq_refl.

(*
N9 CONVERSION: ...but not the same PROOF.  Both are [Qed]-sealed and
   they take different routes — S3 in tree, Z/2 here — so neither reduces
   to the other.  This is what keeps them independent rather than one being
   an alias of the other.

--------
N9 转换：……但不是相同的证明。两者都经过 [Qed] 封装，并且采用不同的路径 —— 树中的 S3，这里的是 Z/2 —— 因此彼此不能简化为对方。这就是它们保持独立而不是互为别名的原因。
*)
Fail Example p442_two_letters_same_proof :
  free_group_two_letters_distinct = free_group_two_generators_distinct
  := eq_refl.

(*
N10 TYPE: the decision procedure is a real argument, not an inferable
   one.  Dropping it leaves the two elements where [SetoidDecidable X] is
   expected.

--------
N10 类型：判定过程是真实的论证，而不是可推导的论证。 删除它会让两个元素处于 [SetoidDecidable X] 期望的位置。
*)
Fail Check (fun (X : Sets) (a b : carrier X) =>
              free_group_unit_injective_dec (X:=X) a b).

Check @free_group_transpose_at_unit.
Check @free_group_unit_injective_of_embedding.
Check @free_group_unit_injective_dec.
Check @free_group_two_letters_distinct.
Check @free_group_two_generators_distinct.
Check @SetoidDecidable.
Check @grp_chi.
Check @TwoLetters.

(**
** I: the NON-CIRCULAR solution set, and the one thing it costs

    Added by the PR "algebraic carriers are sets" (2026-09-17), on the
    pattern of Test/ProbeRngAFTProp.v.  [free_group_via_GAFT] now consumes
    [Grp_Forget_solution_set_prop], the [Prop]-valued congruences on
    [FGWord X].  That change is INVISIBLE TO THE TYPE — the two readings
    inhabit the same statement, and nothing else in the build would notice
    it being reverted — so the [eq_refl] readbacks below name the congruence
    index, and N11 pins that the new index is not the old singleton.

    THE NEW REFUTATIONS ARE N11 (CONVERSION), N12 (CONVERSION) and N13
    (UNIVERSE), taking this file to fifteen.  Each was stripped in a copy of
    the WHOLE file and its exact refusal recorded beside it.
    CORRECTION (#1347): fourteen, since N4 became a control.

--------
** 我：非循环解集，以及它的代价

由PR“代数承载是集合”（2026-09-17）添加，模式参照Test/ProbeRngAFTProp.v。[free_group_via_GAFT]现在使用[Grp_Forget_solution_set_prop]，即[Prop]值的[FGWord X]上的同余。该更改对类型不可见——两个读取共享同一个语句，构建中的其他部分不会注意到它被恢复——因此下面的[eq_refl]回读命名的是同余索引，并且N11确定新索引不是旧的单例。

新的反证为N11（转换）、N12（转换）和N13（宇宙），使得这个文件的反证总数达到十五。每一个都在整个文件的副本中被剥离，其精确的拒绝记录在其旁。
修正（#1347）：十四，因为N4变成了一个控制项。
*)

Check @IsGrpCongruence.
Check @FGCongIdx.
Check @QGrp_Setoid.
Check @QGrp.
Check @QGrp_insert.
Check @fg_ev.
Check @fg_ker.
Check @fg_ker_is_cong.
Check @fg_ker_idx.
Check @fg_ker_med.
Check @QGrpOf.
Check @QGrpInsertOf.
Check @Grp_Forget_solution_set_prop.
Check @free_group_via_GAFT_from_adjunction.
Check @free_group_monad_via_GAFT.

(*
The four arguments of the UNCONDITIONAL application, the twin of
   [p442_via_GAFT_is_GAFT] above.  This is the line that would have to
   change if the circular family came back.

--------
UNCONDITIONAL 应用程序的四个参数，它是上面 [p442_via_GAFT_is_GAFT] 的双胞胎。如果循环系列回来的话，这就是必须改变的那一行。
*)
Example p442_via_GAFT_prop_is_GAFT :
  free_group_via_GAFT
    = GAFT Grp_Forget Grp_Complete
           (Continuous_PreservesImageLimit Grp_Forget_continuous)
           Grp_Forget_solution_set_prop := eq_refl.

Section PropSolutionReadbacks.

Context (X : Sets).

(*
The index IS the congruence type, the members ARE the quotients, and the
   arrows ARE the insertion of generators into them.

--------
指数就是同余类型，成员就是商，而箭头就是生成元的插入。
*)
Example p442_sol_prop_index :
  sol_index (Grp_Forget_solution_set_prop X) = FGCongIdx X := eq_refl.

Example p442_sol_prop_obj (i : FGCongIdx X) :
  sol_obj (Grp_Forget_solution_set_prop X) i = QGrp (`1 i) (`2 i) := eq_refl.

Example p442_sol_prop_arr (i : FGCongIdx X) :
  sol_arr (Grp_Forget_solution_set_prop X) i = QGrp_insert (`1 i) (`2 i)
  := eq_refl.

(*
THE SIZE CLAIM, read back rather than argued: every member's carrier is
   the free group's own word type, so the family is a family of QUOTIENTS
   and not a family of arbitrary groups.  That is what keeps the index at
   the carrier universe.

--------
尺寸声明，是被复述而非辩论的：每个成员的承载体都是自由群自身的字类型，所以这个族是商群的族，而不是任意群的族。这就是保持指数在承载体宇宙中的原因。
*)
Example p442_sol_prop_carrier (i : FGCongIdx X) :
  carrier (grp_setoid (sol_obj (Grp_Forget_solution_set_prop X) i)) = FGWord X
  := eq_refl.

(* The covering is the KERNEL of [free_grp_extend], on the nose. / 覆盖物是 [free_grp_extend] 的核心，正中鼻子。 *)
Example p442_ker_idx_is_kernel (G : Grp) (h : X ~{Sets}~> Grp_Forget G) :
  `1 (fg_ker_idx h) = fg_ker h := eq_refl.

Example p442_ker_is_extension_kernel (G : Grp)
  (h : X ~{Sets}~> Grp_Forget G) (u v : FGWord X) :
  fg_ker h u v
    = @pequiv _ _ (grp_prop G) (fg_ev h u) (fg_ev h v) := eq_refl.

End PropSolutionReadbacks.

(**
** N11 (CONVERSION): the new index is not the old singleton

    If a later edit points [Grp_Forget_solution_set_prop] back at
    [solution_set_of_adjunction], this line stops refusing.  The control is
    [p442_sol_index] in section A, which IS [eq_refl] for the old one.
    Stripped in a copy of this WHOLE file and re-run, the refusal is

      In environment
      X : obj[Sets]
      The term "eq_refl" has type
       "sol_index (Grp_Forget_solution_set_prop X) =
        sol_index (Grp_Forget_solution_set_prop X)"
      while it is expected to have type
       "sol_index (Grp_Forget_solution_set_prop X) = poly_unit"
      (cannot unify "sol_index (Grp_Forget_solution_set_prop X)" and
      "poly_unit").

    Note that the message does NOT name [FGCongIdx]: the index is printed
    unreduced, so the readback [p442_sol_prop_index] above is what carries
    the positive half of the claim and this pins only the disagreement.
    Coq renders such a message with the short names in scope, so it is
    quoted together with the import list at the head of this file.

--------
** N11（转换）：新索引不是旧的单例

如果后来的编辑将 [Grp_Forget_solution_set_prop] 指回 [solution_set_of_adjunction]，这一行将停止拒绝。控件在 A 部分是 [p442_sol_index]，这对于旧的来说是 [eq_refl]。在该整个文件的副本中剥离并重新运行，拒绝是

在环境
      X : obj[Sets]
      术语 "eq_refl" 的类型为
       "sol_index (Grp_Forget_solution_set_prop X) =
        sol_index (Grp_Forget_solution_set_prop X)"
      而期望的类型为
       "sol_index (Grp_Forget_solution_set_prop X) = poly_unit"
      （无法统一 "sol_index (Grp_Forget_solution_set_prop X)" 和
      "poly_unit"）。

请注意，消息并没有具体指出 [FGCongIdx]：索引是未简化打印的，因此上面的读回 [p442_sol_prop_index] 才承载了声明的正半部分，而这只是指出了分歧。Coq 使用作用域内的短名称呈现这样的消息，因此它与此文件开头的导入列表一起被引用。
*)

Fail Example p442_sol_prop_is_not_singleton (X : Sets) :
  sol_index (Grp_Forget_solution_set_prop X) = poly_unit := eq_refl.

(**
** N12 (CONVERSION): the two applications are different terms

    [free_group_via_GAFT] and [free_group_via_GAFT_from_adjunction] inhabit
    the same type and are NOT the same term.  [GAFT] is [Qed], so neither
    reduces; what this pins is that the two are not syntactically
    identified, which is what would happen if one were defined as the
    other.  Stripped in a copy of this WHOLE file, the refusal is

      The term "eq_refl" has type "free_group_via_GAFT = free_group_via_GAFT"
      while it is expected to have type
       "free_group_via_GAFT = free_group_via_GAFT_from_adjunction"
      (cannot unify "free_group_via_GAFT" and
      "free_group_via_GAFT_from_adjunction").

--------
** N12（转换）：这两个应用是不同的项

    [free_group_via_GAFT] 和 [free_group_via_GAFT_from_adjunction] 属于相同类型，但不是同一项。[GAFT] 是 [Qed]，因此都不进行化简；这表明这两个在语法上没有被识别为相同，如果其中一个被定义为另一个，则会发生这种情况。在整个文件的副本中被剥离后，拒绝信息为：

      项“eq_refl”的类型是“free_group_via_GAFT = free_group_via_GAFT”
      ，而期望的类型是
       “free_group_via_GAFT = free_group_via_GAFT_from_adjunction”
      （无法统一“free_group_via_GAFT”和“free_group_via_GAFT_from_adjunction”）。
*)

Fail Example p442_two_applications_differ :
  free_group_via_GAFT = free_group_via_GAFT_from_adjunction := eq_refl.

(**
** The payoff: the theorem applied at named sets

    Before this PR these lines exhibited a free group obtained from an
    adjunction that had been assumed in order to obtain it.

--------
** 结果：定理应用于命名集合

在这个 PR 之前，这些行显示了一个由附加假设得到的自由群，这个假设是为了得到它而提出的。
*)

Check (Grp_Forget_solution_set_prop SetOne).
Check (Grp_Forget_solution_set_prop TwoLetters).
Check (FGCongIdx SetOne).
Check (FGCongIdx TwoLetters).
Check (`1 free_group_via_GAFT SetOne).
Check (fg_ker_idx (fg_insert TwoLetters)).
Check (fg_ker_med (fg_insert TwoLetters)).

(**
** N13 (UNIVERSE): the one price, [Set < carrier], and WHERE it lands

    The index is a sigma over a [Prop]-valued relation; the sort of [Prop]
    is [Set+1]; identifying the index universe with the carrier universe
    therefore puts the carrier strictly above [Set].  Measured, [About]
    under [Set Printing Universes]:

      free_group_via_GAFT@{u u0 u1 u2 u3} :
        ∃ F : Sets@{u0 u} ⟶ Grp@{u u0}, F ⊣ Grp_Forget@{u u u0}
      (* … Set < u0 / u0 < u …

--------
** N13（宇宙）：单一价格，[Set < carrier]，以及它落在哪里

    指数是 [Prop] 值关系上的 σ；[Prop] 的类型是 [Set+1]；因此，将指数宇宙与载体宇宙识别，会将载体严格置于 [Set] 之上。测量时，[About] 处于 [Set Printing Universes] 之下：

      free_group_via_GAFT@{u u0 u1 u2 u3} ：
        ∃ F : Sets@{u0 u} ⟶ Grp@{u u0}, F ⊣ Grp_Forget@{u u u0}
      (* … 集合 < u0 / u0 < u …
*)

      free_group_via_GAFT_from_adjunction@{u … u8} :
        ∃ F : Sets@{u1 u0} ⟶ Grp@{u u1}, F ⊣ Grp_Forget@{u u0 u1}
      (* … Set < u / u1 < u / u1 < u0 … *)

    [About Sets] gives [Sets@{o so} : Category@{so o o}], so the first slot
    is the setoid CARRIER universe; [About Grp] gives
    [Grp@{u p} : Category@{u p p}] with [Set < u] and [p < u] built in.  So
    the circular form's [Set < u] is [Grp]'s own bound on its OBJECT
    universe and is free; the unconditional form's [Set < u0] is on the
    carrier and is not.

    WHERE IT LANDS, and this is the part worth pinning rather than stating:
    NOT on the solution set and NOT on the congruence index, both of which
    are fine with the carrier at [Set] (the two controls in
    [Section SetCarrierPin] below).  It lands on the APPLICATION, because
    that is where [GAFT] identifies the index universe with the carrier.

    Stripped in a copy of this WHOLE file and re-run, the refusal is

      In environment
      Xs : obj[Sets]
      The term "Xs" has type "obj[Sets@{pcar pobj}]"
      while it is expected to have type
       "obj[Sets@{<anon> <anon>}]"
      (universe inconsistency: Cannot enforce pcar = <anon> because pcar
      < <anon>).

    where each [<anon>] is a fresh file-local universe whose printed name
    carries the stripped copy's module name and a serial number, so the
    names themselves are not reproducible and are not quoted.  The
    load-bearing half is the last line: [pcar] is [Set] by the constraint
    above, and the application wants it strictly below the index. *)

Section SetCarrierPin.

Universes pcar pobj.
Constraint pcar = Set.

Context (Xs : obj[Sets@{pcar pobj}]).

(*
CONTROL 1: the non-circular solution set itself elaborates with the
   carrier at [Set].

--------
控制 1：非圆形解集本身在 [Set] 的载体上进行展开。
*)
Definition p442_prop_sols_at_set_carrier : SolutionSet Grp_Forget Xs :=
  Grp_Forget_solution_set_prop Xs.

(* CONTROL 2: and so does the circular application. / 控制 2：圆形应用也是如此。 *)
Definition p442_circular_app_at_set_carrier : obj[Grp] :=
  `1 free_group_via_GAFT_from_adjunction Xs.

(* THE NEGATIVE: the unconditional application does not. / 消极方面：无条件的应用并不会。 *)
Fail Definition p442_uncond_app_at_set_carrier : obj[Grp] :=
  `1 free_group_via_GAFT Xs.

End SetCarrierPin.

(*
AND IT BITES AT A NAMED IN-TREE OBJECT, which is why it is a cost and
   not a formality.  [TwoLetters] (Instance/Grp/Free.v) is the bool
   setoid, and [bool : Set] pins its carrier universe there.  The circular
   application applies to it; the unconditional one is refused, measured by
   stripping this [Fail] in a copy of the WHOLE file:

     The term "TwoLetters" has type "SetoidObject"
     while it is expected to have type "obj[Sets]"
     (universe inconsistency: Cannot enforce Set = <anon> because Set <
     <anon>).

   [SetOne] is NOT affected — [poly_unit] is universe-polymorphic — which
   is why the [SetOne] line above is a control and not an accident.  THIS
   IS THE HONEST STATEMENT OF WHAT THE UNCONDITIONAL APPLICATION COSTS: it
   is total over [Sets] as a polymorphic category, and it does not apply to
   a setoid whose carrier is pinned at [Set].  [Grp_Forget_solution_set_prop
   TwoLetters] above is checked and DOES elaborate, so the restriction is
   the theorem's use of the index, not the solution set's.

--------
并且它会咬一个已命名的树内对象，这就是为什么它是一个成本而不是形式。[TwoLetters]（实例/组/Free.v）是布尔集合，而[bool : Set]将其载体宇宙固定在那里。循环应用适用于它；无条件应用被拒绝，通过在整个文件的副本中剥离这个[Fail]来衡量：

术语“TwoLetters”的类型是“SetoidObject”，而预期类型是“obj[Sets]”（宇宙不一致：无法强制 Set = <匿名> 因为 Set < <匿名>）。

[SetOne] 没有受到影响 — [poly_unit] 是宇宙多态的 — 这就是为什么上面的 [SetOne] 系列是一个控制，而不是意外。 这是关于无条件应用成本的诚实陈述：它是作为多态类别的 [Sets] 的总和，并且它不适用于载体固定在 [Set] 的集合代数。[Grp_Forget_solution_set_prop TwoLetters] 上面已检查并且确实有展开，因此限制在于定理对索引的使用，而不是解集的使用。
*)

Check (`1 free_group_via_GAFT_from_adjunction TwoLetters).

Fail Definition p442_uncond_at_two_letters : obj[Grp] :=
  `1 free_group_via_GAFT TwoLetters.
