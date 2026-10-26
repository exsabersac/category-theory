Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Limit.Initial.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.Continuity.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Theory.Equivalence.Colimit.

Generalizable All Variables.

(*
   * * A full reflective subcategory of a cocomplete category is cocomplete

   Mac Lane §V.5 Exercise 3 (book p. 120, `maclane:V.5:ex3`, #434) — the
   colimit half of Riehl's Proposition 4.6.14, whose limit half is
   Construction/Reflective/Limit.v (#373): colimits in a full reflective
   subcategory are computed by reflecting the ambient colimit, so a full
   reflective subcategory of a cocomplete category is cocomplete.  Over
   Construction/Reflective.v's [Reflective S] (a [Subcategory] record on
   the ambient [C], with [reflective_full], [reflector : C ⟶ Sub C S] and
   [reflective_adj : reflector ⊣ Incl C S]), for a diagram
   [K : J ⟶ Sub C S] and an ambient colimit [L : Colimit (Incl C S ◯ K)]:
   [reflective_colimit L : Colimit K], with apex
   [reflector R (colimit_apex L)] and injections
   [fmap[reflector R] (colimit_inj L x) ∘ rc_unit_hom (K x)] — the formula
   the issue asks for, both at [eq_refl] — the cocone-level form
   [reflective_colimit_cocone], and the packaging
   [reflective_Cocomplete : @Cocomplete C → @Cocomplete (Sub C S)]
   (canonical, matching Limit.v's [reflective_Complete]; the issue's own
   name [reflective_subcategory_cocomplete] is an alias by [:=]).

   THE ROUTE, six tactic-mode proofs — 17 tactic lines, nine of them the
   diagram isomorphism's; the headline is a term.  The reflector is a left
   adjoint, so it carries the ambient colimit to a colimit of
   [reflector ◯ (Incl ◯ K)] (Adjunction/Continuity.v
   [lapc_is_acolimit]); the counit isomorphism [reflector (Incl x) ≅ x],
   whiskered along [K], is a diagram isomorphism
   [reflective_diagram_iso : reflector ◯ (Incl ◯ K) ≈ K] (Theory/Functor.v's
   [Functor_Setoid]), and Theory/Equivalence/Colimit.v's
   [isacolimit_transport] moves the colimit across it with the apex
   untouched; Theory/Equivalence/Limit.v's [isalimit_to_limit] repacks.
   Construction/Reflective.v's [reflective_counit_iso] is [Qed] and is
   consumed here as DATA, so it is restated transparently as
   [rc_counit_iso], with [rc_unit_hom] its inverse leg.  FULLNESS of the
   inclusion is spent exactly once, in [rc_unit_hom], lifting the unit at
   [Incl x] into the subcategory; FAITHFULNESS is not used at all — unlike
   the limit half, which reflects a limit down along [Incl] through
   [ff_reflect_ump].  The reflector is cocontinuous with no hypothesis
   ([reflective_reflector_Cocontinuous], Continuity.v).

   WITNESS.  Over any shape with a terminal object the ambient colimit
   exists in ANY category (Structure/Limit/Initial.v
   [terminal_Colimit]), so [reflective_terminal_shape_colimit] needs no
   cocompleteness hypothesis; Test/ProbeReflectiveColimit434.v
   instantiates it at the torsion-free reflection of abelian groups
   (Instance/Ab/TorsionFree.v [TorsionFree_Reflective]) over
   [Ordinal 2] — two objects and a non-identity arrow, so the generic
   term's leg obligations are discharged at a shape that has one; the
   probe reads back the apex at [eq_refl] and pins no leg there.  The
   instantiation lives in the probe because importing
   Instance/Ab/TorsionFree.v here costs 33 modules of closure (Instance/Ab
   alone 11) and makes Construction/ depend on Instance/Ab.  No ambient of
   an in-tree reflection ([Ab], [Top], [Ord]) is shown cocomplete, so
   [reflective_Cocomplete] at a concrete reflection stays a conditional —
   the status docs/INHABITATION.md records, the same as
   [reflective_Complete]'s.  CORRECTION (#461): one ambient now is.
   Instance/Top/Hausdorff.v's [Haus_Cocomplete] is
   [reflective_Cocomplete] at the Hausdorff reflection [Haus_reflective]
   of the Prop-valued spaces [PTopCat] (Instance/Top/Prop.v), cocomplete
   by Instance/Top/Cocomplete.v's [PTop_Cocomplete], and
   docs/INHABITATION.md's row has moved to the witnessed table.  No
   witness of [reflective_Complete] at a concrete reflection is added.
   CORRECTION (#370): three more ambients are shown cocomplete in tree.
   [Grp], [Rng] and [RMod R] carry #370's [Ab_Reflective_in_Grp],
   [CRng_Reflective_in_Rng] and [TMod_Reflective_in_RMod], and
   Instance/Grp/Colimit.v's [Grp_Cocomplete_via_GAFT], Instance/Rng/
   Colimit.v's [Rng_Cocomplete_via_GAFT] and Instance/Mod/Colimit.v's
   [RMod_Cocomplete_via_GAFT] are their cocompleteness.
   [reflective_Cocomplete] applied to each pair elaborates (measured
   by a [Definition] in a scratch file) but is not made a constant.

   STALE PREMISES (the issue's “Current state”, six).  [Cocomplete]
   (Structure/Complete.v) is said to have “no concrete instance and
   only a hypothesis use in Theory/Adamek/Corollaries.v”: it has three
   inhabitants — [Sets_Cocomplete] (Instance/Sets/Cocomplete.v),
   [Subsets_Cocomplete] (Instance/Powerset.v),
   [Proset_Cocomplete_of_all_joins] (Instance/Proset/Limit.v) — and
   ten files binding a [Cocomplete] hypothesis (grep for [Cocomplete] in
   binder position: `(… : Cocomplete`, `Cocomplete →`, `Context …
   Cocomplete`), none in Adjunction/GAFT.v or its satellites
   (“consumed only as a hypothesis in GAFT” has zero hits).  Both “0 hits”
   greps (`colimits.*subcategory`, `reflective.*colimit`) return one hit
   each, Limit.v's own scope-out paragraph.  [equivalence_creates_colimits]
   is in Theory/Equivalence/Limit.v, but not where the issue cites it.
   The colimit-creation
   vocabulary the issue says is absent exists at
   Structure/Limit/Creation.v ([CreatesColimit],
   [StrictlyCreatesColimit], [CreatesAllColimits], [creates_colimit_lift],
   [creation_preserves_colimit], [creates_colimits_Cocomplete]); it is not
   used here, since a reflective inclusion need not create colimits
   (Riehl §4.6 ex xi — cited, not formalized); probe N4 pins only that
   [reflective_colimit] does not ascribe to [CreatesColimit K (Incl C S)].
   The Adjunction/Continuity.v site the issue cites is a section
   comment rather than any of the constants that follow it, and the
   Construction/Reflective.v site it cites is the field [reflector]
   rather than the record that declares it.  The donor the issue never
   names is Theory/Equivalence/Colimit.v, whose transports do the work.

   UNIVERSES ([About] under `Set Printing Universes`, all 20 heads).  No
   [Set] anywhere.  Every head carries `u0 = u2` (the ambient's hom level
   identified with [Subcategory]'s, in the binder [C : Category@{u u0 u0}]
   as Limit.v records) and the strict `u0 < u4`; the eight heads
   of the shape section carry Limit.v's five block equations (`u0 = u8`,
   `u0 = u10`, `u4 = u11`, `u5 = u9` beside `u0 = u2`), inherited from the
   same donors.  [reflective_Cocomplete] has type
   [Cocomplete@{u7 u12 u0 u} → Cocomplete@{u7 u12 u0 u5}]: the two
   [Cocomplete]s share three of their four levels and differ only in the
   ambient object level — no annotation was needed.  The stdlib caps
   `Basics.compose`, `ID` and Specif's `Projections` are on every head,
   arriving with [radj] from [Reflective] and [Sub].

   MEASURED.  20 `.glob` heads (16 `def`, 4 `prf`), no [Program]
   obligations, all 20 “Closed under the global context”, zero `Axioms:`
   lines; the `make print-assumptions` gate carries the 20.  Two
   `Defined`, both LOAD-BEARING (flipped to `Qed` one at a time in a copy
   of the whole file: [rc_unit_hom] stops [rc_iso_to_from],
   [reflective_diagram_iso] stops the readback [reflective_colimit_inj]);
   four `Qed`; five `eq_refl` Examples.  Closure 45 files excluding self
   (Structure/Limit/Initial.v 9 at the margin — the witness —
   Theory/Equivalence/Colimit.v 2, Construction/Reflective.v 1,
   Structure/Complete.v 1, the other twelve `Require`s 0; none of the 16
   is droppable; Limit.v's closure is 36, and Adjunction/Diagonal/Limit.v's
   [HasColimitsOfShape] form was left out because it costs 31 more against
   the file as shipped — 35 against it without Structure/Limit/Initial.v).
   Zero name collisions for the 20 names (`grep -rlw --include='*.v'`;
   Limit.v's header mentions [reflective_colimit] and
   [reflective_Cocomplete] by design; [reflective_lift] and
   [reflective_incl_adj] are Limit.v's and were avoided — [radj] is a
   section-local alias of [reflective_adj R], term-for-term Limit.v's
   [reflective_incl_adj], and Limit.v is not in this file's closure, so
   importing it for the name would cost more than the alias).
   Test/ProbeReflectiveColimit434.v mirrors the `Require` list plus
   Structure/Limit/Creation.v and the witness's three modules and carries
   5 refutation commands = 1 instrument + N1 TYPING (the reflected apex is
   an object of [Sub C S], not the ambient apex: “has type obj[C] while it
   is expected to have type obj[Sub C S]”) + N2 CONVERSION
   ([Cocomplete (Sub C S) = Cocomplete C] at [eq_refl]) + N3-N4 TYPING
   (the cocone-level result does not ascribe to
   [PreservesColimitCocone K (Incl C S)], nor the colimit to
   [CreatesColimit K (Incl C S)]), each stripped one at a time in a copy
   of the whole file beside its accepted control; six `eq_refl` readbacks;
   guard coverage 20/16 with four exhaustive exceptions (identifier tokens
   inside the five refutation commands / also named outside them, comments
   stripped; the exceptions are the refutation keyword, the two refuted
   Examples' own names and the instrument's absent name);
   rename-simulated 9 library names — [reflective_colimit],
   [colimit_apex], [eq_refl], [Cocomplete], [Sub],
   [reflective_colimit_cocone], [PreservesColimitCocone], [Incl],
   [CreatesColimit] — every first break on a positive line.  `make todo`
   grows by the 5 refutation lines only (2272 → 2277 over #433's tip
   10fdfda4), so the issue's “adds no new hits” box is not met as written
   (disclosed, as in #430 and #433); Coq 8.19 and 8.20 are checked by nix
   source builds of the committed revision, which the PR records.
   Limit.v's header paragraph on the colimit half and its
   docs/INDEX.md bullet's “OPEN” clause are corrected in place, the former
   line-neutrally.

   NOT DELIVERED: creation of colimits by the inclusion, or Riehl §4.6 ex
   xi's counterexample that it need not (no in-tree reflection comes with
   the ambient colimit that would leave the subcategory — a follow-on
   candidate, surfaced in the PR rather than filed); naturality of
   [reflective_diagram_iso] in [K]; the per-shape [HasColimitsOfShape]
   form; any [Cocomplete] inhabitant for an ambient carrying a reflection;
   strict creation, the monadic route through
   Construction/Reflective/Idempotent.v, anything about [Coreflective];
   nothing is registered as an [Instance]; no edit to
   Construction/Reflective.v, Adjunction/Continuity.v,
   Theory/Equivalence/Colimit.v, Structure/Limit/Initial.v or
   Structure/Complete.v.  CORRECTION (#461): the tree now has an ambient
   colimit that leaves its reflective subcategory.
   Instance/Top/Hausdorff.v's [GlueQ] is the coequalizer in [PTopCat] of
   a pair of maps between Hausdorff spaces ([glue_f_h], [glue_g_h]), and
   it is not Hausdorff ([GlueQ_not_PHaus]), so ex xi's counterexample is
   in reach; it is not stated as a [CreatesColimit] refutation anywhere.  A
   [Cocomplete] inhabitant for an ambient carrying a reflection exists
   too, outside this file: [PTop_Cocomplete] (Instance/Top/Cocomplete.v,
   #458), the ambient of #461's reflections. 

   --------
   * * 完全反射子范畴的余完备范畴是余完备的Mac Lane 第 V.5 节练习 3（书第 120 页，`maclane:V.5:ex3`，#434）——Riehl 命题 4.6.14 的余极半部分，其极限半部分见 Construction/Reflective/Limit.v (#373)：在一个全反映子范畴中的余极是通过反映环境中的余极来计算的，因此一个余完备范畴的全反映子范畴也是余完备的。在 Construction/Reflective.v 的 [Reflective S]（一个关于环境 [C] 的 [Subcategory] 记录，带有 [reflective_full]、[reflector : C ⟶ Sub C S] 和 [reflective_adj : reflector ⊣ Incl C S]），对于一个图 [K : J ⟶ Sub C S] 和一个环境余极限 [L : Colimit (Incl C S ◯ K)]：[reflective_colimit L : Colimit K]，顶点为 [reflector R (colimit_apex L)]，注入为 [fmap[reflector R]（colimit_inj L x）∘ rc_unit_hom (K x)] —— 问题所要求的公式，在 [eq_refl] 都适用 —— 錐级形式 [reflective_colimit_cocone]，以及封装 [reflective_Cocomplete : @Cocomplete C → @Cocomplete (Sub C S)]（规范的，匹配 Limit.v 的 [reflective_Complete]；问题自己的名字 [reflective_subcategory_cocomplete] 是 [:=] 的别名）。路线，六个策略模式证明——17条策略线，其中九条是图同构；标题是一个术语。反射子是左伴随，因此它将环境余极限带到 [reflector ◯ (Incl ◯ K)] 的余极限（Adjunction/Continuity.v [lapc_is_acolimit]）；伴随余单位同构 [reflector (Incl x) ≅ x]，经 [K] 鞭状操作，是一个图同构 [reflective_diagram_iso : reflector ◯ (Incl ◯ K) ≈ K]（Theory/Functor.v 的 [Functor_Setoid]），而 Theory/Equivalence/Colimit.v 的 [isacolimit_transport] 将余极限传递过去并保持顶点不变；Theory/Equivalence/Limit.v 的 [isalimit_to_limit] 重新打包。Construction/Reflective.v 的 [reflective_counit_iso] 是 [Qed]，并在此处作为数据使用，因此它透明地重述为 [rc_counit_iso]，其逆变腿为 [rc_unit_hom]。包含的完整性只在 [rc_unit_hom] 中使用一次，将单元在 [Incl x] 中提升到子范畴；忠实性根本没有使用——与极限的一半不同，极限的一半沿 [Incl] 通过 [ff_reflect_ump] 反映下极限。反射器是余连续的，无需假设（[reflective_reflector_Cocontinuous]，Continuity.v）。见证。在任何具有终对象的图形上，任何范畴中都存在环境余极限（Structure/Limit/Initial.v [terminal_Colimit]），因此 [reflective_terminal_shape_colimit] 无需余完备性假设；Test/ProbeReflectiveColimit434.v 在阿贝尔群的无挠反射上实例化它（Instance/Ab/TorsionFree.v [TorsionFree_Reflective]），位于 [Ordinal 2]——两个对象和一个非恒等箭头，因此通用项的边义务在拥有对象的形状上得到满足；探针在 [eq_refl] 读取顶点并且不在那固定任何边。由于在此导入 Instance/Ab/TorsionFree.v 需要 33 个闭包模块（仅 Instance/Ab 就需要 11 个），并使 Construction/ 依赖于 Instance/Ab，因此实例化存在于探针中。没有显示任何树中反射的环境（[Ab]、[Top]、[Ord]）是余完备的，所以在具体反射处的[reflective_Cocomplete]仍然是条件性的——状态记录在docs/INHABITATION.md中，与[reflective_Complete]相同。更正（#461）：现在有一个环境。Instance/Top/Hausdorff.v中的[Haus_Cocomplete]在Hausdorff反射[Haus_reflective]（来自Prop-valued空间[PTopCat]（Instance/Top/Prop.v））处是[reflective_Cocomplete]，通过Instance/Top/Cocomplete.v的[PTop_Cocomplete]是余完备的，并且docs/INHABITATION.md的行已移到已验证表中。在具体反射处没有添加[reflective_Complete]的见证。更正（#370）：在树中显示了另外三个环境为余完备。[Grp]、[Rng] 和 [RMod R] 携带 #370 的 [Ab_Reflective_in_Grp]、[CRng_Reflective_in_Rng] 和 [TMod_Reflective_in_RMod]，Instance/Grp/Colimit.v 的 [Grp_Cocomplete_via_GAFT]、Instance/Rng/Colimit.v 的 [Rng_Cocomplete_via_GAFT] 和 Instance/Mod/Colimit.v 的 [RMod_Cocomplete_via_GAFT] 是它们的余完备性。[reflective_Cocomplete] 应用于每一对进行展开（通过在临时文件中的 [Definition] 进行测量），但并未被设为常量。陈旧的前提（该问题的“当前状态”，六）。[Cocomplete]（Structure/Complete.v）据说“没有具体实例，仅在 Theory/Adamek/Corollaries.v 中作为假设使用”：它有三个实例——[Sets_Cocomplete]（Instance/Sets/Cocomplete.v）、[Subsets_Cocomplete]（Instance/Powerset.v）、[Proset_Cocomplete_of_all_joins]（Instance/Proset/Limit.v）——以及十个文件绑定了一个 [Cocomplete] 假设（在绑定位置搜索 [Cocomplete]：`(… : Cocomplete`、`Cocomplete →`、`Context … Cocomplete`），在 Adjunction/GAFT.v 或其附属文件中没有（“只作为 GAFT 中的假设使用”为零命中）。两个 “零命中” 的 grep（`colimits.*subcategory`、`reflective.*colimit`）各返回一次命中，即 Limit.v 自身的范围段落。[equivalence_creates_colimits] 位于 Theory/Equivalence/Limit.v，但不是问题引用它的地方。问题中所说缺失的余极限创建词汇存在于 Structure/Limit/Creation.v（[CreatesColimit]、[StrictlyCreatesColimit]、[CreatesAllColimits]、[creates_colimit_lift]、[creation_preserves_colimit]、[creates_colimits_Cocomplete]）；它在此处未被使用，因为反射包含不需要创建余极限（Riehl §4.6 ex xi — 已引用，但未形式化）；探针 N4 仅指出 [reflective_colimit] 并未赋予 [CreatesColimit K (Incl C S)]。问题中引用的 Adjunction/Continuity.v 站点是一个节注，而不是其后的任何常量，而它引用的 Construction/Reflective.v 站点是字段 [reflector]，而不是声明它的记录。问题从未提到的捐赠者是 Theory/Equivalence/Colimit.v，其传输完成了这项工作。宇宙（[About] 在 `Set Printing Universes` 下，全部 20 个头）。没有 [Set] 出现。每个头都携带 `u0 = u2`（其环境的同源水平与 [Subcategory] 的相同，在 [C : Category@{u u0 u0}] 绑定器中作为 Limit.v 记录）以及严格的 `u0 < u4`；形状部分的八个头携带 Limit.v 的五个块方程（`u0 = u8`、`u0 = u10`、`u4 = u11`、`u5 = u9` 以及 `u0 = u2`），继承自相同的捐赠者。[reflective_Cocomplete] 类型为 [Cocomplete@{u7 u12 u0 u} → Cocomplete@{u7 u12 u0 u5}]：两个 [Cocomplete] 在四个层级中的三个共享，仅在环境对象层级上不同——不需要注释。stdlib 上的 `Basics.compose`、`ID` 以及 Specif 的 `Projections` 出现在每个头上，随 [radj] 从 [Reflective] 和 [Sub] 带来。已测量。20个`.glob` 头（16个`def`，4个`prf`），无[Program] 义务，全部20个“在全局上下文下关闭”，零`Axioms:` 行；`make print-assumptions` 门承载20个。两个`Defined`，均为承重（在整个文件的副本中一次翻转为`Qed`：[rc_unit_hom] 停止[rc_iso_to_from]，[reflective_diagram_iso] 停止回读[reflective_colimit_inj]）；四个`Qed`；五个`eq_refl` 示例。闭包45个文件，不包括自身
   （Structure/Limit/Initial.v 9 在边缘 — 见证 —
   Theory/Equivalence/Colimit.v 2，Construction/Reflective.v 1，
   Structure/Complete.v 1，其余十二个 `Require` s 0；16个文件中没有一个可以删除；Limit.v的闭包是36，Adjunction/Diagonal/Limit.v 的 [HasColimitsOfShape] 形式被省略，因为它对已有文件会额外增加31的成本 — 如果不考虑 Structure/Limit/Initial.v 则增加35）。对于这20个名称（`grep -rlw --include='*.v'`），没有名称冲突；Limit.v 的头部按设计中提到了 [reflective_colimit] 和 [reflective_Cocomplete]；[reflective_lift] 和 [reflective_incl_adj] 属于 Limit.v 并已避开 — [radj] 是 [reflective_adj R] 的部分局部别名，逐项来说是 Limit.v 的 [reflective_incl_adj]，而 Limit.v 不在此文件的闭包中，因此仅为了名称而导入它的成本会高于使用别名。Test/ProbeReflectiveColimit434.v 镜像了 `Require` 列表以及 Structure/Limit/Creation.v 和证人的三个模块，并携带 5 个反驳命令 = 1 个工具 + N1 类型检查（反映的顶点是 [Sub C S] 的对象，而不是环境顶点：“具有类型 obj [C] ，而期望的类型是 obj [Sub C S]”）+ N2 转换（[Cocomplete (Sub C S) = Cocomplete C] 在 [eq_refl]）+ N3-N4 类型检查（余锥级结果没有归于 [PreservesColimitCocone K (Incl C S)] ，也没有归纳极限到 [CreatesColimit K (Incl C S)]），每次在整个文件的副本中逐一剥离，与其已接受的控制文件并排；六个 `eq_refl` 回读；守护覆盖率 20/16，四个穷尽性异常（位于五个反驳命令内的标识符令牌 / 也命名于其外，已剥除注释；异常是反驳关键字，两者反驳的
   示例自身的名称和仪器缺失的名称);
   重命名模拟的9个库名称 — [reflective_colimit],
   [colimit_apex], [eq_refl], [Cocomplete], [Sub],
   [reflective_colimit_cocone], [PreservesColimitCocone], [Incl],
   [CreatesColimit] — 在每个正向线路的第一次中断处。`make todo` 仅通过 5 条反驳行增长（2272 → 2277 在 #433 的提示 10fdfda4 上），所以问题的“没有新增命中”框如原文所述未满足（如 #430 和 #433 所披露）；Coq 8.19 和 8.20 已通过 nix 构建已提交修订的源码进行检查，PR 已记录。Limit.v 中关于余极限半部分的头段以及 docs/INDEX.md 项的“OPEN”条款已就地更正，前者为行中性修正。未交付：通过包含创建余极限，或 Riehl §4.6 例 xi 的反例，它不一定成立（没有树内反射随环境余极限一起出现从而离开子范畴——一个后续的候选，在 PR 中提出而非提交）；[reflective_diagram_iso] 在 [K] 中的自然性；每个形状的 [HasColimitsOfShape] 形式；对于具有反射的环境的任何 [Cocomplete] 成员；严格创建，通过 Construction/Reflective/Idempotent.v 的单子路径，以及任何关于 [Coreflective] 的内容；没有任何东西被注册为 [Instance]；未对 Construction/Reflective.v、Adjunction/Continuity.v、Theory/Equivalence/Colimit.v、Structure/Limit/Initial.v 或 Structure/Complete.v 进行编辑。更正 (#461)：该树现在具有一个环境余极限，使其离开其反射子范畴。Instance/Top/Hausdorff.v 的 [GlueQ] 是 [PTopCat] 中一个关于豪斯多夫空间 ([glue_f_h], [glue_g_h]) 的一对映射的余等化子，并且它不是豪斯多夫的 ([GlueQ_not_PHaus])，所以 xi 的反例是可达到的；它没有在任何地方被陈述为 [CreatesColimit] 的反驳。对于一个带有反射的环境，[Cocomplete] 的元素也存在，在这个文件之外：[PTop_Cocomplete]（Instance/Top/Cocomplete.v，#458），它是 #461 的反射的环境。
*)

Section ReflectiveColimits.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Reflective S).

Notation I := (Incl C S).

Definition radj : reflector R ⊣ I := reflective_adj R.

(*
   * ** A transparent counit isomorphism

   Construction/Reflective.v's [reflective_counit_iso] is [Qed]; this
   development consumes the isomorphism as DATA (it is whiskered into a
   diagram isomorphism whose components must reduce), so it is restated
   here with [Defined].  Fullness of the inclusion is spent exactly once,
   in [rc_unit_hom]: the unit at [I x] lives in the ambient category and
   has to be lifted into the subcategory. 

   --------
   * ** 一个透明的余单位同构

   Construction/Reflective.v 中的 [reflective_counit_iso] 是 [Qed]；这个
   发展把同构作为数据使用（它被挂到一个图同构中，其组件必须简化），所以这里用 [Defined] 重新表述。包含的充满性恰好使用一次，
   在 [rc_unit_hom]：[I x] 处的单位存在于环境范畴中，需要提升到子范畴中。
*)

Definition rc_unit_hom (x : Sub C S) : x ~{Sub C S}~> reflector R (I x).
Proof.
  exists (@Category.Theory.Adjunction.unit (Sub C S) C (reflector R) I radj
            (I x)).
  apply (reflective_full R).
Defined.

Lemma rc_iso_to_from (x : Sub C S) :
  @counit (Sub C S) C (reflector R) I radj x ∘ rc_unit_hom x ≈ id.
Proof. apply (@fmap_counit_unit (Sub C S) C (reflector R) I radj x). Qed.

Lemma rc_iso_from_to (x : Sub C S) :
  rc_unit_hom x ∘ @counit (Sub C S) C (reflector R) I radj x ≈ id.
Proof.
  rewrite <- (counit_naturality radj).
  apply (@counit_fmap_unit (Sub C S) C (reflector R) I radj (I x)).
Qed.

Definition rc_counit_iso (x : Sub C S) : reflector R (I x) ≅[Sub C S] x :=
  {| to := @counit (Sub C S) C (reflector R) I radj x
   ; from := rc_unit_hom x
   ; iso_to_from := rc_iso_to_from x
   ; iso_from_to := rc_iso_from_to x |}.

Lemma rc_to (x : Sub C S) :
  to (rc_counit_iso x) ≈ @counit (Sub C S) C (reflector R) I radj x.
Proof. reflexivity. Qed.

Lemma rc_from (x : Sub C S) : from (rc_counit_iso x) ≈ rc_unit_hom x.
Proof. reflexivity. Qed.

Section Shape.

Context {J : Category}.
Context (K : J ⟶ Sub C S).

(*
   * ** The diagram isomorphism [reflector ◯ (I ◯ K) ≈ K]

   The counit isomorphism at each [K x], with its naturality square: the
   one triangle identity each way and [counit_naturality]. 

   --------
   * ** 图同构 [reflector ◯ (I ◯ K) ≈ K]

   每个 [K x] 上的余单位同构，以及它的自然性方形：每个方向的一个三角形恒等式和 [counit_naturality] 。
*)

Definition reflective_diagram_iso : (reflector R ◯ (I ◯ K)) ≈ K.
Proof.
  exists (fun x => rc_counit_iso (K x)).
  intros x y f.
  rewrite <- comp_assoc.
  rewrite (rc_to (K x)).
  rewrite <- (counit_naturality radj (fmap[K] f)).
  rewrite comp_assoc.
  rewrite (rc_from (K y)).
  rewrite (rc_iso_from_to (K y)).
  now rewrite id_left.
Defined.

(*
   * ** The reflected colimit

   The reflector, a left adjoint, carries the ambient colimit of [I ◯ K]
   to a colimit of [reflector ◯ (I ◯ K)] (Adjunction/Continuity.v's
   [lapc_is_acolimit]); the diagram isomorphism moves it to [K]
   (Theory/Equivalence/Colimit.v's [isacolimit_transport]); the apex is
   untouched. 

   --------
   * ** 反射余极限

   反射函子，一个左伴随，将环境余极限 [I ◯ K] 
   转换为 [reflector ◯ (I ◯ K)] 的余极限（见 Adjunction/Continuity.v 的 [lapc_is_acolimit]）；图同构将其移动到 [K] 
   （见 Theory/Equivalence/Colimit.v 的 [isacolimit_transport]）；顶点保持不变。
*)

Definition reflective_colimit (L : Colimit (I ◯ K)) : Colimit K :=
  isalimit_to_limit
    (isacolimit_transport reflective_diagram_iso
       (lapc_is_acolimit radj L)).

Example reflective_colimit_apex (L : Colimit (I ◯ K)) :
  colimit_apex (reflective_colimit L) = reflector R (colimit_apex L)
  := eq_refl.

(*
 The injections: the reflector applied to the ambient injections, after
 the inverse counit — the formula the issue asks for, on the nose. 

 --------
 注射：反射器应用于环境注射之后，经过逆单位——问题要求的公式，正是如此。
*)
Example reflective_colimit_inj (L : Colimit (I ◯ K)) (x : J) :
  colimit_inj (colimit_is_acolimit (reflective_colimit L)) x
    = fmap[reflector R] (colimit_inj (colimit_is_acolimit L) x)
        ∘ rc_unit_hom (K x) := eq_refl.

(** ** The cocone-level form / ** 角锥层形式 *)

Definition reflective_lift_cocone (N : Cocone (I ◯ K)) : Cocone K :=
  cocone_transport reflective_diagram_iso (FCocone (reflector R) N).

Example reflective_lift_cocone_apex (N : Cocone (I ◯ K)) :
  vertex_obj[reflective_lift_cocone N] = reflector R vertex_obj[N]
  := eq_refl.

Example reflective_lift_cocone_inj (N : Cocone (I ◯ K)) (x : J) :
  cocone_inj (reflective_lift_cocone N) x
    = fmap[reflector R] (cocone_inj N x) ∘ rc_unit_hom (K x) := eq_refl.

Definition reflective_colimit_cocone (N : Cocone (I ◯ K))
  (HN : IsColimitCocone N) : IsColimitCocone (reflective_lift_cocone N) :=
  isalimit_limitcone
    (isacolimit_transport reflective_diagram_iso
       (colimitcocone_isacolimit
          (left_adjoint_PreservesColimitCocone radj (I ◯ K) N HN))).

End Shape.

(** ** Mac Lane §V.5 Exercise 3 / ** 马克·莱恩 §V.5 练习 3 *)

Definition reflective_Cocomplete (HC : @Cocomplete C) : @Cocomplete (Sub C S) :=
  fun J K => reflective_colimit K (HC J (I ◯ K)).

(* The issue's name for the same constant. / 同一个常量的问题名称。 *)
Definition reflective_subcategory_cocomplete :
  @Cocomplete C → @Cocomplete (Sub C S) := reflective_Cocomplete.

(* The reflector is cocontinuous, with no hypothesis at all. / 反射器是共连续的，完全没有任何假设。 *)
Definition reflective_reflector_Cocontinuous :
  CocontinuousFunctor (reflector R) := left_adjoint_Cocontinuous radj.

(*
   * ** A hypothesis-free witness

   Over any shape with a terminal object the ambient colimit exists in
   ANY category (Structure/Limit/Initial.v's [terminal_Colimit]), so the
   reflected colimit needs no cocompleteness hypothesis. 

   --------
   * ** 一个无假设的证据

   在任何具有终对象的形状上，环境余极限在任何范畴中都存在
   （Structure/Limit/Initial.v 的 [terminal_Colimit]），因此反射余极限不需要完备性假设。
*)

Definition reflective_terminal_shape_colimit {J : Category} (T : @Terminal J)
  (K : J ⟶ Sub C S) : Colimit K :=
  reflective_colimit K (@terminal_Colimit J C T (I ◯ K)).

Example reflective_terminal_shape_apex {J : Category} (T : @Terminal J)
  (K : J ⟶ Sub C S) :
  colimit_apex (reflective_terminal_shape_colimit T K)
    = reflector R (I (K (@terminal_obj J T))) := eq_refl.

End ReflectiveColimits.
