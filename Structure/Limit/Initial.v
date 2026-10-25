Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Cones.
Require Import Category.Instance.Cones.Limit.
Require Import Category.Instance.One.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Ordinal.

Generalizable All Variables.

(* * * Limits over a shape with an initial object, computed by evaluation / * * 对具有初始对象的形状的极限，通过求值计算 *)

(*
 Mac Lane:    Categories for the Working Mathematician, 2nd ed. (GTM 5),
 §III.4 Exercise 3, book p. 72   [maclane:III.4:ex3]
 Fong-Spivak: An Invitation to Applied Category Theory (Seven Sketches),
 §3.5.3 Exercise 3.98
 Riehl:       Category Theory in Context, 2nd ed., §3.1, Example and
 Exercise 3.1.vii
 nLab:        https://ncatlab.org/nlab/show/final+functor
 nLab:        https://ncatlab.org/nlab/show/limit

 THE STATEMENT.  If the indexing category J has an initial object 0, then
 every diagram F : J ⟶ C has a limit, and no construction in C is needed
 to produce it: the limit is the value F 0, and its leg at x is the image
 fmap[F] ¡ of the unique arrow ¡ : 0 ~> x.  Cone coherence is immediate,
 since fmap[F] f ∘ fmap[F] ¡ ≈ fmap[F] (f ∘ ¡) ≈ fmap[F] ¡ by uniqueness
 of arrows out of 0; and the mediator from a competing cone N is simply
 N's own leg at 0, forced because the limit's leg AT 0 is fmap[F] ¡₀ with
 ¡₀ ≈ id, again by uniqueness.  Dually, a terminal object of J computes
 colimits by evaluation at it.

 WHY THE RESULT IS NOT A CURIOSITY.  It is the nullary case of the theory
 of final (cofinal) functors: a functor K : A ⟶ J is FINAL when colimits
 over J may be computed by restricting along K, and INITIAL when limits
 may be (nLab, "final functor").  The inclusion of an initial object of J
 is an initial functor, and the inclusion of a terminal object is a final
 one; restricting to a single object leaves nothing to glue, so the
 (co)limit is the value there.  No cofinality vocabulary exists in this
 tree, and none is introduced here — see WHAT IS NOT DELIVERED.

 RELATION TO Structure/Limit/Terminal.v.  That file is the OTHER extreme
 degenerate shape: J empty, where a cone has no legs and the limit is the
 terminal object of C.  The empty category has no objects and hence no
 initial object, so [Terminal_Limit] is not an instance of anything here,
 and nothing here is an instance of it.  The two files are siblings, not
 refinements of one another.  Note also which category supplies the
 universal object in each: there, the terminal object of the TARGET C;
 here, the initial object of the SHAPE J.

 WHAT WAS ABSENT, AND EXACTLY WHAT SEARCH ESTABLISHES IT.  The tree had
 no statement constraining the indexing category's own initial object.
 Two searches are the evidence, and the claim is scoped to them; both are
 run with THIS file excluded (`-g '!Structure/Limit/Initial.v'`), since
 it now supplies the very matches at issue.  First,
 `rg 'Initial J\b|@Initial J\b' -g '*.v' .` returns nothing.  Second, the
 word-bounded survey `rg -o -N '\b@?Initial [A-Za-z_0-9]+' -g '*.v' .`
 returns twenty-nine distinct two-word matches tree-wide.  Five are prose
 inside comments ("Initial object", "Initial and", "Initial in", "Initial
 structure", and "Initial Algebra" in the paper title at
 Structure/Initial.v).  Of the remaining twenty-four, twenty-one name
 a category outright (`AST`, `Ab`, `Algs`, `CMon`, `Cat`, `Coq`, `Field`,
 `FinSet`, `Grp`, `MonS`, `Nat_Proset`, `Par`, `ParE`, `PointedSets`,
 `Props`, `QuiverCategory`, `Rel`, `Rig`, `Rng`, `Sets`, `Top`) and three
 are variables: `C`, the ambient category of the surrounding
 construction; `D`, the target of an equivalence, at
 Theory/Equivalence/Terminal.v; and `K`, which occurs only inside
 comments, at Theory/Universal/Arrow/Dual.v and
 Test/ProbeCouniversal.v.  That is a search over the SPELLING of the
 hypothesis, not over its meaning: it establishes that nothing in tree
 writes an initial-object hypothesis on a category occupying the index
 position of a diagram.  It does not rule out an equivalent statement
 phrased in some other way.  The two subsidiary searches quoted below are
 run the same way.

 Two further absences, each checked by its own search and each the reason
 a checkbox below had to be BUILT rather than instantiated.
 `Instance/One.v`'s [Cat_Terminal] makes `_1` the terminal object OF
 Cat; that is not `_1` having an initial object WITHIN itself, which is
 what the point-diagram corollary needs, and `rg 'Terminal _1|Initial _1'`
 finds no such instance.  Likewise `rg 'Terminal.*Ordinal|ord_top'`
 returns nothing, so the top stage of a successor ordinal had to be
 named and its terminality proved.

 STRENGTHS, MEASURED.  Every identification below marked `eq_refl` is
 shipped as an [Example] with that proof term, so the claim is machine
 checked rather than asserted.  On the nose: the limit's legs are
 `fmap[F] zero` ([initial_leg_strict]); the apex is `F 0`
 ([initial_apex_strict]); the mediator out of a competing cone IS that
 cone's leg at 0 ([initial_med_strict]); the bundled [Limit]'s cone is
 the evaluation cone ([initial_Limit_strict]); the [Limit] recovered from
 the terminal object of [Cones F] has that same cone
 ([initial_Cones_strict]); and on the dual side the four covariant
 accessors [cocone_inj], [colimit_inj], [colimit_med] and [colimit_apex]
 all reduce to the evaluation data ([terminal_cocone_strict],
 [terminal_inj_strict], [terminal_med_strict],
 [terminal_apex_strict]).  The five witness identifications are `eq_refl`
 too: [point_Cones_strict], [point_Sets_apex], [point_Sets_med],
 [ordinal_omega_apex] and [ordinal_omega_bot].

 Only up to `≈`: [initial_leg_id] (`fmap[F] zero ≈ id` at the initial
 object) — it needs both [zero_unique] and [fmap_id], neither of which is
 a conversion.  That rejection at `eq_refl` was MEASURED, by stripping
 the statement to `Definition … := eq_refl` and reading a genuine
 `cannot unify "initial_leg I F 0" and "id{C}"`, and it is PINNED as
 negative 1 of Test/ProbeLimitInitial334.v.  The same holds of the second
 measured rejection: [Limit_Cones] at [initial_Cones_Terminal] and
 [initial_Limit] agree on their cone components by `eq_refl`
 ([initial_Cones_strict], shipped) yet are not convertible as whole
 [Limit] records; that non-convertibility was measured the same way and
 is pinned as negative 2 of the same probe file.  The
 mediator-commutation and uniqueness
 lemmas are `≈` statements because they are equations between morphisms
 of C, which is the library's setoid discipline and not a weakness.


 UNIVERSES, MEASURED IN THE CONSTRAINT BLOCKS.  [initial_IsALimit] and
 [initial_Limit] display as `@{u u0 u1 u2 u3 u4}` over
 `J : Category@{u u0 u0}` and `C : Category@{u1 u2 u2}` with `u0 = u2` in
 the block, so J's hom level is identified with its proof level and with
 C's hom and proof levels; the two OBJECT universes `u` and `u1` stay
 FREE (they carry only the bounds `u <= u3` and `u1 <= u4`).  That
 identification is the DONOR's and is not introduced here — but it is
 NOT [IsALimit]'s alone, and an earlier draft of this header said it
 was.  Measured in a section declaring the levels apart
 (`Constraint jh < jp`): `ACone c F` and `Cone F` both elaborate, while
 `cone_leg N x` and `IsLimitCone N`
 (Structure/Limit/Preservation.v) and `IsALimit F c`
 (Structure/Limit.v) are ALL rejected,
 each with the same `Cannot enforce jp = jh because jh < jp`.  So there
 are at least three co-equal donors, TWO OF THEM CONE VOCABULARY, and
 the `ACone`/`Cone` control does not show the cause to be [IsALimit]
 rather than the cones — it rules out those two constants and nothing
 more.  Nor is [IsALimit] the donor this file meets first: [initial_med]
 already displays `u0 = u2` while its type mentions no [IsALimit] at all
 (its body is `cone_leg N initial_obj`), and [initial_IsALimit]
 INHERITS the identification rather than introducing it; [initial_leg],
 by contrast, carries only the bound `u0 <= u2`.  All three rejections
 and both controls are PINNED, as negatives 3-5 of
 Test/ProbeLimitInitial334.v.  None of the three donors carries universe
 annotations, so this remains a repairable annotation defect; it is not
 claimed that the identification is unavoidable.

 SEVEN constants carry `Set` in a constraint block — not one, as an
 earlier draft of this header said: [bool_set], [elt_acone],
 [elt_acone_obligation_1], [elt_cone], [point_Sets_apex],
 [point_Sets_med] and [point_Sets_separates], every one of them
 `Set < u` traceable to [bool_set]'s carrier `bool : Set`.  That draft
 named [bool_set] as the CAUSE while omitting it from the list of one,
 which was self-inconsistent as well as undercounted.  This is the
 ordinary price of a concrete witness and it stays local to the [Sets]
 block.  An eighth constant, [ordinal_omega_apex], mentions `Set` in a
 universe INSTANCE (`colimit_apex@{Set u Set Set}`) while acquiring no
 constraint of its own — an instance is not a constraint, and the two
 are counted separately here.  The corollaries proper do carry no `Set`:
 [point_IsALimit], [ordinal_succ_IsAColimit], [One_Initial],
 [Omega_Initial], [Ordinal_Succ_Terminal] and [Omega_no_Terminal] have
 `Set` in no constraint block.

 THE HONEST BICONDITIONAL.  Structure/Limit/Terminal.v states its result
 as an iff, and the pattern is worth matching where it can be matched.
 Here it cannot be matched in the obvious place: nothing in the converse
 direction holds, since a diagram may have a limit for reasons having
 nothing to do with its shape, and NO biconditional of the form
 `Limit F ↔ Initial J` is stated or proved below.  What IS delivered as
 an iff is [limiting_iff_initial_leg_iso]: a cone N over F is limiting
 exactly when its leg at the initial object is invertible.  Both
 directions are proved, the forward one from the two mediators' round
 trips and the backward one by transporting along the resulting cone
 isomorphism ([limitcone_transport]).  The dual
 [colimiting_iff_terminal_inj_iso] is that statement instantiated at the
 opposite categories and then composed with the field permutation of
 [iso_of_op]/[iso_to_op] — invertibility at C^op and at C are the same
 data in a different field order — so no second argument is given.

 NAMING HAZARD, DISCLOSED AND NOT ACTED ON.  Functor/Structure/Terminal.v
 declares `Notation "'InitialFunctor' F" := (@TerminalFunctor _ _
 (F^op) _ _)`, so in this tree "initial functor" means "preserves the
 initial object".  The standard meaning of "initial functor" is the
 cofinality notion recalled above — the one under which the inclusion of
 an initial object into J is the reason this file's theorem is true.  The
 two senses are unrelated.  NOTHING IS RENAMED HERE; the collision is
 recorded so that whoever lands the cofinality vocabulary can resolve it
 there, which is where the issue asks for the fix.

 NOTHING IS REGISTERED FOR INSTANCE RESOLUTION.  [One_Initial],
 [Omega_Initial], [Ordinal_Succ_Terminal] and [initial_Cones_Terminal]
 are plain [Program Definition]s, not [Instance]s: a globally visible
 `Terminal (Cones F)` or `Initial Omega` would change what resolution
 finds elsewhere, and every use below passes its witness explicitly.

 WHAT IS NOT DELIVERED.
 - No cofinality theory: no notion of final or initial functor in the
 cofinal sense, no restriction theorem, no proof that the inclusion of
 the initial object is an initial functor.  The essay above explains
 the result by that theory; the file does not formalize any of it.
 - No converse, in any form.  It is not shown that a shape all of whose
 diagrams have limits computed by evaluation must have an initial
 object, and no `Limit F ↔ Initial J` is claimed.
 - No shape-indexed completeness statement.  Structure/Complete.v's
 [Complete] quantifies over ALL shapes, so it is not inhabited by a
 result about one shape, and no "has all limits of shape J" class
 exists in tree to inhabit; none is introduced.
 - No preservation, reflection or creation results: nothing here says
 that an arbitrary functor carries these limits to limits.
 - No uniqueness-up-to-unique-isomorphism restatement:
 Structure/Limit/Unique.v is neither instantiated nor re-derived, and
 no claim is made here about how it bears on these limits.
 - No weighted or enriched version, and no relation to
 Structure/Limit/Kan/Pointwise.v.
 - Riehl's ω+1 is NOT instantiated, and no ω+1 category exists in tree.
 What is delivered for deliverable 4 is (a) the FINITE successor
 ordinals `Ordinal (S n)`, whose top stage is proved terminal, and
 (b) [Omega_no_Terminal], the half of Riehl's remark that ω itself
 supplies: ω has an initial object ([Omega_Initial], so limits over ω
 ARE evaluation at stage 0) and provably no terminal object, which is
 exactly why a sequential colimit indexed by ω is not its value
 anywhere.  Nothing below claims `Ordinal (S n)` is ω+1.
 - Theory/Shapes.v's [point_of F := F ttt] names the same object as
 the apex of the point-diagram corollary below, but that file is NOT
 required here (it drags Equations, StrictCat, Two, Comma and Arrow),
 so this is a cross-reference and not reuse.  The five in-tree
 [bool_setoid_object] definitions (Instance/Sets.v,
 Theory/Concrete.v, Theory/Algebra/Rig.v, Instance/Top.v,
 Instance/Met/Extended.v) are a different matter — see the note at
 [bool_set] below, which corrects an earlier claim about them.  The
 same holds of [iso_of_op]/[iso_to_op]: Theory/Morphisms/CokernelPair.v
 already carries that field permutation, and that module is not
 required here either. 

 --------
 Mac Lane：    《为在职数学家而作的范畴论》，第2版（GTM 5），
 §III.4 练习 3，书页 72    [maclane:III.4:ex3]
 Fong-Spivak：应用范畴论导引（七个草图），
 §3.5.3 练习 3.98
 Riehl：       《语境中的范畴论》，第2版，§3.1，示例和
 练习 3.1.vii
 nLab：         https://ncatlab.org/nlab/show/final+functor
 nLab：         https://ncatlab.org/nlab/show/limit该陈述。 如果索引范畴 J 具有初始对象 0，那么每个图 F : J ⟶ C 都有极限，并且在 C 中无需任何构造即可得到它：极限就是 F 0 的值，其在 x 处的箭头是唯一箭头 ¡ : 0 ~> x 的像 fmap [F] ¡。锥的一致性是显而易见的，因为 fmap [F] f ∘ fmap [F] ¡ ≈ fmap [F] (f ∘ ¡) ≈ fmap [F] ¡，这来源于从 0 出发的箭头的唯一性；而来自一个竞争锥 N 的中介箭头只是 N 在 0 处的自身箭头，这是被迫如此，因为极限在 0 处的箭头是 fmap [F] ¡₀，其中 ¡₀ ≈ id，同样由唯一性决定。对偶地，J 的终对象通过在其上的取值来计算余极限。为什么这个结果并不是一个奇怪的现象。它是终极（余终极）函子理论的零元情况：当可以通过沿 K 限制来计算 J 上的余极限时，函子 K : A ⟶ J 被称为终极函子；当可以计算极限时，被称为初始函子（nLab，“final functor”）。J 的初始对象的包含是一个初始函子，而终对象的包含是一个终极函子；限制到单个对象时没有什么需要粘合，因此（余）极限就是该处的值。在这棵树中不存在余终极性相关的词汇，这里也没有引入——参见“未提供内容”。与 Structure/Limit/Terminal.v 的关系。那个文件是另一种极端退化的形状：J 为空，其中一个圆锥没有腿，并且极限是 C 的终对象。空范畴没有对象，因此也没有初对象，所以 [Terminal_Limit] 在这里不是任何东西的实例，这里的任何东西也不是它的实例。这两个文件是兄弟关系，而不是彼此的细化。还要注意每个文件中哪个范畴提供了通用对象：在那里，是目标 C 的终对象；这里，是形状 J 的初对象。缺失的内容，以及精确是什么搜索能够确定它。该树没有约束索引类别自身初始对象的语句。两个搜索是证据，且该主张以它们为范围；两者都是在排除此文件（`-g '!Structure/Limit/Initial.v'`）的情况下运行的，因为该文件现在提供了涉及的匹配。首先，`rg 'Initial J\b|@Initial J\b' -g '*.v' .` 没有返回任何结果。其次，词界调查 `rg -o -N '\b@?Initial  [A-Za-z_0-9]ZZ +' -g '*.v' .` 返回了树中 29 个不同的两词匹配。其中五个是注释中的散文（“Initial object”、“Initial and”、“Initial in”、“Initial structure”，以及论文标题 Structure/Initial.v 中的“Initial Algebra”）。在剩下的二十四个中，二十一项直接命名了一个类别 (`AST`, `Ab`, `Algs`, `CMon`, `Cat`, `Coq`, `Field`, `FinSet`, `Grp`, `MonS`, `Nat_Proset`, `Par`, `ParE`, `PointedSets`, `Props`, `QuiverCategory`, `Rel`, `Rig`, `Rng`, `Sets`, `Top`)，三项是变量：`C`，周围构造的环境类别；`D`，在 Theory/Equivalence/Terminal.v 中作为等价的目标；以及 `K`，仅在 Theory/Universal/Arrow/Dual.v 和 Test/ProbeCouniversal.v 中的注释内出现。这是对假设拼写的搜索，而不是对其含义的搜索：它确定在树中没有任何内容在图的索引位置上写初始对象假设。它并不排除以其他方式表达的等效陈述。下面引用的两个辅助搜索也是以相同的方式运行的。另外两个缺失，每一个都通过各自的搜索进行检查，每一个的原因是在下面的复选框必须被构建而不是实例化。`Instance/One.v` 的 [Cat_Terminal] 使得 `_1` 成为 Cat 的终对象；这并不是 `_1` 在自身内部具有初始对象，这是点图推论所需要的，而 `rg 'Terminal _1|Initial _1'` 没有找到这样的实例。同样地，`rg 'Terminal.*Ordinal|ord_top'` 也没有返回任何内容，所以一个后继序数的最高阶段必须被命名，并证明其终性。强度，已测量。下列所有标记 `eq_refl` 的标识都作为 [Example] 发送，并附有该证明术语，因此该主张是机器检查的，而非主张。准确地说：极限的腿是 `fmap [F]ZZ  zero`（[initial_leg_strict]）；顶点是 `F 0`（[initial_apex_strict]）；竞争锥的中介器是该锥在 0 处的腿（[initial_med_strict]）；捆绑的 [Limit] 的锥是评估锥（[initial_Limit_strict]）；从 [Cones F] 的终对象恢复的 [Limit] 具有相同的锥（[initial_Cones_strict]）；在对偶方面，四个协变访存器 [cocone_inj]、[colimit_inj]、[colimit_med] 和 [colimit_apex] 都简化为评估数据（[terminal_cocone_strict]、[terminal_inj_strict]、[terminal_med_strict]、[terminal_apex_strict]）。五个见证标识也是 `eq_refl`：[point_Cones_strict]、[point_Sets_apex]、[point_Sets_med]、[ordinal_omega_apex] 和 [ordinal_omega_bot]。

 仅限于 `≈` ： [initial_leg_id] （初始对象为 `fmap [F]ZZ  zero ≈ id`）——它需要同时具备 [zero_unique] 和 [fmap_id]，它们都不是转换。`eq_refl` 的拒绝是通过剥离到 `Definition … := eq_refl` 并读取真实的 `cannot unify "initial_leg I F 0" and "id{C}"` 来测量的，并且它被固定为 Test/ProbeLimitInitial334.v 的负 1。同样适用于第二次测量的拒绝：[Limit_Cones] 在 [initial_Cones_Terminal] 和 [initial_Limit] 上通过 `eq_refl` （[initial_Cones_strict]，已发货）在其锥形组件上达成一致，但作为完整 [Limit] 记录并不可转换；这种不可转换性是用相同方式测量的，并被固定为同一探针文件的负 2。中介-换位和唯一性引理是 `≈` 陈述，因为它们是 C 的态射之间的方程，而 C 是库的等价类学科，而不是一个弱点。宇宙，以约束块进行测量。[initial_IsALimit] 和 [initial_Limit] 显示为 `@{u u0 u1 u2 u3 u4}` 在 `J : Category@{u u0 u0}` 和 `C : Category@{u1 u2 u2}` 上，并且在块中有 `u0 = u2`，因此 J 的同态层级与其证明层级以及 C 的同态和证明层级相对应；两个对象宇宙 `u` 和 `u1` 保持自由（它们仅携带边界 `u <= u3` 和 `u1 <= u4`）。这种对应关系是捐赠者的，并没有在此引入——但它并非 [IsALimit] 单独的，早期该标题的草稿曾说它是。在声明层级分开的部分（`Constraint jh < jp`）中测量：`ACone c F` 和 `Cone F` 都展开，而 `cone_leg N x` 和 `IsLimitCone N`（Structure/Limit/Preservation.v）以及 `IsALimit F c`（Structure/Limit.v）都被拒绝，每个都有相同的 `Cannot enforce jp = jh because jh < jp`。所以至少有三个同等贡献者，其中两个是 CONE 词汇，而 `ACone` / `Cone` 控件并未显示原因是 [IsALimit] 而非锥体——它仅排除了那两个常量而已。[IsALimit] 并不是此文件首先遇到的捐赠者：[initial_med] 已经显示 `u0 = u2`，而其类型根本未提及 [IsALimit]（其主体是 `cone_leg N initial_obj`），而 [initial_IsALimit] 继承了该标识而非引入它；相比之下，[initial_leg] 仅携带绑定的 `u0 <= u2`。所有三个拒绝和两个控件都被固定，作为 Test/ProbeLimitInitial334.v 的负面 3-5。三位捐赠者都不携带宇宙注释，所以这仍然是可修复的注释缺陷；并不声称该标识是不可避免的。在一个约束块中有七个常数携带 `Set`——而不是早期草稿中所说的一个：[bool_set]、[elt_acone]、[elt_acone_obligation_1]、[elt_cone]、[point_Sets_apex]、[point_Sets_med] 和 [point_Sets_separates]，它们每一个都可以追溯到 [bool_set] 的载体 `bool : Set`。那个草稿将 [bool_set] 命名为原因（CAUSE），但却从单一列表中省略了它，这既自相矛盾又数量不足。这是具体证据的普通代价，并且它保留在 [Sets] 块的本地。第八个常数 [ordinal_omega_apex] 在一个宇宙实例（`colimit_apex@{Set u Set Set}`）中提到 `Set`，但没有获得自己的约束——实例不是约束，这两者在这里被单独计数。正的推论确实不包含 `Set` ：
 [point_IsALimit] 、 [ordinal_succ_IsAColimit] 、 [One_Initial] 、
 [Omega_Initial] 、 [Ordinal_Succ_Terminal] 和 [Omega_no_Terminal] 在任何约束块中都没有 `Set` 。诚实的双条件。Structure/Limit/Terminal.v 将其结果表述为一个 iff，并且该模式值得在可以匹配的地方进行匹配。在显而易见的地方无法匹配：在逆方向上没有任何事成立，因为一个图可能因与其形状无关的原因而具有极限，并且下面没有陈述或证明形如 `Limit F ↔ Initial J` 的任何双条件。确实作为 iff 给出的为 [limiting_iff_initial_leg_iso]：一个 F 上的圆锥 N 恰好当其在初始对象的腿可逆时为极限。两个方向都已证明，正向的证明来自两个中介的循环往返，反向的则是通过沿结果圆锥同构（[limitcone_transport]）进行传递。双重的 [colimiting_iff_terminal_inj_iso] 是将该语句在相反范畴上实例化，然后与 [iso_of_op] / [iso_to_op] 的域置换进行组合——在 C^op 和 C 上的可逆性是相同的数据，只是域顺序不同——因此没有给出第二个参数。命名风险，已披露但未采取措施。Functor/Structure/Terminal.v 声明 `Notation "'InitialFunctor' F" := (@TerminalFunctor _ _ (F^op) _ _)`，所以在这棵树中“初始函子”意味着“保持初始对象”。“初始函子”的标准含义是上文提到的上界性概念——在该概念下，将初始对象包含到 J 是本文件定理成立的原因。两种含义无关。这里没有任何重命名；冲突被记录下来，以便谁使用上界性词汇就可以在那里解决，这也是问题要求修复的地方。没有为实例解析注册任何内容。[One_Initial]、[Omega_Initial]、[Ordinal_Succ_Terminal] 和 [initial_Cones_Terminal] 都是普通的 [Program Definition]，而不是 [Instance]：一个全局可见的 `Terminal (Cones F)` 或 `Initial Omega` 会改变其他地方的解析结果，而且下面的每次使用都会明确传递其见证。未实现的内容。- 没有余终理论：没有最终或初始函子的余终概念，没有限制定理，也没有证明初始对象的包含是一个初始函子。上述文章通过该理论解释了结果；该文件没有对其进行形式化。- 没有逆定理，无论以何种形式。没有展示一个所有图的极限都可以通过求值计算的形状必须有一个初始对象，也没有声称 `Limit F ↔ Initial J`。- 没有形状索引的完备性声明。Structure/Complete.v 中的 [Complete] 对所有形状进行量化，因此不能由关于一个形状的结果填充，也没有“具有形状 J 的所有极限”的类存在于树中以填充；没有引入任何此类。- 没有保存、反映或创造的结果：这里没有说明任意函子会将这些极限映射为极限。- 没有唯一性（至同构唯一）的重述：Structure/Limit/Unique.v 既没有被实例化，也没有被重新推导，这里也没有关于它如何作用于这些极限的声明。- 没有加权或增强版本，也没有与 Structure/Limit/Kan/Pointwise.v 的关系。- Riehl 的 ω+1 没有被实例化，并且在树中不存在 ω+1 范畴。交付物4交付的是 (a) 有限后继序数 `Ordinal (S n)`，其最高阶段已被证明是终端的，以及 (b) [Omega_no_Terminal]，Riehl 的注释的一半，即 ω 本身提供的内容：ω 有一个初始对象 ([Omega_Initial]，因此对 ω 的极限确实是在阶段 0 进行评估) 并且可证明没有终端对象，这正是为什么由 ω 指数的序列余积在任何地方都不是其值的原因。下面没有任何内容声称 `Ordinal (S n)` 是 ω+1。- Theory/Shapes.v 中的 [point_of F := F ttt] 与下方点图推论的顶点命名为同一个对象，但该文件在这里不是必需的（它涉及 Equations、StrictCat、Two、Comma 和 Arrow），所以这只是一个交叉引用，而不是重用。五个在树中的 [bool_setoid_object] 定义（Instance/Sets.v、Theory/Concrete.v、Theory/Algebra/Rig.v、Instance/Top.v、Instance/Met/Extended.v）是另一回事——参见下面的 [bool_set] 注释，它纠正了之前关于它们的说法。[iso_of_op] / [iso_to_op] 也是如此：Theory/Morphisms/CokernelPair.v 已经包含了该域排列，并且这里也不需要该模块。
*)

(* * ** The limit of a diagram over a shape with an initial object / * ** 具有初始对象的形状上的图的极限 *)

Section LimitFromInitial.

Context {J C : Category}.
Context (I : @Initial J).
Context (F : J ⟶ C).

(* The leg at x is the image of the unique arrow ¡ : 0 ~> x. / 在 x 的腿是唯一箭头 ¡ : 0 ~> x 的像。 *)

Definition initial_leg (x : J) : F (@initial_obj J I) ~{C}~> F x :=
  fmap[F] (@zero J I x).

(* Cone coherence is uniqueness of arrows out of 0, pushed through F. / 圆锥的相干性是从 0 出发，通过 F 推送出的箭头的唯一性。 *)

Lemma initial_leg_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[F] f ∘ initial_leg x ≈ initial_leg y.
Proof.
  unfold initial_leg.
  rewrite <- fmap_comp.
  apply fmap_respects.
  apply (@zero_unique J I).
Qed.

Definition initial_acone : ACone (F (@initial_obj J I)) F :=
  {| vertex_map     := initial_leg
   ; cone_coherence := @initial_leg_coherence |}.

Definition initial_cone : Cone F :=
  {| vertex_obj := F (@initial_obj J I)
   ; coneFrom   := initial_acone |}.

(*
 The leg AT the initial object is the identity — only up to `≈`; see the
 header's STRENGTHS paragraph for the measured rejection at `eq_refl`. 

 --------
 初始对象的腿是恒等 — 仅在 `≈` 范围内；有关在 `eq_refl` 处的测量拒绝，请参阅标题的 STRENGTHS 段落。
*)

Lemma initial_leg_id : initial_leg (@initial_obj J I) ≈ id.
Proof.
  unfold initial_leg.
  rewrite (@zero_unique J I _ (@zero J I (@initial_obj J I)) id).
  apply fmap_id.
Qed.

(* The mediator from a competing cone is that cone's own leg at 0. / 来自竞争锥体的中介是该锥体在 0 的自身边。 *)

Definition initial_med (N : Cone F) :
  vertex_obj[N] ~{C}~> F (@initial_obj J I) :=
  cone_leg N (@initial_obj J I).

Lemma initial_med_commutes (N : Cone F) (x : J) :
  initial_leg x ∘ initial_med N ≈ cone_leg N x.
Proof.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) _ _ (@zero J I x)).
Qed.

(*
 Uniqueness: evaluate the factorization condition at 0, where the leg is
 `≈ id`.  This is the whole content of the universal property. 

 --------
 唯一性：在0处评估分解条件，此处的支腿是 `≈ id`。这是泛性质的全部内容。
*)

Lemma initial_med_unique (N : Cone F)
  (v : vertex_obj[N] ~{C}~> F (@initial_obj J I)) :
  (∀ x : J, initial_leg x ∘ v ≈ cone_leg N x) → initial_med N ≈ v.
Proof.
  intro Hv.
  rewrite <- (Hv (@initial_obj J I)).
  rewrite initial_leg_id.
  now rewrite id_left.
Qed.

(* The three packagings: cone-level, apex-pinned, and bundled. / 三种包装：锥形级、顶针固定和捆绑装。 *)

Definition initial_IsLimitCone : IsLimitCone initial_cone :=
  fun N =>
    {| unique_obj      := initial_med N
     ; unique_property := initial_med_commutes N
     ; uniqueness      := initial_med_unique N |}.

Definition initial_IsALimit : IsALimit F (F (@initial_obj J I)) :=
  limitcone_isalimit initial_IsLimitCone.

Definition initial_Limit : Limit F :=
  limitcone_limit initial_cone initial_IsLimitCone.

(* Strictness, measured. / 严格而有分寸。 *)

Example initial_leg_strict (x : J) :
  limit_leg initial_IsALimit x = fmap[F] (@zero J I x) := eq_refl.

Example initial_apex_strict :
  @vertex_obj _ _ _ initial_cone = F (@initial_obj J I) := eq_refl.

Example initial_med_strict (N : Cone F) :
  limit_med initial_IsALimit N = cone_leg N (@initial_obj J I) := eq_refl.

Example initial_Limit_strict :
  @limit_cone _ _ _ initial_Limit = initial_cone := eq_refl.

(* * *** The evaluation cone as a terminal object of [Cones F] / * *** 作为 [Cones F] 的终端对象的评估圆锥 *)

(*
 The terminal-cone reading of the same fact: the evaluation cone is a
 terminal object of Instance/Cones.v's category of cones over F.  This is
 what Instance/Cones/Limit.v's [Limit_Cones] consumes, so the two
 presentations can be compared — see [initial_Cones_strict]. 

 --------
 同一事实的终端锥阅读：评估锥是 Instance/Cones.v 的 F 上锥类别的一个终端对象。这正是 Instance/Cones/Limit.v 的 [Limit_Cones] 所使用的，因此可以比较这两种表示——参见 [initial_Cones_strict]。
*)

Program Definition initial_Cones_Terminal : @Terminal (Cones F) := {|
  terminal_obj := initial_cone;
  one          := fun N => (initial_med N; initial_med_commutes N)
|}.
Next Obligation.
  rewrite <- (initial_med_unique x f X0).
  now rewrite <- (initial_med_unique x g X).
Qed.

Example initial_Cones_strict :
  @limit_cone _ _ _ (@Limit_Cones J C F initial_Cones_Terminal)
    = initial_cone := eq_refl.

(** *** The honest biconditional / *** 诚实的双条件 *)

(*
 A cone over F is limiting exactly when its leg at the initial object is
 invertible.  Forward: the two mediators are mutually inverse, each round
 trip being pinned by a uniqueness clause.  Backward: that inverse is a
 cone isomorphism from the evaluation cone, along which limiting-ness
 transports. 

 --------
 当从初始对象的腿是可逆时，F 的锥正好是极限。正向：两个中介是相互逆的，每次往返都由唯一性条款固定。反向：该逆是来自评估锥的锥同构，通过它极限性得以传输。
*)

Theorem limiting_iff_initial_leg_iso (N : Cone F) :
  IsLimitCone N ↔ IsIsomorphism (cone_leg N (@initial_obj J I)).
Proof.
  split.
  - intro HN.
    unshelve refine
      {| two_sided_inverse := unique_obj (HN initial_cone) |}.
    + rewrite (unique_property (HN initial_cone) (@initial_obj J I)).
      exact initial_leg_id.
    + transitivity (unique_obj (HN N)).
      * symmetry.
        apply (uniqueness (HN N)).
        intro x.
        rewrite comp_assoc.
        rewrite (unique_property (HN initial_cone) x).
        exact (initial_med_commutes N x).
      * apply (uniqueness (HN N)).
        intro x; now rewrite id_right.
  - intro Hiso.
    unshelve refine (limitcone_transport _ initial_IsLimitCone).
    unshelve eexists.
    + unshelve refine {| to   := two_sided_inverse
                       ; from := cone_leg N (@initial_obj J I) |}.
      * apply is_left_inverse.
      * apply is_right_inverse.
    + intro x; simpl.
      rewrite <- (initial_med_commutes N x).
      rewrite <- comp_assoc.
      rewrite is_right_inverse.
      now rewrite id_right.
Qed.

End LimitFromInitial.

(* * ** Reading invertibility back from the opposite category / * **从对立范畴回读可逆性 *)

(*
 [IsIsomorphism] at C^op and at C carry the same inverse and swap their
 two law fields, so passing between them is a field permutation with no
 proof content.  Theory/Morphisms/CokernelPair.v already carries this
 pair, as [IsIsomorphism_of_op] and [op_IsIsomorphism_of]; that module is
 NOT required here — it pulls Theory/Morphisms.v, Structure/Pullback.v,
 Structure/Pushout.v, Theory/Morphisms/Stability.v and
 Theory/Morphisms/Duality.v onto every consumer — so the idiom is copied
 under names that do not collide with it. 

 --------
 [IsIsomorphism] 在 C^op 和 C 上携带相同的逆并交换它们的两个律域，因此在它们之间传递只是一个域置换，没有证明内容。Theory/Morphisms/CokernelPair.v 已经携带这个对，作为 [IsIsomorphism_of_op] 和 [op_IsIsomorphism_of]；该模块在这里不需要——它会将 Theory/Morphisms.v、Structure/Pullback.v、Structure/Pushout.v、Theory/Morphisms/Stability.v 和 Theory/Morphisms/Duality.v 引入每个使用者——所以这个用法在不与其冲突的名称下被复制。
*)

Section OpIso.

Context {C : Category}.

Definition iso_of_op {a b : C} (h : b ~> a)
  (H : @IsIsomorphism (C^op) a b h) : @IsIsomorphism C b a h :=
  @Build_IsIsomorphism C b a h
    (@two_sided_inverse (C^op) a b h H)
    (@is_left_inverse (C^op) a b h H)
    (@is_right_inverse (C^op) a b h H).

Definition iso_to_op {a b : C} (h : b ~> a)
  (H : @IsIsomorphism C b a h) : @IsIsomorphism (C^op) a b h :=
  @Build_IsIsomorphism (C^op) a b h
    (@two_sided_inverse C b a h H)
    (@is_left_inverse C b a h H)
    (@is_right_inverse C b a h H).

End OpIso.

(* * ** The dual: a terminal shape computes colimits by evaluation / * ** 对偶：终端形状通过求值计算余极限 *)

(*
 Everything here is the section above read at J^op and C^op.
 `Initial (J^op)` is notation for `Terminal ((J^op)^op)`, and
 Construction/Opposite.v builds duality so that (J^op)^op is J on the
 nose, so a `Terminal J` IS the hypothesis the primal section wants.  The
 four packagings and the two accessors are supplied by `:=` with no
 tactic.  Of the three lemmas, only [terminal_inj_id] is a single
 [exact] of a PRIMAL lemma (`@initial_leg_id (J^op) (C^op) T (F^op)`);
 an earlier draft of this header said all three were, which is wrong on
 two counts.  [terminal_med_commutes] is a single [exact] of
 [colimit_med_commutes] — a Structure/Limit/Preservation.v ACCESSOR, not
 a primal lemma of this file — and [terminal_med_unique] introduces its
 hypothesis first, so it is TWO tactics and again of an accessor.  The
 biconditional is the primal one composed with the field permutation of
 [iso_of_op]/[iso_to_op].  No second argument is given anywhere.

 The accessors are stated covariantly, in C: no `^op` appears in any type
 below, which is the point of routing through
 Structure/Limit/Preservation.v's [Cocone], [cocone_inj], [IsAColimit],
 [colimit_inj] and [colimit_med]. 

 --------
 这里的一切都是在 J^op 和 C^op 中读取的上一节内容。`Initial (J^op)` 是 `Terminal ((J^op)^op)` 的符号表示，Construction/Opposite.v 构建了对偶性，因此 (J^op)^op 刚好是 J，所以 `Terminal J` 是原始章节所需要的假设。四个打包和两个访问器由 `:=` 提供，无需任何策略。在三个引理中，只有 [terminal_inj_id] 是 PRIMAL 引理（`@initial_leg_id (J^op) (C^op) T (F^op)`）的单一 [exact]；本标题的早期草稿说三个都是，这是错误的，有两点原因。[terminal_med_commutes] 是 [exact] 的单一 [colimit_med_commutes]——一个 Structure/Limit/Preservation.v 的访问器，而不是本文件的原始引理——并且 [terminal_med_unique] 首先引入其假设，因此这是两个策略，并且仍然是访问器。双条件是原始的，并与 [iso_of_op] / [iso_to_op] 的域置换组合。没有在任何地方给出第二个参数。

 访问器在 C 中以协变方式声明：在下面的任何类型中都没有出现 `^op`，这就是通过 Structure/Limit/Preservation.v 的 [Cocone]、[cocone_inj]、[IsAColimit]、[colimit_inj] 和 [colimit_med] 进行路由的目的。
*)

Section ColimitFromTerminal.

Context {J C : Category}.
Context (T : @Terminal J).
Context (F : J ⟶ C).

(* The injection at x is the image of the unique arrow ! : x ~> 1. / 在 x 的单射是唯一箭头 ! : x ~> 1 的像。 *)

Definition terminal_inj (x : J) : F x ~{C}~> F (@terminal_obj J T) :=
  fmap[F] (@one J T x).

Definition terminal_cocone : Cocone F :=
  @initial_cone (J^op) (C^op) T (F^op).

Definition terminal_IsColimitCocone : IsColimitCocone terminal_cocone :=
  @initial_IsLimitCone (J^op) (C^op) T (F^op).

Definition terminal_IsAColimit : IsAColimit F (F (@terminal_obj J T)) :=
  @initial_IsALimit (J^op) (C^op) T (F^op).

Definition terminal_Colimit : Colimit F :=
  @initial_Limit (J^op) (C^op) T (F^op).

(*
 The mediator out of the colimit into a competing cocone is that
 cocone's own injection at the terminal object. 

 --------
 从余极限到一个竞争余锥的中介是该余锥在终端对象处的自身注入。
*)

Definition terminal_med (N : Cocone F) :
  F (@terminal_obj J T) ~{C}~> vertex_obj[N] :=
  cocone_inj N (@terminal_obj J T).

Lemma terminal_med_commutes (N : Cocone F) (x : J) :
  terminal_med N ∘ terminal_inj x ≈ cocone_inj N x.
Proof. exact (colimit_med_commutes terminal_IsAColimit N x). Qed.

Lemma terminal_med_unique (N : Cocone F)
  (v : F (@terminal_obj J T) ~{C}~> vertex_obj[N]) :
  (∀ x : J, v ∘ terminal_inj x ≈ cocone_inj N x) → terminal_med N ≈ v.
Proof. intro Hv. exact (colimit_med_unique terminal_IsAColimit N v Hv). Qed.

Lemma terminal_inj_id : terminal_inj (@terminal_obj J T) ≈ id.
Proof. exact (@initial_leg_id (J^op) (C^op) T (F^op)). Qed.

(* Strictness of the covariant accessors, measured. / 协变访问器的严格性，已测量。 *)

Example terminal_cocone_strict (x : J) :
  cocone_inj terminal_cocone x = terminal_inj x := eq_refl.

Example terminal_inj_strict (x : J) :
  colimit_inj terminal_IsAColimit x = terminal_inj x := eq_refl.

Example terminal_med_strict (N : Cocone F) :
  colimit_med terminal_IsAColimit N = terminal_med N := eq_refl.

Example terminal_apex_strict :
  colimit_apex terminal_Colimit = F (@terminal_obj J T) := eq_refl.

(*
 The dual biconditional.  The primal theorem supplies both directions
 with no second argument; the only residue is that invertibility at C^op
 and at C are the same data in a different field order, which [iso_of_op]
 and [iso_to_op] permute. 

 --------
 对偶双条件。原始定理提供两个方向
 没有第二参数;唯一的剩余是 C^op 处的可逆性
 在C中是相同但场序不同的数据，[iso_of_op]
 并且[iso_to_op]置换。
*)

Definition colimiting_iff_terminal_inj_iso (N : Cocone F) :
  IsColimitCocone N ↔ IsIsomorphism (cocone_inj N (@terminal_obj J T)) :=
  (fun H => iso_of_op _
     (fst (@limiting_iff_initial_leg_iso (J^op) (C^op) T (F^op) N) H),
   fun H => snd (@limiting_iff_initial_leg_iso (J^op) (C^op) T (F^op) N)
     (iso_to_op _ H)).

End ColimitFromTerminal.

(* * ** Deliverable: the point shape (Seven Sketches §3.5.3 Ex 3.98) / * ** 可交付成果：点形状（七个草图 §3.5.3 习题 3.98） *)

(*
 `_1` has an initial object — its unique object — and that instance did
 not exist: Instance/One.v's [Cat_Terminal] says `_1` is terminal in
 Cat, a different statement (see the header). 

 --------
 `_1` 有一个初始对象——它的唯一对象——而那个实例不存在：Instance/One.v 的 [Cat_Terminal] 说 `_1` 在 Cat 中是终端的，这是一个不同的声明（见头部）。
*)

Program Definition One_Initial : @Initial _1 := {|
  terminal_obj := ttt;
  one          := fun _ => ttt
|}.
Next Obligation. now destruct f, g. Qed.

(*
 The limit of a diagram of shape 1 is its value at the point.  This is
 the section-1 theorem instantiated, not a second construction. 

 --------
 形状 1 的图的极限是其在该点的值。这是第 1 节定理的实例化，而不是第二个构造。
*)

Definition point_cone {C : Category} (F : _1 ⟶ C) : Cone F :=
  @initial_cone _1 C One_Initial F.

Definition point_IsALimit {C : Category} (F : _1 ⟶ C) :
  IsALimit F (F ttt) := @initial_IsALimit _1 C One_Initial F.

Definition point_Limit {C : Category} (F : _1 ⟶ C) : Limit F :=
  @initial_Limit _1 C One_Initial F.

(*
 The cross-check the exercise asks for: the same cone is a TERMINAL
 OBJECT of the category of cones, and the [Limit] that
 Instance/Cones/Limit.v reads off it is the very cone built above. 

 --------
 交叉检查练习所要求的：相同的圆锥是圆锥类别的一个终对象，而 Instance/Cones/Limit.v 上读取的 [Limit] 正是上述构建的圆锥。
*)

Definition point_Cones_Terminal {C : Category} (F : _1 ⟶ C) :
  @Terminal (Cones F) := @initial_Cones_Terminal _1 C One_Initial F.

Example point_Cones_strict {C : Category} (F : _1 ⟶ C) :
  @limit_cone _ _ _ (@Limit_Cones _1 C F (point_Cones_Terminal F))
    = point_cone F := eq_refl.

(** *** A computing witness in Sets / *** 集合中的计算见证 *)

(*
 [bool_set] is a REDUNDANT REDECLARATION, and an earlier draft of this
 note gave a reason for it that is false.  That draft said the tree had
 TWO [bool_setoid_object] definitions, in Theory/Concrete.v and
 Theory/Algebra/Rig.v, "neither of which this file has any other reason
 to require".  There are FIVE, and one of them — Instance/Sets.v,
 `bool_setoid_object@{t u}` — is byte-identical in content to [bool_set]
 and lives in a module this file ALREADY requires.  It is
 convertible on the nose (`bool_setoid_object = bool_set := eq_refl`
 compiles against this file's own import list, no new Require), and both
 [Sets] witnesses below replay verbatim against it.  So the copy was
 never forced.  It is kept rather than removed because deleting it is a
 code change, not a correction of the record.  The cone apex, by
 contrast, IS reused
 — it is Instance/Sets.v's terminal singleton, so a cone over a point
 diagram with that apex is literally a global element, and the mediator
 below is the element it names. 

 --------
 [bool_set] 是一个多余的重新声明，早期的该说明草稿给出的原因是错误的。该草稿说该树在 Theory/Concrete.v 和 Theory/Algebra/Rig.v 中有两个 [bool_setoid_object] 定义，“这两个文件都没有其他理由被本文件需要”。实际上有五个，其中一个——Instance/Sets.v 中的 `bool_setoid_object@{t u}`——在内容上与 [bool_set] 完全相同，并且位于本文件已经需要的模块中。它是完全可转换的（`bool_setoid_object = bool_set := eq_refl` 可对照本文件自身的导入列表编译，无需新的 Require），下面的两个 [Sets] 证人也可以逐字对其重放。因此，这个副本从未被强制存在。它被保留而不是删除，因为删除它是代码更改，而不是记录修正。相比之下，锥顶是被重复使用的 —— 它是 Instance/Sets.v 的终端单例，所以以该顶点为锥顶的点图形字面上是一个全局元素，而下面的中介者就是它所命名的元素。
*)

Program Definition bool_set : obj[Sets] :=
  {| carrier := bool ; is_setoid := {| equiv := eq |} |}.

Program Definition elt_acone (b : bool) :
  ACone (@terminal_obj Sets Sets_Terminal) (=(bool_set)) := {|
  vertex_map := fun _ => {| morphism := fun _ => b |}
|}.

Definition elt_cone (b : bool) : Cone (=(bool_set)) :=
  {| vertex_obj := @terminal_obj Sets Sets_Terminal
   ; coneFrom   := elt_acone b |}.

Example point_Sets_apex :
  @vertex_obj _ _ _ (@limit_cone _ _ _ (point_Limit (=(bool_set))))
    = bool_set := eq_refl.

(* The mediator computes: it is the element the competing cone names. / 调解者计算：它是竞争圆锥所命名的元素。 *)

Example point_Sets_med (b : bool) :
  limit_med (point_IsALimit (=(bool_set))) (elt_cone b) ttt = b := eq_refl.

(*
 Non-degeneracy, and it is worth being exact about what this adds.  The
 identification `limit_med … N = cone_leg N 0` holds at ARBITRARY
 arguments ([initial_med_strict]), so instantiating it proves nothing on
 its own.  What is specific to this diagram is that two cones over it
 have provably different mediators, so the limit apex has at least two
 distinct elements.  Be exact about the MECHANISM too: because the
 mediator is DEFINITIONALLY the cone's leg, the statement reduces to
 `true <> false` and [discriminate] closes it — no commutation or
 uniqueness lemma is consumed, so it is not the universal property that
 separates, as an earlier draft of this note said.  What the example
 establishes is the apex's two distinct elements, which is what makes
 the corollary non-degenerate: over a subsingleton apex any two
 mediators would agree automatically. 

 --------
 非退化，并且值得准确说明这增加了什么。等式 `limit_med … N = cone_leg N 0` 在任意参数 ([initial_med_strict]) 下都成立，所以仅仅实例化它本身并不能证明任何东西。这个图的具体之处在于，它上面的两个锥可以被证明有不同的中介者，因此极限顶点至少有两个不同的元素。也要准确说明其机制：因为中介者在定义上就是锥的边，所以该命题简化为 `true <> false`，并且 [discriminate] 使其闭合——没有使用任何交换性或唯一性引理，因此并不是一些早期草稿所说的普遍性质起了关键作用。这个例子所证明的是顶点的两个不同元素，这正是使得推论非退化的原因：在子单元素顶点上，任何两个中介者都将自动相同。
*)

Example point_Sets_separates :
  limit_med (point_IsALimit (=(bool_set))) (elt_cone true) ttt
    <> limit_med (point_IsALimit (=(bool_set))) (elt_cone false) ttt.
Proof. discriminate. Qed.

(* * ** Deliverable: successor ordinals (Riehl §3.1) / * ** 可交付成果：后继序数 (Riehl §3.1) *)

(* The top stage of `Ordinal (S n)`, and its bottom stage, neither of which was named in Instance/Ordinal.v. / `Ordinal (S n)` 的最上层和最下层，它们都没有在 Instance/Ordinal.v 中命名。 *)

Definition ord_top (n : nat) : Ord_obj (S n) := ord_at n le_t_n.

Definition ord_bot (n : nat) : Ord_obj (S n) :=
  ord_at 0 (le_t_SS (le_t_zero n)).

Lemma ord_top_neq_bot (n : nat) : ord_top (S n) <> ord_bot (S n).
Proof. intro H; discriminate (f_equal ord_val H). Qed.

(* The top stage is terminal: the arrow from x is the bound of x with one successor peeled off both sides, and uniqueness is thinness of `le_t`. / 顶层阶段是终端的：来自 x 的箭头是 x 的界限，两边都剥离了一个后继，唯一性是 `le_t` 的稀薄性。 *)

Program Definition Ordinal_Succ_Terminal (n : nat) :
  @Terminal (Ordinal (S n)) := {|
  terminal_obj := ord_top n;
  one          := fun x => le_t_SS_inv (ord_bound x)
|}.
Next Obligation. apply le_t_irr. Qed.

(* Hence: the colimit of a diagram indexed by a successor ordinal is its value at the top stage. / 因此：由后继序数索引的图表的余极限就是它在最高阶段的值。 *)

Definition ordinal_succ_IsAColimit {n : nat} {C : Category}
  (G : Ordinal (S n) ⟶ C) : IsAColimit G (G (ord_top n)) :=
  @terminal_IsAColimit (Ordinal (S n)) C (Ordinal_Succ_Terminal n) G.

Definition ordinal_succ_Colimit {n : nat} {C : Category}
  (G : Ordinal (S n) ⟶ C) : Colimit G :=
  @terminal_Colimit (Ordinal (S n)) C (Ordinal_Succ_Terminal n) G.

(*
 A witness whose diagram genuinely varies from stage to stage:
 Instance/Ordinal.v's embedding of `Ordinal (S n)` into ω sends a stage
 to its own index, so the colimit apex is the numeral n and the bottom
 stage is 0.  The same honesty note applies as in the [Sets] witness:
 `colimit_apex … = G (ord_top n)` holds at ARBITRARY G
 ([terminal_apex_strict]), so the apex computation alone shows nothing.
 What is specific here is [ordinal_omega_nonconstant] — the diagram takes
 different values at the bottom and top stages, so "the colimit is the
 value at the top stage" is not a statement about a constant diagram. 

 --------
 一个从阶段到阶段确实变化的图的见证者：
 实例/Ordinary.v 中将 `Ordinal (S n)` 嵌入 ω，将阶段映射到其自身索引，因此余极限顶点是数词 n，而底阶段是 0。与 [Sets] 的见证者类似，需要注意同样的诚实问题：
 `colimit_apex … = G (ord_top n)` 在任意 G ([terminal_apex_strict]) 上成立，因此仅凭顶点计算无法说明任何问题。
 这里的特殊之处在于 [ordinal_omega_nonconstant]——该图在底阶段和顶阶段取不同的值，因此“余极限是顶阶段的值”并不是关于恒定图的陈述。
*)

Example ordinal_omega_apex (n : nat) :
  colimit_apex (ordinal_succ_Colimit (Ord_Omega (S n))) = n := eq_refl.

Example ordinal_omega_bot (n : nat) :
  Ord_Omega (S n) (ord_bot n) = 0%nat := eq_refl.

Lemma ordinal_omega_nonconstant (n : nat) :
  Ord_Omega (S (S n)) (ord_bot (S n))
    <> Ord_Omega (S (S n)) (ord_top (S n)).
Proof. discriminate. Qed.

(* * *** Why ω itself is outside the colimit half of the theorem / * *** 为什么 ω 本身位于定理的余极限半之外 *)

(*
 ω has an initial object, so LIMITS over ω are evaluation at stage 0 by
 the first section — and provably no terminal object, so the second
 section says nothing about colimits over ω.  That asymmetry is Riehl's
 reason for indexing sequential colimits by ω rather than by a successor
 ordinal: over a successor ordinal the colimit is the top stage and
 nothing is glued.  Note that `Ordinal (S n)` is a FINITE successor
 ordinal; ω+1 is not a category in this tree and is not claimed to be. 

 --------
 ω 有一个初始对象，所以对 ω 的极限在第 0 阶段由第一节进行评估——并且可证明没有终对象，所以第二节没有关于 ω 上余极限的内容。这种不对称是 Riehl 将序列余极限按 ω 编号而不是按继承序数编号的原因：在继承序数上，余极限就是最高阶段，什么也没有被粘合。请注意，`Ordinal (S n)` 是一个有限继承序数；ω+1 在此树中不是一个范畴，也没有声称它是。
*)

Program Definition Omega_Initial : @Initial Omega := {|
  terminal_obj := 0%nat;
  one          := fun x => le_t_zero x
|}.
Next Obligation. apply le_t_irr. Qed.

Theorem Omega_no_Terminal : @Terminal Omega → False.
Proof.
  intro T.
  exact (le_t_no_desc (@one Omega T (S (@terminal_obj Omega T)))).
Qed.
