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

Generalizable All Variables.

(* * * Pointwise limits in a functor category / * * 函子范畴中的逐点极限 *)

(*
 Mac Lane §V.3 Theorem 1 and Corollary 1 (book pp. 115-116;
 maclane:V.3:thm1, maclane:V.3:cor1); Awodey §8.5 Proposition 8.7 and its
 Corollary (presheaf categories are complete, evaluation preserves
 limits); Riehl §3.4 Proposition 3.4.9 (limits in a functor category are
 pointwise, and evaluation preserves them).
 nLab: https://ncatlab.org/nlab/show/functor+category
 https://ncatlab.org/nlab/show/limit

 BACKGROUND.  A diagram D : J ⟶ [P, X] of functors has, at each object p
 of P, an evaluated diagram Eval p ◯ D : J ⟶ X.  When each of these has a
 limit in X, the limit apexes assemble into a functor P ⟶ X whose arrow
 part is the mediating morphism between adjacent pointwise limits — unique
 with that property — and the pointwise legs assemble into a limiting
 cone over D in [P, X]: limits in a functor category are computed
 pointwise.  Consequently a functor category into a complete category is
 complete, every presheaf category [C^op, Sets] in particular, and
 evaluation at any object preserves all limits.  Colimits are the dual
 statement over the opposite categories; they are #715's and are not
 written here.  Creation of limits along the discrete inclusion
 (Theorem 2) is Instance/Fun/Creation.v's (#426).

 STALE PREMISES, RE-MEASURED.
 - “There is no [Terminal] structure on [C, D]”: Instance/Fun/Terminal.v's
 [Functor_Category_Terminal] (an [#[export] Instance], #339) and
 [Fun_HasIndexedProducts] exist; Instance/Fun/Cartesian.v
 [Functor_Category_Cartesian] and Instance/Fun/Pullback.v
 [Fun_HasPullbacks] too.  What was absent is the GENERAL shape and any
 preservation statement for an evaluation functor (Instance/Fun/
 Terminal.v named that gap; corrected in place here).
 - “no [Complete] inhabitant anywhere”: a declaration sweep of the
 non-Test/ tree for constants concluding [@Complete] finds at least
 thirteen, unconditional witnesses and premise-carrying transformers
 together — Instance/Sets/Complete.v's [Sets_Complete] and
 [ConeSet_Complete], Instance/Grp/Limit.v [Grp_Complete],
 Construction/Arrow/Limit.v [Arrow_Complete],
 Construction/Comma/Limit.v [Comma_Complete],
 Construction/Product/Limit.v [PiCat_Complete], [EM_Complete],
 [reflective_Complete] and more; #254 is closed, so Work item 3's
 blocker is discharged and [Presheaf_Complete] is built below.
 - “the evaluation functors do not exist”: Adjunction/Diagonal/
 Connected.v [EvalAt], and #424's Instance/Fun/Eval.v [Eval], which
 this file consumes — the dependency on #424 is real: routing through
 [EvalAt] would add 103 files to this file's closure against 2 for
 Eval.v (marginals over the shipped [Require] list; an earlier revision
 said 115, measured against a list without Instance/Sets/Complete.v).
 - Prose sites (Work item 4), all edited LINE-NEUTRALLY: one in
 Instance/Fun.v (the issue's range overshoots it into a neighbouring
 clause, on
 cartesian closure, which Instance/Fun/Closed.v refutes and which is
 untouched), two in Instance/Fun/Cartesian.v (the issue's range for
 the first overshoots likewise; the second now cites
 [Functor_Category_Terminal]), one in Structure/
 Complete.v (the issue's range starts a line early; the monadic
 clause's own words are untouched — it is [EM_Complete]'s — though
 one of them gained “from Sets”), the fourth site the issue misses,
 Structure/Cartesian/Product.v, and two in Instance/Fun/Terminal.v
 (that file's NOT DELIVERED list denied both the general
 theorem and any preservation statement, both corrected in place;
 and its “stated in PROSE in three places” framing, now that
 those places point here).  Instance/Fun.v's sentence keeps its
 colimit half, attributed to the nLab and #715.
 - Construction/Product/Limit.v's [PiCat_Complete] has term for term
 the same shape as [Functor_Category_Complete], with the projection in
 place of [Eval p]; it is an analogy, not an instance — [PiCat] is a
 dependent product of categories, not [[DiscreteCat I, X]], so neither
 derives from the other.  Its header records the same universe traps.

 WHAT IS DELIVERED (29 named constants plus 11 [Program] obligations,
 every one closed under the global context).
 (1) THE POINTWISE DATA.  Over [D : J ⟶ [P, X]] and [L : ∀ p, Limit (Eval
 p ◯ D)]: [plim_obj], [plim_alimit], [plim_leg], [plim_leg_coherence],
 and joint monicity of the legs ([plim_probe_cone],
 [plim_jointly_monic]).
 (2) THE ARROW PART.  [plim_cone_at f] (the limit at p as a cone over the
 diagram at q, legs [fmap[D j] f ∘ plim_leg p j]; coherence is the
 naturality of [fmap[D] g] followed by cone coherence), [plim_map],
 [plim_map_commutes], and Mac Lane's uniqueness [plim_map_unique].
 (3) THE LIMIT FUNCTOR.  [PointwiseLimit : P ⟶ X]: the three functor
 laws are one [plim_jointly_monic] each.
 (4) THE LIMITING CONE.  [plim_nat j : PointwiseLimit ⟹ D j],
 [PointwiseLimitCone : Cone D].
 (5) THEOREM 1.  [plim_comp_cone] (a cone in [P, X] evaluated at p),
 [plim_ump_map], [plim_ump_commutes], [plim_ump_nat] (natural by
 joint monicity), [PointwiseIsLimitCone : IsLimitCone
 PointwiseLimitCone] — uniqueness in [P, X] IS pointwise uniqueness,
 an equation of transformations reducing componentwise — and the
 issue's pinned [Functor_Category_pointwise_limit : Limit D].
 Readbacks at [eq_refl] (probe): the diagram at p, the object
 action, the leg components, the image cone's apex and legs, the
 mediator's components, the packaged limit's cone.
 (6) PRESERVATION (Riehl 3.4.9 (ii), Awodey 8.7's second clause).
 [Eval_pointwise_IsLimitCone p] — the image of the pointwise cone
 under [Eval p] is limiting with NO coercion, its apex and legs
 being the chosen limit cone's on the nose — and
 [Eval_PreservesLimitCone p : PreservesLimitCone D (Eval p)] for an
 ARBITRARY limiting cone, by [limitcone_transport] along [FCone_iso]
 of [limitcone_iso] (the construction alone gives only the
 canonical cone); [Eval_PreservesLimit] descends to the apex-only
 class.
 (7) COROLLARY 1.  [Fun_HasLimitsOfShape] in the unfolded form
 [(∀ F : J ⟶ X, Limit F) → ∀ D : J ⟶ [P, X], Limit D] — it ascribes
 at Adjunction/Diagonal/Limit.v's [HasLimitsOfShape] downstream
 (probe), and this file does not pay that import — and the issue's
 pinned [Functor_Category_Complete : Complete X → Complete [P, X]];
 [Eval_ContinuousFunctor], [Eval_PreservesAllLimits].  All four are
 ANNOTATED AT THE DEFINITION: written bare, each minimizes P's
 object universe onto its hom universe (probe N2 pins the bare form's
 refusal at [Constraint jo < jh] beside the annotated form's
 acceptance; a section-level [Universe] declaration does NOT lift it,
 measured).
 (8) PRESHEAVES (Awodey's Corollary, Work item 3).  [Presheaf_Complete C :
 Complete [C^op, Sets]] and [Presheaf_Eval_PreservesAllLimits C c]
 from Instance/Sets/Complete.v's [Sets_Complete]; the covariant twin
 [Fun_Sets_Complete].

 UNIVERSES (measured by [About] under [Set Printing Universes] on all 29
 constants).
 - The 22 constants of section [Pointwise] carry exactly four equations,
 [u0 = u2], [u0 = u4], [u0 = u6], [u2 = u4] over [J : Category@{u u0
 u0}], [P : Category@{u1 u2 u2}], [X : Category@{u3 u4 u4}]: J's hom
 = P's hom = X's hom = [P, X]'s hom, one level.  P-hom = X-hom is
 Instance/Fun.v's [Fun]; shape-hom = ambient-hom is Structure/Limit.v's
 [Limit] binder [{J : Category@{u0 u1 u1}} {C : Category@{u2 u1 u1}}],
 applied twice (once in [P, X], once in X) — probe N3 pins it: at a
 shape whose homs sit strictly below X's, the diagram and its [Cone]
 are accepted and its [Limit] is refused.  The OBJECT universes stay
 free (J's, P's and X's are three distinct levels in every block).
 - The four annotated corollaries carry exactly one equation, [jh = ch]
 ([Fun]'s), with [P : Category@{jo jh jh}] free in [jo] — e.g.
 [Functor_Category_Complete@{jo jh co ch u u0 u1 u2 u3 u4 u5} : ∀ {P :
 Category@{jo jh jh}} {X : Category@{co ch ch}}, Complete@{u u2 ch co}
 X → Complete@{u u2 jh u3} [P, X]] with [jo <= jh], [jo <= u3], [jh <
 u4], [co <= u3].
 - The three presheaf constants sit at a category with ONE level for
 objects, homs and proofs ([Presheaf_Complete] and [Fun_Sets_Complete]
 at [C : Category@{u0 u0 u0}] concluding [Complete@{u0 u0 u0 u}];
 [Presheaf_Eval_PreservesAllLimits] at [C : Category@{u2 u2 u2}]
 concluding [PreservesAllLimits]), inherited from [Sets_Complete@{u u0}
 : Complete@{u u u u0}] (its INDEX bullet records the same); no
 equation.
 - No word-bounded [Set], no [JMeq]/[EqdepFacts]/[eq_rect_r] bound in any
 block.

 COUNTS AND CONVENTIONS.
 - 29 [.glob] declaration heads (24 [def], 5 [prf]) plus 11 [Program]
 obligations the [.glob] cannot see ([plim_probe_cone] 1,
 [plim_cone_at] 1, [PointwiseLimit] 3, [plim_nat] 2,
 [PointwiseLimitCone] 1, [plim_comp_cone] 1, [plim_ump_nat] 2), all
 “Closed under the global context”, zero [Axioms:] lines; the gate
 carries the 29 heads, fully qualified.  One [Defined]
 ([PointwiseIsLimitCone]), LOAD-BEARING: flipped to [Qed] the file
 compiles but the probe's mediator readback [p425_mediator] is
 refused.  Sixteen [Qed] tokens (five lemmas, eleven obligations).
 - Closure 37 files excluding self: Instance/Sets/Complete.v costs 12
 at the margin (the presheaf corollaries), Instance/Fun/Eval.v 2, the
 other eleven [Require]s 0 (an earlier revision also required
 Category.Theory.Isomorphism, unused; dropped).  No collision: each new
 name has 0 declaration hits elsewhere in the tree.
 Adjunction/Diagonal/Limit.v would add 25 files and is deliberately
 NOT required; Instance/Fun/Terminal.v would add 28 and is not
 compared against here (marginals over the shipped [Require] list; an
 earlier revision said 37 and 39, measured without
 Instance/Sets/Complete.v).
 - Test/ProbeFunLimit425.v carries 4 refutation commands (1 instrument +
 N1 CONVERSION + N2 UNIVERSE + N3 UNIVERSE), each stripped one at a
 time in a copy of the whole file; seven readbacks at [eq_refl]; the
 [HasLimitsOfShape] ascription and [LimitFunctor] on [P, X] as
 positive controls; guard coverage 19 identifier tokens inside the
 refutations / 16 also named outside, comments stripped, with three
 exhaustive exceptions (the keyword, the refuted declaration's name,
 the absent name); rename-simulated 6/6 ([FCone],
 [PointwiseLimitCone], [limit_cone], [Limit], [Eval],
 [Functor_Category_pointwise_limit], module paths excluded) with every
 first break on a positive line.  [make todo] grows by those 4 lines
 only (2222 → 2226), so the issue's “adds no new hits” box is not met
 as written; disclosed.
 - [Eval p] is parenthesised or applied inside a larger term throughout:
 bare at a definition-body head it parses as the [Eval … in]
 vernacular (Instance/Fun/Eval.v's header).

 NOT DELIVERED.
 - The colimit dual ([Cocomplete X → Cocomplete [P, X]], evaluation
 preserving colimits): #715's, superseding the issue's Work item 2
 clause; not one colimit line is written.
 - Creation of limits by evaluation or along the discrete inclusion
 (Theorem 2): Instance/Fun/Creation.v's (#426).
 - A [HasLimitsOfShape]-typed statement inside this file (the unfolded
 form is delivered; the class is imported only by the probe).
 - Any comparison of [Functor_Category_pointwise_limit] with
 Instance/Fun/Terminal.v's [Fun_iprod] or Instance/Fun/Cartesian.v's
 products at their shapes.
 - No edit to Instance/Fun/Eval.v, Structure/Limit.v, Structure/Limit/
 Preservation.v or Instance/Sets/Complete.v; the five prose edits are
 line-neutral and named above. 

 --------
 Mac Lane §V.3 定理 1 及推论 1（书第 115-116 页；maclane:V.3:thm1, maclane:V.3:cor1）；Awodey §8.5 命题 8.7 及其推论（仿射范畴是完备的，评估保持极限）；Riehl §3.4 命题 3.4.9（函子范畴中的极限是逐点的，且评估保持这些极限）。
 nLab:  https://ncatlab.org/nlab/show/functor+category 
 https://ncatlab.org/nlab/show/limit背景。一个函子图 D : J ⟶  [P, X] 在 P 的每一个对象 p 处都有一个求值图 Eval p ◯ D : J ⟶ X。当这些图在 X 中都有极限时，极限顶点可以组合成一个函子 P ⟶ X，其箭头部分是相邻逐点极限之间的中介态射——该性质下唯一，并且逐点的边可以组合成 [P, X] 中 D 的一个极限锥：函子范畴中的极限是逐点计算的。因此，映入一个完备范畴的函子范畴是完备的，尤其是每个预层范畴 [C^op, Sets]，并且在任意对象上的求值保留所有极限。余极限是对偶陈述，适用于对偶范畴；它们是 #715 的内容，此处不再赘述。沿着离散包含的极限创建（定理 2）是 Instance/Fun/Creation.v 中的 (#426) 结果。

 陈旧的前提，重新测量。- “[C, D]上没有[Terminal]结构”：实例/Fun/Terminal.v
 [Functor_Category_Terminal]（[#[export]实例]，#339）和
 [Fun_HasIndexedProducts]存在;实例/趣味/笛卡尔.v
 [Functor_Category_Cartesian] 和实例/趣味/Pullback.v
 [Fun_HasPullbacks]也一样。缺少的是整体形状和任何
 评估函子的保存语句（实例/Fun/
 Terminal.v 命名了那个空隙;这里已在原地更正）。- “no [Complete] 住在任何地方”：对非 Test/ 树的常量进行声明扫描，得出 [@Complete] 至少有十三个无条件的证人和前提携带变换器一起 — Instance/Sets/Complete.v 的 [Sets_Complete] 和 [ConeSet_Complete]，Instance/Grp/Limit.v 的 [Grp_Complete]，Construction/Arrow/Limit.v 的 [Arrow_Complete]，Construction/Comma/Limit.v 的 [Comma_Complete]，Construction/Product/Limit.v 的 [PiCat_Complete]、[EM_Complete]、[reflective_Complete] 等；#254 已关闭，因此工作项 3 的阻塞器被解除，[Presheaf_Complete] 已在下面构建。- “评估函子不存在”：Adjunction/Diagonal/Connected.v [EvalAt]，以及 #424 的 Instance/Fun/Eval.v [Eval]，本文件使用——对 #424 的依赖是真实的：通过 [EvalAt] 路由将给本文件的闭包增加 103 个文件，而 Eval.v 仅增加 2 个文件（针对已发布的 [Require] 列表的边际；早期修订说过是 115，测量对象是没有 Instance/Sets/Complete.v 的列表）。- 散文位置 (工作项 4)，全部以行中性方式编辑：Instance/Fun.v 中有一个（问题的范围超出了它，延伸到相邻的子句，即关于笛卡尔闭包的内容，而 Instance/Fun/Closed.v 驳斥了这一内容且未被触及），Instance/Fun/Cartesian.v 中有两个（第一个的问题范围同样超出；第二个现在引用了 [Functor_Category_Terminal]），Structure/Complete.v 中有一个（问题范围提前了一行；单子子句自身的词未被触碰——它是 [EM_Complete] 的，尽管其中一个获得了“来自集合”），第四个位置是问题遗漏的 Structure/Cartesian/Product.v，还有两个在 Instance/Fun/Terminal.v（该文件的未交付列表否认了通用定理及任何保持声明，两者均已现场修正；以及其中“陈述于现在这三个地方的散文框架指向这里。Instance/Fun.v 的句子保留了它的余极半部分，归功于 nLab 和 #715。- Construction/Product/Limit.v 的 [PiCat_Complete] 与 [Functor_Category_Complete] 在项上逐项具有相同的形状，投影位置为 [Eval p]；这是一种类比，而不是实例 — [PiCat] 是范畴的依赖积，而不是 [[DiscreteCat I, X]，因此它们互不衍生。它的头部记录了相同的宇宙陷阱。交付内容是什么（29 个命名常量加上 11 个 [Program] 义务，每一个都在全局上下文下封闭）。(1) 点数据。在 [D : J ⟶ [P, X] 上] 和 [L : ∀ p, Limit (Eval p ◯ D)] 中：[plim_obj], [plim_alimit], [plim_leg], [plim_leg_coherence]，以及腿的联合单射性（[plim_probe_cone], [plim_jointly_monic]）。(2) 箭头部分。[plim_cone_at f]（作为锥在 q 图上的 p 处极限，腿为 [fmap[D j] f ∘ plim_leg p j]; 一致性是 [fmap[D] g 的自然性，然后是锥的一致性），[plim_map], [plim_map_commutes]，以及 Mac Lane 的唯一性 [plim_map_unique]。(3) 极限函子。[PointwiseLimit : P ⟶ X]：三个函子定律各为一条 [plim_jointly_monic]。(4) 极限锥。[plim_nat j : PointwiseLimit ⟹ D j], [PointwiseLimitCone : Cone D]。(5) 定理 1。[plim_comp_cone]（在 p 处评估的 [P, X] 中的一个锥），[plim_ump_map], [plim_ump_commutes], [plim_ump_nat]（通过联合单性自然得出），[PointwiseIsLimitCone : IsLimitCone PointwiseLimitCone] —— 在 [P, X] 中的唯一性即逐点唯一性，一个化简为分量的变换方程 —— 以及该问题固定的 [Functor_Category_pointwise_limit : Limit D]。[eq_refl]（探针）处的回读：p 处的图、对象的作用、腿的组成部分、像锥的顶点和腿、中介者的组成部分、打包极限的锥。(6) 保留（Riehl 3.4.9 (ii)，Awodey 8.7 的第二条款）。[Eval_pointwise_IsLimitCone p]  — 在 [Eval p] 下的逐点锥的图像是极限定的，没有任何强制，其顶点和腿正是所选极限锥的本身 — 并且 [Eval_PreservesLimitCone p : PreservesLimitCone D (Eval p)] 对于任意极限锥，通过 [limitcone_transport] 沿 [FCone_iso] 的 [limitcone_iso] （仅该构造给出规范锥）；[Eval_PreservesLimit] 下降到仅顶点类。(7) 推论 1. [Fun_HasLimitsOfShape] 在展开形式 [(∀ F : J ⟶ X, Limit F) → ∀ D : J ⟶ [P, X] ，极限 D] — 它在 Adjunction/Diagonal/Limit.v 的 [HasLimitsOfShape] 下游（探针）赋值，而此文件并没有引入该内容 — 且此问题已固定 [Functor_Category_Complete : Complete X → Complete [P, X] ]; [Eval_ContinuousFunctor] ， [Eval_PreservesAllLimits]。所有四个都是
 在定义上进行了注释：以裸写的方式，每个都将 P 的对象宇宙最小化到其同构宇宙（探针 N2 在注释形式的接受旁固定了裸形式的拒绝 [Constraint jo < jh]；分节级别的 [Universe] 声明不会消除它，已测量）。(8) 预层（Awodey 的推论，工作项 3）[Presheaf_Complete C : 完整的 [C^op, Sets]] 和 [Presheaf_Eval_PreservesAllLimits C c] 来自 Instance/Sets/Complete.v 的 [Sets_Complete]；协变双胞 [Fun_Sets_Complete]。宇宙（通过 [About] 在 [Set Printing Universes] 下对所有 29 个常数进行测量）。- 第 [Pointwise] 节的 22 个常数正好包含四个方程，[u0 = u2]、[u0 = u4]、[u0 = u6]、[u2 = u4] 在 [J : Category@{u u0 u0}] 上，[P : Category@{u1 u2 u2}]、[X : Category@{u3 u4 u4}] : J 的 hom = P 的 hom = X 的 hom = [P, X] 的 hom，在同一层次。P-hom = X-hom 是 Instance/Fun.v 的 [Fun]；shape-hom = ambient-hom 是 Structure/Limit.v 的 [Limit] 绑定器 [{J : Category@{u0 u1 u1}} {C : Category@{u2 u1 u1}}]，应用两次（一次在 [P, X]，一次在 X）——探针 N3 钉住它：在其 hom 严格低于 X 的形状上，该图及其 [Cone] 被接受，而其 [Limit] 被拒绝。OBJECT 宇宙保持自由（每个块中 J、P 和 X 都是三个不同的层次）。- 四个带注释的推论各自包含恰好一个方程，[jh = ch]（[Fun]的），其中[P : Category@{jo jh jh}]在[jo]中是自由的——例如 [Functor_Category_Complete@{jo jh co ch u u0 u1 u2 u3 u4 u5} : ∀ {P : Category@{jo jh jh}} {X : Category@{co ch ch}}, Complete@{u u2 ch co} X → Complete@{u u2 jh u3} [P, X] ] 其中 [jo <= jh]、[jo <= u3]、[jh < u4]、[co <= u3]。- 三个预层常数位于一个具有一个层级的范畴中，适用于对象、同态和证明（[Presheaf_Complete] 和 [Fun_Sets_Complete] 在 [C : Category@{u0 u0 u0}] 中结论为 [Complete@{u0 u0 u0 u}]；[Presheaf_Eval_PreservesAllLimits] 在 [C : Category@{u2 u2 u2}] 中结论为 [PreservesAllLimits]），继承自 [Sets_Complete@{u u0} : Complete@{u u u u0}]（其 INDEX 项记录了相同内容）；无方程。- 在任何块中都没有单词边界的 [Set]，也没有 [JMeq] / [EqdepFacts] / [eq_rect_r] 边界。计数和惯例。- 29 个 [.glob] 声明头（24 个 [def]，5 个 [prf]）加上 11 个 [Program] 义务 [.glob] 不能看到（[plim_probe_cone] 1，[plim_cone_at] 1，[PointwiseLimit] 3，[plim_nat] 2，[PointwiseLimitCone] 1，[plim_comp_cone] 1，[plim_ump_nat] 2），全部“在全局上下文下关闭”，零 [Axioms:] 行；该网关携带 29 个头，完全合格。一个 [Defined]（[PointwiseIsLimitCone]），承载：翻转为 [Qed] 文件可编译，但探针的中介器回读 [p425_mediator] 被拒绝。十六个 [Qed] 令牌（五个词条，十一项义务）。- 关闭37个文件（不包括自身）：Instance/Sets/Complete.v 成本为12（在边际上（预层副推论），Instance/Fun/Eval.v 2，其他十一 个 [Require] 为0（早期版本也需要 Category.Theory.Isomorphism，但未使用；已删除）。没有冲突：每个新名字在树的其他地方声明命中为0。Adjunction/Diagonal/Limit.v 会增加25个文件，并且故意不要求；Instance/Fun/Terminal.v 会增加28个文件，并且这里未进行比较（在已发布 [Require] 列表上的边际；早期版本显示为37和39，测量时未包括 Instance/Sets/Complete.v）。- Test/ProbeFunLimit425.v 包含 4 个否定命令（1 个工具 + N1 CONVERSION + N2 UNIVERSE + N3 UNIVERSE），在整个文件的副本中每次剥离一个；在 [eq_refl] 处进行了七次读取回传；[HasLimitsOfShape] 的归属和 [LimitFunctor] 在 [P, X] 上作为阳性对照；防护覆盖在否定内部有 19 个标识符标记 / 外部同样命名 16 个，注释已剥离，三处全面例外（关键字、被否定的声明名称、缺失名称）；重命名模拟 6/6（[FCone]、[PointwiseLimitCone]、[limit_cone]、[Limit]、[Eval]、[Functor_Category_pointwise_limit]，模块路径不包括在内），每个首次中断都在阳性行上。[make todo] 仅通过那 4 行增长（2222 → 2226），因此按原文描述，该问题的“没有新增命中”框未满足；已披露。 - [Eval p] 在整个过程中都被加上了括号或者应用在更大的项中：在定义体的开头单独出现时，它被解析为 [Eval … in] 的本地语（Instance/Fun/Eval.v 的头部）。未交付。
 - 余极限对偶（[Cocomplete X → Cocomplete [P, X]，保持余极限的评估）：＃715，取代该问题的工作项2条款；没有写下任何一条余极限线。
 - 通过评估或沿离散包含创建极限（定理2）：Instance/Fun/Creation.v 的（＃426）。
 - 本文件中的一个 [HasLimitsOfShape] 类型声明（展开形式已交付；该类仅由探针导入）。
 - 对 [Functor_Category_pointwise_limit] 与 Instance/Fun/Terminal.v 的 [Fun_iprod] 或 Instance/Fun/Cartesian.v 在其形状上的乘积的任何比较。
 - 未编辑 Instance/Fun/Eval.v、Structure/Limit.v、Structure/Limit/Preservation.v 或 Instance/Sets/Complete.v；上述五个文本编辑与行无关并已命名。
*)

Section Pointwise.

Context {J P X : Category}.
Context (D : J ⟶ [P, X]).

(*
 The hypothesis of Mac Lane's Theorem 1: each evaluation of the diagram
 has a limit in X. 

 --------
 Mac Lane 定理 1 的假设：图表的每一次求值在 X 中都有一个极限。
*)
Context (L : ∀ p : P, Limit (Eval p ◯ D)).

(** ** The pointwise data / ** 点数据 *)

Definition plim_obj (p : P) : X := vertex_obj[@limit_cone _ _ _ (L p)].

Definition plim_alimit (p : P) : IsALimit (Eval p ◯ D) (plim_obj p) :=
  limit_is_alimit (L p).

Definition plim_leg (p : P) (j : J) : plim_obj p ~{X}~> fobj[D j] p :=
  limit_leg (plim_alimit p) j.

Lemma plim_leg_coherence (p : P) {i j : J} (g : i ~{J}~> j) :
  transform[fmap[D] g] p ∘ plim_leg p i ≈ plim_leg p j.
Proof. exact (limit_leg_coherence (plim_alimit p) g). Qed.

(* Two arrows into a pointwise limit that agree on every leg are equal: the legs are jointly monic. / 两个箭头指向一个逐点极限，如果在每一条支线上都一致，则它们相等：这些支线是联合单性的。 *)
Program Definition plim_probe_cone {q : P} {c : X} (u : c ~{X}~> plim_obj q) :
  Cone (Eval q ◯ D) := {|
  vertex_obj := c;
  coneFrom := {| vertex_map := fun j => plim_leg q j ∘ u |}
|}.
Next Obligation.
  rewrite comp_assoc.
  now rewrite plim_leg_coherence.
Qed.

Lemma plim_jointly_monic {q : P} {c : X} (u v : c ~{X}~> plim_obj q) :
  (∀ j : J, plim_leg q j ∘ u ≈ plim_leg q j ∘ v) → u ≈ v.
Proof.
  intro H.
  apply (limit_med_eq (plim_alimit q) (plim_probe_cone u) u v);
    intro x; [reflexivity | symmetry; apply H].
Qed.

(* * ** The arrow part: the mediator between adjacent pointwise limits / * ** 箭头部分：相邻逐点极限之间的中介 *)

(*
 An arrow f : p ~> q of P turns the limit at p into a cone over the
 diagram evaluated at q, with legs fmap[D j] f after the legs at p;
 coherence is the naturality of fmap[D] g followed by cone coherence. 

 --------
 P 的一个箭头 f : p ~> q 将 p 处的极限变成在 q 处评估的图形上的一个圆锥，其边为在 p 处的边之后的 fmap [D j] f；相干性是 fmap [D] g 的自然性，随后是圆锥相干性。
*)
Program Definition plim_cone_at {p q : P} (f : p ~{P}~> q) :
  Cone (Eval q ◯ D) := {|
  vertex_obj := plim_obj p;
  coneFrom := {| vertex_map := fun j => fmap[D j] f ∘ plim_leg p j |}
|}.
Next Obligation.
  rewrite comp_assoc.
  rewrite <- (naturality[fmap[D] f0] p q f).
  rewrite <- comp_assoc.
  now rewrite plim_leg_coherence.
Qed.

Definition plim_map {p q : P} (f : p ~{P}~> q) : plim_obj p ~{X}~> plim_obj q :=
  limit_med (plim_alimit q) (plim_cone_at f).

Lemma plim_map_commutes {p q : P} (f : p ~{P}~> q) (j : J) :
  plim_leg q j ∘ plim_map f ≈ fmap[D j] f ∘ plim_leg p j.
Proof. exact (limit_med_commutes (plim_alimit q) (plim_cone_at f) j). Qed.

(* Mac Lane's “unique”: the arrow part is determined by its legs. / Mac Lane 的“唯一性”：箭头部分由它的腿决定。 *)
Lemma plim_map_unique {p q : P} (f : p ~{P}~> q)
  (u : plim_obj p ~{X}~> plim_obj q) :
  (∀ j : J, plim_leg q j ∘ u ≈ fmap[D j] f ∘ plim_leg p j) → plim_map f ≈ u.
Proof. exact (limit_med_unique (plim_alimit q) (plim_cone_at f) u). Qed.

(** ** The pointwise limit functor / ** 点态极限函子 *)

Program Definition PointwiseLimit : P ⟶ X := {|
  fobj := plim_obj;
  fmap := fun _ _ f => plim_map f
|}.
Next Obligation.
  proper.
  apply plim_jointly_monic; intro j.
  rewrite !plim_map_commutes.
  now rewrite X0.
Qed.
Next Obligation.
  apply plim_jointly_monic; intro j.
  rewrite plim_map_commutes, id_right, fmap_id, id_left.
  reflexivity.
Qed.
Next Obligation.
  apply plim_jointly_monic; intro j.
  rewrite plim_map_commutes, comp_assoc, plim_map_commutes.
  rewrite <- comp_assoc, plim_map_commutes, comp_assoc.
  now rewrite fmap_comp.
Qed.

(** ** The limiting cone in [P, X] / ** [P, X] 中的限制锥 *)

Program Definition plim_nat (j : J) : PointwiseLimit ~{[P, X]}~> D j := {|
  transform := fun p => plim_leg p j
|}.
Next Obligation. symmetry; apply plim_map_commutes. Qed.
Next Obligation. apply plim_map_commutes. Qed.

Program Definition PointwiseLimitCone : Cone D := {|
  vertex_obj := PointwiseLimit;
  coneFrom := {| vertex_map := plim_nat |}
|}.
Next Obligation. apply plim_leg_coherence. Qed.

(* * ** Theorem 1: the pointwise cone is limiting / * ** 定理1：逐点锥是极限的 *)

Section Universal.

Context (M : Cone D).

(*
 A cone over D in [P, X], evaluated at p, is a cone over the evaluated
 diagram. 

 --------
 在 [P, X] 中 D 上的一个锥体，在 p 处的值，是对该评估图的一个锥体。
*)
Program Definition plim_comp_cone (p : P) : Cone (Eval p ◯ D) := {|
  vertex_obj := fobj[vertex_obj[M]] p;
  coneFrom := {| vertex_map := fun j => transform[cone_leg M j] p |}
|}.
Next Obligation.
  pose proof (@cone_coherence _ _ _ _ (@coneFrom _ _ _ M) x y f) as Hc.
  simpl in Hc. apply Hc.
Qed.

Definition plim_ump_map (p : P) :
  fobj[vertex_obj[M]] p ~{X}~> plim_obj p :=
  limit_med (plim_alimit p) (plim_comp_cone p).

Lemma plim_ump_commutes (p : P) (j : J) :
  plim_leg p j ∘ plim_ump_map p ≈ transform[cone_leg M j] p.
Proof. exact (limit_med_commutes (plim_alimit p) (plim_comp_cone p) j). Qed.

(* The pointwise mediators are natural in p, by joint monicity. / 通过联合单射性，点态介子在 p 中是自然的。 *)
Program Definition plim_ump_nat :
  vertex_obj[M] ~{[P, X]}~> PointwiseLimit := {|
  transform := plim_ump_map
|}.
Next Obligation.
  apply plim_jointly_monic; intro j.
  rewrite comp_assoc, plim_map_commutes.
  rewrite <- comp_assoc, plim_ump_commutes.
  rewrite comp_assoc, plim_ump_commutes.
  apply (naturality[cone_leg M j]).
Qed.
Next Obligation.
  symmetry.
  apply plim_jointly_monic; intro j.
  rewrite comp_assoc, plim_map_commutes.
  rewrite <- comp_assoc, plim_ump_commutes.
  rewrite comp_assoc, plim_ump_commutes.
  apply (naturality[cone_leg M j]).
Qed.

End Universal.

(*
 Uniqueness in [P, X] is pointwise uniqueness: an equation of
 transformations reduces componentwise. 

 --------
 [P, X] 中的唯一性是逐点唯一性：一个变换的方程可以分组件化简。
*)
Definition PointwiseIsLimitCone : IsLimitCone PointwiseLimitCone.
Proof.
  intro M.
  unshelve refine {| unique_obj := plim_ump_nat M |}.
  - intros j p; simpl.
    apply plim_ump_commutes.
  - intros v Hv p.
    apply (limit_med_unique (plim_alimit p) (plim_comp_cone M p)).
    intro j.
    exact (Hv j p).
Defined.

(* The issue's pinned name: the limit of D in [P, X]. / 问题的固定名称：[P, X] 中 D 的限制。 *)
Definition Functor_Category_pointwise_limit : Limit D :=
  limitcone_limit PointwiseLimitCone PointwiseIsLimitCone.

(* * ** Evaluation preserves the limit / * ** 评估保留极限 *)

(* The image of the pointwise cone under Eval p IS the chosen limit cone at p in apex and legs (readbacks in the probe), so it is limiting with no coercion. / 在 Eval p 下的逐点锥的图像是顶点为 p 且沿腿（探针中的回读）的选定极限锥，因此它是极限的且无需强制转换。 *)
Definition Eval_pointwise_IsLimitCone (p : P) :
  IsLimitCone (FCone (Eval p) PointwiseLimitCone) :=
  limit_limitcone (L p).

(* Any limiting cone over D, not only the canonical one, is sent to a limiting cone: transport along the essential uniqueness of limits. / 任何关于D的限制锥，不仅是规范锥，都会被发送到一个限制锥：沿着极限的本质唯一性进行传递。 *)
Definition Eval_PreservesLimitCone (p : P) : PreservesLimitCone D (Eval p) :=
  fun N HN =>
    limitcone_transport
      (ConeIso_sym (FCone_iso (Eval p) (limitcone_iso HN PointwiseIsLimitCone)))
      (Eval_pointwise_IsLimitCone p).

Definition Eval_PreservesLimit (p : P) : PreservesLimit D (Eval p) :=
  PreservesLimitCone_PreservesLimit (Eval_PreservesLimitCone p).

End Pointwise.

(* * ** Corollary 1: [P, X] has the limits X has, and is complete when X is / * ** 推论 1：[P, X] 拥有 X 的极限，并且当 X 完整时也完整 *)

(*
 Both corollaries are annotated at the DEFINITION: written bare, they
 minimize P's object universe down onto its hom universe (measured; the
 probe pins the unannotated form's refusal at a strictly smaller object
 level and the annotated form's acceptance).  The [+] takes in the two
 levels [Functor_Category_pointwise_limit] leaks. 

 --------
 两个推论都在定义处进行了注释：以裸写形式，它们将 P 的对象宇宙最小化到其同类宇宙（经过测量；探针将未注释形式的拒绝固定在严格较小的对象层次上，而注释形式的接受也是如此）。[+] 接收这两个层次，[Functor_Category_pointwise_limit] 泄漏。
*)
Definition Fun_HasLimitsOfShape@{jo jh co ch io u u0 u1 u2 u3 +}
  {J : Category@{io ch ch}} {P : Category@{jo jh jh}} {X : Category@{co ch ch}}
  (LX : ∀ F : J ⟶ X, Limit@{u io ch co} F) :
  ∀ D : J ⟶ [P, X], Limit@{u io ch u3} D :=
  fun D => Functor_Category_pointwise_limit D (fun p => LX (Eval p ◯ D)).

(* The issue's pinned name. / 该问题的固定名称。 *)
Definition Functor_Category_Complete@{jo jh co ch u u0 u1 u2 u3 +}
  {P : Category@{jo jh jh}} {X : Category@{co ch ch}}
  (HX : @Complete@{u u2 ch co} X) : @Complete@{u u2 jh u3} ([P, X]) :=
  fun J D => Functor_Category_pointwise_limit D (fun p => HX J (Eval p ◯ D)).

(* * ** Evaluation is continuous when X is complete / * ** 当 X 完成时，评估是持续进行的 *)

(*
 Annotated at the definition for the same reason as the corollaries:
 written bare, both minimize P to one universe [Category@{u u u}]
 (measured). 

 --------
 因为与推论相同的原因，对定义进行了注释：
 单独书写时，两者都将 P 最小化到一个宇宙 [Category@{u u u}] 
 （已测量）。
*)
Definition Eval_ContinuousFunctor@{jo jh co ch u u0 u1 u2 u3 +}
  {P : Category@{jo jh jh}} {X : Category@{co ch ch}}
  (HX : @Complete@{u u2 ch co} X) (p : P) : ContinuousFunctor (Eval p) :=
  fun J D => Eval_PreservesLimitCone D (fun q => HX J (Eval q ◯ D)) p.

Definition Eval_PreservesAllLimits@{jo jh co ch u u0 u1 u2 u3 +}
  {P : Category@{jo jh jh}} {X : Category@{co ch ch}}
  (HX : @Complete@{u u2 ch co} X) (p : P) : PreservesAllLimits (Eval p) :=
  Continuous_PreservesAllLimits (Eval_ContinuousFunctor HX p).

(* * ** Presheaves: the concrete corollary / * ** 预层：具体的推论 *)

(*
 Awodey §8.5's Corollary: every presheaf category is complete, from
 Instance/Sets/Complete.v's [Sets_Complete]; and evaluation at any object
 preserves all limits (Proposition 8.7's second clause).  The covariant
 twin [Fun_Sets_Complete] is recorded too. 

 --------
 Awodey §8.5 的推论：每个预层范畴都是完备的，来源于 Instance/Sets/Complete.v 的 [Sets_Complete]；并且在任意对象处的取值保持所有极限（命题 8.7 的第二条款）。协变的对应 [Fun_Sets_Complete] 也被记录。
*)
Definition Presheaf_Complete (C : Category) : @Complete ([C^op, Sets]) :=
  Functor_Category_Complete Sets_Complete.

Definition Presheaf_Eval_PreservesAllLimits (C : Category) (c : C) :
  PreservesAllLimits (@Eval (C^op) Sets c) :=
  @Eval_PreservesAllLimits (C^op) Sets Sets_Complete c.

Definition Fun_Sets_Complete (C : Category) : @Complete ([C, Sets]) :=
  Functor_Category_Complete Sets_Complete.
