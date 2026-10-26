Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.

Generalizable All Variables.

(* * * Limits of rings are computed on underlying sets / * * 环的极限是在基础集合上计算的 *)

(*
 nLab: https://ncatlab.org/nlab/show/created+limit
 nLab: https://ncatlab.org/nlab/show/limit#limits_in_categories_of_algebras
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_rings
 Mac Lane: Categories for the Working Mathematician, 2nd ed. (GTM 5),
 §V.1 Theorems 2 and 3, book pp. 111-112 (PDF pp. 120-121)
 Riehl:    Category Theory in Context, §5.6 Example 5.6.8

 [Rng_Forget] (Instance/Rng.v) STRICTLY CREATES every limit.  Given a
 limiting cone over the underlying diagram of sets, there is exactly one
 ring structure on its apex making every projection a homomorphism
 ([rlim_structure_unique], Mac Lane's Theorem 2), the resulting cone lies
 over the given one ON THE NOSE ([rlim_over_obj] and [rlim_over_legs] are
 both [eq_refl], because [Rng_Forget]'s object map is the [rig_setoid]
 projection -- Instance/Rng.v already records that as an [eq_refl]),
 it is limiting ([rlim_created]), and a cone of rings whose image is
 limiting is itself limiting ([rng_reflects]).  Packaged as
 Structure/Limit/Creation.v's own classes --
 [Rng_Forget_StrictlyCreatesLimit]
 ([StrictlyCreatesLimit]), [Rng_Forget_CreatesLimit] and
 [Rng_Forget_creates_limits] ([CreatesAllLimits]) -- from which the
 standard corollaries follow by application: [Rng_Complete] (Mac Lane's
 Theorem 3) and [Rng_Forget_continuous : ContinuousFunctor Rng_Forget],
 the cone-level reading, with the apex-only
 [Rng_Forget_PreservesAllLimits] derived from it and
 [Rng_Forget_reflects_limits] alongside.

 WHAT HAS TO BE LIFTED, AND HOW MUCH MORE IT IS THAN THE GROUP CASE.  An
 object of [Rng] is Theory/Algebra/Rig.v's [RingObject]: a
 [RigObject] extended by [ring_neg] with [ring_neg_respects] and
 [ring_neg_l].  So FIVE operations are lifted -- [rig_zero], [rig_one],
 [rig_add], [rig_mul], [ring_neg] -- against the group case's three, and
 ELEVEN laws are proved: the four counted off Definition 5.36's clauses
 (a) [rig_add_assoc], [rig_add_comm], [rig_add_zero_l]; (b)
 [rig_mul_assoc], [rig_mul_one_l], [rig_mul_one_r]; (c) [rig_distr_l],
 [rig_distr_r]; (d) [rig_mul_zero_l], [rig_mul_zero_r] -- ten in all --
 plus [ring_neg_l].  Every one is three lines: apply the joint-monicity
 lemma, rewrite the defining triangles, apply the law in [K j].  THE
 METHOD IS UNCHANGED; only the bookkeeping grows.

 ONE PLACE WHERE THE RING SIGNATURE IS GENUINELY DIFFERENT, NOT MERELY
 BIGGER.  [RigHom] (Theory/Algebra/Rig.v) has FOUR clauses --
 [rig_map_zero], [rig_map_add], [rig_map_one], [rig_map_mul] -- and NO
 clause for negation, because Rig.v's [RigHom_neg] proves preservation
 of negation from uniqueness of additive inverses.  Two consequences, both
 visible below.  The coherence of the negation cone ([rlim_neg_coherence])
 is therefore discharged by that THEOREM where its four siblings use a
 projection; and the negation clause of [rlim_structure_unique] is stated
 by hand rather than being read off the hom type, since no leg condition
 on negation is available from [RigHom] at all.  The uniqueness clause
 nevertheless holds at the same strength as its four siblings: it consumes
 only that the legs carry the candidate negation to [ring_neg] in each
 [K j], and no law of the candidate structure.

 THE HEADLINE SENTENCE IS MACHINE-CHECKED AT [eq_refl], NOT ARGUED.  At
 the limits [Sets_Complete] chooses -- the compatible families of
 Instance/Sets/Complete.v ([Sets_limit_obj], [Sets_limit_leg] and
 [Sets_Complete]) -- the created ring is the COORDINATEWISE
 one on the nose: [rng_complete_carrier], [rng_complete_zero],
 [rng_complete_one], [rng_complete_add], [rng_complete_mul],
 [rng_complete_neg] and [rng_complete_leg] are SEVEN [eq_refl] Examples,
 at an ARBITRARY shape and an ARBITRARY diagram of rings.  Nothing in them
 is specific to a witness category, and no isomorphism is interposed; this
 file therefore needs no concrete witness to be non-vacuous, and builds
 none.

 ON THE HOUSE RULE THAT MORPHISMS ARE COMPARED WITH [≈]: four statements
 here write [=] between morphisms -- [rlim_over_legs], [rng_lift_legs],
 [rng_fcone_leg] and [rng_complete_leg] -- and each does so because both
 sides are the SAME TERM, the witness being [eq_refl].  They record
 Mac Lane's [F sigma = tau] at full strength, which is strictly stronger
 than the [≈] the [StrictLift] clause (Structure/Limit/Creation.v)
 asks for; every law, every proof and the [slift_legs] clause consumed by
 [rng_strict_lift] use [≈].  The same applies to the object-level [=] of
 [rlim_over_obj], [rng_lift_apex], [rng_fcone_apex],
 [rng_complete_carrier] and the five [rng_complete_*] element equations,
 which compare OBJECTS and ELEMENTS rather than morphisms and are the
 discipline's sanctioned exception.

 WHAT IS NEW HERE AND WHAT IS NOT, MEASURED RATHER THAN ASSERTED.  This
 is the SECOND algebraic category to get a creation result and the second
 to get [@Complete], not the first: Instance/Grp/Limit.v is the precedent
 ([Grp_Forget_creates_limits], [Grp_Complete]) and this
 file is its clause-for-clause transposition.  Sweeping declaration heads
 of the form “Definition/Program Definition/Theorem/Lemma/Example <name> :
 @?Complete|Cocomplete” over all [.v] files, the roster before this file
 was [Sets_Complete] and [ConeSet_Complete] (Instance/Sets/Complete.v),
 [Sets_Complete_via_Manes] (Structure/Equalizer/Coreflexive.v),
 [Subsets_Complete]/[Subsets_Cocomplete] (Instance/Powerset.v),
 [Grp_Complete] (Instance/Grp/Limit.v), one biconditional at [Proset]
 (Instance/Proset/Limit.v) and two probe files -- nothing for [Rng],
 [Ab], [CMon], [RMod], [Mon] or [Top].

 AND THE CLAIM “NO LIMIT OF RINGS EXISTED IN TREE” WOULD BE FALSE, SO IT
 IS NOT MADE.  Instance/Rng/Zp.v already builds THREE: [Zp_limit :
 IsALimit (ResTower Rcomm d) Zp], [Zp_int_limit] and
 [PowerSeries_limit], each at an [Omega^op]-shaped tower with a
 hand-built carrier.  It also already has the ELEMENTWISE uniqueness at
 that one diagram -- [zp_zero_forced], [zp_one_forced],
 [zp_add_forced], [zp_mul_forced], [zp_neg_forced] --
 and its header states in terms what it does not prove: “Riehl
 §5.6 Example 5.6.8 observes that the underlying-set functor of [Rng] is
 MONADIC and therefore CREATES the limit cone ... Monadicity is NOT proved
 here and is not used”.  THIS FILE SUPPLIES THE CREATION, at an arbitrary
 shape and an arbitrary diagram, and it too does NOT go through
 monadicity: no file in the tree exhibits [Rng] as an Eilenberg-Moore
 category, so the argument is rerun one level down exactly as the group
 case reruns it.  Nothing here is stated about [Zp]; relating [Zp_limit]
 to the created limit at [ResTower] is left undone.

 THE CONTINUITY COROLLARY IS NOT NEW, AND AN EARLIER REVISION OF THIS
 HEADER OVERSTATED HOW NOT-NEW IT IS IN THE WRONG DIRECTION.  That
 revision said continuity of [Rng_Forget] was available “in PRINCIPLE”
 but not as an instantiation, because “transporting [ContinuousFunctor]
 along a natural isomorphism of functors is nowhere in tree”.  That is
 false, and the audit of this file refuted it by building the alternative
 in twelve lines out of constants that already existed:
 Functor/Hom/Continuous.v's [Section Transport] and its
 [ContinuousFunctor_transport] are exactly that construction.  So the
 honest statement is that continuity of [Rng_Forget] WAS reachable before
 this file, by [zpoly_representation] (Instance/Rng/Polynomial.v) and
 [zpoly_representable] — note the names; a previous revision cited
 a [zpoly_hom_iso] that does not exist anywhere in the tree — composed
 with Functor/Hom/Limit.v's [hom_ContinuousFunctor] and then
 transported.

 RAPL is not the route, and here too the earlier revision's PREMISE was
 wrong while its conclusion held.  It said “the only ring adjunction in
 tree is [free_rng_ab_adjunction]”; there are at least four
 ([free_rng_ab_adjunction], Instance/Rng/Free.v;
 [zmring_adjunction], Instance/Rng/MonoidRing.v;
 [grp_ring_adjunction], Instance/Rng/GroupRing.v;
 [poly_pointed_adjunction], Instance/Rng/Pointed.v).  What is true is
 the thing that matters: NONE of them has [Rng_Forget : Rng ⟶ Sets] as
 its right adjoint (measured, [grep -P '⊣\s*Rng_Forget(?![A-Za-z0-9_])']
 returns nothing), so Adjunction/Continuity.v's
 [right_adjoint_Continuous] does not reach it.

 WHAT IS NEW WITHOUT QUALIFICATION is therefore the CREATION result, and
 [Rng_Complete], which no route above gives at all.  Continuity is
 re-derived here as its corollary rather than claimed as a first.

 THE ENGINE IS ONE REUSABLE LEMMA WITH NOTHING RING-THEORETIC IN IT.
 [rng_sets_limit_ext] says the legs of a limiting cone in [Sets] are
 jointly monic ELEMENTWISE: two points of the apex agreeing at every leg
 are equal.  It is proved from the mediator's uniqueness alone, with the
 two constant maps out of the apex itself as probes -- so it needs no
 terminal object and pulls in no further module.  It is the same lemma
 Instance/Grp/Limit.v declares as [sets_limit_ext], RE-DECLARED here under
 a distinct name rather than imported, for two reasons: importing it would
 make this file depend on [Grp], which is an architectural inversion, and
 its natural home is beside its donors in Instance/Sets/Complete.v, which
 this change does not touch.  The duplication is real and is recorded as
 such; whoever upstreams the lemma should retire both copies.

 UNIVERSES, measured off BOTH binder and block over all 122 constants
 (104 [.glob] declaration heads plus the 18 [Program] obligations, which
 no source-level reading sees): ZERO word-bounded [Set] occurrences
 anywhere, and TWELVE carry a block equation at all.  (An earlier
 revision of this paragraph said ELEVEN and added “the 18 obligations
 carry no block equation”; both were wrong, and the cause is worth
 recording -- after [Require Import Category.Instance.Rng.Limit] the BARE
 obligation names are not bound, so [About rng_sets_const_obligation_1]
 answers “not found” and an unqualified sweep silently reports nothing.
 Re-measured with fully qualified names,
 [Category.Instance.Rng.Limit.<name>], over all 122 constants.)  Four are
 the generic [Sets] section -- [rng_sets_pre], [rng_sets_med_eq],
 [rng_sets_limit_ext] and [rng_sets_const] -- all four carrying
 [u0 = u3], which identifies the shape's hom-and-proof universe with
 [Sets]' carrier universe, and the first three additionally [u1 = u2],
 which identifies two of the ambient's; that [u0 = u3] is [IsALimit]'s
 doing and not this file's.  Seven are the [rng_complete_*] readbacks,
 which BIND their shape explicitly and so carry [u = u0], identifying the
 shape's object universe with its hom-and-proof universe -- that is
 [Complete]'s own [@{u u u u0}] shape written out, inherited from
 [Sets_Complete] and not narrowed here.  The twelfth is
 [rng_sets_const_obligation_1], carrying the same [u0 = u3] as the
 constant it belongs to; the other 17 obligations carry none.  The remaining constants carry none either, with
 [Rng_Complete@{u u0 u1} : Complete@{u u u u0}] ([u < u0], [u < u1]) and
 [Rng_Forget_creates_limits@{u u0 u1 u2 u3 u4}] among them, so the
 smallness discipline is exactly [Sets_Complete]'s.  This mirrors the
 group case's reading exactly, at the same count of equation-carrying
 generic constants.

 [Print Assumptions] reports “Closed under the global context” for all
 six headline constants -- [Rng_Complete], [Rng_Forget_continuous],
 [Rng_Forget_creates_limits], [Rng_Forget_PreservesAllLimits],
 [Rng_Forget_StrictlyCreatesLimits] and [Rng_Forget_reflects_limits].
 This is worth saying because Instance/Rng.v itself reaches ZArith and
 QArith for its concrete witnesses; none of that arrives here, the file
 consuming only the category, the forgetful functor and the rig algebra.

 NOT delivered.  (1) No creation result for [Rng_Forget_Ab]
 (Instance/Rng.v), and the reason is structural rather than a matter
 of effort: the cone-mediator method used below does not transpose to
 [Ab].  Multiplication would need a cone whose apex is a direct sum with
 leg [(a, b) ↦ leg a · leg b], and that map is BILINEAR, not additive, so
 it is not a morphism of [Ab] and there is no cone to take a mediator of;
 the multiplicative unit is worse, since the only canonical maps out of
 [Ab]'s zero object (Instance/Ab.v) send everything to zero and
 so cannot select [1].  The available repair is the free abelian group on
 one generator (Instance/Ab/Free.v's [FreeAb]) as the probe object,
 with the multiplication rebuilt one argument at a time as an
 element-indexed family of mediators [L ⟶ L] and respectfulness in the
 outer argument recovered from joint monicity.  That is a different
 argument, not this one instantiated, so it is left for its own change.
 (2) No colimits and no cocompleteness for [Rng].  (CORRECTION, #450:
 [Rng] is cocomplete since #450, by Instance/Rng/Colimit.v's
 [Rng_Cocomplete_via_GAFT], the adjoint functor theorem applied at the
 diagonal with this file's [Rng_Complete] as its completeness
 hypothesis; the coproduct of rings is [Rng_Cocartesian_via_GAFT] there.
 None of those colimits computes.)  (3) No
 signature-generic variant covering [CMon], [Ab], [Rng] and [RMod] at
 once, though the engine transfers unchanged.  (4) No comparison of the
 created limit with Instance/Rng/Zp.v's [Zp_limit], and no comparison of
 the created binary product with any product structure on [Rng].  (5) No
 monadicity statement and no comparison functor, so nothing here says
 [Rng] IS an Eilenberg-Moore category, and Riehl's Example 5.6.8 remains
 an observation rather than a theorem in tree.  (6) No refusal-probe file
 under Test/: the boundaries this file meets are the group case's
 boundaries and Test/ProbeGrpLimit411.v already pins them, but nothing
 here is guarded by a probe of its own, which is a gap and not a claim.
 (7) NOTHING is registered as an [Instance] -- the file declares none,
 following its template, since a chosen limit must not become globally
 resolvable.

 This file contributes ZERO hits to [make todo]. 

 --------
 nLab:  https://ncatlab.org/nlab/show/created+limit
 nLab:  https://ncatlab.org/nlab/show/limit#limits_in_categories_of_algebras
 Wikipedia:  https://en.wikipedia.org/wiki/Category_of_rings
 Mac Lane: 《从业数学家的范畴论》，第二版（GTM 5），§V.1 定理 2 和 3，书中第 111-112 页（PDF 第 120-121 页）
 Riehl: 《语境中的范畴论》，§5.6 例 5.6.8[Rng_Forget]（Instance/Rng.v）严格地创建每一个极限。给定一个在底层集合图上的限制锥，其顶点上恰好有一个环结构使得每个投影都是同态（[rlim_structure_unique]，Mac Lane 定理 2），由此产生的锥完全位于给定的锥之上（[rlim_over_obj] 和 [rlim_over_legs] 都是 [eq_refl]，因为 [Rng_Forget] 的对象映射是 [rig_setoid] 投影——Instance/Rng.v 已经将其记录为 [eq_refl]），它是极限（[rlim_created]），并且映像为极限的环锥自身也是极限（[rng_reflects]）。打包为
 Structure/Limit/Creation.v 自身的类 --
 [Rng_Forget_StrictlyCreatesLimit]
 （[StrictlyCreatesLimit]），[Rng_Forget_CreatesLimit] 和
 [Rng_Forget_creates_limits] （[CreatesAllLimits]）-- 从中通过应用得出标准推论：[Rng_Complete]（Mac Lane 的定理 3）和 [Rng_Forget_continuous : ContinuousFunctor Rng_Forget]，
 锥层阅读，其中仅顶点的 [Rng_Forget_PreservesAllLimits] 从中派生，以及 [Rng_Forget_reflects_limits] 并列。需要被提升的是什么，以及它比群情况多多少。[Rng] 的一个对象是 Theory/Algebra/Rig.v 的 [RingObject]：一个由 [ring_neg] 扩展 [RigObject] 并带有 [ring_neg_respects] 和 [ring_neg_l] 的 [RigObject]。因此有五个运算被提升——[rig_zero]、[rig_one]、[rig_add]、[rig_mul]、[ring_neg]——而群情况只有三个，并且证明了十一条律：四条来自定义 5.36 条款的计数 (a) [rig_add_assoc]、[rig_add_comm]、[rig_add_zero_l]；(b) [rig_mul_assoc]、[rig_mul_one_l]、[rig_mul_one_r]；(c) [rig_distr_l]、[rig_distr_r]；(d) [rig_mul_zero_l]、[rig_mul_zero_r]——总共十条——加上 [ring_neg_l]。每一条都有三行：应用联合单射性引理，重写定义三角，应用 [K j] 中的律。方法没有改变；只是账目更繁琐。一个地方，环的特征是真正不同的，而不仅仅是更大。[RigHom]（理论/代数/Rig.v）有四个条款——[rig_map_zero]、[rig_map_add]、[rig_map_one]、[rig_map_mul]——而没有关于取反的条款，因为Rig.v的[RigHom_neg]证明了取反由加法逆元的唯一性保持。两个结果，如下所示。因此，取反锥（[rlim_neg_coherence]）的相干性通过那个定理被解决，而它的四个兄弟使用投影；而[rlim_structure_unique]的取反条款是手动陈述的，而不是从同类型中读取的，因为从[RigHom]中完全无法获得关于取反的腿条件。唯一性条款
 尽管如此，其效力与其四个兄弟条款相同：它仅要求各分支将候选否定传递到每个 [K j] 中的 [ring_neg]，而不影响候选结构的任何规则。标题句在 [eq_refl] 上经过机器检查，而不是论证。在极限 [Sets_Complete] 选择 —— 兼容的 Instance/Sets/Complete.v 系列（[Sets_limit_obj]、[Sets_limit_leg] 和 [Sets_Complete]） —— 创建的环正是按坐标逐点构造的：[rng_complete_carrier]、[rng_complete_zero]、[rng_complete_one]、[rng_complete_add]、[rng_complete_mul]、[rng_complete_neg] 和 [rng_complete_leg] 是七个 [eq_refl] 示例，适用于任意形状和任意环图。它们中没有任何内容针对特定的 witness 类别，并且没有插入同构；因此，该文件不需要具体 witness 即可非空构建，并且没有构建任何 witness。关于规定在对态射进行比较时适用 [≈] 的内部规则：四个陈述在这里在态射之间写上 [=]——[rlim_over_legs]、[rng_lift_legs]、[rng_fcone_leg] 和 [rng_complete_leg]——每个都这样做是因为两边是相同的项，证据为 [eq_refl]。它们完整记录了 Mac Lane 的 [F sigma = tau]，这比 [StrictLift] 条款（Structure/Limit/Creation.v）所要求的 [≈] 要严格得多；每一条定律、每一个证明以及被 [rng_strict_lift] 消耗的 [slift_legs] 条款都使用 [≈]。同样适用于对象层次的 [=]：[rlim_over_obj]、[rng_lift_apex]、[rng_fcone_apex]、[rng_complete_carrier] 以及五个 [rng_complete_*] 元素方程，它们比较的是对象和元素，而不是态射，这是该学科允许的例外情况。这里的新内容和非新内容是什么，通过衡量而不是断言。这是第二个获得创造结果的代数范畴，也是第二个获得 [@Complete] 的范畴，而不是第一个：Instance/Grp/Limit.v 是先例（[Grp_Forget_creates_limits]，[Grp_Complete]），该文件是其逐条条款的转置。在所有 [.v] 文件中，对形式为“Definition/Program Definition/Theorem/Lemma/Example <name> : @?Complete|Cocomplete”的声明头进行扫描，该文件之前的清单为 [Sets_Complete] 和 [ConeSet_Complete]（Instance/Sets/Complete.v）、[Sets_Complete_via_Manes]（Structure/Equalizer/Coreflexive.v）、[Subsets_Complete] / [Subsets_Cocomplete]（Instance/Powerset.v）、[Grp_Complete]（Instance/Grp/Limit.v），在 [Proset]（Instance/Proset/Limit.v）有一个双条件，以及两个探测文件——[Rng]、[Ab]、[CMon]、[RMod]、[Mon] 或 [Top] 没有内容。而且“树中不存在环的限制”这一说法是错误的，因此并未提出。Instance/Rng/Zp.v 已经构建了三个：[Zp_limit : IsALimit (ResTower Rcomm d) Zp]、[Zp_int_limit] 和 [PowerSeries_limit]，每个都在一个 [Omega^op] 形状的塔上，并有一个手工构建的承载器。它在那个单一图中也已经具有 ELEMENTWISE 的唯一性——[zp_zero_forced]、[zp_one_forced]、[zp_add_forced]、[zp_mul_forced]、[zp_neg_forced]——并且其标题明确说明了它不证明的内容：“Riehl §5.6 示例 5.6.8 观察到 [Rng] 的基础集函子是 MONADIC 的，因此产生了极限锥……这里并未证明 monadicity，并且也未使用它。”此文件提供了创建一个任意形状和任意图表的功能，并且它同样不通过幺半性：树中的任何文件都没有将 [Rng] 表示为 Eilenberg-Moore 范畴，因此该论证会像群情况那样在下一级重新执行。这里没有说明关于 [Zp] 的任何内容；将 [Zp_limit] 与在 [ResTower] 创建的极限联系起来的工作尚未完成。连续性推论并不新颖，而此前对该标题的修订过度夸大了它的新颖性方向错误。那次修订称 [Rng_Forget] 的连续性“原则上”是可行的，但不能实例化，因为“沿着函子自然同构传输 [ContinuousFunctor] 在树中无处可寻”。这是错误的，对该文件的审计通过用已存在的常数在十二行内构建替代方案驳斥了这一点：Functor/Hom/Continuous.v 中的 [Section Transport] 及其 [ContinuousFunctor_transport] 正是那种构建。所以，诚实的说法是，[Rng_Forget] 的连续性在此文件之前是可以通过 [zpoly_representation]（Instance/Rng/Polynomial.v）和 [zpoly_representable] 达到的——注意这些名称；之前的一个修订引用了一个在树中不存在的 [zpoly_hom_iso]——然后与 Functor/Hom/Limit.v 的 [hom_ContinuousFunctor] 组合，然后再传输。RAPL 不是路径，这里也是，早期修订版的前提是错误的，而其结论是正确的。它说“树中唯一的环伴随是 [free_rng_ab_adjunction]”；实际上至少有四个（[free_rng_ab_adjunction]，Instance/Rng/Free.v；[zmring_adjunction]，Instance/Rng/MonoidRing.v；[grp_ring_adjunction]，Instance/Rng/GroupRing.v；[poly_pointed_adjunction]，Instance/Rng/Pointed.v）。真正正确且重要的是：它们没有一个有 [Rng_Forget : Rng ⟶ Sets] 作为其右伴随（测量后，[grep -P '⊣\s*Rng_Forget(?![A-Za-z0-9_]）返回空值），所以 Adjunction/Continuity.v 的 [right_adjoint_Continuous] 无法到达它。

 因此，没有任何限制下的新内容是 CREATION 的结果，以及 [Rng_Complete]，这是上述路径都无法给出的。在这里连续性作为其推论被重新推导，而不是被声称为首次发现。这个引擎是一个可复用的引理，里面没有任何环论内容。[rng_sets_limit_ext] 说明 [Sets] 中极限锥的各条边是逐元素联合单射的：若顶点的两个点在每一条边上都相同，则它们相等。这仅从中介的唯一性就能证明，利用从顶点自身出发的两个常值映射作为探针——因此不需要终对象，也不引入任何额外的模块。Instance/Grp/Limit.v 将其声明为 [sets_limit_ext]，在此处以不同的名称重新声明，而不是导入，有两个原因：导入它会使该文件依赖 [Grp]，这是一个架构上的逆转，而且它自然的位置应该是在 Instance/Sets/Complete.v 中其捐赠者旁边，而这个改动并未触及该位置。这个重复是真实的，并被如此记录；无论谁上游提交该词条，都应该撤回两个副本。UNIVERSES，分别在 binder 和 block 上测量，总共有 122 个常量（104 个 [.glob] 声明头加上 18 个 [Program] 义务，这些在任何源级阅读中都看不到）：在任何地方 [Set] 出现的次数为零，并且只有 12 个带有 block 方程。（这段的早期版本说的是 11 个，并补充“18 个义务没有 block 方程”；两者都是错误的，而且原因值得记录——在 [Require Import Category.Instance.Rng.Limit] 之后，BARE 义务名称未被绑定，因此 [About rng_sets_const_obligation_1] 的答案是“未找到”，且未加限定的遍历默默报告没有结果。）重新测量并使用完全限定的名称，[Category.Instance.Rng.Limit.<name>]，总共122个常量。）其中四个是通用的[Sets]部分——[rng_sets_pre]、[rng_sets_med_eq]、[rng_sets_limit_ext]和[rng_sets_const]——这四个都包含[u0 = u3]，它标识形状的同态与证明宇宙以及[Sets]的载体宇宙，前三个还额外包含[u1 = u2]，它标识环境的两个部分；[u0 = u3]是[IsALimit]的操作，而非此文件的操作。七个是[rng_complete_*]的回读，它们显式绑定其形状，因此包含[u = u0]，标识形状的对象宇宙与其同态与证明宇宙——也就是[Complete]自身的[@{u u u u0}]形状被完整写出，继承自[Sets_Complete]，而此处未被缩小。第十二个是 [rng_sets_const_obligation_1]，携带与其所属常数相同的 [u0 = u3]；其余 17 个义务没有携带任何。剩下的常数也没有携带，其中包括 [Rng_Complete@{u u0 u1} : Complete@{u u u u0}]（[u < u0], [u < u1]）和 [Rng_Forget_creates_limits@{u u0 u1 u2 u3 u4}]，因此小数纪律完全是 [Sets_Complete] 的。这与群情况的解读完全一致，在携带方程的一般常数的数量上相同。

 [Print Assumptions] 为所有六个主要常数——[Rng_Complete]、[Rng_Forget_continuous]、[Rng_Forget_creates_limits]、[Rng_Forget_PreservesAllLimits]、[Rng_Forget_StrictlyCreatesLimits] 和 [Rng_Forget_reflects_limits] 报告“在全局上下文下封闭”。这值得一提，因为 Instance/Rng.v 自身达到了 ZArith 和 QArith，用于其具体证据；这里没有引入这些内容，该文件仅使用范畴、遗忘函子和环代数。未交付。（1）没有为 [Rng_Forget_Ab] (Instance/Rng.v) 创建结果，原因是结构上的，而不是努力的问题：下面使用的锥中介方法不能转用于 [Ab]。乘法需要一个锥，其顶点是与腿 [(a, b) ↦ leg a · leg b] 的直和，而那个映射是双线性的，而不是加性的，所以它不是 [Ab] 的态射，并且没有锥可用于取中介；乘法单位更糟，因为从 [Ab] 的零对象（Instance/Ab.v）出的唯一典型映射会将所有东西映射为零，因此无法选取 [1]。可用的修复是以一个生成元为基础的自由阿贝尔群（Instance/Ab/Free.v 的 [FreeAb]）作为探针对象，乘法以一次一个参数的方式重新构建为一个元素索引的中介族 [L ⟶ L]，并从联合单射性中恢复外部参数的一致性。那是一个不同的参数，不是这个实例化的参数，因此留给它自身的变化。（2）[Rng] 没有余极限，也不完全余完备。（更正，#450：[Rng] 自 #450 起是完全余完备的，由 Instance/Rng/Colimit.v 的 [Rng_Cocomplete_via_GAFT] 以及在对角线处应用本文件的 [Rng_Complete] 作为其完备性假设的伴随函子定理；环的余积在那里是 [Rng_Cocartesian_via_GAFT]。）没有任何这些余极限被计算。) (3) 没有涵盖 [CMon]、[Ab]、[Rng] 和 [RMod] 的通用签名变体，同时引擎保持不变。 (4) 没有将创建的极限与 Instance/Rng/Zp.v 的 [Zp_limit] 进行比较，也没有将创建的二元积与 [Rng] 上的任何积结构进行比较。 (5) 没有单子性陈述，也没有比较函子，因此这里没有任何内容说明 [Rng] 是 Eilenberg-Moore 范畴，Riehl 的示例 5.6.8 仍然是一种观察，而不是树中的定理。 (6) Test/ 下没有拒绝探测文件：该文件满足的边界是群情况的边界，而 Test/ProbeGrpLimit411.v 已经固定了它们，但这里没有任何内容由自身的探针保护，这是一个空白，而不是一个声明。(7) 没有任何东西被注册为 [Instance] —— 文件声明没有，
 按照其模板，因为所选的限制不应变得全球可解析。

 该文件对 [make todo] 没有任何贡献。
*)

(* * * Joint monicity of limit legs in [Sets], elementwise / * * 在 [Sets] 中极限腿的联合单调性，按元素 *)

Section RngSetsExt.

Context {J : Category}.
Context {F : J ⟶ Sets}.
Context {c : Sets}.
Context (H : IsALimit F c).

Definition rng_sets_pre {d : Sets} (u : d ~{Sets}~> c) : Cone F :=
  @Build_Cone J Sets F d
    (@Build_ACone J Sets d F (fun j => limit_leg H j ∘ u)
       (fun x y f =>
          transitivity (comp_assoc _ _ _)
            (@compose_respects Sets _ _ _ _ _ (limit_leg_coherence H f) _ _
               (reflexivity u)))).

Lemma rng_sets_med_eq {d : Sets} (u v : d ~{Sets}~> c) :
  (∀ j : J, limit_leg H j ∘ u ≈ limit_leg H j ∘ v) → u ≈ v.
Proof.
  intro Huv.
  apply (limit_med_eq H (rng_sets_pre u)).
  - intro j; reflexivity.
  - intro j; symmetry; apply Huv.
Qed.

Program Definition rng_sets_const (x : carrier c) : c ~{Sets}~> c :=
  {| morphism := fun _ => x |}.

Lemma rng_sets_limit_ext (x y : carrier c) :
  (∀ j : J, limit_leg H j x ≈ limit_leg H j y) → x ≈ y.
Proof.
  intro Hxy.
  exact (rng_sets_med_eq (rng_sets_const x) (rng_sets_const y)
           (fun j a => Hxy j) x).
Qed.

End RngSetsExt.

(* * * The created ring structure on a limit of underlying sets / * * 在基础集合的极限上创建的环结构 *)

Section RngLift.

Context {J : Category}.
Context (K : J ⟶ Rng).
Context (L : Limit (Rng_Forget ◯ K)).

Definition rlim_leg (j : J) : vertex_obj[L] ~{Sets}~> rig_setoid (K j) :=
  limit_leg (limit_is_alimit L) j.

Lemma rlim_leg_coherence {x y : J} (f : x ~{J}~> y)
  (a : carrier vertex_obj[L]) :
  rig_map (fmap[K] f) (rlim_leg x a) ≈ rlim_leg y a.
Proof. exact (limit_leg_coherence (limit_is_alimit L) f a). Qed.

Lemma rlim_ext (x y : carrier vertex_obj[L]) :
  (∀ j : J, rlim_leg j x ≈ rlim_leg j y) → x ≈ y.
Proof. exact (rng_sets_limit_ext (limit_is_alimit L) x y). Qed.

(** ** The addition / ** 加法 *)

Definition rlim_pair : Sets :=
  {| carrier   := carrier vertex_obj[L] * carrier vertex_obj[L]
   ; is_setoid := prod_setoid |}.

Program Definition rlim_add_leg (j : J) :
  rlim_pair ~{Sets}~> rig_setoid (K j) :=
  {| morphism := fun p =>
       rig_add (K j) (rlim_leg j (fst p)) (rlim_leg j (snd p)) |}.
Next Obligation.
  intros p q Hpq.
  destruct Hpq as [H1 H2].
  now rewrite H1, H2.
Qed.

Lemma rlim_add_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Rng_Forget ◯ K] f ∘ rlim_add_leg x ≈ rlim_add_leg y.
Proof.
  intro p; simpl.
  rewrite rig_map_add.
  now rewrite !rlim_leg_coherence.
Qed.

Definition rlim_add_cone : Cone (Rng_Forget ◯ K) :=
  @Build_Cone J Sets (Rng_Forget ◯ K) rlim_pair
    (@Build_ACone J Sets rlim_pair (Rng_Forget ◯ K)
       rlim_add_leg (@rlim_add_coherence)).

Definition rlim_add_map : rlim_pair ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) rlim_add_cone.

Definition rlim_add (a b : carrier vertex_obj[L]) : carrier vertex_obj[L] :=
  rlim_add_map (a, b).

Lemma rlim_add_triangle (j : J) (a b : carrier vertex_obj[L]) :
  rlim_leg j (rlim_add a b) ≈ rig_add (K j) (rlim_leg j a) (rlim_leg j b).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) rlim_add_cone j (a, b)).
Qed.

Lemma rlim_add_respects :
  Proper (equiv ==> equiv ==> equiv) rlim_add.
Proof.
  intros a a' Ha b b' Hb.
  exact (proper_morphism rlim_add_map (a, b) (a', b') (Ha, Hb)).
Qed.

(** ** The multiplication / ** 乘法 *)

Program Definition rlim_mul_leg (j : J) :
  rlim_pair ~{Sets}~> rig_setoid (K j) :=
  {| morphism := fun p =>
       rig_mul (K j) (rlim_leg j (fst p)) (rlim_leg j (snd p)) |}.
Next Obligation.
  intros p q Hpq.
  destruct Hpq as [H1 H2].
  now rewrite H1, H2.
Qed.

Lemma rlim_mul_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Rng_Forget ◯ K] f ∘ rlim_mul_leg x ≈ rlim_mul_leg y.
Proof.
  intro p; simpl.
  rewrite rig_map_mul.
  now rewrite !rlim_leg_coherence.
Qed.

Definition rlim_mul_cone : Cone (Rng_Forget ◯ K) :=
  @Build_Cone J Sets (Rng_Forget ◯ K) rlim_pair
    (@Build_ACone J Sets rlim_pair (Rng_Forget ◯ K)
       rlim_mul_leg (@rlim_mul_coherence)).

Definition rlim_mul_map : rlim_pair ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) rlim_mul_cone.

Definition rlim_mul (a b : carrier vertex_obj[L]) : carrier vertex_obj[L] :=
  rlim_mul_map (a, b).

Lemma rlim_mul_triangle (j : J) (a b : carrier vertex_obj[L]) :
  rlim_leg j (rlim_mul a b) ≈ rig_mul (K j) (rlim_leg j a) (rlim_leg j b).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) rlim_mul_cone j (a, b)).
Qed.

Lemma rlim_mul_respects :
  Proper (equiv ==> equiv ==> equiv) rlim_mul.
Proof.
  intros a a' Ha b b' Hb.
  exact (proper_morphism rlim_mul_map (a, b) (a', b') (Ha, Hb)).
Qed.

(** ** The additive unit / ** 添加单元 *)

Program Definition rlim_zero_leg (j : J) :
  unit_setoid_object ~{Sets}~> rig_setoid (K j) :=
  {| morphism := fun _ => rig_zero (K j) |}.

Lemma rlim_zero_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Rng_Forget ◯ K] f ∘ rlim_zero_leg x ≈ rlim_zero_leg y.
Proof. intro p; simpl; apply rig_map_zero. Qed.

Definition rlim_zero_cone : Cone (Rng_Forget ◯ K) :=
  @Build_Cone J Sets (Rng_Forget ◯ K) unit_setoid_object
    (@Build_ACone J Sets unit_setoid_object (Rng_Forget ◯ K)
       rlim_zero_leg (@rlim_zero_coherence)).

Definition rlim_zero_map : unit_setoid_object ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) rlim_zero_cone.

Definition rlim_zero : carrier vertex_obj[L] := rlim_zero_map ttt.

Lemma rlim_zero_triangle (j : J) :
  rlim_leg j rlim_zero ≈ rig_zero (K j).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) rlim_zero_cone j ttt).
Qed.

(** ** The multiplicative unit / ** 乘法单位 *)

Program Definition rlim_one_leg (j : J) :
  unit_setoid_object ~{Sets}~> rig_setoid (K j) :=
  {| morphism := fun _ => rig_one (K j) |}.

Lemma rlim_one_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Rng_Forget ◯ K] f ∘ rlim_one_leg x ≈ rlim_one_leg y.
Proof. intro p; simpl; apply rig_map_one. Qed.

Definition rlim_one_cone : Cone (Rng_Forget ◯ K) :=
  @Build_Cone J Sets (Rng_Forget ◯ K) unit_setoid_object
    (@Build_ACone J Sets unit_setoid_object (Rng_Forget ◯ K)
       rlim_one_leg (@rlim_one_coherence)).

Definition rlim_one_map : unit_setoid_object ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) rlim_one_cone.

Definition rlim_one : carrier vertex_obj[L] := rlim_one_map ttt.

Lemma rlim_one_triangle (j : J) :
  rlim_leg j rlim_one ≈ rig_one (K j).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) rlim_one_cone j ttt).
Qed.

(** ** The additive inverse / ** 加法逆元 *)

Program Definition rlim_neg_leg (j : J) :
  vertex_obj[L] ~{Sets}~> rig_setoid (K j) :=
  {| morphism := fun a => ring_neg (K j) (rlim_leg j a) |}.
Next Obligation. intros a b Hab; now rewrite Hab. Qed.

Lemma rlim_neg_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Rng_Forget ◯ K] f ∘ rlim_neg_leg x ≈ rlim_neg_leg y.
Proof.
  intro a; simpl.
  rewrite RigHom_neg.
  now rewrite rlim_leg_coherence.
Qed.

Definition rlim_neg_cone : Cone (Rng_Forget ◯ K) :=
  @Build_Cone J Sets (Rng_Forget ◯ K) vertex_obj[L]
    (@Build_ACone J Sets vertex_obj[L] (Rng_Forget ◯ K)
       rlim_neg_leg (@rlim_neg_coherence)).

Definition rlim_neg_map : vertex_obj[L] ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) rlim_neg_cone.

Definition rlim_neg (a : carrier vertex_obj[L]) : carrier vertex_obj[L] :=
  rlim_neg_map a.

Lemma rlim_neg_triangle (j : J) (a : carrier vertex_obj[L]) :
  rlim_leg j (rlim_neg a) ≈ ring_neg (K j) (rlim_leg j a).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) rlim_neg_cone j a).
Qed.

Lemma rlim_neg_respects : Proper (equiv ==> equiv) rlim_neg.
Proof. intros a b Hab; exact (proper_morphism rlim_neg_map a b Hab). Qed.

(* * ** The eleven laws, each by joint monicity of the legs / * ** 十一条定律，每条由腿的联合单调性决定 *)

Lemma rlim_add_assoc (a b c : carrier vertex_obj[L]) :
  rlim_add (rlim_add a b) c ≈ rlim_add a (rlim_add b c).
Proof.
  apply rlim_ext; intro j.
  rewrite !rlim_add_triangle.
  apply rig_add_assoc.
Qed.

Lemma rlim_add_comm (a b : carrier vertex_obj[L]) :
  rlim_add a b ≈ rlim_add b a.
Proof.
  apply rlim_ext; intro j.
  rewrite !rlim_add_triangle.
  apply rig_add_comm.
Qed.

Lemma rlim_add_zero_l (a : carrier vertex_obj[L]) :
  rlim_add rlim_zero a ≈ a.
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_add_triangle, rlim_zero_triangle.
  apply rig_add_zero_l.
Qed.

Lemma rlim_mul_assoc (a b c : carrier vertex_obj[L]) :
  rlim_mul (rlim_mul a b) c ≈ rlim_mul a (rlim_mul b c).
Proof.
  apply rlim_ext; intro j.
  rewrite !rlim_mul_triangle.
  apply rig_mul_assoc.
Qed.

Lemma rlim_mul_one_l (a : carrier vertex_obj[L]) :
  rlim_mul rlim_one a ≈ a.
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_mul_triangle, rlim_one_triangle.
  apply rig_mul_one_l.
Qed.

Lemma rlim_mul_one_r (a : carrier vertex_obj[L]) :
  rlim_mul a rlim_one ≈ a.
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_mul_triangle, rlim_one_triangle.
  apply rig_mul_one_r.
Qed.

Lemma rlim_distr_l (a b c : carrier vertex_obj[L]) :
  rlim_mul a (rlim_add b c)
    ≈ rlim_add (rlim_mul a b) (rlim_mul a c).
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_add_triangle, !rlim_mul_triangle, rlim_add_triangle.
  apply rig_distr_l.
Qed.

Lemma rlim_distr_r (a b c : carrier vertex_obj[L]) :
  rlim_mul (rlim_add a b) c
    ≈ rlim_add (rlim_mul a c) (rlim_mul b c).
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_add_triangle, !rlim_mul_triangle, rlim_add_triangle.
  apply rig_distr_r.
Qed.

Lemma rlim_mul_zero_l (a : carrier vertex_obj[L]) :
  rlim_mul rlim_zero a ≈ rlim_zero.
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_mul_triangle, !rlim_zero_triangle.
  apply rig_mul_zero_l.
Qed.

Lemma rlim_mul_zero_r (a : carrier vertex_obj[L]) :
  rlim_mul a rlim_zero ≈ rlim_zero.
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_mul_triangle, !rlim_zero_triangle.
  apply rig_mul_zero_r.
Qed.

Lemma rlim_neg_l (a : carrier vertex_obj[L]) :
  rlim_add (rlim_neg a) a ≈ rlim_zero.
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_add_triangle, rlim_neg_triangle, rlim_zero_triangle.
  apply ring_neg_l.
Qed.

(* * ** The vertex's equality is propositional / * ** 顶点的相等性是命题性的 *)

(*
 Since the PR “algebraic carriers are sets” (2026-09-17) a [RigObject]
 carries [rig_prop], so the lifted ring owes a [Prop]-valued relation on
 [vertex_obj[L]] -- and [L] is an ARBITRARY limit of the underlying sets,
 not the one [Sets_Complete] chooses, so Instance/Sets/Propositional.v's
 [limit_PropEquiv] does not apply on the nose.  A HYPOTHESIS on [L] would
 have been fatal for the same reason it was at [LimitAb]
 (Instance/Ab/Limit.v): [CreatesLimits] quantifies over every [L] and
 leaves no place to put it.

 The relation is instead the one this section already has a theorem about:
 two points of the vertex are related when every LEG relates them.
 [rlim_ext] is exactly the implication into `≈`, and it holds at an
 arbitrary limit because a limit's vertex is detected by its projections;
 the converse is each leg being a setoid map.  So a limit of propositional
 carriers is propositional, with no extra hypothesis anywhere. 

 --------
 自从 PR “代数载体是集合” (2026-09-17) 以来，[RigObject] 携带 [rig_prop]，因此提升的环依赖于 [Prop] 值的关系在 [vertex_obj[L] 上——而 [L] 是底层集合的任意极限，而不是 [Sets_Complete] 选择的那个，因此 Instance/Sets/Propositional.v 的 [limit_PropEquiv] 并不直接适用。对 [L] 的假设将是致命的，原因与 [LimitAb] (Instance/Ab/Limit.v) 处相同：[CreatesLimits] 对每个 [L] 量化，而且没有地方放置它。这个关系恰好是本节已经有定理说明的那种关系：
 当顶点的两个点在每条腿上都相关时，它们关联。
 [rlim_ext] 正是对 `≈` 的蕴含，并且它在任意极限处成立，因为极限的顶点可以通过它的投影来检测；
 反之，每条腿都是集合同态映射。所以命题承载的极限是命题的，而没有任何额外假设。
*)
Definition rlim_prop : PropEquiv (is_setoid vertex_obj[L]) :=
  @PropEquiv_of_relation _ (is_setoid vertex_obj[L])
    (fun x y => forall j : J,
       @pequiv _ _ (rig_prop (K j)) (rlim_leg j x) (rlim_leg j y))
    (fun x y H => rlim_ext x y (fun j => pequiv_to _ _ (H j)))
    (fun x y H j => pequiv_from _ _ (proper_morphism (rlim_leg j) x y H)).

(* * ** The lifted rig and the lifted ring / * ** 提起的装置和提起的环 *)

Definition LimitRig : RigObject :=
  {| rig_setoid       := vertex_obj[L]
   ; rig_zero         := rlim_zero
   ; rig_add          := rlim_add
   ; rig_one          := rlim_one
   ; rig_mul          := rlim_mul
   ; rig_add_respects := rlim_add_respects
   ; rig_mul_respects := rlim_mul_respects
   ; rig_add_assoc    := rlim_add_assoc
   ; rig_add_comm     := rlim_add_comm
   ; rig_add_zero_l   := rlim_add_zero_l
   ; rig_mul_assoc    := rlim_mul_assoc
   ; rig_mul_one_l    := rlim_mul_one_l
   ; rig_mul_one_r    := rlim_mul_one_r
   ; rig_distr_l      := rlim_distr_l
   ; rig_distr_r      := rlim_distr_r
   ; rig_mul_zero_l   := rlim_mul_zero_l
   ; rig_mul_zero_r   := rlim_mul_zero_r
   ; rig_prop         := rlim_prop |}.

Definition LimitRing : RingObject :=
  {| ring_rig          := LimitRig
   ; ring_neg          := rlim_neg
   ; ring_neg_respects := rlim_neg_respects
   ; ring_neg_l        := rlim_neg_l |}.

(* * ** The legs are ring homomorphisms / * ** 这些脚是环同态 *)

Program Definition rlim_hom (j : J) : RigHom LimitRing (K j) :=
  {| rig_map := rlim_leg j |}.
Next Obligation. apply rlim_zero_triangle. Qed.
Next Obligation. apply rlim_add_triangle. Qed.
Next Obligation. apply rlim_one_triangle. Qed.
Next Obligation. apply rlim_mul_triangle. Qed.

Lemma rlim_hom_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ rlim_hom x ≈ rlim_hom y.
Proof. intro a; exact (rlim_leg_coherence f a). Qed.

Definition rlim_cone : Cone K :=
  @Build_Cone J Rng K LimitRing
    (@Build_ACone J Rng LimitRing K rlim_hom (@rlim_hom_coherence)).

(* * ** Strictness: the lifted cone lies over [L] on the nose / * ** 严格性：被抬起的圆锥位于鼻子上的 [L] 上 *)

Definition rlim_over_obj : Rng_Forget LimitRing = vertex_obj[L] := eq_refl.

Definition rlim_over_legs (j : J) :
  fmap[Rng_Forget] (cone_leg rlim_cone j) = rlim_leg j := eq_refl.

(** ** The lifted cone is limiting / ** 提升的锥体是有限的 *)

Definition rlim_car_med (N : Cone K) :
  rig_setoid vertex_obj[N] ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) (FCone Rng_Forget N).

Lemma rlim_car_med_commutes (N : Cone K) (j : J)
  (a : carrier (rig_setoid vertex_obj[N])) :
  rlim_leg j (rlim_car_med N a) ≈ rig_map (cone_leg N j) a.
Proof.
  exact (limit_med_commutes (limit_is_alimit L) (FCone Rng_Forget N) j a).
Qed.

Lemma rlim_car_med_zero (N : Cone K) :
  rlim_car_med N (rig_zero vertex_obj[N]) ≈ rlim_zero.
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_car_med_commutes, rlim_zero_triangle.
  apply rig_map_zero.
Qed.

Lemma rlim_car_med_add (N : Cone K)
  (a b : carrier (rig_setoid vertex_obj[N])) :
  rlim_car_med N (rig_add vertex_obj[N] a b)
    ≈ rlim_add (rlim_car_med N a) (rlim_car_med N b).
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_car_med_commutes, rlim_add_triangle, !rlim_car_med_commutes.
  apply rig_map_add.
Qed.

Lemma rlim_car_med_one (N : Cone K) :
  rlim_car_med N (rig_one vertex_obj[N]) ≈ rlim_one.
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_car_med_commutes, rlim_one_triangle.
  apply rig_map_one.
Qed.

Lemma rlim_car_med_mul (N : Cone K)
  (a b : carrier (rig_setoid vertex_obj[N])) :
  rlim_car_med N (rig_mul vertex_obj[N] a b)
    ≈ rlim_mul (rlim_car_med N a) (rlim_car_med N b).
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_car_med_commutes, rlim_mul_triangle, !rlim_car_med_commutes.
  apply rig_map_mul.
Qed.

Program Definition rlim_med (N : Cone K) : vertex_obj[N] ~{Rng}~> LimitRing :=
  {| rig_map := rlim_car_med N |}.
Next Obligation. apply rlim_car_med_zero. Qed.
Next Obligation. apply rlim_car_med_add. Qed.
Next Obligation. apply rlim_car_med_one. Qed.
Next Obligation. apply rlim_car_med_mul. Qed.

Definition rlim_created : IsALimit K LimitRing.
Proof.
  unshelve refine {| limit_acone := @coneFrom _ _ _ rlim_cone |}.
  intro N.
  unshelve refine {| unique_obj := rlim_med N |}.
  - intros j a.
    exact (rlim_car_med_commutes N j a).
  - intros v Hv a.
    exact (limit_med_unique (limit_is_alimit L) (FCone Rng_Forget N)
             (rig_map v) Hv a).
Defined.

(* * ** Uniqueness of the lifted structure (Mac Lane's Theorem 2) / * ** 提升结构的唯一性（Mac Lane 定理 2） *)

Lemma rlim_zero_unique (z : carrier vertex_obj[L])
  (Hz : ∀ j : J, rlim_leg j z ≈ rig_zero (K j)) : z ≈ rlim_zero.
Proof.
  apply rlim_ext; intro j.
  now rewrite Hz, rlim_zero_triangle.
Qed.

Lemma rlim_one_unique (e : carrier vertex_obj[L])
  (He : ∀ j : J, rlim_leg j e ≈ rig_one (K j)) : e ≈ rlim_one.
Proof.
  apply rlim_ext; intro j.
  now rewrite He, rlim_one_triangle.
Qed.

Lemma rlim_add_unique
  (p : carrier vertex_obj[L] → carrier vertex_obj[L] → carrier vertex_obj[L])
  (Hp : ∀ (j : J) a b,
     rlim_leg j (p a b) ≈ rig_add (K j) (rlim_leg j a) (rlim_leg j b))
  (a b : carrier vertex_obj[L]) : p a b ≈ rlim_add a b.
Proof.
  apply rlim_ext; intro j.
  now rewrite Hp, rlim_add_triangle.
Qed.

Lemma rlim_mul_unique
  (m : carrier vertex_obj[L] → carrier vertex_obj[L] → carrier vertex_obj[L])
  (Hm : ∀ (j : J) a b,
     rlim_leg j (m a b) ≈ rig_mul (K j) (rlim_leg j a) (rlim_leg j b))
  (a b : carrier vertex_obj[L]) : m a b ≈ rlim_mul a b.
Proof.
  apply rlim_ext; intro j.
  now rewrite Hm, rlim_mul_triangle.
Qed.

Lemma rlim_neg_unique
  (n : carrier vertex_obj[L] → carrier vertex_obj[L])
  (Hn : ∀ (j : J) a, rlim_leg j (n a) ≈ ring_neg (K j) (rlim_leg j a))
  (a : carrier vertex_obj[L]) : n a ≈ rlim_neg a.
Proof.
  apply rlim_ext; intro j.
  now rewrite Hn, rlim_neg_triangle.
Qed.

(*
 The five clauses together: Mac Lane's “there is exactly one ring
 structure on the limit making every projection a homomorphism”.  No law
 of the candidate structure is consumed -- only that the legs preserve
 it. 

 --------
 五条条款合在一起：Mac Lane 的“在极限上恰好存在一个环结构，使得每个投影都是同态”。候选结构的任何定律都没有被消耗——只是说各条腿保持了该结构。
*)
Lemma rlim_structure_unique
  (z e : carrier vertex_obj[L])
  (p m : carrier vertex_obj[L] → carrier vertex_obj[L] →
           carrier vertex_obj[L])
  (n : carrier vertex_obj[L] → carrier vertex_obj[L])
  (Hz : ∀ j : J, rlim_leg j z ≈ rig_zero (K j))
  (He : ∀ j : J, rlim_leg j e ≈ rig_one (K j))
  (Hp : ∀ (j : J) a b,
     rlim_leg j (p a b) ≈ rig_add (K j) (rlim_leg j a) (rlim_leg j b))
  (Hm : ∀ (j : J) a b,
     rlim_leg j (m a b) ≈ rig_mul (K j) (rlim_leg j a) (rlim_leg j b))
  (Hn : ∀ (j : J) a, rlim_leg j (n a) ≈ ring_neg (K j) (rlim_leg j a)) :
  (((z ≈ rlim_zero) * (e ≈ rlim_one))
     * ((∀ a b, p a b ≈ rlim_add a b) * (∀ a b, m a b ≈ rlim_mul a b)))
    * (∀ a, n a ≈ rlim_neg a).
Proof.
  split; [ split; [ split | split ] | ].
  - exact (rlim_zero_unique z Hz).
  - exact (rlim_one_unique e He).
  - exact (rlim_add_unique p Hp).
  - exact (rlim_mul_unique m Hm).
  - exact (rlim_neg_unique n Hn).
Qed.

End RngLift.

(* * * Reflection: a cone of rings whose image is limiting is limiting / * * 反射：一个环锥，其图像是极限的就是极限的 *)

Section RngReflect.

Context {J : Category}.
Context (K : J ⟶ Rng).
Context (M : Cone K).
Context (HM : IsLimitCone (FCone Rng_Forget M)).

Definition rrefl_med (N : Cone K) :
  rig_setoid vertex_obj[N] ~{Sets}~> rig_setoid vertex_obj[M] :=
  limit_med (limitcone_isalimit HM) (FCone Rng_Forget N).

Lemma rrefl_med_commutes (N : Cone K) (j : J)
  (a : carrier (rig_setoid vertex_obj[N])) :
  rig_map (cone_leg M j) (rrefl_med N a) ≈ rig_map (cone_leg N j) a.
Proof using All.
  exact (limit_med_commutes (limitcone_isalimit HM) (FCone Rng_Forget N) j a).
Qed.

Lemma rrefl_ext (x y : carrier (rig_setoid vertex_obj[M])) :
  (∀ j : J, rig_map (cone_leg M j) x ≈ rig_map (cone_leg M j) y) → x ≈ y.
Proof using All. exact (rng_sets_limit_ext (limitcone_isalimit HM) x y). Qed.

Lemma rrefl_med_zero (N : Cone K) :
  rrefl_med N (rig_zero vertex_obj[N]) ≈ rig_zero vertex_obj[M].
Proof using All.
  apply rrefl_ext; intro j.
  rewrite rrefl_med_commutes, !rig_map_zero.
  reflexivity.
Qed.

Lemma rrefl_med_add (N : Cone K)
  (a b : carrier (rig_setoid vertex_obj[N])) :
  rrefl_med N (rig_add vertex_obj[N] a b)
    ≈ rig_add vertex_obj[M] (rrefl_med N a) (rrefl_med N b).
Proof using All.
  apply rrefl_ext; intro j.
  rewrite rrefl_med_commutes, !rig_map_add, !rrefl_med_commutes.
  reflexivity.
Qed.

Lemma rrefl_med_one (N : Cone K) :
  rrefl_med N (rig_one vertex_obj[N]) ≈ rig_one vertex_obj[M].
Proof using All.
  apply rrefl_ext; intro j.
  rewrite rrefl_med_commutes, !rig_map_one.
  reflexivity.
Qed.

Lemma rrefl_med_mul (N : Cone K)
  (a b : carrier (rig_setoid vertex_obj[N])) :
  rrefl_med N (rig_mul vertex_obj[N] a b)
    ≈ rig_mul vertex_obj[M] (rrefl_med N a) (rrefl_med N b).
Proof using All.
  apply rrefl_ext; intro j.
  rewrite rrefl_med_commutes, !rig_map_mul, !rrefl_med_commutes.
  reflexivity.
Qed.

Program Definition rrefl_hom (N : Cone K) :
  vertex_obj[N] ~{Rng}~> vertex_obj[M] := {| rig_map := rrefl_med N |}.
Next Obligation. apply rrefl_med_zero. Qed.
Next Obligation. apply rrefl_med_add. Qed.
Next Obligation. apply rrefl_med_one. Qed.
Next Obligation. apply rrefl_med_mul. Qed.

Definition rng_reflects : IsLimitCone M.
Proof using All.
  intro N.
  unshelve refine {| unique_obj := rrefl_hom N |}.
  - intros j a.
    exact (rrefl_med_commutes N j a).
  - intros v Hv a.
    exact (limit_med_unique (limitcone_isalimit HM) (FCone Rng_Forget N)
             (rig_map v) Hv a).
Defined.

End RngReflect.

(* * * [Rng_Forget] strictly creates every limit / * * [Rng_Forget] 严格地创造每一个限制 *)

Section RngStrictlyCreates.

Context {J : Category}.
Context (K : J ⟶ Rng).

Definition rng_strict_lift (N : Cone (Rng_Forget ◯ K)) (HN : IsLimitCone N) :
  StrictLift K Rng_Forget N :=
  @Build_StrictLift J Rng Sets K Rng_Forget N
    (rlim_cone K (@Build_Limit J Sets (Rng_Forget ◯ K) N HN))
    eq_refl
    (fun x => reflexivity _).

Definition Rng_Forget_StrictlyCreatesLimit : StrictlyCreatesLimit K Rng_Forget.
Proof.
  unshelve refine {| screates := rng_strict_lift |}.
  - intros N HN.
    exact (@ump_limit _ _ _ _
             (rlim_created K (@Build_Limit J Sets (Rng_Forget ◯ K) N HN))).
  - intros M HM.
    exact (rng_reflects K M HM).
Defined.

Definition Rng_Forget_CreatesLimit : CreatesLimit K Rng_Forget :=
  StrictlyCreatesLimit_CreatesLimit Rng_Forget_StrictlyCreatesLimit.

End RngStrictlyCreates.

Definition Rng_Forget_StrictlyCreatesLimits :
  StrictlyCreatesLimits Rng_Forget :=
  fun J K => Rng_Forget_StrictlyCreatesLimit K.

Definition Rng_Forget_creates_limits : CreatesAllLimits Rng_Forget :=
  fun J K => Rng_Forget_CreatesLimit K.

Definition Rng_Forget_reflects_limits {J : Category} (K : J ⟶ Rng) :
  ReflectsLimitCone K Rng_Forget :=
  creates_reflects_limits (Rng_Forget_CreatesLimit K).

(*
 Mac Lane's uniqueness clause at the categorical level: any cone of
 rings lying over [N] is canonically isomorphic to the created one.
 This is the generic [screates_lift_unique] at this instance, not a
 restatement. 

 --------
 麦克·莱恩在范畴层面的唯一性条款：任何位于  [N]  之上的环的锥体都与所创建的锥体在范畴上同构。这是在此情况下的通用  [screates_lift_unique] ，不是重述。
*)

Definition Rng_lift_cone_unique {J : Category} (K : J ⟶ Rng)
  (N : Cone (Rng_Forget ◯ K)) (HN : IsLimitCone N)
  (M : Cone K) (i : ConeIso (FCone Rng_Forget M) N) :
  ConeIso M (slift_cone (screates N HN)) :=
  screates_lift_unique (Rng_Forget_StrictlyCreatesLimit K) N HN M i.

(* * * The image of a cone of rings is the elementwise cone / * * 圆环圆锥的图像是元素圆锥 *)

Example rng_fcone_apex {J : Category} (K : J ⟶ Rng) (N : Cone K) :
  vertex_obj[FCone Rng_Forget N] = rig_setoid vertex_obj[N] := eq_refl.

Example rng_fcone_leg {J : Category} (K : J ⟶ Rng) (N : Cone K) (j : J) :
  cone_leg (FCone Rng_Forget N) j = rig_map (cone_leg N j) := eq_refl.

(* * * Mac Lane's Theorem 2: the lifting half / * * 麦克雷恩定理2：提升部分 *)

Definition Rng_Forget_lifts_limits {J : Category} (K : J ⟶ Rng)
  (L : Limit (Rng_Forget ◯ K)) : Limit K :=
  creates_limit_lift (Rng_Forget_CreatesLimit K) L.

Example rng_lift_apex {J : Category} (K : J ⟶ Rng)
  (L : Limit (Rng_Forget ◯ K)) :
  Rng_Forget (vertex_obj[Rng_Forget_lifts_limits K L]) = vertex_obj[L]
  := eq_refl.

Example rng_lift_legs {J : Category} (K : J ⟶ Rng)
  (L : Limit (Rng_Forget ◯ K)) (j : J) :
  fmap[Rng_Forget]
    (cone_leg (@limit_cone _ _ _ (Rng_Forget_lifts_limits K L)) j)
    = limit_leg (limit_is_alimit L) j
  := eq_refl.

(* * * Corollaries: [Rng] is complete and [Rng_Forget] is continuous / * * 推论：[Rng] 是完备的，[Rng_Forget] 是连续的 *)

Definition Rng_Complete : @Complete Rng :=
  creates_limits_Complete Rng_Forget Sets_Complete Rng_Forget_creates_limits.

(*
 [ContinuousFunctor] is [PreservesLimitCone] quantified over every shape
 and diagram, which is what the word means in Mac Lane §V.4 -- the
 apex-only [PreservesAllLimits] below is its CONSEQUENCE, not the
 definition (Structure/Limit/Preservation.v). 

 --------
 [ContinuousFunctor] 是在每个形状和图表上量化的 [PreservesLimitCone]，这就是 Mac Lane §V.4 中这个词的含义——下面仅顶点的 [PreservesAllLimits] 是它的结果，而不是定义（Structure/Limit/Preservation.v）。
*)

Definition Rng_Forget_continuous : ContinuousFunctor Rng_Forget :=
  creates_limits_continuous Rng_Forget Sets_Complete Rng_Forget_creates_limits.

Definition Rng_Forget_PreservesAllLimits : PreservesAllLimits Rng_Forget :=
  creates_limits_PreservesAllLimits Rng_Forget Sets_Complete
    Rng_Forget_creates_limits.

(* * * “Limits of rings are computed on underlying sets”, literally / * * “环的极限是在底层集合上计算的”，字面意思 *)

Section RngComputed.

Context {J : Category}.
Context (K : J ⟶ Rng).

Example rng_complete_carrier :
  rig_setoid (vertex_obj[Rng_Complete J K]) = Sets_limit_obj (Rng_Forget ◯ K)
  := eq_refl.

Example rng_complete_add
  (a b : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (rig_add (vertex_obj[Rng_Complete J K]) a b) d
    = rig_add (K d) (`1 a d) (`1 b d) := eq_refl.

Example rng_complete_zero (d : J) :
  `1 (rig_zero (vertex_obj[Rng_Complete J K])) d = rig_zero (K d) := eq_refl.

Example rng_complete_mul
  (a b : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (rig_mul (vertex_obj[Rng_Complete J K]) a b) d
    = rig_mul (K d) (`1 a d) (`1 b d) := eq_refl.

Example rng_complete_one (d : J) :
  `1 (rig_one (vertex_obj[Rng_Complete J K])) d = rig_one (K d) := eq_refl.

Example rng_complete_neg
  (a : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (ring_neg (vertex_obj[Rng_Complete J K]) a) d
    = ring_neg (K d) (`1 a d) := eq_refl.

Example rng_complete_leg (d : J) :
  rig_map (cone_leg (@limit_cone _ _ _ (Rng_Complete J K)) d)
    = Sets_limit_leg (Rng_Forget ◯ K) d := eq_refl.

End RngComputed.
