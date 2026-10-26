(*
   * * Cat has set-indexed products; StrictCat is small-complete under UIP

   Mac Lane, CWM 2nd ed., §V.1 Exercise 5 (book p. 112, [maclane:V.1:ex5]):
   the category of small categories has all small limits — products
   componentwise on objects and arrows, equalizers the evident
   subcategories, the general limit by products and equalizers.  Also
   Awodey §7.1 ([awodey:7.1:construction-cat-equalizer], the equalizer of
   two parallel functors as the subcategory on which they agree, and
   [awodey:7.1:remark-cat-complete]), Riehl §3.1 Exercise 3.1.x
   ([riehl:3.1:exx], the product of an indexed family of categories),
   §3.6 Proposition 3.6.6 ([riehl:3.6:prop6]) and §4.6 Corollary 4.6.15
   ([riehl:4.6:cor15]).

   WHAT IS DELIVERED, AND IN WHICH CATEGORY OF CATEGORIES.

   (A) [Cat_HasIndexedProducts : HasIndexedProducts Cat], UNCONDITIONAL.
   Its object field IS [PiCat], its projections ARE [PiCat_Proj] and
   its universal property IS [PiCat_ump] (Construction/Product/
   Indexed.v), consumed and not rebuilt; [PiCat_IsIndexedProduct] is
   the apex-pinned record beneath it.  The probe reads the class's
   object and projections back at [eq_refl].  This is Riehl's indexed
   clause and Awodey's “all small products”, in the tree's [Cat].

   (B) The equalizer of [F G : C ⟶ D] as a SUBCATEGORY, Awodey's and
   Riehl's construction verbatim: [EqSub F G : Subcategory C] has
   objects [{c & F c = G c}] (a LEIBNIZ equation of objects) and arrows
   those [f] with [hom_cast p p' (fmap[F] f) ≈ fmap[G] f] — the two
   images agree after transport along the two object equations —
   [EqCat F G := Sub C (EqSub F G)] and [EqIncl := Incl C (EqSub F G)].
   Its universal property is [Eq_IsEqualizer (uip : ObjUIP D) :
   @IsEqualizer StrictCat C D F G (EqCat F G) (EqIncl F G)] in
   Structure/Equalizer/Fork.v's apex-pinned record, and
   [StrictCat_HasEqualizers : (∀ C, ObjUIP C) → HasEqualizers
   StrictCat] its packaging in that file's class (the issue's
   “[HasEqualizers] form”).  [Eq_commutes] is a [:=] with no tactic —
   the fork equation's object component IS the equation each object
   carries and its arrow component IS the equation each arrow carries.

   (C) [StrictCat_HasIndexedProducts : (∀ C, ObjUIP C) → DepFunext →
   HasIndexedProducts StrictCat], on the SAME [PiCat]/[PiCat_Proj]/
   [PiCat_Pair], and [StrictCat_Complete := Complete_from_products_
   equalizers (StrictCat_HasIndexedProducts uip fe)
   (StrictCat_HasEqualizers uip)] — Mac Lane's “the general limit
   follows by the products-and-equalizers construction” is exactly one
   application of Structure/Limit/FromProducts.v's theorem (#416),
   consumed and not re-derived.

   THE ISSUE'S PINNED NAMES [Cat_HasEqualizers] AND [Cat_Complete] ARE NOT
   DELIVERED, AND THE REASON IS RIEHL'S OWN SHARPENING ON THE ISSUE.
   Instance/Cat.v gives [Cat] the hom-setoid [Functor_Setoid],
   natural isomorphism of functors, so this [Cat] is Ho(Cat) and an
   isomorphism in it is an EQUIVALENCE of categories.  The on-the-nose
   subcategory (B) is then not merely unproven but WRONG as an equalizer
   in [Cat], and that is a THEOREM here rather than a remark:
   [EqCat_not_Cat_equalizer] takes the parallel pair [1 ⇉ Chaotic bool]
   picking [true] and [false] — two functors that are EQUIVALENT in [Cat]
   ([ChaoticBool_points_equiv], every hom-set of the chaotic category
   being a singleton) — whose strict equalizer has NO objects
   ([EqCat_ChaoticBool_empty], by [discriminate]), while [Id[1]] is a
   competing fork in [Cat]; a mediator would be a functor out of [1] into
   the empty category.  Read it at its width: it refutes THIS apex at THIS
   pair.  Whether Ho(Cat) has equalizers, or is complete, is NEITHER
   PROVED NOR REFUTED here, and the iso-comma (“inserter”) replacement is
   UNATTEMPTED.  The issue's sharpening offers two ways out — “build it in
   Instance/StrictCat, or adopt the inserter and disclose” — and (B)-(C)
   take the first.  Instance/StrictCat.v's hom-setoid
   [Functor_StrictEq_Setoid] is Leibniz equality of the object actions
   together with transported agreement of the arrow actions, which is what
   a subcategory cut by [F c = G c] can satisfy.  So the answer to Mac
   Lane's exercise as this library can state it is: [StrictCat] is
   small-complete under two hypotheses, and [Cat] has small products
   outright.

   THE TWO HYPOTHESES, WHERE EACH IS SPENT, AND THAT BOTH ARE NECESSARY.
   [ObjUIP D] (Theory/Category/Monoid.v) enters the equalizer side at ONE
   lemma, [Eq_obj_eq]: two objects of [EqCat F G] over one object of [C]
   carry two proofs of [F c = G c], and the uniqueness clause
   [Eq_med_unique] must identify a competing mediator's object [(c; p)]
   with the canonical [(c; q)].  [Eq_commutes], [Eq_med] and [Eq_med_incl]
   take no hypothesis, and the five [Program] obligations of [EqSub]
   (two) and [Eq_med] (three) take none.  On the product side [DepFunext]
   (dependent function extensionality at the index and small object
   universes, declared here as a bare [Type]) and [ObjUIP] enter at ONE
   lemma, [pi_obj_eq]: two
   objects of [PiCat C] that agree pointwise must be identified, and the
   identification's projections must be the given pointwise equations;
   [PiCat_Pair_Proj_strict] takes neither.  Both hypotheses are NECESSARY
   for the uniqueness clauses as STATED — uniformly, for every parallel
   pair or family, with no hypothesis on the target:
   [Eq_uniqueness_forces_UIP] derives UIP for every type at the small
   object universe (the loops [p : x = x] at a point [x] of [Chaotic X]
   each name a functor [1 ⟶ EqCat (ChaoticPt x) (ChaoticPt x)] satisfying
   the triangle, so uniqueness identifies them; axiom-free through
   [inj_pair2_eq_dec] at the decidable index [poly_unit]) — this is
   Instance/Cat/Pullback.v's [FP_uniqueness_forces_UIP] one shape over —
   and [PiCat_uniqueness_forces_funext] derives dependent function
   extensionality (two pointwise-equal families [f g : ∀ i, P i] name two
   mediators [1 ⟶ PiCat (fun i => Chaotic (P i))] for one cone).  Scope
   both precisely: each is about the uniqueness clause OF THIS APEX, so
   neither refutes [HasEqualizers StrictCat] or [HasIndexedProducts
   StrictCat] with some other apex, and no such refutation is offered.
   The blanket [∀ C, ObjUIP C] is free for decidable object equality by
   Hedberg (Instance/Cat/Pullback.v's [ObjUIP_of_ObjDecEq]), and
   [DepFunext] has no axiom-free inhabitant in the tree; neither is
   registered as an [Instance].

   RELATION TO #337 (Instance/Cat/Pullback.v).  Same design decisions for
   the same reason: the universal property in [StrictCat], [ObjUIP] as the
   hypothesis, its necessity proved by a loop-space countermodel.  Pullbacks
   ARE a special case of (C) in principle (an equalizer of two composites
   out of a binary product), but no derivation of that file's
   [StrictCat_HasPullbacks] from [StrictCat_Complete] is built — it would
   go through [Structure/Pullback/Reduction.v]'s reduction, which wants a
   [Cartesian StrictCat] that does not exist — so the relation is recorded
   in prose only.  That module is NOT required — its own closure is 38
   modules excluding itself, and requiring it would take this file's from
   52 to 58 (measured with [coqdep -sort] over both files: 59 modules
   counting both) — and its [fmap_hom_cast] is RESTATED as
   [eq_fmap_hom_cast].

   RIEHL'S [ob]/[mor] LEAD-IN IS NOT TAKEN, AND WHY.  Riehl computes
   limits in [Cat] by representing objects and morphisms through [1] and
   [2].  Instance/Cat/Objects.v proves that over THIS [Cat] no objects
   functor into a target comparing object maps by Leibniz equality exists
   ([objects_not_functorial_over_Cat]), the same fact that blocks the
   on-the-nose equalizer; its [StrictCat_Objects] is the strict version.
   The limits here are computed DIRECTLY from the product and subcategory
   constructions and nothing goes through an [ob] or [mor] functor.

   AWODEY'S CAVEAT.  Coequalizers of categories are much harder to
   describe (already for posets), so the COLIMIT side is scoped out
   explicitly: nothing here is about coequalizers, coproducts (#338's
   [Cat_HasIndexedCoproducts]) or cocompleteness, and no colimit
   construction is attempted.

   UNIVERSES, MEASURED OFF BOTH BINDER AND BLOCK OVER ALL 58 CONSTANTS.
   [Cat_HasIndexedProducts@{i so sh u u0} : HasIndexedProducts@{i i i so u
   so} Cat@{u so u0 so sh}] — index universe [i], small categories at
   [Category@{so sh sh}] — with, among ten constraints, the bounds
   [i <= sh], [i <= so], [sh <= so], three strict bounds into the ambient
   levels ([so < u], [sh < u], [sh < u0]), four stdlib [Projections] caps,
   and NO equation.  The explicit binders are LOAD-BEARING: with the
   universe binders removed and the lambda binders left untyped, the two
   definitions minimize [i], [so] and [sh] to ONE level, [Cat]'s ambient
   level staying separate (measured; that form reads
   [Cat_HasIndexedProducts@{u u0} : HasIndexedProducts@{u u u u u0 u}
   Cat@{u0 u u0 u u}]).  The bound
   [sh <= so] — the small categories' hom universe at or below their
   object universe — is [PiCat_Proj]'s, MEASURED AND NOT ATTRIBUTED BY
   READING: at levels declared [so < sh], [PiCat C : Category@{so sh sh}],
   [PiCat C : obj[Cat@{_ sh _ so sh}]], the class applied up to the
   projections, and the BARE [PiCat_Proj C a] and [PiCat_ump R] are all
   accepted, while [PiCat_Proj C a : PiCat@{i so sh so sh} C ⟶ C a] is
   refused — the projection's declared [PiCat] instance identifies the
   index universe with the small hom universe and bounds the product's
   OBJECT universe below by it, so the projection's product cannot sit at
   object universe [so]; [PiCat_IsIndexedProduct] (at its argument) and the
   instance inherit it.  Annotating [Cat]'s hom universe separately, in
   the instance alone and in both the record and the instance, was tried
   and does not lift it (the first re-derives [so = m], the second keeps
   [sh <= so]); the donor is Construction/Product/Indexed.v's unannotated
   declaration, the same one Construction/Product/Limit.v records, and
   the bound is not claimed unavoidable.  Every constant of the equalizer
   development is over [C : Category@{u u0 u0}], [D : Category@{u1 u2
   u2}] — hom identified with proof IN THE BINDER, [Subcategory]'s and
   [Functor_StrictEq_Setoid]'s doing; [EqCat] carries NO block equation,
   [EqIncl] carries [u0 = u2] ([Sub]'s hom universe is [C]'s), and every
   constant stating a [StrictCat] equation ([Eq_commutes], [Eq_IsEqualizer],
   the whole Mediator section) carries [u = u1] and [u0 = u2] — [StrictCat]
   identifies the object AND hom universes of [C] and [D], its objects being
   [Category@{u u0 u0}] at ONE instance — the Mediator section adding
   [u = u3], [u0 = u4] for the competitor's category [Z].
   [StrictCat_HasEqualizers@{u u0 u1 u2 u3 u4}] carries no equation.
   [PiCat_ump_unique_strict] and [PiCat_IsIndexedProduct_strict] carry
   [u = u1] (index = small hom, [PiCat_Proj] again), and
   [StrictCat_HasIndexedProducts@{u u0 u1} : (∀ C : Category@{u u u},
   ObjUIP C) → DepFunext@{u u} → HasIndexedProducts@{u u u u u0 u}
   StrictCat@{u0 u u0 u u}] collapses index, object and hom to one level.
   THE SMALLNESS SIDE CONDITION is carried by [StrictCat_Complete@{u u0
   u1} : … → Complete@{u0 u0 u0 u}]: the diagram shapes range over
   [Category@{u0 u0 u0}], the same universe instance as the small
   categories, the collapse forced by [Complete_from_products_equalizers],
   whose index universe IS the ambient hom universe (the discipline of
   Instance/Sets/Complete.v's [Sets_Complete@{u u0} : Complete@{u u u
   u0}], and Structure/Complete.v's note).  The necessity theorems
   match the sufficiency statements' shapes: [Eq_uniqueness_forces_UIP@{o h
   u u0 u1 u2}] carries no equation, [PiCat_uniqueness_forces_funext@{i o h
   u u0}] carries [h = i].  [Chaotic@{o h p}] is free in all three levels
   (its homs are [poly_unit]; Instance/Discrete/Reconstruct.v's
   [Indiscrete] pins its homs to the stdlib [unit : Set] and would have
   confined the product half to [Set]-indexed families) and [DepFunext@{i
   o} : Type@{max(i+1,o+1)}] carries none.  ZERO word-bounded [Set] in
   the binder or block of any of the 58.

   COUNTS.  58/58 constants closed under the global context with ZERO
   [Axioms:] lines — 40 declaration heads (19 [Definition], 6 [Program
   Definition], 11 [Lemma], 3 [Theorem], 1 [Instance]) plus the 18
   [Program] obligations [Print Module] lists and a source sweep cannot
   see (5 [Next Obligation]s are written; [EqSub], [Eq_med], [ChaoticPt],
   [eq_loop_functor], [pi_point] and [ChaoticBool_points_equiv] generate
   18), all in the [make print-assumptions] gate FULLY QUALIFIED.  Ten
   [Defined] tokens, exactly THREE load-bearing by flipping each alone to
   [Qed] with both this file and the probe recompiled: [Chaotic], whose
   flip stops [ChaoticPt]'s [fobj] field in this file (an opaque
   [Chaotic X] no longer unfolds to [X]: “x has type X while it is
   expected to have type obj[Chaotic X]”); [Eq_IsEqualizer],
   whose flip stops the probe's readback of the mediator; and
   [StrictCat_HasEqualizers], whose flip stops the probe's readbacks of
   the chosen equalizer and its inclusion — the other seven flip with both
   files green and are kept [Defined] by the data convention.  Closure 52
   modules excluding self.
   Zero collisions over the 58 names after THREE were renamed before
   landing: [punit_eq] is Instance/Cat/Pullback.v's (same statement,
   a module deliberately not required), and [CB] matched the section
   variables of two files and a section-local [Notation CB]
   (Structure/Limit/Power/Adjunction.v) — not global collisions,
   but a two-letter global name in a gate that loads many modules into
   one scope is a hazard, hence [ChaoticBool]; [CBtrue]/[CBfalse]
   matched nothing and were renamed with it ([ChaoticBool_true]/
   [ChaoticBool_false]).  The [Program] obligations of the Necessity sections
   are closed by a LOCAL obligation tactic that must open [Proper] with
   [repeat intro] — with [intros] the [fmap_respects] obligation stays
   folded and [ChaoticPt] never enters the environment (measured, and the
   cause of one lost compile).

   Test/ProbeCatLimit414.v mirrors this file's [Require] list and carries
   10 refutation commands = 1 instrument check + 9 negatives of THREE
   kinds told apart by the error TEXT: 6 FORMABILITY (the [PiCat_Proj]
   donor with its five accepted controls, the two inheriting constants,
   [StrictCat_HasIndexedProducts] and [StrictCat_Complete] at an index
   universe strictly below the hom universe, and their donor
   [Complete_from_products_equalizers] at the same levels), 1 TYPING
   ([Eq_IsEqualizer] ascribed at [@IsEqualizer Cat …], a plain has-type
   mismatch with no “cannot unify” and no universe clause) and 2
   CONVERSION (the equalizer and product triangles as WHOLE functor
   records, each beside its two [eq_refl] data controls) — each stripped
   ONE AT A TIME in a copy of the whole file and compiled alone with its
   error read; guard coverage measured mechanically (48 identifiers inside
   a refutation command, 41 also outside, the seven exceptions
   exhaustively the refutation keyword itself, the three bound variables
   [Cu]/[HP]/[HE], the two names the refuted [Example]s declare and the
   instrument's absent name); rename-simulated 9/9 over the target
   constants the negatives name, each rename applied in THIS file only and
   every break landing on a [Check] or control line of the probe, none
   inside a refutation command.  [make todo] grows by 16 lines, ALL in the
   probe — its 10 refutation commands and 6 header lines that name the
   refutation keyword — and this file contributes ZERO.

   NOT DELIVERED.  [Cat_HasEqualizers], [Cat_Complete] and any equalizer
   or completeness statement about Ho(Cat), neither proved nor refuted; the
   inserter; any colimit; the pullback special case as a theorem; a
   [Cartesian StrictCat]; the [ob]/[mor] functors on [Cat]; an axiom-free
   inhabitant of [DepFunext] or of the blanket [ObjUIP]; naturality of any
   identification in the diagram; a comparison of [StrictCat_Complete]'s
   chosen limits with [Instance/Cat/Cartesian.v]'s binary products or
   [Instance/One.v]'s terminal category; and nothing registered as an
   [Instance] except [Cat_HasIndexedProducts], which carries no hypothesis
   and so may safely resolve. 

   --------
   * * Cat 有指数集产品；StrictCat 在 UIP 下是小完备的

   Mac Lane，《CWM》第2版，第V.1节 练习 5（书第112页，[maclane:V.1:ex5]）：
   小类的范畴拥有所有小极限——在对象和箭头上按分量构造的积，显而易见子范畴的等化子，通过积和等化子构造的一般极限。此外，Awodey §7.1（[awodey:7.1:construction-cat-equalizer]，两个平行函子等化子作为它们一致的子范畴，并且[awodey:7.1:remark-cat-complete]），Riehl §3.1 练习3.1.x（[riehl:3.1:exx]，一族范畴的指数积），§3.6 命题3.6.6（[riehl:3.6:prop6]）和 §4.6 推论4.6.15（[riehl:4.6:cor15]）。

   提供了什么，以及在哪个范畴的范畴中提供。(A) [Cat_HasIndexedProducts : HasIndexedProducts Cat]，无条件的。 它的对象域是 [PiCat]，它的投影是 [PiCat_Proj]， 它的通用性质是 [PiCat_ump]（构造/乘积/索引.v），已被使用且未重建；[PiCat_IsIndexedProduct] 是其下方的顶点固定记录。 探针在 [eq_refl] 读回类的对象和投影。 这是 Riehl 的索引条款和 Awodey 的“所有小乘积”，位于树的 [Cat]。（B） [F G : C ⟶ D] 作为子范畴的等化子，Awodey 的 和
   Riehl 的构造逐字表示：[EqSub F G : Subcategory C]
   物体[{c & F c = G c}]（LEIBNIZ对象方程）和箭头
   那些[f] [hom_cast p p' (fmap[F] f）≈fmap [G] f]——两个
   图像在传输后沿两个物体方程一致——
   [EqCat F G := Sub C (EqSub F G)] 和 [EqIncl := Incl C (EqSub F G)] 。其普适性质为 [Eq_IsEqualizer （uip ： ObjUIP D） ：
   @IsEqualizer StrictCat C D F G（EqCat F G）（EqIncl F G））
   Structure/Equalizer/Fork.v 的顶点固定记录，
   [StrictCat_HasEqualizers ：（∀ C，ObjUIP C）→ HasEqualizers
   StrictCat] 它在该文件类别中的打包（问题的
   “[HasEqualizers]形式”）。[Eq_commutes] 是一个没有策略的 [:=]——
   叉方程的对象分量就是每个对象携带的方程，
   它的箭头分量就是每个箭头携带的方程。

   (C) [StrictCat_HasIndexedProducts : (∀ C, ObjUIP C) → DepFunext →
   HasIndexedProducts StrictCat]，在相同的 [PiCat] / [PiCat_Proj] / [PiCat_Pair] 上，
   并且 [StrictCat_Complete := Complete_from_products_equalizers (StrictCat_HasIndexedProducts uip fe) (StrictCat_HasEqualizers uip)] — Mac Lane 的 “一般极限由乘积和等化子构造得出” 正是 Structure/Limit/FromProducts.v 定理（#416）的一次应用，被使用而未重新推导。该问题固定的名称 [Cat_HasEqualizers] 和 [Cat_Complete] 没有被提供，原因是 RIEHL 对该问题的自身锐化。实例/Cat.v 给出了 [Cat] 的同类集合 [Functor_Setoid]，函子之间的自然同构，因此这个 [Cat] 是 Ho(Cat)，在其中的同构是范畴的等价。所谓的恰到好处的子类别 (B) 在 [Cat] 中不仅没有被证明，而且作为均衡器是错误的，这在这里是一个定理，而不是一个注释：[EqCat_not_Cat_equalizer] 取并行对 [1 ⇉ Chaotic bool] ，选取 [true] 和 [false] —— 这是在 [Cat] 中等价的两个函子（[ChaoticBool_points_equiv]，每个混乱范畴的 Hom 集都是单点集）——其严格均衡器没有对象（[EqCat_ChaoticBool_empty]，由 [discriminate] 得出），而 [Id[1] 是在 [Cat] 中的一个竞争叉；中介将是从 [1] 到空范畴的一个函子。全面理解这一点：它反驳了该顶点在这对上的结论。Ho(Cat) 是否存在均衡器，或是否完备，在这里既未被证明也未被否定，而等距逗号（“插入器”）的替代方案未尝试。这个问题的强化提供了两种解决方法——“在 Instance/StrictCat 中构建它，或采用插入器并公开”——而 (B)-(C) 选择了第一种方法。Instance/StrictCat.v 的同态集合 [Functor_StrictEq_Setoid] 是对象作用的 Leibniz 等价以及箭头作用的传递一致性，这是由 [F c = G c] 切割的子范畴可以满足的条件。因此，根据该库的陈述，Mac Lane 的练习题的答案是：在两个假设下，[StrictCat] 是小完备的，并且 [Cat] 完全具有小积。两个假设，说明每个假设的消耗情况，以及两者都是必要的。[ObjUIP D] (Theory/Category/Monoid.v) 在 ONE 引理的等化器端入口，[Eq_obj_eq]：在一个 [C] 对象上，[EqCat F G] 的两个对象携带 [F c = G c] 的两个证明，并且唯一性条款 [Eq_med_unique] 必须将竞争中介者的对象 [(c; p)] 与规范的 [(c; q)] 识别。[Eq_commutes]、[Eq_med] 和 [Eq_med_incl] 不需要假设，[EqSub]（两个）和 [Eq_med]（三个）的五个 [Program] 义务也不需要假设。在乘积方面 [DepFunext]（在索引和小对象宇宙上的依赖函数外延性，这里作为一个裸 [Type] 声明）和 [ObjUIP] 在一个引理中出现，[pi_obj_eq]：[PiCat C] 的两个对象如果在各点上相同，则必须被认同，并且该认同的投影必须是给定的逐点方程；[PiCat_Pair_Proj_strict] 不接受任何。两个假设对于所陈述的唯一性条款都是必要的——对于每一个平行对或族都是统一的，对目标没有假设：[Eq_uniqueness_forces_UIP] 在小对象范畴的每种类型上推导出UIP（在 [Chaotic X] 的一点 [x] 上的循环 [p : x = x] 每个命名一个函子 [1 ⟶ EqCat (ChaoticPt x) (ChaoticPt x)] 满足三角形，因此唯一性识别它们；在可判定指标 [poly_unit] 上通过 [inj_pair2_eq_dec] 无公理）——这是 Instance/Cat/Pullback.v 的 [FP_uniqueness_forces_UIP] 单个形状上——并且 [PiCat_uniqueness_forces_funext] 推导出依赖函数的外延性（两个逐点相等的族 [f g : ∀ i, P i] 为一个圆锥命名两个中介 [1 ⟶ PiCat (fun i => Chaotic (P i))]）。范围
   两者都很精确：每个都涉及本 APEX 的唯一性条款，因此
   都不会用其他 apex 反驳 [HasEqualizers StrictCat] 或 [HasIndexedProducts
   StrictCat]，而且也没有提供这样的反驳。通过 Hedberg（Instance/Cat/Pullback.v 的 [ObjUIP_of_ObjDecEq]），[∀ C, ObjUIP C] 对可判定对象相等是自由的，并且
   [DepFunext] 在树中没有无公理的元素；两者都未被注册为 [Instance]。与 #337（Instance/Cat/Pullback.v）的关系。出于相同的原因作出了相同的设计决定：在 [StrictCat]、[ObjUIP] 中作为假设的范畴论泛性，其必要性通过环空间反例得到证明。Pullbacks 本质上是 (C) 的特例（两个二元积的复合函数的等化子），但没有从该文件的 [StrictCat_Complete] 推导出 [StrictCat_HasPullbacks] —— 这将通过 [Structure/Pullback/Reduction.v] 的化简进行，而它需要一个不存在的 [Cartesian StrictCat] —— 因此这种关系只在文字中记录。该模块并非必需——它自身的闭包是 38 个模块（不包括它自己），而要求它会将该文件的模块数从 52 增加到 58（以 [coqdep -sort] 衡量两个文件：总共计算两个的话是 59 个模块）——它的 [fmap_hom_cast] 被重新表述为 [eq_fmap_hom_cast]。RIEHL 的 [ob] / [mor] 引导没有被采用，原因是什么。Riehl 通过 [1] 和 [2] 表示对象和态射来计算 [Cat] 中的极限。Instance/Cat/Objects.v 证明在 THIS [Cat] 上不存在将对象函子映射到目标的对象映射（按 Leibniz 等式比较）（[objects_not_functorial_over_Cat]），这个事实同样阻止了精确等化器；它的 [StrictCat_Objects] 是严格版本。这里的极限是直接从积和子范畴构造中计算的，没有经过 [ob] 或 [mor] 函子。AWODEY 的警告。范畴的余等化子要难得多（即使对于偏序集也是如此），所以 COLIMIT 这一面被明确排除：这里没有关于余等化子、余积（#338 的 [Cat_HasIndexedCoproducts]）或余完备性的内容，也没有尝试任何余极限的构造。宇宙，测量了所有 58 个常数上的绑定器和块。[Cat_HasIndexedProducts@{i so sh u u0} : HasIndexedProducts@{i i i so u so} Cat@{u so u0 so sh}] — 指数宇宙 [i]，小类别在 [Category@{so sh sh}] — 在十个约束中，包括边界 [i <= sh]、[i <= so]、[sh <= so]，三个严格边界进入环境级别（[so < u]、[sh < u]、[sh < u0]），四个 stdlib [Projections] 上限，并且没有方程。显式绑定器是承重的：在移除宇宙绑定器并保留未类型化的 lambda 绑定器后，这两个定义将 [i]、[so] 和 [sh] 最小化到一个级别，[Cat] 的环境级别保持独立（已测量；该形式读取为 [Cat_HasIndexedProducts@{u u0} : HasIndexedProducts@{u u u u u0 u} Cat@{u0 u u0 u u}]）。绑定的
   [sh <= so] — 小范畴在其对象宇宙之上或之下的同构宇宙 — 是 [PiCat_Proj] 的，通过测量而非通过阅读赋值: 在声明的级别 [so < sh], [PiCat C : Category@{so sh sh}], [PiCat C : obj[Cat@{_ sh _ so sh}]]，类应用到投影为止，且 [PiCat_Proj C a] 和 [PiCat_ump R] 的基本形式都被接受，而 [PiCat_Proj C a : PiCat@{i so sh so sh} C ⟶ C a] 被拒绝 — 投影声明的 [PiCat] 实例将索引宇宙与小的同构宇宙对应，并将乘积的对象宇宙下界定为它，因此投影的乘积不能位于对象宇宙 [so]；[PiCat_IsIndexedProduct]（在其参数上）及其实例继承它。分别注释 [Cat] 的 hom 宇宙，在仅实例中以及在记录和实例中都尝试过，但都没有提升它（第一次会重新推导出 [so = m]，第二次保持 [sh <= so]）；捐赠者是 Construction/Product/Indexed.v 中未注释的声明，正是 Construction/Product/Limit.v 记录的那个，并且该界限并未被认为是不可避免的。均衡器开发的每一个常数都在 [C : Category@{u u0 u0}] 上，[D : Category@{u1 u2 u2}] — 同态与 BINDER 中的证明相对应，[Subcategory] 和 [Functor_StrictEq_Setoid] 在执行；[EqCat] 不包含块方程，[EqIncl] 包含 [u0 = u2]（[Sub] 的同态宇宙是 [C] 的），每个声明 [StrictCat] 方程（[Eq_commutes]、[Eq_IsEqualizer]、整个调解器部分）的常数都包含 [u = u1] 和 [u0 = u2] — [StrictCat] 标识 [C] 和 [D] 的对象及同态宇宙，其对象在单一实例中为 [Category@{u u0 u0}] — 调解器部分增加 [u = u3]、[u0 = u4] 给竞争者的类别 [Z]。[StrictCat_HasEqualizers@{u u0 u1 u2 u3 u4}] 不包含方程。[PiCat_ump_unique_strict] 和 [PiCat_IsIndexedProduct_strict] 承载 [u = u1]（索引 = small hom, [PiCat_Proj] 再次），并且 [StrictCat_HasIndexedProducts@{u u0 u1} : (∀ C : Category@{u u u}, ObjUIP C) → DepFunext@{u u} → HasIndexedProducts@{u u u u u0 u} StrictCat@{u0 u u0 u u}] 将索引、对象和态射合并到一个层次。小尺度的附加条件由 [StrictCat_Complete@{u u0 u1} : … → Complete@{u0 u0 u0 u}] 承载：图形的形状取自 [Category@{u0 u0 u0}]，与小型范畴相同的宇宙实例，由 [Complete_from_products_equalizers] 强制合并，其索引宇宙就是环境态射宇宙（Instance/Sets/Complete.v 中的 [Sets_Complete@{u u0} : Complete@{u u u u0}] 以及 Structure/Complete.v 的注释）。必要性定理与充分性陈述的形式相匹配：[Eq_uniqueness_forces_UIP@{o h u u0 u1 u2}] 没有携带方程，[PiCat_uniqueness_forces_funext@{i o h u u0}] 携带 [h = i]。[Chaotic@{o h p}] 在三个层次中都是自由的（其 hom 是 [poly_unit]；Instance/Discrete/Reconstruct.v 的 [Indiscrete] 将其 hom 固定为 stdlib 的 [unit : Set]，并且本来会将积的一半限制为 [Set] 索引的族），而 [DepFunext@{i o} : Type@{max(i+1,o+1)}] 没有携带任何。任何 58 个中的绑定器或代码块中都没有 ZERO 字长的 [Set]。计数。58/58 常量在全局上下文中关闭，带有零 [Axioms:] 行——40 个声明头（19 个 [Definition]，6 个 [程序定义]，11 个 [Lemma]，3 个 [Theorem]，1 个 [Instance]）加上 18 个 [Program] 义务 [Print Module] 列表，而且源扫描无法看到（5 个 [Next Obligation] 被写入；[EqSub]、[Eq_med]、[ChaoticPt]、[eq_loop_functor]、[pi_point] 和 [ChaoticBool_points_equiv] 生成 18 个），全部在 [make print-assumptions] 门完全限定。十个
   [Defined]  令牌，正好有三个通过单独翻转到
   [Qed]  承重，同时重新编译该文件和探针：  [Chaotic] ，其
   翻转会阻止  [ChaoticPt] 的  [fobj] 字段在该文件中（一个不透明的
   [Chaotic X] 不再展开为  [X] ：“x 的类型是 X，而期望类型是 obj [Chaotic X]”）；  [Eq_IsEqualizer] ，
   其翻转会阻止探针读取中介者的读回；以及
   [StrictCat_HasEqualizers] ，其翻转会阻止探针读取所选均衡器及其包含 — 其他七个在两个文件中翻转都是绿色，并根据数据约定保留  [Defined]。闭包 52
   个模块，不包括自身。在三个重命名前的 58 个名称中没有发生冲突：[punit_eq] 是 Instance/Cat/Pullback.v 的（相同的语句，一个故意不需要的模块），而 [CB] 与两个文件的段变量以及一个段内局部的 [Notation CB]（Structure/Limit/Power/Adjunction.v）匹配——不是全局冲突，但是在将多个模块加载到一个作用域的门中使用两个字母的全局名称是一个隐患，因此 [ChaoticBool]；[CBtrue] / [CBfalse] 没有匹配任何内容，并与它（[ChaoticBool_true] / [ChaoticBool_false]）一起被重命名。必要性部分的 [Program] 义务由本地义务策略关闭，该策略必须使用 [repeat intro] 打开 [Proper] —— 在 [intros] 的情况下，[fmap_respects] 义务保持折叠状态，[ChaoticPt] 从未进入环境（已测量，并且是一次编译失败的原因）。Test/ProbeCatLimit414.v 反映了此文件的 [Require] 列表，并包含 10 个反驳命令 = 1 个仪器检查 + 9 个三种类型的否定，它们通过错误文本区分：6 个可形成性（[PiCat_Proj] 捐赠者及其五个已接受的控制，两个继承的常数 [StrictCat_HasIndexedProducts] 和 [StrictCat_Complete] 位于严格低于同种宇宙的索引宇宙，以及它们的捐赠者 [Complete_from_products_equalizers] 在相同级别），1 个类型（[Eq_IsEqualizer] 在 [@IsEqualizer Cat …] 上指定，一个普通的类型不匹配，没有“无法统一”和没有宇宙条款）和 2 个转换（作为整体函子记录的等化器和乘积三角形，每个旁边有两个 [eq_refl] 数据控制）— 每个在整个文件的副本中一次剥离，并单独编译其错误读取；守卫覆盖率机械测量（48 个相同在反驳命令内部的限定符，41 也在外部，七个例外详尽地穷尽了反驳关键字本身，三个绑定变量 [Cu] / [HP] / [HE]，两个被反驳的 [Example] 所声明的名称以及工具缺失的名称）；在目标常量上进行 9/9 的重命名模拟，否定的名称，每个重命名仅在此文件中应用，并且每一次中断都落在 [Check] 或探针的控制行上，没有在反驳命令内部。[make todo] 增加了 16 行，全部在探针中——它的 10 条反驳命令和 6 行头部用来命名反驳关键字——而这个文件没有贡献任何内容。

   未交付。[Cat_HasEqualizers]，[Cat_Complete] 以及关于 Ho(Cat) 的任何等化器或完整性声明，既未证明也未反驳；插入器；任何余极限；作为定理的拉回特例；[Cartesian StrictCat]；[ob] / [mor] 在 [Cat] 上的函子；[DepFunext] 或通用 [ObjUIP] 的无公理元素；图中任何认同的自然性；比较 [StrictCat_Complete] 所选的极限与 [Instance/Cat/Cartesian.v] 的二元积或 [Instance/One.v] 的终对象；以及除了 [Cat_HasIndexedProducts]（它没有假设，因此可以安全解决）之外没有注册为 [Instance] 的任何内容。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Category.Monoid.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Product.Indexed.
Require Import Category.Construction.Comma.Diagram.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.One.

From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(** ** Cat has set-indexed products / ** 类具有集合指数的乘积 *)

(*
 The explicit universe binders are load-bearing: written bare, the two
 definitions minimize the index universe, the small categories' object
 universe and their hom universe to ONE level (measured; see the header). 

 --------
 显式宇宙绑定器是承重的：直接写出时，这两个定义将索引宇宙、小范畴的对象宇宙及其同态宇宙最小化到一个级别（可测量；见标题）。
*)
Definition PiCat_IsIndexedProduct@{i so sh +} {I : Type@{i}}
  (C : I → Category@{so sh sh}) :
  @IsIndexedProduct Cat I C (PiCat C) (PiCat_Proj C) :=
  @Build_IsIndexedProduct Cat I C (PiCat C) (PiCat_Proj C)
    (fun D R => PiCat_ump R).

#[export]
Instance Cat_HasIndexedProducts@{i so sh +} : @HasIndexedProducts Cat :=
  @Build_HasIndexedProducts Cat
    (fun (A : Type@{i}) (C : A → Category@{so sh sh}) => PiCat C)
    (fun (A : Type@{i}) (C : A → Category@{so sh sh}) a => PiCat_Proj C a)
    (fun (A : Type@{i}) (C : A → Category@{so sh sh}) =>
       PiCat_IsIndexedProduct C).

(** ** A small cast kit / ** 一个小型铸造工具包 *)

(*
 Functors commute with [hom_cast], the endpoints being relabelled by
 [f_equal] of the object map.  Restated from Instance/Cat/Pullback.v's
 [fmap_hom_cast] rather than requiring that module. 

 --------
 函子与 [hom_cast] 交换，端点由 [f_equal] 对象映射重新标记。从 Instance/Cat/Pullback.v 的 [fmap_hom_cast] 重述，而不是要求该模块。
*)
Lemma eq_fmap_hom_cast {X Y : Category} (P : X ⟶ Y) {a b a' b' : X}
      (ea : a = a') (eb : b = b') (f : a ~> b) :
  fmap[P] (hom_cast ea eb f)
    ≈ hom_cast (f_equal (fobj[P]) ea) (f_equal (fobj[P]) eb) (fmap[P] f).
Proof. destruct ea, eb; reflexivity. Qed.

(* A [hom_cast] in a product category, read at one index. / 在一个产品类别中，一个 [hom_cast]，在一个索引处读取。 *)
Lemma hom_cast_pi {I : Type} (C : I → Category) {a b a' b' : PiCat C}
      (ea : a = a') (eb : b = b') (η : a ~> b) (i : I) :
  hom_cast ea eb η i
    = hom_cast (f_equal (fun g => g i) ea) (f_equal (fun g => g i) eb) (η i).
Proof. destruct ea, eb; reflexivity. Qed.

(* A Leibniz equality of morphisms followed by a setoid equation. / 一个紧随集合等价关系的莱布尼茨态射等式。 *)
Definition eq_then_equiv {X : Category} {a b : X} {p q r : a ~> b}
  (e : p = q) (h : q ≈ r) : p ≈ r :=
  match e in _ = q' return q' ≈ r → p ≈ r with eq_refl => fun h => h end h.

(** ** Equalizers in StrictCat / ** StrictCat 中的均衡器 *)

Section Equalizer.

Context {C D : Category}.
Context (F G : C ⟶ D).

#[local] Obligation Tactic := idtac.

(*
 The subcategory of C on the objects where F and G agree, and the arrows
 on which they agree up to the cast along those object agreements. 

 --------
 C 的子范畴，在 F 和 G 相同的对象上，以及在这些对象一致下，它们在箭头上相同的部分。
*)
Program Definition EqSub : Subcategory C := {|
  sobj := fun c => F c = G c;
  shom := fun c c' (p : F c = G c) (p' : F c' = G c') (f : c ~> c') =>
            hom_cast p p' (fmap[F] f) ≈ fmap[G] f
|}.
Next Obligation.
  intros x y z ox oy oz f g Hf Hg; simpl in *.
  rewrite !fmap_comp.
  rewrite <- (hom_cast_comp ox oy oz).
  now rewrite Hf, Hg.
Qed.
Next Obligation.
  intros x ox; simpl.
  rewrite !fmap_id.
  apply hom_cast_id.
Qed.

Definition EqCat : Category := Sub C EqSub.
Definition EqIncl : EqCat ⟶ C := Incl C EqSub.

(*
 The inclusion equalizes F and G, strictly: the object component IS the
 membership equality each object carries, the morphism component IS the
 equation each morphism carries. 

 --------
 包含使 F 和 G 相等，严格来说：对象部分就是每个对象所具有的成员资格等式，态射部分就是每个态射所具有的方程。
*)
Definition Eq_commutes :
  F ∘[StrictCat] EqIncl ≈[StrictCat] G ∘[StrictCat] EqIncl :=
  @Build_strict_eq EqCat D (F ◯ EqIncl) (G ◯ EqIncl)
                   (fun x : EqCat => `2 x)
                   (fun (x y : EqCat) (f : x ~> y) => `2 f).

(*
 Two objects of the equalizer with the same underlying object are equal --
 PROVIDED the two membership proofs can be identified, which is [ObjUIP D]. 

 --------
 具有相同基础对象的均衡器的两个对象是相等的——前提是两个成员证明可以被识别，即 [ObjUIP D]。
*)
Lemma Eq_obj_eq (uip : ObjUIP D) (x y : EqCat) (e : `1 x = `1 y) :
  { E : x = y & f_equal (fobj[EqIncl]) E = e }.
Proof.
  destruct x as [a p], y as [a' p']; simpl in *.
  destruct e, (uip _ _ p p').
  exists eq_refl; reflexivity.
Defined.

Section Mediator.

Context {Z : Category} (h : Z ⟶ C).
Context (Hh : F ∘[StrictCat] h ≈[StrictCat] G ∘[StrictCat] h).

Program Definition Eq_med : Z ⟶ EqCat := {|
  fobj := fun z => (h z; `1 Hh z);
  fmap := fun x y f => (fmap[h] f; strict_fmap_cast Hh f)
|}.
Next Obligation. intros x y f g Hfg; simpl; now rewrite Hfg. Qed.
Next Obligation. intros x; simpl; apply fmap_id. Qed.
Next Obligation. intros x y z f g; simpl; apply fmap_comp. Qed.

Definition Eq_med_incl : EqIncl ∘[StrictCat] Eq_med ≈[StrictCat] h.
Proof.
  refine (@Build_strict_eq Z C (EqIncl ◯ Eq_med) h (fun _ => eq_refl) _).
  intros x y f; reflexivity.
Defined.

(*
 [EqCat]'s hom-setoid compares underlying morphisms, so an equation between
 the inclusion's images IS an equation in [EqCat]; the proof is the
 identity. 

 --------
 [EqCat] 的同质集合比较基础态射，因此包含映射的像之间的方程在 [EqCat] 中是一个方程；证明就是恒等式。
*)
Definition EqCat_equiv_of_incl {x y : EqCat} (f g : x ~> y)
  (H : fmap[EqIncl] f ≈ fmap[EqIncl] g) : f ≈ g := H.

Lemma Eq_med_unique (uip : ObjUIP D) (v : Z ⟶ EqCat)
      (Hv : EqIncl ∘[StrictCat] v ≈[StrictCat] h) :
  v ≈[StrictCat] Eq_med.
Proof.
  refine (@Build_strict_eq Z EqCat v Eq_med
            (fun x => `1 (Eq_obj_eq uip (v x) (Eq_med x) (`1 Hv x))) _).
  intros x y f.
  pose proof (`2 (Eq_obj_eq uip (v x) (Eq_med x) (`1 Hv x))) as Px.
  pose proof (`2 (Eq_obj_eq uip (v y) (Eq_med y) (`1 Hv y))) as Py.
  apply EqCat_equiv_of_incl.
  etransitivity; [ exact (eq_fmap_hom_cast EqIncl _ _ (fmap[v] f)) | ].
  rewrite Px, Py.
  exact (strict_fmap_cast Hv f).
Qed.

End Mediator.

Definition Eq_IsEqualizer (uip : ObjUIP D) :
  @IsEqualizer StrictCat C D F G EqCat EqIncl.
Proof.
  unshelve refine {| fork_eq := Eq_commutes |}.
  intros Z h Hh.
  unshelve refine {| unique_obj := Eq_med h Hh |}.
  - exact (Eq_med_incl h Hh).
  - intros v Hv; symmetry.
    exact (Eq_med_unique h Hh uip v Hv).
Defined.

End Equalizer.

Definition StrictCat_HasEqualizers (uip : ∀ C : Category, ObjUIP C) :
  HasEqualizers StrictCat.
Proof.
  constructor; intros C D F G.
  exists (EqCat F G), (EqIncl F G).
  exact (Eq_IsEqualizer F G (uip D)).
Defined.

(** ** Indexed products in StrictCat / ** 在 StrictCat 中编入索引的产品 *)

(* Dependent function extensionality, at one pair of universes. / 依赖函数外延性，在一对宇宙上。 *)
Definition DepFunext@{i o} : Type@{max(i+1,o+1)} :=
  ∀ (I : Type@{i}) (P : I → Type@{o}) (f g : ∀ i : I, P i),
    (∀ i : I, f i = g i) → f = g.

Section StrictProduct.

Context {I : Type} (C : I → Category).

(*
 The triangle holds on the nose: projecting the pairing IS the component,
 on objects and on arrows. 

 --------
 三角形固定在鼻子上：投射配对就是组件，作用在对象和箭头上。
*)
Definition PiCat_Pair_Proj_strict {D : Category} (R : ∀ i : I, D ⟶ C i)
  (i : I) : PiCat_Proj C i ∘[StrictCat] PiCat_Pair R ≈[StrictCat] R i.
Proof.
  refine (@Build_strict_eq D (C i) (PiCat_Proj C i ◯ PiCat_Pair R) (R i)
            (fun _ => eq_refl) _).
  intros x y f; reflexivity.
Defined.

(*
 Two objects of the product agreeing at every index are equal -- PROVIDED
 object families are compared extensionally -- and the equality returns its
 component projections, so that a cast along it can be rewritten into the
 component casts, which is where UIP on each component's objects enters. 

 --------
 在每个索引上都相等的两个积的对象是相等的——前提是对象族按扩展方式进行比较——并且相等返回其分量投影，因此沿着它的类型转换可以重写为分量转换，这就是每个分量对象的 UIP 所起作用的地方。
*)
Lemma pi_obj_eq
  (uip : ∀ i : I, ObjUIP (C i))
  (fe : ∀ (f g : ∀ i : I, C i), (∀ i, f i = g i) → f = g)
  (a b : PiCat C) (e : ∀ i : I, a i = b i) :
  { E : a = b & ∀ i : I, f_equal (fun g => g i) E = e i }.
Proof.
  exists (fe a b e).
  intro i; apply uip.
Defined.

(* A cast in the product, read at one index, once the two whole-family equalities are known to project to given component equalities. / 产品中的一个类型转换，在一个索引处读取，一旦已知两个全家族等式投影到给定的分量等式。 *)
Lemma hom_cast_pi_ext {a b a' b' : PiCat C} (ea : a = a') (eb : b = b')
  (e1 : ∀ i : I, a i = a' i) (e2 : ∀ i : I, b i = b' i)
  (H1 : ∀ i : I, f_equal (fun g => g i) ea = e1 i)
  (H2 : ∀ i : I, f_equal (fun g => g i) eb = e2 i)
  (η : a ~> b) (i : I) :
  hom_cast ea eb η i = hom_cast (e1 i) (e2 i) (η i).
Proof. rewrite hom_cast_pi, H1, H2; reflexivity. Qed.

(*
 Uniqueness needs two principles a set-theoretic Cat has for free: the
 object families must be compared extensionally, and the two proofs of each
 component equation must be identified.  The proof is one [exact]: the cast
 along the family equality is rewritten into the component casts by
 [hom_cast_pi_ext] and the component agreement is [HP i]'s. 

 --------
 唯一性需要两个原理，而集合论范畴天然拥有这两个原理：对象族必须进行外延比较，并且每个分量方程的两个证明必须被识别。证明如下：[exact]：沿着族等式的类型转换通过[hom_cast_pi_ext]重写为分量类型转换，而分量一致性则归于[HP i]。
*)
Lemma PiCat_ump_unique_strict
  (uip : ∀ i : I, ObjUIP (C i))
  (fe : ∀ (f g : ∀ i : I, C i), (∀ i, f i = g i) → f = g)
  {D : Category} (R : ∀ i : I, D ⟶ C i) (H : D ⟶ PiCat C)
  (HP : ∀ i : I, PiCat_Proj C i ∘[StrictCat] H ≈[StrictCat] R i) :
  H ≈[StrictCat] PiCat_Pair R.
Proof.
  refine (@Build_strict_eq D (PiCat C) H (PiCat_Pair R)
            (fun d => `1 (pi_obj_eq uip fe (H d) (fun i => R i d)
                                    (fun i => `1 (HP i) d))) _).
  intros x y f i.
  exact (eq_then_equiv
           (hom_cast_pi_ext _ _ _ _
              (`2 (pi_obj_eq uip fe (H x) (fun i => R i x)
                              (fun i => `1 (HP i) x)))
              (`2 (pi_obj_eq uip fe (H y) (fun i => R i y)
                              (fun i => `1 (HP i) y)))
              (fmap[H] f) i)
           (strict_fmap_cast (HP i) f)).
Qed.

Definition PiCat_IsIndexedProduct_strict
  (uip : ∀ i : I, ObjUIP (C i))
  (fe : ∀ (f g : ∀ i : I, C i), (∀ i, f i = g i) → f = g) :
  @IsIndexedProduct StrictCat I C (PiCat C) (PiCat_Proj C).
Proof.
  constructor; intros D R.
  unshelve refine {| unique_obj := PiCat_Pair R |}.
  - exact (PiCat_Pair_Proj_strict R).
  - intros H HP; symmetry.
    exact (PiCat_ump_unique_strict uip fe R H HP).
Defined.

End StrictProduct.

Definition StrictCat_HasIndexedProducts
  (uip : ∀ C : Category, ObjUIP C) (fe : DepFunext) :
  HasIndexedProducts StrictCat :=
  @Build_HasIndexedProducts StrictCat
    (fun A C => PiCat C)
    (fun A C a => PiCat_Proj C a)
    (fun A C => PiCat_IsIndexedProduct_strict C (fun i => uip (C i))
                  (fe A (fun i => obj[C i]))).

(** ** StrictCat is small-complete / ** StrictCat 是小完备的 *)

Definition StrictCat_Complete
  (uip : ∀ C : Category, ObjUIP C) (fe : DepFunext) : @Complete StrictCat :=
  Complete_from_products_equalizers
    (StrictCat_HasIndexedProducts uip fe) (StrictCat_HasEqualizers uip).

(* * ** The two hypotheses are necessary / * ** 这两个假设是必要的 *)

(*
 The chaotic category on a type: every hom-set is the polymorphic unit.
 Instance/Discrete/Reconstruct.v's [Indiscrete] pins its homs to the stdlib
 [unit : Set], which would confine the product half below to [Set]-indexed
 families; this one is [_1] with an arbitrary object type. 

 --------
 一种类型上的混乱范畴：每个 Hom 集都是多态单位。
 Instance/Discrete/Reconstruct.v 的 [Indiscrete] 将其 Hom 定义固定在 stdlib [unit : Set] 上，这会将下面的乘积部分限制在 [Set] 索引的族中；这个是 [_1]，具有任意对象类型。
*)
Definition Chaotic@{o h p} (X : Type@{o}) : Category@{o h p}.
Proof.
  unshelve refine {|
    obj     := X;
    hom     := fun _ _ => poly_unit@{h};
    homset  := Morphism_equality@{o h p};
    id      := fun _ => ttt;
    compose := fun _ _ _ _ _ => ttt
  |}.
  all: repeat intro; simpl;
    first [ reflexivity | match goal with |- ?a = ?b => now destruct a, b end ].
Defined.

Lemma chaotic_unit_eq (u : poly_unit) : ttt = u.
Proof. now destruct u. Defined.

Definition chaotic_unit_dec (a b : poly_unit) : {a = b} + {a <> b}.
Proof. destruct a, b; now left. Defined.

Section NecessityUIP.

(* One ambient [StrictCat]: its small categories are [Category@{o h h}]. / 一个环境 [StrictCat]：它的小类别是 [Category@{o h h}]。 *)
Universe o h.

#[local] Obligation Tactic :=
  repeat intro; simpl;
  first [ reflexivity | match goal with |- ?a = ?b => now destruct a, b end ].

(* The functor out of the terminal category picking a point. / 从终端范畴取一个点的函子。 *)
Program Definition ChaoticPt {X : Type@{o}} (x : X) :
  _1@{o h h} ⟶ Chaotic@{o h h} X := {|
  fobj := fun _ => x;
  fmap := fun _ _ _ => ttt
|}.

(*
 Each loop [p : x = x] names a functor into the equalizer of [ChaoticPt x]
 with itself, and every such functor satisfies the triangle. 

 --------
 每个循环 [p : x = x] 都命名了一个函子到 [ChaoticPt x] 与其自身的等化器中，并且每个这样的函子都满足三角形。
*)
Program Definition eq_loop_functor {X : Type@{o}} {x : X} (p : x = x) :
  _1@{o h h} ⟶ EqCat (ChaoticPt x) (ChaoticPt x) := {|
  fobj := fun _ => (ttt; p);
  fmap := fun _ _ _ => (ttt; _)
|}.

Lemma eq_loop_functor_incl {X : Type@{o}} {x : X} (p : x = x) :
  EqIncl (ChaoticPt x) (ChaoticPt x) ∘[StrictCat] eq_loop_functor p
    ≈[StrictCat] Id[_1@{o h h}].
Proof.
  refine (@Build_strict_eq _1 _1
            (EqIncl (ChaoticPt x) (ChaoticPt x) ◯ eq_loop_functor p) Id[_1]
            (fun o => chaotic_unit_eq o) _).
  intros a b k; simpl.
  match goal with |- ?u = ?v => now destruct u, v end.
Qed.

(*
 Deriving the uniqueness clause of the strict equalizer UNIFORMLY -- for
 every parallel pair, with no hypothesis on the target -- entails UIP for
 every type at the small object universe.  So [ObjUIP D] in
 [Eq_IsEqualizer] is what the statement costs; this is
 Instance/Cat/Pullback.v's [FP_uniqueness_forces_UIP] one shape over. 

 --------
 统一地推导严格等化器的唯一性条款——对于每一个平行对，不对目标作任何假设——意味着小对象宇宙中每个类型都具有 UIP。因此 [ObjUIP D] 在 [Eq_IsEqualizer] 中就是该声明的代价；这是 Instance/Cat/Pullback.v 的 [FP_uniqueness_forces_UIP]，向上一个形状。
*)
Theorem Eq_uniqueness_forces_UIP
  (K : ∀ (C D : Category@{o h h}) (F G : C ⟶ D),
         @IsEqualizer StrictCat C D F G (EqCat F G) (EqIncl F G)) :
  ∀ (X : Type@{o}) (x y : X) (p q : x = y), p = q.
Proof.
  assert (loops : ∀ (X : Type@{o}) (x : X) (p : x = x), p = eq_refl).
  { intros X x p.
    pose proof (eq_desc (K _1 (Chaotic X) (ChaoticPt x) (ChaoticPt x))
                  Id[_1] (reflexivity _)) as U.
    pose proof (uniqueness U (eq_loop_functor p) (eq_loop_functor_incl p))
      as Up.
    pose proof (uniqueness U (eq_loop_functor (@eq_refl _ x))
                  (eq_loop_functor_incl eq_refl)) as Ur.
    assert (Hpq : eq_loop_functor p ≈[StrictCat] eq_loop_functor (@eq_refl _ x))
      by (rewrite <- Up; exact Ur).
    exact (inj_pair2_eq_dec _ chaotic_unit_dec _ _ _ _ (`1 Hpq ttt)). }
  intros X x y p q; destruct p; symmetry; apply loops.
Qed.

End NecessityUIP.

Section NecessityFunext.

(* The same ambient, with the index types of its products at [i]. / 相同的环境，其产品的索引类型在 [i]。 *)
Universe i o h.
Constraint i <= o.
Constraint i <= h.

#[local] Obligation Tactic :=
  repeat intro; simpl;
  first [ reflexivity | match goal with |- ?a = ?b => now destruct a, b end ].

(*
 A family [f : ∀ i, P i] names a functor from the terminal category into
 the product of the chaotic categories on the [P i]. 

 --------
 一个家庭 [f : ∀ i, P i] 从终端范畴到 [P i] 上混乱范畴的积中的函子。
*)
Program Definition pi_point {I : Type@{i}} {P : I → Type@{o}} (f : ∀ i, P i) :
  _1@{o h h} ⟶ PiCat (fun i => Chaotic@{o h h} (P i)) := {|
  fobj := fun _ => f;
  fmap := fun _ _ _ i => ttt
|}.

Lemma pi_point_proj {I : Type@{i}} {P : I → Type@{o}} (f g : ∀ i, P i)
  (e : ∀ i, f i = g i) (i : I) :
  PiCat_Proj (fun i => Chaotic@{o h h} (P i)) i ∘[StrictCat] pi_point f
    ≈[StrictCat] ChaoticPt (g i).
Proof.
  refine (@Build_strict_eq _1 (Chaotic (P i))
            (PiCat_Proj (fun i => Chaotic (P i)) i ◯ pi_point f)
            (ChaoticPt (g i)) (fun _ => e i) _).
  intros a b k; simpl.
  match goal with |- ?u = ?v => now destruct u, v end.
Qed.

(*
 Deriving the uniqueness clause of the strict indexed product UNIFORMLY
 entails dependent function extensionality at the index and small object
 universes: two pointwise-equal families name two mediators for one cone,
 and uniqueness identifies them. 

 --------
 导出严格索引积的唯一性条款统一地意味着索引处的依赖函数外延性和小对象宇宙：两个点对点相等的族为一个圆锥命名两个中介，而唯一性则将它们识别出来。
*)
Theorem PiCat_uniqueness_forces_funext
  (K : ∀ (I : Type@{i}) (C : I → Category@{o h h}),
         @IsIndexedProduct StrictCat I C (PiCat C) (PiCat_Proj C)) :
  ∀ (I : Type@{i}) (P : I → Type@{o}) (f g : ∀ i, P i),
    (∀ i, f i = g i) → f = g.
Proof.
  intros I P f g e.
  pose proof (iprod_desc (K I (fun i => Chaotic (P i)))
                (fun i => ChaoticPt (g i))) as U.
  pose proof (uniqueness U (pi_point f) (pi_point_proj f g e)) as Uf.
  pose proof (uniqueness U (pi_point g) (pi_point_proj g g (fun _ => eq_refl)))
    as Ug.
  assert (Hfg : pi_point f ≈[StrictCat] pi_point g)
    by (rewrite <- Uf; exact Ug).
  exact (`1 Hfg ttt).
Qed.

End NecessityFunext.

(* * ** The weak ambient: the strict equalizer is not an equalizer in Cat / * ** 弱环境：严格的均衡器在 Cat 中不是均衡器 *)

Section WeakAmbient.

#[local] Obligation Tactic :=
  intros; simpl;
  first [ reflexivity | match goal with |- ?a = ?b => now destruct a, b end ].

Definition ChaoticBool : Category := Chaotic bool.
Definition ChaoticBool_true  : _1 ⟶ ChaoticBool := ChaoticPt true.
Definition ChaoticBool_false : _1 ⟶ ChaoticBool := ChaoticPt false.

(*
 In Ho(Cat) the two points are the SAME morphism: every hom-set of the
 chaotic category is a singleton, so the family of its unique arrows is a
 natural isomorphism. 

 --------
 在 Ho(Cat) 中，这两个点是相同的态射：混乱范畴的每个 Hom-集都是单元素的，因此它独特箭头的族是一个自然同构。
*)
Program Definition ChaoticBool_points_equiv :
  ChaoticBool_true ≈[Cat] ChaoticBool_false :=
  (fun _ => {| to := ttt; from := ttt |}; _).

Lemma EqCat_ChaoticBool_empty :
  obj[EqCat ChaoticBool_true ChaoticBool_false] → False.
Proof. intros [o e]; simpl in e; discriminate e. Qed.

(*
 The strict equalizer of two functors that are equivalent in [Cat] is
 empty, while the identity of [1] is a competing fork there; so it is not
 an equalizer in [Cat].  Read narrowly: this refutes THIS apex at THIS pair,
 and says nothing about whether [Cat] has equalizers. 

 --------
 在  [Cat]  中两个等价函子严格的等化子是空的，而在  [1]  中的恒等则是那里的竞争分叉；所以它在  [Cat]  中不是等化子。狭义地说：这驳斥了 THIS apex 在 THIS pair 上的情况，并不说明  [Cat]  是否有等化子。
*)
Theorem EqCat_not_Cat_equalizer :
  @IsEqualizer Cat _1 ChaoticBool ChaoticBool_true ChaoticBool_false
    (EqCat ChaoticBool_true ChaoticBool_false)
    (EqIncl ChaoticBool_true ChaoticBool_false)
  → False.
Proof.
  intros K.
  assert (Hc : ChaoticBool_true ∘[Cat] Id[_1]
                 ≈[Cat] ChaoticBool_false ∘[Cat] Id[_1])
    by (rewrite ChaoticBool_points_equiv; reflexivity).
  exact (EqCat_ChaoticBool_empty (fobj[unique_obj (eq_desc K Id[_1] Hc)] ttt)).
Qed.

End WeakAmbient.
