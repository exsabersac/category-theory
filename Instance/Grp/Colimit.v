Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Disjoint.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Bicartesian.Matrix.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Adjunction.Diagonal.Coproduct.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.Grp.Limit.
Require Import Category.Instance.Grp.FreeAFT.
Require Import Category.Instance.Grp.Pushout.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Quotient.Colimit.

Generalizable All Variables.

(* * * Colimits of groups, from the adjoint functor theorem / * * 群的余极限，来自伴随函子定理 *)

(*
 nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
 nLab:      https://ncatlab.org/nlab/show/free+product
 nLab:      https://ncatlab.org/nlab/show/Grp
 Wikipedia: https://en.wikipedia.org/wiki/Free_product
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_groups

 Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
 §V.7 Exercise 1 (book p. 128, PDF p. 137) asks that the free product of
 two groups be obtained from the adjoint functor theorem, and that its
 two injections be shown monic with images meeting in the trivial
 subgroup; §IX.1 Exercise 1 (book p. 214, PDF p. 221) asks that [Grp] be
 shown to have ALL small colimits by the same theorem.  The theorem is
 Freyd's general adjoint functor theorem, §V.6 Theorem 2, which the tree
 carries as Adjunction/GAFT.v's [GAFT]; Instance/Grp/FreeAFT.v applies
 it at the forgetful functor, as §V.6 does on book p. 123 (the page the
 in-repo catalog, doc/plan/books/maclane/inventory/V.json, gives for
 its entry maclane:V.6:construction-free-group).  Wikipedia's
 "Free product" gives the element-level picture this file never builds:
 reduced words alternating between the two factors.

 ** THE ISSUE'S SURVEY IS PARTLY STALE, MEASURED

 Issue #450 says the free product of groups is "prose only" and that
 there is "no [Grp]".  Neither held when this file was written.  [Grp]
 is Instance/Grp.v (#255), and Instance/Grp/Pushout.v already builds the
 free product by generators and relations -- [Grp_free_product], the
 exported [Grp_Cocartesian] and [Grp_free_product_injections_Monic] --
 as an amalgam along constant legs, with no adjoint functor theorem in
 sight.  What WAS absent, measured at the parent commit (e139ecfb) by
 [grep -rn --include='*.v'] over the whole tree: [GAFT] applied at a
 diagonal functor (pattern ['GAFT[A-Za-z_]* +\(?@?Diagonal'], no hit), a
 [HasCoequalizers Grp] (no hit), and a [Cocomplete] at any algebraic
 category (pattern ['@?Cocomplete *\(?(Grp|Rng|Ring|Ab|CMon|RMod|Rg)'],
 whose one hit is Instance/Ab/DirectedColimit.v's prose "No [Cocomplete
 Ab]").  Those are what this file adds, and
 [Grp_coproduct_agrees] below says the free product it obtains IS the one
 Instance/Grp/Pushout.v built.

 NAMES.  The issue suggests a module Instance/Grp/Coproduct.v, not
 used, and its verification block runs [Print Assumptions
 Grp_free_product].  That constant is Instance/Grp/Pushout.v's
 words-based free product, not a construction by the adjoint functor
 theorem; the latter is this file's [Grp_Cocartesian_via_GAFT], and
 [Grp_free_product_iso] and [Grp_coproduct_agrees] relate the two.

 ** THE ROUTE: ONE THEOREM, APPLIED AT THE DIAGONAL

 A J-shaped colimit functor is a left adjoint of the diagonal
 Δ[J] : Grp ⟶ [J, Grp], and Adjunction/Diagonal/Limit.v reads colimits
 off such an adjoint ([Diagonal_left_adjoint_HasColimits]).  So for each
 shape J the UNIVERSES section below allows (homs at the carrier
 universe, objects at or below it), [GAFT] is applied to Δ[J]
 ([Grp_colim_via_GAFT]), and the three hypotheses are:

 - completeness of the domain: Instance/Grp/Limit.v's [Grp_Complete];
 - continuity of Δ[J]: Adjunction/Diagonal/Limit.v's
 [Diagonal_continuous], bridged to [GAFT]'s preservation hypothesis
 by Construction/Comma/Creation.v's [Continuous_PreservesImageLimit]
 (the alternative, [right_adjoint_PreservesImageLimit], would be circular
 here, Δ[J] being a right adjoint exactly when the colimits exist);
 - a solution set at each diagram D : J ⟶ Grp:
 [Diagonal_Grp_solution_set], the one new ingredient.

 [Grp_Cocomplete_via_GAFT] assembles the shapes into a [Cocomplete].

 ** THE SOLUTION SET: CONE CONGRUENCES ON A FREE GROUP

 Following the one idea of Instance/Grp/FreeAFT.v, the index is a family
 of [Prop]-valued congruences on a term model, never a Σ over the
 objects of [Grp] (the size note in the header of Structure/Complete.v
 explains why the latter is one universe too high).  Here the term model
 is the free group [FGWord DGen] on the DISJOINT UNION of the carriers,
 [DGen] = Σ j, carrier (D j), taken with Leibniz equality.  A member of
 the index ([DCongIdx]) is a relation [Rq] with a proof of
 [IsCoconeCong Rq]: [Rq] is a group congruence ([IsGrpCongruence]), it
 identifies the letters of `≈`-equal elements ([cc_resp]), it makes each
 insertion multiplicative ([cc_mul]), and it identifies [a] with its
 image under every arrow of the diagram ([cc_nat]).  Those three extra
 clauses are exactly what makes the insertions into the quotient
 [DQ i] group homomorphisms ([dq_leg], through Instance/Grp.v's
 [Build_GrpHom'], which derives the unit law) and makes them a cocone
 ([dq_arr]).  Covering: a cocone h : D ⟹ Δ(c) flattens to a map of
 generators ([dflat]), extends to the free group
 ([free_grp_extend]), and its kernel ([fg_ker] of Instance/Grp/FreeAFT.v)
 is a cocone congruence ([dker_cocone]) whose quotient maps to c by
 [fg_ker_med].  The kernel is a [Prop] because the TARGET c carries
 [grp_prop]; that is the property the PR "algebraic carriers are sets"
 (2026-09-17) added to every [GrpObject], and without it the index would
 not fit at the carrier universe.

 [dker_cocone] ENDS IN [Defined], AND MUST.  [QGrp] depends on the proof
 of [IsGrpCongruence], so the quotient at the kernel index is the
 quotient [fg_ker_med] maps out of only when [cc_grp _ dker_cocone]
 reduces to [fg_ker_is_cong].  Measured by closing [dker_cocone] with
 [Qed] in a copy of this file: [Diagonal_Grp_solution_set] is then
 refused with "The term "fg_ker_med (dflat c h)" has type "GrpHom (QGrp
 (fg_ker (dflat c h)) (fg_ker_is_cong (dflat c h))) c" while it is
 expected to have type "DQ (dker_idx c h) ~{ Grp }~> c"" (universe
 instances elided).

 ** FINITE COLIMITS, THROUGH THE EXISTING BRIDGES

 The binary coproduct, the coequalizers and the initial object are NOT
 rebuilt: Structure/Limit/Finite.v's bridges are applied to
 [Cocomplete_FinitelyCocomplete Grp_Cocomplete_via_GAFT], read in
 [Grp^op] by [FinitelyCocomplete_FinitelyComplete_op].
 [Grp_Cocartesian_via_GAFT] is [FinitelyComplete_Cartesian] of it,
 [Grp_HasCoequalizers_via_GAFT] is Structure/Pullback/Reduction.v's
 [HasCoequalizers_of_HasEqualizers_op] after [FinitelyComplete_HasEqualizers],
 and [Grp_Initial_via_GAFT] is [FinitelyCocomplete_Initial].

 What that assembly IS, read off the bodies of those bridges in
 Structure/Limit/Finite.v: [FinitelyComplete_Cartesian] and
 [FinitelyComplete_HasEqualizers] are [Cartesian_of_HasPullbacks_Terminal]
 and [HasEqualizers_of_HasPullbacks_Terminal] at
 [FinitelyComplete_Terminal] and [FinitelyComplete_HasPullbacks], so,
 read back in [Grp], the binary coproduct is the AFT pushout over the
 AFT initial object, the coequalizer is assembled from AFT pushouts and
 the AFT initial object, and the initial object is the AFT colimit of
 the empty diagram.  Every one of those colimits is itself a [GAFT]
 colimit at a diagonal: [Grp_Cocomplete_via_GAFT] at the opposite of
 Finite.v's walking cospan [Roof^op] for a pushout, and at the
 opposite of its [EmptyShape] for the initial object.  The direct
 reading -- the coproduct as [GAFT]'s colimit over a discrete
 two-object shape, the coequalizer as its colimit over the walking
 parallel pair -- is NOT the one used; the same bridge assembly is
 used for all three categories of #450 (this file,
 Instance/Rng/Colimit.v and Instance/Variety/Colimit.v).

 Structure/Limit/Cartesian.v's [Cartesian_Limit] over
 Instance/Two/Discrete.v's [Two_Discrete] is deliberately NOT the route:
 [About] reads [Two_Discrete@{u u0} : Category@{u Set Set}] and
 [Cartesian_Limit@{u u0 u1 u2} : ∀ C : Category@{u2 Set Set}, …], and
 [Fun] identifies a shape's hom universe with the target's, so that route
 would pin the group carriers to [Set], below the [Set < carrier] side
 condition of [Grp_colim_via_GAFT] (UNIVERSES, below).

 ** INSTANCE DISCIPLINE

 This file imports Instance/Grp/Pushout.v, whose [Grp_Cocartesian] is
 [#[export]].  Every statement below that mentions a coproduct therefore
 passes its [Cocartesian] argument EXPLICITLY, so that no headline says
 "via the adjoint functor theorem" while resolving to the words-based
 instance.  Nothing in this file is registered as an [Instance].

 ** WHAT IS PROVED ABOUT WHAT WAS BUILT

 Agreement.  [Grp_coproduct_agrees] is Theory/Adjunction.v's
 [left_adjoint_iso] over Adjunction/Diagonal/Coproduct.v's
 [Diagonal_Coproduct_Adjunction] at the two [Cocartesian] structures: the
 two coproduct bifunctors [+(Grp)] agree up to natural isomorphism.  At
 one pair, [Grp_free_product_iso] is the comparison G +_AFT H ≅ G * H
 built from the two copairings, and [Grp_free_product_iso_inl] /
 [Grp_free_product_iso_inr] say it carries injections to injections --
 so the object the adjoint functor theorem produces is Instance/Grp/
 Pushout.v's free product, compatibly with the injections
 ([Grp_Cocartesian_obj_is_free_product] reads the right-hand object back
 as [Grp_free_product G H] by [eq_refl]).  [Grp_initial_agrees] compares
 the initial object with Instance/Grp.v's trivial group [Grp_Initial],
 and [Grp_coequalizer_agrees_normal_closure] compares the coequalizer of
 (f, 0) with Instance/Grp/Quotient/Colimit.v's quotient by the normal
 closure of the image of f (Riehl, "Category Theory in Context",
 Example 3.1.25).  The last two could not have been stated before #450,
 when Instance/Grp.v's zero object lived only at [Set] carriers; #450
 wrote out its universes in place (see the essay above [Grp_trivial]
 there).

 Exercise 1, second half.  [Grp_inl_via_GAFT_Monic] and
 [Grp_inr_via_GAFT_Monic] are Structure/Bicartesian/Matrix.v's
 [inl_Monic] / [inr_Monic] at [Grp_Zero] and the AFT coproduct: each
 injection is split by the copairing of the identity with the trivial
 map.  That is NOT the exercise's own method.  The in-repo catalog's
 statement summary of §V.7 Exercise 1
 (doc/plan/books/maclane/inventory/V.json, entry maclane:V.7:ex1, book
 page 128) opens this half with "Using the product G x H", which in
 this library is the comparison G + H → G × H, Structure/Semiadditive.v's
 [can_comparison]; the retraction needs no product at all, and
 Theory/Subobject/Disjoint.v's header records why that route is
 preferred there.  [Grp_free_product_meet_trivial] is
 Theory/Subobject/Disjoint.v's [coproduct_injections_meet_trivial] at
 the same structures: the intersection of the two injections, in the
 sense of #445's [sub_meet] (a pullback), is the bottom subobject, whose
 domain IS the trivial group by [eq_refl]
 ([Grp_free_product_meet_bottom_is_trivial]).  Its pullbacks are
 [Grp_HasPullbacks], chosen by measurement between two routes:
 [FinitelyComplete_HasPullbacks (Complete_FinitelyComplete Grp_Complete)]
 and Structure/Pullback/Reduction.v's
 [HasPullbacks_of_Cartesian_HasEqualizers] at [Grp_Cartesian].  Both
 carry the same strict bound, carrier < [eq_rect_r.u0]; the second
 reaches its equalizers through the first's pullbacks, and its
 constraint block has 23 constraints on stdlib globals against the
 first's 18 (the same strict one, plus four bounds [eq.u0],
 [eq_ind.u0], [eq_ind_r.u0], [Fin.case0.u0] on the carrier and one,
 [False_rect.u0], on the object universe), so the first is used.

 ** STRENGTHS, STRICTEST FIRST

 Nothing about a colimit object computes.  [GAFT] ends in [Qed] (so
 does [left_adjoint_iso]; [About] reports both opaque), and so the AFT
 coproduct of two groups is not convertible to [Grp_free_product]:
 measured in a scratch file, [Example conv (G H : Grp) : @Coprod Grp
 Grp_Cocartesian_via_GAFT G H = Grp_free_product G H := eq_refl] is
 refused with "cannot unify "G + H" and "Grp_free_product G H"".
 Every agreement is therefore an isomorphism, carried as data:
 [Grp_free_product_iso],
 [Grp_initial_agrees] and [Grp_coequalizer_agrees_normal_closure] are
 [≅], [Grp_coproduct_agrees] is `≈` of functors (a natural isomorphism),
 and the equations about them ([Grp_free_product_iso_inl] and
 [Grp_free_product_iso_inr]) are `≈`.  The meet is `≈` in the subobject
 setoid, which is again an isomorphism of domains.  The two [eq_refl]
 [Example]s are about the words-based instance and about the bottom
 subobject, not about anything the theorem built.

 ** UNIVERSES, MEASURED

 By [About] under [Set Printing Universes], dropping bounds on stdlib
 globals: [Diagonal_Grp_solution_set] takes J : Category@{u u0 u0} and
 D : J ⟶ Grp@{u1 u0} and returns [SolutionSet@{u2 u1 u1 u0}] with
 [u0 <= u2] and [Set < u2] on the index [u2] -- an index of
 [Prop]-valued relations sits strictly above [Set] -- and [Set < u1]
 (Grp's own), but no [Set] bound on the carrier [u0].  [GAFT] itself,
 [GAFT@{cobj dobj h u u0 u1}], takes [SolutionSet@{h dobj cobj h}]:
 the index AT the hom universe [h], which for [Grp] is the carrier.
 [Grp_colim_via_GAFT] takes
 J : Category@{u2 u3 u3} with [u2 <= u3]: J's objects stay free below
 the carrier, which is what [Diagonal_continuous]'s explicit binders buy.
 [Grp_Cocomplete_via_GAFT] is [Cocomplete@{u u0 u u1}] over [Grp@{u1 u}]
 with [Set < u], [u < u1] and [u0 <= u]: the one side condition is
 [Set < carrier], the same as Instance/Grp/FreeAFT.v's
 [free_group_via_GAFT].  It is [GAFT]'s, not the solution set's: the
 index must sit AT the carrier, and it sits above [Set].  Measured in a
 scratch file under [Monomorphic Constraint Set < gu]: at
 J : Category@{Set Set Set} and D : J ⟶ Grp@{gu Set},
 [@Diagonal_Grp_solution_set J D] is accepted, while
 [Grp_colim_via_GAFT@{gu _ _ Set Set _ _} J] is refused with "Universe
 inconsistency. Cannot enforce Set < Set because Set = Set."
 Test/ProbeAlgColimit450.v's N4 pins the refusal, with the solution set
 and [GAFT] applied to every argument but it both accepted at the same
 J as its controls.  The finite-colimit constants add, through
 [FinitelyComplete_HasPullbacks] (Structure/Limit/Finite.v, attributed
 by [About] on that constant), the strict stdlib bound carrier <
 [eq_rect_r.u0]; [Grp_Initial_via_GAFT] does not carry it.

 ** NON-VACUITY

 [Grp_free_product_via_GAFT_nontrivial]: the AFT coproduct of Z/2 with
 itself is not a subsingleton (¬ ∀ a b, a ≈ b), because [inl] is injective
 ([Grp_inl_via_GAFT_injective], from monicity by Instance/Grp.v's
 [Grp_injectivity_is_monic]).  It is stated at Instance/Grp.v's [Z2],
 which #450 also lifted off [Set] in place; before, [Z2] could not meet
 the [Set < carrier] side condition at all.  [Grp_initial_via_GAFT_trivial]
 shows the initial object is the one-element group.

 ** AXIOMS

 Every constant of this file reports "Closed under the global context".

 ** NOT DELIVERED

 No element-level description of any colimit built here: no reduced
 words, no normal form and no word problem, and none of the colimit
 objects computes.  No general coequalizer described as a quotient: the
 normal closure of the image of f · g⁻¹ is still not built, and only the
 pair (f, 0) is compared with an explicit quotient.  No filtered-colimit
 route (Mac Lane's primary argument in §IX.1).  No monadicity.  Riehl's
 presentation of the free product as a coequalizer of free groups
 (§5.6) is not in this file: it is Instance/Grp/Colimit/Presentation.v,
 whose [Grp_free_product_is_coequalizer] is stated at this file's
 coproduct and whose [Grp_free_product_coequalizer_agrees] compares it
 with this file's coequalizers.  Nothing at [Set]-level carriers, no
 [Cocartesian] agreement among it: the solution set itself elaborates
 there, but [GAFT] puts its index at the carrier universe and the index
 sits strictly above [Set] (UNIVERSES, above).  Nothing is registered
 as an [Instance]. 

 --------
 nLab：       https://ncatlab.org/nlab/show/adjoint+functor+theorem 
 nLab：       https://ncatlab.org/nlab/show/free+product 
 nLab：       https://ncatlab.org/nlab/show/Grp 
 维基百科：  https://en.wikipedia.org/wiki/Free_product 
 维基百科：  https://en.wikipedia.org/wiki/Category_of_groups麦克莱恩，《为工作数学家而设的范畴论》，第2版（GTM 5），§V.7 练习1（书本第128页，PDF第137页）要求利用伴随函子定理构造两个群的自由积，并证明它的两个注入映射是单射且它们的像在平凡子群中相交；§IX.1 练习1（书本第214页，PDF第221页）要求利用同一个定理证明  [Grp]  拥有所有小余极限。所用定理是弗雷德的一般伴随函子定理，§V.6 定理2，树结构在 Adjunction/GAFT.v 中表示为 [GAFT]；Instance/Grp/FreeAFT.v 在遗忘函子上应用该定理，正如§V.6 在书本第123页所做的（该页在仓库目录 doc/plan/books/maclane/inventory/V.json 中记录为 maclane:V.6:construction-free-group）。维基百科的
 “自由产品”提供了这个文件从未构建的元素级图景：
 在两个因子之间交替的约简词。

 ** 问题的调查部分已过时，已测量第450号问题说群的自由积是“仅限文字描述”，并且“没有 [Grp]”。在编写此文件时，两者都不存在。[Grp] 是 Instance/Grp.v (#255)，而 Instance/Grp/Pushout.v 已经通过生成元和关系构建了自由积——[Grp_free_product]，以及导出的 [Grp_Cocartesian] 和 [Grp_free_product_injections_Monic]——作为沿常量分支的并合，没有看到伴随函子定理。当时缺失的是，在父提交（e139ecfb）上由 [grep -rn --include='*.v'] 在整个树上测量：[GAFT] 应用于对角函子（模式 ['GAFT[A-Za-z_] * +\(?@?Diagonal'，未命中）、[HasCoequalizers Grp]（未命中）以及在任何代数范畴上的 [Cocomplete]（模式 ['@?Cocomplete *\(?(Grp|Rng|Ring|Ab|CMon|RMod|Rg)']，其唯一命中是在 Instance/Ab/DirectedColimit.v 的文字描述“没有 [Cocomplete Ab]”）。这些是此文件添加的内容，下面的 [Grp_coproduct_agrees] 说明它获得的自由积是 Instance/Grp/Pushout.v 构建的那个。

 名称。该问题建议了一个模块 Instance/Grp/Coproduct.v，没有使用，其验证块运行 [Print Assumptions Grp_free_product]。该常量是基于 Instance/Grp/Pushout.v 的字词形式自由积，而不是通过伴随函子定理的构造；后者是此文件的 [Grp_Cocartesian_via_GAFT]，[Grp_free_product_iso] 和 [Grp_coproduct_agrees] 将两者联系起来。

 ** 路径：一个定理，在对角线处应用J 型余极限函子是对角函子 Δ [J] : Grp ⟶ [J, Grp] 的左伴随，而 Adjunction/Diagonal/Limit.v 从这样的伴随 ([Diagonal_left_adjoint_HasColimits]) 中读取余极限。因此，对于每个形状 J，下方的 UNIVERSES 部分允许（在承载宇宙中的同态，在其上或以下的对象），[GAFT] 被应用到 Δ [J] ([Grp_colim_via_GAFT])，三个假设是：- 域的完备性：Instance/Grp/Limit.v 的 [Grp_Complete]；
 - Δ [J] 的连续性：Adjunction/Diagonal/Limit.v 的 [Diagonal_continuous]，通过 Construction/Comma/Creation.v 的 [Continuous_PreservesImageLimit] 与 [GAFT] 的保持假设相关联（备选方案 [right_adjoint_PreservesImageLimit] 在此会形成循环，因为 Δ [J] 恰好在余极限存在时是右伴随）；
 - 在每个图 D : J ⟶ Grp 上的解集：[Diagonal_Grp_solution_set]，唯一的新成分。

 [Grp_Cocomplete_via_GAFT] 将这些形状组装成一个 [Cocomplete]。

 ** 解集：自由群上的锥同余遵循 Instance/Grp/FreeAFT.v 的一个思路，索引是一个 [Prop] 值的一族同余关系在项模型上，从不在 [Grp] 的对象之上 Σ（Structure/Complete.v 头部的大小说明解释了为什么后者的宇宙级别高了一层）。这里的项模型是自由群 [FGWord DGen]，基于载体的 DISJOINT UNION，[DGen] = Σ j, carrier (D j)，采用 Leibniz 等式。索引的一个成员（[DCongIdx]）是一个关系 [Rq]，并伴随一个证明 [IsCoconeCong Rq]：[Rq] 是群同余（[IsGrpCongruence]），它识别 `≈` 相等元素的字母（[cc_resp]），它使每个插入操作成为乘法性的（[cc_mul]），并且它将 [a] 识别为其在图的每条箭头下的像（[cc_nat]）。那三条额外的条款正是使得对商群的插入 [DQ i] 成为群同态（[dq_leg]，通过 Instance/Grp.v 的 [Build_GrpHom']，推导出单位律）并使它们成为一个余锥（[dq_arr]）。覆盖：一个余锥 h : D ⟹ Δ(c) 展开为生成元映射（[dflat]），延展到自由群（[free_grp_extend]），并且它的核（Instance/Grp/FreeAFT.v 中的 [fg_ker]）是一个余锥同余（[dker_cocone]），其商映射到 c，通过 [fg_ker_med]。核是一个 [Prop]，因为目标 c 具有 [grp_prop]；这就是 PR “代数承载是集合”（2026-09-17）添加到每个 [GrpObject] 的属性，如果没有它，指数将不适合承载宇宙。[dker_cocone] 以 [Defined] 结尾，并且必须如此。[QGrp] 依赖于 [IsGrpCongruence] 的证明，因此在核指数处的商只有在 [cc_grp _ dker_cocone] 化简为 [fg_ker_is_cong] 时才由 [fg_ker_med] 映射出。通过在本文件的一个副本中用 [Qed] 闭合 [dker_cocone] 来测量：[Diagonal_Grp_solution_set] 随后被拒绝，提示“项 "fg_ker_med (dflat c h)" 的类型为 "GrpHom (QGrp (fg_ker (dflat c h)) (fg_ker_is_cong (dflat c h))) c"，而期望的类型为 "DQ (dker_idx c h) ~{ Grp }~> c"”（省略了宇宙实例）。

 ** 有限余极限，通过现有桥接二元余积、共同等化子和初始对象未被重建：Structure/Limit/Finite.v 的桥应用于 [Cocomplete_FinitelyCocomplete Grp_Cocomplete_via_GAFT]，由 [FinitelyCocomplete_FinitelyComplete_op] 在 [Grp^op] 中读取。[Grp_Cocartesian_via_GAFT] 是它的 [FinitelyComplete_Cartesian]，[Grp_HasCoequalizers_via_GAFT] 是 Structure/Pullback/Reduction.v 的 [HasCoequalizers_of_HasEqualizers_op] 在 [FinitelyComplete_HasEqualizers] 之后，[Grp_Initial_via_GAFT] 是 [FinitelyCocomplete_Initial]。那个集合是什么，从 Structure/Limit/Finite.v 中那些桥的主体中读出：[FinitelyComplete_Cartesian] 和 [FinitelyComplete_HasEqualizers] 是 [Cartesian_of_HasPullbacks_Terminal] 和 [HasEqualizers_of_HasPullbacks_Terminal]，在 [FinitelyComplete_Terminal] 和 [FinitelyComplete_HasPullbacks]，所以，在 [Grp] 中读回，二元余积是 AFT 从 AFT 初始对象推出的推挤，等化子由 AFT 推挤和 AFT 初始对象组装而成，而初始对象是空图的 AFT 余极限。每一个这样的余极限本身都是对角线上的 [GAFT] 余极限：[Grp_Cocomplete_via_GAFT] 在 Finite.v 的行走余跨的对面 [Roof^op] 上用于推挤，且在其 [EmptyShape] 的对面用于初始对象。直接读取——把余积当作 [GAFT] 在离散的两个对象形状上的余极限，把共同化等化器当作它在并行对上的余极限——不是使用的方式；同样的桥接组合用于 #450 的三个范畴（本文件、Instance/Rng/Colimit.v 和 Instance/Variety/Colimit.v）。

 Structure/Limit/Cartesian.v 中的 [Cartesian_Limit] 在 Instance/Two/Discrete.v 中的 [Two_Discrete] 上故意不是路线：
 [About] 读取 [Two_Discrete@{u u0} : Category@{u Set Set}] 和 [Cartesian_Limit@{u u0 u1 u2} : ∀ C : Category@{u2 Set Set}, …]，并且 [Fun] 将一个形状的 Hom 宇宙与目标的同一，这条路线会将群承载器固定在 [Set] 下，低于 [Set < carrier] 对 [Grp_colim_via_GAFT]（宇宙，见下文）的边条件。

 ** 实例纪律该文件导入了 Instance/Grp/Pushout.v，其 [Grp_Cocartesian] 为 [#[export]]。因此，下面每个提到余积的语句都显式地传递了它的 [Cocartesian] 参数，这样在解析到基于词的实例时，没有标题会写着“通过伴随函子定理”。该文件中没有任何内容被注册为 [Instance]。

 ** 关于已构建内容的证明]协议。[Grp_coproduct_agrees] 是 Theory/Adjunction.v 的 [left_adjoint_iso] ，在 Adjunction/Diagonal/Coproduct.v 的 [Diagonal_Coproduct_Adjunction] 上具有两个 [Cocartesian] 结构：两个余积双函子 [+(Grp)] 在自然同构意义下是相同的。在一对情况下，[Grp_free_product_iso] 是通过两个共配对构建的比较 G +_AFT H ≅ G * H，而 [Grp_free_product_iso_inl] / [Grp_free_product_iso_inr] 表示它将注入保持为注入——因此，伴随函子定理产生的对象是 Instance/Grp/Pushout.v 的自由积，并与这些注入兼容（[Grp_Cocartesian_obj_is_free_product] 通过 [eq_refl] 将右侧对象读回为 [Grp_free_product G H]）。[Grp_initial_agrees] 比较了初始对象与 Instance/Grp.v 的平凡群 [Grp_Initial]，[Grp_coequalizer_agrees_normal_closure] 则比较了 (f, 0) 的余等化子与 Instance/Grp/Quotient/Colimit.v 中通过 f 的像的正规闭包得到的商（Riehl，《情境中的范畴论》，例 3.1.25）。在 #450 之前，最后两个还无法表述，因为 Instance/Grp.v 的零对象只存在于 [Set] 的承载物中；#450 将其宇宙写出以代替（参见上文 [Grp_trivial] 那里的文章）。练习 1，下半部分。[Grp_inl_via_GAFT_Monic] 和 [Grp_inr_via_GAFT_Monic] 是 Structure/Bicartesian/Matrix.v 中的 [inl_Monic] / [inr_Monic]，在 [Grp_Zero] 以及 AFT 余积下：每个注入都被恒等映射与平凡映射的余对所分裂。这并不是该练习自身的方法。库内目录对 §V.7 练习 1 的陈述摘要（doc/plan/books/maclane/inventory/V.json，条目 maclane:V.7:ex1，书页 128）以“使用乘积 G x H”开头，而在本库中，这对应于比较 G + H → G × H，Structure/Semiadditive.v 的 [can_comparison]；这个收缩完全不需要乘积，并且 Theory/Subobject/Disjoint.v 的页眉记录了为何该路线在那里更优选。[Grp_free_product_meet_trivial] 是 Theory/Subobject/Disjoint.v 的 [coproduct_injections_meet_trivial]，在相同的结构上：两个注入的交集，在 #445 的 [sub_meet]（一个拉回）的意义下，是最底层的子对象，其域根据 [eq_refl]（[Grp_free_product_meet_bottom_is_trivial]）是平凡群。它的拉回为 [Grp_HasPullbacks]，由两条路径之间的测量选取：[FinitelyComplete_HasPullbacks (Complete_FinitelyComplete Grp_Complete)] 和 Structure/Pullback/Reduction.v 的 [HasPullbacks_of_Cartesian_HasEqualizers] 在 [Grp_Cartesian]。两者都承载相同的严格界限，承载体 < [eq_rect_r.u0]；第二个通过第一个的拉回达到其等化器，其约束块对 stdlib 全局有 23 个约束，而第一个有 18 个约束（相同的严格约束外，加上四个承载体的界限 [eq.u0]，[eq_ind.u0]，[eq_ind_r.u0]，[Fin.case0.u0]，以及对象宇宙上的一个 [False_rect.u0]），所以使用第一个。** 优势，从最严格的开始关于余极限对象没有任何计算。[GAFT] 以 [Qed] 结束（[left_adjoint_iso] 也是如此；[About] 报告两者都是不透明的），因此两个群的 AFT 余积不能转换为 [Grp_free_product]：在一个测试文件中测量时，[Example conv (G H : Grp) : @Coprod Grp Grp_Cocartesian_via_GAFT G H = Grp_free_product G H := eq_refl] 被拒绝，显示“cannot unify 'G + H' and 'Grp_free_product G H'”。因此，每个一致都为同构，并作为数据携带：[Grp_free_product_iso]、[Grp_initial_agrees] 和 [Grp_coequalizer_agrees_normal_closure] 是 [≅]，[Grp_coproduct_agrees] 是函子（自然同构）的 `≈`，并且它们之间的方程（[Grp_free_product_iso_inl] 和 [Grp_free_product_iso_inr]）是 `≈`。交集是子对象等价类中的 `≈`，这又是定义域的一个同构。这两个 [eq_refl] [Example] 是关于基于词的实例和关于底层子对象的，而不是关于定理构建的任何内容。

 ** 宇宙，测量由 [About] 在 [Set Printing Universes] 下，取消对 stdlib 的界限
 全局变量：[Diagonal_Grp_solution_set] 接受 J : Category@{u u0 u0} 和
 D : J ⟶ Grp@{u1 u0} 并返回 [SolutionSet@{u2 u1 u1 u0}]，具有
 [u0 <= u2] 和 [Set < u2] 在索引 [u2] 上 —— 一个 [Prop] 值关系的索引，严格位于 [Set] 之上 —— 以及 [Set < u1]
 （Grp 自身的），但载体 [u0] 上没有 [Set] 的界限。[GAFT] 本身，
 [GAFT@{cobj dobj h u u0 u1}]，接受 [SolutionSet@{h dobj cobj h}]：
 在同伦宇宙 [h] 上的索引，对于 [Grp] 而言，这就是载体。[Grp_colim_via_GAFT] 接受
 J : Category@{u2 u3 u3}，且 [u2 <= u3]：J 的对象在载体以下保持自由，正是 [Diagonal_continuous] 的显式绑定器所提供的。[Grp_Cocomplete_via_GAFT] 在 [Grp@{u1 u}] 上方的 [Cocomplete@{u u0 u u1}]，具有 [Set < u]、[u < u1] 和 [u0 <= u]：一边的条件是 [Set < carrier]，与 Instance/Grp/FreeAFT.v 的 [free_group_via_GAFT] 相同。它是 [GAFT] 的，而不是解集的：索引必须位于承载体上，并且它位于 [Set] 之上。在 [Monomorphic Constraint Set < gu] 下的一个临时文件中测量：在 J : Category@{Set Set Set} 和 D : J ⟶ Grp@{gu Set} 时，[@Diagonal_Grp_solution_set J D] 被接受，而 [Grp_colim_via_GAFT@{gu _ _ Set Set _ _} J] 被拒绝，并显示“宇宙不一致。无法强制 Set < Set 因为 Set = Set。” Test/ProbeAlgColimit450.v 的 N4 钉住了拒绝，解集和 [GAFT] 应用于每个参数，但在与其控制相同的 J 上都被接受。有限余极限常数通过 [FinitelyComplete_HasPullbacks]（Structure/Limit/Finite.v，在该常数上由 [About] 标注）添加严格的 stdlib 有界载体 < [eq_rect_r.u0]；[Grp_Initial_via_GAFT] 并不携带它。

 ** 非空性

 [Grp_free_product_via_GAFT_nontrivial]：Z/2 与自身的 AFT 余积不是子单集合（¬ ∀ a b, a ≈ b），因为 [inl] 是单射的（[Grp_inl_via_GAFT_injective]，由 Instance/Grp.v 的 [Grp_injectivity_is_monic] 的单性得出）。它在 Instance/Grp.v 的 [Z2] 中被陈述，#450 也从 [Set] 提升了它；在此之前，[Z2] 完全无法满足 [Set < carrier] 的边条件。[Grp_initial_via_GAFT_trivial] 显示初始对象是单元素群。

 ** 公理

 此文件的每个常数都报告“在全局上下文下封闭”。

 ** 未交付这里没有任何余极限的元素级描述：没有约简词、没有规范形式，也没有字问题，且没有任何余极限对象能够计算。没有将一般的等化器描述为商：f · g⁻¹ 的像的法闭包仍未构建，并且仅将 (f, 0) 这一对与显式商进行比较。没有过滤余极限的方案（Mac Lane 在 §IX.1 的主要论证）。没有单子性。Riehl 对自由积作为自由群等化器的呈现（§5.6）不在此文件中：它在 Instance/Grp/Colimit/Presentation.v 中，其 [Grp_free_product_is_coequalizer] 在此文件的余积中说明，其 [Grp_free_product_coequalizer_agrees] 将其与此文件的等化器进行比较。在 [Set] 级载体上没有任何东西，[Cocartesian] 之间没有协议：解集本身在那里展开，但 [GAFT] 将其索引置于载体宇宙中，并且该索引严格位于 [Set]（宇宙之上）之上。没有任何东西被注册为 [Instance]。
*)

(** ** The solution set at a diagram / ** 图表上的解集 *)

Section DiagonalSolutionSet.

Context {J : Category}.
Context (D : J ⟶ Grp).

(* The generators: the disjoint union of the carriers, with Leibniz equality. Each factor's own `≈` enters through [cc_resp] below. / 生成元：承载体的不交并，并带有莱布尼茨等式。每个因子的 `≈` 自身通过下方的 [cc_resp] 进入。 *)
Definition DGen : SetoidObject :=
  {| carrier := { j : obj[J] & carrier (grp_setoid (D j)) };
     is_setoid := eq_Setoid _ |}.

Definition dins (j : J) (a : carrier (grp_setoid (D j))) : FGWord DGen :=
  fg_insert DGen (j; a).

(* A congruence on the free group that makes the insertions a cocone of group homomorphisms. / 在自由群上的一个合同，使插入成为群同态的余锥。 *)
Record IsCoconeCong (Rq : FGWord DGen → FGWord DGen → Prop) : Prop := {
  cc_grp  : IsGrpCongruence Rq;
  cc_resp : ∀ j a b, a ≈ b → Rq (dins j a) (dins j b);
  cc_mul  : ∀ j a b, Rq (dins j (grp_mul (D j) a b))
                        (grp_mul (FreeGrpObject DGen) (dins j a) (dins j b));
  cc_nat  : ∀ j k (f : j ~{J}~> k) a,
              Rq (dins k (grp_map (fmap[D] f) a)) (dins j a)
}.

Definition DCongIdx : Type :=
  { Rq : FGWord DGen → FGWord DGen → Prop & IsCoconeCong Rq }.

Definition DQ (i : DCongIdx) : obj[Grp] := QGrp (`1 i) (cc_grp _ (`2 i)).

Definition dq_leg (i : DCongIdx) (j : J) : D j ~{Grp}~> DQ i.
Proof.
  unshelve refine (@Build_GrpHom' (D j) (DQ i)
                     {| morphism := dins j |} _).
  - intros a b Hab; exact (cc_resp _ (`2 i) j a b Hab).
  - intros a b; exact (cc_mul _ (`2 i) j a b).
Defined.

Definition dq_arr (i : DCongIdx) :
  D ~{[J, Grp]}~> fobj[@Diagonal Grp J] (DQ i).
Proof.
  unshelve refine (@Build_Transform' J Grp D (fobj[@Diagonal Grp J] (DQ i))
                     (fun j => dq_leg i j) _).
  intros j k f a; simpl.
  apply (gc_sym _ _ (cc_grp _ (`2 i))).
  exact (cc_nat _ (`2 i) j k f a).
Defined.

(* The covering: the kernel of a cocone's extension to the free group. / 覆盖：余圆扩展到自由群的核心。 *)
Section Cover.

Context (c : Grp) (h : D ~{[J, Grp]}~> fobj[@Diagonal Grp J] c).

Definition dflat : DGen ~{Sets}~> Grp_Forget c.
Proof using h.
  unshelve refine {| morphism := fun p => grp_map (transform[h] (`1 p)) (`2 p) |}.
  intros p q Hpq; simpl in Hpq; subst; reflexivity.
Defined.

Lemma dflat_gen (j : J) (a : carrier (grp_setoid (D j))) :
  fg_ev dflat (dins j a) ≈ grp_map (transform[h] j) a.
Proof using h. exact (free_grp_extend_generators DGen c dflat (j; a)). Qed.

(* Transparent on purpose: see the header. / 故意透明：请参阅标题。 *)
Lemma dker_cocone : IsCoconeCong (fg_ker dflat).
Proof using h.
  constructor.
  - exact (fg_ker_is_cong dflat).
  - intros j a b Hab; unfold fg_ker; apply (@pequiv_from _ _ (grp_prop c)).
    rewrite !dflat_gen; now rewrite Hab.
  - intros j a b; unfold fg_ker; apply (@pequiv_from _ _ (grp_prop c)).
    unfold fg_ev; rewrite (grp_map_mul (free_grp_extend dflat)).
    fold (fg_ev dflat (dins j a)); fold (fg_ev dflat (dins j b)).
    fold (fg_ev dflat (dins j (grp_mul (D j) a b))).
    rewrite !dflat_gen.
    apply (grp_map_mul (transform[h] j)).
  - intros j k f a; unfold fg_ker; apply (@pequiv_from _ _ (grp_prop c)).
    rewrite !dflat_gen.
    pose proof (@naturality_sym _ _ _ _ h j k f a) as Hn; simpl in Hn.
    rewrite Hn; reflexivity.
Defined.

Definition dker_idx : DCongIdx := (fg_ker dflat; dker_cocone).

End Cover.

Definition Diagonal_Grp_solution_set : SolutionSet (@Diagonal Grp J) D.
Proof.
  unshelve refine (@Build_SolutionSet Grp ([J, Grp]) (@Diagonal Grp J) D
                     DCongIdx DQ dq_arr _).
  intros c h.
  exists (dker_idx c h).
  exists (fg_ker_med (dflat c h)).
  intros j a; simpl.
  exact (dflat_gen c h j a).
Defined.

End DiagonalSolutionSet.

(* * ** Every colimit of groups within the shape discipline / * ** 在形状学科中的群的每一个余极限 *)

Definition Grp_colim_via_GAFT (J : Category) :
  { K : [J, Grp] ⟶ Grp & K ⊣ @Diagonal Grp J } :=
  GAFT (@Diagonal Grp J) Grp_Complete
       (Continuous_PreservesImageLimit Diagonal_continuous)
       (@Diagonal_Grp_solution_set J).

Definition Grp_Cocomplete_via_GAFT : @Cocomplete Grp :=
  fun J F => Diagonal_left_adjoint_HasColimits (projT2 (Grp_colim_via_GAFT J)) F.

(* * ** Coproducts, coequalizers and the initial object / * ** 余积、余等化子和初对象 *)

Definition Grp_FinitelyCocomplete_via_GAFT : @FinitelyCocomplete Grp :=
  Cocomplete_FinitelyCocomplete Grp_Cocomplete_via_GAFT.

Definition Grp_Cocartesian_via_GAFT : @Cocartesian Grp :=
  FinitelyComplete_Cartesian
    (FinitelyCocomplete_FinitelyComplete_op Grp_FinitelyCocomplete_via_GAFT).

Definition Grp_HasCoequalizers_via_GAFT : HasCoequalizers Grp :=
  HasCoequalizers_of_HasEqualizers_op
    (FinitelyComplete_HasEqualizers
       (FinitelyCocomplete_FinitelyComplete_op Grp_FinitelyCocomplete_via_GAFT)).

Definition Grp_Initial_via_GAFT : @Initial Grp :=
  FinitelyCocomplete_Initial Grp_FinitelyCocomplete_via_GAFT.

(* * ** Agreement with the constructions already in tree / * ** 与树中已有结构的一致性 *)

(*
 The coproduct bifunctors agree up to natural isomorphism: both are left
 adjoint to the diagonal [Grp ⟶ Grp ∏ Grp]. 

 --------
 余积双函子在自然同构下是一致的：两者都是对角函子 [Grp ⟶ Grp ∏ Grp] 的左伴随。
*)
Definition Grp_coproduct_agrees :
  @InternalCoproductFunctor Grp Grp_Cocartesian_via_GAFT
    ≈ @InternalCoproductFunctor Grp Grp_Cocartesian :=
  left_adjoint_iso (Diagonal_Product Grp) _ _
    (@Diagonal_Coproduct_Adjunction Grp Grp_Cocartesian_via_GAFT)
    (@Diagonal_Coproduct_Adjunction Grp Grp_Cocartesian).

(* At one pair of groups: the comparison built from the two copairings, which carries injections to injections. / 在一对群上：由两个同配对构建的比较，它将单射映射到单射。 *)
Definition Grp_free_product_iso@{u p +} (G H : Grp@{u p}) :
  @Coprod Grp@{u p} Grp_Cocartesian_via_GAFT G H
    ≅ @Coprod Grp@{u p} Grp_Cocartesian G H.
Proof.
  unshelve refine {|
    to   := @merge Grp Grp_Cocartesian_via_GAFT _ _ _
              (@inl Grp Grp_Cocartesian G H) (@inr Grp Grp_Cocartesian G H);
    from := @merge Grp Grp_Cocartesian _ _ _
              (@inl Grp Grp_Cocartesian_via_GAFT G H)
              (@inr Grp Grp_Cocartesian_via_GAFT G H) |}.
  - rewrite <- (@merge_comp Grp Grp_Cocartesian).
    rewrite (@inl_merge Grp Grp_Cocartesian_via_GAFT),
            (@inr_merge Grp Grp_Cocartesian_via_GAFT).
    exact (@merge_inl_inr Grp Grp_Cocartesian G H).
  - rewrite <- (@merge_comp Grp Grp_Cocartesian_via_GAFT).
    rewrite (@inl_merge Grp Grp_Cocartesian),
            (@inr_merge Grp Grp_Cocartesian).
    exact (@merge_inl_inr Grp Grp_Cocartesian_via_GAFT G H).
Defined.

Lemma Grp_free_product_iso_inl@{u p +} (G H : Grp@{u p}) :
  to (Grp_free_product_iso G H) ∘ @inl Grp Grp_Cocartesian_via_GAFT G H
    ≈ @inl Grp Grp_Cocartesian G H.
Proof. exact (@inl_merge Grp Grp_Cocartesian_via_GAFT _ _ _ _ _). Qed.

Lemma Grp_free_product_iso_inr@{u p +} (G H : Grp@{u p}) :
  to (Grp_free_product_iso G H) ∘ @inr Grp Grp_Cocartesian_via_GAFT G H
    ≈ @inr Grp Grp_Cocartesian G H.
Proof. exact (@inr_merge Grp Grp_Cocartesian_via_GAFT _ _ _ _ _). Qed.

(* The right-hand object above IS Instance/Grp/Pushout.v's free product. / 上方右侧的对象是 Instance/Grp/Pushout.v 的自由积。 *)
Example Grp_Cocartesian_obj_is_free_product (G H : Grp) :
  @Coprod Grp Grp_Cocartesian G H = Grp_free_product G H := eq_refl.

(* The initial object is the trivial group. / 初始对象是平凡群。 *)
Definition Grp_initial_agrees :
  @initial_obj Grp Grp_Initial_via_GAFT ≅ @initial_obj Grp Grp_Initial :=
  initial_unique Grp_Initial_via_GAFT Grp_Initial.

Lemma Grp_initial_via_GAFT_trivial
  (a b : carrier (grp_setoid (@initial_obj Grp Grp_Initial_via_GAFT))) :
  a ≈ b.
Proof.
  pose proof (iso_from_to Grp_initial_agrees a) as Ha.
  pose proof (iso_from_to Grp_initial_agrees b) as Hb.
  simpl in Ha, Hb.
  rewrite <- Ha, <- Hb.
  destruct (grp_map (to Grp_initial_agrees) a),
           (grp_map (to Grp_initial_agrees) b).
  reflexivity.
Qed.

(* The coequalizer of f with the trivial map is the quotient by the normal closure of the image of f (Riehl, Example 3.1.25). / f 与平凡映射的共同余子等于 f 的像的正规闭包的商 (Riehl，例 3.1.25)。 *)
Definition Grp_coequalizer_agrees_normal_closure {G H : Grp}
  (f : G ~{Grp}~> H) :
  `1 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _ f (@zero_mor Grp Grp_Zero G H))
    ≅ QuotientGrp (NormalClosure f) :=
  coequalizer_unique _ _
    (`2 (`2 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _ f
                (@zero_mor Grp Grp_Zero G H))))
    (normal_closure_IsCoequalizer f).

(* * ** Mac Lane §V.7 Exercise 1, second half / * ** 马克·莱恩 §V.7 练习 1，下半部分 *)

(*
 Both injections of the free product are monic, split by the copairing
 of the identity with the trivial map. 

 --------
 自由积的两次注入都是单射，通过恒等映射与平凡映射的共配对分裂。
*)
Definition Grp_inl_via_GAFT_Monic (G H : Grp) :
  Monic (@inl Grp Grp_Cocartesian_via_GAFT G H) :=
  @inl_Monic Grp Grp_Zero Grp_Cocartesian_via_GAFT G H.

Definition Grp_inr_via_GAFT_Monic (G H : Grp) :
  Monic (@inr Grp Grp_Cocartesian_via_GAFT G H) :=
  @inr_Monic Grp Grp_Zero Grp_Cocartesian_via_GAFT G H.

Lemma Grp_inl_via_GAFT_injective (G H : Grp) (a b : carrier (grp_setoid G)) :
  grp_map (@inl Grp Grp_Cocartesian_via_GAFT G H) a
    ≈ grp_map (@inl Grp Grp_Cocartesian_via_GAFT G H) b → a ≈ b.
Proof.
  exact (snd (Grp_injectivity_is_monic _) (Grp_inl_via_GAFT_Monic G H) a b).
Qed.

Lemma Grp_inr_via_GAFT_injective (G H : Grp) (a b : carrier (grp_setoid H)) :
  grp_map (@inr Grp Grp_Cocartesian_via_GAFT G H) a
    ≈ grp_map (@inr Grp Grp_Cocartesian_via_GAFT G H) b → a ≈ b.
Proof.
  exact (snd (Grp_injectivity_is_monic _) (Grp_inr_via_GAFT_Monic G H) a b).
Qed.

(* The pullbacks the subobject meet is taken in. / 子对象遇到的回拉被考虑在内。 *)
Definition Grp_HasPullbacks : HasPullbacks Grp :=
  FinitelyComplete_HasPullbacks (Complete_FinitelyComplete Grp_Complete).

(* The images of the two injections meet in the trivial subgroup. / 两个单射的像在平凡子群中相交。 *)
Definition Grp_free_product_meet_trivial (G H : Grp) :
  @sub_meet Grp Grp_HasPullbacks _
     (@sub_inl Grp Grp_Zero Grp_Cocartesian_via_GAFT G H)
     (@sub_inr Grp Grp_Zero Grp_Cocartesian_via_GAFT G H)
    ≈ @coprod_bot Grp Grp_Zero Grp_Cocartesian_via_GAFT G H :=
  @coproduct_injections_meet_trivial Grp Grp_Zero Grp_Cocartesian_via_GAFT
     Grp_HasPullbacks G H.

Example Grp_free_product_meet_bottom_is_trivial (G H : Grp) :
  sub_dom (@coprod_bot Grp Grp_Zero Grp_Cocartesian_via_GAFT G H)
    = Grp_trivial := eq_refl.

(** ** Non-vacuity / ** 非空性 *)

Example Grp_free_product_via_GAFT_nontrivial :
  (∀ a b : carrier (grp_setoid (@Coprod Grp Grp_Cocartesian_via_GAFT Z2 Z2)),
     a ≈ b) → False.
Proof.
  intro Hall.
  apply Z2_nontrivial.
  apply (Grp_inl_via_GAFT_injective Z2 Z2).
  apply Hall.
Qed.
