Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Adjunction.Continuity.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.

Generalizable All Variables.

(* * * Colimits of spaces: the final topology, and [PTopCat] cocomplete / * * 空间的余极限：最终拓扑，以及 [PTopCat] 余完备 *)

(*
 Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
 §V.9, read from the page images: the quotient construction, book
 pp. 133-134 (PDF pp. 142-143), and the paragraph that closes it on
 book p. 134 (PDF p. 143), "Now Proposition 1 was proved just from the
 axioms for a category, so its dual is also true.  This dual
 proposition and the above adjunction prove that Top has
 coequalizers.  Similar constructions yield coproducts (= disjoint
 unions) and general colimits in Top" (catalog id
 maclane:V.9:remark2, #458's); and Exercise 2, book p. 135 (PDF
 p. 144), which names the indiscrete functor "the right adjoint
 D' : Set → Top to the forgetful functor" (the exercise itself is not
 delivered)
 Riehl, "Category Theory in Context", Dover 2016, §3.6, printed p. 116
 (PDF p. 136), read from the PDF's text: Proposition 3.6.2, "the
 underlying set functor U : Top → Set is continuous and cocontinuous"
 (riehl:3.6:prop2, whose cocontinuity half is here), with, in its
 proof, "the coproduct is formed by assigning the disjoint union ...
 the finest topology so that each of the coproduct-inclusions ... is
 continuous" and "Theorem 4.6.2 implies that the colimit must be
 constructed in this manner"; and Example 3.6.3, "Any limit or colimit
 in Top can be constructed ... by forming the limit or colimit of the
 diagram of underlying sets and then topologizing the resulting space
 with the coarsest (in the case of limits) or finest (in the case of
 colimits) topologies so that the legs of the limit or colimit cones
 are continuous" (riehl:3.6:example3, whose colimit half is here)
 nLab: https://ncatlab.org/nlab/show/Top
 nLab: https://ncatlab.org/nlab/show/initial+topology
 nLab: https://ncatlab.org/nlab/show/quotient+space
 nLab: https://ncatlab.org/nlab/show/topological+concrete+category
 nLab: https://ncatlab.org/nlab/show/cocomplete+category

 BACKGROUND.  Colimits are how topology glues.  Mac Lane's own examples
 on book p. 134 are an open cover, which exhibits a space as the
 colimit of its pieces and their pairwise intersections, and the space
 X/A obtained by collapsing a subset to a point; quotient spaces,
 adjunction spaces and cell complexes are built the same way.  Every
 one of them is computed by one recipe: form the colimit of the
 underlying sets and give it the finest topology for which every leg of
 the colimiting cocone is continuous, the final topology of the family
 of legs, of which the quotient topology is the case of one map (nLab's
 initial-topology page gives both forms, as Instance/Top/Subspace.v's
 header records).  Riehl's proof explains why nothing else can happen:
 the underlying-set functor has a right adjoint, the indiscrete
 topology, so it preserves colimits, and the underlying set of any
 colimit of spaces IS the colimit of the underlying sets.  Categories
 whose forgetful functor lifts every (co)limit of the underlying sets
 in this way are nLab's topological concrete categories, the setting in
 which the recipe is a theorem about the functor rather than about
 spaces.  Mac Lane takes the other classical route.  Proposition 1
 (Instance/Top/Subspace.v) builds equalizers from a sliced adjunction,
 its dual builds coequalizers from the quotient topology, and "similar
 constructions yield coproducts"; a category with coproducts and
 coequalizers is cocomplete by the dual of his Theorem V.2.1, which the
 tree has as Structure/Limit/FromProducts.v's
 [Cocomplete_from_coproducts_coequalizers] (#416).  Both routes are
 delivered below, and compared.

 WHY [PTopCat].  Instance/Top/Prop.v's header explains why the
 Type-valued [Top] puts its homs strictly above its points and what
 the Prop-valued [PTop] buys.  For colimits the consequence is
 measured in Instance/Top/Cocomplete/TypeValued.v, which builds the
 pieces that ARE formable over [Top] (coproducts indexed at or below
 the points, and coequalizers on Instance/Top/Subspace/TypeValued.v's
 [TQuot]) and records the three walls that stop the rest; and
 Instance/Top/Cocomplete/Refutations.v refutes cocompleteness of both
 categories at every shape universe above the points under
 informative excluded middle (or decidable equality of spaces), and at
 any shape universe that carries an arrow index.  Everything in
 this file is over [PTopCat], by the maintainer's decision of
 2026-09-24 on #458; the issue's [Top_Cocomplete] is [PTop_Cocomplete]
 here, a stated deviation of name and category.

 WHAT IS HERE.
 - The final topology.  [PFinal S Ix X f] is the setoid [S] with the
 finest topology making every [f k : X k → S] continuous, for an
 index type [Ix] at ANY universe: a predicate is open when it
 respects the equality of [S] and its preimage along every [f k] is
 open ([PFinal_open], at [eq_refl]).  [pfinal_universal] is the
 universal property over arbitrary spaces [Z] mapping out, both
 directions; [pfinal_desc] is its book form, a map out of the final
 topology; [pfinal_finest] says it is the finest (any family of
 equality-respecting predicates with open preimages along every
 [f k] consists of opens of it, the family not required to be a
 topology); [pfinal_one_map_PQuot] says Instance/Top/Subspace.v's
 quotient topology [PQuot X T q] is its one-map case, with the same
 opens.
 - THE RECIPE, as a general lemma (Riehl's Example 3.6.3, colimit
 half).  For a diagram [F : D ⟶ PTopCat] and ANY cocone [N] of the
 underlying diagram [PForget ◯ F] in [Sets], [PFinalCocone F N] is
 [N]'s apex with the final topology for [N]'s legs; its image under
 [PForget] has [N]'s apex and legs on the nose
 ([PFinalCocone_points], [PFinalCocone_legs]).
 [pfinal_cocone_colimiting]: if [N] is colimiting in [Sets], the
 lifted cocone is colimiting in [PTopCat], at every shape universe,
 and its mediator IS the [Sets] mediator ([pfinal_cocone_med_map]).
 [pfinal_cocone_colimiting_reflect] is the converse, through the
 cocontinuity of [PForget] below, so [N] is colimiting exactly when
 its lift is.  [PTop_Colimit_lift] is the recipe for a [Colimit]
 record of the points.  [PTop_colimit_open_iff_final] is the recipe
 in Riehl's "must be constructed in this manner" form: the opens of
 EVERY colimit of spaces, however it was built, are exactly those of
 the final topology on its points for its legs.  The recipe is
 stated once, for every shape; the coproducts below reuse its
 [PFinal] rather than a topology of their own; products, equalizers
 and the limit half of the recipe are the limit side of #458
 (Instance/Top/Complete.v).
 - Remark 2 directly.  [PColimit F] is [PTop_Colimit_lift] at
 Instance/Sets/Cocomplete.v's [Sets_Colimit] of [PForget ◯ F], and
 [PTop_Cocomplete] packages it: [PTopCat] is cocomplete.  Its apex
 reads back at [eq_refl] as the final topology on [Sets_colim_obj]
 for the legs [Sets_colim_inj] ([PColimit_apex]), its points as
 [Sets_colim_obj] ([PColimit_points]) and its injections as
 [Sets_colim_inj] ([PColimit_inj]), and the mediator into a cocone
 [M] sends the point [x] of the summand at [d] to [M]'s leg at [d]
 applied to [x] ([PColimit_med_at]), the triangle that
 Instance/Sets/Cocomplete.v's [Sets_colim_triangle] states for
 [Sets].
 - Coproducts.  [PSigma Ix X] is the disjoint union
 [Sets_icoprod_obj] of the points with the final topology for its
 injections ([PSigma_points], [PSigma_open], at [eq_refl]);
 [psigma_inj], [psigma_case] (its value at a point of a summand,
 [psigma_case_at], at [eq_refl]), [psigma_desc], and
 [PTop_HasIndexedCoproducts], every index universe at or below the
 points'.
 - Remark 2 by the book's route.  [PTop_Cocomplete_via_coproducts] is
 [Cocomplete_from_coproducts_coequalizers] fed
 [PTop_HasIndexedCoproducts] and Instance/Top/Subspace.v's
 [PTop_HasCoequalizers], which is the dual of Proposition 1 at the
 quotient topology: the book's sentence, term for term.
 [PTop_Cocomplete_via_coproducts_apex] reads the resulting colimit's apex
 back, by [reflexivity] against the witnesses, as [PQuot] of
 [PSigma] of the diagram's spaces along [sets_coeq_proj] of a [Sets]
 coequalizer: literally a quotient topology on a disjoint union.
 [PTop_Cocomplete_routes_iso] compares the two routes where both
 are stated: the apexes are isomorphic in [PTopCat], compatibly
 with the injections ([PTop_Cocomplete_routes_iso_injs]), by
 Structure/Limit/Unique.v's [colimit_unique_iso].
 - Cocontinuity (Riehl's Proposition 3.6.2, cocontinuity half).
 [PIndiscrete S], the coarsest topology (the uniform predicates;
 [PIndiscrete_open], at [eq_refl]), into which every setoid map is
 continuous ([pindisc_cont]); [PIndisc : Sets ⟶ PTopCat], Mac
 Lane's D'; [PForget_PIndisc : PForget ⊣ PIndisc], built by
 Theory/Adjunction.v's [Build_Adjunction'] from a hom-set
 isomorphism that is the identity on underlying maps;
 [PForget_Cocontinuous], Adjunction/Continuity.v's
 [left_adjoint_Cocontinuous] at it; and
 [PForget_PreservesColimitCocone], the same per shape with the
 shape's universes named.  The continuity half, from the discrete
 functor, is Instance/Top/Complete.v's [PDisc] and
 [PForget_Continuous].
 - Non-vacuity.  [PTwoIndiscSum] is the coproduct of two copies of
 the indiscrete two-point space [PTwoIndisc].  Its two injections
 differ ([PTwoIndiscSum_injections_differ]); each summand is open
 ([PTwoIndiscSum_summand_open]) and not uniform, so the topology is
 not the indiscrete one ([PTwoIndiscSum_not_indiscrete]: not every
 open is uniform); and the point (true, true) respects the points'
 equality yet is not open ([PTwoIndiscSum_not_discrete]), so it is
 not the discrete one either.  The final topology is computed, not
 collapsed to an extreme.

 STRENGTHS, measured strict first.
 - At [eq_refl]: [PFinal_carrier], [PFinal_open], [pfinal_leg_map],
 [pfinal_desc_map], [PFinalCocone_points], [PFinalCocone_legs],
 [pfinal_cocone_med_map], [PTop_Colimit_lift_apex],
 [PColimit_apex], [PColimit_points], [PColimit_inj],
 [PColimit_med_at], [PSigma_points], [PSigma_open], [psigma_case_at],
 [PIndiscrete_carrier], [PIndiscrete_open], [pindisc_mor_map] and
 [PIndisc_fobj].  [PTop_Cocomplete_via_coproducts_apex] is closed by
 [reflexivity] once its three witnesses are left as evars, so the
 apex equation holds at [eq_refl] at the witnesses Coq finds.
 - Isomorphism, not equality: [PTop_Cocomplete_routes_iso].  The two
 apexes' points have the same underlying type, the sigma over the
 diagram's objects (at [eq_refl], measured in a scratch file), but
 different equalities: [colim_rel], generated by the arrows
 directly, against the equivalence that a [Sets] coequalizer
 generates from a parallel pair indexed by the arrows.  The equation
 of the two point setoids at [eq_refl] is refused in the same
 scratch file, and so is that of the two spaces (Coq: the term
 "eq_refl" has type ... while it is expected to have type ...).
 - Up to [≈]: the universal properties ([psigma_desc], and the
 uniqueness halves of [pfinal_cocone_colimiting] and of the two
 [Cocomplete] inhabitants) and [PTop_Cocomplete_routes_iso_injs].
 - Propositional equivalences: [pfinal_universal],
 [pfinal_one_map_PQuot] and [PTop_colimit_open_iff_final].  The last
 cannot be Leibniz: the opens of an arbitrary colimit are whatever
 predicate its apex carries, and only their extension is fixed.
 - Four proofs end [Defined], counted by token, and one of them is
 load-bearing, measured by closing each alone [Qed] in a scratch
 copy of this file: [pfinal_cocone_colimiting], whose mediator the
 two triangle readbacks unfold ([pfinal_cocone_med_map] is refused,
 and with it removed [PColimit_med_at] is refused as well).
 [psigma_desc], [PTop_Cocomplete_via_coproducts_apex] and
 [PForget_PIndisc] are [Defined] by the data convention only: closed
 [Qed], the copy compiles.

 UNIVERSES, read by [About] under [Set Printing Universes], stdlib caps
 ([o <= compose.u0] and the like) left out except where one is strict.
 - [PFinal@{o i}] and [PIndiscrete@{o}]: empty blocks.  The final
 topology's index universe [i] is free; so is the shape universe of
 the recipe.
 - [pfinal_cocone_colimiting@{o so s r r' x x' u}] has type
 [IsColimitCocone@{x' x' r' s o so} N →
 IsColimitCocone@{x x r s o so} (PFinalCocone F N)]: the shape's
 object universe [s] is bounded only by [s <= r] and [s <= r'], so
 the recipe holds at EVERY shape universe, above the points
 included (there, under informative excluded middle, not every
 diagram has a [Sets] colimit to consume:
 Instance/Top/Cocomplete/Refutations.v's [Sets_not_cocomplete_IEM]
 refutes cocompleteness of [Sets] above its carriers under
 informative excluded middle, through this very lemma).  The one
 strict bound besides [o < so] is [o < u], Theory/Functor.v's
 [Compose@{u u0 u1 u2 u3}]'s own [u3 < u2] at [PForget ◯ F].  The
 two universal properties sit at independent levels [r'] and [r]
 because the statement names them.  Left to inference, as measured
 in a scratch copy with the annotations removed, the two
 [IsColimitCocone] instances elaborate as one
 ([IsColimitCocone@{u0 u0 u1 s o so}] on both sides), and then
 [PTop_Colimit_lift] carries [r = r'] and [PColimit] carries [r = o],
 the level at which Instance/Sets/Cocomplete.v's
 [Sets_Colimit@{u u0 u1}] builds its record ([Colimit@{u0 u u0
 u1}]).  Annotated, [PTop_Colimit_lift@{r r' s o so u u0 u1}]
 maps [Colimit@{r' s o so}] to [Colimit@{r s o so}] with no
 equation.
 - [PColimit@{r s o so u u0}] and
 [PTop_Cocomplete@{r s o so u u0} : Cocomplete@{r s o so}
 PTopCat@{o so}]: the block has [s <= o], which is [Sets_Colimit]'s
 own [u <= u0] (the sigma over the shape's objects must be a set at
 the carriers' level), [s <= r] and [o <= r] ([Cocomplete]'s own),
 [r <= u] and [so <= u] bounding an auxiliary of
 [PTop_Colimit_lift], and [o < u0], [Compose]'s own bound again;
 [r] is otherwise free.  Measured in the scratch file of
 Instance/Top/Complete.v's boundary paragraph (the six files of #458
 after the union of their import lists, universes named as here):
 [PTop_Cocomplete] read at [Cocomplete@{r o o so}] under a declared
 [o < r] is accepted, at a shape universe [s < o] is accepted, at
 [o := Set] is accepted, and at [o < s] is refused ("universe
 inconsistency: Cannot enforce o = <1> because o < s <= <1>", the
 generated universe written <1>).
 - [PTop_colimit_open_iff_final@{o so s r u}] carries two strict
 stdlib caps, [o < projections.u0] and [o < projections.u1].  Their
 first carrier is [PForget_PreservesColimitCocone], whose block has
 [o < u1] ([Compose]'s own bound at [PForget ◯ K]) with
 [u1 <= projections.u0] and [u1 <= projections.u1].
 - [PSigma@{o i u}]: [i <= o] (the sigma carrier sits at the points'
 universe) and [o < u], which is Instance/Sets/Products.v's
 [Sets_icoprod_inj@{u u0}]'s own [u < u0] (its arrow lives in
 [Sets@{u u0}]).  [PTop_HasIndexedCoproducts@{o so u u0 u1} :
 HasIndexedCoproducts@{u u0 o so o} PTopCat@{o so}], the index
 universe [u0] with [u0 <= o] and the class's own [u0 < u].
 - [PTop_Cocomplete_via_coproducts@{o so u u0 u1 u2 u3 u4} :
 Cocomplete@{o o o so} PTopCat@{o so}]: the shape's objects and the
 colimit record both at the points' universe, the type of
 [Cocomplete_from_coproducts_coequalizers@{u u0 u1 u2}] itself
 ([Cocomplete@{u0 u0 u0 u2}]).  [Cocomplete] is invariant in those
 slots: read at [r > o] it is refused ("Cannot enforce o = r because
 o < r"), at [s < o] refused ("Cannot enforce o = s because s < o"),
 both in the same scratch file; the order of the two universes in
 such a message varies with the environment that prints it.  So
 the direct route is the wider statement, every [s <= o] against
 [s = o], and the comparison
 [PTop_Cocomplete_routes_iso] is stated at shapes
 [Category@{o o o}].
 - [PIndisc@{o so}]: [PTopCat]'s bounds and stdlib caps.
 [PForget_PIndisc@{o so u u0}] adds [o < u]: [u] is the object
 universe of the [Sets] in which the hom-set isomorphism lives
 ([pforget_indisc_iso@{o so u}] is an [Isomorphism@{u o o}]), and
 [o < u] is that [Sets]' own bound.
 [PForget_PreservesColimitCocone@{s o so u u0 u1 u2 u3}] at
 [J : Category@{s o o}]: [s] is bounded only by [s <= u], [u] the
 level of the colimit property; accepted at [o < s] in the same
 scratch file.  [PForget_Cocontinuous] is [CocontinuousFunctor@{u
 u1 u1 u0 u1 u2 o so so u3} PForget@{o so}], with the shapes
 quantified inside.
 - [Set]: no universe of this file is pinned at [Set] and no block
 carries an equation, over the [About] output of all 78 of its
 constants (its [Print Module] listing, the seven [Program]
 obligations included; it declares no record or inductive).
 [Set < so] occurs in 41 blocks, inherited from [PTopCat], whose
 block records [PTop]'s sort with it; [o < so] implies it.
 [Set < Projections.u0] occurs in the 4 blocks of the book route
 ([PTop_Cocomplete_via_coproducts], its apex readback, the routes
 isomorphism and its injections), inherited from Instance/Top/
 Subspace.v's [PTop_HasCoequalizers], whose block carries it
 beside the [so <= Projections.u0] that implies it.

 ROUTE AND COST.  Closure: 93 [Category.*] modules excluding this file
 ([Print Libraries] on a file requiring it), against 81 for
 Instance/Top/Subspace.v; the 11 added beyond Subspace.v itself are
 the [Sets] colimit and coproducts (Instance/Sets/Cocomplete.v,
 Instance/Sets/Products.v and, through them, Instance/Sets/Cocartesian.v,
 Instance/Sets/Cartesian/Closed.v and Structure/Cartesian/Closed.v),
 Structure/Complete.v, Structure/Limit/Coproduct.v,
 Structure/Limit/Product.v, Structure/Limit/FromProducts.v,
 Structure/Limit/Unique.v and Adjunction/Continuity.v.

 NOT DELIVERED.  Cocompleteness (colimits of every shape) of the
 Type-valued [Top] at shapes at or below its points (its coequalizers
 and small-index coproducts are Instance/Top/Cocomplete/TypeValued.v's,
 which records the walls; the question is open there, not refuted);
 any comparison with
 the Type-valued binary coproducts and pushouts of
 Instance/Top/Coproduct.v and Instance/Top/Pushout.v; Mac Lane's
 Exercise 2 (that [PIndisc] has no right adjoint) and his two worked
 colimits of book p. 134 (the open cover and the collapse X/A;
 CORRECTION (#459): for the collapse, this entry holds of this file
 only — Instance/Top/Quotient.v builds it, over the Type-valued
 [Top]); Riehl's
 remark that the disjoint union of bases is a basis; functoriality of
 the colimit in the diagram; a strict creation statement (the lift of a
 colimit unique up to equality of spaces): [PTop_colimit_open_iff_final]
 fixes the opens up to [<->]; and the book route at shapes other than
 [Category@{o o o}]. 

 --------
 Mac Lane，《数学工作者的范畴论》，第2版（GTM 5），§V.9，从页面图像阅读：商构造，书本第133-134页（PDF第142-143页），以及结束此部分的段落在书本第134页（PDF第143页），"现在命题1仅从范畴的公理中证明，因此其对偶命题也成立。这个对偶命题和上述伴随定理证明了Top具有余等化子。类似的构造会产生Top中的余积（= 不相交并集）和一般余极限"（目录ID maclane:V.9:remark2，#458的）；以及练习2，书本第135页（PDF第144页），它将不可分离函子命名为“对应忘记函子的右伴随 D' : Set → Top”（练习本身未提供） Riehl，《语境中的范畴论》，Dover 2016，§3.6，印刷第116页（PDF第136)，从 PDF 文本中读取：命题 3.6.2，“基础集合函子 U : Top → Set 是连续且协连续的”（riehl:3.6:prop2，其协连续部分在此），在其证明中，“余积是通过赋予不相交并集…以最细拓扑，使得每个余积-包含…都是连续的”以及“定理 4.6.2 表明余极限必须以这种方式构造”；以及例 3.6.3，“Top 中的任意极限或余极限都可以构造…通过形成底层集合图的极限或余极限，然后用最粗（在极限情况下）或最细（在余极限情况下）的拓扑对所得空间进行拓扑化，使得极限或余极锥的各个腿是连续的（riehl:3.6:example3，其余极限部分在这里）
 nLab:  https://ncatlab.org/nlab/show/Top 
 nLab:  https://ncatlab.org/nlab/show/initial+topology 
 nLab:  https://ncatlab.org/nlab/show/quotient+space 
 nLab:  https://ncatlab.org/nlab/show/topological+concrete+category 
 nLab:  https://ncatlab.org/nlab/show/cocomplete+category背景。余极限是拓扑学的粘合方式。麦克莱恩自己在书第134页的例子是一个开覆盖，它将一个空间表示为其各个部分及它们的两两交集的余极限，以及通过将一个子集压缩为一点而得到的空间 X/A；商空间、附加空间和胞腔复形都是以相同的方式构建的。它们每一个都通过一个配方计算：形成底层集合的余极限，并赋予它一个最细拓扑，使得余极限余锥的每条边都是连续的，这就是该族边的最终拓扑，其中商拓扑就是单个映射的情况（nLab 的初始拓扑页面提供了这两种形式，如 Instance/Top/Subspace.v 的页眉所记录）。Riehl 的证明解释了为什么不可能发生其他情况：底层集函子有一个右伴随，即最粗拓扑，因此它保持余极限，并且任意空间余极限的底层集合就是底层集合的余极限。忘却函子以这种方式提升底层集合的每个（余）极限的范畴是 nLab 所称的拓扑具体范畴，这是配方成为关于函子而不是空间的定理的背景。Mac Lane 采取了另一条经典路线。命题 1
 （Instance/Top/Subspace.v）从切割的陪伴构建等化器，其对偶从商拓扑构建余等化器，“类似的构造产生余积”；一个具有余积和余等化器的范畴通过其定理 V.2.1 的对偶是余完备的，该定理在树中作为 Structure/Limit/FromProducts.v 的 [Cocomplete_from_coproducts_coequalizers]（#416）。下面给出了两种方法，并进行了比较。为什么 [PTopCat]。Instance/Top/Prop.v 的头部解释了为什么类型值 [Top] 将其 Hom 严格放置在其点之上，以及 Prop 值 [PTop] 的作用。对于余极限，其结果在 Instance/Top/Cocomplete/TypeValued.v 中衡量，该文件构建了可以在 [Top] 上形成的部分（在点上或以下索引的余积，以及在 Instance/Top/Subspace/TypeValued.v 的 [TQuot] 上的余等化器）并记录阻止其余部分的三道墙；Instance/Top/Cocomplete/Refutations.v 在信息排中值律（或空间的可判定等式）下，否定了每个点上方形宇宙中两个范畴的余完备性，并在携带箭头索引的任何形状宇宙中也进行否定。此文件中的所有内容均属于 [PTopCat]，由维护者在 2026-09-24 于 #458 上决定；该问题的 [Top_Cocomplete] 在此为 [PTop_Cocomplete]，这是一种已说明的名称和类别偏差。这里是什么。- 最终拓扑。[PFinal S Ix X f] 是集合 [S]，并带有使每个 [f k : X k → S] 连续的最精细拓扑，对于任何宇宙中的索引类型 [Ix]：当一个谓词遵循 [S] 的等式并且其沿每个 [f k] 的原像是开放的（[PFinal_open]，在 [eq_refl] 上）时，它是开放的。[pfinal_universal] 是任意空间上的普遍性质 [Z] 输出，双向；[pfinal_desc] 是它的书本形式，从最终拓扑映射；[pfinal_finest] 表示它是最精细的（任何具有沿每个 [f k] 的开前像的等价谓词族，其成员是它的开集，该族不要求是拓扑）；[pfinal_one_map_PQuot] 表示 Instance/Top/Subspace.v 的商拓扑 [PQuot X T q] 是它的单映射情况，具有相同的开集。- 作为一般引理的配方（Riehl 的例 3.6.3，余极限半部分）。对于图 [F : D ⟶ PTopCat] 以及基于 [PForget ◯ F] 在 [Sets] 中的任意余锥 [N]，ZWZ33WZZ 是 [N] 的顶点，并且配备了 [N] 的腿的最终拓扑；它在 [PForget] 下的像具有 [N] 的顶点和腿（[PFinalCocone_points]，[PFinalCocone_legs]）。[pfinal_cocone_colimiting]：如果 [N] 在 [Sets] 中是余极限的，提升后的余锥在 [PTopCat] 的每个形状宇宙中也是余极限的，并且它的中介正是 [Sets] 的中介（[pfinal_cocone_med_map]）。[pfinal_cocone_colimiting_reflect] 是逆命题，通过下面 [PForget] 的余连续性，所以 [N] 恰好在其提升为余极限时才是余极限。[PTop_Colimit_lift] 是 ZZWT50WZZ 点记录的配方。[PTop_colimit_open_iff_final] 是配方，在 Riehl 的“必须以这种方式构建”形式中：每个空间的每个余极限的开集，无论它是如何构建的，都恰好是其各支的点的最终拓扑的开集。这个配方只陈述一次，适用于每种形状；下面的余积重用其 [PFinal]，而不是自己的拓扑；积、等化器以及配方的极限部分是 #458（Instance/Top/Complete.v）中的极限侧。——直接参考备注 2。[PColimit F] 是 Instance/Sets/Cocomplete.v 中 [Sets_Colimit] 的 [PTop_Colimit_lift] 的 [PForget ◯ F]，[PTop_Cocomplete] 将其打包：[PTopCat] 是余完备的。它的顶点
 在 [Sets_colim_obj] 上读取为 [eq_refl] 的最终拓扑
 对于腿 [Sets_colim_inj]（[PColimit_apex]），它的点为
 [Sets_colim_obj]（[PColimit_points]），它的注入为
 [Sets_colim_inj]（[PColimit_inj]），并且进入余圆锥的中介物
 [M] 将 [d] 处的和的点 [x] 发送到 [M] 在 [d] 的腿上
 应用于 [x]（[PColimit_med_at]），三角形是
 Instance/Sets/Cocomplete.v 的 [Sets_colim_triangle] 对 [Sets] 所述的。- 余积。[PSigma Ix X] 是不相交的并集 [Sets_icoprod_obj]，其点具有最终拓扑，用于其注入 ([PSigma_points], [PSigma_open], 在 [eq_refl]); [psigma_inj], [psigma_case] (它在某个分量点的值, [psigma_case_at], 在 [eq_refl]), [psigma_desc], 和 [PTop_HasIndexedCoproducts]，每个索引宇宙位于点或点以下。- 书中的路线的备注 2。[PTop_Cocomplete_via_coproducts] 是 [Cocomplete_from_coproducts_coequalizers] 的输入 [PTop_HasIndexedCoproducts] 和 Instance/Top/Subspace.v 的 [PTop_HasCoequalizers]，这是商拓扑下命题 1 的对偶：书中的句子，逐项。[PTop_Cocomplete_via_coproducts_apex] 将结果余极的顶点读回，通过 [reflexivity] 针对见证者，如 [PQuot] 所述 [PSigma] 的图空间沿 [sets_coeq_proj] 的 [Sets] 协同等化子：字面意思是在不相交并集上的商拓扑。[PTop_Cocomplete_routes_iso] 比较了两条路线，其中两条路线都被陈述：[PTopCat] 中的顶点是同构的，与注入 ([PTop_Cocomplete_routes_iso_injs]) 兼容，由 Structure/Limit/Unique.v 的 [colimit_unique_iso] 给出。- Kokontinuity（Riehl 命题 3.6.2，kokontinuity 部分）。[PIndiscrete S]，最粗拓扑（统一谓词；[PIndiscrete_open]，在 [eq_refl]），其中每个集合类映射都是连续的（[pindisc_cont]）；[PIndisc : Sets ⟶ PTopCat]，Mac Lane 的 D'；[PForget_PIndisc : PForget ⊣ PIndisc]，由 Theory/Adjunction.v 的 [Build_Adjunction'] 构建，从一个在底层映射上是恒等映射的 Hom-集同构；[PForget_Cocontinuous]，Adjunction/Continuity.v 的 [left_adjoint_Cocontinuous] 在其中；以及 [PForget_PreservesColimitCocone]，对应形状相同，并且形状的宇宙已命名。连续性部分，来自离散函子，是 Instance/Top/Complete.v 的 [PDisc] 和 [PForget_Continuous]。- 非空性。[PTwoIndiscSum] 是两个不可分二点空间 [PTwoIndisc] 的余积。它的两个嵌入不同（[PTwoIndiscSum_injections_differ]）；每个直和都是开集（[PTwoIndiscSum_summand_open]）且非均匀，因此拓扑不是不可分的拓扑（[PTwoIndiscSum_not_indiscrete]：并非每个开集都是均匀的）；且点 (true, true) 尊重点的相等性，但不是开集（[PTwoIndiscSum_not_discrete]），因此它也不是离散拓扑。最终拓扑被计算出来，而不是被坍缩到极端。优势，先严格测量。- 在 [eq_refl] ：[PFinal_carrier]，[PFinal_open]，[pfinal_leg_map]，[pfinal_desc_map]，[PFinalCocone_points]，[PFinalCocone_legs]，[pfinal_cocone_med_map]，[PTop_Colimit_lift_apex]，[PColimit_apex]，[PColimit_points]，[PColimit_inj]，[PColimit_med_at]，[PSigma_points]，[PSigma_open]，[psigma_case_at]，[PIndiscrete_carrier]，[PIndiscrete_open]，[pindisc_mor_map] 和 [PIndisc_fobj]。[PTop_Cocomplete_via_coproducts_apex] 在其三个见证者被保留为 evars 后被 [reflexivity] 关闭，因此在 Coq 找到的见证者处 [eq_refl] 的顶点方程成立。- 同构，而非等同：[PTop_Cocomplete_routes_iso]。两个顶点的点具有相同的基础类型，即图形对象上的 sigma（在 [eq_refl] 处，在一个临时文件中测量），但具有不同的等式：[colim_rel]，由箭头直接生成，与由箭头索引的平行对生成的 [Sets] 共等化器的等价关系不同。在同一个临时文件中，两个点集的方程 [eq_refl] 被拒绝，两个空间的方程也是如此（Coq：术语“eq_refl”的类型是…，但期望类型是…）。- 到 [≈]：泛性质（[psigma_desc]，以及 [pfinal_cocone_colimiting] 的唯一性一半和两个 [Cocomplete] 元素）及 [PTop_Cocomplete_routes_iso_injs]。- 命题等价：[pfinal_universal]、[pfinal_one_map_PQuot] 和 [PTop_colimit_open_iff_final]。最后一个不能是莱布尼茨：任意余极限的开集就是其顶点所携带的任意谓词，只有它们的扩展是固定的。——四个证明结束  [Defined] ，按记号计数，其中一个是承重的，通过在这个文件的临时副本中单独关闭每个  [Qed] 来测量：  [pfinal_cocone_colimiting] ，其调解者是两个三角形的回读展开（[pfinal_cocone_med_map] 被拒绝，并且随着它被移除 [PColimit_med_at] 也被拒绝）。[psigma_desc] ， [PTop_Cocomplete_via_coproducts_apex] 及 [PForget_PIndisc] 仅根据数据惯例为 [Defined] ：关闭 [Qed] ，副本可编译。宇宙，由 [About] 在 [Set Printing Universes] 下读取，标准库大写字母（例如 [o <= compose.u0] 等）被省略，除非严格需要。- [PFinal@{o i}] 和 [PIndiscrete@{o}]：空块。最终拓扑的索引宇宙 [i] 是自由的；配方的形状宇宙也是自由的。- [pfinal_cocone_colimiting@{o so s r r' x x' u}] 的类型是
 [IsColimitCocone@{x' x' r' s o so} N →
 IsColimitCocone@{x x r s o so} (PFinalCocone F N)]: 该形状的对象宇宙 [s] 仅受 [s <= r] 和 [s <= r'] 的限制，因此该公式在每个形状宇宙中都成立，超过所包含的点（在那里，在信息排中律下，并非每个图都有一个 [Sets] 上极限可使用：
 Instance/Top/Cocomplete/Refutations.v 文件中的 [Sets_not_cocomplete_IEM] 通过这个引理否定了在信息排中律下 [Sets] 在其承载对象上的余完备性）。除了 [o < so] 外，唯一的严格界限是 [o < u]，Theory/Functor.v 文件中 [Compose@{u u0 u1 u2 u3}] 在 [PForget ◯ F] 上自身的 [u3 < u2]。这两个通用性质位于独立的层次 [r'] 和 [r]，因为陈述命名了它们。如果依赖推理测量，在移除注释的草稿副本中，这两个 [IsColimitCocone] 实例被展开为一个（双方的 [IsColimitCocone@{u0 u0 u1 s o so}]），然后 [PTop_Colimit_lift] 携带 [r = r']，而 [PColimit] 携带 [r = o]，这是 Instance/Sets/Cocomplete.v 的 [Sets_Colimit@{u u0 u1}] 构建其记录 ([Colimit@{u0 u u0 u1}]) 的层次。带注释的情况下，[PTop_Colimit_lift@{r r' s o so u u0 u1}] 将 [Colimit@{r' s o so}] 映射到 [Colimit@{r s o so}]，且没有等式。-  [PColimit@{r s o so u u0}] 以及
 [PTop_Cocomplete@{r s o so u u0} : Cocomplete@{r s o so}
 PTopCat@{o so}]：该块具有 [s <= o]，它是 [Sets_Colimit] 自身的 [u <= u0]（形状对象上的 sigma 在承载者层面必须是一个集合），[s <= r] 和 [o <= r]（[Cocomplete] 自身的），[r <= u] 和 [so <= u] 对 [PTop_Colimit_lift] 的一个辅助进行界定，以及 [o < u0]，再次是 [Compose] 自身的界限；[r] 否则是自由的。在 Instance/Top/Complete.v 的边界段的临时文件中测量（在合并导入列表之后的 #458 的六个文件，宇宙命名如这里所示）：[PTop_Cocomplete] 在 [Cocomplete@{r o o so}] 中读取，在声明的 [o < r] 下被接受，在形状宇宙 [s < o] 下被接受，在 [o := Set] 下被接受，而在 [o < s] 下被拒绝（"宇宙不一致：无法强制 o = <1> 因为 o < s <= <1>"，生成的宇宙写为 <1>）。- [PTop_colimit_open_iff_final@{o so s r u}] 拥有两个严格的 stdlib 上限，[o < projections.u0] 和 [o < projections.u1]。它们的第一个承载者是 [PForget_PreservesColimitCocone]，其块具有 [o < u1]（[Compose] 在 [PForget ◯ K] 的自身边界）以及 [u1 <= projections.u0] 和 [u1 <= projections.u1]。-  [PSigma@{o i u}] :  [i <= o] （sigma载体位于点的宇宙）以及  [o < u] ，它是 Instance/Sets/Products.v 中 [Sets_icoprod_inj@{u u0}] 自身的 [u < u0] （它的箭头位于 [Sets@{u u0}]）。[PTop_HasIndexedCoproducts@{o so u u0 u1} : HasIndexedCoproducts@{u u0 o so o} PTopCat@{o so}]，索引宇宙 [u0] 伴随 [u0 <= o] 以及该类自身的 [u0 < u]。- [PTop_Cocomplete_via_coproducts@{o so u u0 u1 u2 u3 u4} : Cocomplete@{o o o so} PTopCat@{o so}]：图形的对象和余极限记录都位于点的宇宙，[Cocomplete_from_coproducts_coequalizers@{u u0 u1 u2}] 本身的类型（[Cocomplete@{u0 u0 u0 u2}]）。[Cocomplete] 在那些槽中是不变的：在 [r > o] 处读取时被拒绝（“无法强制 o = r 因为 o < r”），在 [s < o] 处被拒绝（“无法强制 o = s 因为 s < o”），两者都在同一个临时文件中；这种消息中两个宇宙的顺序因打印它的环境而异。因此，直接途径是更宽泛的陈述，每个 [s <= o] 对应 [s = o]，并且比较 [PTop_Cocomplete_routes_iso] 在形状 [Category@{o o o}] 上说明。 - [PIndisc@{o so}]：[PTopCat] 的界限和标准库上限。[PForget_PIndisc@{o so u u0}] 添加了 [o < u]：[u] 是 [Sets] 的对象宇宙，其中同态集合同构存在（[pforget_indisc_iso@{o so u}] 是一个 [Isomorphism@{u o o}]），并且 [o < u] 是 [Sets] 自身的界限。[PForget_PreservesColimitCocone@{s o so u u0 u1 u2 u3}] 在 [J : Category@{s o o}] ：[s] 仅被 [s <= u]、[u] 所限制，为余极限性质的层级；在同一临时文件中的 [o < s] 被接受。[PForget_Cocontinuous] 是 [CocontinuousFunctor@{u u1 u1 u0 u1 u2 o so so u3} PForget@{o so}]，形状在内部量化。- [Set] ：此文件中的任何宇宙在 [Set] 均未固定，并且没有区块携带方程，超过它的所有78个常数的 [About] 输出（其 [Print Module] 列表，包括七个 [Program] 义务；它未声明记录或归纳）。[Set < so] 出现在41个区块中，由 [PTopCat] 继承，其区块记录了 [PTop] 的类型；[o < so] 意味着它。[Set < Projections.u0] 出现在书籍路线的 4 个区块中（[PTop_Cocomplete_via_coproducts]，其顶点回读，该路线的同构及其注入），继承自 Instance/Top/Subspace.v 的 [PTop_HasCoequalizers]，其区块在 [so <= Projections.u0] 旁携带它，[so <= Projections.u0] 表明了它的含义。路由和成本。关闭：93 个 [Category.*] 模块（不包括此文件）（[Print Libraries] 在需要的文件上），相比于 Instance/Top/Subspace.v 的 81 个；在 Subspace.v 本身之外增加的 11 个是 [Sets] 的余极限和余积（Instance/Sets/Cocomplete.v、Instance/Sets/Products.v，以及通过它们的 Instance/Sets/Cocartesian.v、Instance/Sets/Cartesian/Closed.v 和 Structure/Cartesian/Closed.v）、Structure/Complete.v、Structure/Limit/Coproduct.v、Structure/Limit/Product.v、Structure/Limit/FromProducts.v、Structure/Limit/Unique.v 和 Adjunction/Continuity.v。未交付。类型值 [Top] 在其点及以下的形状上的共完备性（每种形状的余极限）（其等化器和小指标余积是 Instance/Top/Cocomplete/TypeValued.v 的记录，其记录壁；这个问题尚未解决，未被反驳）；与 Instance/Top/Coproduct.v 和 Instance/Top/Pushout.v 的类型值二元余积和推出的任何比较；Mac Lane 的练习 2（[PIndisc] 没有右伴随函数）以及他书中两条已处理的余极限 p.134（开覆盖和塌陷 X/A；
 修正（#459）：对于塌陷，此条目仅适用于此文件 —— Instance/Top/Quotient.v 构建它，在类型值 [Top] 上）；Riehl 的评论是底的析取并集是一个基；图中的余极限的函子性；一个严格的创建声明（余极限的提升在空间相等的情况下唯一）：ZWZ277WZZ 修正了到 [<->] 的开集；以及书本路径在 [Category@{o o o}] 以外的形状上。
*)

#[local] Obligation Tactic := idtac.

(* * ** The final topology of a family of maps into a setoid / * ** 映射族到一个集合化的最终拓扑 *)

Section Final.

Universes o i.

Context (S : SetoidObject@{o o}) (Ix : Type@{i}) (X : Ix → PTop@{o})
        (f : ∀ k : Ix, SetoidMorphism@{o o o} (X k) S).

(* A predicate on [S] is open when it respects the equality of [S] and its preimage along every [f k] is open. / 当一个 ZZ W0WZZ 上的谓词尊重 ZZ W1WZZ 的等式并且其沿每个 ZZ W2WZZ 的原像是开放时，它是开放的。 *)
Definition pfinal_open (V : S → Prop) : Prop :=
  (∀ s t : S, s ≈ t → V s → V t) /\
  (∀ k : Ix, POpen (X k) (fun x => V (f k x))).

Lemma pfinal_open_respects (U V : S → Prop) :
  (∀ s, U s <-> V s) → pfinal_open U → pfinal_open V.
Proof.
  intros H [Hp Ho]; split.
  - intros s t e v. apply (proj1 (H t)), (Hp s t e), (proj2 (H s)), v.
  - intro k. exact (popen_respects (X k) _ _ (fun x => H (f k x)) (Ho k)).
Qed.

Lemma pfinal_open_proper (U : S → Prop) :
  pfinal_open U → ∀ s t : S, s ≈ t → U s → U t.
Proof. intros [Hp _]; exact Hp. Qed.

Lemma pfinal_open_union (F : (S → Prop) → Prop) :
  (∀ V, F V → pfinal_open V) →
  pfinal_open (fun s => ex (fun V => F V /\ V s)).
Proof.
  intro HF; split.
  - intros s t e [V [FV v]]. exists V; split; [exact FV|].
    exact (proj1 (HF V FV) s t e v).
  - intro k.
    apply (popen_respects (X k)
             (fun x => ex (fun U => ex (fun V => F V /\
                                          ∀ y, U y <-> V (f k y)) /\ U x))).
    + intro x; split.
      * intros [U [[V [FV HUV]] u]]. exists V.
        split; [exact FV|exact (proj1 (HUV x) u)].
      * intros [V [FV v]]. exists (fun y => V (f k y)).
        split; [|exact v]. exists V; split; [exact FV|].
        intro y; exact (iff_refl _).
    + apply popen_union. intros U [V [FV HUV]].
      apply (popen_respects (X k) (fun y => V (f k y))).
      * intro y; exact (iff_sym (HUV y)).
      * exact (proj2 (HF V FV) k).
Qed.

Lemma pfinal_open_whole : pfinal_open (fun _ => True).
Proof. split; [intros; exact I|intro k; exact (popen_whole (X k))]. Qed.

Lemma pfinal_open_inter (U V : S → Prop) :
  pfinal_open U → pfinal_open V → pfinal_open (fun s => U s /\ V s).
Proof.
  intros [HpU HoU] [HpV HoV]; split.
  - intros s t e [u v]; exact (conj (HpU s t e u) (HpV s t e v)).
  - intro k; exact (popen_inter (X k) _ _ (HoU k) (HoV k)).
Qed.

(* A record literal over the five lemmas, so that the points and the opens read back at [eq_refl]. / 在这五个引理上有一个记录字面值，这样分数和开放项就可以在 [eq_refl] 上读回。 *)
Definition PFinal : PTop@{o} := {|
  pt_carrier     := S;
  POpen          := pfinal_open;
  popen_respects := pfinal_open_respects;
  popen_proper   := pfinal_open_proper;
  popen_union    := pfinal_open_union;
  popen_whole    := pfinal_open_whole;
  popen_inter    := pfinal_open_inter
|}.

Example PFinal_carrier : pt_carrier PFinal = S := eq_refl.

Example PFinal_open (V : S → Prop) :
  POpen PFinal V
  = ((∀ s t : S, s ≈ t → V s → V t) /\
     (∀ k : Ix, POpen (X k) (fun x => V (f k x)))) := eq_refl.

Lemma pfinal_leg_cont (k : Ix) : @PCont (X k) PFinal (f k).
Proof. intros V HV; exact (proj2 HV k). Qed.

Definition pfinal_leg (k : Ix) : PMor@{o} (X k) PFinal :=
  @Build_PMor (X k) PFinal (f k) (pfinal_leg_cont k).

Example pfinal_leg_map (k : Ix) : pmap (pfinal_leg k) = f k := eq_refl.

(*
 The universal property, over ARBITRARY spaces [Z] mapping out: a setoid
 map out of [S] is continuous from the final topology exactly when its
 composite with every [f k] is continuous. 

 --------
 普遍性质，对于任意空间  [Z]  的映射：从  [S]  映射出去是连续的，当且仅当它与每个  [f k]  的复合是连续的情况下，从最终拓扑来看。
*)
Lemma pfinal_universal (Z : PTop@{o}) (g : SetoidMorphism@{o o o} S Z) :
  @PCont PFinal Z g <->
  (∀ k, @PCont (X k) Z (setoid_morphism_compose@{o o o} g (f k))).
Proof.
  split.
  - intros Hg k W HW. exact (proj2 (Hg W HW) k).
  - intros Hc W HW; split.
    + intros s t e w.
      exact (popen_proper Z W HW (g s) (g t) (proper_morphism g s t e) w).
    + intro k; exact (Hc k W HW).
Qed.

(* The book's form of it: the map out of the final topology. / 这本书的形式：最终拓扑的映射。 *)
Definition pfinal_desc (Z : PTop@{o}) (g : SetoidMorphism@{o o o} S Z)
  (Hg : ∀ k, @PCont (X k) Z (setoid_morphism_compose@{o o o} g (f k))) :
  PMor@{o} PFinal Z :=
  @Build_PMor PFinal Z g (proj2 (pfinal_universal Z g) Hg).

Example pfinal_desc_map (Z : PTop@{o}) (g : SetoidMorphism@{o o o} S Z)
  (Hg : ∀ k, @PCont (X k) Z (setoid_morphism_compose@{o o o} g (f k))) :
  pmap (pfinal_desc Z g Hg) = g := eq_refl.

(*
 It is the FINEST topology making every [f k] continuous: any family of
 predicates on [S] respecting its equality, each with open preimages
 along every [f k], consists of opens of the final topology.  The family
 need not be a topology. 

 --------
 它是最优的拓扑，使每个 [f k] 连续：对 [S] 上的每一族谓词，只要它们尊重其等式，并且沿每个 [f k] 的原像是开集，那么它们就由最终拓扑的开集组成。该族不必是一个拓扑。
*)
Lemma pfinal_finest (T : (S → Prop) → Prop)
  (Hp : ∀ U, T U → ∀ s t : S, s ≈ t → U s → U t)
  (Hc : ∀ U, T U → ∀ k, POpen (X k) (fun x => U (f k x))) :
  ∀ U, T U → POpen PFinal U.
Proof. intros U HU; exact (conj (Hp U HU) (Hc U HU)). Qed.

End Final.

(* The quotient topology of Instance/Top/Subspace.v is the one-map case: [PQuot X T q] and the final topology of the single map [q] have the same opens. / Instance/Top/Subspace.v 的商拓扑是单映射情况：[PQuot X T q]，单映射 [q] 的极限拓扑具有相同的开集。 *)
Lemma pfinal_one_map_PQuot@{o +} (X : PTop@{o}) (T : SetoidObject@{o o})
  (q : SetoidMorphism@{o o o} X T) (V : T → Prop) :
  POpen (PQuot X T q) V
  <-> POpen (PFinal T Datatypes.unit (fun _ => X) (fun _ => q)) V.
Proof.
  split.
  - intros [Hp Ho]; split; [exact Hp|intros _; exact Ho].
  - intros [Hp Ho]; split; [exact Hp|exact (Ho tt)].
Qed.

(* * ** The recipe: the final topology on a colimit of the points / * ** 配方：点上的余极限的最终拓扑 *)

Section Recipe.

Universes o so s.
Constraint o < so.

Context {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so}).

Local Notation G := (PForget@{o so} ◯ F).

Section OverACocone.

Context (N : Cocone G).

(* The final topology on the apex of [N] for its legs. / [N] 顶点上腿部的最终拓扑结构。 *)
Definition pfinal_cocone_obj : PTop@{o} :=
  PFinal (vertex_obj[N]) (obj[D]) (fun d => F d) (fun d => cocone_inj N d).

Definition pfinal_cocone_inj (d : D) :
  F d ~{PTopCat@{o so}}~> pfinal_cocone_obj :=
  pfinal_leg _ _ _ _ d.

Program Definition PFinalCocone : Cocone F := {|
  vertex_obj := pfinal_cocone_obj;
  coneFrom   := {| vertex_map := pfinal_cocone_inj |}
|}.
Next Obligation.
  intros d d' g x.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) d d' g x).
Qed.

(* The lifted cocone forgets to [N] on the nose: its image under [PForget] has [N]'s apex and [N]'s legs. / 提升的余锥在鼻子上忘记了 [N]：它在 [PForget] 下的像有 [N] 的顶点和 [N] 的腿。 *)
Example PFinalCocone_points :
  vertex_obj[FCocone PForget@{o so} PFinalCocone] = vertex_obj[N] := eq_refl.

Example PFinalCocone_legs (d : D) :
  cocone_inj (FCocone PForget@{o so} PFinalCocone) d = cocone_inj N d
  := eq_refl.

End OverACocone.

End Recipe.

(*
 THE RECIPE, as a lemma: if [N] is a colimiting cocone of the points,
 the final topology for its legs makes the lifted cocone colimiting.
 The two universal properties are stated at independent levels. 

 --------
 配方，作为一个引理：如果 [N] 是这些点的余极限锥，那么其各腿的极限拓扑使得提升后的锥成为余极限。两个普适性质在独立的层次上陈述。
*)
Lemma pfinal_cocone_colimiting@{o so s r r' x x' +| o < so +}
  {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so})
  (N : Cocone (PForget@{o so} ◯ F))
  (HN : IsColimitCocone@{x' x' r' s o so} N) :
  IsColimitCocone@{x x r s o so} (PFinalCocone F N).
Proof.
  intro M.
  pose proof (colimitcocone_ump HN (FCocone PForget@{o so} M)) as U.
  unshelve eapply Build_Unique.
  - refine (pfinal_desc _ _ _ _ (vertex_obj[M]) (unique_obj U) _).
    intro d.
    apply (pcont_respects (pmap (cocone_inj M d))).
    + intro x; symmetry; exact (unique_property U d x).
    + exact (pcont (cocone_inj M d)).
  - intros d x. exact (unique_property U d x).
  - intros v Hv x. simpl.
    exact (uniqueness U (pmap v) (fun d y => Hv d y) x).
Defined.

(* The mediator out of the lifted cocone IS the [Sets] mediator. / 从提升的余锥中出来的中介是 [Sets] 中介。 *)
Example pfinal_cocone_med_map@{o so s r r' x x' +| o < so +}
  {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so})
  (N : Cocone (PForget@{o so} ◯ F))
  (HN : IsColimitCocone@{x' x' r' s o so} N) (M : Cocone F) :
  pmap (unique_obj (pfinal_cocone_colimiting@{o so s r r' x x' _} F N HN M))
    = unique_obj (colimitcocone_ump HN (FCocone PForget@{o so} M)) := eq_refl.

(* The recipe for a colimit record of the points. The colimit of the points and the colimit of spaces are records at two levels, [r'] and [r], left independent. / 点的余极限的公式。点的余极限和空间的余极限是在两个层次上的记录，[r'] 和 [r]，彼此独立。 *)
Definition PTop_Colimit_lift@{r r' s o so +| o < so +}
  {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so})
  (L : Colimit@{r' s o so} (PForget@{o so} ◯ F)) : Colimit@{r s o so} F :=
  limitcone_limit (PFinalCocone F (@limit_cone _ _ _ L))
    (pfinal_cocone_colimiting F _ (colimit_colimitcocone L)).

Example PTop_Colimit_lift_apex@{r r' s o so +| o < so +}
  {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so})
  (L : Colimit@{r' s o so} (PForget@{o so} ◯ F)) :
  vertex_obj[@limit_cone _ _ _ (PTop_Colimit_lift@{r r' s o so _ _ _} F L)]
    = PFinal (vertex_obj[@limit_cone _ _ _ L]) (obj[D]) (fun d => F d)
        (fun d => cocone_inj (@limit_cone _ _ _ L) d) := eq_refl.

(* * ** Remark 2 directly: the recipe at the colimit of [Sets] / * ** 直接备注 2： [Sets] 的余极限处的配方 *)

Section PColimit.

Universes r s o so.
Constraint o < so.
Constraint s <= o.
Constraint o <= r.

Context {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so}).

Local Notation G := (PForget@{o so} ◯ F).

Definition PColimit : Colimit@{r s o so} F :=
  PTop_Colimit_lift F (Sets_Colimit G).

Example PColimit_apex :
  vertex_obj[@limit_cone _ _ _ PColimit]
    = PFinal (Sets_colim_obj G) (obj[D]) (fun d => F d)
        (fun d => Sets_colim_inj G d) := eq_refl.

Example PColimit_points :
  pt_carrier (vertex_obj[@limit_cone _ _ _ PColimit]) = Sets_colim_obj G
  := eq_refl.

Example PColimit_inj (d : D) :
  pmap (cocone_inj (@limit_cone _ _ _ PColimit) d) = Sets_colim_inj G d
  := eq_refl.

(*
 The triangle, on the nose: the mediator into a cocone [M] sends the
 point [x] of the summand at [d] to [M]'s leg at [d] applied to [x], as
 Instance/Sets/Cocomplete.v's [Sets_colim_triangle] does for [Sets]. 

 --------
 三角形，在鼻子上：作为余锥的中介 [M] 将和的点 [x] 在 [d] 处送到 [M] 在 [d] 处的边上应用于 [x]，就像 Instance/Sets/Cocomplete.v 的 [Sets_colim_triangle] 对 [Sets] 所做的那样。
*)
Example PColimit_med_at (M : Cocone F) (d : D) (x : pt_carrier (F d)) :
  pmap (unique_obj (@ump_limits _ _ _ PColimit M)) (existT _ d x)
    = pmap (cocone_inj M d) x := eq_refl.

End PColimit.

Definition PTop_Cocomplete@{r s o so +| o < so, s <= o, o <= r +} :
  @Cocomplete@{r s o so} PTopCat@{o so} := fun D F => PColimit F.

(* * ** Indexed coproducts: the final topology on the disjoint union / * ** 指数积的余积：在不相交并集上的最终拓扑 *)

Section PSigma.

Universes o i.
Constraint i <= o.

Context (Ix : Type@{i}) (X : Ix → PTop@{o}).

(* The disjoint union of the points, [Sets_icoprod_obj], with the final topology for its injections. / 点 [Sets_icoprod_obj] 的不相交并集，带有其注入映射的最终拓扑。 *)
Definition PSigma : PTop@{o} :=
  PFinal (Sets_icoprod_obj (fun k => pt_carrier (X k))) Ix X
    (fun k => Sets_icoprod_inj (fun k => pt_carrier (X k)) k).

Example PSigma_points :
  pt_carrier PSigma = Sets_icoprod_obj (fun k => pt_carrier (X k)) := eq_refl.

Example PSigma_open (V : Sets_icoprod_obj (fun k => pt_carrier (X k)) → Prop) :
  POpen PSigma V
  = ((∀ p q : Sets_icoprod_obj (fun k => pt_carrier (X k)),
        p ≈ q → V p → V q) /\
     (∀ k : Ix, POpen (X k) (fun x => V (existT _ k x)))) := eq_refl.

End PSigma.

Section PSigmaUMP.

Universes o so i.
Constraint o < so.
Constraint i <= o.

Context (Ix : Type@{i}) (X : Ix → PTopCat@{o so}).

Definition psigma_inj (k : Ix) : X k ~{PTopCat@{o so}}~> PSigma Ix X :=
  pfinal_leg _ _ _ _ k.

Definition psigma_case (Z : PTopCat@{o so})
  (iota : ∀ k, X k ~{PTopCat@{o so}}~> Z) :
  PSigma Ix X ~{PTopCat@{o so}}~> Z :=
  pfinal_desc _ Ix X (fun k => Sets_icoprod_inj (fun k => pt_carrier (X k)) k)
    Z (Sets_icoprod_case (fun k => pt_carrier (X k)) (pt_carrier Z)
         (fun k => pmap (iota k)))
    (fun k => pcont (iota k)).

Example psigma_case_at (Z : PTopCat@{o so})
  (iota : ∀ k, X k ~{PTopCat@{o so}}~> Z) (k : Ix) (x : X k) :
  pmap (psigma_case Z iota) (existT _ k x) = pmap (iota k) x := eq_refl.

Lemma psigma_desc (Z : PTopCat@{o so})
  (iota : ∀ k, X k ~{PTopCat@{o so}}~> Z) :
  ∃! u : PSigma Ix X ~{PTopCat@{o so}}~> Z, ∀ k, u ∘ psigma_inj k ≈ iota k.
Proof.
  unshelve eapply Build_Unique.
  - exact (psigma_case Z iota).
  - intros k x; reflexivity.
  - intros v Hv [k x]; simpl. symmetry. exact (Hv k x).
Defined.

Definition PTop_IsIndexedCoproduct :
  IsIndexedCoproduct X (PSigma Ix X) psigma_inj :=
  Build_IsIndexedCoproduct X _ _ (fun c iota => psigma_desc c iota).

End PSigmaUMP.

Definition PTop_HasIndexedCoproducts@{o so +| o < so +} :
  HasIndexedCoproducts PTopCat@{o so} :=
  @Build_HasIndexedCoproducts PTopCat@{o so}
    (fun A f => PSigma A f)
    (fun A f k => psigma_inj A f k)
    (fun A f => PTop_IsIndexedCoproduct A f).

(* * ** Remark 2 by the book's route: coproducts and the dual of Proposition 1 / * ** 书中路线的备注 2：余积以及命题 1 的对偶 *)

Definition PTop_Cocomplete_via_coproducts@{o so +| o < so +} :
  @Cocomplete PTopCat@{o so} :=
  Cocomplete_from_coproducts_coequalizers PTop_HasIndexedCoproducts
    PTop_HasCoequalizers.

(* The book-route colimit IS a quotient topology on a disjoint union: its apex is [PQuot] of [PSigma] of the diagram's spaces, along the projection onto a [Sets] coequalizer, on the nose. / 书本路线上余极限是一个在不相交并集上的商拓扑：它的顶点是图中空间的 [PQuot] 对 [PSigma] ，沿着投影到一个 [Sets] 共轭器，完全精确。 *)
Example PTop_Cocomplete_via_coproducts_apex@{o so +| o < so +}
  (D : Category@{o o o}) (F : D ⟶ PTopCat@{o so}) :
  { A : SetoidObject@{o o} &
  { f : A ~{Sets@{o so}}~> pt_carrier (PSigma (obj[D]) (fun d => F d)) &
  { g : A ~{Sets@{o so}}~> pt_carrier (PSigma (obj[D]) (fun d => F d)) &
    vertex_obj[@limit_cone _ _ _ (PTop_Cocomplete_via_coproducts D F)]
      = PQuot (PSigma (obj[D]) (fun d => F d)) (SetsCoeq f g)
          (sets_coeq_proj f g) } } }.
Proof. eexists; eexists; eexists; reflexivity. Defined.

(*
 The two routes agree where both are stated, at shapes whose objects sit
 at the points' universe: the two apexes are isomorphic, compatibly with
 the injections (Structure/Limit/Unique.v's [colimit_unique_iso]). 

 --------
 当两条路径都被说明时，它们在形状上是相符合的，这些形状的对象位于点的宇宙中：两个顶点是同构的，并且与注入兼容（Structure/Limit/Unique.v 的 [colimit_unique_iso]）。
*)
Definition PTop_Cocomplete_routes_iso@{o so +| o < so +}
  (D : Category@{o o o}) (F : D ⟶ PTopCat@{o so}) :
  colimit_apex (PTop_Cocomplete D F)
    ≅[PTopCat@{o so}] colimit_apex (PTop_Cocomplete_via_coproducts D F) :=
  colimit_unique_iso (colimit_is_acolimit _) (colimit_is_acolimit _).

Lemma PTop_Cocomplete_routes_iso_injs@{o so +| o < so +}
  (D : Category@{o o o}) (F : D ⟶ PTopCat@{o so}) (d : D) :
  to (PTop_Cocomplete_routes_iso D F)
    ∘ colimit_inj (colimit_is_acolimit (PTop_Cocomplete D F)) d
  ≈ colimit_inj (colimit_is_acolimit (PTop_Cocomplete_via_coproducts D F)) d.
Proof. exact (fst (colimit_unique_iso_injs _ _) d). Qed.

(*
   * ** The indiscrete topology, and the underlying-set functor as a left
   adjoint 

   --------
   * ** 非离散拓扑，以及作为左伴随函子的底集合函子
*)

Section Indiscrete.

Universe o.

Context (S : SetoidObject@{o o}).

(* The coarsest topology: the uniform predicates. / 最粗糙的拓扑：一致谓词。 *)
Definition pindisc_open (U : S → Prop) : Prop := ∀ x y : S, U x → U y.

Lemma pindisc_open_respects (U V : S → Prop) :
  (∀ x, U x <-> V x) → pindisc_open U → pindisc_open V.
Proof.
  intros H HU x y v. apply (proj1 (H y)), (HU x y), (proj2 (H x)), v.
Qed.

Lemma pindisc_open_proper (U : S → Prop) :
  pindisc_open U → ∀ x y : S, x ≈ y → U x → U y.
Proof. intros HU x y _; exact (HU x y). Qed.

Lemma pindisc_open_union (F : (S → Prop) → Prop) :
  (∀ U, F U → pindisc_open U) →
  pindisc_open (fun x => ex (fun U => F U /\ U x)).
Proof.
  intros HF x y [U [FU u]]. exists U; split; [exact FU|].
  exact (HF U FU x y u).
Qed.

Lemma pindisc_open_whole : pindisc_open (fun _ => True).
Proof. intros x y t; exact t. Qed.

Lemma pindisc_open_inter (U V : S → Prop) :
  pindisc_open U → pindisc_open V → pindisc_open (fun x => U x /\ V x).
Proof.
  intros HU HV x y [u v]; exact (conj (HU x y u) (HV x y v)).
Qed.

Definition PIndiscrete : PTop@{o} := {|
  pt_carrier     := S;
  POpen          := pindisc_open;
  popen_respects := pindisc_open_respects;
  popen_proper   := pindisc_open_proper;
  popen_union    := pindisc_open_union;
  popen_whole    := pindisc_open_whole;
  popen_inter    := pindisc_open_inter
|}.

Example PIndiscrete_carrier : pt_carrier PIndiscrete = S := eq_refl.

Example PIndiscrete_open (U : S → Prop) :
  POpen PIndiscrete U = (∀ x y : S, U x → U y) := eq_refl.

(*
 Every setoid map into an indiscrete space is continuous: the preimage of
 a uniform predicate is constant up to [<->], and constants are open
 (Instance/Top/Prop.v's [popen_const]). 

 --------
 映入无离散空间的每个等价类映射都是连续的：均匀谓词的原像在  [<->] 下是常数，而常数是开集（Instance/Top/Prop.v 的  [popen_const] ）。
*)
Lemma pindisc_cont (X : PTop@{o}) (f : SetoidMorphism@{o o o} X S) :
  @PCont X PIndiscrete f.
Proof.
  intros U HU. apply (popen_respects X (fun _ => ex (fun x => U (f x)))).
  - intro x; split.
    + intros [y u]. exact (HU (f y) (f x) u).
    + intro u. exists x. exact u.
  - apply popen_const.
Qed.

Definition pindisc_mor (X : PTop@{o}) (f : SetoidMorphism@{o o o} X S) :
  PMor@{o} X PIndiscrete := @Build_PMor X PIndiscrete f (pindisc_cont X f).

Example pindisc_mor_map (X : PTop@{o}) (f : SetoidMorphism@{o o o} X S) :
  pmap (pindisc_mor X f) = f := eq_refl.

End Indiscrete.

Section IndiscreteAdjunction.

Universes o so.
Constraint o < so.

Program Definition PIndisc : Sets@{o so} ⟶ PTopCat@{o so} := {|
  fobj := fun S => PIndiscrete S;
  fmap := fun S T f => pindisc_mor T (PIndiscrete S) f
|}.
Next Obligation. intros S T f g H x; exact (H x). Qed.
Next Obligation. intros S x; reflexivity. Qed.
Next Obligation. intros S T U f g x; reflexivity. Qed.

Example PIndisc_fobj (S : Sets@{o so}) : fobj[PIndisc] S = PIndiscrete S
  := eq_refl.

Program Definition pforget_indisc_iso (X : PTopCat@{o so}) (S : Sets@{o so}) :
  @Isomorphism Sets
    {| carrier := @hom Sets@{o so} (PForget@{o so} X) S
     ; is_setoid := @homset Sets@{o so} (PForget@{o so} X) S |}
    {| carrier := @hom PTopCat@{o so} X (PIndisc S)
     ; is_setoid := @homset PTopCat@{o so} X (PIndisc S) |} := {|
  to   := {| morphism := fun k => pindisc_mor S X k |};
  from := {| morphism := fun g => pmap g |}
|}.
Next Obligation. intros X S k k' H x; exact (H x). Qed.
Next Obligation. intros X S g x; reflexivity. Qed.
Next Obligation. intros X S k x; reflexivity. Qed.

(*
 [PForget ⊣ PIndisc]: both transposes are the identity on underlying
 maps. 

 --------
 [PForget ⊣ PIndisc]：两个转置在底层映射上都是恒等映射。
*)
Definition PForget_PIndisc : PForget@{o so} ⊣ PIndisc.
Proof.
  unshelve eapply (@Build_Adjunction' _ _ PForget PIndisc pforget_indisc_iso).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

(*
 Riehl §3.6 Proposition 2, the cocontinuity half, by Adjunction/
 Continuity.v's left adjoints preserve colimits. 

 --------
 Riehl §3.6 命题 2，共连续性的那一半，通过伴随/连续性，左伴随保留余极限。
*)
Definition PForget_Cocontinuous : CocontinuousFunctor PForget@{o so} :=
  left_adjoint_Cocontinuous PForget_PIndisc.

End IndiscreteAdjunction.

(* The preservation statement per shape, with the shape's universes named. / 每个形状的保存声明，以及该形状的宇宙命名。 *)
Definition PForget_PreservesColimitCocone@{s o so +| o < so +}
  (J : Category@{s o o}) (K : J ⟶ PTopCat@{o so}) :
  PreservesColimitCocone K PForget@{o so} :=
  left_adjoint_PreservesColimitCocone PForget_PIndisc K.

(*
 The converse of the recipe: a lifted cocone that is colimiting forgets
 to a colimiting cocone, [PForget]'s image of [PFinalCocone N] having
 [N]'s apex and legs.  With [pfinal_cocone_colimiting], [N] is
 colimiting exactly when its lift is. 

 --------
 配方的逆命题：一个提升的余角锥，如果是余极限的，就会忘记为一个余极限的角锥，[PForget] 对 [PFinalCocone N] 的像具有 [N] 的顶点和边。对于 [pfinal_cocone_colimiting]，当且仅当它的提升是余极限时，[N] 才是余极限的。
*)
Lemma pfinal_cocone_colimiting_reflect@{o so s r x +| o < so +}
  {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so})
  (N : Cocone (PForget@{o so} ◯ F))
  (H : IsColimitCocone@{x x r s o so} (PFinalCocone F N)) :
  IsColimitCocone@{x x r s o so} N.
Proof.
  exact (PForget_PreservesColimitCocone D F (PFinalCocone F N) H).
Qed.

(* Riehl's recipe in its "any colimit" form: the topology of EVERY colimit of spaces is the final topology on its points for its legs. / Riehl 的配方在其“任何余极限”形式中：空间的每一个余极限的拓扑都是其各支上点的最终拓扑。 *)
Lemma PTop_colimit_open_iff_final@{o so s r +| o < so +}
  {D : Category@{s o o}} {F : D ⟶ PTopCat@{o so}}
  (L : Colimit@{r s o so} F) (V : pt_carrier (colimit_apex L) → Prop) :
  POpen (colimit_apex L) V
  <-> POpen (PFinal (pt_carrier (colimit_apex L)) (obj[D]) (fun d => F d)
               (fun d => pmap (colimit_inj (colimit_is_acolimit L) d))) V.
Proof.
  split.
  - intro HV; split.
    + exact (popen_proper _ V HV).
    + intro d. exact (pcont (colimit_inj (colimit_is_acolimit L) d) V HV).
  - intro HV.
    set (N := FCocone PForget@{o so} (@limit_cone _ _ _ L)).
    pose proof (PForget_PreservesColimitCocone D F _
                  (colimit_colimitcocone L)) as HN.
    pose proof (colimitcocone_ump HN N) as U.
    destruct (colimitcocone_ump (colimit_colimitcocone L) (PFinalCocone F N))
      as [m Hm _].
    assert (Hid : ∀ y, pmap m y ≈ y).
    { intro y.
      transitivity (unique_obj U y).
      - symmetry. exact (uniqueness U (pmap m) (fun d x => Hm d x) y).
      - exact (uniqueness U setoid_morphism_id (fun d x => reflexivity _) y). }
    apply (popen_respects _ (fun y => V (pmap m y))).
    + intro y; split; intro v.
      * exact (proj1 HV _ _ (Hid y) v).
      * exact (proj1 HV _ _ (symmetry (Hid y)) v).
    + exact (pcont m V HV).
Qed.

(* * ** Non-vacuity: two indiscrete two-point spaces, side by side / * ** 非空性：两个不连续的两点空间，并列 *)

Definition PTwoIndisc@{o} : PTop@{o} := PIndiscrete bool_setoid_object@{o o}.

(* The sum, with its index universe set to the points' own, so that every statement below names one space. / 这个和，将其索引集合设置为点自身的集合，这样下面的每个语句都命名一个空间。 *)
Definition PTwoIndiscSum@{o u | o < u +} : PTop@{o} :=
  PSigma@{o o u} bool (fun _ => PTwoIndisc@{o}).

(* The two injections are different arrows of [PTopCat]. / 这两次注射是 [PTopCat] 的不同箭头。 *)
Lemma PTwoIndiscSum_injections_differ@{o so u | o < so, o < u +} :
  psigma_inj@{o so o u} bool (fun _ => PTwoIndisc@{o}) true
    ≈[PTopCat@{o so}] psigma_inj@{o so o u} bool (fun _ => PTwoIndisc) false
  → False.
Proof. intro H. destruct (H true) as [e _]. discriminate e. Qed.

(* Each summand is open, and it is not uniform: the topology is not the indiscrete one. / 每个加数都是开集，并且它不是一致的：拓扑不是平凡拓扑。 *)
Lemma PTwoIndiscSum_summand_open@{o u | o < u +} :
  POpen PTwoIndiscSum@{o u} (fun p => projT1 p = true).
Proof.
  split.
  - intros [i x] [j y] [e _] Hi; simpl in *. rewrite <- e. exact Hi.
  - intros k x y Hx. exact Hx.
Qed.

Lemma PTwoIndiscSum_not_indiscrete@{o u | o < u +} :
  (∀ U, POpen PTwoIndiscSum@{o u} U →
     ∀ p q : PTwoIndiscSum@{o u}, U p → U q) → False.
Proof.
  intro H.
  discriminate (H _ PTwoIndiscSum_summand_open
                  (existT _ true true) (existT _ false true) eq_refl).
Qed.

(* A point respecting the points' equality that is NOT open: the topology is not the discrete one either. / 一个关于点的等价性的点不是开集：该拓扑也不是离散拓扑。 *)
Lemma PTwoIndiscSum_not_discrete@{o u | o < u +} :
  (∀ p q : PTwoIndiscSum@{o u}, p ≈ q →
     projT1 p = true /\ projT2 p = true → projT1 q = true /\ projT2 q = true)
  /\ ~ POpen PTwoIndiscSum@{o u}
         (fun p => projT1 p = true /\ projT2 p = true).
Proof.
  split.
  - intros [i x] [j y] [e H] [Hi Hx]; simpl in *. destruct e. simpl in H.
    subst. split; reflexivity.
  - intros [_ Ho]. specialize (Ho true true false). simpl in Ho.
    destruct (Ho (conj eq_refl eq_refl)) as [_ H]. discriminate H.
Qed.
