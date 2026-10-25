(*
   * * T0-spaces are a full reflective subcategory of Top

   Book: Mac Lane, "Categories for the Working Mathematician", 2nd
   ed., Springer GTM 5, §IV.3, printed p. 92, Exercise 4.
   Verbatim from the page image: "4. Show the following
   subcategories to be reflective: (a) The full subcategory of
   all partial orders in the category Preord of all preorders,
   with arrows all monotone functions. (b) The full subcategory
   of T₀-spaces in Top."  Catalog id: maclane:IV.3:ex4.  This
   file is clause (b) ONLY; clause (a) -- posets inside the
   category of all preorders -- is the sibling development in
   Instance/Ord.v and Instance/Ord/Poset.v, whose pinned name is
   [Poset_Reflective_in_Ord].  Nothing here depends on it and
   nothing there depends on this.

   ** What is delivered

   [T0_Reflective_in_Top : Reflective T0_Subcategory] -- the record of
   Construction/Reflective.v, whose three fields are exactly the
   three things Mac Lane's phrase names: FULLNESS of the subcategory
   ([T0_Full]), a REFLECTOR ([T0_reflector]), and the ADJUNCTION
   ([T0_adj]) making it left adjoint to the inclusion.  The adjunction
   ALONE is strictly less than the record, and that mismatch is this
   development's typing rejection in Test/ProbeKolmogorov372.v.

   Around it: topological indistinguishability [SameOpens] with its
   three equivalence lemmas and [SameOpens_of_equiv]; the T0 predicate
   [IsT0]; the full subcategory [T0_Subcategory]/[T0Spaces] with the
   inclusion proved Full AND Faithful; the Kolmogorov quotient
   [KolmogorovQuotient] with [KolmogorovQuotient_T0] and the
   projection [kolmogorov_proj]; the universal property
   [kolmogorov_universal] and its packaging
   [kolmogorov_universal_arrow]; the counit corollary
   [t0_reflect_iso] -- a T0 space is its own Kolmogorov quotient up to
   isomorphism -- instantiated at the two-point discrete space as
   [bool_reflect_iso]; and [Hausdorff_T0_nn].

   ** The route

   Universal arrows, exactly the path Instance/Ab/TorsionFree.v takes
   for §IV.3 Exercise 2 and Instance/Grp/Abelianize.v for §III.1
   Exercise 3: state the ∃! ([kolmogorov_universal]), package it with
   Theory/Universal/Arrow.v's [universal_arrow_from_UMP]
   ([kolmogorov_universal_arrow]), then read the functor and the
   adjunction off that file's [LeftAdjointFunctorFromUniversalArrows]
   and its [AdjunctionFromUniversalArrows] with no further proof.
   Nothing in that chain is re-derived here.

   ** THE UNIVERSE OBSTRUCTION, AND THE DESIGN IT FORCES

   This is the substance of the file, and it is a measurement rather
   than a preference.

   The obvious rendering of indistinguishability is "x and y lie in
   exactly the same opens", quantified over EVERY open of X.  In this
   library that relation does not fit, and the rejection is a genuine
   universe inconsistency rather than a bookkeeping annoyance.
   [TopSpace@{o}] (Instance/Top.v) has [top_carrier :>
   SetoidObject@{o o}], so a space's own `≈` is a
   [crelation@{o o}] -- valued in [Type@{o}] -- while [IsOpen]
   quantifies over predicates [X → Type@{o}], so a relation
   quantifying over all of them lands at a level strictly above [o].
   Measured: the
   unrestricted relation elaborates as [∀ X : TopSpace@{o}, X → X →
   Type@{h}] with [o < h], and building a [SetoidObject@{o o}] on it
   is refused with "Cannot enforce ... = o because o < h <= ...".  So
   the "same carrier, coarser `≈`" design that
   Instance/Ab/TorsionFree.v uses, and that the sibling clause (a)
   uses, is NOT available for [Top] at one and the same universe.
   [SameOpensAll] is kept in the file as that unrestricted relation --
   it is a perfectly good [Definition], it simply cannot be a space's
   setoid -- and [SameOpensAll_SameOpens] relates the two.

   What IS available, and is what this file delivers, is
   indistinguishability tested against the opens whose VALUES lie at a
   level [s] strictly below the space's own level [o]:

   [SameOpens@{s o} X x y := ∀ U : X → Type@{s},
   IsOpen X U → (U x ↔ U y)]

   which sits at [Type@{o}] exactly because [X → Type@{s} :
   Type@{o}] when [s < o].  Every [Prop]-valued open is such a [U] (by
   cumulativity, at every [s]), so the family being tested against is
   generous; both concrete witnesses below separate their points with
   a [Prop]-valued open.

   The quotient then carries the SAME carrier type, the coarsened `≈`
   [SameOpens X], and as its opens exactly those opens of X that
   RESPECT that relation ([kq_open]).  The two definitions look
   circular and are not, and the lemma that breaks the circle is
   [small_open_is_kq_open]: an open of X valued at level [s] respects
   [SameOpens X] AUTOMATICALLY, since the relation says in so many
   words that x and y agree on it.  Hence every level-[s] open of X is
   still an open of the quotient, [KolmogorovQuotient_T0] is three
   lines, and -- the other half of the same fact -- the mediator out
   of the quotient is continuous because a [Type@{o}]-valued open of
   the T0 target pulls back to an open that respects the relation, by
   [open_proper] of the target.  Classically, where opens are
   [Prop]-valued and small, [kq_open] IS the topology of X and this is
   the ordinary Kolmogorov quotient.

   Read [IsT0] with that in mind: it is "points that agree on all
   level-[s] opens are equal", a STRONGER requirement than agreement
   on all opens would give, since [SameOpensAll] implies [SameOpens]
   and not conversely by anything proved here.  The restriction is
   visible in the statement rather than hidden inside it.

   ** Same carrier, no choice principle

   [KolmogorovQuotient X] forms no new carrier: [kq_carrier_strict]
   records by [eq_refl] that its carrier IS X's, and
   [kq_equiv_strict] that its `≈` IS [SameOpens X].  No equivalence
   class, no quotient axiom, no representative is ever chosen, and
   [kolmogorov_proj] is the identity on points.  Everything in the
   file is [Type]-valued data: [SameOpens] is a Π of products, its
   witnesses are taken apart directly, and nothing anywhere extracts
   a witness from a [Prop]-valued existential -- so no choice
   principle appears.  All 76 constants are closed under the global
   context, with no [Axioms:] line anywhere; in particular this file
   requires none of
   Instance/Top/Interval.v, Instance/Top/Homotopy.v or the metric
   files, so the standard library's real-number axioms are nowhere in
   its closure.

   ** Prior art, measured at d658518e (the issue's "Current state" is
   stale and is corrected rather than repeated)

   Issue #372 says "both ambient categories are missing" and that
   "there is no Instance/Top.v".  Both are false at d658518e:
   [Top : Category] is Instance/Top.v, with [TopSpace],
   [Continuous], [ContinuousMorphism], the discrete and
   indiscrete constructors, and the Hausdorff and
   compact-Hausdorff full subcategories already in place.

   What IS absent, and is what this file supplies: a case-insensitive
   search over the [.v] files for 'kolmogorov', 'specializ' and
   'indistinguish' returns no topological hit at all (the two
   'kolmogorov' hits are Chapman-Kolmogorov in
   Structure/Monoidal/Markov.v, the one 'indistinguish' hit is
   Theory/Algebra/Monoid/Product.v about type display, and the
   'specializ' matches are the tactic [specialize] and prose about
   specializing a theorem), and a search for the token 'T0' returns
   three lines --
   Adjunction/Additive.v and Structure/AbCategory.v --
   every one of them Mac Lane's phrase "whence T0 = 0" about an
   additive functor, which is unrelated.  There was no T0 predicate,
   no indistinguishability relation, no Kolmogorov quotient and no
   reflection.

   ** Reused, and what that saves

   - Instance/Top.v: [TopSpace] and its six fields, [Continuous],
   [ContinuousMorphism], [Build_ContinuousMorphism], [Top],
   [IsHausdorff] for [Hausdorff_T0_nn], and the two witness
   spaces [Bool_Discrete] and [TwoPoint_Indiscrete]
   with [bool_setoid_object].  The [Sub Top] pattern is
   [Hausdorff_Subcategory] / [HausdorffSpaces] /
   [Hausdorff_Full] copied field for field.
   - Construction/Subcategory.v: [Subcategory], [Sub],
   [Incl], [Incl_Faithful], [Full],
   [Full_Implies_Full_Functor].  The trivially-true [shom] is
   the [Hausdorff_Subcategory] and Instance/Rng.v's [CRng_Sub]
   pattern, and [Full] is written qualified because
   Construction/Subcategory.v exports its OWN [Full], whose first
   argument is a Category.
   - Construction/Reflective.v: [Reflective] and
   [reflective_counit_iso].
   - Theory/Universal/Arrow.v: the three constants named under "The
   route" above.

   The quotient-topology precedents in tree -- Instance/Top.v's
   [CP_open], Instance/Top/Wedge.v's [wedge_open],
   Instance/Top/Pushout.v's [tp_open] -- all glue POINTS by an
   inductive or closed-form relation and re-derive openness from
   scratch.  None of them is required here and none is needed: this
   quotient changes no points.

   NEW here: [SameOpens] and its four lemmas, [SameOpensAll], [IsT0],
   the subcategory, the five [kq_*] topology lemmas and
   [KolmogorovQuotient], [small_open_is_kq_open], the mediator and the
   universal property, [Hausdorff_T0_nn], and the three witnesses.

   ** Strengths, measured strict-first

   Holding at [eq_refl] (eight occurrences outside comments, none of
   them inside a rejection: the SIX [Example]s named in this
   paragraph, which pin a definitional identity, plus two uses inside
   the witness proofs [Bool_Discrete_T0] and [tri_point_apart] -- the
   file's two other [Example]s, [indiscrete_quot_identifies] and
   [tri_quot_merges], are inhabitants rather than [eq_refl]s): the
   quotient's carrier IS the base
   space's and its `≈` IS [SameOpens X] ([kq_carrier_strict],
   [kq_equiv_strict]); the reflector's object part IS the quotient
   ([t0_reflector_obj]); the universal arrow IS [kolmogorov_proj] and
   its object IS [KolmogorovT0 X] ([kolmogorov_arrow_is_proj],
   [kolmogorov_arrow_obj] -- since [universal_arrow_from_UMP] stores
   the supplied morphism as the second projection of the comma object
   it builds); and the adjunction's UNIT is the projection applied to
   any point ([t0_unit_is_proj]).

   Falling back, with the cause diagnosed in each case:

   - The unit as a MORPHISM RECORD is only `≈` the projection
   ([t0_unit_is_proj_hom]).  Cause:
   [AdjunctionFromUniversalArrows] builds ⌊−⌋ as [fun g => fmap[U]
   g ∘ arrow], so the class unit is a COMPOSITE record,
   [fmap[Incl] id ∘ kolmogorov_proj X]; applied to a point that
   composite reduces, as a [ContinuousMorphism] record it does not.
   The same shape is recorded for #371's [torsion_unit_is_proj_hom]
   and for Instance/Mod/Free.v's [free_module_unit_is_insert].
   CORRECTION (#1347): as a record it now does: the unit IS
   [kolmogorov_proj X] at [eq_refl] (Test/ProbeKolmogorov372.v's
   CONVERSION 1, now a control), since Instance/Sets.v gives its
   identity's and composite's properness fields as terms.  The cause
   above was argued; the residue was the standard library's, the
   opaque lemmas instance resolution had put in the two properness fields,
   the identity's and the composite's.  Of the two cases named, #371's
   whole [CMonHom] record is still refused (Test/ProbeTorsionFree371.v),
   while Instance/Mod/Free.v's unit, a morphism of [Sets], now IS
   [fv_insert X] at [eq_refl] (control C9 of Test/ProbeSetsTerms1347.v,
   which master 687ac356 refuses).
   - [KolmogorovQuotient Bool_Discrete] is isomorphic to
   [Bool_Discrete] but not equal to it: [bool_reflect_iso] is a pure
   instantiation of [reflective_counit_iso] with no tactic, while
   [KolmogorovQuotient Bool_Discrete = Bool_Discrete] is refused.
   Cause: [Discrete_Top]'s opens are the `≈`-respecting predicates
   and the quotient's are the pairs of an open with a proof that it
   respects [SameOpens], so the two [IsOpen] fields differ as terms
   -- and so, separately, do the setoid field and every law field.
   - The COUNIT is not read back at all.  It is the other transpose,
   [unique_obj (ump_universal_arrows …)], and
   [ump_universal_arrows] (Theory/Universal/Arrow.v) is closed
   with [Qed], so nothing on that side reduces and no [eq_refl] is
   claimed for it in either direction.
   - [Hausdorff_T0_nn] yields only [¬ ¬ (x ≈ y)], and it is stated
   against [SameOpensAll], not against [SameOpens].  TWO independent
   reasons, both measured rather than guessed.  First, logic: from
   "x and y lie in the same opens" and "x is apart from y" one gets
   the separating pair and a contradiction, which refutes the
   apartness and gives a double negation; turning that into [x ≈ y]
   is double-negation elimination for the carrier's own `≈`, which
   this library does not have.  Second, levels: [IsHausdorff]
   produces separating opens valued at [Type@{o}], which are not
   among the level-[s] opens [SameOpens] tests, so the argument does
   not even start from [SameOpens].  Consequently NOTHING here
   derives [IsT0] from [IsHausdorff], and no such implication is
   claimed; [Bool_Discrete_T0] is proved directly instead, from one
   [Prop]-valued open.

   ** Universes

   Measured with [Set Printing Universes] on every constant, reading
   BOTH the binder and the constraint block.

   The file's own content is the strict inequality [s < o] in
   [SameOpens@{s o}] -- the level of the opens tested strictly below
   the level of the space -- declared with the trailing [+] of
   Instance/Top.v's idiom, and that [+] is load-bearing across
   versions: without it Coq 8.19 and 8.20 reject the declaration with
   "Universe constraints are not implied by the ones declared" (six
   inferred bounds against [prod] and [sigT]) while Rocq 9.1 accepts
   it, which the three-version nix build found and which is why the
   declaration is not closed.  It propagates: [IsT0@{u u0 u1}]
   carries [u0 < u1] with [u1 <= u], and [KolmogorovQuotient@{u u0} :
   TopSpace@{u} → TopSpace@{u}] carries [u0 < u] (with four inherited
   [Projections] bounds), so the quotient is a genuine ENDOfunction on
   the objects of one and the same [Top] --
   which is what makes [T0_reflector] and hence the [Reflective]
   record formable at all.

   Two identifications sit in BINDERS, where a reader of the blocks
   alone would miss them, and both are the DONORS'.  First,
   [Top@{u u1}] is [Category@{u u u}] (Instance/Top.v's own note: the
   hom-sets live one step above the points), so hom and proof are
   identified there; [T0Spaces] inherits it, printing as
   [Category@{u0 u u}].  Second, [Subcategory] is declared over
   [Category@{u u0 u0}] and [Reflective] over [Category@{u3 u5 u5}],
   the same identification once more; it is guarded by the probe's
   formability rejection, where naming a hom-set and an identity at
   hom-strictly-below-proof levels succeeds while [Subcategory] is
   refused.  Read that rejection at its strength: it fires at
   [Subcategory], and [Reflective] cannot be tested apart from its
   [Subcategory] argument, so whether [Reflective] identifies anything
   OF ITS OWN is not measured here.  Neither identification is
   introduced by this file and neither is claimed unavoidable.

   NO constraint block of any constant in this file carries a universe
   EQUATION -- every entry is [<] or [<=], measured over all 70 blocks
   the 76 constants print.  Read the [Set] measurement exactly: the
   token occurs in the [About] output of this file's constants in
   precisely TWO places, and NEITHER is a universe binder or a
   constraint block -- [Tri@{} : Set], which is the SORT [Inductive
   Tri : Set] declares, and the motive of Coq's generated eliminator
   [Tri_rec : ∀ P : Tri → Set, …].  No universe binder and no
   constraint entry of any constant in the file mentions [Set]; that
   every universe variable satisfies [Set <= _] is Coq's own
   convention and is not printed, so nothing is claimed about it.

   ** Non-vacuity

   Proved in both directions, so the subcategory is neither empty nor
   everything, and the quotient is shown to do something and not to do
   too much.

   [Bool_Discrete] is T0 ([Bool_Discrete_T0], by testing the
   [Prop]-valued open [fun z => z = x]), so [T0Spaces] is inhabited
   and [bool_reflect_iso] applies.  [TwoPoint_Indiscrete] is NOT
   ([TwoPoint_Indiscrete_not_T0]): its opens are the uniform
   predicates, so every pair of points is indistinguishable, while
   [true ≈ false] is [true = false].  The quotient identifies exactly
   that pair, with the witness written out
   ([indiscrete_quot_identifies], whose proof term IS
   [indiscrete_points_same_opens]).

   [Tri_Top] is the mixed three-point space: carrier [Tri] with its
   opens the predicates that cannot tell [Tri_l] from [Tri_r].  It is
   not T0 ([Tri_Top_not_T0]), its quotient merges that pair
   ([tri_quot_merges]) and keeps [Tri_l] apart from the third point
   ([tri_quot_keeps_point_apart]; that [Tri_r] is apart from it too
   follows in one line from [SameOpens_sym]/[SameOpens_trans] and is
   not stated).  Say precisely how the two negatives close, since the
   two mechanisms differ: the first PROVES the relation at every open,
   directly from [tri_open]'s two components, and feeds it to [IsT0];
   the second INSTANTIATES the relation at the single [Prop]-valued
   open [fun z => z = Tri_pt].  Both then close by [discriminate] on
   the discrete carrier.  No map out of the quotient into a second
   space is used anywhere, and no induction over a generated relation
   occurs, there being no generated relation.

   ** NOT delivered

   - No T1/T2 chain beyond [Hausdorff_T0_nn], which as measured above
   does not give [IsT0]; no sober spaces, no T3/T4, no
   specialization ORDER as a preorder, and in particular no bridge
   to the sibling clause (a): the specialization preorder of a space
   would be the natural object of [Ord] connecting the two halves of
   Mac Lane's exercise and it is NOT built here.  CORRECTION (#461):
   over the Prop-valued spaces [PTopCat] the chain now exists, in
   Instance/Top/Separation.v ([PT0], [PT1] and the positive Hausdorff
   form [PHaus], with their reflections) and Instance/Top/Hausdorff.v
   (regular spaces [PReg] and [PT3]); over [Top] this item stands.
   - No Kolmogorov quotient of a pointed space, and no relation to
   Instance/Top/Homotopy.v's [Toph] or [Top_pointed].
   - No functoriality statement for [KolmogorovQuotient] beyond the
   reflector itself, and no naturality of [kolmogorov_proj] stated
   separately from the adjunction's unit.
   - No proof that [KolmogorovQuotient] is a quotient in any
   categorical sense (no coequalizer, no [RegularEpi]); the
   projection is not shown epic.
   - No comparison between [SameOpens] and [SameOpensAll] beyond
   [SameOpensAll_SameOpens]; no space is exhibited separating them,
   so the restriction to level-[s] opens is not shown to be strict.
   - No idempotent monad of the reflection.
   Construction/Reflective/Idempotent.v gives it by instantiation
   from [T0_Reflective_in_Top]; that instantiation is not made.

   ** Corrections to the brief that guided this file

   Each is a measurement, not an opinion.  (1) The brief's plan
   proposed [SameOpens] quantified over ALL opens and the quotient
   with "[IsOpen := IsOpen X] verbatim", noting that "coarsening the
   carrier's `≈` to 'agree on every open' keeps every open predicate
   open on the nose".  That is true of the mathematics and false of
   the universes: the relation is a level too big to be a space's `≈`,
   as measured above and pinned in the probe, so the level-restricted
   relation and the respecting-opens topology are used instead.  (2)
   The brief asked whether [KolmogorovQuotient_T0] is definitional; it
   is not -- it is a three-line proof whose content is
   [small_open_is_kq_open] -- because the quotient's opens are the
   respecting ones rather than X's verbatim.  (3) The brief expected
   [Hausdorff_T0] possibly weakened to a double negation; the double
   negation is indeed all that comes out, and there is a SECOND
   obstruction (the level of the separating opens) that the brief does
   not anticipate, so the lemma is stated against [SameOpensAll].  (4)
   The brief offered [Sum_Top] from Instance/Top/Coproduct.v for the
   mixed witness "if it is cheap"; [Tri_Top] is built directly in
   fifty lines instead, which adds nothing to the closure.  Every
   donor line number the brief gave was re-grepped here and is
   correct. 

   --------
   * * T0-空间是拓扑空间（Top）的一个全反射子范畴

   书籍：Mac Lane，《为在职数学家而作的范畴论》，第二版，Springer GTM 5，§IV.3，第92页印刷版，习题4。从页面图像逐字摘录：“4. 证明以下子范畴是反射的：(a) 在所有预序构成的范畴 Preord 中，所有偏序的全子范畴，箭头为所有单调函数。(b) 拓扑空间（Top）中 T₀-空间的全子范畴。” 目录ID：maclane:IV.3:ex4。此文件仅包含条款(b)；条款(a)——所有预序范畴中的偏序——在 Instance/Ord.v 和 Instance/Ord/Poset.v 中的相关开发，固定名称为 [Poset_Reflective_in_Ord]。这里只涉及条款(b)，并不依赖条款(a)，那边也不依赖这里。** 交付内容

   [T0_Reflective_in_Top : Reflective T0_Subcategory] —— Construction/Reflective.v 的记录，其三个字段正好对应 Mac Lane 术语中的三件事：子范畴的完整性（[T0_Full]）、一个反射器（[T0_reflector]）以及使其成为包含函数的左伴随的伴随（[T0_adj]）。仅伴随本身严格小于该记录，而这种不匹配就是本开发在 Test/ProbeKolmogorov372.v 中的类型拒绝问题。围绕它：拓扑不可区分性 [SameOpens] 及其三个等价引理和 [SameOpens_of_equiv]；T0 谓词 [IsT0]；完全子范畴 [T0_Subcategory] / [T0Spaces]，包含被证明为完全且忠实；Kolmogorov 商 [KolmogorovQuotient] 及 [KolmogorovQuotient_T0] 和投影 [kolmogorov_proj]；泛性质 [kolmogorov_universal] 及其封装 [kolmogorov_universal_arrow]；余单位推论 [t0_reflect_iso]——T0 空间在同构意义上是它自身的 Kolmogorov 商——在两点离散空间上实例化为 [bool_reflect_iso]；以及 [Hausdorff_T0_nn]。

   ** 路线通用箭头，正是 Instance/Ab/TorsionFree.v 为 §IV.3 练习 2 所采取的路径，以及 Instance/Grp/Abelianize.v 为 §III.1 练习 3 所采取的路径：说明 ∃! ([kolmogorov_universal])，将其与 Theory/Universal/Arrow.v 的 [universal_arrow_from_UMP] ([kolmogorov_universal_arrow]) 打包，然后从该文件的 [LeftAdjointFunctorFromUniversalArrows] 及其 [AdjunctionFromUniversalArrows] 中读取函子和伴随，而无需进一步证明。该链中的内容在此处不重新推导。

   ** 宇宙障碍及其强制的设计

   这是该文件的实质，它是一种测量而非偏好。不可区分性的显而易见的表述是“x 和 y 位于完全相同的开集”，这个开集是对 X 的每一个开集量化。在这个库中，该关系不适用，并且被拒绝是一个真正的宇宙不一致，而不是记账上的烦恼。[TopSpace@{o}] (Instance/Top.v) 有 [top_carrier :> SetoidObject@{o o}]，所以一个空间自身的 `≈` 是一个 [crelation@{o o}] —— 在 [Type@{o}] 中取值 —— 而 [IsOpen] 对 [X → Type@{o}] 的谓词进行量化，因此对所有谓词进行量化的关系落在严格高于 [o] 的层次。测量结果：无限制关系展开为 [∀ X : TopSpace@{o}, X → X → Type@{h}] 带有 [o < h]，构建其上的 [SetoidObject@{o o}] 被拒绝，并显示“Cannot enforce ... = o because o < h <= ...”。所以
   Instance/Ab/TorsionFree.v 使用的“相同载体、更粗糙的 `≈`”设计，以及兄弟条款 (a) 使用的设计，在同一个宇宙中对于 [Top] 是不可用的。[SameOpensAll] 保留在文件中作为那个无限制的关系——它是一个完全正常的 [Definition]，它只是不可以成为空间的集合准则——而 [SameOpensAll_SameOpens] 关联了两者。

   可用的，并且是这个文件提供的，是针对其值位于比空间自身层次 [o] 更低的层次 [s] 的 opens 进行的不可区分性测试：

   [SameOpens@{s o} X x y := ∀ U : X → Type@{s},
   IsOpen X U → (U x ↔ U y)]它正好位于 [Type@{o}]，因为 [X → Type@{s} : Type@{o}] 当 [s < o]。每个 [Prop] 值的开集都是这样的 [U]（由于累积性，在每个 [s]），所以被测试的族是慷慨的；下面的两个具体证据都用一个 [Prop] 值的开集分开它们的点。然后，商集带有相同的承载类型，即粗化后的 `≈` [SameOpens X]，并且其开集正好是那些尊重该关系（[kq_open]）的 X 的开集。两个定义看起来像是循环定义，但实际上不是，而打破循环的引理是 [small_open_is_kq_open]：X 的一个在 [s] 级别取值的开集会自动尊重 [SameOpens X]，因为该关系明确说明 x 和 y 在其上是一致的。因此，X 的每个 [s] 级别的开集仍然是商集的开集，[KolmogorovQuotient_T0] 是三行，并且——相同事实的另一半——来自商集的中介映射是连续的，因为 T0 目标上的 [Type@{o}] 值开集通过 [open_proper] 的操作回拉到一个尊重该关系的开集。经典上，当开集是 [Prop] 值的小集合时，[kq_open] 是 X 的拓扑，这是普通的 Kolmogorov 商空间。

   带着这个理解去读 [IsT0]：它是“在所有 [s] 级别的开集上都一致的点相等”，这一要求比在所有开集上一致的要求更强，因为 [SameOpensAll] 蕴含 [SameOpens]，而在这里证明的任何内容都不能反过来。这个限制在陈述中是可见的，而不是隐藏在里面。

   ** 相同承载，无选择公理[KolmogorovQuotient X] 不形成新的载体：[kq_carrier_strict] 由 [eq_refl] 记录其载体是 X 的，并且 [kq_equiv_strict] 记录其 `≈` 是 [SameOpens X]。没有等价类，没有商公理，没有代表被选择，并且 [kolmogorov_proj] 是点上的恒等映射。文件中的所有内容都是 [Type] 值数据：[SameOpens] 是乘积的 Π，其证人被直接拆开，并且在任何地方都没有从 [Prop] 值的存在式中抽取证人——所以没有选择公理出现。所有 76 个常数在全局上下文中都是封闭的，且任何地方都没有 [Axioms:] 行；特别是，这个文件不依赖 Instance/Top/Interval.v、Instance/Top/Homotopy.v 或度量文件，因此标准库的实数公理在其封闭集中没有出现。** 先前技术，测量于 d658518e（该问题的“当前状态”已过时，已被纠正而非重复）

   问题 #372 说“两个环境类别都缺失”，并且“没有 Instance/Top.v”。在 d658518e，这两点都是错误的：
   [Top : Category] 是 Instance/Top.v，其中包括 [TopSpace]、[Continuous]、[ContinuousMorphism]，即离散和非离散构造子，以及已经就位的 Hausdorff 和紧 Hausdorff 全子类别。缺失的正是这个文件提供的内容：在 [.v] 文件中对 'kolmogorov'、'specializ' 和 'indistinguish' 进行不区分大小写的搜索，完全没有拓扑学相关的命中（两个 'kolmogorov' 的命中是在 Structure/Monoidal/Markov.v 中的 Chapman-Kolmogorov，唯一的 'indistinguish' 命中是在 Theory/Algebra/Monoid/Product.v 中关于类型显示的讨论，而 'specializ' 的匹配项是战术 [specialize] 和关于定理特化的文字说明），而对标记 'T0' 的搜索返回了三行——分别在 Adjunction/Additive.v 和 Structure/AbCategory.v——每一行都是 Mac Lane 的短语“whence T0 = 0”，关于加法函子，与此无关。没有 T0 谓词、没有不可区分关系、没有 Kolmogorov 商，也没有反射。

   ** 可重用部分，以及它节省的内容- Instance/Top.v：[TopSpace]及其六个字段，[Continuous]，[ContinuousMorphism]，[Build_ContinuousMorphism]，[Top]，[IsHausdorff]用于[Hausdorff_T0_nn]，以及两个证明空间[Bool_Discrete]和[TwoPoint_Indiscrete]与[bool_setoid_object]。[Sub Top]模式是[Hausdorff_Subcategory] / [HausdorffSpaces] / [Hausdorff_Full]逐字段复制的。  
   - Construction/Subcategory.v：[Subcategory]，[Sub]，[Incl]，[Incl_Faithful]，[Full]，[Full_Implies_Full_Functor]。平凡成立的[shom]是[Hausdorff_Subcategory]和Instance/Rng.v的[CRng_Sub]模式，而[Full]被写为限定形式，因为Construction/Subcategory.v导出了它自己的[Full]，其第一个参数是一个Category。  
   - Construction/Reflective.v：[Reflective]和[reflective_counit_iso]。  
   - Theory/Universal/Arrow.v：上述“路线”下命名的三个常量。树中的商拓扑前例 -- Instance/Top.v 的 [CP_open]，Instance/Top/Wedge.v 的 [wedge_open]，Instance/Top/Pushout.v 的 [tp_open] -- 都通过归纳或闭式关系粘合点，并从头重新导出开性。在这里不需要其中任何一个，也不需要：这个商拓扑并不改变任何点。

   这里的新内容：[SameOpens] 及其四个引理 [SameOpensAll]、[IsT0]、子范畴，五个 [kq_*] 拓扑引理，以及 [KolmogorovQuotient]、[small_open_is_kq_open]、调解器和泛性质 [Hausdorff_T0_nn]，以及三个见证。

   ** 优点，严格优先测量在 [eq_refl] 处保持（在注释之外出现八次，没有一次出现在拒绝中：本段中提到的六个 [Example]，确定了定义性的身份，加上两次在证人证明 [Bool_Discrete_T0] 和 [tri_point_apart] 中的使用——文件中的另外两个 [Example]，[indiscrete_quot_identifies] 和 [tri_quot_merges]，是居民而不是 [eq_refl]）：商的载体是基础空间的，其 `≈` 是 [SameOpens X]（[kq_carrier_strict]，[kq_equiv_strict]）；反射器的对象部分是商（[t0_reflector_obj]）；全局箭头是 [kolmogorov_proj]，其对象是 [KolmogorovT0 X]（[kolmogorov_arrow_is_proj]，[kolmogorov_arrow_obj]——因为 [universal_arrow_from_UMP] 将所提供的态射存储为其构建的逗号对象的第二投影）；并且伴随的单元是应用于任意点的投影（[t0_unit_is_proj] ).退回，每种情况均已诊断原因：- 作为 MORPHISM RECORD 的 unit 仅是 `≈` 投影（[t0_unit_is_proj_hom]）。原因：
   [AdjunctionFromUniversalArrows] 构建 ⌊−⌋ 为 [fun g => fmap[U] g ∘ arrow]，因此类 unit 是一个 COMPOSITE 记录，[fmap[Incl] id ∘ kolmogorov_proj X]; 应用于一个点时，复合简化，而作为 [ContinuousMorphism] 记录则不简化。相同的形式记录在 #371 的 [torsion_unit_is_proj_hom] 和 Instance/Mod/Free.v 的 [free_module_unit_is_insert] 中。更正 (#1347)：作为记录它现在确实简化：unit 是 [kolmogorov_proj X] 在 [eq_refl] （Test/ProbeKolmogorov372.v 的 CONVERSION 1，现在是一个控制），因为 Instance/Sets.v 提供其 identity 和 composite 的 properness 字段作为项。以上原因已被论证；剩余部分属于标准库，模糊引理实例解析已放入两个适当性字段中，一个是恒等的，一个是复合的。在提到的两个案例中，#371的整个 [CMonHom] 记录仍被拒绝（Test/ProbeTorsionFree371.v），而 Instance/Mod/Free.v 的单元——一个 [Sets] 的态射，现在在 [eq_refl] 上是 [fv_insert X]（Test/ProbeSetsTerms1347.v 的控制 C9，主版本 687ac356 拒绝它）。- [KolmogorovQuotient Bool_Discrete] 与 [Bool_Discrete] 同构，但不相等：[bool_reflect_iso] 是 [reflective_counit_iso] 的纯实例化，没有使用任何策略，而 [KolmogorovQuotient Bool_Discrete = Bool_Discrete] 被拒绝。原因：[Discrete_Top] 的 opens 是 `≈` - 尊重的谓词，并且商是一个开集与一个证明它尊重 [SameOpens] 的配对，所以两个 [IsOpen] 字段在项上不同——因此，setoid 字段和每个律字段也是分别不同的。- COUNIT 完全没有被读回。它是另一个转置，[unique_obj (ump_universal_arrows …)]，并且 [ump_universal_arrows] (Theory/Universal/Arrow.v) 与 [Qed] 闭合，因此那一边没有任何归约，也没有在任一方向为它声明 [eq_refl]。- [Hausdorff_T0_nn] 仅产生 [¬ ¬ (x ≈ y)]，并且它是针对 [SameOpensAll]，而不是针对 [SameOpens]。两个独立的原因，都是通过测量而非猜测得出的。首先，逻辑：从“x 和 y 位于相同的开集”以及“x 与 y 分离”可以得到分离对和矛盾，这驳斥了分离并给出了双重否定；将其转化为 [x ≈ y] 是对承载的 `≈` 本身的双重否定消除，而本库没有这个功能。其次，层次：[IsHausdorff] 产生值为 [Type@{o}] 的分离开集，这些不在层次 [s] 的开集 [SameOpens] 测试之中，因此论证甚至没有从 [SameOpens] 开始。因此，这里没有任何内容能从 [IsHausdorff] 推导出 [IsT0]，也没有声称有这样的蕴含；[Bool_Discrete_T0] 是直接证明的，来自一个值为 [Prop] 的开集。

   ** 宇宙在每个常量上使用 [Set Printing Universes] 测量，同时读取粘合剂和约束块。文件自身的内容是在
   [SameOpens@{s o}] 中的严格不等式 [s < o] —— 所测试的 opens 的级别严格低于空间的级别 —— 通过 Instance/Top.v 的习语中的尾随 [+] 声明，并且 [+] 在各版本之间是承重的：没有它，Coq 8.19 和 8.20 会以“宇宙约束没有被声明的约束所暗示”（六个推断的界限对 [prod] 和 [sigT]）拒绝该声明，而 Rocq 9.1 接受它，这是三版本 nix 构建发现的原因，也正是声明未关闭的原因。它传播：[IsT0@{u u0 u1}] 携带 [u0 < u1] 与 [u1 <= u]，并且 [KolmogorovQuotient@{u u0} : TopSpace@{u} → TopSpace@{u}] 携带 [u0 < u]（具有四个继承的 [Projections] 边界），因此商是同一 [Top] 上对象的真正 ENDOfunction——这正是使 [T0_reflector] 以及因此 [Reflective] 记录可形成的原因。两个标识符位于 BINDERS 中，如果只看代码块的阅读者可能会错过它们，并且两者都是 DONORS 的。首先，[Top@{u u1}] 是 [Category@{u u u}]（Instance/Top.v 自注：同构集合位于点的上一级），因此在这里同构和证明被识别；[T0Spaces] 继承了它，打印为 [Category@{u0 u u}]。其次，[Subcategory] 在 [Category@{u u0 u0}] 上声明，而 [Reflective] 在 [Category@{u3 u5 u5}] 上声明，同样的标识再次出现；它受到探针形式化拒绝的保护，在 hom-严格低于证明级别时命名同构集合和身份成功，而 [Subcategory] 被拒绝。以其优势阅读该驳回：它针对 [Subcategory] 发射，而 [Reflective] 无法在不考虑其 [Subcategory] 参数的情况下进行测试，因此 [Reflective] 是否识别任何它自己的内容在此未被衡量。此文件未引入任何识别，也未声称其不可避免。此文件中没有任何常量的约束块包含宇宙方程——每个条目都是 [<] 或 [<=]，在所有 70 个块中测量 76 个常量打印。精确读取 [Set] 测量：该标记出现在此文件常量的 [About] 输出中，恰好在两个地方出现，而且都不是宇宙绑定器或约束块——[Tri@{} : Set]，即 SORT [Inductive Tri : Set] 所声明的，以及 Coq 生成的消解器的动机 [Tri_rec : ∀ P : Tri → Set, …]。文件中没有任何常量的宇宙绑定器或约束条目提到 [Set]；每个宇宙变量满足 [Set <= _] 是 Coq 自身的约定，并未打印，因此对此不做任何声明。

   ** 非空性在两个方向上都已证明，因此子范畴既不为空也不是所有的，并且商被证明可以做一些事情而不会做得太多。

   [Bool_Discrete] 是 T0 ([Bool_Discrete_T0]，通过测试 [Prop] 值的开集 [fun z => z = x])，所以 [T0Spaces] 是非空的并且 [bool_reflect_iso] 可适用。[TwoPoint_Indiscrete] 并不是 ([TwoPoint_Indiscrete_not_T0])：它的开集是统一谓词，所以每一对点都是不可区分的，同时 [true ≈ false] 是 [true = false]。商恰好识别那一对点，其证明写出为 ([indiscrete_quot_identifies]，其证明项是 [indiscrete_points_same_opens])。[Tri_Top] 是混合三点空间：载体 [Tri] 及其打开集构成的谓词无法区分 [Tri_l] 和 [Tri_r]。它不是 T0（[Tri_Top_not_T0]），其商将那一对（[tri_quot_merges]）合并，同时将 [Tri_l] 保持在第三个点（[tri_quot_keeps_point_apart]）之外；[Tri_r] 也与它分开，这从 [SameOpens_sym] / [SameOpens_trans] 可直接推得，但未明言。精确说明这两个否定是如何闭合的，因为两种机制不同：第一种直接从 [tri_open] 的两个分量，在每个开集上证明该关系，并将其传给 [IsT0]；第二种则在单一的 [Prop] 值的开集 [fun z => z = Tri_pt] 上实例化该关系。然后两者都通过离散载体上的 [discriminate] 闭合。在任何地方都没有使用从商映射到第二个空间，也没有对生成的关系进行归纳，因为没有生成的关系。

   ** 未交付- 在 [Hausdorff_T0_nn] 之后没有 T1/T2 链，如上所测量，也不能得到 [IsT0]；没有清晰空间，没有 T3/T4，也没有作为预序的专化顺序，尤其没有与兄弟子句 (a) 的桥梁：空间的专化预序本应是 [Ord] 连接 Mac Lane 练习两半的自然对象，但此处没有构建。更正 (#461)：在 Prop 值空间 [PTopCat] 上，该链现在存在，在 Instance/Top/Separation.v ([PT0], [PT1] 以及正豪斯多夫形式 [PHaus] 及其反射) 和 Instance/Top/Hausdorff.v (正则空间 [PReg] 和 [PT3]) 中；在 [Top] 上，此项依然成立。- 没有一个指向空间的Kolmogorov商，也与Instance/Top/Homotopy.v中的[Toph]或[Top_pointed]没有关系。- 对于[KolmogorovQuotient]除了反射器本身之外，没有任何函子性声明，也没有单独从伴随的单位陈述[kolmogorov_proj]的自然性。- 没有证明[KolmogorovQuotient]在任何范畴意义上是一个商（没有共同等化器，没有[RegularEpi]）；投影没有显示为满射。- 在[SameOpens]和[SameOpensAll]之间除了[SameOpensAll_SameOpens]之外，没有进行比较；没有展示任何空间将它们区分，因此限制到[s]层次的开集并没有被证明是严格的。- 反射的幂等单子不存在。Construction/Reflective/Idempotent.v通过从[T0_Reflective_in_Top]实例化构建它；该实例化没有完成。

   ** 对指导此文件的简报的更正每一个都是测量，而不是意见。(1) 简报的计划提出 [SameOpens] 对所有开集进行量化，并与“[IsOpen := IsOpen X] 原样”做商，指出“将承载者的 `≈` 粗化为‘同意每个开集’可保持每个开子句精确开放”。这在数学上是正确的，但在宇宙层面上是错误的：该关系的层级比空间的 `≈` 大，如上所测并在探针中固定，因此使用层级限制的关系和尊重开集的拓扑。 (2) 简报问 [KolmogorovQuotient_T0] 是否是定义性的；它不是——它是一个三行证明，其内容是 [small_open_is_kq_open] ——因为商的开集是尊重的开集，而不是 X 的原样开集。(3) 预期的简述 [Hausdorff_T0] 可能被削弱为双重否定；实际上出现的确实只有双重否定，而且存在第二个阻碍（分隔开的层级），简述中没有预料到，因此引理是针对 [SameOpensAll] 陈述的。(4) 简述提供了来自 Instance/Top/Coproduct.v 的 [Sum_Top] 作为混合证据“如果它便宜的话”；相反，[Tri_Top] 直接在五十行中构建，这对闭包没有任何增加。简述中给出的每个捐赠行号在此都重新检索过，并且是正确的。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.

Generalizable All Variables.

(*
   * * Topological indistinguishability

   Two points are indistinguishable when every open tested holds of
   one exactly when it holds of the other.  The opens tested are
   those valued at the level [s], strictly below the space's own
   level [o]; see the header for why the unrestricted relation cannot
   be a space's `≈` in this library. 

   --------
   * * 拓扑不可区分性

   当每个被测试的开集在一个点上成立当且仅当它在另一个点上也成立时，两个点是不可区分的。被测试的开集是那些值在 [s] 水平的集合，严格低于空间自身的 [o] 水平；关于为什么不受限制的关系不能在此库中成为空间的 `≈`，见标题说明。
*)

Definition SameOpens@{s o | s < o +} (X : TopSpace@{o}) (x y : X)
  : Type@{o} :=
  ∀ U : X → Type@{s}, IsOpen X U → (U x ↔ U y).

Lemma SameOpens_refl (X : TopSpace) (x : X) : SameOpens X x x.
Proof. intros U HU; split; exact (fun w => w). Defined.

Lemma SameOpens_sym (X : TopSpace) (x y : X) :
  SameOpens X x y → SameOpens X y x.
Proof.
  intros H U HU; destruct (H U HU) as [f g]; split; assumption.
Defined.

Lemma SameOpens_trans (X : TopSpace) (x y z : X) :
  SameOpens X x y → SameOpens X y z → SameOpens X x z.
Proof.
  intros Hxy Hyz U HU.
  destruct (Hxy U HU) as [f1 g1]; destruct (Hyz U HU) as [f2 g2].
  split; auto.
Defined.

(*
 Equivalent points are indistinguishable: this is [open_proper],
 used in both directions. 

 --------
 等效点无法区分：这是 [open_proper]，两端都使用。
*)
Lemma SameOpens_of_equiv (X : TopSpace) (x y : X) :
  x ≈ y → SameOpens X x y.
Proof.
  intros Hxy U HU; split.
  - exact (open_proper X U HU x y Hxy).
  - exact (open_proper X U HU y x (symmetry Hxy)).
Defined.

(*
   * * Agreement on ALL opens

   The unrestricted relation.  It is a perfectly good predicate; what
   it cannot be, for the reason measured in the header, is the
   equivalence of a [SetoidObject@{o o}].  It is used only to state
   [Hausdorff_T0_nn]. 

   --------
   * * 关于所有打开的协议

   不受限制的关系。它是一个完全有效的谓词；根据标题中的原因，它不能是 [SetoidObject@{o o}] 的等价物。它仅用于声明 [Hausdorff_T0_nn]。
*)

Definition SameOpensAll (X : TopSpace) (x y : X) : Type :=
  ∀ U : X → Type, IsOpen X U → (U x ↔ U y).

Lemma SameOpensAll_SameOpens (X : TopSpace) (x y : X) :
  SameOpensAll X x y → SameOpens X x y.
Proof. intros H U HU; exact (H U HU). Defined.

(*
   * * T0 spaces

   Kolmogorov's axiom in its setoid reading: indistinguishable points
   are equal -- the same move Instance/Pos.v makes for
   antisymmetry ([pos_antisym : pos_le x y → pos_le y x → x ≈ y]),
   where the conclusion is the carrier's `≈` rather than Leibniz
   equality. 

   --------
   * * T0 空间

   Kolmogorov 公理在其集合论解读中的表述：不可区分的点是相等的 —— 这是 Instance/Pos.v 在处理反对称性（[pos_antisym : pos_le x y → pos_le y x → x ≈ y]）时采取的相同步骤，
   其中结论是载体的 `≈`，而不是 Leibniz 等式。
*)

Definition IsT0 (X : TopSpace) : Type :=
  ∀ x y : X, SameOpens X x y → x ≈ y.

Definition T0_Subcategory : Subcategory Top :=
  @Build_Subcategory Top
    (fun X : Top => IsT0 X)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition T0Spaces : Category := Sub Top T0_Subcategory.

Lemma T0_Full :
  Category.Construction.Subcategory.Full Top T0_Subcategory.
Proof. intros x y ox oy g; exact I. Defined.

Lemma T0_Incl_Full : Functor.Full (Incl Top T0_Subcategory).
Proof.
  exact (Full_Implies_Full_Functor Top T0_Subcategory T0_Full).
Defined.

Lemma T0_Incl_Faithful : Functor.Faithful (Incl Top T0_Subcategory).
Proof. exact (Incl_Faithful Top T0_Subcategory). Defined.

(* * * The Kolmogorov quotient Same carrier, coarser `≈`, and as opens exactly those opens of X that respect the coarser `≈`. / * * 柯尔莫哥洛夫商 相同的载体，更粗的 `≈`，作为开集的集合正好是 X 中那些遵守更粗 `≈` 的开集。 *)

Definition kq_setoid (X : TopSpace) : SetoidObject :=
  {| carrier := top_carrier X
   ; is_setoid :=
       {| equiv := SameOpens X
        ; setoid_equiv :=
            Build_Equivalence _ (SameOpens_refl X)
              (SameOpens_sym X) (SameOpens_trans X) |} |}.

Definition kq_open (X : TopSpace) (V : top_carrier X → Type) : Type :=
  (IsOpen X V *
   (∀ x y : top_carrier X, SameOpens X x y → V x → V y))%type.

Lemma kq_respects (X : TopSpace) (U V : top_carrier X → Type) :
  (∀ x, U x ↔ V x) → kq_open X U → kq_open X V.
Proof.
  intros HUV [HU Hr]; split.
  - exact (open_respects X U V HUV HU).
  - intros x y Hxy Vx.
    exact (fst (HUV y) (Hr x y Hxy (snd (HUV x) Vx))).
Defined.

Lemma kq_proper (X : TopSpace) (V : top_carrier X → Type) :
  kq_open X V → ∀ x y : top_carrier X, SameOpens X x y → V x → V y.
Proof. intros [HV Hr]; exact Hr. Defined.

Lemma kq_union (X : TopSpace) (I : Type)
      (U : I → (top_carrier X → Type)) :
  (∀ i, kq_open X (U i)) →
  kq_open X (fun x => { i : I & U i x }).
Proof.
  intro HU; split.
  - exact (open_union X I U (fun i => fst (HU i))).
  - intros x y Hxy w.
    exact (projT1 w; snd (HU (projT1 w)) x y Hxy (projT2 w)).
Defined.

Lemma kq_whole (X : TopSpace) : kq_open X (fun _ => poly_unit).
Proof.
  split; [ exact (open_whole X) | intros x y _ w; exact w ].
Defined.

Lemma kq_inter (X : TopSpace) (U V : top_carrier X → Type) :
  kq_open X U → kq_open X V →
  kq_open X (fun x => U x ∧ V x).
Proof.
  intros [HU HrU] [HV HrV]; split.
  - exact (open_inter X U V HU HV).
  - intros x y Hxy w.
    exact (HrU x y Hxy (fst w), HrV x y Hxy (snd w)).
Defined.

Definition KolmogorovQuotient (X : TopSpace) : TopSpace :=
  {| top_carrier   := kq_setoid X
   ; IsOpen        := kq_open X
   ; open_respects := kq_respects X
   ; open_proper   := kq_proper X
   ; open_union    := kq_union X
   ; open_whole    := kq_whole X
   ; open_inter    := kq_inter X |}.

(*
 THE CRUX.  An open of [X] whose values lie at the level the
 indistinguishability relation tests respects that relation
 AUTOMATICALLY, because the relation says in so many words that x
 and y agree on it.  So every such open of X is still an open of the
 quotient, with no hypothesis, and that is what makes the definition
 of [SameOpens] and the definition of [kq_open] non-circular. 

 --------
 关键点。一个 [X] 的开集，其值处于不可区分关系测试的水平，会自动尊重该关系，因为该关系明确表示 x 和 y 在其上是一致的。因此，每个这样的 X 的开集仍然是商空间的开集，无需任何假设，这就是使 [SameOpens] 的定义和 [kq_open] 的定义不会循环依赖的原因。
*)
Lemma small_open_is_kq_open (X : TopSpace) (U : X → Type) :
  IsOpen X U → IsOpen (KolmogorovQuotient X) U.
Proof.
  intro HU; split; [ exact HU | ].
  intros a b Hab; exact (fst (Hab U HU)).
Defined.

Lemma KolmogorovQuotient_T0 (X : TopSpace) :
  IsT0 (KolmogorovQuotient X).
Proof.
  intros x y H U HU.
  exact (H U (small_open_is_kq_open X U HU)).
Defined.

Definition kq_proj_setoid (X : TopSpace) :
  SetoidMorphism (top_carrier X) (top_carrier (KolmogorovQuotient X)).
Proof.
  refine {| morphism := fun x : top_carrier X => x |}.
  intros x y Hxy; exact (SameOpens_of_equiv X x y Hxy).
Defined.

Lemma kq_proj_continuous (X : TopSpace) :
  Continuous X (KolmogorovQuotient X) (kq_proj_setoid X).
Proof. intros V HV; exact (fst HV). Defined.

Definition kolmogorov_proj (X : TopSpace)
  : X ~{Top}~> KolmogorovQuotient X :=
  Build_ContinuousMorphism X (KolmogorovQuotient X)
    (kq_proj_setoid X) (kq_proj_continuous X).

(** * The universal property / * 泛性质 *)

(* A continuous map into a T0 space cannot tell indistinguishable points apart: pulling back a level-[s] open of the target along f gives a level-[s] open of the source. / 连续映射到 T0 空间不能区分无法区分的点：沿着 f 拉回目标的一个级别-[s]开的集合会得到源的一个级别-[s]开的集合。 *)
Definition kq_med_resp {X D : TopSpace} (HD : IsT0 D)
    (f : X ~{Top}~> D) (x y : top_carrier X) :
  SameOpens X x y → continuous_map f x ≈ continuous_map f y.
Proof.
  intro Hxy.
  apply HD.
  intros V HV.
  exact (Hxy (fun z => V (continuous_map f z)) (continuity f V HV)).
Defined.

Definition kq_med_setoid {X D : TopSpace} (HD : IsT0 D)
    (f : X ~{Top}~> D) :
  SetoidMorphism (top_carrier (KolmogorovQuotient X)) (top_carrier D).
Proof.
  refine {| morphism := fun x => continuous_map f x |}.
  intros x y Hxy; exact (kq_med_resp HD f x y Hxy).
Defined.

Lemma kq_med_continuous {X D : TopSpace} (HD : IsT0 D)
    (f : X ~{Top}~> D) :
  Continuous (KolmogorovQuotient X) D (kq_med_setoid HD f).
Proof.
  intros V HV; split.
  - exact (continuity f V HV).
  - intros x y Hxy Vfx.
    exact (open_proper D V HV _ _ (kq_med_resp HD f x y Hxy) Vfx).
Defined.

Definition kolmogorov_med {X D : TopSpace} (HD : IsT0 D)
    (f : X ~{Top}~> D) : KolmogorovQuotient X ~{Top}~> D :=
  Build_ContinuousMorphism (KolmogorovQuotient X) D
    (kq_med_setoid HD f) (kq_med_continuous HD f).

Definition KolmogorovT0 (X : TopSpace) : T0Spaces :=
  (KolmogorovQuotient X; KolmogorovQuotient_T0 X).

Theorem kolmogorov_universal (X : TopSpace) :
  ∀ (d : T0Spaces) (f : X ~{Top}~> Incl Top T0_Subcategory d),
    ∃! g : KolmogorovT0 X ~{T0Spaces}~> d,
      f ≈ fmap[Incl Top T0_Subcategory] g ∘ kolmogorov_proj X.
Proof.
  intros d f.
  unshelve eexists.
  - exact (kolmogorov_med `2 d f; I).
  - intro x; simpl; reflexivity.
  - intros g Hg x; simpl.
    exact (Hg x).
Defined.

Definition kolmogorov_universal_arrow (X : TopSpace)
  : @UniversalArrow Top T0Spaces X (Incl Top T0_Subcategory) :=
  @universal_arrow_from_UMP Top T0Spaces X (Incl Top T0_Subcategory)
    (KolmogorovT0 X) (kolmogorov_proj X) (kolmogorov_universal X).

Definition T0_reflector : Top ⟶ T0Spaces :=
  LeftAdjointFunctorFromUniversalArrows (Incl Top T0_Subcategory)
    kolmogorov_universal_arrow.

Definition T0_adj : T0_reflector ⊣ Incl Top T0_Subcategory :=
  AdjunctionFromUniversalArrows (Incl Top T0_Subcategory)
    kolmogorov_universal_arrow.

Definition T0_Reflective_in_Top : Reflective T0_Subcategory :=
  @Build_Reflective Top T0_Subcategory T0_Full T0_reflector T0_adj.

(** * Strict readbacks / * 严格复述 *)

Example kq_carrier_strict (X : TopSpace) :
  carrier (top_carrier (KolmogorovQuotient X)) = carrier (top_carrier X)
  := eq_refl.

Example kq_equiv_strict (X : TopSpace) (x y : top_carrier X) :
  @equiv _ (is_setoid (top_carrier (KolmogorovQuotient X))) x y
    = SameOpens X x y := eq_refl.

Example t0_reflector_obj (X : TopSpace) :
  `1 (fobj[T0_reflector] X) = KolmogorovQuotient X := eq_refl.

Example kolmogorov_arrow_is_proj (X : TopSpace) :
  @arrow Top T0Spaces X (Incl Top T0_Subcategory)
    (kolmogorov_universal_arrow X) = kolmogorov_proj X := eq_refl.

Example kolmogorov_arrow_obj (X : TopSpace) :
  @arrow_obj Top T0Spaces X (Incl Top T0_Subcategory)
    (kolmogorov_universal_arrow X) = KolmogorovT0 X := eq_refl.

Definition t0_unit (X : TopSpace)
  : X ~{Top}~> Incl Top T0_Subcategory (fobj[T0_reflector] X) :=
  @Category.Theory.Adjunction.unit _ _ _ _ T0_adj X.

Example t0_unit_is_proj (X : TopSpace) (x : X) :
  continuous_map (t0_unit X) x = continuous_map (kolmogorov_proj X) x
  := eq_refl.

Lemma t0_unit_is_proj_hom (X : TopSpace) :
  t0_unit X ≈ kolmogorov_proj X.
Proof. intro x; reflexivity. Defined.

(*
 A T0 space is its own Kolmogorov quotient, up to isomorphism in the
 subcategory: the counit of a full reflective subcategory. 

 --------
 T0 空间是它自身的 Kolmogorov 商，直到子范畴中的同构：一个完全反射子范畴的余单位。
*)
Definition t0_reflect_iso (x : T0Spaces) :
  fobj[T0_reflector] (Incl Top T0_Subcategory x) ≅[T0Spaces] x :=
  reflective_counit_iso T0_Reflective_in_Top x.

(*
   * * Hausdorff spaces

   What comes out is a DOUBLE NEGATION, against the unrestricted
   relation; see the header for the two independent reasons this does
   not give [IsT0]. 

   --------
   * * 豪斯多夫空间

   得到的是一个双重否定，针对不受限制的关系；参见标题中关于这不产生 [IsT0] 的两个独立原因。
*)

Lemma Hausdorff_T0_nn (X : TopSpace) (H : IsHausdorff X) (x y : X) :
  SameOpensAll X x y → ¬ ¬ (x ≈ y).
Proof.
  intros Hxy Hne.
  destruct (H x y Hne) as [U [V [[HU HV] [[Ux Vy] Hdisj]]]].
  exact (Hdisj y (fst (Hxy U HU) Ux) Vy).
Defined.

(* * * Non-vacuity: the two-point discrete space is T0 / * * 非空性：两点离散空间是 T0 *)

Lemma bool_point_open (x : bool_setoid_object) :
  IsOpen Bool_Discrete (fun z : bool_setoid_object => z = x).
Proof. intros a b Hab Ha; simpl in Hab; now subst. Defined.

Theorem Bool_Discrete_T0 : IsT0 Bool_Discrete.
Proof.
  intros x y H.
  symmetry.
  exact (fst (H (fun z : bool_setoid_object => z = x)
                (bool_point_open x)) eq_refl).
Defined.

Definition Bool_Discrete_T0Space : T0Spaces :=
  (Bool_Discrete; Bool_Discrete_T0).

Definition bool_reflect_iso :
  fobj[T0_reflector] (Incl Top T0_Subcategory Bool_Discrete_T0Space)
    ≅[T0Spaces] Bool_Discrete_T0Space :=
  t0_reflect_iso Bool_Discrete_T0Space.

(* * * Non-vacuity: the two-point indiscrete space is not T0 / * * 非空性：二点不可分空间不是 T0 *)

Lemma indiscrete_points_same_opens :
  SameOpens TwoPoint_Indiscrete true false.
Proof.
  intros U HU; split; intro w.
  - exact (HU true false w).
  - exact (HU false true w).
Defined.

Theorem TwoPoint_Indiscrete_not_T0 : IsT0 TwoPoint_Indiscrete → False.
Proof.
  intro H.
  pose proof (H true false indiscrete_points_same_opens) as Heq.
  simpl in Heq; discriminate.
Defined.

Example indiscrete_quot_identifies :
  @equiv _ (is_setoid (top_carrier
              (KolmogorovQuotient TwoPoint_Indiscrete))) true false
  := indiscrete_points_same_opens.

(*
   * * Non-vacuity: a three-point space merging exactly one pair

   The opens are the predicates that cannot tell [Tri_l] from
   [Tri_r]; [Tri_pt] is separated from both by a [Prop]-valued
   open. 

   --------
   * * 非空性：一个三点空间正好合并一对

   开集是无法区分  [Tri_l]  和
   [Tri_r]  的谓词；  [Tri_pt]  通过一个取值为  [Prop]  的开集与两者分开。
*)

Inductive Tri : Set := Tri_l | Tri_r | Tri_pt.

Definition Tri_setoid : SetoidObject :=
  {| carrier := Tri; is_setoid := eq_Setoid Tri |}.

Definition tri_open (U : Tri_setoid → Type) : Type :=
  ((U Tri_l → U Tri_r) * (U Tri_r → U Tri_l))%type.

Lemma tri_respects (U V : Tri_setoid → Type) :
  (∀ x, U x ↔ V x) → tri_open U → tri_open V.
Proof.
  intros HUV [f g]; split; intro w.
  - exact (fst (HUV Tri_r) (f (snd (HUV Tri_l) w))).
  - exact (fst (HUV Tri_l) (g (snd (HUV Tri_r) w))).
Defined.

Lemma tri_proper (U : Tri_setoid → Type) :
  tri_open U → ∀ x y : Tri_setoid, x ≈ y → U x → U y.
Proof. intros _ x y Hxy Ux; simpl in Hxy; now subst. Defined.

Lemma tri_union (I : Type) (U : I → (Tri_setoid → Type)) :
  (∀ i, tri_open (U i)) →
  tri_open (fun x => { i : I & U i x }).
Proof.
  intro HU; split; intro w.
  - exact (projT1 w; fst (HU (projT1 w)) (projT2 w)).
  - exact (projT1 w; snd (HU (projT1 w)) (projT2 w)).
Defined.

Lemma tri_whole : tri_open (fun _ => poly_unit).
Proof. split; intro w; exact w. Defined.

Lemma tri_inter (U V : Tri_setoid → Type) :
  tri_open U → tri_open V → tri_open (fun x => U x ∧ V x).
Proof.
  intros [f1 g1] [f2 g2]; split; intro w.
  - exact (f1 (fst w), f2 (snd w)).
  - exact (g1 (fst w), g2 (snd w)).
Defined.

Definition Tri_Top : TopSpace :=
  {| top_carrier   := Tri_setoid
   ; IsOpen        := tri_open
   ; open_respects := tri_respects
   ; open_proper   := tri_proper
   ; open_union    := tri_union
   ; open_whole    := tri_whole
   ; open_inter    := tri_inter |}.

Lemma tri_pair_same_opens : SameOpens Tri_Top Tri_l Tri_r.
Proof. intros U HU; split; [ exact (fst HU) | exact (snd HU) ]. Defined.

Theorem Tri_Top_not_T0 : IsT0 Tri_Top → False.
Proof.
  intro H.
  pose proof (H Tri_l Tri_r tri_pair_same_opens) as Heq.
  simpl in Heq; discriminate.
Defined.

Lemma tri_point_open :
  IsOpen Tri_Top (fun z : Tri_setoid => z = Tri_pt).
Proof. split; intro w; discriminate w. Defined.

Theorem tri_point_apart : SameOpens Tri_Top Tri_l Tri_pt → False.
Proof.
  intro H.
  pose proof (snd (H (fun z : Tri_setoid => z = Tri_pt) tri_point_open)
                eq_refl) as Heq.
  discriminate Heq.
Defined.

Example tri_quot_merges :
  @equiv _ (is_setoid (top_carrier (KolmogorovQuotient Tri_Top)))
    Tri_l Tri_r := tri_pair_same_opens.

Theorem tri_quot_keeps_point_apart :
  @equiv _ (is_setoid (top_carrier (KolmogorovQuotient Tri_Top)))
    Tri_l Tri_pt → False.
Proof. exact tri_point_apart. Defined.

Definition Tri_T0 : T0Spaces := KolmogorovT0 Tri_Top.
