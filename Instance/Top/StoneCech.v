Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.CompHaus.
Require Import Category.Adjunction.GAFT.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(*
 The Stone–Čech compactification over the tree's [Top]

 Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5):
 §V.6, book p. 125 (PDF p. 134), the compactification of a discrete set by
 the general adjoint functor theorem
 (maclane:V.6:construction-stone-cech-discrete); §V.8, Construction 1,
 book pp. 131–132 (PDF pp. 140–141), the compactification of an arbitrary
 space by the special adjoint functor theorem with the unit interval as
 cogenerator (maclane:V.8:construction1); and §V.8 Exercise 4, the
 injectivity of the unit on completely regular spaces (maclane:V.8:ex4).
 Riehl, "Category Theory in Context", 2nd ed., Example 4.7.12, printed
 p. 178 (PDF p. 198; riehl:4.7:example12).
 nLab:  https://ncatlab.org/nlab/show/Stone-Cech+compactification
 nLab:  https://ncatlab.org/nlab/show/Tychonoff+theorem
 Paper: M. H. Stone, "Applications of the theory of Boolean rings to
 general topology", Trans. Amer. Math. Soc. 41 (1937), 375–481
 Paper: E. Čech, "On bicompact spaces", Ann. of Math. 38 (1937), 823–844

 BACKGROUND.  Stone and Čech found, independently and in the same year,
 that a space X sits inside a compact Hausdorff space βX through which
 every continuous map from X to a compact Hausdorff space extends
 uniquely.  The nLab page reads this categorically: the inclusion of
 compact Hausdorff spaces into all spaces has a left adjoint β, so the
 compact Hausdorff spaces form a reflective subcategory, and the unit
 X → βX is an embedding precisely when X is a Tychonoff space.  It is
 one of the universal mapping problems Samuel collected in 1948
 (Theory/Universal/Arrow.v's header).  Mac Lane uses it twice as the
 showcase of the adjoint functor theorems: through GAFT at the
 underlying-set functor, where the compactification of a discrete set
 has a solution set bounded by the double power set, and through SAFT
 at the inclusion, where Urysohn's lemma makes [0,1] a cogenerator.
 Riehl names what the SAFT construction produces, the closure of the
 image of X in a power of the interval.  The classical direct
 construction is the space of ultrafilters on X; Tychonoff's theorem
 for Hausdorff spaces needs the ultrafilter theorem, "and possibly
 excluded middle", while for locales "no choice whatsoever is needed"
 (nLab, Tychonoff theorem), which is why the constructive home of these
 constructions is locale theory (Johnstone, "Stone Spaces", CUP 1982).

 THE ISSUE'S TWO HEADLINE NAMES ARE NOT CONSTANTS HERE, FOR TWO
 DIFFERENT REASONS.  Stated as the issue pins them, [StoneCech_discrete]
 is a left adjoint to the underlying-set functor [CompHaus_Forget]
 obtained from GAFT, and [StoneCech] a left adjoint to the inclusion
 [CompHaus_Incl] obtained from SAFT with the interval as cogenerator.
 - The §V.6 statement, the adjunction at [CompHaus_Forget], is refuted
 under informative excluded middle at the universe instance that
 [GAFT_CompHaus_only_complete] produces, the one with the objects of
 [CompHaus] at its hom universe ([StoneCech_adjunction_refuted_IEM]).
 [IEM] (Instance/Sets/Classifier/OneLevel.v) is a hypothesis there,
 never an axiom, and it holds classically, so at that instance the
 statement is false in every classical model: for this name the
 obstacle is not a missing proof.  It is refuted as well with the
 objects above the hom universe
 ([StoneCech_adjunction_refuted_IEM_above]); below it the statement
 is not formable.  Both refutations reach the instances
 Refutations.v's COVERAGE records: the [Top] slot at the hom
 universe, the proof that a space is compact Hausdorff at the
 object universe, and the separating opens of its Hausdorff proof
 at the points' universe.  #455's review measured what a draft of
 this bullet denied, that the refutation goes through at an
 instance whose object universe lies above the hom universe: an
 arrow index of [Top], which [IEM] supplies, indexes the arrows of
 [CompHaus] at every object universe at or above the hom universe
 (Refutations.v's [CompHaus_ArrowIndex_of_Top]).
 - The §V.8 statement, the adjunction at [CompHaus_Incl], is NOT
 refuted, and classically it holds.  Refutations.v's argument needs,
 in the left adjoint's domain, an object as large as the arrow
 collection of [CompHaus]; the domain [Top@{h o}] has its points at
 [o], strictly below [h], so the argument does not apply, and the
 book's βX of a space whose points lie in a universe has at most
 2^2^|X| points and lies in that universe (a meta-argument about the
 set-theoretic model with choice, not a theorem here).  What is
 vacuous in this encoding is the adjoint-functor-theorem ROUTE to
 it: SAFT at the inclusion consumes a completeness hypothesis that
 is refuted under [IEM] at every shape universe SAFT accepts there,
 at the instances Refutations.v's COVERAGE records
 ([CompHaus_not_complete_IEM_below], paired with SAFT on one
 hypothesis in [SAFT_Incl_IEM_vacuous_below]; at the shapes at or
 above the objects also [CompHaus_not_complete_IEM] and
 [SAFT_Incl_IEM_vacuous]).  Refutations.v's [SAFT_CompHaus_Incl] is
 a conditional at more instances than those, and there its premise
 stays classically false, a meta-argument (Refutations.v's (3)).
 For this name the obstacle IS a missing proof: a direct
 construction, such as the space of ultrafilters, or an encoding
 under which the route is not vacuous.
 The arguments are in the satellite Instance/Top/StoneCech/Refutations.v.
 The repair is filed as two follow-up issues: #1328 re-encodes [Top] and
 [CompHaus] with Prop-valued opens, putting continuous maps at the
 universe of the points, and #1329 is Stone–Čech proper, over #1328's
 encoding for the adjoint-functor-theorem routes or by a direct
 construction in this one.

 WHY: THE UNIVERSE OF TOP'S HOMS.  Instance/Top.v's header (its point 2)
 places the hom-sets of [Top@{h o}] strictly above the points, o < h,
 because continuity quantifies over the opens of the codomain.  An object
 is a [TopSpace@{o}], of type [Type@{o+1}], so the objects AND the arrows
 of [Top], and of its full subcategory [CompHaus], all fit in [Type@{h}]:
 the category is small relative to its own hom universe.  The adjoint
 functor theorems as the tree states them consume completeness at shapes
 no smaller than the homs: Adjunction/GAFT.v's [GAFT] takes
 [Complete@{h h h cobj}], and Adjunction/SAFT/Characterization.v's
 [SAFT_wellpowered] takes [Complete@{so so h o}] under [h <= so].  At
 those shapes a product indexed by every arrow of [CompHaus] is formable,
 and Freyd's argument (Structure/Complete/Freyd.v) applies: [CompHaus]
 has two parallel arrows from the point to the two-point space that
 evaluation at the point tells apart constructively, so it has no such
 products once its arrows carry an index, and decidable equality of
 objects, which [IEM] supplies, is such an index ([canonical_ArrowIndex]).
 This is the reverse of Structure/Complete.v's size note for [Sets] and
 the algebraic categories, where homs sit at the level of the carriers
 and objects one level up: there the solution sets are the wall; here
 they are free ([taut_sols] below) and completeness is.
 A Prop-valued topology moves the homs down.  Over
 Test/ProbeStoneCech455.v's [p455_TopP], a minimal record of Prop-valued
 opens, that file's [p455_ContHom X Y : Type@{o}], a setoid map with
 Prop-valued preservation of Prop-valued opens, is accepted under a
 closed binder [@{o}], so with an empty constraint block, while
 [ContinuousMorphism X Y] ascribed at [Type@{o}] for [X Y : TopSpace@{o}]
 is refused: "universe inconsistency: Cannot enforce <1> <= o because o <
 <1>" (the generated universe written <1>).  That probe pins both (its
 N6).  With homs at the points' universe the objects sit one level above
 them, as in [Sets].  The expectation, which nothing in this file tests,
 is that Freyd's argument then no longer reaches the universes the
 theorems use and that completeness becomes the classical question
 (Tychonoff) it is in the book.  That re-encoding is #1328, and
 Stone–Čech over it is #1329; neither is attempted here.  Since #457:
 the re-encoding's first item, a Prop-valued space record and category
 with homs at the points' universe, has landed as Instance/Top/Prop.v's
 [PTop] and [PTopCat] (its [PMor X Y] is accepted at [Type@{o}] under
 the closed binder [@{o}], Test/ProbeSubspace457.v's [p457_pmor_at_o]);
 [PCompHaus], the comparison with [Top] and completeness stay with
 #1328, and nothing in this file is rebuilt on it.  CORRECTION (#458):
 the completeness of [PTopCat] itself no longer stays with #1328.
 Instance/Top/Complete.v's [PTop_Complete] proves it at every shape
 universe at or below the points', the points' own included, with no
 hypothesis, and Instance/Top/Complete/Refutations.v refutes it above
 them under informative excluded middle; so the first half of the
 expectation above holds for [PTopCat]: no arrow index of it exists at
 or below the points, constructively ([PTop_no_ArrowIndex_below]
 there).  [PCompHaus], its completeness (the Tychonoff half) and the
 comparison with [Top] stay with #1328.

 WHAT IS CONSUMED AND BUILT, in this file.
 (1) Discrete spaces.  [Discrete_Hausdorff]: every discrete space
 (Instance/Top.v's [Discrete_Top]) is Hausdorff, at every universe,
 separating two points by the opens [z ≈ x] and [z ≈ y].  It is used
 here in place of Instance/Top.v's [Point_Hausdorff], which is
 monomorphised at a [Set] carrier (About: [IsHausdorff@{u Set Set
 Set} Point_Top@{Set}]; that file's comment carries the correction).
 [FinEnum A] is a list meeting every [≈]-class of [A], and
 [Discrete_Compact_of_FinEnum] with [FinEnum_of_Discrete_Compact]
 prove THE DISCRETE SPACE ON [A] IS COMPACT IF AND ONLY IF [A] IS
 FINITELY ENUMERABLE, compactness in [IsCompact]'s strong sense (the
 finite subcover handed over as a list, with a covering index for
 each point).  [Discrete_nat_not_compact] shows the condition is a
 real restriction.  [Bool_CH], [Point_CH] and [Discrete_CH X FX] are
 the objects of [CompHaus] built from these.
 (2) The finite case of §V.6.  [StoneCech_finite X FX] is a
 [UniversalArrow] from [Setoid_Lift X] to [CompHaus_Forget] for every
 finitely enumerable setoid [X]: βX is [X] with the discrete topology,
 the unit is the identity, and a map extends as itself, continuous by
 Instance/Top.v's [out_of_discrete_continuous].  The arrow starts at
 a LIFTED setoid because [CompHaus_Forget] lands in the [Sets] one
 universe up, [Sets@{h s}] (Instance/Top/Forgetful.v's header), so the
 universal arrow is from [Setoid_Lift@{o h} X] for [X] at the points'
 universe [o].
 (3) GAFT at [CompHaus_Forget], reduced to completeness alone.
 [CompHaus_Forget_PreservesImageLimit]: the forgetful functor
 preserves every limit that exists, because it is represented by the
 one-point space; a point of the limit is read off the cone from the
 point that an element of a competing cone determines ([sc_pt_cone]),
 and uniqueness is the limit's.  No decidability and no hypothesis is
 used.  [taut_sols]: the tautological solution set, every object with
 every arrow, fits at the hom universe, because the whole object type
 of [CompHaus] does.  So [GAFT_CompHaus_only_complete] is GAFT with
 one hypothesis left, [Complete@{h h h h} CompHaus], and Mac Lane's
 double-power-set bound is not needed.  That hypothesis is refuted
 under [IEM] in Refutations.v, which pairs the two on a single [comp]
 ([GAFT_CompHaus_IEM_vacuous]): GAFT's own instance is the refuted
 one.  With the objects above the homs [taut_sols] no longer fits
 GAFT, and Refutations.v's [GAFT_CompHaus_IEM_vacuous_above] pairs
 GAFT, with any family of solution sets, against the refutation of
 its completeness hypothesis at that instance.
 (4) Exercise 4 at the level of universal arrows, assuming of the
 compactification nothing beyond the universal arrow itself.  Over
 the underlying-set functor: [unit_injective_of_separated] (points
 separated by maps into compact Hausdorff spaces make the unit
 injective), its converse [separated_of_unit_injective], so the two
 are equivalent, and [unit_injective_of_dec] (decidable equality
 suffices, the separating map being the characteristic map [sc_chi]
 into [Bool_CH]).  At a space, over the inclusion:
 [StoneCech_unit_injective_completely_regular], the issue's pinned
 name, stated PARAMETRICALLY: for any compact Hausdorff [K] whose maps
 separate the points of [X] ([KSeparated K X]), the unit of any
 universal arrow at [X] is injective.  Its converse comes in two
 strengths.  [KSeparated_of_unit_injective_local] asks only that [K]
 separate the points of the universal object, and that premise is
 met: [KSeparated_of_unit_injective_local_at_CompHaus] applies it at
 [CompHaus_Incl_universal K].  [KSeparated_of_unit_injective] asks
 [K] to separate the points of EVERY compact Hausdorff space.  No
 [K] in the tree is shown to meet that premise, and any [K] that
 meets it with ¬¬-stable equality of points yields double-negation
 elimination (Refutations.v's
 [CompHaus_point_separator_stable_DNE]).  At [K] = [0,1],
 [KSeparated] is the point-separating half of complete regularity
 (classically, being functionally Hausdorff), which is what the
 book's hypothesis is used for; the interval itself is not an object
 of [CompHaus] in the tree (NOT DELIVERED).  The only universal arrow
 at [CompHaus_Incl] in the tree is [CompHaus_Incl_universal], at a
 space that is already compact Hausdorff, so the one in-tree
 application of the pinned name is at an identity unit, not at the
 interval.  The issue's note that the restriction to completely
 regular spaces is unnecessary at the level of universal arrows is
 read here, as an interpretation that no constant of this file
 shows, as: classically the universal arrow exists at every space
 whatever its separation, and separation is exactly what makes its
 unit injective (the theorem and its local converse above).
 Instance/Top/StoneCech/Refutations.v then states the metatheorems:
 completeness of [CompHaus] and of [Top] at the theorems' universes
 refuted under an arrow index and under [IEM], at every shape universe at
 or above the hom universe with the limits its COVERAGE records; the
 adjunction at [CompHaus_Forget] refuted under [IEM] at every object
 universe at or above the hom universe, the only ones at which it is
 formable, at the instances its COVERAGE records; the vacuity pairs for
 GAFT and SAFT; SAFT at the inclusion
 reduced to three hypotheses; an injection, from completeness alone, of
 [obj[CompHaus] → bool] into the points of one space; and the cost
 (double-negation elimination) of any cogenerating family of [CompHaus]
 with ¬¬-stable members, and of any single ¬¬-stable [K] that separates
 the points of every compact Hausdorff space.

 STRENGTHS, strict first.
 - [eq_refl]: [StoneCech_finite_obj] (the universal object IS
 [Discrete_CH X FX]), [StoneCech_finite_unit] (the unit IS
 [sc_fin_unit X FX], by definition the identity of [Sets] at
 [Setoid_Lift X]), and [CompHaus_Incl_universal_obj] (the universal
 object at a compact Hausdorff space is the space itself).  A wrong-value
 control for [StoneCech_finite_obj] has to name a genuinely different
 object.  At [X] := [bool_setoid_object] the equation with [Bool_CH] on
 the right is ACCEPTED, [Bool_CH] being [Discrete_CH] at [bool_FinEnum] up
 to conversion ([Bool_Discrete] is [Discrete_Top bool_setoid_object]), so
 a control written that way would pass vacuously.  The wrong-value control
 is the equation with the one-point space [Point_CH] on the right: it is
 refused at the carrier ("cannot unify" [arrow_obj] and [Point_CH]), and
 its value is wrong as a theorem (Test/ProbeStoneCech455.v's N1, whose
 [p455_n1_wrong_value] derives [False] from it).  The same equation
 against [Discrete_CH] at a second enumeration of bool, listing [false]
 first, is refused as well ("cannot unify" [arrow_obj] and [Discrete_CH]
 at that enumeration), but it pins only that the universal object carries
 the enumeration it was built from: the two objects have one space and
 differ in their [Qed] compactness proofs, so that their values differ is
 meta-level (the probe's N2).
 - [UniversalArrow] records: [StoneCech_finite] and
 [CompHaus_Incl_universal], each built by Theory/Universal/Arrow.v's
 [universal_arrow_from_UMP] from unique existence whose uniqueness is
 [≈] of continuous maps, pointwise.
 - [∃!] up to [≈]: [CompHaus_Forget_PreservesImageLimit].
 - [≈] on points, never [=], in all of Exercise 4; data both ways in
 the compactness characterization ([FinEnum] and [IsCompact] are
 [Type]-valued).
 - [False]: [nat_not_FinEnum], [Discrete_nat_not_compact].

 UNIVERSES, measured with [Set Printing Universes. About …], stdlib
 bounds left out.  Every binder is explicit: [o] the points, [h] the hom
 universe of [Top] (and of [CompHaus] where the two coincide), [s] the
 objects of the [Sets] that [CompHaus_Forget] lands in, [j] a shape.

 Discrete_Hausdorff@{h o} : ∀ A : SetoidObject@{o o},
 IsHausdorff@{h o o o} (Discrete_Top@{o o} A)      ( * o < h * )
 FinEnum@{o} : SetoidObject@{o o} → Type@{o}
 StoneCech_finite@{o h …} : ∀ X : SetoidObject@{o o}, FinEnum@{o} X →
 UniversalArrow (Setoid_Lift@{o h} X) CompHaus_Forget
 ( * o < h, h < the Sets level * )
 GAFT_CompHaus_only_complete@{h s …} : Complete@{h h h h} →
 ∃ F : Sets@{h s} ⟶ CompHaus, F ⊣ CompHaus_Forget  ( * h < s * )
 StoneCech_unit_injective_completely_regular@{h o …} :
 ∀ K X, KSeparated K X → ∀ UA : UniversalArrow X CompHaus_Incl, …
 ( * o < h, X : Top@{h o} * )

 All four universes of GAFT's completeness hypothesis are [h]: the
 objects of [CompHaus] are placed at its hom universe, which is exactly
 what makes the tautological solution set legal and what Freyd's
 argument exploits.  A word-bounded [Set] occurs in none of the 41
 readbacks of this file.  One binder was measured to matter: without
 one, [bool_FinEnum] elaborates at [FinEnum@{Set} bool_setoid_object@{Set
 Set}] (About, on the same lemma stated without a binder;
 Test/ProbeStoneCech455.v pins its consequences), which would force
 [Bool_CH], built from it, and so the refutations that use [Bool_CH], to
 a [Set] carrier.  Every constant takes its hypotheses as top-level
 binders; no [Section] is used.

 NON-VACUITY.  [FinEnum] is inhabited ([bool_FinEnum]; the one-point
 space through Instance/Top.v's [Point_Compact]) and not universal
 ([Discrete_nat_not_compact]).  [StoneCech_finite_bool_injective] applies
 [unit_injective_of_dec] to [StoneCech_finite] at the two-point set with
 the decider [sc_bool_dec], and [StoneCech_unit_injective_at_CompHaus]
 applies [StoneCech_unit_injective_completely_regular] at every compact
 Hausdorff [K] to [CompHaus_Incl_universal K] with [KSeparated_self K]:
 the premises of both forms of Exercise 4 are jointly met, at compatible
 universes, by universal arrows built here.  Their conclusions carry no
 new content (at both, the unit is the identity).
 [KSeparated_of_unit_injective_local_at_CompHaus] closes the round trip
 at [CompHaus_Incl_universal K]: all three premises of the local
 converse are met there, the injectivity of the unit by
 [StoneCech_unit_injective_at_CompHaus].  The strong converse
 [KSeparated_of_unit_injective] has no witness: no [K] in the tree is
 shown to meet its premise, and a [K] with ¬¬-stable equality of points
 meets it only at the price of double-negation elimination (see (4)).
 The hypothesis of [GAFT_CompHaus_only_complete] IS refuted under
 [IEM]: that constant is a conditional with a classically false premise,
 kept as the measured reduction, not as a result.

 STALE PREMISES OF THE ISSUE, RE-MEASURED.
 - "No topological categories exist — no [Top], no [CompHaus]": both
 exist, Instance/Top.v (#259) and Instance/Top/CompHaus.v (#413).
 - "SAFT itself is never applied to any concrete category"
 (docs/INHABITATION.md): its [SAFT_wellpowered] row records
 applications at the powerset lattice [Subsets Y] and at
 [Indiscrete], conditionally on [Untruncate] at [Sets], and at
 [(RMod R)^op] (#454).
 - "#413 supplies [CompHaus] and the creation of limits by its
 underlying-set functor, which creates limits, so [CompHaus] is
 complete": #413 formed [CreatesLimit K CompHaus_Forget] but did not
 prove it (Instance/Top/CompHaus.v, NOT DELIVERED (c)), and
 completeness at the universes the theorems use here is refuted
 under [IEM], with the objects of [CompHaus] at its hom universe and
 above it (Refutations.v, COVERAGE).
 - The issue's search for Stone, Čech, Tychonoff, Urysohn and complete
 regularity, narrowed to the terms themselves, finds nothing but
 comment prose outside this development.  Method: grep -E, case-sensitive,
 over the files of _CoqProject other than this development's own
 (these two and Test/ProbeStoneCech455.v), with the pattern
 "Čech|Stone-Cech|[Cc]ompactif|Tychonoff|Urysohn|[Cc]ompletely regular"
 (the issue's case-insensitive pattern also matches words such as
 "ConstOne" and "milestone").  It finds four files:
 Theory/Universal/Arrow.v, Structure/Limit.v (Čech cohomology),
 Instance/Roster.v and Instance/Top/CompHaus.v, every hit inside a
 comment.

 NOT DELIVERED.
 - A constant named [StoneCech_discrete].  Its statement, the §V.6
 adjunction at [CompHaus_Forget], is refuted under [IEM] at the
 instance GAFT produces and at every object universe above it, at
 the instances Refutations.v's COVERAGE records (above).
 - A constant named [StoneCech].  Its statement, the §V.8 adjunction
 at [CompHaus_Incl], is not refuted and holds classically, but
 neither a direct construction nor a non-vacuous route to it is
 built here.
 - #1329 carries both constructions, over #1328's encoding or, where
 the statement is not refuted, by a direct construction in this
 one.
 - Stone–Čech at an infinite set or at a non-discrete space, the
 ultrafilter construction of βX, Tychonoff at any arity and Urysohn's
 lemma; Mac Lane's double-power-set solution set (not needed at these
 universes, see (3)); Riehl's closure-of-the-image description.
 - The interval as an object of [CompHaus], hence the SAFT route with
 the interval cogenerator (the issue's Reviewer line) even as a
 conditional, and the interval form of Exercise 4.
 Instance/Top/Interval.v's [I_Top] is shown neither compact nor
 Hausdorff there, and every constant naming it inherits the stdlib
 axioms [ClassicalDedekindReals.sig_forall_dec] and
 [functional_extensionality_dep] (Print Assumptions [I_Top]; that file
 is among docs/AXIOMS.md's reals-importing files), so none is here.
 The route would be vacuous classically in any case: its completeness
 hypothesis is the refuted one, and Refutations.v's
 [CompHaus_cogenerator_stable_DNE] shows that any cogenerating family
 of [CompHaus] with ¬¬-stable members, the interval's among them,
 costs double-negation elimination.
 - The discrete case as a composite with a packaged [Discrete ⊣
 Forget] on [Top]: Instance/Top/Forgetful.v shows that adjunction
 cannot be packaged as one [Adjunction] record, its two functors
 living on different [Sets].
 - Nothing is registered as an [Instance].

 COUNTS.  41 constants here (22 [Definition], 8 [Lemma], 8 [Theorem],
 3 [Example]), all closed under the global context by their fully
 qualified names, [Print Module] listing exactly these 41, so no
 auxiliary constant is generated.  Seven proofs end [Defined] (by token);
 four are load-bearing, each measured by flipping it alone to [Qed] and
 recompiling this file and its satellite: [sc_pt_cone] (its vertex must
 unfold to the point for [sc_pres_pt]), [sc_pres_map] (unfolded by
 [CompHaus_Forget_PreservesImageLimit]), [sc_chi] (computed by the
 [discriminate] in [unit_injective_of_dec]) and [CompHaus_Incl_universal]
 (its readback [CompHaus_Incl_universal_obj]); the other three,
 [sc_fin_ump], [taut_sols] and [sc_bool_dec], flip with everything green
 and are kept [Defined] as data.  Closure 67 modules excluding self:
 Instance/Top/CompHaus.v costs 11 at the margin, Adjunction/GAFT.v 8,
 each of the other thirteen [Category.*] [Require]s 0 (each dropped
 alone). 

 --------
 树的 [Top] 上的 Stone–Čech 紧化Mac Lane，《为工作中的数学家准备的范畴论》，第2版（GTM 5）：
 第V.6节，书本第125页（PDF第134页），通过一般伴随函子定理对离散集合的紧化
 (maclane:V.6:construction-stone-cech-discrete)；第V.8节，构造1，书本第131–132页（PDF第140–141页），通过特殊伴随函子定理以单位区间作为辅生成元对任意空间的紧化 (maclane:V.8:construction1)；以及第V.8节练习4，完全正则空间中单位元的单射性 (maclane:V.8:ex4)。
 Riehl，《上下文中的范畴论》，第2版，例4.7.12，印刷页178（PDF第198页；riehl:4.7:example12）。
 nLab: https://ncatlab.org/nlab/show/Stone-Cech+compactification
 nLab: https://ncatlab.org/nlab/show/Tychonoff+theorem
 论文：M. H. Stone，《布尔环理论在一般拓扑学中的应用》，美国数学学会会刊（Trans. Amer. Math. Soc.)41 (1937), 375–481 论文：E. Čech, 《关于双紧空间》，数学年刊 38 (1937), 823–844背景。Stone 和 Čech 在同一年独立发现，一个空间 X 嵌入在紧豪斯多夫空间 βX 中，通过它，从 X 到任意紧豪斯多夫空间的每个连续映射都可以唯一扩展。nLab 页面从范畴论的角度这样描述：紧豪斯多夫空间包含在所有空间中具有左伴随 β，因此紧豪斯多夫空间形成一个反射子范畴，并且当且仅当 X 是 Tychonoff 空间时，幺射 X → βX 才是一个嵌入。这是 Samuel 在 1948 年收集的普遍映射问题之一（Theory/Universal/Arrow.v 的标题）。Mac Lane 两次使用它作为伴随函子定理的展示：一次是在基础集合函子处通过 GAFT，其中离散集的紧化具有由双重幂集界定的解集；另一次是在包含函子处通过 SAFT，其中乌里松引理使 [0,1] 成为余生成元。Riehl 将 SAFT 构造产生的称为 X 在区间幂中的像的闭包。经典的直接构造是 X 上的超滤子空间；Tychonoff 定理对于豪斯多夫空间需要超滤子定理，“并且可能需要排中律”，而对于 Locale，“完全不需要选择”（nLab，Tychonoff 定理），这就是为什么这些构造的构造性归宿是 Locale 理论（Johnstone，《Stone Spaces》，CUP 1982）。这个问题的两个头条名称在这里并不是常量，有两个不同的原因。如题中所述，[StoneCech_discrete] 是从 GAFT 得到的基本集合函子 [CompHaus_Forget] 的左伴随，而 [StoneCech] 是从 SAFT 得到的包含函子 [CompHaus_Incl] 的左伴随，使用区间作为共生成器。——§V.6 中的陈述，即 [CompHaus_Forget] 处的伴随，在由 [GAFT_CompHaus_only_complete] 产生的宇宙实例下，在信息排中律条件下被驳斥，该宇宙实例在其 hom 宇宙 ([StoneCech_adjunction_refuted_IEM]) 中具有 [CompHaus] 的对象。[IEM] (Instance/Sets/Classifier/OneLevel.v) 在那里是假设，从未是公理，并且在经典逻辑下成立，因此在该实例中该陈述在每个经典模型中均为假：对于这个名称，障碍不是缺少证明。它也被上述同构宇宙之上的对象所反驳（[StoneCech_adjunction_refuted_IEM_above]）；在其下，该陈述不可形成。两种反驳都达到了实例 Refutations.v 的 COVERAGE 记录：同构宇宙中的 [Top] 插槽、对象宇宙中一个空间是紧致豪斯多夫的证明，以及其豪斯多夫证明在点宇宙中的分离开集。#455 的审查测量了此项目草稿所否认的内容，即反驳在一个对象宇宙位于同构宇宙之上的实例中也成立：[IEM] 提供的 [Top] 的箭头索引索引了 [CompHaus] 在任何等于或高于同构宇宙的对象宇宙中的箭头（Refutations.v 的 [CompHaus_ArrowIndex_of_Top]）。- §V.8 中的陈述，即在 [CompHaus_Incl] 处的伴随，不是被驳斥的，并且在经典意义上它成立。Refutations.v 的论证需要在左伴随的范畴中有一个与 [CompHaus] 的箭集合一样大的对象；而范畴 [Top@{h o}] 的点在 [o]，严格低于 [h]，因此该论证不适用，并且书中所说其点位于某个集合中的空间 βX 至多有 2^2^|X| 个点，并且位于该集合中（这是关于带选择公理的集合论模型的元论证，而非此处的定理）。在这个编码中空洞的，是通向它的伴随函子定理路线：SAFT 在包含时消耗了一个完全性假设，而在每个形宇宙下 [IEM] 都会否定这个假设，SAFT 在那里接受这些实例，在 Refutations.v 的 COVERAGE 中记录了（[CompHaus_not_complete_IEM_below]，与 SAFT 在 [SAFT_Incl_IEM_vacuous_below] 中一个假设配对；在对象之上或之下的形也有 [CompHaus_not_complete_IEM] 和 [SAFT_Incl_IEM_vacuous]）。Refutations.v 的 [SAFT_CompHaus_Incl] 是在更多实例下的条件性，并且在那里的前提仍然是经典地错误，这是一个元论证（Refutations.v 的 (3)）。对于这个名字来说，障碍是一个缺失的证明：一个直接构造，例如超滤子的空间，或者一个使得路线不空洞的编码。这些论证在卫星文件 Instance/Top/StoneCech/Refutations.v 中。修复被归档为两个后续问题：#1328 重新编码 [Top] 和 [CompHaus] 为以命题为值的 opens，将连续映射放在点的宇宙中；#1329 是标准的 Stone–Čech，在 #1328 对伴随函子定理路径的编码基础上，或者通过本文件中的直接构造。原因：Top 的 Homs 的宇宙。Instance/Top.v 的标题（第 2 点）将 [Top@{h o}] 的 hom 集严格放在点之上，o < h，因为连续性对值域的开集进行量化。一个对象是 [TopSpace@{o}]，类型为 [Type@{o+1}]，因此 [Top] 的对象和箭头以及其完全子范畴 [CompHaus] 的所有元素都适合在 [Type@{h}] 中：该范畴相对于其自身的 hom 宇宙是小的。如树所述的伴随函子定理在形状上消耗完备性，其形状不小于 hom：Adjunction/GAFT.v 的 [GAFT] 接受 [Complete@{h h h cobj}]，Adjunction/SAFT/Characterization.v 的 [SAFT_wellpowered] 接受 [Complete@{so so h o}] 在 [h <= so] 下。在那些形状下，每个箭头的 [CompHaus] 的积都是可以形成的，并且 Freyd 的论证（Structure/Complete/Freyd.v）适用：[CompHaus] 从点到两点空间有两条平行箭头，而在点处的评估可以构造性地区分它们，因此一旦其箭头带有索引，它就没有这样的积，而对象的可判等性——[IEM] 提供的，就是这样一个索引（[canonical_ArrowIndex]）。这与 Structure/Complete.v 对 [Sets] 及代数范畴的大小说明相反，在那里同态位于载体层级，对象位于上一层：在那里解集是壁；在这里它们是自由的（见下文 [taut_sols]），并且是完备的。一个 Prop 值的拓扑会将同态降低下来。在 Test/ProbeStoneCech455.v 的 [p455_TopP] 上，这是一个 Prop 值开集的最小记录，该文件的 [p455_ContHom X Y : Type@{o}] 是一个集合态映射，并且具有 Prop 值开集的 Prop 值保持性，它在闭合绑定器 [@{o}] 下被接受，因此约束块为空，而在 [Type@{o}] 上为 [X Y : TopSpace@{o}] 指定的 [ContinuousMorphism X Y] 被拒绝：“宇宙不一致：无法强制执行 <1> <= o，因为 o < <1>”（生成的宇宙写作 <1>）。该探针固定了它的两个点（其 N6）。在这些点的宇宙处的同态中，对象位于它们之上一级，如 [Sets] 所示。预期情况下，该文件中没有任何测试的内容是，Freyd 的论证随后不再涉及定理使用的宇宙，并且完备性成为书中作为经典问题（Tychonoff）的问题。该重新编码是 #1328，而其上的 Stone–Čech 是 #1329；这里未尝试任何操作。自 #457 起：重新编码的第一个项，一个 Prop 值的空间记录和范畴，其 Hom 在点的宇宙中，已作为 Instance/Top/Prop.v 的 [PTop] 和 [PTopCat] 落地（其 [PMor X Y] 在闭合绑定器 [@{o}] 下被接受于 [Type@{o}]，Test/ProbeSubspace457.v 的 [p457_pmor_at_o]）；[PCompHaus]、与 [Top] 的比较以及完整性仍归 #1328，而本文件中没有任何内容在其上重建。更正 (#458)：[PTopCat] 本身的完整性不再归 #1328。Instance/Top/Complete.v 的 [PTop_Complete] 在每个形状的宇宙中证明了它，在点或以下的宇宙中，包括点自身，没有假设；而 Instance/Top/Complete/Refutations.v 在信息排中律下在它们之上反驳了它；因此上述期望的前半部分适用于 [PTopCat]：在点或以下没有它的箭头索引，从构造上讲（[PTop_no_ArrowIndex_below] 在那里）。[PCompHaus]，它的完备性（Tychonoff 半部分）以及与 [Top] 的比较仍然记录在 #1328 中。在这个文件中，被消耗和构建的内容。（1）离散空间。[Discrete_Hausdorff]：每个离散空间（Instance/Top.v 的 [Discrete_Top]）在每个宇宙中都是豪斯多夫的，通过开集 [z ≈ x] 和 [z ≈ y] 分离两个点。这里用它来代替 Instance/Top.v 的 [Point_Hausdorff]，该项在 [Set] 载体上是单态化的（参考：[IsHausdorff@{u Set Set Set} Point_Top@{Set}]；该文件的注释提供了修正）。[FinEnum A] 是一个满足每个 [≈] 类的 [A] 的列表，并且 [Discrete_Compact_of_FinEnum] 与 [FinEnum_of_Discrete_Compact] 证明了 [A] 上的离散空间当且仅当 [A] 是有限可枚举的时是紧致的，紧致性采用 [IsCompact] 的强意义（有限子覆盖以列表形式提供，每个点有一个覆盖索引）。[Discrete_nat_not_compact] 显示该条件是真正的限制。[Bool_CH]、[Point_CH] 和 [Discrete_CH X FX] 是由这些构建的 [CompHaus] 的对象。(2) §V.6 的有限情况。[StoneCech_finite X FX] 是从 [Setoid_Lift X] 到 [CompHaus_Forget] 的 [UniversalArrow]，对于每个有限可枚举的集合 [X]：βX 是带有离散拓扑的 [X]，单位是恒等映射，映射自身扩展，根据 Instance/Top.v 的 [out_of_discrete_continuous] 是连续的。该箭头始于一个提升的集合，因为 [CompHaus_Forget] 落在 [Sets] 一个更高的宇宙中，[Sets@{h s}]（Instance/Top/Forgetful.v 的标题），因此通用箭头是从 [Setoid_Lift@{o h} X] 到 [X]，在点的宇宙 [o] 上。(3) 在 [CompHaus_Forget] 的 GAFT，仅简化为完备性。[CompHaus_Forget_PreservesImageLimit]：遗忘函子保留所有存在的极限，因为它由单点空间表示；极限的一个点从锥体中读出，由竞争锥体的一个元素决定的点（[sc_pt_cone]），唯一性属于极限本身。没有使用可判定性和假设。[taut_sols]：同义解集，每个对象与每个箭头，在同构宇宙中适配，因为 [CompHaus] 的整个对象类型适配。因此 [GAFT_CompHaus_only_complete] 是 GAFT，只剩下一个假设 [Complete@{h h h h} CompHaus]，而且不需要 Mac Lane 的双幂集界限。该假设在 Refutations.v 的 [IEM] 下被驳斥，它将两者在单个 [comp]（[GAFT_CompHaus_IEM_vacuous]）上配对：GAFT 自身的实例是被驳斥的那个。在上面的对象下，homs [taut_sols] 不再适用于 GAFT，而 Refutations.v 的 [GAFT_CompHaus_IEM_vacuous_above] 则适用于 GAFT，对任何解集族，都可以针对其在该实例下完整性假设的反驳。(4) 在普遍箭头的层次上练习4，仅假设除了普遍箭头本身之外的紧化。基于底层集函子：[unit_injective_of_separated]（通过映射到紧豪斯多夫空间分离的点使单位映射成为单射），其逆 [separated_of_unit_injective]，因此两者是等价的，以及 [unit_injective_of_dec]（可判定的等式就足够了，分离映射是特征映射 [sc_chi] 到 [Bool_CH]）。在一个空间上，关于包含：
 [StoneCech_unit_injective_completely_regular]，该问题的固定名称，参数化地陈述为：对于任何紧豪斯多夫空间 [K]，其映射能够分离 [X]（[KSeparated K X]）的点，[X] 上任何泛箭的单位都是单射。其逆命题有两种强度。[KSeparated_of_unit_injective_local] 只要求 [K] 能够分离泛对象的点，而且这一前提得以满足：[KSeparated_of_unit_injective_local_at_CompHaus] 在 [CompHaus_Incl_universal K] 上应用了它。[KSeparated_of_unit_injective] 要求 [K] 能够分离每一个紧豪斯多夫空间的点。在树中的没有 [K] 显示满足该前提，并且任何满足该前提且具有点的 ¬¬-稳定相等性的 [K] 都会导致双重否定消去（Refutations.v 的 [CompHaus_point_separator_stable_DNE]）。在 [K] = [0,1] 时，[KSeparated] 是完整规律的点分离一半（在经典意义上，功能上是豪斯多夫的），这正是书中假设所使用的；该区间本身不是树中 [CompHaus] 的对象（未交付）。树中 [CompHaus_Incl] 的唯一通用箭头是 [CompHaus_Incl_universal]，该空间已是紧致豪斯多夫的，因此固定名称在树内的唯一应用是在恒等单元，而不是在区间上。该问题的注释指出，在普遍箭头的层面上，对完全正规空间的限制是不必要的，这里被理解为一种解释，即此文件中没有显示任何常数，因为按照经典理论，普遍箭头在每个空间中都存在，无论其分离性如何，而分离性正是使其单位同态为单射的原因（上述定理及其局部逆定理）。Instance/Top/StoneCech/Refutations.v 然后陈述了元定理：
 [CompHaus] 的完全性以及 [Top] 在定理的范畴下的完全性
 在箭头索引和 [IEM] 下被驳斥，在所有形状范畴中，位于或高于同构范畴，其限制是其 COVERAGE 记录；
 [CompHaus_Forget] 的拼接在 [IEM] 下被驳斥，在所有对象范畴中，位于或高于同构范畴，这是它可形成的唯一范畴，于其 COVERAGE 记录的实例中；
 GAFT 和 SAFT 的空性对；SAFT 在包含下减少到三个假设；
 单射，仅从完全性即可将 [obj[CompHaus] → bool 注入一个空间的点中；以及
 任何具有 ¬¬-稳定成员的 [CompHaus] 的共生家族的代价（双重否定消除），以及任何单个 ¬¬-稳定的 [K] 的代价，该 [K] 可分离每个紧豪斯多夫空间的点。

 优势，严格先行。- [eq_refl]：[StoneCech_finite_obj]（通用对象是[Discrete_CH X FX]），[StoneCech_finite_unit]（单位是[sc_fin_unit X FX]，根据定义是[Sets]在[Setoid_Lift X]的恒等式），以及[CompHaus_Incl_universal_obj]（紧豪斯多夫空间上的通用对象就是该空间本身）。[StoneCech_finite_obj]的错误值控制必须命名一个真正不同的对象。在[X] := [bool_setoid_object]时，方程右边为[Bool_CH]的情况是允许的，[Bool_CH]在[bool_FinEnum]处与[Discrete_CH]相同，转换后（[Bool_Discrete]是[Discrete_Top bool_setoid_object]），因此以这种方式编写的控制会自动通过。错误值控制是右侧具有单点空间 [Point_CH] 的方程：它在载体处被拒绝（"无法统一" [arrow_obj] 和 [Point_CH]），并且其作为定理的值是错误的（Test/ProbeStoneCech455.v 的 N1，其 [p455_n1_wrong_value] 从中推导出 [False]）。同样的方程在布尔的第二次枚举中针对 [Discrete_CH]，并且先列出 [false]，也被拒绝（"无法统一" [arrow_obj] 和 [Discrete_CH] 在该枚举中），但它只确定那一普遍对象承载了它被创建时的枚举：两个对象有一个空间，但在其 [Qed] 紧致性证明上有所不同，因此它们的值在元层面上有所不同（探针的 N2）。- [UniversalArrow] 记录：[StoneCech_finite] 和 [CompHaus_Incl_universal]，每个由 Theory/Universal/Arrow.v 的 [universal_arrow_from_UMP] 从唯一存在构建，其唯一性是 [≈] 的连续映射，逐点。- [∃!] 到 [≈]：[CompHaus_Forget_PreservesImageLimit]。- [≈] 作用于点，从不 [=]，在整个练习 4 中；紧性表征中的数据是双向的（[FinEnum] 和 [IsCompact] 是 [Type] 值的）。- [False]：[nat_not_FinEnum]，[Discrete_nat_not_compact]。

 宇宙，用 [Set Printing Universes. About …] 测量，stdlib 的界限省略。每个绑定器都是显式的：[o] 是点，[h] 是 [Top] 的同伦宇宙（以及 [CompHaus] 的，当两者重合时），[s] 是 [Sets] 的对象，[CompHaus_Forget] 落入其中，[j] 是一个形状。Discrete_Hausdorff@{h o} : ∀ A : SetoidObject@{o o},
 IsHausdorff@{h o o o} (Discrete_Top@{o o} A)      ( * o < h * )
 FinEnum@{o} : SetoidObject@{o o} → Type@{o}
 StoneCech_finite@{o h …} : ∀ X : SetoidObject@{o o}, FinEnum@{o} X →
 UniversalArrow (Setoid_Lift@{o h} X) CompHaus_Forget
 ( * o < h, h < the Sets level * )
 GAFT_CompHaus_only_complete@{h s …} : Complete@{h h h h} →
 ∃ F : Sets@{h s} ⟶ CompHaus, F ⊣ CompHaus_Forget  ( * h < s * )
 StoneCech_unit_injective_completely_regular@{h o …} :
 ∀ K X, KSeparated K X → ∀ UA : UniversalArrow X CompHaus_Incl, …
 ( * o < h, X : Top@{h o} * )GAFT 完备性假设的所有四个宇宙都是 [h]：[CompHaus] 的对象被放置在其同类宇宙中，这正是使同义解决集合法律化以及 Freyd 的论证所利用的原因。一个单词界限的 [Set] 在该文件的 41 个回读中都未出现。测量到一个绑定器是重要的：没有它，[bool_FinEnum] 会在 [FinEnum@{Set} bool_setoid_object@{Set Set}] 处展开（关于，在没有绑定器的情况下陈述的相同引理；Test/ProbeStoneCech455.v 固定了其后果），这将强制 [Bool_CH]（从它构建）以及使用 [Bool_CH] 的反驳，成为一个 [Set] 承载体。每个常量都将其假设作为顶层绑定器；没有使用 [Section]。非空性。[FinEnum] 是有元素的（[bool_FinEnum]；通过 Instance/Top.v 的 [Point_Compact] 的一点空间）且不是全体的（[Discrete_nat_not_compact]）。[StoneCech_finite_bool_injective] 将 [unit_injective_of_dec] 应用于 [StoneCech_finite] 在两点集合上使用判定器 [sc_bool_dec]，并且 [StoneCech_unit_injective_at_CompHaus] 在每个紧 Hausdorff [K] 上将 [StoneCech_unit_injective_completely_regular] 应用于 [CompHaus_Incl_universal K] 与 [KSeparated_self K]：练习 4 的两种形式的前提在兼容的宇宙中由此处构建的全体箭头共同满足。它们的结论没有带来新的内容（在两者中，单位都是恒等映射）。[KSeparated_of_unit_injective_local_at_CompHaus] 在 [CompHaus_Incl_universal K] 处完成往返：局部逆的三个前提在那里都满足，单位的单射性由 [StoneCech_unit_injective_at_CompHaus] 保证。强对立命题
 [KSeparated_of_unit_injective] 没有证据：树中的任何 [K] 都没有显示满足其前提，而一个具有 ¬¬-稳定点等式的 [K] 只能以双重否定消除为代价满足它（见 (4)）。在 [IEM] 下，[GAFT_CompHaus_only_complete] 的假设 IS 被驳斥：那个常数是一个具有经典上为假的前提的条件，仅作为测量的还原保留，并非作为结果。问题的陈旧前提，重新测量。- “不存在拓扑范畴 — 没有 [Top]，没有 [CompHaus]”：两者都存在，Instance/Top.v (#259) 和 Instance/Top/CompHaus.v (#413)。- “SAFT 本身从未应用于任何具体范畴”（docs/INHABITATION.md）：其 [SAFT_wellpowered] 行记录了在幂集合格 [Subsets Y] 以及在 [Indiscrete] 上的应用，有条件地在 [Sets] 的 [Untruncate] 上，以及在 [(RMod R)^op] 上 (#454)。- “#413 供应了 [CompHaus] 以及其基础集合函子所创建的极限，该函子会创建极限，因此 [CompHaus] 是完整的”：#413 形成了 [CreatesLimit K CompHaus_Forget]，但并未证明它（Instance/Top/CompHaus.v，未交付 (c)），并且在定理在这里使用的宇宙下完整性在 [IEM] 下被驳斥，其对象为 [CompHaus] 于其同构宇宙及其之上（Refutations.v，覆盖范围）。- 关于 Stone、Čech、Tychonoff、Urysohn 以及完全规整性的搜索问题，缩小到这些术语本身，除了本开发之外的评论性文章外没有找到任何内容。方法：使用 grep -E，区分大小写，
 搜索 _CoqProject 中除本开发自身的文件之外的文件
 （除了这两个文件和 Test/ProbeStoneCech455.v），匹配模式
 "Čech|Stone-Cech| [Cc] ompactif|Tychonoff|Urysohn| [Cc] ompletely regular"
 （该问题的大小写不敏感模式也会匹配诸如
 "ConstOne" 和 "milestone" 之类的词）。它找到了四个文件：
 Theory/Universal/Arrow.v、Structure/Limit.v（Čech 上同调）、
 Instance/Roster.v 和 Instance/Top/CompHaus.v，每个命中都在注释中。未交付。- 一个名为 [StoneCech_discrete] 的常量。其陈述，即在 [CompHaus_Forget] 处的 §V.6 附加，在 [IEM] 下被驳斥，在 GAFT 生成的实例及其上方的每个对象宇宙中，在 Refutations.v 的覆盖记录（如上）处亦是如此。- 一个名为 [StoneCech] 的常量。其陈述，即在 [CompHaus_Incl] 处的 §V.8 附加，没有被驳斥，并且在经典逻辑下成立，但在这里既没有构建直接的构造，也没有建立非空的途径。- #1329 包含了两种构造，基于 #1328 的编码，或者在陈述未被驳斥的情况下，通过此处的直接构造。- 在无限集合或非离散空间上的 Stone–Čech，βX 的超滤器构造，任意元下的 Tychonoff 定理以及 Urysohn 引理；Mac Lane 的双幂集解集（在这些宇宙中不需要，见 (3)）；Riehl 的像闭包描述。 - 区间作为 [CompHaus] 的对象，因此即使作为条件，也采用带区间余生成元的 SAFT 方法（这是期刊的审稿人关注点），以及练习 4 的区间形式。Instance/Top/Interval.v 的 [I_Top] 在那里既未显示为紧致也未显示为 Hausdorff，每个为其命名的常量都继承了 stdlib 公理 [ClassicalDedekindReals.sig_forall_dec] 和 [functional_extensionality_dep]（打印假设 [I_Top]；该文件在 docs/AXIOMS.md 的实数导入文件中），因此这里没有。该路线在任何情况下从经典上都是空洞的：它的完备性假设是被驳斥的，Refutations.v 的 [CompHaus_cogenerator_stable_DNE] 显示任何具有 ¬¬-稳定成员的 [CompHaus] 的共同生成族，其中包含区间，都会消耗双重否定消除。- 离散情况作为在 [Top] 上封装的 [Discrete ⊣ Forget] 的复合：Instance/Top/Forgetful.v 显示伴随不能封装为一个 [Adjunction] 记录，它的两个函子存在于不同的 [Sets] 上。- 没有任何东西被注册为 [Instance] 。计数。这里有41个常量（22个[Definition]，8个[Lemma]，8个[Theorem]，3个[Example]），它们通过其完全限定名在全局上下文中都是封闭的，[Print Module] 正好列出了这41个，因此没有生成辅助常量。七个证明以 [Defined] 结束（按标记）；其中四个是承重的，每个通过单独翻转为 [Qed] 并重新编译此文件及其附属文件来测量：[sc_pt_cone]（其顶点必须展开到 [sc_pres_pt] 的点），[sc_pres_map]（由 [CompHaus_Forget_PreservesImageLimit] 展开），[sc_chi]（由 [unit_injective_of_dec] 中的 [discriminate] 计算）和 [CompHaus_Incl_universal]（其回读 [CompHaus_Incl_universal_obj]）；其他三个，[sc_fin_ump]、[taut_sols] 和 [sc_bool_dec]，与所有绿色一起翻转，并作为数据保留 [Defined]。关闭除自身外的 67 个模块：
 Instance/Top/CompHaus.v 在边际上的成本为 11，Adjunction/GAFT.v 为 8，
 其他十三个 [Category.*] [Require] 的成本为 0（单独丢弃时各自为 0）。
*)

(* * * Discrete spaces: separation, and compactness as finite enumerability / * * 离散空间：分离性，以及作为有限可列性的紧性 *)

Lemma Discrete_Hausdorff@{h o +| o < h +} (A : SetoidObject@{o o}) :
  IsHausdorff@{h o o o} (Discrete_Top@{o o} A).
Proof.
  intros x y nxy.
  exists (fun z => z ≈ x). exists (fun z => z ≈ y).
  refine ((_, _), ((_, _), _)); simpl.
  - intros u v Huv Hu. exact (transitivity (symmetry Huv) Hu).
  - intros u v Huv Hu. exact (transitivity (symmetry Huv) Hu).
  - reflexivity.
  - reflexivity.
  - intros z Hx Hy. apply nxy. exact (transitivity (symmetry Hx) Hy).
Qed.

(* A finite enumeration of a setoid: a list meeting every class. / 集合的有限枚举：满足每个类的列表。 *)
Definition FinEnum@{o +} (A : SetoidObject@{o o}) : Type@{o} :=
  ∃ l : list A, ∀ x : A, ∃ y : A, (In y l ∧ x ≈ y)%type.

(*
 Every open cover of a finitely enumerable discrete space has a finite
 subcover: one covering index per listed point. 

 --------
 每个有限可枚举离散空间的开放覆盖都有一个有限子覆盖：每个列出的点对应一个覆盖指标。
*)
Lemma Discrete_Compact_of_FinEnum@{o +} (A : SetoidObject@{o o})
  (F : FinEnum A) : IsCompact (Discrete_Top@{o o} A).
Proof.
  intros I U HU.
  destruct F as [l Hl].
  exists (map (fun y => `1 (fst (snd HU y) ttt)) l).
  intro x. destruct (Hl x) as [y [Hin Hxy]].
  exists (`1 (fst (snd HU y) ttt)). split.
  - exact (in_map (fun y => `1 (fst (snd HU y) ttt)) l y Hin).
  - exact (fst HU _ y x (symmetry Hxy) (`2 (fst (snd HU y) ttt))).
Qed.

(* Conversely, the cover by the singleton classes has a finite subcover, which is a finite enumeration. / 相反，单例类的覆盖有一个有限子覆盖，它是一个有限枚举。 *)
Lemma FinEnum_of_Discrete_Compact@{o +} (A : SetoidObject@{o o})
  (C : IsCompact (Discrete_Top@{o o} A)) : FinEnum A.
Proof.
  destruct (C A (fun a z => z ≈ a)) as [l Hl].
  - split.
    + intros a u v Huv Hu. exact (transitivity (symmetry Huv) Hu).
    + intro x; split.
      * intros _. exists x. reflexivity.
      * intros _. exact ttt.
  - exists l. exact Hl.
Qed.

(*
 The finiteness premise is a real restriction: discrete ℕ is not
 compact. 

 --------
 有限性前提是一个真实的限制：离散的 ℕ 不是紧致的。
*)
Definition sc_nat_setoid@{o +} : SetoidObject@{o o} :=
  {| carrier := nat; is_setoid := eq_Setoid nat |}.

Lemma sc_in_le_fold_max@{} (l : list nat) (y : nat) :
  In y l → le y (fold_right Nat.max O l).
Proof.
  induction l as [|a l IH]; simpl; intro H; [contradiction|].
  destruct H as [<-|H].
  - apply Nat.le_max_l.
  - etransitivity; [exact (IH H)|apply Nat.le_max_r].
Qed.

Lemma nat_not_FinEnum@{o +} :
  FinEnum (sc_nat_setoid : SetoidObject@{o o}) → False.
Proof.
  intros [l Hl].
  destruct (Hl (S (fold_right Nat.max O l))) as [y [Hin Hy]].
  simpl in Hy. subst y.
  exact (Nat.nle_succ_diag_l _ (sc_in_le_fold_max l _ Hin)).
Qed.

Theorem Discrete_nat_not_compact@{o +} :
  IsCompact (Discrete_Top@{o o} sc_nat_setoid) → False.
Proof. intro C. exact (nat_not_FinEnum (FinEnum_of_Discrete_Compact _ C)). Qed.

(*
 The two-point and one-point discrete spaces as objects of [CompHaus],
 at every carrier universe. 

 --------
 在每个承载宇宙中，作为 [CompHaus] 对象的两点和一点离散空间。
*)
Lemma bool_FinEnum@{o +} : FinEnum bool_setoid_object@{o o}.
Proof.
  exists (true :: false :: nil). intros [|].
  - exists true. split; [left; reflexivity | reflexivity].
  - exists false. split; [right; left; reflexivity | reflexivity].
Qed.

Definition Bool_CH@{o +} : CompHaus :=
  (Bool_Discrete@{o}; (Discrete_Compact_of_FinEnum _ bool_FinEnum,
                       Discrete_Hausdorff _)).

Definition Point_CH@{o +} : CompHaus :=
  (Point_Top@{o}; (Point_Compact, Discrete_Hausdorff _)).

(* * * The finite case: the discrete space is its own compactification / * * 有限情况：离散空间本身就是它的紧化 *)

Definition Discrete_CH@{o +} (X : SetoidObject@{o o}) (FX : FinEnum X) :
  CompHaus :=
  (Discrete_Top@{o o} X;
     (Discrete_Compact_of_FinEnum X FX, Discrete_Hausdorff X)).

Definition sc_fin_unit@{o h +} (X : SetoidObject@{o o}) (FX : FinEnum X) :
  Setoid_Lift@{o h} X ~{Sets}~> CompHaus_Forget (Discrete_CH X FX) :=
  @id Sets (Setoid_Lift@{o h} X).

(* A map out of the lifted setoid, read back at the points' universe. / 从提升的集合等价类映射，在点的宇宙中读取回去。 *)
Definition sc_unlift@{o h +} (X : SetoidObject@{o o}) {d : CompHaus}
  (f : Setoid_Lift@{o h} X ~{Sets}~> CompHaus_Forget d) :
  SetoidMorphism@{o o o} X (top_carrier (`1 d)) :=
  @Build_SetoidMorphism (carrier X) (is_setoid X)
    (carrier (top_carrier (`1 d))) (is_setoid (top_carrier (`1 d)))
    (fun x => f x) (fun a b e => proper_morphism f a b e).

Definition sc_fin_ext@{o h +} (X : SetoidObject@{o o}) (FX : FinEnum X)
  {d : CompHaus} (f : Setoid_Lift@{o h} X ~{Sets}~> CompHaus_Forget d) :
  Discrete_CH X FX ~{CompHaus}~> d :=
  (Build_ContinuousMorphism (Discrete_Top X) (`1 d) (sc_unlift X f)
     (out_of_discrete_continuous X (`1 d) (sc_unlift X f)); I).

Definition sc_fin_ump@{o h +} (X : SetoidObject@{o o}) (FX : FinEnum X)
  (d : CompHaus) (f : Setoid_Lift@{o h} X ~{Sets}~> CompHaus_Forget d) :
  ∃! g : Discrete_CH X FX ~{CompHaus}~> d,
    f ≈ fmap[CompHaus_Forget] g ∘ sc_fin_unit X FX.
Proof.
  unshelve refine {| unique_obj := sc_fin_ext X FX f |}.
  - intro x. simpl. apply reflexive_lift.
  - intros v Hv x. simpl. exact (Hv x).
Defined.

Definition StoneCech_finite@{o h +} (X : SetoidObject@{o o})
  (FX : FinEnum X) :
  UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget :=
  universal_arrow_from_UMP _ _ (Discrete_CH X FX) (sc_fin_unit X FX)
    (sc_fin_ump X FX).

Example StoneCech_finite_obj@{o h +} (X : SetoidObject@{o o})
  (FX : FinEnum X) :
  @arrow_obj Sets _ (Setoid_Lift@{o h} X) _ (StoneCech_finite X FX)
    = Discrete_CH X FX := eq_refl.

Example StoneCech_finite_unit@{o h +} (X : SetoidObject@{o o})
  (FX : FinEnum X) :
  @arrow Sets _ (Setoid_Lift@{o h} X) _ (StoneCech_finite X FX)
    = sc_fin_unit X FX := eq_refl.

(* * * The reduction: continuity is free, and so is the solution set / * * 简化：连续性是免费的，解集也是免费的 *)

(* An element [n] of a cone over [CompHaus_Forget ◯ G] is a cone over [G] from the one-point space. / 一个锥体 [n] 上的元素 [n] 来自单点空间的 [G] 的锥体。 *)
Definition sc_pt_cone@{j h +} {J : Category@{j h h}} (G : J ⟶ CompHaus)
  (N : Cone (CompHaus_Forget ◯ G)) (n : vertex_obj[N]) : Cone G.
Proof.
  refine {| vertex_obj := Point_CH;
            coneFrom := @Build_ACone _ _ Point_CH G
              (fun x => ((top_point (`1 (G x)) (cone_leg N x n); I)
                          : Point_CH ~{CompHaus}~> G x)) _ |}.
  intros x y f t. simpl.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f n).
Defined.

Definition sc_pres_pt@{j h +} {J : Category@{j h h}} (G : J ⟶ CompHaus)
  (L : Limit G) (N : Cone (CompHaus_Forget ◯ G)) (n : vertex_obj[N]) :
  carrier (top_carrier (`1 (vertex_obj[L]))) :=
  continuous_map (`1 (limit_med (limit_is_alimit L) (sc_pt_cone G N n))) ttt.

Lemma sc_pt_const_med@{j h +} {J : Category@{j h h}} (G : J ⟶ CompHaus)
  (L : Limit G) (N : Cone (CompHaus_Forget ◯ G)) (n : vertex_obj[N])
  (p : carrier (top_carrier (`1 (vertex_obj[L]))))
  (Hp : ∀ x : J, continuous_map (`1 (limit_leg (limit_is_alimit L) x)) p
                 ≈ cone_leg N x n) :
  sc_pres_pt G L N n ≈ p.
Proof.
  unfold sc_pres_pt.
  refine (limit_med_unique (limit_is_alimit L) (sc_pt_cone G N n)
           (top_point (`1 (vertex_obj[L])) p; I) _ ttt).
  intros x t. simpl. exact (Hp x).
Qed.

Definition sc_pres_map@{j h +} {J : Category@{j h h}} (G : J ⟶ CompHaus)
  (L : Limit G) (N : Cone (CompHaus_Forget ◯ G)) :
  vertex_obj[N] ~{Sets}~> CompHaus_Forget L.
Proof.
  unshelve refine {| morphism := sc_pres_pt G L N |}.
  intros n n' e.
  apply sc_pt_const_med. intro x.
  transitivity (cone_leg N x n').
  - exact (limit_med_commutes (limit_is_alimit L) (sc_pt_cone G N n') x ttt).
  - symmetry. exact (proper_morphism (cone_leg N x) n n' e).
Defined.

Theorem CompHaus_Forget_PreservesImageLimit@{h s +} :
  @PreservesImageLimit CompHaus Sets@{h s} CompHaus_Forget.
Proof.
  intros J G L N.
  unshelve refine {| unique_obj := sc_pres_map G L N |}.
  - intros x n.
    exact (limit_med_commutes (limit_is_alimit L) (sc_pt_cone G N n) x ttt).
  - intros v Hv n. simpl.
    apply sc_pt_const_med. intro x. exact (Hv x n).
Qed.

(*
 Every object with every arrow: legal at the hom universe, because the
 whole object type of [CompHaus] lives there. 

 --------
 每个带箭头的物体：在 hom 宇宙中是合法的，因为整个 [CompHaus] 类型的物体都存在那里。
*)
Definition taut_sols@{h s +} (d : obj[Sets@{h s}]) :
  SolutionSet CompHaus_Forget d.
Proof.
  unshelve refine
    {| sol_index := { K : CompHaus & d ~{Sets}~> CompHaus_Forget K };
       sol_obj := fun p => `1 p;
       sol_arr := fun p => `2 p |}.
  intros c h. exists (c; h). exists id.
  intro x. simpl. apply reflexive_lift.
Defined.

(*
 GAFT with completeness as the one remaining hypothesis.  That hypothesis
 is refuted under [IEM] (Refutations.v); this is the measured reduction,
 not a construction. 

 --------
 GAFT 以完整性作为唯一剩余的假设。根据 [IEM]（Refutations.v），该假设被驳斥；这是测量得到的归约，而不是构造。
*)
Definition GAFT_CompHaus_only_complete@{h s +}
  (comp : @Complete@{h h h h} CompHaus) :
  { F : Sets@{h s} ⟶ CompHaus & F ⊣ CompHaus_Forget } :=
  GAFT CompHaus_Forget comp CompHaus_Forget_PreservesImageLimit taut_sols.

(* * * Exercise 4 at the level of universal arrows / * * 在泛箭头水平的练习 4 *)

Theorem unit_injective_of_separated@{o h +} (X : SetoidObject@{o o})
  (UA : UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget) :
  (∀ x y : X, (∀ (K : CompHaus)
                 (f : Setoid_Lift X ~{Sets}~> CompHaus_Forget K), f x ≈ f y)
              → x ≈ y) →
  ∀ x y : X, @arrow _ _ _ _ UA x ≈ @arrow _ _ _ _ UA y → x ≈ y.
Proof.
  intros Hsep x y E. apply Hsep. intros K f.
  pose proof (unique_property (ump_universal_arrows UA f)) as H.
  rewrite (H x), (H y). simpl.
  exact (proper_morphism
           (continuous_map (`1 (unique_obj (ump_universal_arrows UA f))))
           _ _ E).
Qed.

Theorem separated_of_unit_injective@{o h +} (X : SetoidObject@{o o})
  (UA : UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget) :
  (∀ x y : X, @arrow _ _ _ _ UA x ≈ @arrow _ _ _ _ UA y → x ≈ y) →
  ∀ x y : X, (∀ (K : CompHaus)
                (f : Setoid_Lift X ~{Sets}~> CompHaus_Forget K), f x ≈ f y)
             → x ≈ y.
Proof. intros Hinj x y H. apply Hinj. exact (H _ (@arrow _ _ _ _ UA)). Qed.

(* The characteristic map of a point, into the two-point space. / 一个点的特征映射，映射到二点空间。 *)
Definition sc_chi@{o h +} (X : SetoidObject@{o o})
  (dec : ∀ x y : X, (x ≈ y) + ((x ≈ y) → False)) (x : X) :
  Setoid_Lift@{o h} X ~{Sets}~> CompHaus_Forget Bool_CH.
Proof.
  unshelve refine {| morphism := fun z => if dec z x then true else false |}.
  intros a b e. simpl.
  destruct (dec a x) as [ha|na], (dec b x) as [hb|nb]; try reflexivity.
  - exfalso. apply nb. exact (transitivity (symmetry e) ha).
  - exfalso. apply na. exact (transitivity e hb).
Defined.

Theorem unit_injective_of_dec@{o h +} (X : SetoidObject@{o o})
  (UA : UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget)
  (dec : ∀ x y : X, (x ≈ y) + ((x ≈ y) → False)) :
  ∀ x y : X, @arrow _ _ _ _ UA x ≈ @arrow _ _ _ _ UA y → x ≈ y.
Proof.
  apply unit_injective_of_separated.
  intros x y H.
  pose proof (H Bool_CH (sc_chi X dec x)) as Hc. simpl in Hc.
  destruct (dec x x) as [_|n]; [| destruct (n (reflexivity x))].
  destruct (dec y x) as [hy|ny]; [exact (symmetry hy) | discriminate Hc].
Qed.

(* Non-vacuity: the premises are met by a universal arrow built above. / 非空性：前提由上方构建的普遍箭头满足。 *)
Definition sc_bool_dec@{o +} (x y : bool_setoid_object@{o o}) :
  (x ≈ y) + ((x ≈ y) → False).
Proof.
  destruct x, y; simpl;
    [left; reflexivity | right; discriminate | right; discriminate
    | left; reflexivity].
Defined.

Definition StoneCech_finite_bool_injective@{o h +} :=
  unit_injective_of_dec bool_setoid_object@{o o}
    (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum
     : UniversalArrow (C:=Sets) (Setoid_Lift@{o h} bool_setoid_object@{o o})
         CompHaus_Forget)
    sc_bool_dec.

(* * * Exercise 4 at a space: the unit of the inclusion / * * 练习 4 在空间：包含的单位 *)

(*
 The maps from [X] into [K] separate the points of [X].  At [K] = [0,1]
 this is the point-separating half of complete regularity. 

 --------
 从 [X] 到 [K] 的映射分离了 [X] 的点。在 [K] = [0,1] 时，这是完全正则性的点分离一半。
*)
Definition KSeparated@{h o +} (K : CompHaus) (X : Top@{h o}) : Type@{h} :=
  ∀ x y : top_carrier X,
    (∀ k : X ~{Top}~> CompHaus_Incl K, continuous_map k x ≈ continuous_map k y)
    → x ≈ y.

Theorem StoneCech_unit_injective_completely_regular@{h o +}
  (K : CompHaus) (X : Top@{h o}) (HX : KSeparated K X)
  (UA : UniversalArrow (C:=Top@{h o}) X CompHaus_Incl) :
  ∀ x y : top_carrier X,
    continuous_map (@arrow _ _ _ _ UA) x
      ≈ continuous_map (@arrow _ _ _ _ UA) y
    → x ≈ y.
Proof.
  intros x y E. apply HX. intro k.
  pose proof (unique_property (ump_universal_arrows UA k)) as H.
  rewrite (H x), (H y). simpl.
  exact (proper_morphism
           (continuous_map (`1 (unique_obj (ump_universal_arrows UA k))))
           _ _ E).
Qed.

(*
 The converse, for a [K] that separates the points of EVERY compact
 Hausdorff space.  No [K] in the tree is shown to meet this premise, and
 one with ¬¬-stable equality of points yields double-negation
 elimination (Refutations.v's [CompHaus_point_separator_stable_DNE]). 

 --------
 相反，对于一个分离每个紧豪斯多夫空间点的 [K]。树中的 [K] 没有被证明满足这个前提，而一个具有点的 ¬¬-稳定相等性的 [K] 会产生双重否定消去（Refutations.v 的 [CompHaus_point_separator_stable_DNE]）。
*)
Theorem KSeparated_of_unit_injective@{h o +} (K : CompHaus)
  (sepK : ∀ (Y : CompHaus) (p q : top_carrier (`1 Y)),
            (∀ k : Y ~{CompHaus}~> K,
               continuous_map (`1 k) p ≈ continuous_map (`1 k) q) → p ≈ q)
  (X : Top@{h o}) (UA : UniversalArrow (C:=Top@{h o}) X CompHaus_Incl)
  (Hinj : ∀ x y : top_carrier X,
     continuous_map (@arrow _ _ _ _ UA) x
       ≈ continuous_map (@arrow _ _ _ _ UA) y
     → x ≈ y) :
  KSeparated K X.
Proof.
  intros x y Hk. apply Hinj.
  apply (sepK (@arrow_obj _ _ _ _ UA)). intro k.
  exact (Hk (fmap[CompHaus_Incl] k ∘ @arrow _ _ _ _ UA)).
Qed.

(*
 The same converse from the premise the proof uses: [K] separates the
 points of the universal object alone.  Unlike the premise above, this
 one is met (see [KSeparated_of_unit_injective_local_at_CompHaus]). 

 --------
 证明所使用的前提的相反命题相同：[K] 单独分离了普遍对象的点。与上面的前提不同，这一个得到了满足（见 [KSeparated_of_unit_injective_local_at_CompHaus]）。
*)
Theorem KSeparated_of_unit_injective_local@{h o +} (K : CompHaus)
  (X : Top@{h o}) (UA : UniversalArrow (C:=Top@{h o}) X CompHaus_Incl)
  (sepK : ∀ p q : top_carrier (`1 (@arrow_obj _ _ _ _ UA)),
            (∀ k : @arrow_obj _ _ _ _ UA ~{CompHaus}~> K,
               continuous_map (`1 k) p ≈ continuous_map (`1 k) q) → p ≈ q)
  (Hinj : ∀ x y : top_carrier X,
     continuous_map (@arrow _ _ _ _ UA) x
       ≈ continuous_map (@arrow _ _ _ _ UA) y
     → x ≈ y) :
  KSeparated K X.
Proof.
  intros x y Hk. apply Hinj.
  apply sepK. intro k.
  exact (Hk (fmap[CompHaus_Incl] k ∘ @arrow _ _ _ _ UA)).
Qed.

(*
 Non-vacuity of the pair of premises: at a compact Hausdorff space the
 identity is universal, and the space is separated by itself. 

 --------
 前提对的非空性：在紧致豪斯多夫空间中，恒等映射是普遍的，并且该空间由自身分离。
*)
Definition CompHaus_Incl_universal@{h o +} (K : CompHaus) :
  UniversalArrow (C:=Top@{h o}) (CompHaus_Incl K) CompHaus_Incl.
Proof.
  unshelve refine (universal_arrow_from_UMP _ _ K id _).
  intros d f.
  unshelve refine {| unique_obj := (f; I) |}.
  - intro x. reflexivity.
  - intros v Hv x. simpl in *. exact (Hv x).
Defined.

Example CompHaus_Incl_universal_obj@{h o +} (K : CompHaus) :
  @arrow_obj Top@{h o} _ (CompHaus_Incl K) _ (CompHaus_Incl_universal K) = K
  := eq_refl.

Lemma KSeparated_self@{h o +} (K : CompHaus) :
  KSeparated K (CompHaus_Incl K : obj[Top@{h o}]).
Proof. intros x y H. exact (H id). Qed.

Definition StoneCech_unit_injective_at_CompHaus@{h o +} (K : CompHaus) :=
  StoneCech_unit_injective_completely_regular K
    (CompHaus_Incl K : obj[Top@{h o}]) (KSeparated_self K)
    (CompHaus_Incl_universal K).

(*
 Non-vacuity of the local converse: its three premises are met at the
 identity universal arrow, the injectivity of the unit by the theorem
 just applied. 

 --------
 局部逆命题的非空性：其三个前提在同一通用箭头上得到满足，通过刚应用的定理，单位的单射性也得到满足。
*)
Definition KSeparated_of_unit_injective_local_at_CompHaus@{h o +}
  (K : CompHaus) : KSeparated K (CompHaus_Incl K : obj[Top@{h o}]) :=
  KSeparated_of_unit_injective_local K (CompHaus_Incl K : obj[Top@{h o}])
    (CompHaus_Incl_universal K) (fun p q H => H id)
    (StoneCech_unit_injective_at_CompHaus K).
