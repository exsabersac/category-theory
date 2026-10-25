(**
* Probe for SAFT as a characterization (issue #453)

    Pins the measured boundaries of Adjunction/SAFT/Characterization.v (Mac
    Lane §V.8 Theorem 2, the Lemma inside its proof and the Corollary after
    it, book pp. 129-130; Awodey Remark 9.35; Riehl Theorem 4.7.10,
    Corollary 4.7.13 and the Epilogue's two restatements) and of its three
    satellites Adjunction/SAFT/Characterization/Cover.v,
    Adjunction/SAFT/Characterization/Corollaries.v and
    Adjunction/SAFT/Characterization/Examples.v.  Every negative restates a
    refusal or a readback measured on #453 by its scouts, builders or
    reviews, except N14 (the trivial well-powering at [SAFT_cover_wp_at])
    and N23 (a peel of N22), which are this file's own; N26-N29 are the
    probe review's body-level and [GAFT]-direct forms of N9, N10, N14 and
    N25, numbered after the others so that N1-N25 keep their numbers; N10,
    N20 and N21 pin as refusals three equations first measured as readbacks
    ([About] printing "r = r2", "h = cr" and "su = pa"), and N17 is the
    refusal a scout measured on an unannotated prototype of its own,
    restated at an unannotated wrapper of the library constant.  The
    positive controls restate the files' claims independently.

    THE IMPORT LIST, measured by comparing [Require] lines.  First
    Adjunction/SAFT/Characterization.v's twenty-two lines verbatim and in
    order; then the lines each other target adds, file by file, the target
    modules aside: Cover.v ten, Corollaries.v six and Examples.v thirteen;
    then the four target modules in _CoqProject order.  One supplier module
    is added, immediately before the section that needs it and named there:
    Instance/Sets/SpecialInitial.v before N25 and N29 (its [setsop_comp] and
    [setsop_cog]; Examples.v's header measured N25 with its own import list
    and that file).  So every command above that addition runs under
    exactly the four targets' list.  Structure/Pullback/Wide/Complete.v,
    whose [complete_wide_pullback] is the completeness route of N22-N24,
    was a second addition, before N22, in an earlier revision of this file;
    Adjunction/SAFT/Characterization.v has imported it since its
    [Complete_HasSubobjectWidePullbacks] landed, so it is now one of the
    twenty-two and the addition is gone.  Adjunction/SAFT.v is imported
    after Theory/Subobject.v, so the short name [sub_dom] is
    [SubobjectIndex]'s field and a subobject's is written
    [Subobject.sub_dom], as the targets write it.  Functor/Opposite.v is
    imported after Construction/Opposite.v (Cover.v's list), so [C^op] reads
    as the opposite of a functor unless scoped; N25, N29 and their controls
    write [(Sets@{o so}^op)%category].  A shorter import list is what makes
    a probe pass for no reason.

    DISCIPLINE.  The instrument was checked both ways: the refutation of an
    absent name is refused for that reason, and each of the fifty-six
    definitions and examples of this file that is not a refutation, wrapped
    in one in a copy of this WHOLE file, stops the build at that command
    with the report that the guarded command had been accepted (fifty-six of
    fifty-six, by a script over the copies); [Print Assumptions] of each of
    the fifty-six, by its fully qualified name, reports "Closed under the
    global context".  Every negative other than that instrument is a
    [Definition] or an [Example], never a [Check], so that an open evar or a
    missing instance cannot satisfy it.  Each negative was stripped of its
    refutation keyword in a copy of this WHOLE file, one at a time,
    compiled, and its error read; the kind recorded is the kind of that
    error, and each has positive controls beside it; every identifier a
    negative uses, its own name and the instrument's absent one aside, is
    used by some positive control of this file (by a script over the
    identifiers of the commands).  In one further copy of this WHOLE file
    each negative other than the instrument was followed by a BINDER
    INSTRUMENT, the same universe binder, arguments and return type with a
    trivial body (a hypothesis of the return type, or [Datatypes.unit] where
    the command states none): twenty-eight of the twenty-nine are accepted,
    and N8's is refused with N8's own text, so every negative but N8 is
    refused by its body.  Every UNIVERSE negative is a top-level definition
    whose universes are declared in its own binder or left to inference,
    never a [Section]'s.  Quotations are Rocq 9.1.1's under this file's
    import list, with the error's environment block left out; Rocq prints
    the "cannot unify" parenthetical with the short names in scope, and a
    universe the stripped copy names after itself and a serial number is
    written <1>, <2>, ..., numbered afresh in each quotation in order of
    first appearance.  The file also compiles on Coq 8.19.2 and 8.20.1,
    against copies of prebuilt trees of this library for those versions in
    which every file of the probe's closure whose source differs from this
    tree's, and every file depending on one, was recompiled in dependency
    order; the stripped copies were compiled there as well.  Every one is
    refused on both at the same line and the same character range.  Under
    8.20.1 every error is the Rocq 9.1.1 one up to the serial numbers
    (compared by a script over the copies).  Under 8.19.2 seventeen are (the
    instrument, N1-N7, N11, N18, N21-N27); N8 names its two universes by
    serial numbers, N9 prints a serial number where Rocq 9.1.1 prints [o],
    and N19's chain names [jo] where Rocq 9.1.1 names a generated universe;
    N10 and N17 print as "cannot unify" mismatches, and N12-N16, N20, N28
    and N29 as type mismatches, those ten with no universe-inconsistency
    clause.

    KINDS.  Thirty refutations, counted as the lines that open with the
    refutation keyword: NAME-ABSENCE (the instrument), CONVERSION (N1-N7,
    N18), TYPING (N21), BINDER (N8, whose error is a universe inconsistency
    raised by its own binder, as its binder instrument shows) and UNIVERSE
    (N9-N17, N19, N20, N22-N29): one, eight, one, one and nineteen.

    LABELS.  The pins carry the N-numbers of this file; the #453 reviews and
    builders asked for them under other names, recorded here so that the
    target headers can cite either: the first review's [r_neg], [r_neg2] and
    [r2_neg] are N1, N2 and N3; its [u_ctrl] is N8 and its [u_ctrl2] N9; its
    [h_large] is N22, [h_ctrl] being the control [p453_hw_at_objects]; the
    second builder's M2, M3, N1, N1w, N2c, N3, T2 and M1b are N6, N7, N11,
    N13, N15, N25, N18 and N19, and its N2, measured against a stub of the
    headline file, is N16; the first builder's [m1_gaft_route_obj],
    [m1_thm2_gaft_obj], [m1_hw_of_complete_large] and [m2_sets_hw_large] are
    N4, N5, N22 and N24, and its readback [m2_r2] is N10's; the second
    review's direct [GAFT] form of N1 is N12, and its [wp_trivial]
    application is the positive control [p453_cover_trivial]; the probe
    review's E1, E6, E2 and E5 are N26, N27, N28 and N29, its E2c is N28's
    control [p453_gaft_trivial_small], and its E7 is the control
    [p453_sets_wp_trivial].  The labels are not constants.

    ** The two left adjoints, read back

    N1-N3 (CONVERSION).  Both left adjoints read back by [eq_refl]:
    [p453_left_obj] and [p453_thm2_left_obj] restate
    Adjunction/SAFT/Characterization.v's [SAFT_left_obj] and
    [SAFT_thm2_left_obj], and [p453_iff_left_obj] and [p453_iff_thm2_obj]
    read the same values through the backward halves of
    [SAFT_wellpowered_iff] and [SAFT_iff].  The readbacks discriminate.  N1,
    the Corollary's value against the comma's cogenerator product itself:
      (cannot unify "fobj[projT1 (SAFT_wellpowered U comp cont G WP)] d" and
      "snd (projT1 (cogen_prod (Comma_Complete cont comp) (comma_cogenerator
      U d G)))").
    N2, against the intersection of the EMPTY class [fun _ => False], which
    differs from the readback in that one predicate: the same head and "snd
    (projT1 (Subobject.sub_dom (complete_intersection … False)))))", the
    middle elided here.  N3, Theorem 2's value against the product:
      (cannot unify "fobj[projT1 (SAFT_thm2 U comp cont G HW HU)] d" and
      "snd (projT1 (cogen_prod (Comma_Complete cont comp) (comma_cogenerator
      U d G)))").

    N4, N5 (CONVERSION).  The same assembly through Adjunction/GAFT.v's
    [GAFT_from_initials], which ends in [Qed]: the routes are formed
    ([p453_gaft_route], [p453_thm2_gaft_route]), and their readbacks, the
    transparent controls' statements with the route in place of the
    constant, are refused,
      (cannot unify "fobj[projT1 (p453_gaft_route U comp cont G WP)] d" and
      "snd (projT1 (Subobject.sub_dom (complete_intersection … True)))))")
    and
      (cannot unify "fobj[projT1 (p453_thm2_gaft_route U comp cont G HW HU)]
      d" and "WPull (HW … `1 (k)))"),
    the middles elided.  So the transparent assembly of both theorems,
    through Theory/Universal/Arrow.v's
    [LeftAdjointFunctorFromUniversalArrows], is what the readbacks rest on.

    N6, N7 (CONVERSION).  Cover.v's route through [GAFT] IS [GAFT] at its
    solution sets ([p453_cover_is_gaft], restating [SAFT_cover_wp_is_GAFT])
    and agrees with the Corollary's left adjoint up to isomorphism
    ([p453_cover_iso], [SAFT_cover_wp_iso]); N6, the two left adjoints at
    [eq_refl]:
      (cannot unify "projT1 (SAFT_cover_wp U comp cont G WP)" and "projT1
      (SAFT_wellpowered U comp cont G WP)").
    The two routes index the same family ([p453_same_index], restating
    [comma_cogenerator_index]); N7, their products at [eq_refl]:
      (cannot unify "snd (projT1 (cogen_prod (Comma_Complete cont comp)
      (comma_cogenerator U d G)))" and "saft_prod U comp G d").

    ** The regime of the theorems

    N8 (BINDER; an instrument).  [p453_small] and [p453_small_iff] accept
    the Corollary with the homs strictly below the shapes and the shapes
    strictly below the objects ([h < so, so < o, c < so, w < h]), and
    [p453_thm2_small] and [p453_thm2_small_iff] accept Theorem 2 at [h < so,
    so < o, c < so, o < q, h < q].  That the acceptances hold at that
    regime, and not at a collapse of it, is read off [About]: [p453_small]
    keeps [h < so], [so < o], [c < so] and [w < h], [p453_thm2_small] keeps
    [o < q], [h < so], [so < o], [c < so] and [h < q], and neither carries
    an equation.  N8 is the Corollary's command with [so < h], refused over
    the whole command:
      Universe inconsistency. Cannot enforce h <= so because so < h.
    That text is the binder's own: [Complete@{so so h o}] declares [h] at or
    below its first slot (Structure/Complete.v), whatever the body, as
    Test/ProbeSpecialInitial452.v's N4 records, and N8's binder instrument
    is refused with the same text.  What N8 pins is only that a binder's
    constraints are enforced.  [p453_t_below_pa] and [p453_pa_below_t]
    accept the Corollary with [WellPowered]'s [t] and
    [PreservesImageLimit]'s auxiliary [pa] apart in both orders: the "t =
    pa" collapses (a) and (b) Adjunction/SAFT/Characterization.v's header
    records as removed stay removed.  [p453_thm2_q_below_r] accepts Theorem
    2 with the class index strictly below both wide-pullback universes, so
    its collapse (c), "q = r" and "q = rd", stays removed too; and
    [p453_cover_t_below_pa] and [p453_cover_pa_below_t] (placed with the
    controls without a negative) do the same for Cover.v's [saft_cover_at],
    whose readback once carried "t = pa".

    N9 (UNIVERSE).  Theorem 2's class index below the objects, the control
    [p453_thm2_small] differing from it in [o < q] alone:
      The term "HW" has type "HasSubobjectWidePullbacks@{o h q r k} C" while
      it is expected to have type "HasSubobjectWidePullbacks@{o h <1> <2>
      <3>} C" (universe inconsistency: Cannot enforce <1> <= q because q < o
      <= <1>).
    That refusal records [SAFT_thm2]'s own declared bound: its binder
    carries [o <= q], and <1> is its [q].  N26 is the cause at the body.
    [least_index], the corresponding family of the comma's cogenerator
    product, lives at or above the objects ([About least_index]: [o <=
    lq]), and [SAFT_thm2_initial] asks [HW] to intersect it: the same
    application, alone, is accepted with the index at or above the objects
    ([p453_least_index_at_objects], [o <= q]) and N26, at [q < o]:
      The term "least_index U d (cogen_prod (Comma_Complete cont comp)
      (comma_cogenerator U d G))" has type "Type@{<1>}" while it is expected
      to have type "Type@{q}" (universe inconsistency: Cannot enforce <1> <=
      q because q < o <= <1>).

    N10 (UNIVERSE).  [HU]'s C-side wide-pullback universe declared strictly
    above [HW]'s:
      The term "HU" has type "PreservesWidePullbacks@{o h dobj h pw q r2 rd}
      U" while it is expected to have type "PreservesWidePullbacks@{o h dobj
      h <1> q r <2>} U" (universe inconsistency: Cannot enforce r = r2
      because r < r2).
    The control declares [r <= r2] ([p453_thm2_r_le]) and is accepted, the
    equation added.  That refusal records [SAFT_thm2]'s own binder, which
    gives [HW] and [HU] one [r].  N27 is the cause at the body:
    [SAFT_thm2_initial]'s body restated with [HU]'s slot [r2] apart from
    [HW]'s [r] is accepted at [r <= r2] ([p453_thm2_initial_r_le], [About]
    printing "r = r2") and refused at [r < r2] where
    [wide_pullback_is_pullback] hands [HW]'s cone to [HU]:
      The term "wide_pullback_is_pullback (HW ?z0 (∃ y, ?P1 y) (λ k : ∃ y,
      ?P1 y, `1 (k)))" has type "IsWidePullback@{q r o h} …" while it is
      expected to have type "IsWidePullback@{q r2 o h} …" (universe
      inconsistency: Cannot enforce r = r2 because r < r2),
    the arguments elided.  The first builder read "r = r2" back from an
    application of [SAFT_thm2] naming the two apart (the shape of N10's
    control), and the first review fold from [SAFT_thm2_initial]'s restated
    body (the shape of N27's).

    ** Well-poweredness one universe up, at the pin

    N11-N13 (UNIVERSE).  At [Sets@{o so}] without [Untruncate], the
    unconditional well-powerings in tree include two, both indexed strictly
    above the homs [o]: Instance/Sets/WellPowered.v's
    [Sets_WellPoweredAt_up], whose index sits at its own upper universe, and
    Structure/WellPowered.v's [wp_trivial], whose index [SubObj x] sits at
    or above the objects' [so] ([p453_sets_wp_trivial] states it at [so],
    [WellPoweredAt@{so so so o so}]).  Cover.v's [saft_cover_at] accepts
    each ([p453_cover_up] and [p453_sets_cover_trivial], a small
    [Cogenerator] taken as a hypothesis since none is built without
    [Untruncate]), and [saft_solution_set_at] accepts the first, its index
    universe left free ([p453_solution_set_up]).  N11, [SAFT_cover_wp_at],
    whose binder declares [w <= h]:
      The term "Sets_WellPoweredAt_up ?X" has type "WellPoweredAt@{<1> <2>
      <2> <3> <1>} ?X" while it is expected to have type "WellPoweredAt@{<4>
      so <5> o <6>} (saft_prod@{so so o o <7>} Id[Sets@{o so}]
      Sets_Complete@{o so} G d)" (universe inconsistency: Cannot enforce <4>
      = <6> because <4> <= <8> < <6>).
    N11 records that constant's own declared bound; N12 is the same step
    with Adjunction/GAFT.v's [GAFT] applied directly to the solution sets,
    so that the pin is [GAFT]'s:
      The term "saft_solution_set_at Id[Sets] Sets_Complete
      Sets_Id_PreservesImageLimit G d (Sets_WellPoweredAt_up (saft_prod
      Id[Sets] Sets_Complete G d))" has type "SolutionSet@{<1> so so o}
      Id[Sets@{o so}] d" while it is expected to have type "SolutionSet@{o
      so so o} Id[Sets@{o so}] d" (universe inconsistency: Cannot enforce
      <1> = o because o < <2> <= <1>).
    [GAFT]'s solution sets are indexed at the homs.  N13, #451's
    [WellPowered] itself, before any theorem is applied ([p453_wp_up_at] the
    per-object control):
      The term "Sets_WellPoweredAt_up x" has type "WellPoweredAt@{<1> <2>
      <2> o <1>} x" while it is expected to have type "WellPoweredAt@{<3> so
      <4> o <5>} x" (universe inconsistency: Cannot enforce <3> = <5>
      because <3> <= <6> < <5>).
    Under [Untruncate] the small well-powering meets the pin, and both
    routes are accepted ([p453_sets_id], [p453_sets_id_cover]).

    N14, N28 (UNIVERSE).  The cover needs no well-poweredness: at an
    arbitrary complete, continuous, cogenerated [C], Structure/
    WellPowered.v's [wp_trivial], indexed by [SubObj] itself, supplies
    [saft_cover_at]'s datum ([p453_cover_trivial], a POSITIVE control, the
    datum at [wp_trivial]'s own bounds, its index [w] with [o <= w] and [h
    <= w]), so the cover follows from completeness, preservation and the
    cogenerating family.  [SAFT_cover_wp_at] takes [wp_trivial] when the
    objects fit in the homs ([o <= h], [p453_cover_wp_trivial_small]), and
    N14, the same at [h < o]:
      The term "wp_trivial (saft_prod U comp G d)" has type
      "WellPoweredAt@{<1> o <2> h <3>} (saft_prod@{o dobj h h <4>} U comp G
      d)" while it is expected to have type "WellPoweredAt@{<5> o <6> h <7>}
      (saft_prod@{o dobj h h <8>} U comp G d)" (universe inconsistency:
      Cannot enforce <1> = <5> because <5> <= <9> < o <= <1>).
    That refusal records [SAFT_cover_wp_at]'s own declared [w <= h], as
    N11's does.  N28 is the same step with [GAFT] applied directly to the
    solution sets, so that the pin is [GAFT]'s: accepted at [o <= h]
    ([p453_gaft_trivial_small]), and at [h < o]
      The term "saft_solution_set_at U comp cont G d (wp_trivial (saft_prod
      U comp G d))" has type "SolutionSet@{<1> dobj o h} U d" while it is
      expected to have type "SolutionSet@{h dobj o h} U d" (universe
      inconsistency: Cannot enforce <1> = h because h < o <= <2> <= <1>).
    [wp_trivial]'s index is at or above the objects and [GAFT]'s solution
    sets are indexed at the homs: it is at [GAFT]'s pin that
    well-poweredness bites.

    ** The large cogenerating family of [Sets]

    N15, N16 (UNIVERSE).  Instance/Sets/Cogenerator.v's
    [Sets_Cogenerator_large], indexed by all objects, is a [Cogenerator] of
    [Sets] ([p453_large_cog]), and the Corollary takes it over a
    completeness datum whose shape universe is its index universe
    ([p453_large_cog_abstract], the datum a hypothetical variable).  N15,
    through Cover.v's [SAFT_cover_wp], whose [Cogenerator@{h o h}] indexes
    the family at the homs whatever completeness datum is supplied:
      The term "Sets_Cogenerator_large" has type "Cogenerator@{<1> <2> <3>}
      Sets@{<3> <2>}" while it is expected to have type "Cogenerator@{o so
      o} Sets@{o so}" (universe inconsistency: Cannot enforce <3> = o
      because <3> < o).
    and N16, through [SAFT_wellpowered], whose [Cogenerator@{c o h}] carries
    [c <= so], at [Sets_Complete], whose shape universe is the homs:
      The term "Sets_Cogenerator_large" has type "Cogenerator@{<1> <2> <3>}
      Sets@{<3> <2>}" while it is expected to have type "Cogenerator@{<4> so
      o} Sets@{o so}" (universe inconsistency: Cannot enforce <3> = o
      because <3> < <1> <= o).

    ** The binders are load-bearing

    N17 (UNIVERSE).  [p453_unannotated] wraps [SAFT_wellpowered] with no
    universe annotation; minimization then puts the well-powering's index at
    the homs ([About] reads its [WellPowered] with index universe and hom
    universe equal, measured in a scratch file carrying the four targets'
    import list).  The library constant takes Examples.v's index [Set],
    strictly below the homs ([p453_indiscrete_set_index], restating
    [indiscrete_saft]); the wrapper takes the index at the homs
    ([p453_unannotated_hom_index]) and N17, the index at [Set]:
      The term "Indiscrete_WellPowered Type" has type "WellPowered@{o j Set
      o <1>} (Indiscrete@{o j j} Type@{j})" while it is expected to have
      type "WellPowered@{o j j <2> <3>} (Indiscrete@{o j j} Type@{j})"
      (universe inconsistency: Cannot enforce Set = j).
    A scout measured this refusal on an unannotated prototype of its own
    through [GAFT]; the wrapper here is a different constant, with the same
    kind and the same cause.

    ** The cover's lift and the corollaries

    N18 (CONVERSION).  [saft_lift]'s cone takes its [Compose] universe from
    [cont]: the body at [pa] is accepted ([p453_lift_at_pa]), and N18, with
    a universe [pc] strictly above [pa] in its place, is refused by
    conversion, the two types differing in that universe alone:
      (cannot unify "Functor.Compose_obligation_1@{dobj so o pc h} Roof@{so
      h}^op C D U (ASpan@{so o <1> h} (saft_kappa@{o dobj h so dp cp} U comp
      G d c h) (cogen_canonical@{cp so h so o} comp G c))^op" and
      "Functor.Compose_obligation_1@{dobj so o pa h} Roof@{so h}^op C D U
      (ASpan@{so o <1> h} (…) (…))^op"),
    the second term's arguments elided, identical to the first's.

    N19 (UNIVERSE).  Riehl 4.7.13's proviso: the Corollary at [@Diagonal C
    J] is accepted with the shapes at or below the homs ([p453_diag_small]),
    and the diagonal alone with them above ([p453_diag_alone]); N19, the
    Corollary there:
      The term "Diagonal J" has type "@Functor@{o h h <1> <2> <2>} C
      (@Fun@{jo h o h <1> <2> <3>} J C)" while it is expected to have type
      "@Functor@{<4> <5> <5> <6> <5> <5>} ?C ?D" (universe inconsistency:
      Cannot enforce <2> = h because h < <7> <= <2>).
    [Fun J C]'s homs sit at or above [J]'s objects, and the theorem shares
    [C]'s hom universe with [D]'s.

    N20 (UNIVERSE).  [saft_cocomplete]'s colimit-datum universe is the homs,
    inherited from #353's [Diagonal_left_adjoint_HasColimits]: declared at
    or above them ([p453_cocomplete_cr_le]) it is accepted, the equation
    added, and N20, strictly above:
      The term "Diagonal_left_adjoint_HasColimits (projT2 (saft_colim C comp
      G WP J : ∃ L : ([J, C]) ⟶ C, L ⊣ Diagonal J)) F" has type "Colimit@{h
      jo h o} F" while it is expected to have type "Colimit@{cr jo h o} F"
      (universe inconsistency: Cannot enforce h = cr because h < cr).

    N21 (TYPING).  [continuous_Set_functor_representable_iff] carries [su =
    pa] ([About]), [su] the objects of [Sets@{h su}], and
    [continuous_Set_functor_representable] does not: the latter is accepted
    at [pa < su] ([p453_repr_pa_below_su]), the biconditional at [pa <= su]
    ([p453_repr_iff_pa_le_su]), and N21, the biconditional at [pa < su], is
    refused with no parenthetical, the two types differing in
    [PreservesImageLimit]'s seventh universe alone:
      The term "continuous_Set_functor_representable_iff K comp G WP" has
      type "Representable@{<1> <2> su o h} K ↔ PreservesImageLimit@{o h su h
      <3> so su so}" while it is expected to have type "Representable@{ra rt
      su o h} K ↔ PreservesImageLimit@{o h su h pl so pa so}".
    Peeled to its donor, Adjunction/Representability/Sets.v's
    [preserves_image_of_representable], the refusal is by conversion at the
    cone's [Compose] universe, [su] against [pa] (measured in a scratch file
    carrying the four targets' import list); so this is the same
    identification as N18's, and N21 is not reported as a universe
    inconsistency.

    ** Wide pullbacks of subobjects from completeness

    N22-N24 (UNIVERSE).  Completeness supplies
    Adjunction/SAFT/Characterization.v's [HasSubobjectWidePullbacks] when
    the objects fit in the shapes: with the index at the shapes
    ([p453_hw_at_shapes]) and at the objects ([p453_hw_at_objects]), both at
    [o <= so].  The second term IS that file's
    [Complete_HasSubobjectWidePullbacks] at the index at the objects
    ([p453_hw_is_library], by [eq_refl]); N22 and N23 restate the body
    rather than apply the constant, whose binder declares its index at or
    below the shapes ([q <= so]), so that a refusal is the body's and not
    that declaration's.  N22, the second at [so < o], refused at the index
    while instantiating an evar:
      The term "i" has type "?J" while it is expected to have type "I"
      (unable to find a well-typed instantiation for "?J": cannot ensure
      that "Type@{o}" is a subtype of "Type@{<1>}").
    N23 peels it, the family's index given explicitly (control
    [p453_hw_index_ok] at [o <= so]):
      The term "I" has type "Type@{o}" while it is expected to have type
      "Type@{<1>}" (universe inconsistency: Cannot enforce o <= <1> because
      <1> <= <2> < o).
    N24, at [Sets@{o so}], [Sets_Complete]'s shapes at the homs: the index
    at the homs is accepted ([p453_sets_hw_small], and the library constant
    there, [p453_sets_hw_library]) and at the objects refused,
      The term "Subobject.sub_mono (S i)" has type "Subobject.sub_dom (S i)
      ~{ Sets }~> x" while it is expected to have type "?A i ~{ Sets }~> ?z"
      (universe inconsistency: Cannot enforce o = <1> because o < so <= <2>
      <= <1>).
    Where the completeness route does apply, every premise of Theorem 2 is
    inhabited: [p453_thm2_subsets], at the thin [Subsets Y] with [U :=
    InverseImage f], both preservation premises read off
    [image_preimage_adjunction f] itself (so the conclusion was known).
    Adjunction/SAFT/Characterization/Examples.v's
    [subsets_inverse_image_thm2] IS that assembly
    ([p453_thm2_subsets_is_library], by [eq_refl]).

    ** [Sets^op]

    N25, N29 (UNIVERSE).  [Sets^op] is complete and cogenerated
    unconditionally (Instance/Sets/SpecialInitial.v) and co-well-powered
    only one universe up ([Sets_CoWellPoweredAt_up]).  The cover accepts it
    ([p453_setsop_cover_up]); N25, [SAFT_cover_wp_at]:
      The term "Sets_CoWellPoweredAt_up ?X" has type "WellPoweredAt@{<1> <2>
      <2> <3> <1>} ?X" while it is expected to have type "WellPoweredAt@{<4>
      so <5> o <6>} (saft_prod@{so so o o <7>} Id[Sets@{o so}^op]
      setsop_comp@{o so} setsop_cog@{o o so} d)" (universe inconsistency:
      Cannot enforce <4> = <6> because <4> <= <8> < <6>).
    That refusal records [SAFT_cover_wp_at]'s own [w <= h], as N11's does;
    N29 is the [GAFT]-direct form, as N12 is N11's: the solution set is
    accepted ([p453_setsop_solution_set_up]), and handed to [GAFT]
      The term "saft_solution_set_at Id[Sets^op] setsop_comp
      (right_adjoint_PreservesImageLimit adj_id) setsop_cog d
      (Sets_CoWellPoweredAt_up (saft_prod Id[Sets^op] setsop_comp setsop_cog
      d))" has type "SolutionSet@{<1> so so o} Id[Sets@{o so}^op] d" while
      it is expected to have type "SolutionSet@{o so so o} Id[Sets@{o
      so}^op] d" (universe inconsistency: Cannot enforce <1> = o because o <
      <2> <= <1>).

    CONTROLS WITHOUT A NEGATIVE.  The representing object is the left
    adjoint at the singleton ([p453_repr_obj], restating
    [continuous_Set_functor_representable_obj]); the cover's index IS the
    well-powering's name for the pullback subobject ([p453_cover_index],
    restating [saft_cover_at_index]), and the cover takes [t] and [pa] apart
    in both orders ([p453_cover_t_below_pa], [p453_cover_pa_below_t], the
    paragraph on N8); at one tuple at [Id[Sets]] under
    [Untruncate] the reshaped datum holds at every object and the old one is
    refuted ([p453_separation], through [sets_id_cover_separation]); the
    monos lemma at its stated type ([p453_monos_lemma]).

    NOT PINNED HERE.  Refusals the target headers quote that no command of
    this file can restate: Adjunction/SAFT/Characterization.v's "Illegal
    application (Non-functional construction)" with the [Require] of
    Instance/Sets.v dropped (a refusal under a SHORTER import list, which
    this file must not carry), and the collapses its header and Cover.v's
    record as found and removed during the build (readbacks of drafts that
    no longer exist; what is pinned is that (a)-(c) and Cover.v's "t = pa"
    stay removed, by the controls the paragraph on N8 names, and collapse
    (d), "oc = sc" on the comma's unnamed universes, is not pinned).
    Corollaries.v's refusal of [saft_colim] at [h < jo] is its own binder's
    [jo <= h] and is not pinned; N19 is the substantive one.

    The guard block at the end names all ninety-three constants of the four
    target files (forty-seven, twenty-two, eight and sixteen, by [Print
    Module] of each and, the same counts, by the [def] and [prf] entries of
    their .glob files), so that a rename breaks this file.  The two that
    landed after this file was first written, Adjunction/SAFT/
    Characterization.v's [Complete_HasSubobjectWidePullbacks] and
    Examples.v's [subsets_inverse_image_thm2], each have a positive control
    above as well ([p453_hw_is_library] and [p453_sets_hw_library];
    [p453_thm2_subsets_is_library]).  Under the full import list with its
    one addition, [Locate] lists exactly one constant for each of the
    ninety-three names, the target's.

--------
* 作为表征的 SAFT 探针（问题 #453）

固定 Adjunction/SAFT/Characterization.v（Mac Lane §V.8 定理 2，其证明中的引理以及其后的推论，书中第 129-130 页；Awodey 注释 9.35；Riehl 定理 4.7.10，推论 4.7.13 以及结尾的两次重述）以及其三个附属文件 Adjunction/SAFT/Characterization/Cover.v、Adjunction/SAFT/Characterization/Corollaries.v 和 Adjunction/SAFT/Characterization/Examples.v 的测量边界。每个否定都重申了一个拒绝或通过#453由其侦察员、建造者或评论员测量的回读，除了N14（[SAFT_cover_wp_at]的平凡供能）和N23（N22的剥离），它们属于本文件自身；N26-N29是N9、N10、N14和N25在探针评论中的主体级和[GAFT]直接形式，编号在其他之后，以便N1-N25保持其编号；N10、N20和N21作为拒绝固定了三条最初作为回读测量的公式（[About] 打印“r = r2”、“h = cr”和“su = pa”），而N17是侦察员在其自身未注释原型上测量的拒绝，在库常量未注释的包装器上重申。阳性对照独立地重申了文件的主张。

导入列表，通过比较 [Require] 行来衡量。首先，Adjunction/SAFT/Characterization.v 的二十二行逐字且按顺序；然后是每个其他目标文件添加的行，按文件列出，但目标模块除外：Cover.v 十行，Corollaries.v 六行，Examples.v 十三行；然后是以 _CoqProject 顺序的四个目标模块。一个供应模块被添加在需要它的部分之前，并在那里命名：Instance/Sets/SpecialInitial.v 在 N25 和 N29 之前（它的 [setsop_comp] 和 [setsop_cog]；Examples.v 的头部用它自己的导入列表测量 N25 和那个文件）。所以上面每个命令的执行都严格遵循四个目标的列表。Structure/Pullback/Wide/Complete.v，其 [complete_wide_pullback] 是 N22-N24 的完整性路径，是在 N22 之前的第二次添加，在该文件的早期版本中；Adjunction/SAFT/Characterization.v 自从其 [Complete_HasSubobjectWidePullbacks] 进入以来就已经导入它，所以它现在是二十二之一，而这个添加已不存在。Adjunction/SAFT.v 在 Theory/Subobject.v 之后被导入，因此简短名称 [sub_dom] 是 [SubobjectIndex] 的字段，一个子对象的名称写作 [Subobject.sub_dom]，就像目标中写的一样。Functor/Opposite.v 是在 Construction/Opposite.v（Cover.v 的列表）之后导入的，所以 [C^op] 在未限定作用域时被读取为函子（functor）的相反；N25、N29 及其控件写入 [(Sets@{o so}^op)%category]。更短的导入列表就是导致探针无故通过的原因。

纪律。该工具以两种方式进行了检查：由于这个原因，拒绝对一个缺席的名称进行反驳，而且这个文件中每一个不是反驳的五十六个定义和示例，在这个完整文件的一份副本中被包裹在一个反驳里，都会在该命令处停止构建，并报告已接受受保护命令（副本脚本统计为五十六个中的五十六个）；每一个五十六个中的[Print Assumptions]，通过其完全限定的名称，都会报告“在全局上下文下关闭”.除了该仪器之外的每一个否定项都是 [Definition] 或 [Example]，从不出现 [Check]，因此一个未关闭的 evar 或缺失的实例无法满足它。每个否定项在该整个文件的副本中逐一去掉其反驳关键字，进行编译，并读取其错误；记录下的错误类型就是该错误的类型，并且每个否定项旁边都有正面控制；每个否定项使用的标识符，除其自身名称和仪器缺失的名称外，都被该文件的一些正面控制使用（通过对命令标识符的脚本）。在这个整个文件的另外一份副本中，每个除乐器之外的否定项后面都跟着一个绑定器乐器，使用相同的宇宙绑定器、参数和返回类型，并带有一个简单的主体（返回类型的假设，或在命令声明为无时使用 [Datatypes.unit]）：二十九个中有二十八个被接受，N8 的被以 N8 自己的文本拒绝，因此除了 N8 之外的每个否定项都被其主体拒绝。每个宇宙否定项都是顶级定义，其宇宙在自己的绑定器中声明或留给推断，从不使用 [Section]。引用是 Rocq 9.1.1 在此文件的导入列表下的内容，省略了错误的环境块；Rocq 会打印带有作用域内短名的“无法统一”括号，而一个宇宙的剥离副本按自身和一个序列号命名，写作 <1>、<2>……，在每个引用中按照首次出现的顺序重新编号。该文件也可以在 Coq 8.19.2 和 8.20.1 上编译，针对这些版本的该库的预先构建树的副本，其中探针闭包中与该树不同的每个文件，以及依赖于其中一个的每个文件，都是按照依赖顺序重新编译的；剥离后的副本也在那里进行了编译。每个文件在两者上都在相同的行和相同的字符范围内被拒绝。在 8.20.1 下，每个错误都是 Rocq 9.1.1 的错误，直到序列号为止（通过对副本运行的脚本进行比较）。在 8.19.2 条下，十七项是（该仪器、N1-N7、N11、N18、N21-N27）；N8 通过序列号命名其两个宇宙，N9 打印一个序列号，而 Rocq 9.1.1 打印 [o]，N19 的链命名为 [jo]，而 Rocq 9.1.1 命名一个生成的宇宙；N10 和 N17 打印为“无法统一”的不匹配，N12-N16、N20、N28 和 N29 打印为类型不匹配，这十项没有宇宙不一致条款。

种类。三十个反驳，可按照以反驳关键词开头的行来计算：NAME-ABSENCE（该工具）、CONVERSION（N1-N7, N18）、TYPING（N21）、BINDER（N8，其错误是由其自身绑定器引起的宇宙不一致，正如其绑定器工具所显示）以及UNIVERSE（N9-N17, N19, N20, N22-N29）：分别为一、八、一、一和十九。

标签。这些引脚承载着此文件的 N 编号；#453 的审查和制造者在其他名称下请求了它们，现记录于此，以便目标头文件可以引用任意一者：第一次审查的 [r_neg]、[r_neg2] 和 [r2_neg] 是 N1、N2 和 N3；其 [u_ctrl] 是 N8，[u_ctrl2] 是 N9；其 [h_large] 是 N22，[h_ctrl] 作为控制 [p453_hw_at_objects]；第二位制造者的 M2、M3、N1、N1w、N2c、N3、T2 和 M1b 分别是 N6、N7、N11、N13、N15、N25、N18 和 N19，其 N2 对照标题文件的存根测得为 N16；第一位制造者的 [m1_gaft_route_obj]、[m1_thm2_gaft_obj]、[m1_hw_of_complete_large] 和 [m2_sets_hw_large] 分别是 N4、N5、N22 和 N24，其回读的 [m2_r2] 是 N10 的；第二次审查的直接 [GAFT] 形式的 N1 是 N12，其 [wp_trivial] 应用是阳性对照 [p453_cover_trivial]；探针审查的 E1、E6、E2 和 E5 是 N26、N27、N28 和 N29，其 E2c 是 N28 的控制 [p453_gaft_trivial_small]，而其 E7 是控制 [p453_sets_wp_trivial]。这些标签不是常量。

** 两个左伴随，回读

N1-N3（转换）。两个左伴随由 [eq_refl] 读取回：
    [p453_left_obj] 和 [p453_thm2_left_obj] 重述了
    Adjunction/SAFT/Characterization.v 的 [SAFT_left_obj] 和
    [SAFT_thm2_left_obj]，并且 [p453_iff_left_obj] 和 [p453_iff_thm2_obj]
    通过 [SAFT_wellpowered_iff] 和 [SAFT_iff] 的后半部分读取相同的值。读取回差异化。N1，
    推论的值针对逗号的余生成器乘积本身：
      （无法统一 "fobj[projT1 (SAFT_wellpowered U comp cont G WP)] d" 和
      "snd (projT1 (cogen_prod (Comma_Complete cont comp) (comma_cogenerator
      U d G)))")。N2，对空类 [fun _ => False] 的交集，其与回读不同之处在于一个谓词：相同的头部和“snd (projT1 (Subobject.sub_dom (complete_intersection … False)))”），中间部分在此省略。N3，定理 2 的值对积而言：无法统一“fobj[projT1 (SAFT_thm2 U comp cont G HW HU)] d”和“snd (projT1 (cogen_prod (Comma_Complete cont comp) (comma_cogenerator U d G)))”。

N4、N5（转换）。通过 Adjunction/GAFT.v 的 [GAFT_from_initials] 进行同样的组装，最终到达 [Qed]：路线被形成（[p453_gaft_route]、[p453_thm2_gaft_route]），以及它们的回读，透明控件的语句用路线代替常量，都被拒绝，
      （无法统一 "fobj[projT1 (p453_gaft_route U comp cont G WP)] d" 和
      "snd (projT1 (Subobject.sub_dom (complete_intersection … True)))"）
      以及
      （无法统一 "fobj[projT1 (p453_thm2_gaft_route U comp cont G HW HU)] d" 和 "WPull (HW … `1 (k)))"），
      中间部分省略。因此，通过 Theory/Universal/Arrow.v 的 [LeftAdjointFunctorFromUniversalArrows] 进行的两个定理的透明组装，就是回读所依赖的内容。

N6, N7（转换）。Cover.v 经过 [GAFT] 的路径是 [GAFT] 在其解集处的路径（[p453_cover_is_gaft]，重述 [SAFT_cover_wp_is_GAFT]）并且与推论的左伴随在同构意义上相符（[p453_cover_iso]，[SAFT_cover_wp_iso]）；N6，在 [eq_refl] 的两个左伴随：
      （无法统一 "projT1 (SAFT_cover_wp U comp cont G WP)" 和 "projT1 (SAFT_wellpowered U comp cont G WP)"）。这两条路径索引同一个族（[p453_same_index]，重述 [comma_cogenerator_index]）；N7，在 [eq_refl] 的它们的积：
      （无法统一 "snd (projT1 (cogen_prod (Comma_Complete cont comp) (comma_cogenerator U d G)))" 和 "saft_prod U comp G d"）。

** 定理的体制

N8（绑定器；一种工具）。[p453_small] 和 [p453_small_iff] 接受推论，其同态严格位于形状之下，并且形状严格位于对象之下（[h < so, so < o, c < so, w < h]），而 [p453_thm2_small] 和 [p453_thm2_small_iff] 接受定理 2 在 [h < so, so < o, c < so, o < q, h < q]。在该体系下且不在其崩溃时，这些接受成立，这可从 [About] 读取：[p453_small] 保留 [h < so]、[so < o]、[c < so] 和 [w < h]，[p453_thm2_small] 保留 [o < q]、[h < so]、[so < o]、[c < so] 和 [h < q]，并且二者都不包含方程。N8 是 Corollary 的命令，带有 [so < h]，被整条命令拒绝：
  宇宙不一致。不能强制执行 h <= so，因为 so < h。该文本是绑定器本身的：[Complete@{so so h o}] 在其第一个槽（Structure/Complete.v）上或以下声明 [h]，无论主体如何，如 Test/ProbeSpecialInitial452.v 的 N4 记录，且 N8 的绑定器工具以相同文本被拒绝。N8 固定的只是绑定器的约束被执行。[p453_t_below_pa] 和 [p453_pa_below_t] 接受推论，以及 [WellPowered] 的 [t] 和 [PreservesImageLimit] 的辅助 [pa]，各自排列的两种顺序中都分开：“t = pa” 在 (a) 和 (b) 中崩溃，Adjunction/SAFT/Characterization.v 的头部记录被删除后保持删除状态。[p453_thm2_q_below_r] 接受定理 2，其类索引严格低于两个宽拉回宇宙，因此其崩溃 (c)、“q = r” 和 “q = rd” 也保持删除状态；[p453_cover_t_below_pa] 和 [p453_cover_pa_below_t]（与没有负号的控制一起放置）对于 Cover.v 的 [saft_cover_at] 也做同样处理，其回读曾经包含“t = pa”。

N9（宇宙）。定理 2 的类索引位于对象之下，控制 [p453_thm2_small] 与它的不同仅在 [o < q]：
  术语“HW”的类型为“HasSubobjectWidePullbacks@{o h q r k} C”，而预期类型为“HasSubobjectWidePullbacks@{o h <1> <2> <3>} C”（宇宙不一致：无法强制 <1> <= q 因为 q < o <= <1>）。该拒绝记录了 [SAFT_thm2] 自身声明的界限：其绑定器携带 [o <= q]，并且 <1> 是其 [q]。N26 是主体中的原因。[least_index]，逗号的共生成器产品的相应系列，存在于对象之上或以上（[About least_index]: [o <= lq]），并且 [SAFT_thm2_initial] 请求 [HW] 与之相交：相同的应用程序，单独使用时，在对象之上或以上的索引下被接受（[p453_least_index_at_objects], [o <= q]）以及 N26，在 [q < o]：
      术语 "least_index U d (cogen_prod (Comma_Complete cont comp) (comma_cogenerator U d G))" 的类型是 "Type@{<1>}"，而预期类型是 "Type@{q}"（宇宙不一致：无法强制执行 <1> <= q，因为 q < o <= <1>）。

N10（宇宙）。[HU] 的 C 侧广泛回拉宇宙严格声明高于 [HW]：
      术语“HU”的类型为“PreservesWidePullbacks@{o h dobj h pw q r2 rd} U”，而期望的类型为“PreservesWidePullbacks@{o h dobj h <1> q r <2>} U”（宇宙不一致：无法强制 r = r2，因为 r < r2）。控制声明了 [r <= r2]（[p453_thm2_r_le]）并被接受，方程已添加。该拒绝记录了 [SAFT_thm2] 自身的绑定器，这给了 [HW] 和 [HU] 一个 [r]。N27 是在主体处的原因：
    [SAFT_thm2_initial] 的主体以 [HU] 的插槽 [r2] 表述，除此之外
    [HW] 的 [r] 在 [r <= r2] 被接受（[p453_thm2_initial_r_le]，[About]
    打印 "r = r2"）并在 [r < r2] 被拒绝，其中
    [wide_pullback_is_pullback] 将 [HW] 的锥体交给 [HU]：
      术语 “wide_pullback_is_pullback (HW ?z0 (∃ y, ?P1 y) (λ k : ∃ y,
      ?P1 y, `1 (k)))” 的类型是 “IsWidePullback@{q r o h} …”，而它
      预期的类型是 “IsWidePullback@{q r2 o h} …”（宇宙不一致：无法强制 r = r2，因为 r < r2），
    参数已省略。第一个构建者从 [SAFT_thm2] 的一个应用中读出了“r = r2”，将两者区分开来（N10 控制的形状），以及从 [SAFT_thm2_initial] 重述的主体中得到的第一个检查折叠（N27 的形状）。

** 强大的能力，一个宇宙向上，在别针处

N11-N13（宇宙）。在没有 [Untruncate] 的 [Sets@{o so}] 中，树中的无条件良幂包含两个，均严格索引于同态 [o] 之上：Instance/Sets/WellPowered.v 的 [Sets_WellPoweredAt_up]，其索引位于其自身的上层宇宙，以及 Structure/WellPowered.v 的 [wp_trivial]，其索引 [SubObj x] 位于对象的 [so] 处或之上（[p453_sets_wp_trivial] 将其置于 [so]，[WellPoweredAt@{so so so o so}]）。Cover.v 的 [saft_cover_at] 接受每个 ([p453_cover_up] 和 [p453_sets_cover_trivial]，一个小的 [Cogenerator] 被假设，因为没有构建不带 [Untruncate] 的实例)，而 [saft_solution_set_at] 接受第一个，其索引宇宙保持自由 ([p453_solution_set_up])。N11，[SAFT_cover_wp_at]，其绑定器声明 [w <= h]：
      术语 "Sets_WellPoweredAt_up ?X" 的类型为 "WellPoweredAt@{<1> <2> <2> <3> <1>} ?X"，而期望其类型为 "WellPoweredAt@{<4> so <5> o <6>} (saft_prod@{so so o o <7>} Id[Sets@{o so}] Sets_Complete@{o so} G d)"（宇宙不一致：无法强制 <4> = <6> 因为 <4> <= <8> < <6>）。N11 记录了该常数自身声明的界限；N12 是同一步骤，Adjunction/GAFT.v 的 [GAFT] 直接应用于解集，因此该针脚是 [GAFT] 的：
      术语 “saft_solution_set_at Id[Sets] Sets_Complete Sets_Id_PreservesImageLimit G d (Sets_WellPoweredAt_up (saft_prod Id[Sets] Sets_Complete G d))” 的类型为 “SolutionSet@{<1> so so o} Id[Sets@{o so}] d”，而期望的类型为 “SolutionSet@{o so so o} Id[Sets@{o so}] d”（宇宙不一致：不能强制 <1> = o 因为 o < <2> <= <1>）。[GAFT] 的解集根据同态进行索引。N13，#451的
    [WellPowered] 本身，在应用任何定理之前（[p453_wp_up_at] 每对象控制）：
      术语“Sets_WellPoweredAt_up x”的类型为“WellPoweredAt@{<1> <2> <2> o <1>} x”，而期望的类型为“WellPoweredAt@{<3> so <4> o <5>} x”（宇宙不一致：无法强制 <3> = <5> 因为 <3> <= <6> < <5>）。在 [Untruncate] 下，小规模良定符合要求，两条路线都被接受（[p453_sets_id], [p453_sets_id_cover]）。

N14, N28（宇宙）。覆盖不需要良冗余性：在任意完备的、连续的、共生的 [C] 上，结构/WellPowered.v 的 [wp_trivial]，由 [SubObj] 自身索引，提供 [saft_cover_at] 的数据（[p453_cover_trivial]，一个正控制，该数据在 [wp_trivial] 自身的界限上，其索引为 [w]，与 [o <= w] 及 [h <= w]），因此覆盖由完备性、保持性和共生族得出。[SAFT_cover_wp_at] 当对象适合于 homs ([o <= h], [p453_cover_wp_trivial_small]) 时会采用 [wp_trivial]，N14 在 [h < o] 时也是如此：
  术语 "wp_trivial (saft_prod U comp G d)" 的类型是
  "WellPoweredAt@{<1> o <2> h <3>} (saft_prod@{o dobj h h <4>} U comp G d)"，而期望的类型是 "WellPoweredAt@{<5> o <6> h <7>} (saft_prod@{o dobj h h <8>} U comp G d)" (宇宙不一致：无法强制 <1> = <5> 因为 <5> <= <9> < o <= <1>)。该拒绝记录了 [SAFT_cover_wp_at] 自己声明的 [w <= h]，就像 N11 的记录一样。N28 与直接应用 [GAFT] 于解集的步骤相同，因此针脚是 [GAFT] 的：在 [o <= h]（[p453_gaft_trivial_small]）处被接受，并在 [h < o] 处。 术语“saft_solution_set_at U comp cont G d (wp_trivial (saft_prod U comp G d))”的类型是“SolutionSet@{<1> dobj o h} U d”，而预期类型是“SolutionSet@{h dobj o h} U d”（宇宙不一致：无法强制 <1> = h 因为 h < o <= <2> <= <1>）。[wp_trivial] 的索引在对象处或之上，而 [GAFT] 的解集索引在 Hom 上：正是在 [GAFT] 的针脚上，良有幂性产生了影响。

** [Sets] 的大型联合发电系列

N15, N16（宇宙）。Instance/Sets/Cogenerator.v 的 [Sets_Cogenerator_large]，由所有对象索引，是 [Sets]（[p453_large_cog]）的 [Cogenerator]，并且推论是针对其索引宇宙形状的完备性数据项（[p453_large_cog_abstract]，该数据项是一个假设变量）。N15，通过 Cover.v 的 [SAFT_cover_wp]，其 [Cogenerator@{h o h}] 索引家族在所提供的任何完整性数据处：
      术语 “Sets_Cogenerator_large” 的类型为 “Cogenerator@{<1> <2> <3>} Sets@{<3> <2>}”，而期望的类型为 “Cogenerator@{o so o} Sets@{o so}”（宇宙不一致：无法强制 <3> = o，因为 <3> < o）。以及 N16，通过 [SAFT_wellpowered]，其 [Cogenerator@{c o h}] 携带 [c <= so]，在 [Sets_Complete]，其形状宇宙是同类：
  术语 "Sets_Cogenerator_large" 的类型是 "Cogenerator@{<1> <2> <3>} Sets@{<3> <2>}"，而期望的类型是 "Cogenerator@{<4> so o} Sets@{o so}"（宇宙不一致：无法强制 <3> = o，因为 <3> < <1> <= o）。

** 这些活页夹是承重的

N17（宇宙）。[p453_unannotated] 在没有宇宙注释的情况下包装 [SAFT_wellpowered]；然后最小化将良好供电的索引放在 homs 上（[About] 以索引宇宙和 hom 宇宙相等的方式读取其 [WellPowered]，在一个包含四个目标导入列表的临时文件中测量）。库常量采用 Examples.v 的索引 [Set]，严格低于 homs（[p453_indiscrete_set_index]，重述 [indiscrete_saft]）；封装器在 homs 处采用索引（[p453_unannotated_hom_index]）和 N17，即在 [Set] 处的索引：
“Indiscrete_WellPowered 类型” 的类型为 "WellPowered@{o j Set o <1>} (Indiscrete@{o j j} Type@{j})"，而预期的类型为 "WellPowered@{o j j <2> <3>} (Indiscrete@{o j j} Type@{j})"（宇宙不一致：无法强制 Set = j）。一个侦察兵通过 [GAFT] 在其未加注释的原型上测量了这种拒绝；这里的封装是一个不同的常量，但具有相同的类型和相同的原因。

** 封面的提升及其推论

N18（转换）。[saft_lift] 的锥体将其 [Compose] 宇宙取自 [cont]：在 [pa] 的主体被接受（[p453_lift_at_pa]），而 N18，其宇宙 [pc] 严格高于 [pa]，则被转换拒绝，这两种类型仅在该宇宙中不同：
  （无法统一 "Functor.Compose_obligation_1@{dobj so o pc h} Roof@{so h}^op C D U (ASpan@{so o <1> h} (saft_kappa@{o dobj h so dp cp} U comp G d c h) (cogen_canonical@{cp so h so o} comp G c))^op" 和 
  "Functor.Compose_obligation_1@{dobj so o pa h} Roof@{so h}^op C D U (ASpan@{so o <1> h} (…) (…))^op"），第二个项的参数已省略，与第一个项相同。

N19（宇宙）。Riehl 4.7.13 的附带条件：在 [@Diagonal C J] 处的推论在同态 ([p453_diag_small]) 的形状或以下被接受，而仅在它们之上采用对角线 ([p453_diag_alone])；N19，那里的推论：
    术语“Diagonal J”的类型为“@Functor@{o h h <1> <2> <2>} C (@Fun@{jo h o h <1> <2> <3>} J C)”，而它预计具有类型“@Functor@{<4> <5> <5> <6> <5> <5>} ?C ?D”（宇宙不一致：无法强制 <2> = h，因为 h < <7> <= <2>）。
[Fun J C] 的同态位于 [J] 的对象之上或之上，该定理与 [D] 的同态宇宙共享 [C] 的同态宇宙。

N20（宇宙）。[saft_cocomplete] 的 colimit-数据宇宙是由 #353 的 [Diagonal_left_adjoint_HasColimits] 继承的 homs：在它们之上（或同级别，[p453_cocomplete_cr_le]）声明时，它是被接受的，方程已添加，而 N20 则严格在其之上：
  术语“Diagonal_left_adjoint_HasColimits (projT2 (saft_colim C comp G WP J : ∃ L : ([J, C]) ⟶ C, L ⊣ Diagonal J)) F”的类型是“Colimit@{h jo h o} F”，而期望的类型是“Colimit@{cr jo h o} F”（宇宙不一致：无法强制 h = cr，因为 h < cr）。

N21（打字）。[continuous_Set_functor_representable_iff] 携带 [su = pa] ([About]), [su] [Sets@{h su}] 的对象，而 [continuous_Set_functor_representable] 不携带：后者在 [pa < su] ([p453_repr_pa_below_su]) 被接受，双条件在 [pa <= su] ([p453_repr_iff_pa_le_su])，而 N21，在 [pa < su] 的双条件被拒绝，且没有括号，这两种类型仅在 [PreservesImageLimit] 的第七个宇宙中有所不同：
      术语 "continuous_Set_functor_representable_iff K comp G WP" 的类型是 "Representable@{<1> <2> su o h} K ↔ PreservesImageLimit@{o h su h <3> so su so}"，而预期类型为 "Representable@{ra rt su o h} K ↔ PreservesImageLimit@{o h su h pl so pa so}"。剥离到其捐赠者，Adjunction/Representability/Sets.v 的 [preserves_image_of_representable]，拒绝是通过锥体的 [Compose] 宇宙在 [su] 对 [pa] 的转换实现的（在包含四个目标导入列表的临时文件中进行测量）；所以这与 N18 的识别相同，并且 N21 并未报告为宇宙不一致。

** 从完备性广泛回拉子对象

N22-N24（宇宙）。完备性提供了  
    Adjunction/SAFT/Characterization.v 的 [HasSubobjectWidePullbacks]，当  
    对象适合形状时：在形状上的索引（[p453_hw_at_shapes]）和在对象上的索引（[p453_hw_at_objects]），两者都在 [o <= so]。第二项是该文件在对象索引处的 [Complete_HasSubobjectWidePullbacks]（[p453_hw_is_library]，由 [eq_refl]）；N22 和 N23 重述主体而不是应用常数，其绑定器声明其索引在形状处或以下（[q <= so]），因此拒绝是主体的而不是该声明的。N22，在 [so < o] 的第二个，在 index 处拒绝时尝试实例化一个 evar：
      术语 "i" 的类型是 "?J"，而期望的类型是 "I"
      （无法找到 "?J" 的类型良好的实例化：无法确保 "Type@{o}" 是 "Type@{<1>}" 的子类型）。N23 对其进行剥离，明确给出家族的索引（control [p453_hw_index_ok] 在 [o <= so]）：
      术语 "I" 的类型是 "Type@{o}"，而期望的类型是 "Type@{<1>}" （宇宙不一致：无法强制 o <= <1> 因为 <1> <= <2> < o）。N24，在 [Sets@{o so}]，[Sets_Complete] 在 homs 的形状：在 homs 的索引被接受（[p453_sets_hw_small]，以及那里的库常量 [p453_sets_hw_library]），而在对象上被拒绝，
术语“Subobject.sub_mono (S i)”的类型为“Subobject.sub_dom (S i) ~{ Sets }~> x”，而预期的类型是“?A i ~{ Sets }~> ?z”（宇宙不一致：无法强制 o = <1> 因为 o < so <= <2> <= <1>）。在完整性路径适用的情况下，定理2的每个前提都是有内容的：[p453_thm2_subsets]，在薄的 [Subsets Y] 上，用 [U := InverseImage f]，两个保持性前提都是直接从 [image_preimage_adjunction f] 本身读取（所以结论是已知的）。Adjunction/SAFT/Characterization/Examples.v 的 [subsets_inverse_image_thm2] 是那个组装 ([p453_thm2_subsets_is_library]，由 [eq_refl])。

** [Sets^op]

N25, N29 (宇宙)。[Sets^op] 已完成并且无条件地协同生成（Instance/Sets/SpecialInitial.v），并且在上一个宇宙中协同良好（[Sets_CoWellPoweredAt_up]）。覆盖接受它（[p453_setsop_cover_up]）；N25, [SAFT_cover_wp_at]：
      术语 "Sets_CoWellPoweredAt_up ?X" 的类型是 "WellPoweredAt@{<1> <2> <2> <3> <1>} ?X"，而预期类型是 "WellPoweredAt@{<4> so <5> o <6>} (saft_prod@{so so o o <7>} Id[Sets@{o so}^op] setsop_comp@{o so} setsop_cog@{o o so} d)"（宇宙不一致：无法强制 <4> = <6> 因为 <4> <= <8> < <6>）。该拒绝记录了 [SAFT_cover_wp_at] 自身的 [w <= h]，如同 N11 的记录；
N29 是 [GAFT]-直接形式，就像 N12 是 N11 的形式一样：解集被接受（[p453_setsop_solution_set_up]），并交给 [GAFT]。
术语“saft_solution_set_at Id[Sets^op] setsop_comp (right_adjoint_PreservesImageLimit adj_id) setsop_cog d (Sets_CoWellPoweredAt_up (saft_prod Id[Sets^op] setsop_comp setsop_cog d))”的类型为“SolutionSet@{<1> so so o} Id[Sets@{o so}^op] d”，而预期类型为“SolutionSet@{o so so o} Id[Sets@{o so}^op] d”（宇宙不一致：无法强制 <1> = o，因为 o < <2> <= <1>）。

没有负面的控制。表示的对象是在单元([p453_repr_obj]，重述[continuous_Set_functor_representable_obj])处的左伴随；覆盖的指标是拉回子对象的名称([p453_cover_index]，重述[saft_cover_at_index])，而且覆盖在两个顺序中分别拆开[t]和[pa]([p453_cover_t_below_pa]，[p453_cover_pa_below_t]，关于N8的段落)；在[Id[Sets]处的一个元组下，在[Untruncate]重新形状的数据在每个对象处都成立，而旧的数据被反驳([p453_separation]，通过[sets_id_cover_separation])；其所述类型处的单态引理([p453_monos_lemma])。

这里未固定。拒绝的目标头引用表示，没有任何命令可以重新声明此文件：Adjunction/SAFT/Characterization.v 的“非法应用（非功能性构造）”，以及 Instance/Sets.v 的 [Require] 被删除（在较短的导入列表下的拒绝，而此文件不得携带该列表），并且在构建过程中其头文件和 Cover.v 的记录被发现并删除（对已不存在的草稿的回读；固定的是 (a)-(c) 和 Cover.v 的“t = pa”保持被删除，由 N8 段落中的控制命名，而合并 (d)，“oc = sc” 在逗号的未命名宇宙上未被固定）。Corollaries.v 在 [h < jo] 拒绝 [saft_colim] 是它自己的绑定器的 [jo <= h]，并且没有被固定；N19 才是实质性的那个。

在末尾的守卫块中，列出了四个目标文件的全部九十三个常量（分别是四十七、二十二、八和十六，通过各自的 [Print Module] 输出，且在它们的 .glob 文件中的 [def] 和 [prf] 条目中也有相同的数量），因此重命名会破坏此文件。在这个文件最初写入之后出现的两个文件，Adjunction/SAFT/Characterization.v 的 [Complete_HasSubobjectWidePullbacks] 和 Examples.v 的 [subsets_inverse_image_thm2]，每个也都有上方的正控制（[p453_hw_is_library] 和 [p453_sets_hw_library]；[p453_thm2_subsets_is_library]）。在完整的导入列表及其一个附加项下，[Locate] 为目标的九十三个名称中的每一个列出了恰好一个常量。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.Pullback.Wide.Complete.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.SAFT.InitialObject.
Require Import Category.Adjunction.SpanningArrow.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Span.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Roof.
Require Import Category.Adjunction.GAFT.
Require Import Category.Functor.Representable.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Fun.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Functor.Hom.Limit.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Instance.Adjoints.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Sets.WellPowered.
Require Import Category.Instance.Sets.Cogenerator.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Powerset.WellPowered.
Require Import Category.Adjunction.GAFT.Sets.
Require Import Category.Adjunction.SAFT.Sets.
Require Import Category.Adjunction.SAFT.WellPowered.
Require Import Category.Adjunction.SAFT.InitialObject.Examples.
Require Import Category.Adjunction.SAFT.Characterization.
Require Import Category.Adjunction.SAFT.Characterization.Cover.
Require Import Category.Adjunction.SAFT.Characterization.Corollaries.
Require Import Category.Adjunction.SAFT.Characterization.Examples.

Generalizable All Variables.

(** ** Instrument: the refutation keyword is live / ** 工具：反驳关键词是实时的 *)

Fail Check probe453_absent_name.

(** ** N1-N3 (CONVERSION): the two left adjoints read back / ** N1-N3（转换）：两个左伴随返回读取 *)

(* CONTROL: [SAFT_left_obj], restated. / 控制：[SAFT_left_obj]，重申。 *)
Example p453_left_obj@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) (d : D) :
  fobj[`1 (SAFT_wellpowered U comp cont G WP)] d
    = snd (`1 (Subobject.sub_dom
        (complete_intersection (Comma_Complete cont comp)
           (wp_class_family
              (comma_WellPoweredAt U d (complete_pullbacks comp)
                 (cogen_prod (Comma_Complete cont comp)
                    (comma_cogenerator U d G))
                 (WP _))
              (fun _ => True))))) :=
  eq_refl.

(*
CONTROL: the same through the backward half of the Corollary's
   biconditional.

--------
控制：贯穿推论的后半部分的双条件相同。
*)
Example p453_iff_left_obj@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) (d : D) :
  fobj[`1 (snd (SAFT_wellpowered_iff U comp G WP) cont)] d
    = snd (`1 (Subobject.sub_dom
        (complete_intersection (Comma_Complete cont comp)
           (wp_class_family
              (comma_WellPoweredAt U d (complete_pullbacks comp)
                 (cogen_prod (Comma_Complete cont comp)
                    (comma_cogenerator U d G))
                 (WP _))
              (fun _ => True))))) :=
  eq_refl.

Fail Example p453_n1_obj_is_product@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) (d : D) :
  fobj[`1 (SAFT_wellpowered U comp cont G WP)] d
    = snd (`1 (cogen_prod (Comma_Complete cont comp)
                 (comma_cogenerator U d G))) :=
  eq_refl.

Fail Example p453_n2_obj_empty_class@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) (d : D) :
  fobj[`1 (SAFT_wellpowered U comp cont G WP)] d
    = snd (`1 (Subobject.sub_dom
        (complete_intersection (Comma_Complete cont comp)
           (wp_class_family
              (comma_WellPoweredAt U d (complete_pullbacks comp)
                 (cogen_prod (Comma_Complete cont comp)
                    (comma_cogenerator U d G))
                 (WP _))
              (fun _ => False))))) :=
  eq_refl.

(* CONTROL: [SAFT_thm2_left_obj], restated. / 控制：[SAFT_thm2_left_obj]，重申。 *)
Example p453_thm2_left_obj@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) (d : D) :
  fobj[`1 (SAFT_thm2 U comp cont G HW HU)] d
    = WPull (HW (snd (`1 (cogen_prod (Comma_Complete cont comp)
                              (comma_cogenerator U d G))))
                (least_index U d
                   (cogen_prod (Comma_Complete cont comp)
                      (comma_cogenerator U d G)))
                (fun k => `1 k)) :=
  eq_refl.

(*
CONTROL: the same through the backward half of Theorem 2's
   biconditional.

--------
控制：贯穿定理2的双条件命题的后半部分相同。
*)
Example p453_iff_thm2_obj@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) (d : D) :
  fobj[`1 (snd (SAFT_iff U comp G HW) (cont, HU))] d
    = WPull (HW (snd (`1 (cogen_prod (Comma_Complete cont comp)
                              (comma_cogenerator U d G))))
                (least_index U d
                   (cogen_prod (Comma_Complete cont comp)
                      (comma_cogenerator U d G)))
                (fun k => `1 k)) :=
  eq_refl.

Fail Example p453_n3_thm2_obj_is_product@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) (d : D) :
  fobj[`1 (SAFT_thm2 U comp cont G HW HU)] d
    = snd (`1 (cogen_prod (Comma_Complete cont comp)
                 (comma_cogenerator U d G))) :=
  eq_refl.

(** ** N4, N5 (CONVERSION): the same readbacks through [GAFT_from_initials] / ** N4，N5（转换）：通过 [GAFT_from_initials] 的相同回读 *)

(*
CONTROL: the route through Adjunction/GAFT.v's [Qed] assembly is
   formed, for the Corollary ...

--------
控制：通过 Adjunction/GAFT.v 的 [Qed] 装配形成的路线是，为了推论 ...
*)
Definition p453_gaft_route@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  { F : D ⟶ C & F ⊣ U } :=
  GAFT_from_initials U (SAFT_comma_initial U comp cont G WP).

(* ... and for Theorem 2. / ... 以及定理2。 *)
Definition p453_thm2_gaft_route@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) :
  { F : D ⟶ C & F ⊣ U } :=
  GAFT_from_initials U (SAFT_thm2_initial U comp cont G HW HU).

Fail Example p453_n4_gaft_route_obj@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) (d : D) :
  fobj[`1 (p453_gaft_route U comp cont G WP)] d
    = snd (`1 (Subobject.sub_dom
        (complete_intersection (Comma_Complete cont comp)
           (wp_class_family
              (comma_WellPoweredAt U d (complete_pullbacks comp)
                 (cogen_prod (Comma_Complete cont comp)
                    (comma_cogenerator U d G))
                 (WP _))
              (fun _ => True))))) :=
  eq_refl.

Fail Example p453_n5_thm2_gaft_route_obj@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) (d : D) :
  fobj[`1 (p453_thm2_gaft_route U comp cont G HW HU)] d
    = WPull (HW (snd (`1 (cogen_prod (Comma_Complete cont comp)
                              (comma_cogenerator U d G))))
                (least_index U d
                   (cogen_prod (Comma_Complete cont comp)
                      (comma_cogenerator U d G)))
                (fun k => `1 k)) :=
  eq_refl.

(** ** N6, N7 (CONVERSION): the cover's route and the comma's product / ** N6、N7（转换）：封面的路线和逗号的产品 *)

(* CONTROL: [SAFT_cover_wp_is_GAFT], restated. / 控制：[SAFT_cover_wp_is_GAFT]，重申。 *)
Example p453_cover_is_gaft@{o dobj h dp cp w s t pl pa +|
    h < dp, h < cp, w <= h +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) (WP : WellPowered@{o h w s t} C) :
  SAFT_cover_wp@{o dobj h dp cp w s t pl pa _ _ _} U comp cont G WP
    = GAFT U comp cont
        (fun d => saft_solution_set_at@{o dobj h h dp cp w s t pl pa h _ _ _}
                    U comp cont G d
                    (WP (saft_prod@{o dobj h h dp} U comp G d))) :=
  eq_refl.

(* CONTROL: the two left adjoints are isomorphic ([SAFT_cover_wp_iso]). / 控制：两个左伴随是同构的 ([SAFT_cover_wp_iso])。 *)
Definition p453_cover_iso@{o dobj h dp cp w s t pl pa +|
    h < dp, h < cp, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) (WP : WellPowered@{o h w s t} C) :
  projT1 (SAFT_cover_wp@{o dobj h dp cp w s t pl pa _ _ _} U comp cont G WP)
    ≈ projT1 (SAFT_wellpowered U comp cont G WP) :=
  SAFT_cover_wp_iso U comp cont G WP.

Fail Example p453_n6_routes_convertible@{o dobj h dp cp w s t pl pa +|
    h < dp, h < cp, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) (WP : WellPowered@{o h w s t} C) :
  projT1 (SAFT_cover_wp@{o dobj h dp cp w s t pl pa _ _ _} U comp cont G WP)
    = projT1 (SAFT_wellpowered U comp cont G WP) :=
  eq_refl.

(*
CONTROL: [comma_cogenerator_index], restated: the two routes index the
   same family.

--------
控制：[comma_cogenerator_index]，重述：这两条路径索引同一个家族。
*)
Example p453_same_index@{o dobj h so +| h <= so +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D)
  (G : Cogenerator@{so o h} C) :
  cog_index (comma_cogenerator U d G) = saft_index U G d :=
  eq_refl.

Fail Example p453_n7_same_product@{o dobj h so dp pk pa +|
    h <= so, h < dp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{so o h} C) :
  snd (`1 (cogen_prod (Comma_Complete cont comp) (comma_cogenerator U d G)))
    = saft_prod@{o dobj h so dp} U comp G d :=
  eq_refl.

(** ** N8-N10, N26, N27 (BINDER, UNIVERSE): the regime of the theorems / ** N8-N10, N26, N27（BINDER, UNIVERSE）：定理的体制 *)

(*
CONTROL: the Corollary with the homs strictly below the shapes and the
   shapes strictly below the objects.

--------
控制：推论与同态严格地位于形状之下，而形状严格地位于对象之下。
*)
Definition p453_small@{o dobj h so c w s t pk pa +|
    h < so, so < o, c < so, w < h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_wellpowered U comp cont G WP.

(* CONTROL: its biconditional at the same universes. / 控制：它在相同的宇宙中是双条件的。 *)
Definition p453_small_iff@{o dobj h so c w s t pk pa +|
    h < so, so < o, c < so, w < h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  { F : D ⟶ C & F ⊣ U }
    ↔ @PreservesImageLimit@{o h dobj h pk so pa so} C D U :=
  SAFT_wellpowered_iff U comp G WP.

(*
CONTROL: [WellPowered]'s [t] and [PreservesImageLimit]'s auxiliary
   [pa] apart, in both orders.

--------
控制：将[WellPowered]的[t]和[PreservesImageLimit]的辅助[pa]分开，两种顺序都可以。
*)
Definition p453_t_below_pa@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, t < pa +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_wellpowered U comp cont G WP.

Definition p453_pa_below_t@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, pa < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_wellpowered U comp cont G WP.

(*
INSTRUMENT: the binder's constraints are enforced.  [Complete@{so so h
   o}] declares [h] at or below its first slot, so this is refused
   whatever the body.

--------
工具：绑定器的约束被强制执行。[Complete@{so so h o}] 在或低于其第一个槽位声明 [h]，因此无论主体如何，这都被拒绝。
*)
Fail Definition p453_n8_shapes_below_homs@{o dobj h so c w s t pk pa +|
    so < h, c < so, w < h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_wellpowered U comp cont G WP.

(*
CONTROL: Theorem 2 at the same regime, the class index strictly above
   the objects.

--------
控制：同一条件下的定理2，类别索引严格高于对象。
*)
Definition p453_thm2_small@{o dobj h so c pk pa q r rd pw k +|
    h < so, so < o, c < so, o < q, h < q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_thm2 U comp cont G HW HU.

(* CONTROL: its biconditional at the same universes. / 控制：它在相同的宇宙中是双条件的。 *)
Definition p453_thm2_small_iff@{o dobj h so c pk pa q r rd pw k +|
    h < so, so < o, c < so, o < q, h < q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C) :
  { F : D ⟶ C & F ⊣ U }
    ↔ (@PreservesImageLimit@{o h dobj h pk so pa so} C D U
       * PreservesWidePullbacks@{o h dobj h pw q r rd} U) :=
  SAFT_iff U comp G HW.

(*
CONTROL: Theorem 2 with the class index strictly below both
   wide-pullback universes, [q < r] and [q < rd].

--------
控制：定理2，其类别指数严格低于两个广拉回宇宙，[q < r] 和 [q < rd]。
*)
Definition p453_thm2_q_below_r@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q, q < r, q < rd +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_thm2 U comp cont G HW HU.

Fail Definition p453_n9_class_index_small@{o dobj h so c pk pa q r rd pw k +|
    h < so, so < o, c < so, q < o, h < q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_thm2 U comp cont G HW HU.

(*
CONTROL: [HU]'s C-side wide-pullback universe [r2] declared at or
   above [HW]'s [r].

--------
控制：[HU] 的 C 面宽回撤宇宙 [r2] 在 [HW] 的 [r] 处或以上宣布。
*)
Definition p453_thm2_r_le@{o dobj h so c pk pa q r r2 rd pw k +|
    h <= so, c <= so, o <= q, h <= q, r <= r2 +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r2 rd} U) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_thm2 U comp cont G HW HU.

Fail Definition p453_n10_thm2_r_apart@{o dobj h so c pk pa q r r2 rd pw k +|
    h <= so, c <= so, o <= q, h <= q, r < r2 +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r2 rd} U) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_thm2 U comp cont G HW HU.

(*
CONTROL: N26's term, [HW] applied to the corresponding family
   [least_index] of the comma's cogenerator product, the class index at or
   above the objects.

--------
控制：N26 的术语，[HW] 应用于相应的家族 [least_index] 的逗号协同生成器产品，对象之上的类索引或更高。
*)
Definition p453_least_index_at_objects@{o dobj h so c pk pa q r k +|
    h < so, so < o, c < so, o <= q, h < q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C) (d : D) :=
  HW (snd (`1 (cogen_prod (Comma_Complete cont comp)
                 (comma_cogenerator U d G))))
     (least_index U d (cogen_prod (Comma_Complete cont comp)
                         (comma_cogenerator U d G)))
     (fun k => `1 k).

Fail Definition p453_n26_least_index_small@{o dobj h so c pk pa q r k +|
    h < so, so < o, c < so, q < o, h < q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C) (d : D) :=
  HW (snd (`1 (cogen_prod (Comma_Complete cont comp)
                 (comma_cogenerator U d G))))
     (least_index U d (cogen_prod (Comma_Complete cont comp)
                         (comma_cogenerator U d G)))
     (fun k => `1 k).

(*
CONTROL: [SAFT_thm2_initial]'s body, [HU]'s C-side wide-pullback
   universe [r2] declared at or above [HW]'s [r].

--------
控制：[SAFT_thm2_initial] 的身体，[HU] 的 C 面宽回拉宇宙 [r2] 在 [HW] 的 [r] 处或以上被宣布。
*)
Definition p453_thm2_initial_r_le@{o dobj h so c pk pa q r r2 rd pw k +|
    h <= so, c <= so, o <= q, h <= q, r <= r2 +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r2 rd} U) (d : D) :
  @Initial (=(d) ↓ U) :=
  special_initial_object_least (Comma_Complete cont comp)
    (comma_cogenerator U d G)
    (@least_sub C D U d
       (cogen_prod (Comma_Complete cont comp) (comma_cogenerator U d G))
       (HW _ _ (fun k => `1 k))
       (HU _ _ _ _ (fun k => Subobject.sub_is_monic (`1 k)) _ _
          (wide_pullback_is_pullback (HW _ _ (fun k => `1 k)))))
    (least_le (complete_pullbacks comp)
       (HU _ _ _ _ (fun k => Subobject.sub_is_monic (`1 k)) _ _
          (wide_pullback_is_pullback (HW _ _ (fun k => `1 k))))).

Fail Definition p453_n27_initial_r_apart@{o dobj h so c pk pa q r r2 rd pw k +|
    h <= so, c <= so, o <= q, h <= q, r < r2 +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r2 rd} U) (d : D) :
  @Initial (=(d) ↓ U) :=
  special_initial_object_least (Comma_Complete cont comp)
    (comma_cogenerator U d G)
    (@least_sub C D U d
       (cogen_prod (Comma_Complete cont comp) (comma_cogenerator U d G))
       (HW _ _ (fun k => `1 k))
       (HU _ _ _ _ (fun k => Subobject.sub_is_monic (`1 k)) _ _
          (wide_pullback_is_pullback (HW _ _ (fun k => `1 k)))))
    (least_le (complete_pullbacks comp)
       (HU _ _ _ _ (fun k => Subobject.sub_is_monic (`1 k)) _ _
          (wide_pullback_is_pullback (HW _ _ (fun k => `1 k))))).

(** ** N11-N14, N28 (UNIVERSE): well-poweredness one universe up, at the pin / ** N11-N14, N28（宇宙）：在针处，一个宇宙的强大 *)

(*
CONTROL: at [Sets] with the unconditional well-powering one universe up
   and a small cogenerating family taken as a hypothesis, the cover is
   accepted ...

--------
控制：在 [Sets] 使用无条件的全能宇宙提升以及作为假设的小型共生家庭，覆盖被接受……
*)
Definition p453_cover_up@{o so +| o < so +} (d : Sets@{o so})
  (G : Cogenerator@{o so o} Sets@{o so}) :=
  saft_cover_at (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit G d
    (Sets_WellPoweredAt_up _).

(*
... and so is the solution set built from it, its index universe left
   free.

--------
... 因此由它构建的解集也是如此，其索引集合保持自由。
*)
Definition p453_solution_set_up@{o so +| o < so +} (d : Sets@{o so})
  (G : Cogenerator@{o so o} Sets@{o so}) :=
  saft_solution_set_at (@Id Sets@{o so}) Sets_Complete
    Sets_Id_PreservesImageLimit G d (Sets_WellPoweredAt_up _).

(*
CONTROL: the other unconditional well-powering of [Sets@{o so}],
   Structure/WellPowered.v's [wp_trivial], indexed at the objects' [so],
   strictly above the homs [o] ...

--------
控制：[Sets@{o so}]的另一种无条件强力，Structure/WellPowered.v的[wp_trivial]，在对象的[so]处索引，严格高于homs [o] ...
*)
Definition p453_sets_wp_trivial@{o so +| o < so +} (d : Sets@{o so}) :
  WellPoweredAt@{so so so o so} d :=
  wp_trivial d.

(* ... and the cover accepts it too. / ... 盖子也可以接受它。 *)
Definition p453_sets_cover_trivial@{o so +| o < so +} (d : Sets@{o so})
  (G : Cogenerator@{o so o} Sets@{o so}) :=
  saft_cover_at (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit G d
    (wp_trivial _).

Fail Definition p453_n11_cover_wp_at_up@{o so +| o < so +}
  (G : Cogenerator@{o so o} Sets@{o so}) :
  { F : Sets@{o so} ⟶ Sets@{o so} & F ⊣ Id } :=
  SAFT_cover_wp_at (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit G
    (fun d => Sets_WellPoweredAt_up _).

Fail Definition p453_n12_gaft_at_up@{o so +| o < so +}
  (G : Cogenerator@{o so o} Sets@{o so}) :
  { F : Sets@{o so} ⟶ Sets@{o so} & F ⊣ Id } :=
  GAFT (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit
    (fun d => saft_solution_set_at (@Id Sets@{o so}) Sets_Complete
                Sets_Id_PreservesImageLimit G d (Sets_WellPoweredAt_up _)).

(* CONTROL: the well-powering one universe up, per object. / 控制：每个对象的单一宇宙能量提升者。 *)
Definition p453_wp_up_at@{o so +| o < so +} (x : Sets@{o so}) :=
  Sets_WellPoweredAt_up x.

Fail Definition p453_n13_wp_up@{o so +| o < so +} : WellPowered Sets@{o so} :=
  fun x => Sets_WellPoweredAt_up x.

(*
CONTROL: under [Untruncate] the small well-powering meets the pin, and
   both routes are accepted ([sets_id_saft], [sets_id_saft_cover]).

--------
控制：在 [Untruncate] 下，小型供电与引脚相接，并且两条线路都被接受（[sets_id_saft]，[sets_id_saft_cover]）。
*)
Definition p453_sets_id@{o so +| Set < o, o < so +} (Un : Untruncate@{o}) :
  { F : Sets@{o so} ⟶ Sets@{o so} & F ⊣ @Id Sets@{o so} } :=
  SAFT_wellpowered (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit
    (Sets_Cogenerator_untruncate Un) (Sets_WellPowered_untruncate Un).

Definition p453_sets_id_cover@{o so +| Set < o, o < so +}
  (Un : Untruncate@{o}) :
  { F : Sets@{o so} ⟶ Sets@{o so} & F ⊣ @Id Sets@{o so} } :=
  SAFT_cover_wp (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit
    (Sets_Cogenerator_untruncate Un) (Sets_WellPowered_untruncate Un).

(*
POSITIVE CONTROL: the cover needs no well-poweredness at all.  At an
   arbitrary complete, continuous, cogenerated [C], Structure/
   WellPowered.v's [wp_trivial], indexed by [SubObj] itself, supplies the
   datum, at [w s t] with [wp_trivial]'s own bounds: its index [w] at or
   above the objects.

--------
阳性对照：覆盖根本不需要良好幂。 在任意完备、连续、共生成的 [C] 上，Structure/WellPowered.v 的 [wp_trivial]，由 [SubObj] 本身索引，提供数据，在 [w s t] 上使用 [wp_trivial] 自身的界限：其索引 [w] 位于或高于对象。
*)
Definition p453_cover_trivial@{o dobj h so dp cp w s t pl pa +|
    h <= so, h < dp, h < cp, o <= w, h <= w, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D) :=
  saft_cover_at U comp cont G d
    (wp_trivial@{o h w s t} (saft_prod U comp G d)).

(*
CONTROL: [GAFT]'s pin takes [wp_trivial] when the objects fit in the
   homs.

--------
控制：当物体适合在孔中时，[GAFT] 的针脚会接收 [wp_trivial]。
*)
Definition p453_cover_wp_trivial_small@{o dobj h dp cp s t pl pa +|
    o <= h, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_cover_wp_at U comp cont G (fun d => wp_trivial (saft_prod U comp G d)).

Fail Definition p453_n14_cover_wp_trivial_large@{o dobj h dp cp s t pl pa +|
    h < o, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_cover_wp_at U comp cont G (fun d => wp_trivial (saft_prod U comp G d)).

(*
CONTROL: N28's term, [GAFT] applied directly to the solution sets built
   from [wp_trivial], when the objects fit in the homs.

--------
控制：当对象适合同态时，N28 的术语 [GAFT] 直接应用于从 [wp_trivial] 构建的解集。
*)
Definition p453_gaft_trivial_small@{o dobj h dp cp pl pa +|
    o <= h, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) :
  { F : D ⟶ C & F ⊣ U } :=
  GAFT U comp cont
    (fun d => saft_solution_set_at U comp cont G d
                (wp_trivial (saft_prod U comp G d))).

Fail Definition p453_n28_gaft_trivial_large@{o dobj h dp cp pl pa +|
    h < o, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) :
  { F : D ⟶ C & F ⊣ U } :=
  GAFT U comp cont
    (fun d => saft_solution_set_at U comp cont G d
                (wp_trivial (saft_prod U comp G d))).

(** ** N15, N16 (UNIVERSE): the large cogenerating family of [Sets] / ** N15，N16（宇宙）：[Sets]的大型联合发电家族 *)

(* CONTROL: the family itself. / 控制：家庭本身。 *)
Definition p453_large_cog@{c o so +| o < so, o < c +} :
  Cogenerator@{c so o} Sets@{o so} :=
  Sets_Cogenerator_large@{c o so}.

(*
CONTROL: the Corollary takes it over a completeness datum whose shape
   universe is the family's index universe, a hypothetical datum taken as
   a variable ([Sets_Complete] is [Complete@{o o o so}]).

--------
控制：推论将其作用于一个完整性数据，其形状宇宙是该家族的索引宇宙，这是一个假设数据，被视为一个变量（[Sets_Complete] 即 [Complete@{o o o so}]）。
*)
Definition p453_large_cog_abstract@{c o so w s t pk pa +|
    o < so, o < c, w <= o, so <= s, o <= s, o < t +}
  (comp : @Complete@{c c o so} Sets@{o so})
  (cont : @PreservesImageLimit@{so o so o pk c pa c} Sets@{o so} Sets@{o so}
            (@Id Sets@{o so}))
  (WP : WellPowered@{so o w s t} Sets@{o so}) :
  { F : Sets@{o so} ⟶ Sets@{o so} & F ⊣ @Id Sets@{o so} } :=
  SAFT_wellpowered (@Id Sets@{o so}) comp cont Sets_Cogenerator_large@{c o so}
    WP.

Fail Definition p453_n15_large_cog_cover@{o so +| Set < o, o < so +}
  (Un : Untruncate@{o}) :
  { F : Sets@{o so} ⟶ Sets@{o so} & F ⊣ Id } :=
  SAFT_cover_wp (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit
    Sets_Cogenerator_large (Sets_WellPowered_untruncate Un).

Fail Definition p453_n16_large_cog_comma@{o so +| Set < o, o < so +}
  (Un : Untruncate@{o}) :
  { F : Sets@{o so} ⟶ Sets@{o so} & F ⊣ Id } :=
  SAFT_wellpowered (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit
    Sets_Cogenerator_large (Sets_WellPowered_untruncate Un).

(** ** N17 (UNIVERSE): the binders are load-bearing / ** N17（宇宙）：这些活页夹能承重 *)

(*
An unannotated wrapper of [SAFT_wellpowered]: minimization sets the
   well-powering's index universe to the homs.

--------
[SAFT_wellpowered] 的未注释包装器：最小化将井-供能的指数宇宙设置为 Homs。
*)
Definition p453_unannotated {C D : Category} (U : C ⟶ D)
  (comp : @Complete C) (cont : @PreservesImageLimit C D U)
  (G : Cogenerator C) (WP : WellPowered C) : { F : D ⟶ C & F ⊣ U } :=
  SAFT_wellpowered U comp cont G WP.

(*
CONTROL: the library constant takes the index at [Set], strictly below
   the homs ([indiscrete_saft], restated).

--------
控制：库常量取 [Set] 的索引，严格位于 homs（[indiscrete_saft]，重申）以下。
*)
Definition p453_indiscrete_set_index@{j o +| j < o +} :
  { F : Indiscrete@{o j j} Type@{j} ⟶ Indiscrete@{o j j} Type@{j}
    & F ⊣ @Id (Indiscrete@{o j j} Type@{j}) } :=
  SAFT_wellpowered (@Id (Indiscrete@{o j j} Type@{j}))
    (Indiscrete_Complete (Datatypes.unit : Type@{j}))
    (right_adjoint_PreservesImageLimit (@adj_id (Indiscrete@{o j j} Type@{j})))
    (Indiscrete_Cogenerator_empty Type@{j})
    (Indiscrete_WellPowered@{o j Set o _} Type@{j}).

(* CONTROL: the wrapper takes the index at the homs. / 控制：包装器在homs处获取索引。 *)
Definition p453_unannotated_hom_index@{j o +| j < o +} :
  { F : Indiscrete@{o j j} Type@{j} ⟶ Indiscrete@{o j j} Type@{j}
    & F ⊣ @Id (Indiscrete@{o j j} Type@{j}) } :=
  p453_unannotated (@Id (Indiscrete@{o j j} Type@{j}))
    (Indiscrete_Complete (Datatypes.unit : Type@{j}))
    (right_adjoint_PreservesImageLimit (@adj_id (Indiscrete@{o j j} Type@{j})))
    (Indiscrete_Cogenerator_empty Type@{j})
    (Indiscrete_WellPowered@{o j j o _} Type@{j}).

Fail Definition p453_n17_unannotated_set_index@{j o +| j < o +} :
  { F : Indiscrete@{o j j} Type@{j} ⟶ Indiscrete@{o j j} Type@{j}
    & F ⊣ @Id (Indiscrete@{o j j} Type@{j}) } :=
  p453_unannotated (@Id (Indiscrete@{o j j} Type@{j}))
    (Indiscrete_Complete (Datatypes.unit : Type@{j}))
    (right_adjoint_PreservesImageLimit (@adj_id (Indiscrete@{o j j} Type@{j})))
    (Indiscrete_Cogenerator_empty Type@{j})
    (Indiscrete_WellPowered@{o j Set o _} Type@{j}).

(** ** N18 (CONVERSION): the lift's [Compose] universe is [cont]'s / ** N18（转换）：电梯的 [Compose] 宇宙是 [cont] 的 *)

(* CONTROL: [saft_lift]'s body, the cone at [pa]. / 控制：[saft_lift] 的身体，[pa] 上的锥体。 *)
Definition p453_lift_at_pa@{o dobj h so dp cp pl pa +|
    h <= so, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D) (c : C) (h : d ~> U c) :
  d ~> U (Subobject.sub_dom
           (saft_sub@{o dobj h so dp cp _ _} U comp G d c h)) :=
  unique_obj (cont _ _ _ (saft_pb_cone@{o dobj h so dp cp pl pa so pa _}
                            U comp cont G d c h)).

Fail Definition p453_n18_lift_at_pc@{o dobj h so dp cp pl pa pc +|
    h <= so, h < dp, h < cp, h < pc, pa < pc +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D) (c : C) (h : d ~> U c) :
  d ~> U (Subobject.sub_dom
           (saft_sub@{o dobj h so dp cp _ _} U comp G d c h)) :=
  unique_obj (cont _ _ _ (saft_pb_cone@{o dobj h so dp cp pl pa so pc _}
                            U comp cont G d c h)).

(** ** N19-N21 (UNIVERSE, TYPING): the corollaries' universes / ** N19-N21（宇宙，打字）：推论的宇宙 *)

(* CONTROL: the Corollary at the diagonal, shapes at or below the homs. / 控制：对角线上的推论，形状在同源以下或处于同源。 *)
Definition p453_diag_small@{o h so c w s t jo +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, jo <= h +}
  (C : Category@{o h h}) (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C)
  (J : Category@{jo h h}) :=
  SAFT_wellpowered (@Diagonal C J) comp
    (Continuous_PreservesImageLimit Diagonal_continuous) G WP.

(* CONTROL: the diagonal alone, shapes strictly above the homs. / 控制：仅对角线，形状严格位于homs之上。 *)
Definition p453_diag_alone@{o h jo +| h < jo +}
  (C : Category@{o h h}) (J : Category@{jo h h}) :=
  @Diagonal C J.

Fail Definition p453_n19_diag_large@{o h so c w s t jo +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, h < jo +}
  (C : Category@{o h h}) (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C)
  (J : Category@{jo h h}) :=
  SAFT_wellpowered (@Diagonal C J) comp
    (Continuous_PreservesImageLimit Diagonal_continuous) G WP.

(*
CONTROL: [saft_cocomplete]'s body with a colimit-datum universe [cr]
   declared at or above the homs.

--------
控制：使用在或高于同态处声明的余极限-数据宇宙 [cr] 来控制 [saft_cocomplete] 的身体。
*)
Definition p453_cocomplete_cr_le@{o h so c w s t jo fo fa cr +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, jo <= h,
    o <= fo, h <= fo, h < fa, h <= cr, jo <= cr +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  @Cocomplete@{cr jo h o} C :=
  fun J F => Diagonal_left_adjoint_HasColimits
               (projT2 (saft_colim C comp G WP J
                        : { L : @Fun@{jo h o h fo h fa} J C ⟶ C
                          & L ⊣ @Diagonal@{fo h fa jo o h} C J })) F.

Fail Definition p453_n20_cocomplete_cr_above@{o h so c w s t jo fo fa cr +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, jo <= h,
    o <= fo, h <= fo, h < fa, h < cr, jo <= cr +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  @Cocomplete@{cr jo h o} C :=
  fun J F => Diagonal_left_adjoint_HasColimits
               (projT2 (saft_colim C comp G WP J
                        : { L : @Fun@{jo h o h fo h fa} J C ⟶ C
                          & L ⊣ @Diagonal@{fo h fa jo o h} C J })) F.

(*
CONTROL: the representability corollary with [PreservesImageLimit]'s
   auxiliary [pa] strictly below the objects [su] of [Sets@{h su}].

--------
控制：当 [PreservesImageLimit] 的辅助 [pa] 严格位于 [Sets@{h su}] 的对象 [su] 之下时的可表示性推论。
*)
Definition p453_repr_pa_below_su@{o h so c w s t su pl pa ra rt +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, h < su, pa < su +}
  {C : Category@{o h h}} (K : C ⟶ Sets@{h su})
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h su h pl so pa so} C Sets@{h su} K)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  Representable@{ra rt su o h} K :=
  continuous_Set_functor_representable K comp cont G WP.

(* CONTROL: its biconditional with [pa] declared at or below [su]. / 控制：它与在 [su] 或以下声明的 [pa] 等值。 *)
Definition p453_repr_iff_pa_le_su@{o h so c w s t su pl pa ra rt +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, h < su, pa <= su +}
  {C : Category@{o h h}} (K : C ⟶ Sets@{h su})
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  Representable@{ra rt su o h} K
    ↔ @PreservesImageLimit@{o h su h pl so pa so} C Sets@{h su} K :=
  continuous_Set_functor_representable_iff K comp G WP.

Fail Definition p453_n21_repr_iff_pa_below_su@{o h so c w s t su pl pa ra rt +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, h < su, pa < su +}
  {C : Category@{o h h}} (K : C ⟶ Sets@{h su})
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  Representable@{ra rt su o h} K
    ↔ @PreservesImageLimit@{o h su h pl so pa so} C Sets@{h su} K :=
  continuous_Set_functor_representable_iff K comp G WP.

(** ** N22-N24 (UNIVERSE): wide pullbacks of subobjects from completeness / ** N22-N24（宇宙）：从完备性中对子对象的广泛回拉 *)

(*
CONTROL: completeness supplies them with the index at the shapes, the
   objects at or below the shapes.

--------
控制：完整性为它们提供形状的索引，以及形状上或形状下的对象。
*)
Definition p453_hw_at_shapes@{o h so k +| h <= so, o <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C) :
  HasSubobjectWidePullbacks@{o h so so k} C :=
  fun x I S => complete_wide_pullback comp (fun i => Subobject.sub_mono (S i)).

(* CONTROL: and with the index at the objects, when they fit. / 控制：当它们合适时，用指数指向物体。 *)
Definition p453_hw_at_objects@{o h so k +| h <= so, o <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C) :
  HasSubobjectWidePullbacks@{o h o o k} C :=
  fun x I S => complete_wide_pullback comp (fun i => Subobject.sub_mono (S i)).

(*
CONTROL: Adjunction/SAFT/Characterization.v's
   [Complete_HasSubobjectWidePullbacks], at the index at the objects, IS
   that term.

--------
控制：Adjunction/SAFT/Characterization.v的
   [Complete_HasSubobjectWidePullbacks]，在对象的索引处，是
   该术语。
*)
Example p453_hw_is_library@{o h so k +| h <= so, o <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C) :
  (Complete_HasSubobjectWidePullbacks comp
     : HasSubobjectWidePullbacks@{o h o o k} C)
    = p453_hw_at_objects comp :=
  eq_refl.

Fail Definition p453_n22_hw_large@{o h so k +| h <= so, so < o +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C) :
  HasSubobjectWidePullbacks@{o h o o k} C :=
  fun x I S => complete_wide_pullback comp (fun i => Subobject.sub_mono (S i)).

(*
CONTROL: N23's term, the family's index explicit, at the objects'
   universe, when the objects fit in the shapes.

--------
控制：N23 的项，家庭的索引明确，在物体的宇宙中，当物体适合这些形状时。
*)
Definition p453_hw_index_ok@{o h so +| h <= so, o <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C) (x : C)
  (I : Type@{o}) (S : I → SubObj x) :=
  @complete_wide_pullback C comp I (fun i => Subobject.sub_dom (S i)) x
    (fun i => Subobject.sub_mono (S i)).

Fail Definition p453_n23_hw_large_index@{o h so +| h <= so, so < o +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C) (x : C)
  (I : Type@{o}) (S : I → SubObj x) :=
  @complete_wide_pullback C comp I (fun i => Subobject.sub_dom (S i)) x
    (fun i => Subobject.sub_mono (S i)).

(* CONTROL: at [Sets], the index at the homs. / 控制：在 [Sets]，homs 的索引。 *)
Definition p453_sets_hw_small@{o so k +| Set < o, o < so +} :
  HasSubobjectWidePullbacks@{so o o o k} Sets@{o so} :=
  fun x I S => complete_wide_pullback Sets_Complete
                 (fun i => Subobject.sub_mono (S i)).

(* CONTROL: the library constant there, the index at the homs. / 控制：那里是库常数，homs 的索引。 *)
Definition p453_sets_hw_library@{o so k +| Set < o, o < so +} :
  HasSubobjectWidePullbacks@{so o o o k} Sets@{o so} :=
  Complete_HasSubobjectWidePullbacks Sets_Complete.

Fail Definition p453_n24_sets_hw_large@{o so k +| Set < o, o < so +} :
  HasSubobjectWidePullbacks@{so o so so k} Sets@{o so} :=
  fun x I S => complete_wide_pullback Sets_Complete
                 (fun i => Subobject.sub_mono (S i)).

(*
POSITIVE CONTROL: every premise of Theorem 2 at the thin [Subsets Y],
   [U := InverseImage f]; both preservation premises come from
   [image_preimage_adjunction f] itself.

--------
阳性对照：定理2在薄 [Subsets Y]、[U := InverseImage f] 的每个前提；两个保持前提都来自 [image_preimage_adjunction f] 本身。
*)
Definition p453_thm2_subsets@{o u so k +| o <= u, u <= so, o <= so +}
  {X Y : SetoidObject@{o o}} (f : X ~{Sets}~> Y) :
  { F : Subsets@{o u} X ⟶ Subsets@{o u} Y & F ⊣ InverseImage f } :=
  SAFT_thm2 (InverseImage f) (Subsets_Complete_free Y)
    (right_adjoint_PreservesImageLimit (image_preimage_adjunction f))
    (Subsets_Cogenerator_empty Y)
    (p453_hw_at_shapes (Subsets_Complete_free Y))
    (right_adjoint_PreservesWidePullbacks (image_preimage_adjunction f)).

(*
CONTROL: Adjunction/SAFT/Characterization/Examples.v's
   [subsets_inverse_image_thm2] IS that assembly.

--------
CONTROL: Adjunction/SAFT/Characterization/Examples.v 的
   [subsets_inverse_image_thm2] 是那个程序集。
*)
Example p453_thm2_subsets_is_library@{o so u +| Set < o, o < so, o <= u +}
  {X Y : SetoidObject@{o o}} (f : X ~{Sets@{o so}}~> Y) :
  subsets_inverse_image_thm2 f
    = (p453_thm2_subsets f
       : { F : Subsets@{o u} X ⟶ Subsets@{o u} Y & F ⊣ InverseImage f }) :=
  eq_refl.

(** ** N25, N29 (UNIVERSE): [Sets^op], co-well-powered one universe up / ** N25, N29（宇宙）：[Sets^op]，共同增强的一个宇宙上升 *)

Require Import Category.Instance.Sets.SpecialInitial.

(* CONTROL: the cover is accepted there. / 控制：封面在那里被接受。 *)
Definition p453_setsop_cover_up@{o so +| o < so +}
  (d : (Sets@{o so}^op)%category) :=
  saft_cover_at (@Id ((Sets@{o so}^op)%category)) setsop_comp
    (right_adjoint_PreservesImageLimit (@adj_id ((Sets@{o so}^op)%category)))
    setsop_cog d (Sets_CoWellPoweredAt_up _).

Fail Definition p453_n25_setsop_cover_wp_at_up@{o so +| o < so +} :
  { F : (Sets@{o so}^op)%category ⟶ (Sets@{o so}^op)%category & F ⊣ Id } :=
  SAFT_cover_wp_at (@Id ((Sets@{o so}^op)%category)) setsop_comp
    (right_adjoint_PreservesImageLimit (@adj_id ((Sets@{o so}^op)%category)))
    setsop_cog (fun d => Sets_CoWellPoweredAt_up _).

(* CONTROL: N29's solution set, not handed to [GAFT]. / 控制：N29 的解集，未交给 [GAFT]。 *)
Definition p453_setsop_solution_set_up@{o so +| o < so +}
  (d : (Sets@{o so}^op)%category) :=
  saft_solution_set_at (@Id ((Sets@{o so}^op)%category)) setsop_comp
    (right_adjoint_PreservesImageLimit (@adj_id ((Sets@{o so}^op)%category)))
    setsop_cog d (Sets_CoWellPoweredAt_up _).

Fail Definition p453_n29_setsop_gaft_up@{o so +| o < so +} :
  { F : (Sets@{o so}^op)%category ⟶ (Sets@{o so}^op)%category & F ⊣ Id } :=
  GAFT (@Id ((Sets@{o so}^op)%category)) setsop_comp
    (right_adjoint_PreservesImageLimit (@adj_id ((Sets@{o so}^op)%category)))
    (fun d =>
       saft_solution_set_at (@Id ((Sets@{o so}^op)%category)) setsop_comp
         (right_adjoint_PreservesImageLimit
            (@adj_id ((Sets@{o so}^op)%category)))
         setsop_cog d (Sets_CoWellPoweredAt_up _)).

(** ** Controls without a negative / ** 没有否定的控制 *)

(*
The representing object is the left adjoint at the singleton
   ([continuous_Set_functor_representable_obj], restated).

--------
表示对象是在单例 ([continuous_Set_functor_representable_obj], 重新表述) 上的左伴随。
*)
Example p453_repr_obj@{o h so c w s t su pl pa ra rt +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, h < su +}
  {C : Category@{o h h}} (K : C ⟶ Sets@{h su})
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h su h pl so pa so} C Sets@{h su} K)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  @repr_obj C K
    (continuous_Set_functor_representable K comp cont G WP
       : Representable@{ra rt su o h} K)
    = fobj[projT1 (SAFT_wellpowered K comp cont G WP)] SetsOne :=
  eq_refl.

(*
The cover's index at [h] IS the well-powering's name for the pullback
   subobject ([saft_cover_at_index], restated).

--------
[h] 的封面索引是为回撤子对象（[saft_cover_at_index]，重述）命名的良好电源名称。
*)
Example p453_cover_index@{o dobj h so dp cp w s t pl pa +|
    h <= so, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D)
  (W : WellPoweredAt@{w o s h t} (saft_prod@{o dobj h so dp} U comp G d))
  (c : C) (h : d ~> U c) :
  projT1 (saft_cover_at@{o dobj h so dp cp w s t pl pa _ _ _}
            U comp cont G d W c h)
    = wp_from W (saft_sub@{o dobj h so dp cp _ _} U comp G d c h) :=
  eq_refl.

(*
The cover with the well-powering's [t] and [PreservesImageLimit]'s
   auxiliary [pa] apart, in both orders.

--------
带有强力供电的 [t] 和 [PreservesImageLimit] 的盖子，其辅助 [pa] 分开，按任意顺序。
*)
Definition p453_cover_t_below_pa@{o dobj h so dp cp w s t pl pa +|
    h <= so, h < dp, h < cp, o <= s, h <= s, h < t, t < pa +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D)
  (W : WellPoweredAt@{w o s h t} (saft_prod@{o dobj h so dp} U comp G d)) :=
  saft_cover_at@{o dobj h so dp cp w s t pl pa _ _ _} U comp cont G d W.

Definition p453_cover_pa_below_t@{o dobj h so dp cp w s t pl pa +|
    h <= so, h < dp, h < cp, o <= s, h <= s, h < t, pa < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D)
  (W : WellPoweredAt@{w o s h t} (saft_prod@{o dobj h so dp} U comp G d)) :=
  saft_cover_at@{o dobj h so dp cp w s t pl pa _ _ _} U comp cont G d W.

(*
At one tuple at [Id[Sets]] under [Untruncate], the reshaped covering
   datum holds at every object and the old one is refuted.

--------
在[Untruncate]下的[Id[Sets]处的一个元组中，重新构形的覆盖基准在每个对象上都成立，而旧的被驳斥。
*)
Definition p453_separation@{o so t +| Set < o, o < so, o < t +}
  (Un : Untruncate@{o}) :
  (∀ d : Sets@{o so},
     SubobjectCoverAt (@Id Sets@{o so}) Sets_Complete
       (Sets_Cogenerator_untruncate Un) d
       (Sets_WellPowered_untruncate@{o so t} Un _))
  * (SubobjectCover (@Id Sets@{o so}) Sets_Complete
       (Sets_Cogenerator_untruncate Un)
       (WellPowered_SubobjectIndex (Sets_WellPowered_untruncate@{o so t} Un))
     → False) :=
  sets_id_cover_separation Un.

(* The monos lemma over pullbacks in [C], at its stated type. / [C] 中在其声明类型下关于拉回的 monomorphism 引理。 *)
Definition p453_monos_lemma@{o hc dobj h +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  (HP : HasPullbacks C) {X Y : =(d) ↓ U} (m : X ~{=(d) ↓ U}~> Y) :
  Monic m ↔ Monic (snd (`1 m)) :=
  comma_monic_iff_underlying_monic HP m.

(** ** Guard block / ** 防守格挡 *)

Check @comma_monic_of_underlying.
Check @kp_diag.
Check @kp_diag_fst.
Check @kp_diag_snd.
Check @kp_obj.
Check @kp_fst.
Check @kp_snd.
Check @underlying_monic_of_comma_monic.
Check @comma_monic_iff_underlying_monic.
Check @comma_cogenerator.
Check @comma_wp_index.
Check @comma_wp_dom.
Check @comma_wp_mono.
Check @comma_wp_to.
Check @underlying_sub.
Check @comma_wp_from.
Check @comma_wp_iso_to.
Check @comma_wp_iso_from.
Check @comma_wp_to_from.
Check @comma_WellPoweredAt.
Check @comma_WellPowered.
Check @SAFT_comma_initial.
Check @SAFT_universal_arrow.
Check @SAFT_left.
Check @SAFT_adjunction.
Check @SAFT_wellpowered.
Check @SAFT_left_obj.
Check @SAFT_wellpowered_iff.
Check @HasSubobjectWidePullbacks.
Check @Complete_HasSubobjectWidePullbacks.
Check @least_index.
Check @least_top.
Check @least_lift.
Check @least_lift_commutes.
Check @least_dom.
Check @least_mono.
Check @least_sub.
Check @least_index_of.
Check @least_le.
Check @SAFT_thm2_initial.
Check @SAFT_thm2_universal_arrow.
Check @SAFT_thm2_left.
Check @SAFT_thm2_adjunction.
Check @SAFT_thm2.
Check @SAFT_thm2_left_obj.
Check @right_adjoint_PreservesWidePullbacks.
Check @SAFT_iff.
Check @image_family_cone.
Check @saft_index.
Check @saft_fam.
Check @saft_prod_limit.
Check @saft_prod.
Check @saft_point.
Check @saft_point_commutes.
Check @saft_kappa.
Check @saft_square.
Check @saft_sub.
Check @saft_sub_to.
Check @saft_pb_cone.
Check @saft_lift.
Check @saft_lift_commutes.
Check @SubobjectCoverAt.
Check @saft_cover_at.
Check @saft_solution_set_at.
Check @SAFT_cover_wp_at.
Check @SAFT_cover_wp.
Check @saft_cover_at_index.
Check @saft_solution_set_at_index.
Check @SAFT_cover_wp_is_GAFT.
Check @continuous_Set_functor_representable.
Check @continuous_Set_functor_representable_obj.
Check @continuous_Set_functor_representable_iff.
Check @continuous_Set_functor_representable_at.
Check @saft_colim.
Check @saft_cocomplete.
Check @SAFT_cover_wp_iso.
Check @comma_cogenerator_index.
Check @sets_id_saft.
Check @sets_id_saft_cover.
Check @sets_id_new_cover.
Check @sets_id_old_cover_refuted.
Check @sets_id_cover_separation.
Check @sets_hom_saft.
Check @sets_id_repr_saft.
Check @sets_hom_repr_saft.
Check @sets_saft_cocomplete.
Check @subsets_inverse_image_saft.
Check @subsets_inverse_image_thm2.
Check @subsets_saft_cocomplete.
Check @indiscrete_saft.
Check @indiscrete_saft_cocomplete.
Check @sets_id_saft_iso.
Check @subsets_inverse_image_saft_iso.
