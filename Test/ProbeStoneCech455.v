(**
* Probe for Stone–Čech and Mac Lane V.8 Exercise 4 (issue #455)

    Pins the measured boundaries of the two files #455 adds for Mac Lane
    §V.6, printed p. 125, and §V.8, printed pp. 131–132 (the Stone–Čech
    compactification through the adjoint functor theorems, and Exercise
    4): Instance/Top/StoneCech.v (the finite case of §V.6 as a universal
    arrow with its [eq_refl] readbacks, GAFT at the underlying-set functor
    reduced to completeness, and Exercise 4 at the level of universal
    arrows) and Instance/Top/StoneCech/Refutations.v (completeness of
    [CompHaus] and of [Top], and the adjunction at [CompHaus_Forget],
    refuted under an arrow index or [IEM], above the hom universe through
    an index of [Top]; the vacuity pairs; SAFT at the inclusion reduced to
    three hypotheses; [big_inj]; the cost of a cogenerator with stable
    members, and of a single point-separating space).  N2, N6-N14 and
    N18-N22 restate a readback or a refusal that a target header records,
    N2 and N12 first measured by #455's review; N1, N3-N5 and N15-N17 are
    this file's own.  The positive controls restate the files' claims
    independently.

    THE IMPORT LIST, measured by comparing [Require] lines by script.
    First Instance/Top/StoneCech/Refutations.v's twenty lines verbatim and
    in order, one of them the target Instance/Top/StoneCech.v; then the
    five lines Instance/Top/StoneCech.v adds, in its order
    (Structure/Cone.v, Structure/Limit.v, Structure/Limit/Preservation.v,
    Instance/Sets/Classifier.v and the standard library's [PeanoNat]);
    then the one target Refutations.v's list does not carry, itself.
    Twenty-six lines, with no addition for any section.  Instance/Sets.v
    and Instance/Top.v each define a [bool_setoid_object]; under this list
    the short name is Instance/Top.v's, the one the targets use, and
    Instance/Sets.v's is [Sets.bool_setoid_object] ([Locate]).  A shorter
    import list is what makes a probe pass for no reason.

    DISCIPLINE.  The instrument was checked both ways: the refutation of an
    absent name is refused for that reason, and each of the eighty-one
    definitions, examples, lemmas and records of this file that is not a
    refutation, wrapped in one in a copy of this WHOLE file, stops the
    build at that command with the report that the guarded command had
    been accepted (eighty-one of eighty-one, by a script over the
    copies).
    Every negative other than that instrument is a [Definition] or an
    [Example], never a [Check], so that an open evar or a missing instance
    cannot satisfy it.  Each negative was stripped of its refutation
    keyword in a copy of this WHOLE file, one at a time, compiled, and its
    error read; each of the twenty-three copies stops inside the stripped
    command (by the File line that precedes its error, compared by a
    script with the command's extent).  The kind recorded is the kind of
    that error, and each negative has positive controls beside it; every
    identifier a negative uses, its own name and the universes its binder
    names aside, is used by some positive control of this file (by a
    script over the identifiers of the commands).  In one further copy of
    this WHOLE file, each negative was followed by a BINDER INSTRUMENT, the
    same universe binder, arguments and return type with a trivial body
    (a hypothesis of the return type, or [Datatypes.unit] where the command
    states none): all twenty-two are accepted, so every negative is refused
    by its body.  Every UNIVERSE negative is a top-level definition whose
    universes are declared in its own binder, never a [Section]'s.
    Quotations are Rocq 9.1.1's under this file's import list, with the
    error's environment block left out; Rocq prints the "cannot unify"
    parenthetical with the short names in scope, and a universe the
    stripped copy names after itself and a serial number is written <1>,
    <2>, ..., numbered afresh in each quotation in order of first
    appearance.  The file also compiles on Coq 8.19.2 and 8.20.1, against
    the prebuilt trees of this library for those versions with the two
    targets compiled beside them from this tree; over the 152 files of
    the targets' dependency closure other than the targets, the sources of
    those trees are this tree's byte for byte but for Instance/Top.v and
    Instance/Top/CompHaus.v, which differ in comment blocks alone
    (compared by [cmp] and [diff]).  The stripped copies were compiled
    there as well, and every one is refused on both at the line and
    character range of its Rocq 9.1.1 refusal.  Under 8.20.1 every error
    but N13's is the Rocq 9.1.1 one up to the serial numbers (compared by
    a script over the copies); N13's clause names a generated universe
    where Rocq 9.1.1 names c.  Under 8.19.2 eleven are (the instrument,
    N1-N6, N8 and N20-N22); N15 keeps its clause with serial names in
    place of c and h, N7, N9-N11, N13, N14, N16, N18 and N19 print a
    "cannot unify" parenthetical in place of theirs, and N12 and N17
    print the type mismatch with no parenthetical.

    KINDS.  Twenty-three refutations, counted as the lines that open with
    the refutation keyword: NAME-ABSENCE (the instrument), CONVERSION
    (N1-N4), TYPING (N5) and UNIVERSE (N6-N22): one, four, one and
    seventeen.  No refusal is an INSTANCE or a BINDER one: every binder
    instrument is accepted.  N15 is reported over the whole command rather
    than at a subterm; the type it forms is its body, and its binder
    instrument is accepted.  N20, N21 and N22 carry no universe clause:
    each is reported as a mismatch whose two sides differ in universe
    instances alone, and in universes their binders name only at the
    slots of [CompHaus] their paragraphs give (the fourth for N20, the
    third for N21, the fourteenth and fifteenth for N22); every other
    slot that differs is one the binder leaves to inference ([_]).

    LABELS.  The pins carry the N-numbers of this file; #455's builder and
    review measured several of them in scratch files under other names,
    recorded here so that the target headers can cite either.  The
    review's p1 is the control [p455_fin_obj_bool], its p2 is N2 (its
    [bool_FinEnum'] is [p455_bool_FinEnum_rev]) and its p2pos the control
    [p455_fin_obj_bool_enum]; its p3 is [p455_refutes_gaft_output], its
    p6 is N12, its p8_big_inj is [p455_big_inj_unsplit], its p9_iff is
    [p455_compact_iff] and its w1 is [p455_saft_incl_apart].  The
    builder's and the review's [TopP], [ContHom] and [ContHomT] are
    [p455_TopP], [p455_ContHom] and N6, and the builder's
    [t_bool_FinEnum] is [p455_bool_FinEnum_bare].  The review of this
    file named v_sub_index, v_adj_refuted_IEM_above,
    v_gaft_shape_refuted_above and v_not_complete_IEM_below, which
    Refutations.v now carries as [CompHaus_ArrowIndex_of_Top],
    [StoneCech_adjunction_refuted_IEM_above],
    [CompHaus_not_complete_IEM_above] and
    [CompHaus_not_complete_IEM_below]; its v_saft_wp_below is N19, its
    v_n8_at_set [p455_bool_ch_bare_at_set], its v_ts_free
    [p455_trivial_small_free], its v_n1_wrong [p455_n1_wrong_value] and
    its v_n2_same_space [p455_n2_same_space].  A later review's adj14 is
    N22 and its s14ctl [p455_adj_above_hausdorff_at_o].  The labels are
    not constants.

    ** Instance/Top/StoneCech.v

    N1, N2 (CONVERSION).  The universal object of [StoneCech_finite] is
    [Discrete_CH X FX] at [eq_refl] ([p455_fin_obj_at], restating
    [StoneCech_finite_obj]).  At the two-point set a wrong value has to be
    chosen with care: [Bool_CH] is NOT one, being by definition
    [Discrete_CH] of [bool_setoid_object] at [bool_FinEnum], and the
    equation with it is accepted ([p455_fin_obj_bool], the trap).  N1
    compares the universal object with the one-point space, whose carrier
    differs:
      The term "eq_refl" has type "arrow_obj = arrow_obj" while it is
      expected to have type "arrow_obj = Point_CH" (cannot unify
      "arrow_obj" and "Point_CH").
    N2 compares it with [Discrete_CH] at a second enumeration of the same
    set, [p455_bool_FinEnum_rev], whose list is reversed and whose object
    is formed ([p455_bool_ch_rev]):
      The term "eq_refl" has type "arrow_obj = arrow_obj" while it is
      expected to have type "arrow_obj = Discrete_CH bool_setoid_object
      p455_bool_FinEnum_rev" (cannot unify "arrow_obj" and "Discrete_CH
      bool_setoid_object p455_bool_FinEnum_rev").
    The same statement at [bool_FinEnum] is accepted
    ([p455_fin_obj_bool_enum]).  Both enumerations end [Qed], so N2 would
    be refused for ANY second enumeration, one with the same list under
    another name among them: it pins that the universal object carries the
    enumeration it was built from.  Whether the value compared is wrong is
    meta-level: the two objects have one space ([p455_n2_same_space], at
    [eq_refl]) and differ only in their compactness proofs, [Qed] terms
    whose values no lemma of the tree exposes, so the wrongness is of the
    normal forms behind [Qed], not a theorem.  A draft of this paragraph
    said that reversing the list made the value wrong as well as
    unconvertible; #455's review measured it unconvertible only.
    N1 is refused at the carrier, where no opacity is involved, and its
    value is wrong as a theorem: [p455_n1_wrong_value] derives [False] from
    the equation, carrying [true] and [false] of the two-point carrier to
    the point.

    N3 (CONVERSION).  The unit is [sc_fin_unit X FX] at [eq_refl]
    ([p455_fin_unit_at], restating [StoneCech_finite_unit]); it does not
    see the enumeration ([p455_fin_unit_other_enum]: at [FX] it IS
    [sc_fin_unit X FX'] for any [FX']), and at the two-point set it is the
    identity of [Sets] ([p455_fin_unit_bool_id]).  N3 compares it with the
    negation [p455_negb_lift], an arrow of the same type, ending [Defined],
    that differs from the unit at the point [true] ([p455_negb_not_unit]):
      The term "eq_refl" has type "arrow = arrow" while it is expected to
      have type "arrow = p455_negb_lift" (cannot unify "arrow" and
      "p455_negb_lift").

    N4 (CONVERSION).  At a compact Hausdorff [K] the identity universal
    arrow has [K] as its universal object ([p455_incl_obj_at], restating
    [CompHaus_Incl_universal_obj]); at [K] := [Point_CH] the equation with
    [Point_CH] is accepted ([p455_incl_obj_point]), and at a variable [K]:
      The term "eq_refl" has type "arrow_obj = arrow_obj" while it is
      expected to have type "arrow_obj = Point_CH" (cannot unify
      "arrow_obj" and "Point_CH").

    N5 (TYPING).  Why every universal arrow of the two targets is written
    [UniversalArrow (C:=Sets) ...] or [(C:=Top@{h o})], and every readback
    [@arrow_obj Sets _ ...]: Theory/Universal/Arrow.v's [UniversalArrow]
    elaborates its object before its category, so without [C] the object
    is refused, and with it the type is formed ([p455_ua_with_C]):
      The term "Setoid_Lift X" has type "SetoidObject" while it is expected
      to have type "obj[?C]".
    The same refusal meets [@arrow_obj _ _ (Setoid_Lift X) ...] and
    [UniversalArrow (KSet AI) ...], both recorded by #455's builder and
    scouts (measured in scratch files with this file's import list).

    N6 (UNIVERSE).  StoneCech.v's header, WHY: THE UNIVERSE OF TOP'S HOMS,
    records that a Prop-valued topology puts continuous maps at the
    universe of the points, and cites this file's [p455_TopP] (a setoid
    with Prop-valued opens closed under unions indexed at the points'
    universe, and no other field) and [p455_ContHom], both accepted under
    the CLOSED binder [@{o}], so [p455_ContHom@{o}] lands in [Type@{o}]
    with no constraint at all.  The tree's
    [ContinuousMorphism] is accepted at [Type@{h}] with [o < h]
    ([p455_conthom_at_h]); at [Type@{o}], N6:
      The term "ContinuousMorphism X Y" has type "Type@{<1>}" while it is
      expected to have type "Type@{o}" (universe inconsistency: Cannot
      enforce <1> <= o because o < <1>).
    The header's quotation, from a closed binder [@{o}], carries the same
    clause; N6's binder is extensible, so the refusal is not the binder's.

    N7 (UNIVERSE).  Instance/Top.v's [Point_Hausdorff] is monomorphised at
    a [Set] carrier ([About]: [IsHausdorff@{u Set Set Set}
    Point_Top@{Set}]; that file's CORRECTION (#455) comment).  It is
    accepted there ([p455_point_hausdorff_set]); above [Set] the one-point
    space is separated by [Discrete_Hausdorff] ([p455_point_hausdorff_o])
    and compact by Instance/Top.v's universe-general [Point_Compact]
    ([p455_point_compact_o]), and [Point_CH]'s space is [Point_Top@{o}] at
    [Set < o] ([p455_point_ch_above_set]).  [Point_Hausdorff] at that
    type, N7:
      The term "Point_Hausdorff" has type "IsHausdorff@{<1> Set Set Set}
      Point_Top@{Set}" while it is expected to have type "IsHausdorff@{h o
      o o} Point_Top@{o}" (universe inconsistency: Cannot enforce Set =
      o).

    N8 (UNIVERSE).  StoneCech.v's header, UNIVERSES: without a binder,
    [bool_FinEnum] elaborates at [FinEnum@{Set} bool_setoid_object@{Set
    Set}], "which would force [Bool_CH], built from it, and so the
    refutations that use [Bool_CH], to a [Set] carrier".  Restated as
    [p455_bool_FinEnum_bare], the same proof with no binder, whose [About]
    reads the same (measured in a scratch copy of this file).  N8's own
    body at [Set] is accepted ([p455_bool_ch_bare_at_set]), so that "forces
    a [Set] carrier" is measured rather than read off the clause.  What it
    forces is narrower than the lemma: it is accepted at [Set]
    ([p455_bare_at_set]); at [FinEnum bool_setoid_object@{o o}] with [Set
    < o] it is accepted too, by conversion ([p455_bare_at_o]); and so is an
    object of [CompHaus] above [Set] built from it once the setoid is named
    at [o] ([p455_bare_named_setoid]).  What is refused is [Bool_CH]'s own
    body, which leaves the setoid to inference, so that the placeholder is
    solved from the lemma's type, at [Set].  That body with the file's
    [bool_FinEnum] is accepted under an extensible binder
    ([p455_bool_ch_body]), and [Bool_CH] itself lives above [Set]
    ([p455_bool_ch_above_set]); with [p455_bool_FinEnum_bare], N8:
      The term "(Bool_Discrete; (Discrete_Compact_of_FinEnum
      bool_setoid_object p455_bool_FinEnum_bare, Discrete_Hausdorff ?A))"
      has type "∃ x : obj[Top], Subcategory.sobj _
      CompactHausdorff_Subcategory x" while it is expected to have type
      "obj[CompHaus]" (cannot satisfy constraint "IsCompact (Discrete_Top
      bool_setoid_object) ∧ IsHausdorff (Discrete_Top ?A)" == "(λ x :
      obj[Top], Subcategory.sobj _ CompactHausdorff_Subcategory x)
      Bool_Discrete"; universe inconsistency: Cannot enforce Set = o).
    With [Set < o] declared the same body is refused with the same clause
    (measured in a scratch file with this file's import list).  So the
    header's sentence holds of [Bool_CH] as written, where the binder is
    load-bearing; the lemma itself converts to any carrier.

    N9 (UNIVERSE).  StoneCech.v's header, (3) and UNIVERSES: the
    tautological solution set is legal because the whole object type of
    [CompHaus] sits at its hom universe, and all four universes of GAFT's
    completeness hypothesis are h.  [taut_sols] itself is not bound to
    that: its index is the universe of the objects of the [CompHaus] its
    [CompHaus_Forget] starts from ([About]), and with those objects at c
    above h it is accepted ([p455_taut_sols_above]).  Adjunction/GAFT.v's
    [GAFT] takes solution sets indexed at the hom universe
    ([SolutionSet@{h dobj cobj h}]), so
    GAFT at [CompHaus_Forget] with [taut_sols] is accepted with the objects
    at h ([p455_gaft_body], [GAFT_CompHaus_only_complete]'s body restated,
    and [p455_gaft_only_complete]), and at [h < c] N9 is refused at
    [taut_sols], whose type, a solution set indexed at the objects'
    universe, is expected to be one indexed at h:
      (universe inconsistency: Cannot enforce c = h because h < c).
    The placement of the objects at h is what GAFT's use of the
    tautological solution set costs; with the objects above h GAFT would
    need another solution set, which neither target builds.

    ** Instance/Top/StoneCech/Refutations.v

    N10 (UNIVERSE).  Refutations.v's UNIVERSES: the index form
    [CompHaus_not_complete] ties nothing between the shape s and the
    objects c, the [IEM] form needs [c <= s].  The index form is accepted
    at [s < c] ([p455_not_complete_index]), the [IEM] form at [c <= s] and
    [h <= s] ([p455_not_complete_IEM]) and at GAFT's instance
    ([p455_not_complete_IEM_gaft]).  The [IEM] form at [s < c], N10:
      The term "comp" has type "Complete@{r s h c}" while it is expected
      to have type "Complete@{<1> s h <2>}" (universe inconsistency:
      Cannot enforce <2> = c because <2> <= <3> < c).
    Structure/Complete/Freyd.v's [canonical_ArrowIndex], which
    [CompHaus_not_complete_IEM] applies to [CompHaus]'s own objects,
    indexes at or above the objects and the homs ([About]:
    [ArrowIndex@{u u0 u1}] under [u0 <= u] and [u1 <= u]).  So N10 pins
    the scope of that constant, not the reach of [IEM]:
    [CompHaus_ArrowIndex_of_Top] transports an index of [Top]
    ([p455_sub_index]), [IEM] supplies one at every [s] with [h <= s], and
    [CompHaus_not_complete_IEM_below] refutes N10's statement with
    [h <= s] added ([p455_not_complete_IEM_below]), GAFT's shape with the
    objects above the homs being its case
    [CompHaus_not_complete_IEM_above] ([p455_not_complete_IEM_above]).

    N11 (UNIVERSE).  The same for [Top]: [Top_not_complete] is accepted at
    [s < h] ([p455_top_not_complete_index]) and [Top_not_complete_IEM] at
    [h <= s] ([p455_top_not_complete_IEM]); the latter at [s < h], N11:
      The term "comp" has type "Complete@{r s h h}" while it is expected
      to have type "Complete@{<1> <2> <3> <3>}" (universe inconsistency:
      Cannot enforce <3> = h because <3> <= <2> < h).

    N12 (UNIVERSE).  The reach of [StoneCech_adjunction_refuted_IEM]: it
    is proved at [CompHaus@{h h h h ...}], the objects at the hom
    universe, which is the instance [GAFT_CompHaus_only_complete] produces
    ([p455_adj_refuted_IEM], restating it, and [p455_refutes_gaft_output],
    the refutation applied to GAFT's own output).  With the objects at c
    above h, N12 is refused at the argument [A], whose type, as written in
    the binder, is expected to be the one the constant quantifies over,
    with one universe in the object and hom slots of its [CompHaus]:
      (universe inconsistency: Cannot enforce c = h because h < c).
    The index form reaches that instance: given an arrow index at the hom
    universe, [large_universal_arrow_refuted] refutes the adjunction with
    the objects at c above h ([p455_adj_refuted_index_above]).  N12 pins
    the scope of [StoneCech_adjunction_refuted_IEM], which applies
    [canonical_ArrowIndex] to [CompHaus]'s own objects, not the reach of
    [IEM]: [IEM] supplies an index at the hom universe through [Top]'s,
    and [StoneCech_adjunction_refuted_IEM_above] refutes N12's very
    statement ([p455_adj_refuted_IEM_above]).  A draft of this paragraph
    said that [IEM] does not supply such an index; #455's review measured
    that it does, through [CompHaus_ArrowIndex_of_Top].

    N20-N22 (UNIVERSE).  Refutations.v's COVERAGE: the forms through
    [Top]'s index apply only at instances of [CompHaus] whose third slot,
    the hom universe of its [Top], is h, whose fourth, the universe of the
    proof that a space is compact Hausdorff, is c, and whose fourteenth
    and fifteenth, the universes of the separating opens of its Hausdorff
    proof, are the points' universe o.  With [CompHaus]
    written out slot by slot, [StoneCech_adjunction_refuted_IEM_above] is
    accepted with the fourth slot at c ([p455_adj_above_slots]); with it
    at h, N20 is refused at [A]:
      The term "A" has type "∃ F : Sets@{h s} ⟶ CompHaus@{c h h h ...},
      F ⊣ CompHaus_Forget@{...}" while it is expected to have type "∃ F :
      Sets@{h s} ⟶ CompHaus@{c h h c ...}, F ⊣ CompHaus_Forget@{...}".
    [CompHaus_not_complete_IEM_below] at GAFT's shape above the homs is
    accepted with the third slot at h ([p455_not_complete_below_slots]);
    with it at t below h, N21 is refused at [comp]:
      The term "comp" has type "@Complete@{h h h c} CompHaus@{c h t c
      ...}" while it is expected to have type "@Complete@{h h h c}
      CompHaus@{c h h c ...}" (cannot unify "D ⟶ CompHaus@{c h h c ...}"
      and "D ⟶ CompHaus@{c h t c ...}"),
    the last eleven slots of each [CompHaus], and the instances of
    [CompHaus_Forget], elided.  The older form reaches the third slot
    below h where its [c <= s] holds ([p455_not_complete_IEM_top_slot], at
    c = h = s); at an instance with t < h < c and a shape below c neither
    form applies, the older one needing [c <= s] (N10).
    [StoneCech_adjunction_refuted_IEM_above] is accepted with the
    fourteenth and fifteenth slots written out at o
    ([p455_adj_above_hausdorff_at_o]), o being where [Bool_CH] and
    [Point_CH] put them, from [Discrete_Hausdorff@{h o}]; with both at q
    below o, where the adjunction's type is still formed (N22's binder
    instrument), N22 is refused at [A]:
      The term "A" has type "∃ F : Sets@{h s} ⟶ CompHaus@{c h h c ...
      q q}, F ⊣ CompHaus_Forget@{...}" while it is expected to have type
      "∃ F : Sets@{h s} ⟶ CompHaus@{c h h c ... o o}, F ⊣
      CompHaus_Forget@{...}",
    the fifth through thirteenth slots of each [CompHaus], and the
    instances of [CompHaus_Forget], elided.  #455's review measured the
    same refusal with either slot alone below o, and a refusal of every
    other form, the index forms included, with both below o (in scratch
    files with this file's import list).

    N13, N14 (UNIVERSE).  Refutations.v's (3): discharging the
    well-poweredness of SAFT at the inclusion by [CompHaus_WellPowered]
    forces [c = h].  [SAFT_CompHaus_Incl] is restated ([p455_saft_incl]),
    and its body with c and h named apart and nothing declared between
    them is accepted ([p455_saft_incl_apart]; its [About] reads "c = h",
    measured in a scratch copy of this file).  At [h < c], N13 is refused
    at [CompHaus_WellPowered], whose type is expected at the instance the
    other arguments fix:
      (universe inconsistency: Cannot enforce h = <1> because h < c <=
      <1>),
    and at [c < h] N14 is refused at [comp], before the well-powering is
    reached, with the inclusion's clause (N17, N19):
      The term "comp" has type "Complete@{s s h c}" while it is expected
      to have type "Complete@{s s h <1>}" (universe inconsistency: Cannot
      enforce <1> = c because c < h <= <1>).
    With a well-powering hypothesis indexed at the objects' universe in
    place of [CompHaus_WellPowered], SAFT at the inclusion is accepted at
    [h < c] ([p455_saft_wp_hyp_above]), and so are the two vacuity pairs
    with theirs ([p455_saft_vacuous], [p455_saft_iem_vacuous]): the half
    [c <= h] of the equation is [CompHaus_WellPowered]'s, not SAFT's.
    The half [h <= c] is the inclusion's under ANY well-powering: with a
    well-powering hypothesis at [c < h], N19 is refused at [comp] with the
    same clause as N14:
      The term "comp" has type "Complete@{s s h c}" while it is expected
      to have type "Complete@{s s h <1>}" (universe inconsistency: Cannot
      enforce <1> = c because c < h <= <1>).
    A draft of this paragraph attributed the whole equation to
    [CompHaus_WellPowered]; #455's review measured that only [c <= h] is
    its (N19).  With
    the shape below the objects, which such a well-powering allows,
    [SAFT_Incl_IEM_vacuous_below] still pairs SAFT with the refutation
    ([p455_saft_iem_vacuous_below]).

    N15-N17 (UNIVERSE).  Where each half of [c = h] comes from.  [c <= h]:
    Structure/WellPowered.v's [WellPowered@{o h w s t}] declares [o <= s],
    and [trivial_small] fixes s at the hom universe ([WellPowered@{o h h h
    t}]).  [CompHaus_WellPowered] is restated ([p455_wellpowered]),
    [trivial_small] is accepted at [c < h] ([p455_trivial_small_below]),
    and a well-powering type indexed at c is formed at [h < c]
    ([p455_wp_type_at_c]); the one indexed at h is not, N15:
      Universe inconsistency. Cannot enforce c <= h because h < c.
    and [trivial_small] does not inhabit the one indexed at c, N16:
      The term "trivial_small CompHaus" has type "WellPowered@{<1> <2> <2>
      <2> <3>} CompHaus@{...}" while it is expected to have type
      "WellPowered@{c h h c t} CompHaus@{...}" (universe inconsistency:
      Cannot enforce c = h because h < c),
    the two instances of [CompHaus] elided; with c and h left unordered
    the same type is inhabited, at c = h ([p455_trivial_small_free], whose
    [About] reads "c = h").  [h <= c]: [CompHaus_Incl]
    carries its domain's hom universe below its objects' ([About]: the
    domain is [CompHaus@{u u0 u0 ...}] under [u0 <= u]).  The inclusion is
    accepted at [h < c] ([p455_incl_above]); at [c < h], N17 is refused at
    [CompHaus_Incl], whose type is expected at the ascribed [CompHaus]:
      (universe inconsistency: Cannot enforce <1> = h because <1> <= <2> <
      h).

    N18 (UNIVERSE).  Refutations.v's (4): [big_inj] ties its index to the
    objects of the very category [comp] is about, by the local definition
    [C := CompHaus], and its block carries [c <= s].
    [big_inj_injective] is restated ([p455_big_inj_injective]), and
    [big_inj]'s body with [obj[CompHaus]] written in both places is
    accepted at [s < c] ([p455_big_inj_unsplit]), the two [CompHaus] then
    separate instances; [big_inj] at [s < c], N18:
      The term "comp" has type "Complete@{r s h c}" while it is expected
      to have type "Complete@{<1> s h <2>}" (universe inconsistency:
      Cannot enforce <2> = c because <2> <= <3> < c).

    CONTROLS of the rest of the two files, each restating a constant at
    its stated type: the constructive pieces [p455_stonecech_finite],
    [p455_discrete_hausdorff], [p455_compact_iff] (compactness of a
    discrete space iff finite enumerability, both directions at one
    instance) and [p455_nat_not_compact]; the reduction [p455_pres] and
    [p455_taut_sols]; Exercise 4, [p455_ex4_separated],
    [p455_ex4_converse], [p455_ex4_dec], [p455_ex4_bool],
    [p455_ex4_incl], [p455_ex4_incl_converse], [p455_ex4_at_CompHaus],
    [p455_ex4_incl_local] and [p455_ex4_local_at_CompHaus]; and the
    metatheorems [p455_large_ua_refuted], [p455_gaft_vacuous],
    [p455_gaft_vacuous_above], [p455_cogen_dne] and [p455_point_sep_dne].
    Nothing here inhabits the premises of the completeness conditionals,
    of [p455_cogen_dne] or of [p455_point_sep_dne].

    NOT PINNED HERE.  (a) That the tree builds no unconditional binary
    product in [Top]: the two walls in front of the pairing's continuity
    are Test/ProbeCompHaus413.v's N1 and N2.  A draft of this item said
    that [Top] has no binary products without a hypothesis, and that that
    probe pins it; #455's review found that this is not a theorem
    (classically [Top] has them).  (b) The
    report of #455's scouts that [Section] [Context] binders over
    [CompHaus] are refused: it did not reproduce for #455's builder, and
    neither target rests on it.  (c) [About] readbacks as such, the
    [Set] of [p455_bool_FinEnum_bare], the "c = h" of
    [p455_saft_incl_apart] and the index of [taut_sols]: measured in
    scratch copies of this file, and pinned here by their consequences (N8,
    N13-N17 and N9); likewise the [h <= c] that [CompHaus_Forget] and
    [CompHaus_Incl] carry and the slots Refutations.v's COVERAGE names
    (N12, N17, N19-N22).  (d) Flip censuses ([Defined] against [Qed]) and the
    closure of the targets under [Print Assumptions]: measurements of the
    build rather than of commands; the Makefile's print-assumptions gate
    is where closure is kept.  An item (e), the review's p4 and p5, is
    retired: both are now constants of the targets, restated by
    [p455_ex4_incl_local], [p455_ex4_local_at_CompHaus] and
    [p455_point_sep_dne].

    The guard block at the end names the seventy-four constants of the
    two targets, so that a rename breaks this file: forty-one of
    Instance/Top/StoneCech.v and thirty-three of
    Instance/Top/StoneCech/Refutations.v.  They are the [def] and [prf]
    entries of the targets' .glob files, which carry no entry of any other
    kind (no [abbrev] among them), and exactly the names [Print Module]
    lists for each (compared by [diff]); neither target uses [Program], so
    there is no obligation constant.  Under the full import list, [Locate]
    lists exactly one object for each of the seventy-four, the target's.

--------
* 关于 Stone–Čech 和 Mac Lane V.8 的探讨 练习 4（问题 #455）

固定两个文件 #455 为 Mac Lane 添加的测量边界 §V.6，印刷在第 125 页，以及 §V.8，印刷在若干页上。131–132（通过伴随函子定理的 Stone–Čech 紧化，以及练习 4）：Instance/Top/StoneCech.v（§V.6 的有限情况作为一个带有其 [eq_refl] 回读的普遍算子，底层集合函子下的 GAFT 降到完备性，以及普遍算子层面的练习 4）和 Instance/Top/StoneCech/Refutations.v（[CompHaus] 和 [Top] 的完备性，以及 [CompHaus_Forget] 的伴随，对箭头索引或 [IEM] 进行反驳，通过 [Top] 的索引超过同构宇宙；空对；包含的 SAFT 降到三个假设；[big_inj]；具有稳定元素的余生成元的代价，以及单点可分空间的代价）。N2、N6-N14 和 N18-N22 重述了目标头记录的回读或拒绝，N2 和 N12 首次由 #455 的审查测量；N1、N3-N5 和 N15-N17 属于本文件自身。阳性对照独立重述了文件的主张。

导入列表，通过比较 [Require] 的各行脚本来衡量。首先是 Instance/Top/StoneCech/Refutations.v 的二十行逐字且顺序与目标 Instance/Top/StoneCech.v 相同；然后是 Instance/Top/StoneCech.v 新增的五行，按其顺序（Structure/Cone.v、Structure/Limit.v、Structure/Limit/Preservation.v、Instance/Sets/Classifier.v 以及标准库的 [PeanoNat]）；接着是目标 Refutations.v 的列表中没有的那一行自身。共二十六行，各部分无任何新增内容。Instance/Sets.v 和 Instance/Top.v 各自定义了一个 [bool_setoid_object]；在这个列表下，短名称是 Instance/Top.v 的，这是目标使用的名称，而 Instance/Sets.v 的名称是 [Sets.bool_setoid_object]（[Locate]）。更短的导入列表会导致探针无故通过。

纪律。该工具以两种方式进行了检查：因为缺失名称的反驳而被拒绝，并且该文件中每一个不是反驳的八十一条定义、示例、引理和记录，如果在该整个文件的副本中被包装成一个反驳，会在该命令处停止构建，并报告受保护的命令已被接受（八十一条中的八十一条，由一个脚本在副本上完成）。除了该工具之外的每一个否定都是 [Definition] 或 [Example]，从不为 [Check]，因此一个未绑定的 evar 或缺失的实例无法满足它。每个否定在整份文件的副本中都被去掉了反驳关键字，一次一个地进行，编译后读取其错误；二十三份副本中的每一份在被剥离的命令内部停止（通过脚本比较该命令范围前的错误所在的文件行）。记录的类型是该错误的类型，每个否定旁边都有正向控制；否定使用的每个标识符，除其自身名称及绑定器命名的宇宙之外，都会被该文件的某个正向控制使用（通过脚本对命令的标识符进行操作）。在这个完整文件的另一个副本中，每个负例后面都紧跟着一个绑定器工具，相同的宇宙绑定器、参数和返回类型，且具有一个简单的主体（返回类型的假设，或者在命令说明无时为 [Datatypes.unit]）：所有二十二个都被接受，因此每个负例都被其主体拒绝。每个宇宙负例都是顶层定义，其宇宙在其自身绑定器中声明，从不属于 [Section] 的。引用是 Rocq 9.1.1 在此文件的导入列表下的内容，错误的环境块被省略；Rocq 打印“无法统一”的括号内容，其中包含作用域内的简写名称，而一个宇宙的剥离副本按自身和一个序列号命名，写作 <1>、<2>……，在每个引用中按照首次出现的顺序重新编号。该文件也可以在 Coq 8.19.2 和 8.20.1 上编译，针对这些版本的该库预构建树，并在这些树旁边编译两个目标；在目标依赖闭包的 152 个文件（不包括目标本身）上，这些树的源文件与该树逐字节相同，唯独 Instance/Top.v 和 Instance/Top/CompHaus.v 不同，仅在注释块中有所差异（通过 [cmp] 和 [diff] 比较）。剥离副本也在那编译过，每一个在 Rocq 9.1.1 的拒绝行和字符范围上都被拒绝。根据 8.20.1，除了 N13 的错误之外，每个错误都是 Rocq 9.1.1 的错误，直到序列号（由脚本在副本上比较）；N13 的条款命名了一个生成的宇宙，而 Rocq 9.1.1 命名为 c。根据 8.19.2，有十一项是（仪器、N1-N6、N8 和 N20-N22）；N15 保持其条款，序列名代替 c 和 h，N7、N9-N11、N13、N14、N16、N18 和 N19 在原来的位置打印 "无法统一" 的括号，N12 和 N17 打印类型不匹配而不带括号。

种类。二十三个反驳，被计算为以反驳关键词开头的行：NAME-ABSENCE（工具）、CONVERSION（N1-N4）、TYPING（N5）和UNIVERSE（N6-N22）：分别为一、四、一和十七。没有拒绝是INSTANCE或BINDER的：每一个绑定工具都被接受。N15是针对整个命令报告的，而不是在子项上；它形成的类型是它的主体，并且它的绑定工具被接受。N20、N21 和 N22 没有宇宙条款：每一个都被报告为其两边仅在宇宙实例上不同的不匹配，并且在宇宙中它们的绑定器只在 [CompHaus] 指定的槽位上命名它们的段落（N20 为第四个，N21 为第三个，N22 为第十四和第十五个）；每一个其他不同的槽都是绑定器留给推断的（[_]）。

标签。引脚携带此文件的 N 编号；#455 的构建者和审核者在其他名称的临时文件中测量了其中几个，引脚在此处记录，以便目标头文件可以引用任意一个。审核者的 p1 是控制 [p455_fin_obj_bool]，它的 p2 是 N2（它的 [bool_FinEnum'] 是 [p455_bool_FinEnum_rev]），而它的 p2pos 是控制 [p455_fin_obj_bool_enum]；它的 p3 是 [p455_refutes_gaft_output]，它的 p6 是 N12，它的 p8_big_inj 是 [p455_big_inj_unsplit]，它的 p9_iff 是 [p455_compact_iff]，而它的 w1 是 [p455_saft_incl_apart]。构建者和审核者的 [TopP]、[ContHom] 和 [ContHomT] 分别是 [p455_TopP]、[p455_ContHom] 和 N6，而构建者的 [t_bool_FinEnum] 是 [p455_bool_FinEnum_bare]。对名为 v_sub_index、v_adj_refuted_IEM_above、v_gaft_shape_refuted_above 和 v_not_complete_IEM_below 的文件的复审，目前 Refutations.v 将它们记录为 [CompHaus_ArrowIndex_of_Top]、[StoneCech_adjunction_refuted_IEM_above]、[CompHaus_not_complete_IEM_above] 和 [CompHaus_not_complete_IEM_below]；其 v_saft_wp_below 是 N19，其 v_n8_at_set 为 [p455_bool_ch_bare_at_set]，其 v_ts_free 为 [p455_trivial_small_free]，其 v_n1_wrong 为 [p455_n1_wrong_value]，其 v_n2_same_space 为 [p455_n2_same_space]。后续复审的 adj14 是 N22，其 s14ctl 为 [p455_adj_above_hausdorff_at_o]。标签不是常量。

** 实例/顶端/StoneCech.v

N1，N2（转换）。[StoneCech_finite] 的通用对象是 [Discrete_CH X FX] 位于 [eq_refl]（[p455_fin_obj_at]，重述 [StoneCech_finite_obj]）。在二点集中，必须小心选择错误的值：[Bool_CH] 不是一个，因为按定义它是 [bool_setoid_object] 在 [bool_FinEnum] 时的 [Discrete_CH]，而且与它的方程被接受（[p455_fin_obj_bool]，陷阱）。N1 将通用对象与单点空间进行比较，其承载体不同：
术语“eq_refl”的类型为“arrow_obj = arrow_obj”，而预期的类型为“arrow_obj = Point_CH”（无法统一“arrow_obj”和“Point_CH”）。N2在同一集合的第二次枚举[p455_bool_FinEnum_rev]中，将其与[Discrete_CH]进行比较，[p455_bool_FinEnum_rev]的列表是反向的，其对象被形成（[p455_bool_ch_rev]）：
      术语“eq_refl”的类型为“arrow_obj = arrow_obj”，而期望的类型为“arrow_obj = Discrete_CH bool_setoid_object p455_bool_FinEnum_rev”（无法统一“arrow_obj”和“Discrete_CH bool_setoid_object p455_bool_FinEnum_rev”）。在[bool_FinEnum]处的相同语句被接受（[p455_fin_obj_bool_enum]）。两个枚举都以 [Qed] 结束，因此 N2 会拒绝任何第二次枚举，其中包括在它们之间以另一名称列出的相同列表：它表明通用对象携带的是它所构建的枚举。所比较的值是否错误属于元层面：这两个对象只有一个空间（[p455_n2_same_space]，在 [eq_refl] 上）并且仅在其紧凑性证明上有所不同，[Qed] 术语的值没有树的任何引理揭示，所以错误在于 [Qed] 背后的标准形式，而不是定理。这一段的草稿指出，反转列表不仅会使数值错误，还会使其不可转换；#455的审查只判断其为不可转换。N1在载体上被拒绝，其中没有涉及不透明性，其数值作为一个定理是错误的：[p455_n1_wrong_value] 从方程中推导出 [False]，同时将两点载体的 [true] 和 [false] 带到该点。

N3（转换）。该单元是 [sc_fin_unit X FX] 位于 [eq_refl]（[p455_fin_unit_at]，重述 [StoneCech_finite_unit]）；它不识别枚举（[p455_fin_unit_other_enum]：在 [FX] 它对于任何 [FX'] 为 [sc_fin_unit X FX']），并且在双点集合上它是 [Sets] 的恒等（[p455_fin_unit_bool_id]）。N3 将其与否定 [p455_negb_lift] 进行比较，这是同类型箭头，结束于 [Defined]，在 [true] 点与单元不同（[p455_negb_not_unit]）：
      术语“eq_refl”的类型为“arrow = arrow”，而它被期望具有类型“arrow = p455_negb_lift”（无法统一“arrow”和“p455_negb_lift”）。

N4（转换）。在紧致豪斯多夫空间 [K] 上，恒等通箭有 [K] 作为其通用对象（[p455_incl_obj_at]，重述 [CompHaus_Incl_universal_obj]）；在 [K] := [Point_CH] 时，与 [Point_CH] 的方程被接受（[p455_incl_obj_point]），在一个变量 [K] 上：
  术语“eq_refl”的类型是“arrow_obj = arrow_obj”，而预期的类型是“arrow_obj = Point_CH”（无法统一“arrow_obj”和“Point_CH”）。

N5（打字）。为什么两个目标的每一个通用箭头都被写为 [UniversalArrow (C:=Sets) ...] 或 [(C:=Top@{h o})]，并且每一个回读 [@arrow_obj Sets _ ...]：Theory/Universal/Arrow.v 的 [UniversalArrow] 在其类别之前展开其对象，所以没有 [C] 对象会被拒绝，而有了它类型会形成（[p455_ua_with_C]）：术语 "Setoid_Lift X" 的类型是 "SetoidObject"，而它被期望的类型是 "obj[?C]"。同样的拒绝也会遇到 [@arrow_obj _ _ (Setoid_Lift X) ...] 和 [UniversalArrow (KSet AI) ...]，这两个都是由 #455 的构建者和侦查者记录的（在使用此文件的导入列表的临时文件中测量）。

N6（宇宙）。StoneCech.v 的标题，原因：Top 的 Homs 宇宙，记录了一个 Prop 值的拓扑将连续映射置于点的宇宙中，并引用了本文件的 [p455_TopP]（一个带有 Prop 值开集且在点的宇宙下闭合于并集的集合点集，并且没有其他字段）和 [p455_ContHom]，二者都在 CLOSED binder [@{o}] 下被接受，因此 [p455_ContHom@{o}] 无任何约束地落在 [Type@{o}] 中。树的 [ContinuousMorphism] 在 [Type@{h}] 被接受，使用 [o < h]（[p455_conthom_at_h]）；在 [Type@{o}]，N6：
  术语“ContinuousMorphism X Y”的类型是“Type@{<1>}”，而预期的类型是“Type@{o}”（宇宙不一致：无法强制执行 <1> <= o 因为 o < <1>）。头部的引用来自一个封闭的绑定器 [@{o}]，带有相同的条款；N6 的绑定器是可扩展的，因此拒绝不是绑定器的原因。

N7（宇宙）。Instance/Top.v 中的 [Point_Hausdorff] 被单态化在一个 [Set] 载体上（[About]: [IsHausdorff@{u Set Set Set} Point_Top@{Set}]；该文件的 CORRECTION（#455）评论）。它在那里被接受（[p455_point_hausdorff_set]）；在 [Set] 之上，单点空间被 [Discrete_Hausdorff]（[p455_point_hausdorff_o]）分离，并且通过 Instance/Top.v 的宇宙通用 [Point_Compact]（[p455_point_compact_o]）是紧的，并且 [Point_CH] 的空间在 [Set < o]（[p455_point_ch_above_set]）是 [Point_Top@{o}]。[Point_Hausdorff] 在该类型，N7:
      术语 “Point_Hausdorff”的类型是 “IsHausdorff@{<1> Set Set Set} Point_Top@{Set}”，而预期类型是 “IsHausdorff@{h o o o} Point_Top@{o}”（宇宙不一致：无法强制 Set = o）。

N8（宇宙）。StoneCech.v 的头部，宇宙：没有绑定器，[bool_FinEnum] 在 [FinEnum@{Set} bool_setoid_object@{Set Set}] 中展开，"这将迫使由它构建的 [Bool_CH]，以及使用 [Bool_CH] 的反驳，进入 [Set] 载体"。重新表述为 [p455_bool_FinEnum_bare]，相同的无绑定器证明，其 [About] 读取相同（在该文件的临时副本中测量）。N8 自身在 [Set] 的主体被接受（[p455_bool_ch_bare_at_set]），因此“迫使 [Set] 载体”是被测量而非直接读取子句。它强制的比引理更窄：在 [Set] ([p455_bare_at_set]) 处被接受；在 [FinEnum bool_setoid_object@{o o}] 与 [Set < o] 处也被接受，通过转换 ([p455_bare_at_o])；并且 [CompHaus] 的一个对象在 [Set] 以上由它构造，一旦集合体在 [o] 命名 ([p455_bare_named_setoid]) 后也是如此。被拒绝的是 [Bool_CH] 自身的主体，这将集合体交给推理，从而占位符在 [Set] 处从引理的类型中被解出。带有文件的那个主体 [bool_FinEnum] 在可扩展绑定器 ([p455_bool_ch_body]) 下被接受，而 [Bool_CH] 本身位于 [Set] ([p455_bool_ch_above_set]) 之上；对于 [p455_bool_FinEnum_bare]，N8：
      术语 “(Bool_Discrete; (Discrete_Compact_of_FinEnum bool_setoid_object p455_bool_FinEnum_bare, Discrete_Hausdorff ?A))”
      的类型为 “∃ x : obj[Top], Subcategory.sobj _ CompactHausdorff_Subcategory x”，但预期类型为
      “obj[CompHaus]”（无法满足约束条件 “IsCompact (Discrete_Top bool_setoid_object) ∧ IsHausdorff (Discrete_Top ?A)” == “(λ x : obj[Top], Subcategory.sobj _ CompactHausdorff_Subcategory x) Bool_Discrete”；宇宙不一致：无法强制 Set = o）。声明了 [Set < o] 后，相同的主体会因相同的条款而被拒绝（在带有此文件导入列表的草稿文件中测量）。因此，头文件的句子对于 [Bool_CH] 依然成立，其中绑定器是承重的；引理本身可以转换为任意载体。

N9（宇宙）。StoneCech.v 的头部，（3）和宇宙：重言式解集是合法的，因为 [CompHaus] 的整个对象类型处于其自身宇宙中，而 GAFT 完备性假设的所有四个宇宙都是 h。[taut_sols] 本身不受此约束：它的索引是 [CompHaus] 对象的宇宙，其 [CompHaus_Forget] 从 [About] 开始，并且当这些对象在 h 之上的 c 时，它被接受（[p455_taut_sols_above]）。Adjunction/GAFT.v 的
[GAFT] 接受在 Hom 宇宙中索引的解集
([SolutionSet@{h dobj cobj h}])，所以
在 [CompHaus_Forget] 处带有 [taut_sols] 的 GAFT 被接受，其对象在 h 处
([p455_gaft_body]，重述 [GAFT_CompHaus_only_complete] 的主体，
以及 [p455_gaft_only_complete])，而在 [h < c] 处的 N9 在
[taut_sols] 被拒绝，其类型是一个在对象的宇宙中索引的解集，期望是一个在 h 中索引的解集：
  （宇宙不一致性：无法强制 c = h 因为 h < c）。在 h 处放置物体是 GAFT 使用同义解集所付出的代价；当物体位于 h 之上时，GAFT 将需要另一个解集，而这两个目标都没有构建这个解集。

** 实例/顶/StoneCech/反驳.v

N10（宇宙）。驳斥.v 的宇宙：索引形式
    [CompHaus_not_complete] 不在形状 s 与对象 c 之间建立任何联系，[IEM] 形式需要 [c <= s]。索引形式在 [s < c]（[p455_not_complete_index]）被接受，[IEM] 形式在 [c <= s] 和 [h <= s]（[p455_not_complete_IEM]）以及 GAFT 实例（[p455_not_complete_IEM_gaft]）被接受。[IEM] 形式在 [s < c]，N10：
      术语“comp”的类型为“Complete@{r s h c}”，但期望其类型为“Complete@{<1> s h <2>}”（宇宙不一致：无法强制 <2> = c 因为 <2> <= <3> < c）。结构/完整/Freyd.v 的 [canonical_ArrowIndex]，其中 [CompHaus_not_complete_IEM] 适用于 [CompHaus] 自身的对象，对对象及同态进行索引（[About]：[ArrowIndex@{u u0 u1}] 在 [u0 <= u] 和 [u1 <= u] 之下）。所以 N10 确定了该常数的范围，而不是 [IEM] 的作用范围：[CompHaus_ArrowIndex_of_Top] 传递 [Top] 的索引（[p455_sub_index]），[IEM] 在每个 [s] 提供一个带 [h <= s] 的索引，并且 [CompHaus_not_complete_IEM_below] 用 [h <= s]（[p455_not_complete_IEM_below]）否定了 N10 的陈述，GAFT 的形状其对象位于同态之上作为其情形 [CompHaus_not_complete_IEM_above]（[p455_not_complete_IEM_above]）。

N11（宇宙）。对于 [Top] 同样：[Top_not_complete] 在 [s < h]（[p455_top_not_complete_index]）被接受，[Top_not_complete_IEM] 在 [h <= s]（[p455_top_not_complete_IEM]）；后者在 [s < h]，N11：
      术语“comp”的类型为“Complete@{r s h h}”，而预计的类型为“Complete@{<1> <2> <3> <3>}”（宇宙不一致：无法强制 <3> = h，因为 <3> <= <2> < h）。

N12（宇宙）。[StoneCech_adjunction_refuted_IEM] 的覆盖范围：它在 [CompHaus@{h h h h ...}] 被证明，在同质宇宙中的对象，这是 [GAFT_CompHaus_only_complete] 所产生的实例（[p455_adj_refuted_IEM]，重申它，以及 [p455_refutes_gaft_output]，对 GAFT 自身输出的反驳）。在 h 之上的 c 的对象情况下，N12 在论证 [A] 中被拒绝，其类型如绑定器中所写，预计应为常量所量化的类型，在其 [CompHaus] 的对象和同质槽中有一个宇宙：
  （宇宙不一致：无法强制 c = h，因为 h < c）。索引形式达到该实例：在同域宇宙中给定箭头索引，[large_universal_arrow_refuted] 否定了与上述 h 的对象的伴随关系（[p455_adj_refuted_index_above]）。N12 固定了 [StoneCech_adjunction_refuted_IEM] 的范围，该范围将 [canonical_ArrowIndex] 应用于 [CompHaus] 自身的对象，而不是 [IEM] 的可达范围：[IEM] 通过 [Top] 提供同域宇宙的索引，而 [StoneCech_adjunction_refuted_IEM_above] 否定了 N12 的原始陈述（[p455_adj_refuted_IEM_above]）。本段草稿中提到 [IEM] 不提供这样的索引；#455 的评审测定它确实提供了，通过 [CompHaus_ArrowIndex_of_Top]。

N20-N22（宇宙）。反驳.v 的覆盖：通过 [Top] 的索引的形式仅适用于 [CompHaus] 的实例，其第三个位置，其 [Top] 的同类宇宙，为 h，其第四个位置，即证明一个空间是紧豪斯多夫的宇宙，为 c，其第十四和第十五位置，即其豪斯多夫证明中分离开集的宇宙，为点的宇宙 o。使用 [CompHaus] 逐槽写出后，当第四个槽为 c 时，[StoneCech_adjunction_refuted_IEM_above] 被接受 ([p455_adj_above_slots])；当它为 h 时，N20 在 [A] 被拒绝：
      术语 “A”的类型为 “∃ F : Sets@{h s} ⟶ CompHaus@{c h h h ...}, F ⊣ CompHaus_Forget@{...}”，而预期其类型为 “∃ F : Sets@{h s} ⟶ CompHaus@{c h h c ...}, F ⊣ CompHaus_Forget@{...}”。在 GAFT 的形状中，位于 homs 之上的 [CompHaus_not_complete_IEM_below] 被接受，当第三个槽位在 h 时（[p455_not_complete_below_slots]）；当它在 h 以下的 t 时，N21 在 [comp] 被拒绝：
  术语“comp”的类型为“@Complete@{h h h c} CompHaus@{c h t c ...}”，而预期的类型为“@Complete@{h h h c} CompHaus@{c h h c ...}”（无法统一“D ⟶ CompHaus@{c h h c ...}”和“D ⟶ CompHaus@{c h t c ...}”），
每个 [CompHaus] 的最后十一槽，以及 [CompHaus_Forget] 的实例，已省略。较老的版本则排在第三个位置
    在 h 以下，其[c <= s] 保持 （[p455_not_complete_IEM_top_slot]， at at
    c = h = s）;在 t < h < c 且形状小于 c 的实例中，也不是
    适用表格，较旧的需要[c <= s]（N10）。[StoneCech_adjunction_refuted_IEM_above]被接受为
    第十四和第十五个名额写在O位
    （[p455_adj_above_hausdorff_at_o]），o 是[Bool_CH] 和
    [Point_CH]从[Discrete_Hausdorff@{h o}]放它们;两者都位于 Q
    在O以下，伴随物的类型仍然形成（N22的结合剂）
    N22在[A]被拒绝）：
      术语“A”的类型为“∃ F ： Sets@{h s} ⟶ CompHaus@{c h h c ..."q q}, F ⊣ CompHaus_Forget@{...}"，但它预期具有类型
      "∃ F : Sets@{h s} ⟶ CompHaus@{c h h c ... o o}, F ⊣
      CompHaus_Forget@{...}",
第五到第十三个 [CompHaus] 槽，以及 [CompHaus_Forget] 的实例，省略。#455 的审查测量到相同的拒绝，无论单独的槽在 o 以下，还是每种其他形式（包括索引形式）在 o 以下，在该文件的导入列表的临时文件中都会拒绝。

N13, N14（宇宙）。反驳.v的第（3）条：在 [CompHaus_WellPowered] 的包含下解除 SAFT 的强制力度，使 [c = h] 起作用。[SAFT_CompHaus_Incl] 被重述（[p455_saft_incl]），其主体中带有分别命名的 c 和 h，并且它们之间未声明任何内容，已被接受（[p455_saft_incl_apart]；其 [About] 读取为“c = h”，在该文件的临时副本中测量）。在 [h < c]，N13 被拒绝
在 [CompHaus_WellPowered]，其类型在其他参数确定时预期为该实例：
  （宇宙不一致：无法强制 h = <1> 因为 h < c <= <1>），
在 [c < h]，N14 在达到良好幂次之前在 [comp] 被拒绝，包含的条款（N17, N19）：
  术语 “comp” 的类型为 “Complete@{s s h c}”，而预期类型为 “Complete@{s s h <1>}”（宇宙不一致：无法强制 <1> = c 因为 c < h <= <1>）。在对象宇宙中以良好验证的假设替代 [CompHaus_WellPowered] 时，在 [h < c]（[p455_saft_wp_hyp_above]）处接受 SAFT 的包含，同样它们的两个空性对（[p455_saft_vacuous]，[p455_saft_iem_vacuous]）也是如此：方程的一半 [c <= h] 属于 [CompHaus_WellPowered]，而不是 SAFT。半个 [h <= c] 是在任何完井情况下包含的：在 [c < h] 处假设完井，N19 在 [comp] 被拒绝，使用与 N14 相同的条款：
  术语“comp”的类型为“Complete@{s s h c}”，而预期的类型为“Complete@{s s h <1>}”（宇宙不一致：无法强制 <1> = c，因为 c < h <= <1>）。本段草稿将整个方程归因于 [CompHaus_WellPowered]；#455 的审查测量显示，只有 [c <= h] 是其（N19）。在物体下方的形状，通过这种良好的供能，[SAFT_Incl_IEM_vacuous_below] 仍然将 SAFT 与反驳（[p455_saft_iem_vacuous_below]）配对。

N15-N17（宇宙）。[c = h] 的每一半来自哪里。[c <= h]：
    Structure/WellPowered.v 的 [WellPowered@{o h w s t}] 声明了 [o <= s]，
    并且 [trivial_small] 在同一宇宙中修复了 s（[WellPowered@{o h h h t}]）。[CompHaus_WellPowered] 被重述（[p455_wellpowered]），
    [trivial_small] 在 [c < h]（[p455_trivial_small_below]）被接受，并且在 [h < c]（[p455_wp_type_at_c]）形成了一个以 c 索引的良好赋能类型；以 h 索引的没有，N15：
      宇宙不一致。无法强制 c <= h，因为 h < c。并且 [trivial_small] 并不驻留在索引为 c, N16 的那个对象上：
      术语 “trivial_small CompHaus” 的类型为 “WellPowered@{<1> <2> <2>
      <2> <3>} CompHaus@{...}”，而期望的类型是
      “WellPowered@{c h h c t} CompHaus@{...}”（宇宙不一致：
      无法强制 c = h 因为 h < c），
    两个 [CompHaus] 的实例被省略；在 c 和 h 未排序的情况下
    同一类型是可驻留的，当 c = h 时（[p455_trivial_small_free]，其
    [About] 读取为 “c = h”）。[h <= c]：[CompHaus_Incl]
    将其域的 hom 宇宙置于其对象之下（[About]：域是 [CompHaus@{u u0 u0 ...}]，
    在 [u0 <= u] 下）。该包含在 [h < c] ([p455_incl_above]) 被接受；在 [c < h]，N17 在 [CompHaus_Incl] 被拒绝，其类型预期为被指定的 [CompHaus]：
  （宇宙不一致：无法强制 <1> = h 因为 <1> <= <2> < h）。

N18（宇宙）。反驳.v的 (4)：[big_inj] 将其索引绑定到 [comp] 所涉及的同一类别的对象，根据局部定义 [C := CompHaus]，并且其块包含 [c <= s]。[big_inj_injective] 被重述（[p455_big_inj_injective]），并且 [big_inj] 的主体与 [obj[CompHaus]] 在两个地方都被接受于 [s < c]（[p455_big_inj_unsplit]），然后两个 [CompHaus] 分离为各自实例；[big_inj] 在 [s < c]，N18：
  术语“comp”的类型为“Complete@{r s h c}”，而预期类型为“Complete@{<1> s h <2>}”（宇宙不一致：无法强制 <2> = c，因为 <2> <= <3> < c）。

其余两个文件的控制，每个文件都在其规定的类型下重述一个常量：构造性部分 [p455_stonecech_finite]、[p455_discrete_hausdorff]、[p455_compact_iff]（离散空间的紧致性当且仅当有限可数性，两个方向在一个实例中）和 [p455_nat_not_compact]；归约 [p455_pres] 和 [p455_taut_sols]；练习 4，[p455_ex4_separated]、[p455_ex4_converse]、[p455_ex4_dec]、[p455_ex4_bool]、[p455_ex4_incl]、[p455_ex4_incl_converse]、[p455_ex4_at_CompHaus]、[p455_ex4_incl_local] 和 [p455_ex4_local_at_CompHaus]；以及元定理 [p455_large_ua_refuted]、[p455_gaft_vacuous]、[p455_gaft_vacuous_above]、[p455_cogen_dne] 和 [p455_point_sep_dne]。这里没有任何东西属于完整性条件的前提，也不属于 [p455_cogen_dne] 或 [p455_point_sep_dne] 的范围。

此处未固定。(a) 树在 [Top] 中不构建无条件二元积：配对连续性的前方的两个壁是 Test/ProbeCompHaus413.v 的 N1 和 N2。该条目的草稿指出 [Top] 在没有假设的情况下没有二元积，并且该探针固定了它；#455 的审查发现这不是一个定理（从经典意义上看 [Top] 有它们）。(b) #455 的侦察报告指出 [Section] [Context] 在 [CompHaus] 上的绑定器被拒绝：它没有为 #455 的构建者复现，且目标也没有依赖它。(c) [About] 的读回，如 [p455_bool_FinEnum_bare] 的 [Set]，[p455_saft_incl_apart] 的“c = h”，以及 [taut_sols] 的索引：在该文件的临时副本中测量，并通过其结果固定在此（N8, N13-N17 及 N9）；同样地，[CompHaus_Forget] 和 [CompHaus_Incl] 所携带的 [h <= c] 以及 Refutations.v 的 COVERAGE 名称插槽（N12, N17, N19-N22）。(d) 翻转统计（[Defined] 对抗 [Qed]）以及目标在 [Print Assumptions] 下的闭包：测量的是构建而非命令；Makefile 的 print-assumptions 门控是保存闭包的地方。一项物品 (e)，审查的 p4 和 p5，已被弃用：它们现在都是目标的常量，由 [p455_ex4_incl_local]、[p455_ex4_local_at_CompHaus] 和 [p455_point_sep_dne] 重新说明。

末尾的保护块列出了两个目标的七十四个常量的名称，因此重命名会破坏该文件：Instance/Top/StoneCech.v 中的四十一项和 Instance/Top/StoneCech/Refutations.v 中的三十三项。它们是目标的 .glob 文件中的 [def] 和 [prf] 条目，这些文件不包含任何其他类型的条目（其中没有 [abbrev]），并且正好是 [Print Module] 为每个目标列出的名称（通过 [diff] 比较）；两个目标都不使用 [Program]，因此没有义务常量。在完整导入列表下，[Locate] 正好为每一个七十四个常量列出一个对象，即目标的对象。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Complete.Freyd.
Require Import Category.Structure.WellPowered.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.CompHaus.
Require Import Category.Instance.Top.StoneCech.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.SAFT.Characterization.
Require Import Coq.Lists.List.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Sets.Classifier.
Require Import Coq.Arith.PeanoNat.
Require Import Category.Instance.Top.StoneCech.Refutations.

Generalizable All Variables.

(** ** Instrument: the refutation keyword is live / ** 工具：反驳关键词是实时的 *)

Fail Check probe455_absent_name.

(** ** N1-N5 (CONVERSION, TYPING): Instance/Top/StoneCech.v, the readbacks / ** N1-N5（转换，打字）：实例/顶部/StoneCech.v，回读 *)

(* CONTROL: [StoneCech_finite], restated at its stated type. / 控制：[StoneCech_finite]，按其指定类型重述。 *)
Definition p455_stonecech_finite@{o h +} (X : SetoidObject@{o o})
  (FX : FinEnum X) :
  UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget :=
  StoneCech_finite X FX.

(* CONTROL: [StoneCech_finite_obj] and [StoneCech_finite_unit], restated. / 控制：[StoneCech_finite_obj] 和 [StoneCech_finite_unit]，重申。 *)
Example p455_fin_obj_at@{o h +} (X : SetoidObject@{o o}) (FX : FinEnum X) :
  @arrow_obj Sets _ (Setoid_Lift@{o h} X) _ (StoneCech_finite X FX)
    = Discrete_CH X FX := eq_refl.

Example p455_fin_unit_at@{o h +} (X : SetoidObject@{o o}) (FX : FinEnum X) :
  @arrow Sets _ (Setoid_Lift@{o h} X) _ (StoneCech_finite X FX)
    = sc_fin_unit X FX := eq_refl.

(*
CONTROL: at the two-point set the universal object IS [Bool_CH], so
   [Bool_CH] is not a wrong value there; and it is [Discrete_CH] at the
   enumeration passed.

--------
控制：在两点处，通用对象是 [Bool_CH]，所以 [Bool_CH] 并不是错误的值；在传递的枚举中，它是 [Discrete_CH]。
*)
Example p455_fin_obj_bool@{o h +} :
  @arrow_obj Sets _ (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
    (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum) = Bool_CH :=
  eq_refl.

Example p455_fin_obj_bool_enum@{o h +} :
  @arrow_obj Sets _ (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
    (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum)
    = Discrete_CH bool_setoid_object@{o o} bool_FinEnum := eq_refl.

(*
CONTROL: the one-point space is an object of [CompHaus] at every
   carrier universe.

--------
控制：一点空间是每个载体宇宙中 [CompHaus] 的一个对象。
*)
Example p455_point_ch_above_set@{o +| Set < o +} :
  `1 Point_CH = Point_Top@{o} := eq_refl.

Fail Example p455_n1_fin_obj_bool_point@{o h +} :
  @arrow_obj Sets _ (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
    (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum) = Point_CH :=
  eq_refl.

(*
CONTROL: N1's value is wrong, not merely unconvertible: the equation
   carries [true] and [false] of the two-point carrier to the point.

--------
控制：N1的值错误，而不仅仅是无法转换：该方程将两点载波的[true]和[false]传递到该点。
*)
Lemma p455_n1_wrong_value@{o h +} :
  @arrow_obj Sets _ (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
    (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum) = Point_CH →
  False.
Proof.
  intro H.
  assert (E : ∀ a b : top_carrier (`1 (@arrow_obj Sets _
                 (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
                 (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum))),
              a = b).
  { rewrite H. intros [] []. reflexivity. }
  specialize (E true false). discriminate E.
Qed.

(*
CONTROL: a second enumeration of the two-point set, its list reversed,
   and the object it gives.

--------
控制：对二点集合的第二次枚举，其列表被反转，以及它所给出的对象。
*)
Lemma p455_bool_FinEnum_rev@{o +} : FinEnum bool_setoid_object@{o o}.
Proof.
  exists (false :: true :: nil). intros [|].
  - exists true. split; [right; left; reflexivity | reflexivity].
  - exists false. split; [left; reflexivity | reflexivity].
Qed.

Definition p455_bool_ch_rev@{o +} : CompHaus :=
  Discrete_CH bool_setoid_object@{o o} p455_bool_FinEnum_rev.

Fail Example p455_n2_fin_obj_other_enum@{o h +} :
  @arrow_obj Sets _ (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
    (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum)
    = Discrete_CH bool_setoid_object@{o o} p455_bool_FinEnum_rev := eq_refl.

(*
CONTROL: N2's two objects have one space; they differ in the
   compactness proof alone.

--------
控制：N2 的两个对象有一个空间；它们仅在紧性证明上有所不同。
*)
Example p455_n2_same_space@{o +} :
  `1 (Discrete_CH bool_setoid_object@{o o} bool_FinEnum)
  = `1 (Discrete_CH bool_setoid_object@{o o} p455_bool_FinEnum_rev) :=
  eq_refl.

(*
CONTROL: the unit does not see the enumeration; at the two-point set it
   IS the identity of [Sets].

--------
控制：该单元不识别枚举；在双点设置时，它是 [Sets] 的标识。
*)
Example p455_fin_unit_other_enum@{o h +} (X : SetoidObject@{o o})
  (FX FX' : FinEnum X) :
  @arrow Sets _ (Setoid_Lift@{o h} X) _ (StoneCech_finite X FX)
    = sc_fin_unit X FX' := eq_refl.

Example p455_fin_unit_bool_id@{o h +} :
  @arrow Sets _ (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
    (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum)
    = @id Sets (Setoid_Lift@{o h} bool_setoid_object@{o o}) := eq_refl.

(*
CONTROL: negation, an arrow of the unit's type that differs from the
   unit at a point.

--------
控制：否定，与单位在某一点上的类型不同的单位箭头。
*)
Definition p455_negb_lift@{o h +} :
  Setoid_Lift@{o h} bool_setoid_object@{o o} ~{Sets}~>
    CompHaus_Forget (Discrete_CH bool_setoid_object@{o o} bool_FinEnum).
Proof.
  unshelve refine {| morphism := negb |}.
  intros a b e. simpl in *. rewrite e. reflexivity.
Defined.

Lemma p455_negb_not_unit@{o h +} :
  p455_negb_lift
    ≈ @arrow Sets _ (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
        (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum) → False.
Proof. intro H. specialize (H true). simpl in H. discriminate H. Qed.

Fail Example p455_n3_fin_unit_negb@{o h +} :
  @arrow Sets _ (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
    (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum)
    = p455_negb_lift := eq_refl.

(* CONTROL: [CompHaus_Incl_universal_obj], restated, and at the point. / 控制：[CompHaus_Incl_universal_obj]，重申，并到位。 *)
Example p455_incl_obj_at@{h o +} (K : CompHaus) :
  @arrow_obj Top@{h o} _ (CompHaus_Incl K) _ (CompHaus_Incl_universal K)
    = K := eq_refl.

Example p455_incl_obj_point@{h o +} :
  @arrow_obj Top@{h o} _ (CompHaus_Incl Point_CH) _
    (CompHaus_Incl_universal Point_CH) = Point_CH := eq_refl.

Fail Example p455_n4_incl_obj_point@{h o +} (K : CompHaus) :
  @arrow_obj Top@{h o} _ (CompHaus_Incl K) _ (CompHaus_Incl_universal K)
    = Point_CH := eq_refl.

(* CONTROL: the type of a universal arrow with its category named. / 控制：具有其类别名称的通用箭头类型。 *)
Definition p455_ua_with_C@{o h +} (X : SetoidObject@{o o}) : Type :=
  UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget.

Fail Definition p455_n5_ua_without_C@{o h +} (X : SetoidObject@{o o}) :
  Type :=
  UniversalArrow (Setoid_Lift@{o h} X) CompHaus_Forget.

(** ** N6-N8 (UNIVERSE): Instance/Top/StoneCech.v, the universes / ** N6-N8（宇宙）：Instance/Top/StoneCech.v，宇宙 *)

(*
CONTROL: the header's Prop-valued topology.  A setoid with Prop-valued
   opens closed under unions indexed at the points' universe, and its
   continuous maps, at that universe, under a CLOSED binder.

--------
控制：标题的 Prop 值拓扑。一个具有 Prop 值开集的集合，关于索引于点的宇宙的并闭合，以及其连续映射，在那个宇宙下，受一个闭合绑定器约束。
*)
Record p455_TopP@{o} := {
  p455_tp_carrier :> SetoidObject@{o o};
  p455_POpen : (p455_tp_carrier → Prop) → Prop;
  p455_popen_union (I : Type@{o}) (U : I → p455_tp_carrier → Prop) :
    (∀ i, p455_POpen (U i)) → p455_POpen (fun x => exists i, U i x)%type
}.

Definition p455_ContHom@{o} (X Y : p455_TopP@{o}) : Type@{o} :=
  { f : SetoidMorphism@{o o o} X Y &
    ∀ U : Y → Prop, p455_POpen Y U → p455_POpen X (fun x => U (f x)) }.

(* CONTROL: the tree's continuous maps one universe up. / 控制：那棵树的连续映射将一个宇宙向上推进。 *)
Definition p455_conthom_at_h@{h o +| o < h +} (X Y : TopSpace@{o}) :
  Type@{h} :=
  ContinuousMorphism X Y.

Fail Definition p455_n6_conthom_at_o@{o +} (X Y : TopSpace@{o}) :
  Type@{o} :=
  ContinuousMorphism X Y.

(*
CONTROL: [Point_Hausdorff] at its [Set] carrier; the one-point space
   separated and compact above [Set], by [Discrete_Hausdorff] and by
   Instance/Top.v's [Point_Compact].

--------
控制：[Point_Hausdorff] 在其 [Set] 载体上；在 [Set] 上方由一个空格分隔和紧凑，由 [Discrete_Hausdorff] 和 Instance/Top.v 的 [Point_Compact]。
*)
Definition p455_point_hausdorff_set : IsHausdorff Point_Top@{Set} :=
  Point_Hausdorff.

Definition p455_point_hausdorff_o@{h o +| o < h +} :
  IsHausdorff@{h o o o} Point_Top@{o} :=
  Discrete_Hausdorff _.

Definition p455_point_compact_o@{o +| Set < o +} :
  IsCompact Point_Top@{o} :=
  Point_Compact.

Fail Definition p455_n7_point_hausdorff_o@{h o +| o < h +} :
  IsHausdorff@{h o o o} Point_Top@{o} :=
  Point_Hausdorff.

(*
CONTROL: [bool_FinEnum] stated without a universe binder, and its uses:
   at [Set], at [FinEnum] above [Set] by conversion, and in an object of
   [CompHaus] above [Set] once its setoid is named at that universe.

--------
控制：[bool_FinEnum] 指出没有宇宙绑定器，以及它的用途：在 [Set]， 在 [FinEnum] 之上通过转换在 [Set]，以及在 [CompHaus] 之上的一 个对象中，一旦它的集体在那个宇宙中被命名在 [Set]。
*)
Lemma p455_bool_FinEnum_bare : FinEnum bool_setoid_object.
Proof.
  exists (true :: false :: nil). intros [|].
  - exists true. split; [left; reflexivity | reflexivity].
  - exists false. split; [right; left; reflexivity | reflexivity].
Qed.

Definition p455_bare_at_set : FinEnum bool_setoid_object@{Set Set} :=
  p455_bool_FinEnum_bare.

Definition p455_bare_at_o@{o +| Set < o +} :
  FinEnum bool_setoid_object@{o o} :=
  p455_bool_FinEnum_bare.

Definition p455_bare_named_setoid@{o +| Set < o +} : CompHaus :=
  (Bool_Discrete@{o};
     (Discrete_Compact_of_FinEnum bool_setoid_object@{o o}
        p455_bool_FinEnum_bare, Discrete_Hausdorff _)).

(* CONTROL: [Bool_CH]'s body, and [Bool_CH] itself above [Set]. / 控制：[Bool_CH] 的身体，以及 [Bool_CH] 本身在 [Set] 之上。 *)
Definition p455_bool_ch_body@{o +} : CompHaus :=
  (Bool_Discrete@{o};
     (Discrete_Compact_of_FinEnum _ bool_FinEnum, Discrete_Hausdorff _)).

Example p455_bool_ch_above_set@{o +| Set < o +} :
  `1 Bool_CH = Bool_Discrete@{o} := eq_refl.

(* CONTROL: N8's own body at [Set]. / 控制：N8的自身身体在[Set]。 *)
Definition p455_bool_ch_bare_at_set : CompHaus :=
  (Bool_Discrete@{Set};
     (Discrete_Compact_of_FinEnum _ p455_bool_FinEnum_bare,
      Discrete_Hausdorff _)).

Fail Definition p455_n8_bool_ch_bare@{o +} : CompHaus :=
  (Bool_Discrete@{o};
     (Discrete_Compact_of_FinEnum _ p455_bool_FinEnum_bare,
      Discrete_Hausdorff _)).

(** ** N9 (UNIVERSE): Instance/Top/StoneCech.v, the reduction of GAFT / ** N9（宇宙）：Instance/Top/StoneCech.v，GAFT 的化简 *)

(* CONTROL: the reduction of GAFT at [CompHaus_Forget] to completeness. / 控制：将 [CompHaus_Forget] 的 GAFT 降低至完全。 *)
Definition p455_pres@{h s +} :
  @PreservesImageLimit CompHaus Sets@{h s} CompHaus_Forget :=
  CompHaus_Forget_PreservesImageLimit.

Definition p455_taut_sols@{h s +} (d : obj[Sets@{h s}]) :
  SolutionSet CompHaus_Forget d :=
  taut_sols d.

Definition p455_gaft_only_complete@{h s +}
  (comp : @Complete@{h h h h} CompHaus) :
  { F : Sets@{h s} ⟶ CompHaus & F ⊣ CompHaus_Forget } :=
  GAFT_CompHaus_only_complete comp.

(* CONTROL: [GAFT_CompHaus_only_complete]'s body, restated. / 控制：[GAFT_CompHaus_only_complete] 的身体，重述。 *)
Definition p455_gaft_body@{h s +} (comp : @Complete@{h h h h} CompHaus) :
  { F : Sets@{h s} ⟶ CompHaus & F ⊣ CompHaus_Forget } :=
  GAFT CompHaus_Forget comp CompHaus_Forget_PreservesImageLimit taut_sols.

(*
CONTROL: the tautological solution set with the objects of [CompHaus]
   above its homs.

--------
控制：带有 [CompHaus] 对象的同态上方的同义反复解集。
*)
Definition p455_taut_sols_above@{h s c +| h < c +} (d : obj[Sets@{h s}]) :
  SolutionSet (CompHaus_Forget : (CompHaus : Category@{c h h}) ⟶ Sets@{h s})
    d :=
  taut_sols d.

Fail Definition p455_n9_gaft_taut_above@{h s c +| h < c +}
  (comp : @Complete@{h h h c} CompHaus) :
  { F : Sets@{h s} ⟶ CompHaus & F ⊣ CompHaus_Forget } :=
  GAFT CompHaus_Forget comp CompHaus_Forget_PreservesImageLimit taut_sols.

(** ** Controls: the constructive pieces of Instance/Top/StoneCech.v / ** 控件：Instance/Top/StoneCech.v 的构造部分 *)

(*
CONTROL: [Discrete_Hausdorff]; compactness of a discrete space iff
   finite enumerability, at one instance; discrete ℕ not compact.

--------
控制：[Discrete_Hausdorff]；离散空间的紧性当且仅当有限可列，在某一实例；离散的ℕ不紧。
*)
Definition p455_discrete_hausdorff@{h o +| o < h +}
  (A : SetoidObject@{o o}) : IsHausdorff@{h o o o} (Discrete_Top@{o o} A) :=
  Discrete_Hausdorff A.

Definition p455_compact_iff@{o +} (A : SetoidObject@{o o}) :
  (FinEnum A → IsCompact (Discrete_Top@{o o} A))
  ∧ (IsCompact (Discrete_Top@{o o} A) → FinEnum A) :=
  (Discrete_Compact_of_FinEnum A, FinEnum_of_Discrete_Compact A).

Definition p455_nat_not_compact@{o +} :
  IsCompact (Discrete_Top@{o o} sc_nat_setoid) → False :=
  Discrete_nat_not_compact.

(* CONTROL: Exercise 4 over the underlying-set functor. / 控制：练习4 关于基础集合函子。 *)
Definition p455_ex4_separated@{o h +} (X : SetoidObject@{o o})
  (UA : UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget) :
  (∀ x y : X, (∀ (K : CompHaus)
                 (f : Setoid_Lift X ~{Sets}~> CompHaus_Forget K), f x ≈ f y)
              → x ≈ y) →
  ∀ x y : X, @arrow _ _ _ _ UA x ≈ @arrow _ _ _ _ UA y → x ≈ y :=
  unit_injective_of_separated X UA.

Definition p455_ex4_converse@{o h +} (X : SetoidObject@{o o})
  (UA : UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget) :
  (∀ x y : X, @arrow _ _ _ _ UA x ≈ @arrow _ _ _ _ UA y → x ≈ y) →
  ∀ x y : X, (∀ (K : CompHaus)
                (f : Setoid_Lift X ~{Sets}~> CompHaus_Forget K), f x ≈ f y)
             → x ≈ y :=
  separated_of_unit_injective X UA.

Definition p455_ex4_dec@{o h +} (X : SetoidObject@{o o})
  (UA : UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget)
  (dec : ∀ x y : X, (x ≈ y) + ((x ≈ y) → False)) :
  ∀ x y : X, @arrow _ _ _ _ UA x ≈ @arrow _ _ _ _ UA y → x ≈ y :=
  unit_injective_of_dec X UA dec.

Definition p455_ex4_bool@{o h +} :
  ∀ x y : bool_setoid_object@{o o},
    @arrow _ _ _ _ (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum
                    : UniversalArrow (C:=Sets)
                        (Setoid_Lift@{o h} bool_setoid_object@{o o})
                        CompHaus_Forget) x
    ≈ @arrow _ _ _ _ (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum
                      : UniversalArrow (C:=Sets)
                          (Setoid_Lift@{o h} bool_setoid_object@{o o})
                          CompHaus_Forget) y
    → x ≈ y :=
  StoneCech_finite_bool_injective.

(* CONTROL: Exercise 4 at a space, over the inclusion. / 控制：在空间上，第4项练习，超过包含。 *)
Definition p455_ex4_incl@{h o +} (K : CompHaus) (X : Top@{h o})
  (HX : KSeparated K X)
  (UA : UniversalArrow (C:=Top@{h o}) X CompHaus_Incl) :
  ∀ x y : top_carrier X,
    continuous_map (@arrow _ _ _ _ UA) x
      ≈ continuous_map (@arrow _ _ _ _ UA) y
    → x ≈ y :=
  StoneCech_unit_injective_completely_regular K X HX UA.

Definition p455_ex4_incl_converse@{h o +} (K : CompHaus)
  (sepK : ∀ (Y : CompHaus) (p q : top_carrier (`1 Y)),
            (∀ k : Y ~{CompHaus}~> K,
               continuous_map (`1 k) p ≈ continuous_map (`1 k) q) → p ≈ q)
  (X : Top@{h o}) (UA : UniversalArrow (C:=Top@{h o}) X CompHaus_Incl)
  (Hinj : ∀ x y : top_carrier X,
     continuous_map (@arrow _ _ _ _ UA) x
       ≈ continuous_map (@arrow _ _ _ _ UA) y
     → x ≈ y) :
  KSeparated K X :=
  KSeparated_of_unit_injective K sepK X UA Hinj.

Definition p455_ex4_at_CompHaus@{h o +} (K : CompHaus) :
  ∀ x y : top_carrier (CompHaus_Incl K : obj[Top@{h o}]),
    continuous_map (@arrow _ _ _ _ (CompHaus_Incl_universal K)) x
      ≈ continuous_map (@arrow _ _ _ _ (CompHaus_Incl_universal K)) y
    → x ≈ y :=
  StoneCech_unit_injective_at_CompHaus K.

Definition p455_ex4_incl_local@{h o +} (K : CompHaus) (X : Top@{h o})
  (UA : UniversalArrow (C:=Top@{h o}) X CompHaus_Incl)
  (sepK : ∀ p q : top_carrier (`1 (@arrow_obj _ _ _ _ UA)),
            (∀ k : @arrow_obj _ _ _ _ UA ~{CompHaus}~> K,
               continuous_map (`1 k) p ≈ continuous_map (`1 k) q) → p ≈ q)
  (Hinj : ∀ x y : top_carrier X,
     continuous_map (@arrow _ _ _ _ UA) x
       ≈ continuous_map (@arrow _ _ _ _ UA) y
     → x ≈ y) :
  KSeparated K X :=
  KSeparated_of_unit_injective_local K X UA sepK Hinj.

Definition p455_ex4_local_at_CompHaus@{h o +} (K : CompHaus) :
  KSeparated K (CompHaus_Incl K : obj[Top@{h o}]) :=
  KSeparated_of_unit_injective_local_at_CompHaus K.

(**
** N10-N12, N20-N22 (UNIVERSE): Instance/Top/StoneCech/Refutations.v,
       the reach of the refutations

--------
** N10-N12, N20-N22（UNIVERSE）：实例/顶/StoneCech/反驳.v，反驳的范围
*)

(*
CONTROL: completeness of [CompHaus] refuted by an index at a shape
   below its objects; by [IEM] at [c <= s] and [h <= s], and at GAFT's
   instance.

--------
控制：[CompHaus] 的完整性被其对象下方形状的索引驳回；由 [IEM] 在 [c <= s] 和 [h <= s] 处，以及在 GAFT 的实例处。
*)
Definition p455_not_complete_index@{r s c h +| s < c +}
  (AI : ArrowIndex@{s c h} CompHaus) (comp : @Complete@{r s h c} CompHaus) :
  False :=
  CompHaus_not_complete AI comp.

Definition p455_not_complete_IEM@{e r s c h +| c <= s, h <= s +}
  (E : IEM@{e}) (comp : @Complete@{r s h c} CompHaus) : False :=
  CompHaus_not_complete_IEM E comp.

Definition p455_not_complete_IEM_gaft@{e h +} (E : IEM@{e})
  (comp : @Complete@{h h h h} CompHaus) : False :=
  CompHaus_not_complete_IEM E comp.

(*
CONTROL: an arrow index of [Top] transported to [CompHaus]; through it,
   N10's statement with [h <= s] refuted under [IEM], and GAFT's shape
   with the objects above the homs.

--------
控制：将 [Top] 传输到 [CompHaus] 的箭头索引；通过它，N10 在 [IEM] 下对 [h <= s] 的陈述被驳回，以及 GAFT 的形状与上方的物体。
*)
Definition p455_sub_index@{s h o c +} (AIT : ArrowIndex@{s h h} Top@{h o}) :
  ArrowIndex@{s c h} (CompHaus : Category@{c h h}) :=
  CompHaus_ArrowIndex_of_Top AIT.

Definition p455_not_complete_IEM_below@{e r s c h +| s < c, h <= s +}
  (E : IEM@{e}) (comp : @Complete@{r s h c} CompHaus) : False :=
  CompHaus_not_complete_IEM_below E comp.

Definition p455_not_complete_IEM_above@{e h c +| h < c +} (E : IEM@{e})
  (comp : @Complete@{h h h c} (CompHaus : Category@{c h h})) : False :=
  CompHaus_not_complete_IEM_above E comp.

Fail Definition p455_n10_not_complete_IEM_below@{e r s c h +| s < c +}
  (E : IEM@{e}) (comp : @Complete@{r s h c} CompHaus) : False :=
  CompHaus_not_complete_IEM E comp.

(*
CONTROL: [CompHaus] written out slot by slot, its [Top] slot (the
   third) at the homs, its proof slot (the fourth) at the objects: the
   form through [Top]'s index at GAFT's shape above the homs; the older
   form with the [Top] slot below the homs.

--------
控制：[CompHaus] 按槽逐一写出，其 [Top] 槽（第三个）位于 homs，其 proof 槽（第四个）位于 objects：通过 [Top] 的索引在 GAFT 的 homs 上方的形状得到的形式；具有 [Top] 槽在 homs 下方的旧形式。
*)
Definition p455_not_complete_below_slots@{e h c o +| h < c +}
  (E : IEM@{e})
  (comp : @Complete@{h h h c}
            (CompHaus@{c h h c _ _ o _ _ _ _ _ _ _ _} : Category@{c h h})) :
  False :=
  CompHaus_not_complete_IEM_below@{e h h c h o _ _ _ _ _ _ _} E comp.

Definition p455_not_complete_IEM_top_slot@{e h t o +| t < h +}
  (E : IEM@{e})
  (comp : @Complete@{h h h h}
            (CompHaus@{h h t h _ _ o _ _ _ _ _ _ _ _} : Category@{h h h})) :
  False :=
  CompHaus_not_complete_IEM E comp.

Fail Definition p455_n21_below_top_slot@{e h c t o +| t < h, h < c +}
  (E : IEM@{e})
  (comp : @Complete@{h h h c}
            (CompHaus@{c h t c _ _ o _ _ _ _ _ _ _ _} : Category@{c h h})) :
  False :=
  CompHaus_not_complete_IEM_below@{e h h c h o _ _ _ _ _ _ _} E comp.

(* CONTROL: the same for [Top]. / 控制：与 [Top] 相同。 *)
Definition p455_top_not_complete_index@{r s h o +| s < h +}
  (AI : ArrowIndex@{s h h} Top@{h o}) (comp : @Complete@{r s h h} Top@{h o}) :
  False :=
  Top_not_complete AI comp.

Definition p455_top_not_complete_IEM@{e r s h o +| h <= s +} (E : IEM@{e})
  (comp : @Complete@{r s h h} Top@{h o}) : False :=
  Top_not_complete_IEM E comp.

Fail Definition p455_n11_top_not_complete_IEM_below@{e r s h o +| s < h +}
  (E : IEM@{e}) (comp : @Complete@{r s h h} Top@{h o}) : False :=
  Top_not_complete_IEM E comp.

(*
CONTROL: the adjunction refuted under [IEM], applied to GAFT's own
   output; the universal arrow at a large set refuted by an index.

--------
控制：在 [IEM] 下被驳斥的附加，应用于 GAFT 自己的输出；在一个大集合上的通用箭头被一个指标驳斥。
*)
Definition p455_adj_refuted_IEM@{e h s +} (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ CompHaus & F ⊣ CompHaus_Forget }) : False :=
  StoneCech_adjunction_refuted_IEM E A.

Definition p455_refutes_gaft_output@{e h s +} (E : IEM@{e})
  (comp : @Complete@{h h h h} CompHaus) : False :=
  StoneCech_adjunction_refuted_IEM E
    (GAFT_CompHaus_only_complete@{h s _ _ _ _ _ _ _ _} comp).

Definition p455_large_ua_refuted@{c h +} (AI : ArrowIndex@{h c h} CompHaus)
  (UA : UniversalArrow (C:=Sets) (KSet AI) CompHaus_Forget) : False :=
  large_universal_arrow_refuted AI UA.

Definition p455_gaft_vacuous@{e h s +} (E : IEM@{e})
  (comp : @Complete@{h h h h} CompHaus) :
  ({ F : Sets@{h s} ⟶ CompHaus & F ⊣ CompHaus_Forget } * False)%type :=
  GAFT_CompHaus_IEM_vacuous E comp.

(*
CONTROL: with the objects above the homs, the adjunction refuted by an
   arrow index at the hom universe.

--------
控制：在同构上的对象中，由同构宇宙中的箭头索引驳斥的结合。
*)
Definition p455_adj_refuted_index_above@{h s c +| h < c +}
  (AI : ArrowIndex@{h c h} (CompHaus : Category@{c h h}))
  (A : { F : Sets@{h s} ⟶ (CompHaus : Category@{c h h})
       & F ⊣ CompHaus_Forget }) : False :=
  large_universal_arrow_refuted AI
    (universal_arrow_of_adjunction (`2 A) (KSet AI)).

(* CONTROL: N12's statement, refuted under [IEM] through [Top]'s index. / 控制：N12 的声明，通过 [IEM] 到 [Top] 的索引被反驳。 *)
Definition p455_adj_refuted_IEM_above@{e h s c +| h < c +} (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ (CompHaus : Category@{c h h})
       & F ⊣ CompHaus_Forget }) : False :=
  StoneCech_adjunction_refuted_IEM_above E A.

Fail Definition p455_n12_adj_refuted_above@{e h s c +| h < c +}
  (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ (CompHaus : Category@{c h h})
       & F ⊣ CompHaus_Forget }) : False :=
  StoneCech_adjunction_refuted_IEM E A.

(*
CONTROL: the same slot by slot, the proof slot at the objects; and
   GAFT's route with the objects above the homs, any solution sets.

--------
控制：逐槽相同，对象处的证明槽；以及 GAFT 的路线在同调之上的对象，任何解集。
*)
Definition p455_adj_above_slots@{e h s c o +| h < c +} (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ (CompHaus@{c h h c _ _ o _ _ _ _ _ _ _ _}
                             : Category@{c h h})
       & F ⊣ CompHaus_Forget }) : False :=
  StoneCech_adjunction_refuted_IEM_above@{e h s o c _ _ _ _ _ _ _} E A.

Definition p455_gaft_vacuous_above@{e h s c +| h < c +} (E : IEM@{e})
  (comp : @Complete@{h h h c} (CompHaus : Category@{c h h}))
  (sols : ∀ d : obj[Sets@{h s}], SolutionSet CompHaus_Forget d) :
  ({ F : Sets@{h s} ⟶ (CompHaus : Category@{c h h})
     & F ⊣ CompHaus_Forget } * False)%type :=
  GAFT_CompHaus_IEM_vacuous_above E comp sols.

Fail Definition p455_n20_adj_above_proof_slot@{e h s c o +| h < c +}
  (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ (CompHaus@{c h h h _ _ o _ _ _ _ _ _ _ _}
                             : Category@{c h h})
       & F ⊣ CompHaus_Forget }) : False :=
  StoneCech_adjunction_refuted_IEM_above@{e h s o c _ _ _ _ _ _ _} E A.

(*
CONTROL: the same with the fourteenth and fifteenth slots, the
   universes of the separating opens of the Hausdorff proof, written out
   at the points' universe o.

--------
控制：与第十四和第十五插槽相同，豪斯多夫证明的分离开口的宇宙，写在点的宇宙o处。
*)
Definition p455_adj_above_hausdorff_at_o@{e h s c o +| h < c +}
  (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ (CompHaus@{c h h c _ _ o _ _ _ _ _ _ o o}
                             : Category@{c h h})
       & F ⊣ CompHaus_Forget }) : False :=
  StoneCech_adjunction_refuted_IEM_above@{e h s o c _ _ _ _ _ _ _} E A.

Fail Definition p455_n22_hausdorff_opens_below@{e h s c o q +| h < c, q < o +}
  (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ (CompHaus@{c h h c _ _ o _ _ _ _ _ _ q q}
                             : Category@{c h h})
       & F ⊣ CompHaus_Forget }) : False :=
  StoneCech_adjunction_refuted_IEM_above@{e h s o c _ _ _ _ _ _ _} E A.

(**
** N13-N17, N19 (UNIVERSE): Instance/Top/StoneCech/Refutations.v, SAFT
       at the inclusion

--------
** N13-N17, N19（宇宙）：实例/顶层/StoneCech/反驳.v，在包含处的SAFT
*)

(*
CONTROL: [SAFT_CompHaus_Incl], restated; the same body with the objects'
   universe c and the homs' h named apart and nothing declared between
   them; and SAFT at the inclusion at [h < c] with the well-powering a
   hypothesis.

--------
控制：[SAFT_CompHaus_Incl]，重述；相同的主体与对象的宇宙c以及homs的h分别命名，并且它们之间未声明任何内容；并且SAFT在[h < c]的包含处与良好供能的a假设。
*)
Definition p455_saft_incl@{s h +} (comp : @Complete@{s s h h} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl) (G : Cogenerator CompHaus) :
  { F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } :=
  SAFT_CompHaus_Incl comp cont G.

Definition p455_saft_incl_apart@{s c h +}
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl) (G : Cogenerator CompHaus) :
  { F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } :=
  SAFT_wellpowered CompHaus_Incl comp cont G CompHaus_WellPowered.

Definition p455_saft_wp_hyp_above@{s c h t +| h < c +}
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl) (G : Cogenerator CompHaus)
  (WP : WellPowered@{c h h c t} (CompHaus : Category@{c h h})) :
  { F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } :=
  SAFT_wellpowered CompHaus_Incl comp cont G WP.

(* CONTROL: the two vacuity pairs, restated. / 控制：重新陈述的两个空虚对。 *)
Definition p455_saft_vacuous@{s c h +} (AI : ArrowIndex@{s c h} CompHaus)
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl)
  (G : Cogenerator CompHaus) (WP : WellPowered CompHaus) :
  ({ F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } * False)%type :=
  SAFT_Incl_vacuous AI comp cont G WP.

Definition p455_saft_iem_vacuous@{e s c h +} (E : IEM@{e})
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl)
  (G : Cogenerator CompHaus) (WP : WellPowered CompHaus) :
  ({ F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } * False)%type :=
  SAFT_Incl_IEM_vacuous E comp cont G WP.

Definition p455_saft_iem_vacuous_below@{e s c h +| h <= s, s < c +}
  (E : IEM@{e}) (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl)
  (G : Cogenerator CompHaus) (WP : WellPowered CompHaus) :
  ({ F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } * False)%type :=
  SAFT_Incl_IEM_vacuous_below E comp cont G WP.

Fail Definition p455_n13_saft_incl_above@{s c h +| h < c +}
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl) (G : Cogenerator CompHaus) :
  { F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } :=
  SAFT_wellpowered CompHaus_Incl comp cont G CompHaus_WellPowered.

Fail Definition p455_n14_saft_incl_below@{s c h +| c < h +}
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl) (G : Cogenerator CompHaus) :
  { F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } :=
  SAFT_wellpowered CompHaus_Incl comp cont G CompHaus_WellPowered.

Fail Definition p455_n19_saft_wp_below@{s c h +| c < h +}
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl) (G : Cogenerator CompHaus)
  (WP : WellPowered CompHaus) :
  { F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } :=
  SAFT_wellpowered CompHaus_Incl comp cont G WP.

(*
CONTROL: [CompHaus_WellPowered], restated; Structure/WellPowered.v's
   [trivial_small] at [CompHaus] with its objects below its homs; the type
   of a well-powering indexed at the objects' universe, above the homs; the
   inclusion with its objects above its homs.

--------
控制：[CompHaus_WellPowered]，重述；Structure/WellPowered.v 的 [trivial_small] 在 [CompHaus] 及其同态之下的对象；一个在对象的宇宙中索引的良好赋能类型，高于同态；其对象在同态之上的包含。
*)
Definition p455_wellpowered@{c h t +} :
  WellPowered@{c h h h t} (CompHaus : Category@{c h h}) :=
  CompHaus_WellPowered.

Definition p455_trivial_small_below@{c h t +| c < h +} :
  WellPowered@{c h h h t} (CompHaus : Category@{c h h}) :=
  trivial_small CompHaus.

Definition p455_trivial_small_free@{c h t +} :
  WellPowered@{c h h c t} (CompHaus : Category@{c h h}) :=
  trivial_small CompHaus.

Definition p455_wp_type_at_c@{c h t +| h < c +} : Type :=
  WellPowered@{c h h c t} (CompHaus : Category@{c h h}).

Definition p455_incl_above@{c h +| h < c +} :=
  CompHaus_Incl : (CompHaus : Category@{c h h}) ⟶ Top.

Fail Definition p455_n15_wp_type_at_h@{c h t +| h < c +} : Type :=
  WellPowered@{c h h h t} (CompHaus : Category@{c h h}).

Fail Definition p455_n16_trivial_small_at_c@{c h t +| h < c +} :
  WellPowered@{c h h c t} (CompHaus : Category@{c h h}) :=
  trivial_small CompHaus.

Fail Definition p455_n17_incl_below@{c h +| c < h +} :=
  CompHaus_Incl : (CompHaus : Category@{c h h}) ⟶ Top.

(** ** N18 (UNIVERSE): Instance/Top/StoneCech/Refutations.v, [big_inj] / ** N18（宇宙）：实例/顶部/StoneCech/反驳.v，[big_inj] *)

(*
CONTROL: [big_inj_injective], restated; [big_inj]'s body with
   [obj[CompHaus]] written in both places, at [s < c].

--------
控制：[big_inj_injective]，重述；[big_inj]的身体上写着[obj[CompHaus]，两个地方都写着，在[s < c]。
*)
Definition p455_big_inj_injective@{r s c h +}
  (C := CompHaus : Category@{c h h})
  (comp : @Complete@{r s h c} C) (phi psi : obj[C] → bool) :
  big_inj comp phi ≈ big_inj comp psi → ∀ j, phi j = psi j :=
  big_inj_injective comp phi psi.

Definition p455_big_inj_unsplit@{r s c h +| s < c +}
  (comp : @Complete@{r s h c} (CompHaus : Category@{c h h}))
  (phi : obj[CompHaus] → bool) :=
  continuous_map
    (`1 (unique_obj
           (iprod_desc
              (complete_iprod comp (fun _ : obj[CompHaus] => Bool_CH))
              (fun j => sc_pt_bool (phi j))))) ttt.

Fail Definition p455_n18_big_inj_below@{r s c h +| s < c +}
  (comp : @Complete@{r s h c} (CompHaus : Category@{c h h}))
  (phi : obj[CompHaus] → bool) :=
  big_inj comp phi.

(* CONTROL: the cost of a cogenerator with ¬¬-stable members. / 控制：具有¬¬稳定部件的联合发电机的成本。 *)
Definition p455_cogen_dne@{k c h +} (G : Cogenerator@{k c h} CompHaus)
  (stable : ∀ j (a b : top_carrier (`1 (cog_obj G j))),
              ((a ≈ b → False) → False) → a ≈ b) :
  ∀ P : Prop, ~~P → P :=
  CompHaus_cogenerator_stable_DNE G stable.

(*
CONTROL: the cost of a single point-separating space with ¬¬-stable
   points.

--------
控制：具有¬¬-稳定点的单点分隔空间的成本。
*)
Definition p455_point_sep_dne@{c h +} (K : (CompHaus : Category@{c h h}))
  (sepK : ∀ (Y : (CompHaus : Category@{c h h})) (p q : top_carrier (`1 Y)),
            (∀ k : Y ~{CompHaus}~> K,
               continuous_map (`1 k) p ≈ continuous_map (`1 k) q) → p ≈ q)
  (stable : ∀ a b : top_carrier (`1 K), ((a ≈ b → False) → False) → a ≈ b) :
  ∀ P : Prop, ~~P → P :=
  CompHaus_point_separator_stable_DNE K sepK stable.

(** ** Guard block / ** 防守格挡 *)

(* Instance/Top/StoneCech.v: 41 names / 实例/顶部/StoneCech.v：41 个名字 *)
Check @Discrete_Hausdorff.
Check @FinEnum.
Check @Discrete_Compact_of_FinEnum.
Check @FinEnum_of_Discrete_Compact.
Check @sc_nat_setoid.
Check @sc_in_le_fold_max.
Check @nat_not_FinEnum.
Check @Discrete_nat_not_compact.
Check @bool_FinEnum.
Check @Bool_CH.
Check @Point_CH.
Check @Discrete_CH.
Check @sc_fin_unit.
Check @sc_unlift.
Check @sc_fin_ext.
Check @sc_fin_ump.
Check @StoneCech_finite.
Check @StoneCech_finite_obj.
Check @StoneCech_finite_unit.
Check @sc_pt_cone.
Check @sc_pres_pt.
Check @sc_pt_const_med.
Check @sc_pres_map.
Check @CompHaus_Forget_PreservesImageLimit.
Check @taut_sols.
Check @GAFT_CompHaus_only_complete.
Check @unit_injective_of_separated.
Check @separated_of_unit_injective.
Check @sc_chi.
Check @unit_injective_of_dec.
Check @sc_bool_dec.
Check @StoneCech_finite_bool_injective.
Check @KSeparated.
Check @StoneCech_unit_injective_completely_regular.
Check @KSeparated_of_unit_injective.
Check @KSeparated_of_unit_injective_local.
Check @CompHaus_Incl_universal.
Check @CompHaus_Incl_universal_obj.
Check @KSeparated_self.
Check @StoneCech_unit_injective_at_CompHaus.
Check @KSeparated_of_unit_injective_local_at_CompHaus.

(* Instance/Top/StoneCech/Refutations.v: 33 names / 实例/顶/StoneCech/反驳.v: 33 个名字 *)
Check @sc_pt_bool.
Check @sc_eval_pt.
Check @sc_eval_pt_resp.
Check @CompHaus_not_complete.
Check @ObjDecEq_of_IEM.
Check @CompHaus_not_complete_IEM.
Check @Top_not_complete.
Check @Top_not_complete_IEM.
Check @CompHaus_ArrowIndex_of_Top.
Check @CompHaus_not_complete_IEM_below.
Check @CompHaus_not_complete_IEM_above.
Check @KSet.
Check @sc_phi_map.
Check @large_universal_arrow_refuted.
Check @StoneCech_adjunction_refuted_IEM.
Check @StoneCech_adjunction_refuted_IEM_above.
Check @GAFT_CompHaus_IEM_vacuous.
Check @GAFT_CompHaus_IEM_vacuous_above.
Check @CompHaus_WellPowered.
Check @SAFT_CompHaus_Incl.
Check @SAFT_Incl_vacuous.
Check @SAFT_Incl_IEM_vacuous.
Check @SAFT_Incl_IEM_vacuous_below.
Check @big_inj.
Check @big_inj_injective.
Check @sc_yp_equiv.
Check @sc_yp_equiv_Equivalence.
Check @sc_YP.
Check @sc_yp_FinEnum.
Check @YP_CH.
Check @sc_yp_const.
Check @CompHaus_cogenerator_stable_DNE.
Check @CompHaus_point_separator_stable_DNE.
