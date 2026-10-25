(**
* Probe for Mac Lane V.9's Remarks 1 and 2 and Exercise 3 (issue #458)

    Pins the measured boundaries of the six files #458 adds for Mac Lane
    §V.9, book pp. 133-136 (catalog ids maclane:V.9:remark1, that Top is
    complete; maclane:V.9:remark2, that it is cocomplete; and
    maclane:V.9:ex3, products through the functor G_* a functor induces
    on categories of cones; the book numbers neither remark, and the ids
    are names, not book numbering), and for the items appended to the
    issue: Awodey §2.6 (awodey:2.6:construction-product-top), Riehl §3.1
    Example 3.1.10 (riehl:3.1:example10, the box topology a non-example),
    Riehl §3.6 Proposition 3.6.2 (riehl:3.6:prop2, the underlying-set
    functor continuous and cocontinuous) and Riehl §3.6 Example 3.6.3
    (riehl:3.6:example3, the recipe as a lemma, both halves).  The targets
    are Instance/Top/Complete.v (the initial topology [PInit], the recipe
    for limits, products, [PTop_Complete] and the book's route to it),
    with its satellites Instance/Top/Complete/ConeComma.v (Exercise 3,
    corrected to a RIGHT adjoint of G_*: (a) as printed is refuted, and
    (b)'s left adjoint exists but is the discrete one) and Instance/Top/
    Complete/Refutations.v (where completeness stops, over [PTopCat] and
    over the Type-valued [Top] below its homs); and Instance/Top/
    Cocomplete.v (the final topology [PFinal], the recipe for colimits,
    coproducts, [PTop_Cocomplete] and the book's route to it), with its
    satellites Instance/Top/Cocomplete/Refutations.v (where
    cocompleteness stops) and Instance/Top/Cocomplete/TypeValued.v (what
    is formable over the Type-valued [Top] of Instance/Top.v, and the
    three walls that stop the rest).  The positive results are over
    Instance/Top/Prop.v's Prop-valued [PTopCat], by the maintainer's
    decision of 2026-09-24 on #458.  N2-N4, N8-N14, N16-N22 and N27-N35
    restate a refusal that a target header records, measured by #458's
    builders and reviews in scratch files or in this file; N1, N5-N7,
    N15 and N23-N26 are this file's own.  The positive controls restate
    the files' claims independently.

    THE IMPORT LIST, measured by comparing [Require] lines by script.
    First Instance/Top/Complete.v's twenty-two lines verbatim and in
    order, then that file; then the seven lines Instance/Top/Complete/
    ConeComma.v adds, in its order (Structure/Terminal.v, Structure/Limit/
    Comparison.v, Instance/Cones.v, Instance/Cones/Limit.v,
    Instance/Discrete.v, Instance/One.v, Instance/Roof.v), and the
    satellite; then the six lines Instance/Top/Complete/Refutations.v
    adds (Structure/Complete/Freyd.v, Construction/Quotient.v,
    Instance/Sets/Classifier/OneLevel.v, Instance/Top.v,
    Instance/Top/CompHaus.v, Instance/Top/StoneCech/Refutations.v) and
    the satellite; then the six lines Instance/Top/Cocomplete.v adds
    (Functor/Opposite.v, Construction/Opposite.v, Structure/Limit/
    Coproduct.v, Structure/Coequalizer.v, Instance/Sets/Cocomplete.v,
    Instance/Sets/Coequalizer.v) and that file; then the one line
    Instance/Top/Cocomplete/Refutations.v adds (Construction/Product/
    Limit.v; its [From Coq Require Import Eqdep_dec] loads the module
    Instance/Top/Complete.v already requires as [Coq.Logic.Eqdep_dec],
    and it requires Instance/Top/Complete/Refutations.v, already above)
    and the satellite; then the one line Instance/Top/Cocomplete/
    TypeValued.v adds (Instance/Top/Subspace/TypeValued.v) and the
    satellite.  Forty-nine lines: the forty-six distinct [Require]s of
    the six targets and the three targets no other target requires.  A
    shorter import list is what makes a probe pass for no reason.

    DISCIPLINE.  The instrument was checked both ways: the refutation of
    an absent name is refused for that reason ("The reference
    probe458_absent_name was not found in the current environment."),
    and each of the one hundred and one definitions, examples, lemmas and
    inductives of this file that is not a refutation (eighty-one,
    seventeen, one and two), wrapped in one in a copy of this WHOLE file,
    stops the build at that command with the report that the guarded
    command had been accepted (one hundred and one of one hundred and
    one, by a script over the copies).  Every negative other than that
    instrument is a [Definition], an [Example] or an [Inductive], never a
    [Check], so that an open evar cannot satisfy it.  Each negative was
    stripped of its refutation keyword in a copy of this WHOLE file, one
    at a time, compiled, and its error read; each of the thirty-six
    copies stops inside the stripped command (by the File line that
    precedes its error, compared by a script with the command's extent).
    The kind recorded is the kind of that error, and each negative has
    positive controls beside it; every identifier a negative uses, its
    own name, the constructors it declares and the universes its binder
    names aside, is used by some positive control of this file (by a
    script over the identifiers of the commands, the guard block not
    counted).  In one further copy of this WHOLE file, each negative but
    the instrument and N17 was followed by a BINDER INSTRUMENT, the same
    universe binder, binders and return type with a hypothesis of the
    return type as its body (for N19, the same arity with no
    constructors): all thirty-four are accepted, so every negative is
    refused by its body, never by its statement.  N17 has neither binder
    nor type.  And each of the thirteen UNIVERSE negatives whose binder
    declares the constraint that separates it from a control, N1-N4,
    N8-N12, N15, N29, N31 and N32, was rewritten in one copy of this
    WHOLE file with its refutation keyword removed AND that constraint
    deleted, the "+" kept: the copy compiles, so each of the thirteen is
    refused exactly because of the declared constraint.  The separating
    constraint of N16-N20 is [o < h], which Instance/Top.v's [Top@{h o}]
    carries itself, and N24-N28, N30 and N33-N35 separate by an instance
    equation, not a constraint (N30, N33 and N34 by an explicit universe
    instance of the refutation they read).  Every UNIVERSE negative is a
    top-level command whose universes are declared in its own binder,
    never a [Section]'s, but N17, which declares none.  Quotations are
    Rocq 9.1.1's under this file's import list, with the error's
    environment block left out; Rocq prints the "cannot unify"
    parenthetical with the short names in scope, and a universe the
    stripped copy names after itself and a serial number is written <1>,
    <2>, ..., numbered afresh in each quotation in order of first
    appearance.  Under this import list the file's dependency closure is
    one hundred and eighty-two [Category] modules ([Print Libraries]),
    the six targets among them.  The file also compiles on Coq 8.19.2 and
    8.20.1, with no warning, against the prebuilt trees of this library
    for those versions: of their one thousand and seventy-two sources, one
    thousand and sixty-three are this tree's byte for byte and the other
    nine, the master files #458 corrects, differ from it in comments only
    (compared by script, comments and white space removed), and the six
    targets were compiled beside them from this tree.  The stripped copies
    were compiled there as well, and every one of the thirty-six is
    refused on both at the File line of its Rocq 9.1.1 refusal.  Under
    8.20.1 every error is the Rocq 9.1.1 one up to the serial names; under
    8.19.2 twelve are, and the other twenty-four, all UNIVERSE, print the
    same type mismatch with a "cannot unify" clause between universe
    instances in place of the inconsistency (N2-N4, N8-N12, N24-N28, N31,
    N32, N35), with no clause (N1, N15, N18, N29), or the same
    inconsistency between serial names (N19, N30, N33, N34) (compared by a
    script over the copies).

    KINDS.  Thirty-six refutations, counted as the lines that open with
    the refutation keyword: NAME-ABSENCE (the instrument), UNIVERSE (N1-N4,
    N8-N12, N15-N20, N24-N35), CONVERSION (N5, N13, N14) and TYPING (N6,
    N7, N21-N23): one, twenty-seven, three and five.  No refusal is a
    BINDER one: every binder instrument is accepted.  None is an INSTANCE
    or a SECTION-VARIABLE refusal.  N21 and N22 are the elimination rule
    for propositions: a proof of a [Prop] builds only proofs.  N29 is an
    encoding artifact, pinned as one, not a wall: see its paragraph.

    LABELS.  The pins carry the N-numbers of this file; #458's builders
    and reviews measured most of them in scratch files under other names,
    recorded here so that the target headers can cite either; a review
    is named after the builder whose half it reviewed.  Builder B's walls
    file: its W1 is N16, its W1free N17, its W2 (the relation
    [tcolim_rel]) N19, its [tcolim_relH_at_o] N20, its W3 N21 and its
    W3squash N22; its controls [W1ctl_coprod], [W1ctl_coeq],
    [tcolim_relH], [tcolim_prel], [tcolim_prel_at_o] and
    [tcolim_med_respects_squashed] are [p458_top_coproducts_small],
    [p458_top_coequalizers], [p458_tcolim_relH], [p458_tcolim_prel],
    [p458_tcolim_prel_at_o] and [p458_tcolim_med_squashed].  Builder B's
    bounds file: its B1 is N10, its B2 N11, its B2r N12, its B8 N18 and
    its B10 N27; its B1ctl, B1below, B3, B4, B5, B6, B9 and B11 are
    [p458_cocomplete_at_points], [p458_cocomplete_below],
    [p458_cocomplete_points_at_set], [p458_not_cocomplete_points_at_set],
    [p458_corecipe_above], [p458_pforget_copreserves_above],
    [p458_icoprod_at_points] and [p458_cocomplete_record_above].  Builder
    B's routes file: its [routes_points] is N13, its [routes_apex] N14 and
    its [routes_carrier] [p458_cocomplete_routes_carrier].  Builder A's
    boundary table, re-measured in its review's boundary file: that
    file's d4 and d4b (annotated and free) are N2, its d1v N3, its d3v N4
    and its d3c N8; its d1, d1c, d2, d3 and d4n are
    [p458_complete_below], [p458_complete_via_cones_below],
    [p458_complete_at_set], [p458_complete_record_above] and
    [p458_not_complete_above]; builder A's "refused at s > o" for the
    cone route is N9.  The review's comparison file's [cone_eq] is
    [p458_via_cones_cone].  The second review's transport files: its
    [cm_rebuild] is the target's [top_rebuild] and its [TAI_rebuild]
    [Top_ArrowIndex_transport]; its rebuild with the field passed through,
    refused under a closed binder with no "+" ("Universe constraints are
    not implied by the ones declared: h1 = h2", re-measured under this
    file's import list), is the artifact N29 pins at [h1 < h2]; its
    [Top_not_complete_IEM_transported], [Top_iprod_refuted_IEM_below_h],
    [Top_not_cocomplete_ObjDecEq_try] and
    [CompHaus_not_complete_IEM_between_try] are the targets'
    [Top_not_complete_below_IEM], [Top_iprod_refuted_below_IEM],
    [Top_not_cocomplete_ObjDecEq] and [CompHaus_not_complete_below_IEM].
    The labels are not constants: each refutation carries its own in a
    comment on the line above it, the instrument's reading "The
    instrument".

    ** Instance/Top/Complete.v

    Controls of the initial topology.  [PInit]'s index universe is free:
    it and its opens' readback are stated under the CLOSED binder
    [@{o i}] ([p458_pinit], [p458_pinit_open]); its universal property
    over ARBITRARY spaces mapping in ([p458_pinit_universal]); along one
    map it has the opens of Instance/Top/Subspace.v's [PSub]
    ([p458_pinit_one_psub]).  The recipe, Riehl's Example 3.6.3 for
    limits, at a shape universe ABOVE the points, [o < j], the consumed
    and produced limit properties at independent universes
    ([p458_recipe_above]); its mediator IS the [Sets] one, at [eq_refl]
    ([p458_recipe_med_map]); Riehl's "must", the opens of ANY limiting
    cone ([p458_topology_forced]).  [PForget] is continuous
    ([p458_pforget_continuous]) and preserves the limits of shapes above
    the points ([p458_pforget_preserves_above]).

    N1 (UNIVERSE).  Instance/Top/Complete.v's header, WHAT IS HERE:
    [PTop_HasIndexedProducts] builds products "at every index universe
    at or below [o]".  At the points' universe and strictly below it
    they are formed ([p458_iprod_at_points], [p458_iprod_below]);
    indexed strictly above, at the class [HasIndexedProducts@{s s s s so
    o}] that Instance/Top/Complete/Refutations.v's
    [PTop_iprod_refuted_IEM] refutes under [IEM], N1:
      The term "PTop_HasIndexedProducts" has type
      "HasIndexedProducts@{<1> <1> <1> <2> <3> <2>} PTopCat@{<2> <3>}"
      while it is expected to have type "HasIndexedProducts@{s s s s so
      o} PTopCat@{o so}" (universe inconsistency: Cannot enforce s = o
      because o < s).
    The product IS the product topology at [eq_refl] ([p458_product_obj],
    [p458_pprod_open]), and the topology of ANY indexed product is the
    initial one ([p458_iprod_topology_forced]) and of ANY equalizer the
    subspace topology along its arrow ([p458_equalizer_topology_forced],
    restating [PTop_equalizer_open_iff_PSub]): the reviewer's "products
    must carry the initial topology and equalizers the subspace
    topology".

    N2 (UNIVERSE).  The same header, UNIVERSES: [PTop_Complete] is
    accepted at a shape universe [s < o], at [s := Set] and at a limit
    record [r > o], and refused above the points.  Restated at [s = o],
    at [s < o], at [Set] with [Set < o], with the points themselves at
    [Set], and with the record above the points
    ([p458_complete_at_points], [p458_complete_below],
    [p458_complete_at_set], [p458_complete_points_at_set],
    [p458_complete_record_above]); at [o < s], N2:
      The term "PTop_Complete" has type "Complete@{<1> <2> <3> <4>}"
      while it is expected to have type "Complete@{r s o so}" (universe
      inconsistency: Cannot enforce o = <3> because o < s <= <3>).
    Its limit is the initial topology on the [Sets] limit, at [eq_refl]
    ([p458_complete_apex]).

    N3, N4 (UNIVERSE).  The same paragraph: the book's route
    [PTop_Complete_via_products] is accepted only at [s = o] and [r = o].
    It IS #416's [Complete_from_products_equalizers] at the products and
    #457's [PTop_HasEqualizers], at [eq_refl]
    ([p458_complete_via_products], [p458_via_products_is_book_route]); at
    [s < o], N3:
      The term "PTop_Complete_via_products" has type "Complete@{<1> <1>
      <1> <2>}" while it is expected to have type "Complete@{o s o so}"
      (universe inconsistency: Cannot enforce o = s because s < o).
    and at [r > o], N4:
      The term "PTop_Complete_via_products" has type "Complete@{o o o
      so}" while it is expected to have type "Complete@{r o o so}"
      (universe inconsistency: Cannot enforce o = r because o < r).

    N5 (CONVERSION).  The two routes' apexes are isomorphic
    ([p458_complete_routes_iso]) and the book route's is a subspace of a
    product space ([p458_via_products_apex]); unlike the colimit routes
    (N13), their points' underlying types are not equal at [eq_refl], N5:
      The term "eq_refl" has type "vertex_obj[PTop_Complete J T] =
      vertex_obj[PTop_Complete J T]" while it is expected to have type
      "vertex_obj[PTop_Complete J T] = vertex_obj[PTop_Complete_via_products
      J T]" (cannot unify "carrier vertex_obj[PTop_Complete J T]" and
      "carrier vertex_obj[PTop_Complete_via_products J T]").
    Rocq prints the equation with the coercions [carrier] and
    [pt_carrier] elided, and the parenthetical with [pt_carrier] elided.
    The direct route's points are those of Instance/Sets/Complete.v's
    limit, the book route's those of a [Sets] equalizer of two maps out
    of the product over the shape's objects.

    Controls of Awodey and Riehl.  Awodey's description of the binary
    product's opens as unions of boxes ([p458_ppair_open_iff_box]) and
    the cartesian structure ([p458_cartesian]); the box space on the
    nat-indexed power of [PBool] is not an indexed product
    ([p458_box_not_product], [box_not_indexed_product] at the index
    type's [Nat.eq_dec]), the product topology does mediate
    ([p458_box_mediator]), and the box-open [pbox_all_false] is not
    product-open ([p458_box_strictly_finer]).

    ** Instance/Top/Complete/ConeComma.v

    N6 (TYPING).  The header, THE PRINTED STATEMENT, CORRECTED: Exercise
    3(a) holds with a RIGHT adjoint of G_*.  G_*'s object action is
    [FCone] at [eq_refl] ([p458_coneimage_obj]), and the corrected (a) is
    restated at its type, for any [G], [T] and shape ([p458_ex3a_right]);
    the same lemma given a LEFT adjoint of G_*, the printed premise, N6:
      The term "A" has type "F ⊣ ConeImage G T" while it is expected to
      have type "ConeImage G T ⊣ F".
    The lemma's shape is the correction: G_* on the left of [⊣].

    N7 (TYPING).  The same paragraph: at [PForget] G_* has BOTH adjoints.
    The right one is the weakest topology ([p458_pinitcone_obj], at
    [eq_refl]), and (a) at it IS [PTop_limit_via_cones] at [eq_refl]
    ([p458_limit_via_right], [p458_limit_via_right_is]); the left one, the
    discrete topology, exists ([p458_left_adjoint_at_pforget]) and does
    not fit the lemma, N7:
      The term "pdisc_cone_adjunction T" has type "PDiscCone T ⊣
      ConeImage PForget T" while it is expected to have type "ConeImage
      PForget T ⊣ PDiscCone T".
    So (b)'s left adjoint exists but is the discrete one, and it does
    not construct the weakest topology.

    N8, N9 (UNIVERSE).  The same header, UNIVERSES:
    [PTop_Complete_via_cones] carries the equation [r = o] and the bound
    [s <= o].  It is accepted strictly below the points and at them
    ([p458_complete_via_cones_below], [p458_complete_via_cones_at_points]);
    with the record above the points, N8:
      The term "PTop_Complete_via_cones" has type "Complete@{o o o so}"
      while it is expected to have type "Complete@{r o o so}" (universe
      inconsistency: Cannot enforce o = r because o < r).
    and with the shape above them, N9:
      The term "PTop_Complete_via_cones" has type "Complete@{<1> <2> <1>
      <3>}" while it is expected to have type "Complete@{s s o so}"
      (universe inconsistency: Cannot enforce o = <1> because o < s <=
      <1>).
    Its whole limit cone, not only the apex the header's
    [PTop_via_cones_apex] compares, IS [PTop_Complete]'s at [eq_refl]:
    the target's [PTop_via_cones_cone], restated independently
    ([p458_via_cones_cone], builder A's review's measurement) and at its
    own type ([p458_via_cones_cone_is]); Exercise 3(c)'s products at
    their type ([p458_products_via_cone_comma]).

    ** Instance/Top/Cocomplete.v

    Controls of the final topology.  [PFinal]'s index universe is free
    and its opens read back at [eq_refl], under the CLOSED binder [@{o i}]
    ([p458_pfinal], [p458_pfinal_open]); its universal property over
    ARBITRARY spaces mapping out ([p458_pfinal_universal]); along one map
    it has the opens of Instance/Top/Subspace.v's [PQuot]
    ([p458_pfinal_one_pquot]).  The colimit recipe at a shape universe
    ABOVE the points, the two colimit properties at independent levels
    ([p458_corecipe_above]); the direct colimit's apex at [eq_refl]
    ([p458_pcolimit_apex]); the triangle of its mediator on the nose, at
    [eq_refl], restated independently ([p458_pcolimit_med_at]) and as the
    target's [PColimit_med_at] at its type ([p458_pcolimit_med_at_is]);
    the header's STRENGTHS records that it holds because
    [pfinal_cocone_colimiting] ends [Defined]; Riehl's "must" for colimits
    ([p458_colimit_open_iff_final]).  [PForget] is cocontinuous
    ([p458_pforget_cocontinuous]) and preserves the colimits of shapes
    above the points ([p458_pforget_copreserves_above]).

    N10 (UNIVERSE).  The header, UNIVERSES: [PTop_Cocomplete] is
    accepted with the record above the points, at [s < o] and with the
    points at [Set], and refused at [o < s].  Restated at the points,
    below them, at [Set] and with the record above
    ([p458_cocomplete_at_points], [p458_cocomplete_below],
    [p458_cocomplete_points_at_set], [p458_cocomplete_record_above]); at
    [o < s], N10:
      The term "PTop_Cocomplete" has type "Cocomplete@{<1> <2> <3> <4>}"
      while it is expected to have type "Cocomplete@{r s o so}" (universe
      inconsistency: Cannot enforce o = <3> because o < s <= <3>).

    N11, N12 (UNIVERSE).  The same paragraph: the book's route
    [PTop_Cocomplete_via_coproducts] is [Cocomplete@{o o o so}] only.  It
    IS #416's [Cocomplete_from_coproducts_coequalizers] at the coproducts
    and #457's [PTop_HasCoequalizers], at [eq_refl]
    ([p458_cocomplete_via_coeq], [p458_via_coeq_is_book_route]); at
    [s < o], N11:
      The term "PTop_Cocomplete_via_coproducts" has type
      "Cocomplete@{<1> <1> <1> <2>}" while it is expected to have type
      "Cocomplete@{o s o so}" (universe inconsistency: Cannot enforce
      o = s because s < o).
    and at [r > o], N12:
      The term "PTop_Cocomplete_via_coproducts" has type
      "Cocomplete@{o o o so}" while it is expected to have type
      "Cocomplete@{r o o so}" (universe inconsistency: Cannot enforce
      o = r because o < r).

    N13, N14 (CONVERSION).  The same header, STRENGTHS: the two routes'
    apexes are isomorphic ([p458_cocomplete_routes_iso]) and their
    points' underlying types are equal at [eq_refl]
    ([p458_cocomplete_routes_carrier]); the point setoids are not, N13:
      The term "eq_refl" has type "colimit_apex (PTop_Cocomplete D F) =
      colimit_apex (PTop_Cocomplete D F)" while it is expected to have
      type "colimit_apex (PTop_Cocomplete D F) = colimit_apex
      (PTop_Cocomplete_via_coproducts D F)" (cannot unify "pt_carrier
      (colimit_apex (PTop_Cocomplete D F))" and "pt_carrier (colimit_apex
      (PTop_Cocomplete_via_coproducts D F))").
    and neither are the two spaces, N14, the same message with the
    parenthetical (cannot unify "colimit_apex (PTop_Cocomplete D F)" and
    "colimit_apex (PTop_Cocomplete_via_coproducts D F)").  Rocq prints
    N13's equation of point setoids with the coercion [pt_carrier]
    elided, so the two quotations differ only in the parenthetical.  The
    setoids' equalities differ, the header records: [colim_rel] against
    the equivalence a [Sets] coequalizer generates.

    N15 (UNIVERSE).  The same header, UNIVERSES: the coproducts'
    index universe sits at or below the points'.  The coproduct's opens
    at [eq_refl] ([p458_psigma_open]) and coproducts indexed at the
    points' universe ([p458_icoprod_at_points]); indexed strictly above,
    N15:
      The term "PTop_HasIndexedCoproducts" has type
      "HasIndexedCoproducts@{<1> <2> <3> <4> <3>} PTopCat@{<3> <4>}"
      while it is expected to have type "HasIndexedCoproducts@{u s s so
      o} PTopCat@{o so}" (universe inconsistency: Cannot enforce s = o
      because o < s).
    The non-vacuity witness's injections differ
    ([p458_sum_injections_differ]).

    ** Instance/Top/Cocomplete/TypeValued.v

    N16-N18 (UNIVERSE).  The header, THE WALLS, W1: the book's route over
    [Top] is refused, annotated and with every universe left to
    inference, and the coproducts read at an index universe [h] are
    refused the same way.  The two ingredients are formed alone
    ([p458_top_coproducts_small], [p458_top_coequalizers]) and the
    coequalizer IS the quotient topology on the [Sets] coequalizer at
    [eq_refl] ([p458_top_coequalizer_obj]); the route annotated
    [@{o h +| o < h +}], N16, and free, N17, each:
      The term "Top_HasIndexedCoproducts_small" has type
      "HasIndexedCoproducts@{<1> <2> <3> <3> <3>} Top@{<3> <4>}" while it
      is expected to have type "HasIndexedCoproducts@{<5> <6> <6> <7>
      <6>} ?C" (universe inconsistency: Cannot enforce <2> = <7> because
      <2> <= <4> < <7>).
    [<4>] is the points' universe of that [Top] and [<7>] its hom
    universe.  At an index universe [h], N18:
      The term "Top_HasIndexedCoproducts_small" has type
      "HasIndexedCoproducts@{<1> <2> <3> <3> <3>} Top@{<3> <4>}" while it
      is expected to have type "HasIndexedCoproducts@{u h h h h} Top@{h
      o}" (universe inconsistency: Cannot enforce <2> = h because <2> <=
      <4> < h).

    N19, N20 (UNIVERSE).  W2: Instance/Sets/Cocomplete.v's [colim_rel],
    restated for a diagram in [Top@{h o}] over a shape at or below the
    points ([p458_tcarr], the points of the colimit at [Type@{o}]), is
    refused as a relation at [Type@{o}], N19:
      Universe inconsistency. Cannot enforce h <= o because o < h.
    The same inductive valued at [Type@{h}] is formed
    ([p458_tcolim_relH]); read as a relation at [Type@{o}], N20:
      The term "p458_tcolim_relH D F" has type "p458_tcarr@{o h s} D F →
      p458_tcarr@{o h s} D F → Type@{h}" while it is expected to have
      type "p458_tcarr@{o h s} D F → p458_tcarr@{o h s} D F → Type@{o}"
      (universe inconsistency: Cannot enforce h <= o because o < h).
    N19's arity is formed (its binder instrument, with no constructors,
    is accepted): the glue constructor, quantifying over the arrows of
    the shape at [h], is what is refused.

    N21, N22 (TYPING).  W3: the relation valued in [Prop] is formed and
    read at [Type@{o}] ([p458_tcolim_prel], [p458_tcolim_prel_at_o]); the
    mediator respects it up to [inhabited] ([p458_tcolim_med_squashed]),
    and a squash eliminates into a proposition ([p458_squash_prop]).
    Eliminating the relation into the Type-valued [≈] of an apex, N21:
      Incorrect elimination of "H" in the inductive type
      "p458_tcolim_prel": the return type has sort "Type" while it should
      be SProp or Prop. Elimination of an inductive object of sort Prop
      is not allowed on a predicate in sort "Type" because proofs can be
      eliminated only to build proofs.
    and unwrapping the squash, N22, the same message for "w" in the
    inductive type "inhabited".  N21's branches are holes; its refusal
    is the elimination's, not theirs.

    ** REFUTATION CONSTANTS

    The constants of Instance/Top/Complete/Refutations.v and
    Instance/Top/Cocomplete/Refutations.v, and the [ex3_*] and [Ex3a_*]
    pieces of Instance/Top/Complete/ConeComma.v's refutation of the
    printed Exercise 3(a), are named only in the two sections of that
    name below and in the guard block, so that renaming them touches
    those places and, of this header, the paragraphs LABELS, N1 and
    N23-N35.

    N23 (TYPING).  ConeComma.v's header: the printed (a) is refuted at
    the empty shape into [Roof] ([p458_ex3a_literal_refuted], restating
    [ex3a_left_adjoint_literal_refuted]), by three facts about the same
    [G] and [T] ([p458_ex3a_counterexample]): a left adjoint of G_*
    ([p458_ex3_left_adj]), a limit of [G ◯ T] ([p458_ex3_point_limit])
    and no limit of [T].  The refutation holds under a CLOSED binder
    naming its eleven universes, every one of them declared strictly
    above [Set] ([p458_ex3a_literal_above_set]): the counterexample's
    hom universe is not pinned to [Set].  The left adjunction fed to the
    corrected (a), N23:
      The term "ex3_left_adj" has type "ex3_LeftAdj ⊣ ConeImage ex3_G1
      ex3_T0" while it is expected to have type "ConeImage ex3_G1 ex3_T0
      ⊣ ex3_LeftAdj".
    So the counterexample does not touch the corrected lemma.

    N24, N25 (UNIVERSE).  Instance/Top/Complete/Refutations.v's header,
    THE BOUNDARY.  Completeness and products are refuted above the points
    under [IEM] ([p458_not_complete_above], [p458_iprod_refuted_above]),
    and no arrow index exists at or below them, constructively
    ([p458_no_arrow_index_below]); the two refutations read at the
    points' universe, where [PTop_Complete] and [PTop_HasIndexedProducts]
    hold, N24:
      The term "PTop_not_complete_IEM" has type "IEM@{e} → ¬
      Complete@{<1> <2> <3> <4>}" while it is expected to have type
      "IEM@{e} → ¬ Complete@{r o o so}" (universe inconsistency: Cannot
      enforce <3> = o because <3> < o).
    and N25:
      The term "PTop_iprod_refuted_IEM" has type "IEM@{e} → ¬
      HasIndexedProducts@{<1> <1> <1> <1> <2> <3>} PTopCat@{<3> <2>}"
      while it is expected to have type "IEM@{e} → ¬
      HasIndexedProducts@{o o o o so o} PTopCat@{o so}" (universe
      inconsistency: Cannot enforce o = <3> because <3> < o).

    N26 (UNIVERSE).  The same header: [Top_iprod_refuted_IEM_canonical]
    refutes the Type-valued [Top]'s products at its hom universe
    ([p458_top_iprod_refuted]); the class indexed at the points' universe
    is formed (N26's binder instrument) and the canonical refutation does
    not reach it, N26:
      The term "Top_iprod_refuted_IEM_canonical" has type "IEM@{e} → ¬
      HasIndexedProducts@{<1> <1> <1> <1> <2> <2>} Top@{<2> <3>}" while
      it is expected to have type "IEM@{e} → ¬ HasIndexedProducts@{o o o
      h h h} Top@{h o}" (universe inconsistency: Cannot enforce o = h
      because o < h).
    Nor does [Top_iprod_refuted_below_IEM] (N33).  Products of [Top] at
    index universes at or below its points are neither built nor
    refuted: that is the formability boundary pinned.

    N27 (UNIVERSE).  Instance/Top/Cocomplete/Refutations.v's header, THE
    BOUNDARY: cocompleteness is refuted above the points under [IEM],
    with the points at [Set] as well ([p458_not_cocomplete_above],
    [p458_not_cocomplete_points_at_set]), and so is that of [Sets] and of
    [Top] ([p458_sets_not_cocomplete_above],
    [p458_top_not_cocomplete_above]); read at a shape universe equal to
    the points', N27:
      The term "PTop_not_cocomplete_IEM" has type "IEM@{e} → ¬
      Cocomplete@{<1> <2> <3> <4>}" while it is expected to have type
      "IEM@{e} → ¬ Cocomplete@{r o o so}" (universe inconsistency: Cannot
      enforce <3> = o because <3> < o).

    N28 (UNIVERSE).  The same header, THE BOUNDARY: under decidable
    equality of spaces cocompleteness of [PTopCat] is refuted with the
    points at [Set] by Freyd's argument through the transport
    ([p458_not_cocomplete_objdeceq_at_set]), and by Cantor's only with
    the points above [Set] ([p458_cantor_objdeceq_above_set]); Cantor's
    read at [o := Set], N28:
      The term "PTop_not_cocomplete_Cantor_ObjDecEq" has type
      "ObjDecEq@{<1> <2>} PTopCat@{<2> <1>} → ¬ Cocomplete@{<3> <4>
      <2> <1>}" while it is expected to have type "ObjDecEq@{so Set}
      PTopCat@{Set so} → ¬ Cocomplete@{r s Set so}" (universe
      inconsistency: Cannot enforce Set = <2> because Set < <2>).
    The bound is the separator's, [pcc_Prop] at [Set+1], a property of
    that proof route and not of the refuted statement.

    N29 (UNIVERSE; an encoding artifact, not a wall).
    Instance/Top/Complete/Refutations.v's header, WHAT IS HERE: a
    continuous map of [Top@{h1 o}] is rebuilt as one of [Top@{h2 o}],
    the continuity field eta-expanded, at [h1 < h2]
    ([p458_top_rebuild_up], [top_rebuild]); the field passed through
    unexpanded is accepted where the two hom universes are one
    ([p458_top_rebuild_unexpanded_at_h]), and at [h1 < h2], N29:
      The term "{| continuous_map := f; continuity := continuity f |}"
      has type "ContinuousMorphism@{h1 o} X Y" while it is expected to
      have type "ContinuousMorphism@{h2 o} X Y" (universe inconsistency:
      Cannot enforce h1 = h2 because h1 < h2).
    Elaboration unifies the two continuity types first-order and adds
    [h1 = h2]: with the separating [h1 < h2] deleted the same record is
    accepted, and under [@{o h1 h2 | o < h1, o < h2 +}] it reads back
    with that equation ([About], in a scratch file carrying this file's
    import list).  The hom universes of
    [Top] are NOT walled off from each other: an arrow index moves up
    and down between them ([p458_top_transport_up],
    [p458_top_transport_down], [Top_ArrowIndex_transport]).
    N29 pins elaborator behaviour, not a library boundary: a future
    Rocq that unfolds before unifying would accept the command, which
    would mean the artifact is gone, not that a wall moved.

    N30, N31 (UNIVERSE).  The same header, THE BOUNDARY: completeness of
    [Top] is refuted under [IEM] at a shape universe strictly between the
    points and the homs ([p458_top_not_complete_below]) and under
    [ObjDecEq] with the points at [Set]
    ([p458_top_not_complete_below_at_set]); #455's
    [Top_not_complete_IEM] refutes it at and above the homs
    ([p458_top_not_complete_canonical]).  The first read at [s := o], by
    its universe instance, N30:
      Universe inconsistency. Cannot enforce o < o because o = o.
    and #455's read at [o < s < h], N31:
      The term "Top_not_complete_IEM" has type "IEM@{e} → ¬
      Complete@{<1> <2> <3> <3>}" while it is expected to have type
      "IEM@{e} → ¬ Complete@{r s h h}" (universe inconsistency: Cannot
      enforce <3> = h because <3> <= <2> < h).
    So the [_below] form reaches strictly more shapes than #455's, and
    no refutation reaches the shapes at or below the points.

    N32 (UNIVERSE).  The same paragraph, and Instance/Top/CompHaus.v's
    CORRECTION (#458): completeness of [CompHaus] is refuted under [IEM]
    at a shape universe strictly between the points and the homs
    ([p458_comphaus_not_complete_below]), #455's
    [CompHaus_not_complete_IEM_below] at and above the homs
    ([p458_comphaus_not_complete_canonical]); #455's read at
    [o < s < h], N32:
      The term "CompHaus_not_complete_IEM_below" has type "IEM@{e} → ¬
      Complete@{<1> <2> <3> <4>}" while it is expected to have type
      "IEM@{e} → ¬ Complete@{r s h c}" (universe inconsistency: Cannot
      enforce <3> = h because <3> <= <2> < h).

    N33 (UNIVERSE).  The same header: products of [Top] are refuted under
    [IEM] at an index universe strictly between the points and the homs,
    at the reading [HasIndexedProducts@{s s s h h h}]
    ([p458_top_iprod_refuted_below]); read at the index universe [o], by
    its universe instance, N33:
      Universe inconsistency. Cannot enforce o < o because o = o.

    N34, N35 (UNIVERSE).  Instance/Top/Cocomplete/Refutations.v's header,
    THE BOUNDARY: cocompleteness of [Top] is refuted under [IEM] at a
    shape universe strictly between the points and the homs, by Freyd's
    argument through the transport and by Cantor's
    ([p458_top_not_cocomplete_between], [p458_top_not_cocomplete_cantor]),
    and under [ObjDecEq] with the points at [Set] by Freyd's
    ([p458_top_not_cocomplete_at_set]), by Cantor's only above [Set]
    ([p458_top_cantor_objdeceq_above_set]).  The Freyd [IEM] form read at
    [s := o], by its universe instance, N34:
      Universe inconsistency. Cannot enforce o < o because o = o.
    and Cantor's [ObjDecEq] form read at [o := Set], N35:
      The term "Top_not_cocomplete_Cantor_ObjDecEq" has type
      "ObjDecEq@{<1> <1>} Top@{<1> <2>} → ¬ Cocomplete@{<3> <4> <1>
      <1>}" while it is expected to have type "ObjDecEq@{h h} Top@{h
      Set} → ¬ Cocomplete@{r s h h}" (universe inconsistency: Cannot
      enforce Set = <2> because Set < <2>).

    NOT PINNED HERE.  (a) [About] readbacks as such, the headers' [Set]
    censuses and their attributions to first carriers: pinned only where
    a CLOSED binder carries them ([p458_pinit], [p458_pinit_open],
    [p458_pfinal], [p458_pfinal_open], [p458_top_rebuild_up],
    [p458_top_transport_up], [p458_top_transport_down],
    [p458_ex3a_literal_above_set]) or a refusal does; in particular the
    equation [h1 = h2] that the unexpanded rebuild reads back with is
    pinned only through N29's refusal.  (b) Flip censuses ([Defined]
    against [Qed]) and the closure of the targets under
    [Print Assumptions]: measurements of the build rather than of
    commands; the Makefile's print-assumptions gate is where closure is
    kept.  What a flip decides is pinned where it has a command: the
    triangles [p458_recipe_med_map] and [p458_pcolimit_med_at] hold at
    [eq_refl].  (c) The decidable equality of the index type that
    Instance/Top/Complete.v's [pbox_proj_cont] takes: no refusal shows it
    necessary, and the header records it as a hypothesis of the
    construction, not as a boundary.  (d) Anything about the Type-valued
    [Top] at shapes at or below its points: open there, neither built
    nor refuted, so nothing is refused but the readings N26, N30, N33
    and N34, which only show the refutations do not reach there.

    The guard block at the end names the three hundred and twenty-six
    constants of the six targets, so that a rename breaks this file: one
    hundred and twelve of Instance/Top/Complete.v, sixty-four of
    Instance/Top/Complete/ConeComma.v, seventeen of Instance/Top/
    Complete/Refutations.v, seventy-eight of Instance/Top/Cocomplete.v,
    thirty-two of Instance/Top/Cocomplete/Refutations.v and twenty-three
    of Instance/Top/Cocomplete/TypeValued.v, exactly the list
    [Print Module] gives for each, the forty-two [Program] obligations
    included; the targets declare no record or inductive, so there is
    no [Build_] constructor to name.  The obligations are not reachable
    by their short names under this import list; each is named by the
    shortest qualified name [Locate] gives for it.  Under the full import
    list, [Locate] lists exactly one object for each of the three hundred
    and twenty-six.

--------
* 查找 Mac Lane V.9 的备注 1 和 2 以及练习 3（问题 #458）

钉上 Mac Lane 添加的六个文件 #458 的测量边界 §V.9，书页。133-136（目录 ID maclane:V.9:remark1，关于 Top 是完整的；maclane:V.9:remark2，关于它是余完备的；以及 maclane:V.9:ex3，通过函子 G_* 在锥体类别上诱导的积函子；书中未编号这些注释，这些 ID 是名称，而不是书的编号），以及附加到该问题的条目：Awodey §2.6（awodey:2.6:construction-product-top），Riehl §3.1 示例 3.1.10（riehl:3.1:example10，盒拓扑是一个非例子），Riehl §3.6 命题 3.6.2（riehl:3.6:prop2，底层集合函子是连续且余连续的）以及 Riehl §3.6 示例 3.6.3（riehl:3.6:example3，将配方作为引理，两个部分）。这些目标是 Instance/Top/Complete.v（初始拓扑 [PInit]，有关极限、积、[PTop_Complete] 的构造方法以及书中达到它的路径），以及它的附属文件 Instance/Top/Complete/ConeComma.v（练习 3，更正为 G_* 的右伴随：(a) 如印刷所示被反驳，且 (b) 的左伴随存在但为离散的）和 Instance/Top/Complete/Refutations.v（完备性在此停止，涉及 [PTopCat] 以及位于其 Hom 下的 Type 值 [Top]）；以及 Instance/Top/Cocomplete.v（最终拓扑 [PFinal]，有关余极限、余积、[PTop_Cocomplete] 的构造方法以及书中达到它的路径），以及它的附属文件 Instance/Top/Cocomplete/Refutations.v（余完备性在此停止）和 Instance/Top/Cocomplete/TypeValued.v（可以在 Instance/Top.v 的 Type 值 [Top] 上形成的内容，以及阻止其余部分的三个壁垒）。积极结果已结束
实例/Top/Prop.v 中的 Prop-valued [PTopCat]，由维护者在 2026-09-24 对 #458 的决定。N2-N4、N8-N14、N16-N22 和 N27-N35 重申了目标头记录的拒绝，这些通过 #458 的构建者和审核者在临时文件或此文件中进行测量；N1、N5-N7、N15 和 N23-N26 属于此文件本身。阳性对照独立重申了文件的声明。

通过脚本比较 [Require] 行来衡量的导入列表。First Instance/Top/Complete.v 的二十二行逐字记录
 顺序，然后是该文件； 然后是七行 Instance/Top/Complete/
 ConeComma.v 按顺序添加（Structure/Terminal.v、Structure/Limit/
 Comparison.v、Instance/Cones.v、Instance/Cones/Limit.v、
 Instance/Discrete.v、Instance/One.v、Instance/Roof.v）以及
 卫星； 然后是六行 Instance/Top/Complete/Refutations.v
 添加（Structure/Complete/Freyd.v、Construction/Quotient.v、
 实例/集/分类器/OneLevel.v，实例/Top.v，
 实例/顶部/CompHaus.v、实例/顶部/StoneCech/Refutations.v）和
 卫星； 然后添加六行 Instance/Top/Cocomplete.v
 （函子/Opposite.v、构造/Opposite.v、结构/极限/
 Coproduct.v、Structure/Coequalizer.v、Instance/Sets/Cocomplete.v、
 Instance/Sets/Coequalizer.v) 和该文件； 然后一行
 Instance/Top/Cocomplete/Refutations.v 添加（构造/产品/
 限制.v； 其 [From Coq Require Import Eqdep_dec] 加载模块
 Instance/Top/Complete.v 已经需要 [Coq.Logic.Eqdep_dec]，
 并且它需要 Instance/Top/Complete/Refutations.v，已在上面）
 和卫星； 然后一行 Instance/Top/Cocomplete/
 TypeValued.v 添加 (Instance/Top/Subspace/TypeValued.v) 和
 卫星。四十九行：六个目标的四十六个不同的 [Require] 和三个其他目标不需要的目标。更短的导入列表就是使探测器无缘无故通过的原因。

纪律。该工具在两种方式下都进行了检查：由于这个原因，拒绝对一个不存在的名称进行反驳（“在当前环境中未找到引用探针458_absent_name”），以及该文件中每一个不是反驳的一百零一条定义、示例、引理和归纳项（分别为八十一、十七、一和二），将它们在这个整个文件的一个副本中封装在一起，在该命令处停止构建，并报告受保护的命令已被接受（一百零一条中全部被接受，通过对副本的脚本操作）。除了那个仪器之外，每个否定都是 [Definition]、[Example] 或 [Inductive]，从来不是 [Check]，因此一个开放的 evar 无法满足它。每个否定在这个完整文件的一个副本中被逐个去掉了其反驳关键字，进行编译，并读取其错误；这三十六个副本中的每一个都在去掉的命令内部停止（通过脚本将错误前的文件行与命令的范围进行比较）。记录的类型是那种错误的类型，每个负例旁边都有正例控制；每个负例使用的标识符，其自身的名字，它声明的构造函数以及它的绑定器命名的宇宙，都会被本文件中的某个正例控制使用（通过一个对命令标识符的脚本，但不包括守卫块）。在这个完整文件的另一个副本中，每一个负号除了仪器和 N17 之外，后面都跟着一个绑定器仪器，相同的宇宙绑定器、绑定器和返回类型，其返回类型的假设作为其主体（对于 N19，具有相同的元数且没有构造函数）：所有三十四个都被接受，因此每个负号都是被其主体拒绝的，从未被其语句拒绝。N17 既没有绑定器也没有类型。而每一个十三个UNIVERSE负例，其绑定器声明了将其与控制分开的约束，即N1-N4、N8-N12、N15、N29、N31和N32，都被重新写入了这个完整文件的一份副本中，同时移除了其反驳关键字并删除了该约束，保留了“+”：该副本可以编译，因此每一个十三个负例正是因为声明的约束而被拒绝。N16-N20 的分离约束是 [o < h]，而 Instance/Top.v 的 [Top@{h o}] 自身携带此约束，N24-N28、N30 以及 N33-N35 通过实例方程分离，而不是通过约束（N30、N33 和 N34 通过它们读取的反驳的显式宇宙实例）。每个 UNIVERSE 否定都是一个顶层命令，其宇宙在其自身的绑定器中声明，从不在 [Section] 中声明，但 N17 什么也不声明。引用是在 Rocq 9.1.1 的此文件导入列表下，其中省略了错误的环境块；Rocq 在作用域内用简短名称打印“无法统一”的括号，并且一个宇宙给被剥离的副本命名后，加上一个序列号，写作 <1>、<2>……，每个引用中按首次出现的顺序重新编号。在此导入列表下，文件的依赖闭包是 182 个 [Category] 模块（[Print Libraries]），其中六个是目标。该文件也能在 Coq 8.19.2 和 8.20.1 上编译，无任何警告，针对这些版本的该库预构建树：在它们的一千零七十二个源文件中，一千零六十三个与此树完全相同，另外九个，是主文件 #458 修正的，只在注释上与它不同（通过脚本比较，已移除注释和空白），而六个目标文件也是从此树在它们旁边编译的。精简版副本也在那里进行了编译，每一个三十六个文件在 Rocq 9.1.1 的拒绝文件行上都会被拒绝。根据 8.20.1，每个错误都是 Rocq 9.1.1 到序列名称的一个错误；根据 8.19.2，有十二个错误，其他二十四个都是 UNIVERSE，打印出相同类型的不匹配，并在宇宙实例之间使用“无法统一”子句代替不一致性（N2-N4, N8-N12, N24-N28, N31, N32, N35），没有子句（N1, N15, N18, N29），或者在序列名称之间出现相同的不一致性（N19, N30, N33, N34）（通过脚本对副本进行比较）。

种类。三十六个反驳，按以反驳关键字开头的行计算：NAME-ABSENCE（工具）、UNIVERSE（N1-N4, N8-N12, N15-N20, N24-N35）、CONVERSION（N5, N13, N14）和TYPING（N6, N7, N21-N23）：分别为一条、二十七条、三条和五条。没有拒绝是BINDER类型：每个绑定器工具都被接受。没有一个是INSTANCE或SECTION-VARIABLE拒绝。N21和N22是命题的消去规则：[Prop]的证明只建立证明。N29是一个编码工件，被标记为一，而不是墙：见其段落。

标签。引脚承载了此文件的 N 号；#458 的构建者和评审在其他名称的临时文件中测量了大多数引脚，在此记录以便目标头文件可以引用其中任一个；评审以其评审的一半的构建者命名。构建者 B 的墙文件：其 W1 是 N16，W1free 是 N17，W2（关系 [tcolim_rel]）是 N19，[tcolim_relH_at_o] 是 N20，W3 是 N21，W3squash 是 N22；其控件 [W1ctl_coprod]、[W1ctl_coeq]、[tcolim_relH]、[tcolim_prel]、[tcolim_prel_at_o] 和 [tcolim_med_respects_squashed] 分别是 [p458_top_coproducts_small]、[p458_top_coequalizers]、[p458_tcolim_relH]、[p458_tcolim_prel]、[p458_tcolim_prel_at_o] 和 [p458_tcolim_med_squashed]。构建器 B 的边界文件：其 B1 为 N10，B2 为 N11，B2r 为 N12，B8 为 N18，B10 为 N27；其 B1ctl、B1below、B3、B4、B5、B6、B9 和 B11 分别为 [p458_cocomplete_at_points]、[p458_cocomplete_below]、[p458_cocomplete_points_at_set]、[p458_not_cocomplete_points_at_set]、[p458_corecipe_above]、[p458_pforget_copreserves_above]、[p458_icoprod_at_points] 和 [p458_cocomplete_record_above]。构建器 B 的路线文件：其 [routes_points] 为 N13，[routes_apex] 为 N14，[routes_carrier] 为 [p458_cocomplete_routes_carrier]。建设者A的边界表，在其审查的边界文件中重新测量：该文件的d4和d4b（带注释和空闲）为N2，其d1v为N3，其d3v为N4，d3c为N8；其d1、d1c、d2、d3和d4n分别为[p458_complete_below]、[p458_complete_via_cones_below]、[p458_complete_at_set]、[p458_complete_record_above]和[p458_not_complete_above]；建设者A对圆锥路径的“在s > o时拒绝”为N9。审查的比较文件中的[cone_eq]为[p458_via_cones_cone]。第二次审查的传输文件：它的 [cm_rebuild] 是目标的 [top_rebuild]，且它的 [TAI_rebuild] [Top_ArrowIndex_transport]；其通过字段传递重建，在没有 "+" 的封闭绑定器下被拒绝（"宇宙约束并不由声明的约束暗示：h1 = h2"，根据此文件的导入列表重新测量），是位于 [h1 < h2] 的 N29 引脚；它的 [Top_not_complete_IEM_transported]、[Top_iprod_refuted_IEM_below_h]、[Top_not_cocomplete_ObjDecEq_try] 和 [CompHaus_not_complete_IEM_between_try] 是目标的 [Top_not_complete_below_IEM]、[Top_iprod_refuted_below_IEM]、[Top_not_cocomplete_ObjDecEq] 和 [CompHaus_not_complete_below_IEM]。这些标签不是常量：每个反驳都有它自己的标签，写在其上方一行的注释中，即仪器的读数“仪器”

** 实例/顶层/完成.v

初始拓扑的控制。[PInit] 的指标集合是免费的：
    它及其开集的回读在 CLOSED 绑定器下说明
    [@{o i}]（[p458_pinit]，[p458_pinit_open]）；它在 ARBITRARY 空间上映射的通用属性（[p458_pinit_universal]）；沿着一条映射，它拥有 Instance/Top/Subspace.v 的 [PSub]（[p458_pinit_one_psub]）的开集。该配方，Riehl 的例子 3.6.3 关于极限，在点之上的形状宇宙，[o < j]，独立宇宙 ([p458_recipe_above]) 的消耗和产生的极限性质；其中介者是 [Sets]，在 [eq_refl] ([p458_recipe_med_map])；Riehl 的“必须”，任意极限锥的开集 ([p458_topology_forced])。[PForget] 是连续的 ([p458_pforget_continuous]) 并且保持点之上的形状的极限 ([p458_pforget_preserves_above])。

N1（宇宙）。Instance/Top/Complete.v 的头部，这里是什么：
    [PTop_HasIndexedProducts] 构建的产品“在每个索引宇宙中
    位于或低于 [o]”。在点的宇宙及严格低于它的地方  
    它们被形成（[p458_iprod_at_points], [p458_iprod_below]）；  
    在严格高于的索引上，在类 [HasIndexedProducts@{s s s s so  
    o}] 中，Instance/Top/Complete/Refutations.v 的  
    [PTop_iprod_refuted_IEM] 在 [IEM] 下反驳，N1：  
      术语 "PTop_HasIndexedProducts" 的类型是  
      "HasIndexedProducts@{<1> <1> <1> <2> <3> <2>} PTopCat@{<2> <3>}"  
      而预期类型是 "HasIndexedProducts@{s s s s so  
      o} PTopCat@{o so}"（宇宙不一致：无法强制 s = o  
      因为 o < s）。该乘积是 [eq_refl]（[p458_product_obj], [p458_pprod_open]）处的乘积拓扑，任何索引乘积的拓扑都是初始拓扑（[p458_iprod_topology_forced]），任何等化子的拓扑都是沿其箭头的子空间拓扑（[p458_equalizer_topology_forced]，重述 [PTop_equalizer_open_iff_PSub]）：审稿人所说的“乘积必须带有初始拓扑，等化子必须带有子空间拓扑”

N2（宇宙）。相同的标题，UNIVERSES: [PTop_Complete] 在形状宇宙 [s < o]、[s := Set] 以及极限记录 [r > o] 上被接受，而在这些点之上被拒绝。在 [s = o]、[s < o]、[Set] 使用 [Set < o] 重述，点本身在 [Set]，并且记录位于点之上（[p458_complete_at_points]、[p458_complete_below]、[p458_complete_at_set]、[p458_complete_points_at_set]、[p458_complete_record_above]）；在 [o < s]，N2：
      术语“PTop_Complete”的类型为“Complete@{<1> <2> <3> <4>}”，而预期类型为“Complete@{r s o so}”（宇宙不一致：无法强制 o = <3> 因为 o < s <= <3>）。其极限是 [Sets] 极限上的初始拓扑，在 [eq_refl]（[p458_complete_apex]）。

N3, N4（宇宙）。同一段落：书的路径 [PTop_Complete_via_products] 仅在 [s = o] 和 [r = o] 被接受。它是 #416 在产品上的 [Complete_from_products_equalizers]，以及 #457 的 [PTop_HasEqualizers]，在 [eq_refl]（[p458_complete_via_products], [p458_via_products_is_book_route]）；在 [s < o], N3：
      术语 “PTop_Complete_via_products” 类型为 “Complete@{<1> <1> <1> <2>}”，而期望类型为 “Complete@{o s o so}”（宇宙不一致：无法强制 o = s，因为 s < o）。在 [r > o] 的 N4：
      术语“PTop_Complete_via_products”的类型是“Complete@{o o o so}”，而预期类型是“Complete@{r o o so}”
      （宇宙不一致：无法强制 o = r，因为 o < r）。

N5（转换）。这两条路径的顶点是同构的（[p458_complete_routes_iso]），而书本路径的顶点是积空间的一个子空间（[p458_via_products_apex]）；与余极限路径（N13）不同，它们的点的底层类型在 [eq_refl], N5 处不相等：
      术语“eq_refl”的类型是“vertex_obj[PTop_Complete J T] = vertex_obj[PTop_Complete J T]”，而期望的类型是“vertex_obj[PTop_Complete J T] = vertex_obj[PTop_Complete_via_products J T]”（无法统一“carrier vertex_obj[PTop_Complete J T]”和“carrier vertex_obj[PTop_Complete_via_products J T]”）。Rocq 打印了省略了强制转换 [carrier] 和 [pt_carrier] 的方程，以及省略了 [pt_carrier] 的括号。直接路径的点是 Instance/Sets/Complete.v 的极限，书籍路径的点是形状对象上积的两个映射的 [Sets] 等化器。

Awodey 和 Riehl 的控制。Awodey 对二元积的开集描述为盒子的并集（[p458_ppair_open_iff_box]）以及笛卡尔结构（[p458_cartesian]）；在自然数索引的 [PBool] 次方上的盒子空间不是索引积（[p458_box_not_product]，索引类型的 [Nat.eq_dec] 上的 [box_not_indexed_product]），积拓扑确实起到中介作用（[p458_box_mediator]），而盒子开集 [pbox_all_false] 并非积开集（[p458_box_strictly_finer]）。

** 实例/顶部/完整/锥形逗号.v

N6（打字）。标题，《已修正的印刷声明》：练习 3(a) 对 G_* 的右伴随成立。G_* 对象的作用是 [FCone] 在 [eq_refl]（[p458_coneimage_obj]），修正的 (a) 在其类型下重新陈述，对于任意 [G]、[T] 和形状 ([p458_ex3a_right])；同一个引理给定 G_* 的左伴随，印刷前提，N6：
    术语 "A" 的类型是 "F ⊣ ConeImage G T"，而期望它的类型是 "ConeImage G T ⊣ F"。
引理的形状就是修正：G_* 在 [⊣] 的左边。

N7（打字）。同一段落：在 [PForget]，G_* 具有两个伴随。右边的是最弱拓扑（[p458_pinitcone_obj]，在 [eq_refl]），并且（a）在它处是 [PTop_limit_via_cones] 在 [eq_refl]（[p458_limit_via_right]，[p458_limit_via_right_is]）；左边的离散拓扑存在（[p458_left_adjoint_at_pforget]），但不符合引理 N7：
      术语 “pdisc_cone_adjunction T” 的类型是 “PDiscCone T ⊣ ConeImage PForget T”，而预期类型是 “ConeImage PForget T ⊣ PDiscCone T”。
    因此，（b）的左伴随存在，但它是离散的，并不能构造最弱拓扑。

N8，N9（宇宙）。相同的标题，宇宙：
    [PTop_Complete_via_cones] 包含方程 [r = o] 和约束 [s <= o]。它严格在这些点之下以及在这些点上被接受
    （[p458_complete_via_cones_below]，[p458_complete_via_cones_at_points]）；
    对于高于这些点的记录，N8：
      术语“PTop_Complete_via_cones”的类型为“Complete@{o o o so}”，
      但预期类型为“Complete@{r o o so}”（宇宙不一致：无法强制 o = r，因为 o < r）。以及在它们上方的形状，N9：
      术语 "PTop_Complete_via_cones" 的类型为 "Complete@{<1> <2> <1>
      <3>}"，而它期望的类型为 "Complete@{s s o so}"
      （宇宙不一致：无法强制 o = <1> 因为 o < s <=
      <1>）。它的整个极限锥，不仅是头部 [PTop_via_cones_apex] 对比的顶点，
      而是 [PTop_Complete] 在 [eq_refl] 的顶点：
      目标的 [PTop_via_cones_cone]，独立重述（[p458_via_cones_cone]，构建者 A 的审查测量）以及其自身类型 ([p458_via_cones_cone_is])；
      练习 3(c) 的乘积在它们的类型 ([p458_products_via_cone_comma]) 下。

** 实例/顶层/完备余积.v

最终拓扑的控制。[PFinal] 的指标宇宙是自由的，它的开集在 [eq_refl] 中可读，在 CLOSED 绑定器 [@{o i}]（[p458_pfinal], [p458_pfinal_open]）下；它在任意空间映射出（[p458_pfinal_universal]）上具有普遍性质；沿着一个映射，它具有 Instance/Top/Subspace.v 的开集 [PQuot]（[p458_pfinal_one_pquot]）。在形状宇宙中的余极限公式 高于点的两个独立层次的余极限性质 ([p458_corecipe_above])；直接余极限的顶点在 [eq_refl] ([p458_pcolimit_apex])；其介入三角形在 [eq_refl] 处，独立地重述 ([p458_pcolimit_med_at]) 并作为目标在其类型的 [PColimit_med_at] ([p458_pcolimit_med_at_is])；标题的 STRENGTHS 记录它成立，因为 [pfinal_cocone_colimiting] 结束 [Defined]；Riehl 对余极限的“必须” ([p458_colimit_open_iff_final])。[PForget] 是余连续的 ([p458_pforget_cocontinuous]) 并保持高于点的形状的余极限 ([p458_pforget_copreserves_above])。

N10（宇宙）。标题 UNIVERSES: [PTop_Cocomplete] 在上面记录的点处（[s < o]）、带有点的情况下（[Set]）被接受，但在 [o < s] 被拒绝。在点下方重新声明，在它们下方，在 [Set] 以及记录在其上的情况下（[p458_cocomplete_at_points]、[p458_cocomplete_below]、[p458_cocomplete_points_at_set]、[p458_cocomplete_record_above]）；在 [o < s]，N10：
  术语 "PTop_Cocomplete" 的类型为 "Cocomplete@{<1> <2> <3> <4>}"，而预期类型为 "Cocomplete@{r s o so}"（宇宙不一致：无法强制 o = <3> 因为 o < s <= <3>）。

N11, N12（宇宙）。同一段落：书的路径
    [PTop_Cocomplete_via_coproducts] 只是 [Cocomplete@{o o o so}]。它
    是 #416 在余积处的 [Cocomplete_from_coproducts_coequalizers]
    和 #457 的 [PTop_HasCoequalizers]，在 [eq_refl]
    （[p458_cocomplete_via_coeq]，[p458_via_coeq_is_book_route]）；在
    [s < o]，N11：
      术语 "PTop_Cocomplete_via_coproducts" 的类型是
      "Cocomplete@{<1> <1> <1> <2>}"，而期望的类型是
      "Cocomplete@{o s o so}"（宇宙不一致：无法强制
      o = s，因为 s < o）。在 [r > o]，N12：
      术语 "PTop_Cocomplete_via_coproducts" 的类型是
      "Cocomplete@{o o o so}"，而预期类型是
      "Cocomplete@{r o o so}"（宇宙不一致：无法强制
      o = r 因为 o < r）。

N13, N14（转换）。相同的标题，优点：两条路径的顶点同构（[p458_cocomplete_routes_iso]），并且它们的点的底层类型在 [eq_refl] 处相等（[p458_cocomplete_routes_carrier]）；点集类则不相等，N13：术语“eq_refl”的类型为“colimit_apex (PTop_Cocomplete D F) = colimit_apex (PTop_Cocomplete D F)”，而期望类型为“colimit_apex (PTop_Cocomplete D F) = colimit_apex (PTop_Cocomplete_via_coproducts D F)”（无法统一“pt_carrier (colimit_apex (PTop_Cocomplete D F))”与“pt_carrier (colimit_apex (PTop_Cocomplete_via_coproducts D F))”）。两个空间 N14 也不一样，相同的信息出现在括号中（不能统一 “colimit_apex (PTop_Cocomplete D F)” 和 “colimit_apex (PTop_Cocomplete_via_coproducts D F)”）。Rocq 打印 N13 的点集等式时省略了强制 [pt_carrier]，因此两个引用的不同仅在括号中。集合等价关系的相等性不同，标题记录为：[colim_rel] 与商等生成的等价 a [Sets]。

N15 (宇宙)。相同的标题，宇宙：积对象的索引宇宙位于或低于点的宇宙。积对象在 [eq_refl] ([p458_psigma_open]) 开放，并且积对象在点的宇宙中被索引 ([p458_icoprod_at_points])；严格高于 N15：
  术语 “PTop_HasIndexedCoproducts”的类型为
  “HasIndexedCoproducts@{<1> <2> <3> <4> <3>} PTopCat@{<3> <4>}”，
  而期望的类型为 “HasIndexedCoproducts@{u s s so o} PTopCat@{o so}”（宇宙不一致：无法强制 s = o，因为 o < s）。
非空性证明的注入不同 ([p458_sum_injections_differ])。

** 实例/顶层/完备/类型值.v

N16-N18（宇宙）。标题，《墙》，W1：本书在 [Top] 上的路径被拒绝、带有注释，并且所有剩余宇宙均留待推断，而在索引宇宙 [h] 读取的余积也以同样的方式被拒绝。这两种成分是单独形成的
    ([p458_top_coproducts_small], [p458_top_coequalizers])，并且
    对等化子就是在 [eq_refl] ([p458_top_coequalizer_obj]) 上 [Sets] 对等化子的商拓扑；标注的路径
    [@{o h +| o < h +}]、N16 和自由的 N17，每个：
      术语 "Top_HasIndexedCoproducts_small" 的类型为
      "HasIndexedCoproducts@{<1> <2> <3> <3> <3>} Top@{<3> <4>}"，但期望的类型为 "HasIndexedCoproducts@{<5> <6> <6> <7> <6>} ?C"（宇宙不一致：无法强制 <2> = <7> 因为 <2> <= <4> < <7>）。[<4>] 是该 [Top] 的点的宇宙，[<7>] 是其 hom 宇宙。在索引宇宙 [h], N18：
      术语“Top_HasIndexedCoproducts_small”的类型是
      “HasIndexedCoproducts@{<1> <2> <3> <3> <3>} Top@{<3> <4>}”，而预期类型是“HasIndexedCoproducts@{u h h h h} Top@{h o}”（宇宙不一致：无法强制 <2> = h，因为 <2> <= <4> < h）。

N19, N20（宇宙）。W2：Instance/Sets/Cocomplete.v 中的 [colim_rel]，
    针对 [Top@{h o}] 中在一个形状上的图重新表述，该形状位于或低于点
    （[p458_tcarr]，在 [Type@{o}] 处余极限的点），在 [Type@{o}] 处被拒绝为一个关系，N19：
      宇宙不一致。无法强制 h <= o，因为 o < h。相同的归纳类型在 [Type@{h}] 处被形成 ([p458_tcolim_relH])；在 [Type@{o}]，N20 上读取为一个关系：
  术语 "p458_tcolim_relH D F" 的类型为 "p458_tcarr@{o h s} D F → p458_tcarr@{o h s} D F → Type@{h}"，而预期类型为 "p458_tcarr@{o h s} D F → p458_tcarr@{o h s} D F → Type@{o}"（宇宙不一致：无法强制 h <= o，因为 o < h）。N19 的元类型被形成（其绑定器工具，没有构造子，是被接受的）：用于 [h] 处形状的箭头量化的粘合构造子，是被拒绝的。

N21, N22（输入）。W3：在 [Prop] 中形成并在 [Type@{o}]（[p458_tcolim_prel], [p458_tcolim_prel_at_o]）读取该关系；中介者在 [inhabited]（[p458_tcolim_med_squashed]）之前都尊重该关系，并且 squash 将其消除为一个命题（[p458_squash_prop]）。将关系消除为 apex 的类型值 [≈]，N21：在归纳类型“p458_tcolim_prel”中错误地消除了“H”：返回类型的排序为“Type”，而应为 SProp 或 Prop。在“Type”排序的谓词上不允许消除 Prop 排序的归纳对象，因为证明只能被消除来构建新的证明。并展开 squash，N22，在归纳类型“inhabited”中的“w”得到相同的消息。N21 的分支是空洞；它的拒绝是消除操作的，而不是它们的。

** 反驳常数

Instance/Top/Complete/Refutations.v 和 Instance/Top/Cocomplete/Refutations.v 的常量，以及 Instance/Top/Complete/ConeComma.v 对印刷版练习 3(a) 的反驳中的 [ex3_*] 和 [Ex3a_*] 部分，仅在下面的同名两个部分和保护块中命名，因此重命名它们会影响这些地方，以及本标题中的段落 LABELS、N1 和 N23-N35。

N23（打字）。ConeComma.v 的头文件：打印的 (a) 在空形状中被推翻到 [Roof]（[p458_ex3a_literal_refuted]，重述 [ex3a_left_adjoint_literal_refuted]），通过关于同一 [G] 和 [T]（[p458_ex3a_counterexample]）的三个事实：G_*（[p458_ex3_left_adj]）的左伴随，[G ◯ T]（[p458_ex3_point_limit]）的极限，以及 [T] 的无极限。该推翻在一个封闭绑定下成立，该绑定命名其十一条宇宙，每一条宇宙都被严格声明高于 [Set]（[p458_ex3a_literal_above_set]）：反例的 hom 宇宙没有固定在 [Set]。给修正后的 (a), N23 输入的左伴随：
      术语 "ex3_left_adj" 的类型是 "ex3_LeftAdj ⊣ ConeImage ex3_G1 ex3_T0"，而预期类型是 "ConeImage ex3_G1 ex3_T0 ⊣ ex3_LeftAdj"。因此反例并未影响修正后的引理。

N24, N25（宇宙）。Instance/Top/Complete/Refutations.v 的标题，
    边界。在 [IEM]（[p458_not_complete_above]、[p458_iprod_refuted_above]）下的点上，上述的完整性和乘积被驳斥，
    并且在它们之上或之下没有箭头索引，建设性地（[p458_no_arrow_index_below]）；两个驳斥在点的宇宙中读取，
    其中 [PTop_Complete] 和 [PTop_HasIndexedProducts] 成立，N24：
      术语 "PTop_not_complete_IEM" 的类型是 "IEM@{e} → ¬ Complete@{<1> <2> <3> <4>}"，而预期类型是
      "IEM@{e} → ¬ Complete@{r o o so}"（宇宙不一致：无法强制 <3> = o，因为 <3> < o）。和 N25:
      术语“PTop_iprod_refuted_IEM”的类型为“IEM@{e} → ¬
      HasIndexedProducts@{<1> <1> <1> <1> <2> <3>} PTopCat@{<3> <2>}”，
      而预期的类型为“IEM@{e} → ¬
      HasIndexedProducts@{o o o o so o} PTopCat@{o so}”（宇宙不一致：无法强制 o = <3> 因为 <3> < o）。

N26（宇宙）。相同的标题：[Top_iprod_refuted_IEM_canonical] 否定了其本原宇宙中的 Type 值 [Top] 的产品（[p458_top_iprod_refuted]）；在点的宇宙中索引的类被形成（N26 的绑定器工具），且规范否定无法触及它，N26：
      术语“Top_iprod_refuted_IEM_canonical”的类型为“IEM@{e} → ¬HasIndexedProducts@{<1> <1> <1> <1> <2> <2>} Top@{<2> <3>}”，而预期类型为“IEM@{e} → ¬HasIndexedProducts@{o o o h h h} Top@{h o}”（宇宙不一致：无法强制 o = h，因为 o < h）。[Top_iprod_refuted_below_IEM]（N33）也是如此。[Top] 的产品在其分数或以下的索引宇宙中既不会被构建，也不会被驳斥：也就是说，这是形成性边界的固定。

N27 (宇宙)。Instance/Top/Cocomplete/Refutations.v 的头部，边界：在 [IEM] 下的点上，上述的完备性被反驳，[Set] 处的点也被反驳（[p458_not_cocomplete_above], [p458_not_cocomplete_points_at_set]），[Sets] 和 [Top] 的完备性也同样被反驳（[p458_sets_not_cocomplete_above], [p458_top_not_cocomplete_above]）；在与这些点相等的形状宇宙中读取，N27：
      术语“PTop_not_cocomplete_IEM”的类型为“IEM@{e} → ¬ Cocomplete@{<1> <2> <3> <4>}”，而预期类型为“IEM@{e} → ¬ Cocomplete@{r o o so}”（宇宙不一致：无法强制 <3> = o 因为 <3> < o）。

N28（宇宙）。相同的标题，边界：在空间的可判等下，[PTopCat] 的余完备性被 Freyd 的论证通过 [Set] 处的点以及传输 ([p458_not_cocomplete_objdeceq_at_set]) 否定，并且通过 Cantor 仅在 [Set] 之上的点 ([p458_cantor_objdeceq_above_set]) 否定；Cantor 在 [o := Set]，N28 处读作：
      术语 "PTop_not_cocomplete_Cantor_ObjDecEq" 的类型为
      "ObjDecEq@{<1> <2>} PTopCat@{<2> <1>} → ¬ Cocomplete@{<3> <4> <2> <1>}"，而期望的类型为
      "ObjDecEq@{so Set} PTopCat@{Set so} → ¬ Cocomplete@{r s Set so}"（宇宙不一致：无法强制 Set = <2> 因为 Set < <2>）。该界限是分隔符的，[pcc_Prop] 在 [Set+1]，是该证明路径的属性，而不是被驳回的陈述的属性。

N29（宇宙；一种编码产物，而不是墙）。Instance/Top/Complete/Refutations.v 的头部，内容如下：一个 [Top@{h1 o}] 的连续映射被重建为 [Top@{h2 o}] 的映射，连续性域在 [h1 < h2] ([p458_top_rebuild_up], [top_rebuild]) 处被 η-扩展；未扩展通过的域在两个同源宇宙相同时被接受 ([p458_top_rebuild_unexpanded_at_h])，并且在 [h1 < h2]，N29：
      项“{| continuous_map := f; continuity := continuity f |}”的类型为“ContinuousMorphism@{h1 o} X Y”，但预期类型为“ContinuousMorphism@{h2 o} X Y”（宇宙不一致：无法强制 h1 = h2，因为 h1 < h2）。阐述统一了两种连续性类型：一阶，并添加了 [h1 = h2]；在分隔符 [h1 < h2] 被删除的情况下，同一记录被接受，并且在 [@{o h1 h2 | o < h1, o < h2 +}] 下，它读取回带有该方程的内容（[About]，在携带此文件导入列表的临时文件中）。[Top] 的同质宇宙之间**不是**相互隔离的：箭头索引在它们之间上下移动（[p458_top_transport_up], [p458_top_transport_down], [Top_ArrowIndex_transport]）。N29 针脚说明的是 elaborator 的行为，而不是库的边界：一个在统一之前展开的未来 Rocq 会接受该命令，这意味着工件已经消失，而不是墙移动了。

N30, N31（宇宙）。相同的标题，边界：在严格位于点和同态（[p458_top_not_complete_below]）之间的形状宇宙下，[Top] 的完整性在 [IEM] 下被驳斥，并且在 [ObjDecEq] 下，点位于 [Set]（[p458_top_not_complete_below_at_set]）；#455 的 [Top_not_complete_IEM] 在同态及以上（[p458_top_not_complete_canonical]）处驳斥它。第一次在 [s := o] 读取，由其宇宙实例 N30：宇宙不一致。无法强制 o < o，因为 o = o。并且 #455 在 [o < s < h], N31 的读取：
      术语 "Top_not_complete_IEM" 的类型为 "IEM@{e} → ¬
      Complete@{<1> <2> <3> <3>}"，而预期类型为 
      "IEM@{e} → ¬ Complete@{r s h h}"（宇宙不一致：无法
      强制 <3> = h，因为 <3> <= <2> < h）。因此 [_below] 形式严格覆盖 #455 的更多形状，并且没有反驳能够覆盖在这些点或其以下的形状。

N32（宇宙）。同一段，以及 Instance/Top/CompHaus.v 的更正 (#458)：在严格位于点与 Hom 之间的形宇宙下，[CompHaus] 的完备性在 [IEM] 下被反驳（[p458_comphaus_not_complete_below]），#455 的 [CompHaus_not_complete_IEM_below] 在及以上 Hom（[p458_comphaus_not_complete_canonical]）； #455 的读作 [o < s < h], N32：
  术语 "CompHaus_not_complete_IEM_below" 的类型为 "IEM@{e} → ¬ Complete@{<1> <2> <3> <4>}"，而预期类型为 "IEM@{e} → ¬ Complete@{r s h c}"（宇宙不一致：无法强制 <3> = h，因为 <3> <= <2> < h）。

N33（宇宙）。相同标题：[Top] 的产品在 [IEM] 下被否定，位于点和同态之间的索引宇宙中，在读取 [HasIndexedProducts@{s s s h h h}]（[p458_top_iprod_refuted_below]）时；在索引宇宙 [o] 中，由其宇宙实例 N33 读取：宇宙不一致。无法强制 o < o，因为 o = o。

N34, N35（宇宙）。Instance/Top/Cocomplete/Refutations.v 的头部，
    边界：在 [IEM] 下，[Top] 的余完备性在形状宇宙中被反驳，该宇宙严格位于点和 Hom 之间，通过 Freyd 论证通过传输以及 Cantor（[p458_top_not_cocomplete_between]，[p458_top_not_cocomplete_cantor]），
    并且在 [ObjDecEq] 下，点位于 [Set]，由 Freyd（[p458_top_not_cocomplete_at_set]）论证，Cantor 仅在 [Set]（[p458_top_cantor_objdeceq_above_set]）之上。Freyd [IEM] 形式在 [s := o] 读取，通过其宇宙实例，N34：
      宇宙不一致。无法强制执行 o < o，因为 o = o。以及 Cantor 的 [ObjDecEq] 表格在 [o := Set], N35 处读取：
      术语“Top_not_cocomplete_Cantor_ObjDecEq”的类型为
      "ObjDecEq@{<1> <1>} Top@{<1> <2>} → ¬ Cocomplete@{<3> <4> <1> <1>}"，而预期的类型为 "ObjDecEq@{h h} Top@{h Set} → ¬ Cocomplete@{r s h h}"（宇宙不一致：无法强制 Set = <2> 因为 Set < <2>）。

未在此处固定。(a) [About] 如此回读，标题的 [Set] 统计及其对第一次承运人的归属：仅在封闭的活页夹包含它们时固定（[p458_pinit]、[p458_pinit_open]、[p458_pfinal]、[p458_pfinal_open]、[p458_top_rebuild_up]、[p458_top_transport_up]、[p458_top_transport_down]、[p458_ex3a_literal_above_set]），或在拒绝时固定；特别地，方程 [h1 = h2]，在未展开重建回读时，仅通过 N29 的拒绝固定。(b) 翻转普查（[Defined] 对 [Qed]）以及在 [Print Assumptions] 下目标的闭包：测量的是构建而不是命令；Makefile 的 print-assumptions 门控是保持闭包的地方。翻转决定的内容固定在它有命令的地方：三角形 [p458_recipe_med_map] 和 [p458_pcolimit_med_at] 在 [eq_refl] 保持不变。 (c) Instance/Top/Complete.v 的 [pbox_proj_cont] 所采用的索引类型的可判定等式：没有拒绝显示它是必要的，头文件将其记录为构造的假设，而不是作为边界。(d) 关于类型值 [Top] 在其点以下或相应形状的任何内容：在那里是开放的，既未建立也未被驳回，因此没有东西被拒绝，只有 N26、N30、N33 和 N34 的读数，它们仅显示驳回未达到那里。

在末尾的保护块中，列出了六个目标的三百二十六个常量，以便重命名会破坏此文件：Instance/Top/Complete.v 中有一百一十二个，Instance/Top/Complete/ConeComma.v 中有六十四个，Instance/Top/Complete/Refutations.v 中有十七个，Instance/Top/Cocomplete.v 中有七十八个，Instance/Top/Cocomplete/Refutations.v 中有三十二个，Instance/Top/Cocomplete/TypeValued.v 中有二十三个，正是 [Print Module] 为每个目标提供的列表，其中包括四十二个 [Program] 义务；这些目标没有声明记录或归纳，因此没有 [Build_] 构造函数可以命名。在此导入列表下，这些义务无法通过它们的简称来访问；每个义务都以 [Locate] 为其提供的最短限定名称命名。在完整导入列表下，[Locate] 为三百二十六个中的每一个列出了准确一个对象。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Cartesian.
Require Import Category.Adjunction.Continuity.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Eqdep_dec.
Require Import Category.Instance.Top.Complete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Instance.Cones.
Require Import Category.Instance.Cones.Limit.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.One.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Top.Complete.ConeComma.
Require Import Category.Structure.Complete.Freyd.
Require Import Category.Construction.Quotient.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.CompHaus.
Require Import Category.Instance.Top.StoneCech.Refutations.
Require Import Category.Instance.Top.Complete.Refutations.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Instance.Top.Cocomplete.
Require Import Category.Construction.Product.Limit.
Require Import Category.Instance.Top.Cocomplete.Refutations.
Require Import Category.Instance.Top.Subspace.TypeValued.
Require Import Category.Instance.Top.Cocomplete.TypeValued.

Generalizable All Variables.

(** ** Instrument: the refutation keyword is live / ** 工具：反驳关键词是实时的 *)

(* The instrument / 乐器 *)
Fail Check probe458_absent_name.

(** ** Instance/Top/Complete.v: the initial topology and the recipe / ** Instance/Top/Complete.v：初始拓扑和配方 *)

(*
CONTROL: [PInit]'s index universe is free, under the CLOSED binder
   [@{o i}]; its opens read back at [eq_refl].

--------
控制：[PInit] 的索引范围是免费的，在关闭的绑定器 [@{o i}] 下；它的打开在 [eq_refl] 回读。
*)
Definition p458_pinit@{o i} (S : SetoidObject@{o o}) (I : Type@{i})
  (X : I → PTop@{o}) (t : ∀ k : I, SetoidMorphism@{o o o} S (X k)) :
  PTop@{o} := PInit S I X t.

Example p458_pinit_open@{o i} (S : SetoidObject@{o o}) (I : Type@{i})
  (X : I → PTop@{o}) (t : ∀ k : I, SetoidMorphism@{o o o} S (X k))
  (V : S → Prop) :
  POpen (PInit S I X t) V = pinit_open S I X t V := eq_refl.

(*
CONTROL: the universal property over ARBITRARY spaces mapping in, and
   the one-map case, the subspace topology, restated.

--------
控制：对任意空间的映射的普遍性质，以及单映射情况的子空间拓扑，重新表述。
*)
Definition p458_pinit_universal@{o i +} (S : SetoidObject@{o o})
  (I : Type@{i}) (X : I → PTop@{o})
  (t : ∀ k : I, SetoidMorphism@{o o o} S (X k)) (Z : PTop@{o})
  (g : SetoidMorphism@{o o o} Z S) :
  @PCont Z (PInit S I X t) g <->
  (∀ k, @PCont Z (X k) (setoid_morphism_compose@{o o o} (t k) g)) :=
  pinit_universal S I X t Z g.

Definition p458_pinit_one_psub@{o +} (X : PTop@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S X)
  (V : S → Prop) :
  POpen (PInit S Datatypes.unit (fun _ => X) (fun _ => h)) V
  <-> POpen (PSub X S h) V :=
  PInit_one_PSub X S h V.

(*
CONTROL: the recipe at a shape universe ABOVE the points, [o < j],
   the consumed and the produced limit properties at independent
   universes; its mediator IS the [Sets] one at [eq_refl].

--------
控制：在一个高于这些点的形状宇宙中的配方，[o < j]，独立宇宙中消耗和产生的极限属性；它的中介是位于 [eq_refl] 的 [Sets]。
*)
Definition p458_recipe_above@{j o so v v1 w w1 +| o < so, o < j +}
  {J : Category@{j o o}} (T : J ⟶ PTopCat@{o so})
  (N : Cone (PForget@{o so} ◯ T)) (HN : IsLimitCone@{v v1 j o so} N) :
  IsLimitCone@{w w1 j o so} (pinit_cone T N) :=
  pinit_cone_limiting T N HN.

Example p458_recipe_med_map@{j o so +| o < so +}
  {J : Category@{j o o}} (T : J ⟶ PTopCat@{o so})
  (N : Cone (PForget@{o so} ◯ T)) (HN : IsLimitCone N) (M : Cone T) :
  pmap (unique_obj (pinit_cone_limiting T N HN M))
    = unique_obj (HN (FCone PForget M)) := eq_refl.

(*
CONTROL: Riehl's "must": the opens of ANY limiting cone are those of
   the initial topology of its legs.

--------
控制：Riehl 的“必须”：任何限制锥的开集都是其各支的初始拓扑的开集。
*)
Definition p458_topology_forced@{j o so +| o < so +}
  {J : Category@{j o o}} (T : J ⟶ PTopCat@{o so}) (L : Cone T)
  (HL : IsLimitCone L) (V : vertex_obj[L] → Prop) :
  POpen (vertex_obj[L]) V
  <-> POpen (vertex_obj[pinit_cone T (FCone PForget L)]) V :=
  PTop_limit_open_iff_initial T L HL V.

(*
CONTROL: [PForget] is continuous, and preserves the limits of shapes
   ABOVE the points, [o < s].

--------
控制：[PForget] 是连续的，并保持形状在点以上的限制，[o < s]。
*)
Definition p458_pforget_continuous@{o so +| o < so +} :
  ContinuousFunctor PForget@{o so} := PForget_Continuous.

Definition p458_pforget_preserves_above@{s o so +| o < so, o < s +}
  (J : Category@{s o o}) (T : J ⟶ PTopCat@{o so}) :
  PreservesLimitCone T PForget@{o so} := PForget_PreservesLimitCone J T.

(** ** Instance/Top/Complete.v: products and their index boundary / ** Instance/Top/Complete.v：产品及其索引边界 *)

(*
CONTROL: products indexed at the points' universe and strictly
   below it.

--------
控制：产品在点的宇宙中被索引，并严格位于其下方。
*)
Definition p458_iprod_at_points@{o so +| o < so +} :
  @HasIndexedProducts@{o o o o so o} PTopCat@{o so} :=
  PTop_HasIndexedProducts.

Definition p458_iprod_below@{i o so +| i < o, o < so +} :
  @HasIndexedProducts@{i i i o so o} PTopCat@{o so} :=
  PTop_HasIndexedProducts.

(* N1 *)
Fail Definition p458_iprod_above@{s o so +| o < so, o < s +} :
  @HasIndexedProducts@{s s s s so o} PTopCat@{o so} :=
  PTop_HasIndexedProducts.

(*
CONTROL: the product IS the product topology, at [eq_refl]; the
   topology of ANY indexed product is the initial one.

--------
控制：产品就是产品拓扑，在 [eq_refl]；任何索引产品的拓扑都是初始拓扑。
*)
Example p458_product_obj@{i o so +| i <= o, o < so +} (A : Type@{i})
  (X : A → PTop@{o}) :
  @indexed_product PTopCat@{o so} PTop_HasIndexedProducts A X
    = PProd A X := eq_refl.

Example p458_pprod_open@{i o +| i <= o +} (A : Type@{i})
  (X : A → PTop@{o}) (V : PProd_carrier A X → Prop) :
  POpen (PProd A X) V
    = pinit_open (PProd_carrier A X) A X (pprod_leg A X) V := eq_refl.

Definition p458_iprod_topology_forced@{i o so +| i <= o, o < so +}
  (A : Type@{i}) (X : A → PTop@{o}) (Y : PTop@{o})
  (p : ∀ a, Y ~{PTopCat@{o so}}~> X a)
  (H : @IsIndexedProduct PTopCat@{o so} A X Y p) (V : Y → Prop) :
  POpen Y V <-> POpen (PInit Y A X (fun a => pmap (p a))) V :=
  PTop_iprod_open_iff_initial A X Y p H V.

(*
CONTROL: the topology of ANY equalizer of spaces is the subspace
   topology along its arrow.

--------
控制：任何空间等化器的拓扑是沿其箭头的子空间拓扑。
*)
Definition p458_equalizer_topology_forced@{o so +| o < so +}
  {X Y : PTop@{o}} (f g : X ~{PTopCat@{o so}}~> Y) (E : PTop@{o})
  (e : E ~{PTopCat@{o so}}~> X)
  (H : @IsEqualizer PTopCat@{o so} X Y f g E e) (V : E → Prop) :
  POpen E V <-> POpen (PSub X E (pmap e)) V :=
  PTop_equalizer_open_iff_PSub f g E e H V.

(** ** Instance/Top/Complete.v: Remark 1 and its universe boundary / ** 实例/顶部/完成.v：备注1及其宇宙边界 *)

(*
CONTROL: [PTop_Complete] at a shape universe equal to the points',
   strictly below them, at [Set], with the points at [Set], and with the
   limit record strictly above the points.

--------
控制：在形状宇宙等于这些点的情况下的 [PTop_Complete]，严格低于这些点的情况下，在 [Set]，点位于 [Set] 的情况下，以及限制记录严格高于这些点的情况下。
*)
Definition p458_complete_at_points@{o so +| o < so +} :
  @Complete@{o o o so} PTopCat@{o so} := PTop_Complete.

Definition p458_complete_below@{s o so +| s < o, o < so +} :
  @Complete@{o s o so} PTopCat@{o so} := PTop_Complete.

Definition p458_complete_at_set@{o so +| Set < o, o < so +} :
  @Complete@{o Set o so} PTopCat@{o so} := PTop_Complete.

Definition p458_complete_points_at_set@{so +| Set < so +} :
  @Complete@{Set Set Set so} PTopCat@{Set so} := PTop_Complete.

Definition p458_complete_record_above@{r o so +| o < r, o < so +} :
  @Complete@{r o o so} PTopCat@{o so} := PTop_Complete.

(* N2 *)
Fail Definition p458_complete_above@{r s o so +| o < s, o < so, s <= r +} :
  @Complete@{r s o so} PTopCat@{o so} := PTop_Complete.

(*
CONTROL: its limit is the initial topology on the [Sets] limit, at
   [eq_refl].

--------
控制：它的极限是在 [eq_refl] 上 [Sets] 极限的初始拓扑。
*)
Example p458_complete_apex@{s o so +| s <= o, o < so +}
  (J : Category@{s o o}) (T : J ⟶ PTopCat@{o so}) :
  vertex_obj[@limit_cone _ _ _ (@PTop_Complete@{o s o so _ _} J T)]
    = pinit_top T (Sets_limit_cone (PForget ◯ T)) := eq_refl.

(*
CONTROL: the book's route, at its one instance [Complete@{o o o so}];
   it IS #416's theorem at the products and #457's equalizers.

--------
控制：该书的路径，在其一个实例 [Complete@{o o o so}]；它是 #416 在乘积上的定理以及 #457 的等化器。
*)
Definition p458_complete_via_products@{o so +| o < so +} :
  @Complete@{o o o so} PTopCat@{o so} := PTop_Complete_via_products.

Example p458_via_products_is_book_route@{o so +| o < so +} :
  @PTop_Complete_via_products@{o so _ _ _ _ _}
    = @Complete_from_products_equalizers PTopCat@{o so}
        PTop_HasIndexedProducts PTop_HasEqualizers := eq_refl.

(* N3 *)
Fail Definition p458_via_products_below@{s o so +| s < o, o < so +} :
  @Complete@{o s o so} PTopCat@{o so} := PTop_Complete_via_products.

(* N4 *)
Fail Definition p458_via_products_record_above@{r o so +| o < r, o < so +} :
  @Complete@{r o o so} PTopCat@{o so} := PTop_Complete_via_products.

(*
CONTROL: the book route's limit is a subspace of a product space, and
   the two routes' apexes are isomorphic.

--------
控制：书路线的极限是一个乘积空间的子空间，并且两条路线的顶点是同构的。
*)
Definition p458_via_products_apex@{o so +| o < so +}
  (J : Category@{o o o}) (T : J ⟶ PTopCat@{o so}) :
  ex (fun S => ex (fun h =>
    vertex_obj[@limit_cone _ _ _ (@PTop_Complete_via_products J T)]
      = PSub (PProd (obj[J]) (fun j => fobj[T] j)) S h)) :=
  PTop_Complete_via_products_apex J T.

Definition p458_complete_routes_iso@{o so +| o < so +}
  (J : Category@{o o o}) (T : J ⟶ PTopCat@{o so}) :
  vertex_obj[@limit_cone _ _ _ (@PTop_Complete J T)]
    ≅[PTopCat@{o so}]
  vertex_obj[@limit_cone _ _ _ (@PTop_Complete_via_products J T)] :=
  PTop_Complete_routes_iso J T.

(* N5 *)
Fail Example p458_complete_routes_carrier@{o so +| o < so +}
  (J : Category@{o o o}) (T : J ⟶ PTopCat@{o so}) :
  carrier (pt_carrier (vertex_obj[@limit_cone _ _ _ (PTop_Complete J T)]))
  = carrier (pt_carrier
      (vertex_obj[@limit_cone _ _ _ (PTop_Complete_via_products J T)])) :=
  eq_refl.

(** ** Instance/Top/Complete.v: Awodey §2.6 and Riehl's box topology / ** 实例/顶/完整.v：Awodey §2.6 和 Riehl 的盒拓扑 *)

(*
CONTROL: Awodey's description of the binary product's opens, and the
   cartesian structure.

--------
控制：Awodey 对二元积的开集以及笛卡尔结构的描述。
*)
Definition p458_ppair_open_iff_box@{o +} (X1 X2 : PTop@{o})
  (W : PPair_carrier X1 X2 → Prop) :
  POpen (PPair X1 X2) W <-> pair_box_union X1 X2 W :=
  PPair_open_iff_box X1 X2 W.

Definition p458_cartesian@{o so +| o < so +} : @Cartesian PTopCat@{o so} :=
  PTop_Cartesian.

(*
CONTROL: the box space on the nat-indexed power of [PBool] is not an
   indexed product; the product topology mediates; the box-open
   [pbox_all_false] is not product-open.

--------
控制：在 nat 索引的 [PBool] 次方上，盒空间不是索引乘积；乘积拓扑起作用；盒开 [pbox_all_false] 不是乘积开集。
*)
Definition p458_box_not_product@{o so +| o < so +} :
  @IsIndexedProduct PTopCat@{o so} nat (fun _ => PBool@{o})
    (PBoxTop nat (fun _ => PBool@{o}))
    (pbox_proj nat (fun _ => PBool@{o}) Nat.eq_dec)
  → False :=
  box_not_indexed_product.

Definition p458_box_mediator@{o +} :
  PMor@{o} PConv@{o} (PProd nat (fun _ => PBool@{o})) :=
  pconv_prod_mediator.

Definition p458_box_strictly_finer@{o +} :
  POpen (PProd nat (fun _ => PBool@{o})) pbox_all_false → False :=
  pbox_all_false_not_product_open.

(** ** Instance/Top/Complete/ConeComma.v: Exercise 3, corrected / ** 实例/顶/完整/圆锥逗号.v：练习 3，已更正 *)

(*
CONTROL: G_*'s object action, and (a) with a RIGHT adjoint of G_*,
   restated for any [G], [T] and shape.

--------
控制：G_* 的对象操作，以及 (a) G_* 的右伴随，重新表述用于任何 [G]、[T] 和形状。
*)
Example p458_coneimage_obj@{oj oc od h +} {J : Category@{oj h h}}
  {C : Category@{oc h h}} {D : Category@{od h h}} (G : C ⟶ D)
  (T : J ⟶ C) (N : Cone T) : fobj[ConeImage G T] N = FCone G N :=
  eq_refl.

Definition p458_ex3a_right@{oj oc od h +} {J : Category@{oj h h}}
  {C : Category@{oc h h}} {D : Category@{od h h}} (G : C ⟶ D)
  (T : J ⟶ C) (W : Cones (G ◯ T) ⟶ Cones T) (A : ConeImage G T ⊣ W)
  (L : Limit (G ◯ T)) : Limit T :=
  limit_from_cone_right_adjoint G T W A L.

(* N6 *)
Fail Definition p458_ex3a_left@{oj oc od h +} {J : Category@{oj h h}}
  {C : Category@{oc h h}} {D : Category@{od h h}} (G : C ⟶ D)
  (T : J ⟶ C) (F : Cones (G ◯ T) ⟶ Cones T) (A : F ⊣ ConeImage G T)
  (L : Limit (G ◯ T)) : Limit T :=
  limit_from_cone_right_adjoint G T F A L.

(*
CONTROL: at [PForget] the right adjoint is the weakest topology, and
   (a) at it IS [PTop_limit_via_cones]; the left adjoint, the discrete
   topology, exists too.

--------
控制：在 [PForget]，右伴随是最弱的拓扑，并且
   (a) 在它上是 [PTop_limit_via_cones]；左伴随，离散拓扑，也存在。
*)
Example p458_pinitcone_obj@{j o so +| o < so +} {J : Category@{j o o}}
  (T : J ⟶ PTopCat@{o so}) (N : Cone (PForget@{o so} ◯ T)) :
  fobj[PInitCone T] N = pinit_cone T N := eq_refl.

Definition p458_limit_via_right@{j o so +| o < so +}
  {J : Category@{j o o}} (T : J ⟶ PTopCat@{o so})
  (L : Limit (PForget@{o so} ◯ T)) : Limit T :=
  limit_from_cone_right_adjoint PForget T (PInitCone T)
    (pcone_adjunction T) L.

Example p458_limit_via_right_is@{j o so +| o < so +} {J : Category@{j o o}}
  (T : J ⟶ PTopCat@{o so}) (L : Limit (PForget@{o so} ◯ T)) :
  p458_limit_via_right T L = PTop_limit_via_cones T L := eq_refl.

Definition p458_left_adjoint_at_pforget@{j o so +| o < so +}
  {J : Category@{j o o}} (T : J ⟶ PTopCat@{o so}) :
  PDiscCone T ⊣ ConeImage PForget@{o so} T :=
  pdisc_cone_adjunction T.

(* N7 *)
Fail Definition p458_limit_via_left@{j o so +| o < so +}
  {J : Category@{j o o}} (T : J ⟶ PTopCat@{o so})
  (L : Limit (PForget@{o so} ◯ T)) : Limit T :=
  limit_from_cone_right_adjoint PForget T (PDiscCone T)
    (pdisc_cone_adjunction T) L.

(*
CONTROL: [PTop_Complete_via_cones] strictly below the points and at
   them; its whole limit cone IS [PTop_Complete]'s at [eq_refl]; the
   products of (c).

--------
控制：[PTop_Complete_via_cones] 严格位于点以下及其上；其整体极限锥是 [PTop_Complete] 在 [eq_refl] 的；（c）的乘积。
*)
Definition p458_complete_via_cones_below@{s o so +| s < o, o < so +} :
  @Complete@{o s o so} PTopCat@{o so} := PTop_Complete_via_cones.

Definition p458_complete_via_cones_at_points@{o so +| o < so +} :
  @Complete@{o o o so} PTopCat@{o so} := PTop_Complete_via_cones.

(* N8 *)
Fail Definition p458_via_cones_record_above@{r o so +| o < r, o < so +} :
  @Complete@{r o o so} PTopCat@{o so} := PTop_Complete_via_cones.

(* N9 *)
Fail Definition p458_via_cones_above@{s o so +| o < s, o < so +} :
  @Complete@{s s o so} PTopCat@{o so} := PTop_Complete_via_cones.

Example p458_via_cones_cone@{s o so +| s <= o, o < so +}
  (J : Category@{s o o}) (T : J ⟶ PTopCat@{o so}) :
  @limit_cone _ _ _ (@PTop_Complete_via_cones@{o s o so _ _ _} J T)
    = @limit_cone _ _ _ (@PTop_Complete@{o s o so _ _} J T) := eq_refl.

Definition p458_via_cones_cone_is@{s o so +| s <= o, o < so +}
  (J : Category@{s o o}) (T : J ⟶ PTopCat@{o so}) :
  @limit_cone _ _ _ (@PTop_Complete_via_cones@{o s o so _ _ _} J T)
    = @limit_cone _ _ _ (@PTop_Complete@{o s o so _ _} J T) :=
  PTop_via_cones_cone J T.

Definition p458_products_via_cone_comma@{i o so +| i <= o, o < so +} :
  @HasIndexedProducts@{i i i o so o} PTopCat@{o so} :=
  PTop_products_via_cone_comma.

(** ** Instance/Top/Cocomplete.v: the final topology and the recipe / ** Instance/Top/Cocomplete.v：最终拓扑与配方 *)

(*
CONTROL: [PFinal]'s index universe is free, under the CLOSED binder
   [@{o i}]; its opens read back at [eq_refl].

--------
控制：[PFinal] 的索引宇宙是免费的，在封闭的 [@{o i}] 目录下；它在 [eq_refl] 可重新读取。
*)
Definition p458_pfinal@{o i} (S : SetoidObject@{o o}) (Ix : Type@{i})
  (X : Ix → PTop@{o}) (f : ∀ k : Ix, SetoidMorphism@{o o o} (X k) S) :
  PTop@{o} := PFinal S Ix X f.

Example p458_pfinal_open@{o i} (S : SetoidObject@{o o}) (Ix : Type@{i})
  (X : Ix → PTop@{o}) (f : ∀ k : Ix, SetoidMorphism@{o o o} (X k) S)
  (V : S → Prop) :
  POpen (PFinal S Ix X f) V
  = ((∀ s t : S, s ≈ t → V s → V t) /\
     (∀ k : Ix, POpen (X k) (fun x => V (f k x)))) := eq_refl.

(*
CONTROL: the universal property over ARBITRARY spaces mapping out,
   and the one-map case, the quotient topology, restated.

--------
控制：在任意空间上映射出的普遍性质，以及单映射的情况，即商拓扑，重新表述。
*)
Definition p458_pfinal_universal@{o i +} (S : SetoidObject@{o o})
  (Ix : Type@{i}) (X : Ix → PTop@{o})
  (f : ∀ k : Ix, SetoidMorphism@{o o o} (X k) S) (Z : PTop@{o})
  (g : SetoidMorphism@{o o o} S Z) :
  @PCont (PFinal S Ix X f) Z g <->
  (∀ k, @PCont (X k) Z (setoid_morphism_compose@{o o o} g (f k))) :=
  pfinal_universal S Ix X f Z g.

Definition p458_pfinal_one_pquot@{o +} (X : PTop@{o})
  (T : SetoidObject@{o o}) (q : SetoidMorphism@{o o o} X T)
  (V : T → Prop) :
  POpen (PQuot X T q) V
  <-> POpen (PFinal T Datatypes.unit (fun _ => X) (fun _ => q)) V :=
  pfinal_one_map_PQuot X T q V.

(*
CONTROL: the colimit recipe at a shape universe ABOVE the points; the
   direct colimit's apex; Riehl's "must" for colimits.

--------
控制：在点之上的形宇宙中的余极限配方；直接余极限的顶点；Riehl 关于余极限的“必须”。
*)
Definition p458_corecipe_above@{o so s r r' x x' +| o < so, o < s +}
  {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so})
  (N : Cocone (PForget@{o so} ◯ F))
  (HN : IsColimitCocone@{x' x' r' s o so} N) :
  IsColimitCocone@{x x r s o so} (PFinalCocone F N) :=
  pfinal_cocone_colimiting F N HN.

Example p458_pcolimit_apex@{r s o so +| o < so, s <= o, o <= r +}
  {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so}) :
  vertex_obj[@limit_cone _ _ _ (@PColimit@{r s o so _ _} D F)]
    = PFinal (Sets_colim_obj (PForget ◯ F)) (obj[D]) (fun d => F d)
        (fun d => Sets_colim_inj (PForget ◯ F) d) := eq_refl.

Example p458_pcolimit_med_at@{r s o so +| o < so, s <= o, o <= r +}
  {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so}) (M : Cocone F) (d : D)
  (x : pt_carrier (F d)) :
  pmap (unique_obj (@ump_limits _ _ _ (@PColimit@{r s o so _ _} D F) M))
    (existT _ d x) = pmap (cocone_inj M d) x := eq_refl.

Definition p458_pcolimit_med_at_is@{r s o so +| o < so, s <= o, o <= r +}
  {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so}) (M : Cocone F) (d : D)
  (x : pt_carrier (F d)) :
  pmap (unique_obj (@ump_limits _ _ _ (@PColimit@{r s o so _ _} D F) M))
    (existT _ d x) = pmap (cocone_inj M d) x :=
  PColimit_med_at F M d x.

Definition p458_colimit_open_iff_final@{o so s r +| o < so +}
  {D : Category@{s o o}} {F : D ⟶ PTopCat@{o so}}
  (L : Colimit@{r s o so} F) (V : pt_carrier (colimit_apex L) → Prop) :
  POpen (colimit_apex L) V
  <-> POpen (PFinal (pt_carrier (colimit_apex L)) (obj[D]) (fun d => F d)
               (fun d => pmap (colimit_inj (colimit_is_acolimit L) d))) V :=
  PTop_colimit_open_iff_final L V.

(*
CONTROL: [PForget] is cocontinuous, and preserves the colimits of
   shapes ABOVE the points.

--------
控制：[PForget] 是共连续的，并且保持点以上形状的余极限。
*)
Definition p458_pforget_cocontinuous@{o so +| o < so +} :
  CocontinuousFunctor PForget@{o so} := PForget_Cocontinuous.

Definition p458_pforget_copreserves_above@{s o so +| o < so, o < s +}
  (J : Category@{s o o}) (K : J ⟶ PTopCat@{o so}) :
  PreservesColimitCocone K PForget@{o so} :=
  PForget_PreservesColimitCocone J K.

(** ** Instance/Top/Cocomplete.v: Remark 2 and its universe boundary / ** Instance/Top/Cocomplete.v：备注 2 及其宇宙边界 *)

(*
CONTROL: [PTop_Cocomplete] at the points' universe, strictly below
   it, with the points at [Set], and with the colimit record strictly
   above the points.

--------
控制：在点的宇宙中 [PTop_Cocomplete]，严格低于它，在 [Set] 处的点，以及在点之上的余极限记录严格
*)
Definition p458_cocomplete_at_points@{o so +| o < so +} :
  @Cocomplete@{o o o so} PTopCat@{o so} := PTop_Cocomplete.

Definition p458_cocomplete_below@{s o so +| s < o, o < so +} :
  @Cocomplete@{o s o so} PTopCat@{o so} := PTop_Cocomplete.

Definition p458_cocomplete_points_at_set@{so +| Set < so +} :
  @Cocomplete@{Set Set Set so} PTopCat@{Set so} := PTop_Cocomplete.

Definition p458_cocomplete_record_above@{r o so +| o < r, o < so +} :
  @Cocomplete@{r o o so} PTopCat@{o so} := PTop_Cocomplete.

(* N10 *)
Fail Definition p458_cocomplete_above@{r s o so +| o < s, o < so, s <= r +} :
  @Cocomplete@{r s o so} PTopCat@{o so} := PTop_Cocomplete.

(*
CONTROL: the book's route, at its one instance
   [Cocomplete@{o o o so}]; it IS #416's theorem at the coproducts and
   #457's coequalizers.

--------
控制：书的路径，在它的一个实例中
   [Cocomplete@{o o o so}]；它是#416在余积处的定理，以及
   #457的等化器。
*)
Definition p458_cocomplete_via_coeq@{o so +| o < so +} :
  @Cocomplete@{o o o so} PTopCat@{o so} := PTop_Cocomplete_via_coproducts.

Example p458_via_coeq_is_book_route@{o so +| o < so +} :
  @PTop_Cocomplete_via_coproducts@{o so _ _ _ _ _ _}
    = Cocomplete_from_coproducts_coequalizers PTop_HasIndexedCoproducts
        PTop_HasCoequalizers := eq_refl.

(* N11 *)
Fail Definition p458_via_coeq_below@{s o so +| s < o, o < so +} :
  @Cocomplete@{o s o so} PTopCat@{o so} := PTop_Cocomplete_via_coproducts.

(* N12 *)
Fail Definition p458_via_coeq_record_above@{r o so +| o < r, o < so +} :
  @Cocomplete@{r o o so} PTopCat@{o so} := PTop_Cocomplete_via_coproducts.

(*
CONTROL: the two routes' apexes are isomorphic, and their points'
   underlying types are equal at [eq_refl].

--------
控制：这两条路径的顶点是同构的，并且它们的点的底层类型在 [eq_refl] 处是相等的。
*)
Definition p458_cocomplete_routes_iso@{o so +| o < so +}
  (D : Category@{o o o}) (F : D ⟶ PTopCat@{o so}) :
  colimit_apex (PTop_Cocomplete D F)
    ≅[PTopCat@{o so}] colimit_apex (PTop_Cocomplete_via_coproducts D F) :=
  PTop_Cocomplete_routes_iso D F.

Example p458_cocomplete_routes_carrier@{o so +| o < so +}
  (D : Category@{o o o}) (F : D ⟶ PTopCat@{o so}) :
  carrier (pt_carrier (colimit_apex (PTop_Cocomplete D F)))
  = carrier
      (pt_carrier (colimit_apex (PTop_Cocomplete_via_coproducts D F))) :=
  eq_refl.

(* N13 *)
Fail Example p458_cocomplete_routes_points@{o so +| o < so +}
  (D : Category@{o o o}) (F : D ⟶ PTopCat@{o so}) :
  pt_carrier (colimit_apex (PTop_Cocomplete D F))
  = pt_carrier (colimit_apex (PTop_Cocomplete_via_coproducts D F)) := eq_refl.

(* N14 *)
Fail Example p458_cocomplete_routes_spaces@{o so +| o < so +}
  (D : Category@{o o o}) (F : D ⟶ PTopCat@{o so}) :
  colimit_apex (PTop_Cocomplete D F)
  = colimit_apex (PTop_Cocomplete_via_coproducts D F) := eq_refl.

(** ** Instance/Top/Cocomplete.v: coproducts and their index boundary / ** Instance/Top/Cocomplete.v：余积及其索引边界 *)

(*
CONTROL: the coproduct's opens at [eq_refl]; coproducts indexed at
   the points' universe; the non-vacuity witness.

--------
控制：余积在 [eq_refl] 处打开；余积在点的宇宙中索引；非空性证明者。
*)
Example p458_psigma_open@{o i +| i <= o +} (Ix : Type@{i})
  (X : Ix → PTop@{o})
  (V : Sets_icoprod_obj (fun k => pt_carrier (X k)) → Prop) :
  POpen (PSigma Ix X) V
  = ((∀ p q : Sets_icoprod_obj (fun k => pt_carrier (X k)),
        p ≈ q → V p → V q) /\
     (∀ k : Ix, POpen (X k) (fun x => V (existT _ k x)))) := eq_refl.

Definition p458_icoprod_at_points@{o so u +| o < so, so <= u, o < u +} :
  @HasIndexedCoproducts@{u o o so o} PTopCat@{o so} :=
  PTop_HasIndexedCoproducts.

(* N15 *)
Fail Definition p458_icoprod_above@{s o so u +| o < so, o < s, so <= u,
  s < u +} :
  @HasIndexedCoproducts@{u s s so o} PTopCat@{o so} :=
  PTop_HasIndexedCoproducts.

Definition p458_sum_injections_differ@{o so u | o < so, o < u +} :
  psigma_inj@{o so o u} bool (fun _ => PTwoIndisc@{o}) true
    ≈[PTopCat@{o so}] psigma_inj@{o so o u} bool (fun _ => PTwoIndisc) false
  → False := PTwoIndiscSum_injections_differ.

(** ** Instance/Top/Cocomplete/TypeValued.v: the three walls / ** Instance/Top/Cocomplete/TypeValued.v：三堵墙 *)

(*
CONTROL: W1's two ingredients, each accepted alone; the coequalizer
   IS the quotient topology at [eq_refl].

--------
控制：W1 的两种成分，各自单独接受；等化器就是 [eq_refl] 的商拓扑。
*)
Definition p458_top_coproducts_small@{o h u u0 +| o < h, u0 <= o, h < u +} :
  @HasIndexedCoproducts@{u u0 h h h} Top@{h o} :=
  Top_HasIndexedCoproducts_small.

Definition p458_top_coequalizers@{o h +| o < h +} :
  @HasCoequalizers Top@{h o} := Top_HasCoequalizers.

Example p458_top_coequalizer_obj@{o h +| o < h +} {x y : Top@{h o}}
  (f g : x ~{Top@{h o}}~> y) :
  `1 (@coeq _ Top_HasCoequalizers x y f g)
    = TQuot y (SetsCoeq (continuous_map f) (continuous_map g))
        (sets_coeq_proj (continuous_map f) (continuous_map g)) := eq_refl.

(* N16 *)
Fail Definition p458_top_book_route@{o h +| o < h +} :
  @Cocomplete Top@{h o} :=
  Cocomplete_from_coproducts_coequalizers Top_HasIndexedCoproducts_small
    Top_HasCoequalizers.

(* N17 *)
Fail Definition p458_top_book_route_free :=
  Cocomplete_from_coproducts_coequalizers Top_HasIndexedCoproducts_small
    Top_HasCoequalizers.

(* N18 *)
Fail Definition p458_top_coproducts_at_homs@{o h u +| o < h, h < u +} :
  @HasIndexedCoproducts@{u h h h h} Top@{h o} :=
  Top_HasIndexedCoproducts_small.

(*
The points of a colimit of [Top@{h o}] over a shape at or below the
   points: the sigma over the shape's objects, at [o].

--------
在点或以下的形状上，[Top@{h o}] 的余极限的点：在 [o] 处的该形状对象上的 sigma。
*)
Definition p458_tcarr@{o h s +| o < h, s <= o +} (D : Category@{s h h})
  (F : D ⟶ Top@{h o}) : Type@{o} :=
  { d : obj[D] & top_carrier (F d) }.

(* N19 *)
Fail Inductive p458_tcolim_rel@{o h s +| o < h, s <= o +}
  (D : Category@{s h h}) (F : D ⟶ Top@{h o}) :
  p458_tcarr D F → p458_tcarr D F → Type@{o} :=
  | p458_tcr_point : ∀ (d : D) (x y : top_carrier (F d)), x ≈ y →
      p458_tcolim_rel (existT _ d x) (existT _ d y)
  | p458_tcr_glue : ∀ (d d' : D) (f : d ~{D}~> d') (x : top_carrier (F d)),
      p458_tcolim_rel (existT _ d x)
        (existT _ d' (continuous_map (fmap[F] f) x))
  | p458_tcr_sym : ∀ p q, p458_tcolim_rel p q → p458_tcolim_rel q p
  | p458_tcr_trans : ∀ p q r, p458_tcolim_rel p q →
      p458_tcolim_rel q r → p458_tcolim_rel p r.

(* CONTROL: the same relation valued at the homs' universe [h]. / 控制：在 hms 的宇宙 [h] 中相同的关系价值。 *)
Inductive p458_tcolim_relH@{o h s +| o < h, s <= o +}
  (D : Category@{s h h}) (F : D ⟶ Top@{h o}) :
  p458_tcarr D F → p458_tcarr D F → Type@{h} :=
  | p458_tcrH_point : ∀ (d : D) (x y : top_carrier (F d)), x ≈ y →
      p458_tcolim_relH (existT _ d x) (existT _ d y)
  | p458_tcrH_glue : ∀ (d d' : D) (f : d ~{D}~> d') (x : top_carrier (F d)),
      p458_tcolim_relH (existT _ d x)
        (existT _ d' (continuous_map (fmap[F] f) x))
  | p458_tcrH_sym : ∀ p q, p458_tcolim_relH p q → p458_tcolim_relH q p
  | p458_tcrH_trans : ∀ p q r, p458_tcolim_relH p q →
      p458_tcolim_relH q r → p458_tcolim_relH p r.

(* N20 *)
Fail Definition p458_tcolim_relH_at_o@{o h s +| o < h, s <= o +}
  (D : Category@{s h h}) (F : D ⟶ Top@{h o}) :
  p458_tcarr D F → p458_tcarr D F → Type@{o} :=
  p458_tcolim_relH D F.

(*
CONTROL: the same relation valued in [Prop] fits at [Type@{o}]; the
   mediator respects it up to [inhabited]; the squash eliminates into a
   proposition.

--------
控制：在 [Prop] 中评估的相同关系适用于 [Type@{o}]；中介者在 [inhabited] 之前尊重它；压缩最终转化为一个命题。
*)
Inductive p458_tcolim_prel@{o h s +| o < h, s <= o +}
  (D : Category@{s h h}) (F : D ⟶ Top@{h o}) :
  p458_tcarr D F → p458_tcarr D F → Prop :=
  | p458_tcp_point : ∀ (d : D) (x y : top_carrier (F d)),
      inhabited (x ≈ y) → p458_tcolim_prel (existT _ d x) (existT _ d y)
  | p458_tcp_glue : ∀ (d d' : D) (f : d ~{D}~> d') (x : top_carrier (F d)),
      p458_tcolim_prel (existT _ d x)
        (existT _ d' (continuous_map (fmap[F] f) x))
  | p458_tcp_sym : ∀ p q, p458_tcolim_prel p q → p458_tcolim_prel q p
  | p458_tcp_trans : ∀ p q r, p458_tcolim_prel p q →
      p458_tcolim_prel q r → p458_tcolim_prel p r.

Definition p458_tcolim_prel_at_o@{o h s +| o < h, s <= o +}
  (D : Category@{s h h}) (F : D ⟶ Top@{h o}) :
  p458_tcarr D F → p458_tcarr D F → Type@{o} :=
  p458_tcolim_prel D F.

Lemma p458_tcolim_med_squashed@{o h s +| o < h, s <= o +}
  (D : Category@{s h h}) (F : D ⟶ Top@{h o}) (Z : TopSpace@{o})
  (m : p458_tcarr D F → top_carrier Z)
  (Hp : ∀ d (x y : top_carrier (F d)), x ≈ y →
          m (existT _ d x) ≈ m (existT _ d y))
  (Hm : ∀ d d' (f : d ~{D}~> d') x,
          m (existT _ d x) ≈ m (existT _ d' (continuous_map (fmap[F] f) x)))
  (p q : p458_tcarr D F) :
  p458_tcolim_prel D F p q → inhabited (m p ≈ m q).
Proof.
  induction 1 as [d x y [e]|d d' f x|p q _ [IH]|p q r _ [IH1] _ [IH2]].
  - constructor. exact (Hp d x y e).
  - constructor. exact (Hm d d' f x).
  - constructor. symmetry. exact IH.
  - constructor. transitivity (m q); assumption.
Qed.

Definition p458_squash_prop@{o +} (Z : TopSpace@{o}) (a b : top_carrier Z)
  (P : Prop) (k : a ≈ b → P) (w : inhabited (a ≈ b)) : P :=
  match w with inhabits e => k e end.

(* N21 *)
Fail Definition p458_tcolim_elim@{o h s +| o < h, s <= o +}
  (D : Category@{s h h}) (F : D ⟶ Top@{h o}) (Z : TopSpace@{o})
  (m : p458_tcarr D F → top_carrier Z) (p q : p458_tcarr D F)
  (H : p458_tcolim_prel D F p q) : m p ≈ m q :=
  match H with
  | p458_tcp_point _ _ _ _ _ _ => _
  | p458_tcp_glue _ _ _ _ _ _ => _
  | p458_tcp_sym _ _ _ _ _ => _
  | p458_tcp_trans _ _ _ _ _ _ _ => _
  end.

(* N22 *)
Fail Definition p458_squash_elim@{o +} (Z : TopSpace@{o})
  (a b : top_carrier Z) (w : inhabited (a ≈ b)) : a ≈ b :=
  match w with inhabits e => e end.

(**
** REFUTATION CONSTANTS: the two Refutations satellites and the pieces
       of Exercise 3's printed reading

--------
** 反驳常数：两颗反驳卫星以及练习3的印刷阅读材料的部分内容
*)

(*
CONTROL: the printed (a) refuted, the refuting data, the left
   adjunction and the limit of [G ◯ T] it consists of, restated.

--------
控制：印刷的 (a) 被反驳的，反驳的数据，左附加及其包含的 [G ◯ T] 的极限，重述。
*)
Definition p458_ex3a_literal_refuted :
  Ex3a_left_literal ex3_G1 ex3_T0 → False :=
  ex3a_left_adjoint_literal_refuted.

(*
CONTROL: the same refutation under a CLOSED binder that puts every one
   of its eleven universes strictly above [Set].

--------
控制：同样的反驳在一个封闭的册子下，将其所有十一重宇宙严格置于 [Set] 之上。
*)
Definition p458_ex3a_literal_above_set@{u u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 |
  Set < u, Set < u0, Set < u1, Set < u2, Set < u3, Set < u4, Set < u5,
  Set < u6, Set < u7, Set < u8, Set < u9, u8 < u5, u9 < u2 +} :
  Ex3a_left_literal@{u u5 u0 u1 u2 u9 u3 u4 u6 u8 u7} ex3_G1@{u7 u4 u8}
    ex3_T0@{u6 u8 u7 u5} → False :=
  ex3a_left_adjoint_literal_refuted@{u u0 u1 u2 u3 u4 u5 u6 u7 u8 u9}.

Definition p458_ex3a_counterexample :
  Ex3a_left_refuting_data ex3_G1 ex3_T0 := ex3a_left_counterexample.

Definition p458_ex3_left_adj : ex3_LeftAdj ⊣ ConeImage ex3_G1 ex3_T0 :=
  ex3_left_adj.

Definition p458_ex3_point_limit : Limit (ex3_G1 ◯ ex3_T0) :=
  ex3_point_limit.

(* N23 *)
Fail Definition p458_ex3a_left_at_roof : Limit ex3_T0 :=
  limit_from_cone_right_adjoint ex3_G1 ex3_T0 ex3_LeftAdj ex3_left_adj
    ex3_point_limit.

(*
CONTROL: completeness refuted above the points under [IEM]; no arrow
   index at or below them, constructively.

--------
控制：在 [IEM] 下方的点上方已驳回完整性；没有箭头索引在它们上面或下面，具有建设性。
*)
Definition p458_not_complete_above@{e r s o so +| o < so, o < s,
  s <= r +} :
  IEM@{e} → @Complete@{r s o so} PTopCat@{o so} → False :=
  PTop_not_complete_IEM.

(* N24 *)
Fail Definition p458_not_complete_at_points@{e r o so +| o < so, o <= r +} :
  IEM@{e} → @Complete@{r o o so} PTopCat@{o so} → False :=
  PTop_not_complete_IEM.

Definition p458_no_arrow_index_below@{s o so +| s <= o, o < so +} :
  ArrowIndex@{s so o} PTopCat@{o so} → False :=
  PTop_no_ArrowIndex_below.

(* CONTROL: products refuted above the points under [IEM]. / 控制：上述 [IEM] 下的点已被否定的产品。 *)
Definition p458_iprod_refuted_above@{e s o so +| o < so, o < s +} :
  IEM@{e} → @HasIndexedProducts@{s s s s so o} PTopCat@{o so} → False :=
  PTop_iprod_refuted_IEM.

(* N25 *)
Fail Definition p458_iprod_refuted_at_points@{e o so +| o < so +} :
  IEM@{e} → @HasIndexedProducts@{o o o o so o} PTopCat@{o so} → False :=
  PTop_iprod_refuted_IEM.

(*
CONTROL: products of the Type-valued [Top] refuted at the homs'
   universe under [IEM].

--------
控制：Type 值 [Top] 的产品在 [IEM] 下的同类宇宙中被驳斥。
*)
Definition p458_top_iprod_refuted@{e h o +| o < h +} :
  IEM@{e} → @HasIndexedProducts@{h h h h h h} Top@{h o} → False :=
  Top_iprod_refuted_IEM_canonical.

(* N26 *)
Fail Definition p458_top_iprod_refuted_at_points@{e h o +| o < h +} :
  IEM@{e} → @HasIndexedProducts@{o o o h h h} Top@{h o} → False :=
  Top_iprod_refuted_IEM_canonical.

(*
CONTROL: cocompleteness refuted above the points under [IEM], with
   the points at [Set] too; of [Sets] and of [Top] as well.

--------
控制：在 [IEM] 下的要点上反驳了协同完整性，[Set] 的要点也是如此；以及 [Sets] 和 [Top] 的要点。
*)
Definition p458_not_cocomplete_above@{e r s o so +| o < so, o < s,
  s <= r +} :
  IEM@{e} → @Cocomplete@{r s o so} PTopCat@{o so} → False :=
  PTop_not_cocomplete_IEM.

Definition p458_not_cocomplete_points_at_set@{e r s so +| Set < so,
  Set < s, s <= r +} :
  IEM@{e} → @Cocomplete@{r s Set so} PTopCat@{Set so} → False :=
  PTop_not_cocomplete_IEM.

(* N27 *)
Fail Definition p458_not_cocomplete_at_points@{e r o so +| o < so,
  o <= r +} :
  IEM@{e} → @Cocomplete@{r o o so} PTopCat@{o so} → False :=
  PTop_not_cocomplete_IEM.

Definition p458_sets_not_cocomplete_above@{e r s o so +| o < so, o < s,
  s <= r +} :
  IEM@{e} → @Cocomplete@{r s o so} Sets@{o so} → False :=
  Sets_not_cocomplete_IEM.

Definition p458_top_not_cocomplete_above@{e r s o h +| o < h, o < s,
  s <= r, h <= r +} :
  IEM@{e} → @Cocomplete@{r s h h} Top@{h o} → False :=
  Top_not_cocomplete_IEM.

(**
** REFUTATION CONSTANTS: [ObjDecEq] with the points at [Set], and the
       Type-valued [Top] below its homs

--------
** 反驳常数：[ObjDecEq]，点为 [Set]，以及其 Hom 下面的类型值 [Top]
*)

(*
CONTROL: cocompleteness of [PTopCat] refuted under decidable equality
   of spaces with the points at [Set], by Freyd's argument through the
   transport; by Cantor's with the points above [Set].

--------
控制：在可判等的空间下，[PTopCat] 的共完备性被驳回，通过 Freyd 的论证通过运输；通过 Cantor 的论证，在 [Set] 以上的点处。
*)
Definition p458_not_cocomplete_objdeceq_at_set@{r s so +| Set < so,
  Set < s, s <= r +} :
  ObjDecEq PTopCat@{Set so} → @Cocomplete@{r s Set so} PTopCat@{Set so}
  → False :=
  PTop_not_cocomplete_ObjDecEq.

Definition p458_cantor_objdeceq_above_set@{r s o so +| Set < o, o < so,
  o < s, s <= r +} :
  ObjDecEq PTopCat@{o so} → @Cocomplete@{r s o so} PTopCat@{o so} → False :=
  PTop_not_cocomplete_Cantor_ObjDecEq.

(* N28 *)
Fail Definition p458_cantor_objdeceq_at_set@{r s so +| Set < so, Set < s,
  s <= r +} :
  ObjDecEq PTopCat@{Set so} → @Cocomplete@{r s Set so} PTopCat@{Set so}
  → False :=
  PTop_not_cocomplete_Cantor_ObjDecEq.

(*
CONTROL: a continuous map rebuilt between two hom universes of [Top],
   the continuity field eta-expanded, at [h1 < h2]; the field passed
   through unexpanded where the two hom universes are one.

--------
控制：在 [Top] 的两个同质宇宙之间重建的连续映射，连续性场在 [h1 < h2] 展开 eta；当两个同质宇宙合一时，场通过未展开形式传递。
*)
Definition p458_top_rebuild_up@{o h1 h2 | o < h1, h1 < h2 +}
  {X Y : TopSpace@{o}} (f : ContinuousMorphism@{h1 o} X Y) :
  ContinuousMorphism@{h2 o} X Y :=
  top_rebuild f.

Definition p458_top_rebuild_unexpanded_at_h@{o h | o < h +}
  {X Y : TopSpace@{o}} (f : ContinuousMorphism@{h o} X Y) :
  ContinuousMorphism@{h o} X Y :=
  {| continuous_map := continuous_map f; continuity := continuity f |}.

(* N29 *)
Fail Definition p458_top_rebuild_unexpanded@{o h1 h2 | o < h1, h1 < h2 +}
  {X Y : TopSpace@{o}} (f : ContinuousMorphism@{h1 o} X Y) :
  ContinuousMorphism@{h2 o} X Y :=
  {| continuous_map := continuous_map f; continuity := continuity f |}.

(*
CONTROL: an arrow index of [Top] moves up and down between hom
   universes.

--------
控制：[Top] 的箭头索引在不同的 hom 宇宙之间上下移动。
*)
Definition p458_top_transport_up@{s o h1 h2 | o < h1, h1 < h2 +}
  (AI : ArrowIndex@{s h1 h1} Top@{h1 o}) : ArrowIndex@{s h2 h2} Top@{h2 o} :=
  Top_ArrowIndex_transport AI.

Definition p458_top_transport_down@{s o h1 h2 | o < h2, h2 < h1 +}
  (AI : ArrowIndex@{s h1 h1} Top@{h1 o}) : ArrowIndex@{s h2 h2} Top@{h2 o} :=
  Top_ArrowIndex_transport AI.

(*
CONTROL: completeness of [Top] refuted under [IEM] at a shape universe
   strictly between the points and the homs, and under [ObjDecEq] with
   the points at [Set]; #455's form at and above the homs.

--------
控制：在形状宇宙中，[Top] 的完整性在严格位于点和同态之间的 [IEM] 下被驳回，并且在 [ObjDecEq] 下点位于 [Set]；#455 的形式在同态处及以上。
*)
Definition p458_top_not_complete_below@{e r s h o +| o < s, s < h,
  h <= r +} :
  IEM@{e} → @Complete@{r s h h} Top@{h o} → False :=
  Top_not_complete_below_IEM.

Definition p458_top_not_complete_below_at_set@{r s h +| Set < s, s < h,
  h <= r +} :
  ObjDecEq Top@{h Set} → @Complete@{r s h h} Top@{h Set} → False :=
  Top_not_complete_below_ObjDecEq.

Definition p458_top_not_complete_canonical@{e r s h o +| o < h, h <= s,
  s <= r +} :
  IEM@{e} → @Complete@{r s h h} Top@{h o} → False :=
  Top_not_complete_IEM.

(* N30 *)
Fail Definition p458_top_not_complete_at_points@{e r h o +| o < h,
  h <= r +} :
  IEM@{e} → @Complete@{r o h h} Top@{h o} → False :=
  Top_not_complete_below_IEM@{e r o h o}.

(* N31 *)
Fail Definition p458_top_not_complete_canonical_below@{e r s h o +| o < s,
  s < h, h <= r +} :
  IEM@{e} → @Complete@{r s h h} Top@{h o} → False :=
  Top_not_complete_IEM.

(*
CONTROL: completeness of [CompHaus] refuted under [IEM] at a shape
   universe strictly between the points and the homs; #455's form at and
   above the homs.

--------
控制：在形状宇宙中，[CompHaus] 的完整性在 [IEM] 下被驳斥，该形状宇宙严格位于点和同态之间；#455 的形式在同态处及以上。
*)
Definition p458_comphaus_not_complete_below@{e r s c h o +| o < s, s < h,
  h <= c, h <= r +} :
  IEM@{e} → @Complete@{r s h c} (CompHaus : Category@{c h h}) → False :=
  CompHaus_not_complete_below_IEM.

Definition p458_comphaus_not_complete_canonical@{e r s c h o +| o < h,
  h <= s, h <= c, s <= r +} :
  IEM@{e} → @Complete@{r s h c} (CompHaus : Category@{c h h}) → False :=
  CompHaus_not_complete_IEM_below.

(* N32 *)
Fail Definition p458_comphaus_canonical_below@{e r s c h o +| o < s, s < h,
  h <= c, h <= r +} :
  IEM@{e} → @Complete@{r s h c} (CompHaus : Category@{c h h}) → False :=
  CompHaus_not_complete_IEM_below.

(*
CONTROL: products of [Top] refuted under [IEM] at an index universe
   strictly between the points and the homs.

--------
控制：在索引宇宙中，[IEM] 下驳斥的 [Top] 产品，严格位于点和同态之间。
*)
Definition p458_top_iprod_refuted_below@{e s h o +| o < s, s < h +} :
  IEM@{e} → @HasIndexedProducts@{s s s h h h} Top@{h o} → False :=
  Top_iprod_refuted_below_IEM.

(* N33 *)
Fail Definition p458_top_iprod_below_at_points@{e h o +| o < h +} :
  IEM@{e} → @HasIndexedProducts@{o o o h h h} Top@{h o} → False :=
  Top_iprod_refuted_below_IEM@{e o h o}.

(*
CONTROL: cocompleteness of [Top] refuted under [IEM] at a shape
   universe strictly between the points and the homs, under [ObjDecEq]
   with the points at [Set], and by Cantor's argument between the points
   and the homs as well, its [ObjDecEq] form with the points above
   [Set].

--------
控制：在形状宇宙严格介于点和同态之间的情况下，[Top] 的完备性在 [IEM] 下被否定，在 [ObjDecEq] 下点在 [Set]，并且通过康托的论证在点和同态之间也被否定，其 [ObjDecEq] 形式点在 [Set] 之上。
*)
Definition p458_top_not_cocomplete_between@{e r s h o +| o < s, s < h,
  h <= r +} :
  IEM@{e} → @Cocomplete@{r s h h} Top@{h o} → False :=
  Top_not_cocomplete_IEM.

Definition p458_top_not_cocomplete_at_set@{r s h +| Set < s, s < h,
  h <= r +} :
  ObjDecEq Top@{h Set} → @Cocomplete@{r s h h} Top@{h Set} → False :=
  Top_not_cocomplete_ObjDecEq.

Definition p458_top_not_cocomplete_cantor@{e r s h o +| o < s, s < h,
  h <= r +} :
  IEM@{e} → @Cocomplete@{r s h h} Top@{h o} → False :=
  Top_not_cocomplete_Cantor_IEM.

Definition p458_top_cantor_objdeceq_above_set@{r s h o +| Set < o, o < s,
  s < h, h <= r +} :
  ObjDecEq Top@{h o} → @Cocomplete@{r s h h} Top@{h o} → False :=
  Top_not_cocomplete_Cantor_ObjDecEq.

(* N34 *)
Fail Definition p458_top_not_cocomplete_at_points@{e r h o +| o < h,
  h <= r +} :
  IEM@{e} → @Cocomplete@{r o h h} Top@{h o} → False :=
  Top_not_cocomplete_IEM@{e r o h o}.

(* N35 *)
Fail Definition p458_top_cantor_objdeceq_at_set@{r s h +| Set < s, s < h,
  h <= r +} :
  ObjDecEq Top@{h Set} → @Cocomplete@{r s h h} Top@{h Set} → False :=
  Top_not_cocomplete_Cantor_ObjDecEq.

(** ** Guard: every constant of the six targets / ** 守卫：六个目标的每一个常量 *)

(* Instance/Top/Complete.v / 实例/顶端/完成.v *)
Check PBoxTop.
Check PConv.
Check PDisc.
Check PDisc_PForget.
Check Complete.PDisc_obligation_1.
Check Complete.PDisc_obligation_2.
Check Complete.PDisc_obligation_3.
Check PForget_Continuous.
Check PForget_PreservesLimitCone.
Check PInit.
Check PInit_carrier.
Check PInit_one_PSub.
Check PInit_open.
Check PIsTopology.
Check PPair.
Check PPair_carrier.
Check PPair_open_iff_box.
Check PProd.
Check PProd_carrier.
Check PProd_open.
Check PTop_Cartesian.
Check PTop_Complete.
Check PTop_Complete_apex.
Check PTop_Complete_routes_iso.
Check PTop_Complete_routes_iso_legs.
Check PTop_Complete_via_products.
Check PTop_Complete_via_products_apex.
Check PTop_HasIndexedProducts.
Check PTop_IsIndexedProduct.
Check PTop_Limit_lift.
Check PTop_equalizer_open_iff_PSub.
Check PTop_iprod_open_iff_initial.
Check PTop_iprod_ump.
Check Complete.PTop_iprod_ump_obligation_1.
Check Complete.PTop_iprod_ump_obligation_2.
Check PTop_limit_open_iff_initial.
Check PTop_product_obj.
Check box_not_indexed_product.
Check equalizer_points_monic.
Check iprod_points_jointly_monic.
Check pair_box_union.
Check pair_box_union_topology.
Check pbox_all_false.
Check pbox_all_false_not_product_open.
Check pbox_all_false_open.
Check pbox_at.
Check pbox_no_mediator.
Check pbox_open.
Check pbox_open_inter.
Check pbox_open_proper.
Check pbox_open_respects.
Check pbox_open_union.
Check pbox_open_whole.
Check pbox_proj.
Check pbox_proj_cont.
Check pconv_ind.
Check pconv_ind_cont.
Check pconv_ind_map.
Check pconv_ind_mor.
Check pconv_limit_point_not_open.
Check pconv_open.
Check pconv_open_inter.
Check pconv_open_proper.
Check pconv_open_respects.
Check pconv_open_union.
Check pconv_open_whole.
Check pconv_prod_mediator.
Check pconv_setoid.
Check pdisc_forget_iso.
Check Complete.pdisc_forget_iso_obligation_1.
Check Complete.pdisc_forget_iso_obligation_2.
Check Complete.pdisc_forget_iso_obligation_3.
Check Complete.pdisc_forget_iso_obligation_4.
Check pinit_cone.
Check pinit_cone_leg.
Check pinit_cone_limiting.
Check pinit_cone_med_map.
Check pinit_cone_points.
Check pinit_leg.
Check pinit_leg_cont.
Check pinit_leg_map.
Check pinit_lift.
Check pinit_lift_map.
Check pinit_open.
Check pinit_open_inter.
Check pinit_open_proper.
Check pinit_open_respects.
Check pinit_open_union.
Check pinit_open_whole.
Check pinit_sub.
Check pinit_top.
Check pinit_universal.
Check pinit_weakest.
Check plimit_point.
Check plimit_point_cone.
Check plimit_points_jointly_monic.
Check popen_topology.
Check ppair_exl.
Check ppair_exr.
Check ppair_fam.
Check ppair_fork.
Check ppair_fork_map.
Check ppair_fst.
Check ppair_leg.
Check ppair_snd.
Check pprod_leg.
Check pprod_open_pbox_open.
Check pprod_tuple.
Check pproj.
Check pproper.
Check pproper_topology.
Check ptuple.

(* Instance/Top/Complete/ConeComma.v / 实例/顶部/完整/圆锥逗号.v *)
Check ConeImage.
Check ConeImage_obj.
Check Ex3a_left_literal.
Check Ex3a_left_refuting_data.
Check PDiscCone.
Check PDiscCone_open.
Check PInitCone.
Check PInitCone_obj.
Check PTop_Complete_via_cones.
Check PTop_iprod_cone.
Check PTop_iprod_via_cones.
Check PTop_limit_via_cones.
Check PTop_products_via_cone_comma.
Check PTop_via_cones_apex.
Check PTop_via_cones_cone.
Check cone_adjoints_differ_at_empty_shape.
Check ex3_G1.
Check ex3_LeftAdj.
Check ConeComma.ex3_LeftAdj_obligation_1.
Check ConeComma.ex3_LeftAdj_obligation_2.
Check ConeComma.ex3_LeftAdj_obligation_3.
Check ConeComma.ex3_LeftAdj_obligation_4.
Check ex3_T0.
Check ex3_left_adj.
Check ex3_left_adj_iso.
Check ConeComma.ex3_left_adj_iso_obligation_1.
Check ConeComma.ex3_left_adj_iso_obligation_2.
Check ConeComma.ex3_left_adj_iso_obligation_3.
Check ConeComma.ex3_left_adj_iso_obligation_4.
Check ConeComma.ex3_left_adj_iso_obligation_5.
Check ConeComma.ex3_left_adj_iso_obligation_6.
Check ex3_point_cone.
Check ex3_point_limit.
Check ex3_point_terminal.
Check ConeComma.ex3_point_terminal_obligation_1.
Check ConeComma.ex3_point_terminal_obligation_2.
Check ex3_roof_cone.
Check ex3_roof_from_apex.
Check ex3_roof_no_limit.
Check ex3a_left_adjoint_literal_refuted.
Check ex3a_left_counterexample.
Check limit_from_cone_right_adjoint.
Check pbool_cone.
Check pcone_adj_iso.
Check ConeComma.pcone_adj_iso_obligation_1.
Check ConeComma.pcone_adj_iso_obligation_2.
Check ConeComma.pcone_adj_iso_obligation_3.
Check ConeComma.pcone_adj_iso_obligation_4.
Check ConeComma.pcone_adj_iso_obligation_5.
Check ConeComma.pcone_adj_iso_obligation_6.
Check ConeComma.pcone_adj_iso_obligation_7.
Check pcone_adjunction.
Check pdisc_cone.
Check pdisc_cone_adj_iso.
Check ConeComma.pdisc_cone_adj_iso_obligation_1.
Check ConeComma.pdisc_cone_adj_iso_obligation_2.
Check ConeComma.pdisc_cone_adj_iso_obligation_3.
Check ConeComma.pdisc_cone_adj_iso_obligation_4.
Check ConeComma.pdisc_cone_adj_iso_obligation_5.
Check ConeComma.pdisc_cone_adj_iso_obligation_6.
Check pdisc_cone_adjunction.
Check pempty_diagram.
Check puniform_topology.
Check terminal_of_right_adjoint.

(* Instance/Top/Complete/Refutations.v / 实例/顶端/完整/反驳.v *)
Check CompHaus_not_complete_below_IEM.
Check PTop_ArrowIndex_transport.
Check PTop_iprod_refuted_IEM.
Check PTop_no_ArrowIndex_at_points.
Check PTop_no_ArrowIndex_below.
Check PTop_not_complete_Freyd.
Check PTop_not_complete_IEM.
Check PTop_not_complete_IEM_canonical.
Check PTop_not_complete_ObjDecEq.
Check Top_ArrowIndex_transport.
Check Top_iprod_refuted_IEM_canonical.
Check Top_iprod_refuted_below_IEM.
Check Top_not_complete_below_IEM.
Check Top_not_complete_below_ObjDecEq.
Check pbool_eval_pt.
Check pbool_eval_pt_resp.
Check top_rebuild.

(* Instance/Top/Cocomplete.v / 实例/顶点/完备.v *)
Check PColimit.
Check PColimit_apex.
Check PColimit_inj.
Check PColimit_med_at.
Check PColimit_points.
Check PFinal.
Check PFinalCocone.
Check PFinalCocone_legs.
Check Cocomplete.PFinalCocone_obligation_1.
Check PFinalCocone_points.
Check PFinal_carrier.
Check PFinal_open.
Check PForget_Cocontinuous.
Check PForget_PIndisc.
Check PForget_PreservesColimitCocone.
Check PIndisc.
Check PIndisc_fobj.
Check Cocomplete.PIndisc_obligation_1.
Check Cocomplete.PIndisc_obligation_2.
Check Cocomplete.PIndisc_obligation_3.
Check PIndiscrete.
Check PIndiscrete_carrier.
Check PIndiscrete_open.
Check PSigma.
Check PSigma_open.
Check PSigma_points.
Check PTop_Cocomplete.
Check PTop_Cocomplete_routes_iso.
Check PTop_Cocomplete_routes_iso_injs.
Check PTop_Cocomplete_via_coproducts.
Check PTop_Cocomplete_via_coproducts_apex.
Check PTop_Colimit_lift.
Check PTop_Colimit_lift_apex.
Check PTop_HasIndexedCoproducts.
Check PTop_IsIndexedCoproduct.
Check PTop_colimit_open_iff_final.
Check PTwoIndisc.
Check PTwoIndiscSum.
Check PTwoIndiscSum_injections_differ.
Check PTwoIndiscSum_not_discrete.
Check PTwoIndiscSum_not_indiscrete.
Check PTwoIndiscSum_summand_open.
Check pfinal_cocone_colimiting.
Check pfinal_cocone_colimiting_reflect.
Check pfinal_cocone_inj.
Check pfinal_cocone_med_map.
Check pfinal_cocone_obj.
Check pfinal_desc.
Check pfinal_desc_map.
Check pfinal_finest.
Check pfinal_leg.
Check pfinal_leg_cont.
Check pfinal_leg_map.
Check pfinal_one_map_PQuot.
Check pfinal_open.
Check pfinal_open_inter.
Check pfinal_open_proper.
Check pfinal_open_respects.
Check pfinal_open_union.
Check pfinal_open_whole.
Check pfinal_universal.
Check pforget_indisc_iso.
Check Cocomplete.pforget_indisc_iso_obligation_1.
Check Cocomplete.pforget_indisc_iso_obligation_2.
Check Cocomplete.pforget_indisc_iso_obligation_3.
Check pindisc_cont.
Check pindisc_mor.
Check pindisc_mor_map.
Check pindisc_open.
Check pindisc_open_inter.
Check pindisc_open_proper.
Check pindisc_open_respects.
Check pindisc_open_union.
Check pindisc_open_whole.
Check psigma_case.
Check psigma_case_at.
Check psigma_desc.
Check psigma_inj.

(* Instance/Top/Cocomplete/Refutations.v / 实例/顶端/余宿/反驳.v *)
Check PTop_not_cocomplete_Cantor_IEM.
Check PTop_not_cocomplete_Cantor_ObjDecEq.
Check PTop_not_cocomplete_Freyd.
Check PTop_not_cocomplete_IEM.
Check PTop_not_cocomplete_ObjDecEq.
Check Sets_not_cocomplete_IEM.
Check Top_not_cocomplete_Cantor_IEM.
Check Top_not_cocomplete_Cantor_ObjDecEq.
Check Top_not_cocomplete_Freyd.
Check Top_not_cocomplete_IEM.
Check Top_not_cocomplete_ObjDecEq.
Check cocomp_cantor_diagonal.
Check pcc_Prop.
Check Refutations.pcc_Prop_obligation_1.
Check pcc_contradiction.
Check pcc_enc.
Check pcc_enc_inj.
Check pcc_index.
Check pcc_inj.
Check pcc_leg.
Check pcc_sep.
Check pcc_sep_at.
Check pcc_sum.
Check tcc_contradiction.
Check tcc_enc.
Check tcc_enc_inj.
Check tcc_index.
Check tcc_inj.
Check tcc_leg.
Check tcc_sep.
Check tcc_sep_at.
Check tcc_sum.

(* Instance/Top/Cocomplete/TypeValued.v / 实例/顶部/余积完备/类型值.v *)
Check TSigma.
Check TSigma_carrier.
Check TSigma_open.
Check Top_HasCoequalizers.
Check Top_HasIndexedCoproducts_small.
Check Top_coequalizer_obj.
Check tcoeq_IsCoequalizer.
Check tcoeq_cofork.
Check tcoeq_desc.
Check tcoeq_med.
Check tcoeq_obj.
Check tcoeq_proj.
Check tsig_case.
Check tsig_case_cont.
Check tsig_desc.
Check tsig_inj.
Check tsig_open.
Check tsig_open_inter.
Check tsig_open_proper.
Check tsig_open_respects.
Check tsig_open_union.
Check tsig_open_whole.
Check tsig_setoid.
