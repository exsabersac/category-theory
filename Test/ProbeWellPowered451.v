(**
* Probe for well-powered and co-well-powered categories (issue #451)

    Pins the measured boundaries of Structure/WellPowered.v (Mac Lane
    §V.8, book p. 130) and of the files #451 added or corrected beside it:
    Structure/WellPowered/Counterexample.v, Structure/Pullback/Wide/
    Complete.v, Instance/Sets/WellPowered.v, Instance/Grp/WellPowered.v,
    Instance/Powerset/WellPowered.v, Instance/FinSet/WellPowered.v,
    Adjunction/SAFT/WellPowered.v, Adjunction/SAFT/Sets.v, and the #451
    corrections in Adjunction/SpanningArrow.v and Instance/Variety/
    Spanning.v.  Every negative restates a refusal one of those headers
    quotes or describes, and the positive controls restate their claims
    independently.

    THE IMPORT LIST, measured by comparing [Require] lines.  First
    Structure/WellPowered.v's twenty-one lines verbatim and in order; then
    the lines each other target adds, file by file: Structure/Pullback/
    Wide/Complete.v four, Structure/WellPowered/Counterexample.v one,
    Instance/Sets/WellPowered.v eight, Instance/Grp/WellPowered.v three,
    Instance/Powerset/WellPowered.v three, Instance/FinSet/WellPowered.v
    two, Adjunction/SAFT/WellPowered.v three (Adjunction/SAFT/Sets.v adds
    none), Adjunction/SpanningArrow.v one, Instance/Variety/Spanning.v four,
    and Instance/Variety/Limit.v four, since the spanning corrections were
    measured with that file loaded; then the eleven modules those lines
    were collected from that the first twenty-one do not already name; then
    three supplier modules, which provide constants a negative names but
    whose own headers are not under test: Instance/Ordinal/Large.v
    ([SmallOrd_op_Complete]), Instance/Parallel/Wide.v ([WideParallel])
    and Structure/Equalizer/Wide.v (the wide-equalizer route).  The
    suppliers' own lists are not replayed.  Instance/Ordinal/Large.v's
    includes the standard library's [Coq.Classes.RelationClasses], and
    with it loaded, [Locate] shows the term-level [transitivity] and
    [reflexivity], and [Equivalence], resolving to that library's
    [Prop]-valued classes instead of the setoid layer's ones, which no
    target file sees.  A shorter prefix is what makes a probe pass for no
    reason.  One shadowing the list does carry: Adjunction/SAFT.v is
    imported after Theory/Subobject.v, so the short names [sub_dom] and
    [sub_mono] are [SubobjectIndex]'s fields, and a subobject's are
    written [Subobject.sub_dom] and [Subobject.sub_mono].

    DISCIPLINE.  The instrument was checked both ways: the refutation of an
    absent name is refused for that reason, and wrapping a control in a
    refutation, in a copy of this WHOLE file, stops the build with the
    report that the guarded command had been accepted (done twice, at
    [p451_trivial_small] and at [p451_svariety_hwp]).  Every negative
    other than that instrument is a [Definition] or an [Example], never a
    [Check], so that an open evar or a missing instance cannot satisfy it;
    N22, the one INSTANCE negative, is a [Definition] whose body is a
    hole.  Each negative was stripped of its refutation keyword in a copy
    of this WHOLE file, one at a time, compiled, and its error read; the
    kind recorded is the kind of that error, and each has a positive
    control beside it naming the same library constants.  Every UNIVERSE
    negative is a top-level definition whose universes are declared in its
    own binder or left to inference, never those of a [Section], so that
    the stripped error names the bound ("... because h < o") rather than
    the rigidity of a [Section] universe; the one [Section] holding a
    negative (N9) declares no universe, and its refusal is about the sort
    of an elimination, not a level.
    Quotations are Rocq 9.1.1's under this file's import list; Rocq prints
    the "cannot unify" parenthetical with the short names in scope, and a
    universe the stripped copy names after itself and a serial number is
    written <anon>.  The file also compiles on Coq 8.19.2 and 8.20.1, its
    whole dependency closure rebuilt on each, and the stripped copies were
    compiled there as well.  Under 8.20.1 every one is refused with the
    same kind, and every quotation below is found in its error except N7's
    chain (checked by a script over the copies).  Under 8.19.2 every one is
    refused at the same construct; seven of the universe refusals (N1-N3,
    N10, N14, N20, N21) print there as type mismatches whose two sides
    differ only in their universe instances, with no universe-inconsistency
    clause, and N9 prints as "Case analysis on sort Type is not allowed for
    inductive definition ex.".

    KINDS.  Twenty-three refutations, counted as the lines that open with
    the refutation keyword: NAME-ABSENCE (the instrument), UNIVERSE (N1-N8,
    N10, N11, N14-N16, N19-N21), TYPING (N9, N17, N18), CONVERSION (N12,
    N13) and INSTANCE (N22).

    ** The pin

    N1 (UNIVERSE).  [WellPowered] pins the index at or below the hom
    universe, and the trivial witness (the index [SubObj x] itself) is
    refused under it at [Sets@{o so}]:
      The term "wp_trivial X" has type "WellPoweredAt@{<anon> so <anon> o
      <anon>} X" while it is expected to have type "WellPoweredAt@{w so s
      o t} X" (universe inconsistency: Cannot enforce <anon> = w because
      w <= o < so <= <anon>).
    The controls: the unpinned per-object record takes the trivial index
    at [Sets]; a copy of [WellPowered] with only the pin [w <= h] deleted
    ([p451_WellPowered_unpinned]) accepts the same body at [Sets], so the
    pin is what N1 meets; and [trivial_small] is accepted where the objects
    sit at or below the homs ([o <= h]).

    N2 (UNIVERSE).  Instance/Sets/WellPowered.v's witness one universe up
    is refused at the pin, [WellPowered@{so o o so so} Sets@{o so}]:
      The term "Sets_WellPoweredAt_up X" has type "WellPoweredAt@{<anon>
      <anon> <anon> o <anon>} X" while it is expected to have type
      "WellPoweredAt@{o so so o so} X" (universe inconsistency: Cannot
      enforce o = so because o < so).
    That is the refusal that file's header quotes.  The controls:
    [Sets_WellPoweredAt_up@{o so so} X] is accepted per object, and at
    exactly N2's type and universe block the conditional
    [Sets_WellPowered_untruncate U] is accepted; an [eq_refl] readback
    shows the conditional witness IS Structure/WellPowered.v's generic
    [wp_of_classifier] at [Sets_Classifier U].

    N3 (UNIVERSE).  The same at [Grp@{o h}] with [h < o]:
      The term "Grp_WellPoweredAt_up G" has type "WellPoweredAt@{<anon> o
      o h <anon>} G" while it is expected to have type "WellPoweredAt@{h
      o o h o} G" (universe inconsistency: Cannot enforce o = h because
      h < o).
    Instance/Grp/WellPowered.v's header quotes the same; the control is
    [Grp_WellPoweredAt_up@{o o h} G].  No pinned [Grp] witness exists in
    tree, so N3 has no pinned control.

    ** Well-poweredness is consumed

    N4, N5, N6 (UNIVERSE).  At the adjoint-functor regime,
    [C : Category@{o h h}] with [h < o] and [comp : Complete@{h h h o}],
    the class [{ m : SubObj x & P m }] (N4) and the identity family on
    [SubObj x] (N5) are refused by the well-poweredness-free
    [complete_intersection_IsIntersection]:
      Found type "∃ m : SubObj x, P m" where "?J" was expected (unable to
      find a well-typed instantiation for "?J": cannot ensure that
      "Type@{max(o,h)}" is a subtype of "Type@{<anon>}").
    and, for N5, the same with "SubObj x" found.  That is the text
    Structure/WellPowered.v's header quotes, a universe comparison
    reported while instantiating an evar.  N6 peels it: the same class fed
    to [Complete_HasWidePullbacks comp] directly, the index now explicit,
    gives
      The term "∃ m : SubObj x, P m" has type "Type@{max(o,h)}" while it
      is expected to have type "Type@{h}" (universe inconsistency: Cannot
      enforce o <= h because h < o).
    The controls: [wellpowered_complete_has_intersections] and
    [wellpowered_complete_intersection_all] given [WellPowered C] at the
    same regime; a family indexed at or below [h], through both
    [complete_intersection_IsIntersection] and the wide pullback; and the
    very terms of N4 and of N5 with the bound turned round ([o <= h]),
    [p451_class_small_objects] and [p451_all_small_objects], both
    accepted, so the bound [h < o] is what each of N4 and N5 meets.

    N7 (UNIVERSE).  At [Sets@{o so}] with [Sets_Complete], the identity
    family on [SubObj X] without well-poweredness:
      The term "m" has type "SubObj@{so o} X" while it is expected to have
      type "SubObj@{<anon> <anon>} ?x" (universe inconsistency: Cannot
      enforce o = <anon> because o < <anon> <= <anon> <= <anon>).
    The chain printed is not stable: Structure/WellPowered.v's header
    quotes "o < so <= ...", measured with [X : Sets@{o so}] as a
    [Section] [Context]; this file, with [X] a binder of the definition,
    prints the chain above under Rocq 9.1.1 and the header's "o < so <=
    <anon> <= <anon>" under Coq 8.20.1, for the same refusal.  Measured
    under Rocq 9.1.1 in copies of this whole file: with [X] in a
    [Section]'s [Context] the chain is "o < so <= <anon> <= <anon>",
    whether or not the [Section] declares [o < so]; with [X] a binder
    inside a [Section] that declares [Universes o so] and [o < so], it is
    "o < <anon> <= <anon> <= <anon>", as here.
    The controls: [wellpowered_complete_intersection_all] given an abstract
    [WellPowered Sets], the same fed [Sets_WellPowered_untruncate U], and a
    family indexed at the carrier universe.

    N8 (UNIVERSE), N9 (TYPING).  Arbitrary large families, the two readings
    Structure/WellPowered.v's "WHY CLASSES" paragraph measures.  N8, the
    typed image of [S : J → SubObj x] with [J : Type@{o}]:
      The term "∃ j : J, S j ≈ m" has type "Type@{max(o,<anon>)}" while it
      is expected to have type "Type@{<anon>}" (universe inconsistency:
      Cannot enforce o <= <anon> because <anon> <= <anon> < o).
    Its control is the same class for [J] at or below [h], accepted.  N9,
    the greatest-lower-bound step for the [Prop]-truncated image, whose
    [_prop] intersection and lower bounds are accepted (the controls
    [p451_trunc_meet] and [p451_trunc_le]):
      Incorrect elimination in the inductive type "ex": the return type
      has sort "Type" while it should be SProp or Prop.
    The header's quotation of this reads "Type@{h}": with [Set Printing
    Universes], which this file does not set, the same refusal prints the
    sort with its universe (measured in a copy of this file: "ex@{}" and
    "Type@{<anon>}", the universe here coming from the [Section]'s
    [Context] and so unnamed; and "ex@{}" and "Type@{h}", the header's
    text, in a [Section] declaring [Universes o h] with [h < o] over
    [C : Category@{o h h}] and [J : Type@{o}]).
    Two controls take a [Type]-valued witness in place of the truncated
    one, both accepted in the same [Section]: [p451_typed_greatest], the
    per-member step, and [p451_typed_greatest_full], the whole step N9
    attempts, over the typed image's intersection [p451_typed_meet], so
    that the truncation is the only difference from N9.

    ** The wide pullbacks

    N10 (UNIVERSE).  Structure/Pullback/Wide/Complete.v's reason for not
    going through Structure/Equalizer/Wide.v: [WideParallel J] is
    hand-pinned at object universe [Set], and [comp (WideParallel J)] at
    [Complete@{h h h o}] with [Set < h] is refused:
      The term "WideParallel J" has type "Category@{Set <anon> <anon>}"
      while it is expected to have type "Category@{h h h}" (universe
      inconsistency: Cannot enforce Set = h).
    the text that header quotes.  No "because" clause is printed even with
    [Set < h] declared, [h] being a universe bound by the definition; the
    attribution is fixed by the control [p451_wideparallel_at_set], the
    same application at [Complete@{h Set h o}], which is accepted, so the
    shape-object slot is exactly what N10 meets.  The second control is the
    route taken, [Complete_HasWidePullbacks comp] at the regime.

    N11 (UNIVERSE).  [complete_wide_pullback]'s index must lie at or below
    [Complete]'s shape-object universe; at [J : Type@{o}], applied with the
    index explicit:
      The term "J" has type "Type@{o}" while it is expected to have type
      "Type@{<anon>}" (universe inconsistency: Cannot enforce o <= <anon>
      because <anon> <= <anon> < o).
    The control is the same application at [J : Type@{h}].

    N12, N13 (CONVERSION).  Structure/WellPowered.v's STRENGTHS, at
    [Indiscrete bool] completed by [Indiscrete_Complete true], where every
    hom is [unit] and ≈ is Leibniz equality.  The controls: the product
    mediator and the wide pullback's leg reduce to [tt] by [eq_refl]; the
    wide pullback's mediator IS [tt] up to ≈, by case analysis on [unit].
    N12, that mediator by [eq_refl]:
      (cannot unify "unique_obj (ump_wide_pullbacks (complete_wide_pullback
      p451_IC_comp p451_fam) false p451_cone p451_cone_commutes)" and
      "()")
    N13, the header's remark that Adjunction/GAFT.v's
    [Complete_HasEqualizers] would not help: its equalizer's mediator,
    whose ≈ to [tt] is again a control, by [eq_refl]:
      (cannot unify "unique_obj (eq_desc (projT2 (projT2 (equalizer ()
      ()))) () eq_refl)" and "()")

    ** Non-vacuity, and where the pin excludes something

    N14 (UNIVERSE).  [trivial_small SmallOrd_op_Proset] is accepted (the
    homs raised to the objects), and so is
    [wellpowered_complete_intersection_all] at [SmallOrd_op_Complete] over
    an abstract witness; the two together are refused:
      The term "SmallOrd_op_Complete" has type "Complete@{<anon> <anon>
      <anon> <anon>}" while it is expected to have type "Complete@{<anon>
      <anon> <anon> <anon>}" (universe inconsistency: Cannot enforce
      <anon> = <anon> because <anon> <= <anon> <= <anon> < <anon>).
    The equation is on [Complete]'s object slot.  [trivial_small] asks the
    objects to sit at or below the homs, where its index lives, and the
    theorem asks the index to sit at or below [Complete]'s shape-object
    universe, so the objects would have to sit at or below the shape
    universe; [SmallOrd^op]'s shape universe lies strictly below its
    objects.  The header quotes the refusal in that shape.

    N15 (UNIVERSE).  Instance/Powerset.v's own [Subsets_Complete], homs at
    [Set] and objects at [o] with [Set < o], cannot meet the trivial
    witness, which needs the objects at or below the homs:
      The term "Subsets_Complete" has type "Complete@{<anon> <anon> Set o}"
      while it is expected to have type "Complete@{<anon> <anon> Set
      <anon>}" (universe inconsistency: Cannot enforce <anon> = o because
      <anon> < o).
    The controls: [Subsets_Complete] at its own homs, and
    Instance/Powerset/WellPowered.v's route, [Subsets_Complete_free] with
    [Subsets_WellPowered] at [o <= u], fed to the theorem.

    N16 (UNIVERSE).  Structure/WellPowered/Counterexample.v's verdict
    depends on the hom instantiation.  [AntichainTop_WellPoweredAt_up],
    the pinned datum at the top object for [i < h], is refused at [h <= i]:
      The term "AntichainTop_WellPoweredAt_up" has type
      "WellPoweredAt@{<anon> <anon> <anon> <anon> <anon>} None" while it is
      expected to have type "WellPoweredAt@{h o s h t} None" (universe
      inconsistency: Cannot enforce <anon> = i because <anon> < <anon> <=
      i).
    The controls: the same constant at [i < h]; [AntichainTop_trivial], one
    universe up; and, at N16's universe block together with [w <= h] for
    the witness's index, the refutation [AntichainTop_not_WellPowered]
    applied to a [WellPowered] witness.

    ** The routes to [Sets] at the pin without [Untruncate]

    N17, N18 (TYPING), N19 (UNIVERSE), the other three refusals
    Instance/Sets/WellPowered.v's "WHY THE PINNED WITNESS USES
    [Untruncate]" quotes (the first it quotes is N2's), each reproduced
    here with the text quoted there.
    N17, a preimage truncated by [inhabited]:
      Incorrect elimination of "proj2_sig p" in the inductive type
      "inhabited": the return type has sort "Type" while it should be
      SProp or Prop.
    Its control carries the preimage as data.  N18, the impredicative
    [Powerset_squash] the classifier uses:
      The term "q" has type "∃ a : A, m a ≈ b" while it is expected to have
      type "?Q" (unable to find a well-typed instantiation for "?Q":
      cannot ensure that "Type" is a subtype of "Prop").
    a comparison of sorts, [Type] against [Prop], not of levels.  Its
    control is [Untruncate] inverting exactly that truncation.  N19,
    Lattice.v's [sub_intersection] at [Sets_HasWidePullbacks] over the
    index one universe up:
      Found type "option (∃ i : wp_index (Sets_WellPoweredAt_up X), P
      (wp_to (Sets_WellPoweredAt_up X) i))" where "option ?A" was expected
      (unable to find a well-typed instantiation for "?A": cannot ensure
      that "Type@{max(o,<anon>)}" is a subtype of "Type@{<anon>}").
    Its control is the same term over [Sets_WellPoweredAt_untruncate U X].

    ** The spanning-arrow corrections

    N20, N21 (UNIVERSE).  [Complete_HasWidePullbacks] inhabits the class at
    [SVariety E] (the control [p451_svariety_hwp]) and at [Sets], where it
    reads back at the universes of Instance/Sets/SubobjectLattice.v's
    direct [Sets_HasWidePullbacks] (the controls
    [p451_sets_hwp_from_complete] and [p451_sets_hwp_direct], ascribed the
    same type), but it does not feed Adjunction/SpanningArrow.v's
    [spanning_solution_set], which the controls accept over an abstract
    class.  N20, at [SVariety_Forget E]:
      The term "Complete_HasWidePullbacks (SVariety_Complete E)" has type
      "HasWidePullbacks@{a c b c} (SVariety@{...} E)" while it is expected
      to have type "HasWidePullbacks@{d e f c} (SVariety@{...} E)"
      (universe inconsistency: Cannot enforce a = d because a <= <anon> <
      <anon> <= <anon> <= <anon> <= d).
    N21, at [Id[Sets]]:
      The term "Complete_HasWidePullbacks Sets_Complete" has type
      "HasWidePullbacks@{a a b a} Sets@{a b}" while it is expected to have
      type "HasWidePullbacks@{c d e f} Sets@{f e}" (universe
      inconsistency: Cannot enforce d = f because f < <anon> <= <anon> <=
      d).
    Each <anon> of the heads is renamed to one letter there, and the
    [SVariety] instances elided.  N21 is the shape the correction in
    Adjunction/SpanningArrow.v quotes: the class's second universe [d]
    must lie strictly above the carrier [f], and completeness gives it at
    the carrier.  The corrections quote N20 as "Cannot enforce <carrier> =
    <the class's second universe> because <carrier> < ...", measured with
    the preservation hypothesis [GP] as a [Section] hypothesis; here [GP]
    is an ordinary binder, and Rocq reports the index slot's equation
    first.  Both forms were measured under this file's import list: the
    [Section] form, in a copy of this file, prints the corrections' shape;
    the binder form is kept because a [Section] hypothesis can itself fix
    universes, and the refusal stands without one.

    N22 (INSTANCE).  With Structure/Pullback/Wide/Complete.v and
    Instance/Variety/Limit.v both loaded, class search finds no
    [HasWidePullbacks (SVariety E)]:
      Cannot infer this placeholder of type "HasWidePullbacks (SVariety E)"
      (no type class instance found)
    That [Complete_HasWidePullbacks] is a definition and not an instance
    is not the whole reason.  Registering it alone as a local instance
    leaves the hole refused with the same parenthetical, and so does
    registering [SVariety_Complete] alone as a local hint for
    [typeclass_instances]: [Complete] is a plain definition, a Π-type over
    diagrams and not a class, and [SVariety_Complete] is no instance, so
    search has no chain from the class through [Complete_HasWidePullbacks]
    to [SVariety_Complete] unless both are registered (both refusals
    measured in copies of this whole file).  With both registered locally
    the hole resolves: the [Section] [SearchBoth] below accepts it as
    [p451_n22_hwp_by_search_both], and [p451_n22_search_finds] reads back
    by [eq_refl] that what search found IS [Complete_HasWidePullbacks
    (SVariety_Complete E)].  The other control is [p451_svariety_hwp],
    the class supplied by hand.  Test/ProbeVarietySpanning448.v's P1 pins
    the same absence with a shorter import list that loads neither file.

    CONTROLS WITHOUT A NEGATIVE.  The exhaustiveness clause [wp_to_from],
    the headline and its dual at their stated types; [CoWellPowered C] IS
    [WellPowered (C^op)] by [eq_refl]; the subobject the headline returns
    IS the [complete_intersection] of the small reindexed family by
    [eq_refl]; [FinSet_WellPowered] at the pin with its index read back as
    [Fin.t n → Fin.t 2] by [eq_refl]; [Indiscrete_types_has_intersections]
    and [Subsets_intersection_all_not_top] at their stated types; the index
    of Adjunction/SAFT/WellPowered.v's [WellPowered_SubobjectIndex] IS the
    well-powered index by [eq_refl]; and [SubobjectIndex_not_exhaustive].

    FORMERLY REFUSED, NOW CONTROLS.  Two binders the #451 review fixed,
    kept here in the [Section] form the fix was stated in, since a
    [Section]'s rigid universes can only make an acceptance harder.
    [SAFT_of_WellPowered] with [WellPowered]'s [t] declared strictly below
    [SAFT]'s slot [u] ([p451_saft_of_wp], beside [SAFT] applied to the
    bridge directly) was measured refused before its binder named [u], as
    Adjunction/SAFT/WellPowered.v's header records.
    [SubobjectCover_Id_Sets_absurd] with [cogen_prod]'s slot [u] declared
    strictly above the object universe ([p451_cover_above]) was measured
    refused before its binder was declared, and the slot strictly below
    ([p451_cover_below]) is the scratch acceptance Adjunction/SAFT/Sets.v's
    header records.  They break if either binder returns to minimization.
    The guard block at the end names seventy-three constants of the #451
    files (counted as its lines), so that a rename breaks this file.

--------
* 探讨充足能量和协充足能量范畴（问题 #451）

固定了 Structure/WellPowered.v（Mac Lane §V.8，书页 130）的测量边界，以及紧挨着它添加或修正的 #451 文件：Structure/WellPowered/Counterexample.v、Structure/Pullback/Wide/Complete.v、Instance/Sets/WellPowered.v、Instance/Grp/WellPowered.v、Instance/Powerset/WellPowered.v、Instance/FinSet/WellPowered.v、Adjunction/SAFT/WellPowered.v、Adjunction/SAFT/Sets.v，以及 Adjunction/SpanningArrow.v 和 Instance/Variety/Spanning.v 中的 #451 修正内容。每个否定都重申了其中一个标题所引用或描述的拒绝，而肯定的控制则独立重申它们的主张。

通过比较 [Require] 行来衡量的导入列表。第一
 Structure/WellPowered.v 的二十一行逐字且按顺序排列； 然后
 对方目标逐个文件添加的行：Structure/Pullback/
 Wide/Complete.v 四、Structure/WellPowered/Counterexample.v 一、
 Instance/Sets/WellPowered.v 八个，Instance/Grp/WellPowered.v 三个，
 Instance/Powerset/WellPowered.v 三、Instance/FinSet/WellPowered.v
 二、Adjunction/SAFT/WellPowered.v 三（Adjunction/SAFT/Sets.v 添加
 无），Adjunction/SpanningArrow.v 一，Instance/Variety/Spanning.v 四，
 和 Instance/Variety/Limit.v 四，因为跨度修正是
 加载该文件后进行测量； 然后是十一个模块那些行
 是从前二十一个尚未命名的收集而来的； 然后
 三个供应商模块，它们提供常量的负名称，但是
 其自己的标头未接受测试：Instance/Ordinal/Large.v
 ([SmallOrd_op_Complete])、实例/并行/Wide.v ([WideParallel])
 Structure/Equalizer/Wide.v（宽均衡器路线）。供应商自己的列表不会被重放。Instance/Ordinal/Large.v 包含标准库的 [Coq.Classes.RelationClasses]，并且加载后，[Locate] 显示术语级的 [transitivity] 和 [reflexivity]，以及 [Equivalence]，解析为该库的 [Prop] 值的类，而不是集同层的类，任何目标文件都看不到它们。一个较短的前缀会让探针无缘无故地通过。遮蔽该列表的确有效：Adjunction/SAFT.v 在 Theory/Subobject.v 之后被导入，因此短名称 [sub_dom] 和 [sub_mono] 是 [SubobjectIndex] 的字段，而子对象的字段则写作 [Subobject.sub_dom] 和 [Subobject.sub_mono]。

纪律。该工具进行了双向检查：因为缺少名称的反驳而被拒绝，并且在此整个文件的副本中将一个控制包裹在反驳中，会通过报告受保护命令已被接受而停止构建（在 [p451_trivial_small] 和 [p451_svariety_hwp] 两次完成）。除了该工具之外的每个负值都是 [Definition] 或 [Example]，从不是 [Check]，因此一个开放的 evar 或缺失的实例无法满足它；N22，唯一的 INSTANCE 负值，是一个 [Definition]，其主体是一个空洞。每个否定在这个完整文件的副本中一次去掉其反驳关键字，编译后读取其错误；记录的类型是该错误的类型，并且每个旁边都有一个阳性对照，命名相同的库常量。每个 UNIVERSE 否定都是一个顶级定义，其 universes 在其自己的绑定器中声明或留给推导，从不使用 [Section] 的 universes，因此去掉的错误命名了绑定的（"...因为 H < o“），而不是[Section]宇宙的刚性;持有负数（N9）的那个[Section]宣告无宇宙，其拒绝属于一种消去，而非层级。引号为该文件导入列表中的 Rocq 9.1.1;Rocq 打印”无法统一“括号，作用域中的短名称，并写入一个宇宙，其被剥离的副本命名为自身后，序列号。<anon>该文件还可在 Coq 8.19.2 和 8.20.1 上编译，其
    整个依赖关闭在每个人上重建，剥离的复制品是
    也在那里编译。根据8.20.1，所有申请均被拒绝
    同一种，且以下所有引文均在其错误中，唯独N7的
    链（通过脚本检查副本）。在8.19.2
    在同一构造中拒绝;宇宙中有七个拒绝（N1-N3，
    N10、N14、N20、N21）在该处印刷为两面不符的字体
    仅在它们的宇宙实例中有所不同，没有宇宙不一致
    N9 打印为“不允许对排序类型进行案例分析，适用于
    归纳定义示例“。

种类。二十三条反驳，计算为以反驳关键词开头的行：NAME-ABSENCE（工具）、UNIVERSE（N1-N8、N10、N11、N14-N16、N19-N21）、TYPING（N9、N17、N18）、CONVERSION（N12、N13）和INSTANCE（N22）。

** 连接针

N1（宇宙）。[WellPowered] 将索引固定在同源宇宙或以下，并且在 [Sets@{o so}] 下拒绝了平凡证人（索引 [SubObj x] 本身）：
  术语 "wp_trivial X" 的类型是 "WellPoweredAt@{<anon> so <anon> o <anon>} X"，而期望的类型是 "WellPoweredAt@{w so s o t} X"（宇宙不一致：无法强制 <anon> = w，因为 w <= o < so <= <anon>）。控制：未固定的每对象记录在 [Sets] 处采用简单索引；一个仅删除了固定 [w <= h] 的 [WellPowered] 副本（[p451_WellPowered_unpinned]）在 [Sets] 处接受相同的主体，因此固定是 N1 遇到的；而 [trivial_small] 在对象位于 homs 处或以下时被接受（[o <= h]）。

N2（宇宙）。实例/Sets/WellPowered.v 中的 witness one universe up 在引脚处被拒绝，[WellPowered@{so o o so so} Sets@{o so}]：
      术语“Sets_WellPoweredAt_up X”的类型是“WellPoweredAt@{<anon> <anon> <anon> o <anon>} X”，而预期类型是“WellPoweredAt@{o so so o so} X”（宇宙不一致：无法强制 o = so，因为 o < so）。这就是文件头中引用的拒绝原因。控制：
[Sets_WellPoweredAt_up@{o so so} X] 按对象接受，并且在恰好 N2 的类型和宇宙下阻止条件下，[Sets_WellPowered_untruncate U] 被接受；[eq_refl] 的回读显示条件见证是 Structure/WellPowered.v 的通用 [wp_of_classifier] 位于 [Sets_Classifier U]。

N3（UNIVERSE）。在 [Grp@{o h}] 与 [h < o] 中相同：
      术语 “Grp_WellPoweredAt_up G”的类型为 “WellPoweredAt@{<anon> o o h <anon>} G”，而预期类型为 “WellPoweredAt@{h o o h o} G”（宇宙不一致：无法强制 o = h，因为 h < o）。
    Instance/Grp/WellPowered.v 的头部引用相同；控制是 [Grp_WellPoweredAt_up@{o o h} G]。在树中不存在固定的 [Grp] 证据，因此 N3 没有固定控制。

** 强大能力已消耗

N4、N5、N6（宇宙）。在伴随函子机制下，
    [C : Category@{o h h}] 与 [h < o] 和 [comp : Complete@{h h h o}]，
    类 [{ m : SubObj x & P m }]（N4）以及在 [SubObj x]（N5）上的恒等族被无完备性约束的 [complete_intersection_IsIntersection] 拒绝：
      找到类型 “∃ m : SubObj x, P m”，但期望的是 “?J”（无法为 “?J” 找到类型正确的实例化：无法保证 “Type@{max(o,h)}” 是 “Type@{<anon>}” 的子类型）。对于 N5，情况相同，但找到的是 “SubObj x”。这就是 Structure/WellPowered.v 的头部引文，在实例化一个 evar 时报告的宇宙比较。N6 对其进行剥离：同一类直接喂给 [Complete_HasWidePullbacks comp]，索引现在已显式，生成
  术语“∃ m : SubObj x, P m”的类型是“Type@{max(o,h)}”，而期望的类型是“Type@{h}”（宇宙不一致：无法强制 o <= h，因为 h < o）。控制：[wellpowered_complete_has_intersections] 和 [wellpowered_complete_intersection_all] 在相同制度下给定 [WellPowered C]；一个索引在 [h] 或以下的家庭，通过 [complete_intersection_IsIntersection] 和广泛的回撤；以及 N4 和 N5 的具体条款，当边界翻转（[o <= h]）时，[p451_class_small_objects] 和 [p451_all_small_objects] 都被接受，因此边界 [h < o] 是 N4 和 N5 各自满足的条件。

N7（宇宙）。在 [Sets@{o so}] 使用 [Sets_Complete] 时，[SubObj X] 上的身份族在没有充分强大的情况下：
      术语“m”的类型是“SubObj@{so o} X”，而它预期的类型是“SubObj@{<anon> <anon>} ?x”（宇宙不一致：无法强制 o = <anon> 因为 o < <anon> <= <anon> <= <anon>）。打印的链不稳定：Structure/WellPowered.v 的头部引用了“o < so <= ...”，使用 [X : Sets@{o so}] 测量为 [Section] [Context]；这个文件，包含 [X] 的定义绑定器，在 Rocq 9.1.1 下打印上述链，而在 Coq 8.20.1 下打印头部的“o < so <= <anon> <= <anon>”，原因相同。根据 Rocq 9.1.1 测量，在此整个文件的副本中：在 [Section] 的 [Context] 中使用 [X] 时，链为“o < so <= <anon> <= <anon>”，无论 [Section] 是否声明 [o < so]；在 [Section] 内使用 [X] 并声明 [Universes o so] 和 [o < so] 时，链为“o < <anon> <= <anon> <= <anon>”，如这里所示。控制：将抽象 [WellPowered Sets] 给定 [wellpowered_complete_intersection_all]，同样输入 [Sets_WellPowered_untruncate U]，及以载体宇宙为索引的族。

N8（宇宙）、N9（类型）。任意大的族，两个读法
    Structure/WellPowered.v 的“为什么使用类”段落测量。N8，
    [S : J → SubObj x] 与 [J : Type@{o}] 的类型化映像：
      术语 “∃ j : J, S j ≈ m” 的类型为 “Type@{max(o,<anon>)}”，而其
      预期类型为 “Type@{<anon>}”（宇宙不一致：无法强制 o <= <anon> 因为 <anon> <= <anon> < o）。其控制在 [J] 在 [h] 处或以下时为相同的类，被接受。N9，[Prop] 截断图像的最大下界步骤，其 [_prop] 交集和下界已被接受（控制项 [p451_trunc_meet] 和 [p451_trunc_le]）：在归纳类型“ex”中的不正确消除：返回类型为“Type”，而它应该是 SProp 或 Prop。该头部的引用内容为“Type@{h}”：带有 [Set Printing Universes]，而这个文件没有设置，相同的拒绝会打印带有其宇宙的排序（在该文件的副本中测量：“ex@{}” 和 “Type@{<anon>}”，这里的宇宙来自 [Section] 的 [Context]，因此未命名；以及 “ex@{}” 和 “Type@{h}”，头部文本，在 [Section] 中声明 [Universes o h]，并以 [h < o] 作用于 [C : Category@{o h h}] 和 [J : Type@{o}]）。两个控制使用一个 [Type] 值的见证代替截断的见证，两者都在相同的 [Section] 中被接受：[p451_typed_greatest]，每个成员的步骤，以及 [p451_typed_greatest_full]，整个步骤 N9 尝试，作用于类型化图像的交集 [p451_typed_meet]，因此截断是与 N9 唯一的不同。

** 大幅回调

N10（宇宙）。Structure/Pullback/Wide/Complete.v 未通过 Structure/Equalizer/Wide.v 的原因：[WideParallel J] 在对象宇宙 [Set] 处被手动固定，且 [comp (WideParallel J)] 在 [Complete@{h h h o}] 与 [Set < h] 处被拒绝：
      术语 “WideParallel J” 的类型为 “Category@{Set <anon> <anon>}”，
      而期望的类型为 “Category@{h h h}”（宇宙不一致：无法强制 Set = h）。头部引用的文本。即使声明了 [Set < h]，[h] 作为定义约束的宇宙，也不会打印任何 “because” 子句；归属由控制 [p451_wideparallel_at_set] 固定，应用于 [Complete@{h Set h o}] 的相同应用被接受，因此形状对象槽正好符合 N10。第二个控制是所采取的路径，即 [Complete_HasWidePullbacks comp] 在该制度下。

N11（宇宙）。[complete_wide_pullback] 的索引必须位于或低于 [Complete] 的形状对象宇宙；在 [J : Type@{o}]，上下文以显式索引应用：
  术语 “J” 的类型为 “Type@{o}”，而期望类型为 “Type@{<anon>}”（宇宙不一致：无法强制 o <= <anon> 因为 <anon> <= <anon> < o）。
  控制是 [J : Type@{h}] 的相同应用。

N12, N13（转换）。Structure/WellPowered.v 的 STRENGTHS，在 [Indiscrete bool] 由 [Indiscrete_Complete true] 完成，其中每个 hom 为 [unit]，≈ 是 Leibniz 等式。控制条件：乘积中介和宽拉回的腿通过 [eq_refl] 归结为 [tt]；宽拉回的中介通过对 [unit] 的情况分析在 ≈ 意义下是 [tt]。N12，由 [eq_refl] 的那个中介者：
      （无法统一 "unique_obj (ump_wide_pullbacks (complete_wide_pullback p451_IC_comp p451_fam) false p451_cone p451_cone_commutes)" 和 "()"）
    N13，标题中的注释说 Adjunction/GAFT.v 的 [Complete_HasEqualizers] 无法帮忙：它的等化器的中介者，其与 [tt] 的近似又是一个控制，由 [eq_refl] 给出：
      （无法统一 "unique_obj (eq_desc (projT2 (projT2 (equalizer () ()))) () eq_refl)" 和 "()"）

** 非空性，以及针头排除某物的地方

N14（宇宙）。[trivial_small SmallOrd_op_Proset] 被接受（将同态提升到对象上），[wellpowered_complete_intersection_all] 在 [SmallOrd_op_Complete] 上对一个抽象证人也是被接受的；但两者一起被拒绝：
      术语 "SmallOrd_op_Complete" 的类型是 "Complete@{<anon> <anon> <anon> <anon>}"，而预期的类型是 "Complete@{<anon> <anon> <anon> <anon>}"（宇宙不一致：无法强制 <anon> = <anon> 因为 <anon> <= <anon> <= <anon> < <anon>）。方程在 [Complete] 的对象槽上。[trivial_small] 要求对象位于其指数所在的 homs 处或以下，而该定理要求指数位于 [Complete] 的形状对象宇宙处或以下，所以对象必须位于形状宇宙处或以下；[SmallOrd^op] 的形状宇宙严格位于其对象之下。标题引用了该形状中的拒绝。

N15（宇宙）。Instance/Powerset.v 自身的 [Subsets_Complete]，在 [Set] 的同源，以及在 [o] 的对象与 [Set < o]，无法满足简单见证，该见证需要对象位于同源处或以下：
  术语“Subsets_Complete”的类型为“Complete@{<anon> <anon> Set o}”，而期望类型为“Complete@{<anon> <anon> Set <anon>}”（宇宙不一致：无法强制 <anon> = o，因为 <anon> < o）。
控制项：其自身同源处的 [Subsets_Complete]，以及 Instance/Powerset/WellPowered.v 的路径 [Subsets_Complete_free] 与 [Subsets_WellPowered] 在 [o <= u]，输入到该定理。

N16（宇宙）。Structure/WellPowered/Counterexample.v 的裁决取决于同态实例化。[AntichainTop_WellPoweredAt_up]，位于 [i < h] 顶层对象的固定数据，在 [h <= i] 被拒绝：
  术语 “AntichainTop_WellPoweredAt_up”的类型为
  “WellPoweredAt@{<匿名> <匿名> <匿名> <匿名> <匿名>} None”，而期望的类型为“WellPoweredAt@{h o s h t} None”（宇宙不一致：无法强制 <匿名> = i 因为 <匿名> < <匿名> <= i）。控制：在 [i < h] 上是相同的常数；[AntichainTop_trivial]，上一个宇宙；并且，在 N16 的宇宙块上，与 [w <= h] 一起用于证人的索引，反驳 [AntichainTop_not_WellPowered] 应用于 [WellPowered] 证人。

** 在没有 [Untruncate] 的情况下，通过引脚连接到 [Sets] 的线路

N17, N18（类型），N19（宇宙），其他三个拒绝实例/集合/WellPowered.v 中的“为什么固定的证人使用 [Untruncate]”引用（它引用的第一个是 N2 的），每个在此都复现了那里引用的文本。N17，由 [inhabited] 截断的原像：
  在归纳类型“inhabited”中错误地消除了“proj2_sig p”：返回类型的排序为“Type”，而它应该是 SProp 或 Prop。其控制将原像作为数据携带。N18，该不可预言的 [Powerset_squash] 分类器使用：
      术语“q”的类型为“∃ a : A, m a ≈ b”，但期望它的类型为“?Q”（无法找到“?Q”的类型良好的实例化：无法确保“Type”是“Prop”的子类型）。一种类别的比较，[Type] 对比 [Prop]，而不是层次的比较。它的控制是 [Untruncate] 正好反转该截断。N19，
    Lattice.v 中的 [sub_intersection] 在 [Sets_HasWidePullbacks] 上的索引一个上层宇宙：
      发现类型“option (∃ i : wp_index (Sets_WellPoweredAt_up X), P (wp_to (Sets_WellPoweredAt_up X) i))”，而期望的是“option ?A”（无法找到 ?A 的类型正确实例：无法确保“Type@{max(o,<anon>)}”是“Type@{<anon>}”的子类型）。它的控制与 [Sets_WellPoweredAt_untruncate U X] 上的相同项相同。

**跨度箭头修正

N20, N21（宇宙）。[Complete_HasWidePullbacks] 位于 [SVariety E] 的类中（控制 [p451_svariety_hwp]）以及 [Sets]，在那里它会回读 Instance/Sets/SubobjectLattice.v 的直接 [Sets_HasWidePullbacks] 的宇宙（控制 [p451_sets_hwp_from_complete] 和 [p451_sets_hwp_direct]，被赋予相同类型），但是它不会向 Adjunction/SpanningArrow.v 的 [spanning_solution_set] 提供输入，后者的控制在抽象类上接收。N20，在 [SVariety_Forget E]：
      术语“Complete_HasWidePullbacks (SVariety_Complete E)”的类型为
      “HasWidePullbacks@{a c b c} (SVariety@{...} E)”，而期望类型是
      “HasWidePullbacks@{d e f c} (SVariety@{...} E)”（宇宙不一致：无法强制 a = d，因为 a <= <匿名> < <匿名> <= <匿名> <= <匿名> <= d）。N21，在 [Id[Sets]]:
      术语 “Complete_HasWidePullbacks Sets_Complete”的类型为
      “HasWidePullbacks@{a a b a} Sets@{a b}”，而预期类型为
      “HasWidePullbacks@{c d e f} Sets@{f e}”（宇宙不一致：无法强制 d = f，因为 f < <anon> <= <anon> <= d）。头部的每个 <anon> 在那里都被重命名为一个字母，并且省略了 [SVariety] 实例。N21 是在 Adjunction/SpanningArrow.v 中引用修正的形状：类的第二个宇宙 [d] 必须严格高于承载 [f]，并且完整性在承载处赋予它。这些修正将 N20 引用为“不能强制执行 <carrier> = <该类的第二个宇宙> 因为 <carrier> < ...”，使用保护假设 [GP] 作为 [Section] 假设进行测量；这里 [GP] 是一个普通绑定器，而 Rocq 首先报告了索引槽的方程。两种形式均在此文件的导入列表下进行测量：[Section] 形式在此文件的一个副本中打印修正的形状；绑定器形式被保留，因为 [Section] 假设本身可以修复宇宙，并且即使没有它，拒绝仍然成立。

N22（实例）。在加载 Structure/Pullback/Wide/Complete.v 和 Instance/Variety/Limit.v 后，类搜索未找到 [HasWidePullbacks (SVariety E)]：
      无法推断该类型为“HasWidePullbacks (SVariety E)”的占位符
      （未找到类型类实例）
    之所以 [Complete_HasWidePullbacks] 是定义而非实例，并不是全部原因。仅将其注册为本地实例会使该孔仍然带有相同的括号拒绝，单独将 [SVariety_Complete] 注册为 [typeclass_instances] 的本地提示也会如此：[Complete] 是一个普通定义，是关于图的 Π 型，而不是一个类，[SVariety_Complete] 不是实例，因此搜索不会从类通过 [Complete_HasWidePullbacks] 到 [SVariety_Complete] 建立链，除非两者都被注册（两个拒绝都是以整份文件的副本来衡量的）。在本地注册后，这个空洞得到解决：下方的 [Section] [SearchBoth] 接受它作为 [p451_n22_hwp_by_search_both]，而 [p451_n22_search_finds] 通过 [eq_refl] 读回搜索到的内容是 [Complete_HasWidePullbacks (SVariety_Complete E)]。另一个控制是 [p451_svariety_hwp]，由人工提供的类。Test/ProbeVarietySpanning448.v 的 P1 引脚在较短的导入列表中也显示出同样的缺失，该列表没有加载任何文件。

没有负面控制。穷尽性条款 [wp_to_from]，标题及其对应类型；[CoWellPowered C] 由 [eq_refl] 是 [WellPowered (C^op)]；标题返回的子对象是小重编索引族由 [eq_refl] 的 [complete_intersection]；针脚处的 [FinSet_WellPowered]，其索引回读为 [Fin.t n → Fin.t 2]，由 [eq_refl]；[Indiscrete_types_has_intersections] 和 [Subsets_intersection_all_not_top] 在其指定类型；Adjunction/SAFT/WellPowered.v 的索引 [WellPowered_SubobjectIndex] 是由 [eq_refl] 定义的良性索引；以及 [SubobjectIndex_not_exhaustive]。

曾被拒绝，现在已控制。两个由#451评审修复的活页夹，保存在这里的[Section]表单中，修复内容已在其中说明，因为[Section]的刚性宇宙只能使接受更加困难。[SAFT_of_WellPowered]与[WellPowered]的[t]被严格声明在[SAFT]的槽[u]下（[p451_saft_of_wp]，旁边[SAFT]直接应用于桥）在其名为[u]的活页夹之前被测量为拒绝，如Adjunction/SAFT/WellPowered.v的头记录所示。[SubobjectCover_Id_Sets_absurd] 与 [cogen_prod] 的槽 [u] 声明在对象宇宙 ([p451_cover_above]) 之上严格测量，在其绑定器声明之前被拒绝，而严格位于下方的槽 ([p451_cover_below]) 是 scratch acceptance Adjunction/SAFT/Sets.v 的头记录。如果任何绑定器返回到最小化，它们会破坏。结尾的保护块命名了 #451 文件的七十三个常量（按其行数计算），因此重命名会破坏此文件。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.Limit.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.Pullback.Wide.Complete.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Structure.Equalizer.Fork.
Require Import Coq.Logic.Hurkens.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.QuotObj.
Require Import Category.Instance.Sets.SubobjectLattice.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Epi.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.GAFT.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Comp.
Require Import Category.Instance.Variety.
Require Import Category.Instance.Variety.Free.
Require Import Category.Construction.Subcategory.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Structure.WellPowered.
Require Import Category.Structure.WellPowered.Counterexample.
Require Import Category.Instance.Sets.WellPowered.
Require Import Category.Instance.Grp.WellPowered.
Require Import Category.Instance.Powerset.WellPowered.
Require Import Category.Instance.FinSet.WellPowered.
Require Import Category.Adjunction.SAFT.WellPowered.
Require Import Category.Adjunction.SAFT.Sets.
Require Import Category.Adjunction.SpanningArrow.
Require Import Category.Instance.Variety.Limit.
Require Import Category.Instance.Variety.Spanning.
Require Import Category.Instance.Ordinal.Large.
Require Import Category.Instance.Parallel.Wide.
Require Import Category.Structure.Equalizer.Wide.

Generalizable All Variables.

Module UA := Category.Instance.Comp.UniversalAlgebra.

(** ** Instrument: the refutation keyword is live / ** 工具：反驳关键词是实时的 *)

Fail Check probe451_absent_name.

(** ** A. The definition, its exhaustiveness clause and the headline / ** A. 定义、其穷尽条款及标题 *)

Check (@wp_to_from : ∀ (C : Category) (x : C) (W : WellPoweredAt x)
  (u : SubObj x), wp_to W (wp_from W u) ≈ u).

Check (@wellpowered_complete_has_intersections :
  ∀ (C : Category) (WP : WellPowered C) (comp : @Complete C) (x : C)
    (P : SubObj x → Type), (∀ m m' : SubObj x, m ≈ m' → P m → P m') →
  { w : SubObj x & IsIntersection (fun k : { m : SubObj x & P m } => `1 k) w }).

Check (@cowellpowered_cocomplete_has_cointersections :
  ∀ (C : Category) (CWP : CoWellPowered C) (cocomp : @Cocomplete C) (x : C)
    (P : QuotObj x → Type), (∀ q q' : QuotObj x, q ≈ q' → P q → P q') →
  { w : QuotObj x &
    @IsIntersection (C^op) x _ (fun k : { q : QuotObj x & P q } => `1 k) w }).

(* The dual is the definition at the opposite category, on the nose. / 对偶是在相对范畴上的定义，正中要点。 *)
Example p451_cowp_is_wp_op (C : Category) :
  CoWellPowered C = WellPowered (C^op) := eq_refl.

(* The intersection IS the small reindexed one. / 交集就是那个小的重新索引的。 *)
Example p451_intersection_is_small (C : Category) (WP : WellPowered C)
  (comp : @Complete C) (x : C) (P : SubObj x → Type)
  (HP : ∀ m m' : SubObj x, m ≈ m' → P m → P m') :
  `1 (wellpowered_complete_has_intersections WP comp x P HP)
    = complete_intersection comp (wp_class_family (WP x) P) := eq_refl.

(** ** N1 (UNIVERSE): the trivial witness is refused under the pin / ** N1（宇宙）：在支撑点下琐碎的证人被拒绝 *)

(*
CONTROL: the per-object record, left unpinned, takes the trivial index
   at [Sets].

--------
控制：每个对象记录，如果没有固定，会在 [Sets] 处采用平凡索引。
*)
Definition p451_trivial_at_sets (X : Sets) : WellPoweredAt X := wp_trivial X.

(*
CONTROL: a copy of [WellPowered] with the pin [w <= h] deleted accepts the
   trivial witness at [Sets], so the pin is what N1 meets.

--------
控制：删除针脚 [w <= h] 的 [WellPowered] 副本接受 [Sets] 处的平凡见证，因此该针脚是 N1 所满足的。
*)
Definition p451_WellPowered_unpinned@{o h w s t | o <= s, h <= s, h < t +}
  (C : Category@{o h h}) := ∀ x : C, WellPoweredAt@{w o s h t} x.

Definition p451_trivial_unpinned_sets :
  p451_WellPowered_unpinned Sets := fun X => wp_trivial X.

(* CONTROL: objects at or below the homs, and the trivial index is small. / 控制：位于或低于homs的对象，并且平凡指标很小。 *)
Definition p451_trivial_small@{o h t | o <= h, h < t +}
  (C : Category@{o h h}) : WellPowered@{o h h h t} C := trivial_small C.

Fail Definition p451_n1_trivial_at_pin@{o so w s t} :
  WellPowered@{so o w s t} Sets@{o so} := fun X => wp_trivial X.

(**
** N2 (UNIVERSE): [Sets] one universe up is refused at the pin, and the
    [Untruncate] conditional is accepted there

--------
** N2（宇宙）：[Sets] 在引脚上向上一个宇宙被拒绝，而 [Untruncate] 条件在那里被接受
*)

(* CONTROL: the witness one universe up, per object. / 控制：证人每个对象在一个宇宙之上。 *)
Definition p451_sets_up@{o so | o < so +} (X : SetoidObject@{o o}) :=
  Sets_WellPoweredAt_up@{o so so} X.

(* CONTROL: at exactly N2's type, the conditional witness. / 控制：在恰好 N2 类型时，条件证人。 *)
Definition p451_sets_pinned_untruncate@{o so | o < so, Set < o +}
  (U : Untruncate@{o}) : WellPowered@{so o o so so} Sets@{o so} :=
  Sets_WellPowered_untruncate U.

(* CONTROL: the conditional witness IS the generic classifier witness. / 控制：条件见证人是通用分类器见证人。 *)
Example p451_sets_untruncate_is_classifier (U : Untruncate) (X : SetoidObject) :
  Sets_WellPoweredAt_untruncate U X
    = @wp_of_classifier Sets Sets_Terminal Sets_HasPullbacks
        (Sets_Classifier U) X := eq_refl.

Fail Definition p451_n2_sets_up_at_pin@{o so | o < so, Set < o +} :
  WellPowered@{so o o so so} Sets@{o so} := fun X => Sets_WellPoweredAt_up X.

(** ** N3 (UNIVERSE): [Grp] one universe up is refused at the pin / ** N3（宇宙）：[Grp] 上的一个宇宙在引脚处被拒绝 *)

(* CONTROL: the witness one universe up, per object. / 控制：证人每个对象在一个宇宙之上。 *)
Definition p451_grp_up@{o h | h < o, Set < o +} (G : Grp@{o h}) :=
  Grp_WellPoweredAt_up@{o o h} G.

Fail Definition p451_n3_grp_up_at_pin@{o h | h < o, Set < o +} :
  WellPowered@{o h h o o} Grp@{o h} := fun G => Grp_WellPoweredAt_up G.

(**
** N4-N6 (UNIVERSE): without well-poweredness, the class of subobjects
    is refused at the adjoint-functor regime

--------
** N4-N6（宇宙）：在没有良好幂性的情况下，子对象的类在伴随体制下被拒绝
*)

(*
CONTROL: a family indexed at or below the homs needs no
   well-poweredness.

--------
控制：在 homs 或以下索引的家庭不需要良好健全性。
*)
Definition p451_small_family@{o h j +| h < o, j <= h +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) (x : C)
  (J : Type@{j}) (S : J → SubObj x) :=
  complete_intersection_IsIntersection comp S.

(* CONTROL: the class, given [WellPowered C]. / 控制：该类，给定 [WellPowered C]。 *)
Definition p451_class_with_wp@{o h +| h < o +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) (WP : WellPowered C)
  (x : C) (P : SubObj x → Type@{h})
  (HP : ∀ m m' : SubObj x, m ≈ m' → P m → P m') :=
  wellpowered_complete_has_intersections WP comp x P HP.

(* CONTROL: all subobjects, given [WellPowered C]. / 控制：所有子对象，给定 [WellPowered C]。 *)
Definition p451_all_with_wp@{o h +| h < o +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) (WP : WellPowered C)
  (x : C) := wellpowered_complete_intersection_all WP comp x.

(* CONTROL: N4's term with the objects at or below the homs. / 控制：N4 与位于或低于 Homs 的物体的关系。 *)
Definition p451_class_small_objects@{o h +| o <= h +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) (x : C)
  (P : SubObj x → Type@{h}) :=
  complete_intersection_IsIntersection comp
    (fun k : { m : SubObj x & P m } => `1 k).

Fail Definition p451_n4_class_no_wp@{o h +| h < o +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) (x : C)
  (P : SubObj x → Type@{h}) :=
  complete_intersection_IsIntersection comp
    (fun k : { m : SubObj x & P m } => `1 k).

(* CONTROL: N5's term with the objects at or below the homs. / 控制：N5 与位于同类或以下的对象的关系。 *)
Definition p451_all_small_objects@{o h +| o <= h +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) (x : C) :=
  complete_intersection_IsIntersection comp (fun m : SubObj x => m).

Fail Definition p451_n5_all_no_wp@{o h +| h < o +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) (x : C) :=
  complete_intersection_IsIntersection comp (fun m : SubObj x => m).

(* CONTROL: the wide pullback of a small family of subobjects' monos. / 控制：一小族子对象单射的广泛回拉。 *)
Definition p451_wide_small@{o h j +| h < o, j <= h +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) (x : C)
  (J : Type@{j}) (S : J → SubObj x) :=
  @wide_pullback C (Complete_HasWidePullbacks comp) J
    (fun k => Subobject.sub_dom (S k)) x (fun k => Subobject.sub_mono (S k)).

Fail Definition p451_n6_class_wide_pullback@{o h +| h < o +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) (x : C)
  (P : SubObj x → Type@{h}) :=
  @wide_pullback C (Complete_HasWidePullbacks comp) { m : SubObj x & P m }
    (fun k => Subobject.sub_dom (`1 k)) x
    (fun k => Subobject.sub_mono (`1 k)).

(** ** N7 (UNIVERSE): the class of all subobjects at [Sets] / ** N7（宇宙）：[Sets] 上所有子对象的类别 *)

(* CONTROL: given [WellPowered Sets]. / 控制：给定 [WellPowered Sets]。 *)
Definition p451_sets_all_with_wp@{o so +| o < so +} (X : Sets@{o so})
  (WP : WellPowered Sets@{o so}) :=
  wellpowered_complete_intersection_all WP Sets_Complete X.

(* CONTROL: the [Untruncate] witness fed to the generic theorem. / 控制：[Untruncate] 证人被输入到通用定理中。 *)
Definition p451_sets_all_untruncate@{o so +| o < so, Set < o +}
  (U : Untruncate@{o}) (X : Sets@{o so}) :=
  wellpowered_complete_intersection_all (Sets_WellPowered_untruncate U)
    Sets_Complete X.

(* CONTROL: a family indexed at the carrier universe. / 控制：在载体宇宙中索引的一个家族。 *)
Definition p451_sets_small_family@{o so +| o < so +} (X : Sets@{o so})
  (J : Type@{o}) (S : J → SubObj X) :=
  complete_intersection_IsIntersection Sets_Complete S.

Fail Definition p451_n7_sets_all_no_wp@{o so +| o < so +} (X : Sets@{o so}) :=
  complete_intersection_IsIntersection Sets_Complete (fun m : SubObj X => m).

(** ** N8 (UNIVERSE), N9 (TYPING): arbitrary large families / ** N8（宇宙），N9（打字）：任意大的族 *)

Definition p451_image_resp {C : Category} {x : C} {J : Type}
  (S : J → SubObj x) :
  ∀ m m' : SubObj x, m ≈ m' → { j : J & S j ≈ m } → { j : J & S j ≈ m' }.
Proof.
  intros m m' e [j H]; exists j; etransitivity; [exact H | exact e].
Defined.

(* CONTROL: the typed image of a family indexed at or below the homs. / 控制：在或低于homs索引的家庭输入图像。 *)
Definition p451_image_small@{o h j +| h < o, j <= h +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) (WP : WellPowered C)
  (x : C) (J : Type@{j}) (S : J → SubObj x) :=
  wellpowered_complete_has_intersections WP comp x
    (fun m => { j : J & S j ≈ m }) (p451_image_resp S).

Fail Definition p451_n8_image_large@{o h +| h < o +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) (WP : WellPowered C)
  (x : C) (J : Type@{o}) (S : J → SubObj x) :=
  wellpowered_complete_has_intersections WP comp x
    (fun m => { j : J & S j ≈ m }) (p451_image_resp S).

Section LargeFamily.

Context {C : Category} (comp : @Complete C) (WP : WellPowered C) (x : C).
Context {J : Type} (S : J → SubObj x).

Definition p451_trunc_class (m : SubObj x) : Prop :=
  ex (fun j : J => inhabited (S j ≈ m)).

Lemma p451_trunc_resp :
  ∀ m m' : SubObj x, m ≈ m' → p451_trunc_class m → p451_trunc_class m'.
Proof.
  intros m m' e [j [H]]; exists j; constructor; etransitivity;
    [exact H | exact e].
Qed.

(* CONTROL: the truncated image IS a class the [Prop] form accepts... / 控制：截断的图像是 [Prop] 表单接受的一个类... *)
Definition p451_trunc_meet :=
  wellpowered_complete_has_intersections_prop WP comp x
    p451_trunc_class p451_trunc_resp.

(* CONTROL: ...and its intersection lies below every member of [S]. / 控制：……它的交点位于 [S] 的每个成员之下。 *)
Definition p451_trunc_le (j : J) : sub_le (`1 p451_trunc_meet) (S j) :=
  inter_le _ _ (`2 p451_trunc_meet)
    (S j; ex_intro _ j (inhabits (Equivalence_Reflexive (S j)))).

(* CONTROL: the greatest step with a [Type]-valued witness. / 控制：与一个 [Type] 值见证人的最大步骤。 *)
Definition p451_typed_greatest (v : SubObj x) (Hv : ∀ j, sub_le v (S j))
  (m : SubObj x) (w : { j : J & S j ≈ m }) : sub_le v m :=
  sub_le_trans _ _ _ (Hv (`1 w)) (sub_le_of_equiv _ _ (`2 w)).

(*
CONTROL: the whole greatest step, over the intersection of the typed
   image, so that the truncation is the only difference from N9.

--------
控制：整个最大步骤，跨越已输入图像的交叉点，因此截断是与N9唯一的区别。
*)
Definition p451_typed_meet :=
  wellpowered_complete_has_intersections WP comp x
    (fun m => { j : J & S j ≈ m }) (p451_image_resp S).

Definition p451_typed_greatest_full (v : SubObj x)
  (Hv : ∀ j, sub_le v (S j)) : sub_le v (`1 p451_typed_meet) :=
  ltac:(apply (inter_greatest _ _ (`2 p451_typed_meet));
        intros [m [j e]];
        exact (sub_le_trans _ _ _ (Hv j) (sub_le_of_equiv _ _ e))).

Fail Definition p451_n9_trunc_greatest (v : SubObj x)
  (Hv : ∀ j, sub_le v (S j)) : sub_le v (`1 p451_trunc_meet) :=
  ltac:(apply (inter_greatest _ _ (`2 p451_trunc_meet));
        intros [m [j [e]]];
        exact (sub_le_trans _ _ _ (Hv j) (sub_le_of_equiv _ _ e))).

End LargeFamily.

(**
** N10, N11 (UNIVERSE): the wide pullbacks, by which route and at
    which index

--------
** N10, N11（宇宙）：大幅回调，通过哪条路线以及在哪个指数
*)

(*
CONTROL: at a shape-object universe of [Set], the wide-equalizer shape
   is accepted.

--------
控制：在 [Set] 的形状-对象宇宙中，宽均衡器形状被接受。
*)
Definition p451_wideparallel_at_set@{o h +| Set < h, h < o +}
  (C : Category@{o h h}) (comp : @Complete@{h Set h o} C) (J : Type@{h}) :=
  comp (WideParallel J).

(* CONTROL: the route taken, at the regime. / 控制：在制度下所采取的路线。 *)
Definition p451_wide_pullbacks_regime@{o h +| Set < h, h < o +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) :
  HasWidePullbacks C := Complete_HasWidePullbacks comp.

Fail Definition p451_n10_wideparallel_regime@{o h +| Set < h, h < o +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C) (J : Type@{h}) :=
  comp (WideParallel J).

(* CONTROL: a family indexed at the shape-object universe. / 控制：在形状-对象宇宙中被索引的一个家族。 *)
Definition p451_wide_index_small@{o h +| h < o +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C)
  (J : Type@{h}) (A : J → C) (z : C) (f : ∀ j, A j ~> z) :=
  @complete_wide_pullback C comp J A z f.

Fail Definition p451_n11_wide_index_large@{o h +| h < o +}
  (C : Category@{o h h}) (comp : @Complete@{h h h o} C)
  (J : Type@{o}) (A : J → C) (z : C) (f : ∀ j, A j ~> z) :=
  @complete_wide_pullback C comp J A z f.

(**
** N12, N13 (CONVERSION): the lower bounds compute, the greatest-lower-
    bound factorization does not

--------
** N12, N13（转换）：下界可以计算，最大下界分解不能
*)

Definition p451_IC : Category := Indiscrete bool.
Definition p451_IC_comp : @Complete p451_IC := Indiscrete_Complete true.
Definition p451_fam :
  ∀ j : Datatypes.unit,
    (fun _ => true : obj[p451_IC]) j ~{p451_IC}~> (true : obj[p451_IC]) :=
  fun _ => tt.
Definition p451_cone :
  ∀ j : Datatypes.unit,
    (false : obj[p451_IC]) ~{p451_IC}~> (fun _ => true : obj[p451_IC]) j :=
  fun _ => tt.
Definition p451_cone_commutes :
  ∀ i j : Datatypes.unit,
    p451_fam i ∘ p451_cone i ≈ p451_fam j ∘ p451_cone j :=
  fun _ _ => eq_refl.

(* CONTROL: the product mediator of the same completeness witness. / 控制：同等完整性的产品中介见证。 *)
Example p451_product_mediator_computes :
  unique_obj
    (iprod_ump (fun _ : Datatypes.unit => (true : obj[p451_IC]))
       (p451_IC_comp _
          (DiscreteCat_Functor
             (fun _ : Datatypes.unit => (true : obj[p451_IC]))))
       (false : obj[p451_IC]) p451_cone) = tt := eq_refl.

(* CONTROL: the legs of the wide pullback, hence every [inter_le]. / 控制：宽回撤的腿，因此每个 [inter_le]。 *)
Example p451_leg_computes :
  wide_pullback_proj (complete_wide_pullback p451_IC_comp p451_fam) tt = tt
  := eq_refl.

(*
CONTROL: the mediator IS [tt] up to ≈, which in [Indiscrete] is
   Leibniz equality, by case analysis on [unit].

--------
控制：中介是 [tt] 直到 ≈，在 [Indiscrete] 中是莱布尼茨等式，通过对 [unit] 的情况分析。
*)
Definition p451_mediator_equiv :
  unique_obj (ump_wide_pullbacks (complete_wide_pullback p451_IC_comp p451_fam)
                (false : obj[p451_IC]) p451_cone p451_cone_commutes) ≈ tt :=
  ltac:(destruct (unique_obj (ump_wide_pullbacks
                   (complete_wide_pullback p451_IC_comp p451_fam)
                   (false : obj[p451_IC]) p451_cone p451_cone_commutes));
        reflexivity).

Fail Example p451_n12_mediator_by_conversion :
  unique_obj (ump_wide_pullbacks (complete_wide_pullback p451_IC_comp p451_fam)
                (false : obj[p451_IC]) p451_cone p451_cone_commutes) = tt
  := eq_refl.

(* CONTROL: the GAFT equalizer's mediator, up to ≈. / 控制：GAFT 均衡器的中介，最高可达 ≈。 *)
Definition p451_gaft_equalizer := Complete_HasEqualizers p451_IC_comp.

Definition p451_gaft_mediator_equiv :
  unique_obj (eq_desc (`2 (`2 (@equalizer p451_IC p451_gaft_equalizer
                                  true true tt tt)))
                (z := false) tt eq_refl) ≈ tt :=
  ltac:(destruct (unique_obj (eq_desc (`2 (`2 (@equalizer p451_IC
                   p451_gaft_equalizer true true tt tt))) (z := false) tt
                   eq_refl)); reflexivity).

Fail Example p451_n13_gaft_mediator_by_conversion :
  unique_obj (eq_desc (`2 (`2 (@equalizer p451_IC p451_gaft_equalizer
                                  true true tt tt)))
                (z := false) tt eq_refl) = tt := eq_refl.

(** ** N14 (UNIVERSE): [SmallOrd^op]'s shape universe lies below its objects / ** N14（宇宙）：[SmallOrd^op] 的形状宇宙位于其物体之下 *)

(* CONTROL: the trivial witness, with the homs raised to the objects. / 控制：平凡的证人，手持物体将其举起。 *)
Definition p451_smallord_wp := trivial_small SmallOrd_op_Proset.

(*
CONTROL: the theorem at [SmallOrd_op_Complete], over an abstract
   witness.

--------
控制：关于抽象证人的 [SmallOrd_op_Complete] 定理。
*)
Definition p451_smallord_abstract (WP : WellPowered SmallOrd_op_Proset)
  (x : SmallOrd_op_Proset) :=
  wellpowered_complete_intersection_all WP SmallOrd_op_Complete x.

Fail Definition p451_n14_smallord_trivial (x : SmallOrd_op_Proset) :=
  wellpowered_complete_intersection_all (trivial_small SmallOrd_op_Proset)
    SmallOrd_op_Complete x.

(**
** N15 (UNIVERSE): Instance/Powerset.v's [Subsets_Complete], homs at
    [Set], meets the trivial witness nowhere

--------
** N15（宇宙）：Instance/Powerset.v 的 [Subsets_Complete]，在 [Set] 处的同态映射，处处不满足平凡的证人
*)

(* CONTROL: the literal [Subsets_Complete] at its own homs. / 控制：字面上的 [Subsets_Complete] 在它自己的归宿。 *)
Definition p451_subsets_complete_at_set@{o +| Set < o +}
  (X : SetoidObject@{o o}) : @Complete (Subsets@{o Set} X) :=
  @Subsets_Complete X.

(* CONTROL: the free-hom-level restatement, fed to the theorem. / 控制：自由同级重述，输入定理。 *)
Definition p451_subsets_free@{o u +| Set < o, o <= u +}
  (X : SetoidObject@{o o}) (S : Subsets@{o u} X) :=
  wellpowered_complete_intersection_all (Subsets_WellPowered X)
    (Subsets_Complete_free X) S.

Fail Definition p451_n15_subsets_at_set@{o +| Set < o +}
  (X : SetoidObject@{o o}) (S : Subsets@{o Set} X) :=
  wellpowered_complete_intersection_all (trivial_small _)
    (@Subsets_Complete X) S.

(**
** N16 (UNIVERSE): the antichain with a top is well-powered at the pin
    only with its homs raised

--------
** N16（宇宙）：具有顶点的反链在引脚处是良有势的，仅在其同态提升时
*)

(* CONTROL: one universe up, the trivial index. / 控制：一个宇宙向上，琐碎的指数。 *)
Definition p451_at_trivial@{i o h t | i < o, h < t, h <= o +} :
  @WellPoweredAt@{o o o h t} AntichainTop@{i o h} None := AntichainTop_trivial.

(* CONTROL: at the pin, with [i < h]. / 控制：在引脚处，使用 [i < h]。 *)
Definition p451_at_up@{i o h s t | i < o, i < h, h < t, o <= s, h <= s +} :
  @WellPoweredAt@{h o s h t} AntichainTop@{i o h} None :=
  AntichainTop_WellPoweredAt_up.

(* CONTROL: at N16's universes, the refutation. / 控制：在N16的宇宙中，反驳。 *)
Definition p451_at_refuted@{i o h w s t |
    i < o, h <= i, w <= h, h < t, o <= s, h <= s +}
  (WP : WellPowered@{o h w s t} AntichainTop@{i o h}) : False :=
  AntichainTop_not_WellPowered WP.

Fail Definition p451_n16_at_up_low_homs@{i o h s t |
    i < o, h <= i, h < t, o <= s, h <= s +} :
  @WellPoweredAt@{h o s h t} AntichainTop@{i o h} None :=
  AntichainTop_WellPoweredAt_up.

(**
** N17, N18 (TYPING), N19 (UNIVERSE): the routes to [Sets] at the pin
    without [Untruncate]

--------
** N17, N18（打字）, N19（宇宙）：到引脚的 [Sets] 路径，没有 [Untruncate]
*)

(* CONTROL: a preimage carried as data gives the element back. / 控制：作为数据携带的原像会返回元素。 *)
Definition p451_typed_preimage@{o so | o < so +} (X A : SetoidObject@{o o})
  (m : A ~{Sets@{o so}}~> X) :
  { b : carrier X & { a : carrier A & m a ≈ b } } → carrier A :=
  fun p => `1 (`2 p).

Fail Definition p451_n17_inhabited_preimage@{o so | o < so +}
  (X A : SetoidObject@{o o}) (m : A ~{Sets@{o so}}~> X) :
  { b : carrier X | inhabited { a : carrier A & m a ≈ b } } → carrier A :=
  fun p => match proj2_sig p with inhabits q => `1 q end.

(* CONTROL: [Untruncate] inverts exactly the truncation N18 meets. / 控制：[Untruncate] 完全反转 N18 遇到的截断。 *)
Definition p451_untruncated_preimage@{o so | o < so +} (U : Untruncate@{o})
  (X A : SetoidObject@{o o}) (m : A ~{Sets@{o so}}~> X) (b : carrier X)
  (h : Powerset_squash@{o} { a : carrier A & m a ≈ b }) : carrier A :=
  `1 (U _ h).

Fail Definition p451_n18_squashed_preimage@{o so | o < so +}
  (X A : SetoidObject@{o o}) (m : A ~{Sets@{o so}}~> X) (b : carrier X)
  (h : Powerset_squash@{o} { a : carrier A & m a ≈ b }) : carrier A :=
  `1 (h _ (fun q => q)).

(* CONTROL: the intersection over the pinned, conditional index. / 控制：固定的、有条件的索引上的交集。 *)
Definition p451_sets_meet_pinned@{o so | o < so, Set < o +}
  (U : Untruncate@{o}) (X : SetoidObject@{o o})
  (P : @SubObj Sets@{o so} X → Type@{o}) : @SubObj Sets@{o so} X :=
  @sub_intersection Sets@{o so} Sets_HasWidePullbacks@{o so} X _ None
    (fun j : option { i : wp_index (Sets_WellPoweredAt_untruncate U X)
                    & P (wp_to (Sets_WellPoweredAt_untruncate U X) i) } =>
       match j with
       | None => @sub_top Sets@{o so} X
       | Some p => wp_to (Sets_WellPoweredAt_untruncate U X) (`1 p)
       end).

Fail Definition p451_n19_sets_meet_up@{o so | o < so, Set < o +}
  (X : SetoidObject@{o o})
  (P : @SubObj Sets@{o so} X → Type@{o}) : @SubObj Sets@{o so} X :=
  @sub_intersection Sets@{o so} Sets_HasWidePullbacks@{o so} X _ None
    (fun j : option { i : wp_index (Sets_WellPoweredAt_up X)
                    & P (wp_to (Sets_WellPoweredAt_up X) i) } =>
       match j with
       | None => @sub_top Sets@{o so} X
       | Some p => wp_to (Sets_WellPoweredAt_up X) (`1 p)
       end).

(**
** N22 (INSTANCE): the class from completeness is a definition, and
    class search does not find it

--------
** N22（实例）：来自 completeness 的类是一个定义，而类搜索找不到它
*)

(* CONTROL: the inhabitant #451 adds, supplied by hand. / 控制：居民 #451 补充道，由手工提供。 *)
Definition p451_svariety_hwp {S : UA.OpSignature} (E : UA.EqSignature S) :
  HasWidePullbacks (SVariety E) :=
  Complete_HasWidePullbacks (SVariety_Complete E).

Fail Definition p451_n22_hwp_by_search {S : UA.OpSignature}
  (E : UA.EqSignature S) : HasWidePullbacks (SVariety E) := _.

(*
CONTROL: with BOTH the producer and the completeness witness registered
   locally, class search resolves the same hole, and what it finds IS the
   producer at [SVariety_Complete E].  Either registration alone leaves the
   hole refused (measured, see the header), so being a definition is not
   the whole of N22's reason.

--------
控制：当生产者和完整性见证都在本地注册时，类搜索会解析同一个漏洞，并且它找到的是位于 [SVariety_Complete E] 的生产者。单独注册任一方都会导致漏洞被拒绝（已测量，见头文件），所以成为一个定义并不是 N22 的全部原因。
*)
Section SearchBoth.

#[local] Existing Instance Complete_HasWidePullbacks.
#[local] Hint Resolve SVariety_Complete : typeclass_instances.

Definition p451_n22_hwp_by_search_both {S : UA.OpSignature}
  (E : UA.EqSignature S) : HasWidePullbacks (SVariety E) := _.

Example p451_n22_search_finds {S : UA.OpSignature} (E : UA.EqSignature S) :
  p451_n22_hwp_by_search_both E
    = Complete_HasWidePullbacks (SVariety_Complete E) := eq_refl.

End SearchBoth.

(**
** N20, N21 (UNIVERSE): wide pullbacks from completeness do not feed the
    spanning-arrow solution set

--------
** N20, N21（宇宙）：从完整性的大幅回撤不会喂给跨箭头解集
*)

(* CONTROL: the solution set over an abstract [HasWidePullbacks]. / 控制：在抽象 [HasWidePullbacks] 上的解集。 *)
Definition p451_span_abstract {S : UA.OpSignature} (E : UA.EqSignature S)
  (HWP : HasWidePullbacks (SVariety E))
  (GP : PreservesWidePullbacks (SVariety_Forget E)) (x : Sets) :=
  @spanning_solution_set _ _ (SVariety_Forget E) HWP GP x.

Fail Definition p451_n20_span_svariety {S : UA.OpSignature}
  (E : UA.EqSignature S) (GP : PreservesWidePullbacks (SVariety_Forget E))
  (x : Sets) :=
  @spanning_solution_set _ _ (SVariety_Forget E)
    (Complete_HasWidePullbacks (SVariety_Complete E)) GP x.

(*
CONTROL: at [Sets] the class from completeness reads back at the
   universes of the direct instance.

--------
控制：在 [Sets]，来自完整性的类回读直接实例的宇宙。
*)
Definition p451_sets_hwp_from_complete@{o so +| o < so +} :
  HasWidePullbacks@{o o so o} Sets@{o so} :=
  Complete_HasWidePullbacks Sets_Complete.

Definition p451_sets_hwp_direct@{o so +| o < so +} :
  HasWidePullbacks@{o o so o} Sets@{o so} := Sets_HasWidePullbacks.

(* CONTROL: the solution set at [Id[Sets]] over an abstract class. / 控制：在抽象类上，[Id[Sets]] 的解集。 *)
Definition p451_span_sets_abstract (HWP : HasWidePullbacks Sets)
  (GP : PreservesWidePullbacks (@Id Sets)) (x : Sets) :=
  @spanning_solution_set _ _ (@Id Sets) HWP GP x.

Fail Definition p451_n21_span_sets (GP : PreservesWidePullbacks (@Id Sets))
  (x : Sets) :=
  @spanning_solution_set _ _ (@Id Sets)
    (Complete_HasWidePullbacks Sets_Complete) GP x.

(** ** Controls without a negative / ** 没有否定的控制 *)

(* FinSet, unconditionally at the pin, with its index read back. / FinSet，无条件地在针脚上，读取其索引。 *)
Definition p451_finset_wp@{o h s t u v +| Set < u, h < t, o <= s, h <= s +} :
  WellPowered@{o h h s t} FinSet@{o h u v} := FinSet_WellPowered.

Example p451_finset_index (n : FinSet) :
  wp_index (FinSet_WellPowered n) = (Fin.t n → Fin.t 2) := eq_refl.

(* The unconditional instance with objects above homs. / 具有对象上同态的无条件实例。 *)
Check (Indiscrete_types_has_intersections :
  ∀ (x : Indiscrete Type) (P : SubObj x → Type),
    (∀ m m' : SubObj x, m ≈ m' → P m → P m') →
    { w : SubObj x &
      IsIntersection (fun k : { m : SubObj x & P m } => `1 k) w }).

(* The unconditional non-degenerate instance at the powerset lattice. / 幂集格上的无条件非简并实例。 *)
Check (Subsets_intersection_all_not_top :
  ∀ (X : SetoidObject) (x : carrier X),
    `1 (Subsets_intersection_all X subset_top) ≈ sub_top → False).

(* The bridge to SAFT's index, whose index IS the well-powered one. / 通往SAFT指数的桥梁，其指数是强大的那个。 *)
Example p451_bridge_index (C : Category) (W : WellPowered C) (x : C) :
  sub_index (WellPowered_SubobjectIndex W x) = wp_index (W x) := eq_refl.

Check (@SubobjectIndex_not_exhaustive :
  ∀ (C : Category) (x : C),
    (SubObj x → sub_index (empty_SubobjectIndex x)) → False).

(*
Formerly refused: [SAFT_of_WellPowered] with [WellPowered]'s [t] held
   strictly below [SAFT]'s slot [u].

--------
先前拒绝：[SAFT_of_WellPowered] 与 [WellPowered] 的 [t] 保持在 [SAFT] 的槽位 [u] 之下。
*)
Section SAFTBinder.

Universes cobj dobj h u u1 u2 w s t.
Constraint h < u.
Constraint h < u1.
Constraint w <= h.
Constraint cobj <= s.
Constraint h <= s.
Constraint h < t.
Constraint t < u.

Context (C : Category@{cobj h h}) (D : Category@{dobj h h}) (U : C ⟶ D).
Context (comp : @Complete@{h h h cobj} C).
Context (cont : @PreservesImageLimit@{cobj h dobj h u1 h u h} C D U).
Context (G : Cogenerator@{h cobj h} C) (W : WellPowered@{cobj h w s t} C).
Context (cover : SubobjectCover@{u2 w h u h dobj cobj h} U comp G
                   (WellPowered_SubobjectIndex@{cobj h w s t} W)).

Definition p451_saft_direct :=
  SAFT U comp cont G (WellPowered_SubobjectIndex@{cobj h w s t} W) cover.
Definition p451_saft_of_wp := SAFT_of_WellPowered U comp cont G W cover.

End SAFTBinder.

(*
Formerly refused: the [Id[Sets]] refutation with [cogen_prod]'s slot [u]
   declared strictly above, and strictly below, the object universe.

--------
以前拒绝：[Id[Sets]] 对 [cogen_prod] 的插槽 [u] 的反驳，被声明严格位于对象宇宙之上和之下。
*)
Section CoverAbove.

Universes cobj h u u2 u3.
Constraint Set < h.
Constraint h < cobj.
Constraint cobj < u.
Constraint u3 <= h.

Context (comp : @Complete@{h h h cobj} Sets@{h cobj}).
Context (G : Cogenerator@{h cobj h} Sets@{h cobj}).
Context (WP : ∀ x : Sets@{h cobj}, SubobjectIndex@{u3 cobj h} x).
Context (cover : SubobjectCover@{u2 u3 h u h cobj cobj h}
                   (@Id Sets@{h cobj}) comp G WP).

Definition p451_cover_above : False :=
  SubobjectCover_Id_Sets_absurd comp G WP cover.

End CoverAbove.

Section CoverBelow.

Universes cobj h u u2 u3.
Constraint Set < h.
Constraint h < u.
Constraint u < cobj.
Constraint u3 <= h.

Context (comp : @Complete@{h h h cobj} Sets@{h cobj}).
Context (G : Cogenerator@{h cobj h} Sets@{h cobj}).
Context (WP : ∀ x : Sets@{h cobj}, SubobjectIndex@{u3 cobj h} x).
Context (cover : SubobjectCover@{u2 u3 h u h cobj cobj h}
                   (@Id Sets@{h cobj}) comp G WP).

Definition p451_cover_below : False :=
  SubobjectCover_Id_Sets_absurd comp G WP cover.

End CoverBelow.

(** ** Guard block / ** 防守格挡 *)

Check @WellPoweredAt.
Check @wp_index.
Check @wp_to.
Check @wp_from.
Check @wp_to_from.
Check @wp_index_setoid.
Check @wp_from_resp.
Check @wp_from_to.
Check @WellPowered.
Check @CoWellPowered.
Check @quot_obj_is_sub_op.
Check @quot_setoid_is_sub_setoid_op.
Check @cowp_to_from.
Check @sub_opt_top.
Check @IsIntersection_drop_top.
Check @complete_intersection.
Check @complete_intersection_IsIntersection.
Check @wp_class_index.
Check @wp_class_family.
Check @IsIntersection_reindex.
Check @wp_complete_class_intersection.
Check @wellpowered_complete_has_intersections.
Check @wellpowered_intersection_is_small.
Check @wellpowered_complete_has_intersections_prop.
Check @wellpowered_complete_intersection_all.
Check @wellpowered_complete_least_subobject.
Check @cowellpowered_cocomplete_has_cointersections.
Check @cointersection_quot_le.
Check @wp_trivial.
Check @trivial_small.
Check @wp_groupoid.
Check @Groupoid_WellPowered.
Check @Groupoid_CoWellPowered.
Check @DiscreteCat_WellPowered.
Check @DiscreteCat_CoWellPowered.
Check @DiscreteCat_types_WellPowered.
Check @Indiscrete_WellPowered.
Check @Indiscrete_CoWellPowered.
Check @wp_of_classifier.
Check @Classifier_WellPowered.
Check @Indiscrete_Complete.
Check @Indiscrete_types_has_intersections.
Check @complete_wide_pullback.
Check @Complete_HasWidePullbacks.
Check @retract_paradox.
Check @AntichainTop.
Check @AntichainTop_not_WellPoweredAt.
Check @AntichainTop_not_WellPowered.
Check @AntichainTop_Set_not_WellPowered.
Check @AntichainTop_op_not_CoWellPowered.
Check @AntichainTop_trivial.
Check @AntichainTop_WellPoweredAt_up.
Check @FinSet_WellPowered.
Check @Sets_WellPoweredAt_up.
Check @Sets_CoWellPoweredAt_up.
Check @Sets_WellPoweredAt_untruncate.
Check @Sets_WellPowered_untruncate.
Check @Sets_wellpowered_intersection.
Check @Sets_intersection_all_empty.
Check @Grp_WellPoweredAt_up.
Check @Subsets_Complete_free.
Check @Subsets_WellPowered.
Check @Subsets_has_intersections.
Check @Subsets_intersection_all.
Check @Subsets_intersection_all_not_top.
Check @SubobjectIndex_of_WellPoweredAt.
Check @WellPowered_SubobjectIndex.
Check @SAFT_of_WellPowered.
Check @empty_SubobjectIndex.
Check @SubobjectIndex_not_exhaustive.
Check @SubobjectCover_Id_retract.
Check @SubobjectCover_Id_Sets_absurd.
Check @SubobjectCover_Id_Sets_absurd_at_SAFT.
