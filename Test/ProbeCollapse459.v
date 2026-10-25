(**
* Probe for Mac Lane V.9's collapse X/A and category of pairs (issue #459)

    Pins the measured boundaries of the two files #459 adds for Mac Lane
    §V.9, book pp. 134-135 (PDF pp. 143-144): catalog id
    maclane:V.9:construction5, the space X/A obtained by collapsing a
    subset A of X to a point, the wide coequalizer of the point-inclusions
    of A (Instance/Top/Quotient.v, with the tree's first inhabitant of
    [HasWideCoequalizers]); and maclane:V.9:construction6, the category
    [Top_pairs] of pairs ⟨X, A⟩ and the quotient functor ⟨X, A⟩ ↦ X/A left
    adjoint to Y ↦ ⟨Y, *⟩ (Instance/Top/Quotient/Pairs.v).  The book
    numbers neither construction; the ids are names.  Mac Lane defines
    the coequalizer of a pair elementarily (book p. 64, display (6)),
    reads it as a universal arrow to the diagonal (p. 65), and defines
    coequalizers of any set of maps "in the same way"; the two readings
    agree on every nonempty set of maps, and the book does not treat the
    empty one.  Read as the universal arrow, a colimit over the shape
    that has * as a vertex, Structure/Coequalizer/Wide.v's
    [WideCoequalizer], the two constructions agree at every A: Pairs.v's
    X/A, (X ⊔ {∗})/(A ∼ ∗), is that colimit for every A, the empty one
    included, where it is X ⊔ *.  Read elementarily, as the record
    [IsWideCoequalizer], X/∅ is X itself, pointless when X is, and the
    two constructions part at A = ∅: Pairs.v proves X/A an elementary
    wide coequalizer whenever A has a point, and, under the elementary
    reading, refutes a pointed X/A at ⟨∅, ∅⟩ for every construction.
    This file restates those results as controls.  N1, N4, N6-N8, N11
    and N13 restate refusals #459's builder measured in scratch files; N2, N3,
    N5, N9, N10, N12 and N14-N16 are this file's own.  Every one is
    recorded in a target header, which cites it by its N-number.  The
    positive controls restate the files' claims independently.

    THE IMPORT LIST, measured by comparing [Require] lines by script.
    First Instance/Top/Quotient.v's ten lines verbatim and in order, then
    that file; then the eleven lines Instance/Top/Quotient/Pairs.v adds,
    in its order (Theory/Functor.v, Theory/Adjunction.v,
    Construction/Opposite.v, Functor/Opposite.v, Structure/Cone.v,
    Structure/Limit/Preservation.v, Structure/Pullback.v,
    Structure/Pushout.v, Instance/Parallel.v, Instance/Top/Coproduct.v,
    Instance/Top/Homotopy.v), and that file.  Twenty-three lines: the
    twenty-two distinct [Require]s of the two targets,
    Instance/Top/Quotient.v among them, and Pairs.v, which no target
    requires.  Under this list the file's dependency closure is sixty-one
    [Category] modules ([Print Libraries]), the two targets among them.
    Instance/Top/Homotopy.v requires the stdlib reals and opens [R_scope],
    so the products and sums of types below are written under [%type].
    A shorter import list is what makes a probe pass for no reason.

    DISCIPLINE.  The instrument was checked both ways: the refutation of
    an absent name is refused for that reason ("The reference
    probe459_absent_name was not found in the current environment."),
    and each of the sixty-nine definitions, examples and inductives of
    this file that is not a refutation (forty-five, twenty-two and two),
    wrapped in the refutation keyword in a copy of this WHOLE file, stops
    the build at that command with the report that the guarded command
    had been accepted (sixty-nine of sixty-nine, by a script over the
    copies).  Every negative other than that instrument is a
    [Definition], an [Example] or an [Inductive], never a [Check], so
    that an open evar cannot satisfy it.  Each negative was stripped of
    its refutation keyword in a copy of this WHOLE file, one at a time,
    compiled, and its error read; each of the seventeen copies stops
    inside the stripped command (by the File line of its error, compared
    by a script with the command's extent).  The kind recorded is the
    kind of that error, and each negative has positive controls beside
    it.  Quotations are Rocq 9.1.1's under this file's import list, with
    the error's environment block left out; Rocq prints the "cannot
    unify" parenthetical with the short names in scope, and a universe
    the stripped copy names after itself and a serial number is written
    <1>, <2>, ..., numbered afresh in each quotation in order of first
    appearance.  An "is unbound" message also prints the location of the
    universe it names, written (...) here and described in words.  The
    two targets and this file also compile on Coq 8.19.2 and 8.20.1, with
    no warning, against the prebuilt trees of this library for those
    versions: of the fifty-nine other [Category] modules of this file's
    closure, fifty-eight are this tree's sources byte for byte, and
    Structure/Coequalizer/Wide.v, which #459 corrects, differs in
    comments only (compared by script, comments and white space removed).
    Each of the seventeen stripped copies is refused there inside the
    stripped command, twelve at the File line of the Rocq 9.1.1 refusal
    and the five UNBOUND ones at the whole command, naming a universe
    located where Rocq 9.1.1 locates it.  Under 8.20.1 every error is the
    Rocq 9.1.1 one up to the serial names; under 8.19.2 fifteen are, N1
    prints the same inconsistency between serial names and N5 the same
    type mismatch with no parenthetical (compared by a script).

    KINDS.  Seventeen refutations, counted as the lines that open with the
    refutation keyword: NAME-ABSENCE (the instrument), UNIVERSE (N1-N6),
    UNBOUND (N7, N8, N13-N15), CONVERSION (N9, N12, N16) and TYPING (N10,
    N11): one, six, five, three and two.  A UNIVERSE refusal is an
    inconsistency or an undeclared constraint; an UNBOUND one is a
    universe the command needs that its closed binder does not name.  N7,
    N8 and N15 are refused in the body, at [wide_coequalizer_unique]; N13
    and N14 at the statement, at the notation [⊣] (the location each
    message prints).  N11 is the elimination rule for propositions: a
    proof of a [Prop] builds only proofs.  N10's parenthetical is the
    universe clause of a sort mismatch, [Type] where [Prop] is expected;
    it is counted TYPING by the head of its message.

    LABELS.  #459's builder measured most of the pins in scratch files
    under other names, recorded here so that the target headers can cite
    either.  Its walls file: [wa] is N1, [wb] N4 and [wc] N6, the last with
    the builder's shape, its return type left to inference; [ctlA],
    [ctlB] and [ctlC] are [p459_hwc_small], [p459_rel_at_points] and
    [p459_colimit_flexible].  Its Prop-subset file: [unsquash] is N11 and
    [ctl_squash] [p459_squash].  Its respect-field file:
    [rel_noproper_not_transitive] is [p459_unsat_rel_not_transitive].
    The review's saturation file: [srel_Equivalence] is
    [p459_sat_rel_Equivalence].  The review's probe file: [pointless_any]
    is [p459_pointless_any]; its [no_pointed_coequalizer_at_empty] and
    [pointed_iso] are the targets' [no_pointed_coequalizer_at_empty] and
    [pquot_collapse_iso_pointed], and its [no_functor_to_coequalizer] is
    the target's [no_pointed_elementary_coequalizers], restated over a
    function on objects ([p459_no_functor] reads it at a functor); its
    [Top_HWC_nobound], whose [About] reads [i <= o] back from a binder
    that omits it, is what N2 and N3 pin as refusals.  The final audit's
    colimit files: [fess_colimit] is the target's
    [pquot_wide_coequalizer_colimit] and [fess_colimit_pointed_at_empty]
    is [p459_colimit_pointed_at_empty].  Instance/Top/Quotient.v's walls:
    its W-a is N1-N3, its W-b N4, its W-c N5 and N6.  The labels are not
    constants: each refutation carries its own in a comment on the line
    above it, the instrument's reading "The instrument".

    ** Instance/Top/Quotient.v

    Controls of the small wide coequalizers.
    [Top_HasWideCoequalizers_small] at an index at or below the points,
    under the binder [@{i o h | i <= o, o < h +}] ([p459_hwc_small]), and
    its object, the quotient topology on [WSetsCoeq], at [eq_refl]
    ([p459_hwc_obj]).

    N1 (UNIVERSE).  The header's W-a: the instance read with its index at
    the hom universe, N1:
      Universe inconsistency. Cannot enforce h <= o because o < h.

    N2, N3 (UNIVERSE).  The same paragraph: the bound [i <= o] is not a
    choice of the instance but forced by [wcoeq_rel], whose glue
    constructor quantifies over the index.  The relation under a closed
    constraint list that declares the bound is formed
    ([p459_rel_bounded]); under the closed empty list [@{i o|}], N2:
      Universe constraints are not implied by the ones declared: i <= o
    The inductive itself declared afresh is formed with the bound
    ([p459_wrel]) and, under [@{i o|}], without its glue constructor
    ([p459_wrel_noglue]); with it, under [@{i o|}], N3, the same message.
    So the glue constructor is what forces the bound.

    N4 (UNIVERSE).  The header's W-b: the relation with its index at the
    points' universe is formed ([p459_rel_at_points]); with the index at
    the hom universe, read as a relation at [Type@{o}], N4:
      The term "fs" has type "I → SetoidMorphism@{o o o} A B" while it is
      expected to have type "I → SetoidMorphism@{<1> <1> <1>} ?A ?B"
      (universe inconsistency: Cannot enforce o = <1> because o < h <=
      <2> <= <1>).

    Controls of Construction 5.  X/A's points are X's, their equality IS
    [collapse_rel] at [eq_refl] ([p459_collapse_equiv]); the mediator is
    the competing map itself, as a setoid map and at every point, at
    [eq_refl] ([p459_desc_map_points], [p459_desc_map_at]); Construction 5
    in the elementary form at the flexible index and at Mac Lane's, the
    points of A ([p459_collapse_coequalizer], [p459_coequalizer_at_points]);
    the record read at the hom universe ([p459_coequalizer_at_hom]); the
    collapse map epic ([p459_collapse_epic]).

    N5, N6 (UNIVERSE).  The header's W-c: [IsWideCoequalizer] is not
    cumulative.  The record read at index [o] is not one at index [h],
    N5:
      The term "collapse_family_coequalizer X I p" has type
      "IsWideCoequalizer@{o h h} (collapse_family@{o h} X I p)
      (Top_collapse@{o} X I p) (collapse_proj@{o h} X I p)" while it is
      expected to have type "IsWideCoequalizer@{h h h}
      (collapse_family@{o h} X I p) (Top_collapse@{o} X I p)
      (collapse_proj@{o h} X I p)" (universe inconsistency: Cannot
      enforce o = h because o < h).
    So the colimit round trip, which reads the record at the hom
    universe, is fed the flexible binder at [h] ([p459_colimit_flexible],
    and the colimit form given a point of A, [p459_collapse_colimit]),
    and at [o], N6, the same message with the expected type
    "IsWideCoequalizer@{h h h} (collapse_family@{o h} X I p) ?q ?e".

    N7, N8 (UNBOUND).  The header's UNIVERSES: [collapse_iso_generic] and
    [collapse_empty_iso] carry a universe [u] their statements do not
    mention, [wide_coequalizer_unique]'s own.  Their bodies with [u] in
    the binder ([p459_iso_generic], [p459_empty_iso]), the comparison the
    identity on points both ways at [eq_refl] ([p459_iso_generic_to],
    [p459_iso_generic_from]); without it, N7 and N8, each:
      Universe <1> (...) is unbound.
    at the body's [wide_coequalizer_unique].

    N9 (CONVERSION).  The elementary X/∅ ≅ X is an isomorphism, not an
    equation: the underlying types are equal at [eq_refl]
    ([p459_empty_carrier]), the spaces are not, N9:
      The term "eq_refl" has type "Top_collapse_sub X (λ _ : X, False) =
      Top_collapse_sub X (λ _ : X, False)" while it is expected to have
      type "Top_collapse_sub X (λ _ : X, False) = X" (cannot unify
      "Top_collapse_sub X (λ _ : X, False)" and "X").

    Controls of the empty subset.  Every elementary wide coequalizer of
    the empty family at ∅ is pointless, whatever its construction
    ([p459_empty_coequalizer_pointless]);
    [collapse_empty_pointless] ([p459_collapse_empty_pointless]) is a
    readback of [Empty_Top]'s carrier: the same proof closes for every
    subset of ∅ ([p459_pointless_any]).

    ** Instance/Top/Quotient/Pairs.v

    Controls of the category of pairs: [Top_pairs] at [Category@{h h h}]
    ([p459_top_pairs]), the two functors ([p459_point_pair_functor],
    [p459_quotient_functor]); ⟨Y, *⟩'s subset is the Type-valued
    predicate y ≈ y0 at [eq_refl] ([p459_point_sub],
    [p459_point_pair_sub]).

    N10, N11 (TYPING).  The header's THE CATEGORY OF PAIRS, Type, not
    Prop: that predicate read as Prop-valued, N10:
      The term "y ≈ ptop_pt Y" has type "Type" while it is expected to
      have type "Prop" (universe inconsistency: Cannot enforce <1> <=
      Prop).
    Its squash eliminates into a proposition ([p459_squash]); unsquashed,
    as the transpose would need, N11:
      Incorrect elimination of "H" in the inductive type "inhabited": the
      return type has sort "Type" while it should be SProp or Prop.
      Elimination of an inductive object of sort Prop is not allowed on a
      predicate in sort "Type" because proofs can be eliminated only to
      build proofs.

    The respect field is a design choice, and is pinned as one, by two
    controls and no refutation.  With A saturated inside the
    identification, the four-case relation over [option X] is an
    equivalence with no field ([p459_sat_rel_Equivalence]); unsaturated
    and without the field it is not transitive
    ([p459_unsat_rel_not_transitive], at [bool] with the total equality
    and A := (= true)).

    Controls of the adjunction.  [pairs_quotient_adjunction] at its
    explicit record instance [Adjunction@{h h h h h h h h u h v}]
    ([p459_adjunction]); unit and counit at [eq_refl]
    ([p459_unit_eval], [p459_counit_some], [p459_counit_none]); its
    hom-set isomorphism IS [pairs_quotient_iso] at [eq_refl]
    ([p459_adj_is]).

    N12 (CONVERSION).  The book's display Top_*(X/A, Y) = Top^(2)(⟨X, A⟩,
    ⟨Y, *⟩) holds as that isomorphism in [Sets]; as an equation of hom
    types, N12:
      The term "eq_refl" has type "(fobj[PairQuotient] X ~{ Top_pointed
      }~> Y) = (fobj[PairQuotient] X ~{ Top_pointed }~> Y)" while it is
      expected to have type "(fobj[PairQuotient] X ~{ Top_pointed }~> Y)
      = (X ~{ Top_pairs }~> fobj[PointPair] Y)" (cannot unify
      "fobj[PairQuotient] X ~{ Top_pointed }~> Y" and "X ~{ Top_pairs }~>
      fobj[PointPair] Y").

    N13, N14 (UNBOUND).  The header's UNIVERSES: the adjunction's [v] is
    [Adjunction]'s binder [sp], in no constraint.  The target's
    [Build_Adjunction'] term at the explicit instance is accepted
    ([p459_adjunction_built]); stated through the notation [⊣] under the
    closed binder, [v] named in it, N13:
      Universe <1> (...) is unbound.
    at the statement's [⊣].  The finished constant reads through [⊣] once
    the binder names [v] ([p459_adjunction_notation]); when it does not,
    N14, the same message at the same place.

    Controls of X/A as the pushout X ⊔_A ∗, apex at [eq_refl]
    ([p459_pushout], [p459_pushout_apex]).

    Controls of the universal-arrow reading, the colimit form, for every
    A.  X/A is the colimit of the point-inclusions of A, a
    [WideCoequalizer], for every pair and with no point of A
    ([p459_wide_colimit]), at the type of Construction 5's
    [collapse_colimit] written as Instance/Top/Quotient.v writes it
    ([p459_wide_colimit_collapse_type], beside [p459_collapse_colimit]);
    its apex is [pquot_space X], its leg out of X is [pquot_in X], its leg
    out of * sends the one point to the left adjoint's basepoint, and the
    left adjoint's underlying space is its apex, all at [eq_refl]
    ([p459_wide_colimit_apex], [p459_wide_colimit_in],
    [p459_wide_colimit_base], [p459_wide_colimit_quotient]); at ⟨X, ∅⟩
    its apex is X ⊔ * ([p459_wide_colimit_empty]); and every colimit of
    the family has a point ([p459_colimit_point]), at ⟨∅, ∅⟩ the new
    point [None] ([p459_colimit_pointed_at_empty]).

    Controls of the elementary record given a point of A.  X/A is then an
    elementary wide coequalizer of the point-inclusions
    ([p459_pquot_coequalizer]), isomorphic to Construction 5's X/A in
    [Top] with [u] in the binder
    ([p459_pquot_collapse_iso]), x ↦ [Some x] and [None] ↦ a0 at
    [eq_refl] ([p459_pquot_collapse_iso_to],
    [p459_pquot_collapse_iso_from_none]), and in [Top_pointed]
    ([p459_pquot_collapse_iso_pointed], the basepoint read back at
    [eq_refl] by [p459_collapse_pointed_pt]).

    N15 (UNBOUND).  The same header's UNIVERSES: [pquot_collapse_iso]'s
    body without [u], N15, the message of N7 at the body's
    [wide_coequalizer_unique].

    N16 (CONVERSION).  X/∅ is X₊ in [Top] ([p459_empty_sum_iso]), [Some x]
    ↦ [inl x] and [None] ↦ [inr ttt] at [eq_refl] ([p459_empty_sum_some],
    [p459_empty_sum_none]); as an equation of spaces, N16:
      The term "eq_refl" has type "pquot_space (empty_pair X) =
      pquot_space (empty_pair X)" while it is expected to have type
      "pquot_space (empty_pair X) = Sum_Top X Point_Top" (cannot unify
      "pquot_space (empty_pair X)" and "Sum_Top X Point_Top").

    Controls of the elementary record at A = ∅.  Under the elementary
    reading a pointed X/A is refuted at Pairs.v's construction
    ([p459_pquot_empty_not_coequalizer], [p459_pquot_needs_point]) and for
    every construction: no pointed space's underlying space is an
    elementary wide coequalizer of the empty family at ∅
    ([p459_no_pointed_coequalizer]); no assignment of a pointed space to
    each pair makes every underlying space one ([p459_no_assignment]), a
    functor's object map among them ([p459_no_functor]); and at ⟨∅, ∅⟩ no
    colimit's apex carries one ([p459_empty_colimit_not_elementary]).
    They restate the targets' [no_pointed_coequalizer_at_empty],
    [no_pointed_elementary_coequalizers] and
    [empty_colimit_not_elementary], which depend on no construction of
    X/A.  They are statements about the elementary reading, the record
    [IsWideCoequalizer]; the universal-arrow reading is the colimit form
    pinned above, under which the two constructions agree at every A.

    NOT PINNED HERE.  (a) [About] readbacks as such, the headers' [Set]
    censuses and their attributions to first carriers: pinned only where
    a closed binder carries them or a refusal does (N1-N8, N13-N15).
    (b) Flip censuses ([Defined] against [Qed]) and the closure of the
    targets under [Print Assumptions]: measurements of the build rather
    than of commands; the Makefile's print-assumptions gate is where
    closure is kept.  What a flip decides is pinned where it has a
    command: [p459_iso_generic_to], [p459_unit_eval],
    [p459_pquot_collapse_iso_to] and [p459_pquot_collapse_iso_from_none]
    hold at [eq_refl].
    (c) Any necessity of the respect field of [PairTop]: there is none,
    and the two controls above say why.  (d) The pushout for other
    topologies on A (argued in Pairs.v's header), an initial object of
    [Top_pointed] and what a left adjoint must send ⟨∅, ∅⟩ to: not
    formalized; what the adjoint built here sends every pair to is the
    coequalizer in the universal-arrow reading, pinned above
    ([p459_wide_colimit_quotient]).

    The guard block at the end names the one hundred and fifty-four
    constants of the two targets, so that a rename breaks this file:
    fifty-four of Instance/Top/Quotient.v and one hundred of
    Instance/Top/Quotient/Pairs.v, exactly the [Definition] and
    [Parameter] entries [Print Module] gives for each (the four generated
    schemes of [wcoeq_rel], the five record projections and the fourteen
    [Program] obligations included) together with the inductive
    [wcoeq_rel] and its four constructors and the records [PairTop] and
    [PairMap] with their constructors [Build_PairTop] and
    [Build_PairMap].  The obligations are not reachable by their short
    names under this import list; each is named by the shorter name
    [Locate] gives for it.  Under the full import list, [Locate] lists
    exactly one object for each of the one hundred and fifty-four.

--------
* 探查 Mac Lane V.9 的坍塌 X/A 及成对类别（问题 #459）

固定了两个文件 #459 为 Mac Lane 添加的测量边界
§V.9，书本页码 pp. 134-135（PDF 页码 pp. 143-144）：目录 ID
maclane:V.9:construction5，通过将 X 的子集 A 压缩为一点得到的空间 X/A，A 的点嵌入的宽余联范畴（Instance/Top/Quotient.v，使用树的 [HasWideCoequalizers] 的第一个元素）；以及 maclane:V.9:construction6，成对 ⟨X, A⟩ 构成的范畴 [Top_pairs] 以及商函子 ⟨X, A⟩ ↦ X/A，它是 Y ↦ ⟨Y, *⟩ 的左伴随（Instance/Top/Quotient/Pairs.v）。书中没有编号任何构造；这些 ID 是名字。Mac Lane 将一对元素的共同等化子定义为基本元素（书第64页，公式(6)），将其读作到对角线的通用箭头（第65页），并以“同样的方式”定义任意映射集合的共同等化子；在每个非空映射集合上，这两种读法是一致的，而书中没有处理空集合。作为通用箭头来读的话，一个以 * 为顶点的形状的余极限，Structure/Coequalizer/Wide.v 的 [WideCoequalizer]，在每个 A 上两种构造都是一致的：Pairs.v 的 X/A，(X ⊔ {∗})/(A ∼ ∗)，对于每个 A，包括空集合，都是该余极限，其中为空集合时为 X ⊔ *。按照初等方式读取时，如记录所示 [IsWideCoequalizer], X/∅ 就是 X 本身，当 X 存在时毫无意义，并且这两个结构在 A = ∅ 处分离：Pairs.v 证明每当 A 有一个点时，X/A 是初等宽余核，并且在初等解读下，对每个结构，它在 ⟨∅, ∅⟩ 处否定了有点的 X/A。该文件将这些结果重新陈述为对照。N1、N4、N6-N8、N11 和 N13 重新陈述了在临时文件中测量的拒绝 #459 的构建；N2、N3、N5、N9、N10、N12 和 N14-N16 是该文件自身的。每一个都记录在目标头文件中，并通过其 N 号引用。阳性对照独立地重述了这些文件的主张。

导入列表，通过比较 [Require] 的脚本行来测量。首先是 Instance/Top/Quotient.v 文件中前十行逐字且按顺序，然后是该文件；接着是 Instance/Top/Quotient/Pairs.v 添加的十一行，按其顺序（Theory/Functor.v, Theory/Adjunction.v, Construction/Opposite.v, Functor/Opposite.v, Structure/Cone.v, Structure/Limit/Preservation.v, Structure/Pullback.v, Structure/Pushout.v, Instance/Parallel.v, Instance/Top/Coproduct.v, Instance/Top/Homotopy.v），以及该文件。二十三行：二十二个不同的 [Require] 属于两个目标，其中包括 Instance/Top/Quotient.v，以及 Pairs.v，该文件没有任何目标需要。在此列表下，文件的依赖闭包是六十一 [Category] 模块（[Print Libraries]），其中包括两个目标。Instance/Top/Homotopy.v 需要 stdlib reals 并打开 [R_scope]，因此下面的类型乘积和和在 [%type] 下写出。一个较短的导入列表会让一个探针无缘无故通过。

纪律。该工具从两个方面进行了检查：缺失名称的反驳因该原因被拒绝（“在当前环境中未找到引用探针459_absent_name。”），以及该文件中每一个不是反驳的六十九个定义、示例和归纳（四十五、二十二和两个），在该整个文件的副本中用反驳关键字包裹后，在该命令下构建会停止，并报告守卫命令已被接受（六十九个中的六十九个，由副本上的脚本完成）。除该仪器外，每个负例都是 [Definition]、[Example] 或 [Inductive]，从不出现 [Check]，因此一个打开的 evar 不能满足它。每个负例在此整个文件的副本中依次去掉了其驳斥关键字，进行了编译，并读取了其错误；十七个副本中的每一个都在去掉的命令内停止（通过其错误的 File 行，由脚本与命令的范围进行比较）。记录的类型是该错误的类型，每个负例旁边都有正面控件。引用是在此文件的导入列表下的 Rocq 9.1.1 中，错误的环境块被省略；Rocq 打印带有作用域内短名称的“无法统一”括号，宇宙在剥离的副本中用其自身名称和一个序列号命名，标记为 <1>、<2>、…，每个引用中按首次出现的顺序重新编号。还会打印“未绑定”消息，显示其命名的宇宙的位置，这里写作（...）并用文字描述。这两个目标以及此文件也可以在 Coq 8.19.2 和 8.20.1 上编译，没有警告，针对这些版本的该库预构建树：在该文件闭包的其他五十九个 [Category] 模块中，有五十八个是此树的源文件逐字相同的，而 Structure/Coequalizer/Wide.v（由 #459 修正）仅在注释上有所不同（通过脚本比较，注释和空白已删除）。每份十七份剥离的副本都在剥离命令内被拒绝，其中十二份在Rocq 9.1.1拒绝的文件行，五份未绑定的在整个命令中，命名一个位于Rocq 9.1.1定位的宇宙。在8.20.1下，每个错误都是Rocq 9.1.1的错误，直到序列名；在8.19.2下，有十五个，N1在序列名之间打印相同的不一致，而N5打印相同类型的不匹配，没有括号（由脚本比较）。

种类。十七个反驳，计算为以反驳关键字开头的行：NAME-ABSENCE（工具）、UNIVERSE（N1-N6）、UNBOUND（N7、N8、N13-N15）、CONVERSION（N9、N12、N16）和TYPING（N10、N11）：分别为一个、六个、五个、三个和两个。UNIVERSE 拒绝是指不一致或未声明的约束；UNBOUND 拒绝是指命令需要而其闭合绑定器未命名的宇宙。N7、N8 和 N15 在主体中被拒绝，在 [wide_coequalizer_unique]；N13 和 N14 在语句中被拒绝，在符号 [⊣]（每条消息打印的位置）。N11 是命题的消解规则：a 对 [Prop] 的证明只构建证明。N10 的括号部分是类型不匹配的宇宙子句，[Type] 预期为 [Prop]；它被消息的标题计为 TYPING。

标签。#459 的构建者在草稿文件中测量了大多数引脚，并使用其他名称记录在此，以便目标头文件可以引用其中任意一个。其 walls 文件：[wa] 是 N1，[wb] 是 N4，[wc] 是 N6，最后一个使用构建者的形状，其返回类型留作推断；[ctlA]、[ctlB] 和 [ctlC] 分别是 [p459_hwc_small]、[p459_rel_at_points] 和 [p459_colimit_flexible]。其 Prop 子集文件：[unsquash] 是 N11，[ctl_squash] 是 [p459_squash]。其 respect-field 文件：[rel_noproper_not_transitive] 是 [p459_unsat_rel_not_transitive]。审查的饱和文件：[srel_Equivalence] 是 [p459_sat_rel_Equivalence]。审查的探测文件：[pointless_any] 是 [p459_pointless_any]；它的 [no_pointed_coequalizer_at_empty] 和 [pointed_iso] 是目标的 [no_pointed_coequalizer_at_empty] 和 [pquot_collapse_iso_pointed]，其 [no_functor_to_coequalizer] 是目标的 [no_pointed_elementary_coequalizers]，在对象上的一个函数中重述（[p459_no_functor] 在函子中读取它）；它的 [Top_HWC_nobound]，其 [About] 从省略它的绑定器中读取 [i <= o]，是 N2 和 N3 标记为拒绝的。最终审核的余极文件：[fess_colimit] 是目标的 [pquot_wide_coequalizer_colimit]，[fess_colimit_pointed_at_empty] 是 [p459_colimit_pointed_at_empty]。Instance/Top/Quotient.v 的墙：它的 W-a 是 N1-N3，W-b 是 N4，W-c 是 N5 和 N6。这些标签不是常量：每个反驳在其上方一行的注释中都有自己的标签，仪器的读数“仪器”。

** 实例/顶部/商.v

小型广义等同器的控制。[Top_HasWideCoequalizers_small] 在一个等于或低于点的索引处，在绑定器 [@{i o h | i <= o, o < h +}] ([p459_hwc_small]) 下，以及其对象 [WSetsCoeq] 上的商拓扑，在 [eq_refl] ([p459_hwc_obj]) 处。

N1（宇宙）。头部的 W-a：使用其在同一宇宙 N1 的索引读取实例：
  宇宙不一致。无法强制 h <= o，因为 o < h。

N2, N3（宇宙）。同一段落：绑定的 [i <= o] 不是实例的选择，而是由 [wcoeq_rel] 强制的，其 glue 构造函数对索引量化。在声明该绑定的闭合约束列表下，形成的关系是 ([p459_rel_bounded])；在闭合的空列表 [@{i o|}] 下，N2: 宇宙约束不会被声明的约束所暗示：i <= o。自我重新声明的归纳体是用绑定 ([p459_wrel]) 形成的，并且在 [@{i o|}] 下，没有它的 glue 构造函数 ([p459_wrel_noglue])；有它时，在 [@{i o|}] 下，N3，同样的信息。所以胶水构造函数就是强制边界的东西。

N4（宇宙）。头的 W-b：在点的宇宙中，它与索引的关系已形成（[p459_rel_at_points]）；在同宇宙的索引下，读取为 [Type@{o}] 的一个关系，N4：
  术语“fs”的类型为“I → SetoidMorphism@{o o o} A B”，而预期类型为“I → SetoidMorphism@{<1> <1> <1>} ?A ?B”（宇宙不一致：无法强制 o = <1>，因为 o < h <= <2> <= <1>）。

构造的控制 5. X/A 的点是 X 的点，它们的相等性是 [collapse_rel] 在 [eq_refl]（[p459_collapse_equiv]）；调解者是竞争映射自身，作为一个集合等价映射且在每个点上，在 [eq_refl]（[p459_desc_map_points], [p459_desc_map_at]）；构造 5 在基本形式下于灵活索引处以及在 Mac Lane 的处，A 的点（[p459_collapse_coequalizer], [p459_coequalizer_at_points]）；在同质宇宙中读取的记录（[p459_coequalizer_at_hom]）；塌缩映射为满射（[p459_collapse_epic]）。

N5, N6（宇宙）。标题的 W-c: [IsWideCoequalizer] 不是累积的。在索引 [o] 读取的记录不是索引 [h] 的记录，
N5:
  术语“collapse_family_coequalizer X I p”的类型为
  “IsWideCoequalizer@{o h h} (collapse_family@{o h} X I p)
  (Top_collapse@{o} X I p) (collapse_proj@{o h} X I p)”，而预期类型为
  “IsWideCoequalizer@{h h h} (collapse_family@{o h} X I p) (Top_collapse@{o} X I p)
  (collapse_proj@{o h} X I p)”（宇宙不一致：无法强制 o = h，因为 o < h）。因此，共极限往返操作，它在同伦宇宙中读取记录，会将灵活绑定器提供给 [h]（[p459_colimit_flexible]，以及给出 A 点的共极限形式，[p459_collapse_colimit]），并且在 [o]，N6，发送相同消息，其预期类型为 "IsWideCoequalizer@{h h h} (collapse_family@{o h} X I p) ?q ?e"。

N7、N8（未绑定）。头部的宇宙：[collapse_iso_generic] 和 [collapse_empty_iso] 携带一个 [u] 宇宙，他们的声明未提及 [wide_coequalizer_unique] 自己的。它们在绑定器中的主体与 [u]（[p459_iso_generic]，[p459_empty_iso]），在 [eq_refl]（[p459_iso_generic_to]，[p459_iso_generic_from]）上进行了双向的点同一性比较；如果没有它，N7 和 N8 各自：
      宇宙 <1> (...) 未绑定。
    在主体的 [wide_coequalizer_unique] 上。

N9（转换）。初等的 X/∅ ≅ X 是一个同构，而不是一个等式：底层类型在 [eq_refl]（[p459_empty_carrier]）处相等，但空间不相等，N9：
  术语“eq_refl”的类型为“Top_collapse_sub X (λ _ : X, False) = Top_collapse_sub X (λ _ : X, False)”，而期望的类型为“Top_collapse_sub X (λ _ : X, False) = X”（无法统一“Top_collapse_sub X (λ _ : X, False)”和“X”）。

空子集的控制。空集合 ∅ 上的每个基本广义共等化器都是无点的，无论其构造如何 ([p459_empty_coequalizer_pointless])；[collapse_empty_pointless] ([p459_collapse_empty_pointless]) 是 [Empty_Top] 的载体的回读：对 ∅ 的每个子集 ([p459_pointless_any]) 同样的证明都是成立的。

** 实例/顶部/商/对.v

成对类别的控制：[Top_pairs] 在 [Category@{h h h}] ([p459_top_pairs])，两个函子 ([p459_point_pair_functor], [p459_quotient_functor])；⟨Y, *⟩ 的子集是类型值谓词 y ≈ y0 在 [eq_refl] ([p459_point_sub], [p459_point_pair_sub])。

N10, N11（打字）。标题是 PAIRS 的类别，类型，而不是 Prop：该谓词被读取为 Prop 值，N10：
  术语 "y ≈ ptop_pt Y" 的类型是 "Type"，而预期类型是 "Prop"（宇宙不一致：无法强制执行 <1> <= Prop）。它的 squash 会消除为命题（[p459_squash]）；未 squash 时，如转置所需，N11：
  在归纳类型 "inhabited" 中对 "H" 的消除不正确：返回类型的类别是 "Type"，而它应该是 SProp 或 Prop。不允许在“Type”类型的谓词上消除 Prop 类型的归纳对象，因为证明只能通过消除来构造其他证明。

尊重字段是一种设计选择，由两个控件固定为一个，并且没有反驳。在识别内部饱和的情况下，[option X] 上的四案例关系是一个没有字段（[p459_sat_rel_Equivalence]）的等价关系；未饱和且没有该字段时，它不是可传递的（[p459_unsat_rel_not_transitive]，在 [bool] 处与总体相等且 A := (= true)）。

伴随的控制。在其显式记录实例 [Adjunction@{h h h h h h h h u h v}]（[p459_adjunction]）上的 [pairs_quotient_adjunction]；在 [eq_refl]（[p459_unit_eval], [p459_counit_some], [p459_counit_none]）上的单位和余单位；其 Hom 集同构是 [pairs_quotient_iso] 在 [eq_refl]（[p459_adj_is]）上。

N12（转换）。书中显示 Top_*(X/A, Y) = Top^(2)(⟨X, A⟩, ⟨Y, *⟩) 成立，因为它在 [Sets] 中是那个同构；作为同态类型的方程，N12：
      术语“eq_refl”的类型是“(fobj[PairQuotient] X ~{ Top_pointed }~> Y) = (fobj[PairQuotient] X ~{ Top_pointed }~> Y)”，而期望类型是“(fobj[PairQuotient] X ~{ Top_pointed }~> Y) = (X ~{ Top_pairs }~> fobj[PointPair] Y)”（无法统一“fobj[PairQuotient] X ~{ Top_pointed }~> Y”和“X ~{ Top_pairs }~> fobj[PointPair] Y”）。

N13, N14（未绑定）。标题的宇宙：附加的 [v] 是 [Adjunction] 的绑定器 [sp]，没有任何约束。显式实例中目标的 [Build_Adjunction'] 项被接受（[p459_adjunction_built]）；通过符号 [⊣] 在闭合绑定器下表述，[v] 在其中命名，N13：
  宇宙 <1> (...) 是未绑定的。
在语句的 [⊣]。完成的常量通过 [⊣] 读取，一旦绑定器命名为 [v]（[p459_adjunction_notation]）；当没有时，N14，在相同位置显示相同信息。

X/A 的控制作为推出 X ⊔_A ∗，顶点在 [eq_refl]（[p459_pushout]，[p459_pushout_apex]）。

普遍箭头读法的控制，余极限形式，对于每个 A。X/A 是 A 的点包含的余极限，对于每一对并且没有 A 的点，在 Construction 5 的类型上写作 Instance/Top/Quotient.v （如下所示）；它的顶点是 [pquot_space X]，它从 X 出发的腿是 [pquot_in X]，从 * 出发的腿将唯一的点发送到左伴随的基点，左伴随的底层空间是它的顶点，都在 [eq_refl]（[p459_wide_colimit_apex], [p459_wide_colimit_in], [p459_wide_colimit_base], [p459_wide_colimit_quotient]）；在 ⟨X, ∅⟩ 上，它的顶点是 X ⊔ * （[p459_wide_colimit_empty]）；并且该族的每个余极限都有一个点（[p459_colimit_point]），在 ⟨∅, ∅⟩ 上新的点是 [None] （[p459_colimit_pointed_at_empty]）。

给定点 A 的基本记录的控制。X/A 然后是点包含 ([p459_pquot_coequalizer]) 的一个基本宽共等化子，与构造 5 中 [Top] 的 X/A 同构，在绑定器 ([p459_pquot_collapse_iso]) 中有 [u]，映射 x ↦ [Some x] 和 [None] ↦ a0 于 [eq_refl] ([p459_pquot_collapse_iso_to], [p459_pquot_collapse_iso_from_none])，并且在 [Top_pointed] ([p459_pquot_collapse_iso_pointed]，中通过 [p459_collapse_pointed_pt] 读取回的基点 [eq_refl])。

N15（未绑定）。相同标题的宇宙：[pquot_collapse_iso]的主体没有[u]，N15，主体中N7的信息位于[wide_coequalizer_unique]。

N16（转换）。X/∅ 在 [Top]（[p459_empty_sum_iso]）、[Some x] ↦ [inl x] 和 [None] ↦ [inr ttt] 于 [eq_refl]（[p459_empty_sum_some]、[p459_empty_sum_none]）；作为空间的方程，N16：
      术语“eq_refl”的类型是“pquot_space (empty_pair X) = pquot_space (empty_pair X)”，而期望的类型是“pquot_space (empty_pair X) = Sum_Top X Point_Top”（无法统一“pquot_space (empty_pair X)”和“Sum_Top X Point_Top”）。

对 A = ∅ 的初级记录进行控制。在 基本
    读取带尖X/A的做法在Pairs.v的构造中被推翻
    （[p459_pquot_empty_not_coequalizer]，[p459_pquot_needs_point]）以及
    每一个构造：没有带点空间的底层空间是
    空族在∅时的初级广域协等化器
    （[p459_no_pointed_coequalizer]）;不将带点空间赋值为
    每对空间都使每个底层空间为1（[p459_no_assignment]），a
    函子对象映射（[p459_no_functor]）;在 ⟨∅ 处，∅⟩ 否
    Colimit的Apex有1个（[p459_empty_colimit_not_elementary]）。他们重申了目标的 [no_pointed_coequalizer_at_empty]、[no_pointed_elementary_coequalizers] 和 [empty_colimit_not_elementary]，这些不依赖于 X/A 的构造。它们是关于基本读取记录 [IsWideCoequalizer] 的陈述；通用箭头读取是上面固定的余极形式，在该形式下，两种构造在每个 A 上一致。

未固定在此处。(a) [About] 读取如上，标题的 [Set] 人口普查及其归属于首批承运人：仅在封闭的活页夹携带它们或拒绝接受时才固定（N1-N8, N13-N15）。(b) 翻转人口普查（[Defined] 对 [Qed]）以及在 [Print Assumptions] 下目标的关闭：测量的是构建而非指令；Makefile 的 print-assumptions 门控是保持关闭的位置。翻转决定的内容固定在其有指令的位置：[p459_iso_generic_to], [p459_unit_eval], [p459_pquot_collapse_iso_to] 和 [p459_pquot_collapse_iso_from_none] 保存在 [eq_refl]。(c) [PairTop] 的 respect 字段的任何必要性：没有必要，上面两个控件说明了原因。 (d) 对 A 上其他拓扑结构的推挤（在 Pairs.v 的标题中论证）、[Top_pointed] 的初始对象以及左伴随必须将 ⟨∅, ∅⟩ 发送到的位置：未形式化；这里构建的伴随将每对发送到的位置是在通用箭头读法中的等化器，上面已固定 ([p459_wide_colimit_quotient])。

在末尾的守护块中列出了两个目标的154个常量，以便重命名会破坏此文件：Instance/Top/Quotient.v中的54个，以及Instance/Top/Quotient/Pairs.v中的100个，正好是[Definition]和[Parameter]为每个条目提供的[Print Module]（包括[wcoeq_rel]生成的四个方案、五个记录投影和十四个[Program]义务），还有归纳[wcoeq_rel]及其四个构造函数，以及记录[PairTop]和[PairMap]及其构造函数[Build_PairTop]和[Build_PairMap]。在此导入列表下，这些义务无法通过它们的简短名称访问；每个义务都由 [Locate] 为其提供的较短名称命名。在完整的导入列表下，[Locate] 为一百五十四个中的每一个列出了恰好一个对象。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Coequalizer.Wide.
Require Import Category.Instance.Parallel.Wide.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Subspace.TypeValued.
Require Import Category.Instance.Top.Quotient.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Top.Coproduct.
Require Import Category.Instance.Top.Homotopy.
Require Import Category.Instance.Top.Quotient.Pairs.

Generalizable All Variables.

(** ** Instrument: the refutation keyword is live / ** 工具：反驳关键词是实时的 *)

(* The instrument / 乐器 *)
Fail Check probe459_absent_name.

(** ** Instance/Top/Quotient.v: small wide coequalizers, W-a and W-b / ** Instance/Top/Quotient.v：小宽共同余子器，W-a 和 W-b *)

(*
CONTROL: the instance at an index at or below the points, the class's
   first inhabitant, and its object read back at [eq_refl].

--------
控制：索引在点数处或以下的实例，类的第一个实例，以及在 [eq_refl] 处读取的对象。
*)
Definition p459_hwc_small@{i o h | i <= o, o < h +} :
  HasWideCoequalizers@{i h h} Top@{h o} :=
  Top_HasWideCoequalizers_small@{i o h}.

Example p459_hwc_obj@{i o h | i <= o, o < h +}
  {I : Type@{i}} {x y : Top@{h o}} (fs : I → x ~{Top@{h o}}~> y) :
  `1 (@wide_coeq Top@{h o} Top_HasWideCoequalizers_small@{i o h} I x y fs)
    = TQuot y (WSetsCoeq@{i o} (fun i => continuous_map (fs i)))
        (wsets_coeq_proj@{i o} (fun i => continuous_map (fs i))) := eq_refl.

(* N1 *)
Fail Definition p459_hwc_at_hom@{o h | o < h +} :
  HasWideCoequalizers@{h h h} Top@{h o} :=
  Top_HasWideCoequalizers_small@{h o h}.

(*
CONTROL: the relation under a closed constraint list that declares
   [i <= o].

--------
控制：在声明 [i <= o] 的闭合约束列表下的关系。
*)
Definition p459_rel_bounded@{i o | i <= o} {I : Type@{i}}
  {A B : SetoidObject@{o o}} (fs : I → SetoidMorphism@{o o o} A B) :
  B → B → Type@{o} := wcoeq_rel@{i o} fs.

(* N2 *)
Fail Definition p459_rel_unbounded@{i o |} {I : Type@{i}}
  {A B : SetoidObject@{o o}} (fs : I → SetoidMorphism@{o o o} A B) :
  B → B → Type@{o} := wcoeq_rel@{i o} fs.

(*
CONTROL: [wcoeq_rel] declared afresh under the closed binder with the
   bound, and without its glue constructor under the binder without it.

--------
控制：[wcoeq_rel] 在封闭的绑定器下重新声明，有绑定，但在没有绑定器的情况下没有其胶水构造函数。
*)
Inductive p459_wrel@{i o | i <= o} {I : Type@{i}} {A B : SetoidObject@{o o}}
  (fs : I → SetoidMorphism@{o o o} A B) : B → B → Type@{o} :=
  | p459_wbase : ∀ b1 b2 : B, b1 ≈ b2 → p459_wrel b1 b2
  | p459_wglue : ∀ (i j : I) (a : A), p459_wrel (fs i a) (fs j a)
  | p459_wsym : ∀ b1 b2 : B, p459_wrel b1 b2 → p459_wrel b2 b1
  | p459_wtrans : ∀ b1 b2 b3 : B,
      p459_wrel b1 b2 → p459_wrel b2 b3 → p459_wrel b1 b3.

Inductive p459_wrel_noglue@{i o |} {I : Type@{i}}
  {A B : SetoidObject@{o o}} (fs : I → SetoidMorphism@{o o o} A B) :
  B → B → Type@{o} :=
  | p459_nbase : ∀ b1 b2 : B, b1 ≈ b2 → p459_wrel_noglue b1 b2
  | p459_nsym : ∀ b1 b2 : B, p459_wrel_noglue b1 b2 → p459_wrel_noglue b2 b1
  | p459_ntrans : ∀ b1 b2 b3 : B,
      p459_wrel_noglue b1 b2 → p459_wrel_noglue b2 b3 →
      p459_wrel_noglue b1 b3.

(* N3 *)
Fail Inductive p459_wrel_unbounded@{i o |} {I : Type@{i}}
  {A B : SetoidObject@{o o}} (fs : I → SetoidMorphism@{o o o} A B) :
  B → B → Type@{o} :=
  | p459_ubase : ∀ b1 b2 : B, b1 ≈ b2 → p459_wrel_unbounded b1 b2
  | p459_uglue : ∀ (i j : I) (a : A), p459_wrel_unbounded (fs i a) (fs j a)
  | p459_usym : ∀ b1 b2 : B,
      p459_wrel_unbounded b1 b2 → p459_wrel_unbounded b2 b1
  | p459_utrans : ∀ b1 b2 b3 : B,
      p459_wrel_unbounded b1 b2 → p459_wrel_unbounded b2 b3 →
      p459_wrel_unbounded b1 b3.

(* CONTROL: the relation with its index at the points' universe. / 控制：与其在点的宇宙中的索引的关系。 *)
Definition p459_rel_at_points@{o h | o < h +} (I : Type@{o})
  (A B : SetoidObject@{o o}) (fs : I → SetoidMorphism@{o o o} A B) :
  B → B → Type@{o} := wcoeq_rel fs.

(* N4 *)
Fail Definition p459_rel_at_hom@{o h | o < h +} (I : Type@{h})
  (A B : SetoidObject@{o o}) (fs : I → SetoidMorphism@{o o o} A B) :
  B → B → Type@{o} := wcoeq_rel fs.

(** ** Instance/Top/Quotient.v: Construction 5 and W-c / ** Instance/Top/Quotient.v：构造 5 和 W-c *)

(*
CONTROL: X/A's points are those of X, and their equality IS
   [collapse_rel], at [eq_refl].

--------
控制：X/A 的点数属于 X，它们的相等是 [collapse_rel]，在 [eq_refl]。
*)
Example p459_collapse_equiv@{o} (X : TopSpace@{o}) (I : Type@{o})
  (p : I → X) (x y : X) :
  @equiv _ (is_setoid (top_carrier (Top_collapse X I p))) x y
    = collapse_rel X I p x y := eq_refl.

(*
CONTROL: the mediator is the competing map itself, as a setoid map and
   at every point, at [eq_refl].

--------
控制：中介者是竞争地图本身，作为一个等价映射，并且在每一点上，在 [eq_refl]。
*)
Example p459_desc_map_points@{o h | o < h +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) {Z : Top@{h o}} (k : X ~{Top@{h o}}~> Z)
  (Hk : ∀ i j : I, k ∘ collapse_family X I p i ≈ k ∘ collapse_family X I p j) :
  continuous_map (collapse_desc_map X I p k Hk) = collapse_med X I p k Hk
  := eq_refl.

Example p459_desc_map_at@{o h | o < h +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) {Z : Top@{h o}} (k : X ~{Top@{h o}}~> Z)
  (Hk : ∀ i j : I, k ∘ collapse_family X I p i ≈ k ∘ collapse_family X I p j)
  (x : X) :
  continuous_map (collapse_desc_map X I p k Hk) x = continuous_map k x
  := eq_refl.

(*
CONTROL: Construction 5 in the elementary form at the flexible index,
   and at Mac Lane's index, the points of A.

--------
控制：在灵活指标的初等形式下构造5，以及在Mac Lane指标下，A的点。
*)
Definition p459_collapse_coequalizer@{o h i | o < h, o <= i +}
  (X : TopSpace@{o}) (A : X → Type@{o}) :
  IsWideCoequalizer@{i h h} (C := Top@{h o}) (collapse_sub_family X A)
    (Top_collapse_sub X A) (collapse_sub_proj X A) :=
  collapse_coequalizer@{o h i} X A.

Definition p459_coequalizer_at_points@{o h | o < h +} (X : TopSpace@{o})
  (A : X → Type@{o}) :
  IsWideCoequalizer@{o h h} (C := Top@{h o}) (collapse_sub_family X A)
    (Top_collapse_sub X A) (collapse_sub_proj X A) :=
  collapse_coequalizer@{o h o} X A.

(* CONTROL: the record read at the hom universe. / 控制：在同源宇宙中读取的记录。 *)
Definition p459_coequalizer_at_hom@{o h | o < h +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) :
  IsWideCoequalizer@{h h h} (C := Top@{h o}) (collapse_family X I p)
    (Top_collapse X I p) (collapse_proj X I p) :=
  collapse_family_coequalizer@{o h h} X I p.

(* N5 *)
Fail Definition p459_coequalizer_cumulative@{o h | o < h +}
  (X : TopSpace@{o}) (I : Type@{o}) (p : I → X) :
  IsWideCoequalizer@{h h h} (C := Top@{h o}) (collapse_family X I p)
    (Top_collapse X I p) (collapse_proj X I p) :=
  collapse_family_coequalizer@{o h o} X I p.

(*
CONTROL: the colimit round trip fed the record at the hom universe,
   and the colimit form given a point of A.

--------
控制：余圆往返将记录传送到同一宇宙，并且余圆形式在 A 点上给出。
*)
Definition p459_colimit_flexible@{o h | o < h +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) (i0 : I) :=
  is_wide_coequalizer_colimit (C := Top@{h o}) (collapse_family@{o h} X I p)
    i0 (collapse_family_coequalizer@{o h h} X I p).

Definition p459_collapse_colimit@{o h | o < h +} (X : TopSpace@{o})
  (A : X → Type@{o}) (a0 : collapse_sub_points X A) :
  WideCoequalizer (AWide (C := Top@{h o}) (collapse_sub_family X A)) :=
  collapse_colimit X A a0.

(* N6 *)
Fail Definition p459_colimit_at_points@{o h | o < h +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) (i0 : I) :=
  is_wide_coequalizer_colimit (C := Top@{h o}) (collapse_family@{o h} X I p)
    i0 (collapse_family_coequalizer@{o h o} X I p).

(* CONTROL: the collapse map is epic. / 控制点：坍塌地图很史诗。 *)
Definition p459_collapse_epic@{o h | o < h +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) : Epic (collapse_proj X I p) :=
  collapse_proj_epic X I p.

(** ** Instance/Top/Quotient.v: the comparisons and their extra universe / ** Instance/Top/Quotient.v：比较及其额外的宇宙 *)

(*
CONTROL: the direct collapse against the generic wide coequalizer, with
   [u] in the binder, the identity on points both ways at [eq_refl].

--------
控制：针对通用宽余等化器的直接塌陷，结合器中有 [u]，在 [eq_refl] 上两边的点恒等。
*)
Definition p459_iso_generic@{o h u | o < h, h < u +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) :
  Top_collapse X I p ≅[Top@{h o}] twcoeq_obj@{o o h} (collapse_family X I p) :=
  wide_coequalizer_unique _ (collapse_family_coequalizer@{o h o} X I p)
    (twcoeq_IsWideCoequalizer@{o o h} (collapse_family X I p)).

Example p459_iso_generic_to@{o h u | o < h, h < u +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) (x : X) :
  continuous_map (to (collapse_iso_generic@{o h u} X I p)) x = x := eq_refl.

Example p459_iso_generic_from@{o h u | o < h, h < u +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) (x : X) :
  continuous_map (from (collapse_iso_generic@{o h u} X I p)) x = x
  := eq_refl.

(* N7 *)
Fail Definition p459_iso_generic_no_u@{o h | o < h +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) :
  Top_collapse X I p ≅[Top@{h o}] twcoeq_obj@{o o h} (collapse_family X I p) :=
  wide_coequalizer_unique _ (collapse_family_coequalizer@{o h o} X I p)
    (twcoeq_IsWideCoequalizer@{o o h} (collapse_family X I p)).

(* CONTROL: X/∅ ≅ X with [u] in the binder. / 控制：X/∅ ≅ X 与 [u] 在结合器中。 *)
Definition p459_empty_iso@{o h u | o < h, h < u +} (X : TopSpace@{o}) :
  Top_collapse_sub X (fun _ => False) ≅[Top@{h o}] X :=
  wide_coequalizer_unique _ (collapse_coequalizer@{o h o} X (fun _ => False))
    (wide_empty_id_IsWideCoequalizer _
       (fun a : collapse_sub_points X (fun _ => False) => projT2 a)).

(* N8 *)
Fail Definition p459_empty_iso_no_u@{o h | o < h +} (X : TopSpace@{o}) :
  Top_collapse_sub X (fun _ => False) ≅[Top@{h o}] X :=
  wide_coequalizer_unique _ (collapse_coequalizer@{o h o} X (fun _ => False))
    (wide_empty_id_IsWideCoequalizer _
       (fun a : collapse_sub_points X (fun _ => False) => projT2 a)).

(* CONTROL: X/∅ and X have the same underlying type at [eq_refl]. / 控制：X/∅ 和 X 在 [eq_refl] 具有相同的基础类型。 *)
Example p459_empty_carrier@{o} (X : TopSpace@{o}) :
  carrier (top_carrier (Top_collapse_sub X (fun _ => False)))
    = carrier (top_carrier X) := eq_refl.

(* N9 *)
Fail Example p459_empty_eq@{o} (X : TopSpace@{o}) :
  Top_collapse_sub X (fun _ => False) = X := eq_refl.

(*
CONTROL: at ∅ every elementary wide coequalizer of the empty family is
   pointless; [collapse_empty_pointless] is a readback of [Empty_Top]'s
   carrier, and a proof closes for every subset of ∅
   ([p459_pointless_any]).

--------
控制：在∅上，每个空族的基本广义共等化器都是无点的；[collapse_empty_pointless] 是 [Empty_Top] 的承载的回读，并且对于 ∅ 的每个子集 ([p459_pointless_any]) 都有证明结束。
*)
Definition p459_empty_coequalizer_pointless@{o h i | o < h, o <= i +}
  (Q : Top@{h o}) (e : Empty_Top@{o} ~{Top@{h o}}~> Q) :
  IsWideCoequalizer@{i h h} (C := Top@{h o})
    (collapse_sub_family Empty_Top@{o} (fun _ => False)) Q e →
  top_carrier Q → False :=
  empty_wide_coequalizer_pointless@{o h i} Q e.

Definition p459_collapse_empty_pointless@{o} :
  top_carrier (Top_collapse_sub Empty_Top@{o} (fun _ => False)) → False :=
  collapse_empty_pointless@{o}.

Definition p459_pointless_any@{o}
  (A : carrier (top_carrier Empty_Top@{o}) → Type@{o}) :
  top_carrier (Top_collapse_sub Empty_Top@{o} A) → False :=
  fun z => match z with end.

(** ** Instance/Top/Quotient/Pairs.v: the category of pairs / ** Instance/Top/Quotient/Pairs.v: 成对的类别 *)

(* CONTROL: the category and the two functors. / 控制：类别和两个函子。 *)
Definition p459_top_pairs@{h o | o < h +} : Category@{h h h} :=
  Top_pairs@{h o}.

Definition p459_point_pair_functor@{h o | o < h +} :
  Top_pointed@{h o} ⟶ Top_pairs@{h o} := PointPair@{h o}.

Definition p459_quotient_functor@{h o | o < h +} :
  Top_pairs@{h o} ⟶ Top_pointed@{h o} := PairQuotient@{h o}.

(*
CONTROL: ⟨Y, *⟩'s subset is the Type-valued predicate y ≈ y0, at
   [eq_refl].

--------
控制：⟨Y, *⟩的子集是类型值谓词 y ≈ y0，位于 [eq_refl]。
*)
Definition p459_point_sub@{o} (Y : PointedTop@{o}) :
  carrier (top_carrier (ptop_space Y)) → Type@{o} :=
  fun y => y ≈ ptop_pt Y.

Example p459_point_pair_sub@{h o | o < h +} (Y : PointedTop@{o}) :
  pair_sub (fobj[PointPair@{h o}] Y) = p459_point_sub Y := eq_refl.

(* N10 *)
Fail Definition p459_point_sub_prop@{o} (Y : PointedTop@{o}) :
  carrier (top_carrier (ptop_space Y)) → Prop :=
  fun y => y ≈ ptop_pt Y.

(* CONTROL: the squash eliminates into a proposition. / 控制：压榨消除成一个命题。 *)
Definition p459_squash@{o} (Y : PointedTop@{o})
  (y : carrier (top_carrier (ptop_space Y)))
  (H : inhabited (y ≈ ptop_pt Y)) : inhabited (y ≈ ptop_pt Y) :=
  match H with inhabits e => inhabits e end.

(* N11 *)
Fail Definition p459_unsquash@{o} (Y : PointedTop@{o})
  (y : carrier (top_carrier (ptop_space Y)))
  (H : inhabited (y ≈ ptop_pt Y)) : y ≈ ptop_pt Y :=
  match H with inhabits e => e end.

(*
CONTROL: the respect field is a choice.  With A saturated inside the
   identification, the four-case relation over [option X] is an
   equivalence with no field; unsaturated and without the field it is not
   transitive.

--------
控制：尊重字段是一个选择。在标识中A是饱和的情况下，[option X]上的四类关系是一个没有字段的等价关系；未饱和且没有该字段时，它不是传递的。
*)
Definition p459_sat@{o} (X : TopSpace@{o}) (A : X → Type@{o}) (x : X) :
  Type@{o} := { a : X & (A a * (a ≈ x))%type }.

Definition p459_sat_respects@{o} (X : TopSpace@{o}) (A : X → Type@{o})
  (x y : X) (e : x ≈ y) (s : p459_sat X A x) : p459_sat X A y :=
  (projT1 s; (fst (projT2 s), transitivity (snd (projT2 s)) e)).

Definition p459_sat_rel@{o} (X : TopSpace@{o}) (A : X → Type@{o})
  (u v : option X) : Type@{o} :=
  match u, v with
  | Some x, Some y => ((x ≈ y) + (p459_sat X A x * p459_sat X A y))%type
  | Some x, None => p459_sat X A x
  | None, Some y => p459_sat X A y
  | None, None => poly_unit@{o}
  end.

Definition p459_sat_rel_Equivalence@{o} (X : TopSpace@{o})
  (A : X → Type@{o}) : Equivalence (p459_sat_rel X A) :=
  ltac:(constructor;
    [ intros [x|]; simpl; [left; reflexivity | exact ttt]
    | intros [x|] [y|] H; simpl in *; try exact H;
      destruct H as [H|[H1 H2]]; [left; now symmetry | right; exact (H2, H1)]
    | intros [x|] [y|] [z|] H1 H2; simpl in *; try exact ttt;
      [ destruct H1 as [H1|[H1 H1']], H2 as [H2|[H2 H2']];
        [ left; now transitivity y
        | right; split;
            [ exact (p459_sat_respects X A _ _ (symmetry H1) H2) | exact H2' ]
        | right; split; [ exact H1 | exact (p459_sat_respects X A _ _ H2 H1') ]
        | right; exact (H1, H2') ]
      | destruct H1 as [H1|[H1 H1']];
        [ exact (p459_sat_respects X A _ _ (symmetry H1) H2) | exact H1 ]
      | right; exact (H1, H2)
      | exact H1
      | destruct H2 as [H2|[H2 H2']];
        [ exact (p459_sat_respects X A _ _ H2 H1) | exact H2' ]
      | exact H2 ] ]).

Definition p459_unsat_rel@{o} (S : SetoidObject@{o o}) (A : S → Type@{o})
  (u v : option S) : Type@{o} :=
  match u, v with
  | Some x, Some y => ((x ≈ y) + (A x * A y))%type
  | Some x, None => A x
  | None, Some y => A y
  | None, None => poly_unit@{o}
  end.

Definition p459_bool_total : SetoidObject := {|
  carrier := bool;
  is_setoid := {| equiv := fun _ _ => poly_unit;
                  setoid_equiv := ltac:(constructor; repeat intro; exact ttt) |}
|}.

Definition p459_unsat_rel_not_transitive :
  (∀ (S : SetoidObject) (A : S → Type), Transitive (p459_unsat_rel S A)) →
  False :=
  fun H => match H p459_bool_total (fun b => b = true) (Some false)
                   (Some true) None (inl ttt) eq_refl in _ = b
                   return if b then False else True with
           | eq_refl => I
           end.

(** ** Instance/Top/Quotient/Pairs.v: the adjunction / ** Instance/Top/Quotient/Pairs.v：伴随 *)

(*
CONTROL: the adjunction at its explicit record instance, its unit and
   counit read back at [eq_refl], and its hom-set isomorphism IS
   [pairs_quotient_iso] at [eq_refl].

--------
控制：在其显式记录实例处的附加，其单位和余单位在 [eq_refl] 处读取回，并且其 Hom 集同构 IS 在 [eq_refl] 处为 [pairs_quotient_iso]。
*)
Definition p459_adjunction@{h o u v | o < h, h < u +} :
  @Adjunction@{h h h h h h h h u h v} Top_pointed@{h o} Top_pairs@{h o}
    PairQuotient@{h o} PointPair@{h o} :=
  pairs_quotient_adjunction@{h o u v}.

Example p459_unit_eval@{h o u v | o < h, h < u +} (X : PairTop@{o})
  (x : carrier (top_carrier (pair_space X))) :
  continuous_map
    (pair_map (@unit _ _ _ _ pairs_quotient_adjunction@{h o u v} X)) x
    = Some x := eq_refl.

Example p459_counit_some@{h o u v | o < h, h < u +} (Y : PointedTop@{o})
  (y : carrier (top_carrier (ptop_space Y))) :
  continuous_map
    (ptop_map (@counit _ _ _ _ pairs_quotient_adjunction@{h o u v} Y))
    (Some y) = y := eq_refl.

Example p459_counit_none@{h o u v | o < h, h < u +} (Y : PointedTop@{o}) :
  continuous_map
    (ptop_map (@counit _ _ _ _ pairs_quotient_adjunction@{h o u v} Y)) None
    = ptop_pt Y := eq_refl.

Example p459_adj_is@{h o u v | o < h, h < u +} (X : PairTop@{o})
  (Y : PointedTop@{o}) :
  @adj _ _ _ _ pairs_quotient_adjunction@{h o u v} X Y
    = pairs_quotient_iso@{h o u} X Y := eq_refl.

(* N12 *)
Fail Example p459_hom_eq@{h o | o < h +} (X : PairTop@{o})
  (Y : PointedTop@{o}) :
  @hom Top_pointed@{h o} (PairQuotient@{h o} X) Y
    = @hom Top_pairs@{h o} X (PointPair@{h o} Y) := eq_refl.

(*
CONTROL: the [Build_Adjunction'] term of the target at the explicit
   record instance.

--------
控制：在显式记录实例中目标的 [Build_Adjunction'] 术语。
*)
Definition p459_adjunction_built@{h o u v | o < h, h < u +} :
  @Adjunction@{h h h h h h h h u h v} Top_pointed@{h o} Top_pairs@{h o}
    PairQuotient@{h o} PointPair@{h o} :=
  @Build_Adjunction' Top_pointed@{h o} Top_pairs@{h o} PairQuotient@{h o}
    PointPair@{h o} pairs_quotient_iso@{h o u}
    ltac:(intros X Y Z f g x; reflexivity)
    ltac:(intros X Y Z f g x; reflexivity).

(* N13 *)
Fail Definition p459_adjunction_built_notation@{h o u v | o < h, h < u +} :
  PairQuotient@{h o} ⊣ PointPair@{h o} :=
  @Build_Adjunction' Top_pointed@{h o} Top_pairs@{h o} PairQuotient@{h o}
    PointPair@{h o} pairs_quotient_iso@{h o u}
    ltac:(intros X Y Z f g x; reflexivity)
    ltac:(intros X Y Z f g x; reflexivity).

(*
CONTROL: the finished adjunction read through the notation, [v] named
   in the binder.

--------
控制：完成的附加通过记录读取，[v] 在活页夹中命名。
*)
Definition p459_adjunction_notation@{h o u v | o < h, h < u +} :
  PairQuotient@{h o} ⊣ PointPair@{h o} :=
  pairs_quotient_adjunction@{h o u v}.

(* N14 *)
Fail Definition p459_adjunction_notation_no_v@{h o u | o < h, h < u +} :
  PairQuotient@{h o} ⊣ PointPair@{h o} :=
  pairs_quotient_adjunction.

(** ** Instance/Top/Quotient/Pairs.v: X/A as the pushout / ** Instance/Top/Quotient/Pairs.v：X/A 作为推挤出 *)

(* CONTROL: X/A is the pushout X ⊔_A ∗, its apex at [eq_refl]. / 控制：X/A 是推出 X ⊔_A ∗，其顶点在 [eq_refl]。 *)
Definition p459_pushout@{h o | o < h +} (X : PairTop@{o}) :
  IsPushout (C := Top@{h o}) (pair_sub_incl X) (top_one (pair_sub_space X)) :=
  pquot_pushout@{h o} X.

Example p459_pushout_apex@{h o | o < h +} (X : PairTop@{o}) :
  pushout_apex (pquot_pushout@{h o} X) = pquot_space X := eq_refl.

(** ** Instance/Top/Quotient/Pairs.v: the colimit form, every A / ** Instance/Top/Quotient/Pairs.v：余极形式，每个 A *)

(*
CONTROL: X/A is the colimit of the point-inclusions of A for every pair,
   with no point of A, at the type of Construction 5's [collapse_colimit]
   written as Instance/Top/Quotient.v writes it.

--------
控制：X/A 是每对 A 的点包含的余极限，A 中没有的点，在构造 5 的 [collapse_colimit] 类型下，按照 Instance/Top/Quotient.v 的写法。
*)
Definition p459_wide_colimit@{o h | o < h +} (X : PairTop@{o}) :
  WideCoequalizer (AWide@{h h h h h} (C := Top@{h o})
                     (collapse_sub_family (pair_space X) (pair_sub X))) :=
  pquot_wide_coequalizer_colimit@{o h} X.

Definition p459_wide_colimit_collapse_type@{o h | o < h +}
  (X : PairTop@{o}) :
  WideCoequalizer (AWide (C := Top@{h o})
                     (collapse_sub_family (pair_space X) (pair_sub X))) :=
  pquot_wide_coequalizer_colimit@{o h} X.

(*
CONTROL: its apex is X/A, its leg out of X the inclusion, its leg out of
   * at the one point the left adjoint's basepoint, and the left adjoint's
   underlying space its apex, all at [eq_refl].

--------
控制：它的顶点是 X/A，它的腿从 X 的包含之外，它的腿从 * 在一点处左伴随的基点，以及左伴随的基础空间它的顶点，都在 [eq_refl]。
*)
Example p459_wide_colimit_apex@{o h | o < h +} (X : PairTop@{o}) :
  colimit_apex (pquot_wide_coequalizer_colimit@{o h} X) = pquot_space X
  := eq_refl.

Example p459_wide_colimit_in@{o h | o < h +} (X : PairTop@{o}) :
  colimit_inj (colimit_is_acolimit (pquot_wide_coequalizer_colimit@{o h} X))
    ParY = pquot_in X := eq_refl.

Example p459_wide_colimit_base@{o h | o < h +} (X : PairTop@{o}) :
  continuous_map
    (colimit_inj (colimit_is_acolimit (pquot_wide_coequalizer_colimit@{o h} X))
       ParX) ttt
    = ptop_pt (fobj[PairQuotient@{h o}] X) := eq_refl.

Example p459_wide_colimit_quotient@{o h | o < h +} (X : PairTop@{o}) :
  ptop_space (fobj[PairQuotient@{h o}] X)
    = colimit_apex (pquot_wide_coequalizer_colimit@{o h} X) := eq_refl.

(*
CONTROL: at the empty subset the colimit is X ⊔ *; every colimit of the
   family has a point, at ⟨∅, ∅⟩ the new point [None].

--------
控制：在空子集上，余极限是 X ⊔ *；该族的每个余极限都有一个点，在 ⟨∅, ∅⟩ 上新增的点是 [None]。
*)
Definition p459_wide_colimit_empty@{o h | o < h +} (X : TopSpace@{o}) :
  colimit_apex (pquot_wide_coequalizer_colimit@{o h} (empty_pair X))
    ≅[Top@{h o}] Sum_Top X Point_Top@{o} :=
  pquot_wide_coequalizer_colimit_empty@{o h} X.

Definition p459_colimit_point@{o h | o < h +} (X : TopSpace@{o})
  (A : X → Type@{o})
  (L : WideCoequalizer (AWide@{h h h h h} (C := Top@{h o})
                          (collapse_sub_family X A))) :
  top_carrier (colimit_apex L) :=
  collapse_colimit_point@{o h} X A L.

Definition p459_colimit_pointed_at_empty@{o h | o < h +} :
  top_carrier (colimit_apex
    (pquot_wide_coequalizer_colimit@{o h} (empty_pair Empty_Top@{o}))) :=
  None.

(** ** Instance/Top/Quotient/Pairs.v: the elementary record, given a point / ** Instance/Top/Quotient/Pairs.v：给定一个点的基本记录 *)

(*
CONTROL: given a point of A, X/A is an elementary wide coequalizer of
   the point-inclusions, isomorphic to Construction 5's in [Top] and in
   [Top_pointed].

--------
控制：给定一个点 A，X/A 是点包含的基本宽共等化器，同构于 [Top] 和 [Top_pointed] 中构造 5 的结果。
*)
Definition p459_pquot_coequalizer@{o h i | o < h, o <= i +}
  (X : PairTop@{o}) (a0 : collapse_sub_points (pair_space X) (pair_sub X)) :
  IsWideCoequalizer@{i h h} (C := Top@{h o})
    (collapse_sub_family (pair_space X) (pair_sub X))
    (pquot_space X) (pquot_in X) :=
  pquot_coequalizer@{o h i} X a0.

Definition p459_pquot_collapse_iso@{o h u | o < h, h < u +}
  (X : PairTop@{o}) (a0 : collapse_sub_points (pair_space X) (pair_sub X)) :
  Top_collapse_sub (pair_space X) (pair_sub X) ≅[Top@{h o}] pquot_space X :=
  wide_coequalizer_unique _
    (collapse_coequalizer@{o h o} (pair_space X) (pair_sub X))
    (pquot_coequalizer@{o h o} X a0).

Example p459_pquot_collapse_iso_to@{o h u | o < h, h < u +}
  (X : PairTop@{o}) (a0 : collapse_sub_points (pair_space X) (pair_sub X))
  (x : carrier (top_carrier (pair_space X))) :
  continuous_map (to (pquot_collapse_iso@{o h u} X a0)) x = Some x
  := eq_refl.

Example p459_pquot_collapse_iso_from_none@{o h u | o < h, h < u +}
  (X : PairTop@{o}) (a0 : collapse_sub_points (pair_space X) (pair_sub X)) :
  continuous_map (from (pquot_collapse_iso@{o h u} X a0)) None = projT1 a0
  := eq_refl.

(* N15 *)
Fail Definition p459_pquot_collapse_iso_no_u@{o h | o < h +}
  (X : PairTop@{o}) (a0 : collapse_sub_points (pair_space X) (pair_sub X)) :
  Top_collapse_sub (pair_space X) (pair_sub X) ≅[Top@{h o}] pquot_space X :=
  wide_coequalizer_unique _
    (collapse_coequalizer@{o h o} (pair_space X) (pair_sub X))
    (pquot_coequalizer@{o h o} X a0).

Definition p459_pquot_collapse_iso_pointed@{o h u | o < h, h < u +}
  (X : PairTop@{o}) (a0 : collapse_sub_points (pair_space X) (pair_sub X)) :
  collapse_pointed X a0 ≅[Top_pointed@{h o}] fobj[PairQuotient@{h o}] X :=
  pquot_collapse_iso_pointed@{o h u} X a0.

Example p459_collapse_pointed_pt@{o} (X : PairTop@{o})
  (a0 : collapse_sub_points (pair_space X) (pair_sub X)) :
  ptop_pt (collapse_pointed X a0) = projT1 a0 := eq_refl.

(** ** Instance/Top/Quotient/Pairs.v: the empty subset / ** Instance/Top/Quotient/Pairs.v：空子集 *)

(*
CONTROL: X/∅ is X₊ in [Top], [Some x] ↦ [inl x] and [None] ↦ [inr ttt]
   at [eq_refl].

--------
控制：X/∅ 在 [Top] 中为 X₊，[Some x] ↦ [inl x] 且 [None] ↦ [inr ttt]，发生在 [eq_refl]。
*)
Definition p459_empty_sum_iso@{h o | o < h +} (X : TopSpace@{o}) :
  pquot_space (empty_pair X) ≅[Top@{h o}] Sum_Top X Point_Top@{o} :=
  pquot_empty_sum_iso@{h o} X.

Example p459_empty_sum_some@{h o | o < h +} (X : TopSpace@{o})
  (x : carrier (top_carrier X)) :
  continuous_map (to (pquot_empty_sum_iso@{h o} X)) (Some x)
    = Datatypes.inl x := eq_refl.

Example p459_empty_sum_none@{h o | o < h +} (X : TopSpace@{o}) :
  continuous_map (to (pquot_empty_sum_iso@{h o} X)) None
    = Datatypes.inr ttt := eq_refl.

(* N16 *)
Fail Example p459_empty_sum_eq@{o} (X : TopSpace@{o}) :
  pquot_space (empty_pair X) = Sum_Top X Point_Top@{o} := eq_refl.

(*
CONTROL: the elementary record at ⟨∅, ∅⟩ refuted for pointed spaces, at
   this file's construction and for every construction; an object
   assignment suffices, a functor's included; and no colimit's apex
   carries the record there.

--------
控制：在⟨∅, ∅⟩处的基本记录已被针对尖点空间驳斥，在该文件的构造中以及对于每一个构造；一个对象分配就足够，一个函子包含其中；且没有余极的顶点携带该记录。
*)
Definition p459_pquot_empty_not_coequalizer@{o h i | o < h, o <= i +} :
  IsWideCoequalizer@{i h h} (C := Top@{h o})
    (collapse_sub_family (pair_space (empty_pair Empty_Top@{o}))
       (pair_sub (empty_pair Empty_Top@{o})))
    (pquot_space (empty_pair Empty_Top@{o}))
    (pquot_in (empty_pair Empty_Top@{o})) → False :=
  pquot_empty_not_coequalizer@{o h i}.

Definition p459_pquot_needs_point@{o h i | o < h, o <= i +} :
  (∀ X : PairTop@{o},
     IsWideCoequalizer@{i h h} (C := Top@{h o})
       (collapse_sub_family (pair_space X) (pair_sub X))
       (pquot_space X) (pquot_in X)) → False :=
  pquot_coequalizer_needs_point@{o h i}.

Definition p459_no_pointed_coequalizer@{o h i | o < h, o <= i +}
  (Q : PointedTop@{o}) (e : Empty_Top@{o} ~{Top@{h o}}~> ptop_space Q) :
  IsWideCoequalizer@{i h h} (C := Top@{h o})
    (collapse_sub_family Empty_Top@{o} (fun _ => False)) (ptop_space Q) e →
  False :=
  no_pointed_coequalizer_at_empty@{o h i} Q e.

Definition p459_no_assignment@{o h i | o < h, o <= i +}
  (L : PairTop@{o} → PointedTop@{o}) :
  (∀ X : PairTop@{o}, ∃ e : pair_space X ~{Top@{h o}}~> ptop_space (L X),
     IsWideCoequalizer@{i h h} (C := Top@{h o})
       (collapse_sub_family (pair_space X) (pair_sub X)) (ptop_space (L X)) e)
  → False :=
  no_pointed_elementary_coequalizers@{o h i} L.

Definition p459_no_functor@{o h i | o < h, o <= i +}
  (L : Top_pairs@{h o} ⟶ Top_pointed@{h o}) :
  (∀ X : PairTop@{o}, ∃ e : pair_space X ~{Top@{h o}}~> ptop_space (L X),
     IsWideCoequalizer@{i h h} (C := Top@{h o})
       (collapse_sub_family (pair_space X) (pair_sub X)) (ptop_space (L X)) e)
  → False :=
  no_pointed_elementary_coequalizers@{o h i} (fun X => fobj[L] X).

Definition p459_empty_colimit_not_elementary@{o h i | o < h, o <= i +}
  (L : WideCoequalizer (AWide@{h h h h h} (C := Top@{h o})
                          (collapse_sub_family Empty_Top@{o}
                             (fun _ => False))))
  (e : Empty_Top@{o} ~{Top@{h o}}~> colimit_apex L) :
  IsWideCoequalizer@{i h h} (C := Top@{h o})
    (collapse_sub_family Empty_Top@{o} (fun _ => False)) (colimit_apex L) e →
  False :=
  empty_colimit_not_elementary@{o h i} L e.

(** ** Guard: every constant of the two targets / ** 守卫：两个目标的每一个常数 *)

(* Instance/Top/Quotient.v / 实例/顶部/商.v *)
Check Top_HasWideCoequalizers_small.
Check Top_collapse.
Check Top_collapse_equiv.
Check Top_collapse_sub.
Check Top_wide_coequalizer_obj.
Check WSetsCoeq.
Check collapse_carrier.
Check collapse_coequalizer.
Check collapse_colimit.
Check collapse_desc.
Check collapse_desc_map.
Check collapse_desc_map_points.
Check collapse_empty_iso.
Check collapse_empty_pointless.
Check collapse_family.
Check collapse_family_coequalizer.
Check collapse_family_colimit.
Check collapse_image.
Check collapse_image_respects.
Check collapse_iso_generic.
Check collapse_iso_generic_from.
Check collapse_iso_generic_to.
Check collapse_med.
Check collapse_med_proper.
Check collapse_proj.
Check collapse_proj_epic.
Check collapse_q.
Check collapse_rel.
Check collapse_rel_Equivalence.
Check collapse_setoid.
Check collapse_sub_family.
Check collapse_sub_incl.
Check collapse_sub_points.
Check collapse_sub_proj.
Check collapse_wcofork.
Check empty_wide_coequalizer_pointless.
Check twcoeq_IsWideCoequalizer.
Check twcoeq_cofork.
Check twcoeq_desc.
Check twcoeq_med.
Check twcoeq_obj.
Check twcoeq_proj.
Check wcoeq_rel.
Check wcoeq_rel_Equivalence.
Check wcoeq_rel_ind.
Check wcoeq_rel_of_cofork.
Check wcoeq_rel_rec.
Check wcoeq_rel_rect.
Check wcoeq_rel_sind.
Check wcq_base.
Check wcq_glue.
Check wcq_sym.
Check wcq_trans.
Check wsets_coeq_proj.

(* Instance/Top/Quotient/Pairs.v / 实例/顶部/商/对.v *)
Check Build_PairMap.
Check Build_PairTop.
Check PairMap.
Check PairMap_Setoid.
Check PairMap_equiv_Equivalence.
Check PairQuotient.
Check Pairs.PairQuotient_obligation_1.
Check Pairs.PairQuotient_obligation_2.
Check Pairs.PairQuotient_obligation_3.
Check PairTop.
Check PointPair.
Check Pairs.PointPair_obligation_1.
Check Pairs.PointPair_obligation_2.
Check Pairs.PointPair_obligation_3.
Check PointPair_sub.
Check Top_pairs.
Check Pairs.Top_pairs_obligation_1.
Check Pairs.Top_pairs_obligation_2.
Check Pairs.Top_pairs_obligation_3.
Check Pairs.Top_pairs_obligation_4.
Check collapse_colimit_point.
Check collapse_pointed.
Check empty_colimit_not_elementary.
Check empty_pair.
Check no_pointed_coequalizer_at_empty.
Check no_pointed_elementary_coequalizers.
Check pair_carries.
Check pair_compose.
Check pair_compose_respects.
Check pair_id.
Check pair_map.
Check pair_space.
Check pair_sub.
Check pair_sub_equiv_Equivalence.
Check pair_sub_incl.
Check pair_sub_incl_map.
Check pair_sub_proper.
Check pair_sub_setoid.
Check pair_sub_space.
Check pairs_quotient_adj_is.
Check pairs_quotient_adjunction.
Check pairs_quotient_counit_none.
Check pairs_quotient_counit_some.
Check pairs_quotient_iso.
Check Pairs.pairs_quotient_iso_obligation_1.
Check Pairs.pairs_quotient_iso_obligation_2.
Check Pairs.pairs_quotient_iso_obligation_3.
Check Pairs.pairs_quotient_iso_obligation_4.
Check pairs_quotient_unit_eval.
Check point_pair.
Check point_pair_map.
Check pquot_base.
Check pquot_basepoint.
Check pquot_carrier.
Check pquot_coequalizer.
Check pquot_coequalizer_needs_point.
Check pquot_collapse_iso.
Check pquot_collapse_iso_from_none.
Check pquot_collapse_iso_from_some.
Check pquot_collapse_iso_pointed.
Check pquot_collapse_iso_to.
Check pquot_empty_new_point.
Check pquot_empty_not_coequalizer.
Check pquot_empty_sum_from.
Check pquot_empty_sum_iso.
Check pquot_empty_sum_iso_none.
Check pquot_empty_sum_iso_some.
Check pquot_empty_sum_to.
Check pquot_fmap.
Check pquot_fmap_cont.
Check pquot_fmap_map.
Check pquot_from.
Check pquot_from_eval_none.
Check pquot_from_eval_some.
Check pquot_from_map.
Check pquot_in.
Check pquot_po_map.
Check pquot_po_med.
Check pquot_pointed.
Check pquot_pushout.
Check pquot_pushout_apex.
Check pquot_rel.
Check pquot_rel_Equivalence.
Check pquot_setoid.
Check pquot_some.
Check pquot_space.
Check pquot_space_carrier.
Check pquot_space_open.
Check pquot_to.
Check pquot_to_eval.
Check pquot_wide_cocone.
Check pquot_wide_coequalizer_colimit.
Check pquot_wide_coequalizer_colimit_apex.
Check pquot_wide_coequalizer_colimit_base.
Check pquot_wide_coequalizer_colimit_empty.
Check pquot_wide_coequalizer_colimit_in.
Check pquot_wide_coequalizer_colimit_quotient.
Check pquot_wide_legs.
Check pquot_wide_legs_coherence.
Check pquot_wide_ump.
