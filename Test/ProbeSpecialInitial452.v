(**
* Probe for the special initial-object theorem (issue #452)

    Pins the measured boundaries of Adjunction/SAFT/InitialObject.v (Mac
    Lane §V.8 Theorem 1, book p. 128; Riehl Lemma 4.7.11, printed p. 177)
    and of the three files #452 added beside it: Adjunction/SAFT/
    InitialObject/Examples.v, Instance/Sets/Cogenerator.v and Instance/
    Sets/SpecialInitial.v.  Every negative but two restates a refusal
    measured on #452 by its scouts, builders or review; N7, a peel of N6,
    and N14, the theorem beside N13's product, are this file's own.  The
    positive controls restate the files' claims independently.

    THE IMPORT LIST, measured by comparing [Require] lines.  First
    Adjunction/SAFT/InitialObject.v's twenty-one lines verbatim and in
    order; then the lines each other target adds, file by file, the target
    modules aside: Adjunction/SAFT/InitialObject/Examples.v five, Instance/
    Sets/Cogenerator.v two and Instance/Sets/SpecialInitial.v seven; then
    the four target modules in dependency order.  No supplier module is
    added.  Adjunction/SAFT.v is imported after Theory/Subobject.v, so the
    short names [sub_dom] and [sub_mono] are [SubobjectIndex]'s fields
    ([Locate] lists Adjunction/SAFT.v's first), and a subobject's are
    written [Subobject.sub_dom].  Instance/Discrete.v is loaded by the list
    but not imported ([Locate] gives the shorter name
    [Discrete.DiscreteCat_Functor]), so N5 and its control write
    [Category.Instance.Discrete.DiscreteCat_Functor] in full: it is the
    term Adjunction/SAFT.v's [cogen_power_limit] is built from.  A shorter
    import list is what makes a probe pass for no reason.

    DISCIPLINE.  The instrument was checked both ways: the refutation of an
    absent name is refused for that reason, and wrapping a control in a
    refutation, in a copy of this WHOLE file, stops the build with the
    report that the guarded command had been accepted (done five times,
    at [p452_obj], [p452_binder_ok], [p452_sets_iem_direct],
    [p452_large_cog] and [p452_large_prod_abstract]).  Every negative
    other than that instrument is a [Definition] or an [Example], never a
    [Check], so that an open evar or a missing instance cannot satisfy it.
    Each negative was stripped of its refutation keyword in a copy of this
    WHOLE file, one at a time, compiled, and its error read; the kind
    recorded is the kind of that error, and each has positive controls
    beside it that between them name the same library constants.  Every
    UNIVERSE negative is a top-level definition whose universes are
    declared in its own binder or left to inference, never those of a
    [Section], so that the stripped error names the bound where Rocq can.
    Quotations are Rocq 9.1.1's under this file's import list; Rocq prints
    the "cannot unify" parenthetical with the short names in scope, and a
    universe the stripped copy names after itself and a serial number is
    written <1>, <2>, ..., numbered afresh in each quotation in order of
    first appearance.  The file also compiles on Coq 8.19.2 and 8.20.1,
    against the nix store's builds of this library for those versions with
    the four target files compiled on each, and the stripped copies were
    compiled there as well.  Every one is refused on both at the same
    construct, and at the same character range except N13 and N14, whose
    range there also covers the family's explicit universe instance.
    Under 8.20.1 every error is the Rocq 9.1.1 one up to the serial
    numbers (compared by a script over the copies).  Under 8.19.2 nine of
    the universe refusals (N2, N3, N8, N9, N11, N13-N16) print as type
    mismatches with no universe-inconsistency clause, N4 names its two
    universes by serial numbers, and N5's chain reads "so < <5> <= <4> <=
    <1>" in place of "so < h <= <4> <= <1>", <5> being a universe the
    Rocq 9.1.1 error does not print.

    KINDS.  Nineteen refutations, counted as the lines that open with the
    refutation keyword: NAME-ABSENCE (the instrument), CONVERSION (N1,
    N17, N18) and UNIVERSE (N2-N16).

    LABELS.  Three pins also carry the names under which #452's review
    asked for them, and the target headers cite each by that label, its
    N-number and its constants: P_H_le_so is N5, P_type_truth is N11 and
    N12, P_large_cog is N13 and N14.  The labels appear in this header and
    in the section titles below; they are not constants.

    ** The theorem's object

    N1 (CONVERSION).  [special_initial_object]'s object IS
    [Subobject.sub_dom w] by [eq_refl] ([p452_obj]), and its arrow to [c]
    is the pullback leg after the lower-bound factor ([p452_zero]), both
    restated from Adjunction/SAFT/InitialObject.v's readbacks;
    [p452_is_initial] states the conclusion in the type.  The readback
    discriminates: the product itself is refused,
      The term "eq_refl" has type "0 = 0" while it is expected to have
      type "0 = cogen_prod comp G" (cannot unify "0" and "cogen_prod comp
      G").
    [0] being Structure/Initial.v's notation for [initial_obj].

    ** The two donor collapses

    N2 (UNIVERSE).  Adjunction/SAFT.v's unannotated [cogen_prod] takes the
    family's index universe AT [Complete]'s shape universe, and a family
    indexed strictly below it is refused:
      The term "G" has type "Cogenerator@{c o h} C" while it is expected
      to have type "Cogenerator@{so o h} C" (universe inconsistency:
      Cannot enforce c = so because c < so).
    The controls: [cogen_prod] at [c = so] ([p452_prod_at_so]), and
    [cogen_power], whose shape is a Σ over the index, at the same [c < so]
    ([p452_power_low_index]).

    N3 (UNIVERSE).  The unannotated [cogen_power] takes [Complete]'s
    limit-datum universe, its first slot, AT the shape universe, and a
    datum above it is refused:
      The term "comp" has type "Complete@{r so h o}" while it is expected
      to have type "Complete@{so so h o}" (universe inconsistency: Cannot
      enforce r = so because so < r).
    The controls: [cogen_power] at [r = so] ([p452_power_at_so]), and
    [cogen_prod] at the same [so < r] ([p452_prod_high_datum]).  N2 and N3
    are why Adjunction/SAFT/InitialObject.v's statements take
    [Complete@{so so h o}] and [Cogenerator@{so o h}].

    ** Small hom-sets

    N4, N5 (UNIVERSE; N5 is P_H_le_so).  The bound [h <= so], the book's
    "small hom-sets", was first measured on #452 at [cogen_power] and at
    [special_initial_object] under the binder [Complete@{so so h o}] with
    [so < h], and quoted as "Universe inconsistency. Cannot enforce h <= so
    because so < h."  That text is the binder's own.  N4, whose body is its
    argument [x] and names neither [cogen_power] nor the theorem, is
    refused with exactly it, over the whole command rather than at an
    argument:
      Universe inconsistency. Cannot enforce h <= so because so < h.
    [Complete@{r so h o}] declares [h <= r] (Structure/Complete.v) and the
    binder puts [r] at [so], so a refutation in that shape holds whatever
    its body and guards nothing about [cogen_power]; what N4 does pin is
    that declared [h <= r], read at [r = so], the shape N3's collapse gives
    the statements.  N5 is the body's own bound, with [r] kept apart.  The
    instrument [p452_binder_ok], whose body is trivial, shows the binder
    formable at [so < h <= r], and [cogen_prod] is accepted there
    ([p452_prod_small_shape]); [cogen_power_limit]'s body, written out
    because [cogen_power] itself would meet N3 first, with its shape
    argument left to unification where [Print cogen_power_limit] shows
    [Discrete.DiscreteCat (cogen_power_index G c)], is refused at the
    functor:
      The term "Discrete.DiscreteCat_Functor (cogen_power_fam G c)" has
      type "@Functor@{<1> <2> <3> o h h} (Discrete.DiscreteCat@{<1> <2>
      <3>} (@cogen_power_index@{<4> so o h} C G c)) C" while it is
      expected to have type "@Functor@{so h h o h h} ?D C" (universe
      inconsistency: Cannot enforce <1> = so because so < h <= <4> <=
      <1>).
    The chain is the bound: [cogen_power_index G c], a Σ over the family's
    index and the arrows [c ~> cog_obj G j], lies at or above the hom
    universe [h], and the discrete shape on it must sit at the shape
    universe [so].  The control is the same body at [h <= so <= r]
    ([p452_power_limit_ok]).

    ** Small objects

    N6, N7 (UNIVERSE).  [special_initial_object_small]'s route,
    [complete_intersection_IsIntersection] over the family of ALL
    subobjects of the product, at [so < o]:
      Found type "SubObj (cogen_prod comp G)" where "?J" was expected
      (unable to find a well-typed instantiation for "?J": cannot ensure
      that "Type@{max(o,h)}" is a subtype of "Type@{<1>}").
    the refusal Adjunction/SAFT/InitialObject.v's header records for the
    small route, a universe comparison reported while instantiating an
    evar.  N7 peels it, the index given explicitly:
      The term "SubObj (cogen_prod comp G)" has type "Type@{max(o,h)}"
      while it is expected to have type "Type@{<1>}" (universe
      inconsistency: Cannot enforce o <= <1> because <1> <= <2> < o).
    The controls: both terms at [o <= so] ([p452_small_route_ok],
    [p452_small_index_ok]), and the library constant there
    ([p452_small_const]).

    ** Freyd's construction

    N8 (UNIVERSE).  [special_vs_freyd]'s statement at [h < so]:
      The term "comp" has type "Complete@{so so h o}" while it is expected
      to have type "Complete@{<1> <1> <1> <2>}" (universe inconsistency:
      Cannot enforce h = so because h < so).
    Theory/WeaklyInitial.v's [initial_from_weakly_initial_complete] takes
    one universe for the shape objects, the limit datum and the homs, so
    the in-tree comparison is stated at [so = h] only; the control is the
    same statement and body there ([p452_freyd_at_h]).  Any two initial
    objects are isomorphic, so N8 bounds the route through that constant,
    not the comparison as such.

    N9 (UNIVERSE).  Freyd's construction fed [wif_of_cogenerator] with its
    index [w] strictly below the homs:
      The term "wif_of_cogenerator comp G W" has type
      "WeaklyInitialFamily@{w o h} C" while it is expected to have type
      "WeaklyInitialFamily@{h o h} C" (universe inconsistency: Cannot
      enforce w = h because w < h).
    The controls: [wif_of_cogenerator] alone at [w < h] ([p452_wif_low]),
    and the same body at [w = h] ([p452_freyd_wif_at_h], which is
    [freyd_of_cogenerator]'s body).

    ** [Sets] and [Sets^op]

    N10 (UNIVERSE).  [special_initial_object_small] at [Sets], with
    [Sets_Complete] ascribed its universes, as N13 does, and
    [Sets_Cogenerator_IEM E], the refusal Instance/Sets/SpecialInitial.v's
    header records:
      The term "Sets_Complete : Complete" has type "Complete@{o o o so}"
      while it is expected to have type "Complete@{o o o <1>}" (universe
      inconsistency: Cannot enforce <1> = so because <1> <= <2> < so).
    [Complete]'s last slot is the object universe: the small form bounds
    it by its shape universe, which at [Sets_Complete] is [o], and the
    chain puts it strictly below [so], where the objects of [Sets@{o so}]
    live.  The shape first measured on #452 left [Sets_Complete]'s
    universes to inference; a whole-file copy with that form in place of
    N10 is refused at the same argument, with every universe a serial
    number ("Cannot enforce <1> = <2> because <1> <= <3> < <2>").  The
    controls: [sets_special_initial_IEM E] at the same universes
    ([p452_sets_iem]); its body, [special_initial_object] over the least
    subobject with the ascribed [Sets_Complete] and [Sets_Cogenerator_IEM
    E] named directly ([p452_sets_iem_direct]); and
    [special_initial_object_small] itself where objects fit the shapes
    ([p452_small_const]).

    N11, N12 (UNIVERSE; P_type_truth).  The [Type]-valued route to a
    cogenerator of [Sets], which Instance/Sets/Cogenerator.v records as
    refused, quoting these two.  The object of truth values is [Type@{l}]
    under [iffT] ([p452_iff_setoid], its equivalence proved in full, so
    that each negative differs from its control in a universe only).  N11,
    the truth setoid at the carrier level itself:
      The term "{| carrier := Type; is_setoid := p452_iff_setoid |}" has
      type "SetoidObject" while it is expected to have type "obj[Sets]"
      (universe inconsistency: Cannot enforce <1> = o because o < <1>).
    Its control is the same one level down, [l < o] ([p452_truth_low]).
    N12, the test map at a point [y0] of an arbitrary object into that
    lower truth setoid, written [@equiv _ (is_setoid Y) y0 b] so that no
    class search is involved:
      The term "y0 ≈ b" has type "Type" while it is expected to have type
      "carrier {| carrier := Type; is_setoid := p452_iff_setoid |}"
      (universe inconsistency: Cannot enforce o <= l because l < o).
    Its control is the same map for [Y : SetoidObject@{l l}]
    ([p452_char_low]), and [Sets_Cogenerator_untruncate U] is accepted at
    the same universes ([p452_cog_untruncate]).  N11 is not the form first
    measured on #452, whose scratch probe left the equivalence proof as a
    hole; the kind and the bound are the same.
    Both refuse one construction; neither shows that no small cogenerator
    of [Sets] exists.

    N13, N14 (UNIVERSE; P_large_cog).  [Sets] has a [Cogenerator] with no
    hypothesis: Instance/Sets/Cogenerator.v's [Sets_Cogenerator_large],
    every object, each tested by its identity, accepted at the universes
    that file's header states ([p452_large_cog]; [About] reads
    [Cogenerator@{c so o} Sets@{o so}] under [o < c, o < so], stdlib
    bounds aside).  Its index, the type of all objects, sits strictly
    above [Sets_Complete]'s shape universe [o], where [cogen_prod] needs
    it (N2's collapse).  N13, its product at [Sets_Complete]:
      The term "Sets_Cogenerator_large" has type "Cogenerator@{c so o}
      Sets@{o so}" while it is expected to have type "Cogenerator@{o so o}
      Sets@{o so}" (universe inconsistency: Cannot enforce c = o because
      o < c).
    N14, [special_initial_object] at [Sets_Complete] over the least
    subobject [sets_special_initial_untruncate] uses, is refused with the
    same text.  Both give the family its universe instance and ascribe
    [Sets_Complete] its universes, so that the error names the bound; a
    first draft of this file left them to inference and was refused with
    the same kind, every universe then a serial number.  The controls:
    [cogen_prod] and [special_initial_object_least] take the family over a
    completeness datum [Complete@{c c o so}] whose shape universe is its
    index universe ([p452_large_prod_abstract],
    [p452_large_sio_abstract]), a hypothetical datum taken as a variable,
    [Sets_Complete] being [Complete@{o o o so}], its shape universe [o]
    and not [c]; and at [Sets_Complete] the conditional cogenerator is
    accepted in both places ([p452_small_prod_sets],
    [p452_small_sio_sets]).  What [Sets] lacks unconditionally in tree is
    a SMALL cogenerator, indexed at the shape universe of [Sets_Complete],
    and not a cogenerator.

    N15, N16 (UNIVERSE).  [Sets^op] through well-poweredness.  The only
    co-well-poweredness of [Sets] in tree, Instance/Sets/WellPowered.v's
    [Sets_CoWellPoweredAt_up], has its index at its own [t], one universe
    above the homs ([p452_sets_cowp_up], accepted per object).  N15, at
    the corollary [special_initial_object_wellpowered]:
      The term "Sets_CoWellPoweredAt_up X" has type "WellPoweredAt@{<1> <2>
      <2> o <1>} X" while it is expected to have type "WellPoweredAt@{<3>
      so <4> o <5>} X" (universe inconsistency: Cannot enforce <3> = <5>
      because <3> <= <6> < <5>).
    [WellPowered] pins the index at or below the homs, which lie strictly
    below [t].  N16, at the per-object corollary
    [special_initial_object_wellpowered_at] and the one object
    [cogen_prod setsop_comp setsop_cog], which bounds the index by
    [Complete]'s shape universe instead (at [setsop_comp] that is the hom
    universe):
      The term "Sets_CoWellPoweredAt_up (cogen_prod setsop_comp
      setsop_cog)" has type "WellPoweredAt@{<1> <2> <2> <3> <1>} (…)"
      while it is expected to have type "WellPoweredAt@{<4> <5> <6> <7>
      <8>} (…)" (universe inconsistency: Cannot enforce <4> = <8> because
      <4> <= <7> < <8>).
    with the product's universe instances elided as (…), and the numbering
    taken over the text as quoted.  The controls:
    both corollaries with the datum left free ([p452_setsop_wp_free],
    [p452_setsop_wp_at_free]).  So the hand-built least subobject
    [setsop_L] is what makes [Sets^op] unconditional, as Instance/Sets/
    SpecialInitial.v says.

    N17, N18 (CONVERSION).  Instance/Sets/SpecialInitial.v's readbacks by
    [eq_refl] discriminate: at [Sets^op] the object IS [Sets_Terminal]'s
    singleton ([p452_setsop_obj]), and at [Sets] under [IEM] it IS
    [Sets_Initial]'s empty setoid ([p452_sets_iem_obj]).  N17, the
    [Sets^op] object against the empty setoid, the error printed with
    explicit arguments throughout:
      (cannot unify "@initial_obj (Opposite Sets) setsop_special_initial"
      and "@initial_obj Sets Sets_Initial")
    N18, the [IEM] object against the singleton:
      The term "eq_refl" has type "0 = 0" while it is expected to have
      type "0 = 1" (cannot unify "0" and "1").
    Both objects are the ones handed to the theorem (the circularity
    caveat of that file's header); N17 and N18 show that the readbacks say
    which.

    CONTROLS WITHOUT A NEGATIVE.  [Indiscrete_types_special_initial]'s
    object IS [unit] by [eq_refl] ([p452_indiscrete_obj]);
    [Subsets_special_initial_is_empty] and [Sets_terminal_not_cogenerates]
    at their stated types; the book's form at [Sets] over the #451
    intersection ([p452_sets_book]).  The guard block at the end names all
    seventy constants of the four target files (twenty-nine, twelve, seven
    and twenty-two, counted as the lines of each that open with
    [Definition], [Lemma] or [Example]), so that a rename breaks this
    file.

--------
* 探测特殊初始对象定理（问题 #452）

固定了 Adjunction/SAFT/InitialObject.v 的测量边界（Mac Lane §V.8 定理 1，书籍第 128 页；Riehl 引理 4.7.11，印刷第 177 页）以及其旁边添加的三个文件 #452：Adjunction/SAFT/InitialObject/Examples.v、Instance/Sets/Cogenerator.v 和 Instance/Sets/SpecialInitial.v。除了两个例外，每一个否定都重新陈述了其侦查员、建造者或审查在 #452 上进行测量的拒绝；N7 是 N6 的剥离，N14 是紧挨 N13 的乘积定理，是该文件自己的。正面控制则独立地重申了这些文件的声明。

导入列表，通过比较 [Require] 行来测量。首先，Adjunction/SAFT/InitialObject.v 的二十一行逐字且按顺序列出；然后列出其他目标每个文件添加的行，目标模块除外：Adjunction/SAFT/InitialObject/Examples.v 五行，Instance/Sets/Cogenerator.v 两行，以及 Instance/Sets/SpecialInitial.v 七行；然后按依赖顺序列出四个目标模块。没有添加供应模块。Adjunction/SAFT.v 在 Theory/Subobject.v 之后被导入，因此短名称 [sub_dom] 和 [sub_mono] 是 [SubobjectIndex] 的字段（[Locate] 列出 Adjunction/SAFT.v 的前面内容），子对象的字段写作 [Subobject.sub_dom]。Instance/Discrete.v 被列表加载但未导入（[Locate] 提供短名称 [Discrete.DiscreteCat_Functor]），因此 N5 及其控制会完整写作 [Category.Instance.Discrete.DiscreteCat_Functor]：它是 Adjunction/SAFT.v 的 [cogen_power_limit] 构建的项。较短的导入列表就是让探针无缘无故通过的原因。

纪律。该工具以两种方式进行了检查：由于该原因，拒绝对缺席的名称进行驳斥，并且在对这整个文件的副本中将控制包裹在驳斥中，会停止构建，并报告受保护的命令已被接受（在 [p452_obj]、[p452_binder_ok]、[p452_sets_iem_direct]、[p452_large_cog] 和 [p452_large_prod_abstract] 中各执行五次）。除了该工具之外，每个否定都是 [Definition] 或 [Example]，从不为 [Check]，因此开放的 evar 或缺失的实例无法满足它。每个否定在这整个文件的副本中都被逐一去掉了其驳斥关键字，进行编译，并读取其错误；记录的类型即为该错误的类型，并且每个否定旁边都有正面控制，它们之间命名了相同的库常量。
每个 UNIVERSE 负例都是一个顶层定义，其宇宙在其自身的绑定器中声明或留给推断，从不使用 [Section] 的宇宙，因此剥离后的错误会在 Rocq 可以的绑定处命名。引文是 Rocq 9.1.1 在本文件导入列表下的；Rocq 打印带有作用域内短名称的“无法统一”的括号，并且剥离的宇宙副本以自身和一个序列号命名，写作 <1>、<2>……，在每个引文中按首次出现的顺序重新编号。该文件也能在 Coq 8.19.2 和 8.20.1 上编译，对应 nix 存储中该库针对这些版本的构建，每个版本编译了四个目标文件，剥离的副本也在那儿编译。
除 N13 和 N14 外，每个人在相同的构造和相同的字符范围内都会被拒绝，它们的范围还覆盖了该家族的显式宇宙实例。根据 8.20.1，每个错误都是 Rocq 9.1.1 错误，直到序列号为止（通过脚本对副本进行比较）。根据 8.19.2，九个宇宙拒绝（N2、N3、N8、N9、N11、N13-N16）显示为类型不匹配，没有宇宙不一致条款，N4 通过序列号命名其两个宇宙，而 N5 的链显示为“so <<5> <= <4> <= <1>” 代替 “so < h <= <4> <= <1>”，其中 <5> 是 Rocq 9.1.1 错误不会打印的宇宙。

种类。十九种反驳，以以反驳关键词开头的行计算：NAME-ABSENCE（工具）、CONVERSION（N1、N17、N18）和UNIVERSE（N2-N16）。

标签。三个引脚还带有#452的审查中要求的名称，目标头文件通过该标签、它的N编号及其常量来引用每一个：P_H_le_so 是 N5，P_type_truth 是 N11 和 N12，P_large_cog 是 N13 和 N14。标签出现在此头文件和下面的章节标题中；它们不是常量。

** 定理的对象

N1（转换）。 [special_initial_object] 的对象是由 [eq_refl]（[p452_obj]）通过 [Subobject.sub_dom w] 构成的，其指向 [c] 的箭头是在下界因子（[p452_zero]）之后的回拉段，这些都从 Adjunction/SAFT/InitialObject.v 的回读中重新表述；[p452_is_initial] 在类型中陈述了结论。回读区分：乘积本身被拒绝，术语“eq_refl”的类型是“0 = 0”，而预期类型是“0 = cogen_prod comp G”（无法统一“0”和“cogen_prod comp G”）。[0] 是 Structure/Initial.v 中 [initial_obj] 的记号。

** 两个供体倒塌

N2（宇宙）。Adjunction/SAFT.v 中未标注的 [cogen_prod] 将家族的指数宇宙取为 [Complete] 的形状宇宙，而严格低于它的家族会被拒绝：
  术语“G”的类型是“Cogenerator@{c o h} C”，但期望它的类型是“Cogenerator@{so o h} C”（宇宙不一致：无法强制 c = so，因为 c < so）。
控件：[cogen_prod] 在 [c = so]（[p452_prod_at_so]）处，以及 [cogen_power]，其形状为指数的 Σ，在同一 [c < so]（[p452_power_low_index]）处。

N3（宇宙）。未注释的 [cogen_power] 采用 [Complete] 的极限-数据宇宙，它的第一个槽，在形状宇宙处，并且位于其上的数据被拒绝：
  术语“comp”的类型是“Complete@{r so h o}”，而期望类型是“Complete@{so so h o}”（宇宙不一致：无法强制 r = so，因为 so < r）。
控件：[cogen_power] 在 [r = so]（[p452_power_at_so]），以及 [cogen_prod] 在相同的 [so < r]（[p452_prod_high_datum]）。N2 和 N3 是为什么 Adjunction/SAFT/InitialObject.v 的语句采用 [Complete@{so so h o}] 和 [Cogenerator@{so o h}] 的原因。

** 小同集

N4, N5（UNIVERSE；N5 是 P_H_le_so）。绑定的 [h <= so]，该书的“small hom-sets”，最早在 #452 于 [cogen_power] 测量，并且在 [special_initial_object] 在绑定器 [Complete@{so so h o}] 下使用 [so < h] 测量，并引用为“Universe inconsistency。Cannot enforce h <= so because so < h。” 该文本属于绑定器自身。N4，其主体是其参数 [x]，并且既不命名 [cogen_power] 也不命名定理，被完全以这个拒绝，而不是在某个参数上：
      Universe inconsistency。Cannot enforce h <= so because so < h。[Complete@{r so h o}] 声明 [h <= r]（Structure/Complete.v），绑定器将 [r] 放在 [so]，因此这种形状的反驳成立，无论其主体是什么，并且对 [cogen_power] 没有任何约束；N4 固定的是声明的 [h <= r]，在 [r = so] 读取，N3 崩溃的形状给出了这些陈述。
N5 是身体自身的绑定，[r] 保持分开。仪器 [p452_binder_ok]，其本体微不足道，显示在 [so < h <= r] 可以形成绑定器，并且 [cogen_prod] 在那里被接受（[p452_prod_small_shape]）；[cogen_power_limit] 的本体被写出，因为 [cogen_power] 本身会首先遇到 N3，其形状参数留给统一处理，在 [Print cogen_power_limit] 显示 [Discrete.DiscreteCat (cogen_power_index G c)]，被在函子处拒绝：
  术语 "Discrete.DiscreteCat_Functor (cogen_power_fam G c)" 的类型是 "@Functor@{<1> <2> <3> o h h} (Discrete.DiscreteCat@{<1> <2> <3>} (@cogen_power_index@{<4> so o h} C G c)) C"，而它预计的类型是 "@Functor@{so h h o h h} ?D C"（宇宙不一致：无法强制 <1> = so，因为 so < h <= <4> <= <1>）。
链条是约束：[cogen_power_index G c]，是家庭索引及箭头 [c ~> cog_obj G j] 的 Σ，总是处于或高于本体宇宙 [h]，并且其上的离散形状必须位于形状宇宙 [so]。控制是位于 [h <= so <= r]（[p452_power_limit_ok]）的同一主体。

** 小物件

N6, N7（宇宙）。[special_initial_object_small]的路径，
[complete_intersection_IsIntersection]在产品的所有子对象族上，在[so < o]：
  找到类型“SubObj (cogen_prod comp G)”，但预期为“?J”
  （无法找到“?J”的类型正确实例化：无法确保 “Type@{max(o,h)}” 是 “Type@{<1>}” 的子类型）。
拒绝Adjunction/SAFT/InitialObject.v的头记录用于
小路径，在实例化evar时报告了宇宙比较。N7将其展开，显式给出索引：
  术语“SubObj (cogen_prod comp G)” 类型为 “Type@{max(o,h)}”，
  但预期类型为“Type@{<1>}”（宇宙不一致：无法强制 o <= <1> 因为 <1> <= <2> < o）。
控制：[o <= so]（[p452_small_route_ok], [p452_small_index_ok]）处的两个术语，以及
那里的库常量（[p452_small_const]）。

** 弗雷德的构造

N8（宇宙）。[special_vs_freyd]在[h < so]的声明：
      术语“comp”的类型为“Complete@{so so h o}”，而期望的类型为“Complete@{<1> <1> <1> <2>}”（宇宙不一致：
      无法强制 h = so 因为 h < so）。
    Theory/WeaklyInitial.v 的 [initial_from_weakly_initial_complete] 为形状对象、极限数据和同态取一个宇宙，因此树内比较仅在 [so = h] 中陈述；控制是在那里相同的声明和主体（[p452_freyd_at_h]）。任何两个初始对象是同构的，因此 N8 限制了通过该常量的路径，而不是比较本身。

N9（宇宙）。Freyd 的构造将 [wif_of_cogenerator] 传递给其 index [w] 严格地低于同态：
  术语“wif_of_cogenerator comp G W”的类型为
  “WeaklyInitialFamily@{w o h} C”，而预期类型为
  “WeaklyInitialFamily@{h o h} C”（宇宙不一致：无法
  强制 w = h 因为 w < h）。
控件：单独在 [w < h]（[p452_wif_low]）处的 [wif_of_cogenerator]，
以及在 [w = h]（[p452_freyd_wif_at_h]，[freyd_of_cogenerator] 的主体）处的相同主体。

** [Sets] 和 [Sets^op]

N10（宇宙）。[special_initial_object_small] 位于 [Sets]，同时 [Sets_Complete] 被分配了它的宇宙，就像 N13 一样，以及 [Sets_Cogenerator_IEM E]，拒绝 Instance/Sets/SpecialInitial.v 的头记录：
      术语 “Sets_Complete : Complete” 的类型为 “Complete@{o o o so}”，而预期类型为 “Complete@{o o o <1>}”（宇宙不一致：无法强制 <1> = so，因为 <1> <= <2> < so）。[Complete] 的最后一个槽是对象宇宙：它由其形状宇宙限制，在 [Sets_Complete] 处为 [o]，并且该链严格低于 [so]，[Sets@{o so}] 的对象位于那里。
首先在 #452 左侧 [Sets_Complete] 的宇宙中测量了形状以推理；在相同的参数下，整个文件的副本中用该形状替换 N10 是被拒绝的，每个宇宙都是一个序列号（“无法强制 <1> = <2> 因为 <1> <= <3> < <2>”）。控制项：在相同的宇宙中（[p452_sets_iem]）的 [sets_special_initial_IEM E]；其主体 [special_initial_object] 在具有指定 [Sets_Complete] 和直接命名的 [Sets_Cogenerator_IEM E] 的最小子对象上（[p452_sets_iem_direct]）；以及对象符合形状的 [special_initial_object_small] 本身（[p452_small_const]）。

N11, N12（宇宙；P_type_truth）。通向 [Sets] 的共生成器的 [Type] 值路由，Instance/Sets/Cogenerator.v 将其记录为拒绝，引用这两个。真值对象是在 [iffT] 下的 [Type@{l}]（[p452_iff_setoid]，其等价已完全证明，因此每个负值仅在一个宇宙中与其控制值不同）。N11，即承载层级自身的真集代数：
      术语“{| carrier := Type; is_setoid := p452_iff_setoid |}”的类型为“SetoidObject”，但预期类型为“obj[Sets]”（宇宙不一致：无法强制 <1> = o，因为 o < <1>）。其控制在下一层相同，为 [l < o]（[p452_truth_low]）。
N12，在任意对象的某点 [y0] 上的测试映射到那个较低的真值集合中，记作 [@equiv _ (is_setoid Y) y0 b]，因此不涉及类搜索：
      术语 “y0 ≈ b” 的类型是 “Type”，而其预期类型是 “carrier {| carrier := Type; is_setoid := p452_iff_setoid |}”
      （宇宙不一致：无法强制 o <= l 因为 l < o）。它的控制与 [Y : SetoidObject@{l l}]（[p452_char_low]） 的映射相同，并且 [Sets_Cogenerator_untruncate U] 被接受于相同的宇宙（[p452_cog_untruncate]）。N11 不是在 #452 上首次测量的形式，其临时探针留下了等价性证明的空白；类型和界限相同。两者都拒绝某个构造；也都没有显示 [Sets] 的小型余生生成元不存在。

N13, N14（宇宙；P_large_cog）。[Sets] 有一个 [Cogenerator]，没有假设：Instance/Sets/Cogenerator.v 的 [Sets_Cogenerator_large]，每个对象，每个通过其身份测试，在该文件头声明的宇宙中被接受（[p452_large_cog]；[About] 在 [o < c, o < so] 下读取 [Cogenerator@{c so o} Sets@{o so}]，忽略标准库边界）。其索引，即所有对象的类型，严格高于 [Sets_Complete] 的形状宇宙 [o]，在 [cogen_prod] 需要它的地方（N2 的崩塌）。N13，其在 [Sets_Complete] 的积：
  术语 "Sets_Cogenerator_large" 的类型是 "Cogenerator@{c so o} Sets@{o so}"，而期望的类型是 "Cogenerator@{o so o} Sets@{o so}"（宇宙不一致：无法强制 c = o，因为 o < c）。N14，[special_initial_object] 在 [Sets_Complete] 上对于使用的最小子对象 [sets_special_initial_untruncate] 被拒绝，错误文本相同。
两者都为族赋予它的宇宙实例，并将 [Sets_Complete] 归属于它的宇宙，以便错误命名该绑定；该文件的初稿将它们交给推断，但被以同样的方式拒绝，此时每个宇宙都有一个序列号。控制如下：[cogen_prod] 和 [special_initial_object_least] 将族作用于一个完整性数据 [Complete@{c c o so}]，其形状宇宙是它的索引宇宙（[p452_large_prod_abstract], [p452_large_sio_abstract]），该假设数据被作为变量采用，[Sets_Complete] 为 [Complete@{o o o so}]，其形状宇宙为 [o] 而非 [c]；在 [Sets_Complete] 时，条件共生成器在两个位置都被接受（[p452_small_prod_sets], [p452_small_sio_sets]）。[Sets] 在树中无条件缺少的是一个 SMALL 共生成器，它在 [Sets_Complete] 的形状宇宙中被索引，而不是一个共生成器。

N15, N16（宇宙）。通过良有势性得到 [Sets^op]。[Sets] 在树中的唯一共良有势性，在 Instance/Sets/WellPowered.v 的 [Sets_CoWellPoweredAt_up] 中，其指标位于其自身的 [t]，比同态层高一个宇宙（[p452_sets_cowp_up]，按对象接受）。N15，在推论 [special_initial_object_wellpowered] 中：
    术语 “Sets_CoWellPoweredAt_up X” 的类型为 “WellPoweredAt@{<1> <2> <2> o <1>} X”，而期望类型为 “WellPoweredAt@{<3> so <4> o <5>} X”（宇宙不一致：无法强制 <3> = <5>，因为 <3> <= <6> < <5>）。[WellPowered] 将指标固定在同态以下，而同态严格低于 [t]。
N16，在每个对象的推论中
    [special_initial_object_wellpowered_at] 和单个对象
    [cogen_prod setsop_comp setsop_cog]，它通过 [Complete] 的类型宇宙限制索引（在 [setsop_comp] 那里是同构宇宙）：
      术语 "Sets_CoWellPoweredAt_up (cogen_prod setsop_comp setsop_cog)" 的类型是 "WellPoweredAt@{<1> <2> <2> <3> <1>} (…)"
      而期望类型是 "WellPoweredAt@{<4> <5> <6> <7> <8>} (…)"（宇宙不一致：无法强制 <4> = <8> 因为 <4> <= <7> < <8>）。使用省略的积的宇宙实例表示为 (…) ，编号按文本中引用的方式。控制项：
    两个推论的数据保持自由（[p452_setsop_wp_free]，[p452_setsop_wp_at_free]）。因此，手工构建的最小子对象 [setsop_L] 使得 [Sets^op] 无条件成立，如 Instance/Sets/SpecialInitial.v 所述。

N17, N18（转换）。通过 [eq_refl] 辨别 Instance/Sets/SpecialInitial.v 的读回：在 [Sets^op]，该对象是 [Sets_Terminal] 的单例（[p452_setsop_obj]）；在 [Sets] 下，在 [IEM] 下，它是 [Sets_Initial] 的空集合族（[p452_sets_iem_obj]）。N17，在空集合族上的 [Sets^op] 对象，使用整个显式参数打印的错误：
  （无法统一 "@initial_obj (Opposite Sets) setsop_special_initial" 和 "@initial_obj Sets Sets_Initial"）
N18，在单例上的 [IEM] 对象：
  术语 "eq_refl" 的类型为 "0 = 0"，而预期类型为 "0 = 1" （无法统一 "0" 和 "1"）。
两个对象都是传递给定理的对象（那个文件头部的循环性警告）；N17 和 N18 显示了读回所指出的内容。

没有否定的控制。 [Indiscrete_types_special_initial] 的对象由 [eq_refl] ([p452_indiscrete_obj]) 的 [unit]； [Subsets_special_initial_is_empty] 和 [Sets_terminal_not_cogenerates] 按其声明的类型；书籍在 #451 交叉点的 [Sets] 处的形式 ([p452_sets_book])。 末尾的保护块列出四个目标文件的所有七十个常量（分别是二十九、十二、七和二十二，按每个文件以 [Definition]、[Lemma] 或 [Example] 开头的行数计算），因此重命名会破坏此文件。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.WeaklyInitial.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.SAFT.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Powerset.WellPowered.
Require Import Category.Theory.Concrete.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Construction.Product.Limit.
Require Import Category.Structure.Generator.Dual.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Instance.Sets.Generator.
Require Import Category.Instance.Sets.SubobjectLattice.
Require Import Category.Instance.Sets.WellPowered.
Require Import Category.Adjunction.SAFT.InitialObject.
Require Import Category.Adjunction.SAFT.InitialObject.Examples.
Require Import Category.Instance.Sets.Cogenerator.
Require Import Category.Instance.Sets.SpecialInitial.

Generalizable All Variables.

(** ** Instrument: the refutation keyword is live / ** 工具：反驳关键词是实时的 *)

Fail Check probe452_absent_name.

(** ** N1 (CONVERSION): the object IS the intersection, and not the product / ** N1（转换）：对象是交集，而不是乘积 *)

(* CONTROL: the object readback, restated. / 控制：对象回读，重述。 *)
Example p452_obj@{o h so q +| h <= so, o <= q, h <= q +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : IsIntersection@{o h q} (fun m : SubObj (cogen_prod comp G) => m) w) :
  @initial_obj C (special_initial_object comp G w Hw) = Subobject.sub_dom w :=
  eq_refl.

(* CONTROL: the zero-arrow readback, restated. / 控制：零箭头回读，重述。 *)
Example p452_zero@{o h so q +| h <= so, o <= q, h <= q +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : IsIntersection@{o h q} (fun m : SubObj (cogen_prod comp G) => m) w)
  (c : C) :
  @zero C (special_initial_object comp G w Hw) c
    = cogen_pullback_to comp G c
        ∘ `1 (inter_le _ _ Hw (cogen_pullback_sub comp G c)) :=
  eq_refl.

(* CONTROL: the conclusion in the type. / 控制：类型中的结论。 *)
Definition p452_is_initial@{o h so q +| h <= so, o <= q, h <= q +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : IsIntersection@{o h q} (fun m : SubObj (cogen_prod comp G) => m) w) :
  IsInitialObj (Subobject.sub_dom w) :=
  special_initial_IsInitialObj comp G w Hw.

Fail Example p452_n1_obj_is_product@{o h so q +| h <= so, o <= q, h <= q +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : IsIntersection@{o h q} (fun m : SubObj (cogen_prod comp G) => m) w) :
  @initial_obj C (special_initial_object comp G w Hw) = cogen_prod comp G :=
  eq_refl.

(** ** N2, N3 (UNIVERSE): the two donor collapses / ** N2，N3（宇宙）：两个供体坍塌 *)

(* CONTROL: [cogen_prod] at the collapsed index universe, [c = so]. / 控制：在塌缩索引宇宙中的 [cogen_prod]，[c = so]。 *)
Definition p452_prod_at_so@{o h so +| h <= so +} {C : Category@{o h h}}
  (comp : @Complete@{so so h o} C) (G : Cogenerator@{so o h} C) : C :=
  cogen_prod comp G.

(*
CONTROL: [cogen_power], whose shape is a Σ over the index, takes an index
   universe below the shape universe.

--------
控制：[cogen_power]，其形状是索引上的 Σ，采用一个低于形状宇宙的索引宇宙。
*)
Definition p452_power_low_index@{o h so c +| h <= so, c < so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (x : C) : C :=
  cogen_power comp G x.

Fail Definition p452_n2_prod_low_index@{o h so c +| h <= so, c < so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) : C :=
  cogen_prod comp G.

(* CONTROL: [cogen_power] at the collapsed limit-datum universe, [r = so]. / 控制：[cogen_power] 在坍塌的极限基准宇宙，[r = so]。 *)
Definition p452_power_at_so@{o h so +| h <= so +} {C : Category@{o h h}}
  (comp : @Complete@{so so h o} C) (G : Cogenerator@{so o h} C) (x : C) : C :=
  cogen_power comp G x.

(*
CONTROL: [cogen_prod] takes a limit-datum universe above the shape
   universe.

--------
控制：[cogen_prod] 在形状宇宙之上获取一个极限数据宇宙。
*)
Definition p452_prod_high_datum@{o h r so +| h <= so, so < r +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C)
  (G : Cogenerator@{so o h} C) : C :=
  cogen_prod comp G.

Fail Definition p452_n3_power_high_datum@{o h r so +| h <= so, so < r +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C)
  (G : Cogenerator@{so o h} C) (x : C) : C :=
  cogen_power comp G x.

(** ** N4, N5 (UNIVERSE; N5 is P_H_le_so): small hom-sets, [h <= so] / ** N4, N5（宇宙；N5 是 P_H_le_so）：小同类集，[h <= so] *)

(*
INSTRUMENT: with the limit-datum universe [r] kept apart, the binder is
   formable at [so < h], so a refusal under it is about the body.

--------
仪器：在限制基准宇宙 [r] 中保持分离时，绑定器在 [so < h] 可成型，因此根据它的拒绝与主体有关。
*)
Definition p452_binder_ok@{o h r so +| so < h, h <= r +} {C : Category@{o h h}}
  (comp : @Complete@{r so h o} C) (G : Cogenerator@{so o h} C) (x : C) : C :=
  x.

(* With [r = so] the binder alone is refused, whatever the body. / With [r = so] the binder alone is refused, whatever the body. / 使用 [r = so] 时，无论主体如何，单独的绑定器都会被拒绝。 *)
Fail Definition p452_n4_binder_collapsed@{o h so +| so < h +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (x : C) : C :=
  x.

(* CONTROL: [cogen_prod] at [so < h <= r]. / 控制：[cogen_prod] 于 [so < h <= r]。 *)
Definition p452_prod_small_shape@{o h r so +| so < h, h <= r +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C)
  (G : Cogenerator@{so o h} C) : C :=
  cogen_prod comp G.

(* CONTROL: [cogen_power_limit]'s body at [h <= so <= r]. / 控制：[cogen_power_limit] 的身体位于 [h <= so <= r]。 *)
Definition p452_power_limit_ok@{o h r so +| h <= so, so <= r +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C)
  (G : Cogenerator@{so o h} C) (c : C) :=
  comp _ (Category.Instance.Discrete.DiscreteCat_Functor (cogen_power_fam G c)).

Fail Definition p452_n5_power_limit_small_shape@{o h r so +| so < h, h <= r +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C)
  (G : Cogenerator@{so o h} C) (c : C) :=
  comp _ (Category.Instance.Discrete.DiscreteCat_Functor (cogen_power_fam G c)).

(** ** N6, N7 (UNIVERSE): the small-objects route at [so < o] / ** N6, N7（宇宙）：[so < o]的小物体路线 *)

(*
CONTROL: [special_initial_object_small]'s body, objects at or below the
   shape universe.

--------
控制：[special_initial_object_small] 的身体，以及位于或低于形状宇宙的物体。
*)
Definition p452_small_route_ok@{o h so +| h <= so, o <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) : @Initial C :=
  special_initial_object comp G _
    (complete_intersection_IsIntersection comp
       (fun m : SubObj (cogen_prod comp G) => m)).

(* CONTROL: the library constant at the same universes. / 控制：同一宇宙中的库常数。 *)
Definition p452_small_const@{o h so +| h <= so, o <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) : @Initial C :=
  special_initial_object_small comp G.

Fail Definition p452_n6_small_route@{o h so +| h <= so, so < o +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) : @Initial C :=
  special_initial_object comp G _
    (complete_intersection_IsIntersection comp
       (fun m : SubObj (cogen_prod comp G) => m)).

(* CONTROL: N7's term, the family's index explicit, at [o <= so]. / 控制：N7 的任期，家庭索引明确，在 [o <= so]。 *)
Definition p452_small_index_ok@{o h so +| h <= so, o <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) :=
  @complete_intersection_IsIntersection C comp (cogen_prod comp G)
    (SubObj (cogen_prod comp G)) (fun m : SubObj (cogen_prod comp G) => m).

Fail Definition p452_n7_small_index@{o h so +| h <= so, so < o +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) :=
  @complete_intersection_IsIntersection C comp (cogen_prod comp G)
    (SubObj (cogen_prod comp G)) (fun m : SubObj (cogen_prod comp G) => m).

(** ** N8, N9 (UNIVERSE): the comparison with Freyd's construction / ** N8, N9（宇宙）：与弗雷德的构造比较 *)

(* CONTROL: [special_vs_freyd]'s statement and body at [so = h]. / 控制：[special_vs_freyd] 的陈述和尸体位于 [so = h]。 *)
Definition p452_freyd_at_h@{o h +} {C : Category@{o h h}}
  (comp : @Complete@{h h h o} C) (G : Cogenerator@{h o h} C)
  (w : SubObj (cogen_prod comp G))
  (Hw : ∀ v : SubObj (cogen_prod comp G), sub_le w v) :
  @initial_obj C (special_initial_object_least comp G w Hw)
  ≅ @initial_obj C
      (initial_from_weakly_initial_complete comp (Complete_HasEqualizers comp)
         (wif_of_weakly_initial (special_weakly_initial comp G w Hw))) :=
  initial_unique _ _.

Fail Definition p452_n8_freyd_above@{o h so +| h < so +} {C : Category@{o h h}}
  (comp : @Complete@{so so h o} C) (G : Cogenerator@{so o h} C)
  (w : SubObj (cogen_prod comp G))
  (Hw : ∀ v : SubObj (cogen_prod comp G), sub_le w v) :
  @initial_obj C (special_initial_object_least comp G w Hw)
  ≅ @initial_obj C
      (initial_from_weakly_initial_complete comp (Complete_HasEqualizers comp)
         (wif_of_weakly_initial (special_weakly_initial comp G w Hw))) :=
  initial_unique _ _.

(*
CONTROL: the weakly initial family of subobjects is formed with its index
   strictly below the homs.

--------
控制：弱初始子对象族是在其指标严格低于同态时形成的。
*)
Definition p452_wif_low@{o h w s t d +| w < h, h < t, h < d, o <= s, h <= s +}
  {C : Category@{o h h}} (comp : @Complete@{h h h o} C)
  (G : Cogenerator@{h o h} C)
  (W : WellPoweredAt@{w o s h t} (cogen_prod@{h d h o h} comp G)) :
  WeaklyInitialFamily C :=
  wif_of_cogenerator comp G W.

(*
CONTROL: Freyd's construction takes it with the index AT the homs, which
   is [freyd_of_cogenerator]'s body.

--------
控制：Freyd 的构造将其取在 homs 的指数上，这就是 [freyd_of_cogenerator] 的主体。
*)
Definition p452_freyd_wif_at_h@{o h s t d +| h < t, h < d, o <= s, h <= s +}
  {C : Category@{o h h}} (comp : @Complete@{h h h o} C)
  (G : Cogenerator@{h o h} C)
  (W : WellPoweredAt@{h o s h t} (cogen_prod@{h d h o h} comp G)) :
  @Initial C :=
  initial_from_weakly_initial_complete comp (Complete_HasEqualizers comp)
    (wif_of_cogenerator comp G W).

Fail Definition p452_n9_freyd_wif_low@{o h w s t d +|
    w < h, h < t, h < d, o <= s, h <= s +}
  {C : Category@{o h h}} (comp : @Complete@{h h h o} C)
  (G : Cogenerator@{h o h} C)
  (W : WellPoweredAt@{w o s h t} (cogen_prod@{h d h o h} comp G)) :
  @Initial C :=
  initial_from_weakly_initial_complete comp (Complete_HasEqualizers comp)
    (wif_of_cogenerator comp G W).

(** ** N10 (UNIVERSE): the small-objects form at [Sets] / ** N10（宇宙）：小物体在 [Sets] 形成 *)

(* CONTROL: the least-subobject form at the same universes. / 控制：在相同的宇宙中最小子对象形式。 *)
Definition p452_sets_iem@{o so +| o < so +} (E : IEM@{o}) :
  @Initial Sets@{o so} :=
  sets_special_initial_IEM E.

(*
CONTROL: its body, with [Sets_Complete], ascribed as in N10, and
   [Sets_Cogenerator_IEM E] named directly.

--------
控制：其主体，使用 [Sets_Complete]，归因于 N10，并且 [Sets_Cogenerator_IEM E] 直接命名。
*)
Definition p452_sets_iem_direct@{o so +| o < so +} (E : IEM@{o}) :
  @Initial Sets@{o so} :=
  special_initial_object (Sets_Complete : @Complete@{o o o so} Sets@{o so})
    (Sets_Cogenerator_IEM E)
    (sub_bot (Sets_zero_monic _))
    (intersection_all_of_least _ (sub_bot_least (Sets_zero_monic _))).

Fail Definition p452_n10_small_at_sets@{o so +| o < so +} (E : IEM@{o}) :
  @Initial Sets@{o so} :=
  special_initial_object_small
    (Sets_Complete : @Complete@{o o o so} Sets@{o so})
    (Sets_Cogenerator_IEM E).

(** ** N11, N12 (UNIVERSE; P_type_truth): the [Type]-valued truth setoid / ** N11, N12（宇宙；P_type_truth）：[Type] 值的真值集合 *)

(*
[Type@{l}] under [iffT]: the classical object of truth values, with the
   library's [Type]-valued equivalence.

--------
[Type@{l}] 在 [iffT] 下：经典的真值对象，具有库的 [Type] 值等价。
*)
Definition p452_iff_setoid@{l m p +| l < m, l <= p +} :
  Setoid@{m p} Type@{l}.
Proof.
  refine (@Build_Setoid Type@{l} (fun P Q : Type@{l} => iffT P Q) _).
  constructor.
  - intro P; split; intro x; exact x.
  - intros P Q [a b]; split; assumption.
  - intros P Q R [a b] [c d]; split; intro x; auto.
Defined.

(* CONTROL: one level down, it IS an object of [Sets@{o so}]. / 控制：下降一级，它确实是 [Sets@{o so}] 的一个对象。 *)
Definition p452_truth_low@{l o so +| l < o, o < so +} : obj[Sets@{o so}] :=
  @Build_SetoidObject Type@{l} p452_iff_setoid.

Fail Definition p452_n11_truth_at@{o so +| o < so +} : obj[Sets@{o so}] :=
  @Build_SetoidObject Type@{o} p452_iff_setoid.

(* CONTROL: the test map at a point [y0], for a setoid one level down. / 控制：在点 [y0] 的测试地图，对于下一层的集合体。 *)
Definition p452_char_low@{l o so +| l < o, o < so +}
  (Y : SetoidObject@{l l}) (y0 : carrier Y) :
  carrier Y → carrier (@Build_SetoidObject Type@{l} p452_iff_setoid) :=
  fun b => @equiv _ (is_setoid Y) y0 b.

Fail Definition p452_n12_char_at@{l o so +| l < o, o < so +}
  (Y : SetoidObject@{o o}) (y0 : carrier Y) :
  carrier Y → carrier (@Build_SetoidObject Type@{l} p452_iff_setoid) :=
  fun b => @equiv _ (is_setoid Y) y0 b.

(* CONTROL: the conditional cogenerator at the same universes. / 控制：在相同宇宙中的条件协同发电机。 *)
Definition p452_cog_untruncate@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) : Cogenerator Sets@{o so} :=
  Sets_Cogenerator_untruncate U.

(** ** N13, N14 (UNIVERSE; P_large_cog): a large cogenerator of [Sets] / ** N13, N14（宇宙；P_large_cog）：[Sets] 的大型联合发电机 *)

(*
CONTROL: Instance/Sets/Cogenerator.v's [Sets_Cogenerator_large], every
   object tested by its identity, IS a [Cogenerator] of [Sets] with no
   hypothesis, at the universes that file's header states; its index is
   the type of all objects.

--------
控制：Instance/Sets/Cogenerator.v 的 [Sets_Cogenerator_large]，每个对象通过其身份进行测试，是没有假设的 [Sets] 的 [Cogenerator]，在该文件头声明的宇宙中；其索引是所有对象的类型。
*)
Definition p452_large_cog@{c o so +| o < so, o < c +} :
  Cogenerator@{c so o} Sets@{o so} :=
  Sets_Cogenerator_large@{c o so}.

(*
CONTROL: [cogen_prod] takes it over a completeness datum whose shape
   universe is the family's index universe.  The datum is hypothetical, a
   variable: [Sets_Complete] is [Complete@{o o o so}], its shape universe
   [o] and not the [c] above it.

--------
控制：[cogen_prod] 接管了一个完整性数据，该数据的形状宇宙是该家族的索引宇宙。该数据是假设的，一个变量：[Sets_Complete] 是 [Complete@{o o o so}]，其形状宇宙是 [o]，而不是其上方的 [c]。
*)
Definition p452_large_prod_abstract@{c o so +| o < so, o < c +}
  (comp : @Complete@{c c o so} Sets@{o so}) : obj[Sets@{o so}] :=
  cogen_prod comp Sets_Cogenerator_large@{c o so}.

(*
CONTROL: and so does the theorem, over any least subobject, the datum
   hypothetical as above.

--------
控制：定理也是如此，对于任何最小子对象，上述假设的数据。
*)
Definition p452_large_sio_abstract@{c o so +| o < so, o < c +}
  (comp : @Complete@{c c o so} Sets@{o so})
  (w : SubObj (cogen_prod comp Sets_Cogenerator_large@{c o so}))
  (Hw : ∀ v : SubObj (cogen_prod comp Sets_Cogenerator_large@{c o so}),
          sub_le w v) :
  @Initial Sets@{o so} :=
  special_initial_object_least comp Sets_Cogenerator_large@{c o so} w Hw.

(* CONTROL: a small cogenerator's product at [Sets_Complete]. / 控制：[Sets_Complete] 的一个小型联合发电机产品。 *)
Definition p452_small_prod_sets@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) : obj[Sets@{o so}] :=
  cogen_prod (Sets_Complete : @Complete@{o o o so} Sets@{o so})
    (Sets_Cogenerator_untruncate U).

Fail Definition p452_n13_large_prod_sets@{c o so +| o < so, o < c +} :
  obj[Sets@{o so}] :=
  cogen_prod (Sets_Complete : @Complete@{o o o so} Sets@{o so})
    Sets_Cogenerator_large@{c o so}.

(*
CONTROL: [sets_special_initial_untruncate]'s body, the small cogenerator
   at [Sets_Complete].

--------
控制：[sets_special_initial_untruncate] 的主体，位于 [Sets_Complete] 的小型共发生器。
*)
Definition p452_small_sio_sets@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) : @Initial Sets@{o so} :=
  special_initial_object (Sets_Complete : @Complete@{o o o so} Sets@{o so})
    (Sets_Cogenerator_untruncate U)
    (sub_bot (Sets_zero_monic _))
    (intersection_all_of_least _ (sub_bot_least (Sets_zero_monic _))).

Fail Definition p452_n14_large_sio_sets@{c o so +| o < so, o < c +} :
  @Initial Sets@{o so} :=
  special_initial_object (Sets_Complete : @Complete@{o o o so} Sets@{o so})
    Sets_Cogenerator_large@{c o so}
    (sub_bot (Sets_zero_monic _))
    (intersection_all_of_least _ (sub_bot_least (Sets_zero_monic _))).

(** ** N15, N16 (UNIVERSE): [Sets^op] through well-poweredness / ** N15, N16（宇宙）：[Sets^op] 通过强大的能力 *)

(* CONTROL: the corollary at [Sets^op] with the datum left free. / 控制：在 [Sets^op] 的推论，基准保持自由。 *)
Definition p452_setsop_wp_free@{o so +| o < so +}
  (WP : WellPowered (Sets@{o so}^op)) : @Initial (Sets@{o so}^op) :=
  special_initial_object_wellpowered WP setsop_comp setsop_cog.

(* CONTROL: the co-well-powered datum one universe up, per object. / 控制：每个对象，每一宇宙向上共用电源的数据。 *)
Definition p452_sets_cowp_up@{o so +| o < so +} (X : SetoidObject@{o o}) :=
  Sets_CoWellPoweredAt_up@{o so so} X.

Fail Definition p452_n15_setsop_wp_up@{o so +| o < so +} :
  @Initial (Sets@{o so}^op) :=
  special_initial_object_wellpowered (C := Sets@{o so}^op)
    (fun X => Sets_CoWellPoweredAt_up X) setsop_comp setsop_cog.

(*
CONTROL: the per-object corollary at [Sets^op] with the datum left
   free.

--------
控制：在 [Sets^op] 上的每个对象的对应项，数据项保持自由。
*)
Definition p452_setsop_wp_at_free@{o so +| o < so +}
  (W : WellPoweredAt (C := Sets@{o so}^op)
         (cogen_prod setsop_comp setsop_cog)) :
  @Initial (Sets@{o so}^op) :=
  special_initial_object_wellpowered_at setsop_comp setsop_cog W.

Fail Definition p452_n16_setsop_wp_at_up@{o so +| o < so +} :
  @Initial (Sets@{o so}^op) :=
  special_initial_object_wellpowered_at setsop_comp setsop_cog
    (Sets_CoWellPoweredAt_up (cogen_prod setsop_comp setsop_cog)).

(** ** N17, N18 (CONVERSION): the objects at [Sets^op] and at [Sets] / ** N17, N18（转换）：位于 [Sets^op] 和 [Sets] 的对象 *)

(* CONTROL: at [Sets^op] the object IS the singleton. / 控制：在 [Sets^op] 中，该对象是单例。 *)
Example p452_setsop_obj@{o so +| o < so +} :
  @initial_obj (Sets@{o so}^op) setsop_special_initial
    = @terminal_obj Sets@{o so} Sets_Terminal := eq_refl.

Fail Example p452_n17_setsop_obj_empty@{o so +| o < so +} :
  @initial_obj (Sets@{o so}^op) setsop_special_initial
    = @initial_obj Sets@{o so} Sets_Initial := eq_refl.

(* CONTROL: at [Sets] under [IEM] the object IS the empty setoid. / 控制：在 [Sets] 下的 [IEM] 中，该对象是空集。 *)
Example p452_sets_iem_obj@{o so +| o < so +} (E : IEM@{o}) :
  @initial_obj Sets@{o so} (sets_special_initial_IEM E)
    = @initial_obj Sets@{o so} Sets_Initial := eq_refl.

Fail Example p452_n18_sets_iem_obj_singleton@{o so +| o < so +}
  (E : IEM@{o}) :
  @initial_obj Sets@{o so} (sets_special_initial_IEM E)
    = @terminal_obj Sets@{o so} Sets_Terminal := eq_refl.

(** ** Controls without a negative / ** 没有否定的控制 *)

(* The degenerate generic witness reads back as [unit]. / 退化的通用见证回读为 [unit]。 *)
Example p452_indiscrete_obj@{j o t +| j < o, j < t +} :
  @initial_obj (Indiscrete@{o j j} Type@{j}) Indiscrete_types_special_initial
    = (Datatypes.unit : Type@{j}) := eq_refl.

(* The non-degenerate generic witness has no members. / 非退化的通用见证没有成员。 *)
Check (Subsets_special_initial_is_empty :
  ∀ (X : SetoidObject) (G : Cogenerator (Subsets X)) (x : carrier X),
    (@initial_obj _ (Subsets_special_initial X G)
       : carrier (Powerset_Prop_obj X)) x → False).

(* The book's form at [Sets], from the #451 intersection. / 这本书在 [Sets] 的形式，从 #451 路口。 *)
Definition p452_sets_book@{o so +| Set < o, o < so +} (U : Untruncate@{o}) :
  @Initial Sets@{o so} :=
  special_initial_object_book Sets_Complete (Sets_Cogenerator_untruncate U)
    (Sets_HasClassIntersections_untruncate U).

(* No family of copies of the terminal object cogenerates [Sets]. / 没有终端对象的副本族共同生成 [Sets]。 *)
Check (Sets_terminal_not_cogenerates :
  ∀ I : Type,
    ¬ (∀ (x y : SetoidObject) (f g : x ~{Sets}~> y),
         (I → ∀ k : y ~{Sets}~> @terminal_obj Sets Sets_Terminal,
                k ∘ f ≈ k ∘ g) → f ≈ g)).

(** ** Guard block / ** 防守格挡 *)

Check @equalizer_sub.
Check @least_sub_arrows_agree.
Check @cogen_prod_to_power.
Check @cogen_canonical_sub.
Check @complete_pullbacks.
Check @cogen_pullback_sub.
Check @cogen_pullback_to.
Check @special_initial_zero.
Check @special_initial_object_least.
Check @least_of_intersection_all.
Check @intersection_all_of_least.
Check @special_initial_object.
Check @special_initial_object_obj.
Check @special_initial_object_zero.
Check @special_initial_IsInitialObj.
Check @HasClassIntersections.
Check @special_initial_object_book.
Check @special_initial_object_book_obj.
Check @wellpowered_class_intersections.
Check @special_initial_object_wellpowered.
Check @special_initial_object_wellpowered_obj.
Check @special_initial_object_wellpowered_at.
Check @special_initial_object_wellpowered_at_obj.
Check @special_initial_object_small.
Check @special_weakly_initial.
Check @special_vs_freyd.
Check @wif_of_cogenerator.
Check @freyd_of_cogenerator.
Check @special_vs_freyd_of_cogenerator.
Check @Subsets_Cogenerator_empty.
Check @Subsets_Cogenerator_bot.
Check @Subsets_special_initial.
Check @Subsets_special_initial_obj.
Check @Subsets_special_initial_empty.
Check @Subsets_special_initial_bot.
Check @Subsets_special_vs_bot.
Check @Subsets_special_initial_is_empty.
Check @Subsets_special_initial_not_top.
Check @Indiscrete_Cogenerator_empty.
Check @Indiscrete_types_special_initial.
Check @Indiscrete_types_special_initial_obj.
Check @Sets_Cogenerator_untruncate.
Check @sets_cogenerator_untruncate_obj.
Check @sets_bool_char.
Check @Sets_Cogenerator_IEM.
Check @sets_cogenerator_IEM_obj.
Check @Sets_Cogenerator_large.
Check @Sets_terminal_not_cogenerates.
Check @setsop_comp.
Check @setsop_cog.
Check @setsop_point.
Check @setsop_L.
Check @setsop_L_least.
Check @setsop_special_initial.
Check @setsop_special_obj.
Check @setsop_special_vs_known.
Check @setsop_terminal_IsInitialObj.
Check @sets_special_initial_untruncate.
Check @sets_special_untruncate_obj.
Check @sets_special_initial_wellpowered.
Check @sets_special_wellpowered_obj.
Check @sets_special_wellpowered_vs_known.
Check @sets_special_wellpowered_empty.
Check @Sets_HasClassIntersections_untruncate.
Check @sets_special_initial_book.
Check @sets_special_book_obj.
Check @sets_special_book_vs_known.
Check @sets_special_initial_IEM.
Check @sets_special_IEM_obj.
Check @sets_special_initial_IEM_at_Set.
