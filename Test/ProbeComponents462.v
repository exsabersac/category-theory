(**
* Probe for the connected and path components (issue #462)

    Pins the measured boundaries of the three files #462 adds for Mac
    Lane §V.9 Exercise 1, book p. 135 (PDF p. 144), catalog item
    maclane:V.9:ex1, with the appended Riehl Example 3.3.2
    (riehl:3.3:example2).  The files are Adjunction/Continuity/
    Equalizer.v (right adjoints preserve equalizers, in the elementary
    form, and the refutation it packages), Instance/Top/Components.v
    (the connected-components functor on the locally connected spaces of
    [PTopCat], left adjoint to the discrete functor from the
    propositional sets and with no left adjoint of its own, and the
    reading into all of [Sets] under [Untruncate]) and Instance/Top/
    Components/Paths.v (Riehl's path-components functor as the colimit
    functor after P).  N1-N12 restate refusals that #462's two builders,
    its review and its fold measured in scratch files (LABELS, below);
    every one is recorded in a target header, which cites it by its
    label here.  The positive controls restate the files' claims
    independently.
    CORRECTION (#1347): N10 and N11 now hold at [eq_refl], since
    Instance/Sets.v gives its identity's and composite's properness fields
    as terms; they are controls, and keep their labels.

    THE IMPORT LIST, measured by comparing [Require] lines by script.
    First the ten standard-library lines of Instance/Top/Components/
    Paths.v, in its order: that file puts them before its [Category]
    lines, and placed after Category.Lib they shadow Lib/Setoid.v's
    [equiv] ([Locate equiv] then lists Relation_Definitions.equiv
    first, measured), which [p462_components_equiv] below does not
    survive.  Then, target by target in the order named above, the
    [Require] lines each adds to those before it, in its own order, and
    then that target: eight lines and Equalizer.v, twelve and
    Components.v (Theory/Concrete.v required without [Import], as
    Components.v requires it), twelve and Paths.v.  Then five lines for
    the walls: Instance/Top.v and Instance/Top/Forgetful.v (the
    Type-valued [Top] and its discrete functor, N1-N5), and
    Functor/Hom.v, Theory/Kan/Extension.v and Construction/Opposite.v
    (the Yoneda derivation, N12).  Fifty lines, thirty-nine of them
    naming [Category] modules.  Under this list [Print Libraries] in a
    scratch file loads one hundred and thirty [Category] modules, the
    three targets among them, and eight modules of the standard
    library's reals, seven under Reals/Cauchy and the eighth
    Reals/Abstract/ConstructiveReals.  A shorter import list is what
    makes a probe pass for no reason.  CORRECTION (#469): #469 appends a
    fifty-first line, the fortieth naming a [Category] module (Instance/
    Sets/Propositional/Full.v, after every other command), and the list
    now loads one hundred and thirty-one [Category] modules, by the same
    [Print Libraries] count.  CORRECTION (#1349): Components.v now
    requires Full.v, so the fifty lines before it load the one hundred and
    thirty-one already, Full.v among them, and the fifty-first adds no
    module, by the same count.

    DISCIPLINE.  The instrument was checked both ways: the refutation of an
    absent name is refused for that reason ("The reference p462_absent_name
    was not found in the current environment."), and each of the forty-nine
    definitions and examples of this file that is not a refutation, wrapped
    in the refutation keyword in a copy of this WHOLE file, stops the build
    at that command with the report that the guarded command had been
    accepted (forty-nine of forty-nine, by a script over the copies;
    CORRECTION (#469): fifty-one of fifty-one with #469's two controls
    at the end, each wrapped alone in a copy of the whole file).  Every
    negative other than that instrument is a [Definition] or an [Example],
    never a [Check], so that an open evar cannot satisfy it.  Each negative
    was stripped of its refutation keyword in a copy of this WHOLE file, one
    at a time, compiled, and its error read; each of the twelve copies stops
    inside the stripped command (by the File line of its error, compared by
    a script with the command's extent).  The kind recorded is the kind of
    that error, and each negative has positive controls beside it.
    Quotations are Rocq 9.1.1's under this file's import list, with the
    error's environment block left out; Rocq prints the "cannot unify"
    parenthetical with the short names in scope, and <1> to <7> stand for
    the universes a stripped copy names after itself and a serial number.
    The three targets and this file also compile on Coq 8.19.2 and 8.20.1,
    with no warning, overlaid on the prebuilt trees of this library for
    those versions, whose sources of the one hundred and twenty-seven
    modules this file loads besides the three targets are this tree's byte
    for byte (compared by script) but for one, Instance/Top/Prop.v, which
    differs only by the CORRECTION (#462) comment #462 adds.  Each of the
    twelve stripped copies is refused there inside the stripped command, at
    the File line of the Rocq 9.1.1 refusal, and with the Rocq 9.1.1 error
    up to the serial names of universes (compared by a script), with two
    exceptions: Coq 8.19.2 prints the type mismatch of N1 and N2 without the
    parenthetical that names the universe inconsistency, and both older
    versions mark N1's term [Sets@{o so}] (characters 21-32 of its line)
    where Rocq 9.1.1 marks [Sets] (21-25).  Five controls were adjusted to
    reach the older versions, because Coq 8.19.2 refuses a closed constraint
    list that omits the constraints the template-polymorphic [ex],
    [inhabited], [sigT] and [prod] contribute ("Universe constraints are not
    implied by the ones declared"): [tcomp_rel_prop] and [p462_tconnsub]
    take the closed universe list [@{o}] in place of [@{o|}], and the three
    controls one universe up an extensible constraint list in place of the
    closed [@{o h | o < h}].
    CORRECTION (#1347): N10 and N11 are controls now.  Each, wrapped in
    the refutation keyword in a copy of this WHOLE file, stops the build
    at that command with the report that it was accepted, so the
    definitions and examples that are not refutations are fifty-three.
    The negatives are ten, and each of the ten, stripped in a copy of
    this WHOLE file, stops inside its command with the error it printed
    before #1347 (compared by script, universe serial names aside).  Both
    measurements on Rocq 9.1.1 only; the older versions were not re-run.
    Re-run after #1349, which changes what the [Require] of Components.v
    loads, in whole-file copies on Rocq 9.1.1: each of the eleven
    stripped copies stops inside its command with the text the tree
    before #1349 gives, from its "Error:", and each of the fifty-three
    controls, wrapped, stops the build at its own command.  In overlays
    of master 687ac356 with #1349's changes, on Coq 8.19.2 and 8.20.1,
    the three targets and this file compile, with the warnings of master
    and none from these files.

    KINDS.  Thirteen refutations, counted as the lines that open with the
    refutation keyword: NAME-ABSENCE (the instrument), UNIVERSE (N1, N2,
    N3, N4, N5, N8, N12), ELIMINATION (N6, N7) and CONVERSION (N9, N10,
    N11): one, seven, two and three.  A UNIVERSE refusal is a type
    mismatch whose parenthetical is a universe inconsistency, or a bare
    universe inconsistency (N8); an ELIMINATION refusal is "Incorrect
    elimination" of a proof of a proposition into a type; a CONVERSION
    refusal is [eq_refl] refused with a "cannot unify" parenthetical.
    CORRECTION (#1347): N10 and N11 now hold at [eq_refl] and are
    controls, so the refutations are eleven and CONVERSION is N9 alone:
    one, seven, two and one.  N10 and N11 were CONVERSION by their errors;
    Instance/Top/Components/Paths.v gave their cause, by argument, as the
    two setoid maps' respectfulness proofs being built differently, and
    the measurement shows the residue was the standard library's: the
    opaque lemmas instance resolution had put in Instance/Sets.v's two
    properness fields.

    LABELS.  The review's TopFun is N1 and its TopProp the control
    [tcomp_rel_prop]; builder-comp's W1, W2 and W3 are N3, N4 and N5,
    its E1' is N7, its AtO N8 and its Conv N9; builder-pi0's M2 is N10
    (its Meas1) and N11 (its Meas3b), and its M1 is N12.  N2 is the
    fold's own, and so is N6, which stands for builder-comp's E1: that
    command matched on a proof of [comp_rel] and returned
    [reflexivity _] where [pmap g x ≈ pmap g y] was expected, so it was
    ill-typed apart from the elimination; N6 extracts a Type-valued
    witness instead, a term well typed but for the elimination.  The
    labels are not constants: each refutation carries its own in a
    comment on the line above it, the instrument's reading "The
    instrument".
    CORRECTION (#1347): N10 and N11 are controls now and keep these
    labels, each in a comment on the line above it.

    ** Instance/Top/Components.v, ENCODING: the Type-valued [Top]

    Controls: a functor [Top@{h o} ⟶ Sets@{h so}], one universe up, and
    an [Adjunction] record between [Top@{h o}] and [Sets@{h so}]
    ([p462_top_to_sets_up], [p462_top_adj_up]); the component relation
    over [Top], Prop-valued, under the closed universe list [@{o}]
    ([p462_tconnsub], [tcomp_rel_prop]); the three Type-valued
    forms at [Type@{h}] under [o < h] ([p462_tcomp_rel_sigma_up],
    [p462_tcomp_rel_forall_up], [p462_tconnected_up]).

    N1 (UNIVERSE).  The functor into the [Sets] of the point setoids:
      The term "Sets" has type "Category@{so o o}" while it is expected
      to have type "Category@{<1> <2> <3>}" (universe inconsistency:
      Cannot enforce o = <2> because o < h <= <2>).
    N2 (UNIVERSE).  An adjunction one universe up whose right adjoint is
    Instance/Top/Forgetful.v's discrete functor:
      The term "Top_Discrete" has type "Sets@{<1> <3>} ⟶ Top@{<2> <1>}"
      while it is expected to have type "Sets@{h so} ⟶ Top@{h o}"
      (universe inconsistency: Cannot enforce <2> = h because h < <2>).
    N3, N4, N5 (UNIVERSE).  The sum over Type-valued subsets, the
    quasi-component form and connectedness over discrete targets, at the
    points' universe:
      The term "∃ W : X → Type, W x ∧ W y" has type "Type@{o+1}" while
      it is expected to have type "Type@{o}" (universe inconsistency:
      Cannot enforce o < o because o = o).
      The term "∀ U : X → Type, IsOpen X U → U x → U y" has type
      "Type@{o+1}" while it is expected to have type "Type@{o}"
      (universe inconsistency: Cannot enforce o < o because o = o).
      The term "∀ (S : SetoidObject) (g : X → S) (a b : X), W a → W b →
      g a ≈ g b" has type "Type@{max(o+1,<1>,<2>,<3>)}" while it is
      expected to have type "Type@{o}" (universe inconsistency: Cannot
      enforce o < o because o = o).

    ** Instance/Top/Components.v, MAC LANE'S SET: the propositional sets

    Controls: through a [PropEquiv] of the target the truncation is
    eliminated ([p462_transpose_pe], Lib/Setoid/Propositional.v's
    [pequiv_elim_inhabited]) and a continuous map into a discrete space
    respects components ([p462_comp_respect]); into all of [Sets] an
    adjunction makes [Untruncate] merely true and yields the unsquashing
    principle ([p462_unsquash], [p462_unsquash_principle]), and under
    [Untruncate] the adjunction exists ([p462_adj_Sets]); [PSetsSub]'s
    object predicate placed at the points' universe
    ([p462_psets_sub_at_o]), and [PSetsSub] itself at [o := Set]
    ([p462_psets_sub_Set]).

    N6 (ELIMINATION).  A Type-valued witness out of [comp_rel]:
      Incorrect elimination of "H" in the inductive type "ex": the
      return type has sort "Type" while it should be SProp or Prop.
    N7 (ELIMINATION).  The truncated equality of two values, into the
    equality itself:
      Incorrect elimination of "HR" in the inductive type "inhabited":
      the return type has sort "Type" while it should be SProp or Prop.
    (Both go on: "Elimination of an inductive object of sort Prop is not
    allowed on a predicate in sort "Type" because proofs can be
    eliminated only to build proofs.")
    N8 (UNIVERSE).  [PSetsSub]'s predicate placed at the points'
    universe, at [o := Set]:
      Universe inconsistency. Cannot enforce Set < Set because Set = Set.

    ** Adjunction/Continuity/Equalizer.v: why the proof is direct

    Controls: the two diagrams agree on both objects at [eq_refl]
    ([p462_pair_obj_X], [p462_pair_obj_Y]); right adjoints preserve
    equalizers ([p462_rapl_equalizers]).

    N9 (CONVERSION).  The header's WHY A DIRECT PROOF, at the variable
    functor and the variable pair of a [Section]:
      (cannot unify "U ◯ APair f g" and "APair (fmap[U] f) (fmap[U] g)")

    ** Instance/Top/Components.v: the adjunction and the refutations

    Controls: both transposes and the unit are the identity on points,
    at [eq_refl], for the adjunction at [PSets] and for the one into all
    of [Sets] under [Untruncate] ([p462_to_points], [p462_from_points],
    [p462_unit_points], [p462_Sets_to_points], [p462_Sets_from_points]),
    which the two adjunctions' [Defined] closure allows; D is [PDisc] on
    objects and C's equality is [comp_rel], at [eq_refl]
    ([p462_LDisc_obj], [p462_components_equiv]); the fork on the
    three-point space is an equalizer in [Lconn] that C does not
    preserve ([p462_zig_equalizer], [p462_zig_not_preserved]); the four
    refutations ([p462_no_left_adjoint], [p462_any_left_adjoint],
    [p462_no_left_on_PTop], [p462_PDisc_no_left]); ten theorems at
    [o := Set], the controls whose names end in [_at_Set].

    ** Instance/Top/Components/Paths.v: π₀ = colim ∘ P

    Controls: the arrow part of π₀ IS [Colim_map] of P's, and on a
    representative point it is postcomposition, at [eq_refl]
    ([p462_pi0_fmap], [p462_pi0_fmap_point]); the identity law up to
    [≈] ([p462_pi0_id]) and the underlying functions at [eq_refl]
    ([p462_id_fun]); the endpoint pair in [PTopCat^op] and the Yoneda
    embedding of [PTopCat] ([p462_iota], [p462_yoneda]); the interval
    connected in the two-point form, π₀ of the interval one point and
    π₀ of [PBool] two ([p462_interval_connected], [p462_pi0_interval],
    [p462_pi0_bool]).

    N10 (CONVERSION).  The header's STRENGTHS, the identity law on a
    representative point:
      (cannot unify "fmap[PPi0] (pid X) (ParY; x)" and "(ParY; x)")
    N11 (CONVERSION).  The two setoid maps under it:
      (cannot unify "pmap (pcompose (pid X) x)" and "pmap x")
    CORRECTION (#1347): N10 and N11 now hold at [eq_refl], since
    Instance/Sets.v gives its identity's and composite's properness fields
    as terms; they are controls.  The map part of [pcompose (pid X) x] is
    [setoid_morphism_compose] of [setoid_morphism_id] and [pmap x], and
    what kept it from converting with [pmap x] was the two properness fields,
    the identity's and that composite's.
    N12 (UNIVERSE).  The header's P AND π₀, P derived from the Yoneda
    embedding:
      The term "Curried_CoHom PTopCat" has type "@Functor@{so o o <1>
      <2> <2>} PTopCat@{o so} (@Fun@{so o <3> o <1> <2> <3>}
      (Opposite@{o so} PTopCat@{o so}) Sets@{o <3>})" while it is
      expected to have type "@Functor@{<4> <5> <5> <6> <5> <5>} ?C ?D"
      (universe inconsistency: Cannot enforce <2> = o because o < <7>
      <= <2>).

    ** Closure: a readback, not a refutation

    [Print Assumptions] of [right_adjoint_PreservesEqualizers],
    [components_functor], [components_left_adjoint_discrete],
    [components_no_left_adjoint], [components_left_adjoint_discrete_Sets]
    and [PPi0], near the end of this file, each print "Closed under the
    global context".  A [Print Assumptions] cannot refuse, so these lines
    are readbacks and guard nothing; the Makefile's print-assumptions
    gate is where closure is kept.  By the same command all forty-nine
    constants of this file are closed under the global context.
    CORRECTION (#1347): by the same command, in a copy of this WHOLE
    file, all fifty-three constants it now defines are closed, #469's two
    controls and N10 and N11 among them.

    NOT PINNED HERE.  (a) [About] readbacks as such: the headers' [Set]
    censuses, their attributions to first carriers, and the [Set < o]
    that [p462_psets_sub_at_o] carries, read by [About] in a scratch
    file.  (b) Flip censuses and the closure of the targets under
    [Print Assumptions]: measurements of the build rather than of
    commands.  (c) The refusals of the closed universe lists
    [ibis_cv_ge@{o}] and [ibis_cv_le@{o}] that Coq 8.19.2 and 8.20.1
    make and Rocq 9.1.1 does not (Paths.v's UNIVERSES): a file that
    compiles under all three cannot pin a refusal made by only two.
    (d) The absences the headers record (no comparison of path
    components with connected components, no axiom-free inhabitant of
    [Untruncate], connectedness of the interval in the two-point form
    only): an absence has no command.  (e) builder-comp's E1 as it was
    written (LABELS).

    The guard block at the end names the two hundred and fifty-six
    constants of the three targets, so that a rename breaks this file:
    two of Adjunction/Continuity/Equalizer.v, one hundred and
    twenty-eight of Instance/Top/Components.v and one hundred and
    twenty-six of Instance/Top/Components/Paths.v.  They are exactly the
    entries [Print Module] gives for each, forty-two [Program]
    obligations among them, and the three constructors of the one
    inductive, [zig_pt], which [Print Module] lists under its type; no
    record is declared, so there is no [Build_] constructor to add.
    Each is written fully qualified, so that no short name in scope can
    stand in for it.  CORRECTION (#1349): the squash setoid's four
    constants, [squash_rel], [squash_sym], [squash_trans] and
    [SquashSetoid], moved from Instance/Top/Components.v to
    Instance/Sets/Propositional/Full.v, which Components.v now requires,
    and the guard names them there, in a group after Components.v's: one
    hundred and twenty-four of Components.v (its [Print Module] entries,
    the three constructors included) and four of Full.v, still two
    hundred and fifty-six lines.  [unsquash_Untruncate] and
    [Untruncate_unsquash] stay in Components.v, now derived from Full.v's
    [untr_of_choice] and [choice_of_untr], and [PSetsSub] and [PSets] are
    Full.v's [PropSets_sub] and [PropSets] by definition.

--------
* 探测连通分量和路径分量（问题 #462）

固定三个文件 #462 为 Mac 添加的测量边界
    Lane §V.9 练习 1，书第 135 页（PDF 第 144 页），目录项
    maclane:V.9:ex1，附加 Riehl 示例 3.3.2
    (riehl:3.3:example2)。这些文件是 Adjunction/Continuity/Equalizer.v（右伴随保持等化器，以基本形式表示，以及它打包的反驳）、Instance/Top/Components.v（在 [PTopCat] 的局部连通空间上的连通分量函子，是来自命题集的离散函子的左伴随，并且自身没有左伴随，以及在 [Untruncate] 下读取到所有 [Sets]）和 Instance/Top/Components/Paths.v（Riehl 的路径分量函子作为 P 之后的余极限函子）。N1-N12 重述了 #462 的两名构建者的拒绝，及其在草稿文件（下文标签）中的审查和折叠测量；每一项都记录在目标标题中，并在此引用其标签。阳性对照独立地重述文件的声明。更正（#1347）：N10 和 N11 现保持在 [eq_refl]，因为 Instance/Sets.v 提供了其身份及复合的正确性字段作为项；它们是对照，并保留其标签。

导入列表，通过脚本比较 [Require] 行来衡量。首先是 Instance/Top/Components/Paths.v 的十条标准库行，按其顺序：该文件将它们放在其 [Category] 行之前，并且放在 Category.Lib 之后，它们会覆盖 Lib/Setoid.v 的 [equiv]（然后 [Locate equiv] 首先列出 Relation_Definitions.equiv，被衡量），而 [p462_components_equiv] 在下面不会保留。然后，按照上述顺序，一个目标接一个目标，[Require] 的每一行都会在自身顺序中加入到之前的行中，然后是该目标：八行和 Equalizer.v，十二行和 Components.v（在没有 [Import] 的情况下需要 Theory/Concrete.v，因为 Components.v 需要它），十二行和 Paths.v。然后是墙的五行：Instance/Top.v 和 Instance/Top/Forgetful.v（类型值 [Top] 及其离散函子，N1-N5），以及 Functor/Hom.v、Theory/Kan/Extension.v 和 Construction/Opposite.v（Yoneda 推导，N12）。五十行，其中三十九行命名了 [Category] 模块。在这个列表下，[Print Libraries] 在一个临时文件中加载了一百三十个 [Category] 模块，其中三个是目标模块，还有标准库中的八个实数模块，其中七个在 Reals/Cauchy 下，第八个在 Reals/Abstract/ConstructiveReals 下。导入列表较短是使探针无缘无故通过的原因。修正 (#469)：#469 添加了第五十一行，第四十行命名了一个 [Category] 模块（Instance/Sets/Propositional/Full.v，在每个其他命令之后），现在该列表共加载了一百三十一 [Category] 模块，按相同的 [Print Libraries] 计数。更正 (#1349)：Components.v 现在需要 Full.v，所以在它之前的五十行已经加载了一百三十一行，其中包含 Full.v，第五十一行没有新增任何模块，根据同样的计算方式。

纪律。该工具以两种方式进行了检查：由于这个原因，缺失名称的反驳被拒绝（“在当前环境中未找到参考 p462_absent_name。”），并且该文件中每一个不是反驳的四十九个定义和示例，在整个文件的副本中用反驳关键字封装，每个都在该命令处停止构建，并报告守卫命令已被接受（49 个中的 49 个，通过对副本的脚本；更正（#469）：51 个中的 51 个，#469 的两个控制在最后，每个单独封装在整个文件的副本中）。除了那个仪器之外的每个否定都是 [Definition] 或 [Example]，从来不是 [Check]，因此一个打开的 evar 无法满足它。每个否定都在这个整个文件的副本中一次去掉了其反驳关键字，编译后读取其错误；这十二个副本中的每一个都在去掉的命令内部停止（通过错误的文件行，由脚本与命令的范围进行比较）。记录的类型是该错误的类型，每个否定旁边都有正面控制。引用是 Rocq 9.1.1 在此文件的导入列表下的内容，错误的环境块被省略；Rocq 会打印带有作用域内简写名称的“无法统一”括注，而 <1> 到 <7> 代表一个被剥离的副本按照其自身名称和序列号命名的宇宙。这三个目标和这个文件也可以在 Coq 8.19.2 和 8.20.1 上编译，没有任何警告，覆盖在该库这些版本的预构建树上，这个文件除了三个目标之外加载的一百二十七个模块的源文件与该树逐字（通过脚本对比）相同，唯独 Instance/Top/Prop.v 不同，仅在于添加了 CORRECTION (#462) 注释 #462。每一个十二个剥离的副本都在剥离命令内部被拒绝，在 Rocq 9.1.1 拒绝的文件行上，并且伴随 Rocq 9.1.1 错误直到宇宙的序列名称（由脚本比较），有两个例外：Coq 8.19.2 打印 N1 和 N2 的类型不匹配时没有带上命名宇宙不一致的括号，并且两个旧版本都标记 N1 的项 [Sets@{o so}]（其行的第 21-32 个字符）而 Rocq 9.1.1 标记 [Sets]（第 21-25 个字符）。为了达到旧版本，对五个控件进行了调整，因为 Coq 8.19.2 拒绝一个封闭的约束列表，如果该列表中省略了模板多态 [ex]、[inhabited]、[sigT] 和 [prod] 所贡献的约束（“宇宙约束并不由声明的约束隐含”）：[tcomp_rel_prop] 和 [p462_tconnsub] 用封闭宇宙列表 [@{o}] 代替 [@{o|}]，而这三个控件将封闭的 [@{o h | o < h}] 替换为可扩展约束列表中的一个宇宙。修正 (#1347)：N10 和 N11 现在是控件。每个在这个完整文件的副本中用反驳关键词包裹的部分，都会在该命令处停止构建，并报告它被接受，因此那些不是反驳的定义和例子共有五十三个。否定项有十个，而这十个中，每个在这个完整文件的副本中被剥离后，都会在其命令内部以它在#1347之前打印的错误停止（通过脚本比较，不考虑宇宙序列名）。以上两个测量仅在 Rocq 9.1.1 上进行；旧版本未重新运行。在 #1349 之后重新运行，它改变了 Components.v 中 [Require] 的加载方式，在 Rocq 9.1.1 上的整文件副本中：每一个剥离的十一份副本都会在其命令中停止，并显示 #1349 之前版本树提供的文本，从其“Error:”开始；每一个包裹的五十三个控件都会在其自身命令处停止构建。在带有 #1349 改动的 master 687ac356 覆盖中，在 Coq 8.19.2 和 8.20.1 上，三个目标和这个文件可以编译，伴随 master 的警告，而这些文件没有警告。

类别。十三个反驳，被计为以反驳关键词开头的行：NAME-ABSENCE（工具）、UNIVERSE（N1、N2、N3、N4、N5、N8、N12）、ELIMINATION（N6、N7）和CONVERSION（N9、N10、N11）：分别为一个、七个、两个和三个。UNIVERSE 拒绝是一种类型不匹配，其括号内为宇宙不一致，或是单独的宇宙不一致（N8）；ELIMINATION 拒绝是将一个命题的证明错误地消除为某种类型；CONVERSION 拒绝是[eq_refl] 被拒绝，括号中显示“无法统一”。更正 (#1347)：N10 和 N11 现在保持在 [eq_refl] 并且是控制，因此反驳是十一，而 CONVERSION 仅是 N9：一、七、二 和一。N10 和 N11 是由于它们的错误而被 CONVERSION；Instance/Top/Components/Paths.v 给出了它们原因，通过论证，是因为两个集合态映射的尊重性证明构建方式不同，而测量显示残差是标准库的：不透明引理的实例解析已放入 Instance/Sets.v 的两个 properness 字段中。

标签。审查的 TopFun 是 N1，其 TopProp 是控制 [tcomp_rel_prop]；builder-comp 的 W1、W2 和 W3 分别是 N3、N4 和 N5，其 E1' 是 N7，其 AtO 是 N8，其 Conv 是 N9；builder-pi0 的 M2 是 N10（其 Meas1）和 N11（其 Meas3b），其 M1 是 N12。N2 是 fold 自身的，N6 也是，这代表 builder-comp 的 E1：该命令在 [comp_rel] 的证明上匹配并返回了 [reflexivity _]，而预期的是 [pmap g x ≈ pmap g y]，因此除了消去外，它类型错误；N6 提取了一个类型值的见证人，一个在消去之外类型正确的项。这些标签不是常量：每个反驳在其上方一行的注释中都有自己的标签，仪器的读数为“仪器”。更正（#1347）：N10 和 N11 现在是控制项，并保留这些标签，每个都在其上方一行的注释中。

** 实例/顶层/组件.v, 编码: 类型值 [Top]

控件：一个函子 [Top@{h o} ⟶ Sets@{h so}]，在高一阶的宇宙中，以及一个 [Adjunction] 记录在 [Top@{h o}] 和 [Sets@{h so}] 之间 ([p462_top_to_sets_up], [p462_top_adj_up])；在封闭宇宙列表 [@{o}] ([p462_tconnsub], [tcomp_rel_prop]) 下，组件关系在 [Top] 上，为 Prop 值；在 [o < h] ([p462_tcomp_rel_sigma_up], [p462_tcomp_rel_forall_up], [p462_tconnected_up]) 下，[Type@{h}] 处的三个 Type 值形式。

N1（宇宙）。点集合的 [Sets] 上函子：
      术语“Sets”的类型为“Category@{so o o}”，而预期其类型为“Category@{<1> <2> <3>}”（宇宙不一致：无法强制 o = <2> 因为 o < h <= <2>）。
N2（宇宙）。一个向上一个宇宙的伴随，其右伴随为 Instance/Top/Forgetful.v 的离散函子：
      术语“Top_Discrete”的类型为“Sets@{<1> <3>} ⟶ Top@{<2> <1>}”，而预期其类型为“Sets@{h so} ⟶ Top@{h o}”（宇宙不一致：无法强制 <2> = h 因为 h < <2>）。
N3，N4，N5（宇宙）。在 Type 值子集上的求和、准分量形式以及在离散目标上的连通性，在点的宇宙中：
术语 “∃ W : X → Type, W x ∧ W y” 的类型是 “Type@{o+1}”，而期望的类型是 “Type@{o}”（宇宙不一致：无法强制 o < o 因为 o = o）。术语 “∀ U : X → Type, IsOpen X U → U x → U y” 的类型是 “Type@{o+1}”，而期望的类型是 “Type@{o}”（宇宙不一致：无法强制 o < o 因为 o = o）。术语 "∀ (S : SetoidObject) (g : X → S) (a b : X), W a → W b → g a ≈ g b" 的类型为 "Type@{max(o+1,<1>,<2>,<3>)}"，而预期的类型为 "Type@{o}"（宇宙不一致：无法强制执行 o < o 因为 o = o）。

** 实例/顶层/组件.v，麦克·莱恩的集合：命题集合

控制：通过目标的 [PropEquiv]，截断被消除（[p462_transpose_pe]，Lib/Setoid/Propositional.v 的 [pequiv_elim_inhabited]），并且到离散空间的连续映射尊重分量（[p462_comp_respect]）；对于所有 [Sets]，一个伴随使 [Untruncate] 仅仅为真，并产生取消压缩原理（[p462_unsquash]，[p462_unsquash_principle]），并且在 [Untruncate] 下伴随存在（[p462_adj_Sets]）；[PSetsSub] 的对象谓词放置在点的宇宙中（[p462_psets_sub_at_o]），以及 [PSetsSub] 本身位于 [o := Set]（[p462_psets_sub_Set]）。

N6（消去）。来自 [comp_rel] 的类型值见证：
      在归纳类型“ex”中对“H”的消去不正确：返回类型的类型为“Type”，而它应该是 SProp 或 Prop。
N7（消去）。两个值的截断等式转换为等式本身：
      在归纳类型“inhabited”中对“HR”的消去不正确：返回类型的类型为“Type”，而它应该是 SProp 或 Prop。（两者均附带说明：“不允许在类型为 Prop 的归纳对象上对类型为 Type 的谓词进行消去，因为证明只能用于构建其他证明。”）
N8（宇宙）。[PSetsSub] 的谓词置于点的宇宙，在 [o := Set]：
宇宙不一致。无法强制执行 Set < Set，因为 Set = Set。

** Adjunction/Continuity/Equalizer.v：为什么证明是直接的

控件：两个图在 [eq_refl]（[p462_pair_obj_X]、[p462_pair_obj_Y]）上的两个对象上是一致的；右伴随保持等化器（[p462_rapl_equalizers]）。

N9（转换）。标题为“为什么是直接证明”，位于变量函子和 [Section] 的变量对处：
      （无法统一 "U ◯ APair f g" 和 "APair (fmap[U] f) (fmap[U] g)"）

** Instance/Top/Components.v：伴随与反驳

控制：在 [eq_refl] 上，转换和单位在点上都是恒等的，对于 [PSets] 上的伴随以及通过 [Untruncate] 进入整个 [Sets]（[p462_to_points]、[p462_from_points]、[p462_unit_points]、[p462_Sets_to_points]、[p462_Sets_from_points]）的伴随两者的 [Defined] 闭包允许的情况；D 在对象上是 [PDisc]，C 的相等性是 [comp_rel]，在 [eq_refl]（[p462_LDisc_obj]、[p462_components_equiv]）；三点空间上的叉是 [Lconn] 中的等化器，而 C 不保留（[p462_zig_equalizer]、[p462_zig_not_preserved]）；四个反例（[p462_no_left_adjoint]、[p462_any_left_adjoint]、[p462_no_left_on_PTop]、[p462_PDisc_no_left]）；在 [o := Set] 上的十个定理，其控制名称以 [_at_Set] 结尾。

** 实例/顶层/组件/路径.v: π₀ = colim ∘ P

控制：π₀ 的箭头部分是 P 的 [Colim_map]，并且在一个代表点上它是复合后置，在 [eq_refl] ([p462_pi0_fmap], [p462_pi0_fmap_point])；恒等律直到 [≈] ([p462_pi0_id]) 以及在 [eq_refl] ([p462_id_fun]) 上的基础函数；端点对在 [PTopCat^op] 以及 [PTopCat] 的 Yoneda 嵌入 ([p462_iota], [p462_yoneda])；区间以两点形式连接，区间单点的 π₀ 和 [PBool] 两点的 π₀ ([p462_interval_connected], [p462_pi0_interval], [p462_pi0_bool])。

N10（转换）。头部的优点，在一个代表点上的恒等律：
  （无法统一 “fmap[PPi0] (pid X) (ParY; x)” 和 “(ParY; x)”）
N11（转换）。其下的两个集合态射图：
  （无法统一 “pmap (pcompose (pid X) x)” 和 “pmap x”）
修正（#1347）：N10 和 N11 现在在 [eq_refl] 上成立，因为 Instance/Sets.v 提供了其恒等和复合函数的适当性字段作为项；它们是控制项。[pcompose (pid X) x] 的地图部分是
    [setoid_morphism_id] 和 [pmap x] 的 [setoid_morphism_compose]，并且
    阻止其与 [pmap x] 转换的是两个适当性字段，
    一个是身份，一个是那个复合的。N12（宇宙）。头的 P 和 π₀，P 来源于 Yoneda 嵌入：
      术语 “Curried_CoHom PTopCat” 的类型是 “@Functor@{so o o <1>
      <2> <2>} PTopCat@{o so} (@Fun@{so o <3> o <1> <2> <3>}
      (Opposite@{o so} PTopCat@{o so}) Sets@{o <3>})”，而它被期望的类型是 “@Functor@{<4> <5> <5> <6> <5> <5>} ?C ?D”
      （宇宙不一致：无法强制 <2> = o 因为 o < <7> <= <2>）。

** 结论：一种复述，而非反驳

[Print Assumptions]、[right_adjoint_PreservesEqualizers]、[components_functor]、[components_left_adjoint_discrete]、[components_no_left_adjoint]、[components_left_adjoint_discrete_Sets] 和 [PPi0]，在此文件的末尾，每个都打印“在全局上下文下已关闭”。[Print Assumptions] 无法拒绝，所以这些行只是回读，并不保护任何内容；Makefile 的 print-assumptions 网关才是保持闭合的地方。通过同一命令，此文件的四十九个常量均在全局上下文下闭合。修正（#1347）：通过同一命令，在此整个文件的副本中，它现在定义的五十三个常量都闭合，包括 #469 的两个控制以及其中的 N10 和 N11。

这里未固定。(a) [About] 的回读如下：标题的 [Set] 计数、它们分配给首个承运人的情况，以及 [Set < o] [p462_psets_sub_at_o] 所携带的内容，由 [About] 在临时文件中读取。(b) 在 [Print Assumptions] 下翻转计数和目标的闭合：构建的测量而非命令的测量。(c) Coq 8.19.2 和 8.20.1 所生成且 Rocq 9.1.1 不生成的闭合集合列表 [ibis_cv_ge@{o}] 和 [ibis_cv_le@{o}] 的拒绝（Paths.v 的 UNIVERSES）：在三者中都可编译的文件无法固定仅由其中两者产生的拒绝。(d) 头文件记录的缺失（没有将路径组件与连通组件进行比较，没有 [Untruncate] 的无公理元素，仅在两点形式下的区间连通性）：缺失没有命令。(e) builder-comp 的 E1 如原先所写（标签）。

结尾的守卫块列出了三个目标的二百五十六个常量，因此重命名会破坏此文件：Adjunction/Continuity/Equalizer.v 中的两个，Instance/Top/Components.v 中的一百二十八个，以及 Instance/Top/Components/Paths.v 中的一百二十六个。它们正是 [Print Module] 为每个目标提供的条目，它们之间有四十二个 [Program] 义务，以及这个唯一归纳类型 [zig_pt] 的三个构造函数，[Print Module] 在其类型下列出了这些构造函数；没有记录被声明，因此没有可添加的 [Build_] 构造函数。每个都是完全限定的书写方式，以便作用域内没有短名称可以替代它。修正 (#1349)：squash 等价类的四个常量 [squash_rel]、[squash_sym]、[squash_trans] 和 [SquashSetoid]，从 Instance/Top/Components.v 移动到 Instance/Sets/Propositional/Full.v，Components.v 现在需要它们，并且在那里的守卫以其名称命名，在 Components.v 之后的一组中：Components.v 中共有一百二十四个（其 [Print Module] 条目，包括三个构造函数）和 Full.v 中的四个，仍然是二百五十六行。[unsquash_Untruncate] 和 [Untruncate_unsquash] 保留在 Components.v 中，现在从 Full.v 的 [untr_of_choice] 和 [choice_of_untr] 派生，并且 [PSetsSub] 和 [PSets] 按定义是 Full.v 的 [PropSets_sub] 和 [PropSets]。
*)

Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lqa.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyReals.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyRealsMult.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyAbs.
Require Import Coq.Reals.Cauchy.ConstructiveRcomplete.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Adjunction.Continuity.Equalizer.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Subcategory.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Complete.
Require Import Category.Instance.Top.Cocomplete.
Require Import Category.Instance.Top.Separation.
Require Category.Theory.Concrete.
Require Import Coq.Arith.PeanoNat.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Top.Components.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Instance.Top.Subspace.
Require Import Category.Instance.Top.Circle.
Require Import Category.Instance.Top.Components.Paths.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.
Require Import Category.Functor.Hom.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

Open Scope category_scope.

(** ** Instrument: the refutation keyword is live / ** 工具：反驳关键词是实时的 *)

(* The instrument / 乐器 *)
Fail Check p462_absent_name.

(** ** Instance/Top/Components.v, ENCODING: the Type-valued [Top] / ** 实例/顶层/组件.v，编码：类型值 [Top] *)

(*
CONTROL: a functor out of [Top@{h o}] into the [Sets] one universe up,
   and an [Adjunction] record between them.

--------
CONTROL：一个从 [Top@{h o}] 到 [Sets] 的函子，向上一个宇宙，
以及它们之间的一个 [Adjunction] 记录。
*)
Definition p462_top_to_sets_up@{h o so +} (C : Top@{h o} ⟶ Sets@{h so}) :
  True := I.

Definition p462_top_adj_up@{h o so +} (C : Top@{h o} ⟶ Sets@{h so})
  (D : Sets@{h so} ⟶ Top@{h o}) (A : C ⊣ D) : True := I.

(* N1 *)
Fail Definition p462_top_to_sets@{h o so +}
  (C : Top@{h o} ⟶ Sets@{o so}) : True := I.

(* N2 *)
Fail Definition p462_top_adj_discrete@{h o so +}
  (C : Top@{h o} ⟶ Sets@{h so}) (A : C ⊣ Top_Discrete) : True := I.

(*
CONTROL: the component relation over [Top], Prop-valued, is formable
   under the closed universe list of the points' universe alone.

--------
控制：[Top] 上的组件关系，属性值类型，在仅在点的宇宙闭合列表下是可形成的。
*)
Definition p462_tconnsub@{o} (X : TopSpace@{o}) (W : X → Prop) : Prop :=
  ∀ φ : X → Prop,
    (∀ z, W z → ex (fun O : X → Type@{o} =>
        inhabited (IsOpen X O) /\ inhabited (O z) /\
        ∀ w, W w → inhabited (O w) → (φ w <-> φ z))) →
    ∀ a b, W a → W b → φ a → φ b.

Definition tcomp_rel_prop@{o} (X : TopSpace@{o}) (x y : X) : Prop :=
  ex (fun W : X → Prop => p462_tconnsub X W /\ W x /\ W y).

(* CONTROL: the Type-valued forms, one universe up. / 控制：类型值形式，向上的一个宇宙。 *)
Definition p462_tcomp_rel_sigma_up@{o h | o < h +} (X : TopSpace@{o})
  (x y : X) : Type@{h} :=
  { W : X → Type@{o} & (W x * W y)%type }.

Definition p462_tcomp_rel_forall_up@{o h | o < h +} (X : TopSpace@{o})
  (x y : X) : Type@{h} :=
  ∀ U : X → Type@{o}, IsOpen X U → U x → U y.

Definition p462_tconnected_up@{o h | o < h +} (X : TopSpace@{o})
  (W : X → Type@{o}) : Type@{h} :=
  ∀ (S : SetoidObject@{o o}) (g : X → S), ∀ a b, W a → W b → g a ≈ g b.

(* N3 *)
Fail Definition p462_tcomp_rel_sigma@{o} (X : TopSpace@{o}) (x y : X) :
  Type@{o} :=
  { W : X → Type@{o} & (W x * W y)%type }.

(* N4 *)
Fail Definition p462_tcomp_rel_forall@{o} (X : TopSpace@{o}) (x y : X) :
  Type@{o} :=
  ∀ U : X → Type@{o}, IsOpen X U → U x → U y.

(* N5 *)
Fail Definition p462_tconnected@{o} (X : TopSpace@{o}) (W : X → Type@{o}) :
  Type@{o} :=
  ∀ (S : SetoidObject@{o o}) (g : X → S), ∀ a b, W a → W b → g a ≈ g b.

(** ** Instance/Top/Components.v, MAC LANE'S SET: the propositional sets / ** 实例/顶层/组件.v，麦克莱恩的集合：命题集合 *)

(* N6 *)
Fail Definition p462_comp_rel_witness@{o} (X : PTop@{o}) (x y : X)
  (H : comp_rel X x y) :
  { W : X → Prop & (PConnectedSub X W * W x * W y)%type } :=
  match H with ex_intro _ W (conj HW (conj wx wy)) => existT _ W (HW, wx, wy)
  end.

(* N7 *)
Fail Definition p462_transpose_inh@{o} (X : PTop@{o})
  (S : SetoidObject@{o o}) (g : PMor@{o} X (PDiscrete S)) (x y : X)
  (HR : inhabited (pmap g x ≈ pmap g y)) : pmap g x ≈ pmap g y :=
  match HR with inhabits h => h end.

(*
CONTROL: through a [PropEquiv] of the target the truncation is
   eliminated, and the transposition respects components.

--------
控制：通过目标的 [PropEquiv]，截断被消除，并且置换遵循组件。
*)
Definition p462_transpose_pe@{o} (X : PTop@{o}) (S : SetoidObject@{o o})
  (P : PropEquiv@{o o} (is_setoid S)) (g : PMor@{o} X (PDiscrete S))
  (x y : X) (HR : inhabited (pmap g x ≈ pmap g y)) : pmap g x ≈ pmap g y :=
  @pequiv_elim_inhabited _ _ P _ _ HR.

Definition p462_comp_respect@{o} (X : PTop@{o}) (S : SetoidObject@{o o})
  (P : PropEquiv@{o o} (is_setoid S)) (g : PMor@{o} X (PDiscrete S))
  (x y : X) : comp_rel X x y → pmap g x ≈ pmap g y := comp_respect X S P g x y.

(*
CONTROL: into all of [Sets], an adjunction makes [Untruncate] merely
   true, and [Untruncate] gives one.

--------
控制：在整个 [Sets] 中，一个附加使 [Untruncate] 仅仅为真，并且 [Untruncate] 给出一个。
*)
Definition p462_unsquash@{o so ua ub | o < so, o < ua +}
  (C' : Lconn@{o so} ⟶ Sets@{o so})
  (A : @Adjunction@{so o o so o o o o ua o ub} Sets@{o so} Lconn@{o so}
         C' LDisc@{o so}) : inhabited Untruncate@{o} :=
  components_on_all_Sets_Untruncate C' A.

Definition p462_unsquash_principle@{o so ua ub | o < so, o < ua +}
  (C' : Lconn@{o so} ⟶ Sets@{o so})
  (A : @Adjunction@{so o o so o o o o ua o ub} Sets@{o so} Lconn@{o so}
         C' LDisc@{o so}) : inhabited (∀ Q : Type@{o}, inhabited Q → Q) :=
  components_on_all_Sets_unsquashes C' A.

Definition p462_adj_Sets@{o so | o < so +} (U : Untruncate@{o}) :
  components_functor_Sets@{o so} ⊣ LDisc@{o so} :=
  components_left_adjoint_discrete_Sets U.

(*
CONTROL: [PSetsSub]'s object predicate placed at the points' universe
   is formable, with [Set < o] in its block; at the pin, at [so].

--------
控制：[PSetsSub] 的对象谓词置于点的宇宙中是可形成的，块中有 [Set < o]；在引脚处，在 [so]。
*)
Definition p462_psets_sub_at_o@{o so | o < so +} :
  Subcategory@{so o o o} Sets@{o so} :=
  @Build_Subcategory@{so o o o} Sets@{o so}
    (fun S : SetoidObject@{o o} => PropEquivObj S)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition p462_psets_sub_Set@{so | Set < so +} := PSetsSub@{Set so}.

(* N8 *)
Fail Definition p462_psets_sub_o_Set@{so | Set < so +} :=
  p462_psets_sub_at_o@{Set so}.

(** ** Adjunction/Continuity/Equalizer.v: why the proof is direct / ** Adjunction/Continuity/Equalizer.v：为什么证明是直接的 *)

Section Pair.

Context {C D : Category} (U : C ⟶ D) {x y : C} (f g : x ~> y).

(* CONTROL: the two diagrams agree on objects, at [eq_refl]. / 控制：两个图表在 [eq_refl] 上对对象达成一致。 *)
Example p462_pair_obj_X :
  fobj[U ◯ APair f g] ParX = fobj[APair (fmap[U] f) (fmap[U] g)] ParX
  := eq_refl.

Example p462_pair_obj_Y :
  fobj[U ◯ APair f g] ParY = fobj[APair (fmap[U] f) (fmap[U] g)] ParY
  := eq_refl.

(* N9 *)
Fail Example p462_pair : U ◯ APair f g = APair (fmap[U] f) (fmap[U] g)
  := eq_refl.

End Pair.

(* CONTROL: right adjoints preserve equalizers, and the refutation. / 控制：右伴随保持等化子，以及反驳。 *)
Definition p462_rapl_equalizers@{co do h +} {C : Category@{co h h}}
  {D : Category@{do h h}} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) :
  PreservesEqualizers U := right_adjoint_PreservesEqualizers A.

(** ** Instance/Top/Components.v: the adjunction, at [eq_refl] / ** Instance/Top/Components.v：在 [eq_refl] 的伴随 *)

(* CONTROL: both transposes and the unit are the identity on points. / 控制：转置和单位在点上都是恒等映射。 *)
Example p462_to_points@{o so | o < so +} (X : Lconn@{o so})
  (S : PSets@{o so}) (h : components_functor@{o so} X ~{PSets@{o so}}~> S)
  (x : pt_carrier (`1 X)) :
  pmap (`1 (to (@adj _ _ _ _ components_left_adjoint_discrete@{o so} X S) h))
    x = `1 h x := eq_refl.

Example p462_from_points@{o so | o < so +} (X : Lconn@{o so})
  (S : PSets@{o so}) (g : X ~{Lconn@{o so}}~> PSetsDisc@{o so} S)
  (x : pt_carrier (`1 X)) :
  `1 (from (@adj _ _ _ _ components_left_adjoint_discrete@{o so} X S) g) x
    = pmap (`1 g) x := eq_refl.

Example p462_unit_points@{o so | o < so +} (X : Lconn@{o so})
  (x : pt_carrier (`1 X)) :
  pmap (`1 (@unit _ _ _ _ components_left_adjoint_discrete@{o so} X)) x = x
  := eq_refl.

Example p462_Sets_to_points@{o so | o < so +} (U : Untruncate@{o})
  (X : Lconn@{o so}) (S : Sets@{o so})
  (h : components_functor_Sets@{o so} X ~{Sets@{o so}}~> S)
  (x : pt_carrier (`1 X)) :
  pmap (`1 (to (@adj _ _ _ _
                 (components_left_adjoint_discrete_Sets@{o so} U) X S) h)) x
    = h x := eq_refl.

Example p462_Sets_from_points@{o so | o < so +} (U : Untruncate@{o})
  (X : Lconn@{o so}) (S : Sets@{o so})
  (g : X ~{Lconn@{o so}}~> LDisc@{o so} S) (x : pt_carrier (`1 X)) :
  from (@adj _ _ _ _ (components_left_adjoint_discrete_Sets@{o so} U) X S)
    g x = pmap (`1 g) x := eq_refl.

(* CONTROL: D is [PDisc] on objects and arrows, and C is [comp_rel]. / 控制：D 是对象和箭头上的 [PDisc]，C 是 [comp_rel]。 *)
Example p462_LDisc_obj@{o so | o < so +} (S : Sets@{o so}) :
  `1 (fobj[LDisc@{o so}] S) = fobj[PDisc@{o so}] S := eq_refl.

Example p462_components_equiv@{o so | o < so +} (X : Lconn@{o so})
  (x y : pt_carrier (`1 X)) :
  @equiv _ (is_setoid (`1 (fobj[components_functor@{o so}] X))) x y
    = comp_rel (`1 X) x y := eq_refl.

(**
** Instance/Top/Components.v: the concrete equalizer, and the
    non-existence statements

--------
** Instance/Top/Components.v：具体的均衡器，以及不存在声明
*)

(*
CONTROL: the fork on the three-point space is an equalizer in [Lconn],
   and C does not preserve it.

--------
控制：三点空间上的叉子在[Lconn]中是一个均衡器，而C不能保持它。
*)
Definition p462_zig_equalizer@{o so | o < so +} :
  @IsEqualizer Lconn@{o so} LZig@{o so} LTwoIndisc@{o so}
    zig_f@{o so} zig_g@{o so} LBool@{o so} zig_e@{o so} :=
  Lconn_zig_equalizer.

Definition p462_zig_not_preserved@{o so | o < so +} :
  @IsEqualizer PSets@{o so} _ _
    (fmap[components_functor@{o so}] zig_f@{o so})
    (fmap[components_functor@{o so}] zig_g@{o so})
    (components_functor@{o so} LBool@{o so})
    (fmap[components_functor@{o so}] zig_e@{o so}) → False :=
  components_zig_not_preserved.

(* CONTROL: the refutations, restated. / 控制：反驳，重述。 *)
Definition p462_no_left_adjoint@{o so u u0 | o < so, o < u +}
  (L : PSets@{o so} ⟶ Lconn@{o so})
  (B : @Adjunction@{so o o so o o o o u o u0} Lconn@{o so} PSets@{o so}
         L components_functor@{o so}) : False :=
  components_no_left_adjoint L B.

Definition p462_any_left_adjoint@{o so ua ub u u0 +| o < so, o < ua,
    o < ub +}
  (C : Lconn@{o so} ⟶ PSets@{o so})
  (A : @Adjunction@{so o o so o o o o ua o u} PSets@{o so} Lconn@{o so}
         C PSetsDisc@{o so})
  (L : PSets@{o so} ⟶ Lconn@{o so})
  (B : @Adjunction@{so o o so o o o o ub o u0} Lconn@{o so} PSets@{o so}
         L C) : False :=
  discrete_left_adjoint_no_left_adjoint C A L B.

Definition p462_no_left_on_PTop@{o so u u0 | o < so, o < u +}
  (C' : PTopCat@{o so} ⟶ PSets@{o so})
  (A : @Adjunction@{so o o so o o o o u o u0} PSets@{o so} PTopCat@{o so}
         C' PSetsDiscTop@{o so}) : False :=
  discrete_no_left_adjoint_on_PTop C' A.

Definition p462_PDisc_no_left@{o so u u0 | o < so, o < u +}
  (C' : PTopCat@{o so} ⟶ Sets@{o so})
  (A : @Adjunction@{so o o so o o o o u o u0} Sets@{o so} PTopCat@{o so}
         C' PDisc@{o so}) : False :=
  PDisc_no_left_adjoint C' A.

(* CONTROL: the points may be in [Set]: the ten theorems at [o := Set]. / 控制：这些点可能在 [Set]：[o := Set] 的十个定理中。 *)
Definition p462_adj_at_Set@{so | Set < so +} :=
  components_left_adjoint_discrete@{Set so}.

Definition p462_adj_Sets_at_Set@{so | Set < so +} :=
  components_left_adjoint_discrete_Sets@{Set so}.

Definition p462_no_left_at_Set@{so u u0 | Set < so, Set < u +} :=
  components_no_left_adjoint@{Set so u u0}.

Definition p462_any_left_at_Set@{so ua ub u u0 | Set < so, Set < ua,
    Set < ub +} :=
  discrete_left_adjoint_no_left_adjoint@{Set so ua ub u u0}.

Definition p462_unsquash_principle_at_Set@{so u u0 | Set < so,
    Set < u +} :=
  components_on_all_Sets_unsquashes@{Set so u u0}.

Definition p462_unsquash_at_Set@{so u u0 | Set < so, Set < u +} :=
  components_on_all_Sets_Untruncate@{Set so u u0}.

Definition p462_ptop_at_Set@{so u u0 | Set < so, Set < u +} :=
  discrete_no_left_adjoint_on_PTop@{Set so u u0}.

Definition p462_pdisc_at_Set@{so u u0 | Set < so, Set < u +} :=
  PDisc_no_left_adjoint@{Set so u u0}.

Definition p462_zig_at_Set@{so | Set < so +} :=
  components_zig_not_preserved@{Set so}.

Definition p462_swap_at_Set@{so | Set < so +} :=
  components_swap_not_preserved@{Set so}.

(** ** Instance/Top/Components/Paths.v: π₀ = colim ∘ P / ** Instance/Top/Components/Paths.v: π₀ = colim ∘ P *)

(*
CONTROL: the arrow part of π₀ IS the colimit functor's, and on
   representatives it is postcomposition.

--------
控制：π₀ 的箭头部分就是余极限函子，并且在代表元上它是后合成。
*)
Example p462_pi0_fmap@{o so p f | o < so, p <= o, o < f +}
  {X Y : PTop@{o}} (h : PMor@{o} X Y) :
  fmap[PPi0@{o so p f}] h
    = Colim_map PathColim@{o so p} (PPathPair_map@{o so p} h) := eq_refl.

Example p462_pi0_fmap_point@{o so p f | o < so, p <= o, o < f +}
  {X Y : PTop@{o}} (h : PMor@{o} X Y) (x : PMor@{o} PPoint@{o} X) :
  fmap[PPi0@{o so p f}] h (existT _ ParY x) = existT _ ParY (pcompose h x)
  := eq_refl.

(*
CONTROL: the identity law, up to [≈], and the underlying functions,
   at [eq_refl].

--------
控制：同一律，直到 [≈]，以及底层函数，位于 [eq_refl]。
*)
Definition p462_pi0_id@{o so p f | o < so, p <= o, o < f +} (X : PTop@{o})
  (x : PMor@{o} PPoint@{o} X) :
  fmap[PPi0@{o so p f}] (pid X) (existT _ ParY x) ≈ existT _ ParY x :=
  @fmap_id _ _ PPi0@{o so p f} X (existT _ ParY x).

Example p462_id_fun@{o} (X : PTop@{o}) (x : PMor@{o} PPoint@{o} X) :
  (fun u => pmap (pcompose (pid X) x) u) = (fun u => pmap x u) := eq_refl.

(* N10 *)
Example p462_pi0_id_point@{o so p f | o < so, p <= o, o < f +}
  (X : PTop@{o}) (x : PMor@{o} PPoint@{o} X) :
  fmap[PPi0@{o so p f}] (pid X) (existT _ ParY x) = existT _ ParY x
  := eq_refl.

(* N11 *)
Example p462_id_setoid_map@{o} (X : PTop@{o})
  (x : PMor@{o} PPoint@{o} X) : pmap (pcompose (pid X) x) = pmap x
  := eq_refl.

(*
CONTROL: the endpoint pair as a diagram in [PTopCat^op], and the
   Yoneda embedding of [PTopCat].

--------
控制：[PTopCat^op] 中作为图的端点对，以及 [PTopCat] 的Yoneda嵌入。
*)
Definition p462_iota@{o so +| o < so +} : Parallel ⟶ PTopCat@{o so}^op :=
  @APair (PTopCat@{o so}^op) PInterval@{o} PPoint@{o}
    ival_end0@{o} ival_end1@{o}.

Definition p462_yoneda@{o so +| o < so +} := Curried_CoHom PTopCat@{o so}.

(* N12 *)
Fail Definition p462_P_derived@{o so +| o < so +} :=
  Induced p462_iota ◯ Curried_CoHom PTopCat@{o so}.

(*
CONTROL: the interval is connected in Instance/Top/Components.v's
   two-point form; π₀ of the interval and of [PBool].

--------
控制：该区间在 Instance/Top/Components.v 的两点形式中连接；该区间和 [PBool] 的 π₀。
*)
Definition p462_interval_connected@{o} : PConnectedBool PInterval@{o} :=
  interval_PConnectedBool.

Definition p462_pi0_interval@{o so p f | o < so, p <= o, o < f +} :
  fobj[PPi0@{o so p f}] PInterval@{o} ≅[Sets@{o so}] unit_setoid_object@{o o}
  := PPi0_PInterval_iso.

Definition p462_pi0_bool@{o so p f | o < so, p <= o, o < f +} :
  fobj[PPi0@{o so p f}] PBool@{o} ≅[Sets@{o so}] bool_setoid_object@{o o}
  := PPi0_PBool_iso.

(** ** Closure: a readback, not a refutation / ** 结论：一种复述，而不是反驳 *)

Print Assumptions right_adjoint_PreservesEqualizers.
Print Assumptions components_functor.
Print Assumptions components_left_adjoint_discrete.
Print Assumptions components_no_left_adjoint.
Print Assumptions components_left_adjoint_discrete_Sets.
Print Assumptions PPi0.

(** ** Guard: the constants of the three targets / ** 守卫：三个目标的常量 *)

(* Adjunction/Continuity/Equalizer.v: 2 names. / Adjunction/Continuity/Equalizer.v：2 个名称。 *)
Check Category.Adjunction.Continuity.Equalizer.not_PreservesEqualizers_no_left_adjoint.
Check Category.Adjunction.Continuity.Equalizer.right_adjoint_PreservesEqualizers.

(*
Instance/Top/Components.v: 125 names and the constructors of [zig_pt].
   CORRECTION (#1349): 121 names now; the squash setoid's four follow the
   group, by their new names.

--------
Instance/Top/Components.v：[zig_pt] 的 125 个名称及构造函数。
   修正 (#1349)：现在是 121 个名称；压缩集合的四个名称按新的名称跟随该组。
*)
Check Category.Instance.Top.Components.adj_from_points.
Check Category.Instance.Top.Components.adj_Sets_from_points.
Check Category.Instance.Top.Components.adj_Sets_to_points.
Check Category.Instance.Top.Components.adj_to_points.
Check Category.Instance.Top.Components.comp_adj_iso.
Check Category.Instance.Top.Components.comp_adj_iso_obligation_1.
Check Category.Instance.Top.Components.comp_adj_iso_obligation_2.
Check Category.Instance.Top.Components.comp_adj_iso_obligation_3.
Check Category.Instance.Top.Components.comp_adj_iso_obligation_4.
Check Category.Instance.Top.Components.comp_adj_iso_U.
Check Category.Instance.Top.Components.comp_adj_iso_U_obligation_1.
Check Category.Instance.Top.Components.comp_adj_iso_U_obligation_2.
Check Category.Instance.Top.Components.comp_adj_iso_U_obligation_3.
Check Category.Instance.Top.Components.comp_adj_iso_U_obligation_4.
Check Category.Instance.Top.Components.comp_cont.
Check Category.Instance.Top.Components.comp_PropEquiv.
Check Category.Instance.Top.Components.comp_rel.
Check Category.Instance.Top.Components.comp_rel_map.
Check Category.Instance.Top.Components.comp_rel_of_equiv.
Check Category.Instance.Top.Components.comp_rel_sym.
Check Category.Instance.Top.Components.comp_rel_trans.
Check Category.Instance.Top.Components.comp_respect.
Check Category.Instance.Top.Components.comp_respect_U.
Check Category.Instance.Top.Components.comp_setoid_map.
Check Category.Instance.Top.Components.components_equiv.
Check Category.Instance.Top.Components.components_fmap.
Check Category.Instance.Top.Components.components_functor.
Check Category.Instance.Top.Components.components_functor_Sets.
Check Category.Instance.Top.Components.components_left_adjoint_discrete.
Check Category.Instance.Top.Components.components_left_adjoint_discrete_Sets.
Check Category.Instance.Top.Components.components_no_left_adjoint.
Check Category.Instance.Top.Components.components_obj.
Check Category.Instance.Top.Components.components_on_all_Sets_unsquashes.
Check Category.Instance.Top.Components.components_on_all_Sets_Untruncate.
Check Category.Instance.Top.Components.components_swap_not_preserved.
Check Category.Instance.Top.Components.components_unit_points.
Check Category.Instance.Top.Components.components_zig_not_preserved.
Check Category.Instance.Top.Components.CompSet.
Check Category.Instance.Top.Components.CompSetoid.
Check Category.Instance.Top.Components.CompTop.
Check Category.Instance.Top.Components.CompTop_obligation_1.
Check Category.Instance.Top.Components.CompTop_obligation_2.
Check Category.Instance.Top.Components.CompTop_obligation_3.
Check Category.Instance.Top.Components.connected_bool_constant.
Check Category.Instance.Top.Components.connected_no_separation.
Check Category.Instance.Top.Components.discrete_left_adjoint_no_left_adjoint.
Check Category.Instance.Top.Components.discrete_left_adjoint_not_preserved.
Check Category.Instance.Top.Components.discrete_no_left_adjoint_on_PTop.
Check Category.Instance.Top.Components.empty_set_map.
Check Category.Instance.Top.Components.image_connected.
Check Category.Instance.Top.Components.LBool.
Check Category.Instance.Top.Components.Lconn.
Check Category.Instance.Top.Components.Lconn_Sub.
Check Category.Instance.Top.Components.Lconn_swap_equalizer.
Check Category.Instance.Top.Components.Lconn_zig_equalizer.
Check Category.Instance.Top.Components.LDisc.
Check Category.Instance.Top.Components.LDisc_obligation_1.
Check Category.Instance.Top.Components.LDisc_obligation_2.
Check Category.Instance.Top.Components.LDisc_obligation_3.
Check Category.Instance.Top.Components.LDisc_PDisc_fmap.
Check Category.Instance.Top.Components.LDisc_PDisc_obj.
Check Category.Instance.Top.Components.LEmpty.
Check Category.Instance.Top.Components.locconst_restrict.
Check Category.Instance.Top.Components.LocConstOn.
Check Category.Instance.Top.Components.LTwoIndisc.
Check Category.Instance.Top.Components.LZig.
Check Category.Instance.Top.Components.negb_no_fixpoint.
Check Category.Instance.Top.Components.pbool_two_components.
Check Category.Instance.Top.Components.PConnected.
Check Category.Instance.Top.Components.PConnected_Bool.
Check Category.Instance.Top.Components.PConnected_Sep.
Check Category.Instance.Top.Components.PConnectedBool.
Check Category.Instance.Top.Components.PConnectedSep.
Check Category.Instance.Top.Components.PConnectedSub.
Check Category.Instance.Top.Components.pconv_not_locconn.
Check Category.Instance.Top.Components.pdisc_locconn.
Check Category.Instance.Top.Components.PDisc_no_left_adjoint.
Check Category.Instance.Top.Components.PLocConn.
Check Category.Instance.Top.Components.point_connected.
Check Category.Instance.Top.Components.PSets.
Check Category.Instance.Top.Components.PSetsDisc.
Check Category.Instance.Top.Components.PSetsDisc_obj.
Check Category.Instance.Top.Components.PSetsDiscTop.
Check Category.Instance.Top.Components.PSetsOne.
Check Category.Instance.Top.Components.PSetsSub.
Check Category.Instance.Top.Components.PTop_zig_equalizer.
Check Category.Instance.Top.Components.PTwoIndisc_connected.
Check Category.Instance.Top.Components.PTwoIndisc_PLocConn.
Check Category.Instance.Top.Components.PZig.
Check Category.Instance.Top.Components.PZig_connected.
Check Category.Instance.Top.Components.PZig_one_component.
Check Category.Instance.Top.Components.PZig_PLocConn.
Check Category.Instance.Top.Components.squash_id.
Check Category.Instance.Top.Components.squash_id_cont.
Check Category.Instance.Top.Components.swap_e.
Check Category.Instance.Top.Components.swap_L.
Check Category.Instance.Top.Components.swap_map.
Check Category.Instance.Top.Components.swap_set.
Check Category.Instance.Top.Components.union_connected.
Check Category.Instance.Top.Components.unsquash_choice.
Check Category.Instance.Top.Components.unsquash_Untruncate.
Check Category.Instance.Top.Components.Untruncate_unsquash.
Check Category.Instance.Top.Components.zig_a.
Check Category.Instance.Top.Components.zig_b.
Check Category.Instance.Top.Components.zig_c.
Check Category.Instance.Top.Components.zig_e.
Check Category.Instance.Top.Components.zig_e_fun.
Check Category.Instance.Top.Components.zig_e_map.
Check Category.Instance.Top.Components.zig_e_set.
Check Category.Instance.Top.Components.zig_f.
Check Category.Instance.Top.Components.zig_f_map.
Check Category.Instance.Top.Components.zig_f_set.
Check Category.Instance.Top.Components.zig_g.
Check Category.Instance.Top.Components.zig_g_fun.
Check Category.Instance.Top.Components.zig_g_map.
Check Category.Instance.Top.Components.zig_g_set.
Check Category.Instance.Top.Components.zig_lift_fun.
Check Category.Instance.Top.Components.zig_open.
Check Category.Instance.Top.Components.zig_pt.
Check Category.Instance.Top.Components.zig_pt_ind.
Check Category.Instance.Top.Components.zig_pt_rec.
Check Category.Instance.Top.Components.zig_pt_rect.
Check Category.Instance.Top.Components.zig_pt_sind.
Check Category.Instance.Top.Components.zig_setoid.

(*
Instance/Sets/Propositional/Full.v: the squash setoid's 4 names, moved
   there from Instance/Top/Components.v by #1349.

--------
Instance/Sets/Propositional/Full.v：squash 集合等价类的4个名称，已从 Instance/Top/Components.v 通过 #1349 移动到此处。
*)
Check Category.Instance.Sets.Propositional.Full.squash_rel.
Check Category.Instance.Sets.Propositional.Full.squash_sym.
Check Category.Instance.Sets.Propositional.Full.squash_trans.
Check Category.Instance.Sets.Propositional.Full.SquashSetoid.

(* Instance/Top/Components/Paths.v: 126 names. / Instance/Top/Components/Paths.v: 126 个名称。 *)
Check Category.Instance.Top.Components.Paths.ibis_clamp.
Check Category.Instance.Top.Components.Paths.ibis_clamp_hi.
Check Category.Instance.Top.Components.Paths.ibis_clamp_id.
Check Category.Instance.Top.Components.Paths.ibis_clamp_ival.
Check Category.Instance.Top.Components.Paths.ibis_clamp_lo.
Check Category.Instance.Top.Components.Paths.ibis_contra.
Check Category.Instance.Top.Components.Paths.ibis_cv_ge.
Check Category.Instance.Top.Components.Paths.ibis_cv_le.
Check Category.Instance.Top.Components.Paths.ibis_inv.
Check Category.Instance.Top.Components.Paths.ibis_left_close.
Check Category.Instance.Top.Components.Paths.ibis_lim.
Check Category.Instance.Top.Components.Paths.ibis_lim_cv.
Check Category.Instance.Top.Components.Paths.ibis_lim_ival.
Check Category.Instance.Top.Components.Paths.ibis_lim_pt.
Check Category.Instance.Top.Components.Paths.ibis_nest.
Check Category.Instance.Top.Components.Paths.ibis_pt.
Check Category.Instance.Top.Components.Paths.ibis_q_pos_inv.
Check Category.Instance.Top.Components.Paths.ibis_right_in.
Check Category.Instance.Top.Components.Paths.ibis_seq.
Check Category.Instance.Top.Components.Paths.ibis_seq_cauchy.
Check Category.Instance.Top.Components.Paths.ibis_seq_in.
Check Category.Instance.Top.Components.Paths.ibis_stage.
Check Category.Instance.Top.Components.Paths.ibis_step.
Check Category.Instance.Top.Components.Paths.ibis_val.
Check Category.Instance.Top.Components.Paths.ibis_val_proper.
Check Category.Instance.Top.Components.Paths.ibis_width.
Check Category.Instance.Top.Components.Paths.ibis_width_bound.
Check Category.Instance.Top.Components.Paths.ibis_width_mono.
Check Category.Instance.Top.Components.Paths.ibis_width_pos.
Check Category.Instance.Top.Components.Paths.ibis_width_small.
Check Category.Instance.Top.Components.Paths.interval_bool_constant.
Check Category.Instance.Top.Components.Paths.interval_bool_endpoints.
Check Category.Instance.Top.Components.Paths.interval_PConnectedBool.
Check Category.Instance.Top.Components.Paths.ival_abs_le.
Check Category.Instance.Top.Components.Paths.ival_end0.
Check Category.Instance.Top.Components.Paths.ival_end1.
Check Category.Instance.Top.Components.Paths.ival_incl.
Check Category.Instance.Top.Components.Paths.ival_incl_obligation_1.
Check Category.Instance.Top.Components.Paths.ival_mult_pred.
Check Category.Instance.Top.Components.Paths.ival_one.
Check Category.Instance.Top.Components.Paths.ival_pred.
Check Category.Instance.Top.Components.Paths.ival_pred_0.
Check Category.Instance.Top.Components.Paths.ival_pred_1.
Check Category.Instance.Top.Components.Paths.ival_scale_map.
Check Category.Instance.Top.Components.Paths.ival_scale_map_obligation_1.
Check Category.Instance.Top.Components.Paths.ival_segment.
Check Category.Instance.Top.Components.Paths.ival_segment_0.
Check Category.Instance.Top.Components.Paths.ival_segment_1.
Check Category.Instance.Top.Components.Paths.ival_segment_map.
Check Category.Instance.Top.Components.Paths.ival_zero.
Check Category.Instance.Top.Components.Paths.IvalSetoid.
Check Category.Instance.Top.Components.Paths.IvalSetoid_obligation_1.
Check Category.Instance.Top.Components.Paths.line_scale.
Check Category.Instance.Top.Components.Paths.line_scale_obligation_1.
Check Category.Instance.Top.Components.Paths.ParSets.
Check Category.Instance.Top.Components.Paths.path_at.
Check Category.Instance.Top.Components.Paths.path_at_obligation_1.
Check Category.Instance.Top.Components.Paths.PathColim.
Check Category.Instance.Top.Components.Paths.pbool_at_point.
Check Category.Instance.Top.Components.Paths.pbool_at_point_obligation_1.
Check Category.Instance.Top.Components.Paths.pbool_at_zero.
Check Category.Instance.Top.Components.Paths.pbool_at_zero_obligation_1.
Check Category.Instance.Top.Components.Paths.PHomSetoid.
Check Category.Instance.Top.Components.Paths.pi0_bool_cocone.
Check Category.Instance.Top.Components.Paths.Pi0_PBool_two.
Check Category.Instance.Top.Components.Paths.PInterval.
Check Category.Instance.Top.Components.Paths.pinterval_point_rel.
Check Category.Instance.Top.Components.Paths.pinterval_rel.
Check Category.Instance.Top.Components.Paths.pline_scale.
Check Category.Instance.Top.Components.Paths.pline_scale_cont.
Check Category.Instance.Top.Components.Paths.PPathPair.
Check Category.Instance.Top.Components.Paths.PPathPair_ev0.
Check Category.Instance.Top.Components.Paths.PPathPair_ev1.
Check Category.Instance.Top.Components.Paths.PPathPair_fmap_paths.
Check Category.Instance.Top.Components.Paths.PPathPair_map.
Check Category.Instance.Top.Components.Paths.PPathPair_map_obligation_1.
Check Category.Instance.Top.Components.Paths.PPathPair_map_obligation_2.
Check Category.Instance.Top.Components.Paths.PPathPair_obj.
Check Category.Instance.Top.Components.Paths.PPathPair_obligation_1.
Check Category.Instance.Top.Components.Paths.PPathPair_obligation_2.
Check Category.Instance.Top.Components.Paths.PPathPair_obligation_3.
Check Category.Instance.Top.Components.Paths.PPathPair_paths.
Check Category.Instance.Top.Components.Paths.PPathPair_points.
Check Category.Instance.Top.Components.Paths.PPi0.
Check Category.Instance.Top.Components.Paths.PPi0_carrier.
Check Category.Instance.Top.Components.Paths.PPi0_coeq_iso.
Check Category.Instance.Top.Components.Paths.PPi0_coeq_iso_obligation_1.
Check Category.Instance.Top.Components.Paths.PPi0_coeq_iso_obligation_2.
Check Category.Instance.Top.Components.Paths.PPi0_equiv.
Check Category.Instance.Top.Components.Paths.PPi0_fmap.
Check Category.Instance.Top.Components.Paths.PPi0_fmap_path.
Check Category.Instance.Top.Components.Paths.PPi0_fmap_point.
Check Category.Instance.Top.Components.Paths.PPi0_fobj.
Check Category.Instance.Top.Components.Paths.ppi0_from_coeq.
Check Category.Instance.Top.Components.Paths.ppi0_from_coeq_obligation_1.
Check Category.Instance.Top.Components.Paths.ppi0_from_coeq_point.
Check Category.Instance.Top.Components.Paths.ppi0_from_points.
Check Category.Instance.Top.Components.Paths.ppi0_from_points_at.
Check Category.Instance.Top.Components.Paths.ppi0_from_points_obligation_1.
Check Category.Instance.Top.Components.Paths.PPi0_inj_point.
Check Category.Instance.Top.Components.Paths.PPi0_PBool_iso.
Check Category.Instance.Top.Components.Paths.PPi0_PBool_iso_obligation_1.
Check Category.Instance.Top.Components.Paths.PPi0_PBool_iso_obligation_2.
Check Category.Instance.Top.Components.Paths.PPi0_PBool_iso_obligation_3.
Check Category.Instance.Top.Components.Paths.PPi0_PInterval_iso.
Check Category.Instance.Top.Components.Paths.PPi0_PInterval_iso_obligation_1.
Check Category.Instance.Top.Components.Paths.PPi0_PInterval_iso_obligation_2.
Check Category.Instance.Top.Components.Paths.PPi0_PInterval_iso_obligation_3.
Check Category.Instance.Top.Components.Paths.PPi0_PInterval_iso_obligation_4.
Check Category.Instance.Top.Components.Paths.PPi0_points_iso.
Check Category.Instance.Top.Components.Paths.PPi0_points_iso_obligation_1.
Check Category.Instance.Top.Components.Paths.PPi0_points_iso_obligation_2.
Check Category.Instance.Top.Components.Paths.ppi0_to_coeq.
Check Category.Instance.Top.Components.Paths.ppi0_to_coeq_path.
Check Category.Instance.Top.Components.Paths.ppi0_to_coeq_point.
Check Category.Instance.Top.Components.Paths.ppi0_to_points.
Check Category.Instance.Top.Components.Paths.ppi0_to_points_fun.
Check Category.Instance.Top.Components.Paths.ppi0_to_points_obligation_1.
Check Category.Instance.Top.Components.Paths.ppi0_to_points_point.
Check Category.Instance.Top.Components.Paths.ppi0_to_points_respects.
Check Category.Instance.Top.Components.Paths.ppoint_at.
Check Category.Instance.Top.Components.Paths.ppostcomp.
Check Category.Instance.Top.Components.Paths.ppostcomp_obligation_1.
Check Category.Instance.Top.Components.Paths.pprecomp.
Check Category.Instance.Top.Components.Paths.pprecomp_obligation_1.
Check Category.Instance.Top.Components.Paths.rball_scale.

(*
Added by #469.  Instance/Sets/Propositional/Full.v builds the same
   category as [PSets] and the same subcategory record as [PSetsSub];
   these two controls pin that at [eq_refl].  The [Require] is loaded
   after every other command, so it changes the environment of these two
   controls alone, and it costs this probe one module (Full.v, whose
   closure is otherwise inside Components.v's).  CORRECTION (#1349):
   Components.v now requires Full.v and defines [PSetsSub] and [PSets]
   as [PropSets_sub] and [PropSets], so these two hold by unfolding that
   definition; they are kept as controls of it.  The [Require] now adds
   no module, Full.v being inside Components.v's closure; it brings
   Full.v's short names into scope for these two controls alone.

--------
由 #469 添加。Instance/Sets/Propositional/Full.v 构建了与 [PSets] 相同的类别，以及与 [PSetsSub] 相同的子类别记录；这两个控件在 [eq_refl] 处固定。[Require] 在每个其他命令之后加载，因此它仅改变这两个控件的环境，并且它花费了该探针一个模块（Full.v，其闭包原本在 Components.v 中）。修正 (#1349)：Components.v 现在需要 Full.v 并将 [PSetsSub] 和 [PSets] 定义为 [PropSets_sub] 和 [PropSets]，因此通过展开该定义，这两个控件保持成立；它们作为其控件保留。[Require] 现在不增加任何模块，因为 Full.v 位于 Components.v 的闭包中；它仅将 Full.v 的简短名称引入这两个控件的作用域中。
*)
Require Import Category.Instance.Sets.Propositional.Full.

Example p462_c469_propsets_sub@{o so | o < so +} :
  PropSets_sub@{o so} = PSetsSub@{o so} := eq_refl.

Example p462_c469_propsets@{o so | o < so +} :
  PropSets@{o so} = PSets@{o so} := eq_refl.
