Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Construction.Quotient.
Require Import Category.Adjunction.LeftInverse.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Discrete.Reconstruct.

(**
* Left-adjoint-right-inverses, and Mac Lane's Exercise IV.4.3

    nLab: https://ncatlab.org/nlab/show/adjoint+equivalence
    nLab: https://ncatlab.org/nlab/show/equivalence+of+categories
    nLab: https://ncatlab.org/nlab/show/fully+faithful+functor
    nLab: https://ncatlab.org/nlab/show/essentially+surjective+functor
    nLab: https://ncatlab.org/nlab/show/coreflective+subcategory

    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          GTM 5, Springer 1998, SS IV.4, printed p. 95, Exercise 3.

    Transliterated to ASCII from the page image:

      "3.  If S : A -> C is full, faithful, and surjective on objects
       (each c in C is c = Sa for some a in A), prove that there is an
       adjoint equivalence <T, S; 1, epsilon> : C -> A with unit the
       identity (and thence that T is a left-adjoint-right-inverse
       of S)."

    Under the SS IV.1 convention the first-listed functor of a triple
    C -> A is the LEFT adjoint, so T : C ⟶ A is left adjoint to S, the
    unit 1 : Id[C] ⟹ S ◯ T is the identity, and the counit
    epsilon : T ◯ S ⟹ Id[A] is an isomorphism -- NOT an identity; see
    below.  Exercise 4 on the same page (the left-adjoint-LEFT-inverse
    characterization) is Adjunction/LeftInverse.v, which is CONSUMED here
    and not rebuilt; Exercises 1, 2 and 5 are separate catalog items and
    are cited rather than delivered.

    ** The design crux: "unit the identity" is not an equation

    In this library the unit of [T ⊣ S] at [c] runs [c ~> S (T c)]
    (Theory/Adjunction.v) while [id[c]] runs [c ~> c], so the two live
    in one hom-set only when [S (T c)] and [c] are the same object at
    LEIBNIZ equality.  So surjectivity on objects must carry that equation
    as DATA, and "the unit is the identity" must be stated against the
    identity TRANSPORTED along it.  This is Adjunction/LeftInverse.v's
    situation one variance over, and the same [id_cast] transport kit
    (Construction/Quotient.v) does the work.

    [SurjectiveOnObjects S := ∀ c, { a & S a = c }] is therefore a chosen
    preimage together with its object equation, the exact mirror of
    Adjunction/LeftInverse.v's [InjectiveOnObjects], with the same
    three closure constants -- but note the ASYMMETRY in the cancellation
    lemma: [InjectiveOnObjects_cancel] recovers the INNER factor [F] of an
    injective [G ◯ F], while [SurjectiveOnObjects_cancel] recovers the
    OUTER factor [G] of a surjective one.  No choice principle is
    consumed anywhere: the tree's [∃] is [sigT], so the witness is data.

    [surjective_ESO] repackages it as Theory/Equivalence.v's
    [EssentiallySurjective], the generic form of
    Construction/Grothendieck/RoundTrip.v's [RT_EssSurj]; at an
    [eq_refl] witness -- the shape [RT_EssSurj] is in -- both legs of the
    witnessing isomorphism are [id] on the nose
    ([surjective_ESO_refl_to], [surjective_ESO_refl_from]).

    ** What is delivered, and at what strength

    [LeftAdjointRightInverse S] is the record: a left adjoint
    [lari_left], an adjunction [lari_adj], a family
    [lari_obj c : S (lari_left c) = c], and
    [lari_unit c : unit c ≈ id_cast (eq_sym (lari_obj c))].

    Mac Lane's Exercise 3 is [ff_surjective_adjoint_equivalence], an
    [AdjointEquivalence ff_surjective_left S] (Adjoint.v), with
    [ff_surjective_LARI] the left-adjoint-right-inverse it carries.  The
    left adjoint [T := ff_surjective_left] has object action the chosen
    preimage and arrow action [prefmap] of the conjugate
    [id_cast⁻¹ ∘ f ∘ id_cast]; every functor law is [fmap_inj] followed by
    [fmap_sur], the [ImageFrom] pattern of Adjunction/LeftInverse.v.  The
    adjunction is built DIRECTLY from the hom-set isomorphism through
    [Build_Adjunction'] (Theory/Adjunction.v), which is why the unit
    computes; see the route note below.

    Strengths, measured strict first.  Holding at [eq_refl]:
    [ff_surj_left_obj], [ff_surj_left_map], [ff_surj_to], [ff_surj_from],
    [ff_surj_lari_left], [ff_surj_lari_adj], [ff_surj_equiv_adj],
    [ff_surj_counit_unfold] (the counit IS the [prefmap] of the
    transported identity), and the two comparisons with the alternative
    route below.  Reaching [≈] only: [ff_surj_unit_is], whose residue is
    exhibited at Leibniz equality by [ff_surj_unit_residue] -- the unit is
    [⌊id⌋], so it carries an [fmap[S] id] that no choice of transpose can
    remove, and the strict form is refuted and pinned in
    Test/ProbeStrict377.v.

    ** The two routes, and which one computes

    The alternative route is the one Construction/Subcategory/Dense.v
    takes: [surjective_ESO], then Theory/Equivalence/FullFaithful.v's
    [FF_ESO_Equivalence], then Adjoint.v's
    [Equivalence_to_AdjointEquivalence], then its
    [AdjointEquivalence_swap] to put the correct functor on the left.  It
    is built here as [ff_surj_eso_adjoint_equivalence] and MEASURED
    against the direct one.

    The two left adjoints agree on BOTH actions at [eq_refl]
    ([ff_surj_eso_inverse_obj], [ff_surj_eso_inverse_map]), hence at
    Theory/Functor.v's [Functor_StrictEq_Setoid] with every object
    component [eq_refl] ([ff_surj_eso_inverse_strict]); the whole functor
    RECORDS are not Leibniz-equal, the three law fields being rebuilt.
    But the ADJUNCTIONS are not the same, and the difference is exactly
    what the exercise is about: the alternative route's unit does not
    reduce to the transported identity, and it does not reduce at all --
    it is stuck at [equiv_adj_to EquivalenceOfCategories_sym id], i.e. at
    the [symmetry] taken on Theory/Functor.v's [Functor_Setoid], whose
    [Equivalence] obligation that file closes opaquely --
    a chain confirmed constant by constant (every route constant prints a
    body; [equiv_adj_to] is [equivalence_prefmap], which projects
    [`1 equivalence_unit], and the symmetric equivalence's unit field IS
    that [symmetry]), though no experiment removes that one step and shows
    the term then reducing, so it is not claimed to be the only blocker.
    So the direct route is shipped, and both stuck points are pinned in
    the probe.

    ** What a left-adjoint-right-inverse does NOT give

    Read Exercise 3 in the direction it is stated.  The converse that
    suggests itself -- that [S] having a left-adjoint-right-inverse makes
    [S] full, faithful and surjective on objects -- is TRUE only in its
    third clause, and the other two are refuted here.

    What IS delivered is [lari_left_ff_surjective]: the LEFT adjoint is
    full and faithful ([lari_left_Full], [lari_left_Faithful]) and [S] is
    surjective on objects ([lari_surjective]).  That is the correct
    reading: for [T ⊣ S] an invertible unit makes T fully faithful, and it
    is an invertible COUNIT that would make S fully faithful.  The record
    demands nothing of the counit.  Both halves of that statement are
    already theorems in tree, cited rather than consumed:
    Adjunction/FullFaithful.v's [left_adjoint_fully_faithful_iff_unit_iso]
    and its [right_adjoint_fully_faithful_iff_counit_iso].
    [lari_left_Full] and [lari_left_Faithful] ARE derivable from the first
    in one line ([snd left_adjoint_fully_faithful_iff_unit_iso] at
    [lari_unit_IsIsomorphism], compiled out of tree), so the five lemmas
    here are a deliberate re-derivation on a measurement: requiring that
    file raises this file's closure from 38 modules to 97, where
    [Instance/Coq] was declined for 23.

    The two refutations share one construction: for any [A] with an
    initial object, the erasing functor [erase_pt A : A ⟶ 1] has a
    left-adjoint-right-inverse [erase_LARI], the left adjoint being
    constant at the initial object.  Instantiated at the walking arrow it
    gives [lari_does_not_imply_Full] -- there is no arrow TwoY ~> TwoX
    (Instance/Two.v) while there is one between their images -- and at
    [Sets] it gives [lari_does_not_imply_Faithful], the identity and the
    constant [true] on the two-element setoid being distinct arrows with
    equal images.  The same [Sets] witness gives
    [lari_does_not_imply_AdjointEquivalence]: the counit at that setoid
    is the unique arrow out of the empty setoid ([Sets_Initial],
    Instance/Sets.v), whose inverse would carry [true] into [False].
    [Sets] is chosen over [Coq] on a measurement: both refutations go
    through verbatim over either, and [Instance/Sets] is already in this
    file's closure through [Theory/Adjunction], where [Instance/Coq]
    would add twenty-three modules for two witnesses.  All three are packaged
    over a sigma binding the functor ONCE, since two occurrences of one
    universe-polymorphic constant in a single statement are two instances
    and would relate two categories rather than one.

    So the honest statement of the equivalence is one-directional: full +
    faithful + surjective-on-objects gives a left-adjoint-right-inverse
    ([ff_surjective_LARI]), and the hypothesis "S has a left adjoint" that
    the naive converse would add is REDUNDANT -- the left adjoint is
    constructed, not assumed.

    ** Non-vacuity

    [indiscrete_LARI] and [indiscrete_adjoint_equivalence] instantiate the
    headline at [Erase (Indiscrete bool)] (Reconstruct.v), which is
    full, faithful and surjective on objects without being injective on
    objects: [IndT ttt] is [true] on the nose, so at the other point the
    counit connects [true] to [false], two objects proved distinct by
    [indiscrete_counit_endpoints_differ].  That is why Mac Lane's epsilon
    is an isomorphism and not an identity, and why
    [counit a ≈ id[a]] is not even well-typed in general; it is pinned in
    the probe as a typing negative.

    ** Universes

    [SurjectiveOnObjects@{ao ah ap co ch cp}] is FREE: six binders, and
    its constraint block carries only the bounds [Functor] itself imposes,
    with no equation -- character for character the same five bounds
    [InjectiveOnObjects] carries.  The one difference between the two is
    the SORT: injectivity lands in [Prop], surjectivity in
    [Type@{max(Set,ao,co)}], because the chosen preimage is data.  Its
    three closure constants are not free, exactly as their mirrors are
    not: [SurjectiveOnObjects_Id] carries [cp = ch], which is [Id]'s own,
    and [SurjectiveOnObjects_Compose] and [SurjectiveOnObjects_cancel]
    bind all three categories at ONE hom-and-proof level in the BINDER,
    which is [Compose]'s, with no equation in either block.
    [surjective_ESO], by contrast, identifies both categories' hom and
    proof universes with one another, which is [EssentiallySurjective]'s
    doing.  [LeftAdjointRightInverse@{u u0 u1 u2 u3}] reads
    [A : Category@{u u3 u3}] and [C : Category@{u2 u3 u3}] in the BINDER,
    so hom is identified with proof in both and the two hom universes with
    each other; its block carries no such equation, so reading the block
    alone would report none.  [ff_surjective_left], [ff_surj_adj],
    [ff_surjective_LARI] and [ff_surjective_adjoint_equivalence] carry
    [u0 = u2] in the block (the two categories' hom levels) with both
    OBJECT universes free, and no [Set] anywhere.

    The witness block is a different matter and the restriction is
    disclosed rather than worked around: [erase_LARI] and everything below
    it read [A : Category@{_ Set Set}].  The cause is [_1]'s hom type
    [poly_unit@{h}], pinned at [Set] inside [erase_left], after which both
    hom-setoids of the adjunction's isomorphism must sit in a [Sets] whose
    carrier universe is [Set].  Two repairs were tried and neither works.
    Turning minimization to [Set] off is INERT here -- measured, by
    compiling the file with and without the flag and comparing the printed
    universe instances, which are identical -- so no such flag is set.
    Annotating [erase_left] with explicit universe binders is rejected
    outright, its [Program] obligations then needing universes outside the
    declared list, with or without the flexible-binder marker.  The pin is
    NOT claimed unavoidable, and it costs the three witnesses nothing:
    each is a concrete category, and an existential witness is not
    weakened by a restriction on the class it is drawn from.

    ** Prior art, measured at f16f04e9

    No constant named for surjectivity on objects existed anywhere:
    [rg -n 'surjective on objects|SurjectiveOnObjects'] over [*.v] returns
    prose only (Theory/Lawvere/Sets.v, Theory/Connected/Components.v,
    Construction/Grothendieck/RoundTrip.v,
    Construction/Coproduct/Indexed.v).  Neither was there any
    left-adjoint-right-inverse packaging.  The issue's own line reference
    for [EssentiallySurjective] is stale -- it points into
    Theory/Equivalence.v at the wrong place; its references to
    [FF_ESO_Equivalence] and [Equivalence_to_AdjointEquivalence] are
    right.

    [poly_unit_all_eq] is deliberately NOT called [poly_unit_eq]:
    Instance/StrictCat/Terminal.v has that name for the identical
    statement.

    ** Registration

    Nothing here is registered for instance resolution, following
    Theory/Equivalence.v: a chosen preimage is data, and a
    left-adjoint-right-inverse is a choice of adjoint, always passed
    explicitly at use sites.

    ** NOT delivered

    No dual (CORRECTION (#457): an earlier revision named the dual a
    right-adjoint-left-inverse; under the opposite adjunction it is a
    right-adjoint-right-inverse, which Structure/SlicedInverse.v's
    [RightAdjointRightInverse] now provides, no op-duality between the
    two records being proved; the coreflective reading of the image of
    [T] is still not delivered); no comparison of [LeftAdjointRightInverse] with
    Adjunction/LeftInverse.v's [LeftAdjointLeftInverse] beyond naming the
    pair; no uniqueness statement for the left adjoint; no statement in
    [StrictCat] and no equality of functors [S ◯ T = Id[C]]; no
    identification of the two routes' ADJUNCTIONS at any strength (only
    their left adjoints are compared); no characterization of when a
    left-adjoint-right-inverse upgrades to an adjoint equivalence; and no
    [Reflective]- or [Coreflective]-style subcategory packaging.

--------
* 左伴随右逆，以及麦克莱恩练习 IV.4.3

nLab: https://ncatlab.org/nlab/show/adjoint+equivalence
nLab: https://ncatlab.org/nlab/show/equivalence+of+categories
nLab: https://ncatlab.org/nlab/show/fully+faithful+functor
nLab: https://ncatlab.org/nlab/show/essentially+surjective+functor
nLab: https://ncatlab.org/nlab/show/coreflective+subcategory

书籍：Mac Lane，《为在职数学家准备的范畴》，第2版，GTM 5，Springer 1998，第IV.4节，印刷第95页，习题3。

从页面图像音译为 ASCII：

3. 如果 S : A -> C 是满的、忠实的，并且在对象上是满射的（即对于 C 中的每个 c，存在某个 a ∈ A 使得 c = Sa），证明存在一个伴随等价 <T, S; 1, ε> : C -> A，其单位是恒等映射（从而 T 是 S 的左伴随-右逆）。

根据 SS IV.1 公约，三元组 C -> A 中第一个列出的函子是左伴随，因此 T : C ⟶ A 是 S 的左伴随，单位 1 : Id[C] ⟹ S ◯ T 是恒等映射，而余单位 epsilon : T ◯ S ⟹ Id[A] 是一个同构 —— 不是恒等映射；见下文。同一页上的练习 4（左伴随-左逆-特征）是 Adjunction/LeftInverse.v，它在这里被使用而未重新构建；练习 1、2 和 5 是单独的目录条目，被引用而不是直接提供。

** 设计关键：“单位恒等”不是一个等式

在这个库中，[T ⊣ S] 在 [c] 的单位运行 [c ~> S (T c)]（Theory/Adjunction.v），而 [id[c] 运行 [c ~> c]，因此只有当 [S (T c)] 和 [c] 在 LEIBNIZ 等式下是相同对象时，这两个才存在于同一个同态集中。因此，对对象的满射性必须将该等式作为数据，并且“单位是恒等映射”必须针对沿其传递的恒等映射进行说明。这是 Adjunction/LeftInverse.v 的情况一次变化，而相同的 [id_cast] 运输工具包（Construction/Quotient.v）完成了工作。

因此，[SurjectiveOnObjects S := ∀ c, { a & S a = c }] 是一个选择的原像以及它的对象方程，与 Adjunction/LeftInverse.v 中的 [InjectiveOnObjects] 完全对应，具有相同的三个闭包常数——但注意消去引理中的不对称性：[InjectiveOnObjects_cancel] 恢复一个单射 [G ◯ F] 的内部因子 [F]，而 [SurjectiveOnObjects_cancel] 恢复一个满射的外部因子 [G]。没有选择原则在任何地方被消耗：树的 [∃] 是 [sigT]，所以见证是数据。

[surjective_ESO] 将其重新打包为 Theory/Equivalence.v 的 [EssentiallySurjective]，是 Construction/Grothendieck/RoundTrip.v 的 [RT_EssSurj] 的通用形式；在一个 [eq_refl] 的证据点上——形状 [RT_EssSurj] 所在的地方——见证同构的两条分支都是完全 [id]（[surjective_ESO_refl_to], [surjective_ESO_refl_from]）。

** 交付的是什么，以及其强度是多少

[LeftAdjointRightInverse S] 是记录：一个左伴随 [lari_left]，一个伴随关系 [lari_adj]，一个族 [lari_obj c : S (lari_left c) = c]，以及 [lari_unit c : unit c ≈ id_cast (eq_sym (lari_obj c))]。

Mac Lane 的练习 3 是 [ff_surjective_adjoint_equivalence]，一个 [AdjointEquivalence ff_surjective_left S]（Adjoint.v），其携带的左伴随右逆为 [ff_surjective_LARI]。左伴随 [T := ff_surjective_left] 的对象作用是所选择的原像，箭头作用是伴随的 [id_cast⁻¹ ∘ f ∘ id_cast] 的 [prefmap]；每条函子律都是 [fmap_inj] 后跟 [fmap_sur]，即 Adjunction/LeftInverse.v 的 [ImageFrom] 模式。该伴随直接通过同态集同构构建，经过 [Build_Adjunction']（Theory/Adjunction.v），这就是单元可以计算的原因；参见下面的路径注释。

优点，首先严格衡量。持有 [eq_refl]：
    [ff_surj_left_obj], [ff_surj_left_map], [ff_surj_to], [ff_surj_from],
    [ff_surj_lari_left], [ff_surj_lari_adj], [ff_surj_equiv_adj],
    [ff_surj_counit_unfold]（该余单位是所运输恒等的 [prefmap]），以及下面与替代路线的两次比较。仅达到 [≈]：[ff_surj_unit_is]，其残差在 Leibniz 等式中由 [ff_surj_unit_residue] 展示 —— 单位是 [⌊id⌋]，因此它携带一个 [fmap[S] ID]，任何转置选项都无法消除，并且严格形式在 Test/ProbeStrict377.v 中被驳斥并固定。

** 两条路线，以及哪一条进行计算

替代路线是 Construction/Subcategory/Dense.v 所采取的：先是 [surjective_ESO]，然后是 Theory/Equivalence/FullFaithful.v 的 [FF_ESO_Equivalence]，再然后是 Adjoint.v 的 [Equivalence_to_AdjointEquivalence]，然后是它的 [AdjointEquivalence_swap] 以将正确的函子放到左边。它在这里构建为 [ff_surj_eso_adjoint_equivalence] 并与直接路线进行 MEASURED 对比。

两个左伴随在 [eq_refl] 的两个作用上是一致的
    （[ff_surj_eso_inverse_obj], [ff_surj_eso_inverse_map]），因此在
    Theory/Functor.v 的 [Functor_StrictEq_Setoid] 上对每个对象
    分量 [eq_refl]（[ff_surj_eso_inverse_strict]）；整个函子
    RECORDS 并不是 Leibniz 相等的，三个律域正在重建。但是附加部分（ADJUNCTIONS）并不相同，而差异正是这个练习所涉及的：替代路线的单元不能化简为传递的同一性，并且它根本无法化简——它卡在 [equiv_adj_to EquivalenceOfCategories_sym id]，也就是说。在 [symmetry] 上的 Theory/Functor.v 的 [Functor_Setoid]，被 [Equivalence] 的义务以不透明的方式关闭该文件——一个由常量到常量确认的链条（每个路径常量都会打印一个主体；[equiv_adj_to] 是 [equivalence_prefmap]，它投影 [`1 equivalence_unit]，对称等价的单位域就是 [symmetry]），尽管没有实验移除那一步并显示术语随后简化，因此并不声称它是唯一的阻碍因素。所以直接路径被传送，并且两个卡住的点都被固定在探针中。

** 左伴随右逆不提供的内容

按照题目所示的方向阅读练习 3。自己联想到的逆命题——即 [S] 拥有左伴随右逆时使 [S] 满、忠实且对象上满射——仅在其第三条款中为真，另外两条在这里被否定。

实际交付的是 [lari_left_ff_surjective]：左伴随函数是完整且忠实的 ([lari_left_Full], [lari_left_Faithful])，并且 [S] 对对象是满射的 ([lari_surjective])。这是正确的理解：对于 [T ⊣ S]，可逆单元使 T 完全忠实，而正是可逆余单元会使 S 完全忠实。记录对余单元没有任何要求。该陈述的两部分已经是树中的定理，引用而非消耗：Adjunction/FullFaithful.v 的 [left_adjoint_fully_faithful_iff_unit_iso] 及其 [right_adjoint_fully_faithful_iff_counit_iso]。[lari_left_Full] 和 [lari_left_Faithful] 可以从第一部分一行推导出来（[snd left_adjoint_fully_faithful_iff_unit_iso] 在 [lari_unit_IsIsomorphism]，已从树中编译出来），因此这里的五个引理是基于度量的有意重新推导：要求该文件会将此文件的闭包从 38 个模块提升到 97 个，其中 [Instance/Coq] 被拒绝了 23 次。

这两个反驳共享一个构造：对于任何具有初始对象的 [A]，擦除函子 [erase_pt A : A ⟶ 1] 有一个左伴随-右逆 [erase_LARI]，其中左伴随在初始对象处是恒定的。在步行箭头处实例化时，它给出 [lari_does_not_imply_Full] —— 没有箭头 TwoY ~> TwoX (Instance/Two.v)，而它们的映像之间有一个箭头 —— 在 [Sets] 处，它给出了 [lari_does_not_imply_Faithful]、同一性以及双元素集合上常量 [true]，作为具有相等映像的不同箭头。同一个 [Sets] 证人给出 [lari_does_not_imply_AdjointEquivalence]：该集合等价类上的余单位是空集合等价类（[Sets_Initial]，Instance/Sets.v）唯一的箭头，其逆箭头会将 [true] 转换为 [False]。[Sets] 在测量上被选择胜过 [Coq]：两者的反证都可逐字通过，并且 [Instance/Sets] 已经在通过 [Theory/Adjunction] 的本文件闭包中，其中 [Instance/Coq] 会为两个证人增加二十三个模块。所有三者都被包装在一个 sigma 上，绑定函子 ONCE，因为在单个语句中，一个宇宙多态常量的两个出现是两个实例，并且会关联两个范畴而不是一个。

所以关于等价性的诚实表述是单向的：完全 + 充满 + 对对象满射给出一个左伴随-右逆 ([ff_surjective_LARI])，而幼稚的逆向所添加的假设“S 有左伴随”是多余的——左伴随是构造出来的，而不是假设的。

** 非空性

[indiscrete_LARI] 和 [indiscrete_adjoint_equivalence] 在 [Erase (Indiscrete bool)]（Reconstruct.v）中实例化了标题，它在对象上是完整、忠实且满射的，但在对象上并非单射：[IndT ttt] 精确等于 [true]，所以在另一点上，余单位将 [true] 连接到 [false]，这两个对象已被 [indiscrete_counit_endpoints_differ] 证明是不同的。这就是为什么 Mac Lane 的 ε 是同构而不是恒等式，以及为什么 [counit a ≈ id[a]] 通常甚至不是良类型；它在探针中被固定为类型负。

** 宇宙

[SurjectiveOnObjects@{ao ah ap co ch cp}] 是免费的：六个活页夹，其约束块只包含 [Functor] 自身施加的边界，没有方程——与 [InjectiveOnObjects] 所包含的五个边界逐字符完全相同。两者之间的唯一区别是排序：单射性位于 [Prop]，满射性位于 [Type@{max(Set,ao,co)}]，因为所选择的原像是数据。它的三个闭合常数不是自由的，正如它们的镜像也不是：[SurjectiveOnObjects_Id] 拥有 [cp = ch]，而 [cp = ch] 属于 [Id] 自身，并且 [SurjectiveOnObjects_Compose] 和 [SurjectiveOnObjects_cancel] 在 BINDER 中以一个同态和证明层绑定所有三类，这属于 [Compose]，两块中都没有方程。相比之下，[surjective_ESO] 将两个范畴的同态和证明宇宙相互识别，这是 [EssentiallySurjective] 的做法。[LeftAdjointRightInverse@{u u0 u1 u2 u3}] 读取 BINDER 中的 [A : Category@{u u3 u3}] 和 [C : Category@{u2 u3 u3}]，因此 hom 在两者中都有证明，并且两个 hom 宇宙互相对应；其区块不包含这样的方程，因此单独读取该区块将报告无。[ff_surjective_left]、[ff_surj_adj]、[ff_surjective_LARI] 和 [ff_surjective_adjoint_equivalence] 在区块中携带 [u0 = u2]（两个范畴的 hom 水平），两个 OBJECT 宇宙都是自由的，并且任何地方都没有 [Set]。

证人块是另一回事，这种限制是披露出来的，而不是被规避：[erase_LARI]及其以下的部分显示为[A : Category@{_ Set Set}]。原因是[_1]的同类类型[poly_unit@{h}]，在[erase_left]内部固定于[Set]，此后伴随同构的两个同类集必须位于一个其承载宇宙是[Set]的[Sets]中。尝试了两种修复方法，但都不起作用。在这里，将最小化设为 [Set] 关闭是无效的——通过编译带有和不带有该标志的文件并比较打印的 universe 实例来测量，它们是相同的——所以没有设置这样的标志。直接用显式的 universe 绑定注释 [erase_left] 会被拒绝，其 [Program] 义务随后需要超出声明列表的 universe，无论是否有灵活绑定标记。这个引脚并不被认为是不可避免的，而且它对三个证人来说没有任何成本：每个都是一个具体的范畴，并且存在性证人不会因为其所属范畴的限制而被削弱。

** 现有技术，测量于 f16f04e9

关于对象的满射性没有任何已存在的常量命名：
    [rg -n 'surjective on objects|SurjectiveOnObjects'] 在 [*.v] 上返回
    仅文本（Theory/Lawvere/Sets.v, Theory/Connected/Components.v,
    Construction/Grothendieck/RoundTrip.v,
    Construction/Coproduct/Indexed.v）。也没有任何左伴随-右逆的封装。该问题自身的行引用
针对 [EssentiallySurjective] 已过时——它指向 Theory/Equivalence.v 的位置不正确；它对 [FF_ESO_Equivalence] 和 [Equivalence_to_AdjointEquivalence] 的引用是正确的。

[poly_unit_all_eq] 故意没有被命名为 [poly_unit_eq]：
    Instance/StrictCat/Terminal.v 使用该名称是因为相同的语句。

** 注册

这里没有任何东西被注册用于实例解析，遵循 Theory/Equivalence.v：一个选定的原像是数据，一个左伴侣右逆是伴侣的选择，总是显式地在使用点传递。

** 未送达

没有双重（更正 (#457)：早期版本将双重称为右伴随-左逆；在对偶伴随下，它是右伴随-右逆，Structure/SlicedInverse.v 的 [RightAdjointRightInverse] 现在提供了这一点，但未证明两个记录之间的操作对偶性；[T] 的像的余反射读取仍未提供）；没有将 [LeftAdjointRightInverse] 与 Adjunction/LeftInverse.v 的 [LeftAdjointLeftInverse] 进行比较，除了命名这对；没有左伴随的唯一性陈述；[StrictCat] 中没有陈述，也没有函子 [S ◯ T = Id[C] 的等式；没有在任何强度下识别两条路径的 ADJUNCTIONS（只比较了它们的左伴随）；没有对左伴随-右逆何时升级为伴随等价的刻画；也没有 [Reflective] 或 [Coreflective] 风格的子范畴封装。
*)

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** ** Surjectivity on objects, as data / ** 对象上的满射性，作为数据 *)

Definition SurjectiveOnObjects@{ao ah ap co ch cp}
  {A : Category@{ao ah ap}} {C : Category@{co ch cp}} (S : A ⟶ C) :=
  ∀ c : C, { a : A & S a = c }.

Definition SurjectiveOnObjects_Id@{co ch cp} {C : Category@{co ch cp}} :
  SurjectiveOnObjects Id[C] :=
  fun c => (c; eq_refl).

Definition SurjectiveOnObjects_Compose {A B C : Category}
  {F : A ⟶ B} {G : B ⟶ C}
  (HG : SurjectiveOnObjects G) (HF : SurjectiveOnObjects F) :
  SurjectiveOnObjects (G ◯ F) :=
  fun c => (`1 (HF (`1 (HG c)));
            eq_trans (f_equal (fobj[G]) (`2 (HF (`1 (HG c)))))
                     (`2 (HG c))).

Definition SurjectiveOnObjects_cancel {A B C : Category}
  {F : A ⟶ B} {G : B ⟶ C} (HGF : SurjectiveOnObjects (G ◯ F)) :
  SurjectiveOnObjects G :=
  fun c => (F (`1 (HGF c)); `2 (HGF c)).

Definition surjective_ESO {A C : Category} {S : A ⟶ C}
  (surj : SurjectiveOnObjects S) : EssentiallySurjective S :=
  @Build_EssentiallySurjective A C S
    (fun c => `1 (surj c))
    (fun c => id_cast_iso (`2 (surj c))).

(*
The chosen preimage survives the repackaging on the nose, and at an
   [eq_refl] witness -- the shape [Construction/Grothendieck/RoundTrip.v]'s
   [RT_EssSurj] is in -- the witnessing isomorphism has [id] for both
   legs.

--------
选定的原像在精确重打包中存活下来，并且在一个 [eq_refl] 见证者处——形状 [Construction/Grothendieck/RoundTrip.v] 的 [RT_EssSurj] 所在之处——见证同构的两个分支都有 [id]。
*)
Example surjective_ESO_obj {A C : Category} {S : A ⟶ C}
  (surj : SurjectiveOnObjects S) (c : C) :
  @eso_obj A C S (surjective_ESO surj) c = `1 (surj c) := eq_refl.

Example surjective_ESO_refl_to {C : Category} (c : C) :
  to (@eso_iso C C Id[C] (surjective_ESO SurjectiveOnObjects_Id) c) = id
  := eq_refl.

Example surjective_ESO_refl_from {C : Category} (c : C) :
  from (@eso_iso C C Id[C] (surjective_ESO SurjectiveOnObjects_Id) c) = id
  := eq_refl.

(** ** Left-adjoint-right-inverses / ** 左伴随-右逆 *)

Record LeftAdjointRightInverse {A C : Category} (S : A ⟶ C) : Type := {
  lari_left : C ⟶ A;
  lari_adj : lari_left ⊣ S;
  lari_obj (c : C) : S (lari_left c) = c;
  lari_unit (c : C) :
    @unit A C lari_left S lari_adj c ≈ id_cast (eq_sym (lari_obj c))
}.

Arguments lari_left {A C S} _.
Arguments lari_adj {A C S} _.
Arguments lari_obj {A C S} _ _.
Arguments lari_unit {A C S} _ _.

(** ** Consequences of having a left-adjoint-right-inverse / ** 具有左伴随右逆的后果 *)

Section Consequences.

Context {A C : Category}.
Context {S : A ⟶ C}.
Context (P : LeftAdjointRightInverse S).

Local Notation T := (lari_left P).
Local Notation e := (lari_obj P).
Local Notation D := (lari_adj P).

Definition lari_unit_iso (c : C) : c ≅ S (T c) := id_cast_iso_sym (e c).

Program Definition lari_unit_IsIsomorphism (c : C) :
  IsIsomorphism (@unit A C T S D c) := {|
  two_sided_inverse := id_cast (e c)
|}.
Next Obligation.
  intros c; rewrite (lari_unit P c); apply id_cast_inv_l.
Qed.
Next Obligation.
  intros c; rewrite (lari_unit P c); apply id_cast_inv_r.
Qed.

Definition lari_surjective : SurjectiveOnObjects S :=
  fun c => (T c; e c).

(*
The forward transpose of an image arrow is the unit followed by the
   arrow itself: [to_adj_nat_l] at the identity.

--------
图像箭头的前向转置是箭头本身之后跟随的单位：在恒等映射下为 [to_adj_nat_l]。
*)
Lemma lari_to_fmap {x y : C} (f : x ~> y) :
  to (@adj A C T S D x (T y)) (fmap[T] f) ≈ @unit A C T S D y ∘ f.
Proof.
  rewrite <- (id_left (fmap[T] f)).
  rewrite (@to_adj_nat_l A C T S D).
  reflexivity.
Qed.

(* The unit is componentwise monic, being a transported identity. / 该单位是分量单射的，因为它是被传递的恒等。 *)
Lemma lari_unit_monic {x y : C} (f g : x ~> y) :
  @unit A C T S D y ∘ f ≈ @unit A C T S D y ∘ g → f ≈ g.
Proof.
  intros Hfg.
  rewrite (lari_unit P y) in Hfg.
  rewrite <- (id_left f), <- (id_left g).
  rewrite <- (id_cast_inv_r (e y)).
  rewrite <- !comp_assoc.
  now rewrite Hfg.
Qed.

(* The forward transpose is injective, being one leg of an isomorphism. / 前向转置是单射的，作为同构的一条腿。 *)
Lemma lari_adj_to_inj {x : C} {a : A} (u v : T x ~> a) :
  to (@adj A C T S D x a) u ≈ to (@adj A C T S D x a) v → u ≈ v.
Proof.
  intros Huv.
  rewrite <- (@to_adj_comp_law A C T S D x a u).
  rewrite <- (@to_adj_comp_law A C T S D x a v).
  now rewrite Huv.
Qed.

Program Definition lari_left_Full : Category.Theory.Functor.Full T := {|
  prefmap := fun x y g =>
    id_cast (e y) ∘ to (@adj A C T S D x (T y)) g
|}.
Next Obligation.
  intros x y g.
  apply lari_adj_to_inj.
  rewrite lari_to_fmap.
  rewrite (lari_unit P y).
  rewrite comp_assoc, id_cast_inv_l, id_left.
  reflexivity.
Qed.

Program Definition lari_left_Faithful : Faithful T := {| fmap_inj := _ |}.
Next Obligation.
  intros x y f g Hfg.
  apply lari_unit_monic.
  rewrite <- !lari_to_fmap.
  now rewrite Hfg.
Qed.

(*
What a left-adjoint-right-inverse of [S] yields: the LEFT adjoint is
   full and faithful, and [S] is surjective on objects.  Nothing here
   asserts that [S] is full or faithful; both are refuted below.

--------
[S]的左伴随-右逆产生的结果是：左伴随是完备且忠实的，并且[S]在对象上是满射的。这里没有任何断言[S]是完备或忠实的；下面将否定两者。
*)
Definition lari_left_ff_surjective :
  (Category.Theory.Functor.Full T * Faithful T) * SurjectiveOnObjects S :=
  ((lari_left_Full, lari_left_Faithful), lari_surjective).

End Consequences.

Arguments lari_unit_iso {A C S} _ _.
Arguments lari_surjective {A C S} _ _.

(** ** A conjugation lemma for the two casts / ** 两个转换的共轭引理 *)

Lemma cast_conj_comp {D : Category} {x y z x' y' z' : D}
  (ex : x' = x) (ey : y' = y) (ez : z' = z) (f : y ~> z) (g : x ~> y) :
  (id_cast (eq_sym ez) ∘ f ∘ id_cast ey)
    ∘ (id_cast (eq_sym ey) ∘ g ∘ id_cast ex)
    ≈ id_cast (eq_sym ez) ∘ (f ∘ g) ∘ id_cast ex.
Proof. destruct ex, ey, ez; cat. Qed.

(** ** Mac Lane's Exercise IV.4.3 / ** 麦克莱恩练习 IV.4.3 *)

Section FFSurjective.

Context {A C : Category}.
Context {S : A ⟶ C}.
Context `{@Category.Theory.Functor.Full A C S}.
Context `{@Faithful A C S}.
Context (surj : SurjectiveOnObjects S).

Definition ff_surj_obj (c : C) : A := `1 (surj c).

Definition ff_surj_eq (c : C) : S (ff_surj_obj c) = c := `2 (surj c).

Definition ff_surj_conj {c c' : C} (f : c ~> c') :
  S (ff_surj_obj c) ~> S (ff_surj_obj c') :=
  id_cast (eq_sym (ff_surj_eq c')) ∘ f ∘ id_cast (ff_surj_eq c).

Program Definition ff_surjective_left : C ⟶ A := {|
  fobj := ff_surj_obj;
  fmap := fun c c' f => prefmap (ff_surj_conj f)
|}.
Next Obligation.
  intros c c' f g Hfg.
  apply fmap_inj.
  rewrite !fmap_sur.
  unfold ff_surj_conj.
  now rewrite Hfg.
Qed.
Next Obligation.
  intros c.
  apply fmap_inj.
  rewrite fmap_sur, fmap_id.
  unfold ff_surj_conj.
  rewrite id_right.
  apply id_cast_inv_l.
Qed.
Next Obligation.
  intros c c' c'' f g.
  apply fmap_inj.
  rewrite fmap_comp, !fmap_sur.
  unfold ff_surj_conj.
  symmetry.
  apply cast_conj_comp.
Qed.

Program Definition ff_surj_hom_iso (c : C) (a : A) :
  @Isomorphism Sets
    {| carrier := @hom A (ff_surjective_left c) a;
       is_setoid := @homset A (ff_surjective_left c) a |}
    {| carrier := @hom C c (S a);
       is_setoid := @homset C c (S a) |} := {|
  to := {| morphism := fun f => fmap[S] f ∘ id_cast (eq_sym (ff_surj_eq c)) |};
  from := {| morphism := fun g => prefmap (g ∘ id_cast (ff_surj_eq c)) |}
|}.
Next Obligation.
  intros c a f g Hfg; simpl in *.
  now rewrite Hfg.
Qed.
Next Obligation.
  intros c a f g Hfg; simpl in *.
  apply fmap_inj.
  rewrite !fmap_sur.
  now rewrite Hfg.
Qed.
Next Obligation.
  intros c a g; simpl in *.
  rewrite fmap_sur.
  rewrite <- comp_assoc, id_cast_inv_r.
  apply id_right.
Qed.
Next Obligation.
  intros c a f; simpl in *.
  apply fmap_inj.
  rewrite fmap_sur.
  rewrite <- comp_assoc, id_cast_inv_l.
  apply id_right.
Qed.

Definition ff_surj_adj : ff_surjective_left ⊣ S.
Proof.
  unshelve eapply (@Build_Adjunction' A C ff_surjective_left S
                     ff_surj_hom_iso).
  - intros x y z f g; simpl.
    rewrite fmap_comp, fmap_sur.
    unfold ff_surj_conj.
    rewrite <- !comp_assoc.
    rewrite id_cast_inv_r, id_right.
    reflexivity.
  - intros x y z f g; simpl.
    rewrite fmap_comp.
    rewrite <- comp_assoc.
    reflexivity.
Defined.

Program Definition ff_surjective_LARI : LeftAdjointRightInverse S := {|
  lari_left := ff_surjective_left;
  lari_adj := ff_surj_adj;
  lari_obj := ff_surj_eq
|}.
Next Obligation.
  intros c.
  unfold unit; simpl.
  rewrite fmap_id, id_left.
  reflexivity.
Qed.

Definition ff_surjective_unit_iso (c : C) :
  IsIsomorphism (@unit A C ff_surjective_left S ff_surj_adj c) :=
  lari_unit_IsIsomorphism ff_surjective_LARI c.

Lemma ff_surj_counit_unfold (a : A) :
  @counit A C ff_surjective_left S ff_surj_adj a
    = prefmap (id[S a] ∘ id_cast (ff_surj_eq (S a))).
Proof. reflexivity. Qed.

Program Definition ff_surjective_counit_iso (a : A) :
  IsIsomorphism (@counit A C ff_surjective_left S ff_surj_adj a) := {|
  two_sided_inverse := prefmap (id_cast (eq_sym (ff_surj_eq (S a))))
|}.
Next Obligation.
  intros a.
  rewrite ff_surj_counit_unfold.
  apply fmap_inj.
  rewrite fmap_comp, !fmap_sur, fmap_id.
  rewrite id_left.
  apply id_cast_inv_r.
Qed.
Next Obligation.
  intros a.
  rewrite ff_surj_counit_unfold.
  apply fmap_inj.
  rewrite fmap_comp, !fmap_sur, fmap_id.
  rewrite id_left.
  apply id_cast_inv_l.
Qed.

Definition ff_surjective_adjoint_equivalence :
  AdjointEquivalence ff_surjective_left S :=
  @Build_AdjointEquivalence C A ff_surjective_left S ff_surj_adj
    ff_surjective_unit_iso ff_surjective_counit_iso.

(** *** Strict readbacks and the one residue / *** 严格复读和唯一残留 *)

Example ff_surj_left_obj (c : C) : ff_surjective_left c = ff_surj_obj c :=
  eq_refl.

Example ff_surj_left_map (c c' : C) (f : c ~> c') :
  fmap[ff_surjective_left] f = prefmap (ff_surj_conj f) := eq_refl.

Example ff_surj_to (c : C) (a : A) (f : ff_surjective_left c ~> a) :
  to (@adj A C ff_surjective_left S ff_surj_adj c a) f
    = fmap[S] f ∘ id_cast (eq_sym (ff_surj_eq c)) := eq_refl.

Example ff_surj_from (c : C) (a : A) (g : c ~> S a) :
  from (@adj A C ff_surjective_left S ff_surj_adj c a) g
    = prefmap (g ∘ id_cast (ff_surj_eq c)) := eq_refl.

(*
The unit is the transported identity only up to [≈]: the residue is a
   [fmap[S] id], exhibited here at Leibniz equality.

--------
该单元仅在 [≈] 之前是被传输的恒等：残基是一个 [fmap[S] id]，在此处展示于莱布尼茨等式。
*)
Example ff_surj_unit_residue (c : C) :
  @unit A C ff_surjective_left S ff_surj_adj c
    = fmap[S] (id[ff_surjective_left c]) ∘ id_cast (eq_sym (ff_surj_eq c))
  := eq_refl.

Definition ff_surj_unit_is (c : C) :
  @unit A C ff_surjective_left S ff_surj_adj c
    ≈ id_cast (eq_sym (ff_surj_eq c)) :=
  lari_unit ff_surjective_LARI c.

Example ff_surj_lari_left : lari_left ff_surjective_LARI = ff_surjective_left
  := eq_refl.

Example ff_surj_lari_adj : lari_adj ff_surjective_LARI = ff_surj_adj
  := eq_refl.

Example ff_surj_equiv_adj :
  @adj_equivalence C A ff_surjective_left S ff_surjective_adjoint_equivalence
    = ff_surj_adj := eq_refl.

(** *** The route through [FF_ESO_Equivalence], measured / *** 通过 [FF_ESO_Equivalence] 的路线，已测量 *)

Definition ff_surj_eso : EssentiallySurjective S := surjective_ESO surj.

Definition ff_surj_eso_equivalence : EquivalenceOfCategories S :=
  @FF_ESO_Equivalence A C S _ _ ff_surj_eso.

Definition ff_surj_eso_adjoint_equivalence :
  AdjointEquivalence (@ff_eso_inverse A C S _ _ ff_surj_eso) S :=
  AdjointEquivalence_swap
    (Equivalence_to_AdjointEquivalence ff_surj_eso_equivalence).

(* Both actions of the two left adjoints agree on the nose. / 两个左伴随的作用完全一致。 *)
Example ff_surj_eso_inverse_obj (c : C) :
  @ff_eso_inverse A C S _ _ ff_surj_eso c = ff_surjective_left c := eq_refl.

Example ff_surj_eso_inverse_map (c c' : C) (f : c ~> c') :
  fmap[@ff_eso_inverse A C S _ _ ff_surj_eso] f
    = fmap[ff_surjective_left] f := eq_refl.

(*
Hence the two left adjoints are equal at [Functor_StrictEq_Setoid], with
   every object component [eq_refl]; the whole functor RECORDS are not
   Leibniz-equal, the three law fields being rebuilt.

--------
因此，在 [Functor_StrictEq_Setoid] 上两个左伴随是相等的，且每个对象分量都是 [eq_refl]；整个函子 RECORDS 并不是莱布尼茨意义上的相等，三个律域正在被重建。
*)
Program Definition ff_surj_eso_inverse_strict :
  @equiv _ (@Functor_StrictEq_Setoid C A)
    (@ff_eso_inverse A C S _ _ ff_surj_eso) ff_surjective_left :=
  (fun _ => eq_refl; _).
Next Obligation. intros x y f; reflexivity. Qed.


End FFSurjective.

(** ** Witnesses / ** 证人 *)

(* Any two parallel arrows of the point are equal: its hom is [poly_unit]. / 点的任意两条平行箭头是相等的：它的同态是 [poly_unit]。 *)
Lemma one_hom_unique {x y : @obj _1} (f g : x ~{_1}~> y) : f ≈ g.
Proof. destruct f, g; reflexivity. Qed.

(*
[_1]'s hom-setoid is [Morphism_equality], i.e. Leibniz equality, and a
   tactic that unfolds [≈] leaves goals in that shape.  [apply] cannot use
   the lemma just above on such a goal: [hom _1] ignores its endpoints, so
   the implicit [y] is not determined by unification.  The endpoint-free
   spelling below is what those goals need.  It is NOT called
   [poly_unit_eq]: that name is taken by Instance/StrictCat/Terminal.v
   for the identical statement, and the print-assumptions target loads many
   modules into one scope, where a shared name audits the wrong constant.

--------
[_1] 的同构集合是 [Morphism_equality]，即莱布尼茨等式，而一个展开 [≈] 的策略会让目标保持这种形式。[apply] 不能在这样的目标上使用上面的引理：[hom _1] 忽略它的端点，因此隐含的 [y] 无法通过统一确定。下面的不带端点的书写形式是这些目标所需要的。它不叫做 [poly_unit_eq]：这个名字被 Instance/StrictCat/Terminal.v 用于相同的陈述，而且 print-assumptions 目标会将许多模块加载到一个作用域中，在那个作用域中，共享的名字会检查错误的常量。
*)
Lemma poly_unit_all_eq (f g : poly_unit) : f = g.
Proof. destruct f, g; reflexivity. Qed.

(** *** The erasing functor of a category with an initial object / *** 具有初始对象的范畴的擦除函子 *)

Program Definition erase_left {A : Category}
  (I : @Initial A) : _1 ⟶ A := {|
  fobj := fun _ => @initial_obj A I;
  fmap := fun _ _ _ => id
|}.
Next Obligation. proper. Qed.
Next Obligation. intros; simpl; rewrite ?id_left; reflexivity. Qed.

Definition erase_pt (A : Category) : A ⟶ _1 := Erase A.

Program Definition erase_hom_iso {A : Category}
  (I : @Initial A) (x : @obj _1) (a : A) :
  @Isomorphism Sets
    {| carrier := @hom A (erase_left I x) a;
       is_setoid := @homset A (erase_left I x) a |}
    {| carrier := @hom _1 x (erase_pt A a);
       is_setoid := @homset _1 x (erase_pt A a) |} := {|
  to := {| morphism := fun _ => ttt |};
  from := {| morphism := fun _ => @zero A I a |}
|}.
Next Obligation.
  try proper; try (intros; simpl);
  first [ apply one_hom_unique | apply poly_unit_all_eq
        | apply zero_unique | reflexivity ].
Qed.
Next Obligation.
  try proper; try (intros; simpl);
  first [ apply one_hom_unique | apply poly_unit_all_eq
        | apply zero_unique | reflexivity ].
Qed.
Next Obligation.
  try proper; try (intros; simpl);
  first [ apply one_hom_unique | apply poly_unit_all_eq
        | apply zero_unique | reflexivity ].
Qed.

Definition erase_adj {A : Category} (I : @Initial A) :
  erase_left I ⊣ erase_pt A.
Proof.
  unshelve eapply (@Build_Adjunction' A _ (erase_left I) (erase_pt A)
                     (erase_hom_iso I)).
  - intros x y z f g; apply one_hom_unique.
  - intros x y z f g; apply one_hom_unique.
Defined.

Definition erase_obj_eq {A : Category} (I : @Initial A) :
  ∀ c, erase_pt A (erase_left I c) = c :=
  fun c => match c with ttt => eq_refl end.

Program Definition erase_LARI {A : Category} (I : @Initial A) :
  LeftAdjointRightInverse (erase_pt A) := {|
  lari_left := erase_left I;
  lari_adj := erase_adj I;
  lari_obj := erase_obj_eq I
|}.
Next Obligation. intros A I c; apply one_hom_unique. Qed.

Example erase_pt_is_Erase (A : Category) : erase_pt A = Erase A := eq_refl.

(** *** The walking arrow: a left-adjoint-right-inverse without fullness / *** 行走的箭头：一个没有满性的左伴右逆 *)

Program Definition Two_Initial : @Initial _2 := {|
  terminal_obj := TwoX;
  one := fun x => match x return TwoX ~{_2}~> x with
                  | TwoX => TwoIdX
                  | TwoY => TwoXY
                  end
|}.
Next Obligation. intros x f g; apply Two_thin. Qed.

Definition two_erase_LARI : LeftAdjointRightInverse (erase_pt _2) :=
  erase_LARI Two_Initial.

Example two_erase_left_TwoY :
  lari_left two_erase_LARI (erase_pt _2 TwoY) = TwoX := eq_refl.

Lemma two_erase_object_moved :
  lari_left two_erase_LARI (erase_pt _2 TwoY) = TwoY → False.
Proof. discriminate. Qed.

Theorem two_erase_not_Full :
  Category.Theory.Functor.Full (Erase _2) → False.
Proof.
  intros F.
  exact (TwoHom_Y_X_absurd (@prefmap _2 _1 (Erase _2) F TwoY TwoX ttt)).
Qed.

(*
Packaged so that BOTH halves speak of one and the same functor: two
   separate occurrences of [erase_pt _2] in one statement would be two
   universe instances, and the pair would then relate two categories
   rather than one.

--------
包装方式使得两个部分都表达同一个函子：在一个语句中两次出现 [erase_pt _2] 将是两个宇宙实例，而这对将因此关联两个范畴而非一个。
*)
Definition lari_does_not_imply_Full :
  { X : Category & { S : X ⟶ _1 &
      LeftAdjointRightInverse S
        * (Category.Theory.Functor.Full S → False) } } :=
  (_2; (erase_pt _2; (two_erase_LARI, two_erase_not_Full))).

(** *** Sets: a left-adjoint-right-inverse without faithfulness / *** 集合：一个没有忠诚性的左伴随-右逆 *)

Definition sets_erase_LARI : LeftAdjointRightInverse (erase_pt Sets) :=
  erase_LARI Sets_Initial.

(*
The two-element setoid under Leibniz equality, and two distinct parallel
   arrows on it.  The lambda domains are annotated and the respectfulness
   certificates written by hand: left to instance search, an unannotated
   record literal resolves its source setoid before meeting the expected
   type (the Theory/Universal/Element.v hazard).

--------
在莱布尼茨等式下的二元素集合，并且其上有两个不同的平行箭头。lambda 域被标注，并且尊重性证书是手写的：留给实例搜索，一个未标注的记录字面量在遇到预期类型之前解析其源集合（Theory/Universal/Element.v 的风险）。
*)
Definition sets_bool_obj : SetoidObject :=
  {| carrier := bool; is_setoid := eq_Setoid bool |}.

Definition sets_bool_id : sets_bool_obj ~{Sets}~> sets_bool_obj :=
  {| morphism := fun b : bool => b;
     proper_morphism := ltac:(intros a b H; exact H) |}.

Definition sets_bool_const_true : sets_bool_obj ~{Sets}~> sets_bool_obj :=
  {| morphism := fun _ : bool => true;
     proper_morphism := ltac:(intros a b H; reflexivity) |}.

Theorem sets_erase_not_Faithful : Faithful (Erase Sets) → False.
Proof.
  intros FF.
  assert (@fmap Sets _1 (Erase Sets) sets_bool_obj sets_bool_obj sets_bool_id
            ≈ @fmap Sets _1 (Erase Sets) sets_bool_obj sets_bool_obj
                sets_bool_const_true)
    as Hf by reflexivity.
  pose proof (@fmap_inj Sets _1 (Erase Sets) FF sets_bool_obj sets_bool_obj
                sets_bool_id sets_bool_const_true Hf false) as Hx.
  simpl in Hx.
  discriminate.
Qed.

Definition lari_does_not_imply_Faithful :
  { X : Category & { S : X ⟶ _1 &
      LeftAdjointRightInverse S * (Faithful S → False) } } :=
  (Sets; (erase_pt Sets; (sets_erase_LARI, sets_erase_not_Faithful))).

Theorem sets_erase_counit_not_iso :
  IsIsomorphism (@counit Sets _ (lari_left sets_erase_LARI) (erase_pt Sets)
                   (lari_adj sets_erase_LARI) sets_bool_obj) → False.
Proof. intros [g _ _]; destruct (g true). Qed.

Definition lari_does_not_imply_AdjointEquivalence :
  { X : Category & { S : X ⟶ _1 & { P : LeftAdjointRightInverse S &
      { a : X & IsIsomorphism
                  (@counit X _1 (lari_left P) S (lari_adj P) a) → False } } } }
  := (Sets; (erase_pt Sets; (sets_erase_LARI;
       (sets_bool_obj; sets_erase_counit_not_iso)))).

(** *** A non-degenerate instance of the exercise / *** 该练习的非退化实例 *)

Program Definition indiscrete_erase_Full :
  Category.Theory.Functor.Full (Erase (Indiscrete bool)) := {|
  prefmap := fun x y g => tt
|}.
Next Obligation. intros x y g; apply one_hom_unique. Qed.

Program Definition indiscrete_erase_Faithful :
  Faithful (Erase (Indiscrete bool)) := {| fmap_inj := _ |}.
Next Obligation. intros x y f g Hfg; destruct f, g; reflexivity. Qed.

Definition indiscrete_erase_surjective :
  SurjectiveOnObjects (Erase (Indiscrete bool)) :=
  fun c => (true; match c with ttt => eq_refl end).

Definition IndT : _1 ⟶ Indiscrete bool :=
  @ff_surjective_left (Indiscrete bool) _1 (Erase (Indiscrete bool))
    indiscrete_erase_Full indiscrete_erase_Faithful
    indiscrete_erase_surjective.

Definition indiscrete_LARI :
  LeftAdjointRightInverse (Erase (Indiscrete bool)) :=
  @ff_surjective_LARI (Indiscrete bool) _1 (Erase (Indiscrete bool))
    indiscrete_erase_Full indiscrete_erase_Faithful
    indiscrete_erase_surjective.

Definition indiscrete_adjoint_equivalence :
  AdjointEquivalence IndT (Erase (Indiscrete bool)) :=
  @ff_surjective_adjoint_equivalence (Indiscrete bool) _1
    (Erase (Indiscrete bool)) indiscrete_erase_Full
    indiscrete_erase_Faithful indiscrete_erase_surjective.

Example indiscrete_left_obj : IndT ttt = true := eq_refl.

Lemma indiscrete_counit_endpoints_differ :
  IndT (Erase (Indiscrete bool) false) = false → False.
Proof. discriminate. Qed.

