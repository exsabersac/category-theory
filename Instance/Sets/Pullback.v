Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Regular.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.

Generalizable All Variables.

(** * Pullbacks in [Sets] / * [Sets]中的回调 *)

(*
 nLab:      https://ncatlab.org/nlab/show/pullback
 nLab:      https://ncatlab.org/nlab/show/kernel+pair
 Wikipedia: https://en.wikipedia.org/wiki/Pullback_(category_theory)

 Mac Lane, “Categories for the Working Mathematician” 2nd ed., Springer
 GTM 5 1998, §III.4 Exercise 1 (p. 72) -- the pullback in Set is the set
 of pairs on which the two legs agree, with the evident projections --
 and §III.4 Exercise 6 (p. 72), the kernel pair: the pullback of f along
 itself, which is the equivalence relation “f x = f x'”
 ([maclane:III.4:ex1], [maclane:III.4:ex6]).  Awodey, “Category Theory”
 2nd ed., Oxford Logic Guides 52 2010, §5.2 gives the same construction
 and, in Example 5.9, the case that makes it useful: pulling a subset
 inclusion V ↪ B back along f : A ⟶ B is taking the preimage
 {a | f a ∈ V} ([awodey:5.2:example9]).  Riehl, “Category Theory in
 Context”, Dover 2016, §3.2 Example 3.2.9 records that a pullback IS the
 equalizer of the two composites out of the binary product
 ([riehl:3.2:example9]).

 WHAT WAS MISSING

 [HasPullbacks] (Structure/Pullback.v) had exactly ONE inhabitant
 for a concrete category, [FinSet_Pullbacks] (Instance/FinSet/
 Classifier.v) -- measured by [rg -n “HasPullbacks” -g '*.v' .]
 over the whole tree, whose other hits are the class itself, prose, the
 generic conditionals [HasPullbacks_of_Cartesian_HasEqualizers]
 (Structure/Pullback/Reduction.v), [HasPullbacks_op_of_HasPushouts]
 (Structure/Pushout.v) and [codomain_cleaving_pullbacks]
 (Construction/Displayed/Codomain.v) -- THREE, an earlier revision
 named two -- the two [*_of_HasPullbacks_Terminal] constants named for
 it, the class FIELDS [regular_pullbacks] (Structure/Regular.v)
 and [topos_pullbacks] (Structure/Topos.v), and hypothesis
 binders.
 None of those is a concrete inhabitant, so the headline is unaffected;
 the enumeration is corrected because it was offered as exhaustive.
 [Sets] had no pullbacks at all.  What it did have is [sets_char_pullback]
 (Instance/Sets/Classifier.v), and that is a different statement: it
 proves ONE particular square -- the classifying square of a given mono
 -- to be a pullback, it says nothing about arbitrary cospans, and it is
 stated over [Sets@{so sso}], one universe above the [Sets@{o so}] whose
 objects it is about.

 Nor did any concrete category carry the kernel pair.  [kernel_pair]
 (Structure/Regular.v) is [pullback f f]; the only in-tree constant
 built from it at a fixed category is [image_kernel_pair]
 (Structure/Regular/Factorization.v), and that sits under
 [Context (R : Regular C)], a class with no instance anywhere:
 searching [Regular] tree-wide, then discarding [RegularEpi], the
 [regular_*] field names and the von-Neumann-regularity vocabulary,
 leaves only [Require]s of Structure/Regular.v and that one binder.
 The [Instance/*/Regular.v] files are about the von Neumann regularity
 of ARROWS (Theory/Morphisms.v), a different notion sharing the
 word.

 THE DERIVATION ROUTE: MEASURED, AND NOT TAKEN

 Since jwiegley/category-theory#326 landed, [Sets] has had all the
 ingredients for a pullback to be read off a reduction:
 [Sets_Cartesian] (Instance/Sets/Cartesian.v), [Sets_HasEqualizers]
 (Adjunction/GAFT/Sets.v), and
 [HasPullbacks_of_Cartesian_HasEqualizers].  That route was tried before
 this file was written, and it produces an apex in the WRONG
 DESCRIPTION -- not an opaque one, a transparent one that unfolds to
 something else.  [Sets_HasEqualizers] is [Complete_HasEqualizers
 Sets_Complete], so its equalizer is the limit of the walking parallel
 pair as Instance/Sets/Complete.v builds it, and with

 Definition Derived : @HasPullbacks Sets :=
 @HasPullbacks_of_Cartesian_HasEqualizers Sets _ Sets_HasEqualizers.
 Definition DerObj : Sets := Pull f g (@pullback Sets Derived _ _ _ f g).

 in scope, BOTH of the following elaborate as written:

 ( * accepted: * )
 Definition derived_is_limit_obj :
 DerObj = Sets_limit_obj (APair (f ∘ exl) (g ∘ exr)) := eq_refl.
 ( * rejected: * )
 Definition strict_obj : DerObj = sets_pb_obj f g := eq_refl.

 the second with “cannot unify ”DerObj“ and ”sets_pb_obj f g“”.  So the
 derived apex IS, on the nose, the setoid of COMPATIBLE FAMILIES over
 the walking parallel pair: a dependent function on [ParObj] paired with
 a constraint quantified over every arrow of [Parallel].  An element of
 it is not a pair, and the agreement condition is not one equation.
 Deliverable (B) IS the claim that this object is the relation setoid,
 and (D)'s comparison map and mediator are written on pairs, so both
 would have had to be conducted through that encoding.  Scope that
 honestly: (C)'s headline would NOT have been affected, since
 [equalizer_of_pullback] applies to any [IsPullback] whatever its apex
 -- only (C)'s elementwise readings would move.  The construction here
 is therefore DIRECT, and #326's reduction is consumed the other way
 round, in (C), to say what the directly-built pullback is as an
 equalizer.

 That measurement is NOT pinned in this file, and the reason is
 dependency weight rather than doubt: stating it needs
 [Adjunction/GAFT/Sets.v], which would put the whole GAFT closure behind
 every consumer of pullbacks in [Sets].  It belongs in a Test/ probe.
 The fragment above reproduces in a scratch file that requires, beyond
 this file's own imports, Instance/Sets/Complete.v, Instance/Parallel.v,
 Structure/Limit.v, Adjunction/GAFT.v and Adjunction/GAFT/Sets.v.

 A STALE NOTE CORRECTED

 The issue text behind this file says Riehl's “the pullback is the
 equalizer” is stated nowhere in the tree and is recorded as a known gap
 at Structure/Topos.v.  That is not what that file says now, and the
 correction runs in both directions.  Structure/Topos.v says only
 that the topos class “deliberately do[es] not add equalizers”, and
 its header says in terms that the reduction and its converse “ARE
 formalized”, naming [equalizer_of_pullback]
 (Structure/Pullback/Reduction.v).  So the GENERIC theorem exists
 and this file does not supply it.  What did not exist is any
 INSTANTIATION at a concrete category: searching [IsEqualizer] tree-wide
 turns up, outside Structure/ and Test/, only [matr_IsEqualizer_op]
 (Instance/Matr/Coequalizer.v), which is the opposite-category
 reading of a matrix COequalizer and not a pullback square at all.  (C)
 below is the first place a pullback in a named category is exhibited as
 an equalizer.

 WHAT IS BUILT

 (A) [sets_pb_obj f g] is the sub-setoid of the product carrier cut out
 by the agreement condition: elements are pairs [(p; w)] with
 [w : f (fst p) ≈ g (snd p)], and two are identified when their
 underlying pairs are -- the witness plays no part, the discipline
 Instance/Sets/Complete.v uses and there attributes to
 Instance/Sets/End.v.  With
 [sets_pb_fst], [sets_pb_snd] and the mediator [sets_pb_med] this
 gives [Sets_IsPullback], [Sets_Pullback] and the registered
 instance [Sets_HasPullbacks].  The mediator's agreement witness is
 the competing square's own commuting equation read at a point, so
 nothing is chosen and no quotient is formed.

 (B) [sets_ker f] is [sets_pb_obj f f], the relation setoid
 {(u, v) | f u ≈ f v}.  Structure/Regular.v's [kernel_pair] IS that
 object with those two projections, recorded by [eq_refl] in
 [sets_kernel_pair_obj], [sets_kernel_pair_fst] and
 [sets_kernel_pair_snd].  The equivalence-relation reading is given
 AS ARROWS, in the standard internal form: [sets_ker_refl] is the
 diagonal [a ~> R] splitting both projections, [sets_ker_sym] is the
 swap [R ~> R] exchanging them, and [sets_ker_trans] goes out of
 [sets_ker_comp], the object of composable pairs -- which is itself
 a pullback, of [sets_ker_snd] along [sets_ker_fst], recorded by
 [eq_refl] in [sets_ker_comp_is_pullback].  All six leg equations
 are proved.  No internal-equivalence-relation CLASS is inhabited,
 because the tree has none; the six equations are stated directly.

 (C) [sets_pullback_is_equalizer] is Riehl's statement: the agreement
 subset, with the pairing of its two projections, is an
 [IsEqualizer] of [f ∘ exl] and [g ∘ exr].  It is
 [equalizer_of_pullback] applied to (A) -- an application of #326's
 theorem, not a second proof -- and [sets_equalizer_is_pullback]
 runs the reduction back the other way.

 (E) Non-vacuity.  NOTE THE ORDER: this paragraph is narrated before (D)
 although the code runs (A)(B)(C)(D)(E), so the witnesses named here
 that belong to the preimage section -- [even_preimage],
 [choose_factors], [sets_preimage_criterion] and
 [constThree_does_not_factor] -- are forward references to the
 paragraph below.  [graph_even] is the pullback of [Nat.even] along the
 identity of [bool], so its agreement subset is the graph of
 [Nat.even]; two of its elements are exhibited, a third pair is
 shown excluded, and the mediator out of [PbNatSet] evaluates on
 closed input.  [sets_ker evenM] identifies 0 and 2, and
 [even_ker_not_diagonal] proves the relation is therefore NOT the
 diagonal; the symmetry and transitivity arrows are evaluated on
 it, [(0,2)] composing with [(2,4)] to give [(0,4)].
 [even_preimage] is the preimage of [{true}], with 4 in it and 3
 provably not; [choose_factors] factors a non-constant map through
 it, [sets_preimage_criterion] carries that factorization
 downstairs and the result evaluates, and
 [constThree_does_not_factor] refutes the other case.

 (D) [sets_preimage f S] is the preimage of a subset along f, and
 [sets_preimage_IsPullback] is Awodey's Example 5.9.  A subset is a
 [Type]-valued predicate on the carrier saturated under [≈]
 ([SubsetOf]); a SINGLE such subset stays at the universe of the
 carriers, and it is the setoid of ALL [Type]-valued subsets that
 must move up a level (Instance/Sets/Powerset.v's [Powerset_obj]),
 which is why that file is neither needed nor required here.  The
 elementwise criterion is [sets_preimage_criterion]: t factors
 through the preimage exactly when f ∘ t factors through the
 subset, an [iffT] whose two
 directions are genuine constructions (forward composes with the
 comparison map, backward transports a membership witness along the
 downstairs factorization).  [FactorsThrough] is a [sigT], so the
 factoring map is data.

 STRENGTHS, MEASURED STRICT-FIRST

 Closing by [eq_refl]:
 - [Sets_Pullback_obj]/[_fst]/[_snd]: the bundled [Pullback] record's
 apex and projections are the three constants of (A);
 - [sets_kernel_pair_obj]/[_fst]/[_snd] and
 [sets_ker_comp_is_pullback], as described in (B);
 - [sets_preimage_mem]: membership in the preimage IS membership
 downstream;
 - [even_med_is_ump]: the mediator that [ump_pullbacks] hands back at
 the concrete cospan of (E) is [sets_pb_med] on the nose.  SCOPE
 THIS ONE HONESTLY: it is listed under (E) but carries NO
 non-vacuity content, because the GENERAL statement -- the same
 equation at an arbitrary cospan, apex and commuting witness --
 also holds by [eq_refl] (measured).  So the concrete instance
 demonstrates nothing the general fact would not, and would hold at
 degenerate cospans too.  The general form is the one a consumer
 wants and it is NOT stated here; adding it is left open rather
 than slipped in;
 - [sets_equalizer_round_fst_pointwise]/[_snd_pointwise]: projecting
 out of the pairing recovers the projection POINTWISE on carriers;
 - the [Example]s of (E): each is either an element of an agreement
 subset exhibited with an [eq_refl] agreement witness, or an
 equation between carriers closed by [eq_refl].

 Holding only up to [≈], with the strict form refuted (each attempted
 before the [≈] form was accepted; the refutations are measured here and
 ALL THREE are pinned in Test/ProbeSetsPullback333.v -- an earlier
 revision pinned only two and left this first one guarded nowhere while
 calling it measured):
 - [sets_equalizer_round_fst]/[_snd] as MORPHISMS: the two
 [SetoidMorphism] records agree on their underlying functions (that
 is the pointwise [eq_refl] above) and differ in the rebuilt
 [proper_morphism] certificate, so
 [exl ∘ sets_pb_pair = sets_pb_fst f g := eq_refl] is rejected;
 - [sets_pb_pair_computes]: the equalizing map sends an element to its
 underlying pair only up to [≈], since [sets_pb_pair u] is
 [(fst `1 u, snd `1 u)] and stdlib [prod] has no definitional eta --
 [sets_pb_pair f g u = `1 u := eq_refl] is rejected.  This is the
 same absence of surjective pairing that
 Construction/Free/Quiver/Constructions.v records for [QuiverSwap].

 UNIVERSES, READ OFF THE CONSTRAINT BLOCKS

 [Sets_HasPullbacks@{u u0} : HasPullbacks@{u u0} Sets@{u0 u}] carries
 [u0 < u] -- which is [Sets]'s own declaration constraint -- together
 with bounds on the stdlib donors [Basics.compose], [Projections],
 [ID] and the distinct lowercase [projections] family ([u0 <=
 projections.u0], [u0 <= projections.u1]) -- FOUR, an earlier revision
 named three.  There is no identification and no [Set] anywhere.  The
 multi-object statements do identify universes, but only because their
 objects are objects of ONE [Sets]: [Sets_IsPullback] and
 [sets_pullback_is_equalizer] read [u = u1], [u0 = u2], [u0 = u4] --
 x, y and z living in one and the same [Sets] -- and the
 two-object [sets_preimage_IsPullback] reads [u = u1], [u0 = u2].
 [SubsetOf@{u u0 u1}] leaves the MEMBERSHIP universe [u0] free; it is
 forming [sub_obj] that bounds it by the carrier universe, and the
 bound is [u1 <= u0] in that constant's own block.  The concrete
 witnesses of (E) are polymorphic too -- [PbNatSet@{u u0}] has [u0 < u],
 five stdlib donor bounds and no identification -- because they are over
 [eq_Setoid] (Lib/Setoid.v), which is universe-polymorphic, rather
 than by resolving [eq_equivalence] at an unannotated binder.

 ZERO AXIOMS.  All 103 constants of this file report “Closed under the
 global context”.  Enumerated as the 95 names the [.glob] records under
 [def], [prf], [inst], [proj] and [rec], plus the 7 [_obligation_]
 constants that [Print Module] lists and the [.glob] does not, plus
 [Build_SubsetOf], which appears in neither.

 WHAT IS NOT DELIVERED -- scoped to this file, no claim about the tree

 - The [Top] half of Mac Lane's Exercise 1 (the pullback of two
 continuous maps, with the subspace topology) is NOT built.  It is
 host-category-gated on jwiegley/category-theory#259 and is recorded
 here as the natural extension rather than as an obstruction: the
 carrier construction would be this one, and what is missing is the
 topology side.
 - No [Complete]-style packaging: nothing here relates
 [Sets_HasPullbacks] to [Sets_Complete] (Instance/Sets/Complete.v)
 or to [Sets_HasEqualizers], and in particular the pullback built
 here is NOT proved isomorphic to the derived one.  The two are
 isomorphic by [pullback_unique], but that composition is not
 performed and the comparison map is not named.
 - No [Regular Sets], no [HasCoequalizers]-based coequalizer of a
 kernel pair, and so no statement that a surjection is the
 coequalizer of its kernel pair.
 - No internal-equivalence-relation class, hence no theorem that
 [sets_ker] is one; (B) gives the six leg equations and stops.  No
 quotient by a kernel pair is formed and nothing here is related to
 Instance/Sets/Quotient.v.
 - Nothing about wide pullbacks, pullback pasting, or stability here;
 pasting and stability are Theory/Morphisms/Stability.v's, and wide
 pullbacks at Sets are Instance/Sets/SubobjectLattice.v's.
 - [SubsetOf] is a local convenience, not a subobject theory: it is
 not related to Theory/Subobject.v, not shown to be the same as
 Instance/Sets/Powerset.v's subsets, and [sub_incl] is proved
 [Monic] but no converse (every mono is such an inclusion) is
 claimed.
 - The mediator of (D)'s pullback is not compared with (A)'s; the two
 constructions are independent, and no isomorphism between
 [sub_obj (sets_preimage f S)] and [sets_pb_obj f (sub_incl S)] is
 built.
 - No [Fail] probe of any kind lives here. 

 --------
 nLab：       https://ncatlab.org/nlab/show/pullback
 nLab：       https://ncatlab.org/nlab/show/kernel+pair
 维基百科：  https://en.wikipedia.org/wiki/Pullback_(category_theory)Mac Lane，《为工作中的数学家论范畴》第二版，Springer GTM 5 1998，第III.4节 习题1（第72页）——在Set中的拉回是那些两个分支一致的对的集合，并具有显而易见的投影——以及第III.4节 习题6（第72页），核对：沿自身的f的拉回，即等价关系“f x = f x'”（[maclane:III.4:ex1], [maclane:III.4:ex6]）。Awodey，《范畴论》第二版，Oxford Logic Guides 52 2010，第5.2节给出了相同的构造，并在例5.9中说明了其用途：将子集包含V ↪ B沿f : A ⟶ B拉回即取原像 {a | f a ∈ V}（[awodey:5.2:example9]）。Riehl，《语境中的范畴论》，Dover 2016，第3.2节例3.2.9记录了拉回就是二元积的两个复合的等化子（[riehl:3.2:example9]）。

 缺失的是什么[HasPullbacks]（Structure/Pullback.v）在一个具体范畴中恰好有一个元素，[FinSet_Pullbacks]（Instance/FinSet/Classifier.v）——由[rg -n “HasPullbacks” -g '*.v' .]在整个树上测量，其它命中的是类本身、散文、一般条件[HasPullbacks_of_Cartesian_HasEqualizers]（Structure/Pullback/Reduction.v）、[HasPullbacks_op_of_HasPushouts]（Structure/Pushout.v）和[codomain_cleaving_pullbacks]（Construction/Displayed/Codomain.v）——三个，早期修订提到两个——两个以其命名的[*_of_HasPullbacks_Terminal]常量，类FIELDS [regular_pullbacks]（Structure/Regular.v）和[topos_pullbacks]（Structure/Topos.v），以及假设绑定。没有一个是具体元素，因此标题不受影响；枚举已修正，因为它曾被作为详尽列举。[Sets] 完全没有拉回。它确实有的是 [sets_char_pullback] (Instance/Sets/Classifier.v)，那是一个不同的陈述：它证明了一个特定的平方——给定单态的分类平方——是一个拉回图，它并没有涉及任意的余锥，而且它是在 [Sets@{so sso}] 之上陈述的，比它所涉及的对象所在的 [Sets@{o so}] 高一个宇宙。没有任何具体类别包含核对。[kernel_pair]（Structure/Regular.v）是[pullback f f]；在固定类别中由它构建的唯一树内常量是[image_kernel_pair]（Structure/Regular/Factorization.v），它位于[Context (R : Regular C)]之下，一个在任何地方都没有实例的类：在整个[Regular]树中搜索，然后丢弃[RegularEpi]、[regular_*]字段名称和冯·诺伊曼正则性词汇表，只剩下Structure/Regular.v的[Require]以及那个绑定器。[Instance/*/Regular.v]文件涉及箭头(Theory/Morphisms.v)的冯·诺伊曼正则性，这是一个不同的概念但使用了相同的词语。

 推导路线：已测量，但未采用自从 jwiegley/category-theory#326 合并以来，[Sets] 已经具备了从归约中读取回拉所需的所有要素：[Sets_Cartesian]（Instance/Sets/Cartesian.v）、[Sets_HasEqualizers]（Adjunction/GAFT/Sets.v），以及 [HasPullbacks_of_Cartesian_HasEqualizers]。这个路径在编写此文件之前就已经尝试过，并且它会在错误的描述下生成顶点——不是不透明的，而是可以展开为其他东西的透明顶点。[Sets_HasEqualizers] 是 [Complete_HasEqualizers Sets_Complete]，所以它的等化器是步行平行对的极限，由 Instance/Sets/Complete.v 构建，并且有

 Definition Derived : @HasPullbacks Sets :=
 @HasPullbacks_of_Cartesian_HasEqualizers Sets _ Sets_HasEqualizers.
 Definition DerObj : Sets := Pull f g (@pullback Sets Derived _ _ _ f g).

 在作用域中，以下两者都会如原文展开：( * 接受: * )
 定义 derived_is_limit_obj :
 DerObj = Sets_limit_obj (APair (f ∘ exl) (g ∘ exr)) := eq_refl.
 ( * 拒绝: * )
 定义 strict_obj : DerObj = sets_pb_obj f g := eq_refl.第二个包含“无法统一 'DerObj' 和 'sets_pb_obj f g'”。因此，派生的顶点精确地是行走平行对上的兼容族的集合论：一个依赖函数在 [ParObj] 上，与一个对 [Parallel] 上每个箭头量化的约束配对。它的一个元素不是一对，并且一致性条件不是一个等式。交付物 (B) 是声称这个对象是关系集合体，而 (D) 的比较映射和中介是写在对上的，因此两者都必须通过该编码进行。老实考虑这个范围：(C) 的标题不会受到影响，因为 [equalizer_of_pullback] 适用于任何 [IsPullback]，无论其顶点如何——只有 (C) 的逐元素解读会移动。因此，这里的构造是直接的，而 #326 的化简则在相反的方向上被使用，在 (C) 中说明了直接构建的拉回作为一个等化器的情况。

 该测量未在此文件中固定，其原因是依赖权重而非疑问：声明它需要 [Adjunction/GAFT/Sets.v]，这会使整个 GAFT 闭包落在 [Sets] 中每个拉回的使用者之后。它属于 Test/ probe。上述片段在一个临时文件中可以重现，除了该文件自身的导入之外，还需要 Instance/Sets/Complete.v、Instance/Parallel.v、Structure/Limit.v、Adjunction/GAFT.v 和 Adjunction/GAFT/Sets.v。

 一条过期的注释已更正该文件背后的问题文本说 Riehl 的“拉回是等化器”在树中没有任何地方被说明，并且在 Structure/Topos.v 被记录为已知的缺失。这不是该文件现在所说的内容，且该修正是双向的。Structure/Topos.v 只说明 topos 类“有意不添加等化器”，其标题中用术语说明了约简及其逆“已被形式化”，并命名了 [equalizer_of_pullback] (Structure/Pullback/Reduction.v)。因此，通用定理是存在的，而该文件并没有提供它。不存在的是在具体范畴中的任何实例化：在整个 [IsEqualizer] 树中搜索，在 Structure/ 和 Test/ 之外，只找到 [matr_IsEqualizer_op] (Instance/Matr/Coequalizer.v)，它是矩阵 COequalizer 的对立范畴解释，并不是一个拉回平方。下面 (C) 是在一个命名范畴中第一次将拉回显示为等化器的地方。

 建立的内容是什么(A)  [sets_pb_obj f g] 是由一致性条件切割出的乘积承载子子集：元素是成对的 [(p; w)]，满足 [w : f (fst p) ≈ g (snd p)]，当它们的基础对相同时，两者被识别——见证者不起作用，Instance/Sets/Complete.v 使用它们的属性到 Instance/Sets/End.v。 有了 [sets_pb_fst]、[sets_pb_snd] 和中介者 [sets_pb_med]，这给出了 [Sets_IsPullback]、[Sets_Pullback] 和登记的实例 [Sets_HasPullbacks]。中介者的一致性见证是竞争方形自身在某一点处的交换方程，所以什么都没有被选择，也没有形成商。(B) [sets_ker f] 是 [sets_pb_obj f f]，即关系等价类集合 {(u, v) | f u ≈ f v}。Structure/Regular.v 的 [kernel_pair] 是那个带有两投影的对象，由 [eq_refl] 记录在 [sets_kernel_pair_obj]、[sets_kernel_pair_fst] 和 [sets_kernel_pair_snd] 中。等价关系的读取以 ARROWS 形式给出，在标准内部形式中：[sets_ker_refl] 是对角线 [a ~> R]，分割两个投影；[sets_ker_sym] 是交换它们的交换 [R ~> R]；[sets_ker_trans] 由 [sets_ker_comp] 出发，该对象是可组合对——它本身是 [sets_ker_snd] 沿 [sets_ker_fst] 的拉回，由 [eq_refl] 记录在 [sets_ker_comp_is_pullback] 中。所有六条腿方程都已证明。内部等价关系类没有元素，因为树中没有；这六条方程直接陈述。(C) [sets_pullback_is_equalizer] 是 Riehl 的陈述：该协议子集及其两个投影的配对，是 [IsEqualizer] 对 [f ∘ exl] 和 [g ∘ exr] 的 [equalizer_of_pullback] 应用——应用于 (A) ——#326 定理的应用，而不是第二个证明——并且 [sets_equalizer_is_pullback] 以相反的方式运行还原。(E) 非空性。注意顺序：这一段在(D)之前叙述，尽管代码的运行顺序是(A)(B)(C)(D)(E)，因此这里提到的属于原像部分的证人——[even_preimage]、[choose_factors]、[sets_preimage_criterion] 和 [constThree_does_not_factor]——是对下面段落的前向引用。[graph_even] 是沿着 [bool] 的恒等映射对 [Nat.even] 的拉回，因此其一致子集是 [Nat.even] 的图；其两个元素被展示，第三对被排除，并且来自 [PbNatSet] 的中介在闭合输入上求值。[sets_ker evenM] 识别 0 和 2，而 [even_ker_not_diagonal] 证明因此该关系不是对角线；对称性和传递性箭头在其上求值，[(0,2)] 与 [(2,4)] 组合得到 [(0,4)]。[even_preimage] 是 [{true}] 的原像，其中包含 4，而 3 可被证明不包含；[choose_factors] 将一个非常数映射分解通过它，[sets_preimage_criterion] 将该分解传递到底部并计算出结果，[constThree_does_not_factor] 否定了另一种情况。(D) [sets_preimage f S] 是沿 f 的一个子集的逆像，[sets_preimage_IsPullback] 是 Awodey 的例子 5.9。一个子集是 [Type] 值的谓词，在其载体上在 [≈]（[SubsetOf]）下饱和；一个单独的这样子集停留在载体的宇宙中，并且它是所有 [Type] 值子集的集合论等价类，这些子集必须提升一个层次（Instance/Sets/Powerset.v 中的 [Powerset_obj]），这就是为什么在这里那份文件既不需要也不要求。逐元素标准是 [sets_preimage_criterion]：当且仅当 f ∘ t 通过子集分解时，t 才能通过逆像分解，这是一个 [iffT]，其中两个方向都是实际构造（向前与比较映射组合，向后沿下层分解传输一个元素属于性证据）。[FactorsThrough] 是一个 [sigT]，所以分解映射是数据。

 优势，严格优先测量[eq_refl] 的结论：
 -  [Sets_Pullback_obj] / [_fst] / [_snd] ：捆绑的 [Pullback] 记录的顶点和投影是 (A) 的三个常数；
 -  [sets_kernel_pair_obj] / [_fst] / [_snd] 以及 [sets_ker_comp_is_pullback] ，如 (B) 所述；
 -  [sets_preimage_mem] ：原像中的成员资格即下游中的成员资格；
 -  [even_med_is_ump] ：[ump_pullbacks] 在 (E) 的具体余锥上返回的中介是完全等于 [sets_pb_med] 的。坦白地说关注这个：它列在 (E) 下，但不包含任何非空内容，因为一般陈述——在任意余锥、顶点和交换见证下的相同方程——也由 [eq_refl]（经过测量）成立。因此，具体实例并没有展示一般事实不会展示的内容，并且在退化余锥上也同样成立。一般形式是消费者想要的形式，这里没有说明；是否添加它是开放的，而不是偷偷加入的；
 - [sets_equalizer_round_fst_pointwise] / [_snd_pointwise]：从配对中投射会在载体上逐点恢复投射；
 - (E) 的 [Example]：每个要么是用 [eq_refl] 协议证人展示的协议子集中的元素，要么是由 [eq_refl] 闭合的载体之间的等式。仅持有到 [≈]，严格形式被否定（在接受 [≈] 形式之前每次尝试都被否定；反驳在这里被测量，并且全部三个都固定在 Test/ProbeSetsPullback333.v 中——早期修订仅固定了两个，并且没有保护第一个，同时称其为已测量）：
 - [sets_equalizer_round_fst] / [_snd] 作为 MORPHISMS：两个 [SetoidMorphism] 记录在其基础函数上是一致的（即上面的逐点 [eq_refl]），并在重建的 [proper_morphism] 证书中有所不同，因此 [exl ∘ sets_pb_pair = sets_pb_fst f g := eq_refl] 被拒绝；
 - [sets_pb_pair_computes]：均衡映射将元素映射到其基础对仅到 [≈]，因为 [sets_pb_pair u] 是 [(fst `1 u, snd `1 u)]，且 stdlib [prod] 没有定义的 eta —— [sets_pb_pair f g u = `1 u := eq_refl] 被拒绝。这是 Construction/Free/Quiver/Constructions.v 对 [QuiverSwap] 记录的相同的缺乏满射配对的情况。

 宇宙，读取约束块[Sets_HasPullbacks@{u u0} : HasPullbacks@{u u0} Sets@{u0 u}]  包含
 [u0 < u]  -- 这是 [Sets] 自己的声明约束 -- 以及 stdlib 捐赠者的边界 [Basics.compose] , [Projections] ,
 [ID] 和不同的小写 [projections] 系列 ([u0 <= projections.u0], [u0 <= projections.u1] ) -- FOUR，早期版本称为 three。没有任何标识，也没有 [Set]。多对象语句确实识别宇宙，但仅因为它们的对象是同一个 [Sets] 的对象：[Sets_IsPullback] 和
 [sets_pullback_is_equalizer] 读取 [u = u1] , [u0 = u2] , [u0 = u4] -- x、y 和 z 生活在同一个 [Sets] -- 而两个对象 [sets_preimage_IsPullback] 读取 [u = u1] , [u0 = u2]。[SubsetOf@{u u0 u1}] 离开了 MEMBERSHIP 宇宙 [u0] 是自由的；它正在形成 [sub_obj]，这将其按承载宇宙进行界定，并且界限在该常量自身的块中为 [u1 <= u0]。 (E) 的具体实例也是多态的——[PbNatSet@{u u0}] 有 [u0 < u]，五个 stdlib 供体界限且没有标识——因为它们是位于 [eq_Setoid] (Lib/Setoid.v)，这是宇宙多态的，而不是通过在未注释的绑定器处解析 [eq_equivalence]。 

 零公理。此文件的所有 103 个常量报告为“在全局上下文下封闭”。按 [.glob] 在 [def]、[prf]、[inst]、[proj] 和 [rec] 下记录的 95 个名称枚举，加上 [Print Module] 列出而 [.glob] 未列出的 7 个 [_obligation_] 常量，以及 [Build_SubsetOf]，它两者都未出现。未交付的内容——仅限于此文件，不涉及整个树的说明- Mac Lane 练习 1 的 [Top] 一半（两个连续映射的拉回及其子空间拓扑）尚未构建。它在 jwiegley/category-theory#259 上受宿主类别控制，并作为自然扩展而非障碍记录在此：承载构造就是这个，而缺失的是拓扑部分。- 没有 [Complete] 风格的封装：这里没有任何内容将 [Sets_HasPullbacks] 与 [Sets_Complete]（Instance/Sets/Complete.v）或 [Sets_HasEqualizers] 联系起来，尤其是这里构建的拉回未被证明与派生的拉回同构。它们通过 [pullback_unique] 是同构的，但该组合未进行，并且比较映射未命名。- 没有 [Regular Sets]，没有基于 [HasCoequalizers] 的核对偶的余等化器，因此也没有说明一个满射是其核对偶的余等化器。- 没有内部等价关系类，因此也没有 [sets_ker] 是一个等价关系的定理；(B) 给出了六条腿方程并在此停止。没有形成核对偶的商，也没有与 Instance/Sets/Quotient.v 有关的内容。- 关于宽拉回、拉回拼接或稳定性没有任何内容；拼接和稳定性属于 Theory/Morphisms/Stability.v，而集合上的宽拉回属于 Instance/Sets/SubobjectLattice.v。- [SubsetOf] 是一个局部便利，而不是子对象理论：它与 Theory/Subobject.v 无关，也没有被证明与 Instance/Sets/Powerset.v 的子集相同，并且 [sub_incl] 被证明为 [Monic]，但没有声称其逆命题（每个单态都是这样的包含）。
 - (D) 的拉回的中介与 (A) 的没有进行比较；这两个构造是独立的，并且没有建立 [sub_obj (sets_preimage f S)] 和 [sets_pb_obj f (sub_incl S)] 之间的同构。
 - 这里没有任何类型的 [Fail] 探针。
*)

(* ====================================================================== *)
(* * * (A) The agreement sub-setoid / * *（A）协议子半序集 *)

Section SetsPullback.

Context {x y z : Sets}.
Context (f : x ~{Sets}~> z) (g : y ~{Sets}~> z).

(*
 An element of the pullback is a pair of elements on which f and g
 agree.  The agreement witness is carried alongside the pair rather
 than quotiented away, exactly as the compatibility constraint is in
 Instance/Sets/Complete.v. 

 --------
 拉回的一个元素是一对在其上 f 和 g 相符的元素。相符的证据与这对元素一起携带，而不是被取商，正如 Instance/Sets/Complete.v 中的兼容约束一样。
*)
Definition sets_pb_carrier : Type :=
  { p : carrier x * carrier y & @equiv _ z (f (fst p)) (g (snd p)) }.

(* Two elements are identified when the underlying pairs are: the agreement witness plays no part. / 当基础配对是以下情况时，会识别出两个元素：协议证人不起任何作用。 *)
Definition sets_pb_equiv : crelation sets_pb_carrier :=
  fun u v => (@equiv _ x (fst `1 u) (fst `1 v) *
              @equiv _ y (snd `1 u) (snd `1 v))%type.

Lemma sets_pb_equivalence : Equivalence sets_pb_equiv.
Proof.
  constructor.
  - intros u; split; reflexivity.
  - intros u v [H1 H2]; split; symmetry; assumption.
  - intros u v w [H1 H2] [K1 K2]; split.
    + transitivity (fst `1 v); assumption.
    + transitivity (snd `1 v); assumption.
Qed.

Definition sets_pb_obj : Sets :=
  {| carrier   := sets_pb_carrier
   ; is_setoid := {| equiv        := sets_pb_equiv
                   ; setoid_equiv := sets_pb_equivalence |} |}.

Program Definition sets_pb_fst : sets_pb_obj ~{Sets}~> x :=
  {| morphism := fun u => fst `1 u |}.
Next Obligation. intros u v H; exact (fst H). Qed.

Program Definition sets_pb_snd : sets_pb_obj ~{Sets}~> y :=
  {| morphism := fun u => snd `1 u |}.
Next Obligation. intros u v H; exact (snd H). Qed.

Lemma sets_pb_commutes : f ∘ sets_pb_fst ≈ g ∘ sets_pb_snd.
Proof. intros u; exact (`2 u). Qed.

(* The mediator out of a competing square: bundle the two legs at a point, the agreement witness being the competing square's own commuting equation read at that point. / 来自竞争方正方形的中介：在一点处将两条边捆绑，该协议的见证是竞争方正方形自身在该点处读取的通勤方程。 *)
Program Definition sets_pb_med {Q : Sets}
        (q1 : Q ~{Sets}~> x) (q2 : Q ~{Sets}~> y)
        (Hq : f ∘ q1 ≈ g ∘ q2) : Q ~{Sets}~> sets_pb_obj :=
  {| morphism := fun e => ((q1 e, q2 e); Hq e) |}.
Next Obligation.
  intros e e' H.
  exact (proper_morphism q1 e e' H, proper_morphism q2 e e' H).
Qed.

Definition Sets_IsPullback :
  IsPullback f g sets_pb_obj sets_pb_fst sets_pb_snd.
Proof.
  constructor.
  - exact sets_pb_commutes.
  - intros Q q1 q2 Hq.
    unshelve eapply Build_Unique.
    + exact (sets_pb_med q1 q2 Hq).
    + split; intros e; reflexivity.
    + intros v [Hv1 Hv2] e; split; symmetry; [exact (Hv1 e)|exact (Hv2 e)].
Defined.

Definition Sets_Pullback : Pullback f g :=
  is_pullback_pullback Sets_IsPullback.

(* The bundled record's apex and projections are the three constants above, on the nose. / 捆绑记录的顶点和投影就是上面三个位于准确位置的常数。 *)
Definition Sets_Pullback_obj : Pull f g Sets_Pullback = sets_pb_obj := eq_refl.
Definition Sets_Pullback_fst :
  pullback_fst f g Sets_Pullback = sets_pb_fst := eq_refl.
Definition Sets_Pullback_snd :
  pullback_snd f g Sets_Pullback = sets_pb_snd := eq_refl.

End SetsPullback.

#[export] Instance Sets_HasPullbacks : HasPullbacks Sets :=
  {| pullback := @Sets_Pullback |}.

(* ====================================================================== *)
(* * * (B) The kernel pair (Mac Lane §III.4 Exercise 6) / * *（B）核对偶（Mac Lane §III.4 练习 6） *)

Section KernelPair.

Context {a b : Sets}.
Context (f : a ~{Sets}~> b).

(*
 The relation setoid {(u, v) | f u ≈ f v}, which is the agreement
 sub-setoid of (A) taken at the cospan (f, f). 

 --------
 关系等价类 {(u, v) | f u ≈ f v}，它是在余锥 (f, f) 上取的 (A) 的一致子等价类。
*)
Definition sets_ker : Sets := sets_pb_obj f f.

Definition sets_ker_fst : sets_ker ~{Sets}~> a := sets_pb_fst f f.
Definition sets_ker_snd : sets_ker ~{Sets}~> a := sets_pb_snd f f.

(*
 Structure/Regular.v's generic [kernel_pair] IS that relation setoid,
 with those two projections, on the nose. 

 --------
 Structure/Regular.v 的通用 [kernel_pair] 是那个关系等价体，有那两个投影，本质上是一样的。
*)
Definition sets_kernel_pair_obj :
  Pull f f (@kernel_pair Sets Sets_HasPullbacks a b f) = sets_ker := eq_refl.

Definition sets_kernel_pair_fst :
  pullback_fst f f (@kernel_pair Sets Sets_HasPullbacks a b f) = sets_ker_fst
  := eq_refl.

Definition sets_kernel_pair_snd :
  pullback_snd f f (@kernel_pair Sets Sets_HasPullbacks a b f) = sets_ker_snd
  := eq_refl.

(* Membership, both ways. / 会员，双向的。 *)
Definition sets_ker_pair (u v : carrier a) (H : @equiv _ b (f u) (f v)) :
  carrier sets_ker := ((u, v); H).

Lemma sets_ker_related (w : carrier sets_ker) :
  @equiv _ b (f (sets_ker_fst w)) (f (sets_ker_snd w)).
Proof. exact (`2 w). Qed.

(* * ** The equivalence-relation laws, exhibited as arrows / * ** 作为箭头显示的等价关系定律 *)

(* Reflexivity: the diagonal a ~> R, splitting both projections. / 自反性：对角线 a ~> R，分裂两个投影。 *)
Program Definition sets_ker_refl : a ~{Sets}~> sets_ker :=
  {| morphism := fun u => ((u, u); reflexivity (f u)) |}.
Next Obligation. intros u v H; exact (H, H). Qed.

Lemma sets_ker_refl_fst : sets_ker_fst ∘ sets_ker_refl ≈ id[a].
Proof. intros u; reflexivity. Qed.

Lemma sets_ker_refl_snd : sets_ker_snd ∘ sets_ker_refl ≈ id[a].
Proof. intros u; reflexivity. Qed.

(* Symmetry: the swap R ~> R, exchanging the two projections. / 对称性：交换 R ~> R，交换两个投影。 *)
Program Definition sets_ker_sym : sets_ker ~{Sets}~> sets_ker :=
  {| morphism := fun w => ((snd `1 w, fst `1 w); symmetry (`2 w)) |}.
Next Obligation. intros w w' H; exact (snd H, fst H). Qed.

Lemma sets_ker_sym_fst : sets_ker_fst ∘ sets_ker_sym ≈ sets_ker_snd.
Proof. intros w; reflexivity. Qed.

Lemma sets_ker_sym_snd : sets_ker_snd ∘ sets_ker_sym ≈ sets_ker_fst.
Proof. intros w; reflexivity. Qed.

(*
 Transitivity needs the object of composable pairs, which is itself a
 pullback: the pullback of [sets_ker_snd] along [sets_ker_fst]. 

 --------
 传递性需要可组合对的对象，它本身是一个拉回：沿着  [sets_ker_fst] 的 [sets_ker_snd] 的拉回。
*)
Definition sets_ker_comp : Sets := sets_pb_obj sets_ker_snd sets_ker_fst.

Definition sets_ker_comp_is_pullback :
  Pull sets_ker_snd sets_ker_fst
       (@pullback Sets Sets_HasPullbacks _ _ _ sets_ker_snd sets_ker_fst)
  = sets_ker_comp := eq_refl.

Definition sets_ker_comp_fst : sets_ker_comp ~{Sets}~> sets_ker :=
  sets_pb_fst sets_ker_snd sets_ker_fst.
Definition sets_ker_comp_snd : sets_ker_comp ~{Sets}~> sets_ker :=
  sets_pb_snd sets_ker_snd sets_ker_fst.

Lemma sets_ker_trans_related (w : carrier sets_ker_comp) :
  @equiv _ b (f (fst `1 (fst `1 w))) (f (snd `1 (snd `1 w))).
Proof.
  transitivity (f (snd `1 (fst `1 w))).
  - exact (`2 (fst `1 w)).
  - transitivity (f (fst `1 (snd `1 w))).
    + exact (proper_morphism f _ _ (`2 w)).
    + exact (`2 (snd `1 w)).
Qed.

Program Definition sets_ker_trans : sets_ker_comp ~{Sets}~> sets_ker :=
  {| morphism := fun w => ((fst `1 (fst `1 w), snd `1 (snd `1 w));
                           sets_ker_trans_related w) |}.
Next Obligation. intros w w' H; exact (fst (fst H), snd (snd H)). Qed.

Lemma sets_ker_trans_fst :
  sets_ker_fst ∘ sets_ker_trans ≈ sets_ker_fst ∘ sets_ker_comp_fst.
Proof. intros w; reflexivity. Qed.

Lemma sets_ker_trans_snd :
  sets_ker_snd ∘ sets_ker_trans ≈ sets_ker_snd ∘ sets_ker_comp_snd.
Proof. intros w; reflexivity. Qed.

End KernelPair.

(* ====================================================================== *)
(* * * (C) The pullback IS the equalizer (Riehl §3.2 Example 3.2.9) / * * (C) 拉回是均等化器 (Riehl §3.2 例3.2.9) *)

Section PullbackAsEqualizer.

Context {x y z : Sets}.
Context (f : x ~{Sets}~> z) (g : y ~{Sets}~> z).

(* The equalizing map into the product: the two projections paired. / 映射到积的等化映射：两个投影配对。 *)
Definition sets_pb_pair : sets_pb_obj f g ~{Sets}~> (x × y)%object :=
  (sets_pb_fst f g △ sets_pb_snd f g).

Definition sets_pullback_is_equalizer :
  IsEqualizer (f ∘ exl) (g ∘ exr) (sets_pb_obj f g) sets_pb_pair :=
  equalizer_of_pullback (Sets_IsPullback f g).

(* And back: reading that equalizer as a pullback through the same reduction returns the projections composed with the pairing. / 回过头来看：将该均衡器视为通过同样的约减回拉，返回的是与配对组成的映射。 *)
Definition sets_equalizer_is_pullback :
  IsPullback f g (sets_pb_obj f g) (exl ∘ sets_pb_pair) (exr ∘ sets_pb_pair) :=
  pullback_of_equalizer f g sets_pullback_is_equalizer.

Lemma sets_equalizer_round_fst : exl ∘ sets_pb_pair ≈ sets_pb_fst f g.
Proof. intros u; reflexivity. Qed.

Lemma sets_equalizer_round_snd : exr ∘ sets_pb_pair ≈ sets_pb_snd f g.
Proof. intros u; reflexivity. Qed.

(*
 Measured strict-first: the round trip holds POINTWISE at Leibniz
 equality on the carriers, and only at `≈` as MORPHISMS -- the two
 [SetoidMorphism] records differ in their rebuilt [proper_morphism]
 certificate.  See the header for the refutation. 

 --------
 严格优先测量：往返在载体上的莱布尼茨等价下逐点成立，并且仅在 `≈` 作为态射时成立 —— 两个 [SetoidMorphism] 记录在其重建的 [proper_morphism] 证书中有所不同。详见标题以获取反证。
*)
Example sets_equalizer_round_fst_pointwise (u : carrier (sets_pb_obj f g)) :
  (exl ∘ sets_pb_pair) u = sets_pb_fst f g u := eq_refl.

Example sets_equalizer_round_snd_pointwise (u : carrier (sets_pb_obj f g)) :
  (exr ∘ sets_pb_pair) u = sets_pb_snd f g u := eq_refl.

(* Elementwise: the equalizing map sends an element of the agreement subset to its underlying pair, and that pair equalizes the two composites. / 逐元素：等化映射将协议子集的一个元素发送到其底层对，而该对使两个复合映射相等。 *)
Lemma sets_pb_pair_computes (u : carrier (sets_pb_obj f g)) :
  @equiv _ (x × y)%object (sets_pb_pair u) (`1 u).
Proof. split; reflexivity. Qed.

Lemma sets_pb_pair_equalizes (u : carrier (sets_pb_obj f g)) :
  @equiv _ z ((f ∘ exl) (sets_pb_pair u)) ((g ∘ exr) (sets_pb_pair u)).
Proof. exact (`2 u). Qed.

End PullbackAsEqualizer.

(* ====================================================================== *)
(* * * (D) Pulling a subset back is taking the preimage (Awodey Ex. 5.9) / * * (D) 拉回一个子集就是取原像（Awodey 练习 5.9） *)

(*
 A subset of a setoid B: a Type-valued predicate on its carrier that is
 saturated under `≈`.  A single subset stays at the universe of the
 carriers; it is the setoid of ALL subsets that must move up a level,
 and that object is not formed here (Instance/Sets/Powerset.v). 

 --------
 集合 B 的一个子集：其载体上的一个类型值谓词，并且在 `≈` 下是饱和的。单个子集停留在载体的宇宙中；它是所有子集的集合，需要提升一个层级，并且该对象在此处未形成（Instance/Sets/Powerset.v）。
*)
Record SubsetOf (B : Sets) : Type := {
  sub_mem : carrier B -> Type;
  sub_mem_resp : ∀ p q : carrier B, @equiv _ B p q -> sub_mem p -> sub_mem q
}.

Arguments sub_mem {B} _ _.
Arguments sub_mem_resp {B} _ {p q} _ _.

Section Subset.

Context {B : Sets}.
Context (S : SubsetOf B).

Lemma sub_obj_equivalence :
  Equivalence (fun u v : { p : carrier B & sub_mem S p } =>
                 @equiv _ B `1 u `1 v).
Proof.
  constructor.
  - intros u; reflexivity.
  - intros u v H; symmetry; exact H.
  - intros u v w H K; transitivity (`1 v); assumption.
Qed.

(*
 The subset as an object of [Sets]: elements of B together with a
 membership witness, compared by their underlying elements. 

 --------
 作为 [Sets] 对象的子集：B 的元素以及一个成员资格证明，通过其基础元素进行比较。
*)
Definition sub_obj : Sets :=
  {| carrier   := { p : carrier B & sub_mem S p }
   ; is_setoid := {| equiv        := fun u v => @equiv _ B `1 u `1 v
                   ; setoid_equiv := sub_obj_equivalence |} |}.

(*
 CORRECTED, and the correction matters because the original named the
 wrong mechanism.  An earlier revision said “[Program] raises no
 obligation here -- instance resolution closes [proper_morphism] during
 elaboration -- which is the shape Instance/Sets/Products.v
 records as a universe-pinning hazard”.  That is FALSE: the [Program]
 form DOES raise one, [sub_incl_obligation_1] (measured by elaborating
 it and reading [Print]).  Products.v defines its hazard as the
 definition raising NO obligation AT ALL, so this site is not an
 instance of that shape and the transplanted sentence was wrong twice.
 What survives is the CONCLUSION, which is independently measured: both
 forms were
 elaborated side by side and print the same binder
 [sub_incl@{u u0 u1} : ∀ {B : obj[Sets@{u0 u}]}, ...] with a
 character-for-character identical constraint block, so the hand-supplied
 certificate below is uniformity, not a repair. 

 --------
 已更正，这一更正很重要，因为原文命名了错误的机制。早期的一个修订版本说“[Program] 在这里不引发任何义务——实例解析在推演过程中关闭 [proper_morphism]——这是 Instance/Sets/Products.v 文件中记录为宇宙固定风险的形态”。这是错误的：[Program] 形式确实会引发一个义务，[sub_incl_obligation_1]（通过推演它并读取 [Print] 来测量）。Products.v 将其风险定义为定义根本不引发任何义务，因此该位置不是该形态的一个实例，而且移植的句子错误了两次。存留下来的部分是结论，它是独立测量的：两种形式是并排制作的，并打印相同的装订器 [sub_incl@{u u0 u1} : ∀ {B : obj[Sets@{u0 u}] }, ...]，具有逐字相同的约束块，因此下面手工提供的证书是统一性，而不是修复。
*)
Definition sub_incl : sub_obj ~{Sets}~> B.
Proof.
  unshelve refine {| morphism := fun u => `1 u |}.
  intros u v H; exact H.
Defined.

Lemma sub_incl_Monic : Monic sub_incl.
Proof. constructor; intros Z u v H e; exact (H e). Qed.

End Subset.

Arguments sub_obj {B} _.
Arguments sub_incl {B} _.

(* Factoring a map through a given map, as data (the tree's ∃ is sigT, so the factoring map is data and nothing is chosen). / 通过给定映射对映射进行因式分解，作为数据（树的 ∃ 是 sigT，因此因式分解映射是数据，且没有被选择的内容）。 *)
Definition FactorsThrough {Z W V : Sets} (m : W ~{Sets}~> V)
           (h : Z ~{Sets}~> V) : Type :=
  { k : Z ~{Sets}~> W & m ∘ k ≈ h }.

Section Preimage.

Context {A B : Sets}.
Context (f : A ~{Sets}~> B) (S : SubsetOf B).

(* The preimage {p | f p ∈ S}. / 原像 {p | f p ∈ S}。 *)
Definition sets_preimage : SubsetOf A.
Proof using All.
  unshelve refine {| sub_mem := fun p => sub_mem S (f p) |}.
  intros u v Huv Hm.
  exact (sub_mem_resp S (proper_morphism f u v Huv) Hm).
Defined.

(* Membership in the preimage IS membership downstream, definitionally. / 从定义上讲，原像中的成员资格就是下游的成员资格。 *)
Definition sets_preimage_mem (p : carrier A) :
  sub_mem sets_preimage p = sub_mem S (f p) := eq_refl.

(* The comparison over the cospan: an element of the preimage maps to its image, which carries the same membership witness. / 余跨度上的比较：原像的一个元素映射到其像，该像携带相同的隶属证明。 *)
Program Definition sets_preimage_over :
  sub_obj sets_preimage ~{Sets}~> sub_obj S :=
  {| morphism := fun u => (f `1 u; `2 u) |}.
Next Obligation. intros u v H; exact (proper_morphism f _ _ H). Qed.

(* The preimage square is a pullback. / 原像平方是一个拉回。 *)
Definition sets_preimage_IsPullback :
  IsPullback f (sub_incl S) (sub_obj sets_preimage)
             (sub_incl sets_preimage) sets_preimage_over.
Proof.
  constructor.
  - intros u; reflexivity.
  - intros Q q1 q2 Hq.
    unshelve eapply Build_Unique.
    + unshelve refine {| morphism := fun e => (q1 e; _) |}.
      * exact (sub_mem_resp S (symmetry (Hq e)) (`2 (q2 e))).
      * intros e e' H; exact (proper_morphism q1 e e' H).
    + split; intros e; [reflexivity|exact (Hq e)].
    + intros v [Hv1 Hv2] e; symmetry; exact (Hv1 e).
Defined.

(** ** The elementwise criterion / ** 元素逐项标准 *)

(* Awodey's criterion: t factors through the preimage exactly when f ∘ t factors through the subset. / Awodey 的标准：t 当且仅当 f ∘ t 通过该子集时，才通过原像。 *)
Lemma sets_preimage_criterion {Z : Sets} (t : Z ~{Sets}~> A) :
  FactorsThrough (sub_incl sets_preimage) t ↔
  FactorsThrough (sub_incl S) (f ∘ t).
Proof.
  split.
  - intros [k Hk].
    exists (sets_preimage_over ∘ k).
    intros e; exact (proper_morphism f _ _ (Hk e)).
  - intros [j Hj].
    unshelve refine (_; _).
    + unshelve refine {| morphism := fun e => (t e; _) |}.
      * exact (sub_mem_resp S (Hj e) (`2 (j e))).
      * intros e e' H; exact (proper_morphism t e e' H).
    + intros e; reflexivity.
Defined.

End Preimage.

(* ====================================================================== *)
(* * * (E) Non-vacuity: pullbacks in [Sets] that compute / * * (E) 非空性：在 [Sets] 中进行计算的回拉 *)

(*
 Two discrete setoids, over [eq_Setoid] of Lib/Setoid.v so that `≈` is
 Leibniz equality on the carriers and the equations below are genuine
 computations rather than instances of a coarse relation. 

 --------
 两个离散的集合等价体，在 Lib/Setoid.v 的 [eq_Setoid] 上，使得 `≈` 是载体上的莱布尼茨相等，并且下面的方程是实际计算而不是粗糙关系的实例。
*)
Definition PbNatSet : Sets :=
  {| carrier := nat; is_setoid := eq_Setoid nat |}.

Definition PbBoolSet : Sets :=
  {| carrier := bool; is_setoid := eq_Setoid bool |}.

Definition evenM : PbNatSet ~{Sets}~> PbBoolSet.
Proof.
  unshelve refine {| morphism := Nat.even |};
  try (intros n m H; rewrite H; reflexivity).
Defined.

Definition idB : PbBoolSet ~{Sets}~> PbBoolSet.
Proof.
  unshelve refine {| morphism := fun c : bool => c |};
  try (intros c c' H; exact H).
Defined.

(* * ** A cospan whose agreement subset is the graph of [Nat.even] / * ** 一个其一致子集是 [Nat.even] 图的协跨度 *)

(* The pullback of [evenM] along [idB]: pairs (n, c) with even n = c. / 沿着 [idB] 的 [evenM] 的回拉：偶数 n = c 的配对 (n, c)。 *)
Definition graph_even : Sets := sets_pb_obj evenM idB.

Example graph_even_3 : carrier graph_even := ((3%nat, false); eq_refl).
Example graph_even_4 : carrier graph_even := ((4%nat, true); eq_refl).

Example graph_even_3_fst :
  sets_pb_fst evenM idB graph_even_3 = 3%nat := eq_refl.
Example graph_even_3_snd :
  sets_pb_snd evenM idB graph_even_3 = false := eq_refl.

(* (3, true) is NOT in the agreement subset: no witness can be supplied. / (3, true) 不在协议子集中：无法提供任何证人。 *)
Lemma graph_even_excludes_3_true :
  @equiv _ PbBoolSet (evenM 3%nat) (idB true) → False.
Proof. discriminate. Qed.

(** ** The mediator computes / ** 调解员计算 *)

Lemma even_square : evenM ∘ id[PbNatSet] ≈ idB ∘ evenM.
Proof. intros n; reflexivity. Qed.

Definition even_med : PbNatSet ~{Sets}~> graph_even :=
  sets_pb_med evenM idB id[PbNatSet] evenM even_square.

(* The mediator produced by the universal property IS that map. / 由泛性质产生的中介者就是那个映射。 *)
Definition even_med_is_ump :
  unique_obj (ump_pullbacks evenM idB (Sets_Pullback evenM idB)
                            PbNatSet id[PbNatSet] evenM even_square)
  = even_med := eq_refl.

Example even_med_5_fst :
  sets_pb_fst evenM idB (even_med 5%nat) = 5%nat := eq_refl.
Example even_med_5_snd :
  sets_pb_snd evenM idB (even_med 5%nat) = false := eq_refl.
Example even_med_6_snd :
  sets_pb_snd evenM idB (even_med 6%nat) = true := eq_refl.

(* * ** The kernel pair of [evenM] is not the diagonal / * ** [evenM] 的核对不是对角线 *)

Example even_ker_02 : carrier (sets_ker evenM) := ((0%nat, 2%nat); eq_refl).

Example even_ker_02_fst : sets_ker_fst evenM even_ker_02 = 0%nat := eq_refl.
Example even_ker_02_snd : sets_ker_snd evenM even_ker_02 = 2%nat := eq_refl.

(* So the relation genuinely identifies two distinct elements. / 因此，该关系真正地识别了两个不同的元素。 *)
Lemma even_ker_not_diagonal :
  @equiv _ PbNatSet (sets_ker_fst evenM even_ker_02)
                  (sets_ker_snd evenM even_ker_02) → False.
Proof. discriminate. Qed.

(* The symmetry arrow moves it, and the reflexivity arrow does not land on it. / 对称箭头移动它，而自反箭头没有落在它上面。 *)
Example even_ker_sym_02_fst :
  sets_ker_fst evenM (sets_ker_sym evenM even_ker_02) = 2%nat := eq_refl.

Example even_ker_refl_0_snd :
  sets_ker_snd evenM (sets_ker_refl evenM 0%nat) = 0%nat := eq_refl.

(* And the transitivity arrow composes (0,2) with (2,4) to give (0,4). / 传递性箭头将 (0,2) 与 (2,4) 组合，得到 (0,4)。 *)
Example even_ker_24 : carrier (sets_ker evenM) := ((2%nat, 4%nat); eq_refl).

Example even_ker_composable : carrier (sets_ker_comp evenM) :=
  ((even_ker_02, even_ker_24); eq_refl).

Example even_ker_trans_fst :
  sets_ker_fst evenM (sets_ker_trans evenM even_ker_composable) = 0%nat
  := eq_refl.

Example even_ker_trans_snd :
  sets_ker_snd evenM (sets_ker_trans evenM even_ker_composable) = 4%nat
  := eq_refl.

(** ** The preimage of a subset / ** 子集的原像 *)

Definition TrueSub : SubsetOf PbBoolSet.
Proof.
  refine (Build_SubsetOf PbBoolSet (fun c : bool => c = true) _).
  intros u v Huv Hm; rewrite <- Huv; exact Hm.
Defined.

(* The preimage of {true} along [evenM] is the set of even naturals. / 沿着 [evenM] 的 {true} 的原像是偶数自然数的集合。 *)
Definition even_preimage : SubsetOf PbNatSet := sets_preimage evenM TrueSub.

Example even_preimage_4 : carrier (sub_obj even_preimage) := (4%nat; eq_refl).

Lemma even_preimage_excludes_3 : sub_mem even_preimage 3%nat → False.
Proof. discriminate. Qed.

(*
 A non-constant map into the preimage, and the criterion carrying it
 downstairs. 

 --------
 一个映射到原像的非常数映射，以及将其带到下面的标准。
*)
Definition chooseM : PbBoolSet ~{Sets}~> PbNatSet.
Proof.
  unshelve refine {| morphism := fun c : bool => if c then 4%nat else 2%nat |};
  try (intros c c' H; rewrite H; reflexivity).
Defined.

Definition choose_factors :
  FactorsThrough (sub_incl even_preimage) chooseM.
Proof.
  unshelve refine (_; _).
  - unshelve refine {| morphism := fun c : bool => (chooseM c; _) |}.
    all: try (intros c c' H; rewrite H; reflexivity).
    all: try (destruct c; reflexivity).
  - intros c; reflexivity.
Defined.

Definition choose_factors_downstairs :
  FactorsThrough (sub_incl TrueSub) (evenM ∘ chooseM) :=
  fst (sets_preimage_criterion evenM TrueSub chooseM) choose_factors.

Example choose_downstairs_true :
  `1 (`1 choose_factors_downstairs true) = true := eq_refl.

Example choose_downstairs_false :
  `1 (`1 choose_factors_downstairs false) = true := eq_refl.

(*
 The criterion is not vacuous in the negative direction either: the
 constant 3 does not factor through the preimage. 

 --------
 该准则在否定方向上也不是空洞的：常数3不能通过原像分解。
*)
Definition constThree : PbBoolSet ~{Sets}~> PbNatSet.
Proof.
  unshelve refine {| morphism := fun _ : bool => 3%nat |};
  try (intros c c' H; reflexivity).
Defined.

Lemma constThree_does_not_factor :
  FactorsThrough (sub_incl even_preimage) constThree → False.
Proof.
  intros [k Hk].
  pose proof (`2 (k true)) as Hm.
  pose proof (Hk true) as He.
  simpl in He, Hm.
  rewrite He in Hm.
  discriminate.
Qed.
