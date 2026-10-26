Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Theory.Skeleton.

Generalizable All Variables.

(* * * An isomorphism-dense full subcategory is reflective / * * 一个满同构稠密子范畴是反射的 *)

(*
 nLab: https://ncatlab.org/nlab/show/reflective+subcategory
 nLab: https://ncatlab.org/nlab/show/essentially+surjective+functor
 nLab: https://ncatlab.org/nlab/show/dense+subcategory

 Mac Lane, Categories for the Working Mathematician, 2nd ed., §IV.4,
 printed p. 94, states the result this file formalizes:

 “Proposition 2.  If A is a full subcategory of C and every c in C is
 isomorphic (in C) to some object of A, then the insertion K : A -> C
 is an equivalence and is part of an adjoint equivalence
 <T, K; eta, 1> : C -> A with counit the identity.  Therefore A is
 reflective in C.”

 The paragraph immediately before it supplies the proof idea, reading
 the general characterization of adjoint equivalences at an insertion:

 “In this proof, suppose that A is a full subcategory of C and that
 S = K : A -> C is the insertion.  For objects a in A subset C we can
 then choose a_0 = a = Ka and eta_{Ka} the identity.  Then K eps_a = 1,
 hence eps_a = 1 for all a.”

 and the paragraph after it records the two riders: “This includes in
 particular the case already noted, when A is a skeleton of C”, and the
 definition of a LEFT-ADJOINT-LEFT-INVERSE, with its Exercise 4 (“G is an
 isomorphism of A to a reflective subcategory of X”).  Exercise 4 is a
 separate catalog item and is cited here, not proved.

 ** What the proposition asks, and at which strength each half lands

 Four things are asserted.  Three are delivered outright and one is
 delivered in the form this library's setoid discipline supports:

 (1) the insertion is an EQUIVALENCE          [dense_incl_equivalence]
 (2) it is part of an ADJOINT EQUIVALENCE     [dense_incl_adjoint_-
 equivalence], and in the
 other handedness
 [dense_adj]
 (3) the counit is the IDENTITY               NOT delivered as stated;
 delivered as a
 componentwise ISOMORPHISM
 [dense_counit_iso],
 [dense_counit_Isomorphism]
 (4) the subcategory is REFLECTIVE            [dense_full_subcategory_-
 reflective]

 (3) is discussed at length below: with the chosen-representative reading
 of the hypothesis that this library already uses, the identity form is
 not merely unproved, it is not TYPEABLE.

 ** The hypothesis, first class

 [IsoDense S] is Mac Lane's “every c in C is isomorphic (in C) to some
 object of A”, with the object CHOSEN: a Type-valued sigma handing back,
 for each c, an object a of the subcategory together with an isomorphism
 Incl a =~= c in C.  This is exactly the reading [EssentiallySurjective]
 (Theory/Equivalence.v) already takes -- its [eso_obj] field is a
 function, not an existential -- and [iso_dense_ESO] is the repackaging,
 a plain [Definition] raising no obligation.  No choice principle is
 consumed anywhere in this file: the choice IS the hypothesis, supplied
 by the caller, exactly as [EssentiallySurjective] supplies it.  The
 converse repackaging [ESO_iso_dense] and both round trips are recorded;
 the object components agree at [eq_refl] in both directions, and the
 [EssentiallySurjective] whole record returns at [eq_refl] as well (a
 two-field class under Lib.v's [Set Primitive Projections] has eta),
 while the [IsoDense] whole record does NOT, since stdlib [sigT] is not
 covered by that setting.  That last one is refuted and pinned in
 Test/ProbeDense375.v.

 ** The route: pure reuse, with one design decision

 This file proves no new equation about any category.  Every field of
 every delivered constant comes from an existing donor:

 fullness of the inclusion functor   Full_Implies_Full_Functor
 (Construction/Subcategory.v)
 faithfulness of the inclusion       Incl_Faithful
 (Construction/Subcategory.v)
 essential surjectivity              iso_dense_ESO, from the hypothesis
 equivalence from those three        FF_ESO_Equivalence
 (Theory/Equivalence/-
 FullFaithful.v)
 adjoint equivalence from that       Equivalence_to_AdjointEquivalence
 (Theory/Equivalence/Adjoint.v)
 the OTHER handedness                AdjointEquivalence_swap_adjunction
 (Theory/Equivalence/Adjoint.v)
 the reflective packaging            Build_Reflective
 (Construction/Reflective.v)

 [Incl_Faithful] is literally in the proof term of
 [dense_incl_equivalence], which is a [:=] with no tactic:

 @FF_ESO_Equivalence _ _ (Incl C S)
 (Full_Implies_Full_Functor C S F) (Incl_Faithful C S)
 (iso_dense_ESO D)

 so the generic faithful-inclusion lemma is used rather than bypassed.
 That lemma is closed with [Qed], which costs nothing here: [Faithful] is
 a one-field class whose field is a proof, so there is no data to reduce.

 The ONE design decision is the HANDEDNESS.  Mac Lane writes the adjoint
 equivalence as <T, K; eta, 1>, and under the §IV.1 convention the
 first-listed functor of such a triple is the LEFT adjoint -- so T, the
 reflector, is left adjoint and the insertion K is the RIGHT adjoint.
 [Equivalence_to_AdjointEquivalence] makes the equivalence's OWN functor
 the left adjoint, so at F := Incl it yields Incl -| T, which is the
 opposite handedness and is NOT the reflection adjunction.
 [AdjointEquivalence_swap_adjunction] is what supplies T -| K, and that
 is the shape Theory/Equivalence/Creation.v already uses to read an
 equivalence as a right adjoint.  Both handednesses are shipped:
 [dense_incl_adjoint_equivalence] is Mac Lane's triple read with K on the
 left, [dense_adj] is the reflection adjunction.

 ** The counit

 Mac Lane's “with counit the identity” rests on a case distinction his
 prose does not mark as one, though it states the choice out loud: “For
 objects a in A subset C we can then choose a_0 = a”.  That is a choice
 made per object, DIFFERENTLY for objects already in the subcategory
 than for the rest.  Here the choice is one
 function [D], applied uniformly, so the representative of an object of
 the subcategory is the VALUE [`1 (D (Incl C S a))], which is not [a] --
 neither definitionally, nor up to any equation the hypothesis carries.
 Consequently

 counit (dense_adj D) a = id[a]

 is not false, it is ILL-TYPED: the counit runs
 [dense_reflector (Incl a) ~> a] and its two endpoints are different
 objects of [Sub C S].  That is pinned as a TYPING negative in
 Test/ProbeDense375.v at a witness where the two endpoints are provably
 distinct: a full subcategory of [Indiscrete bool] containing BOTH
 points, whose chosen representative for each point is the OTHER point.
 That witness is the honest content of Mac Lane's remark -- the identity
 counit is a property of a well-chosen family of representatives, not of
 iso-density.

 What is delivered instead is the componentwise isomorphism:
 [dense_counit_iso a : IsIsomorphism (counit (dense_adj D) a)], which is
 [adj_equiv_counit_iso] of the swapped adjoint equivalence and therefore
 a [:=] with no tactic, and its bundled reading
 [dense_counit_Isomorphism a : dense_reflector (Incl a) =~= a] in
 [Sub C S], whose forward leg IS the counit at [eq_refl].  The
 [Reflective]-level statement of the same fact is
 [reflective_counit_iso] (Construction/Reflective.v); it is cited
 rather than restated, and the direct form above is preferred because
 that lemma produces data and is closed with [Qed], so neither of its
 legs reduces.

 A further identification was attempted and is reported as MEASURED and
 NOT obtained: the counit ought to be the fullness-lift of the chosen
 isomorphism, so that [fmap[Incl C S] (counit (dense_adj D) a)] would be
 [approx] [to (`2 (D (Incl C S a)))].  The statement is true -- the
 symmetry branch of [Functor_Setoid]'s [Equivalence] obligation
 (Theory/Functor.v) builds [iso_sym] componentwise, [from] then
 [to] -- but that is a fact about the tactic's OUTPUT and not about the
 type, and it is not available by conversion: the route through
 [equiv_adjunction_counit_at] (Theory/Equivalence/Adjoint.v) is
 blocked at [symmetry], which is [Equivalence_Symmetric] of
 [Functor_Setoid] (Theory/Functor.v), whose [Equivalence] obligation
 is discharged by the [equivalence] tactic and closed with [Qed], so the
 isomorphism family it produces does not reduce and its type -- a bare
 natural isomorphism -- does not pin its components.  The identification
 is therefore not available through the swap, and no second route is
 built here.  The refuted strict form is pinned in the probe.  One
 sharper datum was measured out of tree after the audited constant set
 was fixed, and is recorded rather than shipped: the equivalence's own
 counit cell IS the chosen isomorphism on the nose,
 [equivalence_counit_at (dense_incl_equivalence D) c = `2 (D c)] at
 [eq_refl].

 For the same reason the strictified variant that a reader might expect
 -- a hypothesis [`1 (D (Incl C S a)) = a] making the counit an
 endomorphism, transported, and then [approx] [id] -- is NOT delivered,
 and the reason is sharper than opacity: even under that hypothesis the
 chosen isomorphism [`2 (D (Incl C S a))] may be a NON-IDENTITY
 automorphism of [a], so the counit still need not be the identity.  Such
 a hypothesis is therefore not sufficient, and the witness above is one
 where it does not hold.  Mac Lane's remark needs the isomorphism chosen
 to be the identity too, which is what his “and eta_{Ka} the identity”
 says.  No [eq_refl] identity is claimed for that case either: the
 triangle identity through which the counit would be read is an
 [approx]-equation.

 ** The skeleton rider, and a note on the order of events

 Mac Lane's “This includes in particular the case already noted, when A
 is a skeleton of C” is [skeleton_IsoDense] and [skeleton_reflective]: a
 [Skeleton] (Theory/Skeleton.v) carries [skel_rep] and [skel_iso],
 which ARE iso-density data with the isomorphism in the reverse
 orientation, so [skeleton_IsoDense] pairs [skel_rep] with [iso_sym] of
 that field and nothing more.  The rider is unusual in this tree in that
 the SPECIAL CASE preceded the general statement: Theory/Skeleton.v
 already proved [skeleton_inclusion_is_equivalence] by exactly this
 route, and had already defined [skel_reflect] as its
 quasi-inverse.  What was
 absent was the hypothesis as a first-class notion, the adjoint
 equivalence in the reflector-on-the-left handedness, and the conclusion
 [Reflective].  Because the two ESO records agree fieldwise and
 [EssentiallySurjective] has eta, the general theorem's reflector at a
 skeleton IS [skel_reflect] on the nose ([skeleton_reflector_is_skel_-
 reflect], [eq_refl]), so no second reflector enters the tree.

 ** Universes

 Measured with [About] and [Set Printing Universes] on all 26 constants,
 binder and block.  Every constant is over [C : Category@{u u0 u0}] --
 hom identified with proof in the BINDER, by reusing the level -- and
 that identification is inherited from [Subcategory@{u u0 u1 u2}], which
 is declared over [Category@{u u0 u0}] with an EMPTY constraint block;
 the probe pins it by rejecting [Subcategory Cu] at a category whose
 proof universe is declared strictly above its hom universe, with that
 category's hom-set, identity and hom-setoid accepted at those levels.
 Twenty-one constraint blocks carry no equation, only bounds.  Five carry
 exactly one, [u0 = u2], and they are exactly
 [dense_full_subcategory_reflective] and its four [eq_refl] readbacks --
 the four skeleton constants package [Reflective] too and carry none --
 because [Reflective@{u u0 u1 u2 u3 u4 u5}] is declared over
 [Subcategory@{u3 u5 u4 u5} C], instantiating [Subcategory]'s fourth
 universe at C's hom level where [Subcategory] itself leaves it free, so
 the equation is the record's and not this file's -- [dense_adj],
 [dense_reflector] and [dense_incl_equivalence] carry none.  No binder,
 block or universe instance of the 26 contains the token [Set].  None of
 these identifications is claimed unavoidable.

 ** Witnesses (in the probe, so this file's closure stays lean)

 Test/ProbeDense375.v instantiates the theorem twice over
 [Indiscrete bool] (Instance/Discrete/Reconstruct.v, whose hom and
 proof universes are the literal [Set] -- a pin the witnesses inherit and
 this file does not carry): once through [skeleton_reflective] at
 Theory/Skeleton/Separation.v's [Indiscrete_bool_Skeleton], where the
 reflection is proved NOT inert at the non-representative point, and
 once at a full subcategory on BOTH points whose chosen representative of
 each point is the OTHER point, the witness behind the counit paragraph
 above.

 ** Prior art, and four claims of the issue that are stale

 Measured on the base commit of this branch, over the .v files:

 (a) The issue says there is no generic [Faithful (Incl C S)] instance
 and that faithfulness of an inclusion is asserted in comments and
 proved per instance.  FALSE: Construction/Subcategory.v is
 [Lemma Incl_Faithful : Functor.Faithful Incl], consumed by
 Theory/Skeleton.v, by Adjunction/FullFaithful.v and by
 Construction/Reflective/Limit.v among others.  Nothing here
 rebuilds it.

 (b) Several donor line numbers in the issue have drifted.  At this
 base the issue misses [Incl], [Full] and
 [Full_Implies_Full_Functor] in Construction/Subcategory.v, and
 [EssentiallySurjective] in Theory/Equivalence.v.  Its
 citations of [FF_ESO_Equivalence] and
 [Equivalence_to_AdjointEquivalence] are right.

 (c) The issue says the existing applications of [FF_ESO_Equivalence]
 are not subcategory inclusions.  STALE:
 Theory/Skeleton.v applies it to [skel_incl S], which IS the
 [Incl] of a [Sub].  (Instance/FinSet/Skeleton.v also applies it to
 a functor called [FinSet_Incl], but that one is a hand-built
 [Program Definition] and not an [Incl C S] at all.)  So
 the specialization to a subcategory inclusion existed for the
 skeleton; what did not exist is measured in the paragraph above.

 (d) The issue defers the skeleton corollary until the skeleton
 development lands.  It has landed: Theory/Skeleton.v exists and
 declares [Record Skeleton], so the corollary is delivered here.

 Searches run on the same base: [IsoDense], [iso_dense] and
 [dense_full_subcategory_reflective] have zero hits outside this file and
 its probe, and [Build_Reflective] has exactly four application sites
 (Construction/Reflective/Idempotent.v, Instance/Ord/Poset.v,
 Instance/Ab/TorsionFree.v, Instance/Top/Kolmogorov.v), none of
 them obtained from an equivalence; a fifth textual hit,
 Instance/Ab/TorsionFree.v, is a comment quoting the search string.

 ** Registration

 NOTHING in this file is registered for instance resolution, following
 the rule Theory/Equivalence.v and Theory/Equivalence/FullFaithful.v
 state for themselves: a quasi-inverse and a chosen preimage object are
 CHOICES and must be passed explicitly.  [EssentiallySurjective] is a
 class, so [iso_dense_ESO] would be resolvable if declared an [Instance];
 it is a plain [Definition] on purpose.

 ** Not delivered

 Exercise 4 of the same page (a left-adjoint-left-inverse of G makes G an
 isomorphism onto a reflective subcategory) is a separate catalog item
 and is not attempted.  The converse of the proposition -- a reflective
 subcategory whose unit is a componentwise isomorphism is iso-dense -- is
 not stated.  Nothing is said about [Coreflective], about naturality of
 the choice [D] in any variable, or about uniqueness of the reflector. 

 --------
 nLab:  https://ncatlab.org/nlab/show/reflective+subcategory 
 nLab:  https://ncatlab.org/nlab/show/essentially+surjective+functor 
 nLab:  https://ncatlab.org/nlab/show/dense+subcategory 

 Mac Lane, 《为工作数学家而作的范畴论》，第二版，第 IV.4 节，
 印刷页 94 上，陈述了该文件形式化的结果：

 “命题 2。如果 A 是 C 的一个充满子范畴，并且 C 中的每个对象 c 
 都在 C 中与 A 的某个对象同构，则插入函子 K : A -> C 
 是一个等效函子，并且是一个伴随等价 
 <T, K; eta, 1> : C -> A 的一部分，其余单位为恒等。 
 因此 A 在 C 中是反射子的。”

 紧接在前面的段落提供了证明思路，阅读插入处伴随等价的一般表征：在这个证明中，假设 A 是 C 的一个完全子范畴，并且 S = K : A -> C 是插入。对于位于 A ⊆ C 中的对象 a，我们可以选择 a_0 = a = Ka 并且 η_{Ka} 为恒等映射。然后 K ε_a = 1，因此对所有 a 都有 ε_a = 1。

 接下来的段落记录了两个附加说明：“这特别包括已经注意到的情况，即当 A 是 C 的一个骨架时”，以及 LEFT-ADJOINT-LEFT-INVERSE 的定义及其练习 4（“G 是 A 到 X 的反射子范畴的同构”）。练习 4 是一个单独的目录项，这里引用但不证明。

 ** 命题要求的内容，以及各部分所达到的强度

 总共断言了四件事。三件是直接给出的，一件是以本库的等价类规范方式提供的。(1) 插入是一个等价           [dense_incl_equivalence]
 (2) 它是一个伴随等价的一部分     [dense_incl_adjoint_equivalence]，在
 另一种手性下                       [dense_adj]
 (3) 余单位是恒等的               并非如所述提供；
 而是作为一个分量同构提供       [dense_counit_iso] ，
 [dense_counit_Isomorphism]
 (4) 子范畴是反射的               [dense_full_subcategory_reflective](3) 在下面详细讨论：根据这个库已经使用的假设的选定代表性解读，同一形式不仅未被证明，它甚至 **不可类型化**。

 ** 该假设，第一类[IsoDense S] 是 Mac Lane 的“每个 C 中的 c 在 C 中同构于 A 中的某个对象”，所选择的对象：一个类型值的 sigma，它为每个 c 返回子范畴的一个对象 a，并伴随一个同构 Incl a =~= c 在 C 中。这正是 [EssentiallySurjective] (Theory/Equivalence.v) 已经采用的解读——它的 [eso_obj] 字段是一个函数，而不是存在性——而 [iso_dense_ESO] 是重新打包，一个普通的 [Definition] 并不增加任何义务。在这个文件的任何地方都没有消耗选择原则：选择正是由调用者提供的假设，正如 [EssentiallySurjective] 提供的那样。反向重新打包 [ESO_iso_dense]，并且两个往返都已记录；
 对象组件在两个方向上都在 [eq_refl] 一致，而 [EssentiallySurjective] 整条记录也在 [eq_refl] 返回（Lib.v 的 [Set Primitive Projections] 下的一个两字段类有 eta），
 而 [IsoDense] 整条记录没有，因为 stdlib [sigT] 不在该设置覆盖范围内。最后一条在 Test/ProbeDense375.v 中被驳斥并固定。

 ** 路径：纯重用，加上一项设计决策

 此文件没有证明关于任何类别的新方程。每个已提供常量的每个字段都来自现有的捐赠者：包含函子的满性   Full_Implies_Full_Functor
 (Construction/Subcategory.v)
 包含的忠实性       Incl_Faithful
 (Construction/Subcategory.v)
 本质满射性              iso_dense_ESO, 来自假设
 由这三者得到的等价        FF_ESO_Equivalence
 (Theory/Equivalence/-
 FullFaithful.v)
 由此得到的伴随等价       Equivalence_to_AdjointEquivalence
 (Theory/Equivalence/Adjoint.v)
 另一种方向                AdjointEquivalence_swap_adjunction
 (Theory/Equivalence/Adjoint.v)
 反射性封装Build_Reflective
 (Construction/Reflective.v)[Incl_Faithful] 事实上在 [dense_incl_equivalence] 的证明项中，后者是一个没有策略的 [:=] ：

 @FF_ESO_Equivalence _ _ (Incl C S)
 (Full_Implies_Full_Functor C S F) (Incl_Faithful C S)
 (iso_dense_ESO D)

 所以使用的是通用的忠实包含引理，而不是绕过它。该引理以 [Qed] 封闭，在这里完全没有成本：[Faithful] 是一个只有一个字段的类，该字段是一个证明，所以没有数据可以化简。唯一的设计决策是“手性”。Mac Lane 将伴随等价写作 <T, K; eta, 1>，根据 §IV.1 的约定，这样三元组中列在第一位的函子是左伴随——因此 T，即反射函子，是左伴随，而插入 K 是右伴随。[Equivalence_to_AdjointEquivalence] 使等价自身的函子成为左伴随，所以在 F := Incl 时，它得出 Incl -| T，这与原有手性相反，并且不是反射伴随。[AdjointEquivalence_swap_adjunction] 提供的是 T -| K，这正是 Theory/Equivalence/Creation.v 已经用来将等价读作右伴随的形式。两种手性都已提供：[dense_incl_adjoint_equivalence] 是按 Mac Lane 的方式读三元组，K 在左边，[dense_adj] 是反射伴随。

 ** 余单元麦克莱恩的“以余单位为恒等”的说法基于一个情况区分，他的文字并没有标明这是一个区分，尽管它明确说明了选择：“对于 A 子集 C 中的对象 a，我们可以选择 a_0 = a”。这是针对每个对象做出的选择，对于已经在子范畴中的对象与其他对象的选择是不同的。在这里，选择是一个函数 [D]，统一应用，因此子范畴对象的代表是值 [`1 (D (Incl C S a))]，它不是 [a]——无论是定义上，还是在假设所允许的任何等式下。因此

 counit (dense_adj D) a = id [a]不是错误的，它是类型错误的：余单位运行在
 [dense_reflector (Incl a) ~> a] 上，其两个端点是 [Sub C S] 的不同对象。
 这在 Test/ProbeDense375.v 中被标记为类型检查的负例，在这个例子中两个端点可以被证明是不同的：ZW35WZZ 的一个完整子范畴，包含两个点，其每个点选取的代表是另一个点。
 这个例子就是 Mac Lane 所说内容的真实体现——恒等余单位是对精心选择的代表族的一个性质，而不是同构密度的性质。取而代之的是按分量的同构：
 [dense_counit_iso a : IsIsomorphism (counit (dense_adj D) a)]，它是
 [adj_equiv_counit_iso] 被交换伴随等价，因此
 是一个没有策略的 [:=]，并且其捆绑的读法
 [dense_counit_Isomorphism a : dense_reflector (Incl a) =~= a] 在
 [Sub C S] 中，其前向分支是位于 [eq_refl] 的辅单元。相同事实的 [Reflective] 级别陈述是
 [reflective_counit_iso]（Construction/Reflective.v）；它被引用而不是重新陈述，上面的直接形式更为优选，因为该引理生成数据并且由 [Qed] 封闭，所以它的分支都不会简化。进一步的识别尝试已进行，并报告为已测量且未获得：counit 应该是所选择同构的 fullness-lift，因此 [[fmap[Incl C S] (counit (dense_adj D) a)] 将是 [approx] [to (`2 (D (Incl C S a)))] 。该陈述是正确的——[Functor_Setoid] 的 [Equivalence] 义务（Theory/Functor.v） 的对称分支 [iso_sym] 是按组件构建的，然后是 [to] ——但这是关于策略输出的事实，而不是关于类型，并且无法通过转换获得：通过 [equiv_adjunction_counit_at] （Theory/Equivalence/Adjoint.v）的途径在 [symmetry] 阻塞，该处是 [Functor_Setoid] （Theory/Functor.v） 的 [Equivalence_Symmetric]，其 [Equivalence] 义务由 [equivalence] 策略完成并用 [Qed] 关闭，因此它生成的同构族不会约简，其类型——一个纯粹的自然同构——不会固定其组件。因此，通过交换无法获得该标识，这里也没有构建第二条路径。被否定的严格形式在探测中被固定。在审核过的常数集合固定之后，从树中测量出一个更尖锐的基准，并被记录而非运送：等价自身的余单位单元就是精确选择的同构，[equivalence_counit_at (dense_incl_equivalence D) c = `2 (D c)] 位于 [eq_refl]。出于同样的原因，读者可能预期的严格化变体——假设 [`1 (D (Incl C S a)) = a] 使得余单位成为一个自同态，经转移后，再 [approx]  [id] ——并未给出，其原因比不透明性更明确：即使在该假设下，所选同构 [`2 (D (Incl C S a))] 也可能是 [a] 的非恒等自同构，因此余单位仍不一定是恒等的。因此，这样的假设是不充分的，上文提供的例子正是一个不满足该假设的情况。Mac Lane 的备注要求所选同构必须也是恒等的，这就是他所说的“并且 eta_{Ka} 为恒等”的意思。对于该情况，也没有声称 [eq_refl] 恒等：通过余单位读取出的三角恒等式是一个 [approx] 方程。** 骷髅骑士，以及关于事件顺序的说明Mac Lane的“这特别包括已经提到的情况，当A是C的骨架时”是[skeleton_IsoDense]和[skeleton_reflective]：一个[Skeleton]（Theory/Skeleton.v）携带[skel_rep]和[skel_iso]，它们是同构密度数据，且同构方向相反，所以[skeleton_IsoDense]将[skel_rep]与该域的[iso_sym]配对，仅此而已。这个附加条件在这棵树中是不寻常的，因为特殊情况先于一般陈述：Theory/Skeleton.v已经通过完全相同的路径证明了[skeleton_inclusion_is_equivalence]，并且已经将[skel_reflect]定义为它的拟逆。缺失的是作为一等公理的假设、反射器在左手偏向下的伴随等价，以及结论[Reflective]。因为两个 ESO 记录在字段上是一致的，并且 [EssentiallySurjective] 有 eta，一般定理在骨架上的反射器确实是 [skel_reflect]（[skeleton_reflector_is_skel_-reflect], [eq_refl]），所以没有第二个反射器进入树中。

 ** 宇宙使用 [About] 和 [Set Printing Universes] 测量所有 26 个常数、绑定器和块。每个常数都在 [C : Category@{u u0 u0}] 之上——在 BINDER 中通过重新使用级别进行证明同构识别——并且这种识别继承自 [Subcategory@{u u0 u1 u2}]，它在 [Category@{u u0 u0}] 上以 EMPTY 约束块声明；探针通过在一个证明宇宙被严格声明在其同构宇宙之上的类别中拒绝 [Subcategory Cu] 来固定它，并在这些级别接受该类别的同构集合、恒等和同构类。二十一个约束块不携带方程，仅有界限。五个携带
 恰好一个，[u0 = u2]，且它们恰好是
 [dense_full_subcategory_reflective] 及其四个 [eq_refl] 回读——
 四个骨架常量包 [Reflective] 也携带零——
 因为 [Reflective@{u u0 u1 u2 u3 u4 u5}] 在 [Subcategory@{u3 u5 u4 u5} C] 上被声明，实例化了 [Subcategory] 的第四个
 宇宙在 C 的同伦级，其中 [Subcategory] 本身让它自由，因此
 方程属于记录而非此文件——[dense_adj]，
 [dense_reflector] 和 [dense_incl_equivalence] 不携带任何。没有绑定器、
 块或 26 的宇宙实例包含标记 [Set]。没有
 这些标识被声明为不可避免。

 ** 见证（在探测中，所以此文件的闭包保持精简）Test/ProbeDense375.v 在两个地方实例化了定理
 [Indiscrete bool]  (Instance/Discrete/Reconstruct.v，其 hom 和
 proof 宇是字面上的 [Set]  —— 一个见证的固定点，而
 本文件不包含): 一次通过 [skeleton_reflective] 在
 Theory/Skeleton/Separation.v 的 [Indiscrete_bool_Skeleton] 上，其中在非代表性点处证明了反射不是惰性的，
 一次在一个全子范畴上，覆盖两个点，其每个点的选定代表是另一个点，即上面余单位段落背后的见证。

 ** 先前工作，以及四项已过时的问题主张

 在该分支的基础提交上测量，针对 .v 文件:(a) 该问题指出没有通用的 [Faithful (Incl C S)] 实例，并且包含的忠实性在评论中被断言，并且按实例证明。错误：Construction/Subcategory.v 是 [Lemma Incl_Faithful : Functor.Faithful Incl]，被 Theory/Skeleton.v、Adjunction/FullFaithful.v 和 Construction/Reflective/Limit.v 等使用。这里没有任何东西重建它。

 (b) 该问题中几个捐赠者行号已经漂移。在此基础上，该问题遗漏了 Construction/Subcategory.v 中的 [Incl]、[Full] 和 [Full_Implies_Full_Functor]，以及 Theory/Equivalence.v 中的 [EssentiallySurjective]。它对 [FF_ESO_Equivalence] 和 [Equivalence_to_AdjointEquivalence] 的引用是正确的。(c) 问题指出 [FF_ESO_Equivalence] 的现有应用不是子类别包含。陈旧：Theory/Skeleton.v 将其应用于 [skel_incl S]，而 [skel_incl S] 是 [Sub] 的 [Incl]。（Instance/FinSet/Skeleton.v 也将其应用于一个名为 [FinSet_Incl] 的函子，但那个是手工构建的 [Program Definition]，根本不是 [Incl C S]。）因此，对一个子类别包含的特化在 skeleton 中存在；不存在的是上段中测量的内容。

 (d) 问题将 skeleton 推论推迟到 skeleton 开发完成。它已经完成：Theory/Skeleton.v 存在并声明了 [Record Skeleton]，所以推论在这里交付。搜索在相同的基础上运行：[IsoDense]、[iso_dense] 和 [dense_full_subcategory_reflective] 在此文件及其探针之外没有命中，而 [Build_Reflective] 则正好有四个应用位置（Construction/Reflective/Idempotent.v、Instance/Ord/Poset.v、Instance/Ab/TorsionFree.v、Instance/Top/Kolmogorov.v），其中没有一个是通过等价关系获得的；第五个文本命中，Instance/Ab/TorsionFree.v，是一个引用搜索字符串的注释。

 ** 注册此文件中没有任何内容被注册用于实例解析，遵循 Theory/Equivalence.v 和 Theory/Equivalence/FullFaithful.v 的规则，它们自己说明：一个准逆元和一个被选的原像对象是选择项，必须明确传递。[EssentiallySurjective] 是一个类，因此如果将 [iso_dense_ESO] 声明为 [Instance]，它将可解析；它故意是一个普通的 [Definition]。

 ** 未交付同一页的练习4（G的左伴随左逆使G成为到反射子范畴的同构）是一个单独的目录条目，没有尝试。命题的逆命题——一个单位为分量同构的反射子范畴是同构稠密的——没有说明。关于[Coreflective]、在任何变量中选择[D]的自然性，或反射子唯一性，没有任何说明。
*)

Section Dense.

Context {C : Category}.
Context (S : Subcategory C).

(** ** The hypothesis / ** 假设 *)

(*
 Mac Lane's “every c in C is isomorphic (in C) to some object of A”, with
 the object chosen.  The sigma is Type-valued, so the representative and
 the isomorphism are both DATA. 

 --------
 Mac Lane 的“C 中的每个 c 在 C 中与 A 的某个对象同构”，并选择该对象。Sigma 是类型值，因此代表和同构都是数据。
*)

Definition IsoDense : Type :=
  ∀ c : C, { a : Sub C S & Incl C S a ≅ c }.

(*
 ... which is [EssentiallySurjective] for the inclusion, field for
 field.  A plain [Definition], raising no obligation. 

 --------
 ... 对于逐字段包含，它是 [EssentiallySurjective]。一个普通的 [Definition]，不引起任何义务。
*)

Definition iso_dense_ESO (D : IsoDense) :
  EssentiallySurjective (Incl C S) :=
  {| eso_obj := fun c => `1 (D c)
   ; eso_iso := fun c => `2 (D c) |}.

Example iso_dense_ESO_obj (D : IsoDense) (c : C) :
  @eso_obj _ _ _ (iso_dense_ESO D) c = `1 (D c) := eq_refl.

(* ... and back. *)

Definition ESO_iso_dense (E : EssentiallySurjective (Incl C S)) :
  IsoDense :=
  fun c => (@eso_obj _ _ _ E c; @eso_iso _ _ _ E c).

Example ESO_iso_dense_obj (E : EssentiallySurjective (Incl C S)) (c : C) :
  `1 (ESO_iso_dense E c) = @eso_obj _ _ _ E c := eq_refl.

(* One round trip closes on the WHOLE record, because [EssentiallySurjective] is a two-field class and Lib.v sets [Set Primitive Projections]. / 一次往返会关闭整个记录，因为 [EssentiallySurjective] 是一个两字段类，并且 Lib.v 设置了 [Set Primitive Projections]。 *)

Example ESO_round_whole (E : EssentiallySurjective (Incl C S)) :
  iso_dense_ESO (ESO_iso_dense E) = E := eq_refl.

(*
 The other closes only on the object component: stdlib [sigT] has no eta,
 so the [IsoDense] whole record does not return.  Refuted and pinned in
 Test/ProbeDense375.v. 

 --------
 另一个仅在对象组件上关闭：stdlib [sigT] 没有 eta，因此 [IsoDense] 整个记录不会返回。在 Test/ProbeDense375.v 中被反驳并固定。
*)

Example iso_dense_round_obj (D : IsoDense) (c : C) :
  `1 (ESO_iso_dense (iso_dense_ESO D) c) = `1 (D c) := eq_refl.

Context (F : Subcategory.Full C S).

(* * ** (1) The insertion is an equivalence / * ** (1) 插入是等价的 *)

(*
 [Incl_Faithful] appears here, in a [:=] with no tactic; the reviewer
 check for this issue is that the generic lemma is consumed rather than
 bypassed. 

 --------
 [Incl_Faithful] 出现在这里，在一个没有策略的 [:=] 中；审阅者检查此问题的方法是通用引理被使用而不是被绕过。
*)

Definition dense_incl_equivalence (D : IsoDense) :
  EquivalenceOfCategories (Incl C S) :=
  @FF_ESO_Equivalence _ _ (Incl C S)
    (Full_Implies_Full_Functor C S F)
    (Incl_Faithful C S)
    (iso_dense_ESO D).

(*
 The quasi-inverse acts on objects by the chosen representative:
 [FF_ESO_Equivalence] is [Defined] and [ff_eso_inverse]'s [fobj] is
 [eso_obj], so this reduces all the way. 

 --------
 准逆通过选择的代表作用于对象：
 [FF_ESO_Equivalence] 是 [Defined]，[ff_eso_inverse] 的 [fobj] 是 [eso_obj]，所以这一路归约。
*)

Example dense_incl_quasi_obj (D : IsoDense) (c : C) :
  fobj[@quasi_inverse _ _ _ (dense_incl_equivalence D)] c = `1 (D c)
  := eq_refl.

(* * ** (2) The adjoint equivalence, in both handednesses / * **（2）伴随等价，在两种手性中 *)

(* Mac Lane's triple read with the insertion on the LEFT. / Mac Lane的三重读法，插入在左边。 *)

Definition dense_incl_adjoint_equivalence (D : IsoDense) :
  AdjointEquivalence (Incl C S)
    (@quasi_inverse _ _ _ (dense_incl_equivalence D)) :=
  Equivalence_to_AdjointEquivalence (dense_incl_equivalence D).

(* Mac Lane's T. / 麦克莱恩的T *)

Definition dense_reflector (D : IsoDense) : C ⟶ Sub C S :=
  @quasi_inverse _ _ _ (dense_incl_equivalence D).

Example dense_reflector_obj (D : IsoDense) (c : C) :
  fobj[dense_reflector D] c = `1 (D c) := eq_refl.

(*
 ... and the reflection adjunction T -| K, the handedness the
 [Reflective] record asks for. 

 --------
 ...以及反射伴随 T -| K，记录 [Reflective] 所要求的手性。
*)

Definition dense_adj (D : IsoDense) : dense_reflector D ⊣ Incl C S :=
  AdjointEquivalence_swap_adjunction (dense_incl_adjoint_equivalence D).

(** ** (4) Reflectivity / **（4）反射率 *)

Definition dense_full_subcategory_reflective (D : IsoDense) : Reflective S :=
  @Build_Reflective C S F (dense_reflector D) (dense_adj D).

Example dense_reflective_reflector (D : IsoDense) :
  reflector (dense_full_subcategory_reflective D) = dense_reflector D
  := eq_refl.

Example dense_reflective_adj (D : IsoDense) :
  reflective_adj (dense_full_subcategory_reflective D) = dense_adj D
  := eq_refl.

Example dense_reflective_full (D : IsoDense) :
  reflective_full (dense_full_subcategory_reflective D) = F := eq_refl.

Example dense_reflective_obj (D : IsoDense) (c : C) :
  fobj[reflector (dense_full_subcategory_reflective D)] c = `1 (D c)
  := eq_refl.

(* * ** (3) The counit, as an isomorphism / * **（3）余单位，作为一个同构 *)

(*
 [:=] with no tactic: the swapped adjoint equivalence carries this as a
 field. 

 --------
 [:=] 没有策略：交换的伴随等价将其作为一个场。
*)

Definition dense_counit_iso (D : IsoDense) (a : Sub C S) :
  IsIsomorphism (@counit _ _ _ _ (dense_adj D) a) :=
  @adj_equiv_counit_iso _ _ _ _
    (AdjointEquivalence_swap (dense_incl_adjoint_equivalence D)) a.

(*
 The bundled reading, in [Sub C S].  Its forward leg is the counit on the
 nose, recorded below; contrast [reflective_counit_iso]
 (Construction/Reflective.v), which states the same fact at the level
 of the [Reflective] record but is closed with [Qed] while producing
 data, so neither of its legs reduces. 

 --------
 捆绑的读数，在 [Sub C S] 中。它的前支是鼻上的余单位，记录如下；对比 [reflective_counit_iso]（Construction/Reflective.v），它在 [Reflective] 记录的层面上陈述了相同的事实，但以 [Qed] 结束，同时生成数据，所以它的任何一条支路都不会简化。
*)

Definition dense_counit_Isomorphism (D : IsoDense) (a : Sub C S) :
  dense_reflector D (Incl C S a) ≅[Sub C S] a :=
  @IsIsoToIso (Sub C S) _ _ _ (dense_counit_iso D a).

Example dense_counit_Isomorphism_to (D : IsoDense) (a : Sub C S) :
  to (dense_counit_Isomorphism D a)
    = @counit _ _ _ _ (dense_adj D) a := eq_refl.

End Dense.

Arguments IsoDense {C} S.

(** ** The skeleton rider / ** 骷髅骑士 *)

(*
 Mac Lane's “This includes in particular the case already noted, when A
 is a skeleton of C”.  [skel_iso] is stated in the reverse orientation,
 so the whole content of this passage is [iso_sym]. 

 --------
 Mac Lane 的“这特别包括先前提到的情况，当 A 是 C 的骨架”。[skel_iso] 是以相反的方向说明的，所以这一段的整个内容是 [iso_sym]。
*)

Definition skeleton_IsoDense {C : Category} (Sk : Skeleton C) :
  IsoDense (skel_sub Sk) :=
  fun c => (skel_rep Sk c; iso_sym (skel_iso Sk c)).

Definition skeleton_reflective {C : Category} (Sk : Skeleton C) :
  Reflective (skel_sub Sk) :=
  dense_full_subcategory_reflective (skel_sub Sk) (skel_full Sk)
    (skeleton_IsoDense Sk).

Example skeleton_reflector_obj {C : Category} (Sk : Skeleton C) (c : C) :
  fobj[reflector (skeleton_reflective Sk)] c = skel_rep Sk c := eq_refl.

(*
 The reflector produced by the general theorem IS Theory/Skeleton.v's
 [skel_reflect], on the nose: the two [EssentiallySurjective] records
 agree field for field, and that class has eta. 

 --------
 由一般定理产生的反射器是 Theory/Skeleton.v 的 [skel_reflect]，准确无误：两个 [EssentiallySurjective] 记录在每一字段上都一致，并且该类具有 eta。
*)

Example skeleton_reflector_is_skel_reflect {C : Category} (Sk : Skeleton C) :
  reflector (skeleton_reflective Sk) = skel_reflect Sk := eq_refl.

Example skeleton_reflective_full {C : Category} (Sk : Skeleton C) :
  reflective_full (skeleton_reflective Sk) = skel_full Sk := eq_refl.
