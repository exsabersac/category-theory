Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Theory.Subobject.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Theory.Universal.Element.

Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(* * * A universal element for the contravariant power-set functor / * * 余变幂集函子的一般元素 *)

(*
 nLab:      https://ncatlab.org/nlab/show/universal+element
 nLab:      https://ncatlab.org/nlab/show/subobject+classifier
 Wikipedia: https://en.wikipedia.org/wiki/Power_set

 Mac Lane asks (CWM 2nd ed., §III.1, Exercise 2, printed p. 59) for a
 universal element of the contravariant power-set functor, and the
 classical answer is the pair ⟨2, {1}⟩: every subset S ⊆ A is the
 preimage of the distinguished truth value under exactly one map
 A ⟶ 2.  Riehl states the same example (Category Theory in Context,
 2nd ed., §2.3 Example 2.3.6, printed p. 68) with an emphasis that is
 a correctness condition rather than a flourish: the universal element
 is the SUBSET {⊤} ∈ P(Ω) — an element of the functor's VALUE at Ω —
 and not the POINT ⊤ ∈ Ω, the isomorphism being the one that carries
 f : A ⟶ Ω to the subset f⁻¹(⊤) ⊆ A.  Awodey runs the same
 correspondence for Sets (Category Theory, §5.3 Example 5.14, printed
 pp. 104-106), where the punchline is that it is NATURAL in the object.

 The section-and-page coordinates and the one-line summaries of what
 those passages contain are reproduced from the catalogue entry of the
 issue this file answers (jwiegley/category-theory#311, items
 maclane:III.1:ex2, riehl:2.3:example6, awodey:5.3:example14); the
 printed texts were not consulted while writing the file, so every
 statement here about their content is the issue's characterization
 rather than a reading of the books.  The mathematics below stands on
 its own proofs.

 A CORRECTION TO THAT ISSUE'S ACCOUNT OF THE PRIOR ART, measured
 against the parent commit rather than restated from the issue.  Its
 "Current state" says the library has "no power-set functor on a
 set-like category with a III.1-style universal-element statement",
 which read as a claim about power-set functors would be wrong:
 Instance/Sets/Powerset.v (issue #227) already contains FOUR of them —
 [Powerset], [Powerset_op], [Powerset_Prop] and [Powerset_Prop_Lift] —
 and they are substantial.  Three separate things were genuinely
 absent, and they are what these files add:

 (a) a CONTRAVARIANT power-set functor at a SINGLE universe level.
 The donor's contravariant one, [Powerset_op], is
 [(Sets@{o so})^op ⟶ Sets@{so sso}] — its codomain is one
 universe up — and its one-level functor, [Powerset_Prop], is
 COVARIANT.  Neither shape can be the [H] of a universal element
 over [Sets], which needs [H : D ⟶ Sets] for the same [Sets].

 (b) a universal-element statement for ANY power-set functor: no
 [UniversalElement] or [AUniversalElement] anywhere in the tree
 mentioned one.

 (c) the natural-isomorphism upgrade of [classifier_classifies].
 That theorem was per-object, and [Sub] had never been exhibited
 as a representable presheaf.  The upgrade is
 Structure/SubobjectClassifier/Natural.v, delivered for an
 ARBITRARY [SubobjectClassifier] rather than only here.

 THE LEAD THE ISSUE DID NOT TAKE, AND WHY IT WORKS.  The issue proposes
 building this over [FinSet] "where it exists at one universe level",
 taking for granted that [Sets] does not.  [Sets] does.  The donor
 needed the impredicative truncation [Powerset_squash] because the
 DIRECT image has an existential ([λ y, ∃ x, S x ∧ f x ≈ y]) that must
 be squashed to land in [Prop].  The INVERSE image is [λ y, T (f y)]: a
 composition, with no quantifier introduced, so a [Prop]-valued subset
 pulls back to a [Prop]-valued subset with nothing to truncate.
 [Powerset_squash] therefore appears NOWHERE in the construction of
 [Powerset_Prop_op] below.  It reappears in the universal ELEMENT,
 because the donor's singleton is truncated uniformly, and later in the
 direct-image comparison and the subobject section; and at
 Ω that truncation is INERT, which is proved rather than asserted
 ([powerset_squash_prop_inert]: over a [Prop] the squash is
 interderivable with its argument, by impredicativity).  So the tree
 had built the hard half of the power-set story and left the easy half
 undone.

 The pay-off is that [Powerset_Prop_op] and its domain live in the SAME
 [Sets@{o so}], which is what [AUniversalElement (H : D ⟶ Sets) r]
 requires of [H].  Nothing here is a workaround: no cumulativity
 assumption, no disabled universe checking, no axiom.  Impredicativity
 of [Prop] is used exactly where the donor uses it and for the same
 reason — it is what puts a [Prop]-valued predicate setoid at the level
 of the carriers.

 ONE DONOR RESTRICTION BITES, AND IT IS MEASURED RATHER THAN GUESSED.
 [Theory/Universal/Element.v] records that [Yoneda_Lemma] — and hence
 [universal_element_yoneda] and [universal_element_representation] — is
 stated over [C : Category@{u0 u0 u0}], with object, hom and proof
 universes IDENTIFIED, so it cannot be instantiated at a category whose
 objects sit strictly above its homs.  [Sets@{o so} : Category@{so o o}]
 is exactly such a category: its objects live at [so] and its homs at
 [o], with [o < so] forced.  The Yoneda route is therefore unavailable
 here, and the refusal is a genuine universe inconsistency, of the form
 "Cannot enforce _ = _ because _ < _" naming the two anonymous levels;
 it is pinned in Test/ProbePowersetUniversal.v against a positive
 control that uses the direct route at the same arguments.  Everything
 below accordingly goes through the Yoneda-FREE constructions
 [ue_transform], [ue_representation] and [AUniversalElement_of_repr]
 that the donor file built for this situation.  This file is a second
 instance of that restriction (the first being Instance/Coq/Nat.v's
 [Endos]), not an escape from it.

 WHAT THIS FILE DELIVERS, AND AT WHICH STRENGTH.

 (1) [Powerset_Prop_op] — the CONTRAVARIANT power-set functor at ONE
 universe level, [(Sets@{o so})^op ⟶ Sets@{o so}], with subsets
 [Prop]-valued and the action the inverse image.

 (2) [Powerset_Prop_universal_element] — Mac Lane's §III.1 clause
 verbatim, through [Theory/Universal/Element.v]'s
 [AUniversalElement]: the pair ⟨Ω, {⊤}⟩, with Ω the level-o
 truth-value setoid and {⊤} the singleton subset of it.

 (3) Riehl's emphasis, machine-checked twice over: the universal
 element is TYPED as an element of [Powerset_Prop_obj Ω] rather
 than of Ω (the probe file pins the point's rejection in the
 element's position as a type error, against a control), and the
 forward leg of the representing isomorphism IS the preimage of
 {⊤}, by [eq_refl] ([powerset_representation_to_is_preimage]).

 (4) [Powerset_representation] — the representation
 [Hom ─,Ω] ≅ P as an isomorphism in [[Sets^op, Sets]], which is
 Awodey's naturality clause FOR THE POWER SET.  His naturality
 clause for the SUBOBJECT functor is a different statement about
 a different functor, and it is delivered separately, for an
 arbitrary [SubobjectClassifier], in
 Structure/SubobjectClassifier/Natural.v.

 HOW MUCH CONTENT IS IN THIS, STATED PLAINLY, because the packaging
 reads stronger than the mathematics.  In this library a [Prop]-valued
 subset of A IS a map A ~> Ω — the two types are equal by [eq_refl]
 ([powerset_subsets_are_maps]) — so the correspondence is not a
 bijection between two different things.  Its entire content is the
 single equivalence "membership in {⊤} detects truth"
 ([Powerset_truth_subset_intro] / [Powerset_truth_subset_elim]), and
 everything else is bookkeeping around those two lines.  The companion
 file Instance/FinSet/Powerset.v answers the same exercise where
 nothing is definitional — the power set of the n-element set is the
 2^n-element set, subsets are elements of it, and the correspondence
 computes — and the two files are deliberately both shipped for that
 contrast.

 WHAT THIS FILE DOES NOT DELIVER, STATED PLAINLY.  It does not produce
 a [SubobjectClassifier Sets] instance, and it does not claim
 [Powerset_Prop_obj A] and [SubObj A] are isomorphic.  The last section
 proves the half that is true — every [Prop]-valued subset is recovered
 from the subobject it names — and says exactly what blocks the other
 half.  See "The classifier obstruction is a different obstruction"
 below. 

 --------
 nLab：       https://ncatlab.org/nlab/show/universal+element
 nLab：       https://ncatlab.org/nlab/show/subobject+classifier
 维基百科：  https://en.wikipedia.org/wiki/Power_setMac Lane 在《CWM》第2版，第III.1节，练习2（印刷版第59页）中询问了共变幂集函子（contravariant power-set functor）的一个通用元素，经典答案是对 ⟨2, {1}⟩：每个子集 S ⊆ A 都恰好是通过唯一一个映射 A ⟶ 2 对区分真值的原像。Riehl 在《Category Theory in Context》第2版，第2.3节示例2.3.6（印刷版第68页）中提出了相同的例子，并强调这是一个正确性条件，而不是修饰：通用元素是子集 {⊤} ∈ P(Ω)——函子的 Ω 点值的元素——而不是点 ⊤ ∈ Ω，那个同构将 f : A ⟶ Ω 映射到子集 f⁻¹(⊤) ⊆ A。Awodey 在《Category Theory》第5.3节示例5.14（印刷版第104-106页）中对集合（Sets）进行了相同的对应，其中关键点是它在对象上是自然的（NATURAL）。这些段落所在的章节和页码坐标，以及对这些段落内容的一行总结，是从本文件所回答的问题的目录条目中摘录的（jwiegley/category-theory#311，条目 maclane:III.1:ex2，riehl:2.3:example6，awodey:5.3:example14）；在撰写此文件时没有参考印刷文本，因此这里关于它们内容的每一条陈述都是问题的描述，而不是对书籍的阅读。下面的数学内容依靠其自身的证明成立。对该问题中关于现有技术的描述的更正，是相对于父提交进行的衡量，而不是从问题中重新陈述。其“当前状态”称该库在“类集合范畴上没有 III.1 风格普遍元素陈述的幂集函子”，如果将其解读为关于幂集函子的主张就是错误的：Instance/Sets/Powerset.v（问题 #227）已经包含了四个这样的函子——[Powerset]、[Powerset_op]、[Powerset_Prop] 和 [Powerset_Prop_Lift]——而且它们都是重要的。实际上有三样东西真正缺失，它们就是这些文件所添加的内容：(a) 在单一宇宙层次上的一个逆变幂集函子。捐赠者的逆变函数 [Powerset_op] 是 [(Sets@{o so})^op ⟶ Sets@{so sso}] ——它的余域高一个宇宙层次——且它的单层次函子 [Powerset_Prop] 是共变的。没有哪种形状可以成为 [H] 在 [Sets] 上的一个通用元元素，这需要 [H : D ⟶ Sets] 来实现相同的 [Sets]。

 (b) 对于任何幂集函子的通用元素陈述：在所提树中，无论哪里都没有 [UniversalElement] 或 [AUniversalElement]。

 (c) [classifier_classifies] 的自然同构升级。该定理是针对对象的，并且 [Sub] 从未被展示为可表示的预层。这个升级位于 Structure/SubobjectClassifier/Natural.v，为任意 [SubobjectClassifier] 提供，而不仅仅是此处。问题没有采纳这个线索，以及它为何有效。该问题建议在 [FinSet] 上构建“它在一个宇宙层次上存在”，并理所当然地认为 [Sets] 不存在。而 [Sets] 是存在的。供体需要不可递归截断 [Powerset_squash]，因为直接像有一个存在量词 ([λ y, ∃ x, S x ∧ f x ≈ y])，必须被压缩才能落入 [Prop]。逆像是 [λ y, T (f y)]：一个组合，没有引入量词，因此 [Prop] 值的子集拉回到 [Prop] 值的子集时没有需要截断的部分。因此 [Powerset_squash] 在下面 [Powerset_Prop_op] 的构造中根本不存在。它在通用 ELEMENT 中重新出现，因为供体的单例被均匀截断，并且随后出现在直接映像比较和子对象部分；在 Ω 上，这种截断是惰性的，这一点是被证明而不是被断言的（[powerset_squash_prop_inert]：在 [Prop] 上，通过自反性，压缩与其论元是相互可推导的）。所以这棵树已经构建了幂集故事的困难部分，而轻松部分还未完成。收益在于 [Powerset_Prop_op] 及其领域位于同一 [Sets@{o so}] 中，这正是 [AUniversalElement (H : D ⟶ Sets) r] 对 [H] 的要求。这里没有任何变通方法：没有累积性假设，没有禁用宇宙检查，没有公理。[Prop] 的不可支配性正是在供体使用它的地方并且出于相同的原因使用——它使一个 [Prop] 值的谓词集合体处于承载者的层级。一个供体限制产生问题，并且它是被测量的而不是猜测的。[Theory/Universal/Element.v] 记录了 [Yoneda_Lemma] — 从而也记录了 [universal_element_yoneda] 和 [universal_element_representation] — 被声明在 [C : Category@{u0 u0 u0}] 上，对象、同态和证明宇宙已被确定，因此它不能在对象严格高于其同态的范畴中被实例化。[Sets@{o so} : Category@{so o o}] 正好就是这样一个范畴：它的对象位于 [so]，而其同态位于 [o]，其中 [o < so] 被强制。因此，Yoneda 路径在这里不可用，而这种拒绝是真正的宇宙不一致，其形式为“无法强制 _ = _ 因为 _ < _”，命名两个匿名层级；它在 Test/ProbePowersetUniversal.v 中被固定，对照使用相同参数的直接路径作为阳性控制。以下内容相应地通过 Yoneda-FREE 构造 [ue_transform]、[ue_representation] 和 [AUniversalElement_of_repr] 进行，而这些构造是捐赠文件为此情境建立的。这个文件是该限制的第二个实例（第一个是 Instance/Coq/Nat.v 的 [Endos]），而不是对它的规避。

 这个文件提供的内容，以及其强度。

 (1) [Powerset_Prop_op] — 单个宇宙层级上的逆变幂集函子 [(Sets@{o so})^op ⟶ Sets@{o so}]，其子集取值为 [Prop]，操作为逆像。

 (2) [Powerset_Prop_universal_element] — Mac Lane 的 §III.1 条款逐字演绎，通过 [Theory/Universal/Element.v] 的 [AUniversalElement]：对 ⟨Ω, {⊤}⟩，其中 Ω 是层级 0 的真值集合等价类，{⊤} 是它的单元素子集。(3) Riehl 强调的内容，经机器两次检查：通用元素被类型化为 [Powerset_Prop_obj Ω] 的一个元素，而不是 Ω 的元素（探针文件将该点在元素中的位置作为类型错误的拒绝记录，与控制相比），并且代表同构的前向分支确实是 {⊤} 的原像，由 [eq_refl] ([powerset_representation_to_is_preimage]) 给出。

 (4) [Powerset_representation] — 表示 [Hom ─,Ω] ≅ P 作为 [[Sets^op, Sets] 中的一个同构，这是 Awodey 的幂集自然性条款。他对于子对象函子（SUBOBJECT functor）的自然性条款是关于不同函子的不同陈述，并且它被单独给出，对于任意 [SubobjectClassifier]，在 Structure/SubobjectClassifier/Natural.v 中。这个内容到底有多少，说得明白点，因为包装看上去比数学本身还要复杂。在这个库里，一个取值于  A 的 [Prop] 子集是一个映射 A ~> Ω——这两种类型通过 [eq_refl] ([powerset_subsets_are_maps]) 是相等的——所以这种对应关系并不是两个不同事物之间的双射。它的全部内容就是那个单一的等价关系“属于 {⊤} 检测真值” ([Powerset_truth_subset_intro] / [Powerset_truth_subset_elim])，其余的一切都是围绕这两行的记录工作。配套文件 Instance/FinSet/Powerset.v 回答了同样的练习题，但没有任何定义性内容——n 元集合的幂集是一个 2^n 元集合，子集是它的元素，并且该对应关系可以计算——这两个文件是故意都提供的，以便进行这种对比。本文件明确说明它不提供的内容。它不会生成一个 [SubobjectClassifier Sets] 实例，也不声称 [Powerset_Prop_obj A] 和 [SubObj A] 是同构的。最后一节证明了其中正确的一半——每个 [Prop] 值的子集都可以从其命名的子对象中恢复——并准确说明了另一半受阻的原因。见下文“分类器障碍是不同的障碍”。
*)

(* ------------------------------------------------------------------------ *)
(* * ** The inverse image, and the contravariant functor / * ** 逆像，以及逆变函子 *)

(*
 The inverse image of [T ⊆ X] along [f : Y ~> X] is [λ y, T (f y)] — the
 underlying predicate of [T] composed with the underlying function of
 [f].  Respectfulness is the two respectfulnesses composed. 

 --------
 沿着 [f : Y ~> X] 的 [T ⊆ X] 的逆像是 [λ y, T (f y)] —— [T] 的底层谓词与 [f] 的底层函数的组合。尊重性是两个尊重性的组合。
*)

Definition Powerset_Prop_preimage@{o} {X Y : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} Y X)
  (T : carrier (Powerset_Prop_obj@{o} X)) :
  carrier (Powerset_Prop_obj@{o} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier Y) (is_setoid Y) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ y, T (f y)) _).
  intros y y' Hyy'.
  exact (@proper_morphism _ _ _ _ T (f y) (f y')
           (proper_morphism f _ _ Hyy')).
Defined.

(* Taking inverse images is itself a setoid map on subsets. / 取逆像本身就是子集上的一类集合映射。 *)
Definition Powerset_Prop_comap@{o} {X Y : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} Y X) :
  SetoidMorphism@{o o o} (Powerset_Prop_obj@{o} X) (Powerset_Prop_obj@{o} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier (Powerset_Prop_obj@{o} X)) (is_setoid (Powerset_Prop_obj@{o} X))
       (carrier (Powerset_Prop_obj@{o} Y)) (is_setoid (Powerset_Prop_obj@{o} Y))
       (λ T, Powerset_Prop_preimage@{o} f T) _).
  intros T U HTU y; exact (HTU (f y)).
Defined.

Lemma Powerset_Prop_comap_respects@{o} {X Y : SetoidObject@{o o}}
  (f g : SetoidMorphism@{o o o} Y X) (H : f ≈ g) :
  Powerset_Prop_comap@{o} f ≈ Powerset_Prop_comap@{o} g.
Proof.
  intros T y; split; intro Ht.
  - exact (proj1 (@proper_morphism _ _ _ _ T (f y) (g y) (H y)) Ht).
  - exact (proj2 (@proper_morphism _ _ _ _ T (f y) (g y) (H y)) Ht).
Qed.

(*
 [fmap_id] and [fmap_comp] are both a pair of identity implications: the
 inverse image along the identity is the subset itself ON THE NOSE as a
 predicate, and the inverse image along a composite is the iterated
 inverse image, again on the nose.  Only the setoid packaging keeps
 these from being [eq_refl]; the two [split; intro Ht; exact Ht] proofs
 below record exactly that.
 CORRECTION (#1347): since Instance/Sets.v gives its identity's and
 composite's properness fields as terms, both laws hold at [eq_refl] as
 equations of setoid morphisms: the identity law is a control of
 Test/ProbePowersetUniversal.v, its boundary (5), and so is the
 composition law ([powerset_fmap_comp_strict]), which a copy of the
 probe as it stood at master 687ac356, compiled against that tree,
 refuses.  The two proofs below are unchanged. 

 --------
 [fmap_id] 和 [fmap_comp] 都是一对恒等蕴含：沿恒等映射的逆像作为谓词正好是子集自身，而沿复合映射的逆像正好是迭代逆像。同一集合的封装只是让这些不成为 [eq_refl]；下面的两个 [split; intro Ht; exact Ht] 证明正好记录了这一点。
 修正 (#1347)：由于 Instance/Sets.v 将其恒等映射和复合映射的适当性字段以项的形式给出，因此这两个定律在 [eq_refl] 上均成立，作为集合态射的方程：恒等律控制了 Test/ProbePowersetUniversal.v，其边界 (5)，复合律也是如此 ([powerset_fmap_comp_strict])，这是在 master 687ac356 时的探针副本，对应编译树拒绝。下面的两个证明保持不变。
*)
Lemma Powerset_Prop_comap_id@{o} {X : SetoidObject@{o o}} :
  Powerset_Prop_comap@{o} (@setoid_morphism_id@{o o o} X)
    ≈ @setoid_morphism_id@{o o o} (Powerset_Prop_obj@{o} X).
Proof. intros T x; split; intro Ht; exact Ht. Qed.

Lemma Powerset_Prop_comap_comp@{o} {X Y Z : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} Z Y) (g : SetoidMorphism@{o o o} Y X) :
  Powerset_Prop_comap@{o} (@setoid_morphism_compose@{o o o} Z Y X g f)
    ≈ @setoid_morphism_compose@{o o o}
        (Powerset_Prop_obj@{o} X) (Powerset_Prop_obj@{o} Y)
        (Powerset_Prop_obj@{o} Z)
        (Powerset_Prop_comap@{o} f) (Powerset_Prop_comap@{o} g).
Proof. intros T z; split; intro Ht; exact Ht. Qed.

(* THE CONTRAVARIANT POWER-SET FUNCTOR, at one level. Compare [Powerset_op] of the donor file, whose codomain is [Sets] one universe up. / 反变幂集函子，在一个层次上。比较捐赠文件的 [Powerset_op]，其对域是 [Sets]，上一个宇宙。 *)
Definition Powerset_Prop_op@{o so} : @Functor (Sets@{o so})^op Sets@{o so}.
Proof.
  unshelve refine
    (@Build_Functor (Sets@{o so})^op Sets@{o so}
       Powerset_Prop_obj@{o}
       (fun (X Y : SetoidObject@{o o}) (f : Y ~{Sets@{o so}}~> X) =>
          Powerset_Prop_comap@{o} f) _ _ _).
  - intros X Y f g H; exact (Powerset_Prop_comap_respects@{o} f g H).
  - intros X; exact (@Powerset_Prop_comap_id@{o} X).
  - intros X Y Z f g; exact (@Powerset_Prop_comap_comp@{o} X Y Z f g).
Defined.

(*
 [fmap[Powerset_Prop_op]] IS the inverse image: the two sides are the
 very same term, so the equality is Leibniz [=] rather than [≈].  This is
 the convertibility exception, on the Functor/Bifunctor.v
 precedent the donor file cites for its own five same-term lemmas. 

 --------
 [fmap[Powerset_Prop_op] 是逆像：两边是完全相同的项，所以等式是莱布尼茨 [=] 而不是 [≈]。这是可转换性的例外，在 Functor/Bifunctor.v 中，根据前例，源文件引用了自己的五个相同项的引理。
*)
Lemma Powerset_Prop_op_fmap_preimage@{o so} {X Y : SetoidObject@{o o}}
  (f : Y ~{Sets@{o so}}~> X) (T : carrier (Powerset_Prop_obj@{o} X)) :
  fmap[Powerset_Prop_op@{o so}] (f : X ~{(Sets@{o so})^op}~> Y) T
    = Powerset_Prop_preimage@{o} f T.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(* * ** Ω, the point ⊤, and the SUBSET {⊤} / * ** Ω，点 ⊤，以及子集 {⊤} *)

(*
 The truth-value object is the donor's [Powerset_Prop_truth]: carrier
 [Prop], equivalence mutual implication.  It is named here so that the
 statements below read as Mac Lane and Riehl write them, and the
 identification is recorded by [eq_refl] so the name adds nothing. 

 --------
 真值对象是捐赠者的 [Powerset_Prop_truth]：载体 [Prop]，等价互涵。这里命名它是为了使下面的陈述与 Mac Lane 和 Riehl 的写法一致，并且通过 [eq_refl] 记录了这种识别，所以这个名称没有增加任何信息。
*)
Definition Powerset_Omega@{o} : SetoidObject@{o o} := Powerset_Prop_truth@{o}.

Example powerset_Omega_is_truth@{o} :
  Powerset_Omega@{o} = Powerset_Prop_truth@{o} := eq_refl.

(* The POINT ⊤ ∈ Ω. / 点 ⊤ ∈ Ω。 *)
Definition Powerset_truth_point@{o} : carrier Powerset_Omega@{o} := True.

(*
 The SUBSET {⊤} ∈ P(Ω).  This — not the point above — is Mac Lane's e
 and Riehl's universal element.  It is the donor's singleton predicate
 at the point, so nothing new is constructed; what is new is that it is
 the second component of a universal pair. 

 --------
 子集 {⊤} 属于 P(Ω)。这——不是上面提到的点——是 Mac Lane 的 e 和 Riehl 的通用元素。它是在该点处捐赠者的单例谓词，因此没有构造新的东西；新的是它是一个通用对的第二个分量。
*)
Definition Powerset_truth_subset@{o} :
  carrier (Powerset_Prop_obj@{o} Powerset_Omega@{o}) :=
  Powerset_Prop_singleton_pred@{o} (X:=Powerset_Omega@{o})
    Powerset_truth_point@{o}.

Example powerset_truth_subset_is_singleton@{o} :
  Powerset_truth_subset@{o}
    = Powerset_Prop_singleton_pred@{o} (X:=Powerset_Omega@{o})
        Powerset_truth_point@{o} := eq_refl.

(*
 THE ELEMENT-VERSUS-POINT DISTINCTION, AT THE LEVEL OF TYPES.  The two
 live in different types, and the difference is not a matter of
 emphasis: [Powerset_truth_point] is a [carrier Powerset_Omega] and
 [Powerset_truth_subset] is a [carrier (Powerset_Prop_obj
 Powerset_Omega)].  Putting the point where the element belongs is a
 type error, and Test/ProbePowersetUniversal.v pins it as such against
 a positive control.  This lemma is the affirmative half: the two
 readings of "{⊤}" — the singleton subset, and the predicate "holds" —
 agree up to [≈] (and only up to [≈]; the strict form is refuted, and
 is pinned in the same probe file). 

 --------
 在类型层面上的元素与点的区分。两者属于不同的类型，这种差异不是强调的问题：[Powerset_truth_point] 是一个 [carrier Powerset_Omega]，而 [Powerset_truth_subset] 是一个 [承载器 (Powerset_Prop_obj Powerset_Omega)]。把点放到元素所属的位置是一个类型错误，Test/ProbePowersetUniversal.v 对其进行正控制验证。这个引理是肯定的一半：“{⊤}”的两种解释——单元素子集和谓词“成立”——在 [≈] 之前是一致的（且仅在 [≈] 之前一致；严格形式被驳斥，并在同一个测试文件中进行了固定）。
*)

(* The predicate "P holds", as a subset of Ω. / 作为 Ω 的一个子集的谓词“P 成立”。 *)
Definition Powerset_holds@{o} :
  carrier (Powerset_Prop_obj@{o} Powerset_Omega@{o}).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       Prop (is_setoid Powerset_Omega@{o})
       Prop (is_setoid Powerset_Prop_truth@{o})
       (λ P : Prop, P) _).
  intros P Q [HPQ HQP]; split; assumption.
Defined.

(*
 THE ONE PIECE OF MATHEMATICAL CONTENT IN THE WHOLE CORRESPONDENCE, in
 isolation: the singleton subset {⊤} of Ω DETECTS TRUTH.  Membership of
 [P] in {⊤} unfolds to [Powerset_squash (True ≈ P)], and the two
 implications below say that this squashed pair of implications is
 interderivable with [P] itself.  Everything after this section is
 bookkeeping around these two lines.

 The elimination direction is where impredicativity of [Prop] earns its
 keep: [Powerset_squash A] is [∀ Q : Prop, (A → Q) → Q], so eliminating
 it into the [Prop] goal [P] is instantiation at [Q := P] — legal
 precisely because [P] is a [Prop].  (Into a [Type]-valued goal it would
 not be, which is the donor's own reason for the truncation.) 

 --------
 在整段通信中唯一的数学内容，单独来看：Ω的单元素子集 {⊤} 能够检测真值。[P] 是否属于 {⊤} 展开后为 [Powerset_squash (True ≈ P)]，并且下面的两个蕴含表示这一对压缩的蕴含与 [P] 本身是可互推的。在本节之后的所有内容都是对这两行的记录整理。

 消去方向是 [Prop] 的自洽性发挥作用的地方：[Powerset_squash A] 是 [∀ Q : Prop, (A → Q) → Q]，因此将其消去到目标 [Prop] [P] 中相当于在 [Q := P] 处进行实例化——之所以合法，正是因为 [P] 是一个 [Prop]。（对于一个 [Type] 值的目标则不合法，这也是提供者自己截断的原因。）
*)

(*
 The truncation is INERT over a [Prop], which is the fact the header
 promises rather than asserts: [Powerset_squash A] is
 [∀ Q : Prop, (A → Q) → Q], so when A is itself a [Prop] the
 instantiation at [Q := A] recovers it.  This is what makes the donor's
 uniformly-truncated singleton usable at Ω, whose own equivalence is
 [Prop]-valued. 

 --------
 截断在 [Prop] 上是惰性的，这实际上是头部所承诺的，而不是断言：[Powerset_squash A] 是 [∀ Q : Prop, (A → Q) → Q]，所以当 A 本身是一个 [Prop] 时，[Q := A] 处的实例化会恢复它。这就是使供体的均匀截断单例在 Ω 上可用的原因，其自身的等价性是 [Prop] 值。
*)
Lemma powerset_squash_prop_inert@{o} (P : Prop) :
  Powerset_squash@{o} P <-> P.
Proof.
  split.
  - intro H; exact (H P (fun p => p)).
  - exact (@Powerset_squash_intro@{o} P).
Qed.

Lemma Powerset_truth_subset_intro@{o} (P : Prop) (p : P) :
  Powerset_truth_subset@{o} P.
Proof. exact (Powerset_squash_intro@{o} (conj (fun _ => p) (fun _ => I))). Qed.

Lemma Powerset_truth_subset_elim@{o} (P : Prop) (H : Powerset_truth_subset@{o} P) :
  P.
Proof. exact (H P (fun q => proj1 q I)). Qed.

Lemma powerset_truth_subset_holds@{o} :
  Powerset_truth_subset@{o} ≈ Powerset_holds@{o}.
Proof.
  intro P; split.
  - exact (@Powerset_truth_subset_elim@{o} P).
  - exact (@Powerset_truth_subset_intro@{o} P).
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** A subset of A IS a map A ⟶ Ω, definitionally / * ** A 的子集本质上是一个映射 A ⟶ Ω *)

(*
 This library's [Prop]-valued subsets of [A] are, by construction,
 exactly the setoid maps [A ~> Ω]: both are
 [SetoidMorphism A Powerset_Prop_truth].  The identification is
 [eq_refl], and saying so up front is what keeps the universal property
 below honest — its content is NOT this type identification but the
 [≈]-level round trip of the next section, since the preimage of {⊤}
 along a map is NOT that map on the nose (the strict form is refuted in
 the probe file, and the reason is that the two records carry different
 respectfulness proofs). 

 --------
 这个库的  [Prop] 值子集  [A] ，通过构造，恰好是集合映射  [A ~> Ω] ：两者都是  [SetoidMorphism A Powerset_Prop_truth] 。这种对应关系是  [eq_refl] ，事先说明这一点可以保持下面的泛性质真实——其内容不是这种类型的识别，而是下一节的  [≈] 级回路传递，因为一个映射的 {⊤} 逆像并不是该映射本身（严格形式在 probe 文件中被驳斥，原因是两个记录携带不同的尊重性证明）。
*)
Example powerset_subsets_are_maps@{o so} (A : SetoidObject@{o o}) :
  carrier (Powerset_Prop_obj@{o} A)
    = (A ~{Sets@{o so}}~> Powerset_Omega@{o}) := eq_refl.

(* The characteristic map of a subset is the subset, read across that identification. / 子集的特征映射就是该子集，通过那个标识来读取。 *)
Definition Powerset_char@{o so} {A : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  A ~{Sets@{o so}}~> Powerset_Omega@{o} := S.

Example powerset_char_is_subset@{o so} {A : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  Powerset_char@{o so} S = S := eq_refl.

(* The preimage of {⊤} along [k], which is Riehl's f⁻¹(⊤). / {⊤} 沿着 [k] 的原像，即 Riehl 的 f⁻¹(⊤)。 *)
Definition Powerset_preimage_of_truth@{o so} {A : SetoidObject@{o o}}
  (k : A ~{Sets@{o so}}~> Powerset_Omega@{o}) :
  carrier (Powerset_Prop_obj@{o} A) :=
  Powerset_Prop_preimage@{o} k Powerset_truth_subset@{o}.

(*
 ... and it IS the action of the functor on the universal element, by
 [eq_refl].  The convertibility exception again. 

 --------
 ... 并且它确实是函子在泛元素上的作用，由 [eq_refl] 提供。再次出现可转换性异常。
*)
Example powerset_preimage_is_fmap@{o so} {A : SetoidObject@{o o}}
  (k : A ~{Sets@{o so}}~> Powerset_Omega@{o}) :
  fmap[Powerset_Prop_op@{o so}]
    (k : Powerset_Omega@{o} ~{(Sets@{o so})^op}~> A) Powerset_truth_subset@{o}
    = Powerset_preimage_of_truth@{o so} k := eq_refl.

(*
 The two round trips, at [≈].  Together they are the bijection Riehl
 describes, and each is exactly one half of the universal property
 assembled in the next section. 

 --------
 两个往返，在 [≈]。它们一起构成了 Riehl 描述的双射，每一个正好是下一节中组装的泛性质的一半。
*)
Lemma powerset_preimage_char@{o so} {A : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  Powerset_preimage_of_truth@{o so} (Powerset_char@{o so} S) ≈ S.
Proof.
  intro a; split.
  - exact (@Powerset_truth_subset_elim@{o} (S a)).
  - exact (@Powerset_truth_subset_intro@{o} (S a)).
Qed.

Lemma powerset_char_preimage@{o so} {A : SetoidObject@{o o}}
  (k : A ~{Sets@{o so}}~> Powerset_Omega@{o}) :
  Powerset_char@{o so} (Powerset_preimage_of_truth@{o so} k) ≈ k.
Proof.
  intro a; split.
  - exact (@Powerset_truth_subset_elim@{o} (k a)).
  - exact (@Powerset_truth_subset_intro@{o} (k a)).
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** Mac Lane's §III.1 universal element / * ** 马克·莱恩 §III.1 通用元素 *)

(*
 Mac Lane's clause, read at [D := Sets^op] and [H := Powerset_Prop_op]:
 for every object A of [Sets] and every subset [S] of [A] there is a
 UNIQUE arrow [k : Ω ~{Sets^op}~> A] — that is, a unique setoid map
 [k : A ~> Ω] — with [(P k) {⊤} ≈ S], i.e. with [k⁻¹(⊤) ≈ S].  The
 witness is [S] itself, read as a map through the identification above;
 uniqueness is the observation that two maps whose preimages of {⊤}
 agree are pointwise mutually implying. 

 --------
 Mac Lane 的条款，在 [D := Sets^op] 和 [H := Powerset_Prop_op] 处阅读：对于 [Sets] 的每个对象 A 以及 [A] 的每个子集 [S]，存在一个唯一的箭头 [k : Ω ~{Sets^op}~> A]——也就是一个唯一的集合模映射 [k : A ~> Ω] ——具有 [(P k) {⊤} ≈ S]，即具有 [k⁻¹(⊤) ≈ S]。见证者是 [S] 本身，通过上述识别作为映射来读取；唯一性是指两个映射如果它们的 {⊤} 的原象相同，则在每个点上相互蕴含的观察。
*)
Definition Powerset_Prop_universal_element@{o so} :
  @AUniversalElement (Sets@{o so})^op Powerset_Prop_op@{o so}
    Powerset_Omega@{o}.
Proof.
  unshelve econstructor.
  - exact Powerset_truth_subset@{o}.
  - intros A S.
    unshelve econstructor.
    + exact (Powerset_char@{o so} S).
    + exact (powerset_preimage_char@{o so} S).
    + intros k Hk a; split.
      * intro Hs.
        exact (@Powerset_truth_subset_elim@{o} (k a) (proj2 (Hk a) Hs)).
      * intro Hka.
        exact (proj1 (Hk a) (@Powerset_truth_subset_intro@{o} (k a) Hka)).
Defined.

(* The element of the pair is {⊤}, and the mediating arrow of a subset is that subset — both by [eq_refl], so no reader has to trust the assembly above. / 该对的元素是 {⊤}，而子集的中介箭头是该子集——都由 [eq_refl] 定义，因此没有读者需要信任上述组合。 *)
Example powerset_aue_elem@{o so} :
  @aue_elem (Sets@{o so})^op Powerset_Prop_op@{o so} Powerset_Omega@{o}
    Powerset_Prop_universal_element@{o so}
    = Powerset_truth_subset@{o} := eq_refl.

Example powerset_aue_med@{o so} (A : SetoidObject@{o o})
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  unique_obj (@aue_universal (Sets@{o so})^op Powerset_Prop_op@{o so}
                Powerset_Omega@{o} Powerset_Prop_universal_element@{o so} A S)
    = S := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** The representation, and Awodey's naturality for the power set / * ** 表示，以及 Awodey 对幂集的自然性 *)

(*
 Through the Yoneda-FREE route of Theory/Universal/Element.v (see the
 header for why the Yoneda route is unavailable at [Sets]): the
 contravariant power-set functor is represented by Ω.  As a presheaf on
 [Sets], [@Curried_Hom (Sets^op) Ω] is [Hom_Sets(−, Ω)], the object the
 library writes [Hom ─,Ω]; the [eq_refl] below records that the two
 spellings are the same term. 

 --------
 通过 Theory/Universal/Element.v 的 Yoneda-FREE 路径（参见头文件了解为何在 [Sets] 上 Yoneda 路径不可用）：逆变幂集函子由 Ω 表示。作为 [Sets] 上的一个预层，[@Curried_Hom (Sets^op) Ω] 是 [Hom_Sets(−, Ω)]，即库中写作 [Hom ─,Ω] 的对象；下面的 [eq_refl] 记录了这两种写法是同一个项。
*)
Definition Powerset_representation@{o so} :
  @Curried_Hom (Sets@{o so})^op Powerset_Omega@{o}
    ≅[[(Sets@{o so})^op, Sets@{o so}]] Powerset_Prop_op@{o so} :=
  ue_representation Powerset_Prop_op@{o so} Powerset_Omega@{o}
    Powerset_Prop_universal_element@{o so}.

Example powerset_repr_source@{o so} :
  @Curried_Hom (Sets@{o so})^op Powerset_Omega@{o}
    = @Curried_CoHom Sets@{o so} Powerset_Omega@{o} := eq_refl.

(*
 RIEHL'S SENTENCE, MACHINE-CHECKED AT LEIBNIZ EQUALITY.  "The
 isomorphism sends f : A ⟶ Ω to the preimage f⁻¹(⊤) ⊆ A" is not a
 description of the forward leg up to [≈]; it IS the forward leg, term
 for term. 

 --------
 RIEHL 的句子，在莱布尼茨等式下由机器检查。“该同构将 f : A ⟶ Ω 映射到原像 f⁻¹(⊤) ⊆ A”并不是对正向部分的描述，直至 [≈]；它就是正向部分，逐项对应。
*)
Example powerset_representation_to_is_preimage@{o so}
  (A : SetoidObject@{o o}) (k : A ~{Sets@{o so}}~> Powerset_Omega@{o}) :
  transform (to Powerset_representation@{o so}) A k
    = Powerset_preimage_of_truth@{o so} k := eq_refl.

(* ... and the backward leg is the subset read as a map, again by [eq_refl]. / ... 而后退的腿是作为映射读取的子集，再次由 [eq_refl] 读取。 *)
Example powerset_representation_from_is_char@{o so}
  (A : SetoidObject@{o o}) (S : carrier (Powerset_Prop_obj@{o} A)) :
  transform (from Powerset_representation@{o so}) A S
    = Powerset_char@{o so} S := eq_refl.

(*
 The bundled form.  [Representable] is [Functor/Representable.v]'s
 class; the representing object is Ω on the nose. 

 --------
 打包的形式。[Representable] 是 [Functor/Representable.v] 的类；表示对象正是 Ω。
*)
Definition Powerset_Prop_Representable@{o so} :
  Representable Powerset_Prop_op@{o so} :=
  Representable_of_UniversalElement
    (UniversalElement_of_AUniversalElement
       Powerset_Prop_universal_element@{o so}).

Example powerset_repr_obj@{o so} :
  @repr_obj (Sets@{o so})^op Powerset_Prop_op@{o so}
    Powerset_Prop_Representable@{o so}
    = Powerset_Omega@{o} := eq_refl.

(*
 Riehl's bijection packaged as an isomorphism of setoids in [Sets], with
 the forward map the preimage of {⊤} and the backward map the
 characteristic subset.  A DISCLOSURE about its strength, because the
 packaging reads stronger than it is: by [powerset_subsets_are_maps]
 the two setoids are the SAME object of [Sets], so what this
 isomorphism carries beyond [Powerset_representation] is exactly its
 two round-trip equations — not an identification of two different
 setoids.  It is stated because it is the shape Riehl's sentence has,
 and because the [to] field names the preimage map explicitly. 

 --------
 Riehl 的双射被包装为 [Sets] 中集合结构的同构，其中前向映射为 {⊤} 的原像，后向映射为特征子集。关于其强度的披露，因为这种包装看起来比实际强：根据 [powerset_subsets_are_maps]，这两个集合结构是 [Sets] 的同一个对象，因此这个同构在 [Powerset_representation] 之外携带的恰好是它的两个往返方程——而不是两个不同集合结构的等同。之所以提出，是因为这是 Riehl 句子的形式，并且因为 [to] 字段显式命名了原像映射。
*)
Definition powerset_truth_bijection@{o so} (A : SetoidObject@{o o}) :
  @Isomorphism Sets@{o so}
    {| carrier   := A ~{Sets@{o so}}~> Powerset_Omega@{o}
     ; is_setoid := @homset Sets@{o so} A Powerset_Omega@{o} |}
    (Powerset_Prop_obj@{o} A).
Proof.
  unshelve refine {| to := _ ; from := _ |}.
  - unshelve refine {| morphism := fun k => Powerset_preimage_of_truth@{o so} k |}.
    intros k k' Hk a.
    exact (@proper_morphism _ _ _ _ Powerset_truth_subset@{o} (k a) (k' a) (Hk a)).
  - unshelve refine {| morphism := fun S => Powerset_char@{o so} S |}.
    intros S S' HS a; exact (HS a).
  - intro S; exact (powerset_preimage_char@{o so} S).
  - intro k; exact (powerset_char_preimage@{o so} k).
Defined.

(* ------------------------------------------------------------------------ *)
(* * ** Non-vacuity, and the degeneracies excluded by proof / * ** 非空性，以及通过证明排除的退化情况 *)

(*
 Three ways this could have proved nothing, and the statement that
 excludes each.

 (1) A DEGENERATE Ω.  If ⊤ and ⊥ were identified in Ω, every subset
 would be everything and the universal property would be empty.
 [powerset_Omega_nondegenerate] refutes that.

 (2) A DEGENERATE UNIVERSAL ELEMENT.  If {⊤} were the empty subset of Ω
 or all of Ω, it would carry no information.  It is neither:
 [powerset_truth_subset_inhabited] and
 [powerset_truth_subset_proper].

 (3) A CONTRAVARIANT ACTION THAT IS SECRETLY THE COVARIANT ONE.  The
 inverse image and the direct image of the SAME morphism on the
 SAME subset are separated below, on a two-element carrier, by
 [powerset_inverse_ne_direct].

 Beyond those, the correspondence is exhibited computing on a concrete
 subset of a three-element setoid, and two distinct subsets are shown
 to have distinct characteristic maps. 

 --------
 三种方式可能证明这毫无意义，以及排除每种情况的说明。

 (1) 退化的 Ω。如果在 Ω 中将 ⊤ 和 ⊥ 识别为相同元素，则每个子集都将是全集，而泛性质将为空。
 [powerset_Omega_nondegenerate] 否定了这一点。

 (2) 退化的全体元素。如果 {⊤} 是 Ω 的空子集或 Ω 的全部，它将不携带任何信息。它都不是：
 [powerset_truth_subset_inhabited] 和
 [powerset_truth_subset_proper]。

 (3) 逆变作用实际上是协变作用。同一个态射在同一个子集上的逆像和像在下文的两元素承载集合上被
 [powerset_inverse_ne_direct] 区分。除此之外，该对应关系在一个三元素集合的具体子集上进行计算，并且证明两个不同的子集具有不同的特征映射。
*)

Lemma powerset_Omega_nondegenerate@{o} :
  @equiv _ (is_setoid Powerset_Omega@{o}) Powerset_truth_point@{o} False
  → False.
Proof. intros [H _]; exact (H I). Qed.

Lemma powerset_truth_subset_inhabited@{o} :
  Powerset_truth_subset@{o} Powerset_truth_point@{o}.
Proof. exact (@Powerset_truth_subset_intro@{o} True I). Qed.

Lemma powerset_truth_subset_proper@{o} :
  Powerset_truth_subset@{o} False → False.
Proof. exact (@Powerset_truth_subset_elim@{o} False). Qed.

(*
 The three-element carrier, and two subsets of it.  [Powerset_Prop_truth]
 forces [Set < o], so the donor's universe-polymorphic
 [Powerset_Prop_fin_object] is the right carrier here (its own header
 records that this is the only reason it exists). 

 --------
 三元素载体，以及它的两个子集。   [Powerset_Prop_truth] 
 强制 [Set < o] ，因此供体的宇宙多态
 [Powerset_Prop_fin_object] 是这里正确的载体（它自己的头部
 记录表明这是它存在的唯一原因）。
*)

Definition powerset_fin3@{o} : SetoidObject@{o o} :=
  Powerset_Prop_fin_object@{o} 3.

Definition powerset_sub01@{o} : carrier (Powerset_Prop_obj@{o} powerset_fin3@{o}).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (Fin.t 3) (is_setoid powerset_fin3@{o})
       Prop (is_setoid Powerset_Prop_truth@{o})
       (λ i : Fin.t 3, i = Fin.F1 \/ i = Fin.FS Fin.F1) _).
  intros x y Hxy; rewrite Hxy; split; intro H; exact H.
Defined.

Definition powerset_sub0@{o} : carrier (Powerset_Prop_obj@{o} powerset_fin3@{o}).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (Fin.t 3) (is_setoid powerset_fin3@{o})
       Prop (is_setoid Powerset_Prop_truth@{o})
       (λ i : Fin.t 3, i = Fin.F1) _).
  intros x y Hxy; rewrite Hxy; split; intro H; exact H.
Defined.

(* The two subsets are genuinely different: 1 belongs to one and not the other. / 这两个子集确实不同：1归属于其中一个，而不属于另一个。 *)
Lemma powerset_sub01_ne_sub0@{o} :
  powerset_sub01@{o} ≈ powerset_sub0@{o} → False.
Proof.
  intro H.
  assert (H1 : @Fin.FS 2 Fin.F1 = Fin.F1)
    by exact (proj1 (H (Fin.FS Fin.F1)) (or_intror eq_refl)).
  discriminate H1.
Qed.

(* ... so their characteristic maps are different: the correspondence is not collapsing subsets. / ... 因此它们的特征映射是不同的：这种对应关系不会把子集塌缩。 *)
Lemma powerset_chars_distinct@{o so} :
  Powerset_char@{o so} powerset_sub01@{o}
    ≈ Powerset_char@{o so} powerset_sub0@{o} → False.
Proof. exact powerset_sub01_ne_sub0@{o}. Qed.

(* The characteristic map takes the expected values: 0 and 1 are in, 2 is out. / 特征映射采用期望值：0 和 1 属于，2 不属于。 *)
Lemma powerset_char_at_0@{o so} :
  Powerset_char@{o so} powerset_sub01@{o} Fin.F1.
Proof. exact (or_introl eq_refl). Qed.

Lemma powerset_char_at_1@{o so} :
  Powerset_char@{o so} powerset_sub01@{o} (Fin.FS Fin.F1).
Proof. exact (or_intror eq_refl). Qed.

Lemma powerset_char_at_2@{o so} :
  Powerset_char@{o so} powerset_sub01@{o} (Fin.FS (Fin.FS Fin.F1)) → False.
Proof. intros [H | H]; discriminate H. Qed.

(* The round trip on a concrete subset: pulling {⊤} back along the characteristic map of {0,1} returns {0,1}. / 在混凝土子集上的往返：沿着 {0,1} 的特征映射将 {⊤} 拉回会返回 {0,1}。 *)
Lemma powerset_fin3_round@{o so} :
  Powerset_preimage_of_truth@{o so} (Powerset_char@{o so} powerset_sub01@{o})
    ≈ powerset_sub01@{o}.
Proof. exact (powerset_preimage_char@{o so} powerset_sub01@{o}). Qed.

(*
 The inverse image is not the direct image.  [powerset_const0] is the
 constant map at 0 on a two-element carrier, so both actions land in the
 same power set and can be compared; the direct image of {1} is {0},
 while its inverse image is empty. 

 --------
 逆像不是像。[powerset_const0] 是一个在两元素载体上取值为 0 的常值映射，所以两个作用都落在同一个幂集中，可以进行比较；{1} 的像是 {0}，而它的逆像是空的。
*)

Definition powerset_fin2@{o} : SetoidObject@{o o} :=
  Powerset_Prop_fin_object@{o} 2.

Definition powerset_const0@{o so} : powerset_fin2@{o} ~{Sets@{o so}}~> powerset_fin2@{o}.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (Fin.t 2) (is_setoid powerset_fin2@{o})
       (Fin.t 2) (is_setoid powerset_fin2@{o})
       (λ _, Fin.F1) _).
  intros x y _; reflexivity.
Defined.

Definition powerset_sng1@{o} : carrier (Powerset_Prop_obj@{o} powerset_fin2@{o}) :=
  Powerset_Prop_singleton_pred@{o} (X:=powerset_fin2@{o}) (Fin.FS Fin.F1).

Lemma powerset_inverse_sng1_empty@{o so} (i : Fin.t 2) :
  fmap[Powerset_Prop_op@{o so}]
    (powerset_const0@{o so} : powerset_fin2@{o} ~{(Sets@{o so})^op}~> powerset_fin2@{o})
    powerset_sng1@{o} i → False.
Proof.
  intro H; hnf in H.
  refine (H False _); intro Heq; discriminate Heq.
Qed.

Lemma powerset_direct_sng1_at_0@{o so} :
  fmap[Powerset_Prop@{o so}] powerset_const0@{o so} powerset_sng1@{o} Fin.F1.
Proof.
  hnf.
  apply Powerset_squash_intro@{o}.
  exists (Fin.FS Fin.F1); split.
  - apply Powerset_squash_intro@{o}; reflexivity.
  - reflexivity.
Qed.

Theorem powerset_inverse_ne_direct@{o so} :
  fmap[Powerset_Prop@{o so}] powerset_const0@{o so} powerset_sng1@{o}
    ≈ fmap[Powerset_Prop_op@{o so}]
        (powerset_const0@{o so}
           : powerset_fin2@{o} ~{(Sets@{o so})^op}~> powerset_fin2@{o})
        powerset_sng1@{o}
  → False.
Proof.
  intro H.
  exact (powerset_inverse_sng1_empty@{o so} Fin.F1
           (proj1 (H Fin.F1) powerset_direct_sng1_at_0@{o so})).
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** The classifier obstruction is a DIFFERENT obstruction / * ** 分类器阻塞是一种不同的阻塞 *)

(*
 Instance/Sets/Classifier.v proves the subobject-classifier theorems for
 [Sets] as CROSS-UNIVERSE statements, and its header explains why: the
 characteristic predicate of a MONO [m : A ~> B] is
 [λ b, ∃ a, m a ≈ b], which is [Type@{o}]-valued because [≈] is, and
 [sets_char_pullback] and [sets_char_unique] must recover the witness
 [a] out of the truth value in order to mediate for a cone.  Truncating
 to [Prop] destroys exactly what they need.

 Nothing of the sort is asked of a power set.  Mac Lane's §III.1 clause
 asks only for a unique arrow with [(H k) e ≈ x], and above, the
 mediating arrow IS the subset — no witness is extracted from a truth
 value anywhere in [Powerset_Prop_universal_element].  That is why one
 level suffices here, and why the two results coexist without either
 weakening the other.

 READ THAT COMPARISON PRECISELY: NO IMPOSSIBILITY IS PROVED.  What is measured
 is that Classifier.v's construction consumes a witness and this one does not.
 Whether some OTHER construction yields a one-level [SubobjectClassifier Sets]
 was not settled here — it was not attempted below, and nothing below rules it
 out.  It is answered CONDITIONALLY in Instance/Sets/Classifier/OneLevel.v:
 the instance whose Ω is [Powerset_Omega] exists under [Untruncate], i.e.
 exactly when the impredicative truncation used here can be inverted, and what
 that hypothesis buys is precisely the composite "in the other direction" left
 unproven in the next paragraph.  NO IMPOSSIBILITY IS PROVED there either.
 The issue asked for a note on why [Sets] may support only the cross-universe
 reading for the CLASSIFIER even where the power-set universal element works
 at one level; this paragraph is that note, and it is a note about a
 construction, not a theorem about the category.

 THE CONSEQUENCE, AND THE HONEST LIMIT.  This file does NOT produce a
 [SubobjectClassifier Sets] instance, and no such instance follows from
 what is proved here, because [SubobjectClassifier] classifies [SubObj]
 — monos up to isomorphism — not [Prop]-valued subsets.  The passage
 from a subset to a subobject is available and its round trip holds
 (both are proved immediately below); the passage back truncates the
 membership witness, and recovering it is the very step Classifier.v
 records as blocked.  So the composite in the other direction is left
 unproven and unclaimed here, rather than asserted in either
 direction. 

 --------
 Instance/Sets/Classifier.v 对 [Sets] 的子对象分类器定理进行了证明，作为跨宇宙（CROSS-UNIVERSE）语句，并且其头部解释了原因：一个单射（MONO）[m : A ~> B] 的特征谓词是 [λ b, ∃ a, m a ≈ b]，之所以是 [Type@{o}] 值，是因为 [≈] 也是如此，并且 [sets_char_pullback] 和 [sets_char_unique] 必须从真值中恢复证据 [a]，以便在锥体中起到中介作用。截断到 [Prop] 恰恰会破坏它们所需要的东西。

 对于幂集（power set）并没有类似的要求。Mac Lane 的 §III.1 条款仅要求存在一个唯一的箭头 [(H k) e ≈ x]，而在上文中，中介箭头就是子集——在 [Powerset_Prop_universal_element] 中没有从真值中提取任何证据。这就是为什么在这里一层就足够，以及为什么这两个结果可以共存而互不削弱。精确阅读该比较：没有任何不可能性被证明。所测量的是 Classifier.v 的构造消耗了一个见证，而这一个则没有。是否有其他构造产生一级 [SubobjectClassifier Sets] 并未在此解决——下面也没有尝试，并且下面的内容并不排除这一点。在 Instance/Sets/Classifier/OneLevel.v 中有有条件的回答：其 Ω 为 [Powerset_Omega] 的实例在 [Untruncate] 下存在，即恰恰当这里使用的任意归纳截断可以被逆转，而该假设所带来的恰恰是下一段中未被证明的“另一方向”的复合。在那里也没有证明任何不可能性。这个问题要求对为什么 [Sets] 可能只支持 CLASSIFIER 的跨宇宙读取，即使幂集的通用元素在某一级别上有效，作一个说明；这一段就是那个说明，它是关于一个构造的说明，而不是关于该范畴的定理。结果与诚实的限制。这个文件不会生成一个 [SubobjectClassifier Sets] 实例，并且从这里证明的内容也不会得出这样的实例，因为 [SubobjectClassifier] 对 [SubObj] — 同构下的单子 — 进行分类，而不是 [Prop] 值的子集。从子集到子对象的转换是可行的，并且其往返过程成立（两者在下面立即证明）；向回的转换会截断成员资格证据，而恢复它正是 Classifier.v 记录为被阻止的步骤。因此，另一个方向的复合在此处没有被证明也没有被声明，而不是在任何方向上被断言。
*)

(*
 A subset [S] of [A] names a subobject of [A]: the sub-setoid of
 elements satisfying [S], with the first projection.  Since membership
 is a [Prop] and the sub-setoid compares only first components, the
 projection is injective, hence monic. 

 --------
 子集 [S] 的 [A] 命名了 [A] 的一个子对象：满足 [S] 的元素的子集合，以第一投影为准。由于成员资格是 [Prop]，并且子集合仅比较第一个分量，因此该投影是单射的，因此是单态的。
*)
Definition Powerset_subset_setoid@{o} {A : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} A)) : SetoidObject@{o o}.
Proof.
  unshelve refine
    {| carrier   := { a : carrier A & S a }
     ; is_setoid :=
         {| equiv := fun p q => @equiv _ (is_setoid A) (projT1 p) (projT1 q) |} |}.
  constructor.
  - intro p; reflexivity.
  - intros p q H; now symmetry.
  - intros p q r H K; now transitivity (projT1 q).
Defined.

Definition Powerset_subset_incl@{o so} {A : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  Powerset_subset_setoid@{o} S ~{Sets@{o so}}~> A.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       { a : carrier A & S a } (is_setoid (Powerset_subset_setoid@{o} S))
       (carrier A) (is_setoid A)
       (λ p, projT1 p) _).
  intros p q Hpq; exact Hpq.
Defined.

Lemma Powerset_subset_incl_monic@{o so} {A : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  @Monic Sets@{o so} _ _ (Powerset_subset_incl@{o so} S).
Proof.
  apply (injectivity_is_monic@{so o} (Powerset_subset_incl@{o so} S)).
  intros p q H; exact H.
Qed.

Definition Powerset_subobject_of_subset@{o so} {A : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} A)) : @SubObj Sets@{o so} A :=
  @Build_SubObj Sets@{o so} A
    (Powerset_subset_setoid@{o} S)
    (Powerset_subset_incl@{o so} S)
    (Powerset_subset_incl_monic@{o so} S).

(* ... and back: the truncated image of a mono is a [Prop]-valued subset. This is the step that discards the witness. / ... 和返回：单声道的截断图像是一个 [Prop] 值子集。 这是丢弃见证的步骤。 *)
Definition Powerset_subset_of_subobject@{o so} {A : SetoidObject@{o o}}
  (u : @SubObj Sets@{o so} A) : carrier (Powerset_Prop_obj@{o} A).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier A) (is_setoid A) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ a, Powerset_squash@{o}
               (∃ p : carrier (sub_dom u),
                  @equiv _ (is_setoid A) (sub_mono u p) a)) _).
  intros a a' Haa'; split; intros H Q k; apply H; intros [p Hp]; apply k;
    exists p.
  - now transitivity a.
  - transitivity a'; [ exact Hp | now symmetry ].
Defined.

(*
 THE HALF THAT HOLDS: a subset is recovered from the subobject it names.
 Both directions stay inside [Prop], so the truncation is transparent
 here — which is exactly what is not true in the other order. 

 --------
 保持的一半：一个子集从它所命名的子对象中被恢复。
 两个方向都保持在 [Prop] 内，所以这里的截断是透明的——而在另一个顺序中情况正好相反。
*)
Theorem Powerset_subset_roundtrip@{o so} {A : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  Powerset_subset_of_subobject@{o so} (Powerset_subobject_of_subset@{o so} S)
    ≈ S.
Proof.
  intro a; split.
  - intro H; hnf in H.
    refine (H (S a) _); intros [[b Hb] Hba]; simpl in Hba.
    exact (proj1 (@proper_morphism _ _ _ _ S b a Hba) Hb).
  - intro Ha.
    hnf.
    apply Powerset_squash_intro@{o}.
    exists (existT _ a Ha); reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** Where the rest of the exercise lives / * ** 其他练习内容所在的位置 *)

(*
 Awodey's naturality clause for the SUBOBJECT functor —
 [Sub ≅ Hom(─,Ω)] in [[C^op, Sets]] for an arbitrary classifier — is
 Structure/SubobjectClassifier/Natural.v, and the same exercise answered
 where the correspondence is not definitional, over skeletal [FinSet]
 with Ω = 2 and everything computing, is Instance/FinSet/Powerset.v.
 Neither is restated here. 

 --------
 Awodey 对 SUBOBJECT 函子——在任意分类器上的 [Sub ≅ Hom(─,Ω)] 到 [[C^op, Sets]——的自然性条款在 Structure/SubobjectClassifier/Natural.v 中，而当对应关系不是定义性的，在骨架 [FinSet] 上且 Ω = 2 且一切可计算时的同一练习答案在 Instance/FinSet/Powerset.v 中。这里都没有重述。
*)
