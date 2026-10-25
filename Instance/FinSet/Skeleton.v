Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.FinSet.

Require Import Coq.Vectors.Fin.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Category.Theory.Skeleton.

Generalizable All Variables.

(* * * The skeleton equivalence: finite setoids and finite ordinals / * * 骨架等价：有限集合类与有限序数 *)

(*
 nLab: https://ncatlab.org/nlab/show/skeleton+of+a+category
 nLab: https://ncatlab.org/nlab/show/equivalence+of+categories

 Mac Lane's motivating example for equivalence of categories
 (Categories for the Working Mathematician, 2nd ed., §I.4, printed
 pp. 17-18): the category of all finite sets and the skeletal category
 of finite ordinals are equivalent, and equivalent is the most that can
 be asked of them.  This file supplies the missing half over the
 library's existing skeleton (Instance/FinSet.v: objects [nat],
 morphisms all functions [Fin.t m → Fin.t n]), builds the two functors,
 and proves the comparison cells.

 [Set_f] is a category of FINITE SETOIDS.  An object bundles a
 [SetoidObject] (Instance/Sets.v), a natural number, and an
 isomorphism in [Sets] from the setoid to the canonical one — Mac Lane's
 chosen bijection [θ_X : X ≅ #X].  Morphisms, identities, composition
 and the hom-setoid are those of [Sets] verbatim, so the evident functor
 [Set_f ⟶ Sets] is FULLY FAITHFUL — but it is NOT injective on objects,
 so [Set_f] is not a subcategory of [Sets].  An audit of the first commit
 was right to insist on the distinction, and the file's own centrepiece
 depends on it: [two_swap] and [finset_obj 2] have the SAME underlying
 setoid and differ only in the bijection they carry, which is exactly
 what makes the counit at [two_swap] a transposition rather than an
 identity.  Were [Set_f] a full subcategory of [Sets], those two objects
 would be one object and the asymmetry below would collapse.  An
 isomorphism of [Set_f] is nonetheless an isomorphism of [Sets] on the
 nose
 ([setf_iso] and [sets_iso] repackage the same four fields and carry no
 content of their own).  Finiteness is meant in the setoid sense —
 finitely many equivalence classes — so a carrier may be infinite;
 [parity_two] below is [nat] under equality of parity, an object of
 [Set_f] of cardinality 2.

 THE WITNESS IS DATA, NOT AN ASSERTION.  [fs_theta] is a field of the
 object record, so the cardinal functor [Card] can read it off and act
 on morphisms by Mac Lane's formula [# f = θ_Y ∘ f ∘ θ_X⁻¹].  Were
 finiteness recorded instead as a [Prop]-valued existential, its witness
 could not be eliminated into [Type], so it would be unavailable to
 [Card]'s morphism map, and producing one for every object at once is
 exactly what a choice principle does.  This is the discipline the library keeps
 throughout — chosen pullbacks, the chosen lifts of [Cleaving]
 (Theory/Fibration.v), the split [Full] class of Theory/Functor.v, and
 the split [EssentiallySurjective] class of Theory/Equivalence.v, whose
 header records that the classical full + faithful + essentially
 surjective criterion is otherwise equivalent to the axiom of choice.
 Every constant below is closed under the global context.

 The equivalence is not assembled by hand.  Awodey's two characteristic
 conditions (Category Theory, 1st ed. Carnegie Mellon pre-print,
 September 2005, §7.8, unnumbered remark, printed p. 178) are discharged
 for this instance — [FinSet_Incl] is shown full, faithful and
 essentially surjective — and [FinSet_Setf_Equivalence] is
 [FF_ESO_Equivalence] (Theory/Equivalence/FullFaithful.v) applied to
 those three witnesses.  Two things are worth saying plainly about that
 route:

 - Fullness and faithfulness hold definitionally here, and are to that
 extent content-free: the inclusion hands the underlying function
 straight through, so [prefmap] gives it back and [fmap_inj] is the
 identity.  What the inclusion does add is a respectfulness proof, so
 the section law of [Full] is an equation of underlying functions
 rather than of records — which is all the class asks, since it is
 stated up to ≈.  The one mathematical input is [fin_map]: on the
 canonical setoids ≈ IS Leibniz equality, so every function between
 them is respectful.
 - Essential surjectivity carries the content, and it is exactly the
 chosen [fs_theta] read backwards.  [Card] is then not an independent
 construction: it agrees with the quasi-inverse that
 [FF_ESO_Equivalence] produces on objects and on morphisms up to
 conversion ([Card_quasi_inverse_fobj], [Card_quasi_inverse_fmap]),
 which is why [Card_is_quasi_inverse] holds by [reflexivity].

 THE ASYMMETRY (Awodey, op. cit., §7.8, Example 7.23, printed
 pp. 176-177).  One round trip is strict and the other is not:

 - [Card ◯ FinSet_Incl] is the identity functor on the nose — its object
 map and its morphism map are Leibniz-equal to the identity's, by
 [eq_refl] ([Card_Incl_fobj_strict], [Card_Incl_fmap_strict]), and the
 comparison cell that [FF_ESO_Equivalence] computes at every object is
 literally the identity morphism ([Incl_unit_is_identity]) — its
 COMPONENTS are, in both directions; the isomorphism RECORD is not
 [iso_id], since the two carry different proof fields.  This is
 the effect of giving the canonical objects the identity bijection.
 - [FinSet_Incl ◯ Card] is compared to the identity only by the natural
 isomorphism [Incl_Card_theta], whose components are the chosen
 [θ].  At [two_swap] — whose carrier is already the canonical
 [Fin.t 2], but whose chosen bijection is the transposition — the
 comparison component is that transposition and provably not the
 identity ([counit_at_two_swap_not_identity]), and the composite
 replaces the carried bijection by the identity one
 ([Incl_Card_forgets_theta]).

 What is deliberately NOT claimed is a Leibniz disequality
 [FinSet_Incl ◯ Card ≠ Id[Set_f]] of functors or of objects: nothing
 here establishes one, the objects compared differ only in the bijection
 they carry, and no statement below rests on such a disequality.  The
 asymmetry is stated where Awodey states it, at the comparison cells.

 SKELETALITY AND CARDINALITY (Fong and Spivak, Seven Sketches in
 Compositionality, CUP 2019, §3.2.5, printed p. 88).  [FinSet_skeletal]
 is the first statement in the tree about isomorphisms of [FinSet] —
 Instance/FinSet.v contains no occurrence of [Isomorphism] at all, and
 its satellites only require the module.  An isomorphism [m ≅ n] forces
 [m = n], by counting: [fin_enum] enumerates [Fin.t n] without
 repetition, and each enumeration embeds in the image of the other
 ([fin_bijection_index]).  Hence [setf_cardinality A], the index
 the object carries, is THE index it is isomorphic to
 ([setf_cardinality_unique]), and Cantor's reading follows: setf_cardinality is
 constant on isomorphism classes and separates them
 ([setf_cardinality_iso_invariant], [setf_cardinality_complete],
 [setf_cardinality_classifies]).

 WHERE [=] APPEARS, AND WHY.  Morphisms are compared with ≈ throughout;
 the exceptions are deliberate and each is flagged where it is stated.
 (a) Equality of OBJECTS is the point of [FinSet_skeletal] and of the
 cardinality theorems — there [=] is what is being proved.  (b) The
 strictness lemmas compare morphisms and functor components with [=];
 each is genuinely stronger than the ≈ or ≅ statement it refines, and
 says so at the statement.  Most of them sit in the asymmetry section,
 but not all — [Card_quasi_inverse_fmap] is one and appears with the
 equivalence.  (b') Beyond those five classes the file also states a few
 equalities of Types and of booleans (carrier identifications, and the
 counting kit's list lengths); they are not comparisons of categorical
 data at all, and are listed here only so this taxonomy is not read as
 exhaustive.  (c) Equations
 between ELEMENTS of a canonical setoid [fin_setoid n] are written [=]
 because [Fin_Setoid]'s equivalence IS Leibniz equality, so there [=] and
 ≈ are the same relation and nothing is being strengthened.  (d) Two
 statements compare elements of [parity_setoid], whose ≈ is equality of
 parity; there [=] is strictly stronger, deliberately, and each says so.
 (e) [setf_sets_iso], [sets_setf_iso] and [Incl_Card_forgets_theta]
 compare isomorphism RECORDS — carried data, not morphisms.

 SCOPE.  This is the finite concrete case only.  No general [Skeleton]
 vocabulary is introduced: the statement that every category has a
 skeleton is itself equivalent to the axiom of choice (nLab, "skeleton
 of a category"), and Theory/Equivalence.v's header records the
 library's decision to confine skeletons to concrete instances such as
 this one. 

 --------
 nLab：https://ncatlab.org/nlab/show/skeleton+of+a+category
 nLab：https://ncatlab.org/nlab/show/equivalence+of+categories

 Mac Lane 关于范畴等价的动机示例
 （《为在职数学家而写的范畴论》，第二版，第 I.4 节，印刷页 17-18）：所有有限集合的范畴与有限序数的骨架范畴是等价的，而等价是对它们可以提出的最高要求。该文件在库现有骨架（Instance/FinSet.v：对象 [nat]，态射为所有函数 [Fin.t m → Fin.t n]）的基础上提供缺失的一半，构建两个函子，并证明比较单元。[Set_f] 是一个有限集合类（FINITE SETOIDS）的类别。一个对象捆绑了一个 [SetoidObject]（Instance/Sets.v）、一个自然数，以及一个 [Sets] 中从该集合类到标准集合类的同构——Mac Lane 选择的双射 [θ_X : X ≅ #X]。态射、恒等态射、复合和同态集合类完全照搬 [Sets]，因此显然的函子 [Set_f ⟶ Sets] 是完全忠实的（FULLY FAITHFUL）——但它在对象上并非单射，因此 [Set_f] 不是 [Sets] 的子类别。对首次提交的审查坚持区分是正确的，并且该文件自身的核心依赖于此：[two_swap] 和 [finset_obj 2] 具有相同的基础集合类，仅在它们携带的双射上有所不同，这正是使得 [two_swap] 的余单元是置换而不是恒等式的原因。如果 [Set_f] 是 [Sets] 的一个满子范畴，那么那两个对象将会是同一个对象，下方的不对称将会消失。[Set_f] 的同构仍然是 [Sets] 上严格的同构（[setf_iso] 和 [sets_iso] 重新打包相同的四个字段，并不包含自身的内容）。有限性是按集合类的意义——有限个等价类——所以承载体可能是无限的；下方的 [parity_two] 是 [nat] 按奇偶性相等的情况，是 [Set_f] 中一个基数为 2 的对象。证据是数据，而不是断言。[fs_theta] 是对象记录的一个字段，因此基数函子 [Card] 可以读取它，并通过 Mac Lane 的公式 [# f = θ_Y ∘ f ∘ θ_X⁻¹] 作用于态射。如果有限性记录为一个 [Prop] 值的存在式，它的证据就无法被消解到 [Type] 中，因此 [Card] 的态射映射将无法使用它，并且为每个对象同时生成一个正是选择公理所做的事情。这是图书馆始终保持的规律 —— 精选的回退，理论/纤维化.v（Theory/Fibration.v）中的精选提升 [Cleaving]，理论/函子.v（Theory/Functor.v）中的分裂类 [Full]，以及理论/等价.v（Theory/Equivalence.v）中的分裂类 [EssentiallySurjective]，其标题记录表明，经典的满 + 可信 + 本质上满射准则在其他情况下等价于选择公理。下面的每个常量都在全局上下文中封闭。这个等价不是手工组装的。Awodey 的两个特征条件（《范畴论》，第一版，卡内基梅隆预印本，2005年9月，第7.8节，无编号备注，印刷页178）在这个实例中已被满足——[FinSet_Incl] 被证明是满的、忠实的并且本质上是满射——而 [FinSet_Setf_Equivalence] 是 [FF_ESO_Equivalence]（Theory/Equivalence/FullFaithful.v）应用于这三个证明者。有两点关于该路线值得明确说明：- 这里的充足性和忠实性在定义上成立，因此在这个范围内是无内容的：包含将底层函数直接传递，因此 [prefmap] 将其返回，而 [fmap_inj] 是恒等映射。包含所增加的是一个恭敬性证明，因此 [Full] 的截面律是底层函数的等式，而不是记录的等式——这正是该类所要求的，因为它是在 ≈ 下陈述的。唯一的数学输入是 [fin_map]：在规范集合子集上，≈ 是莱布尼茨等价，因此它们之间的每个函数都是恭敬的。 - 本质的满射性承载内容，它恰好是选定的 [fs_theta] 反向读取。[Card] 不是一个独立的构造：它与 [FF_ESO_Equivalence] 在对象和态射上产生的准逆一致，直至转换（[Card_quasi_inverse_fobj]，[Card_quasi_inverse_fmap]），这就是为什么 [Card_is_quasi_inverse] 可以通过 [reflexivity] 成立。

 非对称性（Awodey，前引文献，第7.8节，例7.23，印刷页176-177）。一次往返是严格的，而另一次则不是：- [Card ◯ FinSet_Incl] 本身就是恒等函子——它的对象映射和态射映射根据 [eq_refl]（[Card_Incl_fobj_strict]，[Card_Incl_fmap_strict]）与恒等函子完全相等，并且 [FF_ESO_Equivalence] 在每个对象上计算的比较单元完全是恒等态射（[Incl_unit_is_identity]）——其组成部分在两个方向上都是相同的；这个同构记录不是 [iso_id]，因为二者携带不同的证明字段。这是给出标准对象恒等双射的效果。- [FinSet_Incl ◯ Card] 仅通过自然同构 [Incl_Card_theta] 与恒等函子进行比较，其组成部分是所选的 [θ]。在 [two_swap] — 其承载者已经是规范的 [Fin.t 2]，但其选择的双射是换位 — 比较组件就是该换位，并且可以证明不是恒等 ([counit_at_two_swap_not_identity])，组合则用恒等双射 ([Incl_Card_forgets_theta]) 替换承载的双射。

 明确没有主张的是范畴或对象的莱布尼茨不等式 [FinSet_Incl ◯ Card ≠ Id[Set_f]：这里没有建立任何不等式，被比较的对象仅在它们承载的双射上有所不同，下文的任何陈述都不依赖这种不等式。非对称性在 Awodey 表述的比较单元处被陈述出来。骨架性与基数性（Fong 和 Spivak，《组合性中的七个素描》，CUP 2019，第3.2.5节，印刷页88）。[FinSet_skeletal] 是树中关于 [FinSet] 同构的第一个陈述——Instance/FinSet.v 中完全没有出现 [Isomorphism]，其卫星仅需要该模块。一个同构 [m ≅ n] 通过计数强制 [m = n]：[fin_enum] 枚举 [Fin.t n]，无重复，每个枚举嵌入在另一个的像中（[fin_bijection_index]）。因此 [setf_cardinality A]，即该对象携带的指标，就是它同构的指标（[setf_cardinality_unique]），康托尔的解读随之而来：setf_cardinality 在同构类上是常数并区分它们（[setf_cardinality_iso_invariant], [setf_cardinality_complete], [setf_cardinality_classifies]）。[=] 出现的地方以及原因。态射在整个文中都与 ≈ 进行比较；例外是有意为之，并在说明时标注。(a) 对象的相等性是 [FinSet_skeletal] 以及基数定理的重点——这里 [=] 是正在被证明的内容。(b) 严格性引理将态射和函子分量与 [=] 进行比较；每一个都比它所细化的 ≈ 或 ≅ 陈述更强，并在陈述中指出。它们大多数位于非对称性部分，但并非全部——[Card_quasi_inverse_fmap] 就是其中一个，并与等价性一起出现。(b') 除了这五类之外，文件还说明了几种类型和布尔值的等式（承载标识和计数工具的列表长度）；它们根本不是类别数据的比较，这里列出它们只是为了不让这个分类法被理解为穷尽的。 (c) 对一个规范集族 [fin_setoid n] 的元素之间的方程式写作 [=]，因为 [Fin_Setoid] 的等价关系就是莱布尼茨等式，所以 [=] 和 ≈ 是相同的关系，没有任何加强。 (d) 两个陈述比较 [parity_setoid] 的元素，其 ≈ 是奇偶性的等式；这里 [=] 的比较是严格更强的，这是刻意为之，并且每个陈述都有说明。 (e) [setf_sets_iso]、[sets_setf_iso] 和 [Incl_Card_forgets_theta] 比较的是同构记录（RECORDS）——承载的数据，而不是态射。范围。本例仅限于有限的具体情况。未引入一般的 [Skeleton] 词汇：每个范畴都有一个骨架的陈述本身就相当于选择公理（nLab，“范畴的骨架”），而 Theory/Equivalence.v 的标题记录了该库将骨架限定为像本例这样的具体实例的决定。
*)

(*
 Why a category and its skeleton are the same, and why that took work

 nLab: https://ncatlab.org/nlab/show/skeleton+of+a+category
 nLab: https://ncatlab.org/nlab/show/principle+of+equivalence

 Counting is the oldest piece of mathematics, and this file is its
 categorical form.  To say that a finite set has n elements is to
 choose a bijection with the standard n-element set; Cantor's move
 was to make the number secondary and the bijection primary, so that
 two sets have the same cardinality precisely when some bijection
 exists (Fong and Spivak, Seven Sketches in Compositionality, CUP
 2019, §3.2.5, present cardinality in exactly this isomorphism-class
 reading; the in-file constant is named [setf_cardinality] only to avoid
 shadowing an unrelated [cardinality] in Theory/Metacategory.v).  The categorical statement adds functoriality: the
 assignment of a number to a set is not merely well defined on
 isomorphism classes, it is a functor, and the choice of bijections
 through which it acts on maps is invisible in the result up to
 natural isomorphism.

 Mac Lane introduces equivalence of categories through this very
 example (CWM §I.4, printed pp. 17-18), and the reason it must be
 equivalence rather than isomorphism is visible in the objects
 themselves: the ordinal 2 is one object, whereas the two-element
 sets form a proper class, so no bijection of object collections is
 available and none should be wanted.  Awodey draws the moral in
 §7.8 (printed p. 178): the two conditions that characterize an
 equivalence — full and faithful, and essentially surjective — are
 each visibly satisfied by the inclusion, while the composite in one
 order is the identity and in the other only isomorphic to it.  This
 is the concrete case of the principle of equivalence: a property of
 categories that distinguishes the ordinals from the finite sets is
 not a categorical property at all, and skeletality — which does
 distinguish them — is exactly such a non-invariant property (nLab,
 "skeleton of a category").

 The constructive reading is what the setoid presentation buys.
 Classically one says "every finite set is isomorphic to some
 ordinal" and then chooses, for every set at once, an isomorphism;
 that choice is the axiom of choice, and Theory/Equivalence.v's
 header traces the standard responses to it (Makkai's anafunctors;
 the univalent-foundations dissolution).  Here the choice is made
 once, by the object, and carried: an object of [Set_f] IS a setoid
 together with its counting.  The cardinal functor then exists
 outright, and the equivalence is closed under the global context.
 The same trade recurs across the library wherever a universal
 property is turned into an operation.

 Within this tree the result completes a corner that
 Instance/FinSet.v had left open.  That file builds the skeleton for
 its computational virtues — objects are literal numbers, object
 equality is decidable, and the topos structure on it evaluates by
 [eq_refl] (Instance/FinSet/Topos.v) — and its header explains what
 the skeleton is FOR.  What was missing is the reason one is entitled
 to use it in place of the finite sets at all.  That reason is the
 equivalence proved here, together with [FinSet_skeletal], which says
 the skeleton is a skeleton: it has one object per isomorphism class,
 no more. 

 --------
 为什么一个范畴及其骨架是相同的，以及为什么那需要工作

 nLab:  https://ncatlab.org/nlab/show/skeleton+of+a+category 
 nLab:  https://ncatlab.org/nlab/show/principle+of+equivalence计数是最古老的数学之一，而这个文件是它的范畴形式。说一个有限集合有 n 个元素，就是选择一个与标准 n 元集合的双射；康托的做法是使数字变成次要的，而将双射作为主要的，从而当且仅当存在某个双射时，两个集合具有相同的基数（Fong 和 Spivak，《组合性中的七个草图》，CUP 2019，第 3.2.5 节，正是以这种同构类的方式呈现基数；文件中的常量被命名为 [setf_cardinality]，仅仅是为了避免与 Theory/Metacategory.v 中无关的 [cardinality] 冲突）。范畴陈述增加了函子性：将一个数字分配给一个集合不仅仅是在同构类上定义良好的，它是一个函子，并且它作用于映射的双射选择在结果中是不可见的，直到自然同构为止。麦克莱恩通过这个例子引入了范畴的等价（CWM §I.4，印刷页 17-18），而它必须是等价而不是同构的原因在对象本身就可以看出：序数 2 是一个对象，而两个元素的集合组成一个适当类，因此不存在对象集合的双射，也不应当存在。阿沃迪在 §7.8（印刷页 178）总结了这个道理：表征等价的两个条件——充满且忠实，以及本质上满射——每一个通过包含映射都明显满足，而组合在一个顺序上是恒等映射，而在另一个顺序上仅与之同构。这是等价原理的具体例子：一个区分类从有限集的序数的范畴的性质根本不是范畴性质，而骨架性——恰好区分它们的性质——正是这样一种非不变性质（nLab，“范畴的骨架”）。建设性的理解是集合等价表示所获得的。 传统上有人会说“每个有限集合都同构于某个序数”，然后为每个集合一次性选择一个同构；这种选择就是选择公理，而 Theory/Equivalence.v 的头部追踪了对此的标准回应（Makkai 的自函子；统一基础的解散）。这里的选择由对象一次性完成，并被保留：[Set_f] 的一个对象是一个集合等价物及其计数。于是基数函子就直接存在，并且等价在全局上下文中是封闭的。类似的权衡在整个库中重复出现，每当一个通用性质被转化为一个操作时。在这棵树中，结果完成了 Instance/FinSet.v 留下的一个空白。该文件构建了其计算性质的骨架——对象是字面数字，对象相等性是可判定的，并且其上的拓扑结构通过 [eq_refl] （Instance/FinSet/Topos.v）进行求值——其文件头解释了骨架的用途。缺少的是使用它来替代有限集的合理依据。这个理由就是这里证明的等价性，以及 [FinSet_skeletal]，它说明骨架确实是一个骨架：每个同构类有且仅有一个对象，不多也不少。
*)

(* * ** The canonical n-element setoid / * ** 标准 n 元集合 *)

Definition fin_setoid (n : nat) : SetoidObject := {|
  carrier := Fin.t n;
  is_setoid := Fin_Setoid
|}.

(*
 A setoid map, packaged from its respectfulness proof in the shape the
 proofs below produce.  Nothing here is specific to finiteness. 

 --------
 一个集合映射，从其遵守性证明中打包，按照下面证明产生的形式。这里没有任何内容是特定于有限性的。
*)
Definition setoid_map {X Y : SetoidObject} (f : X → Y)
  (Hf : ∀ a b, a ≈ b → f a ≈ f b) : X ~{Sets}~> Y :=
  Build_SetoidMorphism X (is_setoid X) Y (is_setoid Y) f Hf.

(*
 On the canonical setoids the equivalence is Leibniz equality, so EVERY
 function between them is respectful: this is exactly why the inclusion
 below is full. 

 --------
 在典型的集合等价结构上，等价关系是莱布尼茨等式，因此它们之间的每个函数都是尊重性的：这正是下面包含是满射的原因。
*)
Definition fin_map {m n : nat} (f : Fin.t m → Fin.t n) :
  fin_setoid m ~{Sets}~> fin_setoid n :=
  setoid_map (X := fin_setoid m) (Y := fin_setoid n) f
    (fun a b H => f_equal f H).

(* * ** Counting: a bijection of finite ordinals pins the ordinal / * ** 计数：有限序数的一一对应固定了序数 *)

Fixpoint fin_enum (n : nat) : list (Fin.t n) :=
  match n with
  | O => nil
  | Datatypes.S k => Fin.F1 :: List.map Fin.FS (fin_enum k)
  end.

(* Stated locally rather than taken from the standard library, whose name for it moved between the supported versions. / 本地声明，而不是从标准库中获取，其名称在支持的版本之间有所变化。 *)
Lemma length_of_map {A B : Type} (h : A → B) (l : list A) :
  List.length (List.map h l) = List.length l.
Proof.
  induction l as [| a l IH]; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma fin_enum_length (n : nat) : List.length (fin_enum n) = n.
Proof.
  induction n as [| k IH]; simpl.
  - reflexivity.
  - now rewrite length_of_map, IH.
Qed.

Lemma fin_enum_full {n : nat} (i : Fin.t n) : List.In i (fin_enum n).
Proof.
  induction n as [| k IH].
  - exact (Fin.case0 (fun i => List.In i (fin_enum 0)) i).
  - apply (Fin.caseS' i (fun i => List.In i (fin_enum (Datatypes.S k)))).
    + now left.
    + intro q; right.
      now apply List.in_map.
Qed.

(*
 Injectivity of [Fin.FS], proved through a local partial inverse rather
 than by [injection] on a dependent constructor, so that it holds by
 plain reduction on every supported version. 

 --------
 [Fin.FS] 的单射性，是通过局部部分逆而不是通过依赖构造上的 [injection] 证明的，因此它在每个支持的版本上都通过简单化简成立。
*)
(*
 NOTE ON THE NAME.  Instance/FinSet/Classifier.v and
 Instance/FinSet/Pushout.v already export a [fin_pred], with a
 DIFFERENT type — theirs takes a default value and returns a [Fin.t n],
 this one returns an [option].  Since all three live under
 Instance/FinSet/, the suffix here keeps a reader who greps from
 conflating them. 

 --------
 关于名称的说明。Instance/FinSet/Classifier.v 和 Instance/FinSet/Pushout.v 已经导出一个 [fin_pred]，但类型不同——它们的版本接受一个默认值并返回 [Fin.t n]，而这个版本返回 [option]。由于这三个都位于 Instance/FinSet/ 下，这里的后缀可以防止读者在检索时将它们混淆。
*)
Definition fin_pred_option {n : nat} (i : Fin.t (Datatypes.S n)) : option (Fin.t n) :=
  Fin.caseS' i (fun _ => option (Fin.t n)) None (fun q => Some q).

Lemma FS_injective {n : nat} (x y : Fin.t n) : Fin.FS x = Fin.FS y → x = y.
Proof.
  intro H.
  apply (f_equal fin_pred_option) in H.
  simpl in H.
  now injection H.
Qed.

(* [Fin.FS] is injective, so it carries duplicate-freeness along. / [Fin.FS] 是单射的，所以它保持无重复性。 *)
Lemma nodup_map_FS {k : nat} (l : list (Fin.t k)) :
  List.NoDup l → List.NoDup (List.map Fin.FS l).
Proof.
  induction l as [| a l IH]; simpl; intro Hnd.
  - constructor.
  - inversion Hnd as [| ? ? Hnotin Hnd']; subst.
    constructor.
    + intro Hin.
      apply List.in_map_iff in Hin.
      destruct Hin as [q [Hq Hq']].
      apply FS_injective in Hq; subst.
      contradiction.
    + now apply IH.
Qed.

Lemma fin_enum_nodup (n : nat) : List.NoDup (fin_enum n).
Proof.
  induction n as [| k IH]; simpl.
  - constructor.
  - constructor.
    + intro Hin.
      apply List.in_map_iff in Hin.
      destruct Hin as [q [Hq _]].
      discriminate Hq.
    + now apply nodup_map_FS.
Qed.

(*
 Two finite ordinals connected by mutually inverse maps have the same
 index: each enumeration embeds into the image of the other without
 repetition, so the two lengths bound one another. 

 --------
 两个通过互逆映射连接的有限序数具有相同的指标：每个枚举都嵌入到另一个的像中且没有重复，因此两个长度彼此界定。
*)
Lemma fin_bijection_index {m n : nat}
  (f : Fin.t m → Fin.t n) (g : Fin.t n → Fin.t m)
  (fg : ∀ j, f (g j) = j) (gf : ∀ i, g (f i) = i) : m = n.
Proof.
  assert (Hle : ∀ (p q : nat) (u : Fin.t p → Fin.t q) (v : Fin.t q → Fin.t p),
             (∀ j, u (v j) = j) → (q <= p)%nat).
  { intros p q u v uv.
    rewrite <- (fin_enum_length q), <- (fin_enum_length p).
    rewrite <- (length_of_map u (fin_enum p)).
    apply List.NoDup_incl_length.
    - apply fin_enum_nodup.
    - intros j Hj.
      apply List.in_map_iff.
      exists (v j); split; [apply uv | apply fin_enum_full]. }
  apply Nat.le_antisymm.
  - exact (Hle n m g f gf).
  - exact (Hle m n f g fg).
Qed.

(* * ** The category of finite setoids / * ** 有限集合类型 *)

(*
 An object is a setoid, a number, and a CHOSEN isomorphism between them
 in [Sets] — Mac Lane's [θ_X : X ≅ #X], carried as data.  Two objects
 with the same underlying setoid but different chosen bijections are
 different objects; [two_swap] below is the case that makes the
 asymmetry of the two round trips visible. 

 --------
 一个对象是一个集合等价类、一个数以及它们之间的一个已选择同构，在 [Sets] 中——Mac Lane 的 [θ_X : X ≅ #X]，以数据形式携带。两个具有相同基础集合等价类但不同已选择双射的对象是不同的对象；下面的 [two_swap] 是使两个往返的不对称性明显的情况。
*)
Record FinSetoid : Type := {
  fs_obj : SetoidObject;
  fs_card : nat;
  fs_theta : @Isomorphism Sets fs_obj (fin_setoid fs_card)
}.

(*
 Morphisms, identities, composition, hom-setoid and all five laws are
 [Sets]' own, so nothing is re-proved and the forgetful functor to [Sets]
 is fully faithful.  It is NOT a subcategory: the object map forgets the
 carried bijection and is therefore not injective (see the header). 

 --------
 态射、恒等、组合、同质集合以及所有五条定律都是 [Sets] 自己的，因此没有重新证明，而且到 [Sets] 的忘记函子是完全忠实的。它不是子范畴：对象映射忘记了所携带的双射，因此不是单射（见标题）。
*)
Definition Set_f : Category := {|
  obj := FinSetoid;
  hom := fun A B => fs_obj A ~{Sets}~> fs_obj B;
  homset := fun A B => @homset Sets (fs_obj A) (fs_obj B);
  id := fun A => @id Sets (fs_obj A);
  compose := fun A B C f g => @compose Sets (fs_obj A) (fs_obj B) (fs_obj C) f g;
  compose_respects := fun A B C =>
    @compose_respects Sets (fs_obj A) (fs_obj B) (fs_obj C);
  id_left := fun A B => @id_left Sets (fs_obj A) (fs_obj B);
  id_right := fun A B => @id_right Sets (fs_obj A) (fs_obj B);
  comp_assoc := fun A B C D =>
    @comp_assoc Sets (fs_obj A) (fs_obj B) (fs_obj C) (fs_obj D);
  comp_assoc_sym := fun A B C D =>
    @comp_assoc_sym Sets (fs_obj A) (fs_obj B) (fs_obj C) (fs_obj D)
|}.

(*
 An isomorphism of [Set_f] and an isomorphism in [Sets] between the
 underlying setoids are the same four fields: these two transports
 typecheck by conversion and carry no mathematical content.  They exist
 only so that the direction of the packaging is explicit at use sites. 

 --------
 [Set_f] 的同构和 [Sets] 中底层集合族之间的同构是相同的四个域：这两种传输通过转换进行类型检查，并且不包含任何数学内容。它们的存在仅仅是为了在使用时明确打包的方向。
*)
Definition setf_iso {A B : Set_f}
  (i : @Isomorphism Sets (fs_obj A) (fs_obj B)) : A ≅[Set_f] B :=
  @Build_Isomorphism Set_f A B (to i) (from i)
    (iso_to_from i) (iso_from_to i).

Definition sets_iso {A B : Set_f}
  (i : A ≅[Set_f] B) : @Isomorphism Sets (fs_obj A) (fs_obj B) :=
  @Build_Isomorphism Sets (fs_obj A) (fs_obj B) (to i) (from i)
    (iso_to_from i) (iso_from_to i).

(*
 The packaging is inverse on the nose in both directions.  Stated with
 Leibniz equality rather than ≈ because that is the claim: no data is
 lost or renamed, the two transports are the same four fields. 

 --------
 包装在鼻子上在两个方向上都是相反的。 使用莱布尼茨等式而不是≈来表示，因为这是声明：没有数据丢失或重命名，这两种传输是相同的四个字段。
*)
Example setf_sets_iso (A B : Set_f) (i : A ≅[Set_f] B) :
  setf_iso (sets_iso i) = i.
Proof. now destruct i. Qed.

Example sets_setf_iso (A B : Set_f)
  (i : @Isomorphism Sets (fs_obj A) (fs_obj B)) :
  sets_iso (@setf_iso A B i) = i.
Proof. now destruct i. Qed.

(* * ** The inclusion of finite ordinals / * ** 有限序数的包含 *)

(*
 The canonical objects: [Fin.t n] counted by the IDENTITY bijection.
 Mac Lane makes this choice too ("choose [θ_n = 1_n]"), and it is what
 makes the [Card ◯ FinSet_Incl] round trip strict below — tested, not
 asserted: [Card_conjugation_moves_constant] exhibits an object of the
 same underlying setoid carrying the transposition instead, at which the
 conjugation [θ ∘ f ∘ θ⁻¹] does move a morphism. 

 --------
 典型对象：通过恒等映射 (IDENTITY) 计数的 [Fin.t n]。Mac Lane 也做了这个选择（“选择 [θ_n = 1_n]”），这正是使得下面的 [Card ◯ FinSet_Incl] 循环严格成立的原因——这是经过测试的，而非断言：[Card_conjugation_moves_constant] 展示了一个承载换位的相同基础集族对象，而共轭 [θ ∘ f ∘ θ⁻¹] 则会移动一个态射。
*)
Definition finset_obj (n : nat) : FinSetoid := {|
  fs_obj := fin_setoid n;
  fs_card := n;
  fs_theta := iso_id
|}.

Program Definition FinSet_Incl : FinSet ⟶ Set_f := {|
  fobj := finset_obj;
  fmap := fun m n f => fin_map f
|}.

(** ** The cardinal functor / ** 基本函子 *)

(*
 The two halves of the carried bijection.  Note the asymmetry already
 present here: on the ordinal side the round trip is Leibniz equality
 (the canonical setoid is discrete), on the setoid side only ≈ — which
 is the whole point of allowing an object like [parity_two], where
 [θ⁻¹ (θ a)] is a DIFFERENT natural number of the same parity.  The [=]
 in [theta_to_from] is [Fin_Setoid]'s ≈ written out, not a
 strengthening of it. 

 --------
 被携带的双射的两部分。注意这里已经存在的不对称：在序数方面，往返是莱布尼茨相等（典型的集合等价是离散的），而在集合等价方面只有≈——这正是允许像 [parity_two] 这样的对象的全部意义，其中 [θ⁻¹ (θ a)] 是具有相同奇偶性的不同自然数。[theta_to_from] 中的 [=] 是 [Fin_Setoid] 的≈的写出，而不是对它的强化。
*)
Lemma theta_to_from {A : Set_f} (i : Fin.t (fs_card A)) :
  to (fs_theta A) (from (fs_theta A) i) = i.
Proof. exact (iso_to_from (fs_theta A) i). Qed.

Lemma theta_from_to {A : Set_f} (a : fs_obj A) :
  from (fs_theta A) (to (fs_theta A) a) ≈ a.
Proof. exact (iso_from_to (fs_theta A) a). Qed.

(*
 Where the setoid discipline earns its keep: [Card] is well defined on
 ≈-classes of morphisms precisely because the chosen enumeration is
 respectful.  Over a discrete source it would come free by [f_equal] —
 that is precisely [fin_map] — but [Set_f] has objects like [parity_two]
 where it does not.  (Both conclusions
 are equations in [Fin.t (fs_card _)], where ≈ is Leibniz equality, so
 the [=] is that setoid's ≈.) 

 --------
 集合论纪律体现其价值的地方：[Card] 在态射的≈类上是良定义的，恰恰因为所选择的枚举是尊重性的。在一个离散的源上，它会由[f_equal] 免费得到——那正是[fin_map]——但是[Set_f] 有像[parity_two] 那样的对象，它没有。（两个结论都是[Fin.t (fs_card _)] 中的方程，其中≈是莱布尼茨等式，因此[=] 是那个集合论的≈。）
*)
Lemma card_map_respects {A B : Set_f} (f g : A ~{Set_f}~> B)
  (i : Fin.t (fs_card A)) :
  f ≈ g →
  to (fs_theta B) (f (from (fs_theta A) i))
    = to (fs_theta B) (g (from (fs_theta A) i)).
Proof.
  intro Hfg.
  exact (proper_morphism (to (fs_theta B)) _ _ (Hfg (from (fs_theta A) i))).
Qed.

Lemma card_map_comp {A B C : Set_f} (f : B ~{Set_f}~> C) (g : A ~{Set_f}~> B)
  (i : Fin.t (fs_card A)) :
  to (fs_theta C) (f (g (from (fs_theta A) i)))
    = to (fs_theta C)
        (f (from (fs_theta B) (to (fs_theta B) (g (from (fs_theta A) i))))).
Proof.
  exact (proper_morphism (to (fs_theta C)) _ _
           (proper_morphism f _ _
              (symmetry (theta_from_to (g (from (fs_theta A) i)))))).
Qed.

(*
 Mac Lane's cardinal functor [#]: on objects the carried index, on
 morphisms [# f = θ_Y ∘ f ∘ θ_X⁻¹].  Definable without any choice
 principle exactly because [fs_theta] is data. 

 --------
 Mac Lane 的基数函子 [#]：在对象上承载索引，在态射上是 [# f = θ_Y ∘ f ∘ θ_X⁻¹]。可以在没有任何选择公理的情况下定义，正因为 [fs_theta] 是数据。
*)
Program Definition Card : Set_f ⟶ FinSet := {|
  fobj := fs_card;
  fmap := fun A B f i => to (fs_theta B) (f (from (fs_theta A) i))
|}.
Next Obligation.
  repeat intro.
  now apply card_map_respects.
Qed.
Next Obligation. now apply theta_to_from. Qed.
Next Obligation. now apply card_map_comp. Qed.

(* * ** The inclusion is full, faithful and essentially surjective / * ** 该包含是完全的、忠实的且本质上是满射的 *)

(*
 Awodey's two characteristic conditions, discharged for this instance.
 Fullness and faithfulness are definitional — [prefmap] returns the
 underlying function and [fmap_inj] is the identity — so as stated they
 would hold of any functor that is the identity on hom-carriers; the
 mathematical input is upstream, in [fin_map].  Essential surjectivity
 is the substantive one: the chosen [fs_theta], inverted. 

 --------
 Awodey 的两个特征条件，在此实例中已经被满足。  
 充足性和信实性是定义性的 —— [prefmap] 返回底层函数，[fmap_inj] 是恒等映射 —— 因此如前所述，它们对任何在同态承载上是恒等映射的函子都成立；数学输入在上游，即 [fin_map]。  
 本质上的满射性才是实质性条件：所选择的 [fs_theta] 被反转。
*)
Definition FinSet_Incl_Full : @Full FinSet Set_f FinSet_Incl :=
  @Build_Full FinSet Set_f FinSet_Incl
    (fun m n g i => g i)
    (fun m n g i => eq_refl).

Definition FinSet_Incl_Faithful : @Faithful FinSet Set_f FinSet_Incl :=
  @Build_Faithful FinSet Set_f FinSet_Incl (fun m n f g H => H).

Definition FinSet_Incl_EssSurj :
  @EssentiallySurjective FinSet Set_f FinSet_Incl :=
  @Build_EssentiallySurjective FinSet Set_f FinSet_Incl
    fs_card
    (fun A => @setf_iso (finset_obj (fs_card A)) A (iso_sym (fs_theta A))).

(** ** The equivalence / ** 等价 *)

(*
 Mac Lane's example, obtained through the general criterion rather than
 by hand.  This is the constant to audit with [Print Assumptions]. 

 --------
 Mac Lane 的例子，是通过一般标准获得的，而不是手工得到的。这是使用 [Print Assumptions] 审核的常量。
*)
Definition FinSet_Setf_Equivalence : EquivalenceOfCategories FinSet_Incl :=
  @FF_ESO_Equivalence FinSet Set_f FinSet_Incl
    FinSet_Incl_Full FinSet_Incl_Faithful FinSet_Incl_EssSurj.

Lemma Card_is_quasi_inverse :
  @quasi_inverse FinSet Set_f FinSet_Incl FinSet_Setf_Equivalence ≈ Card.
Proof.
  exists (fun A => iso_id).
  intros A B f i.
  reflexivity.
Qed.

(*
 Sharper than the ≈ above, and the reason it went through by [reflexivity]:
 the quasi-inverse produced by [FF_ESO_Equivalence] and [Card] have the
 SAME object map and the SAME morphism map up to conversion — Leibniz
 equality, not merely ≈.  (The two functor records are still distinct
 terms: they carry different proofs of the three functor laws, which is
 why the comparison above is stated with ≈.) 

 --------
 比上面的 ≈ 更严格，其被 [reflexivity] 通过的原因是：由 [FF_ESO_Equivalence] 和 [Card] 产生的准逆具有相同的对象映射和相同的态射映射，达到了可转换的程度——即莱布尼茨等价，而不仅仅是 ≈。（这两个函子记录仍然是不同的项：它们携带了三个函子定律的不同证明，这就是上面的比较使用 ≈ 的原因。）
*)
Example Card_quasi_inverse_fobj (A : Set_f) :
  fobj[@quasi_inverse FinSet Set_f FinSet_Incl FinSet_Setf_Equivalence] A
    = fobj[Card] A := eq_refl.

Example Card_quasi_inverse_fmap {A B : Set_f} (f : A ~> B) :
  fmap[@quasi_inverse FinSet Set_f FinSet_Incl FinSet_Setf_Equivalence] f
    = fmap[Card] f := eq_refl.

(* * ** The two comparison cells, stated with [Card] / * ** 两个比较单元格，用 [Card] 表示 *)

(*
 The issue's two cells, now phrased with [Card] itself: [# ∘ S ≈ Id]
 and [θ : Id ≅ S ∘ #].  [Card_Incl_id] is proved by [reflexivity] at
 every component (see the strictness lemmas below); [Incl_Card_theta]
 genuinely needs the two round trips. 

 --------
 该问题的两个单元格，现在用 [Card] 本身表述为：[# ∘ S ≈ Id] 和 [θ : Id ≅ S ∘ #]。[Card_Incl_id] 由 [reflexivity] 在每个分量上证明（见下文的严格性引理）；[Incl_Card_theta] 确实需要两次往返。
*)
Definition Card_Incl_id : Card ◯ FinSet_Incl ≈ Id[FinSet].
Proof.
  exists (fun n => iso_id).
  intros m n f i.
  reflexivity.
Defined.

Definition Incl_Card_theta : Id[Set_f] ≈ FinSet_Incl ◯ Card.
Proof.
  exists (fun A => @setf_iso A (finset_obj (fs_card A)) (fs_theta A)).
  intros A B f a.
  (* [f a] first travels along the round trip at A, then back along the round trip at B; both cancellations are [theta_from_to]. / [f a] 先沿着 A 的往返路线旅行，然后沿着 B 的往返路线返回；两次取消都是 [theta_from_to]。 *)
  transitivity (f (from (fs_theta A) (to (fs_theta A) a))).
  - exact (proper_morphism f _ _ (symmetry (theta_from_to a))).
  - exact (symmetry
             (theta_from_to (f (from (fs_theta A) (to (fs_theta A) a))))).
Defined.

Definition Card_Equivalence : EquivalenceOfCategories Card :=
  @Build_EquivalenceOfCategories Set_f FinSet Card FinSet_Incl
    Card_Incl_id Incl_Card_theta.

Definition Incl_Card_theta_iso : Id[Set_f] ≅[Fun] FinSet_Incl ◯ Card :=
  equiv_iso Incl_Card_theta.

(** ** Skeletality / ** 骨骼状 *)

(*
 [FinSet] is skeletal: isomorphic objects are EQUAL.  The conclusion is
 a Leibniz equality of objects, and that is deliberate — equality of
 objects always yields an isomorphism, whereas the converse is precisely
 what a category with repeated isomorphism classes lacks, and SAYING it
 holds here is what the word skeletal means.  Fong and Spivak's §3.2.5 reading needs
 exactly this: the index a finite set is isomorphic to is determined,
 not merely determined up to isomorphism.

 Not vacuous in either direction: the hypothesis is inhabited by
 non-identity isomorphisms ([FinSet_swap_iso], with
 [FinSet_swap_not_identity] showing it is not the identity), and the
 conclusion has bite ([FinSet_one_not_iso_two]). 

 --------
 [FinSet] 是骨架的：同构对象是相等的。结论是对象的莱布尼茨等式，这是刻意为之——对象的相等总是产生一个同构，而反之正是那些具有重复同构类的范畴所缺乏的，而在这里说它成立正是“骨架”一词的意思。Fong 和 Spivak 的 §3.2.5 阅读需要正是这个：索引一个有限集合的同构是确定的，而不仅仅是确定到同构。

 在任意方向上都不是空的：假设存在非同一同构（[FinSet_swap_iso]，其中 [FinSet_swap_not_identity] 显示它不是同一同构），而结论有实质内容（[FinSet_one_not_iso_two]）。
*)
Theorem FinSet_skeletal {m n : FinSet} (i : m ≅ n) : m = n.
Proof.
  exact (fin_bijection_index (to i) (from i) (iso_to_from i) (iso_from_to i)).
Qed.

(** ** Cardinality / ** 基数 *)

(*
 Cardinality as an isomorphism invariant.  The definition simply reads
 the carried index; the theorems say that this is forced —
 [setf_cardinality A] is the unique n with [FinSet_Incl n ≅ A], it is
 constant on isomorphism classes (Cantor's reading), and it separates
 them. 

 --------
 基数作为同构不变量。定义仅仅表示所携带的指标；定理说明这是必然的——[setf_cardinality A] 是唯一的 n，使得 [FinSet_Incl n ≅ A]，它在同构类上是恒定的（康托尔的理解），并且它可以区分它们。
*)
(*
 NOTE ON THE NAME.  Theory/Metacategory.v exports a [cardinality]
 that counts the identity arrows of a metacategory — an unrelated notion.
 The prefix here marks this one as the cardinality of an object of
 [Set_f], so the two cannot be confused. 

 --------
 关于名称的说明。Theory/Metacategory.v 导出了一个 [cardinality]，它用于计算元范畴的身份箭头——这是一个无关的概念。这里的前缀将其标记为 [Set_f] 对象的基数，因此两者不能混淆。
*)
Definition setf_cardinality (A : Set_f) : nat := fs_card A.

Definition setf_cardinality_iso (A : Set_f) : FinSet_Incl (setf_cardinality A) ≅ A :=
  @eso_iso FinSet Set_f FinSet_Incl FinSet_Incl_EssSurj A.

Lemma setf_cardinality_unique (A : Set_f) (n : nat) :
  FinSet_Incl n ≅ A → n = setf_cardinality A.
Proof.
  intro i.
  apply FinSet_skeletal.
  apply (@FullyFaithful FinSet Set_f FinSet_Incl
           FinSet_Incl_Full FinSet_Incl_Faithful).
  exact (iso_compose (iso_sym (setf_cardinality_iso A)) i).
Qed.

Theorem setf_cardinality_iso_invariant (A B : Set_f) :
  A ≅ B → setf_cardinality A = setf_cardinality B.
Proof.
  intro i.
  apply setf_cardinality_unique.
  exact (iso_compose i (setf_cardinality_iso A)).
Qed.

Theorem setf_cardinality_complete (A B : Set_f) :
  setf_cardinality A = setf_cardinality B → A ≅ B.
Proof.
  intro H.
  apply (iso_compose (setf_cardinality_iso B)).
  rewrite <- H.
  exact (iso_sym (setf_cardinality_iso A)).
Qed.

Corollary setf_cardinality_classifies (A B : Set_f) :
  (A ≅ B) ↔ (setf_cardinality A = setf_cardinality B).
Proof.
  split.
  - apply setf_cardinality_iso_invariant.
  - apply setf_cardinality_complete.
Qed.

(* * ** The asymmetry of the two round trips / * ** 两次往返的非对称性 *)

(*
 The strict side.  These three are Leibniz equalities and are genuinely
 stronger than the ≈ / ≅ statements they refine: [Card_Incl_id] compares
 the two functors only up to natural isomorphism, whereas here the
 object map and the morphism map of [Card ◯ FinSet_Incl] are the
 identity's, and the comparison cell computed by [FF_ESO_Equivalence] is
 the identity morphism itself.  All three hold by [eq_refl]. 

 --------
 严格的一面。这三个是莱布尼兹等式，实际上比它们所细化的 ≈ / ≅ 语句更强：[Card_Incl_id] 仅比较两个函子直到自然同构，而在这里 [Card ◯ FinSet_Incl] 的对象映射和态射映射都是恒等的，并且 [FF_ESO_Equivalence] 计算的比较单元就是恒等态射本身。所有三个都由 [eq_refl] 成立。
*)
Lemma Card_Incl_fobj_strict (n : FinSet) : fobj[Card ◯ FinSet_Incl] n = n.
Proof. reflexivity. Qed.

Lemma Card_Incl_fmap_strict {m n : FinSet} (f : m ~> n) :
  fmap[Card ◯ FinSet_Incl] f = f.
Proof. reflexivity. Qed.

Lemma Incl_unit_is_identity (n : FinSet) :
  to (@equivalence_unit_at FinSet Set_f FinSet_Incl FinSet_Setf_Equivalence n)
    = id[n].
Proof. reflexivity. Qed.

(** ** Concrete objects / ** 具体对象 *)

(*
 The non-strict side, at a concrete object.  [two_swap] has the
 canonical carrier [Fin.t 2] but carries the transposition as its chosen
 bijection, so [FinSet_Incl (Card two_swap)] and [two_swap] have the same
 underlying setoid and differ exactly in the choice. 

 --------
 非严格一边，在一个具体对象上。[two_swap] 拥有规范载体 [Fin.t 2]，但将换位作为其选择的双射，因此 [FinSet_Incl (Card two_swap)] 和 [two_swap] 拥有相同的基础集体，并且恰好在选择上有所不同。
*)
Definition fin_swap2 (i : Fin.t 2) : Fin.t 2 :=
  Fin.caseS' i (fun _ => Fin.t 2) (Fin.FS Fin.F1) (fun _ => Fin.F1).

Lemma fin_swap2_involutive (i : Fin.t 2) : fin_swap2 (fin_swap2 i) = i.
Proof.
  apply (Fin.caseS' i (fun i => fin_swap2 (fin_swap2 i) = i)).
  - reflexivity.
  - intro q.
    apply (Fin.caseS' q
             (fun q => fin_swap2 (fin_swap2 (Fin.FS q)) = Fin.FS q)).
    + reflexivity.
    + intro r.
      exact (Fin.case0
               (fun r => fin_swap2 (fin_swap2 (Fin.FS (Fin.FS r)))
                           = Fin.FS (Fin.FS r)) r).
Qed.

Definition fin_swap2_iso :
  @Isomorphism Sets (fin_setoid 2) (fin_setoid 2) :=
  @Build_Isomorphism Sets (fin_setoid 2) (fin_setoid 2)
    (fin_map fin_swap2) (fin_map fin_swap2)
    fin_swap2_involutive fin_swap2_involutive.

Definition two_swap : FinSetoid := {|
  fs_obj := fin_setoid 2;
  fs_card := 2;
  fs_theta := fin_swap2_iso
|}.

Definition FinSet_swap_iso : @Isomorphism FinSet (2 : nat) (2 : nat) :=
  @Build_Isomorphism FinSet (2 : nat) (2 : nat) fin_swap2 fin_swap2
    fin_swap2_involutive fin_swap2_involutive.

Example FinSet_swap_not_identity :
  to FinSet_swap_iso ≈ @id FinSet (2 : nat) → False.
Proof.
  intro H.
  specialize (H Fin.F1).
  discriminate H.
Qed.

(*
 PROJECTION, not computation: the statement is [2 = 2], so the only
 content here is that the hypothesis typechecks — that a non-identity
 isomorphism can be supplied. The inhabitation evidence proper is
 [FinSet_swap_iso] together with [FinSet_swap_not_identity]. 

 --------
 投影，而不是计算：声明是 [2 = 2]，因此这里的唯一内容是该假设类型检查——可以提供一个非恒等同构。实际的居住证据是 [FinSet_swap_iso] 和 [FinSet_swap_not_identity]。
*)
Example FinSet_skeletal_at_swap : (2 = 2)%nat :=
  FinSet_skeletal FinSet_swap_iso.

Example FinSet_one_not_iso_two :
  @Isomorphism FinSet (1 : nat) (2 : nat) → False.
Proof.
  intro i.
  apply FinSet_skeletal in i.
  discriminate i.
Qed.

(*
 The comparison cell at [two_swap] computes to the transposition, and
 is provably not the identity — contrast [Incl_unit_is_identity], which
 holds at EVERY object of [FinSet]. 

 --------
 位于 [two_swap] 的比较单元计算为换位，并且可证明不是恒等 — 对比 [Incl_unit_is_identity]，它在 [FinSet] 的每个对象上都成立。
*)
Example counit_at_two_swap :
  to (@equivalence_counit_at FinSet Set_f FinSet_Incl
        FinSet_Setf_Equivalence two_swap) Fin.F1 = Fin.FS Fin.F1.
Proof. reflexivity. Qed.

Example counit_at_two_swap_not_identity :
  to (@equivalence_counit_at FinSet Set_f FinSet_Incl
        FinSet_Setf_Equivalence two_swap) ≈ @id Set_f two_swap → False.
Proof.
  intro H.
  specialize (H Fin.F1).
  simpl in H.
  discriminate H.
Qed.

(*
 The cardinal functor at work: [two_swap] and [finset_obj 2] have the
 same underlying setoid, so the IDENTITY function is a morphism between
 them — and [# f = θ_Y ∘ f ∘ θ_X⁻¹] conjugates it into the
 transposition.  This is the conjugation formula doing something. 

 --------
 正在发挥作用的基数函子：[two_swap] 和 [finset_obj 2] 有相同的基础集合同态，所以 IDENTITY 函数是它们之间的一个态射 —— 而 [# f = θ_Y ∘ f ∘ θ_X⁻¹] 将其共轭为换位。这就是共轭公式在起作用。
*)
(*
 PROJECTION, not computation: [Card]'s object part IS [fs_card], so this
 reads off a field rather than exercising the functor. The computational
 evidence is [Card_parity_succ_F1]/[_FS] below, which run through the
 enumeration. 

 --------
 投影，而不是计算：[Card] 的对象部分是 [fs_card]，所以这是读取一个字段，而不是执行函子。计算证据如下 [Card_parity_succ_F1] / [_FS]，它们通过枚举运行。
*)
Example Card_two_swap : Card two_swap = 2%nat := eq_refl.

Example Card_conjugates_theta :
  fmap[Card] (fin_map (fun i : Fin.t 2 => i)
                : finset_obj 2 ~{Set_f}~> two_swap) Fin.F1
    = Fin.FS Fin.F1 := eq_refl.

(*
 And the test behind the claim at [finset_obj]: at [two_swap], which
 carries the transposition rather than the identity, [Card] conjugates
 the constant map [fun _ => F1] into the constant map [fun _ => FS F1].
 Had the canonical objects been given a non-identity bijection, the
 [Card ◯ FinSet_Incl] round trip would move morphisms in just this way
 and could not have been strict. 

 --------
 在 [finset_obj] 的声明背后的测试：在 [two_swap]，其中携带了换位而非恒等变换，[Card] 将恒定映射 [fun _ => F1] 共轭为恒定映射 [fun _ => FS F1]。如果标准对象被赋予一个非恒等的双射，[Card ◯ FinSet_Incl] 的往返操作将以这种方式移动态射，并且不可能是严格的。
*)
Example Card_conjugation_moves_constant :
  fmap[Card] (fin_map (fun _ : Fin.t 2 => Fin.F1)
                : two_swap ~{Set_f}~> two_swap) Fin.F1
    = Fin.FS Fin.F1 := eq_refl.

(*
 Sharper, and available here only because both sides have literally the
 same underlying setoid and index, so the two chosen bijections have the
 same type: the composite replaces the carried bijection by the identity
 one.  (This is a Leibniz equality of isomorphisms, not of morphisms;
 what it compares is carried DATA.) 

 --------
 更精确，并且仅在这里可用，因为两边实际上具有相同的底层集合和索引，所以所选的两个双射具有相同的类型：复合将所携带的双射替换为恒等双射。（这是同构的莱布尼茨等式，而不是态射的等式；它比较的是所携带的数据。）
*)
Example Incl_Card_forgets_theta :
  fs_theta (FinSet_Incl (Card two_swap)) = fs_theta two_swap → False.
Proof.
  intro H.
  apply (f_equal (fun i : @Isomorphism Sets (fin_setoid 2) (fin_setoid 2)
                  => to i Fin.F1)) in H.
  simpl in H.
  discriminate H.
Qed.

(* * ** A finite setoid whose carrier is infinite / * ** 其承载集合是无限的有限集合族 *)

(*
 [nat] under equality of parity: two equivalence classes, infinitely
 many inhabitants.  It is an object of [Set_f] of cardinality 2, so
 [Set_f] is not a relabelling of [FinSet] — and the cardinal functor
 computes on it. 

 --------
 在奇偶性相等的情况下：两个等价类，无穷多个元素。它是一个基数为 2 的 [Set_f] 对象，因此 [Set_f] 不是 [FinSet] 的重新标记——并且基数函子在其上进行计算。
*)
Program Definition parity_setoid : SetoidObject := {|
  carrier := nat;
  is_setoid := {| equiv := fun x y => Nat.odd x = Nat.odd y |}
|}.

Definition parity_index (i : Fin.t 2) : nat :=
  Fin.caseS' i (fun _ => nat) (0%nat) (fun _ => 1%nat).

Definition parity_enum (x : nat) : Fin.t 2 :=
  if Nat.odd x then Fin.FS Fin.F1 else Fin.F1.

Lemma parity_enum_respects (a b : nat) :
  Nat.odd a = Nat.odd b → parity_enum a = parity_enum b.
Proof. intro H; unfold parity_enum; now rewrite H. Qed.

Lemma parity_index_respects (i j : Fin.t 2) :
  i = j → Nat.odd (parity_index i) = Nat.odd (parity_index j).
Proof. intro H; now subst. Qed.

Lemma parity_to_from (i : Fin.t 2) : parity_enum (parity_index i) = i.
Proof.
  apply (Fin.caseS' i (fun i => parity_enum (parity_index i) = i)).
  - reflexivity.
  - intro q.
    apply (Fin.caseS' q
             (fun q => parity_enum (parity_index (Fin.FS q)) = Fin.FS q)).
    + reflexivity.
    + intro r.
      exact (Fin.case0
               (fun r => parity_enum (parity_index (Fin.FS (Fin.FS r)))
                           = Fin.FS (Fin.FS r)) r).
Qed.

Lemma parity_from_to (a : nat) :
  Nat.odd (parity_index (parity_enum a)) = Nat.odd a.
Proof.
  unfold parity_enum.
  destruct (Nat.odd a) eqn:Ha; now simpl.
Qed.

Definition parity_iso : @Isomorphism Sets parity_setoid (fin_setoid 2) :=
  @Build_Isomorphism Sets parity_setoid (fin_setoid 2)
    (setoid_map (X := parity_setoid) (Y := fin_setoid 2)
       parity_enum parity_enum_respects)
    (setoid_map (X := fin_setoid 2) (Y := parity_setoid)
       parity_index parity_index_respects)
    parity_to_from parity_from_to.

Definition parity_two : FinSetoid := {|
  fs_obj := parity_setoid;
  fs_card := 2;
  fs_theta := parity_iso
|}.

Lemma succ_respects (a b : nat) :
  Nat.odd a = Nat.odd b → Nat.odd (Datatypes.S a) = Nat.odd (Datatypes.S b).
Proof.
  intro H.
  rewrite !Nat.odd_succ, <- !Nat.negb_odd.
  now rewrite H.
Qed.

Definition parity_succ : parity_two ~{Set_f}~> parity_two :=
  setoid_map (X := parity_setoid) (Y := parity_setoid)
    Datatypes.S succ_respects.

(*
 The carrier is [nat]: an object of [Set_f] is finite in the setoid sense
 — finitely many EQUIVALENCE CLASSES — so its carrier type need not be. 

 --------
 载体是 [nat]：在集合等价意义下，[Set_f] 的一个对象是有限的——等价类有限——所以它的载体类型不必是有限的。
*)
(*
 PROJECTION: an identification of carriers, holding because [parity_two]
 was built over [parity_setoid] whose carrier is [nat]. It records that a
 two-element object may have an infinite carrier; it proves nothing about
 the finiteness witness. 

 --------
 投影：一个承载体的识别，成立因为 [parity_two] 是在 [parity_setoid] 上构建的，其承载体是 [nat]。它记录了一个二元对象可能有无限承载体；它并不证明关于有限性的证据。
*)
Example parity_carrier_is_nat : carrier (fs_obj parity_two) = nat := eq_refl.

(*
 The round trip at [parity_two] is the identity only up to ≈: it sends 3
 to 1.  The [=] here is Leibniz equality of natural numbers and is
 therefore STRICTLY STRONGER than the ≈ of [parity_setoid], under which
 3 and 1 are equal — which is exactly why the statement has content, and
 exactly what [theta_from_to] can and cannot say. 

 --------
 在 [parity_two] 的往返旅行仅在 ≈ 下为恒等：它将 3 发送到 1。这里的 [=] 是自然数的莱布尼茨等式，因此严格比 [parity_setoid] 的 ≈ 强，在 [parity_setoid] 下 3 和 1 是相等的——这正是该陈述有内容的原因，也是 [theta_from_to] 可以说和不能说的地方。
*)
Example parity_round_trip_moves_3 :
  parity_index (parity_enum 3) = 1%nat := eq_refl.

(*
 PROJECTION, for the same reason as [Card_two_swap]: [setf_cardinality]
 is defined as [fs_card], so this reads off the carried index. What makes
 the index CORRECT is [setf_cardinality_unique], and what computes is
 [Card_parity_succ_F1]/[_FS]. 

 --------
 投影，出于与 [Card_two_swap] 相同的原因：[setf_cardinality] 被定义为 [fs_card]，因此它读取了所携带的索引。使索引正确的是 [setf_cardinality_unique]，而计算的是 [Card_parity_succ_F1] / [_FS]。
*)
Example cardinality_parity_two : setf_cardinality parity_two = 2%nat := eq_refl.

Example Card_parity_succ_F1 :
  fmap[Card] parity_succ Fin.F1 = Fin.FS Fin.F1 := eq_refl.

Example Card_parity_succ_FS :
  fmap[Card] parity_succ (Fin.FS Fin.F1) = Fin.F1 := eq_refl.

(*
 The counit at [parity_two], computed.  Again Leibniz equality of
 natural numbers, strictly stronger than [parity_setoid]'s ≈: the
 component does not merely land in the even class, it returns 0. 

 --------
 在 [parity_two] 处计算了余单位。再次，自然数的莱布尼茨等式，严格强于 [parity_setoid] 的 ≈：该分量不仅仅落在偶数类中，它返回 0。
*)
Example counit_at_parity_two :
  to (@equivalence_counit_at FinSet Set_f FinSet_Incl
        FinSet_Setf_Equivalence parity_two) Fin.F1 = 0%nat := eq_refl.

(* * ** Bridge to the general skeleton theory / * ** 通向一般骨架理论 *)

(*
 [Skeletal C] (Theory/Skeleton.v) is by definition [∀ x y, x ≅ y → x = y],
 which is exactly [FinSet_skeletal] above with its binders made explicit.
 The two were proved independently -- this file's concrete counting
 argument, and the general theory's abstract class -- so the bridge is a
 restatement, not a second proof: [FinSet] is the tree's witness that the
 [Skeletal] class is inhabited by a category whose skeletality is a real
 theorem rather than a definitional accident.

 [FinSet_Skeleton] then packages [FinSet] as a [Skeleton] of itself via
 [Skeleton_of_Skeletal]; that is the trivial route, and the non-trivial
 witness for the [Skeleton] record lives in Theory/Skeleton/Separation.v. 

 --------
 [Skeletal C]（Theory/Skeleton.v）按定义是 [∀ x y, x ≅ y → x = y]，
 这正是上面的 [FinSet_skeletal]，只是将其绑定器明确化。
 这两者是独立证明的——这个文件的具体计数论证
 ，以及一般理论的抽象类——所以桥梁只是重述，而不是第二个证明：[FinSet] 是树的证据，表明 [Skeletal] 类由一个其骨架性是一个真正定理而不是定义性偶然的范畴所占据。

 然后 [FinSet_Skeleton] 通过 [Skeleton_of_Skeletal] 将 [FinSet] 打包为 [Skeleton] 本身；这是简单路径，而 [Skeleton] 记录的非平凡证据存在于 Theory/Skeleton/Separation.v 中。
*)

Theorem FinSet_Skeletal : Skeletal FinSet.
Proof. intros m n i; exact (FinSet_skeletal i). Qed.

Definition FinSet_Skeleton : Skeleton FinSet :=
  Skeleton_of_Skeletal FinSet_Skeletal.
