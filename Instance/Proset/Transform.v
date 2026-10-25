Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Proset.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(* * * Natural transformations into a preorder / * * 自然变换到一个预序 *)

(*
 nLab:  https://ncatlab.org/nlab/show/preorder
 nLab:  https://ncatlab.org/nlab/show/thin+category
 Book:  Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Springer 1998, §I.4, printed p. 19, exercise 4
 Book:  Fong and Spivak, "Seven Sketches in Compositionality", Cambridge
 2019, §3.3.4, Example 3.57 (printed pp. 96-97) and Exercise 3.58
 (printed p. 97)
 Book:  Riehl, "Category Theory in Context", Dover 2016, §1.4,
 Exercise 1.4.iii (printed p. 30)

 Let [P] be a preorder, regarded as the thin category [Proset P] of
 Instance/Proset.v: objects are the elements of the carrier, and there is a
 morphism [x ~> y] exactly when [R x y] holds.  Mac Lane's exercise asks for
 the natural transformations between two functors [S T : C ⟶ Proset P]:

 a natural transformation [S ⟹ T] exists if and only if [S c ≤ T c] for
 every object [c] of [C], and when it exists it is unique.

 Both halves are visible in the [Proset] construction.  A component of a
 transformation at [c] is by definition a morphism [S c ~> T c], which is
 literally a proof of [R (S c) (T c)]; so a transformation carries exactly a
 pointwise family of order witnesses.  Conversely such a family assembles
 into a transformation with no side condition, because the hom-setoid of
 [Proset] is [fun _ _ => True] (all parallel morphisms are identified), so
 every naturality square commutes for free.  Uniqueness is the same
 observation once more: any two transformations [S ⟹ T] agree componentwise
 under [≈], since [≈] on each hom-set of [Proset] is the total relation.

 The library's setoid discipline is what makes "unique" the right word here.
 Two transformations built from *different* proofs of the same pointwise
 order are not equal in Coq's intensional sense, and nothing in this file
 claims they are; they are equal in the hom-setoid of the functor category,
 which is the library's notion of sameness for morphisms throughout (see
 [Transform_Setoid] in Theory/Natural/Transformation.v).  Every comparison
 of two morphisms below uses [≈] WHEREVER THE COMPARISON IS WHAT IS AT
 STAKE — uniqueness, thinness, the isomorphism laws.

 There is exactly one deliberate exception, and an audit of the first
 commit was right to insist it be named rather than covered by a
 universal: [endo_of_monotone_of_endo_fmap] states an [=] between two
 morphisms of [Nat_Proset].  It is stated that way because it is the
 informative form.  Its [≈] counterpart is vacuous — [≈] between [Proset]
 morphisms is the total relation, so the [≈] version would hold of any two
 morphisms whatever — whereas the [=] version says something real: the
 arrow part of the round trip is the ORIGINAL arrow, on the nose.  The
 remaining [=] statements in this file are round-trip identities for the
 translation functions and an object-part agreement, and each is flagged
 where it appears. 

 --------
 nLab:   https://ncatlab.org/nlab/show/preorder 
 nLab:   https://ncatlab.org/nlab/show/thin+category 
 书籍:  Mac Lane，《为在职数学家准备的范畴论》，第2版，
 Springer 1998，第I.4节，印刷页19，练习题4
 书籍:  Fong 和 Spivak，《组合性中的七个小结》，Cambridge
 2019，第3.3.4节，例3.57（印刷页96-97）和练习题3.58
 （印刷页97）
 书籍:  Riehl，《语境中的范畴论》，Dover 2016，第1.4节，
 练习题1.4.iii（印刷页30）

 设 [P] 为一个预序，被视为薄范畴 [Proset P] 的
 Instance/Proset.v：对象是承载集合的元素，并且当 [R x y] 成立时
 存在一个态射 [x ~> y]。Mac Lane 的练习要求找出两个函子 [S T : C ⟶ Proset P] 之间的自然变换：存在自然变换 [S ⟹ T] 当且仅当 [S c ≤ T c] 对 [C] 的每个对象 [c] 都成立，并且当它存在时，它是唯一的。

 在 [Proset] 构造中可以看到这两个部分。变换在 [c] 处的分量按定义是一个态射 [S c ~> T c]，这实际上是 [R (S c) (T c)] 的证明；因此一个变换精确地携带一系列按点的顺序证明。反过来，这样的一系列可以组装成一个没有附加条件的变换，因为 [Proset] 的同态集体是 [fun _ _ => True]（所有平行态射都被识别），所以每个自然性方格自动交换。唯一性也是同样的观察：任何两个变换 [S ⟹ T] 在 [≈] 下在每个分量上都一致，因为 [Proset] 的每个同态集上的 [≈] 是全关系。库的集合等价纪律使得“唯一”在这里是合适的词。
 由同一点顺序的*不同*证明构建的两个变换在 Coq 的强度意义下并不相等，本文件中也没有任何内容声称它们相等；它们在函子范畴的同构集合中是相等的，这是库中整体现态下对态射相同性的定义（参见 Theory/Natural/Transformation.v 中的 [Transform_Setoid]）。下面对两个态射的每一次比较，都使用 [≈]，只要比较的内容涉及关键问题——唯一性、薄性、同构律。确切地说，有一个特意的例外，对第一次提交的审查坚持要求它被命名而不是由通用的覆盖是正确的：[endo_of_monotone_of_endo_fmap] 陈述了 [=] 在两个 [Nat_Proset] 的态射之间。之所以这样陈述，是因为它是信息性的形式。它的 [≈] 对应版本是空洞的——[≈] 在 [Proset] 态射之间是完全关系，所以 [≈] 版本会适用于任意两个态射——而 [=] 版本则说明了真实的内容：往返的箭头部分正好是原始的箭头。该文件中其余的 [=] 语句是翻译函数的往返恒等式以及对象部分的一致性，并且每条语句在出现的地方都有标记。
*)

(*
 What the exercise buys, and where the dual argument stops

 nLab:  https://ncatlab.org/nlab/show/thin+category
 nLab:  https://ncatlab.org/nlab/show/functor+category
 Book:  Fong and Spivak, "Seven Sketches in Compositionality", Cambridge
 2019, §3.3.4
 Book:  Riehl, "Category Theory in Context", Dover 2016, §1.4

 Existence-and-uniqueness together say that the hom-sets of the functor
 category [[C, Proset P]] are subsingletons: at most one morphism up to [≈]
 between any two objects.  That is precisely thinness, so the functor
 category into a preorder is itself a preorder — the headline of Fong and
 Spivak's Example 3.57, which the pointwise existence lemma alone does not
 state.  The order in question is the pointwise one, [S ≤ T] iff [S c ≤ T c]
 for all [c], and the identification of [[C, Proset P]] with the proset of
 that order is [Fun_Proset_iso] (in [Cat]) and [Fun_Proset_strict_iso] (in
 [StrictCat]) below.  Instantiated at the naturals it says that the category
 of endofunctors of [(ℕ, ≤)] is the preorder of monotone maps
 [ℕ → ℕ] ordered pointwise — [endo_nat_monotone_iso].

 The identification at the naturals has a subtlety the general statement does
 not.  A functor [Proset P ⟶ Proset Q] *is* a monotone map: its object part
 is the map, its arrow part is the monotonicity proof, and the functor laws
 are vacuous in a thin target.  Passing from a monotone map back to a functor
 nonetheless has to supply arrow data, and the choice is unique only up to
 [≈] — which is exactly why the round trip is an isomorphism in [Cat] rather
 than an equality of functors.  Note that [≅[Cat]] in this library already
 IS equivalence of categories, because [Functor_Setoid] identifies naturally
 isomorphic functors (Instance/Cat.v); the on-the-nose statements available
 here are recorded separately as [monotone_of_endo_of_monotone] and
 [endo_of_monotone_of_endo].

 The dual is false, and Fong and Spivak's Exercise 3.58 asks for the
 counterexample: transformations *out of* a preorder need not be unique,
 since nothing about the domain constrains the target's hom-sets.  Below,
 the domain is the preorder [(ℕ, ≤)] and the target is the walking parallel
 pair [Parallel] of Instance/Parallel.v, whose two arrows [ParX ~> ParY] are
 kept apart by a boolean tag in its hom-setoid; the two constant-functor
 transformations built from them are shown non-equivalent in the
 transformation setoid ([proset_out_not_unique]), not merely written
 differently.

 Riehl's Exercise 1.4.iii is the special case in which the domain is also a
 preorder: a natural transformation between monotone maps of preorders is
 unique when it exists.  Everything below quantifies over an arbitrary domain
 category [C], so that case is an instance rather than a separate theorem;
 [proset_to_proset_transform_iff] records it explicitly. 

 --------
 练习所涉及的对象，以及二元论证的终点

 nLab:   https://ncatlab.org/nlab/show/thin+category 
 nLab:   https://ncatlab.org/nlab/show/functor+category 
 书籍:  Fong 和 Spivak，《组合性中的七个草图》，剑桥 2019，第3.3.4节
 书籍:  Riehl，《情境中的范畴论》，多佛 2016，第1.4节存在性与唯一性一起表明函子范畴 [[C, Proset P] 的 Hom 集是子单子集：在任意两个对象之间最多有一个态射（最多到 [≈]）。这正是薄性，因此映入偏序的函子范畴本身也是偏序——这是 Fong 和 Spivak 的示例 3.57 的标题，仅凭逐点存在性引理并未说明。相关的顺序是逐点顺序，即 [S ≤ T] 当且仅当 [S c ≤ T c] 对所有 [c] 成立，并且将 [[C, Proset P] ] 与该顺序的前集（proset）对应的识别是 [Fun_Proset_iso]（在 [Cat] 中）和 [Fun_Proset_strict_iso]（在 [StrictCat] 中）如下。在自然数上实例化，它表明 [(ℕ, ≤)] 的端函子范畴是单调映射 [ℕ → ℕ] 的偏序范畴，逐点有序——[endo_nat_monotone_iso]。在自然变换处的同一性有一种一般陈述没有的微妙性。函子 [Proset P ⟶ Proset Q] *确实是*一个单调映射：它的对象部分是映射，它的箭头部分是单调性证明，而在薄目标中函子定律是空的。然而，从单调映射回到函子仍然必须提供箭头数据，并且该选择在 [≈] 下是唯一的——这正是为什么在 [Cat] 中往返是一个同构而不是函子的相等。注意，该库中的 [≅[Cat] 已经是范畴等价，因为 [Functor_Setoid] 自然地识别同构函子（Instance/Cat.v）；这里可用的精确声明则单独记录为 [monotone_of_endo_of_monotone] 和 [endo_of_monotone_of_endo]。对偶是错误的，Fong 和 Spivak 的练习 3.58 要求提供反例：*从*预序出发的变换不必是唯一的，因为域的任何特性都不约束目标的 Hom 集。如下，域是预序  [(ℕ, ≤)] ，目标是 Instance/Parallel.v 中的 walking parallel pair  [Parallel] ，它的两条箭头  [ParX ~> ParY] 由同态集中的布尔标签区分开来；用它们构建的两个常量函子变换在变换集合 [proset_out_not_unique] 中显示为不等价，而不仅仅是写法不同。Riehl 的练习 1.4.iii 是一个特殊情况，其中定义域也是一个预序：当存在时，预序单调映射之间的自然变换是唯一的。下面的所有内容都对任意定义域范畴 [C] 进行量化，因此该情况是一个实例，而不是一个单独的定理；[proset_to_proset_transform_iff] 明确记录了它。
*)

(* * ** Mac Lane §I.4, exercise 4: existence and uniqueness / * ** Mac Lane §I.4，第4题：存在性和唯一性 *)

Section ProsetTransform.

Context {C : Category}.
Context {A : Type}.
Context {R : relation A}.
Context {P : PreOrder R}.

(*
 The pointwise order on functors into a proset: [S ≤ T] when [S c ≤ T c] for
 every object [c].  Note that [S c] is the object part of the functor applied
 to [c] (via the [fobj] coercion), so this is a relation on [C ⟶ Proset P]
 with values in [Prop], exactly as [R] itself is. 

 --------
 函数子到一个预序集的按点顺序：当每个对象都满足时。注意， 是函数子作用于 的对象部分（通过 强制类型转换），所以这是 在 中的一个值在 的关系，正如 本身一样。
*)

Definition proset_pointwise (S T : C ⟶ Proset P) : Prop :=
  ∀ c : C, R (S c) (T c).

(*
 Right to left: a pointwise family of order witnesses IS a transformation.
 The components are the witnesses themselves, and both naturality fields are
 proofs of [True] because the hom-setoid of [Proset] identifies all parallel
 morphisms.  No hypothesis on [S], [T] or [C] is used. 

 --------
 从右到左：逐点的阶见证族是一个变换。组件本身就是见证，而两个自然性场都是  [True] 的证明，因为  [Proset] 的同态集合识别了所有平行态射。没有使用关于  [S]、[T] 或 [C] 的假设。
*)

Definition proset_transform {S T : C ⟶ Proset P}
           (H : proset_pointwise S T) : S ⟹ T :=
  @Build_Transform C (Proset P) S T (fun c => H c)
                   (fun _ _ _ => I) (fun _ _ _ => I).

(* Left to right: read the pointwise witnesses off the components. / 从左到右：从各个分量中读取逐点见证。 *)

Definition proset_pointwise_of {S T : C ⟶ Proset P}
           (N : S ⟹ T) : proset_pointwise S T :=
  fun c => transform N c.

(*
 The existence criterion.  [↔] is notation (declared in Lib/Foundation.v)
 for [iffT] of Coq.Classes.CRelationClasses, the Type-valued
 biconditional the library uses for statements whose two directions carry
 computational content — here the two translations just given. 

 --------
 存在准则。[↔] 是在 Lib/Foundation.v 中声明的符号，用于 Coq.Classes.CRelationClasses 的 [iffT]，是库用于那些两个方向都具有计算内容的陈述的类型值双条件——这里指刚给出的两个翻译。
*)

Theorem proset_transform_iff (S T : C ⟶ Proset P) :
  (S ⟹ T) ↔ proset_pointwise S T.
Proof. exact (@proset_pointwise_of S T, @proset_transform S T). Qed.

(*
 The two translations are mutually inverse.  One round trip is a propositional
 equality of order-witness families (it holds by eta), the other an
 equivalence of transformations; the latter cannot be an equality, since
 rebuilding a transformation replaces its naturality proofs.

 The [=] in the first is deliberate and is not a lapse from the library's
 [≈] discipline: it is a round-trip statement about the two translation
 functions, and its [≈] counterpart would be vacuous here, since [≈] between
 two families of [Proset] morphisms is the total relation.  Everywhere the
 comparison of two morphisms is what is at stake — uniqueness, thinness, the
 isomorphism laws — the statements below use [≈].

 AND THE SECOND ROUND TRIP IS VACUOUS, which the first commit advertised as
 though it were evidence of invertibility.  It is not: it is
 [proset_transform_unique] wearing a round-trip costume.  Its proof is
 [fun _ => I], and the same proof establishes `M ≈ N` for ANY two
 transformations between the same functors, related to the translations or
 not.  The informative half of the pair is therefore the [=] statement
 alone; the [≈] statement is kept because the shape of a round trip is
 what a reader looks for, but it carries no information beyond thinness. 

 --------
 这两个翻译是相互逆的。 一次往返是关于序见证族的命题等式（它由η成立），另一次是变换的等价；后者不能是等式，因为重建一个变换会替换其自然性证明。

 第一个中的 [=] 是故意的，并不是库的 [≈] 规范的疏忽：它是关于这两个翻译函数的一次往返声明，而它的 [≈] 对应在此处将是空洞的，因为两个 [Proset] 同族之间的 [≈] 是全关系。 在任何地方，比较两个态射才是关键——唯一性、稀薄性、同构定律——下面的陈述使用 [≈] 。第二次往返是空洞的，第一次提交宣传它时，仿佛它是可逆性的证据。它不是：它是穿着往返服装的 [proset_transform_unique]。它的证明是 [fun _ => I]，并且相同的证明可以建立 `M ≈ N`，对任意两个在同一函子之间的变换，无论是否与翻译相关。对偶的有信息的一半因此仅是 [=] 语句；[≈] 语句被保留是因为读者会寻找往返的形状，但它除稀薄性之外不携带任何信息。
*)

Theorem proset_pointwise_of_transform {S T : C ⟶ Proset P}
        (H : proset_pointwise S T) :
  proset_pointwise_of (proset_transform H) = H.
Proof. reflexivity. Qed.

Theorem proset_transform_of_pointwise {S T : C ⟶ Proset P} (N : S ⟹ T) :
  proset_transform (proset_pointwise_of N) ≈ N.
Proof. exact (fun _ => I). Qed.

(*
 Uniqueness: any two transformations [S ⟹ T] are equal in the hom-setoid.
 The proof is [fun _ => I]: componentwise the goal is the trivial relation of
 [Proset]'s hom-setoid.  It is stated all the same, as the exercise does. 

 --------
 唯一性：在同值集合中，任意两个变换 [S ⟹ T] 是相等的。证明是 [fun _ => I]：在分量上，目标是 [Proset] 的同值集合的平凡关系。它仍然如练习中所述的那样陈述。
*)

Theorem proset_transform_unique {S T : C ⟶ Proset P} (α β : S ⟹ T) : α ≈ β.
Proof. exact (fun _ => I). Qed.

(*
 The headline of the exercise, both halves in one statement: the hom-setoid
 of [[C, Proset P]] between any two objects is inhabited exactly when the
 pointwise order holds, and has at most one element up to [≈]. 

 --------
 练习的标题，两部分合在一个陈述中：当且仅当逐点顺序成立时，任意两个对象之间的 [[C, Proset P] 的同构集合存在，并且至多有一个元素，直到 [≈]。
*)

Theorem proset_transform_subsingleton (S T : C ⟶ Proset P) :
  ((S ⟹ T) ↔ proset_pointwise S T) ∧ (∀ α β : S ⟹ T, α ≈ β).
Proof. exact (proset_transform_iff S T, @proset_transform_unique S T). Qed.

(* * ** Seven Sketches Example 3.57: the functor category is thin / * ** 七个草图 示例 3.57：函子范畴是稀薄的 *)

(*
 Thinness of [[C, Proset P]] is uniqueness restated one level up: any two
 parallel morphisms of the functor category agree under [≈].  (The library
 has no [Thin] predicate to instantiate — there is no Structure/Thin.v and no
 such class anywhere in the tree — so the property is stated directly.) 

 --------
 [[C, Proset P] 的稀薄性是独特性在更高一级上的重新表述：该函子范畴中任何两个平行的态射在 [≈] 下都相同。（库中没有 [Thin] 谓词可以实例化——没有 Structure/Thin.v，也没有在树中的任何该类——因此该性质是直接陈述的。）
*)

Theorem Fun_Proset_thin (S T : [C, Proset P])
        (α β : S ~{[C, Proset P]}~> T) : α ≈ β.
Proof. exact (fun _ => I). Qed.

(*
 Hence a preorder.  The pointwise order on functors is reflexive and
 transitive because [R] is, so it presents [[C, Proset P]] as a proset. 

 --------
 因此是一个预序。函子上的点态顺序是自反的且传递的，因为[R]是的，所以它将[[C, Proset P]]表示为一个预序集合。
*)

(*
 Kept a plain [Definition] rather than an [Instance]: registering a
 [PreOrder] for an arbitrary pointwise relation as a global typeclass
 instance would enter resolution for every [PreOrder] goal in the library,
 and nothing here needs it to be found automatically. 

 --------
 保持使用普通的 [Definition] 而不是 [Instance]：将 [PreOrder] 注册为任意逐点关系的全局类型类实例，会导致库中的每个 [PreOrder] 目标都进入解析，而这里没有什么需要它自动被找到。
*)

Definition Fun_Proset_PreOrder : PreOrder proset_pointwise.
Proof.
  constructor.
  - intros S c.
    exact (@PreOrder_Reflexive A R P (S c)).
  - intros S T U H1 H2 c.
    exact (@PreOrder_Transitive A R P (S c) (T c) (U c) (H1 c) (H2 c)).
Defined.

Definition Fun_Proset : Category := Proset Fun_Proset_PreOrder.

(*
 The comparison, in both directions.  Each is the identity on objects: the
 objects of [Fun_Proset] are by construction the functors [C ⟶ Proset P],
 i.e. the objects of [[C, Proset P]].  Only the morphism parts differ, and
 they are the two translations of the existence criterion. 

 --------
 双向的比较。每一个在对象上都是恒等的：[Fun_Proset] 的对象按照构造是函子 [C ⟶ Proset P]，即 [[C, Proset P] 的对象。只有态射部分不同，它们是存在性准则的两种翻译。
*)

Program Definition Fun_Proset_forward : [C, Proset P] ⟶ Fun_Proset := {|
  fobj := fun S => S;
  fmap := fun S T N => proset_pointwise_of N
|}.

Program Definition Fun_Proset_backward : Fun_Proset ⟶ [C, Proset P] := {|
  fobj := fun S => S;
  fmap := fun S T H => proset_transform H
|}.

(*
 [[C, Proset P] ≅[Cat] Fun_Proset].  Because both composites are the identity
 on objects definitionally, the natural isomorphisms witnessing the two
 round trips have identity components, and their coherence conditions are
 discharged by thinness of the targets. 

 --------
 [[C, Proset P] ≅ [Cat] Fun_Proset]。因为两个复合在对象上在定义上都是恒等的，见证两个往返的自然同构具有恒等分量，并且它们的一致性条件被目标的稀薄性所满足。
*)

Theorem Fun_Proset_iso : [C, Proset P] ≅[Cat] Fun_Proset.
Proof.
  unshelve econstructor.
  - exact Fun_Proset_forward.
  - exact Fun_Proset_backward.
  - exists (fun x => @iso_id Fun_Proset x).
    intros; exact I.
  - exists (fun x => @iso_id ([C, Proset P]) x).
    intros; exact (fun _ => I).
Defined.

(*
 The same comparison in [StrictCat], where functors are compared by
 [Functor_StrictEq_Setoid]: propositional equality of object parts together
 with agreement of the morphism parts in the target hom-setoid.  Here the
 object parts are equal by [eq_refl] — both composites are literally the
 identity on objects — and the morphism condition is trivial because both
 categories are thin.  This is stronger than the [Cat] statement — strict
 equality of functors implies natural isomorphism (Instance/StrictCat.v's
 header) and the converse fails (Instance/Cat.v, which is where that
 failure is actually recorded) — and it is worth having precisely because
 [≅[Cat]] in this library IS equivalence of categories, never an
 on-the-nose isomorphism.  It is still *not* the assertion that the two
 composite functors are equal as records, which would need function
 extensionality to identify their proof fields.

 A reader should also not over-read the strict form HERE.  Because both
 categories are thin, the arrow-agreement leg of the strict hom-setoid is
 the trivial relation, so what this theorem asserts beyond the [Cat] form
 is that the two comparison functors agree with the identity ON OBJECTS,
 definitionally.  That is a real strengthening and it is why the object leg
 is [eq_refl], but it is not a bijection of hom-sets — thin categories have
 nothing to bijate.  The content of the comparison lives in the functors
 themselves, which carry the criterion. 

 --------
 在 [StrictCat] 中进行了相同的比较，其中函子通过 [Functor_StrictEq_Setoid] 进行比较：对象部分的命题等价以及目标 Hom-集合中态射部分的一致性。这里对象部分根据 [eq_refl] 是相等的——两个复合函子在对象上都是字面意义上的恒等——而态射条件是平凡的，因为两个范畴都是稀疏的。这比 [Cat] 的陈述更强——函子的严格相等意味着自然同构（Instance/StrictCat.v 的标题中提到），而其逆命题不成立（Instance/Cat.v 中实际记录了该失败）——并且其价值正在于 [≅[Cat] 在该库中是范畴的等价，而从不要求逐点同构。这仍然*不是*声称两个复合函子作为记录是相等的，这将需要函数外延性来识别它们的证明字段。

 读者也不应过度解读这里的严格形式。因为这两个范畴都是稀疏的，严格同态集的箭头一致性部分是平凡关系，所以这个定理在  [Cat]  形式之外所断言的是两个比较函子在对象上与身份函子一致，这是定义上的。也就是说，这是一个真正的加强，这也是对象部分是  [eq_refl] 的原因，但它不是同态集的双射——稀疏范畴什么都没有可以进行双射。比较的内容存在于函子自身，它们携带了判据。
*)

Theorem Fun_Proset_strict_iso : [C, Proset P] ≅[StrictCat] Fun_Proset.
Proof.
  unshelve econstructor.
  - exact Fun_Proset_forward.
  - exact Fun_Proset_backward.
  - exists (fun x => eq_refl).
    intros; exact I.
  - exists (fun x => eq_refl).
    intros; exact (fun _ => I).
Defined.

End ProsetTransform.

(* * ** Riehl Exercise 1.4.iii: the preorder-to-preorder case / * ** Riehl 练习 1.4.iii：从预序到预序的情况 *)

(*
 The development above quantifies over an arbitrary domain category [C], so
 the case in which the domain is itself a preorder — Riehl's exercise, and
 the setting of Seven Sketches' monotone maps — is an instance rather than a
 separate theorem.  It is recorded here explicitly. 

 --------
 上述发展在任意域类别 [C] 上进行量化，因此，当域本身是一个预序——Riehl 的练习，以及《七幅素描》中单调映射的设置——时，这只是一个实例，而不是一个独立的定理。这里明确记录了这一点。
*)

Corollary proset_to_proset_transform_iff
          {B : Type} {Rb : relation B} (Q : PreOrder Rb)
          {A : Type} {R : relation A} (P : PreOrder R)
          (S T : Proset Q ⟶ Proset P) :
  (S ⟹ T) ↔ (∀ b : B, R (S b) (T b)).
Proof. exact (proset_transform_iff S T). Qed.

Corollary proset_to_proset_transform_unique
          {B : Type} {Rb : relation B} (Q : PreOrder Rb)
          {A : Type} {R : relation A} (P : PreOrder R)
          {S T : Proset Q ⟶ Proset P} (α β : S ⟹ T) : α ≈ β.
Proof. exact (proset_transform_unique α β). Qed.

(* * ** Seven Sketches Example 3.57 at the naturals: monotone maps / * ** 七个素描 示例 3.57 在自然数上：单调映射 *)

(*
 [Nat_Proset] is the preorder [(ℕ, ≤)] as a category: the example
 [LessThanEqualTo_Category] of Instance/Proset.v.  Instance/Poset.v exports a
 same-named example, so the reference below is fully qualified. 

 --------
 [Nat_Proset] 是类别的预序 [(ℕ, ≤)]：实例/上偏序集.v 的示例 [LessThanEqualTo_Category] 导出一个同名的示例，因此下面的引用是完全限定的。
*)

Definition Nat_Proset : Category :=
  Category.Instance.Proset.LessThanEqualTo_Category.

(* Monotone maps [ℕ → ℕ], ordered pointwise. / 单调映射 [ℕ → ℕ] ，按点逐个有序。 *)

Definition Monotone : Type :=
  ∃ m : nat → nat,
    ∀ x y : nat, PeanoNat.Nat.le x y → PeanoNat.Nat.le (m x) (m y).

Definition monotone_le : relation Monotone :=
  fun m m' => ∀ n : nat, PeanoNat.Nat.le (`1 m n) (`1 m' n).

Definition monotone_le_PreOrder : PreOrder monotone_le.
Proof.
  constructor.
  - intros m n.
    exact (PeanoNat.Nat.le_refl (`1 m n)).
  - intros m m' m'' H1 H2 n.
    exact (PeanoNat.Nat.le_trans _ _ _ (H1 n) (H2 n)).
Defined.

Definition MonotoneProset : Category := Proset monotone_le_PreOrder.

(*
 An endofunctor of [(ℕ, ≤)] IS a monotone map: its object part is the map and
 its arrow part is the monotonicity proof.

 Every [Monotone] value in this file is built in tactic mode so that the
 expected type drives the elaboration of the dependent pair.  Written as a
 term, Coq 8.19 and 8.20 infer a NON-dependent [sigT] predicate for the pair
 and then cannot reconcile it with [Monotone], whose predicate genuinely
 mentions the map; taking the goal as given removes that guess. 

 --------
 [(ℕ, ≤)] 的一个 endofunctor 是一个单调映射：它的对象部分是映射，箭头部分是单调性证明。

 本文件中的每个 [Monotone] 值都是在 tactic 模式下构建的，因此预期类型会驱动依赖对的详细化。以项的方式书写时，Coq 8.19 和 8.20 会为该对推断出一个非依赖的 [sigT] 谓词，然后无法将其与 [Monotone] 调和，因为后者的谓词确实涉及该映射；将目标视为已给定可以消除此猜测。
*)

Definition monotone_of_endo (F : Nat_Proset ⟶ Nat_Proset) : Monotone.
Proof.
  exists (fobj[F]).
  intros x y h.
  exact (fmap[F] h).
Defined.

(*
 Conversely a monotone map determines an endofunctor.  The arrow part has to
 be supplied — it is the monotonicity proof — and the three functor laws are
 proofs of [True] in the thin target. 

 --------
 相反，一个单调映射决定了一个自函子。箭头部分必须被提供——它是单调性证明——而三个函子定律是在薄目标中 [True] 的证明。
*)

Program Definition endo_of_monotone (m : Monotone) : Nat_Proset ⟶ Nat_Proset := {|
  fobj := `1 m;
  fmap := fun x y h => `2 m x y h
|}.

(*
 One round trip holds on the nose: rebuilding a monotone map through its
 endofunctor returns it up to eta of the sigma pair. 

 --------
 一次往返紧紧抓住核心：通过其自函子重建单调映射，使其返回到西格玛对的 eta。
*)

Theorem monotone_of_endo_of_monotone (m : Monotone) :
  monotone_of_endo (endo_of_monotone m) = m.
Proof. destruct m; reflexivity. Qed.

(*
 The other round trip returns a functor with the same object part and the
 same arrow part — both hold by [eq_refl], recorded below — but with freshly
 built proof fields.  Identifying those with the original's would need
 function extensionality, which this library does not assume; what IS
 available axiom-free is equivalence in [Functor_StrictEq_Setoid], i.e. equal
 object parts plus agreeing arrow parts. 

 --------
 另一个往返返回一个具有相同对象部分和相同箭头部分的函子——两者均由 [eq_refl] 维持，如下所示——但具有新构建的证明字段。将它们与原来的证明字段进行识别需要函数外延性，而该库并未假设这一点；无需公理可用的则是在 [Functor_StrictEq_Setoid] 中的等价性，即对象部分相等且箭头部分一致。
*)

Example endo_of_monotone_of_endo_fobj (F : Nat_Proset ⟶ Nat_Proset) :
  fobj[endo_of_monotone (monotone_of_endo F)] = fobj[F] := eq_refl.

Example endo_of_monotone_of_endo_fmap (F : Nat_Proset ⟶ Nat_Proset)
        (x y : nat) (h : PeanoNat.Nat.le x y) :
  fmap[endo_of_monotone (monotone_of_endo F)] h = fmap[F] h := eq_refl.

Theorem endo_of_monotone_of_endo (F : Nat_Proset ⟶ Nat_Proset) :
  endo_of_monotone (monotone_of_endo F) ≈[StrictCat] F.
Proof.
  exists (fun x => eq_refl).
  intros; exact I.
Qed.

(* The comparison functors. / 比较函数对象。 *)

Program Definition Endo_Monotone_forward :
  [Nat_Proset, Nat_Proset] ⟶ MonotoneProset := {|
  fobj := monotone_of_endo;
  fmap := fun F G N n => transform N n
|}.

Program Definition Endo_Monotone_backward :
  MonotoneProset ⟶ [Nat_Proset, Nat_Proset] := {|
  fobj := endo_of_monotone;
  fmap := fun m m' H =>
    @Build_Transform Nat_Proset Nat_Proset
      (endo_of_monotone m) (endo_of_monotone m')
      (fun n => H n) (fun _ _ _ => I) (fun _ _ _ => I)
|}.

(*
 The headline of Example 3.57 at the naturals: the category of endofunctors
 of [(ℕ, ≤)] is the preorder of monotone maps ordered pointwise.

 The strength achieved is an isomorphism in [Cat] — which in this library IS
 equivalence of categories, since [Functor_Setoid] identifies naturally
 isomorphic functors (Instance/Cat.v).  Unlike [Fun_Proset_strict_iso] there
 is no [StrictCat] counterpart here: the composite
 [Endo_Monotone_backward ◯ Endo_Monotone_forward] sends a functor to a
 functor with the same object and arrow parts but rebuilt proof fields, and
 the [StrictCat] hom-setoid would require those two *functors* to be
 propositionally equal as objects of [[Nat_Proset, Nat_Proset]], which is
 function extensionality applied to their [True]-valued fields.  The
 on-the-nose content that IS available is isolated in
 [monotone_of_endo_of_monotone], [endo_of_monotone_of_endo] and the two
 [eq_refl] examples above. 

 --------
 例 3.57 的标题在自然数处：[(ℕ, ≤)] 的 endofunctors 类别是按点序排列的单调映射的前序。

 实现的强度是在 [Cat] 中的同构——在这个库中，这就是类别等价，因为 [Functor_Setoid] 自然识别同构的函子（Instance/Cat.v）。不像 [Fun_Proset_strict_iso]，这里没有 [StrictCat] 对应：复合 [Endo_Monotone_backward ◯ Endo_Monotone_forward] 将一个函子映射到一个具有相同对象和箭头部分但重建证明字段的函子，而 [StrictCat] hom-setoid 将要求这两个*函子*作为 [[Nat_Proset, Nat_Proset] 的对象在命题上相等，这相当于对它们的 [True] 值字段应用函数外延性。实际可用的内容则被隔离在 [monotone_of_endo_of_monotone]、[endo_of_monotone_of_endo] 以及上述两个 [eq_refl] 示例中。
*)

Theorem endo_nat_monotone_iso :
  [Nat_Proset, Nat_Proset] ≅[Cat] MonotoneProset.
Proof.
  unshelve econstructor.
  - exact Endo_Monotone_forward.
  - exact Endo_Monotone_backward.
  - unshelve refine (_; _).
    + intro m.
      unshelve econstructor.
      * intro n; exact (PeanoNat.Nat.le_refl (`1 m n)).
      * intro n; exact (PeanoNat.Nat.le_refl (`1 m n)).
      * exact I.
      * exact I.
    + intros; exact I.
  - unshelve refine (_; _).
    + intro F.
      unshelve econstructor.
      * exact (@Build_Transform Nat_Proset Nat_Proset
                 (endo_of_monotone (monotone_of_endo F)) F
                 (fun n => PeanoNat.Nat.le_refl (F n))
                 (fun _ _ _ => I) (fun _ _ _ => I)).
      * exact (@Build_Transform Nat_Proset Nat_Proset
                 F (endo_of_monotone (monotone_of_endo F))
                 (fun n => PeanoNat.Nat.le_refl (F n))
                 (fun _ _ _ => I) (fun _ _ _ => I)).
      * exact (fun _ => I).
      * exact (fun _ => I).
    + intros; exact (fun _ => I).
Defined.

(* * ** The criterion has teeth: existence and non-existence / * ** 这个标准有分量：存在与不存在 *)

(*
 Neither half of the exercise is vacuous.  The two monotone maps below are
 comparable in one direction and not the other, and the criterion converts
 that numeric fact into the existence — respectively the non-existence — of a
 natural transformation.  In particular [no_transform_id_to_zero] runs the
 forward direction of [proset_transform_iff] to REFUTE the existence of a
 transformation, which a vacuously true criterion could not do. 

 --------
 练习的两部分都不是空洞的。下面的两个单调映射在一个方向上是可比的，而在另一个方向上则不可比，该判据将这一数值事实转换为自然变换的存在——或者分别是不存在。特别地，[no_transform_id_to_zero] 运行 [proset_transform_iff] 的正向方向以反驳变换的存在，而一个空洞的真判据无法做到这一点。
*)

Definition monotone_zero : Monotone.
Proof.
  exists (fun _ : nat => 0%nat).
  intros x y h.
  exact (PeanoNat.Nat.le_refl 0%nat).
Defined.

Definition monotone_id : Monotone.
Proof.
  exists (fun n : nat => n).
  intros x y h.
  exact h.
Defined.

Definition Endo_zero : Nat_Proset ⟶ Nat_Proset := endo_of_monotone monotone_zero.
Definition Endo_id : Nat_Proset ⟶ Nat_Proset := endo_of_monotone monotone_id.

(* [0 ≤ n] holds pointwise, so a transformation exists (and by [proset_transform_unique] it is the only one up to [≈]). / [0 ≤ n] 在每一点上都成立，因此存在一个变换（并且根据 [proset_transform_unique]，它是唯一的，最多相差 [≈] ）。 *)

Definition zero_le_id : proset_pointwise Endo_zero Endo_id.
Proof.
  intro n.
  exact (PeanoNat.Nat.le_0_l n).
Defined.

Definition transform_zero_to_id : Endo_zero ⟹ Endo_id :=
  proset_transform zero_le_id.

(* The converse pointwise order breaks down at [1], so by the criterion there is no transformation in the other direction. / 逆点态顺序在 [1] 处失效，因此根据这一标准没有向另一个方向的变换。 *)

Theorem not_id_le_zero : ¬ proset_pointwise Endo_id Endo_zero.
Proof.
  intro H.
  specialize (H 1%nat).
  simpl in H.
  inversion H.
Qed.

Theorem no_transform_id_to_zero : ¬ (Endo_id ⟹ Endo_zero).
Proof.
  intro N.
  exact (not_id_le_zero (proset_pointwise_of N)).
Qed.

(* * ** Seven Sketches Exercise 3.58, clause 2: the dual is refuted / * ** 七个草图练习3.58，第2条：对偶被反驳 *)

(*
 Transformations *out of* a preorder need not be unique.  The domain is the
 preorder [(ℕ, ≤)] — a genuine preorder with infinitely many objects and
 non-identity arrows — and the target is the walking parallel pair
 [Parallel] of Instance/Parallel.v, whose hom-setoid compares the boolean tag
 of an arrow and so genuinely tells [ParOne] and [ParTwo] apart.  ([_2] of
 Instance/Two.v would not serve: it is thin, with [TwoXY] the only arrow
 [TwoX ~> TwoY] and [Morphism_equality] for its hom-setoid, so no two
 parallel arrows there are distinguishable.)

 The two functors are the constant functors at [ParX] and [ParY], obtained
 from the diagonal [Diagonal] of Functor/Diagonal.v; the two transformations
 are the images under the diagonal of the two parallel arrows, so their
 naturality is [Diagonal]'s own. 

 --------
 从一个预序导出的变换不一定是唯一的。定义域是预序  [(ℕ, ≤)] —— 一个拥有无限多个对象和非同一箭头的真正预序 —— 目标是 Instance/Parallel.v 中的平行对 [Parallel]，其同态集合会比较箭头的布尔标记，因此可以真正区分 [ParOne] 和 [ParTwo]。 (Instance/Two.v 中的 [_2] 不适用：它是薄的，同态集合中只有 [TwoXY] 这个箭头 [TwoX ~> TwoY] 和 [Morphism_equality]，因此没有两个平行箭头可以区分。)

 两个函子是常值函子，分别在 [ParX] 和 [ParY] 处得到，从 Functor/Diagonal.v 的对角线 [Diagonal] 导出；两个变换是通过对角线作用于两个平行箭头的图像，因此它们的自然性就是 [Diagonal] 自身的自然性。
*)

Definition par_one : ParX ~{Parallel}~> ParY := (true; ParOne).
Definition par_two : ParX ~{Parallel}~> ParY := (false; ParTwo).

Definition ConstParX : Nat_Proset ⟶ Parallel :=
  @Diagonal Parallel Nat_Proset ParX.
Definition ConstParY : Nat_Proset ⟶ Parallel :=
  @Diagonal Parallel Nat_Proset ParY.

Definition proset_out_one : ConstParX ⟹ ConstParY :=
  fmap[@Diagonal Parallel Nat_Proset] par_one.
Definition proset_out_two : ConstParX ⟹ ConstParY :=
  fmap[@Diagonal Parallel Nat_Proset] par_two.

(*
 Distinctness in the transformation setoid, which is what the exercise wants:
 not that the two are written differently, but that they cannot be identified
 under [≈].  Testing the components at the object [0] reduces the claim to
 [true = false]. 

 --------
 在变换范畴中的不同性，这正是练习所要求的：
 并不是说两者写法不同，而是它们在 [≈] 下无法被识别。 在对象 [0] 上测试这些分量将该断言简化为 [true = false]。
*)

Theorem proset_out_not_unique : ¬ (proset_out_one ≈ proset_out_two).
Proof.
  intro H.
  specialize (H 0%nat).
  simpl in H.
  discriminate.
Qed.

(*
 For contrast, in the direction the exercise does hold, any pair of functors
 out of [Parallel] has at most one transformation between them once the
 *target* is a preorder — an instance of [proset_transform_unique]. 

 --------
 作为对比，在练习成立的方向上，任何来自  [Parallel]  的函子对之间，一旦 *目标* 是一个预序 —— 也就是 [proset_transform_unique] 的实例 —— 它们之间最多有一个变换。
*)

Corollary proset_in_unique {A : Type} {R : relation A} (P : PreOrder R)
          {S T : Parallel ⟶ Proset P} (α β : S ⟹ T) : α ≈ β.
Proof. exact (proset_transform_unique α β). Qed.
