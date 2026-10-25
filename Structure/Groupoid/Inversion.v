Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Groupoid.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Structure.Groupoid.

Generalizable All Variables.

(* * * A groupoid is isomorphic to its opposite / * * 一个范畴群同构于它的对偶 *)

(*
 nLab:      https://ncatlab.org/nlab/show/groupoid
 nLab:      https://ncatlab.org/nlab/show/opposite+category
 Book:      Riehl, "Category Theory in Context", Example 1.3.14, clauses
 (i) and (ii), printed pp. 21-22

 Riehl records that any groupoid is isomorphic to its opposite, by the
 identity-on-objects functor sending each morphism to its inverse; clause
 (i) is the one-object case, the device by which a right action of a group
 is presented as a left action.  This file builds that functor
 ([Inversion]) and proves the isomorphism ([Inversion_iso]).

 HOW STRONG THE ISOMORPHISM IS.  In this library `≅[Cat]` is NOT an
 isomorphism of categories: the hom-setoid of [Cat] is [Functor_Setoid],
 which identifies functors up to natural isomorphism, so an isomorphism in
 [Cat] IS an equivalence of categories — Theory/Equivalence.v says exactly
 that, and its [Equivalence_to_Cat_Iso]/[Cat_Iso_to_Equivalence] repack the
 two notions into one another.  The statement below is therefore made in
 [StrictCat] (Instance/StrictCat.v), whose hom-setoid is
 [Functor_StrictEq_Setoid]: two functors are identified there when their
 object maps are propositionally EQUAL and their morphism maps agree, after
 transport along that equality, up to `≈`.  So [Inversion_iso] says

 - the two composites are the identity on objects on the nose, and
 - each composite sends every morphism to one equivalent to itself,

 which is what "isomorphism of categories" can mean in a setoid library
 without function extensionality (Leibniz equality of the two functors is
 not available, and is not claimed).  It implies the [Cat]-level statement,
 through [Inversion_Cat_iso] below; the converse implication does not hold
 in general, since equivalent categories need not be isomorphic — the
 essay heading Theory/Equivalence.v cites finite-dimensional vector spaces
 against the small category of natural numbers and matrices.

 Contents:

 Inversion G         the identity-on-objects functor C ⟶ C^op
 Inversion_iso       C ≅[StrictCat] C^op
 Inversion_Cat_iso   the weaker C ≅[Cat] statement, derived
 Deloop_Inversion_iso  Riehl's clause (i): B G ≅ (B G)^op
 core_Inversion_iso    the same for the core of any category
 Z3_inversion_not_identity  an instance where the morphism map really
 moves an arrow 

 --------
 nLab:       https://ncatlab.org/nlab/show/groupoid 
 nLab:       https://ncatlab.org/nlab/show/opposite+category 
 书籍:      Riehl，《语境中的范畴论》，例 1.3.14，第 (i) 和 (ii) 条款，印刷页 21-22

 Riehl 记录了任何群体都是与其对偶同构的，通过对对象恒等的函子将每个态射映射到其逆态射；条款 (i) 是单对象情况，也是将群的右作用表示为左作用的方法。此文件构建了该函子 ( [Inversion] ) 并证明了同构 ( [Inversion_iso] )。同构的强度。在这个库中，`≅ [Cat]ZZ ` 不是范畴的同构：[Cat] 的 Hom-setoid 是 [Functor_Setoid]，它将函子同一自然同构视为相同，因此在 [Cat] 中的同构就是范畴等价——Theory/Equivalence.v 正是这样表述的，而它的 [Equivalence_to_Cat_Iso] / [Cat_Iso_to_Equivalence] 将这两种概念相互重新打包。因此，下面的陈述是在 [StrictCat]（Instance/StrictCat.v）中提出的，其 Hom-setoid 是 [Functor_StrictEq_Setoid]：当两个函子在对象映射上命题上相等，并且在该等式下通过传输其态射映射都一致（至 `≈`）时，它们被视为相同。因此 [Inversion_iso] 表示

 - 两个复合函子在对象上严格为恒等，且
 - 每个复合函子将每个态射映射到与自身等价的态射。这就是“范畴同构”在没有函数外延性的 setoid 库中可能的含义（两个函子之间的莱布尼茨等价不可用，也没有宣称）。它通过下面的 [Inversion_Cat_iso] 意味着 [Cat] 级别的陈述；相反的蕴含一般不成立，因为等价的范畴不一定同构——文章标题 Theory/Equivalence.v 引用了有限维向量空间与自然数和矩阵的小范畴作比较。

 目录：Inversion G         对象恒等函子 C ⟶ C^op
 Inversion_iso       C ≅ [StrictCat]  C^op
 Inversion_Cat_iso   较弱的 C ≅ [Cat]  陈述，由此得出
 Deloop_Inversion_iso  Riehl 的条款 (i)：B G ≅ (B G)^op
 core_Inversion_iso    对任意范畴的核也是一样
 Z3_inversion_not_identity  一个例子，其中态射映射确实
 移动了一个箭头
*)

(*
 Why inversion is a functor at all, and what it is used for

 nLab:  https://ncatlab.org/nlab/show/opposite+category
 Book:  Riehl, "Category Theory in Context", Example 1.2.2(iii)

 Inversion reverses composition: (f ∘ g)⁻¹ ≈ g⁻¹ ∘ f⁻¹, which is
 [ginv_comp] in Structure/Groupoid.v.  Taking the codomain to be C^op is
 what makes that law the functoriality law rather than an obstruction to
 it — composition in C^op is composition in C with its arguments swapped,
 so the [fmap_comp] obligation below is discharged by [ginv_comp] verbatim,
 with no reordering step.  This is the standard reason a contravariant
 construction is presented as a covariant functor out of (or into) an
 opposite category.  (For a groupoid whose composition happens to be
 commutative — the delooping of an abelian group, say — the two orders
 agree and inversion is an endofunctor as well; nothing below relies on
 either case.)

 Its classical use, which is Riehl's clause (i), is that a right action of
 a group G — a functor (B G)^op ⟶ C — becomes a left action by
 precomposition with the inversion isomorphism.  Group theory states the
 same fact elementwise: x · g becomes g⁻¹ · x.  Because the composite of
 inversion with itself is the identity up to `≈`, the translation is
 reversible, which is what makes "right action" and "left action" two
 presentations of one notion rather than two notions.

 Construction/Deloop/Opposite.v handles a neighbouring statement that
 should not be confused with this one: there [Deloop_op] compares (B M)^op
 with B (M^op) for an arbitrary MONOID M — no inverses are involved, and the
 opposite monoid genuinely differs from M when M is not commutative.  The
 isomorphism here is available only for groupoids, and identifies C with
 C^op rather than with the delooping of anything. 

 --------
 为什么逆转本身是一个函子，以及它的用途

 nLab:   https://ncatlab.org/nlab/show/opposite+category 
 书籍:  Riehl，《上下文中的范畴论》，例子 1.2.2(iii)求逆会颠倒复合：(f ∘ g)⁻¹ ≈ g⁻¹ ∘ f⁻¹，在 Structure/Groupoid.v 中表示为 [ginv_comp]。将余域取为 C^op 就是使该律成为函子律而不是对它的阻碍——C^op 中的复合就是 C 中复合但交换了参数，因此下面的 [fmap_comp] 义务可以按原样由 [ginv_comp] 解除，无需重新排序步骤。这是将一个逆变构造表示为一个从（或到）对偶范畴的协变函子的标准原因。（对于一个其复合恰好是可交换的群族——比如一个阿贝尔群的去环化——两种顺序是一致的，求逆也是一个端函子；以下内容不依赖于任一情况。）它的经典用法，即 Riehl 的条款 (i)，是一个群 G 的右作用——一个函子 (B G)^op ⟶ C——通过与逆同构的预组合变为左作用。群论以元素方式陈述相同的事实：x · g 变为 g⁻¹ · x。因为逆操作与自身的复合在 `≈` 上同一，所以这种转换是可逆的，这正是“右作用”和“左作用”是一个概念的两种表述而非两个不同概念的原因。Construction/Deloop/Opposite.v 处理一个相邻的语句，不应将其与此语句混淆：那里 [Deloop_op] 比较 (B M)^op 与 B (M^op) 对于任意 MONOID M — 不涉及逆元，而且当 M 非交换时，对偶幺半群与 M 确实不同。这里的同构仅对群范畴可用，并且将 C 识别为 C^op，而不是识别为任何对象的去环（delooping）。
*)

(** ** The functor / ** 函子 *)

(*
 Identity on objects, and f ↦ f⁻¹ on morphisms.  Each functor law is a
 [ginv] law from Structure/Groupoid.v: respectfulness is [ginv_respects],
 preservation of identities is [ginv_id], and preservation of composition
 is [ginv_comp] — whose right-hand side g⁻¹ ∘ f⁻¹ IS composition in C^op,
 with no reordering needed. 

 --------
 在对象上是恒等映射，在态射上是 f ↦ f⁻¹。每个函子定律都是 Structure/Groupoid.v 中的 [ginv] 定律：保持性是 [ginv_respects]，保持恒等映射是 [ginv_id]，保持复合是 [ginv_comp] —— 其右边 g⁻¹ ∘ f⁻¹ 就是 C^op 中的复合，无需重新排序。
*)
Program Definition Inversion {C : Category} (G : IsGroupoid C) : C ⟶ C^op := {|
  fobj := fun x => x;
  fmap := fun x y f => ginv G f
|}.
Next Obligation. now apply ginv_respects. Qed.
Next Obligation. now apply ginv_id. Qed.
Next Obligation. now apply ginv_comp. Qed.

(*
 The functor is the identity on objects, literally: [fobj] is [fun x => x],
 so this [=] is an equality of objects holding by [eq_refl], not a claim
 about morphisms. 

 --------
 函子在对象上是恒等的，字面意思是：[fobj] 是 [fun x => x]，所以这个 [=] 是由 [eq_refl] 保持的对象的等式，而不是关于态射的主张。
*)
Example Inversion_identity_on_objects {C : Category} (G : IsGroupoid C)
  (x : C) : fobj[Inversion G] x = x := eq_refl.

(*
 The same functor for C^op, which is a groupoid by [IsGroupoid_op].  Its
 codomain is (C^op)^op, and Construction/Opposite.v makes that C by
 [reflexivity] — the involution is definitional there, so no transport is
 needed to read this as a functor C^op ⟶ C. 

 --------
 C^op 的相同函子，它是由 [IsGroupoid_op] 定义的群。它的余域是 (C^op)^op，而 Construction/Opposite.v 通过 [reflexivity] 使其成为 C——在这里自反定义是定义性的，所以不需要迁移就可以将其作为一个函子 C^op ⟶ C 来理解。
*)
Definition Inversion_op {C : Category} (G : IsGroupoid C) : C^op ⟶ C :=
  Inversion (IsGroupoid_op G).

(** ** The isomorphism / ** 同构 *)

(*
 Riehl, Example 1.3.14(ii).  Both composites are the identity on objects on
 the nose, so the object-equality component is [eq_refl] and the transports
 in [Functor_StrictEq_Setoid] disappear; what remains in each case is
 (f⁻¹)⁻¹ ≈ f, which is [ginv_involutive]. 

 --------
 Riehl，例 1.3.14(ii)。 两个复合在对象上完全是恒等的，因此对象相等分量是 [eq_refl]，而 [Functor_StrictEq_Setoid] 中的迁移消失；每种情况下剩下的是 (f⁻¹)⁻¹ ≈ f，这就是 [ginv_involutive]。
*)
Program Definition Inversion_iso {C : Category} (G : IsGroupoid C) :
  C ≅[StrictCat] C^op := {|
  to   := Inversion G;
  from := Inversion_op G
|}.
Next Obligation.
  exists (fun x => eq_refl).
  intros x y f.
  exact (ginv_involutive G f).
Qed.
Next Obligation.
  exists (fun x => eq_refl).
  intros x y f.
  exact (ginv_involutive G f).
Qed.

(*
 The weaker [Cat]-level statement, obtained by transporting along the
 identity-on-objects comparison functor [StrictCat_to_Cat]
 (Instance/StrictCat/ToCat.v) — a functor carries isomorphisms to
 isomorphisms ([fobj_iso], Theory/Functor.v).  Per this file's header this
 is an EQUIVALENCE of categories, not an isomorphism of them; it is
 recorded because it is the form most consumers in the library take. 

 --------
 较弱的 [Cat] 级别陈述，通过沿着对象上的恒等比较函子 [StrictCat_to_Cat] (Instance/StrictCat/ToCat.v) 传输获得——函子把同构映射到同构 ([fobj_iso], Theory/Functor.v)。根据本文件的头部，这是范畴的等价，而不是它们的同构；它被记录下来是因为它是库中大多数使用者采用的形式。
*)
Definition Inversion_Cat_iso {C : Category} (G : IsGroupoid C) :
  C ≅[Cat] C^op :=
  fobj_iso StrictCat_to_Cat C (C^op) (Inversion_iso G).

(** ** Instances / ** 实例 *)

(*
 Riehl's clause (i): the delooping of a group is isomorphic to its
 opposite, by inversion.  This is the one-object case of the statement
 above, and the device by which a right action of G — a functor
 (B G)^op ⟶ C — is presented as a left action B G ⟶ C, by precomposing
 with this isomorphism; elementwise, x · g becomes g⁻¹ · x. 

 --------
 Riehl 的条款 (i)：一个群的去环化（delooping）与其对立群通过取逆同构。这是上述陈述中的单对象情况，也是将 G 的右作用——一个函子 (B G)^op ⟶ C——表示为左作用 B G ⟶ C 的方法，通过与此同构进行前合成；在元素层面上，x · g 变为 g⁻¹ · x。
*)
Definition Deloop_Inversion_iso (G : GrpObject) :
  Deloop G ≅[StrictCat] (Deloop G)^op :=
  Inversion_iso (Deloop_IsGroupoid G).

(*
 At Z/2, concretely — so the statement is inhabited at an actual group and
 not only parametrically.

 DEGENERATE, and flagged as such: every element of Z/2 is its own inverse,
 so the morphism map of [Inversion] is the identity function here and this
 instance exercises nothing about inversion.  The next one does. 

 --------
 在 Z/2 上，具体来说——所以该陈述在一个实际的群上是有实例的，而不仅仅是参数化的。

 退化，并且被标记为退化：Z/2 的每个元素都是它自身的逆，所以 [Inversion] 的态射映射在这里是恒等函数，这个实例没有涉及任何关于求逆的操作。下一个实例会涉及。
*)
Definition Bool_Inversion_iso :
  Deloop Bool_Xor_Grp ≅[StrictCat] (Deloop Bool_Xor_Grp)^op :=
  Deloop_Inversion_iso Bool_Xor_Grp.

(*
 Z/3 is the smallest group for which inversion moves an element, so it is
 the smallest instance at which the functor is not the identity on
 morphisms.  Structure/Groupoid.v supplies the group. 

 --------
 Z/3 是最小的群，其中取逆运算会移动一个元素，因此它是函子在态射上不是恒等的最小实例。Structure/Groupoid.v 提供了该群。
*)
Definition Z3_Inversion_iso :
  Deloop Z3_Grp ≅[StrictCat] (Deloop Z3_Grp)^op :=
  Deloop_Inversion_iso Z3_Grp.

(*
 The morphism map really moves the arrow [Z3_1].  Both [=]s are Leibniz
 equality on [Z3], which is exactly the `≈` of that carrier setoid, so
 nothing weaker is being claimed. 

 --------
 同态映射确实移动了箭头 [Z3_1]。两个 [=] 是 [Z3] 上的莱布尼茨等式，这正是该载体集合的 `≈`，因此没有声称任何较弱的内容。
*)
Example Z3_inversion_nontrivial :
  @fmap _ _ (Inversion deloop_Z3_groupoid) ttt ttt Z3_1 = Z3_2 := eq_refl.

Lemma Z3_inversion_not_identity :
  @fmap _ _ (Inversion deloop_Z3_groupoid) ttt ttt Z3_1 <> Z3_1.
Proof. discriminate. Qed.

(*
 And the core of ANY category is isomorphic to its opposite, since the core
 is always a groupoid ([core_is_groupoid]).  This holds for every C
 whatever, so the family of instances is as large as the library's supply
 of categories. 

 --------
 任何范畴的核心都是与其对偶范畴同构的，因为核心总是一个群范畴（ [core_is_groupoid] ）。这对任何 C 都成立，因此实例的集合与库中范畴的数量一样大。
*)
Definition core_Inversion_iso (C : Category) :
  Groupoid C ≅[StrictCat] (Groupoid C)^op :=
  Inversion_iso (core_is_groupoid C).
