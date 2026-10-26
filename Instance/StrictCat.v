Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(* * * The strict category of categories / * * 严格的类别范畴 *)

(*
 nLab: https://ncatlab.org/nlab/show/strict+category
 nLab: https://ncatlab.org/nlab/show/Cat
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_small_categories

 StrictCat is the category of categories where functors are compared by a
 *strict* relation, in which objects are equal on the nose rather than merely
 isomorphic:

 objects               Categories
 arrows                Functors
 arrow equivalence     Strict equality of functors ([Functor_StrictEq_Setoid])
 identity              Identity Functor
 composition           Horizontal composition of Functors

 Strict equivalence: two functors F, G : C ⟶ D are identified when there is a
 proof [eq_on_obj : ∀ x, F x = G x] of propositional equality on objects,
 together with a coherence condition forcing the morphism maps to agree once
 [fmap F f] and [fmap G f] are transported along [eq_on_obj] into a common
 hom-setoid. This matches the nLab notion of a strict category, whose objects
 carry a genuine equality relation (a *set* of objects), and the resulting
 equality of strict functors: [Ob(F) = Ob(G)] together with compatible
 agreement of the underlying morphism actions.

 Difference from [Cat]: the sibling category [Cat] uses [Functor_Setoid],
 which identifies functors up to natural isomorphism (object maps related by
 [F x ≅ G x]); its isomorphisms are therefore *equivalences* of categories,
 making it the homotopy category Ho(Cat). StrictCat instead uses
 [Functor_StrictEq_Setoid] with [F x = G x], so it is the strict 1-category in
 which an isomorphism is a genuine (on-the-nose) isomorphism of categories —
 matching the textbook bare-name “Cat”. The library nonetheless works up to the
 weaker notion of equivalence in [Cat] almost everywhere, to suit Coq's
 metatheory (no function extensionality); StrictCat is provided for the few
 constructions that genuinely need on-the-nose object equality. Under the axiom
 of choice this strict 1-category is equivalent, as a bicategory, to the weak
 [Cat].

 Strict equality of functors implies natural isomorphism, so there is an
 identity-on-objects comparison functor [StrictCat_to_Cat : StrictCat ⟶ Cat],
 built in [Category.Instance.StrictCat.ToCat]. The strictness of StrictCat is
 what makes functors *out of* it well-defined even when they do not respect
 natural isomorphism — e.g. the underlying-graph functor
 [Category.Construction.Free.Quiver.Forgetful : StrictCat ⟶ Quiv], the
 motivating example of issue #138, which has no counterpart over the weak
 [Cat]. 

 --------
 nLab: https://ncatlab.org/nlab/show/strict+category
 nLab: https://ncatlab.org/nlab/show/Cat
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_small_categories

 StrictCat 是一个类别的类别，在这个类别中函子通过*严格*关系进行比较，其中对象是完全相同的，而不仅仅是同构的：

 对象                  类别
 箭头                  函子
 箭头等价              函子的严格相等（[Functor_StrictEq_Setoid]）
 恒等                  恒等函子
 复合                  函子的水平复合严格等价：当存在一个关于对象的命题等式证明 [eq_on_obj : ∀ x, F x = G x]，并且存在强制态射映射在 [fmap F f] 和 [fmap G f] 沿 [eq_on_obj] 运输到公共同态集群后保持一致的相容条件时，两个函子 F, G : C ⟶ D 被认为是相同的。这与 nLab 中严格范畴的概念一致，其对象具备真正的等式关系（一个对象的*集合*），以及由此得到的严格函子的等式：[Ob(F) = Ob(G)] 以及基础态射作用的相容一致性。与 [Cat] 的区别：兄弟类别 [Cat] 使用 [Functor_Setoid]， 它将函子识别到自然同构（由 [F x ≅ G x] 相关的对象映射）；因此，它的同构是类别的*等价*，使其成为同伦类别 Ho(Cat)。而 StrictCat 则使用带 [F x = G x] 的 [Functor_StrictEq_Setoid]，因此它是严格的 1-类别，在其中同构是类别的真正（严格意义上的）同构——与教材中的“Cat”名称相匹配。然而，该库几乎在所有地方都使用 [Cat] 中的较弱等价概念，以适应 Coq 的元理论（没有函数外延性）；StrictCat 提供给那些确实需要严格对象相等的少数构造。在选择公理下，这个严格的1-范畴作为双范畴与弱 [Cat] 等价。

 函子严格相等意味着自然同构，因此存在一个在对象上保持恒等的比较函子 [StrictCat_to_Cat : StrictCat ⟶ Cat]，它内建于 [Category.Instance.StrictCat.ToCat] 中。StrictCat 的严格性使得即使函子不保持自然同构，从它出发的函子也能被良确定——例如基础图函子 [Category.Construction.Free.Quiver.Forgetful : StrictCat ⟶ Quiv]，它是问题 #138 的动机性例子，而在弱 [Cat] 上没有对应物。
*)

#[export]
Instance StrictCat : Category := {
  obj     := Category;
  hom     := @Functor;
  homset  := @Functor_StrictEq_Setoid;
  id      := @Id;
  compose := @Compose;

  compose_respects := @Compose_respects_stricteq;
  id_left          := @fun_strict_equiv_id_left;
  id_right         := @fun_strict_equiv_id_right;
  comp_assoc       := @fun_strict_equiv_comp_assoc;
  comp_assoc_sym   := fun a b c d f g h =>
    symmetry (@fun_strict_equiv_comp_assoc a b c d f g h)
}.
