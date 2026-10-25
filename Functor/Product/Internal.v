Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Construction.Product.

Generalizable All Variables.

(** The internal product as a bifunctor ×(C) : C ∏ C ⟶ C.  / 作为双函子的内积 ×(C) : C ∏ C ⟶ C。*)

(*
nLab: https://ncatlab.org/nlab/show/product
   Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)

   In a cartesian category C, the binary product is functorial: it assembles
   into a bifunctor ×(C) : C ∏ C ⟶ C from the product category C ∏ C (the
   "product of categories", Construction/Product.v) back into C. This is the
   product *bifunctor*, distinct from a product *of two functors*.

   On objects it sends a pair (x, y) to the product object x × y. On a
   morphism (f, g) : (x, y) ~> (x', y') of C ∏ C — that is, a pair of a
   morphism f : x ~> x' and a morphism g : y ~> y' in C — it yields the
   "cartesian product of morphisms" f × g : x × y ~> x' × y', the unique arrow
   characterized by exl ∘ (f × g) ≈ f ∘ exl and exr ∘ (f × g) ≈ g ∘ exr. By
   the universal property of the product this is the pairing

       (f ∘ exl) △ (g ∘ exr) : x × y ~> x' × y',

   which is exactly the [split] combinator of Structure/Cartesian.v applied to
   the two components. The functor laws hold because pairing is determined by
   the projections: ×(C) preserves id since exl △ exr ≈ id, and preserves
   composition by [fork_comp] together with associativity. 

--------
nLab：https://ncatlab.org/nlab/show/product
 维基百科：https://en.wikipedia.org/wiki/Product_(category_theory)

在笛卡尔类别 C 中，二元乘积是函数式的：它组装
 转化为双函子 ×(C) : C ∏ C ⟶ C 来自产品类别 C ∏ C （
 “类别的产品”，Construction/Product.v) 回到 C。这是
 产品*双函子*，与*两个函子*的产品不同。

在对象上，它将一对 (x, y) 发送到产品对象 x × y。 上一个
 态射 (f, g) : C ∏ C 的 (x, y) ~> (x', y') — 即一对 a
 C 中的态射 f : x ~> x' 和态射 g : y ~> y' — 它产生
 “态射的笛卡尔积” f × g : x × y ~> x' × y'，唯一箭头
 其特征为 exl ∘ (f × g) ≈ f ∘ exl 和 exr ∘ (f × g) ≈ g ∘ exr。 由
 产品的通用属性，这就是配对

(f ∘ exl) △ (g ∘ exr) : x × y ~> x' × y',

这正是 Structure/Cartesian.v 的 [split] 组合器应用于
 两个组件。 函子定律成立是因为配对由下式决定
 投影：×(C) 保留 id，因为 exl △ exr ≈ id，并且保留
 由 [fork_comp] 与关联性组合。 
*)

#[export]
Program Instance InternalProductFunctor `(C : Category) `{@Cartesian C} :
  C ∏ C ⟶ C := {
  fobj := fun p => fst p × snd p;
  fmap := fun _ _ p => (fst p ∘ exl) △ (snd p ∘ exr)
}.
Next Obligation.
  proper.
  simpl in *.
  rewrites.
  reflexivity.
Qed.
Next Obligation.
  simpl in *.
  rewrite <- fork_comp.
  rewrite <- !comp_assoc; cat.
Qed.

Notation "×( C )" := (@InternalProductFunctor C _)
  (at level 0, format "×( C )") : functor_scope.
