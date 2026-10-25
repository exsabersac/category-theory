Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

(** The pointwise product of two functors into a monoidal category.  / 两个函子的逐点乘积形成幺半群范畴。*)

(*
nLab: https://ncatlab.org/nlab/show/monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

   Given two functors F, G : C ⟶ D into a monoidal category D, their pointwise
   product F :*: G : C ⟶ D acts objectwise by the tensor of D:

     (F :*: G) x  =  F x ⨂ G x          (on objects)
     (F :*: G) f  =  fmap[F] f ⨂ fmap[G] f  (on arrows, i.e. bimap (F f) (G f))

   The functor laws hold pointwise: each follows from the corresponding law in
   F and G together with the bifunctoriality of the tensor ⊗ (bimap_respects,
   bimap_id_id, bimap_comp). This is the construction by which a monoidal
   structure on D is transported pointwise to the functor category [C, D], the
   unit being the constant functor at the monoidal unit I.

   This is the OBJECTWISE/pointwise tensor of two functors with a common
   domain and codomain. It is distinct from:
     - Functor/Construction/Product.v, the componentwise product F ∏⟶ G of
       functors on product categories, C ∏ J ⟶ D ∏ K; and
     - the coend tensor of functors ∫^c F c ⨂ G c (nLab "tensor product of
       functors"), which is not this pointwise construction. 

--------
nLab：https://ncatlab.org/nlab/show/monoidal+category
 维基百科：https://en.wikipedia.org/wiki/Monoidal_category

给定两个函子 F, G : C ⟶ D 到幺半群范畴 D 中，它们的逐点
 乘积 F :*: G : C ⟶ D 通过 D 的张量进行对象操作：

(F :*: G) x = F x ⨂ G x（在物体上）
 (F :*: G) f = fmap[F] f ⨂ fmap[G] f（在箭头上，即 bimap (F f) (G f)）

函子定律逐点成立：每个定律都遵循以下相应定律：
 F 和 G 以及张量 ⊗ 的双函性 (bimap_respects,
 bimap_id_id、bimap_comp）。 这是幺半群的构造
 D 上的结构被逐点传输到函子类别 [C, D]，
 单位是幺半群单位 I 处的常数函子。

这是具有共同点的两个函子的对象/逐点张量
 域和辅域。 它不同于：
 - Functor/Construction/Product.v，分量积 F ∏⟶ G 的
 产品类别上的函子，C ∏ J ⟶ D ∏ K； 和
 - 函子 ∫^c F c ⨂ G c 的共端张量（nLab“张量积
 函子”），这不是逐点构造。 
*)

#[export]
Program Instance Product
        {C : Category} {D : Category} `{@Monoidal D}
        {F : C ⟶ D} {G : C ⟶ D} : C ⟶ D := {
  fobj := fun x => (F x ⨂ G x)%object;          (* objectwise tensor: F x ⨂ G x *)
  fmap := fun _ _ f => fmap[F] f ⨂ fmap[G] f     (* arrowwise: bimap (F f) (G f) *)
}.
Next Obligation.
  proper;
  apply bimap_respects;
  now apply fmap_respects.
Qed.
Next Obligation. normal; reflexivity. Qed.

Notation "F :*: G" := (@Product _ _ _ F%functor G%functor)
  (at level 9) : functor_scope.
