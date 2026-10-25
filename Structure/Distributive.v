Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/distributive+category
 Wikipedia: https://en.wikipedia.org/wiki/Distributive_category

 A (finitary) distributive category is a category with finite products and
 finite coproducts in which products distribute over coproducts. Concretely,
 for all objects the canonical morphism

 x × y + x × z ~> x × (y + z),

 induced by the coproduct injections via x × inl and x × inr, is an
 isomorphism (the binary distributivity law), and likewise the canonical
 morphism

 0 ~> x × 0

 into the nullary product is an isomorphism (the nullary law, equivalently
 x × 0 ≅ 0). Together these say that the functor x × - preserves finite
 coproducts. The two sources state the canonical map in the direction
 x × y + x × z ~> x × (y + z); since we record an [Isomorphism] rather than a
 directed map, the orientation chosen below is immaterial.

 The nullary law does not follow from binary distributivity in general (it
 must be assumed), and one of its consequences is that the initial object of
 a distributive category is strict. Every bicartesian closed category is
 distributive, because x × - then has a right adjoint and so preserves all
 colimits (see [Structure.BiCCC]). 

 --------
 nLab:  https://ncatlab.org/nlab/show/distributive+category 
 维基百科:  https://en.wikipedia.org/wiki/Distributive_category 

 （有限）分配范畴是具有有限积和有限余积的范畴，并且积对余积分配。具体来说，对于所有对象，由余积注入通过 x × inl 和 x × inr 引起的典范态射

 x × y + x × z ~> x × (y + z),

 是一个同构（二元分配律），类似地，典范态射

 0 ~> x × 0

 到零元积中也是同构（零元律，等价于 x × 0 ≅ 0）。这些共同说明函子 x × - 保持有限余积。两个来源都说明了从 x × y + x × z ~> x × (y + z) 的典范映射；由于我们记录的是一个 [Isomorphism] 而不是定向映射，因此下面选择的方向是无关紧要的。零元律通常不从二元分配律推导出来（必须假定），其一个结果是分配范畴的初始对象是严格的。每个双余笛闭范畴都是分配的，因为 x × - 之后有一个右伴随，因此保留所有余极限（参见 [Structure.BiCCC]）。
*)

Section Distributive.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Cocartesian C}.
Context `{@Initial C}.

Class Distributive := {
  (* Binary distributivity: x × - preserves binary coproducts. / 二元分配性：x × - 保持二元余积。 *)
  distr_prod_coprod {x y z} : @Isomorphism C (x × (y + z)) (x × y + x × z);
  (*
 Nullary law: x × - preserves the initial (nullary coproduct) object. 

 --------
 零元律：x × - 保持初始（零元余积）对象。
*)
  distr_zero {x} : x × 0 ≅ 0
}.

End Distributive.
