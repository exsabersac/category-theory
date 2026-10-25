Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Cartesian.
Require Import Category.Construction.Product.

Generalizable All Variables.

Section ProductCartesian.

Context {C : Category}.
Context {D : Category}.
Context `{@Cartesian C}.
Context `{@Cartesian D}.

(*
 nLab: https://ncatlab.org/nlab/show/product+category
 nLab: https://ncatlab.org/nlab/show/functor+category
 Wikipedia: https://en.wikipedia.org/wiki/Product_category

 Binary products in a product category are computed componentwise. If C and
 D both have binary products, then so does C ∏ D, with the structure taken
 factorwise in each coordinate. On objects x = (c, d) and y = (c', d'),

 (c, d) × (c', d') = (c × c', d × d'),

 and the projections and pairing are pairs of the corresponding maps in C
 and D:

 exl       = (exl, exl)
 exr       = (exr, exr)
 (f, f') △ (g, g') = (f △ g, f' △ g').

 This is the special case, for the discrete two-object diagram shape, of the
 general fact that limits in a functor category [J, D] are computed
 pointwise whenever D has them (Instance/Fun/Limit.v): C ∏ D inherits any limit
 that both factors possess. The universal mapping property [ump_products]
 therefore holds because it holds separately in each coordinate. 

 --------
 nLab:  https://ncatlab.org/nlab/show/product+category 
 nLab:  https://ncatlab.org/nlab/show/functor+category 
 维基百科:  https://en.wikipedia.org/wiki/Product_category 

 一个积范畴中的二元积按分量计算。如果 C 和 D 都有二元积，那么 C ∏ D 也有二元积，其结构在每个坐标中按因子取。对于对象 x = (c, d) 和 y = (c', d')，

 (c, d) × (c', d') = (c × c', d × d')，

 投影和配对是 C 和 D 中对应映射的对：

 exl       = (exl, exl)
 exr       = (exr, exr)
 (f, f') △ (g, g') = (f △ g, f' △ g')。这是一个特殊情况，对于离散的两个对象的图形，是一般事实的特例：当 D 中存在极限时，函子范畴 [J, D] 中的极限可以逐点计算（Instance/Fun/Limit.v）：C ∏ D 继承了两个因子都拥有的任何极限。因此，普遍映射性质 [ump_products] 成立，因为它在每个坐标中分别成立。
*)

Program Instance Product_Cartesian : @Cartesian (C ∏ D) := {
  product_obj := fun x y => (fst x × fst y, snd x × snd y);  (* (c×c', d×d') *)

  fork := fun _ _ _ f g => (fst f △ fst g, snd f △ snd g);   (* pairing, componentwise / 配对，逐组件 *)
  exl  := fun x y => (exl, exl);                             (* left projection, componentwise / 左投影，按分量 *)
  exr  := fun x y => (exr, exr)                              (* right projection, componentwise / 右投影，逐分量 *)
}.
Next Obligation. proper; now rewrites. Qed.
Next Obligation.
  simplify; rewrites; cat;
  rewrite fork_comp; cat.
Qed.

End ProductCartesian.
