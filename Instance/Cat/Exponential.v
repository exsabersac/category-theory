Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.BiCCC.
Require Import Category.Structure.Cartesian.Closed.Natural.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Coproduct.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Cat.Cartesian.
Require Import Category.Instance.Cat.Cartesian.Closed.
Require Import Category.Instance.Cat.Cocartesian.

Generalizable All Variables.

(* * * The exponential laws at Cat: isomorphisms of functor categories / * * Cat 中的指数律：函子范畴的同构 *)

(*
 nLab: https://ncatlab.org/nlab/show/Cat
 nLab: https://ncatlab.org/nlab/show/cartesian+closed+category

 [Cat] is cartesian (Instance/Cat/Cartesian.v, with
 [product_obj := @Product], the product of categories [C ∏ D]), cocartesian
 (Instance/Cat/Cocartesian.v, [product_obj := @Coproduct], read in the
 opposite category, so the coproduct object is [C ∐ D]) and closed
 (Instance/Cat/Cartesian/Closed.v, [exponent_obj := @Fun], so the internal
 hom is the functor category [C, D]).

 Instantiating the four exponential laws there therefore turns them into
 isomorphisms OF FUNCTOR CATEGORIES, and the curried law is the currying of
 [Cat_Closed] internalized: [C ∏ D, E] ≅ [C, [D, E]] says that a functor of
 two variables is a functor into a functor category, which is exactly the
 content of the transposition [exp_iso] that [Cat_Closed] supplies.

 Each of the four statements below is TYPED as an isomorphism between
 explicitly spelled functor categories and INHABITED by the generic
 instance, so the two readings are checked to agree by conversion: nothing
 here is asserted in prose.  The four natural upgrades of
 Structure/Cartesian/Closed/Natural.v are instantiated at [Cat] as well.

 Mac Lane, “Categories for the Working Mathematician”, 2nd ed., §II.5
 Exercise 2 (printed p. 44) is the source of the four laws; this file
 answers work item 3 of jwiegley/category-theory#284, which asks what they
 say at [Cat].  It lives under Instance/ rather than beside the general
 development because Structure/ files must not depend on Instance/. 

 --------
 nLab:  https://ncatlab.org/nlab/show/Cat 
 nLab:  https://ncatlab.org/nlab/show/cartesian+closed+category 

 [Cat] 是笛卡尔的（Instance/Cat/Cartesian.v，带有 [product_obj := @Product]，类别 [C ∏ D] 的积），余笛卡尔的（Instance/Cat/Cocartesian.v，[product_obj := @Coproduct]，在对偶类别中读取，所以余积对象是 [C ∐ D]）且闭合的（Instance/Cat/Cartesian/Closed.v，[exponent_obj := @Fun]，所以内部 Hom 是函子范畴 [C, D]）。

 因此，在此实例化四个指数律，会将它们变为函子范畴的同构，并且柯里化律是 [Cat_Closed] 的柯里化内部化：[C ∏ D, E] ≅ [C, [D, E]，表示一个双变量函子是一个进入函子范畴的函子，这正是 [exp_iso] 通过 [Cat_Closed] 提供的置换内容。下面的四个陈述中，每一个都被标注为在显式拼写的函子范畴之间的同构，并且被泛型实例占有，因此通过转换检查两种读取是否一致：这里没有以散文形式断言的内容。Structure/Cartesian/Closed/Natural.v 的四个自然升级也在 [Cat] 处实例化。

 Mac Lane，《为工作数学家准备的范畴论》，第二版，第 II.5 节，练习 2（印刷页 44）是这四条定律的来源；这个文件回答了 jwiegley/category-theory#284 的工作项 3，该工作项询问它们在 [Cat] 处的含义。它位于 Instance/ 下而不是与一般开发并列，因为 Structure/ 文件不得依赖于 Instance/。
*)

Section CatExponential.

(* * ** The four laws, read as isomorphisms of functor categories / * ** 四条定律，可视为函子范畴的同构 *)

(*
 Currying: a functor out of a product category is a functor into a functor
 category. 

 --------
 柯里化：从积范畴出的函子是一个进入函子范畴的函子。
*)
Example Cat_exp_prod_l (C D E : Cat) :
  @Isomorphism Cat ([C ∏ D, E]) ([C, [D, E]]) :=
  @exp_prod_l Cat _ _ C D E.

(* A functor into a product category is a pair of functors. / 进入积范畴的函子是一对函子。 *)
Example Cat_exp_prod_r (C D E : Cat) :
  @Isomorphism Cat ([C, D ∏ E]) ([C, D] ∏ [C, E]) :=
  @exp_prod_r Cat _ _ C D E.

(* Distributivity of the product of categories over their coproduct. / 范畴的积对它们的余积的分配律。 *)
Example Cat_prod_coprod_r (C D E : Cat) :
  @Isomorphism Cat (C ∏ (D ∐ E)) ((C ∏ D) ∐ (C ∏ E)) :=
  @prod_coprod_r Cat _ _ _ C D E.

(* A functor out of a coproduct category is a pair of functors. / 从余积范畴出的函子是一对函子。 *)
Example Cat_exp_coprod (C D E : Cat) :
  @Isomorphism Cat ([D ∐ E, C]) ([D, C] ∏ [E, C]) :=
  @exp_coprod Cat _ _ _ C D E.

(*
   * ** The same four, upgraded to natural isomorphisms

   These are the isomorphisms of Structure/Cartesian/Closed/Natural.v taken
   at [C := Cat]; each lives in a functor category whose domain is a product
   of copies of [Cat] and [Cat^op]. 

   --------
   * ** 相同的四个，升级为自然同构

   这些是 Structure/Cartesian/Closed/Natural.v 中的同构，
   在 [C := Cat] 中取值；它们每一个都存在于一个函子范畴中，
   其定义域是 [Cat] 和 [Cat^op] 的若干副本的乘积。
*)

Example Cat_exp_prod_l_natural :
  @Isomorphism ([(Cat^op ∏ Cat^op) ∏ Cat, Cat])
    (@ExpProdL_LHS Cat _ _) (@ExpProdL_RHS Cat _ _) :=
  @exp_prod_l_natural Cat _ _.

Example Cat_exp_prod_r_natural :
  @Isomorphism ([Cat^op ∏ (Cat ∏ Cat), Cat])
    (@ExpProdR_LHS Cat _ _) (@ExpProdR_RHS Cat _ _) :=
  @exp_prod_r_natural Cat _ _.

Example Cat_prod_coprod_r_natural :
  @Isomorphism ([Cat ∏ (Cat ∏ Cat), Cat])
    (@ProdCoprodR_LHS Cat _ _) (@ProdCoprodR_RHS Cat _ _) :=
  @prod_coprod_r_natural Cat _ _ _.

Example Cat_exp_coprod_natural :
  @Isomorphism ([(Cat^op ∏ Cat^op) ∏ Cat, Cat])
    (@ExpCoprod_LHS Cat _ _ _) (@ExpCoprod_RHS Cat _ _) :=
  @exp_coprod_natural Cat _ _ _.

End CatExponential.
