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

(* * * The exponential laws at Cat: isomorphisms 函子 范畴 （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/cartesian+closed+category

   本文件给出 Cat 相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CatExponential.

(* * ** The four laws, read isomorphisms 函子 范畴 （已译） *)

(* Currying: a functor out of a product category is a functor into a functor
   category. *)
Example Cat_exp_prod_l (C D E : Cat) :
  @Isomorphism Cat ([C ∏ D, E]) ([C, [D, E]]) :=
  @exp_prod_l Cat _ _ C D E.

(* A functor into a product category is a pair of functors. *)
Example Cat_exp_prod_r (C D E : Cat) :
  @Isomorphism Cat ([C, D ∏ E]) ([C, D] ∏ [C, E]) :=
  @exp_prod_r Cat _ _ C D E.

(* Distributivity of the product of categories over their coproduct. *)
Example Cat_prod_coprod_r (C D E : Cat) :
  @Isomorphism Cat (C ∏ (D ∐ E)) ((C ∏ D) ∐ (C ∏ E)) :=
  @prod_coprod_r Cat _ _ _ C D E.

(* A functor out of a coproduct category is a pair of functors. *)
Example Cat_exp_coprod (C D E : Cat) :
  @Isomorphism Cat ([D ∐ E, C]) ([D, C] ∏ [E, C]) :=
  @exp_coprod Cat _ _ _ C D E.

(*
   本节说明函子、同构、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
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
