Require Import Category.Lib.

From Equations Require Import Equations.
Set Equations With UIP.

Set Transparent Obligations.

(** Simple types for the de Bruijn STLC / de Bruijn STLC 的简单类型 *)

(*
 The grammar of simple types used to index the intrinsically-typed syntax
 [Exp Γ τ].  This is a closed type system generated from the unit type, with
 the two type formers of the simply-typed lambda calculus:

 τ ::= unit | τ × τ | τ ⟶ τ

 There are no extra base types: [TyUnit] is the only ground type, and every
 other type is built from it by product and arrow.  This is the internal
 language of a cartesian closed category (Lambek), and the type formers
 correspond exactly to the CCC structure later used to model it (see [Sem]):

 TyUnit      unit type     ↔  terminal object
 TyPair      product type  ↔  categorical product
 TyArrow     arrow type    ↔  exponential / internal hom

 simply typed lambda calculus:
 https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus
 https://ncatlab.org/nlab/show/simply+typed+lambda+calculus
 cartesian closed category (its internal language):
 https://ncatlab.org/nlab/show/cartesian+closed+category 

 --------
 用于索引本质类型语法的简单类型语法 [Exp Γ τ]。这是一个从单元类型生成的封闭类型系统，具有简单类型 lambda 演算的两种类型构造子：

 τ ::= unit | τ × τ | τ ⟶ τ

 没有额外的基本类型：[TyUnit] 是唯一的基本类型，其他所有类型都是通过积和箭头从它构造的。这是一个笛卡尔闭范畴（Lambek）的内部语言，类型构造子完全对应于后来用于建模它的 CCC 结构（见 [Sem]）：

 TyUnit      单元类型     ↔ 终对象
 TyPair      积类型       ↔ 范畴积
 TyArrow     箭头类型     ↔ 指数 / 内部 Hom简单类型 λ 演算：
 https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus 
 https://ncatlab.org/nlab/show/simply+typed+lambda+calculus 
 笛卡尔闭范畴（它的内部语言）：
 https://ncatlab.org/nlab/show/cartesian+closed+category
*)

Section Ty.

Inductive Ty : Set :=
  | TyUnit  : Ty                 (* unit type: terminal object / 单元类型：终端对象 *)
  | TyPair  : Ty → Ty → Ty       (* product type: categorical product / 产品类型：类别产品 *)
  | TyArrow : Ty → Ty → Ty.      (* arrow type: exponential / hom / 箭头类型：指数 / 同类 *)

Derive NoConfusion NoConfusionHom Subterm EqDec for Ty.

End Ty.

Declare Scope Ty_scope.
Bind Scope Ty_scope with Ty.
Delimit Scope Ty_scope with ty.

Infix "⟶" := TyArrow (at level 51, right associativity) : Ty_scope.
Infix "×"  := TyPair  (at level 41, right associativity) : Ty_scope.
