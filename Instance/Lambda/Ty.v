Require Import Category.Lib.

From Equations Require Import Equations.
Set Equations With UIP.

Set Transparent Obligations.

(** Simple types for the de Bruijn STLC *)

(*
   本文件给出 λ 演算相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Ty.

Inductive Ty : Set :=
  | TyUnit  : Ty                 (* unit type:    terminal object       *)
  | TyPair  : Ty → Ty → Ty       (* product type: categorical product   *)
  | TyArrow : Ty → Ty → Ty.      (* arrow type:   exponential / hom      *)

Derive NoConfusion NoConfusionHom Subterm EqDec for Ty.

End Ty.

Declare Scope Ty_scope.
Bind Scope Ty_scope with Ty.
Delimit Scope Ty_scope with ty.

Infix "⟶" := TyArrow (at level 51, right associativity) : Ty_scope.
Infix "×"  := TyPair  (at level 41, right associativity) : Ty_scope.
