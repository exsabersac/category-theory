From Equations Require Import Equations.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Lib.IList.
Require Import Category.Theory.Category.
Require Import Category.Solver.Expr.

(*
   本文件给出 Denote 相关定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Denote.

Context `{Arrows}.

Open Scope nat_scope.

(*
   本节说明 Denote 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition lookup_arr (f : nat) dom :
  option (∃ cod, objD dom ~> objD cod) :=
  let cod := snd (List.nth f tys (0, 0)) in
  match ith_exact f (dom, cod) arrs with
  | Some f => Some (cod; f)
  | _ => None
  end.

(*
   本节说明 Denote 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fixpoint termD_work dom (e : Term) :
  option (∃ cod, objD dom ~> objD cod) :=
  match e with
  | Ident => Some (dom; id)
  | Morph a => lookup_arr a dom
  | Comp f g =>
    match termD_work dom g with
    | Some (mid; g) =>
      match termD_work mid f with
      | Some (y; f) => Some (y; f ∘ g)
      | _ => None
      end
    | _ => None
    end
  end.

Import EqNotations.

(*
   本节说明 Denote 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition termD dom cod (e : Term) :
  option (objD dom ~> objD cod) :=
  match termD_work dom e with
  | Some (y; f) =>
    match eq_dec y cod with
    | left H => Some (rew [fun y => _ ~> objD y] H in f)
    | _ => None
    end
  | _ => None
  end.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fixpoint exprD (e : Expr) : Type :=
  match e with
  | Top      => True
  | Bottom   => False
  | And p q  => exprD p ∧ exprD q
  | Or p q   => exprD p + exprD q
  | Impl p q => exprD p → exprD q

  | Equiv d c f g =>
    match termD d c f, termD d c g with
    | Some f, Some g => f ≈ g
    | _, _ => False
    end
  end.

End Denote.
