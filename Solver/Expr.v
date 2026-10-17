Require Import Category.Lib.
Require Import Category.Lib.IList.
Require Import Category.Theory.Category.

(*
   本文件给出 Expr 相关定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* An object of the syntax is just an index into the ambient [objs] list. *)
Definition Obj := nat.

(* Resolve an object index to a concrete object of [C], falling back to the
   default [d] when the index is out of range (so the lookup is total). *)
Definition objD' {C : Category} (d : C) (objs : list C) (n : Obj) :=
  List.nth n objs d.

(* The hom-set type a morphism variable of typing [(dom, cod)] must inhabit;
   used below as the index family [B] of the heterogeneous [arrs]. *)
Definition arrD' {C : Category} (d : C) (objs : list C) '(dom, cod) :=
  objD' d objs dom ~> objD' d objs cod.

(*
   本节说明 Expr 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class Objects (cat : Category) := {
  def_obj : cat;
  objs : list cat;
  objD := objD' def_obj objs;
}.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class Arrows (cat : Category) := {
  has_objects : Objects cat;

  arrD := arrD' def_obj objs;
  tys  : list (Obj * Obj);
  arrs : ilist (B:=arrD) tys;
}.
#[export] Existing Instance has_objects.

(*
   nLab: https://ncatlab.org/nlab/show/free+category

   本节说明 Expr 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive Term : Set :=
  | Ident
  | Morph (a : nat)
  | Comp  (f g : Term).

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive Expr : Set :=
  | Top
  | Bottom
  | And   (p q : Expr)
  | Or    (p q : Expr)
  | Impl  (p q : Expr)
  | Equiv (x y : Obj) (f g : Term).
