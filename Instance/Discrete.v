Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Discrete.

Generalizable All Variables.

Import EqNotations.

(* * * The discrete 范畴 Type （已译） *)

(*
   本文件给出离散范畴实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Discrete 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition DiscreteCat@{o h p} (A : Type@{o}) : Category@{o h p} := {|
  obj     := A;                       (* objects are elements of A *)
  hom     := fun x y => x = y;        (* morphisms are equality proofs *)
  homset  := fun x y => Morphism_equality@{o h p} x y;  (* strict-eq setoid *)
  id      := fun _ => eq_refl;        (* identity is reflexivity *)
  compose := fun _ _ _ g f => eq_trans f g  (* composition is transitivity *)
|}.
(*
   本节说明 Discrete 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition DiscreteCat_Functor@{o h p uo uh up +}
  {A : Type@{o}} {C : Category@{uo uh up}} (f : A → C) :
  DiscreteCat@{o h p} A ⟶ C := {|
  fobj := f;
  fmap := fun x y (e : x = y) => match e with eq_refl => id end
|}.
(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Discrete 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma DiscreteCat_Discrete@{o h p} (A : Type@{o}) :
  Discrete (DiscreteCat@{o h p} A).
Proof.
  intros x y e.
  exists e.                     (* the equality witness 态射 itself （已译） *)
  now destruct e.               (* [e ≈ rew e in eq_refl] by destructing [e] *)
Qed.
