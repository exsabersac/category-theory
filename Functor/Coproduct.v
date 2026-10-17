Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Coproduct.

Generalizable All Variables.

(** The fold (codiagonal) functor [Id, Id] : C ∐ C ⟶ C. *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Coproduct

   本文件给出余积实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Coproduct.

Context {C : Category}.
Context `{@Cocartesian C}.

(* Object action: both inl x inr x sent x. [const C] (non-
 dependent) motive [sum_rect]; both branches 恒等 对象. （已译） *)
Definition sum_obj : C ∐ C → C :=
  sum_rect (const C) Datatypes.id Datatypes.id.

Section sum_map.

#[local] Set Transparent Obligations.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition sum_map (a : C ∐ C) (b : C ∐ C) (f : a ~> b) :
  sum_obj a ~> sum_obj b :=
  match a, b with
  | Datatypes.inl x, Datatypes.inl y => _
  | Datatypes.inl _, Datatypes.inr _ => !
  | Datatypes.inr x, Datatypes.inl _ => !
  | Datatypes.inr x, Datatypes.inr y => _
  end.

End sum_map.

#[export]
Program Instance CoproductFunctor : C ∐ C ⟶ C := {
  fobj := sum_obj;    (* inl x, inr x ↦ x *)
  fmap := sum_map;    (* identity on each summand's morphisms *)
}.
Next Obligation.
  proper; destruct x, y; simpl; tauto.
Qed.
Next Obligation.
  destruct x; simpl; reflexivity.
Qed.
Next Obligation.
  destruct x, y, z; simpl; cat; tauto.
Qed.

End Coproduct.
