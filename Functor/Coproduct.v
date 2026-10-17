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

(* Object action: both inl x and inr x are sent to x. [const C] is the (non-
   dependent) motive of [sum_rect]; both branches are the identity on objects. *)
Definition sum_obj : C ∐ C → C :=
  sum_rect (const C) Datatypes.id Datatypes.id.

Section sum_map.

#[local] Set Transparent Obligations.

(* Morphism action: identity on each summand's hom-set (the [_] branches solve
   x ~> y from f : x ~> y in C); the off-diagonal homs are False, so [!] derives
   the goal from the impossible hypothesis. *)
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
