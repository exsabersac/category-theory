Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.One.
Require Import Category.Instance.StrictCat.

Generalizable All Variables.

(** * 1 is the terminal object of StrictCat *)

(*
   本文件给出终对象实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* [poly_unit] is contractible: any two inhabitants are equal. *)
Lemma poly_unit_eq (u v : poly_unit) : u = v.
Proof. now destruct u, v. Qed.

(*
   本节说明函子、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export]
Program Instance StrictCat_Terminal : @Terminal StrictCat := {
  terminal_obj := _1;        (* the terminal category 1 *)
  one := Erase               (* the unique functor ! : C ⟶ 1 *)
}.
Next Obligation.
  exists (fun c => poly_unit_eq (f c) (g c)).
  intros c c' h; simpl.
  apply poly_unit_eq.
Qed.
