Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.FAlg.

Generalizable All Variables.

(** * The category of F-coalgebras *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/F-coalgebra

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition FCoalg `(F : C ⟶ C) : Category := (FAlg (F^op))^op.

(* A co-algebra hom-set of [FCoalg F] is, on the nose, an [F^op]-algebra hom of
   the opposite category. *)
Lemma fcoalg_hom `(F : C ⟶ C) (x y : FCoalg F) :
  (x ~{FCoalg F}~> y) = (y ~{FAlg (F^op)}~> x).
Proof. reflexivity. Qed.

(* The forgetful functor to the underlying category, by dualizing
   [FAlg_Forget] and using [C^op^op = C]. *)
Definition FCoalg_Forget `(F : C ⟶ C) : FCoalg F ⟶ C :=
  (FAlg_Forget (F^op))^op.
