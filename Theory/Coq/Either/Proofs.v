Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Functor.Proofs.
Require Import Category.Theory.Coq.Either.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** Law proofs for the Either/sum [a + b] instances *)

(*
 nLab: https://ncatlab.org/nlab/show/coproduct
   Wikipedia: https://en.wikipedia.org/wiki/Coproduct

   本文件给出相应结构的证明。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Either_Functor {E} : IsFunctor (@Either_Functor E) := {|
  a_fmap := @Either_Functor E;
|}.
Next Obligation.
  proper.
  simpl.
  now rewrite H.
Qed.
Next Obligation.
  destruct x0; simpl; congruence.
Qed.
Next Obligation.
  destruct x0; simpl; congruence.
Qed.
