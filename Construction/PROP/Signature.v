Require Import Category.Lib.

From Coq Require Import Arith.

Generalizable All Variables.

(*
   本文件给出 PROP 相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Signature : Type := nat -> nat -> Type.

(** ** Examples *)

(*
   本节说明 Signature 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Empty_Sig : Signature :=
  fun (_ _ : nat) => Empty_set.

(*
   本节说明 Signature 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Single_Sig (m n : nat) : Signature :=
  fun a b => if Nat.eqb a m
             then if Nat.eqb b n then unit else Empty_set
             else Empty_set.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Sum_Sig (S T : Signature) : Signature :=
  fun m n => sum (S m n) (T m n).

(** Sub-signature: an arity-preserving family of generator
    relabellings into another signature — despite the name, no
    injectivity is required (generator collapses are allowed).
    Inhabited by [inl] / [inr] / nested projection chains. *)
Definition SubSig (Sub Sup : Signature) : Type :=
  forall m n, Sub m n -> Sup m n.

(** The identity sub-signature. *)
Definition SubSig_id (S : Signature) : SubSig S S :=
  fun _ _ s => s.

(** Sub-signature composition. *)
Definition SubSig_compose {S T U : Signature}
  (f : SubSig T U) (g : SubSig S T) : SubSig S U :=
  fun m n s => f m n (g m n s).
