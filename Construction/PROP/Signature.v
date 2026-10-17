Require Import Category.Lib.

From Coq Require Import Arith.

Generalizable All Variables.

(*
   本文件给出 PROP 相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Signature : Type := nat -> nat -> Type.

(** ** Examples *)

(** The empty signature.  Useful as a base case: [FreePROP Empty_Sig]
    is the PROP whose morphisms are exactly the strict-SMC syntactic
    rearrangements (identity, composition, tensor, braid) — the free
    PROP on no generators. *)
Definition Empty_Sig : Signature :=
  fun (_ _ : nat) => Empty_set.

(** The signature of a single generator [g : m -> n] (with [m] inputs
    and [n] outputs), with no other generators.  The generator's arity
    [(m, n)] is arbitrary, not fixed to a binary operation: [Sig a b]
    is [unit] exactly when [(a, b) = (m, n)] and [Empty_set] otherwise.
    Parameterised over the input and output arities
    so the same skeleton can present a Y-junction (2, 1), a fork (1, 2),
    a unit (0, 1), and so on. *)
Definition Single_Sig (m n : nat) : Signature :=
  fun a b => if Nat.eqb a m
             then if Nat.eqb b n then unit else Empty_set
             else Empty_set.

(** ** Operations on signatures

    Sum (disjoint union) of two signatures: a generator is a generator
    of one or the other.  This lets you build complex signatures from
    smaller ones — e.g. the commutative-monoid signature is the sum of
    [Single_Sig 2 1] (multiplication) and [Single_Sig 0 1] (unit). *)
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
