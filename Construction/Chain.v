Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Omega.

Generalizable All Variables.

(** * The initial-algebra chain of an endofunctor *)

(*
 nLab: https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor

   本文件给出链相关构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Chain.

Context {C : Category}.
Context `{@Initial C}.
Context (F : C ⟶ C).

Fixpoint chain_obj (n : nat) : C :=
  match n with
  | O   => initial_obj
  | S k => F (chain_obj k)
  end.

Fixpoint chain_step (n : nat) : chain_obj n ~> chain_obj (S n) :=
  match n with
  | O   => zero
  | S k => fmap[F] (chain_step k)
  end.

(* The action on an order proof [m ≤ n]: iterate [chain_step] along the
   derivation. *)
Fixpoint chain_hom {m n} (p : le_t m n) : chain_obj m ~> chain_obj n :=
  match p with
  | le_t_n    => id
  | le_t_S p' => chain_step _ ∘ chain_hom p'
  end.

(* Functoriality on composites: transporting along a fused order proof is the
   composite of the transports (in the direction fixed by [Omega]'s
   composition [le_t_trans g f]). *)
Lemma chain_hom_trans {m n k} (a : le_t m n) (b : le_t n k) :
  chain_hom (le_t_trans a b) ≈ chain_hom b ∘ chain_hom a.
Proof.
  induction b as [| k' b' IH]; simpl.
  - now rewrite id_left.
  - rewrite IH; now rewrite comp_assoc.
Qed.

Program Definition Chain : Omega ⟶ C := {|
  fobj := chain_obj;
  fmap := fun _ _ p => chain_hom p
|}.
(* fmap_respects: strict-equality hom-setoid; fmap_id: chain_hom of the
   reflexivity proof is [id] definitionally; fmap_comp: chain_hom_trans. *)
Solve All Obligations with
  (simpl; intros; try subst; try reflexivity;
   try (now apply chain_hom_trans); try (now rewrite chain_hom_trans); try cat).

End Chain.

(* The dual chain (a co-chain into the codomain), for the final-coalgebra
   development, by duality through [C^op]. *)
Definition Cochain {C : Category} `{@Terminal C} (F : C ⟶ C) :
  Omega^op ⟶ C := (@Chain (C^op) _ (F^op))^op.
