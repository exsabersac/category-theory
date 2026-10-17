Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** * The ordinal ω as a thin category *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Total_order

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Inductive le_t@{u} (n : nat) : nat → Type@{u} :=
  | le_t_n : le_t n
  | le_t_S {m} : le_t m → le_t (S m).

Arguments le_t_n {n}.
Arguments le_t_S {n m} _.

(* Transitivity, by recursion on the second derivation, so that composition in
   [Omega] reduces on closed inputs (needed by [chain_hom]). *)
Fixpoint le_t_trans@{u} {m n k} (f : le_t@{u} m n) (g : le_t@{u} n k) :
  le_t@{u} m k :=
  match g in le_t _ k' return le_t@{u} m k' with
  | le_t_n     => f
  | le_t_S g'  => le_t_S (le_t_trans f g')
  end.

(* Reflexivity is a strict left unit for [le_t_trans] by the [le_t_n] branch.
   These three unit/associativity lemmas are left with inferred universe
   binders (no explicit [@{u}]): stating an [eq] between [le_t]-terms draws in
   the equality's own universe alongside [le_t]'s, which a single [@{u}] binder
   cannot name on Coq 8.19/8.20 ("unbound universes"); auto-polymorphism binds
   them correctly on every supported version.  The load-bearing annotations are
   the ones inside [Omega] below. *)
Lemma le_t_trans_id_l {m n} (f : le_t m n) :
  le_t_trans f le_t_n = f.
Proof. reflexivity. Qed.

Lemma le_t_trans_id_r {m n} (f : le_t m n) :
  le_t_trans le_t_n f = f.
Proof.
  induction f as [| n' f' IH]; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma le_t_trans_assoc {m n k l}
  (f : le_t m n) (g : le_t n k) (h : le_t k l) :
  le_t_trans (le_t_trans f g) h = le_t_trans f (le_t_trans g h).
Proof.
  induction h as [| l' h' IH]; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

Program Definition Omega@{o h p} : Category@{o h p} := {|
  obj     := nat;
  hom     := le_t@{h};
  homset  := Morphism_equality@{o h p};
  id      := fun _ => le_t_n@{h};
  compose := fun _ _ _ f g => le_t_trans@{h} g f
|}.
Solve All Obligations with
  (simpl; intros; try subst;
   rewrite ?le_t_trans_id_l, ?le_t_trans_id_r, ?le_t_trans_assoc;
   try reflexivity).

(* The generating step morphism [n ~> S n]. *)
Definition omega_step (n : nat) : @hom Omega n (S n) := le_t_S le_t_n.
