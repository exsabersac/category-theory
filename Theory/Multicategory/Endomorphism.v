Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Theory.Multicategory.

From Coq Require Import Lists.List.
From Coq Require Import Arith.Peano_dec.
Import ListNotations.

Generalizable All Variables.

(** * The endomorphism operad of an object in a cartesian category *)

(*
 nLab: https://ncatlab.org/nlab/show/endomorphism+operad

   本文件给出自同态相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section EndOperad.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context (X : C).

(** ** Finite powers *)

(* The right-nested product fold realising [X^n]. *)
Fixpoint pow (n : nat) : C :=
  match n with
  | O => 1%object
  | S n' => (X × pow n')%object
  end.

(** ** Reindexing casts *)

(* Recast a power along a propositional equality of exponents.  [nat] is
   Type-level object data, so [=] is sanctioned here; morphisms are only
   ever compared by [≈]. *)
Definition pow_cast {m n : nat} (e : m = n) : pow m ~> pow n :=
  match e in _ = y return pow m ~> pow y with
  | eq_refl => id
  end.

(* Casting along any loop is the identity: UIP on [nat] is axiom-free. *)
Lemma pow_cast_refl {n : nat} (e : n = n) : pow_cast e ≈ id.
Proof. now rewrite (UIP_nat _ _ e eq_refl). Qed.

(* Casting does not depend on the proof cast along. *)
Lemma pow_cast_irrel {m n : nat} (e e' : m = n) : pow_cast e ≈ pow_cast e'.
Proof. now rewrite (UIP_nat _ _ e e'). Qed.

(* Casts compose. *)
Lemma pow_cast_fuse {m n p : nat} (e1 : m = n) (e2 : n = p) :
  pow_cast e2 ∘ pow_cast e1 ≈ pow_cast (eq_trans e1 e2).
Proof. destruct e1, e2; simpl; cat. Qed.

(* Tail-carrying form of [pow_cast_fuse], for rewriting inside chains. *)
Lemma pow_cast_fuse' {m n p : nat} (e1 : m = n) (e2 : n = p)
  {w : C} (t : w ~> pow m) :
  pow_cast e2 ∘ (pow_cast e1 ∘ t) ≈ pow_cast (eq_trans e1 e2) ∘ t.
Proof.
  rewrite comp_assoc.
  now rewrite pow_cast_fuse.
Qed.

(* A cast along a successor equality acts on the tail factor only. *)
Lemma pow_cast_S {m n : nat} (e : m = n) (e' : S m = S n) :
  pow_cast e' ≈ second (z:=X) (pow_cast e).
Proof.
  destruct e.
  rewrite pow_cast_refl.
  unfold second; cat.
Qed.

(** ** Block splitting *)

(* The inverse product associator, given by its fork formula.  A named
   constant (rather than [prod_assoc⁻¹]) so that [simpl] leaves it folded
   inside the fixpoints below, keeping goals rewritable. *)
Definition passoc {x y z : C} : x × (y × z) ~> (x × y) × z :=
  (exl △ (exl ∘ exr)) △ (exr ∘ exr).

Lemma passoc_from {x y z : C} :
  passoc ≈ ((prod_assoc (x:=x) (y:=y) (z:=z))⁻¹).
Proof. reflexivity. Qed.

(*
   本节说明 Endomorphism 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fixpoint pow_split (m n : nat) : pow (m + n) ~> pow m × pow n :=
  match m with
  | O => one △ id
  | S m' => passoc ∘ second (pow_split m' n)
  end.

(* Projecting away an empty suffix block is the reindexing cast. *)
Lemma pow_split_r0 (m : nat) (e : (m + 0)%nat = m) :
  exl ∘ pow_split m 0%nat ≈ pow_cast e.
Proof.
  induction m; simpl.
  - apply one_unique.
  - rewrite (pow_cast_S (eq_sym (plus_n_O m)) e).
    rewrite comp_assoc.
    unfold passoc.
    rewrite exl_fork.
    apply ump_products; split.
    + rewrite exl_fork_comp.
      apply exl_second.
    + rewrite exr_fork_comp.
      rewrite <- comp_assoc.
      rewrite (exr_second (pow_split m 0%nat)).
      rewrite comp_assoc.
      now rewrite IHm.
Qed.

(** ** Naturality of the product associator *)

(* The inverse associator is natural in each of its three slots.  All three
   are elementary fork algebra. *)
Lemma assoc_from_first {x x' y z : C} (u : x ~> x') :
  passoc (x:=x') (y:=y) (z:=z) ∘ first u
    ≈ first (first u) ∘ passoc (x:=x) (y:=y) (z:=z).
Proof. unfold passoc; unfork. Qed.

Lemma assoc_from_mid {x y y' z : C} (v : y ~> y') :
  passoc (x:=x) (y:=y') (z:=z) ∘ second (first v)
    ≈ first (second v) ∘ passoc (x:=x) (y:=y) (z:=z).
Proof. unfold passoc; unfork. Qed.

Lemma assoc_from_right {x y z z' : C} (w : z ~> z') :
  passoc (x:=x) (y:=y) (z:=z') ∘ second (second w)
    ≈ second w ∘ passoc (x:=x) (y:=y) (z:=z).
Proof. unfold passoc; unfork. Qed.

(* Tail-carrying forms of the naturality lemmas, for rewriting inside
   right-associated composition chains. *)
Lemma assoc_from_mid' {x y y' z w : C} (v : y ~> y') (t : w ~> x × (y × z)) :
  first (second v) ∘ (passoc ∘ t)
    ≈ passoc ∘ (second (first v) ∘ t).
Proof.
  rewrite !comp_assoc.
  now rewrite <- assoc_from_mid.
Qed.

Lemma assoc_from_right' {x y z z' w : C} (u : z ~> z') (t : w ~> x × (y × z)) :
  passoc ∘ (second (second u) ∘ t)
    ≈ second u ∘ (passoc ∘ t).
Proof.
  rewrite !comp_assoc.
  now rewrite <- assoc_from_right.
Qed.

(* The pentagon for the inverse associator, with a tail. *)
Lemma pentagon_from' {w x y z v : C} (t : v ~> w × (x × (y × z))) :
  first passoc ∘ (passoc ∘ (second passoc ∘ t))
    ≈ passoc ∘ (passoc ∘ t).
Proof.
  rewrite !comp_assoc.
  apply compose_respects; [|reflexivity].
  unfold passoc; unfork.
Qed.

(* Associativity of block splitting: splitting off an [a]-block and then a
   [b]-block agrees with splitting at [a + b] and subdividing, up to the
   product associator and the reindexing cast. *)
Lemma pow_split_assoc (a b c : nat)
  (E : (a + (b + c))%nat = ((a + b) + c)%nat) :
  first (pow_split a b) ∘ pow_split (a + b) c ∘ pow_cast E
    ≈ passoc ∘ second (pow_split b c) ∘ pow_split a (b + c).
Proof.
  revert E; induction a; intros E; simpl.
  - (* The cast is a loop, and both sides are elementary fork algebra. *)
    rewrite pow_cast_refl, id_right.
    unfold passoc; unfork.
    apply fork_respects; [apply fork_respects|]; try reflexivity.
    apply one_unique.
  - rewrite (pow_cast_S (eq_add_S _ _ E) E).
    rewrite first_comp.
    rewrite <- !comp_assoc.
    rewrite assoc_from_mid'.
    rewrite <- !second_comp.
    rewrite (comp_assoc (first (pow_split a b)) (pow_split (a + b) c)).
    rewrite IHa.
    rewrite !second_comp.
    rewrite <- !comp_assoc.
    rewrite pentagon_from'.
    now rewrite assoc_from_right'.
Qed.

(*
   本节说明 Endomorphism 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fixpoint graft (m d k : nat) (g : pow d ~> X) :
  pow (m + (d + k)) ~> pow (m + S k) :=
  match m with
  | O => first g ∘ pow_split d k
  | S m' => second (graft m' d k g)
  end.

#[export] Instance graft_respects (m d k : nat) :
  Proper (equiv ==> equiv) (graft m d k).
Proof.
  intros g g' eg.
  induction m; simpl.
  - now rewrite eg.
  - now rewrite IHm.
Qed.

(* Grafting the unary identity operation is the identity. *)
Lemma graft_id (m k : nat) : graft m 1 k exl ≈ id.
Proof.
  induction m; simpl.
  - unfold passoc; unfork.
  - rewrite IHm.
    now rewrite second_id.
Qed.

(* Two more tail-carrying commutation helpers. *)
Lemma second_first' {x x' y y' w : C} (f : x ~> x') (g : y ~> y')
  (t : w ~> x × y) :
  second g ∘ (first f ∘ t) ≈ first f ∘ (second g ∘ t).
Proof.
  rewrite !comp_assoc.
  now rewrite <- first_second.
Qed.

Lemma assoc_from_first' {x x' y z w : C} (u : x ~> x')
  (t : w ~> x × (y × z)) :
  passoc ∘ (first u ∘ t) ≈ first (first u) ∘ (passoc ∘ t).
Proof.
  rewrite !comp_assoc.
  now rewrite assoc_from_first.
Qed.

(** ** Commuting the graft past block splitting *)

(* Grafting inside the FIRST block commutes with splitting off a trailing
   [n]-block. *)
Lemma split_graft_first (m t k n : nat) (h : pow t ~> X)
  (E1 : (m + S (k + n))%nat = ((m + S k) + n)%nat)
  (E2 : (m + (t + (k + n)))%nat = ((m + (t + k)) + n)%nat) :
  pow_split (m + S k) n ∘ pow_cast E1 ∘ graft m t (k + n) h
    ≈ first (graft m t k h) ∘ pow_split (m + (t + k)) n ∘ pow_cast E2.
Proof.
  revert E1 E2; induction m as [|m IHm]; intros E1 E2; simpl.
  - rewrite first_comp.
    rewrite <- !comp_assoc.
    rewrite pow_cast_refl, id_left.
    rewrite second_first'.
    rewrite assoc_from_first'.
    apply compose_respects; [reflexivity|].
    rewrite !comp_assoc.
    symmetry; apply pow_split_assoc.
  - rewrite (pow_cast_S (eq_add_S _ _ E1) E1).
    rewrite (pow_cast_S (eq_add_S _ _ E2) E2).
    rewrite <- !comp_assoc.
    rewrite assoc_from_mid'.
    rewrite <- !second_comp.
    apply compose_respects; [reflexivity|].
    apply second_respects.
    rewrite !comp_assoc.
    apply IHm.
Qed.

(* Grafting inside the SECOND block commutes with splitting off a leading
   [a]-block. *)
Lemma split_graft_second (a m d k : nat) (h : pow d ~> X)
  (E1 : ((a + m) + S k)%nat = (a + (m + S k))%nat)
  (E2 : ((a + m) + (d + k))%nat = (a + (m + (d + k)))%nat) :
  pow_split a (m + S k) ∘ pow_cast E1 ∘ graft (a + m) d k h
    ≈ second (graft m d k h) ∘ pow_split a (m + (d + k)) ∘ pow_cast E2.
Proof.
  revert E1 E2; induction a as [|a IHa]; intros E1 E2; simpl.
  - rewrite !pow_cast_refl, !id_right.
    rewrite second_fork.
    rewrite <- fork_comp.
    apply fork_respects.
    + apply one_unique.
    + cat.
  - rewrite (pow_cast_S (eq_add_S _ _ E1) E1).
    rewrite (pow_cast_S (eq_add_S _ _ E2) E2).
    rewrite <- !comp_assoc.
    rewrite <- assoc_from_right'.
    rewrite <- !second_comp.
    apply compose_respects; [reflexivity|].
    apply second_respects.
    rewrite !comp_assoc.
    apply IHa.
Qed.

(** ** The two associativity cores *)

(* Nested shape: grafting [h] into the block fed to [g'] agrees with
   grafting [g' ∘ (graft of h)] directly. *)
Lemma graft_nested (m1 m2 k1 k2 t : nat)
  (g' : pow (m2 + S k2) ~> X) (h : pow t ~> X)
  (E1 : ((m1 + m2) + S (k2 + k1))%nat = (m1 + ((m2 + S k2) + k1))%nat)
  (E2 : ((m1 + m2) + (t + (k2 + k1)))%nat
          = (m1 + ((m2 + (t + k2)) + k1))%nat) :
  graft m1 (m2 + S k2) k1 g' ∘ pow_cast E1 ∘ graft (m1 + m2) t (k2 + k1) h
    ≈ graft m1 (m2 + (t + k2)) k1 (g' ∘ graft m2 t k2 h) ∘ pow_cast E2.
Proof.
  revert E1 E2; induction m1 as [|m1 IHm1]; intros E1 E2; simpl.
  - rewrite first_comp.
    rewrite <- !comp_assoc.
    apply compose_respects; [reflexivity|].
    rewrite !comp_assoc.
    apply split_graft_first.
  - rewrite (pow_cast_S (eq_add_S _ _ E1) E1).
    rewrite (pow_cast_S (eq_add_S _ _ E2) E2).
    rewrite <- !comp_assoc.
    rewrite <- !second_comp.
    apply second_respects.
    rewrite !comp_assoc.
    apply IHm1.
Qed.

(* Disjoint shape: two grafts into separate blocks of the same context may
   be performed in either order. *)
Lemma graft_disjoint (m1 m2 m3 dg dh : nat)
  (g : pow dg ~> X) (h : pow dh ~> X)
  (E1 : ((m1 + (dg + m2)) + S m3)%nat = (m1 + (dg + (m2 + S m3)))%nat)
  (E2 : ((m1 + S m2) + S m3)%nat = (m1 + S (m2 + S m3))%nat)
  (E3 : (m1 + S (m2 + (dh + m3)))%nat = ((m1 + S m2) + (dh + m3))%nat)
  (E4 : ((m1 + (dg + m2)) + (dh + m3))%nat
          = (m1 + (dg + (m2 + (dh + m3))))%nat) :
  graft m1 dg (m2 + S m3) g ∘ pow_cast E1 ∘ graft (m1 + (dg + m2)) dh m3 h
    ≈ pow_cast E2 ∘ graft (m1 + S m2) dh m3 h ∘ pow_cast E3
        ∘ graft m1 dg (m2 + (dh + m3)) g ∘ pow_cast E4.
Proof.
  revert E1 E2 E3 E4;
  induction m1 as [|m1 IHm1]; intros E1 E2 E3 E4; simpl.
  - rewrite !pow_cast_refl.
    rewrite id_left, id_right.
    rewrite <- !comp_assoc.
    rewrite second_first'.
    apply compose_respects; [reflexivity|].
    rewrite !comp_assoc.
    apply split_graft_second.
  - rewrite (pow_cast_S (eq_add_S _ _ E1) E1).
    rewrite (pow_cast_S (eq_add_S _ _ E2) E2).
    rewrite (pow_cast_S (eq_add_S _ _ E3) E3).
    rewrite (pow_cast_S (eq_add_S _ _ E4) E4).
    rewrite <- !comp_assoc.
    rewrite <- !second_comp.
    apply second_respects.
    rewrite !comp_assoc.
    apply IHm1.
Qed.

(** ** The operad data *)

(*
   本节说明 Endomorphism 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fixpoint len_app {A : Type} (l1 l2 : list A) :
  length (l1 ++ l2) = (length l1 + length l2)%nat :=
  match l1 with
  | [] => eq_refl
  | _ :: t => f_equal S (len_app t l2)
  end.

Definition len_zip (Γ1 Γ2 : list poly_unit) (b : poly_unit) :
  length (Γ1 ++ b :: Γ2) = (length Γ1 + S (length Γ2))%nat :=
  len_app Γ1 (b :: Γ2).

Definition len_splice (Γ1 Δ Γ2 : list poly_unit) :
  length (Γ1 ++ Δ ++ Γ2)
    = (length Γ1 + (length Δ + length Γ2))%nat :=
  eq_trans (len_app Γ1 (Δ ++ Γ2))
           (f_equal (λ n, (length Γ1 + n)%nat) (len_app Δ Γ2)).

(* Multimorphisms of End(X): the colour set is the one-point type, and an
   operation with source list Γ is a morphism out of the |Γ|-th power. *)
Definition End_hom (Γ : list poly_unit) (_ : poly_unit) : Type :=
  pow (length Γ) ~{C}~> X.

Definition End_mcast {Γ Γ' : list poly_unit} {c : poly_unit} (e : Γ = Γ')
  (f : End_hom Γ c) : End_hom Γ' c :=
  f ∘ pow_cast (f_equal (@length poly_unit) (eq_sym e)).

Definition End_mid (a : poly_unit) : End_hom [a] a := exl.

Definition End_mcomp {Γ1 Γ2 Δ : list poly_unit} {b c : poly_unit}
  (f : End_hom (Γ1 ++ b :: Γ2) c) (g : End_hom Δ b) :
  End_hom (Γ1 ++ Δ ++ Γ2) c :=
  f ∘ pow_cast (eq_sym (len_zip Γ1 Γ2 b))
    ∘ graft (length Γ1) (length Δ) (length Γ2) g
    ∘ pow_cast (len_splice Γ1 Δ Γ2).

(*
   本节说明 Endomorphism 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The braid on the two head factors of a right-nested product:
   (a, (b, w)) ↦ (b, (a, w)). *)
Definition braid {w : C} : X × (X × w) ~> X × (X × w) :=
  (exl ∘ exr) △ (exl △ (exr ∘ exr)).

Fixpoint perm_act {Γ Δ : list poly_unit} (p : tperm Γ Δ) :
  pow (length Δ) ~> pow (length Γ) :=
  match p in tperm Γ0 Δ0
    return pow (length Δ0) ~> pow (length Γ0) with
  | tperm_nil => id
  | tperm_skip x q => second (perm_act q)
  | tperm_swap x y l => braid
  | tperm_trans q r => perm_act q ∘ perm_act r
  end.

Definition End_msym {Γ Δ : list poly_unit} {c : poly_unit}
  (p : tperm Γ Δ) (f : End_hom Γ c) : End_hom Δ c :=
  f ∘ perm_act p.

(** ** The cast pack and respectfulness *)

Lemma End_mcast_respects {Γ Γ' : list poly_unit} {c : poly_unit}
  (e : Γ = Γ') :
  Proper (equiv ==> equiv) (End_mcast (c:=c) e).
Proof.
  intros f g ef; unfold End_mcast.
  now rewrite ef.
Qed.

Lemma End_mcast_id {Γ : list poly_unit} {c : poly_unit} (e : Γ = Γ)
  (f : End_hom Γ c) :
  End_mcast e f ≈ f.
Proof.
  unfold End_mcast.
  now rewrite pow_cast_refl, id_right.
Qed.

Lemma End_mcast_trans {Γ Γ' Γ'' : list poly_unit} {c : poly_unit}
  (e : Γ = Γ') (e' : Γ' = Γ'') (f : End_hom Γ c) :
  End_mcast e' (End_mcast e f) ≈ End_mcast (eq_trans e e') f.
Proof.
  unfold End_mcast.
  rewrite <- comp_assoc.
  rewrite pow_cast_fuse.
  apply compose_respects; [reflexivity|].
  apply pow_cast_irrel.
Qed.

Lemma End_mcomp_respects {Γ1 Γ2 Δ : list poly_unit} {b c : poly_unit} :
  Proper (equiv ==> equiv ==> equiv) (@End_mcomp Γ1 Γ2 Δ b c).
Proof.
  intros f f' ef g g' eg; unfold End_mcomp.
  now rewrite ef, eg.
Qed.

Lemma End_msym_respects {Γ Δ : list poly_unit} {c : poly_unit}
  (p : tperm Γ Δ) :
  Proper (equiv ==> equiv) (End_msym (c:=c) p).
Proof.
  intros f g ef; unfold End_msym.
  now rewrite ef.
Qed.

(** ** The unit laws *)

Lemma End_mcomp_id_left {Δ : list poly_unit} {b : poly_unit}
  (g : End_hom Δ b) :
  End_mcast (splice_eq_unit_left Δ)
    (End_mcomp (Γ1:=[]) (Γ2:=[]) (End_mid b) g) ≈ g.
Proof.
  unfold End_mcast, End_mcomp, End_mid; simpl.
  (* The zipper cast computes away: [len_app [] [b]] reduces to [eq_refl],
     so [pow_cast] of it is literally [id]. *)
  rewrite id_right.
  rewrite <- !comp_assoc.
  rewrite pow_cast_fuse.
  rewrite (comp_assoc exl (first g)).
  rewrite exl_first.
  rewrite <- comp_assoc.
  rewrite (comp_assoc exl (pow_split (length Δ) 0%nat)).
  rewrite (pow_split_r0 (length Δ) (eq_sym (plus_n_O (length Δ)))).
  rewrite pow_cast_fuse.
  now rewrite pow_cast_refl, id_right.
Qed.

Lemma End_mcomp_id_right {Γ1 Γ2 : list poly_unit} {a c : poly_unit}
  (f : End_hom (Γ1 ++ a :: Γ2) c) :
  End_mcast (splice_eq_unit_right Γ1 Γ2 a) (End_mcomp f (End_mid a)) ≈ f.
Proof.
  unfold End_mcast, End_mcomp, End_mid; simpl.
  rewrite graft_id, id_right.
  rewrite <- !comp_assoc.
  rewrite !pow_cast_fuse.
  now rewrite pow_cast_refl, id_right.
Qed.

(** ** The elementary symmetry laws *)

(* The canonical reflexivity witness acts trivially. *)
Lemma perm_act_refl (Γ : list poly_unit) :
  perm_act (tperm_refl Γ) ≈ id.
Proof.
  induction Γ; simpl.
  - reflexivity.
  - rewrite IHΓ.
    apply second_id.
Qed.

Lemma End_msym_id {Γ : list poly_unit} {c : poly_unit} (f : End_hom Γ c) :
  End_msym (tperm_refl Γ) f ≈ f.
Proof.
  unfold End_msym.
  now rewrite perm_act_refl, id_right.
Qed.

Lemma End_msym_compose {Γ Δ Λ : list poly_unit} {c : poly_unit}
  (p : tperm Γ Δ) (q : tperm Δ Λ) (f : End_hom Γ c) :
  End_msym q (End_msym p f) ≈ End_msym (tperm_trans p q) f.
Proof.
  unfold End_msym; simpl.
  now rewrite <- comp_assoc.
Qed.

(*
   本节说明 Endomorphism 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fixpoint plug (m : nat) {s s' : nat} (u : pow s ~> pow s') :
  pow (m + s) ~> pow (m + s') :=
  match m with
  | O => u
  | S m' => second (plug m' u)
  end.

#[export] Instance plug_respects (m s s' : nat) :
  Proper (equiv ==> equiv) (@plug m s s').
Proof.
  intros u v eu.
  induction m; simpl.
  - exact eu.
  - now rewrite IHm.
Qed.

Lemma plug_comp (m : nat) {s s' s'' : nat}
  (u : pow s' ~> pow s'') (v : pow s ~> pow s') :
  plug m (u ∘ v) ≈ plug m u ∘ plug m v.
Proof.
  induction m; simpl.
  - reflexivity.
  - rewrite IHm.
    apply second_comp.
Qed.

(* A cast between powers with a common prefix is a plugged cast. *)
Lemma plug_cast (m : nat) {s s' : nat} (e : s = s')
  (E : (m + s)%nat = (m + s')%nat) :
  pow_cast E ≈ plug m (pow_cast e).
Proof.
  induction m; simpl.
  - apply pow_cast_irrel.
  - rewrite (pow_cast_S (f_equal (λ n, (m + n)%nat) e) E).
    apply second_respects.
    apply IHm.
Qed.

(* The graft is the plugged payload row. *)
Lemma graft_plug (m d k : nat) (g : pow d ~> X) :
  graft m d k g ≈ plug m (s':=S k) (first g ∘ pow_split d k).
Proof.
  induction m; simpl.
  - reflexivity.
  - now rewrite IHm.
Qed.

(* Splitting after a plugged tail map is the tail map on the second
   block. *)
Lemma split_plug (a : nat) {s s' : nat} (v : pow s ~> pow s') :
  pow_split a s' ∘ plug a v ≈ second v ∘ pow_split a s.
Proof.
  induction a; simpl.
  - rewrite second_fork.
    rewrite <- fork_comp.
    apply fork_respects.
    + apply one_unique.
    + cat.
  - rewrite <- comp_assoc.
    rewrite <- second_comp.
    rewrite IHa.
    rewrite second_comp.
    rewrite comp_assoc.
    rewrite assoc_from_right.
    now rewrite <- comp_assoc.
Qed.

(* The braid is natural in the tail. *)
Lemma braid_natural {w w' : C} (v : w ~> w') :
  braid ∘ second (second v) ≈ second (second v) ∘ braid.
Proof. unfold braid; unfork. Qed.

(* Right whiskering acts by plugging under the prefix. *)
Lemma act_app_r_plug (Γ : list poly_unit) {Δ Δ' : list poly_unit}
  (q : tperm Δ Δ')
  (E1 : (length Γ + length Δ)%nat = length (Γ ++ Δ))
  (E2 : length (Γ ++ Δ') = (length Γ + length Δ')%nat) :
  perm_act (tperm_app_r Γ q)
    ≈ pow_cast E1 ∘ plug (length Γ) (perm_act q) ∘ pow_cast E2.
Proof.
  induction Γ; simpl.
  - rewrite !pow_cast_refl; cat.
  - rewrite (pow_cast_S (eq_add_S _ _ E1) E1).
    rewrite (pow_cast_S (eq_add_S _ _ E2) E2).
    rewrite <- !second_comp.
    apply second_respects.
    apply IHΓ.
Qed.

(* Splitting off a tail block commutes with the head braid. *)
Lemma split_braid (n m : nat) :
  pow_split (S (S n)) m ∘ braid (w:=pow (n + m))
    ≈ first (braid (w:=pow n)) ∘ pow_split (S (S n)) m.
Proof.
  simpl; unfold braid, passoc; unfork.
Qed.

(* [split_braid] with a reindexing cast interposed: stated at the nat
   level so that the cast can be destructed away. *)
Lemma split_braid_cast (n m j : nat) (e : j = (n + m)%nat)
  (E E' : S (S j) = (S (S n) + m)%nat) :
  pow_split (S (S n)) m ∘ pow_cast E ∘ braid (w:=pow j)
    ≈ first (braid (w:=pow n)) ∘ pow_split (S (S n)) m ∘ pow_cast E'.
Proof.
  subst j.
  assert (HE : pow_cast E ≈ id) by apply pow_cast_refl.
  assert (HE' : pow_cast E' ≈ id) by apply pow_cast_refl.
  rewrite HE, HE', !id_right.
  apply split_braid.
Qed.

(* Left whiskering: the action of [tperm_app_l p T] is the action of [p]
   on the first block, seen through the block splitting. *)
Lemma act_app_l_split {Γ Γ' : list poly_unit} (p : tperm Γ Γ')
  (T : list poly_unit)
  (E : length (Γ ++ T) = (length Γ + length T)%nat)
  (E' : length (Γ' ++ T) = (length Γ' + length T)%nat) :
  pow_split (length Γ) (length T) ∘ pow_cast E ∘ perm_act (tperm_app_l p T)
    ≈ first (perm_act p) ∘ pow_split (length Γ') (length T) ∘ pow_cast E'.
Proof.
  revert E E'; induction p; intros E E'.
  - (* nil *)
    simpl.
    rewrite perm_act_refl, id_right.
    rewrite first_id, id_left.
    apply compose_respects; [reflexivity|].
    apply pow_cast_irrel.
  - (* skip *)
    simpl.
    rewrite (pow_cast_S (eq_add_S _ _ E) E).
    rewrite (pow_cast_S (eq_add_S _ _ E') E').
    rewrite <- !comp_assoc.
    rewrite assoc_from_mid'.
    rewrite <- !second_comp.
    apply compose_respects; [reflexivity|].
    apply second_respects.
    rewrite !comp_assoc.
    apply IHp.
  - (* swap: the braid case *)
    simpl perm_act.
    change (length (y :: x :: Γ)) with (S (S (length Γ))).
    change (length (x :: y :: Γ)) with (S (S (length Γ))).
    apply (split_braid_cast (length Γ) (length T) (length (Γ ++ T))
             (len_app Γ T) E E').
  - (* trans *)
    simpl.
    rewrite first_comp.
    rewrite comp_assoc.
    rewrite (IHp1 E (len_app Δ T)).
    rewrite <- !comp_assoc.
    apply compose_respects; [reflexivity|].
    rewrite !comp_assoc.
    apply IHp2.
Qed.

(* Braid conjugation with reindexing casts, at the nat level. *)
Lemma braid_plug_cast {s s' j j' : nat} (w : pow s ~> pow s')
  (e : j = s) (e' : j' = s')
  (E1 : S (S j) = S (S s)) (E2 : S (S j') = S (S s'))
  (E3 : S (S s') = S (S j')) (E4 : S (S j) = S (S s)) :
  second (second w) ∘ pow_cast E1 ∘ braid (w:=pow j)
    ≈ pow_cast E2 ∘ braid (w:=pow j') ∘ pow_cast E3
        ∘ second (second w) ∘ pow_cast E4.
Proof.
  subst j j'.
  assert (H1 : pow_cast E1 ≈ id) by apply pow_cast_refl.
  assert (H2 : pow_cast E2 ≈ id) by apply pow_cast_refl.
  assert (H3 : pow_cast E3 ≈ id) by apply pow_cast_refl.
  assert (H4 : pow_cast E4 ≈ id) by apply pow_cast_refl.
  rewrite H1, H2, H3, H4.
  rewrite id_left, !id_right.
  symmetry; apply braid_natural.
Qed.

(* Moving the action of a left whiskering across a plugged tail map. *)
Lemma act_app_l_plug {Γ Γ' : list poly_unit} (p : tperm Γ Γ')
  {T T' : list poly_unit} (u : pow (length T) ~> pow (length T'))
  (E1 : length (Γ ++ T) = (length Γ + length T)%nat)
  (E2 : length (Γ ++ T') = (length Γ + length T')%nat)
  (E3 : (length Γ' + length T')%nat = length (Γ' ++ T'))
  (E4 : length (Γ' ++ T) = (length Γ' + length T)%nat) :
  plug (length Γ) u ∘ pow_cast E1 ∘ perm_act (tperm_app_l p T)
    ≈ pow_cast E2 ∘ perm_act (tperm_app_l p T') ∘ pow_cast E3
        ∘ plug (length Γ') u ∘ pow_cast E4.
Proof.
  revert E1 E2 E3 E4; induction p; intros E1 E2 E3 E4.
  - (* nil *)
    simpl.
    rewrite !perm_act_refl.
    rewrite !pow_cast_refl.
    cat.
  - (* skip *)
    simpl.
    rewrite (pow_cast_S (eq_add_S _ _ E1) E1).
    rewrite (pow_cast_S (eq_add_S _ _ E2) E2).
    rewrite (pow_cast_S (eq_add_S _ _ E3) E3).
    rewrite (pow_cast_S (eq_add_S _ _ E4) E4).
    rewrite <- !second_comp.
    apply second_respects.
    apply IHp.
  - (* swap *)
    simpl perm_act.
    apply (braid_plug_cast (plug (length Γ) u)
             (len_app Γ T) (len_app Γ T') E1 E2 E3 E4).
  - (* trans *)
    simpl.
    rewrite comp_assoc.
    rewrite (IHp1 E1 E2 (eq_sym (len_app Δ T')) (len_app Δ T)).
    rewrite <- !comp_assoc.
    apply compose_respects; [reflexivity|].
    apply compose_respects; [reflexivity|].
    rewrite (comp_assoc (plug (length Δ) u) (pow_cast (len_app Δ T))).
    rewrite (IHp2 (len_app Δ T) (len_app Δ T') E3 E4).
    rewrite <- !comp_assoc.
    rewrite pow_cast_fuse'.
    rewrite pow_cast_refl, id_left.
    reflexivity.
Qed.

(* The payload-level core of the equivariance law: acting on the payload
   block and on the suffix block commutes with the payload row. *)
Lemma equivariant_core {Δ Δ' Γ2 Γ2' : list poly_unit}
  (q : tperm Δ Δ') (r : tperm Γ2 Γ2') (g : pow (length Δ) ~> X) :
  ((first g ∘ pow_split (length Δ) (length Γ2)) ∘ pow_cast (len_app Δ Γ2))
    ∘ (perm_act (tperm_app_l q Γ2) ∘ perm_act (tperm_app_r Δ' r))
    ≈ second (perm_act r)
        ∘ ((first (g ∘ perm_act q) ∘ pow_split (length Δ') (length Γ2'))
             ∘ pow_cast (len_app Δ' Γ2')).
Proof.
  rewrite (act_app_r_plug Δ' r (eq_sym (len_app Δ' Γ2)) (len_app Δ' Γ2')).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (pow_cast (len_app Δ Γ2))).
  rewrite (comp_assoc (pow_split (length Δ) (length Γ2))).
  rewrite (comp_assoc (pow_split (length Δ) (length Γ2))).
  rewrite (act_app_l_split q Γ2 (len_app Δ Γ2) (eq_sym (eq_sym (len_app Δ' Γ2)))).
  rewrite <- !comp_assoc.
  rewrite pow_cast_fuse'.
  rewrite pow_cast_refl, id_left.
  rewrite (comp_assoc (pow_split (length Δ') (length Γ2))).
  rewrite split_plug.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (first g)).
  rewrite <- first_comp.
  rewrite (comp_assoc (first (g ∘ perm_act q))).
  rewrite first_second.
  now rewrite <- !comp_assoc.
Qed.

(* Tail-carrying forms for mid-chain rewriting. *)
Lemma plug_comp' (m : nat) {s s' s'' : nat}
  (u : pow s' ~> pow s'') (v : pow s ~> pow s')
  {w : C} (t : w ~> pow (m + s)) :
  plug m u ∘ (plug m v ∘ t) ≈ plug m (u ∘ v) ∘ t.
Proof.
  rewrite comp_assoc.
  now rewrite <- plug_comp.
Qed.

Corollary act_app_l_plug' {Γ Γ' : list poly_unit} (p : tperm Γ Γ')
  {T T' : list poly_unit} (u : pow (length T) ~> pow (length T'))
  (E1 : length (Γ ++ T) = (length Γ + length T)%nat)
  (E2 : length (Γ ++ T') = (length Γ + length T')%nat)
  (E3 : (length Γ' + length T')%nat = length (Γ' ++ T'))
  (E4 : length (Γ' ++ T) = (length Γ' + length T)%nat)
  {w : C} (t : w ~> pow (length (Γ' ++ T))) :
  plug (length Γ) u ∘ (pow_cast E1 ∘ (perm_act (tperm_app_l p T) ∘ t))
    ≈ pow_cast E2
        ∘ (perm_act (tperm_app_l p T')
             ∘ (pow_cast E3
                  ∘ (plug (length Γ') u ∘ (pow_cast E4 ∘ t)))).
Proof.
  rewrite !comp_assoc.
  apply compose_respects; [|reflexivity].
  apply act_app_l_plug.
Qed.

(** ** Equivariance *)

Lemma End_mcomp_equivariant
  {Γ1 Γ1' Γ2 Γ2' Δ Δ' : list poly_unit} {b c : poly_unit}
  (p : tperm Γ1 Γ1') (q : tperm Δ Δ') (r : tperm Γ2 Γ2')
  (f : End_hom (Γ1 ++ b :: Γ2) c) (g : End_hom Δ b) :
  End_msym (perm_block3 p q r) (End_mcomp f g)
    ≈ End_mcomp (End_msym (perm_block_slot b p r) f) (End_msym q g).
Proof.
  unfold End_msym, End_mcomp, perm_block3, perm_block_slot, tperm_app.
  simpl perm_act.
  rewrite !graft_plug.
  unfold len_splice.
  rewrite <- !pow_cast_fuse.
  rewrite (plug_cast (length Γ1) (len_app Δ Γ2)
             (f_equal (λ n, (length Γ1 + n)%nat) (len_app Δ Γ2))).
  rewrite (plug_cast (length Γ1') (len_app Δ' Γ2')
             (f_equal (λ n, (length Γ1' + n)%nat) (len_app Δ' Γ2'))).
  rewrite (act_app_r_plug Γ1'
             (tperm_trans (tperm_app_l q Γ2) (tperm_app_r Δ' r))
             (eq_sym (len_app Γ1' (Δ ++ Γ2))) (len_app Γ1' (Δ' ++ Γ2'))).
  rewrite (act_app_r_plug Γ1' (tperm_skip b r)
             (eq_sym (len_zip Γ1' Γ2 b)) (len_zip Γ1' Γ2' b)).
  rewrite <- !comp_assoc.
  rewrite !plug_comp'.
  rewrite (act_app_l_plug' p (T':=b :: Γ2)
             ((first g ∘ pow_split (length Δ) (length Γ2))
                ∘ pow_cast (len_app Δ Γ2))
             (len_app Γ1 (Δ ++ Γ2)) (len_zip Γ1 Γ2 b)
             (eq_sym (len_zip Γ1' Γ2 b)) (len_app Γ1' (Δ ++ Γ2))).
  rewrite !pow_cast_fuse'.
  rewrite !pow_cast_refl, !id_left.
  rewrite !plug_comp'.
  apply compose_respects; [reflexivity|].
  apply compose_respects; [reflexivity|].
  apply compose_respects; [apply pow_cast_irrel|].
  apply compose_respects; [|apply pow_cast_irrel].
  apply plug_respects.
  apply equivariant_core.
Qed.

(*
   本节说明 Endomorphism 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma End_mcomp_assoc_nested {Γ1 Γ2 Δ1 Δ2 Θ : list poly_unit}
  {a b c : poly_unit}
  (f : End_hom (Γ1 ++ b :: Γ2) c) (g : End_hom (Δ1 ++ a :: Δ2) b)
  (h : End_hom Θ a)
  (e1 : Γ1 ++ (Δ1 ++ a :: Δ2) ++ Γ2 = (Γ1 ++ Δ1) ++ a :: (Δ2 ++ Γ2))
  (e2 : Γ1 ++ (Δ1 ++ Θ ++ Δ2) ++ Γ2 = (Γ1 ++ Δ1) ++ Θ ++ (Δ2 ++ Γ2)) :
  End_mcomp (End_mcast e1 (End_mcomp f g)) h
    ≈ End_mcast e2 (End_mcomp f (End_mcomp g h)).
Proof.
  unfold End_mcast, End_mcomp.
  unfold End_hom in f, g, h.
  generalize (f_equal (@length poly_unit) (eq_sym e1)).
  generalize (f_equal (@length poly_unit) (eq_sym e2)).
  generalize (eq_sym (len_zip Γ1 Γ2 b)).
  generalize (len_splice Γ1 (Δ1 ++ a :: Δ2) Γ2).
  generalize (eq_sym (len_zip (Γ1 ++ Δ1) (Δ2 ++ Γ2) a)).
  generalize (len_splice (Γ1 ++ Δ1) Θ (Δ2 ++ Γ2)).
  generalize (eq_sym (len_zip Δ1 Δ2 a)).
  generalize (len_splice Δ1 Θ Δ2).
  generalize (len_splice Γ1 (Δ1 ++ Θ ++ Δ2) Γ2).
  intros P9 P7 P6 P5 P4 P2 P1 Pe2 Pe1.
  set (j1 := length (Γ1 ++ b :: Γ2)) in *.
  set (j2 := length (Δ1 ++ a :: Δ2)) in *.
  set (j3 := length (Γ1 ++ (Δ1 ++ a :: Δ2) ++ Γ2)) in *.
  set (j4 := length ((Γ1 ++ Δ1) ++ a :: Δ2 ++ Γ2)) in *.
  set (j5 := length (Γ1 ++ Δ1)) in *.
  set (j6 := length (Δ2 ++ Γ2)) in *.
  set (j8 := length (Δ1 ++ Θ ++ Δ2)) in *.
  set (j9 := length (Γ1 ++ (Δ1 ++ Θ ++ Δ2) ++ Γ2)) in *.
  set (j10 := length ((Γ1 ++ Δ1) ++ Θ ++ Δ2 ++ Γ2)) in *.
  assert (Hj1 : j1 = (length Γ1 + S (length Γ2))%nat)
    by apply (len_zip Γ1 Γ2 b).
  assert (Hj2 : j2 = (length Δ1 + S (length Δ2))%nat)
    by apply (len_zip Δ1 Δ2 a).
  assert (Hj3 : j3 = (length Γ1 + (j2 + length Γ2))%nat)
    by apply (len_splice Γ1 (Δ1 ++ a :: Δ2) Γ2).
  assert (Hj4 : j4 = (j5 + S j6)%nat)
    by apply (len_zip (Γ1 ++ Δ1) (Δ2 ++ Γ2) a).
  assert (Hj5 : j5 = (length Γ1 + length Δ1)%nat)
    by apply (len_app Γ1 Δ1).
  assert (Hj6 : j6 = (length Δ2 + length Γ2)%nat)
    by apply (len_app Δ2 Γ2).
  assert (Hj8 : j8 = (length Δ1 + (length Θ + length Δ2))%nat)
    by apply (len_splice Δ1 Θ Δ2).
  assert (Hj9 : j9 = (length Γ1 + (j8 + length Γ2))%nat)
    by apply (len_splice Γ1 (Δ1 ++ Θ ++ Δ2) Γ2).
  assert (Hj10 : j10 = (j5 + (length Θ + j6))%nat)
    by apply (len_splice (Γ1 ++ Δ1) Θ (Δ2 ++ Γ2)).
  clearbody j1 j2 j3 j4 j5 j6 j8 j9 j10.
  symmetry in Hj1; destruct Hj1.
  symmetry in Hj3; destruct Hj3.
  symmetry in Hj4; destruct Hj4.
  symmetry in Hj9; destruct Hj9.
  symmetry in Hj10; destruct Hj10.
  symmetry in Hj2; destruct Hj2.
  symmetry in Hj5; destruct Hj5.
  symmetry in Hj6; destruct Hj6.
  symmetry in Hj8; destruct Hj8.
  rewrite !pow_cast_refl.
  rewrite !id_right.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  apply graft_nested.
Qed.

Lemma End_mcomp_assoc_disjoint {Γ1 Γ2 Γ3 Δ Θ : list poly_unit}
  {a b c : poly_unit}
  (f : End_hom (Γ1 ++ a :: Γ2 ++ b :: Γ3) c)
  (g : End_hom Δ a) (h : End_hom Θ b)
  (d1 : Γ1 ++ Δ ++ Γ2 ++ b :: Γ3 = (Γ1 ++ Δ ++ Γ2) ++ b :: Γ3)
  (d2 : Γ1 ++ a :: Γ2 ++ b :: Γ3 = (Γ1 ++ a :: Γ2) ++ b :: Γ3)
  (d3 : (Γ1 ++ a :: Γ2) ++ Θ ++ Γ3 = Γ1 ++ a :: Γ2 ++ Θ ++ Γ3)
  (d4 : Γ1 ++ Δ ++ Γ2 ++ Θ ++ Γ3 = (Γ1 ++ Δ ++ Γ2) ++ Θ ++ Γ3) :
  End_mcomp (End_mcast d1 (End_mcomp f g)) h
    ≈ End_mcast d4
        (End_mcomp (End_mcast d3 (End_mcomp (End_mcast d2 f) h)) g).
Proof.
  unfold End_mcast, End_mcomp.
  unfold End_hom in f, g, h.
  generalize (f_equal (@length poly_unit) (eq_sym d1)).
  generalize (f_equal (@length poly_unit) (eq_sym d2)).
  generalize (f_equal (@length poly_unit) (eq_sym d3)).
  generalize (f_equal (@length poly_unit) (eq_sym d4)).
  generalize (eq_sym (len_zip Γ1 (Γ2 ++ b :: Γ3) a)).
  generalize (len_splice Γ1 Δ (Γ2 ++ b :: Γ3)).
  generalize (eq_sym (len_zip (Γ1 ++ Δ ++ Γ2) Γ3 b)).
  generalize (len_splice (Γ1 ++ Δ ++ Γ2) Θ Γ3).
  generalize (eq_sym (len_zip (Γ1 ++ a :: Γ2) Γ3 b)).
  generalize (len_splice (Γ1 ++ a :: Γ2) Θ Γ3).
  generalize (eq_sym (len_zip Γ1 (Γ2 ++ Θ ++ Γ3) a)).
  generalize (len_splice Γ1 Δ (Γ2 ++ Θ ++ Γ3)).
  intros PB4 PA4 PB3 PA3 PB2 PA2 PB1 PA1 PD4 PD3 PD2 PD1.
  set (jA := length (Γ1 ++ a :: Γ2 ++ b :: Γ3)) in *.
  set (kA := length (Γ2 ++ b :: Γ3)) in *.
  set (jB := length (Γ1 ++ Δ ++ Γ2 ++ b :: Γ3)) in *.
  set (jC := length ((Γ1 ++ Δ ++ Γ2) ++ b :: Γ3)) in *.
  set (jD := length (Γ1 ++ Δ ++ Γ2)) in *.
  set (jE := length ((Γ1 ++ Δ ++ Γ2) ++ Θ ++ Γ3)) in *.
  set (jF := length ((Γ1 ++ a :: Γ2) ++ b :: Γ3)) in *.
  set (jG := length (Γ1 ++ a :: Γ2)) in *.
  set (jH := length ((Γ1 ++ a :: Γ2) ++ Θ ++ Γ3)) in *.
  set (jI := length (Γ1 ++ a :: Γ2 ++ Θ ++ Γ3)) in *.
  set (kJ := length (Γ2 ++ Θ ++ Γ3)) in *.
  set (jK := length (Γ1 ++ Δ ++ Γ2 ++ Θ ++ Γ3)) in *.
  assert (HjA : jA = (length Γ1 + S kA)%nat)
    by apply (len_zip Γ1 (Γ2 ++ b :: Γ3) a).
  assert (HkA : kA = (length Γ2 + S (length Γ3))%nat)
    by apply (len_zip Γ2 Γ3 b).
  assert (HjB : jB = (length Γ1 + (length Δ + kA))%nat)
    by apply (len_splice Γ1 Δ (Γ2 ++ b :: Γ3)).
  assert (HjC : jC = (jD + S (length Γ3))%nat)
    by apply (len_zip (Γ1 ++ Δ ++ Γ2) Γ3 b).
  assert (HjD : jD = (length Γ1 + (length Δ + length Γ2))%nat)
    by apply (len_splice Γ1 Δ Γ2).
  assert (HjE : jE = (jD + (length Θ + length Γ3))%nat)
    by apply (len_splice (Γ1 ++ Δ ++ Γ2) Θ Γ3).
  assert (HjF : jF = (jG + S (length Γ3))%nat)
    by apply (len_zip (Γ1 ++ a :: Γ2) Γ3 b).
  assert (HjG : jG = (length Γ1 + S (length Γ2))%nat)
    by apply (len_zip Γ1 Γ2 a).
  assert (HjH : jH = (jG + (length Θ + length Γ3))%nat)
    by apply (len_splice (Γ1 ++ a :: Γ2) Θ Γ3).
  assert (HjI : jI = (length Γ1 + S kJ)%nat)
    by apply (len_zip Γ1 (Γ2 ++ Θ ++ Γ3) a).
  assert (HkJ : kJ = (length Γ2 + (length Θ + length Γ3))%nat)
    by apply (len_splice Γ2 Θ Γ3).
  assert (HjK : jK = (length Γ1 + (length Δ + kJ))%nat)
    by apply (len_splice Γ1 Δ (Γ2 ++ Θ ++ Γ3)).
  clearbody jA kA jB jC jD jE jF jG jH jI kJ jK.
  symmetry in HjA; destruct HjA.
  symmetry in HjB; destruct HjB.
  symmetry in HjC; destruct HjC.
  symmetry in HjE; destruct HjE.
  symmetry in HjF; destruct HjF.
  symmetry in HjH; destruct HjH.
  symmetry in HjI; destruct HjI.
  symmetry in HjK; destruct HjK.
  symmetry in HkA; destruct HkA.
  symmetry in HjD; destruct HjD.
  symmetry in HjG; destruct HjG.
  symmetry in HkJ; destruct HkJ.
  rewrite !pow_cast_refl.
  rewrite !id_right.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  apply graft_disjoint.
Qed.

(** ** The endomorphism operad *)

Definition EndOperad : Multicategory := {|
  mobj := poly_unit;
  mhom := End_hom;
  mhomset := λ Γ _, @homset C (pow (length Γ)) X;
  mcast := @End_mcast;
  mcast_respects := @End_mcast_respects;
  mcast_id := @End_mcast_id;
  mcast_trans := @End_mcast_trans;
  mid := End_mid;
  mcomp := @End_mcomp;
  mcomp_respects := @End_mcomp_respects;
  mcomp_id_left := @End_mcomp_id_left;
  mcomp_id_right := @End_mcomp_id_right;
  mcomp_assoc_nested := @End_mcomp_assoc_nested;
  mcomp_assoc_disjoint := @End_mcomp_assoc_disjoint;
  msym := @End_msym;
  msym_respects := @End_msym_respects;
  msym_id := @End_msym_id;
  msym_compose := @End_msym_compose;
  mcomp_equivariant := @End_mcomp_equivariant
|}.

End EndOperad.
