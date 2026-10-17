Require Import Category.Lib.
Require Import Category.Theory.Category.

From Coq Require Import Lists.List.
From Coq Require Import Sorting.Permutation.
Import ListNotations.

Generalizable All Variables.

(** * Symmetric multicategories *)

(* nLab: https://ncatlab.org/nlab/show/multicategory
   Wikipedia: https://en.wikipedia.org/wiki/Multicategory

   多范畴 (multicategory)（又称 colored operad 的多对象形式）有对象与多态射
   f : (x₁,…,xₙ) → y，复合沿多输入「拼接」列表。单位是一元恒等。对称多范畴还带有
   输入置换作用。本文件给出多范畴类、拼接方程套件，以及与 operad / 对称变体的接口。
   长历史短文若仍为英文属后续波次；定义性文首已译。 *)

(*
   关于multicategories的来源与用途

   nLab:  https://ncatlab.org/nlab/show/multicategory
   nLab:  https://ncatlab.org/nlab/show/operad
   Paper: Lambek, "Deductive systems and categories II. Standard
   Book:  Leinster, "Higher Operads, Higher Categories", Cambridge

   本节说明多元范畴、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Multicategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SpliceKit.

Context {A : Type}.

(** Boundary of the left unit law: splicing into [mid] at the unique slot
    ([Γ1 = Γ2 = []]).  [[] ++ (Δ ++ [])] is definitionally [Δ ++ []], so
    this is [app_nil_r] up to conversion. *)
Lemma splice_eq_unit_left (Δ : list A) : [] ++ Δ ++ [] = Δ.
Proof. apply app_nil_r. Qed.

(** Boundary of the right unit law: splicing [mid a] into a slot.
    [[a] ++ Γ2] is definitionally [a :: Γ2], so this is [eq_refl] up to
    conversion; kept as a named lemma for uniformity. *)
Lemma splice_eq_unit_right (Γ1 Γ2 : list A) (a : A) :
  Γ1 ++ [a] ++ Γ2 = Γ1 ++ a :: Γ2.
Proof. reflexivity. Qed.

(** Nested associativity, first cast: the context of [mcomp f g] (slot
    zipper [(Δ1, a, Δ2)] spliced between [Γ1] and [Γ2]) re-expressed as a
    zipper with the slot [a] on top. *)
Lemma splice_eq_nested_slot (Γ1 Δ1 : list A) (a : A) (Δ2 Γ2 : list A) :
  Γ1 ++ (Δ1 ++ a :: Δ2) ++ Γ2 = (Γ1 ++ Δ1) ++ a :: (Δ2 ++ Γ2).
Proof. rewrite app_comm_cons; now rewrite !app_assoc. Qed.

(** Nested associativity, final cast: the two orders of splicing produce
    the same context up to reassociation. *)
Lemma splice_eq_nested (Γ1 Δ1 Θ Δ2 Γ2 : list A) :
  Γ1 ++ (Δ1 ++ Θ ++ Δ2) ++ Γ2 = (Γ1 ++ Δ1) ++ Θ ++ (Δ2 ++ Γ2).
Proof. now rewrite !app_assoc. Qed.

(** Disjoint associativity: pulling a trailing block [w] out of the suffix
    of a three-block context. *)
Lemma splice_eq_out (x y z w : list A) :
  x ++ y ++ (z ++ w) = (x ++ y ++ z) ++ w.
Proof. now rewrite !app_assoc. Qed.

(** Disjoint associativity: pulling a trailing block [w] out of the suffix
    of a slot zipper. *)
Lemma splice_eq_slot_out (x : list A) (a : A) (y w : list A) :
  x ++ a :: (y ++ w) = (x ++ a :: y) ++ w.
Proof. rewrite app_comm_cons; now rewrite !app_assoc. Qed.

(** Inverse orientation of [splice_eq_slot_out]: pushing a trailing block
    back into the suffix of a slot zipper. *)
Lemma splice_eq_slot_in (x : list A) (a : A) (y w : list A) :
  (x ++ a :: y) ++ w = x ++ a :: (y ++ w).
Proof. symmetry; apply splice_eq_slot_out. Qed.

End SpliceKit.

(*
   本节说明 Multicategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Inductive tperm {A : Type} : list A → list A → Type :=
  | tperm_nil : tperm [] []
  | tperm_skip (x : A) {Γ Δ : list A} :
      tperm Γ Δ → tperm (x :: Γ) (x :: Δ)
  | tperm_swap (x y : A) (Γ : list A) :
      tperm (y :: x :: Γ) (x :: y :: Γ)
  | tperm_trans {Γ Δ Λ : list A} :
      tperm Γ Δ → tperm Δ Λ → tperm Γ Λ.

Arguments tperm_nil {A}.

(** The canonical reflexivity witness: a stack of [tperm_skip]s. *)
Fixpoint tperm_refl {A : Type} (Γ : list A) : tperm Γ Γ :=
  match Γ with
  | [] => tperm_nil
  | x :: Γ' => tperm_skip x (tperm_refl Γ')
  end.

(** Soundness: every witness maps to the stdlib proposition. *)
Fixpoint tperm_Permutation {A : Type} {Γ Δ : list A} (p : tperm Γ Δ) :
  Permutation Γ Δ :=
  match p with
  | tperm_nil => perm_nil A
  | tperm_skip x q => perm_skip x (tperm_Permutation q)
  | tperm_swap x y l => perm_swap x y l
  | tperm_trans q r => perm_trans (tperm_Permutation q) (tperm_Permutation r)
  end.

(*
   本节说明 Multicategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** Whiskering a witness by a fixed tail on the right. *)
Fixpoint tperm_app_l {A : Type} {Γ Γ' : list A} (p : tperm Γ Γ')
  (Δ : list A) : tperm (Γ ++ Δ) (Γ' ++ Δ) :=
  match p in tperm Γ0 Γ0' return tperm (Γ0 ++ Δ) (Γ0' ++ Δ) with
  | tperm_nil => tperm_refl Δ
  | tperm_skip x q => tperm_skip x (tperm_app_l q Δ)
  | tperm_swap x y l => tperm_swap x y (l ++ Δ)
  | tperm_trans q r => tperm_trans (tperm_app_l q Δ) (tperm_app_l r Δ)
  end.

(** Whiskering a witness by a fixed prefix on the left. *)
Fixpoint tperm_app_r {A : Type} (Γ : list A) {Δ Δ' : list A}
  (q : tperm Δ Δ') : tperm (Γ ++ Δ) (Γ ++ Δ') :=
  match Γ with
  | [] => q
  | x :: Γ' => tperm_skip x (tperm_app_r Γ' q)
  end.

(** Parallel composition of witnesses across [++]. *)
Definition tperm_app {A : Type} {Γ Γ' Δ Δ' : list A}
  (p : tperm Γ Γ') (q : tperm Δ Δ') : tperm (Γ ++ Δ) (Γ' ++ Δ') :=
  tperm_trans (tperm_app_l p Δ) (tperm_app_r Γ' q).

(** Blockwise permutation of a three-block context [x ++ y ++ z]. *)
Definition perm_block3 {A : Type} {x x' y y' z z' : list A}
  (p : tperm x x') (q : tperm y y') (r : tperm z z') :
  tperm (x ++ y ++ z) (x' ++ y' ++ z') :=
  tperm_app p (tperm_app q r).

(** Blockwise permutation of a slot zipper [x ++ b :: z], fixing the slot. *)
Definition perm_block_slot {A : Type} (b : A) {x x' z z' : list A}
  (p : tperm x x') (r : tperm z z') :
  tperm (x ++ b :: z) (x' ++ b :: z') :=
  tperm_app p (tperm_skip b r).

(** ** The class *)

Class Multicategory : Type := {
  (* Objects (colours). *)
  mobj : Type;

  (* Multimorphisms: a finite list of sources, one target. *)
  mhom : list mobj → mobj → Type;

  mhomset (Γ : list mobj) (c : mobj) : Setoid (mhom Γ c);

  (* Boundary coherence: recast a multimorphism along a propositional
     equality of source lists (Type-level object data, so [=] is
     sanctioned).  A field with groupoid laws, not an [eq_rect]: loop
     collapse over an ARBITRARY proof of [Γ = Γ] would otherwise require
     UIP on [list mobj]. *)
  mcast {Γ Γ' : list mobj} {c : mobj} (e : Γ = Γ') : mhom Γ c → mhom Γ' c;

  mcast_respects {Γ Γ' c} (e : Γ = Γ') :
    Proper (equiv ==> equiv) (@mcast Γ Γ' c e);

  (* Proof-irrelevance of the boundary: casting along any loop is the
     identity. *)
  mcast_id {Γ c} (e : Γ = Γ) (f : mhom Γ c) : mcast e f ≈ f;

  (* Casts compose. *)
  mcast_trans {Γ Γ' Γ'' c} (e : Γ = Γ') (e' : Γ' = Γ'') (f : mhom Γ c) :
    mcast e' (mcast e f) ≈ mcast (eq_trans e e') f;

  (* The identity multimorphism on the singleton context. *)
  mid (a : mobj) : mhom [a] a;

  (* Single-slot ("circle-i") composition, slot addressed by the zipper
     [(Γ1, b, Γ2)]: splice [g] into the [b]-slot of [f]. *)
  mcomp {Γ1 Γ2 Δ : list mobj} {b c : mobj} :
    mhom (Γ1 ++ b :: Γ2) c → mhom Δ b → mhom (Γ1 ++ Δ ++ Γ2) c;

  mcomp_respects {Γ1 Γ2 Δ b c} :
    Proper (equiv ==> equiv ==> equiv) (@mcomp Γ1 Γ2 Δ b c);

  (* Left unit: splicing [g] into the unique slot of [mid b]
     ([Γ1 = Γ2 = []]) gives back [g], up to the cast normalising
     [[] ++ Δ ++ []] to [Δ]. *)
  mcomp_id_left {Δ : list mobj} {b : mobj} (g : mhom Δ b) :
    mcast (splice_eq_unit_left Δ) (mcomp (Γ1:=[]) (Γ2:=[]) (mid b) g) ≈ g;

  (* Right unit: splicing [mid a] into a slot of [f] gives back [f], up to
     the cast normalising [Γ1 ++ [a] ++ Γ2] to [Γ1 ++ a :: Γ2]. *)
  mcomp_id_right {Γ1 Γ2 : list mobj} {a c : mobj}
    (f : mhom (Γ1 ++ a :: Γ2) c) :
    mcast (splice_eq_unit_right Γ1 Γ2 a) (mcomp f (mid a)) ≈ f;

  (*
   本节说明 Multicategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  mcomp_assoc_nested {Γ1 Γ2 Δ1 Δ2 Θ : list mobj} {a b c : mobj}
    (f : mhom (Γ1 ++ b :: Γ2) c) (g : mhom (Δ1 ++ a :: Δ2) b) (h : mhom Θ a)
    (e1 : Γ1 ++ (Δ1 ++ a :: Δ2) ++ Γ2 = (Γ1 ++ Δ1) ++ a :: (Δ2 ++ Γ2))
    (e2 : Γ1 ++ (Δ1 ++ Θ ++ Δ2) ++ Γ2 = (Γ1 ++ Δ1) ++ Θ ++ (Δ2 ++ Γ2)) :
    mcomp (mcast e1 (mcomp f g)) h ≈ mcast e2 (mcomp f (mcomp g h));

  (*
   本节说明 Multicategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  mcomp_assoc_disjoint {Γ1 Γ2 Γ3 Δ Θ : list mobj} {a b c : mobj}
    (f : mhom (Γ1 ++ a :: Γ2 ++ b :: Γ3) c) (g : mhom Δ a) (h : mhom Θ b)
    (d1 : Γ1 ++ Δ ++ Γ2 ++ b :: Γ3 = (Γ1 ++ Δ ++ Γ2) ++ b :: Γ3)
    (d2 : Γ1 ++ a :: Γ2 ++ b :: Γ3 = (Γ1 ++ a :: Γ2) ++ b :: Γ3)
    (d3 : (Γ1 ++ a :: Γ2) ++ Θ ++ Γ3 = Γ1 ++ a :: Γ2 ++ Θ ++ Γ3)
    (d4 : Γ1 ++ Δ ++ Γ2 ++ Θ ++ Γ3 = (Γ1 ++ Δ ++ Γ2) ++ Θ ++ Γ3) :
    mcomp (mcast d1 (mcomp f g)) h
      ≈ mcast d4 (mcomp (mcast d3 (mcomp (mcast d2 f) h)) g);

  (*
   本节说明 Multicategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  msym {Γ Δ : list mobj} {c : mobj} (p : tperm Γ Δ) :
    mhom Γ c → mhom Δ c;

  msym_respects {Γ Δ c} (p : tperm Γ Δ) :
    Proper (equiv ==> equiv) (@msym Γ Δ c p);

  (* The action of the canonical reflexivity witness is trivial.  ONLY
     the [tperm_refl] witness: a nontrivial self-permutation need not act
     trivially, so no loop-quantified variant is stated. *)
  msym_id {Γ c} (f : mhom Γ c) : msym (tperm_refl Γ) f ≈ f;

  (* The action is functorial along the [tperm_trans] constructor. *)
  msym_compose {Γ Δ Λ c} (p : tperm Γ Δ) (q : tperm Δ Λ)
    (f : mhom Γ c) :
    msym q (msym p f) ≈ msym (tperm_trans p q) f;

  (* Equivariance of splicing, block form: permuting the three blocks
     [Γ1], [Δ], [Γ2] independently (slot fixed) commutes with [mcomp].
     Both sides land in [mhom (Γ1' ++ Δ' ++ Γ2') c] on the nose, so no
     cast is needed. *)
  mcomp_equivariant {Γ1 Γ1' Γ2 Γ2' Δ Δ' : list mobj} {b c : mobj}
    (p : tperm Γ1 Γ1') (q : tperm Δ Δ')
    (r : tperm Γ2 Γ2')
    (f : mhom (Γ1 ++ b :: Γ2) c) (g : mhom Δ b) :
    msym (perm_block3 p q r) (mcomp f g)
      ≈ mcomp (msym (perm_block_slot b p r) f) (msym q g)
}.

#[export] Existing Instance mhomset.
#[export] Existing Instance mcast_respects.
#[export] Existing Instance mcomp_respects.
#[export] Existing Instance msym_respects.

(*
   本节说明 Multicategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section MulticategoryLemmas.

Context {M : Multicategory}.

(* Casting there and back again cancels (left orientation). *)
Lemma mcast_symm_l {Γ Γ' : list mobj} {c : mobj} (e : Γ = Γ')
  (f : mhom Γ c) :
  mcast (eq_sym e) (mcast e f) ≈ f.
Proof.
  rewrite mcast_trans; apply mcast_id.
Qed.

(* Casting back and there again cancels (right orientation). *)
Lemma mcast_symm_r {Γ Γ' : list mobj} {c : mobj} (e : Γ = Γ')
  (g : mhom Γ' c) :
  mcast e (mcast (eq_sym e) g) ≈ g.
Proof.
  rewrite mcast_trans; apply mcast_id.
Qed.

(* Reorienting a cast equation: a cast may be moved to the other side of
   [≈] by inverting the equality it rides on. *)
Lemma mcast_flip {Γ Γ' : list mobj} {c : mobj} (e : Γ = Γ')
  (f : mhom Γ c) (g : mhom Γ' c) :
  mcast e f ≈ g ↔ f ≈ mcast (eq_sym e) g.
Proof.
  split; intros H.
  - rewrite <- H.
    symmetry; apply mcast_symm_l.
  - rewrite H.
    apply mcast_symm_r.
Qed.

(* Casting does not depend on the proof cast along: the groupoid laws
   [mcast_id]/[mcast_trans] force any two parallel proofs to cast
   identically — no UIP on [list mobj] involved. *)
Lemma mcast_proof_irrel {Γ Γ' : list mobj} {c : mobj} (e1 e2 : Γ = Γ')
  (f : mhom Γ c) :
  mcast e1 f ≈ mcast e2 f.
Proof.
  apply (snd (mcast_flip e1 f (mcast e2 f))).
  symmetry; rewrite mcast_trans; apply mcast_id.
Qed.

(* [mcast_trans] with the composite proof replaced by any proof of the
   endpoints' equation. *)
Lemma mcast_trans_any {Γ Γ' Γ'' : list mobj} {c : mobj}
  (e1 : Γ = Γ') (e2 : Γ' = Γ'') (e3 : Γ = Γ'') (f : mhom Γ c) :
  mcast e2 (mcast e1 f) ≈ mcast e3 f.
Proof.
  rewrite mcast_trans; apply mcast_proof_irrel.
Qed.

(* The left unit law along any proof of its boundary equation. *)
Lemma mcomp_id_left_any {Δ : list mobj} {b : mobj}
  (e : [] ++ Δ ++ [] = Δ) (g : mhom Δ b) :
  mcast e (mcomp (Γ1:=[]) (Γ2:=[]) (mid b) g) ≈ g.
Proof.
  transitivity
    (mcast (splice_eq_unit_left Δ) (mcomp (Γ1:=[]) (Γ2:=[]) (mid b) g)).
  - apply mcast_proof_irrel.
  - apply mcomp_id_left.
Qed.

(* The right unit law along any proof of its boundary equation. *)
Lemma mcomp_id_right_any {Γ1 Γ2 : list mobj} {a c : mobj}
  (e : Γ1 ++ [a] ++ Γ2 = Γ1 ++ a :: Γ2) (f : mhom (Γ1 ++ a :: Γ2) c) :
  mcast e (mcomp f (mid a)) ≈ f.
Proof.
  transitivity
    (mcast (splice_eq_unit_right Γ1 Γ2 a) (mcomp f (mid a))).
  - apply mcast_proof_irrel.
  - apply mcomp_id_right.
Qed.

(* The right unit law with no cast at all: the boundary equation
   [Γ1 ++ [a] ++ Γ2 = Γ1 ++ a :: Γ2] is definitional, so the two sides
   already inhabit convertible hom-setoids. *)
Lemma mcomp_id_right_plain {Γ1 Γ2 : list mobj} {a c : mobj}
  (f : mhom (Γ1 ++ a :: Γ2) c) :
  mcomp f (mid a) ≈ f.
Proof.
  transitivity
    (mcast (splice_eq_unit_right Γ1 Γ2 a) (mcomp f (mid a))).
  - symmetry; apply mcast_id.
  - apply mcomp_id_right.
Qed.

End MulticategoryLemmas.
