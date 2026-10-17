Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.FinSet.

Require Import Coq.Vectors.Fin.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

(** * Simplex, the simplicial category Δ *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Simplicial_category
 Book:      Mac Lane, "Categories for the Working Mathematician",

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab: https://ncatlab.org/nlab/show/simplex+category
   nLab: https://ncatlab.org/nlab/show/simplicial+set

   本节说明伴随、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition fin_nat {n : nat} (i : Fin.t n) : nat := proj1_sig (Fin.to_nat i).

Definition fin_bound {n : nat} (i : Fin.t n) : Nat.lt (fin_nat i) n :=
  proj2_sig (Fin.to_nat i).

Definition fin_le {n : nat} (i j : Fin.t n) : Prop :=
  Nat.le (fin_nat i) (fin_nat j).

Lemma fin_nat_inj {n : nat} (i j : Fin.t n) : fin_nat i = fin_nat j → i = j.
Proof. apply Fin.to_nat_inj. Qed.

Lemma fin_nat_FS {n : nat} (i : Fin.t n) : fin_nat (Fin.FS i) = S (fin_nat i).
Proof. unfold fin_nat; simpl; now destruct (Fin.to_nat i). Qed.

Lemma fin_nat_F1 {n : nat} : fin_nat (@Fin.F1 n) = 0%nat.
Proof. reflexivity. Qed.

(*
   本节说明 Simplex 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record Monotone (m n : nat) : Type := {
  mono_map :> Fin.t m → Fin.t n;
  mono_ord : ∀ i j : Fin.t m, fin_le i j → fin_le (mono_map i) (mono_map j)
}.

Arguments mono_map {m n} _ _.
Arguments mono_ord {m n} _ {i j} _.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Simplex : Category := {|
  obj := nat;
  hom := Monotone;
  homset := fun m n =>
    {| equiv := fun f g => ∀ i, mono_map f i = mono_map g i |};
  id := fun _ => {| mono_map := fun i => i |};
  compose := fun _ _ _ f g =>
    {| mono_map := fun i => mono_map f (mono_map g i) |}
|}.
Next Obligation.
  (* Pointwise equality of function parts is an equivalence. *)
  constructor.
  - intros f i; reflexivity.
  - intros f g Hfg i; symmetry; apply Hfg.
  - intros f g h Hfg Hgh i; transitivity (mono_map g i);
      [ apply Hfg | apply Hgh ].
Qed.
Next Obligation.
  (* A composite of monotone maps is monotone. *)
  now apply mono_ord, mono_ord.
Qed.
Next Obligation.
  (* Composition respects pointwise equality in both arguments. *)
  intros f f' Hf g g' Hg i; simpl.
  rewrite (Hg i); apply Hf.
Qed.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Simplex_FinSet : Simplex ⟶ FinSet := {|
  fobj := fun n => n;
  fmap := fun m n f => mono_map f
|}.

(* Wide: the inclusion is the identity on objects, so every object of
   FinSet is hit, and hit exactly once. *)
Lemma Simplex_FinSet_wide (n : nat) : Simplex_FinSet n = n.
Proof. reflexivity. Qed.

(* Faithful: the hom-setoid of [Simplex] compares exactly the data the
   inclusion retains, so its hom-maps are injective on the nose. *)
Lemma Simplex_fmap_inj {m n : nat} (f g : @hom Simplex m n) :
  (∀ i, mono_map f i = mono_map g i) → f ≈ g.
Proof. intro H; exact H. Qed.

#[export] Program Instance Simplex_FinSet_Faithful : Faithful Simplex_FinSet.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition fin2_swap (i : Fin.t 2%nat) : Fin.t 2%nat :=
  Fin.caseS' i (fun _ => Fin.t 2%nat) (Fin.FS Fin.F1) (fun _ => Fin.F1).

Example fin2_swap_F1 : fin2_swap Fin.F1 = Fin.FS Fin.F1 := eq_refl.
Example fin2_swap_FS : fin2_swap (Fin.FS Fin.F1) = Fin.F1 := eq_refl.

(* The sharp content, independent of how fullness is packaged: no
   morphism of [Simplex] has the swap as its underlying function.
   Monotonicity applied to 0 ≤ 1 would give swap 0 ≤ swap 1, i.e. 1 ≤ 0. *)
Lemma no_monotone_swap (f : @hom Simplex 2%nat 2%nat) :
  (∀ i, mono_map f i = fin2_swap i) → False.
Proof.
  intro Hf.
  assert (Hle : fin_le (mono_map f Fin.F1) (mono_map f (Fin.FS Fin.F1))).
  { apply mono_ord; unfold fin_le, fin_nat; simpl; lia. }
  rewrite (Hf Fin.F1), (Hf (Fin.FS Fin.F1)) in Hle.
  unfold fin_le, fin_nat in Hle; simpl in Hle; lia.
Qed.

(* Non-fullness follows: a [Full] structure would supply exactly such a
   morphism as the chosen preimage of the swap. *)
Lemma Simplex_FinSet_not_Full : Full Simplex_FinSet → False.
Proof.
  intro H.
  pose (g := fin2_swap
             : @hom FinSet (Simplex_FinSet 2%nat) (Simplex_FinSet 2%nat)).
  exact (no_monotone_swap (@prefmap _ _ _ H 2%nat 2%nat g)
                          (@fmap_sur _ _ _ H 2%nat 2%nat g)).
Qed.

(*
   本节说明 Simplex 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition fin_weak {n : nat} (i : Fin.t n) : Fin.t (S n) :=
  Fin.of_nat_lt (p := fin_nat i) _.
Next Obligation. pose proof (fin_bound i); lia. Qed.

Program Definition fin_skip {n : nat} (i : Fin.t (S n)) (x : Fin.t n) :
  Fin.t (S n) :=
  Fin.of_nat_lt
    (p := if Nat.ltb (fin_nat x) (fin_nat i)
          then fin_nat x else S (fin_nat x)) _.
Next Obligation.
  pose proof (fin_bound x); destruct (Nat.ltb (fin_nat x) (fin_nat i)); lia.
Qed.

Program Definition fin_dup {n : nat} (i : Fin.t n) (x : Fin.t (S n)) :
  Fin.t n :=
  Fin.of_nat_lt
    (p := if Nat.leb (fin_nat x) (fin_nat i)
          then fin_nat x else Nat.pred (fin_nat x)) _.
Next Obligation.
  pose proof (fin_bound i); pose proof (fin_bound x).
  destruct (Nat.leb (fin_nat x) (fin_nat i)) eqn:E.
  - apply Nat.leb_le in E; lia.
  - apply Nat.leb_gt in E; lia.
Qed.

Lemma fin_nat_weak {n : nat} (i : Fin.t n) : fin_nat (fin_weak i) = fin_nat i.
Proof. unfold fin_nat, fin_weak; now rewrite Fin.to_nat_of_nat. Qed.

Lemma fin_nat_skip {n : nat} (i : Fin.t (S n)) (x : Fin.t n) :
  fin_nat (fin_skip i x)
    = if Nat.ltb (fin_nat x) (fin_nat i) then fin_nat x else S (fin_nat x).
Proof. unfold fin_nat, fin_skip; now rewrite Fin.to_nat_of_nat. Qed.

Lemma fin_nat_dup {n : nat} (i : Fin.t n) (x : Fin.t (S n)) :
  fin_nat (fin_dup i x)
    = if Nat.leb (fin_nat x) (fin_nat i)
      then fin_nat x else Nat.pred (fin_nat x).
Proof. unfold fin_nat, fin_dup; now rewrite Fin.to_nat_of_nat. Qed.

(*
   本节说明 Simplex 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Ltac fin_arith :=
  apply fin_nat_inj;
  repeat (rewrite ?fin_nat_skip, ?fin_nat_dup, ?fin_nat_weak, ?fin_nat_FS);
  repeat (match goal with
          | [ |- context[Nat.ltb ?a ?b] ] => destruct (Nat.ltb_spec a b)
          | [ |- context[Nat.leb ?a ?b] ] => destruct (Nat.leb_spec a b)
          end;
          rewrite ?fin_nat_skip, ?fin_nat_dup, ?fin_nat_weak, ?fin_nat_FS);
  lia.

Lemma fin_weak_monotone {n : nat} (x y : Fin.t n) :
  fin_le x y → fin_le (fin_weak x) (fin_weak y).
Proof. unfold fin_le; now rewrite !fin_nat_weak. Qed.

Lemma fin_skip_monotone {n : nat} (i : Fin.t (S n)) (x y : Fin.t n) :
  fin_le x y → fin_le (fin_skip i x) (fin_skip i y).
Proof.
  unfold fin_le; rewrite !fin_nat_skip.
  destruct (Nat.ltb_spec (fin_nat x) (fin_nat i));
    destruct (Nat.ltb_spec (fin_nat y) (fin_nat i)); lia.
Qed.

Lemma fin_dup_monotone {n : nat} (i : Fin.t n) (x y : Fin.t (S n)) :
  fin_le x y → fin_le (fin_dup i x) (fin_dup i y).
Proof.
  unfold fin_le; rewrite !fin_nat_dup.
  destruct (Nat.leb_spec (fin_nat x) (fin_nat i));
    destruct (Nat.leb_spec (fin_nat y) (fin_nat i)); lia.
Qed.

(* The generators as morphisms of [Simplex]. *)

Definition sface {n : nat} (i : Fin.t (S n)) : @hom Simplex n (S n) :=
  {| mono_map := fin_skip i; mono_ord := @fin_skip_monotone n i |}.

Definition sdegen {n : nat} (i : Fin.t n) : @hom Simplex (S n) n :=
  {| mono_map := fin_dup i; mono_ord := @fin_dup_monotone n i |}.

(*
   本节说明 Simplex 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* δ_1 : 2 ~> 3 omits the value 1 — it sends 0 ↦ 0 and 1 ↦ 2. *)
Example sface_skips_at_0 :
  fin_nat (mono_map (@sface 2%nat (Fin.FS Fin.F1)) Fin.F1) = 0%nat := eq_refl.

Example sface_skips_at_1 :
  fin_nat (mono_map (@sface 2%nat (Fin.FS Fin.F1)) (Fin.FS Fin.F1))
    = 2%nat := eq_refl.

(* σ_1 : 3 ~> 2 repeats the value 1 — it sends 0 ↦ 0, 1 ↦ 1 and 2 ↦ 1. *)
Example sdegen_repeats_at_0 :
  fin_nat (mono_map (@sdegen 2%nat (Fin.FS Fin.F1)) Fin.F1) = 0%nat := eq_refl.

Example sdegen_repeats_at_1 :
  fin_nat (mono_map (@sdegen 2%nat (Fin.FS Fin.F1)) (Fin.FS Fin.F1))
    = 1%nat := eq_refl.

Example sdegen_repeats_at_2 :
  fin_nat (mono_map (@sdegen 2%nat (Fin.FS Fin.F1)) (Fin.FS (Fin.FS Fin.F1)))
    = 1%nat := eq_refl.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* (1) δ_i ∘ δ_j = δ_{j+1} ∘ δ_i  for i ≤ j. *)
Theorem simplicial_face_face {n : nat} (i j : Fin.t (S n)) (H : fin_le i j) :
  sface (fin_weak i) ∘ sface j ≈ sface (Fin.FS j) ∘ sface i.
Proof. intro x; simpl; unfold fin_le in H; fin_arith. Qed.

(* (2) σ_j ∘ σ_i = σ_i ∘ σ_{j+1}  for i ≤ j. *)
Theorem simplicial_degen_degen {n : nat} (i j : Fin.t n) (H : fin_le i j) :
  sdegen j ∘ sdegen (fin_weak i) ≈ sdegen i ∘ sdegen (Fin.FS j).
Proof. intro x; simpl; unfold fin_le in H; fin_arith. Qed.

(* (3) σ_{j+1} ∘ δ_i = δ_i ∘ σ_j  for i ≤ j. *)
Theorem simplicial_degen_face_lt {n : nat} (j : Fin.t n) (i : Fin.t (S n))
  (H : Nat.le (fin_nat i) (fin_nat j)) :
  sdegen (Fin.FS j) ∘ sface (fin_weak i) ≈ sface i ∘ sdegen j.
Proof. intro x; simpl; fin_arith. Qed.

(* (4a) σ_j ∘ δ_j = id. *)
Theorem simplicial_degen_face_eq {n : nat} (j : Fin.t n) :
  sdegen j ∘ sface (fin_weak j) ≈ @id Simplex n.
Proof. intro x; simpl; fin_arith. Qed.

(* (4b) σ_j ∘ δ_{j+1} = id. *)
Theorem simplicial_degen_face_succ {n : nat} (j : Fin.t n) :
  sdegen j ∘ sface (Fin.FS j) ≈ @id Simplex n.
Proof. intro x; simpl; fin_arith. Qed.

(* (5) σ_j ∘ δ_{i+1} = δ_i ∘ σ_j  for j < i. *)
Theorem simplicial_degen_face_gt {n : nat} (j : Fin.t n) (i : Fin.t (S n))
  (H : Nat.lt (fin_nat j) (fin_nat i)) :
  sdegen (fin_weak j) ∘ sface (Fin.FS i) ≈ sface i ∘ sdegen j.
Proof. intro x; simpl; fin_arith. Qed.
