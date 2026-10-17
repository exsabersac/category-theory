Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.FinSet.

Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(** * Regular arrows in FinSet, by finite search *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Regular_semigroup
 Wikipedia: https://en.wikipedia.org/wiki/Axiom_of_choice

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** What the classical statement costs, and what is proved instead *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** The finite search *)

(*
   本节说明 Regular 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fixpoint fin_preimage (m n : nat) (f : Fin.t m → Fin.t n) (b : Fin.t n)
         {struct m} : option (Fin.t m) :=
  match m return (Fin.t m → Fin.t n) → option (Fin.t m) with
  | O    => fun _ => None
  | S m' => fun f =>
      match Fin.eq_dec (f Fin.F1) b with
      | left _  => Some Fin.F1
      | right _ =>
          match fin_preimage m' n (fun q => f (Fin.FS q)) b with
          | Some q => Some (Fin.FS q)
          | None   => None
          end
      end
  end f.

Arguments fin_preimage {m n} f b.

(*
   本节说明 Regular 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma fin_preimage_correct {m n : nat} (f : Fin.t m → Fin.t n) (a : Fin.t m) :
  match fin_preimage f (f a) with
  | Some a' => f a' = f a
  | None    => False
  end.
Proof.
  revert f.
  induction a as [m | m a IH]; intros f; simpl.
  - (* head index: the test at [Fin.F1] succeeds outright *)
    destruct (Fin.eq_dec (f Fin.F1) (f Fin.F1)) as [_ | ne].
    + reflexivity.
    + now contradiction ne.
  - (* tail index: either the head already hits the value, or recurse *)
    destruct (Fin.eq_dec (f Fin.F1) (f (Fin.FS a))) as [e | _].
    + exact e.
    + specialize (IH (fun q => f (Fin.FS q))); simpl in IH.
      destruct (fin_preimage (fun q => f (Fin.FS q)) (f (Fin.FS a)));
        exact IH.
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition finset_pseudoinverse {m n : nat} (a0 : Fin.t m)
           (f : Fin.t m → Fin.t n) : Fin.t n → Fin.t m :=
  fun b => match fin_preimage f b with
           | Some a => a
           | None   => a0
           end.

(* ------------------------------------------------------------------------ *)
(** ** Mac Lane §I.5 Exercise 7, second half, over FinSet *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition finset_regular {m n : nat} (a0 : Fin.t m) (f : m ~{FinSet}~> n) :
  RegularMorphism f.
Proof.
  exists (finset_pseudoinverse a0 f).
  intro a; simpl; unfold finset_pseudoinverse.
  pose proof (fin_preimage_correct f a) as H.
  destruct (fin_preimage f (f a)) as [a' |].
  - exact H.
  - contradiction.
Defined.

(* The same statement with inhabitation read off the object: an arrow out of
   a successor object is regular, with [Fin.F1] as the fallback. *)
Definition finset_regular_pos {m n : nat} (f : S m ~{FinSet}~> n) :
  RegularMorphism f := finset_regular Fin.F1 f.

(* ------------------------------------------------------------------------ *)
(** ** The hypothesis is sharp, and every epimorphism splits regardless *)

(*
   本节说明 Regular 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma finset_empty_domain_not_regular {n : nat} (f : 0%nat ~{FinSet}~> S n) :
  RegularMorphism f → False.
Proof. intros [g _]; exact (Fin.case0 (fun _ => False) (g Fin.F1)). Qed.

(*
   本节说明 Regular 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition finset_empty_to_one : 0%nat ~{FinSet}~> 1%nat :=
  fun a => Fin.case0 (fun _ => Fin.t 1) a.

Definition finset_empty_to_one_not_regular :
  RegularMorphism finset_empty_to_one → False :=
  finset_empty_domain_not_regular finset_empty_to_one.

(*
   本节说明 Regular 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma finset_epi_from_empty_absurd {n : nat} (f : 0%nat ~{FinSet}~> n) :
  Epic f → Fin.t n → False.
Proof.
  intros E b.
  destruct n as [| n'].
  - exact (Fin.case0 (fun _ => False) b).
  - pose proof (@epic _ _ _ f E 2%nat (fun _ => Fin.F1)
                  (fun _ => Fin.FS Fin.F1)
                  (fun a => Fin.case0 (fun _ => _) a)) as H.
    discriminate (H Fin.F1).
Qed.

(* So such an epimorphism splits vacuously: its codomain has no element to
   choose a preimage for. *)
Lemma finset_epi_from_empty_splits {n : nat} (f : 0%nat ~{FinSet}~> n) :
  Epic f → Retraction f.
Proof.
  intro E.
  exists (fun b => False_rect (Fin.t 0) (finset_epi_from_empty_absurd f E b)).
  intro b.
  exact (False_rect _ (finset_epi_from_empty_absurd f E b)).
Qed.

(*
   本节说明（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition finset_every_epi_splits {m n : nat} (f : m ~{FinSet}~> n) :
  Epic f → Retraction f :=
  match m return ∀ f : m ~{FinSet}~> n, Epic f → Retraction f with
  | O    => fun f E => finset_epi_from_empty_splits f E
  | S m' => fun f E => regular_epic_retraction f (finset_regular_pos f) E
  end f.

(* ------------------------------------------------------------------------ *)
(** ** Non-vacuity I: regular, but neither a section nor a retraction *)

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition finset_shift3 : 3%nat ~{FinSet}~> 3%nat :=
  fun a =>
    Fin.caseS' a (fun _ => Fin.t 3)
      (Fin.FS (Fin.FS Fin.F1))
      (fun a1 =>
         Fin.caseS' a1 (fun _ => Fin.t 3)
           (Fin.FS (Fin.FS Fin.F1))
           (fun _ => Fin.F1)).

(* Exhaustive case analysis on a three-element index, needed to show that a
   value is missed by every argument. *)
Lemma fin3_cases (a : Fin.t 3) :
  (a = Fin.F1) ∨ (a = Fin.FS Fin.F1) ∨ (a = Fin.FS (Fin.FS Fin.F1)).
Proof.
  apply (Fin.caseS' a
           (fun a => (a = Fin.F1) ∨ (a = Fin.FS Fin.F1)
                       ∨ (a = Fin.FS (Fin.FS Fin.F1)))).
  - now left.
  - intro b.
    apply (Fin.caseS' b
             (fun b => (Fin.FS b = Fin.F1) ∨ (Fin.FS b = Fin.FS Fin.F1)
                         ∨ (Fin.FS b = Fin.FS (Fin.FS Fin.F1)))).
    + right; now left.
    + (* the remaining index lives in [Fin.t 1], a singleton by
         [fin1_unique] (Instance/FinSet.v) *)
      intro c.
      right; right.
      now rewrite (fin1_unique c).
Qed.

(* It is regular: the finite search supplies the pseudoinverse. *)
Definition finset_shift3_regular : RegularMorphism finset_shift3 :=
  finset_regular_pos finset_shift3.

(* It is not injective -- indices 0 and 1 share an image -- so it has no left
   inverse. *)
Lemma finset_shift3_not_section : Section finset_shift3 → False.
Proof.
  intros [s Hs].
  (* s ∘ f ≈ id, evaluated at the two indices sharing an image *)
  pose proof (Hs Fin.F1) as H0.
  pose proof (Hs (Fin.FS Fin.F1)) as H1.
  simpl in H0, H1.
  (* both reduce to a statement about s applied to the SAME value *)
  rewrite H0 in H1.
  discriminate.
Qed.

(* It misses the value 1 entirely, so it has no right inverse. *)
Lemma finset_shift3_not_retraction : Retraction finset_shift3 → False.
Proof.
  intros [r Hr].
  pose proof (Hr (Fin.FS Fin.F1)) as H.
  simpl in H.
  destruct (fin3_cases (r (Fin.FS Fin.F1))) as [E | [E | E]];
    rewrite E in H; discriminate.
Qed.

(* Hence not an isomorphism either: an inverse would in particular be a left
   inverse. *)
Lemma finset_shift3_not_iso : IsIsomorphism finset_shift3 → False.
Proof.
  intros [g _ Hl].
  exact (finset_shift3_not_section (Build_Section _ _ finset_shift3 g Hl)).
Qed.

(* The exercise's point, packaged: regularity is strictly weaker than
   one-sided invertibility, and strictly weaker than invertibility. *)
Definition finset_regular_not_split :
  RegularMorphism finset_shift3
  * (Section finset_shift3 → False)
  * (Retraction finset_shift3 → False)
  * (IsIsomorphism finset_shift3 → False) :=
  (finset_shift3_regular, finset_shift3_not_section,
   finset_shift3_not_retraction, finset_shift3_not_iso).

(* ------------------------------------------------------------------------ *)
(** ** Non-vacuity II: a split pair whose idempotent is not the identity *)

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition finset_point : 1%nat ~{FinSet}~> 2%nat := fun _ => Fin.F1.
Definition finset_bang  : 2%nat ~{FinSet}~> 1%nat := fun _ => Fin.F1.
Definition finset_collapse : 2%nat ~{FinSet}~> 2%nat := fun _ => Fin.F1.

(* One composite is the identity of the 1-element object. *)
Lemma finset_split_pair : finset_bang ∘ finset_point ≈ id.
Proof. intro i; exact (eq_sym (fin1_unique i)). Qed.

(* The other composite is [finset_collapse], on the nose. *)
Lemma finset_point_bang : finset_point ∘ finset_bang ≈ finset_collapse.
Proof. intro i; reflexivity. Qed.

(* So the collapse is idempotent -- by the general lemma, not by hand. *)
Lemma finset_collapse_idempotent : Idempotent finset_collapse.
Proof.
  apply (idempotent_respects (finset_point ∘ finset_bang)).
  - exact finset_point_bang.
  - exact (split_pair_idempotent finset_bang finset_point finset_split_pair).
Qed.

(* And it is NOT the identity: it sends index 1 to index 0.  Without this the
   idempotence above would be witnessed by identities alone. *)
Lemma finset_collapse_not_id : finset_collapse ≈ id → False.
Proof.
  intro H.
  pose proof (H (Fin.FS Fin.F1)) as H1.
  simpl in H1.
  discriminate.
Qed.

(*
   本节说明 Regular 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition finset_split_pair_nontrivial :
  (finset_bang ∘ finset_point ≈ id)
  * (finset_point ∘ finset_bang ≈ finset_collapse)
  * Idempotent finset_collapse
  * (finset_collapse ≈ id → False) :=
  (finset_split_pair, finset_point_bang,
   finset_collapse_idempotent, finset_collapse_not_id).

(* ------------------------------------------------------------------------ *)
(** ** The search runs *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example finset_preimage_late :
  fin_preimage finset_shift3 Fin.F1 = Some (Fin.FS (Fin.FS Fin.F1)) := eq_refl.

Example finset_preimage_miss :
  fin_preimage finset_shift3 (Fin.FS Fin.F1) = None := eq_refl.

Example finset_preimage_first :
  fin_preimage finset_shift3 (Fin.FS (Fin.FS Fin.F1)) = Some Fin.F1 := eq_refl.

(*
   本节说明 Regular 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example finset_pseudoinverse_computes :
  (finset_pseudoinverse Fin.F1 finset_shift3 Fin.F1,
   finset_pseudoinverse Fin.F1 finset_shift3 (Fin.FS Fin.F1),
   finset_pseudoinverse Fin.F1 finset_shift3 (Fin.FS (Fin.FS Fin.F1)))
  = (Fin.FS (Fin.FS Fin.F1), Fin.F1, Fin.F1) := eq_refl.

(* And the witness projected out of the regularity proof is that same
   program, at every index -- the [Defined] on [finset_regular] is what makes
   this hold by [eq_refl]. *)
Example finset_regular_witness_computes :
  (`1 finset_shift3_regular Fin.F1,
   `1 finset_shift3_regular (Fin.FS Fin.F1),
   `1 finset_shift3_regular (Fin.FS (Fin.FS Fin.F1)))
  = (Fin.FS (Fin.FS Fin.F1), Fin.F1, Fin.F1) := eq_refl.

(*
   本节说明 Regular 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma finset_bang_epic : Epic finset_bang.
Proof.
  constructor; intros z g1 g2 H i.
  rewrite (fin1_unique i).
  exact (H Fin.F1).
Qed.

Example finset_epi_split_computes :
  @retract _ _ _ _ (finset_every_epi_splits finset_bang finset_bang_epic) Fin.F1
  = Fin.F1 := eq_refl.
