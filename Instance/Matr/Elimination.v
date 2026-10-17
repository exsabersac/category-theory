(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Coq.QArith.QArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Matr.
Require Import Category.Instance.Matr.Determinant.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Field.
Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(*
   本节说明 Elimination 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Elimination 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* [Fin.t 1] is a singleton. *)
Lemma fin1_F1 (j : Fin.t 1) : j = Fin.F1.
Proof.
  pattern j; apply (Fin.caseS' j); clear j.
  - reflexivity.
  - intro y; inversion y.
Qed.

(*
   本节说明 Elimination 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma fin_delete_surj {n : nat} (p j : Fin.t (S n)) :
  j ≠ p → { r : Fin.t n & fin_delete p r = j }.
Proof.
  revert p j; induction n as [|n1 IH]; intros p j.
  - intro Hne; exfalso; apply Hne.
    now rewrite (fin1_F1 j), (fin1_F1 p).
  - pattern p; apply (Fin.caseS' p); clear p.
    + pattern j; apply (Fin.caseS' j); clear j.
      * intro H; exfalso; now apply H.
      * intros y _; exists y; apply fin_delete_F1.
    + intro s.
      pattern j; apply (Fin.caseS' j); clear j.
      * intros _; exists Fin.F1; apply fin_delete_FS_F1.
      * intros y Hy.
        assert (Hys : y ≠ s) by (intro He; apply Hy; now rewrite He).
        destruct (IH s y Hys) as [r Hr].
        exists (Fin.FS r).
        now rewrite fin_delete_FS_FS, Hr.
Qed.

(* 相关说明。 （已译） *)
Lemma fin_pivot_cases {n : nat} (p j : Fin.t (S n)) :
  (j = p) + { r : Fin.t n & fin_delete p r = j }.
Proof.
  destruct (Fin.eq_dec j p) as [He|Hne].
  - left; exact He.
  - right; exact (fin_delete_surj p j Hne).
Qed.

Section Elimination.

(* * ** The base: field zero test

 [Kdec] has type Instance/Field.v's [field_dec_stable] takes; see
 header why no weaker 假设 will do. （已译） *)

Context (K : FieldObject).
Context (Kdec : ∀ a b : carrier (rig_setoid K), (a ≈ b) + (a ≈ b → False)).

Set Default Proof Using "All".

Local Notation Kc := (carrier (rig_setoid K)).

Local Infix "⊕" := (rig_add K) (at level 50, left associativity).
Local Infix "⊗" := (rig_mul K) (at level 40, left associativity).
Local Notation "⊖ x" := (ring_neg K x) (at level 35, right associativity).
Local Notation "0K" := (rig_zero K).
Local Notation "1K" := (rig_one K).

(*
   本节说明 Elimination 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition mat_id (a : nat) : Matrix K a a := fun i j => delta K i j.

Definition mat_zero {a b : nat} : Matrix K a b := fun _ _ => 0K.

Definition mat_mul {a b c : nat} (A : Matrix K a b) (B : Matrix K b c) :
  Matrix K a c :=
  fun i j => fin_sum K (fun l : Fin.t b => A i l ⊗ B l j).

Definition mat_sub {a b : nat} (A B : Matrix K a b) : Matrix K a b :=
  fun i j => A i j ⊕ ⊖ (B i j).

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Instance Matrix_Setoid {a b : nat} : Setoid (Matrix K a b) :=
  @homset (Matr K) b a.

Example matrix_is_hom (a b : nat) : Matrix K a b = (b ~{Matr K}~> a) :=
  eq_refl.

Example mat_mul_is_compose {a b c : nat}
  (A : Matrix K a b) (B : Matrix K b c) :
  mat_mul A B = @compose (Matr K) c b a A B := eq_refl.

Example mat_id_is_id (a : nat) : mat_id a = @id (Matr K) a := eq_refl.

Example mat_equiv_is_homset_equiv {a b : nat} (A B : Matrix K a b) :
  (A ≈ B) = (A ≈[Matr K] B) := eq_refl.

(* * ** Matrix algebra

 Associativity unit laws 范畴's, cited the
 identifications above. Everything else finite-sum computation. （已译） *)

#[local] Instance mat_mul_respects {a b c : nat} :
  Proper (equiv ==> equiv ==> equiv) (@mat_mul a b c) :=
  @compose_respects (Matr K) c b a.

Lemma mat_mul_assoc {a b c d : nat} (A : Matrix K a b) (B : Matrix K b c)
  (C : Matrix K c d) :
  mat_mul (mat_mul A B) C ≈ mat_mul A (mat_mul B C).
Proof. exact (@comp_assoc_sym (Matr K) d c b a A B C). Qed.

Lemma mat_mul_id_l {a b : nat} (A : Matrix K a b) :
  mat_mul (mat_id a) A ≈ A.
Proof. exact (@id_left (Matr K) b a A). Qed.

Lemma mat_mul_id_r {a b : nat} (A : Matrix K a b) :
  mat_mul A (mat_id b) ≈ A.
Proof. exact (@id_right (Matr K) b a A). Qed.

Lemma mat_mul_zero_r {a b c : nat} (A : Matrix K a b) :
  mat_mul A (@mat_zero b c) ≈ mat_zero.
Proof.
  intros i j.
  transitivity (fin_sum K (fun _ : Fin.t b => 0K)).
  - apply fin_sum_respects; intro l; apply rig_mul_zero_r.
  - apply fin_sum_zero.
Qed.

Lemma mat_mul_zero_l {a b c : nat} (B : Matrix K b c) :
  mat_mul (@mat_zero a b) B ≈ mat_zero.
Proof.
  intros i j.
  transitivity (fin_sum K (fun _ : Fin.t b => 0K)).
  - apply fin_sum_respects; intro l; apply rig_mul_zero_l.
  - apply fin_sum_zero.
Qed.

(*
   本节说明 Elimination 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma fin_sum_cons {n : nat} (f : Fin.t (S n) → Kc) :
  fin_sum K f = f Fin.F1 ⊕ fin_sum K (fun i => f (Fin.FS i)).
Proof. reflexivity. Qed.

Lemma fin_sum_delete {n : nat} (f : Fin.t (S n) → Kc) (p : Fin.t (S n)) :
  fin_sum K f ≈ f p ⊕ fin_sum K (fun r => f (fin_delete p r)).
Proof.
  revert f p; induction n as [|n1 IH]; intros f p.
  - rewrite (fin1_F1 p); reflexivity.
  - pattern p; apply (Fin.caseS' p); clear p.
    + rewrite fin_sum_cons.
      apply rig_add_respects; [ reflexivity |].
      apply fin_sum_respects; intro r.
      now rewrite fin_delete_F1.
    + intro s.
      transitivity (f Fin.F1 ⊕ (f (Fin.FS s)
        ⊕ fin_sum K (fun r => f (Fin.FS (fin_delete s r))))).
      { rewrite fin_sum_cons.
        apply rig_add_respects; [ reflexivity |].
        exact (IH (fun i => f (Fin.FS i)) s). }
      transitivity (f (Fin.FS s) ⊕ (f Fin.F1
        ⊕ fin_sum K (fun r => f (Fin.FS (fin_delete s r))))).
      { rewrite <- !rig_add_assoc.
        apply rig_add_respects; [ apply rig_add_comm | reflexivity ]. }
      apply rig_add_respects; [ reflexivity |].
      rewrite fin_sum_cons.
      apply rig_add_respects.
      * now rewrite fin_delete_FS_F1.
      * apply fin_sum_respects; intro y.
        now rewrite fin_delete_FS_FS.
Qed.

(* 相关说明。 （已译） *)
Lemma delta_delete {n : nat} (p : Fin.t (S n)) (r s : Fin.t n) :
  delta K (fin_delete p r) (fin_delete p s) ≈ delta K r s.
Proof.
  destruct (Fin.eq_dec r s) as [He|Hne].
  - rewrite He, !delta_refl; reflexivity.
  - rewrite (delta_neq K r s Hne).
    apply delta_neq.
    intro Heq; apply Hne; exact (fin_delete_inj p r s Heq).
Qed.

(*
   本节说明 Elimination 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition find_nonzero : ∀ (n : nat) (c : Fin.t n → Kc),
  { i : Fin.t n & (c i ≈ 0K → False) } + (∀ i, c i ≈ 0K).
Proof.
  induction n as [|n1 IH]; intro c.
  - right; intro i; inversion i.
  - destruct (Kdec (c Fin.F1) 0K) as [Hz | Hnz].
    + destruct (IH (fun i => c (Fin.FS i))) as [[i Hi] | Hall].
      * left; exists (Fin.FS i); exact Hi.
      * right; intro i.
        pattern i; apply (Fin.caseS' i); [ exact Hz | exact Hall ].
    + left; exists Fin.F1; exact Hnz.
Defined.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition pivot_coeff {m' : nat} (c : Fin.t (S m') → Kc)
  (p : Fin.t (S m')) (r : Fin.t m') : Kc :=
  c (fin_delete p r) ⊗ finv K (c p).

Definition pivot_basis {m' : nat} (c : Fin.t (S m') → Kc)
  (p : Fin.t (S m')) : Matrix K m' (S m') :=
  fun r j => delta K (fin_delete p r) j
             ⊕ ⊖ (pivot_coeff c p r ⊗ delta K p j).

(* 相关说明。 （已译） *)
Lemma fin_sum_pivot_row {m' : nat} (c : Fin.t (S m') → Kc)
  (p : Fin.t (S m')) (r : Fin.t m') (g : Fin.t (S m') → Kc) :
  fin_sum K (fun l => pivot_basis c p r l ⊗ g l)
    ≈ g (fin_delete p r) ⊕ ⊖ (pivot_coeff c p r ⊗ g p).
Proof.
  transitivity (fin_sum K (fun l => delta K (fin_delete p r) l ⊗ g l)
                ⊕ fin_sum K (fun l =>
                    ⊖ ((pivot_coeff c p r ⊗ delta K p l) ⊗ g l))).
  { rewrite <- fin_sum_add.
    apply fin_sum_respects; intro l.
    unfold pivot_basis.
    rewrite rig_distr_r.
    apply rig_add_respects; [ reflexivity |].
    apply ring_neg_mul_l. }
  apply rig_add_respects; [ apply fin_sum_delta_l |].
  assert (HX : fin_sum K (fun l =>
                 (pivot_coeff c p r ⊗ delta K p l) ⊗ g l)
               ≈ pivot_coeff c p r ⊗ g p).
  { transitivity (pivot_coeff c p r
                  ⊗ fin_sum K (fun l => delta K p l ⊗ g l)).
    - rewrite fin_sum_mul_l.
      apply fin_sum_respects; intro l.
      apply rig_mul_assoc.
    - apply rig_mul_respects; [ reflexivity |].
      apply fin_sum_delta_l. }
  rewrite fin_sum_neg, HX.
  reflexivity.
Qed.

(* Every row pivot basis kills column it was built —
 这是 where [finv_l] spent, where [Hp] pays guard. （已译） *)
Lemma pivot_basis_annihilates {m' : nat} (c : Fin.t (S m') → Kc)
  (p : Fin.t (S m')) (Hp : c p ≈ 0K → False) (r : Fin.t m') :
  fin_sum K (fun l => pivot_basis c p r l ⊗ c l) ≈ 0K.
Proof.
  rewrite fin_sum_pivot_row.
  unfold pivot_coeff.
  rewrite rig_mul_assoc.
  rewrite (finv_l K (c p) Hp).
  rewrite rig_mul_one_r.
  apply ring_neg_r.
Qed.

(* 相关说明。 （已译） *)
Lemma pivot_col_pivot {m' : nat} (c : Fin.t (S m') → Kc)
  (p : Fin.t (S m')) (v : Fin.t m' → Kc) :
  fin_sum K (fun r => v r ⊗ pivot_basis c p r p)
    ≈ ⊖ (fin_sum K (fun r => v r ⊗ pivot_coeff c p r)).
Proof.
  rewrite <- fin_sum_neg.
  apply fin_sum_respects; intro r.
  unfold pivot_basis.
  rewrite (delta_neq K (fin_delete p r) p (fin_delete_neq p r)).
  rewrite delta_refl, rig_mul_one_r, rig_add_zero_l.
  apply ring_neg_mul_r.
Qed.

(* Every other column combination basis rows reads off the
 corresponding coefficient — 这是 independence half. （已译） *)
Lemma pivot_col_other {m' : nat} (c : Fin.t (S m') → Kc)
  (p : Fin.t (S m')) (v : Fin.t m' → Kc) (r0 : Fin.t m') :
  fin_sum K (fun r => v r ⊗ pivot_basis c p r (fin_delete p r0)) ≈ v r0.
Proof.
  transitivity (fin_sum K (fun r => v r ⊗ delta K r r0)).
  - apply fin_sum_respects; intro r.
    apply rig_mul_respects; [ reflexivity |].
    unfold pivot_basis.
    rewrite (delta_neq K p (fin_delete p r0)
               (fun H => fin_delete_neq p r0 (eq_sym H))).
    rewrite rig_mul_zero_r, ring_neg_zero, rig_add_zero_r.
    apply delta_delete.
  - apply fin_sum_delta_r.
Qed.

(*
   本节说明 Elimination 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma pivot_mediator_pivot_col {m' z : nat} (c : Fin.t (S m') → Kc)
  (p : Fin.t (S m')) (Hp : c p ≈ 0K → False) (h : Matrix K z (S m'))
  (Hh : ∀ a, fin_sum K (fun l => h a l ⊗ c l) ≈ 0K) (a : Fin.t z) :
  fin_sum K (fun r => h a (fin_delete p r) ⊗ pivot_basis c p r p)
    ≈ h a p.
Proof.
  rewrite pivot_col_pivot.
  assert (Hsum : fin_sum K (fun r =>
                   h a (fin_delete p r) ⊗ pivot_coeff c p r)
                 ≈ ⊖ (h a p ⊗ c p) ⊗ finv K (c p)).
  { transitivity (fin_sum K (fun r =>
        (h a (fin_delete p r) ⊗ c (fin_delete p r)) ⊗ finv K (c p))).
    - apply fin_sum_respects; intro r.
      unfold pivot_coeff.
      symmetry; apply rig_mul_assoc.
    - rewrite <- fin_sum_mul_r.
      apply rig_mul_respects; [| reflexivity ].
      apply (ring_neg_unique K).
      transitivity (fin_sum K (fun l => h a l ⊗ c l)).
      + symmetry; apply (fin_sum_delete (fun l => h a l ⊗ c l) p).
      + apply Hh. }
  rewrite Hsum, ring_neg_mul_l, ring_neg_involutive, rig_mul_assoc.
  rewrite (finv_r K (c p) Hp).
  apply rig_mul_one_r.
Qed.

(*
   本节说明 Elimination 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition mat_col0 {m n : nat} (M : Matrix K m (S n)) : Matrix K m 1 :=
  fun i _ => M i Fin.F1.

Definition mat_tail {m n : nat} (M : Matrix K m (S n)) : Matrix K m n :=
  fun i j => M i (Fin.FS j).

Example mat_mul_col0_strict {z m n : nat} (h : Matrix K z m)
  (M : Matrix K m (S n)) :
  mat_col0 (mat_mul h M) = mat_mul h (mat_col0 M) := eq_refl.

Example mat_mul_tail_strict {z m n : nat} (h : Matrix K z m)
  (M : Matrix K m (S n)) :
  mat_tail (mat_mul h M) = mat_mul h (mat_tail M) := eq_refl.

Lemma mat_mul_col0 {z m n : nat} (h : Matrix K z m)
  (M : Matrix K m (S n)) :
  mat_col0 (mat_mul h M) ≈ mat_mul h (mat_col0 M).
Proof. intros a j; reflexivity. Qed.

Lemma mat_mul_tail {z m n : nat} (h : Matrix K z m)
  (M : Matrix K m (S n)) :
  mat_tail (mat_mul h M) ≈ mat_mul h (mat_tail M).
Proof. intros a j; reflexivity. Qed.

Lemma col0_of_zero {a n : nat} (X : Matrix K a (S n)) :
  X ≈ mat_zero → mat_col0 X ≈ mat_zero.
Proof. intros H i j; exact (H i Fin.F1). Qed.

Lemma tail_of_zero {a n : nat} (X : Matrix K a (S n)) :
  X ≈ mat_zero → mat_tail X ≈ mat_zero.
Proof. intros H i j; exact (H i (Fin.FS j)). Qed.

Lemma zero_of_col0_tail {a n : nat} (X : Matrix K a (S n)) :
  mat_col0 X ≈ mat_zero → mat_tail X ≈ mat_zero → X ≈ mat_zero.
Proof.
  intros H0 H1 i j.
  pattern j; apply (Fin.caseS' j); clear j.
  - exact (H0 i Fin.F1).
  - intro y; exact (H1 i y).
Qed.

Lemma zero_cols {m : nat} (M : Matrix K m 0) : M ≈ mat_zero.
Proof. intros i j; inversion j. Qed.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record LeftNullBasis {m n : nat} (M : Matrix K m n) : Type := {
  lnb_dim : nat;
  lnb_basis : Matrix K lnb_dim m;
  lnb_annih : mat_mul lnb_basis M ≈ mat_zero;
  lnb_univ : ∀ (z : nat) (h : Matrix K z m),
    mat_mul h M ≈ mat_zero →
    ∃! u : Matrix K z lnb_dim, mat_mul u lnb_basis ≈ h
}.

Arguments lnb_dim {m n M} _.
Arguments lnb_basis {m n M} _.
Arguments lnb_annih {m n M} _.
Arguments lnb_univ {m n M} _ _ _ _.

(*
   本节说明 Elimination 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition lnb_id {m n : nat} (M : Matrix K m n) (Hz : M ≈ mat_zero) :
  LeftNullBasis M.
Proof.
  refine {| lnb_dim := m; lnb_basis := mat_id m |}.
  - rewrite mat_mul_id_l; exact Hz.
  - intros z h _.
    refine {| unique_obj := h |}.
    + apply mat_mul_id_r.
    + intros v Hv.
      transitivity (mat_mul v (mat_id m)).
      * symmetry; exact Hv.
      * apply mat_mul_id_r.
Defined.

(*
   本节说明 Elimination 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition col_null_basis :
  ∀ (m : nat) (C : Matrix K m 1), LeftNullBasis C.
Proof.
  intro m; destruct m as [|m']; intro C.
  - apply (lnb_id C).
    intros i j; inversion i.
  - destruct (find_nonzero (S m') (fun i => C i Fin.F1))
      as [[p Hp] | Hall].
    + refine {| lnb_dim := m';
                lnb_basis := pivot_basis (fun i => C i Fin.F1) p |}.
      * intros r j.
        rewrite (fin1_F1 j).
        exact (pivot_basis_annihilates (fun i => C i Fin.F1) p Hp r).
      * intros z h Hh.
        assert (Hcol : ∀ a, fin_sum K
                        (fun l => h a l ⊗ C l Fin.F1) ≈ 0K)
          by (intro a; exact (Hh a Fin.F1)).
        refine {| unique_obj :=
                    fun a r => h a (fin_delete p r) |}.
        -- intros a j.
           destruct (fin_pivot_cases p j) as [He | [r0 Hr0]].
           ++ rewrite He.
              exact (pivot_mediator_pivot_col
                       (fun i => C i Fin.F1) p Hp h Hcol a).
           ++ rewrite <- Hr0.
              exact (pivot_col_other (fun i => C i Fin.F1) p
                       (fun r => h a (fin_delete p r)) r0).
        -- intros v Hv a r.
           symmetry.
           transitivity (fin_sum K (fun s =>
             v a s ⊗ pivot_basis (fun i => C i Fin.F1) p s
                       (fin_delete p r))).
           ++ symmetry; apply pivot_col_other.
           ++ exact (Hv a (fin_delete p r)).
    + apply (lnb_id C).
      intros i j; rewrite (fin1_F1 j); exact (Hall i).
Defined.

(*
   本节说明 Elimination 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition lnb_step {m n : nat} (M : Matrix K m (S n))
  (B1 : LeftNullBasis (mat_col0 M))
  (B2 : LeftNullBasis (mat_mul (lnb_basis B1) (mat_tail M))) :
  LeftNullBasis M.
Proof.
  refine {| lnb_dim := lnb_dim B2;
            lnb_basis := mat_mul (lnb_basis B2) (lnb_basis B1) |}.
  - apply zero_of_col0_tail.
    + rewrite mat_mul_col0, mat_mul_assoc, (lnb_annih B1).
      apply mat_mul_zero_r.
    + rewrite mat_mul_tail, mat_mul_assoc.
      exact (lnb_annih B2).
  - intros z h Hh.
    assert (H0 : mat_mul h (mat_col0 M) ≈ mat_zero).
    { rewrite <- mat_mul_col0.
      apply col0_of_zero; exact Hh. }
    assert (H1 : mat_mul (unique_obj (lnb_univ B1 z h H0))
                   (mat_mul (lnb_basis B1) (mat_tail M)) ≈ mat_zero).
    { rewrite <- mat_mul_assoc.
      rewrite (unique_property (lnb_univ B1 z h H0)).
      rewrite <- mat_mul_tail.
      apply tail_of_zero; exact Hh. }
    refine {| unique_obj := unique_obj (lnb_univ B2 z _ H1) |}.
    + rewrite <- mat_mul_assoc.
      rewrite (unique_property (lnb_univ B2 z _ H1)).
      exact (unique_property (lnb_univ B1 z h H0)).
    + intros v Hv.
      apply (uniqueness (lnb_univ B2 z _ H1)).
      symmetry.
      apply (uniqueness (lnb_univ B1 z h H0)).
      rewrite mat_mul_assoc; exact Hv.
Defined.

(*
   本节说明 Elimination 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fixpoint lnb_rec (n : nat) :
  ∀ (m : nat) (M : Matrix K m n), LeftNullBasis M :=
  match n with
  | O => fun m M => lnb_id M (zero_cols M)
  | S n' => fun m M =>
      let B1 := col_null_basis m (mat_col0 M) in
      lnb_step M B1
        (lnb_rec n' (lnb_dim B1)
           (mat_mul (lnb_basis B1) (mat_tail M)))
  end.

(* 相关说明。 （已译） *)
Definition left_null_basis {m n : nat} (M : Matrix K m n) :
  LeftNullBasis M := lnb_rec n m M.

(*
   本节说明 Elimination 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma mat_mul_sub_r {a b c : nat} (h : Matrix K a b)
  (A B : Matrix K b c) :
  mat_mul h (mat_sub A B) ≈ mat_sub (mat_mul h A) (mat_mul h B).
Proof.
  intros i j.
  transitivity (fin_sum K (fun l =>
                  h i l ⊗ A l j ⊕ ⊖ (h i l ⊗ B l j))).
  - apply fin_sum_respects; intro l.
    unfold mat_sub.
    rewrite rig_distr_l.
    apply rig_add_respects; [ reflexivity |].
    apply ring_neg_mul_r.
  - rewrite fin_sum_add.
    apply rig_add_respects; [ reflexivity |].
    apply fin_sum_neg.
Qed.

Lemma mat_sub_zero {a b : nat} (A B : Matrix K a b) :
  (mat_sub A B ≈ mat_zero) ↔ (A ≈ B).
Proof.
  split.
  - intros H i j.
    assert (Hij : A i j ⊕ ⊖ (B i j) ≈ 0K) by exact (H i j).
    transitivity (A i j ⊕ (⊖ (B i j) ⊕ B i j)).
    + rewrite (ring_neg_l K (B i j)), rig_add_zero_r; reflexivity.
    + rewrite <- rig_add_assoc, Hij, rig_add_zero_l; reflexivity.
  - intros H i j.
    change (A i j ⊕ ⊖ (B i j) ≈ 0K).
    rewrite (H i j).
    apply ring_neg_r.
Qed.

Theorem mat_mul_sub_zero_iff {a b c : nat} (h : Matrix K a b)
  (A B : Matrix K b c) :
  (mat_mul h (mat_sub A B) ≈ mat_zero) ↔ (mat_mul h A ≈ mat_mul h B).
Proof.
  split; intro H.
  - apply (fst (mat_sub_zero (mat_mul h A) (mat_mul h B))).
    rewrite <- mat_mul_sub_r; exact H.
  - rewrite mat_mul_sub_r.
    apply (snd (mat_sub_zero (mat_mul h A) (mat_mul h B))); exact H.
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem left_null_basis_diff {m n : nat} (A B : Matrix K m n) :
  { k : nat & { E : Matrix K k m &
      (mat_mul E A ≈ mat_mul E B) ∧
      (∀ (z : nat) (h : Matrix K z m), mat_mul h A ≈ mat_mul h B →
        ∃! u : Matrix K z k, mat_mul u E ≈ h) } }.
Proof.
  pose (Bs := left_null_basis (mat_sub A B)).
  exists (lnb_dim Bs), (lnb_basis Bs).
  split.
  - apply (fst (mat_mul_sub_zero_iff (lnb_basis Bs) A B)).
    exact (lnb_annih Bs).
  - intros z h Hh.
    apply (lnb_univ Bs z h).
    apply (snd (mat_mul_sub_zero_iff h A B)); exact Hh.
Qed.

End Elimination.

(*
   本节说明 Elimination 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Arguments LeftNullBasis K {m n} _.
Arguments lnb_dim {K m n M} _.
Arguments lnb_basis {K m n M} _.
Arguments lnb_annih {K m n M} _.
Arguments lnb_univ {K m n M} _ _ _ _.

(*
   本节说明 Elimination 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition F2_dec_inhabits :
  ∀ a b : carrier (rig_setoid F2_Field), (a ≈ b) + (a ≈ b → False) :=
  F2_Field_dec.

Definition Q_dec_inhabits :
  ∀ a b : carrier (rig_setoid Q_Field), (a ≈ b) + (a ≈ b → False) :=
  Q_Field_dec.

Definition f2_dec (a b : carrier (rig_setoid F2_Field)) :
  (a ≈ b) + (a ≈ b → False).
Proof.
  destruct a, b; solve [ left; reflexivity | right; discriminate ].
Defined.

Definition q_dec (a b : carrier (rig_setoid Q_Field)) :
  (a ≈ b) + (a ≈ b → False).
Proof.
  destruct (Qeq_dec a b) as [H | H]; [ left | right ]; exact H.
Defined.

(*
   本节说明 Elimination 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)
Definition f2_col : Matrix F2_Field 2 1 := fun _ _ => true.

Definition f2_col_lnb : LeftNullBasis F2_Field f2_col :=
  left_null_basis F2_Field f2_dec f2_col.

Example f2_col_dim : lnb_dim f2_col_lnb = 1%nat := eq_refl.

Example f2_col_basis_0 :
  lnb_basis f2_col_lnb Fin.F1 Fin.F1 = true := eq_refl.

Example f2_col_basis_1 :
  lnb_basis f2_col_lnb Fin.F1 (Fin.FS Fin.F1) = true := eq_refl.

(* The annihilation, COMPUTED rather than cited: 1·1 + 1·1 = 0 in F₂. *)
Example f2_col_annih_computes :
  mat_mul F2_Field (lnb_basis f2_col_lnb) f2_col Fin.F1 Fin.F1 = false :=
  eq_refl.

(*
   本节说明 Elimination 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition f2_h : Matrix F2_Field 1 2 := fun _ _ => true.

Lemma f2_h_kills : mat_mul F2_Field f2_h f2_col ≈ mat_zero F2_Field.
Proof. intros i j; reflexivity. Qed.

(* 相关说明。 （已译） *)
Definition f2_mediator := lnb_univ f2_col_lnb 1 f2_h f2_h_kills.

Example f2_mediator_computes :
  unique_obj f2_mediator Fin.F1 Fin.F1 = true := eq_refl.

(* The dimension responds matrix, what makes search
 pivot load-bearing: 2 × 2 恒等 has NO nonzero row
 vector left null space... （已译） *)
Definition f2_id2 : Matrix F2_Field 2 2 :=
  fun i j => delta F2_Field i j.

Example f2_id2_dim :
  lnb_dim (left_null_basis F2_Field f2_dec f2_id2) = 0%nat :=
  eq_refl.

(* ...while the all-ones 2 × 2 matrix, whose two columns coincide, has a
   one-dimensional one, spanned again by (1, 1). *)
Definition f2_ones : Matrix F2_Field 2 2 := fun _ _ => true.

Definition f2_ones_lnb : LeftNullBasis F2_Field f2_ones :=
  left_null_basis F2_Field f2_dec f2_ones.

Example f2_ones_dim : lnb_dim f2_ones_lnb = 1%nat := eq_refl.

Example f2_ones_basis_0 :
  lnb_basis f2_ones_lnb Fin.F1 Fin.F1 = true := eq_refl.

Example f2_ones_basis_1 :
  lnb_basis f2_ones_lnb Fin.F1 (Fin.FS Fin.F1) = true := eq_refl.

(*
   本节说明 Elimination 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition q_col : Matrix Q_Field 2 1 :=
  fun i _ => match i with
             | Fin.F1 => 1%Q
             | _ => 2%Q
             end.

Definition q_col_lnb : LeftNullBasis Q_Field q_col :=
  left_null_basis Q_Field q_dec q_col.

Example q_col_dim : lnb_dim q_col_lnb = 1%nat := eq_refl.

Example q_col_basis_0 :
  lnb_basis q_col_lnb Fin.F1 Fin.F1 = (-2 # 1)%Q := eq_refl.

Example q_col_basis_1 :
  lnb_basis q_col_lnb Fin.F1 (Fin.FS Fin.F1) = (1 # 1)%Q := eq_refl.

(* (−2)·1 + 1·2 = 0, computed in ℚ. *)
Example q_col_annih_computes :
  mat_mul Q_Field (lnb_basis q_col_lnb) q_col Fin.F1 Fin.F1
    = (0 # 1)%Q := eq_refl.
