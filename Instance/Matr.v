Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Vectors.Fin.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(*
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_matrices

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The finite-sum library *)

Section FinSum.

Context (R : RigObject).

(* Σ_{i : Fin.t n} f i, by recursion on n. *)
Fixpoint fin_sum {n : nat} : (Fin.t n → carrier (rig_setoid R)) →
  carrier (rig_setoid R) :=
  match n with
  | O => fun _ => rig_zero R
  | S k => fun f => rig_add R (f Fin.F1) (fin_sum (fun i => f (Fin.FS i)))
  end.

Lemma fin_sum_respects {n : nat}
  (f g : Fin.t n → carrier (rig_setoid R)) :
  (∀ i, f i ≈ g i) → fin_sum f ≈ fin_sum g.
Proof.
  induction n; simpl; intros H.
  - reflexivity.
  - apply rig_add_respects; [ apply H |].
    apply IHn; intro i; apply H.
Qed.

Lemma fin_sum_zero {n : nat} :
  fin_sum (fun _ : Fin.t n => rig_zero R) ≈ rig_zero R.
Proof.
  induction n; simpl.
  - reflexivity.
  - now rewrite IHn, rig_add_zero_l.
Qed.

(* Σ (f + g) ≈ Σ f + Σ g, by commutativity and associativity of +. *)
Lemma fin_sum_add {n : nat}
  (f g : Fin.t n → carrier (rig_setoid R)) :
  fin_sum (fun i => rig_add R (f i) (g i))
    ≈ rig_add R (fin_sum f) (fin_sum g).
Proof.
  induction n; simpl.
  - now rewrite rig_add_zero_l.
  - rewrite IHn.
    (* (a+b)+(c+d) ≈ (a+c)+(b+d) *)
    rewrite rig_add_assoc.
    rewrite <- (rig_add_assoc R (g Fin.F1)).
    rewrite (rig_add_comm R (g Fin.F1)
               (fin_sum (fun i => f (Fin.FS i)))).
    rewrite rig_add_assoc.
    rewrite <- rig_add_assoc.
    reflexivity.
Qed.

(* Exchange of double sums. *)
Lemma fin_sum_swap {n m : nat}
  (f : Fin.t n → Fin.t m → carrier (rig_setoid R)) :
  fin_sum (fun i => fin_sum (fun j => f i j))
    ≈ fin_sum (fun j => fin_sum (fun i => f i j)).
Proof.
  induction n; simpl.
  - now rewrite fin_sum_zero.
  - rewrite IHn.
    now rewrite <- fin_sum_add.
Qed.

(* 相关说明。 （已译） *)
Lemma fin_sum_mul_l {n : nat} (x : carrier (rig_setoid R))
  (f : Fin.t n → carrier (rig_setoid R)) :
  rig_mul R x (fin_sum f) ≈ fin_sum (fun i => rig_mul R x (f i)).
Proof.
  induction n; simpl.
  - apply rig_mul_zero_r.
  - now rewrite rig_distr_l, IHn.
Qed.

Lemma fin_sum_mul_r {n : nat} (x : carrier (rig_setoid R))
  (f : Fin.t n → carrier (rig_setoid R)) :
  rig_mul R (fin_sum f) x ≈ fin_sum (fun i => rig_mul R (f i) x).
Proof.
  induction n; simpl.
  - apply rig_mul_zero_l.
  - now rewrite rig_distr_r, IHn.
Qed.

(* 相关说明。 （已译） *)

Definition delta {n : nat} (i j : Fin.t n) : carrier (rig_setoid R) :=
  match Fin.eq_dec i j with
  | left _ => rig_one R
  | right _ => rig_zero R
  end.

Lemma delta_refl {n : nat} (i : Fin.t n) : delta i i ≈ rig_one R.
Proof.
  unfold delta.
  destruct (Fin.eq_dec i i) as [_|Hne]; [ reflexivity |].
  contradiction Hne; reflexivity.
Qed.

Lemma delta_neq {n : nat} (i j : Fin.t n) :
  i ≠ j → delta i j ≈ rig_zero R.
Proof.
  intro Hne; unfold delta.
  destruct (Fin.eq_dec i j) as [He|_]; [ contradiction | reflexivity ].
Qed.

Lemma delta_sym {n : nat} (i j : Fin.t n) : delta i j ≈ delta j i.
Proof.
  unfold delta.
  destruct (Fin.eq_dec i j) as [He|Hne], (Fin.eq_dec j i) as [He'|Hne'];
    try reflexivity.
  - contradiction Hne'; now symmetry.
  - contradiction Hne; now symmetry.
Qed.

(* Σ_l delta i l · f l ≈ f i: only the l = i summand survives. *)
Lemma fin_sum_delta_l {n : nat} (i : Fin.t n)
  (f : Fin.t n → carrier (rig_setoid R)) :
  fin_sum (fun l => rig_mul R (delta i l) (f l)) ≈ f i.
Proof.
  induction n; simpl.
  - inversion i.
  - revert f.
    pattern i.
    apply (Fin.caseS' i); intros; simpl.
    + rewrite delta_refl, rig_mul_one_l.
      rewrite (fin_sum_respects
                 (fun l => rig_mul R (delta Fin.F1 (Fin.FS l)) (f (Fin.FS l)))
                 (fun _ => rig_zero R)).
      * now rewrite fin_sum_zero, rig_add_zero_r.
      * intro l.
        rewrite (delta_neq Fin.F1 (Fin.FS l)); [ apply rig_mul_zero_l |].
        discriminate.
    + rewrite (delta_neq (Fin.FS p) Fin.F1); [| discriminate ].
      rewrite rig_mul_zero_l, rig_add_zero_l.
      rewrite (fin_sum_respects
                 (fun l => rig_mul R (delta (Fin.FS p) (Fin.FS l)) (f (Fin.FS l)))
                 (fun l => rig_mul R (delta p l) (f (Fin.FS l)))).
      * apply IHn.
      * intro l.
        apply rig_mul_respects; [| reflexivity ].
        unfold delta.
        destruct (Fin.eq_dec p l) as [He|Hne],
                 (Fin.eq_dec (Fin.FS p) (Fin.FS l)) as [He'|Hne'];
          try reflexivity.
        -- contradiction Hne'; now rewrite He.
        -- contradiction Hne; now apply Fin.FS_inj.
Qed.

(* Σ_l f l · delta l j ≈ f j. *)
Lemma fin_sum_delta_r {n : nat} (j : Fin.t n)
  (f : Fin.t n → carrier (rig_setoid R)) :
  fin_sum (fun l => rig_mul R (f l) (delta l j)) ≈ f j.
Proof.
  rewrite (fin_sum_respects
             (fun l => rig_mul R (f l) (delta l j))
             (fun l => rig_mul R (f l) (delta j l))).
  2: { intro l; apply rig_mul_respects; [ reflexivity | apply delta_sym ]. }
  induction n; simpl.
  - inversion j.
  - revert f.
    pattern j.
    apply (Fin.caseS' j); intros; simpl.
    + rewrite delta_refl, rig_mul_one_r.
      rewrite (fin_sum_respects
                 (fun l => rig_mul R (f (Fin.FS l)) (delta Fin.F1 (Fin.FS l)))
                 (fun _ => rig_zero R)).
      * now rewrite fin_sum_zero, rig_add_zero_r.
      * intro l.
        rewrite (delta_neq Fin.F1 (Fin.FS l)); [ apply rig_mul_zero_r |].
        discriminate.
    + rewrite (delta_neq (Fin.FS p) Fin.F1); [| discriminate ].
      rewrite rig_mul_zero_r, rig_add_zero_l.
      rewrite (fin_sum_respects
                 (fun l => rig_mul R (f (Fin.FS l)) (delta (Fin.FS p) (Fin.FS l)))
                 (fun l => rig_mul R (f (Fin.FS l)) (delta p l))).
      * apply IHn.
      * intro l.
        apply rig_mul_respects; [ reflexivity |].
        unfold delta.
        destruct (Fin.eq_dec p l) as [He|Hne],
                 (Fin.eq_dec (Fin.FS p) (Fin.FS l)) as [He'|Hne'];
          try reflexivity.
        -- contradiction Hne'; now rewrite He.
        -- contradiction Hne; now apply Fin.FS_inj.
Qed.

End FinSum.

(** ** The category *)

Section Matr.

Context (R : RigObject).

(* An arrow n ~> m is an m × n matrix: m rows, n columns. *)
Definition Matrix (rows cols : nat) : Type :=
  Fin.t rows → Fin.t cols → carrier (rig_setoid R).

#[local] Obligation Tactic := idtac.

Program Definition Matr : Category := {|
  obj     := nat;
  hom     := fun n m => Matrix m n;
  homset  := fun n m => {|
    Setoid.equiv := fun A B => ∀ i j, A i j ≈ B i j
  |};
  id      := fun n => fun i j => delta R i j;
  compose := fun n m k A B => fun i j =>
    fin_sum R (fun l : Fin.t m => rig_mul R (A i l) (B l j))
|}.
Next Obligation.
  intros n m; simpl.
  equivalence.
  now rewrite X, X0.
Qed.
Next Obligation.
  intros n m k A A' HA B B' HB i j; simpl.
  apply fin_sum_respects; intro l.
  now rewrite (HA i l), (HB l j).
Qed.
Next Obligation.
  intros n m A i j; simpl.
  apply (fin_sum_delta_l R i (fun l => A l j)).
Qed.
Next Obligation.
  intros n m A i j; simpl.
  apply (fin_sum_delta_r R j (fun l => A i l)).
Qed.
Next Obligation.
  intros n m k w A B C i j; simpl.
  (* Σ_l A i l · (Σ_p B l p · C p j) ≈ Σ_p (Σ_l A i l · B l p) · C p j *)
  etransitivity.
  { apply fin_sum_respects; intro l.
    apply fin_sum_mul_l. }
  etransitivity; [ apply fin_sum_swap |].
  apply fin_sum_respects; intro p.
  etransitivity.
  2: { symmetry; apply fin_sum_mul_r. }
  apply fin_sum_respects; intro l.
  symmetry; apply rig_mul_assoc.
Qed.
Next Obligation.
  intros n m k w A B C i j; simpl.
  symmetry.
  etransitivity.
  { apply fin_sum_respects; intro l.
    apply fin_sum_mul_l. }
  etransitivity; [ apply fin_sum_swap |].
  apply fin_sum_respects; intro p.
  etransitivity.
  2: { symmetry; apply fin_sum_mul_r. }
  apply fin_sum_respects; intro l.
  symmetry; apply rig_mul_assoc.
Qed.

End Matr.

(* 相关说明。 （已译） *)

Definition Matr_N : Category := Matr Nat_Rig.

Example Matr_N_id_entry : @id Matr_N 2%nat Fin.F1 Fin.F1 = 1%nat := eq_refl.
Example Matr_N_id_off :
  @id Matr_N 2%nat Fin.F1 (Fin.FS Fin.F1) = 0%nat := eq_refl.

(* A concrete 1×1 product computes: (3) · (4) = (12). *)
Example Matr_N_prod :
  (@compose Matr_N 1%nat 1%nat 1%nat (fun _ _ => 3%nat) (fun _ _ => 4%nat))
    Fin.F1 Fin.F1 = 12%nat := eq_refl.

(* 相关说明。 （已译） *)

Section Transpose.

Context (R : RigObject).
Context (comm : ∀ a b, rig_mul R a b ≈ rig_mul R b a).

#[local] Obligation Tactic := idtac.

(* Identity 对象; A ↦ Aᵀ arrows. An arrow n ~> m Matr is an
 m × n matrix; its transpose is n × m matrix, arrow m ~> n,
 i.e. arrow n ~> m 反 — 恒等-on-对象 really is
 right type. Functoriality (AB)ᵀ ≈ BᵀAᵀ is where [comm] is
 spent.（已译） *)
Program Definition Matr_Transpose : Matr R ⟶ (Matr R)^op := {|
  fobj := fun n : nat => n;
  fmap := fun n m A => fun j i => A i j
|}.
Next Obligation.
  intros n m A B HAB j i; simpl.
  apply HAB.
Qed.
Next Obligation.
  intros n j i; simpl.
  apply delta_sym.
Qed.
Next Obligation.
  intros n m k A B j i; simpl.
  apply fin_sum_respects; intro l.
  apply comm.
Qed.

(* Transposition involutive nose, so same 函子 read
 backwards inverts it; pair 同构 范畴. （已译） *)
Program Definition Matr_Transpose_op : (Matr R)^op ⟶ Matr R := {|
  fobj := fun n : nat => n;
  fmap := fun n m A => fun j i => A i j
|}.
Next Obligation.
  intros n m A B HAB j i; simpl.
  exact (HAB i j).
Qed.
Next Obligation.
  intros n j i; simpl.
  apply delta_sym.
Qed.
Next Obligation.
  intros n m k A B j i; simpl.
  apply fin_sum_respects; intro l.
  apply comm.
Qed.

(* Mac Lane II.3 Exercise 4 / Riehl 1.3.14(v): the matrix category is
   isomorphic to its opposite, identity on objects, by transposition. *)
Program Definition Matr_transpose_iso : Matr R ≅[Cat] (Matr R)^op := {|
  to := Matr_Transpose;
  from := Matr_Transpose_op
|}.
Next Obligation.
  exists (fun n => iso_id).
  intros n m A i j; simpl.
  symmetry.
  etransitivity.
  { apply (fin_sum_delta_l R). }
  apply (fin_sum_delta_r R).
Qed.
Next Obligation.
  exists (fun n => iso_id).
  intros n m A i j; simpl.
  symmetry.
  etransitivity.
  { apply (fin_sum_delta_r R j
             (fun l => fin_sum R
                         (fun p => rig_mul R (delta R i p) (A p l)))). }
  apply (fin_sum_delta_l R i (fun p => A p j)).
Qed.

End Transpose.

(** ** Acceptance tests *)

(* 相关说明。 （已译） *)
Definition Matr_N_transpose_iso : Matr_N ≅[Cat] Matr_N^op :=
  Matr_transpose_iso Nat_Rig (fun a b => Nat.mul_comm a b).

(* 相关说明。 （已译） *)
Definition Matr_Z : Category := Matr Int_Rig.
Definition Matr_Z_transpose_iso : Matr_Z ≅[Cat] Matr_Z^op :=
  Matr_transpose_iso Int_Rig (fun a b => Z.mul_comm a b).

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example Matr_zero_collapse (n m : nat)
  (A B : n ~{Matr Zero_Rig}~> m) : A ≈ B.
Proof. intros i j; exact I. Qed.

(* Objects really bare naturals, 恒等 Kronecker. （已译） *)
Example Matr_obj (R : RigObject) : obj[Matr R] = nat := eq_refl.
