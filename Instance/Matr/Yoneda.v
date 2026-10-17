Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Sheaf.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Matr.
Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/Yoneda+lemma
 Wikipedia: https://en.wikipedia.org/wiki/Elementary_matrix

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Row operations *)

Section RowOps.

Context (R : RigObject).

(*
   本节说明自然变换、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition row_operation (n : nat) : Type :=
  @hom (@Presheaves (Matr R) Sets)
    (@Curried_CoHom (Matr R) n) (@Curried_CoHom (Matr R) n).

(* Naturality, read concretely: row operation commutes right
 multiplication — linearity 推论's 证明 turns on. （已译） *)
Lemma row_operation_natural {n : nat} (η : row_operation n)
  {m m' : nat} (f : m' ~{Matr R}~> m) (M : m ~{Matr R}~> n) :
  transform[η] m' (M ∘[Matr R] f) ≈ transform[η] m M ∘[Matr R] f.
Proof.
  symmetry; exact (@naturality _ _ _ _ η _ _ f M).
Qed.

(* Conversely, any ≈-respecting family commuting right
 multiplication row operation: 自然性 EXACTLY that
 property, so two notions coincide. （已译） *)
Program Definition Build_row_operation {n : nat}
  (φ : ∀ m : nat, (m ~{Matr R}~> n) → (m ~{Matr R}~> n))
  (φ_respects : ∀ m (M M' : m ~{Matr R}~> n),
     M ≈ M' → φ m M ≈ φ m M')
  (φ_linear : ∀ (m m' : nat) (f : m' ~{Matr R}~> m) (M : m ~{Matr R}~> n),
     φ m' (M ∘[Matr R] f) ≈ φ m M ∘[Matr R] f) :
  row_operation n :=
  Build_Transform' (F := @Curried_CoHom (Matr R) n)
    (G := @Curried_CoHom (Matr R) n)
    (fun m => {| morphism := φ m ; proper_morphism := φ_respects m |})
    _.

(* * ** The 推论, through Yoneda embedding （已译） *)

(* The 表示 matrix row operation: [to] direction the
 Yoneda embedding's 同构. （已译） *)
Definition representing_matrix {n : nat} (η : row_operation n) :
  n ~{Matr R}~> n :=
  to (Yoneda_Embedding (Matr R) n n) η.

(* It operation applied 恒等 matrix — evaluation at
 恒等 being forward map Yoneda 引理. （已译） *)
Lemma representing_matrix_at_id {n : nat} (η : row_operation n) :
  representing_matrix η ≈ transform[η] n (@id (Matr R) n).
Proof.
  unfold representing_matrix; simpl.
  reflexivity.
Qed.

(*
   本节说明 Yoneda 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem row_operations_are_left_multiplication {n : nat}
  (η : row_operation n) (m : nat) (M : m ~{Matr R}~> n) :
  transform[η] m M ≈ representing_matrix η ∘[Matr R] M.
Proof.
  symmetry.
  exact (iso_from_to (Yoneda_Embedding (Matr R) n n) η m M).
Qed.

(* ...and 表示 matrix unique: any matrix acts η
 left multiplication 表示 matrix, injectivity of
 embedding's [to] through other round trip. （已译） *)
Theorem representing_matrix_unique {n : nat}
  (η : row_operation n) (P : n ~{Matr R}~> n) :
  (∀ (m : nat) (M : m ~{Matr R}~> n),
     transform[η] m M ≈ P ∘[Matr R] M) →
  P ≈ representing_matrix η.
Proof.
  intro HP.
  rewrite <- (iso_to_from (Yoneda_Embedding (Matr R) n n) P).
  unfold representing_matrix.
  apply (proper_morphism (to (Yoneda_Embedding (Matr R) n n))).
  (* 相关说明。 （已译） *)
  intros m M i j; simpl.
  symmetry.
  apply (HP m M i j).
Qed.

End RowOps.

(* 相关说明。 （已译） *)

Section Swap.

Context (R : RigObject).

(* The transposition of Fin.t 2. *)
Definition fin2_swap (i : Fin.t 2) : Fin.t 2 :=
  match i with
  | Fin.F1 => Fin.FS Fin.F1
  | Fin.FS _ => Fin.F1
  end.

(* Swapping two rows 2 × m matrix. Rows permuted, columns
 untouched, so right multiplication passes through — linearity
 假设 definitional. （已译） *)
Program Definition swap_rows_op : row_operation R 2 :=
  Build_row_operation R
    (fun m M => fun i j => M (fin2_swap i) j)
    _ _.

End Swap.

(* * ** The 表示 matrix swap computes over ℕ （已译） *)

(* Applying swap 2 × 2 恒等 yields permutation matrix
 [[0,1],[1,0]], entry entry, pure computation. （已译） *)
Example swap_rep_00 :
  representing_matrix Nat_Rig (swap_rows_op Nat_Rig) Fin.F1 Fin.F1 = 0%nat
  := eq_refl.
Example swap_rep_01 :
  representing_matrix Nat_Rig (swap_rows_op Nat_Rig)
    Fin.F1 (Fin.FS Fin.F1) = 1%nat := eq_refl.
Example swap_rep_10 :
  representing_matrix Nat_Rig (swap_rows_op Nat_Rig)
    (Fin.FS Fin.F1) Fin.F1 = 1%nat := eq_refl.
Example swap_rep_11 :
  representing_matrix Nat_Rig (swap_rows_op Nat_Rig)
    (Fin.FS Fin.F1) (Fin.FS Fin.F1) = 0%nat := eq_refl.
