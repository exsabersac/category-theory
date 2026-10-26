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
   * * Row operations are left multiplication by a matrix

   Riehl, “Category Theory in Context”, 2nd ed., §2.2, Corollary 2.2.10
   (printed p. 65) [riehl:2.2:cor10].
   nLab: https://ncatlab.org/nlab/show/Yoneda+lemma
   Wikipedia: https://en.wikipedia.org/wiki/Elementary_matrix

   In the matrix category (Instance/Matr.v: objects the naturals, an
   arrow m ~> n an n × m matrix over a rig R), the matrices with n rows
   are the elements of the represented presheaf [Hom ─,n], and a ROW
   OPERATION — an operation defined uniformly on all matrices with n
   rows, commuting with right multiplication — is exactly a natural
   endomorphism of that presheaf.  The Yoneda lemma therefore makes
   Gaussian elimination categorical: every row operation is left
   multiplication by the single n × n matrix obtained by applying the
   operation to the identity, and that matrix is unique.

   THE DERIVATION IS THE POINT, as the issue insists: the corollary is
   read off Functor/Hom/Yoneda.v's [Yoneda_Embedding] — the setoid
   isomorphism  Presheaves [Hom ─,n] [Hom ─,n] ≊ (n ~> n)  — rather
   than proved by a matrix computation.  Its [from] direction IS
   left-multiplication, so the factorization is the round trip
   [iso_from_to] read pointwise, the representing matrix is the [to]
   direction (evaluation at the identity, [representing_matrix_at_id]),
   and uniqueness is injectivity of [to] through the other round trip.
   In the headline theorem no entry of any matrix is ever inspected
   (the supporting lemmas bind entry indices only to peel Matr's
   entrywise hom-setoid).

   NATURALITY IS LINEARITY.  The presheaf action of [Hom ─,n] is right
   multiplication, so the naturality square of an endomorphism η says
   η (M · f) ≈ η M · f — the “linearity in the columns” that lets an
   operation defined row-wise be applied before or after a change of
   basis on the source.  [row_operation_natural] and
   [Build_row_operation] state the two directions: every row operation
   has the property, and any ≈-respecting family with the property
   assembles into a row operation.

   THE WITNESS: swapping the two rows of a 2 × m matrix, packaged as
   [swap_rows_op] over any rig, with its representing matrix computed
   entrywise BY [eq_refl] over ℕ — the permutation matrix
   [[0,1],[1,0]], as Gaussian elimination expects. 

   --------
   * * 行操作是矩阵的左乘

   Riehl，《情境中的范畴论》，第二版，第2.2节，推论2.2.10
   （印刷版第65页）  [riehl:2.2:cor10]。
   nLab: https://ncatlab.org/nlab/show/Yoneda+lemma
   维基百科: https://en.wikipedia.org/wiki/Elementary_matrix

   在矩阵范畴（Instance/Matr.v：对象为自然数，箭头 m ~> n 是一个在幂 R 上的 n × m 矩阵）中，具有 n 行的矩阵是表示的预层  [Hom ─,n] 的元素，并且行操作——在所有具有 n 行的矩阵上统一定义、与右乘法交换的操作——正是该预层的自然自同态。因此，Yoneda 引理使高斯消元具有范畴意义：每个行操作都是通过将该操作作用在单位矩阵上得到的单一 n × n 矩阵的左乘，而该矩阵是唯一的。推导才是关键，正如该问题所坚持的：推论可以从 Functor/Hom/Yoneda.v 的 [Yoneda_Embedding] 读取 —— 该集合等价同构 Presheaves [Hom ─,n] [Hom ─,n] ≊ (n ~> n) —— 而不是通过矩阵计算来证明。它的 [from] 方向是左乘法，因此分解就是 [iso_from_to] 的往返点读取，表示矩阵是 [to] 方向（在恒等元素处求值，[representing_matrix_at_id]），唯一性通过另一条往返路线对应 [to] 的单射性来体现。在标题定理中，没有任何矩阵条目会被直接检查（辅助引理只是将条目索引绑定到抽取 Matr 的逐条目同态集合）。自然性就是线性。[Hom ─,n] 的预层作用是右乘，所以一个自同态 η 的自然性方格表达的是 η (M · f) ≈ η M · f——列的“线性性”使得按行定义的操作可以在源矩阵的基变换之前或之后应用。[row_operation_natural] 和 [Build_row_operation] 表示两个方向：每个行操作都有此性质，并且任何具有该性质的保持≈关系的家族都可以组装成一个行操作。

   证明：交换一个 2 × m 矩阵的两行，将其包装为 [swap_rows_op]，适用于任意幺半环，并通过 [eq_refl] 在 ℕ 上逐元素计算其表示矩阵——置换矩阵 [[0,1], [1,0]，就像高斯消元所期望的那样。
*)

(** ** Row operations / ** 行操作 *)

Section RowOps.

Context (R : RigObject).

(*
 A row operation on matrices with n rows: a natural endomorphism of
 the presheaf represented by n.  [Presheaves] is the functor category
 [(Matr R)^op, Sets]; its homs are natural transformations. 

 --------
 对具有 n 行的矩阵的行操作：由 n 表示的预层的自然自同态。[Presheaves] 是函子范畴 [(Matr R)^op, Sets]；其 Hom 是自然变换。
*)
Definition row_operation (n : nat) : Type :=
  @hom (@Presheaves (Matr R) Sets)
    (@Curried_CoHom (Matr R) n) (@Curried_CoHom (Matr R) n).

(*
 Naturality, read concretely: a row operation commutes with right
 multiplication — the linearity the corollary's proof turns on. 

 --------
 自然性，具体地说：行运算与右乘法可交换——这一性质是推论证明所依赖的线性性。
*)
Lemma row_operation_natural {n : nat} (η : row_operation n)
  {m m' : nat} (f : m' ~{Matr R}~> m) (M : m ~{Matr R}~> n) :
  transform[η] m' (M ∘[Matr R] f) ≈ transform[η] m M ∘[Matr R] f.
Proof.
  symmetry; exact (@naturality _ _ _ _ η _ _ f M).
Qed.

(*
 Conversely, any ≈-respecting family commuting with right
 multiplication is a row operation: naturality is EXACTLY that
 property, so the two notions coincide. 

 --------
 相反，任何与右乘法交换的≈-保持族都是一种行操作：自然性正是那个性质，因此这两个概念是重合的。
*)
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

(* * ** The corollary, through the Yoneda embedding / * ** 通过 Yoneda 嵌入的推论 *)

(*
 The representing matrix of a row operation: the [to] direction of the
 Yoneda embedding's isomorphism. 

 --------
 行变换的表示矩阵：Yoneda 嵌入同构的 [to] 方向。
*)
Definition representing_matrix {n : nat} (η : row_operation n) :
  n ~{Matr R}~> n :=
  to (Yoneda_Embedding (Matr R) n n) η.

(*
 It is the operation applied to the identity matrix — evaluation at
 the identity being the forward map of the Yoneda lemma. 

 --------
 这是施加在单位矩阵上的运算——在单位矩阵处的求值是约内达引理的前向映射。
*)
Lemma representing_matrix_at_id {n : nat} (η : row_operation n) :
  representing_matrix η ≈ transform[η] n (@id (Matr R) n).
Proof.
  unfold representing_matrix; simpl.
  reflexivity.
Qed.

(*
 Riehl, Corollary 2.2.10: every row operation is left multiplication
 by its representing matrix.  The proof is the [iso_from_to] round
 trip of the embedding, read pointwise — the [from] direction is
 literally left-composition. 

 --------
 Riehl，推论 2.2.10：每一个行操作都是通过其表示矩阵进行的左乘。证明是嵌入的 [iso_from_to] 往返过程，逐点读取 —— [from] 方向字面意思是左复合。
*)
Theorem row_operations_are_left_multiplication {n : nat}
  (η : row_operation n) (m : nat) (M : m ~{Matr R}~> n) :
  transform[η] m M ≈ representing_matrix η ∘[Matr R] M.
Proof.
  symmetry.
  exact (iso_from_to (Yoneda_Embedding (Matr R) n n) η m M).
Qed.

(*
 ...and the representing matrix is unique: any matrix that acts as η
 by left multiplication is the representing matrix, by injectivity of
 the embedding's [to] through the other round trip. 

 --------
 ...并且表示矩阵是唯一的：根据嵌入的 [to] 通过另一轮往返的单射性，任何通过左乘作为 η 作用的矩阵都是表示矩阵。
*)
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
  (* the transformations agree pointwise, in the opposite orientation / 变换在每一点上都一致，但方向相反 *)
  intros m M i j; simpl.
  symmetry.
  apply (HP m M i j).
Qed.

End RowOps.

(* * ** A worked elementary operation: swapping two rows / * ** 一个已操作的初等变换：交换两行 *)

Section Swap.

Context (R : RigObject).

(* The transposition of Fin.t 2. / Fin.t 2 的换位 *)
Definition fin2_swap (i : Fin.t 2) : Fin.t 2 :=
  match i with
  | Fin.F1 => Fin.FS Fin.F1
  | Fin.FS _ => Fin.F1
  end.

(*
 Swapping the two rows of a 2 × m matrix.  Rows are permuted, columns
 untouched, so right multiplication passes through — the linearity
 hypothesis is definitional. 

 --------
 交换一个 2 × m 矩阵的两行。行被置换，列保持不变，因此右乘法通过——线性假设是定义性的。
*)
Program Definition swap_rows_op : row_operation R 2 :=
  Build_row_operation R
    (fun m M => fun i j => M (fin2_swap i) j)
    _ _.

End Swap.

(* * ** The representing matrix of the swap computes over ℕ / * ** 交换的表示矩阵在 ℕ 上计算 *)

(*
 Applying the swap to the 2 × 2 identity yields the permutation matrix
 [[0,1],[1,0]], entry by entry, by pure computation. 

 --------
 将交换应用于 2 × 2 单位矩阵得到排列矩阵 [[0,1]，[1,0]，逐项通过纯计算得到。
*)
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
