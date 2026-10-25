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
   * * Matr: the matrix category over a rig

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §I.2
   (printed p. 11): for a commutative ring K, [Matr_K] has the positive
   integers as objects — here all of [nat], the issue's specification;
   0 is the empty matrix and costs nothing — and an arrow n → m is an
   m × n matrix over K,
   composed by matrix product [maclane:I.2:construction5]; §II.3
   Exercise 4 (printed p. 40): the opposite of the matrix category is
   the matrix category again, via transposition [maclane:II.3:ex4].
   Awodey, "Category Theory", §1.4 (printed p. 8): the same category
   with NATURAL-number entries — matrices over the rig ℕ
   [awodey:1.4:construction-mat].
   Riehl, "Category Theory in Context", §1.1 Example 1.1.4(i) and §1.3
   Example 1.3.14(v): the category and its transpose self-duality
   [riehl:1.1:example4, riehl:1.3:example14].
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_matrices

   THE BASE IS A RIG, per the issue's QA corrections: the category laws
   need only associativity, units, distributivity and annihilation —
   never subtraction — so [Matr] is stated over Theory/Algebra/Rig.v's
   [RigObject] (#839's class, consumed, not redefined), and Awodey's
   ℕ-matrix category is the instance [Matr_N := Matr Nat_Rig].  Matrices
   over Mac Lane's commutative ring K are the instance at any
   [RingObject]'s underlying rig with commutative multiplication.

   ORIENTATION, as the issue asks to fix and document: following Mac
   Lane's "an arrow A : n → m is an m × n matrix", the hom [n ~> m] is
   [Matrix R m n] — m rows, n columns, a function
   [Fin.t m → Fin.t n → carrier R] — so composition
   [A ∘ B := fun i j => Σ_l A i l · B l j] is the usual matrix product
   with NO transposition anywhere.  Morphism equality is entrywise ≈.

   THE ENGINE is a small reusable finite-sum library, parameterized by
   the RIG (the additive-only lemmas — [fin_sum] with congruence,
   [fin_sum_zero], additivity, and the exchange [fin_sum_swap] — spend
   only the additive commutative monoid, i.e. [rig_cmon R], and a
   monoid-level refounding over [CMonObject] is a disclosed possible
   generalization, deferred until a monoid-only consumer exists);
   bilinearity of · over Σ ([fin_sum_mul_l/r]) is where distributivity
   and annihilation are spent, and the Kronecker collapse
   ([fin_sum_delta_l/r]) is where decidability of [Fin.t] equality via
   [Fin.eq_dec] is spent.  The issue asks these be kept reusable: the
   GL_n/determinant issue consumes them next.

   THE SELF-DUALITY: transposition is an identity-on-objects functor
   [Matr_Transpose : Matr R ⟶ (Matr R)^op] whenever the rig's
   multiplication is COMMUTATIVE — (AB)ᵀ = BᵀAᵀ needs exactly the
   commutation of the two factors inside the sum — and it is involutive
   on the nose, so the pair assembles into the isomorphism of categories
   [Matr_transpose_iso : Matr R ≅[Cat] (Matr R)^op] (Riehl 1.3.14(v),
   Mac Lane II.3 Ex 4).  Over a non-commutative rig the same functor
   would land in matrices over the OPPOSITE rig; that generalization is
   noted and not needed by any consumer in the queue. 

   --------
   * * Matr：一个环上的矩阵范畴Mac Lane，《为工作中的数学家准备的范畴论》，第2版，第I.2节（印刷第11页）：对于一个交换环K，[Matr_K]的对象是正整数——这里[nat]的所有元素都是问题的指定；0是空矩阵且不花费——箭头n → m是一个m × n的K上的矩阵，由矩阵乘法[maclane:I.2:construction5]组成；第II.3节习题4（印刷第40页）：矩阵范畴的对偶仍然是矩阵范畴，通过转置[maclane:II.3:ex4]。Awodey，《范畴论》，第1.4节（印刷第8页）：同一个范畴，其条目为自然数——ℕ上的矩阵[awodey:1.4:construction-mat]。Riehl，《语境中的范畴论》，第1.1节示例1.1.4(i)和第1.3节示例1.3.14(v)：该范畴及其转置自对偶[riehl:1.1:example4, riehl:1.3:example14]。维基百科：https://en.wikipedia.org/wiki/Category_of_matrices根据该问题的 QA 更正，基础是一个幺半环：该范畴律只需要结合律、单位元、分配律和幺化律——从不需要减法——因此 [Matr] 是在 Theory/Algebra/Rig.v 的 [RigObject]（#839 的类，已使用，未重新定义）上陈述的，而 Awodey 的 ℕ-矩阵范畴是实例 [Matr_N := Matr Nat_Rig]。矩阵在 Mac Lane 的交换环 K 上是任何 [RingObject] 的底层幺半环的实例（具有交换乘法）。

   方向性，正如问题要求修复和记录的：遵循 Mac Lane 的“一个箭头 A : n → m 是一个 m × n 矩阵”，同态 [n ~> m] 是 [Matrix R m n]——m 行，n 列，一个函数 [Fin.t m → Fin.t n → carrier R]——因此组合 [A ∘ B := fun i j => Σ_l A i l · B l j] 是通常的矩阵乘法，任何地方都没有转置。态射相等是按条目逐个 ≈。引擎是一个小型可重用的有限和库，由 RIG 参数化（仅加性引理——[fin_sum] 带一致性，[fin_sum_zero]，加法性，以及交换 [fin_sum_swap]——仅使用加性交换幺半群，即 [rig_cmon R]，并且在 [CMonObject] 上进行单子级别的重建是一个已公布的可能推广，推迟到存在仅单子使用者时）；Σ 上 · 的双线性性（[fin_sum_mul_l/r]）是分配性和消去性被使用的地方，而克罗内克塌缩（[fin_sum_delta_l/r]）是通过 [Fin.eq_dec] 决定 [Fin.t] 是否相等被使用的地方。该问题要求这些保持可重用：GL_n/行列式问题随后会消耗它们。自对偶性：转置是一个在对象上为恒等的函子 [Matr_Transpose : Matr R ⟶ (Matr R)^op]，当且仅当环的乘法是可交换的——(AB)ᵀ = BᵀAᵀ 正好需要和式中两个因子的交换——并且它在本身上是自反的，因此该对可以组装成范畴的同构 [Matr_transpose_iso : Matr R ≅[Cat] (Matr R)^op] (Riehl 1.3.14(v), Mac Lane II.3 习题 4)。在非交换环上，相同的函子会映射到对偶环上的矩阵；该推广已被指出，但队列中的任何使用者都不需要它。
*)

(** ** The finite-sum library / ** 有限和库 *)

Section FinSum.

Context (R : RigObject).

(* Σ_{i : Fin.t n} f i, by recursion on n. / Σ_{i : Fin.t n} f i，通过对 n 的递归。 *)
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

(* Σ (f + g) ≈ Σ f + Σ g, by commutativity and associativity of +. / Σ (f + g) ≈ Σ f + Σ g，根据 + 的交换律和结合律。 *)
Lemma fin_sum_add {n : nat}
  (f g : Fin.t n → carrier (rig_setoid R)) :
  fin_sum (fun i => rig_add R (f i) (g i))
    ≈ rig_add R (fin_sum f) (fin_sum g).
Proof.
  induction n; simpl.
  - now rewrite rig_add_zero_l.
  - rewrite IHn.
    (* (a+b)+(c+d) ≈ (a+c)+(b+d) / (a+b)+(c+d) ≈ (a+c)+(b+d) *)
    rewrite rig_add_assoc.
    rewrite <- (rig_add_assoc R (g Fin.F1)).
    rewrite (rig_add_comm R (g Fin.F1)
               (fin_sum (fun i => f (Fin.FS i)))).
    rewrite rig_add_assoc.
    rewrite <- rig_add_assoc.
    reflexivity.
Qed.

(* Exchange of double sums. / 双重求和的交换。 *)
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

(* Bilinearity: multiplication distributes over Σ on both sides — the two clauses of distributivity, and annihilation at n = 0. / 双线性：乘法在两边对Σ分配——分配律的两个条款，以及在 n = 0 时的消去。 *)
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

(* * ** The Kronecker delta and its collapse / * ** 克罗内克δ及其塌缩 *)

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

(* Σ_l delta i l · f l ≈ f i: only the l = i summand survives. / Σ_l delta i l · f l ≈ f i：只有 l = i 的项会存活。 *)
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

(* Σ_l f l · delta l j ≈ f j. / Σ_l f_l · δ_lj ≈ f_j。 *)
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

(** ** The category / ** 类别 *)

Section Matr.

Context (R : RigObject).

(* An arrow n ~> m is an m × n matrix: m rows, n columns. / 一个箭头 n ~> m 是一个 m × n 的矩阵：m 行，n 列。 *)
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
  (* Σ_l A i l · (Σ_p B l p · C p j) ≈ Σ_p (Σ_l A i l · B l p) · C p j / Σ_l A i l · (Σ_p B l p · C p j) ≈ Σ_p (Σ_l A i l · B l p) · C p j *)
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

(* * ** Awodey's instance: matrices over the rig ℕ / * ** Awodey 的例子：关于幺半环 ℕ 的矩阵 *)

Definition Matr_N : Category := Matr Nat_Rig.

Example Matr_N_id_entry : @id Matr_N 2%nat Fin.F1 Fin.F1 = 1%nat := eq_refl.
Example Matr_N_id_off :
  @id Matr_N 2%nat Fin.F1 (Fin.FS Fin.F1) = 0%nat := eq_refl.

(* A concrete 1×1 product computes: (3) · (4) = (12). / 一个具体的 1×1 产品计算： (3) · (4) = (12)。 *)
Example Matr_N_prod :
  (@compose Matr_N 1%nat 1%nat 1%nat (fun _ _ => 3%nat) (fun _ _ => 4%nat))
    Fin.F1 Fin.F1 = 12%nat := eq_refl.

(* * ** The transpose self-duality (commutative base) / * ** 转置自对偶性（交换基） *)

Section Transpose.

Context (R : RigObject).
Context (comm : ∀ a b, rig_mul R a b ≈ rig_mul R b a).

#[local] Obligation Tactic := idtac.

(*
 Identity on objects; A ↦ Aᵀ on arrows.  An arrow n ~> m of Matr is an
 m × n matrix; its transpose is the n × m matrix, an arrow m ~> n,
 i.e. an arrow n ~> m of the opposite — identity-on-objects really is
 the right type.  Functoriality (AB)ᵀ ≈ BᵀAᵀ is where [comm] is
 spent. 

 --------
 对象上的恒等映射；箭头上的 A ↦ Aᵀ。Matr 的箭头 n ~> m 是一个 m × n 矩阵；它的转置是 n × m 矩阵，一个箭头 m ~> n，即对偶范畴的箭头 n ~> m —— 对象上的恒等映射确实是正确的类型。函子性 (AB)ᵀ ≈ BᵀAᵀ 就是在 [comm] 上花费的地方。
*)
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

(*
 Transposition is involutive on the nose, so the same functor read
 backwards inverts it; the pair is an isomorphism of categories. 

 --------
 换位在准确意义上是自反的，因此同一个函子倒过来读就会取反；这一对是范畴的同构。
*)
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

(*
 Mac Lane II.3 Exercise 4 / Riehl 1.3.14(v): the matrix category is
 isomorphic to its opposite, identity on objects, by transposition. 

 --------
 Mac Lane II.3 练习 4 / Riehl 1.3.14(v)：矩阵范畴通过转置在对象上保持恒等，与其对立范畴同构。
*)
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

(** ** Acceptance tests / ** 验收测试 *)

(* The naturals are a commutative rig, so Matr_N is self-dual. / 自然数是一个交换半环，所以 Matr_N 是自对偶的。 *)
Definition Matr_N_transpose_iso : Matr_N ≅[Cat] Matr_N^op :=
  Matr_transpose_iso Nat_Rig (fun a b => Nat.mul_comm a b).

(* Mac Lane's own headline case: matrices over a commutative RING — the integers, with the transpose self-duality at Z.mul_comm. / Mac Lane 自己的重点案例：交换环上的矩阵——整数，以及在 Z.mul_comm 的转置自对偶性。 *)
Definition Matr_Z : Category := Matr Int_Rig.
Definition Matr_Z_transpose_iso : Matr_Z ≅[Cat] Matr_Z^op :=
  Matr_transpose_iso Int_Rig (fun a b => Z.mul_comm a b).

(*
 Sanity, as the issue asks: over a one-element rig the category
 collapses — any two parallel matrices are equal, the carrier's
 equivalence being total.  [Zero_Rig] is Instance/Rng.v's zero ring. 

 --------
 理智，如问题所述：在一个单元素环上，范畴坍塌——任何两个平行矩阵都是相等的，载体的等价关系是全等的。[Zero_Rig] 是 Instance/Rng.v 的零环。
*)
Example Matr_zero_collapse (n m : nat)
  (A B : n ~{Matr Zero_Rig}~> m) : A ≈ B.
Proof. intros i j; exact I. Qed.

(* Objects really are bare naturals, and the identity is Kronecker. / 对象确实是裸自然数，而同一性是克罗内克形式。 *)
Example Matr_obj (R : RigObject) : obj[Matr R] = nat := eq_refl.
