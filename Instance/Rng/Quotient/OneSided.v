Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Quotient.
Require Import Category.Instance.Rng.Algebras.Associative.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * * A one-sided ideal does not give a quotient ring

   Mac Lane, “Categories for the Working Mathematician”, 2nd ed., §III.1
   Exercise 6 (printed p. 59) [maclane:III.1:ex6]: the quotient of a
   ring is taken by a TWO-SIDED ideal.  Instance/Rng/Quotient.v carries
   the construction and explains why both absorption laws are consumed;
   this file proves that neither can be dropped, by exhibiting a LEFT
   ideal for which the quotient relation is not a congruence for
   multiplication.

   THIS IS THE RING-LEVEL COUNTERPART of
   Instance/Grp/Quotient.v's [S3_refl_sub_not_normal], which refutes
   the normality CLOSURE condition for a particular subgroup.  Here
   [ut2_left_ideal_not_mul_congruence] refutes the CONGRUENCE itself,
   which is the property [rquot_rel_mul] establishes and the one the
   construction actually consumes; [ut2_e11_not_right_absorbing]
   separately refutes the dropped closure condition, so both readings
   are covered.

   READ THE COMPARISON PRECISELY.  An earlier draft of this header said
   the ring statement was stronger in shape because the group side left
   “and therefore the quotient would not be well defined” to the
   reader.  That was wrong, and an audit caught it: the group side
   ALREADY carries a congruence-level refutation, namely
   Instance/Grp/Congruence.v's [S3_refl_sub_no_congruence] -- at
   the same subgroup, landed by #301 -- so no inference is left
   implicit there either.  What is actually different is narrower and
   is all that is claimed: the refutation here is DIRECT, where the
   group one is obtained through [congruence_iff_normal]; and it lands
   on the MULTIPLICATION congruence specifically, which is the clause
   one-sidedness is unable to supply.

   THE WITNESS.  [UT2] (Instance/Rng/Algebras/Associative.v) is the
   ring of upper-triangular 2×2 integer matrices, carried as triples
   (a, b, c) for [[a, b], [0, c]], and that file proves it
   non-commutative ([UT2_not_commutative]).  It is NOT the tree's only
   non-commutative [RingObject] -- Instance/Rng/MonoidRing.v's
   [zmring_not_commutative] exhibits a monoid ring that is not
   commutative, although it proves that by mapping INTO [UT2] -- but it
   is the smallest, and the one whose elements compute, being integer
   triples.  The left ideal is ℤ·E₁₁, the multiples of
   the matrix unit E₁₁ = [[1, 0], [0, 0]]:

   x · (a, 0, 0) = (a'·a, 0, 0)   -- absorbed on the left,
   (1, 0, 0) · (0, 1, 0) = (0, 1, 0)   -- NOT absorbed on the right.

   Non-commutativity is not merely convenient here, it is necessary:
   over a commutative ring the two absorption laws are the same
   statement, so no commutative witness could exist.  That is why this
   file must reach for [UT2] and why it is a separate file --
   Instance/Rng/Algebras/Associative.v requires Instance/Mod.v and the
   associative-algebra tower, and no consumer of quotient rings should
   inherit that dependency.

   WHAT IS NOT CLAIMED.  Nothing here says a left ideal gives no
   quotient of any kind: ℤ·E₁₁ is in particular an additive subgroup, so
   UT2/ℤ·E₁₁ is a perfectly good quotient ABELIAN GROUP, and the
   left-module structure survives as well.  What is refuted is exactly
   that the ring MULTIPLICATION descends.  Nor is the RIGHT-sided
   mirror stated: the symmetric counterexample (a right ideal that is
   not a left one) would need the transpose witness and adds nothing,
   and the header says so rather than leaving a reader to wonder. 

   --------
   * * 单边理想不能生成一个商环

   Mac Lane，《为工作中的数学家准备的范畴》，第2版，§III.1
   练习 6（印刷第59页）  [maclane:III.1:ex6]：环的商是通过一个双边理想来取的。Instance/Rng/Quotient.v 文件包含了该构造，并解释了为何需要两个吸收律；该文件通过展示一个左理想，使得商关系对于乘法不是同余，证明了任何一个吸收律都不能被省略。这是 Instance/Grp/Quotient.v 的 [S3_refl_sub_not_normal] 的环级对应物，它反驳了某个子群的正规闭包条件。这里 [ut2_left_ideal_not_mul_congruence] 反驳了同余本身，这是 [rquot_rel_mul] 所建立的性质，也是构造实际使用的性质；[ut2_e11_not_right_absorbing] 单独反驳了被省略的闭包条件，因此两种情况都涵盖了。请精确阅读比较。一版早期的标题说环的陈述在形状上更强，因为群的部分把“因此商不会被良好定义”留给读者。那是错误的，审核发现了：群的部分已经带有同余级别的反驳，即 Instance/Grp/Congruence.v 中的 [S3_refl_sub_no_congruence] ——在相同子群上，由 #301 导出——所以那里也没有隐含的推理。实际上不同的是更狭窄的，这就是全部所声称的内容：这里的反驳是直接的，而群的反驳则是通过 [congruence_iff_normal] 获得的；并且它正好落在乘法同余上，这是单边性无法提供的条款。证据。[UT2]（Instance/Rng/Algebras/Associative.v）是上三角2×2整数矩阵的环，以三元组(a, b, c)表示，用于[[a, b], [0, c]，而且该文件证明它是非交换的（[UT2_not_commutative]）。它不是该树上唯一的非交换[RingObject]——Instance/Rng/MonoidRing.v的[zmring_not_commutative]展示了一个非交换的幺半群环，尽管它通过映射到[UT2]来证明——但它是最小的，并且其元素可计算，因为它们是整数三元组。左理想是ℤ·E₁₁，即矩阵单位E₁₁ = [[1, 0], [0, 0]的倍数：

   x · (a, 0, 0) = (a'·a, 0, 0)   —— 在左侧被吸收，
   (1, 0, 0) · (0, 1, 0) = (0, 1, 0)   —— 在右侧未被吸收。非交换性在这里不仅是方便的，它是必要的：在交换环上，两个吸收律是相同的表述，因此不可能存在交换的证据。这就是为什么这个文件必须引用 [UT2]，并且为什么它是一个单独的文件——Instance/Rng/Algebras/Associative.v 需要 Instance/Mod.v 和结合代数层次，而商环的使用者不应继承该依赖。未声明的内容。这里没有说一个左理想不会产生任何类型的商：特别是，ℤ·E₁₁ 是一个加法子群，因此 UT2/ℤ·E₁₁ 是一个完全良好的商阿贝尔群，且左模结构也依然存在。被驳斥的恰恰是环乘法能够下传。也没有提出右侧的对称情况：对称的反例（一 个不是左理想的右理想）需要转置的证据，并没有增加任何内容，标题也说明了这一点，而不是让读者自行猜测。
*)

(** ** ℤ·E₁₁ as a left ideal of UT2 / ** ℤ·E₁₁ 作为 UT2 的左理想 *)

Definition ut2_col1 (x : ut2) : Type := { a : Z & x = (a, 0, 0)%Z }.

Program Definition E11Left : LeftIdeal UT2 := {| lidl_mem := ut2_col1 |}.
Next Obligation.
  intros x y Hxy [a Ha]; unfold ut2_eqT in Hxy.
  exists a; now subst.
Qed.
Next Obligation. exists 0%Z; reflexivity. Qed.
Next Obligation.
  intros [[x1 x2] x3] [[y1 y2] y3] [a Ha] [b Hb].
  inversion Ha; inversion Hb; subst.
  exists (a + b)%Z.
  unfold rig_add, UT2, UT2_Rig, ut2_add; simpl.
  apply ut2_eq3; ring.
Qed.
Next Obligation.
  intros [[r1 r2] r3] [[x1 x2] x3] [a Ha].
  inversion Ha; subst.
  exists (r1 * a)%Z.
  unfold rig_mul, UT2, UT2_Rig, ut2_mul; simpl.
  apply ut2_eq3; ring.
Qed.

(* Non-vacuity of the left ideal itself: E₁₁ is in it and is not zero. / 左理想本身的非空性：E₁₁ 在其中且不为零。 *)
Theorem E11Left_nontrivial :
  lidl_mem E11Left ut2_e11 * (ut2_e11 = ut2_zero → False).
Proof.
  split.
  - exists 1%Z; reflexivity.
  - discriminate.
Qed.

(** ** It is NOT a right ideal / ** 这不是一个右理想 *)

(* E₁₁ · E₁₂ = E₁₂, which has a nonzero entry off the first column. / E₁₁ · E₁₂ = E₁₂，它在第一列之外有一个非零条目。 *)
Example ut2_e11_times_e12 : rig_mul UT2 ut2_e11 ut2_e12 = ut2_e12 := eq_refl.

Theorem ut2_e11_not_right_absorbing :
  lidl_mem E11Left (rig_mul UT2 ut2_e11 ut2_e12) → False.
Proof. intros [a Ha]; discriminate Ha. Qed.

(* So the fifth field of [Ideal] is not derivable from the other four: no [Ideal UT2] has [E11Left]'s membership predicate. / 所以 [Ideal] 的第五个字段不能从其他四个字段推导出来：没有 [Ideal UT2] 具有 [E11Left] 的成员谓词。 *)
Theorem E11Left_is_not_an_Ideal :
  { I : Ideal UT2 & ∀ x, idl_mem I x ↔ lidl_mem E11Left x } → False.
Proof.
  intros [I HI].
  apply ut2_e11_not_right_absorbing.
  apply (fst (HI _)).
  apply idl_absorb_r.
  apply (snd (HI _)).
  exists 1%Z; reflexivity.
Qed.

(*
   * ** ...and the quotient relation is not a congruence for
   multiplication

   The witnesses: E₁₁ ~ 0 (their difference is E₁₁, which is in the
   ideal) and E₁₂ ~ E₁₂, yet E₁₁·E₁₂ = E₁₂ is not congruent to
   0·E₁₂ = 0. 

   --------
   * **…而且商关系对于乘法不是合同关系

   证据：E₁₁ ~ 0（它们的差是 E₁₁，属于理想中）且 E₁₂ ~ E₁₂，但 E₁₁·E₁₂ = E₁₂ 并不与 0·E₁₂ = 0 同余。
*)

(*
 Since the PR “algebraic carriers are sets” (2026-09-17) [lquot_rel] is the
 propositional truncation of membership -- truncated in lockstep with
 [rquot_rel], so that [lquot_rel_is_rquot_rel] stays a convertibility -- so
 each witness is wrapped by [constructor] going in and unwrapped by an
 extra layer of intro pattern coming out.  The refutation is unaffected:
 its conclusion is [False], already a [Prop]. 

 --------
 自从 PR “代数承载体是集合”（2026-09-17）以来，[lquot_rel] 是成员资格的命题截断——与 [rquot_rel] 同步截断，因此 [lquot_rel_is_rquot_rel] 保持可转换性——所以每个证据都由 [constructor] 包装进入，并由额外一层引入模式解开。反驳没有受到影响：其结论是 [False]，已经是 [Prop]。
*)
Lemma ut2_e11_rel_zero : lquot_rel E11Left ut2_e11 ut2_zero.
Proof. constructor; exists 1%Z; reflexivity. Qed.

Lemma ut2_e12_rel_self : lquot_rel E11Left ut2_e12 ut2_e12.
Proof. constructor; exists 0%Z; reflexivity. Qed.

Theorem ut2_left_ideal_not_mul_congruence :
  LeftIdealMulCongruence E11Left → False.
Proof.
  intro Hcong.
  pose proof (Hcong ut2_e11 ut2_zero ut2_e12 ut2_e12
                ut2_e11_rel_zero ut2_e12_rel_self) as H.
  destruct H as [[a Ha]].
  discriminate Ha.
Qed.

(*
   * ** The positive half, at the same ring

   Every TWO-SIDED ideal of UT2 does give a congruence, so what the
   counterexample separates is the two-sidedness and not something about
   [UT2].  The strictly upper-triangular matrices are the witness: a
   two-sided ideal of UT2 that is proper and nontrivial, whose
   congruence is [ideal_mul_congruence] instantiated. 

   --------
   * ** 正半部分，在相同的环上

   UT2 的每一个双边理想确实都会产生一个合同，因此反例所区分的只是双边性，而不是关于 [UT2] 的某些内容。严格的上三角矩阵是证据：UT2 的一个双边理想，它是适当且非平凡的，其合同是 [ideal_mul_congruence] 的具体实例。
*)

Definition ut2_strict (x : ut2) : Type := { b : Z & x = (0, b, 0)%Z }.

Program Definition StrictUpper : Ideal UT2 := {| idl_mem := ut2_strict |}.
Next Obligation.
  intros x y Hxy [b Hb]; unfold ut2_eqT in Hxy.
  exists b; now subst.
Qed.
Next Obligation. exists 0%Z; reflexivity. Qed.
Next Obligation.
  intros [[x1 x2] x3] [[y1 y2] y3] [b Hb] [c Hc].
  inversion Hb; inversion Hc; subst.
  exists (b + c)%Z.
  unfold rig_add, UT2, UT2_Rig, ut2_add; simpl.
  apply ut2_eq3; ring.
Qed.
Next Obligation.
  intros [[r1 r2] r3] [[x1 x2] x3] [b Hb].
  inversion Hb; subst.
  exists (r1 * b)%Z.
  unfold rig_mul, UT2, UT2_Rig, ut2_mul; simpl.
  apply ut2_eq3; ring.
Qed.
Next Obligation.
  intros [[x1 x2] x3] [[r1 r2] r3] [b Hb].
  inversion Hb; subst.
  exists (b * r3)%Z.
  unfold rig_mul, UT2, UT2_Rig, ut2_mul; simpl.
  apply ut2_eq3; ring.
Qed.

Definition StrictUpper_congruence : IdealMulCongruence StrictUpper :=
  ideal_mul_congruence StrictUpper.

(* Proper: E₁₁ is not strictly upper triangular. / 正确：E₁₁ 不是严格的上三角矩阵。 *)
Theorem StrictUpper_proper : idl_mem StrictUpper ut2_e11 → False.
Proof. intros [b Hb]; discriminate Hb. Qed.

(* Nontrivial: E₁₂ is, and is not zero. / 非平凡的：E₁₂ 是零，也不是零。 *)
Theorem StrictUpper_nontrivial :
  idl_mem StrictUpper ut2_e12 * (ut2_e12 = ut2_zero → False).
Proof.
  split.
  - exists 1%Z; reflexivity.
  - discriminate.
Qed.

(*
 And the quotient by it does not collapse: E₁₁ stays apart from 0 in
 UT2/StrictUpper, so the two-sided construction is exercised on a
 nondegenerate non-commutative example and not only on ℤ. 

 --------
 并且通过它的商不会崩塌：E₁₁ 在 UT2/StrictUpper 中保持远离 0，因此双边构造是在一个非退化的非交换示例上进行的，而不仅仅是在 ℤ 上。
*)
Theorem UT2_mod_strict_not_collapsed :
  rquot_rel StrictUpper ut2_e11 ut2_zero → False.
Proof. intros [[b Hb]]; discriminate Hb. Qed.

Theorem UT2_mod_strict_collapses_e12 :
  rig_map (rquot_proj StrictUpper) ut2_e12
    ≈ rig_map (rquot_proj StrictUpper) ut2_zero.
Proof. constructor; exists 1%Z; reflexivity. Qed.

(* The quotient ring UT2/StrictUpper is not the zero ring. / 商环 UT2/StrictUpper 不是零环。 *)
Theorem UT2_mod_strict_nonzero :
  rig_one (QuotientRing StrictUpper) ≈ rig_zero (QuotientRing StrictUpper)
    → False.
Proof. intros [[b Hb]]; discriminate Hb. Qed.

(*
 It IS commutative, though UT2 is not -- the quotient of a
 non-commutative ring can be commutative, which is why “quotient” here
 is a genuine construction and not a relabelling.  On the nose: the
 two products differ only in the middle entry, which the ideal
 kills. 

 --------
 它确实是交换的，虽然 UT2 不是——非交换环的商可以是交换的，这就是为什么这里的“商”是一个真正的构造，而不是简单的重新命名。准确来说：这两个乘积只在中间的项上不同，而这个项被理想消掉了。
*)
Theorem UT2_mod_strict_commutative :
  ∀ x y : carrier (rig_setoid (QuotientRing StrictUpper)),
    rig_mul (QuotientRing StrictUpper) x y
      ≈ rig_mul (QuotientRing StrictUpper) y x.
Proof.
  intros [[x1 x2] x3] [[y1 y2] y3].
  constructor.
  exists (x1 * y2 + x2 * y3 - (y1 * x2 + y2 * x3))%Z.
  unfold rig_mul, UT2, UT2_Rig, ut2_mul; simpl.
  apply ut2_eq3; ring.
Qed.
