Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.

Generalizable All Variables.

(*
   * * Subtraction in an abelian group

   Instance/Ab.v carries [ab_neg_right], [ab_cancel_l], [ab_neg_unique],
   [ab_neg_zero], [ab_neg_plus] and [ab_map_neg], but no SUBTRACTION and
   no involutivity of negation.  Both quotient constructions that follow
   -- Instance/Mod/Quotient.v's quotient by a submodule and
   Instance/Rng/Quotient.v's quotient by a two-sided ideal -- are
   defined by the relation “x - y lies in the sub-thing”, so both need
   the same dozen shuffles, and this file is where they live so that
   neither restates them and no ring file has to depend on a module
   file to get them.

   Nothing here mentions a scalar action or a multiplication: it is
   stated over [AbObject] and applies at [Ab], at [RMod R] through the
   [rm_ab] coercion, and at the additive group [ring_ab R] of a ring.

   THIS FILE IS AN UPSTREAMING STAGING POST, and says so rather than
   pretending to be the first word.  [ab_neg_invol] is the THIRD copy of
   ELEMENT-LEVEL negation-involutivity in the tree (the qualifier is
   load-bearing: Structure/AbCategory.v's [abneg_invol] is a fourth
   involutivity, but of the negation on the HOM-GROUPS of an
   Ab-enriched category, not on the elements of an [AbObject]):
   Instance/Rep.v has it as [ab_neg_neg]
   with this exact statement (that file's own header calls it an
   upstreaming candidate for Instance/Ab.v), and Instance/Rng.v has
   [ring_neg_involutive] for the additive group of a ring.  The name
   differs from Rep.v's deliberately, so that a file importing both does
   not shadow.  The right fix is to move the whole block into
   Instance/Ab.v and delete the other two; that is not done here because
   Instance/Ab.v sits under [Rng], [Mod] and much else, and the rebuild
   is not this issue's to spend. 

   --------
   * * 阿贝尔群中的减法

   Instance/Ab.v 包含 [ab_neg_right]、[ab_cancel_l]、[ab_neg_unique]、
   [ab_neg_zero]、[ab_neg_plus] 和 [ab_map_neg]，但没有减法也没有取负的自反性。接下来的两个商构造——Instance/Mod/Quotient.v 中的子模的商和 Instance/Rng/Quotient.v 中的双边理想的商——都是由关系“x - y 属于子结构”定义的，因此都需要相同的一打变换，这个文件就是它们所在的地方，这样它们都不需要重复定义，且任何环文件也不必依赖模块文件来获得这些定义。

   这里没有提到标量作用或乘法：它是在 [AbObject] 上陈述的，并适用于 [Ab]、通过 [RMod R] 到 [rm_ab] 的强制转换，以及环的加法群 [ring_ab R] 上。此文件是一个上游阶段性发布，并且如此声明，而不是假装是第一个词。[ab_neg_invol] 是树中元素级否定-自反性的第三个副本（限定符是承重的：Structure/AbCategory.v 的 [abneg_invol] 是第四个自反性，但它是针对 Ab 丰富范畴的 HOM-GROUPS 的否定，而不是针对 [AbObject] 元素的）：Instance/Rep.v 将其定义为 [ab_neg_neg]，并带有完全相同的声明（该文件自己的标题称它是 Instance/Ab.v 的上游候选文件），而 Instance/Rng.v 对环的加法群定义了 [ring_neg_involutive]。名称故意不同于 Rep.v，以便一个导入两者的文件不会发生遮蔽。正确的解决方法是将整个块移到 Instance/Ab.v 并删除另外两个；这里没有这样做，因为 Instance/Ab.v 位于 [Rng]、[Mod] 以及其他许多内容之下，而且重建并不是这个问题需要花费的。
*)

Definition ab_sub (A : AbObject) (x y : carrier (cmon_setoid A)) :
  carrier (cmon_setoid A) := cmon_plus A x (ab_neg A y).

#[export] Instance ab_sub_respects (A : AbObject) :
  Proper (equiv ==> equiv ==> equiv) (ab_sub A).
Proof.
  intros x x' Hx y y' Hy; unfold ab_sub.
  now rewrite Hx, Hy.
Qed.

Lemma ab_neg_invol (A : AbObject) (a : carrier (cmon_setoid A)) :
  ab_neg A (ab_neg A a) ≈ a.
Proof.
  symmetry; apply ab_neg_unique.
  apply ab_neg_right.
Qed.

Lemma ab_sub_self (A : AbObject) (x : carrier (cmon_setoid A)) :
  ab_sub A x x ≈ cmon_zero A.
Proof. apply ab_neg_right. Qed.

Lemma ab_sub_zero_r (A : AbObject) (x : carrier (cmon_setoid A)) :
  ab_sub A x (cmon_zero A) ≈ x.
Proof.
  unfold ab_sub.
  rewrite ab_neg_zero.
  apply cmon_plus_zero_r.
Qed.

Lemma ab_sub_zero_l (A : AbObject) (x : carrier (cmon_setoid A)) :
  ab_sub A (cmon_zero A) x ≈ ab_neg A x.
Proof. unfold ab_sub; apply cmon_plus_zero_l. Qed.

(* -(x - y) ≈ y - x, proved through [ab_neg_unique] so that involutivity is not needed for THIS one. / -(x - y) ≈ y - x，通过[ab_neg_unique]证明，因此对于这个不需要自反性。 *)
Lemma ab_sub_neg (A : AbObject) (x y : carrier (cmon_setoid A)) :
  ab_neg A (ab_sub A x y) ≈ ab_sub A y x.
Proof.
  symmetry; apply ab_neg_unique.
  unfold ab_sub.
  rewrite !cmon_plus_assoc.
  rewrite <- (cmon_plus_assoc A (ab_neg A x) x (ab_neg A y)).
  rewrite ab_neg_left, cmon_plus_zero_l.
  apply ab_neg_right.
Qed.

(* (-x) - (-y) ≈ y - x. *)
Lemma ab_sub_neg_neg (A : AbObject) (x y : carrier (cmon_setoid A)) :
  ab_sub A (ab_neg A x) (ab_neg A y) ≈ ab_sub A y x.
Proof.
  unfold ab_sub.
  rewrite (ab_neg_invol A y).
  apply cmon_plus_comm.
Qed.

(* (x - y) + (y - z) ≈ x - z: the transitivity computation. / (x - y) + (y - z) ≈ x - z：传递性计算。 *)
Lemma ab_sub_trans (A : AbObject) (x y z : carrier (cmon_setoid A)) :
  cmon_plus A (ab_sub A x y) (ab_sub A y z) ≈ ab_sub A x z.
Proof.
  unfold ab_sub.
  rewrite cmon_plus_assoc.
  rewrite <- (cmon_plus_assoc A (ab_neg A y) y (ab_neg A z)).
  rewrite ab_neg_left, cmon_plus_zero_l.
  reflexivity.
Qed.

(*
 (x - y) + (u - v) ≈ (x + u) - (y + v).  THIS is the step that
 COMMUTATIVITY buys, and it is the additive counterpart of the
 conjugation shuffle in [quot_rel_mul] (Instance/Grp/Quotient.v), which
 in the group case is where normality is spent. 

 --------
 (x - y) + (u - v) ≈ (x + u) - (y + v)。这就是**交换律**带来的步骤，它是 [quot_rel_mul]（Instance/Grp/Quotient.v）中**共轭变换洗牌**的加法对应物，在群的情况下，这就是消耗**正规性**的地方。
*)
Lemma ab_sub_plus (A : AbObject) (x y u v : carrier (cmon_setoid A)) :
  cmon_plus A (ab_sub A x y) (ab_sub A u v)
    ≈ ab_sub A (cmon_plus A x u) (cmon_plus A y v).
Proof.
  unfold ab_sub.
  rewrite ab_neg_plus.
  rewrite !cmon_plus_assoc.
  apply cmon_plus_respects; [ reflexivity |].
  rewrite <- !cmon_plus_assoc.
  apply cmon_plus_respects; [| reflexivity ].
  apply cmon_plus_comm.
Qed.

(* (x + y) - x ≈ y and y + (x - y) ≈ x: the two cancellations. / (x + y) - x ≈ y 和 y + (x - y) ≈ x：这两种抵消。 *)
Lemma ab_sub_add_cancel (A : AbObject) (x y : carrier (cmon_setoid A)) :
  ab_sub A (cmon_plus A x y) x ≈ y.
Proof.
  unfold ab_sub.
  rewrite (cmon_plus_comm A x y).
  rewrite cmon_plus_assoc.
  rewrite ab_neg_right.
  apply cmon_plus_zero_r.
Qed.

Lemma ab_add_sub_cancel (A : AbObject) (x y : carrier (cmon_setoid A)) :
  cmon_plus A y (ab_sub A x y) ≈ x.
Proof.
  unfold ab_sub.
  rewrite <- cmon_plus_assoc.
  rewrite (cmon_plus_comm A y x).
  rewrite cmon_plus_assoc.
  rewrite ab_neg_right.
  apply cmon_plus_zero_r.
Qed.

(* x - y ≈ 0 exactly when x ≈ y. / 当且仅当 x ≈ y 时，x - y ≈ 0。 *)
Lemma ab_sub_eq_zero_iff (A : AbObject) (x y : carrier (cmon_setoid A)) :
  ab_sub A x y ≈ cmon_zero A ↔ x ≈ y.
Proof.
  split.
  - intro H.
    apply (ab_cancel_l A (ab_neg A y)).
    rewrite (ab_neg_left A y).
    rewrite (cmon_plus_comm A (ab_neg A y) x).
    exact H.
  - intro H; rewrite H; apply ab_sub_self.
Qed.

Lemma ab_map_sub {A B : AbObject} (f : AbHom A B)
  (x y : carrier (cmon_setoid A)) :
  cmon_map f (ab_sub A x y) ≈ ab_sub B (cmon_map f x) (cmon_map f y).
Proof.
  unfold ab_sub.
  rewrite cmon_map_plus.
  now rewrite ab_map_neg.
Qed.
