(* * * Character groups and the double-dual evaluation / * * 字符组与双重-双重评估 *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qreduction.

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 §I.4, printed p. 17 (PDF 27) — maclane:I.4:construction3
 (the finite-iso and non-naturality halves are
 Instance/Ab/Character/Finite.v's and NonNatural.v's)
 nLab:      https://ncatlab.org/nlab/show/Pontryagin+duality
 Wikipedia: https://en.wikipedia.org/wiki/Pontryagin_duality

 Mac Lane's §I.4 example: the character group D(G) = hom(G, ℚ/ℤ) is
 contravariant in G, its square DD is a covariant endofunctor of Ab,
 and the evaluation family τ_G : G → DD(G), a ↦ (χ ↦ χ a), is
 natural in G — his second worked example of a natural
 transformation.  This file delivers the dualizing group, both
 functors, and the natural evaluation; the finite-iso theorem and
 the non-naturality remark live in the sibling files.

 - [QZ]: the circle group ℚ/ℤ as an [AbObject] — carrier ℚ,
 identified up to integer difference, with decidable ≈
 - [D_ob]/[D]: the character group and the contravariant functor
 [D : Ab^op ⟶ Ab], acting by precomposition
 - [DD]: the covariant double dual, defined directly (its action
 Ξ ↦ (χ ↦ Ξ (χ ∘ f)) makes the two flips visible)
 - [tau]/[tau_natural]/[tau_Transform]: the evaluation family and
 its naturality square, packaged as [Id ⟹ DD]

 Design:

 1. ℚ/ℤ, NOT ℝ/ℤ, AND WHY THAT IS FAITHFUL.  The book's dualizing
 group is the circle ℝ/ℤ; every character of a FINITE group
 lands in its torsion subgroup, which is exactly ℚ/ℤ, so on the
 finite abelian groups of the example the two dualizing choices
 agree.  ℚ/ℤ is chosen because the stdlib rationals are
 axiom-free while the reals import classical axioms
 (docs/AXIOMS.md) — the issue's disclosed restriction.
 CORRECTION (#410): the standard library's classical reals [R]
 do; its constructive Cauchy reals [CReal] do not, and over them
 Instance/Top/Solenoid/Presentations.v builds ℝ/ℤ as an abelian
 group, [CircleGroup], closed under the global context.  Nothing
 here is rebuilt on it: ℚ/ℤ stays this file's dualizing group.

 2. THE QUOTIENT IS A SETOID, AND IT IS DECIDABLE.  A point of ℚ/ℤ
 is a rational; two are identified when they differ by an
 integer.  No quotient construction is needed — the setoid
 discipline IS the quotient — and the relation is decidable
 ([qz_dec]): x − y is an integer exactly when its [Qred]
 canonical form has denominator 1, by [Qred]'s completeness.
 Decidability is not consumed here, but the finite half of the
 development counts characters, and counting needs it.

 3. CHARACTERS FORM AN ABELIAN GROUP POINTWISE.  D(G) carries the
 hom-set [AbHom G QZ] with pointwise addition, zero, and
 negation; the hom-setoid is [CMonHom_Setoid]'s pointwise
 equality, reused rather than rebuilt.  [D] acts by
 precomposition; [DD] is defined directly rather than as a
 composite through [Ab^op], so its object and arrow actions
 unfold definitionally in the evaluation's naturality square. 

 --------
 书籍：      Mac Lane，《Categories for the Working Mathematician》，第二版，
 §I.4，第17页印刷版（PDF第27页）—— maclane:I.4:construction3
 （有限同构与非自然性部分分别在 Instance/Ab/Character/Finite.v 和 NonNatural.v 中）
 nLab：     https://ncatlab.org/nlab/show/Pontryagin+duality 
 维基百科：  https://en.wikipedia.org/wiki/Pontryagin_duality 

 Mac Lane §I.4 的例子：特征群 D(G) = hom(G, ℚ/ℤ) 在 G 上是对变的，其平方 DD 是 Ab 的协变自函子，而评估族 τ_G : G → DD(G), a ↦ (χ ↦ χ a)，在 G 上是自然的——这是他第二个关于自然变换的详细例子。该文件提供了对偶化群、两个函子以及自然评估；有限同构定理和非自然性备注则存在于相关的其他文件中。-  [QZ]：作为 [AbObject] 的圆群 ℚ/ℤ — 携带者 ℚ，
 在整数差下识别，其 ≈ 可判定
 -  [D_ob] / [D]：字符群和逆变函子
 [D : Ab^op ⟶ Ab]，通过前组合作用
 -  [DD]：协变双重对偶，直接定义（其作用
 Ξ ↦ (χ ↦ Ξ (χ ∘ f)) 显示了两个翻转）
 -  [tau] / [tau_natural] / [tau_Transform]：评估族及其自然性方阵，打包为 [Id ⟹ DD] 

 设计：1. ℚ/ℤ，而不是 ℝ/ℤ，以及为什么它是忠实的。 这本书的对偶化群是圆 ℝ/ℤ；每个有限群的特征值都会落在它的挠子群中，而这正是 ℚ/ℤ，因此在例子中的有限阿贝尔群上，这两个对偶化选择是一致的。选择 ℚ/ℤ 是因为标准库的有理数是不依赖公理的，而实数则引入了经典公理（docs/AXIOMS.md）——这是问题披露的限制。更正 (#410)：标准库的经典实数 [R] 是依赖公理的；其构造性的柯西实数 [CReal] 则不依赖，并且在它们上面，Instance/Top/Solenoid/Presentations.v 将 ℝ/ℤ 构建为一个阿贝尔群 [CircleGroup]，在全局上下文中是封闭的。这里没有任何内容是基于它重新构建的：ℚ/ℤ 仍然是本文件的对偶化群。2. 商集是一个集合同构，并且它是可判定的。 ℚ/ℤ 的一个点是一个有理数；当两个有理数相差一个整数时，它们被认为是相同的。无需构造商集——集合同构的规则本身就是商集——并且该关系是可判定的（[qz_dec]）：当 x − y 的标准形式的分母为 1 时，它恰好是一个整数，根据 [Qred] 的完备性。可判定性在这里不会被消耗，但开发过程中有限的一部分需要计算字符，而计数需要可判定性。3. 字符在每一点上形成阿贝尔群。D(G) 通过每一点的加法、零元素和取负运算承载同态集合 [AbHom G QZ]；同态集合的等价关系是 [CMonHom_Setoid] 的逐点相等关系，重用而不是重新构建。[D] 通过前合成作用；[DD] 是直接定义的，而不是通过 [Ab^op] 的复合定义，因此它的对象和箭头作用在评估的自然性方格中按定义展开。
*)

(** ** The circle group ℚ/ℤ / ** 圈群 ℚ/ℤ *)

(* x and y are identified when they differ by an integer. / 当 x 和 y 相差一个整数时，它们被认为是相同的。 *)
Definition qz_eq (x y : Q) : Type := { z : Z & x - y == inject_Z z }.

Lemma qz_eq_refl (x : Q) : qz_eq x x.
Proof. exists 0%Z; ring. Qed.

Lemma qz_eq_sym (x y : Q) : qz_eq x y → qz_eq y x.
Proof.
  intros [z Hz]; exists (- z)%Z.
  rewrite inject_Z_opp.
  rewrite <- Hz; ring.
Qed.

Lemma qz_eq_trans (x y w : Q) : qz_eq x y → qz_eq y w → qz_eq x w.
Proof.
  intros [z1 H1] [z2 H2]; exists (z1 + z2)%Z.
  rewrite inject_Z_plus.
  rewrite <- H1, <- H2; ring.
Qed.

(* Qeq is a special case (difference zero). / Qeq 是一个特殊情况（差值为零）。 *)
Lemma qz_of_Qeq (x y : Q) : x == y → qz_eq x y.
Proof.
  intro H; exists 0%Z.
  rewrite H; ring.
Qed.

(* The canonical form of an integer has denominator 1, by the ggcd specification (gcd with 1 is 1). / 根据 ggcd 规范（与 1 的最大公约数是 1），整数的标准形式的分母为 1。 *)
Lemma Qred_inject_Z_den (z : Z) : Qden (Qred (inject_Z z)) = 1%positive.
Proof.
  unfold Qred, inject_Z; simpl.
  pose proof (Z.ggcd_gcd z 1) as Hg.
  pose proof (Z.ggcd_correct_divisors z 1) as Hd.
  destruct (Z.ggcd z 1) as [g [aa bb]]; simpl in *.
  destruct Hd as [Ha Hb].
  rewrite Z.gcd_1_r in Hg; subst g.
  rewrite Z.mul_1_l in Hb; subst bb.
  reflexivity.
Qed.

(* Decidability: the canonical form of an integer has denominator 1. / 可判定性：一个整数的标准形式分母为 1。 *)
Lemma qz_eq_dec (x y : Q) : qz_eq x y + (qz_eq x y → False).
Proof.
  destruct (Pos.eq_dec (Qden (Qred (x - y))) 1%positive) as [He|He].
  - left.
    destruct (Qred (x - y)) as [n d] eqn:Er.
    simpl in He; subst d.
    exists n.
    pose proof (Qred_correct (x - y)) as Hc.
    rewrite Er in Hc.
    unfold inject_Z.
    apply Qeq_sym; exact Hc.
  - right.
    intros [z Hz].
    apply He.
    rewrite (Qred_complete _ _ Hz).
    apply Qred_inject_Z_den.
Qed.

(*
 The setoid is NAMED, and so is its [Prop] mirror, because since the PR
 “algebraic carriers are sets” (2026-09-17) the [AbObject] below owes a
 [cmon_prop] and a field of a [Program] record literal cannot mention a
 setoid that is still an evar while the literal is being elaborated. 

 --------
 这个集合体被命名了，它的 [Prop] 镜像也是如此，因为自从 PR“代数载体是集合”（2026-09-17）以来，下面的 [AbObject] 需要一个 [cmon_prop]，而 [Program] 记录字面量的字段在被展开时不能引用仍然是 evar 的集合体。
*)
Program Definition qz_setoid : Setoid Q := {| equiv := qz_eq |}.
Next Obligation.
  constructor.
  - exact qz_eq_refl.
  - exact qz_eq_sym.
  - exact qz_eq_trans.
Qed.

(*
 [qz_eq] KEEPS its [sigT]: the integer witness is computed, not chosen, and
 several results below read it back out.  What the [PropEquiv] adds is a
 [Prop] relation that holds exactly when [qz_eq] does -- and the implication
 BACK into [qz_eq], which is an elimination of a [Prop] into a [Type], goes
 through the DECISION PROCEDURE [qz_eq_dec] above rather than through the
 [Prop] proof: the left branch supplies the witness outright, and the right
 branch contradicts the hypothesis.  No choice principle is consumed. 

 --------
 [qz_eq] 保持其 [sigT]：整数见证是计算出来的，而不是选择的，下面的几个结果会读回它。[PropEquiv] 添加的是一个 [Prop] 关系，只有当 [qz_eq] 成立时才成立 —— 并且回到 [qz_eq] 的蕴含，这是将 [Prop] 消去到 [Type]，通过上述决策程序 [qz_eq_dec]，而不是通过 [Prop] 证明：左分支直接提供见证，右分支与假设矛盾。没有使用选择原理。
*)
Definition qz_peq (x y : Q) : Prop :=
  (exists z : Z, Qeq (Qminus x y) (inject_Z z))%type.

Definition qz_PropEquiv : PropEquiv qz_setoid.
Proof.
  unshelve refine (@PropEquiv_of_relation _ qz_setoid qz_peq _ _).
  - intros x y H.
    destruct (qz_eq_dec x y) as [Hd|Hd].
    + exact Hd.
    + exfalso.
      destruct H as [z Hz].
      exact (Hd (existT _ z Hz)).
  - intros x y H.
    destruct H as [z Hz].
    exists z.
    exact Hz.
Defined.

(*
 The circle as an abelian group object: ℚ with the integer-difference
 setoid, addition, and negation. 

 --------
 作为阿贝尔群对象的圆：ℚ 配整数差集合、加法和取反。
*)
Program Definition QZ : AbObject := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := Q;
                      is_setoid := qz_setoid |};
    cmon_zero := 0;
    cmon_plus := Qplus;
    cmon_prop := qz_PropEquiv
  |};
  ab_neg := Qopp
|}.
Next Obligation.
  intros x x' [z1 H1] y y' [z2 H2].
  exists (z1 + z2)%Z.
  rewrite inject_Z_plus.
  rewrite <- H1, <- H2; ring.
Qed.
Next Obligation.
  intros a b c; apply qz_of_Qeq; cbn; ring.
Qed.
Next Obligation.
  intros a b; apply qz_of_Qeq; cbn; ring.
Qed.
Next Obligation.
  intro a; apply qz_of_Qeq; cbn; ring.
Qed.
Next Obligation.
  intros x y [z Hz].
  exists (- z)%Z.
  rewrite inject_Z_opp.
  rewrite <- Hz; ring.
Qed.
Next Obligation.
  intro a; apply qz_of_Qeq; cbn; ring.
Qed.

(** ** The character group / ** 字符组 *)

(* The zero character. / 零字符。 *)
Program Definition char_zero (G : AbObject) : AbHom G QZ := {|
  cmon_map := {| morphism := fun _ => 0 |}
|}.
Next Obligation.
  intros G x y H; apply qz_eq_refl.
Qed.
Next Obligation.
  intros G; apply qz_eq_refl.
Qed.
Next Obligation.
  intros G a b; apply qz_of_Qeq; cbn; ring.
Qed.

(* Pointwise sum of characters. / 字符的逐点求和。 *)
Program Definition char_plus (G : AbObject) (χ ψ : AbHom G QZ) :
  AbHom G QZ := {|
  cmon_map := {| morphism := fun a => cmon_map χ a + cmon_map ψ a |}
|}.
Next Obligation.
  intros G χ ψ x y H.
  apply QZ.(ab_cmon).(cmon_plus_respects);
    apply (proper_morphism (cmon_map _)); exact H.
Qed.
Next Obligation.
  intros G χ ψ.
  eapply qz_eq_trans.
  - apply QZ.(ab_cmon).(cmon_plus_respects);
      [ apply (cmon_map_zero χ) | apply (cmon_map_zero ψ) ].
  - apply qz_of_Qeq; cbn; ring.
Qed.
Next Obligation.
  intros G χ ψ a b.
  eapply qz_eq_trans.
  - apply QZ.(ab_cmon).(cmon_plus_respects);
      [ apply (cmon_map_plus χ) | apply (cmon_map_plus ψ) ].
  - apply qz_of_Qeq; cbn; ring.
Qed.

(*
 Pointwise negation of a character (a homomorphism because negation
 in ℚ/ℤ is additive). 

 --------
 字符的逐点取反（是一个同态，因为在 ℚ/ℤ 中取反是可加的）。
*)
Program Definition char_neg (G : AbObject) (χ : AbHom G QZ) :
  AbHom G QZ := {|
  cmon_map := {| morphism := fun a => - cmon_map χ a |}
|}.
Next Obligation.
  intros G χ x y H.
  apply QZ.(ab_neg_respects).
  apply (proper_morphism (cmon_map _)); exact H.
Qed.
Next Obligation.
  intros G χ.
  eapply qz_eq_trans.
  - apply QZ.(ab_neg_respects), (cmon_map_zero χ).
  - apply qz_of_Qeq; cbn; ring.
Qed.
Next Obligation.
  intros G χ a b.
  eapply qz_eq_trans.
  - apply QZ.(ab_neg_respects), (cmon_map_plus χ).
  - apply qz_of_Qeq; cbn; ring.
Qed.

(* The character group D(G) = hom(G, ℚ/ℤ), pointwise. / 群 D(G) = hom(G, ℚ/ℤ)，逐点。 *)
Program Definition D_ob (G : AbObject) : AbObject := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := AbHom G QZ;
                      is_setoid := @CMonHom_Setoid G QZ |};
    cmon_zero := char_zero G;
    cmon_plus := char_plus G;
    cmon_prop := @CMonHom_PropEquiv G QZ
  |};
  ab_neg := char_neg G
|}.
Next Obligation.
  intros G χ χ' Hχ ψ ψ' Hψ a; simpl.
  apply QZ.(ab_cmon).(cmon_plus_respects); [ exact (Hχ a) | exact (Hψ a) ].
Qed.
Next Obligation.
  intros G χ ψ ρ a; simpl.
  apply qz_of_Qeq; cbn; ring.
Qed.
Next Obligation.
  intros G χ ψ a; simpl.
  apply qz_of_Qeq; cbn; ring.
Qed.
Next Obligation.
  intros G χ a; simpl.
  apply qz_of_Qeq; cbn; ring.
Qed.
Next Obligation.
  intros G χ χ' Hχ a; simpl.
  apply QZ.(ab_neg_respects); exact (Hχ a).
Qed.
Next Obligation.
  intros G χ a; simpl.
  apply qz_of_Qeq; cbn; ring.
Qed.

(* * ** The contravariant character functor / * ** 逆变范畴函子 *)

(*
 Precomposition: a homomorphism f : H → G pulls characters of G back
 to characters of H. 

 --------
 预组合：同态 f : H → G 将 G 的特征映射拉回到 H 的特征。
*)
Program Definition char_precomp {G H : AbObject} (f : AbHom H G)
        (χ : AbHom G QZ) : AbHom H QZ := {|
  cmon_map := {| morphism := fun a => cmon_map χ (cmon_map f a) |}
|}.
Next Obligation.
  intros G H f χ x y Hxy.
  apply (proper_morphism (cmon_map χ)).
  apply (proper_morphism (cmon_map f)); exact Hxy.
Qed.
Next Obligation.
  intros G H f χ.
  eapply qz_eq_trans.
  - apply (proper_morphism (cmon_map χ)), (cmon_map_zero f).
  - apply (cmon_map_zero χ).
Qed.
Next Obligation.
  intros G H f χ a b.
  eapply qz_eq_trans.
  - apply (proper_morphism (cmon_map χ)), (cmon_map_plus f).
  - apply (cmon_map_plus χ).
Qed.

(* D : Ab^op ⟶ Ab, the contravariant character functor. / D ：Ab^op ⟶ Ab，对应的反变特征函子。 *)
Program Definition D : Ab^op ⟶ Ab := {|
  fobj := fun G => D_ob G;
  fmap := fun G H (f : G ~{Ab^op}~> H) =>
    {| cmon_map := {| morphism := fun χ => char_precomp f χ |} |}
|}.
Next Obligation.
  intros G H f χ ψ Hχψ a; simpl.
  exact (Hχψ (cmon_map f a)).
Qed.
Next Obligation.
  intros G H f a; simpl.
  apply qz_eq_refl.
Qed.
Next Obligation.
  intros G H f χ ψ a; simpl.
  apply qz_eq_refl.
Qed.
Next Obligation.
  intros G H f g Hfg χ a; simpl.
  apply (proper_morphism (cmon_map χ)).
  exact (Hfg a).
Qed.
Next Obligation.
  intros G χ a; simpl.
  apply qz_eq_refl.
Qed.
Next Obligation.
  intros G H K f g χ a; simpl.
  apply qz_eq_refl.
Qed.

(** ** The covariant double dual / ** 协变双重对偶 *)

(*
 Evaluation-style action: Ξ ↦ (χ ↦ Ξ (χ ∘ f)).  Defined directly so
 both flips are visible and everything unfolds in the naturality
 square. 

 --------
 评价风格的操作：Ξ ↦ (χ ↦ Ξ (χ ∘ f))。直接定义，因此两个翻转都可见，并且一切在自然性方格中展开。
*)
Program Definition DD : Ab ⟶ Ab := {|
  fobj := fun G => D_ob (D_ob G);
  fmap := fun G H (f : G ~{Ab}~> H) =>
    {| cmon_map := {| morphism := fun Ξ =>
      {| cmon_map := {| morphism := fun χ : AbHom H QZ =>
           cmon_map Ξ (char_precomp f χ) |} |} |} |}
|}.
Next Obligation.
  intros G H f Ξ χ ψ Hχψ; simpl.
  apply (proper_morphism (cmon_map Ξ)).
  intro a; simpl.
  exact (Hχψ (cmon_map f a)).
Qed.
Next Obligation.
  intros G H f Ξ; simpl.
  eapply qz_eq_trans; [ | apply (cmon_map_zero Ξ) ].
  apply (proper_morphism (cmon_map Ξ)).
  intro a; simpl.
  apply qz_eq_refl.
Qed.
Next Obligation.
  intros G H f Ξ χ ψ; simpl.
  eapply qz_eq_trans; [ | apply (cmon_map_plus Ξ) ].
  apply (proper_morphism (cmon_map Ξ)).
  intro a; simpl.
  apply qz_eq_refl.
Qed.
Next Obligation.
  intros G H f Ξ Θ HΞΘ χ; simpl.
  exact (HΞΘ (char_precomp f χ)).
Qed.
Next Obligation.
  intros G H f χ; simpl.
  apply qz_eq_refl.
Qed.
Next Obligation.
  intros G H f Ξ Θ χ; simpl.
  apply qz_eq_refl.
Qed.
Next Obligation.
  intros G H f g Hfg Ξ χ; simpl.
  apply (proper_morphism (cmon_map Ξ)).
  intro a; simpl.
  apply (proper_morphism (cmon_map χ)).
  exact (Hfg a).
Qed.
Next Obligation.
  intros G Ξ χ; simpl.
  apply (proper_morphism (cmon_map Ξ)).
  intro a; simpl.
  apply qz_eq_refl.
Qed.
Next Obligation.
  intros G H K f g Ξ χ; simpl.
  apply (proper_morphism (cmon_map Ξ)).
  intro a; simpl.
  apply qz_eq_refl.
Qed.

(** ** The natural evaluation / ** 自然评估 *)

(* The evaluation character of an element: χ ↦ χ a. / 一个元素的评估特征：χ ↦ χ a。 *)
Program Definition tau_component {G : AbObject} (a : carrier (cmon_setoid G)) :
  AbHom (D_ob G) QZ := {|
  cmon_map := {| morphism := fun χ : AbHom G QZ => cmon_map χ a |}
|}.
Next Obligation.
  intros G a χ ψ Hχψ.
  exact (Hχψ a).
Qed.
Next Obligation.
  intros G a; simpl.
  apply qz_eq_refl.
Qed.
Next Obligation.
  intros G a χ ψ; simpl.
  apply qz_eq_refl.
Qed.

(* τ_G : G → DD(G), a ↦ (χ ↦ χ a). *)
Program Definition tau (G : AbObject) : G ~{Ab}~> DD G := {|
  cmon_map := {| morphism := fun a => tau_component a |}
|}.
Next Obligation.
  intros G x y Hxy χ; simpl.
  apply (proper_morphism (cmon_map χ)); exact Hxy.
Qed.
Next Obligation.
  intros G χ; simpl.
  apply (cmon_map_zero χ).
Qed.
Next Obligation.
  intros G a b χ; simpl.
  apply (cmon_map_plus χ).
Qed.

(* Mac Lane's naturality square: DD f ∘ τ_G ≈ τ_H ∘ f. / 麦克莱恩的自然性方格：DD f ∘ τ_G ≈ τ_H ∘ f。 *)
Lemma tau_natural {G H : AbObject} (f : G ~{Ab}~> H) :
  fmap[DD] f ∘ tau G ≈ tau H ∘ f.
Proof.
  intros a χ; simpl.
  apply qz_eq_refl.
Qed.

(*
 The evaluation family packaged as a natural transformation
 Id ⟹ DD. 

 --------
 作为自然变换封装的评估族 Id ⟹ DD。
*)
Program Definition tau_Transform : Id[Ab] ⟹ DD := {|
  transform := tau
|}.
Next Obligation.
  intros G H f a χ; simpl.
  apply qz_eq_refl.
Qed.
Next Obligation.
  intros G H f a χ; simpl.
  apply qz_eq_refl.
Qed.
