Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.
Require Import Category.Theory.Algebra.CommutativeFrobenius.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Structure.Monoidal.Hypergraph.Spider.

Generalizable All Variables.

(*
   * * Hint database for hypergraph-level rewrites

   Bundles the simplification-direction (LHS more complex than RHS)
   spider lemmas into a single [hypergraph] hint database.

   Downstream code can write

   autorewrite with hypergraph.

   to apply all of these rewrites until fixpoint.  Combined with
   [autorewrite with categories] and the library's [cat] tactic, this
   gives a fast path for closing routine SCFA-algebra goals.

   Bidirectional lemmas — [spider_mu_assoc], [spider_delta_coassoc],
   [spider_frobenius], [spider_frobenius_sym], [spider_2_to_2],
   [spider_3_to_1], [spider_1_to_3] — are NOT in this database because
   [autorewrite] would loop on them.  Use them manually with
   [rewrite].

   The lemmas registered here are exactly:

   spider_collapse              μ ∘ δ ≈ id
   spider_mu_unit_left          μ ∘ bimap η id ≈ to unit_left
   spider_mu_unit_right         μ ∘ bimap id η ≈ to unit_right
   spider_delta_counit_left     bimap ε id ∘ δ ≈ from unit_left
   spider_delta_counit_right    bimap id ε ∘ δ ≈ from unit_right
   spider_mu_commutative        μ ∘ braid ≈ μ
   spider_delta_cocommutative   braid ∘ δ ≈ δ

   --------
   * * 用于超图级重写的提示数据库

   将简化方向（左侧比右侧复杂）
   的 spider 引理捆绑到一个单独的 [hypergraph] 提示数据库中。

   下游代码可以写

   autorewrite with hypergraph.

   来应用所有这些重写直到固定点。结合
   [autorewrite with categories] 和库中的 [cat] 策略，这
   提供了一个快速路径来完成常规 SCFA-代数目标。

   双向引理 — [spider_mu_assoc], [spider_delta_coassoc],
   [spider_frobenius], [spider_frobenius_sym], [spider_2_to_2],
   [spider_3_to_1], [spider_1_to_3] — 不在此数据库中，因为
   [autorewrite] 会在它们上循环。请使用
   [rewrite] 手动使用它们。

   此处注册的引理如下：spider_collapse              μ ∘ δ ≈ id
   spider_mu_unit_left          μ ∘ bimap η id ≈ to unit_left
   spider_mu_unit_right         μ ∘ bimap id η ≈ to unit_right
   spider_delta_counit_left     bimap ε id ∘ δ ≈ from unit_left
   spider_delta_counit_right    bimap id ε ∘ δ ≈ from unit_right
   spider_mu_commutative        μ ∘ braid ≈ μ
   spider_delta_cocommutative   braid ∘ δ ≈ δ
*)

#[export] Hint Rewrite
  @spider_collapse
  @spider_mu_unit_left
  @spider_mu_unit_right
  @spider_delta_counit_left
  @spider_delta_counit_right
  @spider_mu_commutative
  @spider_delta_cocommutative
  : hypergraph.

(*
   * * [solve_hypergraph]: an automation tactic for SCFA-algebra goals

   Composes:
   1. [autorewrite with hypergraph]   simplify via the spider rules
   registered above
   2. [autorewrite with categories]    simplify via the library's
   category laws ([id_left],
   [id_right], [comp_assoc])
   3. [auto with category_laws]        close any remaining setoid
   reflexivity / [Proper] goals

   The tactic loops on its own simplification pass until fixpoint, so
   composite goals that decompose into a sequence of spider rewrites
   interleaved with category-law cleanups close in one call.

   Goals it does NOT close:

   - Anything requiring the BIDIRECTIONAL Frobenius / associativity
   rules ([spider_frobenius], [spider_mu_assoc], [spider_3_to_1]).
   Use [rewrite] manually for those.
   - Anything requiring monoidal-coherence (associator / unitor)
   manipulation beyond what's in the [categories] hint database.
   Combine with the future [strict_collapse] tactic for the
   strict-monoidal case.

   Typical use:

   Lemma foo : forall (X : C) (f : X ~> X),
   scfa_mu (scfa X) ∘ scfa_delta (scfa X) ∘ f ≈ f.
   Proof. intros; solve_hypergraph. Qed. 

   --------
   * *  [solve_hypergraph]：用于 SCFA-代数目标的自动化策略

   组成：
   1.  [autorewrite with hypergraph]    通过上面注册的蜘蛛规则简化
   2.  [autorewrite with categories]    通过库的范畴律简化（[id_left], [id_right], [comp_assoc]）
   3.  [auto with category_laws]    关闭任何剩余的集合同构自反性 / [Proper] 目标

   该策略在自身的简化步骤上循环，直到达到不变点，因此
   分解为一系列蜘蛛重写与范畴律清理交错的复合目标可以在一次调用中关闭。

   它不能关闭的目标：- 任何需要双向 Frobenius / 结合律规则（[spider_frobenius]、[spider_mu_assoc]、[spider_3_to_1]）的内容。对于这些规则，请手动使用 [rewrite]。
   - 任何需要超出 [categories] 提示数据库的单元模（associator / unitor）操作的内容。对于严格模单元情况，可结合将来的 [strict_collapse] 策略。

   典型用法：

   引理 foo : 对所有 (X : C) (f : X ~> X)，有
   scfa_mu (scfa X) ∘ scfa_delta (scfa X) ∘ f ≈ f。
   证明。intros; solve_hypergraph. Qed.
*)

Ltac solve_hypergraph :=
  repeat (autorewrite with hypergraph in *;
          autorewrite with categories in *);
  try (auto with category_laws);
  try reflexivity.

