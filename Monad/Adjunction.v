Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * 由伴随诱导的单子。 *)

(* nLab: https://ncatlab.org/nlab/show/monad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)

   每个伴随 F ⊣ U 在复合 U ◯ F 上诱导单子：单位是伴随的单位 η，乘法是 U ε F
   （whiskered 余单位）。本文件记录该构造 [Adjunction_Monad]。亦可从 counit/unit 形式
   F ∹ U 出发直接读出 η 与 U ε。两者产出同一单子 U ◯ F。

   逆命题——每个单子都来自伴随——也成立，经 Kleisli（初始）与 Eilenberg–Moore（终结）
   分解（见 Monad/Kleisli.v 与 Monad/Eilenberg/Moore.v）。但裸复合 U ◯ F 本身不记住伴随：
   可把 Id 与任意单子 M 复合而得不到伴随，故仅有单子呈现、无伴随数据，不足以重建 F 与 U。 *)

Section AdjunctionMonad.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

Theorem Adjunction_Monad : F ⊣ U → @Monad D (U ◯ F).
Proof.
  intros.
  unshelve econstructor; simpl; intros.
  - apply (to (adj[X])); simpl.
    exact id.
  - apply fmap.
    apply (from (adj[X])); simpl.
    exact id.
  - rewrite <- to_adj_nat_r.
    rewrite <- to_adj_nat_l.
    cat.
  - simpl.
    rewrite <- !fmap_comp.
    apply fmap_respects.
    rewrite <- from_adj_nat_r.
    rewrite <- from_adj_nat_l.
    cat.
  - rewrite <- !fmap_comp; simpl.
    rewrite <- from_adj_nat_l.
    rewrite id_left.
    destruct X, adj; simpl in *.
    rewrite iso_from_to.
    exact fmap_id.
  - rewrite <- to_adj_nat_r; simpl.
    rewrite id_right.
    destruct X, adj; simpl in *.
    rewrite iso_to_from.
    reflexivity.
  - rewrite <- !fmap_comp; simpl.
    apply fmap_respects.
    rewrite <- from_adj_nat_r.
    rewrite <- from_adj_nat_l.
    cat.
Qed.

Theorem Adjunction_Nat_Monad : F ∹ U → @Monad D (U ◯ F).
Proof.
  intros.
  unshelve econstructor; simpl; intros.
  - exact (transform[unit] _).
  - exact (fmap (transform[counit] _)).
  - symmetry.
    apply (naturality[unit]).
  - rewrite <- !fmap_comp.
    apply fmap_respects.
    symmetry.
    apply (naturality[counit]).
  - rewrite <- !fmap_comp.
    srewrite (@counit_fmap_unit); cat.
  - simpl.
    srewrite (@fmap_counit_unit); cat.
  - rewrite <- !fmap_comp.
    apply fmap_respects.
    symmetry.
    apply (naturality[counit]).
Qed.

End AdjunctionMonad.
