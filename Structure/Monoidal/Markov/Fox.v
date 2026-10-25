Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Relevance.
Require Import Category.Structure.Monoidal.Semicartesian.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Structure.Monoidal.Braided.Proofs.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Structure.Monoidal.CopyDiscard.
Require Import Category.Structure.Monoidal.CopyDiscard.Proofs.
Require Import Category.Structure.Monoidal.CopyDiscard.Deterministic.
Require Import Category.Structure.Monoidal.Markov.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.CommutativeComonoid.

Generalizable All Variables.

(*
   * * Fox's theorem: Markov categories with all morphisms deterministic

   Fox's theorem (Fox 1976; Heunen–Vicary 2012, p. 84) delimits the
   boundary between synthetic probability and ordinary (cartesian)
   computation:

   - a Markov category in which EVERY morphism is deterministic — i.e.
   copying commutes with every morphism — is cartesian monoidal
   ([all_deterministic_cartesian]); and, conversely,
   - in a cartesian monoidal category every morphism is deterministic
   with respect to the canonical diagonal/discard supply
   ([cartesian_all_deterministic]).

   Both directions together say that the copy-discard structure of a
   Markov category carries genuine probabilistic content exactly when
   copy-naturality breaks down somewhere; demanding it globally collapses the
   tensor to a categorical product.  This grounds the "cartesianization
   obstruction": no interesting Markov category factors through a
   cartesian one without killing its nondeterminism.

   The forward direction assembles a [RelevanceMonoidal] from the copy
   supply — naturality of the diagonal being exactly the determinism
   hypothesis — and discharges [CartesianMonoidal]'s remaining fields:

   proj_left_diagonal / proj_right_diagonal
   — the comonoid counit laws traded across terminality of [I]
   ([proj_left_copy] / [proj_right_copy], Markov.v);
   unit_left_braid / unit_right_braid
   — the derived braid–unitor coherences [braid_unit_left] /
   [braid_unit_right] of Structure/Monoidal/Braided/Proofs.v
   (Joyal–Street Prop. 2.1), the load-bearing import.

   Since in a Markov category the ε-triangle [discard ∘ f ≈ discard]
   holds for free (terminality of [I]), determinism there is equivalent
   to the copy square alone ([markov_deterministic_iff_copy]); this is
   why the forward direction needs nothing beyond copy-naturality.

   The packaging corollary [markov_all_deterministic_iff_cartesian]
   states the equivalence in existential form: a category carries a
   Markov structure whose morphisms are all deterministic iff it carries
   a cartesian monoidal structure.  The two roundtrip corollaries pin
   down that the forward construction preserves the supply: the copy
   and discard induced by the produced cartesian structure agree with
   the original ones.

   nLab:      https://ncatlab.org/nlab/show/Markov+category
   Reference: Fox, "Coalgebras and cartesian categories",
   Comm. Algebra 4(7):665–667, 1976
   Reference: Heunen & Vicary, "Categories for Quantum Theory",
   Oxford UP, 2019, §4.3 (Fox's theorem, p. 84 of the 2012
   lecture notes)
   Reference: Fritz, "A synthetic approach to Markov kernels ..."
   (arXiv:1908.07021), §10 

   --------
   * * 福克斯定理：所有态射都是确定性的马尔可夫范畴

   福克斯定理（Fox 1976；Heunen–Vicary 2012, 第84页）界定了合成概率与普通（笛卡尔）计算之间的边界：

   - 一个所有态射都是确定性的马尔可夫范畴——即复制与每个态射交换——是笛卡尔幺半群的（[all_deterministic_cartesian]）；反之，
   - 在一个笛卡尔幺半群范畴中，每个态射都是相对于典型对角/丢弃供应的确定性态射（[cartesian_all_deterministic]）。两个方向共同说明，马尔可夫范畴的复制-丢弃结构仅在某处复制自然而然性失效时才承载真正的概率内容；如果在全局要求它，则张量会坍缩为范畴乘积。这为“笛卡尔化障碍”提供了依据：没有有趣的马尔可夫范畴可以在不破坏其非确定性的情况下经过笛卡尔范畴因子分解。

   正向方向从复制供给中组装出 [RelevanceMonoidal]——对角线的自然性恰好对应确定性假设——并释放 [CartesianMonoidal] 的剩余字段：proj_left_diagonal / proj_right_diagonal
   — 通过 [I] 的终对象性交换的 comonoid counit 法则
   ([proj_left_copy] / [proj_right_copy], Markov.v);
   unit_left_braid / unit_right_braid
   — 导出的 braid–unitor 一致性 [braid_unit_left] /
   [braid_unit_right] 来自 Structure/Monoidal/Braided/Proofs.v
   (Joyal–Street 命题 2.1)，承载重要的导入。

   由于在 Markov 范畴中 ε-triangle [discard ∘ f ≈ discard]
   是自然成立的（[I] 的终对象性），
   那里的确定性等价于仅使用 copy square ([markov_deterministic_iff_copy])；
   这就是为什么正向方向除了 copy-naturality 外不需要其他东西。包装推论 [markov_all_deterministic_iff_cartesian] 声明了存在形式下的等价性：一个范畴携带马尔可夫结构且其态射全部是确定性的，当且仅当其携带笛卡尔幺半群结构。这两个往返推论明确指出正向构造保持供给：由生成的笛卡尔结构引起的复制和丢弃与原始结构一致。

   nLab：https://ncatlab.org/nlab/show/Markov+category
   参考文献：Fox, 《Coalgebras and cartesian categories》，Comm. Algebra 4(7):665–667, 1976
   参考文献：Heunen & Vicary, 《Categories for Quantum Theory》，Oxford UP, 2019, §4.3 (Fox 的定理, 2012 年讲义第 84 页)
   参考文献：Fritz, 《A synthetic approach to Markov kernels ...》(arXiv:1908.07021), §10
*)

Section Fox.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Section AllDeterministicCartesian.

Context `{M : @MarkovCategory C S}.

(*
   * ** Determinism in a Markov category is the copy square alone

   The ε-triangle of a comonoid homomorphism is automatic when the unit
   is terminal, so a morphism of a Markov category is deterministic as
   soon as it commutes with copying (Fritz, Definition 10.1). 

   --------
   * ** 马尔可夫范畴中的确定性仅是拷贝方块

   当单位对象是终对象时，余单同态的 ε-三角形是自动成立的，因此马尔可夫范畴的一个态射一旦与拷贝交换，就为确定性（Fritz，定义10.1）。
*)

Lemma markov_deterministic_of_copy {x y : C} (f : x ~> y) :
  copy[y] ∘ f ≈ (f ⨂ f) ∘ copy[x] → deterministic f.
Proof.
  intro Hcopy.
  split.
  - exact Hcopy.
  - apply (@unit_terminal C _ markov_semicartesian).
Qed.

Corollary markov_deterministic_iff_copy {x y : C} (f : x ~> y) :
  deterministic f ↔ (copy[y] ∘ f ≈ (f ⨂ f) ∘ copy[x]).
Proof.
  split.
  - exact (copy_natural_on_deterministic f).
  - exact (markov_deterministic_of_copy f).
Qed.

(* * ** All morphisms deterministic ⇒ cartesian monoidal / * ** 所有态射都是确定性的 ⇒ 笛卡尔单体 *)

Context (D : ∀ x y (f : x ~> y), deterministic f).

(*
 The copy supply becomes a natural diagonal: naturality is the
 determinism hypothesis, and the remaining coherence fields are the
 comonoid laws of the supply re-oriented. 

 --------
 复制供应变成自然的对角线：自然性是决定论假设，剩余的相干场是重新定向的供应的余范畴法则。
*)
Program Definition Relevance_of_deterministic : @RelevanceMonoidal C := {|
  relevance_is_symmetric := S;
  diagonal := fun x => copy[x]
|}.
Next Obligation.
  (*
 diagonal_natural: exactly the δ-square of the determinism
 hypothesis, read right-to-left. 

 --------
 diagonal_natural：正是决定论假设的 δ 平方，从右向左阅读。
*)
  symmetry.
  apply (copy_natural_on_deterministic _ (D _ _ _)).
Qed.
Next Obligation.
  (* diagonal_unit: the unit-coherence field of the supply. / diagonal_unit：供应的单位一致性领域。 *)
  apply copy_unit.
Qed.
Next Obligation.
  (* diagonal_tensor_assoc: coassociativity of the comonoid on x, solved for the forward associator. / diagonal_tensor_assoc：x 上余单元的余结合性，已为前向结合子求解。 *)
  unfold copy, ccomon_delta.
  rewrite <- comp_assoc.
  rewrite delta_coassoc.
  rewrite !comp_assoc.
  rewrite iso_to_from.
  rewrite id_left.
  reflexivity.
Qed.
Next Obligation.
  (* braid_diagonal: cocommutativity of the supply. / braid_diagonal：供应的共换性。 *)
  unfold copy, ccomon_delta.
  apply delta_cocommutative_of_ccomon.
Qed.
Next Obligation.
  (* diagonal_braid2: the tensor-coherence field, with [braid2] recognized as [mid_swap_inv] (cf. braid2_mid_swap_inv). / diagonal_braid2：张量相干场，其中 [braid2] 被识别为 [mid_swap_inv]（参见 braid2_mid_swap_inv）。 *)
  rewrite copy_tensor.
  comp_right.
  unfold mid_swap_inv.
  rewrite !bimap_comp_id_left.
  rewrite !comp_assoc.
  reflexivity.
Qed.

Program Definition all_deterministic_cartesian : @CartesianMonoidal C := {|
  cartesian_is_relevance     := Relevance_of_deterministic;
  cartesian_is_semicartesian := markov_semicartesian
|}.
Next Obligation.
  (* proj_left_diagonal: the right counit law across terminality. / proj_left_diagonal：跨终端性的右单位律。 *)
  apply proj_left_copy.
Qed.
Next Obligation.
  (* proj_right_diagonal: the left counit law across terminality. / proj_right_diagonal：跨终端性的左余单位律。 *)
  apply proj_right_copy.
Qed.
Next Obligation.
  (* unit_left_braid: Joyal–Street ρ ≈ λ ∘ β (Braided/Proofs.v). / unit_left_braid: Joyal–Street ρ ≈ λ ∘ β (Braided/Proofs.v). *)
  apply braid_unit_left.
Qed.
Next Obligation.
  (* unit_right_braid: the mirror coherence λ ≈ ρ ∘ β. / unit_right_braid: 镜像相干 λ ≈ ρ ∘ β。 *)
  apply braid_unit_right.
Qed.

(*
   * ** Roundtrip: the produced cartesian structure carries the original
   supply

   The copy-discard structure induced by [all_deterministic_cartesian]
   (via [CD_of_Cartesian]) has the same copy — definitionally — and the
   same discard — by terminality — as the Markov category we started
   from.  Fox's construction loses nothing. 

   --------
   * ** 往返：生成的笛卡尔结构保留了原始的供应

   由 [all_deterministic_cartesian]（通过 [CD_of_Cartesian]）引起的复制-丢弃结构在定义上具有相同的复制，并且由于终端性而具有与我们开始的马尔可夫范畴相同的丢弃。Fox 的构造没有丢失任何东西。
*)

Corollary all_deterministic_cartesian_copy {x : C} :
  @copy C S (@CD_of_Cartesian C all_deterministic_cartesian) x ≈ copy[x].
Proof. reflexivity. Qed.

Corollary all_deterministic_cartesian_discard {x : C} :
  @discard C S (@CD_of_Cartesian C all_deterministic_cartesian) x
    ≈ discard[x].
Proof. apply (@unit_terminal C _ markov_semicartesian). Qed.

End AllDeterministicCartesian.

(* * ** Cartesian monoidal ⇒ all morphisms deterministic / * ** 笛卡尔幺半群 ⇒ 所有态射都是确定性的 *)

Section CartesianDeterministic.

Context `{H : @CartesianMonoidal C}.

(*
 Every morphism of a cartesian monoidal category is a comonoid
 homomorphism for the canonical diagonal/discard supply: the δ-square
 is naturality of the diagonal, and the ε-triangle is terminality of
 the unit.  "All kernels are deterministic": the degenerate,
 probability-free reading of a cartesian category as a Markov one. 

 --------
 笛卡尔单体范畴的每一个态射都是余单体同态，对应于规范的对角/丢弃供应：δ方形是对角的自然性，ε三角是单位的终对象性。“所有核都是确定性的”：将笛卡尔范畴作为马尔可夫范畴的简化、无概率的解读。
*)
Theorem cartesian_all_deterministic :
  ∀ x y (f : x ~> y), @deterministic C _ (@CD_of_Cartesian C H) x y f.
Proof.
  intros x y f.
  split.
  - symmetry; apply diagonal_natural.
  - apply unit_terminal.
Qed.

End CartesianDeterministic.

End Fox.

(*
   * ** Packaging: Fox's theorem as an equivalence

   A category carries a Markov structure in which every morphism is
   deterministic precisely when it carries a cartesian monoidal
   structure.  The forward direction is [all_deterministic_cartesian];
   the backward direction equips the category with the canonical Markov
   structure of its cartesian one ([Markov_of_Cartesian]) and observes
   that all morphisms are deterministic there. 

   --------
   * ** 打包：福克斯定理作为等价

   一个范畴携带马尔可夫结构，其中每个态射都是确定性的，当且仅当它携带笛卡尔幺半群结构。正向方向是 [all_deterministic_cartesian]；反向方向为该范畴配备其笛卡尔结构的典范马尔可夫结构 ([Markov_of_Cartesian])，并观察到所有态射在那里都是确定性的。
*)

Section FoxPackaging.

Context {C : Category}.

Corollary markov_all_deterministic_iff_cartesian :
  (∃ (S : @SymmetricMonoidal C) (M : @MarkovCategory C S),
     ∀ x y (f : x ~> y), @deterministic C S (@markov_is_cd C S M) x y f)
    ↔ @CartesianMonoidal C.
Proof.
  split.
  - intros [S' [M' D]].
    exact (@all_deterministic_cartesian C S' M' D).
  - intro H.
    exists (@relevance_is_symmetric C (@cartesian_is_relevance C H)).
    exists (@Markov_of_Cartesian C H).
    intros x y f.
    exact (@cartesian_all_deterministic C H x y f).
Qed.

End FoxPackaging.
