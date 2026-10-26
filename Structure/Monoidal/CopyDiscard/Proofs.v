Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.Proofs.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.CopyDiscard.
Require Import Category.Structure.Monoidal.Relevance.
Require Import Category.Structure.Monoidal.Semicartesian.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Structure.Monoidal.Heunen_Vicary.Proofs.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.CommutativeComonoid.
Require Import Category.Theory.Algebra.Frobenius.
Require Import Category.Theory.Algebra.CommutativeFrobenius.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.

Generalizable All Variables.

(*
   * * Copy-discard categories: lemma kit and sound generic instances

   Derived facts about the [CopyDiscard] class of
   Structure/Monoidal/CopyDiscard.v:

   - naturality of the middle-interchange map [mid_swap_inv] in both
   of its (diagonal) arguments — the workhorse behind closure of
   deterministic morphisms under ⨂;
   - the bridge identifying [RelevanceMonoidal]'s [braid2] at
   (x, x, y, y) with [mid_swap_inv x y];
   - rewrite-friendly forms of the tensor- and unit-coherence fields
   ([copy_tensor], [discard_tensor], [copy_unit], [discard_unit]);
   - the two SOUND generic instances:
   [CD_of_Cartesian]  : CartesianMonoidal ⇒ CopyDiscard
   (Fox's projection laws proj_*_diagonal supply the comonoid
   counit laws), and
   [CD_of_Hypergraph] : Hypergraph ⇒ CopyDiscard
   (forget the monoid half of each SCFA; the coherence fields
   are literally the scfa_tensor and scfa_unit fields).

   There is deliberately NO instance from [RelevanceMonoidal] (with or
   without [SemicartesianMonoidal]): a relevance diagonal comes with no
   counit whatsoever, and the comonoid counit laws
   [(ε ⨂ id) ∘ δ ≈ λ⁻¹] are exactly Fox's [proj_right_diagonal] /
   [proj_left_diagonal] axioms — underivable without them.

   Reference: Fritz, “A synthetic approach to Markov kernels ...”
   (arXiv:1908.07021), §2
   Reference: Fox, “Coalgebras and cartesian categories”,
   Comm. Algebra 4(7):665–667, 1976 

   --------
   * * 复制-丢弃类别：词条工具包和通用声音实例

   关于 [CopyDiscard] 类的衍生事实
   结构/幺半群/复制丢弃.v：- 中间互换映射 [mid_swap_inv] 在其两个（对角线）参数中的自然性 — 是决定性态射在 ⨂ 下闭合的关键；
   - 将 [RelevanceMonoidal] 在 (x, x, y, y) 处的 [braid2] 与 [mid_swap_inv x y] 对应的桥梁；
   - 张量和单位相干场的可重写形式（[copy_tensor]、[discard_tensor]、[copy_unit]、[discard_unit]）；
   - 两个 SOUND 泛实例：
   [CD_of_Cartesian] ：CartesianMonoidal ⇒ CopyDiscard
   （Fox 的投影律 proj_*_diagonal 提供了上半群余律），以及
   [CD_of_Hypergraph] ：Hypergraph ⇒ CopyDiscard
   （忽略每个 SCFA 的半群部分；相干场字面上就是 scfa_tensor 和 scfa_unit 字段）。故意没有来自 [RelevanceMonoidal]（无论是否有 [SemicartesianMonoidal]）的实例：一个关联对角线完全没有余单元，并且余单元的余模律 [(ε ⨂ id) ∘ δ ≈ λ⁻¹] 恰好是 Fox 的 [proj_right_diagonal] / [proj_left_diagonal] 公理——没有它们无法推导。

   参考文献：Fritz，《A synthetic approach to Markov kernels ...》（arXiv:1908.07021），§2
   参考文献：Fox，《Coalgebras and cartesian categories》，Comm. Algebra 4(7):665–667, 1976
*)

Section MidSwapNatural.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

(*
 Naturality of the middle-four interchange at the diagonal: tensoring
 f with itself and f' with itself commutes past [mid_swap_inv].  The
 diagonal instance of the four-slot [swap_inner_natural] of
 Structure/Monoidal/Braided/Proofs.v ([mid_swap_inv x x'] being
 definitionally [swap_inner x x x' x']); stated in [mid_swap_inv] form
 rather than via Relevance.v's [braid2_natural] because [braid2] is a
 [RelevanceMonoidal] field while [mid_swap_inv] needs only symmetry. 

 --------
 对角线上的中间四交换的自然性：将 f 与自身以及 f' 与自身进行张量操作可以通过 [mid_swap_inv] 交换。结构/单体/编织/Proofs.v 中的四槽 [swap_inner_natural] 的对角线实例（[mid_swap_inv x x'] 在定义上为 [swap_inner x x x' x']）；以 [mid_swap_inv] 形式陈述，而不是通过 Relevance.v 的 [braid2_natural]，因为 [braid2] 是一个 [RelevanceMonoidal] 域，而 [mid_swap_inv] 仅需要对称性。
*)
Lemma mid_swap_inv_natural {x x' y y'} (f : x ~> y) (f' : x' ~> y') :
  mid_swap_inv y y' ∘ ((f ⨂ f) ⨂ (f' ⨂ f'))
    ≈ ((f ⨂ f') ⨂ (f ⨂ f')) ∘ mid_swap_inv x x'.
Proof. exact (swap_inner_natural f f f' f'). Qed.

End MidSwapNatural.

Section Braid2Bridge.

Context {C : Category}.
Context `{R : @RelevanceMonoidal C}.

(*
 [RelevanceMonoidal]'s middle-four interchange [braid2], instantiated
 at (x, x, y, y), is definitionally the same composite as
 [mid_swap_inv x y] — the only difference is that [braid2] tensors
 id[x] against the three inner maps at once, while [mid_swap_inv]
 distributes the tensoring.  Expand with [bimap_comp_id_left]. 

 --------
 [RelevanceMonoidal] 的中间四次互换 [braid2] ，在 (x, x, y, y) 处实例化，从定义上与 [mid_swap_inv x y] 是相同的复合——唯一的区别是 [braid2] 对三个内部映射同时张量 id [x]，而 [mid_swap_inv] 则分配张量操作。用 [bimap_comp_id_left] 展开。
*)
Lemma braid2_mid_swap_inv (x y : C) :
  @braid2 C R x x y y ≈ mid_swap_inv x y.
Proof.
  unfold braid2, mid_swap_inv.
  rewrite !bimap_comp_id_left.
  rewrite !comp_assoc.
  reflexivity.
Qed.

End Braid2Bridge.

Section CopyDiscardRewrites.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

(*
 The tensor-coherence fields of [CopyDiscard], unfolded through
 [canonical_tensor_delta] / [canonical_tensor_epsilon] into directly
 rewritable equations. 

 --------
 [CopyDiscard] 的张量相干场，通过 [canonical_tensor_delta] / [canonical_tensor_epsilon] 展开成可直接重写的方程。
*)

Corollary copy_tensor `{CD : @CopyDiscard C S} (X Y : C) :
  copy[(X ⨂ Y)%object] ≈ mid_swap_inv X Y ∘ (copy[X] ⨂ copy[Y]).
Proof.
  unfold copy.
  rewrite cd_tensor_delta.
  unfold canonical_tensor_delta.
  reflexivity.
Qed.

Corollary discard_tensor `{CD : @CopyDiscard C S} (X Y : C) :
  discard[(X ⨂ Y)%object]
    ≈ to (@unit_left C _ I) ∘ (discard[X] ⨂ discard[Y]).
Proof.
  unfold discard.
  rewrite cd_tensor_epsilon.
  unfold canonical_tensor_epsilon.
  reflexivity.
Qed.

(* The unit-coherence fields, in the same rewrite-friendly form. / 单位相干场，以相同的便于重写的形式。 *)

Corollary copy_unit `{CD : @CopyDiscard C S} :
  copy[I] ≈ (@unit_left C _ I)⁻¹.
Proof. exact cd_unit_delta. Qed.

Corollary discard_unit `{CD : @CopyDiscard C S} : discard[I] ≈ id[I].
Proof. exact cd_unit_epsilon. Qed.

End CopyDiscardRewrites.

Section CDCartesian.

Context {C : Category}.
Context `{H : @CartesianMonoidal C}.

(*
 SOUND instance 1: in a cartesian monoidal category the natural
 diagonal ∆ (Relevance) and the terminal-unit discard [eliminate]
 (Semicartesian) form a commutative comonoid on every object — the
 counit laws are Fox's proj_*_diagonal axioms, packaged by
 [eliminate_left_diagonal] / [eliminate_right_diagonal] in
 Structure/Monoidal/Heunen_Vicary/Proofs.v — and the comonoid supply
 is coherent with the tensor and the unit. 

 --------
 SOUND 实例 1：在笛卡尔幺半群范畴中，自然对角线 ∆（相关性）和终对象-单位丢弃 [eliminate]（半笛卡尔）在每个对象上形成一个交换余单体——余单位律是 Fox 的 proj_*_diagonal 公理，由 [eliminate_left_diagonal] / [eliminate_right_diagonal] 在 Structure/Monoidal/Heunen_Vicary/Proofs.v 中打包——并且余单体供应与张量和单位相干。
*)
Program Definition CD_of_Cartesian :
  @CopyDiscard C (@relevance_is_symmetric C (@cartesian_is_relevance C H)) := {|
  cd_comonoid := fun X =>
    {| ccomon_comonoid :=
         {| delta   := @diagonal C _ X;
            epsilon := @eliminate C _ _ X |} |}
|}.
Next Obligation.
  (* delta_coassoc: reorient diagonal_tensor_assoc by cancelling α. / delta_coassoc：通过消去 α 来重新定向 diagonal_tensor_assoc。 *)
  rewrite <- comp_assoc.
  rewrite diagonal_tensor_assoc.
  rewrite !comp_assoc.
  rewrite iso_from_to, id_left.
  reflexivity.
Qed.
Next Obligation.
  (* delta_counit_left: (ε ⨂ id) ∘ ∆ ≈ λ⁻¹ is Fox's proj_right_diagonal. / delta_counit_left: (ε ⨂ id) ∘ ∆ ≈ λ⁻¹ 是 Fox 的 proj_right_diagonal。 *)
  apply eliminate_left_diagonal.
Qed.
Next Obligation.
  (* delta_counit_right: (id ⨂ ε) ∘ ∆ ≈ ρ⁻¹ is Fox's proj_left_diagonal. / delta_counit_right: (id ⨂ ε) ∘ ∆ ≈ ρ⁻¹ 是 Fox 的 proj_left_diagonal。 *)
  apply eliminate_right_diagonal.
Qed.
Next Obligation.
  (* cocommutativity: braid ∘ ∆ ≈ ∆. / 余交换性：编织 ∘ ∆ ≈ ∆。 *)
  apply braid_diagonal.
Qed.
Next Obligation.
  (*
 cd_tensor_delta: ∆ on a tensor is the canonical comonoid.  This is
 diagonal_braid2 composed with the braid2 ≈ mid_swap_inv bridge; the
 [braid2] let-field arrives inlined in diagonal_braid2's statement,
 so we replay the expansion of [braid2_mid_swap_inv] directly. 

 --------
 cd_tensor_delta: 张量上的 ∆ 是典型的余单体。这是 diagonal_braid2 与 braid2 ≈ mid_swap_inv 桥的组合；[braid2] let-字段内联到 diagonal_braid2 的语句中，因此我们直接重放 [braid2_mid_swap_inv] 的展开。
*)
  unfold ccomon_delta, canonical_tensor_delta; simpl.
  rewrite diagonal_braid2.
  comp_right.
  unfold mid_swap_inv.
  rewrite !bimap_comp_id_left.
  rewrite !comp_assoc.
  reflexivity.
Qed.
Next Obligation.
  (* cd_tensor_epsilon: both sides are maps into the terminal unit. / cd_tensor_epsilon：两边都映射到终端单位。 *)
  apply unit_terminal.
Qed.
Next Obligation.
  (* cd_unit_delta: ∆ at I is the canonical iso I ≅ I ⨂ I. / cd_unit_delta: 在 I 处的 ∆ 是典型的同构 I ≅ I ⨂ I。 *)
  apply diagonal_unit.
Qed.
Next Obligation.
  (* cd_unit_epsilon: both sides are maps into the terminal unit. / cd_unit_epsilon：两边都是映射到终端单位。 *)
  apply unit_terminal.
Qed.

End CDCartesian.

Section CDHypergraph.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.
Context `{H : @Hypergraph C S}.

(*
 SOUND instance 2: a hypergraph category supplies a special
 commutative Frobenius algebra on every object; forgetting the monoid
 half of each SCFA leaves exactly a coherent commutative-comonoid
 supply.  The four coherence obligations are literally the
 scfa_tensor_delta/epsilon and scfa_unit_delta/epsilon fields. 

 --------
 声音例子 2：一个超图范畴在每个对象上提供一个特殊的交换 Frobenius 代数；忘记每个 SCFA 的幺半部分，正好留下一个连贯的交换余单子供应。这四个连贯性义务实际上就是 scfa_tensor_delta/epsilon 和 scfa_unit_delta/epsilon 字段。
*)
Program Definition CD_of_Hypergraph : @CopyDiscard C S := {|
  cd_comonoid := fun X =>
    {| ccomon_comonoid :=
         @frob_comonoid C _ X
           (@cfrob_frobenius C S X (@scfa_commutative C S X (scfa X)));
       delta_cocommutative_of_ccomon :=
         @delta_cocommutative C S X (@scfa_commutative C S X (scfa X)) |}
|}.
Next Obligation.
  (* cd_tensor_delta ≈ scfa_tensor_delta, up to unfolding projections. / cd_tensor_delta ≈ scfa_tensor_delta，直到展开投影。 *)
  apply scfa_tensor_delta.
Qed.
Next Obligation.
  apply scfa_tensor_epsilon.
Qed.
Next Obligation.
  apply scfa_unit_delta.
Qed.
Next Obligation.
  apply scfa_unit_epsilon.
Qed.

End CDHypergraph.
