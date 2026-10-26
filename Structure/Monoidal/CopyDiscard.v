Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.CommutativeComonoid.

Generalizable All Variables.

(*
   * * Copy-discard (gs-monoidal) categories

   A copy-discard category — also called a gs-monoidal category (“garbage
   and sharing”) — is a symmetric monoidal category [(C, ⨂, I, σ)] equipped
   with a chosen commutative comonoid

   copy[X]    : X ~> X ⨂ X      (comultiplication, “duplicate the wire”)
   discard[X] : X ~> I          (counit, “delete the wire”)

   on every object, such that the comonoid on [X ⨂ Y] is canonically
   assembled from those on [X] and [Y] (via the middle-interchange
   isomorphism), and the comonoid on [I] is the trivial one.

   THE defining negative space of this class: there is deliberately NO
   naturality condition on [copy] or [discard].  A morphism [f] need not
   satisfy [copy ∘ f ≈ (f ⨂ f) ∘ copy] nor [discard ∘ f ≈ discard]; the
   two squares together are precisely what single out the DETERMINISTIC
   morphisms (Cho–Jacobs; see CopyDiscard/Deterministic.v).  The two
   omissions carry different weight.  Imposing the discard square on ALL
   morphisms is exactly semicartesianness — it says any map into [I]
   agrees with [discard], i.e. [I] is terminal — which is the Markov case,
   not a degeneracy: Structure/Monoidal/Markov.v derives [discard_natural]
   for every morphism as a corollary of [unit_terminal].  Imposing the
   copy square on ALL morphisms makes [copy] a natural diagonal, yielding
   [RelevanceMonoidal]'s naturality together with the counits that class
   lacks; imposing both squares globally is Fox's theorem territory: the
   structure collapses to cartesian monoidal (see Heunen_Vicary.v and
   Markov/Fox.v).  This class is therefore INCOMPARABLE with
   [RelevanceMonoidal], not below it: [CopyDiscard] carries counits that
   [RelevanceMonoidal] lacks, while [RelevanceMonoidal] carries the
   naturality that [CopyDiscard] deliberately drops.  What both strengthen
   is the bare per-object [CommutativeComonoid] supply with no coherence
   at all.

   Accordingly [RelevanceMonoidal] is NOT a source of instances for this
   class: its diagonal comes with no counit whatsoever, so the comonoid
   counit laws [(ε ⨂ id) ∘ δ ≈ λ⁻¹] are underivable there.  The sound
   generic instances — from [CartesianMonoidal] (Fox's projection laws
   supply the counits) and from [Hypergraph] (forget the monoid half of
   each SCFA) — live in Structure/Monoidal/CopyDiscard/Proofs.v.

   The class shape mirrors Hypergraph.v's SCFA supply verbatim: a
   per-object structure field, canonical-tensor coherence, and unit
   coherence, reusing [canonical_tensor_delta] / [canonical_tensor_epsilon]
   (stated there for plain [Comonoid] arguments; [CommutativeComonoid]
   coerces).  The Hypergraph.v import supplies only that
   middle-interchange vocabulary ([mid_swap_inv] and the two
   [canonical_tensor_*] composites) — symmetric-monoidal-level material
   with no Frobenius content.  Conceptually the dependency runs the
   other way: every hypergraph category is a copy-discard category
   ([CD_of_Hypergraph] in CopyDiscard/Proofs.v).

   nLab:      https://ncatlab.org/nlab/show/copy-discard+category
   Reference: Cho & Jacobs, “Disintegration and Bayesian inversion via
   string diagrams”, MSCS 29(7):938–971, 2019 (arXiv:1709.00322)
   Reference: Fritz, “A synthetic approach to Markov kernels, conditional
   independence and theorems on sufficient statistics”,
   Adv. Math. 370:107239, 2020 (arXiv:1908.07021), §2
   Reference: Corradini & Gadducci, “An algebraic presentation of term
   graphs, via gs-monoidal categories”, Appl. Categ. Structures
   7(4):299–331, 1999 

   --------
   * * 拷贝-丢弃（gs-单体）范畴

   拷贝-丢弃范畴——也称为 gs-单体范畴（“垃圾和共享”）——是一个对称单体范畴  [(C, ⨂, I, σ)] ，配备了一个选定的交换余单体

   copy [X]     : X ~> X ⨂ X      （余乘法，“复制线”）
   discard [X]  : X ~> I          （余单位，“删除线”）

   在每个对象上，使得对象  [X ⨂ Y] 上的余单体可以由对象  [X] 和  [Y] 上的余单体通过中间互换同构自然组装而成，并且对象  [I] 上的余单体是平凡的。这一类的定义性负空间：在  [copy]  或  [discard] 上故意没有自然性条件。一个态射  [f]  不需要满足  [copy ∘ f ≈ (f ⨂ f) ∘ copy]  也不需要满足  [discard ∘ f ≈ discard]；这两个方框正是区分确定性态射（Cho–Jacobs；见 CopyDiscard/Deterministic.v）的关键。两者的省略具有不同的重量。在所有态射上施加丢弃方框正是半笛卡尔性质——它表示任何映射到  [I]  的映射都与  [discard]  一致，即  [I]  是终对象——这是马尔可夫情况，而不是退化：Structure/Monoidal/Markov.v 从  [unit_terminal]  的结果推导出每个态射的  [discard_natural]。在所有态射上强加拷贝方格使得 [copy] 成为自然对角，从而产生 [RelevanceMonoidal] 的自然性以及该类缺失的协单位；在全局上同时强加两个方格是 Fox 定理的领域：结构会坍缩为笛卡尔幺半群（参见 Heunen_Vicary.v 和 Markov/Fox.v）。因此该类与 [RelevanceMonoidal] 是不可比较的，不在其之下：[CopyDiscard] 拥有 [RelevanceMonoidal] 所缺失的协单位，而 [RelevanceMonoidal] 拥有 [CopyDiscard] 特意放弃的自然性。两者所增强的都是每个对象上最基本的 [CommutativeComonoid] 供给，而且完全没有任何相容性。因此，[RelevanceMonoidal] 不是这个类的实例来源：它的对角完全没有伴单位，因此在这里 [(ε ⨂ id) ∘ δ ≈ λ⁻¹] 的余单元律是不可推导的。可靠的通用实例——来自 [CartesianMonoidal]（Fox 的投影律提供了余单元）和来自 [Hypergraph]（忽略每个 SCFA 的单子部分）——位于 Structure/Monoidal/CopyDiscard/Proofs.v 中。类 shape 精确镜像 Hypergraph.v 的 SCFA 提供：每个对象的结构字段、规范张量一致性和单位一致性，重用 [canonical_tensor_delta] / [canonical_tensor_epsilon]（在那里为普通 [Comonoid] 参数声明；[CommutativeComonoid] 强制转换）。Hypergraph.v 导入仅提供中间交换词汇（[mid_swap_inv] 和两个 [canonical_tensor_*] 复合体）——对称单幺范畴层面的内容，没有 Frobenius 内容。概念上依赖关系是相反的：每个超图范畴都是一个拷贝-丢弃范畴（CopyDiscard/Proofs.v 中的 [CD_of_Hypergraph]）。nLab: https://ncatlab.org/nlab/show/copy-discard+category 
   参考文献: Cho & Jacobs, 《通过弦图的解离与贝叶斯反演》，MSCS 29(7):938–971, 2019 (arXiv:1709.00322)
   参考文献: Fritz, 《对马尔可夫核、条件独立及充分统计定理的综合性方法》，Adv. Math. 370:107239, 2020 (arXiv:1908.07021), 第2节
   参考文献: Corradini & Gadducci, 《通过 gs-单体范畴的项图代数表述》，Appl. Categ. Structures 7(4):299–331, 1999
*)

Section CopyDiscard.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Class CopyDiscard : Type := {
  cd_comonoid (X : C) : CommutativeComonoid X;

  (*
 Tensor coherence: the comonoid on [X ⨂ Y] agrees with the canonical
 one assembled from those on [X] and [Y] through [mid_swap_inv]
 (Hypergraph.v):  δ_{X⨂Y} ≈ mid_swap_inv ∘ (δ_X ⨂ δ_Y). 

 --------
 张量相干性：[X ⨂ Y] 上的余单子与通过 [mid_swap_inv] 从 [X] 和 [Y] 上的余单子组装而成的规范余单子一致（Hypergraph.v）：δ_{X⨂Y} ≈ mid_swap_inv ∘ (δ_X ⨂ δ_Y).
*)
  cd_tensor_delta (X Y : C) :
    ccomon_delta (cd_comonoid (X ⨂ Y))
      ≈ canonical_tensor_delta (cd_comonoid X) (cd_comonoid Y);

  (* ε_{X⨂Y} ≈ unit_left ∘ (ε_X ⨂ ε_Y). / ε_{X⨂Y} ≈ unit_left ∘ (ε_X ⨂ ε_Y). *)
  cd_tensor_epsilon (X Y : C) :
    ccomon_epsilon (cd_comonoid (X ⨂ Y))
      ≈ canonical_tensor_epsilon (cd_comonoid X) (cd_comonoid Y);

  (* Unit coherence: the comonoid on [I] is the trivial one, δ_I ≈ unit_left⁻¹ and ε_I ≈ id (cf. scfa_unit_delta/epsilon). / 单位相干性：在 [I] 上的余半群是平凡的， δ_I ≈ unit_left⁻¹ 且 ε_I ≈ id（参见 scfa_unit_delta/epsilon）。 *)
  cd_unit_delta   : ccomon_delta   (cd_comonoid I) ≈ from (@unit_left C _ I);
  cd_unit_epsilon : ccomon_epsilon (cd_comonoid I) ≈ id[I]
}.

(*
 [cd_comonoid] is deliberately NOT an [Existing Instance] (mirroring
 [scfa] in Hypergraph.v): typeclass resolution must never invent a
 comonoid structure on an object; access it via the projections below. 

 --------
 [cd_comonoid] 故意不是 [Existing Instance]（对应 Hypergraph.v 中的 [scfa]）：类型类解析绝不应在一个对象上发明一个余单子结构；通过下方的投影访问它。
*)

Definition copy `{CopyDiscard} (X : C) : X ~> (X ⨂ X)%object :=
  ccomon_delta (cd_comonoid X).

Definition discard `{CopyDiscard} (X : C) : X ~> I :=
  ccomon_epsilon (cd_comonoid X).

End CopyDiscard.

Arguments cd_comonoid {C S _} X.
Arguments copy {C S _} X.
Arguments discard {C S _} X.
Arguments CopyDiscard C {S}.

Notation "copy[ X ]" := (copy X)
  (at level 9, format "copy[ X ]") : morphism_scope.
Notation "discard[ X ]" := (discard X)
  (at level 9, format "discard[ X ]") : morphism_scope.
