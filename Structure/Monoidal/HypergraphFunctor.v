Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.
Require Import Category.Structure.Monoidal.Hypergraph.

Generalizable All Variables.

(*
   * * Hypergraph functors

   Reference: Fong, "The Algebra of Open and Interconnected Systems"
   (arXiv:1609.05382), Definition 1.4; Fong–Spivak, "Hypergraph
   categories" (Journal of Pure and Applied Algebra 223, 2019;
   arXiv:1806.08304), Definition 2.12.

   nLab:      https://ncatlab.org/nlab/show/hypergraph+category
   (defines hypergraph categories; the page does NOT define
   "hypergraph functor" — see the arXiv references above)
   nLab:      https://ncatlab.org/nlab/show/monoidal+functor
   (the underlying strong symmetric monoidal functor notion)
   Wikipedia: no dedicated article for hypergraph categories or
   hypergraph functors as of this writing.

   A HYPERGRAPH FUNCTOR between hypergraph categories [(C, ⨂_C, I_C, …)]
   and [(D, ⨂_D, I_D, …)] is a STRONG symmetric monoidal functor (per
   Fong–Spivak, "Hypergraph categories", Definition 2.12; Seven Sketches
   Def. 6.60 defines hypergraph categories themselves) preserving the
   SCFA structure on each object.  Concretely, the functor carries comparison
   *isomorphisms* [F X ⨂_D F Y ≅ F (X ⨂_C Y)] and [I_D ≅ F I_C]
   AND sends μ_X, η_X, δ_X, ε_X to μ_{F X}, η_{F X}, δ_{F X}, ε_{F X}
   up to transport along those isomorphisms.  (The fully-strict case,
   where the comparison isomorphisms are identities, recovers the
   on-the-nose equations [F (μ_X) ≈ μ_{F X}], etc.)

   This is the morphism notion in the category [HypGraph] of hypergraph
   categories.  Examples include the BLACK-BOXING functors of
   Baez–Fong–Spivak: every concrete black-box (electrical-circuit,
   Markov-process, signal-flow) factors as a hypergraph functor from a
   decorated-cospan domain into a target hypergraph category (relations,
   linear maps, ZX-diagrams).

   CAVEAT: the [HypergraphFunctor] record formalised below is a
   DELIBERATELY WEAKENED version of this literature notion.  It drops
   the strong-monoidal coherence equations (associator/unitor squares,
   naturality, braid-compatibility) and only records the comparison
   isomorphisms together with the four SCFA-preservation equations; see
   the "Known scoping limitation: missing monoidal coherences" section
   below.  As a consequence the record is NOT in general a symmetric
   monoidal functor.  The inhabitants currently provided are the trivial
   [Id_HypergraphFunctor] below and the images of the forgetful bridge
   [SymmetricMonoidalFunctor_HypergraphFunctor]
   (Functor/Structure/Monoidal/Hypergraph.v).

   ** Coq-specific organisation

   To keep the record self-contained in the present library and avoid
   the typeclass-resolution loops that arise when nesting
   [#[export] Instance Hypergraph] under another typeclass that itself
   triggers Hypergraph resolution on the codomain, we present
   [HypergraphFunctor] as a RECORD parameterised by the two ambient
   [Hypergraph] instances (and their underlying [SymmetricMonoidal]
   structures).  Instances of this record are built locally and are
   NOT auto-marked as [#[export] Instance].

   The record records (i) the underlying functor [F : C ⟶ D] and
   (ii) preservation of the four SCFA generators on every object,
   stated up to the [≈] equivalence in [D] modulo the canonical
   transport along the strict-monoidal coherences that identify
   [F X ⨂_D F Y] with [F (X ⨂_C Y)] and [I_D] with [F I_C].  In the
   fully-strict / on-the-nose case those transports are identities,
   yielding the literature definition verbatim.

   ** Known scoping limitation: missing monoidal coherences

   Per Fong–Spivak (Definition 2.12), a hypergraph functor is a
   (symmetric) STRONG monoidal functor that ALSO preserves the SCFA
   generators.  The record below carries [hf_unit_iso] and
   [hf_tensor_iso] as raw isomorphisms, BUT omits the standard
   lax-monoidal coherence equations:

   - associator hexagon for [hf_tensor_iso] vs. [tensor_assoc];
   - unitor squares for [hf_tensor_iso] vs. [unit_left] /
   [unit_right];
   - naturality of [hf_tensor_iso] in both arguments;
   - braid-compatibility ([fmap[F] braid ∘ hf_tensor_iso X Y ≈
   hf_tensor_iso Y X ∘ braid]).

   Consequence: two distinct choices of [hf_tensor_iso] / [hf_unit_iso]
   could each satisfy the four SCFA-preservation equations without
   [F] actually being a symmetric monoidal functor.  Downstream code
   that assumes "a [HypergraphFunctor] is in particular a symmetric
   monoidal functor" does NOT get that property from this record.

   The trivial [Id_HypergraphFunctor] instance below is fine
   ([hf_tensor_iso := iso_id], [hf_unit_iso := iso_id] discharge all
   coherences definitionally).  A non-trivial instance — e.g. the
   [forget_decoration] black-boxing functor — would need to
   additionally re-establish the missing coherences separately, or
   the record would need to be re-factored to extend an existing
   [Functor/Structure/Monoidal.v:MonoidalFunctor] (a deferred
   refactor).

   A more rigorous future redesign of this record either (a) adds
   the missing coherence fields here verbatim, or (b) re-parameterises
   on the library's [MonoidalFunctor] class together with its
   [SymmetricMonoidalFunctor] refinement
   (Functor/Structure/Monoidal/Braided.v) and inherits the coherence
   equations from there.  The sound forgetful half of option (b) now
   exists — [SymmetricMonoidalFunctor_HypergraphFunctor] in
   Functor/Structure/Monoidal/Hypergraph.v packages any strong
   symmetric monoidal functor preserving the SCFA generators as an
   inhabitant of this record — but forgetting into the record loses
   the coherences irrecoverably: the missing fields described above
   remain missing, and consumers of the record remain subject to this
   caveat. 

   --------
   * * 超图函子

   参考文献：Fong，《开放和互联系统的代数》
   (arXiv:1609.05382)，定义 1.4；Fong–Spivak，《超图范畴》
   (Journal of Pure and Applied Algebra 223, 2019; arXiv:1806.08304)，定义 2.12。

   nLab:       https://ncatlab.org/nlab/show/hypergraph+category 
   （定义超图范畴；该页面不定义“超图函子”——参见上述 arXiv 参考文献）
   nLab:       https://ncatlab.org/nlab/show/monoidal+functor 
   （底层强对称幺半范畴函子概念）
   维基百科：截至目前没有专门关于超图范畴或超图函子的条目。在超图范畴 [(C, ⨂_C, I_C, …)] 和 [(D, ⨂_D, I_D, …)] 之间的超图函子是一个强对称幺半函子（根据 Fong–Spivak，《超图范畴》，定义 2.12；《七个概述》，定义 6.60 定义了超图范畴本身），它保持每个对象上的 SCFA 结构。具体来说，该函子携带比较*同构* [F X ⨂_D F Y ≅ F (X ⨂_C Y)] 和 [I_D ≅ F I_C]，并将 μ_X、η_X、δ_X、ε_X 发送到 μ_{F X}、η_{F X}、δ_{F X}、ε_{F X}，沿着这些同构进行传输。（完全严格的情况，即比较同构为恒等映射时，会恢复精确的方程 [F (μ_X) ≈ μ_{F X}] 等。）这是超图类别 [HypGraph] 中的态射概念。示例包括 Baez–Fong–Spivak 的黑箱化函子：每个具体的黑箱（电路、马尔可夫过程、信号流）都可分解为从一个装饰余积域到目标超图类别（关系、线性映射、ZX-图）的超图函子。注意：下面形式化的 [HypergraphFunctor] 记录是对这一文献概念的刻意弱化版本。它舍弃了强单体范畴的相干方程（结合子/单位子方形、自然性、编织兼容性），只记录比较同构以及四个 SCFA 保持方程；见下文“已知的作用域限制：缺失单体相干性”部分。因此，该记录通常不是对称单体范畴函子。目前提供的元素是下文的平凡 [Id_HypergraphFunctor] 以及遗忘桥 [SymmetricMonoidalFunctor_HypergraphFunctor]（Functor/Structure/Monoidal/Hypergraph.v）的像。

   ** Coq 特定的组织结构为了在当前库中保持记录的自包含性，并避免在将 [#[export] 实例 Hypergraph 嵌套在另一个自身会触发 Hypergraph 在陪域上解析的类型类时产生的类型类解析循环，我们将 [HypergraphFunctor] 作为由两个外围 [Hypergraph] 实例（及其底层 [SymmetricMonoidal] 结构）参数化的 RECORD。该记录的实例在本地构建，并且不会被自动标记为 [#[export] 实例。该记录记录了 (i) 基础函子 [F : C ⟶ D] 和 (ii) 在每个对象上保持四个 SCFA 生成元的性质，表述为在 [D] 中的 [≈] 等价类下，并且模掉沿严格单态（strict-monoidal）相干性（coherences）的规范传输，这些相干性将 [F X ⨂_D F Y] 与 [F (X ⨂_C Y)] 以及 [I_D] 与 [F I_C] 对应起来。在完全严格 / 准确情况（on-the-nose）下，这些传输是恒等映射，从而得到文献中的定义逐字复制。

   ** 已知范围限制：缺少单态相干性

   根据 Fong–Spivak（定义 2.12），超图函子是一个（对称的）强单态（STRONG monoidal）函子，同时还保持 SCFA 生成元。下面的记录携带了 [hf_unit_iso] 和 [hf_tensor_iso] 作为原始同构，但省略了标准的松单态（lax-monoidal）相干方程:- 对于 [hf_tensor_iso] 与 [tensor_assoc] 的联结六边形；
   - 对于 [hf_tensor_iso] 与 [unit_left] / [unit_right] 的单位方形；
   - [hf_tensor_iso] 在两个参数中的自然性；
   - 编织兼容性（[fmap[F] 编织 ∘ hf_tensor_iso X Y ≈ hf_tensor_iso Y X ∘ 编织）。

   结果：两种不同的 [hf_tensor_iso] / [hf_unit_iso] 选择都可以满足四个 SCFA 保留方程，而不需要 [F] 真正成为一个对称单体函子。下游代码假设“一个 [HypergraphFunctor] 特别是一个对称单体函子”，但不能从该记录获得该属性。下面的简单 [Id_HypergraphFunctor] 实例是可以的（[hf_tensor_iso := iso_id]、[hf_unit_iso := iso_id] 按定义清除了所有相干性）。一个非简单的实例——例如 [forget_decoration] 黑箱函子——则需要另外单独重新建立缺失的相干性，或者需要重新整理记录以扩展现有的 [Functor/Structure/Monoidal.v:MonoidalFunctor]（一次延迟的重构）。对该记录进行更严格的未来重新设计，要么 (a) 在此逐字添加缺失的相干性字段，要么 (b) 基于库的 [MonoidalFunctor] 类及其 [SymmetricMonoidalFunctor] 精炼（Functor/Structure/Monoidal/Braided.v）重新参数化，并从那里继承相干性方程。选项 (b) 的可靠忘记一半现在已经存在——Functor/Structure/Monoidal/Hypergraph.v 中的 [SymmetricMonoidalFunctor_HypergraphFunctor] 将任何保持 SCFA 生成元的强对称单子函子作为该记录的一个成员进行打包——但是忘记到记录中会导致相干性不可恢复地丢失：上述缺失字段仍然缺失，记录的使用者仍然受到此警告的影响。
*)

Section HypergraphFunctor.

Context {C : Category}.
Context `{SC : @SymmetricMonoidal C}.
Context `{HG_C : @Hypergraph C SC}.

Context {D : Category}.
Context `{SD : @SymmetricMonoidal D}.
Context `{HG_D : @Hypergraph D SD}.

(*
   * A hypergraph functor [F : C ⟶ D] consists of an underlying functor
   together with *witnesses* that
   - tensor on objects is preserved up to a *fixed* iso [hf_tensor X Y :
   F X ⨂ F Y ≅ F (X ⨂ Y)];
   - the monoidal unit is preserved up to a *fixed* iso [hf_unit :
   I ≅ F I];
   - the SCFA generators on every [X] are preserved up to those
   transports (one equation per generator).

   The strict-on-the-nose case takes [hf_tensor X Y := id] and
   [hf_unit := id]; the SCFA preservation equations then reduce to the
   literature form [F (μ_X) ≈ μ_{F X}], etc.  We keep the iso
   parameterisation in the record because the standard library's
   [Functor] type does not record monoidality, so any concrete
   hypergraph-functor instance must supply these comparison iso's
   explicitly. 

   --------
   * 一个超图函子 [F : C ⟶ D] 由一个基础函子组成，同时附带 *证明*，说明：
   - 对象的张量在 *固定* 同构下被保留 [hf_tensor X Y : F X ⨂ F Y ≅ F (X ⨂ Y)];
   - 单位对象在 *固定* 同构下被保留 [hf_unit : I ≅ F I];
   - 每个 [X] 上的 SCFA 生成元在这些变换下被保留（每个生成元一条方程）。

   严格的一致情况取得 [hf_tensor X Y := id] 和 [hf_unit := id]；SCFA 保留方程则简化为文献中的形式 [F (μ_X) ≈ μ_{F X}] 等。我们在记录中保留同构参数化是因为标准库的 [Functor] 类型并不记录幺半群性，因此任何具体的超图函子实例必须显式提供这些比较同构。
*)

Record HypergraphFunctor : Type := {
  hf_functor :> C ⟶ D;

  (*
   * Comparison isomorphisms (the lax-monoidal data on [hf_functor],
   packaged here since [Functor] does not record it). 

   --------
   * 比较同构（在此封装的 [hf_functor] 上的松单元数据，因为 [Functor] 没有记录它）。
*)
  hf_unit_iso : @I D _ ≅ hf_functor (@I C _);
  hf_tensor_iso : forall (X Y : C),
    (hf_functor X ⨂ hf_functor Y)%object ≅ hf_functor (X ⨂ Y)%object;

  (*
   * SCFA preservation: the four generators on every [X] are sent to
   the corresponding generators on [F X], up to transport along the
   comparison isomorphisms.

   For [mu]:
   F (μ_X)  ∘  hf_tensor_iso X X  ≈  μ_{F X}.
   For [delta]: the corresponding equation in the opposite direction.
   For [eta]: the unit-comparison transports the source.
   For [epsilon]: the unit-comparison transports the codomain. 

   --------
   * SCFA 保持：每个 [X] 上的四个生成元被发送到 [F X] 上对应的生成元，沿比较同构的传输进行。

   对于 [mu]：
   F (μ_X) ∘ hf_tensor_iso X X ≈ μ_{F X}。
   对于 [delta]：相应的方程在相反方向。
   对于 [eta]：单位比较传输源。
   对于 [epsilon]：单位比较传输值域。
*)

  hf_preserves_mu : forall (X : C),
    fmap[hf_functor] (scfa_mu (scfa X)) ∘ to (hf_tensor_iso X X)
      ≈ scfa_mu (scfa (hf_functor X));

  hf_preserves_eta : forall (X : C),
    fmap[hf_functor] (scfa_eta (scfa X)) ∘ to hf_unit_iso
      ≈ scfa_eta (scfa (hf_functor X));

  hf_preserves_delta : forall (X : C),
    from (hf_tensor_iso X X) ∘ fmap[hf_functor] (scfa_delta (scfa X))
      ≈ scfa_delta (scfa (hf_functor X));

  hf_preserves_epsilon : forall (X : C),
    from hf_unit_iso ∘ fmap[hf_functor] (scfa_epsilon (scfa X))
      ≈ scfa_epsilon (scfa (hf_functor X))
}.

End HypergraphFunctor.

Arguments HypergraphFunctor {C SC} HG_C {D SD} HG_D.
Arguments hf_functor {C SC HG_C D SD HG_D} _.
Arguments hf_unit_iso {C SC HG_C D SD HG_D} _.
Arguments hf_tensor_iso {C SC HG_C D SD HG_D} _ _ _.
Arguments hf_preserves_mu {C SC HG_C D SD HG_D} _ _.
Arguments hf_preserves_eta {C SC HG_C D SD HG_D} _ _.
Arguments hf_preserves_delta {C SC HG_C D SD HG_D} _ _.
Arguments hf_preserves_epsilon {C SC HG_C D SD HG_D} _ _.

(*
   * ** The identity hypergraph functor

   For any hypergraph category [(C, HG_C)], the identity functor
   [Id C : C ⟶ C] is canonically a hypergraph functor with
   [hf_unit_iso := iso_id] and [hf_tensor_iso X Y := iso_id].

   All four preservation equations follow from [fmap[Id] f = f] (the
   definitional equation of the identity functor), combined with
   [iso_id]'s components reducing to [id] under composition. 

   --------
   * ** 恒等超图函子

   对于任意超图范畴 [(C, HG_C)]，恒等函子 [Id C : C ⟶ C] 自然是一个超图函子，具有 [hf_unit_iso := iso_id] 和 [hf_tensor_iso X Y := iso_id]。

   所有四个保持方程都可以由 [fmap[Id] f = f]（恒等函子的定义方程）推导出来，并结合 [iso_id] 的分量在组合下简化为 [id]。
*)

Section IdHypergraphFunctor.

Context {C : Category}.
Context `{SC : @SymmetricMonoidal C}.
Context `{HG_C : @Hypergraph C SC}.

Program Definition Id_HypergraphFunctor : HypergraphFunctor HG_C HG_C := {|
  hf_functor := Id[C] ;
  hf_unit_iso := iso_id ;
  hf_tensor_iso := fun X Y => iso_id
|}.

End IdHypergraphFunctor.

(*
   * ** Discussion: the BlackBox / forget-decoration use case

   The forgetful "drop the decoration" functor from [DecoratedCospanCat F]
   to [CospanCat C] is a hypergraph functor: it acts as the identity on
   objects, projects out the cospan part of every morphism, and the SCFA
   on a cospan-category object is given by the [Cospan_Hypergraph]
   instance — which by definition is the SCFA the forgetful functor
   preserves on the nose.

   Fully packaging [forget_decoration] as a [HypergraphFunctor] requires
   [DecoratedCospanCat F] to be a [Category] record (the
   [Construction/DecoratedCospan.v] module exports the API, the [Setoid],
   identity, and composition; the full [Category] obligations are
   discharged at the cospan level by [Construction/Cospan/Category.v]
   and at the decoration level by the lax-monoidal functor coherences).

   See [Construction/Cospan/BlackBox.v] for the cospan-equivalence
   well-definedness lemmas that this record-form encapsulates. 

   --------
   * ** 讨论：BlackBox / 忘记装饰的用例

   从 [DecoratedCospanCat F] 到 [CospanCat C] 的“忘记装饰”函子是一个超图函子：它在对象上作为恒等函数作用，对每个态射投射出 cospan 部分，并且 cospan-范畴对象上的 SCFA 由 [Cospan_Hypergraph] 实例提供 —— 根据定义，这正是忘记函子严格保持的 SCFA。

   将 [forget_decoration] 完全封装为 [HypergraphFunctor] 需要 [DecoratedCospanCat F] 是一个 [Category] 记录（[Construction/DecoratedCospan.v] 模块导出 API、[Setoid]、恒等和组合；完整的 [Category] 义务由 cospan 级别的 [Construction/Cospan/Category.v] 和装饰级别的 lax-monoidal 函子一致性来履行）。请参见 [Construction/Cospan/BlackBox.v] 关于这个记录形式所封装的余对等价良定义性引理。
*)

(*
   * ** Composition of hypergraph functors

   [HypergraphFunctor (HG_B, HG_C) -> HypergraphFunctor (HG_C, HG_D) ->
   HypergraphFunctor (HG_B, HG_D)]: composing the underlying functors,
   pairing the comparison iso's via [iso_compose] interleaved with
   [fmap]-transport, and combining the preservation equations.

   The composition law is mechanical but volumetric (each comparison
   iso composes through one [fmap], each preservation equation is the
   sum of the two component preservations).  We leave the explicit
   composition data to downstream sites that genuinely need it
   (the present library's main BlackBox use case only requires the
   identity instance and the literature pattern). 

   --------
   * ** 超图函子（hypergraph functors）的组合

   [HypergraphFunctor (HG_B, HG_C) -> HypergraphFunctor (HG_C, HG_D) ->
   HypergraphFunctor (HG_B, HG_D)]：组合底层函子，
   通过 [iso_compose] 配对比较同构，并穿插 [fmap]-传输，
   并结合保持方程。

   组合律是机械的但体积大（每个比较同构通过一个 [fmap] 组合，每个保持方程是两个组成保持的和）。我们将具体的组合数据留给真正需要它的下游站点（本库的主要 BlackBox 用例只需要恒等实例和文献模板）。
*)
