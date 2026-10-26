Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.
Require Import Category.Theory.Algebra.CommutativeFrobenius.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Construction.Cospan.Category.
Require Import Category.Construction.Cospan.Bridging.
Require Import Category.Construction.Cospan.Hypergraph.
Require Import Category.Construction.Cospan.Symmetric.
Require Import Category.Construction.Cospan.HypergraphInstance.
Require Import Category.Construction.DecoratedCospan.
Require Import Category.Construction.DecoratedCospan.Category.
Require Import Category.Construction.DecoratedCospan.Symmetric.
Require Import Category.Construction.DecoratedCospan.Monoidal.
Require Import Category.Construction.DecoratedCospan.Braided.

Generalizable All Variables.

(*
   * * Hypergraph structure on [DecoratedCospanCat]

   Reference: Brendan Fong, “Decorated Cospans”, arXiv:1502.00872,
   Theorem 3.5 (the decorated-cospan category is symmetric monoidal and
   a hypergraph category); Fong–Spivak, “Hypergraph categories”,
   JPAA 223 (2019) = arXiv:1806.08304, Definition 4.1.1 (hypergraph
   category) and Definition 4.1.3 (hypergraph functor).

   This module assembles the [Hypergraph] instance on
   [DecoratedCospanCat HP LM id_decoration cospan_merge] by layering
   a decoration coherence class on top of [Cospan_Hypergraph] from
   [Construction/Cospan/HypergraphInstance.v].

   ** Architecture

   The [Hypergraph] class on [DC] requires:

   - an SCFA on every object [X];
   - tensor coherence ([scfa_tensor_mu], [scfa_tensor_eta],
   [scfa_tensor_delta], [scfa_tensor_epsilon]) — the SCFA on
   [X ⨂ Y] agrees with the canonical SCFA assembled from those
   of [X] and [Y];
   - unit coherence ([scfa_unit_mu], [scfa_unit_eta],
   [scfa_unit_delta], [scfa_unit_epsilon]) — the SCFA on [I]
   is the trivial one.

   The literature-correct packaging (Fong–Spivak, Definition 4.1.1 of
   the “Hypergraph categories” paper) bundles all of this — the
   decoration-coherent SCFA per object plus the 8 coherence equations
   — as a single hypergraph-decoration coherence class.  Concrete
   decoration choices (Fong's circuits, Baez–Fong Markov processes)
   would supply explicit witnesses for all fields; this library does
   not yet provide any such instance (see the status note below).

   We package this as [DecCospan_Hypergraph_Coherent], whose principal
   field is a per-object [SpecialCommutativeFrobenius DC X], plus the
   8 standard tensor + unit coherence equations.

   ** Note on the lax-symmetric requirement (Fong Definition 3.1 / Theorem 3.5)

   Fong introduces [F] as a lax braided monoidal functor in
   Definition 3.1; the hypergraph structure (Theorem 3.5) requires the
   SYMMETRIC strengthening, so [F] must be a LAX SYMMETRIC monoidal
   functor.  The symmetric-laxness is needed here because
   [μ] for the SCFA on [X+Y] uses braiding to interleave decorations:
   without [F (braid_C) ∘ lax_ap ≈ lax_ap ∘ braid_D], the canonical
   SCFA on [X+Y] (assembled from the SCFAs of [X] and [Y]) cannot
   be shown to satisfy the Frobenius/commutativity laws on decorated
   cospans.

   In this library's factoring, the [DecCospan_Braided_Coherent] and
   [DecCospan_Symmetric_Coherent] classes (taken as [Context] above)
   encode exactly the decorated-cospan-side consequences of [F] being
   lax-symmetric — instantiating them is impossible without an
   underlying lax-symmetric [F].

   ** Status: CONDITIONAL on unfilled coherence assumptions

   [DecoratedCospan_Hypergraph] below is built inside a [Section] whose
   [Context] assumes the full stack of coherence classes
   ([DecCospan_Coherent], [DecCospan_Bifunctor_Coherent],
   [DecCospan_Monoidal_Coherent], [DecCospan_Braided_Coherent],
   [DecCospan_Symmetric_Coherent], [DecCospan_Hypergraph_Coherent]).
   NONE of these classes is instantiated anywhere in the library: only
   the [Class] declarations and the [Context] assumptions exist, with no
   [Instance]/[Build_] witnesses.  This construction is therefore a
   CONDITIONAL result — given the coherence witnesses it would yield the
   [Hypergraph] instance, but it is not a finished, inhabited result.
   Even the “trivial decoration” ([F = Δ I_D]) witness is NOT supplied
   here; the discussion of how each field would be discharged (below) is
   a sketch of intended work, not a delivered instance. 

   --------
   * * 超图结构在 [DecoratedCospanCat] 上 

   参考文献：Brendan Fong，《Decorated Cospans》，arXiv:1502.00872，定理 3.5（装饰余蕨范畴是对称幺半范畴并且是超图范畴）；Fong–Spivak，《Hypergraph categories》，JPAA 223 (2019) = arXiv:1806.08304，定义 4.1.1（超图范畴）和定义 4.1.3（超图函子）。

   该模块通过在 [Construction/Cospan/HypergraphInstance.v] 的 [Cospan_Hypergraph] 上叠加装饰一致性类来组合 [DecoratedCospanCat HP LM id_decoration cospan_merge] 上的 [Hypergraph] 实例。

   ** 架构

   [DC] 上的 [Hypergraph] 类需要：- 每个对象上的 SCFA  [X]；
   - 张量相干性 ([scfa_tensor_mu], [scfa_tensor_eta], [scfa_tensor_delta], [scfa_tensor_epsilon]) — [X ⨂ Y] 上的 SCFA 与由 [X] 和 [Y] 组装而成的标准 SCFA 一致；
   - 单位相干性 ([scfa_unit_mu], [scfa_unit_eta], [scfa_unit_delta], [scfa_unit_epsilon]) — [I] 上的 SCFA 是平凡的。文献中正确的包装方式（Fong–Spivak，《超图范畴》论文中的定义4.1.1）将所有这些内容——每个对象的装饰一致SCFA以及8个一致性方程——捆绑为一个单一的超图装饰一致性类。具体的装饰选择（Fong的电路，Baez–Fong的马尔可夫过程）会为所有字段提供明确的实例；这个库目前还没有提供任何这样的实例（见下方状态说明）。

   我们将其打包为[DecCospan_Hypergraph_Coherent]，其主要字段为每个对象的[SpecialCommutativeFrobenius DC X]，以及8个标准的张量+单位一致性方程。

   ** 关于松对称性要求的说明（Fong 定义3.1 / 定理3.5）Fong 在定义 3.1 中将 [F] 引入为一个松弛的编织单体函子；超图结构（定理 3.5）要求对称加强，因此 [F] 必须是一个松弛对称单体函子。这里需要对称松弛性，因为 [μ] 对 [X+Y] 上的 SCFA 使用了编织来交错装饰：没有 [F (braid_C) ∘ lax_ap ≈ lax_ap ∘ braid_D]，从 [X] 和 [Y] 的 SCFA 组装而成的 [X+Y] 上的规范 SCFA 无法证明满足带有装饰的余半群/交换律。在这个库的分解中，[DecCospan_Braided_Coherent] 和 [DecCospan_Symmetric_Coherent] 类（如上文采用的 [Context]）精确地编码了 [F] 是松对称时的装饰余半范后果——在没有基础松对称 [F] 的情况下实例化它们是不可能的。

   ** 状态：取决于未完成的相干性假设[DecoratedCospan_Hypergraph] 下方构建在一个 [Section] 内部，其 [Context] 假设了完整的相干类栈（[DecCospan_Coherent], [DecCospan_Bifunctor_Coherent], [DecCospan_Monoidal_Coherent], [DecCospan_Braided_Coherent], [DecCospan_Symmetric_Coherent], [DecCospan_Hypergraph_Coherent]）。这些类中没有任何一个在库中被实例化：只有 [Class] 声明和 [Context] 假设存在，并且没有 [Instance] / [Build_] 见证人。因此，这种构造是一个条件性的结果——在给定相干见证人的情况下，它会生成 [Hypergraph] 实例，但它不是一个完整的、已填充的结果。即便是“平凡装饰”（[F = Δ I_D]）见证人也未在此提供；下面对每个字段如何被解决的讨论只是预期工作的草图，而不是实际交付的实例。
*)

Section DecoratedCospanHypergraph.

Context {C : Category}.
Context (HP : HasPushouts C).
Context `{H_Coc : @Cocartesian C}.
Context `{H_Ini : @Initial C}.
Context `{MC : @Monoidal C}.
Context {D : Category}.
Context `{MD : @Monoidal D}.
Context {F : C ⟶ D}.
Context (LM : @LaxMonoidalFunctor C D MC MD F).
Context (id_decoration : forall X : C, @I D _ ~{D}~> F X).
Context (cospan_merge :
          forall (N M : C), (N ⨂[MC] M)%object ~{C}~> (N + M)%object).
Context `{DCC : @DecCospan_Coherent C HP H_Coc MC D MD F LM
                                     id_decoration cospan_merge}.
Context `{DCBC : @DecCospan_Bifunctor_Coherent C HP H_Coc MC D MD F LM
                                                id_decoration cospan_merge}.
Context `{DCMC : @DecCospan_Monoidal_Coherent C HP H_Coc H_Ini MC D MD F LM
                                               id_decoration cospan_merge}.
Context `{DCBrC : @DecCospan_Braided_Coherent C HP H_Coc MC D MD F LM
                                                id_decoration cospan_merge}.
Context `{DCSC : @DecCospan_Symmetric_Coherent C HP H_Coc MC D MD F LM
                                                 id_decoration cospan_merge}.

Notation DC := (DecoratedCospanCat HP LM id_decoration cospan_merge).
Notation DCMon := (DecoratedCospan_Monoidal HP LM id_decoration cospan_merge).
Notation DCSMC :=
  (DecoratedCospan_SymmetricMonoidal HP LM id_decoration cospan_merge).

(*
   * ** Coherence class for the Hypergraph structure on [DC]

   Fong's “decorated SCFA” data: a decoration-coherent choice of
   SCFA generator for every object, satisfying the 8 standard
   coherence equations of the [Hypergraph] class.

   Each field's RHS uses the [DecoratedCospan_SymmetricMonoidal]
   instance (which is the SMC structure on [DC] from Braided.v); the
   LHS is the user-supplied data.

   The principal field [dec_cospan_scfa] supplies the per-object
   decorated SCFA.  In the trivial-decoration case it is the
   [Cospan_Hypergraph]-SCFA with [id_decoration] decorations on each
   apex; in genuine decorated-cospan examples it is the SCFA carrying
   the application-specific data on each apex (Fong circuits use the
   “no-resistors” decoration, Baez–Fong Markov processes use the
   “no-transitions” decoration, etc.). 

   --------
   * ** [DC] 上超图结构的相干性类

   Fong 的“装饰 SCFA”数据：每个对象的 SCFA 生成元的装饰一致选择，满足 [Hypergraph] 类的 8 个标准相干方程。

   每个字段的右侧使用 [DecoratedCospan_SymmetricMonoidal] 实例（这是来自 Braided.v 的 [DC] 上的 SMC 结构）；左侧是用户提供的数据。

   主要字段 [dec_cospan_scfa] 提供每个对象的装饰 SCFA。在平凡装饰情况下，它是顶点上带有 [id_decoration] 装饰的 [Cospan_Hypergraph]-SCFA；在真正的装饰余积实例中，它是携带每个顶点应用特定数据的 SCFA（Fong 电路使用“无电阻器”装饰，Baez–Fong 马尔可夫过程使用“无转移”装饰，等等）。
*)

Class DecCospan_Hypergraph_Coherent : Type := {
  dec_cospan_scfa : forall (X : DC),
    @SpecialCommutativeFrobenius DC DCSMC X;

  (*
   * Tensor coherence: the SCFA on [X ⨂ Y] agrees with the canonical
   assembled one. 

   --------
   * 张量相干性：在 [X ⨂ Y] 上的 SCFA 与典型组装的 SCFA 一致。
*)
  dec_scfa_tensor_mu : forall (X Y : DC),
    @scfa_mu DC DCSMC _ (dec_cospan_scfa (X ⨂ Y)%object)
      ≈ @canonical_tensor_mu DC DCSMC X Y
          (dec_cospan_scfa X) (dec_cospan_scfa Y);

  dec_scfa_tensor_eta : forall (X Y : DC),
    @scfa_eta DC DCSMC _ (dec_cospan_scfa (X ⨂ Y)%object)
      ≈ @canonical_tensor_eta DC DCSMC X Y
          (dec_cospan_scfa X) (dec_cospan_scfa Y);

  dec_scfa_tensor_delta : forall (X Y : DC),
    @scfa_delta DC DCSMC _ (dec_cospan_scfa (X ⨂ Y)%object)
      ≈ @canonical_tensor_delta DC DCSMC X Y
          (dec_cospan_scfa X) (dec_cospan_scfa Y);

  dec_scfa_tensor_epsilon : forall (X Y : DC),
    @scfa_epsilon DC DCSMC _ (dec_cospan_scfa (X ⨂ Y)%object)
      ≈ @canonical_tensor_epsilon DC DCSMC X Y
          (dec_cospan_scfa X) (dec_cospan_scfa Y);

  (*
   * Unit coherence: the SCFA on [I_DC] is the trivial one. 

   --------
   * 单位一致性：[I_DC] 上的 SCFA 是平凡的。
*)
  dec_scfa_unit_mu :
    @scfa_mu DC DCSMC _ (dec_cospan_scfa (@I DC DCMon))
      ≈ to (@unit_left DC DCMon (@I DC DCMon));

  dec_scfa_unit_eta :
    @scfa_eta DC DCSMC _ (dec_cospan_scfa (@I DC DCMon))
      ≈ id[(@I DC DCMon)];

  dec_scfa_unit_delta :
    @scfa_delta DC DCSMC _ (dec_cospan_scfa (@I DC DCMon))
      ≈ from (@unit_left DC DCMon (@I DC DCMon));

  dec_scfa_unit_epsilon :
    @scfa_epsilon DC DCSMC _ (dec_cospan_scfa (@I DC DCMon))
      ≈ id[(@I DC DCMon)]
}.

Context `{DCHGC : DecCospan_Hypergraph_Coherent}.

Set Default Proof Using "All".

(*
   * ** [DecoratedCospan_Hypergraph] : the Hypergraph instance 

   --------
   * **  [DecoratedCospan_Hypergraph]  ：超图实例
*)

Program Definition DecoratedCospan_Hypergraph : @Hypergraph DC DCSMC := {|
  scfa                := dec_cospan_scfa ;
  scfa_tensor_mu      := dec_scfa_tensor_mu ;
  scfa_tensor_eta     := dec_scfa_tensor_eta ;
  scfa_tensor_delta   := dec_scfa_tensor_delta ;
  scfa_tensor_epsilon := dec_scfa_tensor_epsilon ;
  scfa_unit_mu        := dec_scfa_unit_mu ;
  scfa_unit_eta       := dec_scfa_unit_eta ;
  scfa_unit_delta     := dec_scfa_unit_delta ;
  scfa_unit_epsilon   := dec_scfa_unit_epsilon
|}.

End DecoratedCospanHypergraph.

(*
   * ** Discussion: how the coherence class WOULD be discharged

   The following sketches the intended witnesses; none is constructed in
   this library (the coherence classes are assumed, never instantiated —
   see the status note in the header above).

   The [DecCospan_Hypergraph_Coherent] class packages exactly the
   structure Fong identifies in Theorem 3.5 of “Decorated Cospans”:
   a per-object decoration-coherent SCFA plus the 8 standard
   hypergraph coherences.

   For the trivial decoration ([F = Δ I_D]):

   - [dec_cospan_scfa X] is the [Cospan_Hypergraph.scfa] wrapped
   with [id_decoration] on every apex (the apex for [mu] is [X],
   for [eta] is [X], etc.);

   - the 8 coherence equations would be inherited from the
   corresponding [Cospan_Hypergraph] equations under apex-iso
   transport of [id_decoration], which simplifies when [F = Δ I_D]
   (since [fmap[F] _ = id]) — but even this trivial witness is not
   actually built here.

   For Fong's electrical circuits, [dec_cospan_scfa X] is the SCFA
   carrying the “empty resistor network” decoration (the additive
   unit of the resistor-network monoid on [X]); the tensor and unit
   coherences follow from the algebra of resistor networks on
   coproducts.

   For Baez–Fong Markov processes, [dec_cospan_scfa X] is the SCFA
   carrying the “no transitions” decoration; the coherences follow
   from the monoid structure on transition graphs.

   In every case the witness would be a short calculation in the chosen
   decoration data, building on the cospan-level SCFA construction
   already done by [Cospan_Hypergraph]; those calculations are not yet
   carried out here, so no [DecCospan_Hypergraph_Coherent] instance is
   provided. 

   --------
   * ** 讨论：如何履行相干类

   以下概述了预期的见证；在此库中没有构造任何一个（相干类被假定，永远不实例化——请参阅上方标题中的状态注释）。

   [DecCospan_Hypergraph_Coherent] 类封装了 Fong 在《装饰余积》中定理 3.5 确定的结构：
   每个对象的装饰相干 SCFA 加上 8 个标准超图相干。

   对于平凡装饰（[F = Δ I_D]）：

   - [dec_cospan_scfa X] 是 [Cospan_Hypergraph.scfa] 包装后的形式，
   在每个顶点上附加 [id_decoration]（[mu] 的顶点是 [X]，
   [eta] 的顶点是 [X]，等等）。- 这8个相干方程将从对应的 [Cospan_Hypergraph] 方程继承，通过 [id_decoration] 的顶点等距传输来实现，当 [F = Δ I_D] 时，这将简化（因为 [fmap[F] _ = id）——但即使这个简单的例证在这里也并未实际构建。

   对于 Fong 的电路，[dec_cospan_scfa X] 是携带“空电阻网络”装饰的 SCFA（位于 [X] 电阻网络幺半群上的加法单位）；张量和单位相干性来自于余积上的电阻网络代数。

   对于 Baez–Fong 的马尔可夫过程，[dec_cospan_scfa X] 是携带“无转换”装饰的 SCFA；其相干性来自于转换图上的幺半群结构。在每种情况下，证据都会是在所选装饰数据中的一个简短计算，建立在 [Cospan_Hypergraph] 已经完成的 cospan 级 SCFA 构造之上；这些计算在此尚未进行，因此未提供 [DecCospan_Hypergraph_Coherent] 实例。
*)
