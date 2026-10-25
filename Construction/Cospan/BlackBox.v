Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Construction.Cospan.Category.
Require Import Category.Construction.DecoratedCospan.
Require Import Category.Construction.DecoratedCospan.Category.

(*
   * * Black-boxing functor for decorated cospans

   Reference: Baez–Fong, "A compositional framework for passive linear
   networks", arXiv:1504.05625 §4 (the black-box functor ♭ : Circ →
   LagRel); Fong, "The Algebra of Open and Interconnected Systems",
   arXiv:1609.05382 (PhD thesis), where black-boxing is developed across
   Ch. 3 ("Corelations: a tool for black boxing") and Ch. 4 ("Decorated
   corelations: black-boxed open systems").

   nLab has no dedicated "black boxing" page; the concept is documented
   under https://ncatlab.org/nlab/show/decorated+cospan and
   https://ncatlab.org/nlab/show/hypergraph+category.  Wikipedia has no
   article on this (applied-category-theory) sense of black-boxing.

   The black-boxing concept: a "decorated cospan" represents an open
   system with an internal mechanism (the decoration) and an external
   interface (the cospan).  Black-boxing forgets the internal mechanism,
   retaining only the observable input/output behaviour — typically a
   relation, a Markov kernel, or a linear map.

   Categorically, black-boxing is a HYPERGRAPH FUNCTOR

   ⬛ : DecoratedCospanCat F  ⟶  ObservableCat

   that preserves the symmetric monoidal AND the SCFA structure on each
   object.  This is what makes black-boxing COMPOSITIONAL: the black-box
   of a composite system is the composite of the black-boxes, and the
   black-box of a parallel composition is the parallel composition of
   the black-boxes.

   ** What this file lands

   1. The "underlying cospan" forgetful black-box

   [forget_decoration : DecoratedCospanCat F → CospanCat C]

   — a black-box that throws away the decoration entirely, keeping
   only the cospan.

   2. The well-definedness lemmas: forgetting respects the
   [dec_cospan_equiv] equivalence (so the action descends to the
   quotient), and preserves identity and composition on the nose.

   3. A discussion of how the general black-boxing functor — taking
   decorated cospans to relations, Markov kernels, linear maps, or
   ZX-diagrams — instantiates the same pattern.

   See Fong's thesis, Theorem 6.1, which states that the original
   Baez–Fong electrical-circuit black-boxing functor ♭ : Circ → LagRel
   is a hypergraph functor (equivalently Baez–Fong arXiv:1504.05625).
   The categorical content of that theorem is precisely: apex-iso
   transport + lax-monoidal naturality + SCFA preservation; the
   forgetful black-box below is the trivial instance that exhibits this
   structure with the cleanest possible proof. 

   --------
   * * 装饰余积的黑箱函子

   参考文献：Baez–Fong，《被动线性网络的组合框架》，arXiv:1504.05625 §4（黑箱函子 ♭ : Circ → LagRel）；Fong，《开放与互联系统的代数》，arXiv:1609.05382（博士论文），其中黑箱化在第3章（“核心关系：黑箱工具”）和第4章（“装饰核心关系：黑箱化开放系统”）中进行阐述。

   nLab 没有专门的“黑箱化”页面；该概念记录在 https://ncatlab.org/nlab/show/decorated+cospan 和 https://ncatlab.org/nlab/show/hypergraph+category. 下。Wikipedia 没有关于这种（应用范畴理论）意义上的黑箱化的条目。黑箱化概念：“装饰余范”表示一个具有内部机制（装饰）和外部接口（余范）的开放系统。黑箱化会忽略内部机制，仅保留可观测的输入/输出行为——通常是一个关系、马尔可夫核或线性映射。

   在范畴论上，黑箱化是一个超图函子

   ⬛ : DecoratedCospanCat F  ⟶  ObservableCat

   它保持对称幺半群结构以及每个对象的特殊交换 Frobenius 代数结构（SCFA）。这就是黑箱化具有组合性的原因：复合系统的黑箱是各个黑箱的复合，而并行组合的黑箱是各个黑箱的并行组合。

   ** 本文件内容

   1. “基础余范”的遗忘式黑箱[forget_decoration : DecoratedCospanCat F → CospanCat C]

   — 一个完全丢弃装饰的黑箱，只保留余範围。

   2. 良定义性引理：遗忘操作遵守 [dec_cospan_equiv] 等价（因此该操作可以下降到商上），并严格保持恒等与复合。

   3. 关于泛黑箱函子的一些讨论 — 将装饰的余範围映射到关系、马尔可夫核、线性映射或 ZX 图 — 实现了相同的模式。参见Fong的论文，第6.1定理，该定理指出原始的Baez–Fong电路黑箱函子♭ : Circ → LagRel是一个超图函子（等价于Baez–Fong arXiv:1504.05625）。该定理的范畴论内容正是：顶点同构传递 + 松单态自然性 + SCFA保持；下面的遗忘黑箱是展示这一结构的最简单实例，并且具有尽可能干净的证明。
*)

(* * ** Section: forgetful black-box on decorated cospans / * ** 章节：装饰余圆上的健忘黑箱 *)

Section ForgetDecoration.

Context {C : Category}.
Context (HP : HasPushouts C).
Context {MC : @Monoidal C}.
Context {D : Category}.
Context {MD : @Monoidal D}.
Context (F : C ⟶ D).
Context (LM : @LaxMonoidalFunctor C D MC MD F).
Context `{H_Coc : @Cocartesian C}.

(** The action on objects: identity. / 对象的操作：身份。 *)
Definition forget_decoration_obj : C -> C := fun X => X.

(*
   * The action on morphisms: project the cospan out of the decorated cospan. 

   --------
   * 对态射的作用：将装饰余副投影出来。
*)
Definition forget_decoration_morphism
  {X Y : C} (f : DecoratedCospanArrow X Y)
  : CospanArrow X Y := dc_cospan f.

(*
   * [forget_decoration] respects the decorated-cospan equivalence,
   descending to a well-defined function on the equivalence classes
   of [DecoratedCospanCat]. 

   --------
   *  [forget_decoration] 尊重已装饰的余跨度等价，降到 [DecoratedCospanCat] 的等价类上得到一个良定义的函数。
*)
Lemma forget_decoration_morphism_respects
  {X Y : C} (f g : DecoratedCospanArrow X Y) :
  dec_cospan_equiv f g ->
  cospan_equiv (forget_decoration_morphism f) (forget_decoration_morphism g).
Proof.
  intros [E _].
  exact E.
Qed.

Context (id_decoration : forall X : C, @I D _ ~{D}~> F X).
Context (cospan_merge :
          forall (N M : C), (N ⨂[MC] M)%object ~{C}~> (N + M)%object).

(*
   * [forget_decoration] preserves identity: the underlying cospan of the
   identity-decorated cospan on [X] is the identity cospan on [X]. 

   --------
   *  [forget_decoration] 保留身份：在 [X] 上带身份装饰的余跨的底层余跨是 [X] 上的身份余跨。
*)
Lemma forget_decoration_id (X : C) :
  forget_decoration_morphism
    (dec_cospan_id id_decoration X)
  = cospan_id X.
Proof. reflexivity. Qed.

(*
   * [forget_decoration] preserves composition: the underlying cospan of a
   composed decorated cospan is the composed cospan. 

   --------
   * [forget_decoration] 保持组合性：一个组合装饰余跨度的底层余跨度就是组合后的余跨度。
*)
Lemma forget_decoration_compose {X Y Z : C}
  (g : DecoratedCospanArrow Y Z)
  (f : DecoratedCospanArrow X Y) :
  forget_decoration_morphism
    (dec_cospan_compose HP LM cospan_merge g f)
  = cospan_compose HP (forget_decoration_morphism g) (forget_decoration_morphism f).
Proof. reflexivity. Qed.

(*
   * Cospan-equivalence variants (for downstream use via [≈] rewriting). 

   --------
   * Cospan 等价变体（用于通过 [≈] 重写进行下游使用）。
*)
Lemma forget_decoration_correct_id {X : C} :
  cospan_equiv
    (forget_decoration_morphism (dec_cospan_id id_decoration X))
    (cospan_id X).
Proof. apply cospan_equiv_refl. Qed.

Lemma forget_decoration_correct_compose {X Y Z : C}
  (g : DecoratedCospanArrow Y Z)
  (f : DecoratedCospanArrow X Y) :
  cospan_equiv
    (forget_decoration_morphism
       (dec_cospan_compose HP LM cospan_merge g f))
    (cospan_compose HP
       (forget_decoration_morphism g)
       (forget_decoration_morphism f)).
Proof.
  rewrite forget_decoration_compose.
  apply cospan_equiv_refl.
Qed.

End ForgetDecoration.

(*
   * ** The forgetful black-box as a [Functor]

   With [DecoratedCospanCat] in scope (and the [DecCospan_Coherent]
   coherence class), [forget_decoration] is a [Functor] record from
   [DecoratedCospanCat HP LM id_decoration cospan_merge] to
   [CospanCat C HP].

   The functor laws are immediate from the [forget_decoration_*]
   lemmas above: the underlying cospan of the identity decorated
   cospan IS the identity cospan, and the underlying cospan of a
   composite IS the composite of underlying cospans (both by
   reflexivity of the cospan setoid). 

   --------
   * ** 忘记的黑箱作为 [Functor]  

   在 [DecoratedCospanCat] 范围内（以及 [DecCospan_Coherent] 相干类），[forget_decoration] 是从  
   [DecoratedCospanCat HP LM id_decoration cospan_merge] 到  
   [CospanCat C HP] 的 [Functor] 记录。  

   函子定律可以直接从上述 [forget_decoration_*] 引理得到：带装饰的恒等共跨的底层共跨是恒等共跨，而复合的底层共跨是底层共跨的复合（两者均由共跨等价集合的自反性得出）。
*)

Section ForgetDecorationFunctor.

Context {C : Category}.
Context (HP : HasPushouts C).
Context `{H_Coc : @Cocartesian C}.
Context {MC : @Monoidal C}.
Context {D : Category}.
Context {MD : @Monoidal D}.
Context {F : C ⟶ D}.
Context (LM : @LaxMonoidalFunctor C D MC MD F).
Context (id_decoration : forall X : C, @I D _ ~{D}~> F X).
Context (cospan_merge :
          forall (N M : C), (N ⨂[MC] M)%object ~{C}~> (N + M)%object).
Context `{DCC : @DecCospan_Coherent C HP H_Coc MC D MD F LM
                                     id_decoration cospan_merge}.

Program Definition forget_decoration
  : (DecoratedCospanCat HP LM id_decoration cospan_merge) ⟶ (CospanCat C HP) := {|
  fobj := fun X => X;
  fmap := fun X Y f => @forget_decoration_morphism C D MD F X Y f
|}.
Next Obligation.
  proper.
  apply (@forget_decoration_morphism_respects C D MD F);
    assumption.
Defined.
Next Obligation.
  apply (@forget_decoration_correct_id C D MD F id_decoration).
Defined.
Next Obligation.
  apply (@forget_decoration_correct_compose C HP MC D MD F LM
                                            H_Coc cospan_merge).
Defined.

End ForgetDecorationFunctor.

(*
   * ** Hypergraph-functoriality of the forgetful black-box

   [CospanCat C HP] carries the canonical hypergraph structure
   [Cospan_Hypergraph] (in [Construction/Cospan/HypergraphInstance.v]).
   Lifting [DecoratedCospanCat F] to a full hypergraph category — by
   pairing the cospan-level SCFA with a CHOSEN decoration on each of
   [μ, η, δ, ε] — and then forgetting the decoration leaves the SCFA
   on [forget_decoration X = X] equal to [Cospan_Hypergraph]'s SCFA,
   so preservation is REFLEXIVE: [F (μ_X) = μ_{F X}] etc.

   The strict form of hypergraph-functor preservation:

   F (mu_X)     ≈ mu_{F X}
   F (eta_X)    ≈ eta_{F X}
   F (delta_X)  ≈ delta_{F X}
   F (eps_X)    ≈ eps_{F X}

   follows from the cospan-level reflexivity ([forget_decoration_id]
   and [forget_decoration_compose]) combined with the definitional
   equality of [scfa] generators on a [DecoratedCospanCat F]-object's
   underlying cospan-category object.  The full packaging requires
   DecoratedCospanCat itself as a [Category] record (the
   [Construction/DecoratedCospan.v] module exports the API and the
   Setoid; the [Category] record packaging follows the standard pattern
   from [CospanCat]'s construction).

   ** Discussion: the general black-boxing functor

   In its full generality (Baez–Fong, Fong–Spivak), black-boxing is a
   hypergraph functor

   ⬛ : DecoratedCospanCat F  ⟶  Rel

   or, depending on the application,

   ⬛ : DecoratedCospanCat F  ⟶  Cospan(FinSet)   (Markov-process variant)
   ⬛ : DecoratedCospanCat F  ⟶  Vect_R           (linear-circuit variant)
   ⬛ : DecoratedCospanCat F  ⟶  ZX_Cat.          (quantum variant)

   Each instance specialises the codomain hypergraph category and the
   decoration-to-behaviour map.  The categorical content — that the
   construction is a hypergraph functor — is the SAME in every case:
   apex-iso transport + lax-monoidal naturality + SCFA preservation.

   This file provides the canonical forgetful black-box, the
   well-definedness lemmas at the cospan/equivalence level, and the
   pattern-recipe for instantiating the general case.

   ** Packaging as a [HypergraphFunctor] record

   [Structure/Monoidal/HypergraphFunctor.v] defines the literature
   notion of a hypergraph functor (Fong–Spivak, "Hypergraph
   Categories", arXiv:1806.08304, Def. 4.1.3): a strong symmetric
   monoidal functor between hypergraph categories preserving the SCFA
   structure on every object.

   The forgetful black-box [forget_decoration : DecoratedCospanCat F →
   CospanCat C] is, by construction, a STRICT hypergraph functor: it
   acts as the identity on objects, and on each generator it sends
   the decorated SCFA-generator back to the underlying cospan-level
   SCFA-generator (since the decoration is, by definition, an extra
   layer wrapped around the cospan).

   Formally building the [HypergraphFunctor] instance requires:

   1. [DecoratedCospanCat F] as a [Category] record (done by
   [Construction/DecoratedCospan/Category.v], parameterised by
   a [DecCospan_Coherent] instance);

   2. the SMC structure on [DecoratedCospanCat] (the
   [Construction/DecoratedCospan/Category.v] discussion section
   outlines the [DecCospan_Monoidal_Coherent] +
   [DecCospan_Symmetric_Coherent] coherence-class signatures);

   3. the [Hypergraph] structure on [DecoratedCospanCat] (chosen
   decorations on each of the four SCFA generators, lifting
   [Cospan_Hypergraph]'s scfa fields one level).

   With (1)-(3) in scope, the [HypergraphFunctor] instance for
   [forget_decoration] takes [hf_unit_iso := iso_id] and
   [hf_tensor_iso X Y := iso_id] (the functor acts as the identity
   on objects), and discharges each of the four preservation
   equations by [reflexivity] (since
   [forget_decoration_morphism (scfa_gen_dec X) = scfa_gen X]
   holds on the nose by the choice of decorated SCFA).

   This file provides the forgetful functor [forget_decoration] and
   the recipe above for packaging it as the canonical Fong-style
   "black-box is a hypergraph functor" (Theorem 6.1 in his thesis,
   arXiv:1609.05382).  The [HypergraphFunctor] instance itself is NOT
   yet constructed here: it awaits the [DecCospan_*_Coherent]
   instances of steps (1)-(3) above (the [HypergraphFunctor]
   inhabitants currently in the library are the trivial
   [Id_HypergraphFunctor] of [Structure/Monoidal/HypergraphFunctor.v]
   and the images of the forgetful bridge
   [SymmetricMonoidalFunctor_HypergraphFunctor] of
   [Functor/Structure/Monoidal/Hypergraph.v]). 

   --------
   * ** 忘记型黑箱的超图函子性

   [CospanCat C HP]  携带了规范的超图结构
   [Cospan_Hypergraph]  （在  [Construction/Cospan/HypergraphInstance.v] 中）。
   将  [DecoratedCospanCat F]  提升为完整的超图范畴 — 通过
   将余跨联范畴级 SCFA 与在每个
   [μ, η, δ, ε] 上选择的装饰配对 — 然后忘记装饰，会保留
   使得  [forget_decoration X = X] 上的 SCFA 等于  [Cospan_Hypergraph] 的 SCFA，
   因此保持性是自反的：  [F (μ_X) = μ_{F X}] 等。

   超图函子保持的严格形式：

   F (mu_X)     ≈ mu_{F X}
   F (eta_X)    ≈ eta_{F X}
   F (delta_X)  ≈ delta_{F X}
   F (eps_X)    ≈ eps_{F X}这是由余弦双范畴层次的自反性（[forget_decoration_id] 和 [forget_decoration_compose]）以及 [scfa] 生成元在 [DecoratedCospanCat F] 对象的底层余弦双范畴对象上的定义性等式结合得出的。完整的封装需要将 DecoratedCospanCat 本身作为 [Category] 记录（[Construction/DecoratedCospan.v] 模块导出 API 和 Setoid；[Category] 记录封装遵循 [CospanCat] 构造的标准模式）。

   **讨论：一般的黑盒函子**

   在其完全一般性（Baez–Fong, Fong–Spivak）下，黑盒化是一个超图函子

   ⬛ : DecoratedCospanCat F  ⟶  Rel

   或者，取决于应用,⬛ : DecoratedCospanCat F  ⟶  Cospan(FinSet)   （马尔可夫过程变体）
   ⬛ : DecoratedCospanCat F  ⟶  Vect_R           （线性电路变体）
   ⬛ : DecoratedCospanCat F  ⟶  ZX_Cat.          （量子变体）

   每个实例都专门化了余域的超图范畴和从装饰到行为的映射。范畴内容——即该构造是超图函子——在每一种情况下都是相同的：顶点同构传输 + 弱幺半群自然性 + SCFA 保持。

   该文件提供了规范的遗忘黑盒、在 cospan/等价层上的良定义性引理，以及实例化一般情形的模式配方。

   ** 打包为 [HypergraphFunctor] 记录[Structure/Monoidal/HypergraphFunctor.v] 定义了文献中超图函子（Fong–Spivak，《Hypergraph Categories》，arXiv:1806.08304，定理 4.1.3）的概念：在超图范畴之间的强对称单体函子，保持每个对象上的 SCFA 结构。

   遗忘黑箱 [forget_decoration : DecoratedCospanCat F → CospanCat C] 按构造是一个严格的超图函子：它在对象上表现为恒等，并且在每个生成元上，它将装饰过的 SCFA 生成元映射回底层的 cospan 级 SCFA 生成元（因为按定义，装饰是额外包裹在 cospan 外的一层）。

   正式构建 [HypergraphFunctor] 实例需要：

   1. 将 [DecoratedCospanCat F] 作为 [Category] 记录（由 [Construction/DecoratedCospan/Category.v] 完成，由 [DecCospan_Coherent] 实例参数化）；2. 在 [DecoratedCospanCat] 上的 SMC 结构（[Construction/DecoratedCospan/Category.v] 讨论部分概述了 [DecCospan_Monoidal_Coherent] + [DecCospan_Symmetric_Coherent] 的一致性类签名）；

   3. 在 [DecoratedCospanCat] 上的 [Hypergraph] 结构（在四个 SCFA 生成元上选择的装饰，将 [Cospan_Hypergraph] 的 SCFA 域提升一级）。

   在 (1)-(3) 范围内，[forget_decoration] 的 [HypergraphFunctor] 实例采用 [hf_unit_iso := iso_id] 和 [hf_tensor_iso X Y := iso_id]（函子在对象上作为恒等作用），并通过 [reflexivity] 解除四个保持方程的每个方程（由于 [forget_decoration_morphism (scfa_gen_dec X) = scfa_gen X] 通过装饰 SCFA 的选择严格成立）。此文件提供了遗忘函子 [forget_decoration] 以及上述将其打包为典型 Fong 风格“黑箱是超图函子”的方法（他论文中的定理 6.1，arXiv:1609.05382）。[HypergraphFunctor] 实例本身尚未在此构造：它等待上述步骤 (1)-(3) 的 [DecCospan_*_Coherent] 实例（当前库中 [HypergraphFunctor] 元素是 [Structure/Monoidal/HypergraphFunctor.v] 的平凡 [Id_HypergraphFunctor] 以及遗忘桥 [SymmetricMonoidalFunctor_HypergraphFunctor] 的 [Functor/Structure/Monoidal/Hypergraph.v] 映射）。
*)
