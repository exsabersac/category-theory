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
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Construction.Cospan.Category.
Require Import Category.Construction.Cospan.Hypergraph.
Require Import Category.Construction.Cospan.Symmetric.
Require Import Category.Construction.DecoratedCospan.
Require Import Category.Construction.DecoratedCospan.Category.

Generalizable All Variables.

(*
   * * Symmetric monoidal structure on [DecoratedCospanCat]

   Reference: Brendan Fong, “Decorated Cospans”, arXiv:1502.00872,
   Theorem 3.5 (the decorated-cospan category is a symmetric monoidal
   hypergraph category whenever the decorating functor is a lax braided
   (symmetric) monoidal functor).
   nLab: https://ncatlab.org/nlab/show/decorated+cospan
   Wikipedia: https://en.wikipedia.org/wiki/Symmetric_monoidal_category

   This module assembles the symmetric monoidal hierarchy on
   [DecoratedCospanCat] by layering decoration coherences on top of the
   [Cospan_*] structural witnesses from [Construction/Cospan/Symmetric.v].

   Following the [DecCospan_Coherent] pattern established in
   [Construction/DecoratedCospan/Category.v], each layer bundles its
   decoration-side coherence requirements as a typeclass, parameterised
   by the same lax-monoidal data ([F], [LM], [id_decoration],
   [cospan_merge]) used to define [DecoratedCospanCat] itself.

   Concrete instances of each coherence class correspond to the
   explicit constructions one finds in the categorical-systems
   literature (Fong's circuits, Baez–Fong Markov processes,
   Fong–Spivak signal-flow diagrams).  The structural propositions of
   this file are independent of any concrete instance; they organise
   the bookkeeping so that a downstream consumer supplying the
   coherence-class instance receives the full symmetric monoidal
   hypergraph structure for free.

   ** Layered class architecture

   [DecCospan_Coherent]         (Category obligations — already in
   [DecoratedCospan/Category.v])
   ↓ provides
   [DecCospan_Bifunctor_Coherent] (decoration-side bifunctor laws)
   ↓ provides
   [DecCospan_Monoidal_Coherent]  (unitor/associator decoration coherence)
   ↓ provides
   [DecCospan_Braided_Coherent]   (braid decoration coherence; requires
   F to be symmetric-lax-monoidal)
   ↓ provides
   [DecCospan_Symmetric_Coherent] (symmetric braid coherence)

   Each step pairs the cospan-level fact (already in
   [Construction/Cospan/Symmetric.v]) with the matching decoration-level
   coherence. 

   --------
   * * [DecoratedCospanCat] 的对称幺半群结构

   参考文献：Brendan Fong，《Decorated Cospans》，arXiv:1502.00872，
   定理 3.5（当装饰函子是一个松弛编织（对称）幺半群函子时，装饰余积范畴是一个对称幺半群超图范畴）。
   nLab: https://ncatlab.org/nlab/show/decorated+cospan
   维基百科: https://en.wikipedia.org/wiki/Symmetric_monoidal_category

   该模块通过在 [Cospan_*] 的结构证明之上叠加装饰一致性，组装 [DecoratedCospanCat] 的对称幺半群层次结构。

   按照在 [Construction/DecoratedCospan/Category.v] 中建立的 [DecCospan_Coherent] 模式，每一层将其装饰侧的一致性要求打包为一个类型类，由定义 [DecoratedCospanCat] 本身所使用的相同松弛幺半群数据（[F]、[LM]、[id_decoration]、[cospan_merge]）参数化。每种相干类的具体实例对应于在范畴系统文献中可以找到的显式构造（Fong 的电路、Baez–Fong 马尔可夫过程、Fong–Spivak 信号流图）。该文件的结构命题独立于任何具体实例；它们组织账簿记录，以便下游使用者提供相干类实例时，可以免费获得完整的对称单体超图结构。

   ** 分层类架构[DecCospan_Coherent]          （类别义务 — 已在 [DecoratedCospan/Category.v] 中）
   ↓ 提供
   [DecCospan_Bifunctor_Coherent]  （装饰侧双函子律）
   ↓ 提供
   [DecCospan_Monoidal_Coherent]   （单位子/结合子装饰一致性）
   ↓ 提供
   [DecCospan_Braided_Coherent]    （编织装饰一致性；需要 F 是对称-松模的）
   ↓ 提供
   [DecCospan_Symmetric_Coherent]  （对称编织一致性）

   每一步将 cospan 级事实（已在 [Construction/Cospan/Symmetric.v] 中）与匹配的装饰级一致性配对。
*)

Section DecoratedCospanSymmetric.

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

(*
   * ** Decorated cospan tensor

   Given decorated cospans [f : X → X'] (apex [Nf], decoration [d_f])
   and [g : Y → Y'] (apex [Ng], decoration [d_g]), the tensor cospan
   [f ⊗ g : X+Y → X'+Y'] has:

   - cospan part: [cospan_tensor (dc_cospan f) (dc_cospan g)] with apex
   [Nf + Ng] (built in [Construction/Cospan/Hypergraph.v]);
   - decoration: the composite

   I  -unit_left⁻¹->  I ⨂ I  -d_f ⨂ d_g->  F Nf ⨂ F Ng
   -lax_ap->  F (Nf ⨂_C Ng)  -F (cospan_merge)->  F (Nf + Ng)

   That is, the same combinator used in [dec_compose_decoration]
   applied to the apex pair. 

   --------
   * ** 装饰余跨张量

   给定装饰余跨 [f : X → X']（顶点 [Nf]，装饰 [d_f]）
   和 [g : Y → Y']（顶点 [Ng]，装饰 [d_g]），张量余跨 [f ⊗ g : X+Y → X'+Y'] 具有：

   - 余跨部分：[cospan_tensor (dc_cospan f) (dc_cospan g)]，顶点为
   [Nf + Ng]（在 [Construction/Cospan/Hypergraph.v] 中构建）；
   - 装饰：复合

   I  -unit_left⁻¹->  I ⨂ I  -d_f ⨂ d_g->  F Nf ⨂ F Ng
   -lax_ap->  F (Nf ⨂_C Ng)  -F (cospan_merge)->  F (Nf + Ng)

   即，在顶点对上使用 [dec_compose_decoration] 中相同的组合器。
*)

Definition dec_tensor_decoration
  {X X' Y Y' : C}
  (f : DecoratedCospanArrow X X')
  (g : DecoratedCospanArrow Y Y')
  : @I D _ ~{D}~> F (cospan_apex (cospan_tensor (dc_cospan f) (dc_cospan g))) :=
  let Nf := cospan_apex (dc_cospan f) in
  let Ng := cospan_apex (dc_cospan g) in
  fmap[F] (cospan_merge Nf Ng)
    ∘ lax_ap[F]
    ∘ bimap (dc_decoration f) (dc_decoration g)
    ∘ from (@unit_left D _ (@I D _)).

Definition dec_cospan_tensor
  {X X' Y Y' : C}
  (f : DecoratedCospanArrow X X')
  (g : DecoratedCospanArrow Y Y')
  : DecoratedCospanArrow (X + Y) (X' + Y') := {|
  dc_cospan := cospan_tensor (dc_cospan f) (dc_cospan g);
  dc_decoration := dec_tensor_decoration f g
|}.

(*
   * ** Bifunctor coherence class

   The Bifunctor instance on [DecoratedCospanCat] requires three
   decoration-side coherences (the cospan-side counterparts already
   live in [Construction/Cospan/Hypergraph.v]):

   (i) [dec_tensor_id_dec]: tensor-of-identities decoration equals
   identity decoration up to apex iso;

   (ii) [dec_tensor_respects_dec]: pairwise [dec_cospan_equiv]
   transports through the tensor;

   (iii) [dec_tensor_compose_dec]: tensor distributes over composition
   (interchange law on the decoration side).

   Each is a routine appeal to the lax-monoidal naturality of [F]
   combined with the apex-iso transport produced by the corresponding
   [Cospan/Hypergraph.v] lemma. 

   --------
   * ** 双函子一致性类

   在  [DecoratedCospanCat] 上的双函子实例需要三个
   装饰侧的一致性（余刺侧的对应关系已经
   存在于  [Construction/Cospan/Hypergraph.v] ）：

   (i)  [dec_tensor_id_dec] : 恒等装饰的张量等于
   顶点同构下的恒等装饰；

   (ii)  [dec_tensor_respects_dec] : 成对的  [dec_cospan_equiv] 
   通过张量进行传输；

   (iii)  [dec_tensor_compose_dec] : 张量在复合上分配
   （装饰侧的交换律）。

   每一项都是对 [F] 的松单态自然性结合对应
   [Cospan/Hypergraph.v] 引理产生的顶点同构传输的常规调用。
*)

Class DecCospan_Bifunctor_Coherent : Type := {
  (*
   * Decoration coherence for [tensor_id]: the tensor of two identity
   decorated cospans equals the identity decorated cospan on the
   coproduct, after transport along the cospan-level iso. 

   --------
   * [tensor_id] 的装饰一致性：两个单位装饰余积范畴的张量等于沿余积范畴层级同构传输后的余积上的单位装饰余积范畴。
*)
  dec_tensor_id_dec :
    forall (X Y : C),
      fmap[F] (to (projT1 (cospan_tensor_id X Y)))
        ∘ dec_tensor_decoration
            (dec_cospan_id id_decoration X)
            (dec_cospan_id id_decoration Y)
      ≈ id_decoration (X + Y)%object;

  (*
   * Decoration coherence for [tensor_respects]: pairwise equivalent
   decorated cospans yield equivalent tensors, with the decoration
   transporting along the per-component apex isos. 

   --------
   * [tensor_respects] 的装饰一致性：成对等价  
   装饰的共尖范畴产生等价的张量，装饰沿每个分量顶点同构传递。
*)
  dec_tensor_respects_dec :
    forall {X Y X' Y' : C}
           (f f' : DecoratedCospanArrow X Y)
           (g g' : DecoratedCospanArrow X' Y')
           (Hf : dec_cospan_equiv f f')
           (Hg : dec_cospan_equiv g g'),
      fmap[F] (to (projT1 (cospan_tensor_respects
                              (dc_cospan f) (dc_cospan f')
                              (dc_cospan g) (dc_cospan g')
                              (dce_cospan_eq Hf) (dce_cospan_eq Hg))))
        ∘ dec_tensor_decoration f g
      ≈ dec_tensor_decoration f' g';

  (*
   * Decoration interchange: the tensor of two composites equals the
   composite of two tensors, with decorations matching after the
   cospan-level apex-iso transport. 

   --------
   * 装饰交换：两个复合的张量等于两个张量的复合，在顶点同构跨越余锥层次后，装饰匹配。
*)
  dec_tensor_compose_compat_dec :
    forall {X Y Z X' Y' Z' : C}
           (g : DecoratedCospanArrow Y Z) (f : DecoratedCospanArrow X Y)
           (g' : DecoratedCospanArrow Y' Z') (f' : DecoratedCospanArrow X' Y'),
      fmap[F] (to (projT1 (cospan_tensor_compose_compat HP
                              (dc_cospan g) (dc_cospan f)
                              (dc_cospan g') (dc_cospan f'))))
        ∘ dec_tensor_decoration
            (dec_cospan_compose HP LM cospan_merge g f)
            (dec_cospan_compose HP LM cospan_merge g' f')
      ≈ dec_compose_decoration HP LM cospan_merge
          (dec_cospan_tensor g g')
          (dec_cospan_tensor f f')
}.

Context `{DCBC : DecCospan_Bifunctor_Coherent}.

Set Default Proof Using "All".

(*
   * ** Bifunctor-level lemmas, pairing cospan + decoration coherences 

   --------
   * ** 双函子级引理，成对余格 + 装饰一致性
*)

Lemma dec_cospan_tensor_id (X Y : C) :
  dec_cospan_equiv
    (dec_cospan_tensor
       (dec_cospan_id id_decoration X)
       (dec_cospan_id id_decoration Y))
    (dec_cospan_id id_decoration (X + Y)%object).
Proof.
  unshelve econstructor.
  - exact (cospan_tensor_id X Y).
  - simpl. exact (dec_tensor_id_dec X Y).
Qed.

Lemma dec_cospan_tensor_respects
      {X Y X' Y' : C}
      (f f' : DecoratedCospanArrow X Y)
      (g g' : DecoratedCospanArrow X' Y')
      (Hf : dec_cospan_equiv f f')
      (Hg : dec_cospan_equiv g g') :
  dec_cospan_equiv
    (dec_cospan_tensor f g)
    (dec_cospan_tensor f' g').
Proof.
  unshelve econstructor.
  - exact (cospan_tensor_respects
             (dc_cospan f) (dc_cospan f')
             (dc_cospan g) (dc_cospan g')
             (dce_cospan_eq Hf) (dce_cospan_eq Hg)).
  - simpl. exact (dec_tensor_respects_dec f f' g g' Hf Hg).
Qed.

Lemma dec_cospan_tensor_compose_compat
      {X Y Z X' Y' Z' : C}
      (g : DecoratedCospanArrow Y Z) (f : DecoratedCospanArrow X Y)
      (g' : DecoratedCospanArrow Y' Z') (f' : DecoratedCospanArrow X' Y') :
  dec_cospan_equiv
    (dec_cospan_tensor
       (dec_cospan_compose HP LM cospan_merge g f)
       (dec_cospan_compose HP LM cospan_merge g' f'))
    (dec_cospan_compose HP LM cospan_merge
       (dec_cospan_tensor g g')
       (dec_cospan_tensor f f')).
Proof.
  unshelve econstructor.
  - exact (cospan_tensor_compose_compat HP
             (dc_cospan g) (dc_cospan f)
             (dc_cospan g') (dc_cospan f')).
  - simpl. exact (dec_tensor_compose_compat_dec g f g' f').
Qed.

(*
   * ** [DecoratedCospan_Bifunctor]: the Bifunctor on [DecoratedCospanCat] 

   --------
   * **  [DecoratedCospan_Bifunctor]：在  [DecoratedCospanCat] 上的双函子
*)

#[export] Program Instance dec_cospan_tensor_respects_proper
  {X Y X' Y' : C} :
  Proper (equiv ==> equiv ==> equiv)
    (@dec_cospan_tensor X X' Y Y').
Next Obligation.
  proper.
  now apply dec_cospan_tensor_respects.
Qed.

Program Definition DecoratedCospan_Bifunctor
  : ((DecoratedCospanCat HP LM id_decoration cospan_merge)
       ∏ (DecoratedCospanCat HP LM id_decoration cospan_merge))
    ⟶ (DecoratedCospanCat HP LM id_decoration cospan_merge) := {|
  fobj := fun xy => @Cospan_tensor_obj C H_Coc (fst xy) (snd xy);
  fmap := fun xy uv fg => dec_cospan_tensor (fst fg) (snd fg)
|}.
Next Obligation.
  proper; simpl in *.
  apply dec_cospan_tensor_respects; assumption.
Qed.
Next Obligation.
  apply dec_cospan_tensor_id.
Qed.
Next Obligation.
  apply dec_cospan_tensor_compose_compat.
Qed.

(*
   * ** Decorated lift of a C-morphism

   Given [f : X ~> Y] in [C], the natural decorated-cospan lift is
   [mor_as_cospan f] (apex = Y) carrying [id_decoration Y].  This is
   the canonical “structural” decoration, used to lift the
   unitor/associator/braid of [CospanCat] to [DecoratedCospanCat]. 

   --------
   * ** C-态射的装饰提升

   给定  [f : X ~> Y]  在  [C] 中，自然的装饰余笛提升是
   [mor_as_cospan f]  （顶点 = Y）携带  [id_decoration Y] 。 这是
   规范的“结构”装饰，用于将  [CospanCat]  的单位子/结合子/编织子提升到  [DecoratedCospanCat] 。
*)

Definition dec_mor_as_cospan {X Y : C} (f : X ~> Y)
  : DecoratedCospanArrow X Y :=
  {| dc_cospan := mor_as_cospan f;
     dc_decoration := id_decoration Y |}.

End DecoratedCospanSymmetric.

(*
   * ** Path to the full SMC layer

   The Bifunctor instance above is the first of the four pieces of the
   decorated symmetric monoidal hypergraph structure.  The remaining
   three (Monoidal, BraidedMonoidal, SymmetricMonoidal) follow the same
   layered-coherence pattern:

   - [DecCospan_Monoidal_Coherent] bundles the unitor + associator
   decoration coherences.  The cospan-level facts come from
   [Cospan_Monoidal] in [Construction/Cospan/Hypergraph.v].

   - [DecCospan_Braided_Coherent] bundles the braid-decoration
   coherence.  The cospan-level fact comes from
   [Cospan_BraidedMonoidal] in [Construction/Cospan/Symmetric.v].
   The decoration-side coherence requires [F] to be symmetric in the
   sense that [lax_ap[F] ∘ braid ≈ F(braid) ∘ lax_ap[F]] — i.e. [F]
   is a SYMMETRIC lax monoidal functor.

   - [DecCospan_Symmetric_Coherent] bundles the braid-involution
   decoration coherence — typically automatic from the braided
   coherence and [paws_invol].

   Once those three classes are populated, the [Monoidal /
   BraidedMonoidal / SymmetricMonoidal] instances on
   [DecoratedCospanCat] are constructed in the same pairing-pattern
   as the Bifunctor above: each Program Obligation pairs the
   cospan-level lemma with the matching coherence-class field. 

   --------
   * ** 完整SMC层的路径

   上面的 Bifunctor 实例是装饰对称幺半图结构的四个部分中的第一个。剩下的三个（Monoidal、BraidedMonoidal、SymmetricMonoidal）遵循相同的分层一致性模式：

   - [DecCospan_Monoidal_Coherent] 打包了单位器 + 结合器的装饰一致性。余楔层面的事实来自 [Construction/Cospan/Hypergraph.v] 中的 [Cospan_Monoidal]。

   - [DecCospan_Braided_Coherent] 打包了编织装饰的一致性。余楔层面的事实来自 [Construction/Cospan/Symmetric.v] 中的 [Cospan_BraidedMonoidal]。装饰端的一致性要求 [F] 在 [lax_ap[F] ∘ braid ≈ F(braid) ∘ lax_ap [F] 的意义上是对称的——也就是说，[F] 是一个对称松幺半函子。- [DecCospan_Symmetric_Coherent] 包含了编织-反演装饰一致性——通常由编织的一致性和 [paws_invol] 自动提供。

   一旦这三个类被填充，[Monoidal / BraidedMonoidal / SymmetricMonoidal] 在 [DecoratedCospanCat] 上的实例就按照与上面 Bifunctor 相同的配对模式构建：每个程序义务将余积范围层面的引理与匹配的一致性类字段配对。
*)
