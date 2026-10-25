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
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Construction.Cospan.Category.
Require Import Category.Construction.DecoratedCospan.

Generalizable All Variables.

(*
   * * DecoratedCospanCat as a Category

   nLab: https://ncatlab.org/nlab/show/decorated+cospan
   Wikipedia: none-exists (the Wikipedia "Cospan" article does not
   cover decorated cospans or hypergraph categories).

   Reference: Brendan Fong, "Decorated Cospans", arXiv:1502.00872
   (Theory and Applications of Categories 30 (33), 2015, 1096-1120).
   The fact that the F-decorated cospans form a category — composition
   by pushout, identity by the empty decoration, morphisms taken up to
   apex-iso — is Fong's [3.2. Proposition].  (The earlier draft of this
   header miscited it as "Theorem 2.3"; in the paper Section 2 is about
   plain [Cospan(C)], and [2.3] is not a theorem about [FCospan].)

   [Construction/DecoratedCospan.v] supplies the data layer: the
   [DecoratedCospanArrow] record, the [dec_cospan_equiv] setoid,
   identity, and composition.  This module assembles those into a
   [Category] record [DecoratedCospanCat], discharging the four
   obligations:

   (a) [dec_cospan_compose] is [Proper] w.r.t. [dec_cospan_equiv];
   (b) identity laws  [id ∘ f ≈ f]  and  [f ∘ id ≈ f];
   (c) associativity  [(h ∘ g) ∘ f ≈ h ∘ (g ∘ f)].

   Each obligation has TWO components:

   - the COSPAN-level fact (already proven in [Cospan.Category]):
   [cospan_compose_respects_aux], [cospan_id_left/right],
   [cospan_compose_assoc];
   - the DECORATION-level fact: that the composite-decoration
   formula respects the apex-iso transport produced by the
   cospan-level proof.

   The decoration-level facts are the "lax-monoidal coherence" half
   of Fong's [3.2. Proposition].  They are not free: they depend on the
   chosen identity-decoration [id_decoration] and merge map
   [cospan_merge] being COHERENT with the lax monoidal structure on
   [F].  Fong supplies these coherences as part of the decorated-cospan
   data of his [3.1. Definition] (a lax braided monoidal functor
   [F : (C, +) -> (D, tensor)]), and the diagram chases discharging
   them are the content of the proof of his [3.2. Proposition].

   In this Coq formalisation we bundle those coherences as a
   typeclass [DecCospan_Coherent], parameterised by the same data
   used in [Construction/DecoratedCospan.v].  Concrete instances of
   [DecCospan_Coherent] correspond exactly to Fong's "decorated
   cospan structure" ([3.1. Definition]): a lax monoidal functor [F]
   with a chosen identity-decoration map and merge map, satisfying
   the unit / associativity / functoriality coherences.

   With [DecCospan_Coherent] in scope, the four [Category] obligations
   are discharged by routing the cospan part through
   [Cospan.Category]'s lemmas and the decoration part through the
   [DecCospan_Coherent] fields.

   This is the literature-correct packaging: it makes explicit the
   fact (well-known in the categorical-systems literature) that the
   decorated-cospan category is well-defined exactly when the
   decoration data satisfies a specific list of coherences. 

   --------
   * * 装饰余范畴作为一个范畴

   nLab:  https://ncatlab.org/nlab/show/decorated+cospan 
   维基百科: 无（维基百科“Cospan”条目没有涵盖装饰余范畴或超图范畴）。

   参考文献: Brendan Fong, “Decorated Cospans”, arXiv:1502.00872
   (《范畴理论与应用》30(33), 2015, 1096-1120)。
   F-装饰余范畴形成一个范畴的事实——通过推上来进行复合，通过空装饰获得恒等元，态射取到顶点同构 —— 是 Fong 的  [3.2. Proposition] 。 （本标题的早期草稿错误地引用为“定理 2.3”；在论文中，第 2 节是关于普通的  [Cospan(C)]，而  [2.3] 并不是关于  [FCospan] 的定理。）[Construction/DecoratedCospan.v] 提供数据层：[DecoratedCospanArrow] 记录、[dec_cospan_equiv] 集合态射、恒等和合成。该模块将它们组装成 [Category] 记录 [DecoratedCospanCat]，满足四个义务：

   (a) [dec_cospan_compose] 对 [dec_cospan_equiv] 是 [Proper]；
   (b) 恒等律 [id ∘ f ≈ f] 和 [f ∘ id ≈ f]；
   (c) 结合律 [(h ∘ g) ∘ f ≈ h ∘ (g ∘ f)]。

   每个义务有两个组成部分：

   - COSPAN 级的事实（已经在 [Cospan.Category] 中证明）：[cospan_compose_respects_aux]、[cospan_id_left/right]、[cospan_compose_assoc]；
   - DECORATION 级的事实：复合装饰公式遵循由 cospan 级证明产生的顶点同构传递。装饰级的事实是 Fong 的 [3.2. Proposition] 的“松单同调一致性”部分。它们不是自由的：它们依赖于所选择的恒等装饰 [id_decoration] 和合并映射 [cospan_merge] 与 [F] 上的松单结构保持一致。Fong 将这些一致性作为他 [3.1. Definition] 的装饰余半张量数据的一部分提供（一个松编织单范畴函子 [F : (C, +) -> (D, tensor)]），而对这些一致性进行图形追踪的过程就是他 [3.2. Proposition] 证明的内容。在这个 Coq 形式化中，我们将这些相干性捆绑为一个类型类 [DecCospan_Coherent]，该类型类由在 [Construction/DecoratedCospan.v] 中使用的相同数据参数化。[DecCospan_Coherent] 的具体实例完全对应于 Fong 的“装饰共尖结构”（[3.1. Definition]）：一个松单态函子 [F]，并具有选定的单位装饰映射和合并映射，满足单位/结合性/函子性一致性。 

   在 [DecCospan_Coherent] 的作用域内，通过将共尖部分通过 [Cospan.Category] 的引理以及将装饰部分通过 [DecCospan_Coherent] 的字段，可以解决四个 [Category] 义务。这是文献中正确的封装：它明确指出了一个事实（在范畴系统的文献中是众所周知的）：仅当装饰数据满足特定的协调列表时，装饰余圆范畴才是良好定义的。
*)

Section DecoratedCospanCategory.

Context {C : Category}.
Context (HP : HasPushouts C).
Context `{H_Coc : @Cocartesian C}.
Context `{MC : @Monoidal C}.
Context {D : Category}.
Context `{MD : @Monoidal D}.
Context {F : C ⟶ D}.
Context (LM : @LaxMonoidalFunctor C D MC MD F).
Context (id_decoration : forall X : C, @I D _ ~{D}~> F X).
Context (cospan_merge :
          forall (N M : C), (N ⨂[MC] M)%object ~{C}~> (N + M)%object).

(*
   * ** Coherence class for the decorated-cospan category

   Bundles the four conditions implicit in Fong's [3.1. Definition] /
   [3.2. Proposition] of "Decorated Cospans":

   (i) the decoration laws are [Proper] under the apex-iso
   transport produced by [cospan_equiv];
   (ii) the identity decoration composes coherently on the left;
   (iii) the identity decoration composes coherently on the right;
   (iv) the composite decoration is associative.

   A concrete instance — e.g. for Fong's electrical-circuit example,
   or for Baez–Fong Markov processes — provides explicit proofs of
   each, typically by direct calculation in the chosen [F] and the
   chosen identity-decoration.

   The cospan-level part of each law is proved generically below
   using [Cospan.Category]'s lemmas; the decoration-level part is
   delegated to the [DecCospan_Coherent] fields. 

   --------
   * ** 装饰余锥范畴的相干性类

   将 Fong 的“装饰余锥”的 [3.1. Definition] / [3.2. Proposition] 中隐含的四个条件捆绑在一起：

   (i) 装饰律在由 [cospan_equiv] 产生的顶点同构传输下是 [Proper]；
   (ii) 单位装饰在左侧组合时相干；
   (iii) 单位装饰在右侧组合时相干；
   (iv) 复合装饰是结合的。

   一个具体实例——例如用于 Fong 的电路示例，或 Baez–Fong 马尔可夫过程——提供每个条件的显式证明，通常通过在选定的 [F] 和选定的单位装饰中直接计算得到。每条定律的余范围部分在下面通过 [Cospan.Category] 的引理进行了一般性证明；装饰层部分则委托给 [DecCospan_Coherent] 的领域。
*)

Class DecCospan_Coherent : Type := {
  (*
   * Apex-iso transport for decoration equivalence: if two decorated
   cospans agree at the cospan level (via some [phi]) and the
   composite-decoration formula on either side transports through
   [F phi], they agree.

   Concretely this is the field that says: when forming
   [dec_cospan_compose g f] vs [dec_cospan_compose g' f'] for
   pairwise-equivalent decorated cospans, the apex iso between the
   two composite pushouts (built by [cospan_compose_respects_aux])
   transports the decoration correctly. 

   --------
   * 顶点同构的装饰等价传输：如果两个装饰的余半群在余半群层面上相同（通过某个 [phi]），并且任意一侧的复合装饰公式可通过 [F phi] 传输，那么它们相同。

   具体来说，这就是指：在为成对等价的装饰余半群形成 [dec_cospan_compose g f] 与 [dec_cospan_compose g' f'] 时，两个复合推挤（由 [cospan_compose_respects_aux] 构建）之间的顶点同构会正确传输装饰。
*)
  dc_compose_respects_dec :
    forall {X Y Z : C}
           (g g' : DecoratedCospanArrow Y Z)
           (f f' : DecoratedCospanArrow X Y)
           (Hf : dec_cospan_equiv f f')
           (Hg : dec_cospan_equiv g g'),
      fmap[F] (to (projT1 (cospan_compose_respects_aux HP
                              (dc_cospan g) (dc_cospan g')
                              (dc_cospan f) (dc_cospan f')
                              (dce_cospan_eq Hf) (dce_cospan_eq Hg))))
        ∘ dec_compose_decoration HP LM cospan_merge g f
      ≈ dec_compose_decoration HP LM cospan_merge g' f';

  (*
   * Identity-decoration left coherence: the composite-decoration of
   [(id_decoration Y) ∘ f] equals [dc_decoration f] after transport
   along the cospan-level identity-left apex iso. 

   --------
   * 恒等-装饰左连贯性：沿共尖顶点恒等左同构传输后，[(id_decoration Y) ∘ f] 的复合装饰等于 [dc_decoration f]。
*)
  dc_id_left_dec :
    forall {X Y : C} (f : DecoratedCospanArrow X Y),
      fmap[F] (to (projT1 (cospan_id_left HP (dc_cospan f))))
        ∘ dec_compose_decoration HP LM cospan_merge
            (dec_cospan_id id_decoration Y) f
      ≈ dc_decoration f;

  (*
   * Identity-decoration right coherence: symmetric, for f ∘ id. 

   --------
   * 恒等装饰右一致性：对称的，适用于 f ∘ id。
*)
  dc_id_right_dec :
    forall {X Y : C} (f : DecoratedCospanArrow X Y),
      fmap[F] (to (projT1 (cospan_id_right HP (dc_cospan f))))
        ∘ dec_compose_decoration HP LM cospan_merge
            f (dec_cospan_id id_decoration X)
      ≈ dc_decoration f;

  (*
   * Associativity of the decoration: the composite-decoration of
   [(h ∘ g) ∘ f] equals that of [h ∘ (g ∘ f)] after transport along
   the cospan-level associativity apex iso. 

   --------
   * 装饰的结合性：沿共锥层级结合顶点同构传输后，[(h ∘ g) ∘ f] 的复合装饰等于 [h ∘ (g ∘ f)] 的复合装饰。
*)
  dc_compose_assoc_dec :
    forall {X Y Z W : C}
           (h : DecoratedCospanArrow Z W)
           (g : DecoratedCospanArrow Y Z)
           (f : DecoratedCospanArrow X Y),
      fmap[F] (to (projT1 (cospan_compose_assoc HP
                              (dc_cospan h)
                              (dc_cospan g)
                              (dc_cospan f))))
        ∘ dec_compose_decoration HP LM cospan_merge
            h (dec_cospan_compose HP LM cospan_merge g f)
      ≈ dec_compose_decoration HP LM cospan_merge
          (dec_cospan_compose HP LM cospan_merge h g) f
}.

(*
   * ** The Category record

   With [DecCospan_Coherent] in scope, all four [Category] obligations
   pair the corresponding cospan-level lemma with the matching
   decoration-level coherence field. 

   --------
   * ** 该类别纪录

   在[DecCospan_Coherent]范围内，这四项义务[Category]承担
   将相应的Cospan引理与匹配的引理配对
   装饰级相干场。
*)

Context `{DCC : DecCospan_Coherent}.

Set Default Proof Using "All".

(*
   * Proper instance for composition.  The cospan part comes from
   [cospan_compose_respects_aux]; the decoration part from
   [dc_compose_respects_dec]. 

   --------
   * 适合组合的实例。cospan 部分来自 [cospan_compose_respects_aux]；装饰部分来自 [dc_compose_respects_dec]。
*)
Lemma dec_cospan_compose_respects_aux
      {X Y Z : C}
      (g g' : DecoratedCospanArrow Y Z) (f f' : DecoratedCospanArrow X Y)
      (Hf : dec_cospan_equiv f f') (Hg : dec_cospan_equiv g g') :
  dec_cospan_equiv
    (dec_cospan_compose HP LM cospan_merge g f)
    (dec_cospan_compose HP LM cospan_merge g' f').
Proof.
  unshelve econstructor.
  - exact (cospan_compose_respects_aux HP
             (dc_cospan g) (dc_cospan g')
             (dc_cospan f) (dc_cospan f')
             (dce_cospan_eq Hf) (dce_cospan_eq Hg)).
  - simpl.
    exact (dc_compose_respects_dec g g' f f' Hf Hg).
Qed.

#[export] Program Instance dec_cospan_compose_respects {X Y Z : C} :
  Proper (equiv ==> equiv ==> equiv)
    (@dec_cospan_compose C HP MC D MD F LM H_Coc cospan_merge X Y Z).
Next Obligation.
  proper.
  now apply dec_cospan_compose_respects_aux.
Qed.

(*
   * Identity laws and associativity, each pairing the cospan-level
   lemma with the matching coherence field. 

   --------
   * 身份律和结合律，每个将余跨度级别的引理与匹配的相干场配对。
*)

Lemma dec_cospan_id_left {X Y : C} (f : DecoratedCospanArrow X Y) :
  dec_cospan_equiv
    (dec_cospan_compose HP LM cospan_merge (dec_cospan_id id_decoration Y) f)
    f.
Proof.
  unshelve econstructor.
  - exact (cospan_id_left HP (dc_cospan f)).
  - simpl. exact (dc_id_left_dec f).
Qed.

Lemma dec_cospan_id_right {X Y : C} (f : DecoratedCospanArrow X Y) :
  dec_cospan_equiv
    (dec_cospan_compose HP LM cospan_merge f (dec_cospan_id id_decoration X))
    f.
Proof.
  unshelve econstructor.
  - exact (cospan_id_right HP (dc_cospan f)).
  - simpl. exact (dc_id_right_dec f).
Qed.

Lemma dec_cospan_compose_assoc {X Y Z W : C}
      (h : DecoratedCospanArrow Z W)
      (g : DecoratedCospanArrow Y Z)
      (f : DecoratedCospanArrow X Y) :
  dec_cospan_equiv
    (dec_cospan_compose HP LM cospan_merge h
       (dec_cospan_compose HP LM cospan_merge g f))
    (dec_cospan_compose HP LM cospan_merge
       (dec_cospan_compose HP LM cospan_merge h g) f).
Proof.
  unshelve econstructor.
  - exact (cospan_compose_assoc HP (dc_cospan h) (dc_cospan g) (dc_cospan f)).
  - simpl. exact (dc_compose_assoc_dec h g f).
Qed.

Lemma dec_cospan_compose_assoc_sym {X Y Z W : C}
      (h : DecoratedCospanArrow Z W)
      (g : DecoratedCospanArrow Y Z)
      (f : DecoratedCospanArrow X Y) :
  dec_cospan_equiv
    (dec_cospan_compose HP LM cospan_merge
       (dec_cospan_compose HP LM cospan_merge h g) f)
    (dec_cospan_compose HP LM cospan_merge h
       (dec_cospan_compose HP LM cospan_merge g f)).
Proof.
  apply dec_cospan_equiv_sym, dec_cospan_compose_assoc.
Qed.

(*
   * ** [DecoratedCospanCat] as a [Category] record 

   --------
   * **  [DecoratedCospanCat]  作为  [Category]  记录
*)

Program Definition DecoratedCospanCat : Category := {|
  obj      := @obj C;
  hom      := fun X Y => DecoratedCospanArrow X Y;
  homset   := fun X Y => DecoratedCospanArrow_Setoid;
  id       := fun X => dec_cospan_id id_decoration X;
  compose  := fun X Y Z g f => dec_cospan_compose HP LM cospan_merge g f;
  compose_respects := fun X Y Z => @dec_cospan_compose_respects X Y Z;
  id_left  := fun X Y f => dec_cospan_id_left f;
  id_right := fun X Y f => dec_cospan_id_right f;
  comp_assoc := fun X Y Z W f g h => dec_cospan_compose_assoc f g h;
  comp_assoc_sym := fun X Y Z W f g h => dec_cospan_compose_assoc_sym f g h
|}.

End DecoratedCospanCategory.

Arguments DecoratedCospanCat
  {C} HP {H_Coc} {MC} {D} {MD} {F} LM id_decoration cospan_merge {DCC}.

(*
   * ** Path to the full symmetric monoidal layer

   Given [DecoratedCospanCat], the next-layer structure (Fong, [3.5.
   Theorem] of "Decorated Cospans") is a SYMMETRIC MONOIDAL category —
   in fact a HYPERGRAPH category — extending the underlying
   [CospanCat]'s SMC structure with decoration data:

   - tensor of two decorated cospans: tensor the cospans (via
   [Cospan_Monoidal]) and tensor the decorations via [lax_ap[F]];

   - unitors and associator: inherited from [Cospan_Monoidal]
   (which transports cleanly to the decoration side via the
   lax-monoidal unit and associativity coherences);

   - braid: inherited from [Cospan_BraidedMonoidal] plus the
   symmetric coherence [bimap d_f d_g ∘ braid = braid ∘ bimap d_g d_f]
   (which holds when [F] is a SYMMETRIC lax monoidal functor —
   Fong's standing assumption).

   The categorical infrastructure for stating each obligation is
   already in place: [Cospan_Monoidal], [Cospan_BraidedMonoidal],
   [Cospan_SymmetricMonoidal] live in [Construction/Cospan/Symmetric.v]
   and supply the cospan-level part of every equation.  The
   decoration side is, on every equation, a routine appeal to one of:

   - [lax_monoidal_unit_left], [lax_monoidal_unit_right]
   (for the unitor coherences);
   - [lax_monoidal_assoc] (for the associator coherence);
   - the symmetric-lax-monoidal property [F (braid) = braid] (for
   the braid coherence — this is an EXTRA assumption on [F]
   beyond plain [LaxMonoidalFunctor]).

   Packaging-wise, the cleanest formulation mirrors
   [DecCospan_Coherent]: bundle the decoration-side coherences into a
   class [DecCospan_Monoidal_Coherent] and a class
   [DecCospan_Symmetric_Coherent], then [Program Instance] them as
   [DecoratedCospan_Monoidal] / [DecoratedCospan_SymmetricMonoidal].

   Hypergraph upgrade: with the [Cospan_Hypergraph] instance on
   [CospanCat], the canonical hypergraph structure on
   [DecoratedCospanCat] is the same cospan-level SCFA wrapped with
   chosen decorations on each generator.  The four
   [Hypergraph]-class obligations follow once the underlying SMC is
   in place.

   ** Sticking point analysis

   The implementation cost of the SMC layer is roughly the same as
   [Construction/Cospan/Symmetric.v] (~400 lines), repeated on the
   decoration side.  Most of the work is bookkeeping: each obligation
   is "do the cospan-level fact, then transport along the lax
   coherence".  No genuinely new mathematics enters — the decoration
   layer is, in Fong's words, "natively monoidal" because [F] is.

   The implementation is mechanical but volumetric; we expose the
   [DecoratedCospanCat] [Category] record (above) as the primary
   landing point and document the SMC + Hypergraph upgrades as
   follow-up work with concrete coherence-class signatures.  Once a
   concrete application — Baez–Fong circuits, Markov processes — is
   formalised, the corresponding coherence-class instance is the
   bulk of the work; the SMC + Hypergraph instances themselves are
   then a thin wrapping. 

   --------
   * ** 全对称单体层的路径

   给定 [DecoratedCospanCat]，下一层的结构（Fong，[3.5. 定理] 《装饰余积》）是一个对称单体范畴——实际上是一个超图范畴——将底层 [CospanCat] 的 SMC 结构扩展为带有装饰数据的结构：

   - 两个装饰余积的张量：通过 [Cospan_Monoidal] 对余积进行张量操作，通过 [lax_ap[F] 对装饰进行张量操作；

   - 单位子和结合子：继承自 [Cospan_Monoidal]（通过松单体单位和结合一致性可以干净地传递到装饰端）；

   - 编织子：继承自 [Cospan_BraidedMonoidal]，加上对称一致性 [bimap d_f d_g ∘ braid = braid ∘ bimap d_g d_f]（当 [F] 是一个对称松单体函子时成立——这是 Fong 的基本假设）。陈述每个义务的范畴基础设施已经到位：[Cospan_Monoidal]、[Cospan_BraidedMonoidal]、[Cospan_SymmetricMonoidal] 位于 [Construction/Cospan/Symmetric.v]，并提供每个方程的余范围层部分。装饰部分在每个方程中都是对以下之一的例行调用：

   - [lax_monoidal_unit_left]、[lax_monoidal_unit_right] （用于幺半群同调一致性）；
   - [lax_monoidal_assoc] （用于结合子一致性）；
   - 对称-松弛-单体性质 [F (braid) = braid] （用于编织一致性——这是在普通 [LaxMonoidalFunctor] 之外对 [F] 的额外假设）。

   在打包方面，最清晰的表述是模仿 [DecCospan_Coherent]：将装饰方的一致性捆绑到类 [DecCospan_Monoidal_Coherent] 和类 [DecCospan_Symmetric_Coherent]，然后将它们作为 [DecoratedCospan_Monoidal] / [DecoratedCospan_SymmetricMonoidal] 来 [Program Instance]。超图升级：在 [Cospan_Hypergraph] 实例于 [CospanCat] 上的情况下，[DecoratedCospanCat] 上的标准超图结构是同一个余跨度级 SCFA，每个生成元上包裹了选定的装饰。 一旦基础 SMC 就位，四个 [Hypergraph] 类义务也就随之而来。

   ** 瓶颈分析

   SMC 层的实现成本大致与 [Construction/Cospan/Symmetric.v] 相同（约 400 行），在装饰层也要重复一遍。大部分工作是簿记：每个义务是“做余跨度级事实，然后沿着松弛一致性传输”。没有真正新的数学内容引入——正如 Fong 所说，装饰层是“天生单体的”，因为 [F] 是这样。实现是机械化的，但具有体积性；我们将 [DecoratedCospanCat] [Category] 记录（如上）作为主要的落地点，并将 SMC + 超图升级记录为后续工作，附有具体的相干类签名。一旦具体应用——Baez–Fong 电路、马尔可夫过程——被形式化，对应的相干类实例就是工作的主要部分；而 SMC + 超图实例本身则只是薄薄的包装。
*)

(*
   * ** Discussion: the four coherence fields

   Fong's "Decorated Cospans" paper proves each of the four
   [DecCospan_Coherent] fields directly in the [F = Set] case (where
   decorations are literal elements of [F N]), using:

   - [dc_id_left_dec] / [dc_id_right_dec]: the lax monoidal-unit
   coherences [lax_monoidal_unit_left] / [lax_monoidal_unit_right]
   (van de Wetering's restatement; see [Functor/Structure/Monoidal.v]);

   - [dc_compose_assoc_dec]: the lax monoidal-associativity
   coherence [lax_monoidal_assoc];

   - [dc_compose_respects_dec]: the naturality of [lax_ap] under
   the apex-iso transport, combined with [fmap]'s respectfulness.

   Each is a short calculation in the lax monoidal data, but the
   statements are bulky because they refer to the pushout-mediator
   iso explicitly.  We have packaged them as an OPAQUE typeclass so
   downstream sites discharge them once per concrete decoration
   structure (rather than having every cospan-category user
   re-derive them).

   A concrete instance — for the trivial decoration [F = const(I_D)] —
   is the canonical "no-decoration" case where every coherence holds
   by the [const]-functor laws + [lax_pure ∘ ... = lax_pure] collapses.
   More interesting instances (Baez–Fong electrical circuits, Fong's
   Markov processes) provide bespoke proofs that we leave to the
   application-specific downstream files. 

   --------
   * ** 讨论：四个相干场

   Fong 的《装饰余弦》论文在 [F = Set] 情况下直接证明了四个
   [DecCospan_Coherent] 场（其中装饰是 [F N] 的字面元素），使用了：

   - [dc_id_left_dec] / [dc_id_right_dec]：松单元相干性 [lax_monoidal_unit_left] / [lax_monoidal_unit_right]
   （van de Wetering 的重新表述；见 [Functor/Structure/Monoidal.v]）；

   - [dc_compose_assoc_dec]：松单元结合性相干性 [lax_monoidal_assoc]；

   - [dc_compose_respects_dec]：[lax_ap] 在顶点同构传输下的自然性，与 [fmap] 的遵从性结合。每个计算都是在松单体数据中的简短计算，但由于明确引用了推挤-中介同构，陈述显得笨重。我们已将它们封装为一个 OPAQUE 类型类，因此下游站点在每个具体的装饰结构中只需执行一次（而不是让每个余范畴用户重新推导它们）。

   一个具体实例——对于平凡装饰 [F = const(I_D)]——是典型的“无装饰”情况，其中通过 [const] 函子定律 + [lax_pure ∘ ... = lax_pure] 崩塌，所有相干性都成立。更有趣的实例（Baez–Fong 电路、Fong 的马尔可夫过程）提供了定制的证明，我们将其留给应用特定的下游文件。
*)
