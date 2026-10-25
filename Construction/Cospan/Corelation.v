Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Construction.Span.Category.
Require Import Category.Construction.Cospan.Category.

Generalizable All Variables.

(* * * Corelations: jointly-epic cospans / * * 相关性：联合史诗余积 *)

(*
 nLab:      https://ncatlab.org/nlab/show/corelation
 Wikipedia: none-exists (no category-theoretic article; the page title
 "Corelation" redirects to the statistics article on correlation)

 A corelation from [X] to [Y] is a cospan [X -in1-> N <-in2- Y] whose
 copairing
 [in1, in2] := cospan_in1 ▽ cospan_in2 : X + Y ~> N
 is an epimorphism in [C] (a "jointly-epic" cospan).  Equivalently, the
 cospan apex is the image of [X + Y] under the cocone formed by its two
 legs.  This is the exact dual of a relation, which is a jointly-MONIC
 span [X <- N -> Y] (copairing [N -> X × Y] monic); see
 [Construction.Span] for the spans this dualises.

 Corelations form a subcategory of [CospanCat C] whenever the composite
 pushout-cospan stays jointly epic.  This holds automatically in
 pretoposes (sets, presheaves, …), where pushouts of (regular) epis are
 again epis, but must be carried as a hypothesis in the general setting.
 Rather than expose a generic epi-stability class, we package exactly the
 composite-copairing-is-epi statement we need as the typeclass
 [CorelComposable] below.

 References:
 - nLab, "corelation" (definition and duality with relations).
 - B. Fong, "The Algebra of Open and Interconnected Systems", DPhil
 thesis, Oxford 2016, arXiv:1609.05382 — corelations are introduced
 as the image factorisation of cospans through their
 jointly-surjective (jointly-epic) representative.
 - B. Coya and B. Fong, "Corelations are the prop for extraspecial
 commutative Frobenius monoids", TAC 32 (2017), arXiv:1601.02307. 

 --------
 nLab:       https://ncatlab.org/nlab/show/corelation
 维基百科: 不存在（没有范畴理论文章；页面标题“Corelation”重定向到关于相关性的统计学文章）

 从 [X] 到 [Y] 的一个共关系是一个共尖 [X -in1-> N <-in2- Y]，其
 对偶映射
 [in1, in2]  := cospan_in1 ▽ cospan_in2 : X + Y ~> N
 在 [C] 中是一个满射（"联合满"的共尖）。等价地，
 共尖顶点是其两条腿形成的余锥下 [X + Y] 的像。这是关系的精确对偶，
 关系是一个联合单的跨度 [X <- N -> Y]（对偶映射 [N -> X × Y] 为单射）；参见
 [Construction.Span] 查看被对偶化的跨度。当复合推挤-余联合保持联合本质满射时，相关性形成 [CospanCat C] 的一个子类别。在预上类（集合、预层……）中，这一点是自动成立的，其中（正则）本质满射的推挤仍然是本质满射，但在一般情况下必须作为假设提出。我们没有展示一个通用的本质满射稳定类，而是将我们所需的复合-余配对-是本质满射的陈述封装为下面的类型类 [CorelComposable]。参考文献：
 - nLab，“corelation”（定义及其与关系的对偶）。
 - B. Fong，《开放与互联系统的代数》，牛津大学 DPhil 论文，2016年，arXiv:1609.05382 — 核关系被引入为通过它们的共同满射（联合表象为史密特史密斯映射）代表的 cospan 的像分解。
 - B. Coya 和 B. Fong，“核关系是特异交换 Frobenius 幺半群的 prop”，TAC 32 (2017)，arXiv:1601.02307。
*)

Section Corelation.

Context {C : Category}.
Context `{@Cocartesian C}.

(*
   * A corelation is a cospan together with a proof that its copairing
   is epic.  We package this as a record so that downstream code can
   extract the copairing-epi witness without re-deriving it. 

   --------
   * 相关是一个余跨度以及其余配对是满射的证明。我们将其打包为一个记录，以便下游代码可以在不重新推导的情况下提取余配对满射的证据。
*)
Record CorelationArrow (X Y : C) : Type := {
  corelation_cospan : CospanArrow X Y;
  corelation_copairing_epic :
    Epic (cospan_in1 corelation_cospan ▽ cospan_in2 corelation_cospan)
}.

Arguments corelation_cospan {X Y} _.
Arguments corelation_copairing_epic {X Y} _.

(** Coercion: a corelation IS a cospan. / 强制：一个相关是一个共跨。 *)
Coercion corelation_cospan : CorelationArrow >-> CospanArrow.

(*
   * Two corelations are equivalent iff their underlying cospans are. 

   --------
   * 两个对应关系当且仅当它们的底层共顶点图是等价的时才等价。
*)
Definition corelation_equiv {X Y : C} (f g : CorelationArrow X Y) : Type :=
  cospan_equiv (corelation_cospan f) (corelation_cospan g).

#[export] Program Instance CorelationArrow_Setoid {X Y : C} :
  Setoid (CorelationArrow X Y) := {|
  equiv := fun f g => corelation_equiv f g
|}.
Next Obligation.
  unfold corelation_equiv.
  constructor.
  - intros f.
    apply (@Equivalence_Reflexive _ _
             (@setoid_equiv _ (@CospanArrow_Setoid C X Y))).
  - intros f g.
    apply (@Equivalence_Symmetric _ _
             (@setoid_equiv _ (@CospanArrow_Setoid C X Y))).
  - intros f g h.
    apply (@Equivalence_Transitive _ _
             (@setoid_equiv _ (@CospanArrow_Setoid C X Y))).
Defined.

(*
   * The identity cospan is a corelation: its copairing is
   [id ▽ id : X + X ~> X], which is the codiagonal — an epi. 

   --------
   * 恒等余跨是一个余关联：它的余配对是 [id ▽ id : X + X ~> X]，它是余对角——一个满射。
*)
Lemma id_copairing_epic (X : C) :
  Epic (cospan_in1 (cospan_id X) ▽ cospan_in2 (cospan_id X)).
Proof.
  unfold cospan_id, cospan_in1, cospan_in2; simpl.
  constructor.
  intros Z g1 g2 Heq.
  (*
 g1 ∘ (id ▽ id) ≈ g2 ∘ (id ▽ id) implies g1 ≈ g2.
 Compose both sides with inl: g1 ∘ (id ▽ id) ∘ inl ≈ g2 ∘ (id ▽ id) ∘ inl.
 But (id ▽ id) ∘ inl = id, so g1 ≈ g2. 

 --------
 g1 ∘ (id ▽ id) ≈ g2 ∘ (id ▽ id) 意味着 g1 ≈ g2。
 在两边与 inl 组合：g1 ∘ (id ▽ id) ∘ inl ≈ g2 ∘ (id ▽ id) ∘ inl。
 但是 (id ▽ id) ∘ inl = id，所以 g1 ≈ g2。
*)
  assert (Hl : g1 ≈ g2).
  { rewrite <- (id_right g1).
    rewrite <- (@inl_merge _ _ X X X id[X] id[X]).
    rewrite comp_assoc.
    rewrite Heq.
    rewrite <- comp_assoc.
    rewrite (@inl_merge _ _ X X X id[X] id[X]).
    apply id_right. }
  exact Hl.
Qed.

Definition corelation_id (X : C) : CorelationArrow X X :=
  {| corelation_cospan := cospan_id X;
     corelation_copairing_epic := id_copairing_epic X |}.

(*
   * ** Composition: requires epi-stable pushouts

   The composite of two corelations is a corelation only when pushouts
   preserve epimorphisms.  We carry this as a typeclass hypothesis. 

   --------
   * ** 组成：需要 Epi-稳定的推挤出

   仅当推挤出保持满射时，两个核心关系的复合才是核心关系。我们将其作为类型类假设。
*)

Context (HP : HasPushouts C).

(*
   * ** Epi-stability hypothesis

   The natural axiom we actually use in the composition-preserves-epi
   proof is:

   "Given a pushout of [f2 : Y → Nf] and [g1 : Y → Ng] in [C], if
   [cf = f1 ▽ f2 : X + Y → Nf] is epic and [cg = g1 ▽ g2 : Y + Z → Ng]
   is epic, then the composite copairing of the new cospan is epic."

   This is one form of "joint-epi stability under pushout", and is the
   precise axiom needed for [CorelCat] to be a category.  It holds in
   pretoposes (in particular in [Sets]) and more generally in any
   regular category where the regular-epi factorisation is preserved
   by pushouts.

   Rather than expose a generic [EpiStablePushouts] class and prove the
   derivation from it (which requires a regular-epi factorisation
   system that the library does not currently formalise), we ASSUME
   this composite-copairing-is-epi statement directly as the class
   [CorelComposable] below.  This lets us deliver [CorelCat] and the
   wide-subcategory machinery in V2b, with the only V2c-applications
   obligation being to discharge the [CorelComposable] instance for
   concrete categories like [Sets]. 

   --------
   * ** Epi-稳定性假设

   我们在保持复合为Epi的证明中实际使用的自然公理是：

   “给定在 [C] 中 [f2 : Y → Nf] 和 [g1 : Y → Ng] 的推挤，如果 [cf = f1 ▽ f2 : X + Y → Nf] 是Epi并且 [cg = g1 ▽ g2 : Y + Z → Ng] 是Epi，那么新余并的复合对偶也是Epi。”

   这是一种“在推挤下联合Epi稳定性”的形式，也是 [CorelCat] 成为一个范畴所需的精确公理。它在前拓扑范畴中成立（特别是在 [Sets] 中），更一般地，它在任何正则范畴中也成立，只要正则Epi分解能被推挤保持。与其公开一个通用的 [EpiStablePushouts] 类并证明其派生（这需要一个库当前没有形式化的正射分解系统），我们直接假设这个复合共对是射的陈述，作为下面的 [CorelComposable] 类。这让我们能够在 V2b 中提供 [CorelCat] 和宽子范畴机制，唯一的 V2c 应用义务是为像 [Sets] 这样的具体范畴处理 [CorelComposable] 实例。
*)

Class CorelComposable : Type := {
  composite_copairing_epic :
    forall {X Y Z : C}
           (f : CorelationArrow X Y) (g : CorelationArrow Y Z),
    let cf := corelation_cospan f in
    let cg := corelation_cospan g in
    let P  := pushout (cospan_in2 cf) (cospan_in1 cg) in
      Epic ((pushout_in1 P ∘ cospan_in1 cf) ▽ (pushout_in2 P ∘ cospan_in2 cg))
}.

Context `{CC : CorelComposable}.

(** Underlying cospan-level composition of corelations. / 核相关的基础余积水平组合。 *)
Definition corelation_underlying_compose
           {X Y Z : C}
           (g : CorelationArrow Y Z) (f : CorelationArrow X Y)
  : CospanArrow X Z :=
  cospan_compose HP (corelation_cospan g) (corelation_cospan f).

(*
   * Composition of corelations. The copairing-epi witness is exactly
   [composite_copairing_epic] from the [CorelComposable] hypothesis. 

   --------
   * 核心关系的组合。共配对-满射证据正是来自 [CorelComposable] 假设的 [composite_copairing_epic]。
*)
Definition corelation_compose
           {X Y Z : C}
           (g : CorelationArrow Y Z) (f : CorelationArrow X Y)
  : CorelationArrow X Z :=
  {| corelation_cospan := corelation_underlying_compose g f;
     corelation_copairing_epic := composite_copairing_epic f g |}.

End Corelation.

Arguments CorelationArrow {C _} X Y.
Arguments corelation_cospan {C _ X Y} _.
Arguments corelation_copairing_epic {C _ X Y} _.
Arguments corelation_id {C _} X.
Arguments corelation_compose {C _ HP CC X Y Z} g f.

(* * ** Setoid for corelations, lifted to the global level / * ** 相关性的集合，提升到全局层级 *)
Arguments CorelationArrow_Setoid {C _} X Y.

(*
   * ** Category laws for corelation composition

   Once composition is constructed (via the [CorelComposable]
   hypothesis), the category laws come for free from the underlying
   cospan-level laws: equivalence on corelations is by definition
   equivalence on their underlying cospans, so [cospan_id_left],
   [cospan_id_right], and [cospan_compose_assoc] discharge the goals
   after [corelation_equiv]-unfolding. 

   --------
   * ** 核相关组合的范畴律

   一旦组合被构造（通过 [CorelComposable] 假设），范畴律自然来自基础的联合跨度层级律：核相关的等价性按定义就是其基础联合跨度的等价性，因此 [cospan_id_left]、[cospan_id_right] 和 [cospan_compose_assoc] 在 [corelation_equiv] 展开之后可以解决目标。
*)

Section CorelationCategory.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.
Context (HP : HasPushouts C).
Context `{CC : @CorelComposable C H_Coc HP}.

Lemma corelation_id_left {X Y : C} (f : CorelationArrow X Y) :
  corelation_equiv (corelation_compose (corelation_id Y) f) f.
Proof.
  unfold corelation_equiv, corelation_compose; simpl.
  unfold corelation_underlying_compose.
  apply (cospan_id_left HP (corelation_cospan f)).
Defined.

Lemma corelation_id_right {X Y : C} (f : CorelationArrow X Y) :
  corelation_equiv (corelation_compose f (corelation_id X)) f.
Proof.
  unfold corelation_equiv, corelation_compose; simpl.
  unfold corelation_underlying_compose.
  apply (cospan_id_right HP (corelation_cospan f)).
Defined.

Lemma corelation_compose_assoc {X Y Z W : C}
      (h : CorelationArrow Z W) (g : CorelationArrow Y Z) (f : CorelationArrow X Y) :
  corelation_equiv
    (corelation_compose h (corelation_compose g f))
    (corelation_compose (corelation_compose h g) f).
Proof.
  unfold corelation_equiv, corelation_compose; simpl.
  unfold corelation_underlying_compose; simpl.
  apply (cospan_compose_assoc HP
           (corelation_cospan h)
           (corelation_cospan g)
           (corelation_cospan f)).
Defined.

Lemma corelation_compose_assoc_sym {X Y Z W : C}
      (h : CorelationArrow Z W) (g : CorelationArrow Y Z) (f : CorelationArrow X Y) :
  corelation_equiv
    (corelation_compose (corelation_compose h g) f)
    (corelation_compose h (corelation_compose g f)).
Proof.
  apply (@Equivalence_Symmetric _ _
           (@setoid_equiv _ (@CorelationArrow_Setoid C _ X W))),
        corelation_compose_assoc.
Defined.

Lemma corelation_compose_respects_aux {X Y Z : C}
      (g g' : CorelationArrow Y Z) (f f' : CorelationArrow X Y) :
  corelation_equiv f f' ->
  corelation_equiv g g' ->
  corelation_equiv (corelation_compose g f) (corelation_compose g' f').
Proof.
  unfold corelation_equiv, corelation_compose; simpl.
  unfold corelation_underlying_compose.
  intros Hf Hg.
  exact (@cospan_compose_respects_aux C HP X Y Z
           (corelation_cospan g) (corelation_cospan g')
           (corelation_cospan f) (corelation_cospan f')
           Hf Hg).
Defined.

(** The corelation category. / 相关类别。 *)
Program Definition CorelCat : Category := {|
  obj      := @obj C;
  hom      := fun X Y => CorelationArrow X Y;
  homset   := fun X Y => @CorelationArrow_Setoid C _ X Y;
  id       := fun X => corelation_id X;
  compose  := fun X Y Z g f => corelation_compose g f;
  compose_respects := _;
  id_left  := fun X Y f => corelation_id_left f;
  id_right := fun X Y f => corelation_id_right f;
  comp_assoc := fun X Y Z W f g h => corelation_compose_assoc f g h;
  comp_assoc_sym := fun X Y Z W f g h => corelation_compose_assoc_sym f g h
|}.
Next Obligation.
  unfold Proper, respectful.
  intros g g' Hg f f' Hf.
  now apply corelation_compose_respects_aux.
Defined.

End CorelationCategory.

Arguments CorelCat C {H_Coc} HP {CC}.

(*
   * ** [CorelCat] as a wide subcategory of [CospanCat]

   The forgetful functor [CorelCat → CospanCat] sends each corelation to
   its underlying cospan and acts as the identity on objects.  It is
   faithful (different corelations with the same underlying cospan are
   equal) and bijective on objects (hence "wide"). 

   --------
   * ** [CorelCat] 作为 [CospanCat] 的一个广义子类别

   遗忘函子 [CorelCat → CospanCat] 将每个共相关映到其底层的余叉，并在对象上表现为恒等映射。它是忠实的（具有相同底层余叉的不同共关系是相等的），并且在对象上是双射的（因此称为“广义”）。
*)

Section CorelToCospan.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.
Context (HP : HasPushouts C).
Context `{CC : @CorelComposable C H_Coc HP}.

Program Definition Corel_to_Cospan : @CorelCat C H_Coc HP CC ⟶ CospanCat C HP := {|
  fobj := fun X => X;
  fmap := fun X Y f => corelation_cospan f
|}.
Solve All Obligations with
  (try (intros; reflexivity);
   try (intros; unfold Proper, respectful;
        intros f f' Hff'; exact Hff')).

End CorelToCospan.

(*
   * ** Notes

   The [CorelComposable] hypothesis is the single composite-copairing-
   is-epi axiom needed for [CorelCat] to be a category.  In a regular
   category (e.g. [Sets]), this hypothesis is automatic and follows
   from the regular-epi factorisation system.

   [CorelCat C HP CC] is mathematically complete and parametric over
   [CorelComposable C HP]; concrete instantiation (e.g. for [Sets],
   [FinSet], or any other category with a suitable epi-factorisation)
   is a downstream concern, not part of the cospan/corelation core.
   Producing such an instance in [Sets] requires either a regular-epi
   factorisation system, set-theoretic choice/LEM, or a quotient-style
   pushout setoid — each independent setoid infrastructure outside the
   scope of the cospan formalisation.

   Reference: nLab "corelation"; B. Fong, "The Algebra of Open and
   Interconnected Systems" (DPhil thesis, Oxford 2016, arXiv:1609.05382),
   where Corel(C) is built as the image factorisation of Cospan(C). 

   --------
   * ** 注释

   [CorelComposable] 假设是使 [CorelCat] 成为一个范畴所需的单复合-共配对-是象射公理。在一个正则范畴中（例如 [Sets]），这一假设是自动成立的，并且可以从正则象射分解系统推导出来。

   [CorelCat C HP CC] 在数学上是完备的，并且以 [CorelComposable C HP] 为参数；具体实例化（例如对于 [Sets]、[FinSet]，或任何具有合适象射分解的其他范畴）是下游问题，而不是余并/核心关系的核心内容。在 [Sets] 中生成这样的实例需要正则象射分解系统、集合论中的选择公理/排中律，或者商式推并集合——每一个都是超出余并形式化范围的独立集合结构。参考文献：nLab “corelation”；B. Fong，《开放与互联系统的代数》（牛津大学哲学博士论文，2016年，arXiv:1609.05382），其中 Corel(C) 构建为 Cospan(C) 的像分解。
*)
