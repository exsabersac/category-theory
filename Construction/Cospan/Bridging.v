Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Construction.Cospan.Category.

Generalizable All Variables.

(*
   * * Cospan bridging helpers (direct-CospanCat version) 

   --------
   * * Cospan 桥接助手（直接-CospanCat 版本）
*)

(*
 nLab:      https://ncatlab.org/nlab/show/cospan
 Wikipedia: https://en.wikipedia.org/wiki/Span_(category_theory)

 This file introduces no new categorical concept; it is a collection of
 derived rewrites about the cospan category [CospanCat C] (and the
 ambient coproduct structure) defined in [Construction.Cospan.Category],
 where the cospan concept and its sources are documented in full.

 With [CospanCat] now built directly via pushouts in [C] (rather than as
 [SpanCat (C^op)]), the cospan obligations are already phrased in terms
 of C-direction morphisms.  This file collects a few derived rewrites
 that come up repeatedly in Monoidal / SCFA / Hypergraph coherence proofs
 over [CospanCat C]. 

 --------
 nLab：       https://ncatlab.org/nlab/show/cospan 
 维基百科：  https://en.wikipedia.org/wiki/Span_(category_theory) 

 该文件没有引入新的范畴概念；它是关于余跨度范畴 [CospanCat C]（以及在 [Construction.Cospan.Category] 中定义的环境余积结构）的派生重写的集合，其中余跨度概念及其来源都有完整记录。

 随着 [CospanCat] 现在直接通过 [C] 中的推度构建（而不是作为 [SpanCat (C^op)]），余跨度的相关要求已经以 C 方向态射的形式表达。该文件收集了一些在 [CospanCat C] 上的单体 / SCFA / 超图一致性证明中反复出现的派生重写。
*)

(*
   * ** Section 1: coproduct/cover bridging

   These rewrites are purely about the cocartesian (coproduct) structure
   of [C]; no pushout is involved here (the relevant cospan tensor builds
   its legs from the binary coproduct [+], i.e. the pushout over the
   initial object).  When proving the bifunctor [fmap_comp] for
   [cospan_tensor], the leg conditions involve a [merge]-of-mediators
   composed against [cover]-style legs.  The fundamental simplifications
   are [merge ∘ cover] and [merge ∘ inl/inr]. 

   --------
   * ** 第1节：余积/覆盖桥接

   这些重写纯粹关于  [C] 的余笛卡尔（余积）结构；这里不涉及推挤（pushout）（相关的共跨张量使用二元余积  [+] 构建其腿，也就是以初始对象为底的推挤）。在证明  [cospan_tensor] 的双函子  [fmap_comp] 时，腿条件涉及一个  [merge] 的中介者与  [cover] 风格的腿组合。基本的简化是  [merge ∘ cover] 和  [merge ∘ inl/inr]。
*)

Section CoprodCoverBridging.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.

(*
   * When you have a [merge ∘ cover] composite, you can bring the
   [inl/inr] selector across to the C-level: 

   --------
   * 当你有一个 [merge ∘ cover] 复合件时，你可以将 [inl/inr] 选择器跨到 C 级别：
*)

Lemma merge_cover_inl
      {a b c d e : C}
      (m1 : c ~> e) (m2 : d ~> e)
      (h1 : a ~> c) (h2 : b ~> d) :
  (m1 ▽ m2) ∘ (cover h1 h2) ∘ inl ≈ m1 ∘ h1.
Proof.
  rewrite <- comp_assoc.
  rewrite cover_inl.
  rewrite comp_assoc.
  rewrite inl_merge.
  reflexivity.
Qed.

Lemma merge_cover_inr
      {a b c d e : C}
      (m1 : c ~> e) (m2 : d ~> e)
      (h1 : a ~> c) (h2 : b ~> d) :
  (m1 ▽ m2) ∘ (cover h1 h2) ∘ inr ≈ m2 ∘ h2.
Proof.
  rewrite <- comp_assoc.
  rewrite cover_inr.
  rewrite comp_assoc.
  rewrite inr_merge.
  reflexivity.
Qed.

(*
   * Variant: when the [merge] is composed with an [inl] on the right
   via two-step composition, you can collapse directly. 

   --------
   * 变体：当 [merge] 与右侧的 [inl] 通过两步组合组合时，你可以直接合并。
*)
Lemma merge_inl_assoc
      {a c d e : C} (m1 : c ~> e) (m2 : d ~> e) (h : a ~> c) :
  (m1 ▽ m2) ∘ inl ∘ h ≈ m1 ∘ h.
Proof.
  rewrite inl_merge; reflexivity.
Qed.

Lemma merge_inr_assoc
      {b c d e : C} (m1 : c ~> e) (m2 : d ~> e) (h : b ~> d) :
  (m1 ▽ m2) ∘ inr ∘ h ≈ m2 ∘ h.
Proof.
  rewrite inr_merge; reflexivity.
Qed.

End CoprodCoverBridging.

(*
   * ** Section 2: Coproduct mediator extensionality

   A morphism out of a coproduct is determined by its action on [inl]
   and [inr].  This is the joint-epi property — already available as
   [merge_inv]/[fork_inv], but stated here in a form convenient for
   cospan-leg goals. 

   --------
   * ** 第二节：余积中介的外延性

   从余积射出的态射由其在 [inl] 和 [inr] 上的作用决定。这是联合满射（joint-epi）性质——已在 [merge_inv] / [fork_inv] 中存在，但这里以便于处理共尖目标（cospan-leg goals）的形式表述。
*)

Section CoprodJointEpi.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.

(*
   * Two morphisms out of a coproduct are equal iff they agree on
   [inl] and [inr]. 

   --------
   * 若一个余积的两个态射在 [inl] 和 [inr] 上一致，则它们相等。
*)
Lemma coprod_ext {a b c : C} (u v : a + b ~> c) :
  u ∘ inl ≈ v ∘ inl -> u ∘ inr ≈ v ∘ inr -> u ≈ v.
Proof.
  intros Hl Hr.
  (*
 u ≈ u ∘ id ≈ u ∘ (inl ▽ inr) ≈ (u ∘ inl) ▽ (u ∘ inr) 

 --------
 u ≈ u ∘ id ≈ u ∘ (inl ▽ inr) ≈ (u ∘ inl) ▽ (u ∘ inr)
*)
  rewrite <- (id_right u).
  rewrite <- merge_inl_inr.
  rewrite <- merge_comp.
  rewrite Hl, Hr.
  rewrite merge_comp.
  rewrite merge_inl_inr.
  rewrite id_right.
  reflexivity.
Qed.

End CoprodJointEpi.

(*
   * ** Section 3: Cospan-equiv ergonomic builder

   Builds a [cospan_equiv f g] from a C-iso of apexes plus two C-level
   leg-relations.  In the direct CospanCat this is just the record
   constructor, exposed here for clarity. 

   --------
   * ** 第3节：Cospan-等效的符合人体工程学的构建器

   从顶点的C-同构加上两个C-级腿关系构建[cospan_equiv f g]。在直接的CospanCat中，这只是记录构造函数，这里为了清晰而暴露出来。
*)

Section CospanEquivIntro.

Context {C : Category}.

Lemma cospan_equiv_intro {X Y : C}
      (f g : CospanArrow X Y)
      (phi : cospan_apex f ≅ cospan_apex g)
      (Hin1 : to phi ∘ cospan_in1 f ≈ cospan_in1 g)
      (Hin2 : to phi ∘ cospan_in2 f ≈ cospan_in2 g) :
  cospan_equiv f g.
Proof.
  exists phi; split; [exact Hin1 | exact Hin2].
Defined.

End CospanEquivIntro.

(*
   * ** Section 4: Cospan-compose accessors restated cleanly

   The library already has [cospan_compose_in1/in2] as reflexivity
   lemmas; these are convenience aliases. 

   --------
   * ** 第4节：重新整理Cospan-compose访问器

   该库已经有 [cospan_compose_in1/in2] 作为自反性引理；
   这些是方便的别名。
*)

Section CospanComposeRewrites.

Context {C : Category}.
Context (HP : HasPushouts C).

Lemma cospan_compose_apex_eq {X Y Z : C}
      (g : CospanArrow Y Z) (f : CospanArrow X Y) :
  cospan_apex (cospan_compose HP g f)
  = pushout_apex (pushout (cospan_in2 f) (cospan_in1 g)).
Proof. reflexivity. Qed.

Lemma cospan_compose_in1_eq {X Y Z : C}
      (g : CospanArrow Y Z) (f : CospanArrow X Y) :
  cospan_in1 (cospan_compose HP g f)
  ≈ pushout_in1 (pushout (cospan_in2 f) (cospan_in1 g)) ∘ cospan_in1 f.
Proof. reflexivity. Qed.

Lemma cospan_compose_in2_eq {X Y Z : C}
      (g : CospanArrow Y Z) (f : CospanArrow X Y) :
  cospan_in2 (cospan_compose HP g f)
  ≈ pushout_in2 (pushout (cospan_in2 f) (cospan_in1 g)) ∘ cospan_in2 g.
Proof. reflexivity. Qed.

End CospanComposeRewrites.
