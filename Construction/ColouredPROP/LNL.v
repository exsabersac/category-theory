Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.CopyDiscard.
Require Import Category.Structure.Monoidal.CopyDiscard.Deterministic.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.CommutativeComonoid.
Require Import Category.Theory.Algebra.Comonoid.Hom.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.ColouredPROP.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.Instance.
Require Import Category.Construction.ColouredPROP.Interp.
Require Import Category.Construction.ColouredPROP.Presentation.
Require Import Category.Construction.ColouredPROP.Linear.
Require Import Category.Construction.ColouredPROP.Supply.
Require Import Category.Construction.ColouredPROP.Supply.Instance.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(* * * The linear/non-linear comonoid-supply bridge / * * 线性/非线性余积-供给桥 *)

(*
 nLab: https://ncatlab.org/nlab/show/linear+logic
 nLab: https://ncatlab.org/nlab/show/copy-discard+category
 nLab: https://ncatlab.org/nlab/show/comonoid

 ** SCOPE CONTRACT (read this before extending the file)

 This file states the HONEST, ATTAINABLE form of a linear/non-linear
 bridge for supplied coloured PROPs, in the library's
 copy-discard vocabulary (Structure/Monoidal/CopyDiscard.v and
 CopyDiscard/Deterministic.v — the Cho–Jacobs determinism squares —
 together with the Fong–Spivak comonoid supplies of
 Theory/Algebra/Comonoid/*.v and Construction/ColouredPROP/Supply.v).
 It is deliberately NOT Benton's LNL adjunction, and no part of it
 should be read as claiming one:

 - Benton's LNL model is a symmetric monoidal adjunction between a
 cartesian (closed) category and a symmetric monoidal (closed)
 category.  The right adjoint that manufactures the cartesian
 leg from the linear one is the COFREE COMMUTATIVE COMONOID
 functor (equivalently, the cartesian leg arises from the [!]
 exponential comonad it induces).  This library has no
 cofree-comonoid construction — [Comon_Forget] of
 Theory/Algebra/Comonoid/Hom.v has no right adjoint in-tree — so
 the adjunction itself is out of reach here, and this file says
 so rather than approximating it with an unproved interface.
 What IS delivered is the underlying bridge any such adjunction
 would factor through: the copyable colour class embeds into
 [Comon (cprop_cat P)], and the hom-sets of that embedding ARE
 the supply-deterministic maps, on the nose
 ([LNL_hom_is_deterministic]), with the [LNL_lift] /
 [Comon_Forget] round-trip pair ([LNL_forget_lift] /
 [LNL_lift_unique]) making the identification functorial in
 both directions.

 - A bespoke category of cartesian colour words and deterministic
 maps (with its own hand-rolled monoidal tower) is an explicit
 NON-GOAL, recorded here in the same machine-checked-deferral
 style the spine uses for out-of-scope successors (cf. the
 deferral notes of Construction/PROP/Algebra.v and
 Construction/ColouredPROP/Algebra.v).  [Comon (cprop_cat P)] —
 the sigma-packaged category of internal comonoids that
 Theory/Algebra/Comonoid/Hom.v already provides — IS the
 non-linear leg; duplicating it as a bespoke record tower would
 add coherence obligations without adding theorems.

 The conceptual neighbour of this bridge elsewhere in the library is
 the “cartesian colour” discussion of Structure/Monoidal/Collapse.v:
 there, semicartesian collapse shows what happens when copy/discard
 become NATURAL for every morphism (Fox's theorem territory, where
 the tensor is forced cartesian); here, the per-colour supply keeps
 naturality confined to the deterministic subclass, which is exactly
 what lets linear (non-copyable) colours coexist with cartesian
 (copyable) ones inside one coloured PROP.

 Concretely the file delivers:

 1.  [SupplyDeterministic] — Cho–Jacobs determinism relativised to
 the DERIVED boundary supplies [supply_list]: a boundary map
 between all-copyable words is supply-deterministic when it is a
 [ComonoidHom] between the derived supplies.  This is
 [deterministic] of CopyDiscard/Deterministic.v with the global
 [cd_comonoid] supply replaced by the per-boundary
 [supply_list] — a coloured PROP with linear colours has no
 global supply, precisely because linear wires carry none.
 Definitionally equal to [sel_deterministic] of Linear.v
 (pinned by [SupplyDeterministic_is_sel_deterministic]), and —
 at the total-supply degeneration point, the one instance in
 this file where a global [cd_comonoid] supply exists —
 definitionally equal to that [deterministic] itself
 (pinned by [SupplyDeterministic_is_deterministic]).

 2.  [supplied_obj] / [LNL_lift] — the embedding of the copyable
 colour class into [Comon (cprop_cat P)] at the symmetric-side
 monoidal structure [MBc P], with the round-trip pair
 [LNL_forget_lift] (forget after lift is the underlying map,
 reflexivity-grade) and [LNL_lift_unique] (any [Comon]-hom
 agreeing with [f] under [Comon_Forget] IS the lift of [f], via
 [Comon_Forget_Faithful]), plus the functoriality laws
 [LNL_lift_id] / [LNL_lift_comp].

 3.  [CopyDiscard_of_total_supply] — the degeneration test: over the
 TOTAL copyability predicate [fun _ => true], the free supplied
 PROP [SupplyPROP] of Supply/Instance.v carries an honest
 [CopyDiscard] structure, with
 [cd_comonoid X := supply_list X (all_true X)] and the four
 coherence fields discharged by the Fong–Spivak coherence
 THEOREMS [supply_app_delta] / [supply_app_epsilon] of Supply.v
 together with the unconditional evidence irrelevance of bool
 copyability ([all_copyable_irrelevant]).  At [SupplyPROP] the
 [ctensor_app_b] / [cunit_nil_b] mediation casts of those
 theorems are [eq_refl] (the pinned Examples of
 Supply/Instance.v), so every [hom_cast] vanishes DEFINITIONALLY
 and the obligations are [exact] applications.  A remark on
 class fit: [CopyDiscard] demands a comonoid on EVERY object,
 while a supply only provides them on the image of
 [cprop_of_list]; for a general coloured PROP that gap would
 need a surjectivity hypothesis.  At [SupplyPROP] the objects
 ARE the colour words and [cprop_of_list] is the identity, so
 no such hypothesis arises — the class's non-surjectivity
 observation is recorded as a non-defect, not worked around.

 4.  [linear_cartesian_characterization] — the closing lemma, at the
 pure supply PROP (base signature [Empty_CSig]): a colour is
 linear exactly when its wire supports NEITHER a
 commutative-comonoid supply NOR a bare fan-out morphism
 [[c] ~> [c; c]] (both refuted through [SupplyPROP_no_fanout]:
 a supply's comultiplication would itself be a fan-out), and
 copyable exactly when it supports BOTH ([supply_wire_comonoid]
 and [SupplyPROP_fanout]).  This is the categorical content of
 the fan-out linearity check: fan-out at a linear wire is not
 disallowed by convention — it is UNINHABITED.

 Reference: Benton, “A mixed linear and non-linear logic: proofs,
 terms and models”, CSL 1994, LNCS 933
 Reference: Cho & Jacobs, “Disintegration and Bayesian inversion via
 string diagrams”, MSCS 29(7):938–971, 2019
 (arXiv:1709.00322), §2
 Reference: Fong & Spivak, “Supplying bells and whistles in
 symmetric monoidal categories” (arXiv:1908.02633),
 §§1–2 

 --------
 nLab:  https://ncatlab.org/nlab/show/linear+logic 
 nLab:  https://ncatlab.org/nlab/show/copy-discard+category 
 nLab:  https://ncatlab.org/nlab/show/comonoid 

 ** 范围协议（在扩展文件前请阅读）

 本文件说明了针对库中提供的有色PROPs的线性/非线性桥的诚实、可实现形式，使用库的复制-丢弃词汇（Structure/Monoidal/CopyDiscard.v 和 CopyDiscard/Deterministic.v — Cho–Jacobs 确定性方格 — 以及 Theory/Algebra/Comonoid/*.v 和 Construction/ColouredPROP/Supply.v 的 Fong–Spivak comonoid 供应）。
 它故意不是Benton的LNL对偶，并且不应将其任何部分解读为宣称是LNL对偶。- Benton 的 LNL 模型是在一个笛卡尔（闭）范畴与一个对称单体（闭）范畴之间的一个对称单体伴随。将线性支路生成笛卡尔支路的右伴随是 COFREE COMMUTATIVE COMONOID 函子（等价地，笛卡尔支路来源于它所引出的 [!] 指数余模范畴）。这个库没有 cofree-comonoid 构造——Theory/Algebra/Comonoid/Hom.v 中的 [Comon_Forget] 在树中没有右伴随——所以伴随本身在这里无法实现，并且这个文件也是这样说明的，而不是用未经证明的接口去近似它。所交付的内容是任何此类伴随所需经过的基础桥梁：可复制的颜色类嵌入到 [Comon (cprop_cat P)] 中，并且该嵌入的 Hom 集就是供应确定性映射，精确对应于 [LNL_hom_is_deterministic]，且 [LNL_lift] / [Comon_Forget] 的往返对 ([LNL_forget_lift] / [LNL_lift_unique]) 使得该识别在两个方向上都是函子化的。- 一个定制的笛卡尔颜色词和确定性映射的类别（带有自己手工制作的幺半群塔）是一个明确的非目标，这里以脊柱用于超出范围的继承者的同样机器校验延迟风格记录（参见 Construction/PROP/Algebra.v 和 Construction/ColouredPROP/Algebra.v 的延迟注释）。[Comon (cprop_cat P)] —— Theory/Algebra/Comonoid/Hom.v 已经提供的内部余幺半群的 sigma 打包类别 —— 是非线性分支；将其复制作一个定制的记录塔将增加一致性义务，却不会增加定理。这个桥在图书馆的其他地方的概念邻居是 Structure/Monoidal/Collapse.v 中的“笛卡尔颜色”讨论：在那里，半笛卡尔塌缩展示了当 copy/discard 对每个态射都变得自然时会发生什么（Fox 定理的领域，其中张量被迫为笛卡尔性质）；在这里，每种颜色的供应将自然性限制在确定性子类中，这正是使线性（不可复制）颜色能够与笛卡尔（可复制）颜色在一个有色 PROP 中共存的原因。

 具体来说，这个文件提供了：1. [SupplyDeterministic] — 针对派生边界的 Cho–Jacobs 决定性被相对化，从而提供 [supply_list]：当它是派生供应之间的 [ComonoidHom] 时，所有可复制词之间的边界映射是供应决定性的。这是 CopyDiscard/Deterministic.v 的 [deterministic]，且将全局 [cd_comonoid] 供应替换为每边界的 [supply_list] —— 具有线性色彩的彩色 PROP 没有全局供应，恰恰因为线性导线不携带任何供应。从定义上等同于 Linear.v 的 [sel_deterministic]（由 [SupplyDeterministic_is_sel_deterministic] 固定），并且——在总供应退化点，本文件中唯一存在全局 [cd_comonoid] 供应的实例——从定义上等同于该 [deterministic] 本身（由 [SupplyDeterministic_is_deterministic] 固定）。2.   [supplied_obj]  /  [LNL_lift]  ——可复制颜色类在对称侧单体结构 [MBc P] 中嵌入 [Comon (cprop_cat P)]，其中往返对 [LNL_forget_lift]（升起后忘记的是基础映射，反身等级）和 [LNL_lift_unique]（任何与 [Comon_Forget] 下的 [f] 一致的 [Comon]-同态就是通过 [Comon_Forget_Faithful] 对 [f] 的升起），以及函子律 [LNL_lift_id] / [LNL_lift_comp]。3. [CopyDiscard_of_total_supply]  — 退化测试：在总可复制性谓词 [fun _ => true] 上，Supply/Instance.v 提供的自由 PROP [SupplyPROP] 具有一个真实的 [CopyDiscard] 结构，并且 [cd_comonoid X := supply_list X (all_true X)] 以及四个相干场由 Supply.v 的 Fong–Spivak 相干定理 [supply_app_delta] / [supply_app_epsilon] 与 bool 可复制性的无条件证据不可区分性 ([all_copyable_irrelevant]) 一起消解。在 [SupplyPROP]，[ctensor_app_b] / [cunit_nil_b] 的这些定理的调解类型是 [eq_refl]（Supply/Instance.v 的固定示例），因此每个 [hom_cast] 在定义上消失，义务为 [exact] 的应用。关于类适合性的说明：[CopyDiscard] 需要在每个对象上都有一个余幺半群，而 supply 仅在 [cprop_of_list] 的像上提供它们；对于一般的带颜色的 PROP，这种差距需要一个满射假设。在 [SupplyPROP] 处，对象就是颜色词，[cprop_of_list] 是恒等，所以不存在这样的假设——该类的非满射性观察被记录为非缺陷，而不是通过某种方法来解决。4. [linear_cartesian_characterization] —— 闭合引理，在纯供应 PROP（基础标记 [Empty_CSig]）上：当且仅当其线不支持交换-余单体供应或裸分批映射 [[c] ~> [c; c] 时，一个颜色是线性的（两者都通过 [SupplyPROP_no_fanout] 被驳斥：供应的余乘自身就是一个分批），并且当且仅当它同时支持 [supply_wire_comonoid] 和 [SupplyPROP_fanout] 时是可复制的。这是分批线性检查的范畴内容：线性线上的分批不是按惯例被禁止的——它是未被占用的。参考文献：Benton，《混合线性和非线性逻辑：证明、项和模型》，CSL 1994，LNCS 933
 参考文献：Cho & Jacobs，《通过弦图的解体与贝叶斯逆》，MSCS 29(7)：938–971，2019（arXiv:1709.00322），§2
 参考文献：Fong & Spivak，《在对称单模范畴中提供铃声与哨声》（arXiv:1908.02633），§§1–2
*)

(* ------------------------------------------------------------------ *)

(* * ** The bridge: supplied objects and deterministic maps / * ** 桥梁：提供的对象和确定性映射 *)

Section LNLBridge.

Context {Colour : Type}.
Context (P : ColouredPROP Colour).
Context (copyable : Colour -> bool).
Context `{SS : @SelectiveSupply Colour P copyable}.

(*
   * The coloured-PROP-object [⟦cs⟧c], as in
   [Construction/ColouredPROP.v] (whose notation is section-local
   there and must be re-declared per file). 

   --------
   * 彩色-PROP-对象 [⟦cs⟧c]，如同 [Construction/ColouredPROP.v] （其表示法在该节是本地的，且必须在每个文件中重新声明）。
*)
Notation "⟦ cs ⟧c" := (@cprop_of_list Colour P cs)
  (at level 0, format "⟦ cs ⟧c").

(*
   * Cho–Jacobs determinism at the derived boundary supplies: the two
   preservation squares

   scopy ds Hd ∘ f    ≈ (f ⨂ f) ∘ scopy cs Hc
   sdiscard ds Hd ∘ f ≈ sdiscard cs Hc

   packaged as the [ComonoidHom] they abbreviate — the bridge's
   export of [sel_deterministic] (Construction/ColouredPROP/
   Linear.v), stated directly at the derived supplies. 

   --------
   * 在派生边界处的 Cho–Jacobs 决定性提供了：两个保留方块

   scopy ds Hd ∘ f    ≈ (f ⨂ f) ∘ scopy cs Hc
   sdiscard ds Hd ∘ f ≈ sdiscard cs Hc

   打包为他们缩写的 [ComonoidHom] —— 桥的导出 [sel_deterministic]（Construction/ColouredPROP/Linear.v），直接在派生供应中声明。
*)
Definition SupplyDeterministic {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (f : ⟦cs⟧c ~{P}~> ⟦ds⟧c) : Type :=
  @ComonoidHom P (MBc P) ⟦cs⟧c ⟦ds⟧c
    (@ccomon_comonoid P (@cprop_symmetric Colour P) ⟦cs⟧c
       (supply_list cs Hc))
    (@ccomon_comonoid P (@cprop_symmetric Colour P) ⟦ds⟧c
       (supply_list ds Hd))
    f.

(*
   * The bridge predicate IS Linear.v's determinism predicate, on the
   nose. 

   --------
   * 桥接谓词正是 Linear.v 的确定性谓词，完全对应。
*)
Example SupplyDeterministic_is_sel_deterministic
  {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (f : ⟦cs⟧c ~{P}~> ⟦ds⟧c) :
  SupplyDeterministic Hc Hd f = sel_deterministic Hc Hd f := eq_refl.

(*
   * The embedding of the copyable colour class into the category of
   internal comonoids of [P] (at the symmetric-side monoidal
   structure [MBc P], where the derived supplies live): a boundary
   word together with its derived supply, sigma-packed as an object
   of [Comon].  Explicit pair, so both projections are
   definitional. 

   --------
   * 可复制颜色类在  [P]  的内部余单子范畴中的嵌入（在对称单侧幺半群结构  [MBc P] 下，派生供应存在的地方）：一个边界字以及其派生供应，以 sigma 打包为  [Comon] 的一个对象。明确的对偶，所以两个投影都是定义性的。
*)
Definition supplied_obj (cs : list Colour)
  (H : all_copyable copyable cs) : @Comon (cprop_cat P) (MBc P) :=
  (⟦cs⟧c;
   @ccomon_comonoid P (@cprop_symmetric Colour P) ⟦cs⟧c
     (supply_list cs H)).

(*
   * A supply-deterministic map lifts to a [Comon]-hom between the
   supplied objects: the sigma-pack of the map with its determinism
   witness. 

   --------
   * 一个供应确定性的映射可以提升为供应对象之间的 [Comon] -同态：该映射与其确定性证据的 sigma 包。
*)
Definition LNL_lift {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (f : ⟦cs⟧c ~{P}~> ⟦ds⟧c) (Hf : SupplyDeterministic Hc Hd f) :
  supplied_obj cs Hc ~{@Comon (cprop_cat P) (MBc P)}~> supplied_obj ds Hd :=
  (f; Hf).

(*
   * The hom-sets of the embedding ARE the supply-deterministic maps —
   on the nose, not merely up to bijection: a [Comon]-hom between
   supplied objects is by definition a boundary map together with a
   [SupplyDeterministic] witness.  Machine-checked as a definitional
   equality of types. 

   --------
   * 嵌入的 Hom 集是供给确定性映射——严格意义上是这样，而不仅仅是双射意义上的：在已供给对象之间的 [Comon]-hom 根据定义是一个边界映射以及一个 [SupplyDeterministic] 证明。已作为类型的定义性等式通过机器验证。
*)
Example LNL_hom_is_deterministic (cs ds : list Colour)
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds) :
  (supplied_obj cs Hc ~{@Comon (cprop_cat P) (MBc P)}~> supplied_obj ds Hd)
  = { f : ⟦cs⟧c ~{P}~> ⟦ds⟧c & SupplyDeterministic Hc Hd f }
  := eq_refl.

(*
   * *** The round-trip lemma pair

   Forget after lift is the identity on the underlying map
   (reflexivity-grade), and — via faithfulness of [Comon_Forget] —
   any [Comon]-hom agreeing with [f] under the forgetful functor IS
   the lift of [f].  Together these exhibit the [Comon]-homs between
   supplied objects as exactly the deterministic maps. 

   --------
   * *** 往返引理对

   提升后的遗忘函数在底层映射上是恒等映射（自反级），并且——通过  [Comon_Forget] 的忠实性——
   任何在遗忘函子下与  [f] 一致的  [Comon] 同构都是  [f] 的提升。
   这些共同展示了给定对象之间的  [Comon] 同构正好是确定性映射。
*)

Lemma LNL_forget_lift {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (f : ⟦cs⟧c ~{P}~> ⟦ds⟧c) (Hf : SupplyDeterministic Hc Hd f) :
  fmap[@Comon_Forget (cprop_cat P) (MBc P)] (LNL_lift Hc Hd f Hf) ≈ f.
Proof. reflexivity. Qed.

Lemma LNL_lift_unique {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (f : ⟦cs⟧c ~{P}~> ⟦ds⟧c) (Hf : SupplyDeterministic Hc Hd f)
  (u : supplied_obj cs Hc
         ~{@Comon (cprop_cat P) (MBc P)}~> supplied_obj ds Hd) :
  fmap[@Comon_Forget (cprop_cat P) (MBc P)] u ≈ f ->
  u ≈[@Comon (cprop_cat P) (MBc P)] LNL_lift Hc Hd f Hf.
Proof.
  intros Hu.
  apply (@fmap_inj _ _ _ (@Comon_Forget_Faithful (cprop_cat P) (MBc P)) _ _).
  rewrite LNL_forget_lift.
  exact Hu.
Qed.

(*
   * The eta-form of uniqueness: every [Comon]-hom between supplied
   objects is the lift of its own underlying map, its determinism
   witness being its own second projection. 

   --------
   * 唯一性的 η-形式：每个 [Comon]-同态在提供的对象之间都是其自身底层映射的提升，其确定性证明是其自身的第二投影。
*)
Corollary LNL_lift_eta {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (u : supplied_obj cs Hc
         ~{@Comon (cprop_cat P) (MBc P)}~> supplied_obj ds Hd) :
  u ≈[@Comon (cprop_cat P) (MBc P)]
  LNL_lift Hc Hd (fmap[@Comon_Forget (cprop_cat P) (MBc P)] u) `2 u.
Proof.
  apply LNL_lift_unique.
  reflexivity.
Qed.

(*
   * *** Functoriality of the lift

   [LNL_lift] sends identities to identities and composites to
   composites.  Stated over an ARBITRARY determinism witness — the
   hom equivalence of [Comon] compares only the underlying maps, so
   the witness is irrelevant up to [≈]; [sel_deterministic_id] /
   [sel_deterministic_comp] of Linear.v provide the canonical
   witnesses. 

   --------
   * *** 提升的函子性

   [LNL_lift] 将恒等映射映射为恒等映射，将复合映射映射为复合映射。对于任意的确定性证据来说——[Comon] 的同态等价仅比较基础映射，因此该证据在 [≈] 下是无关的；Linear.v 的 [sel_deterministic_id] / [sel_deterministic_comp] 提供了规范的证据。
*)

Lemma LNL_lift_id (cs : list Colour) (Hc : all_copyable copyable cs)
  (Hid : SupplyDeterministic Hc Hc (@id P ⟦cs⟧c)) :
  LNL_lift Hc Hc id Hid ≈[@Comon (cprop_cat P) (MBc P)] id.
Proof.
  change (@id P ⟦cs⟧c ≈ @id P ⟦cs⟧c).
  reflexivity.
Qed.

Lemma LNL_lift_comp {cs ds es : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (He : all_copyable copyable es)
  (g : ⟦ds⟧c ~{P}~> ⟦es⟧c) (f : ⟦cs⟧c ~{P}~> ⟦ds⟧c)
  (Hg : SupplyDeterministic Hd He g) (Hf : SupplyDeterministic Hc Hd f)
  (Hgf : SupplyDeterministic Hc He (g ∘ f)) :
  LNL_lift Hc He (g ∘ f) Hgf
    ≈[@Comon (cprop_cat P) (MBc P)]
  LNL_lift Hd He g Hg ∘[@Comon (cprop_cat P) (MBc P)] LNL_lift Hc Hd f Hf.
Proof.
  change (g ∘ f ≈ g ∘ f).
  reflexivity.
Qed.

End LNLBridge.

(* ------------------------------------------------------------------ *)

(*
   * ** Total-supply degeneration: [CopyDiscard] from a total supply

   When EVERY colour is copyable, the free supplied PROP collapses
   into the world of Structure/Monoidal/CopyDiscard.v: the derived
   boundary supplies assemble into an honest [CopyDiscard] structure.
   This is the degeneration test for the selective-supply design —
   dial the copyability predicate to [fun _ => true] and the
   [CopyDiscard] class is recovered on the nose.

   The four coherence obligations are [exact] applications of the
   Fong–Spivak coherence theorems [supply_app_delta] /
   [supply_app_epsilon] of Supply.v (tensor) and of the definitional
   collapse of the empty-boundary supply onto the unit comonoid
   (unit): at [SupplyPROP] the [ctensor_app_b] / [cunit_nil_b]
   mediation is [eq_refl] (the pinned Examples of Supply/Instance.v),
   so the [hom_cast] mediation of the theorems vanishes
   definitionally and no cast survives into the obligations.

   On class fit: [CopyDiscard] supplies a comonoid on EVERY object of
   the category, whereas a coloured-PROP supply covers only the image
   of [cprop_of_list]; in general the two differ by a surjectivity
   hypothesis.  At [SupplyPROP] the objects ARE the colour words and
   [cprop_of_list] is the identity, so the gap is empty — recorded as
   a non-defect of the class, not worked around. 

   --------
   * ** 总供应退化：从总供应的 [CopyDiscard]

   当每种颜色都可复制时，免费供应的 PROP 会塌缩
   进入 Structure/Monoidal/CopyDiscard.v 的世界：派生的
   边界供应组合成一个真实的 [CopyDiscard] 结构。
   这是选择性供应设计的退化测试——
   将可复制性谓词调整为 [fun _ => true]，就可以精确地恢复 [CopyDiscard] 类。四个相干性义务是 Fong–Spivak 相干性定理的应用 / Supply.v（张量）的定义性塌缩以及将空边界供给塌缩到单位余单子（单位）：在 / 调解是（Supply/Instance.v 的固定示例），因此定理的调解在定义上消失，没有转换残留在义务中。关于类的适合性：[CopyDiscard] 在该范畴的每一个对象上都提供了一个余单体，而有色 PROP 的提供仅覆盖 [cprop_of_list] 的像；一般来说，两者的区别在于一个满射假设。在 [SupplyPROP] 处，对象就是颜色词，而 [cprop_of_list] 是恒等，因此差异为空——被记录为类的非缺陷，而没有通过其他方式解决。
*)

Section TotalSupply.

Context {Colour : Type}.
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (S : CSignature Colour).

(*
   * Every colour word is all-copyable for the total predicate: a
   computing fixpoint ([forallb (fun _ => true)] peels cons cells
   definitionally). 

   --------
   * 每个颜色词对于整体谓词都是可完全复制的：一个计算不动点（[forallb (fun _ => true)] 定义地去皮 cons 单元）。
*)
Fixpoint all_true (cs : list Colour) :
  all_copyable (fun _ : Colour => true) cs :=
  match cs with
  | [] => eq_refl
  | _ :: cs' => all_true cs'
  end.

Notation TotalPROP := (SupplyPROP Cdec S (fun _ : Colour => true)).
Notation TotalSS :=
  (SupplyPROP_SelectiveSupply Cdec S (fun _ : Colour => true)).

(*
   * Decidable object equality for the presented supply PROP: objects
   are colour words (per the D2 discipline this is a definition fed
   the one canonical [Cdec], not an instance). 

   --------
   * 对所呈现的供应 PROP 可判定的对象相等性：对象是颜色词（根据 D2 学科，这是一个定义，输入的是唯一规范的 [Cdec]，而不是一个实例）。
*)
Definition TotalPROP_ObjDecEq : @ObjDecEq (cprop_cat TotalPROP) :=
  CFreeCat_ObjDecEq (SupplyExtSig S (fun _ : Colour => true)) Cdec.

(*
   * The [CopyDiscard] instance: the comonoid on the word [X] is its
   derived supply.  Fully type-ascribed Program definition, keeping
   every obligation at the ascribed instance (the [CPresented_Strict]
   precedent of Presentation.v); the obligations are the class fields
   verbatim. 

   --------
   * [CopyDiscard] 实例：单词 [X] 上的 comonoid 是它的派生 supply。完全类型标注的程序定义，在标注的实例上保留每个义务（Presentation.v 的 [CPresented_Strict] 先例）；这些义务逐字对应类字段。
*)
#[local] Obligation Tactic := intros.

Program Definition CopyDiscard_of_total_supply :
  @CopyDiscard (cprop_cat TotalPROP)
    (@cprop_symmetric Colour TotalPROP) := {|
  cd_comonoid := fun X : cprop_cat TotalPROP =>
    supply_list (P := TotalPROP) (SS := TotalSS) X (all_true X)
|}.
Next Obligation.
  (*
 cd_tensor_delta: [X ⨂ Y ≡ X ++ Y] definitionally, so this IS the
 coherence square at [all_true] evidence, its [hom_cast] mediation
 gone by conversion. 

 --------
 cd_tensor_delta：[X ⨂ Y ≡ X ++ Y] 从定义上来说，所以这确实是在 [all_true] 的相干平方证据，其 [hom_cast] 的调解已通过转换消失。
*)
  exact (@supply_app_delta Colour TotalPROP TotalPROP_ObjDecEq
           (fun _ : Colour => true) TotalSS
           X Y (all_true X) (all_true Y) (all_true ((X ++ Y)%list))).
Qed.
Next Obligation.
  (* cd_tensor_epsilon: mirror. / cd_tensor_epsilon：镜像。 *)
  exact (@supply_app_epsilon Colour TotalPROP TotalPROP_ObjDecEq
           (fun _ : Colour => true) TotalSS
           X Y (all_true X) (all_true Y) (all_true ((X ++ Y)%list))).
Qed.
Next Obligation.
  (*
 cd_unit_delta: the supply on [I ≡ []] is the (untransported) unit
 comonoid, whose δ is the inverse left unitor on the nose. 

 --------
 cd_unit_delta：在 [I ≡ [] 上的供应是（未运输的）单位余半范畴，其 δ 恰好是左单位的逆变换。
*)
  reflexivity.
Qed.
Next Obligation.
  (*
 cd_unit_epsilon: its ε is the identity on the nose. 

 --------
 cd_unit_epsilon：它的 ε 是严格的恒等式。
*)
  reflexivity.
Qed.

(*
   * The copy and discard morphisms of the degenerate instance are the
   derived supply's, definitionally. 

   --------
   * 退化实例的拷贝和丢弃态射在定义上是派生供应的态射。
*)
Example CopyDiscard_of_total_supply_copy (X : list Colour) :
  @copy (cprop_cat TotalPROP) (@cprop_symmetric Colour TotalPROP)
    CopyDiscard_of_total_supply X
  = scopy (P := TotalPROP) (SS := TotalSS) X (all_true X) := eq_refl.

Example CopyDiscard_of_total_supply_discard (X : list Colour) :
  @discard (cprop_cat TotalPROP) (@cprop_symmetric Colour TotalPROP)
    CopyDiscard_of_total_supply X
  = sdiscard (P := TotalPROP) (SS := TotalSS) X (all_true X) := eq_refl.

(*
   * The degeneration also closes the vocabulary loop of the SCOPE
   CONTRACT: at the total supply — the one instance where a global
   [cd_comonoid] supply exists — the bridge predicate
   [SupplyDeterministic] IS [deterministic] of
   CopyDiscard/Deterministic.v at [CopyDiscard_of_total_supply], on
   the nose.  Machine-checked as a definitional equality of types, so
   any drift in the [cd_comonoid] choice above or in the
   [supply_list] mediation would be caught here. 

   --------
   * 这种退化也闭合了 SCOPE 合约的词汇环：在总供应量——这是全球 [cd_comonoid] 供应存在的唯一实例——桥接谓词 [SupplyDeterministic] 等于 [deterministic]，在 CopyDiscard/Deterministic.v 的 [CopyDiscard_of_total_supply] 位置上，恰好如此。经机器检查为类型的定义性等式，因此上述 [cd_comonoid] 的选择或 [supply_list] 的调解中的任何偏差都将在这里被发现。
*)
Example SupplyDeterministic_is_deterministic (X Y : list Colour)
  (f : X ~{TotalPROP}~> Y) :
  SupplyDeterministic TotalPROP (fun _ : Colour => true)
    (SS := TotalSS) (all_true X) (all_true Y) f
  = @deterministic _ _ CopyDiscard_of_total_supply X Y f
  := eq_refl.

End TotalSupply.

(* ------------------------------------------------------------------ *)

(*
   * ** The linear/cartesian characterization

   At the pure supply PROP — base signature [Empty_CSig], so the ONLY
   generators are the per-wire dup/del of copyable colours — the
   copyability predicate is characterised by the geometry of the
   hom-sets: a colour is linear exactly when its wire supports neither
   a commutative-comonoid supply nor a bare fan-out morphism, and
   copyable exactly when it supports both.  Fan-out at a linear wire is
   not disallowed by convention; it is UNINHABITED
   ([SupplyPROP_no_fanout] — even a supply is refuted through its own
   comultiplication), and conversely a copyable wire realises its
   supply syntactically ([supply_wire_comonoid], [SupplyPROP_fanout]).
   This is the categorical content of the fan-out linearity check. 

   --------
   * ** 线性/笛卡尔特征

   在纯供应 PROP — 基本签名 [Empty_CSig] 上，因此唯一的生成元是每条线的可复制颜色的复制/删除 — 可复制性谓词由 Hom 集的几何性质刻画：当且仅当其导线既不支持交换共幺半群供应也不支持裸放大映射时，该颜色是线性的；当且仅当它同时支持两者时，该颜色是可复制的。在线性导线上放大按惯例不被禁止；它是未占用的（[SupplyPROP_no_fanout] — 即使是供应也会通过自身的共乘法被否定），反之，可复制导线在语法上实现其供应 ([supply_wire_comonoid], [SupplyPROP_fanout])。这是放大线性检查的范畴内容。
*)

Section Characterization.

Context {Colour : Type}.
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (copyable : Colour -> bool).

Notation PurePROP := (SupplyPROP Cdec Empty_CSig copyable).

Theorem linear_cartesian_characterization (c : Colour) :
  (LinearColour copyable c
     <-> ((@CommutativeComonoid (cprop_cat PurePROP)
             (@cprop_symmetric Colour PurePROP)
             (wire (P := PurePROP) c) -> False)
          /\ ((([c] : list Colour) ~{PurePROP}~> [c; c]) -> False)))
  /\ (copyable c = true
     <-> (inhabited (@CommutativeComonoid (cprop_cat PurePROP)
                       (@cprop_symmetric Colour PurePROP)
                       (wire (P := PurePROP) c))
          /\ inhabited (([c] : list Colour) ~{PurePROP}~> [c; c]))).
Proof.
  split.
  - (* linear <-> neither supply nor fan-out / 线性 <-> 既不供电也不分流 *)
    split.
    + intros Hlin.
      split.
      * (* no supply: its comultiplication would BE a fan-out / 没有供应：它的共乘法将是一个扇出 *)
        intros M.
        exact (SupplyPROP_no_fanout Cdec Empty_CSig copyable c Hlin
                 (pure_base_conservative Cdec c)
                 (@ccomon_delta (cprop_cat PurePROP)
                    (@cprop_symmetric Colour PurePROP)
                    (wire (P := PurePROP) c) M)).
      * (* no fan-out / 无扇出 *)
        exact (SupplyPROP_no_fanout Cdec Empty_CSig copyable c Hlin
                 (pure_base_conservative Cdec c)).
    + intros [HnoM _].
      destruct (copyable c) eqn:Hc.
      * exfalso.
        exact (HnoM (supply_wire_comonoid Cdec Empty_CSig copyable c Hc)).
      * exact Hc.
  - (* copyable <-> both supply and fan-out / 可复制 <-> 既供给又分流 *)
    split.
    + intros Hc.
      split.
      * exact (inhabits
                 (supply_wire_comonoid Cdec Empty_CSig copyable c Hc)).
      * exact (inhabits (SupplyPROP_fanout Cdec Empty_CSig copyable c Hc)).
    + intros [_ [t]].
      destruct (copyable c) eqn:Hc.
      * reflexivity.
      * exfalso.
        exact (SupplyPROP_no_fanout Cdec Empty_CSig copyable c Hc
                 (pure_base_conservative Cdec c) t).
Qed.

End Characterization.
