Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Bicategory.
Require Import Category.Theory.Bicategory.Adjunction.
Require Import Category.Theory.Bicategory.Mates.
Require Import Category.Instance.Cat.Bicategory.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Theory.Adjunction.

Generalizable All Variables.

(** Adjunctions and mates in the bicategory `Cat` / 双范畴 `Cat` 中的伴随和伴侣 *)

(*
 nLab: https://ncatlab.org/nlab/show/adjoint+functor
 nLab: https://ncatlab.org/nlab/show/mate

 `Instance/Cat/Bicategory.v` exhibits `Cat` as a bicategory: its 0-cells are
 categories, its hom-category `bicat C D` is *definitionally* the functor
 category `[C, D]`, horizontal composition `∘∘∘` is functor composition `◯`
 (extended to natural transformations by the Godement composite), `bi1id` is
 the identity functor, and the unitors/associator are the coherence natural
 isomorphisms `nat_ρ`/`nat_λ`/`nat_α` of `Instance/Fun.v`.

 This file is the payoff of the bicategory-mates development: it identifies the
 abstract 2-cell calculus of `Theory/Bicategory/{Adjunction,Mates}.v`,
 specialised to `Cat`, with the ordinary category-theoretic notions, so that
 the general constructions become usable by ordinary-CT files.

 1. AN INTERNAL ADJUNCTION IN `Cat` IS AN ORDINARY ADJUNCTION.  Because
 `∘∘∘ = ◯` and `bi1id = Id`, a `BicatAdjunction (B:=Cat_Bicategory) F U`
 carries a unit `adj_unit : Id ⟹ U ◯ F` and a counit
 `adj_counit : F ◯ U ⟹ Id` that are literally natural transformations, and
 its two bicategorical triangle identities — conjugated by the `Cat`
 unitors `nat_λ`/`nat_ρ` and the associator `nat_α`, whose components are
 all `fmap id` — collapse COMPONENTWISE to exactly the two zig-zag
 identities of the unit/counit presentation `F ∹ U`
 (`Adjunction/Natural/Transformation.v`).  Hence
 `Cat_BicatAdjunction_iff : BicatAdjunction F U ↔ (F ∹ U)`, and, composing
 with the `F ∹ U ↔ F ⊣ U` bridge of
 `Adjunction/Natural/Transformation/Universal.v`, internal adjunctions in
 `Cat` coincide with hom-set adjunctions `F ⊣ U`
 (`Cat_BicatAdjunction_Adjunction_iff`).

 2. MATES IN `Cat` UNFOLD TO THE TRANSPOSES.  The precomposition
 hom-adjunction `precomp_to` of `Theory/Bicategory/Mates.v`, specialised to
 `Cat`, IS the adjunction transpose `⌊−⌋`: componentwise
 `(precomp_to A σ) t ≈ fmap[U] (σ t) ∘ η (c t) = ⌊ σ t ⌋`.  The
 postcomposition hom-adjunction `postcomp_to` is the counit whiskering
 `(postcomp_to A γ) t ≈ fmap[e] (ε t) ∘ γ (U t)`.  Threading these through
 the definition `mate σ = postcomp (α⁻¹ ∘ precomp σ)` gives the classical
 mate formula componentwise (`Cat_mate_unfold`):

 (mate σ) Z ≈ fmap[U'] (fmap[b] (ε Z)) ∘ ⌊ σ (U Z) ⌋
 = fmap[U'] (fmap[b] (ε Z))
 ∘ fmap[U'] (σ (U Z)) ∘ η' (a (U Z)),

 where `η'` is the unit of `F' ⊣ U'` and `ε` the counit of `F ⊣ U`.

 The engine behind every proof here is the “standing trap” made harmless: in
 `Cat` the identity 2-cell `bi2id`, the unitor and associator components are
 all `fmap[_] id`, so after `simpl` a single `rewrite !fmap_id` followed by
 `id_left`/`id_right` clears every coherence factor, leaving precisely the
 ordinary-CT expression. 

 --------
 nLab：https://ncatlab.org/nlab/show/adjoint+functor
 nLab：https://ncatlab.org/nlab/show/mate

 `Instance/Cat/Bicategory.v` 作为一个双范畴展示了 `Cat`：其 0-元是范畴，其同范畴 `bicat C D` *定义性* 地是函子范畴 ` [C, D]ZZ `，水平复合 `∘∘∘` 是函子复合 `◯`（通过 Godement 复合扩展到自然变换），`bi1id` 是单位函子，而单元子/结合子是 `Instance/Fun.v` 的相干自然同构 `nat_ρ` / `nat_λ` / `nat_α`。

 此文件是双范畴-伴随发展成果的体现：它将 `Theory/Bicategory/{Adjunction,Mates}.v` 的抽象 2-元计算，专门化到 `Cat`，与普通范畴论概念对应，使得一般构造能够被普通 CT 文件使用。1. 在 `Cat` 中的一个内部伴随是一个普通伴随。因为 `∘∘∘ = ◯` 和 `bi1id = Id`，`BicatAdjunction (B:=Cat_Bicategory) F U` 携带一个单元 `adj_unit : Id ⟹ U ◯ F` 和一个余单元 `adj_counit : F ◯ U ⟹ Id`，它们是字面上的自然变换，并且它的两个双范畴三角恒等式——通过 `Cat` 单位器 `nat_λ` / `nat_ρ` 和结合子 `nat_α`（其分量都是 `fmap id`）共轭——在分量上完全坍缩为单位/余单元表示 `F ∹ U` (`Adjunction/Natural/Transformation.v`) 的两个之字形恒等式。因此 `Cat_BicatAdjunction_iff : BicatAdjunction F U ↔ (F ∹ U)`，并且，通过与 `Adjunction/Natural/Transformation/Universal.v` 的 `F ∹ U ↔ F ⊣ U` 桥的组合，`Cat` 中的内部伴随与霍姆集伴随 `F ⊣ U` (`Cat_BicatAdjunction_Adjunction_iff`) 相一致。2. 在 `Cat` 中的 MATES 展开为转置。将 `Theory/Bicategory/Mates.v` 的预组合 hom-伴随 `precomp_to` 特化到 `Cat`，是伴随转置 `⌊−⌋`：逐分量 `(precomp_to A σ) t ≈ fmap [U]ZZ  (σ t) ∘ η (c t) = ⌊ σ t ⌋`。后组合 hom-伴随 `postcomp_to` 是余单位刷 `(postcomp_to A γ) t ≈ fmap [e]ZZ  (ε t) ∘ γ (U t)`。通过 `mate σ = postcomp (α⁻¹ ∘ precomp σ)` 的定义，将它们串联起来得到逐分量的经典 mate 公式 (`Cat_mate_unfold`)：

 (mate σ) Z ≈ fmap [U']  (fmap [b]  (ε Z)) ∘ ⌊ σ (U Z) ⌋
 = fmap [U']  (fmap [b]  (ε Z))
 ∘ fmap [U']  (σ (U Z)) ∘ η' (a (U Z))，

 其中 `η'` 是 `F' ⊣ U'` 的单位，`ε` 是 `F ⊣ U` 的余单位。这里每个证明背后的引擎是被化为无害的“固定陷阱”：在 `Cat` 中，恒等 2-态 `bi2id`、单位子和结合子组件都是 `fmap [_]ZZ  id`，因此在 `simpl` 之后，一个 `rewrite !fmap_id` 紧跟着 `id_left` / `id_right` 就消除了所有一致性因子，留下精确的普通 CT 表达式。
*)

(* ------------------------------------------------------------------ *)
(* 1. Internal adjunctions in `Cat` coincide with `F ∹ U` and `F ⊣ U`. / 1. `Cat` 中的内部附加与 `F ∹ U` 和 `F ⊣ U` 相一致。 *)
(* ------------------------------------------------------------------ *)

Section CatAdjunction.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context {U : D ⟶ C}.

(*
 Pristine obligations: the two structural fields we supply (`unit`/`counit`
 and `adj_unit`/`adj_counit`) are complete natural transformations, so the
 only obligations are the triangle/zig-zag laws, which we discharge by hand
 through the componentwise `fmap id` collapse. 

 --------
 原始义务：我们提供的两个结构域（`unit` / `counit` 和 `adj_unit` / `adj_counit`）是完整的自然变换，因此唯一的义务是三角/之字形律，我们通过分量式的 `fmap id` 折叠手动完成这些义务。
*)
#[local] Obligation Tactic := idtac.

(*
 Forward: an internal adjunction supplies the unit/counit data directly, and
 its bicategorical triangle identities give the two zig-zag identities. 

 --------
 前向：一个内部伴随直接提供单位/余单位数据，其双范畴三角恒等式给出了两个之字形恒等式。
*)
Program Definition Cat_BicatAdjunction_to_Transform
  (H : BicatAdjunction (B:=Cat_Bicategory) F U) : F ∹ U := {|
  Transformation.unit   := adj_unit   (B:=Cat_Bicategory) F U;
  Transformation.counit := adj_counit (B:=Cat_Bicategory) F U
|}.
Next Obligation.
  (* counit_fmap_unit: εF ∘ Fη = 1, read off the left bicat triangle at X. / counit_fmap_unit: εF ∘ Fη = 1，从 X 处的左双类三角形读取。 *)
  intros H X.
  pose proof (adj_triangle_left (B:=Cat_Bicategory) F U X) as TLX.
  simpl in TLX.
  rewrite !fmap_id in TLX.
  rewrite ?id_left, ?id_right in TLX.
  exact TLX.
Qed.
Next Obligation.
  (* fmap_counit_unit: Uε ∘ ηU = 1, read off the right bicat triangle at X. / fmap_counit_unit：Uε ∘ ηU = 1，从右双范畴三角形在 X 处读出。 *)
  intros H X.
  pose proof (adj_triangle_right (B:=Cat_Bicategory) F U X) as TRX.
  simpl in TRX.
  rewrite !fmap_id in TRX.
  rewrite ?id_left, ?id_right in TRX.
  exact TRX.
Qed.

(*
 Backward: the unit/counit data assembles into an internal adjunction, its two
 bicategorical triangle identities holding componentwise by the same collapse,
 where each side reduces to a zig-zag identity of the transform. 

 --------
 向后：单位/余单位数据组装成一个内部伴随，其中两个双范畴三角形恒等式在分量上由相同的坍缩成立，其中每一边都简化为变换的之字形恒等式。
*)
Program Definition Cat_Transform_to_BicatAdjunction
  (A : F ∹ U) : BicatAdjunction (B:=Cat_Bicategory) F U := {|
  adj_unit   := @Category.Adjunction.Natural.Transformation.unit   _ _ _ _ A;
  adj_counit := @Category.Adjunction.Natural.Transformation.counit _ _ _ _ A
|}.
Next Obligation.
  (* adj_triangle_left, componentwise, is εF ∘ Fη = 1. / adj_triangle_left，逐分量，是 εF ∘ Fη = 1。 *)
  intros A X.
  simpl.
  rewrite !fmap_id.
  rewrite ?id_left, ?id_right.
  exact (@Category.Adjunction.Natural.Transformation.counit_fmap_unit _ _ _ _ A X).
Qed.
Next Obligation.
  (* adj_triangle_right, componentwise, is Uε ∘ ηU = 1. / adj_triangle_right，逐分量，是 Uε ∘ ηU = 1。 *)
  intros A X.
  simpl.
  rewrite !fmap_id.
  rewrite ?id_left, ?id_right.
  exact (@Category.Adjunction.Natural.Transformation.fmap_counit_unit _ _ _ _ A X).
Qed.

(*
 Internal adjunctions in `Cat` are exactly unit/counit adjunctions `F ∹ U`.
 (Type-valued `↔`, i.e. `iffT`; `Print Assumptions` closed on both legs.)
 Both directions transport the unit/counit data verbatim — `adj_unit ↔ unit`,
 `adj_counit ↔ counit` — so this is the identity correspondence on that data
 (only the triangle-law witnesses are re-derived); record-level mutual
 inverseness is not separately asserted and is not needed downstream. 

 --------
 `Cat` 中的内部伴随正好是 `F ∹ U` 的单位/余单位伴随。
 （类型值 `↔`，即 `iffT`；`Print Assumptions` 在两边都闭合。）
 两个方向都逐字传递单位/余单位数据 —— `adj_unit ↔ unit`，`adj_counit ↔ counit` —— 因此这是该数据上的恒等对应关系
 （只有三角形律的证据是重新推导的）；记录级的相互逆性没有单独声明，也在后续处理中不需要。
*)
Theorem Cat_BicatAdjunction_iff :
  BicatAdjunction (B:=Cat_Bicategory) F U  ↔  (F ∹ U).
Proof.
  split.
  - exact Cat_BicatAdjunction_to_Transform.
  - exact Cat_Transform_to_BicatAdjunction.
Qed.

(*
 Composing with the `F ∹ U ↔ F ⊣ U` bridge (Universal.v): an internal
 adjunction in `Cat` yields a hom-set adjunction, and conversely. 

 --------
 使用 `F ∹ U ↔ F ⊣ U` 桥 (Universal.v) 作曲：在 `Cat` 中的一个内部伴随产生一个同态集伴随，反之亦然。
*)
Definition Cat_BicatAdjunction_Adjunction
  (H : BicatAdjunction (B:=Cat_Bicategory) F U) : F ⊣ U :=
  Adjunction_from_Transform (Cat_BicatAdjunction_to_Transform H).

Definition Cat_Adjunction_BicatAdjunction
  (A : F ⊣ U) : BicatAdjunction (B:=Cat_Bicategory) F U :=
  Cat_Transform_to_BicatAdjunction (Adjunction_to_Transform (A:=A)).

Theorem Cat_BicatAdjunction_Adjunction_iff :
  BicatAdjunction (B:=Cat_Bicategory) F U  ↔  (F ⊣ U).
Proof.
  split.
  - exact Cat_BicatAdjunction_Adjunction.
  - exact Cat_Adjunction_BicatAdjunction.
Qed.

End CatAdjunction.

(* ------------------------------------------------------------------ *)
(* 2. The two hom-adjunctions in `Cat` are the transpose and the / 2. 在 `Cat` 中的两个同态伴随是转置和 *)
(* counit whiskering. / 计数器打毛刺 *)
(* ------------------------------------------------------------------ *)

Section CatHomAdjunction.

Context {vx vy : Category}.
Context {F : vx ⟶ vy} {U : vy ⟶ vx}.
Context (A : BicatAdjunction (B:=Cat_Bicategory) F U).

(*
 Precomposition transpose `precomp_to A : (F ◯ c ⟹ d) → (c ⟹ U ◯ d)`, read
 componentwise, is the unit-transpose `⌊−⌋` of the induced adjunction: the
 unitor/associator components of `preΘ` collapse to identities. 

 --------
 先复合置换 `precomp_to A : (F ◯ c ⟹ d) → (c ⟹ U ◯ d)`，按分量读取，是诱导伴随的单位置换 `⌊−⌋`：`preΘ` 的单元/结合子分量简化为恒等映射。
*)
Lemma Cat_precomp_to_component {w0 : Category}
  {c : w0 ⟶ vx} {d : w0 ⟶ vy} (σ : F ◯ c ⟹ d) (t : w0) :
  transform[precomp_to A σ] t
    ≈ fmap[U] (σ t) ∘ adj_unit (B:=Cat_Bicategory) F U (fobj[c] t).
Proof.
  simpl.
  rewrite !fmap_id.
  rewrite ?id_left, ?id_right.
  reflexivity.
Qed.

(*
 The same, phrased through the hom-set transpose `⌊−⌋ = to adj[-]` of the
 induced adjunction: `precomp_to` at `Cat` IS `⌊−⌋` componentwise.  (The two
 sides are in fact definitionally equal — `Adjunction_from_Transform` sends
 `g` to `fmap[U] g ∘ η` — so `reflexivity` closes it after rewriting.) 

 --------
 同样，通过诱导伴随的同集换位 `⌊−⌋ = to adj [-]ZZ ` 表述：在 `Cat` 处，`precomp_to` 与 `⌊−⌋` 逐分量相等。（实际上两边在定义上是相等的——`Adjunction_from_Transform` 将 `g` 发送到 `fmap [U]ZZ  g ∘ η`——所以 `reflexivity` 在重写后将其闭合。）
*)
Lemma Cat_precomp_to_transpose {w0 : Category}
  {c : w0 ⟶ vx} {d : w0 ⟶ vy} (σ : F ◯ c ⟹ d) (t : w0) :
  transform[precomp_to A σ] t
    ≈ to adj[Cat_BicatAdjunction_Adjunction A] (σ t).
Proof.
  rewrite Cat_precomp_to_component.
  reflexivity.
Qed.

(*
 Postcomposition transpose `postcomp_to A : (c ⟹ e ◯ F) → (c ◯ U ⟹ e)`, read
 componentwise, is the counit `ε` whiskered by `e`: the unitor/associator
 components of `postΛ` collapse to identities. 

 --------
 后组合转置 `postcomp_to A : (c ⟹ e ◯ F) → (c ◯ U ⟹ e)`，按分量读取，是由 `e` 夹持的余单位 `ε`：`postΛ` 的单元/结合子分量塌缩为恒等式。
*)
Lemma Cat_postcomp_to_component {w0 : Category}
  {c : vx ⟶ w0} {e : vy ⟶ w0} (γ : c ⟹ e ◯ F) (t : vy) :
  transform[postcomp_to A γ] t
    ≈ fmap[e] (adj_counit (B:=Cat_Bicategory) F U t) ∘ γ (fobj[U] t).
Proof.
  simpl.
  rewrite !fmap_id.
  rewrite ?id_left, ?id_right.
  reflexivity.
Qed.

End CatHomAdjunction.

(* ------------------------------------------------------------------ *)
(* 3. Mates in `Cat` unfold to the transposes (the payoff). / 3. `Cat` 中的伙伴展开成转置（收益）。 *)
(* ------------------------------------------------------------------ *)

Section CatMates.

Context {x y x' y' : Category}.
Context {F  : x  ⟶ y }  {U  : y  ⟶ x }  (Af  : BicatAdjunction (B:=Cat_Bicategory) F  U ).
Context {F' : x' ⟶ y'}  {U' : y' ⟶ x'}  (Af' : BicatAdjunction (B:=Cat_Bicategory) F' U').
Context {a : x ⟶ x'} {b : y ⟶ y'}.
Context (σ : F' ◯ a ⟹ b ◯ F).

(*
 Raw unfolding of the mate: the classical pasting formula, in terms of the
 unit `η'` of `F' ⊣ U'`, the counit `ε` of `F ⊣ U`, `fmap`, and `σ` alone.
 Every coherence isomorphism (unitors, associators) contributes only a
 `fmap id`, cleared by the collapse; `α⁻¹ ∘ α = id` never even appears because
 the associator components are themselves identities in `Cat`. 

 --------
 对伴随的原始展开：经典粘贴公式，以  `η'`  单元  `F' ⊣ U'` 的形式，  `ε`  对偶元  `F ⊣ U` 、  `fmap` 和  `σ` 单独呈现。每个相干同构（单位子、结合子）仅贡献一个 `fmap id`，由压缩清除；  `α⁻¹ ∘ α = id` 从未出现，因为结合子分量在 `Cat` 本身就是恒等映射。
*)
Theorem Cat_mate_unfold_raw (Z : y) :
  transform[mate Af Af' σ] Z
    ≈ fmap[U'] (fmap[b] (adj_counit (B:=Cat_Bicategory) F U Z))
        ∘ (fmap[U'] (σ (fobj[U] Z))
             ∘ adj_unit (B:=Cat_Bicategory) F' U' (fobj[a] (fobj[U] Z))).
Proof.
  simpl.
  rewrite !fmap_id.
  rewrite ?id_left, ?id_right.
  reflexivity.
Qed.

(*
 The headline: the mate unfolds to the hom-set transpose `⌊−⌋` of `F' ⊣ U'`
 post-whiskered by the counit `ε` of `F ⊣ U`.  This is the form that makes the
 bicategorical mate usable from ordinary-CT files: `⌊ σ (U Z) ⌋` is the
 adjunction transpose of the component of `σ`. 

 --------
 标题：配偶展开为 `F' ⊣ U'` 的同集余变换 `⌊−⌋`，由 `F ⊣ U` 的余单位 `ε` 后胡须化。这是使双范畴配偶可用于普通 CT 文件的形式：`⌊ σ (U Z) ⌋` 是 `σ` 分量的伴随余变换。
*)
Theorem Cat_mate_unfold (Z : y) :
  transform[mate Af Af' σ] Z
    ≈ fmap[U'] (fmap[b] (adj_counit (B:=Cat_Bicategory) F U Z))
        ∘ to adj[Cat_BicatAdjunction_Adjunction Af'] (σ (fobj[U] Z)).
Proof.
  rewrite Cat_mate_unfold_raw.
  reflexivity.
Qed.

End CatMates.
