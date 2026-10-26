Require Import Category.Lib.
Require Import Category.Theory.EckmannHilton.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Bicartesian.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Preadditive.

Generalizable All Variables.

(** * Semiadditive categories / * 半加性范畴 *)

(*
 nLab:      https://ncatlab.org/nlab/show/semiadditive+category
 Wikipedia: https://en.wikipedia.org/wiki/Biproduct

 A semiadditive category is a category in which finite products and finite
 coproducts exist and coincide (as biproducts).  Its hom-setoids are then
 canonically commutative monoids, and this file proves the two theorems
 that make the slogan precise, in both directions:

 (i)  [biproduct_addition]: in a category enriched in commutative monoids
 (a [Preadditive] category in the CMon sense of
 Structure/Preadditive.v) with a zero object, biproducts express the
 enrichment: f + g ≈ ∇ ∘ (f ⊕ g) ∘ Δ.  Moreover the enrichment
 already forces every product to be a biproduct
 ([cartesian_biproduct]), the key identity being the decomposition
 of the identity [biproduct_id_decomp]:
 inl ∘ exl + inr ∘ exr ≈ id.

 (ii) [bicartesian_preadditive]: conversely, in a bicartesian category
 with a zero object where the canonical comparison morphism
 x + y ~> x × y ([can_comparison]) is invertible, the convolution

 f + g  :=  (f ▽ g) ∘ can⁻¹ ∘ ⟨id, id⟩

 makes the category preadditive.  Commutativity and associativity
 of the convolution follow from an Eckmann–Hilton argument: the
 coproduct-flavoured convolution [conv] and the product-flavoured
 convolution [conv_pr] share the unit 0 and satisfy the interchange
 law (via [fork_merge] of Structure/Bicartesian.v), hence coincide
 and are commutative and associative. 

 --------
 nLab:       https://ncatlab.org/nlab/show/semiadditive+category 
 维基百科:  https://en.wikipedia.org/wiki/Biproduct 

 半加类是指一个类，其中有限积与有限余积存在并相同（作为双积）。其态射集合（hom-setoids）自然构成交换幺半群，并且该文件证明了使这一标语在两方向上成立的两个定理：

 (i)   [biproduct_addition] ：在一个以交换幺半群扩展的类中
 （即 Structure/Preadditive.v 中 CMon 意义下的 [Preadditive] 类）且具有零对象，双积表达了这种扩展：f + g ≈ ∇ ∘ (f ⊕ g) ∘ Δ。此外，这种扩展已经迫使每个积都是双积（[cartesian_biproduct]），关键恒等式是恒等映射的分解 [biproduct_id_decomp] ：
 inl ∘ exl + inr ∘ exr ≈ id。(ii) [bicartesian_preadditive]：相反地，在一个具有零对象的双笛卡尔范畴中，如果典型的比较态射 x + y ~> x × y ([can_comparison]) 是可逆的，则卷积

 f + g := (f ▽ g) ∘ can⁻¹ ∘ ⟨id, id⟩

 使该范畴成为预加性范畴。卷积的交换律和结合律可以通过 Eckmann–Hilton 论证得到：余积类型的卷积 [conv] 和积类型的卷积 [conv_pr] 共享单位 0 并满足交换律（通过 Structure/Bicartesian.v 的 [fork_merge]），因此它们相同并且是交换的和结合的。
*)

(* * ** Theorem (i): biproducts realize the preadditive structure / * ** 定理 (i)：双积实现了预加性结构 *)

Section BiproductAddition.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{P : @Preadditive C}.

(*
 The identity of a biproduct decomposes as the sum of its two
 “projection-then-injection” idempotents.  Both sides mediate the product
 cone (bi_exl, bi_exr), so they agree by the uniqueness half of the
 product universal property. 

 --------
 一个二元积的恒等映射可以分解为其两个“先投影后注入”幂等元的和。 两边都介导积锥 (bi_exl, bi_exr)，因此根据积的泛性质的唯一性部分，它们是一致的。
*)
Theorem biproduct_id_decomp {x y : C} (B : Biproduct x y) :
  padd (bi_inl B ∘ bi_exl B) (bi_inr B ∘ bi_exr B) ≈ id.
Proof.
  apply (bi_pair_eq B (bi_exl B) (bi_exr B)).
  - rewrite compose_padd_left.
    rewrite !comp_assoc.
    rewrite bi_exl_inl, bi_exl_inr.
    rewrite id_left.
    rewrite zero_mor_right.
    rewrite <- pzero_zero_mor.
    apply padd_zero_right.
  - rewrite compose_padd_left.
    rewrite !comp_assoc.
    rewrite bi_exr_inl, bi_exr_inr.
    rewrite id_left.
    rewrite zero_mor_right.
    rewrite <- pzero_zero_mor.
    apply padd_zero_left.
  - apply id_right.
  - apply id_right.
Qed.

(*
 Every morphism into a biproduct is the sum of its two components,
 reinjected.  This is the identity decomposition transported along the
 pairing. 

 --------
 每一个指向双积的态射都是其两个分量的和，再次注入。这是沿配对传输的恒等分解。
*)
Lemma bi_pair_decomp {x y z : C} (B : Biproduct x y)
  (f : z ~> x) (g : z ~> y) :
  bi_pair B f g ≈ padd (bi_inl B ∘ f) (bi_inr B ∘ g).
Proof.
  transitivity (id ∘ bi_pair B f g).
  - now rewrite id_left.
  - rewrite <- (biproduct_id_decomp B).
    rewrite compose_padd_right.
    apply padd_respects.
    + now rewrite <- comp_assoc, bi_exl_pair.
    + now rewrite <- comp_assoc, bi_exr_pair.
Qed.

(* Copairing against pairing computes the matrix product: a 1×2 row against a 2×1 column yields the sum of the diagonal composites. / 反配对与配对运算计算矩阵乘积：1×2 行与 2×1 列相乘得到对角线复合的和。 *)
Lemma bi_copair_pair {x y z w : C} (B : Biproduct x y)
  (u : x ~> w) (v : y ~> w) (f : z ~> x) (g : z ~> y) :
  bi_copair B u v ∘ bi_pair B f g ≈ padd (u ∘ f) (v ∘ g).
Proof.
  rewrite bi_pair_decomp.
  rewrite compose_padd_left.
  apply padd_respects.
  - now rewrite comp_assoc, bi_copair_inl.
  - now rewrite comp_assoc, bi_copair_inr.
Qed.

(* Pairing fuses with the biproduct's functorial action. / 配对与副产品的函子作用融合。 *)
Lemma bimap_bi_pair {x y x' y' z : C}
  (B : Biproduct x y) (B' : Biproduct x' y')
  (f : x ~> x') (g : y ~> y') (h : z ~> x) (k : z ~> y) :
  bimap B B' f g ∘ bi_pair B h k ≈ bi_pair B' (f ∘ h) (g ∘ k).
Proof.
  symmetry.
  apply bi_pair_unique.
  - rewrite comp_assoc.
    rewrite bimap_exl.
    now rewrite <- comp_assoc, bi_exl_pair.
  - rewrite comp_assoc.
    rewrite bimap_exr.
    now rewrite <- comp_assoc, bi_exr_pair.
Qed.

(*
 The first canonical theorem: the enrichment addition is computed by the
 biproduct as f + g ≈ ∇ ∘ (f ⊕ g) ∘ Δ. 

 --------
 第一个典型定理：加法的丰富性通过二积来计算，即 f + g ≈ ∇ ∘ (f ⊕ g) ∘ Δ。
*)
Theorem biproduct_addition {x y : C} (B : Biproduct x x) (B' : Biproduct y y)
  (f g : x ~> y) :
  padd f g ≈ bi_copair B' id id ∘ bimap B B' f g ∘ bi_pair B id id.
Proof.
  rewrite <- comp_assoc.
  rewrite bimap_bi_pair.
  rewrite bi_copair_pair.
  now rewrite !id_left, !id_right.
Qed.

End BiproductAddition.

(*
   * ** Theorem (i), continued: products are biproducts in a preadditive
   category 

   --------
   * ** 定理 (i)，续：在一个预加性范畴中，积是二积
*)

Section CartesianBiproduct.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{P : @Preadditive C}.
Context `{H : @Cartesian C}.

(*
 The product-side universal property, packaged for the biproduct record:
 the mediator is the fork, and uniqueness is [ump_products]. 

 --------
 乘积端的通用性质，为双积记录打包：调解器是叉子，唯一性是 [ump_products]。
*)
Definition cartesian_bi_is_product (x y z : C) (f : z ~> x) (g : z ~> y) :
  ∃! h : z ~> x × y, (exl ∘ h ≈ f) ∧ (exr ∘ h ≈ g).
Proof.
  unshelve refine {| unique_obj := f △ g |}.
  - split.
    + apply exl_fork.
    + apply exr_fork.
  - intros v Hv.
    symmetry.
    now apply ump_products.
Defined.

(*
 The identity decomposition for the product equipped with the additive
 injections id △ 0 and 0 △ id.  Both sides mediate the cone (exl, exr). 

 --------
 对于配备加法注入 id △ 0 和 0 △ id 的积，其身份分解。双方都调解锥 (exl, exr)。
*)
Lemma cartesian_id_decomp {x y : C} :
  padd ((id △ zero_mor) ∘ exl) ((zero_mor △ id) ∘ exr) ≈ id[x × y].
Proof.
  rewrite <- fork_exl_exr.
  apply ump_products; split.
  - rewrite compose_padd_left.
    rewrite !comp_assoc.
    rewrite !exl_fork.
    rewrite id_left.
    rewrite zero_mor_right.
    rewrite <- pzero_zero_mor.
    apply padd_zero_right.
  - rewrite compose_padd_left.
    rewrite !comp_assoc.
    rewrite !exr_fork.
    rewrite id_left.
    rewrite zero_mor_right.
    rewrite <- pzero_zero_mor.
    apply padd_zero_left.
Qed.

(*
 The coproduct-side universal property of the product: the mediator out of
 x × y is the sum of the composites through the projections, and its
 uniqueness follows from [cartesian_id_decomp]. 

 --------
 积的余积边的通用性质：x × y 的中介是通过投影的复合的和，其唯一性来自 [cartesian_id_decomp]。
*)
Definition cartesian_bi_is_coproduct (x y z : C) (f : x ~> z) (g : y ~> z) :
  ∃! h : x × y ~> z,
    (h ∘ (id △ zero_mor) ≈ f) ∧ (h ∘ (zero_mor △ id) ≈ g).
Proof using C H P Z.
  unshelve refine {| unique_obj := padd (f ∘ exl) (g ∘ exr) |}.
  - split.
    + rewrite compose_padd_right.
      rewrite <- !comp_assoc.
      rewrite exl_fork, exr_fork.
      rewrite id_right.
      rewrite zero_mor_left.
      rewrite <- pzero_zero_mor.
      apply padd_zero_right.
    + rewrite compose_padd_right.
      rewrite <- !comp_assoc.
      rewrite exl_fork, exr_fork.
      rewrite id_right.
      rewrite zero_mor_left.
      rewrite <- pzero_zero_mor.
      apply padd_zero_left.
  - intros v Hv.
    destruct Hv as [Hl Hr].
    symmetry.
    transitivity (v ∘ padd ((id △ zero_mor) ∘ exl) ((zero_mor △ id) ∘ exr)).
    + rewrite cartesian_id_decomp.
      now rewrite id_right.
    + rewrite compose_padd_left.
      rewrite !comp_assoc.
      rewrite Hl, Hr.
      reflexivity.
Defined.

(*
 In a preadditive category, every binary product is a biproduct: the
 injections are id △ 0 and 0 △ id, and the four interaction laws are the
 fork computation rules. 

 --------
 在一个前加性范畴中，每个二元积都是二重积：注入是 id △ 0 和 0 △ id，四条交互律是叉运算规则。
*)
Definition cartesian_biproduct (x y : C) : Biproduct x y := {|
  biproduct_obj := x × y;
  bi_inl := id △ zero_mor;
  bi_inr := zero_mor △ id;
  bi_exl := exl;
  bi_exr := exr;
  bi_exl_inl := exl_fork id zero_mor;
  bi_exr_inr := exr_fork zero_mor id;
  bi_exl_inr := exl_fork zero_mor id;
  bi_exr_inl := exr_fork id zero_mor;
  bi_is_product := cartesian_bi_is_product x y;
  bi_is_coproduct := cartesian_bi_is_coproduct x y
|}.

(*
 Corollary: a preadditive category with finite products has all binary
 biproducts. 

 --------
 推论：具有有限乘积的前加性范畴具有所有二元双积。
*)
Definition cartesian_has_biproducts : HasBiproducts C := {|
  biproduct := cartesian_biproduct
|}.

End CartesianBiproduct.

(*
   * ** Theorem (ii): semiadditivity from a bicartesian category with an
   invertible canonical comparison 

   --------
   * ** 定理 (ii)：来自具有可逆典型比较的双余积范畴的半加性
*)

Section BicartesianSemiadditive.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{HC : @Cartesian C}.
Context `{HD : @Cocartesian C}.

(* Two morphisms into a product agree when their projections agree. / 当两个态射的投影相同时，它们进入积的态射也相同。 *)
Lemma fork_ext {x y z : C} (u v : x ~> y × z) :
  exl ∘ u ≈ exl ∘ v → exr ∘ u ≈ exr ∘ v → u ≈ v.
Proof.
  intros Hl Hr.
  transitivity ((exl ∘ u) △ (exr ∘ u)).
  - rewrite fork_comp, fork_exl_exr.
    now rewrite id_left.
  - rewrite Hl, Hr.
    rewrite fork_comp, fork_exl_exr.
    now rewrite id_left.
Qed.

(*
 Dually, two morphisms out of a coproduct agree when their restrictions
 along the injections agree. 

 --------
 对应地，当沿注入的限制一致时，从余积出的两个态射也一致。
*)
Lemma merge_ext {x y z : C} (u v : x + y ~{C}~> z) :
  u ∘ inl ≈ v ∘ inl → u ∘ inr ≈ v ∘ inr → u ≈ v.
Proof.
  intros Hl Hr.
  transitivity ((u ∘ inl) ▽ (u ∘ inr)).
  - rewrite merge_comp, merge_inl_inr.
    now rewrite id_right.
  - rewrite Hl, Hr.
    rewrite merge_comp, merge_inl_inr.
    now rewrite id_right.
Qed.

(*
 The canonical comparison morphism from the coproduct to the product,
 the “identity matrix” ((id, 0), (0, id)). 

 --------
 从余积到积的典型比较态射，“单位矩阵” ((id, 0), (0, id))。
*)
Definition can_comparison (x y : C) : x + y ~{C}~> x × y :=
  (id △ zero_mor) ▽ (zero_mor △ id).

(* The two column computations... / 两栏计算…… *)
Lemma can_inl {x y : C} : can_comparison x y ∘ inl ≈ id △ zero_mor.
Proof. apply inl_merge. Qed.

Lemma can_inr {x y : C} : can_comparison x y ∘ inr ≈ zero_mor △ id.
Proof. apply inr_merge. Qed.

(* ...and the four matrix entries of the comparison. / ...以及比较的四个矩阵条目。 *)
Lemma exl_can_inl {x y : C} : exl ∘ can_comparison x y ∘ inl ≈ id.
Proof.
  rewrite <- comp_assoc, can_inl.
  apply exl_fork.
Qed.

Lemma exr_can_inl {x y : C} : exr ∘ can_comparison x y ∘ inl ≈ zero_mor.
Proof.
  rewrite <- comp_assoc, can_inl.
  apply exr_fork.
Qed.

Lemma exl_can_inr {x y : C} : exl ∘ can_comparison x y ∘ inr ≈ zero_mor.
Proof.
  rewrite <- comp_assoc, can_inr.
  apply exl_fork.
Qed.

Lemma exr_can_inr {x y : C} : exr ∘ can_comparison x y ∘ inr ≈ id.
Proof.
  rewrite <- comp_assoc, can_inr.
  apply exr_fork.
Qed.

(* Semiadditivity hypothesis: the canonical comparison is invertible. / 半加性假设：典型比较是可逆的。 *)
Context (E : ∀ x y : C, IsIsomorphism (can_comparison x y)).

Definition can_inv (x y : C) : x × y ~{C}~> x + y :=
  @two_sided_inverse C _ _ (can_comparison x y) (E x y).

Lemma can_can_inv {x y : C} : can_comparison x y ∘ can_inv x y ≈ id.
Proof. exact (@is_right_inverse C _ _ (can_comparison x y) (E x y)). Qed.

Lemma can_inv_can {x y : C} : can_inv x y ∘ can_comparison x y ≈ id.
Proof. exact (@is_left_inverse C _ _ (can_comparison x y) (E x y)). Qed.

(* Cancellation forms of the inverse laws, shaped for rewriting inside right-associated composites. / 逆律的消去形式，设计用于在右结合复合中重写。 *)
Lemma can_can_inv_cancel {x y z : C} (h : z ~> x × y) :
  can_comparison x y ∘ (can_inv x y ∘ h) ≈ h.
Proof.
  rewrite comp_assoc, can_can_inv.
  now rewrite id_left.
Qed.

Lemma can_inv_can_cancel {x y z : C} (h : z ~> x + y) :
  can_inv x y ∘ (can_comparison x y ∘ h) ≈ h.
Proof.
  rewrite comp_assoc, can_inv_can.
  now rewrite id_left.
Qed.

(* The inverse sends the additive injections of the product back to the coproduct injections. / 逆映射将乘积的加法注入映回到余积注入。 *)
Lemma can_inv_fork_inl {x y : C} : can_inv x y ∘ (id △ zero_mor) ≈ inl.
Proof.
  rewrite <- can_inl.
  apply can_inv_can_cancel.
Qed.

Lemma can_inv_fork_inr {x y : C} : can_inv x y ∘ (zero_mor △ id) ≈ inr.
Proof.
  rewrite <- can_inr.
  apply can_inv_can_cancel.
Qed.

(* The convolution addition on hom-setoids, in its coproduct-flavoured form (sum after the coproduct copairing)... x --⟨id,id⟩--> x × x --can⁻¹--> x + x --f ▽ g--> y / 同态集合上的卷积加法，在其余积风格的形式中（在余积配对之后求和）…… x --⟨id,id⟩--> x × x --can⁻¹--> x + x --f ▽ g--> y *)
Definition conv {x y : C} (f g : x ~> y) : x ~> y :=
  (f ▽ g) ∘ can_inv x x ∘ (id △ id).

(* ...and in its product-flavoured form (sum before the product pairing): x --f △ g--> y × y --can⁻¹--> y + y --[id,id]--> y / ...并且在其产品风味的形式下（在乘积配对之前的和）： x --f △ g--> y × y --can⁻¹--> y + y -- [id,id] --> y *)
Definition conv_pr {x y : C} (f g : x ~> y) : x ~> y :=
  (id ▽ id) ∘ can_inv y y ∘ (f △ g).

#[local] Instance conv_respects {x y : C} :
  Proper (equiv ==> equiv ==> equiv) (@conv x y).
Proof.
  intros f1 f2 Hf g1 g2 Hg.
  unfold conv.
  now rewrite Hf, Hg.
Qed.

#[local] Instance conv_pr_respects {x y : C} :
  Proper (equiv ==> equiv ==> equiv) (@conv_pr x y).
Proof.
  intros f1 f2 Hf g1 g2 Hg.
  unfold conv_pr.
  now rewrite Hf, Hg.
Qed.

(* Copairing with a zero component factors through a single projection. / 与零组件的共配对通过一个单一投影实现。 *)
Lemma merge_zero_left {x y : C} (f : x ~> y) :
  zero_mor ▽ f ≈ (f ∘ exr) ∘ can_comparison x x.
Proof.
  apply merge_ext.
  - rewrite inl_merge.
    rewrite <- !comp_assoc.
    rewrite can_inl.
    rewrite exr_fork.
    now rewrite zero_mor_left.
  - rewrite inr_merge.
    rewrite <- !comp_assoc.
    rewrite can_inr.
    rewrite exr_fork.
    now rewrite id_right.
Qed.

Lemma merge_zero_right {x y : C} (f : x ~> y) :
  f ▽ zero_mor ≈ (f ∘ exl) ∘ can_comparison x x.
Proof.
  apply merge_ext.
  - rewrite inl_merge.
    rewrite <- !comp_assoc.
    rewrite can_inl.
    rewrite exl_fork.
    now rewrite id_right.
  - rewrite inr_merge.
    rewrite <- !comp_assoc.
    rewrite can_inr.
    rewrite exl_fork.
    now rewrite zero_mor_left.
Qed.

(*
 Dually, pairing with a zero component factors through a single
 injection. 

 --------
 同样地，与零分量配对通过单一注入进行因式分解。
*)
Lemma fork_zero_left {x y : C} (f : x ~> y) :
  zero_mor △ f ≈ can_comparison y y ∘ (inr ∘ f).
Proof.
  apply fork_ext.
  - rewrite exl_fork.
    rewrite !comp_assoc.
    rewrite exl_can_inr.
    now rewrite zero_mor_right.
  - rewrite exr_fork.
    rewrite !comp_assoc.
    rewrite exr_can_inr.
    now rewrite id_left.
Qed.

Lemma fork_zero_right {x y : C} (f : x ~> y) :
  f △ zero_mor ≈ can_comparison y y ∘ (inl ∘ f).
Proof.
  apply fork_ext.
  - rewrite exl_fork.
    rewrite !comp_assoc.
    rewrite exl_can_inl.
    now rewrite id_left.
  - rewrite exr_fork.
    rewrite !comp_assoc.
    rewrite exr_can_inl.
    now rewrite zero_mor_right.
Qed.

(* The zero morphism is a two-sided unit for both convolutions. / 零同态是两边卷积的双边单位元。 *)
Lemma conv_zero_left {x y : C} (f : x ~> y) : conv zero_mor f ≈ f.
Proof.
  unfold conv.
  rewrite merge_zero_left.
  rewrite <- !comp_assoc.
  rewrite can_can_inv_cancel.
  rewrite exr_fork.
  now rewrite id_right.
Qed.

Lemma conv_zero_right {x y : C} (f : x ~> y) : conv f zero_mor ≈ f.
Proof.
  unfold conv.
  rewrite merge_zero_right.
  rewrite <- !comp_assoc.
  rewrite can_can_inv_cancel.
  rewrite exl_fork.
  now rewrite id_right.
Qed.

Lemma conv_pr_zero_left {x y : C} (f : x ~> y) : conv_pr zero_mor f ≈ f.
Proof.
  unfold conv_pr.
  rewrite fork_zero_left.
  rewrite <- !comp_assoc.
  rewrite can_inv_can_cancel.
  rewrite comp_assoc.
  rewrite inr_merge.
  now rewrite id_left.
Qed.

Lemma conv_pr_zero_right {x y : C} (f : x ~> y) : conv_pr f zero_mor ≈ f.
Proof.
  unfold conv_pr.
  rewrite fork_zero_right.
  rewrite <- !comp_assoc.
  rewrite can_inv_can_cancel.
  rewrite comp_assoc.
  rewrite inl_merge.
  now rewrite id_left.
Qed.

(* The Eckmann–Hilton interchange law between the two convolutions. It is exactly the bicartesian interchange [fork_merge] of Structure/Bicartesian.v, conjugated by can⁻¹ on both sides. / 两个卷积之间的 Eckmann–Hilton 交换律。它正是 Structure/Bicartesian.v 中的双笛卡尔交换 [fork_merge]，两边都由 can⁻¹ 共轭。 *)
Lemma conv_interchange {x y : C} (a b c d : x ~> y) :
  conv (conv_pr a b) (conv_pr c d) ≈ conv_pr (conv a c) (conv b d).
Proof.
  unfold conv, conv_pr.
  rewrite merge_comp.
  rewrite fork_merge.
  rewrite !fork_comp.
  rewrite !comp_assoc.
  reflexivity.
Qed.

(*
 The three consequences below are the abstract Eckmann–Hilton argument of
 Theory/EckmannHilton.v, read at the hom-setoid [x ~> y] with [conv] and
 [conv_pr] as the two operations.  Everything that argument asks for is
 already in hand: respectfulness is [conv_respects]/[conv_pr_respects],
 the four unit laws are the [conv_*_zero_*] lemmas above, and interchange
 is [conv_interchange].  Note that BOTH units are [zero_mor] here, so the
 abstract theorem's first conclusion ([eh_units], that the two units
 coincide) is [reflexivity] in this instance and is never invoked
 directly (the abstract proofs still route through it internally). 

 --------
 下面的三个结果是 Theory/EckmannHilton.v 中抽象的 Eckmann–Hilton 论证，在同态集合 [x ~> y] 上读取，[conv] 和 [conv_pr] 作为两个运算。论证所要求的一切已具备：保持性是 [conv_respects] / [conv_pr_respects]，四个单位律是上述 [conv_*_zero_*] 引理，换位律是 [conv_interchange]。注意这里两个单位都是 [zero_mor]，因此抽象定理的第一个结论（[eh_units]，即两个单位一致）在此实例中是 [reflexivity]，并且从未被直接调用（抽象证明仍然在内部通过它）。
*)

(* Eckmann–Hilton, first consequence: the two convolutions coincide. Via the abstract [eh_ops] of Theory/EckmannHilton.v. / Eckmann–Hilton，第一个结果：两个卷积相同。通过 Theory/EckmannHilton.v 的抽象 [eh_ops]。 *)
Lemma conv_conv_pr {x y : C} (f g : x ~> y) : conv f g ≈ conv_pr f g.
Proof.
  exact (eh_ops (@conv x y) (@conv_pr x y) zero_mor zero_mor
                (@conv_respects x y) (@conv_pr_respects x y)
                (@conv_zero_left x y) (@conv_zero_right x y)
                (@conv_pr_zero_left x y) (@conv_pr_zero_right x y)
                (@conv_interchange x y) f g).
Qed.

(*
 Eckmann–Hilton, second consequence: convolution is commutative.  Via the
 abstract [eh_comm] of Theory/EckmannHilton.v. 

 --------
 Eckmann–Hilton，第二个结论：卷积是交换的。通过 Theory/EckmannHilton.v 的抽象 [eh_comm]。
*)
Lemma conv_comm {x y : C} (f g : x ~> y) : conv f g ≈ conv g f.
Proof.
  exact (eh_comm (@conv x y) (@conv_pr x y) zero_mor zero_mor
                 (@conv_respects x y) (@conv_pr_respects x y)
                 (@conv_zero_left x y) (@conv_zero_right x y)
                 (@conv_pr_zero_left x y) (@conv_pr_zero_right x y)
                 (@conv_interchange x y) f g).
Qed.

(*
 Eckmann–Hilton, third consequence: convolution is associative.  Via the
 abstract [eh_assoc] of Theory/EckmannHilton.v. 

 --------
 Eckmann–Hilton，第三个结果：卷积是结合的。通过 Theory/EckmannHilton.v 的抽象 [eh_assoc]。
*)
Lemma conv_assoc {x y : C} (f g h : x ~> y) :
  conv (conv f g) h ≈ conv f (conv g h).
Proof.
  exact (eh_assoc (@conv x y) (@conv_pr x y) zero_mor zero_mor
                  (@conv_respects x y) (@conv_pr_respects x y)
                  (@conv_zero_left x y) (@conv_zero_right x y)
                  (@conv_pr_zero_left x y) (@conv_pr_zero_right x y)
                  (@conv_interchange x y) f g h).
Qed.

(* Composition distributes over convolution on the left (computed in the coproduct-flavoured form)... / 组合在左侧对卷积分配（以余积风格形式计算）… *)
Lemma conv_compose_left {x y z : C} (h : y ~> z) (f g : x ~> y) :
  h ∘ conv f g ≈ conv (h ∘ f) (h ∘ g).
Proof.
  unfold conv.
  rewrite !comp_assoc.
  rewrite <- merge_comp.
  reflexivity.
Qed.

(* ...and on the right (computed in the product-flavoured form). / ...在右侧（以乘积风味形式计算）。 *)
Lemma conv_compose_right {x y z : C} (f g : y ~> z) (h : x ~> y) :
  conv f g ∘ h ≈ conv (f ∘ h) (g ∘ h).
Proof.
  rewrite !conv_conv_pr.
  unfold conv_pr.
  rewrite <- !comp_assoc.
  rewrite <- fork_comp.
  reflexivity.
Qed.

(*
 The second canonical theorem: a bicartesian category with a zero object
 in which the canonical comparison x + y ~> x × y is invertible is
 preadditive (CMon-enriched), with convolution as addition and the zero
 morphism as unit.  Together with [cartesian_biproduct] this closes the
 loop: such a category is semiadditive, i.e. its products and coproducts
 are biproducts. 

 --------
 第二条典范定理：一个具有零对象的双笛卡尔范畴，其中典范比较 x + y ~> x × y 可逆，是预加性的（CMon-增强的），卷积作为加法，零态射作为单位。 与 [cartesian_biproduct] 一起，这闭合了循环：这样的范畴是半加性的，即它的积和余积是双积。
*)
Definition bicartesian_preadditive : Preadditive C := {|
  padd := @conv;
  pzero := @zero_mor C Z;
  padd_respects := @conv_respects;
  padd_assoc := @conv_assoc;
  padd_comm := @conv_comm;
  padd_zero_left := @conv_zero_left;
  compose_padd_left := @conv_compose_left;
  compose_padd_right := @conv_compose_right;
  compose_pzero_left := @zero_mor_right C Z;
  compose_pzero_right := @zero_mor_left C Z
|}.

End BicartesianSemiadditive.
