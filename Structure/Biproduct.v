Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.

Generalizable All Variables.

(** * Biproducts / 副产品 *)

(*
 nLab:      https://ncatlab.org/nlab/show/biproduct
 Wikipedia: https://en.wikipedia.org/wiki/Biproduct

 In a category with a zero object, a biproduct of two objects x and y is a
 single object x ⊕ y that is at once a product and a coproduct of the
 pair, with the injections and projections interacting through identity
 and zero morphisms (Wikipedia lists exactly these four equations; nLab
 states the same compatibility conditions):

 exl ∘ inl ≈ id        exr ∘ inr ≈ id
 exl ∘ inr ≈ 0         exr ∘ inl ≈ 0

 [Biproduct x y] packages the object together with both universal
 properties and the four interaction laws, and [HasBiproducts] chooses a
 biproduct for every pair of objects.  The satellite API mirrors the
 mediating-morphism trios of [Structure/Limit/Preservation.v]: [bi_pair]
 and [bi_copair] extract the product and coproduct mediators, each with
 two commutation lemmas and a uniqueness restatement; [bimap] is the
 action of the biproduct on a pair of morphisms; [bi_diag] and
 [bi_codiag] are the diagonal and codiagonal, the raw material for the
 semiadditive convolution downstream. 

 --------
 nLab:       https://ncatlab.org/nlab/show/biproduct 
 维基百科:  https://en.wikipedia.org/wiki/Biproduct 

 在具有零对象的范畴中，两个对象 x 和 y 的双积是单个对象 x ⊕ y，它同时是该对的积和余积，并且注入和投影通过恒等映射和零态射相互作用（维基百科列出了正是这四个方程；nLab 说明了相同的兼容条件）：

 exl ∘ inl ≈ id        exr ∘ inr ≈ id
 exl ∘ inr ≈ 0         exr ∘ inl ≈ 0[Biproduct x y] 将对象与通用属性及四条交互律一起打包，[HasBiproducts] 为每对对象选择一个双积。卫星 API 镜像 [Structure/Limit/Preservation.v] 的中介态射三元组：[bi_pair] 和 [bi_copair] 提取积和余积中介，每个都有两个交换引理和一个唯一性重述；[bimap] 是双积对一对态射的作用；[bi_diag] 和 [bi_codiag] 是对角和余对角，是半加性卷积下游的原料。
*)

Section Biproduct.

Context {C : Category}.
Context `{Z : @ZeroObject C}.

(*
 A biproduct of x and y: injections and projections satisfying the four
 interaction laws, such that (biproduct_obj, bi_exl, bi_exr) is a product
 of x and y and (biproduct_obj, bi_inl, bi_inr) is a coproduct. 

 --------
 x 和 y 的双积：满足四条交互律的注入和投影，使得 (biproduct_obj, bi_exl, bi_exr) 是 x 和 y 的积，并且 (biproduct_obj, bi_inl, bi_inr) 是余积。
*)
(*
   【Record Biproduct 语法与字段展开】/ Syntax & field walkthrough（薄）

   1) 这是什么 / What this is
      双积 = 同一对象既是积又是余积，且投影/内射满足「矩阵单位」四律
      （对角 id、反对角零）。需 ZeroObject。
      Object that is both product and coproduct with matrix-unit laws; needs 0.

   2) 数据 / Data
      biproduct_obj；bi_inl/bi_inr；bi_exl/bi_exr
      四交互律 + bi_is_product / bi_is_coproduct（两侧 UMP）

   3) HasBiproducts：每对对象选一个 Biproduct（半加性原料）。
      Choice of biproducts; feedstock for semiadditive structure.

   阅读：ZeroObject → 四律 → 两侧 UMP → bi_pair/bi_copair。
   Read: ZeroObject → four laws → both UMPs → mediators.
*)

Record Biproduct (x y : C) := {
  biproduct_obj : C;

  bi_inl : x ~> biproduct_obj;        (* coproduct injection (left) / 余积注射（左） *)
  bi_inr : y ~> biproduct_obj;        (* coproduct injection (right) / 余积注射（右） *)
  bi_exl : biproduct_obj ~> x;        (* product projection (left) / 产品投影（左） *)
  bi_exr : biproduct_obj ~> y;        (* product projection (right) / 产品投影（右） *)

  (* matching projection/injection composites are identities / 匹配的投影/注入复合是恒等映射 *)
  bi_exl_inl : bi_exl ∘ bi_inl ≈ id;
  bi_exr_inr : bi_exr ∘ bi_inr ≈ id;

  (* mixed projection/injection composites vanish / 混合投影/注射复合材料消失 *)
  bi_exl_inr : bi_exl ∘ bi_inr ≈ zero_mor;
  bi_exr_inl : bi_exr ∘ bi_inl ≈ zero_mor;

  (*
 the object is a product of x and y via bi_exl, bi_exr 

 --------
 该对象是通过 bi_exl、bi_exr 由 x 和 y 的乘积
*)
  bi_is_product : ∀ (z : C) (f : z ~> x) (g : z ~> y),
    ∃! h : z ~> biproduct_obj, (bi_exl ∘ h ≈ f) ∧ (bi_exr ∘ h ≈ g);

  (* and a coproduct of x and y via bi_inl, bi_inr / 以及通过 bi_inl、bi_inr 的 x 和 y 的余积 *)
  bi_is_coproduct : ∀ (z : C) (f : x ~> z) (g : y ~> z),
    ∃! h : biproduct_obj ~> z, (h ∘ bi_inl ≈ f) ∧ (h ∘ bi_inr ≈ g)
}.

(*
 Make the record parameters implicit for the projections, section-locally;
 the full implicit statuses (with C and Z) are restated after the
 section closes. 

 --------
 对投影的记录参数在段内局部设为隐式；完整的隐式状态（包括 C 和 Z）将在段结束后重新声明。
*)
Arguments biproduct_obj {x y} _.
Arguments bi_inl {x y} _.
Arguments bi_inr {x y} _.
Arguments bi_exl {x y} _.
Arguments bi_exr {x y} _.
Arguments bi_exl_inl {x y} _.
Arguments bi_exr_inr {x y} _.
Arguments bi_exl_inr {x y} _.
Arguments bi_exr_inl {x y} _.
Arguments bi_is_product {x y} _ _ _ _.
Arguments bi_is_coproduct {x y} _ _ _ _.

(*
 A category (with a zero object) has biproducts when every pair of
 objects carries one. 

 --------
 当每一对对象都有一个时，一个具有零对象的范畴就有双积。
*)
Class HasBiproducts := {
  biproduct (x y : C) : Biproduct x y
}.

(* * ** The product mediator [bi_pair] and its trio / * ** 产品中介 [bi_pair] 及其三重组合 *)

(*
 The pairing ⟨f, g⟩ into the biproduct, extracted from the product-side
 universal property. 

 --------
 将配对 ⟨f, g⟩ 输入到双积中，来源于乘积侧的普遍性质。
*)
Definition bi_pair {x y : C} (B : Biproduct x y) {z : C}
  (f : z ~> x) (g : z ~> y) : z ~> biproduct_obj B :=
  unique_obj (bi_is_product B z f g).

Lemma bi_exl_pair {x y : C} (B : Biproduct x y) {z : C}
  (f : z ~> x) (g : z ~> y) :
  bi_exl B ∘ bi_pair B f g ≈ f.
Proof. exact (fst (unique_property (bi_is_product B z f g))). Qed.

Lemma bi_exr_pair {x y : C} (B : Biproduct x y) {z : C}
  (f : z ~> x) (g : z ~> y) :
  bi_exr B ∘ bi_pair B f g ≈ g.
Proof. exact (snd (unique_property (bi_is_product B z f g))). Qed.

Lemma bi_pair_unique {x y : C} (B : Biproduct x y) {z : C}
  (f : z ~> x) (g : z ~> y) (v : z ~> biproduct_obj B) :
  bi_exl B ∘ v ≈ f → bi_exr B ∘ v ≈ g → bi_pair B f g ≈ v.
Proof.
  intros Hl Hr.
  exact (uniqueness (bi_is_product B z f g) v (Hl, Hr)).
Qed.

(*
 Any two morphisms into the biproduct with the same projections agree. 

 --------
 任意两个指向具有相同投影的双积的态射是相同的。
*)
Lemma bi_pair_eq {x y : C} (B : Biproduct x y) {z : C}
  (f : z ~> x) (g : z ~> y) (u v : z ~> biproduct_obj B) :
  bi_exl B ∘ u ≈ f → bi_exr B ∘ u ≈ g →
  bi_exl B ∘ v ≈ f → bi_exr B ∘ v ≈ g →
  u ≈ v.
Proof.
  intros Hul Hur Hvl Hvr.
  transitivity (bi_pair B f g).
  - symmetry.
    exact (bi_pair_unique B f g u Hul Hur).
  - exact (bi_pair_unique B f g v Hvl Hvr).
Qed.

(* Pairing respects ≈ in both components. / 配对在两个组件中都尊重 ≈。 *)
#[export] Instance bi_pair_respects {x y : C} (B : Biproduct x y) {z : C} :
  Proper (equiv ==> equiv ==> equiv) (@bi_pair x y B z).
Proof.
  intros f1 f2 Hf g1 g2 Hg.
  apply bi_pair_unique.
  - rewrite bi_exl_pair.
    now symmetry.
  - rewrite bi_exr_pair.
    now symmetry.
Qed.

(*
   * ** The coproduct mediator [bi_copair] and its trio 

   --------
   * ** 协同乘积调解器 [bi_copair] 及其三重体
*)

(*
 The copairing [f, g] out of the biproduct, extracted from the
 coproduct-side universal property. 

 --------
 从余积一侧的泛性质中提取出的双积分解 [f, g]。
*)
Definition bi_copair {x y : C} (B : Biproduct x y) {z : C}
  (f : x ~> z) (g : y ~> z) : biproduct_obj B ~> z :=
  unique_obj (bi_is_coproduct B z f g).

Lemma bi_copair_inl {x y : C} (B : Biproduct x y) {z : C}
  (f : x ~> z) (g : y ~> z) :
  bi_copair B f g ∘ bi_inl B ≈ f.
Proof. exact (fst (unique_property (bi_is_coproduct B z f g))). Qed.

Lemma bi_copair_inr {x y : C} (B : Biproduct x y) {z : C}
  (f : x ~> z) (g : y ~> z) :
  bi_copair B f g ∘ bi_inr B ≈ g.
Proof. exact (snd (unique_property (bi_is_coproduct B z f g))). Qed.

Lemma bi_copair_unique {x y : C} (B : Biproduct x y) {z : C}
  (f : x ~> z) (g : y ~> z) (v : biproduct_obj B ~> z) :
  v ∘ bi_inl B ≈ f → v ∘ bi_inr B ≈ g → bi_copair B f g ≈ v.
Proof.
  intros Hl Hr.
  exact (uniqueness (bi_is_coproduct B z f g) v (Hl, Hr)).
Qed.

(*
 Any two morphisms out of the biproduct with the same restrictions to the
 injections agree. 

 --------
 来自这个双积的任意两个同态，如果在注入上的限制相同，则它们相同。
*)
Lemma bi_copair_eq {x y : C} (B : Biproduct x y) {z : C}
  (f : x ~> z) (g : y ~> z) (u v : biproduct_obj B ~> z) :
  u ∘ bi_inl B ≈ f → u ∘ bi_inr B ≈ g →
  v ∘ bi_inl B ≈ f → v ∘ bi_inr B ≈ g →
  u ≈ v.
Proof.
  intros Hul Hur Hvl Hvr.
  transitivity (bi_copair B f g).
  - symmetry.
    exact (bi_copair_unique B f g u Hul Hur).
  - exact (bi_copair_unique B f g v Hvl Hvr).
Qed.

(* Copairing respects ≈ in both components. / Copairing 在两个分量中都尊重 ≈。 *)
#[export] Instance bi_copair_respects {x y : C} (B : Biproduct x y) {z : C} :
  Proper (equiv ==> equiv ==> equiv) (@bi_copair x y B z).
Proof.
  intros f1 f2 Hf g1 g2 Hg.
  apply bi_copair_unique.
  - rewrite bi_copair_inl.
    now symmetry.
  - rewrite bi_copair_inr.
    now symmetry.
Qed.

(* * ** Functorial action, diagonal, and codiagonal / * ** 函子作用、对角和余对角 *)

(*
 The action of the biproduct on a pair of morphisms, built through the
 product side: bimap f g ≈ ⟨f ∘ exl, g ∘ exr⟩. 

 --------
 通过乘积端构建的两个态射对上伴随积的作用：bimap f g ≈ ⟨f ∘ exl, g ∘ exr⟩。
*)
Definition bimap {x y x' y' : C}
  (Bxy : Biproduct x y) (Bx'y' : Biproduct x' y')
  (f : x ~> x') (g : y ~> y') :
  biproduct_obj Bxy ~> biproduct_obj Bx'y' :=
  bi_pair Bx'y' (f ∘ bi_exl Bxy) (g ∘ bi_exr Bxy).

Lemma bimap_exl {x y x' y' : C}
  (Bxy : Biproduct x y) (Bx'y' : Biproduct x' y')
  (f : x ~> x') (g : y ~> y') :
  bi_exl Bx'y' ∘ bimap Bxy Bx'y' f g ≈ f ∘ bi_exl Bxy.
Proof. exact (bi_exl_pair Bx'y' (f ∘ bi_exl Bxy) (g ∘ bi_exr Bxy)). Qed.

Lemma bimap_exr {x y x' y' : C}
  (Bxy : Biproduct x y) (Bx'y' : Biproduct x' y')
  (f : x ~> x') (g : y ~> y') :
  bi_exr Bx'y' ∘ bimap Bxy Bx'y' f g ≈ g ∘ bi_exr Bxy.
Proof. exact (bi_exr_pair Bx'y' (f ∘ bi_exl Bxy) (g ∘ bi_exr Bxy)). Qed.

(*
 The diagonal Δ = ⟨id, id⟩ into a biproduct of x with itself, and the
 codiagonal ∇ = [id, id] out of it. 

 --------
 对角线 Δ = ⟨id, id⟩ 映射到 x 与其自身的双积，余对角线 ∇ =  [id, id] 从中映射出。
*)
Definition bi_diag {x : C} (B : Biproduct x x) : x ~> biproduct_obj B :=
  bi_pair B id id.

Definition bi_codiag {x : C} (B : Biproduct x x) : biproduct_obj B ~> x :=
  bi_copair B id id.

End Biproduct.

(*
 Restate implicit arguments so the accessors are usable with implicit
 category and zero-object structure. 

 --------
 重新声明隐式参数，以便访问器可以用于隐式类别和零对象结构。
*)

Arguments Biproduct {C Z} x y.
Arguments HasBiproducts C {Z}.

Arguments biproduct_obj {C Z x y} _.
Arguments bi_inl {C Z x y} _.
Arguments bi_inr {C Z x y} _.
Arguments bi_exl {C Z x y} _.
Arguments bi_exr {C Z x y} _.
Arguments bi_exl_inl {C Z x y} _.
Arguments bi_exr_inr {C Z x y} _.
Arguments bi_exl_inr {C Z x y} _.
Arguments bi_exr_inl {C Z x y} _.
Arguments bi_is_product {C Z x y} _ _ _ _.
Arguments bi_is_coproduct {C Z x y} _ _ _ _.

Arguments biproduct {C Z _} x y.

Arguments bi_pair {C Z x y} B {z} f g.
Arguments bi_exl_pair {C Z x y} B {z} f g.
Arguments bi_exr_pair {C Z x y} B {z} f g.
Arguments bi_pair_unique {C Z x y} B {z} f g v _ _.
Arguments bi_pair_eq {C Z x y} B {z} f g u v _ _ _ _.

Arguments bi_copair {C Z x y} B {z} f g.
Arguments bi_copair_inl {C Z x y} B {z} f g.
Arguments bi_copair_inr {C Z x y} B {z} f g.
Arguments bi_copair_unique {C Z x y} B {z} f g v _ _.
Arguments bi_copair_eq {C Z x y} B {z} f g u v _ _ _ _.

Arguments bimap {C Z x y x' y'} Bxy Bx'y' f g.
Arguments bimap_exl {C Z x y x' y'} Bxy Bx'y' f g.
Arguments bimap_exr {C Z x y x' y'} Bxy Bx'y' f g.

Arguments bi_diag {C Z x} B.
Arguments bi_codiag {C Z x} B.
