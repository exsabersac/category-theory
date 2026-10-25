Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Theory.Bicategory.

Generalizable All Variables.

(*
The bicategory composition notations are declared with `where` clauses local
   to the class body in Theory/Bicategory.v, so they do not persist to importing
   files. They are reserved globally, however; re-establish the interpretations
   here (at the reserved levels) so the 2-cell calculus below reads naturally.
   `∘∘` is vertical 2-cell composition, `∘∘∘` horizontal 1-cell composition.

--------
双范畴的组合记号在 Theory/Bicategory.v 的类主体中通过 `where` 子句声明，因此它们不会保留到导入文件中。然而，它们在全局是保留的；在此处（在保留的级别上）重新建立这些解释，这样下面的 2-胞计算就能自然地读取。`∘∘` 是垂直 2-胞组合，`∘∘∘` 是水平 1-胞组合。
*)
Infix "∘∘" := vcompose : category_scope.
Notation "f ∘∘∘ g" := (hcompose (f, g)) : category_scope.

(** Adjunctions inside a bicategory / 双范畴中的伴随 *)

(*
nLab: https://ncatlab.org/nlab/show/adjunction+in+a+bicategory

   An adjunction inside a bicategory `B` is the internalisation of the ordinary
   notion of adjoint functors: it lives entirely in the 2-cell calculus of `B`.
   Fix two 0-cells `x y : bi0cell`. An adjunction `f ⊣ u` consists of a pair of
   1-cells `f : x ~~> y` (the left adjoint) and `u : y ~~> x` (the right
   adjoint) together with two 2-cells

     - a unit    η : Id_x ⟹ u ∘ f     (in the hom-category `bicat x x`), and
     - a counit  ε : f ∘ u ⟹ Id_y     (in the hom-category `bicat y y`),

   satisfying the two triangle (zig-zag / swallowtail) identities. Because
   horizontal composition in a bicategory is associative and unital only up to
   the coherence 2-isomorphisms `hassoc`, `hunit_left`, `hunit_right`, the two
   zig-zag composites do not literally start and end at `f` and `u`; they are
   conjugated by the unitors and the associator so that the endpoints become the
   1-cells `f` and `u` themselves. The Godement/whiskering operation `hcomp2`
   (the functorial action of `hcompose` on a pair of 2-cells) supplies the
   whiskerings `f ⊲ η` and `ε ⊳ f` that make up each composite.

   Specialising `B` to the bicategory `Cat` (where `bicat C D := [C, D]`,
   horizontal composition is functor composition, and the coherences are the
   canonical natural isomorphisms) recovers exactly the counit/unit presentation
   of an ordinary adjunction `F ⊣ U` from `Theory/Adjunction.v`; this file states
   the general notion through `hcomp2`/`hassoc`/`hunit_*` so that the mates
   correspondence can be developed uniformly over any bicategory.

--------
nLab：https://ncatlab.org/nlab/show/adjunction+in+a+bicategory

二范畴 `B` 中的附加物是普通事物的内化
 伴随的概念：它完全存在于 `B` 的 2 单元演算中。 
修复两个 0 单元 `x y : bi0cell`。 附件 `f ⊣ u` 由一对组成
 1-细胞 `f : x ~~> y`（左伴随）和 `u : y ~~> x`（右伴随）
 伴随）与两个 2 细胞一起

- 单位 η : Id_x ⟹ u ∘ f （在 hom 范畴 `bicat x x` 中），以及
 - 单位 ε : f ∘ u ⟹ Id_y （在 hom 范畴 `bicat y y` 中），

满足两个三角形（锯齿形/燕尾形）恒等式。 因为
 二范畴中的水平组合仅在以下范围内是关联且统一的：
 相干 2-同构 `hassoc`、`hunit_left`、`hunit_right`，这两个
 之字形复合材料实际上并不以 `f` 和 `u` 开始和结束； 他们是
 由单位子和缔合子共轭，使得端点成为
 1-cell `f` 和 `u` 本身。 Godement/晶须操作 `hcomp2`
 （`hcompose` 对一对 2 细胞的功能作用）提供
 构成每种复合材料的 `f ⊲ η` 和 `ε ⊳ f` 晶须。

将 `B` 专门化为二类 `Cat`（其中 `bicat C D := XPROTECT0X`、
 水平复合是函子复合，相干性是
 规范的自然同构）准确地恢复了单位/单位的表示
 `Theory/Adjunction.v` 的普通附件 `F ⊣ U`； 该文件指出
 通过 `hcomp2`/`hassoc`/`hunit_*` 的一般概念，以便配合
 对应关系可以在任何二类上统一开发。
*)

Section BicatAdjunction.

Context {B : Bicategory}.

(* ------------------------------------------------------------------ *)
(* The Godement / interchange calculus of `hcomp2`. / `hcomp2` 的 Godement / 交换演算。                    *)
(*                                                                     *)
(* `hcomp2 θ η` is by definition `fmap[hcompose] (θ, η)`, so its whole / `hcomp2 θ η` 根据定义是 `fmapXPROTECT0X (θ, η)`，所以它的整体 *)
(* algebra is the functoriality of the horizontal-composition functor / 代数是水平组合函子函子性的体现 *)
(* transported through the componentwise structure of the product / 通过乘积的分量结构传输     *)
(* category `bicat y z ∏ bicat x y`. These lemmas package that algebra / 范畴 `bicat y z ∏ bicat x y`。这些词条打包了那个代数 *)
(* for use in the triangle and uniqueness proofs below. / 用于下面的三角形和唯一性证明。                *)
(* ------------------------------------------------------------------ *)

(* `hcomp2` respects `≈` in each argument (it is the action of a functor). / `hcomp2` 在每个参数中尊重 `≈`（这是函子的一种操作）。 *)
#[local] Instance hcomp2_respects
  {x y z : bi0cell} {g g' : bicat y z} {f f' : bicat x y} :
  Proper (equiv ==> equiv ==> equiv) (@hcomp2 B x y z g g' f f').
Proof.
  proper.
  exact (@fmap_respects _ _ (@hcompose B x y z)
           (g, f) (g', f') (x0, x1) (y0, y1) (X, X0)).
Qed.

(*
The horizontal composite of identity 2-cells is the identity 2-cell on the
   horizontal composite 1-cell (`hcompose` preserves identities).

--------
恒等 2-元的水平复合是水平复合 1-元上的恒等 2-元（`hcompose` 保持恒等）。
*)
Lemma hcomp2_id {x y z : bi0cell} (g : bicat y z) (f : bicat x y) :
  hcomp2 (bi2id (a:=g)) (bi2id (a:=f)) ≈ bi2id (a:=g ∘∘∘ f).
Proof. exact (@fmap_id _ _ (@hcompose B x y z) (g, f)). Qed.

(*
Interchange: a horizontal composite of vertical composites is the vertical
   composite of the horizontal composites (`hcompose` preserves composition).

--------
互换：水平复合的垂直复合体是水平复合体的垂直复合体（`hcompose` 保留复合性）。
*)
Lemma hcomp2_comp {x y z : bi0cell}
  {g g' g'' : bicat y z} {f f' f'' : bicat x y}
  (θ' : g' ~> g'') (θ : g ~> g') (η' : f' ~> f'') (η : f ~> f') :
  hcomp2 (θ' ∘∘ θ) (η' ∘∘ η) ≈ hcomp2 θ' η' ∘∘ hcomp2 θ η.
Proof.
  exact (@fmap_comp _ _ (@hcompose B x y z)
           (g, f) (g', f') (g'', f'') (θ', η') (θ, η)).
Qed.

(*
Left whiskering `g ⊲ η := hcomp2 (id g) η` and right whiskering
   `η ⊳ f := hcomp2 η (id f)`, together with their functoriality laws.

--------
左鞭毛 `g ⊲ η := hcomp2 (id g) η` 和右鞭毛 `η ⊳ f := hcomp2 η (id f)`，以及它们的函子律。
*)
Definition lwhisker {x y z : bi0cell} (g : bicat y z) {f f' : bicat x y}
  (η : f ~> f') : (g ∘∘∘ f) ~> (g ∘∘∘ f') := hcomp2 (bi2id (a:=g)) η.

Definition rwhisker {x y z : bi0cell} {g g' : bicat y z} (θ : g ~> g')
  (f : bicat x y) : (g ∘∘∘ f) ~> (g' ∘∘∘ f) := hcomp2 θ (bi2id (a:=f)).

Lemma lwhisker_id {x y z : bi0cell} (g : bicat y z) (f : bicat x y) :
  lwhisker g (bi2id (a:=f)) ≈ bi2id.
Proof. exact (hcomp2_id g f). Qed.

Lemma rwhisker_id {x y z : bi0cell} (g : bicat y z) (f : bicat x y) :
  rwhisker (bi2id (a:=g)) f ≈ bi2id.
Proof. exact (hcomp2_id g f). Qed.

Lemma lwhisker_comp {x y z : bi0cell} (g : bicat y z)
  {f f' f'' : bicat x y} (η' : f' ~> f'') (η : f ~> f') :
  lwhisker g (η' ∘∘ η) ≈ lwhisker g η' ∘∘ lwhisker g η.
Proof.
  unfold lwhisker.
  rewrite <- (bi2id_left (bi2id (a:=g))) at 1.
  now rewrite hcomp2_comp.
Qed.

Lemma rwhisker_comp {x y z : bi0cell}
  {g g' g'' : bicat y z} (θ' : g' ~> g'') (θ : g ~> g') (f : bicat x y) :
  rwhisker (θ' ∘∘ θ) f ≈ rwhisker θ' f ∘∘ rwhisker θ f.
Proof.
  unfold rwhisker.
  rewrite <- (bi2id_left (bi2id (a:=f))) at 1.
  now rewrite hcomp2_comp.
Qed.

(*
Whiskering respects `≈` in its 2-cell argument. Stated as congruence lemmas
   (rather than `Proper` instances) because a whisker's result type depends on
   the 1-cell argument, which blocks the pointwise `Proper` search; these support
   whole-term rewrites of a whisker in a composite.

--------
Whiskering 在其 2-元参数中尊重 `≈`。以同余引理的形式陈述（而不是 `Proper` 实例），因为 whisker 的结果类型依赖于 1-元参数，这会阻止逐点 `Proper` 搜索；这些支持在复合项中对 whisker 的整体项重写。
*)
Lemma lwhisker_cong {x y z : bi0cell} (g : bicat y z) {f f' : bicat x y}
  (η η' : f ~> f') : η ≈ η' → lwhisker g η ≈ lwhisker g η'.
Proof. intro E; unfold lwhisker; now rewrite E. Qed.

Lemma rwhisker_cong {x y z : bi0cell} {g g' : bicat y z} (θ θ' : g ~> g')
  (f : bicat x y) : θ ≈ θ' → rwhisker θ f ≈ rwhisker θ' f.
Proof. intro E; unfold rwhisker; now rewrite E. Qed.

(*
A general horizontal composite factors as a right whisker followed by a left
   whisker, in either order (the two orders agreeing is the interchange law).

--------
一个一般的水平复合因子可以分解为一个右胡须，随后是一个左胡须，顺序可以是任意的（两种顺序相同即为交换律）。
*)
Lemma hcomp2_lwhisker_rwhisker {x y z : bi0cell}
  {g g' : bicat y z} {f f' : bicat x y} (θ : g ~> g') (η : f ~> f') :
  hcomp2 θ η ≈ lwhisker g' η ∘∘ rwhisker θ f.
Proof.
  unfold lwhisker, rwhisker.
  rewrite <- hcomp2_comp.
  now rewrite bi2id_left, bi2id_right.
Qed.

Lemma hcomp2_rwhisker_lwhisker {x y z : bi0cell}
  {g g' : bicat y z} {f f' : bicat x y} (θ : g ~> g') (η : f ~> f') :
  hcomp2 θ η ≈ rwhisker θ f' ∘∘ lwhisker g η.
Proof.
  unfold lwhisker, rwhisker.
  rewrite <- hcomp2_comp.
  now rewrite bi2id_left, bi2id_right.
Qed.

(*
The middle-four interchange in whisker form: the two whiskers of a 2-cell by
   the two legs of a horizontal composite commute past one another.

--------
胡须形式的中四交换：一个 2-胞体的两根胡须与一个水平复合体的两条支腿互相经过。
*)
Lemma whisker_exchange {x y z : bi0cell}
  {g g' : bicat y z} {f f' : bicat x y} (θ : g ~> g') (η : f ~> f') :
  lwhisker g' η ∘∘ rwhisker θ f ≈ rwhisker θ f' ∘∘ lwhisker g η.
Proof.
  rewrite <- hcomp2_lwhisker_rwhisker.
  now rewrite hcomp2_rwhisker_lwhisker.
Qed.

(*
The three single-whisker naturality squares of the associator, each obtained
   from the general `hassoc_natural` field by taking two of the three 2-cells to
   be identities and collapsing the resulting `hcomp2 bi2id bi2id` via
   `hcomp2_id`. They let a whisker be transported across the associator.

--------
结合子的三个单须自然性方块，每个方块都是通过将一般的 `hassoc_natural` 场中的三个 2-胞中的两个取为恒等，并通过 `hcomp2_id` 塌缩由此产生的 `hcomp2 bi2id bi2id` 来获得的。它们允许一个胡须被在结合子上进行传送。
*)

(* Whiskering the outer (top) leg past the associator. / 将外侧（顶部）腿经过关联器时搅拌。 *)
Lemma assoc_nat_top {w x' y' z' : bi0cell} {h h' : bicat y' z'}
  (θ : h ~> h') (g : bicat x' y') (k : bicat w x') :
  rwhisker θ (g ∘∘∘ k) ∘∘ to (hassoc h g k)
    ≈ to (hassoc h' g k) ∘∘ rwhisker (rwhisker θ g) k.
Proof.
  pose proof (hassoc_natural θ (bi2id (a:=g)) (bi2id (a:=k))) as HN.
  now rewrite hcomp2_id in HN.
Qed.

(* Whiskering the middle leg past the associator. / 将中腿打毛经过联想器。 *)
Lemma assoc_nat_mid {w x' y' z' : bi0cell} (h : bicat y' z')
  {g g' : bicat x' y'} (γ : g ~> g') (k : bicat w x') :
  lwhisker h (rwhisker γ k) ∘∘ to (hassoc h g k)
    ≈ to (hassoc h g' k) ∘∘ rwhisker (lwhisker h γ) k.
Proof.
  pose proof (hassoc_natural (bi2id (a:=h)) γ (bi2id (a:=k))) as HN.
  now unfold lwhisker, rwhisker.
Qed.

(* Whiskering the inner (bottom) leg past the associator. / 将内侧（下方）腿擦过关联器。 *)
Lemma assoc_nat_bot {w x' y' z' : bi0cell} (h : bicat y' z')
  (g : bicat x' y') {k k' : bicat w x'} (η : k ~> k') :
  lwhisker h (lwhisker g η) ∘∘ to (hassoc h g k)
    ≈ to (hassoc h g k') ∘∘ lwhisker (h ∘∘∘ g) η.
Proof.
  pose proof (hassoc_natural (bi2id (a:=h)) (bi2id (a:=g)) η) as HN.
  now rewrite hcomp2_id in HN.
Qed.

(*
The coherence 2-isomorphisms live in the hom-categories `bicat _ _`, so their
   inverse laws are stated by the generic `iso_to_from`/`iso_from_to` with the
   ambient `∘`/`id`. These thin wrappers restate them in the vertical-composition
   notation `∘∘`/`bi2id` used throughout, so `rewrite` matches uniformly (the
   proofs are by conversion, since `∘` on `bicat x y` is `vcompose`).

--------
相干 2-同构存在于同态范畴 `bicat _ _` 中，因此它们的逆律由带有环境 `∘`/`id` 的通用 `iso_to_from`/`iso_from_to` 表示。这些薄包装在整个文中使用的纵向组合标记法 `∘∘`/`bi2id` 中重新表述它们，因此 `rewrite` 统一匹配（证明是通过转换进行的，因为 `bicat x y` 上的 `∘` 是 `vcompose`）。
*)
Lemma vto_vfrom {x y : bi0cell} {A A' : bicat x y} (i : A ≅[bicat x y] A') :
  to i ∘∘ from i ≈ bi2id.
Proof. exact (iso_to_from i). Qed.

Lemma vfrom_vto {x y : bi0cell} {A A' : bicat x y} (i : A ≅[bicat x y] A') :
  from i ∘∘ to i ≈ bi2id.
Proof. exact (iso_from_to i). Qed.

(*
Master conjugation lemma: a `to`-direction naturality square for two
   coherence isos transposes to the `from`-direction one. Every inverse-unitor
   and inverse-associator naturality used below is an instance.

--------
主结合元词条：双重相干同构的 `to` 方向的自然性平方会转置为 `from` 方向的平方。下面使用的每个逆单位元和逆结合元自然性都是一个实例。
*)
Lemma iso_conj_from {x y : bi0cell} {A A' Bb Bb' : bicat x y}
  (i : A ≅[bicat x y] Bb) (i' : A' ≅[bicat x y] Bb')
  (η : Bb ~> Bb') (θ : A ~> A') :
  η ∘∘ to i ≈ to i' ∘∘ θ → from i' ∘∘ η ≈ θ ∘∘ from i.
Proof.
  intro HN.
  transitivity ((from i' ∘∘ η) ∘∘ (to i ∘∘ from i)).
  { rewrite vto_vfrom. now rewrite bi2id_right. }
  transitivity (from i' ∘∘ ((η ∘∘ to i) ∘∘ from i)).
  { now rewrite !vcompose_assoc. }
  rewrite HN.
  transitivity ((from i' ∘∘ to i') ∘∘ (θ ∘∘ from i)).
  { now rewrite !vcompose_assoc. }
  rewrite vfrom_vto.
  now rewrite bi2id_left.
Qed.

(* Inverse-direction unitor naturalities, as instances of `iso_conj_from`. / 逆方向的单位自然性，作为 `iso_conj_from` 的实例。 *)
Lemma hunit_left_from_natural {x y : bi0cell} {f f' : bicat x y}
  (η : f ~> f') :
  from (hunit_left f') ∘∘ η ≈ lwhisker bi1id η ∘∘ from (hunit_left f).
Proof. exact (iso_conj_from _ _ _ _ (hunit_left_natural η)). Qed.

Lemma hunit_right_from_natural {x y : bi0cell} {f f' : bicat x y}
  (η : f ~> f') :
  from (hunit_right f') ∘∘ η ≈ rwhisker η bi1id ∘∘ from (hunit_right f).
Proof. exact (iso_conj_from _ _ _ _ (hunit_right_natural η)). Qed.

(*
Whisker-form restatements of the `to`-direction unitor naturality fields
   (definitionally equal to the fields, since `lwhisker`/`rwhisker` unfold to
   `hcomp2`), so they compose uniformly with the whisker calculus.

--------
`to`方向的单位或自然性场的胡须形式重述（从定义上等同于这些场，因为`lwhisker`/`rwhisker`展开为`hcomp2`），因此它们可以与胡须演算统一地组合。
*)
Lemma hunit_left_nat {x y : bi0cell} {f f' : bicat x y} (η : f ~> f') :
  η ∘∘ to (hunit_left f) ≈ to (hunit_left f') ∘∘ lwhisker bi1id η.
Proof. exact (hunit_left_natural η). Qed.

Lemma hunit_right_nat {x y : bi0cell} {f f' : bicat x y} (η : f ~> f') :
  η ∘∘ to (hunit_right f) ≈ to (hunit_right f') ∘∘ rwhisker η bi1id.
Proof. exact (hunit_right_natural η). Qed.

(* ------------------------------------------------------------------ *)
(* The adjunction class. / 伴随类。                                               *)
(* ------------------------------------------------------------------ *)

(*
`f ⊣ u` inside `B`: unit and counit 2-cells and the two triangle identities,
   each stated as an equation between a unitor/associator-conjugated whiskering
   composite with endpoints `f ~> f` (resp. `u ~> u`) and the identity 2-cell.

   The left triangle spells out that the zig-zag

     f = f ∘ Id  ⟹  f ∘ (u ∘ f)  ⟹  (f ∘ u) ∘ f  ⟹  Id ∘ f = f

   (unit whiskered on the left of `f`, reassociated, then counit whiskered on
   the right of `f`, all conjugated by the right/left unitors) is `id[f]`. The
   right triangle is the mirror statement for `u`.

--------
`B` 内的 `f ⊣ u`：单位和单位 2 单元以及两个三角形恒等式，
 每个都表示为单位/缔合体共轭晶须之间的方程
 与端点 `f ~> f`（或 `u ~> u`）和恒等 2-cell 的复合。 

左边的三角形表明锯齿形

 f = f ∘ Id ⟹ f ∘ (u ∘ f) ⟹ (f ∘ u) ∘ f ⟹ Id ∘ f = f

 （`f` 左侧的单元须重新关联，然后单元须在
 `f` 的右侧（全部由右/左单位共轭）是 `idXPROTECT0X`。 的
 直角三角形是 `u` 的镜像语句。
*)

Class BicatAdjunction {x y : bi0cell} (f : bicat x y) (u : bicat y x) := {
  adj_unit   : bi1id ~{bicat x x}~> (u ∘∘∘ f);   (* η : Id_x ⟹ u ∘ f / η : Id_x ⟹ u ∘ f *)
  adj_counit : (f ∘∘∘ u) ~{bicat y y}~> bi1id;   (* ε : f ∘ u ⟹ Id_y / ε : f ∘ u ⟹ Id_y *)

  (* Left triangle: (ε ⊳ f) ∘ α⁻¹ ∘ (f ⊲ η) conjugated by ρ⁻¹ and λ is id[f]. / 左三角形: (ε ⊳ f) ∘ α⁻¹ ∘ (f ⊲ η) 被 ρ⁻¹ 和 λ 共轭是 id[f]。 *)
  adj_triangle_left :
    to (hunit_left f)
      ∘∘ hcomp2 adj_counit (bi2id (a:=f))
      ∘∘ from (hassoc f u f)
      ∘∘ hcomp2 (bi2id (a:=f)) adj_unit
      ∘∘ from (hunit_right f)
    ≈ bi2id (a:=f);

  (* Right triangle: (u ⊲ ε) ∘ α ∘ (η ⊳ u) conjugated by λ⁻¹ and ρ is id[u]. / 直角三角形: (u ⊲ ε) ∘ α ∘ (η ⊳ u) 由 λ⁻¹ 和 ρ 共轭是 id[u]。 *)
  adj_triangle_right :
    to (hunit_right u)
      ∘∘ hcomp2 (bi2id (a:=u)) adj_counit
      ∘∘ to (hassoc u f u)
      ∘∘ hcomp2 adj_unit (bi2id (a:=u))
      ∘∘ from (hunit_left u)
    ≈ bi2id (a:=u)
}.

End BicatAdjunction.

Arguments BicatAdjunction {B x y} f u.
Arguments adj_unit {B x y} f u {_}.
Arguments adj_counit {B x y} f u {_}.
Arguments adj_triangle_left {B x y} f u {_}.
Arguments adj_triangle_right {B x y} f u {_}.

(** Uniqueness of adjoints up to invertible 2-cell / 伴随的唯一性至可逆二胞 *)

(*
Two right adjoints of the same 1-cell `f` are related by an invertible
   2-cell. The comparison 2-cell is the *mate of the identity*: given right
   adjoints `a` and `b` of `f`, the composite

     matecell : a  ⟹  Id_x ∘ a  ⟹  (b ∘ f) ∘ a  ⟹  b ∘ (f ∘ a)  ⟹  b ∘ Id_y  ⟹  b

   whiskering the unit `η_b` of `b` on the right of `a`, reassociating, then
   whiskering the counit `ε_a` of `a` on the left of `b`. The heart of the
   argument is a characterisation: `matecell` is the *unique* 2-cell `γ : a ⟹ b`
   compatible with the units, `(γ ⊳ f) ∘ η_a ≈ η_b` (`mate_charac`), together
   with the fact that `matecell` itself is unit-compatible (`mate_unit_compat`).
   Uniqueness then makes the two mates `a ⟹ b` and `b ⟹ a` mutually inverse.

--------
同一个1-胞元 `f` 的两个右伴随通过一个可逆的2-胞元相关联。比较2-胞元是*恒等的伴随*：给定 `f` 的右伴随 `a` 和 `b`，复合

     matecell : a  ⟹  Id_x ∘ a  ⟹  (b ∘ f) ∘ a  ⟹  b ∘ (f ∘ a)  ⟹  b ∘ Id_y  ⟹  b

在 `a` 的右侧对 `b` 的单位 `η_b` 进行鞭笞，重新结合，然后在 `b` 的左侧对 `a` 的余单位 `ε_a` 进行鞭笞。论证的核心是一个表征：`matecell` 是与单位兼容的*唯一*2-胞元 `γ : a ⟹ b`，以及 `(γ ⊳ f) ∘ η_a ≈ η_b`（`mate_charac`）和事实 `matecell` 本身与单位兼容（`mate_unit_compat`）。唯一性然后使得两个伴随 `a ⟹ b` 和 `b ⟹ a` 相互为逆。
*)

Section AdjointUniqueness.

Context {B : Bicategory}.
Context {x y : bi0cell}.
Context {f : bicat x y}.

(*
Readable accessors for the unit, counit and right triangle of an adjunction
   supplied as an explicit hypothesis.

--------
为伴随提供的单位、余单位和右三角形的可读访问器，作为一个显式假设。
*)
Definition uη {a : bicat y x} (A : BicatAdjunction f a)
  : bi1id ~{bicat x x}~> (a ∘∘∘ f) := @adj_unit B x y f a A.
Definition uε {a : bicat y x} (A : BicatAdjunction f a)
  : (f ∘∘∘ a) ~{bicat y y}~> bi1id := @adj_counit B x y f a A.

(* The comparison 2-cell (mate of the identity) from `a` to `b`. / 从 `a` 到 `b` 的比较 2-胞（恒等的伴随）。 *)
Definition matecell {a b : bicat y x}
  (Aa : BicatAdjunction f a) (Ab : BicatAdjunction f b) : a ~{bicat y x}~> b :=
  to (hunit_right b)
    ∘∘ lwhisker b (uε Aa)
    ∘∘ to (hassoc b f a)
    ∘∘ rwhisker (uη Ab) a
    ∘∘ from (hunit_left a).

(* `matecell Aa Aa` is the right-triangle composite of `Aa`, hence `id`. / `matecell Aa Aa` 是 `Aa` 的直角三角复合，因此是 `id`。 *)
Lemma matecell_id {a : bicat y x} (Aa : BicatAdjunction f a) :
  matecell Aa Aa ≈ bi2id.
Proof.
  unfold matecell, lwhisker, rwhisker, uε, uη.
  exact (@adj_triangle_right B x y f a Aa).
Qed.

(* Characterisation: any unit-compatible 2-cell equals the mate. / 表征：任何单位兼容的二胞等于伴随。 *)
Lemma mate_charac {a b : bicat y x}
  (Aa : BicatAdjunction f a) (Ab : BicatAdjunction f b) (γ : a ~> b) :
  rwhisker γ f ∘∘ uη Aa ≈ uη Ab → γ ≈ matecell Aa Ab.
Proof.
  intro H.
  (* Split the whiskered unit of `b` using the unit-compatibility hypothesis. / 使用单位兼容性假设拆分 `b` 的带胡须单元。 *)
  assert (Hb : rwhisker (uη Ab) a
                 ≈ rwhisker (rwhisker γ f) a ∘∘ rwhisker (uη Aa) a).
  { rewrite <- rwhisker_comp. apply rwhisker_cong. now symmetry. }
  symmetry.
  unfold matecell.
  rewrite Hb.
  (* Slide γ leftwards across the associator (assoc_nat_top). / 将 γ 向左滑过结合子 (assoc_nat_top)。 *)
  transitivity
    (to (hunit_right b) ∘∘ (lwhisker b (uε Aa)
       ∘∘ ((to (hassoc b f a) ∘∘ rwhisker (rwhisker γ f) a)
             ∘∘ (rwhisker (uη Aa) a ∘∘ from (hunit_left a))))).
  { now rewrite !vcompose_assoc. }
  transitivity
    (to (hunit_right b) ∘∘ (lwhisker b (uε Aa)
       ∘∘ ((rwhisker γ (f ∘∘∘ a) ∘∘ to (hassoc a f a))
             ∘∘ (rwhisker (uη Aa) a ∘∘ from (hunit_left a))))).
  { now rewrite <- (assoc_nat_top γ f a). }
  (* Exchange the counit whisker of `b` past γ (whisker_exchange). / 交换 `b` 的辅单位须状物超过 γ (whisker_exchange)。 *)
  transitivity
    (to (hunit_right b) ∘∘ ((lwhisker b (uε Aa) ∘∘ rwhisker γ (f ∘∘∘ a))
       ∘∘ (to (hassoc a f a)
             ∘∘ (rwhisker (uη Aa) a ∘∘ from (hunit_left a))))).
  { now rewrite !vcompose_assoc. }
  transitivity
    (to (hunit_right b) ∘∘ ((rwhisker γ bi1id ∘∘ lwhisker a (uε Aa))
       ∘∘ (to (hassoc a f a)
             ∘∘ (rwhisker (uη Aa) a ∘∘ from (hunit_left a))))).
  { now rewrite (whisker_exchange γ (uε Aa)). }
  (* Slide γ out through the right unitor (hunit_right_nat). / 通过右单位器 (hunit_right_nat) 把 γ 滑出。 *)
  transitivity
    ((to (hunit_right b) ∘∘ rwhisker γ bi1id) ∘∘ (lwhisker a (uε Aa)
       ∘∘ (to (hassoc a f a)
             ∘∘ (rwhisker (uη Aa) a ∘∘ from (hunit_left a))))).
  { now rewrite !vcompose_assoc. }
  transitivity
    ((γ ∘∘ to (hunit_right a)) ∘∘ (lwhisker a (uε Aa)
       ∘∘ (to (hassoc a f a)
             ∘∘ (rwhisker (uη Aa) a ∘∘ from (hunit_left a))))).
  { now rewrite <- (hunit_right_nat γ). }
  (* The remaining factor is the right triangle of `Aa`, hence the identity. / 剩下的因素是 `Aa` 的直角三角形，因此得出该恒等式。 *)
  transitivity (γ ∘∘ matecell Aa Aa).
  { unfold matecell. now rewrite !vcompose_assoc. }
  rewrite matecell_id.
  now rewrite bi2id_right.
Qed.

(* ------------------------------------------------------------------ *)
(* Derived unit-coherence lemmas of the ambient bicategory. / 环境双范畴的派生单位一致性引理。            *)
(*                                                                     *)
(* These are the classical Kelly consequences of the triangle and / 这些是三角形的经典凯利后果和     *)
(* pentagon coherences; they do not mention the adjunction data. They / 五边形的相干性；他们没有提到伴随数据。他们  *)
(* are the reassociation identities needed once the mate is whiskered / 一旦伴侣被胡须化，是否还需要重新组合恒等  *)
(* on the right by `f`. Each is proven purely from the bicategory / 在右边由 `f` 提供。每一个都是完全从双范畴中证明的      *)
(* coherences and naturalities via the whisker calculus above. / 通过上述胡须演算实现连贯性和自然性。         *)
(* ------------------------------------------------------------------ *)

(* Right cancellation of a 2-cell that carries a chosen right inverse. / 携带所选右逆的二胞的右消去。 *)
Lemma vcancel_r {x' y' : bi0cell} {A0 A1 A2 : bicat x' y'}
  (p q : A1 ~> A2) (m : A0 ~> A1) (n : A1 ~> A0) :
  m ∘∘ n ≈ bi2id → p ∘∘ m ≈ q ∘∘ m → p ≈ q.
Proof.
  intros Hmn H.
  transitivity (p ∘∘ (m ∘∘ n)).
  { rewrite Hmn. now rewrite bi2id_right. }
  transitivity ((p ∘∘ m) ∘∘ n).
  { now rewrite vcompose_assoc. }
  rewrite H.
  transitivity (q ∘∘ (m ∘∘ n)).
  { now rewrite <- vcompose_assoc. }
  rewrite Hmn. now rewrite bi2id_right.
Qed.

(* Left cancellation of a 2-cell that carries a chosen left inverse. / 携带所选左逆元的 2-胞腔的左消去。 *)
Lemma vcancel_l {x' y' : bi0cell} {A0 A1 A2 : bicat x' y'}
  (p q : A0 ~> A1) (m : A1 ~> A2) (n : A2 ~> A1) :
  n ∘∘ m ≈ bi2id → m ∘∘ p ≈ m ∘∘ q → p ≈ q.
Proof.
  intros Hnm H.
  transitivity ((n ∘∘ m) ∘∘ p).
  { rewrite Hnm. now rewrite bi2id_left. }
  transitivity (n ∘∘ (m ∘∘ p)).
  { now rewrite <- vcompose_assoc. }
  rewrite H.
  transitivity ((n ∘∘ m) ∘∘ q).
  { now rewrite vcompose_assoc. }
  rewrite Hnm. now rewrite bi2id_left.
Qed.

(* Left-whiskering by the unit 1-cell is faithful: it reflects `≈`. / 由单位 1-单元进行的左搅拌是忠实的：它反映 `≈`。 *)
Lemma lwhisker_unit_faithful {x' y' : bi0cell} {A A' : bicat x' y'}
  (u v : A ~> A') :
  lwhisker bi1id u ≈ lwhisker bi1id v → u ≈ v.
Proof.
  intro H.
  apply (vcancel_r u v (to (hunit_left A)) (from (hunit_left A))).
  - exact (vto_vfrom (hunit_left A)).
  - rewrite (hunit_left_nat u), H. now rewrite <- (hunit_left_nat v).
Qed.

(* Right-whiskering by the unit 1-cell is faithful: it reflects `≈`. / 由单位 1-胞格进行的右甩须是忠实的：它反映了 `≈`。 *)
Lemma rwhisker_unit_faithful {x' y' : bi0cell} {A A' : bicat x' y'}
  (u v : A ~> A') :
  rwhisker u bi1id ≈ rwhisker v bi1id → u ≈ v.
Proof.
  intro H.
  apply (vcancel_r u v (to (hunit_right A)) (from (hunit_right A))).
  - exact (vto_vfrom (hunit_right A)).
  - rewrite (hunit_right_nat u), H. now rewrite <- (hunit_right_nat v).
Qed.

(*
The triangle and pentagon coherences restated in whisker notation (the
   fields are phrased through `hcomp2`, to which the whiskers unfold), so that
   `rewrite` matches the whisker terms occurring below.

--------
用胡须符号重新表述的三角形和五边形相干性（这些字段是通过 `hcomp2` 表示的，胡须符号由此展开），这样 `rewrite` 就与下面出现的胡须项相匹配。
*)
Lemma tri_lr {x' y' z' : bi0cell} (g : bicat y' z') (k : bicat x' y') :
  rwhisker (to (hunit_right g)) k
    ≈ lwhisker g (to (hunit_left k)) ∘∘ to (hassoc g bi1id k).
Proof. exact (hcoherence_triangle g k). Qed.

Lemma pent_lr {v' w' x' y' z' : bi0cell}
  (k : bicat y' z') (h : bicat x' y') (g : bicat w' x') (l : bicat v' w') :
  lwhisker k (to (hassoc h g l))
    ∘∘ to (hassoc k (h ∘∘∘ g) l)
    ∘∘ rwhisker (to (hassoc k h g)) l
    ≈ to (hassoc k h (g ∘∘∘ l)) ∘∘ to (hassoc (k ∘∘∘ h) g l).
Proof. exact (hcoherence_pentagon k h g l). Qed.

(*
Left-unit coherence (Kelly): the left unitor whiskered on the right by `k`
   agrees with the left unitor of the composite, across the associator.

--------
左单位一致性（Kelly）：左单位算子在右侧由 `k` 齐次化，与复合体的左单位算子沿结合子一致。
*)
Lemma left_unit_coherence {x' y' z' : bi0cell}
  (g : bicat y' z') (k : bicat x' y') :
  rwhisker (to (hunit_left g)) k
    ≈ to (hunit_left (g ∘∘∘ k)) ∘∘ to (hassoc bi1id g k).
Proof.
  apply lwhisker_unit_faithful.
  apply (vcancel_r _ _ (to (hassoc bi1id (bi1id ∘∘∘ g) k))
                       (from (hassoc bi1id (bi1id ∘∘∘ g) k))).
  { exact (vto_vfrom _). }
  apply (vcancel_r _ _ (rwhisker (to (hassoc bi1id bi1id g)) k)
                       (rwhisker (from (hassoc bi1id bi1id g)) k)).
  { rewrite <- rwhisker_comp.
    rewrite (rwhisker_cong _ _ k (vto_vfrom (hassoc bi1id bi1id g))).
    now rewrite rwhisker_id. }
  rewrite (assoc_nat_mid bi1id (to (hunit_left g)) k).
  rewrite <- vcompose_assoc.
  rewrite <- rwhisker_comp.
  rewrite <- (rwhisker_cong _ _ k (tri_lr bi1id g)).
  rewrite <- (assoc_nat_top (to (hunit_right bi1id)) g k).
  rewrite (tri_lr bi1id (g ∘∘∘ k)).
  rewrite <- vcompose_assoc.
  rewrite <- (pent_lr bi1id bi1id g k).
  rewrite !vcompose_assoc.
  now rewrite <- lwhisker_comp.
Qed.

(* Right-unit coherence (Kelly), the mirror statement for the right unitor. / 右单位相干性（Kelly），右单位元的镜像陈述。 *)
Lemma right_unit_coherence {x' y' z' : bi0cell}
  (g : bicat y' z') (k : bicat x' y') :
  lwhisker g (to (hunit_right k)) ∘∘ to (hassoc g k bi1id)
    ≈ to (hunit_right (g ∘∘∘ k)).
Proof.
  apply rwhisker_unit_faithful.
  apply (vcancel_l _ _ (to (hassoc g k bi1id)) (from (hassoc g k bi1id))).
  { exact (vfrom_vto (hassoc g k bi1id)). }
  rewrite rwhisker_comp.
  rewrite vcompose_assoc.
  rewrite <- (assoc_nat_mid g (to (hunit_right k)) bi1id).
  rewrite (lwhisker_cong g _ _ (tri_lr k bi1id)).
  rewrite lwhisker_comp.
  transitivity (lwhisker g (lwhisker k (to (hunit_left bi1id)))
    ∘∘ ((lwhisker g (to (hassoc k bi1id bi1id))
          ∘∘ to (hassoc g (k ∘∘∘ bi1id) bi1id))
          ∘∘ rwhisker (to (hassoc g k bi1id)) bi1id)).
  { now rewrite <- !vcompose_assoc. }
  rewrite (pent_lr g k bi1id bi1id).
  rewrite vcompose_assoc.
  rewrite (assoc_nat_bot g k (to (hunit_left bi1id))).
  rewrite <- vcompose_assoc.
  now rewrite <- (tri_lr (g ∘∘∘ k) bi1id).
Qed.

(* Unit-object coherence (Kelly): the two unitors of the unit 1-cell agree. / 单位-对象一致性（Kelly）：单位1元的两个单位元相符。 *)
Lemma unit_left_right_id {x' : bi0cell} :
  to (hunit_left (bi1id (x:=x'))) ≈ to (hunit_right (bi1id (x:=x'))).
Proof.
  apply rwhisker_unit_faithful.
  assert (Hδ : to (hunit_left (bi1id ∘∘∘ bi1id))
                 ≈ lwhisker bi1id (to (hunit_left (bi1id (x:=x'))))).
  { apply (vcancel_l _ _ (to (hunit_left bi1id)) (from (hunit_left bi1id))).
    - exact (vfrom_vto (hunit_left bi1id)).
    - exact (hunit_left_nat (to (hunit_left bi1id))). }
  rewrite (left_unit_coherence bi1id bi1id).
  rewrite Hδ.
  symmetry.
  apply tri_lr.
Qed.

(*
The `from`-direction of left-unit coherence, obtained by inverting the `to`
   form: right-whiskering the inverse left unitor factors as the inverse of the
   composite unitor after the inverse associator.

--------
通过取 `to` 形式的逆运算得到的左单元相干的 `from` 方向：将逆左单元子进行右鞭操作，可分解为逆结合子后的复合单元子的逆。
*)
Lemma left_unit_coherence_from {x' y' z' : bi0cell}
  (g : bicat y' z') (k : bicat x' y') :
  rwhisker (from (hunit_left g)) k
    ≈ from (hassoc bi1id g k) ∘∘ from (hunit_left (g ∘∘∘ k)).
Proof.
  apply (vcancel_r _ _ (rwhisker (to (hunit_left g)) k)
                       (rwhisker (from (hunit_left g)) k)).
  { rewrite <- rwhisker_comp.
    rewrite (rwhisker_cong _ _ k (vto_vfrom (hunit_left g))).
    now rewrite rwhisker_id. }
  rewrite <- rwhisker_comp.
  rewrite (rwhisker_cong _ _ k (vfrom_vto (hunit_left g))).
  rewrite rwhisker_id.
  rewrite (left_unit_coherence g k).
  rewrite <- !vcompose_assoc.
  rewrite (vcompose_assoc (from (hunit_left (g ∘∘∘ k)))
                          (to (hunit_left (g ∘∘∘ k)))
                          (to (hassoc bi1id g k))).
  rewrite vfrom_vto, bi2id_left.
  now rewrite vfrom_vto.
Qed.

(* Cancel a `to`/`from` pair sitting at the head of a right-nested composite. / 取消位于右嵌套复合开头的 `to`/`from` 对。 *)
Lemma vcancel_tf {x' y' : bi0cell} {A0 A1 C : bicat x' y'}
  (i : A0 ≅[bicat x' y'] A1) (r : C ~> A1) :
  to i ∘∘ (from i ∘∘ r) ≈ r.
Proof. rewrite vcompose_assoc, vto_vfrom. now rewrite bi2id_left. Qed.

(*
The associator naturality laws, solved for the doubly-whiskered cell; these
   put each right-whiskered factor of the expanded mate into a normal form whose
   flanking associators telescope against their neighbours.

--------
结合器自然律，对于双搅细胞求解；这些将扩展伴随的每个右搅因子置于一种标准形式，其两侧的结合器与邻居进行望远镜式抵消。
*)
Lemma assoc_top_solve {w x' y' z' : bi0cell} {h h' : bicat y' z'}
  (θ : h ~> h') (g : bicat x' y') (l : bicat w x') :
  rwhisker (rwhisker θ g) l
    ≈ from (hassoc h' g l) ∘∘ (rwhisker θ (g ∘∘∘ l) ∘∘ to (hassoc h g l)).
Proof.
  apply (vcancel_l _ _ (to (hassoc h' g l)) (from (hassoc h' g l))).
  - exact (vfrom_vto _).
  - rewrite (vcancel_tf (hassoc h' g l)).
    symmetry. exact (assoc_nat_top θ g l).
Qed.

Lemma assoc_mid_solve {w x' y' z' : bi0cell} (h : bicat y' z')
  {g g' : bicat x' y'} (γ : g ~> g') (l : bicat w x') :
  rwhisker (lwhisker h γ) l
    ≈ from (hassoc h g' l) ∘∘ (lwhisker h (rwhisker γ l) ∘∘ to (hassoc h g l)).
Proof.
  apply (vcancel_l _ _ (to (hassoc h g' l)) (from (hassoc h g' l))).
  - exact (vfrom_vto _).
  - rewrite (vcancel_tf (hassoc h g' l)).
    symmetry. exact (assoc_nat_mid h γ l).
Qed.

(* The pentagon, solved for the right-whiskered associator. / 五边形，已为右须关联子求解。 *)
Lemma pent_solve {v' w' x' y' z' : bi0cell}
  (k : bicat y' z') (h : bicat x' y') (g : bicat w' x') (l : bicat v' w') :
  rwhisker (to (hassoc k h g)) l
    ≈ from (hassoc k (h ∘∘∘ g) l)
        ∘∘ (lwhisker k (from (hassoc h g l))
             ∘∘ (to (hassoc k h (g ∘∘∘ l)) ∘∘ to (hassoc (k ∘∘∘ h) g l))).
Proof.
  apply (vcancel_l _ _ (lwhisker k (to (hassoc h g l)) ∘∘ to (hassoc k (h ∘∘∘ g) l))
                       (from (hassoc k (h ∘∘∘ g) l) ∘∘ lwhisker k (from (hassoc h g l)))).
  - rewrite <- !vcompose_assoc.
    rewrite (vcompose_assoc (lwhisker k (from (hassoc h g l)))
                            (lwhisker k (to (hassoc h g l)))
                            (to (hassoc k (h ∘∘∘ g) l))).
    rewrite <- lwhisker_comp.
    rewrite (lwhisker_cong k _ _ (vfrom_vto (hassoc h g l))).
    rewrite lwhisker_id, bi2id_left.
    now rewrite vfrom_vto.
  - rewrite (pent_lr k h g l).
    rewrite <- !vcompose_assoc.
    rewrite (vcancel_tf (hassoc k (h ∘∘∘ g) l)).
    rewrite (vcompose_assoc (lwhisker k (to (hassoc h g l)))
                            (lwhisker k (from (hassoc h g l))) _).
    rewrite <- lwhisker_comp.
    rewrite (lwhisker_cong k _ _ (vto_vfrom (hassoc h g l))).
    rewrite lwhisker_id, bi2id_left.
    reflexivity.
Qed.

(*
The mate is itself unit-compatible: whiskering it on the right of `f` and
   composing with the unit of `a` recovers the unit of `b`.

--------
该配件本身与单位兼容：将其在 `f` 的右侧进行搅拌，并与 `a` 的单位组合，可恢复 `b` 的单位。
*)
Lemma mate_unit_compat {a b : bicat y x}
  (Aa : BicatAdjunction f a) (Ab : BicatAdjunction f b) :
  rwhisker (matecell Aa Ab) f ∘∘ uη Aa ≈ uη Ab.
Proof.
  (*
Straighten `η_b ⊳ I` against the inverse left unitor of the unit: the
     right unitor naturality of `η_b` together with `λ_I = ρ_I` turns it into
     `ρ_{b·f}⁻¹ ∘ η_b`.

--------
将 `η_b ⊳ I` 对齐到单位的逆左幺元：`η_b` 的右幺元自然性与 `λ_I = ρ_I` 一起将其转换为 `ρ_{b·f}⁻¹ ∘ η_b`。
*)
  assert (Eη : rwhisker (uη Ab) bi1id ∘∘ from (hunit_left bi1id)
               ≈ from (hunit_right (b ∘∘∘ f)) ∘∘ uη Ab).
  { apply (vcancel_l _ _ (to (hunit_right (b ∘∘∘ f))) (from (hunit_right (b ∘∘∘ f)))).
    - exact (vfrom_vto _).
    - rewrite (vcancel_tf (hunit_right (b ∘∘∘ f))).
      rewrite vcompose_assoc.
      rewrite <- (hunit_right_nat (uη Ab)).
      rewrite <- vcompose_assoc.
      rewrite <- (unit_left_right_id (x':=x)).
      rewrite vto_vfrom.
      now rewrite bi2id_right. }
  (*
The left triangle of `Aa`: the `ε_a`/`η_a` zig-zag on `f`, conjugated by
     the left unitor, straightens to the right unitor `ρ_f`.

--------
`Aa` 的左三角形：在 `f` 上的 `ε_a`/`η_a` 锯齿形，通过左单位元结合后，变为右单位元 `ρ_f`。
*)
  assert (Htri : ((to (hunit_left f) ∘∘ rwhisker (uε Aa) f) ∘∘ from (hassoc f a f))
                   ∘∘ lwhisker f (uη Aa)
                 ≈ to (hunit_right f)).
  { apply (vcancel_r _ _ (from (hunit_right f)) (to (hunit_right f))).
    - exact (vfrom_vto (hunit_right f)).
    - rewrite vto_vfrom. exact (@adj_triangle_left B x y f a Aa). }
  (*
The trailing factors `(η_b ⊳ a) ⊳ f`, `(λ_a⁻¹ ⊳ f)` and `η_a` straighten,
     via the interchange law and `Eη`, into a left whisker of `η_a` by `b`.

--------
尾随因子 `(η_b ⊳ a) ⊳ f`、`(λ_a⁻¹ ⊳ f)` 和 `η_a` 通过交换律和 `Eη`，沿 `b` 方向伸展开形成 `η_a` 的左侧小枝。
*)
  assert (Etail :
    to (hassoc b f (a ∘∘∘ f))
      ∘∘ (rwhisker (uη Ab) (a ∘∘∘ f) ∘∘ (from (hunit_left (a ∘∘∘ f)) ∘∘ uη Aa))
    ≈ lwhisker b (lwhisker f (uη Aa))
      ∘∘ (to (hassoc b f bi1id) ∘∘ (from (hunit_right (b ∘∘∘ f)) ∘∘ uη Ab))).
  { rewrite (hunit_left_from_natural (uη Aa)).
    rewrite (vcompose_assoc (rwhisker (uη Ab) (a ∘∘∘ f))
                            (lwhisker bi1id (uη Aa)) (from (hunit_left bi1id))).
    rewrite <- (whisker_exchange (uη Ab) (uη Aa)).
    rewrite <- (vcompose_assoc (lwhisker (b ∘∘∘ f) (uη Aa))
                               (rwhisker (uη Ab) bi1id) (from (hunit_left bi1id))).
    rewrite Eη.
    rewrite (vcompose_assoc (to (hassoc b f (a ∘∘∘ f)))
                            (lwhisker (b ∘∘∘ f) (uη Aa))
                            (from (hunit_right (b ∘∘∘ f)) ∘∘ uη Ab)).
    rewrite <- (assoc_nat_bot b f (uη Aa)).
    now rewrite <- vcompose_assoc. }
  (*
Main computation: expand the right-whiskered mate into associator-solved
     factors, telescope the four adjacent associator pairs, then apply the tail
     straightening, merge the `b`-whiskers, and collapse via the left triangle
     and right-unit coherence.

--------
主要计算：将右须配的伴侣展开为结合子求解的因子，望远镜化四个相邻的结合子对，然后应用尾部拉直，合并 `b` 须，最后通过左三角和右单元一致性进行合并。
*)
  unfold matecell.
  rewrite !rwhisker_comp.
  rewrite (tri_lr b f).
  rewrite (assoc_mid_solve b (uε Aa) f).
  rewrite (pent_solve b f a f).
  rewrite (assoc_top_solve (uη Ab) a f).
  rewrite (left_unit_coherence_from a f).
  rewrite <- !vcompose_assoc.
  rewrite (vcancel_tf (hassoc b bi1id f)).
  rewrite (vcancel_tf (hassoc b (f ∘∘∘ a) f)).
  rewrite (vcancel_tf (hassoc (b ∘∘∘ f) a f)).
  rewrite (vcancel_tf (hassoc bi1id a f)).
  rewrite Etail.
  rewrite !vcompose_assoc.
  rewrite <- !lwhisker_comp.
  rewrite (lwhisker_cong b _ _ Htri).
  rewrite (right_unit_coherence b f).
  rewrite vto_vfrom.
  now rewrite bi2id_left.
Qed.

(*
Uniqueness of adjoints: two right adjoints of `f` are related by an
   invertible 2-cell, the mate of the identity.

--------
伴随的唯一性：`f` 的两个右伴随通过一个可逆的 2-胞连接相关联，该 2-胞是恒等映射的伴随。
*)
Theorem adjoint_unique {a b : bicat y x}
  (Aa : BicatAdjunction f a) (Ab : BicatAdjunction f b) :
  a ≅[bicat y x] b.
Proof.
  refine (@Build_Isomorphism (bicat y x) a b
            (matecell Aa Ab) (matecell Ab Aa) _ _).
  - (* matecell Aa Ab ∘∘ matecell Ab Aa ≈ id[b] / 配子细胞 Aa Ab ∘∘ 配子细胞 Ab Aa ≈ id[b] *)
    transitivity (matecell Ab Ab).
    + refine (mate_charac Ab Ab (matecell Aa Ab ∘∘ matecell Ab Aa) _).
      rewrite rwhisker_comp.
      rewrite <- vcompose_assoc.
      rewrite (mate_unit_compat Ab Aa).
      now rewrite (mate_unit_compat Aa Ab).
    + exact (matecell_id Ab).
  - (* matecell Ab Aa ∘∘ matecell Aa Ab ≈ id[a] / matecell Ab Aa ∘∘ matecell Aa Ab ≈ id[a] / matecell Ab Aa ∘∘ matecell Aa Ab ≈ id[a] / matecell Ab Aa ∘∘ matecell Aa Ab ≈ id[a] *)
    transitivity (matecell Aa Aa).
    + refine (mate_charac Aa Aa (matecell Ab Aa ∘∘ matecell Aa Ab) _).
      rewrite rwhisker_comp.
      rewrite <- vcompose_assoc.
      rewrite (mate_unit_compat Aa Ab).
      now rewrite (mate_unit_compat Ab Aa).
    + exact (matecell_id Aa).
Qed.

End AdjointUniqueness.

Arguments matecell {B x y f a b} Aa Ab.
Arguments adjoint_unique {B x y f a b} Aa Ab.
