Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Theory.Bicategory.
Require Import Category.Theory.Bicategory.Pseudofunctor.
Require Import Category.Theory.Bicategory.Lax.

Generalizable All Variables.

(** Modifications between lax transformations, and the category they form. / 宽松变换之间的修改，以及它们形成的范畴。 *)

(*
nLab: https://ncatlab.org/nlab/show/modification
   Reference: Johnson–Yau, “2-Dimensional Categories”, Definition 4.4.1.

   Given two lax transformations σ, τ : F ⟹ G between pseudofunctors
   F, G : B ⟶ B', a *modification* Γ : σ ⇛ τ consists of a component 2-cell

     Γ_x : σ_x ⟹ τ_x        in the hom-category  bicat B' (F x) (G x)

   for each 0-cell x, subject to one coherence axiom relating the components to
   the naturators of σ and τ.  With the lax naturator orientation of
   `Theory/Bicategory/Lax.v`,

     lt1 σ f : G f ∘∘∘ σ_x  ⟹  σ_y ∘∘∘ F f,

   the modification axiom is the commuting square (in the hom-category
   bicat B' (F x) (G y)) with the two naturators on the sides and the
   whiskerings of Γ on the other two:

     lt1 τ f ∘∘ (G f ⊲ Γ_x)  ≈  (Γ_y ⊳ F f) ∘∘ lt1 σ f,

   where the left whiskering  G f ⊲ Γ_x  is `hcomp2 (bi2id (a:=pf1[G] f)) (Γ x)`
   (identity on pf1[G] f, the modification component on the source side) and the
   right whiskering  Γ_y ⊳ F f  is `hcomp2 (Γ y) (bi2id (a:=pf1[F] f))`
   (the component on the target side, identity on pf1[F] f).  Both composites
   are 2-cells  G f ∘∘∘ σ_x ⟹ τ_y ∘∘∘ F f, so the equation is well typed.

   Modifications are the 2-cells of the (strict) hom-2-category whose 0-cells
   are pseudofunctors, 1-cells are lax transformations, and whose vertical
   composition of 2-cells is that of the target hom-categories.  This file
   provides the identity and vertical composite modifications, the hom-setoid
   in which two modifications agree iff their components agree at every 0-cell,
   and packages these into the category [LaxTransformation_Category F G] of lax
   transformations F ⟹ G with modifications between them.

   Notation: `∘∘` is vertical 2-cell composition (`vcompose`), `∘∘∘` horizontal
   1-cell composition (`hcompose`), `hcomp2` the Godement horizontal composite;
   `pf1[ ]`, `lt0`, `lt1` are the pseudofunctor hom-functor and the
   lax-transformation component/naturator accessors of the imported files.

--------
nLab：https://ncatlab.org/nlab/show/modification
 参考文献：Johnson–Yau，“二维范畴”，定义 4.4.1。

给定赝函子之间的两个宽松变换 σ, τ : F ⟹ G
 F, G : B ⟶ B', a *修改* Γ : σ ⇛ τ 由 2 单元组成

Γ_x : σ_x ⟹ τ_x 在 hom 范畴 bicat B' (F x) (G x)

对于每个 0 单元格 x，服从一个与分量相关的相干公理
 σ 和 τ 的自然子。 随着宽松的自然取向
 `Theory/Bicategory/Lax.v`，

lt1 σ f : G f ∘∘∘ σ_x ⟹ σ_y ∘∘∘ F f,

修改公理是通勤平方（在 hom 范畴中
 bicat B' (F x) (G y))，两侧有两个自然器，
 另外两个上的 Γ 的晶须：

lt1 τ f ∘∘ (G f ⊲ Γ_x) ≈ (Γ_y ⊳ F f) ∘∘ lt1 σ f,

其中左侧晶须 G f ⊲ Γ_x 为 `hcomp2 (bi2id (a:=pf1XPROTECT0X f)) (Γ x)`
 （pf1[G] f 上的标识，源端的修改组件）和
 右晶须 Γ_y ⊳ F f 是 `hcomp2 (Γ y) (bi2id (a:=pf1XPROTECT2X f))`
 （目标端的组件，pf1[F] f 上的标识）。 两种复合材料
 是 2-cells G f ∘∘∘ σ_x ⟹ τ_y ∘∘∘ F f，所以方程的类型很好。

修饰是（严格）hom-2 范畴的 2 单元，其 0 单元
 是伪函子，1-cell 是宽松变换，其垂直
 2-cell 的组成是目标 hom-categories 的组成。 这个文件
 提供恒等和垂直复合修改， hom-setoid
 其中两个修改一致，当且仅当它们的组件在每个 0 单元格处一致，
 并将它们打包到 lax 的 [LaxTransformation_Category F G] 范畴中
 变换 F ⟹ G 以及它们之间的修改。

符号：`∘∘` 为垂直 2 单元组合 (`vcompose`)，`∘∘∘` 为水平
 1-细胞组合（`hcompose`）、`hcomp2` Godement水平组合；
 `pf1XPROTECT5X`、`lt0`、`lt1` 是伪函子 hom-函子，
 导入文件的 lax-transformation 组件/naturator 访问器。
*)

(*
The modification class, at full strength.  Its datum is the component
   2-cell family [md]; its single law is the modification axiom [md_natural],
   phrased through the Godement composite [hcomp2] and the lax naturators
   [lt1] of the two lax transformations.

--------
修改类，在充分强度下。它的数据是组件2-胞家族[md]；它的单一定律是修改公理[md_natural]，通过Godement复合[hcomp2]和两个松弛变换的松弛自然变换[lt1]来表达。
*)
Class Modification {B B' : Bicategory} {F G : Pseudofunctor B B'}
      (σ τ : LaxTransformation F G) := {
  (* component 2-cells Γ_x : σ_x ⟹ τ_x / 分量 2-胞 Γ_x : σ_x ⟹ τ_x *)
  md (x : @bi0cell B) :
    lt0 σ x ~{ @bicat B' (pf0 F x) (pf0 G x) }~> lt0 τ x;

  (*
the modification axiom: the components commute with the naturators of σ
     and τ, whiskered by pf1[G] f on the source side and pf1[F] f on the
     target side.

--------
修改公理：各分量与 σ 和 τ 的自然化算子交换，在源端由 pf1[G] f 菱形化，在目标端由 pf1[F] f 菱形化。
*)
  md_natural {x y : @bi0cell B} (f : @bicat B x y) :
    lt1 τ f ∘∘ hcomp2 (bi2id (a:=pf1[G] f)) (md x)
      ≈ hcomp2 (md y) (bi2id (a:=pf1[F] f)) ∘∘ lt1 σ f
}.

Arguments md {B B' F G σ τ} _ x.
Arguments md_natural {B B' F G σ τ} _ {x y} f.

(** The identity modification. / 恒等修改。 *)

(*
The identity modification's axiom: with every component the identity 2-cell,
   the two whiskerings reduce (by `hcomp2_id`) to identity 2-cells, and the
   equation collapses to `lt1 σ f ≈ lt1 σ f` by the unit laws of vertical
   composition.  This uses no coincidence of unitors in the target bicategory,
   so it is a genuine (non-vacuous) witness on an *arbitrary* lax
   transformation σ.

--------
恒等修改的公理：对于每个分量的恒等 2-胞，两个须状操作（whiskerings）通过 `hcomp2_id` 简化为恒等 2-胞，并且该方程通过垂直组合的单位律收缩为 `lt1 σ f ≈ lt1 σ f`。这不依赖于目标双范畴中单位子的任何巧合，因此它在*任意*松变换 σ 上是一个真实的（非空洞的）证据。
*)
Lemma id_modification_natural {B B' : Bicategory} {F G : Pseudofunctor B B'}
      (σ : LaxTransformation F G) {x y : @bi0cell B} (f : @bicat B x y) :
  lt1 σ f ∘∘ hcomp2 (bi2id (a:=pf1[G] f)) (bi2id (a:=lt0 σ x))
    ≈ hcomp2 (bi2id (a:=lt0 σ y)) (bi2id (a:=pf1[F] f)) ∘∘ lt1 σ f.
Proof.
  rewrite !hcomp2_id.
  rewrite bi2id_left, bi2id_right.
  reflexivity.
Qed.

Definition id_modification {B B' : Bicategory} {F G : Pseudofunctor B B'}
           (σ : LaxTransformation F G) : Modification σ σ :=
  {| md         := fun x => bi2id
   ; md_natural := fun x y f => id_modification_natural σ f |}.

(** The vertical composite of modifications. / 修改的垂直组合。 *)

(*
Composite modification axiom: componentwise vertical composition.  The two
   whiskerings split over vertical composition by the interchange specialisations
   `hcomp2_comp_right`/`hcomp2_comp_left`, and the resulting pasting is closed by
   the two given modification axioms and associativity of vertical composition.

--------
复合修改公理：按分量的垂直组合。通过交换特化 `hcomp2_comp_right`/`hcomp2_comp_left`，两个刷状操作在垂直组合上被分开，并且所得的粘接由两个给定的修改公理和垂直组合的结合性闭合。
*)
Lemma compose_modification_natural {B B' : Bicategory} {F G : Pseudofunctor B B'}
      {σ τ υ : LaxTransformation F G}
      (n : Modification τ υ) (m : Modification σ τ)
      {x y : @bi0cell B} (f : @bicat B x y) :
  lt1 υ f ∘∘ hcomp2 (bi2id (a:=pf1[G] f)) (md n x ∘∘ md m x)
    ≈ hcomp2 (md n y ∘∘ md m y) (bi2id (a:=pf1[F] f)) ∘∘ lt1 σ f.
Proof.
  rewrite hcomp2_comp_right.
  rewrite hcomp2_comp_left.
  rewrite vcompose_assoc.
  rewrite (md_natural n f).
  rewrite <- !vcompose_assoc.
  rewrite (md_natural m f).
  reflexivity.
Qed.

Definition compose_modification {B B' : Bicategory} {F G : Pseudofunctor B B'}
           {σ τ υ : LaxTransformation F G}
           (n : Modification τ υ) (m : Modification σ τ) : Modification σ υ :=
  {| md         := fun x => md n x ∘∘ md m x
   ; md_natural := fun x y f => compose_modification_natural n m f |}.

(*
Reduction lemmas for the components of the identity and composite
   modifications, in `≈` form (each holds by conversion).  They keep the
   category-law proofs below free of unfolding.

--------
恒等和复合修改的各组成部分的归约引理，以 `≈` 形式（每个都通过转换成立）。它们保持下面的范畴律证明不展开。
*)
Lemma md_id_modification {B B' : Bicategory} {F G : Pseudofunctor B B'}
      (σ : LaxTransformation F G) (x : @bi0cell B) :
  md (id_modification σ) x ≈ bi2id.
Proof. reflexivity. Qed.

Lemma md_compose_modification {B B' : Bicategory} {F G : Pseudofunctor B B'}
      {σ τ υ : LaxTransformation F G}
      (n : Modification τ υ) (m : Modification σ τ) (x : @bi0cell B) :
  md (compose_modification n m) x ≈ md n x ∘∘ md m x.
Proof. reflexivity. Qed.

(** The hom-setoid of modifications and the category of lax transformations. / 修正的同类集和松弛变换的范畴。 *)

#[local] Obligation Tactic := idtac.

(*
Two modifications are equal when their components agree at every 0-cell.
   This is an equivalence relation because `≈` is one at each component.

--------
当两个修改在每个 0-单元的组成部分都相同时，它们是相等的。 这是一个等价关系，因为 `≈` 在每个组成部分上都是相同的。
*)
Program Definition Modification_Setoid {B B' : Bicategory}
        {F G : Pseudofunctor B B'} (σ τ : LaxTransformation F G) :
  Setoid (Modification σ τ) := {|
  equiv := fun m n => ∀ x, md m x ≈ md n x
|}.
Next Obligation.
  constructor.
  - intros m x; reflexivity.
  - intros m n H x; symmetry; apply H.
  - intros m n p H1 H2 x; now rewrite H1, H2.
Qed.

(*
The category of lax transformations F ⟹ G and modifications between them:
   objects are lax transformations, homs the modifications, identity and
   composition as above, and the category laws hold componentwise from the
   corresponding vertical-composition laws in the target hom-categories.  Built
   with [Build_Category'], which derives the dual associativity field.

--------
松弛变换 F ⟹ G 及其之间的修正的范畴：
   对象是松弛变换，箭头是修正，恒等与组合如上，范畴定律按分量成立，从目标 Hom-范畴中的相应垂直组合定律得出。使用 [Build_Category'] 构建，它推导了对偶的结合性域。
*)
Definition LaxTransformation_Category {B B' : Bicategory}
           (F G : Pseudofunctor B B') : Category.
Proof.
  unshelve refine (Build_Category'
    (fun σ τ : LaxTransformation F G => Modification σ τ)  (* hom *)
    (fun σ => id_modification σ)                          (* id *)
    (fun σ τ υ n m => compose_modification n m)).         (* compose / 撰写 *)
  - (* homset / 同域 *)
    exact (fun σ τ => Modification_Setoid σ τ).
  - (* compose respects component-wise equivalence / 组成尊重逐组件等价 *)
    intros σ τ υ n n' Hn m m' Hm x.
    cbv beta.
    rewrite !md_compose_modification.
    rewrite (Hn x), (Hm x).
    reflexivity.
  - (* left identity / 左单位元 *)
    intros σ τ f x.
    cbv beta.
    rewrite md_compose_modification, md_id_modification.
    apply bi2id_left.
  - (* right identity / 正确恒等 *)
    intros σ τ f x.
    cbv beta.
    rewrite md_compose_modification, md_id_modification.
    apply bi2id_right.
  - (* associativity / 结合性 *)
    intros σ0 σ1 σ2 σ3 p q r x.
    cbv beta.
    rewrite !md_compose_modification.
    apply vcompose_assoc.
Defined.

(** Inhabitation witnesses. / 居住见证者。 *)

(*
Concrete closed witnesses on the terminal bicategory's identity lax
   transformation (Theory/Bicategory/Lax.v): the identity modification and its
   self-composite.  These exhibit the class and its composition as inhabited
   with no appeal to any axiom.

--------
终端双范畴的恒等松变换上的具体封闭证人（Theory/Bicategory/Lax.v）：恒等改造及其自我复合。这些展示了该类及其复合是有实例的，无需诉诸任何公理。
*)
Definition Trivial_id_Modification :
  Modification Trivial_LaxTransformation Trivial_LaxTransformation :=
  id_modification Trivial_LaxTransformation.

Definition Trivial_compose_Modification :
  Modification Trivial_LaxTransformation Trivial_LaxTransformation :=
  compose_modification Trivial_id_Modification Trivial_id_Modification.
