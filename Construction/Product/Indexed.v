(* * * Set-indexed products of categories / * * 类的集合指数积 *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Two.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 §II.3 Exercise 3, printed p. 40 (PDF p. 50) — maclane:II.3:ex3
 nLab:      https://ncatlab.org/nlab/show/product+category

 For a set-indexed family of categories, the product category has as
 objects the choice functions of objects and as arrows the
 componentwise families of arrows, with projection functors satisfying
 the evident universal property: a family of functors into the
 components factors through the product, uniquely up to [Cat]'s
 hom-equivalence — the setoid rendering of the book's on-the-nose
 uniqueness.

 - [PiCat C]: objects [∀ i, C i], homs the dependent families of
 component homs, everything componentwise
 - [PiCat_Proj i]: the projections
 - [PiCat_Pair R]: the pairing ⟨R⟩ of a family [R i : D ⟶ C i],
 with [PiCat_Pair_Proj] the triangle [P i ◯ ⟨R⟩ ≈ R i] — its
 components are [iso_id], the composite being DEFINITIONALLY
 [R i] on both objects and arrows — [PiCat_ump_unique] the
 uniqueness half, and [PiCat_ump] the bundled ∃! (the same
 packaging as Structure/Limit/Product.v's [iprod_ump])

 Design:

 1. ONE CATEGORY INSTANCE FOR THE WHOLE FAMILY.  [C : I → Category]
 forces every member onto the same universe instance of
 [Category], so no per-member level juggling arises; the product's
 objects live at the maximum of [I]'s level and the members'
 object level — and [I]'s level also bounds the HOM universe,
 since a hom is itself an [I]-indexed family — exactly as the
 library's {o h p} polymorphism prescribes.  This is the “set-indexed” of the exercise made
 precise: [I] is a [Type], with no smallness apparatus needed.

 2. CONTRAST WITH Structure/Limit/Product.v.  That file's indexed
 products ([iprod] over Instance/Discrete.v's discrete diagrams)
 are products of OBJECTS INSIDE one category; this file's [PiCat]
 is a product OF CATEGORIES — the same distinction as between
 [Cartesian]'s binary product and Construction/Product.v's [∏].
 The two meet at [Cat]: [PiCat] exhibits the data that would make
 [Cat] complete under set-indexed products, the binary case of
 which is Instance/Cat/Cartesian.v's [Cat_Cartesian].

 3. THE BINARY CASE.  At [I := bool], [PiCat] specializes to a
 category equivalent to [C ∏ D] — a choice function on [bool]
 against a pair — recovering [Cat_Cartesian]'s fork; the
 identification is a NOTE, as in the exercise, rather than a
 formalized equivalence, since nothing downstream consumes it; the
 bridge is real but not free — [prod] is not a primitive record,
 so the pair side needs [fst]/[snd] destructs (the obstruction
 Construction/Product/Special.v documents), and the dependent
 identity family needs explicit match motives. 

 --------
 书籍：麦克·莱恩，《为工作中的数学家准备的范畴学》，第2版，§II.3 练习3，第40页（PDF第50页）—— maclane:II.3:ex3
 nLab：https://ncatlab.org/nlab/show/product+category

 对于一个集合索引的范畴族，积范畴的对象是对象的选择函数，箭头是按分量的箭头族，投影函子满足显然的泛性质：进入各分量的函子族通过积唯一地因式分解，唯一性至[Cat]的同态等价——这是该书中确切唯一性通过集合等价所呈现的方式。-  [PiCat C] ：对象  [∀ i, C i] ，同构为依赖族的  
 分量同构，一切按分量  
 -  [PiCat_Proj i] ：投影  
 -  [PiCat_Pair R] ：族  [R i : D ⟶ C i] 的配对 ⟨R⟩ ，  
 其中  [PiCat_Pair_Proj] 为三角形  [P i ◯ ⟨R⟩ ≈ R i]  — 它的  
 分量为  [iso_id] ，复合在对象和箭头上定义上为  
 [R i]  —  [PiCat_ump_unique] 为唯一性的一半，  
 [PiCat_ump] 为打包的 ∃!（与 Structure/Limit/Product.v 中的  
 [iprod_ump] 打包相同）

 设计：1. 整个家族的单一类别实例。[C : I → Category] 强制每个成员进入同一个 [Category] 的宇宙实例，因此不会出现按成员等级的操作；该产品的对象存在于 [I] 的等级和成员对象等级的最大值处 —— 并且 [I] 的等级也界定了 HOM 宇宙，因为一个 hom 本身就是一个 [I] 索引的家族 —— 完全符合库中 {o h p} 多态的规定。这就是练习中“集合索引”概念的精确定义：[I] 是一个 [Type]，不需要任何小范围装置。2. 与 Structure/Limit/Product.v 对比。该文件索引的产品（[iprod]，相对于 Instance/Discrete.v 的离散图）是一个类别内部对象的产品；而这个文件的 [PiCat] 是类别的乘积——与 [Cartesian] 的二元乘积和 Construction/Product.v 的 [∏] 之间的区别相同。两者在 [Cat] 交汇：[PiCat] 展示了在集合索引的乘积下使 [Cat] 完整的数据，其中二元情况是 Instance/Cat/Cartesian.v 的 [Cat_Cartesian]。3. 二元情况。在 [I := bool] 处，[PiCat] 专门化为与 [C ∏ D] 等价的一个范畴——在 [bool] 上针对一对的选择函数——恢复了 [Cat_Cartesian] 的分叉；这种识别是一个笔记（NOTE），如练习中所示，而不是形式化的等价，因为下游没有东西使用它；这个桥是真实的但不是自由的——[prod] 不是原始记录，因此对偶边需要 [fst] / [snd] 解构（Construction/Product/Special.v 中记录了障碍），依赖的同一性族需要显式匹配动机。
*)

(** ** The product category / ** 产品类别 *)

Program Definition PiCat {I : Type} (C : I → Category) : Category := {|
  obj := ∀ i : I, C i;
  hom := fun f g => ∀ i : I, f i ~> g i;
  homset := fun f g =>
    {| equiv := fun η θ => ∀ i : I, η i ≈ θ i |};
  id := fun f i => id;
  compose := fun f g h η θ i => η i ∘ θ i
|}.
Next Obligation.
  intros I C f g; constructor.
  - intros η i; reflexivity.
  - intros η θ Hηθ i; symmetry; apply Hηθ.
  - intros η θ ρ H1 H2 i.
    transitivity (θ i); [ apply H1 | apply H2 ].
Qed.
Next Obligation.
  intros I C f g h η η' Hη θ θ' Hθ i.
  exact (compose_respects _ _ (Hη i) _ _ (Hθ i)).
Qed.
Next Obligation.
  intros I C f g η i; exact (id_left (η i)).
Qed.
Next Obligation.
  intros I C f g η i; exact (id_right (η i)).
Qed.
Next Obligation.
  intros I C f g h k η θ ρ i; exact (comp_assoc (η i) (θ i) (ρ i)).
Qed.
Next Obligation.
  intros I C f g h k η θ ρ i; exact (comp_assoc_sym (η i) (θ i) (ρ i)).
Qed.

(** ** Projections / ** 投影 *)

Program Definition PiCat_Proj {I : Type} (C : I → Category) (i : I) :
  PiCat C ⟶ C i := {|
  fobj := fun f => f i;
  fmap := fun f g η => η i
|}.
Next Obligation.
  intros I C i f g η θ Hηθ; exact (Hηθ i).
Qed.
Next Obligation.
  intros I C i f; reflexivity.
Qed.
Next Obligation.
  intros I C i f g h η θ; reflexivity.
Qed.

(** ** The universal property / ** 通用性质 *)

(*
 Pairing: a family of functors into the components assembles into one
 functor into the product, componentwise. 

 --------
 配对：一族指向各个分量的函子组合成一个分量wise指向乘积的函子。
*)
Program Definition PiCat_Pair {I : Type} {C : I → Category}
  {D : Category} (R : ∀ i : I, D ⟶ C i) : D ⟶ PiCat C := {|
  fobj := fun d i => R i d;
  fmap := fun x y h i => fmap[R i] h
|}.
Next Obligation.
  intros I C D R x y h h' Hh i.
  exact (fmap_respects _ _ _ _ Hh).
Qed.
Next Obligation.
  intros I C D R x i; exact (@fmap_id _ _ (R i) x).
Qed.
Next Obligation.
  intros I C D R x y z h h' i; exact (@fmap_comp _ _ (R i) _ _ _ h h').
Qed.

(*
 The triangle: projecting the pairing IS the component, definitionally
 on both objects and arrows, so the natural isomorphism is the
 identity family. 

 --------
 三角形：投射配对在定义上是组成部分，作用于对象和箭头，因此自然同构是恒等族。
*)
Lemma PiCat_Pair_Proj {I : Type} {C : I → Category}
  {D : Category} (R : ∀ i : I, D ⟶ C i) (i : I) :
  PiCat_Proj C i ◯ PiCat_Pair R ≈ R i.
Proof.
  simpl; exists (fun d => iso_id).
  intros x y h; simpl.
  rewrite id_left, id_right; reflexivity.
Qed.

(*
 Uniqueness, up to Cat's hom-equivalence: any functor whose
 projections agree with the family agrees with the pairing.  The
 witnessing isomorphism is assembled componentwise from the given
 ones, and its naturality is their naturality, component by
 component. 

 --------
 唯一性，取Cat的同范等价：任何投影与该族一致的函子都与配对一致。所见证的同构是从给定的同构按组件组装而成，其自然性是它们的自然性，逐组件地。
*)
Lemma PiCat_ump_unique {I : Type} {C : I → Category} {D : Category}
  (R : ∀ i : I, D ⟶ C i) (H : D ⟶ PiCat C) :
  (∀ i : I, PiCat_Proj C i ◯ H ≈ R i) →
  H ≈ PiCat_Pair R.
Proof.
  intros HP; simpl.
  unshelve eexists.
  - intro d.
    unshelve refine
      (@Build_Isomorphism (PiCat C) (H d) (fun i => R i d)
         (fun i => to (projT1 (HP i) d))
         (fun i => from (projT1 (HP i) d)) _ _).
    + intro i; exact (iso_to_from (projT1 (HP i) d)).
    + intro i; exact (iso_from_to (projT1 (HP i) d)).
  - intros x y h i; simpl.
    exact (projT2 (HP i) x y h).
Qed.

(*
 The whole universal property, bundled: existence is the pairing with
 its triangle, uniqueness the lemma above. 

 --------
 整个泛性质，打包：存在性是与它的三角形配对，唯一性是上面的引理。
*)
Lemma PiCat_ump {I : Type} {C : I → Category} {D : Category}
  (R : ∀ i : I, D ⟶ C i) :
  ∃! F : D ⟶ PiCat C, ∀ i : I, PiCat_Proj C i ◯ F ≈ R i.
Proof.
  unshelve eapply Build_Unique.
  - exact (PiCat_Pair R).
  - exact (fun i => PiCat_Pair_Proj R i).
  - intros H HP; symmetry; exact (PiCat_ump_unique R H HP).
Qed.

(*
 F6-style sanity: the product over a constant two-member family
 projects a choice function to its component, by computation. 

 --------
 F6 风格的理智：对一个固定的双成员族的乘积，通过计算将选择函数投影到其组成部分上。
*)
Example PiCat_witness :
  fobj[PiCat_Proj (fun _ : bool => _2) true] (fun _ => TwoX) = TwoX
  := eq_refl.
