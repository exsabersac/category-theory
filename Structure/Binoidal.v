Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

Section Binoidal.

Context {C : Category}.

Reserved Infix "⋉" (at level 15, right associativity).
Reserved Infix "⋊" (at level 15, right associativity).
Reserved Infix "⊗" (at level 30, right associativity).

(*
 nLab: https://ncatlab.org/nlab/show/binoidal+category
 Wikipedia: none (no "binoidal category" article; the notion is covered
 under https://en.wikipedia.org/wiki/Premonoidal_category)

 A binoidal category is a category C with an object x ⊗ y for each pair of
 objects that is functorial in each argument *separately* rather than
 jointly. Where a monoidal tensor is a single bifunctor C ∏ C ⟶ C, the
 binoidal tensor provides, for each fixed object, two one-argument
 tensoring functors,

 x ⋉ -  : C ⟶ C   maps z to z ⊗ x      ([inj_left x],  - ⊗ x fixed right)
 x ⋊ -  : C ⟶ C   maps z to x ⊗ z      ([inj_right x], x ⊗ - fixed left)

 These need not assemble into a bifunctor: tensoring f : a ~> b on the left
 and f' : a' ~> b' on the right may be applied in two orders, giving in
 general distinct composites a ⊗ a' ~> b ⊗ b'. This is the "premagmoidal"
 precursor to a premonoidal category, which adds a unit and central
 coherence isomorphisms. The premonoidal successor is
 Structure/Premonoidal.v; the funny-tensor characterization of
 separately-functorial tensors is Instance/StrictCat/Premonoid.v. The
 naming here follows the rest of the library; the symbols ⋉ / ⋊ match the
 nLab convention for the right/left tensoring functors. 

 --------
 nLab:  https://ncatlab.org/nlab/show/binoidal+category 
 维基百科: 无（没有“binoidal category”条目；该概念在 https://en.wikipedia.org/wiki/Premonoidal_category) 下有所涉及）

 二元范畴是一个范畴 C，它为每一对对象提供一个对象 x ⊗ y，并且在每个参数上*分别*是函子范畴的，而不是联合的。一个单一的单范畴张量是一个双函子 C ∏ C ⟶ C，而二元张量则为每个固定对象提供两个单参数张量函子，

 x ⋉ -  : C ⟶ C   映射 z 到 z ⊗ x      ([inj_left x], - ⊗ x 固定右)
 x ⋊ -  : C ⟶ C   映射 z 到 x ⊗ z      ([inj_right x], x ⊗ - 固定左)这些不需要组装成一个双函子：在左边对 f : a ~> b 进行张量操作，以及在右边对 f' : a' ~> b' 进行张量操作，可以以两种顺序应用，通常会产生不同的复合 a ⊗ a' ~> b ⊗ b'。这是前单模范畴（premagmoidal）的前身，它会添加一个单位和中心一致性同构。前单模范畴的后继是 Structure/Premonoidal.v；单独函子化张量的滑稽张量特性在 Instance/StrictCat/Premonoid.v 中。这里的命名遵循库的其他部分；符号 ⋉ / ⋊ 对应 nLab 关于右/左张量函子的惯例。
*)
Class Binoidal := {
  tensor (x y : C) : C where "x ⊗ y" := (tensor x y);

  (*
 The binoidal tensor is functorial in each argument separately, whereas
 monoidal categories, whose tensor is a functor from C ∏ C ⟶ C, is
 functorial in both arguments jointly. 

 --------
 双二元张量在每个参数上都是函子性的，而单体范畴的张量是从 C ∏ C ⟶ C 的函子，在两个参数上是联合函子性的。
*)
  left_functor y' : AFunctor (λ x, x ⊗ y');         (* - ⊗ y' (fixes right) / - ⊗ y'（固定右侧） *)
  inj_left (y' : C) : C ⟶ C := FromAFunctor (left_functor y')
    where "x ⋉ y" := (inj_left x y);

  right_functor x' : AFunctor (λ y, x' ⊗ y);        (* x' ⊗ - (fixes left) / x' ⊗ -（固定左） *)
  inj_right (x' : C) : C ⟶ C := FromAFunctor (right_functor x')
    where "x ⋊ y" := (inj_right x y);
}.

Context `{Binoidal}.

Notation "x ⋉ y" := (inj_left x y) (at level 15, right associativity).
Notation "x ⋊ y" := (inj_right x y) (at level 15, right associativity).
Notation "x ⊗ y" := (tensor x y) (at level 30, right associativity).

Corollary inj_left_right {x y} : x ⋉ y = y ⋊ x.
Proof. reflexivity. Qed.

(*
 A morphism f : x ~> y in a binoidal category is central if, for every
 morphism f' : x' ~> y', the two orders of tensoring f and f' agree. The
 first conjunct is the square on x ⊗ x' ~~> y ⊗ y' (f on the left, f' on the
 right); the second is the mirror square on x' ⊗ x ~~> y' ⊗ y. When f is
 central these common composites are the f ⊗ f' and f' ⊗ f below. The
 central morphisms form the centre, a monoidal subcategory of C: it is
 constructed as a wide subcategory in Structure/Binoidal/Central.v
 ([Centre]), and shown monoidal for premonoidal C in
 Structure/Premonoidal/Centre.v ([Centre_Monoidal]). 

 --------
 在双半群范畴中，如果对于每一个态射 f' : x' ~> y'，f : x ~> y 的两种张量顺序相同，则称该态射 f 为中心态射。第一个合取是 x ⊗ x' ~~> y ⊗ y' 的方形图（f 在左边，f' 在右边）；第二个是 x' ⊗ x ~~> y' ⊗ y 的镜像方形图。当 f 是中心态射时，这些公共复合态射便是下面的 f ⊗ f' 和 f' ⊗ f。中心态射构成中心，这是 C 的一个幺半范畴子范畴：它在 Structure/Binoidal/Central.v ([Centre]) 中构造为宽子范畴，并在 Structure/Premonoidal/Centre.v ([Centre_Monoidal]) 中证明对于前半群范畴 C 来说是幺半的。
*)

Definition central `(f : x ~> y) : Type :=
  ∀ x' y' (f' : x' ~> y'),
    (fmap[inj_left y'] f ∘ fmap[inj_right x] f'
       << x ⊗ x' ~~> y ⊗ y' >>
     fmap[inj_right y] f' ∘ fmap[inj_left x'] f)
  ∧ (fmap[inj_left y] f' ∘ fmap[inj_right x'] f
       << x' ⊗ x ~~> y' ⊗ y >>
     fmap[inj_right y'] f ∘ fmap[inj_left x] f').

Definition composite_ff' {x x' y y'} (f : x ~> y) (f' : x' ~> y') :
  x ⊗ x' ~> y ⊗ y' := fmap[inj_right y] f' ∘ fmap[inj_left x'] f.

#[export]
Program Instance composite_ff'_respects {x x' y y'} :
  Proper (equiv ==> equiv ==> equiv) (@composite_ff' x x' y y').
Next Obligation.
  unfold composite_ff'.
  proper.
  destruct H.
  simpl in *.
  destruct left_functor0, right_functor0; simpl in *.
  now rewrite X, X0.
Qed.

Definition composite_f'f {x x' y y'} (f' : x' ~> y') (f : x ~> y) :
  x' ⊗ x ~> y' ⊗ y := fmap[inj_right y'] f ∘ fmap[inj_left x] f'.

#[export]
Program Instance composite_f'f_respects {x x' y y'} :
  Proper (equiv ==> equiv ==> equiv) (@composite_f'f x x' y y').
Next Obligation.
  unfold composite_f'f.
  proper.
  destruct H.
  simpl in *.
  destruct left_functor0, right_functor0; simpl in *.
  now rewrite X, X0.
Qed.

End Binoidal.

Notation "x ⋉ y" := (@inj_left _ _ y x)
  (at level 15, right associativity) : object_scope.
Notation "x ⋊ y" := (@inj_right _ _ x y)
  (at level 15, right associativity) : object_scope.

Notation "f ⋉ y" := (fmap[@inj_left _ _ y] f)
  (at level 15, right associativity) : morphism_scope.
Notation "x ⋊ f" := (fmap[@inj_right _ _ x] f)
  (at level 15, right associativity) : morphism_scope.

Notation "(⊗)" := (@tensor _ _) : functor_scope.
Notation "x ⊗ y" := (@tensor _ _ x%object y%object)
  (at level 30, right associativity) : object_scope.
Notation "f ⊗ g" := (composite_ff' f g)
  (at level 30, right associativity) : morphism_scope.
