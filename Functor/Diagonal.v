Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(** The diagonal functor Δ : C ⟶ [J, C] (and the binary Δ : C ⟶ C ∏ C).  / 对角函子 Δ : C ⟶ [J, C] （以及二进制 Δ : C ⟶ C ∏ C）。*)

(*
nLab: https://ncatlab.org/nlab/show/diagonal+functor
   Wikipedia: https://en.wikipedia.org/wiki/Diagonal_functor

   For a fixed index category J, the diagonal functor Δ[J] : C ⟶ [J, C] sends
   each object c : C to the constant functor Δ[J](c) : J ⟶ C, which takes every
   object of J to c and every morphism of J to id[c]; and it sends each
   morphism f : c ~> c' to the natural transformation Δ[J](c) ⟹ Δ[J](c') whose
   component at every j : J is f itself (naturality is f ∘ id ≈ id ∘ f). When J
   is the discrete two-object category this recovers the binary diagonal
   Δ : C ⟶ C ∏ C with c ↦ (c, c); Diagonal_Product_Two below witnesses that
   agreement.

   The diagonal is the universal source of cones: a cone over a diagram
   F : J ⟶ C with apex c is exactly a natural transformation Δ[J](c) ⟹ F. When
   the relevant universal cones exist, Δ is sandwiched by the limit and colimit
   functors as colim ⊣ Δ ⊣ lim (C is J-cocomplete iff Δ has a left adjoint and
   J-complete iff Δ has a right adjoint); for the binary case this is the
   familiar (-) + (-) ⊣ Δ ⊣ (-) × (-). 

--------
nLab：https://ncatlab.org/nlab/show/diagonal+functor
 维基百科：https://en.wikipedia.org/wiki/Diagonal_functor

对于固定索引类别 J，对角函子 Δ[J] : C ⟶ [J, C] 发送
 每个对象 c : C 到常量函子 Δ[J](c) : J ⟶ C，它取每个
 J 到 c 的对象以及 J 到 id[c] 的每个态射； 它发送每个
 态射 f : c ~> c' 到自然变换 Δ[J](c) ⟹ Δ[J](c') 其
 每个 j 处的分量：J 是 f 本身（自然性是 f ∘ id ≈ id ∘ f）。 当 J
 是离散双对象类别，它恢复二进制对角线
 Δ : C ⟶ C ∏ C 且 c ↦ (c, c)； Diagonal_Product_下面的两个见证人
 协议。

对角线是圆锥体的普遍来源：图表上的圆锥体
 F : J ⟶ C 且顶点为 c 正是自然变换 Δ[J](c) ⟹ F。 
存在相关的通用锥体，Δ 夹在极限和余极限之间
 函子为 colim ⊣ Δ ⊣ lim （C 是 J-余完备当且仅当 Δ 有左伴随且
 J-完备当且仅当 Δ 有右伴随）； 对于二进制情况，这是
 熟悉的 (-) + (-) ⊣ Δ ⊣ (-) × (-)。 
*)

(*
   【Diagonal 实例展开】/ Instance walkthrough

   1) 这是什么 / What this is
      Δ[J] : C ⟶ [J, C] —— 把对象 c 送到「常值函子」（处处 c、箭头为 id），
      把 f : c ~> c' 送到分量处处为 f 的自然变换。
      Sends c to the constant functor at c; f to the constant nat. trans. at f.
      锥的来源：锥 = Δ(c) ⟹ F；故 lim ⊣ Δ ⊣ 不对，正确是 colim ⊣ Δ ⊣ lim。
      Cones are Δ(c) ⟹ F; adjunction sandwich: colim ⊣ Δ ⊣ lim.

   2) 二元情形 / Binary case
      Diagonal_Product : C ⟶ C ∏ C，c ↦ (c,c)；J=离散两点时与上面一致。
      Binary diagonal c ↦ (c,c).

   阅读：常值函子 → Δ → 锥/极限 → 二元 Δ。
   Read: constant functor → Δ → cones/limits → binary Δ.
*)

#[export]
Program Instance Diagonal {C : Category} (J : Category) : C ⟶ [J, C] := {
  fobj := fun x =>
    {| fobj := fun _ => x
     ; fmap := fun _ _ _ => id[x] |};
  fmap := fun _ _ f =>
    {| transform := fun _ => f |}
}.

Section Diagonal_Product.

#[local] Set Transparent Obligations.

#[export]
Program Instance Diagonal_Product `(C : Category) : C ⟶ C ∏ C.

End Diagonal_Product.

Notation "Δ[ J ]( c )" := (Diagonal J c) (at level 0, format "Δ[ J ]( c )") : functor_scope.

Require Import Category.Instance.One.

Notation "Δ( c )" := (Diagonal _ c) (at level 0, format "Δ( c )") : functor_scope.
Notation "=( c )" := (Diagonal 1 c) (at level 0, format "=( c )") : functor_scope.

Definition Δ {C J : Category} := @Diagonal C J.

(*
Wikipedia: https://en.wikipedia.org/wiki/Diagonal_functor

   Wikipedia: “In category theory, a branch of mathematics, the diagonal
   functor C → C × C is given by Δ(a) = ⟨a, a⟩, which maps objects as well as
   morphisms. This functor can be employed to give a succinct alternate
   description of the product of objects within the category C: a product a ×
   b is a universal arrow from Δ to ⟨a, b⟩. The arrow comprises the projection
   maps.”

  “More generally, in any functor category Cᴶ (here J should be thought of as
  a small index category), for each object a in C, there is a constant functor
  with fixed object a : Δ(a) ∈ Cᴶ. The diagonal functor Δ : C → Cᴶ assigns to
  each object of C the functor Δ(a), and to each morphism f : a → b in C the
  obvious natural transformation η in Cᴶ (given by ηⱼ = f). In the case that J
  is a discrete category with two objects, the diagonal functor C → C × C is
  recovered.” 

--------
维基百科：https://en.wikipedia.org/wiki/Diagonal_functor

 维基百科：“在范畴论中，数学的一个分支，对角线
 函子 C → C × C 由 Δ(a) = ⟨a, a⟩ 给出，它映射对象以及
 态射。 这个函子可以用来给出一个简洁的替代方案
 C 类对象的产品描述：产品 a ×
 b 是从 Δ 到 ⟨a, b⟩ 的通用箭头。 箭头包括投影
 地图。”

 “更一般地，在任何函子类别 Cᴶ 中（这里 J 应该被认为是
 一个小的索引类别），对于C中的每个对象a，都有一个常量函子
 具有固定对象 a : Δ(a) ∈ Cᴶ。 对角函子 Δ : C → Cᴶ 赋值给
 C 的每个对象函子 Δ(a)，并且对于 C 中的每个态射 f : a → b
 Cᴶ 中明显的自然变换 η（由 ηⱼ = f 给出）。 如果是 J
 是具有两个对象的离散类别，对角函子 C → C × C 是
 康复了。” 
*)

Require Import Category.Instance.Two.Discrete.

Theorem Diagonal_Product_Two (C : Category) :
  (∀ x, Diagonal_Product C x ≅ (Diagonal Two_Discrete x TwoDX,
                                Diagonal Two_Discrete x TwoDY)) *
  (∀ x y (f : x ~> y),
     fmap[Diagonal_Product C] f
       ≈ (transform[fmap[Diagonal Two_Discrete] f] TwoDX,
          transform[fmap[Diagonal Two_Discrete] f] TwoDY)).
Proof.
  split; intros.
  - isomorphism; simpl; intros; try exact (id, id); cat.
  - reflexivity.
Qed.

#[export]
Instance Transform_Const `(x ~{C}~> y) : Δ(x) ⟹ Δ(y).
Proof. construct; auto; cat_simpl. Qed.
