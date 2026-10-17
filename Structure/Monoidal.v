Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.

Generalizable All Variables.

Section Monoidal.

Context {C : Category}.

(* nLab: https://ncatlab.org/nlab/show/monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

   幺半范畴是配备张量积与单位对象、在连贯同构下结合与有单位的范畴。数据是单位对象 I、
   张量双函子 ⊗ : C ∏ C ⟶ C，以及三个自然同构，

       lambda  : I ⊗ x ≅ x              ([unit_left]),
       rho     : x ⊗ I ≅ x              ([unit_right]),
       alpha   : (x ⊗ y) ⊗ z ≅ x ⊗ (y ⊗ z)   ([tensor_assoc]),

   分别是左单位子、右单位子与结合子。结合子方向 (x ⊗ y) ⊗ z ≅ x ⊗ (y ⊗ z) 依 nLab；
   某些来源取相反定向，仅差逆。

   每个同构的自然性在正向 (to) 与反向 (from) 都显式记录，使重写与对偶化两向可用。
   对 lambda 即方块 g ∘ λ ≈ λ ∘ (id ⊗ g)，rho 与 alpha 类似。

   两条连贯条件支配这些同构的相互作用：

       triangle:  (ρ ⊗ id) ≈ (id ⊗ λ) ∘ α   在   (x ⊗ I) ⊗ y 上
       pentagon:  (id ⊗ α) ∘ α ∘ (α ⊗ id) ≈ α ∘ α
                                              在  ((x ⊗ y) ⊗ z) ⊗ w 上

   三角形恒等式经单位关联单位子与结合子；五边形恒等式使四重张量的两种重结合一致。
   由 Mac Lane 连贯定理，这两定律迫使由 α、λ、ρ 建造的每个形式图交换。 *)

(*
   nLab:  https://ncatlab.org/nlab/show/monoidal+category
   Paper: Bénabou, "Catégories avec multiplication", C. R. Acad. Sci.
   Paper: Mac Lane, "Natural Associativity and Commutativity", Rice
   Paper: Kelly, "On MacLane's conditions for coherence of natural
   Paper: Joyal, Street, "The geometry of tensor calculus, I", Advances
   Paper: Baez, Stay, "Physics, Topology, Logic and Computation: A

   本节说明 Monoidal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Reserved Infix "⨂" (at level 30, right associativity).

Class Monoidal := {
  I : C;                        (* unit_obj *)
  tensor : C ∏ C ⟶ C where "x ⨂ y" := (tensor (x, y));

  unit_left  {x} : I ⨂ x ≅ x;  (* lambda *)
  unit_right {x} : x ⨂ I ≅ x;  (* rho *)

  tensor_assoc {x y z} : (x ⨂ y) ⨂ z ≅ x ⨂ (y ⨂ z);  (* alpha *)

  (* alpha, lambda and rho are all natural isomorphisms. *)

  to_unit_left_natural {x y} (g : x ~> y) :
    g ∘ unit_left << I ⨂ x ~~> y >> unit_left ∘ bimap id g;
  from_unit_left_natural {x y} (g : x ~> y) :
    bimap id g ∘ unit_left⁻¹ << x ~~> I ⨂ y >> unit_left⁻¹ ∘ g;

  to_unit_right_natural {x y} (g : x ~> y) :
    g ∘ unit_right << x ⨂ I ~~> y >> unit_right ∘ bimap g id;
  from_unit_right_natural {x y} (g : x ~> y) :
    bimap g id ∘ unit_right⁻¹ << x ~~> y ⨂ I >> unit_right⁻¹ ∘ g;

  to_tensor_assoc_natural
    {x y z w v u} (g : x ~> y) (h : z ~> w) (i : v ~> u) :
    bimap g (bimap h i) ∘ tensor_assoc
      << (x ⨂ z) ⨂ v ~~> y ⨂ w ⨂ u >>
    tensor_assoc ∘ bimap (bimap g h) i;

  from_tensor_assoc_natural
    {x y z w v u} (g : x ~> y) (h : z ~> w) (i : v ~> u) :
    bimap (bimap g h) i ∘ tensor_assoc⁻¹
      << x ⨂ z ⨂ v ~~> (y ⨂ w) ⨂ u >>
    tensor_assoc⁻¹ ∘ bimap g (bimap h i);

  (* The above observe the following coherence conditions:
     the triangle identity (unitors vs. associator) and the pentagon
     identity (the two reassociations of a fourfold tensor agree). *)

  triangle_identity {x y} :
    bimap unit_right id
      << (x ⨂ I) ⨂ y ~~> x ⨂ y >>
    bimap id unit_left ∘ tensor_assoc;

  pentagon_identity {x y z w} :
    bimap id tensor_assoc ∘ tensor_assoc ∘ bimap tensor_assoc id
      << ((x ⨂ y) ⨂ z) ⨂ w ~~> x ⨂ (y ⨂ (z ⨂ w)) >>
    tensor_assoc ∘ tensor_assoc
}.

End Monoidal.

Notation "(⨂)" := (@tensor _ _) : functor_scope.
Notation "x ⨂ y" := (@tensor _ _ (x%object, y%object))
  (at level 30, right associativity) : object_scope.
Notation "x ⨂[ M ] y" := (fobj[@tensor _ M] (x, y))
  (at level 30, only parsing, right associativity) : object_scope.
Notation "f ⨂ g" := (bimap[(⨂)] f g)
  (at level 30, right associativity) : morphism_scope.
Notation "f ⨂[ M ] g" := (bimap[@tensor _ M] f g)
  (at level 30, only parsing, right associativity) : morphism_scope.
