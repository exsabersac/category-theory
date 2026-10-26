Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

(** * Internal monoids in a monoidal category / * 单性范畴中的内部幺半群 *)

(*
nLab: https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Monoid_(category_theory)

   Given a monoidal category (C, ⨂, I), a monoid (object) on an object X : C
   is a triple (X, mu, eta) with a multiplication mu : X ⨂ X ~> X and a unit
   eta : I ~> X satisfying the associativity and left/right unit laws, with
   the associator and unitors inserted to make the maps composable:

     associativity  mu ∘ (mu ⨂ id) ≈ mu ∘ (id ⨂ mu) ∘ α     (α = to tensor_assoc)
     left unit      mu ∘ (eta ⨂ id) ≈ λ                       (λ = to unit_left)
     right unit     mu ∘ (id ⨂ eta) ≈ ρ                       (ρ = to unit_right)

   Here ⨂ on morphisms is [bimap], α : (X ⨂ X) ⨂ X ≅ X ⨂ (X ⨂ X) is the
   associator, and λ : I ⨂ X ≅ X, ρ : X ⨂ I ≅ X are the left/right unitors;
   the [to] direction of each isomorphism is the one used above.

   This is the standard nLab/Wikipedia definition of “monoid in a monoidal
   category”. The existing [Structure.Monoid] file gives an equivalent
   presentation, but its [MonoidObject] is developed alongside the cartesian
   case using the cartesian unit/associator. Here we factor out the abstract
   monoid-in-a-monoidal-category form so it can be reused as the building
   block for Frobenius algebras (and dualised to give comonoids).

   The laws are stated as setoid equalities ([≈]), so that morphisms which
   are merely equivalent up to the homset equivalence are considered to be
   “the same” structural map.

--------
nLab：https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category
维基百科：https://en.wikipedia.org/wiki/Monoid_(category_theory)

给定一个幺半范畴 (C, ⨂, I)，在对象 X : C 上的一个幺半（对象）是一个三元组 (X, mu, eta)，其中包含一个乘法 mu : X ⨂ X ~> X 和一个单位 eta : I ~> X，满足结合律以及左/右单位律，并在映射可组合的地方插入结合子和单位子：

结合律  mu ∘ (mu ⨂ id) ≈ mu ∘ (id ⨂ mu) ∘ α     (α = tensor_assoc)  
左单位  mu ∘ (eta ⨂ id) ≈ λ                       (λ = unit_left)  
右单位  mu ∘ (id ⨂ eta) ≈ ρ                       (ρ = unit_right)

这里⨂在态射上是[bimap]，α : (X ⨂ X) ⨂ X ≅ X ⨂ (X ⨂ X)是结合子，λ : I ⨂ X ≅ X，ρ : X ⨂ I ≅ X是左/右单位同构；每个同构的[to]方向是上面使用的方向。

这是 nLab/Wikipedia 对“单体范畴中的幺半群”的标准定义。现有的 [Structure.Monoid] 文件给出了一个等价的表示，但它的 [MonoidObject] 是在笛卡尔情况中使用笛卡尔单位/结合子一起开发的。在这里，我们将抽象的单体范畴中幺半群形式提取出来，以便可以将其重新用作弗罗贝尼乌斯代数的构建模块（并进行对偶化以产生余半群）。

这些定律被表述为集合等式（[≈]），因此仅在上同态集合等价下等价的态射被认为是“相同”的结构映射。
*)

Section Monoid.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class Monoid (X : C) : Type := {
  mu  : X ⨂ X ~> X;             (* multiplication μ : X ⨂ X ~> X / 乘法 μ : X ⨂ X ~> X *)
  eta : I ~> X;                 (* unit           η : I     ~> X / 单位           η : I     ~> X *)

  (* associativity: mu ∘ (mu ⨂ id) ≈ mu ∘ (id ⨂ mu) ∘ α / 结合性：mu ∘ (mu ⨂ id) ≈ mu ∘ (id ⨂ mu) ∘ α *)
  mu_assoc :
    mu ∘ bimap mu id[X]
      ≈ mu ∘ bimap id[X] mu ∘ to tensor_assoc;

  (* left unit: mu ∘ (eta ⨂ id) ≈ λ (left unitor) / 左单位元：mu ∘ (eta ⨂ id) ≈ λ（左单位子） *)
  mu_unit_left :
    mu ∘ bimap eta id[X]
      ≈ to (@unit_left C M X);

  (* right unit: mu ∘ (id ⨂ eta) ≈ ρ (right unitor) / 右单位元：mu ∘ (id ⨂ eta) ≈ ρ（右单元子） *)
  mu_unit_right :
    mu ∘ bimap id[X] eta
      ≈ to (@unit_right C M X)
}.

End Monoid.

Arguments mu  {C M X _}.
Arguments eta {C M X _}.

Notation "'mu[' Mon ]"  := (@mu _ _ _ Mon)
  (at level 9, format "'mu[' Mon ]") : morphism_scope.
Notation "'eta[' Mon ]" := (@eta _ _ _ Mon)
  (at level 9, format "'eta[' Mon ]") : morphism_scope.
