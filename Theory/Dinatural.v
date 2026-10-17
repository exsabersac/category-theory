Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.

Generalizable All Variables.

Section Dinatural.

Context {C : Category}.
Context {D : Category}.
Context {F : C^op ∏ C ⟶ D}.
Context {G : C^op ∏ C ⟶ D}.

(* `prod_split f g` 把反变分量 `f`（`C^op` 的态射）与共变分量 `g`（`C` 的态射）
   打包成积范畴 `C^op ∏ C` 的单个态射，供 `F` 与 `G` 作用。记号 `f ⋆⋆⋆ g`
   （section 局部）只是 `(f, g)` 的缩写，使 `dinaturality` 使用点处每个函子变元的
   混合变差显式可见。 *)
Definition prod_split {x y z w} (f : x ~{C^op}~> z) (g : y ~{C}~> w) :
  (x, y) ~{ (C ^op) ∏ C }~> (z, w) := (f, g).
Arguments prod_split {_ _ _ _} _ _ /.

Infix "⋆⋆⋆" := prod_split (at level 100) : category_scope.

(* nLab: https://ncatlab.org/nlab/show/dinatural+transformation
   Wikipedia: https://en.wikipedia.org/wiki/Dinatural_transformation

   双自然变换 (dinatural transformation) α : F ⇸ G 介于两函子
   F, G : C^op ∏ C ⟶ D 之间，是一族分量 α_c : F(c,c) ~> G(c,c)，使对每个
   f : c ~> c' 下列六边形交换（混合单变元的反变与共变出现）。它弱于自然变换：
   当 F 与 G 实际来自忽略一变元的函子时，双自然性退化为普通自然性。 *)
Class Dinatural := {
  ditransform {x} : F (x, x) ~> G (x, x);  (* component α_x on the diagonal *)

  (* dinaturality hexagon, for `f : x ~> y`, both sides `F (y,x) ~> G (x,y)`:
     `G f x ∘ α_x ∘ F f x ≈ G x f ∘ α_y ∘ F x f` *)
  dinaturality {x y} (f : x ~{C}~> y) :
    fmap[G] (op f ⋆⋆⋆ id) ∘ @ditransform y ∘ fmap[F] (id ⋆⋆⋆ f)
        ≈ fmap[G] (id ⋆⋆⋆ f) ∘ @ditransform x ∘ fmap[F] (op f ⋆⋆⋆ id)
}.

#[export] Program Instance Dinatural_Setoid : Setoid Dinatural := {|
  equiv := fun X Y => forall x, (@ditransform X x) ≈ (@ditransform Y x)
|}.
Next Obligation.
  equivalence.
  transitivity (@ditransform y x0); auto.
Qed.

End Dinatural.

Notation "ditransform[ F ]" := (@ditransform _ _ _ _ F)
  (at level 9, format "ditransform[ F ]") : category_scope.

(* Dinatural transformations can be applied directly to functorial values to
   perform the functor mapping they imply. *)
Coercion ditransform : Dinatural >-> Funclass.
