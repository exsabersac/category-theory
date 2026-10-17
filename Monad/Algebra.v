Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.

Generalizable All Variables.

(** * Algebras over a monad (Eilenberg–Moore algebras) *)

(* nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)

   对范畴 C 上的单子 (T, ret, join)——单位 ret（η : Id ⟹ T）与乘法 join（μ : T ○ T ⟹ T）——
   对象 [a] 上的 T-代数是结构映射 t_alg（h : T a ~> a），服从两定律。单位律
   t_alg ∘ ret ≈ id（h ∘ η_a = id_a）说结构映射撤销单位；作用律
   t_alg ∘ fmap t_alg ≈ t_alg ∘ join（h ∘ T h = h ∘ μ_a）说它与乘法相容：先用 μ 压平再作用一次
   与作用两次一致。这些是 Eilenberg–Moore 代数；连同下文态射构成 Eilenberg–Moore 范畴 C^T
   （nLab: https://ncatlab.org/nlab/show/Eilenberg-Moore+category），组装于
   [Monad.Eilenberg.Moore]。每个对象上的自由代数 (T a, join) 恢复遗忘函子 C^T ⟶ C 的左伴随。 *)
Class TAlgebra `(T : C ⟶ C) `{@Monad C T} (a : C) := {
  t_alg : T a ~> a;

  t_id     : t_alg ∘ ret ≈ id;
  t_action : t_alg ∘ fmap t_alg ≈ t_alg ∘ join
}.

Arguments TAlgebra {C} T {_} a.

Notation "t_alg[ T ]" := (@t_alg _ _ _ _ T)
  (at level 9, format "t_alg[ T ]") : morphism_scope.

(* nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)

   A morphism of T-algebras (an algebra homomorphism) from (a, t_alg[F]) to
   (b, t_alg[G]) is an underlying arrow t_alg_hom (f : a ~> b) commuting with
   the structure maps: t_alg_hom ∘ t_alg[F] ≈ t_alg[G] ∘ fmap[T] t_alg_hom
   (f ∘ h_F = h_G ∘ T f). Equivalently, the square sending each algebra action
   through f agrees with first lifting f along T and then acting. *)
Class TAlgebraHom `(T : C ⟶ C) `{@Monad C T} (a b : C)
      (F : TAlgebra T a) (G : TAlgebra T b) := {
  t_alg_hom : a ~> b;

  t_alg_hom_commutes : t_alg_hom ∘ t_alg[F] ≈ t_alg[G] ∘ fmap[T] t_alg_hom
}.

Notation "t_alg_hom[ F ]" := (@t_alg_hom _ _ _ _ _ _ _ F)
  (at level 9, format "t_alg_hom[ F ]") : morphism_scope.
