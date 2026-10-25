Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.

Generalizable All Variables.

(** * Algebras over a monad (Eilenberg–Moore algebras)  / * 单子上的代数（艾伦伯格-摩尔代数）*)

(*
nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)

   For a monad (T, ret, join) on a category C — with unit ret (η : Id ⟹ T)
   and multiplication join (μ : T ○ T ⟹ T) — a T-algebra on an object [a] is
   a structure map t_alg (h : T a ~> a) satisfying two laws. The unit law
   t_alg ∘ ret ≈ id (h ∘ η_a = id_a) says the structure map undoes the unit,
   and the action law t_alg ∘ fmap t_alg ≈ t_alg ∘ join (h ∘ T h = h ∘ μ_a)
   says it is compatible with the multiplication: flattening with μ first and
   acting once agrees with acting twice. These are the Eilenberg–Moore
   algebras; together with the morphisms below they form the Eilenberg–Moore
   category C^T (nLab: https://ncatlab.org/nlab/show/Eilenberg-Moore+category),
   assembled in [Monad.Eilenberg.Moore]. The free algebra (T a, join) on each
   object recovers a left adjoint to the forgetful functor C^T ⟶ C. 

--------
nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)

   对范畴 C 上的单子 (T, ret, join)——单位 ret（η : Id ⟹ T）与乘法 join（μ : T ○ T ⟹ T）——
   对象 [a] 上的 T-代数是结构映射 t_alg（h : T a ~> a），服从两定律。单位律
   t_alg ∘ ret ≈ id（h ∘ η_a = id_a）说结构映射撤销单位；作用律
   t_alg ∘ fmap t_alg ≈ t_alg ∘ join（h ∘ T h = h ∘ μ_a）说它与乘法相容：先用 μ 压平再作用一次
   与作用两次一致。这些是 Eilenberg–Moore 代数；连同下文态射构成 Eilenberg–Moore 范畴 C^T
   （nLab: https://ncatlab.org/nlab/show/Eilenberg-Moore+category），组装于
   [Monad.Eilenberg.Moore]。每个对象上的自由代数 (T a, join) 恢复遗忘函子 C^T ⟶ C 的左伴随。 
*)
(*
   【Class TAlgebra 语法与字段展开】/ Syntax & field walkthrough
   （口吻对齐 Theory/Functor.v @ c826572；受众：Coq 小白 + 范畴论小白的 Haskell 程序员）

   1) 这是什么 / What this is
      T-代数 = 载体 a + 结构映射 t_alg : T a ~> a，服从单位与作用律。
      它们是 Eilenberg–Moore 范畴的对象。
      T-algebra = carrier + structure map; objects of the EM category.
      Haskell 对照：可想成「能把 T a 解释回 a」且与 return/join 相容；
      日常代码较少直接写，但是理解 EM / 单子性的钥匙。
      Everyday Haskell rarely writes these; key to EM / monadicity.

   2) 数据与定律（均对 ≈）/ Data & laws (up to ≈)
      - t_alg : T a ~> a
      - t_id     : t_alg ∘ ret ≈ id
      - t_action : t_alg ∘ fmap t_alg ≈ t_alg ∘ join
      下文 TAlgebraHom：底层箭头与两边 t_alg 交换（也是 ≈）。
      TAlgebraHom below: underlying arrow commuting with both t_alg's.

   阅读顺序：t_alg → 两律 → TAlgebraHom → EilenbergMoore。
   Reading order: t_alg → two laws → TAlgebraHom → EilenbergMoore.
*)

Class TAlgebra `(T : C ⟶ C) `{@Monad C T} (a : C) := {
  t_alg : T a ~> a;

  t_id     : t_alg ∘ ret ≈ id;
  t_action : t_alg ∘ fmap t_alg ≈ t_alg ∘ join
}.

Arguments TAlgebra {C} T {_} a.

Notation "t_alg[ T ]" := (@t_alg _ _ _ _ T)
  (at level 9, format "t_alg[ T ]") : morphism_scope.

(*
nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)

   A morphism of T-algebras (an algebra homomorphism) from (a, t_alg[F]) to
   (b, t_alg[G]) is an underlying arrow t_alg_hom (f : a ~> b) commuting with
   the structure maps: t_alg_hom ∘ t_alg[F] ≈ t_alg[G] ∘ fmap[T] t_alg_hom
   (f ∘ h_F = h_G ∘ T f). Equivalently, the square sending each algebra action
   through f agrees with first lifting f along T and then acting. 

--------
nLab：https://ncatlab.org/nlab/show/algebra+over+a+monad
 维基百科：https://en.wikipedia.org/wiki/Monad_(category_theory)

 T 代数的态射（代数同态）从 (a, t_alg[F]) 到
 (b, t_alg[G]) 是一个底层箭头 t_alg_hom (f : a ~> b) 通勤
 结构映射： t_alg_hom ∘ t_alg[F] ≈ t_alg[G] ∘ fmap[T] t_alg_hom
 (f ∘ h_F = h_G ∘ T f)。 等效地，发送每个代数动作的方块
 through f 与先沿 T 提升 f 然后再作用一致。 
*)
Class TAlgebraHom `(T : C ⟶ C) `{@Monad C T} (a b : C)
      (F : TAlgebra T a) (G : TAlgebra T b) := {
  t_alg_hom : a ~> b;

  t_alg_hom_commutes : t_alg_hom ∘ t_alg[F] ≈ t_alg[G] ∘ fmap[T] t_alg_hom
}.

Notation "t_alg_hom[ F ]" := (@t_alg_hom _ _ _ _ _ _ _ F)
  (at level 9, format "t_alg_hom[ F ]") : morphism_scope.
