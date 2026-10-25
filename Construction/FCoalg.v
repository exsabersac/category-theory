Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.FAlg.

Generalizable All Variables.

(** * The category of F-coalgebras / * F-余代数的类别 *)

(*
 nLab:      https://ncatlab.org/nlab/show/coalgebra+of+an+endofunctor
 Wikipedia: https://en.wikipedia.org/wiki/F-coalgebra

 An F-coalgebra is an object [a] with a structure map [γ : a ~> F a]
 ([FCoalgebra F a] of Theory/Functor.v); a coalgebra morphism commutes with
 the structure maps.  This is exactly an [F^op]-algebra in [C^op], so the
 category is obtained by duality rather than re-proving the laws:

 FCoalg F := (FAlg (F^op))^op.

 Because the library's duality is definitional ([C^op^op = C] by
 reflexivity), the covariant components are the expected ones: objects are
 pairs [(a, γ : a ~> F a)] and the forgetful functor lands back in [C].  The
 final coalgebra (when it exists) is the greatest fixed point of [F];
 [lambek_final] (Theory/Lambek.v) makes its structure map an isomorphism. 

 --------
 nLab：       https://ncatlab.org/nlab/show/coalgebra+of+an+endofunctor 
 维基百科：  https://en.wikipedia.org/wiki/F-coalgebra 

 一个 F-余代数是一个对象  [a] ，带有一个结构映射  [γ : a ~> F a] 
 ( [FCoalgebra F a]  来自 Theory/Functor.v)；余代数态射与结构映射交换。 这正好是一个  [F^op] -代数在  [C^op] ，因此该范畴是通过对偶获得的，而不是重新证明定律：

 FCoalg F := (FAlg (F^op))^op。

 因为库的对偶性是定义性的 ( [C^op^op = C]  通过自反性)，协变分量是预期的：对象是对  [(a, γ : a ~> F a)] ，而遗忘函子返回到  [C] 。
 最终余代数（当它存在时）是  [F] 的最大不动点； [lambek_final] (Theory/Lambek.v) 使其结构映射成为同构。
*)

Definition FCoalg `(F : C ⟶ C) : Category := (FAlg (F^op))^op.

(*
 A co-algebra hom-set of [FCoalg F] is, on the nose, an [F^op]-algebra hom of
 the opposite category. 

 --------
 [FCoalg F] 的余代数同态集，严格来说，是对偶范畴中的 [F^op]-代数同态。
*)
Lemma fcoalg_hom `(F : C ⟶ C) (x y : FCoalg F) :
  (x ~{FCoalg F}~> y) = (y ~{FAlg (F^op)}~> x).
Proof. reflexivity. Qed.

(*
 The forgetful functor to the underlying category, by dualizing
 [FAlg_Forget] and using [C^op^op = C]. 

 --------
 通过对 [FAlg_Forget]  进行对偶化并使用 [C^op^op = C] ，指向底层范畴的遗忘函子。
*)
Definition FCoalg_Forget `(F : C ⟶ C) : FCoalg F ⟶ C :=
  (FAlg_Forget (F^op))^op.
