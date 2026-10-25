Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.

From Coq Require Import Arith.

Generalizable All Variables.

(* * * Parallel-composition bifunctor on FreeCat / * * 在自由范畴上的平行组合双函子 *)

(*
 nLab: https://ncatlab.org/nlab/show/monoidal+category
 nLab: https://ncatlab.org/nlab/show/PROP
 Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

 The monoidal product of a (strict, symmetric) monoidal category is a
 bifunctor [⊗ : C ∏ C ⟶ C].  For the free PROP [FreeCat S] this is the
 parallel composition of string diagrams, with arities given by addition:

 - on objects:    [(m, n) ↦ m + n]   (tensor on objects is [Nat.add])
 - on morphisms:  [(f, g) ↦ T_tens f g], so [f : m1 ~> n1] and
 [g : m2 ~> n2] yield [f ⊗ g : m1 + m2 ~> n1 + n2]

 The bifunctor laws (a functor out of the product category [FreeCat S ∏
 FreeCat S]) follow from the [TE_tens_*] constructors of the [TermEq]
 quotient relation:
 - respectfulness (fmap_respects):  [TE_tens_cong]
 - identity preservation (fmap_id): [TE_tens_id]
 [id_m ⊗ id_n ≈ id_(m+n)]
 - composition preservation (fmap_comp), i.e. the middle-four
 interchange [(f1 ⊙ f2) ⊗ (g1 ⊙ g2) ≈ (f1 ⊗ g1) ⊙ (f2 ⊗ g2)]:
 [TE_interchange] (used via [TE_sym], since the constructor states
 the reverse orientation). 

 --------
 nLab:  https://ncatlab.org/nlab/show/monoidal+category 
 nLab:  https://ncatlab.org/nlab/show/PROP 
 维基百科:  https://en.wikipedia.org/wiki/Monoidal_category 
 维基百科:  https://en.wikipedia.org/wiki/PROP_(category_theory) 

 （严格对称）单模范畴的模乘积是一个双函子 [⊗ : C ∏ C ⟶ C] 。对于自由 PROP [FreeCat S] ，这是弦图的平行组合，其元数由加法给出：

 - 对象上:     [(m, n) ↦ m + n]    （对象上的张量是 [Nat.add] ）
 - 态射上:   [(f, g) ↦ T_tens f g] ，所以 [f : m1 ~> n1] 和 [g : m2 ~> n2] 产生 [f ⊗ g : m1 + m2 ~> n1 + n2]双函子定律（一个从积范畴 [FreeCat S ∏ FreeCat S] 到外部的函子）遵循 [TE_tens_*] 构造的 [TermEq] 商关系：
 - 尊重性（fmap_respects）：[TE_tens_cong] 
 - 恒等保持（fmap_id）：[TE_tens_id] 
 [id_m ⊗ id_n ≈ id_(m+n)] 
 - 组合保持（fmap_comp），即中间四交换 [(f1 ⊙ f2) ⊗ (g1 ⊙ g2) ≈ (f1 ⊗ g1) ⊙ (f2 ⊗ g2)]：
 [TE_interchange]（通过 [TE_sym] 使用，因为构造器声明了反向方向）。
*)

Section FreeTensor.

Context (S : Signature).

(** The tensor bifunctor on FreeCat S. / 自由范畴 S 上的张量双函子。 *)
Program Definition FreeCat_Tensor : FreeCat S ∏ FreeCat S ⟶ FreeCat S := {|
  fobj := fun p => Nat.add (fst p) (snd p);
  fmap := fun p q m =>
    @T_tens S (fst p) (fst q) (snd p) (snd q) (fst m) (snd m)
|}.
Next Obligation.
  unfold Proper, respectful.
  intros [f1 f2] [g1 g2] [Hf Hg]; simpl in *.
  apply TE_tens_cong; assumption.
Qed.
Next Obligation.
  apply TE_tens_id.
Qed.
Next Obligation.
  apply TE_sym, TE_interchange.
Qed.

End FreeTensor.

Arguments FreeCat_Tensor S : assert.
