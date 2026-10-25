Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

(** Product (componentwise) monoidal structure on C ∏ D / C × D 上的乘积（按分量）单幺半群结构 *)

(*
 nLab: https://ncatlab.org/nlab/show/monoidal+category
 nLab: https://ncatlab.org/nlab/show/MonCat
 Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

 Given monoidal categories (C, ⊗_C, I_C) and (D, ⊗_D, I_D), the product
 category C ∏ D carries the pointwise monoidal structure:

 tensor:  (c, d) ⊗ (c', d')  =  (c ⊗_C c', d ⊗_D d')
 unit:    I                  =  (I_C, I_D)

 The associator and the left/right unitors act componentwise, pairing the
 corresponding isomorphism from C with the one from D; likewise their
 naturality squares. The triangle and pentagon coherence laws hold in C ∏ D
 because they already hold in each factor and equivalence in C ∏ D is the
 componentwise conjunction (see Construction.Product). This construction is
 the cartesian product in the (2-)category MonCat of monoidal categories.

 Note: this is the *product* monoidal structure (a pointwise tensor built
 from two given monoidal structures), not the *cartesian* monoidal structure
 (tensor = categorical product, unit = terminal object), which is a distinct
 notion. 

 --------
 nLab: https://ncatlab.org/nlab/show/monoidal+category
 nLab: https://ncatlab.org/nlab/show/MonCat
 Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

 给定幺半群范畴 (C, ⊗_C, I_C) 和 (D, ⊗_D, I_D)，它们的积范畴 C ∏ D 具有逐点幺半群结构：

 张量: (c, d) ⊗ (c', d') = (c ⊗_C c', d ⊗_D d')
 单位: I = (I_C, I_D)

 结合子和左/右单位子在每个分量上作用，将 C 的对应同构与 D 的对应同构配对；它们的自然性方形也同样如此。三角形和五边形的相容律在 C ∏ D 中成立，因为它们已经在每个因子中成立，并且 C ∏ D 中的等价是逐分量的结合（参见 Construction.Product）。这个构造是在幺半群范畴 MonCat（2-范畴）中的笛卡尔积。注意：这是*乘积*单范畴结构（一个基于两个给定单范畴结构构建的逐点张量），而不是*笛卡尔*单范畴结构（张量 = 范畴积，单位 = 终对象），这是一个不同的概念。
*)

#[local] Obligation Tactic := simpl; intros; simplify; simpl in *.

#[export]
Program Instance Product_Monoidal `{@Monoidal C} `{@Monoidal D} :
  @Monoidal (C ∏ D) := {
  tensor :=
    {| fobj := fun p => (fst (fst p) ⨂ fst (snd p),
                         snd (fst p) ⨂ snd (snd p))%object
     ; fmap := fun _ _ f => (fst (fst f) ⨂ fst (snd f),
                             snd (fst f) ⨂ snd (snd f)) |};
  I := (@I C _, @I D _)
}.
Next Obligation. exact H. Defined.
Next Obligation. exact H0. Defined.
Next Obligation.
  proper; simplify; simpl in *;
  rewrites; reflexivity.
Qed.
Next Obligation. all:normal; reflexivity. Qed.
Next Obligation. all:apply bimap_comp. Qed.
Next Obligation.
  isomorphism; simpl; simplify; simpl.
  - apply unit_left.
  - apply unit_left.
  - apply (unit_left⁻¹).
  - apply (unit_left⁻¹).
  - apply iso_to_from.
  - apply iso_to_from.
  - apply iso_from_to.
  - apply iso_from_to.
Defined.
Next Obligation.
  isomorphism; simpl; simplify; simpl.
  - apply unit_right.
  - apply unit_right.
  - apply (unit_right⁻¹).
  - apply (unit_right⁻¹).
  - apply iso_to_from.
  - apply iso_to_from.
  - apply iso_from_to.
  - apply iso_from_to.
Defined.
Next Obligation.
  isomorphism; simpl; simplify; simpl.
  - apply tensor_assoc.
  - apply tensor_assoc.
  - apply (tensor_assoc⁻¹).
  - apply (tensor_assoc⁻¹).
  - apply iso_to_from.
  - apply iso_to_from.
  - apply iso_from_to.
  - apply iso_from_to.
Defined.
Next Obligation. all:apply to_unit_left_natural. Qed.
Next Obligation. all:apply from_unit_left_natural. Qed.
Next Obligation. all:apply to_unit_right_natural. Qed.
Next Obligation. all:apply from_unit_right_natural. Qed.
Next Obligation. all:apply to_tensor_assoc_natural. Qed.
Next Obligation. all:apply from_tensor_assoc_natural. Qed.
Next Obligation. all:apply triangle_identity. Qed.
Next Obligation. all:apply pentagon_identity. Qed.
