Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Product.Internal.
Require Import Category.Structure.Cartesian.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * The diagonal–product adjunction Δ ⊣ ×  / * 对角积加法 Δ ⊣ ×*)

(*
nLab: https://ncatlab.org/nlab/show/diagonal+functor
   Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)

   In a cartesian category C the binary product functor ×(C) : C ∏ C ⟶ C is
   right adjoint to the binary diagonal Δ = Diagonal_Product C : C ⟶ C ∏ C
   (so that, dually, the coproduct is left adjoint to Δ -- that dual half is
   Adjunction/Diagonal/Coproduct.v's [Diagonal_Coproduct_Adjunction]): nLab
   records that
   “C is J-cocomplete (J-complete) iff Δ has a left (right) adjoint”, and the
   two-object discrete case is exactly the binary product/coproduct. The
   adjunction is presented here in hom-set form, as the family of bijections

       (Δ x ~{C ∏ C}~> p)  ≅  (x ~{C}~> ×(C) p)

   natural in x : C and p : C ∏ C. Spelling out the left side: a morphism
   Δ x ~> p is a pair (f, g) with f : x ~> fst p and g : x ~> snd p, while the
   right side is a single arrow x ~> fst p × snd p. The forward transpose
   [to] pairs the components, (f, g) ↦ f △ g, and the inverse [from] splits an
   arrow by postcomposing with the projections, h ↦ (exl ∘ h, exr ∘ h). That
   these are mutually inverse and natural is precisely the universal property
   of the product (the [fork]/projection laws of Structure/Cartesian.v), which
   is why the obligations below discharge by [unfork] and [fork_comp]. 

--------
nLab：https://ncatlab.org/nlab/show/diagonal+functor
 维基百科：https://en.wikipedia.org/wiki/Product_(category_theory)

在笛卡尔范畴 C 中，二元积函子 ×(C) : C ∏ C ⟶ C 是
 二进制对角线的右伴随 Δ = Diagonal_Product C : C ⟶ C ∏ C
 （因此，对偶而言，余积与 Δ 相连——对偶一半是
 Adjunction/Diagonal/Coproduct.v 的 [Diagonal_Coproduct_Adjunction])：nLab
 记录了
 “C 是 J-余完备（J-完备）当且仅当 Δ 有左（右）伴随”，并且
 双对象离散情况正是二元积/余积。 的
 附加在这里以 hom-set 形式呈现，作为双射族

(Δ x ~{C ∏ C}~> p) ≅ (x ~{C}~> ×(C) p)

x : C 和 p : C ∏ C 中的自然数。 拼出左侧：态射
 Δ x ~> p 是一对 (f, g)，其中 f : x ~> fst p 和 g : x ~> snd p，而
 右侧是一个单箭头 x ~> fst p × snd p。 前向转置
 [to] 将分量 (f, g) ↦ f △ g 配对，而逆 [from] 将
 与投影 h ↦ (exl ∘ h, exr ∘ h) 进行后合成的箭头。 那
 这些是互逆的，自然的正是普遍属性
 产品的（[fork]/Structure/Cartesian.v 的投影定律），其中
 这就是 [unfork] 和 [fork_comp] 履行以下义务的原因。 
*)

#[export]
Program Instance Diagonal_Product_Adjunction (C : Category) `{@Cartesian C} :
  Diagonal_Product C ⊣ ×(C) := {
  adj := fun _ _ =>
    {| to   := {| morphism := fun f => fst f △ snd f |}
     ; from := {| morphism := fun f => (exl ∘ f, exr ∘ f) |} |}
}.
Next Obligation. proper; apply fork_respects; auto. Qed.
Next Obligation. rewrite fork_comp; cat. Qed.
Next Obligation. unfork. Qed.
Next Obligation. unfork. Qed.
Next Obligation. split; unfork. Qed.
