Require Import Category.Lib.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Cartesian.

Generalizable All Variables.

(* * * Cartesian (binary product) structure on [Sets] / * * [Sets] 上的笛卡尔（乘积）结构 *)

(*
 nLab: https://ncatlab.org/nlab/show/product
 nLab: https://ncatlab.org/nlab/show/setoid
 Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)

 The category [Sets] of setoids has binary products, computed as the
 product setoid. The product of two setoids x and y has

 carrier:  carrier x * carrier y     (the type of ordered pairs)
 ≈:  (a₁, b₁) ≈ (a₂, b₂)  :=  a₁ ≈ a₂  ∧  b₁ ≈ b₂

 i.e. the carrier is the product type and equivalence is componentwise (the
 `*` joining the two [equiv] proofs is conjunction, the product in [Type]).
 This is the standard product in Set, refined to setoids so that the
 componentwise relation is again an equivalence.

 The two projections [exl], [exr] are the underlying [fst], [snd] (which
 respect `≈` by definition of the componentwise relation), and the pairing
 ⟨f, g⟩ ([fork]) of f : x ~> y and g : x ~> z is x ↦ (f x, g x). These
 satisfy the universal mapping property of [Cartesian]: ⟨f, g⟩ is the unique
 map h with exl ∘ h ≈ f and exr ∘ h ≈ g, since equivalence of pairs is exactly
 componentwise equivalence. 

 --------
 nLab:  https://ncatlab.org/nlab/show/product 
 nLab:  https://ncatlab.org/nlab/show/setoid 
 维基百科:  https://en.wikipedia.org/wiki/Product_(category_theory) 

 集合同构范畴  [Sets] 有二元积，可以算作积集合同构。两个集合同构 x 和 y 的积具有

 载体:  carrier x * carrier y     （有序对的类型）
 ≈:  (a₁, b₁) ≈ (a₂, b₂)  :=  a₁ ≈ a₂  ∧  b₁ ≈ b₂

 即载体是积类型，等价关系是分量逐一的（将两个  [equiv]  证明连接的  `*` 是合取，在  [Type] 中是积）。
 这是 Set 中的标准积，经过精炼以适用于集合同构，使得分量关系仍然是等价关系。两个投影 [exl]、[exr] 是基础的 [fst]、[snd]（根据分量关系的定义，它们遵守 `≈`），而 f : x ~> y 和 g : x ~> z 的配对 ⟨f, g⟩（[fork]）是 x ↦ (f x, g x)。它们满足 [Cartesian] 的泛映射性质：⟨f, g⟩ 是唯一的映射 h，使得 exl ∘ h ≈ f 且 exr ∘ h ≈ g，因为对偶的等价恰好是分量的等价。
*)

#[export]
Program Instance Sets_Cartesian : @Cartesian Sets := {
  product_obj := fun x y =>
    {| carrier := (carrier x * carrier y)%type
     ; is_setoid :=
         {| equiv := fun z w =>
                       @equiv _ x (fst z) (fst w) *
                       @equiv _ y (snd z) (snd w)
          ; setoid_equiv := _
          |} |};
  fork := fun _ _ _ f g => {| morphism := fun x => (f x, g x) |};
  exl := fun _ _ => {| morphism := fst |};
  exr := fun _ _ => {| morphism := snd |}
}.
Next Obligation. proper; apply proper_morphism; assumption. Qed.
Next Obligation. all:firstorder. Qed.
