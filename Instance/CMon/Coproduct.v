Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Biproduct.Cartesian.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.

Generalizable All Variables.

(* * * The direct sum is the coproduct in CMon / * * 直和是 CMon 中的余积 *)

(*
 Book: Mac Lane, "Categories for the Working Mathematician" (2nd ed.),
 §III.3, book p. 63 (maclane:III.3:remark1)
 Wikipedia: https://en.wikipedia.org/wiki/Biproduct

 Instance/CMon/Biproduct.v proved
 that the direct product of two commutative monoids is at once their
 product and their coproduct — [CMon_bi_is_product] and
 [CMon_bi_is_coproduct] at Instance/CMon/Biproduct.v, both
 in the ∃!-form, packaged as [CMon_Biproducts].  What it never did was
 say so in the vocabulary the rest of the library uses: there was no
 [Cartesian CMon] and no [Cocartesian CMon] anywhere.

 This file is that sentence, and it is DELIVERED WITH NO NEW PROOF AT
 ALL — two lines, both supplied by
 [:=], the whole content coming from Structure/Biproduct/Cartesian.v's
 generic bridge applied to the existing [CMon_Biproducts].  It is
 included because it is the bridge's cleanest demonstration: the
 donor's biproduct was already complete, so what the bridge adds is
 exactly and only the vocabulary.

 Instance/Ab/Coproduct.v and Instance/Mod/Coproduct.v are the same
 statement one and two layers up, where the donor's biproduct does NOT
 already exist and must be built; the three files together are Mac
 Lane's "direct sum" roster entry.

 WHAT IS NOT DELIVERED.  Nothing beyond the repackaging: no indexed
 coproducts, no [Additive CMon] (there are no inverses — that is what
 Instance/Ab.v adds), and no claim that the coproduct injections are
 monic. 

 --------
 书籍：Mac Lane，《给工作的数学家的范畴论》（第2版），§III.3，第63页（maclane:III.3:remark1）
 维基百科：https://en.wikipedia.org/wiki/Biproduct

 Instance/CMon/Biproduct.v 证明了两个交换幺半群的直积同时是它们的积和余积——[CMon_bi_is_product] 和 [CMon_bi_is_coproduct] 在 Instance/CMon/Biproduct.v 中，都以 ∃!-形式表达，并打包为 [CMon_Biproducts]。它从未用库中其他部分使用的词汇来说：在任何地方都没有 [Cartesian CMon]，也没有 [Cocartesian CMon]。这个文件就是那句话，而且它完全没有提供新的证明——两行内容，都是由 [:=] 提供的，全部内容来自 Structure/Biproduct/Cartesian.v 的通用桥应用到现有的 [CMon_Biproducts] 上。它被包含进来是因为它是这个桥最清晰的演示：捐赠者的积已经完整，所以桥所添加的正是且仅是词汇。

 Instance/Ab/Coproduct.v 和 Instance/Mod/Coproduct.v 是相同的陈述，只是层级高一到两层，在这种情况下捐赠者的积尚不存在，必须构建；这三个文件一起构成了 Mac Lane 的“直和”的名录条目。未交付的内容。 除了重新包装之外没有其他内容：没有索引的余积，没有 [Additive CMon]（没有逆——这正是 Instance/Ab.v 添加的内容），并且没有声明余积注入是单射。
*)

#[export] Instance CMon_Cartesian : @Cartesian CMon :=
  @biproduct_Cartesian CMon CMon_Zero CMon_Biproducts.

#[export] Instance CMon_Cocartesian : @Cocartesian CMon :=
  @biproduct_Cocartesian CMon CMon_Zero CMon_Biproducts.

(** ** Strict identifications / ** 严格识别 *)

(* The coproduct IS the product, the same object. / 余积就是积，同一个对象。 *)
Example CMon_coprod_is_prod (M N : CMonObject) :
  @Coprod CMon CMon_Cocartesian M N
    = @product_obj CMon CMon_Cartesian M N := eq_refl.

Example CMon_coprod_obj (M N : CMonObject) :
  @Coprod CMon CMon_Cocartesian M N = CMon_product M N := eq_refl.

Example CMon_inl_is_CMon_inl (M N : CMonObject) :
  @inl CMon CMon_Cocartesian M N = CMon_inl M N := eq_refl.

Example CMon_inr_is_CMon_inr (M N : CMonObject) :
  @inr CMon CMon_Cocartesian M N = CMon_inr M N := eq_refl.

Example CMon_merge_is_copair (M N P : CMonObject)
  (f : M ~{CMon}~> P) (g : N ~{CMon}~> P) :
  @merge CMon CMon_Cocartesian P M N f g = CMon_copair f g := eq_refl.

Example CMon_exl_is_CMon_exl (M N : CMonObject) :
  @exl CMon CMon_Cartesian M N = CMon_exl M N := eq_refl.

Example CMon_exr_is_CMon_exr (M N : CMonObject) :
  @exr CMon CMon_Cartesian M N = CMon_exr M N := eq_refl.
