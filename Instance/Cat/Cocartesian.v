Require Import Category.Lib.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Coproduct.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** Cat has finite coproducts: the coproduct of two categories. / 类具有有限余积：两个范畴的余积。 *)

(*
 nLab:      https://ncatlab.org/nlab/show/Cat
 nLab:      https://ncatlab.org/nlab/show/coproduct
 Wikipedia: https://en.wikipedia.org/wiki/Coproduct

 Cat has finite coproducts. The coproduct of two categories C and D is the
 disjoint-union (coproduct) category C ∐ D of Construction/Coproduct.v, and
 here it is exhibited as the categorical coproduct in Cat:

 product_obj := C ∐ D    (the coproduct object, read in Cat^op)
 exl         := Inl       (inclusion functor C ⟶ C ∐ D)
 exr         := Inr       (inclusion functor D ⟶ C ∐ D)
 fork F G    := [F, G]    (copairing / case functor C ∐ D ⟶ E)

 Because [Cocartesian C] is by definition [Cartesian (C^op)] (a coproduct in
 C is a product in C^op, dualizing all arrows), this instance is literally a
 proof that Cat^op is Cartesian: the product fields of Cat^op are the
 coproduct fields of Cat, and [ump_products] read in Cat^op is the universal
 property of the coproduct -- a functor C ∐ D ⟶ E is uniquely the case
 functor [F, G] of a pair of functors F : C ⟶ E and G : D ⟶ E.

 The copairing's action on a hom is forced by the disjoint union: within a
 summand it runs F (resp. G), and the cross-summand hom-sets are empty (False
 in Construction/Coproduct.v), discharged here by [False_rect].

 The nullary coproduct, the initial object of Cat, is the empty category 0
 (Instance/Zero.v); it is supplied separately by [Initial] and is not a field
 of this binary-coproduct class. 

 --------
 nLab:       https://ncatlab.org/nlab/show/Cat 
 nLab:       https://ncatlab.org/nlab/show/coproduct 
 Wikipedia:  https://en.wikipedia.org/wiki/Coproduct 

 Cat 具有有限余积。两个范畴 C 和 D 的余积是 Construction/Coproduct.v 中的不相交并（余积）范畴 C ∐ D，这里它被展示为 Cat 中的范畴余积：

 product_obj := C ∐ D    （余积对象，在 Cat^op 中读取）
 exl         := Inl       （包含函子 C ⟶ C ∐ D）
 exr         := Inr       （包含函子 D ⟶ C ∐ D）
 fork F G    :=  [F, G]     （配对 / 情况函子 C ∐ D ⟶ E）因为 [Cocartesian C] 按定义是 [Cartesian (C^op)]（C 中的余积在 C^op 中是积，对所有箭头取对偶），所以这个实例实际上是一个证明 Cat^op 是笛卡尔积的例子：Cat^op 的积字段是 Cat 的余积字段，并且在 Cat^op 中阅读 [ump_products] 就是余积的泛性质——函子 C ∐ D ⟶ E 唯一地对应于一对函子 F : C ⟶ E 和 G : D ⟶ E 的情况函子 [F, G]。

 余对的在 Hom 上的作用是由不相交并迫出的：在每个加数中它运行 F（分别是 G），而跨加数的 Hom 集为空（Construction/Coproduct.v 中为 False），在这里由 [False_rect] 解决。

 零元余积，即 Cat 的初始对象，是空范畴 0（Instance/Zero.v）；它由 [Initial] 单独提供，并且不是这个二元余积类的一个字段。
*)

#[export]
Program Instance Cat_Cocartesian : @Cocartesian Cat := {
  product_obj := @Coproduct;
  fork := fun _ _ _ F G =>
    {| fobj := fun x =>
                 match x with
                 | Datatypes.inl x => F x
                 | Datatypes.inr x => G x
                 end
     ; fmap := fun x y f =>
                 match x with
                 | Datatypes.inl x =>
                   match y with
                   | Datatypes.inl y => _
                   | Datatypes.inr y => False_rect _ _
                   end
                 | Datatypes.inr x =>
                   match y with
                   | Datatypes.inl y => False_rect _ _
                   | Datatypes.inr y => _
                   end
                 end |};
  exl := fun _ _ =>
            {| fobj := Datatypes.inl
             ; fmap := fun _ _ => _ |};
  exr := fun _ _ =>
            {| fobj := Datatypes.inr
             ; fmap := fun _ _ => _ |};
}.
Next Obligation. exact (fmap f). Defined.
Next Obligation. exact (fmap f). Defined.
Next Obligation.
  proper.
  destruct x, y; simpl in *;
  solve [ apply fmap_respects; auto | contradiction ].
Qed.
Next Obligation.
  destruct x; simpl in *; cat.
Qed.
Next Obligation.
  destruct x, y, z; simpl in *; try tauto;
  apply fmap_comp.
Qed.
Next Obligation.
  rename x into A.
  rename y into B.
  rename z into C.
  proper.
  destruct x3, y1; simpl; auto; tauto.
Qed.
Next Obligation.
  rename x into A.
  rename y into B.
  rename z into C.
  split; intros; simplify.
  - apply (e (Datatypes.inl x0) (Datatypes.inl y)).
  - apply (e (Datatypes.inr x0) (Datatypes.inr y)).
  - destruct x1; auto.
  - destruct x1, y.
    + apply e0; tauto.
    + tauto.
    + tauto.
    + apply e; tauto.
Qed.
