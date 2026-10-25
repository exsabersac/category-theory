Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Hom.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Profunctor.

Generalizable All Variables.

(** Representable profunctors versus adjunctions. / 可表示的双函子与伴随关系。 *)

(*
nLab: https://ncatlab.org/nlab/show/profunctor
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   An adjunction is exactly a natural isomorphism of representable profunctors.
   For F : D ⟶ C and U : C ⟶ D (the library orients F ⊣ U with F the left
   adjoint D ⟶ C and U the right adjoint C ⟶ D), the two representable
   profunctors of Theory/Profunctor.v are

     Repr_left F  : D ⇸ C,   (d, c) ↦ C(F d, c),
     Repr_right U : D ⇸ C,   (d, c) ↦ D(d, U c),

   both objects of the profunctor category [D^op ∏ C, Sets]. An adjunction
   F ⊣ U is precisely a natural isomorphism Repr_left F ≅ Repr_right U in that
   category: this is the hom-set (transpose) form of an adjunction.

   The witnessing isomorphism is literally the hom-bifunctor isomorphism hom_adj
   of Adjunction/Hom.v, whose two sides Hom C ◯ (F^op ∏⟶ Id) and
   Hom D ◯ (Id^op ∏⟶ U) are definitionally Repr_left F and Repr_right U. So
   this file is a repackaging, through the profunctor vocabulary, of the two
   conversions already established there — Adjunction_Universal_to_Hom (from the
   universal-property adjunction Theory/Adjunction.v to the hom-iso form) and
   Adjunction_Hom_to_Universal (back) — bundled into the Type-valued iff
   representable_adjunction. Both directions are genuine, so the iff holds at
   full strength; nothing here is a one-way implication.

--------
nLab：https://ncatlab.org/nlab/show/profunctor
维基百科：https://en.wikipedia.org/wiki/Adjoint_functors

一个伴随正是可表示的概型函子之间的自然同构。对于 F : D ⟶ C 和 U : C ⟶ D（库将 F ⊣ U 定向为 F 是左伴随 D ⟶ C，U 是右伴随 C ⟶ D），Theory/Profunctor.v 中的两个可表示概型函子是

Repr_left F  : D ⇸ C,   (d, c) ↦ C(F d, c),
Repr_right U : D ⇸ C,   (d, c) ↦ D(d, U c),

profunctor 范畴 [D^op ∏ C, Sets] 的两个对象。一个伴随关系 F ⊣ U 恰好是在该范畴中 Repr_left F ≅ Repr_right U 的自然同构：这是伴随关系的同态集（转置）形式。

见证同构实际上是伴随/Hom.v 中的同余函子同构 hom_adj，其两边 Hom C ◯ (F^op ∏⟶ Id) 和 Hom D ◯ (Id^op ∏⟶ U) 在定义上分别是 Repr_left F 和 Repr_right U。所以这个文件是通过拟函子(profunctor)的词汇，对那里已经建立的两种转换——Adjunction_Universal_to_Hom（从范畴论/伴随中的通用性质伴随 Theory/Adjunction.v 到同余同构形式）和 Adjunction_Hom_to_Universal（返回）——进行重新打包，并捆绑到取值为类型的 iff representable_adjunction 中。两个方向都是实在的，因此 iff 在完全意义上成立；这里没有任何是单向蕴含。
*)

Section RepresentableAdjunction.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

(*
Forward direction: an adjunction F ⊣ U transposes to a natural isomorphism of
   the representable profunctors. Concretely we route the universal-property
   adjunction through Adjunction_Universal_to_Hom to obtain the hom-bifunctor
   isomorphism hom_adj, whose endpoints are Repr_left F and Repr_right U.

--------
正向方向：一个伴随 F ⊣ U 对应于可表示的拟函子之间的自然同构。具体地，我们通过 Adjunction_Universal_to_Hom 将普遍性质的伴随映射，以得到同态双函子同构 hom_adj，其端点是 Repr_left F 和 Repr_right U。
*)
Definition adjunction_to_repr_iso (A : F ⊣ U) :
  Repr_left F ≅[[D^op ∏ C, Sets]] Repr_right U :=
  @hom_adj C D F U (@Adjunction_Universal_to_Hom C D F U A).

(*
Reverse direction: a natural isomorphism Repr_left F ≅ Repr_right U is exactly
   the datum of an Adjunction_Hom (its hom_adj field), which converts back to a
   universal-property adjunction through Adjunction_Hom_to_Universal.

--------
反方向：一个自然同构 Repr_left F ≅ Repr_right U 恰好是 Adjunction_Hom 的数据（它的 hom_adj 字段），该数据通过 Adjunction_Hom_to_Universal 转换回一个具有泛性质的余adjunction。
*)
Definition repr_iso_to_adjunction
  (iso : Repr_left F ≅[[D^op ∏ C, Sets]] Repr_right U) : F ⊣ U :=
  @Adjunction_Hom_to_Universal C D F U {| hom_adj := iso |}.

(*
The representability criterion for adjunctions as a Type-valued iff (↔ is
   iffT here), bundling the two conversions above.

--------
作为类型值的伴随的可表示性标准即iff（↔在这里是iffT），将上述两个转换捆绑在一起。
*)
Definition representable_adjunction :
  (F ⊣ U) ↔ (Repr_left F ≅[[D^op ∏ C, Sets]] Repr_right U) :=
  (adjunction_to_repr_iso, repr_iso_to_adjunction).

End RepresentableAdjunction.
