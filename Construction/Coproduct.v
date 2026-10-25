Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** The coproduct (disjoint union) of two categories. / 两个范畴的余积（不相交并集）。 *)

(*
 nLab: https://ncatlab.org/nlab/show/coproduct
 Wikipedia: https://en.wikipedia.org/wiki/Coproduct

 The coproduct category C ∐ D has as objects the tagged disjoint union of the
 objects of C and D, an object being either inl c with c : C or inr d with
 d : D. Morphisms exist only within a single summand: a hom inl c ~> inl c'
 is a morphism c ~> c' in C, a hom inr d ~> inr d' is a morphism d ~> d' in
 D, and the hom-set between objects of different summands is empty (encoded
 here as False). Identity and composition are inherited from whichever
 summand the objects live in, and equivalence of morphisms is the ≈ of that
 summand. The unit and associativity laws hold because they hold in each
 summand.

 This is the coproduct in Cat, the category of categories: the inclusion
 functors C ⟶ C ∐ D and D ⟶ C ∐ D exhibit C ∐ D as the categorical coproduct
 of C and D, so a functor C ∐ D ⟶ E is the same as a pair of functors C ⟶ E
 and D ⟶ E. This is the coproduct *of categories*, and is distinct from a
 coproduct *object* inside a single category, formed via a universal cocone
 in Structure/Cocartesian.v. 

 --------
 nLab：https://ncatlab.org/nlab/show/coproduct
 Wikipedia：https://en.wikipedia.org/wiki/Coproduct

 余积范畴 C ∐ D 的对象是 C 和 D 对象的带标签的离散并集，一个对象要么是 inl c，其中 c ：C，要么是 inr d，其中 d ：D。态射只存在于单个子集内：inl c ~> inl c' 是 C 中的态射 c ~> c'，inr d ~> inr d' 是 D 中的态射 d ~> d'，而来自不同子集对象之间的态射集为空（这里编码为 False）。恒等态射和复合从对象所在的子集中继承，并且态射的等价性是该子集的 ≈。单位律和结合律成立，因为它们在每个子集中都成立。这是 Cat 中的余积，即范畴的范畴：包含函子 C ⟶ C ∐ D 和 D ⟶ C ∐ D 将 C ∐ D 显示为 C 和 D 的范畴余积，因此函子 C ∐ D ⟶ E 与一对函子 C ⟶ E 和 D ⟶ E 是相同的。这是 *范畴* 的余积，与单个范畴内部通过 Structure/Cocartesian.v 中的通用余锥形成的 *对象* 余积不同。
*)

Section Coproduct.

Context {C : Category}.
Context {D : Category}.

Local Set Warnings "-intuition-auto-with-star".

(*
   【Coproduct 范畴定义展开】/ Coproduct walkthrough
   （口吻对齐 Theory/Category.v；受众：Coq 小白 + 范畴论小白的 Haskell 程序员）

   1) 这是什么 / What this is
      Coproduct C D = C ∐ D：对象是带标签并 C + D（inl / inr）；
      态射只活在同一侧，跨侧 Hom 是 False（空）。
      Tagged disjoint union of categories; no arrows between summands.
      Haskell 对照：Either a b —— 但这里两侧各自带着自己的态射。
      Haskell: Either, but each side keeps its own morphisms.

   2) 关键字段 / Key fields
      - obj := C + D
      - hom：match 两侧；同侧用原 Hom，异侧 False
      - id / compose：按所在侧继承；≈ 也是该侧的 ≈

   3) 与积的对比 / vs Product
      积 = Cat 的笛卡尔积；余积 = Cat 的余积。
      函子 C ∐ D ⟶ E ≃ 一对 C ⟶ E 与 D ⟶ E（像 case 分析）。
      Maps *out* of a coproduct are pairs of maps (like case).
      对象余积在 Structure/Cocartesian.v，勿混。

   阅读：inl/inr → 同侧 Hom → False 跨侧 → 侧内定律。
   Read: tags → within-summand homs → False across → laws per side.
*)

Program Definition Coproduct : Category := {|
  obj     := C + D;            (* tagged disjoint union of objects / 带标签的对象不相交并集 *)
  hom     := fun x y =>        (* within a summand; False across summands / 在同一项内；在各项之间为假 *)
               match x return Type with
               | Datatypes.inl x =>
                 match y with
                 | Datatypes.inl y => x ~> y
                 | Datatypes.inr _ => False
                 end
               | Datatypes.inr x =>
                 match y with
                 | Datatypes.inl _ => False
                 | Datatypes.inr y => x ~> y
                 end
               end;
  homset  := fun x y => {| equiv := fun f g => _ |};
  id      := fun x =>
               match x with
               | Datatypes.inl x => id
               | Datatypes.inr x => id
               end;
  compose := fun _ _ _ f g => _
|}.
Next Obligation.
  destruct x.
  - destruct y.
    + exact (f ≈ g).
    + contradiction.
  - destruct y.
    + contradiction.
    + exact (f ≈ g).
Defined.
Next Obligation.
  equivalence;
  destruct x, y; simpl; intuition;
  unfold Coproduct_obligation_1 in *;
  intuition; auto with *.
Qed.
Next Obligation.
  repeat match goal with [ H : _ + _ |- _ ] => destruct H end;
  intuition; exact (f ∘ g).
Defined.
Next Obligation.
  proper.
  destruct x, y, z;
  unfold Coproduct_obligation_1 in *;
  unfold Coproduct_obligation_3 in *;
  intuition; auto with *.
Qed.
Next Obligation.
  destruct x, y;
  unfold Coproduct_obligation_1 in *;
  unfold Coproduct_obligation_3 in *;
  intuition; cat.
Qed.
Next Obligation.
  destruct x, y;
  unfold Coproduct_obligation_1 in *;
  unfold Coproduct_obligation_3 in *;
  intuition; cat.
Qed.
Next Obligation.
  destruct x, y, z, w;
  unfold Coproduct_obligation_1 in *;
  unfold Coproduct_obligation_3 in *;
  intuition; cat.
Qed.
Next Obligation.
  destruct x, y, z, w;
  unfold Coproduct_obligation_1 in *;
  unfold Coproduct_obligation_3 in *;
  intuition; cat.
Qed.

End Coproduct.

Notation "C ∐ D" := (@Coproduct C D) (at level 90) : category_scope.
