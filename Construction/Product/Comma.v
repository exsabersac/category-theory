Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Product.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.

Generalizable All Variables.

(*
   * The comma category over the terminal category is the product category. 

   --------
   * 终端范畴上的逗号范畴是积范畴。
*)

(*
 nLab: https://ncatlab.org/nlab/show/comma+category
 nLab: https://ncatlab.org/nlab/show/product+category
 Wikipedia: https://en.wikipedia.org/wiki/Comma_category
 Wikipedia: https://en.wikipedia.org/wiki/Product_category

 For any functors F : C ⟶ 1 and G : D ⟶ 1 into the terminal category 1, the
 comma category (F ↓ G) is isomorphic in Cat to the product category C ∏ D:

 (F ↓ G) ≅[Cat] C ∏ D.

 An object of (F ↓ G) is a triple (c, d, h : F c ~> G d), but since 1 is
 terminal its only hom-set is the singleton poly_unit, so the mediating
 morphism h is forced and carries no information; an object is thus a pair
 (c, d). A morphism (c, d, h) ~> (c', d', h') is a pair (f, g) subject to the
 commuting square h' ∘ F f ≈ G g ∘ h, but that square lives in 1 where all
 morphisms are equal, so the condition is vacuous and a morphism is just a
 pair (f, g). Hence (F ↓ G) is exactly C ∏ D. The result does not depend on
 which F and G are chosen, only on the codomain being terminal: this is
 distinct from the special case in which the *domains* of the two functors
 are 1 (Wikipedia), where the comma category is instead the discrete category
 of morphisms between the two selected objects. 

 --------
 nLab:  https://ncatlab.org/nlab/show/comma+category 
 nLab:  https://ncatlab.org/nlab/show/product+category 
 Wikipedia:  https://en.wikipedia.org/wiki/Comma_category 
 Wikipedia:  https://en.wikipedia.org/wiki/Product_category 

 对于任意函子 F : C ⟶ 1 和 G : D ⟶ 1，目标为终结范畴 1，
 括号范畴 (F ↓ G) 在 Cat 中同构于乘积范畴 C ∏ D：

 (F ↓ G) ≅ [Cat]  C ∏ D.一个 (F ↓ G) 的对象是一个三元组 (c, d, h : F c ~> G d)，但由于 1 是终对象，它的唯一同态集合是单元素 poly_unit，所以中介态射 h 是确定的且不携带信息；因此，一个对象就是一个二元组 (c, d)。一个态射 (c, d, h) ~> (c', d', h') 是一个二元组 (f, g)，满足交换方形 h' ∘ F f ≈ G g ∘ h，但该方形位于 1 中，其中所有态射都相等，因此条件是空的，态射只是一个二元组 (f, g)。因此 (F ↓ G) 正好是 C ∏ D。这个结果不依赖于选择哪两个 F 和 G，只依赖于陪域是终对象：这与特殊情况不同，特殊情况是两个函子的*定义域*为 1（维基百科），此时逗号范畴反而是两个选定对象之间态射的离散范畴。
*)

Section ProductComma.

(*
 Build the isomorphism (and its functors, naturals, and proofs) by repeatedly
 peeling the head connective of the goal and discharging the leaf with the
 appropriate category tactic. 

 --------
 通过反复剥离目标的头部连接词，并使用适当的范畴战术消解叶子，构建同构（及其函子、自然变换和证明）。
*)
Ltac simpl_cat :=
  repeat (
    simpl; intros;
    simplify;
    simpl; intros;
    match goal with
    | [ |- _ ≅ _ ] => unshelve econstructor
    | [ |- _ ⟹ _ ] => unshelve econstructor
    | [ |- _ ⟶ _ ] => unshelve econstructor
    | [ |- @Proper _ _ _ ] => first [ abstract proper | proper ]
    | [ |- @Equivalence _ _ ] => first [ abstract equivalence | equivalence ]
    | [ |- _ ≈ _ ] => abstract cat
    | _ => cat
    end).

Theorem Comma_Product {C : Category} {D : Category}
        (F : C ⟶ 1) (G : D ⟶ 1) :
  (F ↓ G) ≅[Cat] C ∏ D.
Proof. simpl_cat. Qed.

End ProductComma.
