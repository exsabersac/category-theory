Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(* * * The thin category of a preorder (proset) / * * 预序（前序集）的稀薄类别 *)

(*
 nLab: https://ncatlab.org/nlab/show/preorder
 nLab: https://ncatlab.org/nlab/show/thin+category
 Wikipedia: https://en.wikipedia.org/wiki/Preorder

 Any preordered set (a "proset": a set [A] with a reflexive and transitive
 relation [R], not necessarily antisymmetric) forms a category. Its objects
 are the elements of [A], and there is a (unique) morphism [x ~> y] exactly
 when [R x y] holds: identities come from reflexivity and composition from
 transitivity. See Instance/Pos.v for [Pos], the category whose
 objects are posets, and Instance/Ord.v for [Ord], the category whose
 objects are ALL preorders (Mac Lane's Preord, #372).  #786, the
 preorder/Bool-category equivalence, is still open; it should consume
 that [Ord] rather than build one.

 Because antisymmetry is not required, distinct objects [x] and [y] may be
 isomorphic (when both [R x y] and [R y x] hold) without being equal; this
 is precisely what distinguishes a proset from a poset (see Instance/Poset.v,
 which adds antisymmetry). The resulting category is "thin": any two parallel
 morphisms are equal, so each hom-set has at most one element.

 Wikipedia: "A category with at most one morphism from any object X to any
 other object Y is a preorder. Such categories are called thin. In this
 sense, categories 'generalize' preorders by allowing more than one relation
 between objects: each morphism is a distinct (named) preorder relation." 

 --------
 nLab:  https://ncatlab.org/nlab/show/preorder 
 nLab:  https://ncatlab.org/nlab/show/thin+category 
 Wikipedia:  https://en.wikipedia.org/wiki/Preorder 

 任意预序集（一个“proset”：集合 [A] 具有自反且传递的关系 [R] ，不一定是反对称的）形成一个范畴。它的对象是 [A] 的元素，并且当且仅当 [R x y] 成立时存在（唯一的）态射 [x ~> y] ：恒等态射来自自反性，复合来自传递性。参见 Instance/Pos.v 了解 [Pos] ，其对象是偏序集，以及 Instance/Ord.v 了解 [Ord] ，其对象是所有预序集（Mac Lane 的 Preord，#372）。 #786，即预序/布尔范畴等价，仍未解决；它应该使用 [Ord] 而不是重新构建一个。因为不要求反对称性，不同的对象 [x] 和 [y] 可能是同构的（当 [R x y] 和 [R y x] 都成立时），但并不相等；这正是区分前序集（proset）和偏序集（poset）的关键（参见 Instance/Poset.v，它添加了反对称性）。由此产生的范畴是“稀薄的”：任意两条平行态射都是相等的，因此每个 Hom 集最多只有一个元素。

 维基百科：“从任意对象 X 到任意其他对象 Y 至多只有一个态射的范畴是前序。这样的范畴被称为稀薄范畴。从这个意义上说，范畴‘推广’了前序，通过允许对象之间存在多个关系：每个态射都是一个独特的（有名的）前序关系。”
*)

(*
   【Proset 范畴实例展开】/ Proset instance walkthrough
   （口吻对齐 Theory/Functor.v；受众：Coq 小白 + Haskell）

   1) 这是什么 / What this is
      Proset P 把预序 (A,R) 变成薄范畴：对象=元素；x~>y 当且仅当 R x y（至多一条箭）。
      Thin category of a preorder: at most one arrow x→y, namely the fact R x y.
      id=自反；compose=传递。不必反对称 → 互≤可同构但不相等（区别于 Poset）。
      id=refl; compose=trans. Without antisym, mutual ≤ ⇒ iso ≠ equality.

   2) 关键字段 / Key fields
      - obj := A；hom := R
      - homset.equiv := True（任意两平行箭视为相等 → 薄）
      - id := reflexivity；compose := transitivity（注意顺序 g 然后 f）

   Haskell 对照：像「证明无关的约束」——只有是否成立，没有多名箭头。
   Analogy: proof-irrelevant constraints; presence/absence only.

   阅读：Proset 记录 → LessThanEqualTo_Category 例子 → 再看 Poset.v。
   Read: Proset → ≤ example → then Poset.v.
*)
Program Definition Proset {A : Type} {R : relation A} (P : PreOrder R) :
  Category := {|
  obj     := A;
  hom     := R;
  (*
 Since there can be at most one arrow between any two objects, multiple
 arrows of the same type are equal. 

 --------
 由于任意两个对象之间最多只能有一条箭头，所以同类型的多条箭头是相等的。
*)
  homset  := fun A B => {| Setoid.equiv := fun _ _ => True |};
  id      := fun x => @reflexivity A R (@PreOrder_Reflexive A R P) x;
  compose := fun x y z f g =>
    @transitivity A R (@PreOrder_Transitive A R P) x y z g f
|}.

(* The typical example found in Category Theory theories and lectures is ≤. / 在范畴论的理论和讲座中，典型的例子是 ≤。 *)

Definition LessThanEqualTo_Category : Category :=
  @Proset nat PeanoNat.Nat.le PeanoNat.Nat.le_preorder.
