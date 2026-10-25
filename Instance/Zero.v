Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** The initial (empty) category 0. / 初始（空）类别 0。 *)

(*
 nLab:      https://ncatlab.org/nlab/show/empty+category
 nLab:      https://ncatlab.org/nlab/show/initial+object
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_small_categories
 Wikipedia: https://en.wikipedia.org/wiki/Initial_and_terminal_objects

 0 is the empty category: no objects and hence no morphisms.  Here the object
 type and every hom are [Empty_set], so the identity, composition, and all
 category laws hold vacuously (each obligation is discharged by [inversion] on
 the empty hypothesis); the hom-setoid is strict equality.

 0 is the initial object of Cat: for every category C there is a unique
 functor `¡ : 0 ⟶ C` ([From_0]), defined vacuously since there is nothing to
 map.  Dually, [_1] is the terminal/point category 1 (Instance/One.v). 

 --------
 nLab：       https://ncatlab.org/nlab/show/empty+category 
 nLab：       https://ncatlab.org/nlab/show/initial+object 
 维基百科：  https://en.wikipedia.org/wiki/Category_of_small_categories 
 维基百科：  https://en.wikipedia.org/wiki/Initial_and_terminal_objects 

 0 是空范畴：没有对象，因此也没有态射。这里的对象类型和每个同态集合都是 [Empty_set]，所以恒等、复合以及所有范畴律都是空值成立（每个义务都由在空假设下的 [inversion] 完成）；同态集是严格相等。

 0 是 Cat 的初始对象：对于每个范畴 C，存在唯一函子 `¡ : 0 ⟶ C`（[From_0]），由于没有任何要映射的内容，因此它是空定义的。对偶地，[_1] 是终端/点范畴 1（Instance/One.v）。
*)

#[local] Obligation Tactic :=
  intros; try match goal with [ H : Empty_set |- _ ] => inversion H end.

(*
   【0 / _0 初范畴实例展开】/ Empty category walkthrough
   （口吻对齐 Theory/Functor.v；受众：Coq 小白 + Haskell）

   1) 这是什么 / What this is
      0 = 空范畴：对象与 Hom 皆 Empty_set；定律空成立。Cat 的初对象。
      Empty category; initial object of Cat.
      函子 0⟶C 唯一（From_0，空定义）。对偶终范畴见 One.v。
      Unique ¡ : 0⟶C. Dual terminal category in One.v.

   2) 关键字段 / Key fields
      - obj/hom := Empty_set；homset := Morphism_equality
      - id/compose 等由 Obligation 对空假设 inversion 消解

   阅读：_0 → From_0 → Cat_Initial。
   Read: _0 → From_0 → Cat_Initial.
*)
Program Definition _0 : Category := {|
  obj    := Empty_set;
  hom    := fun _ _ => Empty_set;
  homset := Morphism_equality
|}.

Notation "0" := _0 : category_scope.

#[export]
Program Instance From_0 `(C : Category) : 0 ⟶ C.
Next Obligation. destruct X. Defined.
Next Obligation. destruct x. Defined.
Next Obligation. destruct x. Qed.
Next Obligation. destruct x. Qed.

#[export]
Program Instance Cat_Initial : @Initial Cat := {
  terminal_obj := _0;
  one := From_0
}.
Next Obligation.
  constructive; try contradiction.
Qed.
