(*
PROBE for QA finding E1 (#929): how many natural transformations between the
   object-functor ob and the morphism-functor mor on Cat?

   #929 as filed miscounts these.  The correct counts come from co-Yoneda:
   ob = Cat(1, -) and mor = Cat(2, -), where 1 is the terminal category and 2
   the walking arrow.  So
       Nat(ob, mor) = Nat(Cat(1,-), Cat(2,-)) ~= Cat(2, 1)   -- ONE functor
       Nat(mor, ob) = Nat(Cat(2,-), Cat(1,-)) ~= Cat(1, 2)   -- TWO functors
   i.e. one transformation ob ==> mor and two mor ==> ob, THREE in total.

   This probe checks the two counting facts the argument turns on, at the level
   of the shapes themselves: there is exactly one map from the walking arrow to
   the point, and exactly two points of the walking arrow.

--------
用于 QA 查找 E1 (#929) 的探测器：在 Cat 上的对象函子 ob 和态射函子 mor 之间有多少自然变换？

#929 提交时对此计数错误。正确的计数来自余 Yoneda 引理：
ob = Cat(1, -) 和 mor = Cat(2, -)，其中 1 是终对象范畴，2 是行走箭头。所以
    Nat(ob, mor) = Nat(Cat(1,-), Cat(2,-)) ~= Cat(2, 1)   -- 一个函子
    Nat(mor, ob) = Nat(Cat(2,-), Cat(1,-)) ~= Cat(1, 2)   -- 两个函子
也就是说，一个变换 ob ==> mor，两个 mor ==> ob，总共三个。

这个探测器检查论证所依赖的两个计数事实，在形状自身层面：从行走箭头到点的映射恰好有一个，从行走箭头的点出发的点恰好有两个。
*)

Require Import Coq.Init.Datatypes.

(* Objects of the walking arrow 2, and of the terminal category 1. / 行走箭头2的对象，以及终端范畴1的对象。 *)
Inductive Two := TZero | TOne.
Inductive One := Star.

(*
Cat(2,1) on objects: every functor 2 -> 1 sends both objects to Star, so the
   object-map is unique.

--------
Cat(2,1) 关于对象：每个函子 2 -> 1 都将两个对象发送到 Star，因此对象映射是唯一的。
*)
Theorem two_to_one_unique :
  forall f g : Two -> One, forall t : Two, f t = g t.
Proof. intros f g t. destruct (f t), (g t). reflexivity. Qed.

(*
Cat(1,2) on objects: a functor 1 -> 2 is a choice of object of 2, and there
   are exactly two such choices.

--------
Cat(1,2) 关于对象：一个函子 1 -> 2 是 2 的一个对象的选择，并且恰好有两个这样的选择。
*)
Theorem one_to_two_two_choices :
  forall f : One -> Two, (f Star = TZero) \/ (f Star = TOne).
Proof. intro f. destruct (f Star). - left. reflexivity. - right. reflexivity. Qed.

Theorem one_to_two_choices_differ : TZero <> TOne.
Proof. discriminate. Qed.
