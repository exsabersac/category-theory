(*
   本文件给出 ObMorProbe 相关定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Coq.Init.Datatypes.

(* Objects walking arrow 2, terminal 范畴 1. （已译） *)
Inductive Two := TZero | TOne.
Inductive One := Star.

(* Cat(2,1) on objects: every functor 2 -> 1 sends both objects to Star, so the
   object-map is unique. *)
Theorem two_to_one_unique :
  forall f g : Two -> One, forall t : Two, f t = g t.
Proof. intros f g t. destruct (f t), (g t). reflexivity. Qed.

(* Cat(1,2) 对象: 函子 1 -> 2 choice 对象 2, there
 exactly two such choices. （已译） *)
Theorem one_to_two_two_choices :
  forall f : One -> Two, (f Star = TZero) \/ (f Star = TOne).
Proof. intro f. destruct (f Star). - left. reflexivity. - right. reflexivity. Qed.

Theorem one_to_two_choices_differ : TZero <> TOne.
Proof. discriminate. Qed.
