(*
   本文件给出 ObMorProbe 相关定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Coq.Init.Datatypes.

(* Objects of the walking arrow 2, and of the terminal category 1. *)
Inductive Two := TZero | TOne.
Inductive One := Star.

(* Cat(2,1) on objects: every functor 2 -> 1 sends both objects to Star, so the
   object-map is unique. *)
Theorem two_to_one_unique :
  forall f g : Two -> One, forall t : Two, f t = g t.
Proof. intros f g t. destruct (f t), (g t). reflexivity. Qed.

(* Cat(1,2) on objects: a functor 1 -> 2 is a choice of object of 2, and there
   are exactly two such choices. *)
Theorem one_to_two_two_choices :
  forall f : One -> Two, (f Star = TZero) \/ (f Star = TOne).
Proof. intro f. destruct (f Star). - left. reflexivity. - right. reflexivity. Qed.

Theorem one_to_two_choices_differ : TZero <> TOne.
Proof. discriminate. Qed.
