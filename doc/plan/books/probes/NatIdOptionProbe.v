(*
   本文件给出 NatIdOptionProbe 相关定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Coq.Init.Datatypes.

Definition nat_trans (F G : Type -> Type) := forall X : Type, F X -> G X.

Definition omap {A B} (f : A -> B) (o : option A) : option B :=
  match o with Some a => Some (f a) | None => None end.

(* Candidate 1: the injection. *)
Definition inject : nat_trans (fun X => X) option := fun X x => Some x.

(* Candidate 2: the constant-None family. *)
Definition constNone : nat_trans (fun X => X) option := fun X _ => None.

(* Both are natural: omap f (alpha_X x) = alpha_Y (f x). *)
Theorem inject_natural :
  forall (X Y : Type) (f : X -> Y) (x : X), omap f (inject X x) = inject Y (f x).
Proof. reflexivity. Qed.

Theorem constNone_natural :
  forall (X Y : Type) (f : X -> Y) (x : X), omap f (constNone X x) = constNone Y (f x).
Proof. reflexivity. Qed.

(* They are distinct, so Nat(Id, option) has AT LEAST two elements. *)
Theorem inject_neq_constNone : inject <> constNone.
Proof.
  intro H.
  assert (inject unit tt = constNone unit tt) as HC by (rewrite H; reflexivity).
  simpl in HC. discriminate.
Qed.

(* The counting engine: option unit has exactly two inhabitants, what
 bounds family count above two once 自然性 pins alpha alpha_unit. （已译） *)
Theorem option_unit_exactly_two :
  forall o : option unit, o = Some tt \/ o = None.
Proof. intro o. destruct o as [u|]. - left. destruct u. reflexivity. - right. reflexivity. Qed.
