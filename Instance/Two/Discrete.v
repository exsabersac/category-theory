Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** The discrete category on two objects. *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Discrete_category

   本文件给出离散范畴实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Inductive TwoDObj : Set := TwoDX | TwoDY.

Inductive TwoDHom : TwoDObj → TwoDObj → Set :=
  | TwoDIdX : TwoDHom TwoDX TwoDX
  | TwoDIdY : TwoDHom TwoDY TwoDY.

Definition TwoDHom_inv_t : ∀ x y, TwoDHom x y → Prop.
Proof.
  intros [] [] f.
  - exact (f = TwoDIdX).
  - exact False.          (* Unused, any Prop is ok here *)
  - exact False.          (* Unused, any Prop is ok here *)
  - exact (f = TwoDIdY).
Defined.

Corollary TwoDHom_inv x y f : TwoDHom_inv_t x y f.
Proof. destruct f; reflexivity. Qed.

Lemma TwoDHom_X_Y_absurd : TwoDHom TwoDX TwoDY → False.
Proof. inversion 1. Qed.

#[export] Hint Extern 4 => contradiction TwoDHom_X_Y_absurd : two_laws.

Lemma TwoDHom_Y_X_absurd : TwoDHom TwoDY TwoDX → False.
Proof. inversion 1. Qed.

#[export] Hint Extern 4 => contradiction TwoDHom_Y_X_absurd : two_laws.

Local Set Warnings "-intuition-auto-with-star".

(* The discrete 范畴 2 has two 对象 恒等 态射. （已译） *)

Program Definition Two_Discrete : Category := {|
  obj     := TwoDObj;
  hom     := TwoDHom;
  homset  := Morphism_equality;
  id      := fun x => match x with
    | TwoDX => TwoDIdX
    | TwoDY => TwoDIdY
    end;
  compose := fun x y z (f : TwoDHom y z) (g : TwoDHom x y) =>
    match x, y, z with
    | TwoDX, TwoDX, TwoDX => TwoDIdX
    | TwoDY, TwoDY, TwoDY => TwoDIdY
    | _,    _,    _    => _
    end
|}.
Next Obligation. destruct x, y, z; intuition; auto with *. Qed.
Next Obligation.
  destruct x, y, z; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation.
  destruct x, y, z; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation.
  destruct x, y, z; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation.
  destruct x, y, z; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation.
  destruct x, y; auto with two_laws;
  symmetry; exact (TwoDHom_inv _ _ f).
Qed.
Next Obligation.
  destruct x, y; auto with two_laws;
  symmetry; exact (TwoDHom_inv _ _ f).
Qed.
Next Obligation.
  destruct x, y, z, w; auto with two_laws; intuition.
Qed.
Next Obligation.
  destruct x, y, z, w; auto with two_laws; intuition.
Qed.

(*
   本节说明函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Pick_Two {C : Category} (a b : C) :
  Two_Discrete ⟶ C := {|
  fobj := λ x,
    match x with
    | TwoDX => a
    | TwoDY => b
    end;
  fmap := λ x y _,
    match x, y with
    | TwoDX, TwoDX => id
    | TwoDY, TwoDY => id
    | _,    _      => !
    end
|}.
Next Obligation.
  destruct x, y; auto with two_laws.
Qed.
Next Obligation.
  destruct x, y; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation.
  destruct x, y; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation.
  destruct x; auto with two_laws; cat.
Qed.
Next Obligation.
  destruct x, y, z; auto with two_laws; cat.
Qed.
