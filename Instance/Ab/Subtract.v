Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.

Generalizable All Variables.

(*
   本文件给出阿贝尔群相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition ab_sub (A : AbObject) (x y : carrier (cmon_setoid A)) :
  carrier (cmon_setoid A) := cmon_plus A x (ab_neg A y).

#[export] Instance ab_sub_respects (A : AbObject) :
  Proper (equiv ==> equiv ==> equiv) (ab_sub A).
Proof.
  intros x x' Hx y y' Hy; unfold ab_sub.
  now rewrite Hx, Hy.
Qed.

Lemma ab_neg_invol (A : AbObject) (a : carrier (cmon_setoid A)) :
  ab_neg A (ab_neg A a) ≈ a.
Proof.
  symmetry; apply ab_neg_unique.
  apply ab_neg_right.
Qed.

Lemma ab_sub_self (A : AbObject) (x : carrier (cmon_setoid A)) :
  ab_sub A x x ≈ cmon_zero A.
Proof. apply ab_neg_right. Qed.

Lemma ab_sub_zero_r (A : AbObject) (x : carrier (cmon_setoid A)) :
  ab_sub A x (cmon_zero A) ≈ x.
Proof.
  unfold ab_sub.
  rewrite ab_neg_zero.
  apply cmon_plus_zero_r.
Qed.

Lemma ab_sub_zero_l (A : AbObject) (x : carrier (cmon_setoid A)) :
  ab_sub A (cmon_zero A) x ≈ ab_neg A x.
Proof. unfold ab_sub; apply cmon_plus_zero_l. Qed.

(* 相关说明。 （已译） *)
Lemma ab_sub_neg (A : AbObject) (x y : carrier (cmon_setoid A)) :
  ab_neg A (ab_sub A x y) ≈ ab_sub A y x.
Proof.
  symmetry; apply ab_neg_unique.
  unfold ab_sub.
  rewrite !cmon_plus_assoc.
  rewrite <- (cmon_plus_assoc A (ab_neg A x) x (ab_neg A y)).
  rewrite ab_neg_left, cmon_plus_zero_l.
  apply ab_neg_right.
Qed.

(* (-x) - (-y) ≈ y - x. *)
Lemma ab_sub_neg_neg (A : AbObject) (x y : carrier (cmon_setoid A)) :
  ab_sub A (ab_neg A x) (ab_neg A y) ≈ ab_sub A y x.
Proof.
  unfold ab_sub.
  rewrite (ab_neg_invol A y).
  apply cmon_plus_comm.
Qed.

(* (x - y) + (y - z) ≈ x - z: the transitivity computation. *)
Lemma ab_sub_trans (A : AbObject) (x y z : carrier (cmon_setoid A)) :
  cmon_plus A (ab_sub A x y) (ab_sub A y z) ≈ ab_sub A x z.
Proof.
  unfold ab_sub.
  rewrite cmon_plus_assoc.
  rewrite <- (cmon_plus_assoc A (ab_neg A y) y (ab_neg A z)).
  rewrite ab_neg_left, cmon_plus_zero_l.
  reflexivity.
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ab_sub_plus (A : AbObject) (x y u v : carrier (cmon_setoid A)) :
  cmon_plus A (ab_sub A x y) (ab_sub A u v)
    ≈ ab_sub A (cmon_plus A x u) (cmon_plus A y v).
Proof.
  unfold ab_sub.
  rewrite ab_neg_plus.
  rewrite !cmon_plus_assoc.
  apply cmon_plus_respects; [ reflexivity |].
  rewrite <- !cmon_plus_assoc.
  apply cmon_plus_respects; [| reflexivity ].
  apply cmon_plus_comm.
Qed.

(* 相关说明。 （已译） *)
Lemma ab_sub_add_cancel (A : AbObject) (x y : carrier (cmon_setoid A)) :
  ab_sub A (cmon_plus A x y) x ≈ y.
Proof.
  unfold ab_sub.
  rewrite (cmon_plus_comm A x y).
  rewrite cmon_plus_assoc.
  rewrite ab_neg_right.
  apply cmon_plus_zero_r.
Qed.

Lemma ab_add_sub_cancel (A : AbObject) (x y : carrier (cmon_setoid A)) :
  cmon_plus A y (ab_sub A x y) ≈ x.
Proof.
  unfold ab_sub.
  rewrite <- cmon_plus_assoc.
  rewrite (cmon_plus_comm A y x).
  rewrite cmon_plus_assoc.
  rewrite ab_neg_right.
  apply cmon_plus_zero_r.
Qed.

(* x - y ≈ 0 exactly when x ≈ y. *)
Lemma ab_sub_eq_zero_iff (A : AbObject) (x y : carrier (cmon_setoid A)) :
  ab_sub A x y ≈ cmon_zero A ↔ x ≈ y.
Proof.
  split.
  - intro H.
    apply (ab_cancel_l A (ab_neg A y)).
    rewrite (ab_neg_left A y).
    rewrite (cmon_plus_comm A (ab_neg A y) x).
    exact H.
  - intro H; rewrite H; apply ab_sub_self.
Qed.

Lemma ab_map_sub {A B : AbObject} (f : AbHom A B)
  (x y : carrier (cmon_setoid A)) :
  cmon_map f (ab_sub A x y) ≈ ab_sub B (cmon_map f x) (cmon_map f y).
Proof.
  unfold ab_sub.
  rewrite cmon_map_plus.
  now rewrite ab_map_neg.
Qed.
