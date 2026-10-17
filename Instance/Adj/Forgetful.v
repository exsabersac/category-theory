Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Adj.

Generalizable All Variables.

#[local] Obligation Tactic := intros.

(** * The two forgetful functors off the category of adjunctions *)

(*
   本文件给出遗忘函子相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The first forgetful functor: an adjunction to its left adjoint, a
   conjugate pair to its sigma. *)
Program Definition AdjForgetLeft (C D : Category) : Adj C D ⟶ [D, C] := {|
  fobj := fun x => adjobj_left x;
  fmap := fun _ _ f => conj_left f
|}.
Next Obligation. intros f g [Hl _]; exact Hl. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(* The second, on the OPPOSITE of the category of adjunctions: an
   adjunction to its right adjoint, a conjugate pair to its tau. *)
Program Definition AdjForgetRight (C D : Category) :
  (Adj C D)^op ⟶ [C, D] := {|
  fobj := fun x => adjobj_right x;
  fmap := fun _ _ f => conj_right f
|}.
Next Obligation. intros f g [_ Hr]; exact Hr. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(* Faithful: the tau of a conjugate pair is determined by its sigma. *)
#[export]
Program Instance AdjForgetLeft_Faithful (C D : Category) :
  Faithful (AdjForgetLeft C D).
Next Obligation.
  split; [ exact X | now apply conj_pair_right_unique ].
Qed.

(* Full: every sigma has a conjugate, namely its mate. *)
#[export]
Program Instance AdjForgetLeft_Full (C D : Category) :
  Full (AdjForgetLeft C D) := {|
  prefmap := fun x y g =>
    {| conj_left  := g
     ; conj_right := conj_mate (adjobj_adj y) (adjobj_adj x) g |}
|}.
Next Obligation. exact (conjugate_conj_mate _ _ g). Qed.
Next Obligation. reflexivity. Qed.

(* Faithful: the sigma of a conjugate pair is determined by its tau. *)
#[export]
Program Instance AdjForgetRight_Faithful (C D : Category) :
  Faithful (AdjForgetRight C D).
Next Obligation.
  split; [ now apply conj_pair_left_unique | exact X ].
Qed.

(* Full: every tau has a conjugate, namely its inverse mate. *)
#[export]
Program Instance AdjForgetRight_Full (C D : Category) :
  Full (AdjForgetRight C D) := {|
  prefmap := fun x y g =>
    {| conj_left  := conj_mate_inv (adjobj_adj x) (adjobj_adj y) g
     ; conj_right := g |}
|}.
Next Obligation. exact (conjugate_conj_mate_inv _ _ g). Qed.
Next Obligation. reflexivity. Qed.
