Require Import Coq.Unicode.Utf8.
Require Import Coq.Lists.List.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Import ListNotations.

(** Indexed (heterogeneous) lists *)

(*
 nLab: https://ncatlab.org/nlab/show/dependent+product

   本文件给出 IList 相关定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ilist.

Context {A : Type}.
Context {B : A → Type}.

(* 相关说明。 （已译） *)
Fixpoint ilist (l : list A) : Type :=
  match l with
  | []      => unit
  | x :: xs => B x * ilist xs
  end.

(* 相关说明。 （已译） *)
Definition icons
           (a : A)
           {l : list A}
           (b : B a)
           (il : ilist l) : ilist (a :: l) :=
  (b, il).

(* The empty indexed list: [ilist []] reduces to [unit], so [inil] is [tt]. *)
Definition inil : ilist [] := tt.

(*
   本节说明 IList 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ilist_hd {As : list A} (il : ilist As) :
  match As return ilist As → Type with
    | a :: As' => fun il => B a
    | [] => fun _ => unit
  end il :=
  match As return
        ∀ (il : ilist As),
          match As return ilist As → Type with
            | a :: As' => fun il => B a
            | [] => fun _ => unit
          end il with
    | a :: As => fun il => fst il
    | [] => fun il => tt
  end il.

(* 相关说明。 （已译） *)
Definition ilist_tl {As : list A} (il : ilist As) :
  match As return ilist As → Type with
    | a :: As' => fun il => ilist As'
    | [] => fun _ => unit
  end il :=
  match As return
        ∀ (il : ilist As),
          match As return ilist As → Type with
            | a :: As' => fun il => ilist As'
            | [] => fun _ => unit
          end il with
    | a :: As => fun il => snd il
    | [] => fun il => tt
  end il.

(*
   本节说明 IList 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ith (n : nat) {As : list A} (il : ilist As)
  {defA : A} (defB : B defA) : B (nth n As defA).
Proof.
  generalize dependent As.
  induction n; intros.
  - destruct As; simpl.
    + exact defB.
    + exact (fst il).
  - destruct As; simpl.
    + exact defB.
    + apply IHn.
      exact (snd il).
Defined.

(*
   本节说明 IList 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ith_exact `{EqDec A} (n : nat) (a : A)
  {As : list A} (il : ilist As) : option (B a).
Proof.
  generalize dependent As.
  induction n; intros.
  - destruct As; simpl.
    + exact None.
    + simpl in il.
      destruct (eq_dec a a0); subst.
      * exact (Some (fst il)).
      * exact None.
  - destruct As; simpl.
    + exact None.
    + simpl in il.
      destruct il.
      exact (IHn As i).
Defined.

(* 相关说明。 （已译） *)
Equations iapp `(xs : ilist l) `(ys : ilist l') : ilist (l ++ l') :=
  iapp (l:=[]) tt ys := ys;
  iapp (x, xs) ys := (x, iapp xs ys).

(*
   本节说明 IList 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Equations isplit `(xs : ilist (l ++ l')) : ilist l * ilist l'  :=
  isplit (l:=[]) xs := (tt, xs);
  isplit (x, xs) with isplit xs := {
    | (xs', ys) => ((x, xs'), ys)
  }.

End ilist.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Equations imap `(f : A → C) `(k : ∀ (a : A), B a → D (f a))
  `(xs : @ilist A B l) : @ilist C D (map f l) :=
  imap f k (l:=[]) tt := tt;
  imap f k (l:=j :: js) (x, xs) := (k j x, imap f k xs).

(* 相关说明。 （已译） *)
Equations imap' `(k : ∀ (a : A), B a → C a)
  `(xs : @ilist A B l) : @ilist A C l :=
  imap' k (l:=[]) tt := tt;
  imap' k (l:=j :: js) (x, xs) := (k j x, imap' k xs).
