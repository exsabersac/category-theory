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

(* [ilist l] computes the right-nested product [B a0 * (B a1 * (... * unit))].
   The empty list yields [unit]; a cons prepends one [B]-typed factor. *)
Fixpoint ilist (l : list A) : Type :=
  match l with
  | []      => unit
  | x :: xs => B x * ilist xs
  end.

(* Cons for indexed lists: prepend a [B a] head onto an [ilist l], giving an
   [ilist (a :: l)].  This is just pairing, the constructor for the product
   that [ilist (a :: l)] reduces to. *)
Definition icons
           (a : A)
           {l : list A}
           (b : B a)
           (il : ilist l) : ilist (a :: l) :=
  (b, il).

(* The empty indexed list: [ilist []] reduces to [unit], so [inil] is [tt]. *)
Definition inil : ilist [] := tt.

(* Get the car of an ilist.  The result type is computed from [As]: for a
   cons [a :: As'] it is [B a], and for the empty list it degenerates to
   [unit] (there is no head).  Both the type annotation and the body match on
   [As] so that [fst]/[tt] are well-typed in each branch. *)
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

(* Get the cdr of an ilist: the remaining [ilist As'] after dropping the
   head.  As with [ilist_hd], the return type is computed from [As] so the
   empty-list branch can fall back to [unit]. *)
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

(* Positional lookup (CPDT's [get]): return the [n]th element of [il].  Since
   [n] may be out of range, the caller supplies a default index [defA] with a
   witness [defB : B defA]; the result type [B (nth n As defA)] mirrors the
   default used by [List.nth], so out-of-bounds lookups return [defB].
   Defined by structural recursion on [n], descending through the tail. *)
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

(* Total, type-checked lookup at position [n]: with decidable equality on the
   index type [A], look up the [n]th entry and confirm its index equals the
   requested [a].  Returns [Some (b : B a)] only when both the position is in
   range and the indices match (rewriting along [eq_dec] to coerce the found
   [B a0] to [B a]); otherwise [None].  Used by Solver/Denote.v to fetch a
   reified morphism of the expected domain/codomain.  The [subst] relies only
   on [eq_dec]'s evidence, so this stays axiom-free. *)
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

(* Append two indexed lists, concatenating their index lists: the result is
   indexed by [l ++ l'], matching [List.app] on the underlying indices.
   Recurses on the first list's structure. *)
Equations iapp `(xs : ilist l) `(ys : ilist l') : ilist (l ++ l') :=
  iapp (l:=[]) tt ys := ys;
  iapp (x, xs) ys := (x, iapp xs ys).

(* Inverse of [iapp]: split an [ilist (l ++ l')] back into its [ilist l] and
   [ilist l'] halves.  Note that [l] (not just [l ++ l']) must be known for
   the recursion to fire, since the split point is dictated by [l]'s length. *)
Equations isplit `(xs : ilist (l ++ l')) : ilist l * ilist l'  :=
  isplit (l:=[]) xs := (tt, xs);
  isplit (x, xs) with isplit xs := {
    | (xs', ys) => ((x, xs'), ys)
  }.

End ilist.

(* Map over an indexed list, reindexing along [f : A -> C].  Each element
   [x : B a] is sent to [k a x : D (f a)], so the whole [ilist] over [l] for
   family [B] becomes an [ilist] over [map f l] for family [D].  This is the
   functorial action of [ilist] (CPDT's [imap]). *)
Equations imap `(f : A → C) `(k : ∀ (a : A), B a → D (f a))
  `(xs : @ilist A B l) : @ilist C D (map f l) :=
  imap f k (l:=[]) tt := tt;
  imap f k (l:=j :: js) (x, xs) := (k j x, imap f k xs).

(* The index-preserving special case of [imap]: keep the same index list [l]
   and only change the value family from [B] to [C] via [k a : B a -> C a]. *)
Equations imap' `(k : ∀ (a : A), B a → C a)
  `(xs : @ilist A B l) : @ilist A C l :=
  imap' k (l:=[]) tt := tt;
  imap' k (l:=j :: js) (x, xs) := (k j x, imap' k xs).
