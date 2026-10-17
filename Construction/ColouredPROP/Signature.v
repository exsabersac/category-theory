Require Import Category.Lib.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(** * Signatures over coloured PROPs *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CSignature.

Context (Colour : Type).

Definition CSignature : Type := list Colour -> list Colour -> Type.

(** ** Examples *)

(** The empty signature.  Useful as a base case: the free coloured
    PROP on [Empty_CSig] is the coloured permutation category. *)
Definition Empty_CSig : CSignature :=
  fun _ _ => Empty_set.

(*
   本节说明 Signature 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Single_CSig (ms ns : list Colour) : CSignature :=
  fun xs ys => ((xs = ms) * (ys = ns))%type.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Sum_CSig (S T : CSignature) : CSignature :=
  fun cs ds => (S cs ds + T cs ds)%type.

(** Sub-signature: a boundary-preserving family of generator
    relabellings into another signature — despite the name, no
    injectivity is required (generator collapses are allowed).
    Inhabited by [inl] / [inr] / nested projection chains. *)
Definition CSubSig (Sub Sup : CSignature) : Type :=
  forall cs ds, Sub cs ds -> Sup cs ds.

(** The identity sub-signature. *)
Definition CSubSig_id (S : CSignature) : CSubSig S S :=
  fun _ _ g => g.

(** Sub-signature composition. *)
Definition CSubSig_compose {S T U : CSignature}
  (h2 : CSubSig T U) (h1 : CSubSig S T) : CSubSig S U :=
  fun cs ds g => h2 cs ds (h1 cs ds g).

End CSignature.

Arguments CSignature Colour : assert.
Arguments Empty_CSig {Colour} _ _.
Arguments Single_CSig {Colour} ms ns _ _.
Arguments Sum_CSig {Colour} S T _ _.
Arguments CSubSig {Colour} Sub Sup.
Arguments CSubSig_id {Colour} S.
Arguments CSubSig_compose {Colour S T U} h2 h1.

(*
   本节说明 Signature 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CTerm.

Context {Colour : Type}.
Context (S : CSignature Colour).

Inductive CTerm : list Colour -> list Colour -> Type :=
  | CT_id (cs : list Colour) : CTerm cs cs
  | CT_braid (cs ds : list Colour) : CTerm (cs ++ ds) (ds ++ cs)
  | CT_comp {cs ds es} : CTerm ds es -> CTerm cs ds -> CTerm cs es
  | CT_tens {cs1 ds1 cs2 ds2} :
      CTerm cs1 ds1 -> CTerm cs2 ds2 -> CTerm (cs1 ++ cs2) (ds1 ++ ds2)
  | CT_gen {cs ds} : S cs ds -> CTerm cs ds.

End CTerm.

Arguments CT_id    {Colour S} cs.
Arguments CT_braid {Colour S} cs ds.
Arguments CT_comp  {Colour S cs ds es} _ _.
Arguments CT_tens  {Colour S cs1 ds1 cs2 ds2} _ _.
Arguments CT_gen   {Colour S cs ds} _.

Declare Scope cterm_scope.
Delimit Scope cterm_scope with cterm.

Notation "g ⊙c f" := (CT_comp g f)
  (at level 40, left associativity) : cterm_scope.
Notation "f ⊕c g" := (CT_tens f g)
  (at level 30, right associativity) : cterm_scope.

(** ** Smart constructors *)

(** The "swap" braid on two single typed wires.  Note that
    [[c] ++ [d]] is definitionally [[c; d]], so this term also
    inhabits [CTerm S [c; d] [d; c]] on the nose. *)
Definition CT_swap {Colour} {S : CSignature Colour} (c d : Colour) :
  CTerm S ([c] ++ [d]) ([d] ++ [c]) :=
  CT_braid [c] [d].

(** Identity on a single typed wire.  Named [cwire] to steer clear of
    the [wire] projection of [Construction/ColouredPROP.v]'s supply
    vocabulary. *)
Definition cwire {Colour} {S : CSignature Colour} (c : Colour) :
  CTerm S [c] [c] :=
  CT_id [c].

(** The empty term: no input wires, no output wires — the monoidal
    unit's identity. *)
Definition CT_nothing {Colour} {S : CSignature Colour} : CTerm S [] [] :=
  CT_id [].

(*
   本节说明 Signature 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
