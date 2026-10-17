Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Slice.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** * The slice over a terminal object is the ambient category *)

(*
   nLab:      https://ncatlab.org/nlab/show/over+category
   nLab:      https://ncatlab.org/nlab/show/terminal+object
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category

   本文件给出终对象相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Block A: the slice over a terminal object *)

Section SliceTerminal.

Context {C : Category}.
Context {T : @Terminal C}.

(* The forgetful functor C/1 ⟶ C: drop the structure morphism.  This is the
   comma projection [comma_proj1] read through [Comma_Slice]; it is spelled out
   directly here so that both its object and arrow maps are the literal first
   projections and hence compute. *)
Program Definition Slice_Forget :
  @Slice C (@terminal_obj C T) ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.

(* The section C ⟶ C/1: equip an object with its unique arrow into 1.  The
   triangle condition for an arrow f is `one ∘ f ≈ one`, discharged by
   [one_unique] (equivalently, it is the corollary [one_comp]) — the only place
   terminality is used in this direction. *)
Program Definition Slice_Section :
  C ⟶ @Slice C (@terminal_obj C T) := {|
  fobj := fun x => (x; one);
  fmap := fun _ _ f => (f; _)
|}.
Next Obligation. apply one_unique. Qed.

(* Every slice object is canonically isomorphic to its "renormalised" form
   (a; !).  The carrier of the isomorphism is the identity of C in both
   directions; only the triangle proofs differ, and [one_unique] supplies both.
   This is the natural-isomorphism component of the round trip below, isolated
   so that the strength claim in the header can be read off. *)
Program Definition slice_terminal_unit (x : @Slice C (@terminal_obj C T)) :
  Slice_Section (Slice_Forget x) ≅ x := {|
  to   := (id; _);
  from := (id; _)
|}.
Next Obligation. apply one_unique. Qed.
Next Obligation. apply one_unique. Qed.

(* The component is carried by the identity of C, in both directions. *)
Corollary slice_terminal_unit_carrier
  (x : @Slice C (@terminal_obj C T)) :
  (`1 (to (slice_terminal_unit x)) ≈ id) ∧
  (`1 (from (slice_terminal_unit x)) ≈ id).
Proof. split; reflexivity. Qed.

(* Mac Lane, §II.6, Exercise 2 [maclane:II.6:ex2].  Note the strength: `≅[Cat]`
   is EQUIVALENCE of categories in this library (Instance/Cat.v), and the header
   explains why the on-the-nose isomorphism Mac Lane states is unavailable
   here. *)
Program Definition Slice_Terminal :
  @Slice C (@terminal_obj C T) ≅[Cat] C := {|
  to   := Slice_Forget;
  from := Slice_Section
|}.
(* The C-side clause `Slice_Forget ◯ Slice_Section ≈ Id[C]` is discharged by the
   library's default obligation tactic — that composite is the identity on
   objects definitionally, so [iso_id] components suffice; the explicit and
   sharper statement is [Slice_Terminal_strict_section] below.  The clause left
   over is the slice-side one. *)
Next Obligation.
  (* Slice_Section ◯ Slice_Forget ≈ Id[C/1]: the components are the
     renormalisation isomorphisms above; naturality is `id ∘ f ∘ id ≈ f` on the
     underlying C-morphisms, the slice hom-setoid comparing nothing else. *)
  exists slice_terminal_unit.
  intros x y f; simpl.
  now rewrite id_left, id_right.
Qed.

(* The C-side round trip at strict strength: [Slice_Section] is a STRICT
   section of [Slice_Forget].  Both maps of the composite are definitionally
   the identity's, so the [Functor_StrictEq_Setoid] object witness is
   `fun _ => eq_refl` and the arrow coherence is `f ≈ f`.  This is strictly
   stronger than the [Cat]-level clause of [Slice_Terminal] and is the precise
   sense in which one half of Mac Lane's isomorphism does survive. *)
Lemma Slice_Terminal_strict_section :
  @equiv _ Functor_StrictEq_Setoid (Slice_Forget ◯ Slice_Section) Id[C].
Proof.
  exists (fun _ => eq_refl).
  intros x y f; simpl.
  reflexivity.
Qed.

End SliceTerminal.

(** ** Block B: the coslice under an initial object *)

(* Why this is proved directly rather than transported from Block A.

   `Initial C` is literally `Terminal (C^op)` (Structure/Initial.v), so the
   dual statement OUGHT to be Block A read in the opposite category.  It is
   not, and the obstruction is presentational rather than mathematical.
   Unfolding, the opposite of the slice over C^op has homs

     ∃ f : `1 x ~> `1 y,  f ∘ `2 x ≈ `2 y

   whereas Construction/Slice.v's [Coslice] record has homs

     ∃ f : `1 x ~> `1 y,  `2 y ≈ f ∘ `2 x

   — the same equation written in the other orientation.  Those are distinct
   types, so `Coslice C c` is NOT definitionally `(Slice (C^op) c)^op` and the
   transport would have to be mediated by an explicit comparison isomorphism
   built out of [symmetry] in the hom-setoid, plus the action of the duality
   functor [Op : Cat ⟶ Cat] (Instance/Cat/Opposite.v) on isomorphisms.  That is
   strictly more work, and a heavier dependency, than restating the four short
   definitions with [zero_unique] in place of [one_unique] — which is what
   follows.  Nothing below re-proves any mathematics that Block A proved; the
   two arguments are each two appeals to the uniqueness law. *)

Section CosliceInitial.

Context {C : Category}.
Context {I : @Initial C}.

(* Drop the structure morphism out of 0. *)
Program Definition Coslice_Forget :
  @Coslice C (@initial_obj C I) ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.

(* Equip an object with its unique arrow out of 0; the triangle condition
   `zero ≈ f ∘ zero` is discharged by [zero_unique] (equivalently, the
   corollary [zero_comp]). *)
Program Definition Coslice_Section :
  C ⟶ @Coslice C (@initial_obj C I) := {|
  fobj := fun x => (x; zero);
  fmap := fun _ _ f => (f; _)
|}.
Next Obligation. apply zero_unique. Qed.

Program Definition coslice_initial_unit (x : @Coslice C (@initial_obj C I)) :
  Coslice_Section (Coslice_Forget x) ≅ x := {|
  to   := (id; _);
  from := (id; _)
|}.
Next Obligation. apply zero_unique. Qed.
Next Obligation. apply zero_unique. Qed.

Corollary coslice_initial_unit_carrier
  (x : @Coslice C (@initial_obj C I)) :
  (`1 (to (coslice_initial_unit x)) ≈ id) ∧
  (`1 (from (coslice_initial_unit x)) ≈ id).
Proof. split; reflexivity. Qed.

(* The dual of [Slice_Terminal], at the same strength and for the same
   reason. *)
Program Definition Coslice_Initial :
  @Coslice C (@initial_obj C I) ≅[Cat] C := {|
  to   := Coslice_Forget;
  from := Coslice_Section
|}.
(* As in Block A the C-side clause is discharged by the default obligation
   tactic — the composite is the identity on objects definitionally — and the
   explicit, sharper form is [Coslice_Initial_strict_section] below. *)
Next Obligation.
  exists coslice_initial_unit.
  intros x y f; simpl.
  now rewrite id_left, id_right.
Qed.

Lemma Coslice_Initial_strict_section :
  @equiv _ Functor_StrictEq_Setoid (Coslice_Forget ◯ Coslice_Section) Id[C].
Proof.
  exists (fun _ => eq_refl).
  intros x y f; simpl.
  reflexivity.
Qed.

End CosliceInitial.
