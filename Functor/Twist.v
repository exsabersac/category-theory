Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(** * Twisting a functor by a family of isomorphisms *)

(*
   nLab: https://ncatlab.org/nlab/show/natural+isomorphism

   本文件给出函子相关定义或实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Twist.

Context {C : Category}.
Context (F : C ⟶ C).
Context (α : ∀ x : C, x ≅ F x).

#[local] Obligation Tactic := idtac.

(* The twisted functor.  Note [fobj := fun x => x]: the object function is
   the identity function itself, not merely a function isomorphic to it. *)
Program Definition Twist : C ⟶ C := {|
  fobj := fun x => x;
  fmap := fun x y f => (α y)⁻¹ ∘ fmap[F] f ∘ α x
|}.
Next Obligation.
  intros x y f g Hfg.
  now rewrite Hfg.
Qed.
Next Obligation.
  intros x; simpl.
  rewrite fmap_id, id_right.
  apply iso_from_to.
Qed.
Next Obligation.
  intros x y z f g; simpl.
  rewrite fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity |].
  rewrite (comp_assoc (α y)).
  rewrite iso_to_from, id_left.
  reflexivity.
Qed.

(* The object function is the identity, by computation.  The [=] is on
   OBJECTS, which is where this library does use propositional equality --
   it is what [Functor_StrictEq_Setoid] compares; morphisms are compared
   with ≈ everywhere. *)
Lemma Twist_fobj (x : C) : fobj[Twist] x = x.
Proof. reflexivity. Qed.

(* If α is natural, the twist is strictly equal to the identity functor:
   the object equalities are all [eq_refl], and the arrow condition is
   α cancelling itself across f. *)
Theorem Twist_natural_strict_id
  (nat : ∀ (x y : C) (f : x ~> y), α y ∘ f ≈ fmap[F] f ∘ α x) :
  @equiv _ Functor_StrictEq_Setoid Twist (@Id C).
Proof.
  exists (fun _ => eq_refl).
  intros x y f.
  (* Both transports are along [eq_refl], hence the identity, so the
     coherence condition reduces by conversion to the arrow maps agreeing. *)
  change ((α y)⁻¹ ∘ fmap[F] f ∘ α x ≈ f).
  rewrite <- comp_assoc.
  rewrite <- nat.
  rewrite comp_assoc.
  rewrite iso_from_to.
  apply id_left.
Qed.

(* The converse, given uniqueness of identity proofs on the objects of C.
   The hypothesis is needed because the strict setoid allows an ARBITRARY
   proof of [x = x] as the object component; without [uip] a nontrivial
   loop could in principle scramble the transports. *)
Theorem Twist_strict_id_natural
  (uip : ∀ (x : C) (p : x = x), p = eq_refl)
  (H : @equiv _ Functor_StrictEq_Setoid Twist (@Id C)) :
  ∀ (x y : C) (f : x ~> y), α y ∘ f ≈ fmap[F] f ∘ α x.
Proof.
  destruct H as [eq_on_obj coherent].
  intros x y f.
  pose proof (coherent x y f) as Hc.
  rewrite (uip x (eq_on_obj x)), (uip y (eq_on_obj y)) in Hc.
  (* with both object equalities [eq_refl] the transports vanish *)
  assert (Hred : (α y)⁻¹ ∘ fmap[F] f ∘ α x ≈ f) by exact Hc.
  assert (Hpost : α y ∘ ((α y)⁻¹ ∘ fmap[F] f ∘ α x) ≈ α y ∘ f)
    by (apply compose_respects; [ reflexivity | exact Hred ]).
  rewrite <- Hpost.
  rewrite !comp_assoc.
  rewrite iso_to_from, id_left.
  reflexivity.
Qed.

(* The distinctness criterion in the form it is used: a SINGLE morphism at
   which α is not natural separates the twist from the identity in
   the strict functor setoid. *)
Corollary Twist_not_strict_id
  (uip : ∀ (x : C) (p : x = x), p = eq_refl)
  {x y : C} {f : x ~> y}
  (Hnat : α y ∘ f ≈ fmap[F] f ∘ α x → False) :
  @equiv _ Functor_StrictEq_Setoid Twist (@Id C) → False.
Proof.
  intro H.
  exact (Hnat (Twist_strict_id_natural uip H x y f)).
Qed.

End Twist.

Arguments Twist {C} F α.

(* Uniqueness of identity proofs from decidable equality of objects
   (Hedberg's argument, via the stdlib's axiom-free [UIP_dec]); this is
   how the [uip] hypothesis above is discharged for the concrete
   categories used as witnesses. *)
Definition uip_of_dec {A : Type}
  (dec : ∀ x y : A, {x = y} + {x <> y}) (x : A) (p : x = x) : p = eq_refl :=
  UIP_dec dec p eq_refl.

Section TwistId.

Context {C : Category}.
Context (α : ∀ x : C, x ≅ x).

(* The twist of the IDENTITY functor is always naturally isomorphic to the
   identity functor -- α is the natural isomorphism, and the coherence
   condition of [Functor_Setoid] is literally the definition of the
   twisted arrow map.  Hence the weak setoid, which is the hom-setoid of
   [Cat], never separates this pair, however far α is from being natural. *)
Theorem Twist_Id_weak_equiv :
  @equiv _ Functor_Setoid (Twist (@Id C) α) (@Id C).
Proof.
  exists α.
  intros x y f; simpl.
  reflexivity.
Qed.

End TwistId.
