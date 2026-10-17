Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Discrete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.

From Coq Require Import Eqdep_dec.

Generalizable All Variables.

Import EqNotations.

(** * Reconstructing a discrete category from its set of objects *)

(*
 Reference: Saunders Mac Lane, "Categories for the Working Mathematician",
 Reference: Michael Hedberg, "A coherence theorem for Martin-Löf's type

   本文件给出离散范畴实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Why a separate file rather than extending Instance/Discrete.v, as the
   issue's work-plan suggested: NOT layering -- Instance/Discrete.v,
   Instance/Cat.v and Instance/StrictCat.v are independent siblings, and
   adding the imports there would create no cycle.  The reason is cost to
   consumers: Instance/Discrete.v is imported by Adjunction/GAFT.v,
   Adjunction/SAFT.v, Structure/Limit/Product.v and Theory/WeaklyInitial.v,
   and extending it would drag Instance/Cat, Instance/StrictCat and the
   Eqdep_dec development into all four of those dependency cones for the
   sake of theorems none of them consume. *)

(** ** Transported identities *)

(* Composing transported identities transports along the concatenated proof. *)
Lemma rew_id_trans {C : Category} {x y z : C} (H : x = y) (H' : y = z) :
  rew H' in id ∘ rew H in id ≈ rew (eq_trans H H') in id.
Proof. destruct H, H'; cat. Qed.

(* A transported identity is invertible, its inverse being the identity
   transported along the reversed proof. *)
Lemma rew_id_iso_to {C : Category} {x y : C} (H : x = y) :
  rew (eq_sym H) in id ∘ rew H in id ≈ id.
Proof. destruct H; cat. Qed.

Lemma rew_id_iso_from {C : Category} {x y : C} (H : x = y) :
  rew H in id ∘ rew (eq_sym H) in id ≈ id.
Proof. destruct H; cat. Qed.

(** ** The comparison functor *)

(* [DiscreteCat (obj C) ⟶ C]: the identity on objects, sending an equality
   proof to the identity transported along it.  The explicit universe binders
   force the discrete category to sit at [C]'s own universes, which is what the
   [StrictCat] statement below needs; [Program] is avoided here because its
   obligations cannot refer to named universes. *)
Definition Discrete_Compare@{o h p} (C : Category@{o h p}) :
  DiscreteCat@{o h p} C ⟶ C.
Proof.
  unshelve refine (@Build_Functor@{o h p o h p} (DiscreteCat@{o h p} C) C
    (fun x : C => x)
    (fun (x y : C) (e : x = y) => rew [fun z : C => x ~{C}~> z] e in id)
    _ _ _).
  (* [≈] on the source is [eq]; [rew eq_refl in id] is [id] *)
  - intros x y; proper; destruct X; reflexivity.
  - intros x; reflexivity.
  - intros x y z H H'; symmetry; apply rew_id_trans.
Defined.

(* The action on morphisms, in the [rew] shape used by Structure/Discrete.v. *)
Lemma fmap_Discrete_Compare {C : Category} {x y : C} (e : x = y) :
  fmap[Discrete_Compare C] e ≈ rew e in id.
Proof. reflexivity. Qed.

(* Fullness is exactly the [Discrete] predicate: the witness it produces for an
   arrow [g] is a preimage of [g] under [fmap].  No further hypothesis. *)
Program Definition Discrete_Compare_Full (C : Category) (D : Discrete C) :
  Full (Discrete_Compare C) := {|
  prefmap := fun x y g => `1 (D x y g)
|}.
Next Obligation. symmetry; exact (`2 (D x y g)). Qed.

(** ** Rigidity: faithfulness of the comparison functor *)

(* The reconstruction hypothesis: an equality proof is recoverable from the
   identity it transports.  Equivalently (see below) the comparison functor is
   faithful. *)
Definition DiscreteRigid (C : Category) : Type :=
  ∀ (x y : C) (H H' : x = y),
    fmap[Discrete_Compare C] H ≈ fmap[Discrete_Compare C] H' → H = H'.

(* The same condition spelled out without the functor. *)
Lemma DiscreteRigid_elementary (C : Category) :
  DiscreteRigid C ↔
    (∀ (x y : C) (H H' : x = y),
       (rew H in id : x ~> y) ≈ rew H' in id → H = H').
Proof. split; intros r x y H H'; exact (r x y H H'). Qed.

(* And in the library's vocabulary. *)
Lemma DiscreteRigid_Faithful (C : Category) :
  DiscreteRigid C ↔ Faithful (Discrete_Compare C).
Proof.
  split; intro r.
  - constructor; intros x y f g e; exact (r x y f g e).
  - intros x y H H' e; exact (@fmap_inj _ _ _ r x y H H' e).
Qed.

(* Uniqueness of identity proofs on the objects is one sufficient condition:
   under it the hypothesis of rigidity is discarded outright. *)
Definition DiscreteRigid_UIP (C : Category)
  (uip : ∀ (x y : C) (H H' : x = y), H = H') : DiscreteRigid C :=
  fun x y H H' _ => uip x y H H'.

(* Decidable object equality is another, through Hedberg's theorem. *)
Definition DiscreteRigid_dec (C : Category)
  (dec : ∀ x y : C, {x = y} + {x <> y}) : DiscreteRigid C :=
  DiscreteRigid_UIP C (@UIP_dec (obj[C]) dec).

(* On a discrete category the comparison functor acts as the identity on
   morphisms, since there [rew H in id] reduces to [H] itself. *)
Lemma DiscreteCat_rew_id {A : Type} {x y : A} (H : x = y) :
  fmap[Discrete_Compare (DiscreteCat A)] H = H.
Proof. destruct H; reflexivity. Qed.

(* Hence every [DiscreteCat A] is rigid, for every [A], with no hypothesis —
   the gain over phrasing the theorem with UIP. *)
Lemma DiscreteCat_Rigid (A : Type) : DiscreteRigid (DiscreteCat A).
Proof.
  intros x y H H' e.
  rewrite <- (DiscreteCat_rew_id H), <- (DiscreteCat_rew_id H').
  exact e.
Qed.

(** ** The reconstruction functor and the correspondence *)

Section Reconstruction.

Context {C : Category}.
Context (Dis : Discrete C).
Context (rigid : DiscreteRigid C).

(* The equality proof that [Discrete] attaches to an arrow. *)
Definition disc_eq {x y : C} (f : x ~> y) : x = y := `1 (Dis x y f).

(* ... and its defining property, in comparison-functor form. *)
Lemma disc_eq_spec {x y : C} (f : x ~> y) :
  f ≈ fmap[Discrete_Compare C] (disc_eq f).
Proof. exact (`2 (Dis x y f)). Qed.

(* The reconstruction functor [C ⟶ DiscreteCat (obj C)]: the identity on
   objects, sending an arrow to its [Discrete] witness.  Each of the three
   functor laws is an equation between equality proofs, and each is discharged
   by rigidity from the corresponding law in [C]. *)
Definition Discrete_Reconstruct : C ⟶ DiscreteCat C.
Proof using C Dis rigid.
  unshelve refine (@Build_Functor C (DiscreteCat C)
    (fun x : C => x) (fun (x y : C) (f : x ~> y) => disc_eq f) _ _ _).
  - intros x y; proper.
    apply rigid.
    now rewrite <- !disc_eq_spec.
  - intros x.
    apply rigid.
    rewrite <- disc_eq_spec.
    now rewrite fmap_id.
  - intros x y z f g.
    apply rigid.
    rewrite fmap_comp.
    now rewrite <- !disc_eq_spec.
Defined.

(* Mac Lane's "determined by its set of objects", on the nose: reconstruction
   and comparison are mutually inverse in [StrictCat].  Both object maps are
   the identity, so both strict-equality witnesses are [eq_refl] and only the
   morphism coherence has content.  The [from ∘ to] coherence is exactly the
   [Discrete] witness property; the [to ∘ from] coherence is a further appeal
   to rigidity. *)
Definition Discrete_iso : C ≅[StrictCat] DiscreteCat C.
Proof using C Dis rigid.
  unshelve refine (@Build_Isomorphism StrictCat C (DiscreteCat C)
    Discrete_Reconstruct (Discrete_Compare C) _ _).
  - exists (fun _ => eq_refl).
    intros x y f; simpl.
    apply rigid.
    now rewrite <- disc_eq_spec.
  - exists (fun _ => eq_refl).
    intros x y f.
    symmetry; exact (disc_eq_spec f).
Defined.

(* The same correspondence read in [Cat], where functors are compared up to
   natural isomorphism.  This is strictly weaker and is recorded only for
   convenience: it does not relax the hypothesis. *)
Definition Discrete_iso_Cat : C ≅[Cat] DiscreteCat C :=
  @Build_Isomorphism Cat C (DiscreteCat C)
    Discrete_Reconstruct (Discrete_Compare C)
    (strict_equiv_implies_fun_equiv _ _ (iso_to_from Discrete_iso))
    (strict_equiv_implies_fun_equiv _ _ (iso_from_to Discrete_iso)).

End Reconstruction.

(** ** The iso-robust restatement *)

(* Every arrow of a discrete category is invertible; no hypothesis needed. *)
Lemma Discrete_invertible (C : Category) (D : Discrete C)
  (x y : C) (f : x ~> y) :
  ∃ g : y ~> x, (f ∘ g ≈ id) ∧ (g ∘ f ≈ id).
Proof.
  destruct (D x y f) as [H Hf].
  exists (rew [fun z : C => y ~{C}~> z] (eq_sym H) in id).
  split; rewrite Hf.
  - apply rew_id_iso_from.
  - apply rew_id_iso_to.
Qed.

(* The equivalence-respecting reading of discreteness: hom-setoids are
   subsingletons and every arrow is invertible.  No object equality appears. *)
Definition DiscreteUpToIso (C : Category) : Type :=
  (∀ (x y : C) (f g : x ~> y), f ≈ g)
    ∧ (∀ (x y : C) (f : x ~> y), ∃ g : y ~> x, (f ∘ g ≈ id) ∧ (g ∘ f ≈ id)).

(* [Discrete] implies the restatement once the objects have UIP: the two
   witnesses attached to two parallel arrows are then the same proof. *)
Theorem Discrete_DiscreteUpToIso (C : Category) (D : Discrete C)
  (uip : ∀ (x y : C) (H H' : x = y), H = H') : DiscreteUpToIso C.
Proof.
  split.
  - intros x y f g.
    destruct (D x y f) as [H Hf], (D x y g) as [H' Hg].
    rewrite Hf, Hg, (uip x y H H').
    reflexivity.
  - apply Discrete_invertible, D.
Qed.

(* For the constructed discrete categories the restatement is *exactly* UIP on
   the underlying type: its subsingleton clause is that statement verbatim,
   because the hom-setoid is strict equality of equality proofs.  Compare
   [DiscreteCat_Discrete], which holds with no hypothesis at all. *)
Theorem DiscreteUpToIso_DiscreteCat (A : Type) :
  DiscreteUpToIso (DiscreteCat A) ↔ (∀ (x y : A) (p q : x = y), p = q).
Proof.
  split.
  - intros [sub _] x y p q; exact (sub x y p q).
  - intros uip; split.
    + intros x y f g; exact (uip x y f g).
    + intros x y f.
      exists (eq_sym f).
      split; destruct f; reflexivity.
Qed.

(* Hence no general implication from [Discrete] to the restatement can be
   proven: it would decide UIP for every type, which Rocq's logic leaves open.
   This is the precise sense in which the restatement is *not* equivalent to
   the existing predicate. *)
Theorem Discrete_DiscreteUpToIso_forces_UIP
  (K : ∀ C : Category, Discrete C → DiscreteUpToIso C) :
  ∀ (A : Type) (x y : A) (p q : x = y), p = q.
Proof.
  intro A.
  apply (fst (DiscreteUpToIso_DiscreteCat A)).
  apply K, DiscreteCat_Discrete.
Qed.

(** ** The indiscrete category separates the two predicates *)

(* One arrow between any two objects; the codiscrete/indiscrete right adjoint
   to the underlying-set functor, included here only as the separating
   witness. *)
(* The same reverse-mathematics argument for the PRIMARY hypothesis: if every
   [Discrete] category were [DiscreteRigid], UIP would hold for every type.
   The countermodel makes the premise of rigidity vacuous: objects [A],
   morphisms equality proofs, but the hom-setoid INDISCRETE, so that any two
   parallel arrows are equivalent.  Such a category is [Discrete] -- the
   morphism is its own witness -- while its rigidity is literally UIP on [A].
   Hence [DiscreteRigid] is a genuine extra hypothesis of [Discrete_iso], not
   a deficiency of its proof. *)
Program Definition Blurry (A : Type) : Category := {|
  obj     := A;
  hom     := fun x y => x = y;
  homset  := fun x y => {| equiv := fun _ _ => True |};
  id      := fun x => eq_refl;
  compose := fun x y z (g : y = z) (f : x = y) => eq_trans f g
|}.

Lemma Blurry_Discrete (A : Type) : Discrete (Blurry A).
Proof. intros x y f. exists f. exact I. Qed.

Lemma Blurry_Rigid_is_UIP (A : Type) :
  DiscreteRigid (Blurry A) → ∀ (x y : A) (p q : x = y), p = q.
Proof. intros r x y p q. exact (r x y p q I). Qed.

Theorem Discrete_DiscreteRigid_forces_UIP
  (K : ∀ C : Category, Discrete C → DiscreteRigid C) :
  ∀ (A : Type) (x y : A) (p q : x = y), p = q.
Proof.
  intros A. apply Blurry_Rigid_is_UIP. apply K, Blurry_Discrete.
Qed.

(* The binders are load-bearing, for the same reason as
   [DiscreteCat_Functor] (Instance/Discrete.v): declared bare, this
   minimized to [Indiscrete@{u} : Type@{u} → Category@{u Set Set}], pinning
   the hom and proof levels of the indiscrete category to [Set] and so
   pinning every limit taken over it.  The pin is INDEPENDENT of
   [DiscreteCat_Functor]'s — annotating that one does not touch this one,
   which is why Instance/Cat/Objects.v behaved differently
   while only one of the two donors was annotated.  (Both are annotated
   now, so both of those lines are plain [Check]s and both are accepted;
   an earlier revision of this sentence cited them,
   where they stood as [Fail Check]s before the PR "algebraic carriers
   are sets" (2026-09-17).)  The measured signature is

     Indiscrete@{o h p} : Type@{o} → Category@{o h p}
     (* o h p |= h <= eq_ind.u0 / h <= Logic_lemmas.equality.u0
                 / h <= eq_ind_r.u0 / h <= p *)

   — no literal [Set] anywhere, and [o] is now unconstrained.  [unit : Set]
   still inhabits the hom type, but cumulativity absorbs that silently: the
   constraint block records no lower bound on [h] at all. *)
Program Definition Indiscrete@{o h p} (A : Type@{o}) : Category@{o h p} := {|
  obj     := A;
  hom     := fun _ _ => unit;
  homset  := fun x y => Morphism_equality@{o h p} x y;
  id      := fun _ => tt;
  compose := fun _ _ _ _ _ => tt
|}.
(* All category laws are equations in [unit] and are discharged by the default
   obligation tactic. *)

(* It satisfies the restatement for every [A]: [unit] is a subsingleton and
   [tt] inverts [tt]. *)
Lemma Indiscrete_DiscreteUpToIso (A : Type) : DiscreteUpToIso (Indiscrete A).
Proof.
  split.
  - intros x y f g; now destruct f, g.
  - intros x y f; exists tt; split; reflexivity.
Qed.

(* But on [bool] it is not [Discrete]: the arrow [tt : true ~> false] would
   have to produce a proof of [true = false].  So the restatement does not
   imply the existing predicate either — the two are incomparable. *)
Lemma Indiscrete_bool_Discrete_absurd : Discrete (Indiscrete bool) → False.
Proof. intro D; destruct (D true false tt) as [H _]; discriminate. Qed.
