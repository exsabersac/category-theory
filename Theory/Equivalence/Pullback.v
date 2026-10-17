Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Structure.Pullback.

Generalizable All Variables.

(*
 nLab:      https://ncatlab.org/nlab/show/equivalence+of+categories
 Wikipedia: https://en.wikipedia.org/wiki/Equivalence_of_categories

   本文件给出拉回相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Joint monicity of a pullback's projections *)

(*
   The standard consequence of the 普遍性质: two maps into the

   本节说明相关定义、性质与动机。 apex agreeing after both projections are equal. Stated separately because transport's uniqueness clause consumes it C while working D.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma is_pullback_jointly_monic {C : Category} {x y z : C}
      {f : x ~> z} {g : y ~> z} {P : C} {p1 : P ~> x} {p2 : P ~> y}
      (HP : IsPullback f g P p1 p2) (Q : C) (a b : Q ~> P) :
  p1 ∘ a ≈ p1 ∘ b → p2 ∘ a ≈ p2 ∘ b → a ≈ b.
Proof.
  intros H1 H2.
  assert (Hc : f ∘ (p1 ∘ a) ≈ g ∘ (p2 ∘ a)).
  { rewrite !comp_assoc.
    now rewrite (is_pullback_commutes HP). }
  pose proof (is_pullback_ump HP Q (p1 ∘ a) (p2 ∘ a) Hc) as U.
  transitivity (unique_obj U).
  - symmetry.
    apply (uniqueness U); split; reflexivity.
  - apply (uniqueness U); split.
    + now symmetry.
    + now symmetry.
Qed.

Section PullbackTransport.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context (E : @EquivalenceOfCategories C D F).

(* The two corrected legs of the transported square. *)
Definition pullback_transport_leg {d : D} {P : C}
           (p : P ~> @quasi_inverse C D F E d) : F P ~> d :=
  to (@equivalence_counit_at C D F E d) ∘ fmap[F] p.

(* Any two maps into F P that agree after both corrected legs agree, when
   the two uncorrected legs are jointly monic downstairs.  This is the
   whole content of the uniqueness clause below. *)
Lemma pullback_transport_jointly_monic {x y : D} {P : C}
      {p1 : P ~> @quasi_inverse C D F E x}
      {p2 : P ~> @quasi_inverse C D F E y}
      (JM : ∀ (Z : C) (a b : Z ~> P),
              p1 ∘ a ≈ p1 ∘ b → p2 ∘ a ≈ p2 ∘ b → a ≈ b)
      {Q : D} (v w : Q ~> F P) :
  pullback_transport_leg p1 ∘ v ≈ pullback_transport_leg p1 ∘ w →
  pullback_transport_leg p2 ∘ v ≈ pullback_transport_leg p2 ∘ w →
  v ≈ w.
Proof.
  intros H1 H2.
  (* Cancel the counit isomorphisms, then apply the faithful
     quasi-inverse. *)
  apply (fmap_inj (Faithful := Equivalence_Inverse_Faithful E)).
  (* The unit at P is invertible, so it suffices to compare after
     [from (unit at P)]. *)
  apply (monic (Monic := iso_from_monic
                  (@equivalence_unit_at C D F E P))).
  (* Reduce to the two projections downstairs. *)
  apply JM.
  - apply (monic (Monic := iso_to_monic
                    (@equivalence_unit_at C D F E
                       (@quasi_inverse C D F E x)))).
    rewrite !comp_assoc.
    rewrite <- !(equivalence_unit_conjugate p1).
    rewrite <- !fmap_comp.
    apply fmap_respects.
    unfold pullback_transport_leg in H1.
    apply (monic (Monic := iso_to_monic
                    (@equivalence_counit_at C D F E x))).
    rewrite !comp_assoc.
    exact H1.
  - apply (monic (Monic := iso_to_monic
                    (@equivalence_unit_at C D F E
                       (@quasi_inverse C D F E y)))).
    rewrite !comp_assoc.
    rewrite <- !(equivalence_unit_conjugate p2).
    rewrite <- !fmap_comp.
    apply fmap_respects.
    unfold pullback_transport_leg in H2.
    apply (monic (Monic := iso_to_monic
                    (@equivalence_counit_at C D F E y))).
    rewrite !comp_assoc.
    exact H2.
Qed.

(** ** The apex-pinned transport *)

Lemma IsPullback_transport {x y z : D} {f : x ~> z} {g : y ~> z}
      {P : C}
      {p1 : P ~> @quasi_inverse C D F E x}
      {p2 : P ~> @quasi_inverse C D F E y}
      (HP : IsPullback (fmap[@quasi_inverse C D F E] f)
                       (fmap[@quasi_inverse C D F E] g) P p1 p2) :
  IsPullback f g (F P)
    (pullback_transport_leg p1) (pullback_transport_leg p2).
Proof.
  constructor.
  - (* the corrected square commutes: counit naturality on both sides *)
    unfold pullback_transport_leg.
    rewrite !comp_assoc.
    rewrite <- (equivalence_counit_to_natural f).
    rewrite <- (equivalence_counit_to_natural g).
    rewrite <- !comp_assoc, <- !fmap_comp.
    apply compose_respects; [reflexivity|].
    apply fmap_respects.
    exact (is_pullback_commutes HP).
  - intros Q q1 q2 Hq.
    (* transport the competing cone into C with the quasi-inverse *)
    assert (Hq' : fmap[@quasi_inverse C D F E] f
                    ∘ fmap[@quasi_inverse C D F E] q1
                  ≈ fmap[@quasi_inverse C D F E] g
                    ∘ fmap[@quasi_inverse C D F E] q2).
    { rewrite <- !fmap_comp.
      now apply fmap_respects. }
    destruct (is_pullback_ump HP (@quasi_inverse C D F E Q)
                (fmap[@quasi_inverse C D F E] q1)
                (fmap[@quasi_inverse C D F E] q2) Hq') as [u [U1 U2] Uu].
    unshelve refine {| unique_obj :=
      fmap[F] u ∘ from (@equivalence_counit_at C D F E Q) |}.
    + split; unfold pullback_transport_leg.
      * rewrite <- !comp_assoc, (comp_assoc (fmap[F] p1)), <- fmap_comp.
        rewrite U1, comp_assoc.
        rewrite (equivalence_counit_to_natural q1).
        rewrite <- comp_assoc, iso_to_from.
        apply id_right.
      * rewrite <- !comp_assoc, (comp_assoc (fmap[F] p2)), <- fmap_comp.
        rewrite U2, comp_assoc.
        rewrite (equivalence_counit_to_natural q2).
        rewrite <- comp_assoc, iso_to_from.
        apply id_right.
    + intros v [V1 V2].
      apply (pullback_transport_jointly_monic
               (is_pullback_jointly_monic HP)).
      * rewrite V1.
        unfold pullback_transport_leg.
        rewrite <- !comp_assoc, (comp_assoc (fmap[F] p1)), <- fmap_comp.
        rewrite U1, comp_assoc.
        rewrite (equivalence_counit_to_natural q1).
        rewrite <- comp_assoc, iso_to_from.
        now rewrite id_right.
      * rewrite V2.
        unfold pullback_transport_leg.
        rewrite <- !comp_assoc, (comp_assoc (fmap[F] p2)), <- fmap_comp.
        rewrite U2, comp_assoc.
        rewrite (equivalence_counit_to_natural q2).
        rewrite <- comp_assoc, iso_to_from.
        now rewrite id_right.
Qed.

(** ** The packaged transport *)

Definition HasPullbacks_transport (HP : @HasPullbacks C) :
  @HasPullbacks D :=
  {| pullback := fun x y z f g =>
       is_pullback_pullback
         (IsPullback_transport
            (pullback_is_pullback _ _
               (@pullback C HP _ _ _
                  (fmap[@quasi_inverse C D F E] f)
                  (fmap[@quasi_inverse C D F E] g)))) |}.

(* The transported pullback object is the image of the one chosen
   downstairs, on the nose. *)
Example HasPullbacks_transport_obj (HP : @HasPullbacks C)
        {x y z : D} (f : x ~> z) (g : y ~> z) :
  Pull f g (@pullback D (HasPullbacks_transport HP) x y z f g)
    = F (Pull _ _ (@pullback C HP _ _ _
                     (fmap[@quasi_inverse C D F E] f)
                     (fmap[@quasi_inverse C D F E] g)))
  := eq_refl.

End PullbackTransport.
