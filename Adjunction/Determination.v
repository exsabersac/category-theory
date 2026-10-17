Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Universal.Arrow.Dual.

Generalizable All Variables.

(*
    nLab:      https://ncatlab.org/nlab/show/adjoint+functor
    nLab:      https://ncatlab.org/nlab/show/universal+morphism
    Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors
    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
    Book: Awodey, "Category Theory", 2nd ed., §9.2 Corollary 9.5,

   本文件给出伴随相关构造与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)


Section CounitCouniversal.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

#[local] Existing Instance A.

(* Mac Lane §IV.1 Theorem 2, the converse leg: each counit component is a
   couniversal arrow, PACKAGED as one. *)
Definition adj_counit_couniversal (c : C) : CouniversalArrow c F.
Proof using A U.
  unshelve eapply (couniversal_arrow_from_UMP c F (U c) counit).
  intros d' f.
  unshelve eexists ((to adj[A] f)).
  - exact (snd (adj_univ_impl f (to adj[A] f)) (reflexivity _)).
  - intros v Hv.
    exact (fst (adj_univ_impl f v) Hv).
Defined.

Example adj_counit_couniversal_obj (c : C) :
  coarrow_obj (adj_counit_couniversal c) = U c := eq_refl.

Example adj_counit_couniversal_arrow (c : C) :
  coarrow (adj_counit_couniversal c) = @counit C D F U A c := eq_refl.

(*
   本节说明 Determination 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma adj_counit_couniversal_med (c : C) (d : D) (f : F d ~{C}~> c) :
  unique_obj (ump_couniversal_arrows (adj_counit_couniversal c) f)
    ≈ to adj[A] f.
Proof using A U.
  symmetry.
  exact (fst (adj_univ_impl f _)
             (unique_property
                (ump_couniversal_arrows (adj_counit_couniversal c) f))).
Qed.

Lemma adj_counit_factor_unique {x y : C} (f : x ~{C}~> y)
      (g : U x ~{D}~> U y) :
  f ∘ @counit C D F U A x ≈ @counit C D F U A y ∘ fmap[F] g →
  g ≈ fmap[U] f.
Proof using A U.
  intro Hg.
  rewrite <- (fst (adj_univ_impl (f ∘ counit) g) Hg).
  symmetry.
  apply fmap_to_adj_counit.
Qed.

End CounitCouniversal.

Section CounitRoundTrip.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

Definition counit_couniversal_family : ∀ c : C, CouniversalArrow c F :=
  adj_counit_couniversal A.

Definition right_adjoint_of_counit : C ⟶ D :=
  RightAdjointFunctorFromCouniversalArrows F counit_couniversal_family.

Definition adjunction_of_counit : F ⊣ right_adjoint_of_counit :=
  AdjunctionFromCouniversalArrows F counit_couniversal_family.

Example right_adjoint_of_counit_obj (c : C) :
  fobj[right_adjoint_of_counit] c = fobj[U] c := eq_refl.

Lemma adjunction_of_counit_counit (c : C) :
  @counit C D F right_adjoint_of_counit adjunction_of_counit c
    ≈ @counit C D F U A c.
Proof using A U.
  exact (counit_couniversal F counit_couniversal_family c).
Qed.

Lemma right_adjoint_of_counit_fmap {x y : C} (f : x ~{C}~> y) :
  fmap[right_adjoint_of_counit] f ≈ fmap[U] f.
Proof using A U.
  apply (adj_counit_factor_unique A).
  rewrite <- (adjunction_of_counit_counit x).
  rewrite <- (adjunction_of_counit_counit y).
  symmetry.
  exact (adj_counit_naturality adjunction_of_counit f).
Qed.

Lemma right_adjoint_of_counit_iso : right_adjoint_of_counit ≈ U.
Proof using A U.
  exists (fun c => iso_id).
  intros x y f; simpl.
  rewrite id_left, id_right.
  apply right_adjoint_of_counit_fmap.
Qed.

Lemma adjunction_of_counit_to {x : D} {y : C} (g : F x ~{C}~> y) :
  to adj[adjunction_of_counit] g ≈ to adj[A] g.
Proof using A U.
  symmetry.
  apply (fst (@adj_univ_impl C D F U A x y g _)).
  rewrite <- (adjunction_of_counit_counit y).
  exact (snd (@adj_univ_impl C D F right_adjoint_of_counit
                adjunction_of_counit x y g _) (reflexivity _)).
Qed.

Lemma adjunction_of_counit_from {x : D} {y : C} (h : x ~{D}~> U y) :
  from adj[adjunction_of_counit] h ≈ from adj[A] h.
Proof using A U.
  rewrite (@from_adj_counit C D F right_adjoint_of_counit
             adjunction_of_counit x y h).
  rewrite (@from_adj_counit C D F U A x y h).
  now rewrite (adjunction_of_counit_counit y).
Qed.

Lemma adjunction_of_counit_unit (d : D) :
  @unit C D F right_adjoint_of_counit adjunction_of_counit d
    ≈ @unit C D F U A d.
Proof using A U. exact (adjunction_of_counit_to id). Qed.

End CounitRoundTrip.

(** ** The other composite: couniversal arrows, adjunction, counit *)

Section CouniversalRoundTrip.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context (H : ∀ c : C, CouniversalArrow c F).

Example couniversal_of_counit_obj (c : C) :
  coarrow_obj (adj_counit_couniversal (AdjunctionFromCouniversalArrows F H) c)
    = coarrow_obj (H c) := eq_refl.

Lemma couniversal_of_counit_arrow (c : C) :
  coarrow (adj_counit_couniversal (AdjunctionFromCouniversalArrows F H) c)
    ≈ coarrow (H c).
Proof using H. exact (counit_couniversal F H c). Qed.

Lemma couniversal_of_counit_med (c : C) :
  cua_med (adj_counit_couniversal (AdjunctionFromCouniversalArrows F H) c)
          (H c) ≈ id.
Proof using H.
  apply cua_med_unique.
  rewrite fmap_id, id_right.
  symmetry.
  apply couniversal_of_counit_arrow.
Qed.

Lemma couniversal_of_counit_iso (c : C) :
  couniversal_arrow_iso
    (adj_counit_couniversal (AdjunctionFromCouniversalArrows F H) c) (H c)
    ≈ iso_id.
Proof using H.
  apply to_equiv_implies_iso_equiv; simpl.
  apply couniversal_of_counit_med.
Qed.

End CouniversalRoundTrip.

(** ** Mac Lane's first presentation: a natural unit whose every component
       is universal *)

Section UnitSide.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

Class UnitPresentation := {
  up_unit : Id[D] ⟹ U ◯ F;
  up_universal {d : D} {c : C} (f : d ~{D}~> U c) :
    ∃! g : F d ~{C}~> c, f ≈ fmap[U] g ∘ transform[up_unit] d
}.

Definition unit_presentation_of_adjunction (A : F ⊣ U) : UnitPresentation.
Proof.
  unshelve eapply Build_UnitPresentation.
  - unshelve eapply Build_Transform.
    + exact (fun d => @unit C D F U A d).
    + exact (fun x y f => adj_unit_naturality A f).
    + exact (fun x y f => symmetry (adj_unit_naturality A f)).
  - intros d c f; simpl.
    unshelve eexists (from adj[A] f).
    + rewrite <- (@to_adj_unit C D F U A d c (from adj[A] f)).
      symmetry.
      exact (@from_adj_comp_law C D F U A d c f).
    + intros v Hv.
      symmetry.
      apply (snd (@adj_univ C D F U A d c v f)).
      rewrite (@to_adj_unit C D F U A d c v).
      now symmetry.
Defined.

Definition adjunction_of_unit_presentation (P : UnitPresentation) : F ⊣ U.
Proof.
  unshelve eapply Build_Adjunction'.
  - intros d c.
    unshelve eapply Isomorphism.Build_Isomorphism.
    + unshelve eapply Sets.Build_SetoidMorphism.
      * exact (fun g => fmap[U] g ∘ transform[up_unit] d).
      * abstract (intros g1 g2 Hg; apply compose_respects;
                  [ exact (fmap_respects _ _ g1 g2 Hg) | reflexivity ]).
    + unshelve eapply Sets.Build_SetoidMorphism.
      * exact (fun f => unique_obj (up_universal f)).
      * abstract (intros f1 f2 Hf; apply uniqueness;
                  etransitivity; [ exact Hf
                                 | exact (unique_property (up_universal f2)) ]).
    + abstract (intro f; symmetry; exact (unique_property (up_universal f))).
    + abstract (intro g; apply uniqueness; reflexivity).
  - abstract (intros x y z f g; simpl;
              rewrite fmap_comp, <- comp_assoc;
              rewrite (@naturality _ _ _ _ up_unit _ _ g);
              now rewrite comp_assoc).
  - abstract (intros x y z f g; simpl;
              now rewrite fmap_comp, <- comp_assoc).
Defined.

(* Mac Lane's transpose formula, on the nose. *)
Example unit_presentation_transpose (P : UnitPresentation)
        {d : D} {c : C} (g : F d ~{C}~> c) :
  to adj[adjunction_of_unit_presentation P] g
    = fmap[U] g ∘ transform[up_unit] d := eq_refl.

Example unit_presentation_untranspose (P : UnitPresentation)
        {d : D} {c : C} (f : d ~{D}~> U c) :
  from adj[adjunction_of_unit_presentation P] f
    = unique_obj (up_universal f) := eq_refl.

End UnitSide.
