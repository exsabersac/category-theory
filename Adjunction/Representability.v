Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Opposite.
Require Import Category.Functor.Representable.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Theory.Universal.Element.

Generalizable All Variables.

(*
    nLab:      https://ncatlab.org/nlab/show/adjoint+functor
    nLab:      https://ncatlab.org/nlab/show/representable+functor
    Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors
    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
    Book: Riehl, "Category Theory in Context", Dover 2016, §4.4 -- the

   本文件给出伴随相关构造与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** From an adjunction to pointwise representability *)

Section Forward.

Context {C : Category}.
Context {D : Category}.
Context {F : C ⟶ D}.
Context {G : D ⟶ C}.
Context (A : F ⊣ G).

#[local] Existing Instance A.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition adj_unit_auniversal (c : C) : AUniversalArrow c G (F c).
Proof using A F G.
  unshelve econstructor.
  - exact unit.
  - intros d f.
    unshelve econstructor.
    + exact (from adj[A] f).
    + simpl.
      rewrite <- to_adj_unit.
      apply from_adj_comp_law.
    + simpl; intros v Hv.
      symmetry.
      apply (snd (adj_univ v f)).
      rewrite to_adj_unit.
      exact Hv.
Defined.

(* The comma-initial packaging, through the passage that makes the whole
   chain composable. *)
Definition adj_unit_universal (c : C) : UniversalArrow c G :=
  ua_of_aua (adj_unit_auniversal c).

(* Both readbacks survive the packaging, because
   [universal_arrow_from_UMP] builds the comma object as ((ttt, a); η) and
   the two projections return what they were given. *)
Example adj_unit_universal_obj (c : C) :
  @arrow_obj C D c G (adj_unit_universal c) = F c := eq_refl.

Example adj_unit_universal_arrow (c : C) :
  @arrow C D c G (adj_unit_universal c) = @unit D C F G A c := eq_refl.

(* Mac Lane's Hom_C(c, G−) with its universal element, then its
   representation.  Both steps are Theory/Universal/Element.v's, applied. *)
Definition adj_auniversal_element (c : C)
  : AUniversalElement (HomAfter G c) (F c) :=
  AUniversalElement_of_hom G c (adj_unit_auniversal c).

Definition adj_universal_element (c : C) : UniversalElement (HomAfter G c) :=
  UniversalElement_of_AUniversalElement (adj_auniversal_element c).

Definition adj_representable (c : C) : Representable (HomAfter G c) :=
  Representable_of_UniversalElement (adj_universal_element c).

Example adj_representable_obj (c : C) :
  @repr_obj D (HomAfter G c) (adj_representable c) = F c := eq_refl.

End Forward.

(** ** From pointwise representability to an adjunction *)

Section Converse.

Context {C : Category}.
Context {D : Category}.
Context (G : D ⟶ C).

(* A representation of Hom_C(c, G−) IS a universal arrow from c to G:
   read it as a universal element, then across
   [AUniversalArrow_of_hom].  No tactic is spent -- the whole passage is
   three applications. *)
Definition auniversal_of_representable
  (R : ∀ c : C, Representable (HomAfter G c)) (c : C)
  : AUniversalArrow c G (@repr_obj D (HomAfter G c) (R c)) :=
  AUniversalArrow_of_hom G c
    (AUniversalElement_of_UniversalElement
       (UniversalElement_of_Representable (R c))).

Definition universal_of_representable
  (R : ∀ c : C, Representable (HomAfter G c)) (c : C) : UniversalArrow c G :=
  ua_of_aua (auniversal_of_representable R c).

Example universal_of_representable_arrow
  (R : ∀ c : C, Representable (HomAfter G c)) (c : C) :
  @arrow C D c G (universal_of_representable R c)
    = @universal_arrow C D c G _ (auniversal_of_representable R c) := eq_refl.

Definition left_adjoint_of_representable
  (R : ∀ c : C, Representable (HomAfter G c)) : C ⟶ D :=
  LeftAdjointFunctorFromUniversalArrows G (universal_of_representable R).

Definition adjunction_of_representable
  (R : ∀ c : C, Representable (HomAfter G c))
  : left_adjoint_of_representable R ⊣ G :=
  AdjunctionFromUniversalArrows G (universal_of_representable R).

(* The check Mac Lane's phrasing calls for: the left adjoint built from a
   family of representations agrees ON OBJECTS with the chosen
   representing objects, definitionally. *)
Example left_adjoint_of_representable_obj
  (R : ∀ c : C, Representable (HomAfter G c)) (c : C) :
  fobj[left_adjoint_of_representable R] c
    = @repr_obj D (HomAfter G c) (R c) := eq_refl.

(*
   本节说明 Representability 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example adjunction_of_representable_unit_residue
  (R : ∀ c : C, Representable (HomAfter G c)) (c : C) :
  @unit D C (left_adjoint_of_representable R) G
        (adjunction_of_representable R) c
    = fmap[G] (id{D}) ∘ @universal_arrow C D c G _
                          (auniversal_of_representable R c) := eq_refl.

Lemma adjunction_of_representable_unit
  (R : ∀ c : C, Representable (HomAfter G c)) (c : C) :
  @unit D C (left_adjoint_of_representable R) G
        (adjunction_of_representable R) c
    ≈ @universal_arrow C D c G _ (auniversal_of_representable R c).
Proof.
  rewrite adjunction_of_representable_unit_residue, fmap_id.
  apply id_left.
Qed.

End Converse.

(** ** The round trip *)

Section RoundTrip.

Context {C : Category}.
Context {D : Category}.
Context {F : C ⟶ D}.
Context {G : D ⟶ C}.
Context (A : F ⊣ G).

(* Reading an adjunction out as a family of representations and building
   the left adjoint back returns F on objects, definitionally. *)
Example representable_roundtrip_obj (c : C) :
  fobj[left_adjoint_of_representable G (adj_representable A)] c = F c
  := eq_refl.

(* On arrows the same residue appears, for the same reason. *)
Example representable_roundtrip_arrow_residue (c : C) :
  @arrow C D c G (universal_of_representable G (adj_representable A) c)
    = fmap[G] (id{D}) ∘ @unit D C F G A c := eq_refl.

Lemma representable_roundtrip_arrow (c : C) :
  @arrow C D c G (universal_of_representable G (adj_representable A) c)
    ≈ @unit D C F G A c.
Proof.
  rewrite representable_roundtrip_arrow_residue, fmap_id.
  apply id_left.
Qed.

End RoundTrip.

(** ** Mac Lane §IV.1 Corollary 2 as a biconditional *)

Section Biconditional.

Context {C : Category}.
Context {D : Category}.
Context (G : D ⟶ C).

(* Stated over an arbitrary G, with no adjunction in the ambient
   context -- the point of the sectioning. *)
Theorem adjunction_iff_pointwise_representable :
  (∀ c : C, Representable (HomAfter G c)) ↔ { L : C ⟶ D & L ⊣ G }.
Proof.
  split.
  - intro R.
    exact (left_adjoint_of_representable G R; adjunction_of_representable G R).
  - intros [L AL] c.
    exact (adj_representable AL c).
Defined.

End Biconditional.

(** ** The dual orientation (Mac Lane §IV.1 Exercise 1) *)

Section Dual.

Context {C : Category}.
Context {D : Category}.
Context (F : C ⟶ D).

(* d ↦ Hom_D(F d, a), as a functor C^op ⟶ Sets.  It is [HomAfter] at the
   opposite functor: the value at d is Hom_{D^op}(a, F d), which is
   Hom_D(F d, a). *)
Definition CoHomBefore (a : D) : C^op ⟶ Sets :=
  HomAfter (Opposite_Functor F) a.

(* [CouniversalArrow a F] is by definition the [UniversalArrow] in the
   opposite categories that [universal_of_representable] returns there, so
   this is instantiation and nothing else. *)
Definition couniversal_of_corepresentable
  (R : ∀ a : D, Representable (CoHomBefore a)) (a : D)
  : CouniversalArrow a F :=
  universal_of_representable (Opposite_Functor F) R a.

Definition right_adjoint_of_corepresentable
  (R : ∀ a : D, Representable (CoHomBefore a)) : D ⟶ C :=
  RightAdjointFunctorFromCouniversalArrows F
    (couniversal_of_corepresentable R).

Definition adjunction_of_corepresentable
  (R : ∀ a : D, Representable (CoHomBefore a))
  : F ⊣ right_adjoint_of_corepresentable R :=
  AdjunctionFromCouniversalArrows F (couniversal_of_corepresentable R).

Example right_adjoint_of_corepresentable_obj
  (R : ∀ a : D, Representable (CoHomBefore a)) (a : D) :
  fobj[right_adjoint_of_corepresentable R] a
    = @repr_obj (C^op) (CoHomBefore a) (R a) := eq_refl.

End Dual.

Section DualForward.

Context {C : Category}.
Context {D : Category}.
Context {F : C ⟶ D}.
Context {G : D ⟶ C}.
Context (A : F ⊣ G).

(* The forward leg dualizes by instantiating [adj_representable] at the
   opposite adjunction; [Opposite_Adjunction] carries [F ⊣ G] to
   [Opposite_Functor G ⊣ Opposite_Functor F]. *)
Definition adj_corepresentable (a : D) : Representable (CoHomBefore F a) :=
  adj_representable (Opposite_Adjunction F G A) a.

Example adj_corepresentable_obj (a : D) :
  @repr_obj (C^op) (CoHomBefore F a) (adj_corepresentable a) = G a := eq_refl.

End DualForward.

Section DualBiconditional.

Context {C : Category}.
Context {D : Category}.
Context (F : C ⟶ D).

Theorem coadjunction_iff_pointwise_representable :
  (∀ a : D, Representable (CoHomBefore F a)) ↔ { R : D ⟶ C & F ⊣ R }.
Proof.
  split.
  - intro R.
    exact (right_adjoint_of_corepresentable F R;
           adjunction_of_corepresentable F R).
  - intros [R AR] a.
    exact (adj_corepresentable AR a).
Defined.

End DualBiconditional.

(** ** Uniqueness of the extension *)

Section Uniqueness.

Context {C : Category}.
Context {D : Category}.
Context (G : D ⟶ C).
Context (L : C ⟶ D).
Context (H : ∀ c : C, AUniversalArrow c G (L c)).

(* Naturality of the family in c: the unit square. *)
Definition UnitNatural : Type :=
  ∀ (x y : C) (f : x ~{C}~> y),
    fmap[G] (fmap[L] f) ∘ @universal_arrow C D x G (L x) (H x)
      ≈ @universal_arrow C D y G (L y) (H y) ∘ f.

(*
   本节说明 Representability 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma unit_square_forces_fmap {x y : C} (f : x ~{C}~> y)
      (g : L x ~{D}~> L y)
      (Hf : fmap[G] (fmap[L] f) ∘ @universal_arrow C D x G (L x) (H x)
              ≈ @universal_arrow C D y G (L y) (H y) ∘ f)
      (Hg : fmap[G] g ∘ @universal_arrow C D x G (L x) (H x)
              ≈ @universal_arrow C D y G (L y) (H y) ∘ f) :
  fmap[L] f ≈ g.
Proof.
  pose (W := @universal_arrow_universal C D x G (L x) (H x) (L y)
               (@universal_arrow C D y G (L y) (H y) ∘ f)).
  rewrite <- (uniqueness W _ Hf).
  exact (uniqueness W _ Hg).
Qed.

(*
   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition adjunction_of_natural_universal (N : UnitNatural) : L ⊣ G.
Proof.
  unshelve eapply Build_Adjunction'.
  - intros x y.
    unshelve eapply Isomorphism.Build_Isomorphism.
    + unshelve eapply Sets.Build_SetoidMorphism.
      * exact (fun g => fmap[G] g ∘ @universal_arrow C D x G (L x) (H x)).
      * abstract (proper; now rewrite X).
    + unshelve eapply Sets.Build_SetoidMorphism.
      * exact (fun f =>
                 unique_obj (@universal_arrow_universal C D x G (L x)
                               (H x) y f)).
      * abstract (proper;
          apply (uniqueness
                   (@universal_arrow_universal C D x G (L x) (H x) y x0));
          rewrite X;
          exact (unique_property
                   (@universal_arrow_universal C D x G (L x) (H x) y y0))).
    + abstract (intro f;
        exact (unique_property
                 (@universal_arrow_universal C D x G (L x) (H x) y f))).
    + abstract (simpl; intro g;
        apply (uniqueness
                 (@universal_arrow_universal C D x G (L x) (H x) y _));
        reflexivity).
  - abstract (intros x y z f g; simpl;
      rewrite fmap_comp, <- comp_assoc, (N x y g), comp_assoc;
      reflexivity).
  - abstract (intros x y z f g; simpl;
      rewrite fmap_comp, <- comp_assoc; reflexivity).
Defined.

(* Only up to [≈], and for the residue reason recorded in the header. *)
Lemma adjunction_of_natural_universal_unit (N : UnitNatural) (c : C) :
  @unit D C L G (adjunction_of_natural_universal N) c
    ≈ @universal_arrow C D c G (L c) (H c).
Proof.
  unfold unit; simpl.
  rewrite fmap_id.
  apply id_left.
Qed.

(* The weaker, object-assignment-free comparison. *)
Corollary natural_universal_left_adjoint_iso (N : UnitNatural)
          (L' : C ⟶ D) (AL' : L' ⊣ G) : L ≈ L'.
Proof.
  exact (left_adjoint_iso G L L' (adjunction_of_natural_universal N) AL').
Qed.

End Uniqueness.

Section UniquenessOfRepresentableExtension.

Context {C : Category}.
Context {D : Category}.
Context (G : D ⟶ C).
Context (R : ∀ c : C, Representable (HomAfter G c)).

(* The induced functor's arrow action is defined BY the factorization, so
   naturality is that factorization's own property read backwards. *)
Lemma left_adjoint_of_representable_natural :
  UnitNatural G (left_adjoint_of_representable G R)
    (auniversal_of_representable G R).
Proof.
  intros x y f; simpl.
  symmetry.
  exact (unique_property
           (ump_universal_arrows (universal_of_representable G R x)
              (@arrow C D y G (universal_of_representable G R y) ∘ f))).
Qed.

Theorem left_adjoint_of_representable_fmap_unique {x y : C}
        (f : x ~{C}~> y)
        (g : @repr_obj D (HomAfter G x) (R x)
               ~{D}~> @repr_obj D (HomAfter G y) (R y))
        (Hg : fmap[G] g
                ∘ @universal_arrow C D x G _ (auniversal_of_representable G R x)
              ≈ @universal_arrow C D y G _ (auniversal_of_representable G R y)
                ∘ f) :
  fmap[left_adjoint_of_representable G R] f ≈ g.
Proof.
  exact (unit_square_forces_fmap G (left_adjoint_of_representable G R)
           (auniversal_of_representable G R) f g
           (left_adjoint_of_representable_natural x y f) Hg).
Qed.

(* The weaker statement again, at the induced functor. *)
Corollary left_adjoint_of_representable_iso (L : C ⟶ D) (AL : L ⊣ G) :
  L ≈ left_adjoint_of_representable G R.
Proof.
  exact (left_adjoint_iso G L (left_adjoint_of_representable G R) AL
           (adjunction_of_representable G R)).
Qed.

End UniquenessOfRepresentableExtension.
