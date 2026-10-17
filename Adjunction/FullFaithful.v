Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Transfer.
Require Import Category.Adjunction.Fullness.

Generalizable All Variables.

(** * Mac Lane §IV.3 Theorem 1: fullness and faithfulness through ε *)

(*
   本文件给出范畴等价的经典刻画：函子是等价当且仅当它全、忠实且本质满射（本库中为带选择的分裂版本，两个方向均可构造）。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------ *)
(** ** A packaging lemma: split monic + epi ⟹ invertible *)

(* Theory/Isomorphism.v's [Epic_Section_Iso] already runs the
   cancellation argument, but it concludes with the object-level
   [Isomorphism].  This repackages it as the predicate [IsIsomorphism]
   that Theorem 1(iii) is stated with, reusing that instance for the one
   law ([f ∘ section ≈ id]) that [Section] does not carry as a field;
   the other law IS [section_comp]. *)

Definition Epic_Section_IsIsomorphism {E : Category} {x y : E}
           {f : x ~> y} (s : Section f) (e : Epic f) : IsIsomorphism f :=
  {| two_sided_inverse := @section E x y f s
   ; is_right_inverse  := iso_to_from (@Epic_Section_Iso E x y f s e)
   ; is_left_inverse   := @section_comp E x y f s |}.

Section FullFaithful.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context `{A : F ⊣ U}.

Notation "'η' x" := (@unit C D F U A x)
  (at level 9, only parsing).
Notation "'ε' x" := (@counit C D F U A x)
  (at level 9, only parsing).
Notation "⌊ f ⌋" := (to (@adj C D F U A _ _) f) (only parsing).
Notation "⌈ f ⌉" := (from (@adj C D F U A _ _) f) (only parsing).

(* ------------------------------------------------------------------ *)
(** ** (A) The bridge: Mac Lane's composite is precomposition with ε *)

(* "Apply the Yoneda Lemma to the natural transformation (arrow function
   of G followed by the adjunction) A(a,c) → X(Ga,Gc) → A(FGa,c)."  Read
   in this library's vocabulary that composite is
   `g ↦ ⌈fmap[U] g⌉`, and the identification below says it is
   precomposition with ε_a.  It is one rewrite of [fmap_to_adj_counit]
   followed by one cancellation. *)

Lemma counit_precomp_is_from_adj_fmap_U {a c : C} (g : a ~> c) :
  g ∘ ε a ≈ ⌈ fmap[U] g ⌉.
Proof.
  rewrite (@fmap_to_adj_counit C D F U A a c g).
  symmetry.
  exact (@to_adj_comp_law C D F U A (U a) c (g ∘ ε a)).
Qed.

(* ... and the composite IS the component of the transfer transformation
   at ε_a, on the nose.  Deliberate strictness: this is what makes the
   transfer lemma applicable without a comparison map. *)

Example transfer_at_counit_is_precomp {a c : C} (g : a ~> c) :
  transform[hom_transfer (ε a)] c g = g ∘ ε a := eq_refl.

(* The other orientation, for readers who prefer Mac Lane's arrow: U's
   arrow map is the transfer followed by the forward transpose. *)

Lemma fmap_U_is_transfer_then_transpose {a c : C} (g : a ~> c) :
  fmap[U] g ≈ ⌊ transform[hom_transfer (ε a)] c g ⌋.
Proof. exact (@fmap_to_adj_counit C D F U A a c g). Qed.

(* ------------------------------------------------------------------ *)
(** ** (B) Theorem 1 (i): faithful ⟺ every counit component is epi *)

(* Faithfulness makes every component of the transfer at ε_a injective:
   two arrows out of a agreeing after ε_a have the same U-image, by the
   bridge, hence are equal. *)

Definition counit_transfer_monic_of_faithful (HU : Faithful U) (a : C) :
  @Monic ([C, Sets]) _ _ (hom_transfer (ε a)).
Proof.
  apply pointwise_monic_is_monic; intro c.
  apply (fst (injectivity_is_monic (transform[hom_transfer (ε a)] c))).
  intros g1 g2 Heq.
  assert (Heq' : g1 ∘ ε a ≈ g2 ∘ ε a) by exact Heq.
  apply (@fmap_inj C D U HU a c).
  rewrite (@fmap_to_adj_counit C D F U A a c g1).
  rewrite (@fmap_to_adj_counit C D F U A a c g2).
  now rewrite Heq'.
Defined.

(* ... and the lemma turns that into epicness of ε_a. *)

Definition counit_epic_of_faithful (HU : Faithful U) (a : C) :
  Epic (ε a) :=
  epic_of_hom_transfer_monic (ε a)
    (counit_transfer_monic_of_faithful HU a).

(* Conversely, epicness of every ε_a makes U faithful: the lemma turns it
   into monicity of the transfer, hence injectivity of each component,
   and the bridge carries `fmap[U] f ≈ fmap[U] g` to
   `f ∘ ε ≈ g ∘ ε`. *)

Definition faithful_of_counit_epic (H : ∀ a : C, Epic (ε a)) :
  Faithful U.
Proof.
  constructor; intros x y f g Hfg.
  apply (snd (injectivity_is_monic (transform[hom_transfer (ε x)] y))
             (sets_functor_monic_pointwise (hom_transfer (ε x))
                (hom_transfer_monic_of_epic (ε x) (H x)) y) f g).
  change (f ∘ ε x ≈ g ∘ ε x).
  rewrite (counit_precomp_is_from_adj_fmap_U f).
  rewrite (counit_precomp_is_from_adj_fmap_U g).
  now rewrite Hfg.
Defined.

Definition right_adjoint_faithful_iff_counit_epic :
  Faithful U ↔ (∀ a : C, Epic (ε a)).
Proof.
  split.
  - exact counit_epic_of_faithful.
  - exact faithful_of_counit_epic.
Defined.

(* ------------------------------------------------------------------ *)
(** ** (C) Theorem 1 (ii): full ⟺ every counit component is split monic *)

(* Mac Lane's route for the forward direction: fullness makes every
   component of the transfer SURJECTIVE, the preimage of k being the
   U-preimage of its transpose.  Shipped even though the headline's
   forward half consumes the cheaper #368 donor, so that the book's proof
   is present in all four directions. *)

Definition counit_transfer_epic_of_full (HU : Full U) (a : C) :
  @Epic ([C, Sets]) _ _ (hom_transfer (ε a)).
Proof.
  apply pointwise_epic_is_epic; intro c.
  apply (fst (surjectivity_is_epic (transform[hom_transfer (ε a)] c))).
  intro k.
  exists (@prefmap C D U HU a c ⌊k⌋).
  change (@prefmap C D U HU a c ⌊k⌋ ∘ ε a ≈ k).
  rewrite (counit_precomp_is_from_adj_fmap_U
             (@prefmap C D U HU a c ⌊k⌋)).
  rewrite (@fmap_sur C D U HU a c ⌊k⌋).
  exact (@to_adj_comp_law C D F U A (U a) c k).
Defined.

Definition counit_section_via_transfer (HU : Full U) (a : C) :
  Section (ε a) :=
  section_of_hom_transfer_epic (ε a) (counit_transfer_epic_of_full HU a).

(* The backward direction, through the lemma: a left inverse of ε_a makes
   the transfer epic, hence every component surjective, and the preimage
   of ⌈g⌉ is a U-preimage of g. *)

Definition full_data_of_counit_section (H : ∀ a : C, Section (ε a))
           {x y : C} (g : U x ~> U y) : { h : x ~> y & fmap[U] h ≈ g }.
Proof.
  destruct (epic_implies_surjective
              (transform[hom_transfer (ε x)] y)
              (sets_functor_epic_pointwise (hom_transfer (ε x))
                 (hom_transfer_epic_of_section (ε x) (H x)) y)
              ⌈g⌉) as [h Hh].
  exists h.
  assert (Hh' : h ∘ ε x ≈ ⌈g⌉) by exact Hh.
  rewrite (@fmap_to_adj_counit C D F U A x y h).
  rewrite Hh'.
  exact (@from_adj_comp_law C D F U A (U x) y g).
Defined.

Definition full_of_counit_section (H : ∀ a : C, Section (ε a)) : Full U :=
  {| prefmap := fun x y g => `1 (full_data_of_counit_section H g)
   ; fmap_sur := fun x y g => `2 (full_data_of_counit_section H g) |}.

Definition right_adjoint_full_iff_counit_split_monic :
  Full U ↔ (∀ a : C, Section (ε a)).
Proof.
  split.
  - exact (fun HU a => @counit_split_mono_of_full_right C D F U A HU a).
  - exact full_of_counit_section.
Defined.

(* ------------------------------------------------------------------ *)
(** ** (D) Theorem 1, conclusion: fully faithful ⟺ ε invertible *)

Definition right_adjoint_fully_faithful_iff_counit_iso :
  (Full U * Faithful U)%type ↔ (∀ a : C, IsIsomorphism (ε a)).
Proof.
  split.
  - intros [HFull HFaith] a.
    exact (Epic_Section_IsIsomorphism
             (@counit_split_mono_of_full_right C D F U A HFull a)
             (counit_epic_of_faithful HFaith a)).
  - intros H.
    split.
    + apply full_of_counit_section; intro a.
      exact {| section      := @two_sided_inverse C _ _ _ (H a)
             ; section_comp := @is_left_inverse C _ _ _ (H a) |}.
    + apply faithful_of_counit_epic; intro a.
      constructor; intros z g1 g2 Heq.
      rewrite <- (id_right g1), <- (id_right g2).
      rewrite <- (@is_right_inverse C _ _ _ (H a)).
      rewrite !comp_assoc.
      now rewrite Heq.
Defined.

(* ------------------------------------------------------------------ *)
(** ** (E) Mac Lane §IV.3 Exercise 5: the pin and a direct control *)

(* "prove that G is faithful if and only if φ⁻¹ carries epis to epis."
   φ⁻¹ is ⌈−⌉.  The BACKWARD direction is the cheap one: id is epi, and
   ⌈id⌉ IS the counit by definition (Theory/Adjunction.v), so (i)
   applies.  The identity `⌈id⌉ = ε a` is pinned as an [eq_refl] Example
   below.

   The exercise's biconditional [right_adjoint_faithful_iff_from_adj_epic]
   and the FORWARD half it rests on are NOT here but in section (F): the
   derivation the issue asks for reads [adj_monic] at the opposite
   adjunction, and [Opposite_Adjunction] is not in scope until the Require
   that opens (F).  What section (E) supplies is the definitional pin and
   a direct proof of the forward half, shipped as a control so that the
   opposite-adjunction derivation is not the only route in the file.  The
   two forward proofs are NOT compared: [Epic] is a one-field record whose
   field is a proof, so an [eq_refl] between them is refuted for the
   uninformative reason that the two proof terms differ, and there is no
   setoid on [Epic] in which to state anything weaker. *)

Example from_adj_id_is_counit (a : C) : ⌈ id[U a] ⌉ = ε a := eq_refl.

(* A direct proof of the forward direction, shipped as a control for the
   derivation that follows: transpose the cancellation hypothesis with
   [to_adj_nat_r], cancel the epi f, and finish with faithfulness. *)

Definition from_adj_epic_of_epic_direct (HU : Faithful U)
           {x : D} {a : C} (f : x ~> U a) (Hf : Epic f) : Epic ⌈f⌉.
Proof.
  constructor; intros c g h Heq.
  apply (@fmap_inj C D U HU a c).
  apply (@epic D x (U a) f Hf (U c)).
  assert (Hg : fmap[U] g ∘ f ≈ ⌊ g ∘ ⌈f⌉ ⌋).
  { rewrite (@to_adj_nat_r C D F U A x a c g ⌈f⌉).
    now rewrite (@from_adj_comp_law C D F U A x a f). }
  assert (Hh : fmap[U] h ∘ f ≈ ⌊ h ∘ ⌈f⌉ ⌋).
  { rewrite (@to_adj_nat_r C D F U A x a c h ⌈f⌉).
    now rewrite (@from_adj_comp_law C D F U A x a f). }
  rewrite Hg, Hh.
  exact (@to_adj_respects C D F U A x c _ _ Heq).
Defined.

End FullFaithful.

(* ------------------------------------------------------------------ *)
(** ** (F) Riehl's dual clauses, and Exercise 5's biconditional *)

(* Everything below the Require needs [Opposite_Adjunction]: Riehl's three
   dual clauses instantiate (i)-(iii) at it, and Mac Lane's Exercise 5
   reads [adj_monic] at it.  The three dual clauses are obtained by
   instantiating (i)-(iii) at the opposite adjunction.  Two definitional
   coincidences make that free, and both are recorded below at [eq_refl]:

       counit (Opposite_Adjunction F U A) x  =  unit A x
       unit   (Opposite_Adjunction F U A) a  =  counit A a

   — because `unit := ⌊id⌋` and `counit := ⌈id⌉` while the opposite
   adjunction is built by swapping [to] and [from] of the very same
   isomorphism (Adjunction/Opposite.v).  #368 measured this out of
   tree and pinned it nowhere; it is pinned here, and again in the probe.

   The remaining transport is the Monic/Epic and Section/Retraction
   quartets of Theory/Morphisms/Duality.v, and
   [Full_op]/[Faithful_op]/[Full_of_op]/[Faithful_of_op] of
   Functor/Opposite.v.  Six of those twelve are record literals
   with no proof content — the Monic/Epic quartet, which is what
   Duality.v's "one constructor application" sentence covers, and the
   two [Faithful] passages; the other six ([op_Retraction_of_Section]
   and its three siblings, [Full_op], [Full_of_op]) are [Program
   Definition]s whose single obligation is an [exact] of the other
   side's law at the swapped indices (Functor/Opposite.v says so
   of its own two).  None runs an argument of its own, so the dual
   clauses cost no argument here: no direct proof is cheaper and none is
   shipped.

   NOTATION HAZARD.  This Require is deferred to here on purpose; see
   ENGINEERING FINDINGS in the header. *)

Require Import Category.Adjunction.Opposite.

Section Duals.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context `{A : F ⊣ U}.

Notation "'η' x" := (@unit C D F U A x)
  (at level 9, only parsing).
Notation "'ε' x" := (@counit C D F U A x)
  (at level 9, only parsing).
Notation "⌊ f ⌋" := (to (@adj C D F U A _ _) f) (only parsing).
Notation "⌈ f ⌉" := (from (@adj C D F U A _ _) f) (only parsing).

(* The two definitional coincidences, at Leibniz equality. *)

Example op_counit_is_unit (x : D) :
  @counit (Opposite D) (Opposite C) (Opposite_Functor U)
          (Opposite_Functor F) (Opposite_Adjunction F U A) x
  = η x := eq_refl.

Example op_unit_is_counit (a : C) :
  @unit (Opposite D) (Opposite C) (Opposite_Functor U)
        (Opposite_Functor F) (Opposite_Adjunction F U A) a
  = ε a := eq_refl.

(* Riehl 4.6.11 dual (i): F faithful ⟺ every unit component is monic. *)

Definition left_adjoint_faithful_iff_unit_monic :
  Faithful F ↔ (∀ x : D, Monic (η x)).
Proof.
  pose proof (@right_adjoint_faithful_iff_counit_epic
                (Opposite D) (Opposite C) (Opposite_Functor U)
                (Opposite_Functor F) (Opposite_Adjunction F U A)) as H.
  split.
  - intros HF x.
    exact (Monic_of_op_Epic (η x) (fst H (Faithful_op HF) x)).
  - intros Hm.
    apply (@Faithful_of_op D C F).
    apply (snd H); intro x.
    exact (op_Epic_of_Monic (η x) (Hm x)).
Defined.

(* Riehl 4.6.11 dual (ii): F full ⟺ every unit component is a split epi.
   The forward half is #368's [unit_split_epi_of_full_left] read through
   the opposite adjunction; the two are compared below. *)

Definition left_adjoint_full_iff_unit_split_epic :
  Full F ↔ (∀ x : D, Retraction (η x)).
Proof.
  pose proof (@right_adjoint_full_iff_counit_split_monic
                (Opposite D) (Opposite C) (Opposite_Functor U)
                (Opposite_Functor F) (Opposite_Adjunction F U A)) as H.
  split.
  - intros HF x.
    exact (Retraction_of_op_Section (η x) (fst H (Full_op HF) x)).
  - intros Hr.
    apply (@Full_of_op D C F).
    apply (snd H); intro x.
    exact (op_Section_of_Retraction (η x) (Hr x)).
Defined.

(* The op route's right inverse for η_x IS #368's, on the nose: the
   opposite adjunction's counit at x is η x, [Full_op]'s [prefmap] is the
   original's at swapped indices, and [Opposite_Functor U] applied to F x
   is U (F x) — so both sides reduce to
   `prefmap F HF (U (F x)) x (ε (F x))`. *)

Example unit_retract_agrees (HF : Full F) (x : D) :
  @retract D x (U (F x)) (η x)
    (fst left_adjoint_full_iff_unit_split_epic HF x)
  = @retract D x (U (F x)) (η x)
    (@unit_split_epi_of_full_left C D F U A HF x) := eq_refl.

(* Riehl 4.6.11 dual (iii): F fully faithful ⟺ η is an isomorphism.  The
   forward half CONSUMES #368's [unit_iso_of_full_monic] rather
   than re-running the split-plus-cancellation argument. *)

Definition left_adjoint_fully_faithful_iff_unit_iso :
  (Full F * Faithful F)%type ↔ (∀ x : D, IsIsomorphism (η x)).
Proof.
  split.
  - intros [HFull HFaith] x.
    exact (@unit_iso_of_full_monic C D F U A HFull
             (fst left_adjoint_faithful_iff_unit_monic HFaith) x).
  - intros H.
    split.
    + apply (snd left_adjoint_full_iff_unit_split_epic); intro x.
      exact {| retract      := @two_sided_inverse D _ _ _ (H x)
             ; retract_comp := @is_right_inverse D _ _ _ (H x) |}.
    + apply (snd left_adjoint_faithful_iff_unit_monic); intro x.
      constructor; intros z g1 g2 Heq.
      rewrite <- (id_left g1), <- (id_left g2).
      rewrite <- (@is_left_inverse D _ _ _ (H x)).
      rewrite <- !comp_assoc.
      now rewrite Heq.
Defined.

(* ... and the derivation the issue asks for: the SAME fact is
   [adj_monic] (Theory/Adjunction.v) read at the opposite adjunction.
   At `Opposite_Adjunction F U A` the left adjoint is [Opposite_Functor U],
   so `Faithful F` there is `Faithful U` here (through [Faithful_op]),
   `Monic f` there is `Epic f` here (through [op_Monic_of_Epic]), the
   forward transpose ⌊−⌋ there is ⌈−⌉ here, and composition is reversed —
   so the conclusion `⌊f⌋ ∘ g ≈ ⌊f⌋ ∘ h → g ≈ h` reads, in C, as
   `g ∘ ⌈f⌉ ≈ h ∘ ⌈f⌉ → g ≈ h`, which is [Epic ⌈f⌉].  Every OTHER step
   is a conversion: the script is `constructor; intros` and one [exact],
   whose only non-conversion content is those two transports. *)

Definition from_adj_epic_of_epic (HU : Faithful U)
           {x : D} {a : C} (f : x ~> U a) (Hf : Epic f) : Epic ⌈f⌉.
Proof.
  constructor; intros c g h Heq.
  exact (@adj_monic (Opposite D) (Opposite C) (Opposite_Functor U)
           (Opposite_Functor F) (Opposite_Adjunction F U A)
           a x f c g h (Faithful_op HU) (op_Monic_of_Epic f Hf) Heq).
Defined.

Definition right_adjoint_faithful_iff_from_adj_epic :
  Faithful U
    ↔ (∀ (x : D) (a : C) (f : x ~> U a), Epic f → Epic ⌈f⌉).
Proof.
  split.
  - intros HU x a f Hf. exact (from_adj_epic_of_epic HU f Hf).
  - intros H.
    apply (@faithful_of_counit_epic C D F U A); intro a.
    exact (H (U a) a id (@id_epic D (U a))).
Defined.

End Duals.

(* ------------------------------------------------------------------ *)
(** ** (G) The reflective special case, as a corollary *)

(* Mac Lane, printed p. 91 (image p367-100.png), immediately after the
   proof of Theorem 1:

     "A subcategory A of B is called reflective in B when the inclusion
      functor K : A → B has a left adjoint F : B → A. ...  Since the
      inclusion functor K is always faithful, the counit ε of a
      reflection is always epi. ...  If a full subcategory A ⊂ B is
      reflective in B, then by Theorem 1 each object a ∈ A is isomorphic
      to F K a, and hence R a ≅ a for all a."

   That is exactly Construction/Reflective.v's [reflective_counit_iso],
   and here it becomes a corollary: the inclusion is faithful
   ([Incl_Faithful], Construction/Subcategory.v) and full as a functor
   whenever the subcategory is full ([Full_Implies_Full_Functor]),
   so (iii) applies.

   Two facts about the inclusion are used and nothing else; in
   particular no property of the reflector, and no subcategory-specific
   argument.  See DONOR DEFECT in the header for why the result cannot be
   compared field-by-field with the existing lemma. *)

Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.

Definition reflective_incl_Full {C : Category} {S : Subcategory C}
           (R : Reflective S) : Functor.Full (Incl C S) :=
  @Full_Implies_Full_Functor C S (reflective_full R).

Definition reflective_incl_Faithful {C : Category} {S : Subcategory C}
           (R : Reflective S) : Functor.Faithful (Incl C S) :=
  @Incl_Faithful C S.

(* The general theorem, instantiated.  [Incl C S] is the RIGHT adjoint of
   the reflection, so this is (iii) verbatim. *)

Definition reflective_counit_IsIsomorphism_general {C : Category}
           {S : Subcategory C} (R : Reflective S) (x : Sub C S) :
  IsIsomorphism (@counit (Sub C S) C (reflector R) (Incl C S)
                   (reflective_adj R) x) :=
  fst (@right_adjoint_fully_faithful_iff_counit_iso
         (Sub C S) C (reflector R) (Incl C S) (reflective_adj R))
      (reflective_incl_Full R, reflective_incl_Faithful R) x.

(* The object-level reading, which is Mac Lane's own sentence "each
   object a ∈ A is isomorphic to F K a". *)

Definition reflective_counit_Isomorphism_general {C : Category}
           {S : Subcategory C} (R : Reflective S) (x : Sub C S) :
  reflector R (Incl C S x) ≅[Sub C S] x :=
  IsIsoToIso _ (reflective_counit_IsIsomorphism_general R x).

(* Faithfulness alone already gives Mac Lane's weaker sentence "the
   counit of a reflection is always epi", with no fullness hypothesis. *)

Definition reflection_counit_Epic {C : Category} {S : Subcategory C}
           (R : Reflective S) (x : Sub C S) :
  Epic (@counit (Sub C S) C (reflector R) (Incl C S)
          (reflective_adj R) x) :=
  counit_epic_of_faithful (reflective_incl_Faithful R) x.
