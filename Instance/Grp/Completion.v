Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.Mon.Free.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Quotient.Colimit.
Require Import Category.Instance.Rng.MonoidRing.
Require Import Category.Instance.Rng.GroupRing.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 nLab:      https://ncatlab.org/nlab/show/group+completion
 nLab:      https://ncatlab.org/nlab/show/free+group
 nLab:      https://ncatlab.org/nlab/show/presentation+of+a+group
 Wikipedia: https://en.wikipedia.org/wiki/Grothendieck_group
 Book: Riehl, "Category Theory in Context" (2nd ed., Dover 2016), §4.1

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** A trivial homomorphism, and rigidity of free groups *)

Definition grp_trivial_hom (G H : GrpObject) : G ~{Grp}~> H :=
  @Build_GrpHom' G H
    {| morphism        := fun _ : carrier G => grp_unit H
     ; proper_morphism := fun a b (_ : a ≈ b) => reflexivity (grp_unit H) |}
    (fun a b => symmetry (grp_mul_unit_l H (grp_unit H))).

Definition grp_unit_map (X : SetoidObject) (H : GrpObject)
  : X ~{Sets}~> Grp_Forget H :=
  {| morphism        := fun _ : carrier X => grp_unit H
   ; proper_morphism := fun a b (_ : a ≈ b) => reflexivity (grp_unit H) |}.

(* A homomorphism out of a free group that kills every generator is
   trivial.  No induction on words: both it and the constant-unit
   homomorphism extend the same map, so [free_grp_extend_unique] applies
   twice. *)
Lemma free_grp_hom_trivial {X : SetoidObject} {H : GrpObject}
  (g : FreeGrpObject X ~{Grp}~> H)
  (Hg : ∀ a : carrier X, grp_map g (fg_insert X a) ≈ grp_unit H)
  (w : FGWord X) : grp_map g w ≈ grp_unit H.
Proof.
  transitivity (grp_map (free_grp_extend (grp_unit_map X H)) w).
  - exact (free_grp_extend_unique X H (grp_unit_map X H) g Hg w).
  - symmetry.
    exact (free_grp_extend_unique X H (grp_unit_map X H)
             (grp_trivial_hom (FreeGrpObject X) H)
             (fun a => reflexivity (grp_unit H)) w).
Qed.

(** ** The presentation *)

Section Completion.

Context (M : MonSets).

(* The free group on the underlying setoid of M. *)
Definition comp_free : GrpObject := FreeGrpObject (mcar M).

Definition comp_gen (a : carrier (mcar M)) : carrier comp_free :=
  fg_insert (mcar M) a.

#[local] Instance comp_gen_respects : Proper (equiv ==> equiv) comp_gen :=
  proper_morphism (fg_insert (mcar M)).

#[local] Instance comp_mop_respects
  : Proper (equiv ==> equiv ==> equiv) (mop M) := mop_respects M.

(* The relator word attached to a pair: what must become trivial for the
   insertion to be multiplicative. *)
Definition comp_rel_word (a b : carrier (mcar M)) : carrier comp_free :=
  grp_mul comp_free (grp_mul comp_free (comp_gen a) (comp_gen b))
    (grp_inv comp_free (comp_gen (mop M a b))).

Lemma comp_rel_word_respects (a a' b b' : carrier (mcar M)) :
  a ≈ a' → b ≈ b' → comp_rel_word a b ≈ comp_rel_word a' b'.
Proof.
  intros Ha Hb; unfold comp_rel_word.
  now rewrite Ha, Hb.
Qed.

(* The relator index: a pair of elements of M, compared componentwise. *)
Program Definition CompRelSetoid
  : Setoid (carrier (mcar M) * carrier (mcar M)) := {|
  equiv := fun p q => (fst p ≈ fst q) * (snd p ≈ snd q)
|}.
Next Obligation.
  constructor.
  - intros [a b]; split; reflexivity.
  - intros [a b] [c d] [H1 H2]; split; symmetry; assumption.
  - intros [a b] [c d] [e f] [H1 H2] [H3 H4]; split;
      [ transitivity c | transitivity d ]; assumption.
Qed.

Definition CompRelIdx : SetoidObject :=
  {| carrier := carrier (mcar M) * carrier (mcar M)
   ; is_setoid := CompRelSetoid |}.

Definition comp_relator (p : carrier CompRelIdx) : carrier comp_free :=
  comp_rel_word (fst p) (snd p).

Definition comp_relator_map : CompRelIdx ~{Sets}~> Grp_Forget comp_free :=
  {| morphism        := comp_relator
   ; proper_morphism := fun p q H =>
       comp_rel_word_respects (fst p) (fst q) (snd p) (snd q)
         (fst H) (snd H) |}.

(* Read as a homomorphism out of the free group on the relator index, so
   that [NormalClosure] -- which closes the IMAGE of a homomorphism --
   applies verbatim. *)
Definition comp_relator_hom : FreeGrpObject CompRelIdx ~{Grp}~> comp_free :=
  free_grp_extend comp_relator_map.

Definition CompletionNS : NormalSubgroup comp_free :=
  NormalClosure comp_relator_hom.

Definition CompletionObject : GrpObject := QuotientGrp CompletionNS.

Definition comp_class (a : carrier (mcar M)) : carrier CompletionObject :=
  comp_gen a.

(* Two conversion helpers.  An earlier revision said "both bodies are the
   corresponding [quot_rel] fact verbatim: `≈` at [CompletionObject] IS
   [quot_rel CompletionNS], so no proof step intervenes".  Since the PR
   "algebraic carriers are sets" (2026-09-17) the quotient's `≈` is the
   PROPOSITIONAL TRUNCATION of [quot_rel CompletionNS], so each body is that
   same fact under one [inhabits] -- still no mathematical step. *)
Lemma comp_quot_of_equiv (x y : carrier comp_free) :
  x ≈ y → (x : carrier CompletionObject) ≈ y.
Proof. exact (fun H => inhabits (quot_rel_of_equiv CompletionNS x y H)). Qed.

Lemma comp_quot_of_mem (x y : carrier comp_free) :
  sub_mem CompletionNS (grp_mul comp_free x (grp_inv comp_free y)) →
  (x : carrier CompletionObject) ≈ y.
Proof. exact (fun H => inhabits H). Qed.

(* Every relator lies in the normal closure. *)
Lemma comp_relator_mem (p : carrier CompRelIdx) :
  sub_mem CompletionNS (comp_relator p).
Proof.
  exact (nc_resp
           (free_grp_extend_generators CompRelIdx comp_free
              comp_relator_map p)
           (nc_gen (fg_insert CompRelIdx p))).
Qed.

Lemma comp_class_respects (a b : carrier (mcar M)) :
  a ≈ b → comp_class a ≈ comp_class b.
Proof. intro Hab; apply comp_quot_of_equiv; now rewrite Hab. Qed.

(* The insertion is multiplicative: this is exactly the relator, inverted. *)
Lemma comp_class_op (a b : carrier (mcar M)) :
  comp_class (mop M a b)
    ≈ grp_mul CompletionObject (comp_class a) (comp_class b).
Proof.
  apply comp_quot_of_mem.
  apply (sub_at CompletionNS
           (a := grp_inv comp_free (comp_rel_word a b))).
  - unfold comp_rel_word.
    rewrite grp_inv_mul, grp_inv_inv.
    reflexivity.
  - exact (sub_inv CompletionNS _ (comp_relator_mem (a, b))).
Qed.

(* ...and unital, which is a CONSEQUENCE rather than a second relator: an
   idempotent of a group is its unit. *)
Lemma comp_class_one : comp_class (mone M) ≈ grp_unit CompletionObject.
Proof.
  assert (Hu : grp_mul CompletionObject
                 (comp_class (mone M)) (comp_class (mone M))
                 ≈ comp_class (mone M)).
  { transitivity (comp_class (mop M (mone M) (mone M))).
    - symmetry; apply comp_class_op.
    - apply comp_class_respects, mop_one_l. }
  apply (grp_cancel_r CompletionObject (comp_class (mone M))).
  rewrite grp_mul_unit_l.
  exact Hu.
Qed.

End Completion.

Arguments comp_free M : clear implicits.
Arguments CompletionObject M : clear implicits.

(* The insertion, as a morphism of [MonSets].  It is declared OUTSIDE the
   section above deliberately: [Grp_MonSets] is instantiable only at
   [Set]-carrier groups (see the header), and a section variable
   [M : MonSets] has its universes fixed before that constraint can be
   imposed, so naming [Grp_MonSets] inside the section is a universe
   inconsistency.  Outside it, each definition is generalized on its own
   and the instantiation goes through. *)
Definition completion_insert (M : MonSets)
  : M ~{MonSets}~> Grp_MonSets (CompletionObject M) :=
  @mhom M (Grp_MonSets (CompletionObject M))
    (comp_class M) (comp_class_respects M) (comp_class_op M)
    (comp_class_one M).

(** ** The extension of a monoid homomorphism into a group *)

Section Extend.

Context (M : MonSets) (H : Grp) (h : M ~{MonSets}~> Grp_MonSets H).

Definition comp_target_map : mcar M ~{Sets}~> Grp_Forget H := `1 h.

(* The word evaluation.  It is the free group's own extension of the
   underlying setoid map of [h]; the monoid structure of [M] is not
   consulted here at all -- it enters only in [comp_bar_relator]. *)
Definition comp_bar : comp_free M ~{Grp}~> H :=
  free_grp_extend comp_target_map.

Lemma comp_bar_gen (a : carrier (mcar M)) :
  grp_map comp_bar (comp_gen M a) ≈ mmap h a.
Proof. exact (free_grp_extend_generators (mcar M) H comp_target_map a). Qed.

(* [h] being multiplicative is exactly what kills the relators. *)
Lemma comp_bar_relator (a b : carrier (mcar M)) :
  grp_map comp_bar (comp_rel_word M a b) ≈ grp_unit H.
Proof.
  unfold comp_rel_word.
  rewrite (grp_map_mul comp_bar), (grp_map_mul comp_bar),
    (grp_map_inv comp_bar), !comp_bar_gen.
  rewrite (mmap_op h a b).
  apply grp_mul_inv_r.
Qed.

Lemma comp_bar_kills (x : carrier (comp_free M)) :
  sub_mem (CompletionNS M) x → grp_map comp_bar x ≈ grp_unit H.
Proof.
  apply (normal_closure_killed (comp_relator_hom M) comp_bar).
  intro w.
  refine (free_grp_hom_trivial (comp_bar ∘ comp_relator_hom M) _ w).
  intro p.
  transitivity (grp_map comp_bar (comp_relator M p)).
  - exact (proper_morphism (grp_map comp_bar) _ _
             (free_grp_extend_generators (CompRelIdx M) (comp_free M)
                (comp_relator_map M) p)).
  - exact (comp_bar_relator (fst p) (snd p)).
Qed.

Definition comp_kills : Kills (CompletionNS M) H :=
  existT _ comp_bar comp_bar_kills.

Definition completion_extend : CompletionObject M ~{Grp}~> H :=
  quot_med (CompletionNS M) comp_kills.

Lemma completion_extend_gen (a : carrier (mcar M)) :
  grp_map completion_extend (comp_class M a) ≈ mmap h a.
Proof. exact (comp_bar_gen a). Qed.

Lemma completion_extend_unique (g : CompletionObject M ~{Grp}~> H)
  (Hg : ∀ a : carrier (mcar M), grp_map g (comp_class M a) ≈ mmap h a) :
  g ≈ completion_extend.
Proof.
  symmetry.
  apply (quot_med_unique (CompletionNS M) comp_kills g).
  intro w.
  exact (free_grp_extend_unique (mcar M) H comp_target_map
           (g ∘ quot_proj (CompletionNS M)) Hg w).
Qed.

End Extend.

Arguments comp_bar {M H} h.
Arguments completion_extend {M H} h.
Arguments completion_extend_gen {M H} h a.
Arguments completion_extend_unique {M H} h g Hg.

(** ** The universal property *)

Theorem completion_universal (M : MonSets) :
  ∀ (H : Grp) (h : M ~{MonSets}~> Grp_MonSets H),
    ∃! g : CompletionObject M ~{Grp}~> H,
      h ≈ fmap[Grp_MonSets] g ∘ completion_insert M.
Proof.
  intros H h.
  unshelve eexists.
  - exact (completion_extend h).
  - intro a.
    symmetry; exact (completion_extend_gen h a).
  - intros g Hg.
    symmetry.
    exact (completion_extend_unique h g (fun a => symmetry (Hg a))).
Qed.

(** ** The universal arrow, in both encodings *)

Definition completion_universal_arrow (M : MonSets)
  : UniversalArrow M Grp_MonSets :=
  universal_arrow_from_UMP M Grp_MonSets (CompletionObject M)
    (completion_insert M) (completion_universal M).

Program Definition completion_AUniversalArrow (M : MonSets)
  : AUniversalArrow M Grp_MonSets (CompletionObject M) := {|
  universal_arrow := completion_insert M
|}.
Next Obligation.
  intros M H h.
  unshelve eexists.
  - exact (completion_extend h).
  - intro a.
    exact (completion_extend_gen h a).
  - intros g Hg.
    symmetry.
    exact (completion_extend_unique h g Hg).
Qed.

(** ** The completion functor, built directly *)

Program Definition CompletionFunctor : MonSets ⟶ Grp := {|
  fobj := CompletionObject;
  fmap := fun X Y f => completion_extend (completion_insert Y ∘ f)
|}.
Next Obligation.
  intros X Y f g Hfg.
  symmetry.
  apply completion_extend_unique.
  intro a.
  transitivity (comp_class Y (mmap g a)).
  - exact (completion_extend_gen (completion_insert Y ∘ g) a).
  - exact (comp_class_respects Y _ _ (symmetry (Hfg a))).
Qed.
Next Obligation.
  intros X.
  symmetry.
  apply completion_extend_unique.
  intro a; reflexivity.
Qed.
Next Obligation.
  intros X Y Z f g.
  symmetry.
  apply completion_extend_unique.
  intro a.
  transitivity (grp_map (completion_extend (completion_insert Z ∘ f))
                  (comp_class Y (mmap g a))).
  - exact (proper_morphism
             (grp_map (completion_extend (completion_insert Z ∘ f))) _ _
             (completion_extend_gen (completion_insert Y ∘ g) a)).
  - exact (completion_extend_gen (completion_insert Z ∘ f) (mmap g a)).
Qed.

(** ** The adjunction *)

Definition CompletionLeft : MonSets ⟶ Grp :=
  LeftAdjointFunctorFromUniversalArrows Grp_MonSets completion_universal_arrow.

Definition completion_adjunction : CompletionLeft ⊣ Grp_MonSets :=
  AdjunctionFromUniversalArrows Grp_MonSets completion_universal_arrow.

(** ** Strengths, measured strict-first *)

Example completion_class_is_generator (M : MonSets) (a : carrier (mcar M)) :
  comp_class M a = fg_insert (mcar M) a := eq_refl.

Example completion_insert_computes (M : MonSets) (a : carrier (mcar M)) :
  mmap (completion_insert M) a = comp_class M a := eq_refl.

Example completion_mul_is_free_mul (M : MonSets) :
  grp_mul (CompletionObject M) = grp_mul (comp_free M) := eq_refl.

Example completion_functor_obj (M : MonSets) :
  fobj[CompletionFunctor] M = CompletionObject M := eq_refl.

Example CompletionLeft_obj (M : MonSets) :
  CompletionLeft M = CompletionObject M := eq_refl.

Example completion_functor_obj_agrees (M : MonSets) :
  fobj[CompletionFunctor] M = CompletionLeft M := eq_refl.

Example completion_arrow_is_insert (M : MonSets) :
  @arrow _ _ M Grp_MonSets (completion_universal_arrow M)
    = completion_insert M := eq_refl.

Example completion_auniversal_arrow_is_insert (M : MonSets) :
  @universal_arrow _ _ M Grp_MonSets (CompletionObject M)
    (completion_AUniversalArrow M) = completion_insert M := eq_refl.

Example completion_extend_is_bar (M : MonSets) (H : Grp)
  (h : M ~{MonSets}~> Grp_MonSets H) (x : carrier (comp_free M)) :
  grp_map (completion_extend h) x = grp_map (comp_bar h) x := eq_refl.

Definition completion_unit (M : MonSets)
  : M ~{MonSets}~> Grp_MonSets (CompletionLeft M) :=
  @Category.Theory.Adjunction.unit _ _ _ _ completion_adjunction M.

Example completion_unit_is_insert (M : MonSets) (a : carrier (mcar M)) :
  mmap (completion_unit M) a = comp_class M a := eq_refl.

(** ** The counit evaluates a word, and the triangle identities *)

Definition completion_counit (H : Grp)
  : CompletionLeft (Grp_MonSets H) ~{Grp}~> H :=
  @Category.Theory.Adjunction.counit _ _ _ _ completion_adjunction H.

Lemma completion_counit_class (H : Grp) (a : carrier (grp_setoid H)) :
  grp_map (completion_counit H) (comp_class (Grp_MonSets H) a) ≈ a.
Proof. exact (@to_adj_counit _ _ _ _ completion_adjunction H a). Qed.

Theorem completion_counit_evaluates (H : Grp)
  (x : carrier (CompletionObject (Grp_MonSets H))) :
  grp_map (completion_counit H) x
    ≈ grp_map (completion_extend (@id MonSets (Grp_MonSets H))) x.
Proof.
  exact (completion_extend_unique (@id MonSets (Grp_MonSets H))
           (completion_counit H) (completion_counit_class H) x).
Qed.

Corollary completion_triangle_left (M : MonSets) :
  completion_counit (CompletionLeft M)
    ∘ fmap[CompletionLeft] (completion_unit M)
    ≈ @id Grp (CompletionLeft M).
Proof. exact (@counit_fmap_unit _ _ _ _ completion_adjunction M). Qed.

Corollary completion_triangle_right (H : Grp) :
  fmap[Grp_MonSets] (completion_counit H) ∘ completion_unit (Grp_MonSets H)
    ≈ @id MonSets (Grp_MonSets H).
Proof. exact (@fmap_counit_unit _ _ _ _ completion_adjunction H). Qed.

(** ** The two left functors agree *)

Theorem completion_fmap_agrees {X Y : MonSets} (f : X ~{MonSets}~> Y) :
  fmap[CompletionLeft] f ≈ fmap[CompletionFunctor] f.
Proof.
  apply (uniqueness (ump_universal_arrows (completion_universal_arrow X)
                       (completion_insert Y ∘ f))).
  intro a.
  symmetry.
  exact (completion_extend_gen (completion_insert Y ∘ f) a).
Qed.

(** ** Non-vacuity: the completion can be non-abelian *)

Definition S3Mon : MonSets := Grp_MonSets S3.

Definition comp_S3 : GrpObject := CompletionObject S3Mon.

Definition comp_S3_down : comp_S3 ~{Grp}~> S3 :=
  completion_extend (@id MonSets S3Mon).

Definition comp_S3_r : carrier comp_S3 := comp_class S3Mon S3_r.
Definition comp_S3_s : carrier comp_S3 := comp_class S3Mon S3_s.

Lemma comp_S3_down_class (a : carrier S3) :
  grp_map comp_S3_down (comp_class S3Mon a) ≈ a.
Proof. exact (completion_extend_gen (@id MonSets S3Mon) a). Qed.

(* The insertion of a GROUP's underlying monoid is injective, because the
   completion retracts onto it. *)
Theorem completion_S3_insert_injective (a b : carrier S3) :
  comp_class S3Mon a ≈ comp_class S3Mon b → a ≈ b.
Proof.
  intro Hab.
  transitivity (grp_map comp_S3_down (comp_class S3Mon a)).
  - symmetry; exact (comp_S3_down_class a).
  - transitivity (grp_map comp_S3_down (comp_class S3Mon b)).
    + exact (proper_morphism (grp_map comp_S3_down) _ _ Hab).
    + exact (comp_S3_down_class b).
Qed.

Theorem completion_can_be_nonabelian :
  grp_mul comp_S3 comp_S3_r comp_S3_s ≈ grp_mul comp_S3 comp_S3_s comp_S3_r
    → False.
Proof.
  intro Hcomm.
  apply S3_nonabelian.
  transitivity (grp_map comp_S3_down (grp_mul comp_S3 comp_S3_r comp_S3_s)).
  - rewrite (grp_map_mul comp_S3_down).
    unfold comp_S3_r, comp_S3_s.
    now rewrite !comp_S3_down_class.
  - rewrite Hcomm, (grp_map_mul comp_S3_down).
    unfold comp_S3_r, comp_S3_s.
    now rewrite !comp_S3_down_class.
Qed.

Theorem completion_S3_generators_distinct : comp_S3_r ≈ comp_S3_s → False.
Proof.
  intro H.
  pose proof (completion_S3_insert_injective S3_r S3_s H) as E.
  discriminate E.
Qed.

(** ** The completion of a free monoid is the free group

    Riehl's own headline instance, and the one
    [Instance/CMon/Grothendieck.v]'s reason (2) argues from: the group
    completion of the free monoid on X is the free group on X.  Both are
    universal arrows from X to [Grp_Forget] -- note [UMonS ∘ Grp_MonSets]
    IS [Grp_Forget] by conversion, both being [fun H => grp_setoid H] --
    so [universal_arrow_iso] supplies the comparison and nothing is
    constructed by hand. *)

Definition comp_free_mon_insert (X : Sets)
  : X ~{Sets}~> Grp_Forget (CompletionObject (FreeMonSetsObject X)) :=
  `1 (completion_insert (FreeMonSetsObject X)) ∘ free_mon_insert X.

Theorem comp_free_mon_universal (X : Sets) :
  ∀ (H : Grp) (k : X ~{Sets}~> Grp_Forget H),
    ∃! g : CompletionObject (FreeMonSetsObject X) ~{Grp}~> H,
      k ≈ fmap[Grp_Forget] g ∘ comp_free_mon_insert X.
Proof.
  intros H k.
  pose (km := @free_mon_hom X (Grp_MonSets H) k (proper_morphism k)).
  unshelve eexists.
  - exact (completion_extend km).
  - intro a.
    symmetry.
    transitivity (mmap km (free_mon_insert X a)).
    + exact (completion_extend_gen km (free_mon_insert X a)).
    + exact (@free_mon_extend_generator X (Grp_MonSets H) k a).
  - intros g Hg.
    symmetry.
    apply (completion_extend_unique km g).
    intro w.
    exact (@free_mon_extend_unique X (Grp_MonSets H) k
             (fmap[Grp_MonSets] g ∘ completion_insert (FreeMonSetsObject X))
             (fun a => symmetry (Hg a)) w).
Qed.

Definition comp_free_mon_universal_arrow (X : Sets)
  : UniversalArrow X Grp_Forget :=
  universal_arrow_from_UMP X Grp_Forget
    (CompletionObject (FreeMonSetsObject X)) (comp_free_mon_insert X)
    (comp_free_mon_universal X).

Definition completion_free_monoid_iso (X : Sets)
  : CompletionObject (FreeMonSetsObject X) ≅[Grp] FreeGrpObject X :=
  @universal_arrow_iso Sets Grp X Grp_Forget
    (comp_free_mon_universal_arrow X) (free_group_universal_arrow X).

(* The comparison carries the class of a one-letter word to the
   corresponding free generator -- the leg equation a bare [≅] would not
   carry. *)
Lemma completion_free_monoid_iso_gen (X : Sets) (a : carrier X) :
  grp_map (to (completion_free_monoid_iso X))
    (comp_class (FreeMonSetsObject X) (free_mon_insert X a))
    ≈ fg_insert X a.
Proof.
  exact (ua_med_commutes (comp_free_mon_universal_arrow X)
           (free_group_universal_arrow X) a).
Qed.

(* Hence the canonical non-abelian instance, transported from
   [Instance/Grp/Free.v]'s witness rather than reproved. *)
Theorem completion_free_mon_two_nonabelian :
  grp_mul (CompletionObject (FreeMonSetsObject TwoLetters))
    (comp_class (FreeMonSetsObject TwoLetters)
       (free_mon_insert TwoLetters true))
    (comp_class (FreeMonSetsObject TwoLetters)
       (free_mon_insert TwoLetters false))
  ≈ grp_mul (CompletionObject (FreeMonSetsObject TwoLetters))
      (comp_class (FreeMonSetsObject TwoLetters)
         (free_mon_insert TwoLetters false))
      (comp_class (FreeMonSetsObject TwoLetters)
         (free_mon_insert TwoLetters true))
    → False.
Proof.
  intro Hcomm.
  apply free_group_two_generators_nonabelian.
  pose proof (proper_morphism
                (grp_map (to (completion_free_monoid_iso TwoLetters)))
                _ _ Hcomm) as Hi.
  rewrite !(grp_map_mul (to (completion_free_monoid_iso TwoLetters))) in Hi.
  rewrite !completion_free_monoid_iso_gen in Hi.
  exact Hi.
Qed.

(** ** Measured negatives

    Each [Fail] below was stripped once and its failure KIND read off the
    error message, and each is paired with a positive control that must
    succeed.  Three are CONVERSION failures ("cannot unify") and three are
    FORMABILITY failures (universe inconsistencies naming the declared
    level); they are kept lexically apart. *)

(* Instrument check: the mechanism reports a genuine failure on a
   scope-free proposition. *)
Fail Definition completion_probe_instrument : true = false := eq_refl.

(** *** Conversion negatives *)

(* (1) The COUNIT does not compute.  It is
   [unique_obj (ump_universal_arrows …)] and [ump_universal_arrows]
   (Theory/Universal/Arrow.v) is [Qed], so nothing reduces through it.
   The probe DISCRIMINATES: [completion_unit_is_insert] above closes by
   [eq_refl] at the SAME adjunction, so the obstruction is that one
   constant's opacity and not the adjunction packaging. *)
Fail Example completion_probe_counit (H : Grp)
  (x : carrier (CompletionObject (Grp_MonSets H))) :
  grp_map (completion_counit H) x
    = grp_map (completion_extend (@id MonSets (Grp_MonSets H))) x := eq_refl.

(* (2) [fmap[CompletionLeft]] does not compute either, for the same
   reason: [LeftAdjointFunctorFromUniversalArrows] defines it by universal
   factorization rather than by a formula.  This is why
   [CompletionFunctor] is built directly and why [completion_fmap_agrees]
   is [≈].  The control is [completion_functor_obj_agrees], where the
   OBJECT actions do agree strictly. *)
Fail Example completion_probe_fmap (X Y : MonSets) (f : X ~{MonSets}~> Y) :
  fmap[CompletionLeft] f = fmap[CompletionFunctor] f := eq_refl.

(* (3) The insertion is multiplicative only up to [≈]: the completion is a
   genuine QUOTIENT, and the two sides are distinct words of the free
   group identified by the relator.  [comp_class_op] is the [≈]
   statement, and it is what the whole presentation exists to supply. *)
Fail Example completion_probe_insert_op (M : MonSets)
  (a b : carrier (mcar M)) :
  comp_class M (mop M a b)
    = grp_mul (CompletionObject M) (comp_class M a) (comp_class M b)
  := eq_refl.

(** *** Formability negatives: the donor's [Set] pin

    [Grp_MonSets] is instantiable only at [GrpObject@{Set Set _}] --
    measured off [grp_monoid]'s own signature, which reads
    [∀ G : GrpObject@{Set Set u}, Monoid@{_ Set} G].  The two controls
    below show that the group's own data is formable at a strictly larger
    carrier universe, and (crucially) that the TYPE [grp_monoid] inhabits
    is formable there too, so the pin is introduced by that DEFINITION and
    is not demanded by its statement.  It is the universe-minimization
    family the tree records elsewhere; it is NOT claimed unavoidable, and
    it is NOT repaired here. *)

Section CompletionSetPin.

Universe uo uh up.
Constraint Set < uo.

Check (fun G : GrpObject@{uo uh up} => grp_setoid G).
Check (fun G : GrpObject@{uo uh up} =>
         @Monoid Sets Sets_Product_Monoidal (grp_setoid G)).

(* Control: [grp_monoid] must be named OUTSIDE a [Fail], or renaming it
   would turn the negative below vacuously green on "reference not
   found" while this file still compiled. *)
Check @grp_monoid.

Fail Check (fun G : GrpObject@{uo uh up} => grp_monoid G).
Fail Check (fun G : GrpObject@{uo uh up} => Grp_MonSets G).

End CompletionSetPin.

(* And the pin's BOUNDARY is measured rather than assumed: the whole
   presentation layer -- the free group, the relator subgroup, the
   quotient and its multiplicativity -- is formable over a monoid whose
   carrier universe sits strictly ABOVE [Set], and it is exactly the first
   constant whose TYPE names [Grp_MonSets] that is rejected there. *)

Section CompletionInsertPin.

Universe uo uh.
Constraint Set < uo.

Check (fun M : obj[MonSets@{uo uh}] => comp_free M).
Check (fun M : obj[MonSets@{uo uh}] => CompletionObject M).
Check (fun (M : obj[MonSets@{uo uh}]) (a b : carrier (mcar M)) =>
         comp_class_op M a b).

Fail Check (fun M : obj[MonSets@{uo uh}] => completion_insert M).

End CompletionInsertPin.
