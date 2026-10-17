Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pushout.Split.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.

Generalizable All Variables.

(** * Pushouts in Grp: the free product with amalgamation *)

(*
 nLab:      https://ncatlab.org/nlab/show/pushout
 Wikipedia: https://en.wikipedia.org/wiki/Free_product  (amalgamation)

   本文件给出推出实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Formal words *)

Inductive AmTerm (B C : GrpObject) : Type :=
  | am_l   : carrier B → AmTerm
  | am_r   : carrier C → AmTerm
  | am_one : AmTerm
  | am_mul : AmTerm → AmTerm → AmTerm
  | am_inv : AmTerm → AmTerm.

Arguments am_l {B C} _.
Arguments am_r {B C} _.
Arguments am_one {B C}.
Arguments am_mul {B C} _ _.
Arguments am_inv {B C} _.

(** ** The generated congruence *)

(* [am_eq] lands in [Prop].  Since the PR "algebraic carriers are sets"
   (2026-09-17) a [GrpObject] carries [grp_prop], so the amalgam's carrier
   setoid owes a [Prop]-valued mirror of its `≈`; the cheapest and most
   faithful one is the congruence itself, declared in [Prop].  Two
   constructors carry a [Type]-valued `≈` premise ([ae_l_resp], [ae_r_resp])
   and both stay VERBATIM: a [Prop] inductive may store [Type]-valued data,
   it simply may not be eliminated into [Type].  Nothing below is proved by
   induction on [am_eq] except [am_eval_respects], whose one elimination is
   routed through [pequiv] at the target group. *)
Inductive am_eq {A B C : GrpObject}
                (f : A ~{Grp}~> B) (g : A ~{Grp}~> C)
  : AmTerm B C → AmTerm B C → Prop :=
  (* the two insertions respect the groups' own equivalences *)
  | ae_l_resp : ∀ b b' : carrier B,
      b ≈ b' → am_eq (am_l b) (am_l b')
  | ae_r_resp : ∀ c c' : carrier C,
      c ≈ c' → am_eq (am_r c) (am_r c')
  (* the two insertions preserve multiplication *)
  | ae_l_mul : ∀ b b' : carrier B,
      am_eq (am_l (grp_mul B b b')) (am_mul (am_l b) (am_l b'))
  | ae_r_mul : ∀ c c' : carrier C,
      am_eq (am_r (grp_mul C c c')) (am_mul (am_r c) (am_r c'))
  (* the amalgamation: the span is coequalized *)
  | ae_glue : ∀ a : carrier A,
      am_eq (am_l (f a)) (am_r (g a))
  (* the group laws, in their left-handed form *)
  | ae_assoc : ∀ u v w,
      am_eq (am_mul (am_mul u v) w) (am_mul u (am_mul v w))
  | ae_unit_l : ∀ u, am_eq (am_mul am_one u) u
  | ae_inv_l : ∀ u, am_eq (am_mul (am_inv u) u) am_one
  (* congruence for the two operations *)
  | ae_mul_cong : ∀ u u' v v',
      am_eq u u' → am_eq v v' →
      am_eq (am_mul u v) (am_mul u' v')
  | ae_inv_cong : ∀ u u',
      am_eq u u' → am_eq (am_inv u) (am_inv u')
  (* symmetry and transitivity; reflexivity is derived below *)
  | ae_sym : ∀ u v, am_eq u v → am_eq v u
  | ae_trans : ∀ u v w, am_eq u v → am_eq v w → am_eq u w.

Arguments ae_l_resp {A B C f g} _ _ _.
Arguments ae_r_resp {A B C f g} _ _ _.
Arguments ae_l_mul {A B C f g} _ _.
Arguments ae_r_mul {A B C f g} _ _.
Arguments ae_glue {A B C f g} _.
Arguments ae_assoc {A B C f g} _ _ _.
Arguments ae_unit_l {A B C f g} _.
Arguments ae_inv_l {A B C f g} _.
Arguments ae_mul_cong {A B C f g} _ _ _ _ _ _.
Arguments ae_inv_cong {A B C f g} _ _ _.
Arguments ae_sym {A B C f g} _ _ _.
Arguments ae_trans {A B C f g} _ _ _ _ _.

Section AmalgamCore.

Context {A B C : GrpObject}.
Context (f : A ~{Grp}~> B) (g : A ~{Grp}~> C).

(* Reflexivity is DERIVED rather than posted as a constructor.  Every
   former has a congruence rule except [am_one], and the unit itself is
   reached by [ae_unit_l am_one] composed with its own symmetry. *)
Lemma am_eq_refl (u : AmTerm B C) : am_eq f g u u.
Proof.
  induction u as [b | c | | u IHu v IHv | u IHu].
  - apply ae_l_resp; reflexivity.
  - apply ae_r_resp; reflexivity.
  - exact (ae_trans _ _ _ (ae_sym _ _ (ae_unit_l am_one)) (ae_unit_l am_one)).
  - exact (ae_mul_cong _ _ _ _ IHu IHv).
  - exact (ae_inv_cong _ _ IHu).
Qed.

Definition AmSetoid : Setoid (AmTerm B C) := {|
  equiv := am_eq f g;
  setoid_equiv :=
    Build_Equivalence (am_eq f g) am_eq_refl (ae_sym) (ae_trans)
|}.

Definition AmCarrier : SetoidObject := {|
  carrier := AmTerm B C;
  is_setoid := AmSetoid
|}.

(* The amalgamated free product B *_A C.  Every group law is a
   CONSTRUCTOR of [am_eq], so the record below is a literal with no proof
   obligation of its own -- the [Instance/Mod/Free.v] payoff.

   CORRECTION.  That sentence was exactly true before the PR "algebraic
   carriers are sets" (2026-09-17).  The record now has a ninth field,
   [grp_prop], which is not a group law; it is still supplied by a literal
   here, and costs no obligation, because [am_eq] IS the [Prop] relation and
   the two implications are the identity.  So the record remains a literal
   with no proof obligation of its own -- with one more field in it. *)
Definition AmalgamGrp : GrpObject := {|
  grp_setoid := AmCarrier;
  grp_unit := am_one;
  grp_mul := am_mul;
  grp_inv := am_inv;
  grp_mul_respects := fun u u' Hu v v' Hv => ae_mul_cong _ _ _ _ Hu Hv;
  grp_mul_assoc := ae_assoc;
  grp_mul_unit_l := ae_unit_l;
  grp_mul_inv_l := ae_inv_l;
  grp_prop :=
    @PropEquiv_of_relation _ AmSetoid (am_eq f g)
      (fun _ _ h => h) (fun _ _ h => h)
|}.

(** ** The two injections *)

Definition am_inj1_map
  : SetoidMorphism (grp_setoid B) (grp_setoid AmalgamGrp).
Proof.
  unshelve notypeclasses refine {| morphism := am_l |}.
  intros b b' Hb; exact (ae_l_resp b b' Hb).
Defined.

Definition am_inj2_map
  : SetoidMorphism (grp_setoid C) (grp_setoid AmalgamGrp).
Proof.
  unshelve notypeclasses refine {| morphism := am_r |}.
  intros c c' Hc; exact (ae_r_resp c c' Hc).
Defined.

Definition am_inj1 : B ~{Grp}~> AmalgamGrp :=
  Build_GrpHom' am_inj1_map (fun b b' => ae_l_mul b b').

Definition am_inj2 : C ~{Grp}~> AmalgamGrp :=
  Build_GrpHom' am_inj2_map (fun c c' => ae_r_mul c c').

(* The pushout square commutes: this IS the [ae_glue] constructor. *)
Lemma am_square : am_inj1 ∘[Grp] f ≈ am_inj2 ∘[Grp] g.
Proof. intro a; exact (ae_glue a). Qed.

End AmalgamCore.

Arguments AmalgamGrp {A B C} f g.
Arguments am_inj1 {A B C} f g.
Arguments am_inj2 {A B C} f g.

(** ** The mediating homomorphism *)

Section AmalgamMediator.

Context {A B C : GrpObject}.
Context (f : A ~{Grp}~> B) (g : A ~{Grp}~> C).
Context {Q : GrpObject}.
Context (q1 : B ~{Grp}~> Q) (q2 : C ~{Grp}~> Q).

(* Evaluation of a formal word in a competing group.  A [Fixpoint], so
   the three homomorphism laws of the mediator hold DEFINITIONALLY. *)
Fixpoint am_eval (t : AmTerm B C) : carrier Q :=
  match t with
  | am_l b => grp_map q1 b
  | am_r c => grp_map q2 c
  | am_one => grp_unit Q
  | am_mul u v => grp_mul Q (am_eval u) (am_eval v)
  | am_inv u => grp_inv Q (am_eval u)
  end.

Context (Hcomm : q1 ∘[Grp] f ≈ q2 ∘[Grp] g).

(* Well-definedness on the quotient, by induction on the derivation.  The
   glue case is the ONLY one that consumes [Hcomm]; every other case is a
   law of [Q] or of one of the two homomorphisms. *)
(* [am_eq] is a [Prop] since the PR "algebraic carriers are sets"
   (2026-09-17), so the induction may not land in the [Type]-valued goal
   [am_eval u ≈ am_eval v] directly.  The whole proof is therefore conducted
   inside [Q]'s own [Prop] equality: [pequiv_to] opens it, each of the twelve
   branches closes with [pequiv_from] and then runs the ORIGINAL tactic
   unchanged, and [ae_sym]/[ae_trans] use [pequiv]'s own transported
   equivalence laws.  No mathematics moved. *)
Lemma am_eval_respects (u v : AmTerm B C) (H : am_eq f g u v) :
  am_eval u ≈ am_eval v.
Proof using All.
  apply (@pequiv_to _ _ (grp_prop Q)).
  induction H as
    [ b b' Hbb' | c c' Hcc' | b b' | c c' | a
    | u v w | u | u
    | u u' v v' Huu' IHu Hvv' IHv
    | u u' Huu' IHu
    | u v Huv IHuv
    | u v w Huv IHuv Hvw IHvw ].
  - apply (@pequiv_from _ _ (grp_prop Q)); simpl; now apply proper_morphism.
  - apply (@pequiv_from _ _ (grp_prop Q)); simpl; now apply proper_morphism.
  - apply (@pequiv_from _ _ (grp_prop Q)); simpl; now apply grp_map_mul.
  - apply (@pequiv_from _ _ (grp_prop Q)); simpl; now apply grp_map_mul.
  - apply (@pequiv_from _ _ (grp_prop Q)); simpl; exact (Hcomm a).
  - apply (@pequiv_from _ _ (grp_prop Q)); simpl; now apply grp_mul_assoc.
  - apply (@pequiv_from _ _ (grp_prop Q)); simpl; now apply grp_mul_unit_l.
  - apply (@pequiv_from _ _ (grp_prop Q)); simpl; now apply grp_mul_inv_l.
  - apply (@pequiv_from _ _ (grp_prop Q)); simpl.
    apply grp_mul_respects;
      [ exact (@pequiv_to _ _ (grp_prop Q) _ _ IHu)
      | exact (@pequiv_to _ _ (grp_prop Q) _ _ IHv) ].
  - apply (@pequiv_from _ _ (grp_prop Q)); simpl.
    apply grp_inv_respects_law.
    exact (@pequiv_to _ _ (grp_prop Q) _ _ IHu).
  - now symmetry.
  - now transitivity (am_eval v).
Qed.

Definition am_eval_map
  : SetoidMorphism (grp_setoid (AmalgamGrp f g)) (grp_setoid Q).
Proof using All.
  unshelve notypeclasses refine {| morphism := am_eval |}.
  intros u v Huv; exact (am_eval_respects u v Huv).
Defined.

Definition am_med : AmalgamGrp f g ~{Grp}~> Q :=
  Build_GrpHom' am_eval_map (fun u v => reflexivity _).

Lemma am_med_inj1 : am_med ∘[Grp] am_inj1 f g ≈ q1.
Proof. intro b; reflexivity. Qed.

Lemma am_med_inj2 : am_med ∘[Grp] am_inj2 f g ≈ q2.
Proof. intro c; reflexivity. Qed.

(* Uniqueness, by induction on the WORD rather than on the congruence: a
   competing homomorphism is pinned on the two insertions by hypothesis
   and on the three formers by its own homomorphism laws. *)
Lemma am_med_unique (v : AmalgamGrp f g ~{Grp}~> Q)
      (H1 : v ∘[Grp] am_inj1 f g ≈ q1)
      (H2 : v ∘[Grp] am_inj2 f g ≈ q2) :
  am_med ≈ v.
Proof.
  intro t.
  induction t as [b | c | | s IHs t IHt | s IHs]; simpl.
  - symmetry; exact (H1 b).
  - symmetry; exact (H2 c).
  - symmetry; exact (grp_map_unit v).
  - transitivity (grp_mul Q (grp_map v s) (grp_map v t)).
    + now apply grp_mul_respects.
    + symmetry; exact (grp_map_mul v s t).
  - transitivity (grp_inv Q (grp_map v s)).
    + now apply grp_inv_respects_law.
    + symmetry; exact (grp_map_inv v s).
Qed.

End AmalgamMediator.


(** ** The universal property, packaged *)

Local Obligation Tactic := idtac.

#[export] Program Instance Grp_HasPushouts : HasPushouts Grp := {|
  pushout := fun A B C f g =>
    {| Pull         := AmalgamGrp f g;
       pullback_fst := am_inj1 f g;
       pullback_snd := am_inj2 f g
    |}
|}.
Next Obligation.
  intros A B C f g.
  exact (am_square f g).
Defined.
Next Obligation.
  intros A B C f g Q q1 q2 Hcomm.
  unshelve refine {| unique_obj := am_med f g q1 q2 Hcomm |}.
  - split.
    + exact (am_med_inj1 f g q1 q2 Hcomm).
    + exact (am_med_inj2 f g q1 q2 Hcomm).
  - intros v [Hv1 Hv2].
    exact (am_med_unique f g q1 q2 Hcomm v Hv1 Hv2).
Defined.

(** ** The chosen pushout, and what reduces *)

Definition Grp_pushout {A B C : GrpObject}
           (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) : IsPushout f g :=
  @pushout Grp Grp_HasPushouts A B C f g.

(* The apex and both injections are the hand-built ones ON THE NOSE. *)
Example Grp_pushout_apex_is_AmalgamGrp {A B C : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) :
  pushout_apex (Grp_pushout f g) = AmalgamGrp f g := eq_refl.

Example Grp_pushout_in1_is_am_inj1 {A B C : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) :
  pushout_in1 (Grp_pushout f g) = am_inj1 f g := eq_refl.

Example Grp_pushout_in2_is_am_inj2 {A B C : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) :
  pushout_in2 (Grp_pushout f g) = am_inj2 f g := eq_refl.

(* The carrier of the apex is literally the type of formal words, and the
   group operations are literally the formers. *)
Example Grp_pushout_carrier {A B C : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) :
  carrier (AmalgamGrp f g) = AmTerm B C := eq_refl.

Example Grp_pushout_mul {A B C : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) :
  grp_mul (AmalgamGrp f g) = am_mul := eq_refl.

Example Grp_pushout_unit {A B C : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) :
  grp_unit (AmalgamGrp f g) = am_one := eq_refl.

Example Grp_pushout_inv {A B C : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) :
  grp_inv (AmalgamGrp f g) = am_inv := eq_refl.

(* The mediator's action on the two generating families reduces. *)
Example am_med_on_left {A B C Q : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C)
        (q1 : B ~{Grp}~> Q) (q2 : C ~{Grp}~> Q)
        (Hcomm : q1 ∘[Grp] f ≈ q2 ∘[Grp] g) (b : carrier B) :
  grp_map (am_med f g q1 q2 Hcomm) (am_l b) = grp_map q1 b := eq_refl.

Example am_med_on_right {A B C Q : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C)
        (q1 : B ~{Grp}~> Q) (q2 : C ~{Grp}~> Q)
        (Hcomm : q1 ∘[Grp] f ≈ q2 ∘[Grp] g) (c : carrier C) :
  grp_map (am_med f g q1 q2 Hcomm) (am_r c) = grp_map q2 c := eq_refl.

(* [pushout_med], by contrast, does NOT reduce to [am_med]: Structure/
   Pushout.v states [pushout_ump] as a [Qed] lemma, so [unique_obj] is
   applied to an opaque constant.  The equation holds up to [≈], which is
   what the universal property gives; the strict form is pinned as a
   negative in Test/ProbePushoutGrpTop.v, with the opacity as its
   diagnosed cause. *)
Lemma Grp_pushout_med_is_am_med {A B C Q : GrpObject}
      (f : A ~{Grp}~> B) (g : A ~{Grp}~> C)
      (q1 : B ~{Grp}~> Q) (q2 : C ~{Grp}~> Q)
      (Hcomm : q1 ∘[Grp] f ≈ q2 ∘[Grp] g) :
  pushout_med (Grp_pushout f g) Hcomm ≈ am_med f g q1 q2 Hcomm.
Proof.
  apply (pushout_med_unique (Grp_pushout f g) Hcomm).
  - exact (am_med_inj1 f g q1 q2 Hcomm).
  - exact (am_med_inj2 f g q1 q2 Hcomm).
Qed.

(** ** Mac Lane's monic-legs refinement, at split strength *)

Section GrpSplitRefinement.

Context {A B C : GrpObject}.
Context (f : A ~{Grp}~> B) (g : A ~{Grp}~> C).

(* The generic statements of Structure/Pushout/Split.v, transported to the
   named injections.  The transport is by CONVERSION -- [pushout_in1
   (Grp_pushout f g)] IS [am_inj1 f g], recorded above by [eq_refl] -- so
   each of these is an [exact] of the generic term. *)
Definition am_inj1_Section (Sg : Section g) : Section (am_inj1 f g) :=
  pushout_in1_Section_of_Retraction (Grp_pushout f g) Sg.

Definition am_inj2_Section (Sf : Section f) : Section (am_inj2 f g) :=
  pushout_in2_Section_of_Retraction (Grp_pushout f g) Sf.

(* The weaker hypothesis the free product actually uses: not that the
   opposite leg splits, but that one leg FACTORS through the other. *)
Definition am_inj1_Section_of_factor (r : C ~{Grp}~> B)
           (Hr : r ∘[Grp] g ≈ f) : Section (am_inj1 f g) :=
  pushout_in1_Section (Grp_pushout f g) r Hr.

Definition am_inj2_Section_of_factor (s : B ~{Grp}~> C)
           (Hs : s ∘[Grp] f ≈ g) : Section (am_inj2 f g) :=
  pushout_in2_Section (Grp_pushout f g) s Hs.

Theorem am_inj1_Monic (Sg : Section g) : Monic (am_inj1 f g).
Proof. exact (sections_are_monic _ _ _ (am_inj1_Section Sg)). Qed.

Theorem am_inj2_Monic (Sf : Section f) : Monic (am_inj2 f g).
Proof. exact (sections_are_monic _ _ _ (am_inj2_Section Sf)). Qed.

(* The refinement in the shape Mac Lane states it, at split strength: both
   legs split, therefore both injections are monic AND the vertex is the
   amalgamated product -- the latter definitionally, [AmalgamGrp f g]
   being the apex on the nose. *)
Theorem Grp_split_legs_monic_injections (Sf : Section f) (Sg : Section g) :
  Monic (am_inj1 f g) * Monic (am_inj2 f g).
Proof. exact (am_inj1_Monic Sg, am_inj2_Monic Sf). Qed.

(* Read down to elements through Instance/Grp.v's own characterization of
   monomorphisms: split legs make the two insertions INJECTIVE.  The
   hypotheses are spelled with [am_eq f g], which IS the apex's [≈] by
   construction ([AmSetoid]), so no coercion or transport intervenes. *)
Corollary am_inj1_injective (Sg : Section g) :
  ∀ b b' : carrier B, am_eq f g (am_l b) (am_l b') → b ≈ b'.
Proof.
  exact (snd (Grp_injectivity_is_monic (am_inj1 f g)) (am_inj1_Monic Sg)).
Qed.

Corollary am_inj2_injective (Sf : Section f) :
  ∀ c c' : carrier C, am_eq f g (am_r c) (am_r c') → c ≈ c'.
Proof.
  exact (snd (Grp_injectivity_is_monic (am_inj2 f g)) (am_inj2_Monic Sf)).
Qed.

End GrpSplitRefinement.

(** ** The free product, as the pushout along the constant legs *)

(* The constant homomorphism at the unit.  Multiplicativity is the unit's
   own idempotence, so [Build_GrpHom'] supplies unit-preservation. *)
Definition grp_const_map (A G : GrpObject)
  : SetoidMorphism (grp_setoid A) (grp_setoid G).
Proof.
  unshelve notypeclasses refine {| morphism := fun _ => grp_unit G |}.
  intros a b _; reflexivity.
Defined.

Definition grp_const (A G : GrpObject) : A ~{Grp}~> G.
Proof.
  refine (Build_GrpHom' (grp_const_map A G) _).
  intros a b; simpl.
  symmetry; apply grp_mul_unit_l.
Defined.

(* THE ROUTE NOT TAKEN, and why.  The free product is classically the
   pushout over the TRIVIAL group, and that span's legs even SPLIT --
   [Grp_zero_hom]'s retraction is [Grp_one], the two composites living in
   a hom-set Instance/Grp.v has already proved to be a singleton.  The
   lemma is recorded here because it is the honest classical statement.
   But [Instance/Grp.v]'s [Grp_zero_hom] is declared over
   [GrpObject@{Set Set Set}] -- a donor pin of the family
   Instance/Grp/Quotient/Colimit.v records for [Grp_trivial] -- so
   everything built on it would be confined to [Set]-sized groups.  The
   free product below therefore goes through the CONSTANT legs instead,
   which needs no zero object and carries no pin; the probe file pins the
   donor's rejection above [Set] against this file's acceptance there.
   CORRECTION (#450): the donor pin is lifted in Instance/Grp.v, this
   lemma is universe-polymorphic since ([Grp_zero_hom_Section@{u u0}]),
   and the probe's two negatives are controls. *)
Definition Grp_zero_hom_Section (G : GrpObject) : Section (Grp_zero_hom G).
Proof.
  unshelve refine {| section := Grp_one G |}.
  exact (Grp_zero_hom_unique Grp_trivial
           (Grp_one G ∘[Grp] Grp_zero_hom G) (@id Grp Grp_trivial)).
Defined.

(* B * C: the amalgam along the two constant legs.  This is an INSTANCE of
   the amalgamated product, not a second construction.

   THE SPAN APEX PLAYS NO ROLE, and that is visible rather than argued:
   [AmTerm B C] does not mention the apex at all, and the apex enters
   [am_eq] only through [ae_glue a], whose statement here is
   [am_l (grp_unit B) ~ am_r (grp_unit C)] for EVERY [a] -- one relation,
   repeated, and already derivable from the two insertions'
   unit-preservation.  [B] is taken as the apex only because it is at
   hand.  (That the congruences over two different apexes coincide is not
   stated as a lemma; what IS proved is that this object has the
   coproduct's universal property, which is what a consumer needs.) *)
Definition Grp_free_product (B C : GrpObject) : GrpObject :=
  AmalgamGrp (grp_const B B) (grp_const B C).

Definition Grp_fp_inl (B C : GrpObject) : B ~{Grp}~> Grp_free_product B C :=
  am_inj1 (grp_const B B) (grp_const B C).

Definition Grp_fp_inr (B C : GrpObject) : C ~{Grp}~> Grp_free_product B C :=
  am_inj2 (grp_const B B) (grp_const B C).

(* Any pair of homomorphisms out of B and C automatically forms a cocone
   over the constant span, both composites being constant at the unit of
   Q.  So the free product's copairing needs no compatibility hypothesis
   at all. *)
Lemma Grp_fp_cocone {B C Q : GrpObject}
      (q1 : B ~{Grp}~> Q) (q2 : C ~{Grp}~> Q) :
  q1 ∘[Grp] grp_const B B ≈ q2 ∘[Grp] grp_const B C.
Proof.
  intro b; simpl.
  transitivity (grp_unit Q).
  - exact (grp_map_unit q1).
  - symmetry; exact (grp_map_unit q2).
Qed.

Definition Grp_fp_merge {B C Q : GrpObject}
           (q1 : B ~{Grp}~> Q) (q2 : C ~{Grp}~> Q)
  : Grp_free_product B C ~{Grp}~> Q :=
  am_med (grp_const B B) (grp_const B C) q1 q2 (Grp_fp_cocone q1 q2).

(* Both free-product injections are split monic, with NO hypothesis: each
   constant leg factors through the other, via a third constant map. *)
Lemma grp_const_absorb {A A' G : GrpObject} (h : A ~{Grp}~> A') :
  grp_const A' G ∘[Grp] h ≈ grp_const A G.
Proof. intro a; reflexivity. Qed.

Definition Grp_fp_inl_Section (B C : GrpObject) : Section (Grp_fp_inl B C) :=
  am_inj1_Section_of_factor (grp_const B B) (grp_const B C)
    (grp_const C B) (grp_const_absorb (grp_const B C)).

Definition Grp_fp_inr_Section (B C : GrpObject) : Section (Grp_fp_inr B C) :=
  am_inj2_Section_of_factor (grp_const B B) (grp_const B C)
    (grp_const B C) (grp_const_absorb (grp_const B B)).

Theorem Grp_free_product_injections_Monic (B C : GrpObject) :
  Monic (Grp_fp_inl B C) * Monic (Grp_fp_inr B C).
Proof.
  exact (sections_are_monic _ _ _ (Grp_fp_inl_Section B C),
         sections_are_monic _ _ _ (Grp_fp_inr_Section B C)).
Qed.

(** ** The free product IS the coproduct of Grp

    Cross-reference: the GENERAL bridge "a pushout over the initial object
    is the binary coproduct" is open issue #862 (Seven Sketches 6.2.3) and
    is NOT built here.  What follows is the ad-hoc Grp instance: the
    commutation hypothesis of the pushout's universal property is
    discharged once and for all by [Grp_fp_cocone], leaving exactly the
    coproduct's universal property. *)

Local Obligation Tactic := idtac.

#[export] Program Instance Grp_Cocartesian : @Cocartesian Grp := {|
  product_obj := Grp_free_product;
  fork := fun _ _ _ q1 q2 => Grp_fp_merge q1 q2;
  exl := fun B C => Grp_fp_inl B C;
  exr := fun B C => Grp_fp_inr B C
|}.
Next Obligation.
  intros Q B C q1 q1' H1 q2 q2' H2.
  intro t.
  induction t as [b | c | | s IHs t IHt | s IHs]; simpl.
  - exact (H1 b).
  - exact (H2 c).
  - reflexivity.
  - now apply grp_mul_respects.
  - now apply grp_inv_respects_law.
Qed.
Next Obligation.
  intros Q B C q1 q2 h.
  split.
  - intro Hh.
    split.
    + intro b; exact (Hh (am_l b)).
    + intro c; exact (Hh (am_r c)).
  - intros [Hl Hr].
    symmetry.
    exact (am_med_unique (grp_const B B) (grp_const B C) q1 q2
             (Grp_fp_cocone q1 q2) h Hl Hr).
Qed.

(** ** Non-vacuity

    Nothing below can be proved by induction on [am_eq]: a NEGATIVE fact
    about a generated congruence is only reachable by mapping OUT of the
    quotient, which is what the universal property is for.  Every
    separation here therefore runs through a concrete homomorphism into
    [Instance/Grp.v]'s [Z2]. *)

(* The separating homomorphism out of Z2 * Z2: the identity on the left
   summand, the constant map on the right. *)
Definition fp_probe : Grp_free_product Z2 Z2 ~{Grp}~> Z2 :=
  Grp_fp_merge (@id Grp Z2) (grp_const Z2 Z2).

Example fp_probe_left :
  grp_map fp_probe (@am_l Z2 Z2 true) = true := eq_refl.
Example fp_probe_right :
  grp_map fp_probe (@am_r Z2 Z2 true) = false := eq_refl.

(* The free product does NOT merge the two summands' generators. *)
Theorem fp_generators_distinct :
  am_eq (grp_const Z2 Z2) (grp_const Z2 Z2)
    (@am_l Z2 Z2 true) (@am_r Z2 Z2 true) → False.
Proof.
  intro H.
  assert (Hq : @equiv _ bool_setoid
                 (grp_map fp_probe (@am_l Z2 Z2 true))
                 (grp_map fp_probe (@am_r Z2 Z2 true)))
    by (apply proper_morphism; exact H).
  simpl in Hq.
  discriminate Hq.
Qed.

(* ...and does not merge distinct elements of one summand either, which is
   [Grp_fp_inl_Section] read down to elements. *)
Theorem fp_inl_injective :
  am_eq (grp_const Z2 Z2) (grp_const Z2 Z2)
    (@am_l Z2 Z2 true) (@am_l Z2 Z2 false) → False.
Proof.
  intro H.
  assert (Hq : @equiv _ bool_setoid true false).
  { exact (snd (Grp_injectivity_is_monic (Grp_fp_inl Z2 Z2))
             (fst (Grp_free_product_injections_Monic Z2 Z2))
             true false H). }
  discriminate Hq.
Qed.

(* THE CONTRAST that makes the amalgamation content rather than
   bookkeeping: over the SAME two groups, amalgamating along the identity
   DOES merge the very pair the free product keeps apart. *)
Theorem amalgam_over_Z2_merges :
  am_eq (@id Grp Z2) (@id Grp Z2) (@am_l Z2 Z2 true) (@am_r Z2 Z2 true).
Proof. exact (@ae_glue Z2 Z2 Z2 (@id Grp Z2) (@id Grp Z2) true). Qed.
