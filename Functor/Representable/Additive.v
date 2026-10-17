(** * The Ab-valued hom functor, and the additive upgrade of a representation *)

(*
   Book:      Mac Lane, ibid., §I.8 and §VIII.2 — Ab-categories and
   nLab:      https://ncatlab.org/nlab/show/Eilenberg-Watts+theorem
   nLab:      https://ncatlab.org/nlab/show/additive+functor
   nLab:      https://ncatlab.org/nlab/show/representable+functor

   本文件给出加性相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.AbCategory.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Adjunction.Additive.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Functor.Hom.Continuous.
Require Import Category.Instance.Ab.Limit.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** ** The opposite of a locally propositional category *)

Definition LocallyPropositional_op@{o h +} {C : Category@{o h h}}
  (LP : LocallyPropositional C) : LocallyPropositional (C^op).
Proof. constructor; intros x y; exact (@locally_prop C LP y x). Defined.

Example LocallyPropositional_op_at@{o h +} {C : Category@{o h h}}
  (LP : LocallyPropositional C) (x y : C) :
  @locally_prop (C^op) (LocallyPropositional_op LP) x y
    = @locally_prop C LP y x := eq_refl.

(** ** The Ab-valued hom functor *)

Section HomAbFunctor.

Universes o h a.

Context {C : Category@{o h h}}.
Context {LP : LocallyPropositional C}.
Context (AC : AbEnriched C).
Context (A0 : C).

Definition HomAb_fmap {x y : C} (f : x ~{C}~> y) :
  hom_ab AC A0 x ~{Ab@{a h}}~> hom_ab AC A0 y.
Proof.
  unshelve econstructor; [unshelve econstructor|..].
  - exact (fun g => f ∘ g).
  - intros g g' H. exact (@compose_respects C _ _ _ f f (reflexivity f) g g' H).
  - exact (@compose_pzero_right _ (@abenriched_preadditive C AC) _ _ _ f).
  - intros g k.
    exact (@compose_padd_left _ (@abenriched_preadditive C AC) _ _ _ f g k).
Defined.

Program Definition HomAb : C ⟶ Ab@{a h} := {|
  fobj := fun x => hom_ab AC A0 x;
  fmap := fun x y f => HomAb_fmap f
|}.
Next Obligation.
  intros x y f f' H g.
  exact (@compose_respects C _ _ _ f f' H g g (reflexivity g)).
Qed.
Next Obligation. intros x g; simpl. apply (@id_left C). Qed.
Next Obligation. intros x y z f k g; simpl. apply (@comp_assoc_sym C). Qed.

Example HomAb_obj (x : C) : fobj[HomAb] x = hom_ab AC A0 x := eq_refl.

Example HomAb_fmap_at {x y : C} (f : x ~{C}~> y) (g : A0 ~{C}~> x) :
  cmon_map (fmap[HomAb] f) g = f ∘ g := eq_refl.

(* Post-composition is additive in the arrow composed with. *)
Definition HomAb_additive :
  @AdditiveFunctor C Ab@{a h} AC Ab_AbEnriched HomAb.
Proof.
  constructor.
  intros x y f g k; simpl.
  exact (@compose_padd_right _ (@abenriched_preadditive C AC) _ _ _ f g k).
Defined.

(* Forgetting the group structure gives back the Sets-valued hom functor,
   componentwise by the identity map. *)
Definition HomAb_forget_to : [Hom A0,─] ⟹ Ab_Forget ◯ HomAb.
Proof.
  unshelve eapply Build_Transform'.
  - intro x; simpl.
    exact {| morphism := fun g => g; proper_morphism := fun g g' H => H |}.
  - intros x y f g; simpl; reflexivity.
Defined.

Definition HomAb_forget_from : Ab_Forget ◯ HomAb ⟹ [Hom A0,─].
Proof.
  unshelve eapply Build_Transform'.
  - intro x; simpl.
    exact {| morphism := fun g => g; proper_morphism := fun g g' H => H |}.
  - intros x y f g; simpl; reflexivity.
Defined.

Definition HomAb_forget_iso : [Hom A0,─] ≅[Fun] Ab_Forget ◯ HomAb.
Proof.
  unshelve econstructor.
  - exact HomAb_forget_to.
  - exact HomAb_forget_from.
  - intros x g; simpl; now rewrite id_left.
  - intros x g; simpl; now rewrite id_left.
Defined.

#[local] Obligation Tactic := idtac.

Definition HomAb_representable : Representable (Ab_Forget ◯ HomAb) :=
  {| repr_obj := A0; represented := HomAb_forget_iso |}.

End HomAbFunctor.

Arguments HomAb {C LP} AC A0.
Arguments HomAb_fmap {C LP} AC A0 {x y} f.
Arguments HomAb_additive {C LP} AC A0.
Arguments HomAb_representable {C LP} AC A0.

(** ** The contravariant Ab-valued hom functor *)

Definition CoHomAb@{o h a +} {C : Category@{o h h}}
  {LP : LocallyPropositional C} (AC : AbEnriched C) (A0 : C) :
  C^op ⟶ Ab@{a h} :=
  @HomAb (C^op) (LocallyPropositional_op LP) (AbEnriched_op AC) A0.

Example CoHomAb_fmap_at@{o h a +} {C : Category@{o h h}}
  {LP : LocallyPropositional C} (AC : AbEnriched C) (A0 : C) {x y : C}
  (f : y ~{C}~> x) (g : x ~{C}~> A0) :
  cmon_map (fmap[CoHomAb AC A0] f) g = g ∘ f := eq_refl.

(** ** The Ab-valued hom functors are continuous *)

(* Forgetting the group structure of [HomAb AC A0] gives the Sets-valued
   hom functor up to the identity-component iso [HomAb_forget_iso], which
   is continuous; [Ab_Forget] reflects limit cones, and [cone_assoc_inv]
   repackages a cone over [Ab_Forget ◯ (HomAb ◯ K)] as one over
   [(Ab_Forget ◯ HomAb) ◯ K]. *)
Definition HomAb_continuous@{o h a +}
  {C : Category@{o h h}} {LP : LocallyPropositional C}
  (AC : AbEnriched C) (A0 : C) :
  ContinuousFunctor (HomAb AC A0 : C ⟶ Ab@{a h}) :=
  fun J K N HN =>
    Ab_Forget_reflects_limits (HomAb AC A0 ◯ K) (FCone (HomAb AC A0) N)
      (fun M => representable_iso_ContinuousFunctor A0
                  (iso_equiv (HomAb_forget_iso AC A0)) J K N HN
                  (cone_assoc_inv M)).

(* The contravariant one is the covariant one at [C^op]: it carries the
   colimits of C, which are the limits of [C^op], to limits of [Ab]. *)
Definition CoHomAb_continuous@{o h a +}
  {C : Category@{o h h}} {LP : LocallyPropositional C}
  (AC : AbEnriched C) (A0 : C) :
  ContinuousFunctor (CoHomAb AC A0 : C^op ⟶ Ab@{a h}) :=
  @HomAb_continuous (C^op) (LocallyPropositional_op LP) (AbEnriched_op AC) A0.

(** ** The additive upgrade *)

Section AdditiveUpgrade.

Universes o h a s.

Context {C : Category@{o h h}}.
Context {LP : LocallyPropositional C}.
Context (AC : AbEnriched C).
Context (T : C ⟶ Ab@{a h}).
Context (AF : @AdditiveFunctor C Ab@{a h} AC Ab_AbEnriched T).
Context (Rp : Representable (Ab_Forget@{a s h} ◯ T)).

Definition wab_obj : C := @repr_obj _ _ Rp.

Definition wab_to (x : C) :=
  transform[to (@represented _ _ Rp)] x.

Definition wab_from (x : C) :=
  transform[from (@represented _ _ Rp)] x.

Definition wab_elem : carrier (cmon_setoid (T wab_obj)) :=
  wab_to wab_obj (@id C wab_obj).

Lemma wab_to_elem (x : C) (f : wab_obj ~{C}~> x) :
  wab_to x f ≈ cmon_map (fmap[T] f) wab_elem.
Proof using T Rp.
  pose proof (@naturality _ _ _ _ (to (@represented _ _ Rp)) wab_obj x f
                (@id C wab_obj)) as N.
  unfold wab_to, wab_elem.
  etransitivity; [|symmetry; exact N].
  apply proper_morphism. simpl. symmetry.
  rewrite ?id_left, ?id_right. reflexivity.
Qed.

Lemma wab_to_padd (x : C) (f g : wab_obj ~{C}~> x) :
  wab_to x (@padd _ (@abenriched_preadditive C AC) _ _ f g)
    ≈ cmon_plus (T x) (wab_to x f) (wab_to x g).
Proof using AF.
  rewrite wab_to_elem, wab_to_elem, wab_to_elem.
  pose proof (@fmap_padd _ _ _ _ T AF _ _ f g wab_elem) as H. simpl in H.
  exact H.
Qed.

Lemma wab_to_pzero (x : C) :
  wab_to x (@pzero _ (@abenriched_preadditive C AC) wab_obj x)
    ≈ cmon_zero (T x).
Proof using AF.
  rewrite wab_to_elem.
  pose proof (@fmap_pzero _ _ _ _ T AF wab_obj x wab_elem) as H. simpl in H.
  exact H.
Qed.

Lemma wab_to_from (x : C) (t : carrier (cmon_setoid (T x))) :
  wab_to x (wab_from x t) ≈ t.
Proof using T Rp.
  pose proof (@iso_to_from _ _ _ (@represented _ _ Rp) x t) as H.
  simpl in H. etransitivity; [exact H|]. exact (@fmap_id _ _ T x t).
Qed.

Lemma wab_from_to (x : C) (f : wab_obj ~{C}~> x) :
  wab_from x (wab_to x f) ≈ f.
Proof using T Rp.
  pose proof (@iso_from_to _ _ _ (@represented _ _ Rp) x f) as H.
  simpl in H. etransitivity; [exact H|]. rewrite ?id_left, ?id_right.
  reflexivity.
Qed.

Definition wab_to_hom (x : C) : hom_ab AC wab_obj x ~{Ab@{a h}}~> T x.
Proof using AF.
  unshelve econstructor; [unshelve econstructor|..].
  - exact (wab_to x).
  - exact (@proper_morphism _ _ _ _ (wab_to x)).
  - exact (wab_to_pzero x).
  - exact (wab_to_padd x).
Defined.

Definition wab_from_hom (x : C) : T x ~{Ab@{a h}}~> hom_ab AC wab_obj x.
Proof using AF.
  unshelve econstructor; [unshelve econstructor|..].
  - exact (wab_from x).
  - exact (@proper_morphism _ _ _ _ (wab_from x)).
  - transitivity
      (wab_from x
         (wab_to x (@pzero _ (@abenriched_preadditive C AC) wab_obj x))).
    + apply proper_morphism. symmetry. apply wab_to_pzero.
    + apply wab_from_to.
  - intros t u.
    transitivity (wab_from x (wab_to x
      (@padd _ (@abenriched_preadditive C AC) _ _
         (wab_from x t) (wab_from x u)))).
    + apply proper_morphism. rewrite wab_to_padd, !wab_to_from. reflexivity.
    + apply wab_from_to.
Defined.

Definition wab_to_nat : HomAb AC wab_obj ⟹ T.
Proof using AF.
  unshelve eapply Build_Transform'.
  - exact wab_to_hom.
  - intros x y f g; simpl.
    exact (@naturality _ _ _ _ (to (@represented _ _ Rp)) x y f g).
Defined.

Definition wab_from_nat : T ⟹ HomAb AC wab_obj.
Proof using AF.
  unshelve eapply Build_Transform'.
  - exact wab_from_hom.
  - intros x y f t; simpl.
    exact (@naturality _ _ _ _ (from (@represented _ _ Rp)) x y f t).
Defined.

Definition watt_ab_iso : @Isomorphism (@Fun C Ab@{a h}) (HomAb AC wab_obj) T.
Proof using AF.
  unshelve econstructor.
  - exact wab_to_nat.
  - exact wab_from_nat.
  - intros x t; simpl. etransitivity; [exact (wab_to_from x t)|].
    symmetry; exact (@fmap_id _ _ T x t).
  - intros x f; simpl. etransitivity; [exact (wab_from_to x f)|].
    rewrite ?id_left, ?id_right. reflexivity.
Defined.

Example watt_ab_iso_to_at (x : C) (f : wab_obj ~{C}~> x) :
  cmon_map (transform[to watt_ab_iso] x) f
    = transform[to (@represented _ _ Rp)] x f := eq_refl.

Example watt_ab_iso_from_at (x : C) (t : carrier (cmon_setoid (T x))) :
  cmon_map (transform[from watt_ab_iso] x) t
    = transform[from (@represented _ _ Rp)] x t := eq_refl.

(* Tactic form, kept as a precaution only: the term-mode [existT]
   spelling, and the anonymous-constructor one, also compile on Coq
   8.19.2 and 8.20.1 (measured in scratch copies against built 8.19.2 and
   8.20.1 closures of this file). *)
Definition watt_ab_repr :
  { A : C & @Isomorphism (@Fun C Ab@{a h}) (HomAb AC A) T }.
Proof using AF Rp. exists wab_obj. exact watt_ab_iso. Defined.

End AdditiveUpgrade.

Arguments wab_obj {C T} Rp.
Arguments watt_ab_iso {C LP} AC T AF Rp.
Arguments watt_ab_repr {C LP} AC T AF Rp.

(** ** Non-vacuity: the hom functor itself *)

Definition watt_ab_iso_HomAb@{o h a +} {C : Category@{o h h}}
  {LP : LocallyPropositional C} (AC : AbEnriched C) (A0 : C) :
  @Isomorphism (@Fun C Ab@{a h})
    (HomAb AC (wab_obj (HomAb_representable AC A0))) (HomAb AC A0) :=
  watt_ab_iso AC (HomAb AC A0) (HomAb_additive AC A0)
    (HomAb_representable AC A0).

Example watt_ab_iso_HomAb_obj@{o h a +} {C : Category@{o h h}}
  {LP : LocallyPropositional C} (AC : AbEnriched C) (A0 : C) :
  @wab_obj C (HomAb@{o h a} AC A0) (HomAb_representable AC A0) = A0 :=
  eq_refl.

(* The hypotheses are met in tree: at [Ab] itself, by [Ab_AbEnriched] and
   [Ab_LocallyPropositional]. *)
Definition watt_ab_iso_at_Ab@{a b h +} (A0 : AbObject@{h h h}) :
  @Isomorphism (@Fun Ab@{a h} Ab@{b h})
    (HomAb Ab_AbEnriched (wab_obj (HomAb_representable Ab_AbEnriched A0)))
    (HomAb Ab_AbEnriched A0) :=
  watt_ab_iso_HomAb Ab_AbEnriched A0.
