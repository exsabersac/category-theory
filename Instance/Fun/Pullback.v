Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Structure.Pullback.
Require Import Category.Instance.Fun.

Generalizable All Variables.

Set Default Proof Using "All".

(** * Pointwise pullbacks in a functor category *)

(*
   本文件给出拉回实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------ *)
(** ** (A) Pointwise pullbacks give a pullback in [C, D] *)

Section FunIsPullback.

Context {C D : Category}.
Context {F G H P : C ⟶ D}.
Context (alpha : F ~{[C, D]}~> H) (beta : G ~{[C, D]}~> H).
Context (p1 : P ~{[C, D]}~> F) (p2 : P ~{[C, D]}~> G).
Context (Hpt : ∀ x : C, IsPullback (transform[alpha] x) (transform[beta] x)
                          (P x) (transform[p1] x) (transform[p2] x)).

(* Two arrows into the apex agreeing on both legs agree: the standard
   consequence of the universal property, used to prove naturality of the
   mediator. *)
Lemma fpb_jointly_monic (x : C) {Z : D} (u v : Z ~> P x) :
  transform[p1] x ∘ u ≈ transform[p1] x ∘ v →
  transform[p2] x ∘ u ≈ transform[p2] x ∘ v → u ≈ v.
Proof.
  intros Hu Hv.
  assert (Hs : transform[alpha] x ∘ (transform[p1] x ∘ u)
                 ≈ transform[beta] x ∘ (transform[p2] x ∘ u)).
  { rewrite !comp_assoc. now rewrite (is_pullback_commutes (Hpt x)). }
  pose proof (is_pullback_ump (Hpt x) Z
                (transform[p1] x ∘ u) (transform[p2] x ∘ u) Hs) as U.
  transitivity (unique_obj U).
  - symmetry; apply (uniqueness U); split; reflexivity.
  - apply (uniqueness U); split; [ now rewrite <- Hu | now rewrite <- Hv ].
Qed.

Definition Fun_IsPullback : IsPullback alpha beta P p1 p2.
Proof.
  unshelve refine (Build_IsPullback ([C, D]) F G H alpha beta P p1 p2 _ _).
  - intro x; exact (is_pullback_commutes (Hpt x)).
  - intros Q q1 q2 Hq.
    unshelve refine {| unique_obj := _ |}.
    + unshelve refine (@Build_Transform' C D Q P
        (fun x => unique_obj (is_pullback_ump (Hpt x) (Q x)
                    (transform[q1] x) (transform[q2] x) (Hq x))) _).
      intros x y h.
      set (mx := unique_obj (is_pullback_ump (Hpt x) (Q x)
                   (transform[q1] x) (transform[q2] x) (Hq x))).
      set (my := unique_obj (is_pullback_ump (Hpt y) (Q y)
                   (transform[q1] y) (transform[q2] y) (Hq y))).
      assert (Hmx1 : transform[p1] x ∘ mx ≈ transform[q1] x)
        by (unfold mx; now destruct (unique_property (is_pullback_ump (Hpt x)
              (Q x) (transform[q1] x) (transform[q2] x) (Hq x)))).
      assert (Hmx2 : transform[p2] x ∘ mx ≈ transform[q2] x)
        by (unfold mx; now destruct (unique_property (is_pullback_ump (Hpt x)
              (Q x) (transform[q1] x) (transform[q2] x) (Hq x)))).
      assert (Hmy1 : transform[p1] y ∘ my ≈ transform[q1] y)
        by (unfold my; now destruct (unique_property (is_pullback_ump (Hpt y)
              (Q y) (transform[q1] y) (transform[q2] y) (Hq y)))).
      assert (Hmy2 : transform[p2] y ∘ my ≈ transform[q2] y)
        by (unfold my; now destruct (unique_property (is_pullback_ump (Hpt y)
              (Q y) (transform[q1] y) (transform[q2] y) (Hq y)))).
      apply (fpb_jointly_monic y).
      * rewrite !comp_assoc.
        rewrite <- (@naturality _ _ _ _ p1 _ _ h).
        rewrite Hmy1, <- comp_assoc, Hmx1.
        apply (@naturality _ _ _ _ q1).
      * rewrite !comp_assoc.
        rewrite <- (@naturality _ _ _ _ p2 _ _ h).
        rewrite Hmy2, <- comp_assoc, Hmx2.
        apply (@naturality _ _ _ _ q2).
    + split; intro x; simpl;
        now destruct (unique_property (is_pullback_ump (Hpt x) (Q x)
                        (transform[q1] x) (transform[q2] x) (Hq x))).
    + intros v [Hv1 Hv2] x; simpl in *.
      apply (uniqueness (is_pullback_ump (Hpt x) (Q x)
               (transform[q1] x) (transform[q2] x) (Hq x))).
      split; [ apply Hv1 | apply Hv2 ].
Defined.

End FunIsPullback.

(* ------------------------------------------------------------------ *)
(** ** (B) The chosen pointwise pullback *)

Section FunPullback.

Context {C D : Category}.
Context (HP : @HasPullbacks D).
Context {F G H : C ⟶ D}.
Context (alpha : F ~{[C, D]}~> H) (beta : G ~{[C, D]}~> H).

Definition fpb_at (x : C) :
  Pullback (transform[alpha] x) (transform[beta] x)
  := pullback (transform[alpha] x) (transform[beta] x).

Definition fpb_obj (x : C) : D := Pull _ _ (fpb_at x).
Definition fpb_fst (x : C) : fpb_obj x ~> F x := pullback_fst _ _ (fpb_at x).
Definition fpb_snd (x : C) : fpb_obj x ~> G x := pullback_snd _ _ (fpb_at x).

Lemma fpb_commutes (x : C) :
  transform[alpha] x ∘ fpb_fst x ≈ transform[beta] x ∘ fpb_snd x.
Proof. exact (pullback_commutes _ _ (fpb_at x)). Qed.

(* The square the arrow action factors through: the two naturality
   squares of alpha and beta plus the pointwise commuting square. *)
Lemma fpb_arr_sq {x y : C} (h : x ~> y) :
  transform[alpha] y ∘ (fmap[F] h ∘ fpb_fst x)
    ≈ transform[beta] y ∘ (fmap[G] h ∘ fpb_snd x).
Proof.
  rewrite !comp_assoc.
  rewrite <- (@naturality _ _ _ _ alpha _ _ h).
  rewrite <- (@naturality _ _ _ _ beta _ _ h).
  rewrite <- !comp_assoc.
  now rewrite fpb_commutes.
Qed.

Definition fpb_arr {x y : C} (h : x ~> y) : fpb_obj x ~> fpb_obj y :=
  unique_obj (ump_pullbacks _ _ (fpb_at y) (fpb_obj x)
                (fmap[F] h ∘ fpb_fst x) (fmap[G] h ∘ fpb_snd x)
                (fpb_arr_sq h)).

Lemma fpb_arr_fst {x y : C} (h : x ~> y) :
  fpb_fst y ∘ fpb_arr h ≈ fmap[F] h ∘ fpb_fst x.
Proof.
  unfold fpb_arr.
  now destruct (unique_property (ump_pullbacks _ _ (fpb_at y) (fpb_obj x)
                  (fmap[F] h ∘ fpb_fst x) (fmap[G] h ∘ fpb_snd x)
                  (fpb_arr_sq h))).
Qed.

Lemma fpb_arr_snd {x y : C} (h : x ~> y) :
  fpb_snd y ∘ fpb_arr h ≈ fmap[G] h ∘ fpb_snd x.
Proof.
  unfold fpb_arr.
  now destruct (unique_property (ump_pullbacks _ _ (fpb_at y) (fpb_obj x)
                  (fmap[F] h ∘ fpb_fst x) (fmap[G] h ∘ fpb_snd x)
                  (fpb_arr_sq h))).
Qed.

Lemma fpb_arr_uniq {x y : C} (h : x ~> y) (u : fpb_obj x ~> fpb_obj y) :
  fpb_fst y ∘ u ≈ fmap[F] h ∘ fpb_fst x →
  fpb_snd y ∘ u ≈ fmap[G] h ∘ fpb_snd x → u ≈ fpb_arr h.
Proof.
  intros H1 H2. unfold fpb_arr. symmetry.
  apply (uniqueness (ump_pullbacks _ _ (fpb_at y) (fpb_obj x)
           (fmap[F] h ∘ fpb_fst x) (fmap[G] h ∘ fpb_snd x) (fpb_arr_sq h))).
  now split.
Qed.

(* All three functor laws are the uniqueness clause of the pullback
   applied to the two legs. *)
Definition Fun_Pullback_Functor : C ⟶ D.
Proof.
  unshelve refine (@Build_Functor C D fpb_obj (@fpb_arr) _ _ _).
  - intros x y h1 h2 Hh.
    apply fpb_arr_uniq.
    + rewrite fpb_arr_fst. now rewrite Hh.
    + rewrite fpb_arr_snd. now rewrite Hh.
  - intros x. symmetry. apply fpb_arr_uniq.
    + rewrite fmap_id, id_left, id_right; reflexivity.
    + rewrite fmap_id, id_left, id_right; reflexivity.
  - intros x y z h1 h2. symmetry. apply fpb_arr_uniq.
    + rewrite comp_assoc, fpb_arr_fst, <- comp_assoc, fpb_arr_fst, comp_assoc.
      now rewrite fmap_comp.
    + rewrite comp_assoc, fpb_arr_snd, <- comp_assoc, fpb_arr_snd, comp_assoc.
      now rewrite fmap_comp.
Defined.

(* Naturality of each projection IS the defining equation of the arrow
   action, read backwards. *)
Definition Fun_Pullback_fst : Fun_Pullback_Functor ~{[C, D]}~> F.
Proof.
  unshelve refine (@Build_Transform' C D Fun_Pullback_Functor F fpb_fst _).
  intros x y h. simpl. symmetry. apply fpb_arr_fst.
Defined.

Definition Fun_Pullback_snd : Fun_Pullback_Functor ~{[C, D]}~> G.
Proof.
  unshelve refine (@Build_Transform' C D Fun_Pullback_Functor G fpb_snd _).
  intros x y h. simpl. symmetry. apply fpb_arr_snd.
Defined.

Definition Fun_Pullback_IsPullback :
  IsPullback alpha beta Fun_Pullback_Functor Fun_Pullback_fst Fun_Pullback_snd
  := Fun_IsPullback alpha beta Fun_Pullback_fst Fun_Pullback_snd
       (fun x => pullback_is_pullback _ _ (fpb_at x)).

Definition Fun_Pullback : @Pullback ([C, D]) F G H alpha beta
  := is_pullback_pullback Fun_Pullback_IsPullback.

End FunPullback.

Definition Fun_HasPullbacks {C D : Category} (HP : @HasPullbacks D) :
  @HasPullbacks ([C, D]) :=
  {| pullback := fun F G H alpha beta => Fun_Pullback HP alpha beta |}.

(* ------------------------------------------------------------------ *)
(** ** (C) Readbacks *)

Example fun_pullback_obj_at {C D : Category} (HP : @HasPullbacks D)
  {F G H : C ⟶ D} (alpha : F ~{[C, D]}~> H) (beta : G ~{[C, D]}~> H) (x : C) :
  fobj[Pull _ _ (Fun_Pullback HP alpha beta)] x
    = Pull _ _ (pullback (transform[alpha] x) (transform[beta] x)) := eq_refl.

Example fun_pullback_fst_at {C D : Category} (HP : @HasPullbacks D)
  {F G H : C ⟶ D} (alpha : F ~{[C, D]}~> H) (beta : G ~{[C, D]}~> H) (x : C) :
  transform[pullback_fst _ _ (Fun_Pullback HP alpha beta)] x
    = pullback_fst _ _ (pullback (transform[alpha] x) (transform[beta] x))
  := eq_refl.

Example fun_pullback_snd_at {C D : Category} (HP : @HasPullbacks D)
  {F G H : C ⟶ D} (alpha : F ~{[C, D]}~> H) (beta : G ~{[C, D]}~> H) (x : C) :
  transform[pullback_snd _ _ (Fun_Pullback HP alpha beta)] x
    = pullback_snd _ _ (pullback (transform[alpha] x) (transform[beta] x))
  := eq_refl.

Example fun_haspullbacks_readback {C D : Category} (HP : @HasPullbacks D)
  {F G H : C ⟶ D} (alpha : F ~{[C, D]}~> H) (beta : G ~{[C, D]}~> H) :
  @pullback ([C, D]) (Fun_HasPullbacks HP) F G H alpha beta
    = Fun_Pullback HP alpha beta := eq_refl.

(* The mediator is D's mediator at every component, ON THE NOSE
   ([fun_pullback_med_strict]); the [≈] form below is the weakening a
   consumer rewrites with. *)
Example fun_pullback_med_strict {C D : Category} (HP : @HasPullbacks D)
  {F G H : C ⟶ D} (alpha : F ~{[C, D]}~> H) (beta : G ~{[C, D]}~> H)
  {Q : C ⟶ D} (q1 : Q ~{[C, D]}~> F) (q2 : Q ~{[C, D]}~> G)
  (Hq : alpha ∘ q1 ≈ beta ∘ q2) (x : C) :
  transform[unique_obj (ump_pullbacks _ _ (Fun_Pullback HP alpha beta) Q
                          q1 q2 Hq)] x
    = unique_obj (ump_pullbacks _ _ (fpb_at HP alpha beta x) (Q x)
                    (transform[q1] x) (transform[q2] x) (Hq x))
  := eq_refl.

Lemma fun_pullback_med_at {C D : Category} (HP : @HasPullbacks D)
  {F G H : C ⟶ D} (alpha : F ~{[C, D]}~> H) (beta : G ~{[C, D]}~> H)
  {Q : C ⟶ D} (q1 : Q ~{[C, D]}~> F) (q2 : Q ~{[C, D]}~> G)
  (Hq : alpha ∘ q1 ≈ beta ∘ q2) (x : C) :
  transform[unique_obj (ump_pullbacks _ _ (Fun_Pullback HP alpha beta) Q
                          q1 q2 Hq)] x
    ≈ unique_obj (ump_pullbacks _ _ (fpb_at HP alpha beta x) (Q x)
                    (transform[q1] x) (transform[q2] x) (Hq x)).
Proof.
  apply (uniqueness (ump_pullbacks _ _ (fpb_at HP alpha beta x) (Q x)
           (transform[q1] x) (transform[q2] x) (Hq x))).
  destruct (unique_property (ump_pullbacks _ _ (Fun_Pullback HP alpha beta) Q
                               q1 q2 Hq)) as [Hu1 Hu2].
  split; [ exact (Hu1 x) | exact (Hu2 x) ].
Qed.
