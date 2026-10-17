Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Theory.Sieve.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.SubobjectClassifier.Natural.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Fun.Morphisms.
Require Import Category.Instance.Fun.Pullback.
Require Import Category.Instance.Two.
Require Import Category.Instance.FinSet.

Generalizable All Variables.

Set Default Proof Using "All".

(** * The subobject classifier of a set-valued functor category *)

(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(* ---------------- (A) the truth transformation ---------------- *)

Program Definition sieve_truth (C : Category) :
  @terminal_obj ([C^op, Sets]) (Functor_Category_Terminal Sets_Terminal)
    ⟹ Sieve_Presheaf C := {|
  transform := fun c => {| morphism := fun _ => @total_sieve C c |}
|}.
Next Obligation.
  intros C c; unfold Proper, respectful; intros u v _ d g; simpl.
  split; auto.
Qed.
Next Obligation. intros C x y f u d k; simpl; split; auto. Qed.
Next Obligation. intros C x y f u d k; simpl; split; auto. Qed.

Example sieve_truth_at (C : Category) (c : C)
  (u : carrier (fobj[@terminal_obj ([C^op, Sets])
                       (Functor_Category_Terminal Sets_Terminal)] c)) :
  transform[sieve_truth C] c u = @total_sieve C c := eq_refl.

(* ---------------- (B) the characteristic transformation ------- *)

Section Char.

Context {C : Category}.
Context {E : C^op ⟶ Sets}.
Context {U : C^op ⟶ Sets}.
Context (theta : U ⟹ E).

Definition Efmap_resp {c d : C} (f g : d ~{C}~> c) (Hfg : f ≈ g)
      (e : carrier (fobj[E] c)) : fmap[E] f e ≈ fmap[E] g e
  := @fmap_respects (C^op) Sets E c d f g Hfg e.

Definition Efmap_comp {c d d' : C} (f : d ~{C}~> c) (g : d' ~{C}~> d)
      (x : carrier (fobj[E] c)) :
  fmap[E] (f ∘ g) x ≈ fmap[E] g (fmap[E] f x)
  := @fmap_comp (C^op) Sets E c d d' g f x.

Definition Efmap_id {c : C} (x : carrier (fobj[E] c)) :
  fmap[E] (@id C c) x ≈ x
  := @fmap_id (C^op) Sets E c x.

Definition theta_natural {c d : C} (f : d ~{C}~> c)
    (x : carrier (fobj[U] c)) :
  fmap[E] f (transform[theta] c x) ≈ transform[theta] d (fmap[U] f x)
  := @naturality (C^op) Sets U E theta c d f x.

Definition in_image (d : C) (y : carrier (fobj[E] d)) : Type :=
  ∃ x : carrier (fobj[U] d), transform[theta] d x ≈ y.

Program Definition char_sieve (c : C) (e : carrier (fobj[E] c)) :
  @Sieve C c := {|
  sieve_mem := fun d (f : d ~{C}~> c) =>
                 Powerset_squash (in_image d (fmap[E] f e))
|}.
Next Obligation.
  intros c e d f g Hfg Hmem Q k.
  apply Hmem; intros [x Hx]; apply k; exists x.
  transitivity (fmap[E] f e); [ exact Hx | exact (Efmap_resp f g Hfg e) ].
Qed.
Next Obligation.
  intros c e d d' f g Hmem Q k.
  apply Hmem; intros [x Hx]; apply k.
  exists (fmap[U] g x).
  transitivity (fmap[E] g (transform[theta] d x)).
  - symmetry; exact (theta_natural g x).
  - transitivity (fmap[E] g (fmap[E] f e)).
    + exact (proper_morphism (fmap[E] g) _ _ Hx).
    + symmetry; exact (Efmap_comp f g e).
Qed.

Program Definition char_at (c : C) :
  fobj[E] c ~{Sets}~> @SieveObj C c := {|
  morphism := char_sieve c
|}.
Next Obligation.
  intros c.
  unfold Proper, respectful; intros e e' Hee' d f; simpl.
  split; intros Hmem Q k; apply Hmem; intros [x Hx]; apply k; exists x.
  - transitivity (fmap[E] f e); [ exact Hx | ].
    exact (proper_morphism (fmap[E] f) _ _ Hee').
  - transitivity (fmap[E] f e'); [ exact Hx | ].
    symmetry; exact (proper_morphism (fmap[E] f) _ _ Hee').
Qed.

Program Definition char_nat : E ⟹ Sieve_Presheaf C := {|
  transform := char_at
|}.
Next Obligation.
  intros x y h e d g; simpl.
  pose proof (@Efmap_comp x y d h g e) as Hc.
  split; intros Hmem Q k; apply Hmem; intros [a Ha]; apply k; exists a;
    rewrite Ha; [ exact Hc | symmetry; exact Hc ].
Qed.
Next Obligation.
  intros x y h e d g; simpl.
  pose proof (@Efmap_comp x y d h g e) as Hc.
  split; intros Hmem Q k; apply Hmem; intros [a Ha]; apply k; exists a;
    rewrite Ha; [ symmetry; exact Hc | exact Hc ].
Qed.

(* the square commutes, with no hypothesis at all *)
Theorem char_square :
  char_nat ∘[[C^op, Sets]] theta
    ≈ sieve_truth C ∘[[C^op, Sets]]
        @one ([C^op, Sets]) (Functor_Category_Terminal Sets_Terminal) U.
Proof.
  intros c x d f; simpl.
  split; intro Hm; [ exact I | ].
  intros Q k; apply k.
  exists (fmap[U] f x).
  symmetry; exact (theta_natural f x).
Qed.

End Char.

(* ---------------- (C) a sieve as a subobject of y(c) ---------- *)

Section SieveSub.

Context {C : Category}.

Lemma sieve_sub_eq (c : C) (S : Sieve c) (k : C) :
  Equivalence (fun u v : { g : k ~{C}~> c & sieve_mem S g } =>
                 projT1 u ≈ projT1 v).
Proof.
  constructor; repeat intro.
  - reflexivity.
  - now symmetry.
  - etransitivity; eassumption.
Qed.

Definition sieve_sub_obj (c : C) (S : Sieve c) (k : C) : SetoidObject :=
  {| carrier := { g : k ~{C}~> c & sieve_mem S g }
   ; is_setoid := {| equiv := fun u v => projT1 u ≈ projT1 v
                   ; setoid_equiv := sieve_sub_eq c S k |} |}.

Definition sieve_sub_map (c : C) (S : Sieve c) (k j : C) (h : j ~{C}~> k) :
  sieve_sub_obj c S k ~{Sets}~> sieve_sub_obj c S j.
Proof.
  unshelve refine {| morphism := fun u => existT _ (projT1 u ∘ h) _ |}.
  - exact (sieve_closed S (projT1 u) h (projT2 u)).
  - intros u v Huv; simpl in *. now rewrite Huv.
Defined.

Definition sieve_subpresheaf (c : C) (S : Sieve c) : C^op ⟶ Sets.
Proof.
  unshelve refine (@Build_Functor (C^op) Sets (sieve_sub_obj c S)
                     (fun k j (h : k ~{C^op}~> j) => sieve_sub_map c S k j h)
                     _ _ _).
  - intros k j h1 h2 Hh u; simpl. now rewrite Hh.
  - intros k u; simpl. apply id_right.
  - intros k j l h1 h2 u; simpl. apply comp_assoc.
Defined.

Definition sieve_incl (c : C) (S : Sieve c) :
  sieve_subpresheaf c S ~{[C^op, Sets]}~> Curried_CoHom C c.
Proof.
  unshelve refine (@Build_Transform' (C^op) Sets (sieve_subpresheaf c S)
                     (Curried_CoHom C c) (fun k => _) _).
  - unshelve refine {| morphism := fun u => projT1 u |}.
    intros u v Huv; exact Huv.
  - intros k j h u; simpl. reflexivity.
Defined.

Definition sieve_incl_Monic (c : C) (S : Sieve c) :
  @Monic ([C^op, Sets]) _ _ (sieve_incl c S) :=
  snd (presheaf_monic_iff_injective (sieve_incl c S))
      (fun k a b Hab => Hab).

Definition sieve_subobject (c : C) (S : Sieve c) :
  @SubObj ([C^op, Sets]) (Curried_CoHom C c) :=
  @Build_SubObj ([C^op, Sets]) (Curried_CoHom C c)
    (sieve_subpresheaf c S) (sieve_incl c S) (sieve_incl_Monic c S).

(* the cone into E determined by an element of E c *)
Definition sieve_cone {E : C^op ⟶ Sets} (c : C) (e : carrier (fobj[E] c))
  (S : Sieve c) : sieve_subpresheaf c S ~{[C^op, Sets]}~> E.
Proof.
  unshelve refine (@Build_Transform' (C^op) Sets (sieve_subpresheaf c S) E
                     (fun k => _) _).
  - unshelve refine {| morphism := fun u => fmap[E] (projT1 u) e |}.
    intros u v Huv; simpl in *.
    exact (@fmap_respects _ _ E c k (projT1 u) (projT1 v) Huv e).
  - intros k j h u; simpl. symmetry.
    exact (@fmap_comp _ _ E c k j h (projT1 u) e).
Defined.

End SieveSub.

(* ---------------- (D) uniqueness of the classifying map ------- *)

Section Unique.

Context {C : Category}.
Context {E U : C^op ⟶ Sets}.
Context (theta : U ⟹ E).
Context (h : E ⟹ Sieve_Presheaf C).
Context (HP : @IsPullback ([C^op, Sets]) E
                (@terminal_obj _ (Functor_Category_Terminal Sets_Terminal))
                (Sieve_Presheaf C) h (sieve_truth C) U theta
                (@one _ (Functor_Category_Terminal Sets_Terminal) U)).

Lemma char_sub_h (c : C) (e : carrier (fobj[E] c)) (d : C) (f : d ~{C}~> c) :
  sieve_mem (char_sieve theta c e) f -> sieve_mem (transform[h] c e) f.
Proof.
  intro Hf. apply Hf. intros [x Hx].
  pose proof (is_pullback_commutes HP d x) as Hc; simpl in Hc.
  assert (Hid : sieve_mem (transform[h] d (fmap[E] f e)) (@id C d)).
  { assert (Heq : transform[h] d (transform[theta] d x)
                    ≈ transform[h] d (fmap[E] f e))
      by (apply proper_morphism; exact Hx).
    apply (proj1 (Heq d (@id C d))).
    exact (proj2 (Hc d (@id C d)) I). }
  pose proof (@naturality _ _ _ _ h c d f e) as Hn; simpl in Hn.
  pose proof (proj2 (Hn d (@id C d)) Hid) as Hm2; simpl in Hm2.
  eapply sieve_respects; [ | exact Hm2 ]. apply id_right.
Qed.

Lemma h_sub_char (c : C) (e : carrier (fobj[E] c)) (d : C) (f : d ~{C}~> c) :
  sieve_mem (transform[h] c e) f -> sieve_mem (char_sieve theta c e) f.
Proof.
  intro Hf.
  set (ed := fmap[E] f e).
  set (S := transform[h] d ed).
  assert (HidS : sieve_mem S (@id C d)).
  { unfold S, ed.
    pose proof (@naturality _ _ _ _ h c d f e) as Hn; simpl in Hn.
    apply (proj1 (Hn d (@id C d))). simpl.
    eapply sieve_respects; [ | exact Hf ]. symmetry. apply id_right. }
  set (q1 := @sieve_cone C E d ed S).
  assert (Hcone : ∀ (k : C) (u : carrier (sieve_sub_obj d S k)),
            sieve_equiv (transform[h] k (transform[q1] k u)) (total_sieve k)).
  { intros k u j g. split; intro; [ exact I | ].
    unfold q1, sieve_cone; simpl.
    pose proof (@naturality _ _ _ _ h d k (projT1 u) ed) as Hn; simpl in Hn.
    apply (proj1 (Hn j g)). simpl.
    exact (sieve_closed S (projT1 u) g (projT2 u)). }
  assert (Hsq : h ∘[[C^op, Sets]] q1
                  ≈ sieve_truth C ∘[[C^op, Sets]]
                      @one ([C^op, Sets])
                        (Functor_Category_Terminal Sets_Terminal)
                        (sieve_subpresheaf d S))
    by (intros k u j g; exact (Hcone k u j g)).
  pose proof (is_pullback_ump HP (sieve_subpresheaf d S) q1
                (@one _ (Functor_Category_Terminal Sets_Terminal) _) Hsq)
    as UM.
  destruct (unique_property UM) as [Hu1 Hu2].
  intros P kk. apply kk.
  exists (transform[unique_obj UM] d (existT _ (@id C d) HidS)).
  pose proof (Hu1 d (existT _ (@id C d) HidS)) as Hval; simpl in Hval.
  rewrite Hval. exact (@fmap_id _ _ E d ed).
Qed.

Theorem presheaf_char_unique : h ≈ char_nat theta.
Proof.
  intros c e d f; split; [ apply h_sub_char | apply char_sub_h ].
Qed.

End Unique.

(* ---------------- (E) the classifying square is a pullback ---- *)

Section Pullback.

Context {C : Category}.
Context (UT : Untruncate).
Context {E U : C^op ⟶ Sets}.
Context (theta : U ⟹ E).
Context (M : @Monic ([C^op, Sets]) U E theta).

Definition theta_inj : ∀ (c : C^op) (a b : carrier (fobj[U] c)),
    transform[theta] c a ≈ transform[theta] c b -> a ≈ b
  := fst (presheaf_monic_iff_injective theta) M.

Definition med_img {Q : C^op ⟶ Sets} (q1 : Q ⟹ E)
  (Hq : ∀ (c : C) (z : carrier (fobj[Q] c)),
          sieve_mem (char_sieve theta c (transform[q1] c z)) (@id C c))
  (c : C) (z : carrier (fobj[Q] c)) : in_image theta c (transform[q1] c z).
Proof.
  pose proof (UT _ (Hq c z)) as Hx.
  destruct Hx as [x Hx].
  exists x.
  transitivity (fmap[E] (@id C c) (transform[q1] c z)); [ exact Hx | ].
  exact (Efmap_id (E:=E) (transform[q1] c z)).
Defined.

Definition med_elt {Q : C^op ⟶ Sets} (q1 : Q ⟹ E)
  (Hq : ∀ (c : C) (z : carrier (fobj[Q] c)),
          sieve_mem (char_sieve theta c (transform[q1] c z)) (@id C c))
  (c : C) (z : carrier (fobj[Q] c)) : carrier (fobj[U] c) :=
  projT1 (med_img q1 Hq c z).

Definition med_spec {Q : C^op ⟶ Sets} (q1 : Q ⟹ E)
  (Hq : ∀ (c : C) (z : carrier (fobj[Q] c)),
          sieve_mem (char_sieve theta c (transform[q1] c z)) (@id C c))
  (c : C) (z : carrier (fobj[Q] c)) :
  transform[theta] c (med_elt q1 Hq c z) ≈ transform[q1] c z :=
  projT2 (med_img q1 Hq c z).

Program Definition char_med {Q : C^op ⟶ Sets} (q1 : Q ⟹ E)
  (Hq : ∀ (c : C) (z : carrier (fobj[Q] c)),
          sieve_mem (char_sieve theta c (transform[q1] c z)) (@id C c)) :
  Q ⟹ U := {|
  transform := fun c => {| morphism := fun z => med_elt q1 Hq c z |}
|}.
Next Obligation.
  intros Q q1 Hq c.
  unfold Proper, respectful; intros z z' Hzz'.
  apply (theta_inj c).
  transitivity (transform[q1] c z); [ exact (med_spec q1 Hq c z) | ].
  transitivity (transform[q1] c z').
  - exact (proper_morphism (transform[q1] c) _ _ Hzz').
  - symmetry; exact (med_spec q1 Hq c z').
Qed.
Next Obligation.
  intros Q q1 Hq x y f z; simpl.
  apply (theta_inj y).
  transitivity (fmap[E] f (transform[theta] x (med_elt q1 Hq x z))).
  - symmetry; exact (theta_natural theta f (med_elt q1 Hq x z)).
  - transitivity (fmap[E] f (transform[q1] x z)).
    + exact (proper_morphism (fmap[E] f) _ _ (med_spec q1 Hq x z)).
    + transitivity (transform[q1] y (fmap[Q] f z)).
      * exact (@naturality (C^op) Sets Q E q1 x y f z).
      * symmetry; exact (med_spec q1 Hq y (fmap[Q] f z)).
Qed.
Next Obligation.
  intros Q q1 Hq x y f z; simpl.
  symmetry.
  apply (theta_inj y).
  transitivity (fmap[E] f (transform[theta] x (med_elt q1 Hq x z))).
  - symmetry; exact (theta_natural theta f (med_elt q1 Hq x z)).
  - transitivity (fmap[E] f (transform[q1] x z)).
    + exact (proper_morphism (fmap[E] f) _ _ (med_spec q1 Hq x z)).
    + transitivity (transform[q1] y (fmap[Q] f z)).
      * exact (@naturality (C^op) Sets Q E q1 x y f z).
      * symmetry; exact (med_spec q1 Hq y (fmap[Q] f z)).
Qed.

Definition presheaf_char_pullback :
  @IsPullback ([C^op, Sets]) E
    (@terminal_obj _ (Functor_Category_Terminal Sets_Terminal))
    (Sieve_Presheaf C) (char_nat theta) (sieve_truth C) U theta
    (@one _ (Functor_Category_Terminal Sets_Terminal) U).
Proof.
  constructor.
  - exact (char_square theta).
  - intros Q q1 q2 Hcomm.
    assert (Hq : ∀ (c : C) (z : carrier (fobj[Q] c)),
               sieve_mem (char_sieve theta c (transform[q1] c z)) (@id C c)).
    { intros c z. exact (proj2 (Hcomm c z c (@id C c)) I). }
    unshelve refine {| unique_obj := char_med q1 Hq |}.
    + split.
      * intros c z; simpl. exact (med_spec q1 Hq c z).
      * intros c z; simpl. destruct (transform[q2] c z); reflexivity.
    + intros v [Hv1 Hv2] c z; simpl.
      apply (theta_inj c).
      transitivity (transform[q1] c z); [ exact (med_spec q1 Hq c z) | ].
      symmetry; exact (Hv1 c z).
Defined.

End Pullback.

(* ---------------- (F) the classifier ---------------- *)

Definition Fun_Classifier {C : Category} (UT : Untruncate) :
  @SubobjectClassifier ([C^op, Sets])
    (Functor_Category_Terminal Sets_Terminal) :=
  @Build_SubobjectClassifier ([C^op, Sets])
    (Functor_Category_Terminal Sets_Terminal)
    (Sieve_Presheaf C)
    (sieve_truth C)
    (fun U E theta M => char_nat theta)
    (fun U E theta M => presheaf_char_pullback UT theta M)
    (fun U E theta M h HP => presheaf_char_unique theta h HP).

Definition Fun_Classifier_IEM {C : Category} (Em : IEM) :
  @SubobjectClassifier ([C^op, Sets])
    (Functor_Category_Terminal Sets_Terminal) :=
  Fun_Classifier (untruncate_of_IEM Em).

Definition Fun_Classifier_cov {D : Category} (UT : Untruncate) :
  @SubobjectClassifier ([D, Sets])
    (Functor_Category_Terminal Sets_Terminal) :=
  @Fun_Classifier (D^op) UT.

Example fun_classifier_omega {C : Category} (UT : Untruncate) :
  @Ω ([C^op, Sets]) _ (Fun_Classifier UT) = Sieve_Presheaf C := eq_refl.
Example fun_classifier_truth {C : Category} (UT : Untruncate) :
  @truth ([C^op, Sets]) _ (Fun_Classifier UT) = sieve_truth C := eq_refl.
Example fun_classifier_char {C : Category} (UT : Untruncate)
  {U E : C^op ⟶ Sets} (theta : U ⟹ E) (M : @Monic ([C^op, Sets]) U E theta) :
  @char ([C^op, Sets]) _ (Fun_Classifier UT) U E theta M = char_nat theta
  := eq_refl.

(* ---------------- (G) the arrow shape ---------------- *)

Example op_op_two : (_2^op)^op = _2 := eq_refl.
Check (Sieve_Presheaf (_2^op) : _2 ⟶ Sets).

Definition twoX_pred (P Q : Prop) :
  ∀ (d : _2^op), (d ~{_2^op}~> TwoX) → Prop :=
  fun d => match d with TwoX => fun _ => P | TwoY => fun _ => Q end.

Program Definition twoX_sieve (P Q : Prop) (H : P -> Q) :
  @Sieve (_2^op) TwoX := {| sieve_mem := twoX_pred P Q |}.
Next Obligation. intros P Q H d f g Hfg Hmem; destruct d; exact Hmem. Qed.
Next Obligation.
  intros P Q H d e f g Hmem.
  destruct d, e; simpl in *;
    try solve [ destruct (TwoHom_Y_X_absurd f) ];
    try solve [ destruct (TwoHom_Y_X_absurd g) ];
    auto.
Qed.

Definition twoX_total : @Sieve (_2^op) TwoX :=
  twoX_sieve True True (fun x => x).
Definition twoX_mid : @Sieve (_2^op) TwoX :=
  twoX_sieve False True (fun x => match x return True with end).
Definition twoX_empty : @Sieve (_2^op) TwoX :=
  twoX_sieve False False (fun x => x).

Definition twoY_pred (R : Prop) :
  ∀ (d : _2^op), (d ~{_2^op}~> TwoY) → Prop :=
  fun d => match d with TwoY => fun _ => R | TwoX => fun _ => True end.

Program Definition twoY_sieve (R : Prop) : @Sieve (_2^op) TwoY :=
  {| sieve_mem := twoY_pred R |}.
Next Obligation. intros R d f g Hfg Hmem; destruct d; exact Hmem. Qed.
Next Obligation.
  intros R d e f g Hmem.
  destruct d, e; simpl in *;
    try solve [ destruct (TwoHom_Y_X_absurd f) ];
    try solve [ destruct (TwoHom_Y_X_absurd g) ];
    auto.
Qed.

Definition twoY_total : @Sieve (_2^op) TwoY := twoY_sieve True.
Definition twoY_empty : @Sieve (_2^op) TwoY := twoY_sieve False.

Theorem twoX_total_neq_mid : twoX_total ≈ twoX_mid -> False.
Proof. intro H. exact (proj1 (H TwoX TwoIdX) I). Qed.
Theorem twoX_mid_neq_empty : twoX_mid ≈ twoX_empty -> False.
Proof. intro H. exact (proj1 (H TwoY TwoXY) I). Qed.
Theorem twoX_total_neq_empty : twoX_total ≈ twoX_empty -> False.
Proof. intro H. exact (proj1 (H TwoX TwoIdX) I). Qed.
Theorem twoY_total_neq_empty : twoY_total ≈ twoY_empty -> False.
Proof. intro H. exact (proj1 (H TwoY TwoIdY) I). Qed.

Theorem twoX_sieve_normal (S : @Sieve (_2^op) TwoX) :
  S ≈ twoX_sieve (sieve_mem S TwoIdX) (sieve_mem S TwoXY)
        (fun p => sieve_closed S TwoIdX TwoXY p).
Proof.
  intros d f; destruct d;
    [ pose proof (TwoHom_inv TwoX TwoX f) as Hf
    | pose proof (TwoHom_inv TwoX TwoY f) as Hf ];
    simpl in Hf; subst; simpl; split; auto.
Qed.

Theorem twoY_sieve_normal (S : @Sieve (_2^op) TwoY) :
  S ≈ twoY_sieve (sieve_mem S TwoIdY).
Proof.
  intros d f; destruct d;
    [ destruct (TwoHom_Y_X_absurd f)
    | pose proof (TwoHom_inv TwoY TwoY f) as Hf ];
    simpl in *; subst; simpl; split; auto.
Qed.

Definition jmap :
  @SieveObj (_2^op) TwoX ~{Sets}~> @SieveObj (_2^op) TwoY :=
  @fmap (_2^op^op) Sets (Sieve_Presheaf (_2^op)) TwoX TwoY TwoXY.

Theorem j_total : jmap twoX_total ≈ twoY_total.
Proof.
  intros d f; destruct d;
    [ destruct (TwoHom_Y_X_absurd f) | ]; simpl; split; auto.
Qed.
Theorem j_mid : jmap twoX_mid ≈ twoY_total.
Proof.
  intros d f; destruct d;
    [ destruct (TwoHom_Y_X_absurd f) | ]; simpl; split; auto.
Qed.
Theorem j_empty : jmap twoX_empty ≈ twoY_empty.
Proof.
  intros d f; destruct d;
    [ destruct (TwoHom_Y_X_absurd f) | ]; simpl; split; auto.
Qed.

Theorem j_identifies : jmap twoX_total ≈ jmap twoX_mid.
Proof. transitivity twoY_total; [ apply j_total | symmetry; apply j_mid ]. Qed.

Theorem j_separates : jmap twoX_total ≈ jmap twoX_empty -> False.
Proof.
  intro H. apply twoY_total_neq_empty.
  transitivity (jmap twoX_total); [ symmetry; apply j_total | ].
  transitivity (jmap twoX_empty); [ exact H | apply j_empty ].
Qed.

Theorem twoX_sieve_ext (P Q : Prop) (H : P -> Q) (P' Q' : Prop) (H' : P' -> Q')
        (HP : P <-> P') (HQ : Q <-> Q') :
  twoX_sieve P Q H ≈ twoX_sieve P' Q' H'.
Proof. intros d f; destruct d; simpl; assumption. Qed.

Theorem twoY_sieve_ext (R R' : Prop) (HR : R <-> R') :
  twoY_sieve R ≈ twoY_sieve R'.
Proof. intros d f; destruct d; simpl; [ split; auto | assumption ]. Qed.

Theorem twoX_three_sieves (Em : IEM) (S : @Sieve (_2^op) TwoX) :
  (S ≈ twoX_total) + (S ≈ twoX_mid) + (S ≈ twoX_empty).
Proof.
  pose proof (twoX_sieve_normal S) as HN.
  destruct (Em (sieve_mem S TwoIdX)) as [Hp | Hp].
  - left; left. rewrite HN. apply twoX_sieve_ext.
    + split; [ exact (fun _ => I) | exact (fun _ => Hp) ].
    + split; [ exact (fun _ => I)
             | exact (fun _ => sieve_closed S TwoIdX TwoXY Hp) ].
  - destruct (Em (sieve_mem S TwoXY)) as [Hq | Hq].
    + left; right. rewrite HN. apply twoX_sieve_ext.
      * split; [ exact Hp | intro C0; destruct C0 ].
      * split; [ exact (fun _ => I) | exact (fun _ => Hq) ].
    + right. rewrite HN. apply twoX_sieve_ext.
      * split; [ exact Hp | intro C0; destruct C0 ].
      * split; [ exact Hq | intro C0; destruct C0 ].
Qed.

Theorem twoY_two_sieves (Em : IEM) (S : @Sieve (_2^op) TwoY) :
  (S ≈ twoY_total) + (S ≈ twoY_empty).
Proof.
  pose proof (twoY_sieve_normal S) as HN.
  destruct (Em (sieve_mem S TwoIdY)) as [Hp | Hp].
  - left. rewrite HN. apply twoY_sieve_ext.
    split; [ exact (fun _ => I) | exact (fun _ => Hp) ].
  - right. rewrite HN. apply twoY_sieve_ext.
    split; [ exact Hp | intro C0; destruct C0 ].
Qed.

Theorem total_is_twoX_total : @total_sieve (_2^op) TwoX ≈ twoX_total.
Proof. intros d f; destruct d; split; intro; exact I. Qed.

Theorem total_is_twoY_total : @total_sieve (_2^op) TwoY ≈ twoY_total.
Proof. intros d f; destruct d; split; intro; exact I. Qed.

(* --- Mac Lane's explicit j : {0,1,2} -> {0,2} --- *)

Definition macj : Fin.t 3 -> Fin.t 2 :=
  fun k => match k with
           | Fin.F1 => Fin.F1
           | Fin.FS k' => match k' with
                          | Fin.F1 => Fin.F1
                          | Fin.FS _ => Fin.FS Fin.F1
                          end
           end.

Example macj_0 : macj Fin.F1 = Fin.F1 := eq_refl.
Example macj_1 : macj (Fin.FS Fin.F1) = Fin.F1 := eq_refl.
Example macj_2 : macj (Fin.FS (Fin.FS Fin.F1)) = Fin.FS Fin.F1 := eq_refl.

Definition twoX_code (Em : IEM) (S : @Sieve (_2^op) TwoX) : Fin.t 3 :=
  match Em (sieve_mem S TwoIdX) with
  | inl _ => Fin.F1
  | inr _ => match Em (sieve_mem S TwoXY) with
             | inl _ => Fin.FS Fin.F1
             | inr _ => Fin.FS (Fin.FS Fin.F1)
             end
  end.

Definition twoY_code (Em : IEM) (S : @Sieve (_2^op) TwoY) : Fin.t 2 :=
  match Em (sieve_mem S TwoIdY) with
  | inl _ => Fin.F1
  | inr _ => Fin.FS Fin.F1
  end.

Lemma twoX_code_total (Em : IEM) : twoX_code Em twoX_total = Fin.F1.
Proof.
  unfold twoX_code; destruct (Em (sieve_mem twoX_total TwoIdX)) as [|N];
    [ reflexivity | destruct (N I) ].
Qed.

Lemma twoX_code_mid (Em : IEM) : twoX_code Em twoX_mid = Fin.FS Fin.F1.
Proof.
  unfold twoX_code; destruct (Em (sieve_mem twoX_mid TwoIdX)) as [Hp|N];
    [ destruct Hp | ].
  destruct (Em (sieve_mem twoX_mid TwoXY)) as [|N2];
    [ reflexivity | destruct (N2 I) ].
Qed.

Lemma twoX_code_empty (Em : IEM) :
  twoX_code Em twoX_empty = Fin.FS (Fin.FS Fin.F1).
Proof.
  unfold twoX_code; destruct (Em (sieve_mem twoX_empty TwoIdX)) as [Hp|N];
    [ destruct Hp | ].
  destruct (Em (sieve_mem twoX_empty TwoXY)) as [Hq|];
    [ destruct Hq | reflexivity ].
Qed.

Lemma twoY_code_total (Em : IEM) : twoY_code Em twoY_total = Fin.F1.
Proof.
  unfold twoY_code; destruct (Em (sieve_mem twoY_total TwoIdY)) as [|N];
    [ reflexivity | destruct (N I) ].
Qed.

Lemma twoY_code_empty (Em : IEM) : twoY_code Em twoY_empty = Fin.FS Fin.F1.
Proof.
  unfold twoY_code; destruct (Em (sieve_mem twoY_empty TwoIdY)) as [Hp|];
    [ destruct Hp | reflexivity ].
Qed.

Example two_op_XY_IdY : (TwoXY ∘[_2^op] TwoIdY) = TwoXY := eq_refl.

Lemma jmap_mem_IdY (S : @Sieve (_2^op) TwoX) :
  sieve_mem (jmap S) TwoIdY <-> sieve_mem S TwoXY.
Proof. unfold jmap; simpl; split; intro H; exact H. Qed.

(*
   本节说明层/筛相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition macO (o : TwoObj) : nat := match o with TwoX => 3 | TwoY => 2 end.

Definition macF (x y : TwoObj) (f : TwoHom x y) :
  Fin.t (macO x) -> Fin.t (macO y) :=
  match f with
  | TwoIdX => fun k => k
  | TwoIdY => fun k => k
  | TwoXY  => macj
  end.

Lemma macF_respects (a b : TwoObj) :
  Proper (@equiv _ (@homset _2 a b)
            ==> @equiv _ (@homset FinSet (macO a) (macO b))) (macF a b).
Proof.
  intros f g Hfg; simpl in Hfg.
  assert (Heq : f = g) by exact Hfg.
  rewrite Heq; intro k; reflexivity.
Qed.

Lemma macF_id (a : TwoObj) : macF a a (@id _2 a) ≈ @id FinSet (macO a).
Proof. destruct a; intro k; reflexivity. Qed.

Lemma macF_comp (a b c : TwoObj) (f : b ~{_2}~> c) (g : a ~{_2}~> b) :
  macF a c (f ∘[_2] g) ≈ macF b c f ∘[FinSet] macF a b g.
Proof.
  destruct a, b, c;
    try solve [ destruct (TwoHom_Y_X_absurd g) ];
    try solve [ destruct (TwoHom_Y_X_absurd f) ];
    pose proof (TwoHom_inv _ _ f) as Hf;
    pose proof (TwoHom_inv _ _ g) as Hg;
    simpl in Hf, Hg; subst; intro k; reflexivity.
Qed.

Definition MacOmega : _2 ⟶ FinSet :=
  @Build_Functor _2 FinSet macO macF macF_respects macF_id macF_comp.

Example macOmega_X : fobj[MacOmega] TwoX = 3%nat := eq_refl.
Example macOmega_Y : fobj[MacOmega] TwoY = 2%nat := eq_refl.
Example macOmega_fmap : fmap[MacOmega] TwoXY = macj := eq_refl.

(*
   本节说明层/筛相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem mac_dictionary (Em : IEM) (S : @Sieve (_2^op) TwoX) :
  twoY_code Em (jmap S) = macj (twoX_code Em S).
Proof.
  unfold twoY_code, twoX_code.
  destruct (Em (sieve_mem (jmap S) TwoIdY)) as [Hj | Nj];
  destruct (Em (sieve_mem S TwoIdX)) as [Hx | Nx].
  - reflexivity.
  - destruct (Em (sieve_mem S TwoXY)) as [Hy | Ny]; [ reflexivity | ].
    destruct (Ny (proj1 (jmap_mem_IdY S) Hj)).
  - destruct (Nj (proj2 (jmap_mem_IdY S)
                   (sieve_closed S TwoIdX TwoXY Hx))).
  - destruct (Em (sieve_mem S TwoXY)) as [Hy | Ny].
    + destruct (Nj (proj2 (jmap_mem_IdY S) Hy)).
    + reflexivity.
Qed.

(* ---------------- (H) the two round trips ---------------- *)

Definition fun_truth_subobject {C : Category} (UT : Untruncate) :
  @SubObj ([C^op, Sets])
    (@Ω ([C^op, Sets]) (Functor_Category_Terminal Sets_Terminal)
       (Fun_Classifier UT)) :=
  @truth_subobject ([C^op, Sets]) (Functor_Category_Terminal Sets_Terminal)
    (Fun_Classifier UT).

Definition fun_char_roundtrip {C : Category} (UT : Untruncate)
  {x : C^op ⟶ Sets}
  (h : x ~{[C^op, Sets]}~> @Ω ([C^op, Sets])
                              (Functor_Category_Terminal Sets_Terminal)
                              (Fun_Classifier UT)) :
  @char ([C^op, Sets]) (Functor_Category_Terminal Sets_Terminal)
    (Fun_Classifier UT) _ _
    (sub_mono (@sub_reindex ([C^op, Sets])
                 (Fun_HasPullbacks Sets_HasPullbacks) _ x h
                 (fun_truth_subobject UT)))
    (sub_is_monic (@sub_reindex ([C^op, Sets])
                 (Fun_HasPullbacks Sets_HasPullbacks) _ x h
                 (fun_truth_subobject UT)))
    ≈ h
  := @classifier_char_roundtrip ([C^op, Sets])
       (Functor_Category_Terminal Sets_Terminal)
       (Fun_HasPullbacks Sets_HasPullbacks) (Fun_Classifier UT) x h.

Definition fun_pullback_roundtrip {C : Category} (UT : Untruncate)
  {x : C^op ⟶ Sets} (s : @SubObj ([C^op, Sets]) x) :
  @sub_reindex ([C^op, Sets]) (Fun_HasPullbacks Sets_HasPullbacks) _ x
    (@char ([C^op, Sets]) (Functor_Category_Terminal Sets_Terminal)
       (Fun_Classifier UT) _ _ (sub_mono s) (sub_is_monic s))
    (fun_truth_subobject UT)
    ≈ s
  := @classifier_pullback_roundtrip ([C^op, Sets])
       (Functor_Category_Terminal Sets_Terminal)
       (Fun_HasPullbacks Sets_HasPullbacks) (Fun_Classifier UT) x s.

(* ------------------------------------------------------------------ *)
(** ** (I) The classification theorem, at objects <= homs *)

Section Small.
Universes co o so OO HH.
Constraint Set < o.
Constraint o < so.
Constraint so <= OO.
Constraint OO <= HH.
Context (Cs : Category@{co o o}).
Context (UTs : Untruncate@{o}).
Definition PShSmall : Category@{OO HH HH} := [Cs^op, Sets@{o so}].
Definition PShSmall_Terminal : @Terminal PShSmall :=
  @Functor_Category_Terminal (Cs^op) Sets@{o so} Sets_Terminal.

Definition small_pb (U E : obj[PShSmall]) (theta : U ~{PShSmall}~> E)
  (M : @Monic PShSmall U E theta) :
  @IsPullback PShSmall E (@terminal_obj PShSmall PShSmall_Terminal)
    (Sieve_Presheaf Cs) (char_nat theta) (sieve_truth Cs) U theta
    (@one PShSmall PShSmall_Terminal U).
Proof using Cs UTs.
  constructor.
  - exact (char_square theta).
  - intros Q q1 q2 Hcomm.
    assert (Hq : ∀ (c : Cs) (z : carrier (fobj[Q] c)),
               sieve_mem (char_sieve theta c (transform[q1] c z)) (@id Cs c)).
    { intros c z. exact (proj2 (Hcomm c z c (@id Cs c)) I). }
    unshelve refine {| unique_obj := char_med UTs theta M q1 Hq |}.
    + split.
      * intros c z; simpl. exact (med_spec UTs theta M q1 Hq c z).
      * intros c z; simpl. destruct (transform[q2] c z); reflexivity.
    + intros v [Hv1 Hv2] c z; simpl.
      apply (theta_inj theta M c).
      transitivity (transform[q1] c z);
        [ exact (med_spec UTs theta M q1 Hq c z) | ].
      symmetry; exact (Hv1 c z).
Defined.

Section SmallUnique.
Context (U E : obj[PShSmall]) (theta : U ~{PShSmall}~> E).
Context (h : E ~{PShSmall}~> Sieve_Presheaf Cs).
Context (HP : @IsPullback PShSmall E (@terminal_obj PShSmall PShSmall_Terminal)
                (Sieve_Presheaf Cs) h (sieve_truth Cs) U theta
                (@one PShSmall PShSmall_Terminal U)).

Lemma small_char_sub_h (c : Cs) (e : carrier (fobj[E] c)) (d : Cs)
  (f : d ~{Cs}~> c) :
  sieve_mem (char_sieve theta c e) f -> sieve_mem (transform[h] c e) f.
Proof using All.
  intro Hf. apply Hf. intros [x Hx].
  pose proof (is_pullback_commutes HP d x) as Hc; simpl in Hc.
  assert (Hid : sieve_mem (transform[h] d (fmap[E] f e)) (@id Cs d)).
  { assert (Heq : transform[h] d (transform[theta] d x)
                    ≈ transform[h] d (fmap[E] f e))
      by (apply proper_morphism; exact Hx).
    apply (proj1 (Heq d (@id Cs d))).
    exact (proj2 (Hc d (@id Cs d)) I). }
  pose proof (@naturality _ _ _ _ h c d f e) as Hn; simpl in Hn.
  pose proof (proj2 (Hn d (@id Cs d)) Hid) as Hm2; simpl in Hm2.
  eapply sieve_respects; [ | exact Hm2 ]. apply id_right.
Qed.

Lemma small_h_sub_char (c : Cs) (e : carrier (fobj[E] c)) (d : Cs)
  (f : d ~{Cs}~> c) :
  sieve_mem (transform[h] c e) f -> sieve_mem (char_sieve theta c e) f.
Proof using All.
  intro Hf.
  set (ed := fmap[E] f e).
  set (S := transform[h] d ed).
  assert (HidS : sieve_mem S (@id Cs d)).
  { unfold S, ed.
    pose proof (@naturality _ _ _ _ h c d f e) as Hn; simpl in Hn.
    apply (proj1 (Hn d (@id Cs d))). simpl.
    eapply sieve_respects; [ | exact Hf ]. symmetry. apply id_right. }
  set (q1 := @sieve_cone Cs E d ed S).
  assert (Hcone : ∀ (k : Cs) (u : carrier (sieve_sub_obj d S k)),
            sieve_equiv (transform[h] k (transform[q1] k u)) (total_sieve k)).
  { intros k u j g. split; intro; [ exact I | ].
    unfold q1, sieve_cone; simpl.
    pose proof (@naturality _ _ _ _ h d k (projT1 u) ed) as Hn; simpl in Hn.
    apply (proj1 (Hn j g)). simpl.
    exact (sieve_closed S (projT1 u) g (projT2 u)). }
  assert (Hsq : h ∘[PShSmall] q1
                  ≈ sieve_truth Cs ∘[PShSmall]
                      @one PShSmall PShSmall_Terminal (sieve_subpresheaf d S))
    by (intros k u j g; exact (Hcone k u j g)).
  pose proof (is_pullback_ump HP (sieve_subpresheaf d S) q1
                (@one PShSmall PShSmall_Terminal _) Hsq) as UM.
  destruct (unique_property UM) as [Hu1 Hu2].
  intros P kk. apply kk.
  exists (transform[unique_obj UM] d (existT _ (@id Cs d) HidS)).
  pose proof (Hu1 d (existT _ (@id Cs d) HidS)) as Hval; simpl in Hval.
  rewrite Hval. exact (@fmap_id _ _ E d ed).
Qed.

Theorem small_unique : h ≈ char_nat theta.
Proof using All.
  intros c e d f; split; [ apply small_h_sub_char | apply small_char_sub_h ].
Qed.

End SmallUnique.

Definition Fun_Classifier_small :
  @SubobjectClassifier PShSmall PShSmall_Terminal :=
  @Build_SubobjectClassifier PShSmall PShSmall_Terminal
    (Sieve_Presheaf Cs)
    (sieve_truth Cs)
    (fun U E theta M => char_nat theta)
    (fun U E theta M => small_pb U E theta M)
    (fun U E theta M h HP => small_unique U E theta h HP).

Example fun_classifier_small_omega :
  @Ω PShSmall PShSmall_Terminal Fun_Classifier_small = Sieve_Presheaf Cs
  := eq_refl.
Example fun_classifier_small_truth :
  @truth PShSmall PShSmall_Terminal Fun_Classifier_small = sieve_truth Cs
  := eq_refl.

(*
   本节说明拉回/推出、同构、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition fun_classifier_classifies (x : obj[PShSmall]) :
  @Isomorphism Sets
    {| carrier := @SubObj PShSmall x |}
    {| carrier := x ~{PShSmall}~> @Ω PShSmall PShSmall_Terminal
                                    Fun_Classifier_small |} :=
  @classifier_classifies PShSmall PShSmall_Terminal
    (Fun_HasPullbacks Sets_HasPullbacks) Fun_Classifier_small x.

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition fun_sub_classifier_natural :
  @Isomorphism ([(PShSmall^op), Sets])
    (@Sub PShSmall (Fun_HasPullbacks Sets_HasPullbacks))
    (@Curried_CoHom PShSmall
       (@Ω PShSmall PShSmall_Terminal Fun_Classifier_small)) :=
  @Sub_classifier_natural PShSmall PShSmall_Terminal
    (Fun_HasPullbacks Sets_HasPullbacks) Fun_Classifier_small.

Definition fun_Sub_Representable :
  Representable (@Sub PShSmall (Fun_HasPullbacks Sets_HasPullbacks)) :=
  @Sub_Representable PShSmall PShSmall_Terminal
    (Fun_HasPullbacks Sets_HasPullbacks) Fun_Classifier_small.

End Small.
