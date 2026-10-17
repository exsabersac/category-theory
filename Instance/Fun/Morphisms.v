Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Two.

Generalizable All Variables.

(** * Pointwise monos and epis in a functor category *)

(*
 nLab: https://ncatlab.org/nlab/show/functor+category
 nLab: https://ncatlab.org/nlab/show/monomorphism
 nLab: https://ncatlab.org/nlab/show/epimorphism
 nLab: https://ncatlab.org/nlab/show/kernel+pair
 nLab: https://ncatlab.org/nlab/show/category+of+presheaves

   本文件给出态射相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------ *)
(** ** (A) An arbitrary target: componentwise monic/epic suffices *)

Section General.

Context {C : Category}.
Context {D : Category}.
Context {F : C ⟶ D}.
Context {G : C ⟶ D}.
Context (θ : F ⟹ G).

Theorem pointwise_monic_is_monic :
  (∀ x : C, Monic (transform[θ] x)) → @Monic ([C, D]) F G θ.
Proof.
  intros H.
  constructor; intros K g1 g2 Heq x.
  apply (@monic _ _ _ _ (H x) (K x)).
  exact (Heq x).
Defined.

Theorem pointwise_epic_is_epic :
  (∀ x : C, Epic (transform[θ] x)) → @Epic ([C, D]) F G θ.
Proof.
  intros H.
  constructor; intros K g1 g2 Heq x.
  apply (@epic _ _ _ _ (H x) (K x)).
  exact (Heq x).
Defined.

End General.

(* ------------------------------------------------------------------ *)
(** ** (B) The target Sets: the biconditionals, by pointwise (co)limits *)

Section SetsConverse.

Context {C : Category}.
Context {F : C ⟶ Sets}.
Context {G : C ⟶ Sets}.
Context (θ : F ⟹ G).

(** ** The pointwise kernel-pair functor *)

Lemma theta_nat {x y : C} (f : x ~{C}~> y) (a : carrier (F x)) :
  transform[θ] y (fmap[F] f a) ≈ fmap[G] f (transform[θ] x a).
Proof. exact (naturality_sym θ x y f a). Qed.

Lemma ker_map_ok {x y : C} (f : x ~{C}~> y)
      (u : carrier (sets_ker (transform[θ] x))) :
  transform[θ] y (fmap[F] f (fst `1 u))
    ≈ transform[θ] y (fmap[F] f (snd `1 u)).
Proof.
  transitivity (fmap[G] f (transform[θ] x (fst `1 u))).
  - apply theta_nat.
  - transitivity (fmap[G] f (transform[θ] x (snd `1 u))).
    + apply proper_morphism; exact (`2 u).
    + symmetry; apply theta_nat.
Qed.

Definition ker_fun {x y : C} (f : x ~{C}~> y)
  (u : carrier (sets_ker (transform[θ] x))) :
  carrier (sets_ker (transform[θ] y)) :=
  ((fmap[F] f (fst `1 u), fmap[F] f (snd `1 u)); ker_map_ok f u).

Lemma ker_fun_proper {x y : C} (f : x ~{C}~> y) :
  Proper (equiv ==> equiv) (ker_fun f).
Proof.
  intros u v H; destruct H as [H1 H2].
  split; simpl; now apply proper_morphism.
Qed.

Definition ker_map {x y : C} (f : x ~{C}~> y) :
  sets_ker (transform[θ] x) ~{Sets}~> sets_ker (transform[θ] y) :=
  {| morphism := ker_fun f; proper_morphism := ker_fun_proper f |}.

Program Definition KerPair : C ⟶ Sets := {|
  fobj := fun x => sets_ker (transform[θ] x);
  fmap := fun x y f => ker_map f
|}.
Next Obligation.
  proper; split; simpl;
    exact (@fmap_respects _ _ F _ _ _ _ X _).
Qed.
Next Obligation. split; simpl; exact (@fmap_id _ _ F _ _). Qed.
Next Obligation. split; simpl; exact (@fmap_comp _ _ F _ _ _ _ _ _). Qed.

Program Definition KerFst : KerPair ⟹ F := {|
  transform := fun x => sets_ker_fst (transform[θ] x)
|}.

Program Definition KerSnd : KerPair ⟹ F := {|
  transform := fun x => sets_ker_snd (transform[θ] x)
|}.

Lemma ker_agree : θ ∙ KerFst ≈[Fun] θ ∙ KerSnd.
Proof. intros x u; exact (`2 u). Qed.

Theorem sets_functor_monic_pointwise :
  @Monic ([C, Sets]) F G θ → ∀ x : C, Monic (transform[θ] x).
Proof.
  intros Hm x.
  apply (fst (injectivity_is_monic (transform[θ] x))).
  intros a b Hab.
  exact (@monic _ _ _ _ Hm KerPair KerFst KerSnd ker_agree x
                (sets_ker_pair (transform[θ] x) a b Hab)).
Defined.

Theorem sets_functor_monic_iff_pointwise :
  @Monic ([C, Sets]) F G θ  ↔  (∀ x : C, Monic (transform[θ] x)).
Proof.
  split.
  - exact sets_functor_monic_pointwise.
  - exact (pointwise_monic_is_monic θ).
Defined.

(** ** The pointwise cokernel-pair functor *)

Lemma ck_Im_map {x y : C} (f : x ~{C}~> y) (b : carrier (G x)) :
  Im (transform[θ] x) b → Im (transform[θ] y) (fmap[G] f b).
Proof.
  intros [z Hz]; exists (fmap[F] f z).
  transitivity (fmap[G] f (transform[θ] x z)).
  - apply theta_nat.
  - now apply proper_morphism.
Defined.

Definition ck_fun {x y : C} (f : x ~{C}~> y)
  (u : carrier (CKSetoid (transform[θ] x))) :
  carrier (CKSetoid (transform[θ] y)) :=
  match u with
  | Datatypes.inl b => Datatypes.inl (fmap[G] f b)
  | Datatypes.inr b => Datatypes.inr (fmap[G] f b)
  end.

Lemma ck_fun_proper {x y : C} (f : x ~{C}~> y) :
  Proper (equiv ==> equiv) (ck_fun f).
Proof.
  intros u v H; destruct u, v; simpl in *;
    try (now apply proper_morphism);
    destruct H as [H1 H2]; split;
    [ now apply proper_morphism | now apply ck_Im_map
    | now apply proper_morphism | now apply ck_Im_map ].
Qed.

Definition ck_map {x y : C} (f : x ~{C}~> y) :
  CKSetoid (transform[θ] x) ~{Sets}~> CKSetoid (transform[θ] y) :=
  {| morphism := ck_fun f; proper_morphism := ck_fun_proper f |}.

Program Definition CokerPair : C ⟶ Sets := {|
  fobj := fun x => CKSetoid (transform[θ] x);
  fmap := fun x y f => ck_map f
|}.
Next Obligation.
  proper; destruct x1; simpl;
    exact (@fmap_respects _ _ G _ _ _ _ X _).
Qed.
Next Obligation.
  destruct x0; simpl; exact (@fmap_id _ _ G _ _).
Qed.
Next Obligation.
  destruct x0; simpl; exact (@fmap_comp _ _ G _ _ _ _ _ _).
Qed.

Program Definition CkLeft : G ⟹ CokerPair := {|
  transform := fun x => ck_left (transform[θ] x)
|}.

Program Definition CkRight : G ⟹ CokerPair := {|
  transform := fun x => ck_right (transform[θ] x)
|}.

Lemma ck_agree_nat : CkLeft ∙ θ ≈[Fun] CkRight ∙ θ.
Proof. intros x a; exact (ck_agree (transform[θ] x) a). Qed.

Theorem sets_functor_epic_pointwise :
  @Epic ([C, Sets]) F G θ → ∀ x : C, Epic (transform[θ] x).
Proof.
  intros He x.
  apply (fst (surjectivity_is_epic (transform[θ] x))).
  intros b.
  exact (snd (@epic _ _ _ _ He CokerPair CkLeft CkRight ck_agree_nat x b)).
Defined.

Theorem sets_functor_epic_iff_pointwise :
  @Epic ([C, Sets]) F G θ  ↔  (∀ x : C, Epic (transform[θ] x)).
Proof.
  split.
  - exact sets_functor_epic_pointwise.
  - exact (pointwise_epic_is_epic θ).
Defined.

End SetsConverse.

(* ------------------------------------------------------------------ *)
(** ** (C) Awodey §7.10 Ex 6: invertibility of a GIVEN transformation *)

Section Invertibility.

Context {C : Category}.
Context {D : Category}.
Context {F : C ⟶ D}.
Context {G : C ⟶ D}.
Context (θ : F ⟹ G).

Lemma nat_inv_natural (H : ∀ x : C, IsIsomorphism (transform[θ] x))
      {x y : C} (f : x ~{C}~> y) :
  fmap[F] f ∘ @two_sided_inverse _ _ _ _ (H x)
    ≈ @two_sided_inverse _ _ _ _ (H y) ∘ fmap[G] f.
Proof.
  rewrite <- (id_left (fmap[F] f ∘ _)).
  rewrite <- (@is_left_inverse _ _ _ _ (H y)).
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  rewrite comp_assoc.
  rewrite <- naturality.
  rewrite <- comp_assoc.
  rewrite (@is_right_inverse _ _ _ _ (H x)).
  now rewrite id_right.
Qed.

Program Definition nat_inverse
  (H : ∀ x : C, IsIsomorphism (transform[θ] x)) : G ⟹ F := {|
  transform := fun x => @two_sided_inverse _ _ _ _ (H x)
|}.
Next Obligation. now rewrite nat_inv_natural. Qed.
Next Obligation. now rewrite nat_inv_natural. Qed.

Definition componentwise_iso
  (H : ∀ x : C, IsIsomorphism (transform[θ] x)) :
  @IsIsomorphism ([C, D]) F G θ.
Proof.
  refine (@Build_IsIsomorphism ([C, D]) F G θ (nat_inverse H) _ _);
    intro x; simpl.
  - rewrite (@is_right_inverse _ _ _ _ (H x)).
    now rewrite fmap_id.
  - rewrite (@is_left_inverse _ _ _ _ (H x)).
    now rewrite fmap_id.
Defined.

Definition nat_iso_pointwise (H : @IsIsomorphism ([C, D]) F G θ) (x : C) :
  IsIsomorphism (transform[θ] x).
Proof.
  refine {| two_sided_inverse :=
              transform[@two_sided_inverse _ _ _ _ H] x |}.
  - etransitivity; [ exact (@is_right_inverse _ _ _ _ H x) | ].
    simpl; apply fmap_id.
  - etransitivity; [ exact (@is_left_inverse _ _ _ _ H x) | ].
    simpl; apply fmap_id.
Defined.

Theorem nat_iso_iff_pointwise :
  @IsIsomorphism ([C, D]) F G θ  ↔  (∀ x : C, IsIsomorphism (transform[θ] x)).
Proof.
  split.
  - exact nat_iso_pointwise.
  - exact componentwise_iso.
Defined.

End Invertibility.

(* ------------------------------------------------------------------ *)
(** ** (C, continued) Comparison with [Functor_Setoid_Nat_Iso] *)

Section EquivComparison.

Context {C : Category}.
Context {D : Category}.
Context {F : C ⟶ D}.
Context {G : C ⟶ D}.
Context (θ : F ⟹ G).

Definition nat_iso_family
  (H : ∀ x : C, IsIsomorphism (transform[θ] x)) : F ≈ G.
Proof.
  simpl.
  exists (fun x => @IsIsoToIso D (F x) (G x) (transform[θ] x) (H x)).
  intros x y f; simpl.
  symmetry.
  rewrite <- comp_assoc.
  rewrite naturality.
  rewrite comp_assoc.
  rewrite (@is_left_inverse _ _ _ _ (H y)).
  now rewrite id_left.
Defined.

Example equiv_iso_to_is_theta
  (H : ∀ x : C, IsIsomorphism (transform[θ] x)) (x : C) :
  transform[to (equiv_iso (nat_iso_family H))] x = transform[θ] x
  := eq_refl.

Example equiv_iso_from_is_nat_inverse
  (H : ∀ x : C, IsIsomorphism (transform[θ] x)) (x : C) :
  transform[from (equiv_iso (nat_iso_family H))] x
    = transform[nat_inverse θ H] x := eq_refl.

End EquivComparison.

(* ------------------------------------------------------------------ *)
(** ** (D) Presheaves: monos are the pointwise injections *)

Section Presheaf.

Context {C : Category}.
Context {P : C^op ⟶ Sets}.
Context {Q : C^op ⟶ Sets}.
Context (θ : P ⟹ Q).

Definition presheaf_monic_iff_pointwise :
  @Monic ([C^op, Sets]) P Q θ  ↔  (∀ x : C^op, Monic (transform[θ] x))
  := sets_functor_monic_iff_pointwise θ.

Definition presheaf_epic_iff_pointwise :
  @Epic ([C^op, Sets]) P Q θ  ↔  (∀ x : C^op, Epic (transform[θ] x))
  := sets_functor_epic_iff_pointwise θ.

Theorem presheaf_monic_iff_injective :
  @Monic ([C^op, Sets]) P Q θ  ↔
  (∀ (x : C^op) (a b : carrier (P x)),
      transform[θ] x a ≈ transform[θ] x b → a ≈ b).
Proof.
  split.
  - intros Hm x.
    exact (snd (injectivity_is_monic (transform[θ] x))
               (sets_functor_monic_pointwise θ Hm x)).
  - intros Hi.
    apply (pointwise_monic_is_monic θ); intros x.
    exact (fst (injectivity_is_monic (transform[θ] x)) (Hi x)).
Defined.

Theorem presheaf_epic_iff_surjective :
  @Epic ([C^op, Sets]) P Q θ  ↔
  (∀ (x : C^op) (b : carrier (Q x)), ∃ a, transform[θ] x a ≈ b)%type.
Proof.
  split.
  - intros He x.
    exact (epic_implies_surjective (transform[θ] x)
             (sets_functor_epic_pointwise θ He x)).
  - intros Hs.
    apply (pointwise_epic_is_epic θ); intros x.
    exact (surjective_implies_epic (transform[θ] x) (Hs x)).
Defined.

End Presheaf.

(* ------------------------------------------------------------------ *)
(** ** Non-vacuity *)

Section Witnesses.

Definition const_fun@{co ch cp dro dh dp}
  {C : Category@{co ch cp}} {D : Category@{dro dh dp}} (d : D) : C ⟶ D :=
  {| fobj          := fun _ => d
   ; fmap          := fun _ _ _ => id
   ; fmap_respects := fun _ _ _ _ _ => reflexivity _
   ; fmap_id       := fun _ => reflexivity _
   ; fmap_comp     := fun _ _ _ _ _ => symmetry (id_left id) |}.

Definition TwoOne : _2 ⟶ Sets :=
  @const_fun _2 Sets unit_setoid_object.
Definition TwoBool : _2 ⟶ Sets :=
  @const_fun _2 Sets bool_setoid_object.

Program Definition two_pick_nat : TwoOne ⟹ TwoBool := {|
  transform := fun _ => pick_true
|}.

Program Definition two_collapse : TwoBool ⟹ TwoOne := {|
  transform := fun _ => collapse
|}.

Lemma pick_true_Monic : @Monic Sets _ _ pick_true.
Proof.
  apply (fst (injectivity_is_monic pick_true)).
  intros a b _; destruct a, b; reflexivity.
Defined.

Lemma collapse_Epic : @Epic Sets _ _ collapse.
Proof.
  apply (fst (surjectivity_is_epic collapse)).
  intros b; exists true; destruct b; reflexivity.
Defined.

Definition two_pick_Monic : @Monic ([_2, Sets]) TwoOne TwoBool two_pick_nat :=
  pointwise_monic_is_monic two_pick_nat (fun _ => pick_true_Monic).

Definition two_collapse_Epic :
  @Epic ([_2, Sets]) TwoBool TwoOne two_collapse :=
  pointwise_epic_is_epic two_collapse (fun _ => collapse_Epic).

Lemma two_pick_component_not_surjective :
  (∀ b : carrier bool_setoid_object,
      ∃ a, transform[two_pick_nat] TwoX a ≈ b)%type → False.
Proof.
  intros Hs; destruct (Hs false) as [a Ha]; simpl in Ha; discriminate.
Qed.

Lemma two_pick_not_Epic :
  @Epic ([_2, Sets]) TwoOne TwoBool two_pick_nat → False.
Proof.
  intros He.
  apply two_pick_component_not_surjective.
  exact (epic_implies_surjective (transform[two_pick_nat] TwoX)
           (sets_functor_epic_pointwise two_pick_nat He TwoX)).
Qed.

Lemma two_collapse_not_Monic :
  @Monic ([_2, Sets]) TwoBool TwoOne two_collapse → False.
Proof.
  intros Hm.
  apply collapse_not_monic.
  exact (sets_functor_monic_pointwise two_collapse Hm TwoX).
Qed.

Definition TwoTwoX : _2 ⟶ _2 := @const_fun _2 _2 TwoX.
Definition TwoTwoY : _2 ⟶ _2 := @const_fun _2 _2 TwoY.

Program Definition two_arrow : TwoTwoX ⟹ TwoTwoY := {|
  transform := fun _ => TwoXY
|}.

Definition two_arrow_Monic :
  @Monic ([_2, _2]) TwoTwoX TwoTwoY two_arrow :=
  pointwise_monic_is_monic two_arrow (fun _ => TwoXY_monic).

Definition two_arrow_Epic :
  @Epic ([_2, _2]) TwoTwoX TwoTwoY two_arrow :=
  pointwise_epic_is_epic two_arrow (fun _ => TwoXY_epic).

End Witnesses.
