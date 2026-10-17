(*
 nLab: https://ncatlab.org/nlab/show/abelianization
 nLab: https://ncatlab.org/nlab/show/reflective+subcategory

   本文件给出反射子范畴相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Monad.Comparison.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Idempotent.
Require Import Category.Construction.Reflective.Monadic.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Epi.
Require Import Category.Instance.Grp.Center.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Abelianization.
Require Import Category.Instance.Grp.Abelianize.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** ** The full subcategory of abelian groups *)

Definition IsAbelian@{a c p +} (G : GrpObject@{a c p}) : Type@{a} :=
  ∀ a b : carrier G, grp_mul G a b ≈ grp_mul G b a.

Definition AbGrp_Sub@{u p +} : Subcategory Grp@{u p} :=
  @Build_Subcategory Grp@{u p} IsAbelian
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition AbGrp@{u p +} : Category := Sub Grp@{u p} AbGrp_Sub.

Definition AbGrp_Full@{u p +} :
  Category.Construction.Subcategory.Full Grp@{u p} AbGrp_Sub :=
  fun _ _ _ _ _ => I.

(** ** Descent into an abelian group *)

(*
   本节说明 Reflective 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma abel_kills_grp@{u p +} {G H : GrpObject@{p p p}} (HH : IsAbelian H)
  (f : G ~{Grp@{u p}}~> H) (a b : carrier G) :
  abel_eq G a b → grp_map f a ≈ grp_map f b.
Proof.
  intro Hab.
  apply (@pequiv_to _ _ (grp_prop H)).
  destruct Hab as [Hab].
  apply pequiv_from.
  pose proof (hom_to_abelian_kills HH f _ Hab) as E.
  rewrite (grp_map_mul f), (grp_map_inv f) in E.
  apply (grp_cancel_r _ (grp_inv H (grp_map f b))).
  rewrite E.
  symmetry; apply grp_mul_inv_r.
Qed.

(* G/[G,G], as an object of the subcategory. *)
Definition AbelianizationGrp@{u p +} (G : Grp@{u p}) : AbGrp :=
  (Ab_to_GrpOb (AbelianizationOb G); ab_is_abelian (AbelianizationOb G)).

(* The mediator: the SAME underlying map as [f], read out of the
   quotient. *)
Program Definition abel_med_grp@{u p +} {G H : Grp@{u p}} (HH : IsAbelian H)
  (f : G ~{Grp@{u p}}~> H) :
  Ab_to_GrpOb (AbelianizationOb G) ~{Grp@{u p}}~> H := {|
  grp_map := {| morphism := fun a : carrier G => grp_map f a |}
|}.
Next Obligation.
  intros G H HH f a b Hab; exact (abel_kills_grp HH f a b Hab).
Qed.
Next Obligation. intros G H HH f; exact (grp_map_unit f). Qed.
Next Obligation. intros G H HH f a b; exact (grp_map_mul f a b). Qed.

(** ** Mac Lane's universal arrow: the quotient projection *)

Theorem abgrp_universal@{u p +} (G : Grp@{u p}) :
  ∀ (d : AbGrp) (f : G ~{Grp@{u p}}~> Incl Grp@{u p} AbGrp_Sub d),
    ∃! g : AbelianizationGrp G ~{AbGrp}~> d,
      f ≈ fmap[Incl Grp@{u p} AbGrp_Sub] g ∘ abel_proj G.
Proof.
  intros d f.
  unshelve eexists.
  - exact (abel_med_grp `2 d f; I).
  - intro a; simpl; reflexivity.
  - intros g Hg a; simpl.
    exact (Hg a).
Defined.

Definition abgrp_universal_arrow@{u p +} (G : Grp@{u p})
  : @UniversalArrow Grp@{u p} AbGrp G (Incl Grp@{u p} AbGrp_Sub) :=
  @universal_arrow_from_UMP Grp@{u p} AbGrp G (Incl Grp@{u p} AbGrp_Sub)
    (AbelianizationGrp G) (abel_proj G) (abgrp_universal G).

Definition AbGrp_reflector@{u p +} : Grp@{u p} ⟶ AbGrp :=
  LeftAdjointFunctorFromUniversalArrows (Incl Grp@{u p} AbGrp_Sub)
    abgrp_universal_arrow.

(* The adjunction reading Seven Sketches Example 3.74 asks to see. *)
Definition AbGrp_adj@{u p +} : AbGrp_reflector ⊣ Incl Grp@{u p} AbGrp_Sub :=
  AdjunctionFromUniversalArrows (Incl Grp@{u p} AbGrp_Sub)
    abgrp_universal_arrow.

(* The issue's pinned name. *)
Definition Ab_Reflective_in_Grp@{u p +} : @Reflective Grp@{u p} AbGrp_Sub :=
  @Build_Reflective Grp@{u p} AbGrp_Sub AbGrp_Full AbGrp_reflector AbGrp_adj.

(** ** Readbacks: the unit is the map Mac Lane names *)

Example abgrp_reflector_obj@{u p +} (G : Grp@{u p}) :
  `1 (fobj[AbGrp_reflector] G) = Ab_to_GrpOb (AbelianizationOb G)
  := eq_refl.

Example abgrp_arrow_is_proj@{u p +} (G : Grp@{u p}) :
  @arrow Grp@{u p} AbGrp G (Incl Grp@{u p} AbGrp_Sub)
    (abgrp_universal_arrow G)
    = abel_proj G := eq_refl.

Example abgrp_record_reflector@{u p +} (G : Grp@{u p}) :
  fobj[reflector Ab_Reflective_in_Grp] G = AbelianizationGrp G := eq_refl.

Definition abgrp_unit@{u p +} (G : Grp@{u p})
  : G ~{Grp@{u p}}~> Incl Grp@{u p} AbGrp_Sub (fobj[AbGrp_reflector] G) :=
  @Category.Theory.Adjunction.unit _ _ _ _ AbGrp_adj G.

Example abgrp_unit_pointwise@{u p +} (G : Grp@{u p}) (a : carrier G) :
  grp_map (abgrp_unit G) a = grp_map (abel_proj G) a := eq_refl.

Lemma abgrp_unit_is_proj@{u p +} (G : Grp@{u p}) :
  abgrp_unit G ≈ abel_proj G.
Proof. intro a; reflexivity. Defined.

(* Mac Lane p. 91: for a full reflective subcategory each object is
   isomorphic to its reflection.  At an abelian G, G/[G,G] ≅ G. *)
Definition abgrp_reflect_iso@{u p +} (G : Sub Grp@{u p} AbGrp_Sub) :
  fobj[AbGrp_reflector] (fobj[Incl Grp@{u p} AbGrp_Sub] G) ≅[AbGrp] G :=
  reflective_counit_iso Ab_Reflective_in_Grp G.

(** ** The adjunction of Abelianize.v, factored through the subcategory *)

(*
   本节说明 Reflective 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Grp_to_AbOb@{a c p +} (G : GrpObject@{a c p})
  (HG : IsAbelian G) : AbObject@{a c p} := {|
  ab_cmon := {| cmon_setoid := grp_setoid G
              ; cmon_zero   := grp_unit G
              ; cmon_plus   := grp_mul G
              ; cmon_prop   := grp_prop G |}
 ; ab_neg := grp_inv G
|}.
Solve All Obligations with
  (intros G HG;
   first [ exact (grp_mul_respects G)
         | exact (grp_mul_assoc G)
         | exact HG
         | exact (grp_mul_unit_l G)
         | exact (grp_inv_Proper G)
         | exact (grp_mul_inv_l G) ]).

(* [Ab] (Instance/Ab.v) into the subcategory. *)
Program Definition Ab_to_AbGrp@{u p +} : Ab@{u p} ⟶ AbGrp := {|
  fobj := fun A => (Ab_to_GrpOb A; ab_is_abelian A);
  fmap := fun A B f => (fmap[Ab_to_Grp] f; I)
|}.
Next Obligation. intros A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros A a; simpl; reflexivity. Qed.
Next Obligation. intros A B C f g a; simpl; reflexivity. Qed.

Definition Ab_to_AbGrp_Faithful@{u p +} :
  @Faithful Ab@{u p} AbGrp Ab_to_AbGrp.
Proof. constructor; intros A B f g H; exact H. Defined.

Program Definition Ab_to_AbGrp_Full@{u p +} :
  @Functor.Full Ab@{u p} AbGrp Ab_to_AbGrp := {|
  prefmap := fun A B (h : Ab_to_AbGrp A ~{AbGrp}~> Ab_to_AbGrp B) =>
    {| cmon_map      := grp_map `1 h
     ; cmon_map_zero := grp_map_unit `1 h
     ; cmon_map_plus := grp_map_mul `1 h |}
|}.
Next Obligation. intros A B h a; simpl; reflexivity. Qed.

(* Every object of the subcategory is, up to the identity function, the
   image of the [AbObject] read off it. *)
Program Definition AbGrp_iso@{u p +} (d : Sub Grp@{u p} AbGrp_Sub) :
  Ab_to_AbGrp (Grp_to_AbOb `1 d `2 d) ≅[AbGrp] d := {|
  to   := ({| grp_map := {| morphism := fun a : carrier `1 d => a |} |}; I);
  from := ({| grp_map := {| morphism := fun a : carrier `1 d => a |} |}; I)
|}.
Next Obligation. intros d a b H; exact H. Qed.
Next Obligation. intros d; simpl; reflexivity. Qed.
Next Obligation. intros d a b; simpl; reflexivity. Qed.
Next Obligation. intros d a b H; exact H. Qed.
Next Obligation. intros d; simpl; reflexivity. Qed.
Next Obligation. intros d a b; simpl; reflexivity. Qed.
Next Obligation. intros d a; simpl; reflexivity. Qed.
Next Obligation. intros d a; simpl; reflexivity. Qed.

Definition Ab_to_AbGrp_ESO@{u p +} :
  @EssentiallySurjective Ab@{u p} AbGrp Ab_to_AbGrp :=
  @Build_EssentiallySurjective Ab@{u p} AbGrp Ab_to_AbGrp
    (fun d : AbGrp => Grp_to_AbOb `1 d `2 d) AbGrp_iso.

Definition Ab_AbGrp_Equivalence@{u p +} :
  @EquivalenceOfCategories Ab@{u p} AbGrp Ab_to_AbGrp :=
  @FF_ESO_Equivalence Ab@{u p} _ Ab_to_AbGrp
    Ab_to_AbGrp_Full Ab_to_AbGrp_Faithful
    Ab_to_AbGrp_ESO.

(* Abelianize.v's inclusion [Ab_to_Grp] factors as [Ab_to_AbGrp]
   followed by the inclusion of the subcategory. *)
Example ab_to_grp_factors_obj@{u p +} (A : Ab@{u p}) :
  Incl Grp AbGrp_Sub (Ab_to_AbGrp A) = Ab_to_Grp A := eq_refl.

Example ab_to_grp_factors_fmap@{u p +} (A B : Ab@{u p})
  (f : A ~{Ab@{u p}}~> B) :
  fmap[Incl Grp AbGrp_Sub] (fmap[Ab_to_AbGrp] f) = fmap[Ab_to_Grp] f
  := eq_refl.

(* As functors the two agree up to [≈], with identity components. *)
Lemma ab_to_grp_factors@{u p +} :
  Incl Grp@{u p} AbGrp_Sub ◯ Ab_to_AbGrp ≈ Ab_to_Grp.
Proof.
  exists (fun A => @iso_id Grp@{u p} (Ab_to_GrpOb A)).
  intros A B f a; simpl; reflexivity.
Defined.

(* And the reflector factors as Abelianize.v's left adjoint followed by
   [Ab_to_AbGrp]: on objects on the nose, on arrows up to [≈] by the
   uniqueness clause of the universal property. *)
Example abgrp_reflector_factors_obj@{u p +} (G : Grp@{u p}) :
  fobj[AbGrp_reflector] G = fobj[Ab_to_AbGrp] (fobj[Abelianization_Functor] G)
  := eq_refl.

Lemma abgrp_reflector_factors_fmap@{u p +} (G H : Grp@{u p})
  (f : G ~{Grp@{u p}}~> H) :
  fmap[AbGrp_reflector] f
    ≈ fmap[Ab_to_AbGrp] (fmap[Abelianization_Functor] f).
Proof.
  apply (uniqueness (ump_universal_arrows (abgrp_universal_arrow G) _)).
  intro a; simpl; apply abel_eq_refl.
Qed.

Lemma abgrp_reflector_factors@{u p +} :
  @equiv _ (@Functor_Setoid Grp@{u p} AbGrp) AbGrp_reflector
    (Ab_to_AbGrp ◯ Abelianization_Functor).
Proof.
  exists (fun G => @iso_id AbGrp (AbelianizationGrp G)).
  intros G H f a; simpl.
  exact (abgrp_reflector_factors_fmap G H f a).
Defined.

(** ** Riehl 5.3.ii at this reflection *)

Definition AbGrp_IdempotentMonad@{u p +} :
  @IdempotentMonad Grp@{u p} (Incl Grp@{u p} AbGrp_Sub ◯ AbGrp_reflector)
    (Reflective_Monad Ab_Reflective_in_Grp) :=
  Reflective_IdempotentMonad Ab_Reflective_in_Grp.

Definition AbGrp_Incl_Monadic@{u p +} : Monadic (Incl Grp@{u p} AbGrp_Sub) :=
  Reflective_Monadic Ab_Reflective_in_Grp.

(** ** Non-vacuity at S₃ *)

(* S₃ is not an object of the subcategory. *)
Lemma S3_not_IsAbelian@{a +} : IsAbelian (S3 : GrpObject@{a Set Set}) → False.
Proof.
  intro HS3.
  pose proof (HS3 S3_r S3_s) as E.
  vm_compute in E; discriminate E.
Qed.

(* The unit at S₃ merges the commutator of the two generators with the
   identity... *)
Lemma abgrp_unit_S3_merges@{u +} :
  grp_map (abgrp_unit (S3 : Grp@{u Set})) (gcomm S3 S3_r S3_s)
    ≈ grp_map (abgrp_unit (S3 : Grp@{u Set})) s3_unit.
Proof. exact abelianize_S3_identifies. Qed.

(* ...which were apart in S₃, so the unit at S₃ is not invertible. *)
Theorem abgrp_unit_S3_not_iso@{u +} :
  IsIsomorphism (abgrp_unit (S3 : Grp@{u Set})) → False.
Proof.
  intros [g _ Hgf].
  apply (snd commutator_S3_nontrivial).
  refine (transitivity (symmetry (Hgf (gcomm S3 S3_r S3_s))) _).
  refine (transitivity _ (Hgf s3_unit)).
  exact (proper_morphism (grp_map g) _ _ abgrp_unit_S3_merges).
Qed.

(* The reflection of S₃ is not the trivial group: exercising the
   universal property of the NEW universal arrow on the sign character,
   the mediator separates the reflection from the identity. *)
Definition AbTwo_in_AbGrp@{u p +} : Sub Grp@{u p} AbGrp_Sub :=
  (Ab_to_GrpOb AbTwo; ab_is_abelian AbTwo).

Example abgrp_S3_med_s@{u +} :
  grp_map
    `1 (unique_obj
          (abgrp_universal (S3 : Grp@{u Set}) AbTwo_in_AbGrp ab_two_sign))
    S3_s = grp_two_one := eq_refl.

Example abgrp_S3_med_unit@{u +} :
  grp_map
    `1 (unique_obj
          (abgrp_universal (S3 : Grp@{u Set}) AbTwo_in_AbGrp ab_two_sign))
    s3_unit = grp_two_zero := eq_refl.

Theorem abgrp_S3_separates@{u +} :
  grp_map
    `1 (unique_obj
          (abgrp_universal (S3 : Grp@{u Set}) AbTwo_in_AbGrp ab_two_sign))
    S3_s
    ≈ grp_map
        `1 (unique_obj
              (abgrp_universal (S3 : Grp@{u Set}) AbTwo_in_AbGrp ab_two_sign))
        s3_unit → False.
Proof. intro H; vm_compute in H; exact H. Qed.

(* The same fact on the reflection's own setoid: the class of s and the
   class of the identity stay apart in G/[G, G] at S₃, because the
   mediator above respects that setoid's equality. *)
Lemma S3_reflection_nontrivial@{u +} :
  @equiv (carrier `1 (fobj[AbGrp_reflector] (S3 : Grp@{u Set}))) _
    S3_s s3_unit → False.
Proof.
  intro H.
  apply abgrp_S3_separates.
  exact (proper_morphism
    (grp_map `1 (unique_obj
       (abgrp_universal (S3 : Grp@{u Set}) AbTwo_in_AbGrp ab_two_sign))) _ _ H).
Qed.
