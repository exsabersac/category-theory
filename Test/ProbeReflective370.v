(*
   本文件为测试：ProbeReflective370。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Coreflective.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Construction.Reflective.Idempotent.
Require Import Category.Construction.Reflective.Monadic.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Construction.Reflective.Universal.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Epi.
Require Import Category.Instance.Grp.Center.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Abelianization.
Require Import Category.Instance.Grp.Abelianize.
Require Import Category.Instance.Grp.Abelianize.Reflective.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Instance.Ab.Monoidal.
Require Import Category.Instance.Ab.DirectedColimit.
Require Import Category.Instance.Ab.Character.Finite.
Require Import Category.Adjunction.Unitalization.
Require Import Category.Instance.Ab.TorsionFree.
Require Import Category.Instance.Ab.Torsion.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Quotient.
Require Import Category.Instance.Rng.Commutativize.
Require Import Category.Instance.Rng.Algebras.
Require Import Category.Instance.Rng.Algebras.Associative.
Require Import Coq.ZArith.ZArith.
Require Import Category.Instance.Rng.Commutativize.UT2.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Reals.Rseries.
Require Import Coq.Reals.SeqProp.
Require Import Coq.Reals.Rcomplete.
Require Import Coq.micromega.Lra.
Require Import Category.Instance.Met.
Require Import Category.Instance.Met.Completion.
Require Import Category.Instance.Met.Uniform.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.AbCategory.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Coproduct.
Require Import Category.Instance.Rng.Mod.
Require Import Category.Instance.Mod.Extension.
Require Import Category.Construction.Reflective.FixedPoints.
Require Import Category.Adjunction.FullFaithful.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lia.
Require Import Category.Instance.Mod.RingEpi.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(* The instrument *)
Fail Check p370_absent_name.

(* 相关说明。 （已译） *)

(* CONTROL: 含入 [AbGrp_Sub], record over it, and
 Abelianize.v's [Ab_to_Grp] factoring through it 对象. （已译） *)
Definition p370_abgrp_incl@{u p +} : Sub Grp@{u p} AbGrp_Sub ⟶ Grp@{u p} :=
  Incl Grp@{u p} AbGrp_Sub.

Definition p370_abgrp_record@{u p +} : @Reflective Grp@{u p} AbGrp_Sub :=
  Ab_Reflective_in_Grp.

Example p370_ab_to_grp_obj@{u p +} (A : Ab@{u p}) :
  Incl Grp@{u p} AbGrp_Sub (Ab_to_AbGrp A) = Ab_to_Grp A := eq_refl.

(* N1 *)
Fail Definition p370_incl_is_ab_to_grp (S : Subcategory Grp) :
  Incl Grp S = Ab_to_Grp := eq_refl.

(* N2 *)
Fail Definition p370_record_from_abelianize (S : Subcategory Grp) :
  Reflective S :=
  @Build_Reflective Grp S _ Abelianization_Functor
    abelianize_adjunction_via_transform.

(* 相关说明。 （已译） *)

(* CONTROL: 对象, hom types two [equiv] relations of
 two 范畴 convert. （已译） *)
Example p370_op_obj {C : Category} (S : Subcategory C) :
  obj[Opposite (Sub C S)] = obj[Sub (Opposite C) (op_subcategory S)]
  := eq_refl.

Example p370_op_hom {C : Category} (S : Subcategory C) (x y : Sub C S) :
  @hom (Opposite (Sub C S)) x y
    = @hom (Sub (Opposite C) (op_subcategory S)) x y := eq_refl.

Example p370_op_equiv {C : Category} (S : Subcategory C) (x y : Sub C S) :
  @Setoid.equiv _ (@homset (Opposite (Sub C S)) x y)
    = @Setoid.equiv _ (@homset (Sub (Opposite C) (op_subcategory S)) x y)
  := eq_refl.

(* N3 *)
Fail Example p370_op_cat {C : Category} (S : Subcategory C) :
  Opposite (Sub C S) = Sub (Opposite C) (op_subcategory S) := eq_refl.

(* N4 *)
Fail Example p370_op_homset {C : Category} (S : Subcategory C)
  (x y : Sub C S) :
  @homset (Opposite (Sub C S)) x y
    = @homset (Sub (Opposite C) (op_subcategory S)) x y := eq_refl.

(* CONTROL: record read back covariantly rebuilt record,
 coreflector covariant 函子 进入 subcategory. （已译） *)
Example p370_bridge_roundtrip {C : Category} {S : Subcategory C}
  (R : Coreflective S) :
  Coreflective_of_adjunction (coreflective_full R) (coreflector R)
    (coreflective_adj R) = R := eq_refl.

Definition p370_coreflector_covariant {C : Category} {S : Subcategory C}
  (R : Coreflective S) : C ⟶ Sub C S := coreflector R.

(* N5 *)
Fail Example p370_coreflector_is_reflector {C : Category}
  {S : Subcategory C} (R : Coreflective S) :
  coreflector R = reflector R := eq_refl.

(* 相关说明。 （已译） *)

(* CONTROL: universal arrows, unit transpose the
 恒等 nose. （已译） *)
Example p370_ua_unit {C : Category} {S : Subcategory C}
  (full : Construction.Subcategory.Full C S)
  (UA : ∀ x : C, UniversalArrow x (Incl C S)) (x : C) :
  @Category.Theory.Adjunction.unit _ _ _ _
    (reflective_adj (Reflective_of_UniversalArrows full UA)) x
    = fmap[Incl C S]
        (@id (Sub C S)
           (fobj[reflector (Reflective_of_UniversalArrows full UA)] x))
      ∘ @arrow C (Sub C S) x (Incl C S) (UA x) := eq_refl.

(* N6 *)
Fail Example p370_ua_unit_arrow {C : Category} {S : Subcategory C}
  (full : Construction.Subcategory.Full C S)
  (UA : ∀ x : C, UniversalArrow x (Incl C S)) (x : C) :
  @Category.Theory.Adjunction.unit _ _ _ _
    (reflective_adj (Reflective_of_UniversalArrows full UA)) x
    = @arrow C (Sub C S) x (Incl C S) (UA x) := eq_refl.

(* CONTROL: abelianization unit, transposed 复合 and
 pointwise Mac Lane's projection. （已译） *)
Example p370_abgrp_unit@{u p +} (G : Grp@{u p}) :
  abgrp_unit G
    = fmap[Incl Grp@{u p} AbGrp_Sub] (@id AbGrp (fobj[AbGrp_reflector] G))
      ∘ abel_proj G := eq_refl.

Example p370_abgrp_unit_point@{u p +} (G : Grp@{u p}) (a : carrier G) :
  grp_map (abgrp_unit G) a = grp_map (abel_proj G) a := eq_refl.

(* N7 *)
Fail Example p370_abgrp_unit_proj@{u p +} (G : Grp@{u p}) :
  abgrp_unit G = abel_proj G := eq_refl.

(* N8 *)
Example p370_abgrp_unit_map@{u p +} (G : Grp@{u p}) :
  grp_map (abgrp_unit G) = grp_map (abel_proj G) := eq_refl.

(* CONTROL: torsion counit, likewise, against 含入 TA. （已译） *)
Example p370_torsion_counit@{u p +} (A : Ab@{u p}) :
  torsion_counit A
    = torsion_incl A
      ∘ fmap[Incl Ab@{u p} Torsion_Sub]
          (@id TorsionCat (fobj[torsion_coreflector] A)) := eq_refl.

Example p370_torsion_counit_point@{u p +} (A : Ab@{u p})
  (x : carrier (TorsionAb A)) :
  cmon_map (torsion_counit A) x = cmon_map (torsion_incl A) x := eq_refl.

(* N9 *)
Fail Example p370_torsion_counit_incl@{u p +} (A : Ab@{u p}) :
  torsion_counit A = torsion_incl A := eq_refl.

(* N10 *)
Example p370_torsion_counit_map@{u p +} (A : Ab@{u p}) :
  cmon_map (torsion_counit A) = cmon_map (torsion_incl A) := eq_refl.

(* 相关说明。 （已译） *)
Example p370_crng_unit@{u p +} (R : Rng@{u p}) :
  crng_unit R
    = fmap[Incl Rng@{u p} CRng_Sub] (@id CRng (fobj[CRng_reflector] R))
      ∘ rquot_proj (CommIdeal R) := eq_refl.

Example p370_crng_unit_point@{u p +} (R : Rng@{u p})
  (a : carrier (rig_setoid R)) :
  rig_map (crng_unit R) a = rig_map (rquot_proj (CommIdeal R)) a := eq_refl.

(* N11 *)
Fail Example p370_crng_unit_proj@{u p +} (R : Rng@{u p}) :
  crng_unit R = rquot_proj (CommIdeal R) := eq_refl.

(* N12 *)
Example p370_crng_unit_map@{u p +} (R : Rng@{u p}) :
  rig_map (crng_unit R) = rig_map (rquot_proj (CommIdeal R)) := eq_refl.

(* CONTROL: completion unit MetU Met, pointwise the
 常值 sequence. （已译） *)
Example p370_completionU_unit_point@{u o +} (X : MetU@{u o}) (a : X) :
  umap (@Category.Theory.Adjunction.unit _ _ _ _ completionU_adj X) a
    = eta_seq X a := eq_refl.

Example p370_completion_unit_point@{u o +} (X : Met@{u o}) (a : X) :
  isometry_map (@Category.Theory.Adjunction.unit _ _ _ _ completion_adj X) a
    = eta_seq X a := eq_refl.

(* N13 *)
Example p370_completionU_unit_eta@{u o +} (X : MetU@{u o}) :
  @Category.Theory.Adjunction.unit _ _ _ _ completionU_adj X = etaU X
  := eq_refl.

(* N14 *)
Fail Example p370_completion_unit_eta@{u o +} (X : Met@{u o}) :
  @Category.Theory.Adjunction.unit _ _ _ _ completion_adj X = eta X
  := eq_refl.

(* 相关说明。 （已译） *)
Example p370_tmod_unit_point {R T : Rng} (phi : R ~{Rng}~> T)
  (Hc : CentralImage phi) (He : Epic phi) (M : RMod R)
  (m : carrier (cmon_setoid M)) :
  cmon_map
    (rm_hom (@Category.Theory.Adjunction.unit _ _ _ _
               (TMod_adj phi Hc He) M)) m
    = ext_gen phi M (rig_one (ring_rig T)) m := eq_refl.

(* N15 *)
Fail Example p370_tmod_unit_ext {R T : Rng} (phi : R ~{Rng}~> T)
  (Hc : CentralImage phi) (He : Epic phi) (M : RMod R) :
  @Category.Theory.Adjunction.unit _ _ _ _ (TMod_adj phi Hc He) M
    = extend_adj_unit phi Hc M := eq_refl.

(* * ** Arrow parts, counits 复合 函子 （已译） *)

(* CONTROL: abelianization reflector against Abelianize.v's, on
 对象 nose arrows up [≈]. （已译） *)
Example p370_abgrp_factors_obj@{u p +} (G : Grp@{u p}) :
  fobj[AbGrp_reflector] G
    = fobj[Ab_to_AbGrp] (fobj[Abelianization_Functor] G) := eq_refl.

Definition p370_abgrp_factors_fmap@{u p +} (G H : Grp@{u p})
  (f : G ~{Grp@{u p}}~> H) :
  fmap[AbGrp_reflector] f
    ≈ fmap[Ab_to_AbGrp] (fmap[Abelianization_Functor] f) :=
  abgrp_reflector_factors_fmap G H f.

(* N16 *)
Fail Example p370_abgrp_factors_fmap_eq@{u p +} (G H : Grp@{u p})
  (f : G ~{Grp@{u p}}~> H) :
  fmap[AbGrp_reflector] f
    = fmap[Ab_to_AbGrp] (fmap[Abelianization_Functor] f) := eq_refl.

(* CONTROL: 含入's factorization agrees arrows nose,
 函子 up [≈]. （已译） *)
Example p370_ab_to_grp_fmap@{u p +} (A B : Ab@{u p})
  (f : A ~{Ab@{u p}}~> B) :
  fmap[Incl Grp@{u p} AbGrp_Sub] (fmap[Ab_to_AbGrp] f) = fmap[Ab_to_Grp] f
  := eq_refl.

Definition p370_ab_to_grp_factors@{u p +} :
  Incl Grp@{u p} AbGrp_Sub ◯ Ab_to_AbGrp ≈ Ab_to_Grp :=
  ab_to_grp_factors.

(* N17 *)
Fail Example p370_ab_to_grp_factors_eq@{u p +} :
  Incl Grp@{u p} AbGrp_Sub ◯ Ab_to_AbGrp = Ab_to_Grp := eq_refl.

(* CONTROL: abelianization counit invertible at every 对象 of
 subcategory. （已译） *)
Definition p370_abgrp_counit_iso@{u p +} (d : Sub Grp@{u p} AbGrp_Sub) :
  fobj[AbGrp_reflector] (fobj[Incl Grp@{u p} AbGrp_Sub] d) ≅[AbGrp] d :=
  abgrp_reflect_iso d.

(* N18 *)
Fail Example p370_abgrp_counit_point@{u p +} (d : Sub Grp@{u p} AbGrp_Sub)
  (a : carrier `1 d) :
  grp_map `1 (@counit _ _ _ _ AbGrp_adj d) a = a := eq_refl.

(* CONTROL: couniversal arrow torsion coreflection the
 含入 TA, nose. （已译） *)
Example p370_torsion_coarrow@{u p +} (A : Ab@{u p}) :
  @coarrow Ab@{u p} TorsionCat A (Incl Ab@{u p} Torsion_Sub)
    (torsion_couniversal_arrow A) = torsion_incl A := eq_refl.

(* N19 *)
Fail Example p370_torsion_fmap@{u p +} (A B : Ab@{u p})
  (f : A ~{Ab@{u p}}~> B) :
  fmap[torsion_coreflector] f
    = (torsion_lift (TorsionAb_IsTorsion A) (f ∘ torsion_incl A); I)
  := eq_refl.

(* CONTROL: MetU reflector's 对象 completion, whole
 Σ-对象, nose. （已译） *)
Example p370_completionU_obj@{u o +} (X : MetU@{u o}) :
  fobj[reflector CMet_Reflective_in_MetU] X = CompletionU X := eq_refl.

(* N20 *)
Fail Example p370_completionU_counit_point@{u o +}
  (Y : Sub MetU@{u o} CompleteSpacesU) (y : `1 Y) :
  umap (`1 (@counit _ _ _ _ completionU_adj Y)) (eta_seq (`1 Y) y) = y
  := eq_refl.

(* N21 *)
Fail Example p370_completionU_fmap_point@{u o +} (X Y : MetU@{u o})
  (f : X ~{MetU@{u o}}~> Y) (a : X) :
  umap (`1 (fmap[reflector CMet_Reflective_in_MetU] f)) (eta_seq X a)
    = eta_seq Y (umap f a) := eq_refl.

(* 相关说明。 （已译） *)

(* CONTROL: 常值 map [Harmonic] arrow [MetU]; the
 comparison 恒等 对象; it not full. （已译） *)
Definition p370_const_umap@{u +| Set < u +} :
  Harmonic ~{MetU@{u Set}}~> Harmonic :=
  const_umap Harmonic Harmonic 0%nat.

Example p370_met_to_metu_obj@{u o +| o < u +} (X : Met@{u o}) :
  fobj[Met_to_MetU@{u o}] X = X := eq_refl.

Definition p370_not_full@{u +| Set < u +} :
  Functor.Full Met_to_MetU@{u Set} → False := Met_to_MetU_not_Full.

(* N22 *)
Fail Definition p370_const_isometry@{u +| Set < u +} :
  Harmonic ~{Met@{u Set}}~> Harmonic :=
  const_umap Harmonic Harmonic 0%nat.

(* 相关说明。 （已译） *)

(* CONTROL: localization's 普遍性质 at ring carrier
 level [Set], mediator [loc_hom] above it. （已译） *)
Definition p370_loc_at_set@{u +| Set < u +} (W : obj[Rng@{u Set}])
  (psi : Int_Ring ~{Rng@{u Set}}~> W)
  (H : InvertsSet (R := Int_Ring) PosZ psi) :=
  @snd _ _ ZtoQ_IsLocalization W psi H.

Definition p370_loc_hom_above@{u p +| Set < p, p < u +}
  (W : obj[Rng@{u p}]) (psi : Int_Ring ~{Rng@{u p}}~> W)
  (H : InvertsSet (R := Int_Ring) PosZ psi) : Q_Ring ~{Rng@{u p}}~> W :=
  loc_hom W psi H.

(* N23 *)
Fail Definition p370_loc_above@{u p +| Set < p, p < u +}
  (W : obj[Rng@{u p}]) (psi : Int_Ring ~{Rng@{u p}}~> W)
  (H : InvertsSet (R := Int_Ring) PosZ psi) :=
  @snd _ _ ZtoQ_IsLocalization W psi H.

(* CONTROL: restriction full exactly epimorphisms, arbitrary
 rings, reflection's 伴随 own 常值. （已译） *)
Definition p370_full_iff_epic {R T : Rng} (phi : R ~{Rng}~> T) :
  Functor.Full (Restrict phi) ↔ Epic phi := Restrict_Full_iff_Epic phi.

Definition p370_tmod_adj {R T : Rng} (phi : R ~{Rng}~> T)
  (Hc : CentralImage phi) (He : Epic phi) :
  reflector (TMod_Reflective_in_RMod phi Hc He)
    ⊣ Incl (RMod R) (UnitFixed (extend_restrict_adjunction phi Hc)) :=
  TMod_adj phi Hc He.

(** ** Non-vacuity, restated *)

(* CONTROL: each reflection coreflection proper at named 对象,
 statement restated independently 证明. （已译） *)
Definition p370_S3_nontrivial@{u +} :
  @Setoid.equiv (carrier `1 (fobj[AbGrp_reflector] (S3 : Grp@{u Set}))) _
    S3_s s3_unit → False := S3_reflection_nontrivial.

Definition p370_S3_not_iso@{u +} :
  IsIsomorphism (abgrp_unit (S3 : Grp@{u Set})) → False :=
  abgrp_unit_S3_not_iso.

Definition p370_mixed_not_iso@{u +} :
  IsIsomorphism (torsion_counit (MixedAb : Ab@{u Set})) → False :=
  torsion_counit_MixedAb_not_iso.

Definition p370_UT2_not_iso@{u p +} :
  IsIsomorphism (crng_unit (UT2 : Rng@{u p})) → False :=
  crng_unit_UT2_not_iso.

Definition p370_harmonic_not_iso@{u +| Set < u +} :
  IsIsomorphism
    (@Category.Theory.Adjunction.unit _ _ _ _ completionU_adj
       (Harmonic : MetU@{u Set})) → False :=
  completionU_unit_Harmonic_not_iso.

Definition p370_ZMod_not_fixed :
  sobj (RMod Int_Ring) (UnitFixed (extend_restrict_adjunction ZtoQ Q_central))
    (Ring_RMod Int_Ring) → False := ZMod_not_UnitFixed.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Print Assumptions CMet_Reflective_in_MetU.

(* 相关说明。 （已译） *)

(* Construction/Reflective/Coreflective.v: 15 names. *)
Check Coreflective_of_adjunction.
Check Coreflective_roundtrip.
Check coreflective_adj.
Check coreflective_adj_roundtrip.
Check coreflective_counit_is_op_unit.
Check coreflective_full.
Check coreflective_full_roundtrip.
Check coreflective_unit_is_op_counit.
Check coreflective_unit_iso.
Check coreflector.
Check coreflector_fmap_roundtrip.
Check coreflector_obj_roundtrip.
Check coreflector_op.
Check coreflector_op_adj.
Check coreflector_roundtrip.

(* Construction/Reflective/Monadic.v: 14 names. *)
Check Reflective_EM_Equivalence.
Check Reflective_Monadic.
Check Reflective_Monadic_left.
Check reflective_comparison.
Check reflective_comparison_ESO.
Check reflective_comparison_Faithful.
Check reflective_comparison_Full.
Check reflective_comparison_alg.
Check reflective_comparison_obj.
Check reflective_comparison_prefmap.
Check reflective_eso_iso.
Check reflective_eso_iso_to.
Check reflective_eso_obj.
Check reflective_eso_obj_is_reflector.

(* Construction/Reflective/Universal.v: 6 names. *)
Check Coreflective_of_CouniversalArrows.
Check Coreflective_of_CouniversalArrows_counit.
Check Coreflective_of_CouniversalArrows_obj.
Check Reflective_of_UniversalArrows.
Check Reflective_of_UniversalArrows_obj.
Check Reflective_of_UniversalArrows_unit.

(* Instance/Grp/Abelianize/Reflective.v: 61 names. *)
Check AbGrp.
Check AbGrp_Full.
Check AbGrp_IdempotentMonad.
Check AbGrp_Incl_Monadic.
Check AbGrp_Sub.
Check AbGrp_adj.
Check AbGrp_iso.
Check AbGrp_reflector.
Check AbTwo_in_AbGrp.
Check Ab_AbGrp_Equivalence.
Check Ab_Reflective_in_Grp.
Check Ab_to_AbGrp.
Check Ab_to_AbGrp_ESO.
Check Ab_to_AbGrp_Faithful.
Check Ab_to_AbGrp_Full.
Check AbelianizationGrp.
Check Grp_to_AbOb.
Check IsAbelian.
Check Reflective.AbGrp_iso_obligation_1.
Check Reflective.AbGrp_iso_obligation_2.
Check Reflective.AbGrp_iso_obligation_3.
Check Reflective.AbGrp_iso_obligation_4.
Check Reflective.AbGrp_iso_obligation_5.
Check Reflective.AbGrp_iso_obligation_6.
Check Reflective.AbGrp_iso_obligation_7.
Check Reflective.AbGrp_iso_obligation_8.
Check Reflective.Ab_to_AbGrp_Full_obligation_1.
Check Reflective.Ab_to_AbGrp_obligation_1.
Check Reflective.Ab_to_AbGrp_obligation_2.
Check Reflective.Ab_to_AbGrp_obligation_3.
Check Reflective.Grp_to_AbOb_obligation_1.
Check Reflective.Grp_to_AbOb_obligation_2.
Check Reflective.Grp_to_AbOb_obligation_3.
Check Reflective.Grp_to_AbOb_obligation_4.
Check Reflective.abel_med_grp_obligation_1.
Check Reflective.abel_med_grp_obligation_2.
Check Reflective.abel_med_grp_obligation_3.
Check S3_not_IsAbelian.
Check S3_reflection_nontrivial.
Check ab_to_grp_factors.
Check ab_to_grp_factors_fmap.
Check ab_to_grp_factors_obj.
Check abel_kills_grp.
Check abel_med_grp.
Check abgrp_S3_med_s.
Check abgrp_S3_med_unit.
Check abgrp_S3_separates.
Check abgrp_arrow_is_proj.
Check abgrp_record_reflector.
Check abgrp_reflect_iso.
Check abgrp_reflector_factors.
Check abgrp_reflector_factors_fmap.
Check abgrp_reflector_factors_obj.
Check abgrp_reflector_obj.
Check abgrp_unit.
Check abgrp_unit_S3_merges.
Check abgrp_unit_S3_not_iso.
Check abgrp_unit_is_proj.
Check abgrp_unit_pointwise.
Check abgrp_universal.
Check abgrp_universal_arrow.

(* Instance/Ab/Torsion.v: 37 names. *)
Check IsTorsion.
Check MixedAb_not_torsion.
Check Torsion.torsion_lift_obligation_1.
Check Torsion.torsion_lift_obligation_2.
Check Torsion.torsion_lift_obligation_3.
Check TorsionAb_IsTorsion.
Check TorsionCat.
Check TorsionFree_EM_Equivalence.
Check TorsionFree_EM_MLocal.
Check TorsionFree_IdempotentMonad.
Check TorsionFree_Incl_Monadic.
Check TorsionFree_Monad.
Check TorsionPart.
Check Torsion_Coreflective.
Check Torsion_Full.
Check Torsion_Sub.
Check ZAb_TA_trivial.
Check ZMod2_IsTorsion.
Check ZMod2_Torsion.
Check ZMod2_coreflect_iso.
Check mixed_tors_in_TA.
Check mixed_tors_in_TA_nonzero.
Check torsion_coarrow_is_incl.
Check torsion_coreflection.
Check torsion_coreflector.
Check torsion_coreflector_obj.
Check torsion_counit.
Check torsion_counit_MixedAb_not_iso.
Check torsion_counit_is_incl.
Check torsion_counit_pointwise.
Check torsion_couniversal.
Check torsion_couniversal_arrow.
Check torsion_lift.
Check torsion_map.
Check torsion_record_adj.
Check torsion_record_coreflector.
Check torsionfree_monad_obj.

(* Instance/Rng/Commutativize.v: 30 names. *)
Check CRng_Reflective_in_Rng.
Check CRng_adj.
Check CRng_reflector.
Check CommIdeal.
Check Commutativize.
Check CommutativizeC.
Check Commutativize_comm.
Check InCommIdeal.
Check InCommIdeal_ind.
Check InCommIdeal_rec.
Check InCommIdeal_rect.
Check InCommIdeal_sind.
Check IsCommutative.
Check IsCommutative_is_CRng_sobj.
Check comm_kills.
Check crng_arrow_is_proj.
Check crng_reflect_iso.
Check crng_reflector_obj.
Check crng_unit.
Check crng_unit_is_proj.
Check crng_unit_pointwise.
Check crng_universal.
Check crng_universal_arrow.
Check ici_add.
Check ici_gen.
Check ici_mul_l.
Check ici_mul_r.
Check ici_resp.
Check ici_zero.
Check rcomm.

(* Instance/Rng/Commutativize/UT2.v: 15 names. *)
Check Commutativize_UT2_nonzero.
Check UT2.ut2_diag1_hom_obligation_1.
Check UT2.ut2_diag1_hom_obligation_2.
Check UT2.ut2_diag1_hom_obligation_3.
Check UT2.ut2_diag1_hom_obligation_4.
Check UT2_not_commutative_ring.
Check crng_UT2_med_one.
Check crng_unit_UT2_merges.
Check crng_unit_UT2_not_iso.
Check ut2_diag1.
Check ut2_diag1_hom.
Check ut2_diag1_proper.
Check ut2_e12_commutator.
Check ut2_e12_in_CommIdeal.
Check ut2_e12_nonzero.

(* Instance/Mod/RingEpi.v: 58 names. *)
Check AbEndRing.
Check EndRig_conj.
Check Epic_Restrict_Full.
Check Epic_Restrict_Full_prefmap.
Check InvertsSet.
Check IsLocalization.
Check PosZ.
Check QMod_Reflective_in_ZMod.
Check QMod_equiv_UnitFixed.
Check Restrict_Faithful.
Check Restrict_Full_Epic.
Check Restrict_Full_iff_Epic.
Check Restrict_UnitFixed.
Check Restrict_UnitFixed_ESO.
Check Restrict_UnitFixed_Faithful.
Check Restrict_UnitFixed_Full.
Check Restrict_UnitFixed_incl.
Check Restrict_UnitFixed_obj.
Check Restrict_ZtoQ_Full.
Check TMod_Reflective_in_RMod.
Check TMod_adj.
Check TMod_equiv_UnitFixed.
Check TMod_reflector_obj.
Check TMod_unit_pointwise.
Check ZMod_not_UnitFixed.
Check ZtoQ_IsLocalization.
Check ZtoQ_epic_of_localization.
Check ZtoQ_inverts.
Check inject_pos_nonzero.
Check linear_of_twist_fixed.
Check loc_cancel.
Check loc_fun.
Check loc_fun_add.
Check loc_fun_mul.
Check loc_fun_respects.
Check loc_fun_spec.
Check loc_hom.
Check loc_hom_factors.
Check loc_hom_unique.
Check loc_images_commute.
Check loc_inv.
Check loc_inv_l.
Check loc_inv_one.
Check loc_inv_r.
Check loc_morphism.
Check loc_split.
Check localization_epic.
Check module_rep.
Check restrict_counit_iso.
Check restrict_idempotent.
Check shear_from.
Check shear_iso.
Check shear_to.
Check smul_endo.
Check twist_fixed_of_linear.
Check twisted_rep.
Check twisted_rep_value.
Check two_actions_id.

(* 相关说明。 （已译） *)

(*
   本节说明 ProbeReflective370 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check Build_UMap.
Check CMetU.
Check CMetU_Full.
Check CMetU_Incl.
Check CMet_Reflective_in_Met.
Check CMet_Reflective_in_MetU.
Check CompleteSpacesU.
Check CompletionU.
Check CompletionU_UniversalArrow.
Check MetU.
Check Met_to_MetU.
Check Met_to_MetU_Faithful.
Check Met_to_MetU_not_Full.
Check Met_to_MetU_obj.
Check UCont.
Check UMap.
Check UMap_Setoid.
Check UMap_equiv.
Check Uniform.MetU_obligation_1.
Check Uniform.MetU_obligation_2.
Check Uniform.MetU_obligation_3.
Check Uniform.MetU_obligation_4.
Check Uniform.Met_to_MetU_obligation_1.
Check Uniform.Met_to_MetU_obligation_2.
Check Uniform.Met_to_MetU_obligation_3.
Check Uniform.UMap_Setoid_obligation_1.
Check completionU_adj.
Check completionU_reflector_obj.
Check completionU_unit_Harmonic_not_iso.
Check completionU_unit_pointwise.
Check completion_adj.
Check completion_reflector_obj.
Check completion_reflectors_agree.
Check completion_unit_pointwise.
Check const_umap.
Check etaU.
Check iso_umap.
Check uext.
Check uext_MCauchy.
Check uext_close.
Check uext_eta.
Check uext_morphism.
Check uext_proper.
Check uext_seq.
Check uext_spec.
Check uext_uc.
Check uext_unique.
Check uext_val.
Check umap.
Check umap_MConverges.
Check umap_uc.
Check umet_compose.
Check umet_compose_respects.
Check umet_id.
Check ureal_below_all_zero.
