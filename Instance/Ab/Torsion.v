(*
 nLab: https://ncatlab.org/nlab/show/torsion+subgroup
 nLab: https://ncatlab.org/nlab/show/coreflective+subcategory

   本文件给出阿贝尔群相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Monad.Comparison.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Idempotent.
Require Import Category.Construction.Reflective.Coreflective.
Require Import Category.Construction.Reflective.Monadic.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Instance.Ab.Monoidal.
Require Import Category.Instance.Ab.DirectedColimit.
Require Import Category.Instance.Ab.Character.Finite.
Require Import Category.Adjunction.Unitalization.
Require Import Category.Instance.Ab.TorsionFree.

Generalizable All Variables.

(* 相关说明。 （已译） *)

Definition IsTorsion@{a c p +} (A : AbObject@{a c p}) : Type :=
  ∀ x : carrier A, torsion_mem A x.

Definition Torsion_Sub@{u p +} : Subcategory Ab@{u p} :=
  @Build_Subcategory Ab@{u p} IsTorsion
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition TorsionCat@{u p +} : Category := Sub Ab@{u p} Torsion_Sub.

Definition Torsion_Full@{u p +} :
  Category.Construction.Subcategory.Full Ab@{u p} Torsion_Sub :=
  fun _ _ _ _ _ => I.

(* 相关说明。 （已译） *)
Definition TorsionAb_IsTorsion@{p +} (A : AbObject@{p p p}) :
  IsTorsion (TorsionAb A).
Proof.
  intros [a [k [Hk Hka]]].
  exists k; split; [ exact Hk | ].
  pose proof (nat_smul_hom (torsion_incl A) k
                (existT _ a (existT _ k (Hk, Hka)))) as E.
  simpl in E |- *.
  exact (transitivity E Hka).
Defined.

(* Mac Lane's TA, as an object of the subcategory. *)
Definition TorsionPart@{u p +} (A : Ab@{u p}) : TorsionCat :=
  (TorsionAb A; TorsionAb_IsTorsion A).

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition torsion_map@{u p +} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (a : carrier A) :
  torsion_mem A a → torsion_mem B (cmon_map f a).
Proof.
  intros [k [Hk Hka]].
  exists k; split; [ exact Hk | ].
  rewrite <- nat_smul_hom, Hka.
  apply cmon_map_zero.
Defined.

(* The mediator: a homomorphism out of a torsion group lands in TA. *)
Program Definition torsion_lift@{u p +} {T A : Ab@{u p}} (HT : IsTorsion T)
  (f : T ~{Ab@{u p}}~> A) : T ~{Ab@{u p}}~> TorsionAb A :=
  {| cmon_map := {| morphism := fun t : carrier T =>
       existT _ (cmon_map f t) (torsion_map f t (HT t)) |} |}.
Next Obligation. intros x y Hxy; simpl; now rewrite Hxy. Qed.
Next Obligation. simpl; apply cmon_map_zero. Qed.
Next Obligation. simpl; apply cmon_map_plus. Qed.

Theorem torsion_couniversal@{u p +} (A : Ab@{u p}) :
  ∀ (d : TorsionCat) (f : Incl Ab@{u p} Torsion_Sub d ~{Ab@{u p}}~> A),
    ∃! g : d ~{TorsionCat}~> TorsionPart A,
      f ≈ torsion_incl A ∘ fmap[Incl Ab@{u p} Torsion_Sub] g.
Proof.
  intros d f.
  unshelve eexists.
  - exact (torsion_lift `2 d f; I).
  - intro a; simpl; reflexivity.
  - intros g Hg a; simpl.
    exact (Hg a).
Defined.

Definition torsion_couniversal_arrow@{u p +} (A : Ab@{u p})
  : @CouniversalArrow Ab@{u p} TorsionCat A (Incl Ab@{u p} Torsion_Sub) :=
  @couniversal_arrow_from_UMP Ab@{u p} TorsionCat A (Incl Ab@{u p} Torsion_Sub)
    (TorsionPart A) (torsion_incl A) (torsion_couniversal A).

(* 相关说明。 （已译） *)

Definition torsion_coreflector@{u p +} : Ab@{u p} ⟶ TorsionCat :=
  RightAdjointFunctorFromCouniversalArrows (Incl Ab@{u p} Torsion_Sub)
    torsion_couniversal_arrow.

(* Mac Lane's "coreflective": the inclusion has a RIGHT adjoint. *)
Definition torsion_coreflection@{u p +} :
  Incl Ab@{u p} Torsion_Sub ⊣ torsion_coreflector :=
  AdjunctionFromCouniversalArrows (Incl Ab@{u p} Torsion_Sub)
    torsion_couniversal_arrow.

(* 相关说明。 （已译） *)
Definition Torsion_Coreflective@{u p +} : @Coreflective Ab@{u p} Torsion_Sub :=
  Coreflective_of_adjunction Torsion_Full torsion_coreflector
    torsion_coreflection.

(* * ** Readbacks: counit 含入 TA （已译） *)

Example torsion_coreflector_obj@{u p +} (A : Ab@{u p}) :
  `1 (fobj[torsion_coreflector] A) = TorsionAb A := eq_refl.

Example torsion_coarrow_is_incl@{u p +} (A : Ab@{u p}) :
  @coarrow Ab@{u p} TorsionCat A (Incl Ab@{u p} Torsion_Sub)
    (torsion_couniversal_arrow A)
    = torsion_incl A := eq_refl.

Definition torsion_counit@{u p +} (A : Ab@{u p})
  : Incl Ab@{u p} Torsion_Sub (fobj[torsion_coreflector] A) ~{Ab@{u p}}~> A :=
  @counit _ _ _ _ torsion_coreflection A.

Example torsion_counit_pointwise@{u p +} (A : Ab@{u p})
  (x : carrier (TorsionAb A)) :
  cmon_map (torsion_counit A) x = cmon_map (torsion_incl A) x := eq_refl.

Lemma torsion_counit_is_incl@{u p +} (A : Ab@{u p}) :
  torsion_counit A ≈ torsion_incl A.
Proof.
  exact (counit_couniversal (Incl Ab Torsion_Sub)
           torsion_couniversal_arrow A).
Qed.

(* Read back record, coreflector 伴随 the
 covariant ones nose. （已译） *)
Example torsion_record_coreflector@{u p +} :
  @coreflector Ab@{u p} Torsion_Sub Torsion_Coreflective
    = torsion_coreflector := eq_refl.

Example torsion_record_adj@{u p +} :
  @coreflective_adj Ab@{u p} Torsion_Sub Torsion_Coreflective
    = torsion_coreflection := eq_refl.

(** ** Non-vacuity *)

(* ℤ/2 torsion, so it 对象 subcategory, unit of
 coreflection there invertible. （已译） *)
Definition ZMod2_IsTorsion@{a +} : IsTorsion (ZMod2 : AbObject@{a Set Set}) :=
  ZMod2_all_torsion.

Definition ZMod2_Torsion@{u +} : Sub Ab@{u Set} Torsion_Sub :=
  (ZMod2; ZMod2_IsTorsion).

Definition ZMod2_coreflect_iso@{u +} :
  ZMod2_Torsion ≅[Sub Ab@{u Set} Torsion_Sub]
    fobj[coreflector Torsion_Coreflective]
      (fobj[Incl Ab@{u Set} Torsion_Sub] ZMod2_Torsion) :=
  coreflective_unit_iso Torsion_Coreflective ZMod2_Torsion.

(* ℤ × ℤ/2 is not torsion... *)
Lemma MixedAb_not_torsion@{+} : IsTorsion MixedAb → False.
Proof. intro H; exact (mixed_gen_not_torsion (H mixed_gen)). Qed.

(* ...its torsion part is not trivial... *)
Definition mixed_tors_in_TA@{+} : carrier (TorsionAb MixedAb) :=
  existT _ mixed_tors mixed_tors_torsion.

Lemma mixed_tors_in_TA_nonzero@{+} :
  @equiv (carrier (TorsionAb MixedAb)) _ mixed_tors_in_TA
    (cmon_zero (TorsionAb MixedAb)) → False.
Proof. exact mixed_tors_not_zero. Qed.

(* 相关说明。 （已译） *)
Theorem torsion_counit_MixedAb_not_iso@{u +} :
  IsIsomorphism (torsion_counit (MixedAb : Ab@{u Set})) → False.
Proof.
  intros [g Hfg _].
  apply mixed_gen_not_torsion.
  apply (torsion_resp MixedAb (projT1 (cmon_map g mixed_gen)) mixed_gen).
  - exact (Hfg mixed_gen).
  - exact (projT2 (cmon_map g mixed_gen)).
Qed.

(* The same at ℤ: its torsion part is trivial. *)
Lemma ZAb_TA_trivial@{+} (x : carrier (TorsionAb ZAb)) :
  @equiv (carrier (TorsionAb ZAb)) _ x (cmon_zero (TorsionAb ZAb)).
Proof. exact (ZAb_torsion_trivial (projT1 x) (projT2 x)). Qed.

(* 相关说明。 （已译） *)

Definition TorsionFree_Monad@{u p +} :
  @Monad Ab@{u p} (Incl Ab@{u p} TorsionFree_Sub ◯ TorsionFree_reflector) :=
  Reflective_Monad TorsionFree_Reflective.

Definition TorsionFree_IdempotentMonad@{u p +} :
  @IdempotentMonad Ab@{u p}
    (Incl Ab@{u p} TorsionFree_Sub ◯ TorsionFree_reflector)
    TorsionFree_Monad :=
  Reflective_IdempotentMonad TorsionFree_Reflective.

Example torsionfree_monad_obj@{u p +} (A : Ab@{u p}) :
  fobj[Incl Ab@{u p} TorsionFree_Sub ◯ TorsionFree_reflector] A
    = AbModTorsion A
  := eq_refl.

(* Idempotent.v's correspondence, fed concrete record: algebras of
 induced 单子 equivalent M-local 对象... （已译） *)
Definition TorsionFree_EM_MLocal@{u p +} :
  EquivalenceOfCategories
    (@idem_G Ab@{u p} _ TorsionFree_Monad TorsionFree_IdempotentMonad) :=
  @Idempotent_EM_Equivalence Ab@{u p} _ TorsionFree_Monad
    TorsionFree_IdempotentMonad.

(* 相关说明。 （已译） *)
Definition TorsionFree_EM_Equivalence@{u p +} :
  EquivalenceOfCategories
    (@reflective_comparison Ab@{u p} _ TorsionFree_Reflective) :=
  Reflective_EM_Equivalence TorsionFree_Reflective.

Definition TorsionFree_Incl_Monadic@{u p +} :
  Monadic (Incl Ab@{u p} TorsionFree_Sub) :=
  Reflective_Monadic TorsionFree_Reflective.
