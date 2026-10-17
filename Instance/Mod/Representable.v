Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Free.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 Book: Riehl, "Category Theory in Context", 2nd ed., §2.1
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Book: Riehl, "Category Theory in Context", 2nd ed., §4.1
 nLab:      https://ncatlab.org/nlab/show/representable+functor
 nLab:      https://ncatlab.org/nlab/show/free+module
 Wikipedia: https://en.wikipedia.org/wiki/Representable_functor

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section RingRepresents.

Context (R : RingObject).

(** ** The module map determined by an element *)

(*
   本节说明 Representable 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition rmod_by_element (W : RModObject R)
  (m : carrier (cmon_setoid W)) : Ring_RMod R ~{RMod R}~> W := {|
  rm_hom := {| cmon_map := {| morphism := fun r => rm_smul W r m |} |}
|}.
Next Obligation.
  intros W m a b Hab; exact (rm_smul_respects W _ _ Hab _ _ (reflexivity m)).
Qed.
Next Obligation. intros W m; simpl; apply rm_smul_zero_l. Qed.
Next Obligation. intros W m a b; simpl; apply rm_smul_distr_r. Qed.
Next Obligation. intros W m r a; simpl; apply rm_smul_assoc. Qed.

(** A module map out of R is determined by its value at 1. *)
Lemma rmod_out_of_ring (W : RModObject R) (g : Ring_RMod R ~{RMod R}~> W)
  (r : carrier (rig_setoid R)) :
  cmon_map (rm_hom g) r
    ≈ rm_smul W r (cmon_map (rm_hom g) (rig_one R)).
Proof.
  transitivity (cmon_map (rm_hom g) (rig_mul R r (rig_one R))).
  - apply (proper_morphism (cmon_map (rm_hom g))).
    symmetry; apply rig_mul_one_r.
  - exact (rm_map_smul g r (rig_one R)).
Qed.

(** ** Riehl's Example 2.1.5(iv) *)

(** The unit of R is a universal element of the underlying-set functor.
    The factorization is [rmod_by_element], the commutation is
    [rm_smul_one], and the uniqueness is [rmod_out_of_ring]. *)
Definition ring_universal_element
  : AUniversalElement (RMod_Forget R) (Ring_RMod R).
Proof.
  unshelve econstructor.
  - exact (rig_one R).
  - intros W m.
    unshelve econstructor.
    + exact (rmod_by_element W m).
    + simpl; apply rm_smul_one.
    + intros g Hg r; simpl.
      symmetry.
      transitivity (rm_smul W r (cmon_map (rm_hom g) (rig_one R))).
      * exact (rmod_out_of_ring W g r).
      * exact (rm_smul_respects W _ _ (reflexivity r) _ _ Hg).
Defined.

Definition ring_universal_element_bundled : UniversalElement (RMod_Forget R) :=
  UniversalElement_of_AUniversalElement ring_universal_element.

(** The representation as a NATURAL isomorphism in [[RMod R, Sets]] —
    Riehl's packaging, not merely the ∃! factorization property. *)
Definition rmod_representation
  : @Curried_Hom (RMod R) (Ring_RMod R) ≅[[RMod R, Sets]] RMod_Forget R :=
  ue_representation (RMod_Forget R) (Ring_RMod R) ring_universal_element.

Definition rmod_representable : Representable (RMod_Forget R) :=
  Representable_of_UniversalElement ring_universal_element_bundled.

(** The same content as a universal arrow from the one-point setoid, in
    both of Theory/Universal/Arrow.v's encodings. *)
Definition ring_auniversal_arrow
  : AUniversalArrow SetsOne (RMod_Forget R) (Ring_RMod R) :=
  AUniversalArrow_of_AUniversalElement (RMod_Forget R) (Ring_RMod R)
    ring_universal_element.

Definition ring_universal_arrow : UniversalArrow SetsOne (RMod_Forget R).
Proof.
  unshelve eapply
    (universal_arrow_from_UMP SetsOne (RMod_Forget R) (Ring_RMod R)).
  - exact (@universal_arrow _ _ _ _ _ ring_auniversal_arrow).
  - intros W f.
    unshelve econstructor.
    + exact (unique_obj (@universal_arrow_universal _ _ _ _ _
                           ring_auniversal_arrow W f)).
    + symmetry.
      exact (unique_property (@universal_arrow_universal _ _ _ _ _
                                ring_auniversal_arrow W f)).
    + intros v Hv.
      exact (uniqueness (@universal_arrow_universal _ _ _ _ _
                           ring_auniversal_arrow W f) v (symmetry Hv)).
Defined.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition free_one_universal_element
  : AUniversalElement (RMod_Forget R) (@FreeModObject R SetsOne) :=
  AUniversalElement_of_AUniversalArrow (RMod_Forget R)
    (@FreeModObject R SetsOne)
    (free_module_AUniversalArrow R SetsOne).

Definition free_one_generator_iso
  : @FreeModObject R SetsOne ≅[RMod R] Ring_RMod R :=
  universal_element_iso free_one_universal_element ring_universal_element.

(** The isomorphism carrying the basis vector to 1 is the ONLY one: a
    bare [≅] would leave the free module's automorphisms in play. *)
Definition free_one_generator_iso_unique
  : Unique (fun i : @FreeModObject R SetsOne ≅[RMod R] Ring_RMod R =>
              fmap[RMod_Forget R] (to i)
                (@aue_elem _ (RMod_Forget R) _ free_one_universal_element)
                ≈ rig_one R) :=
  universal_element_unique free_one_universal_element ring_universal_element.

(** The universal element of the free-module side is the basis vector at
    the unique point, definitionally. *)
Example free_one_universal_elem_is_generator :
  @aue_elem _ (RMod_Forget R) _ free_one_universal_element
    = @fv_gen R SetsOne ttt := eq_refl.

End RingRepresents.

(** ** The witness at ℤ

    The represented set of the ℤ-module ℤ is the integers, and the
    mediating map is multiplication by the chosen integer, which
    computes. *)

Example int_universal_elem : @aue_elem _ (RMod_Forget Int_Ring) _
  (ring_universal_element Int_Ring) = 1%Z := eq_refl.

Example int_mediator_computes :
  cmon_map (rm_hom (rmod_by_element Int_Ring Int_RMod 5%Z)) 3%Z = 15%Z
  := eq_refl.
