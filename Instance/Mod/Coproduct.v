Require Import Coq.ZArith.ZArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Biproduct.Cartesian.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.

Generalizable All Variables.

(** * The direct sum is the coproduct in R-Mod *)

(*
 Book: Riehl, "Category Theory in Context" (2nd ed.), §3.1,
 Wikipedia: https://en.wikipedia.org/wiki/Direct_sum_of_modules

   本文件给出余积实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Instance/Mod.v's convention: the obligations below are
   introduced by hand, so that the record binders [M] and [N] arrive with
   their own names rather than whatever the global obligation tactic has
   already put in scope. *)
#[local] Obligation Tactic := idtac.

(** ** The direct sum as an object of R-Mod *)

(* The underlying abelian group is Instance/Ab/Coproduct.v's
   [Ab_product]; all that is added is the componentwise action. *)
Program Definition RMod_product {R : RingObject}
  (M N : RModObject R) : RModObject R := {|
  rm_ab := Ab_product M N;
  rm_smul := fun r p => (rm_smul M r (fst p), rm_smul N r (snd p))
|}.
Next Obligation.
  intros R M N r s Hrs p q [H1 H2].
  split; simpl.
  - now rewrite Hrs, H1.
  - now rewrite Hrs, H2.
Qed.
Next Obligation.
  intros R M N r m n.
  split; simpl; apply rm_smul_distr_l.
Qed.
Next Obligation.
  intros R M N r s m.
  split; simpl; apply rm_smul_distr_r.
Qed.
Next Obligation.
  intros R M N r s m.
  split; simpl; apply rm_smul_assoc.
Qed.
Next Obligation.
  intros R M N m.
  split; simpl; apply rm_smul_one.
Qed.

(** ** The four structural morphisms *)

(* Each wraps the corresponding morphism of Ab; the single new obligation
   is compatibility with the action. *)
Program Definition RMod_inl {R : RingObject} (M N : RModObject R) :
  M ~{RMod R}~> RMod_product M N := {|
  rm_hom := Ab_inl M N
|}.
Next Obligation.
  intros R M N r m.
  split; simpl.
  - reflexivity.
  - symmetry.
    apply rm_smul_zero_r.
Qed.

Program Definition RMod_inr {R : RingObject} (M N : RModObject R) :
  N ~{RMod R}~> RMod_product M N := {|
  rm_hom := Ab_inr M N
|}.
Next Obligation.
  intros R M N r n.
  split; simpl.
  - symmetry.
    apply rm_smul_zero_r.
  - reflexivity.
Qed.

Program Definition RMod_exl {R : RingObject} (M N : RModObject R) :
  RMod_product M N ~{RMod R}~> M := {|
  rm_hom := Ab_exl M N
|}.
Next Obligation. intros R M N r p; reflexivity. Qed.

Program Definition RMod_exr {R : RingObject} (M N : RModObject R) :
  RMod_product M N ~{RMod R}~> N := {|
  rm_hom := Ab_exr M N
|}.
Next Obligation. intros R M N r p; reflexivity. Qed.

(** ** The two mediators *)

Program Definition RMod_pair {R : RingObject} {M N P : RModObject R}
  (f : P ~{RMod R}~> M) (g : P ~{RMod R}~> N) :
  P ~{RMod R}~> RMod_product M N := {|
  rm_hom := CMon_pair (rm_hom f) (rm_hom g)
|}.
Next Obligation.
  intros R M N P f g r a.
  split; simpl.
  - apply (rm_map_smul f).
  - apply (rm_map_smul g).
Qed.

(* The copairing (a, b) ↦ f a + g b.  Its action obligation is the one
   place [rm_smul_distr_l] is spent. *)
Program Definition RMod_copair {R : RingObject} {M N P : RModObject R}
  (f : M ~{RMod R}~> P) (g : N ~{RMod R}~> P) :
  RMod_product M N ~{RMod R}~> P := {|
  rm_hom := CMon_copair (rm_hom f) (rm_hom g)
|}.
Next Obligation.
  intros R M N P f g r p; simpl.
  rewrite (rm_map_smul f), (rm_map_smul g).
  symmetry.
  apply rm_smul_distr_l.
Qed.

(** ** The zero morphism of R-Mod is CMon's *)

(* What makes the two [zero_mor] laws transfer: [RMod_Zero]'s [one] and
   [zero] wrap [Ab_one] and [Ab_zero_hom] (Instance/Mod.v),
   which are [CMon_one] and [CMon_zero_hom], and the hom-setoid compares
   underlying maps. *)
Example rmod_zero_mor_is_cmon_zero_mor {R : RingObject}
  (M N : RModObject R) :
  rm_hom (@zero_mor (RMod R) (RMod_Zero R) M N)
    = @zero_mor CMon CMon_Zero M N := eq_refl.

Lemma rmod_zero_mor_value {R : RingObject} (M N : RModObject R)
  (a : carrier (cmon_setoid M)) :
  cmon_map (rm_hom (@zero_mor (RMod R) (RMod_Zero R) M N)) a
    ≈ cmon_zero N.
Proof.
  simpl.
  apply (cmon_map_zero (Ab_zero_hom N)).
Qed.

(** ** The four interaction laws, all four inherited on the nose *)

Definition RMod_exl_inl {R : RingObject} (M N : RModObject R) :
  RMod_exl M N ∘ RMod_inl M N ≈ id := CMon_exl_inl M N.

Definition RMod_exr_inr {R : RingObject} (M N : RModObject R) :
  RMod_exr M N ∘ RMod_inr M N ≈ id := CMon_exr_inr M N.

Definition RMod_exl_inr {R : RingObject} (M N : RModObject R) :
  RMod_exl M N ∘ RMod_inr M N ≈ @zero_mor (RMod R) (RMod_Zero R) N M :=
  CMon_exl_inr M N.

Definition RMod_exr_inl {R : RingObject} (M N : RModObject R) :
  RMod_exr M N ∘ RMod_inl M N ≈ @zero_mor (RMod R) (RMod_Zero R) M N :=
  CMon_exr_inl M N.

(** ** Both universal properties *)

(* The ∃!-package must be rebuilt — it quantifies over [RModHom], not over
   [CMonHom] — but every equation inside it is, after unfolding
   [RModHom_Setoid] and [rmod_hom_compose], the CMon equation about the
   same underlying maps.  So each proof cites the CMon original and adds
   nothing. *)
Definition RMod_is_product {R : RingObject} (M N P : RModObject R)
  (f : P ~{RMod R}~> M) (g : P ~{RMod R}~> N) :
  ∃! h : P ~{RMod R}~> RMod_product M N,
    (RMod_exl M N ∘ h ≈ f) ∧ (RMod_exr M N ∘ h ≈ g).
Proof.
  unshelve refine {| unique_obj := RMod_pair f g |}.
  - exact (unique_property
             (CMon_bi_is_product M N P (rm_hom f) (rm_hom g))).
  - intros v Hv.
    exact (uniqueness
             (CMon_bi_is_product M N P (rm_hom f) (rm_hom g))
             (rm_hom v) Hv).
Defined.

Definition RMod_is_coproduct {R : RingObject} (M N P : RModObject R)
  (f : M ~{RMod R}~> P) (g : N ~{RMod R}~> P) :
  ∃! h : RMod_product M N ~{RMod R}~> P,
    (h ∘ RMod_inl M N ≈ f) ∧ (h ∘ RMod_inr M N ≈ g).
Proof.
  unshelve refine {| unique_obj := RMod_copair f g |}.
  - exact (unique_property
             (CMon_bi_is_coproduct M N P (rm_hom f) (rm_hom g))).
  - intros v Hv.
    exact (uniqueness
             (CMon_bi_is_coproduct M N P (rm_hom f) (rm_hom g))
             (rm_hom v) Hv).
Defined.

(** ** The biproduct, and with it the product and coproduct structures *)

Definition RMod_Biproduct {R : RingObject} (M N : RModObject R) :
  @Biproduct (RMod R) (RMod_Zero R) M N :=
  @Build_Biproduct (RMod R) (RMod_Zero R) M N
    (RMod_product M N)
    (RMod_inl M N)
    (RMod_inr M N)
    (RMod_exl M N)
    (RMod_exr M N)
    (RMod_exl_inl M N)
    (RMod_exr_inr M N)
    (RMod_exl_inr M N)
    (RMod_exr_inl M N)
    (RMod_is_product M N)
    (RMod_is_coproduct M N).

#[export] Instance RMod_Biproducts (R : RingObject) :
  @HasBiproducts (RMod R) (RMod_Zero R) :=
  @Build_HasBiproducts (RMod R) (RMod_Zero R) (@RMod_Biproduct R).

#[export] Instance RMod_Cartesian (R : RingObject) : @Cartesian (RMod R) :=
  @biproduct_Cartesian (RMod R) (RMod_Zero R) (RMod_Biproducts R).

#[export] Instance RMod_Cocartesian (R : RingObject) :
  @Cocartesian (RMod R) :=
  @biproduct_Cocartesian (RMod R) (RMod_Zero R) (RMod_Biproducts R).

(** ** Strict identifications *)

Example RMod_coprod_is_prod (R : RingObject) (M N : RModObject R) :
  @Coprod (RMod R) (RMod_Cocartesian R) M N
    = @product_obj (RMod R) (RMod_Cartesian R) M N := eq_refl.

Example RMod_coprod_obj (R : RingObject) (M N : RModObject R) :
  @Coprod (RMod R) (RMod_Cocartesian R) M N = RMod_product M N := eq_refl.

(* The two roster entries agree: the underlying abelian group of the
   direct sum of modules IS the direct sum of the underlying groups, as
   built in Instance/Ab/Coproduct.v. *)
Example RMod_coprod_ab (R : RingObject) (M N : RModObject R) :
  rm_ab (@Coprod (RMod R) (RMod_Cocartesian R) M N)
    = Ab_product M N := eq_refl.

Example RMod_inl_is_Ab_inl (R : RingObject) (M N : RModObject R) :
  rm_hom (@inl (RMod R) (RMod_Cocartesian R) M N) = Ab_inl M N := eq_refl.

Example RMod_inr_is_Ab_inr (R : RingObject) (M N : RModObject R) :
  rm_hom (@inr (RMod R) (RMod_Cocartesian R) M N) = Ab_inr M N := eq_refl.

(** ** Non-vacuity over ℤ ⊕ ℤ as a ℤ-module *)

Definition zmod : RModObject Int_Ring := Ring_RMod Int_Ring.

Lemma rmod_coprod_injections_differ :
  cmon_map (rm_hom (@inl (RMod Int_Ring) (RMod_Cocartesian Int_Ring)
                         zmod zmod)) 1%Z
    ≈ cmon_map (rm_hom (@inr (RMod Int_Ring) (RMod_Cocartesian Int_Ring)
                             zmod zmod)) 1%Z → False.
Proof.
  intros [H _].
  simpl in H.
  discriminate H.
Qed.

Example rmod_coprod_merge_computes :
  cmon_map (rm_hom (@merge (RMod Int_Ring) (RMod_Cocartesian Int_Ring)
                           zmod zmod zmod id id)) (2%Z, 3%Z) = 5%Z :=
  eq_refl.

(* The action on the direct sum is componentwise, and computes. *)
Example rmod_coprod_smul_computes :
  rm_smul (RMod_product zmod zmod) 4%Z (2%Z, 3%Z) = (8%Z, 12%Z) := eq_refl.

Example rmod_coprod_exl_computes :
  cmon_map (rm_hom (RMod_exl zmod zmod)) (2%Z, 3%Z) = 2%Z := eq_refl.

Example rmod_coprod_exr_computes :
  cmon_map (rm_hom (RMod_exr zmod zmod)) (2%Z, 3%Z) = 3%Z := eq_refl.
