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

(* 相关说明。 （已译） *)

(*
 Book: Riehl, "Category Theory in Context" (2nd ed.), §3.1,
 Wikipedia: https://en.wikipedia.org/wiki/Direct_sum_of_modules

   本文件给出余积实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Coproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Obligation Tactic := idtac.

(* * ** The direct sum 对象 R-Mod （已译） *)

(* 相关说明。 （已译） *)
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

(* Each wraps corresponding 态射 Ab; single new obligation
 compatibility action. （已译） *)
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

(* 相关说明。 （已译） *)
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

(* * ** The zero 态射 R-Mod CMon's （已译） *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(* 相关说明。 （已译） *)

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

(*
   本节说明 Coproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(* 相关说明。 （已译） *)

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

(* 相关说明。 （已译） *)
Example RMod_coprod_ab (R : RingObject) (M N : RModObject R) :
  rm_ab (@Coprod (RMod R) (RMod_Cocartesian R) M N)
    = Ab_product M N := eq_refl.

Example RMod_inl_is_Ab_inl (R : RingObject) (M N : RModObject R) :
  rm_hom (@inl (RMod R) (RMod_Cocartesian R) M N) = Ab_inl M N := eq_refl.

Example RMod_inr_is_Ab_inr (R : RingObject) (M N : RModObject R) :
  rm_hom (@inr (RMod R) (RMod_Cocartesian R) M N) = Ab_inr M N := eq_refl.

(* 相关说明。 （已译） *)

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

(* 相关说明。 （已译） *)
Example rmod_coprod_smul_computes :
  rm_smul (RMod_product zmod zmod) 4%Z (2%Z, 3%Z) = (8%Z, 12%Z) := eq_refl.

Example rmod_coprod_exl_computes :
  cmon_map (rm_hom (RMod_exl zmod zmod)) (2%Z, 3%Z) = 2%Z := eq_refl.

Example rmod_coprod_exr_computes :
  cmon_map (rm_hom (RMod_exr zmod zmod)) (2%Z, 3%Z) = 3%Z := eq_refl.
