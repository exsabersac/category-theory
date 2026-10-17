(* 相关说明。 （已译） *)

Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import Coq.Vectors.Fin.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Matr.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.FdVect.DoubleDual.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 nLab:      https://ncatlab.org/nlab/show/natural+isomorphism

   本文件给出非自然情形。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Definition Q1 : FdVectObject Q_Field := StdVect Q_Field 1.

(* The basis vector of ℚ¹. *)
Definition e1 : carrier (cmon_setoid (fdv_mod Q1)) :=
  std_basis Q_Field 1 Fin.F1.

(* Scaling fixed rational, 态射 FdVect ℚ, written
 through abstract rig interface so every obligation rig
 law (the house idiom Instance/FdVect.v's std layer). （已译） *)
Definition qscale (c : Q) : Q1 ~{FdVect Q_Field}~> Q1.
Proof.
  unshelve notypeclasses refine
    (@Build_RModHom (field_ring Q_Field) (fdv_mod Q1) (fdv_mod Q1)
       (@Build_CMonHom (std_cmon Q_Field 1) (std_cmon Q_Field 1)
          (@Build_SetoidMorphism _ _ _ _
             (fun v i => rig_mul Q_Field c (v i)) _) _ _)
       _).
  - intros v w Hvw i.
    apply rig_mul_respects; [ reflexivity | exact (Hvw i) ].
  - intro i; apply rig_mul_zero_r.
  - intros v w i; apply rig_distr_l.
  - intros r v i.
    etransitivity;
      [ symmetry; apply rig_mul_assoc | ].
    etransitivity;
      [ apply rig_mul_respects;
        [ apply (field_comm Q_Field c r) | reflexivity ] | ].
    apply rig_mul_assoc.
Defined.

(* 2 · ½ ≈ 1 and ½ · 2 ≈ 1 in ℚ, by computation. *)
Lemma two_half_one : (2 * / 2 == 1)%Q.
Proof. reflexivity. Qed.

Lemma half_two_one : (/ 2 * 2 == 1)%Q.
Proof. reflexivity. Qed.

(* v ↦ 2·v is an automorphism of ℚ¹, with inverse v ↦ ½·v. *)
Program Definition alpha2 : @Isomorphism (FdVect Q_Field) Q1 Q1 := {|
  to   := qscale 2;
  from := qscale (/ 2)
|}.
Next Obligation.
  intros v i.
  etransitivity; [ symmetry; apply rig_mul_assoc | ].
  etransitivity;
    [ apply rig_mul_respects; [ apply two_half_one | reflexivity ] | ].
  apply rig_mul_one_l.
Qed.
Next Obligation.
  intros v i.
  etransitivity; [ symmetry; apply rig_mul_assoc | ].
  etransitivity;
    [ apply rig_mul_respects; [ apply half_two_one | reflexivity ] | ].
  apply rig_mul_one_l.
Qed.

(* 相关说明。 （已译） *)
Lemma q_one_neq_zero : (1 == 0)%Q → False.
Proof.
  intro H; discriminate H.
Qed.

(* The arithmetic heart: 2q ≈ ½q in ℚ forces q ≈ 0. *)
Lemma q_two_half_zero (q : Q) :
  (2 * q == / 2 * q)%Q → (q == 0)%Q.
Proof.
  change (/ 2)%Q with (1 # 2)%Q.
  intro H; lra.
Qed.

(* 相关说明。 （已译） *)
Lemma qscale_smul (c : Q) (v : carrier (cmon_setoid (fdv_mod Q1))) :
  cmon_map (rm_hom (qscale c)) v ≈ rm_smul (fdv_mod Q1) c v.
Proof.
  intro i; reflexivity.
Qed.

(* Every vector of ℚ¹ is its first coordinate times e₁. *)
Lemma q1_expand (w : carrier (cmon_setoid (fdv_mod Q1))) :
  w ≈ rm_smul (fdv_mod Q1) (w Fin.F1) e1.
Proof.
  intro i.
  pattern i; apply (Fin.caseS' i); [ | intro j; inversion j ].
  symmetry.
  etransitivity;
    [ apply rig_mul_respects; [ reflexivity | apply delta_refl ] | ].
  apply rig_mul_one_r.
Qed.

(** ** The violation *)

Section Violation.

Context (s0 : @Isomorphism (FdVect Q_Field) Q1 (DualFdObj Q_Field Q1)).

(*
   本节说明 NonNatural 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Context (Hnat :
  cmon_map (rm_hom (cmon_map (rm_hom (to s0))
                      (cmon_map (rm_hom (qscale 2)) e1))) e1
    ≈ cmon_map (rm_hom (cmon_map (rm_hom (to s0)) e1))
        (cmon_map (rm_hom (qscale (/ 2))) e1)).

Let s : Q1 ~{FdVect Q_Field}~> DualFdObj Q_Field Q1 := to s0.

Let q : Q := cmon_map (rm_hom (cmon_map (rm_hom s) e1)) e1.

(* 相关说明。 （已译） *)
Lemma sigma_two :
  cmon_map (rm_hom (cmon_map (rm_hom s)
                      (cmon_map (rm_hom (qscale 2)) e1))) e1
    ≈ (2 * q)%Q.
Proof using Type.
  transitivity
    (cmon_map (rm_hom (cmon_map (rm_hom s)
                         (rm_smul (fdv_mod Q1) 2 e1))) e1).
  - exact (proper_morphism (cmon_map (rm_hom s)) _ _
             (qscale_smul 2 e1) e1).
  - exact (rm_map_smul s 2 e1 e1).
Qed.

(* Right side square at (e₁, e₁): homogeneity the
 functional σ(e₁) — [RModHom] 进入 ring-as-module, whose
 action multiplication — gives ½q. （已译） *)
Lemma sigma_half :
  cmon_map (rm_hom (cmon_map (rm_hom s) e1))
    (cmon_map (rm_hom (qscale (/ 2))) e1)
    ≈ (/ 2 * q)%Q.
Proof using Type.
  transitivity
    (cmon_map (rm_hom (cmon_map (rm_hom s) e1))
       (rm_smul (fdv_mod Q1) (/ 2) e1)).
  - apply (proper_morphism (cmon_map (rm_hom (cmon_map (rm_hom s) e1)))).
    apply qscale_smul.
  - exact (rm_map_smul (cmon_map (rm_hom s) e1) (/ 2)%Q e1).
Qed.

(* 相关说明。 （已译） *)
Lemma q_zero : (q == 0)%Q.
Proof using Hnat.
  apply q_two_half_zero.
  transitivity
    (cmon_map (rm_hom (cmon_map (rm_hom s)
                         (cmon_map (rm_hom (qscale 2)) e1))) e1).
  - symmetry; exact sigma_two.
  - transitivity
      (cmon_map (rm_hom (cmon_map (rm_hom s) e1))
         (cmon_map (rm_hom (qscale (/ 2))) e1)).
    + exact Hnat.
    + exact sigma_half.
Qed.

(* Hence σ(e₁) is the zero functional. *)
Lemma sigma_e1_zero (w : carrier (cmon_setoid (fdv_mod Q1))) :
  cmon_map (rm_hom (cmon_map (rm_hom s) e1)) w ≈ 0%Q.
Proof using Hnat.
  transitivity
    (cmon_map (rm_hom (cmon_map (rm_hom s) e1))
       (rm_smul (fdv_mod Q1) (w Fin.F1) e1)).
  - apply (proper_morphism (cmon_map (rm_hom (cmon_map (rm_hom s) e1)))).
    apply q1_expand.
  - transitivity ((w Fin.F1) * q)%Q.
    + exact (rm_map_smul (cmon_map (rm_hom s) e1) (w Fin.F1) e1).
    + etransitivity;
        [ apply rig_mul_respects; [ reflexivity | exact q_zero ] | ].
      apply rig_mul_zero_r.
Qed.

(* σ identifies e₁ 0, so — σ being 同构 — e₁ ≈ 0 in
 ℚ¹, coordinate 1 collapse reads 1 ≈ 0 ℚ. （已译） *)
Theorem sigma_square_violation : False.
Proof using s0 Hnat.
  apply q_one_neq_zero.
  assert (He : e1 ≈ cmon_zero (std_cmon Q_Field 1)).
  { transitivity
      (cmon_map (rm_hom (from s0)) (cmon_map (rm_hom (to s0)) e1)).
    - intro i; symmetry; exact (iso_from_to s0 e1 i).
    - transitivity
        (cmon_map (rm_hom (from s0))
           (cmon_zero (DualMod Q_Field (fdv_mod Q1)))).
      + apply (proper_morphism (cmon_map (rm_hom (from s0)))).
        intro w.
        etransitivity; [ exact (sigma_e1_zero w) | ].
        reflexivity.
      + exact (cmon_map_zero (rm_hom (from s0))). }
  exact (He Fin.F1).
Qed.

End Violation.

(* The packaged negative half, STRONG form: no 同构
 ℚ¹ ≅ (ℚ¹)* satisfies even single point (e₁, e₁) the
 pointwise 自然性 square at automorphism 2·(−). （已译） *)
Theorem sigma_not_natural
        (s0 : @Isomorphism (FdVect Q_Field) Q1 (DualFdObj Q_Field Q1)) :
  cmon_map (rm_hom (cmon_map (rm_hom (to s0))
                      (cmon_map (rm_hom (qscale 2)) e1))) e1
    ≈ cmon_map (rm_hom (cmon_map (rm_hom (to s0)) e1))
        (cmon_map (rm_hom (qscale (/ 2))) e1) →
  False.
Proof.
  intro Hnat.
  exact (sigma_square_violation s0 Hnat).
Qed.

(* 相关说明。 （已译） *)
Lemma sigma_square_pointwise
      (s0 : @Isomorphism (FdVect Q_Field) Q1 (DualFdObj Q_Field Q1)) :
  (to s0 ∘ to alpha2 ≈ fmap[DualFd Q_Field] (from alpha2) ∘ to s0) →
  ∀ v w,
    cmon_map (rm_hom (cmon_map (rm_hom (to s0))
                        (cmon_map (rm_hom (qscale 2)) v))) w
      ≈ cmon_map (rm_hom (cmon_map (rm_hom (to s0)) v))
          (cmon_map (rm_hom (qscale (/ 2))) w).
Proof.
  intros H v w.
  exact (H v w).
Qed.

(* Hence the categorical reading is refuted too. *)
Corollary sigma_categorical_not_natural
          (s0 : @Isomorphism (FdVect Q_Field) Q1 (DualFdObj Q_Field Q1)) :
  (to s0 ∘ to alpha2 ≈ fmap[DualFd Q_Field] (from alpha2) ∘ to s0) →
  False.
Proof.
  intro H.
  exact (sigma_not_natural s0 (sigma_square_pointwise s0 H e1 e1)).
Qed.

(*
   本节说明 NonNatural 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary sigma_family_not_natural
          (σ : ∀ V : FdVectObject Q_Field,
                 @Isomorphism (FdVect Q_Field) V (DualFdObj Q_Field V)) :
  cmon_map (rm_hom (cmon_map (rm_hom (to (σ Q1)))
                      (cmon_map (rm_hom (qscale 2)) e1))) e1
    ≈ cmon_map (rm_hom (cmon_map (rm_hom (to (σ Q1))) e1))
        (cmon_map (rm_hom (qscale (/ 2))) e1) →
  False.
Proof.
  intro Hnat.
  exact (sigma_not_natural (σ Q1) Hnat).
Qed.

(*
   本节说明hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition family_premise_inhabited (V : FdVectObject Q_Field) :
  @Isomorphism (FdVect Q_Field) V (DualFdObj Q_Field V).
Proof.
  unshelve refine {| to := _; from := _ |}.
  - exact (to (fd_dual_pointwise_iso Q_Field V)).
  - exact (from (fd_dual_pointwise_iso Q_Field V)).
  - exact (iso_to_from (fd_dual_pointwise_iso Q_Field V)).
  - exact (iso_from_to (fd_dual_pointwise_iso Q_Field V)).
Defined.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition family_not_natural_applies :=
  sigma_family_not_natural family_premise_inhabited.
