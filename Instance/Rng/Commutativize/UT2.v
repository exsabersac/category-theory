(*
 nLab: https://ncatlab.org/nlab/show/reflective+subcategory

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Algebras.
Require Import Category.Instance.Rng.Algebras.Associative.
Require Import Category.Instance.Rng.Quotient.
Require Import Category.Instance.Rng.Commutativize.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(* * ** UT2 not 对象 subcategory （已译） *)

Lemma UT2_not_commutative_ring@{a c p +} :
  IsCommutative (UT2 : RingObject@{a c p}) → False.
Proof. intro H; exact (UT2_not_commutative (H ut2_e11 ut2_e12)). Qed.

(* 相关说明。 （已译） *)

(* E12 = E11·E12 − E12·E11 is itself a commutator. *)
Example ut2_e12_commutator@{a c p +} :
  rcomm (UT2 : RingObject@{a c p}) ut2_e11 ut2_e12 = ut2_e12 := eq_refl.

Lemma ut2_e12_in_CommIdeal@{a c p +} :
  InCommIdeal (UT2 : RingObject@{a c p}) ut2_e12.
Proof. exact (@ici_gen UT2 ut2_e11 ut2_e12). Defined.

Lemma crng_unit_UT2_merges@{u p +} :
  rig_map (crng_unit (UT2 : Rng@{u p})) ut2_e12
    ≈ rig_map (crng_unit (UT2 : Rng@{u p})) ut2_zero.
Proof.
  simpl; unfold rquot_rel; constructor.
  exact (@ici_resp UT2 ut2_e12 _ eq_refl ut2_e12_in_CommIdeal).
Qed.

Lemma ut2_e12_nonzero@{a c p +} :
  @equiv (carrier (rig_setoid (UT2 : RingObject@{a c p}))) _ ut2_e12 ut2_zero
    → False.
Proof. unfold ut2_e12, ut2_zero; simpl; unfold ut2_eqT; discriminate. Qed.

(* 相关说明。 （已译） *)
Theorem crng_unit_UT2_not_iso@{u p +} :
  IsIsomorphism (crng_unit (UT2 : Rng@{u p})) → False.
Proof.
  intros [g _ Hgf].
  apply ut2_e12_nonzero.
  refine (transitivity (symmetry (Hgf ut2_e12)) _).
  refine (transitivity _ (Hgf ut2_zero)).
  exact (proper_morphism (rig_map g) _ _ crng_unit_UT2_merges).
Qed.

(* 相关说明。 （已译） *)

(* The top-left entry is a ring map into ℤ, which is commutative. *)
Definition ut2_diag1@{c +} (x : ut2@{c}) : Z := fst (fst x).

#[local] Obligation Tactic := idtac.

(* 相关说明。 （已译） *)
Definition ut2_diag1_proper@{+}
  : Proper (@equiv _ (is_setoid ut2_setoid_object)
              ==> @equiv _ (is_setoid Z_setoid_object)) ut2_diag1 :=
  fun x y H => f_equal ut2_diag1 H.

Program Definition ut2_diag1_hom@{u p +} :
  (UT2 : Rng@{u p}) ~{Rng@{u p}}~> Int_Ring := {|
  rig_map := {| morphism := ut2_diag1; proper_morphism := ut2_diag1_proper |}
|}.
Next Obligation. reflexivity. Qed.
Next Obligation. intros [[a b] c] [[a' b'] c']; reflexivity. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros [[a b] c] [[a' b'] c']; reflexivity. Qed.

(* Exercising 普遍性质 it separates one zero in
 quotient. （已译） *)
Example crng_UT2_med_one@{u p +} :
  rig_map `1 (unique_obj (crng_universal (UT2 : Rng@{u p}) Int_CRng
                            ut2_diag1_hom))
    (rig_one UT2) = 1%Z := eq_refl.

Theorem Commutativize_UT2_nonzero@{u p +} :
  @equiv (carrier (rig_setoid (Commutativize (UT2 : Rng@{u p})))) _
    (rig_one UT2) (rig_zero UT2) → False.
Proof.
  intro H.
  pose proof (proper_morphism
                (rig_map `1 (unique_obj
                               (crng_universal UT2 Int_CRng ut2_diag1_hom)))
                _ _ H) as E.
  simpl in E; discriminate E.
Qed.
