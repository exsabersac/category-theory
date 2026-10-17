(*
   本文件给出 Tensor 相关定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Coq.QArith.QArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Universal.Element.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 nLab:      https://ncatlab.org/nlab/show/tensor+product
 nLab:      https://ncatlab.org/nlab/show/universal+element
 Wikipedia: https://en.wikipedia.org/wiki/Tensor_product
 Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
 Book: Riehl, Category Theory in Context, Dover 2016, §2.3, printed

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section VectTensor.

Context (F : FieldObject).

(** ** Bilinear maps of vector spaces *)

(** The bilinear maps V × V' → W, at the vector-space level.  This is
    Instance/Mod/Tensor.v's [RBilinear] read through
    [Vct_F F = RMod (field_ring F)]. *)
Definition VctBilinear (V V' W : Vct_F F) : Type := RBilinear V V' W.

Example VctBilinear_is_RBilinear (V V' W : Vct_F F) :
  VctBilinear V V' W = RBilinear V V' W := eq_refl.

(** The bilinear-maps FUNCTOR Bilin(V, V'; −) : Vct_F F ⟶ Sets. *)
Definition VctBilin (V V' : Vct_F F) : Vct_F F ⟶ Sets := Bilin V V'.

(** ** The tensor product, and its canonical bilinear map *)

Definition VctTensor (V V' : Vct_F F) : Vct_F F := TensorMod V V'.

Definition vct_tensor_gen (V V' : Vct_F F) :
  VctBilinear V V' (VctTensor V V') := tensor_gen.

(** ** Mac Lane §III.1 / Riehl §2.3: ⟨V ⊗ V', ⊗⟩ is a universal element

    For every vector space W and every bilinear map β : V × V' → W there
    is one and only one linear map V ⊗ V' ⟶ W carrying ⊗ to β. *)
Definition vct_tensor_universal_element (V V' : Vct_F F) :
  AUniversalElement (VctBilin V V') (VctTensor V V') :=
  tensor_universal_element V V'.

(** The same data as Mac Lane's pair ⟨r, e⟩. *)
Definition vct_tensor_UniversalElement (V V' : Vct_F F) :
  UniversalElement (VctBilin V V') := tensor_UniversalElement V V'.

Example vct_tensor_UniversalElement_obj (V V' : Vct_F F) :
  @ue_obj (Vct_F F) (VctBilin V V') (vct_tensor_UniversalElement V V')
    = VctTensor V V' := eq_refl.

(** ** Unique factorization, elementwise *)

Definition vct_tensor_factor {V V' W : Vct_F F} (β : VctBilinear V V' W) :
  VctTensor V V' ~{Vct_F F}~> W := tensor_factor β.

Lemma vct_tensor_factor_commutes {V V' W : Vct_F F} (β : VctBilinear V V' W)
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  cmon_map (rm_hom (vct_tensor_factor β)) (mt_gen v w) ≈ rbl_map β v w.
Proof. exact (tensor_factor_commutes β v w). Qed.

Lemma vct_tensor_factor_unique {V V' W : Vct_F F} (β : VctBilinear V V' W)
  (k : VctTensor V V' ~{Vct_F F}~> W) :
  (∀ (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')),
      cmon_map (rm_hom k) (mt_gen v w) ≈ rbl_map β v w) →
  vct_tensor_factor β ≈ k.
Proof. exact (tensor_factor_unique β k). Qed.

(** ** What commutativity buys

    The engine file's collapse identity, at a field: its conclusion
    already follows from [field_comm], with no bilinear map in sight, so
    over a field it says nothing.  That is the precise sense in which the
    construction above is the classical tensor product of vector
    spaces. *)
Lemma vct_commutator_vacuous (W : Vct_F F)
  (r s : carrier (rig_setoid (ring_rig (field_ring F))))
  (x : carrier (cmon_setoid W)) :
  rm_smul W (rig_mul (ring_rig (field_ring F)) r s) x
    ≈ rm_smul W (rig_mul (ring_rig (field_ring F)) s r) x.
Proof.
  exact (rbl_commutator_from_commutativity (field_comm F) W r s x).
Qed.

End VectTensor.

Arguments VctBilinear {F} V V' W.
Arguments VctBilin {F} V V'.
Arguments VctTensor {F} V V'.
Arguments vct_tensor_gen {F} V V'.
Arguments vct_tensor_universal_element {F} V V'.
Arguments vct_tensor_UniversalElement {F} V V'.
Arguments vct_tensor_factor {F V V' W} β.

(** ** Non-degeneracy over ℚ

    The field as a one-dimensional space over itself, with multiplication
    as the archetypal bilinear map — the ℤ measurements of
    Instance/Mod/Tensor.v repeated over a scalar setoid whose [≈] is a
    genuine quotient. *)

Definition Q_Vct : Vct_F Q_Field := Ring_RMod (field_ring Q_Field).

(* Index arguments supplied once, as NOTATIONS (so each unfolds to the
   constructor itself) — the device Instance/Mod/Free.v uses. *)
Local Notation qgen  := (@mt_gen (field_ring Q_Field) Q_Vct Q_Vct).
Local Notation qzero := (@mt_zero (field_ring Q_Field) Q_Vct Q_Vct).
Local Notation qsmul := (@mt_smul (field_ring Q_Field) Q_Vct Q_Vct).

Definition Q_mul_bilinear : VctBilinear Q_Vct Q_Vct Q_Vct.
Proof.
  unshelve notypeclasses refine
    (@Build_RBilinear (field_ring Q_Field) Q_Vct Q_Vct Q_Vct Qmult
       _ _ _ _ _).
  - (* rbl_respects *)
    intros a b Hab c d Hcd; simpl in *.
    now rewrite Hab, Hcd.
  - (* rbl_add_l *)
    intros v v' w; simpl; ring.
  - (* rbl_add_r *)
    intros v w w'; simpl; ring.
  - (* rbl_smul_l *)
    intros r v w; simpl; ring.
  - (* rbl_smul_r: the clause that spends commutativity of ℚ *)
    intros r v w; simpl; ring.
Defined.

(** The factorization computes: the mediator is a fixpoint, so its value
    on a closed generator reduces — up to [≈], which here is [Qeq] and so
    is a genuine quotient step rather than a syntactic identity. *)
Example q_tensor_med_computes :
  cmon_map (rm_hom (tensor_med Q_mul_bilinear)) (qgen (1#2) (4#1)) ≈ 2.
Proof. reflexivity. Qed.

Example q_tensor_factor_computes :
  cmon_map (rm_hom (vct_tensor_factor Q_mul_bilinear)) (qgen (1#2) (4#1)) ≈ 2.
Proof. reflexivity. Qed.

(** The quotient does not collapse, proved by mapping OUT through
    [tensor_med_respects]. *)
Lemma q_tensor_gen_nonzero : mt_eq (qgen 1 1) qzero → False.
Proof.
  intro He.
  pose proof (tensor_med_respects Q_mul_bilinear _ _ He) as Hq.
  simpl in Hq; unfold Qeq in Hq; simpl in Hq.
  discriminate Hq.
Qed.

(** The scalars really are ℚ: a proper fraction gives a generator
    distinct from the one at 1 — the counterpart of
    Instance/Vect/Free.v's [free_vect_half_not_one], and the one place
    below where a non-integer scalar does work. *)
Lemma q_tensor_half_distinct : mt_eq (qgen (1#2) 1) (qgen 1 1) → False.
Proof.
  intro He.
  pose proof (tensor_med_respects Q_mul_bilinear _ _ He) as Hq.
  simpl in Hq; unfold Qeq in Hq; simpl in Hq.
  discriminate Hq.
Qed.

(** The same fraction in SCALAR position.  The first is the action rule
    at r = ½ (the product ½·1 reducing to the term [1#2], so the
    statement typechecks by conversion); the second says the action of ½
    genuinely moves the generator, which is what makes the scalar side of
    the module structure non-degenerate over a field rather than merely
    over its prime subring. *)
Lemma q_tensor_smul_half : mt_eq (qsmul (1#2) (qgen 1 1)) (qgen (1#2) 1).
Proof.
  exact (@mte_act_l (field_ring Q_Field) Q_Vct Q_Vct (1#2) 1 1).
Qed.

Lemma q_tensor_smul_half_moves : mt_eq (qsmul (1#2) (qgen 1 1)) (qgen 1 1) → False.
Proof.
  intro He.
  pose proof (tensor_med_respects Q_mul_bilinear _ _ He) as Hq.
  simpl in Hq; unfold Qeq in Hq; simpl in Hq.
  discriminate Hq.
Qed.

(** ℚ ⊗_ℚ ℚ ≅ ℚ in [Vct_F Q_Field], by the same two legs as the ℤ case:
    multiplication one way, q ↦ q ⊗ 1 the other. *)
Program Definition q_tensor_unit :
  Q_Vct ~{Vct_F Q_Field}~> VctTensor Q_Vct Q_Vct := {|
  rm_hom := {| cmon_map := {|
    morphism        := fun q => qgen q 1;
    proper_morphism := fun a b Hab => mte_gen Hab (reflexivity 1) |} |}
|}.
Next Obligation.
  exact (@tensor_zero_l (field_ring Q_Field) Q_Vct Q_Vct 1).
Qed.
Next Obligation.
  intros a b; exact (@mte_add_l (field_ring Q_Field) Q_Vct Q_Vct a b 1).
Qed.
Next Obligation.
  intros r q;
    exact (mte_sym (@mte_act_l (field_ring Q_Field) Q_Vct Q_Vct r q 1)).
Qed.

Program Definition Q_tensor_iso :
  @Isomorphism (Vct_F Q_Field) (VctTensor Q_Vct Q_Vct) Q_Vct := {|
  to   := tensor_med Q_mul_bilinear;
  from := q_tensor_unit
|}.
Next Obligation.
  intro q; simpl; apply Qmult_1_r.
Qed.
Next Obligation.
  refine (tensor_hom_ext
            (q_tensor_unit ∘ tensor_med Q_mul_bilinear)
            (@id (Vct_F Q_Field) (VctTensor Q_Vct Q_Vct)) _).
  intros v w; simpl.
  (* (v·w) ⊗ 1 ≈ (w·v) ⊗ 1 ≈ w·(v ⊗ 1) ≈ v ⊗ (w·1) ≈ v ⊗ w. *)
  refine (mte_trans (@mte_gen (field_ring Q_Field) Q_Vct Q_Vct _ _ _ _
                       (Qmult_comm v w) (reflexivity 1)) _).
  refine (mte_trans
            (mte_sym (@mte_act_l (field_ring Q_Field) Q_Vct Q_Vct w v 1)) _).
  refine (mte_trans (@mte_act_r (field_ring Q_Field) Q_Vct Q_Vct w v 1) _).
  exact (@mte_gen (field_ring Q_Field) Q_Vct Q_Vct _ _ _ _
           (reflexivity v) (Qmult_1_r w)).
Qed.
