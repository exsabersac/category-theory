(*
   本文件为测试：ProbeQuotient479。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Coequalizer.Absolute.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Monad.Monadicity.Crude.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.Propositional.Full.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Coequalizer.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Quotient.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Category.Instance.Rng.Coequalizer.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.BeckObjects.
Require Import Category.Instance.Mon.Coproduct.
Require Import Category.Instance.Mon.Free.
Require Import Category.Instance.Mon.Word.
Require Import Category.Instance.Mon.Presentation.

Generalizable All Variables.

(* The instrument *)
Fail Definition p479_instrument : True := p479_absent_name.

(** ** Groups *)

Section GrpProbe.

Universe p.
Context {G : GrpObject@{p p p}} (N : NormalSubgroup G).
Context (T : Transversal N) (x : carrier G).

(* R1 *)
Fail Example p479_r1_law4 :
  grp_map (semidirect_d1 N) (scoeq_t (transversal_split N T) x)
    = transversal_map T x := eq_refl.

(* C1 *)
Example p479_c1_law4 :
  grp_map (semidirect_d1 N) (scoeq_t (transversal_split N T) x)
    ≈ transversal_map T x.
Proof. exact (scoeq_law4 (transversal_split N T) x). Qed.

(* C2 *)
Example p479_c2_t_snd :
  `1 (snd (scoeq_t (transversal_split N T) x))
    = grp_mul G (grp_inv G x) (transversal_map T x) := eq_refl.

(* C3 *)
Example p479_c3_desc {K : GrpObject@{p p p}} (h : G ~{Grp}~> K)
  (Hh : h ∘ semidirect_d0 N ≈ h ∘ semidirect_d1 N) (a : carrier G) :
  grp_map (unique_obj (coeq_desc (quot_proj_IsCoequalizer N) h Hh)) a
    = grp_map h a := eq_refl.

(* C4 *)
Example p479_c4_round_trip (a : carrier G) :
  transversal_map (split_transversal N (transversal_split N T)) a
    = transversal_map T a := eq_refl.

End GrpProbe.

(* 相关说明。 （已译） *)
Section GrpMembershipAbove.

Universes p m.
Constraint p < m.
Context {G : GrpObject@{p p p}} (N : NormalSubgroup@{m p p p} G).

(* R2 *)
Fail Definition p479_r2_pair := semidirect_d0 N.

(* C5 *)
Definition p479_c5_transversal (T : Transversal N) : CosetUntruncates N :=
  transversal_untruncates N T.

(* C14 *)
Definition p479_c14_sdp : GrpObject := SemidirectGrp N.

End GrpMembershipAbove.

(* Carriers above Set: Z/4's refutation is accepted there, the S3/A3
   splitting is refused. *)
Section AboveSet.

Universes u p.
Constraint Set < p.
Constraint p < u.

(* C6 *)
Definition p479_c6_Z4 :
  @SplitCoequalizer Grp@{u p} _ _ (semidirect_d0 Z4_two)
    (semidirect_d1 Z4_two) → False := Z4_two_not_split_in_Grp.

(* R3 *)
Fail Definition p479_r3_S3 :
  @SplitCoequalizer Grp@{u p} _ _ (semidirect_d0 A3) (semidirect_d1 A3)
  := S3_A3_Grp_split.

End AboveSet.

(* C7 *)
Definition p479_c7_S3 :
  SplitCoequalizer (semidirect_d0 A3) (semidirect_d1 A3) := S3_A3_Grp_split.

(** ** Rings *)

Section RngProbe.

Universe p.
Context {R : RingObject@{p p p}} (A : Ideal R).
Context (T : RTransversal A) (r : carrier (rig_setoid R)).

(* R4 *)
Fail Example p479_r4_law4 :
  rig_map (rsemidirect_d1 A) (scoeq_t (rtransversal_split A T) r)
    = rtransversal_map T r := eq_refl.

(* C8 *)
Example p479_c8_law4 :
  rig_map (rsemidirect_d1 A) (scoeq_t (rtransversal_split A T) r)
    ≈ rtransversal_map T r.
Proof. exact (scoeq_law4 (rtransversal_split A T) r). Qed.

(* C9 *)
Example p479_c9_mul_snd (q q' : carrier (rig_setoid (SemidirectRing A))) :
  `1 (snd (rig_mul (SemidirectRing A) q q'))
    = rig_add R (rig_add R (rig_mul R (fst q) (`1 (snd q')))
                           (rig_mul R (`1 (snd q)) (fst q')))
                (rig_mul R (`1 (snd q)) (`1 (snd q'))) := eq_refl.

End RngProbe.

Section RngMembershipAbove.

Universes p m.
Constraint p < m.
Context {R : RingObject@{p p p}} (A : Ideal@{m p p p} R).

(* R6 *)
Fail Definition p479_r6_pair := rsemidirect_d0 A.

(* C15 *)
Definition p479_c15_transversal (T : RTransversal A) : RCosetUntruncates A :=
  rtransversal_untruncates A T.

(* C16 *)
Definition p479_c16_sdp : RingObject := SemidirectRing A.

End RngMembershipAbove.

(* C10 *)
Example p479_c10_even (a : Z) :
  rtransversal_map EvenIdeal_transversal a = Z.modulo a 2 := eq_refl.

(*
   本节说明 ProbeQuotient479 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section MembershipBelow.

Universes p m.
Constraint m < p.

(* C17 *)
Definition p479_c17_readback {G : GrpObject@{p p p}}
  (N : NormalSubgroup@{m p p p} G) (T : Transversal N) :=
  transversal_split_e T.

(* C18 *)
Definition p479_c18_rreadback {R : RingObject@{p p p}}
  (A : Ideal@{m p p p} R) (T : RTransversal A) :=
  rtransversal_split_e T.

(* C19 *)
Definition p479_c19_untruncate {G : GrpObject@{p p p}}
  (N : NormalSubgroup@{m p p p} G)
  (U : ∀ P : Type@{m}, (∀ Q : Prop, (P → Q) → Q) → P) :
  CosetUntruncates N := choice_untruncates N (choice_of_untr U).

(* C20 *)
Definition p479_c20_untruncate
  (D : ∀ S : Type@{m}, CosetUntruncates (NS S)) :
  ∀ P : Type@{m}, (∀ Q : Prop, (P → Q) → Q) → P :=
  untr_of_choice (fun S => NS_untruncates_chooses S (D S)).

End MembershipBelow.

(** ** Monoids *)

Section MonProbe.

Universes o so.

Local Notation MonOS :=
  (@Mon@{so o so so} Sets@{o so} Sets_Product_Monoidal@{so o}).

Context (M : MonOS) (ww : list (list (mon_ob M))).

(* C11 *)
Example p479_c11_flatten :
  mon_fun (Mon_flatten M) ww = wconcat ww := eq_refl.

(* R5 *)
Fail Example p479_r5_evaluate :
  mon_fun (Mon_free_evaluate M) ww
    = wmap (fun w => mon_fun (Mon_evaluate M) w) ww := eq_refl.

(* C12 *)
Example p479_c12_evaluate :
  mon_fun (Mon_free_evaluate M) ww
    ≈ wmap (fun w => mon_fun (Mon_evaluate M) w) ww.
Proof.
  exact (free_mon_fmap_is_wmap (fmap[Mon_Forget] (Mon_evaluate M)) ww).
Qed.

(* C13 *)
Example p479_c13_s :
  scoeq_s (Mon_canonical_split M) = free_mon_insert (Mon_Forget M) := eq_refl.

End MonProbe.
