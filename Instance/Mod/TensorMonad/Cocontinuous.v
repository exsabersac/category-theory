(* * * R ⊗ (−) 左伴随: premises Riehl's Corollary 5.6.10 （已译） *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Continuity.
Require Import Category.Adjunction.Additive.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Structure.AbCategory.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Tensor.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.BaseChange.
Require Import Category.Instance.Mod.Coextension.
Require Import Category.Instance.Mod.TensorMonad.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/tensor-hom+adjunction
 nLab: https://ncatlab.org/nlab/show/monadic+functor
 nLab: https://ncatlab.org/nlab/show/created+limit

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The tensor–hom adjunction *)

(* Ab(R ⊗ A, B) ≅ Ab(A, Hom_ℤ(R, B)): extension of scalars, then
   coextension, composed. *)

Definition TensorF_left_adjoint@{c o x} (R : RingObject@{c c c}) :
  @Adjunction@{o c c o c c c c x c o} Ab@{o c} Ab@{o c}
    (TensorF@{c c c o x} R)
    (RMod_Forget_Ab@{x o o c c c} R ◯ Coextension@{c c c o x} R) :=
  Adjunction_Compose (zext_adjunction@{c c c o o x c c} R)
    (coex_adjunction@{c c c o x c} R).

Example TensorF_right_adjoint_obj@{c o x} (R : RingObject@{c c c})
  (B : obj[Ab@{o c}]) :
  fobj[RMod_Forget_Ab@{x o o c c c} R ◯ Coextension@{c c c o x} R] B
  = hom_ab Ab_AbEnriched (ring_ab R) B := eq_refl.

Example tensor_hom_to@{c o x} (R : RingObject@{c c c})
  (A B : obj[Ab@{o c}])
  (φ : fobj[TensorF@{c c c o x} R] A ~{Ab@{o c}}~> B)
  (a : carrier (cmon_setoid A)) (r : carrier (rig_setoid (ring_rig R))) :
  @cmon_map (ab_cmon (ring_ab R)) (ab_cmon B)
    (cmon_map (to (@adj _ _ _ _ (TensorF_left_adjoint@{c o x} R) A B) φ) a)
    r
  = cmon_map φ (@ts_gen (ring_ab R) A
                  (rig_mul (ring_rig R) r (rig_one (ring_rig R))) a)
  := eq_refl.

Lemma tensor_hom_to_gen@{c o x} (R : RingObject@{c c c})
  (A B : obj[Ab@{o c}])
  (φ : fobj[TensorF@{c c c o x} R] A ~{Ab@{o c}}~> B)
  (a : carrier (cmon_setoid A)) (r : carrier (rig_setoid (ring_rig R))) :
  @cmon_map (ab_cmon (ring_ab R)) (ab_cmon B)
    (cmon_map (to (@adj _ _ _ _ (TensorF_left_adjoint@{c o x} R) A B) φ) a)
    r
  ≈ cmon_map φ (@ts_gen (ring_ab R) A r a).
Proof.
  apply (proper_morphism (cmon_map φ)).
  exact (@te_gen (ring_ab R) A _ _ _ _
           (rig_mul_one_r (ring_rig R) r) (reflexivity a)).
Qed.

Example tensor_hom_from@{c o x} (R : RingObject@{c c c})
  (A B : obj[Ab@{o c}])
  (ψ : A ~{Ab@{o c}}~>
         fobj[RMod_Forget_Ab@{x o o c c c} R ◯ Coextension@{c c c o x} R] B)
  (a : carrier (cmon_setoid A)) (r : carrier (rig_setoid (ring_rig R))) :
  cmon_map (from (@adj _ _ _ _ (TensorF_left_adjoint@{c o x} R) A B) ψ)
    (@ts_gen (ring_ab R) A r a)
  = @cmon_map (ab_cmon (ring_ab R)) (ab_cmon B) (cmon_map ψ a)
      (rig_mul (ring_rig R) (rig_one (ring_rig R)) r) := eq_refl.

Lemma tensor_hom_from_gen@{c o x} (R : RingObject@{c c c})
  (A B : obj[Ab@{o c}])
  (ψ : A ~{Ab@{o c}}~>
         fobj[RMod_Forget_Ab@{x o o c c c} R ◯ Coextension@{c c c o x} R] B)
  (a : carrier (cmon_setoid A)) (r : carrier (rig_setoid (ring_rig R))) :
  cmon_map (from (@adj _ _ _ _ (TensorF_left_adjoint@{c o x} R) A B) ψ)
    (@ts_gen (ring_ab R) A r a)
  ≈ @cmon_map (ab_cmon (ring_ab R)) (ab_cmon B) (cmon_map ψ a) r.
Proof.
  apply (proper_morphism
           (@cmon_map (ab_cmon (ring_ab R)) (ab_cmon B) (cmon_map ψ a))).
  exact (rig_mul_one_l (ring_rig R) r).
Qed.

(* * ** The square 单子 左伴随 （已译） *)

Definition TensorF2_left_adjoint@{c o x} (R : RingObject@{c c c}) :
  @Adjunction@{o c c o c c c c x c o} Ab@{o c} Ab@{o c}
    (TensorF@{c c c o x} R ◯ TensorF@{c c c o x} R)
    ((RMod_Forget_Ab@{x o o c c c} R ◯ Coextension@{c c c o x} R)
       ◯ (RMod_Forget_Ab@{x o o c c c} R ◯ Coextension@{c c c o x} R)) :=
  Adjunction_Compose (TensorF_left_adjoint@{c o x} R)
    (TensorF_left_adjoint@{c o x} R).

(* 相关说明。 （已译） *)

(* Left adjoints preserve colimits: Riehl's Theorem 4.6.2, here
   Adjunction/Continuity.v. *)

Definition TensorF_cocontinuous@{c o x t l l0 s} (R : RingObject@{c c c}) :
  CocontinuousFunctor@{t l l l0 l s c o o x} (TensorF@{c c c o x} R) :=
  left_adjoint_Cocontinuous@{t l l l0 l x c o s o o c}
    (TensorF_left_adjoint@{c o x} R).

Definition TensorF2_cocontinuous@{c o x t l l0 s} (R : RingObject@{c c c}) :
  CocontinuousFunctor@{t l l l0 l s c o o x}
    (TensorF@{c c c o x} R ◯ TensorF@{c c c o x} R) :=
  left_adjoint_Cocontinuous@{t l l l0 l x c o s o o c}
    (TensorF2_left_adjoint@{c o x} R).

Definition TensorF_preserves_colimits@{c o x t l l0 s}
  (R : RingObject@{c c c}) :
  PreservesAllColimits@{t l x l0 s o c o} (TensorF@{c c c o x} R) :=
  left_adjoint_preserves_colimits@{t l x l0 o c t o s c o}
    (TensorF_left_adjoint@{c o x} R).

Definition TensorF2_preserves_colimits@{c o x t l l0 s}
  (R : RingObject@{c c c}) :
  PreservesAllColimits@{t l x l0 s o c o}
    (TensorF@{c c c o x} R ◯ TensorF@{c c c o x} R) :=
  left_adjoint_preserves_colimits@{t l x l0 o c t o s c o}
    (TensorF2_left_adjoint@{c o x} R).

(* * ** The forgetful 函子 against U^T ◯ K （已译） *)

(* EM_Forget ◯ EM_Comparison agrees U 对象 arrows the
 nose, isomorphic it 恒等 components. （已译） *)

Example rmod_forget_comparison_obj@{a c p o x} (R : RingObject@{a c p})
  (M : obj[RMod@{o x a p c} R]) :
  fobj[EM_Forget (TensorF@{a c p o x} R)
         ◯ EM_Comparison (zext_adjunction@{a c p o o x a a} R)] M
  = fobj[RMod_Forget_Ab@{x o o a p c} R] M := eq_refl.

Example rmod_forget_comparison_map@{a c p o x} (R : RingObject@{a c p})
  (M N : obj[RMod@{o x a p c} R]) (f : M ~{RMod@{o x a p c} R}~> N) :
  fmap[EM_Forget (TensorF@{a c p o x} R)
         ◯ EM_Comparison (zext_adjunction@{a c p o o x a a} R)] f
  = fmap[RMod_Forget_Ab@{x o o a p c} R] f := eq_refl.

Definition rmod_forget_comparison@{a c p o x} (R : RingObject@{a c p}) :
  EM_Forget (TensorF@{a c p o x} R)
    ◯ EM_Comparison (zext_adjunction@{a c p o o x a a} R)
  ≈ RMod_Forget_Ab@{x o o a p c} R.
Proof.
  exists (fun M => @iso_id Ab@{o c} (fobj[RMod_Forget_Ab@{x o o a p c} R] M)).
  intros M N f.
  simpl. intros m. reflexivity.
Defined.
