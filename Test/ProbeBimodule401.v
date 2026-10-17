Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Adjunction.Parameter.
Require Import Category.Adjunction.Additive.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Continuity.
Require Import Category.Adjunction.Right.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Structure.AbCategory.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Mod.Bimodule.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本文件为测试：ProbeBimodule401。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* --------------------------------------------------------------- *)
(* INSTRUMENT.  A passing [Fail] prints nothing under this repo's    *)
(* 相关说明。 （已译） *)
(* --------------------------------------------------------------- *)

Fail Check p401_no_such_constant_anywhere.

(* --------------------------------------------------------------- *)
(* GUARD BLOCK.  Every constant that any negative below names is     *)
(* named here OUTSIDE every [Fail], so that renaming one of them     *)
(* breaks this file at a [Check] line rather than turning a negative *)
(* vacuously green.                                                  *)
(* --------------------------------------------------------------- *)

Check @Category.
Check @Functor.
Check @Adjunction.
Check @Isomorphism.
Check @eq.
Check @obj.
Check @hom.
Check @id.
Check @compose.
Check @Compose.

Check @RingObject.
Check @Ring_op.
Check @RModObject.
Check @RModHom.
Check @RMod.
Check @ModR.
Check @Bimodule.
Check @Build_Bimodule.
Check @bm_left.
Check @bimodule_right_RMod.
Check @rm_ab.
Check @rm_smul.
Check @Int_Ring.
Check @Int_Bimodule.
Check @Ring_RMod.
Check @TensorMod.
Check @RBilinear.
Check @AbEnriched.
Check @hom_ab.
Check @Ab_AbEnriched.

Check @BalTensor.
Check @BalBiadditive.
Check @bs_gen.
Check @be_balance.
Check @bal_med.
Check @bal_hom_ext.
Check @RTensor.
Check @TensorWith.
Check @HomSObj.
Check @HomS.
Check @bimodule_tensor_hom_adjunction.
Check @BimodCat.
Check @BimodHom.
Check @BimodTensor.
Check @bimodule_parametrized_adjunction.
Check @bimodule_hom_bifunctor.
Check @RMod_AbEnriched.

Check @LTensor.
Check @LTensorWith.
Check @LHomSObj.
Check @LHomS.
Check @bimodule_left_tensor_hom_adjunction.
Check @bimodule_left_tensor_preserves_colimits.
Check @bimodule_tensor_preserves_colimits.
Check @PreservesAllColimits.

Check @BimodTensorBimod.
Check @btb_left.
Check @btb_right.
Check @bimodule_adjunction_composite.
Check @tensor_assoc_iso.
Check @ta_to.
Check @ta_from.
Check @ta_iso.
Check @adjunction_along_left_iso.
Check @aali_cell.
Check @bimodule_tensor_bimod_adjunction.
Check @bimodule_hom_composite_iso.

Check @HomAbBimod.
Check @HomAbFunctor.
Check @hab_partial_adj.
Check @bimodule_mirror_family.
Check @bimodule_two_variable_adjunction.
Check @bimodule_third_leg.
Check @mr_left.
Check @mr_right.
Check @mirror_family.
Check @mutually_right_adjoint.
Check @AdjointOnTheRight.
Check @Swap.
Check @Partial_r.
Check @Partial_l.

Check @ZRight.
Check @int_mult_bal.
Check @int_tensor_separates.

(* ================================================================= *)
(* (1) N1-N2.  [Ring_op] is not strictly involutive, so the two       *)
(* 相关说明。 （已译） *)
(*     nose.  Both are CONVERSION.                                    *)
(* ================================================================= *)

Section P401RingOp.

Context (R : RingObject).

(* CONTROLS: all six DATA fields of the double opposite DO agree. *)
Example p401_op_setoid :
  rig_setoid (ring_rig (Ring_op (Ring_op R))) = rig_setoid (ring_rig R)
  := eq_refl.
Example p401_op_add :
  rig_add (ring_rig (Ring_op (Ring_op R))) = rig_add (ring_rig R)
  := eq_refl.
Example p401_op_one :
  rig_one (ring_rig (Ring_op (Ring_op R))) = rig_one (ring_rig R)
  := eq_refl.
Example p401_op_zero :
  rig_zero (ring_rig (Ring_op (Ring_op R))) = rig_zero (ring_rig R)
  := eq_refl.
Example p401_op_mul :
  rig_mul (ring_rig (Ring_op (Ring_op R))) = rig_mul (ring_rig R)
  := eq_refl.
Example p401_op_neg :
  ring_neg (Ring_op (Ring_op R)) = ring_neg R := eq_refl.

(* -- N1 (CONVERSION) -- *)
Fail Example p401_n1 : Ring_op (Ring_op R) = R := eq_refl.

(* -- N2 (CONVERSION) -- *)
Fail Example p401_n2 : ModR (Ring_op R) = RMod R := eq_refl.

(* CONTROL: what IS true on the nose. *)
Example p401_modR_unfold : ModR R = RMod (Ring_op R) := eq_refl.

End P401RingOp.

(* ================================================================= *)
(* (2) N3-N7.  Instance/Mod/Tensor.v's [TensorMod] serves NEITHER     *)
(* 相关说明。 （已译） *)
(*     computes the wrong object.  All TYPING.                        *)
(* ================================================================= *)

Section P401TensorMod.

Context (R S : RingObject).
Context (E : Bimodule R S).
Context (F : Bimodule S R).
Context (N : RModObject (Ring_op R)).

(* -- N3 (TYPING) -- *)
Fail Check (TensorMod N (bm_left E)).

(* -- N4 (TYPING) -- *)
Fail Check (@TensorMod R N (bm_left E)).

(* -- N5 (TYPING) -- *)
Fail Check (@TensorMod (Ring_op R) N (bm_left E)).

(* -- N6 (TYPING) -- *)
Fail Check (RBilinear N (bm_left E) (bm_left E)).

(* 相关说明。 （已译） *)
Check (@TensorMod R (bm_left E) (bm_left E)).
Check (@TensorMod (Ring_op R) N N).

(* 相关说明。 （已译） *)
Definition p401_hazard_accepted : RModObject (Ring_op R) :=
  @TensorMod (Ring_op R) N (bimodule_right_RMod F).

(* -- N7 (TYPING).  It is a right R-module, so it is not an object of
      [ModR S], which is where Exercise 3's N ⊗_R E lives. -- *)
Fail Definition p401_n7 : RModObject (Ring_op S) :=
  @TensorMod (Ring_op R) N (bimodule_right_RMod F).

(* CONTROL: 对象 Exercise 3 does produce, at same [N]. （已译） *)
Check (RTensor E N : RModObject (Ring_op S)).

End P401TensorMod.

(* ================================================================= *)
(* (3) N8-N9.  Riehl's general three-ring form is closed off: a right *)
(*     R-module is not a (ℤ,R)-bimodule in this tree.  Both TYPING.   *)
(* ================================================================= *)

Section P401Integers.

Context (R : RingObject).
Context (M : RModObject (Ring_op R)).

(* -- N8 (TYPING) -- *)
Fail Check (M : RModObject Int_Ring).

(* -- N9 (TYPING) -- *)
Fail Check (@Build_Bimodule Int_Ring R M).

(* 相关说明。 （已译） *)
Check (Int_Bimodule : Bimodule Int_Ring Int_Ring).
Check (bm_left Int_Bimodule : RModObject Int_Ring).
Check (M : RModObject (Ring_op R)).

End P401Integers.

(* ================================================================= *)
(* (4) N10-N13.  Part (c)'s comparison is an isomorphism and NOTHING  *)
(* stronger: two 函子 different records, two （已译） *)
(* 对象 different records, two module structures （已译） *)
(*     on the tensor of two bimodules do not even share a type.       *)
(* ================================================================= *)

Section P401PartC.

Context (R S T : RingObject).
Context (E : Bimodule R S).
Context (E1 : Bimodule S T).
Context (N : RModObject (Ring_op R)).

(* 相关说明。 （已译） *)
Check (tensor_assoc_iso E E1
  : (TensorWith E1 ◯ TensorWith E : ModR R ⟶ ModR T)
      ≈ TensorWith (BimodTensorBimod E E1)).
Check ((RTensor E1 (RTensor E N) : RModObject (Ring_op T))
         = RTensor (BimodTensorBimod E E1) N).

(* -- N10 (CONVERSION) -- *)
Fail Example p401_n10 :
  (TensorWith E1 ◯ TensorWith E : ModR R ⟶ ModR T)
    = TensorWith (BimodTensorBimod E E1) := eq_refl.

(* -- N11 (CONVERSION) -- *)
Fail Example p401_n11 :
  (HomS E ◯ HomS E1 : ModR T ⟶ ModR R)
    = HomS (BimodTensorBimod E E1) := eq_refl.

(* -- N16 (CONVERSION) -- Mac Lane's whiskered description of the
   composite's unit holds at ≈ ([bac_unit_whiskered]) and NOT on the nose:
   Adjunction/Compose.v is a [Qed] corollary proved by rewriting. *)
Fail Example p401_n16 :
  bac_unit E E1 N
    = fmap[HomS E]
        (@unit (ModR T) (ModR S) (TensorWith E1) (HomS E1)
           (bimodule_tensor_hom_adjunction E1) (RTensor E N))
      ∘ @unit (ModR S) (ModR R) (TensorWith E) (HomS E)
          (bimodule_tensor_hom_adjunction E) N := eq_refl.

(* -- N17 (CONVERSION) -- the counit's twin ([bac_counit_whiskered],
   Adjunction/Compose.v). *)
Fail Example p401_n17 (M : RModObject (Ring_op T)) :
  bac_counit E E1 M
    = @counit (ModR T) (ModR S) (TensorWith E1) (HomS E1)
        (bimodule_tensor_hom_adjunction E1) M
      ∘ fmap[TensorWith E1]
          (@counit (ModR S) (ModR R) (TensorWith E) (HomS E)
             (bimodule_tensor_hom_adjunction E) (HomSObj E1 M)) := eq_refl.

(* 相关说明。 （已译） *)
Check (bac_unit_whiskered E E1 N).
Check (fun (M : RModObject (Ring_op T)) => bac_counit_whiskered E E1 M).
Check @bac_unit.
Check @bac_counit.
Check @unit.
Check @counit.
Check @fmap.

(* CONTROL: what the file DOES deliver in place of N11. *)
Check (bimodule_hom_composite_iso E E1
  : (HomS E ◯ HomS E1 : ModR T ⟶ ModR R)
      ≈ HomS (BimodTensorBimod E E1)).

(* 相关说明。 （已译） *)
Fail Check (RTensor E1 (RTensor E N) : RModObject (Ring_op S)).

(* 相关说明。 （已译） *)
Fail Check (btb_left E E1 : RModObject (Ring_op T)).

(* 相关说明。 （已译） *)
Check (btb_left E E1 : RModObject R).
Check (btb_right E E1 : RModObject (Ring_op T)).
Example p401_btb_same_group :
  rm_ab (btb_left E E1) = rm_ab (btb_right E E1) := eq_refl.

End P401PartC.

(* ================================================================= *)
(* (5) N14-N15.  The hom-group's enrichment demands a category whose  *)
(* hom 证明 universes coincide. （已译） *)
(* ================================================================= *)

Section P401Univ.

Universes uo uh up.
Constraint uh < up.

Context (Cu : Category@{uo uh up}).

(* CONTROLS at the DECLARED levels. *)
Check (fun (x y : Cu) => x ~{Cu}~> y).
Check (fun (x : Cu) => @id Cu x).
Check (fun (x y z : Cu) (f : y ~> z) (g : x ~> y) => f ∘ g).

(* -- N14 (FORMABILITY) -- *)
Fail Check (AbEnriched Cu).

(* -- N15 (FORMABILITY, fired at its ARGUMENT) -- *)
Fail Check (fun (AC : AbEnriched Cu) (x y : Cu) => hom_ab AC x y).

End P401Univ.

(* ================================================================= *)
(* 相关说明。 （已译） *)
(* ================================================================= *)

Section P401Positives.

Context (R S T : RingObject).
Context (E : Bimodule R S).
Context (E1 : Bimodule S T).

Check (bimodule_adjunction_composite E E1
  : (TensorWith E1 ◯ TensorWith E) ⊣ (HomS E ◯ HomS E1)).

Check (bimodule_left_tensor_hom_adjunction E
  : LTensorWith E ⊣ LHomS E).

Check (bimodule_tensor_preserves_colimits E
  : PreservesAllColimits (TensorWith E)).

Check (fun (M : RModObject (Ring_op S)) (N : RModObject (Ring_op R)) =>
  bimodule_third_leg M E N
    : @Isomorphism Sets
        {| carrier := E ~{@BimodCat R S}~> HomAbBimod N M;
           is_setoid := @homset (@BimodCat R S) E (HomAbBimod N M) |}
        {| carrier := N ~{ModR R}~> HomSObj E M;
           is_setoid := @homset (ModR R) N (HomSObj E M) |}).

End P401Positives.
