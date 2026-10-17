(*
   本文件为测试：ProbeFreeVect。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Free.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(* 相关说明。 （已译） *)
Local Notation zgen  := (@fv_gen Int_Ring TwoGens).
Local Notation zsmul := (@fv_smul Int_Ring TwoGens).
Local Notation zplus := (@fv_plus Int_Ring TwoGens).

(* * ** Positive control: unit computes

 The unit [fmap[U] id ∘ arrow], both factors reduce, so the
 unit free-forgetful 伴随 IS basis 嵌入 the
 nose. （已译） *)
Example probe_unit_computes (x : carrier TwoGens) :
  free_module_unit Int_Ring TwoGens x = zgen x := eq_refl.

(*
   本节说明 ProbeFreeVect 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example probe_extend_computes :
  fv_eval int_probe
    (zplus (zsmul 2%Z (zgen true)) (zgen false)) = 11%Z := eq_refl.

(*
   本节说明 ProbeFreeVect 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example probe_counit_computes :
  cmon_map (rm_hom (free_module_counit Int_Ring Int_RMod))
    (@fv_gen Int_Ring (RMod_Forget Int_Ring Int_RMod) 3%Z) = 3%Z := eq_refl.

Example probe_counit_up_to_equiv :
  cmon_map (rm_hom (free_module_counit Int_Ring Int_RMod))
    (@fv_gen Int_Ring (RMod_Forget Int_Ring Int_RMod) 3%Z) ≈ 3%Z.
Proof. exact (free_module_counit_generator Int_Ring Int_RMod 3%Z). Qed.

(* * ** Negative: free 函子's action arrow does not compute

 Taken at 恒等 generating setoid, where formula-based
 定义 would reduce immediately. （已译） *)
Fail Example probe_fmap_computes (x : carrier TwoGens) :
  cmon_map (rm_hom (fmap[FreeMod Int_Ring] (@id Sets TwoGens))) (zgen x)
    = zgen x := eq_refl.

Example probe_fmap_up_to_equiv (x : carrier TwoGens) :
  cmon_map (rm_hom (fmap[FreeMod Int_Ring] (@id Sets TwoGens))) (zgen x)
    ≈ zgen x.
Proof.
  exact (@free_module_fmap_generators Int_Ring TwoGens TwoGens
           (@id Sets TwoGens) x).
Qed.

(* * ** Negative: commutativity formal sum not definitional

 The carrier plain inductive; commutativity constructor of
 quotienting 关系, positive control. （已译） *)
Fail Example probe_plus_comm_definitional :
  zplus (zgen true) (zgen false) = zplus (zgen false) (zgen true) := eq_refl.

Example probe_plus_comm_up_to_equiv :
  fv_eq (zplus (zgen true) (zgen false)) (zplus (zgen false) (zgen true)) :=
  fe_comm _ _.
