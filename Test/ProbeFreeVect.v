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

(* Index arguments supplied once, as NOTATIONS (so each unfolds to the
   constructor itself) — the device Instance/Mod/Free.v uses for its own
   witnesses; [Local Notation] does not cross files. *)
Local Notation zgen  := (@fv_gen Int_Ring TwoGens).
Local Notation zsmul := (@fv_smul Int_Ring TwoGens).
Local Notation zplus := (@fv_plus Int_Ring TwoGens).

(** ** Positive control: the unit computes

    The unit is [fmap[U] id ∘ arrow], and both factors reduce, so the
    unit of the free-forgetful adjunction IS the basis insertion on the
    nose. *)
Example probe_unit_computes (x : carrier TwoGens) :
  free_module_unit Int_Ring TwoGens x = zgen x := eq_refl.

(** ** Positive control: the linear extension computes

    The mediator is a [Fixpoint] on formal expressions, so evaluating it
    on a closed expression reduces all the way to a value of the target
    module's carrier. *)
Example probe_extend_computes :
  fv_eval int_probe
    (zplus (zsmul 2%Z (zgen true)) (zgen false)) = 11%Z := eq_refl.

(** ** Negative: the counit does not compute

    Stripped of [Fail] this reports that [eq_refl] cannot unify the
    counit's value at a generator with the generator, the counit being
    [unique_obj] of a [Qed]-opaque uniqueness proof.  The [≈] statement
    IS available and is the control immediately below. *)
Fail Example probe_counit_computes :
  cmon_map (rm_hom (free_module_counit Int_Ring Int_RMod))
    (@fv_gen Int_Ring (RMod_Forget Int_Ring Int_RMod) 3%Z) = 3%Z := eq_refl.

Example probe_counit_up_to_equiv :
  cmon_map (rm_hom (free_module_counit Int_Ring Int_RMod))
    (@fv_gen Int_Ring (RMod_Forget Int_Ring Int_RMod) 3%Z) ≈ 3%Z.
Proof. exact (free_module_counit_generator Int_Ring Int_RMod 3%Z). Qed.

(** ** Negative: the free functor's action on an arrow does not compute

    Taken at the identity of the generating setoid, where a formula-based
    definition would reduce immediately. *)
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

(** ** Negative: commutativity of a formal sum is not definitional

    The carrier is a plain inductive; commutativity is a constructor of
    the quotienting relation, which is the positive control. *)
Fail Example probe_plus_comm_definitional :
  zplus (zgen true) (zgen false) = zplus (zgen false) (zgen true) := eq_refl.

Example probe_plus_comm_up_to_equiv :
  fv_eq (zplus (zgen true) (zgen false)) (zplus (zgen false) (zgen true)) :=
  fe_comm _ _.
