(*
   本文件为测试：ProbeAlgebras。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Coq.ZArith.ZArith.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Construction.Elements.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Rng.Algebras.
Require Import Category.Instance.Rng.Polynomial.
Require Import Category.Instance.Rng.Algebras.Associative.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Matr.GL.
Require Import Category.Instance.Rng.MonoidRing.
Require Import Category.Instance.Rng.GroupRing.
Require Import Category.Instance.Vect.TensorAlgebra.

Monomorphic Universe big.
Monomorphic Constraint Set < big.

(*
   本节说明函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* instrument check *)
Check (Int_Rig@{big big big} : RigObject@{big big big}).
Check (Int_Ring@{big big big} : RingObject@{big big big}).

(* 相关说明。 （已译） *)
Check (Rig_Forget_Mon (Int_Rig@{Set Set Set})).
Check (Rng_Forget_Mon (Int_Ring@{Set Set Set})).

(* NEGATIVE 1: the donor itself does not reach one universe up *)
Fail Check (Rig_Forget_Mon (Int_Rig@{big big big})).

(* NEGATIVE 2: neither does ring-level 函子 built it （已译） *)
Fail Check (Rng_Forget_Mon (Int_Ring@{big big big})).

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* positive controls: scalars and generators DO close by [eq_refl] *)
Check (fun (R : RingObject) (M : MonSets) (S : RingObject)
           (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
           (Hcomm : MRComm phi psi) =>
         eq_refl : rig_map (mring_extend phi psi Hcomm) (mr_scal (rig_zero R))
                     = rig_map phi (rig_zero R)).

Check (fun (R : RingObject) (M : MonSets) (S : RingObject)
           (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
           (Hcomm : MRComm phi psi) (m : carrier (mcar M)) =>
         eq_refl : rig_map (mring_extend phi psi Hcomm) (mr_gen m)
                     = mmap psi m).

(* NEGATIVE 3: preservation of zero is not definitional *)
Fail Check (fun (R : RingObject) (M : MonSets) (S : RingObject)
                (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
                (Hcomm : MRComm phi psi) =>
              eq_refl
                : rig_map (mring_extend phi psi Hcomm)
                    (rig_zero (MonoidRing R M)) = rig_zero S).

(* NEGATIVE 4: nor is preservation of one *)
Fail Check (fun (R : RingObject) (M : MonSets) (S : RingObject)
                (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
                (Hcomm : MRComm phi psi) =>
              eq_refl
                : rig_map (mring_extend phi psi Hcomm)
                    (rig_one (MonoidRing R M)) = rig_one S).

(* 相关说明。 （已译） *)
Check (fun (R : RingObject) (M : MonSets) (S : RingObject)
           (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
           (Hcomm : MRComm phi psi) =>
         rig_map_zero (mring_extend phi psi Hcomm)).

Check (fun (R : RingObject) (M : MonSets) (S : RingObject)
           (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
           (Hcomm : MRComm phi psi) =>
         rig_map_one (mring_extend phi psi Hcomm)).

(* 相关说明。 （已译） *)

Section TensorStrictness.

Context (K : CRng) (V : RModObject (`1 K)) (A : AAlgObject K).
Context (f : AAlgLinear V A).

(* positive controls *)
Check (fun v => eq_refl
        : rig_map (`1 (tensor_extend A f)) (tt_gen v) = alin_map f v).
Check (fun a => eq_refl
        : rig_map (`1 (tensor_extend A f)) (tt_scal a)
            = rig_map (aalg_unit A) a).

(* NEGATIVE 5: preservation of zero is not definitional *)
Fail Check (eq_refl
  : rig_map (`1 (tensor_extend A f)) (rig_zero (TensorRing V))
      = rig_zero (aalg_ring A)).

(* NEGATIVE 6: nor is preservation of one *)
Fail Check (eq_refl
  : rig_map (`1 (tensor_extend A f)) (rig_one (TensorRing V))
      = rig_one (aalg_ring A)).

(* ...and both DO hold up to [≈] *)
Check (rig_map_zero (`1 (tensor_extend A f))).
Check (rig_map_one (`1 (tensor_extend A f))).

End TensorStrictness.

(*
   本节说明 ProbeAlgebras 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check (fun (K : CRng) (V : RModObject (`1 K)) (t : TTerm V) =>
         eq_refl : rig_map (`1 (ext_proj V)) t = t).

Check (fun (K : CRng) (V : RMod (`1 K)) =>
         eq_refl : fobj[TensorFunctor K] V = TensorAlg V).

Check (fun (M : MonSets) =>
         eq_refl : fobj[MonoidRingFunctor] M = ZMonRing M).

Check (fun (G : Grp) =>
         eq_refl : fobj[GroupRingFunctor] G = GrpRing G).

Check (fun (G : Grp) (g : carrier (grp_setoid G)) =>
         eq_refl : `1 (grp_map (grp_ring_insert G) g)
                     = @mr_gen Int_Ring (Grp_MonSets G) g).
