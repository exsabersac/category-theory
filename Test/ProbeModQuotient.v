Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Quotient.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Instance.Mod.Quotient.Isomorphism.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Theory.Universal.Element.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

(*
   本文件为测试：ProbeModQuotient。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section RelationBoundary.

Context {R : RingObject}.
Context {M N : RModObject R}.
Context (f : M ~{RMod R}~> N).
Context (x y : carrier (cmon_setoid N)).

Fail Definition probe_relations_convertible :
  ab_coset_eq (rm_hom f) x y = mquot_rel (ImageSubmod f) x y := eq_refl.

(* 相关说明。 （已译） *)
Definition control_relations_agree :
  ab_coset_eq (rm_hom f) x y ↔ mquot_rel (ImageSubmod f) x y :=
  rmod_quotient_relations_agree f x y.

(*
   本节说明 ProbeModQuotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition control_image_mem :
  smod_mem (ImageSubmod f) x
    = { a : carrier (cmon_setoid M) & cmon_map (rm_hom f) a ≈ x }
  := eq_refl.

End RelationBoundary.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ObjectBoundary.

Context {R : RingObject}.
Context {M N : RModObject R}.
Context (f : M ~{RMod R}~> N).

Fail Definition probe_objects_equal :
  RModQuotient f = QuotientMod (ImageSubmod f) := eq_refl.

(* 相关说明。 （已译） *)
Definition control_carriers_agree :
  carrier (cmon_setoid (RModQuotient f))
    = carrier (cmon_setoid (QuotientMod (ImageSubmod f))) := eq_refl.

(* SECOND POSITIVE CONTROL: 同构 IS available. （已译） *)
Definition control_objects_iso :
  RModQuotient f ≅[RMod R] QuotientMod (ImageSubmod f) :=
  RModQuotient_is_quotient_by_image f.

End ObjectBoundary.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section TriangleBoundary.

Context {R : RingObject}.
Context {M N : RModObject R}.
Context (f : M ~{RMod R}~> N).

(* 相关说明。 （已译） *)
Definition control_to_is_mediator :
  to (mod_first_isomorphism_theorem f)
    = mquot_med (KernelSub f) (mod_image_elem f) := eq_refl.

Definition control_from_is_mediator :
  from (mod_first_isomorphism_theorem f)
    = mod_image_med f (mquot_elem (KernelSub f)) := eq_refl.

Fail Definition probe_triangle_strict :
  to (mod_first_isomorphism_theorem f) ∘ mquot_proj (KernelSub f)
    = mod_image_cores f := eq_refl.

(* 相关说明。 （已译） *)
Definition control_triangle_equiv :
  to (mod_first_isomorphism_theorem f) ∘ mquot_proj (KernelSub f)
    ≈ mod_image_cores f :=
  mod_first_isomorphism_triangle f.

End TriangleBoundary.

(*
   本节说明 ProbeModQuotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ZeroRingBoundary.

Context {R : RingObject}.

Fail Definition probe_total_is_zero_ring :
  QuotientRing (TotalIdeal R) = Zero_Ring := eq_refl.

(* 相关说明。 （已译） *)
Definition control_total_carrier :
  carrier (rig_setoid (QuotientRing (TotalIdeal R)))
    = carrier (rig_setoid R) := eq_refl.

(* 相关说明。 （已译） *)
Definition control_total_one_is_zero :
  rig_one (QuotientRing (TotalIdeal R))
    ≈ rig_zero (QuotientRing (TotalIdeal R)) :=
  rquot_total_one_is_zero R.

End ZeroRingBoundary.

(*
   本节说明 ProbeModQuotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition control_mod_universal_elem {R : RingObject} {M : RModObject R}
  (S : Submodule M) :
  `1 (@aue_elem _ (MKillsFunctor S) (QuotientMod S)
        (mquot_universal_element S)) = mquot_proj S := eq_refl.

Definition control_rng_universal_elem {R : RingObject} (I : Ideal R) :
  `1 (@aue_elem _ (RKillsFunctor I) (QuotientRing I)
        (rquot_universal_element I)) = rquot_proj I := eq_refl.

(* And ring-side reading left ideal's 关系 two-sided
 one, Instance/Rng/Quotient.v claims convertibility. （已译） *)
Definition control_lquot_is_rquot {R : RingObject} (I : Ideal R)
  (x y : carrier (rig_setoid R)) :
  lquot_rel (Ideal_LeftIdeal I) x y = rquot_rel I x y := eq_refl.
