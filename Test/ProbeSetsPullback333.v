(*
   本文件为测试：ProbeSetsPullback333。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Regular.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Adjunction.GAFT.Sets.
Require Import Category.Instance.Sets.Pullback.

(** ** Instrument check

    A [Fail] that never fails would make every negative below vacuous. *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** Negative 1 (CONVERSION): the #326 derivation gives the WRONG apex

    This is the target's design decision, made checkable. *)

Section DerivationRoute.

Context (x y z : Sets) (f : x ~> z) (g : y ~> z).

Definition Derived : HasPullbacks Sets :=
  @HasPullbacks_of_Cartesian_HasEqualizers Sets _ Sets_HasEqualizers.

Definition DerObj := Pull f g (@pullback Sets Derived _ _ _ f g).

Fail Definition probe_derived_is_pair :
  DerObj = sets_pb_obj f g := eq_refl.

(*
   本节说明 ProbeSetsPullback333 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check Derived.
Check DerObj.
Check (sets_pb_obj f g).
Check (@HasPullbacks_of_Cartesian_HasEqualizers Sets).
Check Sets_HasEqualizers.
Check (@pullback Sets Derived _ _ _ f g).

End DerivationRoute.

(** ** Negative 2 (CONVERSION, different cause): prod has no eta *)

Section PairEta.

Context (x y z : Sets) (f : x ~> z) (g : y ~> z) (u : sets_pb_obj f g).

Fail Definition probe_pair_eta :
  sets_pb_pair f g u = `1 u := eq_refl.

(* Positive controls.  The pairing exists and the projections DO compute;
   only the surjective-pairing step is missing. *)
Check (sets_pb_pair f g u).
Check (sets_pb_fst f g).
Check (sets_pb_snd f g).

End PairEta.

(*
   本节说明等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section RoundTripMorphism.

Context (x y z : Sets) (f : x ~> z) (g : y ~> z).

Fail Definition probe_round_fst :
  exl ∘ sets_pb_pair f g = sets_pb_fst f g := eq_refl.

(* Positive controls: the POINTWISE forms ARE proved in the target, and
   every constant in the rejected equation is well-formed here. *)
Check sets_equalizer_round_fst_pointwise.
Check (sets_pb_pair f g).
Check (sets_pb_fst f g).
Check (@exl Sets _ x y).

End RoundTripMorphism.

(*
   本节说明拉回/推出、核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section BundledNotApplicable.

Context (x y z : Sets) (f : x ~> z) (g : y ~> z).

Fail Check (Pullback f g (sets_pb_obj f g)
              (sets_pb_fst f g) (sets_pb_snd f g)).

(* Positive controls: the BUNDLED form takes only the cospan, and the
   APEX-PINNED form is the one that takes apex and legs. *)
Check (Pullback f g).
Check Sets_Pullback.
Check Sets_IsPullback.
Check (@IsPullback Sets).

End BundledNotApplicable.

(** ** Controls for the delivered results *)

Check Sets_HasPullbacks.
Check Sets_Pullback.
Check Sets_IsPullback.
Check sets_pb_med.
Check sets_ker.
Check sets_ker_fst.
Check sets_ker_snd.
Check sets_kernel_pair_obj.
Check sets_kernel_pair_fst.
Check sets_kernel_pair_snd.
Check sets_ker_refl.
Check sets_ker_sym.
Check sets_ker_trans.
Check sets_pullback_is_equalizer.
Check sets_equalizer_is_pullback.
Check SubsetOf.
Check sub_obj.
Check sub_incl.
Check sub_incl_Monic.
Check sets_preimage.
Check sets_preimage_IsPullback.
Check sets_preimage_criterion.

(** ** Non-vacuity controls *)

Check even_ker_not_diagonal.
Check even_med_is_ump.
Check constThree_does_not_factor.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
