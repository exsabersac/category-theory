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

(* Positive controls naming the negative's own constants.  The derivation
   IS formable -- it is the DESCRIPTION that differs, not the term's
   existence -- and the directly-built apex is independently well-formed. *)
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

(** ** Negative 3 (CONVERSION): the equalizer round trip, as MORPHISMS

    The target's header records this and an earlier revision of this probe
    pinned it nowhere.  The two [SetoidMorphism] records agree on their
    underlying functions -- that is the POINTWISE [eq_refl] the target
    ships -- and differ in the rebuilt [proper_morphism] certificate. *)

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

(** ** Negative 4 (TYPING): the bundled Pullback record is not applicable

    A DIFFERENT KIND from 1-3.  [Pullback f g] is a [Type] carrying its
    apex as DATA, so it cannot be applied to an apex and two legs the way
    the apex-pinned [IsPullback] can.  Stripped, the error is
    "Illegal application (Non-functional construction)".  This is a DONOR
    fact -- Theory/Morphisms/CokernelPair.v already pins the pushout dual
    -- and is repeated here only so this file carries two kinds. *)

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

(** ** MEASURED RENAME-SIMULATION SCORE

    The constants the NEGATIVES name:

      Negative 1: [HasPullbacks_of_Cartesian_HasEqualizers],
                  [Sets_HasEqualizers], [Pull], [pullback], [sets_pb_obj]
      Negative 2: [sets_pb_pair]
      Negative 3: [exl], [sets_pb_fst]
      Negative 4: [Pullback], [sets_pb_snd]

    That is TEN, and the denominator is not padded with control-only
    names.  All ten are named by a positive control above, so renaming any
    one breaks this file rather than turning its negative vacuously green.
    Score: 10/10, counted rather than recalled. *)
