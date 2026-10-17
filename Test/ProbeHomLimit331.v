(*
   本文件为测试：ProbeHomLimit331。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Functor.Hom.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Limit.Cartesian.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Instance.Coq.
Require Import Category.Functor.Hom.Limit.

(** ** Instrument check

    A [Fail] that never fails would make every negative below vacuous. *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** Negative 1 (TYPING): HomFrom's implicit category is undeterminable *)

Fail Check (FCone (HomFrom unit) (coq_two_limit (Pick_Two bool nat))).

(* Positive controls naming the negative's own constants.  The EXPLICIT
   spelling is what the target ships, and every constant in the rejected
   expression is independently well-formed here. *)
Check coq_hom_bool_nat_limit.
Check (@FCone Two_Discrete Coq Sets (HomFrom unit)).
Check (HomFrom unit).
Check coq_two_limit.
Check (Pick_Two bool nat).
(* The repair, named: ascribing the object determines [HomFrom]'s implicit
   category, and then FCone's own arguments may stay implicit. *)
Check (FCone (HomFrom (unit : obj[Coq])) (coq_two_limit (Pick_Two bool nat))).

(** ** Former Negative 2 (FORMABILITY, universe): the discrete route no
    longer pins Set

    RECORDED CORRECTION: this section used to hold the file's second
    negative, refused because [DiscreteCat_Functor] was unannotated and
    instantiated [DiscreteCat@{u Set Set}].  Annotated in the PR
    "algebraic carriers are sets" (2026-09-17) it is accepted, and the
    line is retained as a positive control at the same levels. *)

Section AboveSet.

Universe uo uh.
Constraint Set < uh.

Context (C : Category@{uo uh uh}) (c : obj[C]) (fam : bool -> obj[C]).

(* Control (a): the DIRECT product statements carry no [Set] -- they
   elaborate over this category, whose hom universe is strictly above it.
   This is the header's positive claim, exercised rather than asserted. *)
Check (@hom_IsIndexedProduct C c).
Check (@hom_IsCartesianProduct C c).

(* Control (b): the discrete-diagram functor ALONE is formable here.  It
   always was; what used to be refused was the COMBINATION below. *)
Check (@DiscreteCat_Functor bool C fam).

(* The repaired combination, kept as a positive control. *)
Check (fun N : Cone (@DiscreteCat_Functor bool C fam) => IsLimitCone N).

(* Control (c): [IsLimitCone] itself is fine at this ambient category when
   the SHAPE is not the Set-pinned discrete one. *)
Check (fun (J : Category@{uo uh uh}) (K : J ⟶ C) (N : Cone K) =>
         IsLimitCone N).

End AboveSet.

(** ** Controls for the delivered results *)

Check hom_PreservesLimitCone.
Check hom_ContinuousFunctor.
Check hom_PreservesLimit.
Check hom_PreservesAllLimits.
Check hom_preserved_leg.
Check hom_preserved_mediator.
Check hom_med_commutes.
Check hom_med_unique.
Check hom_IsIndexedProduct.
Check hom_IsCartesianProduct.
Check HomFrom.
Check HomTo.
Check hom_to_is_op_hom_from.
Check cohom_ContinuousFunctor.
Check cohom_PreservesLimitCone.
Check cohom_colimit_to_limit.
Check cohom_IsIndexedProduct.
Check cohom_IsCartesianProduct.
Check cartesian_IsCartesianProduct.
Check coq_hom_product.
Check coq_hom_limit_cone.

(** ** MEASURED RENAME-SIMULATION SCORE

    The one remaining negative names [FCone], [HomFrom], [coq_two_limit]
    and [Pick_Two]; the repaired section names [DiscreteCat_Functor],
    [Cone] and [IsLimitCone].

    All SEVEN are named by a positive control above, so renaming any one
    of them breaks this file rather than turning a negative vacuously
    green or a positive control vacuously absent.  Score: 7/7, counted
    rather than recalled.

    RECORDED CORRECTION: an earlier revision counted "two negatives" here
    and assigned the second group to Negative 2.  That negative was
    repaired by annotating [DiscreteCat_Functor]; the constants and the
    score are unchanged, only the KIND of the line they guard. *)
