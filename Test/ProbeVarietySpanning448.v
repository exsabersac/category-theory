Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Comp.
Require Import Category.Instance.Variety.
Require Import Category.Instance.Variety.Free.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.SpanningArrow.
Require Import Category.Instance.Variety.Spanning.

Generalizable All Variables.

(*
   本文件为测试：ProbeVarietySpanning448。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check *)

Fail Check variety_spanning_448_no_such_constant.

(** ** Positive controls *)

Check @Spanning.
Check @SubFactorsThrough.
Check @SpanningArrowsOutOf.
Check @SolutionSet.
Check @sol_index.
Check @HasWidePullbacks.
Check @SVariety.
Check @SVariety_Forget.
Check @CommEq.
Check @variety_spanning.
Check @variety_spanning_arrow.
Check @variety_solution_set.
Check @sgen_alg.
Check @sgen_corestrict.
Check @sgen_subobj.
Check @sgen_factors.
Check @SubAlg.
Check @sa_subobj.
Check @svariety_monic_iff_injective.
Check @svariety_iso.

Section Probes.

Context {S : UA.OpSignature} (E : UA.EqSignature S) (A : SVariety E).
Context (X : Sets) (h : X ~{Sets}~> SVariety_Forget E A).

(* P4 -- positive control: the solution set's index IS the spanning
   arrows, on the nose. *)
Example p448v_control :
  sol_index (variety_solution_set E X)
  = SpanningArrowsOutOf (SVariety_Forget E) X := eq_refl.

(* P2 -- CONVERSION: the spanning arrow is the CORESTRICTION of h, not h
   itself; "cannot unify "SubObj A" and "SubObj (sgen_alg h)"". *)
Fail Definition p448v_h_not_spanning : Spanning (SVariety_Forget E) h :=
  variety_spanning E A X h.

(* P3 -- CONVERSION: the generated subalgebra is a different object from
   A; "cannot unify "sgen_alg h" and "A"". *)
Fail Example p448v_gen_not_all : sgen_alg h = A := eq_refl.

(* P5 -- CONVERSION: the index is not the generating set (the header's
   NOT-DELIVERED smallness claim); "cannot unify
   "sol_index (variety_solution_set E X)" and "carrier X"" -- the
   expected type prints "= X" through the coercion while the message
   names "carrier X". *)
Fail Example p448v_index_not_X :
  sol_index (variety_solution_set E X) = carrier X := eq_refl.

End Probes.

(* P1 -- INSTANCE: the general Lemma's route is not available in tree,
   there being no wide pullbacks of [SVariety]; "Cannot infer this
   placeholder of type "HasWidePullbacks (SVariety CommEq)" (no type
   class instance found)".  A [Definition] with a hole, never a [Check],
   which tolerates the open evar.  (CORRECTION, #451: "there being no
   wide pullbacks of [SVariety]" is no longer true.  Structure/Pullback/
   Wide/Complete.v's [Complete_HasWidePullbacks] applied to Instance/
   Variety/Limit.v's [SVariety_Complete] builds them.  The refusal below
   still stands, because class search registers neither of the two;
   Test/ProbeWellPowered451.v's N22 and its control pin exactly that.) *)
Fail Definition p448v_no_wide_pullbacks :
  @HasWidePullbacks (SVariety CommEq) := _.
