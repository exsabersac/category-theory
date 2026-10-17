(*
   本文件为测试：ProbeDirectedColimit330。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Thin.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Instance.Ab.DirectedColimit.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Relations.Relation_Definitions.

(** ** Instrument check

    A [Fail] that never fails would make every negative below vacuous.
    This one must fail for a reason that has nothing to do with the
    development. *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** Negative 1 (CONVERSION): the factorization triangle is not Leibniz *)

Section TriangleNegative.

Context (A : AbObject) (N : Cocone (FGDiagram A)) (X : FGSub A).

Fail Definition probe_triangle_strict :
  fg_med N ∘ cocone_inj (FGCocone A) X = cocone_inj N X := eq_refl.

(* Positive controls naming the negative's own constants.  The [≈] form IS
   proved in the target, and every constant in the rejected equation is
   independently well-formed here. *)
Check (fg_med_commutes N X).
Check (fg_med N).
Check (cocone_inj (FGCocone A) X).
Check (FGCocone A).
Check (FGDiagram A).
Check (FGSub A).

End TriangleNegative.

(*
   本节说明 ProbeDirectedColimit330 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Check (FGHom ab_Z : relation (FGObj ab_Z)).

(*
   本节说明 ProbeDirectedColimit330 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (fun X Y : FGObj ab_Z => inhabited (FGHom ab_Z X Y) : Prop).
Check FGHom.
Check FGObj.
Check ab_Z.
Check (relation (FGObj ab_Z)).

(** ** Controls for the delivered results

    These name the principal artifacts, so a rename anywhere in the target
    breaks this file loudly. *)

Check ab_fg_colimit.
Check ab_fg_isacolimit.
Check ab_fg_Colimit.
Check FGSub_directed.
Check FGSub_Thin.
Check AbSubgroup.
Check AbSubgroupAb.
Check absub_incl.
Check gen_sub.
Check gen_least.
Check InGen.
Check FinGen.
Check fg_join.
Check fg_of_list.
Check cyc.

(** ** Non-vacuity controls *)

Check Ztwo.
Check Zthree.
Check Ztwo_proper.
Check Zthree_proper.
Check Zsub_incomparable.
Check Zjoin_strictly_larger.
Check Ztwo_dup_iso.

(** ** MEASURED RENAME-SIMULATION SCORE

    The two negatives name these constants:

      Negative 1: [fg_med], [cocone_inj], [FGCocone]
      Negative 2: [FGHom], [FGObj], [ab_Z], [relation]

    All SEVEN are named by a positive control above, so renaming any one
    of them breaks this file rather than turning its negative vacuously
    green.  Score: 7/7, counted rather than recalled. *)
