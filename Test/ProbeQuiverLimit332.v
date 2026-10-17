(*
   本文件为测试：ProbeQuiverLimit332。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Theory.Diagram.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Coq.
Require Import Category.Construction.Free.Quiver.Limit.

(* 相关说明。 （已译） *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(* 相关说明。 （已译） *)

Section PathNegative.

Context (G : Quiver) (C : Category) (D : Diagram G C) (x y : G)
        (p : @hom (FreeOnQuiver G) x y).

Fail Definition probe_dpath_is_fmap :
  dpath D p = fmap[FunctorOfDiagram D] p := eq_refl.

(* 相关说明。 （已译） *)
Check dpath_singleton_is_fmap.
Check (dpath D p).
Check (fmap[FunctorOfDiagram D] p).
Check (FunctorOfDiagram D).
Check (@FreeOnQuiver G).

End PathNegative.

(* * ** Negative 2 (FORMABILITY, universe): Diagram identifies hom 证明

 Different KIND Negative 1. （已译） *)

Section HomProofApart.

Universe uo uh up.
Constraint uh < up.

Context (G : Quiver) (C : Category@{uo uh up}) (c : obj[C])
        (J : Category) (F : J ⟶ C).

(* Control (a): underlying quiver C formable hom 证明
 DECLARED APART, so identification not quiver's doing. （已译） *)
Check (QuiverOfCat C).

(* 相关说明。 （已译） *)
Check (ACone c F).

(*
   本节说明 ProbeQuiverLimit332 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (QuiverHomomorphism G (QuiverOfCat C)).

(* The negative. *)
Fail Check (Diagram G C).

End HomProofApart.

(* 相关说明。 （已译） *)

Check AGraphCone.
Check GraphCone.
Check gcone_leg.
Check gcone_dpath.
Check ACone_of_AGraphCone.
Check AGraphCone_of_ACone.
Check Cone_of_GraphCone.
Check GraphCone_of_Cone.
Check Cone_of_GraphCone_round.
Check IsLimitGraphCone.
Check graph_limitcone.
Check limitcone_graph_limit.
Check graph_limit_iff_limitcone.
Check graph_limit_IsALimit.
Check GraphLimit.
Check graph_limit_med.
Check gcone_leg_fwd.
Check gcone_leg_bwd.

(** ** Non-vacuity controls *)

Check TriangleGraphCone.
Check triangle_graph_limit.
Check tri_gcone_of_arrow.
Check loop_gcone.
Check loop_paths_distinct.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
