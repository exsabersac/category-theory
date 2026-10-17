(*
   本文件为测试：ProbePerp385。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Instance.Grp.Galois.
Require Import Category.Adjunction.Right.
Require Import Category.Instance.InnerProduct.Galois.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(* ------------------------------------------------------------------------ *)
(** ** Negative 1: the instrument *)

(* 相关说明。 （已译） *)
Fail Check probe385_no_such_constant_anywhere.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Check @subset_le.
Check @subset_le_preorder.
Check @subset_le_antisym.
Check @Subsets.
Check @op_rel.
Check @op_PreOrder.
Check @Proset.
Check @GaloisConnection.
Check @Powerset_Prop_obj.
Check @Powerset_Prop_truth.
Check @AdjointOnTheRight.
Check @AdjointOnTheLeft.
Check @PerpRel.
Check @Build_PerpRel.
Check @perp.
Check @perp_sym.
Check @perp_respects.
Check @perp_respects_iff.
Check @perp_set.
Check @perp_set_mem.
Check @perp_transpose.
Check @perp_set_antitone.
Check @perp_set_respects.
Check @perp_galois.
Check @perp_galois_l_is_r.
Check @perp_to_is_from_swapped.
Check @perp_PreOrder_l.
Check @perp_PreOrder_r.
Check @perp_unit.
Check @perp_counit.
Check @perp_unit_is_counit.
Check @perp_triple.
Check @ClosedPerp.
Check @perp_set_closed.
Check @closed_perp_iff.
Check @PerpFunctor.
Check @PerpFunctor_r.
Check @perp_adjunction.
Check @PerpOp.
Check @perp_AdjointOnTheRight.
Check @perp_aor_to.
Check @perp_aor_from.
Check @zz_setoid.
Check @zdot.
Check @ZZPerp.
Check @zz_sub.
Check @zz_e1.
Check @zz_yaxis.
Check @zz_xaxis.
Check @zz_perp_is_dot.
Check @zz_perp_e1_is_yaxis.
Check @zz_perp_yaxis_is_xaxis.
Check @zz_e1_not_ClosedPerp.
Check @zz_yaxis_ClosedPerp.
Check @zz_e1_not_self_perp.
Check @zz_axes_differ.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section AbstractBoundary.

Universe po pu.
Constraint Set < po.

Context (Xp : SetoidObject@{po po}).
Context (Pp : PerpRel@{po} Xp).

(* ---------------------------------------------------------------------- *)
(* 相关说明。 （已译） *)

(*
   本节说明 ProbePerp385 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check (perp_galois Pp
        : GaloisConnection (@subset_le@{po} Xp)
            (op_rel (@subset_le@{po} Xp))).

Fail Check (perp_galois Pp
             : GaloisConnection (@subset_le@{po} Xp)
                 (@subset_le@{po} Xp)).

(* ---------------------------------------------------------------------- *)
(* 相关说明。 （已译） *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check (perp_AdjointOnTheRight Pp
        : AdjointOnTheRight (PerpOp Pp) (PerpOp Pp)).

Fail Check (perp_AdjointOnTheRight Pp
             : AdjointOnTheLeft (PerpOp Pp) (PerpOp Pp)).

(* ---------------------------------------------------------------------- *)
(* * ** Negative 4 (TYPING): [L = R] about MAPS, not 函子 （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check (PerpFunctor Pp
        : Subsets@{po pu} Xp ⟶ Proset@{po pu} (@perp_PreOrder_r Xp)).
Check (PerpFunctor_r Pp
        : Proset@{po pu} (@perp_PreOrder_r Xp) ⟶ Subsets@{po pu} Xp).
Check (perp_galois_l_is_r Pp).

Fail Check (PerpFunctor Pp = PerpFunctor_r Pp).

(* ---------------------------------------------------------------------- *)
(* 相关说明。 （已译） *)

(*
   本节说明 ProbePerp385 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check (fun S => perp_triple Pp S
         : perp_set Pp (perp_set Pp (perp_set Pp S)) ≈ perp_set Pp S).

Fail Check (fun S : carrier (Powerset_Prop_obj@{po} Xp) =>
              (eq_refl : perp_set Pp (perp_set Pp (perp_set Pp S))
                           = perp_set Pp S)).

End AbstractBoundary.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明 ProbePerp385 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check (zz_perp_e1_is_yaxis : perp_set ZZPerp zz_e1 ≈ zz_yaxis).

Fail Check (eq_refl : perp_set ZZPerp zz_e1 = zz_yaxis).

(* ------------------------------------------------------------------------ *)
(* * ** Negative 7 (FORMABILITY): carrier 关系 levels coincide （已译） *)

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UniverseBoundary.

Universe qo qh.
Constraint qh < qo.

Context (Aq : SetoidObject@{qo qh}).

Check (carrier Aq).
Check (is_setoid Aq).
Check (Aq : Type@{qo}).

Fail Check (PerpRel Aq).

End UniverseBoundary.
