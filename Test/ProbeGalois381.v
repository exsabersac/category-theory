(*
   本文件为测试：ProbeGalois381。

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
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Instance.Rep.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Adjunction.Right.
Require Import Category.Instance.Grp.Galois.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(* ------------------------------------------------------------------------ *)
(** ** Negative 1: the instrument *)

(* 相关说明。 （已译） *)
Fail Check probe381_no_such_constant_anywhere.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Check @subset_le.
Check @subset_le_preorder.
Check @Subsets.
Check @op_rel.
Check @op_PreOrder.
Check @Proset.
Check @GaloisConnection.
Check @GrpObject.
Check @grp_setoid.
Check @MSetoidAction.
Check @act_setoid.
Check @grp_mon.
Check @Powerset_Prop_obj.
Check @Z2.
Check @AdjointOnTheRight.
Check @stab.
Check @fixed.
Check @stab_PreOrder_G.
Check @group_action_galois.
Check @group_action_adjunction.
Check @group_action_AdjointOnTheRight.
Check @stab_fixed_stab.
Check @fixed_stab_fixed.
Check @stab_Subgroup.
Check @closed_G_iff.
Check @closed_U_iff.
Check @ClosedG.
Check @ClosedU.
Check @subset_le_antisym.
Check @gal_lrl_below.
Check @gal_lrl_above.
Check @gal_closed_l_iff.
Check @StabOp.
Check @FixedOp.
Check @GalZ2.
Check @GalZ2Act.
Check @GalV4.
Check @GalV4Act.
Check @galois_two.
Check @galois_true.
Check @galois_stab_true_trivial.
Check @galois_v4_stab_proper.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明 ProbeGalois381 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section AntitoneIsNotCovariant.

Universe po pgu.
Constraint Set < po.
Constraint po <= pgu.

(*
   本节说明 ProbeGalois381 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Context (Gp : GrpObject@{pgu po po}).
Context (Ap : MSetoidAction@{po po pgu pgu pgu po po pgu}
                (grp_mon@{pgu po po} Gp)).

(* 相关说明。 （已译） *)
Check (group_action_galois Gp Ap
        : GaloisConnection (@subset_le@{po} (act_setoid Ap))
            (op_rel (@subset_le@{po} (grp_setoid Gp)))).

Fail Check (group_action_galois Gp Ap
             : GaloisConnection (@subset_le@{po} (act_setoid Ap))
                 (@subset_le@{po} (grp_setoid Gp))).

(* ---------------------------------------------------------------------- *)
(* 相关说明。 （已译） *)

(*
   本节说明 ProbeGalois381 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check (fun X => stab_fixed_stab Gp Ap X
         : stab (fixed (stab X)) ≈ stab X).

Fail Check (fun (X : carrier (Powerset_Prop_obj@{po} (act_setoid Ap))) =>
              (eq_refl : @stab Gp Ap (@fixed Gp Ap (@stab Gp Ap X))
                           = @stab Gp Ap X)).

Check (fun S => fixed_stab_fixed Gp Ap S
         : fixed (stab (fixed S)) ≈ fixed S).

Fail Check (fun (S : carrier (Powerset_Prop_obj@{po} (grp_setoid Gp))) =>
              (eq_refl : @fixed Gp Ap (@stab Gp Ap (@fixed Gp Ap S))
                           = @fixed Gp Ap S)).

(* ---------------------------------------------------------------------- *)
(* * ** Negative 5 (CONVERSION): target 范畴 opposite one on
 对象 homs, but not whole record （已译） *)

(*
   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check (eq_refl : obj[Proset@{po Set} (stab_PreOrder_G Gp)]
                   = obj[(Subsets@{po Set} (grp_setoid Gp))^op]).

Check (fun S T : carrier (Powerset_Prop_obj@{po} (grp_setoid Gp)) =>
         (eq_refl : (S ~{Proset@{po Set} (stab_PreOrder_G Gp)}~> T)
                      = (S ~{(Subsets@{po Set} (grp_setoid Gp))^op}~> T))).

Check (fun S : carrier (Powerset_Prop_obj@{po} (grp_setoid Gp)) =>
         (eq_refl : @id (Proset@{po Set} (stab_PreOrder_G Gp)) S
                      = @id ((Subsets@{po Set} (grp_setoid Gp))^op) S)).

Check (fun (S T U : carrier (Powerset_Prop_obj@{po} (grp_setoid Gp)))
           (f : T ~{Proset@{po Set} (stab_PreOrder_G Gp)}~> U)
           (g : S ~{Proset@{po Set} (stab_PreOrder_G Gp)}~> T) =>
         (eq_refl : @compose (Proset@{po Set} (stab_PreOrder_G Gp)) S T U f g
                      = @compose ((Subsets@{po Set} (grp_setoid Gp))^op)
                                 S T U f g)).

Fail Check (eq_refl : Proset@{po Set} (stab_PreOrder_G Gp)
                        = (Subsets@{po Set} (grp_setoid Gp))^op).

End AntitoneIsNotCovariant.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明 ProbeGalois381 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SubsetsIdentifies.

Universe qo qh qgu.
Constraint qo < qh.
Constraint qh <= qgu.

Context (Gq : GrpObject@{qgu qo qh}).
Context (Aq : MSetoidAction@{qo qh qgu qgu qgu qo qh qgu}
                (grp_mon@{qgu qo qh} Gq)).

(* Controls, at those very levels. *)
Check (grp_setoid Gq).
Check (act_setoid Aq).
Check (carrier (grp_setoid Gq)).
Check (grp_mon@{qgu qo qh} Gq).

Fail Check (Subsets (grp_setoid Gq)).

Fail Check (Subsets (act_setoid Aq)).

End SubsetsIdentifies.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明 ProbeGalois381 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check @Z2.
Check (grp_setoid Z2).
Check (Subsets (grp_setoid GalZ2)).

Check (Subsets (grp_setoid Z2)).

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Check (stab (A := GalZ2Act) galois_true).
Check (stab_Subgroup GalV4 GalV4Act galois_true).
Check (group_action_AdjointOnTheRight GalZ2 GalZ2Act).
Check (group_action_adjunction GalZ2 GalZ2Act).
Check (closed_G_iff GalZ2 GalZ2Act galois_true).
Check (closed_U_iff GalZ2 GalZ2Act galois_true).
Check (ClosedG GalZ2Act galois_true).
Check (ClosedU (A := GalZ2Act) galois_true).
Check (subset_le_antisym (X := galois_two)).
Check (gal_lrl_below (stab_PreOrder_U GalZ2 GalZ2Act)
         (group_action_galois GalZ2 GalZ2Act)).
Check (gal_lrl_above (stab_PreOrder_G GalZ2)
         (group_action_galois GalZ2 GalZ2Act)).
Check (gal_closed_l_iff (stab_PreOrder_U GalZ2 GalZ2Act)
         (stab_PreOrder_G GalZ2)
         (group_action_galois GalZ2 GalZ2Act)).
Check (StabOp GalZ2 GalZ2Act).
Check (FixedOp GalZ2 GalZ2Act).
Check galois_stab_true_trivial.
Check galois_v4_stab_proper.
