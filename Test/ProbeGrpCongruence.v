(*
   本文件为测试：ProbeGrpCongruence。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Transform.
Require Import Category.Structure.Groupoid.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Congruence.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Example control_deloop_agrees (H : GrpObject) :
  Deloop (grp_deloop_GrpObject H) = grp_deloop H := eq_refl.

Example control_ginv_agrees (H : GrpObject) (a : carrier H) :
  ginv (grp_deloop_IsGroupoid' H) (x:=ttt) (y:=ttt) a = grp_inv H a := eq_refl.

(* 相关说明。 （已译） *)
Example control_ginv_agrees_Free (H : GrpObject) (a : carrier H) :
  ginv (grp_deloop_IsGroupoid H) (x:=ttt) (y:=ttt) a = grp_inv H a := eq_refl.

(* 相关说明。 （已译） *)
Fail Definition negative_isgroupoid_record (H : GrpObject) :
  grp_deloop_IsGroupoid' H = grp_deloop_IsGroupoid H := eq_refl.

(* 相关说明。 （已译） *)

(* POSITIVE CONTROL: what the recovered membership DOES convert to. *)
Example control_round_unfolds {G : GrpObject} (N : NormalSubgroup G)
  (a : carrier G) :
  sub_mem (@cong_ns G (ns_rel N) (ns_congruence N)) a
    = quot_rel N a (grp_unit G) := eq_refl.

(* NEGATIVE: it is not membership in N on the nose. *)
Fail Definition negative_round_strict {G : GrpObject} (N : NormalSubgroup G)
  (a : carrier G) :
  sub_mem (@cong_ns G (ns_rel N) (ns_congruence N)) a = sub_mem N a := eq_refl.

(* * ** Negative 3: quotient 范畴 not delooping, nose （已译） *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example control_quotient_obj {G : GrpObject} (N : NormalSubgroup G) :
  obj[deloop_quotient N] = obj[grp_deloop (QuotientGrp N)] := eq_refl.

Example control_quotient_hom {G : GrpObject} (N : NormalSubgroup G) :
  (ttt ~{deloop_quotient N}~> ttt)
    = (ttt ~{grp_deloop (QuotientGrp N)}~> ttt) := eq_refl.

Example control_quotient_id {G : GrpObject} (N : NormalSubgroup G) :
  @id (deloop_quotient N) ttt = @id (grp_deloop (QuotientGrp N)) ttt := eq_refl.

Example control_quotient_compose {G : GrpObject} (N : NormalSubgroup G)
  (f g : carrier G) :
  @compose (deloop_quotient N) ttt ttt ttt f g
    = @compose (grp_deloop (QuotientGrp N)) ttt ttt ttt f g := eq_refl.

(* NEGATIVE: whole 范畴 not convertible. （已译） *)
Fail Definition negative_quotient_category {G : GrpObject}
  (N : NormalSubgroup G) :
  deloop_quotient N = grp_deloop (QuotientGrp N) := eq_refl.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Example control_med_map {G K : GrpObject} (N : NormalSubgroup G)
  (p : Kills N K) (a : carrier (QuotientGrp N)) :
  grp_map (cat_med N p) a = grp_map (quot_med N p) a := eq_refl.

(* 相关说明。 （已译） *)
Fail Definition negative_med_record {G K : GrpObject} (N : NormalSubgroup G)
  (p : Kills N K) : cat_med N p = quot_med N p := eq_refl.

(* 相关说明。 （已译） *)

(* POSITIVE CONTROL: what the categorical kernel's membership IS. *)
Example control_kernel_unfolds {G K : GrpObject} (h : G ~{Grp}~> K)
  (a : carrier G) :
  sub_mem (kernel_ns h) a = (grp_map h a ≈ grp_map h (grp_unit G)) := eq_refl.

(* NEGATIVE: it is not #313's kernel membership on the nose. *)
Fail Definition negative_kernel_strict {G K : GrpObject} (h : G ~{Grp}~> K)
  (a : carrier G) :
  sub_mem (kernel_ns h) a = sub_mem (KernelNS h) a := eq_refl.

(* * ** Negative 6: projection 函子 agree arrows, not 对象 （已译） *)

(* 相关说明。 （已译） *)
Example control_proj_fmap {G : GrpObject} (N : NormalSubgroup G)
  (a : carrier G) :
  @fmap _ _ (quot_to_deloop N ◯ deloop_quotient_proj N) ttt ttt a
    = @fmap _ _ (deloop_hom (quot_proj N)) ttt ttt a := eq_refl.

(* NEGATIVE: 对象 actions not. （已译） *)
Fail Definition negative_proj_fobj {G : GrpObject} (N : NormalSubgroup G)
  (x : grp_deloop G) :
  fobj[quot_to_deloop N ◯ deloop_quotient_proj N] x
    = fobj[deloop_hom (quot_proj N)] x := eq_refl.
