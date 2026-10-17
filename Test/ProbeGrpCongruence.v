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

(** ** Negative 1: the two groupoid witnesses are not the same term *)

(* POSITIVE CONTROL: the record conversion deloops to the tree's own
   delooping, and the chosen inverses agree, both by [eq_refl]. *)
Example control_deloop_agrees (H : GrpObject) :
  Deloop (grp_deloop_GrpObject H) = grp_deloop H := eq_refl.

Example control_ginv_agrees (H : GrpObject) (a : carrier H) :
  ginv (grp_deloop_IsGroupoid' H) (x:=ttt) (y:=ttt) a = grp_inv H a := eq_refl.

(* ...and for the OTHER witness too, so that "the data agree" is about
   both of the terms the negative separates and not just one of them. *)
Example control_ginv_agrees_Free (H : GrpObject) (a : carrier H) :
  ginv (grp_deloop_IsGroupoid H) (x:=ttt) (y:=ttt) a = grp_inv H a := eq_refl.

(* NEGATIVE: the whole [IsGroupoid] structures are not convertible. *)
Fail Definition negative_isgroupoid_record (H : GrpObject) :
  grp_deloop_IsGroupoid' H = grp_deloop_IsGroupoid H := eq_refl.

(** ** Negative 2: the membership round trip is a biconditional *)

(* POSITIVE CONTROL: what the recovered membership DOES convert to. *)
Example control_round_unfolds {G : GrpObject} (N : NormalSubgroup G)
  (a : carrier G) :
  sub_mem (@cong_ns G (ns_rel N) (ns_congruence N)) a
    = quot_rel N a (grp_unit G) := eq_refl.

(* NEGATIVE: it is not membership in N on the nose. *)
Fail Definition negative_round_strict {G : GrpObject} (N : NormalSubgroup G)
  (a : carrier G) :
  sub_mem (@cong_ns G (ns_rel N) (ns_congruence N)) a = sub_mem N a := eq_refl.

(** ** Negative 3: the quotient category is not the delooping, on the nose *)

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

(* NEGATIVE: the whole categories are not convertible. *)
Fail Definition negative_quotient_category {G : GrpObject}
  (N : NormalSubgroup G) :
  deloop_quotient N = grp_deloop (QuotientGrp N) := eq_refl.

(** ** Negative 4: the two mediators agree on the map, not as records *)

(* POSITIVE CONTROL: the underlying maps are the same term. *)
Example control_med_map {G K : GrpObject} (N : NormalSubgroup G)
  (p : Kills N K) (a : carrier (QuotientGrp N)) :
  grp_map (cat_med N p) a = grp_map (quot_med N p) a := eq_refl.

(* NEGATIVE: the homomorphism records are not. *)
Fail Definition negative_med_record {G K : GrpObject} (N : NormalSubgroup G)
  (p : Kills N K) : cat_med N p = quot_med N p := eq_refl.

(** ** Negative 5: the categorical kernel is coextensive, not equal *)

(* POSITIVE CONTROL: what the categorical kernel's membership IS. *)
Example control_kernel_unfolds {G K : GrpObject} (h : G ~{Grp}~> K)
  (a : carrier G) :
  sub_mem (kernel_ns h) a = (grp_map h a ≈ grp_map h (grp_unit G)) := eq_refl.

(* NEGATIVE: it is not #313's kernel membership on the nose. *)
Fail Definition negative_kernel_strict {G K : GrpObject} (h : G ~{Grp}~> K)
  (a : carrier G) :
  sub_mem (kernel_ns h) a = sub_mem (KernelNS h) a := eq_refl.

(** ** Negative 6: the projection functors agree on arrows, not on objects *)

(* POSITIVE CONTROL: the arrow actions are the same term. *)
Example control_proj_fmap {G : GrpObject} (N : NormalSubgroup G)
  (a : carrier G) :
  @fmap _ _ (quot_to_deloop N ◯ deloop_quotient_proj N) ttt ttt a
    = @fmap _ _ (deloop_hom (quot_proj N)) ttt ttt a := eq_refl.

(* NEGATIVE: the object actions are not. *)
Fail Definition negative_proj_fobj {G : GrpObject} (N : NormalSubgroup G)
  (x : grp_deloop G) :
  fobj[quot_to_deloop N ◯ deloop_quotient_proj N] x
    = fobj[deloop_hom (quot_proj N)] x := eq_refl.
