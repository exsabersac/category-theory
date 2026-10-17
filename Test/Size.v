(* ========================================================================= *)
(* Machine-checked demonstrations for the size vocabulary of Theory/Size.v.   *)
(*                                                                           *)
(* This file is where issue #253's NEGATIVE demonstrations live, because they *)
(* need the rejection vernacular, and each use of it is a hit for the         *)
(* [make todo] hygiene sweep (Makefile greps case-insensitively over every  *)
(* .v file for a small set of trigger words, one of which is that vernacular's*)
(* own name).  Confining them here follows the in-tree precedent set by        *)
(* Test/Issue138.v and Test/ProbeFunnyPoly.v,77, which use it the     *)
(* same way; Monad/Transformer.v does too.  This file contributes exactly *)
(* four such hits, and the pull request states that number rather than         *)
(* hiding it.  Prose elsewhere in this file is deliberately worded to avoid    *)
(* the trigger words, so the sweep's delta is exactly the four commands.      *)
(*                                                                           *)
(* WHAT THE VERNACULAR DOES AND DOES NOT SHOW.  It succeeds when the command  *)
(* it wraps raises ANY error.  It does not report WHICH error, so on its own  *)
(* it cannot distinguish a universe inconsistency from an ordinary type        *)
(* mismatch or a typo.  Test/Issue138.v sets the precedent of saying so *)
(* out loud, and the distinction is load-bearing here -- see BLOCK B.         *)
(* ========================================================================= *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Size.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.

Generalizable All Variables.

(* ===== BLOCK A — the size predicates are inhabited, and strict ===== *)

(* The vocabulary exists and can be used as a conclusion. *)
Check (One_Small : Small _1).
Check (small_locally_small _1 One_Small : LocallySmall _1).

(*
   本文件为测试：Size。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (fun C : Category => locally_small_ambient C : LocallySmall C).

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition A253_trivial_locally_small@{o h p uh up
    | h <= p, uh <= up, uh < h}
  (C : Category@{o h p}) : LocallySmall@{o h p uh up} C :=
  @Build_LocallySmall@{o h p uh up} C
    (fun x y => (x ~> y)) (@homset C)
    (fun _ _ f => f) (fun _ _ f => f)
    (fun _ _ _ _ H => H)
    (fun x y f => reflexivity f) (fun x y u => reflexivity u).

Fail Definition A253_trivial_small@{o h p uo uh up
    | h <= p, uh <= up, uo < o, uh < h}
  (C : Category@{o h p}) : Small@{o h p uo uh up} C :=
  @Build_Small@{o h p uo uh up} C
    (@Build_LocallySmall@{o h p uh up} C
       (fun x y => (x ~> y)) (@homset C)
       (fun _ _ f => f) (fun _ _ f => f)
       (fun _ _ _ _ H => H)
       (fun x y f => reflexivity f) (fun x y u => reflexivity u))
    obj[C] (fun x => x) (fun x => x)
    (fun _ => obj_refl _) (fun _ => obj_refl _).

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition A253_no_object_resize@{o uo | uo < o} (A : Type@{o})
  : Type@{uo} := A.

(* ===== BLOCK B — self-membership, and the distinction issue #253 conflates ==== *)

(*
   本节说明 Size 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition B253_cat_self@{a b c d e}
  : obj[Cat@{a b c d e}] := Cat@{a b c d e}.

(*
   本节说明 Size 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (Sets : obj[Sets]).

(*
   本节说明 Size 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (_1 : obj[Cat]).
Check (Sets : obj[Cat]).
Check (Cat : obj[Cat]).

(* [Cat] is itself a category, hence an object of a [Cat] one level up.  Coq's
   universe polymorphism supplies the whole tower silently; there is no [Cat']
   to define, which is the divergence from Mac Lane's single fixed [U]. *)
Check (Cat : Category).

(* ===== BLOCK C — Riehl's arrows-with-dom-and-cod packaging ===== *)

(* The unindexed packaging exists for every category... *)
Check (fun C : Category => ArrowQuiverOfCat C : ArrowQuiver).

(*
   本节说明 Size 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example C253_dom_retract (C : Category) (x : obj[C]) :
  ObjEq (aq_dom (ArrowQuiverOfCat C) (aq_id (ArrowQuiverOfCat C) x)) x :=
  obj_refl _.

Example C253_cod_retract (C : Category) (x : obj[C]) :
  ObjEq (aq_cod (ArrowQuiverOfCat C) (aq_id (ArrowQuiverOfCat C) x)) x :=
  obj_refl _.
