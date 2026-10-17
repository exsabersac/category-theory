(*
   本文件为测试：ProbeGroupRepr341。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Group.
Require Import Category.Structure.Group.Representable.

Generalizable All Variables.

(* * ** Negatives 1-3 (FORMABILITY): three donors identify hom 证明 （已译） *)

Section Donors.

Universe uo uh up.
Constraint uh < up.

(* Control: a hom-set of such a category is perfectly formable here. *)
Check (fun (C : Category@{uo uh up}) (x y : C) => x ~> y).

(* Controls: each guarded donor exists at UNCONSTRAINED levels.  Without
   these, a rename of any of them would leave its negative succeeding on a
   reference-not-found error rather than on the universe boundary. *)
Check @Cartesian.
Check @Terminal.
Check @GroupObject.
Check @HomGroupData.

(* NEGATIVE 1. *)
Fail Check (fun (C : Category@{uo uh up}) => @Cartesian C).

(* NEGATIVE 2. *)
Fail Check (fun (C : Category@{uo uh up}) => @Terminal C).

(* NEGATIVE 3.  [HomGroupData] is the target's OWN central record, and
   unlike [GroupObject] it takes no monoidal argument -- its signature is
   [forall {C : Category}, obj[C] -> Type] -- so the rejection is
   attributable to it rather than to something elaborated before it. *)
Fail Check (fun (C : Category@{uo uh up}) (e : C) => @HomGroupData C e).

End Donors.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition probe_homgroupdata_binder
  `{C : Category} (e : C) : Type := HomGroupData e.

(* About probe_homgroupdata_binder.
   About HomGroupData.
     HomGroupData@{u u0} :
       forall {C : Category@{u u0 u0}}, obj -> Type@{max(u,u0)}
     (* u u0 |=  *)                      <-- EMPTY block
                    ^^^^^^^^^^^^^^^^^^   <-- hom = proof in the BINDER *)

(*
   本节说明 ProbeGroupRepr341 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
