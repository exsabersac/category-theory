Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.

Generalizable All Variables.

(** ** The opposite monoid, and delooping against duality *)

(*
   本文件给出反范畴、反函子或反自然变换（2-胞方向反转）。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition MonObject_op (M : MonObject) : MonObject := {|
  mon_setoid := mon_setoid M;
  mon_unit   := mon_unit;
  mon_op     := fun a b => mon_op b a;

  mon_op_respects := _;
  mon_op_assoc    := fun a b c => mon_op_assoc_sym M c b a;
  mon_op_unit_l   := fun a => mon_op_unit_r a;
  mon_op_unit_r   := fun a => mon_op_unit_l a
|}.
Next Obligation. now intros ?? H1 ?? H2; rewrite H1, H2. Qed.

(*
   本节说明 Opposite 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example MonObject_op_op_carrier (M : MonObject) :
  carrier (MonObject_op (MonObject_op M)) = carrier M := eq_refl.
Example MonObject_op_op_unit (M : MonObject) :
  @mon_unit (MonObject_op (MonObject_op M)) = @mon_unit M := eq_refl.
Example MonObject_op_op_op (M : MonObject) :
  @mon_op (MonObject_op (MonObject_op M)) = @mon_op M := eq_refl.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Deloop_op_to (M : MonObject) :
  (Deloop M)^op ⟶ Deloop (MonObject_op M) := {|
  fobj := fun x => x;
  fmap := fun _ _ f => f
|}.

Program Definition Deloop_op_from (M : MonObject) :
  Deloop (MonObject_op M) ⟶ (Deloop M)^op := {|
  fobj := fun x => x;
  fmap := fun _ _ f => f
|}.

(*
   本节说明函子、hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Deloop_op (M : MonObject) :
  (Deloop M)^op ≅[Cat] Deloop (MonObject_op M) := {|
  to   := Deloop_op_to M;
  from := Deloop_op_from M
|}.
(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Next Obligation.
  exists (fun _ => iso_id); simpl; intros.
  now rewrite mon_op_unit_r, mon_op_unit_l.
Qed.
Next Obligation.
  exists (fun _ => iso_id); simpl; intros.
  now rewrite mon_op_unit_r, mon_op_unit_l.
Qed.

(* The group case transports too. *)
Definition GrpObject_op (G : GrpObject) : GrpObject := {|
  grp_monoid := MonObject_op (grp_monoid G);
  grp_inv    := grp_inv (g:=G);
  grp_inv_l  := fun a => grp_inv_r (g:=G) a;
  grp_inv_r  := fun a => grp_inv_l (g:=G) a
|}.

(*
   本节说明函子、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Deloop_op_strict (M : MonObject) :
  (Deloop M)^op ≅[StrictCat] Deloop (MonObject_op M) := {|
  to   := Deloop_op_to M;
  from := Deloop_op_from M
|}.
(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
