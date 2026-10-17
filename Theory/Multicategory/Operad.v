Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Multicategory.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(** * Operads as one-object multicategories *)

(*
 nLab: https://ncatlab.org/nlab/show/operad

   本文件给出 operad 相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The transport helper and the bundled record *)

(*
   本节说明相关定义、性质与动机。 Transport inhabitant [poly_unit] along Type equality. Stated.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition unit_transport {A : Type} (e : poly_unit = A) : A :=
  match e in _ = T return T with eq_refl => ttt end.

(* Any type equal to [poly_unit] is contractible onto the transported
   point.  No UIP: [destruct e] abstracts the variable endpoint, and
   [poly_unit] has a single constructor. *)
Lemma unit_transport_contr {A : Type} (e : poly_unit = A) (x : A) :
  x = unit_transport e.
Proof.
  destruct e.
  now destruct x.
Qed.

(* The one-object condition: [=] on the Type-level colour data. *)
Definition IsOperad (M : Multicategory) : Type :=
  @mobj M = poly_unit.

Record Operad : Type := {
  operad_multi : Multicategory;
  operad_one : IsOperad operad_multi
}.

(** ** The derived point and object contractibility *)

(* The unique colour of the operad.  When [operad_one] is [eq_refl]
   (colour type [poly_unit] on the nose), this reduces to [ttt]. *)
Definition operad_pt (O : Operad) : @mobj (operad_multi O) :=
  unit_transport (eq_sym (operad_one O)).

(* Every object of an operad is the point. *)
Lemma operad_obj_contr (O : Operad) (x : @mobj (operad_multi O)) :
  x = operad_pt O.
Proof.
  apply unit_transport_contr.
Qed.

(*
   Every LIST of 对象 of an operad is a [repeat] of the point: the

   本节说明相关定义、性质与动机。 list-level face contractibility, equality along which round trip below recasts. [Defined] so [f_equal2] spine computes list constructors;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition all_repeat (O : Operad) (Γ : list (@mobj (operad_multi O))) :
  Γ = repeat (operad_pt O) (length Γ).
Proof.
  induction Γ as [|a Γ IH]; simpl.
  - reflexivity.
  - exact (f_equal2 cons (operad_obj_contr O a) IH).
Defined.

(*
   本节说明相关定义、性质与动机。 * ** The transparent repeat-arithmetic kit. The stdlib's [repeat_app] is stated concatenation right is opaque some supported versions;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fixpoint repeat_app_t {A : Type} (x : A) (m n : nat) :
  repeat x (m + n) = repeat x m ++ repeat x n :=
  match m with
  | O => eq_refl
  | S m' => f_equal (cons x) (repeat_app_t x m' n)
  end.

(** ** Arity accessors *)

Section OperadAccessors.

Context (O : Operad).

Local Notation MO := (operad_multi O).
Local Notation pt := (operad_pt O).

(* The setoid of n-ary operations. *)
Definition ohom (n : nat) : Type := @mhom MO (repeat pt n) pt.

#[export] Instance ohom_setoid (n : nat) : Setoid (ohom n) :=
  @mhomset MO (repeat pt n) pt.

(* The unary identity operation: [repeat pt 1] is [[pt]] on the nose. *)
Definition oid : ohom 1 := @mid MO pt.

(*
   本节说明相关定义、性质与动机。 * *** The round trip. Every multimorphism underlying 多元范畴 whose target is point is n-ary operation, [n := length Γ], recasting along [all_repeat];

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition to_ohom {Γ : list (@mobj MO)} (f : @mhom MO Γ pt) :
  ohom (length Γ) :=
  @mcast MO _ _ pt (all_repeat O Γ) f.

Definition of_ohom {Γ : list (@mobj MO)} (g : ohom (length Γ)) :
  @mhom MO Γ pt :=
  @mcast MO _ _ pt (eq_sym (all_repeat O Γ)) g.

#[export] Instance to_ohom_respects {Γ : list (@mobj MO)} :
  Proper (equiv ==> equiv) (@to_ohom Γ).
Proof. apply mcast_respects. Qed.

#[export] Instance of_ohom_respects {Γ : list (@mobj MO)} :
  Proper (equiv ==> equiv) (@of_ohom Γ).
Proof. apply mcast_respects. Qed.

Lemma operad_roundtrip {Γ : list (@mobj MO)} (f : @mhom MO Γ pt) :
  of_ohom (to_ohom f) ≈ f.
Proof. apply mcast_symm_l. Qed.

Lemma operad_roundtrip_inv {Γ : list (@mobj MO)} (g : ohom (length Γ)) :
  to_ohom (of_ohom g) ≈ g.
Proof. apply mcast_symm_r. Qed.

(*
   * *** Single-slot operadic 复合

   本节说明相关定义、性质与动机。 The classical [∘ᵢ]: splice n-ary operation into (i+1)-st input (i + 1 + j)-ary operation, yielding (i + (n + j))-ary operation.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The zipper form of a repeated context: [repeat pt (S j)] is
   [pt :: repeat pt j] on the nose, so [repeat_app_t] already has the
   stated type up to conversion. *)
Definition orep_zip (i j : nat) :
  repeat pt (i + S j) = repeat pt i ++ pt :: repeat pt j :=
  repeat_app_t pt i (S j).

(* Renormalising a three-block spliced context to [repeat] form. *)
Definition orep_splice (i n j : nat) :
  repeat pt i ++ repeat pt n ++ repeat pt j = repeat pt (i + (n + j)) :=
  eq_sym (eq_trans (repeat_app_t pt i (n + j))
                   (f_equal (app (repeat pt i)) (repeat_app_t pt n j))).

Definition ocomp {i j n : nat} (f : ohom (i + S j)) (g : ohom n) :
  ohom (i + (n + j)) :=
  @mcast MO _ _ pt (orep_splice i n j)
    (@mcomp MO (repeat pt i) (repeat pt j) (repeat pt n) pt pt
       (@mcast MO _ _ pt (orep_zip i j) f) g).

#[export] Instance ocomp_respects {i j n : nat} :
  Proper (equiv ==> equiv ==> equiv) (@ocomp i j n).
Proof.
  intros f f' ef g g' eg; unfold ocomp.
  now rewrite ef, eg.
Qed.

(*
   * *** The 对称-group action on arities

   本节说明相关定义、性质与动机。 Self-permutations repeated context [repeat pt n] act n-ary operations. The witnesses are Type-valued [tperm] Theory/多元范畴.v — index class's own action;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition osym {n : nat} (p : tperm (repeat pt n) (repeat pt n)) :
  ohom n → ohom n :=
  @msym MO _ _ pt p.

#[export] Instance osym_respects {n : nat}
  (p : tperm (repeat pt n) (repeat pt n)) :
  Proper (equiv ==> equiv) (@osym n p).
Proof. apply msym_respects. Qed.

Lemma osym_id {n : nat} (f : ohom n) :
  osym (tperm_refl (repeat pt n)) f ≈ f.
Proof. apply msym_id. Qed.

Lemma osym_compose {n : nat} (p q : tperm (repeat pt n) (repeat pt n))
  (f : ohom n) :
  osym q (osym p f) ≈ osym (tperm_trans p q) f.
Proof. apply msym_compose. Qed.

End OperadAccessors.

