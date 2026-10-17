(* * * Products 范畴 subsume classical products （已译） *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Cat.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   nLab:      https://ncatlab.org/nlab/show/product+category

   本文件给出积（分量）构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)


(* * ** The product 幺半群, product group （已译） *)

(*
   本节说明 Special 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition prod_SetoidObject (M N : MonObject) : SetoidObject := {|
  carrier := carrier M * carrier N;
  is_setoid := @prod_setoid _ _ (is_setoid M) (is_setoid N)
|}.

Program Definition MonObject_prod (M N : MonObject) : MonObject := {|
  mon_setoid := prod_SetoidObject M N;
  mon_unit := (mon_unit, mon_unit);
  mon_op := fun p q => (mon_op (fst p) (fst q), mon_op (snd p) (snd q))
|}.
Next Obligation.
  intros M N p p' [Hp1 Hp2] q q' [Hq1 Hq2]; split; simpl.
  - exact (mon_op_respects M _ _ Hp1 _ _ Hq1).
  - exact (mon_op_respects N _ _ Hp2 _ _ Hq2).
Qed.
Next Obligation.
  intros M N a b c; split; simpl; apply mon_op_assoc.
Qed.
Next Obligation.
  intros M N a; split; simpl; apply mon_op_unit_l.
Qed.
Next Obligation.
  intros M N a; split; simpl; apply mon_op_unit_r.
Qed.

Program Definition GrpObject_prod (G H : GrpObject) : GrpObject := {|
  grp_monoid := MonObject_prod G H;
  grp_inv := fun p => (grp_inv (fst p), grp_inv (snd p))
|}.
Next Obligation.
  intros G H a; split; simpl; apply grp_inv_l.
Qed.
Next Obligation.
  intros G H a; split; simpl; apply grp_inv_r.
Qed.

Example GrpObject_prod_monoid (G H : GrpObject) :
  grp_monoid (GrpObject_prod G H) = MonObject_prod G H := eq_refl.

(** ** Delooping preserves products *)

(* Both 函子 恒等 arrows (design note 1); the
 single 对象 need shuttling. （已译） *)
Program Definition Deloop_prod_to (M N : MonObject) :
  Deloop (MonObject_prod M N) ⟶ Deloop M ∏ Deloop N := {|
  fobj := fun _ => (ttt, ttt);
  fmap := fun _ _ p => p
|}.
Next Obligation.
  intros M N x y p q Hpq; exact Hpq.
Qed.
Next Obligation.
  intros M N x; simpl; split; reflexivity.
Qed.
Next Obligation.
  intros M N x y z p q; simpl; split; reflexivity.
Qed.

Program Definition Deloop_prod_from (M N : MonObject) :
  Deloop M ∏ Deloop N ⟶ Deloop (MonObject_prod M N) := {|
  fobj := fun _ => ttt;
  fmap := fun _ _ p => p
|}.
Next Obligation.
  intros M N x y p q Hpq; exact Hpq.
Qed.
Next Obligation.
  intros M N x; simpl; split; reflexivity.
Qed.
Next Obligation.
  intros M N x y z p q; simpl; split; reflexivity.
Qed.

(* The 同构 Cat: composites 恒等 arrows, and
 对象 round trips closed unit-态射 conjugation. （已译） *)
Program Definition Deloop_prod_iso (M N : MonObject) :
  Deloop (MonObject_prod M N) ≅[Cat] Deloop M ∏ Deloop N := {|
  to   := Deloop_prod_to M N;
  from := Deloop_prod_from M N
|}.
Next Obligation.
  intros M N; unshelve eexists.
  - intros [a b].
    unshelve refine
      (@Build_Isomorphism (Deloop M ∏ Deloop N) (ttt, ttt) (a, b)
         (mon_unit, mon_unit) (mon_unit, mon_unit) _ _).
    + split; simpl; apply mon_op_unit_l.
    + split; simpl; apply mon_op_unit_l.
  - intros [a b] [c d] [f g]; simpl; split;
    exact (symmetry
             (transitivity (mon_op_unit_r _) (mon_op_unit_l _))).
Qed.
Next Obligation.
  intros M N; unshelve eexists.
  - intros x.
    unshelve refine
      (@Build_Isomorphism (Deloop (MonObject_prod M N)) ttt x
         (mon_unit, mon_unit) (mon_unit, mon_unit) _ _).
    + split; simpl; apply mon_op_unit_l.
    + split; simpl; apply mon_op_unit_l.
  - intros x y p; simpl; split;
    exact (symmetry
             (transitivity (mon_op_unit_r _) (mon_op_unit_l _))).
Qed.

(*
   本节说明幺半群、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Deloop_grp_prod (G H : GrpObject) :
  Deloop (GrpObject_prod G H) ≅[Cat] Deloop G ∏ Deloop H :=
  Deloop_prod_iso G H.

(* * ** Discrete 范畴 multiply sets （已译） *)

Program Definition Discrete_Product_to (A B : Type) :
  DiscreteCat (A * B) ⟶ DiscreteCat A ∏ DiscreteCat B := {|
  fobj := fun p => p;
  fmap := fun x y e => (f_equal fst e, f_equal snd e)
|}.
Next Obligation.
  intros A B x; simpl; split; reflexivity.
Qed.
Next Obligation.
  intros A B x y z e e'; simpl.
  destruct e, e'; simpl; split; reflexivity.
Qed.

(* Transparent equality kit pairs: stdlib's [surjective_pairing]
 [f_equal2] opaque, would leave arrow action stuck
 sink every 函子 law; these compute. （已译） *)
Definition pair_eta {A B : Type} (p : A * B) : p = (fst p, snd p) :=
  match p with (a, b) => eq_refl end.

Definition pair_equal {A B : Type} {a c : A} {b d : B}
  (e1 : a = c) (e2 : b = d) : (a, b) = (c, d) :=
  match e1 in _ = c', e2 in _ = d' return (a, b) = (c', d') with
  | eq_refl, eq_refl => eq_refl
  end.

Program Definition Discrete_Product_from (A B : Type) :
  DiscreteCat A ∏ DiscreteCat B ⟶ DiscreteCat (A * B) := {|
  fobj := fun p => p;
  fmap := fun x y e =>
    eq_trans (pair_eta x)
      (eq_trans (pair_equal (fst e) (snd e))
         (eq_sym (pair_eta y)))
|}.
Next Obligation.
  intros A B x y e e' He; simpl in *.
  destruct He as [He1 He2]; simpl in *.
  rewrite He1, He2; reflexivity.
Qed.
Next Obligation.
  intros A B [a b]; simpl; reflexivity.
Qed.
Next Obligation.
  intros A B [a b] [c d] [e f] p q; simpl.
  destruct p as [p1 p2], q as [q1 q2]; simpl in *.
  destruct p1, p2, q1, q2; simpl; reflexivity.
Qed.

Program Definition Discrete_Product (A B : Type) :
  DiscreteCat (A * B) ≅[Cat] DiscreteCat A ∏ DiscreteCat B := {|
  to   := Discrete_Product_to A B;
  from := Discrete_Product_from A B
|}.
Next Obligation.
  intros A B; exists (fun p => iso_id).
  intros [a b] [c d] [e1 e2]; simpl in *.
  destruct e1, e2; simpl; split; reflexivity.
Qed.
Next Obligation.
  intros A B; exists (fun x => iso_id).
  intros x y e; simpl.
  destruct e; simpl.
  destruct x; simpl; reflexivity.
Qed.

(** ** Witnesses *)

(* The product 幺半群 computes at Construction/Deloop.v's inhabitants,
 discrete comparison 恒等 concrete pair. （已译） *)
Example MonObject_prod_computes :
  @mon_op (MonObject_prod Nat_Plus Bool_Xor) (3%nat, true) (2%nat, true)
    = (5%nat, false) := eq_refl.

Example Discrete_Product_computes :
  fobj[to (Discrete_Product bool nat)] (true, 7%nat)
    = (true, 7%nat) := eq_refl.
