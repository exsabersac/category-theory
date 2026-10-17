(** * GL_n and the units functor *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Matr.
Require Import Category.Instance.Matr.Determinant.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 nLab:      https://ncatlab.org/nlab/show/general+linear+group
 Wikipedia: https://en.wikipedia.org/wiki/General_linear_group

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** The group units 幺半群 （已译） *)

Definition unit_carrier (M : MonObject) : Type :=
  { u : carrier M
  & { v : carrier M
    & (mon_op u v ≈ mon_unit) * (mon_op v u ≈ mon_unit) } }.

(*
   本节说明幺半群、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition UnitsOf (M : MonObject)
  (PM : PropEquiv (is_setoid (mon_setoid M))) : GrpObject := {|
  grp_setoid :=
    {| carrier := unit_carrier M;
       is_setoid := {| equiv := fun x y => `1 x ≈ `1 y |} |};
  grp_unit := (mon_unit; (mon_unit; (_, _)));
  grp_mul := fun x y =>
    (mon_op (`1 x) (`1 y); (mon_op (`1 (`2 y)) (`1 (`2 x)); (_, _)));
  grp_inv := fun x => (`1 (`2 x); (`1 x; (snd (`2 (`2 x)), fst (`2 (`2 x)))))
|}.
Next Obligation.
  intros M PM; equivalence.
Qed.
Next Obligation.
  intros M PM; apply mon_op_unit_l.
Qed.
Next Obligation.
  intros M PM; apply mon_op_unit_l.
Qed.
Next Obligation.
  (* (u·u')·(v'·v) ≈ 1 *)
  intros M PM [u [v [pl pr]]] [u' [v' [pl' pr']]]; simpl.
  rewrite <- mon_op_assoc.
  rewrite (mon_op_assoc u' v' v).
  rewrite pl'.
  rewrite mon_op_unit_l.
  exact pl.
Qed.
Next Obligation.
  (* (v'·v)·(u·u') ≈ 1 *)
  intros M PM [u [v [pl pr]]] [u' [v' [pl' pr']]]; simpl.
  rewrite <- mon_op_assoc.
  rewrite (mon_op_assoc v u u').
  rewrite pr.
  rewrite mon_op_unit_l.
  exact pr'.
Qed.
Next Obligation.
  intros M PM x y Hxy x' y' Hxy'; simpl.
  apply mon_op_respects; [ exact Hxy | exact Hxy' ].
Qed.
Next Obligation.
  intros M PM x y z; simpl.
  symmetry; apply mon_op_assoc.
Qed.
Next Obligation.
  intros M PM x; simpl.
  apply mon_op_unit_l.
Qed.
Next Obligation.
  intros M PM [u [v [pl pr]]]; simpl.
  exact pr.
Qed.
Next Obligation.
  (*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  intros M PM.
  unshelve refine (sigma_first_PropEquiv _ _ _ PM).
  - intros p q Hpq; exact Hpq.
  - intros p q Hpq; exact Hpq.
Defined.

(* 相关说明。 （已译） *)
Program Definition UnitsOf_map {M N : MonObject}
  {PM : PropEquiv (is_setoid (mon_setoid M))}
  {PN : PropEquiv (is_setoid (mon_setoid N))} (h : MonHom M N) :
  GrpHom (UnitsOf M PM) (UnitsOf N PN) := {|
  grp_map :=
    {| morphism := fun x =>
         (h (`1 x); (h (`1 (`2 x)); (_, _))) |}
|}.
Next Obligation.
  intros M N PM PN h [u [v [pl pr]]]; simpl.
  rewrite <- mon_map_op.
  rewrite pl.
  apply mon_map_unit.
Qed.
Next Obligation.
  intros M N PM PN h [u [v [pl pr]]]; simpl.
  rewrite <- mon_map_op.
  rewrite pr.
  apply mon_map_unit.
Qed.
Next Obligation.
  intros M N PM PN h x y Hxy; simpl.
  apply mon_map_respects; exact Hxy.
Qed.
Next Obligation.
  intros M N PM PN h; simpl.
  apply mon_map_unit.
Qed.
Next Obligation.
  intros M N PM PN h x y; simpl.
  apply mon_map_op.
Qed.

(* * ** The units 函子 commutative rings （已译） *)

(* The multiplicative monoid of a ring. *)
Program Definition Ring_mul_mon (K : RingObject) : MonObject := {|
  mon_setoid := rig_setoid (ring_rig K);
  mon_unit := rig_one (ring_rig K);
  mon_op := rig_mul (ring_rig K);
  mon_op_respects := rig_mul_respects (ring_rig K);
  mon_op_unit_l := rig_mul_one_l (ring_rig K);
  mon_op_unit_r := rig_mul_one_r (ring_rig K)
|}.
Next Obligation.
  intros K a b c; symmetry; apply rig_mul_assoc.
Qed.

(* A rig homomorphism is a monoid homomorphism of the multiplicative
   monoids. *)
Program Definition mul_MonHom {K K' : RingObject}
        (h : RigHom (ring_rig K) (ring_rig K')) :
  MonHom (Ring_mul_mon K) (Ring_mul_mon K') := {|
  mon_map := fun a => rig_map h a;
  mon_map_respects := proper_morphism (rig_map h)
|}.
Next Obligation.
  intros K K' h; apply rig_map_one.
Qed.
Next Obligation.
  intros K K' h a b; apply rig_map_mul.
Qed.

(* The witness [UnitsOf] asks at ring's multiplicative 幺半群: the
 幺半群's carrier setoid IS rig's, so it [rig_prop]. （已译） *)
Definition ring_mul_mon_prop (K : RingObject) :
  PropEquiv (is_setoid (mon_setoid (Ring_mul_mon K))) :=
  rig_prop (ring_rig K).

(* (−)^* : CRng ⟶ Grp — group units, functorially. A CRng
 态射 Subcategory hom: underlying RigHom carrying a
 (trivial) membership witness. （已译） *)
Program Definition Units_Functor : CRng ⟶ Grp := {|
  fobj := fun K => UnitsOf (Ring_mul_mon (`1 K)) (ring_mul_mon_prop (`1 K));
  fmap := fun K K' h => UnitsOf_map (mul_MonHom (`1 h))
|}.
Next Obligation.
  intros K K' f g Hfg [u [v p]]; simpl.
  exact (Hfg u).
Qed.
Next Obligation.
  intros K [u [v p]]; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros K K' K'' f g [u [v p]]; simpl.
  reflexivity.
Qed.

(* * ** The general linear group 函子 （已译） *)

(* The n × n matrix 幺半群 over ring: endomorphism 幺半群 the
 对象 n Matr. （已译） *)
Definition mat_mon (K : RingObject) (n : nat) : MonObject :=
  hom_monoid (Matr (ring_rig K)) n.

(* [Matr R]'s hom-setoid is entrywise `≈` in [R], so it is propositional
   whenever [R] is -- which it always is, [rig_prop] being a field.  Stated
   here rather than in Instance/Matr.v to keep the change local; it is the
   witness [UnitsOf] asks for at [mat_mon]. *)
Definition Matr_LocallyPropositional (R : RigObject) :
  LocallyPropositional (Matr R) :=
  LocallyPropositional_of_relation (Matr R)
    (fun n m A B => forall i j, @pequiv _ _ (rig_prop R) (A i j) (B i j))
    (fun n m A B H i j => pequiv_to _ _ (H i j))
    (fun n m A B H i j => pequiv_from _ _ (H i j)).

(* The witness [UnitsOf] asks at matrix 幺半群. （已译） *)
Definition mat_mon_prop (K : RingObject) (n : nat) :
  PropEquiv (is_setoid (mon_setoid (mat_mon K n))) :=
  @locally_prop (Matr (ring_rig K)) (Matr_LocallyPropositional (ring_rig K))
    n n.

(* Ring maps commute with finite sums: Determinant.v's
   [rig_map_fin_sum] (consumed, not rebuilt). *)

(* Ring maps preserve the Kronecker delta. *)
Lemma rig_map_delta {K K' : RigObject} (h : RigHom K K')
      {n : nat} (i j : Fin.t n) :
  rig_map h (delta K i j) ≈ delta K' i j.
Proof.
  unfold delta.
  destruct (Fin.eq_dec i j).
  - apply rig_map_one.
  - apply rig_map_zero.
Qed.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition mat_map_hom {K K' : RingObject}
        (h : RigHom (ring_rig K) (ring_rig K')) (n : nat) :
  MonHom (mat_mon K n) (mat_mon K' n) := {|
  mon_map := fun A => (fun i j => rig_map h (A i j))
             : @Matrix (ring_rig K') n n
|}.
Next Obligation.
  intros K K' h n A B HAB i j; simpl.
  apply (proper_morphism (rig_map h)); exact (HAB i j).
Qed.
Next Obligation.
  intros K K' h n i j; simpl.
  apply rig_map_delta.
Qed.
Next Obligation.
  intros K K' h n A B i j; simpl.
  rewrite (rig_map_fin_sum K K' h).
  apply fin_sum_respects; intro l.
  apply rig_map_mul.
Qed.

(* GL_n : CRng ⟶ Grp — invertible n × n matrices, functorially. *)
Program Definition GL_n (n : nat) : CRng ⟶ Grp := {|
  fobj := fun K => UnitsOf (mat_mon (`1 K) n) (mat_mon_prop (`1 K) n);
  fmap := fun K K' h => UnitsOf_map (mat_map_hom (`1 h) n)
|}.
Next Obligation.
  intros n K K' f g Hfg [A [B p]] i j; simpl.
  exact (Hfg (A i j)).
Qed.
Next Obligation.
  intros n K [A [B p]] i j; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros n K K' K'' f g [A [B p]] i j; simpl.
  reflexivity.
Qed.

(* * ** The determinant 自然变换 （已译） *)

(* det restricted unit groups: invertible matrix has unit
 determinant — inverse matrix's determinant inverts it, by
 multiplicativity det 恒等. （已译） *)
Program Definition det_GrpHom (n : nat) (K : obj[CRng]) :
  GrpHom (UnitsOf (mat_mon (`1 K) n) (mat_mon_prop (`1 K) n))
         (UnitsOf (Ring_mul_mon (`1 K)) (ring_mul_mon_prop (`1 K))) := {|
  grp_map := {| morphism := fun x =>
    (det (`1 K) (`1 x);
     (det (`1 K) (`1 (`2 x)); (_, _))) |}
|}.
Next Obligation.
  intros n K [A [B [pl pr]]]; simpl.
  rewrite <- (det_compose (`1 K) (`2 K) A B).
  etransitivity; [ apply (det_respects (`1 K)); exact pl | apply det_id ].
Qed.
Next Obligation.
  intros n K [A [B [pl pr]]]; simpl.
  rewrite <- (det_compose (`1 K) (`2 K) B A).
  etransitivity; [ apply (det_respects (`1 K)); exact pr | apply det_id ].
Qed.
Next Obligation.
  intros n K x y Hxy; simpl.
  apply (det_respects (`1 K)); exact Hxy.
Qed.
Next Obligation.
  intros n K; simpl.
  apply det_id.
Qed.
Next Obligation.
  intros n K x y; simpl.
  apply (det_compose (`1 K) (`2 K)).
Qed.

(*
   本节说明自然变换相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition det_Transform (n : nat) :
  GL_n n ⟹ Units_Functor := {|
  transform := fun K => det_GrpHom n K
|}.
Next Obligation.
  intros n K K' h [A [B p]]; simpl.
  apply (det_map (`1 K) (`1 K') (`1 h) A).
Qed.
Next Obligation.
  intros n K K' h [A [B p]]; simpl.
  symmetry.
  apply (det_map (`1 K) (`1 K') (`1 h) A).
Qed.
