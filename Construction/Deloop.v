Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* * * Delooping: monoids one-对象 范畴 （已译） *)

(*
   nLab:      https://ncatlab.org/nlab/show/monoid
   nLab:      https://ncatlab.org/nlab/show/groupoid
   Wikipedia: https://en.wikipedia.org/wiki/Monoid
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Book:      Awodey, "Category Theory", 2nd ed., §1.4, pp. 12-13
   Book:      Riehl, "Category Theory in Context", Example 1.1.4(ii), pp. 5-6
   Book:      Fong, Spivak, "Seven Sketches in Compositionality", CUP 2019,

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record MonObject := {
  mon_setoid :> SetoidObject;

  mon_unit : carrier mon_setoid;
  mon_op : carrier mon_setoid → carrier mon_setoid → carrier mon_setoid;

  mon_op_respects : Proper (equiv ==> equiv ==> equiv) mon_op;

  mon_op_assoc : ∀ a b c,
    mon_op a (mon_op b c) ≈ mon_op (mon_op a b) c;
  mon_op_unit_l : ∀ a, mon_op mon_unit a ≈ a;
  mon_op_unit_r : ∀ a, mon_op a mon_unit ≈ a
}.

#[export] Existing Instance mon_op_respects.

Arguments mon_unit {_}.
Arguments mon_op {_} _ _.
Arguments mon_op_assoc {_} _ _ _.
Arguments mon_op_unit_l {_} _.
Arguments mon_op_unit_r {_} _.

(* 相关说明。 （已译） *)
Corollary mon_op_assoc_sym (M : MonObject) (a b c : carrier M) :
  mon_op (mon_op a b) c ≈ mon_op a (mon_op b c).
Proof.
  symmetry.
  apply mon_op_assoc.
Qed.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma mon_inverse_unique (M : MonObject) (a b c : carrier M) :
  mon_op b a ≈ mon_unit → mon_op a c ≈ mon_unit → b ≈ c.
Proof.
  intros Hba Hac.
  rewrite <- (mon_op_unit_r b).
  rewrite <- Hac.
  rewrite (mon_op_assoc b a c).
  rewrite Hba.
  apply mon_op_unit_l.
Qed.

(* * ** Mac Lane's construction 3: one-对象 范畴 B M （已译） *)

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Deloop (M : MonObject) : Category := {|
  obj     := poly_unit;                        (* the single object *)
  hom     := fun _ _ => carrier M;             (* arrows are elements of M *)
  homset  := fun _ _ => is_setoid M;           (* `≈` is the carrier's own *)
  id      := fun _ => mon_unit;                (* identity is the unit *)
  compose := fun _ _ _ f g => mon_op f g;      (* composition is the product *)

  compose_respects := fun _ _ _ => mon_op_respects M;

  id_left  := fun _ _ => mon_op_unit_l;
  id_right := fun _ _ => mon_op_unit_r;

  comp_assoc     := fun _ _ _ _ => mon_op_assoc;
  comp_assoc_sym := fun _ _ _ _ => mon_op_assoc_sym M
|}.

(* * ** The converse: endomorphism 幺半群 hom(a, a) （已译） *)

(*
   本节说明hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition hom_monoid (C : Category) (a : C) : MonObject := {|
  mon_setoid := {| carrier := a ~> a; is_setoid := @homset C a a |};

  mon_unit := id;
  mon_op   := fun f g => f ∘ g;

  mon_op_respects := @compose_respects C a a a;

  mon_op_assoc  := fun f g h => comp_assoc f g h;
  mon_op_unit_l := @id_left C a a;
  mon_op_unit_r := @id_right C a a
|}.

(* 相关说明。 （已译） *)

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example hom_monoid_Deloop (M : MonObject) : hom_monoid (Deloop M) ttt = M :=
  eq_refl.

(* 相关说明。 （已译） *)
Example hom_monoid_Deloop_carrier (M : MonObject) :
  carrier (hom_monoid (Deloop M) ttt) = carrier M := eq_refl.

Example hom_monoid_Deloop_unit (M : MonObject) :
  @mon_unit (hom_monoid (Deloop M) ttt) = @mon_unit M := eq_refl.

Example hom_monoid_Deloop_op (M : MonObject) :
  @mon_op (hom_monoid (Deloop M) ttt) = @mon_op M := eq_refl.

(* 相关说明。 （已译） *)

(*
   本节说明幺半结构、幺半群、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record GrpObject := {
  grp_monoid :> MonObject;

  grp_inv : carrier grp_monoid → carrier grp_monoid;

  grp_inv_l : ∀ a, mon_op (grp_inv a) a ≈ mon_unit;
  grp_inv_r : ∀ a, mon_op a (grp_inv a) ≈ mon_unit
}.

Arguments grp_inv {_} _.
Arguments grp_inv_l {_} _.
Arguments grp_inv_r {_} _.

(*
   本节说明 Deloop 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance grp_inv_respects (G : GrpObject) :
  Proper (equiv ==> equiv) (@grp_inv G).
Proof.
  intros a b Hab.
  assert (Hinv : mon_op (grp_inv a) b ≈ mon_unit).
  { rewrite <- Hab.
    apply grp_inv_l. }
  exact (mon_inverse_unique G b (grp_inv a) (grp_inv b) Hinv (grp_inv_r b)).
Qed.

(*
   本节说明幺半群、（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Obligation Tactic := idtac.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Program Instance Deloop_group_invertible (G : GrpObject)
  (x y : Deloop G) (f : x ~{Deloop G}~> y) : IsIsomorphism f := {
  two_sided_inverse := grp_inv f    (* 相关说明。 （已译） *)
}.
Next Obligation.
  intros G x y f.                   (* f ∘ f⁻¹ ≈ id  is  a * a⁻¹ ≈ 1 *)
  apply grp_inv_r.
Qed.
Next Obligation.
  intros G x y f.                   (* f⁻¹ ∘ f ≈ id  is  a⁻¹ * a ≈ 1 *)
  apply grp_inv_l.
Qed.

(* The same statement 对象 form: any two 对象 [Deloop G] (there is
 one) isomorphic, each element G names such 同构. （已译） *)
Definition Deloop_group_iso (G : GrpObject) (x y : Deloop G)
  (f : x ~{Deloop G}~> y) : x ≅ y :=
  IsIsoToIso f (Deloop_group_invertible G x y f).

(** ** Witnesses *)

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma nat_add_assoc (a b c : nat) : (a + (b + c))%nat = ((a + b) + c)%nat.
Proof.
  induction a; simpl; [reflexivity | now rewrite IHa].
Qed.

Lemma nat_add_0_r (a : nat) : (a + 0)%nat = a.
Proof.
  induction a; simpl; [reflexivity | now rewrite IHa].
Qed.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Nat_Plus : MonObject := {|
  mon_setoid := {| carrier := nat; is_setoid := nat_setoid |};
  mon_unit   := 0%nat;
  mon_op     := Nat.add
|}.
Next Obligation.
  intros a b c.
  apply nat_add_assoc.
Qed.
Next Obligation.
  intros a; reflexivity.            (* 0 + a is a by computation *)
Qed.
Next Obligation.
  intros a.
  apply nat_add_0_r.
Qed.

(* (bool, xor, false): the underlying monoid of Z/2, over Leibniz equality on
   [bool]. *)
Program Definition Bool_Xor : MonObject := {|
  mon_setoid := {| carrier := bool
                 ; is_setoid := {| equiv := eq
                                 ; setoid_equiv := eq_equivalence |} |};
  mon_unit   := false;
  mon_op     := xorb
|}.
Next Obligation.
  intros a b c; now destruct a, b, c.
Qed.
Next Obligation.
  intros a; now destruct a.
Qed.
Next Obligation.
  intros a; now destruct a.
Qed.

(* Z/2 as a group: every element is its own inverse. *)
Program Definition Bool_Xor_Grp : GrpObject := {|
  grp_monoid := Bool_Xor;
  grp_inv    := fun b => b
|}.
Next Obligation.
  intros a; now destruct a.
Qed.
Next Obligation.
  intros a; now destruct a.
Qed.

(*
   本节说明hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example deloop_nat_compose (a b : Nat_Plus) :
  @compose (Deloop Nat_Plus) ttt ttt ttt a b = (a + b)%nat := eq_refl.

(* 相关说明。 （已译） *)
Example deloop_bool_inverse (b : Bool_Xor_Grp) :
  two_sided_inverse
    (IsIsomorphism:=Deloop_group_invertible Bool_Xor_Grp ttt ttt b) = b
  := eq_refl.
