Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Poset.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(*
 nLab:      https://ncatlab.org/nlab/show/poset
 Wikipedia: https://en.wikipedia.org/wiki/Partially_ordered_set

   本文件为测试：Poset。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Poset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Poset_nat : Category :=
  Category.Instance.Poset.LessThanEqualTo_Category.

(*
   本节说明 Poset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition poset_nat_has_object : obj[Poset_nat] := 0%nat.

Example poset_nat_obj_is_nat : obj[Poset_nat] = nat := eq_refl.

Theorem poset_nat_is_inhabited : inhabited obj[Poset_nat].
Proof. exact (inhabits 0%nat). Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition poset_nat_id0 : (0 ~{Poset_nat}~> 0)%nat := @id Poset_nat 0%nat.

Definition poset_nat_hom_0_1 : (0 ~{Poset_nat}~> 1)%nat := le_S 0 0 (le_n 0).

Definition poset_nat_hom_1_2 : (1 ~{Poset_nat}~> 2)%nat := le_S 1 1 (le_n 1).

Definition poset_nat_comp_0_2 : (0 ~{Poset_nat}~> 2)%nat :=
  @compose Poset_nat 0%nat 1%nat 2%nat poset_nat_hom_1_2 poset_nat_hom_0_1.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition poset_nat_antisym : Antisymmetric nat eq PeanoNat.Nat.le :=
  partial_order_antisym PeanoNat.Nat.le_partialorder.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma poset_nat_skeletal :
  forall x y : obj[Poset_nat],
    (x ~{Poset_nat}~> y)%nat -> (y ~{Poset_nat}~> x)%nat -> x = y.
Proof. intros x y Hxy Hyx; exact (poset_nat_antisym x y Hxy Hyx). Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Inductive two : Type := lo | hi.

Definition two_le (x y : two) : Prop :=
  match x, y with
  | lo, _   => True
  | hi, hi  => True
  | hi, lo  => False
  end.

#[local] Instance two_le_preorder : PreOrder two_le.
Proof.
  constructor.
  - intros [|]; constructor.
  - intros [|] [|] [|]; simpl; auto.
Qed.

#[local] Instance two_le_antisym : @Antisymmetric two eq eq_equiv two_le.
Proof.
  intros [|] [|]; simpl; intros H1 H2;
    solve [ reflexivity | contradiction ].
Qed.

Definition Poset_two : Category := @Poset two two_le two_le_preorder two_le_antisym.

Definition poset_two_has_object : obj[Poset_two] := lo.

Example poset_two_obj_is_two : obj[Poset_two] = two := eq_refl.

Definition poset_two_hom : (lo ~{Poset_two}~> hi) := I.

Theorem poset_two_is_inhabited : inhabited obj[Poset_two].
Proof. exact (inhabits lo). Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma poset_two_skeletal :
  forall x y : obj[Poset_two],
    (x ~{Poset_two}~> y) -> (y ~{Poset_two}~> x) -> x = y.
Proof. intros x y Hxy Hyx; exact (two_le_antisym x y Hxy Hyx). Qed.

(*
   本节说明 Poset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma asym_preorder_forces_empty :
  forall (C : Type) (R : relation C),
    PreOrder R -> Asymmetric R -> C -> False.
Proof.
  intros C R P A x.
  pose proof (@reflexivity C R (@PreOrder_Reflexive C R P) x) as Hrefl.
  exact (A x x Hrefl Hrefl).
Qed.
