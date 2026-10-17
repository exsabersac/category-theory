(* * * The converse [Full_Implies_Full_Functor] needs 假设 （已译） *)

(*
   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

Definition nz (n : nat) : bool := match n with O => true | S _ => false end.

Lemma nz_add : forall m n, nz (m + n) = andb (nz m) (nz n).
Proof. destruct m; simpl; auto. Qed.

#[local] Obligation Tactic := idtac.

Program Definition NZ : Category := {|
  obj     := unit;
  hom     := fun _ _ => nat;
  homset  := fun _ _ => {| equiv := fun m n => nz m = nz n |};
  id      := fun _ => 0%nat;
  compose := fun _ _ _ f g => (f + g)%nat
|}.
Next Obligation.
  intros _ _; constructor; congruence.
Qed.
Next Obligation.
  intros a b c ?? H ?? H0; simpl in *; rewrite !nz_add; congruence.
Qed.
Next Obligation. intros ?? f; simpl; reflexivity. Qed.
Next Obligation. intros ?? f; simpl; rewrite PeanoNat.Nat.add_0_r; reflexivity. Qed.
Next Obligation. intros ???? f g h; simpl; rewrite PeanoNat.Nat.add_assoc; reflexivity. Qed.
Next Obligation. intros ???? f g h; simpl; rewrite PeanoNat.Nat.add_assoc; reflexivity. Qed.

(* The selection data: every 对象; 态射 every natural number
 EXCEPT 1. That closed under + (a sum 1 if one summand 1 and
 other 0) contains id = 0. （已译） *)

Lemma not_one_add : forall m n, m <> 1%nat -> n <> 1%nat -> (m + n)%nat <> 1%nat.
Proof.
  intros [|[|m]] [|[|n]]; simpl; intros H1 H2 Hc;
    try discriminate;
    try (apply H1; reflexivity);
    try (apply H2; reflexivity).
Qed.

Definition NotOne : Subcategory NZ :=
  @Build_Subcategory NZ (fun _ => unit)
    (fun _ _ _ _ f => f <> 1%nat)
    (fun _ _ _ _ _ _ f g Hf Hg => not_one_add f g Hf Hg)
    (fun _ _ => ltac:(discriminate)).

(* The 含入 FULL 函子: given any f : nat, send it 2 it
 1 itself otherwise. The result never 1, it ≈ f because
 2 1 both nonzero. （已译） *)
Definition pick (f : nat) : nat := if Nat.eqb f 1 then 2%nat else f.

Lemma pick_not_one : forall f, pick f <> 1%nat.
Proof.
  intro f; unfold pick; destruct (Nat.eqb f 1) eqn:E.
  - discriminate.
  - intro Hf; subst f; simpl in E; discriminate.
Qed.

Lemma pick_equiv : forall f, nz (pick f) = nz f.
Proof.
  intro f; unfold pick; destruct (Nat.eqb f 1) eqn:E; auto.
  apply PeanoNat.Nat.eqb_eq in E; subst; reflexivity.
Qed.

Program Definition NotOne_Incl_Full : Functor.Full (Incl NZ NotOne) := {|
  prefmap := fun _ _ g => (pick g; pick_not_one g)
|}.
Next Obligation. intros ?? g; simpl; apply pick_equiv. Qed.

(* But subcategory NOT Full data: 1 态射 NZ between
 selected 对象 subcategory does not retain. （已译） *)
Theorem NotOne_not_Full : Subcategory.Full NZ NotOne -> False.
Proof.
  intro HF.
  exact (HF tt tt tt tt 1%nat eq_refl).
Qed.

(*
   本节说明 FullConverse 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem converse_without_ShomRespects_is_false :
  (forall (C : Category) (S : Subcategory C),
      Functor.Full (Incl C S) -> Subcategory.Full C S) -> False.
Proof.
  intro Hbad.
  exact (NotOne_not_Full (Hbad NZ NotOne NotOne_Incl_Full)).
Qed.

(* 相关说明。 （已译） *)
Lemma NZ_setoid_nondegenerate :
  @equiv _ (@homset NZ tt tt) 0%nat 1%nat -> False.
Proof. simpl; discriminate. Qed.

(* 相关说明。 （已译） *)
Lemma NotOne_not_ShomRespects : ShomRespects NZ NotOne -> False.
Proof.
  intro HR.
  assert (Hne : 2%nat <> 1%nat) by discriminate.
  exact (HR tt tt tt tt 2%nat 1%nat eq_refl Hne eq_refl).
Qed.

