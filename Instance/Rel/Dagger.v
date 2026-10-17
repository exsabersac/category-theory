Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Structure.Dagger.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Rel.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.
Require Import Coq.Sets.Ensembles.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 nLab: https://ncatlab.org/nlab/show/Rel

   本文件给出关系范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The converse is a dagger *)

#[export] Program Instance Rel_Dagger : DaggerCategory Rel := {
  dagger := fun x y (R : x ~{Rel}~> y) (b : y) (a : x) => R a b
}.
Next Obligation.
  intros x y R S H b a; exact (H a b).
Qed.
Next Obligation.
  intros x y R b a; split; intro H; exact H.
Qed.
Next Obligation.
  intros x b a; split; intro H; destruct H; constructor.
Qed.
Next Obligation.
  intros x y z f g c a; split; intro H;
    destruct H as [e [H1 H2]]; exists e; split; assumption.
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明函子、hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Rel_Converse : Rel ⟶ Rel^op := {|
  fobj := fun x => x;
  fmap := fun x y (R : x ~{Rel}~> y) => @dagger Rel Rel_Dagger x y R
|}.
Next Obligation.
  intros x y R S H b a; exact (H a b).
Qed.
Next Obligation.
  intros x b a; split; intro H; destruct H; constructor.
Qed.
Next Obligation.
  intros x y z f g c a; split; intro H;
    destruct H as [e [H1 H2]]; exists e; split; assumption.
Qed.

Program Definition Rel_Converse_op : Rel^op ⟶ Rel := {|
  fobj := fun x => x;
  fmap := fun x y (R : x ~{Rel^op}~> y) => @dagger Rel Rel_Dagger y x R
|}.
Next Obligation.
  intros x y R S H b a; exact (H a b).
Qed.
Next Obligation.
  intros x b a; split; intro H; destruct H; constructor.
Qed.
Next Obligation.
  intros x y z f g c a; split; intro H;
    destruct H as [e [H1 H2]]; exists e; split; assumption.
Qed.

#[local] Obligation Tactic := cat_simpl.

Program Definition Rel_self_dual_strict : Rel ≅[StrictCat] Rel^op := {|
  to   := Rel_Converse;
  from := Rel_Converse_op
|}.

#[local] Obligation Tactic := idtac.

Program Definition Rel_self_dual : Rel ≅[Cat] Rel^op := {|
  to   := Rel_Converse;
  from := Rel_Converse_op
|}.
Next Obligation.
  exists (fun x => iso_id).
  intros x y R a b; simpl.
  split; intro H.
  - exists b; split; [| constructor ].
    exists a; split; [ constructor | exact H ].
  - destruct H as [e [[e0 [He0 HR]] Hb]].
    destruct He0.
    destruct Hb.
    exact HR.
Qed.
Next Obligation.
  exists (fun x => iso_id).
  intros x y R a b; simpl.
  split; intro H.
  - exists a; split; [ constructor |].
    exists b; split; [ exact H | constructor ].
  - destruct H as [e [He [e0 [HR Hb]]]].
    destruct He.
    destruct Hb.
    exact HR.
Qed.

(* 相关说明。 （已译） *)

#[export] Instance Relation_Functor_Faithful : Faithful Relation_Functor.
Proof.
  constructor; intros x y f g H a.
  destruct (H a (f a)) as [Hfg _].
  destruct (Hfg (In_singleton _ _)).
  reflexivity.
Qed.

(* * ** The empty set terminal too, hence zero 对象 （已译） *)

#[export] Program Instance Rel_Terminal : @Terminal Rel := {
  terminal_obj := False;
  one := fun _ _ (f : False) => False_rect _ f
}.
Next Obligation. intros x f g a b; contradiction. Qed.

#[export] Program Instance Rel_Zero : ZeroObject Rel := {
  zero_terminal := Rel_Terminal;
  zero_initial  := Rel_Initial;
  zero_coincide := iso_id
}.

(* 相关说明。 （已译） *)

Section Powerset.

Context (X : Type).

(*
   本节说明 Dagger 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition psub (A B : X → bool) : Prop :=
  ∀ x : X, A x = true → B x = true.

#[export] Instance psub_preorder : RelationClasses.PreOrder psub.
Proof.
  constructor.
  - intros A x H; exact H.
  - intros A B C H1 H2 x H; exact (H2 x (H1 x H)).
Qed.

Definition Powerset : Category := Proset psub_preorder.

(* Complementation antitone, hence 函子 进入 opposite
 order; thin target makes every 函子 law free. （已译） *)
Program Definition Powerset_Compl : Powerset ⟶ Powerset^op := {|
  fobj := fun A x => negb (A x);
  fmap := fun A B (H : psub A B) x HB => _
|}.
Next Obligation.
  intros A B H x HB; simpl in HB |- *.
  destruct (A x) eqn:HA.
  - rewrite (H x HA) in HB; discriminate HB.
  - reflexivity.
Qed.
Next Obligation. intros A B f g H; exact I. Qed.
Next Obligation. intros A; exact I. Qed.
Next Obligation. intros A B C f g; exact I. Qed.

Program Definition Powerset_Compl_op : Powerset^op ⟶ Powerset := {|
  fobj := fun A x => negb (A x);
  fmap := fun A B (H : psub B A) x HB => _
|}.
Next Obligation.
  intros A B H x HB; simpl in HB |- *.
  destruct (B x) eqn:HB'.
  - rewrite (H x HB') in HB; discriminate HB.
  - reflexivity.
Qed.
Next Obligation. intros A B f g H; exact I. Qed.
Next Obligation. intros A; exact I. Qed.
Next Obligation. intros A B C f g; exact I. Qed.

Program Definition Powerset_self_dual : Powerset ≅[Cat] Powerset^op := {|
  to   := Powerset_Compl;
  from := Powerset_Compl_op
|}.
Next Obligation.
  unshelve eexists.
  - intro A; unshelve econstructor.
    + intros x H; vm_compute in H |- *; rewrite H; reflexivity.
    + intros x H; vm_compute in H |- *; destruct (A x) eqn:HA;
        [ reflexivity | discriminate H ].
    + exact I.
    + exact I.
  - intros A B H; exact I.
Qed.
Next Obligation.
  unshelve eexists.
  - intro A; unshelve econstructor.
    + intros x H; vm_compute in H |- *; destruct (A x) eqn:HA;
        [ reflexivity | discriminate H ].
    + intros x H; vm_compute in H |- *; rewrite H; reflexivity.
    + exact I.
    + exact I.
  - intros A B H; exact I.
Qed.

End Powerset.

(* 相关说明。 （已译） *)

Definition SEmpty : Sets := {| carrier := False; is_setoid := eq_Setoid False |}.
Definition SUnit  : Sets := {| carrier := unit;  is_setoid := eq_Setoid unit  |}.
Definition SBool  : Sets := {| carrier := bool;  is_setoid := eq_Setoid bool  |}.

#[local] Obligation Tactic := cat_simpl.

Program Definition kbool (b : bool) : SUnit ~{Sets}~> SBool :=
  {| morphism := fun _ => b |}.

(*
   本节说明hom、等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Sets_not_self_dual : Sets ≅[Cat] Sets^op → False.
Proof.
  intro iso.
  pose (E := Cat_Iso_to_Equivalence iso).
  pose (F := to iso).
  pose proof (Equivalence_Full E)     as HFull.
  pose proof (Equivalence_Faithful E) as HFaith.
  assert (Hno : (F SEmpty ~{Sets}~> F SUnit) → False).
  { intro g. exact (@prefmap _ _ F HFull SUnit SEmpty g tt). }
  assert (He : carrier (F SUnit) → False).
  { intro e. unshelve refine (Hno {| morphism := fun _ => e |}).
    abstract (proper). }
  assert (Hfe : fmap[F] (kbool true) ≈ fmap[F] (kbool false)).
  { intro a. elim (He (fmap[F] (kbool true) a)). }
  pose proof (@fmap_inj _ _ F HFaith SUnit SBool _ _ Hfe tt) as Hc.
  discriminate Hc.
Qed.
