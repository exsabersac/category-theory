(* 相关说明。 （已译） *)

(*
   本文件给出 Tactics 相关定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Coq.Bool.Bool.

Require Export Category.Lib.Setoid.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Open Scope lazy_bool_scope.

Module Compat.
  (*
   本节说明 Tactics 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

  Module Fake.
    Notation internal_eq_rew_r_dep := ltac:(fail "should not happen") (only parsing).
    Notation internal_eq_sym_involutive := ltac:(fail "should not happen") (only parsing).
    Notation internal_eq_sym_internal := ltac:(fail "should not happen") (only parsing).
  End Fake.

  Module FromEqdepFactsIfExists.
    Import Fake.
    Import EqdepFacts.

    (* if eq_rew_r_dep exists EqdepFacts then it used here,
 otherwise 这是 "fake" notation （已译） *)
    Notation eq_rew_r_dep := internal_eq_rew_r_dep.

    (* same for the other notations *)
    Notation eq_sym_involutive := internal_eq_sym_involutive.
    Notation eq_sym := internal_eq_sym_internal.
  End FromEqdepFactsIfExists.

  Import FromEqdepFactsIfExists.
  Import Logic.

  (* if eq_rew_r_dep exists in Logic then it is used here,
     otherwise this is internal_eq_rew_r_dep through FromEqdepFactsIfExists. *)
  Notation eq_rew_r_dep := eq_rew_r_dep.

  (* same for the other notations *)
  Notation eq_sym_involutive := eq_sym_involutive.
  Notation eq_sym := eq_sym.
End Compat.

(*
   本节说明 Tactics 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Ltac simpl_eq :=
  unfold eq_rect_r, eq_rect, eq_ind_r, eq_ind, eq_sym, prod_rect,
    Compat.eq_rew_r_dep,
    Compat.eq_sym_involutive,
    Compat.eq_sym in *.

(*
   本节说明 Tactics 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Ltac simplify :=
  repeat
    (match goal with
     | [ H : () |- _ ] => destruct H
     | [ |- () ] => exact tt

     | [ H : (_ &&& _) = true |- _ ] => rewrite <- andb_lazy_alt in H
     | [ |- (_ &&& _) = true ]       => rewrite <- andb_lazy_alt
     | [ H : (_ && _) = true |- _ ]  => apply andb_true_iff in H
     | [ |- (_ && _) = true ]        => apply andb_true_iff; split

     | [ H : _ ∧ _ |- _ ] =>
       let H' := fresh "H" in destruct H as [H H']
     | [ |- _ ∧ _ ] => split

     | [ H : _ /\ _ |- _ ] =>
       let H' := fresh "H" in destruct H as [H H']
     | [ |- _ /\ _ ] => split

     | [ H : _ ↔ _ |- _ ] =>
       let H' := fresh "H" in destruct H as [H H']
     | [ |- _ ↔ _ ] => split

     | [ H : (_, _) = (_, _) |- _ ] => inversion_clear H

     | [ H : _ * _ |- _ ] =>
       let x := fresh "x" in
       let y := fresh "y" in
       destruct H as [x y]
     | [ |- _ * _ ] => split

     | [ H : { _ : _ & _ } |- _ ] =>
       let x := fresh "x" in
       let e := fresh "e" in
       destruct H as [x e]
     | [ |- { _ : _ & _ } ] =>
       unshelve (refine (existT _ _ _))
     end; intros).

(*
   本节说明 Tactics 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Ltac cat :=
  simplify;
  autorewrite with categories;
  auto with category_laws;
  try reflexivity.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Hint Constructors Equivalence : core.

#[export] Hint Unfold Reflexive : core.
#[export] Hint Unfold Symmetric : core.
#[export] Hint Unfold Transitive : core.

#[export] Hint Extern 1 (Reflexive ?X) =>
  unfold Reflexive : core.
#[export] Hint Extern 1 (Symmetric ?X) =>
  unfold Symmetric : core.
#[export] Hint Extern 1 (Transitive ?X) =>
  unfold Transitive : core.
#[export] Hint Extern 1 (Equivalence ?X) =>
  apply Build_Equivalence : core.
#[export] Hint Extern 1 (Proper _ _) => unfold Proper : core.
#[export] Hint Extern 8 (respectful _ _ _ _) =>
  unfold respectful : core.

(* 相关说明。 （已译） *)
#[export] Hint Extern 4 (equiv ?A ?A) => reflexivity : category_laws.
#[export] Hint Extern 6 (equiv ?X ?Y) =>
  apply Equivalence_Symmetric : category_laws.
#[export] Hint Extern 7 (equiv ?X ?Z) =>
  match goal with
    [H : equiv ?X ?Y, H' : equiv ?Y ?Z |- equiv ?X ?Z] => transitivity Y
  end : category_laws.

(*
   本节说明等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Ltac equivalence := constructor; repeat intro; simpl; try cat; intuition;
  try solve [ reflexivity | (symmetry; eassumption) ];
  auto with category_laws.
(* 相关说明。 （已译） *)
Ltac proper := repeat intro; simpl; try cat; intuition.
(* [sapply]/[srewrite]/[srewrite_r]: "setoid" variants that first materialize
   [F] as a hypothesis and [cbn]-normalize it (so projections of records unfold)
   before applying / rewriting left-to-right / rewriting right-to-left.（标题）（已译） *)
Ltac sapply F :=
  let H := fresh "H" in pose proof F as H; cbn in H; apply H; clear H.
Ltac srewrite F :=
  let H := fresh "H" in pose proof F as H; cbn in H; rewrite H; clear H.
Ltac srewrite_r F :=
  let H := fresh "H" in pose proof F as H; cbn in H; rewrite <- H; clear H.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Ltac cat_simpl :=
  program_simpl; autounfold;
  try solve [
    repeat match goal with
    | [ |- Equivalence _ ] => equivalence
    | [ |- Proper _ _ ] => proper
    | [ |- respectful _ _ _ _ ] => proper
    end;
    program_simpl; autounfold in *;
    simpl in *; intros; simplify;
    simpl in *; cat];
  simpl in *.

#[global] Obligation Tactic := cat_simpl.

(* 相关说明。 （已译） *)
Ltac construct := unshelve econstructor; simpl; intros.

(* [inv H]: invert [H], substitute resulting equalities, discard the
 now-redundant 假设 possible. （已译） *)
Ltac inv H := inversion H; subst; try clear H.

(* [spose H X]: introduce (untyped) term [H] 假设 [X] and
 [simpl]-reduce it -- terse [pose proof ... ...] setoid lemmas. （已译） *)
Tactic Notation "spose" uconstr(H) "as" ident(X) :=
  pose proof H as X; simpl in X.
