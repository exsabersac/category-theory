Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Functor.Structure.Cartesian.
Require Import Category.Instance.Coq.
Require Import Category.Instance.AST.
Require Import Category.Tools.Represented.

Generalizable All Variables.

(** * Compiling Coq functions to cartesian-closed combinators *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category

   本文件给出 Abstraction 相关定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Abstraction.

(* The correctness relation for compiling a unary function [lam : a → b] to a
   combinator [ccc : repr a ~> repr b]: [convert] carries [lam] to [ccc]. *)
Definition rel `{Repr a} `{Repr b}
           (lam : a → b) (ccc : repr a ~{AST}~> repr b) : Type :=
  ∀ x : a, convert (lam x) ≈ ccc ∘ convert x.

(*
   本节说明 Abstraction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition rel2 `{Repr a} `{Repr b} `{Repr c}
           (lam : a → b → c) (ccc : repr a ~{AST}~> repr c ^ repr b) : Type :=
  ∀ (x : a) (y : b), convert (lam x y) ≈ uncurry ccc ∘ convert (x, y).

Infix ">==>" := rel (at level 99) : category_scope.
Infix ">===>" := rel2 (at level 99) : category_scope.

(* Variable rule: the identity lambda [λx, x] compiles to the identity arrow. *)
Corollary ccc_id : ∀ `{Repr a}, (λ x : a, x) >==> id.
Proof. unfold rel; intros; cat. Qed.

Tactic Notation "step" constr(x) "=>" constr(y) :=
  replace x with y by auto.

(* Pairing of global elements is the represented pair: this is the [convert] of
   [prod_Repr] (see Tools/Represented) holding definitionally. *)
Corollary convert_fork `{Repr a} `{Repr b} (x : a) (y : b) :
  convert x △ convert y ≈ convert (x, y).
Proof. reflexivity. Qed.

(*
   本节说明 Abstraction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem ccc_apply :
  ∀ `{Repr a} `{Repr b} `{Repr c}
    (U : a → b → c) (U' : repr a ~{AST}~> repr c ^ repr b)
    (V : a → b) (V' : repr a ~{AST}~> repr b),
  U >===> U' ->
  V >==> V' ->
    (λ x, U x (V x)) >==> eval ∘ U' △ V'.
Proof.
  unfold rel, rel2; repeat intros.
  rewrite <- comp_assoc.
  rewrite <- fork_comp.
  rewrites.
  rewrite <- eval_first.
  comp_left.
  unfold first.
  rewrite <- fork_comp.
  rewrite <- comp_assoc.
  rewrite <- convert_fork; cat.
Qed.

(* Application rule with an uncurried callee [U : a * b → c]: the argument is
   paired with the input via [id △ V'] before applying [U']. *)
Theorem ccc_apply_pair :
  ∀ `{Repr a} `{Repr b} `{Repr c}
    (U : a * b → c) (U' : repr a × repr b ~{AST}~> repr c)
    (V : a → b) (V' : repr a ~{AST}~> repr b),
  U >==> U' ->
  V >==> V' ->
    (λ x, U (x, V x)) >==> U' ∘ id △ V'.
Proof.
  unfold rel; intros ??????? U' V; subst; intros.
  rewrite <- comp_assoc.
  rewrite <- fork_comp.
  rewrite id_left.
  rewrites.
  rewrite convert_fork.
  reflexivity.
Qed.

(* Abstraction rule: an inner lambda [λy, U (x, y)] compiles by currying the
   uncurried combinator [U'], so [λx, λy, U (x, y)] compiles to [curry U']. *)
Theorem ccc_curry :
  ∀ `{Repr a} `{Repr b} `{Repr c}
    (U : a * b → c) (U' : repr a × repr b ~> repr c),
    U >==> U' ->
      (λ x, λ y, U (x, y)) >===> curry U'.
Proof.
  unfold rel, rel2; repeat intros.
  rewrite uncurry_curry.
  apply X.
Qed.

(* Unit-introduction rule: the constant [tt] map compiles to the unique arrow
   [one] into the terminal object, by [one_unique]. *)
Theorem ccc_terminal : ∀ `{Repr a},
  (λ _ : a, tt) >==> one.
Proof.
  unfold rel; simpl; intros; cat.
  apply one_unique.
Qed.

(* Logical bookkeeping: a non-dependent hypothesis [a] commutes past a universal
   quantifier in both directions (the curry/uncurry of implications). *)
Lemma distribute_forall : ∀ a {X} P, (a → ∀ (x : X), P x) → (∀ x, a → P x).
Proof.
  intros.
  apply X0.
  assumption.
Qed.

Lemma forall_distribute : ∀ a {X} P, (∀ x, a → P x) → (a → ∀ (x : X), P x).
Proof.
  intros.
  apply X0.
  assumption.
Qed.

End Abstraction.

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class Numerical (C : Category) `{@Cartesian C} := {
  numerical_obj : obj;
  add : numerical_obj × numerical_obj ~> numerical_obj
}.

Section NumericalFunctor.

Context `{F : C ⟶ D}.
Context `{@Cartesian C}.
Context `{@Numerical C _}.
Context `{@Cartesian D}.
Context `{@Numerical D _}.
Context `{@CartesianFunctor _ _ F _ _}.

(*
   本节说明函子、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class NumericalFunctor := {
  map_num : numerical_obj ≅ F numerical_obj;

  fmap_add :
    fmap add ≈ map_num ∘ @add D _ _ ∘ split (map_num⁻¹) (map_num⁻¹)
                       ∘ @prod_out _ _ F _ _ _ numerical_obj numerical_obj
}.

End NumericalFunctor.

#[export]
Instance Coq_Numerical : @Numerical Coq Coq_Cartesian := {
  numerical_obj := nat;
  add := Datatypes.uncurry Nat.add
}.

Section Example.

Infix ">==>" := rel (at level 99) : category_scope.

(*
Theorem ccc_arity2 :
  ∀ (a b c : Type)
    (f : a → b) (f' : F a ~> F b)
    (g : a → b) (g' : F a ~> F b)
    (p : b → b → c) (p' : F b ~> F c ^ F b),
  f >==> f' ->
  g >==> g' ->
  p >==> exp_in ∘ p' ->
  (λ x : a, p (f x) (g x)) >==> uncurry p' ∘ f' △ g'.
Proof.
Abort.

Theorem ccc_plus :
  ∀ (f : nat → nat) (f' : F nat ~> F nat)
    (g : nat → nat) (g' : F nat ~> F nat),
  f >==> f' ->
  g >==> g' ->
  (λ x : nat, (f x + g x)%nat)
    >==> map_num ∘ add ∘ split (map_num⁻¹) (map_num⁻¹) ∘ f' △ g'.
Proof.
  intros.
  pose proof (ccc_arity2 nat nat nat f f' g g' Nat.add
                         (curry (map_num ∘ add ∘ split (map_num⁻¹) (map_num⁻¹)))
                         X X0).
  simpl in X1.
  unfold rel in *; repeat intros.
  rewrite uncurry_curry in X1.
  rewrites; [reflexivity|]; clear X1.
  pose proof (@fmap_add Coq _ _ _ _ _ _ _ _) as HA.
  simpl in HA.
  assert (Nat.add = prod_uncurry (λ p : nat * nat, (fst p + snd p)%nat)) by auto.
  rewrites.
Abort.
*)

(* f : A -->[Setoid] R *)
(* g : A -->[Setoid] R *)
(* + : R * R -->[Setoid] R *)
(* ============== *)
(* lambda x. f x + g x  : A -->[Setoid] R *)

(* Definition generic_add := fmap Nat.add. *)

End Example.

(* Eval simpl in @generic_add. *)
