Require Import Category.Lib.
Require Import Category.Instance.Comp.

Generalizable All Variables.

(** * Derived operators: the clone of a signature *)

(*
 nLab:      https://ncatlab.org/nlab/show/Lawvere+theory
 Wikipedia: https://en.wikipedia.org/wiki/Clone_(algebra)

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Module UA := Category.Instance.Comp.UniversalAlgebra.

Section Clone.

Context (S : UA.OpSignature).

(** ** The arity-graded derived operators *)

Definition DerivedOperators (n : nat) : Type := UA.Tree S (Fin.t n).

Definition clone_var {n} (i : Fin.t n) : DerivedOperators n :=
  UA.generator S (Fin.t n) i.

Definition clone_op {n} (o : UA.operation S)
  (args : UA.arity o → DerivedOperators n) : DerivedOperators n :=
  UA.node S (Fin.t n) o args.

(** ** Closure under substitution, along an ARBITRARY map of arities

    [clone_subst] is Instance/Comp.v's [induced_map] at the free
    algebra on [Fin.t n]; [clone_rename] is substitution by variables, and
    it is where "arbitrary function between finite arities" — duplication
    and deletion included, not merely a braid — enters. *)

Definition clone_subst {m n} (s : Fin.t m → DerivedOperators n)
  : DerivedOperators m → DerivedOperators n :=
  UA.induced_map S (Fin.t m) (UA.Free S (Fin.t n)) s.

Definition clone_rename {m n} (phi : Fin.t m → Fin.t n)
  : DerivedOperators m → DerivedOperators n :=
  clone_subst (fun i => clone_var (phi i)).

(** ** Actions, up to a setoid on the target *)

Record SetoidAction := {
  sact_carrier : Type;
  sact_setoid  : Setoid sact_carrier;
  sact_op      : ∀ o : UA.operation S,
                  (UA.arity o → sact_carrier) → sact_carrier;

  (* the congruence field that replaces functional extensionality *)
  sact_op_respects : ∀ (o : UA.operation S) (k1 k2 : UA.arity o → sact_carrier),
    (∀ j, @equiv _ sact_setoid (k1 j) (k2 j)) →
    @equiv _ sact_setoid (sact_op o k1) (sact_op o k2)
}.

(* A [#[local]] notation, and it SHADOWS Theory/Category.v's
   [x ≈[ C ] y] for morphism equivalence in a named category, for the
   remainder of this section.  That is harmless here — this file never
   compares morphisms of a category — and the [#[local]] keeps it out of
   every other file, but it is worth knowing before copying the idiom
   somewhere that does. *)
#[local] Notation "x ≈[ A ] y" := (@equiv _ (sact_setoid A) x y)
  (at level 79, only parsing).

(* Every [SetoidAction] has an underlying [OpAlgebra]: the setoid and its
   congruence field are extra structure, not a weakening. *)
Definition sact_alg (A : SetoidAction) : UA.OpAlgebra S :=
  {| UA.carrier := sact_carrier A ; UA.op := sact_op A |}.

Fixpoint clone_act {n} (A : SetoidAction) (t : DerivedOperators n)
  (env : Fin.t n → sact_carrier A) : sact_carrier A :=
  match t with
  | UA.generator _ _ i    => env i
  | UA.node _ _ o args => sact_op A o (fun j => clone_act A (args j) env)
  end.

(* Both computation rules hold definitionally; [reflexivity] is not
   hiding a rewrite. *)

Lemma clone_act_var {n} (A : SetoidAction) (i : Fin.t n)
  (env : Fin.t n → sact_carrier A) :
  clone_act A (clone_var i) env ≈[A] env i.
Proof. reflexivity. Qed.

Lemma clone_act_op {n} (A : SetoidAction) (o : UA.operation S)
  (args : UA.arity o → DerivedOperators n)
  (env : Fin.t n → sact_carrier A) :
  clone_act A (clone_op o args) env
    ≈[A] sact_op A o (fun j => clone_act A (args j) env).
Proof. reflexivity. Qed.

(** ** Mac Lane's theorem: the action of Ω determines the action of Λ

    Any operator [F] that acts like the variables on variables and like
    the basic operations on nodes agrees with [clone_act] everywhere.
    AXIOM-FREE: the inductive step closes with [sact_op_respects] where the
    Leibniz form below must close with functional extensionality. *)

Theorem action_extends_to_clone (A : SetoidAction)
  (F : ∀ n, DerivedOperators n → (Fin.t n → sact_carrier A) → sact_carrier A)
  (Hvar : ∀ n (i : Fin.t n) env, F n (clone_var i) env ≈[A] env i)
  (Hop : ∀ n (o : UA.operation S) (args : UA.arity o → DerivedOperators n) env,
           F n (clone_op o args) env
             ≈[A] sact_op A o (fun j => F n (args j) env)) :
  ∀ n (t : DerivedOperators n) env, F n t env ≈[A] clone_act A t env.
Proof.
  intros n t.
  induction t as [i | o args IH]; intro env.
  - apply Hvar.
  - rewrite (Hop n o args env).
    apply sact_op_respects.
    intro j.
    apply IH.
Qed.

(** ** The substitution and renaming laws for the action *)

Lemma clone_act_subst {m n} (A : SetoidAction)
  (s : Fin.t m → DerivedOperators n) (t : DerivedOperators m)
  (env : Fin.t n → sact_carrier A) :
  clone_act A (clone_subst s t) env
    ≈[A] clone_act A t (fun i => clone_act A (s i) env).
Proof.
  induction t as [i | o args IH]; simpl.
  - reflexivity.
  - apply sact_op_respects.
    intro j.
    apply IH.
Qed.

Lemma clone_act_rename {m n} (A : SetoidAction)
  (phi : Fin.t m → Fin.t n) (t : DerivedOperators m)
  (env : Fin.t n → sact_carrier A) :
  clone_act A (clone_rename phi t) env
    ≈[A] clone_act A t (fun i => env (phi i)).
Proof. apply clone_act_subst. Qed.

End Clone.

Arguments clone_var {_ _} _.
Arguments clone_op {_ _} _ _.
Arguments clone_subst {_ _ _} _ _.
Arguments clone_rename {_ _ _} _ _.
Arguments sact_carrier {_} _.
Arguments sact_op {_} _ _ _.
Arguments clone_act {_ _} _ _ _.

(** ** The Leibniz shadows, and their cost

    Shipped so the comparison is available in the tree rather than only in
    this header, and named so that no one mistakes them for the headline
    statements.  BOTH REPORT [functional_extensionality_dep]; neither is
    gated. *)

Section CloneLeibniz.

Context (S : UA.OpSignature).

(* An action with no setoid: Leibniz [=] throughout. *)
Definition leibniz_action (A : UA.OpAlgebra S) : SetoidAction S :=
  {| sact_carrier := UA.carrier A
   ; sact_setoid  := eq_Setoid (UA.carrier A)
   ; sact_op      := UA.op A
   ; sact_op_respects := fun o k1 k2 H =>
       f_equal (UA.op A o) (functional_extensionality_dep k1 k2 H)
  |}.

Theorem action_extends_to_clone_leibniz (A : UA.OpAlgebra S)
  (F : ∀ n, DerivedOperators S n → (Fin.t n → UA.carrier A) → UA.carrier A)
  (Hvar : ∀ n (i : Fin.t n) env, F n (clone_var i) env = env i)
  (Hop : ∀ n (o : UA.operation S) (args : UA.arity o → DerivedOperators S n) env,
           F n (clone_op o args) env
             = UA.op A o (fun j => F n (args j) env)) :
  ∀ n (t : DerivedOperators S n) env,
    F n t env = clone_act (leibniz_action A) t env.
Proof.
  exact (action_extends_to_clone S (leibniz_action A) F Hvar Hop).
Qed.

Lemma clone_act_subst_leibniz {m n} (A : UA.OpAlgebra S)
  (s : Fin.t m → DerivedOperators S n) (t : DerivedOperators S m)
  (env : Fin.t n → UA.carrier A) :
  clone_act (leibniz_action A) (clone_subst s t) env
    = clone_act (leibniz_action A) t
        (fun i => clone_act (leibniz_action A) (s i) env).
Proof. exact (clone_act_subst S (leibniz_action A) s t env). Qed.

End CloneLeibniz.
