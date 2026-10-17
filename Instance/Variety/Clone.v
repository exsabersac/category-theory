Require Import Category.Lib.
Require Import Category.Instance.Comp.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/Lawvere+theory
 Wikipedia: https://en.wikipedia.org/wiki/Clone_(algebra)

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Module UA := Category.Instance.Comp.UniversalAlgebra.

Section Clone.

Context (S : UA.OpSignature).

(* 相关说明。 （已译） *)

Definition DerivedOperators (n : nat) : Type := UA.Tree S (Fin.t n).

Definition clone_var {n} (i : Fin.t n) : DerivedOperators n :=
  UA.generator S (Fin.t n) i.

Definition clone_op {n} (o : UA.operation S)
  (args : UA.arity o → DerivedOperators n) : DerivedOperators n :=
  UA.node S (Fin.t n) o args.

(* 相关说明。 （已译） *)

Definition clone_subst {m n} (s : Fin.t m → DerivedOperators n)
  : DerivedOperators m → DerivedOperators n :=
  UA.induced_map S (Fin.t m) (UA.Free S (Fin.t n)) s.

Definition clone_rename {m n} (phi : Fin.t m → Fin.t n)
  : DerivedOperators m → DerivedOperators n :=
  clone_subst (fun i => clone_var (phi i)).

(* 相关说明。 （已译） *)

Record SetoidAction := {
  sact_carrier : Type;
  sact_setoid  : Setoid sact_carrier;
  sact_op      : ∀ o : UA.operation S,
                  (UA.arity o → sact_carrier) → sact_carrier;

  (* 相关说明。 （已译） *)
  sact_op_respects : ∀ (o : UA.operation S) (k1 k2 : UA.arity o → sact_carrier),
    (∀ j, @equiv _ sact_setoid (k1 j) (k2 j)) →
    @equiv _ sact_setoid (sact_op o k1) (sact_op o k2)
}.

(*
   本节说明等价、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Notation "x ≈[ A ] y" := (@equiv _ (sact_setoid A) x y)
  (at level 79, only parsing).

(* 相关说明。 （已译） *)
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

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

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

(* 相关说明。 （已译） *)

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

(*
   本节说明 Clone 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

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
