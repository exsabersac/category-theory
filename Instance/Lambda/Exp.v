Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Instance.Lambda.Ty.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Set Transparent Obligations.
Unset Uniform Inductive Parameters.

(** Intrinsically-typed de Bruijn syntax for the simply-typed lambda calculus *)

(*
   本文件给出 λ 演算相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Exp.

Import ListNotations.

Open Scope Ty_scope.

(* A typing context: the list of types of the in-scope variables, with the
   most recently bound variable at the head (de Bruijn index 0). *)
Definition Env := list Ty.

(* Well-scoped de Bruijn indices: [Var Γ τ] witnesses that the context Γ has
   a variable of type τ.  [ZV] is index 0 (the head binding); [SV] is the
   successor, weakening a variable under one more binding. *)
Inductive Var : Env → Ty → Set :=
  | ZV {Γ τ}    : Var (τ :: Γ) τ           (* de Bruijn index 0: head slot *)
  | SV {Γ τ τ'} : Var Γ τ → Var (τ' :: Γ) τ.  (* successor: skip the head slot *)

Derive Signature NoConfusion EqDec for Var.

(* Well-typed terms: [Exp Γ τ] is a derivation of Γ ⊢ τ.  Each constructor is
   one STLC typing rule, so the GADT contains exactly the well-typed terms. *)
Inductive Exp Γ : Ty → Set :=
  | EUnit         : Exp Γ TyUnit                              (* unit introduction *)

  | Pair {τ1 τ2}  : Exp Γ τ1 → Exp Γ τ2 → Exp Γ (TyPair τ1 τ2)  (* product introduction *)
  | Fst {τ1 τ2}   : Exp Γ (TyPair τ1 τ2) → Exp Γ τ1          (* first projection *)
  | Snd {τ1 τ2}   : Exp Γ (TyPair τ1 τ2) → Exp Γ τ2          (* second projection *)

  | VAR {τ}       : Var Γ τ → Exp Γ τ                        (* variable *)
  | LAM {dom cod} : Exp (dom :: Γ) cod → Exp Γ (dom ⟶ cod)   (* abstraction *)
  | APP {dom cod} : Exp Γ (dom ⟶ cod) → Exp Γ dom → Exp Γ cod.  (* application *)

Derive Signature NoConfusionHom Subterm EqDec for Exp.

(* Structural size of a term, counting one for every node.  Used as a
   well-founded measure for size-decreasing recursions elsewhere. *)
Fixpoint Exp_size {Γ τ} (e : Exp Γ τ) : nat :=
  match e with
  | EUnit _       => 1
  | Pair _ x y    => 1 + Exp_size x + Exp_size y
  | Fst _ p       => 1 + Exp_size p
  | Snd _ p       => 1 + Exp_size p
  | VAR _ v       => 1
  | LAM _ e       => 1 + Exp_size e
  | APP _ e1 e2   => 1 + Exp_size e1 + Exp_size e2
  end.

Corollary Exp_size_preserved {Γ τ} (e1 e2 : Exp Γ τ) :
  Exp_size e1 ≠ Exp_size e2 → e1 ≠ e2.
Proof. repeat intro; subst; contradiction. Qed.

End Exp.

Arguments EUnit {Γ}.
Arguments Pair {Γ τ1 τ2} _ _.
Arguments Fst {Γ τ1 τ2} _.
Arguments Snd {Γ τ1 τ2} _.
Arguments VAR {Γ τ} _.
Arguments LAM {Γ dom cod} _.
Arguments APP {Γ dom cod} _ _.

(* Judgement notation: [Γ ∋ τ] for a variable, [Γ ⊢ τ] for a well-typed term. *)
Notation "Γ ∋ τ" := (Var Γ τ) (at level 10).
Notation "Γ ⊢ τ" := (Exp Γ τ) (at level 10).
