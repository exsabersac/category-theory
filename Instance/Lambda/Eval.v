Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Instance.Lambda.Ty.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Value.
Require Import Category.Instance.Lambda.Ren.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

(** 本节：A CEK abstract machine de Bruijn STLC （已译） *)

(*
   本文件给出 λ 演算相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Set Transparent Obligations.

Section Eval.

Import ListNotations.

(*
   本节说明 Eval 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive Closed : Ty → Set :=
  | Closure {Γ τ} : Exp Γ τ → ClEnv Γ → Closed τ

with ClEnv : Env → Set :=
  | NoCl : ClEnv []
  | AddCl {Γ τ} : Value τ → ClEnv Γ → ClEnv (τ :: Γ)

with Value : Ty → Set :=
  | Val {Γ τ} (x : Exp Γ τ) : ValueP x → ClEnv Γ → Value τ.

Derive Signature NoConfusion NoConfusionHom Subterm for ClEnv Closed Value.

(* 相关说明。 （已译） *)
Equations get_val `(s : ClEnv Γ) `(v : Var Γ τ) : Value τ :=
  get_val (AddCl x _)  ZV     := x;
  get_val (AddCl _ xs) (SV v) := get_val xs v.

(* Concatenate two environments, mirroring [++] on the underlying contexts. *)
Equations combine `(c1 : ClEnv Γ) `(c2 : ClEnv Γ') : ClEnv (Γ ++ Γ') :=
  combine NoCl         c2 := c2;
  combine (AddCl c c1) c2 := AddCl c (combine c1 c2).

(*
   本节说明（余）端、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fixpoint snoc {a : Type} (x : a) (xs : list a) : list a :=
  match xs with
  | [] => [x]
  | y :: ys => y :: snoc x ys
  end.

(*
   本节说明 Eval 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive EvalContext : Ty → Ty → Set :=
  | MT {τ} : EvalContext τ τ
  | AR {dom cod τ} :
    Closed dom → EvalContext cod τ → EvalContext (dom ⟶ cod) τ
  | FN {dom cod τ} :
    Value (dom ⟶ cod) → EvalContext cod τ → EvalContext dom τ
  | PAIR_FST {τ1 τ2 τ} : Closed τ1 → EvalContext (τ1 × τ2) τ → EvalContext τ2 τ
  | PAIR_SND {τ1 τ2 τ} : Closed τ2 → EvalContext (τ1 × τ2) τ → EvalContext τ1 τ
  | FST {τ1 τ2 τ} : EvalContext τ1 τ → EvalContext (τ1 × τ2) τ
  | SND {τ1 τ2 τ} : EvalContext τ2 τ → EvalContext (τ1 × τ2) τ.

Derive Signature NoConfusion NoConfusionHom Subterm for EvalContext.

(* A machine state: control [Closed] type [u] together continuation
 will turn [u]-result 进入 final [τ]-result. （已译） *)
Inductive Σ : Ty → Set :=
  | MkΣ {u    : Ty}
        (exp  : Closed u)
        {τ    : Ty}
        (knt  : EvalContext u τ) : Σ τ.

Derive Signature NoConfusion NoConfusionHom Subterm for Σ.

(*
   本节说明 Eval 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Equations step {τ : Ty} (s : Σ τ) : Σ τ :=
  (* Constants *)
  step (MkΣ (Closure EUnit _) (FN f κ)) with f := {
    | Val (LAM e) _ ρ' := MkΣ (Closure e (AddCl (Val EUnit UnitP NoCl) ρ')) κ;
  };

  step (MkΣ (Closure (Fst p) ρ) κ) := MkΣ (Closure p ρ) (FST κ);
  step (MkΣ (Closure (Snd p) ρ) κ) := MkΣ (Closure p ρ) (SND κ);

  step (MkΣ (Closure (Pair x y) ρ) (FST κ)) := MkΣ (Closure x ρ) κ;
  step (MkΣ (Closure (Pair x y) ρ) (SND κ)) := MkΣ (Closure y ρ) κ;

  (*
   本节说明 Eval 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  step (MkΣ (Closure (Pair x y) ρ) κ) :=
    MkΣ (Closure x ρ) (PAIR_SND (Closure y ρ) κ);
  step (MkΣ x (PAIR_SND y κ)) := MkΣ y (PAIR_FST x κ);
  step (MkΣ (Closure y ρ) (PAIR_FST (Closure x ρ') κ)) :=
    MkΣ (Closure (Pair (liftL _ x) (liftR _ y)) (combine ρ' ρ)) κ;

  (* A variable might lookup lambda, case continue evaluating down
 vein; otherwise, if no continuation, 这是 far we can go. （已译） *)
  step (MkΣ (Closure (VAR v) ρ) κ) with get_val ρ v := {
    | Val val _ ρ' := MkΣ (Closure val ρ') κ
  };

  (* 相关说明。 （已译） *)
  step (MkΣ (Closure (LAM e) ρ) (AR a κ)) :=
    MkΣ a (FN (Val (LAM e) (LambdaP _) ρ) κ);
  step (MkΣ (Closure (LAM e) ρ) (FN (Val (LAM f) _ ρ') κ)) :=
    MkΣ (Closure f (AddCl (Val (LAM e) (LambdaP _) ρ) ρ')) κ;

  (* Application evaluates lambda then 论元 （已译） *)
  step (MkΣ (Closure (APP f x) ρ) κ) :=
    MkΣ (Closure f ρ) (AR (Closure x ρ) κ);

  step (MkΣ c MT) := MkΣ c MT.

(*
   本节说明 Eval 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Equations loop (gas : nat) {τ : Ty} (s : Σ τ) : Σ τ :=
  loop O s := s;
  loop (S gas') s := loop gas' (step s).

(* Load closed term 进入 initial machine state: empty environment
 [NoCl] closes (nonexistent) free variables, halt continuation
 [MT] will receive final value. （已译） *)
Definition inject {τ : Ty} (e : Exp [] τ) : Σ τ := MkΣ (Closure e NoCl) MT.

(* 相关说明。 （已译） *)
Definition run (gas : nat) {τ : Ty} (e : Exp [] τ) : Σ τ := loop gas (inject e).

(*
   本节说明 Eval 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

End Eval.
