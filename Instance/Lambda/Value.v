Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Instance.Lambda.Exp.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

(** 本节：The values (canonical forms) call-by-value de Bruijn STLC. （已译） *)

(*
   本文件给出 λ 演算相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section Value.

Import ListNotations.

Open Scope Ty_scope.

(* 相关说明。 （已译） *)
Inductive ValueP Γ : ∀ {τ}, Exp Γ τ → Set :=
  | UnitP : ValueP EUnit                          (* () is a value *)
  | PairP {τ1 τ2} {x : Exp Γ τ1} {y : Exp Γ τ2} :
    ValueP x → ValueP y → ValueP (Pair x y)       (* a pair of values is a value *)
  | LambdaP {dom cod} (e : Exp (dom :: Γ) cod) :
    ValueP (LAM e).                               (* an abstraction is a value *)

Derive Signature for ValueP.

#[local] Hint Constructors ValueP : core.

Fixpoint ValueP_irrelevance {Γ τ} (v : Exp Γ τ) (H1 H2 : ValueP _ v) :
  H1 = H2.
Proof.
  dependent elimination H1;
  dependent elimination H2.
  - reflexivity.
  - f_equal;
    now apply ValueP_irrelevance.
  - f_equal;
    now apply ValueP_irrelevance.
Qed.

Lemma ValueP_dec {Γ τ} (e : Exp Γ τ) :
  ValueP Γ e ∨ ¬ ValueP Γ e.
Proof.
  induction e; try solve [now left|now right].
  destruct IHe1, IHe2.
  - left.
    now constructor.
  - right.
    intro.
    dependent elimination H.
    contradiction.
  - right.
    intro.
    dependent elimination H.
    contradiction.
  - right.
    intro.
    dependent elimination H.
    contradiction.
Qed.

End Value.

Arguments ValueP {Γ τ} _.
Arguments UnitP {Γ}.
Arguments PairP {Γ τ1 τ2 x y} _ _.
Arguments LambdaP {Γ dom cod} _.
