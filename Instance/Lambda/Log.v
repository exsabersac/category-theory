Require Import Category.Lib.
Require Import Category.Instance.Lambda.Ltac.
Require Import Category.Instance.Lambda.Ty.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Sub.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

(** 本节：Type-indexed logical predicates relations STLC. （已译） *)

(*
   本文件给出 λ 演算相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Log.

Context {A : Type}.
Context `{L : HostExprs A}.
Context {Γ : Env}.

Variable P : ∀ {τ}, Exp Γ τ → Type.

(** 本节：[ExpP] lifts base predicate [P] type-directed through syntax. （已译） *)
Equations ExpP `(e : Exp Γ τ) : Type :=
  ExpP (τ:=_ ⟶ _) e := P e ∧ (∀ x, ExpP x → ExpP (APP e x));
  ExpP (τ:=_ × _) e := P e ∧ ExpP (Fst e) ∧ ExpP (Snd e);
  ExpP e := P e.

(* [SubP] extends [ExpP] pointwise to substitutions: every pushed term is
   reducible. *)
Inductive SubP : ∀ {Γ'}, Sub Γ Γ' → Type :=
  | NoSubP : SubP (NoSub (Γ:=Γ))
  | PushP {Γ' τ} (e : Exp Γ τ) (s : Sub Γ Γ') :
    ExpP e → SubP s → SubP (Push e s).

Derive Signature for SubP.

(* 相关说明。 （已译） *)
Lemma ExpP_P {τ} {e : Γ ⊢ τ} : ExpP e → P e.
Proof. intros; induction τ; simpl in *; simp ExpP in X; now reduce. Qed.

Variable R : ∀ {τ}, Exp Γ τ → Exp Γ τ → Type.

(** [ExpR] binary analogue [ExpP], lifting base 关系 [R]. （已译） *)
Equations ExpR {τ} (e1 e2 : Exp Γ τ) : Type :=
  ExpR (τ:=_ ⟶ _) f1 f2 :=
    R f1 f2 ∧ (∀ x1 x2, ExpR x1 x2 → ExpR (APP f1 x1) (APP f2 x2));
  ExpR (τ:=_ × _) e1 e2 :=
    R e1 e2 ∧ ExpR (Fst e1) (Fst e2) ∧ ExpR (Snd e1) (Snd e2);
  ExpR e1 e2 := R e1 e2.

(* The base 关系 head component at every type: relatedness implies
 [R]. （已译） *)
Lemma ExpR_R {τ} {e1 e2 : Γ ⊢ τ} : ExpR e1 e2 → R e1 e2.
Proof. intros; induction τ; simpl in *; simp ExpR in X; now reduce. Qed.

(* [SubR] extends [ExpR] pointwise to substitutions. *)
Inductive SubR : ∀ {Γ'}, Sub Γ Γ' → Type :=
  | NoSubR : SubR (NoSub (Γ:=Γ))
  | PushR {Γ' τ} (e e' : Exp Γ τ) (s : Sub Γ Γ') :
    ExpR e e' → SubR s → SubR (Push e s).

Derive Signature for SubR.

End Log.
