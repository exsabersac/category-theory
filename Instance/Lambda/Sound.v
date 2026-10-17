Require Import Category.Lib.
Require Import Category.Instance.Lambda.Ltac.
Require Import Category.Instance.Lambda.Ty.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Log.
Require Import Category.Instance.Lambda.Sub.
Require Import Category.Instance.Lambda.Sem.
Require Import Category.Instance.Lambda.Step.

From Equations Require Import Equations.
Set Equations With UIP.

Section Sound.

Generalizable All Variables.

(** 本节：Soundness CCC semantics small-step reduction STLC （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/beta-reduction
 Wikipedia: https://en.wikipedia.org/wiki/Denotational_semantics

   本文件给出 λ 演算相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Reduction preserves denotation: [e ---> v] entails [SemExp e = SemExp v]. *)
Theorem soundness {Γ τ} {e : Exp Γ τ} {v} {se} :
  e ---> v → SemExp e se = SemExp v se.
Proof.
  intros.
  induction H; simpl; auto.
  - now rewrite IHStep.
  - now rewrite IHStep.
  - now rewrite IHStep.
  - now rewrite IHStep.
  - rewrite <- SemExp_SubSem.
    f_equal; simpl.
    simp SubSem.
    now rewrite SubSem_idSub.
  - now rewrite IHStep.
  - now rewrite IHStep.
Qed.

End Sound.
