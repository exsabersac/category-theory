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

(** Soundness of the CCC semantics for the small-step reduction of the STLC / STLC 小步归约的 CCC 语义的健全性 *)

(*
 nLab: https://ncatlab.org/nlab/show/relation+between+type+theory+and+category+theory
 nLab: https://ncatlab.org/nlab/show/beta-reduction
 Wikipedia: https://en.wikipedia.org/wiki/Denotational_semantics

 This is the semantic payoff of the Curry-Howard-Lambek correspondence for
 the de Bruijn STLC: the denotational interpretation [SemExp] of Sem.v into
 the CCC (here Coq's [Type]) is sound with respect to the call-by-value
 reduction [--->] of Step.v.  Concretely,

 e ---> v   implies   ⟦e⟧ = ⟦v⟧            (as maps ⟦Γ⟧ → ⟦τ⟧)

 so a reduction step never changes the denotation.  Each congruence rule
 (ST_Pair1/2, ST_Fst1, ST_Snd1, ST_AppL/R) follows by the induction
 hypothesis on the reduced subterm; the two projection contractions
 (ST_FstPair, ST_SndPair) hold definitionally because [fst]/[snd] compute on
 a pair; and ST_Beta is the categorical β-law: substitution commutes with
 interpretation ([SemExp_SubSem]), and the single substitution {|| v ||}
 denotes pairing [v] onto the identity environment ([SubSem_idSub]), which is
 exactly the counit (evaluation) of the product-exponential adjunction.  This
 gives soundness of the model; completeness is Lambek's theorem (the syntax
 is the free CCC, Sem.v). 

 --------
 nLab:  https://ncatlab.org/nlab/show/relation+between+type+theory+and+category+theory 
 nLab:  https://ncatlab.org/nlab/show/beta-reduction 
 维基百科:  https://en.wikipedia.org/wiki/Denotational_semantics 

 这是 Curry-Howard-Lambek 对应在 de Bruijn 简单类型 λ 演算 (STLC) 上的语义回报：Sem.v 在 CCC 中的指称解释 [SemExp] （此处为 Coq 的 [Type]）对于 Step.v 的按值调用归约 [--->] 是健全的。具体来说，

 e ---> v   意味着   ⟦e⟧ = ⟦v⟧            （作为映射 ⟦Γ⟧ → ⟦τ⟧）因此一个归约步骤从不改变指称。每条合同规则 (ST_Pair1/2, ST_Fst1, ST_Snd1, ST_AppL/R) 都可以通过对已归约子项的归纳假设得到；两个投影收缩 (ST_FstPair, ST_SndPair) 在定义上成立，因为 [fst] / [snd] 可以在一对上计算；而 ST_Beta 是范畴 β-律：替换与解释 ([SemExp_SubSem]) 交换，并且单一替换 {|| v ||} 在恒等环境 ([SubSem_idSub]) 上表示配对 [v]，这正好是乘积-指数伴随的余单位（求值）。这给出了模型的健全性；完备性是 Lambek 定理（语法是自由 CCC, Sem.v）。
*)

(* Reduction preserves denotation: [e ---> v] entails [SemExp e = SemExp v]. / 化简保持指称：[e ---> v] 蕴含 [SemExp e = SemExp v]。 *)
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
