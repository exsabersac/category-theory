Require Import Category.Lib.
Require Import Category.Instance.Lambda.Ltac.
Require Import Category.Instance.Lambda.Ty.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Value.
Require Import Category.Instance.Lambda.Ren.
Require Import Category.Instance.Lambda.Sub.
Require Import Category.Instance.Lambda.Log.
Require Import Category.Instance.Lambda.Sem.
Require Import Category.Instance.Lambda.Multi.
Require Import Category.Instance.Lambda.Sound.
Require Import Category.Instance.Lambda.Step.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

(** Strong normalization of the intrinsically-typed STLC. / 内在类型的简单类型λ演算的强归约性。 *)

(*
 Every well-typed closed expression reduces to a value.  Because [Step] is
 deterministic (see [Step_deterministic]) there is a single reduction
 sequence out of each term, so reaching a value (here [halts]) coincides with
 strong normalization; the [SN]/[strong_normalization] naming reflects that
 identification.

 The argument is Tait's reducibility / logical-relations method (Tait 1967,
 Girard's “reducibility candidates”):
 https://softwarefoundations.cis.upenn.edu/plf-current/Norm.html

 The reducibility predicate is [SN := ExpP halts], where [ExpP] (from [Log])
 recurses on the type:
 - base ([Unit]):  SN e  :=  halts e
 - arrow (σ ⟶ τ):  SN e  :=  halts e ∧ (∀ x, SN x → SN (APP e x))
 - product (σ × τ): SN e  :=  halts e ∧ SN (Fst e) ∧ SN (Snd e)
 The arrow clause is the crux: halting alone is not preserved by application,
 since β-reduction substitutes the argument and may expose fresh redexes, so
 reducibility must close over application.

 Strong normalization then follows in two steps:
 - the fundamental lemma [SubExp_SN]: under a reducible substitution every
 expression is reducible (the analogue of Software Foundations' msubst_R);
 - [Exp_SN] instantiates it at the empty substitution, and
 [strong_normalization] extracts the halting witness via [SN_halts]. 

 --------
 每个良类型的闭合表达式都能化简为一个值。因为 [Step] 是确定性的（见 [Step_deterministic]），所以每个项都有唯一的化简序列，因此达到一个值（这里是 [halts]）与强归约一致；[SN] / [strong_normalization] 的命名反映了这种对应关系。

 这个论证是 Tait 的可约性 / 逻辑关系方法（Tait 1967，Girard 的“可约性候选”）：https://softwarefoundations.cis.upenn.edu/plf-current/Norm.html可约性谓词是 [SN := ExpP halts]，其中 [ExpP]（来自 [Log]）按照类型递归：
 - 基础类型（[Unit]）：SN e := e 停机
 - 函数类型（σ ⟶ τ）：SN e := e 停机 ∧ (∀ x, SN x → SN (APP e x))
 - 乘积类型（σ × τ）：SN e := e 停机 ∧ SN (Fst e) ∧ SN (Snd e)
 函数类型这一条是关键：单独停机并不能通过应用保持不变，因为 β-归约会替换参数并可能暴露新的可化简表达式，因此可约性必须对应用封闭。

 强归约性随后分两步得出：
 - 基本引理 [SubExp_SN]：在可约替换下，每个表达式都是可约的（类似于 Software Foundations 中的 msubst_R）；
 - [Exp_SN] 在空替换下实例化它，并通过 [SN_halts] 提取停机证明 [strong_normalization]。
*)

Section Norm.

#[local] Hint Constructors ValueP Step : core.

#[local] Hint Extern 7 (_ ---> _) => repeat econstructor : core.

(* A relation is normalizing when every element reaches a normal form. / 当每个元素都达到规范形式时，关系就是规范化的。 *)
Definition normalizing `(R : crelation X) : Type :=
  ∀ t, ∃ t', multi R t t' ∧ normal_form R t'.

(* [e] halts when it reduces in finitely many steps to a value. / 当 [e] 在有限步数内归约到一个值时，它会停止。 *)
Definition halts {Γ τ} (e : Exp Γ τ) : Type :=
  ∃ e', e --->* e' ∧ ValueP e'.

Notation " e '⇓' " := (halts e) (at level 11).

(* [e'] is a normal form of [e]: reachable from [e] and itself irreducible. / [e'] 是 [e] 的一个正常形式：可以从 [e] 到达，并且自身不可约。 *)
Definition normal_form_of {Γ τ} (e e' : Exp Γ τ) : Type :=
  (e --->* e' ∧ normal_form Step e').

(*
 Discharge a goal that contradicts irreducibility: a value or normal form
 cannot take a step. 

 --------
 消解与不可约性相矛盾的目标：一个值或规范形式不能进行一步转化。
*)
Ltac normality :=
  exfalso;
  lazymatch goal with
    | [ H1 : ValueP ?X, H2 : ?X ---> ?Y |- False ] =>
        apply value_is_nf in H1; destruct H1;
        now exists Y
    | [ H1 : normal_form ?R ?X, H2 : ?R ?X ?Y |- False ] =>
        exfalso; now apply (H1 Y)
  end.

(*
 Close a step-inversion subgoal, either by inverting the step or via
 [normality]. 

 --------
 关闭一个步骤反转子目标，可以通过反转该步骤或通过 [normality] 来实现。
*)
Ltac invert_step :=
  try lazymatch goal with
  | [ H : _ ---> _ |- _ ] => now inv H
  end;
  try solve [ f_equal; intuition eauto | normality ].

(* A value already halts: it reaches itself in zero steps. / 一个值已经停止：它在零步中达到自身。 *)
Lemma value_halts {Γ τ} (v : Exp Γ τ) : ValueP v → halts v.
Proof.
  intros X.
  unfold halts.
  now induction X; eexists; repeat constructor.
Qed.

(* Normal forms are unique, since [Step] is deterministic. / 范式是唯一的，因为 [Step] 是确定性的。 *)
Theorem normal_forms_unique Γ τ :
  deterministic (normal_form_of (Γ:=Γ) (τ:=τ)).
Proof.
  unfold deterministic, normal_form_of.
  intros x y1 y2 P1 P2.
  destruct P1 as [P11 P12].
  destruct P2 as [P21 P22].
  generalize dependent y2.
  induction P11; intros.
  - inversion P21; auto.
    now einduction P12; eauto.
  - apply IHP11; auto.
    inv P21.
    + now edestruct P22; eauto.
    + assert (y = y0) by now apply Step_deterministic with x.
      now subst.
Qed.

(* A single step neither creates nor destroys halting (forward determinism). / 单一步骤既不会产生也不会破坏停机（前向确定性）。 *)
Lemma step_preserves_halting {Γ τ} (e e' : Exp Γ τ) :
  (e ---> e') → (halts e ↔ halts e').
Proof.
  intros.
  unfold halts.
  split.
  - intros [e'' [H1 H2]].
    + destruct H1.
      * apply value_is_nf in H2.
        now edestruct H2; eauto.
      * rewrite (Step_deterministic _ _ _ _ _ H s).
        now intuition eauto.
  - intros [e'0 [H1 H2]].
    + exists e'0.
      split; auto.
      now eapply multi_step; eauto.
Qed.

(*
 The reducibility predicate: [halts] lifted type-directed through [ExpP].
 At arrow and product types this also requires the type-indexed components
 (applications, projections) to be reducible, the closure that makes the
 fundamental lemma go through. 

 --------
 可约谓词：[halts] 通过[ExpP] 提升类型导向。在箭头和乘积类型上，这还要求类型索引的组件（应用、投影）是可约的，这种闭包使基本引理得以成立。
*)
Definition SN {Γ τ} : Γ ⊢ τ → Type := ExpP (@halts Γ).
Arguments SN {Γ τ} _ /.

(* Reducibility extended pointwise to substitutions. / 可约性扩展到逐点替换。 *)
Definition SN_Sub {Γ Γ'} : Sub Γ' Γ → Type := SubP (@halts Γ').
Arguments SN_Sub {Γ Γ'} /.

(* CR1: reducible expressions halt (extract the [halts] component of [ExpP]). / CR1：可约表达式停止（提取 [ExpP] 的 [halts] 组件）。 *)
Definition SN_halts {Γ τ} {e : Γ ⊢ τ} : SN e → halts e := ExpP_P _.

#[local] Transparent ExpP.

(* CR2 forward: reducibility is preserved by a reduction step. / CR2 前向：可约性由一个归约步骤保持。 *)
Lemma step_preserves_SN {Γ τ} {e e' : Γ ⊢ τ} :
  (e ---> e') → SN e → SN e'.
Proof.
  intros.
  induction τ; simpl in *;
  pose proof H as H2;
  apply step_preserves_halting in H2;
  firstorder.
Qed.

(* CR2 forward, iterated over a multi-step reduction. / CR2 前进，经过多步迭代归约。 *)
Lemma multistep_preserves_SN {Γ τ} {e e' : Γ ⊢ τ} :
  (e --->* e') → SN e → SN e'.
Proof.
  intros.
  induction X; auto.
  apply IHX.
  now eapply step_preserves_SN; eauto.
Qed.

(*
 CR3 (backward closure): reducibility is reflected by a reduction step.
 This is where determinism of [Step] is essential. 

 --------
 CR3（向后闭包）：可约性通过一个约简步骤体现。这里 [Step] 的确定性是必不可少的。
*)
Lemma step_preserves_SN' {Γ τ} {e e' : Γ ⊢ τ} :
  (e ---> e') → SN e' → SN e.
Proof.
  intros.
  induction τ; simpl in *;
  pose proof H as H2;
  apply step_preserves_halting in H2;
  firstorder.
Qed.

(* Backward closure, iterated over a multi-step reduction. / 向后闭包，经过多步归约迭代。 *)
Lemma multistep_preserves_SN' {Γ τ} {e e' : Γ ⊢ τ} :
  (e --->* e') → SN e' → SN e.
Proof.
  intros.
  induction X; auto.
  now eapply step_preserves_SN'; eauto.
Qed.

(*
 The fundamental lemma (Software Foundations' msubst_R): under a reducible
 substitution [env], every expression [e] is reducible.  Proved by induction
 on [e], using the closure lemmas above for the eliminator cases (Fst/Snd,
 APP) and [SubExp_Push] to handle the β-redex created by LAM applied to an
 argument. 

 --------
 基本引理（Software Foundations 的 msubst_R）：在可约替换 [env] 下，每个表达式 [e] 都是可约的。通过对 [e] 进行归纳证明，使用上述闭包引理处理消元器情况（Fst/Snd，APP），并使用 [SubExp_Push] 处理 LAM 应用于某个参数时产生的 β-规约表达式。
*)
Lemma SubExp_SN {Γ Γ'} (env : Sub Γ' Γ) {τ} (e : Exp Γ τ) :
  SN_Sub env →
  SN (SubExp env e).
Proof.
  generalize dependent env.
  induction e; intros; simpl.
  - now eexists; repeat constructor.
  - split.
    + destruct (SN_halts (IHe1 env X)) as [v1 [P1 Q1]].
      destruct (SN_halts (IHe2 env X)) as [v2 [P2 Q2]].
      exists (Pair v1 v2).
      split.
      * now apply multistep_Pair.
      * now repeat constructor.
    + split.
      * destruct (SN_halts (IHe1 env X)) as [v1 [P1 Q1]].
        destruct (SN_halts (IHe2 env X)) as [v2 [P2 Q2]].
        apply (multistep_preserves_SN' (e':=v1)); auto.
        ** rewrite (multistep_Fst1 (p':=Pair v1 v2)).
           *** now apply multi_R; eauto.
           *** erewrite multistep_Pair1; eauto.
               erewrite multistep_Pair2; eauto.
               now apply multi_refl.
        ** apply (multistep_preserves_SN (e:=SubExp env e1));
           now intuition.
      * destruct (SN_halts (IHe1 env X)) as [v1 [P1 Q1]].
        destruct (SN_halts (IHe2 env X)) as [v2 [P2 Q2]].
        apply (multistep_preserves_SN' (e':=v2)); auto.
        ** rewrite (multistep_Snd1 (p':=Pair v1 v2)).
           *** now apply multi_R; eauto.
           *** erewrite multistep_Pair1; eauto.
               erewrite multistep_Pair2; eauto.
               now apply multi_refl.
        ** apply (multistep_preserves_SN (e:=SubExp env e2));
           now intuition.
  - now apply IHe.
  - now apply IHe.
  - induction env.
    + now inv v.
    + dependent elimination X.
      now dependent elimination v; simpl in *; simp SubVar.
  - split.
    + now eexists; repeat constructor.
    + intros.
      destruct (SN_halts X0) as [v [P Q]].
      apply (multistep_preserves_SN' (e':=SubExp (Push v env) e)); auto.
      * eapply multi_trans; eauto.
        ** now eapply multistep_AppR; eauto.
        ** apply multi_R; auto.
           now rewrite SubExp_Push; eauto 6.
      * apply IHe.
        constructor; auto.
        now eapply multistep_preserves_SN; eauto.
  - now apply IHe1, IHe2.
Qed.

(*
 Every closed expression is reducible: instantiate the fundamental lemma at
 the empty (identity) substitution. 

 --------
 每个封闭表达式都是可约的：在空（恒等）替换下实例化基本引理。
*)
Theorem Exp_SN {τ} (e : Exp nil τ) : SN e.
Proof.
  intros.
  replace e with (SubExp (Γ:=nil) NoSub e).
  - apply SubExp_SN.
    now constructor.
  - now rewrite NoSub_idSub, SubExp_idSub.
Qed.

(* Strong normalization: every closed expression halts at a value. / 强归约性：每个封闭表达式最终都会归约到一个值。 *)
Corollary strong_normalization {τ} (e : Exp nil τ) : e ⇓.
Proof.
  pose proof (Exp_SN e) as X.
  now apply SN_halts.
Qed.

End Norm.
