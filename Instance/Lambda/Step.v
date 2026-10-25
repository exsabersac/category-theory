Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Instance.Lambda.Ltac.
Require Import Category.Instance.Lambda.Ty.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Value.
Require Import Category.Instance.Lambda.Ren.
Require Import Category.Instance.Lambda.Sub.
Require Import Category.Instance.Lambda.Sem.
Require Import Category.Instance.Lambda.Log.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

(** Small-step call-by-value reduction by congruence rules. / 通过合同规则进行的小步调用按值求值。 *)

(*
 This module gives the structural (congruence-rule) presentation of the
 small-step operational semantics for the de Bruijn STLC (see [Exp]).  The
 relation [e ---> e'] reduces one redex; the next redex is located not by a
 reified evaluation context (that is the job of [Full], which factors the
 same relation through [Frame]/[Ctxt]/[Plug]) but by one congruence rule per
 elimination form that descends into the appropriate subterm:

 ST_Pair1   x ---> x'              ⟹  Pair x y ---> Pair x' y
 ST_Pair2   ValueP x,  y ---> y'   ⟹  Pair x y ---> Pair x y'
 ST_Fst1    p ---> p'              ⟹  Fst p ---> Fst p'
 ST_Snd1    p ---> p'              ⟹  Snd p ---> Snd p'
 ST_AppL    e1 ---> e1'            ⟹  APP e1 e2 ---> APP e1' e2
 ST_AppR    ValueP v1, e2 ---> e2' ⟹  APP v1 e2 ---> APP v1 e2'

 and one contraction rule per elimination form at the root:

 ST_FstPair ValueP v1, ValueP v2  ⟹  Fst (Pair v1 v2) ---> v1
 ST_SndPair ValueP v1, ValueP v2  ⟹  Snd (Pair v1 v2) ---> v2
 ST_Beta    ValueP v              ⟹  APP (LAM e) v ---> SubExp {|| v ||} e

 The relation is call-by-value, not full beta: ST_Beta fires only when the
 argument is a value, the projections only when both components are values,
 and the rules guarding a second subterm on a value of the first (ST_Pair2,
 ST_AppR) fix a left-to-right evaluation order.  Reduction never proceeds
 under a [LAM].  Because [Step] is indexed by [Exp Γ τ] on both sides,
 preservation (subject reduction) holds by construction: a step cannot
 change the context or the type, so there is no separate preservation lemma.

 The metatheory established here: [strong_progress] (a closed well-typed
 term is a value or steps), [Value_irreducible]/[Value_cannot_start]/
 [value_is_nf] (values are normal forms), the congruence lemmas
 [AppL_LAM]/[AppR_LAM], and [Step_deterministic] (reduction is a partial
 function).  Semantic soundness of [--->] is proved in [Sound] and strong
 normalization in [Norm].

 References:
 small-step / structural operational semantics
 https://en.wikipedia.org/wiki/Operational_semantics
 beta-reduction      https://ncatlab.org/nlab/show/beta-reduction
 lambda-calculus     https://ncatlab.org/nlab/show/lambda-calculus 

 --------
 该模块给出了 de Bruijn STLC 的小步操作语义的结构性（同余规则）表示（参见 [Exp]）。关系 [e ---> e'] 归约一个重写表达式（redex）；下一个重写表达式不是通过反映的求值上下文定位的（这是 [Full] 的工作，它通过 [Frame] / [Ctxt] / [Plug] 对同一关系进行因式分解），而是通过每个消解形式对应的一个同余规则递降到相应的子项：

 ST_Pair1   x ---> x'              ⟹  Pair x y ---> Pair x' y
 ST_Pair2   ValueP x,  y ---> y'   ⟹  Pair x y ---> Pair x y'
 ST_Fst1    p ---> p'              ⟹  Fst p ---> Fst p'
 ST_Snd1    p ---> p'              ⟹  Snd p ---> Snd p'
 ST_AppL    e1 ---> e1'            ⟹  APP e1 e2 ---> APP e1' e2
 ST_AppR    ValueP v1, e2 ---> e2' ⟹  APP v1 e2 ---> APP v1 e2'在根部的每个消除形式上有一个收缩规则：

 ST_FstPair ValueP v1, ValueP v2  ⟹  Fst (Pair v1 v2) ---> v1
 ST_SndPair ValueP v1, ValueP v2  ⟹  Snd (Pair v1 v2) ---> v2
 ST_Beta    ValueP v              ⟹  APP (LAM e) v ---> SubExp {|| v ||} e

 该关系是按值调用，而不是完全 beta：ST_Beta 仅在参数为值时触发，投影仅在两个组件都是值时触发，而在第一个值的第二个子表达式上进行守卫的规则（ST_Pair2, ST_AppR）固定了从左到右的求值顺序。归约从不在 [LAM] 下进行。因为 [Step] 在两侧都由 [Exp Γ τ] 索引，所以通过构造可以保证保持性（主体归约）：一步不会改变上下文或类型，因此不需要单独的保持性引理。这里建立的元理论：[strong_progress]（一个闭合的良类型项是一个值或可以进行步骤），[Value_irreducible] / [Value_cannot_start] / [value_is_nf]（值是正规形式），合并引理 [AppL_LAM] / [AppR_LAM]，以及 [Step_deterministic]（规约是一个偏函数）。[--->] 的语义正确性在 [Sound] 中得到证明，强归约性在 [Norm] 中得到证明。

 参考文献：
 小步/结构操作语义 https://en.wikipedia.org/wiki/Operational_semantics
 β-规约 https://ncatlab.org/nlab/show/beta-reduction
 λ-演算 https://ncatlab.org/nlab/show/lambda-calculus
*)

Section Step.

Import ListNotations.

Open Scope Ty_scope.

Reserved Notation " t '--->' t' " (at level 40).

(*
 The single-step CBV reduction relation; intrinsically typed, so each step
 preserves the context [Γ] and type [τ] (preservation by construction). 

 --------
 单步 CBV 简化关系；本质上是类型化的，因此每一步都会保留上下文 [Γ] 和类型 [τ]（通过构造保持）。
*)
Inductive Step : ∀ {Γ τ}, Exp Γ τ → Exp Γ τ → Set :=
  | ST_Pair1 Γ τ1 τ2 (x x' : Exp Γ τ1) (y : Exp Γ τ2) :
    x ---> x' →
    Pair x y ---> Pair x' y
  | ST_Pair2 Γ τ1 τ2 (x : Exp Γ τ1) (y y' : Exp Γ τ2) :
    ValueP x →
    y ---> y' →
    Pair x y ---> Pair x y'

  | ST_Fst1 Γ τ1 τ2 (p p' : Exp Γ (TyPair τ1 τ2)) :
    p ---> p' →
    Fst p ---> Fst p'
  | ST_FstPair Γ τ1 τ2 (v1 : Exp Γ τ1) (v2 : Exp Γ τ2) :
    ValueP v1 →
    ValueP v2 →
    Fst (Pair v1 v2) ---> v1

  | ST_Snd1 Γ τ1 τ2 (p p' : Exp Γ (TyPair τ1 τ2)) :
    p ---> p' →
    Snd p ---> Snd p'
  | ST_SndPair Γ τ1 τ2 (v1 : Exp Γ τ1) (v2 : Exp Γ τ2) :
    ValueP v1 →
    ValueP v2 →
    Snd (Pair v1 v2) ---> v2

  | ST_Beta Γ dom cod (e : Exp (dom :: Γ) cod) (v : Exp Γ dom) :
    ValueP v →
    APP (LAM e) v ---> SubExp {|| v ||} e

  | ST_AppL Γ dom cod (e1 : Exp Γ (dom ⟶ cod)) e1' (e2 : Exp Γ dom) :
    e1 ---> e1' →
    APP e1 e2 ---> APP e1' e2

  | ST_AppR Γ dom cod (v1 : Exp Γ (dom ⟶ cod)) (e2 : Exp Γ dom) e2' :
    ValueP v1 →
    e2 ---> e2' →
    APP v1 e2 ---> APP v1 e2'

  where " t '--->' t' " := (Step t t').

Derive Signature for Step.

#[local] Hint Constructors ValueP Step : core.

#[local] Hint Extern 7 (_ ---> _) => repeat econstructor : core.

(* Progress: a closed (well-typed) term is either a value or can take a step. / 进展：一个封闭的（类型正确的）项要么是一个值，要么可以进行一步计算。 *)
Theorem strong_progress {τ} (e : Exp [] τ) :
  ValueP e ∨ ∃ e', e ---> e'.
Proof.
  dependent induction e; reduce.
  - now left; constructor.
  - destruct IHe1 as [V1|[e1' H1']];
    destruct IHe2 as [V2|[e2' H2']].
    + now left; constructor.
    + now right; eauto 6.
    + now right; eauto 6.
    + now right; eauto 6.
  - destruct IHe as [V|[e' H']].
    + dependent elimination V.
      * now right; eauto 6.
    + now right; eauto 6.
  - destruct IHe as [V|[e' H']].
    + dependent elimination V.
      * now right; eauto 6.
    + now right; eauto 6.
  - now inv v.
  - now left; constructor.
  - right.
    destruct IHe1 as [V1|[e1' H1']];
    destruct IHe2 as [V2|[e2' H2']].
    + dependent elimination V1;  now eauto 6.
    + dependent elimination H2'; now eauto 6.
    + dependent elimination H1'; now eauto 6.
    + dependent elimination H1'; now eauto 6.
Qed.

(* Values are irreducible (and the contrapositive [Value_cannot_start]): a value cannot be on the left of a step. / 价值是不可简化的（及其逆否命题 [Value_cannot_start]）：一个价值不能出现在步骤的左侧。 *)
Lemma Value_irreducible {Γ τ} {e e' : Exp Γ τ} :
  ValueP e → ¬ (e ---> e').
Proof.
  repeat intro.
  dependent induction H0;
  dependent elimination H;
  intuition eauto.
Qed.

Lemma Value_cannot_start {Γ τ} {e e' : Exp Γ τ} :
  (e ---> e') → ¬ ValueP e.
Proof.
  repeat intro.
  dependent induction H0;
  dependent elimination H;
  intuition eauto.
Qed.

(* Congruence lemmas restating ST_AppL/ST_AppR with the bound names used by downstream developments ([Multi], [Norm]). / 同余引理重述 ST_AppL/ST_AppR，使用下游开发中使用的绑定名称（[Multi]，[Norm]）。 *)
Lemma AppL_LAM {Γ dom cod} {e e' : Exp Γ (dom ⟶ cod)} {x : Exp Γ dom} :
  e ---> e' →
  APP e x ---> APP e' x.
Proof.
  intros.
  dependent induction H; now eauto 6.
Qed.

Lemma AppR_LAM {Γ dom cod} {e : Exp (dom :: Γ) cod} {x x' : Exp Γ dom} :
  x ---> x' →
  APP (LAM e) x ---> APP (LAM e) x'.
Proof.
  intros.
  dependent induction H; now eauto 6.
Qed.

(*
 A term is in normal form for [R] when no [R]-step issues from it.  The
 commented variant ¬ ∃ t', R t t' is logically equivalent but the ∀/¬ form
 below is more convenient to apply pointwise. 

 --------
 当没有 [R] 步从中产生时，[R] 的一个项处于正规形式。带注释的变体 ¬ ∃ t', R t t' 在逻辑上是等价的，但下面的 ∀/¬ 形式在逐点应用时更方便。
*)
Definition normal_form `(R : crelation X) (t : X) : Type :=
  ∀ t', ¬ R t t'.

Definition deterministic `(R : crelation X) : Type :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2.

(* Every value is a normal form (the [normal_form] packaging of irreducibility). / 每个值都是一种正规形式（不可约性的 [normal_form] 包装）。 *)
Lemma value_is_nf {Γ τ} (v : Exp Γ τ) :
  ValueP v → normal_form Step v.
Proof.
  repeat intro.
  dependent induction H0;
  now inv H.
Qed.

(*
 Determinism: the CBV strategy contracts a unique redex, so [--->] is a
 partial function.  Overlaps between congruence and contraction rules are
 ruled out via [Value_cannot_start] (a stepping subterm is not a value). 

 --------
 决定论：CBV策略收缩唯一的可约子，所以[--->]是一个部分函数。通过[Value_cannot_start]（一个可执行子项不是值）排除了同余和收缩规则之间的重叠。
*)
Theorem Step_deterministic Γ τ :
  deterministic (Step (Γ:=Γ) (τ:=τ)).
Proof.
  repeat intro.
  induction H0.
  - inv H.
    + now f_equal; intuition.
    + eapply Value_cannot_start in H5; eauto; tauto.
  - inv H.
    + eapply Value_cannot_start in H3; eauto; tauto.
    + now f_equal; intuition.
  - inv H.
    + now f_equal; intuition.
    + inv H0.
      * eapply Value_cannot_start in H6; eauto; tauto.
      * eapply Value_cannot_start in H7; eauto; tauto.
  - inv H.
    + inv H3.
      * eapply Value_cannot_start in H1; eauto; tauto.
      * eapply Value_cannot_start in H7; eauto; tauto.
    + now f_equal; intuition.
  - inv H.
    + now f_equal; intuition.
    + inv H0.
      * eapply Value_cannot_start in H6; eauto; tauto.
      * eapply Value_cannot_start in H7; eauto; tauto.
  - inv H.
    + inv H3.
      * eapply Value_cannot_start in H1; eauto; tauto.
      * eapply Value_cannot_start in H7; eauto; tauto.
    + now f_equal; intuition.
  - inv H; auto.
    + now inv H3.
    + eapply Value_cannot_start in H7; eauto; tauto.
  - inv H.
    + now inv H0.
    + now f_equal; intuition.
    + now inv H0.
  - inv H.
    + eapply Value_cannot_start in H0; eauto; tauto.
    + eapply Value_cannot_start in H4; eauto; tauto.
    + now f_equal; intuition.
Qed.

End Step.

Notation " t '--->' t' " := (Step t t') (at level 40).
