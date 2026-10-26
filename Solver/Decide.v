From Equations Require Import Equations.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Lib.IList.
Require Import Category.Theory.Category.
Require Import Category.Solver.Expr.
Require Import Category.Solver.Denote.
Require Import Category.Solver.Reify.
Require Import Category.Solver.Normal.

(**
* The decision procedure and its soundness theorem

    This file is the top of the [Solver/] reflective tower (Expr → Denote →
    Normal → Reify → Decide).  It assembles a decision procedure for morphism
    equalities and proves the one fact that makes the reflective tactic sound:
    if the procedure reports that two reified terms are equal, then their
    denotations are equal under [≈].  The technique is the standard “proof by
    reflection” (https://en.wikipedia.org/wiki/Computational_reflection):
    compute a verdict on the syntax, then transport that verdict to the
    original goal.

    The decision is structural: by [to_morphism] (Solver/Normal.v) a [Term] of
    the free category (https://ncatlab.org/nlab/show/free+category) is sent to a
    flat normal form, and two terms are judged equal exactly when their normal
    forms are [eq_dec]-equal.  Because [Term] normal forms have decidable
    equality and normalization is sound w.r.t. denotation, agreement of normal
    forms implies agreement of denotations.

    The verdict type [partial], its [Yes]/[No] constructors and the
    [Reduce]/[||]/[&&] notation are the decidability monad of Adam Chlipala's
    “Certified Programming with Dependent Types” (CPDT): a [partial P] is either
    a proof of [P] ([Proved]) or [Uncertain].  Note the asymmetry — an
    [Uncertain] result carries no refutation, it merely records that the
    procedure could not establish the goal.  Consequently only soundness is
    proved here, never the converse: the procedure is sound but not claimed to
    be complete, and an honest [Uncertain] is always permitted.  Soundness
    alone is exactly what a reflective tactic needs.

    [expr_sound] is the soundness lemma the tactics below rely on; the
    [categorify] and [categorical] entry points reify a categorical goal (via
    Solver/Reify.v), apply [expr_sound], and discharge the residual
    well-typedness side-condition by [vm_compute].

--------
* 决策程序及其正确性定理

该文件是 [Solver/] 反射塔的顶层（Expr → Denote → Normal → Reify → Decide）。它组装了一个用于态射等式的决策程序，并证明了使反射策略正确的一个事实：如果该程序报告两个重构的项相等，那么在 [≈] 下它们的表示也是相等的。该技术是标准的“通过反射证明”（https://en.wikipedia.org/wiki/Computational_reflection): 先对语法计算出一个判决，然后将该判决转移到原始目标）。

该决定是结构性的：通过 [to_morphism]（Solver/Normal.v）将自由范畴的 [Term]（https://ncatlab.org/nlab/show/free+category)）发送到平坦的规范形式，只有当它们的规范形式 [eq_dec] 相等时，两个项才被判断为相等。因为 [Term] 规范形式具有可判定的相等性，并且归一化在意义上是正确的，所以规范形式的一致性意味着意义的一致性。

裁决类型 [partial]，其 [Yes]/[No] 构造函数以及 [Reduce]/[||]/[&&] 表示法是 Adam Chlipala 的《基于依赖类型的认证编程》(Certified Programming with Dependent Types, CPDT) 的可判定性单子：一个 [partial P] 要么是 [P] ([Proved]) 的证明，要么是 [Uncertain]。请注意这种不对称——[Uncertain] 结果不携带反证，它仅仅记录该过程未能建立目标。因此这里只证明了正确性，从未证明相反情况：该过程是正确的，但不保证是完整的，而且总是允许进行诚实的 [Uncertain]。仅证明正确性正是反射策略所需要的。

[expr_sound] 是下面策略所依赖的健全性引理；[categorify] 和 [categorical] 入口点通过 Solver/Reify.v 对一个范畴目标进行具体化，应用 [expr_sound]，并通过 [vm_compute] 解决剩余的良态性附加条件。
*)

Section Decide.

Context `{Arrows}.

(**
[partial] and the [Yes]/[No]/[Reduce] machinery below are taken from
    Certified Programming with Dependent Types (CPDT).

--------
[partial] 和下面的 [Yes]/[No]/[Reduce] 机械取自《使用依赖类型的认证编程 (CPDT)》.
*)

Inductive partial (P : Type) : Type :=
| Proved : P → partial
| Uncertain : partial.

#[local] Notation "'Yes'" := (Proved _ _).
#[local] Notation "'No'" := (Uncertain _).

#[local] Notation "'Reduce' v" := (if v then Yes else No)
  (at level 100).
#[local] Notation "x || y" := (if x then Yes else Reduce y).
#[local] Notation "x && y" := (if x then Reduce y else No).

Program Fixpoint expr_forward (t : Expr) (hyp : Expr)
        (cont : partial (exprSD t)) :
  partial (exprSD hyp → exprSD t) :=
  match hyp with
  | Top           => Reduce cont
  | Bottom        => Yes
  | Equiv x y f g => Reduce cont
  | And p q       => Reduce cont
  | Or p q        => expr_forward t p cont && expr_forward t q cont
  | Impl _ _      => Reduce cont
  end.
Next Obligation. tauto. Defined.
Next Obligation. intuition. Defined.

#[local] Obligation Tactic := cat_simpl; intuition.

Program Fixpoint expr_backward (t : Expr) :
  partial (exprSD t) :=
  match t with
  | Top           => Yes
  | Bottom        => No
  | Equiv x y f g => Reduce (eq_dec (to_morphism f) (to_morphism g))
  | And p q       => expr_backward p && expr_backward q
  | Or p q        => expr_backward p || expr_backward q
  | Impl p q      => expr_forward q p (expr_backward q)
  end.

Definition expr_tauto t : partial (exprSD t).
Proof.
  intros; refine (Reduce (expr_backward t)); auto.
Defined.

#[export]
Program Instance Term_Setoid : Setoid Term := {
  equiv f g := ∀ d c,
    if expr_tauto (Equiv d c f g) then True else False
}.
Next Obligation.
  unfold expr_tauto.
  construct; repeat intro; simpl.
  - now rewrite peq_dec_refl.
  - destruct (eq_dec _ _).
    + destruct (eq_dec _ _); auto.
    + destruct (eq_dec _ _); auto.
  - destruct (eq_dec _ _).
    + destruct (eq_dec _ _); auto.
      * destruct (eq_dec _ _); auto.
        rewrite e, e0 in n.
        tauto.
      * destruct (eq_dec _ _); auto.
    + destruct (eq_dec _ _); auto.
      * destruct (eq_dec _ _); auto.
      * destruct (eq_dec _ _); auto.
Qed.

#[export]
Program Instance Comp_respects :
  Proper (equiv ==> equiv ==> equiv) Comp.
Next Obligation.
  proper.
  unfold expr_tauto in *.
  simpl in *.
  repeat destruct (eq_dec _ _); auto.
  rewrite e, e0 in n.
  contradiction.
Qed.

(**
Soundness of the procedure, in the form the tactics consume.  The
    [termD d c f = Some h] premise is a definedness witness — it states that
    [f] actually denotes a morphism [d ~> c] — and is discharged by
    [vm_compute] at the call site.  Given that and an equality [f ≈ g] of the
    interpreted terms, the reified goal [exprD (Equiv d c f g)] holds.

--------
过程的健全性，以策略所使用的形式。[termD d c f = Some h] 前提是定义性证据——它声明 [f] 实际上表示一个态射 [d ~> c]——并在调用处由 [vm_compute] 消解。考虑到这一点，以及解释项的等式 [f ≈ g]，重新化的目标 [exprD (Equiv d c f g)] 成立。
*)
Lemma expr_sound {d c f g h} :
  termD d c f = Some h → f ≈ g → exprD (Equiv d c f g).
Proof.
  intros.
  simple apply exprAD_sound'.
  specialize (X d c).
  revert X.
  unfold expr_tauto.
  destruct (expr_backward _); intuition.
  simple eapply exprSD_enough; eauto.
Qed.

End Decide.

Ltac categorify := reify_terms_and_then
  ltac:(fun env g =>
          change (@exprD _ env g);
          simple eapply expr_sound;
            [now vm_compute|eauto];
          clear).

Ltac categorical := reify_terms_and_then
  ltac:(fun env g =>
          change (@exprD _ env g);
          simple eapply expr_sound;
            [now vm_compute|eauto];
          clear;
          now vm_compute).

Example ex_categorical (C : Category) (x y z w : C)
  (f : z ~> w) (g : y ~> z) (h : x ~> y) (i : x ~> z) :
  g ∘ id ∘ id ∘ id ∘ h ≈ i ->
  g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
  g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
  g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
  g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
  g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
  g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
  g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
  g ∘ h ≈ i ->
  f ∘ (id ∘ g ∘ h) ≈ (f ∘ g) ∘ h.
Proof.
  intros.
  categorical.
  (* normalize. / 规范化。 *)
  (* categorify. / 分类化 *)
  (* assert (Comp (Morph 2) (Comp (Morph 1) (Morph 0)) ≈ *)
  (*           Comp (Comp (Morph 2) (Morph 1)) (Morph 0)). { / Comp (Comp (形态 2) (形态 1)) (形态 0)). { *)
  (*   now vm_compute. / 现在 vm_compute。 *)
  (* } *)
  (* rewrite X. / 重写 X。 *)
  (* now vm_compute. / 现在 vm_compute。 *)
Qed.
