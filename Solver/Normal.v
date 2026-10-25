Require Import Coq.Lists.List.

From Equations Require Import Equations.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Solver.Expr.
Require Import Category.Solver.Denote.
Require Import Category.Solver.Reify.

(**
* Normalization: a normal form for free-category expressions

    This file is the heart of the reflective solver
    (https://en.wikipedia.org/wiki/Computational_reflection).  The only laws
    available for the syntactic [Term]s of Solver/Expr.v are the category
    axioms — associativity of [Comp] and the left/right identity laws for
    [Ident] — so the [Term]s are exactly the free category on the reified
    generators (https://ncatlab.org/nlab/show/free+category).  A morphism of a
    free category has a unique normal form: the *flattened list* of its
    generating arrows, with associativity making the bracketing irrelevant and
    the identity laws deleting every [Ident].

    The normal form is encoded by the mutually inductive [Morphism]:

      - [Identity] is the empty composite (the unit);
      - [Morphisms c] wraps a non-empty list [c : Composition] of arrows,
        where [Single f] is the one-element list [[f]] and [Composed f fs] is
        the cons [f :: fs].

    The list is ordered outermost-first, matching the [Comp f g = f ∘ g]
    convention of [termD] (f is applied last): [Composed f fs] denotes
    [f ∘ denote fs].  Composition of normal forms is therefore list
    concatenation ([append], proven associative by [append_assoc]) with
    [Identity] as the unit ([combine]); [to_morphism] folds a [Term] into its
    normal form and [from_morphism] reads a normal form back as a [Term].

    Soundness is the statement that normalization is invisible under the
    denotation of Solver/Denote.v.  It is proven in both directions —
    [from_morphism_to_morphism] and [from_morphism_to_morphism_r] — giving
    [termD d c (from_morphism (to_morphism t)) ≈ termD d c t]; the key step is
    that [combine] (list concatenation) denotes composition, established by the
    paired lemmas [from_morphism_app] and [from_morphism_app_r].  Lifting this
    to the whole proposition language yields [exprAD_sound : exprAD e ↔ exprD e]
    (an [↔], so the [normalize] tactic is both sound and complete for the goals
    it accepts), and [exprAD_sound'] specializes it for fast tactic use.

--------
* 归一化：自由范畴表达式的规范形式

这个文件是反射求解器的核心
    (https://en.wikipedia.org/wiki/Computational_reflection).  Solver/Expr.v 的语法 [Term] 唯一可用的定律是范畴公理——[Comp] 的结合律以及 [Ident] 的左/右恒等律——因此 [Term] 恰好是再化生成元的自由范畴 (https://ncatlab.org/nlab/show/free+category).  自由范畴的态射有唯一的标准形式：其生成箭头的*扁平化列表*，结合律使括号无关紧要，恒等律删除每一个 [Ident]。

该正常形式由相互归纳的 [Morphism] 编码：

- [Identity] 是空的复合体（该单元）；
- [Morphisms c] 包裹一个非空列表 [c : Composition] 的箭头，其中 [Single f] 是单元素列表 [[f]，而 [Composed f fs] 是构造的 [f :: fs]。

该列表按最外层优先排序，与[termD]的[Comp f g = f ∘ g]约定相匹配（f最后应用）：[Composed f fs]表示[f ∘ denote fs]。因此，标准形式的组合就是列表连接（[append]，通过[append_assoc]证明了结合性）以[Identity]作为单位（[combine]）；[to_morphism]将[Term]折叠成其标准形式，而[from_morphism]将标准形式读取回[Term]。

健全性是指在 Solver/Denote.v 的含义下归一化是不可见的。这在两个方向上都得到了证明——[from_morphism_to_morphism] 和 [from_morphism_to_morphism_r]——得出 [termD d c (from_morphism (to_morphism t)) ≈ termD d c t]；关键步骤是 [combine]（列表连接）表示组合，这是通过配对引理 [from_morphism_app] 和 [from_morphism_app_r] 确立的。将其提升到整个命题语言得到 [exprAD_sound : exprAD e ↔ exprD e]（一个 [↔]，所以 [normalize] 策略对于它接受的目标既健全又完备），而 [exprAD_sound'] 将其专门化以便快速使用策略。
*)

Section Normal.

Context `{Arrows}.

Inductive Morphism : Set :=
  | Identity
  | Morphisms (c : Composition)

with Composition : Set :=
  | Single   (f : Arrow)
  | Composed (f : Arrow) (fs : Composition)

with Arrow : Set :=
  | Arr (n : nat).

Ltac breakit :=
  lazymatch goal with
  | [ H : Morphism    |- _ ] => destruct H
  | [ H : Composition |- _ ] => destruct H
  | [ H : Arrow       |- _ ] => destruct H
  end.

Ltac substituted :=
  match goal with
  | [ n : nat, H : ∀ _ _ : nat, _ |- _ ] =>
    specialize (H n n); intuition
  | [ f : Morphism, g : Morphism, H : ∀ _ _ _ _ : Morphism, _ |- _ ] =>
    specialize (H f g f g); intuition
  | [ f : Arrow, g : Composition,
      H : ∀ (_ : Arrow) (_ : Composition)
            (_ : Arrow) (_ : Composition), _ |- _ ] =>
    specialize (H f g f g); intuition
  | [ f : Arrow, H : ∀ _ _ : Arrow, _ |- _ ] =>
    specialize (H f f); intuition
  | [ f : Composition, H : ∀ _ _ : Composition, _ |- _ ] =>
    specialize (H f f); intuition
  end.

Ltac solveit :=
  solve [ intros; subst; breakit; intuition; substituted
        | split; intros; breakit; intuition; discriminate ].

Local Set Warnings "-intuition-auto-with-star".

Program Fixpoint morphism_eq_dec (f g : Morphism) : {f = g} + {f ≠ g} :=
  match f, g with
  | Identity, Identity => left eq_refl
  | Morphisms fs, Morphisms gs =>
    match composition_eq_dec fs gs with
    | left  _ => in_left
    | right _ => in_right
    end
  | _, _ => right _
  end

with composition_eq_dec (f g : Composition) : {f = g} + {f ≠ g} :=
  match f, g with
  | Single f, Single g =>
    match arrow_eq_dec f g with
    | left  _ => in_left
    | right _ => in_right
    end
  | Composed f fs, Composed g gs =>
    match arrow_eq_dec f g with
    | left  _ =>
      match composition_eq_dec fs gs with
      | left  _ => in_left
      | right _ => in_right
      end
    | right _ => in_right
    end
  | _, _ => in_right
  end

with arrow_eq_dec (f g : Arrow) : {f = g} + {f ≠ g} :=
  match f, g with
  | Arr f, Arr g =>
    match PeanoNat.Nat.eq_dec f g with
    | left  _ => in_left
    | right _ => in_right
    end
  end.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.

#[export]
Program Instance Morphism_EqDec : EqDec Morphism := {
  eq_dec := morphism_eq_dec
}.

#[export]
Program Instance Composition_EqDec : EqDec Composition := {
  eq_dec := composition_eq_dec
}.

#[export]
Program Instance Arrow_EqDec : EqDec Arrow := {
  eq_dec := arrow_eq_dec
}.

Fixpoint append (f g : Composition) : Composition :=
  match f, g with
  | Single f, gs      => Composed f gs
  | Composed f fs, gs => Composed f (append fs gs)
  end.

Lemma append_assoc {f g h} :
  append f (append g h) = append (append f g) h.
Proof.
  induction f; simpl; auto.
  now rewrite IHf.
Qed.

Definition combine (f g : Morphism) : Morphism :=
  match f, g with
  | Identity, g => g
  | f, Identity => f
  | Morphisms fs, Morphisms gs => Morphisms (append fs gs)
  end.

Fixpoint to_morphism (t : Term) : Morphism :=
  match t with
  | Ident    => Identity
  | Morph a  => Morphisms (Single (Arr a))
  | Comp f g => combine (to_morphism f) (to_morphism g)
  end.

Coercion to_morphism : Term >-> Morphism.

Definition from_arrow (a : Arrow) : Term :=
  match a with
  | Arr f => Morph f
  end.

Fixpoint from_composition (fs : Composition) : Term :=
  match fs with
  | Single f => from_arrow f
  | Composed f gs => Comp (from_arrow f) (from_composition gs)
  end.

Definition from_morphism (f : Morphism) : Term :=
  match f with
  | Identity => Ident
  | Morphisms fs => from_composition fs
  end.

Ltac matches :=
  match goal with
  | [ H : context[match lookup_arr ?f ?dom with _ => _ end] |- _ ] =>
    destruct (lookup_arr f dom) as [[? ?]|] eqn:?
  | [ H : context[match @termD_work ?c ?h ?n ?s with _ => _ end] |- _ ] =>
    destruct (@termD_work c h n s) as [[? ?]|] eqn:?
  | [ H : context[match Classes.eq_dec ?n ?m with _ => _ end] |- _ ] =>
    destruct (eq_dec n m); subst
  end;
  try contradiction;
  try discriminate;
  let n := numgoals in guard n < 2.

Ltac desh :=
  repeat matches;
  simpl_eq;
  try rewrite peq_dec_refl in *;
  repeat lazymatch goal with
  | [ H : Some _ = Some _ |- _ ] =>
    inversion H; subst; try clear H
  | [ H : (?X; _) = (?X; _) |- _ ] =>
    apply Eqdep_dec.inj_pair2_eq_dec in H;
      [|now apply eq_dec]; subst
  | [ H : ∃ _, _ |- _ ] =>
    let x := fresh "x" in
    let e := fresh "e" in destruct H as [x e]
  | [ H : _ ∧ _ |- _ ] =>
    let x := fresh "x" in
    let e := fresh "e" in destruct H as [x e]
  end; auto; try solve [ cat ].

Lemma from_morphism_app {d c} {t1 t2 : Morphism} {f} :
  termD_work d (from_morphism (combine t1 t2)) = Some (c; f)
    → ∃ m g h, f ≈ g ∘ h
        ∧ termD_work m (from_morphism t1) = Some (c; g)
        ∧ termD_work d (from_morphism t2) = Some (m; h).
Proof.
  generalize dependent c.
  generalize dependent d.
  generalize dependent t2.
  unfold termD; destruct t1; simpl; intros.
  - eexists _, _, f.
    now split; cat.
  - generalize dependent c0.
    induction c; simpl; intros.
    + destruct t2; simpl in *.
      * exists d, f0, id.
        split; cat.
      * desh.
        exists _, h0, h.
        split; cat.
    + destruct t2; simpl in *; desh.
      * specialize (IHc _ _ eq_refl); desh.
        exists _, (h0 ∘ h), id.
        split; cat.
        now rewrite Heqo, Heqo0.
      * specialize (IHc _ _ eq_refl); desh.
        rewrite e.
        exists x0, (h0 ∘ x1), x2.
        rewrite x4, Heqo0.
        split; cat.
        rewrite x3; cat.
Qed.

Theorem from_morphism_to_morphism {d c} {t : Term} {f} :
  termD d c (from_morphism (to_morphism t)) = Some f
    → termD d c t ≈ Some f.
Proof.
  generalize dependent c.
  generalize dependent d.
  unfold termD; induction t; simpl; intros; desh.
  - pose proof (from_morphism_app Heqo); desh.
    specialize (IHt2 _ _ x1).
    rewrite e in IHt2; clear e.
    specialize (IHt1 _ _ x0).
    rewrite x3 in IHt1; clear x3.
    rewrite EqDec.peq_dec_refl in IHt1, IHt2.
    specialize (IHt1 eq_refl).
    specialize (IHt2 eq_refl).
    simpl in *; desh.
    rewrite Heqo1, EqDec.peq_dec_refl.
    now rewrite IHt1, IHt2, <- x2.
Qed.

Lemma from_morphism_app_r {d m c} {t1 t2 : Morphism} {g h} :
    termD_work m (from_morphism t1) = Some (c; g)
  → termD_work d (from_morphism t2) = Some (m; h)
  → ∃ f, f ≈ g ∘ h ∧
          termD_work d (from_morphism (combine t1 t2)) = Some (c; f).
Proof.
  generalize dependent c.
  generalize dependent d.
  generalize dependent t2.
  unfold termD; destruct t1; simpl; intros; desh.
  generalize dependent c0.
  induction c; simpl; intros; desh.
  - destruct t2; simpl in *; desh.
    exists (g ∘ h).
    split; cat.
    now rewrite H1, H0.
  - destruct t2; simpl in *; desh.
    + specialize (IHc _ _ eq_refl); desh.
      exists (h1 ∘ x0).
      split.
      * now rewrite x1; cat.
      * now rewrite e0, Heqo0.
    + specialize (IHc _ _ eq_refl); desh.
      exists (h1 ∘ x0).
      split.
      * now rewrite x1; cat.
      * now rewrite e0, Heqo0.
Qed.

Theorem from_morphism_to_morphism_r {d c} {t : Term} {f} :
  termD d c t = Some f
    → termD d c (from_morphism (to_morphism t)) ≈ Some f.
Proof.
  generalize dependent c.
  generalize dependent d.
  unfold termD; induction t; simpl; intros; desh.
  - specialize (IHt2 _ _ h).
    rewrite Heqo in IHt2; clear Heqo.
    specialize (IHt1 _ _ h0).
    rewrite Heqo0 in IHt1; clear Heqo0.
    rewrite EqDec.peq_dec_refl in IHt1, IHt2.
    specialize (IHt1 eq_refl).
    specialize (IHt2 eq_refl).
    simpl in *; desh.
    pose proof (from_morphism_app_r Heqo0 Heqo); desh.
    rewrite e0, EqDec.peq_dec_refl.
    now rewrite x1, IHt1, IHt2.
Qed.

(*
Normalization gives us a way to define the category of reified terms,
   whose hom-setoid identifies two terms exactly when they share a normal
   form.

--------
归一化为我们提供了一种定义具体化项类别的方法，其同类集仅在两个项共享规范形式时才将其识别为相同。
*)

#[local]
Program Instance Terms : Category := {
  obj        := Obj;
  hom        := λ _ _, Term;
  homset     := λ _ _,
    {| equiv f g := to_morphism f = to_morphism g |};
  id         := λ _, Ident;
  compose    := λ _ _ _, Comp;
}.
Next Obligation.
  unfold combine.
  induction (to_morphism f); auto.
Qed.
Next Obligation.
  unfold combine.
  induction (to_morphism g); auto.
  - induction (to_morphism f); auto.
  - induction (to_morphism f); auto.
    induction (to_morphism h); auto.
    now rewrite append_assoc.
Qed.
Next Obligation.
  symmetry.
  unshelve eapply Terms_obligation_5; eauto.
Qed.

Fixpoint exprAD (e : Expr) : Type :=
  match e with
  | Top    => True
  | Bottom => False
  | Equiv d c f g =>
    match termD d c (from_morphism (to_morphism f)),
          termD d c (from_morphism (to_morphism g)) with
    | Some f, Some g => f ≈ g
    | _, _ => False
    end
  | And p q  => exprAD p ∧ exprAD q
  | Or p q   => exprAD p + exprAD q
  | Impl p q => exprAD p → exprAD q
  end.

Theorem exprAD_sound (e : Expr) : exprAD e ↔ exprD e.
Proof.
  induction e; split; simpl in *; intuition; auto with *.
  - destruct (termD _ _ _) eqn:?; [|tauto].
    destruct (termD _ _ (_ (_ g))) eqn:?; [|tauto].
    apply from_morphism_to_morphism in Heqo.
    apply from_morphism_to_morphism in Heqo0.
    simpl in *.
    destruct (termD _ _ f); [|tauto].
    destruct (termD _ _ g); [|tauto].
    now rewrite Heqo, Heqo0, <- X.
  - desh.
    destruct (termD _ _ f) eqn:?; [|tauto].
    destruct (termD _ _ g) eqn:?; [|tauto].
    apply from_morphism_to_morphism_r in Heqo.
    apply from_morphism_to_morphism_r in Heqo0.
    simpl in *.
    destruct (termD _ _ _) eqn:?; [|tauto].
    destruct (termD _ _ (_ (_ g))) eqn:?; [|tauto].
    now rewrite Heqo, Heqo0, X.
Qed.

Fixpoint exprSD (e : Expr) : Type :=
  match e with
  | Top           => True
  | Bottom        => False
  | Equiv d c f g => (f : d ~> c) ≈ g
  | And p q       => exprSD p ∧ exprSD q
  | Or p q        => exprSD p + exprSD q
  | Impl p q      => exprSD p → exprSD q
  end.

Theorem exprSD_enough {d c f g h} :
  termD d c f = Some h →
  exprSD (Equiv d c f g) → exprAD (Equiv d c f g).
Proof.
  simpl; intros.
  rewrite H1.
  apply from_morphism_to_morphism_r in H0.
  rewrite H1 in H0.
  destruct (termD _ _ _) eqn:?.
  + reflexivity.
  + tauto.
Qed.

End Normal.

(**
The [exprAD e → exprD e] direction of [exprAD_sound], with the [Arrows]
    environment made an explicit argument.  Taking [env] explicitly lets the
    [normalize] tactic apply this with [simple apply] and no instance search,
    which is much faster than appealing to the full [↔].

--------
[exprAD e → exprD e] 对 [exprAD_sound] 的方向，在 [Arrows] 环境中给出了一个显式的参数。显式地采用 [env] 使得 [normalize] 策略可以用 [simple apply] 应用这个，而不进行实例搜索，这比依赖完整的 [↔] 要快得多。
*)
Corollary exprAD_sound' {cat} (env : Arrows cat) (e : Expr) :
  exprAD e → exprD e.
Proof. apply exprAD_sound. Qed.

Ltac normalize :=
  reify_and_change;
  simple apply exprAD_sound';
  vm_compute.

Ltac structure :=
  reify_and_change;
  simple apply exprAD_sound';
  simple eapply exprSD_enough;
    [now vm_compute|];
  clear.

Example ex_normalize
  (C : Category) (x y z w : C)
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
  (* Set Ltac Profiling. / 设置 Ltac 分析。 *)
  normalize.
  clear.
(*
reify_and_change.
  clear.                        (* no effect

--------
具象化并更改。
清除。                        （* 无效果
*)
*)
(*
  structure.                    (* only works on Coq 8.16 / 结构。                    （* 仅适用于 Coq 8.16 *)
*)
  reflexivity.
  (* Show Ltac Profile. / 显示 Ltac 配置文件。 *)
Qed.
