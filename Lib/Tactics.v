(* * * Custom tactics shared across the library / * * 库内共享的定制策略 *)

(*
 This file collects the bespoke Ltac tactics and hint databases that the
 rest of the development relies on.  Because the library models morphisms as
 setoids (equivalence classes under [≈], not strict [=]), the standard
 automation built around [eq] is not enough: proofs must discharge
 reflexivity/symmetry/transitivity of [equiv], respectfulness ([Proper]),
 and the category laws stored in dedicated rewrite/auto hint databases.  The
 tactics below package those recurring obligations.

 The two workhorses are [cat] (used in hundreds of files) and [cat_simpl],
 which is installed globally as the [Program] obligation tactic so that most
 [Program Instance] obligations are dispatched automatically.

 Two hint databases drive the automation:
 - [categories]    : rewrite database of equational category laws
 (e.g. [id_left], [id_right], [fmap_id]), populated
 throughout the library; consumed by [autorewrite].
 - [category_laws] : auto database closing setoid goals via the
 reflexivity/symmetry/transitivity externs declared
 below plus per-construction lemmas; consumed by [auto].

 These tactics are project-internal conveniences with no external
 reference; the underlying ideas (setoid rewriting, equivalence relations,
 [Proper]/respectful morphisms) are standard Coq/Rocq machinery.  None of
 the tactics here cheat: none leaves a goal unproven and none introduces an
 axiom; each either makes progress and closes goals or fails. 

 --------
 本文件汇集开发其余部分依赖的定制 Ltac 策略与提示库。因本库把态射建模为 setoid（[≈] 下的等价类，而非严格 [=]），围绕 [eq] 的标准自动化不够：证明须消解 [equiv] 的自反/对称/传递、尊重性（[Proper]），以及存放在专用 rewrite/auto 提示库中的范畴律。下文策略打包这些反复出现的义务。

 两大主力是 [cat]（数百文件使用）与 [cat_simpl]（全局安装为 [Program] 义务策略，使多数 [Program Instance] 义务自动消解）。

 两个提示库驱动自动化：
 - [categories]    ：等式范畴律的 rewrite 库（如 [id_left]、[id_right]、[fmap_id]），由全库填充；供 [autorewrite] 消费。
 - [category_laws] ：经下文声明的自反/对称/传递 extern 以及各构造引理关闭 setoid 目标的 auto 库；供 [auto] 消费。

 这些策略是项目内部便利设施，无外部文献对应；底层思想（setoid 重写、等价关系、[Proper]/尊重态射）是标准 Coq/Rocq 机制。此处策略皆不作弊：不留下未证目标、不引入公理；要么推进并关闭目标，要么失败。
*)

(*
   【常用 tactic 一眼表】/ Tactic cheat-sheet (beginner)

   本库态射用 ≈，标准 eq 自动化不够；下面几条是日常收尾工具。
   Morphisms use ≈, so eq-automation is not enough; these close goals daily.

   - cat        : 拆联结词 → autorewrite categories → auto category_laws
                  （最常用收尾 / the usual closer）
   - cat_simpl  : Program 义务默认策略；先尝试自动证完 Equivalence/Proper
                  （Global Obligation Tactic）
   - simplify   : 反复拆 ∧/∨/对/sigma/单位
   - equivalence: 证 Equivalence（constructor + 三律）
   - proper     : 证 Proper / respectful
   - construct  : unshelve econstructor 开记录
   - simpl_eq   : 展开 eq_rect 等传送子
   - sapply / srewrite / srewrite_r : 先 cbn 再 apply/rewrite（看清投影）
   - inv / spose : 反演；引入并 simpl 假设

   提示库 / Hint DBs
   - categories    : 范畴等式律（供 autorewrite）
   - category_laws : setoid 自反/对称/传递等（供 auto）

   不必一次记全；看到证明里 cat / cat_simpl 即可对照本表。
   No need to memorize all; match cat / cat_simpl in proofs to this table.
*)

Require Import Coq.Bool.Bool.

Require Export Category.Lib.Setoid.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Open Scope lazy_bool_scope.

Module Compat.
  (*
 In Rocq 9.2 the EqdepFacts.internal_foo schemes moved to Init.Logic
 and dropped the "internal".

 This module uses shadowing to refer to the schemes by the same
 name regardless of Rocq version. 

 --------
 在 Rocq 9.2 中，EqdepFacts.internal_foo 模式移至 Init.Logic，并去掉 “internal” 前缀。

 本模块用遮蔽，使无论 Rocq 版本都以同一名称引用这些模式。
*)

  Module Fake.
    Notation internal_eq_rew_r_dep := ltac:(fail "should not happen") (only parsing).
    Notation internal_eq_sym_involutive := ltac:(fail "should not happen") (only parsing).
    Notation internal_eq_sym_internal := ltac:(fail "should not happen") (only parsing).
  End Fake.

  Module FromEqdepFactsIfExists.
    Import Fake.
    Import EqdepFacts.

    (*
 if eq_rew_r_dep exists in EqdepFacts then it is used here,
 otherwise this is the "fake" notation 

 --------
 若 EqdepFacts 中存在 eq_rew_r_dep 则在此使用，否则这是“假”记号。
*)
    Notation eq_rew_r_dep := internal_eq_rew_r_dep.

    (* same for the other notations / 其他记号同理 *)
    Notation eq_sym_involutive := internal_eq_sym_involutive.
    Notation eq_sym := internal_eq_sym_internal.
  End FromEqdepFactsIfExists.

  Import FromEqdepFactsIfExists.
  Import Logic.

  (*
 if eq_rew_r_dep exists in Logic then it is used here,
 otherwise this is internal_eq_rew_r_dep through FromEqdepFactsIfExists. 

 --------
 若 Logic 中存在 eq_rew_r_dep 则在此使用，否则经 FromEqdepFactsIfExists 使用 internal_eq_rew_r_dep。
*)
  Notation eq_rew_r_dep := eq_rew_r_dep.

  (* same for the other notations / 其他记号同理 *)
  Notation eq_sym_involutive := eq_sym_involutive.
  Notation eq_sym := eq_sym.
End Compat.

(*
 [simpl_eq]: unfold the [eq]-rewriting eliminators ([eq_rect] and friends,
 plus the version-shimmed [Compat] schemes) everywhere, exposing the
 underlying transports so they can be simplified or rewritten. 

 --------
 [simpl_eq]：处处展开 [eq]-改写消去子（[eq_rect] 及其友元，以及经版本垫片的 [Compat] 模式），暴露底层传送以便化简或改写。
*)
Ltac simpl_eq :=
  unfold eq_rect_r, eq_rect, eq_ind_r, eq_ind, eq_sym, prod_rect,
    Compat.eq_rew_r_dep,
    Compat.eq_sym_involutive,
    Compat.eq_sym in *.

(*
 [simplify]: repeatedly break apart logical/structural connectives in both
 hypotheses and goal -- units, lazy and strict [&&], conjunctions ([∧], [/\]),
 bi-implications ([↔]), pairs/products and sigma types -- introducing the
 pieces.  Each arm strictly consumes or refines its target, so the [repeat]
 terminates. 

 --------
 [simplify]：反复拆开假设与目标中的逻辑/结构联结词——单位、惰性与严格 [&&]、合取（[∧]、[/\]）、双蕴涵（[↔]）、对/积与 sigma 类型——引入各片。每臂严格消耗或精化其目标，故 [repeat] 终止。
*)
Ltac simplify :=
  repeat
    (match goal with
     | [ H : () |- _ ] => destruct H
     | [ |- () ] => exact tt

     | [ H : (_ &&& _) = true |- _ ] => rewrite <- andb_lazy_alt in H
     | [ |- (_ &&& _) = true ]       => rewrite <- andb_lazy_alt
     | [ H : (_ && _) = true |- _ ]  => apply andb_true_iff in H
     | [ |- (_ && _) = true ]        => apply andb_true_iff; split

     | [ H : _ ∧ _ |- _ ] =>
       let H' := fresh "H" in destruct H as [H H']
     | [ |- _ ∧ _ ] => split

     | [ H : _ /\ _ |- _ ] =>
       let H' := fresh "H" in destruct H as [H H']
     | [ |- _ /\ _ ] => split

     | [ H : _ ↔ _ |- _ ] =>
       let H' := fresh "H" in destruct H as [H H']
     | [ |- _ ↔ _ ] => split

     | [ H : (_, _) = (_, _) |- _ ] => inversion_clear H

     | [ H : _ * _ |- _ ] =>
       let x := fresh "x" in
       let y := fresh "y" in
       destruct H as [x y]
     | [ |- _ * _ ] => split

     | [ H : { _ : _ & _ } |- _ ] =>
       let x := fresh "x" in
       let e := fresh "e" in
       destruct H as [x e]
     | [ |- { _ : _ & _ } ] =>
       unshelve (refine (existT _ _ _))
     end; intros).

(*
 [cat]: the standard category-proof closer.  Simplify connectives, rewrite
 with the equational [categories] laws, then discharge the residue with the
 [category_laws] auto database, falling back to reflexivity. 

 --------
 [cat]：标准范畴证明收尾。化简联结词，用等式 [categories] 律改写，再以 [category_laws] auto 库消解残余，回退到 reflexivity。
*)
Ltac cat :=
  simplify;
  autorewrite with categories;
  auto with category_laws;
  try reflexivity.

(*
 Teach the [core] database to see through the equivalence-relation
 structure: unfold Reflexive/Symmetric/Transitive/Proper/respectful and
 build an [Equivalence] from its three components on demand. 

 --------
 让 [core] 库看穿等价关系结构：展开 Reflexive/Symmetric/Transitive/Proper/respectful，并按需从其三分量构造 [Equivalence]。
*)
#[export] Hint Constructors Equivalence : core.

#[export] Hint Unfold Reflexive : core.
#[export] Hint Unfold Symmetric : core.
#[export] Hint Unfold Transitive : core.

#[export] Hint Extern 1 (Reflexive ?X) =>
  unfold Reflexive : core.
#[export] Hint Extern 1 (Symmetric ?X) =>
  unfold Symmetric : core.
#[export] Hint Extern 1 (Transitive ?X) =>
  unfold Transitive : core.
#[export] Hint Extern 1 (Equivalence ?X) =>
  apply Build_Equivalence : core.
#[export] Hint Extern 1 (Proper _ _) => unfold Proper : core.
#[export] Hint Extern 8 (respectful _ _ _ _) =>
  unfold respectful : core.

(*
 Seed [category_laws] with the setoid laws for [equiv]: reflexivity for
 syntactically equal sides, and symmetry/transitivity as guarded externs so
 [auto] can chain [≈] hypotheses. 

 --------
 用 [equiv] 的 setoid 律播种 [category_laws]：语法相等两侧的自反，以及作为守卫 extern 的对称/传递，使 [auto] 能串联 [≈] 假设。
*)
#[export] Hint Extern 4 (equiv ?A ?A) => reflexivity : category_laws.
#[export] Hint Extern 6 (equiv ?X ?Y) =>
  apply Equivalence_Symmetric : category_laws.
#[export] Hint Extern 7 (equiv ?X ?Z) =>
  match goal with
    [H : equiv ?X ?Y, H' : equiv ?Y ?Z |- equiv ?X ?Z] => transitivity Y
  end : category_laws.

(*
 [equivalence]: prove an [Equivalence] goal by splitting into its three laws
 ([constructor]) and discharging each with [cat]/[intuition].

 The explicit reflexivity/symmetry pass is load-bearing rather than
 decorative.  When the relation is assembled from other equivalences -- a
 pair of natural isomorphisms, say -- those two laws are closed only if the
 tactic reaches [solve_crelation], a pattern-less [Hint Extern] in the
 standard library's [crelations] database, through a wide [auto].  This
 tactic once ended in [auto with *], which reached it; that fallback was
 later narrowed to [auto with category_laws] for hygiene, and the proofs
 kept building only because the [intuition] step above has its own wide
 [auto with *] leaf that still reached the hint.  On Rocq master that leaf
 no longer reaches it, so the two laws went undischarged and a downstream
 bullet script failed several lines later with an unrelated-looking error
 (issue #213, [Instance/Adjoints.v]).  Closing reflexivity and symmetry from
 the relation's own [Equivalence] instance makes the step deterministic and
 independent of any hint search, wide or narrow; the narrow
 [auto with category_laws] fallback is retained for the remaining goals.
 [Test/Issue213.v] holds it to that. 

 --------
 [equivalence]：通过分裂为三条律（[constructor]）并用 [cat]/[intuition] 消解每一条，证明 [Equivalence] 目标。

 显式的自反/对称遍并非装饰而是承重的。当关系由其他等价拼装——例如一对自然同构——时，仅当策略经宽 [auto] 到达标准库 [crelations] 库中无模式的 [Hint Extern] [solve_crelation] 才能关闭这两律。本策略曾以 [auto with *] 结尾从而到达它；后来为卫生收窄为 [auto with category_laws]，证明仍能构建只因上面的 [intuition] 步骤自带仍能到达该提示的宽 [auto with *] 叶。在 Rocq master 上该叶不再到达，故两律未消解，下游 bullet 脚本数行后以看似无关的错误失败（issue #213，[Instance/Adjoints.v]）。从关系自身的 [Equivalence] 实例关闭自反与对称，使该步确定且独立于任何提示搜索（宽或窄）；窄的 [auto with category_laws] 回退仍保留给其余目标。[Test/Issue213.v] 对此加以钉死。
*)
Ltac equivalence := constructor; repeat intro; simpl; try cat; intuition;
  try solve [ reflexivity | (symmetry; eassumption) ];
  auto with category_laws.
(*
 [proper]: prove a [Proper]/respectful goal -- introduce the related
 arguments, then close with [cat]/[intuition]. 

 --------
 [proper]：证明 [Proper]/respectful 目标——引入相关自变量，再用 [cat]/[intuition] 关闭。
*)
Ltac proper := repeat intro; simpl; try cat; intuition.
(*
 [sapply]/[srewrite]/[srewrite_r]: "setoid" variants that first materialize
 [F] as a hypothesis and [cbn]-normalize it (so projections of records unfold)
 before applying / rewriting left-to-right / rewriting right-to-left. 

 --------
 [sapply]/[srewrite]/[srewrite_r]：“setoid”变体，先把 [F] 物化为假设并 [cbn] 规范化（使记录投影展开），再应用 / 左到右改写 / 右到左改写。
*)
Ltac sapply F :=
  let H := fresh "H" in pose proof F as H; cbn in H; apply H; clear H.
Ltac srewrite F :=
  let H := fresh "H" in pose proof F as H; cbn in H; rewrite H; clear H.
Ltac srewrite_r F :=
  let H := fresh "H" in pose proof F as H; cbn in H; rewrite <- H; clear H.

(*
 [cat_simpl]: the global [Program] obligation tactic (installed below).  Run
 [Program]'s own simplifier, then try to fully solve the goal by repeatedly
 dispatching Equivalence/Proper/respectful sub-obligations and finishing with
 [simplify]+[cat]; if that [solve] fails, leave a [simpl]-reduced goal for the
 caller. 

 --------
 [cat_simpl]：全局 [Program] 义务策略（下方安装）。运行 [Program] 自带化简器，再尝试通过反复消解 Equivalence/Proper/respectful 子义务并以 [simplify]+[cat] 收尾来完全解决目标；若该 [solve] 失败，留给调用方一个 [simpl]-化简后的目标。
*)
Ltac cat_simpl :=
  program_simpl; autounfold;
  try solve [
    repeat match goal with
    | [ |- Equivalence _ ] => equivalence
    | [ |- Proper _ _ ] => proper
    | [ |- respectful _ _ _ _ ] => proper
    end;
    program_simpl; autounfold in *;
    simpl in *; intros; simplify;
    simpl in *; cat];
  simpl in *.

#[global] Obligation Tactic := cat_simpl.

(*
 [construct]: start building a record/structure goal, deferring side
 conditions as fresh goals ([unshelve econstructor]) and introducing the
 fields' arguments. 

 --------
 [construct]：开始构建记录/结构目标，把副作用条件推迟为新目标（[unshelve econstructor]）并引入字段的自变量。
*)
Ltac construct := unshelve econstructor; simpl; intros.

(*
 [inv H]: invert [H], substitute the resulting equalities, and discard the
 now-redundant hypothesis when possible. 

 --------
 [inv H]：反演 [H]，代入所得相等，并在可能时丢弃现已多余的假设。
*)
Ltac inv H := inversion H; subst; try clear H.

(*
 [spose H as X]: introduce the (untyped) term [H] as hypothesis [X] and
 [simpl]-reduce it -- a terse [pose proof ... as ...] for setoid lemmas. 

 --------
 [spose H as X]：把（未加类型的）项 [H] 引入为假设 [X] 并 [simpl]-化简——面向 setoid 引理的简短 [pose proof ... as ...]。
*)
Tactic Notation "spose" uconstr(H) "as" ident(X) :=
  pose proof H as X; simpl in X.
