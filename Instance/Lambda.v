Require Import Category.Instance.Lambda.Ty.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Ren.
Require Import Category.Instance.Lambda.Sem.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Coq.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

(** The syntactic cartesian closed category of the simply-typed lambda calculus. / 简单类型 λ 演算的句法笛卡尔闭范畴。 *)

(*
 nLab: https://ncatlab.org/nlab/show/relation+between+type+theory+and+category+theory
 nLab: https://ncatlab.org/nlab/show/cartesian+closed+category
 Wikipedia: https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence
 Wikipedia: https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus

 This file is the top of the simply-typed lambda calculus (STLC) development
 in Instance/Lambda/ (syntax in Ty.v/Exp.v, de Bruijn renaming/weakening in
 Ren.v, the standard-model interpretation into Coq in Sem.v).  It packages
 that syntax as a category and exhibits its cartesian closed structure, the
 categorical half of the Curry-Howard-Lambek correspondence: STLC is the
 internal language of cartesian closed categories (Lambek & Scott).

 Fixing a typing context `Γ`, the category [Lambda Γ] has

 - objects        types `τ : Ty`,
 - morphisms      `a ~> b  :=  Exp Γ (a ⟶ b)`, i.e. open terms of function
 type in context `Γ`,
 - identity       `LAM (VAR ZV)`              (the term `λx. x`),
 - composition    `LAM (APP (wk f) (APP (wk g) (VAR ZV)))`   (`λx. f (g x)`).

 Morphism equivalence is *semantic*, not syntactic: `f ≈ g` holds when the
 interpretations `SemExp f` and `SemExp g` agree on every environment (see
 [Exp_Setoid]).  This is the denotational, not the β/η-quotient, equality;
 the laws below are therefore discharged by `SemExp_*` rewriting rather than
 by reasoning about reductions.  The cartesian closed structure is then read
 off the term language: `TyUnit` is terminal, `TyPair` gives products with
 the `Pair`/`Fst`/`Snd` introduction and projections, and `TyArrow` gives
 exponentials with the usual [curry]/[uncurry] adjunction.

 Note: `A` and `L : HostExprsSem A` below are vestigial context.  No class
 named `HostExprsSem` is in scope, so `Generalizable All Variables` quietly
 treats it as a free variable to be generalized; since nothing in this file
 depends on `A` or `L`, both are dropped and [Lambda] reduces to `Env →
 Category` (confirmed by `About Lambda`).  They are kept here as a record of
 the intended host-language extension point used in the sibling files. 

 --------
 nLab：https://ncatlab.org/nlab/show/relation+between+type+theory+and+category+theory
 nLab：https://ncatlab.org/nlab/show/cartesian+closed+category
 Wikipedia：https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence
 Wikipedia：https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus

 此文件是简单类型λ演算（STLC）在 Instance/Lambda/ 中的开发顶部（Ty.v/Exp.v 中的语法，Ren.v 中的 de Bruijn 重命名/弱化，在 Sem.v 中进入 Coq 的标准模型解释）。它将该语法封装为一个范畴，并展示其笛卡尔闭合结构，即 Curry-Howard-Lambek 对应的范畴部分：STLC 是笛卡尔闭合范畴的内部语言（Lambek & Scott）。

 固定一个类型上下文 `Γ`，范畴 [Lambda Γ] 具有- 对象        类型  `τ : Ty` ,
 - 态射        `a ~> b  :=  Exp Γ (a ⟶ b)` ，即在上下文  `Γ` 中的函数类型开放项，
 - 恒等        `LAM (VAR ZV)`               （项  `λx. x` ），
 - 复合        `LAM (APP (wk f) (APP (wk g) (VAR ZV)))`    （ `λx. f (g x)` ）。态射等价是*语义*上的，而不是句法上的：当解释 `SemExp f` 和 `SemExp g` 在每个环境中都一致时，`f ≈ g` 成立（见 [Exp_Setoid]）。这是指称上的，而不是 β/η-商的相等；因此，下面的定律是通过 `SemExp_*` 重写来解决的，而不是通过关于约简的推理。然后从项语言中读出笛卡尔闭结构：`TyUnit` 是终结对象，`TyPair` 提供带有 `Pair` / `Fst` / `Snd` 引入和投影的积，`TyArrow` 提供指数，并带有通常的 [curry] / [uncurry] 对偶性。注意：下面的 `A` 和 `L : HostExprsSem A` 是残留的上下文。没有名为 `HostExprsSem` 的类在作用域中，因此 `Generalizable All Variables` 会静默地将其视为要泛化的自由变量；由于此文件中没有任何内容依赖 `A` 或 `L`，因此两者都被删除，[Lambda] 简化为 `Env → Category ` (confirmed by ` About Lambda`。它们在这里保留，作为在相关文件中使用的预期主机语言扩展点的记录。
*)

(*
 The Curry-Howard-Lambek correspondence, and what it is for

 nLab:
 https://ncatlab.org/nlab/show/relation+between+type+theory+and+category+theory

 The correspondence realized here was assembled in three stages.  Church
 introduced the simply typed calculus to avoid the paradoxical use of
 the untyped theory (Church, “A formulation of the simple theory of
 types”, Journal of Symbolic Logic 1940).  Curry had observed in 1934
 that the types of the combinators read as axiom schemes of
 intuitionistic implicational logic (Curry and Feys, “Combinatory
 Logic”, 1958), and Howard's 1969 manuscript, published as “The
 formulae-as-types notion of construction” (Academic Press 1980), made
 the proofs-as-terms analogy explicit.  Lambek supplied the third
 vertex: intuitionistic proofs, typed terms, and the morphisms of a
 cartesian closed category share one equational theory, whence the name
 Curry-Howard-Lambek.  The definitive syntactic statement appears in
 the same Curry Festschrift as Howard's paper — lambda theories
 correspond to cartesian closed categories exactly as algebraic
 theories correspond to Lawvere's finite-product categories (Lambek,
 “From lambda calculus to cartesian closed categories”, Academic Press
 1980) — and the book form is Part I of Lambek and Scott, “Introduction
 to Higher Order Categorical Logic” (Cambridge University Press 1986).
 The earlier “Deductive Systems and Categories” chapter of that history
 is told in Structure/Closed.v, whose header names this file as the
 syntactic realization.

 Within the library the theorem is witnessed from both sides.  This
 file is the syntax-to-category direction: the closed structure is read
 off the type formers, so that [fork], [exl], [exr], [curry] and
 [uncurry] below are categorical combinators written as de Bruijn
 terms.  Instance/Coq.v supplies a semantic cartesian closed category,
 and the standard model of Instance/Lambda/Sem.v is the interpretation
 from the one to the other.  One consequence of the semantic equality
 of [Exp_Setoid] deserves emphasis: with [TyUnit] the only base type,
 the standard model identifies more terms than βη-conversion does.  It
 follows that [Lambda Γ] is the image of the syntactic category inside
 the standard model, not the free cartesian closed category of Lambek's
 theorem on the nose.

 The representation has its own ancestry.  Rather than pair a raw term
 with a separate typing derivation, the encoding makes an [Exp] its own
 derivation — the intrinsically-typed representation of Altenkirch and
 Reus (“Monadic Presentations of Lambda Terms Using Generalized
 Inductive Types”, CSL 1999).  Its Coq discipline — terms indexed by
 context and type, substitution bootstrapped from renaming,
 coercion-free at simple types — is that of Benton, Hur, Kennedy and
 McBride (“Strongly Typed Term Representations in Coq”, Journal of
 Automated Reasoning 2012), and the Ren.v-before-Sub.v layering of the
 sibling files repeats it exactly.

 The correspondence is executable, and the applications exploit that.
 The Categorical Abstract Machine compiles ML-family languages by
 translating lambda terms into exactly such combinators — the
 operations of a cartesian closed category as machine instructions —
 and gave CAML its name (Cousineau, Curien and Mauny, “The categorical
 abstract machine”, Science of Computer Programming 1987).  Elliott
 runs the same idea inside GHC: because the simply typed calculus is
 modeled by any cartesian closed category, one program text can be
 reinterpreted in alternative such categories — hardware circuits,
 automatic differentiation, interval analysis (Elliott, “Compiling to
 categories”, ICFP 2017).  Downstream, the sibling files make the
 operational reading concrete: call-by-value small-step reduction
 (Instance/Lambda/Step.v) is sound for this semantics
 (Instance/Lambda/Sound.v); β-reduction is strongly normalizing, by the
 computability method of Tait (“Intensional interpretations of
 functionals of finite type I”, Journal of Symbolic Logic 1967)
 implemented in Instance/Lambda/Norm.v; and a CEK machine executes
 closed terms with runs checked by `eq_refl` (Instance/Lambda/Eval.v,
 Instance/Lambda/Example.v).  End to end, the development proves that
 well-typed syntax forms a cartesian closed category, that the standard
 model interprets it, that evaluation is sound for that model, and that
 every closed term halts. 

 --------
 柯里-霍华德-兰贝克对应，以及它的用途

 nLab:
 https://ncatlab.org/nlab/show/relation+between+type+theory+and+category+theory这里实现的对应关系分三个阶段组装完成。丘奇引入了简单类型演算，以避免未类型理论的悖论性使用（Church，《简单类型理论的一个表述》，《符号逻辑杂志》，1940年）。柯里在1934年观察到，组合子类型可以被解读为直觉逻辑蕴涵的公理模式（Curry 和 Feys，《组合逻辑》，1958年），而霍华德1969年的手稿，后来以《公式即类型的构造概念》（Academic Press，1980年）出版，将证明与项的类比明确化。Lambek 提供了第三个顶点：直觉主义证明、有类型的项以及笛卡尔闭范畴的态射共享相同的方程理论，因此得名 Curry-Howard-Lambek。明确的句法陈述出现在与霍华德论文相同的库里纪念文集中——lambda理论恰好对应于笛卡尔闭类范畴，就像代数理论对应于劳维尔的有限积范畴一样（Lambek，《从lambda演算到笛卡尔闭类范畴》，Academic Press 1980）——而书籍形式则是Lambek和Scott的第一部分，《高阶范畴逻辑导论》（剑桥大学出版社 1986）。这一历史的早期章节“演绎系统与范畴”记载在Structure/Closed.v中，其头部将该文件命名为句法实现。在图书馆中，该定理从两个方面得到了验证。这个文件是从语法到范畴的方向：闭结构是从类型生成器读取的，因此下面的  [fork]、[exl]、[exr]、[curry] 和 [uncurry] 是以 de Bruijn 项形式写出的范畴组合子。Instance/Coq.v 提供了一个语义笛卡尔闭范畴，而 Instance/Lambda/Sem.v 的标准模型是从一个到另一个的解释。[Exp_Setoid] 的语义等价性有一个后果值得强调：当 [TyUnit] 是唯一的基本类型时，标准模型所识别的项比 βη-转换识别的项还多。因此，[Lambda Γ] 是标准模型内语法范畴的映射，而不是 Lambek 定理上自由笛卡尔闭范畴的原样。该表示法有其自身的来源。与其将一个原始项与单独的类型推导配对，不如让编码使 [Exp] 自身成为一种推导——Altenkirch 和 Reus 的内在类型表示（“使用广义归纳类型的 Lambda 项的单子表示”, CSL 1999）。其 Coq 规范——按上下文和类型索引的项，从重命名引导的替换，在简单类型下无强制类型转换——是 Benton、Hur、Kennedy 和 McBride 的工作（“Coq 中的强类型项表示”, 自动推理杂志 2012），而兄弟文件的 Ren.v-before-Sub.v 分层完全重复了它。这种对应是可执行的，并且应用程序利用了这一点。范畴抽象机通过将 lambda 项翻译为正是这种组合子——作为机器指令的笛卡尔闭范畴的操作——来编译 ML 系列语言，并且因此给 CAML 命名（Cousineau、Curien 和 Mauny，《范畴抽象机》，计算机程序科学，1987 年）。Elliott 在 GHC 内部运行了同样的理念：因为简单类型演算可以由任何笛卡尔闭范畴建模，所以同一段程序文本可以在替代的此类范畴中重新解释——硬件电路、自动微分、区间分析（Elliott，《编译到范畴》，ICFP 2017 年）。在下游，相关的文件使操作性的阅读变得具体：按值调用的小步规约（Instance/Lambda/Step.v）对于该语义是可靠的（Instance/Lambda/Sound.v）；通过 Tait 的可计算性方法（“有限类型函数的内在解释 I”，《符号逻辑杂志》1967）实现的 β-规约是强归约的（Instance/Lambda/Norm.v）；并且 CEK 机执行闭合项，其运行由 `eq_refl` 检查（Instance/Lambda/Eval.v, Instance/Lambda/Example.v）。从头到尾，该开发证明了：良类型语法形式构成了一个笛卡尔闭范畴，标准模型对其进行了诠释，评估对于该模型是可靠的，并且每个闭合项都能终止。
*)

Section Lambda.

Context {A : Type}.
Context `{L : HostExprsSem A}.

Definition identity Γ τ : Exp Γ (τ ⟶ τ) := LAM (VAR ZV).

Definition composition {Γ τ τ' τ''}
           (f : Exp Γ (τ' ⟶ τ''))
           (g : Exp Γ (τ ⟶ τ')) : Exp Γ (τ ⟶ τ'') :=
  LAM (APP (wk f) (APP (wk g) (VAR ZV))).

#[export]
Program Instance TyArrow_Setoid {dom cod} : Setoid (SemTy (dom ⟶ cod)) := {
  equiv := λ f g, f ≈[Coq] g
}.
Next Obligation.
  equivalence.
  now rewrite H, H0.
Qed.

#[export]
Program Instance Exp_Setoid {Γ dom cod} : Setoid (Exp Γ (dom ⟶ cod)) := {
  equiv := λ f g, ∀ E, SemExp f E ≈ SemExp g E
}.
Next Obligation.
  equivalence.
  now rewrite H, H0.
Qed.

Lemma SemExp_identity {Γ τ} (E : SemEnv Γ) :
  SemExp (identity Γ τ) E ≈ id.
Proof. now f_equal. Qed.

Lemma SemExp_composition `(E : SemEnv Γ) {τ τ' τ''}
      (f : Exp Γ (τ' ⟶ τ'')) (g : Exp Γ (τ ⟶ τ')) :
  SemExp (composition f g) E ≈ SemExp f E ∘ SemExp g E.
Proof.
  intro.
  unfold composition; simpl.
  now rewrite !SemExp_wk.
Qed.

#[export]
Program Instance composition_respects {Γ τ τ' τ''} :
  Proper (equiv ==> equiv ==> equiv) (@composition Γ τ τ' τ'').
Next Obligation.
  unfold composition; simpl.
  rewrite !SemExp_wk.
  now rewrite H, H0.
Qed.

Lemma composition_identity_right {Γ τ τ'}
      (f : Exp Γ (τ ⟶ τ')) :
  composition f (identity Γ τ) ≈ f.
Proof.
  intro.
  now rewrite SemExp_composition.
Qed.

Lemma composition_identity_left {Γ τ τ'}
      (f : Exp Γ (τ ⟶ τ')) :
  composition (identity Γ τ') f ≈ f.
Proof.
  intro.
  now rewrite SemExp_composition.
Qed.

Lemma composition_assoc {Γ τ τ' τ'' τ'''}
      (f : Exp Γ (τ'' ⟶ τ'''))
      (g : Exp Γ (τ' ⟶ τ''))
      (h : Exp Γ (τ ⟶ τ')) :
  composition f (composition g h) ≈
  composition (composition f g) h.
Proof.
  intro.
  rewrite !SemExp_composition.
  now rewrite compose_assoc.
Qed.

Lemma composition_assoc_sym {Γ τ τ' τ'' τ'''}
      (f : Exp Γ (τ'' ⟶ τ'''))
      (g : Exp Γ (τ' ⟶ τ''))
      (h : Exp Γ (τ ⟶ τ')) :
  composition (composition f g) h ≈
  composition f (composition g h).
Proof.
  intro.
  rewrite !SemExp_composition.
  now rewrite compose_assoc.
Qed.

#[local] Obligation Tactic := intros.

Program Definition Lambda Γ : Category := {|
  obj     := Ty;
  hom     := λ A B : Ty, Exp Γ (A ⟶ B);
  homset  := @Exp_Setoid Γ;
  id      := @identity Γ;
  compose := @composition Γ;

  compose_respects := @composition_respects Γ;

  id_left := @composition_identity_left Γ;
  id_right := @composition_identity_right Γ;
  comp_assoc := @composition_assoc Γ;
  comp_assoc_sym := @composition_assoc_sym Γ;
|}.

#[export]
Program Instance Lambda_Terminal Γ : @Terminal (Lambda Γ) := {
  terminal_obj := TyUnit;            (* the unit type is the terminal object / 单位类型是终端对象 *)
  one := λ _, LAM EUnit              (* the unique map `λ_. ()` into it / 将独特的地图 `λ_. ()` 放入其中 *)
}.
Next Obligation.
  repeat intro.
  now destruct (SemExp f E x0), (SemExp g E x0).
Qed.

#[export]
Program Instance Lambda_Cartesian Γ : @Cartesian (Lambda Γ) := {
  product_obj := TyPair;             (* the pair type is the categorical product / 这一对类型是范畴积 *)
  fork := λ _ _ _ f g,               (* `⟨f, g⟩ := λx. (f x, g x)` *)
    LAM (Pair (APP (wk f) (VAR ZV)) (APP (wk g) (VAR ZV)));
  exl  := λ _ _, LAM (Fst (VAR ZV)); (* first projection `λp. fst p` / 第一次投影 `λp. fst p` *)
  exr  := λ _ _, LAM (Snd (VAR ZV)); (* second projection `λp. snd p` / 第二次投影 `λp. snd p` *)
}.
Next Obligation.
  proper.
  rewrite !SemExp_wk.
  now rewrite X, X0.
Qed.
Next Obligation.
  split; repeat intro; simpl.
  - split; intros; rewrite !SemExp_wk.
    + rewrite X; simpl.
      rewrite !SemExp_wk.
      now simp RenVar.
    + rewrite X; simpl.
      rewrite !SemExp_wk.
      now simp RenVar.
  - destruct X.
    rewrite !SemExp_wk.
    rewrite <- e, <- e0.
    simp Keep; simpl.
    rewrite !SemExp_wk.
    simp RenVar; simpl.
    apply surjective_pairing.
Qed.

Definition curry {Γ a b c} (f : Exp Γ (a × b ⟶ c)) : Exp Γ (a ⟶ b ⟶ c) :=
  LAM (LAM (APP (wk (wk f)) (Pair (VAR (SV ZV)) (VAR ZV)))).

Definition uncurry {Γ a b c} (f : Exp Γ (a ⟶ b ⟶ c)) : Exp Γ (a × b ⟶ c) :=
  LAM (APP (APP (wk f) (Fst (VAR ZV))) (Snd (VAR ZV))).

#[local] Obligation Tactic := program_simpl.

#[export]
Program Instance Lambda_Closed Γ : @Closed (Lambda Γ) _ := {
  exponent_obj := TyArrow;           (* the function type is the exponential object / 函数类型是指数对象 *)
  exp_iso := λ _ _ _,                (* the natural iso `Hom(a×b,c) ≅ Hom(a,b⟶c)` / 天然同位素 `Hom(a×b,c) ≅ Hom(a,b⟶c)` *)
    {| to   := {| morphism := curry |}
     ; from := {| morphism := uncurry |} |}
}.
Next Obligation.
  proper.
  extensionality z.
  unfold wk at 1.
  unfold wk at 2.
  rewrite <- !SemExp_RenSem.
  repeat setoid_rewrite RenSem_skip1; simpl.
  rewrite !SemExp_wk.
  eauto.
Qed.
Next Obligation.
  proper.
  rewrite !SemExp_wk; simpl.
  congruence.
Qed.
Next Obligation.
  extensionality z.
  rewrite <- !SemExp_RenSem.
  simp RenSem.
  simp RenVar.
  simpl.
  rewrite SemExp_wk.
  now repeat setoid_rewrite RenSem_skip1; simpl.
Qed.
Next Obligation.
  rewrite <- !SemExp_RenSem.
  simp RenSem.
  simp RenVar.
  simpl.
  repeat setoid_rewrite RenSem_skip1; simpl.
  unfold wk at 1.
  rewrite <- !SemExp_RenSem.
  repeat setoid_rewrite RenSem_skip1; simpl.
  now rewrite SemExp_wk.
Qed.
Next Obligation.
  simp RenVar; simpl.
  rewrite <- !SemExp_RenSem.
  simp RenSem.
  unfold wk at 1.
  rewrite <- !SemExp_RenSem.
  repeat setoid_rewrite RenSem_skip1; simpl.
  now rewrite SemExp_wk.
Qed.

End Lambda.
