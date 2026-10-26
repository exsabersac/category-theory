Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Instance.Lambda.Ltac.
Require Import Category.Instance.Lambda.Ty.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Value.
Require Import Category.Instance.Lambda.Sub.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Set Transparent Obligations.

(** Reduction by decomposition into an evaluation context and a redex. / 通过分解为评估上下文和可约表达式进行规约。 *)

(*
 This module gives a Felleisen-Hieb-style, context-based presentation of the
 small-step reduction relation for the de Bruijn STLC (see [Exp]).  Instead
 of one congruence rule per elimination form (as in [Step]), reduction is
 factored into three reusable pieces:

 - a [Redex] is a contraction at the root: beta ([R_Beta]) and the two
 projection rules ([R_Fst], [R_Snd]);
 - a [Ctxt] is an evaluation context, i.e. a typed term with a single hole,
 built as a snoc-list of single-constructor [Frame]s;
 - [Plug e C e'] witnesses that filling the hole of [C] with [e] yields the
 whole term [e'] (the recomposition operation written E[e] on paper).

 A single rule then closes contraction under arbitrary evaluation contexts:

 [Step]:   Plug e1 C e1'  →  Plug e2 C e2'  →  Redex e1 e2  →  e1' ---> e2'

 so e1' ---> e2' iff e1' decomposes as C[e1], e1 contracts to e2, and e2'
 recomposes as C[e2].  This is the standard contextual/reduction-semantics
 schema: decompose into context-plus-redex, contract, plug back.

 Note that, despite living next to a general beta-reduction story, the
 relation here is call-by-value, not full beta-reduction: the redexes
 [R_Fst]/[R_Snd] require both projection components to be values
 ([ValueP]), and the [Plug] constructors that descend into a second
 subterm ([Plug_PairR], [Plug_AppR]) require the first to already be a
 value, fixing a left-to-right evaluation order.  Reduction therefore never
 proceeds under a [LAM], and the contexts decompose exactly the redex that
 [Step] (the congruence-rule presentation) would also reduce.

 The accompanying lemmas establish that this presentation is well behaved:
 [strong_progress] (a closed term is a value or steps), [Plug_functional]
 and [Plug_injective] (plugging is single-valued in either argument),
 [Redex_deterministic] (contraction is a function), and the congruence
 lemmas [AppL_LAM]/[AppR_LAM].  The [Frame]/[Ctxt] and [Plug] layers are
 moreover shown to be categorical: [Ctxt_id]/[Ctxt_comp] satisfy the
 identity and associativity laws ([Ctxt_id_left], [Ctxt_id_right],
 [Ctxt_comp_assoc]).

 References:
 beta-reduction      https://ncatlab.org/nlab/show/beta-reduction
 lambda-calculus     https://ncatlab.org/nlab/show/lambda-calculus
 evaluation contexts / reduction semantics:
 M. Felleisen and R. Hieb, “The revised report on the syntactic
 theories of sequential control and state”, TCS 103(2), 1992. 

 --------
 该模块提供了对 de Bruijn STLC 的小步归约关系的 Felleisen-Hieb 风格、基于上下文的呈现（参见 [Exp]）。与每个消除形式使用一个合取规则（如 [Step]）不同，归约被分解为三个可重用的部分：

 - [Redex] 是在根处的缩减：β（[R_Beta]）以及两个投影规则（[R_Fst], [R_Snd]）；
 - [Ctxt] 是一个求值上下文，即一个带有单个空洞的类型化项，由单构造函数的 [Frame] 构成的 snoc 列表构建而成；
 - [Plug e C e'] 证明将 [C] 的空洞填充为 [e] 会得到整个项 [e']（在论文中写作重组操作 E [e]）。

 然后，一个规则就可以在任意求值上下文下关闭缩减：[Step]：Plug e1 C e1' → Plug e2 C e2' → Redex e1 e2 → e1' ---> e2'

 因此 e1' ---> e2' 当且仅当 e1' 分解为 C [e1]，e1 收缩为 e2，并且 e2' 重新组合为 C [e2]。这是标准的上下文/归约语义模式：分解为上下文加可约式，收缩，然后重新插回。请注意，尽管生活在一般的 beta 简化故事旁边，这里的关系是按值调用，而不是完整的 beta 简化：红ex [R_Fst] / [R_Snd] 需要两个投影组件都是值 ([ValueP])，并且下探到第二个子项的 [Plug] 构造器 ([Plug_PairR], [Plug_AppR]) 要求第一个已经是值，从而固定了从左到右的求值顺序。因此，简化过程永远不会在 [LAM] 下进行，并且上下文正好分解 [Step]（并合规则表示法）也会简化的红ex。随附的引理证明了这个表示是良好处理的：
 [strong_progress] （一个封闭项是一个值或者可以进行步骤），[Plug_functional] 
 和 [Plug_injective] （在任意一个参数中插入是单值的），
 [Redex_deterministic] （收缩是一个函数），以及同余引理
 [AppL_LAM] / [AppR_LAM] 。此外，[Frame] / [Ctxt] 和 [Plug] 层被证明是范畴性的：
 [Ctxt_id] / [Ctxt_comp] 满足单位元和结合律（[Ctxt_id_left], [Ctxt_id_right], [Ctxt_comp_assoc]）。

 参考文献：
 beta-归约       https://ncatlab.org/nlab/show/beta-reduction 
 lambda-演算     https://ncatlab.org/nlab/show/lambda-calculus 
 评估上下文 / 归约语义：
 M. Felleisen 和 R. Hieb, “关于顺序控制和状态的句法理论修订报告”, TCS 103(2), 1992。
*)

Section Full.

Import ListNotations.

Open Scope Ty_scope.

(*
 A [Frame] is an evaluation context with a single hole one constructor deep:
 [Frame Γ τ' τ] has a hole of type [τ'] and, once filled, yields a term of
 type [τ].  Frames are the building blocks snoc-listed together into [Ctxt]. 

 --------
 [Frame] 是一个具有单个空位的评估上下文，构造器深度为一：
 [Frame Γ τ' τ] 具有类型为 [τ'] 的空位，一旦填充，产生类型为 [τ] 的项。帧是构建块，按 snoc 列表方式组合成 [Ctxt]。
*)
Inductive Frame Γ : Ty → Ty → Set :=
  | F_PairL {τ1 τ2}  : Exp Γ τ2 → Frame τ1 (τ1 × τ2)
  | F_PairR {τ1 τ2}  : Exp Γ τ1 → Frame τ2 (τ1 × τ2)
  | F_Fst {τ1 τ2}    : Frame (τ1 × τ2) τ1
  | F_Snd {τ1 τ2}    : Frame (τ1 × τ2) τ2
  | F_AppL {dom cod} : Exp Γ dom → Frame (dom ⟶ cod) cod
  | F_AppR {dom cod} : Exp Γ (dom ⟶ cod) → Frame dom cod.

Derive Signature NoConfusion Subterm for Frame.

Inductive Ctxt Γ : Ty → Ty → Set :=
  | C_Nil {τ}         : Ctxt τ τ
  | C_Cons {τ τ' τ''} : Frame Γ τ' τ → Ctxt τ'' τ' → Ctxt τ'' τ.

Derive Signature NoConfusion NoConfusionHom Subterm for Ctxt.

(* [Ctxt] forms a category with objects = types and morphisms = contexts. / [Ctxt] 形成了一个范畴，其对象 = 类型，态射 = 上下文。 *)

Definition Ctxt_id {Γ τ} : Ctxt Γ τ τ := C_Nil _.
Arguments Ctxt_id {_ _} /.

Program Fixpoint Ctxt_comp {Γ τ τ' τ''}
        (C : Ctxt Γ τ' τ) (C' : Ctxt Γ τ'' τ') : Ctxt Γ τ'' τ :=
  match C with
  | C_Nil _      => C'
  | C_Cons _ f c => C_Cons _ f (Ctxt_comp c C')
  end.

Theorem Ctxt_id_left {Γ τ τ'} {C : Ctxt Γ τ' τ} :
  Ctxt_comp Ctxt_id C = C.
Proof. induction C; simpl; auto; now f_equal. Qed.

Theorem Ctxt_id_right {Γ τ τ'} {C : Ctxt Γ τ' τ} :
  Ctxt_comp C Ctxt_id = C.
Proof. induction C; simpl; auto; now f_equal. Qed.

Theorem Ctxt_comp_assoc {Γ τ τ' τ'' τ'''}
        {C : Ctxt Γ τ' τ} {C' : Ctxt Γ τ'' τ'} {C'' : Ctxt Γ τ''' τ''} :
  Ctxt_comp C (Ctxt_comp C' C'') = Ctxt_comp (Ctxt_comp C C') C''.
Proof. induction C; simpl; auto; now f_equal. Qed.

(*
 [Redex e1 e2] is a root contraction: the three primitive reduction rules,
 each contracting an elimination of a value to its component.  These are the
 only redexes; congruence is handled separately by [Plug]/[Step]. 

 --------
 [Redex e1 e2] 是一种根收缩：三个原始简化规则，每个都将一个值的消除收缩为其组件。这些是唯一的可缩表达式；一致性由 [Plug] / [Step] 单独处理。
*)
Inductive Redex {Γ} : ∀ {τ}, Exp Γ τ → Exp Γ τ → Set :=
  | R_Beta {dom cod} (e : Exp (dom :: Γ) cod) v :
    ValueP v →
    Redex (APP (LAM e) v) (SubExp {|| v ||} e)
  | R_Fst {τ1 τ2} (x : Exp Γ τ1) (y : Exp Γ τ2) :
    ValueP x →
    ValueP y →
    Redex (Fst (Pair x y)) x
  | R_Snd {τ1 τ2} (x : Exp Γ τ1) (y : Exp Γ τ2) :
    ValueP x →
    ValueP y →
    Redex (Snd (Pair x y)) y.

Derive Signature for Redex.

Unset Elimination Schemes.

(*
 [Plug e C e'] is the recomposition relation: filling the hole of context [C]
 with [e] reconstructs the whole term [e'] (written E[e] on paper).  Each
 constructor mirrors one [Frame], and the value side-conditions on
 [Plug_PairR]/[Plug_AppR] enforce left-to-right (call-by-value) evaluation. 

 --------
 [Plug e C e'] 是重组关系：用 [e] 填充上下文 [C] 的空洞可以重建整个项 [e']（在纸上写作 E [e]）。每个构造函数对应一个 [Frame]，并且 [Plug_PairR] / [Plug_AppR] 上的值侧条件强制从左到右（按值调用）求值。
*)
Inductive Plug {Γ τ'} (e : Exp Γ τ') : ∀ {τ}, Ctxt Γ τ' τ → Exp Γ τ → Set :=
  | Plug_Hole : Plug (C_Nil _) e

  | Plug_PairL {τ1 τ2} {C : Ctxt Γ τ' τ1} {e' : Exp Γ τ1} {e2 : Exp Γ τ2} :
    Plug C e' →
    Plug (C_Cons _ (F_PairL _ e2) C) (Pair e' e2)

  | Plug_PairR {τ1 τ2} {C : Ctxt Γ τ' τ2} {e1 : Exp Γ τ1} {e' : Exp Γ τ2} :
    ValueP e1 →
    Plug C e' →
    Plug (C_Cons _ (F_PairR _ e1) C) (Pair e1 e')

  | Plug_Fst {τ1 τ2} {C : Ctxt Γ τ' (τ1 × τ2)} {e' : Exp Γ (τ1 × τ2)} :
    Plug C e' →
    Plug (C_Cons _ (F_Fst _) C) (Fst e')

  | Plug_Snd {τ1 τ2} {C : Ctxt Γ τ' (τ1 × τ2)} {e' : Exp Γ (τ1 × τ2)} :
    Plug C e' →
    Plug (C_Cons _ (F_Snd _) C) (Snd e')

  | Plug_AppL {dom cod} {C : Ctxt Γ τ' (dom ⟶ cod)}
              {e' : Exp Γ (dom ⟶ cod)} {e2 : Exp Γ dom} :
    Plug C e' →
    Plug (C_Cons _ (F_AppL _ e2) C) (APP e' e2)

  | Plug_AppR {dom cod} {C : Ctxt Γ τ' dom}
              {e' : Exp Γ dom} {e1 : Exp Γ (dom ⟶ cod)} :
    ValueP e1 →
    Plug C e' →
    Plug (C_Cons _ (F_AppR _ e1) C) (APP e1 e').

Derive Signature for Plug.

Set Elimination Schemes.

Scheme Plug_ind := Induction for Plug Sort Type.

(*
 [Plug] forms a category with objects = expressions and morphisms = plugs
 over existential contexts. 

 --------
 [Plug] 在存在性上下文上形成一个范畴，其对象 = 表达式，态射 = 插头。
*)

Definition Plug_id {Γ τ} {x : Exp Γ τ} : Plug x (C_Nil Γ) x := Plug_Hole _.
Arguments Plug_id {_ _ _} /.

Fixpoint Plug_comp {Γ τ τ' τ''}
         {x : Exp Γ τ''} {y : Exp Γ τ'} {z : Exp Γ τ}
         {C : Ctxt Γ τ' τ} {C' : Ctxt Γ τ'' τ'}
         (P : Plug x C' y) (P' : Plug y C z) :
  Plug x (Ctxt_comp C C') z :=
  match P' with
  | Plug_Hole _       => P
  | Plug_PairL _ p'   => Plug_PairL _ (Plug_comp P p')
  | Plug_PairR _ V p' => Plug_PairR _ V (Plug_comp P p')
  | Plug_Fst _ p'     => Plug_Fst _ (Plug_comp P p')
  | Plug_Snd _ p'     => Plug_Snd _ (Plug_comp P p')
  | Plug_AppL _ p'    => Plug_AppL _ (Plug_comp P p')
  | Plug_AppR _ V p'  => Plug_AppR _ V (Plug_comp P p')
  end.

(*
   ( * This should be provable, but the dependent types get in the way. * )
   Theorem Plug_id_left {Γ τ τ'} {C : Ctxt Γ τ' τ} {x : Exp Γ τ'} {y : Exp Γ τ}
   (P : Plug x C y) :
   Plug_comp Plug_id P ~= P.

   --------
   ( * 这应该是可以证明的，但依赖类型造成了阻碍。 * )
   定理 Plug_id_left {Γ τ τ'} {C : Ctxt Γ τ' τ} {x : Exp Γ τ'} {y : Exp Γ τ}
   (P : Plug x C y) :
   Plug_comp Plug_id P ~= P.
*)

(* One-step reduction: [e1' ---> e2'] when [e1'] decomposes as C[e1], the redex [e1] contracts to [e2], and [e2'] recomposes as C[e2]. This single rule closes [Redex] under every evaluation context. / 一步归约：当 [e1'] 分解为 C [e1] 时，红ex [e1] 收缩为 [e2]，并且 [e2'] 重组成 C [e2]。这个单一规则使 [Redex] 在每个求值上下文中闭合。 *)
Inductive Step {Γ τ} : Exp Γ τ → Exp Γ τ → Set :=
  | StepRule {τ'} {C : Ctxt Γ τ' τ} {e1 e2 : Exp Γ τ'} {e1' e2' : Exp Γ τ} :
    Plug e1 C e1' →
    Plug e2 C e2' →
    Redex e1 e2 →
    Step e1' e2'.

Notation " t '--->' t' " := (Step t t') (at level 40).

Derive Signature for Step.

#[local] Hint Constructors ValueP Plug Redex Step : core.

#[local] Hint Extern 7 (_ ---> _) => repeat econstructor : core.

(* Progress: every closed term is either a value or takes a step. / 进展：每个封闭项要么是值，要么可以进行一步运算。 *)
Theorem strong_progress {τ} (e : Exp [] τ) :
  ValueP e ∨ ∃ e', e ---> e'.
Proof.
  dependent induction e; reduce.
  - now left; constructor.
  - destruct IHe1 as [V1|[e1' H1']];
    destruct IHe2 as [V2|[e2' H2']].
    + now left; constructor.
    + dependent elimination H2'; now eauto 6.
    + dependent elimination H1'; now eauto 6.
    + dependent elimination H1';
      dependent elimination H2'; now eauto 6.
  - destruct IHe as [V|[e' H']].
    + dependent elimination V;  now eauto 6.
    + dependent elimination H'; now eauto 6.
  - destruct IHe as [V|[e' H']].
    + dependent elimination V;  now eauto 6.
    + dependent elimination H'; now eauto 6.
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

(*
 Unique decomposition: any term [e2] splits into at most one
 context-plus-redex pair.  This is the property that would yield determinism
 of [Step] (cf. [Step_deterministic] in the [Step] module).  It is left open
 here: stating equality of the contexts [C ~= C'] and redexes [e1 ~= f1]
 across distinct hole types requires heterogeneous (JMeq) equality, and the
 dependent inversions have not yet been discharged. 

 --------
 唯一分解：任何项 [e2] 最多只能分解为一个上下文-可约式对。这是能够保证 [Step] 决定性的性质（参见 [Step] 模块中的 [Step_deterministic]）。这一点在这里尚未解决：在不同孔类型之间说明上下文 [C ~= C'] 和可约式 [e1 ~= f1] 的相等性需要异质（JMeq）相等，而依赖的逆运算尚未完成。
*)
(*
   Lemma Plug_deterministic {Γ τ} e2 :
   ∀ τ' (C : Ctxt Γ τ' τ) e1 e1',
   Redex e1 e1' → Plug e1 C e2 →
   ∀ τ'' (C' : Ctxt Γ τ'' τ) f1 f1',
   Redex f1 f1' → Plug f1 C' e2 →
   τ' = τ'' ∧ C ~= C' ∧ e1 ~= f1.

   --------
   引理 Plug_deterministic {Γ τ} e2 ：
   ∀ τ' (C : Ctxt Γ τ' τ) e1 e1',
   Redex e1 e1' → Plug e1 C e2 →
   ∀ τ'' (C' : Ctxt Γ τ'' τ) f1 f1',
   Redex f1 f1' → Plug f1 C' e2 →
   τ' = τ'' ∧ C ~= C' ∧ e1 ~= f1.
*)

(*
 Plugging is a function of its filler: a given (context, hole) recomposes to
 at most one whole term. 

 --------
 插入是其填充物的一个功能：给定的（上下文，孔）最多重组成一个完整的项。
*)
Lemma Plug_functional {Γ τ τ'} {C : Ctxt Γ τ' τ} e :
  ∀ e1, Plug e C e1 → ∀ e2, Plug e C e2 → e1 = e2.
Proof.
  intros.
  dependent induction H0.
  - now inv H.
  - dependent destruction H.
    now f_equal; auto.
  - dependent destruction H.
    now f_equal; auto.
  - dependent destruction H.
    now f_equal; auto.
  - dependent destruction H.
    now f_equal; auto.
  - dependent destruction H.
    now f_equal; auto.
  - dependent destruction H.
    now f_equal; auto.
Qed.

(* Plugging is injective in its filler: a whole term determines the hole that a fixed context decomposed it into. / 在其填充物中，插入是单射的：整个项决定了固定上下文将其分解成的空穴。 *)
Lemma Plug_injective {Γ τ τ'} {C : Ctxt Γ τ' τ} e :
  ∀ e1, Plug e1 C e → ∀ e2, Plug e2 C e → e1 = e2.
Proof.
  intros.
  dependent induction H0.
  - now inv H.
  - dependent destruction H.
    now f_equal; auto.
  - dependent destruction H.
    now f_equal; auto.
  - dependent destruction H.
    now f_equal; auto.
  - dependent destruction H.
    now f_equal; auto.
  - dependent destruction H.
    now f_equal; auto.
  - dependent destruction H.
    now f_equal; auto.
Qed.

(* Contraction is deterministic: a redex has a unique contractum. / 简约是确定的：红色表达式有唯一的约简式。 *)
Lemma Redex_deterministic {Γ τ} {e : Exp Γ τ} :
  ∀ e', Redex e e' → ∀ e'', Redex e e'' → e' = e''.
Proof.
  intros.
  dependent induction H0;
  dependent elimination H; eauto.
Qed.

(* Congruence under application: a step of the operator (resp. operand, with the operator already a [LAM]) lifts to a step of the whole [APP]. / 应用下的一致性：算子（或操作数，在算子已经是 [LAM] 的情况下）的一步提升到整个 [APP] 的一步。 *)
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

(* [t] is a normal form for [R] when it has no [R]-successor. / 当 [R] 没有 [R]-后继时，[t] 是 [R] 的一种规范形式。 *)
Definition normal_form `(R : crelation X) (t : X) : Type :=
  ∀ t', ¬ R t t'.

(* [R] is deterministic when every element has at most one [R]-successor. / 当每个元素最多有一个 [R] 后继时，[R] 是确定性的。 *)
Definition deterministic `(R : crelation X) : Type :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2.

(*
 Values are normal forms.  Provable here as in the [Step] module (where it is
 discharged), but left open in this context-based presentation: it needs the
 unique-decomposition reasoning sketched in [Plug_deterministic] above to rule
 out a redex hiding under any evaluation context. 

 --------
 值是标准形式。在这里可以像在 [Step] 模块中一样证明（在那里它被释放），但在这种基于上下文的呈现中保持开放：它需要上文 [Plug_deterministic] 中概述的唯一分解推理，以排除隐藏在任何求值上下文下的可约表达式。
*)
(*
   Lemma value_is_nf {Γ τ} (v : Exp Γ τ) :
   ValueP v → normal_form Step v.

   --------
   引理 value_is_nf {Γ τ} (v : Exp Γ τ) ：
   ValueP v → normal_form Step v。
*)

End Full.

Notation " t '--->' t' " := (Step t t') (at level 40).
