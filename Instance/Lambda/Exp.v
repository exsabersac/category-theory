Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Instance.Lambda.Ty.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Set Transparent Obligations.
Unset Uniform Inductive Parameters.

(** Intrinsically-typed de Bruijn syntax for the simply-typed lambda calculus / 针对简单类型 λ 演算的内在类型 de Bruijn 语法 *)

(*
 This file gives the well-typed term syntax of the STLC as a GADT indexed by
 its typing judgement: an inhabitant of [Exp Γ τ] *is* a derivation of
 Γ ⊢ τ, so only well-typed terms can be written down (ill-typed terms are
 not expressible).  Variables are de Bruijn indices made intrinsically
 well-scoped by the [Var] family, indexing the context Γ (a list of types,
 innermost binding at the head).

 The constructors below are exactly the STLC typing rules, in the usual
 judgement notation Γ ⊢ e : τ (here [Exp Γ τ], with [Γ ∋ τ] for [Var Γ τ]):

 ───────────── (ZV)        Γ ∋ τ   ──────────── (SV)
 τ :: Γ ∋ τ                         τ' :: Γ ∋ τ

 Γ ∋ τ                ───────────── (EUnit)
 ───────── (VAR)          Γ ⊢ TyUnit
 Γ ⊢ τ

 Γ ⊢ τ1   Γ ⊢ τ2          Γ ⊢ τ1 × τ2          Γ ⊢ τ1 × τ2
 ─────────────── (Pair)   ─────────── (Fst)    ─────────── (Snd)
 Γ ⊢ τ1 × τ2              Γ ⊢ τ1               Γ ⊢ τ2

 dom :: Γ ⊢ cod                 Γ ⊢ dom ⟶ cod   Γ ⊢ dom
 ────────────────── (LAM)       ─────────────────────── (APP)
 Γ ⊢ dom ⟶ cod                  Γ ⊢ cod

 simply typed lambda calculus:
 https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus
 de Bruijn indices:  https://ncatlab.org/nlab/show/de+Bruijn+index
 https://en.wikipedia.org/wiki/De_Bruijn_index 

 --------
 该文件以广义代数数据类型（GADT）的形式给出了STLC的类型正确项语法，该类型由其类型判定索引：[Exp Γ τ] 的一个实例 *就是* Γ ⊢ τ 的一个推导，因此只能书写类型正确的项（类型错误的项无法表达）。变量是de Bruijn索引，通过[Var]家族内在地保证了作用域正确，索引上下文Γ（类型列表，最内层绑定在列表头部）。

 下面的构造子正是STLC的类型规则，以常用的判定符号Γ ⊢ e : τ表示（这里是[Exp Γ τ]，[Γ ∋ τ]表示[Var Γ τ]）：

 ───────────── (ZV)        Γ ∋ τ   ──────────── (SV)
 τ :: Γ ∋ τ                         τ' :: Γ ∋ τ

 Γ ∋ τ                ───────────── (EUnit)
 ───────── (VAR)          Γ ⊢ TyUnit
 Γ ⊢ τΓ ⊢ τ1   Γ ⊢ τ2          Γ ⊢ τ1 × τ2          Γ ⊢ τ1 × τ2
 ─────────────── (配对)   ─────────── (取第一)    ─────────── (取第二)
 Γ ⊢ τ1 × τ2              Γ ⊢ τ1               Γ ⊢ τ2

 dom :: Γ ⊢ cod                 Γ ⊢ dom ⟶ cod   Γ ⊢ dom
 ────────────────── (λ抽象)       ─────────────────────── (应用)
 Γ ⊢ dom ⟶ cod                  Γ ⊢ cod

 简单类型 λ 演算:
 https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus 
 de Bruijn 指数:   https://ncatlab.org/nlab/show/de+Bruijn+index 
 https://en.wikipedia.org/wiki/De_Bruijn_index
*)

Section Exp.

Import ListNotations.

Open Scope Ty_scope.

(* A typing context: the list of types of the in-scope variables, with the most recently bound variable at the head (de Bruijn index 0). / 一个类型环境：在作用域内变量的类型列表，最近绑定的变量位于列表头部（de Bruijn索引0）。 *)
Definition Env := list Ty.

(*
 Well-scoped de Bruijn indices: [Var Γ τ] witnesses that the context Γ has
 a variable of type τ.  [ZV] is index 0 (the head binding); [SV] is the
 successor, weakening a variable under one more binding. 

 --------
 范围良好的 de Bruijn 指数：[Var Γ τ] 证明了上下文 Γ 有一个类型为 τ 的变量。[ZV] 是索引 0（头部绑定）；[SV] 是后继，在额外一个绑定下弱化一个变量。
*)
Inductive Var : Env → Ty → Set :=
  | ZV {Γ τ}    : Var (τ :: Γ) τ           (* de Bruijn index 0: head slot / de Bruijn 索引 0：头槽 *)
  | SV {Γ τ τ'} : Var Γ τ → Var (τ' :: Γ) τ.  (* successor: skip the head slot / 继任者：跳过首席职位 *)

Derive Signature NoConfusion EqDec for Var.

(* Well-typed terms: [Exp Γ τ] is a derivation of Γ ⊢ τ. Each constructor is one STLC typing rule, so the GADT contains exactly the well-typed terms. / 良型术语：[Exp Γ τ] 是 Γ ⊢ τ 的一个推导。每个构造函数都是一个 STLC 类型规则，所以 GADT 恰好包含所有良型术语。 *)
Inductive Exp Γ : Ty → Set :=
  | EUnit         : Exp Γ TyUnit                              (* unit introduction / 单元介绍 *)

  | Pair {τ1 τ2}  : Exp Γ τ1 → Exp Γ τ2 → Exp Γ (TyPair τ1 τ2)  (* product introduction / 产品介绍 *)
  | Fst {τ1 τ2}   : Exp Γ (TyPair τ1 τ2) → Exp Γ τ1          (* first projection / 第一次投影 *)
  | Snd {τ1 τ2}   : Exp Γ (TyPair τ1 τ2) → Exp Γ τ2          (* second projection / 第二投影 *)

  | VAR {τ}       : Var Γ τ → Exp Γ τ                        (* variable / 变量 *)
  | LAM {dom cod} : Exp (dom :: Γ) cod → Exp Γ (dom ⟶ cod)   (* abstraction / 抽象 *)
  | APP {dom cod} : Exp Γ (dom ⟶ cod) → Exp Γ dom → Exp Γ cod.  (* application / 应用 *)

Derive Signature NoConfusionHom Subterm EqDec for Exp.

(* Structural size of a term, counting one for every node. Used as a well-founded measure for size-decreasing recursions elsewhere. / 术语的结构大小，对每个节点计数一次。用于作为其他地方规模递减递归的良基测度。 *)
Fixpoint Exp_size {Γ τ} (e : Exp Γ τ) : nat :=
  match e with
  | EUnit _       => 1
  | Pair _ x y    => 1 + Exp_size x + Exp_size y
  | Fst _ p       => 1 + Exp_size p
  | Snd _ p       => 1 + Exp_size p
  | VAR _ v       => 1
  | LAM _ e       => 1 + Exp_size e
  | APP _ e1 e2   => 1 + Exp_size e1 + Exp_size e2
  end.

Corollary Exp_size_preserved {Γ τ} (e1 e2 : Exp Γ τ) :
  Exp_size e1 ≠ Exp_size e2 → e1 ≠ e2.
Proof. repeat intro; subst; contradiction. Qed.

End Exp.

Arguments EUnit {Γ}.
Arguments Pair {Γ τ1 τ2} _ _.
Arguments Fst {Γ τ1 τ2} _.
Arguments Snd {Γ τ1 τ2} _.
Arguments VAR {Γ τ} _.
Arguments LAM {Γ dom cod} _.
Arguments APP {Γ dom cod} _ _.

(* Judgement notation: [Γ ∋ τ] for a variable, [Γ ⊢ τ] for a well-typed term. / 判定符号：变量使用 [Γ ∋ τ]，类型正确的项使用 [Γ ⊢ τ]。 *)
Notation "Γ ∋ τ" := (Var Γ τ) (at level 10).
Notation "Γ ⊢ τ" := (Exp Γ τ) (at level 10).
