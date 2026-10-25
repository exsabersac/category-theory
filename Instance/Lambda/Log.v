Require Import Category.Lib.
Require Import Category.Instance.Lambda.Ltac.
Require Import Category.Instance.Lambda.Ty.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Sub.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

(** Type-indexed logical predicates and relations for the STLC. / STLC 的类型索引逻辑谓词和关系。 *)

(*
 "Log" here is the *logical relation* / logical predicate of Tait-style
 reducibility, not logarithms or logging.  Given a base predicate [P] on
 well-typed terms, [ExpP] lifts [P] type-directed through the syntax so that
 it is closed under the eliminators (application, projections); [ExpR] is the
 binary analogue lifting a base relation [R].  [Norm.v] instantiates [ExpP]
 with [halts] to obtain the strong-normalization predicate [SN := ExpP halts]
 and runs Tait's reducibility argument.

 Writing [τ |- e] for "[e : Exp Γ τ]", the unary predicate reads:

 ExpP P (e : TyUnit)    :=  P e
 ExpP P (e : σ × ρ)     :=  P e ∧ ExpP P (Fst e) ∧ ExpP P (Snd e)
 ExpP P (e : σ ⟶ ρ)     :=  P e ∧ ∀ x, ExpP P x → ExpP P (APP e x)

 so a function is reducible exactly when it sends reducible arguments to
 reducible results — the arrow case of Tait's "candidat de réductibilité".
 The binary [ExpR] follows the standard logical-relations recipe: related
 functions map related arguments to related results,
 [ExpR R f1 f2] at [σ ⟶ ρ] requiring [∀ x1 x2, ExpR R x1 x2 →
 ExpR R (APP f1 x1) (APP f2 x2)].
 See W. W. Tait, "Intensional interpretations of functionals of finite type
 I", and J. Gallier, "On Girard's 'Candidats de Reductibilité'",
 https://www.cis.upenn.edu/~jean/sngirard.pdf, and
 https://en.wikipedia.org/wiki/Logical_relations.

 Note: [A] and [L : HostExprs A] below are vestigial context.  No class named
 [HostExprs] is in scope, so [Generalizable All Variables] silently treats it
 as a free variable to be generalized; since nothing here depends on [A] or
 [L], both are dropped from the resulting definitions.  They are kept as a
 record of the intended host-language extension point used in sibling files
 (compare the analogous [HostExprsSem] note in [Instance/Lambda.v]). 

 --------
 这里的“Log”是 Tait 风格可约性的*逻辑关系*/逻辑谓词，不是对数或记录。给定一个在良类型项上的基础谓词 [P]，[ExpP] 通过语法对 [P] 进行类型导向提升，使其对消去子（应用、投影）闭合；[ExpR] 是将基础关系 [R] 提升的二元类似物。[Norm.v] 用 [halts] 实例化 [ExpP] 以获得强归一化谓词 [SN := ExpP halts] 并运行 Tait 的可约性论证。

 将 [τ |- e] 写作“[e : Exp Γ τ]”，该一元谓词表述为：

 ExpP P (e : TyUnit)    :=  P e
 ExpP P (e : σ × ρ)     :=  P e ∧ ExpP P (Fst e) ∧ ExpP P (Snd e)
 ExpP P (e : σ ⟶ ρ)     :=  P e ∧ ∀ x, ExpP P x → ExpP P (APP e x)所以一个函数当且仅当它将可约的参数映射到可约的结果时才是可约的——这是 Tait 的“可约性候选”中的箭头情况。二元 [ExpR] 遵循标准的逻辑关系方法：相关的函数将相关的参数映射到相关的结果，[ExpR R f1 f2] 在 [σ ⟶ ρ] 处要求 [∀ x1 x2, ExpR R x1 x2 → ExpR R (APP f1 x1) (APP f2 x2)]。参见 W. W. Tait, “Intensional interpretations of functionals of finite type I”，以及 J. Gallier, “On Girard's 'Candidats de Reductibilité'”，https://www.cis.upenn.edu/~jean/sngirard.pdf, 和 https://en.wikipedia.org/wiki/Logical_relations.。注意：下面的 [A] 和 [L : HostExprs A] 是残余上下文。范围内没有名为 [HostExprs] 的类，因此 [Generalizable All Variables] 会默默地将其视为要泛化的自由变量；由于这里没有任何依赖于 [A] 或 [L] 的内容，它们都从生成的定义中删除。它们被保留作为在同级文件中使用的预期宿主语言扩展点的记录（参见 [Instance/Lambda.v] 中类似的 [HostExprsSem] 注释）。
*)

Section Log.

Context {A : Type}.
Context `{L : HostExprs A}.
Context {Γ : Env}.

Variable P : ∀ {τ}, Exp Γ τ → Type.

(** [ExpP] lifts the base predicate [P] type-directed through the syntax. / [ExpP] 通过语法将基本谓词 [P] 类型导向地提升。 *)
Equations ExpP `(e : Exp Γ τ) : Type :=
  ExpP (τ:=_ ⟶ _) e := P e ∧ (∀ x, ExpP x → ExpP (APP e x));
  ExpP (τ:=_ × _) e := P e ∧ ExpP (Fst e) ∧ ExpP (Snd e);
  ExpP e := P e.

(*
 [SubP] extends [ExpP] pointwise to substitutions: every pushed term is
 reducible. 

 --------
 [SubP] 点对点地扩展 [ExpP] 至替换：每个推送的项都是可约的。
*)
Inductive SubP : ∀ {Γ'}, Sub Γ Γ' → Type :=
  | NoSubP : SubP (NoSub (Γ:=Γ))
  | PushP {Γ' τ} (e : Exp Γ τ) (s : Sub Γ Γ') :
    ExpP e → SubP s → SubP (Push e s).

Derive Signature for SubP.

(* The base predicate is the head component at every type (CR1-style extraction): reducibility implies [P]. / 基本谓词是在每种类型上的头部成分（CR1风格抽取）：可约性意味着 [P]。 *)
Lemma ExpP_P {τ} {e : Γ ⊢ τ} : ExpP e → P e.
Proof. intros; induction τ; simpl in *; simp ExpP in X; now reduce. Qed.

Variable R : ∀ {τ}, Exp Γ τ → Exp Γ τ → Type.

(** [ExpR] is the binary analogue of [ExpP], lifting the base relation [R]. / [ExpR] 是 [ExpP] 的二进制类似物，提升了基本关系 [R]。 *)
Equations ExpR {τ} (e1 e2 : Exp Γ τ) : Type :=
  ExpR (τ:=_ ⟶ _) f1 f2 :=
    R f1 f2 ∧ (∀ x1 x2, ExpR x1 x2 → ExpR (APP f1 x1) (APP f2 x2));
  ExpR (τ:=_ × _) e1 e2 :=
    R e1 e2 ∧ ExpR (Fst e1) (Fst e2) ∧ ExpR (Snd e1) (Snd e2);
  ExpR e1 e2 := R e1 e2.

(*
 The base relation is the head component at every type: relatedness implies
 [R]. 

 --------
 基本关系是在每种类型中的核心组成部分：相关性意味着 [R]。
*)
Lemma ExpR_R {τ} {e1 e2 : Γ ⊢ τ} : ExpR e1 e2 → R e1 e2.
Proof. intros; induction τ; simpl in *; simp ExpR in X; now reduce. Qed.

(* [SubR] extends [ExpR] pointwise to substitutions. / [SubR] 点对点地扩展了 [ExpR] 到替换。 *)
Inductive SubR : ∀ {Γ'}, Sub Γ Γ' → Type :=
  | NoSubR : SubR (NoSub (Γ:=Γ))
  | PushR {Γ' τ} (e e' : Exp Γ τ) (s : Sub Γ Γ') :
    ExpR e e' → SubR s → SubR (Push e s).

Derive Signature for SubR.

End Log.
