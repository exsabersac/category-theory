Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Value.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Set Transparent Obligations.

(** Renaming (variable renaming / weakening) for the de Bruijn calculus / de Bruijn 演算的重命名（变量重命名 / 弱化） *)

(*
 A [Ren Γ Γ'] is an order-preserving embedding (OPE, a.k.a. "thinning") of
 the context Γ' into the context Γ: it lists, in order, which slots of the
 larger context Γ are kept as the variables of the smaller context Γ'.  This
 is the inductive "category of weakenings" of Altenkirch-Hofmann-Streicher
 (1995) / order-preserving embeddings of Chapman (2009).

 The action of a renaming is contravariant: [RenVar]/[RenExp] transport a
 variable / term living in Γ' to one living in the larger Γ, so a renaming
 r : Ren Γ Γ' yields maps  Var Γ' τ → Var Γ τ  and  Exp Γ' τ → Exp Γ τ.
 With composition [RcR] this makes (Env, Ren) a category, and Var(-,τ) and
 Exp(-,τ) presheaves on it; the laws below are exactly its identity,
 associativity, and functoriality equations.

 de Bruijn indices:  https://ncatlab.org/nlab/show/de+Bruijn+index
 https://en.wikipedia.org/wiki/De_Bruijn_index
 substitution / renaming:  https://ncatlab.org/nlab/show/substitution 

 --------
 [Ren Γ Γ'] 是一个顺序保持嵌入（OPE，也称为“稀疏化”），用于将上下文 Γ' 嵌入到上下文 Γ 中：它按顺序列出较大上下文 Γ 的哪些位置被保留作为较小上下文 Γ' 的变量。这是 Altenkirch-Hofmann-Streicher (1995) 的归纳“弱化范畴”/ Chapman (2009) 的顺序保持嵌入。

 重命名的作用是逆变的：[RenVar] / [RenExp] 将居于 Γ' 的变量/项传输到居于较大 Γ 的位置，因此重命名 r : Ren Γ Γ' 产生映射 Var Γ' τ → Var Γ τ 和 Exp Γ' τ → Exp Γ τ。通过组合 [RcR]，这使得 (Env, Ren) 成为一个范畴，而 Var(-,τ) 和 Exp(-,τ) 是其上的预上层；下面的规律正是它的恒等律、结合律以及函子律方程。de Bruijn 指数：   https://ncatlab.org/nlab/show/de+Bruijn+index 
 https://en.wikipedia.org/wiki/De_Bruijn_index 
 替换 / 重命名：   https://ncatlab.org/nlab/show/substitution
*)

Section Ren.

Import ListNotations.

(*
 Renamings as order-preserving embeddings (thinnings):
 NoRen  : the empty thinning [] ↪ []
 Drop r : skip the head slot of the source context (it has no pre-image)
 Keep r : keep the head slot, mapping it to the head of the target 

 --------
 重命名作为保持顺序的嵌入（稀疏映射）：
 NoRen  : 空的稀疏映射 [] ↪ []
 Drop r : 跳过源上下文的头部位置（它没有原象）
 Keep r : 保留头部位置，将其映射到目标的头部
*)
Inductive Ren : Env → Env → Set :=
  | NoRen : Ren [] []
  | Drop {τ Γ Γ'} : Ren Γ Γ' → Ren (τ :: Γ) Γ'
  | Keep {τ Γ Γ'} : Ren Γ Γ' → Ren (τ :: Γ) (τ :: Γ').

Derive Signature NoConfusion EqDec for Ren.

(* Identity renaming: keep every slot (the identity OPE Γ ↪ Γ). / 身份重命名：保留每个槽位（身份 OPE Γ ↪ Γ）。 *)
Fixpoint idRen {Γ} : Ren Γ Γ :=
  match Γ with
  | []     => NoRen
  | τ :: Γ => Keep idRen
  end.

(* Keeping the head of an identity renaming is again the identity. / 保持身份重命名的头部仍然是该身份。 *)
Lemma Keep_idRen {Γ τ} : Keep (τ:=τ) (@idRen Γ) = idRen.
Proof. now induction Γ. Qed.

(* The unique thinning into the empty context: drop every slot. / 唯一稀疏到空上下文：丢弃每个格位。 *)
Equations DropAll {Γ} : Ren Γ [] :=
  DropAll (Γ:=[])      := NoRen;
  DropAll (Γ:=_ :: xs) := Drop (DropAll (Γ:=xs)).

Corollary NoRen_idRen : NoRen = idRen.
Proof. reflexivity. Qed.

Corollary DropAll_nil_idRen : DropAll (Γ:=[]) = idRen.
Proof. reflexivity. Qed.

(* Single-variable weakening: drop one fresh slot τ, keep the rest. / 单变量削弱：丢弃一个新鲜的槽 τ，保留其余的。 *)
Definition skip1 {Γ τ} : Ren (τ :: Γ) Γ := Drop idRen.

(*
 Composition of renamings (diagrammatic in the OPE category): RcR r r'
 first applies the inner thinning r' then the outer r. 

 --------
 重命名的组合（OPE范畴中的图示）：RcR r r' 先应用内部稀疏化 r'，然后应用外部 r。
*)
Equations RcR {Γ Γ' Γ''} (r : Ren Γ' Γ'') (r' : Ren Γ Γ') : Ren Γ Γ'' :=
  RcR σ        NoRen    := σ;
  RcR σ        (Drop δ) := Drop (RcR σ δ);
  RcR (Drop σ) (Keep δ) := Drop (RcR σ δ);
  RcR (Keep σ) (Keep δ) := Keep (RcR σ δ).

(* Left identity law of the renaming category: idRen ∘ σ = σ. / 重命名范畴的左恒等律：idRen ∘ σ = σ。 *)
Lemma RcR_idRen_left {Γ Γ'} (σ : Ren Γ Γ') :
  RcR idRen σ = σ.
Proof.
  induction σ; simp RcR; simpl; simp RcR; auto;
  now rewrite IHσ.
Qed.

(* Right identity law of the renaming category: σ ∘ idRen = σ. / 重命名范畴的右恒等律：σ ∘ idRen = σ。 *)
Lemma RcR_idRen_right {Γ Γ'} (σ : Ren Γ Γ') :
  RcR σ idRen = σ.
Proof.
  induction σ; simp RcR; simpl; simp RcR; auto;
  now rewrite IHσ.
Qed.

(* Associativity law of the renaming category. / 重命名范畴的结合律。 *)
Lemma RcR_assoc {Γ Γ' Γ'' Γ'''}
      (σ : Ren Γ'' Γ''') (δ : Ren Γ' Γ'') (ν : Ren Γ Γ') :
  RcR (RcR σ δ) ν = RcR σ (RcR δ ν).
Proof.
  generalize dependent Γ'''.
  generalize dependent Γ''.
  induction ν; simp RcR; simpl; intros; auto.
  - simp RcR.
    now rewrite IHν.
  - dependent elimination δ; simp RcR; simpl.
    + now rewrite IHν.
    + dependent elimination σ; simp RcR; simpl;
      now rewrite IHν.
Qed.

(* Action of a renaming on a variable (contravariant: Var Γ' → Var Γ). A dropped slot shifts the index by one (SV); a kept slot passes the most-local variable through unchanged. / 对变量的重命名操作（逆变：Var Γ' → Var Γ）。丢弃的槽会使索引增加一（SV）；保留的槽会将最局部的变量保持不变地传递下去。 *)
Equations RenVar {τ Γ Γ'} (r : Ren Γ Γ') (v : Var Γ' τ) : Var Γ τ :=
  RenVar NoRen    v      := v;
  RenVar (Drop σ) v      := SV (RenVar σ v);
  RenVar (Keep σ) ZV     := ZV;
  RenVar (Keep σ) (SV v) := SV (RenVar σ v).

(* Identity law: the identity renaming fixes every variable. / 恒等律：恒等重命名修复每个变量。 *)
Lemma RenVar_idRen {τ Γ} (v : Var Γ τ) :
  RenVar idRen v = v.
Proof.
  induction v; simpl; simp RenVar; intros; auto.
  now rewrite IHv.
Qed.

(* Renaming by skip1 is exactly the variable-shift SV (de Bruijn weakening). / 通过 skip1 重命名恰好是变量移位 SV（de Bruijn 弱化）。 *)
Lemma RenVar_skip1 {τ τ' Γ} (v : Var Γ τ) :
  RenVar (skip1 (τ:=τ')) v = SV v.
Proof.
  unfold skip1; simp RenVar.
  now rewrite RenVar_idRen.
Qed.

(* Functoriality of RenVar over composition of renamings. / RenVar 在重命名组合上的函子性。 *)
Lemma RenVar_RcR {τ Γ Γ' Γ''} (σ : Ren Γ' Γ'') (δ : Ren Γ Γ') (v : Var Γ'' τ) :
  RenVar (RcR σ δ) v = RenVar δ (RenVar σ v).
Proof.
  generalize dependent Γ''.
  induction δ; simpl; simp RcR; intros; auto.
  - simp RenVar.
    now rewrite <- IHδ.
  - dependent elimination σ; simpl; simp RcR; simp RenVar.
    + now rewrite IHδ.
    + dependent elimination v; simp RenVar; auto.
      now rewrite IHδ.
Qed.

(*
 Keep commutes with composition: extending both factors by a kept slot
 and composing equals composing then keeping (used to push renamings
 under binders). 

 --------
 保持与组合的交换：通过保留槽扩展两个因子，然后组合等于先组合再保留（用于在绑定器下推动重命名）。
*)
Lemma Keep_RcR Γ Γ' Γ'' τ (r : Ren Γ' Γ'') (r' : Ren Γ Γ') :
  Keep (τ := τ) (RcR r r') = RcR (Keep r) (Keep r').
Proof.
  generalize dependent Γ''.
  now induction r'.
Qed.

(*
 Action of a renaming on a term (the renaming functor on Exp); LAM pushes
 the renaming under the binder via Keep. 

 --------
 对一个项的重命名操作（Exp 上的重命名函子）；LAM 通过 Keep 将重命名推进绑定器下。
*)
Fixpoint RenExp {Γ Γ' τ} (r : Ren Γ Γ') (e : Exp Γ' τ) : Exp Γ τ :=
  match e with
  | EUnit         => EUnit
  | Pair x y      => Pair (RenExp r x) (RenExp r y)
  | Fst p         => Fst (RenExp r p)
  | Snd p         => Snd (RenExp r p)
  | VAR v         => VAR (RenVar r v)
  | APP e1 e2     => APP (RenExp r e1) (RenExp r e2)
  | LAM e         => LAM (RenExp (Keep r) e)
  end.

(* Renaming preserves term size (no slots are duplicated or erased). / 重命名保持术语大小（不会重复或删除槽位）。 *)
Lemma RenExp_preserves_size {Γ Γ' τ} (r : Ren Γ Γ') (e : Exp Γ' τ) :
  Exp_size (RenExp r e) = Exp_size e.
Proof.
  generalize dependent r.
  generalize dependent Γ.
  now induction e; simpl; simp RcR; simpl; intros; auto.
Qed.

(* Identity law of the renaming functor: idRen acts as the identity on terms. / 重命名函子同一律：idRen 在项上作为同一元作用。 *)
Lemma RenExp_idRen {τ Γ} (e : Exp Γ τ) :
  RenExp idRen e = e.
Proof.
  induction e; simpl; simp RenVar; simpl; intros; auto;
  rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; auto.
  - now rewrite RenVar_idRen.
  - now rewrite Keep_idRen, IHe.
Qed.

(* A closed term is fixed by the (unique) thinning out of the empty context. / 封闭项由空上下文的（唯一）稀疏化所固定。 *)
Lemma RenExp_DropAll {τ} (e : Exp [] τ) :
  RenExp DropAll e = e.
Proof.
  rewrite DropAll_nil_idRen.
  now rewrite RenExp_idRen.
Qed.

(* Functoriality of the renaming functor over composition of renamings. / 重命名函子在重命名组合上的函子性。 *)
Lemma RenExp_RcR {τ Γ Γ' Γ''} (σ : Ren Γ' Γ'') (δ : Ren Γ Γ') (e : Exp Γ'' τ) :
  RenExp (RcR σ δ) e = RenExp δ (RenExp σ e).
Proof.
  generalize dependent Γ'.
  generalize dependent Γ.
  induction e; simpl; intros; auto;
  rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; auto.
  - now rewrite RenVar_RcR.
  - now rewrite <- IHe; simp RcR.
Qed.

(* Renaming preserves values: the image of a value under any renaming is a value of the same shape. Kept transparent (Defined) as it is computational. / 重命名保持值：在任何重命名下，值的映像都是具有相同形状的值。由于它是计算性的，因此保持透明（定义）。 *)
Lemma RenExp_ValueP {Γ Γ' τ} {v : Exp Γ τ} (σ : Ren Γ' Γ) :
  ValueP v → ValueP (RenExp σ v).
Proof.
  intros X.
  now induction X; simpl; intros; try constructor.
Defined.

(* Weakening: introduce one fresh variable τ' on the left (RenExp skip1). / 弱化：在左边引入一个新的变量 τ'（RenExp skip1）。 *)
Definition wk {Γ τ τ'} : Exp Γ τ → Exp (τ' :: Γ) τ := RenExp skip1.

(*
 Right-append weakening on variables: Γ ↪ Γ ++ Γ' leaves de Bruijn indices
 into the prefix Γ unchanged. 

 --------
 在变量上的右附加弱化：Γ ↪ Γ ++ Γ' 保持前缀 Γ 中的 de Bruijn 索引不变。
*)
Equations RenExpandVar {Γ Γ' τ} (v : Var Γ τ) : Var (Γ ++ Γ') τ :=
  RenExpandVar ZV     := ZV;
  RenExpandVar (SV v) := SV (RenExpandVar v).

(* Right-append weakening on terms (extends RenExpandVar structurally). / 在项上右附减弱（在结构上扩展 RenExpandVar）。 *)
Fixpoint RenExpandExp {Γ Γ' τ} (e : Exp Γ τ) : Exp (Γ ++ Γ') τ :=
  match e with
  | EUnit         => EUnit
  | Pair x y      => Pair (RenExpandExp x) (RenExpandExp y)
  | Fst p         => Fst (RenExpandExp p)
  | Snd p         => Snd (RenExpandExp p)
  | VAR v         => VAR (RenExpandVar v)
  | APP e1 e2     => APP (RenExpandExp e1) (RenExpandExp e2)
  | LAM e         => LAM (RenExpandExp e)
  end.

(* Append a context Γ' on the right of an existing context Γ. / 在已有的上下文 Γ 的右边附加一个上下文 Γ'。 *)
Definition liftL Γ' `(e : Exp Γ τ) : Exp (Γ ++ Γ') τ := RenExpandExp e.

(* Prepend a context Γ on the left, iterating single weakenings (skip1). / 在左侧添加一个上下文 Γ，迭代单个弱化（skip1）。 *)
Fixpoint liftR Γ `(e : Exp Γ' τ) : Exp (Γ ++ Γ') τ :=
  match Γ with
  | []      => e
  | x :: xs => RenExp skip1 (liftR xs e)
  end.

End Ren.
