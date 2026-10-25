Require Import Category.Lib.
Require Import Category.Lib.IList.
Require Import Category.Instance.Lambda.Ty.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Ren.
Require Import Category.Instance.Lambda.Sub.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

(** Denotational semantics of the simply-typed lambda calculus in a CCC / 简单类型λ演算在笛卡尔闭范畴中的指称语义 *)

(*
 nLab: https://ncatlab.org/nlab/show/relation+between+type+theory+and+category+theory
 Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category
 Wikipedia: https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence

 This file gives the categorical (denotational) semantics of the de Bruijn
 STLC of Exp.v, realizing the Curry-Howard-Lambek correspondence: a
 cartesian closed category interprets the calculus, with the product type
 denoting the categorical product, the function type denoting the internal
 hom (exponential), and a context denoting the iterated product of its
 types.  Here the interpreting CCC is taken to be Coq's own universe [Type]
 (with [unit] terminal, [*] product, [→] exponential), so the interpretation
 is the standard one read off into that concrete model:

 ⟦TyUnit⟧      := unit                   (terminal object)
 ⟦t1 × t2⟧     := ⟦t1⟧ * ⟦t2⟧            (categorical product)
 ⟦dom ⟶ cod⟧  := ⟦dom⟧ → ⟦cod⟧          (exponential / internal hom)
 ⟦Γ⟧           := ilist ⟦·⟧ Γ            (right-nested product of types)
 ⟦Γ ⊢ t : τ⟧   : ⟦Γ⟧ → ⟦τ⟧              (a morphism in the CCC)

 On terms (SemExp) the standard CCC interpretation is used: a variable is a
 product projection (var = proj), application is evaluation composed with
 pairing (app = eval ∘ ⟨_,_⟩), and lambda abstraction is currying
 (lam = curry).  The remaining results are the semantic compatibility lemmas
 between interpretation and the renaming/substitution machinery of Ren.v and
 Sub.v; they are what make βη-equality sound, witnessed downstream by
 [soundness] in Sound.v ([e ---> v] implies [SemExp e = SemExp v]).  By
 Lambek's theorem the syntax presented here is the free CCC, so this
 interpretation factors uniquely through every model. 

 --------
 nLab:  https://ncatlab.org/nlab/show/relation+between+type+theory+and+category+theory
 维基百科:  https://en.wikipedia.org/wiki/Cartesian_closed_category
 维基百科:  https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence

 此文件提供了 Exp.v 中 de Bruijn STLC 的范畴（指称）语义，实现了 Curry-Howard-Lambek 对应关系：一个笛卡尔闭范畴解释该演算，产品类型表示范畴积，函数类型表示内部 Hom（指数），上下文表示其类型的迭代积。这里解释的 CCC 取为 Coq 自身的宇宙 [Type]（其中 [unit] 为终对象，[*] 为积，[→] 为指数），因此该解释是读入该具体模型的标准解释:⟦TyUnit⟧      := unit                   （终对象）
 ⟦t1 × t2⟧     := ⟦t1⟧ * ⟦t2⟧            （范畴积）
 ⟦dom ⟶ cod⟧  := ⟦dom⟧ → ⟦cod⟧          （指数对象 / 内部 Hom）
 ⟦Γ⟧           := ilist ⟦·⟧ Γ            （类型的右嵌套积）
 ⟦Γ ⊢ t : τ⟧   : ⟦Γ⟧ → ⟦τ⟧              （CCC 中的一个态射）在项 (SemExp) 上使用标准的 CCC 解释：变量是一个积的投影（var = proj），应用是评估与配对的组合（app = eval ∘ ⟨_,_⟩），λ 抽象是柯里化（lam = curry）。其余的结果是解释与 Ren.v 和 Sub.v 的重命名/替换机制之间的语义兼容引理；它们使得 βη 等式是正确的，下游在 Sound.v 中由 [soundness] 证明（[e ---> v] 推出 [SemExp e = SemExp v]）。根据 Lambek 定理，此处呈现的语法是自由 CCC，因此该解释在每个模型中都是唯一可分解的。
*)

Section Sem.

Fixpoint SemTy (τ : Ty) : Type :=
  match τ with
  | TyUnit          => unit                  (* terminal object / 终端对象 *)
  | TyPair t1 t2    => SemTy t1 * SemTy t2   (* categorical product / 笛卡尔积 *)
  | TyArrow dom cod => SemTy dom → SemTy cod (* exponential / internal hom / 指数 / 内部 Hom *)
  end.

(* A context denotes the iterated (right-nested) product of its types. / 一个上下文表示其类型的迭代（右嵌套）乘积。 *)
Definition SemEnv Γ : Type := ilist (B:=SemTy) Γ.

(* A variable denotes a product projection (var = proj). / 一个变量表示一个乘积投影（var = proj）。 *)
Fixpoint SemVar `(v : Var Γ τ) : SemEnv Γ → SemTy τ :=
  match v with
  | ZV   => λ se, fst se              (* first projection / 第一次投影 *)
  | SV v => λ se, SemVar v (snd se)   (* projection through the tail / 通过尾部的投影 *)
  end.

Equations RenSem {Γ Γ'} (r : Ren Γ Γ') (se : SemEnv Γ) : SemEnv Γ' :=
  RenSem NoRen    se      := se;
  RenSem (Drop r) (_, se) := RenSem r se;
  RenSem (Keep r) (e, se) := (e, RenSem r se).

Lemma RenSem_inil (r : Ren nil nil) :
  RenSem r () = ().
Proof. now dependent destruction r. Qed.

Lemma RenSem_idRen {Γ} (se : SemEnv Γ) :
  RenSem idRen se = se.
Proof.
  induction Γ; destruct se; simpl; simp RenSem; intros; auto.
  now rewrite IHΓ.
Qed.

Lemma RenSem_skip1 {Γ τ} (e : SemTy τ) (se : SemEnv Γ) :
  RenSem skip1 (e, se) = se.
Proof.
  induction Γ; destruct se; simpl; intros; auto.
  unfold skip1; simp RenSem.
  now rewrite RenSem_idRen.
Qed.

Lemma SemVar_RenSem Γ τ (v : Var Γ τ) Γ' (r : Ren Γ' Γ) (se : SemEnv Γ') :
  SemVar v (RenSem r se) = SemVar (RenVar r v) se.
Proof.
  intros.
  induction r; simp RenSem; simp RenVar; simpl;
  destruct se; simp RenSem; auto.
  now dependent elimination v; simpl; simp RenVar.
Qed.

Lemma RenSem_RcR {Γ Γ' Γ''} (f : Ren Γ' Γ'') (g : Ren Γ Γ') (se : SemEnv Γ) :
  RenSem (RcR f g) se = RenSem f (RenSem g se).
Proof.
  generalize dependent Γ''.
  generalize dependent Γ'.
  induction Γ; destruct se; simpl; intros; auto.
  - inversion g; subst.
    rewrite RenSem_inil.
    inversion f; subst.
    now rewrite !RenSem_inil.
  - dependent elimination g; simp RenSem.
    + now rewrite <- IHΓ; simp RcR; simp RenSem.
    + dependent elimination f; simp RenSem;
      now rewrite <- IHΓ; simp RcR; simp RenSem.
Qed.

(*
 The term interpretation ⟦Γ ⊢ e : τ⟧ : ⟦Γ⟧ → ⟦τ⟧, the standard CCC
 semantics read into Coq's [Type]: pairing into the product, the product
 projections, a variable as a projection, λ as currying, and application
 as evaluation composed with pairing. 

 --------
 术语解释 ⟦Γ ⊢ e : τ⟧ : ⟦Γ⟧ → ⟦τ⟧，标准的 CCC 语义被引入 Coq 的 [Type] 中：配对进入积，积的投影，变量作为投影，λ 表示柯里化，应用作为与配对组合的求值。
*)
Fixpoint SemExp `(e : Exp Γ τ) : SemEnv Γ → SemTy τ :=
  match e with
  | EUnit     => λ _, tt                              (* unique map to terminal / 到终端的唯一映射 *)
  | Pair x y  => λ se, (SemExp x se, SemExp y se)     (* pairing ⟨_,_⟩           *)
  | Fst p     => λ se, fst (SemExp p se)              (* first projection / 第一次投影 *)
  | Snd p     => λ se, snd (SemExp p se)              (* second projection / 第二投影 *)
  | VAR v     => SemVar v                             (* var = proj              *)
  | LAM e     => λ se x, SemExp e (x, se)             (* lam = curry / 羊腿 = 咖喱 *)
  | APP e1 e2 => λ se, SemExp e1 se (SemExp e2 se)    (* app = eval ∘ ⟨_,_⟩      *)
  end.

Equations SubSem {Γ Γ'} (s : Sub Γ Γ') (se : SemEnv Γ) : SemEnv Γ' :=
  SubSem NoSub      _  := tt;
  SubSem (Push t σ) se := (SemExp t se, SubSem σ se).

Lemma SubSem_inil (s : Sub nil nil) :
  SubSem s () = ().
Proof. now dependent elimination s. Qed.

Lemma SemExp_RenSem {Γ Γ' τ} (e : Exp Γ τ) (r : Ren Γ' Γ) (se : SemEnv Γ') :
  SemExp e (RenSem r se) = SemExp (RenExp r e) se.
Proof.
  generalize dependent Γ'.
  induction e; simpl; intros; auto.
  - now rewrite IHe1, IHe2.
  - now rewrite IHe.
  - now rewrite IHe.
  - now rewrite SemVar_RenSem.
  - extensionality z.
    fold SemTy in z.
    rewrite <- IHe; clear IHe.
    simpl.
    now repeat f_equal.
  - now rewrite IHe1, IHe2.
Qed.

Lemma ScR_idRen {Γ Γ'} (s : Sub Γ Γ') :
  ScR s idRen = s.
Proof.
  induction s; simp ScR; auto.
  now rewrite RenExp_idRen, IHs.
Qed.

Lemma SubSem_ScR {Γ Γ' Γ''} (s : Sub Γ' Γ'') (r : Ren Γ Γ') (se : SemEnv Γ) :
  SubSem (ScR s r) se = SubSem s (RenSem r se).
Proof.
  generalize dependent Γ''.
  generalize dependent Γ'.
  destruct Γ, se; simpl; intros; auto.
  - dependent elimination r; simp RenSem.
    rewrite NoRen_idRen.
    now rewrite ScR_idRen.
  - clear.
    dependent induction s1; simp ScR.
    + now simp SubSem.
    + simp SubSem.
      f_equal.
      * now rewrite SemExp_RenSem.
      * dependent elimination r; simp RenSem;
        now rewrite IHs1.
Qed.

Lemma SubSem_idSub {Γ} (se : SemEnv Γ) :
  SubSem idSub se = se.
Proof.
  induction Γ; destruct se; simpl; simp SubSem; simpl; intros; auto.
  rewrite SubSem_ScR.
  rewrite RenSem_skip1.
  now rewrite IHΓ.
Qed.

Lemma SemExp_wk `(E : SemEnv Γ) {τ τ'} (y : SemTy τ') (e : Exp Γ τ) :
  SemExp (wk e) (y, E) = SemExp e E.
Proof.
  unfold wk.
  rewrite <- SemExp_RenSem; simpl.
  f_equal.
  now rewrite RenSem_skip1.
Qed.

Lemma SemVar_SubSem {Γ Γ' τ} (v : Var Γ τ) (s : Sub Γ' Γ) (se : SemEnv Γ') :
  SemVar v (SubSem s se) = SemExp (SubVar s v) se.
Proof.
  intros.
  induction s; simp SubSem; simp SubVar; simpl.
  - now inversion v.
  - now dependent elimination v; simpl; simp RenVar.
Qed.

Lemma SemExp_SubSem {Γ Γ' τ} (e : Exp Γ τ) (s : Sub Γ' Γ) (se : SemEnv Γ') :
  SemExp e (SubSem s se) = SemExp (SubExp s e) se.
Proof.
  generalize dependent Γ'.
  induction e; simpl; intros; auto.
  - now rewrite IHe1, IHe2.
  - now rewrite IHe.
  - now rewrite IHe.
  - now rewrite SemVar_SubSem.
  - extensionality z.
    fold SemTy in z.
    rewrite <- IHe; clear IHe.
    simpl.
    unfold Keepₛ, Dropₛ; simp SubSem.
    repeat f_equal.
    rewrite SubSem_ScR.
    now rewrite RenSem_skip1.
  - now rewrite IHe1, IHe2.
Qed.

Lemma SubSem_ScS {Γ Γ' Γ''} (s : Sub Γ' Γ'') (t : Sub Γ Γ') (se : SemEnv Γ) :
  SubSem (ScS s t) se = SubSem s (SubSem t se).
Proof.
  generalize dependent Γ''.
  induction s; intros; simpl; simp SubSem; auto.
  now rewrite <- SemExp_SubSem, IHs.
Qed.

Lemma SubSem_RcS {Γ Γ' Γ''} (r : Ren Γ' Γ'') (s : Sub Γ Γ') (se : SemEnv Γ) :
  SubSem (RcS r s) se = RenSem r (SubSem s se).
Proof.
  generalize dependent Γ.
  induction r; intros; simpl; simp RcS; simp RenSem; auto;
  dependent elimination s; simp RcS; simp SubSem; simp RenSem.
  now rewrite IHr.
Qed.

End Sem.
