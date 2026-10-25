Require Import Category.Lib.
Require Import Category.Instance.Lambda.Ltac.
Require Import Category.Instance.Lambda.Ty.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Value.
Require Import Category.Instance.Lambda.Ren.
Require Import Category.Instance.Lambda.Sub.
Require Import Category.Instance.Lambda.Sem.
Require Import Category.Instance.Lambda.Step.

From Equations Require Import Equations.
Set Equations With UIP.

(** Multi-step reduction: the reflexive-transitive closure of [Step] / 多步归约：[Step] 的自反传递闭包 *)

(*
 [multi R] is the reflexive-transitive closure of a relation R: the least
 reflexive and transitive relation containing R.  Applied to the single-step
 reduction [Step], [multi Step] (written t --->* t') is multi-step reduction,
 relating t to t' when t reduces to t' in zero or more steps:

 t --->* t'   iff   t = r0 ---> r1 ---> ... ---> rn = t'   (n >= 0).

 The two constructors are exactly the closure's defining rules: [multi_refl]
 (reflexivity / the empty reduction sequence) and [multi_step] (prepend one
 R-step to a sequence).  [multi_R], [multi_trans], and the PreOrder instance
 record that the closure contains R, is transitive, and hence is a preorder;
 the remaining lemmas lift the single-step congruence rules of [Step] (under
 APP, Pair, Fst, Snd) to multi-step reduction, and [values_final] records
 that a value reduces only to itself.  This is the [multi] combinator of
 Pierce et al., Software Foundations (Smallstep chapter).

 reflexive-transitive closure:
 https://ncatlab.org/nlab/show/transitive+closure
 https://en.wikipedia.org/wiki/Transitive_closure
 abstract rewriting / multi-step reduction:
 https://en.wikipedia.org/wiki/Abstract_rewriting_system
 Software Foundations, Smallstep (the [multi] relation):
 https://softwarefoundations.cis.upenn.edu/plf-current/Smallstep.html 

 --------
 [multi R] 是关系 R 的自反-传递闭包：包含 R 的最小自反且传递的关系。应用于单步约简 [Step]，[multi Step]（写作 t --->* t'）是多步约简，当 t 在零步或多步内约简到 t' 时，将 t 与 t' 关联起来：

 t --->* t'   当且仅当   t = r0 ---> r1 ---> ... ---> rn = t'   (n >= 0)。这两个构造函数正是闭包的定义规则：[multi_refl]（自反性/空归约序列）和[multi_step]（在序列前添加一步R步骤）。[multi_R]、[multi_trans]以及PreOrder实例记录了闭包包含R，是传递的，因此是一个预序；其余引理将[Step]（在APP、Pair、Fst、Snd下）的单步一致性规则提升为多步归约，[values_final]记录值只归约到其自身。这是Pierce等人在Software Foundations（Smallstep章节）中的[multi]组合子。

 自反-传递闭包：
 https://ncatlab.org/nlab/show/transitive+closure
 https://en.wikipedia.org/wiki/Transitive_closure
 抽象重写/多步归约：
 https://en.wikipedia.org/wiki/Abstract_rewriting_system
 Software Foundations, Smallstep（[multi]关系）：
 https://softwarefoundations.cis.upenn.edu/plf-current/Smallstep.html
*)

Section Multi.

Generalizable All Variables.

(* Reflexive-transitive closure of R: [multi_refl] is the empty sequence and [multi_step] prepends one R-step to an existing sequence. / 关系 R 的自反-传递闭包：[multi_refl] 是空序列，[multi_step] 将一个 R 步添加到现有序列的前面。 *)
Inductive multi `(R : crelation X) : crelation X :=
  | multi_refl (x : X) : multi x x
  | multi_step (x y z : X) : R x y → multi y z → multi x z.

Derive Signature for multi.

(* The closure contains R: a single step is a one-step sequence. / 闭包包含R：单一步骤是一-step序列。 *)
Theorem multi_R `(R : crelation X) (x y : X) :
  R x y → multi R x y.
Proof.
  intros.
  eapply multi_step; eauto.
  now constructor.
Qed.

(* Transitivity: concatenation of reduction sequences. / 传递性：约简序列的串联。 *)
Theorem multi_trans `(R : crelation X) (x y z : X) :
  multi R x y →
  multi R y z →
  multi R x z.
Proof.
  intros.
  induction X0; auto.
  now eapply multi_step; eauto.
Qed.

(* The closure is a preorder (reflexive and transitive). / 该闭包是一个前序（自反且传递）。 *)
#[export]
Program Instance multi_PreOrder `(R : crelation X) :
  PreOrder (multi R).
Next Obligation. now constructor. Qed.
Next Obligation. now eapply multi_trans; eauto. Qed.

Notation " t '--->*' t' " := (multi Step t t') (at level 40).

(*
 A multi-step sequence may be extended by one [Step] at either end: the
 contravariant (flipped) argument prepends a step before the sequence, the
 covariant argument appends one after it. 

 --------
 一个多步骤序列可以在任一端通过一个 [Step] 扩展：逆变（翻转）的参数在序列前添加一个步骤，协变的参数在序列后添加一个步骤。
*)
#[export]
Program Instance multi_respects_Step {Γ τ} :
  Proper (Step --> Step ==> arrow) (multi (Step (Γ:=Γ) (τ:=τ))).
Next Obligation.
  econstructor; eauto.
  generalize dependent y0.
  generalize dependent y.
  induction X; intros; eauto.
  - now do 4 (econstructor; eauto).
  - unfold flip in *.
    now econstructor; eauto.
Qed.

(*
 Likewise a sequence may be extended by whole sub-sequences at either end,
 i.e. multi-step reduction is a congruence for itself (by transitivity). 

 --------
 同样，一个序列可以在任一端通过整个子序列进行扩展，即多步约简对其自身是一个合同（通过传递性）。
*)
#[export]
Program Instance multi_respects_multi `(R : crelation X) :
  Proper (multi R --> multi R ==> arrow) (multi R).
Next Obligation.
  unfold flip in *.
  transitivity x; eauto.
  now transitivity x0; eauto.
Qed.

#[local] Hint Constructors ValueP Step : core.

#[local] Hint Extern 7 (_ ---> _) => repeat econstructor : core.

Local Set Warnings "-intuition-auto-with-star".

(*
 A value is a normal form, so it multi-steps only to itself: any sequence
 out of a value must be the empty (reflexive) one. 

 --------
 一个值是一个规范形式，所以它只会多步归约到它自身：任何从一个值开始的序列必须是空的（自反的）序列。
*)
Corollary values_final {Γ τ} {e e' : Exp Γ τ} :
  e --->* e' → ValueP e → e = e'.
Proof.
  intros.
  apply value_is_nf in H.
  unfold normal_form in H.
  induction X; auto.
  now intuition; auto with *.
Qed.

(*
 Congruence/compatibility lemmas: each lifts a single-step congruence rule
 of [Step] to multi-step reduction, reducing one subterm while the rest of
 the expression stays fixed.  [multistep_AppR] reduces the argument of an
 application whose function is already a value (cf. [ST_AppR]/[AppR_LAM]). 

 --------
 同余/兼容引理：每个引理将  [Step]  的单步同余规则提升到多步化简，通过化简一个子项而保持表达式的其余部分不变。[multistep_AppR] 化简一个应用的参数，该应用的函数已经是一个值（参见 [ST_AppR] / [AppR_LAM]）。
*)
Lemma multistep_AppR {Γ dom cod} {e e' : Γ ⊢ dom} {v : Γ ⊢ (dom ⟶ cod)} :
  (e --->* e') → ValueP v → APP v e --->* APP v e'.
Proof.
  intros.
  induction X.
  - now apply multi_refl.
  - rewrite <- IHX; clear IHX; auto.
    inv H.
    eapply (AppR_LAM (e:=e)) in r.
    now apply multi_R.
Qed.

(*
 Common pattern for the remaining congruence lemmas: induct on the given
 reduction sequence; the reflexive case is immediate, and the step case
 prepends the matching single-step congruence rule (found by [econstructor]). 

 --------
 剩余同余引理的常见模式：对给定的归约序列进行归纳；自反情况是显而易见的，步骤情况则在前面加上匹配的单步同余规则（由 [econstructor] 找到）。
*)
Ltac simpl_multistep :=
  intros;
  match goal with
  | [ H : _ --->* _ |- _ ] => induction H
  end;
  [ now apply multi_refl
  | eapply multi_step; eauto;
    now econstructor; eauto ].

Lemma multistep_Pair1 {Γ τ1 τ2} {e1 e1' : Γ ⊢ τ1} {e2 : Γ ⊢ τ2} :
  (e1 --->* e1') → Pair e1 e2 --->* Pair e1' e2.
Proof. now simpl_multistep. Qed.

Lemma multistep_Pair2 {Γ τ1 τ2} {e1 : Γ ⊢ τ1} {e2 e2' : Γ ⊢ τ2} :
  ValueP e1 → (e2 --->* e2') → Pair e1 e2 --->* Pair e1 e2'.
Proof. now simpl_multistep. Qed.

(* Reduce both components of a pair: first the left to a value [e1'] (via [multistep_Pair1]), then the right (via [multistep_Pair2], whose [ST_Pair2] rule requires the left component to already be a value). / 减少一对的两个组件：首先将左侧减少到值 [e1']（通过 [multistep_Pair1]），然后减少右侧（通过 [multistep_Pair2]，其 [ST_Pair2] 规则要求左侧组件已是一个值）。 *)
Lemma multistep_Pair {Γ τ1 τ2} {e1 e1' : Γ ⊢ τ1} {e2 e2' : Γ ⊢ τ2} :
  ValueP e1' →
  (e1 --->* e1') → (e2 --->* e2') → Pair e1 e2 --->* Pair e1' e2'.
Proof.
  intros.
  erewrite multistep_Pair1; eauto.
  erewrite multistep_Pair2; eauto.
  now apply multi_refl.
Qed.

Lemma multistep_Fst1 {Γ τ1 τ2} {p p' : Γ ⊢ (τ1 × τ2)} :
  (p --->* p') → Fst p --->* Fst p'.
Proof. now simpl_multistep. Qed.

Lemma multistep_Snd1 {Γ τ1 τ2} {p p' : Γ ⊢ (τ1 × τ2)} :
  (p --->* p') → Snd p --->* Snd p'.
Proof. now simpl_multistep. Qed.

End Multi.

Notation " t '--->*' t' " := (multi Step t t') (at level 40).
