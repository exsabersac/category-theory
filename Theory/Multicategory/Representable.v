Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Braided.Proofs.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Multicategory.
Require Import Category.Construction.ColouredPROP.

From Coq Require Import Lists.List.
From Coq Require Import Eqdep_dec.
Import ListNotations.

Generalizable All Variables.

(** * The representable multicategory of a symmetric monoidal category / * 对称单体范畴的可表示多重范畴 *)

(*
nLab: https://ncatlab.org/nlab/show/representable+multicategory

   Every symmetric monoidal category [C] carries a multicategory whose
   multimorphisms [Γ → c] are the ordinary morphisms
   [tensor_list Γ ~> c] out of the right-nested tensor fold of the
   source context.  Splicing ([mcomp]) tensors the argument into its
   slot through the coherence isomorphism
   [tensor_list (Γ ++ Δ) ≅ tensor_list Γ ⨂ tensor_list Δ], and the
   symmetric-group action is precomposition with a braiding-built
   realization of the permutation.

   The whole construction is developed once over an object realization
   [ob : A → C] of an abstract colour type [A], so that the same
   development yields both the representable multicategory proper
   ([A := obj C], [ob] the identity) and the multicategory of a
   coloured PROP ([A := Colour], [ob := wire]) with no duplication.

   Hypothesis note.  The instances are stated over a SYMMETRIC monoidal
   base — the mathematical headline, per the work order — but the proofs
   below consume only the braided structure and the [braid] morphism
   itself (no naturality, no involution, no hexagon).  This mirrors the
   SCOPE note of Theory/Multicategory.v: the class's witness-indexed
   symmetric action does not require symmetric-group descent, and the
   braid involution is exactly what the descent law would consume if a
   later phase adds it as a field.

--------
nLab：https://ncatlab.org/nlab/show/representable+multicategory

每个对称单体范畴 [C] 都携带一个多范畴，其多态态 [Γ → c] 是从源上下文的右嵌套张量折叠中得到的普通态射 [tensor_list Γ ~> c]。拼接 ([mcomp]) 通过相容同构 [tensor_list (Γ ++ Δ) ≅ tensor_list Γ ⨂ tensor_list Δ] 将参数张量化到其位置上，对称群作用是通过先前组合的排列实现的编织态射的前合成。

整个构造是针对一个抽象颜色类型 [A] 的对象实现 [ob : A → C] 一次性开发的，因此相同的开发既产生可表示的多重范畴本身（[A := obj C]、[ob] 恒等）又产生没有重复的彩色 PROP 的多重范畴（[A := Colour]、[ob := wire]）。

假设说明。实例是在对称单体基础上说明的——按照工作单的数学标题——但下面的证明仅利用了编织结构和 [braid] 态射本身（没有自然性、没有反演、没有六边形）。这反映了 Theory/Multicategory.v 的 SCOPE 注释：该类的见证索引对称作用不需要对称群下降，而编织反演正是如果后期阶段将其作为字段添加时，下降律将会使用的内容。
*)

(** ** The tensor fold / ** 张量折叠 *)

(**
The right fold of the tensor over the unit: the object realization
    of a source context.  This is the [cprop_tensor_app] pattern of
    Construction/ColouredPROP.v, valued in an arbitrary (non-strict)
    monoidal category, so concatenation is reflected by a coherence
    ISOMORPHISM rather than an equality.

--------
张量在单位上的右折叠：源上下文的对象实现。这是 Construction/ColouredPROP.v 的 [cprop_tensor_app] 模式，其取值在任意（非严格）单范畴中，因此连接是通过相干同构（ISOMORPHISM）而不是等式来体现的。
*)
Definition tensor_list {C : Category} `{M : @Monoidal C} (xs : list C) : C :=
  fold_right (fun a acc => (a ⨂ acc)%object) I xs.

Section RepresentableKit.

Context {C : Category}.
Context `{M : @Monoidal C}.
Context {A : Type}.
Context (ob : A → C).

(**
The tensor fold over an abstract colour type, through the object
    realization [ob].

--------
通过对象实现 [ob]，对抽象颜色类型进行张量折叠。
*)
Definition tfold : list A → C :=
  fold_right (fun a acc => (ob a ⨂ acc)%object) I.

(** ** The concatenation isomorphism, in both directions / ** 连接同构，在两个方向上 *)

Fixpoint tfold_app_to (Γ Δ : list A) :
  tfold (Γ ++ Δ) ~{C}~> (tfold Γ ⨂ tfold Δ)%object :=
  match Γ with
  | [] => unit_left⁻¹
  | a :: Γ' => tensor_assoc⁻¹ ∘ (id[ob a] ⨂ tfold_app_to Γ' Δ)
  end.

Fixpoint tfold_app_from (Γ Δ : list A) :
  (tfold Γ ⨂ tfold Δ)%object ~{C}~> tfold (Γ ++ Δ) :=
  match Γ with
  | [] => unit_left
  | a :: Γ' => (id[ob a] ⨂ tfold_app_from Γ' Δ) ∘ tensor_assoc
  end.

Lemma tfold_app_from_to (Γ Δ : list A) :
  tfold_app_from Γ Δ ∘ tfold_app_to Γ Δ ≈ id.
Proof.
  induction Γ as [| a Γ IH]; simpl.
  - apply iso_to_from.
  - rewrite <- !comp_assoc.
    rewrite (comp_assoc tensor_assoc).
    rewrite iso_to_from, id_left.
    rewrite <- bimap_comp.
    rewrite id_left, IH.
    apply bimap_id_id.
Qed.

Lemma tfold_app_to_from (Γ Δ : list A) :
  tfold_app_to Γ Δ ∘ tfold_app_from Γ Δ ≈ id.
Proof.
  induction Γ as [| a Γ IH]; simpl.
  - apply iso_from_to.
  - rewrite <- !comp_assoc.
    rewrite (comp_assoc (id[ob a] ⨂ tfold_app_to Γ Δ)).
    rewrite <- bimap_comp.
    rewrite id_left, IH.
    rewrite bimap_id_id, id_left.
    apply iso_from_to.
Qed.

(** The two directions packaged as an isomorphism. / 两个方向被包装为同构。 *)
Program Definition tfold_app (Γ Δ : list A) :
  tfold (Γ ++ Δ) ≅ (tfold Γ ⨂ tfold Δ)%object := {|
  to := tfold_app_to Γ Δ;
  from := tfold_app_from Γ Δ
|}.
Next Obligation. apply tfold_app_to_from. Qed.
Next Obligation. apply tfold_app_from_to. Qed.

(**
** Boundary casts on the fold

    [tcast e] is the identity morphism transported along a propositional
    equality of colour lists (Type-level object data, per the hom_cast
    discipline cited in Theory/Multicategory.v).  Lemmas quantified over
    equalities with at least one free endpoint hold by [destruct]; the
    loop-collapse lemma [tcast_loop] instead consumes the uniqueness of
    list equality proofs [luip] supplied to the construction, exactly as
    the UIP-dependent layer of Construction/ColouredPROP/Cast.v consumes
    its colour decider.

--------
** 折叠上的边界投射

[tcast e] 是沿着颜色列表的命题等式传输的恒等变换（类型级对象数据，按照 Theory/Multicategory.v 中引用的 hom_cast 规程）。在至少有一个自由端点的等式上量化的引理由 [destruct] 保持；而循环坍缩引理 [tcast_loop] 则消耗构造提供的列表等式证明 [luip] 的唯一性，正如 Construction/ColouredPROP/Cast.v 中依赖 UIP 的层消耗其颜色判定器一样。
*)

Definition tcast {Γ Δ : list A} (e : Γ = Δ) : tfold Γ ~{C}~> tfold Δ :=
  match e with eq_refl => id end.

Lemma tcast_trans {Γ Δ Λ : list A} (e : Γ = Δ) (e' : Δ = Λ) :
  tcast e' ∘ tcast e ≈ tcast (eq_trans e e').
Proof. destruct e, e'; simpl; apply id_left. Qed.

Lemma tcast_cons (x : A) {Γ Δ : list A} (e : Γ = Δ) :
  tcast (f_equal (cons x) e) ≈ id[ob x] ⨂ tcast e.
Proof. destruct e; simpl; symmetry; apply bimap_id_id. Qed.

Context (luip : ∀ (Γ Δ : list A) (p q : Γ = Δ), p = q).

Lemma tcast_irr {Γ Δ : list A} (p q : Γ = Δ) : tcast p ≈ tcast q.
Proof using luip. rewrite (luip _ _ p q); reflexivity. Qed.

Lemma tcast_loop {Γ : list A} (e : Γ = Γ) : tcast e ≈ id.
Proof using luip. rewrite (luip _ _ e eq_refl); reflexivity. Qed.

(**
** The splice map

    [msplice Γ1 g] realizes single-slot composition on source contexts:
    it rewrites the [b]-slot of the zipper [(Γ1, b, Γ2)] by the argument
    [g : tfold Δ ~> ob b], leaving the blocks alone.  Defined by
    recursion on the prefix [Γ1], so that every law about it is an
    induction with a one-line cons step.

--------
** splice 映射

[msplice Γ1 g] 在源上下文上实现单槽组合：它将拉链 [(Γ1, b, Γ2)] 的 [b] 槽重写为参数 [g : tfold Δ ~> ob b]，同时保持块不变。定义是通过对前缀 [Γ1] 的递归，因此关于它的每条定律都是带有一行 cons 步的归纳。
*)

Fixpoint msplice (Γ1 : list A) {Γ2 Δ : list A} {b : A}
  (g : tfold Δ ~{C}~> ob b) :
  tfold (Γ1 ++ Δ ++ Γ2) ~{C}~> tfold (Γ1 ++ b :: Γ2) :=
  match Γ1 with
  | [] => (g ⨂ id[tfold Γ2]) ∘ tfold_app_to Δ Γ2
  | a :: Γ1' => id[ob a] ⨂ msplice Γ1' g
  end.

(**
** Unit coherence

    The two lemmas feeding the unit laws of the multicategory: folding
    away an empty suffix is the boundary cast, and splicing the unitor
    into a slot is the identity.

--------
** 单元一致性

    为多重范畴的单元定律提供支撑的两个引理：折叠掉空后缀是边界投射，将单位元splice到槽中是恒等式。
*)

(**
Folding an empty suffix away: the right unitor against the
    concatenation map is the cast along [Δ ++ [] = Δ], for any proof of
    that boundary equation.

--------
折叠一个空后缀：对连接映射而言，右单位子是沿 [Δ ++ [] = Δ] 的转换，对于该边界方程的任何证明都是如此。
*)
Lemma tfold_nil_r (Δ : list A) (e : Δ ++ [] = Δ) :
  unit_right ∘ tfold_app_to Δ [] ≈ tcast e.
Proof using luip.
  induction Δ as [| a Δ IH]; simpl.
  - rewrite tcast_loop.
    rewrite <- unit_identity.
    apply iso_to_from.
  - rewrite (luip _ _ e (f_equal (cons a) (app_nil_r Δ))).
    rewrite tcast_cons.
    rewrite comp_assoc.
    rewrite <- triangle_identity_right.
    rewrite <- bimap_comp.
    rewrite id_left.
    now rewrite (IH (app_nil_r Δ)).
Qed.

(**
Splicing the identity multimorphism (the right unitor on a
    singleton context) into any slot is the identity: the core of the
    right unit law.  Both endpoints are definitionally equal, since
    [Γ1 ++ [b] ++ Γ2] and [Γ1 ++ b :: Γ2] are convertible.

--------
将恒等多态同态（单例上下文上的右单位元）拼接到任何位置都是恒等：右单位律的核心。两个端点在定义上是相等的，因为 [Γ1 ++ [b] ++ Γ2] 和 [Γ1 ++ b :: Γ2] 是可转换的。
*)
Lemma msplice_mid (Γ1 : list A) {Γ2 : list A} (b : A) :
  msplice Γ1 (Γ2:=Γ2) (Δ:=[b]) (b:=b) (to (@unit_right C _ (ob b))) ≈ id.
Proof.
  induction Γ1 as [| a Γ1 IH]; simpl.
  - rewrite comp_assoc.
    rewrite <- inverse_triangle_identity.
    rewrite <- bimap_comp.
    rewrite id_left, iso_to_from.
    apply bimap_id_id.
  - rewrite IH.
    apply bimap_id_id.
Qed.

(**
** Associativity coherence

    How the concatenation map interacts with a triple split: folding
    [x ++ y ++ z] by way of [(x ++ y) ++ z] or by way of
    [x ++ (y ++ z)] agrees up to the associator.  This is the
    pentagon-powered core of the file; every associativity law of the
    multicategory reduces to it.

--------
** 结合性一致性

    连接映射如何与三重拆分交互：通过 [(x ++ y) ++ z] 或者通过 [x ++ (y ++ z)] 对 [x ++ y ++ z] 进行折叠，结果在结合子下是一致的。这是文件的五边形驱动核心；多重范畴的每一个结合性律都可归约到它。
*)

Lemma tfold_app_assoc (x y z : list A) (e : x ++ y ++ z = (x ++ y) ++ z) :
  (tfold_app_to x y ⨂ id[tfold z]) ∘ tfold_app_to (x ++ y) z ∘ tcast e
    ≈ tensor_assoc⁻¹ ∘ (id[tfold x] ⨂ tfold_app_to y z)
        ∘ tfold_app_to x (y ++ z).
Proof using luip.
  revert e; induction x as [| a x IH]; intros e; simpl.
  - (*
Empty prefix: the boundary equation is a loop, and the goal is
       the inverse form of Kelly's left-unitor triangle.

--------
空前缀：边界方程是一个循环，目标是凯利的左单位三角形的逆形式。
*)
    rewrite tcast_loop, id_right.
    rewrite <- comp_assoc.
    rewrite from_unit_left_natural.
    rewrite comp_assoc.
    rewrite <- triangle_inverse_left.
    rewrite comp_assoc.
    rewrite iso_from_to, id_left.
    reflexivity.
  - (*
Cons step: slide the head object out of every factor and apply
       the inverse pentagon identity.

--------
反向步骤：将头部对象从每个因子中滑出，并应用逆五边形恒等式。
*)
    rewrite (luip _ _ e (f_equal (cons a) (app_assoc x y z))).
    rewrite tcast_cons.
    rewrite bimap_comp_id_right.
    rewrite <- !comp_assoc.
    rewrite from_assoc_nat_cons.
    rewrite bimap_id_fuse_cons.
    rewrite bimap_id_fuse.
    rewrite (IH (app_assoc x y z)).
    rewrite from_assoc_nat_id2_cons.
    rewrite <- 2!bimap_id_fuse.
    rewrite !comp_assoc.
    now rewrite inverse_pentagon_identity.
Qed.

(** [tfold_app_assoc], re-bracketed for right-nested rewriting. / [tfold_app_assoc]，重新加括号以进行右嵌套重写。 *)
Lemma tfold_app_assoc_cons (x y z : list A)
  (e : x ++ y ++ z = (x ++ y) ++ z) :
  (tfold_app_to x y ⨂ id[tfold z]) ∘ (tfold_app_to (x ++ y) z ∘ tcast e)
    ≈ tensor_assoc⁻¹
        ∘ ((id[tfold x] ⨂ tfold_app_to y z) ∘ tfold_app_to x (y ++ z)).
Proof using luip.
  rewrite !comp_assoc.
  apply tfold_app_assoc.
Qed.

(**
Peeling a shared head colour off a boundary cast, for an ARBITRARY
    proof between cons-shaped endpoints: the tail equation is recovered
    transparently as [f_equal tl].

--------
从边界投射上剥离共享的头部颜色，对于在构造成的端点之间的任意证明：尾部方程被透明地恢复为 [f_equal tl]。
*)
Lemma tcast_cons_any (x : A) {Γ Δ : list A} (e : x :: Γ = x :: Δ) :
  tcast e ≈ id[ob x] ⨂ tcast (f_equal (@tl A) e).
Proof using luip.
  transitivity (tcast (f_equal (cons x) (f_equal (@tl A) e))).
  - apply tcast_irr.
  - apply tcast_cons.
Qed.

(**
** Splice-versus-fold coherence

    The two ways a splice can sit against the concatenation map: the
    slot inside the block being folded off (the NESTED shape), and the
    slot beyond the block being folded off (the DISJOINT shape).  Both
    are stated over arbitrary proofs of their boundary equations.

--------
** 拼接与折叠的一致性

拼接可以在连接映射上存在的两种方式：折叠块内部的槽（嵌套形态），以及折叠块之外的槽（分离形态）。两者都基于其边界方程的任意证明来说明。
*)

(**
Nested shape: folding [Γ2] off a context whose remaining prefix
    contains the slot.  The spliced argument [h] rides inside the left
    tensor factor.

--------
嵌套形状：将 [Γ2] 从其剩余前缀包含该槽的上下文中折叠。拼接的参数 [h] 位于左张量因子内部。
*)
Lemma msplice_fold {Δ1 Δ2 Γ2 Θ : list A} {a : A}
  (h : tfold Θ ~{C}~> ob a)
  (u : Δ1 ++ a :: Δ2 ++ Γ2 = (Δ1 ++ a :: Δ2) ++ Γ2)
  (v : Δ1 ++ Θ ++ Δ2 ++ Γ2 = (Δ1 ++ Θ ++ Δ2) ++ Γ2) :
  tfold_app_to (Δ1 ++ a :: Δ2) Γ2 ∘ tcast u ∘ msplice Δ1 (Γ2:=Δ2 ++ Γ2) h
    ≈ (msplice Δ1 (Γ2:=Δ2) h ⨂ id[tfold Γ2])
        ∘ tfold_app_to (Δ1 ++ Θ ++ Δ2) Γ2 ∘ tcast v.
Proof using luip.
  revert u v; induction Δ1 as [| d Δ1 IH]; intros u v; simpl.
  - (*
Slot at the head: reduce to [tfold_app_assoc] on [Θ], [Δ2], [Γ2]
       and slide [h] across the associator.

--------
头部的槽：在 [Θ]、[Δ2]、[Γ2] 上减少到 [tfold_app_assoc]，并将 [h] 滑过联结器。
*)
    rewrite tcast_loop, id_right.
    rewrite bimap_comp_id_right.
    rewrite <- !comp_assoc.
    rewrite bimap_fuse_cons.
    rewrite id_left, id_right.
    rewrite (tfold_app_assoc_cons Θ Δ2 Γ2 v).
    rewrite from_assoc_nat_cons.
    rewrite bimap_id_id.
    rewrite bimap_fuse_cons.
    rewrite id_left, id_right.
    reflexivity.
  - (*
Cons step: every factor is [id ⨂ -]; fuse, apply the induction
       hypothesis, and unfuse.

--------
Cons 步骤：每个因子都是 [id ⨂ -]；融合，应用归纳假设，然后解除融合。
*)
    rewrite (tcast_cons_any d u), (tcast_cons_any d v).
    rewrite <- !comp_assoc.
    rewrite bimap_id_fuse_cons.
    rewrite bimap_id_fuse.
    rewrite (IH (f_equal (@tl A) u) (f_equal (@tl A) v)).
    rewrite from_assoc_nat_cons.
    rewrite bimap_id_fuse_cons.
    rewrite bimap_id_fuse.
    reflexivity.
Qed.

(**
Disjoint shape: folding a prefix [Δ] off a context whose slot lies
    beyond it.  The spliced argument [h] rides inside the right tensor
    factor.

--------
不相交的形状：将前缀 [Δ] 从其槽位位于其之后的上下文中折叠。拼接的参数 [h] 位于右张量因子内。
*)
Lemma mfold_msplice {Δ Γ2 Γ3 Θ : list A} {b : A}
  (h : tfold Θ ~{C}~> ob b)
  (u : (Δ ++ Γ2) ++ b :: Γ3 = Δ ++ Γ2 ++ b :: Γ3)
  (v : (Δ ++ Γ2) ++ Θ ++ Γ3 = Δ ++ Γ2 ++ Θ ++ Γ3) :
  tfold_app_to Δ (Γ2 ++ b :: Γ3) ∘ tcast u ∘ msplice (Δ ++ Γ2) (Γ2:=Γ3) h
    ≈ (id[tfold Δ] ⨂ msplice Γ2 (Γ2:=Γ3) h)
        ∘ tfold_app_to Δ (Γ2 ++ Θ ++ Γ3) ∘ tcast v.
Proof using luip.
  revert u v; induction Δ as [| d Δ IH]; intros u v; simpl.
  - rewrite !tcast_loop, !id_right.
    now rewrite from_unit_left_natural.
  - rewrite (tcast_cons_any d u), (tcast_cons_any d v).
    rewrite <- !comp_assoc.
    rewrite bimap_id_fuse_cons.
    rewrite bimap_id_fuse.
    rewrite (IH (f_equal (@tl A) u) (f_equal (@tl A) v)).
    rewrite from_assoc_nat_id2_cons.
    rewrite bimap_id_fuse_cons.
    rewrite bimap_id_fuse.
    reflexivity.
Qed.

(** Splicing respects the setoid of the argument. / 拼接尊重参数的等价类。 *)
Lemma msplice_respects (Γ1 : list A) {Γ2 Δ : list A} {b : A}
  (g g' : tfold Δ ~{C}~> ob b) :
  g ≈ g' → msplice Γ1 (Γ2:=Γ2) g ≈ msplice Γ1 (Γ2:=Γ2) g'.
Proof.
  intros Hg.
  induction Γ1 as [| a Γ1 IH]; simpl.
  - now rewrite Hg.
  - now rewrite IH.
Qed.

(**
** The two associativity cores

    Splice-after-splice in the two shapes of the multicategory
    associativity laws, on the splice maps themselves (the outer
    multimorphism [f] is peeled off by congruence in the instance
    obligations).

--------
** 两个结合性核

在多类的两种多分类结合性定律的形状中，接合后接合，在接合映射本身上（外部多态射 [f] 在实例义务中通过合同被剥离）。
*)

(**
Nested shape: the second slot lies INSIDE the context spliced by
    the first.

--------
嵌套形状：第二个插槽位于由第一个拼接的上下文内部。
*)
Lemma msplice_nested {Γ1 Γ2 Δ1 Δ2 Θ : list A} {a b : A}
  (g : tfold (Δ1 ++ a :: Δ2) ~{C}~> ob b) (h : tfold Θ ~{C}~> ob a)
  (u : (Γ1 ++ Δ1) ++ a :: Δ2 ++ Γ2 = Γ1 ++ (Δ1 ++ a :: Δ2) ++ Γ2)
  (v : (Γ1 ++ Δ1) ++ Θ ++ Δ2 ++ Γ2 = Γ1 ++ (Δ1 ++ Θ ++ Δ2) ++ Γ2) :
  msplice Γ1 (Γ2:=Γ2) g ∘ tcast u ∘ msplice (Γ1 ++ Δ1) (Γ2:=Δ2 ++ Γ2) h
    ≈ msplice Γ1 (Γ2:=Γ2) (g ∘ msplice Δ1 (Γ2:=Δ2) h) ∘ tcast v.
Proof using luip.
  revert u v; induction Γ1 as [| a' Γ1 IH]; intros u v; simpl.
  - rewrite bimap_comp_id_right.
    rewrite <- !comp_assoc.
    comp_left.
    rewrite !comp_assoc.
    apply msplice_fold.
  - rewrite (tcast_cons_any a' u), (tcast_cons_any a' v).
    rewrite <- !comp_assoc.
    rewrite bimap_id_fuse_cons.
    rewrite !bimap_id_fuse.
    now rewrite IH.
Qed.

(** [mfold_msplice], re-bracketed for right-nested rewriting. / [mfold_msplice]，重新加括号以进行右嵌套重写。 *)
Lemma mfold_msplice_cons {Δ Γ2 Γ3 Θ : list A} {b : A}
  (h : tfold Θ ~{C}~> ob b)
  (u : (Δ ++ Γ2) ++ b :: Γ3 = Δ ++ Γ2 ++ b :: Γ3)
  (v : (Δ ++ Γ2) ++ Θ ++ Γ3 = Δ ++ Γ2 ++ Θ ++ Γ3) :
  tfold_app_to Δ (Γ2 ++ b :: Γ3)
      ∘ (tcast u ∘ msplice (Δ ++ Γ2) (Γ2:=Γ3) h)
    ≈ (id[tfold Δ] ⨂ msplice Γ2 (Γ2:=Γ3) h)
        ∘ (tfold_app_to Δ (Γ2 ++ Θ ++ Γ3) ∘ tcast v).
Proof using luip.
  rewrite !comp_assoc.
  apply mfold_msplice.
Qed.

(**
Disjoint shape: the two slots lie in the same outer context, the
    [a]-slot before the [b]-slot.

--------
不相交的形状：这两个槽位于相同的外部上下文中，[a] 槽位在 [b] 槽位之前。
*)
Lemma msplice_disjoint {Γ1 Γ2 Γ3 Δ Θ : list A} {a b : A}
  (g : tfold Δ ~{C}~> ob a) (h : tfold Θ ~{C}~> ob b)
  (u : (Γ1 ++ Δ ++ Γ2) ++ b :: Γ3 = Γ1 ++ Δ ++ Γ2 ++ b :: Γ3)
  (v : (Γ1 ++ a :: Γ2) ++ b :: Γ3 = Γ1 ++ a :: Γ2 ++ b :: Γ3)
  (w : Γ1 ++ a :: Γ2 ++ Θ ++ Γ3 = (Γ1 ++ a :: Γ2) ++ Θ ++ Γ3)
  (s : (Γ1 ++ Δ ++ Γ2) ++ Θ ++ Γ3 = Γ1 ++ Δ ++ Γ2 ++ Θ ++ Γ3) :
  msplice Γ1 (Γ2:=Γ2 ++ b :: Γ3) g ∘ tcast u
      ∘ msplice (Γ1 ++ Δ ++ Γ2) (Γ2:=Γ3) h
    ≈ tcast v ∘ msplice (Γ1 ++ a :: Γ2) (Γ2:=Γ3) h ∘ tcast w
        ∘ msplice Γ1 (Γ2:=Γ2 ++ Θ ++ Γ3) g ∘ tcast s.
Proof using luip.
  revert u v w s; induction Γ1 as [| a' Γ1 IH]; intros u v w s; simpl.
  - rewrite !tcast_loop, id_left, id_right.
    rewrite <- !comp_assoc.
    rewrite (mfold_msplice_cons (Δ:=Δ) (Γ2:=Γ2) (Γ3:=Γ3) h u s).
    rewrite !bimap_fuse_cons.
    rewrite !id_left, !id_right.
    reflexivity.
  - rewrite (tcast_cons_any a' u), (tcast_cons_any a' v),
      (tcast_cons_any a' w), (tcast_cons_any a' s).
    rewrite <- !comp_assoc.
    rewrite !bimap_id_fuse_cons.
    rewrite !bimap_id_fuse.
    now rewrite IH.
Qed.

(**
** The block form of the splice

    The splice map conjugated into three tensor blocks: the prefix
    rides as an identity factor, and the argument acts on the middle
    block against the fold of the suffix.  This is the bridge between
    the recursive definition of [msplice] and blockwise reasoning, and
    it is what the equivariance law reduces to.

--------
** 拼接的块形式

拼接映射被卷积成三个张量块：前缀作为恒等因子，参数作用于中间块，对后缀的折叠进行操作。这是[msplice]递归定义与分块推理之间的桥梁，也是等变律的简化形式。
*)
Lemma msplice_block (Γ1 : list A) {Γ2 Δ : list A} {b : A}
  (g : tfold Δ ~{C}~> ob b) :
  msplice Γ1 (Γ2:=Γ2) g
    ≈ tfold_app_from Γ1 (b :: Γ2)
        ∘ (id[tfold Γ1] ⨂ ((g ⨂ id[tfold Γ2]) ∘ tfold_app_to Δ Γ2))
        ∘ tfold_app_to Γ1 (Δ ++ Γ2).
Proof.
  induction Γ1 as [| a Γ1 IH]; simpl.
  - rewrite <- comp_assoc.
    rewrite from_unit_left_natural.
    rewrite comp_assoc.
    rewrite iso_to_from, id_left.
    reflexivity.
  - rewrite IH.
    rewrite <- !comp_assoc.
    rewrite to_assoc_nat_id2_cons.
    rewrite (comp_assoc tensor_assoc).
    rewrite iso_to_from, id_left.
    rewrite !bimap_id_fuse_cons.
    rewrite bimap_id_fuse.
    now rewrite !comp_assoc.
Qed.

End RepresentableKit.

(**
The concatenation isomorphism at the identity realization: the form
    stated for [tensor_list] itself.

--------
在恒等实现下的串联同构：针对 [tensor_list] 本身所述的形式。
*)
Definition tensor_list_app {C : Category} `{M : @Monoidal C}
  (xs ys : list C) :
  tensor_list (xs ++ ys) ≅ (tensor_list xs ⨂ tensor_list ys)%object :=
  tfold_app (fun x => x) xs ys.

(**
** Swap-versus-fold coherence

    The purely monoidal square exchanging an adjacent transposition of
    the two head factors with a fold of the tail: [m] is a GENERIC
    morphism [x ⨂ y ~> y ⨂ x] (in use, the braiding), conjugated by
    associators on either side of a generic tail map [w].  Only
    associator naturality and the pentagon enter — no braiding
    coherence.  This is the swap case of the realization lemmas
    below.

--------
** 交换与折叠的相干性

纯粹的幺半群方形将两个首因子相邻的换位与尾部的折叠交换：[m] 是一个 GENERIC 同态 [x ⨂ y ~> y ⨂ x]（使用时为交换子），在通用尾映射 [w] 的两侧由结合子共轭。只有结合子的自然性和五边形公理生效——没有交换子相干性。这是下面实现引理的交换情况。
*)

Section SwapFold.

Context {C : Category}.
Context `{M : @Monoidal C}.

(** The inverse pentagon identity against a continuation. / 关于延续的逆五边形恒等式。 *)
Lemma inverse_pentagon_cons {x y z w t : C}
  (k : t ~> (x ⨂ (y ⨂ (z ⨂ w)))%object) :
  (tensor_assoc⁻¹ ⨂ id[w])
      ∘ (tensor_assoc⁻¹ ∘ ((id[x] ⨂ tensor_assoc⁻¹) ∘ k))
    ≈ tensor_assoc⁻¹ ∘ (tensor_assoc⁻¹ ∘ k).
Proof.
  rewrite !comp_assoc.
  comp_right.
  apply inverse_pentagon_identity.
Qed.

Lemma swap_fold_coherence {x y L G Z : C}
  (m : (x ⨂ y)%object ~> (y ⨂ x)%object) (w : Z ~> (L ⨂ G)%object) :
  tensor_assoc⁻¹ ∘ (id[y] ⨂ (tensor_assoc⁻¹ ∘ (id[x] ⨂ w)))
      ∘ tensor_assoc ∘ (m ⨂ id[Z]) ∘ tensor_assoc⁻¹
    ≈ ((tensor_assoc ∘ (m ⨂ id[L]) ∘ tensor_assoc⁻¹) ⨂ id[G])
        ∘ (tensor_assoc⁻¹ ∘ (id[x] ⨂ (tensor_assoc⁻¹ ∘ (id[y] ⨂ w)))).
Proof.
  assert (Hsplit : m ⨂ w
    ≈ (m ⨂ id[(L ⨂ G)%object]) ∘ (id[(x ⨂ y)%object] ⨂ w))
    by (rewrite <- bimap_comp; now rewrite id_right, id_left).
  assert (Hslide : (id[(x ⨂ y)%object] ⨂ w) ∘ tensor_assoc⁻¹
    ≈ tensor_assoc⁻¹ ∘ (id[x] ⨂ (id[y] ⨂ w))).
  { pose proof (from_tensor_assoc_natural (id[x]) (id[y]) w) as X.
    rewrite bimap_id_id in X.
    exact X. }
  (* Split the compound tensor factors on both sides. / 将两边的复合张量因子拆开。 *)
  rewrite <- !bimap_id_fuse.
  rewrite !bimap_comp_id_right.
  rewrite <- !comp_assoc.
  (* Left side: slide the tail map [w] to the right end. / 左侧：将尾部地图 [w] 滑动到右端。 *)
  rewrite (to_assoc_nat_cons (id[y]) (id[x]) w).
  rewrite bimap_id_id.
  rewrite bimap_fuse_cons.
  rewrite id_left, id_right.
  rewrite Hsplit.
  rewrite <- !comp_assoc.
  rewrite Hslide.
  (*
Right side: collapse the padded associators by the inverse
     pentagon, slide [m] across the associator, and close with the
     solved pentagon.

--------
右侧：通过逆五边形折叠带衬垫的结合元件，将 [m] 滑过结合元件，然后用已解决的五边形关闭。
*)
  rewrite inverse_pentagon_cons.
  rewrite (from_assoc_nat_cons m (id[L]) (id[G])).
  rewrite bimap_id_id.
  rewrite <- pentagon_from_solved_cons.
  reflexivity.
Qed.

End SwapFold.

(**
** Realizing permutations by braidings

    [perm_arrow p] realizes a structural permutation as a morphism
    between the folds, CONTRAVARIANTLY: the action on multimorphisms is
    precomposition.  Skips tensor an identity on the head, adjacent
    swaps conjugate the braiding by associators, and transitivity
    composes.

--------
** 通过编织实现置换

[perm_arrow p] 将一个结构置换实现为折叠之间的态射，以逆变方式：对多重态射的作用是前置组合。跳过张量在头部取单位，邻近交换通过结合子共轭编织，传递性则进行组合。
*)

Section Realization.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.
Context {A : Type}.
Context (ob : A → C).

Fixpoint perm_arrow {Γ Δ : list A} (p : tperm Γ Δ) :
  tfold ob Δ ~{C}~> tfold ob Γ :=
  match p with
  | tperm_nil => id
  | tperm_skip x q => id[ob x] ⨂ perm_arrow q
  | tperm_swap x y Γ' =>
      tensor_assoc ∘ (braid ⨂ id[tfold ob Γ']) ∘ tensor_assoc⁻¹
  | tperm_trans q r => perm_arrow q ∘ perm_arrow r
  end.

(** The canonical reflexivity permutation acts trivially. / 典型自反排列的作用是平凡的。 *)
Lemma perm_arrow_refl (Γ : list A) :
  perm_arrow (tperm_refl Γ) ≈ id.
Proof.
  induction Γ as [| x Γ IH]; simpl.
  - reflexivity.
  - rewrite IH; apply bimap_id_id.
Qed.

(**
The skip constructor realizes as an identity tensor factor
    (definitional; named for rewriting).

--------
跳过构造函数被实现为一个单位张量因子（定义性的；因重写而得名）。
*)
Lemma perm_arrow_skip (x : A) {Γ Δ : list A} (q : tperm Γ Δ) :
  perm_arrow (tperm_skip x q) ≈ id[ob x] ⨂ perm_arrow q.
Proof. reflexivity. Qed.

(**
Right padding in fold coordinates: the realization of
    [tperm_app_l p Λ] is [perm_arrow p] on the left tensor factor.

--------
折叠坐标中的右填充：[tperm_app_l p Λ] 的实现是在左张量因子上的 [perm_arrow p]。
*)
Lemma perm_arrow_app_l {Γ Δ : list A} (p : tperm Γ Δ) (Λ : list A) :
  tfold_app_to ob Γ Λ ∘ perm_arrow (tperm_app_l p Λ)
    ≈ (perm_arrow p ⨂ id[tfold ob Λ]) ∘ tfold_app_to ob Δ Λ.
Proof.
  induction p as [| x Γ' Δ' q IH | x y Γ' | Γ' Δ' Λ' q IH1 r IH2]; simpl.
  - rewrite perm_arrow_refl, id_right.
    now rewrite bimap_id_id, id_left.
  - rewrite <- !comp_assoc.
    rewrite bimap_id_fuse.
    rewrite IH.
    rewrite <- bimap_id_fuse.
    now rewrite from_assoc_nat_cons.
  - rewrite !comp_assoc.
    rewrite swap_fold_coherence.
    now rewrite !comp_assoc.
  - rewrite comp_assoc.
    rewrite IH1.
    rewrite <- comp_assoc.
    rewrite IH2.
    rewrite comp_assoc.
    now rewrite bimap_fuse_id_right.
Qed.

(**
Left padding in fold coordinates: the realization of
    [tperm_app_r Γ p] is [perm_arrow p] on the right tensor factor.

--------
折叠坐标中的左填充：[tperm_app_r Γ p] 的实现是在右张量因子上的 [perm_arrow p]。
*)
Lemma perm_arrow_app_r (Γ : list A) {Δ Λ : list A} (p : tperm Δ Λ) :
  tfold_app_to ob Γ Δ ∘ perm_arrow (tperm_app_r Γ p)
    ≈ (id[tfold ob Γ] ⨂ perm_arrow p) ∘ tfold_app_to ob Γ Λ.
Proof.
  induction Γ as [| x Γ IH]; simpl.
  - now rewrite from_unit_left_natural.
  - rewrite <- !comp_assoc.
    rewrite bimap_id_fuse.
    rewrite IH.
    rewrite <- bimap_id_fuse.
    now rewrite from_assoc_nat_id2_cons.
Qed.

End Realization.

(**
** Equivariance of the splice

    The interaction of [msplice] with blockwise permutations: the
    prefix, argument, and suffix blocks may be permuted independently,
    and this commutes with splicing.  Everything reduces to the
    padding lemmas above in fold coordinates, plus bimap interchange —
    the blocks never cross the slot, so no braiding coherence beyond
    [perm_arrow_app_l] is needed.

--------
** 拼接的等变性

[msplice] 与分块排列的相互作用：前缀、参数和后缀块可以独立排列，这与拼接操作是可交换的。一切归结于上文折叠坐标中的填充引理，加上双映射交换——块从不跨越槽，因此除了 [perm_arrow_app_l] 之外不需要额外的编织相干性。
*)

Section Equivariance.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.
Context {A : Type}.
Context (ob : A → C).

(**
Cons forms of the padding lemmas, for rewriting inside right-nested
    chains.

--------
用于在右嵌套链中重写的填充引理的Cons形式。
*)
Lemma perm_arrow_app_l_cons {Γ Δ : list A} (p : tperm Γ Δ) (Λ : list A)
  {z : C} (k : z ~> tfold ob (Δ ++ Λ)) :
  tfold_app_to ob Γ Λ ∘ (perm_arrow ob (tperm_app_l p Λ) ∘ k)
    ≈ (perm_arrow ob p ⨂ id[tfold ob Λ]) ∘ (tfold_app_to ob Δ Λ ∘ k).
Proof.
  rewrite !comp_assoc.
  comp_right.
  apply perm_arrow_app_l.
Qed.

(**
Parallel composition across [++], in fold coordinates: the
    realization of [tperm_app p q] is the tensor of the two
    realizations.

--------
在折叠坐标中跨 [++] 的并行组成：[tperm_app p q] 的实现是两个实现的张量。
*)
Lemma perm_arrow_app {Γ Γ' Δ Δ' : list A} (p : tperm Γ Γ') (q : tperm Δ Δ') :
  tfold_app_to ob Γ Δ ∘ perm_arrow ob (tperm_app p q)
    ≈ (perm_arrow ob p ⨂ perm_arrow ob q) ∘ tfold_app_to ob Γ' Δ'.
Proof.
  unfold tperm_app; simpl.
  rewrite perm_arrow_app_l_cons.
  rewrite perm_arrow_app_r.
  rewrite bimap_fuse_cons.
  now rewrite id_left, id_right.
Qed.

(**
[perm_arrow_app] transposed across the concatenation isomorphism,
    against a continuation.

--------
[perm_arrow_app] 在串联同构上转置，针对一个延续。
*)
Lemma perm_arrow_app_from {Γ Γ' Δ Δ' : list A}
  (p : tperm Γ Γ') (q : tperm Δ Δ')
  {z : C} (k : z ~> (tfold ob Γ' ⨂ tfold ob Δ')%object) :
  perm_arrow ob (tperm_app p q) ∘ (tfold_app_from ob Γ' Δ' ∘ k)
    ≈ tfold_app_from ob Γ Δ ∘ ((perm_arrow ob p ⨂ perm_arrow ob q) ∘ k).
Proof.
  rewrite !comp_assoc.
  comp_right.
  rewrite <- (id_left (perm_arrow ob (tperm_app p q))).
  rewrite <- (tfold_app_from_to ob Γ Δ).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (tfold_app_to ob Γ Δ)).
  rewrite perm_arrow_app.
  rewrite <- !comp_assoc.
  rewrite tfold_app_to_from.
  now rewrite id_right.
Qed.

End Equivariance.

(**
** The equivariance core

    Splicing commutes with independent blockwise permutation of the
    prefix, the argument boundary, and the suffix.  Both sides land in
    the same hom-set on the nose, so no boundary cast appears.

--------
** 等变核心

拼接与前缀、参数边界和后缀的独立块状置换是可交换的。两边精确地落在同一个同态集上，因此不会出现边界转换。
*)

Section EquivarianceCore.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.
Context {A : Type}.
Context (ob : A → C).

Lemma msplice_equivariant {Γ1 Γ1' Γ2 Γ2' Δ Δ' : list A} {b : A}
  (p : tperm Γ1 Γ1') (q : tperm Δ Δ') (r : tperm Γ2 Γ2')
  (g : tfold ob Δ ~{C}~> ob b) :
  msplice ob Γ1 (Γ2:=Γ2) g ∘ perm_arrow ob (perm_block3 p q r)
    ≈ perm_arrow ob (perm_block_slot b p r)
        ∘ msplice ob Γ1' (Γ2:=Γ2') (g ∘ perm_arrow ob q).
Proof.
  assert (Harg :
    ((g ⨂ id[tfold ob Γ2]) ∘ tfold_app_to ob Δ Γ2)
        ∘ perm_arrow ob (tperm_app q r)
      ≈ ((g ∘ perm_arrow ob q) ⨂ perm_arrow ob r)
          ∘ tfold_app_to ob Δ' Γ2').
  { rewrite <- comp_assoc.
    rewrite perm_arrow_app.
    rewrite bimap_fuse_cons.
    now rewrite id_left. }
  unfold perm_block3, perm_block_slot.
  rewrite (msplice_block ob Γ1 g).
  rewrite (msplice_block ob Γ1' (g ∘ perm_arrow ob q)).
  rewrite <- !comp_assoc.
  (*
Left side: pull the block realization across the fold, then fold
     the argument block by [Harg].

--------
左侧：将块实现拉到折痕处，然后用 [Harg] 折叠参数块。
*)
  rewrite perm_arrow_app.
  rewrite bimap_fuse_cons.
  rewrite id_left.
  rewrite Harg.
  (*
Right side: transpose the slot realization across [from] and fuse
     the three tensor factors.

--------
右侧：在 [from] 上转置槽实现，并融合三个张量因子。
*)
  rewrite perm_arrow_app_from.
  rewrite bimap_fuse_cons.
  rewrite id_right.
  rewrite perm_arrow_skip.
  rewrite (bimap_fuse_cons (id[ob b]) (perm_arrow ob r)
             (g ∘ perm_arrow ob q) (id[tfold ob Γ2'])
             (tfold_app_to ob Δ' Γ2')).
  now rewrite id_left, id_right.
Qed.

End EquivarianceCore.

(** ** The representable multicategory / ** 可表示的多重范畴 *)

Section Assembly.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.
Context {A : Type}.
Context (ob : A → C).
Context (luip : ∀ (Γ Δ : list A) (p q : Γ = Δ), p = q).

(**
The boundary cast on multimorphisms: hom-side transport along a
    list equality.

--------
施加在多态上的边界：沿列表等式的同态侧传输。
*)
Definition mhcast {Γ Γ' : list A} {c : A} (e : Γ = Γ')
  (f : tfold ob Γ ~{C}~> ob c) : tfold ob Γ' ~{C}~> ob c :=
  match e in _ = Γ0 return tfold ob Γ0 ~{C}~> ob c with
  | eq_refl => f
  end.

(** The hom-side transport is precomposition with the boundary cast. / 同侧传输是与边界映射的预组合。 *)
Lemma mhcast_tcast {Γ Γ' : list A} {c : A} (e : Γ = Γ')
  (f : tfold ob Γ ~{C}~> ob c) :
  mhcast e f ≈ f ∘ tcast ob (eq_sym e).
Proof.
  destruct e; simpl.
  now rewrite id_right.
Qed.

#[local] Obligation Tactic := intros.

(**
Any symmetric monoidal category, realized over a colour type [A],
    yields a multicategory: multimorphisms out of [Γ] are morphisms out
    of the tensor fold of [Γ], composition splices through the
    concatenation isomorphism, and the symmetric action precomposes the
    braiding realization.  The uniqueness of list equality proofs
    [luip] discharges the arbitrary-loop cast laws (Hedberg supplies it
    from a decider; see [ColouredPROP_Multicategory]).

--------
任何对称单体范畴，在颜色类型 [A] 上实现时，会生成一个多重范畴：来自 [Γ] 的多重态射是从 [Γ] 张量折叠出的态射，组合通过连接同构进行拼接，而对称作用则预先组合了交换实现。列表相等证明的唯一性 [luip] 解除任意循环转换规律（Hedberg 从判定器提供它；见 [ColouredPROP_Multicategory]）。
*)
Program Definition Fold_Multicategory : Multicategory := {|
  mobj := A;
  mhom := fun Γ c => tfold ob Γ ~{C}~> ob c;
  mhomset := fun Γ c => @homset C (tfold ob Γ) (ob c);
  mcast := fun Γ Γ' c e => mhcast e;
  mid := fun a => to (@unit_right C _ (ob a));
  mcomp := fun Γ1 Γ2 Δ b c f g => f ∘ msplice ob Γ1 (Γ2:=Γ2) g;
  msym := fun Γ Δ c p f => f ∘ perm_arrow ob p
|}.
Next Obligation.
  (* mcast_respects / mcast_respects *)
  destruct e; repeat intro; assumption.
Qed.
Next Obligation.
  (* mcast_id / 多播ID *)
  rewrite (luip _ _ e eq_refl); reflexivity.
Qed.
Next Obligation.
  (* mcast_trans / 多播传输 *)
  destruct e, e'; reflexivity.
Qed.
Next Obligation.
  (* mcomp_respects / mcomp_尊重 *)
  repeat intro.
  apply compose_respects; [ assumption |].
  now apply msplice_respects.
Qed.
Next Obligation.
  (* mcomp_id_left / mcomp_id_left *)
  rewrite mhcast_tcast; simpl.
  rewrite comp_assoc.
  rewrite <- to_unit_right_natural.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc unit_right (tfold_app_to ob Δ [])).
  rewrite (tfold_nil_r ob luip Δ (app_nil_r Δ)).
  rewrite tcast_trans.
  rewrite (tcast_loop ob luip).
  now rewrite id_right.
Qed.
Next Obligation.
  (* mcomp_id_right / mcomp_id_right *)
  rewrite mhcast_tcast.
  rewrite msplice_mid.
  rewrite (tcast_loop ob luip).
  now rewrite !id_right.
Qed.
Next Obligation.
  (* mcomp_assoc_nested / mcomp_嵌套关联 *)
  cbv beta.
  rewrite !mhcast_tcast.
  rewrite <- !comp_assoc.
  comp_left.
  rewrite !comp_assoc.
  apply (msplice_nested ob luip g h (eq_sym e1) (eq_sym e2)).
Qed.
Next Obligation.
  (* mcomp_assoc_disjoint / mcomp_关联_不相交 *)
  cbv beta.
  rewrite !mhcast_tcast.
  rewrite <- !comp_assoc.
  comp_left.
  rewrite !comp_assoc.
  apply (msplice_disjoint ob luip g h
           (eq_sym d1) (eq_sym d2) (eq_sym d3) (eq_sym d4)).
Qed.
Next Obligation.
  (* msym_respects / msym_尊重 *)
  repeat intro.
  now apply compose_respects.
Qed.
Next Obligation.
  (* msym_id / msym_id *)
  cbv beta.
  rewrite perm_arrow_refl.
  now rewrite id_right.
Qed.
Next Obligation.
  (* msym_compose / msym_组合 *)
  cbv beta; simpl.
  now rewrite comp_assoc.
Qed.
Next Obligation.
  (* mcomp_equivariant / mcomp_等变 *)
  cbv beta.
  rewrite <- !comp_assoc.
  comp_left.
  apply msplice_equivariant.
Qed.

End Assembly.

(**
Every symmetric monoidal category yields a multicategory on its own
    objects: [mhom Γ c := tensor_list Γ ~> c].  The uniqueness of list
    equality proofs on objects is threaded as a hypothesis: the class's
    [mcast_id] is quantified over ARBITRARY loops [e : Γ = Γ], and
    transport along such a loop is provably trivial exactly when
    parallel list equalities are equal — for an arbitrary object type
    this is precisely the fibrewise-UIP discipline of
    Construction/Grothendieck/Strict.v (a decider supplies it by
    Hedberg, as below).

--------
每一个对称单体范畴都会在其自身对象上产生一个多范畴：[mhom Γ c := tensor_list Γ ~> c]。对象上列表等式证明的唯一性作为假设进行传递：该类的 [mcast_id] 在任意循环 [e : Γ = Γ] 上被量化，并且沿着这样的循环的传输在平行列表等式相等时可证显然是平凡的——对于任意对象类型，这正是 Construction/Grothendieck/Strict.v 的纤维化 UIP 规范（Hedberg 提供的判定器，如下所示）。
*)
Definition RepresentableMulticategory (C : Category)
  `{S : @SymmetricMonoidal C}
  (luip : ∀ (Γ Δ : list C) (p q : Γ = Δ), p = q) : Multicategory :=
  Fold_Multicategory (fun x : C => x) luip.

(**
** The multicategory of a coloured PROP

    A coloured PROP is a strict symmetric monoidal category whose
    objects are colour lists, so it realizes its own colours: the
    multicategory has [mobj := Colour] and multimorphisms out of the
    tensor fold of wires.  The colour decider [Cdec] supplies the
    uniqueness of list equality proofs by Hedberg ([UIP_dec], axiom
    free), exactly the decider discipline of the coloured spine
    (Construction/ColouredPROP/Cast.v).

--------
** 有色PROP的多范畴

有色PROP是一个严格对称单体范畴，其对象是颜色列表，因此它实现了自身的颜色：多范畴具有[mobj := Colour]以及从线张量折叠出的多态态射。颜色判定器[Cdec]通过Hedberg定理（[UIP_dec]，无公理）提供了列表相等性证明的唯一性，恰好是有色脊柱的判定器规律（Construction/ColouredPROP/Cast.v）。
*)

(** Uniqueness of list equality proofs from an element decider. / 由元素判定器得到的列表相等证明的唯一性。 *)
Definition list_uip_of_dec {A : Type}
  (dec : ∀ x y : A, {x = y} + {x ≠ y}) :
  ∀ (Γ Δ : list A) (p q : Γ = Δ), p = q :=
  UIP_dec (list_eq_dec dec).

(**
The tensor fold of wires is the canonical colour-list object: the
    strict boundary equalities [cprop_unit_nil]/[cprop_tensor_app]
    collapse the fold (a propositional equality of OBJECTS, the
    sanctioned hom_cast discipline).

--------
线的张量折叠是典型的颜色列表对象：严格的边界等式 [cprop_unit_nil]/[cprop_tensor_app] 折叠了该折叠（对象的命题等式，经批准的 hom_cast 规范）。
*)
Lemma cprop_tfold {Colour : Type} (Q : ColouredPROP Colour)
  (Γ : list Colour) :
  tfold (@wire Colour Q) Γ = cprop_of_list Γ.
Proof.
  induction Γ as [| c Γ IH]; simpl.
  - rewrite <- (cprop_monoidal_coherence Q).
    apply cprop_unit_nil.
  - rewrite IH.
    rewrite <- (cprop_monoidal_coherence Q).
    apply (cprop_tensor_app [c] Γ).
Qed.

(**
The multicategory of a coloured PROP: multimorphisms
    [mhom Γ c ≡ tfold wire Γ ~{Q}~> wire c], where [tfold wire Γ] is
    the object [cprop_of_list Γ] by [cprop_tfold].

--------
有色 PROP 的多范畴：多态射 [mhom Γ c ≡ tfold wire Γ ~{Q}~> wire c]，其中 [tfold wire Γ] 是对象 [cprop_of_list Γ] 通过 [cprop_tfold]。
*)
Definition ColouredPROP_Multicategory {Colour : Type}
  (Q : ColouredPROP Colour)
  (Cdec : ∀ x y : Colour, {x = y} + {x ≠ y}) : Multicategory :=
  @Fold_Multicategory (cprop_cat Q) (cprop_symmetric Q) Colour
    (@wire Colour Q) (list_uip_of_dec Cdec).
