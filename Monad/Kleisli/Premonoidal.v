Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Binoidal.
Require Import Category.Structure.Premonoidal.
Require Import Category.Functor.Strong.
Require Import Category.Monad.Strong.
Require Import Category.Monad.Strong.Symmetric.
Require Import Category.Monad.Kleisli.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

(**
* The Kleisli category of a strong monad is premonoidal

    nLab: https://ncatlab.org/nlab/show/premonoidal+category
    nLab: https://ncatlab.org/nlab/show/strong+monad

    Power–Robinson ("Premonoidal categories and notions of computation",
    Math. Structures Comput. Sci. 7(5), 1997) observed that for a strong
    monad M on a symmetric monoidal category C, the Kleisli category Kl(M)
    carries a canonical premonoidal structure: the tensor of C extends to
    Kl(M) separately in each variable — through the derived right strength
    [rstr] on the left and through the left strength [strength] on the
    right — but not jointly, because the two orders of sequencing a pair of
    effectful computations in general disagree.  This file constructs that
    structure over the library's actual [Kleisli] category
    (Monad/Kleisli.v), in three tiers:

    1. The binoidal structure ([Kleisli_Binoidal]): for each object y' the
       one-variable tensoring functors

           f ↦ rstr ∘ (f ⨂ id[y'])        ([kl_left_fmap],  - ⊗ y')
           f ↦ strength ∘ (id[x'] ⨂ f)    ([kl_right_fmap], x' ⊗ -)

       are Kleisli functors: identity preservation is exactly the η-compat
       laws [rstr_ret] / [strength_ret], and composition preservation is
       exactly the μ-compat laws [rstr_join] / [strength_join] glued by the
       single-variable naturality corollaries of Monad/Strong/Symmetric.v.
       The two composites of a left-tensored f with a right-tensored g
       normalize to the two double strengths ([kl_square_lr],
       [kl_square_rl]), giving the concrete characterization of centrality
       in Kl(M): f is central exactly when [dstr] and [dstr'] agree on
       every tensor with f in either factor ([kleisli_central_iff]).

    2. The pure functor ([Kleisli_Pure]): postcomposing with the unit
       embeds C into Kl(M) by f ↦ ret ∘ f ([kpure]), with the exchange
       laws [kl_pure_post] / [kl_pure_pre] that let pure morphisms slide
       through Kleisli composites, and the transfer laws [pure_inj_left] /
       [pure_inj_right] that let them slide through the tensorings.  Every
       pure morphism is central ([pure_central]): both centrality squares
       collapse through the four double-strength unit laws
       [dstr_ret_left], [dstr'_ret_left], [dstr_ret_right],
       [dstr'_ret_right] of Monad/Strong/Symmetric.v — no commutativity
       of M is needed.

    3. The premonoidal structure ([Kleisli_Premonoidal]): the unitors and
       associator of Kl(M) are the images of C's under [Kleisli_Pure]
       ([Kleisli_pure_iso]), hence central by [pure_central]; their
       one-variable naturality squares are the strength coherences —
       [strength_id_left] and [rstr_id_right] for the unitors, and for the
       associator the three laws [rstr_assoc_to], [strength_rstr_assoc]
       and [strength_assoc], one per tensor position, glued by the
       joint naturality of C's associator; triangle and pentagon transfer
       from C along the pure functor.

    When M is commutative the two tensorings assemble into a genuine
    monoidal structure on Kl(M); that upgrade lives in
    Monad/Kleisli/Commutative.v, built on the all-central engine of
    Structure/Premonoidal/Monoidal.v and on [kleisli_central_iff] below. 

--------
* 强单子的Kleisli范畴是前单子

nLab：https://ncatlab.org/nlab/show/premonoidal+category
 nLab：https://ncatlab.org/nlab/show/strong+monad

Power–Robinson（“Premonoidal 类别和计算概念”，
 数学。 结构计算。 科学。 7(5), 1997）观察到，对于强
 对称幺半群范畴 C 上的单子 M，Kleisli 范畴 Kl(M)
 具有规范的前幺半群结构：C 的张量延伸至
 Kl(M) 分别在每个变量中 — 通过导出的正确强度
 左边的 [rstr] 和左边的力量 [strength] 上的
 正确 - 但不是联合的，因为测序的两个顺序是一对
 有效的计算通常不同意。 该文件构造了
 库实际 [Kleisli] 类别的结构
 (Monad/Kleisli.v)，分三层：

1. 二元结构 ([Kleisli_Binoidal])：对于每个对象 y'
 一变量张量函子

f ↦ rstr ∘ (f ⨂ id[y']) ([kl_left_fmap], - ⊗ y')
 f ↦ 强度 ∘ (id[x'] ⨂ f) ([kl_right_fmap], x' ⊗ -)

是 Kleisli 函子：身份保存正是 η-compat
 法律 [rstr_ret] / [strength_ret]，并且成分保存是
 完全符合 μ-compat 定律 [rstr_join] / [strength_join] 所粘合的
 Monad/Strong/Symmetric.v 的单变量自然性推论。 
左张量 f 与右张量 g 的两个复合
 标准化为两个双倍强度（[kl_square_lr]，
 [kl_square_rl]），给出了中心性的具体表征
 在 Kl(M) 中：当 [dstr] 和 [dstr'] 一致时，f 正好位于中心
 每个因子中包含 f 的张量 ([kleisli_central_iff])。

2.纯函子（[Kleisli_Pure]）：与单元进行后期合成
 通过 f ↦ ret ∘ f ([kpure]) 将 C 嵌入到 Kl(M) 中，并进行交换
 让纯态射滑动的 [kl_pure_post] / [kl_pure_pre] 定律
 通过 Kleisli 复合材料，以及传输定律 [pure_inj_left] /
 [pure_inj_right] 让他们可以通过张量。 每个
 纯态射是中心 ([pure_central])：两个中心性平方
 通过四个双强度单位定律崩溃
 XPTECT24X、[dstr'_ret_left]、[dstr_ret_right]、
 Monad/Strong/Symmetric.v 的 [dstr'_ret_right] — 无交换律
 需要M。

3. 前幺半群结构 ([Kleisli_Premonoidal])：单位和
 Kl(M) 的关联者是 [Kleisli_Pure] 下 C 的图像
 ([Kleisli_pure_iso])，因此以 [pure_central] 为中心； 他们的
 一变量自然性平方是强度相干性 —
 用于单元的 [strength_id_left] 和 [rstr_id_right]，以及用于
 关联三定律 [rstr_assoc_to]、[strength_rstr_assoc]
 [strength_assoc]，每个张量位置一个，由
 C 的关联者的联合自然性； 三角形和五边形转移
 从 C 沿着纯函子。

当 M 是可交换的时，两个张量组装成一个真正的张量
 Kl(M) 上的幺半群结构； 该升级位于
 Monad/Kleisli/Commutative.v，建立在全中心引擎之上
 Structure/Premonoidal/Monoidal.v 和下面的 [kleisli_central_iff]。 
*)

Section KleisliPremonoidal.

Context `{@SymmetricMonoidal C}.
Context {M : C ⟶ C}.
Context `{@StrongMonad C _ M}.

(* ------------------------------------------------------------------ *)
(** ** Tier 1: the Kleisli binoidal structure.                          / ** 第 1 层：Kleisli 二元结构。*)
(* ------------------------------------------------------------------ *)

(*
The action of - ⊗ y' on a Kleisli morphism f : x ~> M z: tensor with the
   identity and re-associate the M through the derived right strength.
   Stated as named C-level definitions so that the [AFunctor] record fields
   below elaborate without inline Kleisli-hom ascriptions. 

--------
- ⊗ y' 对 Kleisli 态射 f : x ~> M z 的作用：张量
 身份并通过派生的正确强度重新关联 M。 
表述为命名的 C 级定义，以便 [AFunctor] 记录字段
 下面详细阐述，没有内嵌的 Kleisli-hom 归属。 
*)
Definition kl_left_fmap (y' : C) {x z : C} (f : x ~{C}~> M z) :
  (x ⨂ y')%object ~{C}~> M ((z ⨂ y')%object) :=
  rstr ∘ (f ⨂ id[y']).

(*
The action of x' ⊗ - on a Kleisli morphism f : y ~> M z, through the
   left strength. 

--------
x' ⊗ 对Kleisli态射 f : y ~> M z 的作用，通过
 剩下的力量。 
*)
Definition kl_right_fmap (x' : C) {y z : C} (f : y ~{C}~> M z) :
  (x' ⨂ y)%object ~{C}~> M ((x' ⨂ z)%object) :=
  strength[M] ∘ (id[x'] ⨂ f).

Lemma kl_left_respects (y' : C) {x z : C} :
  Proper (equiv ==> equiv) (fun f : x ~{C}~> M z => kl_left_fmap y' f).
Proof.
  repeat intro.
  unfold kl_left_fmap.
  apply compose_respects; [reflexivity|].
  apply bimap_respects; [assumption|reflexivity].
Qed.

(*
Identity preservation is the η-compat law of the derived right
   strength. 

--------
身份保存是派生权利的 η-compat 法则
 力量。 
*)
Lemma kl_left_id (y' x : C) :
  kl_left_fmap y' (ret[M]) ≈ (ret[M] : x ⨂ y' ~> M (x ⨂ y')).
Proof. apply rstr_ret. Qed.

(*
Composition preservation is the μ-compat law [rstr_join], with the
   naturality corollary [rstr_natural_l] sliding the tensored middle map
   past the strength. 

--------
成分保存采用 μ-compat 定律 [rstr_join]，其中
 自然推论 [rstr_natural_l] 滑动张量中间图
 过去的实力。 
*)
Lemma kl_left_comp (y' : C) {x y z : C} (f : y ~> M z) (g : x ~> M y) :
  kl_left_fmap y' (join[M] ∘ fmap[M] f ∘ g)
    ≈ join[M] ∘ fmap[M] (kl_left_fmap y' f) ∘ kl_left_fmap y' g.
Proof.
  unfold kl_left_fmap.
  transitivity
    ((rstr ∘ (join[M] ⨂ id[y'])) ∘ ((fmap[M] f ⨂ id[y']) ∘ (g ⨂ id[y']))).
  { rewrite <- !comp_assoc.
    apply compose_respects; [reflexivity|].
    rewrite <- !bimap_comp.
    rewrite !id_left.
    now rewrite !comp_assoc. }
  rewrite rstr_join.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  rewrite <- rstr_natural_l.
  reflexivity.
Qed.

Definition Kleisli_Tensor_Left (y' : C) :
  @AFunctor Kleisli Kleisli (fun x : C => (x ⨂ y')%object) :=
  @Build_AFunctor Kleisli Kleisli (fun x : C => (x ⨂ y')%object)
    (fun x z (f : x ~{Kleisli}~> z) => kl_left_fmap y' f)
    (fun x z => kl_left_respects y')
    (fun x => kl_left_id y' x)
    (fun x y z f g => kl_left_comp y' f g).

Lemma kl_right_respects (x' : C) {y z : C} :
  Proper (equiv ==> equiv) (fun f : y ~{C}~> M z => kl_right_fmap x' f).
Proof.
  repeat intro.
  unfold kl_right_fmap.
  apply compose_respects; [reflexivity|].
  apply bimap_respects; [reflexivity|assumption].
Qed.

(* Identity preservation is the η-compat law of the left strength.  / 身份保存是左强度的 η-compat 定律。*)
Lemma kl_right_id (x' y : C) :
  kl_right_fmap x' (ret[M]) ≈ (ret[M] : x' ⨂ y ~> M (x' ⨂ y)).
Proof. apply strength_ret. Qed.

(*
Composition preservation is the μ-compat law [strength_join], glued by
   [strength_natural_r]. 

--------
组合物保存采用 μ-compat 法则 [strength_join]，通过粘合
 [strength_natural_r]。 
*)
Lemma kl_right_comp (x' : C) {x y z : C} (f : y ~> M z) (g : x ~> M y) :
  kl_right_fmap x' (join[M] ∘ fmap[M] f ∘ g)
    ≈ join[M] ∘ fmap[M] (kl_right_fmap x' f) ∘ kl_right_fmap x' g.
Proof.
  unfold kl_right_fmap.
  transitivity
    ((strength[M] ∘ (id[x'] ⨂ join[M]))
       ∘ ((id[x'] ⨂ fmap[M] f) ∘ (id[x'] ⨂ g))).
  { rewrite <- !comp_assoc.
    apply compose_respects; [reflexivity|].
    rewrite <- !bimap_comp.
    rewrite !id_left.
    now rewrite !comp_assoc. }
  rewrite strength_join.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  rewrite <- strength_natural_r.
  reflexivity.
Qed.

Definition Kleisli_Tensor_Right (x' : C) :
  @AFunctor Kleisli Kleisli (fun y : C => (x' ⨂ y)%object) :=
  @Build_AFunctor Kleisli Kleisli (fun y : C => (x' ⨂ y)%object)
    (fun y z (f : y ~{Kleisli}~> z) => kl_right_fmap x' f)
    (fun y z => kl_right_respects x')
    (fun y => kl_right_id x' y)
    (fun x y z f g => kl_right_comp x' f g).

(*
The Power–Robinson binoidal structure on Kl(M): the object tensor is
   inherited from C, and the two one-variable tensoring functors are the
   strength-mediated actions above. 

--------
Kl(M) 上的 Power-Robinson 二元结构：对象张量为
 继承自 C，两个一变量张量函子是
 上述力量介导的行动。 
*)
Definition Kleisli_Binoidal : @Binoidal Kleisli :=
  @Build_Binoidal Kleisli
    (fun x y : C => (x ⨂ y)%object)
    Kleisli_Tensor_Left
    Kleisli_Tensor_Right.

(*
The tensoring actions in rewrite form: both equations are definitional,
   so downstream proofs can move between the Kleisli-functor view and the
   C-level strength view without unfolding by hand. 

--------
重写形式的张量动作：两个方程都是定义性的，
 因此下游证明可以在 Kleisli 函子视图和
 C级实力观，无需手工展开。 
*)
Lemma kl_inj_left_fmap {y' x z : C} (f : x ~{C}~> M z) :
  fmap[@inj_left Kleisli Kleisli_Binoidal y'] f ≈ rstr ∘ (f ⨂ id[y']).
Proof. reflexivity. Qed.

Lemma kl_inj_right_fmap {x' y z : C} (f : y ~{C}~> M z) :
  fmap[@inj_right Kleisli Kleisli_Binoidal x'] f ≈ strength[M] ∘ (id[x'] ⨂ f).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** ** Normal forms for the two centrality squares.                     / ** 两个中心性正方形的范式。*)
(* ------------------------------------------------------------------ *)

(*
The composite fmap[inj_left] f ∘ fmap[inj_right] g in Kl(M) — in
   execution order: Kleisli composition runs the precomposed factor
   first, so g's computation on the right factor runs before f's on the
   left — computes the double strength [dstr'] (right computation
   sequenced first). 

--------
复合 fmap[inj_left] f ∘ fmap[inj_right] g in Kl(M) — in
 执行顺序：Kleisli 组合运行预组合因子
 首先，所以 g 对右侧因子的计算先于 f 对右侧因子的计算运行
 左 — 计算双倍强度 [dstr']（右计算
 先测序）。 
*)
Lemma kl_square_lr {a b c d} (f : a ~> M b) (g : c ~> M d) :
  @compose Kleisli _ _ _
    (fmap[@inj_left _ Kleisli_Binoidal d] f)
    (fmap[@inj_right _ Kleisli_Binoidal a] g)
    ≈ dstr' ∘ (f ⨂ g).
Proof.
  simpl.
  unfold kl_left_fmap, kl_right_fmap, dstr'.
  rewrite fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  apply compose_respects; [reflexivity|].
  (* fmap (f ⨂ id) ∘ (strength ∘ (id ⨂ g)) ≈ strength ∘ (f ⨂ g) *)
  rewrite comp_assoc.
  rewrite strength_natural_l.
  rewrite <- comp_assoc.
  rewrite <- bimap_comp.
  now rewrite id_left, id_right.
Qed.

(*
The mirror composite fmap[inj_right] g ∘ fmap[inj_left] f — in
   execution order, f's computation on the left factor runs before g's
   on the right — computes the double strength [dstr] (left computation
   sequenced first). 

--------
镜像复合 fmap[inj_right] g ∘ fmap[inj_left] f — in
 执行顺序，f 对左侧因子的计算在 g 之前运行
 右侧 — 计算双倍强度 [dstr]（左侧计算
 先测序）。 
*)
Lemma kl_square_rl {a b c d} (f : a ~> M b) (g : c ~> M d) :
  @compose Kleisli _ _ _
    (fmap[@inj_right _ Kleisli_Binoidal b] g)
    (fmap[@inj_left _ Kleisli_Binoidal c] f)
    ≈ dstr ∘ (f ⨂ g).
Proof.
  simpl.
  unfold kl_left_fmap, kl_right_fmap, dstr.
  rewrite fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  apply compose_respects; [reflexivity|].
  (* fmap (id ⨂ g) ∘ (rstr ∘ (f ⨂ id)) ≈ rstr ∘ (f ⨂ g) *)
  rewrite comp_assoc.
  rewrite rstr_natural_r.
  rewrite <- comp_assoc.
  rewrite <- bimap_comp.
  now rewrite id_left, id_right.
Qed.

(*
The concrete characterization of centrality in Kl(M): a Kleisli morphism
   f is central (Structure/Binoidal.v) exactly when the two double
   strengths agree on every tensor with f in either factor.  Commutative
   monads are precisely those all of whose Kleisli morphisms are central. 

--------
Kl(M) 中心性的具体表征：Kleisli态射
 当两个双精度数时，f 正好位于中心（Structure/Binoidal.v）
 每个张量的强度都与任一因子中的 f 一致。 交换律
 单子正是那些以Kleisli态射为中心的单子。 
*)
Lemma kleisli_central_iff {a b} (f : a ~> M b) :
  @central Kleisli Kleisli_Binoidal a b f
    ↔ ∀ c d (g : c ~> M d),
        (dstr ∘ (f ⨂ g) ≈ dstr' ∘ (f ⨂ g))
      ∧ (dstr ∘ (g ⨂ f) ≈ dstr' ∘ (g ⨂ f)).
Proof.
  split.
  - intros central_f c d g.
    destruct (central_f c d g) as [sq1 sq2].
    split.
    + rewrite <- kl_square_lr, <- kl_square_rl.
      now symmetry.
    + rewrite <- kl_square_lr, <- kl_square_rl.
      now symmetry.
  - intros commutes c d g.
    split.
    + rewrite kl_square_lr, kl_square_rl.
      symmetry; apply commutes.
    + rewrite kl_square_lr, kl_square_rl.
      symmetry; apply commutes.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Tier 2: the pure functor C ⟶ Kl(M).                              / ** 第 2 层：纯函子 C ⟶ Kl(M)。*)
(* ------------------------------------------------------------------ *)

(* A pure Kleisli morphism: an ordinary C-morphism followed by the unit.  / 纯 Kleisli 态射：普通的 C 态射后跟单位。*)
Definition kpure {x y : C} (f : x ~{C}~> y) : x ~{Kleisli}~> y :=
  ret[M] ∘ f.

(*
Postcomposing a Kleisli morphism with a pure map is functorial action:
   the unit collapses through [join_fmap_ret]. 

--------
用纯映射对 Kleisli 态射进行后合成是函数作用：
 该装置通过 [join_fmap_ret] 崩溃。 
*)
Lemma kl_pure_post {x y z : C} (u : y ~{C}~> z) (h : x ~{Kleisli}~> y) :
  @compose Kleisli _ _ _ (kpure u) h ≈ fmap[M] u ∘ h.
Proof.
  simpl.
  unfold kpure.
  apply compose_respects; [|reflexivity].
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite join_fmap_ret.
  now rewrite id_left.
Qed.

(*
Precomposing a Kleisli morphism with a pure map is plain C-level
   precomposition: the unit collapses through [fmap_ret] and [join_ret]. 

--------
用纯映射预组合 Kleisli 态射是简单的 C 级
 预组合：该单元通过 [fmap_ret] 和 [join_ret] 折叠。 
*)
Lemma kl_pure_pre {x y z : C} (h : y ~{C}~> M z) (u : x ~{C}~> y) :
  @compose Kleisli _ _ _ h (kpure u) ≈ h ∘ u.
Proof.
  simpl.
  unfold kpure.
  rewrite comp_assoc.
  apply compose_respects; [|reflexivity].
  rewrite <- comp_assoc.
  rewrite <- fmap_ret.
  rewrite comp_assoc.
  rewrite join_ret.
  now rewrite id_left.
Qed.

(* Kleisli composition of pure maps is pure composition.  / 纯贴图的Kleisli合成是纯合成。*)
Lemma kl_pure_comp {x y z : C} (u : y ~{C}~> z) (v : x ~{C}~> y) :
  @compose Kleisli _ _ _ (kpure u) (kpure v) ≈ kpure (u ∘ v).
Proof.
  rewrite kl_pure_pre.
  unfold kpure.
  now rewrite comp_assoc.
Qed.

Lemma kpure_respects {x y : C} :
  Proper (equiv ==> equiv) (fun f : x ~{C}~> y => (kpure f : x ~{C}~> M y)).
Proof.
  repeat intro.
  unfold kpure.
  apply compose_respects; [reflexivity|assumption].
Qed.

(*
Congruence for [kpure] in apply-friendly form, stated over the C-level
   homset so that no Kleisli unification is required of the caller. 

--------
[kpure] 的一致性以适用的形式在 C 级上表述
 homset，以便调用者不需要 Kleisli 统一。 
*)
Lemma kpure_proper {x y : C} {f g : x ~{C}~> y} (E : f ≈ g) :
  (kpure f : x ~{C}~> M y) ≈ kpure g.
Proof.
  unfold kpure.
  now rewrite E.
Qed.

Lemma kpure_id {x : C} : kpure (@id C x) ≈ @id Kleisli x.
Proof.
  unfold kpure; simpl.
  now rewrite id_right.
Qed.

Lemma kpure_comp_functor {x y z : C} (u : y ~{C}~> z) (v : x ~{C}~> y) :
  kpure (u ∘ v) ≈ @compose Kleisli _ _ _ (kpure u) (kpure v).
Proof. symmetry; apply kl_pure_comp. Qed.

(*
The pure functor: the identity on objects, f ↦ ret ∘ f on morphisms.
   This is the left adjoint of the Kleisli adjunction, viewed here purely
   as the medium through which the structural isomorphisms of C transfer
   to Kl(M). 

--------
纯函子：对象上的恒等式，态射上的 f ↦ ret ∘ f。 
这是 Kleisli 伴随的左伴随，在这里纯粹查看
 作为 C 结构同构传递的媒介
 到KL(M)。 
*)
Definition Kleisli_Pure : C ⟶ Kleisli := {|
  fobj := fun x : C => (x : Kleisli);
  fmap := fun (x y : C) (f : x ~{C}~> y) => kpure f;
  fmap_respects := fun x y : C => @kpure_respects x y;
  fmap_id := fun x : C => @kpure_id x;
  fmap_comp := fun (x y z : C) f g => kpure_comp_functor f g
|}.

(*
Pure maps slide through the left tensoring: the unit exits through the
   η-compat law [rstr_ret] of the derived right strength. 

--------
纯贴图通过左张量滑动：该单元通过
 导出右强度的η-兼容定律[rstr_ret]。 
*)
Lemma pure_inj_left {x y : C} (f : x ~{C}~> y) (z : C) :
  fmap[@inj_left Kleisli Kleisli_Binoidal z] (kpure f) ≈ kpure (f ⨂ id[z]).
Proof.
  rewrite kl_inj_left_fmap.
  unfold kpure.
  rewrite bimap_comp_id_right.
  rewrite comp_assoc.
  rewrite rstr_ret.
  reflexivity.
Qed.

(* Pure maps slide through the right tensoring, through [strength_ret].  / 纯贴图通过 [strength_ret] 滑过右侧张量。*)
Lemma pure_inj_right {x y : C} (f : x ~{C}~> y) (z : C) :
  fmap[@inj_right Kleisli Kleisli_Binoidal z] (kpure f) ≈ kpure (id[z] ⨂ f).
Proof.
  rewrite kl_inj_right_fmap.
  unfold kpure.
  rewrite bimap_comp_id_left.
  rewrite comp_assoc.
  rewrite strength_ret.
  reflexivity.
Qed.

(*
Every pure morphism is central in Kl(M).  Through the characterization
   [kleisli_central_iff], each of the two squares reduces to one of the
   four double-strength unit laws of Monad/Strong/Symmetric.v: feeding a
   returned value into either factor collapses [dstr] and [dstr'] onto the
   SAME single strength ([strength] on the left factor, [rstr] on the
   right), so the two sequencing orders agree.  The proof is direct — no
   thunkability and no commutativity hypothesis enters. 

--------
每个纯态射都是 Kl(M) 的中心。 通过表征
 [kleisli_central_iff]，两个方块中的每一个都减少为其中一个
 Monad/Strong/Symmetric.v 的四个双强度单位定律：
 将 [dstr] 和 [dstr'] 折叠到任一因子中的返回值
 相同的单一强度（[strength] 在左侧因素上，[rstr] 在左侧因素上）
 右），因此两个排序顺序一致。 证据很直接——不
 thunkability 且不存在交换性假设。 
*)
Theorem pure_central {x y : C} (f : x ~{C}~> y) :
  @central Kleisli Kleisli_Binoidal x y (kpure f).
Proof.
  apply kleisli_central_iff; intros c d g.
  split.
  - assert (E : ((kpure f : x ~{C}~> M y) ⨂ g) ≈ (ret[M] ⨂ id[M d]) ∘ (f ⨂ g)).
    { unfold kpure.
      rewrite <- bimap_comp.
      now rewrite id_left. }
    rewrite E.
    rewrite !comp_assoc.
    now rewrite dstr_ret_left, dstr'_ret_left.
  - assert (E : (g ⨂ (kpure f : x ~{C}~> M y)) ≈ (id[M d] ⨂ ret[M]) ∘ (g ⨂ f)).
    { unfold kpure.
      rewrite <- bimap_comp.
      now rewrite id_left. }
    rewrite E.
    rewrite !comp_assoc.
    now rewrite dstr_ret_right, dstr'_ret_right.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Tier 3: the premonoidal structure on Kl(M).                      / ** 第 3 层：Kl(M) 上的前幺半群结构。*)
(* ------------------------------------------------------------------ *)

(*
An isomorphism of C becomes an isomorphism of Kl(M) through the pure
   functor: both inverse laws are the C-level laws under [kl_pure_comp]. 

--------
C 的同构变成 Kl(M) 的同构
 函子：两个逆定律都是 [kl_pure_comp] 下的 C 级定律。 
*)
Lemma kl_pure_iso_law {x y : C} (u : x ~{C}~> y) (v : y ~{C}~> x) :
  u ∘ v ≈ id[y] →
  @compose Kleisli _ _ _ (kpure u) (kpure v) ≈ @id Kleisli y.
Proof.
  intros E.
  rewrite kl_pure_comp.
  unfold kpure.
  rewrite E.
  simpl.
  now rewrite id_right.
Qed.

Definition Kleisli_pure_iso {x y : C} (i : x ≅ y) : @Isomorphism Kleisli x y := {|
  to := kpure (to i);
  from := kpure (from i);
  iso_to_from := kl_pure_iso_law (to i) (from i) (iso_to_from i);
  iso_from_to := kl_pure_iso_law (from i) (to i) (iso_from_to i)
|}.

(*
Naturality of the left unitor in Kl(M): after the pure-map exchange
   laws, this is Kock's unit coherence [strength_id_left] composed with
   naturality of λ in C. 

--------
Kl(M) 中左单位的自然性：纯映射交换后
 定律，这是由 Kock 单位相干 [strength_id_left] 组成
 C 中 λ 的自然性。 
*)
Lemma kl_unit_left_natural {x y : C} (g : x ~{Kleisli}~> y) :
  @compose Kleisli _ _ _ g (kpure (to (@unit_left C _ x)))
    ≈ @compose Kleisli _ _ _ (kpure (to (@unit_left C _ y)))
        (fmap[@inj_right Kleisli Kleisli_Binoidal (@I C _)] g).
Proof.
  rewrite kl_pure_pre, kl_pure_post.
  rewrite kl_inj_right_fmap.
  rewrite comp_assoc.
  rewrite strength_id_left.
  apply (@to_unit_left_natural C _ x (M y) g).
Qed.

(*
Naturality of the right unitor: the mirror argument through the derived
   right strength's ρ-coherence [rstr_id_right]. 

--------
右单位的自然性：通过导出的镜像论证
 右强度的 ρ-相干性 [rstr_id_right]。 
*)
Lemma kl_unit_right_natural {x y : C} (g : x ~{Kleisli}~> y) :
  @compose Kleisli _ _ _ g (kpure (to (@unit_right C _ x)))
    ≈ @compose Kleisli _ _ _ (kpure (to (@unit_right C _ y)))
        (fmap[@inj_left Kleisli Kleisli_Binoidal (@I C _)] g).
Proof.
  rewrite kl_pure_pre, kl_pure_post.
  rewrite kl_inj_left_fmap.
  rewrite comp_assoc.
  rewrite rstr_id_right.
  apply (@to_unit_right_natural C _ x (M y) g).
Qed.

(*
Naturality of the associator in the LEFT tensor position: the α-law of
   the derived right strength ([rstr_assoc_to]) absorbs the two stacked
   left tensorings, and joint naturality of C's associator (with
   identities in the other two positions) closes the square. 

--------
LEFT 张量位置关联子的自然性：α 定律
 导出的正确强度（[rstr_assoc_to]）吸收两个堆叠的
 左张量，以及 C 关联器的联合自然性（与
 其他两个位置的恒等式）关闭了正方形。 
*)
Lemma kl_assoc_natural_left {x y z w : C} (g : x ~{Kleisli}~> y) :
  @compose Kleisli _ _ _
    (fmap[@inj_left Kleisli Kleisli_Binoidal (z ⨂ w)%object] g)
    (kpure (to (@tensor_assoc C _ x z w)))
  ≈ @compose Kleisli _ _ _
      (kpure (to (@tensor_assoc C _ y z w)))
      (fmap[@inj_left Kleisli Kleisli_Binoidal w]
         (fmap[@inj_left Kleisli Kleisli_Binoidal z] g)).
Proof.
  rewrite kl_pure_pre, kl_pure_post.
  rewrite !kl_inj_left_fmap.
  rewrite bimap_comp_id_right.
  rewrite !comp_assoc.
  rewrite rstr_assoc_to.
  pose proof (@to_tensor_assoc_natural
                C _ x (M y) z z w w g (id[z]) (id[w])) as AN.
  rewrite bimap_id_id in AN.
  rewrite <- !comp_assoc.
  rewrite <- AN.
  reflexivity.
Qed.

(*
Naturality of the associator in the MIDDLE tensor position: the sole
   consumer of the mixed coherence [strength_rstr_assoc] of
   Monad/Strong/Symmetric.v, which relates the left strength inside a left
   tensoring to the right strength inside a right tensoring across α. 

--------
中间张量位置关联器的自然性：唯一
 混合相干 [strength_rstr_assoc] 的消费者
 Monad/Strong/Symmetric.v，将左强度与左强度联系起来
 在 α 上的右张量内张量到正确的强度。 
*)
Lemma kl_assoc_natural_middle {x z w y : C} (h : z ~{Kleisli}~> w) :
  @compose Kleisli _ _ _
    (fmap[@inj_right Kleisli Kleisli_Binoidal x]
       (fmap[@inj_left Kleisli Kleisli_Binoidal y] h))
    (kpure (to (@tensor_assoc C _ x z y)))
  ≈ @compose Kleisli _ _ _
      (kpure (to (@tensor_assoc C _ x w y)))
      (fmap[@inj_left Kleisli Kleisli_Binoidal y]
         (fmap[@inj_right Kleisli Kleisli_Binoidal x] h)).
Proof.
  rewrite kl_pure_pre, kl_pure_post.
  rewrite !kl_inj_right_fmap.
  rewrite !kl_inj_left_fmap.
  rewrite bimap_comp_id_left.
  rewrite bimap_comp_id_right.
  rewrite !comp_assoc.
  rewrite strength_rstr_assoc.
  pose proof (@to_tensor_assoc_natural
                C _ x x z (M w) y y (id[x]) h (id[y])) as AN.
  rewrite <- !comp_assoc.
  rewrite <- AN.
  reflexivity.
Qed.

(*
Naturality of the associator in the RIGHT tensor position: Kock's
   associativity coherence [strength_assoc] absorbs the two stacked right
   tensorings. 

--------
右张量位置关联子的自然性：Kock's
 关联性一致性 [strength_assoc] 吸收了两个堆叠的右侧
 张量。 
*)
Lemma kl_assoc_natural_right {x y z w : C} (i : z ~{Kleisli}~> w) :
  @compose Kleisli _ _ _
    (fmap[@inj_right Kleisli Kleisli_Binoidal x]
       (fmap[@inj_right Kleisli Kleisli_Binoidal y] i))
    (kpure (to (@tensor_assoc C _ x y z)))
  ≈ @compose Kleisli _ _ _
      (kpure (to (@tensor_assoc C _ x y w)))
      (fmap[@inj_right Kleisli Kleisli_Binoidal (x ⨂ y)%object] i).
Proof.
  rewrite kl_pure_pre, kl_pure_post.
  rewrite !kl_inj_right_fmap.
  rewrite bimap_comp_id_left.
  rewrite !comp_assoc.
  rewrite strength_assoc.
  pose proof (@to_tensor_assoc_natural
                C _ x x y y z (M w) (id[x]) (id[y]) i) as AN.
  rewrite bimap_id_id in AN.
  rewrite <- !comp_assoc.
  rewrite <- AN.
  reflexivity.
Qed.

(*
The triangle coherence transfers from C: all three structural maps are
   pure, so the equation is the image of C's triangle under [kpure]. 

--------
三角形相干性从 C 转移：所有三个结构图都是
 pure，所以方程是C的三角形在[kpure]下的图像。 
*)
Lemma kl_triangle {x y : C} :
  fmap[@inj_left Kleisli Kleisli_Binoidal y] (kpure (to (@unit_right C _ x)))
  ≈ @compose Kleisli _ _ _
      (fmap[@inj_right Kleisli Kleisli_Binoidal x]
         (kpure (to (@unit_left C _ y))))
      (kpure (to (@tensor_assoc C _ x (@I C _) y))).
Proof.
  rewrite pure_inj_left, pure_inj_right.
  rewrite kl_pure_comp.
  apply kpure_proper.
  apply triangle_identity.
Qed.

(* The pentagon coherence transfers from C the same way.  / 五边形相干性以同样的方式从 C 转移。*)
Lemma kl_pentagon {x y z w : C} :
  @compose Kleisli _ _ _
    (@compose Kleisli _ _ _
       (fmap[@inj_right Kleisli Kleisli_Binoidal x]
          (kpure (to (@tensor_assoc C _ y z w))))
       (kpure (to (@tensor_assoc C _ x (y ⨂ z)%object w))))
    (fmap[@inj_left Kleisli Kleisli_Binoidal w]
       (kpure (to (@tensor_assoc C _ x y z))))
  ≈ @compose Kleisli _ _ _
      (kpure (to (@tensor_assoc C _ x y (z ⨂ w)%object)))
      (kpure (to (@tensor_assoc C _ (x ⨂ y)%object z w))).
Proof.
  rewrite pure_inj_right, pure_inj_left.
  rewrite !kl_pure_comp.
  apply kpure_proper.
  apply pentagon_identity.
Qed.

(*
The Power–Robinson premonoidal structure on the Kleisli category of a
   strong monad over a symmetric monoidal base: unit and structural
   isomorphisms are the pure images of C's, centrality of the structural
   maps is [pure_central], the three one-variable associator squares are
   the three strength coherences, and the coherence laws transfer along
   the pure functor. 

--------
a 的 Kleisli 范畴上的 Power-Robinson 前幺半群结构
 对称单曲面基础上的强单子：单元和结构
 同构是C的纯图像，结构的中心性
 映射是 [pure_central]，三个一变量关联器方块是
 三种强度相干性，相干性定律沿着
 纯函子。 
*)
Definition Kleisli_Premonoidal : @Premonoidal Kleisli Kleisli_Binoidal :=
  @Build_Premonoidal Kleisli Kleisli_Binoidal
    (@I C _)
    (fun x : C => Kleisli_pure_iso (@unit_left C _ x))
    (fun x : C => Kleisli_pure_iso (@unit_right C _ x))
    (fun x y z : C => Kleisli_pure_iso (@tensor_assoc C _ x y z))
    (fun x : C => pure_central (to (@unit_left C _ x)))
    (fun x : C => pure_central (to (@unit_right C _ x)))
    (fun x y z : C => pure_central (to (@tensor_assoc C _ x y z)))
    (fun (x y : C) (g : x ~{Kleisli}~> y) => kl_unit_left_natural g)
    (fun (x y : C) (g : x ~{Kleisli}~> y) => kl_unit_right_natural g)
    (fun (x y z w : C) (g : x ~{Kleisli}~> y) => kl_assoc_natural_left g)
    (fun (x z w y : C) (h : z ~{Kleisli}~> w) => kl_assoc_natural_middle h)
    (fun (x y z w : C) (i : z ~{Kleisli}~> w) => kl_assoc_natural_right i)
    (fun x y : C => @kl_triangle x y)
    (fun x y z w : C => @kl_pentagon x y z w).

End KleisliPremonoidal.
