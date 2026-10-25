Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Structure.Monoidal.CopyDiscard.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.CommutativeComonoid.
Require Import Category.Structure.Binoidal.
Require Import Category.Structure.Binoidal.Central.
Require Import Category.Structure.Premonoidal.
Require Import Category.Structure.Premonoidal.Monoidal.
Require Import Category.Monad.Strong.
Require Import Category.Monad.Strong.Symmetric.
Require Import Category.Monad.Kleisli.
Require Import Category.Monad.Kleisli.Premonoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

(**
* The Kleisli category of a commutative strong monad is monoidal

    nLab: https://ncatlab.org/nlab/show/commutative+monad
    nLab: https://ncatlab.org/nlab/show/premonoidal+category

    Monad/Kleisli/Premonoidal.v equips the Kleisli category Kl(M) of a
    strong monad M over a symmetric monoidal base with its Power-Robinson
    premonoidal structure, and characterizes centrality there: a Kleisli
    morphism f is central exactly when the two double strengths [dstr] and
    [dstr'] agree on every tensor with f in either factor
    ([kleisli_central_iff]).  This file treats the commutative case of
    the Kleisli premonoidal development:

    1. The funnel between commutativity and centrality, in both
       directions.  If M is commutative ([commutative_sm], i.e. dstr and
       dstr' agree everywhere), then EVERY Kleisli morphism is central
       ([kleisli_all_central]): both centrality squares are congruence
       instances of the commutativity equation.  Conversely, if every
       Kleisli morphism is central, instantiating the centrality of the
       identity Kleisli maps id[M x] : M x ~{Kl}~> x against id[M y]
       collapses the centrality square to dstr ≈ dstr' on the nose
       ([kleisli_all_central_commutative]).  Together: M is commutative
       iff Kl(M) is monoidal with its canonical tensor.

    2. The monoidal upgrade ([Kleisli_Monoidal]): the all-central engine
       [Premonoidal_Monoidal] of Structure/Premonoidal/Monoidal.v applied
       to [Kleisli_Premonoidal] with the centrality witness of point 1.
       The induced tensor acts on morphism pairs by the double strength:
       bimap f g ≈ dstr ∘ (f ⨂ g) ([kleisli_bimap_dstr]), and on pure
       morphisms by the pure image of the base tensor ([kl_pure_tensor]).

    3. The braided and symmetric upgrades ([Kleisli_Braided],
       [Kleisli_Symmetric]): the braiding of Kl(M) is the pure image of
       the base braiding.  Its joint naturality square reduces through
       [kleisli_bimap_dstr] to the conjugation identity
       dstr' ≈ M(β) ∘ dstr ∘ β ([dstr_braid], a fact of every strong
       monad over a symmetric base, no commutativity needed); the
       hexagons and the involution law transfer from the base along the
       pure functor.

    4. The copy-discard descent ([Kleisli_CopyDiscard]): when the base
       carries a CopyDiscard structure, Kl(M) does too, with
       copy := kpure copy and discard := kpure discard.  All comonoid
       laws and the tensor/unit coherences are pure transfers; the
       heaviest step is transporting the five-factor middle-interchange
       word [mid_swap_inv] of Hypergraph.v through the pure functor
       ([kl_pure_mid_swap_inv]).  Crucially, naturality of copy and
       discard is not part of the transported structure: in Kl(M) an
       effectful morphism need not commute with duplication or deletion
       of its input, and the two Cho-Jacobs squares single out the
       deterministic morphisms — exactly the substrate
       Monad/Thunkable.v builds on.

    The comm-gated structures are Definitions, not Instances: they take
    the commutativity witness as an argument once the section closes, so
    typeclass resolution can never conjure a monoidal structure on Kl(M)
    without being handed a proof that M commutes. 

--------
* 可交换强单子的 Kleisli 范畴是幺半群

nLab：https://ncatlab.org/nlab/show/commutative+monad
 nLab：https://ncatlab.org/nlab/show/premonoidal+category

Monad/Kleisli/Premonoidal.v 装备了 a 的 Kleisli 类别 Kl(M)
 具有 Power-Robinson 的对称幺半群基上的强单子 M
 前幺半群结构，并表征那里的中心性：Kleisli
 当两个双强度 [dstr] 和
 [dstr'] 同意每个因子中具有 f 的张量
 ([kleisli_central_iff])。 该文件处理可交换的情况
 Kleisli 前幺半群发展：

1. 交换性和中心性之间的漏斗
 方向。 如果 M 是可交换的（[commutative_sm]，即 dstr 和
 dstr' 处处一致），那么每个 Kleisli 态射都是中心
 ([kleisli_all_central])：两个中心性平方是全等的
 交换性方程的实例。 反之，如果每一个
 Kleisli态射是中心，实例化了中心性
 身份 Kleisli 映射 id[M x] : M x ~{Kl}~> x 与 id[M y]
 将鼻子上的中心性平方折叠为 dstr ≈ dstr'
 ([kleisli_all_central_commutative])。 合起来：M 是可交换的
 当且仅当 Kl(M) 与其正则张量是幺半群的。

2.幺半群升级（[Kleisli_Monoidal]）：全中心引擎
 应用 Structure/Premonoidal/Monoidal.v 的 [Premonoidal_Monoidal]
 到 [Kleisli_Premonoidal] 并以第 1 点为中心性见证。 
诱导张量通过双倍强度作用于态射对：
 bimap f g ≈ dstr ∘ (f ⨂ g) ([kleisli_bimap_dstr])，并且在纯
 基张量的纯图像 ([kl_pure_tensor]) 的态射。

3. 编织和对称升级（[Kleisli_Braided]、
 [Kleisli_Symmetric])：Kl(M)的编织是纯图像
 基础编织。 其联合自然性平方通过减少
 [kleisli_bimap_dstr] 的共轭特性
 dstr' ≈ M(β) ∘ dstr ∘ β ([dstr_braid]，每个强的事实
 对称基上的 monad，不需要交换性）； 的
 六边形和对合律从底沿沿
 纯函子。

4. 复制丢弃血统（[Kleisli_CopyDiscard]）：当底座
 带有 CopyDiscard 结构，Kl(M) 也带有 CopyDiscard 结构，其中
 复制 := kpure 复制并丢弃 := kpure 丢弃。 所有类群
 定律和张量/单位相干性是纯传递； 的
 最重的一步是运输五因素中间立交桥
 通过纯函子的 Hypergraph.v 的字 [mid_swap_inv]
 （[kl_pure_mid_swap_inv]）。 至关重要的是，复制的自然性和
 丢弃不是传输结构的一部分：在 Kl(M) 中
 有效的态射不需要与复制或删除交换
 的输入，两个 Cho-Jacobs 方块选出
 确定性态射——正是底物
 Monad/Thunkable.v 构建于此。

通信门控结构是定义，而不是实例：它们采用
 一旦该节结束，交换性见证作为参数，所以
 类型类解析永远无法在 Kl(M) 上构造出幺半群结构
 没有得到 M 通勤的证明。 
*)

Section KleisliCommutative.

Context `{@SymmetricMonoidal C}.
Context {M : C ⟶ C}.
Context `{@StrongMonad C _ M}.

(*
Congruence for [kpure], specialized to the ambient context so that
   [apply] never has to reconstruct the section instances by
   unification: the many transfer proofs below invoke it on goals whose
   endpoint objects are stated through the induced Kleisli tensor. 

--------
[kpure] 的一致性，专门针对环境上下文，以便
 [apply] 永远不必通过以下方式重建部分实例
 统一：下面的许多转移证明在其目标上调用它
 端点对象通过诱导Kleisli张量来表示。 
*)
Lemma kl_pure_eqv {a b : C} {u v : a ~{C}~> b} (E : u ≈ v) :
  (kpure u : a ~{Kleisli}~> b) ≈ kpure v.
Proof. now apply kpure_proper. Qed.

(* ------------------------------------------------------------------ *)
(** ** The braid conjugation identity for the double strengths.         / ** 辫子结合特性具有双重强度。*)
(* ------------------------------------------------------------------ *)

(*
Conjugating [dstr] by the braiding on both sides computes [dstr']:
   unfolding [rstr] inside [dstr] at the swapped indices exposes a braid
   pair that the involution law removes, and naturality of join
   ([join_fmap_fmap]) slides the outer M(β) under the multiplication,
   reassembling [rstr] inside the fmap argument of [dstr'].  This is a
   fact of every strong monad over a symmetric base — no commutativity
   hypothesis enters — and it is what lets the braiding of Kl(M) commute
   with the double-strength tensor below. 

--------
通过两侧的编织结合 [dstr] 计算 [dstr']：
 在 [dstr] 内展开 [rstr]，在交换的索引处露出辫子
 对合律删除的对，以及连接的自然性
 ([join_fmap_fmap]) 在乘法下滑动外部 M(β)，
 在 [dstr'] 的 fmap 参数内重新组装 [rstr]。 这是一个
 每个强单子都位于对称基上的事实——没有交换律
 假设进入——这就是让 Kl(M) 的编织得以通勤的原因
 与下面的双强度张量。 
*)
Lemma dstr_braid {x y : C} :
  (dstr' : M x ⨂ M y ~> M (x ⨂ y))
    ≈ fmap[M] braid ∘ (dstr : M y ⨂ M x ~> M (y ⨂ x)) ∘ braid.
Proof.
  unfold dstr, dstr', rstr.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  rewrite braid_invol.
  rewrite id_right.
  rewrite !comp_assoc.
  rewrite join_fmap_fmap.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Commutativity versus centrality: both directions.                / ** 交换性与中心性：两个方向。*)
(* ------------------------------------------------------------------ *)

(*
If M is commutative, every Kleisli morphism is central: through the
   characterization [kleisli_central_iff], each of the two centrality
   squares asks that [dstr] and [dstr'] agree on a tensor with f in one
   factor, which is a congruence instance of the commutativity
   equation. 

--------
如果 M 是可交换的，则每个 Kleisli 态射都是中心的：通过
 表征 [kleisli_central_iff]，两个中心性中的每一个
 squares 要求 [dstr] 和 [dstr'] 在一个包含 f 的张量上达成一致
 因子，它是交换性的同余实例
 方程。 
*)
Theorem kleisli_all_central (comm : commutative_sm (M:=M))
        {x y : C} (f : x ~{Kleisli}~> y) :
  @central Kleisli Kleisli_Binoidal x y f.
Proof.
  apply kleisli_central_iff; intros c d g.
  split.
  - now rewrite (comm y d).
  - now rewrite (comm d y).
Qed.

(*
Conversely, if every Kleisli morphism is central, M is commutative:
   instantiate the centrality of the Kleisli morphism
   id[M x] : M x ~{Kl}~> x against id[M y] : M y ~{Kl}~> y.  The square
   normalizes to dstr ∘ (id ⨂ id) ≈ dstr' ∘ (id ⨂ id), and the identity
   padding evaporates by [bimap_id_id]. 

--------
相反，如果每个 Kleisli 态射都是中心的，则 M 是可交换的：
 实例化 Kleisli 态射的中心性
 id[M x]：M x ~{Kl}~> x 与 id[M y]：M y ~{Kl}~> y。 广场
 标准化为 dstr ∘ (id ⨂ id) ≈ dstr' ∘ (id ⨂ id)，并且恒等
 [bimap_id_id] 使衬垫蒸发。 
*)
Theorem kleisli_all_central_commutative
        (allc : ∀ (x y : C) (f : x ~{Kleisli}~> y),
                  @central Kleisli Kleisli_Binoidal x y f) :
  commutative_sm (M:=M).
Proof.
  intros x y.
  destruct (kleisli_central_iff (a:=M x) (b:=x) (@id C (M x))) as [fwd _].
  destruct (fwd (allc (M x) x (@id C (M x))) (M y) y (@id C (M y)))
    as [sq _].
  rewrite bimap_id_id in sq.
  rewrite !id_right in sq.
  exact sq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The comm-gated structures.                                       / ** 通信门控结构。*)
(* ------------------------------------------------------------------ *)

Section WithComm.

Hypothesis comm : commutative_sm (M:=M).

(**
*** The monoidal structure on Kl(M)

    The all-central engine of Structure/Premonoidal/Monoidal.v applied
    at the Power-Robinson premonoidal structure of Kl(M), with the
    centrality of all morphisms supplied by [kleisli_all_central]. 

--------
*** Kl(M) 上的幺半群结构

 采用Structure/Premonoidal/Monoidal.v全中心引擎
 在 Kl(M) 的 Power-Robinson 前幺半群结构中，
 [kleisli_all_central] 提供的所有态射的中心性。 
*)

Definition Kleisli_Monoidal : @Monoidal Kleisli :=
  @Premonoidal_Monoidal Kleisli Kleisli_Binoidal Kleisli_Premonoidal
    (fun (x y : Kleisli) (f : x ~{Kleisli}~> y) =>
       kleisli_all_central comm f).

(*
The induced tensor computes the double strength on morphism pairs:
   [bimap] over [Kleisli_Monoidal] is definitionally the interleaved
   composite [composite_ff'], whose right-then-left normal form is
   [kl_square_rl]. 

--------
诱导张量计算态射对的双倍强度：
 [bimap] 相对于 [Kleisli_Monoidal] 定义上是交错的
 复合 [composite_ff']，其先右后左范式为
 [kl_square_rl]。 
*)
Lemma kleisli_bimap_dstr {a b c d : C}
      (f : a ~{Kleisli}~> b) (g : c ~{Kleisli}~> d) :
  (f ⨂[Kleisli_Monoidal] g)
    ≈ dstr ∘ ((f : a ~{C}~> M b) ⨂ (g : c ~{C}~> M d)).
Proof. exact (kl_square_rl f g). Qed.

(*
Padding one side of the tensor with the Kleisli identity leaves the
   corresponding one-variable tensoring functor of the binoidal
   structure; these are [composite_id_right] / [composite_id_left]
   restated over the monoidal [bimap]. 

--------
用 Kleisli 恒等式填充张量的一侧留下
 二元曲线对应的一变量张量函子
 结构； 这些是 [composite_id_right] / [composite_id_left]
 在幺半群 [bimap] 上重述。 
*)
Lemma kl_bimap_inj_left {a b : C} (w : C) (f : a ~{Kleisli}~> b) :
  (f ⨂[Kleisli_Monoidal] (@id Kleisli w))
    ≈ fmap[@inj_left Kleisli Kleisli_Binoidal w] f.
Proof. exact (@composite_id_right Kleisli Kleisli_Binoidal a b w f). Qed.

Lemma kl_bimap_inj_right (w : C) {a b : C} (f : a ~{Kleisli}~> b) :
  ((@id Kleisli w) ⨂[Kleisli_Monoidal] f)
    ≈ fmap[@inj_right Kleisli Kleisli_Binoidal w] f.
Proof. exact (@composite_id_left Kleisli Kleisli_Binoidal a b w f). Qed.

(*
The tensor of two pure morphisms is the pure image of the base
   tensor: after [kleisli_bimap_dstr], feeding returned values into both
   factors of [dstr] collapses it through [dstr_ret_left] and
   [strength_ret] onto a single unit. 

--------
两个纯态射的张量是基的纯像
 张量：在 [kleisli_bimap_dstr] 之后，将返回值输入到两者中
 [dstr] 的因素通过 [dstr_ret_left] 使其崩溃，并且
 [strength_ret] 集成到单个装置上。 
*)
Lemma kl_pure_tensor {a b c d : C} (u : a ~{C}~> b) (v : c ~{C}~> d) :
  ((kpure u) ⨂[Kleisli_Monoidal] (kpure v)) ≈ kpure (u ⨂ v).
Proof.
  rewrite kleisli_bimap_dstr.
  assert (E : ((kpure u : a ~{C}~> M b) ⨂ (kpure v : c ~{C}~> M d))
                ≈ (ret[M] ⨂ ret[M]) ∘ (u ⨂ v)).
  { unfold kpure.
    now rewrite <- bimap_comp. }
  rewrite E; clear E.
  rewrite comp_assoc.
  rewrite dstr_ret_ret.
  unfold kpure.
  reflexivity.
Qed.

(*
One-sided pure padding, the workhorse of every transfer proof below:
   a pure morphism tensored with the Kleisli identity is the pure image
   of the identity-padded base tensor. 

--------
单面纯填充，是下面每个转移证明的主力：
 用 Kleisli 恒等式张量的纯态射是纯像
 身份填充的基张量。 
*)
Lemma kl_bimap_pure_l {a b : C} (u : a ~{C}~> b) (w : C) :
  ((kpure u) ⨂[Kleisli_Monoidal] (@id Kleisli w))
    ≈ kpure (u ⨂ id[w]).
Proof.
  rewrite kl_bimap_inj_left.
  apply pure_inj_left.
Qed.

Lemma kl_bimap_pure_r (w : C) {a b : C} (u : a ~{C}~> b) :
  ((@id Kleisli w) ⨂[Kleisli_Monoidal] (kpure u))
    ≈ kpure (id[w] ⨂ u).
Proof.
  rewrite kl_bimap_inj_right.
  apply pure_inj_right.
Qed.

(**
*** The pure-transfer kit for the structural isomorphisms

    The unitors and associator of [Kleisli_Monoidal] are the pure images
    of the base ones BY DEFINITION — the monoidal structure reuses the
    premonoidal [Kleisli_pure_iso] data — so each transfer equation is
    closed by reflexivity.  They are recorded as lemmas so downstream
    proofs can cite the kit uniformly. 

--------
*** 结构同构的纯转移试剂盒

 [Kleisli_Monoidal] 的单位和关联符是纯图像
 基本结构的定义——幺半群结构重用了
 前幺半群 [Kleisli_pure_iso] 数据 — 因此每个传递方程为
 由反身性封闭。 它们被记录为引理，因此在下游
 校样可以统一引用套件。 
*)

Lemma kl_pure_unit_left (x : C) :
  to (@unit_left Kleisli Kleisli_Monoidal x)
    ≈ kpure (to (@unit_left C _ x)).
Proof. reflexivity. Qed.

Lemma kl_pure_unit_left_from (x : C) :
  from (@unit_left Kleisli Kleisli_Monoidal x)
    ≈ kpure (from (@unit_left C _ x)).
Proof. reflexivity. Qed.

Lemma kl_pure_unit_right (x : C) :
  to (@unit_right Kleisli Kleisli_Monoidal x)
    ≈ kpure (to (@unit_right C _ x)).
Proof. reflexivity. Qed.

Lemma kl_pure_unit_right_from (x : C) :
  from (@unit_right Kleisli Kleisli_Monoidal x)
    ≈ kpure (from (@unit_right C _ x)).
Proof. reflexivity. Qed.

Lemma kl_pure_assoc (x y z : C) :
  to (@tensor_assoc Kleisli Kleisli_Monoidal x y z)
    ≈ kpure (to (@tensor_assoc C _ x y z)).
Proof. reflexivity. Qed.

Lemma kl_pure_assoc_from (x y z : C) :
  from (@tensor_assoc Kleisli Kleisli_Monoidal x y z)
    ≈ kpure (from (@tensor_assoc C _ x y z)).
Proof. reflexivity. Qed.

(**
*** The braided structure on Kl(M)

    The braiding is the pure image of the base braiding.  Its joint
    naturality square — the Naturality-class predicate consumed by the
    [braid_natural] field, mirroring how Instance/StrictCat/Funny.v
    discharges the same obligation — reduces through the two
    double-strength normal forms [kl_square_lr] / [kl_square_rl] and the
    pure exchange laws to a C-level equation between [dstr'] and [dstr],
    which [dstr_braid] closes with one braid involution. 

--------
*** Kl(M)上的编织结构

 编织是基础编织的纯粹形象。 其联合
 natureity-square — 所消耗的自然类谓词
 [braid_natural] 字段，如何镜像 Instance/StrictCat/Funny.v
 履行相同的义务——通过两者减少
 双强度范式 [kl_square_lr] / [kl_square_rl] 和
 [dstr'] 和 [dstr] 之间的 C 级方程的纯交换律，
 [dstr_braid] 以一根编织物对合闭合。 
*)

Lemma kl_braid_natural {x y z w : C}
      (g : x ~{Kleisli}~> y) (h : z ~{Kleisli}~> w) :
  @compose Kleisli _ _ _
    (@compose Kleisli _ _ _
       ((h ⨂[Kleisli_Monoidal] (@id Kleisli y)))
       (((@id Kleisli z) ⨂[Kleisli_Monoidal] g)))
    (kpure braid)
  ≈ @compose Kleisli _ _ _
      (@compose Kleisli _ _ _
         (kpure braid)
         (((@id Kleisli y) ⨂[Kleisli_Monoidal] h)))
      ((g ⨂[Kleisli_Monoidal] (@id Kleisli z))).
Proof.
  rewrite !kl_bimap_inj_left, !kl_bimap_inj_right.
  rewrite <- (comp_assoc (kpure (@braid C _ y w))).
  rewrite (kl_square_lr h g).
  rewrite (kl_square_rl g h).
  rewrite kl_pure_pre.
  rewrite kl_pure_post.
  (* C-level: dstr' ∘ (h ⨂ g) ∘ β ≈ M(β) ∘ (dstr ∘ (g ⨂ h)) *)
  rewrite <- comp_assoc.
  rewrite bimap_braid.
  rewrite dstr_braid.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc braid braid).
  rewrite braid_invol.
  rewrite id_left.
  reflexivity.
Qed.

(*
The two hexagons transfer from the base along the pure functor: after
   converting the padded bimaps to pure images, both sides collapse to
   the pure image of the corresponding base hexagon. 

--------
两个六边形从底边沿纯函子转移：
 将填充的 bimap 转换为纯图像，两侧折叠为
 相应的底六边形的纯图像。 
*)
Lemma kl_hexagon {x y z : C} :
  @compose Kleisli _ _ _
    (@compose Kleisli _ _ _
       (kpure (to (@tensor_assoc C _ y z x)))
       (kpure (@braid C _ x ((y ⨂ z)%object))))
    (kpure (to (@tensor_assoc C _ x y z)))
  ≈ @compose Kleisli _ _ _
      (@compose Kleisli _ _ _
         (((@id Kleisli y) ⨂[Kleisli_Monoidal] (kpure (@braid C _ x z))))
         (kpure (to (@tensor_assoc C _ y x z))))
      (((kpure (@braid C _ x y)) ⨂[Kleisli_Monoidal] (@id Kleisli z))).
Proof.
  rewrite kl_bimap_pure_l, kl_bimap_pure_r.
  rewrite !kl_pure_comp.
  apply kl_pure_eqv.
  apply hexagon_identity.
Qed.

Lemma kl_hexagon_sym {x y z : C} :
  @compose Kleisli _ _ _
    (@compose Kleisli _ _ _
       (kpure (from (@tensor_assoc C _ z x y)))
       (kpure (@braid C _ ((x ⨂ y)%object) z)))
    (kpure (from (@tensor_assoc C _ x y z)))
  ≈ @compose Kleisli _ _ _
      (@compose Kleisli _ _ _
         (((kpure (@braid C _ x z)) ⨂[Kleisli_Monoidal] (@id Kleisli y)))
         (kpure (from (@tensor_assoc C _ x z y))))
      (((@id Kleisli x) ⨂[Kleisli_Monoidal] (kpure (@braid C _ y z)))).
Proof.
  rewrite kl_bimap_pure_l, kl_bimap_pure_r.
  rewrite !kl_pure_comp.
  apply kl_pure_eqv.
  apply hexagon_identity_sym.
Qed.

Definition Kleisli_Braided : @BraidedMonoidal Kleisli :=
  @Build_BraidedMonoidal Kleisli
    Kleisli_Monoidal
    (fun x y : C => kpure (@braid C _ x y))
    (fun (x y : C) (g : x ~{Kleisli}~> y)
         (z w : C) (h : z ~{Kleisli}~> w) => kl_braid_natural g h)
    (fun x y z : C => @kl_hexagon x y z)
    (fun x y z : C => @kl_hexagon_sym x y z).

(* The involution law is the pure image of the base one.  / 对合律是基对合律的纯像。*)
Lemma kl_braid_invol {x y : C} :
  @compose Kleisli _ _ _ (kpure (@braid C _ y x)) (kpure (@braid C _ x y))
    ≈ @id Kleisli ((x ⨂ y)%object).
Proof.
  rewrite kl_pure_comp.
  transitivity (kpure (@id C ((x ⨂ y)%object))).
  - apply kl_pure_eqv.
    apply braid_invol.
  - apply kpure_id.
Qed.

Definition Kleisli_Symmetric : @SymmetricMonoidal Kleisli :=
  @Build_SymmetricMonoidal Kleisli
    Kleisli_Braided
    (fun x y : C => @kl_braid_invol x y).

(*
The braiding of Kl(M) is the pure image of the base braiding by
   construction; recorded to complete the pure-transfer kit. 

--------
Kl(M)的编织是基础编织的纯图像
 建筑； 记录以完成纯转移套件。 
*)
Lemma kl_pure_braid (x y : C) :
  @braid Kleisli (@symmetric_is_braided Kleisli Kleisli_Symmetric) x y
    ≈ kpure (@braid C _ x y).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** ** The copy-discard descent to Kl(M).                               / ** 复制丢弃下降到 Kl(M)。*)
(* ------------------------------------------------------------------ *)

Section WithCD.

Context `{CD : @CopyDiscard C _}.

(*
The five-factor middle-interchange word of Hypergraph.v, computed in
   [Kleisli_Symmetric], is the pure image of the base one: every factor
   is either a pure structural map on the nose or a pure morphism padded
   with an identity, and the pure functor preserves the composite. 

--------
Hypergraph.v 的五因子中间交换词，计算如下
 [Kleisli_Symmetric]，是基础的纯图像：每一个因素
 要么是鼻子上的纯结构图，要么是纯态射填充
 具有恒等式，并且纯函子保留复合值。 
*)
Lemma kl_pure_mid_swap_inv (X Y : C) :
  @mid_swap_inv Kleisli Kleisli_Symmetric X Y
    ≈ kpure (@mid_swap_inv C _ X Y).
Proof.
  unfold mid_swap_inv.
  rewrite !kpure_comp_functor.
  apply compose_respects.
  2: reflexivity.
  apply compose_respects.
  2: exact (kl_bimap_pure_r X (from (@tensor_assoc C _ X Y Y))).
  apply compose_respects.
  2: {
    etransitivity.
    - apply bimap_respects; [reflexivity|].
      exact (kl_bimap_pure_l (@braid C _ X Y) Y).
    - exact (kl_bimap_pure_r X ((@braid C _ X Y) ⨂ id[Y])).
  }
  apply compose_respects.
  2: exact (kl_bimap_pure_r X (to (@tensor_assoc C _ Y X Y))).
  reflexivity.
Qed.

(**
*** The per-object commutative comonoid on Kl(M)

    copy := kpure copy and discard := kpure discard; every law is the
    pure image of the corresponding base law. 

--------
*** Kl(M) 上的每个对象可交换共形群

 复制 := kpure 复制并丢弃 := kpure 丢弃; 每一条法律都是
 相应基法的纯象。 
*)

Lemma kl_delta_coassoc (x : C) :
  @compose Kleisli _ _ _
    (((kpure copy[x]) ⨂[Kleisli_Monoidal] (@id Kleisli x)))
    (kpure copy[x])
  ≈ @compose Kleisli _ _ _
      (@compose Kleisli _ _ _
         (kpure (from (@tensor_assoc C _ x x x)))
         (((@id Kleisli x) ⨂[Kleisli_Monoidal] (kpure copy[x]))))
      (kpure copy[x]).
Proof.
  rewrite kl_bimap_pure_l, kl_bimap_pure_r.
  rewrite !kl_pure_comp.
  apply kl_pure_eqv.
  exact (@delta_coassoc C _ x (cd_comonoid x)).
Qed.

Lemma kl_delta_counit_left (x : C) :
  @compose Kleisli _ _ _
    (((kpure discard[x]) ⨂[Kleisli_Monoidal] (@id Kleisli x)))
    (kpure copy[x])
  ≈ kpure (from (@unit_left C _ x)).
Proof.
  rewrite kl_bimap_pure_l.
  rewrite kl_pure_comp.
  apply kl_pure_eqv.
  exact (@delta_counit_left C _ x (cd_comonoid x)).
Qed.

Lemma kl_delta_counit_right (x : C) :
  @compose Kleisli _ _ _
    (((@id Kleisli x) ⨂[Kleisli_Monoidal] (kpure discard[x])))
    (kpure copy[x])
  ≈ kpure (from (@unit_right C _ x)).
Proof.
  rewrite kl_bimap_pure_r.
  rewrite kl_pure_comp.
  apply kl_pure_eqv.
  exact (@delta_counit_right C _ x (cd_comonoid x)).
Qed.

Definition Kleisli_cd_comonoid_base (x : C) :
  @Comonoid Kleisli Kleisli_Monoidal x :=
  @Build_Comonoid Kleisli Kleisli_Monoidal x
    (kpure copy[x])
    (kpure discard[x])
    (kl_delta_coassoc x)
    (kl_delta_counit_left x)
    (kl_delta_counit_right x).

Lemma kl_delta_cocommutative (x : C) :
  @compose Kleisli _ _ _ (kpure (@braid C _ x x)) (kpure copy[x])
    ≈ kpure copy[x].
Proof.
  rewrite kl_pure_comp.
  apply kl_pure_eqv.
  exact (@delta_cocommutative_of_ccomon C _ x (cd_comonoid x)).
Qed.

Definition Kleisli_cd_comonoid (x : C) :
  @CommutativeComonoid Kleisli Kleisli_Symmetric x :=
  @Build_CommutativeComonoid Kleisli Kleisli_Symmetric x
    (Kleisli_cd_comonoid_base x)
    (kl_delta_cocommutative x).

(**
*** The CopyDiscard coherence fields

    Each side of each coherence is the pure image of the corresponding
    base composite, so the equations descend along the pure functor.
    [kl_cd_tensor_delta] is the heaviest: the canonical delta routes
    through [mid_swap_inv], transported by [kl_pure_mid_swap_inv]. 

--------
*** CopyDiscard 一致性字段

 每个相干性的每一面都是对应的纯像
 基本复合，因此方程沿着纯函子下降。 
[kl_cd_tensor_delta] 是最重的：规范的 Delta 路线
 通过 [mid_swap_inv]，由 [kl_pure_mid_swap_inv] 传输。 
*)

Lemma kl_cd_tensor_delta (X Y : C) :
  kpure copy[(X ⨂ Y)%object]
    ≈ @canonical_tensor_delta Kleisli Kleisli_Symmetric X Y
        (Kleisli_cd_comonoid_base X) (Kleisli_cd_comonoid_base Y).
Proof.
  transitivity
    (kpure (@canonical_tensor_delta C _ X Y
              (cd_comonoid X) (cd_comonoid Y))).
  { apply kl_pure_eqv.
    exact (cd_tensor_delta X Y). }
  unfold canonical_tensor_delta.
  rewrite kpure_comp_functor.
  apply compose_respects.
  - symmetry.
    exact (kl_pure_mid_swap_inv X Y).
  - symmetry.
    exact (kl_pure_tensor copy[X] copy[Y]).
Qed.

Lemma kl_cd_tensor_epsilon (X Y : C) :
  kpure discard[(X ⨂ Y)%object]
    ≈ @canonical_tensor_epsilon Kleisli Kleisli_Symmetric X Y
        (Kleisli_cd_comonoid_base X) (Kleisli_cd_comonoid_base Y).
Proof.
  transitivity
    (kpure (@canonical_tensor_epsilon C _ X Y
              (cd_comonoid X) (cd_comonoid Y))).
  { apply kl_pure_eqv.
    exact (cd_tensor_epsilon X Y). }
  unfold canonical_tensor_epsilon.
  rewrite kpure_comp_functor.
  apply compose_respects.
  - reflexivity.
  - symmetry.
    exact (kl_pure_tensor discard[X] discard[Y]).
Qed.

Lemma kl_cd_unit_delta :
  kpure copy[@I C _] ≈ kpure (from (@unit_left C _ (@I C _))).
Proof.
  apply kl_pure_eqv.
  exact cd_unit_delta.
Qed.

Lemma kl_cd_unit_epsilon :
  kpure discard[@I C _] ≈ @id Kleisli (@I C _).
Proof.
  transitivity (kpure (@id C (@I C _))).
  - apply kl_pure_eqv.
    exact cd_unit_epsilon.
  - apply kpure_id.
Qed.

(*
The copy-discard structure of Kl(M).  Note what is NOT transported:
   naturality of copy and discard, which CopyDiscard deliberately never
   asks for.  In Kl(M) an effectful morphism need not commute with
   duplication or deletion of its input; the morphisms that do are the
   deterministic ones, and Monad/Thunkable.v identifies the thunkable
   Kleisli morphisms inside them. 

--------
Kl(M) 的复制丢弃结构。 请注意不运输的内容：
 复制和丢弃的自然性，CopyDiscard 故意不这样做
 要求。 在 Kl(M) 中，有效的态射不需要与
 重复或删除其输入； 所做的态射是
 确定性的，Monad/Thunkable.v 识别 thunkable
 它们内部存在Kleisli态射。 
*)
Definition Kleisli_CopyDiscard : @CopyDiscard Kleisli Kleisli_Symmetric :=
  @Build_CopyDiscard Kleisli Kleisli_Symmetric
    Kleisli_cd_comonoid
    kl_cd_tensor_delta
    kl_cd_tensor_epsilon
    kl_cd_unit_delta
    kl_cd_unit_epsilon.

End WithCD.

End WithComm.

End KleisliCommutative.
