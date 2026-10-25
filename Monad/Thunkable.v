Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.CopyDiscard.
Require Import Category.Structure.Monoidal.CopyDiscard.Deterministic.
Require Import Category.Structure.Binoidal.
Require Import Category.Monad.Strong.
Require Import Category.Monad.Strong.Symmetric.
Require Import Category.Monad.Kleisli.
Require Import Category.Monad.Kleisli.Premonoidal.
Require Import Category.Monad.Kleisli.Commutative.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

(**
* Thunkable Kleisli morphisms: Führmann's hierarchy over a strong monad

    nLab: https://ncatlab.org/nlab/show/premonoidal+category
    nLab: https://ncatlab.org/nlab/show/strong+monad
    Reference: Führmann, "Direct models of the computational
               lambda-calculus", MFPS XV, ENTCS 20, 1999
    Reference: Cho & Jacobs, "Disintegration and Bayesian inversion via
               string diagrams", MSCS 29(7):938-971, 2019 (arXiv:1709.00322)

    A Kleisli morphism f : x ~> M y of a strong monad M is THUNKABLE
    (Führmann) when freezing its result into a returned computation is the
    same as returning the frozen computation:

        fmap[M] ret[M] ∘ f ≈ ret[M] ∘ f        (at x ~> M (M y))

    Operationally: running f and then wrapping the value is the same as
    wrapping the entire computation f unrun — f can be turned into a thunk
    without changing its meaning, so f carries no observable effect
    ordering of its own.  This file develops Führmann's hierarchy over the
    library's actual Kleisli premonoidal structure
    (Monad/Kleisli/Premonoidal.v), in three tiers:

    1. Over a bare strong monad on a symmetric monoidal base, the
       unconditional part of the hierarchy:

           pure  ⇒  thunkable  ⇒  central

       [pure_thunkable] is a two-line naturality computation, and
       [thunkable_central] runs both centrality squares of
       [kleisli_central_iff] through Führmann's reassociation lemmas
       ([dstr_reassoc_left] / [dstr_reassoc_left'] and their mirrors,
       Monad/Strong/Symmetric.v): rebracketing a double strength through
       an extra M-layer computes [dstr] when the layer is fmap ret and
       [dstr'] when it is a bare ret, and thunkability equates the two
       layers.  Thunkable morphisms contain the identities
       ([thunkable_id]) and are closed under Kleisli composition
       ([thunkable_comp]) and under postcomposition with pure maps
       ([thunkable_fmap_post]), so they form a wide subcategory [Thunk]
       of Kl(M) through Construction/Subcategory.v — sitting inside the
       centre Z(Kl(M)) (the [CentralSub] of Structure/Binoidal/Central.v
       at [Kleisli_Binoidal]) by [thunkable_central].

    2. Over a copy-discard base, the bridge into categorical probability:
       a thunkable morphism is copyable and discardable — the two
       Cho-Jacobs squares stated against the double strength — PROVIDED
       the base copy and discard are natural ([copy_nat], [discard_nat]).
       The engine is the slide lemma [thunkable_slide]: any G that is an
       algebra-map-on-returns (G ∘ ret ≈ ret ∘ g) slides across a
       thunkable f as the pure map g.  The two naturality hypotheses are
       genuinely needed and genuinely available: they hold automatically
       in cartesian bases ([CD_of_Cartesian] in
       Structure/Monoidal/CopyDiscard/Proofs.v, where copy is the natural
       diagonal), and the discard half holds in any Markov category
       ([discard_natural] in Structure/Monoidal/Markov.v).  They are NOT
       derivable in a bare [CopyDiscard] base: taking M := Id makes every
       morphism thunkable, so an unconditional implication would force
       every morphism of every copy-discard category to be a comonoid
       homomorphism — exactly the naturality that [CopyDiscard]
       deliberately never asks for (its negative space is what carves out
       the deterministic morphisms in the first place).

    3. Over a commutative strong monad on a copy-discard base, the honest
       form of the thunkable-determinism statement:
       [thunkable_deterministic] lands every thunkable Kleisli morphism in
       the Cho-Jacobs deterministic class of the descended copy-discard
       structure [Kleisli_CopyDiscard] (Monad/Kleisli/Commutative.v) —
       i.e. inside the wide subcategory [Det] of Kl(M) — and
       [pure_deterministic] transports base-deterministic morphisms along
       the pure functor.  The bridging lemmas [kl_copyable_eq] and
       [kl_discardable_eq] identify the two comonoid-homomorphism squares
       of Kl(M) with [copyable] and [discardable] on the nose.

    Strictness of the hierarchy (recorded as prose, not formalized):
    both inclusions of the thunkable class — inside the centre (tier 1)
    and inside the deterministic class (tier 3) — are strict in general.
    Central but not thunkable: for the writer monad M x = x × W over a
    nontrivial commutative monoid W (in Sets), M is commutative, so
    EVERY Kleisli morphism is central ([kleisli_all_central],
    Monad/Kleisli/Commutative.v), yet the map x ↦ (x, w) with w ≠ e is
    not thunkable, because thunkability forces the written w to equal e;
    Führmann (1999) draws the same separation for continuation monads.
    Deterministic but not thunkable: for the read-only state monad
    M x = x × x (reader along a two-element environment, in Sets), every
    Kleisli morphism is copyable and discardable, but only the morphisms
    that ignore the read value are thunkable (Moss & Perrone,
    "Probability monads with submonads of deterministic states",
    LICS 2022, Theorem 3.14 and Example 3.16).  The converse of
    [thunkable_deterministic] is therefore not provable, and the
    deterministic class is in general strictly larger than the thunkable
    one. 

--------
* Thunkable Kleisli态射: f ü hrmann在强单子上的层次结构

nLab: https://ncatlab.org/nlab/show/premonoidal+category
nLab: https://ncatlab.org/nlab/show/strong+monad
参考: f ü hrmann，“计算的直接模型”
“lambda-演算”，MFPS XV，ENTCS 20, 1999
参考: Cho & Jacobs，“通过分解和贝叶斯反演
字符串图 “，MSCS 29(7):938-971，2019 (arXiv:1709.00322)

强单子M的Kleisli态射f: x ~&gt; M y是雷霆的
(F ü hrmann) 将其结果冻结到返回的计算中时，
与返回冻结计算相同:

fmap[M] ret[M] ○ f ≈ ret[M] ○ f (在x ~&gt; M (M y))

操作上: 运行f，然后包装值与
包装整个计算f unrun-f可以变成一个thunk
在不改变其含义的情况下，因此f不会产生可观察到的影响
自己的订单。此文件开发了f ü hrmann在
图书馆的实际Kleisli前单位体结构
(Monad/Kleisli/Premonoidal.v)，分为三层:

1.在对称单线基数上的裸露强单子上，
层次结构的无条件部分:

纯 ⇒ thunkable ⇒ 中央

[pure_thunkable]是一个两行自然计算，并且
[thunkable_central]运行的两个中心平方
[kleisli_central_iff]通过f ü hrmann的重新关联引理
([dstr_reassoc_left]/[dstr_reassoc_left']及其镜像，
单子/强/对称。v): 通过
当层为fmap ret时，额外的M层计算[dstr]，并且
[dstr']当它是一个裸露的ret时，和thunkability等同于两个
层。Thunkable态射包含身份
([thunkable_id])，并在Kleisli组合下关闭
([thunkable_comp]) 和postcomposition与纯地图
([thunkable_fmap_post])，因此它们构成了一个广泛的子类别[Thunk]
Kl(M) 通过建筑/子类。v-坐在里面
中心Z(Kl(M)) (结构的[CentralSub]/二线/中心.v
在[Kleisli_Binoidal]) 由[thunkable_central]。

2.在复制-丢弃基础上，桥成分类概率:
雷霆的形态是可复制和可丢弃的-这两个
Cho-jacobs squares反对双重力量-提供
基本复制和丢弃是自然的 ([copy_nat]，[discard_nat])。引擎是幻灯片引理[thunkable_slide]: 任何G是一个
代数映射返回 (G ○ ret ≈ ret ○ g) 滑过
将f作为纯映射g。这两个自然假设是
真正需要和真正可用: 它们自动持有
在笛卡尔基 ([CD_of_Cartesian]在
Structure/Monoidal/CopyDiscard/Proofs.v，其中copy是自然的
对角线)，并且丢弃的一半在任何马尔可夫类别中都成立
([discard_natural] in Structure/Monoidal/Markov.v)。
他们不是
可在一个裸露的[CopyDiscard]基础中导出: 取M := Id使每个
态射是令人难以置信的，所以无条件的暗示会迫使
每个复制丢弃类别的每个射态都是comonoid
同态-正是[CopyDiscard]的自然性
故意从不要求 (它的负空间是雕刻出来的
首先是确定性态射)。

3.在复制丢弃基础上的可交换强monad上，诚实的
雷霆决定论声明的形式:
[thunkable_deterministic]将所有可雷霆的Kleisli态射降落在
下降复制丢弃的cho-jacobs确定性类
结构[Kleisli_CopyDiscard] (Monad/Kleisli/可交换.v)-
即在Kl(M) 的宽子类[Det]中-和
[pure_deterministic]沿传输基本确定性态射
纯函子。桥接引理[kl_copyable_eq]和
[kl_discardable_eq]识别两个同态同态正方形
Kl(M) 的鼻子上有[copyable]和[discardable]。

等级的严格性 (记录为散文，未形式化):
雷霆级的两个内含物-中心内 (第1层)
在确定性类 (第3层) 中-通常是严格的。
中央但不为thunkable: 对于作家monad M x = x × W
非平凡可交换单项W (在集合中)，M是可交换的，因此
每个Kleisli态射都是中心 ([kleisli_all_central]，
Monad/Kleisli/可交换.v)，然而w ≠ e的映射x ↦ (x，w) 是
不可雷霆，因为雷霆迫使写入的w等于e；
F ü hrmann (1999) 对连续单子进行了相同的分离。
确定性但不可雷控: 对于只读状态monad
M x = x × x (沿二元环境的读取器，以集合为单元)，每
Kleisli态射是可复制和可丢弃的，但只有态射
忽略读取的值是可理解的 (Moss & Perrone，
“具有确定性状态的子子的概率单子”，
LICS 2022、定理3.14和示例3.16)。的反面
因此，[thunkable_deterministic]是不可证明的，并且
确定性类通常严格大于thunkable
一。 
*)

Section Thunkable.

Context {C : Category}.
Context `{SM : @SymmetricMonoidal C}.
Context {M : C ⟶ C}.
Context `{SMon : @StrongMonad C _ M}.

(* ------------------------------------------------------------------ *)
(** ** Tier 1: thunkability over a bare strong monad.                   / ** 第一层：对裸露的强单子的可重用性。*)
(* ------------------------------------------------------------------ *)

(*
Führmann's definition: f can be frozen into a thunk.  The equation
   lives at x ~> M (M y): on the left the computation runs and its value
   is returned; on the right the whole computation is returned unrun. 

--------
Führmann 的定义：f 可以被冻结成 thunk。 等式
 位于 x ~> M (M y)：左侧是计算运行及其值
 被退回； 在右侧，整个计算未运行就返回。 
*)
Definition thunkable {x y : C} (f : x ~> M y) : Type :=
  fmap[M] ret[M] ∘ f ≈ ret[M] ∘ f.

(* Thunkability is a property of the ≈-class of a morphism.  / 可替换性是态射 ≈ 类的一个属性。*)
Lemma thunkable_respects {x y : C} {f g : x ~> M y} :
  f ≈ g → thunkable f → thunkable g.
Proof.
  unfold thunkable.
  intros E tf.
  now rewrite <- E.
Qed.

(*
The Kleisli identity is thunkable: both sides are the unit naturality
   square [fmap_ret] instantiated at the unit itself. 

--------
Kleisli恒等式是可thunkable的：两边都是单位自然性
 square [fmap_ret] 在单元本身实例化。 
*)
Lemma thunkable_id {x : C} : thunkable (ret[M] : x ~{C}~> M x).
Proof.
  unfold thunkable.
  symmetry.
  apply fmap_ret.
Qed.

(*
Every pure morphism is thunkable: push the outer unit across f with
   [fmap_ret]. 

--------
每个纯态射都是可thunkable的：将外部单元推过f
 [fmap_ret]。 
*)
Lemma pure_thunkable {x y : C} (f : x ~{C}~> y) : thunkable (kpure f).
Proof.
  unfold thunkable, kpure.
  rewrite comp_assoc.
  rewrite <- fmap_ret.
  now rewrite comp_assoc.
Qed.

(*
Thunkable morphisms are closed under Kleisli composition
   join ∘ fmap f ∘ g.  Both sides normalize to fmap f ∘ g: the left via
   naturality of join and [tf] under the doubled functor, collapsing with
   [join_fmap_ret]; the right by walking the unit leftwards across join
   and fmap f with [fmap_ret], meeting [tg], and cancelling with
   [join_ret] inside the fused fmap argument. 

--------
可分值态射在 Kleisli 组合下是封闭的
 连接 ∘ fmap f ∘ g。 两边归一化为 fmap f ∘ g：左边的via
 双函子下 join 和 [tf] 的自然性，崩溃
 [join_fmap_ret]； 向右移动单元向左穿过连接
 和 fmap f 与 [fmap_ret]，满足 [tg]，并取消
 [join_ret] 位于融合的 fmap 参数内。 
*)
Lemma thunkable_comp {x y z : C} {f : y ~> M z} {g : x ~> M y} :
  thunkable f → thunkable g → thunkable (join[M] ∘ fmap[M] f ∘ g).
Proof.
  intros tf tg.
  unfold thunkable in *.
  transitivity (fmap[M] f ∘ g).
  - (* fmap ret ∘ (join ∘ fmap f ∘ g) ≈ fmap f ∘ g *)
    rewrite !comp_assoc.
    rewrite <- join_fmap_fmap.
    rewrite <- (comp_assoc join[M]).
    rewrite <- fmap_comp.
    rewrite tf.
    rewrite fmap_comp.
    rewrite comp_assoc.
    rewrite join_fmap_ret.
    now rewrite id_left.
  - (* fmap f ∘ g ≈ ret ∘ (join ∘ fmap f ∘ g) *)
    symmetry.
    rewrite !comp_assoc.
    rewrite fmap_ret.
    rewrite <- (comp_assoc (fmap[M] join[M])).
    rewrite fmap_ret.
    rewrite <- !comp_assoc.
    rewrite <- tg.
    rewrite (comp_assoc (fmap[M] (fmap[M] f))).
    rewrite <- fmap_comp.
    rewrite comp_assoc.
    rewrite <- fmap_comp.
    rewrite <- fmap_ret.
    rewrite comp_assoc.
    rewrite join_ret.
    now rewrite id_left.
Qed.

(*
Thunkable morphisms absorb pure postcomposition: fmap u ∘ f is again
   thunkable.  The unit walks across u by [fmap_ret], meets [tf], and
   walks back out across fmap u. 

--------
可thunkable态射吸收纯后合成： fmap u ∘ f 又是
 可thunkable。 该装置通过 [fmap_ret] 穿过 u，遇到 [tf]，并且
 穿过 fmap u 往回走。 
*)
Lemma thunkable_fmap_post {x y z : C} (u : y ~{C}~> z) {f : x ~> M y} :
  thunkable f → thunkable (fmap[M] u ∘ f).
Proof.
  intro tf.
  unfold thunkable in *.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite fmap_ret.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite tf.
  rewrite comp_assoc.
  rewrite <- fmap_ret.
  now rewrite <- comp_assoc.
Qed.

(*
Führmann's theorem: every thunkable morphism is central in Kl(M).
   Through [kleisli_central_iff] each centrality square asks that [dstr]
   and [dstr'] agree on a tensor with f in one factor; the reassociation
   lemmas of Monad/Strong/Symmetric.v rewrite [dstr ∘ (f ⨂ g)] as the
   rebracketed word at (fmap ret ∘ f) ⨂ g and [dstr' ∘ (f ⨂ g)] as the
   same word at (ret ∘ f) ⨂ g, and thunkability of f equates the two
   insertions.  No commutativity of M enters. 

--------
Führmann 定理：每个可替换态射都是 Kl(M) 的中心。 
通过 [kleisli_central_iff] 每个中心性方块要求 [dstr]
 和 [dstr'] 在一个因子中具有 f 的张量上达成一致； 重新关联
 Monad/Strong/Symmetric.v 的引理将 [dstr ∘ (f ⨂ g)] 重写为
 (fmap ret ∘ f) ⨂ g 处的重新括号单词和 [dstr' ∘ (f ⨂ g)] 作为
 (ret ∘ f) ⨂ g 处的同一个单词，并且 f 的可替换性等于两者
 插入。 M 没有交换律进入。 
*)
Theorem thunkable_central {x y : C} (f : x ~> M y) :
  thunkable f → @central Kleisli Kleisli_Binoidal x y f.
Proof.
  intros tf.
  apply kleisli_central_iff; intros c d g.
  split.
  - rewrite <- (dstr_reassoc_left f g).
    rewrite <- (dstr_reassoc_left' f g).
    now rewrite tf.
  - rewrite <- (dstr'_reassoc_right g f).
    rewrite <- (dstr'_reassoc_right' g f).
    now rewrite tf.
Qed.

(*
Feeding returned values into BOTH factors of the double strength
   leaves a single unit — [dstr_ret_ret] (Monad/Strong/Symmetric.v), the
   unit law of the lax monoidal structure that [dstr] puts on M, needed
   below for the copyability of thunkable morphisms. 

--------
将返回值输入到双倍强度的两个因子中
 留下一个单元——[dstr_ret_ret] (Monad/Strong/Symmetric.v)，
 [dstr]放在M上的松散幺半群结构的单位律，需要
 下面是可复制态射的可复制性。 
*)

(* ------------------------------------------------------------------ *)
(** ** The wide subcategory Thunk of thunkable morphisms.               / ** 可 thunkable 态射的广泛子类别 Thunk。*)
(* ------------------------------------------------------------------ *)

(*
[thunkable_id] and [thunkable_comp] are exactly the closure conditions
   of Construction/Subcategory.v, read at the definitional Kleisli
   composite (@compose Kleisli is join ∘ fmap f ∘ g on the nose), so the
   thunkable morphisms over ALL objects form a wide subcategory of Kl(M),
   Führmann's category of thunkable maps.  The packaging mirrors
   [DeterministicSub]/[Det] of CopyDiscard/Deterministic.v and
   [CentralSub]/[Centre] of Structure/Binoidal/Central.v.

   Hierarchy note: the shom-collection of [ThunkableSub] includes into
   that of [CentralSub] at [Kleisli_Binoidal] — that inclusion IS
   [thunkable_central] — so Thunk sits inside the centre Z(Kl(M)) as wide
   subcategories of Kl(M); and every pure morphism [kpure f] lands in
   Thunk by [pure_thunkable]. 

--------
[thunkable_id] 和 [thunkable_comp] 正是关闭条件
 Construction/Subcategory.v，请阅读定义 Kleisli
 复合（@compose Kleisli 是在鼻子上连接 ∘ fmap f ∘ g），所以
 所有对象上的可thunkable态射形成了Kl(M)的广泛子类别，
 Führmann 的可转换映射类别。 包装镜子
 CopyDiscard/Deterministic.v 的 [DeterministicSub]/[Det] 和
 Structure/Binoidal/Central.v 的 [CentralSub]/[Centre]。 

层次结构注释：[ThunkableSub] 的 shom 集合包含到
 [CentralSub] 的 [Kleisli_Binoidal] 的内容 — 包含是
 [thunkable_central] — 因此 Thunk 位于中心 Z(Kl(M)) 内，宽度与 Z(Kl(M)) 一样宽
 Kl(M) 的子类别； 每个纯态射 [kpure f] 都落在
 [pure_thunkable] 的 Thunk。 
*)

Program Definition ThunkableSub : Subcategory Kleisli := {|
  sobj  := fun _ => poly_unit;
  shom  := fun x y _ _ f => thunkable f;
  scomp := fun _ _ _ _ _ _ _ _ tf tg => thunkable_comp tf tg;
  sid   := fun _ _ => thunkable_id
|}.

Definition Thunk : Category := Sub Kleisli ThunkableSub.

Lemma Thunk_wide : Wide Kleisli ThunkableSub.
Proof. intro x; exact ttt. Qed.

(*
The inclusion Thunk ⟶ Kl(M) is the generic faithful
   [Incl Kleisli ThunkableSub] from Construction/Subcategory.v. 

--------
包含 Thunk ⟶ Kl(M) 是通用忠实的
 来自 Construction/Subcategory.v 的 [Incl Kleisli ThunkableSub]。 
*)

(* ------------------------------------------------------------------ *)
(** ** Tier 2: copyability and discardability over a CD base.           / ** 第 2 层：基于 CD 的可复制性和可丢弃性。*)
(* ------------------------------------------------------------------ *)

Section ThunkableCD.

Context `{CD : @CopyDiscard C _}.

(*
The two naturality hypotheses.  [CopyDiscard] itself deliberately
   never demands them — their absence for general morphisms is what
   makes the deterministic subclass meaningful — but tier 2 genuinely
   needs them: with M := Id every morphism is thunkable, so deriving
   copyable/discardable from thunkable over a bare CD base would force
   every morphism of every copy-discard category into a comonoid
   homomorphism, which bare CD does not grant.  Both hypotheses hold in
   cartesian bases ([CD_of_Cartesian] in CopyDiscard/Proofs.v: copy is
   the natural diagonal, discard the eliminate of the terminal unit),
   and [discard_nat] alone holds in every Markov category
   ([discard_natural], Structure/Monoidal/Markov.v). 

--------
两种自然性假设。 [CopyDiscard]本身是故意的
 从不要求它们——它们缺乏一般态射是什么
 使确定性子类有意义——但真正的第二层
 需要它们：使用 M := Id 每个态射都是可替换的，所以推导
 从裸 CD 底座上的可复制/可丢弃将强制
 将每个复制丢弃类别的每个态射都转换为共形
 同态，裸 CD 不具备同态性。 两个假设都成立
 笛卡尔基（CopyDiscard/Proofs.v 中的 [CD_of_Cartesian]：副本是
 自然对角线，丢弃终端单元的消除），
 仅 [discard_nat] 就满足每个马尔可夫类别
 （[discard_natural]，结构/Monoidal/Markov.v）。 
*)

Hypothesis copy_nat : ∀ (x y : C) (u : x ~{C}~> y),
  copy[y] ∘ u ≈ (u ⨂ u) ∘ copy[x].

Hypothesis discard_nat : ∀ (x y : C) (u : x ~{C}~> y),
  discard[y] ∘ u ≈ discard[x].

(*
The slide lemma, the engine of tier 2: if G agrees with the pure map
   g on returned values (G ∘ ret ≈ ret ∘ g), then G slides across any
   thunkable f as fmap g.  Proof: conjugate [tf] with fmap G, exchange
   G against g inside the fused functor argument with [algG], convert
   the surviving head fmap ret into a bare ret with
   [thunkable_fmap_post], and cancel the resulting unit under join with
   [join_ret]. 

--------
幻灯片引理，第 2 层的引擎：如果 G 与纯映射一致
 g 对返回值 (G ∘ ret ≈ ret ∘ g)，然后 G 滑过任何
 可将 f 转换为 fmap g。 证明：将 [tf] 与 fmap G 共轭，交换
 G 与 [algG] 的融合函子参数内的 g 相对应，转换
 幸存的头 fmap ret 变成裸 ret
 [thunkable_fmap_post]，并取消 join with 下的结果单元
 [join_ret]。 
*)
Lemma thunkable_slide {a b c : C} (f : a ~> M b) (tf : thunkable f)
      (G : M b ~{C}~> M c) (g : b ~{C}~> c)
      (algG : G ∘ ret[M] ≈ ret[M] ∘ g) :
  G ∘ f ≈ fmap[M] g ∘ f.
Proof.
  assert (E : ret[M] ∘ (fmap[M] g ∘ f) ≈ ret[M] ∘ (G ∘ f)).
  { transitivity (fmap[M] G ∘ (fmap[M] ret[M] ∘ f)).
    - rewrite <- (thunkable_fmap_post g tf).
      rewrite !comp_assoc.
      rewrite <- !fmap_comp.
      rewrite algG.
      reflexivity.
    - rewrite tf.
      rewrite comp_assoc.
      rewrite <- fmap_ret.
      now rewrite <- comp_assoc. }
  rewrite <- (id_left (G ∘ f)).
  rewrite <- (@join_ret C M _ c).
  rewrite <- comp_assoc.
  rewrite <- E.
  rewrite comp_assoc.
  rewrite join_ret.
  now rewrite id_left.
Qed.

(*
The Cho-Jacobs squares for a Kleisli morphism, stated at the double
   strength: copying the output of f agrees with running f twice on a
   copied input (combined by [dstr]), and discarding the output of f
   agrees with discarding its input outright. 

--------
Kleisli 态射的 Cho-Jacobs 平方，在双精度处表示
 强度：复制 f 的输出与在 a 上运行 f 两次一致
 复制输入（由 [dstr] 组合），并丢弃 f 的输出
 同意彻底放弃其输入。 
*)
Definition copyable {x y : C} (f : x ~> M y) : Type :=
  dstr ∘ (f ⨂ f) ∘ copy[x] ≈ fmap[M] copy[y] ∘ f.

Definition discardable {x y : C} (f : x ~> M y) : Type :=
  fmap[M] discard[y] ∘ f ≈ ret[M] ∘ discard[x].

(*
Thunkable morphisms are copyable: naturality of copy at f turns the
   copied-input side into (dstr ∘ copy[M y]) ∘ f, and that G slides
   across f as fmap copy[y] — its algebra-map equation is naturality of
   copy at ret followed by the double-strength unit law
   [dstr_ret_ret]. 

--------
可 thunkable 态射是可复制的： f 处复制的自然性将
 将输入端复制到 (dstr ∘ copy[M y]) ∘ f，并且 G 滑动
 across f as fmap copy[y] — 其代数映射方程的自然性是
 复制 ret 后遵循双强度单位定律
 [dstr_ret_ret]。 
*)
Theorem thunkable_copyable {x y : C} (f : x ~> M y) :
  thunkable f → copyable f.
Proof using C CD M SM SMon copy_nat.
  intro tf.
  unfold copyable.
  rewrite <- comp_assoc.
  rewrite <- (copy_nat x (M y) f).
  rewrite comp_assoc.
  apply (thunkable_slide f tf (dstr ∘ copy[M y]) copy[y]).
  rewrite <- comp_assoc.
  rewrite (copy_nat y (M y) ret[M]).
  rewrite comp_assoc.
  rewrite dstr_ret_ret.
  reflexivity.
Qed.

(*
Thunkable morphisms are discardable: the mirror argument, sliding
   G := ret ∘ discard[M y] across f as fmap discard[y]; both the
   algebra-map equation and the final collapse are [discard_nat]. 

--------
可 thunkable 态射是可丢弃的：镜像论证、滑动
 G := ret ∘discard[M y] 通过 f 作为 fmapdiscard[y]; 两者都
 代数映射方程和最终崩溃是 [discard_nat]。 
*)
Theorem thunkable_discardable {x y : C} (f : x ~> M y) :
  thunkable f → discardable f.
Proof using C CD M SM SMon discard_nat.
  intro tf.
  unfold discardable.
  assert (algG : (ret[M] ∘ discard[M y]) ∘ ret[M] ≈ ret[M] ∘ discard[y]).
  { rewrite <- comp_assoc.
    now rewrite (discard_nat y (M y) ret[M]). }
  rewrite <- (thunkable_slide f tf (ret[M] ∘ discard[M y]) discard[y] algG).
  rewrite <- comp_assoc.
  now rewrite (discard_nat x (M y) f).
Qed.

(*
Pure morphisms are copyable and discardable, through
   [pure_thunkable]. 

--------
纯态射是可复制和可丢弃的，通过
 [pure_thunkable]。 
*)
Corollary pure_copyable {x y : C} (f : x ~{C}~> y) : copyable (kpure f).
Proof using C CD M SM SMon copy_nat.
  apply thunkable_copyable, pure_thunkable.
Qed.

Corollary pure_discardable {x y : C} (f : x ~{C}~> y) :
  discardable (kpure f).
Proof using C CD M SM SMon discard_nat.
  apply thunkable_discardable, pure_thunkable.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Tier 3: the bridge to the deterministic class of Kl(M).          / ** 第 3 层：通往 Kl(M) 确定性类的桥梁。*)
(* ------------------------------------------------------------------ *)

Section ThunkableDeterministic.

(*
When M is commutative, Kl(M) is itself a copy-discard category
   ([Kleisli_CopyDiscard], Monad/Kleisli/Commutative.v: copy and discard
   are the pure images of the base generators), and the Cho-Jacobs
   deterministic predicate of CopyDiscard/Deterministic.v applies to
   Kleisli morphisms.  This section identifies its two comonoid-
   homomorphism squares with [copyable] and [discardable], lands every
   thunkable morphism in the deterministic class — the honest form of
   the thunkable-determinism bridge; see the header for why the M := Id
   reading rules out an unconditional converse-free statement over bare
   CD — and transports base-deterministic morphisms along the pure
   functor. 

--------
当 M 是可交换的时，Kl(M) 本身就是一个复制丢弃范畴
 （[Kleisli_CopyDiscard]，Monad/Kleisli/Commutative.v：复制并丢弃
 是基础生成器的纯图像），以及 Cho-Jacobs
 CopyDiscard/Deterministic.v 的确定性谓词适用于
 Kleisli态射。 本节确定了它的两个共形-
 同态与 [copyable] 和 [discardable] 平方，满足每个
 确定性类中的可thunkable态射——诚实的形式
 thunkable 决定论桥梁； 请参阅标题了解为什么 M := Id
 阅读排除了对 bare 的无条件无逆向陈述
 CD — 并沿着纯态传输基确定性态射
 函子。 
*)

Hypothesis comm : commutative_sm (M:=M).

(*
The δ-square of the descended comonoid at f is exactly [copyable] f:
   the pure exchange laws strip the units, and the induced tensor
   computes the double strength ([kleisli_bimap_dstr]). 

--------
f 处的下降共形函数的 δ 平方正好是 [copyable] f：
 纯交换定律剥离单位，以及诱导张量
 计算双倍强度 ([kleisli_bimap_dstr])。 
*)
Lemma kl_copyable_eq {x y : C} (f : x ~{Kleisli}~> y) :
  (@compose Kleisli _ _ _ (kpure copy[y]) f
     ≈ @compose Kleisli _ _ _
         (f ⨂[Kleisli_Monoidal comm] f) (kpure copy[x]))
  ↔ copyable f.
Proof.
  split; intro E.
  - unfold copyable.
    rewrite kl_pure_post in E.
    rewrite kl_pure_pre in E.
    rewrite (kleisli_bimap_dstr comm f f) in E.
    symmetry; exact E.
  - rewrite kl_pure_post.
    rewrite kl_pure_pre.
    rewrite (kleisli_bimap_dstr comm f f).
    symmetry; exact E.
Qed.

(*
The ε-square of the descended comonoid at f is exactly
   [discardable] f. 

--------
f 处的下降共形函数的 ε 平方正好是
 [discardable] f. 
*)
Lemma kl_discardable_eq {x y : C} (f : x ~{Kleisli}~> y) :
  (@compose Kleisli _ _ _ (kpure discard[y]) f ≈ kpure discard[x])
  ↔ discardable f.
Proof.
  split; intro E.
  - unfold discardable.
    rewrite kl_pure_post in E.
    exact E.
  - rewrite kl_pure_post.
    exact E.
Qed.

(*
The bridge: every thunkable Kleisli morphism is deterministic in the
   Cho-Jacobs sense for the descended copy-discard structure on Kl(M) —
   i.e. it lies in the wide subcategory [Det] of Kl(M) built by
   CopyDiscard/Deterministic.v at [Kleisli_CopyDiscard].  Both comonoid-
   homomorphism squares are tier 2 through the [kl_*_eq]
   identifications. 

--------
桥梁：每个可 thunkable 的 Kleisli 态射在
 Cho-Jacobs 对 Kl(M) 上下降的复制丢弃结构的理解 —
 即它位于 Kl(M) 的宽子类别 [Det] 中，该子类别由
 [Kleisli_CopyDiscard] 上的 CopyDiscard/Deterministic.v。 两者都是共形-
 同态方块是 [kl_*_eq] 的第 2 层
 身份证明。 
*)
Theorem thunkable_deterministic {x y : C} (f : x ~{Kleisli}~> y) :
  thunkable f →
  @deterministic Kleisli (Kleisli_Symmetric comm)
    (Kleisli_CopyDiscard comm (CD:=CD)) x y f.
Proof using C CD M SM SMon comm copy_nat discard_nat.
  intro tf.
  split.
  - exact (snd (kl_copyable_eq f) (thunkable_copyable f tf)).
  - exact (snd (kl_discardable_eq f) (thunkable_discardable f tf)).
Qed.

(*
The two squares of a pure image, as standalone transfers: the pure
   functor carries the base squares to Kl(M) through [kl_pure_comp] and
   [kl_pure_tensor]. 

--------
纯图像的两个方块，作为独立的传输：纯图像
 函子通过 [kl_pure_comp] 将基数方块传送到 Kl(M) 并
 [kl_pure_tensor]。 
*)
Lemma pure_hom_delta {x y : C} (f : x ~{C}~> y)
      (Fd : copy[y] ∘ f ≈ (f ⨂ f) ∘ copy[x]) :
  @compose Kleisli _ _ _ (kpure copy[y]) (kpure f)
    ≈ @compose Kleisli _ _ _
        ((kpure f) ⨂[Kleisli_Monoidal comm] (kpure f)) (kpure copy[x]).
Proof.
  rewrite (kl_pure_tensor comm f f).
  rewrite !kl_pure_comp.
  apply kl_pure_eqv.
  exact Fd.
Qed.

Lemma pure_hom_epsilon {x y : C} (f : x ~{C}~> y)
      (Fe : discard[y] ∘ f ≈ discard[x]) :
  @compose Kleisli _ _ _ (kpure discard[y]) (kpure f) ≈ kpure discard[x].
Proof.
  rewrite kl_pure_comp.
  apply kl_pure_eqv.
  exact Fe.
Qed.

(*
Determinism transports along the pure functor: a base-deterministic
   morphism has a deterministic pure image in Kl(M). 

--------
确定性沿着纯函子传输：基确定性
 态射在 Kl(M) 中具有确定性的纯图像。 
*)
Theorem pure_deterministic {x y : C} (f : x ~{C}~> y) :
  @deterministic C SM CD x y f →
  @deterministic Kleisli (Kleisli_Symmetric comm)
    (Kleisli_CopyDiscard comm (CD:=CD)) x y (kpure f).
Proof.
  intros [Fd Fe].
  split.
  - exact (pure_hom_delta f Fd).
  - exact (pure_hom_epsilon f Fe).
Qed.

End ThunkableDeterministic.

End ThunkableCD.

End Thunkable.
