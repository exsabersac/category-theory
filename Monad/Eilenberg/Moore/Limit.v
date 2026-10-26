Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.

Generalizable All Variables.

(** * Limits of algebras are computed on carriers  / * 代数的极限是在载体上计算的*)

(*
nLab: https://ncatlab.org/nlab/show/created+limit
   nLab: https://ncatlab.org/nlab/show/Eilenberg-Moore+category#limits
   Mac Lane: Categories for the Working Mathematician, 2nd ed. (GTM 5),
             §VI.2 Theorem 1 and the §V.1 creation vocabulary (p. 112)
   Mac Lane: ibid., §VI.2 Exercise 2 (book p. 142, PDF p. 151;
             catalog item maclane:VI.2:ex2), “Show that G^T : X^T → X
             creates limits”

   CORRECTION (#467): the citation above names Theorem 1 as its only
   §VI.2 source.  That theorem (book p. 140, “Every monad is defined by
   its T-algebras”) builds X^T, G^T and the adjunction F^T ⊣ G^T; the
   statement this file proves is Exercise 2 of the same section, cited
   on the line added after it.  Mac Lane's §V.1 Definition (p. 112) is
   unnumbered and numbers its clauses (i) and (ii); the clause-by-clause
   map is the paragraph MAC LANE'S DEFINITION, CLAUSE BY CLAUSE below.

   For any monad T on D, the forgetful functor [EM_Forget T] STRICTLY
   creates every limit: given a limiting cone over [EM_Forget T ◯ K]
   downstairs, the mediating map into its apex from the cone whose legs are
   [t_alg ∘ fmap[T] π] is an algebra structure, the resulting cone upstairs
   lies over the given one on the nose ([em_over_obj] and [em_over_legs] are
   both [eq_refl], because EM_Forget's object map is the first projection),
   it is limiting ([em_created]), its structure map is the only one over
   that cone ([em_alg_unique]), and a cone upstairs whose image is limiting
   is itself limiting ([em_reflects]).

   On the house rule that morphisms are compared with [≈]: [em_over_legs]
   is the one statement here that writes [=] between morphisms, and it does
   so because both sides are the SAME term — the witness is [eq_refl].  It
   records Mac Lane's [F σ = τ] at full strength, which is strictly
   stronger than the [≈] the class asks for; every law, every proof and the
   [StrictLift] leg clause consumed by [em_strict_lift] use [≈].

   MAC LANE'S DEFINITION, CLAUSE BY CLAUSE (#467).  The Definition on
   p. 112 (PDF p. 121), read from the page image: “A functor V: A → X
   creates limits for a functor F: J → A if (i) To every limiting cone
   τ: x →· VF in X there is exactly one pair ⟨a, σ⟩ consisting of an
   object a ∈ A with Va = x and a cone σ: a →· F with Vσ = τ, and if,
   moreover, (ii) This cone σ: a →· F is a limiting cone in A.”  Here V
   is [EM_Forget T], F is [K] and τ is the given limiting cone [N] (or
   the cone of [L]).  Test/ProbeEMCreates467.v restates each [eq_refl]
   strength below as a control, pins R1 as a refusal, and restates the
   two refutations against their constants.

   - (i), existence of a with Va = x: at [eq_refl].  [em_over_obj], the
     [slift_eq] of [em_strict_lift] (which IS [eq_refl]), and the iso of
     the iso-invariant class, [creates_lift_over] of
     [em_forget_CreatesLimit], whose forward map is [id] on the nose.
   - (i), existence of σ with Vσ = τ: at [eq_refl] leg by leg, against
     the GIVEN cone.  [em_over_legs]; the same through the class
     projection [screates] and as the leg family [fun j => …].  The image
     cone as a RECORD is not [eq_refl] to the given cone: apex and legs
     convert, and the coherence field does not (probe R1).  [FCone]'s
     coherence is an application of [fcone_coherence], a [Qed] lemma
     whose body is a rewrite chain over D's abstract hom-setoids; N's is
     a stuck projection of the variable N.  The cause is structural,
     argued so: made transparent, the chain would still not convert to
     that projection.  It is not measured by a full flip.
   - (i), “exactly one pair”: at [≈] only.  [em_alg_unique] at the
     pinned carrier [vertex_obj[L]], and [em_lift_alg_unique] below at
     the carrier of an arbitrary [StrictLift]: that lift is isomorphic in
     [EilenbergMoore T] to the created apex, by an isomorphism whose
     underlying map is ≈ the transport [slift_iso].  The class form is
     Structure/Limit/Creation.v's [screates_lift_unique] at
     [em_forget_StrictlyCreatesLimit T K]: a cone upstairs whose image is
     cone-isomorphic to N is cone-isomorphic to the created lift.
     [em_lift_alg_unique] specialises it to a [StrictLift] and names the
     underlying map of the isomorphism, ≈ the transport; its type is an
     isomorphism of algebras, without the cone compatibility a
     [ConeIso] carries.  σ's legs are then determined at [≈] by
     [slift_legs], since arrows of [EilenbergMoore T] are compared by
     their underlying maps.  Examples.v instantiates it at [Sets]
     ([em_lift_alg_unique_Sets]), at an indiscrete carrier where its
     [≈]-conclusion holds of every map: the instance witnesses the
     premise, a strict lift other than the created one.
     The on-the-nose form, with [=] on the apex for pairs whose legs
     agree with τ by [=], is REFUTED without axioms in
     Monad/Eilenberg/Moore/Limit/Examples.v: [em_lift_not_unique_leibniz],
     at [Sets] with the identity monad and the indiscrete two-point
     setoid, whose two structure maps [id] and [const true] both lift one
     limiting cone with legs equal on the nose, and
     [em_limiting_lift_not_unique_leibniz], the same among lifts that are
     both limiting.  This is a feature of the setoid
     encoding, not of Mac Lane's statement: for him, over any X, a
     T-algebra is a pair ⟨x, h⟩ with h an arrow of X (p. 140), arrows
     are compared by equality, and the universal property determines h,
     while here the structure map is a setoid morphism that the
     universal property determines only up to the carrier's [≈].  “The
     only one” in the summary above is this [≈]-form.
   - (ii), σ limiting: [em_created], and the field [screates_limiting]
     of [em_forget_StrictlyCreatesLimit].
   - Not in Mac Lane's Definition: reflection, [em_reflects] (the field
     [screates_reflect]), which Structure/Limit/Creation.v's classes
     carry in place of the uniqueness clause.
   - “G^T creates limits” for every shape J:
     [em_forget_StrictlyCreatesLimits] and [em_forget_CreatesAllLimits].

   #467's “Current state” (no theorem that [EM_Forget] creates or even
   preserves limits) was accurate when the issue was filed (2026-07-23)
   and has been stale since PR #1083 (#406, commit bdce5ebe), on which
   #467 was filed as depending, merged on 2026-08-13 (the issue's
   createdAt and the pull request's mergedAt, by gh issue view and
   gh pr view): this file and its Examples.v landed with that pull
   request.  #467 adds the citation, the map above,
   [em_lift_alg_unique] and its instance at [Sets], the refutation and
   the probe.

   This makes Structure/Limit/Creation.v's classes inhabited by a functor
   the library already builds, and it turns the prose claim at
   Structure/Complete.v into the theorem [EM_Complete].

   It is the limit-side companion to [monadic_creates]
   (Monad/Monadicity/Beck.v), which creates U-split coequalizers only;
   no comparison lemma between the two is attempted here —
   [CreatesUSplitCoequalizers] quantifies over pairs supplied with a split
   coequalizer of their U-image, which is strictly more data than a
   colimiting cocone, so the honest bridge is a class-indexed restriction
   statement rather than an instance, and [U ◯ APair f g] is not
   convertible with [APair (fmap[U] f) (fmap[U] g)] (since #477 that no
   longer blocks reading a colimit over [U ◯ APair f g] elementarily:
   Structure/Coequalizer.v's [parallel_colimit_coequalizer] and
   [parallel_coequalizer_colimit] hold for every diagram of parallel-pair
   shape, the composed one included; the costed statement below is
   still not shipped).  The statement that
   was costed and declined is [CreatesUSplitCoequalizers U → ∀ {x y}
   (f g : x ~> y), SplitCoequalizer (fmap[U] f) (fmap[U] g) →
   CreatesColimit (APair f g) U], routed through
   [split_coequalizer_is_coequalizer] (Structure/Coequalizer/Split.v) and
   the op repackaging of Structure/Limit/Creation.v; it is recorded here
   rather than shipped, and the issue's request for it is unmet — descope
   ledger entry 18 (doc/classical-completion-plan.md §5).  Neither Beck.v nor
   BeckObjects.v is modified: [CreatedSplitCoequalizer]
   (Monad/Monadicity/BeckObjects.v) is the same pattern at one shape,
   its [created_hom_carrier] being the [slift_legs] clause and its
   [created_alg_unique] the [≈]-form of uniqueness at a pinned carrier.

   The file imports no [Instance/*], mirroring the Beck.v /
   Monad/Monadicity/Examples.v split; the hypothesis-free instantiation
   lives in Monad/Eilenberg/Moore/Limit/Examples.v. 

--------
nLab：https://ncatlab.org/nlab/show/created+limit
 nLab：https://ncatlab.org/nlab/show/Eilenberg-Moore+category#limits
 Mac Lane：工作数学家的类别，第二版。 （GTM 5），
 §VI.2 定理 1 和 §V.1 创造词汇（第 112 页）
 Mac Lane：同上，§VI.2 练习 2（书籍第 142 页，PDF 第 151 页；
 目录项 malane:VI.2:ex2), “显示 G^T : X^T → X
 创造限制”

更正 (#467)：上面的引文将定理 1 命名为其唯一的
 §VI.2 来源。 该定理（书第 140 页，“每个单子都由
 它的 T 代数”）构建 X^T、G^T 和附加 F^T ⊣ G^T； 的
 该文件证明的陈述是同一部分的练习 2，引用
 在其后添加的行上。 Mac Lane 的 §V.1 定义（第 112 页）是
 未编号并对其第(i)和(ii)条进行编号； 逐条
 地图是下面的 MAC LANE'S DEFINITION, CLAUSE BY CLAUSE 段落。

对于 D 上的任何单子 T，健忘函子 [EM_Forget T] STRICTLY
 创建每个限制：给定 [EM_Forget T ◯ K] 上的限制锥体
 楼下，中介图从圆锥体到其顶点，圆锥体的腿是
 [t_alg ∘ fmap[T] π]是一个代数结构，得到的圆锥体在楼上
 位于鼻子上给定的一个（[em_over_obj] 和 [em_over_legs] 是
 都是 [eq_refl]，因为 EM_Forget 的对象图是第一个投影），
 它是有限的（[em_created]），它的结构图是唯一的
 那个圆锥体（[em_alg_unique]），以及楼上的一个圆锥体，其图像受到限制
 本身就是有限的（[em_reflects]）。

关于态射与 [≈] 进行比较的内部规则：[em_over_legs]
 是这里在态射之间写入 [=] 的一条语句，它确实
 因为双方都是同一个术语——见证人是 [eq_refl]。 它
 记录了 Mac Lane 的 [F σ = τ] 的全力状态，严格来说
 比班级要求的 [≈] 更强； 每一条法律、每一个证据和
 [em_strict_lift] 使用 [≈] 消耗的 [StrictLift] 腿子句。

MAC LANE 的定义，逐个条款 (#467)。 的定义
 p。 112（PDF第121页），从页面图像中读取：“函子V：A→X
 为函子 F 创建极限： J → A if (i) 对于每个极限锥
 τ: x →· VF 在 X 中恰好有一对 ⟨a, σ⟩ 组成
 对象 a ∈ A，其中 Va = x 和圆锥 σ：a →· F，其中 Vσ = τ，并且如果，
 此外，(ii) 该锥体 σ: a →· F 是 A 中的极限锥体。” 这里V
 是 [EM_Forget T]，F 是 [K]，τ 是给定的极限锥 [N]（或
 [L] 的锥体）。 Test/ProbeEMCreates467.v 重申每个 [eq_refl]
 下面的强度作为对照，将 R1 引脚作为拒绝，并重申
 对它们的常数的两个反驳。

- (i)，存在 Va = x 的 a：在 [eq_refl] 处。 [em_over_obj]，
 [slift_eq] 的 [em_strict_lift]（即 [eq_refl]），以及 iso
 等不变类，[creates_lift_over]
 [em_forget_CreatesLimit]，其前向图是机头上的[id]。 - (i)，存在 σ 且 Vσ = τ：在 [eq_refl] 逐条腿处，反对
 给定的圆锥体。 [em_over_legs]； 课堂上同样如此
 投影 [screates] 和腿系列 [fun j => …] 一样。 图像
 作为记录的圆锥体不是给定圆锥体的 [eq_refl]：顶点和腿
 转换，但相干场不转换（探头 R1）。 [FCone] 的
 Coherence 是 [fcone_coherence] 的应用，是 [Qed] 引理
 其主体是 D 抽象 hom-setoid 上的重写链； N 是
 变量 N 的投影被卡住。原因是结构性的，
 如此争论：变得透明，链仍然不会转换为
 那个投影。
它不是通过完全翻转来测量的。 - (i)，“恰好一对”：仅适用于 [≈]。 [em_alg_unique] 在
 固定载体 [vertex_obj[L]] 和 [em_lift_alg_unique] 如下
 任意 [StrictLift] 的载体：该升力同构于
 [EilenbergMoore T] 到创建的顶点，通过同构，其
 底层地图是 ≈ 传输 [slift_iso]。 班级形式为
 Structure/Limit/Creation.v 的 [screates_lift_unique] 位于
 [em_forget_StrictlyCreatesLimit T K]：楼上的一个圆锥体，其图像是
 与 N 锥体同构与所产生的升力锥体同构。 [em_lift_alg_unique] 将其专门化为 [StrictLift] 并命名为
 同构的底层图，≈传输； 它的类型是
 代数同构，无锥相容性 a
 [ConeIso] 携带。 然后 σ 的腿在 [≈] 中确定为
 [slift_legs]，因为 [EilenbergMoore T] 的箭头通过
 他们的底层地图。
Examples.v 在 [Sets] 实例化它
 ([em_lift_alg_unique_Sets])，在一个不离散的载体上，其
 [≈] - 每张地图的结论都成立：实例见证了
 前提是除了创建的电梯之外的严格电梯。 鼻子上的形式，[=] 位于顶端，适用于双腿
 同意 [=] 的 τ，在没有公理的情况下被驳斥
 Monad/Eilenberg/Moore/Limit/Examples.v：[em_lift_not_unique_leibniz]，
 在 [Sets] 中，具有恒等单子和不离散两点
 setoid，其两个结构图 [id] 和 [const true] 都提升了一个
 限制锥体的腿在鼻子上相等，并且
 [em_limiting_lift_not_unique_leibniz]，与以下电梯相同
 两者都有限制。 这是setoid的一个特点
 编码，而不是 Mac Lane 的声明：对他来说，在任何 X 上，a
 T 代数是一对 ⟨x, h⟩，其中 h 是 X 的箭头（第 17 页）。
140), 箭头
 通过相等进行比较，通用性质决定了 h，
 而这里的结构图是集合态射
 通用属性仅决定最多运营商的[≈]。 “的
 上面的摘要中只有一个”是 [≈] 形式。 - (ii)、σ 限制：[em_created] 和场 [screates_limiting]
 [em_forget_StrictlyCreatesLimit] 的。 - 不在 Mac Lane 的定义中：反射、[em_reflects]（该字段
 [screates_reflect])，其中 Structure/Limit/Creation.v 的类
 取代唯一性子句。 - “G^T 为每个形状 J 创建限制”：
 [em_forget_StrictlyCreatesLimits] 和 [em_forget_CreatesAllLimits]。

#467 的“当前状态”（[EM_Forget] 没有创建定理，甚至没有定理）
 保留限制）在提交问题时是准确的 (2026-07-23)
 自 PR #1083（#406，提交 bdce5ebe）以来就已经过时了，其中
 #467 被归档为依赖，于 2026-08-13 合并（该问题的
 createAt 和拉取请求的 mergedAt，通过 gh 问题视图和
 gh pr 视图）：该文件及其 Examples.v 随该拉动而落地
 请求。 第467章 添加引文，上面的地图，
 [em_lift_alg_unique]及其在[Sets]的实例，反驳和
 探头。

这使得 Structure/Limit/Creation.v 的类被函子占据
 图书馆已经建成，它把散文的主张变成了
 Structure/Complete.v 转化为定理 [EM_Complete]。

它是 [monadic_creates] 的极限侧伴侣
 (Monad/Monadicity/Beck.v)，仅创建 U-split 协均衡器；
 这里没有尝试比较两者之间的引理 -
 [CreatesUSplitCoequalizers] 对分体提供的线对进行量化
 他们的 U 图像的 coequalizer，这严格来说比一个
 共同限制 cocone，因此诚实桥是一个类索引限制
 语句而不是实例，[U ◯ APair f g] 不是
 可与 [APair (fmap[U] f) (fmap[U] g) 进行转换]（从 #477 开始，没有
 较长的块基本上通过 [U ◯ APair f g] 读取 colimit：
 Structure/Coequalizer.v 的 [parallel_colimit_coequalizer] 和
 [parallel_coequalizer_colimit] 适用于每个并联对图
 形状，包括组合的形状； 下面的成本报表是
 还没发货）。
该声明称
 已计算成本并被拒绝的是 [CreatesUSplitCoequalizers U → ∀ {x y}
 (f g : x ~> y), SplitCoequalizer (fmap[U] f) (fmap[U] g) →
 CreatesColimit (APair f g) U]，路由通过
 [split_coequalizer_is_coequalizer]（结构/均衡器/Split.v）和
 Structure/Limit/Creation.v 的操作重新打包； 记录在这里
 而不是发货，并且问题的要求未得到满足 — descope
 分类帐条目 18（doc/classical-completion-plan.md §5）。 Beck.v 和
 BeckObjects.v 修改为：[CreatedSplitCoequalizer]
 (Monad/Monadicity/BeckObjects.v) 是一种形状的相同模式，
 它的 [created_hom_carrier] 是 [slift_legs] 子句及其
 [created_alg_unique] 是 [≈] 的独特形式，采用固定载体。

该文件未导入 [Instance/*]，镜像 Beck.v /
 Monad/Monadicity/Examples.v 拆分； 无假设实例化
 住在 Monad/Eilenberg/Moore/Limit/Examples.v 中。 
*)

Section EMCreates.

Context {D : Category}.
Context (T : D ⟶ D).
Context `{H : @Monad D T}.
Context {J : Category}.
Context (K : J ⟶ EilenbergMoore T).
Context (L : Limit (EM_Forget T ◯ K)).

(** ** Generic cone precomposition  / ** 通用圆锥预合成*)

Definition cone_pre {c : D} (N : Cone (EM_Forget T ◯ K))
  (u : c ~{D}~> vertex_obj[N]) : Cone (EM_Forget T ◯ K).
Proof.
  unshelve refine (@Build_Cone J D (EM_Forget T ◯ K) c
    (@Build_ACone J D c (EM_Forget T ◯ K) (fun j => cone_leg N j ∘ u) _)).
  intros x y f; simpl.
  rewrite comp_assoc.
  rewrite (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f).
  reflexivity.
Defined.

(** ** The action cone: apex [T L], legs [ν_j ∘ T π_j]  / ** 动作锥体：顶点 XPROTECT 0X，腿部 XPROTECT 1X*)

Definition em_act_leg (j : J) : T (vertex_obj[L]) ~{D}~> (EM_Forget T ◯ K) j :=
  t_alg[`2 (K j)] ∘ fmap[T] (limit_leg (limit_is_alimit L) j).

Lemma em_act_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[EM_Forget T ◯ K] f ∘ em_act_leg x ≈ em_act_leg y.
Proof.
  unfold em_act_leg.
  rewrite comp_assoc.
  rewrite (@t_alg_hom_commutes _ _ _ _ _ _ _ (fmap[K] f)).
  rewrite <- !comp_assoc.
  rewrite <- fmap_comp.
  rewrite (limit_leg_coherence (limit_is_alimit L) f).
  reflexivity.
Qed.

Definition em_act_cone : Cone (EM_Forget T ◯ K) :=
  @Build_Cone J D (EM_Forget T ◯ K) (T (vertex_obj[L]))
    (@Build_ACone J D (T (vertex_obj[L])) (EM_Forget T ◯ K)
       em_act_leg (@em_act_coherence)).

(* The created structure map is the mediator of that cone.  / 创建的结构图是该锥体的中介。*)

Definition em_act : T (vertex_obj[L]) ~{D}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) em_act_cone.

Lemma em_act_triangle (j : J) :
  limit_leg (limit_is_alimit L) j ∘ em_act ≈ em_act_leg j.
Proof. exact (limit_med_commutes (limit_is_alimit L) em_act_cone j). Qed.

(** ** The algebra laws for the created action  / ** 创建动作的代数定律*)

Lemma em_alg_t_id : em_act ∘ ret ≈ id.
Proof.
  apply (limit_med_eq (limit_is_alimit L)
           (@Build_Cone J D (EM_Forget T ◯ K) (vertex_obj[L])
              (@limit_acone _ _ _ _ (limit_is_alimit L)))).
  - intro j.
    rewrite comp_assoc.
    rewrite (em_act_triangle j).
    unfold em_act_leg.
    rewrite <- comp_assoc.
    rewrite <- fmap_ret.
    rewrite comp_assoc.
    rewrite t_id.
    rewrite id_left.
    reflexivity.
  - intro j.
    rewrite id_right.
    reflexivity.
Qed.

Lemma em_action_left (j : J) :
  limit_leg (limit_is_alimit L) j ∘ (em_act ∘ fmap[T] em_act)
    ≈ em_act_leg j ∘ (@join D T H (vertex_obj[L])).
Proof.
  rewrite comp_assoc.
  rewrite (em_act_triangle j).
  unfold em_act_leg at 1.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite (em_act_triangle j).
  unfold em_act_leg.
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite t_action.
  rewrite <- !comp_assoc.
  rewrite join_fmap_fmap.
  reflexivity.
Qed.

Lemma em_action_right (j : J) :
  limit_leg (limit_is_alimit L) j ∘ (em_act ∘ (@join D T H (vertex_obj[L])))
    ≈ em_act_leg j ∘ (@join D T H (vertex_obj[L])).
Proof.
  rewrite comp_assoc.
  rewrite (em_act_triangle j).
  reflexivity.
Qed.

Lemma em_alg_t_action :
  em_act ∘ fmap[T] em_act ≈ em_act ∘ (@join D T H (vertex_obj[L])).
Proof.
  apply (limit_med_eq (limit_is_alimit L)
           (cone_pre em_act_cone (@join D T H (vertex_obj[L])))).
  - exact em_action_left.
  - exact em_action_right.
Qed.

Definition em_alg : @TAlgebra D T H (vertex_obj[L]) :=
  {| t_alg := em_act ; t_id := em_alg_t_id ; t_action := em_alg_t_action |}.

Definition em_apex : EilenbergMoore T := (vertex_obj[L]; em_alg).

Definition em_leg (j : J) : em_apex ~{EilenbergMoore T}~> K j :=
  @Build_TAlgebraHom D T H (vertex_obj[L]) (`1 (K j)) em_alg (`2 (K j))
    (limit_leg (limit_is_alimit L) j) (em_act_triangle j).

Lemma em_leg_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ em_leg x ≈ em_leg y.
Proof. exact (limit_leg_coherence (limit_is_alimit L) f). Qed.

Definition em_cone : Cone K :=
  @Build_Cone J (EilenbergMoore T) K em_apex
    (@Build_ACone J (EilenbergMoore T) em_apex K em_leg (@em_leg_coherence)).

(** ** Strictness: the created cone lies over L on the nose  / ** 严格性：创建的圆锥体位于鼻子上的 L 上方*)

Definition em_over_obj : EM_Forget T em_apex = vertex_obj[L] := eq_refl.

Definition em_over_legs (j : J) :
  fmap[EM_Forget T] (cone_leg em_cone j) = limit_leg (limit_is_alimit L) j
  := eq_refl.

(** ** The lift is limiting  / ** 电梯受到限制*)

Definition car_cone (N : Cone K) : Cone (EM_Forget T ◯ K) :=
  @Build_Cone J D (EM_Forget T ◯ K) (`1 vertex_obj[N])
    (@Build_ACone J D (`1 vertex_obj[N]) (EM_Forget T ◯ K)
       (fun j => t_alg_hom[cone_leg N j])
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)).

Definition car_med (N : Cone K) : (`1 vertex_obj[N]) ~{D}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) (car_cone N).

Lemma car_med_commutes (N : Cone K) (j : J) :
  limit_leg (limit_is_alimit L) j ∘ car_med N ≈ t_alg_hom[cone_leg N j].
Proof. exact (limit_med_commutes (limit_is_alimit L) (car_cone N) j). Qed.

Lemma car_med_hom_left (N : Cone K) (j : J) :
  limit_leg (limit_is_alimit L) j ∘ (car_med N ∘ t_alg[`2 vertex_obj[N]])
    ≈ em_act_leg j ∘ fmap[T] (car_med N).
Proof.
  rewrite comp_assoc.
  rewrite (car_med_commutes N j).
  rewrite (@t_alg_hom_commutes _ _ _ _ _ _ _ (cone_leg N j)).
  unfold em_act_leg.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite (car_med_commutes N j).
  reflexivity.
Qed.

Lemma car_med_hom_right (N : Cone K) (j : J) :
  limit_leg (limit_is_alimit L) j ∘ (em_act ∘ fmap[T] (car_med N))
    ≈ em_act_leg j ∘ fmap[T] (car_med N).
Proof.
  rewrite comp_assoc.
  rewrite (em_act_triangle j).
  reflexivity.
Qed.

Lemma car_med_is_hom (N : Cone K) :
  car_med N ∘ t_alg[`2 vertex_obj[N]] ≈ em_act ∘ fmap[T] (car_med N).
Proof.
  apply (limit_med_eq (limit_is_alimit L)
           (cone_pre em_act_cone (fmap[T] (car_med N)))).
  - exact (car_med_hom_left N).
  - exact (car_med_hom_right N).
Qed.

Definition em_med (N : Cone K) : vertex_obj[N] ~{EilenbergMoore T}~> em_apex :=
  @Build_TAlgebraHom D T H (`1 vertex_obj[N]) (vertex_obj[L])
    (`2 vertex_obj[N]) em_alg (car_med N) (car_med_is_hom N).

Definition em_created : IsALimit K em_apex.
Proof.
  unshelve refine {| limit_acone := @coneFrom _ _ _ em_cone |}.
  intro N.
  unshelve refine {| unique_obj := em_med N |}.
  - exact (car_med_commutes N).
  - intros v Hv.
    exact (limit_med_unique (limit_is_alimit L) (car_cone N) t_alg_hom[v] Hv).
Defined.

(** ** Uniqueness of the lift: the algebra structure is the only one  / ** 电梯的唯一性：代数结构是唯一的*)

(*
The [≈]-form of Mac Lane's uniqueness clause at a pinned carrier, the
   same statement [created_alg_unique] (BeckObjects.v) makes at its own
   shape. 

--------
固定运营商处 Mac Lane 唯一性子句的 [≈] 形式，
 [created_alg_unique] (BeckObjects.v) 自己做出的相同声明
 形状。 
*)

Lemma em_alg_unique (alg' : @TAlgebra D T H (vertex_obj[L]))
  (Halg : ∀ j, limit_leg (limit_is_alimit L) j ∘ t_alg[alg'] ≈ em_act_leg j) :
  t_alg[alg'] ≈ t_alg[em_alg].
Proof.
  symmetry.
  exact (limit_med_unique (limit_is_alimit L) em_act_cone t_alg[alg'] Halg).
Qed.

End EMCreates.

(** ** Reflection: a cone whose image is limiting is limiting  / ** 反射：其图像受到限制的圆锥体就是受到限制的*)

Section EMReflects.

Context {D : Category}.
Context (T : D ⟶ D).
Context `{H : @Monad D T}.
Context {J : Category}.
Context (K : J ⟶ EilenbergMoore T).
Context (M : Cone K).
Context (HM : IsALimit (EM_Forget T ◯ K) (`1 vertex_obj[M])).
Context (Hlegs : ∀ j, limit_leg HM j ≈ t_alg_hom[cone_leg M j]).

Definition rcar_cone (N : Cone K) : Cone (EM_Forget T ◯ K) :=
  @Build_Cone J D (EM_Forget T ◯ K) (`1 vertex_obj[N])
    (@Build_ACone J D (`1 vertex_obj[N]) (EM_Forget T ◯ K)
       (fun j => t_alg_hom[cone_leg N j])
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)).

Definition rcar_med (N : Cone K) :
  (`1 vertex_obj[N]) ~{D}~> (`1 vertex_obj[M]) :=
  limit_med HM (rcar_cone N).

Lemma rcar_med_commutes (N : Cone K) (j : J) :
  t_alg_hom[cone_leg M j] ∘ rcar_med N ≈ t_alg_hom[cone_leg N j].
Proof using All.
  rewrite <- (Hlegs j).
  exact (limit_med_commutes HM (rcar_cone N) j).
Qed.

Definition ract_leg (N : Cone K) (j : J) :
  T (`1 vertex_obj[N]) ~{D}~> (EM_Forget T ◯ K) j :=
  t_alg[`2 (K j)] ∘ fmap[T] (t_alg_hom[cone_leg N j]).

Lemma ract_coherence (N : Cone K) {x y : J} (f : x ~{J}~> y) :
  fmap[EM_Forget T ◯ K] f ∘ ract_leg N x ≈ ract_leg N y.
Proof using All.
  assert (Hc : t_alg_hom[fmap[K] f] ∘ t_alg_hom[cone_leg N x]
                 ≈ t_alg_hom[cone_leg N y])
    by exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f).
  unfold ract_leg.
  rewrite comp_assoc.
  rewrite (@t_alg_hom_commutes _ _ _ _ _ _ _ (fmap[K] f)).
  rewrite <- !comp_assoc.
  rewrite <- fmap_comp.
  rewrite Hc.
  reflexivity.
Qed.

Definition ract_cone (N : Cone K) : Cone (EM_Forget T ◯ K) :=
  @Build_Cone J D (EM_Forget T ◯ K) (T (`1 vertex_obj[N]))
    (@Build_ACone J D (T (`1 vertex_obj[N])) (EM_Forget T ◯ K)
       (ract_leg N) (@ract_coherence N)).

Lemma rcar_hom_left (N : Cone K) (j : J) :
  limit_leg HM j ∘ (rcar_med N ∘ t_alg[`2 vertex_obj[N]]) ≈ ract_leg N j.
Proof using All.
  rewrite (Hlegs j).
  rewrite comp_assoc.
  rewrite (rcar_med_commutes N j).
  exact (@t_alg_hom_commutes _ _ _ _ _ _ _ (cone_leg N j)).
Qed.

Lemma rcar_hom_right (N : Cone K) (j : J) :
  limit_leg HM j ∘ (t_alg[`2 vertex_obj[M]] ∘ fmap[T] (rcar_med N))
    ≈ ract_leg N j.
Proof using All.
  rewrite (Hlegs j).
  rewrite comp_assoc.
  rewrite (@t_alg_hom_commutes _ _ _ _ _ _ _ (cone_leg M j)).
  unfold ract_leg.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite (rcar_med_commutes N j).
  reflexivity.
Qed.

Lemma rcar_med_is_hom (N : Cone K) :
  rcar_med N ∘ t_alg[`2 vertex_obj[N]]
    ≈ t_alg[`2 vertex_obj[M]] ∘ fmap[T] (rcar_med N).
Proof using All.
  apply (limit_med_eq HM (ract_cone N)).
  - exact (rcar_hom_left N).
  - exact (rcar_hom_right N).
Qed.

Definition rem_med (N : Cone K) :
  vertex_obj[N] ~{EilenbergMoore T}~> vertex_obj[M] :=
  @Build_TAlgebraHom D T H (`1 vertex_obj[N]) (`1 vertex_obj[M])
    (`2 vertex_obj[N]) (`2 vertex_obj[M]) (rcar_med N) (rcar_med_is_hom N).

Definition em_reflects : IsALimit K vertex_obj[M].
Proof using All.
  unshelve refine {| limit_acone := @coneFrom _ _ _ M |}.
  intro N.
  unshelve refine {| unique_obj := rem_med N |}.
  - exact (rcar_med_commutes N).
  - intros v Hv.
    apply (limit_med_unique HM (rcar_cone N) t_alg_hom[v]).
    intro j.
    rewrite (Hlegs j).
    exact (Hv j).
Defined.

End EMReflects.

(** ** [EM_Forget] strictly creates every limit  / ** [EM_Forget]严格创造每一个限制*)

Section EMStrictlyCreates.

Context {D : Category}.
Context (T : D ⟶ D).
Context `{H : @Monad D T}.
Context {J : Category}.
Context (K : J ⟶ EilenbergMoore T).

Definition em_strict_lift (N : Cone (EM_Forget T ◯ K)) (HN : IsLimitCone N) :
  StrictLift K (EM_Forget T) N :=
  @Build_StrictLift J (EilenbergMoore T) D K (EM_Forget T) N
    (em_cone T K (@Build_Limit J D (EM_Forget T ◯ K) N HN))
    eq_refl
    (fun x => reflexivity _).

Definition em_forget_StrictlyCreatesLimit :
  StrictlyCreatesLimit K (EM_Forget T).
Proof.
  unshelve refine {| screates := em_strict_lift |}.
  - intros N HN.
    exact (@ump_limit _ _ _ _
             (em_created T K (@Build_Limit J D (EM_Forget T ◯ K) N HN))).
  - intros M HM.
    exact (@ump_limit _ _ _ _
             (em_reflects T K M (limitcone_isalimit HM)
                (fun j => reflexivity _))).
Defined.

Definition em_forget_CreatesLimit : CreatesLimit K (EM_Forget T) :=
  StrictlyCreatesLimit_CreatesLimit em_forget_StrictlyCreatesLimit.

End EMStrictlyCreates.

(** ** Uniqueness of a strict lift, at an unpinned carrier  / ** 无固定支架的严格升降机的独特性*)

(*
The [≈]-form of the uniqueness clause of Mac Lane's (i) for an
   arbitrary [StrictLift]: whatever its algebra, the lift is isomorphic in
   [EilenbergMoore T] to the created apex by an isomorphism lying over
   the transport [slift_iso].  [em_alg_unique] is the step that pins the
   structure map; this statement lets the carrier vary with [slift_eq].
   Its [=]-form is refuted in Monad/Eilenberg/Moore/Limit/Examples.v.

   Universes, read off [About]: [o] and [h] are D's objects and arrows,
   [jo] J's objects, [eo] and [e] the objects and the level of
   [EilenbergMoore], and [l], [l0] those of [IsLimitCone]; the bounds are
   [h < e] and the chain [jo, h <= l0 <= l], [o <= l], [o, h <= eo], with
   the sigma projections' two caps.  A draft that rewrote under [fmap]
   also carried three [prod_rect] caps and a phantom level, and one that
   used [subst] an [EqdepFacts] cap; the proof below destructs the cone
   [N], so that the transport is a match on a variable, and composes
   [compose_respects] and [fmap_respects] by hand. 

--------
Mac Lane 的 (i) 的唯一性子句的 [≈] 形式
 任意 [StrictLift]：无论其代数如何，升力都是同构的
 [EilenbergMoore T] 通过同构到达所创建的顶点
 运输 [slift_iso]。 [em_alg_unique] 是固定的步骤
 结构图； 这个声明让运营商随[slift_eq]而变化。 
它的 [=] 形式在 Monad/Eilenberg/Moore/Limit/Examples.v 中被驳斥。

宇宙，读出 [About]：[o] 和 [h] 是 D 的物体和箭头，
 [jo] J 的对象、[eo] 和 [e] 的对象和级别
 [EilenbergMoore]、[l]、[l0] 是 [IsLimitCone] 的； 界限是
 [h < e] 和链条 [jo, h <= l0 <= l]、[o <= l]、[o, h <= eo]，带
 西格玛投影的两个上限。 在[fmap]下重写的草稿
 还携带三个 [prod_rect] 盖帽和一个幻像水平仪，以及一个
 使用 [subst] 和 [EqdepFacts] 盖； 下面的证明破坏了圆锥体
 [N]，以便传输与变量匹配，并组成
 [compose_respects] 和 [fmap_respects] 手工制作。 
*)

Definition em_lift_alg_unique@{o h jo eo e l l0} {D : Category@{o h h}}
  (T : D ⟶ D) `{H : @Monad D T} {J : Category@{jo h h}}
  (K : J ⟶ EilenbergMoore@{eo o e h} T)
  (N : Cone (EM_Forget T ◯ K)) (HN : IsLimitCone@{l l0 jo h o} N)
  (s : StrictLift@{e eo jo h o} K (EM_Forget T) N) :
  { i : vertex_obj[slift_cone s] ≅[EilenbergMoore T]
          em_apex T K (@Build_Limit J D (EM_Forget T ◯ K) N HN)
  & t_alg_hom[to i] ≈ to (slift_iso s) }.
Proof.
  destruct s as [σ p Hl].
  destruct σ as [[x alg] σc].
  destruct N as [n Nc].
  simpl in p, Hl |- *.
  destruct p.
  simpl in Hl.
  pose (L := @Build_Limit J D (EM_Forget T ◯ K)
               (@Build_Cone J D (EM_Forget T ◯ K) x Nc) HN).
  assert (Ha : t_alg[alg] ≈ t_alg[em_alg T K L]).
  { apply (em_alg_unique T K L alg).
    intro j.
    assert (Hj : t_alg_hom[@vertex_map _ _ _ _ σc j]
                   ≈ limit_leg (limit_is_alimit L) j) by exact (Hl j).
    unfold em_act_leg.
    transitivity (t_alg_hom[@vertex_map _ _ _ _ σc j] ∘ t_alg[alg]).
    { exact (compose_respects _ _ (symmetry Hj) _ _ (reflexivity _)). }
    transitivity
      (t_alg[`2 (K j)] ∘ fmap[T] t_alg_hom[@vertex_map _ _ _ _ σc j]).
    { exact (@t_alg_hom_commutes _ _ _ _ _ _ _ (@vertex_map _ _ _ _ σc j)). }
    exact (compose_respects _ _ (reflexivity _) _ _
             (fmap_respects _ _ _ _ Hj)). }
  unshelve eexists.
  - unshelve refine (@Build_Isomorphism (EilenbergMoore T)
      (existT _ x alg) (em_apex T K L)
      (@Build_TAlgebraHom D T H _ _ alg (em_alg T K L) id _)
      (@Build_TAlgebraHom D T H _ _ (em_alg T K L) alg id _) _ _).
    + simpl.
      transitivity (t_alg[alg]); [apply id_left|].
      transitivity (em_act T K L ∘ id).
      * transitivity (em_act T K L); [exact Ha|symmetry; apply id_right].
      * exact (compose_respects _ _ (reflexivity _) _ _ (symmetry fmap_id)).
    + simpl.
      transitivity (t_alg[em_alg T K L]); [apply id_left|].
      transitivity (t_alg[alg] ∘ id).
      * transitivity (t_alg[alg]);
          [symmetry; exact Ha|symmetry; apply id_right].
      * exact (compose_respects _ _ (reflexivity _) _ _ (symmetry fmap_id)).
    + simpl. apply id_left.
    + simpl. apply id_left.
  - simpl. reflexivity.
Defined.

Definition em_forget_StrictlyCreatesLimits {D : Category} (T : D ⟶ D)
  `{H : @Monad D T} : StrictlyCreatesLimits (EM_Forget T) :=
  fun J K => em_forget_StrictlyCreatesLimit T K.

Definition em_forget_CreatesAllLimits {D : Category} (T : D ⟶ D)
  `{H : @Monad D T} : CreatesAllLimits (EM_Forget T) :=
  fun J K => em_forget_CreatesLimit T K.

(** ** Algebras over a complete base are complete  / ** 完备基上的代数是完备的*)

(*
Mac Lane §V.4 Theorem 2 applied to the witness above; this is the
   standing claim of Structure/Complete.v, as a theorem. 

--------
Mac Lane §V.4 定理 2 适用于上述证人； 这是
 Structure/Complete.v 的长期主张作为定理。 
*)

Definition EM_Complete {D : Category} (T : D ⟶ D) `{H : @Monad D T}
  (HD : @Complete D) : @Complete (EilenbergMoore T) :=
  creates_limits_Complete (EM_Forget T) HD (em_forget_CreatesAllLimits T).
