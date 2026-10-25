Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Transformer.
Require Import Category.Monad.Morphism.

Generalizable All Variables.

(** * Monad transformers are morphisms of monads  / * Monad 转换器是 monad 的态射*)

(*
Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, §VI.2 Exercise 3(a), printed p. 142
         (PDF p. 151) — maclane:VI.2:ex3
   nLab: https://ncatlab.org/nlab/show/monad+transformer
   nLab: https://ncatlab.org/nlab/show/monad (section "The 2-category of
         monads")

   WHAT IS PROVED.  Monad/Transformer.v's [MonadTransformer T], at a
   monad M on C and a monad on T M, carries a family
   lift_a : M a ~> T M a with two laws in the Kleisli form, [lift_return]
   (lift ∘ ret ≈ ret) and [lift_bind] (lift ∘ join ∘ fmap f ≈
   join ∘ fmap (lift ∘ f) ∘ lift).  Its header reads lift as "a monad
   morphism lift : M ⟹ T M", but the class has no naturality field and
   no law about [join] alone, and until this file the tree had no record
   of monad morphisms to measure the reading against.  With Monad/
   Morphism.v's [MonadHom], the reading is a theorem, in both directions:
   - [lift_natural]: lift is natural, from [lift_bind] at ret ∘ g,
     [lift_return] and the unit law [join_fmap_ret] of both monads;
   - [transformer_hom L : MonadHom M (T M)], whose transformation has the
     components of lift ([transformer_hom_lift], [eq_refl]); its unit law
     IS [lift_return], and its multiplication law is [lift_bind] at
     f = id, turned into Monad/Morphism.v's horizontal-composite form by
     [lift_natural] at lift_x;
   - [hom_transformer θ : MonadTransformer T] for any θ : MonadHom M
     (T M), whose lift has the components of θ ([hom_transformer_lift],
     [eq_refl]); [lift_return] IS [mh_ret], and [lift_bind] follows from
     Monad/Morphism.v's [mh_join_nat], the naturality of θ at f and
     [fmap_comp].
   The component families round trip on the nose, both ways
   ([transformer_round_trip], [hom_round_trip]).  The two records do not:
   hom_transformer (transformer_hom L) against L, and transformer_hom
   (hom_transformer θ) against θ, are refused at [eq_refl], because the
   laws are rebuilt proofs where the variable record has projections.
   So the transformer laws at one monad M are exactly a morphism of
   monads M ⟶ T M, up to the proofs of the laws: the "suitable natural
   transformation" of Mac Lane's exercise, specialized to the pair
   (M, T M).  This is the sense in which #468 asks for "generalizing the
   MonadTransformer laws".

   WHERE IT COMES FROM.  nLab's page "monad transformer", read through a
   fetch of the page, states the transformer condition in the return and
   bind form, which it attributes to Liang, Hudak and Jones (1995), and
   states it equivalent to lift's being a homomorphism of monads: a
   natural transformation of the underlying functors respecting the unit
   and the multiplication.  That equivalence is what this file checks at
   the library's definitions.  The same page makes a transformer, as used
   in functional programming, a pointed endofunctor on the category of
   monads, whose point is lift; the class here constrains T at one monad
   M only, and so is one component of such a point.

   ISSUE #468's PREMISE.  Its "Current state" says that [MonadTransformer]
   "packages the monad-morphism laws as `lift : M ⟹ T M`", citing the class
   by a line number.  The class has sat unchanged since before the issue was
   filed (its last commit, 83b38386, is of 2026-06-17, by git log), and lift
   was then, as now, a bare family with no naturality field: the premise was
   imprecise when filed, and [lift_natural] is the missing field, derived.

   STRENGTHS.  By [eq_refl]: [transformer_hom_lift], [hom_transformer_lift]
   and the two component round trips.  At ≈: [lift_natural] and the laws of
   both constructions.  Refused at [eq_refl], by conversion, pinned in
   Test/ProbeMonadMorphism468.v with the component round trips as controls
   (C26, C27): the two whole-record round trips (R10, R11).  Both stand in a
   copy of the probe's dependency closure with every [Qed] turned into
   [Defined] and [Transparent Obligations] set (Instance/Sets.v,
   Structure/Cartesian/Closed.v, Instance/Grp.v and Instance/Grp/Free.v
   keeping their [Qed]s), so they are not opacity: the rebuilt laws are
   compared with projections of the variable L or θ.

   UNIVERSES, read off [About].  [lift_natural], [transformer_hom] and
   [hom_transformer] bind [@{o h}] over [Category@{o h h}], at
   [MonadTransformer@{o h}] and [MonadHom@{o h}], with the constraint list
   closed and empty.  They stay so because no proof uses a setoid [rewrite]:
   measured on copies proved by [rewrite], [lift_natural] carries
   h <= prod_rect.u0/u1/u2, and each of the two constructions an extra
   universe u with h < u.  The four readbacks state = and end their lists
   with [+], for the bound on the standard library's [eq] that Coq 8.19 and
   8.20 add (Monad/Morphism.v's UNIVERSES paragraph).  No [Set], no strict
   bound and no equation occur.

   NOT DELIVERED.  The pointed endofunctor on [Monads C] of nLab's page:
   [MonadTransformer] does not ask T to act on morphisms of monads, and
   nothing here makes it.  Monad/Transformer.v's [MonadTransformerLaws]
   is not addressed: it sits inside a comment block of that file, so the
   tree has no such constant (a [Check] of it is refused, "not found",
   while [Check @MonadTransformer] is accepted).  Neither the class nor
   its instance [IdentityT_MonadTransformer] is changed. 

--------
书：Mac Lane，“工作数学家的类别”，第二版，
 Springer GTM 5, 1998, §VI.2 练习 3(a)，印刷页。 142
 （PDF 第 151 页）— Maclane:VI.2:ex3
 nLab：https://ncatlab.org/nlab/show/monad+transformer
 nLab：https://ncatlab.org/nlab/show/monad（“2 类”部分
 单子”）

已证明什么。 Monad/Transformer.v 的 [MonadTransformer T]，位于
 C 上的单子 M 和 T M 上的单子，承载着一个家庭
 lift_a : M a ~> T M a 具有 Kleisli 形式的两个定律，[lift_return]
 (lift ∘ ret ≈ ret) 和 [lift_bind] (lift ∘ join ∘ fmap f ≈
 连接 ∘ fmap (lift ∘ f) ∘ lift)。 它的标题将 lift 读作“a monad
 态射提升：M ⟹ T M"，但该类没有自然场并且
 没有关于 [join] 的法律，并且在此文件之前，树没有记录
 用来衡量阅读的单子态射。
与莫纳德/
 Morphism.v的[MonadHom]，读出来的是一个定理，两个方向：
 - [lift_natural]：升力是自然的，来自 [lift_bind] 在 ret ∘ g，
 两个单子的 [lift_return] 和单位律 [join_fmap_ret]；
 - [transformer_hom L : MonadHom M (T M)]，其变换有
 电梯组件（[transformer_hom_lift]、[eq_refl]）； 其单位律
 是 [lift_return]，其乘法定律为 [lift_bind] 在
 f = id，转换为 Monad/Morphism.v 的水平复合形式
 [lift_natural] 在 lift_x 处；
 - [hom_transformer θ : MonadTransformer T] 适用于任何 θ ：MonadHom M
 (T M)，其升力的分量为 θ ([hom_transformer_lift]，
 [eq_refl]）； [lift_return] 是 [mh_ret]，[lift_bind] 源自
 Monad/Morphism.v 的 [mh_join_nat]，f 处 θ 的自然性和
 [fmap_comp]。 组件系列双向往返
 （[transformer_round_trip]、[hom_round_trip]）。
这两条记录没有：
 hom_transformer (transformer_hom L) 与 L 相对应，以及 Transformer_hom
 (hom_transformer θ) 反对 θ，在 [eq_refl] 被拒绝，因为
 定律是变量记录具有投影的重建证明。 因此，一个单子 M 的变换定律恰好是以下的态射
 monads M ⟶ T M，直到法律的证明：“合适的自然
 麦克莱恩练习的“转变”，专门针对两人
 （米，TM）。 这就是 #468 要求“概括
 Monad变压器定律”。

它来自哪里。 nLab 的页面“monad Transformer”，通读
 获取页面，在返回中声明变压器条件
 绑定形式，归因于Liang、Hudak 和Jones (1995)，以及
 陈述它相当于 lift 是单子的同态：
 尊重单位的底层函子的自然变换
 和乘法。 这个文件检查的就是这个等价性
 图书馆的定义。 同一页面制作一个变压器，如所用
 在函数式编程中，范畴上的一个尖头函子
 单子，其要点是升力； 这里的类将 T 限制为一个 monad
 M 而已，所以是这样一个点的一个组成部分。

问题 #468 的前提。 其“当前状态”表示 [MonadTransformer]
 “将单子态射法则打包为 `lift : M ⟹ T M`”，引用该类
 通过行号。 自问题出现之前以来，该类一直没有变化
 归档（其最后一次提交，83b38386，是 2026 年 6 月 17 日，通过 git log），并提升
 那时和现在一样，都是一个没有自然场的赤裸家庭：前提是
 提交时不精确，[lift_natural] 是导出的缺失字段。

优势。 通过 [eq_refl]: [transformer_hom_lift], [hom_transformer_lift]
 以及两个组成部分的往返行程。 在 ≈：[lift_natural] 和定律
 两种结构。 在 [eq_refl] 处被拒绝，通过转换，固定在
 Test/ProbeMonadMorphism468.v，以组件往返作为对照
 （C26，C27）：两次全记录往返（R10，R11）。 两人都站在一个
 每个 [Qed] 的探测器依赖闭包的副本变成
 [Defined] 和 [Transparent Obligations] 集（Instance/Sets.v，
 Structure/Cartesian/Closed.v、Instance/Grp.v 和 Instance/Grp/Free.v
 保留他们的 [Qed]s），所以它们不是不透明的：重建的法则是
 与变量 L 或 θ 的投影进行比较。

宇宙，读出 [About]。 [lift_natural]、[transformer_hom] 和
 [hom_transformer] 通过 [Category@{o h h}] 绑定 [@{o h}]，在
 [MonadTransformer@{o h}] 和 [MonadHom@{o h}]，带有约束列表
 关闭且空荡荡的。 它们之所以如此，是因为没有证据使用 setoid [rewrite]：
 在 [rewrite] 证明的副本上进行测量，[lift_natural] 携带
 h <= prod_rect.u0/u1/u2，并且这两个结构中的每一个都有一个额外的
 宇宙 u 且 h < u。 四个读回状态 = 并结束其列表
 使用 [+]，对于 Coq 8.19 和标准库的 [eq] 的绑定
 8.20 添加（Monad/Morphism.v 的 UNIVERSES 段落）。 没有 [Set]，没有严格
 有界且不存在方程。

未交付。 nLab页面[Monads C]上的尖头endofunctor：
 [MonadTransformer] 不要求 T 对单子的态射起作用，并且
 这里什么都做不到。 Monad/Transformer.v 的 [MonadTransformerLaws]
 未解决：它位于该文件的注释块内，因此
 树没有这样的常量（它的 [Check] 被拒绝，“未找到”，
 同时接受 [Check @MonadTransformer]）。 无论是班级还是
 其实例 [IdentityT_MonadTransformer] 已更改。 
*)

(* [lift] is natural: [lift_bind] at ret ∘ g, then [lift_return].  / [lift] 是自然的：[lift_bind] 位于 ret ∘ g，然后是 [lift_return]。*)

Lemma lift_natural@{o h | } {C : Category@{o h h}} {M : C ⟶ C}
  {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)} {HT : @Monad C (T M)}
  (L : @MonadTransformer C M HM T HT) {x y : C} (g : x ~> y) :
  fmap[T M] g ∘ @lift C M HM T HT L x ≈ @lift C M HM T HT L y ∘ fmap[M] g.
Proof.
  pose proof (@lift_bind C M HM T HT L x y (@ret C M HM y ∘ g)) as E.
  (* the right side of E is fmap[T M] g ∘ lift x  / E 的右侧是 fmap[T M] g ∘ lift x*)
  symmetry in E.
  etransitivity; [ | etransitivity; [ exact E | ] ].
  - symmetry.
    apply compose_respects; [ | reflexivity ].
    etransitivity.
    { apply compose_respects; [ reflexivity | ].
      etransitivity; [ apply fmap_respects | ].
      - etransitivity; [ apply comp_assoc | ].
        apply compose_respects; [ apply lift_return | reflexivity ].
      - apply fmap_comp. }
    etransitivity; [ apply comp_assoc | ].
    etransitivity; [ apply compose_respects; [ apply join_fmap_ret | ];
                     reflexivity | ].
    apply id_left.
  - etransitivity.
    { apply compose_respects; [ reflexivity | apply fmap_comp ]. }
    etransitivity; [ apply comp_assoc_sym | ].
    apply compose_respects; [ reflexivity | ].
    etransitivity; [ apply comp_assoc | ].
    etransitivity; [ apply compose_respects; [ apply join_fmap_ret | ];
                     reflexivity | ].
    apply id_left.
Qed.

(** ** A transformer gives a morphism of monads M ⟶ T M  / ** 变压器给出单子 M ⟶ T M 的态射*)

Definition transformer_hom@{o h | } {C : Category@{o h h}} {M : C ⟶ C}
  {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)} {HT : @Monad C (T M)}
  (L : @MonadTransformer C M HM T HT) : MonadHom@{o h} HM HT.
Proof.
  unshelve refine
    (@Build_MonadHom C M (T M) HM HT
       (Build_Transform'@{o h h o h h} (F:=M) (G:=T M)
          (fun x => @lift C M HM T HT L x)
          (fun x y g => lift_natural L g)) _ _).
  - intros x. exact (@lift_return C M HM T HT L x).
  - intros x; simpl.
    pose proof (@lift_bind C M HM T HT L (M x) x id) as E.
    etransitivity; [ | etransitivity; [ exact E | ] ].
    + symmetry.
      etransitivity; [ | apply id_right ].
      apply compose_respects; [ reflexivity | apply fmap_id ].
    + etransitivity; [ apply comp_assoc_sym | ].
      apply compose_respects; [ reflexivity | ].
      etransitivity; [ | apply lift_natural ].
      apply compose_respects; [ | reflexivity ].
      apply fmap_respects. apply id_right.
Defined.

(* Its components are [lift], on the nose.  / 它的组件是 [lift]，位于鼻子上。*)

Example transformer_hom_lift@{o h | +} {C : Category@{o h h}} {M : C ⟶ C}
  {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)} {HT : @Monad C (T M)}
  (L : @MonadTransformer C M HM T HT) (x : C) :
  mh_transform (transformer_hom@{o h} L) x = @lift C M HM T HT L x
  := eq_refl.

(** ** A morphism of monads M ⟶ T M satisfies the transformer laws  / ** 单子 M ⟶ T M 的态射满足变换定律*)

Definition hom_transformer@{o h | } {C : Category@{o h h}} {M : C ⟶ C}
  {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)} {HT : @Monad C (T M)}
  (θ : MonadHom@{o h} HM HT) : @MonadTransformer C M HM T HT.
Proof.
  unshelve refine
    (@Build_MonadTransformer C M HM T HT (fun x => mh_transform θ x) _ _).
  - intros a. exact (mh_ret θ).
  - intros a b f.
    etransitivity;
      [ apply compose_respects; [ apply (mh_join_nat θ b) | reflexivity ] | ].
    etransitivity; [ apply comp_assoc_sym | ].
    etransitivity; [ | apply comp_assoc ].
    apply compose_respects; [ reflexivity | ].
    etransitivity; [ apply comp_assoc_sym | ].
    etransitivity;
      [ apply compose_respects;
          [ reflexivity | symmetry; apply (naturality (mh_transform θ)) ] | ].
    etransitivity; [ apply comp_assoc | ].
    apply compose_respects; [ | reflexivity ].
    symmetry. apply fmap_comp.
Defined.

Example hom_transformer_lift@{o h | +} {C : Category@{o h h}} {M : C ⟶ C}
  {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)} {HT : @Monad C (T M)}
  (θ : MonadHom@{o h} HM HT) (x : C) :
  @lift C M HM T HT (hom_transformer@{o h} θ) x = mh_transform θ x
  := eq_refl.

(* The two round trips, on the component family.  / 组件系列上的两次往返。*)

Example transformer_round_trip@{o h | +} {C : Category@{o h h}}
  {M : C ⟶ C} {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)}
  {HT : @Monad C (T M)} (L : @MonadTransformer C M HM T HT) (x : C) :
  @lift C M HM T HT (hom_transformer@{o h} (transformer_hom@{o h} L)) x
    = @lift C M HM T HT L x := eq_refl.

Example hom_round_trip@{o h | +} {C : Category@{o h h}}
  {M : C ⟶ C} {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)}
  {HT : @Monad C (T M)} (θ : MonadHom@{o h} HM HT) (x : C) :
  mh_transform (transformer_hom@{o h} (hom_transformer@{o h} θ)) x
    = mh_transform θ x := eq_refl.
