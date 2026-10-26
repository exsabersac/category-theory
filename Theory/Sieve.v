Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Sieves, and the presheaf of sieves / * 筛，以及筛的预层 *)

(*
Awodey, *Category Theory* (1st ed., Carnegie Mellon pre-print, September
   2005), §8.8 (Topoi), printed pp. 210-211, inside the proof of
   Proposition 8.17 ([awodey:8.8:def-sieve],
   [awodey:8.8:construction-omega-sieves]).  Verbatim:

     “To that end, for any category C we define a sieve on an object C to
      be any set S of arrows f : · → C (with arbitrary domain) that is
      closed under precomposition, i.e. if f : D → C is in S then so is
      f ∘ g : E → D → C for every g : E → D (think of a sieve as a
      generalization of a ”lower set“ in a poset).  Then let:

          Ω(C) = {S ⊆ C_1 | S is a sieve on C}

      and given h : D → C let:

          h* : Ω(C) → Ω(D)

      be defined by:

          h*(S) = {g : · → D | h ∘ g ∈ S}.

      This clearly defines a presheaf Ω : C^op → Sets, with a
      distinguished point,

          t : 1 → Ω,

      namely, at each C, the ”total sieve“:

          t_C = {f : · → C}.”

   This file delivers every display of that passage except the
   distinguished point t : 1 → Ω itself: the sieve, the object of sieves,
   the restriction h*, the total sieve t_C ([total_sieve], with
   [sieve_restrict_total] recording that h* fixes it), and the presheaf
   [Sieve_Presheaf].  The point t — the MORPHISM 1 ⟹ Ω in the presheaf
   category — is NOT here (see WHY THIS FILE IS LEAN below) and lives in
   Instance/Fun/Classifier.v as [sieve_truth], together with the classifier
   of Mac Lane §IV.9 construction 2 and remark 1 (book pp. 105-106,
   [maclane:IV.9:construction2], [maclane:IV.9:remark1]) that consumes it.

   WHAT A SIEVE IS HERE.  Awodey's “set S of arrows” becomes a
   [Prop]-valued membership predicate on each hom-set, carrying two
   fields beside it: respectfulness for the hom-setoid's [≈] (a set of
   arrows in a setoid-enriched category must not distinguish equivalent
   arrows) and Awodey's closure under precomposition.  Membership is
   [Prop]-valued and not [Type]-valued, and that is FORCED rather than
   chosen: a [Type@{o}]-valued sieve type sits at [o+1], so it is not the
   carrier of an object of [Sets@{o so}] — the refusal is “Cannot enforce
   o < o”, a universe inconsistency, pinned in Test/ProbeFunClassifier403.v
   with the [Prop]-valued [Sieve] as the accepted control.  The price
   of [Prop] is paid in Instance/Fun/Classifier.v, where the
   characteristic sieve must truncate a [Type]-valued existential with
   Instance/Sets/Powerset.v's [Powerset_squash] and pay for the
   truncation with #402's [Untruncate] hypothesis, spent exactly once.

   THE TRUTH-VALUE CONVENTION, stated here because the record fixes it.  The
   distinguished point of [Sieve_Presheaf] is the TOTAL sieve, so “truth”
   is [total_sieve], and Ω(c) is a set of sieves carrying no numeral —
   there is nothing here to agree or disagree with Mac Lane's “0 on the
   subset” (§IV.9 construction 1, book p. 105) or Seven Sketches' “true on
   the subset”, which name one and the same thing, the value every
   classifier puts on its subobjects.  The numeral enters only at the arrow
   shape, in Instance/Fun/Classifier.v's codes, which send the total sieve
   to [Fin.F1] — the page's 0, and also Instance/FinSet/Classifier.v's
   [fin_true]; Instance/Fun/Classifier.v's truth-value paragraph says
   exactly how much of a “convention” that is.

   WHY THIS FILE IS LEAN.  Its transitive in-project closure is 16
   modules, a SUBSET of both Theory/Sheaf.v's (18) and
   Construction/Localization.v's (23) — measured as a set, and the
   set difference is empty in both cases — the two files whose prose
   already mentions sieves (SGA 4's Grothendieck topologies, and covering
   sieves for orthogonal localization), so either could Require it later at
   ZERO extra module cost.  NEITHER IS REWIRED HERE; that is a future
   reuse, and the measurement is what makes it cheap rather than a
   promise.  Putting the truth point here instead would drag in
   Structure/Terminal, Instance/Fun and Instance/Fun/Terminal, whose own
   closure is 60, which is why [sieve_truth] lives downstream.
   For the same reason the reading of a sieve as a SUBOBJECT OF THE
   REPRESENTABLE PRESHEAF — Awodey's “lower set” made categorical — is NOT here
   either: it needs Functor/Hom.v's [Curried_CoHom] and
   Instance/Fun/Morphisms.v's pointwise mono characterisation, neither of which
   is in this closure.  It is Instance/Fun/Classifier.v's [sieve_subpresheaf] /
   [sieve_incl] / [sieve_subobject], where the classifier's uniqueness clause
   consumes the [sieve_subpresheaf] half together with its cone, while
   [sieve_incl] and [sieve_subobject] are the checkbox itself and have no
   consumer (measured there by deleting them).

   UNIVERSES, measured off BOTH binder and block.  NOT ONE of this file's
   constraint blocks contains a universe EQUATION; every entry is [<] or
   [<=].  The identification of hom with proof sits in the BINDER and is
   the record's own — [Sieve@{u u0}] is over [C : Category@{u u0 u0}]
   with a LITERALLY EMPTY block — because [sieve_respects] mentions [≈]
   on homs.  [SieveObj@{u u0 u1 u2}] carries [Set < u] (from [Prop :
   Type@{Set+1}], a strict lower bound and never a pin), [u1 <= u] and
   [u2 <= u]: the first of those two is Awodey's “for any SMALL category
   C” — C's objects at or below the carrier universe — and it is a BOUND,
   not an equation.  [Sieve_Presheaf] adds [Sets]' own [o < so] and one
   strict bound of the [Functor] record's, and no equation; ELEVEN of
   this file's 22 constants carry a word-bounded [Set], always as that
   same lower bound.
   The identifications the presheaf CATEGORY forces (C's hom with C's
   proof, and C's hom with [Sets]' carrier universe) are [Opposite]'s and
   [Fun]'s and appear only downstream; nothing here forces them, which is
   why this file can be Required by a consumer that never forms
   [[C^op, Sets]].

   COUNTS, WITH THEIR CRITERIA.  Constants closed under the global
   context: 22/22, zero [Axioms:] lines, counted as the 21 entries
   [Print Module] emits at five-space indent (the record's three
   projections and NINE [Program] obligations among them) plus
   [Build_Sieve], which it lists only after a [:=]; every one queried
   FULLY QUALIFIED, and all 22 are in the [print-assumptions] gate.
   [Defined] tokens: 0.  Statements closed by [:= eq_refl]: 0 (the
   readbacks are downstream, where the classifier is).  There is no
   refutation command in this file and it contributes ZERO [make todo]
   hits.

   NOT DELIVERED HERE.  No truth point, no classifier, no representable
   reading (all downstream, as above).  No Grothendieck topology, no
   coverage, no sheaf condition, and no relation to Theory/Sheaf.v's
   [Class Site], whose covering families are vector-indexed and carry no
   closure-under-precomposition condition at all.  No lattice of sieves:
   the pointwise order, meets, joins and pullback-stability are not
   built.  No comparison at a poset with a lower-set construction.  No
   cosieve (the covariant dual).  Nothing here is registered as an
   [Instance] except [Sieve_Setoid], which [SieveObj] needs.

--------
Awodey，*范畴论*（第一版，卡内基梅隆大学预印本，九月
 2005），§8.8（Topoi），印刷第 210-211 页，在证明内
 提案 8.17（[awodey:8.8:def-sieve]，
 [awodey:8.8:construction-omega-sieves]）。 逐字：

“为此，对于任何范畴 C，我们在对象 C 上定义一个筛子，以
 是箭头 f : · → C（具有任意域）的任意集合 S，即
 在预合成下闭合，即如果 f : D → C 在 S 中，那么也是
 f ∘ g : E → D → C 对于每个 g : E → D （将筛子视为
 偏序集中“下集”的概括）。 然后让：

Ω(C) = {S ⊆ C_1 | S是C上的筛子}

并给定 h : D → C 令：

h* : Ω(C) → Ω(D)

定义为：

h*(S) = {g : · → D | h ∘ g ∈ S}。

这清楚地定义了预束 Ω : C^op → 集合，其中
 突出点，

t：1→Ω，

即，在每个 C 处，“总筛分”：

t_C = {f : · → C}。“

该文件提供该段落的所有显示，除了
 区分点 t : 1 → Ω 本身：筛子，筛子的对象，
 限制 h*，总筛分 t_C ([total_sieve]，其中
 [sieve_restrict_total] 记录 h* 修复了它），以及预束
 [Sieve_Presheaf]。 点 t — 预束中的 MORPHISM 1 ⟹ Ω
 范畴 - 不在这里（请参阅下面为什么这个文件很精简）并且存在于
 Instance/Fun/Classifier.v 作为 [sieve_truth]，与分类器一起
 Mac Lane §IV.9 构造 2 和备注 1（本书第 105-106 页，
 [maclane:IV.9:construction2]、[maclane:IV.9:remark1]）消耗它。

这是什么筛子。 Awodey 的“S 组箭头”变成了
 每个 hom 集上的 [Prop] 值成员谓词，携带两个
 旁边的字段：尊重 hom-setoid 的 [≈]（一组
 setoid 丰富范畴中的箭头不得区分等效项
 箭头）和预合成下的 Awodey 闭包。 会员资格是
 [Prop] 值而不是 [Type] 值，这是强制而不是
 选择：[Type@{o}] 值的筛子类型位于 [o+1]，因此它不是
 [Sets@{o so}] 对象的载体 — 拒绝是“无法强制执行
 o < o”，宇宙不一致，固定在 Test/ProbeFunClassifier403.v 中
 将 [Prop] 值 [Sieve] 作为可接受的对照。 价格
 [Prop] 在 Instance/Fun/Classifier.v 中支付，其中
 特征筛必须截断 [Type] 值的存在式
 Instance/Sets/Powerset.v 的 [Powerset_squash] 并支付费用
 用 #402 的 [Untruncate] 假设进行截断，只用了一次。

真相价值惯例，在这里声明，因为记录修复了它。 的
 [Sieve_Presheaf]的显着点是TOTAL筛，所以“真相”
 是 [total_sieve]，Ω(c) 是一组不带数字的筛子 —
 这里没有什么可以同意或不同意麦克莱恩的“0 on the
 子集”（§IV.9 结构 1，书第 105 页）或七个草图““正确
 子集”，它命名一个且相同的事物，每个值
 分类器放置其子对象。 数字仅在箭头处输入
 shape，在 Instance/Fun/Classifier.v 的代码中，发送总筛子
 到 [Fin.F1] — 页面的 0，以及 Instance/FinSet/Classifier.v 的
 [fin_true]； Instance/Fun/Classifier.v 的真值段落说
 这究竟是一个多么“约定”的事情。

为什么这个文件很精简。 它的传递性项目内闭包是 16
 模块，Theory/Sheaf.v (18) 的子集和
 Construction/Localization.v's (23) — 作为一个集合进行测量，并且
 在这两种情况下，设置差异都是空的——这两个文件的散文
 已经提到了筛子（SGA 4 的 Grothendieck 拓扑，并覆盖
 用于正交定位的筛子），因此稍后可以要求它
 零额外模块成本。 两者都没有在这里重新布线； 那是一个未来
 重复使用，测量是它便宜的原因，而不是
 承诺。 相反，把真相点放在这里会拖累
 结构/终端、实例/乐趣和实例/乐趣/终端，各自的
 闭包值为 60，这就是 [sieve_truth] 位于下游的原因。
出于同样的原因，将筛子的读数作为 THE 的子对象
 代表性的 PRESHEAF — Awodey 的“下集”已明确 — 不在这里
 要么：它需要 Functor/Hom.v 的 [Curried_CoHom] 和
 Instance/Fun/Morphisms.v 的逐点单声道表征，两者都不是
 就在这个闭包中。 它是 Instance/Fun/Classifier.v 的 [sieve_subpresheaf] /
 [sieve_incl] / [sieve_subobject]，其中分类器的唯一性子句
 消耗 [sieve_subpresheaf] 的一半及其锥体，同时
 [sieve_incl] 和 [sieve_subobject] 是复选框本身，没有
 消费者（通过删除它们来测量）。

宇宙，从粘合剂和块上测量。 不是该文件之一
 约束块包含一个Universe EQUATION； 每个条目都是 [<] 或
 [<=]。 带有证据的 hom 标识位于 BINDER 中，并且是
 记录自己的 — [Sieve@{u u0}] 超过 [C : Category@{u u0 u0}]
 带有一个字面意义上的空块 - 因为 [sieve_respects] 提到了 [≈]
 在霍姆斯。 [SieveObj@{u u0 u1 u2}] 携带 [Set < u]（来自[Prop：
 输入@{Set+1}]，严格的下限，绝不是引脚），[u1 <= u] 和
 [u2 <= u]：这两个中的第一个是 Awodey 的“对于任何小型范畴
 C”——C 的物体位于或低于载体宇宙——并且它是一个束缚，
 不是一个方程式。 [Sieve_Presheaf] 增加了 [Sets] 自己的 [o < so] 和一个
 [Functor] 记录的严格限制，并且没有方程式； 十一个
 该文件的 22 个常量带有字限制的 [Set]，始终如此
 相同的下限。 
预束 CATEGORY 强制的标识（C 的 hom 与 C 的
 证明，C 的 hom 与 [Sets] 的载体宇宙）是 [Opposite] 的和
 [Fun] 和 仅出现在下游； 这里没有什么强迫他们，那就是
 为什么从未形成的消费者可能需要此文件
 [[C^op, Sets]]。

重要的是他们的标准。 全局下常量关闭
 上下文：22/22，零 [Axioms:] 行，计为 21 个条目
 [Print Module] 以五个空格缩进（记录的三个
 预测和其中九项 [Program] 义务）加上
 [Build_Sieve]，仅在 [:=] 之后列出； 每个人都询问过
 完全合格，所有 22 个都在 [print-assumptions] 门中。 
[Defined] 代币：0。[:= eq_refl] 关闭的语句：0（
 回读位于下游，分类器所在的位置）。 没有
 该文件中的反驳命令，它贡献了零 [make todo]
 命中。

不在这里交付。 没有真值点，没有分类器，没有可表示的
 阅读（所有下游，如上所述）。 没有格洛腾迪克拓扑，没有
 覆盖范围，无层条件，与 Theory/Sheaf.v 无关
 [Class Site]，其覆盖家族是向量索引的并且不携带
 完全处于预合成条件下的闭合。 无筛网格子：
 逐点顺序、相遇、连接和回拉稳定性不是
 建造的。 没有将偏序集与较低集结构进行比较。 否
 cosieve（协变对偶）。 这里没有任何内容被注册为
 [Instance] 除了 [Sieve_Setoid] 之外，[SieveObj] 需要 [Sieve_Setoid]。
*)

#[local] Obligation Tactic := idtac.

(* ------------------------------------------------------------------ *)
(** ** Sieves / ** 筛子 *)

(*
A sieve on c: a Prop-valued membership on the arrows into c, closed
   under [≈] and under precomposition.

--------
c上的筛子：箭头指向c的Prop值成员资格，在[≈]下以及在预组合下闭合。
*)

Record Sieve {C : Category} (c : C) := {
  sieve_mem : ∀ (d : C), (d ~> c) → Prop;

  (* membership does not distinguish ≈-equal arrows / 成员资格不区分≈-相等的箭头 *)
  sieve_respects : ∀ (d : C) (f g : d ~> c),
      f ≈ g → sieve_mem d f → sieve_mem d g;

  (* Awodey's closure: f ∈ S implies f ∘ g ∈ S / Awodey 的闭包：f ∈ S 意味着 f ∘ g ∈ S *)
  sieve_closed : ∀ (d e : C) (f : d ~> c) (g : e ~> d),
      sieve_mem d f → sieve_mem e (f ∘ g)
}.

Arguments sieve_mem {C c} _ {d} _.
Arguments sieve_respects {C c} _ {d} _ _ _ _.
Arguments sieve_closed {C c} _ {d e} _ _ _.

(* Two sieves are equivalent when they have the same members. / 当两个筛子有相同的成员时，它们是等价的。 *)
Definition sieve_equiv {C : Category} {c : C} : crelation (Sieve c) :=
  fun S T => ∀ (d : C) (f : d ~> c), sieve_mem S f <-> sieve_mem T f.

#[export]
Program Instance Sieve_Setoid {C : Category} (c : C) : Setoid (Sieve c) := {|
  equiv := sieve_equiv
|}.
Next Obligation.
  intros C c.
  constructor; repeat intro.
  - split; auto.
  - split; apply X.
  - split; intro H.
    + apply X0, X, H.
    + apply X, X0, H.
Qed.

(* Awodey's Ω(C), as an object of [Sets]. / Awodey 的 Ω(C)，作为 [Sets] 的一个对象。 *)
Definition SieveObj {C : Category} (c : C) : SetoidObject := {|
  carrier := Sieve c ; is_setoid := Sieve_Setoid c
|}.

(* ------------------------------------------------------------------ *)
(** ** The total sieve, and restriction / ** 总筛和限制 *)

(* Awodey's t_C = {f : · → C}: every arrow into c. / Awodey 的 t_C = {f : · → C}：每一个指向 C 的箭头。 *)
Program Definition total_sieve {C : Category} (c : C) : Sieve c := {|
  sieve_mem := fun _ _ => True
|}.
Next Obligation. intros; exact I. Qed.
Next Obligation. intros; exact I. Qed.

(* Awodey's h*(S) = {g | h ∘ g ∈ S}, for h : d ~> c in C. / Awodey 的 h*(S) = {g | h ∘ g ∈ S}, 对于 C 中的 h : d ~> c。 *)
Program Definition sieve_restrict {C : Category} {c d : C} (h : d ~> c)
        (S : Sieve c) : Sieve d := {|
  sieve_mem := fun e (g : e ~> d) => sieve_mem S (h ∘ g)
|}.
Next Obligation.
  intros C c d h S e f g Hfg Hmem.
  eapply sieve_respects; [ | exact Hmem ].
  now rewrite Hfg.
Qed.
Next Obligation.
  intros C c d h S e e' f g Hmem.
  eapply sieve_respects.
  - symmetry; apply comp_assoc.
  - now apply sieve_closed.
Qed.

(*
Restriction carries the total sieve to the total sieve; this is the
   naturality content of the truth point built downstream.

--------
限制把总筛传递到总筛；这是下游构建的真理点的自然性内容。
*)
Lemma sieve_restrict_total {C : Category} {c d : C} (h : d ~> c) :
  sieve_restrict h (total_sieve c) ≈ total_sieve d.
Proof. intros e g; split; intro; exact I. Qed.

Program Definition sieve_restrict_mor {C : Category} {c d : C} (h : d ~> c) :
  SieveObj c ~{Sets}~> SieveObj d := {|
  morphism := sieve_restrict h
|}.
Next Obligation.
  intros C c d h.
  unfold Proper, respectful; intros S T HST e g; simpl.
  split; intro H; now apply HST.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The presheaf of sieves / ** 篱笆的前层 *)

(*
Awodey's Ω : C^op → Sets.  The three functor laws are the three
   category laws of C read through membership: respectfulness of [fmap]
   is [sieve_respects] at [h ≈ h'], the identity law is [id_left] and
   the composition law is [comp_assoc].

--------
Awodey 的 Ω : C^op → 集合。三个函子定律是 C 的三个范畴定律，通过成员关系来理解：[fmap] 的尊重性在 [h ≈ h'] 上是 [sieve_respects]，恒等律是 [id_left]，合成律是 [comp_assoc]。
*)

Program Definition Sieve_Presheaf (C : Category) : C^op ⟶ Sets := {|
  fobj := fun c => @SieveObj C c;
  fmap := fun x y (h : x ~{C^op}~> y) => @sieve_restrict_mor C x y h
|}.
Next Obligation.
  intros C x y.
  unfold Proper, respectful; intros h h2 Hh S d g; simpl.
  split; intro H; eapply sieve_respects; try exact H;
    [ now rewrite Hh | now rewrite Hh ].
Qed.
Next Obligation.
  intros C x S d f.
  simpl; split; intro H.
  - eapply sieve_respects; [ | exact H ]. apply id_left.
  - eapply sieve_respects; [ | exact H ]. symmetry; apply id_left.
Qed.
Next Obligation.
  intros C x y z f g S d k.
  simpl; split; intro H.
  - eapply sieve_respects; [ | exact H ]. symmetry; apply comp_assoc.
  - eapply sieve_respects; [ | exact H ]. apply comp_assoc.
Qed.
