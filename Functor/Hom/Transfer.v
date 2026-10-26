Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Morphisms.
Require Import Category.Functor.Hom.

Generalizable All Variables.

(** * Mac Lane §IV.3's transfer lemma: representable transformations  / * Mac Lane §IV.3 的转移引理：可表示变换*)

(*
SOURCES.

   Mac Lane, CWM 2nd ed., §IV.3, printed p. 91 (read from the page image
   p367-100.png):

     “Lemma.  Let f* : A(a, −) ⇸ A(b, −) be the natural transformation
      induced by an arrow f : b → a of A.  Then f* is monic if and only
      if f is epi, while f* is epi if and only if f is a split monic
      (i.e., if and only if f has a left inverse).”

   and, immediately below it on the same page (same image):

     “Note that f* ↦ f is the bijection Nat(A(a, −), A(b, −)) ≅ A(b, a)
      given by the Yoneda lemma.”

   and

     “Observe, also, that for functors S, T : C → B, a natural
      transformation τ : S ⇸ T is epi (respectively, monic) in B^C if and
      only if every component τ_c : S_c → T_c is epi (respectively, monic)
      in B for B = Set; this follows by Exercise III.4.4, computing the
      pushout pointwise as in Exercise III.5.5.”

   and the proof itself (same image):

     “Proof.  For h ∈ A(a, c), f*h = hf.  Hence the first result is just
      the definition of an epi f.  If f* is epi, there is an h_0 : a → b
      with f*h_0 = h_0 f = 1 : b → b, so f has a left inverse.  The
      converse is immediate.”

   Catalog id: maclane:IV.3:lem1.  The theorem the lemma serves is
   maclane:IV.3:thm1, in Adjunction/FullFaithful.v.

   NAMING.  Mac Lane writes the induced transformation f*.  That spelling
   is not used here: `*` is multiplication notation in several scopes of
   this library, and a bare `f*` would be a parsing hazard.  The
   transformation is [hom_transfer f].

   WHAT IS DELIVERED AND AT WHAT STRENGTH.

   Over an ARBITRARY category A and an ARBITRARY arrow f : b ~> a:

   - [hom_transfer f : [Hom a,─] ⟹ [Hom b,─]], component at c the
     precomposition h ↦ h ∘ f.  It is built by hand rather than taken to
     be [fmap[Curried_Hom A] f]; the relation between the two is
     MEASURED rather than assumed, see MEASUREMENTS below.
   - [hom_transfer_monic_iff_epic] : monic in [A, Sets] ⟺ f is [Epic].
   - [hom_transfer_epic_iff_section] : epic in [A, Sets] ⟺ f is
     [Section].  The library's split monomorphism is [Section]
     (Theory/Morphisms.v, aliased [SplitMono]): a chosen LEFT
     inverse, carried as data.  It is deliberately NOT [Monic]: a monic
     need not split, and the reviewer check for this issue asks for the
     split notion.
   - Both biconditionals are [Defined], not [Qed], because both carry
     data in both directions: the forward half of the second EXTRACTS a
     left inverse from the surjectivity of the component at b.

   ROUTE.  Mac Lane's, in three steps, exactly as his proof runs:

   (1) The pointwise characterisation of monos and epis in a functor
       category valued in Set.  This is Mac Lane's “Observe, also”
       paragraph above, which is the catalog item maclane:IV.3:remark1
       and is IN TREE as Instance/Fun/Morphisms.v.  The scripts below
       consume its four one-directional halves by name — the two
       target-agnostic ones [pointwise_monic_is_monic] and
       [pointwise_epic_is_epic] for the backward directions, and
       the two [Sets]-specific converses [sets_functor_monic_pointwise]
 and [sets_functor_epic_pointwise] for the forward
       ones — rather than the packaged biconditionals
       [sets_functor_monic_iff_pointwise] and
       [sets_functor_epic_iff_pointwise], which are those same
       halves paired.  Nothing here is restated.
   (2) The characterisation of monos and epis in Sets as the injections
       and the surjections: Instance/Sets.v's [injectivity_is_monic]
 and [surjectivity_is_epic], the second's backward
       leg exposed as [epic_implies_surjective].  Also consumed.
   (3) The two elementary observations Mac Lane's proof then makes:
       injectivity of h ↦ h ∘ f at every c IS right-cancellability of f,
       and surjectivity at c := b applied to id[b] produces the left
       inverse, while a left inverse s makes every component surjective
       by k ↦ k ∘ s.

   THE YONEDA BIJECTION IS CITED, NOT ROUTED THROUGH.  Mac Lane's
   remark that f ↦ f* is the Yoneda bijection is true here as well —
   [Yoneda_Full]/[Yoneda_Faithful] (Functor/Hom.v) and
   [Yoneda_Embedding'] are exactly that — but no statement below
   consumes them, and that is a deliberate universe decision, not an
   oversight: [Yoneda_Embedding'] is stated over a category whose
   object, hom and proof universes are IDENTIFIED, and routing the
   transfer lemma through it would inherit that identification for no
   gain.  What is recorded instead is the definitional identification
   [hom_transfer_is_fmap] below, from which the Yoneda reading follows
   by citation.

   MEASUREMENTS (strict first).

   - [hom_transfer_component] : the component's value at h is h ∘ f, at
     Leibniz [=], by [eq_refl].  Deliberate strictness, labelled.
   - The comparison with [fmap[Curried_Hom A] f] was measured on a
     three-rung ladder and the answer is NOT uniform, so the header does
     not say “it is [fmap]” without qualification.  VALUES agree at
     Leibniz [=] ([hom_transfer_is_fmap_value], [eq_refl]): both sides
     compute h ∘ f, because [Curried_Hom]'s arrow action is
     `fun g => g ∘ op f` and [op] moves no data
     (Construction/Opposite.v).  The COMPONENT record does NOT
     ([SetoidMorphism] carries a [proper_morphism] certificate, and the
     two are separately elaborated obligations), and neither does the
     whole [Transform] record, which additionally rebuilds [naturality]
     and [naturality_sym].  What holds at record level is [≈] in the
     functor category, [hom_transfer_is_fmap], whose proof is
     `intros c h; reflexivity` — that is, the [≈] is carried entirely by
     the value-level [eq_refl].  Both refutations are pinned as
     CONVERSION negatives in Test/ProbeFullFaithful367.v.
   - [hom_transfer_at_id] : the Yoneda-side readback
     `transform[hom_transfer f] a id ≈ f` holds only up to [≈], not at
     [eq_refl]: the value is `id ∘ f`, and [id_left] is a law field of
     [Category], so conversion does not remove it.  The strict form is
     pinned as a CONVERSION negative in
     Test/ProbeFullFaithful367.v.
   - [hom_transfer] is a [Program Definition] with ZERO remaining
     obligations: the library's obligation tactic (Lib/Tactics.v,
     installed by Lib.v) discharges respectfulness of `h ↦ h ∘ f` and
     both naturality fields, each of which is one [comp_assoc].

   ENGINEERING FINDINGS.

   - `[Hom a,─]` is the notation of Functor/Hom.v for
     `@Curried_Hom _ a`, which parses as the OBJECT action of
     [Curried_Hom] at a — the [Curried_Hom : Category >-> Functor]
     coercion (Functor/Hom.v) is what makes `a` land in the object
     slot.  So `[Hom a,─] : A ⟶ Sets`, not a functor out of A^op.
   - An arrow `f : b ~{A}~> a` IS an arrow `a ~{Opposite A}~> b` on the
     nose, so [fmap[Curried_Hom A] f] typechecks with no coercion; the
     ascription in [hom_transfer_is_fmap] is for the reader.
   - DISPLAY HAZARD.  Because of the [Curried_Hom : Category >-> Functor]
     coercion, an error message about `fmap[Curried_Hom A] f` prints as
     `fmap[A] f` — the functor is displayed by the CATEGORY it was
     coerced from.  Both refuted [eq_refl]s above read that way, and a
     reader who does not know the coercion will look for a functor named
     A.
   - The two biconditionals are stated with the ambient category written
     out, `@Monic ([A, Sets]) _ _ (hom_transfer f)`.  Left implicit, the
     elaborator has no way to choose between the functor category and
     [Sets] for a transformation whose components are [Sets]-morphisms.

   NOT DELIVERED.  No statement about the CONTRAVARIANT induced
   transformation `A(−,b) ⟹ A(−,a)` and no dual pair of biconditionals
   for it; no naturality of [hom_transfer] in f (that it is [fmap] of a
   functor is recorded, but no consequence is drawn); no [Monic]/[Epic]
   statement for a transformation between representables at a target
   other than [Sets]; no identification of [hom_transfer] with anything
   in Functor/Hom/Yoneda.v beyond the citation above; and no
   representability or [Full]/[Faithful] corollary. 

--------
来源。

Mac Lane，CWM 第二版，§IV.3，印刷页。 91（从页面图像中读取
 p367-100.png）：

“引理。设 f* : A(a, −) ⇸ A(b, −) 为自然变换
 由箭头 f : b → a of A 诱导。则 f* 是单调的当且仅
 如果 f 是 epi，而 f* 是 epi 当且仅当 f 是分割单子
 （即，当且仅当 f 有左逆）。”

并且，在同一页面的正下方（同一张图片）：

“注意 f* ↦ f 是双射 Nat(A(a, −), A(b, −)) ≅ A(b, a)
 由米田引理给出。”

和

“还要观察，对于函子 S, T : C → B，一个自然的
 变换 τ : S ⇸ T 是 B^C 中的 Epi（分别为单子），如果和
 仅当每个分量 τ_c : S_c → T_c 都是 epi （分别为单子）
 在 B 中，B = 集合； 接下来是练习 III.4.4，计算
 如练习 III.5.5 中那样逐点推出。”

以及证明本身（同一张图片）：

“证明。对于 h ∈ A(a, c)，f*h = hf。因此第一个结果就是
 epi f 的定义。 如果 f* 是 epi，则有 h_0 : a → b
 其中 f*h_0 = h_0 f = 1 : b → b，因此 f 有左逆元。 的
 交谈是立即的。”

目录 ID：maclane:IV.3:lem1。 引理所服务的定理是
 Maclane:IV.3:thm1，在 Adjunction/FullFaithful.v 中。

命名。 Mac Lane 写出了诱导变换 f*。 那个拼写
 这里不使用：“*”是多个范围内的乘法符号
 这个库，并且裸露的“f*”将是一个解析危险。 的
 转换为[hom_transfer f]。

交付了什么以及强度如何。

在任意类别 A 和任意箭头 f : b ~> a 上：

- [hom_transfer f : [Hom a,─] ⟹ [Hom b,─]]，组件位于 c
 预合成 h ↦ h ∘ f。 它是手工建造的，而不是带到
 是 [fmap[Curried_Hom A] f]； 两者之间的关系是
 测量值而非假设值，请参阅下面的测量值。 
- [hom_transfer_monic_iff_epic] ：[A, Sets] ⟺ f 中的莫尼克是 [Epic]。 
- [hom_transfer_epic_iff_section] ：[A, Sets] 中的史诗⟺ f 是
 [Section]。 该库的分裂单态性是 [Section]
 （Theory/Morphisms.v，别名 [SplitMono]）：选择的 LEFT
 逆，作为数据携带。 它故意不是 [Monic]：一个莫尼克
 不需要拆分，审稿人检查此问题时要求
 分裂的观念。 
- 两个双条件都是 [Defined]，而不是 [Qed]，因为两者都带有
 双向数据：第二个的前半部分 EXTRACTS a
 左为 b 处分量的满射性的倒数。

路线。 麦克莱恩的证明分三步进行：

(1) 函子中 monos 和 epis 的逐点表征
 Set 中的类别值。 这是麦克莱恩的“也观察”
 上面的段落，这是目录项 maclane:IV.3:remark1
 并且在树中为 Instance/Fun/Morphisms.v。 下面的脚本
 按名称消耗它的四个单向一半——两个
 与目标无关的 [pointwise_monic_is_monic] 和
 [pointwise_epic_is_epic] 用于向后方向，以及
 两个 [Sets] 专用的与 [sets_functor_monic_pointwise] 相对
 [sets_functor_epic_pointwise] 用于前锋
 那些 - 而不是打包的双条件
 [sets_functor_monic_iff_pointwise] 和
 [sets_functor_epic_iff_pointwise]，它们是相同的
 两半配对。 这里没有重述任何内容。 (2) Sets中monos和epis作为注射剂的表征
 和投影：Instance/Sets.v 的 [injectivity_is_monic]
 [surjectivity_is_epic]，第二个向后
 腿部暴露为 [epic_implies_surjective]。
也消耗掉了。 (3) Mac Lane 的证明提出了两个基本观察结果：
 h ↦ h ∘ f 在每个 c 处的单射性是 f 的右可消去性，
 将 c := b 处的满射性应用于 id[b] 产生左侧
 逆，而左逆 s 使每个分量都满射
 由 k ↦ k ∘ s。

米田双射是被引用的，而不是通过的。 麦克莱恩的
 注意到 f ↦ f* 是米田双射在这里也成立 —
 [Yoneda_Full]/[Yoneda_Faithful] (Functor/Hom.v) 和
 [Yoneda_Embedding'] 正是如此 - 但下面没有任何声明
 消耗它们，这是一个深思熟虑的宇宙决定，而不是一个
 监督：[Yoneda_Embedding'] 是针对一个类别进行说明的，该类别
 对象、hom 和证明宇宙已被识别，并路由
 通过它传递引理将继承该标识，无需
 增益。 相反，记录的是定义标识
 [hom_transfer_is_fmap] 下面，米田读数如下
 通过引用。

测量（严格第一）。

- [hom_transfer_component] : h 处的分量值为 h ∘ f, at
 莱布尼兹 [=]，由 [eq_refl] 设计。 刻意严格，贴上标签。 - 与 [fmap[Curried_Hom A] f] 的比较是在
 三级梯子，答案不统一，所以标题不统一
 不要毫无条件地说“这是[fmap]”。 价值观一致
 莱布尼兹 [=]（[hom_transfer_is_fmap_value]、[eq_refl]）：两侧
 计算 h ∘ f，因为 [Curried_Hom] 的箭头动作是
 `fun g => g ∘ op f` 且 [op] 不移动任何数据
 （构造/对面.v）。 COMPONENT 记录不
 （[SetoidMorphism] 带有 [proper_morphism] 证书，并且
 两项是单独阐述的义务），而且也没有
 整个 [Transform] 记录，另外重建 [naturality]
 和 [naturality_sym]。
保持记录水平的是 [≈]
 函子类别 [hom_transfer_is_fmap]，其证明为
 `介绍 c h； reflexivity` — 也就是说，[≈] 完全由
 价值级 [eq_refl]。 两种反驳都被固定为
 Test/ProbeFullFaithful367.v 中的转换阴性。 - [hom_transfer_at_id]：米田侧回读
 `transform[hom_transfer f] a id ≈ f` 仅适用于 [≈]，而不适用于
 [eq_refl]：值为`id ∘ f`，[id_left]是
 [Category]，因此转换不会删除它。 严格的形式是
 固定为 CONVERSION 负数
 测试/ProbeFullFaithful367.v。 - [hom_transfer] 是 [Program Definition]，剩余量为零
 义务：图书馆的义务策略（Lib/Tactics.v，
 由 Lib.v 安装）尊重 `h ↦ h ∘ f` 和
 两个自然场，每个场都是一个 [comp_assoc]。

工程发现。

- `[Hom a,─]` 是 Functor/Hom.v 的表示法
 `@Curried_Hom _ a`，解析为 OBJECT 操作
 [Curried_Hom] — [Curried_Hom : Category >-> Functor]
 强制 (Functor/Hom.v) 是使 `a` 落在对象中的原因
 插槽。 所以“[Hom a,─] : A ⟶ Sets”，不是 A^op 中的函子。 
- 箭头 `f : b ~{A}~> a` 是箭头 `a ~{Opposite A}~> b`
 鼻子，所以 [fmap[Curried_Hom A] f] 无需强制进行类型检查； 的
 [hom_transfer_is_fmap] 中的归属供读者使用。 
- 显示危险。 因为 [Curried_Hom : Category >-> Functor]
 强制，有关“fmap[Curried_Hom A] f”的错误消息打印为
 `fmap[A] f` — 函子按其所属类别显示
 被胁迫而来。 上面都反驳了 [eq_refl] 的读法，并且
 不知道强制转换的读者会寻找一个名为的函子
 A.
 - 两个双条件都用环境类别来说明
 输出，`@Monic ([A, Sets]) _ _ (hom_transfer f)`。 左隐含地，
 阐述者无法在函子类别和
 [Sets] 用于组件为 [Sets] 态射的变换。

未交付。 没有关于逆变引起的声明
 变换 `A(−,b) ⟹ A(−,a)` 并且没有双条件对
 为了它； f 中的 [hom_transfer] 没有自然性（它是 a 的 [fmap]）
 函子被记录，但没有得出结果）； 无 [Monic]/[Epic]
 目标可表示之间转换的语句
 [Sets] 除外； [hom_transfer] 无法与任何东西识别
 在 Functor/Hom/Yoneda.v 中，除了上面的引用之外； 没有
 可表征性或 [Full]/[Faithful] 推论。 
*)

Section Transfer.

Context {A : Category}.

(* ** The induced transformation  / ** 诱发的转变*)

(*
Mac Lane's f*: precomposition with f, natural in the second variable
   because composition is associative. 

--------
Mac Lane 的 f*：与 f 预合成，自然在第二个变量中
 因为组合是结合性的。 
*)

Program Definition hom_transfer {a b : A} (f : b ~> a) :
  [Hom a ,─] ⟹ [Hom b ,─] := {|
  transform := fun c => {| morphism := fun h => h ∘ f |}
|}.

(*
The component's value, at Leibniz equality.  Deliberate strictness:
   this is one of the file's two uses of [=] on morphisms, and it is an
   acceptance test rather than a mathematical claim. 

--------
莱布尼茨等式下的分量值。 刻意严格：
 这是该文件在态射上使用 [=] 的两个用途之一，它是一个
 验收测试而不是数学声明。 
*)

Example hom_transfer_component {a b : A} (f : b ~> a) (c : A)
        (h : a ~> c) : transform[hom_transfer f] c h = h ∘ f := eq_refl.

(*
[hom_transfer f] and the arrow action of the curried hom-functor at f,
   read as an arrow of the opposite category.  Measured strict first: the
   VALUES agree at Leibniz [=] (below), the whole [Transform] record does
   NOT, and the transformations agree at [≈] in the functor category.  See
   MEASUREMENTS in the header. 

--------
[hom_transfer f] 和 f 处柯里化 hom 函子的箭头动作，
 读作相反类别的箭头。 首先严格测量：
 价值观与 Leibniz [=] 一致（如下），整个 [Transform] 记录确实如此
 NOT，并且变换在函子类别中的 [≈] 上一致。 参见
 标题中的测量值。 
*)

Example hom_transfer_is_fmap_value {a b : A} (f : b ~> a) (c : A)
        (h : a ~> c) :
  transform[hom_transfer f] c h
    = transform[fmap[Curried_Hom A] (f : a ~{Opposite A}~> b)] c h
  := eq_refl.

Lemma hom_transfer_is_fmap {a b : A} (f : b ~> a) :
  hom_transfer f
    ≈[[A, Sets]] fmap[Curried_Hom A] (f : a ~{Opposite A}~> b).
Proof. intros c h; reflexivity. Qed.

(*
The Yoneda-side readback reaches [≈] and no further: the value is
   `id ∘ f`.  The strict form is refuted, and pinned in the probe. 

--------
米田侧读回达到 [≈]，不再进一步：该值是
 `id ∘ f`。 严格的形式被驳斥，并固定在探针中。 
*)

Lemma hom_transfer_at_id {a b : A} (f : b ~> a) :
  transform[hom_transfer f] a id ≈ f.
Proof. exact (id_left f). Qed.

(* ** Mac Lane's lemma, first half: monic ⟺ epi  / ** Mac Lane 引理，前半部分：monic ⟺ epi*)

(*
“For h ∈ A(a, c), f*h = hf.  Hence the first result is just the
   definition of an epi f.”  In this setoid setting the sentence becomes
   three steps: monic in the functor category is componentwise monic
   (Instance/Fun/Morphisms.v), componentwise monic in Sets is
   componentwise injective (Instance/Sets.v), and componentwise
   injectivity of h ↦ h ∘ f IS right-cancellability of f. 

--------
“对于 h ∈ A(a, c)，f*h = hf。因此第一个结果就是
 epi f 的定义。” 在这个 setoid 设置中，句子变成
 三步：函子范畴中的 monic 是 componentwise monic
 (Instance/Fun/Morphisms.v)，集合中的组件式莫尼克是
 组件单射 (Instance/Sets.v) 和组件
 h ↦ h ∘ f 的单射性是 f 的右可消去性。 
*)

Theorem hom_transfer_monic_iff_epic {a b : A} (f : b ~> a) :
  @Monic ([A, Sets]) _ _ (hom_transfer f) ↔ Epic f.
Proof.
  split.
  - intros Hm.
    constructor; intros c g1 g2 Heq.
    exact (snd (injectivity_is_monic (transform[hom_transfer f] c))
               (sets_functor_monic_pointwise (hom_transfer f) Hm c)
               g1 g2 Heq).
  - intros He.
    apply pointwise_monic_is_monic; intro c.
    apply (fst (injectivity_is_monic (transform[hom_transfer f] c))).
    intros g1 g2 Heq.
    exact (@epic A _ _ f He c g1 g2 Heq).
Defined.

(* ** Mac Lane's lemma, second half: epi ⟺ split monic  / ** Mac Lane 引理，后半部分：epi ⟺ 分裂 monic*)

(*
“If f* is epi, there is an h_0 : a → b with f*h_0 = h_0 f = 1 : b → b,
   so f has a left inverse.  The converse is immediate.”  The witness
   h_0 is obtained by evaluating surjectivity of the component at c := b
   on id[b]; it is DATA, [∃] being [sigT] here, which is why the
   biconditional is [Defined]. 

--------
“如果 f* 是 epi，则存在 h_0 : a → b 且 f*h_0 = h_0 f = 1 : b → b，
 所以 f 有一个左逆元。 相反的情况是立即发生的。” 证人
 h_0 是通过评估 c := b 处分量的满射性获得的
 在 id[b] 上； 它是 DATA，[∃] 在这里是 [sigT]，这就是为什么
 双条件是 [Defined]。 
*)

Theorem hom_transfer_epic_iff_section {a b : A} (f : b ~> a) :
  @Epic ([A, Sets]) _ _ (hom_transfer f) ↔ Section f.
Proof.
  split.
  - intros He.
    destruct (epic_implies_surjective
                (transform[hom_transfer f] b)
                (sets_functor_epic_pointwise (hom_transfer f) He b)
                (id[b])) as [s Hs].
    exact {| section := s ; section_comp := Hs |}.
  - intros Hs.
    apply pointwise_epic_is_epic; intro c.
    apply (fst (surjectivity_is_epic (transform[hom_transfer f] c))).
    intro k.
    exists (k ∘ @section A b a f Hs).
    change ((k ∘ @section A b a f Hs) ∘ f ≈ k).
    rewrite <- comp_assoc.
    rewrite (@section_comp A b a f Hs).
    exact (id_right k).
Defined.

(*
The two halves under their own names, for callers that want just one.
   Each is a projection of the biconditional, so no proof text is
   repeated and the identity of the statements is by conversion. 

--------
两半都在自己的名下，供只想要一份的来电者使用。 
每个都是双条件的投影，因此没有证明文本
 重复，并且语句的同一性是通过转换实现的。 
*)

Definition epic_of_hom_transfer_monic {a b : A} (f : b ~> a) :
  @Monic ([A, Sets]) _ _ (hom_transfer f) → Epic f :=
  fst (hom_transfer_monic_iff_epic f).

Definition hom_transfer_monic_of_epic {a b : A} (f : b ~> a) :
  Epic f → @Monic ([A, Sets]) _ _ (hom_transfer f) :=
  snd (hom_transfer_monic_iff_epic f).

Definition section_of_hom_transfer_epic {a b : A} (f : b ~> a) :
  @Epic ([A, Sets]) _ _ (hom_transfer f) → Section f :=
  fst (hom_transfer_epic_iff_section f).

Definition hom_transfer_epic_of_section {a b : A} (f : b ~> a) :
  Section f → @Epic ([A, Sets]) _ _ (hom_transfer f) :=
  snd (hom_transfer_epic_iff_section f).

(*
A by-product, recorded because it is the shape the theorem file needs
   and because it makes the pointwise reading of each side visible: the
   component at c is injective exactly when f cancels on the right into
   c, and surjective exactly when every arrow out of b factors through
   f. 

--------
副产品，记录下来是因为它是定理文件所需的形状
 因为它使每一面的逐点读数可见：
 当 f 在右侧取消时，c 处的分量是单射的
 c，当 b 中的每个箭头都因式分解时，满射完全成立
 f. 
*)

Lemma hom_transfer_component_injective_iff {a b : A} (f : b ~> a)
      (c : A) :
  (∀ g1 g2 : a ~> c, g1 ∘ f ≈ g2 ∘ f → g1 ≈ g2)
    ↔ Monic (transform[hom_transfer f] c).
Proof. exact (injectivity_is_monic (transform[hom_transfer f] c)). Defined.

Lemma hom_transfer_component_surjective_iff {a b : A} (f : b ~> a)
      (c : A) :
  (∀ k : b ~> c, ∃ g : a ~> c, g ∘ f ≈ k)%type
    ↔ Epic (transform[hom_transfer f] c).
Proof. exact (surjectivity_is_epic (transform[hom_transfer f] c)). Defined.

End Transfer.
