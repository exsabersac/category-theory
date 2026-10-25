Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Morphisms.Duality.

Generalizable All Variables.

(** * Cokernel pairs, and epimorphisms as pushout squares / * 余核对，以及作为推挤方的满射 *)

(*
nLab:      https://ncatlab.org/nlab/show/cokernel+pair
              https://ncatlab.org/nlab/show/kernel+pair
   Wikipedia: https://en.wikipedia.org/wiki/Epimorphism

   Mac Lane, CWM 2nd ed., §III.3 p. 66 (`maclane:III.3:def7`) and §III.4
   Exercise 4 p. 72 (`maclane:III.4:ex4`).  Fong and Spivak, *Seven
   Sketches in Compositionality*, §7.2.1 Definition 7.5, printed p. 226
   (`7sketches:7.2.1:def7.5`).

   The COKERNEL PAIR of f : x ~> y is the pushout of f with itself: an
   object together with a PARALLEL PAIR u, v : y ~> P satisfying
   u ∘ f ≈ v ∘ f and universal among such pairs.  It is the exact dual of
   Structure/Regular.v's [kernel_pair f := pullback f f], and the two are
   the standard measure of how far f is from being epic (resp. monic): f
   is an epimorphism exactly when its cokernel pair is TRIVIAL, i.e. when
   its two legs coincide, equivalently when the square

       x ---f---> y
       |          |
      f|          | id
       v          v
       y ---id--> y

   is a pushout.  Fong and Spivak take that square to BE the definition of
   an epimorphism, with no hypotheses on the ambient category; Mac Lane
   phrases the same fact through the cokernel pair.  Both readings are
   delivered below, and proved equivalent to Theory/Morphisms.v's
   right-cancellation [Epic].

   ------------------------------------------------------------------
   ** Disambiguation

   This is NOT Structure/Kernel.v's cokernel.  That is the zero-object
   notion — the coequalizer of f against the zero morphism — and it needs
   a [ZeroObject].  The cokernel pair needs nothing but a pushout, and in
   a category with a zero object the two are genuinely different objects.
   The names are close enough to mislead, so nothing here is stated in
   terms of [IsCokernel] and nothing there is stated in terms of this
   file's [IsCokernelPair].

   ------------------------------------------------------------------
   ** Engineering finding: the tree's two pushout notions are named
      inconsistently, and the issue's suggested spelling was unusable

   The library carries two pullback notions and, until this file, only one
   pushout notion:

     - Structure/Pullback.v [Record Pullback f g] is BUNDLED: it
       carries its apex [Pull] as data, so it cannot say that a GIVEN
       square is a pullback.
     - Theory/Morphisms/Stability.v [Record IsPullback f g P p1 p2] is
       APEX-PINNED: apex and both legs are parameters.  That file's own
       header says in terms why it had to exist.
     - Structure/Pushout.v [IsPushout f g := @Pullback (C^op) y z x f g]
       is BUNDLED — despite the [Is] prefix, which in the pullback half of
       the tree marks the pinned form.

   So the name [IsPushout] was already taken, by the form that CANNOT
   state "this square is a pushout".  Read the consequence precisely, and
   NOT as an expressibility claim: the theorem's STATEMENT was already
   writable with what existed, as [@IsPullback (C^op) y z x f g P i1 i2] —
   which is exactly what [IsPushoutSquare] abbreviates, by [eq_refl] — and
   a file importing only pre-commit modules elaborates it.  What did not
   exist is a NAMED, C-facing apex-pinned pushout predicate with accessors
   and a smart constructor, and the natural name for one was taken.  An
   earlier draft of this header said the statement was "not expressible
   with what existed"; that was false and an audit refuted it by compiling
   the pre-existing spelling.  The predicate is called [IsPushoutSquare]
   here; renaming the existing constant was out of scope.

   The predicate itself costs nothing.  Exactly as [IsPushout] is
   [Pullback] in C^op, [IsPushoutSquare] is [IsPullback] in C^op, and its
   two field readings [is_pushout_square_commutes] and
   [is_pushout_square_ump], its C-facing smart constructor
   [Build_IsPushoutSquare], and BOTH conversions with the bundled
   [IsPushout] are supplied by [:=] with NO tactic: the two record fields
   of [IsPullback] read at C^op ARE the commuting square and the universal
   property of a pushout in C, on the nose.  (The mediator kit
   [pushout_square_med_in1] and its three siblings do use tactics; they are
   re-derived directly from [unique_property], and are NEW content rather
   than Structure/Pushout.v's mediator lemmas read at C^op — the two
   mediators are not even convertible, [pushout_med] routing through the
   [Qed]-opaque [pushout_ump] where [pushout_square_med] routes through the
   transparent [is_pushout_square_ump].  Stability.v has no mediator kit
   for [IsPullback] at all.)  The
   round trip through the bundled form closes at [eq_refl] on the WHOLE
   record, guarded as [ctl_roundtrip] in Test/ProbeCokernelPair.v.

   ------------------------------------------------------------------
   ** Engineering finding: writing INTO the C^op reading

   Reading a [IsPushoutSquare] is free; BUILDING one directly is not, and
   the reason is worth recording.  Under [constructor] the two goals are
   presented at C^op, where the cocone legs precompose on the LEFT, so
   [id_left] and [id_right] exchange roles and — worse — the identity
   written in the STATEMENT elaborates as [@id C y] while the goal's head
   is [@compose (C^op) …], which makes [apply id_left] and
   [exact (id_right _)] both fail with "Unable to unify C with C^op" even
   though the terms are convertible: [apply] fixes the category from the
   [id] argument before it reaches the composite.

   Two things follow, and both are in the code rather than in prose.
   First, [Build_IsPushoutSquare] exists so that no caller ever meets that
   presentation; it takes both hypotheses in C-facing form and every proof
   below is an ordinary C-level argument.  Second, the record-literal
   syntax [{| is_pullback_commutes := …; … |}] does NOT work in its body:
   [IsPushoutSquare] is a transparent [Definition], but the literal is
   elaborated against fresh metavariables rather than against the expected
   type, and unification then reads [i1 ∘ f ≈ i2 ∘ g] as a pullback square
   in C with apex [x] — a silently wrong instantiation that surfaces as a
   confusing "cannot unify" against a goal nobody wrote.  The constructor
   must be applied explicitly, [@Build_IsPullback (C^op) y z x f g P i1 i2
   Hcomm Hump].  The same applies to [IsIsomorphism] at C^op, which is why
   [IsIsomorphism_of_op] spells [@Build_IsIsomorphism] out.

   ------------------------------------------------------------------
   ** Universes, measured in the constraint blocks

   Every principal artifact states its category with hom and proof
   IDENTIFIED and the object universe bounded but NEVER identified with
   them — that is the substantive fact, and it holds throughout.  The
   PARAMETER COUNT is not uniform, and an earlier draft of this header
   claimed as measured that it was three everywhere with the category
   always [Category@{u u0 u0}]; an audit refuted that.  Measured:
   [epic_iff_pushout_square@{u u0 u1}] and [monic_iff_pullback_square@{u
   u0 u1}] are three over [Category@{u u0 u0}], but
   [epic_iff_cokernel_pair_trivial], [epic_iff_cokernel_pair_left_iso] and
   [IsCokernelPair] each carry FOUR, and [IsCokernelPair@{u u0 u1 u2}] and
   [cokernel_pair@{u u0 u1}] state their category as [Category@{u0 u1 u1}]
   rather than [Category@{u u0 u0}], with [IsCokernelPair]'s block reading
   [u0 <= u2, u1 <= u2, u2 <= u].

   That identification is INHERITED, and it is attributed PER DONOR rather
   than guessed: over a [Category@{uo uh up}] declared with the strict
   [Constraint uh < up], each of [Epic] (Theory/Morphisms.v),
   [Pullback] (Structure/Pullback.v), [IsPullback]
   (Theory/Morphisms/Stability.v) and [IsPushout] (Structure/Pushout.v) is
   INDEPENDENTLY rejected, each reporting "universe inconsistency: Cannot
   enforce vp = vh because vh < vp", while the ambient category and its
   hom-sets are perfectly formable at that setting.  So [Epic] alone and
   [IsPullback] alone each suffice to force it and nothing in this file
   adds to it; negatives 5-9 and their control pin this, one per donor.
   The identification is NOT claimed unavoidable — no attempt was made to
   repair the donors.

   ------------------------------------------------------------------
   ** What is proved, and at what strength

   - [IsPushoutSquare] with its C-facing accessor and mediator layer, its
     smart constructor, and both conversions with [IsPushout].  No
     [Program] and no obligation anywhere in the file.

   - [cokernel_pair f : IsPushout f f] under [HasPushouts], mirroring
     [kernel_pair f : Pullback f f] one for one; the one-off apex-pinned
     form [IsCokernelPair f P u v]; and the accessor layer [ckp_obj],
     [ckp_left], [ckp_right], [ckp_commutes], [ckp_ump] with its mediator
     kit, stated for an ARBITRARY [IsPushout f f] so that the chosen and
     one-off forms are both served.  [ckp_ump] is stated on PARALLEL PAIRS
     COEQUALIZING f, which is the shape a consumer wants.

   - [epic_iff_pushout_square] : Epic f ↔ IsPushoutSquare f f y id id.
     This is Seven Sketches Definition 7.5 against the library's [Epic],
     as a biconditional, over an arbitrary category with no hypotheses at
     all — in particular with no [HasPushouts], since the square names its
     own apex.

   - [epic_iff_cokernel_pair_trivial] : for ANY [P : IsPushout f f],
     Epic f ↔ ckp_left P ≈ ckp_right P.  Mac Lane's phrasing.

   - [epic_iff_cokernel_pair_left_iso] : the same at full strength —
     Epic f ↔ IsIsomorphism (ckp_left P) — with the two-sided inverse
     named ([epic_ckp_left_iso] exhibits it as the mediator of the pair
     (id, id)).  The forward direction is the useful one; the converse
     holds too and is proved, so "the cokernel pair is trivial" is a
     characterization and not merely a consequence.

     [epic_iff_chosen_ckp_trivial] and [epic_iff_chosen_ckp_left_iso] are
     the same two statements at the CHOSEN cokernel pair under
     [HasPushouts], supplied by [:=] so a consumer need not spell the
     pushout argument.

   - The [Monic] dual, DERIVED VIA C^op AND NOT REPROVED
     ([monic_iff_pullback_square], [monic_iff_kernel_pair_trivial],
     [monic_iff_kernel_pair_fst_iso]).  The derivation is literal: the
     three statements are the three [Epic] ones instantiated at C^op and
     re-typed through Duality.v's [Monic_of_op_Epic]/[op_Epic_of_Monic],
     with no tactic reasoning of their own beyond a two-line [split].
     FOUR conversions carry the transfer, and all four are MEASURED rather
     than assumed: [op_collapse_pushout_square],
     [op_collapse_cokernel_pair], [op_collapse_ckp_left] and
     [op_collapse_ckp_right] close by [eq_refl] — the first because
     (C^op)^op is C definitionally in this library
     (Construction/Opposite.v), the others because a pushout of f with
     itself at C^op IS a pullback of f with itself at C and the
     cokernel-pair legs there ARE the pullback projections here.

     ONE step of the transfer is NOT definitional, and the file says so
     rather than rounding it off: [IsIsomorphism] at C^op and at C carry
     the same inverse but their two law fields are SWAPPED, so
     [IsIsomorphism_of_op]/[op_IsIsomorphism_of] are a field permutation
     and the [eq_refl] identification is REFUTED (negative 1).  That is
     why [monic_iff_kernel_pair_fst_iso] is stated in C rather than left
     reading in C^op.

   NINE negatives in all are pinned in Test/ProbeCokernelPair.v — three
   CONVERSION and six FORMABILITY, kept lexically apart — against twelve
   positive controls.  The sharpest is negative 4: it is the structural
   claim above, made machine-checkable by showing that
   [IsPushout f f y id id] is an "Illegal application" — a TYPING error,
   not a universe inconsistency — so the bundled form provably cannot
   state the epimorphism square.

   The mono half of Seven Sketches Definition 7.5 is issue #672's
   territory; what is delivered here is the dual of THIS issue's epi
   theorem, obtained by duality, not that issue's development.

   ------------------------------------------------------------------
   ** Correction to a claim about the tree

   Issue #323 states that `rg 'cokernel.?pair|CokernelPair'` returns 0
   hits.  THAT IS FALSE, and it was false when the issue was written.
   Three genuine cokernel-pair constructions exist, each built to prove
   "epi ⟹ surjective" in its own category:

     - Instance/Sets.v, [Section CokernelPair]: [CKSetoid],
       [ck_left], [ck_right], [ck_agree];
     - Instance/Top.v, [Section CokernelPair]: [CokernelPair],
       [CP_leftLeg], [CP_rightLeg], [CP_legs_agree];
     - Instance/Sets/Pointed.v, the pointed cokernel pair.

   What is genuinely absent — the sharper gap, and the one this file
   closes — is that NONE of the three is ever related to a pushout.  Each
   supplies an apex, two legs and the equation [u ∘ f ≈ v ∘ f], and stops
   there: no universal property of any of them is proved, the string
   "pushout" does not occur in Instance/Top.v or Instance/Sets/Pointed.v
   at all, and in Instance/Sets.v it occurs only in an unrelated
   header line.  So three concrete cokernel pairs existed and none of them
   knew it was a pushout.  Instance/Sets/CokernelPair.v repairs that for
   the [Sets] one.

   ------------------------------------------------------------------
   ** NOT DELIVERED (scoped)

   - No functoriality HERE: the functor on the arrow category and its
     adjunction with the equalizer functor are Adjunction/CokernelPair.v
     (#364), which CONSUMES this file's [cokernel_pair] and ckp_*
     accessors rather than redefining them -- a division of labour.

   - No relation to [RegularEpi] or to [Structure/Regular.v]'s
     [regular_coeq]: it is NOT proved here that the coequalizer of a
     cokernel pair is anything in particular, nor that f is a regular epi
     when it coequalizes its own kernel pair.

   - No [HasPushouts] instance is added; the five that exist (Sets,
     FinSet, Proset, Grp, Top) are untouched.  The last two arrived after
     this file (Instance/Grp/Pushout.v, Instance/Top/Pushout.v); the count
     read three when this note was written.

   - The [Top] and [Sets/Pointed] cokernel pairs are NOT identified with
     this API.  Only the [Sets] one is, in Instance/Sets/CokernelPair.v.
     Nothing is claimed about whether the other two are pushouts; the
     universal property is simply not proved for them here.

   - No uniqueness-up-to-unique-iso statement for cokernel pairs in
     general.  [epic_iff_cokernel_pair_left_iso] gives an isomorphism only
     in the epic case, where the comparison object is the codomain itself;
     the general two-cokernel-pairs comparison would be
     [pullback_transport] read at C^op and is not performed.

--------
nLab：https://ncatlab.org/nlab/show/cokernel+pair
 保护141X
 维基百科：https://en.wikipedia.org/wiki/Epimorphism

Mac Lane，CWM 第二版，第 III.3 页。 66 (`maclane:III.3:def7`) 和§III.4
 练习 4 p. 72（`maclane:III.4:ex4`）。 Fong 和 Spivak，*七
 组合性草图*，§7.2.1 定义 7.5，印刷页。 226
 (`7sketches:7.2.1:def7.5`)。

f : x ~> y 的 COKERNEL PAIR 是 f 与其自身的推出： an
 对象与并行对 u, v : y ~> P 满足
 u ∘ f ≈ v ∘ f 并且在这些对中通用。 它是精确的对偶
 Structure/Regular.v的[kernel_pair f := pullback f f]，这两个是
 衡量 f 距离史诗（resp. monic）有多远的标准度量：f
 当它的 cokernel 对是 TRIVIAL 时，即当
 它的两条腿重合，相当于当正方形

x ---f---> y
 | |
 f| | 编号
 伏
 y ---id--> y

是推出。 Fong 和 Spivak 将这个正方形定义为
 一种外态，对环境范畴没有假设； 麦克莱恩
 通过 cokernel 对表达相同的事实。 两个读数都是
 下面提供，并证明等同于 Theory/Morphisms.v 的
 右取消 [Epic]。

------------------------------------------------------------------
 ** 消歧义

这不是 Structure/Kernel.v 的核心。 这就是零对象
 概念——f 对抗零态射的余均衡器——它需要
 [ZeroObject]。 cokernel 对只需要推出，并且在
 具有零对象的范畴，这两个对象是真正不同的对象。 
这些名称非常接近，容易产生误导，因此这里没有说明任何内容
 [IsCokernel] 条款中没有任何说明
 文件的 [IsCokernelPair].

------------------------------------------------------------------
 ** 工程发现：树的两个推出概念被命名
 不一致，并且该问题的建议拼写不可用

该库带有两个回调概念，直到该文件为止，只有一个
 推出概念：

- Structure/Pullback.v [Record Pullback f g] 已捆绑：它
 携带其顶点 [Pull] 作为数据，因此不能说 GIVEN
 方形是回调。 
- 理论/态射/稳定性.v [Record IsPullback f g P p1 p2] 是
 APEX-PINNED：顶点和两条腿都是参数。 该文件是自己的
 标题用术语说明了它必须存在的原因。 
- 结构/推出.v [IsPushout f g := @Pullback (C^op) y z x f g]
 是捆绑的——尽管有 [Is] 前缀，它在回调的一半中
 树标记了固定的形式。

因此 [IsPushout] 这个名称已经被采用，形式为 CANNOT
 声明“这个方格是推出方”。 准确地读出结果，并且
 不作为可表达性主张：定理的声明已经
 可使用现有的内容进行写入，如 [@IsPullback (C^op) y z x f g P i1 i2] —
 这正是 [IsPushoutSquare] 的缩写，由 [eq_refl] 表示 — 并且
 仅导入预提交模块的文件对其进行了详细说明。 什么没有
 存在是一个带有访问器的命名的、面向 C 的顶点固定推出谓词
 和一个智能构造函数，并采用了其中一个的自然名称。 安
 该标题的早期草案表示该声明“无法表达”
 与存在的东西”； 这是错误的，审计通过编译反驳了它
 预先存在的拼写。 该谓词称为 [IsPushoutSquare]
 在这里； 重命名现有常量超出了范围。

谓词本身不需要任何成本。 正如 [IsPushout] 一样
 C^op 中的 [Pullback]，[IsPushoutSquare] 是 C^op 中的 [IsPullback]，其
 两个现场读数 [is_pushout_square_commutes] 和
 [is_pushout_square_ump]，其面向 C 的智能构造器
 [Build_IsPushoutSquare] 以及捆绑的两种转换
 [IsPushout] 由 [:=] 提供，没有策略：两个记录字段
 在 C^op 上读到的 [IsPullback] 是通勤广场和通用广场
 C 中推出的特性，位于鼻子上。 （中介套件
 [pushout_square_med_in1] 及其三个兄弟确实使用了策略； 他们是
 直接从 [unique_property] 重新派生，并且是新内容
 比在 C^op 中读到的 Structure/Pushout.v 的中介引理 — 两个
 中介者甚至不可转换，[pushout_med]通过
 [Qed]-不透明 [pushout_ump]，其中 [pushout_square_med] 通过
 透明 [is_pushout_square_ump]。 Stability.v 没有中介工具包
 [IsPullback] 完全适用。）
 通过捆绑形式的往返行程在 [eq_refl] 上结束
 记录，在 Test/ProbeCokernelPair.v 中保护为 [ctl_roundtrip]。

------------------------------------------------------------------
 ** 工程发现：写入 C^op 阅读

读取 [IsPushoutSquare] 是免费的； 直接构建一个不是，并且
 原因值得记录。 [constructor] 下的两个目标是
 在 C^op 上提出，其中可锥腿在左侧预合成，所以
 [id_left] 和 [id_right] 交换角色，更糟糕的是交换恒等
 写在STATENT中详细说明为[@id C y]，而目标的头部
 是 [@compose (C^op) …]，它使得 [apply id_left] 和
 [exact (id_right _)] 都失败，甚至出现“Unable to unify C with C^op”
 尽管这些术语是可转换的：[apply] 修复了
 [id] 参数在到达复合之前。

接下来有两件事，并且都是在代码中而不是在散文中。 
首先，[Build_IsPushoutSquare] 的存在是为了确保调用者不会遇到这种情况
 演示； 它需要面向 C 的形式的假设和每个证明
 下面是一个普通的 C 级参数。 二、记录字面意思
 语法 [{| is_pullback_commutes := …; … |}] 在其主体中不起作用：
 [IsPushoutSquare]是透明的[Definition]，但字面意思是
 针对新的元变量而不是针对预期进行阐述
 类型，然后统一将 [i1 ∘ f ≈ i2 ∘ g] 读取为回拉方块
 在 C 中，带有 apex [x] — 一个默默地错误的实例，表面上是
 混淆“无法统一”与没有人写下的目标。 构造函数
 必须显式应用，[@Build_IsPullback (C^op) y z x f g P i1 i2
 Hcomm 驼峰]。 这同样适用于 C^op 处的 [IsIsomorphism]，这就是为什么
 [IsIsomorphism_of_op] 拼出 [@Build_IsIsomorphism]。

------------------------------------------------------------------
 ** 宇宙，在约束块中测量

每个主要文物都用 hom 和证据说明其范畴
 已识别并且对象宇宙有界但从未识别
 他们——这是实质性事实，自始至终都是如此。 的
 PARAMETER COUNT 不统一，此标头的早期草案
 声称经测量，该范畴中到处都是三个
 始终 [Category@{u u0 u0}]； 一项审计驳斥了这一点。 测量：
 [epic_iff_pushout_square@{u u0 u1}] 和 [monic_iff_pullback_square@{u
 u0 u1}] 比 [Category@{u u0 u0}] 多 3 个，但是
 [epic_iff_cokernel_pair_trivial], [epic_iff_cokernel_pair_left_iso] and
 [IsCokernelPair] 每个携带 4 个，[IsCokernelPair@{u u0 u1 u2}] 和
 [cokernel_pair@{u u0 u1}] 声明其范畴为 [Category@{u0 u1 u1}]
 而不是 [Category@{u u0 u0}]，使用 [IsCokernelPair] 的块读取
 [u0 <= u2, u1 <= u2, u2 <= u]。

该恒等是继承的，并且归因于每个捐赠者
 比猜测的要多：通过严格声明的 [Category@{uo uh up}]
 [Constraint uh < up]、每个 [Epic]（理论/态射.v）、
 [Pullback]（结构/拉回.v）、[IsPullback]
 (Theory/Morphisms/Stability.v) 和 [IsPushout] (Structure/Pushout.v) 是
 独立拒绝，每个报告“宇宙不一致：不能
 强制 vp = vh 因为 vh < vp"，而环境范畴及其
 hom-sets 在该设置下可以完美成型。 所以 [Epic] 单独和
 仅 [IsPullback] 就足以强制执行此操作，此文件中没有任何内容
 添加到它； 底片 5-9 及其对照引脚，每个供体一个。 
恒等识别并未声称是不可避免的——没有尝试
 修复捐赠者。

------------------------------------------------------------------
 ** 证明了什么，强度如何

- [IsPushoutSquare] 及其 C 面访问器和中介层，其
 智能构造函数，以及 [IsPushout] 的两种转换。 否
 [Program] 并且文件中任何地方都没有义务。

- [HasPushouts]下的[cokernel_pair f : IsPushout f f]，镜像
 [kernel_pair f : Pullback f f] 一换一； 一次性顶点固定
 形式 [IsCokernelPair f P u v]； 和访问层 [ckp_obj]，
 [ckp_left], [ckp_right], [ckp_commutes], [ckp_ump] with its mediator
 kit, stated for an ARBITRARY [IsPushout f f] so that the chosen and
 两种形式均送达一次性表格。 [ckp_ump] 在平行对上注明
 COEQUALIZING f, which is the shape a consumer wants.

- [epic_iff_pushout_square]：史诗 f ↔ IsPushoutSquare f f y id id。 
这是针对库的 [Epic] 的七个草图定义 7.5，
 as a biconditional, over an arbitrary category with no hypotheses at
 全部 — 特别是没有 [HasPushouts]，因为方块命名为
 自己的巅峰。

- [epic_iff_cokernel_pair_trivial]：适用于任何 [P : IsPushout f f]，
 Epic f ↔ ckp_left P ≈ ckp_right P。Mac Lane 的措辞。

- [epic_iff_cokernel_pair_left_iso] ：全力时相同 —
 Epic f ↔ IsIsomorphism (ckp_left P) — 具有两侧逆
 命名（[epic_ckp_left_iso] 将其展示为该对的中介
 （恒等证，恒等证））。 前进的方向才是有用的；前进的方向才是有用的。 相反
 也成立并被证明，所以“cokernel 对是平凡的”是
 表征而不仅仅是结果。

[epic_iff_chosen_ckp_trivial] 和 [epic_iff_chosen_ckp_left_iso] 是
 在 CHOSEN cokernel 对下的相同两个语句
 [HasPushouts]，由 [:=] 提供，因此消费者无需拼写
 推出论证。

- [Monic] 双，通过 C^op 衍生且未经重新认证
 （[monic_iff_pullback_square]、[monic_iff_kernel_pair_trivial]、
 [monic_iff_kernel_pair_fst_iso]）。 推导是字面意思：
 三个语句是在 C^op 实例化的三个 [Epic] 语句，
 通过 Duality.v 的 [Monic_of_op_Epic]/[op_Epic_of_Monic] 重新输入，
 除了两线 [split] 之外，没有自己的策略推理。 
四个转换进行传输，并且所有四个转换都经过测量
 比假设的：[op_collapse_pushout_square]，
 [op_collapse_cokernel_pair]、[op_collapse_ckp_left] 和
 [op_collapse_ckp_right] 接近 [eq_refl] — 第一个，因为
 (C^op)^op 在此库中定义为 C
 (Construction/Opposite.v)，其他的因为 f 的推出
 其自身在 C^op 处是 f 自身在 C 处的回调，并且
 那里的焦核对腿是这里的回调投影。

传输的一步不是定义性的，文件是这么说的
 而不是四舍五入：[IsIsomorphism] 在 C^op 和 C 进位
 相同的逆，但它们的两个定律场交换了，所以
 [IsIsomorphism_of_op]/[op_IsIsomorphism_of] 是字段排列
 [eq_refl] 标识被拒绝（负 1）。 那就是
 为什么 [monic_iff_kernel_pair_fst_iso] 用 C 语言而不是左边来表示
 在 C^op 中阅读。

Test/ProbeCokernelPair.v 中总共固定了 9 个负数 - 三个
 CONVERSION 和 6 个 FORMABILITY，在词汇上保持独立——与 12 个相对
 阳性对照。 最尖锐的是负面4：它是结构性的
 上述声明，通过证明可以通过机器检查
 [IsPushout f f y id id] 是一个“非法应用程序”——打字错误，
 不是宇宙不一致——所以捆绑形式可以证明不能
 说出外同态平方。

七个草图定义 7.5 的单声道一半是第 #672 期
 领土； 这里提供的是本期 Epi 的对偶
 定理，通过对偶性获得，而不是该问题的发展。

------------------------------------------------------------------
 ** 更正有关该树的说法

问题 #323 指出 `rg 'cokernel.?pair|CokernelPair'` 返回 0
 命中。 这是错误的，在撰写该问题时也是错误的。 
存在三个真正的 cokernel 对结构，每个结构都是为了证明
 "epi ⟹ 满射" 在其自己的范畴中：

- 实例/Sets.v，[Section CokernelPair]：[CKSetoid]，
 [ck_left]、[ck_right]、[ck_agree]；
 - 实例/Top.v，[Section CokernelPair]：[CokernelPair]，
 [CP_leftLeg]、[CP_rightLeg]、[CP_legs_agree]；
 - Instance/Sets/Pointed.v，指向的 cokernel 对。

真正缺失的东西——更尖锐的差距，以及这份文件中的差距
 关闭——这三者中没有一个与推出有关。 每个
 提供一个顶点、两条腿和方程 [u ∘ f ≈ v ∘ f]，并停止
 那里：没有证明它们中任何一个的通用属性，字符串
 “pushout”不会出现在 Instance/Top.v 或 Instance/Sets/Pointed.v 中
 根本没有，并且在 Instance/Sets.v 中它仅发生在不相关的
 标题行。 所以存在三个具体的焦核对，但没有一个
 知道这是一次推出。 Instance/Sets/CokernelPair.v 修复了该问题
 [Sets] 之一。

------------------------------------------------------------------
 ** 未交付（范围内）

- 这里没有函子：箭头范畴上的函子及其
 带有均衡器函子的附加是 Adjunction/CokernelPair.v
 (#364)，它消耗此文件的 [cokernel_pair] 和 ckp_*
 访问器而不是重新定义它们——这是一种劳动分工。

- 与 [RegularEpi] 或 [Structure/Regular.v] 无关
 [regular_coeq]：这里没有证明 a 的协均衡器
 cokernel 对没有什么特别的，f 也不是常规的 Epi
 当它与自己的内核对相等时。

- 未添加[HasPushouts]实例； 存在的五个（集合，
 FinSet、Proset、Grp、Top）未受影响。 最后两个到达后
 该文件（Instance/Grp/Pushout.v、Instance/Top/Pushout.v）； 计数
 写这篇笔记时读了三遍。

- [Top] 和 [Sets/Pointed] cokernel 对未标识为
 这个API。 只有 [Sets] 位于 Instance/Sets/CokernelPair.v 中。 
没有任何关于另外两个是否是推出的说法； 的
 这里根本没有为他们证明普遍财产。

- 中的 cokernel 对没有唯一性至唯一 iso 声明
 一般。 [epic_iff_cokernel_pair_left_iso] 仅给出同构
 在史诗情况下，比较对象是共域本身；
 一般的两核对比较是
 [pullback_transport] 在 C^op 处读取但未执行。
*)

(** ** The apex-pinned pushout square / ** 顶点固定的推出方格 *)

Section PushoutSquare.

Context {C : Category}.

(*
The square

        x ---g---> z
        |          |
       f|          | i2
        v          v
        y ---i1--> P

   commutes and enjoys the universal property of a pushout.  This is
   [IsPullback] read in C^op, where composition is reversed: the field
   [is_pullback_commutes] there reads [i1 ∘ f ≈ i2 ∘ g] here, and
   [is_pullback_ump] there reads as the mediation of cocones here.

--------
该方形图

        x ---g---> z
        |          |
       f|          | i2
        v          v
        y ---i1--> P

   是交换的，并且具有推挤的泛性质。这是
   在 C^op 中读取的 [IsPullback]，其中复合是反向的：那里字段
   [is_pullback_commutes] 在这里读取为 [i1 ∘ f ≈ i2 ∘ g]，并且
   那里的 [is_pullback_ump] 在这里可读作余锥的中介。
*)
Definition IsPushoutSquare {x y z : C} (f : x ~> y) (g : x ~> z)
           (P : C) (i1 : y ~> P) (i2 : z ~> P) : Type :=
  @IsPullback (C^op) y z x f g P i1 i2.

Section Accessors.

Context {x y z : C} {f : x ~> y} {g : x ~> z}.
Context {P : C} {i1 : y ~> P} {i2 : z ~> P}.

(*
The C-facing smart constructor.  Without it a caller must build the
   square with goals displayed in C^op, where the legs precompose on the
   left and [id_left]/[id_right] swap roles — an elaboration nuisance
   recorded in the header.  Like the readers below it is definitional:
   both hypotheses fit the C^op record fields by conversion alone.

--------
面向 C 的智能构造函数。没有它，调用者必须构建在 C^op 中显示目标的平方，其中边在左侧预组合，而 [id_left]/[id_right] 交换角色——这是在头文件中记录的扩展上的麻烦。像下面的读取器一样，它是定义性的：两个假设仅通过转换就适合 C^op 记录字段。
*)
Definition Build_IsPushoutSquare
           (Hcomm : i1 ∘ f ≈ i2 ∘ g)
           (Hump : ∀ (Q : C) (q1 : y ~> Q) (q2 : z ~> Q),
               q1 ∘ f ≈ q2 ∘ g →
               ∃! u : P ~> Q, u ∘ i1 ≈ q1 ∧ u ∘ i2 ≈ q2)
  : IsPushoutSquare f g P i1 i2 :=
  @Build_IsPullback (C^op) y z x f g P i1 i2 Hcomm Hump.

(* Both field readings are definitional: supplied by [:=], no tactic. / 两个现场读数都是定义性的：由 [:=] 提供，无战术。 *)

Definition is_pushout_square_commutes (H : IsPushoutSquare f g P i1 i2) :
  i1 ∘ f ≈ i2 ∘ g := is_pullback_commutes H.

Definition is_pushout_square_ump (H : IsPushoutSquare f g P i1 i2)
           (Q : C) (q1 : y ~> Q) (q2 : z ~> Q) (Hc : q1 ∘ f ≈ q2 ∘ g) :
  ∃! u : P ~> Q, u ∘ i1 ≈ q1 ∧ u ∘ i2 ≈ q2 :=
  is_pullback_ump H Q q1 q2 Hc.

(** *** The mediator kit / *** 调解员工具包 *)

Definition pushout_square_med (H : IsPushoutSquare f g P i1 i2)
           {Q : C} {q1 : y ~> Q} {q2 : z ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ g)
  : P ~> Q := unique_obj (is_pushout_square_ump H Q q1 q2 Hc).

Lemma pushout_square_med_in1 (H : IsPushoutSquare f g P i1 i2)
      {Q : C} {q1 : y ~> Q} {q2 : z ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ g) :
  pushout_square_med H Hc ∘ i1 ≈ q1.
Proof.
  exact (fst (unique_property (is_pushout_square_ump H Q q1 q2 Hc))).
Qed.

Lemma pushout_square_med_in2 (H : IsPushoutSquare f g P i1 i2)
      {Q : C} {q1 : y ~> Q} {q2 : z ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ g) :
  pushout_square_med H Hc ∘ i2 ≈ q2.
Proof.
  exact (snd (unique_property (is_pushout_square_ump H Q q1 q2 Hc))).
Qed.

Lemma pushout_square_med_unique (H : IsPushoutSquare f g P i1 i2)
      {Q : C} {q1 : y ~> Q} {q2 : z ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ g)
      (v : P ~> Q) :
  v ∘ i1 ≈ q1 -> v ∘ i2 ≈ q2 -> pushout_square_med H Hc ≈ v.
Proof.
  intros H1 H2.
  apply (uniqueness (is_pushout_square_ump H Q q1 q2 Hc)); split; assumption.
Qed.

(* Two mediators agreeing on both legs are equal. / 两个调解员在两个方面达成一致是相等的。 *)
Lemma pushout_square_med_eq (H : IsPushoutSquare f g P i1 i2)
      {Q : C} {q1 : y ~> Q} {q2 : z ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ g)
      (u v : P ~> Q) :
  u ∘ i1 ≈ q1 -> u ∘ i2 ≈ q2 -> v ∘ i1 ≈ q1 -> v ∘ i2 ≈ q2 -> u ≈ v.
Proof.
  intros Hu1 Hu2 Hv1 Hv2.
  transitivity (pushout_square_med H Hc).
  - symmetry; apply pushout_square_med_unique; assumption.
  - apply pushout_square_med_unique; assumption.
Qed.

End Accessors.

(**
*** Conversions with the bundled [IsPushout]

    Both are field repackagings, exactly as Stability.v's
    [pullback_is_pullback]/[is_pullback_pullback] are; indeed each is that
    conversion read at C^op, and so is supplied with no tactic.

--------
*** 与捆绑的 [IsPushout] 的转换

    两者都是现场重新包装，完全像 Stability.v 的 [pullback_is_pullback]/[is_pullback_pullback] 一样；实际上每一个都是在 C^op 读取的该转换，因此不附带任何策略。
*)

Definition pushout_is_pushout_square {x y z : C}
           (f : x ~> y) (g : x ~> z) (P : IsPushout f g) :
  IsPushoutSquare f g (pushout_apex P) (pushout_in1 P) (pushout_in2 P) :=
  @pullback_is_pullback (C^op) y z x f g P.

Definition is_pushout_square_pushout {x y z : C}
           {f : x ~> y} {g : x ~> z}
           {P : C} {i1 : y ~> P} {i2 : z ~> P}
           (H : IsPushoutSquare f g P i1 i2) : IsPushout f g :=
  @is_pullback_pullback (C^op) y z x f g P i1 i2 H.

End PushoutSquare.

Arguments IsPushoutSquare {C x y z} f g P i1 i2.

(** ** The cokernel pair / ** 余核对 *)

(*
The cokernel pair of f : x ~> y is the pushout of f with itself: a
   parallel pair out of y, universal among parallel pairs coequalizing f.

   This is the exact dual of Structure/Regular.v's

       Definition kernel_pair `{HasPullbacks C} (f : x ~> y)
         : Pullback f f := pullback f f

   and is spelled to mirror it one for one.

--------
f : x ~> y 的余核对是 f 自身的推出：一个从 y 出发的平行对，在所有对 f 进行共等化的平行对中是通用的。

这是 Structure/Regular.v 中

    Definition kernel_pair `{HasPullbacks C} (f : x ~> y)
      : Pullback f f := pullback f f

的完全对偶，并且拼写上与之一一对应。
*)
Definition cokernel_pair {C : Category} `{H : @HasPushouts C} {x y : C}
  (f : x ~> y) : IsPushout f f := pushout f f.

(*
The one-off apex-pinned form: [u] and [v] ARE a cokernel pair of f.
   Unlike [cokernel_pair] this needs no [HasPushouts], the square naming
   its own apex and legs.

--------
一次性顶点固定形式：[u] 和 [v] 是 f 的一个协核对。
   与 [cokernel_pair] 不同，这不需要 [HasPushouts]，正方形命名其自身的顶点和边。
*)
Definition IsCokernelPair {C : Category} {x y : C} (f : x ~> y)
           (P : C) (u v : y ~> P) : Type := IsPushoutSquare f f P u v.

Section CokernelPairAccessors.

Context {C : Category}.
Context {x y : C}.
Context {f : x ~> y}.

(*
Stated for an ARBITRARY pushout of f with itself, so that the chosen
   form [cokernel_pair f] and any one-off witness are both served.

--------
针对 f 与自身的任意推挤给出了说明，以便所选择的形式 [cokernel_pair f] 和任何一次性见证都能得到满足。
*)
Context (P : IsPushout f f).

Definition ckp_obj : C := pushout_apex P.

(*
The parallel pair.  Both legs run y ~> ckp_obj: this is what makes the
   cokernel pair a PARALLEL PAIR rather than a general cocone.

--------
平行对。 两条腿都运行 y ~> ckp_obj：这就是使余核对成为平行对而不是一般余锥的原因。
*)
Definition ckp_left : y ~> ckp_obj := pushout_in1 P.
Definition ckp_right : y ~> ckp_obj := pushout_in2 P.

(* The defining equation. / 定义方程。 *)
Lemma ckp_commutes : ckp_left ∘ f ≈ ckp_right ∘ f.
Proof. exact (pushout_commutes P). Qed.

(* The universal property, stated on PARALLEL PAIRS COEQUALIZING f. / 在平行对等化 f 上陈述的普遍性质。 *)
Lemma ckp_ump (Q : C) (q1 q2 : y ~> Q) (Hc : q1 ∘ f ≈ q2 ∘ f) :
  ∃! u : ckp_obj ~> Q, u ∘ ckp_left ≈ q1 ∧ u ∘ ckp_right ≈ q2.
Proof. exact (pushout_ump P Q q1 q2 Hc). Qed.

Definition ckp_med {Q : C} {q1 q2 : y ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ f)
  : ckp_obj ~> Q := pushout_med P Hc.

Lemma ckp_med_left {Q : C} {q1 q2 : y ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ f) :
  ckp_med Hc ∘ ckp_left ≈ q1.
Proof. exact (pushout_med_in1 P Hc). Qed.

Lemma ckp_med_right {Q : C} {q1 q2 : y ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ f) :
  ckp_med Hc ∘ ckp_right ≈ q2.
Proof. exact (pushout_med_in2 P Hc). Qed.

Lemma ckp_med_unique {Q : C} {q1 q2 : y ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ f)
      (v : ckp_obj ~> Q) :
  v ∘ ckp_left ≈ q1 -> v ∘ ckp_right ≈ q2 -> ckp_med Hc ≈ v.
Proof. exact (pushout_med_unique P Hc v). Qed.

Lemma ckp_med_eq {Q : C} {q1 q2 : y ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ f)
      (u v : ckp_obj ~> Q) :
  u ∘ ckp_left ≈ q1 -> u ∘ ckp_right ≈ q2 ->
  v ∘ ckp_left ≈ q1 -> v ∘ ckp_right ≈ q2 -> u ≈ v.
Proof. exact (pushout_med_eq P Hc u v). Qed.

(* The apex-pinned reading of the chosen/one-off pushout. / 所选/一次性推挤的顶点固定读数。 *)
Definition ckp_IsCokernelPair : IsCokernelPair f ckp_obj ckp_left ckp_right :=
  pushout_is_pushout_square f f P.

End CokernelPairAccessors.

Arguments ckp_obj {C x y f} P.
Arguments ckp_left {C x y f} P.
Arguments ckp_right {C x y f} P.

(** ** Epimorphisms are exactly the identity pushout squares / ** 上同态恰好是恒等推挤图 *)

Section EpiCharacterization.

Context {C : Category}.
Context {x y : C}.
Context (f : x ~> y).

(*
Seven Sketches Definition 7.5, forward: if f is right-cancellable then
   the square on f with two identity legs is a pushout.  The mediator of a
   cocone (q1, q2) is q1 itself — epicness is exactly what says q2 is the
   same morphism.

--------
七个草图 定义 7.5，前向：如果 f 是右可消的，那么带有两个恒等箭头的 f 正方形是一个推出图。余锥 (q1, q2) 的中介者是 q1 本身——满射性正是说明 q2 与 q1 是相同的态射。
*)
Definition epic_pushout_square (E : Epic f) : IsPushoutSquare f f y id id.
Proof.
  destruct E as [cancel].
  unshelve eapply Build_IsPushoutSquare.
  - (* the square commutes, trivially / 这个方格是交换的，显而易见 *)
    reflexivity.
  - intros Q q1 q2 Hc.
    assert (Hq : q1 ≈ q2) by (apply cancel; exact Hc).
    unshelve refine {| unique_obj := q1 |}.
    + split.
      * apply id_right.
      * rewrite id_right; exact Hq.
    + intros v [Hv1 _].
      rewrite <- Hv1, id_right; reflexivity.
Defined.

(*
Seven Sketches Definition 7.5, backward: if that square is a pushout
   then f is right-cancellable.  A pair coequalizing f is mediated by a
   SINGLE morphism which, precomposed with the identity twice over, is
   both members of the pair.

--------
七个草图 定义 7.5，逆向：如果那个方块是推出图，那么 f 是右可消的。一对对 f 进行等化的 morphism 由一个单一的态射介导，该态射在前置与两次恒等态射组合后，就是该对的两个成员。
*)
Definition pushout_square_epic (H : IsPushoutSquare f f y id id) : Epic f.
Proof.
  constructor.
  intros z g1 g2 Hg.
  pose proof (is_pushout_square_ump H z g1 g2 Hg) as U.
  destruct (unique_property U) as [U1 U2].
  rewrite <- U1, <- U2; reflexivity.
Defined.

Theorem epic_iff_pushout_square : Epic f ↔ IsPushoutSquare f f y id id.
Proof. split; [ exact epic_pushout_square | exact pushout_square_epic ]. Qed.

(** *** Mac Lane's phrasing: the cokernel pair is trivial / *** Mac Lane的表述：余核对是平凡的 *)

Context (P : IsPushout f f).

(* Forward: right cancellation applied to [ckp_commutes]. / 转发：对 [ckp_commutes] 应用了右取消。 *)
Lemma epic_ckp_trivial (E : Epic f) : ckp_left P ≈ ckp_right P.
Proof.
  destruct E as [cancel].
  apply cancel.
  exact (ckp_commutes P).
Qed.

(*
Backward: a pair coequalizing f is mediated, and the two legs being
   equal forces the two members of the pair to agree.

--------
反向：一对共等化 f 是中介的，并且两条腿相等迫使这对成员达成一致。
*)
Lemma ckp_trivial_epic (Ht : ckp_left P ≈ ckp_right P) : Epic f.
Proof.
  constructor.
  intros z g1 g2 Hg.
  transitivity (ckp_med P Hg ∘ ckp_left P).
  - symmetry; exact (ckp_med_left P Hg).
  - rewrite Ht.
    exact (ckp_med_right P Hg).
Qed.

Theorem epic_iff_cokernel_pair_trivial :
  Epic f ↔ ckp_left P ≈ ckp_right P.
Proof. split; [ exact epic_ckp_trivial | exact ckp_trivial_epic ]. Qed.

(** *** The same at full strength: the left leg is an isomorphism / *** 在全强度下相同：左腿是同构 *)

(*
When f is epic, the mediator of the pair (id, id) is a two-sided
   inverse of either leg, so the cokernel-pair apex collapses onto the
   codomain.  Naming the inverse is what makes this stronger than a bare
   [≅].

--------
当 f 是一个上射时，成对 (id, id) 的中介是任一边的双向逆元，因此余核对顶点会收缩到陪域上。命名逆元使得这比单纯的 [≅] 更强。
*)
Lemma epic_ckp_left_iso (E : Epic f) : IsIsomorphism (ckp_left P).
Proof.
  assert (Hid : id[y] ∘ f ≈ id[y] ∘ f) by reflexivity.
  unshelve refine {| two_sided_inverse := ckp_med P Hid |}.
  - (* ckp_left ∘ med ≈ id, by agreeing with id on both legs / ckp_left ∘ med ≈ id，通过在两条支路上与 id 一致 *)
    apply (ckp_med_eq P (ckp_commutes P)).
    + rewrite <- comp_assoc, (ckp_med_left P Hid); apply id_right.
    + rewrite <- comp_assoc, (ckp_med_right P Hid), id_right.
      exact (epic_ckp_trivial E).
    + apply id_left.
    + apply id_left.
  - (* med ∘ ckp_left ≈ id / med ∘ ckp_left ≈ id *)
    exact (ckp_med_left P Hid).
Qed.

(*
Conversely, an invertible left leg forces the two legs to agree: the
   self-cocone (ckp_left, ckp_left) is mediated by a morphism that the
   invertibility pins to the identity.

--------
相反，一个可逆的左腿迫使两条腿达成一致：自共圆锥 (ckp_left, ckp_left) 是通过一个被可逆性固定为恒等的态射来介导的。
*)
Lemma ckp_left_iso_epic (I : IsIsomorphism (ckp_left P)) : Epic f.
Proof.
  destruct I as [k Hk1 Hk2].
  apply ckp_trivial_epic.
  assert (Hc : ckp_left P ∘ f ≈ ckp_left P ∘ f) by reflexivity.
  (*
The self-mediator of the cocone (ckp_left, ckp_left) is forced to be
     the identity, because it is the identity after the invertible leg.

--------
锥体(cocone)的自我中介者(ckp_left, ckp_left)被迫成为恒等映射，因为在可逆的腿之后它是恒等映射。
*)
  assert (Hw : ckp_med P Hc ≈ id).
  { transitivity (ckp_med P Hc ∘ (ckp_left P ∘ k)).
    - rewrite Hk1, id_right; reflexivity.
    - rewrite comp_assoc, (ckp_med_left P Hc); exact Hk1. }
  (*
The mediator carries the RIGHT leg to the left one, and being the
     identity it carries it to itself.

--------
调解者把右腿移到左腿上，而作为恒等，它把它带到自身。
*)
  symmetry.
  transitivity (ckp_med P Hc ∘ ckp_right P).
  - rewrite Hw, id_left; reflexivity.
  - exact (ckp_med_right P Hc).
Qed.

Theorem epic_iff_cokernel_pair_left_iso :
  Epic f ↔ IsIsomorphism (ckp_left P).
Proof. split; [ exact epic_ckp_left_iso | exact ckp_left_iso_epic ]. Qed.

End EpiCharacterization.

Arguments epic_iff_pushout_square {C x y} f.
Arguments epic_iff_cokernel_pair_trivial {C x y} f P.
Arguments epic_iff_cokernel_pair_left_iso {C x y} f P.

(**
*** The same at the CHOSEN cokernel pair

    Named aliases so that a consumer working under [HasPushouts] need not
    spell the pushout argument.  Each is the general statement applied to
    [cokernel_pair f], supplied by [:=].

--------
*** 在选定的余核对上相同

    命名别名，以便在 [HasPushouts] 下工作的使用者无需拼写推卷积参数。每个别名都是应用于 [cokernel_pair f] 的通用语句，由 [:=] 提供。
*)

Definition epic_iff_chosen_ckp_trivial {C : Category}
           `{H : @HasPushouts C} {x y : C} (f : x ~> y) :
  Epic f ↔ ckp_left (cokernel_pair f) ≈ ckp_right (cokernel_pair f) :=
  epic_iff_cokernel_pair_trivial f (cokernel_pair f).

Definition epic_iff_chosen_ckp_left_iso {C : Category}
           `{H : @HasPushouts C} {x y : C} (f : x ~> y) :
  Epic f ↔ IsIsomorphism (ckp_left (cokernel_pair f)) :=
  epic_iff_cokernel_pair_left_iso f (cokernel_pair f).

(**
** The [Monic] dual, by duality

    Every statement below is one of the three above instantiated at C^op
    and re-typed through Duality.v's [Monic]/[Epic] bridges.  No proof
    content is repeated: each is supplied by [:=] or by a two-line
    [split] over the C^op instance.

    The two conversions that carry the transfer are MEASURED, not assumed;
    see the [eq_refl] lemmas immediately below.

--------
** [Monic] 双重，通过对偶性

下列每个陈述都是上面三个之一在 C^op 上的实例化，并通过 Duality.v 的 [Monic]/[Epic] 桥重新类型化。没有重复的证明内容：每个内容由 [:=] 或通过 C^op 实例上的两行 [split] 提供。

承载转换的两个转换是经过测量的 (MEASURED)，而不是假设的；请参见下面的 [eq_refl] 引理。
*)

Section OpConversions.

Context {C : Category}.
Context {x y : C}.
Context (f : x ~> y).

(*
The identity pushout square at C^op IS the identity pullback square at
   C.  This holds because (C^op)^op reduces to C in this library
   (Construction/Opposite.v), so the two [IsPullback] applications are the
   same term.  Measured: [eq_refl].

--------
在 C^op 上的恒等推进方格是 C 上的恒等拉回方格。这是因为在这个库（Construction/Opposite.v）中 (C^op)^op 化简为 C，因此两个 [IsPullback] 的应用是相同的项。测量：[eq_refl]。
*)
Definition op_collapse_pushout_square :
  @IsPushoutSquare (C^op) y x x f f x id id
    = @IsPullback C x x y f f x id id := eq_refl.

(*
A pushout of f with itself in C^op IS a pullback of f with itself in C,
   and the cokernel-pair legs there ARE the pullback projections here.
   Measured: [eq_refl] in all three.  This is what makes the [Monic]
   statements below literal instantiations rather than restatements.

--------
在 C^op 中 f 与自身的推顶是 C 中 f 与自身的拉回，并且那里的余核对的两条腿就是这里的拉回投影。在所有三个中测量：[eq_refl]。这就是下文的 [Monic] 语句成为字面实例而非重述的原因。
*)
Definition op_collapse_cokernel_pair :
  @IsPushout (C^op) y x x f f = @Pullback C x x y f f := eq_refl.

Definition op_collapse_ckp_left (P : Pullback f f) :
  @ckp_left (C^op) y x f P = pullback_fst f f P := eq_refl.

Definition op_collapse_ckp_right (P : Pullback f f) :
  @ckp_right (C^op) y x f P = pullback_snd f f P := eq_refl.

(*
[IsIsomorphism] at C^op and at C carry the same inverse and swap their
   two law fields, so the conversion is a field permutation with no proof
   content.  It is not [eq_refl]: the records differ in field ORDER, and
   the [Fail] probe of Test/ProbeCokernelPair.v pins that.

--------
C^op 和 C 上的 [IsIsomorphism] 拥有相同的逆，并交换它们的两个法律字段，因此该转换只是字段排列，没有证明内容。它不是 [eq_refl]：这些记录在字段顺序上不同，而 Test/ProbeCokernelPair.v 的 [Fail] 探针对此进行了固定。
*)
Definition IsIsomorphism_of_op {a b : C} (h : b ~> a)
           (I : @IsIsomorphism (C^op) a b h) : @IsIsomorphism C b a h :=
  @Build_IsIsomorphism C b a h
    (@two_sided_inverse (C^op) a b h I)
    (@is_left_inverse (C^op) a b h I)
    (@is_right_inverse (C^op) a b h I).

Definition op_IsIsomorphism_of {a b : C} (h : b ~> a)
           (I : @IsIsomorphism C b a h) : @IsIsomorphism (C^op) a b h :=
  @Build_IsIsomorphism (C^op) a b h
    (@two_sided_inverse C b a h I)
    (@is_left_inverse C b a h I)
    (@is_right_inverse C b a h I).

End OpConversions.

Section MonoCharacterization.

Context {C : Category}.
Context {x y : C}.
Context (f : x ~> y).

(*
[Monic f] ↔ the square on f with two identity legs is a PULLBACK.  This
   is Seven Sketches Definition 7.5's mono clause; that clause proper is
   issue #672's territory, and what is delivered here is strictly the dual
   of this issue's epi theorem, obtained by instantiating it at C^op.

--------
[Monic f] ↔ 带有两个恒等箭头的 f 上的方形是一个拉回。这是《Seven Sketches》定义 7.5 的单射条款；该条款本身属于问题 #672 的范围，而这里提供的严格是该问题上满射定理的对偶，通过在 C^op 上实例化该定理获得。
*)
Theorem monic_iff_pullback_square : Monic f ↔ IsPullback f f x id id.
Proof.
  split.
  - intro M.
    exact (epic_pushout_square (C:=C^op) f (op_Epic_of_Monic f M)).
  - intro H.
    exact (Monic_of_op_Epic f (pushout_square_epic (C:=C^op) f H)).
Qed.

(*
The kernel-pair phrasing: f is monic exactly when its kernel pair is
   trivial, i.e. its two projections coincide.  Stated for an ARBITRARY
   pullback of f with itself, matching the cokernel-pair side.

--------
核对偶表述：f 当且仅当其核对偶是平凡的，即其两个投影相同时是单射。针对 f 与其自身的任意拉回，匹配余核对偶一侧的表述。
*)
Theorem monic_iff_kernel_pair_trivial (P : Pullback f f) :
  Monic f ↔ pullback_fst f f P ≈ pullback_snd f f P.
Proof.
  split.
  - intro M.
    exact (epic_ckp_trivial (C:=C^op) f P (op_Epic_of_Monic f M)).
  - intro Ht.
    exact (Monic_of_op_Epic f (ckp_trivial_epic (C:=C^op) f P Ht)).
Qed.

(* Stated in C, not in C^op: the projection is an isomorphism there. / 在 C 中陈述，不在 C^op 中：投影在那里是一个同构。 *)
Theorem monic_iff_kernel_pair_fst_iso (P : Pullback f f) :
  Monic f ↔ IsIsomorphism (pullback_fst f f P).
Proof.
  split.
  - intro M.
    exact (IsIsomorphism_of_op _
             (epic_ckp_left_iso (C:=C^op) f P (op_Epic_of_Monic f M))).
  - intro I.
    exact (Monic_of_op_Epic f
             (ckp_left_iso_epic (C:=C^op) f P (op_IsIsomorphism_of _ I))).
Qed.

End MonoCharacterization.
