Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.

Generalizable All Variables.

(*
Quotient objects, and their lattice, by transport through C^op

   nLab:  https://ncatlab.org/nlab/show/quotient+object
   nLab:  https://ncatlab.org/nlab/show/subobject
   nLab:  https://ncatlab.org/nlab/show/coimage

   Mac Lane, “Categories for the Working Mathematician”, 2nd ed. (GTM 5),
   §V.7, book p. 126 (PDF pp. 135-136), Definition 3, is the source.
   Having defined a subobject of x as an equivalence class of monos into
   x ordered by factorization (Definition 2, the previous file), Mac Lane
   defines a QUOTIENT OBJECT of x to be the dual: an equivalence class of
   epis OUT of x, two epis being equivalent when each factors through the
   other, and the order again given by factorization.  He observes that
   in a category whose epis are surjections these classes are the usual
   quotients -- for groups, the quotient objects of G are exactly the
   G/N for N normal in G, the surjection G ↠ G/N standing for its class.
   Neither clause is discharged in this file, and the NOT DELIVERED
   paragraph below says so in terms.

   THE IDIOM.  A quotient object of x in C is a subobject of x in C^op,
   so the definition is one line and every consequence is an
   instantiation.  That is the library's standard device for dual
   notions: Theory/Monad.v is [Comonad `{M : C ⟶ C} := @Monad (C^op)
   (M^op)], and Comonad/Duality.v ([op_Monad_of_Comonad],
   [Comonad_of_op_Monad]) are the two bridges between the readings, each
   proved by [:= H] -- no data moves, only the name of the direction.
   The same holds here: [QuotObj x := @SubObj (C^op) x], and every lemma
   in the order theory below is a [:=] instantiation of its subobject
   counterpart at C^op, not a second proof.  The only constants in this
   file with proof content of their own are [quot_equiv_iff_iso] with its
   one-directional corollary [quot_equiv_of_cod_iso] (first proved in the
   Grp witness during the parallel build and lifted here), and
   [mk_quot_respects] (the covariant repackaging of the setoid, whose
   necessity is measured below), and the four-field permutations
   [Iso_of_op_Iso]/[op_Iso_of_Iso] -- five in all.

   WHY THE COVARIANT READINGS ARE FREE.  Construction/Opposite.v
   builds [Opposite] by permuting fields rather than by composing them
   with symmetry proofs: [hom := fun x y => @hom C y x] and
   [compose := fun _ _ _ f g => g ∘ f], so a C^op-arrow into x IS
   a C-arrow out of x and a C^op-composite IS the reversed C-composite,
   both on the nose.  Two consequences are pinned here as [eq_refl]
   readbacks, because they are about the DATA and not about a morphism.
   [QuotObj_op_is_SubObj] : [@QuotObj (C^op) x = @SubObj C x] -- quotient
   objects of C^op are subobjects of C, C^op^op being C by conversion.
   [quot_le_unfold] : [quot_le q r] is literally
   [{ k : quot_cod r ~> quot_cod q & k ∘ quot_epi r ≈ quot_epi q }], the
   covariant factorization order, with no rewriting.

   MONIC IN C^op IS EPIC IN C, AND CONVERSELY.  The issue that prompted
   this file (#446) recorded, as one of its gaps, that there is “no lemma
   identifying Monic in C^op with the Epic class of Theory/Morphisms.v”.
   That was STALE when written and is cited here as such:
   Theory/Morphisms/Duality.v carries all four bridges --
   [Monic_of_op_Epic], [op_Epic_of_Monic],
   [Epic_of_op_Monic] and [op_Monic_of_Epic] -- each a single
   constructor application, because [Monic] and [Epic] are two distinct
   one-field records whose fields have the SAME type once the opposite
   hom and composition are unfolded (that file's header says exactly
   this).  [monic_op_iff_epic] below is the pair of the two
   directions this file consumes, and [epic_of_monic_op] /
   [monic_op_of_epic] name its projections.  The other two bridges are
   the reason [QuotObj_op_is_SubObj] closes the circle rather than
   merely pointing one way: an [Epic] in C^op is a [Monic] in C by
   [Monic_of_op_Epic], so the quotient objects of C^op and the
   subobjects of C carry the same monicity witness as well as the same
   arrow.  (The issue cited [Epic] at the wrong place in
   Theory/Morphisms.v; its declaration was re-measured in this worktree
   with grep -n '^Class Epic'.)

   WHAT THE SETOID COSTS, MEASURED.  The one place where the transport
   is NOT free is the equivalence.  Theory/Subobject.v's
   [SubObj_Setoid] witnesses [u ≈ v] by an isomorphism of the DOMAINS
   commuting with the monos; read at C^op that witness is an
   isomorphism IN C^op of the codomains, whose [to] component is a
   C-arrow pointing the other way.  So the definitional unfolding of
   [q ≈ r] is [quot_equiv_unfold] below --
   [{ i : @Isomorphism (C^op) (quot_cod q) (quot_cod r)
      & (to i ∘[C] quot_epi r) ≈ quot_epi q }] -- which needs BOTH the
   C^op spelling of the isomorphism and the composition annotated with
   its category, and which is an [eq_refl].  The naive covariant
   spelling is REFUSED, and this is the measurement, not a guess: with
   the same requirement list,
     [Example m (q r : QuotObj x) :
        (q ≈ r) = { i : quot_cod q ≅ quot_cod r
                  & to i ∘ quot_epi q ≈ quot_epi r } := eq_refl.]
   is rejected as
     “The term ”eq_refl“ has type ”(q ≈ r) = (q ≈ r)“ while it is
      expected to have type ”(q ≈ r) = ∃ i : quot_cod q ≅ quot_cod r,
      i ∘ quot_epi q ≈ quot_epi r“ (cannot unify ...)” --
   a CONVERSION refusal.  The covariant characterization is therefore a
   LEMMA and is stated at ≈, never at [eq_refl]: [quot_equiv_iff_iso]
   says [q ≈ r] iff there is an isomorphism [i : quot_cod q ≅[C]
   quot_cod r] of the codomains IN C with [to i ∘ quot_epi q ≈ quot_epi
   r], the orientation one expects of two epis presenting the same
   quotient.  Its two halves are carried by [Iso_of_op_Iso] and
   [op_Iso_of_Iso], which permute the four fields of [Isomorphism]
   between C^op and C with no proof content -- [iso_to_from] at one side
   IS [iso_from_to] at the other, the two composites having swapped
   endpoints.  An in-tree bridge of this kind already exists, [iso_unop]
   at Functor/Hom/Yoneda/Iso.v, and is NOT required here: it lives in
   the Yoneda development, far above this file, and its orientation is
   the other one ([to := from i], giving [x ≅ y] from [@Isomorphism C^op
   x y], where the orientation needed below is [to := to i], giving
   [y ≅ x]).  Construction/Opposite.v's [Isomorphism_Opposite] goes
   only from C to C^op.

   WHICH ORDER, AND WHICH BOUND IS WHICH.  [quot_le q r] holds when the
   epi of q factors through the epi of r; q is then the COARSER
   quotient, the one further from x.  For groups, with q = (G ↠ G/N) and
   r = (G ↠ G/M), that reads M ⊆ N: the order on quotient objects is the
   REVERSE of the inclusion order on the kernels.  Everything below is
   stated for [quot_le] and the reader must not silently substitute the
   other convention.  In particular [quot_meet] -- [sub_meet] at C^op,
   which is the PUSHOUT in C of the two epis -- is the GREATEST LOWER
   BOUND for [quot_le]: the finest quotient that FACTORS THROUGH both q
   and r, i.e. the finest one below both (an earlier revision of this
   sentence had the direction of “factors through” backwards, saying
   “that both q and r factor through”; an audit caught it against the
   definition two paragraphs up), which for groups is G/(NM).  A reader
   who orders quotients
   by the size of the codomain, or who identifies a quotient with its
   kernel, sees that same object as a JOIN (NM is the join of N and M as
   subgroups).  It is not named [quot_join] here, and [quot_join] below
   means something else: the least upper bound for [quot_le], the
   coimage of the pairing, G/(N ∩ M) in the same illustration.  The two
   ends match: [quot_top] is the identity quotient (the finest, the top
   for [quot_le]) and [quot_bot] is the quotient by the terminal object
   (the coarsest, the bottom), which exists only when [one : x ~> 1] is
   epic.

   WHAT IS TRANSPORTED, AND FROM WHERE.  Theory/Subobject.v supplies the
   record, the setoid, the preorder [sub_le] with its
   monic and unique mediating arrow, and
   [sub_equiv_iff_mutual]; all five arrive here as [quot_cod] /
   [quot_epi] / [QuotObj_Setoid] / [quot_le] / [quot_le_epic] /
   [quot_le_unique] / [quot_equiv_iff_mutual].  Theory/Subobject/
   Lattice.v supplies the order structure: [sub_top] and
   [sub_bot] with [zero_monic_of_strict], the binary
   meet by pullback with its two projections, its
   greatest-lower-bound property and the four laws, the order vocabulary
   [IsIntersection] / [IsMeet], the wide intersection, the [ImageOf]
   record and [HasImages] class, the join by image of the copairing, and
   the absorption pair.
   Three dualizations make the transport work.  Structure/Pushout.v's
   [HasPullbacks_op_of_HasPushouts] turns the [HasPushouts C] hypothesis
   into the [HasPullbacks (C^op)] that [sub_meet] consumes.
   Structure/Cocartesian.v defines [@Cocartesian C] as NOTATION for
   [@Cartesian (C^op)], so the [Cocartesian (C^op)] that [sub_join]
   consumes is [@Cartesian (C^op^op)] and a plain [Cartesian C] is
   accepted for it by conversion -- MEASURED, with
   [Definition m : @Cocartesian (C^op) := _.] compiling under a
   [Context `{@Cartesian C}].  That is why the join half of this file is
   conditional on PRODUCTS of C: [quot_pairing q r] is
   [⟨quot_epi q, quot_epi r⟩ : x ~> quot_cod q × quot_cod r], the C^op
   copairing read forwards, and the join is its coimage.  Likewise
   Structure/Initial.v defines [Initial C] as [@Terminal (C^op)], so
   [sub_bot] at C^op takes a [Terminal C] and a [Monic] of the opposite
   arrow, that is an [Epic (one : x ~> 1)] in C.

   COIMAGES.  [CoimageOf f := @ImageOf (C^op) y x f] for [f : x ~> y],
   read covariantly: a quotient [e : x ↠ z] of x, a map [m : z ~> y]
   with [m ∘ e ≈ f], and the clause that e is the LEAST such quotient
   for [quot_le] -- that is, the COARSEST quotient of x through which f
   factors, which in Sets is x modulo the fibres of f.  [HasCoimages C]
   is notation for [@HasImages (C^op)], following the [Cocartesian] and
   [Initial] precedent so that instance resolution still fires.  One
   inference trap is worth recording, because it cost a compilation
   here: [CoimageOf] takes its category from the type of its argument,
   and an argument SPELLED as a C^op-arrow makes Rocq choose C^op for
   that category and produce [@ImageOf (C^op^op) ...] with the two
   objects swapped.  Hence [quot_pairing], whose type is written in C;
   applying [CoimageOf] to it fixes the category on the first try.

   UNIVERSES, measured with [Set Printing Universes. About ...] rather
   than read off the source, which carries no annotation.  Every
   constant here binds its category as [Category@{u u0 u0}], the hom
   universe identified with the proof universe -- [quot_le], [quot_epi],
   [quot_meet], [quot_join], [CoimageOf], [Iso_of_op_Iso] and the rest;
   [QuotObj] itself prints as
   [QuotObj@{u u0 u1} : ∀ {C : Category@{u0 u1 u1}}, obj[C] →
   Type@{u}], the same collapse with the result level named.  It is
   INHERITED and belongs to Theory/Subobject.v, the first carrier in
   dependency order, whose [SubObj] record holds a mono and its [Monic]
   proof under two universe variables and prints as
   [SubObj@{u u0} : ∀ {C : Category@{u u0 u0}}, obj[C] →
   Type@{max(u,u0)}]; Theory/Subobject/Lattice.v's header records the
   same inheritance for the same reason, and nothing is re-attributed
   here.  Two further constraints are likewise inherited, not
   introduced.  [quot_meet] carries [u0 <= prod_rect.u0],
   [u0 <= prod_rect.u1] and [u0 <= prod_rect.u2], the stdlib bounds that
   come with the sigma and pair types of [sub_le] and the pullback
   universal property.  [quot_equiv_iff_iso] carries the STRICT bound
   [u0 < u1]; measured on the donors, [SubObj_Setoid] at
   Theory/Subobject.v already carries [p < u0] and so do
   [sub_equiv_iff_mutual] and [sub_le_antisym]
   (Theory/Subobject/Lattice.v), the [Setoid] record sitting
   strictly above the proof universe.  No constant here is pinned to
   [Set].

   NOT DELIVERED.  No concrete category: this file has no [HasPushouts],
   no [WidePullback] at C^op, no [HasCoimages] and no [Terminal]
   instance for anything, and exhibits no quotient object of any object
   -- the whole development is a conditional over structure supplied
   from outside, and docs/INHABITATION.md is where the question of which
   witnesses exist is settled.  Mac Lane's two illustrations are
   therefore NOT here: the clause that quotient objects are the usual
   quotients where epis are surjections is not stated over [Sets] (the
   ingredient exists, [epic_implies_surjective] at Instance/Sets.v,
   and is not consumed), and the G/N reading of the quotient objects of
   a group appears only as prose in this header, the tree carrying no
   group theory wired to [QuotObj].  No wide pushouts: Structure/
   Pullback/Wide.v has no wide-pushout vocabulary at all (grep for
   WidePushout over the tree returns nothing) and NONE IS ADDED here --
   [quot_wide_meet] takes a [WidePullback] IN C^op, which is a wide
   pushout of C spelled the other way, and the reader must supply it as
   such.  No total forms: [sub_intersection] under [HasWidePullbacks]
   and [sub_wide_join_via] over an indexed coproduct are not
   transported, and neither are the degenerate-index lemmas
   ([IsIntersection_empty], [IsUnion_empty_of_least], the singletons) or
   [sub_meet_is_wide_intersection].  No coimages from a factorization
   system: [ImageOf_of_OFS] at C^op would need an (E, MonoClass) system
   in C^op and none is built.  No distributivity, no Heyting or Boolean
   structure, no complement and no negation on [QuotObj x].  No
   antisymmetry at Leibniz equality: [quot_le] is Type-valued, its
   induced equivalence is the setoid, and every law below holds at ≈
   only -- [quot_le_antisym] is [sub_equiv_iff_mutual] read at C^op, and
   the two “q ≤ r iff” pairs are four separate lemmas for the same
   reason as in the subobject file.  No respectfulness for the
   accessors: [mk_quot_respects] is proved, a [quot_epi_respects] is
   not, since the epis of two equivalent quotients live over different
   codomains and the statement relating them IS [quot_equiv_iff_iso].
   No functoriality: nothing here says how quotient objects transport
   along a morphism of x, and no Galois connection or adjointness claim
   about such a transport appears.

--------
商对象及其晶格，通过 C^op 传输

nLab：https://ncatlab.org/nlab/show/quotient+object
 nLab：https://ncatlab.org/nlab/show/subobject
 nLab：https://ncatlab.org/nlab/show/coimage

Mac Lane，“工作数学家的范畴”，第二版。 （GTM 5），
 §V.7，书页。 126（PDF 第 135-136 页），定义 3，是来源。 
将 x 的子对象定义为 monos 的等价类
 x 按因式分解排序（定义 2，上一个文件），Mac Lane
 将 x 的 QUOTIENT OBJECT 定义为对偶： 的等价类
 epis OUT of x，当每个因子都通过
 其他，以及因式分解再次给出的顺序。 他观察到
 在一个 Epis 是满射的范畴中，这些类是常见的
 商——对于群，G 的商对象恰好是
 G/N 代表 G 中的 N 正规，满射 G ↠ G/N 代表其范畴。 
此文件中这两个条款均未解除，并且 NOT DELIVERED
 下面的段落是这么说的。

成语。 C 中 x 的商对象是 C^op 中 x 的子对象，
 所以定义是一行，每个结果都是一个
 实例化。 这是图书馆的标准双设备
 概念：Theory/Monad.v 是 [Comonad `{M : C ⟶ C} := @Monad (C^op)
 (M^op)] 和 Comonad/Duality.v ([op_Monad_of_Comonad],
 [Comonad_of_op_Monad]) 是读数之间的两个桥梁，每个桥梁
 由 [:= H] 证明——没有数据移动，只有方向名称。 
这同样适用于：[QuotObj x := @SubObj (C^op) x]，以及每个引理
 下面的顺序理论是其子对象的 [:=] 实例化
 C^op 处的对应部分，而不是第二个证明。 其中唯一的常数
 具有自己的证明内容的文件是 [quot_equiv_iff_iso] 及其
 单向推论 [quot_equiv_of_cod_iso]（首先在
 Grp 在并行构建期间见证并在此处解除），以及
 [mk_quot_respects]（setoid 的协变重新包装，其
 必要性测量如下），以及四场排列
 [Iso_of_op_Iso]/[op_Iso_of_Iso]——总共五个。

为什么协变量读数是免费的。 建筑/对面.v
 通过排列字段而不是组合字段来构建 [Opposite]
 具有对称性证明：[hom := fun x y => @hom C y x] 和
 [compose := fun _ _ _ f g => g ∘ f]，因此 C^op 箭头指向 x IS
 x 中的 C 箭头和 C^op-composite 是反转的 C-composite，
 两者都在鼻子上。 此处将两个结果固定为 [eq_refl]
 回读，因为它们是关于数据而不是态射。 
[QuotObj_op_is_SubObj] : [@QuotObj (C^op) x = @SubObj C x] -- 商
 C^op 的对象是 C 的子对象，C^op^op 通过转换成为 C。 
[quot_le_unfold] : [quot_le q r] 字面意思是
 [{ k : quot_cod r ~> quot_cod q & k ∘ quot_epi r ≈ quot_epi q }]，
 协变分解顺序，无需重写。

C^op 中的 MONIC 是 C 中的史诗，反之亦然。 提示的问题
 该文件（#446）记录了“没有引理”，作为其缺陷之一
 将 C^op 中的 Monic 与 Theory/Morphisms.v 的 Epic 类进行识别。 这是陈旧的，在编写时是这样引用的：
 Theory/Morphisms/Duality.v 承载所有四个桥梁 --
 [Monic_of_op_Epic]、[op_Epic_of_Monic]、
 [Epic_of_op_Monic] 和 [op_Monic_of_Epic] — 各一个
 构造函数应用程序，因为 [Monic] 和 [Epic] 是两个不同的
 单字段记录，其字段具有相同类型，一旦相反
 hom 和合成已展开（该文件的标题准确地说
 这个）。 下面的 [monic_op_iff_epic] 是两者的一对
 该文件使用的方向，以及 [epic_of_monic_op] /
 [monic_op_of_epic] 为其投影命名。
另外两座桥是
 [QuotObj_op_is_SubObj] 关闭圆圈而不是
 仅指向一种方式：C^op 中的 [Epic] 是 C 中的 [Monic]
 [Monic_of_op_Epic]，因此 C^op 的商对象和
 C 的子对象具有相同的货币性见证以及相同的
 箭头。 （该问题在错误的位置引用了 [Epic]
 理论/态射.v； 在此工作树中重新测量了其声明
 与 grep -n '^Class Epic'。）

测量睾酮的费用是多少。 交通一处
 不是免费的是等价的。 理论/子对象.v's
 [SubObj_Setoid] 通过域的同构见证 [u ≈ v]
 与单声道通勤； 在 C^op 读到证人是
 同构 IN C^op 共域，其 [to] 组件是
 C 箭头指向另一个方向。 所以定义展开
 下面是 [q ≈ r] 是 [quot_equiv_unfold] --
 [{ i : @同构 (C^op) (quot_cod q) (quot_cod r)
 & (to i ∘[C] quot_epi r) ≈ quot_epi q }] -- 两者都需要
 同构的 C^op 拼写和注释为的组合
 它的范畴是 [eq_refl]。
朴素协变
 拼写被拒绝，这是测量结果，而不是猜测：
 相同的需求清单，
 [示例 m (q r : QuotObj x) ：
 (q ≈ r) = { i : quot_cod q ≅ quot_cod r
 & 至 i ∘ quot_epi q ≈ quot_epi r } := eq_refl.]
 被拒绝为
 “术语“eq_refl”的类型为“(q ≈ r) = (q ≈ r)”，而它是
 预计具有类型“(q ≈ r) = ∃ i : quot_cod q ≅ quot_cod r,
 i ∘ quot_epi q ≈ quot_epi r“ （无法统一...）” --
 转换拒绝。 因此，协变特征是
 LEMMA 并在 ≈ 处说明，从不在 [eq_refl] 处说明：[quot_equiv_iff_iso]
 说 [q ≈ r] 当且仅当存在同构 [i : quot_cod q ≅[C]
 共域 IN C 的 quot_cod r] 与 [to i ∘ quot_epi q ≈ quot_epi
 r]，人们期望两个 epi 呈现相同的方向
 商。
它的两半由 [Iso_of_op_Iso] 承载，
 [op_Iso_of_Iso]，排列 [Isomorphism] 的四个字段
 C^op 和 C 之间，无证明内容 -- [iso_to_from] 位于一侧
 另一个是 [iso_from_to]，两种复合材料已互换
 端点。 这种树内桥已经存在，[iso_unop]
 在 Functor/Hom/Yoneda/Iso.v，这里不需要：它位于
 米田的开发，远远高于这个文件，它的定位是
 另一个（[to := from i]，从 [@Isomorphism C^op 得到 [x ≅ y]
 x y]，其中下面需要的方向是 [to := to i]，给出
 [y ≅ x]）。 Construction/Opposite.v 的 [Isomorphism_Opposite] 上线
 仅从 C 到 C^op。

哪个顺序，哪个界限就是哪个。 [quot_le q r] 成立时
 q因子的epi通过r的epi； q 是较粗的
 商，离 x 更远的一个。 对于群，q = (G ↠ G/N) 且
 r = (G ↠ G/M)，即 M ⊆ N：商对象的顺序是
 内核上的包含顺序相反。 下面的一切都是
 [quot_le] 的说明，读者不得默默地替换
 其他约定。 特别是 C^op 处的 [quot_meet] -- [sub_meet]，
 这是两个 Epis 的 C 中的 PUSHOUT——是最大的下限
 绑定 [quot_le]：通过两个 q 进行分解的最佳商
 和 r，即
两者之下最好的一个（此的早期修订版
 句子的“因素通过”方向向后，说
 “q 和 r 都通过因子”； 审计发现它反对
 定义上两段），对于组来说是 G/(NM)。 一位读者
 谁对商进行排序
 通过共域的大小，或者用它的商来确定商
 内核，将同一个对象视为 JOIN（NM 是 N 和 M 的连接，如
 子组）。 这里不命名为[quot_join]，下面命名为[quot_join]
 意味着其他东西：[quot_le] 的最小上限，
 配对的余像，同一图中的 G/(N ∩ M)。 两人
 结束匹配：[quot_top] 是同一商（最优秀、最顶级
 对于 [quot_le]），[quot_bot] 是终端对象的商
 （最粗，底部），仅当 [one : x ~> 1] 时存在
 史诗般的。

运输什么以及从哪里运输。 Theory/Subobject.v 提供
 记录，setoid，预购 [sub_le] 及其
 单调和独特的中介箭头，以及
 [sub_equiv_iff_mutual]； 五人均以 [quot_cod] 的恒等抵达这里 /
 [quot_epi] / [QuotObj_Setoid] / [quot_le] / [quot_le_epic] /
 [quot_le_unique] / [quot_equiv_iff_mutual]。 理论/子对象/
 Lattice.v 提供指令结构：[sub_top] 和
 [sub_bot] 与 [zero_monic_of_strict]，二进制文件
 通过回调与其两个投影相遇，其
 最大下界性质和四大定律、顺序词汇
 [IsIntersection] / [IsMeet]，宽交叉路口，[ImageOf]
 记录和 [HasImages] 类，通过配对的图像连接，以及
 吸收对。 三个二元化使运输发挥作用。 结构/Pushout.v's
 [HasPullbacks_op_of_HasPushouts] 改变了 [HasPushouts C] 假设
 到 [sub_meet] 消耗的 [HasPullbacks (C^op)] 中。
Structure/Cocartesian.v 将 [@Cocartesian C] 定义为 NOTATION
 [@Cartesian (C^op)]，所以 [Cocartesian (C^op)] 就是 [sub_join]
 消耗的是 [@Cartesian (C^op^op)]，普通的 [Cartesian C] 是
 通过转换接受它 - MEASURED，与
 [Definition m : @Cocartesian (C^op) := _.]下编译
 XPTECT94X。 这就是为什么这个文件的连接部分是
 以 C: [quot_pairing q r] 的产品为条件
 [⟨quot_epi q, quot_epi r⟩ : x ~> quot_cod q × quot_cod r]，C^op
 copairing 向前读，而 join 是它的余像。 同样
 Structure/Initial.v 将 [Initial C] 定义为 [@Terminal (C^op)]，因此
 C^op 处的 [sub_bot] 采用 [Terminal C] 和相反的 [Monic]
 箭头，即 C 语言的 [Epic (one : x ~> 1)]。

图像。 [CoimageOf f := @ImageOf (C^op) y x f] 用于 [f : x ~> y]，
 协变读取：x 的商 [e : x ↠ z]，映射 [m : z ~> y]
 与 [m ∘ e ≈ f]，以及 e 是 LEAST 这样的商的子句
 对于 [quot_le]——即 x 的 COARSEST 商，通过该商 f
 因子，在集合中是 x 以 f 的纤维为模。 保护109X
 是 [@HasImages (C^op)] 的符号，紧随 [Cocartesian] 和
 [Initial] 先例，因此实例解析仍然会触发。 一
 推理陷阱值得记录，因为它需要编译
 这里：[CoimageOf] 从其参数的类型中获取其范畴，
 并且参数拼写为 C^op 箭头使 Rocq 选择 C^op
 该范畴并生产 [@ImageOf (C^op^op) ...] 与两个
 交换了对象。 因此[quot_pairing]，其类型是用C编写的；
 应用 [CoimageOf] 即可在第一次尝试时修复范畴。

宇宙，用 [Set Printing Universes. About ...] 测量
 而不是阅读没有注释的源代码。 每个
 这里的常量将其范畴绑定为 [Category@{u u0 u0}]，即 hom
 与证明宇宙相同的宇宙——[quot_le]、[quot_epi]、
 [quot_meet]、[quot_join]、[CoimageOf]、[Iso_of_op_Iso] 等；
 [QuotObj] 本身打印为
 [QuotObj@{u u0 u1} : ∀ {C : Category@{u0 u1 u1}}, obj[C] →
 输入@{u}]，与命名的结果级别相同的折叠。 它是
 INHERITED 并属于 Theory/Subobject.v，第一个载体
 依赖顺序，其 [SubObj] 记录保存单声道及其 [Monic]
 两个宇宙变量下的证明并打印为
 [SubObj@{u u0} : ∀ {C : Category@{u u0 u0}}, obj[C] →
 输入@{max(u,u0)}]; Theory/Subobject/Lattice.v 的头记录了
 由于相同的原因，相同的继承，并且没有任何东西被重新归属
 在这里。 另外两个约束同样是继承的，而不是
 介绍了。
[quot_meet] 搭载 [u0 <= prod_rect.u0]，
 [u0 <= prod_rect.u1] 和 [u0 <= prod_rect.u2]，stdlib 限制
 配备 [sub_le] 的 sigma 和pair 类型以及回调
 普遍财产。 [quot_equiv_iff_iso] 具有 STRICT 界限
 XPTECT136X； 对供体进行测量，[SubObj_Setoid]
 Theory/Subobject.v 已经带有 [p < u0] 了
 [sub_equiv_iff_mutual] 和 [sub_le_antisym]
 (Theory/Subobject/Lattice.v)，[Setoid] 保持纪录
 严格高于证明宇宙。 这里没有固定常量
 [Set]。

未交付。 无具体范畴：该文件没有 [HasPushouts]，
 C^op 处无 [WidePullback]、无 [HasCoimages] 且无 [Terminal]
 任何对象的实例，并且不展示任何对象的商对象
 -- 整个开发是有条件的，而不是提供的结构
 从外部，docs/INHABITATION.md 是哪个问题
 证人存在已解决。 Mac Lane 的两张插图是
 因此不在这里：商对象是通常的子句
 Epis 为满射的商未在 [Sets] 上说明（
 成分存在，[epic_implies_surjective] 位于 Instance/Sets.v，
 并且不被消耗），以及商对象的 G/N 读数
 一组仅作为散文出现在该标题中，该树没有携带
 连接到 [QuotObj] 的群论。
无宽推出：结构/
 Pullback/Wide.v 根本没有 Wide-Pushout 词汇（grep for
 树上的 WidePushout 没有返回任何内容）并且这里没有添加任何内容 --
 [quot_wide_meet] 采用 [WidePullback] IN C^op，这是一个宽
 C 的推出以另一种方式拼写，读者必须将其提供为
 这样的。 无总形式：[HasWidePullbacks] 下的 [sub_intersection]
 和 [sub_wide_join_via] 在索引余积上不是
 被传输，并且简并索引引理也不被传输
 （[IsIntersection_empty]、[IsUnion_empty_of_least]、单例）或
 [sub_meet_is_wide_intersection]。 因式分解没有余像
 系统：C^op 处的 [ImageOf_of_OFS] 需要一个（E，MonoClass）系统
 在 C^op 中并且没有构建。 没有分布性，没有 Heyting 或布尔值
 [QuotObj x] 上没有补体和否定结构。
否
 莱布尼茨等式的反对称：[quot_le] 是类型值的，其
 诱导等价是集合，并且下面的每个定律都在 ≈
 仅 -- [quot_le_antisym] 是在 C^op 处读取的 [sub_equiv_iff_mutual]，并且
 两个“q ≤ r iff”对是相同的四个单独的引理
 原因如子对象文件中所示。 没有对人的尊重
 访问器：[mk_quot_respects] 被证明，[quot_epi_respects] 被证明
 不是，因为两个等价商的 epis 存在于不同的环境中
 共域以及与它们相关的声明是 [quot_equiv_iff_iso]。 没有功能性：这里没有说明商对象如何传输
 沿着 x 的态射，并且没有伽罗瓦联系或伴随性主张
 关于这样的运输出现了。
*)

(** ** Quotient objects as subobjects in the opposite category / ** 在对偶范畴中作为子对象的商对象 *)

(*
Mac Lane §V.7: a quotient object of x is (an equivalence class of) an
   epimorphism out of x.  Since [Epic] in C is [Monic] in C^op
   (Theory/Morphisms/Duality.v), the definition is one line, the idiom of
   Theory/Monad.v's [Comonad := @Monad (C^op) (W^op)].

--------
Mac Lane §V.7：x 的商对象是 x 的一个满射（等价类）。由于 C 中的 [Epic] 在 C^op 中是 [Monic]（Theory/Morphisms/Duality.v），定义只有一行，是 Theory/Monad.v 中 [Comonad := @Monad (C^op) (W^op)] 的用法。
*)
Definition QuotObj {C : Category} (x : C) : Type := @SubObj (C^op) x.

Section QuotientAccessors.

Context {C : Category}.
Context {x : C}.

(*
Covariant readings of the record's fields: a C^op-arrow into x is a
   C-arrow out of x, definitionally (Construction/Opposite.v).

--------
记录字段的协变读法：一个指向 x 的 C^op 箭头在定义上是一个从 x 出发的 C 箭头（Construction/Opposite.v）。
*)
Definition quot_cod (q : QuotObj x) : C := sub_dom q.

Definition quot_epi (q : QuotObj x) : x ~> quot_cod q := sub_mono q.

Definition quot_is_epic (q : QuotObj x) : Epic (quot_epi q) :=
  Epic_of_op_Monic (quot_epi q) (sub_is_monic q).

(* A quotient object from an epimorphism of C. / 从 C 的一个满射得到的商对象。 *)
Definition mk_quot {y : C} (e : x ~> y) (He : Epic e) : QuotObj x :=
  @Build_SubObj (C^op) x y e (op_Monic_of_Epic e He).

(*
The setoid and the factorization preorder, read in quotient orientation:
   q ≤ r when the epi of q factors through the epi of r.

--------
集合等价类和分解预序，以商取向阅读：当 q 的满射通过 r 的满射分解时，q ≤ r。
*)
#[export] Instance QuotObj_Setoid : Setoid (QuotObj x) :=
  @SubObj_Setoid (C^op) x.

Definition quot_le (q r : QuotObj x) : Type := @sub_le (C^op) x q r.

End QuotientAccessors.

(** ** Isomorphisms carried across the opposite category / ** 同构在对偶范畴中传递 *)

(*
Four-field permutations, with no proof content: [iso_to_from] on one
   side is [iso_from_to] on the other, because the two round trips swap
   endpoints when the composition is reversed.  Construction/Opposite.v:
   146's [Isomorphism_Opposite] covers only the C-to-C^op direction and
   fixes [to := from i]; both directions and the other orientation are
   needed below.

--------
四域排列，无证明内容：一侧的 [iso_to_from] 在另一侧是 [iso_from_to]，因为当组合顺序被反转时，两次往返会交换端点。Construction/Opposite.v: 146 的 [Isomorphism_Opposite] 仅涵盖 C 到 C^op 的方向，并固定 [to := from i]；下面需要两个方向以及另一种取向。
*)

Section OppositeIso.

Context {C : Category}.

Definition Iso_of_op_Iso {a b : C} (i : @Isomorphism (C^op) a b) : b ≅[C] a :=
  @Build_Isomorphism C b a (to i) (from i) (iso_from_to i) (iso_to_from i).

Definition op_Iso_of_Iso {a b : C} (j : a ≅[C] b) :
  @Isomorphism (C^op) b a :=
  @Build_Isomorphism (C^op) b a (to j) (from j) (iso_from_to j)
    (iso_to_from j).

End OppositeIso.

(** ** The covariant API / ** 协变 API *)

Section QuotientCovariant.

Context {C : Category}.
Context {x : C}.

(*
C^op^op is C by conversion, so the quotient objects of C^op ARE the
   subobjects of C, at Leibniz equality and with no tactic -- a claim
   about the DATA of the type, which is the one place Leibniz equality
   is the right relation.

--------
C^op^op 是通过转换得到的 C，所以 C^op 的商对象是 C 的子对象，在莱布尼茨等式下且没有策略——这是关于类型数据的一个声明，这是莱布尼茨等式是正确关系的唯一地方。
*)
Example QuotObj_op_is_SubObj : @QuotObj (C^op) x = @SubObj C x := eq_refl.

(* The factorization order, covariantly, on the nose. / 因式分解顺序，协变地，恰好如此。 *)
Example quot_le_unfold (q r : QuotObj x) :
  quot_le q r
  = { k : quot_cod r ~> quot_cod q & k ∘ quot_epi r ≈ quot_epi q }
  := eq_refl.

(*
The setoid, covariantly, as far as conversion reaches: the witness is
   an isomorphism IN C^op and the composition must be annotated.  The
   naive spelling, with a C-isomorphism [quot_cod q ≅ quot_cod r] and
   [to i ∘ quot_epi q ≈ quot_epi r], is REFUSED here (cannot unify); the
   header quotes the refusal.  [quot_equiv_iff_iso] below is the
   covariant statement, at ≈ rather than at [eq_refl].

--------
集合体，在协变的情况下，只要转换可达：见证是 C^op 中的同构，并且必须对组合进行注释。这里拒绝了天真的写法，其中有一个 C-同构 [quot_cod q ≅ quot_cod r] 和 [to i ∘ quot_epi q ≈ quot_epi r]（无法统一）；标题引用了拒绝的原因。下方的 [quot_equiv_iff_iso] 是协变声明，使用 ≈ 而不是 [eq_refl]。
*)
Example quot_equiv_unfold (q r : QuotObj x) :
  (q ≈ r)
  = { i : @Isomorphism (C^op) (quot_cod q) (quot_cod r)
    & (to i ∘[C] quot_epi r) ≈ quot_epi q }
  := eq_refl.

Definition quot_le_refl (q : QuotObj x) : quot_le q q :=
  @sub_le_refl (C^op) x q.

Definition quot_le_trans (q r s : QuotObj x) :
  quot_le q r → quot_le r s → quot_le q s :=
  @sub_le_trans (C^op) x q r s.

(*
The mediating arrow of a factorization between quotient objects is
   itself an EPI of C: [sub_le_monic] (Theory/Subobject.v) read at
   C^op, then carried back by [Epic_of_op_Monic].  Both the target type
   and the bridge's category have to be given explicitly, since the
   arrow's type is spelled at C^op and Rocq would otherwise read [Epic]
   there -- which is [Monic] in C, the wrong claim.

--------
因子分解中商对象之间的中介箭头本身就是 C 的一个 EPI：在 C^op 中读取 C^op, 然后通过 [Epic_of_op_Monic] 回传。目标类型和桥的范畴都必须明确给出，因为箭头的类型是在 C^op 中说明的，否则 Rocq 会在那里读取 [Epic] —— 这是在 C 中的 [Monic]，这是错误的说法。
*)
Definition quot_le_epic (q r : QuotObj x) (H : quot_le q r) :
  @Epic C (quot_cod r) (quot_cod q) (`1 H) :=
  @Epic_of_op_Monic C (quot_cod r) (quot_cod q) (`1 H)
    (@sub_le_monic (C^op) x q r H).

(* Mediating arrows are unique, by epicness of the epi factored through. / 调解箭头是独特的，通过史诗因素的史诗性体现出来。 *)
Definition quot_le_unique (q r : QuotObj x)
  (k k' : quot_cod r ~> quot_cod q) :
  k ∘ quot_epi r ≈ quot_epi q → k' ∘ quot_epi r ≈ quot_epi q → k ≈ k' :=
  @sub_le_unique (C^op) x q r k k'.

(* Mac Lane's equivalence of epis: each factors through the other. / Mac Lane 的射的等价性：每个通过另一个分解。 *)
Definition quot_equiv_iff_mutual (q r : QuotObj x) :
  (q ≈ r) ↔ (quot_le q r * quot_le r q) :=
  @sub_equiv_iff_mutual (C^op) x q r.

Definition quot_le_antisym (q r : QuotObj x) :
  quot_le q r → quot_le r q → q ≈ r :=
  @sub_le_antisym (C^op) x q r.

Definition quot_le_of_equiv (q r : QuotObj x) : q ≈ r → quot_le q r :=
  @sub_le_of_equiv (C^op) x q r.

Definition quot_ge_of_equiv (q r : QuotObj x) : q ≈ r → quot_le r q :=
  @sub_ge_of_equiv (C^op) x q r.

(*
The covariant characterization of the setoid, which conversion does
   NOT give (see [quot_equiv_unfold]): two quotient objects are
   equivalent exactly when an isomorphism of their codomains IN C
   carries the one epi to the other.  Both directions go through the
   symmetry of the setoid, because the C^op reading of [q ≈ r] carries
   the isomorphism in the opposite orientation; the field permutations
   then leave nothing to prove, and each branch ends in [exact].

--------
集合化的协变刻画，其转换不能给出（参见 [quot_equiv_unfold]）：当且仅当在 C 中它们上同域的一个同构将一个满射映射到另一个满射时，两个商对象才是等价的。两个方向都通过集合化的对称性，因为 [q ≈ r] 的 C^op 版本以相反的方向传递同构；然后域置换不再留有需要证明的内容，每个分支最终都在 [exact] 结束。
*)
Theorem quot_equiv_iff_iso (q r : QuotObj x) :
  (q ≈ r) ↔ { i : quot_cod q ≅[C] quot_cod r
            & to i ∘ quot_epi q ≈ quot_epi r }.
Proof.
  split.
  - intros H.
    symmetry in H.
    destruct H as [i Hi].
    exists (Iso_of_op_Iso i).
    exact Hi.
  - intros [j Hj].
    symmetry.
    exists (op_Iso_of_Iso j).
    exact Hj.
Defined.

(*
Equivalent epis out of x present the same quotient object, the
   identity isomorphism witnessing it.

--------
来自 x 的等价上射呈现相同的商对象，恒等同构作证其存在。
*)
Definition mk_quot_respects {y : C} (e e' : x ~> y)
  (He : Epic e) (He' : Epic e') : e ≈ e' → mk_quot e He ≈ mk_quot e' He'.
Proof.
  intros Hee.
  apply quot_equiv_iff_iso.
  exists iso_id.
  simpl.
  rewrite id_left.
  now symmetry.
Defined.

(*
The one-directional form with the isomorphism handed in the OTHER way
   round -- from the codomain of the second argument to that of the
   first -- which is the shape a consumer comparing a computed quotient
   with a named one (Instance/Grp/QuotObj.v's isomorphism-theorem reading)
   actually has in hand.  First proved in that file during the parallel
   build; lifted here at integration as a corollary of
   [quot_equiv_iff_iso] rather than kept as a second proof.

--------
单向形式伴随同构以相反的方式——从第二个参数的陪域到第一个参数的陪域——这是一个消费者在比较计算得到的商与一个已命名的商时（Instance/Grp/QuotObj.v 中同构定理的解释）实际上手中所拥有的形状。首次在该文件的并行构建中证明；在集成时作为 [quot_equiv_iff_iso] 的推论引入此处，而不是保留为第二个证明。
*)
Corollary quot_equiv_of_cod_iso (q r : QuotObj x)
  (i : quot_cod r ≅[C] quot_cod q)
  (H : to i ∘ quot_epi r ≈ quot_epi q) : q ≈ r.
Proof.
  symmetry.
  exact (snd (quot_equiv_iff_iso r q) (i; H)).
Defined.

End QuotientCovariant.

(** ** Monic in C^op is Epic in C, both ways / ** 在 C^op 中的单射在 C 中就是满射，反之亦然 *)

Definition monic_op_iff_epic {C : Category} {x y : C} (f : x ~> y) :
  (@Monic (C^op) y x f → @Epic C x y f) * (@Epic C x y f → @Monic (C^op) y x f)
  := (Epic_of_op_Monic f, op_Monic_of_Epic f).

Section Bridges.

Context {C : Category}.
Context {x y : C}.

(*
The two projections, named.  The other two bridges of
   Theory/Morphisms/Duality.v go the other way round the square --
   [Monic_of_op_Epic] turns an [Epic] of C^op into a [Monic] of C
   and [op_Epic_of_Monic] turns a [Monic] of C into an [Epic] of
   C^op -- which is what makes [QuotObj_op_is_SubObj] a genuine
   identification rather than a one-way reading: the monicity witness a
   subobject of C carries is exactly the epicness witness a quotient
   object of C^op carries.

--------
这两个投影，被命名为。Theory/Morphisms/Duality.v 的另外两座桥则沿着方形的另一方向——[Monic_of_op_Epic] 将 C^op 的 [Epic] 转换为 C 的 [Monic]，而 [op_Epic_of_Monic] 将 C 的 [Monic] 转换为 C^op 的 [Epic]——这正是使 [QuotObj_op_is_SubObj] 成为真正的恒等而不是单向理解的原因：C 的子对象所携带的单象性正是 C^op 的商对象所携带的满象性。
*)
Definition epic_of_monic_op (f : x ~> y) : @Monic (C^op) y x f → @Epic C x y f
  := fst (monic_op_iff_epic f).

Definition monic_op_of_epic (f : x ~> y) : @Epic C x y f → @Monic (C^op) y x f
  := snd (monic_op_iff_epic f).

End Bridges.

(** ** The top quotient: x by the identity / ** 顶部商：x 乘以恒等式 *)

Section QuotientTop.

Context {C : Category}.
Context {x : C}.

(*
[sub_top] at C^op.  It is the FINEST quotient of x, and the greatest
   element of [quot_le]: every quotient of x factors through it.

--------
[sub_top] 在 C^op。它是 x 的最优商，也是 [quot_le] 中最大的元素：x 的每个商都通过它分解。
*)
Definition quot_top : QuotObj x := @sub_top (C^op) x.

Example quot_top_cod : quot_cod quot_top = x := eq_refl.
Example quot_top_epi : quot_epi quot_top = @id C x := eq_refl.

Definition quot_top_greatest (q : QuotObj x) : quot_le q quot_top :=
  @sub_top_greatest (C^op) x q.

End QuotientTop.

(** ** The lattice of quotient objects, by transport of the subobject one / ** 商对象的格，通过子对象的传递 *)

Section QuotientMeet.

Context {C : Category}.
Context `{HP : @HasPushouts C}.
Context {x : C}.

(*
The pushout of two epis, read as a quotient object: the meet for
   [quot_le] -- the greatest lower bound, the finest quotient that
   factors through both (the interface stub's gloss had the direction of
   “factors through” backwards; corrected at integration).

--------
两个射满的推挤，读作商对象：[quot_le] 的交 -- 最大下界，通过两个都因子的最细商（接口存根的注释中“通过因子”的方向反了；在集成时已更正）。
*)
Definition quot_meet (q r : QuotObj x) : QuotObj x :=
  @sub_meet (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r.

End QuotientMeet.

(** *** The meet laws, all instantiated at C^op / *** 相会律，全都在 C^op 中实例化 *)

Section QuotientMeetLaws.

Context {C : Category}.
Context `{HP : @HasPushouts C}.
Context {x : C}.

(* Below both factors: the two pushout injections, read backwards. / 下面的两个因素：两个推挤注入，倒着读。 *)
Definition quot_meet_le_l (q r : QuotObj x) : quot_le (quot_meet q r) q :=
  @sub_meet_le_l (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r.

Definition quot_meet_le_r (q r : QuotObj x) : quot_le (quot_meet q r) r :=
  @sub_meet_le_r (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r.

(*
Mac Lane §V.7 dualized: the pushout is the GREATEST quotient object
   below both, in the factorization order [quot_le] -- the finest
   quotient that factors through both q and r.  See the header on why a
   reader who orders by the size of the codomain reads this as a join.

--------
Mac Lane §V.7 对偶化：推出来是两个下面的最大商对象，在分解顺序 [quot_le] 中——通过 q 和 r 的最精细商。参见标题，了解为什么一个根据到值域大小排序的读者会将其视为并。
*)
Definition quot_meet_is_glb (q r : QuotObj x) :
  ∀ w : QuotObj x, quot_le w q → quot_le w r → quot_le w (quot_meet q r) :=
  @sub_meet_is_glb (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r.

(*
The order-theoretic predicate transports unchanged: [IsMeet] at C^op
   is the two-element case of [IsIntersection], whose two clauses are
   stated with [sub_le], which at C^op is [quot_le] on the nose.

--------
序理论谓词保持不变地传递：[IsMeet] 在 C^op 上是 [IsIntersection] 的双元素情况，其两个条款用 [sub_le] 表示，在 C^op 上正是 [quot_le]。
*)
Definition quot_meet_IsMeet (q r : QuotObj x) :
  @IsMeet (C^op) x q r (quot_meet q r) :=
  @sub_meet_IsMeet (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r.

#[export] Instance quot_meet_respects :
  Proper (equiv ==> equiv ==> equiv) (@quot_meet C HP x) :=
  @sub_meet_respects (C^op) (HasPullbacks_op_of_HasPushouts HP) x.

Definition quot_meet_comm (q r : QuotObj x) : quot_meet q r ≈ quot_meet r q :=
  @sub_meet_comm (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r.

Definition quot_meet_assoc (q r s : QuotObj x) :
  quot_meet (quot_meet q r) s ≈ quot_meet q (quot_meet r s) :=
  @sub_meet_assoc (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r s.

Definition quot_meet_idem (q : QuotObj x) : quot_meet q q ≈ q :=
  @sub_meet_idem (C^op) (HasPullbacks_op_of_HasPushouts HP) x q.

(* The identity quotient is a unit for the meet. / 同一商是会面的一个单位。 *)
Definition quot_meet_top (q : QuotObj x) : quot_meet q quot_top ≈ q :=
  @sub_meet_top (C^op) (HasPullbacks_op_of_HasPushouts HP) x q.

(*
“q ≤ r iff q ∧ r ≈ q”, in two lemmas: [quot_le] is Type-valued data
   and the two directions carry different data.

--------
“q ≤ r 当且仅当 q ∧ r ≈ q”，在两个引理中：[quot_le] 是类型值数据，并且两个方向携带不同的数据。
*)
Definition quot_meet_of_le (q r : QuotObj x) :
  quot_le q r → quot_meet q r ≈ q :=
  @sub_meet_of_le (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r.

Definition quot_le_of_meet (q r : QuotObj x) :
  quot_meet q r ≈ q → quot_le q r :=
  @sub_le_of_meet (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r.

End QuotientMeetLaws.

(** *** The bottom quotient, under an epic arrow to the terminal object / *** 底部商，在指向终端对象的史诗箭头下 *)

Section QuotientBottom.

Context {C : Category}.
Context `{T : @Terminal C}.
Context {x : C}.

(*
[sub_bot] at C^op.  Structure/Initial.v makes [Initial (C^op)] the
   same thing as [Terminal C], and [sub_bot]'s hypothesis [Monic zero]
   becomes [Epic (one : x ~> 1)] through [op_Monic_of_Epic].  The
   hypothesis is REAL but OBJECT-DEPENDENT rather than rare, and it is
   left standing here only because this file builds no witness: in
   [Sets] the arrow x → 1 is epic at every INHABITED x and is NOT epic
   at the empty setoid (two maps 1 → Y agree after ∅ → 1 for free), and
   Instance/Sets/QuotObj.v carries both halves -- the three-line
   [Sets_one_epic_of_inhabited], whence the bottom quotient object
   [Sets_quot_bot] at every inhabited setoid, and the refutation
   [Sets_one_not_epic_empty].  The same inhabited/empty split governs
   [Grp], [Ab] and [Top], while in a thin category every arrow is epic.
   An earlier revision of this paragraph said “in most categories the
   arrow to the terminal object is not epic”, which an audit refuted by
   discharging the hypothesis at [Sets] on [bool]; a second revision
   said the discharge “lives with the witnesses” before any had been
   landed, which a second audit caught.

--------
[sub_bot] 位于 C^op。 Structure/Initial.v 使 [Initial (C^op)] 成为
 与 [Terminal C] 相同，以及 [sub_bot] 的假设 [Monic zero]
 通过 [op_Monic_of_Epic] 变为 [Epic (one : x ~> 1)]。 的
 假设是真实的，但依赖于对象而不是罕见的，而且它是
 留在这儿只是因为这个文件没有建立见证：
 [Sets] 箭头 x → 1 在每个 INHABITED x 处都是史诗级的，但不是史诗级的
 在空 setoid 处（两个映射 1 → Y 在 ∅ → 1 后一致），并且
 Instance/Sets/QuotObj.v 包含两半——三行
 [Sets_one_epic_of_inhabited]，由此而来的底部商对象
 [Sets_quot_bot] 在每个有人居住的集合体上，以及反驳
 [Sets_one_not_epic_empty]。 相同的有人居住/无人居住的分割管辖
 [Grp]、[Ab] 和 [Top]，虽然在薄型范畴中，每支箭头都是史诗般的。 
本段的较早修订版表示“在大多数范畴中
 指向终端对象的箭头不是史诗”，审计驳斥了这一点
 在 [bool] 上解除 [Sets] 的假设； 第二次修订
 说在任何事件发生之前，这次放电“与目击者一起生活”
 着陆，第二次审计发现了这一点。
*)
Definition quot_bot (He : Epic (@one C T x)) : QuotObj x :=
  @sub_bot (C^op) T x (op_Monic_of_Epic (@one C T x) He).

(* The coarsest quotient: every quotient object of x sits above it. / 最粗的商：x 的每个商对象都坐落在它之上。 *)
Definition quot_bot_least (He : Epic (@one C T x)) (q : QuotObj x) :
  quot_le (quot_bot He) q :=
  @sub_bot_least (C^op) T x (op_Monic_of_Epic (@one C T x) He) q.

(*
The formal dual of [zero_monic_of_strict] (Theory/Subobject/
   Lattice.v) at C^op, recorded for SYMMETRY ONLY: its strict-
   initial hypothesis reads here as a COSTRICT terminal object -- every
   object receiving a map from 1 is isomorphic to 1 -- which is a
   near-vacuous condition: it does not hold in [Sets] (1 → bool exists
   and bool is not 1) and in any category with a zero object it forces every
   object to be terminal, so it is satisfied essentially only by the
   trivial category.  It is NOT the practical route to [Epic one]; that
   route is the object-by-object one described above (inhabitedness at
   [Sets]).  The isomorphism is supplied in C and carried over by
   [op_Iso_of_Iso]; no category in this tree is shown to satisfy the
   hypothesis, and none should be expected to.

--------
[zero_monic_of_strict]（Theory/Subobject/Lattice.v）在 C^op 下的形式对偶，仅为对称性而记录：其严格的初始假设在这里被读作一个余限制终对象——每个接受来自 1 的映射的对象都与 1 同构——这是一个几乎空洞的条件：它在 [Sets]（1 → bool 存在且 bool 不为 1）中不成立，并且在任何具有零对象的范畴中它会强制每个对象都是终对象，因此它基本上只为平凡范畴所满足。它不是通向 [Epic one] 的实际路径；通向该点的路径是上文描述的逐对象方法（在 [Sets] 的可存在性）。同构在 C 中提供，并通过 [op_Iso_of_Iso] 传递；在这个树中的任何范畴都没有显示满足假设，也不应被期望满足。
*)
Definition one_epic_of_costrict
  (Hco : ∀ (y : C) (f : @terminal_obj C T ~> y),
           @terminal_obj C T ≅[C] y) :
  Epic (@one C T x) :=
  Epic_of_op_Monic (@one C T x)
    (@zero_monic_of_strict (C^op) T x
       (fun y f => op_Iso_of_Iso (Hco y f))).

End QuotientBottom.

(** *** Wide meets, over a wide pullback of C^op / *** 广泛的会面，超过C^op的广泛回撤 *)

Section QuotientWideMeet.

Context {C : Category}.
Context {x : C}.
Context {J : Type}.
Context (S : J → QuotObj x).

(*
[sub_wide_intersection] at C^op.  The [WidePullback] argument is a
   wide pullback IN C^op, which is a wide pushout of C; Structure/
   Pullback/Wide.v supplies no wide-pushout vocabulary and none is added
   here, so the caller states it in the C^op spelling.  The index [j0]
   survives the transport for the reason recorded in the subobject
   file's header: the wide record carries no leg to the common
   codomain, so the epi into the apex is read off a chosen member.

--------
C^op 中的 [sub_wide_intersection]。[WidePullback] 参数是 C^op 中的广拉回，它是 C 的广推挤；Structure/Pullback/Wide.v 不提供广推挤词汇，这里也没有添加，因此调用者以 C^op 拼写来声明它。索引 [j0] 在传输中保留，原因记录在子对象文件的头部：广记录没有到公共余域的分支，因此到顶点的满射是从选定的成员中读取的。
*)
Definition quot_wide_meet (j0 : J)
  (W : @WidePullback (C^op) J (fun j => quot_cod (S j)) x
         (fun j => quot_epi (S j))) : QuotObj x :=
  @sub_wide_intersection (C^op) x J S j0 W.

Definition quot_wide_meet_IsIntersection (j0 : J)
  (W : @WidePullback (C^op) J (fun j => quot_cod (S j)) x
         (fun j => quot_epi (S j))) :
  @IsIntersection (C^op) x J S (quot_wide_meet j0 W) :=
  @sub_wide_intersection_IsIntersection (C^op) x J S j0 W.

Definition quot_wide_meet_index_irrelevant (j0 j1 : J)
  (W : @WidePullback (C^op) J (fun j => quot_cod (S j)) x
         (fun j => quot_epi (S j))) :
  quot_wide_meet j0 W ≈ quot_wide_meet j1 W :=
  @sub_wide_intersection_index_irrelevant (C^op) x J S j0 j1 W.

End QuotientWideMeet.

(** ** Coimages, and joins by coimage of the pairing / ** 余像，以及通过配对的余像进行的连接 *)

Section Coimages.

Context {C : Category}.

(*
An image of C^op, read forwards: the coarsest quotient of x through
   which f factors.  Its fields read [im_sub : QuotObj x],
   [im_factor : quot_cod im_sub ~> y] with
   [im_factor ∘[C] quot_epi im_sub ≈ f] -- the composition MUST be
   annotated with C, for the same reason as in [quot_equiv_unfold]:
   written bare, [∘] is elaborated in C^op from [im_factor]'s spelled
   type and the sentence does not typecheck -- and [im_least] saying
   that any quotient w of x with [g ∘[C] quot_epi w ≈ f] satisfies
   [quot_le im_sub w].

--------
C^op 的像，正读为：x 的最粗商，使得 f 可以通过它分解。它的字段读作 [im_sub : QuotObj x]、[im_factor : quot_cod im_sub ~> y]，带有 [im_factor ∘[C] quot_epi im_sub ≈ f] —— 构成必须用 C 注释，原因同 [quot_equiv_unfold]：若裸写，[∘] 会根据 [im_factor] 拼写的类型在 C^op 中被展开，并且该句不能类型检查 —— 以及 [im_least] 表明任意 x 的商 w，满足 [g ∘[C] quot_epi w ≈ f]，都满足 [quot_le im_sub w]。
*)
Definition CoimageOf {x y : C} (f : x ~> y) : Type := @ImageOf (C^op) y x f.

End Coimages.

(*
Following the [Cocartesian] (Structure/Cocartesian.v) and
   [Initial] (Structure/Initial.v) precedent, this is NOTATION rather
   than a definition, so that instance resolution for the underlying
   [HasImages] class still fires at C^op.

--------
遵循 [Cocartesian]（Structure/Cocartesian.v）和 [Initial]（Structure/Initial.v）的先例，这是一种记号而不是定义，因此底层 [HasImages] 类的实例解析仍会在 C^op 上触发。
*)
Notation "'HasCoimages' C" := (@HasImages (C^op))
  (at level 9) : category_theory_scope.
Notation "@HasCoimages C" := (@HasImages (C^op))
  (at level 9) : category_theory_scope.

Section QuotientJoin.

Context {C : Category}.
Context `{CC : @Cartesian C}.
Context {x : C}.

(*
The copairing of C^op is the pairing of C.  Spelling it in C is what
   makes [CoimageOf] below pick the right category (see the header).

--------
C^op 的对偶配对是 C 的配对。在 C 中拼写它是使下面的 [CoimageOf] 选择正确范畴的原因（见标题）。
*)
Definition quot_pairing (q r : QuotObj x) :
  x ~{C}~> @product_obj C CC (quot_cod q) (quot_cod r) :=
  @fork C CC x (quot_cod q) (quot_cod r) (quot_epi q) (quot_epi r).

(*
The join of two quotient objects: the coimage of the pairing of their
   epis into the product of their codomains, given such a coimage.

--------
两个商对象的并：它们的满射对映入其余域的积中的共像，给定这样的共像。
*)
Definition quot_join_via (q r : QuotObj x)
  (I : CoimageOf (quot_pairing q r)) : QuotObj x :=
  @sub_join_via (C^op) CC x q r I.

Definition quot_join_via_le_l (q r : QuotObj x)
  (I : CoimageOf (quot_pairing q r)) :
  quot_le q (quot_join_via q r I) :=
  @sub_join_via_le_l (C^op) CC x q r I.

Definition quot_join_via_le_r (q r : QuotObj x)
  (I : CoimageOf (quot_pairing q r)) :
  quot_le r (quot_join_via q r I) :=
  @sub_join_via_le_r (C^op) CC x q r I.

(* The coimage is the LEAST quotient object above both. / 共像是位于两者之上的最小商对象。 *)
Definition quot_join_via_is_lub (q r : QuotObj x)
  (I : CoimageOf (quot_pairing q r)) (w : QuotObj x) :
  quot_le q w → quot_le r w → quot_le (quot_join_via q r I) w :=
  @sub_join_via_is_lub (C^op) CC x q r I w.

Definition quot_join_via_IsJoin (q r : QuotObj x)
  (I : CoimageOf (quot_pairing q r)) :
  @IsJoin (C^op) x q r (quot_join_via q r I) :=
  @sub_join_via_IsJoin (C^op) CC x q r I.

End QuotientJoin.

(** *** The join as a lattice operation, with coimages chosen / *** 作为格运算的join，选择了共像 *)

Section QuotientJoinLattice.

Context {C : Category}.
Context `{CC : @Cartesian C}.
Context `{HI : @HasCoimages C}.
Context {x : C}.

Definition quot_join (q r : QuotObj x) : QuotObj x :=
  @sub_join (C^op) CC x HI q r.

Definition quot_join_le_l (q r : QuotObj x) : quot_le q (quot_join q r) :=
  @sub_join_le_l (C^op) CC HI x q r.

Definition quot_join_le_r (q r : QuotObj x) : quot_le r (quot_join q r) :=
  @sub_join_le_r (C^op) CC HI x q r.

Definition quot_join_is_lub (q r : QuotObj x) :
  ∀ w : QuotObj x, quot_le q w → quot_le r w → quot_le (quot_join q r) w :=
  @sub_join_is_lub (C^op) CC HI x q r.

Definition quot_join_IsJoin (q r : QuotObj x) :
  @IsJoin (C^op) x q r (quot_join q r) :=
  @sub_join_IsJoin (C^op) CC HI x q r.

#[export] Instance quot_join_respects :
  Proper (equiv ==> equiv ==> equiv) quot_join :=
  @sub_join_respects (C^op) CC HI x.

Definition quot_join_comm (q r : QuotObj x) : quot_join q r ≈ quot_join r q :=
  @sub_join_comm (C^op) CC HI x q r.

Definition quot_join_assoc (q r s : QuotObj x) :
  quot_join (quot_join q r) s ≈ quot_join q (quot_join r s) :=
  @sub_join_assoc (C^op) CC HI x q r s.

Definition quot_join_idem (q : QuotObj x) : quot_join q q ≈ q :=
  @sub_join_idem (C^op) CC HI x q.

Definition quot_join_of_le (q r : QuotObj x) :
  quot_le q r → quot_join q r ≈ r :=
  @sub_join_of_le (C^op) CC HI x q r.

Definition quot_le_of_join (q r : QuotObj x) :
  quot_join q r ≈ r → quot_le q r :=
  @sub_le_of_join (C^op) CC HI x q r.

End QuotientJoinLattice.

(** *** Absorption: the two operations make a lattice on the setoid / *** 吸收：这两个运算在集合等价类上构成一个格 *)

Section QuotientAbsorption.

Context {C : Category}.
Context `{HP : @HasPushouts C}.
Context `{CC : @Cartesian C}.
Context `{HI : @HasCoimages C}.
Context {x : C}.

Definition quot_meet_absorb (q r : QuotObj x) :
  quot_meet q (quot_join q r) ≈ q :=
  @sub_meet_absorb (C^op) (HasPullbacks_op_of_HasPushouts HP) CC HI x q r.

Definition quot_join_absorb (q r : QuotObj x) :
  quot_join q (quot_meet q r) ≈ q :=
  @sub_join_absorb (C^op) (HasPullbacks_op_of_HasPushouts HP) CC HI x q r.

End QuotientAbsorption.
