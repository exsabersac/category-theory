Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Classes.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Orthogonality.
Require Import Category.Theory.Subobject.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.BiCCC.
Require Import Category.Structure.Factorization.
Require Import Category.Structure.Regular.
Require Import Category.Structure.Regular.Factorization.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.Limit.Coproduct.

Generalizable All Variables.

(*
The lattice of subobjects of an object

   nLab:  https://ncatlab.org/nlab/show/subobject
   nLab:  https://ncatlab.org/nlab/show/image
   nLab:  https://ncatlab.org/nlab/show/wide+pullback
   nLab:  https://ncatlab.org/nlab/show/well-powered+category

   A subobject of x is a monomorphism into x taken up to the equivalence
   that identifies two monos when each factors through the other.
   Theory/Subobject.v carries that data as [SubObj x] and that order as
   [sub_le] (Theory/Subobject.v), a preorder whose mediating arrow is
   itself monic and unique, and whose induced equivalence is
   exactly the setoid on [SubObj x] ([sub_equiv_iff_mutual]).  What
   that file leaves open, and what this one supplies, is the ORDER
   STRUCTURE of that preorder: binary and indexed greatest lower bounds,
   binary and indexed least upper bounds, and the two end points.

   Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
   §V.7, book p. 126 (PDF p. 135), is the source the construction follows.
   Mac Lane observes that a pullback of two monos u : s ↣ x and v : t ↣ x
   is again a pair of monos, and that the composite of either pullback leg
   with the mono below it presents the apex as a subobject of x which is
   contained in both and contains every subobject contained in both: the
   intersection u ∩ v, the greatest lower bound in the factorization
   order.  [sub_meet] below is that composite verbatim, and
   [sub_meet_is_glb] is that greatest-lower-bound claim.  A wide pullback
   of a whole family of monos plays the same role for an indexed
   intersection.  Unions are NOT dual to this in the elementary sense: a
   pushout of two monos is not in general a subobject of x at all, and the
   join has to be built as the IMAGE of the copairing of the two monos out
   of their coproduct.  That is why the join half of this file is
   conditional on an image factorization where the meet half is
   conditional only on pullbacks.

   Riehl, "Category Theory in Context", 2nd ed., §4.7, printed p. 177
   (PDF p. 197), Definition 4.7.9, gives the indexed form.  Riehl defines
   the intersection of a family of subobjects as the LIMIT of the diagram
   consisting of those monomorphisms over their common codomain, and then
   records three facts about it: the legs of the limit cone are monic, the
   induced map from the limit object down to the codomain is monic, and
   the resulting subobject is maximal among the subobjects contained in
   every member of the family.  All three appear below over the
   ELEMENTARY presentation of that limit, the wide pullback of
   Structure/Pullback/Wide.v: the legs are monic by
   [wide_pullback_proj_monic], the induced map is monic by the
   [sub_is_monic] field of [sub_wide_intersection], and maximality is
   [inter_greatest] in [sub_wide_intersection_IsIntersection].

   Fong and Spivak, "Seven Sketches in Compositionality", §1.2.1, printed
   p. 8 (PDF p. 20), meets the same two operations at their most concrete:
   the union and the intersection of subsets of one ambient set, and the
   indexed versions of both over a family.  The unit law they record for
   the union, ∅ ∪ X ≅ X, is [sub_join_bot] below (and [sub_join_via_bot],
   the same law with the image of the copairing handed in), at the level of
   subobjects of an arbitrary object rather than of subsets; its
   intersection counterpart ∅ ∩ X ≅ ∅ is [sub_meet_bot], and the two
   absorption laws that make the pair a lattice are [sub_meet_absorb] and
   [sub_join_absorb].  The merging-versus-tagging contrast that the book
   draws in the same section -- that the union of two subsets of a common
   set merges their overlap where the coproduct tags it -- is exactly the
   distance between [sub_join_via u v I], the image of the copairing, and
   the coproduct [sub_dom u + sub_dom v] it is the image OF.

   In-tree connections, each checked in this worktree.

   The order.  Theory/Subobject.v carries [sub_le], [sub_le_monic],
   [sub_le_unique] and [sub_equiv_iff_mutual]; every antisymmetry
   step below goes through that last one, because [sub_le] is Type-valued
   and the equivalence it induces is the [SubObj] setoid, not Leibniz
   equality.  Note the consequence for how the lattice laws are phrased:
   [SubObj x] is a PREORDER whose setoid identifies mutually-factoring
   subobjects, so the commutativity, associativity, idempotence and
   absorption laws below hold at ≈ and are a lattice ON THAT SETOID, not a
   poset with antisymmetry for Leibniz equality.

   The meet.  Structure/Pullback.v is [HasPullbacks], the chosen-
   pullback class this file's meet is relative to, and
   Theory/Morphisms/Stability.v is [monic_pullback_stable], which is
   what makes the opposite leg monic.  Theory/Subobject/Functor.v is
   [sub_reindex], which packages that same pulled-back leg as a subobject
   of [sub_dom u]; the identification is on the nose, [sub_meet u v] being
   literally [sub_compose u (sub_reindex (sub_mono u) v)] -- the same
   record with the same three fields, including the same [monic_compose]
   proof term.  That is MEASURED, not asserted: with
   Category.Theory.Subobject.Functor added to the requirement list, the
   statement
     [Example e (u v : SubObj x) :
        sub_meet u v = sub_compose u (sub_reindex (sub_mono u) v)
        := eq_refl.]
   compiles, at Leibniz equality and with no tactic -- the one place in
   this development where Leibniz equality is the right relation, because
   the claim is about the DATA of the record and not about its morphism.
   That identification is NOT stated in this file, and the reason is
   NAMESPACE, not cost.  An earlier revision of this paragraph said the
   require was avoided because Theory/Subobject/Functor.v pulls
   Category.Instance.Sets; MEASURED by iterating coqdep to a fixed point,
   that is false as a saving -- this file's own closure (48 files) ALREADY
   contains Instance/Sets.v, through Structure/BiCCC.v,
   Structure/Regular/Factorization.v, Structure/Limit/Coproduct.v and
   Structure/Cartesian/Closed.v, so requiring Functor.v would add exactly
   ONE file.  What the require would add is Functor.v's presheaf [Sub] and
   its reindexing vocabulary alongside the order vocabulary here, and the
   readback is placed in Test/ProbeSubobjectLattice445.v
   ([p445_meet_is_compose_reindex]) by that choice.  The literal Require
   list of this file is instance-free; its closure is not.

   The wide intersection.  Structure/Pullback/Wide.v carries
   [IsWidePullback], the chosen form [WidePullback],
   [HasWidePullbacks], and [wide_pullback_jointly_monic], the joint
   monicity of the projections that [wide_pullback_proj_monic] below turns
   into monicity of each single projection.  One feature of that file
   governs the shape of the interface here: the record carries NO leg to
   the common codomain, so over an empty index it constrains nothing and
   the wide pullback is the TERMINAL object
   ([wide_pullback_empty_terminal], with the converse beside it).  A terminal
   object is not the top subobject, so [sub_wide_intersection] takes an
   index [j0 : J] and reads the mono into x off the j0-th member.  At
   every nonempty index Riehl's limit-over-the-cospan-shape reading and
   this one agree -- the cospan shape has the codomain as an object, and
   its limit leg to the codomain is the composite this file writes by hand
   -- and they differ only at the empty index, where the intersection of
   the empty family of subobjects is [sub_top] ([IsIntersection_empty]
   below) rather than a terminal object.  Structure/Pullback/Wide.v is
   [binary_wide_pullback]; the binary-from-wide comparison below does not
   route through it, for the reason recorded at that lemma.

   The join.  Structure/Cocartesian.v carries [inl_merge] and
   [inr_merge], the two triangles that put each of u and v below the
   image; Structure/Limit/Coproduct.v carries [IsIndexedCoproduct]
   and [icoprod_desc], the indexed replacements for them.
   Structure/Factorization.v carries [Factorization] and [OFS]; an
   (E, Mono) factorization system is precisely a supply of images in the
   sense of the [ImageOf] record below, and [ImageOf_of_OFS] is that
   translation, its minimality clause being the diagonal filler of
   Theory/Orthogonality.v ([Orthogonal], whose [ortho_lift] field
   returns the filler as data).  Theory/Morphisms/Classes.v is
   [MonoClass], which is [fun _ _ f => Monic f] and so matches the
   [sub_is_monic] field with no transport.  Structure/Regular/
   Factorization.v carries [Regular_OFS], the (regular epi, mono) system
   of a regular category, with [image_comparison_monic] as its mono leg;
   [Regular_HasImages] below is [HasImages_of_OFS] applied to it.  That
   corollary is CONDITIONAL and stays so: no [Regular] instance exists
   anywhere in this tree, as Instance/Sets/Pullback.v records in terms
   ("a class with no instance anywhere"), and this file adds none.

   The powerset analogue.  Instance/Powerset.v carries
   [subset_inter] and [subset_union], the predicate-level meet and join of
   a family of subsets of a setoid, with their universal properties
   [subset_inter_IsGLB] and [subset_union_IsLUB].  This
   file is the SubObj-level analogue of that
   pair in an arbitrary category: the same two universal properties, with
   the powerset's pointwise ∀ and ∃ replaced by a wide pullback and an
   image.  (An earlier revision of this header's source instructions gave
   the wrong locations for those two definitions; they were re-measured
   in this worktree with
   grep -n '^Definition subset_inter\|^Definition subset_union'.)

   Where this does NOT go.  Adjunction/SAFT.v packages the
   well-poweredness the special adjoint functor theorem consumes as
   [SubobjectIndex], and builds [SubobjectCover] over it.  Feeding
   the intersections constructed here into that hypothesis list is issue
   #448 and is not attempted in this file; nothing below mentions SAFT,
   and no constant here is named by that development.  (CORRECTION,
   #451: [SubobjectIndex] is not the well-poweredness SAFT consumes in
   the classical theorem -- it has no exhaustiveness clause, and
   Adjunction/SAFT.v's [empty_SubobjectIndex] inhabits it at every
   object; well-poweredness is Structure/WellPowered.v's [WellPowered].
   Nor does [SAFT]'s hypothesis list contain an intersection hypothesis
   to feed: its premises are completeness, cone-level preservation, a
   cogenerating family, the index and the covering datum
   [SubobjectCover].)

   UNIVERSES, measured with [Set Printing Universes. About ...] rather than
   read off the source, which carries no annotation.  Every constant below
   binds its category as [Category@{u u0 u0}] -- the hom universe IDENTIFIED
   with the proof universe.  That collapse is INHERITED, not introduced
   here: Theory/Subobject.v's [SubObj] record itself prints as
   [SubObj@{u u0} : ∀ {C : Category@{u u0 u0}}, obj[C] → Type@{max(u,u0)}],
   because one record holds both the mono (at the hom level) and its
   [Monic] proof (at the proof level) under two universe variables, and
   [sub_le@{o h p u}] carries the block [h <= p, h <= u, h = p].
   So the collapse belongs to the FIRST carrier in dependency order,
   Theory/Subobject.v, and every file consuming [SubObj] -- this one,
   Theory/Subobject/Functor.v ([sub_reindex@{u u0}]), and the witnesses in
   Instance/ -- inherits it.  No constant here pins any universe to [Set],
   and none carries a constraint of its own beyond the stdlib
   [prod_rect]/[projections] bounds that come with sigma types.

   NOT DELIVERED.  No distributivity, and no Heyting or Boolean
   structure: the two absorption laws are proved, the distributive law
   relating meet and join is neither proved nor stated, and there is no
   complement, no implication and no negation on [SubObj x].  No
   antisymmetry: every lattice law holds at ≈ and none at Leibniz
   equality, as explained above.  No concrete inhabitant of any of the
   three hypotheses -- this file has no [HasPullbacks], [HasWidePullbacks]
   or [HasImages] instance for any category, and [Regular_HasImages]
   rests on a class with no instance in tree; the whole development is a
   conditional over structure supplied from outside, and docs/
   INHABITATION.md is where the question of which witnesses exist is
   settled.  No limit presentation: [IsIntersection] is a greatest lower
   bound in the factorization preorder, not a limit cone over a shape
   category, and Structure/Pullback/Wide.v carries no limit presentation
   either (its own header says so), so Riehl's Definition
   4.7.9 is matched in content and not by a literal [Limit] of a diagram.
   No indexed join over an arbitrary family without an indexed coproduct:
   [sub_wide_join_via] takes the coproduct and the image as arguments and
   nothing here manufactures either.  No union of the empty family without
   an initial object: the empty intersection is [sub_top] unconditionally,
   but its dual needs a least subobject and is therefore stated in the
   Bottom section against [sub_bot].  No functoriality: that reindexing
   along a morphism preserves binary meets belongs to a separate file and
   none is added alongside this one, so neither that statement nor any
   naturality, Galois connection or adjointness claim about reindexing
   appears anywhere in this development.  No computation: no [eq_refl]
   readback of any
   construction at any concrete category, and no enumeration of the Seven
   Sketches examples -- the four-versus-five element contrast, the
   increasing family and its union, and the finite arithmetic -- all of
   which need a concrete model and belong with the witness half of the
   issue.  No strictness result in general: [zero_monic_of_strict] takes
   strictness of the initial object as a HYPOTHESIS and derives no
   instance of it; the one case where the hypothesis is discharged is the
   bicartesian closed one, [biccc_zero_monic] through
   Structure/BiCCC.v ([initial_strict]), and even there no initial
   object of any concrete bicartesian closed category is exhibited.

--------
对象的子对象的格子

nLab：https://ncatlab.org/nlab/show/subobject
 nLab：https://ncatlab.org/nlab/show/image
 nLab：https://ncatlab.org/nlab/show/wide+pullback
 nLab：https://ncatlab.org/nlab/show/well-powered+category

x 的子对象是 x 的单态性，达到等价
 当两个单声道互相影响时，它会识别出两个单声道。 
Theory/Subobject.v 将该数据作为 [SubObj x] 并将该顺序作为
 [sub_le] (Theory/Subobject.v)，一个预序，其中介箭头为
 本身是单调且唯一的，其诱导等价是
 与 [SubObj x] ([sub_equiv_iff_mutual]) 上的 setoid 完全相同。 什么
 该文件保持打开状态，而该文件提供的是订单
 该预序的结构：二进制和索引最大下界，
 二进制和索引最小上限，以及两个端点。

Mac Lane，“工作数学家的范畴”，第二版。 （GTM 5），
 §V.7，书页。 126（PDF 第 135 页）是构建所遵循的来源。 
Mac Lane 观察到两个单声道 u : s ↣ x 和 v : t ↣ x 的回调
 又是一对单声道，并且任一回拉腿的组合
 下面的单声道将顶点表示为 x 的子对象，即
 包含在两者中并且包含两者中包含的每个子对象：
 交集 u ∩ v，分解中的最大下界
 订单。 下面的 [sub_meet] 是逐字复合的，并且
 [sub_meet_is_glb] 是最大下限主张。 大幅回调
 整个单核细胞家族对于索引扮演着相同的角色
 交叉点。 从基本意义上来说，联合并不是对偶的：
 两个单声道的推出通常根本不是 x 的子对象，并且
 join 必须构建为两个单声道输出的配对图像
 他们的副产品。 这就是为什么这个文件的连接部分是
 以图像分解为条件，其中满足一半是
 仅以回调为条件。

Riehl，“语境中的范畴理论”，第二版，§4.7，印刷页。 177
 （PDF 第 197 页），定义 4.7.9 给出了索引形式。 里尔定义
 一系列子对象的交集作为图的 LIMIT
 由它们共同的共域上的单态性组成，然后
 记录了关于它的三个事实：极限锥体的腿是莫尼克的，
 从极限对象到共域的诱导映射是单调的，并且
 生成的子对象是包含在的子对象中最大的
 家庭的每一位成员。 所有三个都出现在下面
 该限制的基本介绍，广泛的回调
 Structure/Pullback/Wide.v：腿是单足的
 [wide_pullback_proj_monic]，诱导图是单调的
 [sub_wide_intersection] 的 [sub_is_monic] 域，最大值为
 [sub_wide_intersection_IsIntersection] 中的 [inter_greatest]。

Fong 和 Spivak，“组合性的七个草图”，§1.2.1，印刷版
 p。 8 (PDF p. 20)，满足最具体的相同两个操作：
 一个环境集的子集的并集和交集，以及
 一个家族中两者的索引版本。 他们记录的单位律
 并集 ∅ ∪ X ≅ X 是下面的 [sub_join_bot]（以及 [sub_join_via_bot]，
 与提交的配对图像相同的法律），在
 任意对象的子对象而不是子集； 它的
 交集对应 ∅ ∩ X ≅ ∅ 是 [sub_meet_bot]，并且两个
 使该对成为晶格的吸收定律是 [sub_meet_absorb] 和
 [sub_join_absorb]。 本书中的合并与标记对比
 在同一部分中绘制——公共的两个子集的并集
 集将它们的重叠部分合并到余积标记它的位置 - 正是
 [sub_join_via u v I]、配对图像和
 副产品 [sub_dom u + sub_dom v] 它是 OF 的图像。

树内连接，每个连接都在此工作树中签入。

订单。 Theory/Subobject.v 带有 [sub_le]、[sub_le_monic]、
 [sub_le_unique] 和 [sub_equiv_iff_mutual]； 每一个反对称性
 下面的步骤将完成最后一步，因为 [sub_le] 是类型值的
 它引起的等价物是 [SubObj] setoid，而不是 Leibniz
 平等。 请注意晶格定律的表达方式的结果：
 [SubObj x] 是一个 PREORDER，其 setoid 标识互因子
 子对象，因此交换性、结合性、幂等性和
 下面的吸收定律保持在 ≈ 并且是那个 SETOID 上的一个晶格，而不是一个
 莱布尼兹等式的反对称偏序集。

见面。 Structure/Pullback.v 是 [HasPullbacks]，所选择的-
 该文件的 meet 相对于回调类，并且
 Theory/Morphisms/Stability.v 是 [monic_pullback_stable]，即
 是什么让另一条腿成为莫尼克。 Theory/Subobject/Functor.v 是
 [sub_reindex]，它将相同的拉回腿打包为子对象
 [sub_dom u]； 标识位于鼻子上，[sub_meet u v] 是
 从字面上看 [sub_compose u (sub_reindex (sub_mono u) v)]——相同
 具有相同三个字段的记录，包括相同的[monic_compose]
 证明术语。
这是测量的，而不是断言的：
 Category.Theory.Subobject.Functor 添加到需求列表中，
 声明
 [示例 e (u v : SubObj x) ：
 sub_meet u v = sub_compose u (sub_reindex (sub_mono u) v)
 := eq_refl.]
 编译，在莱布尼兹平等且没有策略的情况下——其中的一个地方
 在这种发展中，莱布尼茨平等是正确的关系，因为
 该声明是关于记录的数据而不是关于它的态射。 该文件中未说明该标识，原因是
 命名空间，而不是成本。
本段的较早修订版表示
 require 被避免，因为 Theory/Subobject/Functor.v 拉
 范畴.实例.集; 通过将 coqdep 迭代到固定点来测量，
 这是错误的保存 - 该文件自己的闭包（48 个文件）已经
 包含 Instance/Sets.v，通过 Structure/BiCCC.v，
 Structure/Regular/Factorization.v、Structure/Limit/Coproduct.v 和
 Structure/Cartesian/Closed.v，因此需要 Functor.v 将精确相加
 一个文件。 需要添加的是 Functor.v 的 presheaf [Sub] 和
 它的重新索引词汇与此处的顺序词汇一起，以及
 回读放置在 Test/ProbeSubobjectLattice445.v 中
 ([p445_meet_is_compose_reindex]) 通过这个选择。 字面要求
 该文件的列表是与实例无关的； 它的关闭不是。

宽阔的十字路口。 结构/回调/Wide.v 携带
 [IsWidePullback]，所选形式[WidePullback]，
 [HasWidePullbacks] 和 [wide_pullback_jointly_monic]，联合
 [wide_pullback_proj_monic] 下面的投影的单调性
 转化为每个单一投影的单调性。 该文件的一项功能
 控制此处界面的形状：记录没有腿
 公共共域，因此在空索引上它不限制任何内容并且
 宽回调是 TERMINAL 对象
 （[wide_pullback_empty_terminal]，其旁边有相反的情况）。 一个终端
 对象不是顶级子对象，因此 [sub_wide_intersection] 采用
 索引 [j0 : J] 并将单声道读入第 j0 个成员的 x 中。
在
 每个非空索引 Riehl's limit-over-the-cospan-shape 读数和
 这个同意——cospan 形状将余域作为对象，并且
 它对共域的限制是该文件手动写入的组合
 -- 它们仅在空索引处不同，其中的交集
 子对象的空族是 [sub_top] ([IsIntersection_empty]
 如下）而不是终端对象。 结构/回调/Wide.v 是
 [binary_wide_pullback]； 下面的二进制范围比较不会
 通过它的路线，原因记录在该引理中。

加入。 Structure/Cocartesian.v 带有 [inl_merge] 和
 [inr_merge]，将 u 和 v 分别置于
 图像； Structure/Limit/Coproduct.v 带有 [IsIndexedCoproduct]
 和 [icoprod_desc]，它们的索引替代品。 
Structure/Factorization.v 携带 [Factorization] 和 [OFS]； 一个
 （E，Mono）分解系统正是提供了图像
 下面是[ImageOf]记录的意义，而[ImageOf_of_OFS]则是
 翻译，其最小子句是对角线填充
 Theory/Orthogonality.v（[Orthogonal]，其 [ortho_lift] 场
 返回填充符作为数据）。 理论/态射/类.v 是
 [MonoClass]，即 [fun _ _ f => Monic f]，因此与
 [sub_is_monic] 现场无传输。 结构/常规/
 Factorization.v 带有 [Regular_OFS]，（常规 Epi、Mono）系统
 常规范畴，以 [image_comparison_monic] 作为其单腿；
 下面的[Regular_HasImages]是[HasImages_of_OFS]的应用。 那
 推论是有条件的并且保持不变：不存在 [Regular] 实例
 此树中的任何位置，如 Instance/Sets/Pullback.v 中的记录
 （“一个在任何地方都没有实例的类”），并且该文件不添加任何实例。

powerset 类似物。 Instance/Powerset.v携带
 [subset_inter] 和 [subset_union]，谓词级满足和连接
 集合类的子集及其通用属性
 [subset_inter_IsGLB] 和 [subset_union_IsLUB]。 这个
 file 是 SubObj 级别的类似物
 任意范畴中的对：相同的两个通用属性，并且
 幂集的逐点 ∀ 和 ∃ 被宽回调和
 图像。 （此标头的源指令的早期修订版给出了
 这两个定义的位置错误； 他们被重新测量
 在此工作树中
 grep -n '^定义subset_inter\|^定义subset_union'。）

这不会去哪里。 Adjunction/SAFT.v 封装了
 特殊伴随定理的幂函数消耗为
 [SubobjectIndex]，并在其上构建 [SubobjectCover]。 喂养
 此处构建到该假设列表中的交叉点是问题
 #448 并且在此文件中未尝试； 下面没有提到 SAFT，
 这里没有任何常数是由这种发展命名的。 （更正，
 #451：[SubobjectIndex] 不是 SAFT 所消耗的强大功能
 经典定理——它没有穷举性子句，并且
 Adjunction/SAFT.v 的 [empty_SubobjectIndex] 经常驻留在其中
 对象； 动力良好的是 Structure/WellPowered.v 的 [WellPowered]。 
[SAFT] 的假设列表也不包含交叉假设
 喂养：其前提是完整性、锥体级保存、
 联产系列、索引和覆盖数据
 [SubobjectCover]。）

宇宙，使用 [Set Printing Universes. About ...] 测量，而不是
 读出没有注释的来源。 下面的每个常数
 将其范畴绑定为 [Category@{u u0 u0}]——已识别的 hom 宇宙
 与证明宇宙。 这种崩溃是继承的，而不是引入的
 此处：Theory/Subobject.v 的 [SubObj] 记录本身打印为
 [SubObj@{u u0} : ∀ {C : Category@{u u0 u0}}, obj[C] → 输入@{max(u,u0)}],
 因为一张唱片既包含单声道（在本音级别）又包含它的
 [Monic] 在两个宇宙变量下的证明（在证明级别），以及
 [sub_le@{o h p u}] 带有 [h <= p, h <= u, h = p] 模块。 
所以崩溃属于依存顺序中的第一个载体，
 Theory/Subobject.v，以及每个使用 [SubObj] 的文件——这个，
 Theory/Subobject/Functor.v ([sub_reindex@{u u0}])，以及见证者
 Instance/——继承它。 这里没有常数将任何宇宙固定到 [Set]，
 除了 stdlib 之外，没有一个具有自己的约束
 西格玛类型附带的 [prod_rect]/[projections] 界限。

未交付。 没有分配性，也没有 Heyting 或 Boolean
 结构：证明了两个吸收定律、分配定律
 关于 meet 和 join 既没有被证明也没有被陈述，并且没有
 [SubObj x] 上是补语，没有暗示，也没有否定。 否
 反对称性：每个晶格定律在 ≈ 时都成立，而在莱布尼兹则不成立
 平等，如上所述。 没有任何具体居民
 三个假设——该文件没有 [HasPullbacks]、[HasWidePullbacks]
 或任何范畴的 [HasImages] 实例，以及 [Regular_HasImages]
 依赖于树中没有实例的类； 整个发展是一个
 对外部提供的结构有条件，并且 docs/
 INHABITATION.md 是存在哪些证人的问题所在
 解决了。
无限制展示：[IsIntersection]是最大的更低
 因式分解预序中的界限，而不是形状上的极限锥
 范畴，Structure/Pullback/Wide.v 没有限制呈现
 要么（它自己的标题这么说），所以 Riehl 的定义
 4.7.9 是在内容上匹配的，而不是通过图表的文字 [Limit] 匹配的。 没有索引余积的任意族上没有索引连接：
 [sub_wide_join_via] 将余积和图像作为参数，
 这里也不生产任何东西。 空虚的家庭没有结合就没有
 初始对象：空交集无条件是 [sub_top]，
 但它的对偶需要一个最小子对象，因此在
 底部部分与 [sub_bot] 相对应。
没有功能性：重新索引
 沿着态射保留二进制满足属于一个单独的文件并且
 没有与此一起添加，因此该声明或任何声明都没有添加
 关于重新索引的自然性、伽罗瓦联系或伴随性主张
 出现在这个发展的任何地方。 无计算：无 [eq_refl]
 任何的回读
 任何具体范畴的构建，并且没有列举七个
 草图示例——四对五元素对比、
 递增族及其并集，以及有限算术——所有这些
 这需要一个具体的模型，并且属于见证者的一半
 问题。
一般情况下没有严格的结果：[zero_monic_of_strict] 需要
 初始对象作为假设的严格性，并得出不
 它的实例； 假设成立的唯一一种情况是
 双笛卡尔闭式一、[biccc_zero_monic]直通
 Structure/BiCCC.v ([initial_strict])，甚至没有初始的
 展示任何具体的双笛卡尔封闭范畴的对象。
*)

(** ** The order-theoretic vocabulary / ** 序理论词汇 *)

Section SubobjectOrder.

Context {C : Category}.
Context {x : C}.

(* The top subobject: x itself along the identity. / 顶级子对象：沿着恒等映射的 x 本身。 *)
Definition sub_top : SubObj x := {|
  sub_dom := x;
  sub_mono := id;
  sub_is_monic := id_monic x
|}.

Lemma sub_top_greatest (u : SubObj x) : sub_le u sub_top.
Proof. exists (sub_mono u); cat. Defined.

(*
Riehl 4.7.9's characterization of the intersection of a family, and its
   dual: the greatest lower bound, respectively least upper bound, of the
   family for the factorization preorder [sub_le].

--------
Riehl 4.7.9 对一个族的交集及其对偶的描述：分别是该族在分解偏序 [sub_le] 下的最大下界和最小上界。
*)
Record IsIntersection {J : Type} (S : J → SubObj x) (w : SubObj x) := {
  inter_le : ∀ j, sub_le w (S j);
  inter_greatest : ∀ v : SubObj x, (∀ j, sub_le v (S j)) → sub_le v w
}.

Record IsUnion {J : Type} (S : J → SubObj x) (w : SubObj x) := {
  union_ge : ∀ j, sub_le (S j) w;
  union_least : ∀ v : SubObj x, (∀ j, sub_le (S j) v) → sub_le w v
}.

(* A two-element family, for the binary cases. / 一个二元家庭，适用于二元情况。 *)
Definition sub_pair (u v : SubObj x) : bool → SubObj x :=
  fun b => if b then u else v.

Definition IsMeet (u v w : SubObj x) : Type := IsIntersection (sub_pair u v) w.
Definition IsJoin (u v w : SubObj x) : Type := IsUnion (sub_pair u v) w.

(** *** Antisymmetry for the induced setoid / *** 归纳集合范畴的反对称性 *)

(*
The half of [sub_equiv_iff_mutual] used everywhere below: mutual
   factorization IS equivalence of subobjects.  [SubObj x] has no Leibniz
   antisymmetry; this is its replacement.

--------
下面到处使用的 [sub_equiv_iff_mutual] 的一半：互相分解等同于子对象的等价。[SubObj x] 没有莱布尼茨反对称性；这是它的替代品。
*)
Lemma sub_le_antisym (u v : SubObj x) : sub_le u v → sub_le v u → u ≈ v.
Proof.
  intros Huv Hvu.
  apply sub_equiv_iff_mutual.
  exact (Huv, Hvu).
Defined.

(*
... and the two projections of the other direction, as named lemmas, so
   that a transport along ≈ reads as one step.

--------
...以及另一个方向的两个投影，作为命名的引理，这样沿着≈的传输就可以读作一步。
*)
Lemma sub_le_of_equiv (u v : SubObj x) : u ≈ v → sub_le u v.
Proof. intros H; exact (fst (fst (sub_equiv_iff_mutual u v) H)). Defined.

Lemma sub_ge_of_equiv (u v : SubObj x) : u ≈ v → sub_le v u.
Proof. intros H; exact (snd (fst (sub_equiv_iff_mutual u v) H)). Defined.

(** *** Uniqueness and transport of the two universal properties / *** 两个普遍性质的独特性与传输 *)

(*
Two greatest lower bounds of the same family agree: each is below every
   member, so each factors through the other by the other's maximality.

--------
同一家族的两个最小上界是一致的：每一个都在每个成员之下，因此每一个都通过另一个的最大性来进行分解。
*)
Lemma IsIntersection_unique {J : Type} (S : J → SubObj x) (w w' : SubObj x) :
  IsIntersection S w → IsIntersection S w' → w ≈ w'.
Proof.
  intros A B.
  apply sub_le_antisym.
  - exact (inter_greatest S w' B w (inter_le S w A)).
  - exact (inter_greatest S w A w' (inter_le S w' B)).
Defined.

Lemma IsUnion_unique {J : Type} (S : J → SubObj x) (w w' : SubObj x) :
  IsUnion S w → IsUnion S w' → w ≈ w'.
Proof.
  intros A B.
  apply sub_le_antisym.
  - exact (union_least S w A w' (union_ge S w' B)).
  - exact (union_least S w' B w (union_ge S w A)).
Defined.

(* Being the intersection transports along ≈ of the bound ... / 作为约束的交汇沿着≈传输... *)
Lemma IsIntersection_respects_w {J : Type} (S : J → SubObj x)
  (w w' : SubObj x) : w ≈ w' → IsIntersection S w → IsIntersection S w'.
Proof.
  intros Hw A.
  constructor.
  - intro j.
    exact (sub_le_trans _ _ _ (sub_ge_of_equiv _ _ Hw) (inter_le S w A j)).
  - intros v Hv.
    exact (sub_le_trans _ _ _ (inter_greatest S w A v Hv)
             (sub_le_of_equiv _ _ Hw)).
Defined.

(* ... and pointwise along ≈ of the family. / ... 并且沿着该族的 ≈ 点对点地。 *)
Lemma IsIntersection_respects_family {J : Type} (S S' : J → SubObj x)
  (w : SubObj x) : (∀ j, S j ≈ S' j) →
  IsIntersection S w → IsIntersection S' w.
Proof.
  intros HS A.
  constructor.
  - intro j.
    exact (sub_le_trans _ _ _ (inter_le S w A j) (sub_le_of_equiv _ _ (HS j))).
  - intros v Hv.
    apply (inter_greatest S w A).
    intro j.
    exact (sub_le_trans _ _ _ (Hv j) (sub_ge_of_equiv _ _ (HS j))).
Defined.

Lemma IsUnion_respects_w {J : Type} (S : J → SubObj x) (w w' : SubObj x) :
  w ≈ w' → IsUnion S w → IsUnion S w'.
Proof.
  intros Hw A.
  constructor.
  - intro j.
    exact (sub_le_trans _ _ _ (union_ge S w A j) (sub_le_of_equiv _ _ Hw)).
  - intros v Hv.
    exact (sub_le_trans _ _ _ (sub_ge_of_equiv _ _ Hw)
             (union_least S w A v Hv)).
Defined.

Lemma IsUnion_respects_family {J : Type} (S S' : J → SubObj x) (w : SubObj x) :
  (∀ j, S j ≈ S' j) → IsUnion S w → IsUnion S' w.
Proof.
  intros HS A.
  constructor.
  - intro j.
    exact (sub_le_trans _ _ _ (sub_ge_of_equiv _ _ (HS j)) (union_ge S w A j)).
  - intros v Hv.
    apply (union_least S w A).
    intro j.
    exact (sub_le_trans _ _ _ (sub_le_of_equiv _ _ (HS j)) (Hv j)).
Defined.

(** *** The two degenerate index shapes / *** 两个退化的指标形状 *)

(*
Over an empty index every subobject is vacuously below every member, so
   the greatest lower bound is the greatest subobject.  This is the case
   at which the wide-pullback presentation of the intersection and the
   order-theoretic one part company: the empty wide pullback is a terminal
   object (Structure/Pullback/Wide.v), which is not [sub_top].

--------
在一个空索引下，每个子对象在逻辑上都位于每个成员之下，因此最下界是最大的子对象。这就是交集的宽拉回表示法和序理论表示法产生分歧的情况：空宽拉回是一个终对象（Structure/Pullback/Wide.v），它不是 [sub_top]。
*)
Lemma IsIntersection_empty {J : Type} (S : J → SubObj x) (Hempty : J → False) :
  IsIntersection S sub_top.
Proof.
  constructor.
  - intro j; destruct (Hempty j).
  - intros v _; exact (sub_top_greatest v).
Defined.

(*
Dually the union of the empty family is the LEAST subobject, which has
   to be supplied: nothing in the bare preorder produces one.  The Bottom
   section below instantiates [b] at [sub_bot].

--------
同样，空族的并集是最小子对象，必须提供：在裸序中没有任何东西能产生它。下面的 Bottom 部分在 [sub_bot] 上实例化 [b]。
*)
Lemma IsUnion_empty_of_least {J : Type} (S : J → SubObj x) (b : SubObj x)
  (Hleast : ∀ u : SubObj x, sub_le b u) (Hempty : J → False) :
  IsUnion S b.
Proof.
  constructor.
  - intro j; destruct (Hempty j).
  - intros v _; exact (Hleast v).
Defined.

(* A one-member family is its own bound, on both sides. / 一个单成员家庭是它自己的界限，在两边都是如此。 *)
Lemma IsIntersection_singleton (S : unit → SubObj x) :
  IsIntersection S (S tt).
Proof.
  constructor.
  - intro j; destruct j; exact (sub_le_refl _).
  - intros v Hv; exact (Hv tt).
Defined.

Lemma IsUnion_singleton (S : unit → SubObj x) : IsUnion S (S tt).
Proof.
  constructor.
  - intro j; destruct j; exact (sub_le_refl _).
  - intros v Hv; exact (Hv tt).
Defined.

End SubobjectOrder.

Arguments IsIntersection_unique {C x J} S {w w'} _ _.
Arguments IsUnion_unique {C x J} S {w w'} _ _.

(** ** Pushing a subobject forward along a mono / ** 沿着单声道向前推动子对象 *)

Section Compose.

Context {C : Category}.

(*
A subobject of the domain of a subobject is a subobject of the ambient
   object: monos compose.

--------
子对象的子对象是母对象的子对象：单射可以组合。
*)
Definition sub_compose {x : C} (u : SubObj x) (w : SubObj (sub_dom u)) :
  SubObj x := {|
  sub_dom := sub_dom w;
  sub_mono := sub_mono u ∘ sub_mono w;
  sub_is_monic := monic_compose (sub_is_monic u) (sub_is_monic w)
|}.

End Compose.

(** ** Binary meets by pullback / ** 二元在回撤时相遇 *)

Section Meet.

Context {C : Category}.
Context `{@HasPullbacks C}.
Context {x : C}.

(*
The intersection of two subobjects: the chosen pullback of their monos,
   mapped into x through the first one.  The composite is monic because
   monos are stable under pullback and closed under composition.

--------
两个子对象的交集：它们单态的选定拉回，通过第一个映射到 x。复合是单态的，因为单态在拉回下是稳定的，并且在组合下是封闭的。
*)
Definition sub_meet (u v : SubObj x) : SubObj x := {|
  sub_dom := Pull (sub_mono u) (sub_mono v)
               (pullback (sub_mono u) (sub_mono v));
  sub_mono := sub_mono u
              ∘ pullback_fst (sub_mono u) (sub_mono v)
                  (pullback (sub_mono u) (sub_mono v));
  sub_is_monic :=
    monic_compose (sub_is_monic u)
      (monic_pullback_stable (sub_mono u) (sub_mono v) (sub_is_monic v)
         (pullback (sub_mono u) (sub_mono v)))
|}.

(*
Below the first factor, by the first projection: the mediating arrow IS
   [pullback_fst] and the triangle is the definition of [sub_meet].

--------
在第一个因子的下方，通过第一个投影：中介箭头是 [pullback_fst]，三角形是 [sub_meet] 的定义。
*)
Lemma sub_meet_le_l (u v : SubObj x) : sub_le (sub_meet u v) u.
Proof.
  exists (pullback_fst (sub_mono u) (sub_mono v)
            (pullback (sub_mono u) (sub_mono v))).
  reflexivity.
Defined.

(*
Below the second factor, by the second projection: here the triangle is
   the commuting square of the pullback, read backwards.

--------
在第二个投影下的第二个因子：这里的三角形是拉回的交换方形，逆向读取。
*)
Lemma sub_meet_le_r (u v : SubObj x) : sub_le (sub_meet u v) v.
Proof.
  exists (pullback_snd (sub_mono u) (sub_mono v)
            (pullback (sub_mono u) (sub_mono v))).
  symmetry.
  exact (pullback_commutes (sub_mono u) (sub_mono v)
           (pullback (sub_mono u) (sub_mono v))).
Defined.

(*
Mac Lane §V.7, book p. 126: the pullback of two monos is the GREATEST
   subobject below both.  A competing w below both supplies a commuting
   square, the universal property supplies the mediator, and the first
   projection triangle turns that mediator into the required
   factorization.

--------
Mac Lane §V.7，书第126页：两个单射的拉回是位于两者之下的最大子对象。一个位于两者之下的竞争对象 w 提供一个可交换的方格，普遍性性质提供了中介者，第一个投影三角形将该中介者变为所需的分解。
*)
Lemma sub_meet_is_glb (u v : SubObj x) :
  ∀ w : SubObj x, sub_le w u → sub_le w v → sub_le w (sub_meet u v).
Proof.
  intros w [k Hk] [l Hl].
  assert (Hsq : sub_mono u ∘ k ≈ sub_mono v ∘ l) by now rewrite Hk, Hl.
  pose proof (ump_pullbacks (sub_mono u) (sub_mono v)
                (pullback (sub_mono u) (sub_mono v)) (sub_dom w) k l Hsq)
    as U.
  exists (unique_obj U).
  simpl.
  rewrite <- comp_assoc.
  rewrite (fst (unique_property U)).
  exact Hk.
Defined.

(* Packaged as the order-theoretic predicate at the two-element family. / 作为二元族上的序理论谓词来打包。 *)
Lemma sub_meet_IsMeet (u v : SubObj x) : IsMeet u v (sub_meet u v).
Proof.
  constructor.
  - intro b; destruct b; simpl.
    + exact (sub_meet_le_l u v).
    + exact (sub_meet_le_r u v).
  - intros w Hw.
    exact (sub_meet_is_glb u v w (Hw true) (Hw false)).
Defined.

(*
Respectfulness is proved through the universal property, not through
   the pullback: [sub_meet u v] and [sub_meet u' v'] are greatest lower
   bounds of pointwise-equivalent families, hence equivalent.  Fighting
   the chosen pullback directly would need a comparison isomorphism of
   apexes that this argument never mentions.

--------
尊重性是通过普遍性质来证明的，而不是通过拉回：[sub_meet u v] 和 [sub_meet u' v'] 是点对点等价族的最大下界，因此是等价的。直接处理所选的拉回将需要顶点的比较同构，而这个论证从未提到这一点。
*)
#[export] Instance sub_meet_respects :
  Proper (equiv ==> equiv ==> equiv) sub_meet.
Proof.
  intros u u' Hu v v' Hv.
  apply (IsIntersection_unique (sub_pair u' v')).
  - apply (IsIntersection_respects_family (sub_pair u v)).
    + intro b; destruct b; assumption.
    + exact (sub_meet_IsMeet u v).
  - exact (sub_meet_IsMeet u' v').
Defined.

(** *** The order laws, at ≈ / *** 序律，在 ≈ *)

Lemma sub_meet_comm (u v : SubObj x) : sub_meet u v ≈ sub_meet v u.
Proof.
  apply sub_le_antisym.
  - apply sub_meet_is_glb; [ exact (sub_meet_le_r u v)
                           | exact (sub_meet_le_l u v) ].
  - apply sub_meet_is_glb; [ exact (sub_meet_le_r v u)
                           | exact (sub_meet_le_l v u) ].
Defined.

Lemma sub_meet_assoc (u v w : SubObj x) :
  sub_meet (sub_meet u v) w ≈ sub_meet u (sub_meet v w).
Proof.
  apply sub_le_antisym.
  - apply sub_meet_is_glb.
    + exact (sub_le_trans _ _ _ (sub_meet_le_l _ _) (sub_meet_le_l _ _)).
    + apply sub_meet_is_glb.
      * exact (sub_le_trans _ _ _ (sub_meet_le_l _ _) (sub_meet_le_r _ _)).
      * exact (sub_meet_le_r _ _).
  - apply sub_meet_is_glb.
    + apply sub_meet_is_glb.
      * exact (sub_meet_le_l _ _).
      * exact (sub_le_trans _ _ _ (sub_meet_le_r _ _) (sub_meet_le_l _ _)).
    + exact (sub_le_trans _ _ _ (sub_meet_le_r _ _) (sub_meet_le_r _ _)).
Defined.

Lemma sub_meet_idem (u : SubObj x) : sub_meet u u ≈ u.
Proof.
  apply sub_le_antisym.
  - exact (sub_meet_le_l u u).
  - exact (sub_meet_is_glb u u u (sub_le_refl u) (sub_le_refl u)).
Defined.

(* The top subobject is a unit for the meet. / 顶部子对象是一个用于会议的单位。 *)
Lemma sub_meet_top (u : SubObj x) : sub_meet u sub_top ≈ u.
Proof.
  apply sub_le_antisym.
  - exact (sub_meet_le_l u sub_top).
  - exact (sub_meet_is_glb u sub_top u (sub_le_refl u) (sub_top_greatest u)).
Defined.

(*
"u ≤ v iff u ∧ v ≈ u", in two separate lemmas: [sub_le] is Type-valued
   data and the two directions carry different data, so they are not
   packaged as one ↔.

--------
“u ≤ v 当且仅当 u ∧ v ≈ u”，在两个独立的引理中：[sub_le] 是类型值的数据，并且两个方向携带不同的数据，所以它们没有打包为一个 ↔。
*)
Lemma sub_meet_of_le (u v : SubObj x) : sub_le u v → sub_meet u v ≈ u.
Proof.
  intros Huv.
  apply sub_le_antisym.
  - exact (sub_meet_le_l u v).
  - exact (sub_meet_is_glb u v u (sub_le_refl u) Huv).
Defined.

Lemma sub_le_of_meet (u v : SubObj x) : sub_meet u v ≈ u → sub_le u v.
Proof.
  intros Hm.
  exact (sub_le_trans _ _ _ (sub_ge_of_equiv _ _ Hm) (sub_meet_le_r u v)).
Defined.

End Meet.

(** ** Wide intersections by wide pullback / ** 通过大幅回调的广泛交叉 *)

Section WideIntersection.

Context {C : Category}.
Context {x : C}.
Context {J : Type}.
Context (S : J → SubObj x).

(*
Every projection of a wide pullback of monos is monic: two maps agreeing
   after one projection agree after every projection, by the commutativity
   of the wide square and the monicity of the family, hence agree by joint
   monicity.  This is Riehl 4.7.9's "the legs of the cone are monic".

--------
每一个关于单态的广泛回拉的投射都是单态的：两个映射在一次投射后相同，则在每一次投射后都相同，这是由于广方的可交换性以及该族的单态性，因此通过联合单态性也相同。这就是 Riehl 4.7.9 中的“圆锥的边是单态的”
*)
Lemma wide_pullback_proj_monic (W : WidePullback (fun j => sub_mono (S j)))
  (j : J) : Monic (wide_pullback_proj W j).
Proof.
  constructor; intros q g1 g2 Hg.
  apply (wide_pullback_jointly_monic (wide_pullback_is_pullback W)).
  intro i.
  apply (monic (Monic := sub_is_monic (S i))).
  rewrite !comp_assoc.
  rewrite (wide_pullback_commutes W i j).
  rewrite <- !comp_assoc.
  now rewrite Hg.
Qed.

(*
The intersection of a family of subobjects, presented at an index j0:
   the wide pullback of the monos, mapped into x through the j0-th member.
   By [wide_pullback_commutes] the mono does not depend on j0 up to ≈.
   The [sub_is_monic] field is Riehl 4.7.9's "the induced map into the
   codomain is again monic".

--------
在指标 j0 处呈现的一族子对象的交集：通过 j0-成员映射到 x 的单射的广拉回。根据 [wide_pullback_commutes]，该单射在 ≈ 意义下不依赖于 j0。[sub_is_monic] 字段是 Riehl 4.7.9 的“诱导到陪域的映射仍然是单射”。
*)
Definition sub_wide_intersection (j0 : J)
  (W : WidePullback (fun j => sub_mono (S j))) : SubObj x := {|
  sub_dom := WPull W;
  sub_mono := sub_mono (S j0) ∘ wide_pullback_proj W j0;
  sub_is_monic :=
    monic_compose (sub_is_monic (S j0)) (wide_pullback_proj_monic W j0)
|}.

(*
Riehl 4.7.9 in full: the wide pullback presents the greatest subobject
   of x contained in every member of the family.  Containment in the j-th
   member is the j-th projection, with the wide square as its triangle;
   maximality is the wide universal property applied to the family of
   factorizations a competing subobject supplies.

--------
Riehl 4.7.9 完整内容：广泛的回拉呈现了包含在族中每个成员中的 x 的最大子对象。第 j 个成员的包含是第 j 个投影，广泛的方形为其三角形；最大性是将广泛的普遍性应用于竞争子对象所提供的分解族。
*)
Theorem sub_wide_intersection_IsIntersection (j0 : J)
  (W : WidePullback (fun j => sub_mono (S j))) :
  IsIntersection S (sub_wide_intersection j0 W).
Proof.
  constructor.
  - (* below every member, by that member's projection / 在每个成员下面，由该成员的投影 *)
    intro j.
    exists (wide_pullback_proj W j).
    exact (wide_pullback_commutes W j j0).
  - (* maximal among the subobjects below every member / 在每个成员下面的子对象中是最大的 *)
    intros v Hv.
    pose (q := fun j => `1 (Hv j)).
    assert (Hq : ∀ i j : J, sub_mono (S i) ∘ q i ≈ sub_mono (S j) ∘ q j).
    { intros i j; unfold q.
      rewrite (`2 (Hv i)), (`2 (Hv j)); reflexivity. }
    pose proof (ump_wide_pullbacks W (sub_dom v) q Hq) as U.
    exists (unique_obj U).
    simpl.
    rewrite <- comp_assoc.
    rewrite (unique_property U j0).
    exact (`2 (Hv j0)).
Defined.

(*
The chosen index is immaterial, and at the strongest available reading:
   the two subobjects have the SAME domain, so the identity isomorphism
   witnesses the equivalence and only the triangle has to be discharged,
   by the wide square.

--------
所选择的索引无关紧要，在最强可用的读法下：两个子对象具有相同的域，因此恒等同构证明了等价性，只有三角形需要通过宽正方形来消解。
*)
Lemma sub_wide_intersection_index_irrelevant (j0 j1 : J)
  (W : WidePullback (fun j => sub_mono (S j))) :
  sub_wide_intersection j0 W ≈ sub_wide_intersection j1 W.
Proof.
  exists iso_id; simpl.
  rewrite id_right.
  exact (wide_pullback_commutes W j1 j0).
Defined.

End WideIntersection.

(** ** The binary meet as a wide intersection / ** 二进制相遇作为一个广泛的交集 *)

Section MeetIsWide.

Context {C : Category}.
Context `{@HasPullbacks C}.
Context {x : C}.

(*
Whenever the pair of monos carries a wide pullback, the wide
   intersection presented at [true] agrees with the chosen binary meet.
   The comparison is made through the two universal properties rather than
   through Structure/Pullback/Wide.v ([binary_wide_pullback]): that
   lemma's family is [two_maps f g] over [two_fam (sub_dom u) (sub_dom v)],
   whereas the family here is [fun b => sub_mono (sub_pair u v b)] over
   [fun b => sub_dom (sub_pair u v b)], and the two index families are
   convertible only at each literal [true] and [false], not as functions
   of a variable b -- so routing through it would cost a transport of the
   whole [IsWidePullback] record along a pointwise-only conversion.  The
   order-theoretic route costs three lines.

--------
每当这对单元承载一个大的回撤时，在 [true] 处呈现的宽交集与所选的二元会合一致。比较是通过两个通用性质进行的，而不是通过 Structure/Pullback/Wide.v（[binary_wide_pullback]）：该引理的族是 [two_maps f g] 在 [two_fam (sub_dom u) (sub_dom v)] 上，而这里的族是 [fun b => sub_mono (sub_pair u v b)] 在 [fun b => sub_dom (sub_pair u v b)] 上，而且这两个索引族仅在每个字面 [true] 和 [false] 处可转换，而不是作为变量 b 的函数——因此通过它进行传递将需要沿逐点转换传输整个 [IsWidePullback] 记录。序理论路线需要三行。
*)
Theorem sub_meet_is_wide_intersection (u v : SubObj x)
  (W : WidePullback (fun b => sub_mono (sub_pair u v b))) :
  sub_meet u v ≈ sub_wide_intersection (sub_pair u v) true W.
Proof.
  apply (IsIntersection_unique (sub_pair u v)).
  - exact (sub_meet_IsMeet u v).
  - exact (sub_wide_intersection_IsIntersection (sub_pair u v) true W).
Defined.

End MeetIsWide.

(** ** The total form: all wide intersections at once / ** 总形式：所有宽交叉口一次性 *)

Section TotalIntersection.

Context {C : Category}.
Context `{@HasWidePullbacks C}.
Context {x : C}.

(*
With every wide pullback chosen, the intersection of a family is a
   total operation -- still presented at an index, for the reason recorded
   in the header.

--------
每次选择的宽回撤，家庭的交集都是一个完全操作——仍然以索引形式呈现，原因记录在标题中。
*)
Definition sub_intersection {J : Type} (j0 : J) (S : J → SubObj x) :
  SubObj x :=
  sub_wide_intersection S j0 (wide_pullback (fun j => sub_mono (S j))).

Theorem sub_intersection_IsIntersection {J : Type} (j0 : J)
  (S : J → SubObj x) : IsIntersection S (sub_intersection j0 S).
Proof.
  exact (sub_wide_intersection_IsIntersection S j0
           (wide_pullback (fun j => sub_mono (S j)))).
Defined.

End TotalIntersection.

(** ** Images as subobjects, and joins by image of the copairing / ** 作为子对象的图像，以及由共对偶的图像形成的连接 *)

Section Images.

Context {C : Category}.

(*
An image of f : y ~> x as a subobject of x: f factors through it, and
   it is the least subobject f factors through.  This is the (E, Mono)
   image of an orthogonal factorization system read as an order-theoretic
   statement; it is what a union of subobjects consumes.

--------
f : y ~> x 的一个图像作为 x 的子对象：f 通过它进行分解，并且它是 f 可以分解通过的最小子对象。这是一个正交分解系统的 (E, Mono) 图像，可作为序理论的陈述来阅读；它就是一个子对象的并集所涵盖的内容。
*)
Record ImageOf {y x : C} (f : y ~> x) := {
  im_sub : SubObj x;
  im_factor : y ~> sub_dom im_sub;
  im_commutes : sub_mono im_sub ∘ im_factor ≈ f;
  im_least : ∀ (w : SubObj x) (g : y ~> sub_dom w),
    sub_mono w ∘ g ≈ f → sub_le im_sub w
}.

Class HasImages := {
  image_of : ∀ {y x : C} (f : y ~> x), ImageOf f
}.

End Images.

Arguments im_sub {C y x f} _.
Arguments im_factor {C y x f} _.
Arguments im_commutes {C y x f} _.
Arguments im_least {C y x f} _ _ _ _.
Arguments HasImages C : clear implicits.
Arguments image_of {C _ y x} f.

Section Join.

Context {C : Category}.
Context `{@Cocartesian C}.
Context {x : C}.

(*
The union of two subobjects: the image of the copairing of their monos
   out of the coproduct of their domains, given such an image.

--------
两个子对象的并集：从它们的域的余积出的单子映射的拼合集的像，给定这样的像。
*)
Definition sub_join_via (u v : SubObj x)
  (I : ImageOf (merge (sub_mono u) (sub_mono v))) : SubObj x := im_sub I.

Definition sub_join `{@HasImages C} (u v : SubObj x) : SubObj x :=
  sub_join_via u v (image_of (merge (sub_mono u) (sub_mono v))).

(*
Above the first factor: the mediating arrow is the image factorization
   precomposed with [inl], and the triangle is [inl_merge]
   (Structure/Cocartesian.v).

--------
在第一个因子之上：中介箭头是与 [inl] 预组合的图像分解，三角形是 [inl_merge]（Structure/Cocartesian.v）。
*)
Lemma sub_join_via_le_l (u v : SubObj x)
  (I : ImageOf (merge (sub_mono u) (sub_mono v))) :
  sub_le u (sub_join_via u v I).
Proof.
  exists (im_factor I ∘ inl).
  unfold sub_join_via.
  rewrite comp_assoc.
  rewrite (im_commutes I).
  exact (inl_merge (sub_mono u) (sub_mono v)).
Defined.

(* ... and above the second, by [inr_merge] (Structure/Cocartesian.v). / ... 并在第二个之上，由 [inr_merge]（Structure/Cocartesian.v）提供。 *)
Lemma sub_join_via_le_r (u v : SubObj x)
  (I : ImageOf (merge (sub_mono u) (sub_mono v))) :
  sub_le v (sub_join_via u v I).
Proof.
  exists (im_factor I ∘ inr).
  unfold sub_join_via.
  rewrite comp_assoc.
  rewrite (im_commutes I).
  exact (inr_merge (sub_mono u) (sub_mono v)).
Defined.

(*
The image is the LEAST subobject above both: a competing w above both
   supplies two factorizations, their copairing factors the copairing of
   the monos through w, and [im_least] is exactly the statement that the
   image is below any subobject the map factors through.

--------
像是同时位于两者之上的最小子对象：一个竞争的 w 位于两者之上提供了两个分解，它们的共配对分解了通过 w 的单映射的共配对，而 [im_least] 正是表明像位于映射所分解的任何子对象之下的陈述。
*)
Lemma sub_join_via_is_lub (u v : SubObj x)
  (I : ImageOf (merge (sub_mono u) (sub_mono v))) (w : SubObj x) :
  sub_le u w → sub_le v w → sub_le (sub_join_via u v I) w.
Proof.
  intros [k Hk] [l Hl].
  apply (im_least I w (merge k l)).
  rewrite <- merge_comp.
  rewrite Hk, Hl.
  reflexivity.
Defined.

Lemma sub_join_via_IsJoin (u v : SubObj x)
  (I : ImageOf (merge (sub_mono u) (sub_mono v))) :
  IsJoin u v (sub_join_via u v I).
Proof.
  constructor.
  - intro b; destruct b; simpl.
    + exact (sub_join_via_le_l u v I).
    + exact (sub_join_via_le_r u v I).
  - intros w Hw.
    exact (sub_join_via_is_lub u v I w (Hw true) (Hw false)).
Defined.

End Join.

(** ** The join as a lattice operation, with images chosen / ** 作为格操作的并，选择了图像 *)

Section JoinLattice.

Context {C : Category}.
Context `{CC : @Cocartesian C}.
Context `{HI : @HasImages C}.
Context {x : C}.

Lemma sub_join_le_l (u v : SubObj x) : sub_le u (sub_join u v).
Proof. exact (sub_join_via_le_l u v _). Defined.

Lemma sub_join_le_r (u v : SubObj x) : sub_le v (sub_join u v).
Proof. exact (sub_join_via_le_r u v _). Defined.

Lemma sub_join_is_lub (u v : SubObj x) :
  ∀ w : SubObj x, sub_le u w → sub_le v w → sub_le (sub_join u v) w.
Proof. intros w Hu Hv; exact (sub_join_via_is_lub u v _ w Hu Hv). Defined.

Lemma sub_join_IsJoin (u v : SubObj x) : IsJoin u v (sub_join u v).
Proof. exact (sub_join_via_IsJoin u v _). Defined.

(*
As with the meet: least upper bounds of pointwise-equivalent families
   agree, so the chosen image never has to be compared with itself.

--------
与交相同：点对点等价族的最小上界是一致的，因此所选择的映像永远不必与自身比较。
*)
#[export] Instance sub_join_respects :
  Proper (equiv ==> equiv ==> equiv) (@sub_join C CC x HI).
Proof.
  intros u u' Hu v v' Hv.
  apply (IsUnion_unique (sub_pair u' v')).
  - apply (IsUnion_respects_family (sub_pair u v)).
    + intro b; destruct b; assumption.
    + exact (sub_join_IsJoin u v).
  - exact (sub_join_IsJoin u' v').
Defined.

Lemma sub_join_comm (u v : SubObj x) : sub_join u v ≈ sub_join v u.
Proof.
  apply sub_le_antisym.
  - apply sub_join_is_lub; [ exact (sub_join_le_r v u)
                           | exact (sub_join_le_l v u) ].
  - apply sub_join_is_lub; [ exact (sub_join_le_r u v)
                           | exact (sub_join_le_l u v) ].
Defined.

Lemma sub_join_assoc (u v w : SubObj x) :
  sub_join (sub_join u v) w ≈ sub_join u (sub_join v w).
Proof.
  apply sub_le_antisym.
  - apply sub_join_is_lub.
    + apply sub_join_is_lub.
      * exact (sub_join_le_l _ _).
      * exact (sub_le_trans _ _ _ (sub_join_le_l _ _) (sub_join_le_r _ _)).
    + exact (sub_le_trans _ _ _ (sub_join_le_r _ _) (sub_join_le_r _ _)).
  - apply sub_join_is_lub.
    + exact (sub_le_trans _ _ _ (sub_join_le_l _ _) (sub_join_le_l _ _)).
    + apply sub_join_is_lub.
      * exact (sub_le_trans _ _ _ (sub_join_le_r _ _) (sub_join_le_l _ _)).
      * exact (sub_join_le_r _ _).
Defined.

Lemma sub_join_idem (u : SubObj x) : sub_join u u ≈ u.
Proof.
  apply sub_le_antisym.
  - exact (sub_join_is_lub u u u (sub_le_refl u) (sub_le_refl u)).
  - exact (sub_join_le_l u u).
Defined.

(* "u ≤ v iff u ∨ v ≈ v", again in two separate lemmas. / “u ≤ v 当且仅当 u ∨ v ≈ v”，再次分成两个独立的引理。 *)
Lemma sub_join_of_le (u v : SubObj x) : sub_le u v → sub_join u v ≈ v.
Proof.
  intros Huv.
  apply sub_le_antisym.
  - exact (sub_join_is_lub u v v Huv (sub_le_refl v)).
  - exact (sub_join_le_r u v).
Defined.

Lemma sub_le_of_join (u v : SubObj x) : sub_join u v ≈ v → sub_le u v.
Proof.
  intros Hj.
  exact (sub_le_trans _ _ _ (sub_join_le_l u v) (sub_le_of_equiv _ _ Hj)).
Defined.

End JoinLattice.

(** ** Absorption: the two operations make a lattice on the setoid / ** 吸收：这两个运算在集合等价类上构成一个格 *)

Section Absorption.

Context {C : Category}.
Context `{@HasPullbacks C}.
Context `{CC : @Cocartesian C}.
Context `{HI : @HasImages C}.
Context {x : C}.

(*
u ∧ (u ∨ v) ≈ u.  One direction is the meet's first projection, the
   other is the greatest-lower-bound property applied to u ≤ u and
   u ≤ u ∨ v.

--------
u ∧ (u ∨ v) ≈ u。一方面是交运算的第一个投影，另一方面是应用于 u ≤ u 和 u ≤ u ∨ v 的最大下界性质。
*)
Theorem sub_meet_absorb (u v : SubObj x) : sub_meet u (sub_join u v) ≈ u.
Proof.
  apply sub_le_antisym.
  - exact (sub_meet_le_l u (sub_join u v)).
  - exact (sub_meet_is_glb u (sub_join u v) u (sub_le_refl u)
             (sub_join_le_l u v)).
Defined.

(* u ∨ (u ∧ v) ≈ u, dually. / u ∨ (u ∧ v) ≈ u，对偶地。 *)
Theorem sub_join_absorb (u v : SubObj x) : sub_join u (sub_meet u v) ≈ u.
Proof.
  apply sub_le_antisym.
  - exact (sub_join_is_lub u (sub_meet u v) u (sub_le_refl u)
             (sub_meet_le_l u v)).
  - exact (sub_join_le_l u (sub_meet u v)).
Defined.

End Absorption.

(** ** Indexed joins / ** 索引连接 *)

Section WideJoin.

Context {C : Category}.
Context {x : C}.
Context {J : Type}.
Context (S : J → SubObj x).

(*
The union of a family: the image of the induced map out of an indexed
   coproduct of the domains, given such an image.

--------
一个家庭的并集：在给定这样的像的情况下，由域的一个索引余积引出的映射的像。
*)
Definition sub_wide_join_via {p : C} {inj : ∀ j, sub_dom (S j) ~> p}
  (P : IsIndexedCoproduct (fun j => sub_dom (S j)) p inj)
  (I : ImageOf (unique_obj (icoprod_desc P (fun j => sub_mono (S j))))) :
  SubObj x := im_sub I.

(*
The indexed least upper bound.  Membership is the j-th coproduct
   injection followed by the image factorization; minimality copairs the
   family of factorizations a competing subobject supplies and identifies
   the result with the induced map by the uniqueness half of
   [icoprod_desc].

--------
带索引的最小上界。成员是第 j 个余积注入，随后进行像分解；最小性是将竞争子对象提供的一族分解进行对偶，并通过 [icoprod_desc] 的唯一性部分将结果与诱导映射识别。
*)
Theorem sub_wide_join_via_IsUnion {p : C} {inj : ∀ j, sub_dom (S j) ~> p}
  (P : IsIndexedCoproduct (fun j => sub_dom (S j)) p inj)
  (I : ImageOf (unique_obj (icoprod_desc P (fun j => sub_mono (S j))))) :
  IsUnion S (sub_wide_join_via P I).
Proof.
  pose (D := icoprod_desc P (fun j => sub_mono (S j))).
  constructor.
  - (* the j-th member sits below the image / 第 j 个成员坐在图片下面 *)
    intro j.
    exists (im_factor I ∘ inj j).
    unfold sub_wide_join_via.
    rewrite comp_assoc.
    rewrite (im_commutes I).
    exact (unique_property D j).
  - (* and the image is below every common upper bound / 并且图像位于每个常见上界之下 *)
    intros v Hv.
    pose proof (icoprod_desc P (fun j => `1 (Hv j))) as E.
    apply (im_least I v (unique_obj E)).
    symmetry.
    apply (uniqueness D).
    intro j.
    rewrite <- comp_assoc.
    rewrite (unique_property E j).
    exact (`2 (Hv j)).
Defined.

End WideJoin.

(** ** The bottom subobject / ** 底部子对象 *)

Section Bottom.

Context {C : Category}.
Context `{I : @Initial C}.
Context {x : C}.

(*
The least subobject, when the arrow out of the initial object is monic
   (it is whenever the initial object is strict).

--------
当初始对象的箭头是单射时（当初始对象是严格时总是如此），最小子对象。
*)
Definition sub_bot (Hz : Monic (@zero C I x)) : SubObj x := {|
  sub_dom := 0;
  sub_mono := zero;
  sub_is_monic := Hz
|}.

Lemma sub_bot_least (Hz : Monic (@zero C I x)) (u : SubObj x) :
  sub_le (sub_bot Hz) u.
Proof. exists zero; apply zero_unique. Defined.

(*
Strictness supplies the hypothesis.  For g1 g2 : w ~> 0, strictness at
   g1 gives an isomorphism i : w ≅ 0; every map w ~> 0 then agrees with
   [to i], because precomposing it with [from i] lands in the endomorphism
   monoid of the initial object, where [zero_unique] leaves only the
   identity.  The cancellation hypothesis of [Monic] is never consumed:
   in a category with a strict initial object ANY two maps into 0 agree.

--------
严格性提供了假设。对于 g1 g2 : w ~> 0，g1 的严格性给出了一个同构 i : w ≅ 0；然后每个从 w ~> 0 的映射都与 [to i] 一致，因为将其与 [from i] 复合会落在初始对象的自同态幺半群中，而 [zero_unique] 仅保留恒等映射。[Monic] 的抵消假设从未被使用：在具有严格初始对象的范畴中，任意两个进入 0 的映射都是一致的。
*)
Lemma zero_monic_of_strict
  (Hstrict : ∀ (y : C) (f : y ~> 0), y ≅ 0) : Monic (@zero C I x).
Proof.
  constructor; intros w g1 g2 _.
  pose proof (Hstrict w g1) as i.
  assert (Hto : ∀ g : w ~> 0, g ≈ to i).
  { intro g.
    transitivity (g ∘ (from i ∘ to i)).
    - rewrite (iso_from_to i); cat.
    - rewrite comp_assoc.
      rewrite (@zero_unique C I 0 (g ∘ from i) id).
      cat. }
  now rewrite (Hto g1), (Hto g2).
Qed.

(* The empty union, at the least subobject. / 空并集，至少的子对象。 *)
Lemma IsUnion_empty_bot (Hz : Monic (@zero C I x)) {J : Type}
  (S : J → SubObj x) (Hempty : J → False) : IsUnion S (sub_bot Hz).
Proof.
  exact (IsUnion_empty_of_least S (sub_bot Hz) (sub_bot_least Hz) Hempty).
Defined.

End Bottom.

(** ** The bottom in a bicartesian closed category / ** 二笛卡尔闭范畴中的底对象 *)

Section BiCCCBottom.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Closed C _}.
Context `{I : @Initial C}.
Context {x : C}.

(*
A cartesian closed category with an initial object has a STRICT
   initial object (Structure/BiCCC.v, [initial_strict]), so the arrow
   out of it is monic and [sub_bot] applies with no further hypothesis.
   This is the one place in this file where the bottom subobject is
   obtained rather than assumed.  Two measurements govern it.  The
   requirement cost was taken only after being measured, by iterating
   [coqdep -R . Category FILE] to a fixed point over the .v files named
   in its right-hand sides: the two files Structure/BiCCC.v adds to this
   file's requirement closure are itself and Structure/Distributive.v,
   taking that closure from 46 to 48 (the whole file's closure is 48
   files; the interface stub this one replaced measured 37 by the same
   procedure).  And the hypothesis list is exactly the one
   below, NOT the full bicartesian closed one: [initial_strict] is proved
   in Structure/BiCCC.v under a cocartesian context as well, but does not
   consume it, so no [Cocartesian] is declared here and none appears in
   the discharged type of [biccc_zero_monic] -- read off with
   [Check @biccc_zero_monic], whose binders are the category, a
   [Cartesian], a [Closed], a [Terminal] of the opposite (that is the
   [Initial]), and the object.

--------
一个具有初始对象的笛卡尔闭范畴具有严格初始对象 (Structure/BiCCC.v, [initial_strict])，因此指向它的箭头是单射，并且 [sub_bot] 在无需进一步假设的情况下适用。这是本文件中唯一一个底子对象是被获得而非假设的地方。有两个测量来管理它。需求成本只有在测量之后才被采用，通过对其右侧命名的 .v 文件迭代 [coqdep -R . Category FILE] 到固定点：Structure/BiCCC.v 添加到本文件需求闭包的两个文件是它自身和 Structure/Distributive.v，将闭包从 46 个文件提高到 48 个（整个文件的闭包为 48 个文件；本文件替换的接口存根通过同样的程序测量为 37 个）。
假设列表正是下面这个，而不是完整的双笛卡尔闭合列表：[initial_strict] 在 Structure/BiCCC.v 中在一个余笛卡尔上下文下被证明，但并未消耗它，因此这里没有声明 [Cocartesian]，也没有出现在 [biccc_zero_monic] 的已释放类型中——可通过 [Check @biccc_zero_monic] 读取，其绑定器是范畴、一个 [Cartesian]、一个 [Closed]、一个 [Terminal] 的对偶（即 [Initial]）以及对象。
*)
Definition biccc_zero_monic : Monic (@zero C I x) :=
  zero_monic_of_strict (fun y f => initial_strict f).

(* ... and the bottom subobject it names. / ... 以及它所命名的底部子对象。 *)
Definition biccc_sub_bot : SubObj x := sub_bot biccc_zero_monic.

End BiCCCBottom.

(** ** The bottom against the two operations / ** 底部对抗两个操作 *)

Section BottomMeet.

Context {C : Category}.
Context `{@HasPullbacks C}.
Context `{I : @Initial C}.
Context {x : C}.

(* ∅ ∩ X ≈ ∅. / ∅ ∩ X ≈ ∅。 *)
Theorem sub_meet_bot (Hz : Monic (@zero C I x)) (u : SubObj x) :
  sub_meet (sub_bot Hz) u ≈ sub_bot Hz.
Proof.
  apply sub_le_antisym.
  - exact (sub_meet_le_l (sub_bot Hz) u).
  - exact (sub_bot_least Hz (sub_meet (sub_bot Hz) u)).
Defined.

End BottomMeet.

Section BottomJoin.

Context {C : Category}.
Context `{CC : @Cocartesian C}.
Context `{HI : @HasImages C}.
Context `{I : @Initial C}.
Context {x : C}.

(*
Fong and Spivak §1.2.1's unit law ∅ ∪ X ≅ X, at the level of
   subobjects, with the image of the copairing handed in: the bottom is
   below u, so u is already a least upper bound of the pair, and least
   upper bounds agree.  Stated first with an explicit [ImageOf], so that a
   category with images for SOME copairings (or a single computed image)
   can use it without a [HasImages] instance; the class form follows.
   [HI] is not consumed by this lemma and is dropped from its discharged
   type -- read it off with [Check @sub_join_via_bot].

--------
Fong 与 Spivak §1.2.1 的单位律 ∅ ∪ X ≅ X，在子对象的层面上，处理了共对映射的像：底部在 u 之下，因此 u 已经是这一对的最小上界，并且最小上界是一致的。首先用显式的 [ImageOf] 表述，以便对某些共对映射有像的范畴（或单个计算出的像）可以在没有 [HasImages] 实例的情况下使用它；类形式随后给出。[HI] 并未被该引理使用，因此从其解除类型中删除——通过 [Check @sub_join_via_bot] 读取。
*)
Lemma sub_join_via_bot (Hz : Monic (@zero C I x)) (u : SubObj x)
  (Img : ImageOf (merge (sub_mono (sub_bot Hz)) (sub_mono u))) :
  sub_join_via (sub_bot Hz) u Img ≈ u.
Proof.
  apply sub_le_antisym.
  - exact (sub_join_via_is_lub (sub_bot Hz) u Img u (sub_bot_least Hz u)
             (sub_le_refl u)).
  - exact (sub_join_via_le_r (sub_bot Hz) u Img).
Defined.

Theorem sub_join_bot (Hz : Monic (@zero C I x)) (u : SubObj x) :
  sub_join (sub_bot Hz) u ≈ u.
Proof.
  exact (sub_join_via_bot Hz u
           (image_of (merge (sub_mono (sub_bot Hz)) (sub_mono u)))).
Defined.

End BottomJoin.

(** ** Images from an orthogonal factorization system / ** 来自正交分解系统的图像 *)

Section OFSImages.

Context {C : Category}.
Context {E : MorphismClass C}.

(*
The mono leg of an (E, Mono) factorization, read as a subobject.  No
   transport is needed: Theory/Morphisms/Classes.v defines [MonoClass]
   as [fun _ _ f => Monic f], so [fact_m_in] IS the [sub_is_monic]
   field.

--------
(E, 单) 分解的单腿，被读作子对象。无需传输：Theory/Morphisms/Classes.v 将 [MonoClass] 定义为 [fun _ _ f => Monic f]，因此 [fact_m_in] 是 [sub_is_monic] 字段。
*)
Definition ofs_image_sub (O : OFS E (@MonoClass C)) {y x : C} (f : y ~> x) :
  SubObj x := {|
  sub_dom := fact_mid (ofs_factor (OFS := O) f);
  sub_mono := fact_m (ofs_factor (OFS := O) f);
  sub_is_monic := fact_m_in (ofs_factor (OFS := O) f)
|}.

(*
Minimality is orthogonality.  A factorization of f through a subobject
   w bounds a commuting square between the E-leg of the factorization and
   the mono of w; the diagonal filler of Theory/Orthogonality.v is the
   arrow exhibiting the image below w, and its second triangle is the
   factorization required by [sub_le].

--------
最小性是正交性。通过子对象 w 对 f 的分解界定了分解的 E 臂与 w 的单态之间的交换方形；Theory/Orthogonality.v 中的对角填充器是展示 w 下图像的箭头，其第二个三角形是 [sub_le] 所需的分解。
*)
Lemma ofs_image_least (O : OFS E (@MonoClass C)) {y x : C} (f : y ~> x)
  (w : SubObj x) (g : y ~> sub_dom w) (Hg : sub_mono w ∘ g ≈ f) :
  sub_le (ofs_image_sub O f) w.
Proof.
  pose proof (ofs_orth (OFS := O) (fact_e (ofs_factor (OFS := O) f))
                (sub_mono w) (fact_e_in (ofs_factor (OFS := O) f))
                (sub_is_monic w)) as Ho.
  assert (Hc : sub_mono w ∘ g
               ≈ fact_m (ofs_factor (OFS := O) f)
                   ∘ fact_e (ofs_factor (OFS := O) f)).
  { rewrite (fact_comm (ofs_factor (OFS := O) f)); exact Hg. }
  pose proof (ortho_lift (Orthogonal := Ho) Hc) as U.
  exists (unique_obj U).
  exact (snd (unique_property U)).
Defined.

(* Every (E, Mono) factorization system supplies images. / 每个（E，单态）分解系统都提供像。 *)
Definition ImageOf_of_OFS (O : OFS E (@MonoClass C)) {y x : C} (f : y ~> x) :
  ImageOf f := {|
  im_sub := ofs_image_sub O f;
  im_factor := fact_e (ofs_factor (OFS := O) f);
  im_commutes := fact_comm (ofs_factor (OFS := O) f);
  im_least := fun w g Hg => ofs_image_least O f w g Hg
|}.

Definition HasImages_of_OFS (O : OFS E (@MonoClass C)) : HasImages C :=
  {| image_of := fun y x f => ImageOf_of_OFS O f |}.

End OFSImages.

(*
A regular category has images, through its (regular epi, mono) system
   Regular_OFS (Structure/Regular/Factorization.v).  CONDITIONAL: no
   [Regular] instance exists in this tree (Instance/Sets/Pullback.v),
   so this corollary is an implication awaiting a model, and it is the
   only route in this file from an established structure to [HasImages].

--------
一个正规范畴通过其（正规满射, 单射）系统具有像 
   Regular_OFS（Structure/Regular/Factorization.v）。条件：否
   这个树中不存在 [Regular] 实例（Instance/Sets/Pullback.v），
   因此这个推论是一个等待模型的蕴含，并且它是这个文件中从一个已建立的结构到 [HasImages] 的唯一途径。
*)
Definition Regular_HasImages {C : Category} (R : Regular C) : HasImages C :=
  HasImages_of_OFS (@Regular_OFS C R).
