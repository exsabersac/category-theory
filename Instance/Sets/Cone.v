Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Diagram.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Presented.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Cone.Const.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Sets.Karoubi.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.GAFT.Sets.
Require Import Category.Adjunction.Diagonal.Limit.

Generalizable All Variables.
#[local] Obligation Tactic := idtac.

(* * * Mac Lane's cone-set limit: the comparison, the remark, the cases / * * 麦克莱恩的锥集极限：比较、评论、例子 *)

(*
 Mac Lane, _Categories for the Working Mathematician_, 2nd ed. (GTM 5),
 SV.1 Theorem 1 and the remark following it, printed p. 110 (PDF p. 119);
 item ids [maclane:V.1:thm1], [maclane:V.1:remark1].  Awodey, _Category
 Theory_ (1st ed., CMU pre-print, September 2005), SS3.3 Example 3.14,
 printed p. 67; item id [awodey:3.3:example14].  Fong & Spivak, _Seven
 Sketches in Compositionality_ (CUP, 2019), SS3.5.3 Theorem 3.95, printed
 p. 112; item id [7sketches:3.5.3:thm3.95].  Riehl, _Category Theory in
 Context_, 2nd ed., SS3.2 Definition 3.2.3, Theorem 3.2.4 and Example
 3.2.7, printed pp. 93-94; item ids [riehl:3.2:def3], [riehl:3.2:thm4],
 [riehl:3.2:example7].

 The construction itself is Instance/Sets/Complete.v's, alongside the
 compatible-family limit that file already carried.  THIS file is the
 rider: the comparison of the two apexes, the remark's natural bijection,
 its identification with the diagonal-limit adjunction, and the equalizer
 and tuple readings.  It is a LEAF -- nothing in the tree depends on it --
 which is why it may carry the heavy [Require]s that the core cannot.

 WHY THESE ARE NOT IN Instance/Sets/Complete.v.  Two separate reasons, and
 only the second is a hard one.  (i) Instance/Sets/Complete.v's transitive
 closure is held at 33 modules ([coqdep -sort], counting the file itself);
 [Structure/Limit/Unique] -- which supplies [limit_unique_iso], i.e. the
 whole comparison -- costs it one more, and the natural-bijection block
 costs four.  Those go here instead, and the number is the reason.  (ii)
 Adjunction/Diagonal/Limit.v REQUIRES Category.Instance.Sets.Complete,
 so the adjunction identification cannot live in that file at all: it
 would be a dependency cycle.  That is what makes this file necessary
 rather than merely tidy.

 THE COMPARISON

 [cone_apex_iso] is [limit_unique_iso] applied to the two limit witnesses.
 Both apexes are limits of the same diagram, so the isomorphism and BOTH
 leg-commutation families come for free -- there is no new proof content
 in this section at all, and the file says so rather than dressing it up.
 What IS worth pinning, and is pinned by [eq_refl], is that the comparison
 is not opaque: its forward leg IS the cone-set mediator
 ([cone_apex_iso_to_is_med]), and the two leg families ARE the named ones
 ([cone_apex_iso_leg_cone], [cone_apex_iso_leg_family]).

 THE APEXES THEMSELVES ARE NOT EQUAL, and the two strict attempts are
 refused: at the object level with “cannot unify” (a CONVERSION refusal),
 because one is a sigma of a dependent function with a compatibility
 witness and the other an [ACone] record.  There is no [≈] grade to fall
 back to either -- objects of [Sets] carry no setoid, so the attempt is a
 RESOLUTION refusal (“Cannot infer the implicit parameter Setoid”).  Both
 are pinned in Test/ProbeConeSets407.v; note that a bare [Check] of the
 second is ACCEPTED, printing an open evar, so the refutation command must
 be a [Definition].

 THE REMARK, DISPLAY (3)

 “The crux of this proof is the (natural) bijection

 Cone (X, F) ~= Set (X, Cone ( *, F))                       (3)

 given by tau |--> h, as above.”

 The parenthesis around “natural” is the book's, and the book does NOT
 prove it -- that is this issue's work item 4, first half, and it is
 proved here.  [ConeSet_Natural_Iso] is a genuine isomorphism in the
 functor category [[Sets^op, Sets]] between [ConePresheaf F] -- the left
 side of (3) AS A FUNCTOR OF X, which is exactly what Structure/Cone.v
 already is -- and [Curried_CoHom Sets (cone_apex F)], the right side.
 Every naturality clause closes by [reflexivity].  [ConeSet_Representable]
 reads the same isomorphism as representability of the cone presheaf,
 which is the content Structure/UniversalProperty/Limit.v states
 abstractly and which is here inhabited.

 THE ADJUNCTION, AND WHICH ORACLE YOU FEED IT

 Mac Lane rewrites (3) as [Nat (Delta X, F) ~= Set (X, Cone ( *, F))] and
 says “By the very definition of limit, this proves that Lim F ~= Cone
 ( *, F)”.  In tree the adjunction is #353's [Diagonal_Limit_Adjunction],
 which takes a [HasLimitsOfShape] as a parameter -- a CHOICE of limits --
 and the identification depends on WHICH choice.

 Fed [ConeSet_HasLimitsOfShape], built from the cone-set construction, the
 book's bijection IS the adjunction's transposition, and four [eq_refl]
 readbacks say so: the adjunction's right-hand object is [cone_apex], its
 leg is [cone_leg_at], its backward transpose has [cone_untranspose]'s
 legs, and its counit component is [cone_leg_at ∘ id].  READ THE THIRD AT
 ITS MEASURED GRADE: it is stated LEG BY LEG and not on whole records,
 because the whole-record form is refused -- for the same donor reason the
 forward transposition is, recorded two paragraphs below -- and that
 refusal is pinned in the probe.

 Fed the PRE-EXISTING [Sets_HasLimitsOfShape] -- which is built on
 [Sets_Complete], the compatible-family oracle -- it is not, and not even
 at the same TYPE: ascribing that adjunction's transposition at the
 cone-set codomain is a plain has-type mismatch (a TYPING refusal, no
 “cannot unify” and no universe clause).  That refusal is pinned in the
 probe with the cone-set form beside it as the discriminating control.
 The bridge between the two readings is [cone_apex_iso].

 SO THE HONEST STATEMENT IS THE CONDITIONAL ONE, and it is the interesting
 content of work item 4: the book's bijection is the transposition of the
 diagonal-limit adjunction AT THE CONE-SET ORACLE.  Nothing here claims it
 is the transposition of the pre-existing [Sets_Diagonal_Limit_Adjunction].

 ONE GRADE IS NOT [eq_refl], AND THE LOCALIZATION IS WEAKER THAN THE
 OBVIOUS ONE.  The FORWARD transposition applied to a cone, compared as a
 whole morphism with [cone_transpose], is refused at CONVERSION.  One
 donor fact is measured and true: [Cone_Natural_Transform]'s [ACone] round
 trip (Structure/Cone/Const.v) returns the LEG FAMILY on the nose --
 [vertex_map] of the round trip is [vertex_map] of the original at
 [eq_refl] -- while the WHOLE record is refused, its [cone_coherence]
 proof being [abstract]ed at Const.v.  But that does NOT localize the
 refusal here, and an earlier revision of this paragraph said it did: the
 two sides of the negative differ ALREADY at the value, refused at a
 point [x : X] and again at the produced cone's leg at [d], both measured.
 So the difference is NOT confined to one law field, no cause is
 isolated, and what holds is the setoid-level identification
 ([coneset_adj_to_is_transpose]).

 EQUALIZERS

 Awodey SS3.3 Example 3.14: in Set the equalizer of [f, g : A → B] is the
 inclusion of [{x ∈ A | f x = g x}].  Riehl SS3.2 Example 3.2.7 says the
 same and adds that it is obtained as the set of cones with summit the
 singleton.

 [HasEqualizers Sets] ALREADY EXISTS THREE TIMES OVER in library files --
 [Sets_HasEqualizers] (Adjunction/GAFT/Sets.v), [SetsEqualizers]
 (Adjunction/CokernelPair.v) and [DiagSets_HasEqualizers]
 (Adjunction/Diagonal/Finite.v) -- so no fourth is added here, and
 the issue's checkbox asking for the class “delivered by name” is already
 met by the first of those.  What is delivered instead is what was
 missing: the CONCRETE presentation and the measured relation to it.

 [sets_eq_obj f g] is Awodey's subset as a sub-setoid, [sets_IsEqualizer]
 its universal property (three one-line obligations: the fork condition IS
 the sigma's witness, commuting is [reflexivity] because the inclusion of
 the mediator IS [h] on the nose, uniqueness is pointwise from the
 competing map's own equation).  No choice, no funext, no decidability.
 [existing_apex_is_limit_obj] pins by [eq_refl] that the EXISTING
 instance's apex is [Sets_limit_obj (APair f g)] and its leg is evaluation
 at [ParX] -- so the existing equalizer is the compatible-family setoid
 over the walking parallel pair, and is neither Awodey's subset nor a cone
 set.  The gap to Awodey's is exactly one application of an existing
 donor, [equalizer_unique] (Structure/Equalizer/Fork.v), delivered as
 [concrete_vs_existing]; the strict form is refused at CONVERSION and is
 pinned.

 RIEHL'S KAROUBI CHECKBOX.  Instance/Sets/Karoubi.v's [sets_split_obj e]
 has carrier [{ a : X & e a ≈ a }].  The issue names the [(id, e)] order,
 and that is what [karoubi_IsEqualizer] delivers.  NOTE THE ASYMMETRY, and
 it is the carrier's: written [e a ≈ a], the [(e, id)] order costs ONE
 [symmetry] against the issue's THREE, so two of the three are the
 order's.  The surviving one is the uniqueness obligation of
 [IsEqualizer]'s [eq_desc], whose goal is [h z ≈ projT1 (v z)]: that
 orientation is the record's field shape and needs [symmetry] at EITHER
 order, measured by compiling the [(e, id)] version with that step and
 without it.  An earlier revision of this paragraph said [(e, id)] needs
 none.  Both compile; only the issue's is shipped, and the other is
 recorded here in prose rather than as a second constant.  No
 idempotency hypothesis is taken: [sets_split_obj] needs none and neither
 does the equalizer.

 A UNIVERSE CONTRAST WORTH KNOWING.  [Parallel]'s constraint block is
 LITERALLY EMPTY, so the equalizer reading carries no [Set] pin at all --
 unlike the discrete reading in Instance/Sets/Complete.v, whose pin is
 [DiscreteCat_Functor]'s.  The asymmetry is the shape functor's, not the
 limit machinery's.

 SEVEN SKETCHES: THE TUPLE FORM

 Theorem 3.95 writes the limit in coordinates: for a shape presented by a
 graph, the limit is the set of vertex-indexed tuples compatible along
 every GENERATING EDGE, with the coordinate projections as legs.  The
 in-tree limit's compatibility quantifies over every ARROW of the shape,
 which over a free category means every PATH.  The bridge is
 [tuple_compat_paths]: a family compatible on generators is compatible
 along every path, by induction on the path.  That is the only new
 MATHEMATICAL content in the section; [tuple_obj]'s setoid obligation and
 the [dpath_fmap] step inside [tuple_bwd] are the rest, and the second is
 flagged at its site as needing a workaround, so neither is an evident
 map.  An earlier revision called this the only new proof content.

 STRONGER THAN THE BOOK, AND THE FILE SAYS SO: the book says “finite
 graph”; [G] here is an ARBITRARY [Quiver], with no finiteness, no
 decidable equality on nodes or edges, and no node-UIP anywhere.  Read the
 [About] of [tuple_iso] for the absence of any such hypothesis.

 The strength is an isomorphism, not an equality, and the [eq_refl] form
 is refused at CONVERSION for the expected reason: the two compatibility
 predicates quantify over paths and over edges respectively.  What DOES
 hold on the nose is recorded by two [eq_refl] Examples: the induced
 functor agrees with the diagram on objects, and the product setoid the
 limit is cut out of IS [Sets_iprod_obj] of the diagram's own vertex
 family.

 SEVEN SKETCHES: PRESENTATION-INDEPENDENCE

 The clause stated alongside the theorem: the limit depends only on the
 generating quiver, so imposed path equations do not affect it.  This is
 CHEAP, and the reason is structural: [Quotient] leaves objects and
 morphisms untouched and coarsens only the hom-setoid, while the limit
 carrier does not read the hom-setoid.  So the carrier is Leibniz-equal
 ([pres_carrier_strict]), the compatibility predicate is Leibniz-equal
 ([pres_compat_strict]), and BOTH legs of [pres_iso] are [fun p => p].

 The OBJECT-level [eq_refl] is nevertheless refused, and that boundary is
 real rather than an artifact of how the statement is written: the carrier
 agrees but the [is_setoid] field does not, its [setoid_equiv] being
 [Sets_limit_obj_obligation_1] applied to two functors that [Compose]
 rebuilds.  It is pinned in the probe, which carries one control of its
 own; the three accepted Examples that locate the refusal in that one
 field -- [pres_fobj_strict], [pres_compat_strict], [pres_carrier_strict]
 -- are in THIS file, at the end of the section, not in the probe.

 WHAT THIS SECTION DOES *NOT* SAY: it is “the limit of a diagram over the
 quotient is the limit of its restriction”, which is the checkbox's own
 phrasing.  It does not by itself say the limit is computed from the
 generating edges -- that is the tuple form above.  The two are not
 composed here; composing them would need
 [presented_restrict] (Construction/Free/Quiver/Presented.v), which is
 not exercised.

 CLOSURE.  86 modules by [coqdep -sort] counting this file; the drop-one
 marginals are [Adjunction/Diagonal/Limit] 14, [Instance/Sets/Karoubi] 5,
 [Theory/Diagram] 2, [Construction/Free/Quiver/Presented] 2,
 [Adjunction/GAFT/Sets] 2, [Structure/Limit/Unique] 1, every other
 [Require] 0.  Nothing depends on this file, so that cost lands on no one.

 STATUS: axiom-free.  [Print Assumptions] reports “Closed under the global
 context” for every constant below; the Makefile's [print-assumptions]
 target audits them by fully qualified name. 

 --------
 Mac Lane，《为在职数学家而作的范畴论》，第2版（GTM 5），SV.1 定理1及其后的备注，印刷版第110页（PDF第119页）；项目编号 [maclane:V.1:thm1]，[maclane:V.1:remark1]。Awodey，《范畴论》（第1版，CMU预印本，2005年9月），SS3.3 示例3.14，印刷版第67页；项目编号 [awodey:3.3:example14]。Fong & Spivak，《组合性中的七个草图》（CUP，2019），SS3.5.3 定理3.95，印刷版第112页；项目编号 [7sketches:3.5.3:thm3.95]。Riehl，《上下文中的范畴论》，第2版，SS3.2 定义3.2.3，定理3.2.4和示例3.2.7，印刷版第93-94页；项目编号 [riehl:3.2:def3]，[riehl:3.2:thm4]，[riehl:3.2:example7]。该构造本身是 Instance/Sets/Complete.v 的内容，以及该文件已经包含的兼容族极限。这个文件是附属部分：比较两个顶点、注释的自然双射、它与对角极限上伴的识别，以及等化器和元组的解读。它是一个叶子 —— 树中的其他部分不依赖它 —— 这就是为什么它可以承载核心无法承受的沉重 [Require]。为什么这些不在 Instance/Sets/Complete.v 中。有两个不同的原因，而且只有第二个是难点。(i) Instance/Sets/Complete.v 的传递闭包包含 33 个模块（[coqdep -sort]，包括文件本身）；[Structure/Limit/Unique] —— 提供 [limit_unique_iso]，即整个比较 —— 使它多一个模块，自然双射模块块消耗四个模块。它们放在这里，数量就是原因。(ii) Adjunction/Diagonal/Limit.v 需要 Category.Instance.Sets.Complete，所以该文件中无法进行伴随识别：那会形成依赖循环。正是这使得此文件是必要的，而不仅仅是为了整洁。

 比较[cone_apex_iso] 是 [limit_unique_iso] 应用于两个极限证人的。两个顶点都是同一图的极限，因此同构和两条腿的交换族都是自动得到的——这一节没有新的证明内容，并且文件也说明了这一点，而不是加以包装。值得强调的，并且由 [eq_refl] 强调的是，对比不是不透明的：它的前腿就是锥集合中介（[cone_apex_iso_to_is_med]），而这两条腿的族正是指定的那些（[cone_apex_iso_leg_cone], [cone_apex_iso_leg_family]）。顶点本身并不相等，并且两次严格尝试都被拒绝：在对象层面出现“无法统一”（一个转换拒绝），因为一个是带有兼容性证据的依赖函数的 sigma，而另一个是 [ACone] 记录。也没有 [≈] 等级可以退回——[Sets] 的对象不携带集合同构，因此尝试是一个解析拒绝（“无法推断隐含参数 Setoid”）。两者都在 Test/ProbeConeSets407.v 中被固定；注意第二个的裸 [Check] 是被接受的，会打印一个开放的 evar，所以驳回命令必须是 [Definition]。

 备注，显示（3）

 “这个证明的关键是（自然）双射

 Cone (X, F) ~= Set (X, Cone ( *, F))                       (3)

 由 tau |--> h 给出，如上。”“natural”周围的括号是书里的，而书并没有证明它——也就是说，这是本期问题的工作项4的前半部分，而这里已经证明了它。[ConeSet_Natural_Iso]在函子范畴[[Sets^op, Sets]之间是一个真正的同构，介于[ConePresheaf F]——作为X的函子的(3)左边，这正是Structure/Cone.v已经存在的——和[Curried_CoHom Sets (cone_apex F)]，即右边。每个自然性条款都由[reflexivity]闭合。[ConeSet_Representable]将同一个同构读作锥预层的可表示性，这正是Structure/UniversalProperty/Limit.v抽象陈述的内容，而且这里已经具体化。

 伴随关系，以及你给它提供的预测Mac Lane 将 (3) 重写为 [Nat (Delta X, F) ~= Set (X, Cone ( *, F))]，并且说“根据极限的定义，这证明了 Lim F ~= Cone( *, F)”。在树中，该伴随是 #353 的 [Diagonal_Limit_Adjunction]，它以 [HasLimitsOfShape] 作为参数——一个极限的选择——而且该识别取决于具体选择的是哪一个。Fed [ConeSet_HasLimitsOfShape]，由锥形集合构造构建，该书的双射是伴随的转置，四个 [eq_refl] 回读表明：伴随的右侧对象是 [cone_apex]，其支架是 [cone_leg_at]，其反向转置具有 [cone_untranspose] 的支架，且其余单位分量是 [cone_leg_at ∘ id]。按其测量等级阅读第三个：它是逐支架说明的，而不是在整个记录上，因为整个记录形式被拒绝——出于同一捐赠者原因，正向转置也被拒绝，见下文两段——这种拒绝被固定在探针中。提供给预先存在的 [Sets_HasLimitsOfShape] -- 它建立在兼容族 Oracle 的 [Sets_Complete] 上 -- 它并不是，也甚至不是相同的类型：将该伴随的移位归属在锥集合陪域上是一个明显的类型不匹配（一个类型拒绝，没有“无法统一”也没有宇宙条款）。这个拒绝在探针中被固定，旁边的锥集合形式作为区分控制。两种读法之间的桥梁是 [cone_apex_iso]。

 所以诚实的表述是条件性的，它是工作项 4 的有趣内容：书中的双射是在锥集合 Oracle 上对对角极限伴随的移位。这里没有任何内容声称它是预先存在的 [Sets_Diagonal_Limit_Adjunction] 的移位。一个等级不是 [eq_refl]，并且本地化比明显的那个还要弱。应用于圆锥的前向换位，与 [cone_transpose] 作为整体态射比较时，在转换时被拒绝。一个供体事实被测量且为真：[Cone_Natural_Transform] 的 [ACone] 往返（Structure/Cone/Const.v）返回的是 LEG FAMILY——往返的 [vertex_map] 是原始的 [vertex_map] 在 [eq_refl]——而整个记录被拒绝，其 [cone_coherence] 证明在 Const.v 中被 [abstract]。但是这并没有在这里本地化拒绝，而这个段落的早期修订版本说是可以：负号两边在值上 ALREADY 已经不同，在 [x : X] 处被拒，以及在所产生圆锥的支腿 [d] 处再次被测量。所以区别并不仅限于某一个法律领域，没有任何原因是孤立的，并且适用的是集合等价级的识别（[coneset_adj_to_is_transpose]）。

 等化器

 Awodey SS3.3 示例 3.14：在 Set 中，[f, g : A → B] 的等化器是 [{x ∈ A | f x = g x}] 的包含。Riehl SS3.2 示例 3.2.7 说的一样，并补充说它是作为顶点为单元素顶点的锥体集合得到的。

 [HasEqualizers Sets] 在库文件中已经存在三次——[Sets_HasEqualizers]（Adjunction/GAFT/Sets.v）、[SetsEqualizers]（Adjunction/CokernelPair.v）和 [DiagSets_HasEqualizers]（Adjunction/Diagonal/Finite.v）——所以这里不再添加第四个，并且问题的复选框要求按名称“提供”的类别已经由第一个文件满足。取而代之的是之前缺失的内容：具体的展示以及与其相关的衡量关系。[sets_eq_obj f g] 是 Awodey 的一个作为子子集类的子集，[sets_IsEqualizer] 它的普遍性质（三个一行的义务：叉条件是 sigma 的证据，交换是 [reflexivity] 因为调解器的包含确实是 [h]，唯一性是从竞争映射自身方程逐点得出的）。没有选择，没有函数扩展，没有可判定性。[existing_apex_is_limit_obj] 被 [eq_refl] 固定，使得现有实例的顶点是 [Sets_limit_obj (APair f g)]，其边是 [ParX] 的值 -- 因此现有的等化器是平行对的兼容族集合，并且既不是 Awodey 的子集也不是锥集合。与 Awodey 的差距恰好是一次现有捐赠者的应用，[equalizer_unique]（Structure/Equalizer/Fork.v），以 [concrete_vs_existing] 交付；严格形式在转换时被拒绝并被固定。RIEHL的KAROUBI复选框。实例/集合/Karoubi.v 的 [sets_split_obj e] 有承载者 [{ a : X & e a ≈ a }]。该问题命名了 [(id, e)] 顺序，而 [karoubi_IsEqualizer] 正是传递的内容。注意这种不对称性，这是承载者的：写作 [e a ≈ a]，[(e, id)] 顺序的成本是一次 [symmetry]，而问题的成本是三次，因此三次中的两次属于该顺序。剩下的一次是 [IsEqualizer] 的 [eq_desc] 所承担的独特性义务，其目标是 [h z ≈ projT1 (v z)]：这种方向是记录的字段形状，并且需要在任一顺序上 [symmetry]，通过编译带有该步骤和不带该步骤的 [(e, id)] 版本来测量。该段的早期修订版本指出 [(e, id)] 不需要任何东西。两者都可以编译；只有问题的被交付，另一个在此以文字记录，而不是作为第二个常量。没有采用幂等性假设：[sets_split_obj] 不需要，均衡器也不需要。

 一个值得了解的宇宙对比。[Parallel] 的约束块实际上是空的，所以均衡器读取根本不携带 [Set] 引脚——这与 Instance/Sets/Complete.v 中的离散读取不同，后者的引脚是 [DiscreteCat_Functor] 的。这个不对称性属于形状函子，而不是极限机制。

 七个素描：元组形式定理 3.95 用坐标写出极限：对于由图表示的形状，极限是沿着每条生成边兼容的顶点索引元组的集合，其坐标投影作为边。树内极限的兼容性量化了形状的每一条箭头，在自由范畴下意味着每一条路径。桥梁是 [tuple_compat_paths]：一族在生成元上兼容的，在路径归纳下沿每条路径也兼容。这是本节中唯一新的数学内容；[tuple_obj] 的集合义务和 [dpath_fmap] 在 [tuple_bwd] 内部的步骤是其余内容，而第二个步骤在其位置上被标记为需解决的方法，所以二者都不是明显的映射。早期版本称其为唯一的新证明内容。比书本更强，而且文件是这么说的：书上说“有限图”；这里的[G]是一个任意的[Quiver]，没有有限性，对节点或边没有可判定的相等性，并且没有任何节点-UIP。关于缺少任何此类假设，请阅读[About]的[tuple_iso]。

 这种强度是一个同构，而不是相等，并且[eq_refl]形式在转换时被拒绝，原因是预料中的：两个兼容性谓词分别对路径和边进行量化。确切成立的内容由两个[eq_refl]记录：诱导函子在对象上与图一致，而极限的乘积集同构于图自身顶点族的[Sets_iprod_obj]。

 七个草图：呈现独立性该定理旁边说明的条款：极限仅依赖于生成的箭图，因此施加的路径方程不会影响它。这是廉价的，其原因是结构性的：[Quotient] 不改变对象和态射，只粗化同态集合，而极限承载不读取同态集合。因此承载是莱布尼茨等价的（[pres_carrier_strict]），兼容性谓词是莱布尼茨等价的（[pres_compat_strict]），并且 [pres_iso] 的两条腿都是 [fun p => p]。对象级别的 [eq_refl] 尽管如此仍被拒绝，而且该边界是真实的，而不是语句书写方式的产物：承载方同意，但 [is_setoid] 字段不同意，其 [setoid_equiv] 被 [Sets_limit_obj_obligation_1] 应用于两个 [Compose] 重建的函子。它被固定在探针中，探针带有一个自己的控制；三个在该字段中定位拒绝的被接受示例——[pres_fobj_strict]、[pres_compat_strict]、[pres_carrier_strict]——在本文件中，该部分末尾，而不在探针中。本节 *未* 说明的内容：它并不是“商上的图的极限就是其限制的极限”，这是勾选框本身的表述。它本身并没有说明极限是从生成边计算的——那是上面元组形式的内容。这里两者并未组合；要组合它们需要 [presented_restrict]（Construction/Free/Quiver/Presented.v），但这里没有使用。

 结尾。按 [coqdep -sort] 计数（包含此文件）共 86 个模块；单独去掉一个边际的情况是 [Adjunction/Diagonal/Limit] 14，[Instance/Sets/Karoubi] 5，[Theory/Diagram] 2，[Construction/Free/Quiver/Presented] 2，[Adjunction/GAFT/Sets] 2，[Structure/Limit/Unique] 1，其余 [Require] 0。没有任何东西依赖此文件，所以这成本不落在任何人身上。状态：无公理。[Print Assumptions] 对下面的每个常量都报告“在全局上下文下已关闭”；Makefile 的 [print-assumptions] 目标通过完全限定名称对它们进行审核。
*)

(* * ** The comparison with the compatible-family limit / * ** 与兼容系列极限的比较 *)

Section Compare.

Context {D : Category}.
Context (F : D ⟶ Sets).

(*
 Both apexes are limits of [F], so [limit_unique_iso] supplies the
 comparison and both leg families with no new proof content. 

 --------
 两个顶点都是 [F] 的极限，因此 [limit_unique_iso] 提供了比较，并为两个边族提供信息，但没有新的证明内容。
*)
Definition cone_apex_iso : Sets_limit_obj F ≅[Sets] cone_apex F :=
  limit_unique_iso (limit_is_alimit (Sets_Limit F)) (cone_set_IsALimit F).

Definition cone_apex_iso_legs :
  (∀ x : D, limit_leg (cone_set_IsALimit F) x ∘ to cone_apex_iso
              ≈ limit_leg (limit_is_alimit (Sets_Limit F)) x) *
  (∀ x : D, limit_leg (limit_is_alimit (Sets_Limit F)) x
              ∘ from cone_apex_iso ≈ limit_leg (cone_set_IsALimit F) x) :=
  limit_unique_iso_legs (limit_is_alimit (Sets_Limit F))
                        (cone_set_IsALimit F).

(* The two leg families are the named ones, on the nose. / 那两个宿腿家族就是指名的那两个，一针见血。 *)
Example cone_apex_iso_leg_cone :
  limit_leg (cone_set_IsALimit F) = cone_leg_at F := eq_refl.

Example cone_apex_iso_leg_family :
  limit_leg (limit_is_alimit (Sets_Limit F)) = Sets_limit_leg F := eq_refl.

(*
 And the comparison is not opaque: its forward leg IS the cone-set
 mediator of Mac Lane's proof.  Read its strength exactly: this is
 [limit_unique_iso]'s forward leg being [limit_med] at ANY two limits of
 ANY diagram, instantiated here -- the generic form is accepted -- so
 what it pins is that this comparison reduces, not anything specific to
 the cone set. 

 --------
 并且这个比较并不模糊：它的前向部分就是 Mac Lane 证明中的锥集合中介。准确地理解它的强度：这是 [limit_unique_iso] 的前向部分在任何图的任意两个极限下都是 [limit_med]，这里进行了实例化——接受通用形式——所以它所固定的是这个比较被简化，而不是锥集合的任何特定内容。
*)
Example cone_apex_iso_to_is_med :
  to cone_apex_iso
  = cone_set_med F (alimit_cone (limit_is_alimit (Sets_Limit F)))
  := eq_refl.

End Compare.

(*
 MAC LANE'S DISCRETE SENTENCE, AT THE CONE SET ITSELF.  “If J is
 discrete, the set Cone( *, F) of J-cones is just the cartesian product
 Pi_j F_j” -- the object the sentence NAMES is the cone set, and
 Instance/Sets/Complete.v's [discrete_iprod_iso] states it of the
 compatible-family apex.  One [iso_compose] carries it across, which is
 what makes the quoted sentence a theorem about its own subject rather
 than about the other oracle.  [{A : Set}] is inherited from
 [discrete_iprod_iso]; see that file's universe note. 

 --------
 麦克莱恩的离散句子位于圆锥集合本身。“如果 J 是离散的，J-圆锥的集合 Cone( *, F) 就是笛卡尔积 Pi_j F_j”——句子所命名的对象是圆锥集合，Instance/Sets/Complete.v 中的 [discrete_iprod_iso] 将其应用于兼容族的顶点。一个 [iso_compose] 将其传递，这正是使引用的句子成为关于其自身主题的定理，而不是关于另一个神谕。[{A : Set}] 是从 [discrete_iprod_iso] 继承的；参见该文件的宇宙注释。
*)
Definition cone_apex_discrete_iprod_iso {A : Set} (f : A -> obj[Sets]) :
  cone_apex (DiscreteCat_Functor f) ≅[Sets] Sets_iprod_obj f :=
  iso_compose (discrete_iprod_iso f)
              (iso_sym (cone_apex_iso (DiscreteCat_Functor f))).

(* * ** The remark: display (3), natural in the apex / * ** 备注：显示 (3)，在顶点自然 *)

Section Remark.

Context {D : Category}.
Context (F : D ⟶ Sets).

(*
 Mac Lane's [tau |--> h]: a cone with apex X becomes a map into the cone
 set, sending [e] to the cone [tau e]. 

 --------
 Mac Lane 的 [tau |--> h]：一个顶点为 X 的锥体变为进入锥体集合的映射，将 [e] 发送到锥体 [tau e]。
*)
Program Definition cone_transpose (X : obj[Sets]) :
  fobj[ConePresheaf F] X
    ~{Sets}~> fobj[Curried_CoHom Sets (cone_apex F)] X := {|
  morphism := fun p =>
    {| morphism := fun e =>
         {| vertex_map := fun d => {| morphism := fun _ =>
              @vertex_map _ _ _ _ p d e |} |} |}
|}.
Next Obligation. intros X p e d u v Huv; reflexivity. Qed.
Next Obligation.
  intros X p e x y f u; exact (@cone_coherence _ _ _ _ p x y f e).
Qed.
Next Obligation.
  intros X p e e' Hee' d u.
  exact (proper_morphism (@vertex_map _ _ _ _ p d) e e' Hee').
Qed.
Next Obligation. intros X p q Hpq e d u; exact (Hpq d e). Qed.

(* The inverse: reindex the tautological cone along h, i.e. compose each leg of display (2) with h. / 逆过程：沿着 h 对同义锥重新索引，即将显示（2）的每一条支线与 h 组合。 *)
Program Definition cone_untranspose (X : obj[Sets]) :
  fobj[Curried_CoHom Sets (cone_apex F)] X
    ~{Sets}~> fobj[ConePresheaf F] X := {|
  morphism := fun h => {| vertex_map := fun d => cone_leg_at F d ∘ h |}
|}.
Next Obligation.
  intros X h x y f e; simpl.
  exact (@cone_coherence _ _ _ _ (h e) x y f ttt).
Qed.
Next Obligation. intros X h h' Hhh' d e; simpl; exact (Hhh' e d ttt). Qed.

(* One round trip is definitional pointwise; the other spends the singleton, exactly once, in the same [destruct] the mediator spends. / 一次往返是定义上的逐点；另一次则在相同的 [destruct] 中花费单例，正如中介所花费的那样，且仅一次。 *)
Lemma cone_transpose_round (X : obj[Sets]) (p : fobj[ConePresheaf F] X) :
  cone_untranspose X (cone_transpose X p) ≈ p.
Proof. intros d e; reflexivity. Qed.

Lemma cone_untranspose_round (X : obj[Sets])
  (h : fobj[Curried_CoHom Sets (cone_apex F)] X) :
  cone_transpose X (cone_untranspose X h) ≈ h.
Proof. intros e d u; destruct u; reflexivity. Qed.

(* Display (3) at a fixed apex. / 在固定顶点显示（3）。 *)
Program Definition cone_hom_iso (X : obj[Sets]) :
  @Isomorphism Sets (fobj[ConePresheaf F] X)
                    (fobj[Curried_CoHom Sets (cone_apex F)] X) := {|
  to := cone_transpose X; from := cone_untranspose X
|}.
Next Obligation. intros X; exact (cone_untranspose_round X). Qed.
Next Obligation. intros X; exact (cone_transpose_round X). Qed.

(* The book's parenthetical “(natural)”, proved. Both directions. / 这本书的括号“（自然）”，被证明了。两种方向。 *)
Lemma cone_transpose_natural (X Y : obj[Sets]) (g : X ~{Sets^op}~> Y) :
  fmap[Curried_CoHom Sets (cone_apex F)] g ∘ cone_transpose X
    ≈ cone_transpose Y ∘ fmap[ConePresheaf F] g.
Proof. intros p e d u; reflexivity. Qed.

Lemma cone_untranspose_natural (X Y : obj[Sets]) (g : X ~{Sets^op}~> Y) :
  fmap[ConePresheaf F] g ∘ cone_untranspose X
    ≈ cone_untranspose Y ∘ fmap[Curried_CoHom Sets (cone_apex F)] g.
Proof. intros h d e; simpl; reflexivity. Qed.

(* Display (3) as an isomorphism of functors of the apex. / 将 (3) 显示为顶点函子之间的同构。 *)
Program Definition ConeSet_Natural_Iso :
  @Isomorphism ([Sets^op, Sets])
               (ConePresheaf F) (Curried_CoHom Sets (cone_apex F)) := {|
  to   := {| transform := cone_transpose |};
  from := {| transform := cone_untranspose |}
|}.
Next Obligation. intros X Y g; exact (cone_transpose_natural X Y g). Qed.
Next Obligation. intros X Y g p e d u; reflexivity. Qed.
Next Obligation. intros X Y g; exact (cone_untranspose_natural X Y g). Qed.
Next Obligation. intros X Y g h e d; simpl; reflexivity. Qed.
Next Obligation. intros X h e d u; destruct u; reflexivity. Qed.
Next Obligation. intros X p d e; reflexivity. Qed.

(* The components are the two named maps, on the nose. / 组件就是那两个明明白白命名的地图。 *)
Example coneset_natural_iso_to (X : obj[Sets]) :
  transform[to ConeSet_Natural_Iso] X = cone_transpose X := eq_refl.

Example coneset_natural_iso_from (X : obj[Sets]) :
  transform[from ConeSet_Natural_Iso] X = cone_untranspose X := eq_refl.

(* The cone presheaf is representable, represented by the cone set. / 圆锥预层是可表示的，由圆锥集合表示。 *)
Program Definition ConeSet_Representable : Representable (ConePresheaf F) := {|
  repr_obj := (cone_apex F : obj[Sets^op]);
  represented := {| to := _; from := _ |}
|}.
Next Obligation. exact (from ConeSet_Natural_Iso). Defined.
Next Obligation. exact (to ConeSet_Natural_Iso). Defined.
Next Obligation. exact (iso_from_to ConeSet_Natural_Iso). Qed.
Next Obligation. exact (iso_to_from ConeSet_Natural_Iso). Qed.

End Remark.

(* * ** The adjunction reading of the remark / * ** 该言论的附加解读 *)

(* The cone-set construction as a choice of limits of a fixed shape. / 作为固定形状的极限选择的锥形集构造。 *)
Definition ConeSet_HasLimitsOfShape (J : Category) :
  HasLimitsOfShape J Sets := fun F => cone_set_Limit F.

(*
 #353's adjunction, fed the cone-set oracle.  Stated outside the section
 below so that [J] is an explicit argument, as it is for the oracle. 

 --------
 #353 的附加项，提供给了圆锥集合预言机。 在下面的部分外部说明，以便 [J] 能成为一个显式参数，就像它对预言机一样。
*)
Definition ConeSet_Diagonal_Limit_Adjunction (J : Category) :
  @Diagonal Sets J ⊣ LimitFunctor (ConeSet_HasLimitsOfShape J) :=
  Diagonal_Limit_Adjunction (ConeSet_HasLimitsOfShape J).

Section Adjunction.

Context {J : Category}.
Context (F : J ⟶ Sets).

(* Four strict readbacks: the adjoint's value, its leg, its backward transposition, and its counit. / 四个严格的回读：伴随的值，它的腿，它的反向转置，以及它的余单位。 *)
Example coneset_lim_obj :
  lim_obj (ConeSet_HasLimitsOfShape J) F = cone_apex F := eq_refl.

Example coneset_lim_leg (j : J) :
  lim_leg (ConeSet_HasLimitsOfShape J) F j = cone_leg_at F j := eq_refl.

Example coneset_adj_from_is_untranspose (X : obj[Sets])
  (h : X ~{Sets}~> cone_apex F) (j : J) :
  transform[from (@adj _ _ _ _ (ConeSet_Diagonal_Limit_Adjunction J) X F) h] j
  = @vertex_map _ _ _ _ (cone_untranspose F X h) j := eq_refl.

(*
 This one discriminates nothing and is kept for the display: it IS
 Adjunction/Diagonal/Limit.v's [lim_counit_component_strict] at this
 oracle, and the same statement is accepted at an arbitrary
 [HasLimitsOfShape] and at the pre-existing [Sets] oracle.  What carries
 content is [coneset_lim_leg] above, which names [cone_leg_at]. 

 --------
 这个不歧视任何东西，并且被保留用于展示：它是 Adjunction/Diagonal/Limit.v 的 [lim_counit_component_strict] 在这个 oracle 上，并且相同的声明在任意 [HasLimitsOfShape] 和预先存在的 [Sets] oracle 上也被接受。承载内容的是上面的 [coneset_lim_leg]，它命名为 [cone_leg_at]。
*)
Example coneset_counit (j : J) :
  transform[lim_counit (ConeSet_HasLimitsOfShape J) F] j
  = cone_leg_at F j ∘ id := eq_refl.

(*
 The forward transposition, at the setoid grade.  Its [eq_refl] form is
 refused at CONVERSION and is pinned in the probe.  The header says what
 is and is not localized: the [ACone] round trip's leg family does return
 on the nose, but these two sides differ already at a point, so the
 refusal is not attributed to the coherence field. 

 --------
 前向换位，在集合等级下。它的 [eq_refl] 形式在转换时被拒绝，并且在探针中被固定。标题说明了什么被本地化以及什么没有被本地化：[ACone] 往返的腿族确实能够精确返回，但这两个侧面在某一点上已经不同，因此拒绝并不归因于相干场。
*)
Lemma coneset_adj_to_is_transpose (X : obj[Sets]) (p : ACone X F) :
  to (@adj _ _ _ _ (ConeSet_Diagonal_Limit_Adjunction J) X F)
     (snd (Cone_Natural_Transform F X) p)
  ≈ cone_transpose F X p.
Proof. intros e d u; reflexivity. Qed.

End Adjunction.

(* * ** Equalizers: Awodey's concrete presentation / * ** 均衡器：Awodey的具体展示 *)

Section Equalizers.

Context {X Y : SetoidObject}.
Context (f g : X ~{Sets}~> Y).

(* The existing [HasEqualizers Sets]' apex is the compatible-family setoid over the walking parallel pair, and its leg is evaluation at [ParX]. / 现有的 [HasEqualizers Sets] 顶点是行走平行对上的兼容族等价集合，其支腿是在 [ParX] 上的求值。 *)
Example existing_apex_is_limit_obj :
  projT1 (@equalizer Sets Sets_HasEqualizers X Y f g)
  = Sets_limit_obj (APair f g) := eq_refl.

Example existing_leg_is_limit_leg :
  projT1 (projT2 (@equalizer Sets Sets_HasEqualizers X Y f g))
  = Sets_limit_leg (APair f g) ParX := eq_refl.

(* Awodey's [{x ∈ A | f x = g x}], as a sub-setoid. / 作为子等价集的 Awodey 的 [{x ∈ A | f x = g x}]。 *)
Program Definition sets_eq_obj : SetoidObject := {|
  carrier   := { a : X & f a ≈ g a };
  is_setoid := {| equiv := fun p q => `1 p ≈ `1 q |}
|}.
Next Obligation. equivalence. Qed.

Program Definition sets_eq_incl : sets_eq_obj ~{Sets}~> X := {|
  morphism := fun p => `1 p
|}.
Next Obligation. intros p q Hpq; exact Hpq. Qed.

Program Definition sets_eq_desc {Z : SetoidObject} (h : Z ~{Sets}~> X)
  (Hh : f ∘ h ≈ g ∘ h) : Z ~{Sets}~> sets_eq_obj := {|
  morphism := fun z => (h z; Hh z)
|}.
Next Obligation. intros Z h Hh z z' Hz; simpl; now rewrite Hz. Qed.

(* “with unique factorization because the inclusion is monic”. / 因为包含是首一的，所以具有唯一分解性。 *)
Program Definition sets_IsEqualizer :
  IsEqualizer f g sets_eq_obj sets_eq_incl := {|
  fork_eq := _;
  eq_desc := fun Z h Hh => {| unique_obj := sets_eq_desc h Hh |}
|}.
Next Obligation. intros p; exact (`2 p). Qed.
Next Obligation. intros Z h Hh z; reflexivity. Qed.
Next Obligation. intros Z h Hh v Hv z; simpl; symmetry; exact (Hv z). Qed.

(* The existing instance, read as an elementary equalizer. / 现有实例，可作为一个初级均衡器来读取。 *)
Definition existing_IsEqualizer :
  IsEqualizer f g (Sets_limit_obj (APair f g))
              (Sets_limit_leg (APair f g) ParX) :=
  projT2 (projT2 (@equalizer Sets Sets_HasEqualizers X Y f g)).

(* The gap between Awodey's presentation and the existing one is one application of [equalizer_unique]. The strict form is refused at CONVERSION and is pinned in the probe. / Awodey 的演示与现有演示之间的差距是 [equalizer_unique] 的一次应用。严格形式在 CONVERSION 时被拒绝，并固定在探针中。 *)
Definition concrete_vs_existing :
  @Isomorphism Sets sets_eq_obj (Sets_limit_obj (APair f g)) :=
  equalizer_unique f g sets_IsEqualizer existing_IsEqualizer.

End Equalizers.

(** ** Riehl's Karoubi instance / ** Riehl 的 Karoubi 实例 *)

Section Karoubi.

Context {X : SetoidObject}.
Context (e : X ~{Sets}~> X).

(*
 Instance/Sets/Karoubi.v's fixed-point sub-setoid, recorded as the
 [(id, e)] equalizer the issue names.  No idempotency is required.  The
 carrier is spelled [e a ≈ a], so this order costs two [symmetry] steps
 MORE than [(e, id)] does; the third, in the uniqueness obligation, is
 needed at either order.  See the header. 

 --------
 实例/集合/Karoubi.v 的固定点子等价类，记录为 [(id, e)] 等化器问题名称。不需要幂等性。载体拼写为 [e a ≈ a]，因此这个顺序比 [(e, id)] 多花费两个 [symmetry] 步；在唯一性义务中，第三个在任一顺序下都是需要的。参见标题。
*)
Program Definition karoubi_med {Z : SetoidObject} (h : Z ~{Sets}~> X)
  (Hh : @id Sets X ∘ h ≈ e ∘ h) : Z ~{Sets}~> sets_split_obj e := {|
  morphism := fun z => (h z; _)
|}.
Next Obligation. intros Z h Hh z; simpl; symmetry; exact (Hh z). Qed.
Next Obligation. intros Z h Hh z z' Hz; simpl; now rewrite Hz. Qed.

Program Definition karoubi_IsEqualizer :
  IsEqualizer (@id Sets X) e (sets_split_obj e) (sets_split_s e) := {|
  fork_eq := _;
  eq_desc := fun Z h Hh => {| unique_obj := karoubi_med h Hh |}
|}.
Next Obligation. intros p; simpl; symmetry; exact (`2 p). Qed.
Next Obligation. intros Z h Hh z; reflexivity. Qed.
Next Obligation. intros Z h Hh v Hv z; simpl; symmetry; exact (Hv z). Qed.

End Karoubi.

(* * ** Seven Sketches: the limit in coordinates / * ** 七个草图：坐标中的极限 *)

Section Tuple.

Context {G : Quiver}.
Context (D : Diagram G Sets).

(* Compatibility along the GENERATING EDGES -- the book's condition. / 生成边缘的兼容性——书的状态。 *)
Definition tuple_compat (x : ∀ i : G, D i) : Type :=
  ∀ (i j : G) (e : edges i j), dedge D e (x i) ≈ x j.

(*
 The bridge, and the section's only new mathematical content: a family
 compatible on generators is compatible along every path.  Two smaller
 proofs sit below it -- [tuple_obj]'s setoid obligation and the
 [dpath_fmap] step inside [tuple_bwd]. 

 --------
 桥梁，以及本节唯一的新数学内容：在生成元上兼容的族沿每条路径都兼容。下面有两个较小的证明——[tuple_obj] 的集合义务和 [tuple_bwd] 内的 [dpath_fmap] 步骤。
*)
Lemma tuple_compat_paths (x : ∀ i : G, D i) (H : tuple_compat x)
  {i j : G} (p : tlist edges i j) : dpath D p (x i) ≈ x j.
Proof.
  induction p as [ | a b e p IH ]; simpl.
  - reflexivity.
  - rewrite <- IH; now rewrite (H _ _ e).
Qed.

(* What agrees on the nose. / 正好符合。 *)
Example tuple_fobj_strict (i : G) : fobj[FunctorOfDiagram D] i = D i
  := eq_refl.

Example tuple_inner_strict :
  Sets_iprod_obj (fun d : FreeOnQuiver G => fobj[FunctorOfDiagram D] d)
  = Sets_iprod_obj (fun i : G => D i) := eq_refl.

(* The book's set of tuples. / 书中的元组集合。 *)
Program Definition tuple_obj : SetoidObject := {|
  carrier   := { x : Sets_iprod_obj (fun i : G => D i) & tuple_compat x };
  is_setoid := {| equiv := fun p q => `1 p ≈ `1 q |}
|}.
Next Obligation.
  constructor.
  - intros p i; reflexivity.
  - intros p q Hpq i; symmetry; exact (Hpq i).
  - intros p q r Hpq Hqr i; transitivity (`1 q i);
    [exact (Hpq i)|exact (Hqr i)].
Qed.

(* Forward: restrict the path condition to single edges. / 前向：将路径条件限制为单边。 *)
Program Definition tuple_fwd :
  Sets_limit_obj (FunctorOfDiagram D) ~{Sets}~> tuple_obj := {|
  morphism := fun p => (`1 p ; fun i j e => _)
|}.
Next Obligation. intros p i j e; exact (`2 p i j (tlist_singleton e)). Defined.
Next Obligation. intros p q Hpq i; exact (Hpq i). Qed.

(* Backward: extend along paths. The natural [rewrite <- (dpath_fmap D f)] is stuck on an unresolved [ProperProxy]; the explicit [transitivity] through [dpath] is what goes through. / 向后：沿路径延伸。自然的 [rewrite <- (dpath_fmap D f)] 卡在未解决的 [ProperProxy] 上；通过 [dpath] 的明确 [transitivity] 才是通过的。 *)
Program Definition tuple_bwd :
  tuple_obj ~{Sets}~> Sets_limit_obj (FunctorOfDiagram D) := {|
  morphism := fun p => (`1 p ; fun i j f => _)
|}.
Next Obligation.
  intros p i j f; simpl in f.
  transitivity (dpath D f (`1 p i)).
  - symmetry; exact (dpath_fmap D f (`1 p i)).
  - exact (tuple_compat_paths (`1 p) (`2 p) f).
Defined.
Next Obligation. intros p q Hpq i; exact (Hpq i). Qed.

(* Theorem 3.95: the limit IS the set of compatible tuples. / 定理 3.95：极限就是兼容元组的集合。 *)
Program Definition tuple_iso :
  @Isomorphism Sets (Sets_limit_obj (FunctorOfDiagram D)) tuple_obj := {|
  to := tuple_fwd; from := tuple_bwd
|}.
Next Obligation. intros p i; reflexivity. Qed.
Next Obligation. intros p i; reflexivity. Qed.

(* “with the coordinate projections as the legs”. / “以坐标投影作为边” *)
Program Definition tuple_proj (i : G) : tuple_obj ~{Sets}~> D i := {|
  morphism := fun p => `1 p i
|}.
Next Obligation. intros i p q Hpq; exact (Hpq i). Qed.

Lemma tuple_proj_is_leg (i : G) :
  tuple_proj i ∘ to tuple_iso ≈ Sets_limit_leg (FunctorOfDiagram D) i.
Proof. intros p; reflexivity. Qed.

Lemma tuple_proj_is_leg_inv (i : G) :
  Sets_limit_leg (FunctorOfDiagram D) i ∘ from tuple_iso ≈ tuple_proj i.
Proof. intros p; reflexivity. Qed.

End Tuple.

(* * ** Seven Sketches: presentation-independence / * ** 七个草图：呈现独立性 *)

Section Presentation.

Context (G : Quiver).
Context (R : PathRel G).
Context (S : PresentedQuiver G R ⟶ Sets).

(* The restriction of S along the quotient projection. / 沿商投影对 S 的限制。 *)
Definition Srestr : FreeOnQuiver G ⟶ Sets := S ◯ PresentedQuiverProj G R.

(*
 The imposed equations touch neither the objects nor the compatibility
 predicate nor the carrier -- only the hom-setoid, which the limit
 carrier does not read. 

 --------
 所施加的方程既不涉及对象，也不涉及兼容谓词或承载体——只涉及同态等价集合，而极限承载体并不读取它。
*)
Example pres_fobj_strict (i : G) : fobj[S] i = fobj[Srestr] i := eq_refl.

Example pres_compat_strict
  (x : Sets_iprod_obj (fun d : PresentedQuiver G R => fobj[S] d)) :
  Sets_limit_compatible S x = Sets_limit_compatible Srestr x := eq_refl.

Example pres_carrier_strict :
  Sets_limit_carrier S = Sets_limit_carrier Srestr := eq_refl.

Program Definition pres_fwd :
  Sets_limit_obj S ~{Sets}~> Sets_limit_obj Srestr := {|
  morphism := fun p => p
|}.
Next Obligation. intros p q Hpq i; exact (Hpq i). Qed.

Program Definition pres_bwd :
  Sets_limit_obj Srestr ~{Sets}~> Sets_limit_obj S := {|
  morphism := fun p => p
|}.
Next Obligation. intros p q Hpq i; exact (Hpq i). Qed.

(*
 Both legs are the identity on elements.  The OBJECT-level [eq_refl] is
 nevertheless refused; see the header, and the probe. 

 --------
 两条腿在元素上都是恒等的。然而，OBJECT级别的 [eq_refl] 被拒绝；请参见头部和探针。
*)
Program Definition pres_iso :
  @Isomorphism Sets (Sets_limit_obj S) (Sets_limit_obj Srestr) := {|
  to := pres_fwd; from := pres_bwd
|}.
Next Obligation. intros p i; reflexivity. Qed.
Next Obligation. intros p i; reflexivity. Qed.

Lemma pres_iso_legs (i : G) :
  Sets_limit_leg Srestr i ∘ to pres_iso ≈ Sets_limit_leg S i.
Proof. intros p; reflexivity. Qed.

Lemma pres_iso_legs_inv (i : G) :
  Sets_limit_leg S i ∘ from pres_iso ≈ Sets_limit_leg Srestr i.
Proof. intros p; reflexivity. Qed.

End Presentation.
