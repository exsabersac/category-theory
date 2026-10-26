Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pushout.Split.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.

Generalizable All Variables.

(* * * Pushouts in Grp: the free product with amalgamation / * * 群中的推挤：带合并的自由积 *)

(*
 Book: Mac Lane, “Categories for the Working Mathematician” (2nd ed.),
 §III.3, book p. 66 / PDF p. 75 (maclane:III.3:remark3)
 nLab:      https://ncatlab.org/nlab/show/pushout
 Wikipedia: https://en.wikipedia.org/wiki/Free_product  (amalgamation)

 Mac Lane's remark that pushouts exist in Grp, with the classical
 refinement that monic legs give monic injections and identify the
 vertex as the free product with amalgamation.

 AN ERRATUM IN THE ISSUE (#325).  Its “Current state” paragraph says
 “The Top clause and the entire Grp clause are absent -- no Top or Grp
 category in-tree”.  That was true when the catalog was written and is
 FALSE now: Instance/Grp.v and Instance/Top.v both exist, several such
 categories having been built earlier in the same campaign.  What was
 genuinely absent is the pushouts, and that is what this file and
 Instance/Top/Pushout.v supply.

 THE CONSTRUCTION.  B *_A C is presented by generators and relations,
 in the inductive-setoid-quotient idiom of Instance/Mod/Free.v and
 Instance/Ab/Tensor.v: [AmTerm] is a formal word over the two carriers
 with the three group formers, and [am_eq] is the congruence generated
 by exactly (i) the two groups' own equivalences, (ii) multiplicativity
 of the two insertions, (iii) the amalgamation [am_l (f a) ~ am_r (g a)],
 (iv) the three left-handed group laws, (v) congruence for the two
 operations, and (vi) symmetry and transitivity.

 WHAT THAT PRESENTATION BUYS, MEASURED.  Every group law is a
 CONSTRUCTOR, so [AmalgamGrp] is a record literal with NO proof
 obligation of its own.  [am_eval] is a [Fixpoint], so the mediator's
 multiplication law closes by [reflexivity] -- recorded, not inferred
 from which tactic fired, by the [eq_refl] controls
 [ctl_grp_med_unit] / [ctl_grp_med_mul] in Test/ProbePushoutGrpTop.v.
 Two facts are DERIVED rather than posted: reflexivity of [am_eq]
 ([am_eq_refl], the [am_one] case going through [ae_unit_l am_one] and
 its own symmetry), and unit-preservation by the two insertions
 (Instance/Grp.v's [Build_GrpHom'], whose redundancy argument is
 cancellation in the quotient).  The UMP costs two inductions: one
 over the CONGRUENCE ([am_eval_respects], twelve cases, of which the
 glue case is the only consumer of the cocone hypothesis) and one over
 the WORD ([am_med_unique], five cases).  The file carries two more
 outside the UMP -- [am_eq_refl] and [Grp_Cocartesian]'s
 [fork_respects] -- so four in total; an earlier draft said “the whole
 price is two inductions”, which undercounted.

 WHAT IS PROVED, AND AT WHAT STRENGTH.  [Grp_HasPushouts] is the
 deliverable.  The chosen pushout's apex and both injections are the
 hand-built ones at LEIBNIZ EQUALITY ([Grp_pushout_apex_is_AmalgamGrp]
 and siblings, [eq_refl]), as are the carrier and all three group
 operations.  [pushout_med] is NOT [am_med] on the nose: Structure/
 Pushout.v states [pushout_ump] as a [Qed] lemma, so [unique_obj] is
 applied to an opaque constant -- the equation holds up to [≈]
 ([Grp_pushout_med_is_am_med]) and the strict form is a pinned negative
 with DONOR OPACITY as its diagnosed cause, paired with the identical
 negative on the Top side so the cause is visibly not about groups.

 MAC LANE'S MONIC-LEGS REFINEMENT: DELIVERED AT SPLIT STRENGTH, AND THE
 GAP IS STATED RATHER THAN GLOSSED.  [Grp_split_legs_monic_injections]
 proves that if both legs SPLIT then both injections are monic, through
 Structure/Pushout/Split.v, where the argument is generic: feed the
 cocone [(id, f ∘ retraction)] to the universal property.  Read down to
 elements by Instance/Grp.v's own [Grp_injectivity_is_monic], this says
 the two insertions are INJECTIVE ([am_inj1_injective],
 [am_inj2_injective]).  The refinement for merely MONIC legs is NOT
 delivered.  It is, for groups, the Schreier normal-form theorem for
 amalgamated free products, whose usual proof (van der Waerden's trick)
 builds an action on alternating normal forms and so must CHOOSE coset
 transversals for f(A) in B and g(A) in C; carrying those transversals
 as data would be the house-idiom fix, and the remaining development --
 normal forms, the action, its well-definedness on the congruence -- is
 a large piece of combinatorial group theory that is not attempted here.
 No claim is made that the split hypothesis is necessary; it is not, and
 no in-tree witness separates “monic” from “split monic” in Grp either,
 so the strictness of the gap is argued rather than proved.

 AND THE OTHER HALF OF MAC LANE'S SENTENCE IS DEFINITIONAL, NOT PROVED.
 “The vertex is the amalgamated product” holds here because the vertex
 IS the presented group B *_A C by construction.  Nothing below relates
 it to an independent definition -- via normal forms, or via a subgroup
 generated inside some ambient group -- so this is an identification by
 fiat of notation, and the reader should not read it as a theorem.

 THE FREE PRODUCT, AND WHY THIS SUBSUMES A SEPARATE ISSUE.
 [Grp_free_product] is an INSTANCE of the amalgamated product rather
 than a second construction, and both its injections are split monic
 with NO hypothesis, because each constant leg factors through the
 other.  Read that precisely, because an earlier draft of this header
 overstated it: what is discharged is the strictly weaker FACTORIZATION
 hypothesis ([Grp_fp_inl_Section] goes through
 [am_inj1_Section_of_factor], not [am_inj1_Section_of_Retraction]), and
 Mac Lane's own monic-legs hypothesis is in fact FALSE for this span --
 the legs are CONSTANT maps, which are not injective into a nontrivial
 group and so not monic.  This is therefore Mac Lane's CONCLUSION
 reached by a different and weaker hypothesis, NOT an instance of his
 refinement.  [Grp_Cocartesian] then
 exhibits the free product as the COPRODUCT of Grp, which the tree did
 not have (issue #1194 owns the Grp free product; nothing in tree
 instantiated [Cocartesian Grp]).  CROSS-REFERENCE, and read it
 precisely: the GENERAL bridge “a pushout over the initial object is the
 binary coproduct” is open issue #862 (Seven Sketches 6.2.3) and is NOT
 built here.  What is built is the ad-hoc Grp instance, in which the
 pushout's commutation hypothesis is discharged once by [Grp_fp_cocone]
 and what remains is literally the coproduct's universal property.

 THE SPAN IS THE CONSTANT ONE, NOT THE ZERO OBJECT, AND THAT IS A
 UNIVERSE DECISION.  Classically the free product is the pushout over
 the TRIVIAL group, and that span's legs even SPLIT --
 [Grp_zero_hom_Section] proves it, its retraction being [Grp_one].  But
 Instance/Grp.v declares [Grp_zero_hom] over [GrpObject@{Set Set Set}]
 (and [Grp_trivial@{u}] over [GrpObject@{u u Set}], one binder where the
 record wants more), the donor defect Instance/Grp/Quotient/Colimit.v
 already records and which confines that whole file to [Set]-sized
 groups.  Building the free product on it would inherit the pin.  It is
 built on the CONSTANT legs instead, which needs no zero object: the
 cocone condition is automatic because every homomorphism preserves the
 unit ([Grp_fp_cocone]), and each leg factors through the other by a
 third constant map ([grp_const_absorb]).  [Grp_zero_hom_Section] is
 kept as the honest record of the route not taken.  CORRECTION (#450):
 the donor pin this paragraph describes is lifted -- #450 wrote out the
 universes of Instance/Grp.v's zero-object constants in place, and
 [About] now reads [Grp_zero_hom@{u p}] over [GrpObject@{p p p}] and
 [Grp_zero_hom_Section@{u u0}] over [GrpObject@{u0 u0 u0}], with no
 binder instantiated at [Set] and no [= Set] constraint in either: the
 one [Set] in each constraint block is [Grp]'s own lower bound
 [Set < u] on its object universe.  The zero-object route would
 therefore no longer inherit a pin; the constant-leg construction is
 kept as it stands.

 UNIVERSES, MEASURED IN THE CONSTRAINT BLOCKS, WITH THE CAUSE PROBED.
 Two separate facts, and they point opposite ways.

 RE-MEASURED after the PR “algebraic carriers are sets” (2026-09-17).
 The [PropEquiv] field puts [Set+1] into [GrpObject]'s sort, which shows up
 as a [Set < _] clause in several of the blocks below; the readbacks are
 restated in place and the ones that became false are marked as such.

 (1) [AmalgamGrp@{u u0 .. u10}] displays THREE separate universe triples
 in its binder -- one per group -- while its constraint block contains
 [u = u0], ..., [u = u7]: those nine collapse.  (An earlier revision said
 [@{u u0 .. u8}] and “all nine”; the field added two more universes, so
 there are twelve in the binder and the collapsing family is still the
 nine the three group triples contribute.)  Reading the binder alone
 gets this wrong.  But the identification is NOT the amalgamation's
 doing, and that is probed rather than assumed: the bare definition
 [fun (A B : GrpObject) (f : @hom Grp A B) => B], which mentions no
 pushout at all, already elaborates at [GrpObject@{u0 u0 u0}] for BOTH
 objects.  Naming a single Grp hom is what identifies the levels; the
 amalgam adds nothing.  [Grp_HasPushouts@{u u0}] correspondingly carries
 [Set < u0] and [u < u0].

 (2) NO [Set] APPEARS ANYWHERE IN THIS FILE'S PRINCIPAL CONSTANTS -- this
 claim is FALSE since the PR “algebraic carriers are sets” (2026-09-17),
 and the correction matters more than the claim did.  Measured now:
 [Grp_free_product@{u u0 u1 u2}] is
 [GrpObject@{u0 u0 u0} -> GrpObject@{u0 u0 u0} -> GrpObject@{u u0 u1}]
 with [Set < u2] and [u0 < u2]; [Grp_HasPushouts@{u u0}] carries
 [Set < u0] and [u < u0]; [Grp_Cocartesian@{u u0}] carries [Set < u] and
 [u0 < u].  Every one of these [Set] clauses is a STRICT LOWER BOUND
 ([Set < _]) and not an identification ([_ = Set]), so nothing is pinned
 AT [Set]: the constants still apply at groups of any carrier level above
 [Set], which is what the constant-leg span was chosen to buy, and
 [Unset Universe Minimization ToSet] (Lib.v) keeps carrier universes
 off [Set] anyway.  What is no longer true is the absence of the token.
 The BOUNDARY is guarded in
 Test/ProbePushoutGrpTop.v rather than asserted: two formability
 negatives reject the DONOR constants [Grp_zero_hom] and
 [Grp_zero_hom_Section] at a group declared strictly above [Set] (a
 genuine “Cannot enforce Set = bg”), against controls that form
 [AmalgamGrp], the chosen pushout, [Grp_free_product], [Grp_fp_inl] and
 [grp_const] at that very level, plus controls naming the two donor
 constants at [Set]-level groups so the negatives are about the universe
 and not about a missing reference.  (CORRECTION, #450: the donor pin is
 lifted, and the two negatives are controls there since; see that
 probe's correction.)

 NON-VACUITY.  A negative fact about a generated congruence cannot come
 from induction on it, so every separation here maps OUT of the quotient
 through a concrete homomorphism into [Z2]: [fp_generators_distinct]
 shows the free product does not merge the two summands' generators, and
 [fp_inl_injective] that it does not merge distinct elements of one
 summand.  THE CONTRAST that makes the amalgamation content rather than
 bookkeeping is [amalgam_over_Z2_merges]: over the SAME two groups,
 amalgamating along the identity DOES merge the very pair the free
 product keeps apart.

 WHAT IS NOT DELIVERED.  No normal form, hence no word problem, no
 coefficient uniqueness and no decision procedure for [am_eq]; the
 Schreier refinement above; no proof that the split hypothesis is
 strictly weaker than monicity (no in-tree monic-but-not-split group
 homomorphism is exhibited); no HNN extension; no Bass-Serre theory; no
 van Kampen theorem, and in particular no connection to
 Instance/Top/FundamentalGroupoid.v; no functoriality of the pushout in
 the span; no comparison with Instance/Grp/Free.v's free group (the free
 product of two free groups is not shown free); and no infinite/indexed
 free products.  (Since #450, Instance/Grp/Colimit.v has every colimit
 of groups within its shape discipline, indexed coproducts among them, from the adjoint
 functor theorem -- as an existence result, not as words.)  The
 [Grp_Cocartesian] instance is registered [#[export]], so importers
 acquire it; no LIBRARY file imports this one -- only
 Test/ProbePushoutGrpTop.v does.  CORRECTION (#450): that list was
 short by one already at the parent commit e139ecfb, where [git grep]
 for a [Require] of Category.Instance.Grp.Pushout finds
 Test/ProbeGrpProp.v as well; and since #450 a library file,
 Instance/Grp/Colimit.v, imports it, to prove that its
 adjoint-functor-theorem coproduct agrees with this file's
 ([Grp_coproduct_agrees]), and it passes every [Cocartesian] instance
 explicitly so that the exported one is never picked up silently. 

 --------
 书籍：Mac Lane，《为在职数学家准备的范畴论》（第2版），
 第III.3节，书籍第66页 / PDF第75页（maclane:III.3:remark3）
 nLab:       https://ncatlab.org/nlab/show/pushout 
 维基百科:  https://en.wikipedia.org/wiki/Free_product   （合并）

 Mac Lane 备注指出在 Grp 中存在推出，并给出经典补充说明：如果腿是单射，则给出单射注入，并将顶点识别为具有合并的自由积。

 该问题（#325）中的勘误。其“当前状态”段落写道：“Top 条款和整个 Grp 条款缺失——树中没有 Top 或 Grp 类别。” 当目录编写时确实如此，但现在是错误的：Instance/Grp.v 和 Instance/Top.v 都存在，多个此类类别早些时候在同一活动中已经建立。真正缺失的是推 出，这正是这个文件和 Instance/Top/Pushout.v 提供的。构造。B *_A C 由生成元和关系给出，采用 Instance/Mod/Free.v 和 Instance/Ab/Tensor.v 中的归纳-集合商范式：[AmTerm] 是两个载体上关于三个群生成元的形式字，[am_eq] 是由以下各项生成的合同关系：(i) 两个群自身的等价关系，(ii) 两个插入的乘法性，(iii) 合并 [am_l (f a) ~ am_r (g a)]，(iv) 三个左手群律，(v) 两个运算的合同关系，以及 (vi) 对称性和传递性。那个演示购买的内容，已测量。每个群法则都是一个构造函数，所以 [AmalgamGrp] 是一个记录字面量，它本身没有证明义务。[am_eval] 是一个 [Fixpoint]，所以调解者的乘法法则通过 [reflexivity] 闭合——已记录，而不是从触发的策略中推导，由 [eq_refl] 控制 [ctl_grp_med_unit] / [ctl_grp_med_mul] 在 Test/ProbePushoutGrpTop.v 中。两个事实是推导出来的而不是发布的：[am_eq] 的自反性（[am_eq_refl]，[am_one] 情况通过 [ae_unit_l am_one] 及其自身对称性进行），以及两个插入保持单位（Instance/Grp.v 的 [Build_GrpHom']，其冗余性论证是在商中的消去）。UMP 需要两次归纳：一次是关于 CONGRUENCE（[am_eval_respects]，十二种情况，其中胶水情况是唯一使用 cocone 假设的），一次是关于 WORD（[am_med_unique]，五种情况）。该文件在 UMP 之外还有两个——[am_eq_refl] 和 [Grp_Cocartesian] 的 [fork_respects]——所以总共有四个；早期的草稿说“总价是两次归纳”，这低估了。已证明的内容以及强度。[Grp_HasPushouts] 是可交付成果。所选择的推出的顶点以及两个注入都是在 莱布尼茨等式([Grp_pushout_apex_is_AmalgamGrp] 及其相关项 [eq_refl])下手工构建的，承载者以及三个群运算也是如此。[pushout_med] 并非严格等于 [am_med]：Structure/Pushout.v 将 [pushout_ump] 作为 [Qed] 引理声明，因此 [unique_obj] 应用于一个不透明常量——该方程在 [≈] ([Grp_pushout_med_is_am_med]) 范围内成立，并且严格形式是带有 DONOR OPACITY 作为诊断原因的固定否定，同时配对顶部的相同否定，因此原因显然与群无关。MAC LANE 的单射腿精炼：以拆分强度给出，并且空隙是陈述的，而不是掩盖的。[Grp_split_legs_monic_injections] 证明如果两条腿都是拆分的，那么通过 Structure/Pushout/Split.v 两次注入都是单射的，其中参数是通用的：将余锥 [(id, f ∘ retraction)] 提供给泛性质。根据 Instance/Grp.v 自己的 [Grp_injectivity_is_monic] 向下读取元素，这表明两个插入是单射的（[am_inj1_injective], [am_inj2_injective]）。仅针对单射腿的精炼未被提供。对于群来说，这是关于合并自由积的施赖尔正规形式定理，其通常的证明方法（范德瓦尔登的方法）是构建在交替正规形式上的作用，因此必须为 B 中的 f(A) 和 C 中的 g(A) 选择陪集横截面；将这些横截面作为数据携带将是修复习惯用法的方法，其余的发展——正规形式、作用及其在同余上的良定义性——是组合群论中的一大块内容，这里不予尝试。文中未主张分裂假设是必要的；它并非必要，而且在 Grp 中也没有树内见证将“首一”与“分裂首一”区分开，因此这一差距的严格性是通过论证而非证明的。而麦克莱恩定理的另一半是定义性的，而非被证明的。
 “顶点是合并积”在这里成立，因为通过构造，顶点就是给定的群 B *_A C。下面的内容没有将其与独立的定义联系起来——无论是通过正规形式，还是通过某个外部群中生成的子群——所以这只是符号的武断认定，读者不应将其理解为一个定理。自由积，以及为什么这涉及一个单独的问题。[Grp_free_product] 是合并积的一个实例，而不是第二种构造，并且它的两个嵌入都是分裂单射，没有任何假设，因为每个常量支路可以通过另一个因子分解。要精确理解这一点，因为这个标题的早期草稿夸大了它：被解除的是严格较弱的分解假设（[Grp_fp_inl_Section] 通过 [am_inj1_Section_of_factor]，而不是 [am_inj1_Section_of_Retraction]），而 Mac Lane 自己的单射支路假设实际上对于这个跨距是错误的——这些支路是恒定映射，它们不能注入到非平凡群中，因此不是单射。因此，这就是 Mac Lane 在不同且较弱假设下得出的结论，而不是他改进的一个实例。[Grp_Cocartesian] 然后展示了自由积作为 Grp 的余积，而树中没有（问题 #1194 拥有 Grp 自由积；树中没有任何实例化 [Cocartesian Grp]）。交叉引用，并精确阅读：一般桥“在初始对象上的推岀是二元余积”是未解决问题 #862（Seven Sketches 6.2.3），在这里没有构建。所构建的是特设的 Grp 实例，其中推岀的交换假设通过 [Grp_fp_cocone] 被释放一次，剩下的字面上就是余积的普遍性质。该跨度是常量的，而不是零对象，这是一个宇宙决定。经典上，自由积是对平凡群的推挤，而该跨度的两条腿甚至可以分裂——[Grp_zero_hom_Section] 证明了这一点，其重traction是 [Grp_one]。但 Instance/Grp.v 声明了 [Grp_zero_hom] 在 [GrpObject@{Set Set Set}] 上（以及 [Grp_trivial@{u}] 在 [GrpObject@{u u Set}] 上，记录只需要一个绑定器，而记录需要更多），捐献者缺陷 Instance/Grp/Quotient/Colimit.v 已经记录下来，并将整个文件限制为 [Set] 尺寸的群。在此基础上构建自由积将继承这个限制。它是建立在常量腿上的，这不需要零对象：余锥条件是自动的，因为每个同态都保持单位（[Grp_fp_cocone]），并且每条腿都通过第三个常量映射（[grp_const_absorb]）因式分解到另一条腿上。[Grp_zero_hom_Section] 被保留作为未采用路径的真实记录。修正 (#450)：
 本段描述的捐赠者 pin 已被移除——#450 将 Instance/Grp.v 的零对象常量的宇宙写出到位，而 [About] 现在在 [GrpObject@{p p p}] 上读作 [Grp_zero_hom@{u p}]，在 [GrpObject@{u0 u0 u0}] 上读作 [Grp_zero_hom_Section@{u u0}]，并且在 [Set] 处没有实例化绑定器，在任一处也没有 [= Set] 约束：每个约束块中唯一的 [Set] 是 [Grp] 自身在其对象宇宙上的下界 [Set < u]。零对象路径因此不再继承 pin；常量分支结构保持不变。

 宇宙，在约束块中测量，并探查原因。两个独立的事实，它们的指向相反。在 PR “代数载体是集合” (2026-09-17) 之后重新测量。[PropEquiv] 字段将 [Set+1] 放入 [GrpObject] 的排序中，这显示为下面几个区块中的 [Set < _] 条款；回读在原位重述，变为假的条目已标记。(1) [AmalgamGrp@{u u0 .. u10}] 在其活页夹中显示三个独立的宇宙三元组——每组一个——而其约束块包含 [u = u0], ..., [u = u7]：这九个会塌缩。（早期版本说的是 [@{u u0 .. u8}] 和“全部九个”；该字段增加了另外两个宇宙，因此活页夹中有十二个，而塌缩的族仍然是三个组的三元组贡献的九个。）仅阅读活页夹会得出错误结论。但是这种识别并不是融合所做的，它是被探测而不是假定的：裸定义 [fun (A B : GrpObject) (f : @hom Grp A B) => B]（根本未提及推出）已经在 [GrpObject@{u0 u0 u0}] 处为两个对象进行了扩展。命名单个 Grp 同态就是识别层级的方法；融合没有增加任何内容。[Grp_HasPushouts@{u u0}] 相应地承载 [Set < u0] 和 [u < u0]。(2) 在此文件的主要常量中没有出现 [Set]——这个说法是错误的，因为 PR “代数承载者是集合”（2026-09-17），而更正比该说法更重要。目前测量结果为：[Grp_free_product@{u u0 u1 u2}] 是 [GrpObject@{u0 u0 u0} -> GrpObject@{u0 u0 u0} -> GrpObject@{u u0 u1}]，带有 [Set < u2] 和 [u0 < u2]；[Grp_HasPushouts@{u u0}] 承载 [Set < u0] 和 [u < u0]；[Grp_Cocartesian@{u u0}] 承载 [Set < u] 和 [u0 < u]。这些 [Set] 条款中的每一条都是严格下界（[Set < _]），而不是标识（[_ = Set]），因此没有任何内容固定在 [Set] 上：常量仍然适用于高于 [Set] 的任何承载者等级群组，这正是选择常量跨度所期望的，而 [Unset Universe Minimization ToSet] （Lib.v）无论如何都将承载者宇宙排除在 [Set] 之外。现在不再真实的是该标记的缺失。在 Test/ProbePushoutGrpTop.v 中 BOUNDARY 是被保护的，而不是被断言的：两个可形成性否定拒绝了 DONOR 常量 [Grp_zero_hom] 和 [Grp_zero_hom_Section]，这些常量位于严格高于 [Set] 的组中（一个真正的“无法强制 Set = bg”），而控制组在同一级别上形成 [AmalgamGrp]（选定的推出）、[Grp_free_product]、[Grp_fp_inl] 和 [grp_const]，并且有控制组在 [Set] 级别的组中命名两个 donor 常量，所以否定是关于宇宙的，而不是关于缺失引用的。（更正，#450：donor 引脚被提起，并且那里的两个否定是控制组；参见该探针的更正。）非空性。一个关于生成的合同关系的负事实不能通过对它进行归纳来得出，所以这里的每一个分离都通过一个具体的同态映射出商到 [Z2] : [fp_generators_distinct] 显示自由积并没有合并两个加数的生成元，并且 [fp_inl_injective] 显示它没有合并一个加数的不同元素。使得这种合并成为内容而不仅仅是记账的对比是 [amalgam_over_Z2_merges]：在相同的两个群上，沿着恒等元进行合并确实合并了自由积保持分开的那一对元素。未交付的内容。没有标准形式，因此没有字问题、没有系数唯一性，也没有 [am_eq] 的判定程序；上面的施赖尔细化；没有证明分裂假设严格弱于单性（未展示树内单一但非分裂的群同态）；没有 HNN 扩张；没有 Bass-Serre 理论；没有 van Kampen 定理，尤其没有与 Instance/Top/FundamentalGroupoid.v 的联系；在跨距中的推挤没有函子性；没有与 Instance/Grp/Free.v 的自由群比较（未展示两个自由群的自由积是自由的）；也没有无限/索引的自由积。(自 #450 起，Instance/Grp/Colimit.v 已经在其形状学科内具有所有群的余极限，以及它们之间的按索引的直和，这是通过伴随函子定理得到的——作为存在性结果，而不是文字说明。) [Grp_Cocartesian] 实例已经注册为 [#[export]，因此导入器可以获取它；没有 LIBRARY 文件导入这个文件——只有 Test/ProbePushoutGrpTop.v 导入。更正 (#450)：在父提交 e139ecfb 时，这个列表已经少了一个，其中 [git grep] 用于 Category.Instance.Grp.Pushout 的 [Require] 也找到了 Test/ProbeGrpProp.v；并且自 #450 以来，库文件 Instance/Grp/Colimit.v 导入了它，以证明它的伴随函子定理直和与该文件的 ([Grp_coproduct_agrees]) 相符，并且它通过了每一个 [Cocartesian] 实例的显式测试，从而确保导出的实例不会被悄悄地采纳。
*)

(** ** Formal words / **正式用语 *)

Inductive AmTerm (B C : GrpObject) : Type :=
  | am_l   : carrier B → AmTerm
  | am_r   : carrier C → AmTerm
  | am_one : AmTerm
  | am_mul : AmTerm → AmTerm → AmTerm
  | am_inv : AmTerm → AmTerm.

Arguments am_l {B C} _.
Arguments am_r {B C} _.
Arguments am_one {B C}.
Arguments am_mul {B C} _ _.
Arguments am_inv {B C} _.

(** ** The generated congruence / ** 生成的同余 *)

(*
 [am_eq] lands in [Prop].  Since the PR “algebraic carriers are sets”
 (2026-09-17) a [GrpObject] carries [grp_prop], so the amalgam's carrier
 setoid owes a [Prop]-valued mirror of its `≈`; the cheapest and most
 faithful one is the congruence itself, declared in [Prop].  Two
 constructors carry a [Type]-valued `≈` premise ([ae_l_resp], [ae_r_resp])
 and both stay VERBATIM: a [Prop] inductive may store [Type]-valued data,
 it simply may not be eliminated into [Type].  Nothing below is proved by
 induction on [am_eq] except [am_eval_respects], whose one elimination is
 routed through [pequiv] at the target group. 

 --------
 [am_eq] 降落在 [Prop]。由于 PR “代数载体是集合”（2026-09-17），一个 [GrpObject] 承载 [grp_prop]，因此合并体的载体集合体欠一个 [Prop] 值的其 `≈` 的镜像；最便宜且最忠实的是自身的同余，在 [Prop] 中声明。两个构造器承载一个 [Type] 值的 `≈` 前提（[ae_l_resp], [ae_r_resp]），并且两者都保持 VERBATIM：一个 [Prop] 归纳可以存储 [Type] 值的数据，它只是不能被消除成 [Type]。以下没有任何内容是通过对 [am_eq] 的归纳证明的，除了 [am_eval_respects]，其唯一的消除是通过目标组的 [pequiv] 路由的。
*)
Inductive am_eq {A B C : GrpObject}
                (f : A ~{Grp}~> B) (g : A ~{Grp}~> C)
  : AmTerm B C → AmTerm B C → Prop :=
  (* the two insertions respect the groups' own equivalences / 这两个插入遵循群体自身的等价关系 *)
  | ae_l_resp : ∀ b b' : carrier B,
      b ≈ b' → am_eq (am_l b) (am_l b')
  | ae_r_resp : ∀ c c' : carrier C,
      c ≈ c' → am_eq (am_r c) (am_r c')
  (* the two insertions preserve multiplication / 这两个插入保持乘法 *)
  | ae_l_mul : ∀ b b' : carrier B,
      am_eq (am_l (grp_mul B b b')) (am_mul (am_l b) (am_l b'))
  | ae_r_mul : ∀ c c' : carrier C,
      am_eq (am_r (grp_mul C c c')) (am_mul (am_r c) (am_r c'))
  (* the amalgamation: the span is coequalized / 融合：跨度被等同化 *)
  | ae_glue : ∀ a : carrier A,
      am_eq (am_l (f a)) (am_r (g a))
  (* the group laws, in their left-handed form / 群律，在它们的左手形式下 *)
  | ae_assoc : ∀ u v w,
      am_eq (am_mul (am_mul u v) w) (am_mul u (am_mul v w))
  | ae_unit_l : ∀ u, am_eq (am_mul am_one u) u
  | ae_inv_l : ∀ u, am_eq (am_mul (am_inv u) u) am_one
  (* congruence for the two operations / 这两种操作的一致性 *)
  | ae_mul_cong : ∀ u u' v v',
      am_eq u u' → am_eq v v' →
      am_eq (am_mul u v) (am_mul u' v')
  | ae_inv_cong : ∀ u u',
      am_eq u u' → am_eq (am_inv u) (am_inv u')
  (* symmetry and transitivity; reflexivity is derived below / 对称性和传递性；反身性在下面推导 *)
  | ae_sym : ∀ u v, am_eq u v → am_eq v u
  | ae_trans : ∀ u v w, am_eq u v → am_eq v w → am_eq u w.

Arguments ae_l_resp {A B C f g} _ _ _.
Arguments ae_r_resp {A B C f g} _ _ _.
Arguments ae_l_mul {A B C f g} _ _.
Arguments ae_r_mul {A B C f g} _ _.
Arguments ae_glue {A B C f g} _.
Arguments ae_assoc {A B C f g} _ _ _.
Arguments ae_unit_l {A B C f g} _.
Arguments ae_inv_l {A B C f g} _.
Arguments ae_mul_cong {A B C f g} _ _ _ _ _ _.
Arguments ae_inv_cong {A B C f g} _ _ _.
Arguments ae_sym {A B C f g} _ _ _.
Arguments ae_trans {A B C f g} _ _ _ _ _.

Section AmalgamCore.

Context {A B C : GrpObject}.
Context (f : A ~{Grp}~> B) (g : A ~{Grp}~> C).

(* Reflexivity is DERIVED rather than posted as a constructor. Every former has a congruence rule except [am_one], and the unit itself is reached by [ae_unit_l am_one] composed with its own symmetry. / 反身性是派生的，而不是作为构造函数发布的。每个前者都有一个合同规则，除了 [am_one]，而且单位本身是通过 [ae_unit_l am_one] 与其自身的对称性组合而达到的。 *)
Lemma am_eq_refl (u : AmTerm B C) : am_eq f g u u.
Proof.
  induction u as [b | c | | u IHu v IHv | u IHu].
  - apply ae_l_resp; reflexivity.
  - apply ae_r_resp; reflexivity.
  - exact (ae_trans _ _ _ (ae_sym _ _ (ae_unit_l am_one)) (ae_unit_l am_one)).
  - exact (ae_mul_cong _ _ _ _ IHu IHv).
  - exact (ae_inv_cong _ _ IHu).
Qed.

Definition AmSetoid : Setoid (AmTerm B C) := {|
  equiv := am_eq f g;
  setoid_equiv :=
    Build_Equivalence (am_eq f g) am_eq_refl (ae_sym) (ae_trans)
|}.

Definition AmCarrier : SetoidObject := {|
  carrier := AmTerm B C;
  is_setoid := AmSetoid
|}.

(*
 The amalgamated free product B *_A C.  Every group law is a
 CONSTRUCTOR of [am_eq], so the record below is a literal with no proof
 obligation of its own -- the [Instance/Mod/Free.v] payoff.

 CORRECTION.  That sentence was exactly true before the PR “algebraic
 carriers are sets” (2026-09-17).  The record now has a ninth field,
 [grp_prop], which is not a group law; it is still supplied by a literal
 here, and costs no obligation, because [am_eq] IS the [Prop] relation and
 the two implications are the identity.  So the record remains a literal
 with no proof obligation of its own -- with one more field in it. 

 --------
 合并自由积 B *_A C。每个群定律都是 [am_eq] 的构造器，因此下面的记录是一个字面量，本身没有证明义务——这是 [Instance/Mod/Free.v] 的回报。

 更正。在 PR“代数载体是集合”（2026-09-17）之前，这句话完全正确。现在记录有了第九个字段 [grp_prop]，它不是群定律；它仍然通过这里的字面量提供，并且不产生义务，因为 [am_eq] 是 [Prop] 的关系，并且这两个蕴含是恒等的。因此，该记录仍然是一个字面量，本身没有证明义务——只是多了一个字段。
*)
Definition AmalgamGrp : GrpObject := {|
  grp_setoid := AmCarrier;
  grp_unit := am_one;
  grp_mul := am_mul;
  grp_inv := am_inv;
  grp_mul_respects := fun u u' Hu v v' Hv => ae_mul_cong _ _ _ _ Hu Hv;
  grp_mul_assoc := ae_assoc;
  grp_mul_unit_l := ae_unit_l;
  grp_mul_inv_l := ae_inv_l;
  grp_prop :=
    @PropEquiv_of_relation _ AmSetoid (am_eq f g)
      (fun _ _ h => h) (fun _ _ h => h)
|}.

(** ** The two injections / ** 两次注射 *)

Definition am_inj1_map
  : SetoidMorphism (grp_setoid B) (grp_setoid AmalgamGrp).
Proof.
  unshelve notypeclasses refine {| morphism := am_l |}.
  intros b b' Hb; exact (ae_l_resp b b' Hb).
Defined.

Definition am_inj2_map
  : SetoidMorphism (grp_setoid C) (grp_setoid AmalgamGrp).
Proof.
  unshelve notypeclasses refine {| morphism := am_r |}.
  intros c c' Hc; exact (ae_r_resp c c' Hc).
Defined.

Definition am_inj1 : B ~{Grp}~> AmalgamGrp :=
  Build_GrpHom' am_inj1_map (fun b b' => ae_l_mul b b').

Definition am_inj2 : C ~{Grp}~> AmalgamGrp :=
  Build_GrpHom' am_inj2_map (fun c c' => ae_r_mul c c').

(* The pushout square commutes: this IS the [ae_glue] constructor. / 推挤方格是可交换的：这就是 [ae_glue] 构造器。 *)
Lemma am_square : am_inj1 ∘[Grp] f ≈ am_inj2 ∘[Grp] g.
Proof. intro a; exact (ae_glue a). Qed.

End AmalgamCore.

Arguments AmalgamGrp {A B C} f g.
Arguments am_inj1 {A B C} f g.
Arguments am_inj2 {A B C} f g.

(** ** The mediating homomorphism / ** 中介同态 *)

Section AmalgamMediator.

Context {A B C : GrpObject}.
Context (f : A ~{Grp}~> B) (g : A ~{Grp}~> C).
Context {Q : GrpObject}.
Context (q1 : B ~{Grp}~> Q) (q2 : C ~{Grp}~> Q).

(* Evaluation of a formal word in a competing group. A [Fixpoint], so the three homomorphism laws of the mediator hold DEFINITIONALLY. / 在竞争群体中对一个形式词的评估。 A [Fixpoint]，因此调解者的三个同态定律在定义上成立。 *)
Fixpoint am_eval (t : AmTerm B C) : carrier Q :=
  match t with
  | am_l b => grp_map q1 b
  | am_r c => grp_map q2 c
  | am_one => grp_unit Q
  | am_mul u v => grp_mul Q (am_eval u) (am_eval v)
  | am_inv u => grp_inv Q (am_eval u)
  end.

Context (Hcomm : q1 ∘[Grp] f ≈ q2 ∘[Grp] g).

(*
 Well-definedness on the quotient, by induction on the derivation.  The
 glue case is the ONLY one that consumes [Hcomm]; every other case is a
 law of [Q] or of one of the two homomorphisms. 

 --------
 在商上的良定义性，通过对推导的归纳。粘合情况是唯一会消耗 [Hcomm] 的情况；其他每种情况都是 [Q] 的一个定律，或者是两个同态之一的定律。
*)
(*
 [am_eq] is a [Prop] since the PR “algebraic carriers are sets”
 (2026-09-17), so the induction may not land in the [Type]-valued goal
 [am_eval u ≈ am_eval v] directly.  The whole proof is therefore conducted
 inside [Q]'s own [Prop] equality: [pequiv_to] opens it, each of the twelve
 branches closes with [pequiv_from] and then runs the ORIGINAL tactic
 unchanged, and [ae_sym]/[ae_trans] use [pequiv]'s own transported
 equivalence laws.  No mathematics moved. 

 --------
 [am_eq] 是一种 [Prop]，因为 PR “代数载体是集合”（2026-09-17），所以归纳可能不会直接落在 [Type] 值的目标 [am_eval u ≈ am_eval v] 上。因此，整个证明是在 [Q] 自身的 [Prop] 等式中进行的：[pequiv_to] 打开它，十二个分支中的每一个都以 [pequiv_from] 关闭，然后运行不变的 ORIGINAL 策略，[ae_sym] / [ae_trans] 使用 [pequiv] 自身传递的等价律。没有数学内容被移动。
*)
Lemma am_eval_respects (u v : AmTerm B C) (H : am_eq f g u v) :
  am_eval u ≈ am_eval v.
Proof using All.
  apply (@pequiv_to _ _ (grp_prop Q)).
  induction H as
    [ b b' Hbb' | c c' Hcc' | b b' | c c' | a
    | u v w | u | u
    | u u' v v' Huu' IHu Hvv' IHv
    | u u' Huu' IHu
    | u v Huv IHuv
    | u v w Huv IHuv Hvw IHvw ].
  - apply (@pequiv_from _ _ (grp_prop Q)); simpl; now apply proper_morphism.
  - apply (@pequiv_from _ _ (grp_prop Q)); simpl; now apply proper_morphism.
  - apply (@pequiv_from _ _ (grp_prop Q)); simpl; now apply grp_map_mul.
  - apply (@pequiv_from _ _ (grp_prop Q)); simpl; now apply grp_map_mul.
  - apply (@pequiv_from _ _ (grp_prop Q)); simpl; exact (Hcomm a).
  - apply (@pequiv_from _ _ (grp_prop Q)); simpl; now apply grp_mul_assoc.
  - apply (@pequiv_from _ _ (grp_prop Q)); simpl; now apply grp_mul_unit_l.
  - apply (@pequiv_from _ _ (grp_prop Q)); simpl; now apply grp_mul_inv_l.
  - apply (@pequiv_from _ _ (grp_prop Q)); simpl.
    apply grp_mul_respects;
      [ exact (@pequiv_to _ _ (grp_prop Q) _ _ IHu)
      | exact (@pequiv_to _ _ (grp_prop Q) _ _ IHv) ].
  - apply (@pequiv_from _ _ (grp_prop Q)); simpl.
    apply grp_inv_respects_law.
    exact (@pequiv_to _ _ (grp_prop Q) _ _ IHu).
  - now symmetry.
  - now transitivity (am_eval v).
Qed.

Definition am_eval_map
  : SetoidMorphism (grp_setoid (AmalgamGrp f g)) (grp_setoid Q).
Proof using All.
  unshelve notypeclasses refine {| morphism := am_eval |}.
  intros u v Huv; exact (am_eval_respects u v Huv).
Defined.

Definition am_med : AmalgamGrp f g ~{Grp}~> Q :=
  Build_GrpHom' am_eval_map (fun u v => reflexivity _).

Lemma am_med_inj1 : am_med ∘[Grp] am_inj1 f g ≈ q1.
Proof. intro b; reflexivity. Qed.

Lemma am_med_inj2 : am_med ∘[Grp] am_inj2 f g ≈ q2.
Proof. intro c; reflexivity. Qed.

(*
 Uniqueness, by induction on the WORD rather than on the congruence: a
 competing homomorphism is pinned on the two insertions by hypothesis
 and on the three formers by its own homomorphism laws. 

 --------
 唯一性，通过对词而不是对合同的归纳：假设下竞争同态在两个插入上被固定，并且在三个前者上由其自身的同态定律固定。
*)
Lemma am_med_unique (v : AmalgamGrp f g ~{Grp}~> Q)
      (H1 : v ∘[Grp] am_inj1 f g ≈ q1)
      (H2 : v ∘[Grp] am_inj2 f g ≈ q2) :
  am_med ≈ v.
Proof.
  intro t.
  induction t as [b | c | | s IHs t IHt | s IHs]; simpl.
  - symmetry; exact (H1 b).
  - symmetry; exact (H2 c).
  - symmetry; exact (grp_map_unit v).
  - transitivity (grp_mul Q (grp_map v s) (grp_map v t)).
    + now apply grp_mul_respects.
    + symmetry; exact (grp_map_mul v s t).
  - transitivity (grp_inv Q (grp_map v s)).
    + now apply grp_inv_respects_law.
    + symmetry; exact (grp_map_inv v s).
Qed.

End AmalgamMediator.


(* * ** The universal property, packaged / * ** 通用属性，打包 *)

Local Obligation Tactic := idtac.

#[export] Program Instance Grp_HasPushouts : HasPushouts Grp := {|
  pushout := fun A B C f g =>
    {| Pull         := AmalgamGrp f g;
       pullback_fst := am_inj1 f g;
       pullback_snd := am_inj2 f g
    |}
|}.
Next Obligation.
  intros A B C f g.
  exact (am_square f g).
Defined.
Next Obligation.
  intros A B C f g Q q1 q2 Hcomm.
  unshelve refine {| unique_obj := am_med f g q1 q2 Hcomm |}.
  - split.
    + exact (am_med_inj1 f g q1 q2 Hcomm).
    + exact (am_med_inj2 f g q1 q2 Hcomm).
  - intros v [Hv1 Hv2].
    exact (am_med_unique f g q1 q2 Hcomm v Hv1 Hv2).
Defined.

(* * ** The chosen pushout, and what reduces / * ** 所选的推送，以及什么会被减少 *)

Definition Grp_pushout {A B C : GrpObject}
           (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) : IsPushout f g :=
  @pushout Grp Grp_HasPushouts A B C f g.

(* The apex and both injections are the hand-built ones ON THE NOSE. / 顶点和两个注射点都是手工制造的，位于鼻子上。 *)
Example Grp_pushout_apex_is_AmalgamGrp {A B C : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) :
  pushout_apex (Grp_pushout f g) = AmalgamGrp f g := eq_refl.

Example Grp_pushout_in1_is_am_inj1 {A B C : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) :
  pushout_in1 (Grp_pushout f g) = am_inj1 f g := eq_refl.

Example Grp_pushout_in2_is_am_inj2 {A B C : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) :
  pushout_in2 (Grp_pushout f g) = am_inj2 f g := eq_refl.

(* The carrier of the apex is literally the type of formal words, and the group operations are literally the formers. / 顶点的承载者字面上是正式词的类型，而群运算字面上是前者。 *)
Example Grp_pushout_carrier {A B C : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) :
  carrier (AmalgamGrp f g) = AmTerm B C := eq_refl.

Example Grp_pushout_mul {A B C : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) :
  grp_mul (AmalgamGrp f g) = am_mul := eq_refl.

Example Grp_pushout_unit {A B C : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) :
  grp_unit (AmalgamGrp f g) = am_one := eq_refl.

Example Grp_pushout_inv {A B C : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) :
  grp_inv (AmalgamGrp f g) = am_inv := eq_refl.

(* The mediator's action on the two generating families reduces. / 调解者对这两个生成族的作用减少了。 *)
Example am_med_on_left {A B C Q : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C)
        (q1 : B ~{Grp}~> Q) (q2 : C ~{Grp}~> Q)
        (Hcomm : q1 ∘[Grp] f ≈ q2 ∘[Grp] g) (b : carrier B) :
  grp_map (am_med f g q1 q2 Hcomm) (am_l b) = grp_map q1 b := eq_refl.

Example am_med_on_right {A B C Q : GrpObject}
        (f : A ~{Grp}~> B) (g : A ~{Grp}~> C)
        (q1 : B ~{Grp}~> Q) (q2 : C ~{Grp}~> Q)
        (Hcomm : q1 ∘[Grp] f ≈ q2 ∘[Grp] g) (c : carrier C) :
  grp_map (am_med f g q1 q2 Hcomm) (am_r c) = grp_map q2 c := eq_refl.

(*
 [pushout_med], by contrast, does NOT reduce to [am_med]: Structure/
 Pushout.v states [pushout_ump] as a [Qed] lemma, so [unique_obj] is
 applied to an opaque constant.  The equation holds up to [≈], which is
 what the universal property gives; the strict form is pinned as a
 negative in Test/ProbePushoutGrpTop.v, with the opacity as its
 diagnosed cause. 

 --------
 相比之下，[pushout_med] 并不会简化为 [am_med] ：Structure/Pushout.v 将 [pushout_ump] 作为 [Qed] 引理，因此 [unique_obj] 被应用于一个不透明常量。该方程在 [≈] 之下成立，这正是普遍性所提供的；严格形式在 Test/ProbePushoutGrpTop.v 中被标记为一个负例，其不透明性被诊断为原因。
*)
Lemma Grp_pushout_med_is_am_med {A B C Q : GrpObject}
      (f : A ~{Grp}~> B) (g : A ~{Grp}~> C)
      (q1 : B ~{Grp}~> Q) (q2 : C ~{Grp}~> Q)
      (Hcomm : q1 ∘[Grp] f ≈ q2 ∘[Grp] g) :
  pushout_med (Grp_pushout f g) Hcomm ≈ am_med f g q1 q2 Hcomm.
Proof.
  apply (pushout_med_unique (Grp_pushout f g) Hcomm).
  - exact (am_med_inj1 f g q1 q2 Hcomm).
  - exact (am_med_inj2 f g q1 q2 Hcomm).
Qed.

(* * ** Mac Lane's monic-legs refinement, at split strength / * ** 马克·莱恩的单射腿改进，在分裂强度下 *)

Section GrpSplitRefinement.

Context {A B C : GrpObject}.
Context (f : A ~{Grp}~> B) (g : A ~{Grp}~> C).

(*
 The generic statements of Structure/Pushout/Split.v, transported to the
 named injections.  The transport is by CONVERSION -- [pushout_in1
 (Grp_pushout f g)] IS [am_inj1 f g], recorded above by [eq_refl] -- so
 each of these is an [exact] of the generic term. 

 --------
 Structure/Pushout/Split.v 的通用语句，被传递到命名的注入。传递是通过转换完成的 -- [pushout_in1 (Grp_pushout f g)] 是 [am_inj1 f g]，如上由 [eq_refl] 记录 -- 所以每一个都是通用项的 [exact]。
*)
Definition am_inj1_Section (Sg : Section g) : Section (am_inj1 f g) :=
  pushout_in1_Section_of_Retraction (Grp_pushout f g) Sg.

Definition am_inj2_Section (Sf : Section f) : Section (am_inj2 f g) :=
  pushout_in2_Section_of_Retraction (Grp_pushout f g) Sf.

(*
 The weaker hypothesis the free product actually uses: not that the
 opposite leg splits, but that one leg FACTORS through the other. 

 --------
 实际使用的较弱假设是：不是对边分裂，而是一条边通过另一条边分解。
*)
Definition am_inj1_Section_of_factor (r : C ~{Grp}~> B)
           (Hr : r ∘[Grp] g ≈ f) : Section (am_inj1 f g) :=
  pushout_in1_Section (Grp_pushout f g) r Hr.

Definition am_inj2_Section_of_factor (s : B ~{Grp}~> C)
           (Hs : s ∘[Grp] f ≈ g) : Section (am_inj2 f g) :=
  pushout_in2_Section (Grp_pushout f g) s Hs.

Theorem am_inj1_Monic (Sg : Section g) : Monic (am_inj1 f g).
Proof. exact (sections_are_monic _ _ _ (am_inj1_Section Sg)). Qed.

Theorem am_inj2_Monic (Sf : Section f) : Monic (am_inj2 f g).
Proof. exact (sections_are_monic _ _ _ (am_inj2_Section Sf)). Qed.

(*
 The refinement in the shape Mac Lane states it, at split strength: both
 legs split, therefore both injections are monic AND the vertex is the
 amalgamated product -- the latter definitionally, [AmalgamGrp f g]
 being the apex on the nose. 

 --------
 麦克莱恩所述的形状的精细化，在拆分强度下：两条腿都拆分，因此两个注入都是单态的，并且顶点是聚合积 —— 后者在定义上，即 [AmalgamGrp f g] 恰好是顶点。
*)
Theorem Grp_split_legs_monic_injections (Sf : Section f) (Sg : Section g) :
  Monic (am_inj1 f g) * Monic (am_inj2 f g).
Proof. exact (am_inj1_Monic Sg, am_inj2_Monic Sf). Qed.

(*
 Read down to elements through Instance/Grp.v's own characterization of
 monomorphisms: split legs make the two insertions INJECTIVE.  The
 hypotheses are spelled with [am_eq f g], which IS the apex's [≈] by
 construction ([AmSetoid]), so no coercion or transport intervenes. 

 --------
 通过 Instance/Grp.v 对单态射的自身描述，向下阅读到元素：分裂的腿使两个插入是单射。假设用 [am_eq f g] 来表述，根据构造（[AmSetoid]），它就是顶点的 [≈]，因此没有强制或传输介入。
*)
Corollary am_inj1_injective (Sg : Section g) :
  ∀ b b' : carrier B, am_eq f g (am_l b) (am_l b') → b ≈ b'.
Proof.
  exact (snd (Grp_injectivity_is_monic (am_inj1 f g)) (am_inj1_Monic Sg)).
Qed.

Corollary am_inj2_injective (Sf : Section f) :
  ∀ c c' : carrier C, am_eq f g (am_r c) (am_r c') → c ≈ c'.
Proof.
  exact (snd (Grp_injectivity_is_monic (am_inj2 f g)) (am_inj2_Monic Sf)).
Qed.

End GrpSplitRefinement.

(* * ** The free product, as the pushout along the constant legs / * ** 自由积，作为沿恒定边的推挤 *)

(*
 The constant homomorphism at the unit.  Multiplicativity is the unit's
 own idempotence, so [Build_GrpHom'] supplies unit-preservation. 

 --------
 单位上的恒同态。乘法性就是单位自身的幂等性，因此 [Build_GrpHom'] 提供了单位保持性。
*)
Definition grp_const_map (A G : GrpObject)
  : SetoidMorphism (grp_setoid A) (grp_setoid G).
Proof.
  unshelve notypeclasses refine {| morphism := fun _ => grp_unit G |}.
  intros a b _; reflexivity.
Defined.

Definition grp_const (A G : GrpObject) : A ~{Grp}~> G.
Proof.
  refine (Build_GrpHom' (grp_const_map A G) _).
  intros a b; simpl.
  symmetry; apply grp_mul_unit_l.
Defined.

(*
 THE ROUTE NOT TAKEN, and why.  The free product is classically the
 pushout over the TRIVIAL group, and that span's legs even SPLIT --
 [Grp_zero_hom]'s retraction is [Grp_one], the two composites living in
 a hom-set Instance/Grp.v has already proved to be a singleton.  The
 lemma is recorded here because it is the honest classical statement.
 But [Instance/Grp.v]'s [Grp_zero_hom] is declared over
 [GrpObject@{Set Set Set}] -- a donor pin of the family
 Instance/Grp/Quotient/Colimit.v records for [Grp_trivial] -- so
 everything built on it would be confined to [Set]-sized groups.  The
 free product below therefore goes through the CONSTANT legs instead,
 which needs no zero object and carries no pin; the probe file pins the
 donor's rejection above [Set] against this file's acceptance there.
 CORRECTION (#450): the donor pin is lifted in Instance/Grp.v, this
 lemma is universe-polymorphic since ([Grp_zero_hom_Section@{u u0}]),
 and the probe's two negatives are controls. 

 --------
 未走的路线，以及原因。自由积在经典上是对平凡群的推出来的，而该跨度的腿甚至可以分裂——[Grp_zero_hom] 的回退是 [Grp_one]，这两个复合函数存在于同一个 hom-set 中，Instance/Grp.v 已经证明它是单元素的。这里记录该引理是因为它是诚实的经典陈述。但是 [Instance/Grp.v] 的 [Grp_zero_hom] 被声明在 [GrpObject@{Set Set Set}] 上——这是该族的一个捐赠引脚。Instance/Grp/Quotient/Colimit.v 为 [Grp_trivial] 记录——因此在其上构建的所有内容都将被限制在 [Set] 尺寸的群上。因此以下自由积通过 CONSTANT 腿进行，这不需要零对象，也不携带任何引脚；探针文件将上面 [Set] 处捐赠者的拒绝与此文件那里的接受对照。更正 (#450)：在 Instance/Grp.v 中提升了捐赠者引脚，该引理是宇宙多态的，因为 ([Grp_zero_hom_Section@{u u0}])，并且探针的两个阴性是控制。
*)
Definition Grp_zero_hom_Section (G : GrpObject) : Section (Grp_zero_hom G).
Proof.
  unshelve refine {| section := Grp_one G |}.
  exact (Grp_zero_hom_unique Grp_trivial
           (Grp_one G ∘[Grp] Grp_zero_hom G) (@id Grp Grp_trivial)).
Defined.

(*
 B * C: the amalgam along the two constant legs.  This is an INSTANCE of
 the amalgamated product, not a second construction.

 THE SPAN APEX PLAYS NO ROLE, and that is visible rather than argued:
 [AmTerm B C] does not mention the apex at all, and the apex enters
 [am_eq] only through [ae_glue a], whose statement here is
 [am_l (grp_unit B) ~ am_r (grp_unit C)] for EVERY [a] -- one relation,
 repeated, and already derivable from the two insertions'
 unit-preservation.  [B] is taken as the apex only because it is at
 hand.  (That the congruences over two different apexes coincide is not
 stated as a lemma; what IS proved is that this object has the
 coproduct's universal property, which is what a consumer needs.) 

 --------
 B * C：沿着两条固定支腿的结合体。这是结合积的一个实例，而不是第二种构造。

 顶点的跨度不起作用，并且这是显而易见的而非需要论证的：
 [AmTerm B C] 完全没有提到顶点，顶点只通过 [ae_glue a] 进入 [am_eq]，而 [ae_glue a] 在这里的陈述是 [am_l (grp_unit B) ~ am_r (grp_unit C)] 对于每一个 [a] —— 一个关系，重复出现，且已经可以从两个嵌入的单位保持性推导出来。[B] 之所以被认为是顶点，仅仅因为它在手边。（两个不同顶点上的同余关系相同并没有被作为引理陈述；确切证明的是这个对象拥有余积的泛性质，这正是使用者所需要的。）
*)
Definition Grp_free_product (B C : GrpObject) : GrpObject :=
  AmalgamGrp (grp_const B B) (grp_const B C).

Definition Grp_fp_inl (B C : GrpObject) : B ~{Grp}~> Grp_free_product B C :=
  am_inj1 (grp_const B B) (grp_const B C).

Definition Grp_fp_inr (B C : GrpObject) : C ~{Grp}~> Grp_free_product B C :=
  am_inj2 (grp_const B B) (grp_const B C).

(*
 Any pair of homomorphisms out of B and C automatically forms a cocone
 over the constant span, both composites being constant at the unit of
 Q.  So the free product's copairing needs no compatibility hypothesis
 at all. 

 --------
 从 B 和 C 出发的任何一对同态自动形成一个关于常量跨度的余锥，两个合成都是 Q 的单位处的常量。因此，自由积的合对根本不需要任何兼容性假设。
*)
Lemma Grp_fp_cocone {B C Q : GrpObject}
      (q1 : B ~{Grp}~> Q) (q2 : C ~{Grp}~> Q) :
  q1 ∘[Grp] grp_const B B ≈ q2 ∘[Grp] grp_const B C.
Proof.
  intro b; simpl.
  transitivity (grp_unit Q).
  - exact (grp_map_unit q1).
  - symmetry; exact (grp_map_unit q2).
Qed.

Definition Grp_fp_merge {B C Q : GrpObject}
           (q1 : B ~{Grp}~> Q) (q2 : C ~{Grp}~> Q)
  : Grp_free_product B C ~{Grp}~> Q :=
  am_med (grp_const B B) (grp_const B C) q1 q2 (Grp_fp_cocone q1 q2).

(*
 Both free-product injections are split monic, with NO hypothesis: each
 constant leg factors through the other, via a third constant map. 

 --------
 这两个自由积注射都是单射分裂的，没有假设：每个常数支通过第三个常数映射通过另一个支。
*)
Lemma grp_const_absorb {A A' G : GrpObject} (h : A ~{Grp}~> A') :
  grp_const A' G ∘[Grp] h ≈ grp_const A G.
Proof. intro a; reflexivity. Qed.

Definition Grp_fp_inl_Section (B C : GrpObject) : Section (Grp_fp_inl B C) :=
  am_inj1_Section_of_factor (grp_const B B) (grp_const B C)
    (grp_const C B) (grp_const_absorb (grp_const B C)).

Definition Grp_fp_inr_Section (B C : GrpObject) : Section (Grp_fp_inr B C) :=
  am_inj2_Section_of_factor (grp_const B B) (grp_const B C)
    (grp_const B C) (grp_const_absorb (grp_const B B)).

Theorem Grp_free_product_injections_Monic (B C : GrpObject) :
  Monic (Grp_fp_inl B C) * Monic (Grp_fp_inr B C).
Proof.
  exact (sections_are_monic _ _ _ (Grp_fp_inl_Section B C),
         sections_are_monic _ _ _ (Grp_fp_inr_Section B C)).
Qed.

(*
   * ** The free product IS the coproduct of Grp

   Cross-reference: the GENERAL bridge “a pushout over the initial object
   is the binary coproduct” is open issue #862 (Seven Sketches 6.2.3) and
   is NOT built here.  What follows is the ad-hoc Grp instance: the
   commutation hypothesis of the pushout's universal property is
   discharged once and for all by [Grp_fp_cocone], leaving exactly the
   coproduct's universal property. 

   --------
   * ** 自由积是Grp的余积

   交叉引用：一般性桥接“初始对象上的推挤是二元余积”是未决问题#862（《七个草图》6.2.3章节），并未在此构建。以下是Grpp的特设实例：一旦通过[Grp_fp_cocone]，推挤的普遍性质的交换假设就被一次性解决，从而正好保留了余积的普遍性质。
*)

Local Obligation Tactic := idtac.

#[export] Program Instance Grp_Cocartesian : @Cocartesian Grp := {|
  product_obj := Grp_free_product;
  fork := fun _ _ _ q1 q2 => Grp_fp_merge q1 q2;
  exl := fun B C => Grp_fp_inl B C;
  exr := fun B C => Grp_fp_inr B C
|}.
Next Obligation.
  intros Q B C q1 q1' H1 q2 q2' H2.
  intro t.
  induction t as [b | c | | s IHs t IHt | s IHs]; simpl.
  - exact (H1 b).
  - exact (H2 c).
  - reflexivity.
  - now apply grp_mul_respects.
  - now apply grp_inv_respects_law.
Qed.
Next Obligation.
  intros Q B C q1 q2 h.
  split.
  - intro Hh.
    split.
    + intro b; exact (Hh (am_l b)).
    + intro c; exact (Hh (am_r c)).
  - intros [Hl Hr].
    symmetry.
    exact (am_med_unique (grp_const B B) (grp_const B C) q1 q2
             (Grp_fp_cocone q1 q2) h Hl Hr).
Qed.

(*
   * ** Non-vacuity

   Nothing below can be proved by induction on [am_eq]: a NEGATIVE fact
   about a generated congruence is only reachable by mapping OUT of the
   quotient, which is what the universal property is for.  Every
   separation here therefore runs through a concrete homomorphism into
   [Instance/Grp.v]'s [Z2]. 

   --------
   * ** 非空性

   以下内容无法通过对 [am_eq] 的归纳来证明：关于生成同余的负事实只能通过映射到商之外才能得到，这正是泛性质的用途。因此，每一次分离都通过一个具体的同态映射到 [Instance/Grp.v] 的 [Z2]。
*)

(*
 The separating homomorphism out of Z2 * Z2: the identity on the left
 summand, the constant map on the right. 

 --------
 从 Z2 * Z2 出发的分离同态：左边直和上的恒等映射，右边上的常值映射。
*)
Definition fp_probe : Grp_free_product Z2 Z2 ~{Grp}~> Z2 :=
  Grp_fp_merge (@id Grp Z2) (grp_const Z2 Z2).

Example fp_probe_left :
  grp_map fp_probe (@am_l Z2 Z2 true) = true := eq_refl.
Example fp_probe_right :
  grp_map fp_probe (@am_r Z2 Z2 true) = false := eq_refl.

(* The free product does NOT merge the two summands' generators. / 自由积不合并两个加数的生成元。 *)
Theorem fp_generators_distinct :
  am_eq (grp_const Z2 Z2) (grp_const Z2 Z2)
    (@am_l Z2 Z2 true) (@am_r Z2 Z2 true) → False.
Proof.
  intro H.
  assert (Hq : @equiv _ bool_setoid
                 (grp_map fp_probe (@am_l Z2 Z2 true))
                 (grp_map fp_probe (@am_r Z2 Z2 true)))
    by (apply proper_morphism; exact H).
  simpl in Hq.
  discriminate Hq.
Qed.

(*
 ...and does not merge distinct elements of one summand either, which is
 [Grp_fp_inl_Section] read down to elements. 

 --------
 ...并且也不合并一个加数的不同元素，即从上到下读取元素的 [Grp_fp_inl_Section]。
*)
Theorem fp_inl_injective :
  am_eq (grp_const Z2 Z2) (grp_const Z2 Z2)
    (@am_l Z2 Z2 true) (@am_l Z2 Z2 false) → False.
Proof.
  intro H.
  assert (Hq : @equiv _ bool_setoid true false).
  { exact (snd (Grp_injectivity_is_monic (Grp_fp_inl Z2 Z2))
             (fst (Grp_free_product_injections_Monic Z2 Z2))
             true false H). }
  discriminate Hq.
Qed.

(*
 THE CONTRAST that makes the amalgamation content rather than
 bookkeeping: over the SAME two groups, amalgamating along the identity
 DOES merge the very pair the free product keeps apart. 

 --------
 使合并内容而非记账的对比：在相同的两组上，沿身份合并确实将自由积保持分开的那对元素合并在一起。
*)
Theorem amalgam_over_Z2_merges :
  am_eq (@id Grp Z2) (@id Grp Z2) (@am_l Z2 Z2 true) (@am_r Z2 Z2 true).
Proof. exact (@ae_glue Z2 Z2 Z2 (@id Grp Z2) (@id Grp Z2) true). Qed.
