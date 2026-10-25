Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Grp.

Generalizable All Variables.

(* * * Limits of groups are computed on underlying sets / * * 群的极限是在其底层集合上计算的 *)

(*
 nLab: https://ncatlab.org/nlab/show/created+limit
 nLab: https://ncatlab.org/nlab/show/limit#limits_in_categories_of_algebras
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_groups
 Mac Lane: Categories for the Working Mathematician, 2nd ed. (GTM 5),
 §V.1 Theorems 2 and 3, book pp. 111-112 (PDF pp. 120-121)
 Awodey:   Category Theory, 1st ed. (CMU pre-print, September 2005),
 §5.6 Proposition 5.32, printed p. 119 (PDF p. 128)

 [Grp_Forget] STRICTLY CREATES every limit.  Given a limiting cone over
 the underlying diagram of sets, there is exactly one group structure on
 its apex making every projection a homomorphism ([glim_structure_unique],
 Mac Lane's Theorem 2), the resulting cone lies over the given one ON THE
 NOSE ([glim_over_obj] and [glim_over_legs] are both [eq_refl], because
 [Grp_Forget]'s object map is the [grp_setoid] projection), it is limiting
 ([glim_created]), and a cone of groups whose image is limiting is itself
 limiting ([grp_reflects]).  Packaged as Structure/Limit/Creation.v's own
 classes -- [Grp_Forget_StrictlyCreatesLimit], [Grp_Forget_CreatesLimit]
 and [Grp_Forget_creates_limits] -- from which the two standard corollaries
 follow by application: [Grp_Complete] (Mac Lane's Theorem 3) and
 [Grp_Forget_continuous : ContinuousFunctor Grp_Forget], the cone-level
 reading, with the apex-only [Grp_Forget_PreservesAllLimits] derived from
 it and [Grp_Forget_reflects_limits] alongside.

 THE HEADLINE SENTENCE IS MACHINE-CHECKED AT [eq_refl], NOT ARGUED.  At
 the limits [Sets_Complete] chooses -- the compatible families of
 Instance/Sets/Complete.v -- the created group is the COORDINATEWISE one
 on the nose: [grp_complete_carrier], [grp_complete_mul],
 [grp_complete_unit], [grp_complete_inv] and [grp_complete_leg] are five
 [eq_refl] Examples, at an ARBITRARY shape and an ARBITRARY diagram of
 groups.  Nothing in them is specific to a witness category, and no
 isomorphism is interposed; this file therefore needs no concrete witness
 to be non-vacuous, and builds none.

 ON THE HOUSE RULE THAT MORPHISMS ARE COMPARED WITH [≈]: four statements
 here write [=] between morphisms -- [glim_over_legs], [grp_lift_legs],
 [grp_fcone_leg] and [grp_complete_leg] -- and each does so because both
 sides are the SAME TERM, the witness being [eq_refl].  They record
 Mac Lane's [F sigma = tau] at full strength, which is strictly stronger
 than the [≈] the [StrictLift] clause asks for; every law, every proof and
 the [slift_legs] clause consumed by [grp_strict_lift] use [≈].  The same
 applies to the object-level [=] of [glim_over_obj], [grp_lift_apex],
 [grp_fcone_apex], [grp_complete_carrier] and the three [grp_complete_*]
 element equations, which compare OBJECTS and ELEMENTS rather than
 morphisms and are the discipline's sanctioned exception.

 TWO FIRSTS, MEASURED BY SHAPE RATHER THAN BY NAME.  [Grp_Complete] is
 the FIRST inhabitant of [@Complete] at ANY ALGEBRAIC CATEGORY: sweeping
 declaration heads whose statement mentions word-bounded [Complete] or
 [Cocomplete], comment-stripped and across line breaks, the entire
 unconditional concrete roster before this file was [Sets_Complete]
 (Instance/Sets/Complete.v), [ConeSet_Complete],
 [Sets_Cocomplete] (Instance/Sets/Cocomplete.v) and
 [Subsets_Complete]/[Subsets_Cocomplete] (Instance/Powerset.v) --
 nothing for [Grp], [Ab], [CMon], [Rng], [RMod], [Mon], [Top] or [Cat].
 And [Grp_Forget_creates_limits] is the FIRST creation inhabitant at a
 NAMED CONCRETE category: outside the declaring file there are exactly
 ELEVEN declaration heads whose statement mentions one of those classes,
 four of them [EM_Forget T] for an arbitrary monad and the other seven
 generic in their functor -- [comma_proj2] once, a subcategory inclusion
 three times, an arbitrary equivalence twice, [Id] once.  Correspondingly
 [EM_Forget] was the ONLY forgetful functor anywhere with a preservation,
 reflection, lifting or creation result: a sweep for [_Forget] heads
 INHABITING A CREATION CLASS returns exactly those four, and widening the
 vocabulary to lifting and reflection adds [em_strict_lift],
 [monadic_creates] (Monad/Monadicity/Beck.v) and
 [em_forget_reflects_isos] (Monad/Monadicity/BeckObjects.v) -- still
 all [EM_Forget].  And NO limit, cone, completeness, creation, lifting,
 preservation or continuity statement about [Grp] or [Grp_Forget] existed
 at all (that sweep returns zero; before this file [Grp_Forget] was known
 to be [Faithful] and to be the right adjoint of [FreeGrp], and nothing
 else structural).

 THE ISSUE'S "Current state" SECTION (#411) IS STALE ON EVERY COUNT AND
 THE MEASUREMENTS ARE RECORDED HERE RATHER THAN REPEATED.  Its claims
 were: (i) "the category of groups does not exist in-tree -- the three
 occurrences of [Grp] are prose"; (ii) "there is likewise no lifting or
 creation vocabulary"; (iii) "no limit theory for any algebra category";
 (iv) "the ONE forgetful functor into [Sets], [CMon_Forget], has no
 consumers and is nowhere shown to preserve, reflect, lift or create
 anything".  Measured at 1fd2f96c: (i) FALSE -- Instance/Grp.v declares
 [Grp] and [Grp_Forget], both consumed here and neither rebuilt, and
 word-bounded [Grp] matches 1022 LINES across 88 [.v] files (1112
 occurrences) rather than three;
 (ii) FALSE -- Structure/Limit/Creation.v declares [CreatesLimit],
 [StrictLift], [StrictlyCreatesLimit] and the
 shape-quantified forms, which is what this file inhabits (the issue's
 literal command does return four hits in two files, all of them prose
 inside comments, so it measured the phrase and not the vocabulary);
 (iii) FALSE as a claim, though its parenthetical is right about the three
 files it names -- the limit theory for an algebra category is
 Monad/Eilenberg/Moore/Limit.v, which the issue does not look at, and
 which is this file's architectural template; (iv) FALSE in three of its
 four clauses -- the line number is right and [CMon_Forget] is still at
 Instance/CMon.v, but it is not the only forgetful functor into [Sets]
 ([Grp_Forget], [Rng_Forget], [Ab_Forget], [Pos_Forget], [Top_Forget],
 [RMod_Forget], [FdVect_Forget] are others) and it does have consumers
 (Instance/Concrete.v, Theory/Algebra/Rig.v,
 Instance/Roster.v), its faithfulness having been proved at
 Instance/Concrete.v; what remains TRUE is the last clause, that no
 preservation, reflection, lifting or creation result about it exists.

 THIS IS NOT AN INSTANCE OF [EM_Complete], AND THAT IS MEASURED RATHER
 THAN ASSUMED: no file in the tree exhibits [Grp] as an Eilenberg-Moore
 category (the token [EilenbergMoore] co-occurs with [Grp] in no [.v]
 file) (CORRECTION (#464): as a token test this does not hold, and it
 did not already before #464, through #370's and #463's files below.
 [grep -lw EilenbergMoore] followed by [grep -lw Grp] over the [.v]
 files outside doc/ lists, besides this header, Instance/Proset/Monad.v
 and Construction/Reflective/Monadic.v, where [Grp] occurs only in a path
 in prose, and #464's Instance/Fun/Action/Monad.v,
 Instance/Fun/Action/Monad/BG.v and Test/ProbeGroupAction464.v, where it
 occurs only as a component of a module path, in [Require] lines,
 qualified names or prose, and whose Eilenberg-Moore categories are those
 of the action monads of a monoid or a group.  None exhibits [Grp] itself
 as an Eilenberg-Moore category, so the claim stands), so the monadicity
 route is unavailable here and the argument is
 rerun one level down.  What the two developments share is the
 ARCHITECTURE -- build the structure as the MEDIATOR of a cone whose legs
 are the diagram's own operations, then get every law from joint monicity
 of the legs -- and this file follows it clause for clause.

 TWO PLACES WHERE THE GROUP CASE COMES OUT CHEAPER THAN THE TEMPLATE.
 First, no image cone is built: [FCone Grp_Forget N] IS the elementwise
 cone on the nose ([grp_fcone_apex], [grp_fcone_leg], both [eq_refl]),
 where the Eilenberg-Moore file declares its own [car_cone] and
 [rcar_cone].  Second, [grp_reflects] takes NO leg hypothesis: it is
 stated directly against [IsLimitCone (FCone Grp_Forget M)], which is
 precisely the [screates_reflect] clause, where [em_reflects] must carry
 an [Hlegs] argument tying its abstract limit to the cone's legs.

 THE ENGINE IS ONE REUSABLE LEMMA WITH NOTHING GROUP-THEORETIC IN IT.
 [sets_limit_ext] says the legs of a limiting cone in [Sets] are jointly
 monic ELEMENTWISE: two points of the apex agreeing at every leg are
 equal.  It is proved from the mediator's uniqueness alone, with the two
 constant maps out of the apex itself as probes -- so it needs no terminal
 object and pulls in no further module.  Every group law below is then
 three lines: apply it, rewrite the defining triangle, apply the law in
 [K j].  It belongs beside its donors in Instance/Sets/Complete.v; it is
 declared here so that this change touches no upstream file.

 REUSABILITY (the issue's work item 3), stated at the strength it has.
 [sets_limit_ext] and the argument skeleton transfer to any category of
 setoid-algebras over [Sets] -- [CMon], [Ab], [Rng], [RMod] -- nothing in
 either being specific to the group signature; that is an engineering
 judgement, nothing is compiled for it here.  What is NOT done is a
 signature-parameterised statement, and the reason is NOT that the obvious
 substrate is axiom-carrying: measured, Instance/Comp.v's [Algs]
 and [GroupOp] are BOTH Closed under the global context.  It is that
 [Algs S] is the category of algebras for an OPERATION signature with no
 equations, so a category of GROUPS there needs the equational layer, and
 each of [GroupEq], [Group] and [Product] (all in Instance/Comp.v)
 carries [functional_extensionality_dep]; moreover [Group] is a
 [Type] of algebras with no category attached, which Instance/Grp.v's own
 header records, so nothing in tree relates it to [Grp].  A
 signature-generic route is therefore a construction rather than an
 instantiation, and it is not attempted -- a SCOPE choice with one
 measured cost attached, not a proof that no such route exists.

 UNIQUENESS IS THE WHOLE CONTENT OF THEOREM 2 AND IS PROVED TWICE OVER, AT
 TWO DIFFERENT STRENGTHS.  Elementwise, [glim_unit_unique],
 [glim_mul_unique] and [glim_inv_unique] show each operation is determined
 by the leg conditions, and [glim_structure_unique] bundles them; note
 what those consume -- ONLY that the legs preserve the candidate
 structure, NO law of it, so the statement is sharper than "any group
 structure making the projections homomorphisms is this one".
 Categorically, [Grp_lift_cone_unique] is the generic
 [screates_lift_unique] at this instance, giving the canonical cone
 isomorphism.  A whole-record statement "[G' = LimitGroup] for any group
 [G'] on that carrier" is NOT delivered and is not a gap that could be
 closed by more work here: it would need [grp_setoid G' = vertex_obj[L]]
 as a Leibniz equality and a transport in the type of every operation,
 which is why the Eilenberg-Moore file's [em_alg_unique] pins its carrier
 the same way.

 UNIVERSES, measured off BOTH binder and block over all 83 constants:
 ZERO word-bounded [Set] occurrences anywhere, and only TEN carry a block
 equation at all.  Five are the generic [Sets] section -- [sets_pre],
 [sets_med_eq], [sets_limit_ext], [sets_const] and its [Program]
 obligation [sets_const_obligation_1], which no source-level reading sees
 -- all five carrying [u0 = u3], which identifies the shape's
 hom-and-proof universe with [Sets]' carrier universe, and the first three
 additionally [u1 = u2], which identifies two of the ambient's; that
 [u0 = u3] is [IsALimit]'s doing and not this file's, and the probe pins
 it with [Cone] ACCEPTED at the very levels where [IsALimit] is refused.
 The other five are the [grp_complete_*] readbacks, which BIND their shape
 explicitly and so carry [u = u0], identifying the shape's object universe
 with its hom-and-proof universe -- that is [Complete]'s own [@{u u u u0}]
 shape written out, inherited from [Sets_Complete] and not narrowed here.
 The remaining 73 constants carry NO block equation,
 [Grp_Complete@{u u0 u1} : Complete@{u u u u0}] with [u < u0] and
 [u0 <= u1] among them, so the smallness discipline is exactly
 [Sets_Complete]'s.  READ THE hom = proof IDENTIFICATION IN THOSE BINDERS
 CORRECTLY: every [Category@{u u0 u0}] here is the SHAPE, and the
 identification is the LIMIT VOCABULARY's rather than [Grp]'s or [Sets]'
 -- at a shape declared with its hom strictly below its proof universe,
 [Jv], [Jv ⟶ Grp], [Cone] and [@Complete Grp] are all ACCEPTED while
 [IsALimit], [Limit], [CreatesLimit], [StrictlyCreatesLimit] and
 [Grp_Complete Jv Kv] are all REFUSED.  It is introduced by neither this
 file nor its statements either way.

 Test/ProbeGrpLimit411.v carries the two refusals this file records and
 the universe boundary a consumer meets: FOUR negatives of THREE kinds
 plus a scope-free instrument check, each stripped ONE AT A TIME in a copy
 of the whole probe and compiled alone.  Everything this file claims at
 [eq_refl] is shipped here as an [Example] and so guards itself.
 [make todo] grows by 13, ALL of them in that probe; this file contributes
 ZERO, so the issue's "adds no new hits" box is not met as written and is
 disclosed rather than glossed.

 NOT delivered: no colimits and no cocompleteness for [Grp] (Awodey
 §5.6's omega-colimit half is #561's, and the filtered-colimit machinery
 it needs exists nowhere in tree) -- CORRECTION (#450): [Grp] is
 cocomplete since #450, by Instance/Grp/Colimit.v's
 [Grp_Cocomplete_via_GAFT], the adjoint functor theorem applied at the
 diagonal with this file's [Grp_Complete] as its completeness
 hypothesis; that is not the filtered-colimit route, which is still
 absent, and none of those colimits computes; no signature-generic
 variant, as above; no comparison of the created binary product with
 Instance/Grp.v's [Grp_Cartesian], which would go through a discrete
 diagram and so through Instance/Discrete.v's unannotated
 [DiscreteCat_Functor], pinning the ambient hom and proof universes to
 the literal [Set] -- CORRECTION (#450): that reason had stopped holding
 before #450.  The PR "algebraic carriers are sets" annotated
 [DiscreteCat_Functor] in place, and [About] reads
 [DiscreteCat_Functor@{o h p uo uh up u}] over [C : Category@{uo uh up}]
 with no [Set] in its constraint block; the comparison itself is still
 not made; no analogue for [CMon], [Ab], [Rng] or [RMod], though the
 engine transfers unchanged; no monadicity statement and no comparison
 functor, so nothing here says [Grp] IS an Eilenberg-Moore category;
 and NOTHING is registered as an [Instance] -- the file declares none,
 following its template, since a chosen limit must not become globally
 resolvable. 

 --------
 nLab:  https://ncatlab.org/nlab/show/created+limit
 nLab:  https://ncatlab.org/nlab/show/limit#limits_in_categories_of_algebras
 Wikipedia:  https://en.wikipedia.org/wiki/Category_of_groups
 Mac Lane: 《为工作中的数学家而作的范畴论》，第2版 (GTM 5),
 §V.1 定理 2 和 3, 书本第 111-112 页 (PDF 第 120-121 页)
 Awodey: 《范畴论》，第1版 (CMU 预印本, 2005年9月),
 §5.6 命题 5.32, 印刷本第 119 页 (PDF 第 128 页)[Grp_Forget] 严格地创建每一个极限。给定一个在集合的底层图上的限制锥，在其顶点上恰好存在一个群结构，使得每个投影都是同态（[glim_structure_unique]，Mac Lane 定理 2），所得到的锥精确地位于给定锥之上（[glim_over_obj] 和 [glim_over_legs] 都是 [eq_refl]，因为 [Grp_Forget] 的对象映射是 [grp_setoid] 投影），它是限制性的（[glim_created]），并且一个映射为限制性的群锥本身也是限制性的（[grp_reflects]）。作为 Structure/Limit/Creation.v 自身的类打包——[Grp_Forget_StrictlyCreatesLimit]，[Grp_Forget_CreatesLimit] 和 [Grp_Forget_creates_limits] ——由此应用可以得到两个标准推论：[Grp_Complete]（Mac Lane 定理 3）和 [Grp_Forget_continuous : ContinuousFunctor Grp_Forget]，锥层面的解读，其顶点唯一的 [Grp_Forget_PreservesAllLimits] 由它和 [Grp_Forget_reflects_limits] 推导而来。头条句子在 [eq_refl] 由机器检查，不用于论证。 在极限处 [Sets_Complete] 选择——兼容的 Instance/Sets/Complete.v 家族——创建的群组正好是逐坐标的群组：[grp_complete_carrier]、[grp_complete_mul]、[grp_complete_unit]、[grp_complete_inv] 和 [grp_complete_leg] 是五个 [eq_refl] 例子，在任意形状和任意群图中。 它们中没有任何内容特定于见证类别，也没有插入同构；因此该文件不需要具体见证即可非空，也未构建任何见证。关于房规，即比较同态的规则与 [≈]：四个陈述  
 在这里将 [=] 写在同态之间——[glim_over_legs]、[grp_lift_legs]、[grp_fcone_leg] 和 [grp_complete_leg]——每一个都是如此，因为双方都是相同的项，证据为 [eq_refl]。它们全面记录了 Mac Lane 的 [F sigma = tau]，这比 [StrictLift] 条款要求的 [≈] 严格得多；每条定律、每个证明以及 [grp_strict_lift] 消耗的 [slift_legs] 都使用了 [≈]。同样适用于对象层的 [glim_over_obj] 的 [=]、[grp_lift_apex]、[grp_fcone_apex]、[grp_complete_carrier] 以及三个 [grp_complete_*] 元素方程，这些方程比较的是对象和元素，而不是同态，并且这是该学科认可的例外。两个首次，按形状而不是名称衡量。[Grp_Complete] 是在任何代数范畴中 [@Complete] 的首个居民：扫描声明头，其陈述提到以单词为界的 [Complete] 或 [Cocomplete]，去掉注释并跨行，当前文件之前的整个无条件具体名单是 [Sets_Complete]（Instance/Sets/Complete.v）、[ConeSet_Complete]、[Sets_Cocomplete]（Instance/Sets/Cocomplete.v）以及 [Subsets_Complete] / [Subsets_Cocomplete]（Instance/Powerset.v）—— [Grp]、[Ab]、[CMon]、[Rng]、[RMod]、[Mon]、[Top] 或 [Cat] 没有。[Grp_Forget_creates_limits] 是第一个在一个命名的具体类别中被创建的元素：在声明文件之外，正好有十一条声明头，其语句提到了这些类中的一个，其中四个是 [EM_Forget T] 对任意单子，另外七个在它们的函子中是泛型的——[comma_proj2] 出现一次，子类别包含出现三次，任意等价出现两次，[Id] 出现一次。相应地，[EM_Forget] 是唯一在任何地方具有保持、反映、提升或创建结果的遗忘函子：对于 [_Forget] 头居于创建类的抽取正好返回那四个，将词汇扩展到提升和反映则增加 [em_strict_lift]、[monadic_creates]（Monad/Monadicity/Beck.v）和 [em_forget_reflects_isos]（Monad/Monadicity/BeckObjects.v）——仍然全都是 [EM_Forget] 。并且关于 [Grp] 或 [Grp_Forget] 根本不存在任何极限、余锥、完备性、创造、提升、保持或连续性声明（该扫描返回零；在此文件之前 [Grp_Forget] 已知为 [Faithful] 并且是 [FreeGrp] 的右伴随，除此之外没有其他结构性内容）。该问题的“当前状态”部分（#411）在各方面都已过时，测量结果记录在此处而非重复。其声明包括：(i) “树中不存在群类别——[Grp] 的三次出现都是散文”；(ii) “同样没有提升或创建的词汇”；(iii) “任何代数类别都没有极限理论”；(iv) “进入 [Sets] 的唯一遗忘函子 [CMon_Forget] 没有使用者，并且没有任何地方显示其保留、反映、提升或创建任何内容。”在 1fd2f96c 上测量：（i）错误 -- Instance/Grp.v 声明了 [Grp] 和 [Grp_Forget]，二者都在此处被使用且都未重建，并且按字界定的 [Grp] 匹配了 88 个 [.v] 文件中的 1022 行（共 1112 次出现），而不是三次；（ii）错误 -- Structure/Limit/Creation.v 声明了 [CreatesLimit]、[StrictLift]、[StrictlyCreatesLimit] 及其形状量化形式，这正是该文件所涵盖的内容（问题的字面命令确实在两个文件中返回四个匹配，全都在注释中的散文里，因此它测量的是短语而不是词汇）；（iii）作为声明是错误的，尽管其括号内容关于它命名的三个文件是正确的——代数范畴的极限理论是 Monad/Eilenberg/Moore/Limit.v，问题没有查看这个文件，而这正是该文件的架构模板；（iv）其中三点是错误的四个条款——行号是正确的，[CMon_Forget] 仍然在 Instance/CMon.v，但它并不是进入 [Sets] 的唯一健忘函子（[Grp_Forget]、[Rng_Forget]、[Ab_Forget]、[Pos_Forget]、[Top_Forget]、[RMod_Forget]、[FdVect_Forget] 是其他函子），并且它确实有使用者（Instance/Concrete.v、Theory/Algebra/Rig.v、Instance/Roster.v），它的忠实性已在 Instance/Concrete.v 证明；剩下仍然为真的条款是最后一条，即不存在关于它的保持、反射、提升或创建的结果。

 这不是 [EM_Complete] 的一个实例，并且这是测量得到的而不是假设的：在该树中的文件没有显示 [Grp] 作为 Eilenberg-Moore 类别（标记 [EilenbergMoore] 与 [Grp] 在没有 [.v] 文件中同时出现）（更正（#464）：作为一个标记测试，这不成立，并且在 #464 之前也不成立，通过下面 #370 和 #463 的文件。）[grep -lw EilenbergMoore] 后跟 [grep -lw Grp]，跨越 [.v] 文件（在 doc/ 列表之外），除了这个头文件，还有 Instance/Proset/Monad.v 和 Construction/Reflective/Monadic.v，其中 [Grp] 仅出现在散文路径中，以及 #464 的 Instance/Fun/Action/Monad.v、Instance/Fun/Action/Monad/BG.v 和 Test/ProbeGroupAction464.v，其中它仅作为模块路径的组成部分出现，在 [Require] 行、限定名或散文中，其 Eilenberg-Moore 范畴是单子或群的作用单子的范畴。没有一个展示 [Grp] 本身作为 Eilenberg-Moore 范畴，因此该声明成立），因此单子性路线在这里不可用，论证被在下一层重新运行。这两种发展共享的是架构——将结构构建为一个锥体的中介，其中锥体的边是图表自身的操作，然后从边的联合单性中获取每条定律——而这个文件逐条遵循它。

 有两个地方群的情况比模板更划算。首先，没有构建图像锥：[FCone Grp_Forget N] 恰好是按元素构成的锥（[grp_fcone_apex]、[grp_fcone_leg]，都是 [eq_refl]），而 Eilenberg-Moore 文件声明了它自己的 [car_cone] 和 [rcar_cone]。其次，[grp_reflects] 不需要边的假设：它直接针对 [IsLimitCone (FCone Grp_Forget M)] 陈述，这正是 [screates_reflect] 条款，其中 [em_reflects] 必须携带一个 [Hlegs] 参数，将其抽象极限与锥的边联系起来。引擎是一个可复用的引理，里面没有任何群论内容。
 [sets_limit_ext] 表示 [Sets] 中极限锥的各条腿在元素层面上是联合单射的：从顶点出来的两点在每条腿上都相等。仅凭中介的唯一性就可以证明这一点，用来自顶点本身的两个恒等映射作为探针——所以它不需要终对象，也不引入额外的模块。下面的每一个群律都是三行：应用它，重写定义三角形，在 [K j] 中应用该律。它应放在 Instance/Sets/Complete.v 的捐赠者旁边；这里声明它，以便此更改不影响上游文件。可重用性（问题的工作项3），如其所体现的强度。[sets_limit_ext]以及论证框架可转移到[Sets]—[CMon]、[Ab]、[Rng]、[RMod]上的任意集合代数类别——在这两者中均没有专门针对群签名的内容；这是工程判断，这里未对其进行任何编译。未完成的是签名参数化的声明，原因并不是显而易见的底层是带公理的：测量表明，Instance/Comp.v中的[Algs]和[GroupOp]在全局上下文下都是闭合的。它是这样的：
 [Algs S] 是一个没有方程的操作签名的代数范畴，所以为了得到一个群的范畴，需要方程层，并且 [GroupEq]、[Group] 和 [Product]（都在 Instance/Comp.v 中）都包含 [functional_extensionality_dep]；此外，[Group] 是一个没有附加范畴的代数的 [Type]，Instance/Grp.v 自身的头文件有记录，所以树中的任何内容都不将它与 [Grp] 关联。因此，签名泛化的路径是一种构造而不是实例化，并且未被尝试——这是一个 SCOPE 的选择，附带一个量化的成本，而不是证明不存在这样的路径。唯一性是定理2的全部内容，并且被两次证明，在两个不同的强度下。元素层面上，[glim_unit_unique]、[glim_mul_unique] 和 [glim_inv_unique] 显示每个运算由腿条件决定，[glim_structure_unique] 将它们打包；注意它们消耗的内容 —— 仅仅是腿保持候选结构，而不涉及其任何规律，因此这个陈述比“任何使投影成为同态的群结构就是这个结构”更精确。范畴层面上，[Grp_lift_cone_unique] 是此实例下的通用 [screates_lift_unique]，给出了典范锥同构。完整记录声明“ [G' = LimitGroup] 对于该载体上的任何群 [G']”未被传递，并且这不是通过这里更多工作可以弥补的空白：它需要 [grp_setoid G' = vertex_obj[L] 作为莱布尼兹等式以及在每个操作类型中的传输，这就是为什么 Eilenberg-Moore 文件的 [em_alg_unique] 以相同方式固定其载体。UNIVERSES，通过绑定器和块测量了所有83个常数：
 ZERO word-bounded [Set] 在任何地方的出现次数为零，只有十个带有块方程。五个是通用的 [Sets] 部分——[sets_pre]、[sets_med_eq]、[sets_limit_ext]、[sets_const] 及其 [Program] 义务 [sets_const_obligation_1]，没有任何源级读取能看到——这五个都带有 [u0 = u3]，它将该形状的 hom-and-proof 宇宙与 [Sets] 的承载宇宙联系起来，并且前三个还额外带有 [u1 = u2]，它标识了两个环境的；[u0 = u3] 是 [IsALimit] 的操作，而非此文件的，探针在 [IsALimit] 被拒绝的相同级别上以 [Cone] 接受它。其他五个是 [grp_complete_*] 的回读，它们明确绑定其形状，因此携带 [u = u0]，识别形状的对象宇宙与其同与证明宇宙——也就是 [Complete] 自己的 [@{u u u u0}] 形状被写出，继承自 [Sets_Complete] 并且在这里没有缩小。其余的 73 个常数不携带任何区块方程，[Grp_Complete@{u u0 u1} : Complete@{u u u u0}] 与 [u < u0] 和 [u0 <= u1] 其中，所以小规模的纪律正是 [Sets_Complete] 的。正确地阅读那些活页夹中的 hom = 证明 身份信息：每个 [Category@{u u0 u0}] 都是形状，并且该身份信息属于极限词汇，而不是 [Grp] 或 [Sets] ——在其 hom 明确低于其证明宇宙的形状声明下，[Jv]、[Jv ⟶ Grp]、[Cone] 和 [@Complete Grp] 都被接受，而 [IsALimit]、[Limit]、[CreatesLimit]、[StrictlyCreatesLimit] 和 [Grp_Complete Jv Kv] 都被拒绝。它既不是由此文件也不是由其声明引入的。Test/ProbeGrpLimit411.v 包含此文件记录的两个拒绝项以及消费者遇到的宇宙边界：三种类型的四个负项，加上一个无范围的仪器检查，每次在整个探针的副本中单独移除并单独编译。此文件在 [eq_refl] 所声称的内容在此以 [Example] 的形式发布，因此自我保护。[make todo] 增长了 13，其中全部在该探针中；此文件贡献为零，因此问题的“未增加新命中”框按原文未满足，并被披露而非掩盖。未交付：[Grp] 没有余极限也没有余完备性（Awodey §5.6 的 Omega-余极限部分是 #561 的，而它所需的过滤余极限机制在树中无处存在）-- 更正 (#450)：[Grp] 自 #450 起是余完备的，根据 Instance/Grp/Colimit.v 的 [Grp_Cocomplete_via_GAFT] ，在对角应用伴随函子定理时使用此文件的 [Grp_Complete] 作为其完备性假设；这不是过滤余极限的路径，该路径仍然缺失，而且这些余极限都无法计算；没有签名通用的变体，如上所述；也没有将创建的二元积与 Instance/Grp.v 的 [Grp_Cartesian] 进行比较，这将通过一个离散图，从而通过 Instance/Discrete.v 中未经注释的 [DiscreteCat_Functor]，将所处的 Hom 和证明宇宙固定为字面上的 [Set] -- 更正 (#450)：tha到#450之前，理由已经停止成立。PR “代数承载体是集合”已标注
 [DiscreteCat_Functor] 已就位，[About] 读取
 [DiscreteCat_Functor@{o h p uo uh up u}] 在 [C : Category@{uo uh up}] 上
 其约束块中没有 [Set]；比较本身仍未进行；没有 [CMon]、[Ab]、[Rng] 或 [RMod] 的类似物，尽管引擎保持不变；没有单子性声明，也没有比较函子，因此这里没有任何内容表示 [Grp] 是一个 Eilenberg-Moore 范畴；而且没有任何内容被注册为 [Instance]——文件没有声明任何，遵循其模板，因为选定的极限不能成为全局可解析的。
*)

(* * * Joint monicity of limit legs in [Sets], elementwise / * * 在 [Sets] 中极限腿的联合单调性，按元素 *)

Section SetsExt.

Context {J : Category}.
Context {F : J ⟶ Sets}.
Context {c : Sets}.
Context (H : IsALimit F c).

Definition sets_pre {d : Sets} (u : d ~{Sets}~> c) : Cone F :=
  @Build_Cone J Sets F d
    (@Build_ACone J Sets d F (fun j => limit_leg H j ∘ u)
       (fun x y f =>
          transitivity (comp_assoc _ _ _)
            (@compose_respects Sets _ _ _ _ _ (limit_leg_coherence H f) _ _
               (reflexivity u)))).

Lemma sets_med_eq {d : Sets} (u v : d ~{Sets}~> c) :
  (∀ j : J, limit_leg H j ∘ u ≈ limit_leg H j ∘ v) → u ≈ v.
Proof.
  intro Huv.
  apply (limit_med_eq H (sets_pre u)).
  - intro j; reflexivity.
  - intro j; symmetry; apply Huv.
Qed.

Program Definition sets_const (x : carrier c) : c ~{Sets}~> c :=
  {| morphism := fun _ => x |}.

Lemma sets_limit_ext (x y : carrier c) :
  (∀ j : J, limit_leg H j x ≈ limit_leg H j y) → x ≈ y.
Proof.
  intro Hxy.
  exact (sets_med_eq (sets_const x) (sets_const y) (fun j a => Hxy j) x).
Qed.

End SetsExt.

(* * * The created group structure on a limit of underlying sets / * * 在基础集合的极限上创建的群结构 *)

Section GrpLift.

Context {J : Category}.
Context (K : J ⟶ Grp).
Context (L : Limit (Grp_Forget ◯ K)).

Definition glim_leg (j : J) : vertex_obj[L] ~{Sets}~> grp_setoid (K j) :=
  limit_leg (limit_is_alimit L) j.

Lemma glim_leg_coherence {x y : J} (f : x ~{J}~> y)
  (a : carrier vertex_obj[L]) :
  grp_map (fmap[K] f) (glim_leg x a) ≈ glim_leg y a.
Proof. exact (limit_leg_coherence (limit_is_alimit L) f a). Qed.

Lemma glim_ext (x y : carrier vertex_obj[L]) :
  (∀ j : J, glim_leg j x ≈ glim_leg j y) → x ≈ y.
Proof. exact (sets_limit_ext (limit_is_alimit L) x y). Qed.

(** ** The multiplication / ** 乘法 *)

Definition glim_pair : Sets :=
  {| carrier   := carrier vertex_obj[L] * carrier vertex_obj[L]
   ; is_setoid := prod_setoid |}.

Program Definition glim_mul_leg (j : J) :
  glim_pair ~{Sets}~> grp_setoid (K j) :=
  {| morphism := fun p =>
       grp_mul (K j) (glim_leg j (fst p)) (glim_leg j (snd p)) |}.
Next Obligation.
  intros p q Hpq.
  destruct Hpq as [H1 H2].
  now rewrite H1, H2.
Qed.

Lemma glim_mul_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Grp_Forget ◯ K] f ∘ glim_mul_leg x ≈ glim_mul_leg y.
Proof.
  intro p; simpl.
  rewrite grp_map_mul.
  now rewrite !glim_leg_coherence.
Qed.

Definition glim_mul_cone : Cone (Grp_Forget ◯ K) :=
  @Build_Cone J Sets (Grp_Forget ◯ K) glim_pair
    (@Build_ACone J Sets glim_pair (Grp_Forget ◯ K)
       glim_mul_leg (@glim_mul_coherence)).

Definition glim_mul_map : glim_pair ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) glim_mul_cone.

Definition glim_mul (a b : carrier vertex_obj[L]) : carrier vertex_obj[L] :=
  glim_mul_map (a, b).

Lemma glim_mul_triangle (j : J) (a b : carrier vertex_obj[L]) :
  glim_leg j (glim_mul a b) ≈ grp_mul (K j) (glim_leg j a) (glim_leg j b).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) glim_mul_cone j (a, b)).
Qed.

Lemma glim_mul_respects :
  Proper (equiv ==> equiv ==> equiv) glim_mul.
Proof.
  intros a a' Ha b b' Hb.
  exact (proper_morphism glim_mul_map (a, b) (a', b') (Ha, Hb)).
Qed.

(** ** The unit *)

Program Definition glim_unit_leg (j : J) :
  unit_setoid_object ~{Sets}~> grp_setoid (K j) :=
  {| morphism := fun _ => grp_unit (K j) |}.

Lemma glim_unit_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Grp_Forget ◯ K] f ∘ glim_unit_leg x ≈ glim_unit_leg y.
Proof. intro p; simpl; apply grp_map_unit. Qed.

Definition glim_unit_cone : Cone (Grp_Forget ◯ K) :=
  @Build_Cone J Sets (Grp_Forget ◯ K) unit_setoid_object
    (@Build_ACone J Sets unit_setoid_object (Grp_Forget ◯ K)
       glim_unit_leg (@glim_unit_coherence)).

Definition glim_unit_map : unit_setoid_object ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) glim_unit_cone.

Definition glim_unit : carrier vertex_obj[L] := glim_unit_map ttt.

Lemma glim_unit_triangle (j : J) :
  glim_leg j glim_unit ≈ grp_unit (K j).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) glim_unit_cone j ttt).
Qed.

(** ** The inversion / ** 倒置 *)

Program Definition glim_inv_leg (j : J) :
  vertex_obj[L] ~{Sets}~> grp_setoid (K j) :=
  {| morphism := fun a => grp_inv (K j) (glim_leg j a) |}.
Next Obligation. intros a b Hab; now rewrite Hab. Qed.

Lemma glim_inv_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Grp_Forget ◯ K] f ∘ glim_inv_leg x ≈ glim_inv_leg y.
Proof.
  intro a; simpl.
  rewrite grp_map_inv.
  now rewrite glim_leg_coherence.
Qed.

Definition glim_inv_cone : Cone (Grp_Forget ◯ K) :=
  @Build_Cone J Sets (Grp_Forget ◯ K) vertex_obj[L]
    (@Build_ACone J Sets vertex_obj[L] (Grp_Forget ◯ K)
       glim_inv_leg (@glim_inv_coherence)).

Definition glim_inv_map : vertex_obj[L] ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) glim_inv_cone.

Definition glim_inv (a : carrier vertex_obj[L]) : carrier vertex_obj[L] :=
  glim_inv_map a.

Lemma glim_inv_triangle (j : J) (a : carrier vertex_obj[L]) :
  glim_leg j (glim_inv a) ≈ grp_inv (K j) (glim_leg j a).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) glim_inv_cone j a).
Qed.


(* * ** The group laws, by joint monicity of the legs / * ** 群法则，通过腿的联合一性 *)

Lemma glim_assoc (a b c : carrier vertex_obj[L]) :
  glim_mul (glim_mul a b) c ≈ glim_mul a (glim_mul b c).
Proof.
  apply glim_ext; intro j.
  rewrite !glim_mul_triangle.
  apply grp_mul_assoc.
Qed.

Lemma glim_unit_l (a : carrier vertex_obj[L]) : glim_mul glim_unit a ≈ a.
Proof.
  apply glim_ext; intro j.
  rewrite glim_mul_triangle, glim_unit_triangle.
  apply grp_mul_unit_l.
Qed.

Lemma glim_inv_l (a : carrier vertex_obj[L]) :
  glim_mul (glim_inv a) a ≈ glim_unit.
Proof.
  apply glim_ext; intro j.
  rewrite glim_mul_triangle, glim_inv_triangle, glim_unit_triangle.
  apply grp_mul_inv_l.
Qed.

(** ** The lifted group / ** 提升的群体 *)

(*
 G3.  The vertex's `≈` is detected by the legs ([glim_ext]), so a limit of
 propositional setoids is propositional: two points are related when every
 leg relates their images under the component group's own [grp_prop].  This
 is [alim_prop]'s route at Instance/Ab/Limit.v, and it needs NO hypothesis
 on [L] -- which matters, because [CreatesLimits] quantifies over every [L]
 and leaves nowhere to put one. 

 --------
 G3. 顶点的 `≈` 由腿 ([glim_ext]) 检测，因此命题型集合的极限是命题型的：当每条腿都将它们在组分自身的 [grp_prop] 下的像联系起来时，两点就是相关的。这是 [alim_prop] 在 Instance/Ab/Limit.v 中的路径，并且它不需要对 [L] 的任何假设——这很重要，因为 [CreatesLimits] 对每个 [L] 进行量化，并且没有地方可以放置假设。
*)
Definition glim_prop : PropEquiv (is_setoid vertex_obj[L]) :=
  @PropEquiv_of_relation _ (is_setoid vertex_obj[L])
    (fun x y => forall j : J,
       @pequiv _ _ (grp_prop (K j)) (glim_leg j x) (glim_leg j y))
    (fun x y H => glim_ext x y (fun j => pequiv_to _ _ (H j)))
    (fun x y H j => pequiv_from _ _ (proper_morphism (glim_leg j) x y H)).

Definition LimitGroup : GrpObject :=
  {| grp_setoid       := vertex_obj[L]
   ; grp_unit         := glim_unit
   ; grp_mul          := glim_mul
   ; grp_inv          := glim_inv
   ; grp_mul_respects := glim_mul_respects
   ; grp_mul_assoc    := glim_assoc
   ; grp_mul_unit_l   := glim_unit_l
   ; grp_mul_inv_l    := glim_inv_l
   ; grp_prop         := glim_prop |}.

(** ** The legs are homomorphisms / ** 腿是同态 *)

Program Definition glim_hom (j : J) : GrpHom LimitGroup (K j) :=
  {| grp_map := glim_leg j |}.
Next Obligation. apply glim_unit_triangle. Qed.
Next Obligation. apply glim_mul_triangle. Qed.

Lemma glim_hom_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ glim_hom x ≈ glim_hom y.
Proof. intro a; exact (glim_leg_coherence f a). Qed.

Definition glim_cone : Cone K :=
  @Build_Cone J Grp K LimitGroup
    (@Build_ACone J Grp LimitGroup K glim_hom (@glim_hom_coherence)).

(* * ** Strictness: the lifted cone lies over [L] on the nose / * ** 严格性：被抬起的圆锥位于鼻子上的 [L] 上 *)

Definition glim_over_obj : Grp_Forget LimitGroup = vertex_obj[L] := eq_refl.

Definition glim_over_legs (j : J) :
  fmap[Grp_Forget] (cone_leg glim_cone j) = glim_leg j := eq_refl.


(** ** The lifted cone is limiting / ** 提升的锥体是有限的 *)

Definition gcar_med (N : Cone K) :
  grp_setoid vertex_obj[N] ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) (FCone Grp_Forget N).

Lemma gcar_med_commutes (N : Cone K) (j : J) (a : carrier vertex_obj[N]) :
  glim_leg j (gcar_med N a) ≈ grp_map (cone_leg N j) a.
Proof.
  exact (limit_med_commutes (limit_is_alimit L) (FCone Grp_Forget N) j a).
Qed.

Lemma gcar_med_unit (N : Cone K) :
  gcar_med N (grp_unit vertex_obj[N]) ≈ glim_unit.
Proof.
  apply glim_ext; intro j.
  rewrite gcar_med_commutes, glim_unit_triangle.
  apply grp_map_unit.
Qed.

Lemma gcar_med_mul (N : Cone K) (a b : carrier vertex_obj[N]) :
  gcar_med N (grp_mul vertex_obj[N] a b)
    ≈ glim_mul (gcar_med N a) (gcar_med N b).
Proof.
  apply glim_ext; intro j.
  rewrite gcar_med_commutes, glim_mul_triangle, !gcar_med_commutes.
  apply grp_map_mul.
Qed.

Program Definition glim_med (N : Cone K) : vertex_obj[N] ~{Grp}~> LimitGroup :=
  {| grp_map := gcar_med N |}.
Next Obligation. apply gcar_med_unit. Qed.
Next Obligation. apply gcar_med_mul. Qed.

Definition glim_created : IsALimit K LimitGroup.
Proof.
  unshelve refine {| limit_acone := @coneFrom _ _ _ glim_cone |}.
  intro N.
  unshelve refine {| unique_obj := glim_med N |}.
  - intros j a.
    exact (gcar_med_commutes N j a).
  - intros v Hv a.
    exact (limit_med_unique (limit_is_alimit L) (FCone Grp_Forget N)
             (grp_map v) Hv a).
Defined.


(* * ** Uniqueness of the lifted structure (Mac Lane's Theorem 2) / * ** 提升结构的唯一性（Mac Lane 定理 2） *)

Lemma glim_unit_unique (e : carrier vertex_obj[L])
  (He : ∀ j : J, glim_leg j e ≈ grp_unit (K j)) : e ≈ glim_unit.
Proof.
  apply glim_ext; intro j.
  now rewrite He, glim_unit_triangle.
Qed.

Lemma glim_mul_unique
  (m : carrier vertex_obj[L] → carrier vertex_obj[L] → carrier vertex_obj[L])
  (Hm : ∀ (j : J) a b,
     glim_leg j (m a b) ≈ grp_mul (K j) (glim_leg j a) (glim_leg j b))
  (a b : carrier vertex_obj[L]) : m a b ≈ glim_mul a b.
Proof.
  apply glim_ext; intro j.
  now rewrite Hm, glim_mul_triangle.
Qed.

Lemma glim_inv_unique
  (i : carrier vertex_obj[L] → carrier vertex_obj[L])
  (Hi : ∀ (j : J) a, glim_leg j (i a) ≈ grp_inv (K j) (glim_leg j a))
  (a : carrier vertex_obj[L]) : i a ≈ glim_inv a.
Proof.
  apply glim_ext; intro j.
  now rewrite Hi, glim_inv_triangle.
Qed.


(*
 The three clauses together: Mac Lane's "there is exactly one group
 structure on the limit making every projection a homomorphism".  No law
 of the candidate structure is consumed -- only that the legs preserve
 it. 

 --------
 三个条款一起：Mac Lane 的“在极限上恰好存在一个群结构，使得每个投射都是同态”。候选结构的任何定律都没有被使用——只是其支腿保持了该结构。
*)
Lemma glim_structure_unique
  (e : carrier vertex_obj[L])
  (m : carrier vertex_obj[L] → carrier vertex_obj[L] → carrier vertex_obj[L])
  (i : carrier vertex_obj[L] → carrier vertex_obj[L])
  (He : ∀ j : J, glim_leg j e ≈ grp_unit (K j))
  (Hm : ∀ (j : J) a b,
     glim_leg j (m a b) ≈ grp_mul (K j) (glim_leg j a) (glim_leg j b))
  (Hi : ∀ (j : J) a, glim_leg j (i a) ≈ grp_inv (K j) (glim_leg j a)) :
  (e ≈ glim_unit)
    * (∀ a b, m a b ≈ glim_mul a b)
    * (∀ a, i a ≈ glim_inv a).
Proof.
  split; [ split | ].
  - exact (glim_unit_unique e He).
  - exact (glim_mul_unique m Hm).
  - exact (glim_inv_unique i Hi).
Qed.

End GrpLift.

(* * * Reflection: a cone of groups whose image is limiting is limiting / * * 反思：一个群体圆锥，如果它的像是极限的，那么它本身也是极限的 *)

Section GrpReflect.

Context {J : Category}.
Context (K : J ⟶ Grp).
Context (M : Cone K).
Context (HM : IsLimitCone (FCone Grp_Forget M)).

Definition grefl_med (N : Cone K) :
  grp_setoid vertex_obj[N] ~{Sets}~> grp_setoid vertex_obj[M] :=
  limit_med (limitcone_isalimit HM) (FCone Grp_Forget N).

Lemma grefl_med_commutes (N : Cone K) (j : J) (a : carrier vertex_obj[N]) :
  grp_map (cone_leg M j) (grefl_med N a) ≈ grp_map (cone_leg N j) a.
Proof using All.
  exact (limit_med_commutes (limitcone_isalimit HM) (FCone Grp_Forget N) j a).
Qed.

Lemma grefl_ext (x y : carrier vertex_obj[M]) :
  (∀ j : J, grp_map (cone_leg M j) x ≈ grp_map (cone_leg M j) y) → x ≈ y.
Proof using All. exact (sets_limit_ext (limitcone_isalimit HM) x y). Qed.

Lemma grefl_med_unit (N : Cone K) :
  grefl_med N (grp_unit vertex_obj[N]) ≈ grp_unit vertex_obj[M].
Proof using All.
  apply grefl_ext; intro j.
  rewrite grefl_med_commutes, !grp_map_unit.
  reflexivity.
Qed.

Lemma grefl_med_mul (N : Cone K) (a b : carrier vertex_obj[N]) :
  grefl_med N (grp_mul vertex_obj[N] a b)
    ≈ grp_mul vertex_obj[M] (grefl_med N a) (grefl_med N b).
Proof using All.
  apply grefl_ext; intro j.
  rewrite grefl_med_commutes, !grp_map_mul, !grefl_med_commutes.
  reflexivity.
Qed.

Program Definition grefl_hom (N : Cone K) :
  vertex_obj[N] ~{Grp}~> vertex_obj[M] := {| grp_map := grefl_med N |}.
Next Obligation. apply grefl_med_unit. Qed.
Next Obligation. apply grefl_med_mul. Qed.

Definition grp_reflects : IsLimitCone M.
Proof using All.
  intro N.
  unshelve refine {| unique_obj := grefl_hom N |}.
  - intros j a.
    exact (grefl_med_commutes N j a).
  - intros v Hv a.
    exact (limit_med_unique (limitcone_isalimit HM) (FCone Grp_Forget N)
             (grp_map v) Hv a).
Defined.

End GrpReflect.

(* * * [Grp_Forget] strictly creates every limit / * * [Grp_Forget] 严格地创造每一个限制 *)

Section GrpStrictlyCreates.

Context {J : Category}.
Context (K : J ⟶ Grp).

Definition grp_strict_lift (N : Cone (Grp_Forget ◯ K)) (HN : IsLimitCone N) :
  StrictLift K Grp_Forget N :=
  @Build_StrictLift J Grp Sets K Grp_Forget N
    (glim_cone K (@Build_Limit J Sets (Grp_Forget ◯ K) N HN))
    eq_refl
    (fun x => reflexivity _).

Definition Grp_Forget_StrictlyCreatesLimit : StrictlyCreatesLimit K Grp_Forget.
Proof.
  unshelve refine {| screates := grp_strict_lift |}.
  - intros N HN.
    exact (@ump_limit _ _ _ _
             (glim_created K (@Build_Limit J Sets (Grp_Forget ◯ K) N HN))).
  - intros M HM.
    exact (grp_reflects K M HM).
Defined.

Definition Grp_Forget_CreatesLimit : CreatesLimit K Grp_Forget :=
  StrictlyCreatesLimit_CreatesLimit Grp_Forget_StrictlyCreatesLimit.

End GrpStrictlyCreates.

Definition Grp_Forget_StrictlyCreatesLimits :
  StrictlyCreatesLimits Grp_Forget :=
  fun J K => Grp_Forget_StrictlyCreatesLimit K.

Definition Grp_Forget_creates_limits : CreatesAllLimits Grp_Forget :=
  fun J K => Grp_Forget_CreatesLimit K.

Definition Grp_Forget_reflects_limits {J : Category} (K : J ⟶ Grp) :
  ReflectsLimitCone K Grp_Forget :=
  creates_reflects_limits (Grp_Forget_CreatesLimit K).

(*
 Mac Lane's uniqueness clause at the categorical level: any cone of
 groups lying over [N] is canonically isomorphic to the created one.
 This is the generic [screates_lift_unique] at this instance, not a
 restatement. 

 --------
 麦克莱恩在范畴层次的唯一性条款：任何位于  [N] 上的群锥都与所创建的锥具有自然同构。这是此实例下的通用  [screates_lift_unique] ，而不是重新表述。
*)

Definition Grp_lift_cone_unique {J : Category} (K : J ⟶ Grp)
  (N : Cone (Grp_Forget ◯ K)) (HN : IsLimitCone N)
  (M : Cone K) (i : ConeIso (FCone Grp_Forget M) N) :
  ConeIso M (slift_cone (screates N HN)) :=
  screates_lift_unique (Grp_Forget_StrictlyCreatesLimit K) N HN M i.

(* * * The image of a cone of groups is the elementwise cone / * * 群的圆锥图像是逐元素圆锥 *)

Example grp_fcone_apex {J : Category} (K : J ⟶ Grp) (N : Cone K) :
  vertex_obj[FCone Grp_Forget N] = grp_setoid vertex_obj[N] := eq_refl.

Example grp_fcone_leg {J : Category} (K : J ⟶ Grp) (N : Cone K) (j : J) :
  cone_leg (FCone Grp_Forget N) j = grp_map (cone_leg N j) := eq_refl.

(* * * Mac Lane's Theorem 2: the lifting half / * * 麦克雷恩定理2：提升部分 *)

Definition Grp_Forget_lifts_limits {J : Category} (K : J ⟶ Grp)
  (L : Limit (Grp_Forget ◯ K)) : Limit K :=
  creates_limit_lift (Grp_Forget_CreatesLimit K) L.

Example grp_lift_apex {J : Category} (K : J ⟶ Grp)
  (L : Limit (Grp_Forget ◯ K)) :
  Grp_Forget (vertex_obj[Grp_Forget_lifts_limits K L]) = vertex_obj[L]
  := eq_refl.

Example grp_lift_legs {J : Category} (K : J ⟶ Grp)
  (L : Limit (Grp_Forget ◯ K)) (j : J) :
  fmap[Grp_Forget]
    (cone_leg (@limit_cone _ _ _ (Grp_Forget_lifts_limits K L)) j)
    = limit_leg (limit_is_alimit L) j
  := eq_refl.

(* * * Corollaries: [Grp] is complete and [Grp_Forget] is continuous / * * 推论：[Grp] 是完备的，[Grp_Forget] 是连续的 *)

Definition Grp_Complete : @Complete Grp :=
  creates_limits_Complete Grp_Forget Sets_Complete Grp_Forget_creates_limits.

(*
 [ContinuousFunctor] is [PreservesLimitCone] quantified over every shape
 and diagram, which is what the word means in Mac Lane §V.4 -- the
 apex-only [PreservesAllLimits] below is its CONSEQUENCE, not the
 definition (Structure/Limit/Preservation.v). 

 --------
 [ContinuousFunctor] 是在每个形状和图表上量化的 [PreservesLimitCone]，这就是 Mac Lane §V.4 中这个词的含义——下面仅顶点的 [PreservesAllLimits] 是它的结果，而不是定义（Structure/Limit/Preservation.v）。
*)

Definition Grp_Forget_continuous : ContinuousFunctor Grp_Forget :=
  creates_limits_continuous Grp_Forget Sets_Complete Grp_Forget_creates_limits.

Definition Grp_Forget_PreservesAllLimits : PreservesAllLimits Grp_Forget :=
  creates_limits_PreservesAllLimits Grp_Forget Sets_Complete
    Grp_Forget_creates_limits.

(* * * "Limits of groups are computed on underlying sets", literally / * * “群的极限是基于其底层集合计算的”，字面意思 *)

(*
 At the limits [Sets_Complete] chooses -- the compatible families of
 Instance/Sets/Complete.v -- the created group is the coordinatewise one
 ON THE NOSE: carrier, multiplication, unit, inversion and every
 projection are all [eq_refl], at an ARBITRARY shape and an ARBITRARY
 diagram of groups.  Nothing here is specific to a witness category; the
 readbacks below are the section header's sentence machine-checked. 

 --------
 在极限处，[Sets_Complete] 选择 -- Instance/Sets/Complete.v 的兼容族 -- 创建的群正是坐标逐点的群：载体、乘法、单位、逆元以及每一个投影在任意形状和任意群图下都是 [eq_refl]。这里没有任何内容是特定于见证范畴的；下面的回读是章节标题的句子经过机器校验的结果。
*)

Section GrpComputed.

Context {J : Category}.
Context (K : J ⟶ Grp).

Example grp_complete_carrier :
  grp_setoid (vertex_obj[Grp_Complete J K]) = Sets_limit_obj (Grp_Forget ◯ K)
  := eq_refl.

Example grp_complete_mul
  (a b : carrier (Sets_limit_obj (Grp_Forget ◯ K))) (d : J) :
  `1 (grp_mul (vertex_obj[Grp_Complete J K]) a b) d
    = grp_mul (K d) (`1 a d) (`1 b d) := eq_refl.

Example grp_complete_unit (d : J) :
  `1 (grp_unit (vertex_obj[Grp_Complete J K])) d = grp_unit (K d) := eq_refl.

Example grp_complete_inv
  (a : carrier (Sets_limit_obj (Grp_Forget ◯ K))) (d : J) :
  `1 (grp_inv (vertex_obj[Grp_Complete J K]) a) d
    = grp_inv (K d) (`1 a d) := eq_refl.

Example grp_complete_leg (d : J) :
  grp_map (cone_leg (@limit_cone _ _ _ (Grp_Complete J K)) d)
    = Sets_limit_leg (Grp_Forget ◯ K) d := eq_refl.

End GrpComputed.
