Require Import Category.Lib.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.Limit.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Structure.Generator.Dual.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Instance.Sets.Generator.
Require Import Category.Instance.Sets.SubobjectLattice.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Sets.WellPowered.
Require Import Category.Instance.Sets.Cogenerator.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.SAFT.InitialObject.

Generalizable All Variables.

(*
 The special initial-object theorem at [Sets^op] and at [Sets]

 nLab:  https://ncatlab.org/nlab/show/initial+object
 nLab:  https://ncatlab.org/nlab/show/adjoint+functor+theorem

 Mac Lane, “Categories for the Working Mathematician”, 2nd ed. (GTM 5),
 §V.8, Theorem 1, book p. 128 (PDF pp. 137–138): a small-complete
 category with small hom-sets, a small cogenerating set, and an
 intersection for every set of subobjects of each object has an initial
 object, the intersection of all subobjects of the product of the
 cogenerating set.  Riehl, “Category Theory in Context”, 2nd ed., Lemma
 4.7.11, printed p. 177 (PDF pp. 197–198), states the same for a locally
 small complete category with a small coseparating set.  Mac Lane's note
 under §V.8 Definition 1, book p. 130 (PDF p. 139), makes the
 intersection hypothesis automatic for a well-powered small-complete
 category.  Adjunction/SAFT/InitialObject.v proves the theorem over an
 arbitrary category in three hypothesis forms and that corollary; this
 file runs it at the two categories of setoids for which the tree can
 supply the hypotheses, and reads what it returns against the initial
 object each category is already known to have.

 WHAT IS CONSUMED AND BUILT.

 (1) [Sets^op], unconditionally.  Completeness is
 Construction/Product/Limit.v's [Complete_op_of_Cocomplete] of
 Instance/Sets/Cocomplete.v's [Sets_Cocomplete] ([setsop_comp]).  The
 cogenerator is Structure/Generator/Dual.v's [cog_of_gen] of
 Instance/Sets/Generator.v's [Sets_Generator], the singleton
 ([setsop_cog]).  It is a genuine separator of a category that is
 not thin (Theory/Concrete.v's [Sets_two_arrows]), so [cog_separates]
 does real work where the theorem's existence half consumes it,
 inside Adjunction/SAFT.v's [cogenerator_canonical_monic].  The
 least subobject of the cogenerator product [P] is built by hand:
 [setsop_L] is the map [P → 1] into Instance/Sets.v's
 [Sets_Terminal] object, read in [Sets^op] as a mono [1 ↣ P].
 Monicity in [Sets^op] is epicity of [P → 1] in [Sets], which needs
 a point of [P]; [setsop_point] is the coprojection of the one
 element of the singleton factor.  [setsop_L_least] shows every
 subobject of [P] in [Sets^op] lies above it, since all arrows into
 [1] agree.  [setsop_special_initial] is the headline
 [special_initial_object], fed through [intersection_all_of_least].
 [setsop_terminal_IsInitialObj] states the conclusion in the type:
 the singleton is initial in [Sets^op].

 (2) [Sets], under [Untruncate], in three ways, the one hypothesis [U]
 supplying the cogenerator (Instance/Sets/Cogenerator.v's
 [Sets_Cogenerator_untruncate]) and whatever else is needed.
 (a) The least subobject: Theory/Subobject/Lattice.v's [sub_bot] at
 Instance/Sets/SubobjectLattice.v's [Sets_zero_monic], least by
 [sub_bot_least] ([sets_special_initial_untruncate]).
 (b) The well-powered corollary: [special_initial_object_wellpowered]
 with Instance/Sets/WellPowered.v's [Sets_WellPowered_untruncate]
 (#451) ([sets_special_initial_wellpowered]).
 (c) The book's blanket hypothesis: Instance/Sets/WellPowered.v's
 [Sets_wellpowered_intersection] is, as it stands, an inhabitant
 of [HasClassIntersections] at [Sets]
 ([Sets_HasClassIntersections_untruncate] is its eta-expansion),
 and [special_initial_object_book] consumes it
 ([sets_special_initial_book]).

 (3) [Sets], under [IEM], through the least subobject, with
 Instance/Sets/Cogenerator.v's [Sets_Cogenerator_IEM]
 ([sets_special_initial_IEM]).  [sets_special_initial_IEM_at_Set]
 is the instance at carrier universe [Set], accepted.

 THE CIRCULARITY CAVEAT.  In (1), (2a) and (3) the least subobject
 handed to the theorem is BUILT FROM the known initial object: the
 domain of [sub_bot] is [Sets_Initial]'s empty setoid, the domain of
 [setsop_L] is [Sets_Terminal]'s singleton.  The theorem then
 rediscovers that object, and the [eq_refl] readbacks below say exactly
 that and no more.  What those three witnesses exercise is the rest of
 the machinery: completeness, the cogenerator product, the canonical
 monic and with it [cog_separates], the pullbacks of the existence half
 and the equalizer argument of the uniqueness half.  Only (2b) and (2c)
 COMPUTE the least subobject, as an intersection: (2b) as
 Structure/WellPowered.v's [complete_intersection] of the well-powered
 class family, (2c) as Instance/Sets/WellPowered.v's wide pullback over
 a small reindexing of the class.  There the comparison with the known
 initial object is [initial_unique], not [eq_refl].

 STRENGTHS, strict first.
 - [eq_refl], the object IS the known initial object:
 [setsop_special_obj] (the initial object of [Sets^op] returned is
 [@terminal_obj Sets Sets_Terminal]), [sets_special_untruncate_obj]
 and [sets_special_IEM_obj] (it is [@initial_obj Sets Sets_Initial]).
 Test/ProbeSpecialInitial452.v's N17 and N18 show that the first
 and last of these discriminate: with the two objects swapped each
 is refused by conversion ([p452_n17_setsop_obj_empty],
 [p452_n18_sets_iem_obj_singleton]).
 - [eq_refl], the object IS the intersection:
 [sets_special_wellpowered_obj], against
 [Subobject.sub_dom (complete_intersection Sets_Complete
 (wp_class_family (Sets_WellPowered_untruncate U (cogen_prod …))
 (fun _ => True)))], and [sets_special_book_obj], against
 [Subobject.sub_dom (`1 (Sets_wellpowered_intersection U
 (cogen_prod …) (fun _ => unit) (fun _ _ _ t => t)))].
 - [≅], by Structure/Initial.v's [initial_unique]:
 [setsop_special_vs_known] (against [Sets_Terminal] read as an
 [@Initial (Sets^op)], which it is by conversion, since
 [Initial C := @Terminal (C^op)] and [C^op^op] is [C]),
 [sets_special_wellpowered_vs_known] and [sets_special_book_vs_known]
 (against [Sets_Initial]).
 - A theorem: [sets_special_wellpowered_empty], the intersection the
 corollary computes has no elements, read off its own zero arrow
 into [Sets_Initial]'s object.
 Every constant here is closed under the global context (Print
 Assumptions on each); [Untruncate] and [IEM] are hypotheses, not
 axioms.

 UNIVERSES, measured with [Set Printing Universes. About …] against the
 integrated Adjunction/SAFT/InitialObject.v, stdlib bounds left out:

 setsop_special_initial@{o so u} : @Initial Sets@{o so}^op
 ( * o < so, so < u * )
 sets_special_initial_untruncate@{o so u} :
 Untruncate@{o} → @Initial Sets@{o so}   ( * Set < o, o < so, so < u * )
 sets_special_initial_wellpowered@{o so u u0} :
 Untruncate@{o} → @Initial Sets@{o so}
 ( * Set < o, o < so, so < u, u0 <= o * )
 sets_special_initial_book@{o so u u0 u1 u2} :
 Untruncate@{o} → @Initial Sets@{o so}
 ( * Set < o, o < so, o < u0, u < u1, u0 < u2, so <= u1, u <= o,
 u <= so * )
 sets_special_initial_IEM@{o so u} :
 IEM@{o} → @Initial Sets@{o so}   ( * o < so, so < u * )
 sets_special_initial_IEM_at_Set@{so u} :
 IEM@{Set} → @Initial Sets@{Set so}   ( * Set < so, so < u * )

 The [Set < o] of the [Untruncate] witnesses is the cogenerator's
 ([Prop] as a carrier, Instance/Sets/Cogenerator.v), and
 [Sets_WellPowered_untruncate] carries the same bound.  Every binder is
 explicit, and one of them is load-bearing in a way that was measured:
 an unannotated first draft of [setsop_L_least] closed its goal with
 [reflexivity] and pinned the carrier universe to [Set] (About:
 [setsop_L_least@{u} : ∀ v : SubObj@{u Set} (cogen_prod@{Set u Set u
 Set} …)], and [setsop_special_initial] became [@Initial Sets@{Set u}^op]).
 Either change alone removes the pin, both measured in whole-file
 copies: with every binder of the file annotated, [reflexivity] is
 accepted with no [Set]; with every binder removed, [exact eq_refl] in
 place of [reflexivity] is too.  This file does both.

 TWO ROUTES REFUSED, pinned by Test/ProbeSpecialInitial452.v, whose
 import list contains this file's and this file itself, each beside a
 positive control and each read by un-wrapping the refused command in
 its own copy of the WHOLE probe.  In the quotes, a universe the compile
 generated is written <1>, <2>, ..., numbered afresh in each quote in
 order of first appearance, as the probe writes them, so that the
 numerals carry identity and no serial number is a claim:
 - [Sets^op] through the well-powered corollary.  With the datum left
 free, [special_initial_object_wellpowered (C := Sets@{o so}^op) WP
 setsop_comp setsop_cog] is accepted ([p452_setsop_wp_free]); with
 the only co-well-poweredness of [Sets] in tree,
 Instance/Sets/WellPowered.v's [Sets_CoWellPoweredAt_up] (one
 universe up), it is refused, the datum's index living one universe
 above the homs where the corollary needs it at or below them (the
 probe's N15, [p452_n15_setsop_wp_up]):
 “The term ”Sets_CoWellPoweredAt_up X“ has type
 ”WellPoweredAt@{<1> <2> <2> o <1>} X“ while it is expected to
 have type ”WellPoweredAt@{<3> so <4> o <5>} X“ (universe
 inconsistency: Cannot enforce <3> = <5> because <3> <= <6> <
 <5>).”
 The per-object corollary [special_initial_object_wellpowered_at],
 fed [Sets_CoWellPoweredAt_up] at the one object [cogen_prod
 setsop_comp setsop_cog], is refused on universes as well (N16,
 [p452_n16_setsop_wp_at_up]; control [p452_setsop_wp_at_free]).  So
 the hand-built [setsop_L] is what makes [Sets^op] unconditional.
 - [special_initial_object_small] at [Sets]: its universe constraint
 that objects fit the shape universe cannot hold here, objects of
 [Sets@{o so}] living at [so] above [Sets_Complete]'s shape universe
 [o].  With [Sets_Complete] ascribed [Complete@{o o o so}] and
 [Sets_Cogenerator_IEM E] it is refused (N10,
 [p452_n10_small_at_sets]):
 “The term ”Sets_Complete : Complete“ has type ”Complete@{o o o
 so}“ while it is expected to have type ”Complete@{o o o <1>}“
 (universe inconsistency: Cannot enforce <1> = so because <1> <=
 <2> < so).”
 The form first measured on #452 left [Sets_Complete]'s universes
 to inference and is refused at the same argument, with every
 universe a serial number.  The controls, [sets_special_initial_IEM]
 at the same universes and its body with [Sets_Complete] ascribed
 ([p452_sets_iem], [p452_sets_iem_direct]), are accepted.

 NON-VACUITY.  [Sets^op] and [Sets] are not thin, and every cogenerator
 used here is small, indexed by [unit] ([cog_index setsop_cog = unit]
 is accepted by [eq_refl] in a scratch file, through Structure/
 Generator.v's [Generator_of_separator]), and genuine:
 Instance/Sets/Cogenerator.v's [Sets_terminal_not_cogenerates] shows
 the condition excludes every family of copies of the terminal object
 at [Sets], and [Sets_two_arrows] shows [Sets^op] has distinct
 parallel arrows for [setsop_cog] to separate.  The (2b) object is
 proved empty, not assumed.

 NOT DELIVERED.  No unconditional witness at [Sets]: the missing piece
 is a SMALL cogenerator, since Instance/Sets/Cogenerator.v's
 unconditional [Sets_Cogenerator_large] is large and [cogen_prod] at
 [Sets_Complete] refuses it (that file's header).  No [Sets^op]
 witness through the well-powered corollary, and none of (2b)/(2c) at
 [Sets^op]: co-well-poweredness of [Sets] at the pin is not in tree.  No
 normal form of the zero arrows was measured; at [Sets] their domain is
 empty, so there is no element to evaluate them at.  No comparison with
 Freyd's initial object at [Sets] as a constant here: it is not
 attempted, and [initial_unique (sets_special_initial_wellpowered U)
 Sets_initial_recovered] (Theory/WeaklyInitial/Sets.v) is accepted at
 [Sets@{o so}] in a scratch file, closed under the global context, as
 are Adjunction/SAFT/InitialObject.v's [special_vs_freyd] and
 [freyd_of_cogenerator] at [Sets] under [Untruncate].  (CORRECTION,
 #452 fess audit: an earlier revision said [Sets_initial_recovered] is
 pinned at [Sets@{Set _}]; [About] reads [@Initial Sets@{u0 u}] with
 [u0 < u] and no [Set].)  The thin witnesses of the theorem are not
 here. 

 --------
 在 [Sets^op] 和 [Sets] 的特殊初始对象定理

 nLab: https://ncatlab.org/nlab/show/initial+object
 nLab: https://ncatlab.org/nlab/show/adjoint+functor+theoremMac Lane, 《为实际数学家准备的范畴论》，第2版 (GTM 5)，§V.8，第1定理，书页128 (PDF页137–138)：一个具有小型Hom集、小型共生成集合以及每个对象的子对象集合交的完备小范畴，存在一个初始对象，即共生成集合的积的所有子对象的交。Riehl, 《上下文中的范畴论》，第2版，引理4.7.11，印刷页177 (PDF页197–198)，对局部小完备范畴具有小型共分离集合也给出了同样的结论。Mac Lane在§V.8 定义1下的注释，书页130 (PDF页139)，指出对于具备良有势的小完备范畴，交的假设是自动成立的。Adjunction/SAFT/InitialObject.v 在任意范畴上以三种假设形式证明了定理及其推论；该文件在两个集合同构的范畴上运行它，其中树能够提供假设，并将它返回的结果与每个范畴已知存在的初始对象进行比较。

 消耗的和构建的是什么。(1) [Sets^op]，无条件地。完整性是 Construction/Product/Limit.v 的 [Complete_op_of_Cocomplete] 对 Instance/Sets/Cocomplete.v 的 [Sets_Cocomplete]（[setsop_comp]）。余生成元是 Structure/Generator/Dual.v 的 [cog_of_gen] 对 Instance/Sets/Generator.v 的 [Sets_Generator]，单元素 ([setsop_cog])。它是一个非稀薄（Theory/Concrete.v 的 [Sets_two_arrows]）范畴的真正分离子，因此 [cog_separates] 在定理存在性的一半被消耗的情况下发挥实际作用，在 Adjunction/SAFT.v 的 [cogenerator_canonical_monic] 中。余生成元积的最小子对象 [P] 是手工构建的：[setsop_L] 是映射 [P → 1] 到 Instance/Sets.v 的 [Sets_Terminal] 对象，读作 [Sets^op] 中的单射 [1 ↣ P]。[Sets^op] 中的单态性是 [Sets] 中 [P → 1] 的史诗性，这需要一个 [P] 点；[setsop_point] 是单元因子的一个元素的余投影。[setsop_L_least] 显示 [Sets^op] 中 [P] 的每一个子对象都位于它之上，因为进入 [1] 的所有箭头都一致。[setsop_special_initial] 是 [special_initial_object] 的标题，通过 [intersection_all_of_least] 输入。[setsop_terminal_IsInitialObj] 在类型中陈述结论：单子在 [Sets^op] 中是初始的。(2)  [Sets]，在  [Untruncate] 下，有三种方式，一种假设  [U] 提供联发器（Instance/Sets/Cogenerator.v 的 [Sets_Cogenerator_untruncate] ）以及其他所需的一切。
 (a) 最小子对象：Theory/Subobject/Lattice.v 的 [sub_bot] 在 Instance/Sets/SubobjectLattice.v 的 [Sets_zero_monic] 中，最小由 [sub_bot_least] （ [sets_special_initial_untruncate] ）。
 (b) 良幂推论：[special_initial_object_wellpowered] 与 Instance/Sets/WellPowered.v 的 [Sets_WellPowered_untruncate] (#451)（ [sets_special_initial_wellpowered] ）。
 (c) 书中的通用假设：Instance/Sets/WellPowered.v 的 [Sets_wellpowered_intersection] 照原样，是 [HasClassIntersections] 在 [Sets] 中的一个元素（ [Sets_HasClassIntersections_untruncate] 是其 η-展开），并且 [special_initial_object_book] 使用它（ [sets_special_initial_book] ）。(3)  [Sets]，在 [IEM] 下，通过最小子对象，使用 Instance/Sets/Cogenerator.v 的 [Sets_Cogenerator_IEM] ( [sets_special_initial_IEM] )。[sets_special_initial_IEM_at_Set] 是在载体宇宙 [Set] 的实例，已被接受。循环性警告。在 (1)、(2a) 和 (3) 中，交给定理的最小子对象是由已知的初始对象构建的：[sub_bot] 的域是 [Sets_Initial] 的空集合，[setsop_L] 的域是 [Sets_Terminal] 的单元素集合。然后该定理重新发现了该对象，下面的 [eq_refl] 读回值正是说明了这一点，没有更多。那三个例子所展示的是其余的机械部分：完备性、余生成器积、伴随单射及其 [cog_separates] 的存在、存在半部分的拉回以及唯一性半部分的等化器论证。只有 (2b) 和 (2c) 会计算最小子对象，作为交集：(2b) 是 Structure/WellPowered.v 中由良基类族的 [complete_intersection]，(2c) 是 Instance/Sets/WellPowered.v 中对类的小重索引进行的广拉回。在那里，与已知初始对象的比较是 [initial_unique]，而不是 [eq_refl]。优势，严格首先。- [eq_refl]，对象是已知的初始对象：[setsop_special_obj]（返回的[Sets^op]的初始对象是[@terminal_obj Sets Sets_Terminal]），[sets_special_untruncate_obj]和[sets_special_IEM_obj]（它是[@initial_obj Sets Sets_Initial]）。Test/ProbeSpecialInitial452.v 的 N17 和 N18 显示这些对象中的第一个和最后一个可以区分：交换这两个对象时，每个都被转换拒绝（[p452_n17_setsop_obj_empty]，[p452_n18_sets_iem_obj_singleton]）。- [eq_refl]，对象是交集：[sets_special_wellpowered_obj]，针对[Subobject.sub_dom（complete_intersection Sets_Complete (wp_class_family (Sets_WellPowered_untruncate U (cogen_prod …)) (fun _ => True)))], 以及 [sets_special_book_obj]，针对[Subobject.sub_dom（`1 (Sets_wellpowered_intersection U (cogen_prod …) (fun _ => unit) (fun _ _ _ t => t)))]。- [≅]，由 Structure/Initial.v 的 [initial_unique]：  
 [setsop_special_vs_known]（针对 [Sets_Terminal]，读取为一个 [@Initial (Sets^op)]，因为它通过转换就是 [@Initial (Sets^op)]，由于 [Initial C := @Terminal (C^op)] 和 [C^op^op] 是 [C]），  
 [sets_special_wellpowered_vs_known] 和 [sets_special_book_vs_known]（针对 [Sets_Initial]）。- 一个定理：[sets_special_wellpowered_empty]，推论计算的交集没有元素，从其自身的零箭头读取到 [Sets_Initial] 的对象。这里的每个常数在全局上下文下都是封闭的（打印每个的假设）；[Untruncate] 和 [IEM] 是假设，而不是公理。  

 宇宙（UNIVERSES），通过 [Set Printing Universes. About …] 测量，相对于集成的 Adjunction/SAFT/InitialObject.v，stdlib 的界限省略：setsop_special_initial@{o so u} : @初始集合@{o so}^op
 ( * o < so, so < u * )
 sets_special_initial_untruncate@{o so u} :
 去截断@{o} → @初始集合@{o so}   ( * 集合 < o, o < so, so < u * )
 sets_special_initial_wellpowered@{o so u u0} :
 去截断@{o} → @初始集合@{o so}
 ( * 集合 < o, o < so, so < u, u0 <= o * )
 sets_special_initial_book@{o so u u0 u1 u2} :
 去截断@{o} → @初始集合@{o so}
 ( * 集合 < o, o < so, o < u0, u < u1, u0 < u2, so <= u1, u <= o,
 u <= so * )
 sets_special_initial_IEM@{o so u} :
 IEM@{o} → @初始集合@{o so}   ( * o < so, so < u * )
 sets_special_initial_IEM_at_Set@{so u} :
 IEM@{集合} → @初始集合@{集合 so}   ( * 集合 < so, so < u * )[Set < o] 的 [Untruncate] 证人的共生成器是 [Prop] 作为载体（Instance/Sets/Cogenerator.v），而 [Sets_WellPowered_untruncate] 具有相同的界限。每个绑定器都是显式的，其中一个在测量中是承重的：未注释的 [setsop_L_least] 初稿使用 [reflexivity] 关闭了它的目标，并将载体宇宙固定在 [Set]（关于：[setsop_L_least@{u} : ∀ v : SubObj@{u Set} (cogen_prod@{Set u Set u Set} …)]），并且 [setsop_special_initial] 变成了 [@Initial Sets@{Set u}^op]。单独的任何更改都会移除固定点，两者在整个文件副本中都进行了测量：当文件的每个绑定器都有注释时，[reflexivity] 被接受，无需 [Set]；当每个绑定器被移除时，[exact eq_refl] 取代 [reflexivity] 也是如此。此文件同时进行了这两种操作。两条路径被拒绝，由 Test/ProbeSpecialInitial452.v 锁定，其导入列表包含该文件及该文件本身，每个旁边都有一个阳性对照，并且每个通过在 WHOLE 探针的自身副本中解封被拒绝的命令来读取。在引号中，编译生成的宇宙写为 <1>、<2>……，在每个引号中按首次出现顺序重新编号，就像探针写的那样，因此这些数字具有身份意义，且没有序列号是一个声明：  -  [Sets^op]  通过强有力的推论。当数据保持自由时，[special_initial_object_wellpowered (C := Sets@{o so}^op) WP setsop_comp setsop_cog] 被接受 ([p452_setsop_wp_free])；而当只考虑 [Sets] 在树中的对良有力性时，Instance/Sets/WellPowered.v 的 [Sets_CoWellPoweredAt_up]（一个宇宙层次更高）被拒绝，数据的索引处于比推导所需的同态更高的宇宙中（探针的 N15，[p452_n15_setsop_wp_up]）：
 “术语 'Sets_CoWellPoweredAt_up X' 的类型为 'WellPoweredAt@{<1> <2> <2> o <1>} X'，而预期类型为 'WellPoweredAt@{<3> so <4> o <5>} X'（宇宙不一致：无法强制 <3> = <5> 因为 <3> <= <6> < <5>）。”
 每对象推论 [special_initial_object_wellpowered_at]，在一个对象上被喂入 [Sets_CoWellPoweredAt_up] [cogen_prod setsop_comp setsop_cog]，在宇宙上也被拒绝（N16，[p452_n16_setsop_wp_at_up]；控制 [p452_setsop_wp_at_free]）。所以
 手工制作的 [setsop_L] 是 [Sets^op] 无条件的原因。- [special_initial_object_small] 在 [Sets] ：它的宇宙约束
 对象适合形状宇宙在这里不成立，[Sets@{o so}] 的对象生活在 [so] 之上 [Sets_Complete] 的形状宇宙 [o]。以 [Sets_Complete] 作为 [Complete@{o o o so}] 并且 [Sets_Cogenerator_IEM E] 它被拒绝（N10，[p452_n10_small_at_sets]）：
 “术语 ‘Sets_Complete : Complete’ 的类型是 ‘Complete@{o o o so}’，而预期类型是 ‘Complete@{o o o <1>}’
 （宇宙不一致：无法强制 <1> = so 因为 <1> <= <2> < so）。”
 #452 首次测量的形式将 [Sets_Complete] 的宇宙留给推理，并在相同的论证中被拒绝，每个宇宙都有一个序号。控制，[sets_special_initial_IEM] 在相同的范畴及其与 [Sets_Complete] 相关的主体（[p452_sets_iem]，[p452_sets_iem_direct]）下，被接受。

 非空性。[Sets^op] 和 [Sets] 并不稀薄，这里使用的每个协生成器都是小的，由 [unit] 索引（[cog_index setsop_cog = unit] 被 [eq_refl] 在临时文件中通过 Structure/Generator.v 的 [Generator_of_separator] 接受），且是真正的：
 Instance/Sets/Cogenerator.v 的 [Sets_terminal_not_cogenerates] 显示该条件排除了 [Sets] 处终对象的每个副本族，且 [Sets_two_arrows] 显示 [Sets^op] 对 [setsop_cog] 具有不同的平行箭头以进行区分。该（2b）对象被证明为空，而非假设为空。未交付。在 [Sets] 处没有无条件证人：缺失的部分是一个小型余生器，因为 Instance/Sets/Cogenerator.v 的无条件 [Sets_Cogenerator_large] 是大的，而 [cogen_prod] 在 [Sets_Complete] 拒绝它（该文件的头部）。通过良有界的推论没有 [Sets^op] 证人，并且在 [Sets^op] 的 (2b)/(2c) 中也没有：[Sets] 在该节点上的余良有界性不在树中。零箭头的正规形式未被测量；在 [Sets] 处它们的域为空，因此没有元素可以对其进行评估。没有与Freyd在[Sets]的初始对象进行比较作为这里的常数：未尝试，[initial_unique (sets_special_initial_wellpowered U) Sets_initial_recovered] (Theory/WeaklyInitial/Sets.v) 已在[Sets@{o so}]的临时文件中被接受，并在全局上下文下关闭，Adjunction/SAFT/InitialObject.v 的[special_vs_freyd]和[freyd_of_cogenerator]在[Sets]下的[Untruncate]也是如此。（更正，#452 fess 审计：早先的修订版说[Sets_initial_recovered]固定在[Sets@{Set _}]；[About]读取[@Initial Sets@{u0 u}]与[u0 < u]并且没有[Set]。）定理的薄见证在这里不存在。
*)

(** ** Sets^op *)

Definition setsop_comp@{o so +| o < so +} :
  @Complete@{o o o so} (Sets@{o so}^op) :=
  Complete_op_of_Cocomplete Sets_Cocomplete.

Definition setsop_cog@{c o so +| o < so +} :
  Cogenerator@{c so o} (Sets@{o so}^op) :=
  cog_of_gen Sets_Generator.

Definition setsop_point@{o so +| o < so +} :
  carrier (@cogen_prod (Sets@{o so}^op) setsop_comp setsop_cog).
Proof.
  exact (iprod_proj (cog_obj setsop_cog)
           (cogen_prod_limit setsop_comp setsop_cog) tt ttt).
Defined.

Definition setsop_L@{o so +| o < so +} :
  @SubObj (Sets@{o so}^op)
    (@cogen_prod (Sets@{o so}^op) setsop_comp setsop_cog).
Proof.
  unshelve refine
    (@Build_SubObj (Sets^op) (cogen_prod setsop_comp setsop_cog)
       (@terminal_obj Sets Sets_Terminal)
       (@one Sets Sets_Terminal (cogen_prod setsop_comp setsop_cog)) _).
  constructor; intros z g1 g2 H u.
  destruct u.
  exact (H setsop_point).
Defined.

Definition setsop_L_least@{o so +| o < so +}
  (v : @SubObj (Sets@{o so}^op)
         (@cogen_prod (Sets@{o so}^op) setsop_comp setsop_cog)) :
  sub_le setsop_L v.
Proof.
  exists (@one Sets Sets_Terminal (Subobject.sub_dom v)).
  intros p; exact eq_refl.
Defined.

Definition setsop_special_initial@{o so +| o < so +} :
  @Initial (Sets@{o so}^op) :=
  special_initial_object setsop_comp setsop_cog setsop_L
    (intersection_all_of_least setsop_L setsop_L_least).

Example setsop_special_obj@{o so +| o < so +} :
  @initial_obj (Sets@{o so}^op) setsop_special_initial
    = @terminal_obj Sets@{o so} Sets_Terminal := eq_refl.

Definition setsop_special_vs_known@{o so +| o < so +} :
  @initial_obj (Sets@{o so}^op) setsop_special_initial
    ≅[Sets@{o so}^op] @initial_obj (Sets@{o so}^op) Sets_Terminal :=
  initial_unique setsop_special_initial Sets_Terminal.

Definition setsop_terminal_IsInitialObj@{o so +| o < so +} :
  @IsInitialObj (Sets@{o so}^op) (@terminal_obj Sets@{o so} Sets_Terminal) :=
  special_initial_IsInitialObj setsop_comp setsop_cog setsop_L
    (intersection_all_of_least setsop_L setsop_L_least).

(* * ** Sets, under Untruncate: the least subobject / * ** 集合，在取消截断下：最小子对象 *)

Definition sets_special_initial_untruncate@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) : @Initial Sets@{o so} :=
  special_initial_object Sets_Complete (Sets_Cogenerator_untruncate U)
    (sub_bot (Sets_zero_monic _))
    (intersection_all_of_least _ (sub_bot_least (Sets_zero_monic _))).

Example sets_special_untruncate_obj@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) :
  @initial_obj Sets@{o so} (sets_special_initial_untruncate U)
    = @initial_obj Sets@{o so} Sets_Initial := eq_refl.

(* * ** Sets, under Untruncate: the well-powered corollary / * ** 集合，在未截断下：强幂推论 *)

Definition sets_special_initial_wellpowered@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) : @Initial Sets@{o so} :=
  special_initial_object_wellpowered (Sets_WellPowered_untruncate U)
    Sets_Complete (Sets_Cogenerator_untruncate U).

Example sets_special_wellpowered_obj@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) :
  @initial_obj Sets@{o so} (sets_special_initial_wellpowered U)
    = Subobject.sub_dom
        (complete_intersection Sets_Complete
           (wp_class_family
              (Sets_WellPowered_untruncate U
                 (cogen_prod Sets_Complete (Sets_Cogenerator_untruncate U)))
              (fun _ => True))) := eq_refl.

Definition sets_special_wellpowered_vs_known@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) :
  @initial_obj Sets@{o so} (sets_special_initial_wellpowered U)
    ≅ @initial_obj Sets@{o so} Sets_Initial :=
  initial_unique (sets_special_initial_wellpowered U) Sets_Initial.

Definition sets_special_wellpowered_empty@{o so +| Set < o, o < so +}
  (U : Untruncate@{o})
  (a : carrier
         (@initial_obj Sets@{o so} (sets_special_initial_wellpowered U))) :
  False :=
  match @zero Sets@{o so} (sets_special_initial_wellpowered U)
          (@initial_obj Sets@{o so} Sets_Initial) a with end.

(* * ** Sets, under Untruncate: the book's blanket hypothesis / * ** 集合，在取消截断下：书的总体假设 *)

Definition Sets_HasClassIntersections_untruncate@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) : HasClassIntersections Sets@{o so} :=
  fun X P HP => Sets_wellpowered_intersection U X P HP.

Definition sets_special_initial_book@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) : @Initial Sets@{o so} :=
  special_initial_object_book Sets_Complete (Sets_Cogenerator_untruncate U)
    (Sets_HasClassIntersections_untruncate U).

Example sets_special_book_obj@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) :
  @initial_obj Sets@{o so} (sets_special_initial_book U)
    = Subobject.sub_dom
        (`1 (Sets_wellpowered_intersection U
               (cogen_prod Sets_Complete (Sets_Cogenerator_untruncate U))
               (fun _ => unit) (fun _ _ _ t => t))) := eq_refl.

Definition sets_special_book_vs_known@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) :
  @initial_obj Sets@{o so} (sets_special_initial_book U)
    ≅ @initial_obj Sets@{o so} Sets_Initial :=
  initial_unique (sets_special_initial_book U) Sets_Initial.

(** ** Sets, under IEM / ** 集合，依据 IEM *)

Definition sets_special_initial_IEM@{o so +| o < so +}
  (E : IEM@{o}) : @Initial Sets@{o so} :=
  special_initial_object Sets_Complete (Sets_Cogenerator_IEM E)
    (sub_bot (Sets_zero_monic _))
    (intersection_all_of_least _ (sub_bot_least (Sets_zero_monic _))).

Example sets_special_IEM_obj@{o so +| o < so +} (E : IEM@{o}) :
  @initial_obj Sets@{o so} (sets_special_initial_IEM E)
    = @initial_obj Sets@{o so} Sets_Initial := eq_refl.

Definition sets_special_initial_IEM_at_Set@{so +| Set < so +}
  (E : IEM@{Set}) : @Initial Sets@{Set so} :=
  sets_special_initial_IEM E.
