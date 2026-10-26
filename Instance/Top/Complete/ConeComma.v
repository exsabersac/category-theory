Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Cones.
Require Import Category.Instance.Cones.Limit.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.One.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Complete.

Generalizable All Variables.

(* * * Limits of spaces through categories of cones: §V.9 Exercise 3 / * * 通过圆锥类别的空间限制：§V.9 练习 3 *)

(*
 Mac Lane, “Categories for the Working Mathematician”, 2nd ed. (GTM 5),
 §V.9 Exercise 3, book pp. 135-136 (PDF pp. 144-145), read from the
 page images (catalog id maclane:V.9:ex3):
 “3. (Categorical construction of the usual products in Top.)
 (a) For diagonal functors Δ : C → C^J, Δ' : D → D^J, and T ∈ C^J,
 each G : C → D defines G_* : (Δ↓T) → (Δ'↓GT) by ⟨τ : c → T⟩ ↦
 ⟨Gτ : Gc → GT⟩.  If G_* has a left adjoint and GT a limit in D,
 prove that T has a limit in C.
 (b) For G the forgetful functor Top → Set and J discrete, construct
 a left adjoint for G_*, showing that it constructs on a set S the
 weakest topology making a given J-indexed family of functions
 f_j : S → GX_j continuous.
 (c) Conclude that Top has all (the usual) products.”
 Remark 1 on book p. 133 (PDF p. 142), quoted in
 Instance/Top/Complete.v's header, points here for its “general fact”.
 nLab: https://ncatlab.org/nlab/show/cone
 nLab: https://ncatlab.org/nlab/show/comma+category
 nLab: https://ncatlab.org/nlab/show/initial+topology

 BACKGROUND.  A limit of T is a terminal object of the category of cones
 over it, (Δ↓T) in Mac Lane's notation, which Instance/Cones/Comma.v's
 [Cones_Comma] identifies with Instance/Cones.v's [Cones T] by an
 isomorphism in Cat.  A functor G carries cones over T to cones over GT,
 and the exercise asks when a limit of GT lifts back.  The mechanism is
 that of Mac Lane's subspace construction earlier in the section (the
 functor L there, a RIGHT adjoint of the sliced forgetful functor): the
 weakest topology W on a cone of functions satisfies G_* ⊣ W, since a
 continuous map into the weakest topology is exactly a function whose
 composites with the family are continuous (Instance/Top/Complete.v's
 [pinit_universal]), and a right adjoint carries the terminal cone over
 GT to a terminal cone over T.

 THE PRINTED STATEMENT, CORRECTED.  As printed, (a) and (b) say “left
 adjoint”.  Read literally (a) is false, and this file refutes it at an
 instance: at the empty shape, with C the walking span Instance/Roof.v's
 [Roof] (an initial object RZero, no terminal object) and D the point
 Instance/One.v's [_1], G_* has a left adjoint (it picks RZero), GT has
 a limit, and T, the empty diagram in [Roof], has none
 ([ex3a_left_adjoint_literal_refuted], [ex3a_left_counterexample]).  A
 left adjoint preserves initial objects, not terminal ones.  At the
 forgetful functor G_* in fact has BOTH adjoints: the left one is the
 discrete topology ([pdisc_cone_adjunction]), the right one the weakest
 ([pcone_adjunction]), and they are different constructions: at the
 empty shape on the two-point set the left adjoint makes {true} open and
 the right adjoint does not ([cone_adjoints_differ_at_empty_shape]).  So
 (b)'s “left adjoint ... constructs ... the weakest topology” fits the
 right adjoint, and (a) holds with “right” ([limit_from_cone_right_adjoint]).
 This file delivers the exercise in that corrected form, by the
 maintainer's decision of 2026-09-24, with the literal reading refuted
 beside it.  (b) is proved at EVERY shape, not only a discrete one.

 WHAT IS HERE.
 - [ConeImage G T : Cones T ⟶ Cones (G ◯ T)], Mac Lane's G_* on
 Instance/Cones.v's cone categories, its object action
 Structure/Limit/Preservation.v's [FCone] ([ConeImage_obj]), for ANY
 [G], [T] and shape.
 - (a), corrected: [terminal_of_right_adjoint] (a right adjoint carries
 a terminal object to a terminal object) and
 [limit_from_cone_right_adjoint]: if [ConeImage G T ⊣ W] and [G ◯ T]
 has a limit, so has [T], through Instance/Cones/Limit.v's
 [Cones_Limit] and [Limit_Cones].
 - (b), at every shape [J : Category@{j o o}] and diagram
 [T : J ⟶ PTopCat]: [PInitCone T] gives the apex of a cone over the
 underlying diagram the weakest topology making its legs continuous
 (its object action IS Instance/Top/Complete.v's [pinit_cone],
 [PInitCone_obj]), and [pcone_adjunction : ConeImage PForget T ⊣
 PInitCone T], by Theory/Adjunction.v's [Build_Adjunction'] from a
 hom-set bijection ([pcone_adj_iso]) that is the identity on
 underlying maps.  [PTop_limit_via_cones] is (a) at it, and
 [PTop_Complete_via_cones] the completeness it gives over
 Instance/Sets/Complete.v's [Sets_Limit], whose limiting cone IS
 [PTop_Complete]'s, apex ([PTop_via_cones_apex]) and legs
 ([PTop_via_cones_cone]), at [eq_refl].
 - (c): [PTop_iprod_cone] and [PTop_iprod_via_cones], the product of a
 family through the cone adjunction at the discrete shape
 (Structure/Limit/Comparison.v's [DiscreteCat_Functor'] and
 [discrete_IsIndexedProduct_of_IsLimitCone]), and
 [PTop_products_via_cone_comma], all products of [PTopCat].
 - The left adjoint: [pdisc_cone], [PDiscCone], [PDiscCone_open] (the
 apex's opens are Instance/Top/Prop.v's [pdisc_open], at [eq_refl]),
 [pdisc_cone_adj_iso] and [pdisc_cone_adjunction : PDiscCone T ⊣
 ConeImage PForget T]; [cone_adjoints_differ_at_empty_shape] over
 [pempty_diagram] (the empty discrete shape at [PTopCat]'s levels),
 [pbool_cone] and [puniform_topology].
 - The literal (a) refuted: [Ex3a_left_literal G T], the printed claim
 at one [G] and [T]; [ex3a_left_adjoint_literal_refuted :
 Ex3a_left_literal ex3_G1 ex3_T0 → False]; and
 [ex3a_left_counterexample : Ex3a_left_refuting_data ex3_G1 ex3_T0],
 the three facts (a left adjoint of G_*, a limit of GT, no limit of
 T) bundled in one type so that all three are about the same [G] and
 [T].  The pieces: [ex3_T0], the empty diagram out of
 Instance/Discrete.v's [DiscreteCat False]; [ex3_G1],
 [ex3_roof_cone], [ex3_point_cone], [ex3_roof_from_apex],
 [ex3_LeftAdj], [ex3_left_adj_iso], [ex3_left_adj],
 [ex3_point_terminal], [ex3_point_limit], [ex3_roof_no_limit] and the
 local tactic [ex3_lit_tac].

 STRENGTHS.  At [eq_refl]: [ConeImage_obj], [PInitCone_obj],
 [PDiscCone_open], [PTop_via_cones_apex] and [PTop_via_cones_cone].
 The adjunctions are hom-set bijections that are the identity on
 underlying maps.  Eleven
 proofs end [Defined] (counted by token); seven are load-bearing,
 measured by closing each alone [Qed] in a scratch copy: [ConeImage]
 ([ConeImage_obj] is refused), [terminal_of_right_adjoint]
 ([PTop_via_cones_apex]), [PInitCone] ([PInitCone_obj]), [pdisc_cone]
 ([PDiscCone]), [PDiscCone] ([PDiscCone_open]), [pbool_cone]
 ([cone_adjoints_differ_at_empty_shape]) and [ex3_roof_cone] (the first
 obligation of [ex3_LeftAdj]); [pcone_adjunction],
 [pdisc_cone_adjunction], [ex3_point_cone] and [ex3_left_adj] are
 [Defined] by the data convention only.  The refutations end in
 [False]; [ex3a_left_counterexample] is data.

 UNIVERSES, read by [About] under [Set Printing Universes], stdlib caps
 left out.
 - [ConeImage@{u u0 u1 u2 u3 u4 u5 u6}] over [J : Category@{u0 u1 u1}],
 [C : Category@{u2 u1 u1}] and [D : Category@{u u1 u1}]: the three
 share the hom universe [u1].  Instance/Cones.v's [Cones@{u u0 u1 u2
 u3 u4}] identifies the homs of its shape and target ([J :
 Category@{u1 u4 u4}], [C : Category@{u2 u4 u4}]), and
 Structure/Limit/Preservation.v's [FCone], the object action, carries
 the block equations [u0 = u2] and [u0 = u4] that identify [D]'s
 homs with them; [Cone] itself carries only [<=] bounds.  [u1 < u6]
 is Theory/Functor.v's [Compose] bound ([u3 < u2]) at [G ◯ T].
 - [limit_from_cone_right_adjoint]: a [Limit@{u u6 u5 u7} (G ◯ T)] in,
 a [Limit@{u u6 u5 u8} T] out, the limit universe [u] the same.
 - [pcone_adjunction@{j o so u u0 u1 u2 u3}] and
 [pdisc_cone_adjunction]: the shape's object universe [j] is free;
 [u1 < u0] is Theory/Adjunction.v's [Adjunction]'s own [h1 < so],
 the bound of the [Sets] its hom-set bijections live in, and
 [pcone_adj_iso]'s [u2 < u0] is Instance/Sets.v's [o < so] of that
 [Sets]; [o < u3] is [Compose]'s at [PForget ◯ T].
 - [PTop_Complete_via_cones@{r s o so u u0 u1} : Complete@{r s o so}],
 block [s <= o] and the equation [r = o]: the limit universe passes
 through [limit_from_cone_right_adjoint] unchanged from
 [Sets_Limit]'s, which is the carrier level [o].  (Instance/Top/
 Complete.v's recipe separates the two, and there [r] is free.)
 Measured in the scratch file of Instance/Top/Complete.v's boundary
 paragraph: accepted as [Complete@{o s o so}] at [s < o], refused at
 [r > o] (“Cannot enforce o = r because o < r”) and at [o < s]
 (“Cannot enforce o = <1> because o < s <= <1>”).
 - [PTop_products_via_cone_comma@{i o so u u0 u1} :
 HasIndexedProducts@{i i i o so o} PTopCat@{o so}], [i <= o].
 - The literal counterexample fixes no universe: its empty shape is
 [DiscreteCat False] at levels of its own ([ex3_T0@{u u0 u1 u2} :
 DiscreteCat@{u u0 u0} False ⟶ Roof@{u1 u0}]), and [Roof]'s homs
 are its [u0].  Over the [About] output of all 64 of this file's
 constants (its [Print Module] listing, obligations included; it
 declares no record or inductive), [Set] occurs in 32 blocks, every
 one as [Set < so], the bound [PTopCat] records, and in none of the
 [ex3_*] and [ex3a_*] blocks; no block carries an equation but
 [PTop_Complete_via_cones]'s [r = o].

 ROUTE AND COST.  Closure: 101 [Category.*] modules excluding this file
 ([Print Libraries]); Instance/One.v and Instance/Roof.v, which serve
 only the refutation, cost nothing at the margin (dropped together, the
 rest of the import list still loads 101).

 NOT DELIVERED.  G_* on Mac Lane's comma categories (Δ↓T) themselves:
 it is defined on [Cones], and [Cones_Comma] is not used to transport
 the adjunctions.  No uniqueness statement: that every right adjoint of
 G_* at [PForget] is [PInitCone] up to isomorphism is not proved, and
 [cone_adjoints_differ_at_empty_shape] compares the two adjoints built
 here, not every left adjoint.  [terminal_of_right_adjoint] and
 [limit_from_cone_right_adjoint] are general category theory placed
 beside their only consumer, not in Adjunction/ or Structure/.  The
 literal refutation is at one pair [G], [T], though at every universe
 level of that pair. 

 --------
 麦克莱恩，《为在职数学家准备的范畴论》，第2版（GTM 5），§V.9 习题3，书本第135-136页（PDF第144-145页），从页面图片阅读（目录ID maclane:V.9:ex3）：
 “3.（Top中通常积的范畴构造。）
 (a) 对于对角函子 Δ : C → C^J、Δ' : D → D^J，以及 T ∈ C^J，每个 G : C → D 定义 G_* : (Δ↓T) → (Δ'↓GT)，由 ⟨τ : c → T⟩ ↦ ⟨Gτ : Gc → GT⟩。如果 G_* 有左伴随，且 GT 在 D 中有极限，证明 T 在 C 中有极限。
 (b) 对于 G 为忘记函子 Top → Set 且 J 为离散，构造 G_* 的一个左伴随，说明它在集合 S 上构造了使给定的 J 索引函数族 f_j : S → GX_j 连续的最弱拓扑。
 (c) 得出结论：Top 拥有所有（通常的）积。”
 书本第133页（PDF第...）的注1142)，引用于 Instance/Top/Complete.v 的头部，这里指出其“常规事实”。nLab: https://ncatlab.org/nlab/show/cone 
 nLab: https://ncatlab.org/nlab/show/comma+category 
 nLab: https://ncatlab.org/nlab/show/initial+topology背景。一种极限 T 是其上的锥的范畴（在 Mac Lane 的符号中记作 (Δ↓T)）的一个终对象，而 Instance/Cones/Comma.v 的 [Cones_Comma] 通过 Cat 中的一个同构将其识别为 Instance/Cones.v 的 [Cones T]。一个函子 G 将 T 上的锥映射到 GT 上的锥，本练习要求讨论 GT 的极限何时可以被提升回去。这一机制是本章前面 Mac Lane 的子空间构造（其中的函子 L，是切片遗忘函子的右伴随）：锥上函数的最弱拓扑 W 满足 G_* ⊣ W，因为映入最弱拓扑的连续映射恰好是与该族复合后连续的函数（Instance/Top/Complete.v 的 [pinit_universal]），而右伴随将 GT 上的终锥映射为 T 上的终锥。印刷版声明，已更正。印刷版中，(a) 和 (b) 写着“左伴随”。按字面理解，(a) 是错误的，并且该文件在一个实例上驳斥了它：在空形状上，令 C 为步行跨距 Instance/Roof.v 的 [Roof]（一个初始对象 RZero，没有终端对象），D 为点 Instance/One.v 的 [_1]，G_* 有一个左伴随（它选择 RZero），GT 有极限，而 T，在 [Roof] 中的空图，则没有（[ex3a_left_adjoint_literal_refuted]，[ex3a_left_counterexample]）。左伴随保持初始对象，而不是终端对象。对于忘记函子 G_*，实际上它有两个伴随：左伴随是离散拓扑（[pdisc_cone_adjunction]），右伴随是最弱的（[pcone_adjunction]），并且它们是不同的构造：在两点集上的空形状上，左伴随使 {true} 成为开集，而右伴随则不（[cone_adjoints_differ_at_empty_shape]）。所以 (b) 的“左伴随……构造……最弱拓扑”符合右伴随，而 (a) 在“右”的情况下成立（[limit_from_cone_right_adjoint]）。这个文件以该经维护者在 2026-09-24 决定的更正形式提供该练习，并在旁边反驳了字面理解。(b) 在每种形状下都被证明成立，而不仅仅是离散形状。这里是什么。 - [ConeImage G T : Cones T ⟶ Cones (G ◯ T)]，Mac Lane 的 G_* 在 Instance/Cones.v 的锥范畴，它的对象作用 Structure/Limit/Preservation.v 的 [FCone] ([ConeImage_obj])，对于任何 [G]，[T] 和形状。- (a)，修正：[terminal_of_right_adjoint]（一个右伴随将终对象映射到终对象）和 [limit_from_cone_right_adjoint]：如果 [ConeImage G T ⊣ W] 和 [G ◯ T] 有极限，那么 [T] 也有，通过 Instance/Cones/Limit.v 的 [Cones_Limit] 和 [Limit_Cones]。-（b），在每个形状 [J : Category@{j o o}] 和图 [T : J ⟶ PTopCat]：[PInitCone T] 给出了一个圆锥的顶点，它位于基础图上，使其边连续的最弱拓扑（其对象动作是 Instance/Top/Complete.v 的 [pinit_cone]，[PInitCone_obj]），以及 [pcone_adjunction：ConeImage PForget T ⊣ PInitCone T]，由 Theory/Adjunction.v 的 [Build_Adjunction'] 通过一个在基础映射上为恒等的同态集双射（[pcone_adj_iso]）。[PTop_limit_via_cones] 是（a）在其上的，而 [PTop_Complete_via_cones] 给出了它在 Instance/Sets/Complete.v 的 [Sets_Limit] 上的完备性，其极限圆锥是 [PTop_Complete] 的，顶点（[PTop_via_cones_apex]）和边（[PTop_via_cones_cone]），在 [eq_refl] 上。- (c)：[PTop_iprod_cone] 和 [PTop_iprod_via_cones]，一个通过在离散形状处的圆锥伴随的族的积（Structure/Limit/Comparison.v 的 [DiscreteCat_Functor'] 和 [discrete_IsIndexedProduct_of_IsLimitCone]），以及 [PTop_products_via_cone_comma]，都是 [PTopCat] 的积。- 左伴随：[pdisc_cone]、[PDiscCone]、[PDiscCone_open]（顶点的开集是 Instance/Top/Prop.v 的 [pdisc_open]，在 [eq_refl] 处），[pdisc_cone_adj_iso] 和 [pdisc_cone_adjunction ：PDiscCone T ⊣ ConeImage PForget T]；[cone_adjoints_differ_at_empty_shape] 在 [pempty_diagram] 上（[PTopCat] 层的空离散形状），[pbool_cone] 和 [puniform_topology]。- 字面意思的 (a) 被驳斥：[Ex3a_left_literal G T]，印刷声明在 [G] 和 [T]；[ex3a_left_adjoint_literal_refuted：Ex3a_left_literal ex3_G1 ex3_T0 → False]；以及 [ex3a_left_counterexample : Ex3a_left_refuting_data ex3_G1 ex3_T0]，三个事实（G_* 的左伴随、GT 的极限、T 无极限）被捆绑在一个类型中，以便这三者都关于同一个 [G] 和 [T]。各部分：[ex3_T0]，来自 Instance/Discrete.v 的空图 [DiscreteCat False]；[ex3_G1]、[ex3_roof_cone]、[ex3_point_cone]、[ex3_roof_from_apex]、[ex3_LeftAdj]、[ex3_left_adj_iso]、[ex3_left_adj]、[ex3_point_terminal]、[ex3_point_limit]、[ex3_roof_no_limit] 以及本地策略 [ex3_lit_tac]。优势。在 [eq_refl]：[ConeImage_obj]，[PInitCone_obj]，[PDiscCone_open]，[PTop_via_cones_apex] 和 [PTop_via_cones_cone]。伴随是同态集合双射，在底层映射上是恒等的。十一份证明在 [Defined] 结束（按标记计数）；七份是承重的，通过在草稿副本中单独闭合每份来衡量：[ConeImage]（[ConeImage_obj] 被拒绝）、[terminal_of_right_adjoint]（[PTop_via_cones_apex]）、[PInitCone]（[PInitCone_obj]）、[pdisc_cone]（[PDiscCone]）、[PDiscCone]（[PDiscCone_open]）、[pbool_cone]（[cone_adjoints_differ_at_empty_shape]）和 [ex3_roof_cone]（[ex3_LeftAdj] 的第一个义务）；[pcone_adjunction]、[pdisc_cone_adjunction]、[ex3_point_cone] 和 [ex3_left_adj] 仅根据数据约定为 [Defined]。反驳在 [False] 结束；[ex3a_left_counterexample] 是数据。宇宙，由 [About] 在 [Set Printing Universes] 下读取，stdlib 大写字母省略。- [ConeImage@{u u0 u1 u2 u3 u4 u5 u6}] 在 [J : Category@{u0 u1 u1}] 上，[C : Category@{u2 u1 u1}] 和 [D : Category@{u u1 u1}]：三者共享同一个同态宇宙 [u1]。Instance/Cones.v 的 [Cones@{u u0 u1 u2 u3 u4}] 确定了其形状和目标的同态 ([J : Category@{u1 u4 u4}], [C : Category@{u2 u4 u4}])，而 Structure/Limit/Preservation.v 的 [FCone]，对象动作，包含了方程块 [u0 = u2] 和 [u0 = u4]，这些方程块将 [D] 的同态与它们联系起来；[Cone] 本身只包含 [<=] 限界。[u1 < u6] 是 Theory/Functor.v 的 [Compose] 限界 ([u3 < u2]) 在 [G ◯ T]。- [limit_from_cone_right_adjoint]：一个 [Limit@{u u6 u5 u7} (G ◯ T)] 输入，一个 [Limit@{u u6 u5 u8} T] 输出，极限宇宙 [u] 相同。- [pcone_adjunction@{j o so u u0 u1 u2 u3}] 和 [pdisc_cone_adjunction]：形状的对象宇宙 [j] 是自由的；[u1 < u0] 是 Theory/Adjunction.v 的 [Adjunction] 自身的 [h1 < so]，[Sets] 的同态集双射的界限所在的地方，[pcone_adj_iso] 的 [u2 < u0] 是 Instance/Sets.v 的 [o < so] 在该 [Sets]；[o < u3] 是 [Compose] 在 [PForget ◯ T] 处。- [PTop_Complete_via_cones@{r s o so u u0 u1} : Complete@{r s o so}]，区块 [s <= o] 和方程 [r = o]：极限宇宙通过 [limit_from_cone_right_adjoint] 保持不变，继承自 [Sets_Limit] 的，位于承载层 [o]。(Instance/Top/Complete.v 的配方将二者分开，并且 [r] 是免费的。)  
 在 Instance/Top/Complete.v 的边界段的草稿文件中测量：在 [s < o] 被接受为 [Complete@{o s o so}]，在 [r > o] 被拒绝（“无法强制 o = r 因为 o < r”）以及在 [o < s]（“无法强制 o = <1> 因为 o < s <= <1>”）。- [PTop_products_via_cone_comma@{i o so u u0 u1}：HasIndexedProducts@{i i i o so o} PTopCat@{o so}]，[i <= o]。- 字面反例不修复任何宇宙：其自身层次的空形状为 [DiscreteCat False] ([ex3_T0@{u u0 u1 u2}：DiscreteCat@{u u0 u0} False ⟶ Roof@{u1 u0}])，以及 [Roof] 的同态是其 [u0]。在该文件所有64个常量的 [About] 输出中（包括其 [Print Module] 列表和义务；它未声明任何记录或归纳），[Set] 出现在32个块中，每个块都作为 [Set < so]，边界 [PTopCat] 记录，并且在 [ex3_*] 和 [ex3a_*] 块中均未出现；没有块包含方程，只有 [PTop_Complete_via_cones] 的 [r = o]。

 路由与成本。闭包：101 个 [Category.*] 模块，不包括此文件（[Print Libraries]）；Instance/One.v 和 Instance/Roof.v 仅用于反驳，在边际上不耗费任何成本（一起删除，其余导入列表仍加载101）。未交付。G_* 在 Mac Lane 的逗号范畴 (Δ↓T) 本身上：它定义在 [Cones] 上，而 [Cones_Comma] 并未用于传递伴随。没有唯一性陈述：每个在 [PForget] 上的 G_* 的右伴随都是 [PInitCone]（最多同构）这一点没有被证明，并且 [cone_adjoints_differ_at_empty_shape] 比较这里构建的两个伴随，而不是每个左伴随。[terminal_of_right_adjoint] 和 [limit_from_cone_right_adjoint] 是放在它们唯一使用者旁边的一般范畴理论，而不在 Adjunction/ 或 Structure/ 中。字面上的反驳出现在一对 [G]、[T] 上，虽然在该对的每个宇宙层级上都成立。
*)

#[local] Obligation Tactic := idtac.

(* * ** G_* : the functor a functor induces on categories of cones / * **G_*** ：函子在锥体范畴上诱导的函子 *)

Section ConeImage.

Context {J C D : Category} (G : C ⟶ D) (T : J ⟶ C).

(*
 Mac Lane's G_* : (Δ ↓ T) → (Δ' ↓ GT), ⟨τ : c → T⟩ ↦ ⟨Gτ : Gc → GT⟩, on
 Instance/Cones.v's [Cones]; its object action is Structure/Limit/
 Preservation.v's [FCone]. 

 --------
 Mac Lane 的 G_* : (Δ ↓ T) → (Δ' ↓ GT), ⟨τ : c → T⟩ 映射为 ⟨Gτ : Gc → GT⟩，在 Instance/Cones.v 的 [Cones] 上；其对象作用在 Structure/Limit/Preservation.v 的 [FCone] 上。
*)
Definition ConeImage : Cones T ⟶ Cones (G ◯ T).
Proof.
  unshelve refine (@Build_Functor (Cones T) (Cones (G ◯ T))
    (fun N => FCone G N) (fun N M u => (fmap[G] (`1 u); _)) _ _ _).
  - intro j. simpl. unfold fcone_leg. simpl.
    rewrite <- fmap_comp. apply fmap_respects. exact (`2 u j).
  - intros N M u v H; simpl in *. now rewrite H.
  - intros N; simpl. apply fmap_id.
  - intros N M P u v; simpl. apply fmap_comp.
Defined.

Example ConeImage_obj (N : Cone T) : fobj[ConeImage] N = FCone G N := eq_refl.

End ConeImage.

(* * ** Exercise 3(a), in the form that holds: G_* with a RIGHT adjoint / * ** 练习 3(a)，形式如下：G_* 具有右伴随 *)

(* A right adjoint carries a terminal object to a terminal object. / 右伴随函子将终对象映射到终对象。 *)
Definition terminal_of_right_adjoint {C D : Category} {F : D ⟶ C}
  {U : C ⟶ D} (A : F ⊣ U) (t : @Terminal C) : @Terminal D.
Proof.
  unshelve refine {| terminal_obj := U (@terminal_obj _ t) |}.
  - intro x. exact (to (@adj _ _ _ _ A x _) (@one _ t (F x))).
  - intros x f g.
    transitivity (to (@adj _ _ _ _ A x _) (from (@adj _ _ _ _ A x _) f)).
    + symmetry. exact (iso_to_from (@adj _ _ _ _ A x _) f).
    + transitivity (to (@adj _ _ _ _ A x _) (from (@adj _ _ _ _ A x _) g)).
      * apply proper_morphism. apply one_unique.
      * exact (iso_to_from (@adj _ _ _ _ A x _) g).
Defined.

(*
 If G_* has a right adjoint and GT has a limit, T has a limit: the right
 adjoint carries the terminal cone over GT to a terminal cone over T. 

 --------
 如果 G_* 有一个右伴随且 GT 有极限，那么 T 也有极限：右伴随将 GT 上的终锥映射为 T 上的终锥。
*)
Definition limit_from_cone_right_adjoint {J C D : Category}
  (G : C ⟶ D) (T : J ⟶ C) (W : Cones (G ◯ T) ⟶ Cones T)
  (A : ConeImage G T ⊣ W) (L : Limit (G ◯ T)) : Limit T :=
  @Limit_Cones _ _ T (terminal_of_right_adjoint A (Cones_Limit (G ◯ T) L)).

(* * ** Exercise 3(b), at every shape: the weakest topology on a Sets-cone / * ** 练习 3(b)，在每个形状上：集合锥上的最弱拓扑 *)

Section InitialCone.

Universes j o so.
Constraint o < so.

Context {J : Category@{j o o}} (T : J ⟶ PTopCat@{o so}).

Local Notation G := PForget@{o so}.

(*
 The right adjoint: a cone over the underlying diagram goes to the same
 cone with its apex given the initial topology for its legs,
 Instance/Top/Complete.v's [pinit_cone]. 

 --------
 右伴随：在底层图上的一个圆锥映射到同一个圆锥，其顶点给定其边的初始拓扑，Instance/Top/Complete.v 的 [pinit_cone]。
*)
Definition PInitCone : Cones (G ◯ T) ⟶ Cones T.
Proof.
  unshelve refine (@Build_Functor (Cones (G ◯ T)) (Cones T)
    (fun N => pinit_cone T N)
    (fun N M u => (@Build_PMor (pinit_top T N) (pinit_top T M) (`1 u) _; _))
    _ _ _).
  - apply (proj2 (pinit_universal _ _ _ _ (pinit_top T N) (`1 u))).
    intro k.
    apply (@pcont_respects (pinit_top T N) (fobj[T] k) (cone_leg N k)).
    + intro s. symmetry. exact (`2 u k s).
    + exact (pinit_leg_cont _ _ _ _ k).
  - intros k s; simpl. exact (`2 u k s).
  - intros N M u v H s; simpl in *. exact (H s).
  - intros N s; simpl. reflexivity.
  - intros N M P u v s; simpl. reflexivity.
Defined.

Example PInitCone_obj (N : Cone (G ◯ T)) : fobj[PInitCone] N = pinit_cone T N :=
  eq_refl.

Program Definition pcone_adj_iso (x : Cones T) (y : Cones (G ◯ T)) :
  @Isomorphism Sets
    {| carrier := @hom (Cones (G ◯ T)) (ConeImage G T x) y
     ; is_setoid := @homset (Cones (G ◯ T)) (ConeImage G T x) y |}
    {| carrier := @hom (Cones T) x (PInitCone y)
     ; is_setoid := @homset (Cones T) x (PInitCone y) |} := {|
  to   := {| morphism := fun k =>
               (@Build_PMor (vertex_obj[x]) (pinit_top T y) (`1 k) _; _) |};
  from := {| morphism := fun k => (pmap (`1 k); _) |}
|}.
Next Obligation.
  intros x y [k Hk]; simpl in *.
  apply (proj2 (pinit_universal _ _ _ _ (vertex_obj[x]) k)).
  intro j.
  apply (pcont_respects (pmap (cone_leg x j))).
  - intro s. symmetry. exact (Hk j s).
  - exact (pcont (cone_leg x j)).
Qed.
Next Obligation. intros x y [k Hk] j s; simpl in *. exact (Hk j s). Qed.
Next Obligation. intros x y k k' H s; simpl in *. exact (H s). Qed.
Next Obligation. intros x y [k Hk] j s; simpl in *. exact (Hk j s). Qed.
Next Obligation. intros x y k k' H s; simpl in *. exact (H s). Qed.
Next Obligation. intros x y k s; simpl. reflexivity. Qed.
Next Obligation. intros x y k s; simpl. reflexivity. Qed.

Definition pcone_adjunction : ConeImage G T ⊣ PInitCone.
Proof.
  unshelve eapply (@Build_Adjunction' _ _ (ConeImage G T) PInitCone
                     pcone_adj_iso).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

(*
 Exercise 3(c)'s engine, at every shape: a limit of the underlying
 diagram, carried across the adjunction. 

 --------
 习题 3(c) 的引擎，在每一个形状下：基础图的极限，通过伴随传递。
*)
Definition PTop_limit_via_cones (L : Limit (G ◯ T)) : Limit T :=
  limit_from_cone_right_adjoint G T PInitCone pcone_adjunction L.

End InitialCone.

Definition PTop_Complete_via_cones@{r s o so +| s <= o, o < so, o <= r +} :
  @Complete@{r s o so} PTopCat@{o so} :=
  fun J T => PTop_limit_via_cones T (Sets_Limit (PForget ◯ T)).

(*
 The two routes of Instance/Top/Complete.v's recipe and of the cone
 adjunction build the same space. 

 --------
 Instance/Top/Complete.v 的配方路线和锥对偶的路线构建了相同的空间。
*)
Example PTop_via_cones_apex@{s o so +| s <= o, o < so +}
  (J : Category@{s o o}) (T : J ⟶ PTopCat@{o so}) :
  vertex_obj[@limit_cone _ _ _ (@PTop_Complete_via_cones J T)]
    = vertex_obj[@limit_cone _ _ _ (@PTop_Complete J T)] := eq_refl.

(* Not only the apex: the whole limiting cone, legs included. / 不仅是顶点：整个限制锥，包括其腿部。 *)
Example PTop_via_cones_cone@{s o so +| s <= o, o < so +}
  (J : Category@{s o o}) (T : J ⟶ PTopCat@{o so}) :
  @limit_cone _ _ _ (@PTop_Complete_via_cones@{o s o so _ _ _} J T)
    = @limit_cone _ _ _ (@PTop_Complete@{o s o so _ _} J T) := eq_refl.

(*
 Exercise 3(c): Top has all products, J discrete.  The limit of the
 discrete diagram on [X], through the cone adjunction. 

 --------
 练习 3(c)：Top 有所有积，J 离散。离散图在 [X] 上的极限，通过圆锥伴随。
*)
Definition PTop_iprod_cone@{i o so +| i <= o, o < so +}
  (A : Type@{i}) (X : A → PTop@{o}) :
  Limit (@DiscreteCat_Functor' A PTopCat@{o so} X) :=
  PTop_limit_via_cones (@DiscreteCat_Functor' A PTopCat@{o so} X)
    (Sets_Limit (PForget ◯ @DiscreteCat_Functor' A PTopCat@{o so} X)).

Definition PTop_iprod_via_cones@{i o so +| i <= o, o < so +}
  (A : Type@{i}) (X : A → PTop@{o}) :
  @IsIndexedProduct PTopCat@{o so} A X
    (vertex_obj[@limit_cone _ _ _ (PTop_iprod_cone A X)])
    (cone_leg (@limit_cone _ _ _ (PTop_iprod_cone A X))) :=
  discrete_IsIndexedProduct_of_IsLimitCone
    (@DiscreteCat_Functor' A PTopCat@{o so} X) _
    (limit_limitcone (PTop_iprod_cone A X)).

Definition PTop_products_via_cone_comma@{i o so +| i <= o, o < so +} :
  @HasIndexedProducts@{i i i o so o} PTopCat@{o so} :=
  @Build_HasIndexedProducts PTopCat@{o so}
    (fun A X => vertex_obj[@limit_cone _ _ _ (PTop_iprod_cone A X)])
    (fun A X => cone_leg (@limit_cone _ _ _ (PTop_iprod_cone A X)))
    (@PTop_iprod_via_cones).

(* * ** The LEFT adjoint of G_* at [PForget]: the discrete topology / * ** G_* 在 [PForget] 处的左伴随：离散拓扑 *)

Section DiscreteCone.

Universes j o so.
Constraint o < so.

Context {J : Category@{j o o}} (T : J ⟶ PTopCat@{o so}).

Local Notation G := PForget@{o so}.

(* A cone over the underlying diagram, its apex given the discrete topology: every leg is continuous out of a discrete space. / 在底层图上的一个圆锥，其顶点赋予离散拓扑：从离散空间出发的每条腿都是连续的。 *)
Definition pdisc_cone (N : Cone (G ◯ T)) : Cone T.
Proof.
  unshelve refine (@Build_Cone J PTopCat@{o so} T (PDiscrete (vertex_obj[N]))
    (@Build_ACone J PTopCat@{o so} (PDiscrete (vertex_obj[N])) T
       (fun k => pdisc_mor (vertex_obj[N]) (fobj[T] k) (cone_leg N k)) _)).
  intros x y f s; simpl.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f s).
Defined.

Definition PDiscCone : Cones (G ◯ T) ⟶ Cones T.
Proof.
  unshelve refine (@Build_Functor (Cones (G ◯ T)) (Cones T)
    (fun N => pdisc_cone N)
    (fun N M u => (pdisc_mor (vertex_obj[N]) (PDiscrete (vertex_obj[M])) (`1 u); _))
    _ _ _).
  - intros k s; simpl. exact (`2 u k s).
  - intros N M u v H s; simpl in *. exact (H s).
  - intros N s; simpl. reflexivity.
  - intros N M P u v s; simpl. reflexivity.
Defined.

Example PDiscCone_open (N : Cone (G ◯ T)) (V : vertex_obj[N] → Prop) :
  POpen (vertex_obj[fobj[PDiscCone] N]) V = pdisc_open (vertex_obj[N]) V :=
  eq_refl.

Program Definition pdisc_cone_adj_iso (x : Cones (G ◯ T)) (y : Cones T) :
  @Isomorphism Sets
    {| carrier := @hom (Cones T) (PDiscCone x) y
     ; is_setoid := @homset (Cones T) (PDiscCone x) y |}
    {| carrier := @hom (Cones (G ◯ T)) x (ConeImage G T y)
     ; is_setoid := @homset (Cones (G ◯ T)) x (ConeImage G T y) |} := {|
  to   := {| morphism := fun k => (pmap (`1 k); _) |};
  from := {| morphism := fun k =>
               (pdisc_mor (vertex_obj[x]) (vertex_obj[y]) (`1 k); _) |}
|}.
Next Obligation. intros x y [k Hk] j s; simpl in *. exact (Hk j s). Qed.
Next Obligation. intros x y k k' H s; simpl in *. exact (H s). Qed.
Next Obligation. intros x y [k Hk] j s; simpl in *. exact (Hk j s). Qed.
Next Obligation. intros x y k k' H s; simpl in *. exact (H s). Qed.
Next Obligation. intros x y k s; simpl. reflexivity. Qed.
Next Obligation. intros x y k s; simpl. reflexivity. Qed.

Definition pdisc_cone_adjunction : PDiscCone ⊣ ConeImage G T.
Proof.
  unshelve eapply (@Build_Adjunction' _ _ PDiscCone (ConeImage G T)
                     pdisc_cone_adj_iso).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

End DiscreteCone.

(*
 At the empty shape the two adjoints of G_* part company: on the
 two-point set, the left adjoint makes [{true}] open and the right
 adjoint, the weakest topology for the empty family of maps, does not. 

 --------
 在空形上，G_* 的两个伴随分道扬镳：在两点集上，左伴随使 [{true}] 成为开集，而右伴随，即对于空映射族的最弱拓扑，则不使其成为开集。
*)
Section EmptyShape.

Universes o so.
Constraint o < so.

(*
 The empty shape at the category's own levels: Instance/Zero.v's [_0]
 is unannotated and sits at homs [Set]. 

 --------
 该类别自身层级的空形状：Instance/Zero.v 的 [_0] 未注释，并且位于 homs [Set]。
*)
Definition pempty_diagram : DiscreteCat@{o o o} False ⟶ PTopCat@{o so} :=
  @DiscreteCat_Functor' False PTopCat@{o so} (fun x : False => match x with end).

Definition pbool_cone : Cone (PForget@{o so} ◯ pempty_diagram).
Proof.
  unshelve refine (@Build_Cone _ Sets@{o so} (PForget ◯ pempty_diagram)
    bool_setoid_object@{o o} (@Build_ACone _ Sets@{o so}
       bool_setoid_object@{o o} (PForget ◯ pempty_diagram) _ _)).
  - intro x; destruct x.
  - intro x; destruct x.
Defined.

Lemma puniform_topology (S : SetoidObject@{o o}) :
  PIsTopology S (fun W => ∀ x y : S, W x → W y).
Proof.
  split; [|split; [|split]].
  - intros U V H HU x y v. apply (proj1 (H y)), (HU x y), (proj2 (H x)), v.
  - intros F HF x y [U [FU u]]. exists U. split; [exact FU|].
    exact (HF U FU x y u).
  - intros x y w; exact w.
  - intros U V HU HV x y [u v]. exact (conj (HU x y u) (HV x y v)).
Qed.

Theorem cone_adjoints_differ_at_empty_shape :
  POpen (vertex_obj[fobj[PDiscCone pempty_diagram] pbool_cone])
        (fun b : bool => b = true) /\
  (POpen (vertex_obj[fobj[PInitCone pempty_diagram] pbool_cone])
         (fun b : bool => b = true) → False).
Proof.
  split.
  - intros x y e H. simpl in e. rewrite <- e. exact H.
  - intro H.
    assert (U : ∀ x y : bool, x = true → y = true).
    { apply (H _ (puniform_topology bool_setoid_object@{o o})).
      intros W [k _]. destruct k. }
    discriminate (U true false eq_refl).
Qed.

End EmptyShape.

(* * ** The book's Exercise 3(a) as printed, refuted / * ** 该书印刷版的练习3(a)已被驳斥 *)

(*
 “If G_* has a LEFT adjoint and GT has a limit in D, prove that T has a
 limit in C.”  Counterexample: the empty shape, C the walking span
 (an initial apex, no terminal object), D the point. 

 --------
 如果 G_* 有一个左伴随且 GT 在 D 中有极限，证明 T 在 C 中也有极限。反例：空形状，C 为行走的跨度（初始顶点，没有终端对象），D 为一点。
*)

Local Ltac ex3_lit_tac :=
  intros; simpl in *; repeat intro; simpl in *;
  repeat match goal with
         | [ H : False |- _ ] => destruct H
         | [ H : poly_unit |- _ ] => destruct H
         end;
  try exact I; try reflexivity;
  try (match goal with
       | [ |- @eq poly_unit ?a ?b ] => destruct a; destruct b; reflexivity
       end).

(* The empty shape, [DiscreteCat False], at the universes of its use: no level of it is fixed. / 空的形状，[DiscreteCat False]，在其使用的宇宙中：没有任何层级是固定的。 *)
Definition ex3_T0 : DiscreteCat False ⟶ Roof :=
  @DiscreteCat_Functor' False Roof (fun x : False => match x with end).
Definition ex3_G1 : Roof ⟶ _1 := Erase Roof.

Definition ex3_roof_cone (c : Roof) : Cone ex3_T0.
Proof.
  unshelve econstructor; [exact c|].
  unshelve econstructor; intros x; destruct x.
Defined.

Definition ex3_point_cone : Cone (ex3_G1 ◯ ex3_T0).
Proof.
  unshelve econstructor; [exact ttt|].
  unshelve econstructor; intros x; destruct x.
Defined.

Definition ex3_roof_from_apex (c : RoofObj) : RoofHom RZero c :=
  match c with RNeg => ZeroNeg | RZero => IdZero | RPos => ZeroPos end.

Program Definition ex3_LeftAdj : Cones (ex3_G1 ◯ ex3_T0) ⟶ Cones ex3_T0 := {|
  fobj := fun _ => ex3_roof_cone RZero;
  fmap := fun _ _ _ => (IdZero; _)
|}.
Next Obligation. ex3_lit_tac. Qed.
Next Obligation. ex3_lit_tac. Qed.
Next Obligation. ex3_lit_tac. Qed.
Next Obligation. ex3_lit_tac. Qed.

Program Definition ex3_left_adj_iso (x : Cones (ex3_G1 ◯ ex3_T0))
  (y : Cones ex3_T0) :
  @Isomorphism Sets
    {| carrier := @hom (Cones ex3_T0) (ex3_LeftAdj x) y
     ; is_setoid := @homset (Cones ex3_T0) (ex3_LeftAdj x) y |}
    {| carrier := @hom (Cones (ex3_G1 ◯ ex3_T0)) x (ConeImage ex3_G1 ex3_T0 y)
     ; is_setoid := @homset (Cones (ex3_G1 ◯ ex3_T0)) x
                      (ConeImage ex3_G1 ex3_T0 y) |} := {|
  to   := {| morphism := fun _ => (ttt; _) |};
  from := {| morphism := fun _ => (ex3_roof_from_apex (vertex_obj[y]); _) |}
|}.
Next Obligation. ex3_lit_tac. Qed.
Next Obligation. ex3_lit_tac. Qed.
Next Obligation. ex3_lit_tac. Qed.
Next Obligation. ex3_lit_tac. Qed.
Next Obligation. ex3_lit_tac. Qed.
Next Obligation. ex3_lit_tac. Qed.

Definition ex3_left_adj : ex3_LeftAdj ⊣ ConeImage ex3_G1 ex3_T0.
Proof.
  unshelve eapply (@Build_Adjunction' _ _ ex3_LeftAdj (ConeImage ex3_G1 ex3_T0)
                     ex3_left_adj_iso).
  - ex3_lit_tac.
  - ex3_lit_tac.
Defined.

Program Definition ex3_point_terminal : @Terminal (Cones (ex3_G1 ◯ ex3_T0)) := {|
  terminal_obj := ex3_point_cone;
  one := fun N => (ttt; _)
|}.
Next Obligation. ex3_lit_tac. Qed.
Next Obligation. ex3_lit_tac. Qed.

Definition ex3_point_limit : Limit (ex3_G1 ◯ ex3_T0) :=
  @Limit_Cones _ _ (ex3_G1 ◯ ex3_T0) ex3_point_terminal.

Theorem ex3_roof_no_limit (L : Limit ex3_T0) : False.
Proof.
  generalize (unique_obj (@ump_limits _ _ _ L (ex3_roof_cone RNeg)))
             (unique_obj (@ump_limits _ _ _ L (ex3_roof_cone RPos))).
  simpl. intros a b.
  revert a b. generalize (@vertex_obj _ _ _ (@limit_cone _ _ _ L)).
  intros v a b. destruct v; inversion a; inversion b.
Qed.

(* The book's claim (a) at one pair [G], [T], with “left”, and the three facts that refute it there, each stated about the same [G] and [T]. / 该书的论点 (a) 在一对 [G]、[T] 上，带有“左”，以及三条在同一 [G] 和 [T] 上反驳它的事实。 *)
Definition Ex3a_left_literal {J C D : Category} (G : C ⟶ D) (T : J ⟶ C) :
  Type := ∀ F : Cones (G ◯ T) ⟶ Cones T,
            F ⊣ ConeImage G T → Limit (G ◯ T) → Limit T.

Definition Ex3a_left_refuting_data {J C D : Category} (G : C ⟶ D)
  (T : J ⟶ C) : Type :=
  { F : Cones (G ◯ T) ⟶ Cones T & F ⊣ ConeImage G T } *
  Limit (G ◯ T) * (Limit T → False).

Definition ex3a_left_counterexample :
  Ex3a_left_refuting_data ex3_G1 ex3_T0 :=
  ((ex3_LeftAdj; ex3_left_adj), ex3_point_limit, ex3_roof_no_limit).

Theorem ex3a_left_adjoint_literal_refuted :
  Ex3a_left_literal ex3_G1 ex3_T0 → False.
Proof.
  intro H.
  exact (ex3_roof_no_limit (H ex3_LeftAdj ex3_left_adj ex3_point_limit)).
Qed.
