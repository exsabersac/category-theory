Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Functor.Structure.Cartesian.
Require Import Category.Adjunction.Continuity.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Instance.Ab.Free.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(* * * The free abelian group functor is not continuous / * * 自由阿贝尔群函子不是连续的 *)

(*
 Mac Lane §V.4 Exercise 3 (book p. 118; maclane:V.4:ex3): the free
 abelian group functor Sets ⟶ Ab does not preserve limits — a left
 adjoint need not be continuous.
 nLab: https://ncatlab.org/nlab/show/continuous+functor
 Wikipedia: https://en.wikipedia.org/wiki/Free_abelian_group

 BACKGROUND.  The free abelian group functor is a left adjoint
 (Instance/Ab/Free.v's [free_ab_adjunction : FreeAb ⊣ Ab_Forget], #400),
 so it preserves colimits; Mac Lane's exercise asks for a limit it does
 not preserve, and hints at a countable product.  This file exhibits the
 discontinuity at three shapes — the empty shape, a countable product in
 Mac Lane's shape, and the binary product through the canonical
 comparison map — and packages it as the tree's first refutation of
 [ContinuousFunctor] and of [PreservesAllLimits] at a named functor.

 ONE FACT, STATED ONCE.  The free abelian group on a point has two
 distinct endomorphisms, the identity and the zero map, because its
 generator is not zero (Instance/Ab/Free.v's [free_ab_gen_not_zero], read
 at ℤ); so it is not the zero group ([free_ab_one_id_not_zero]).  Every
 refutation below is this fact plus bookkeeping: over the empty shape it
 is immediately non-terminality; over a DISCONNECTED shape
 whose diagram is constant at the point, the limit in Sets is the point
 again and every image leg is [≈ id], so the mediator would have to equal
 every leg of a competing cone at once, and a cone with legs [id] and the
 zero map has none; over the binary shape the same fact appears as
 [exl ≈ exr] after cancelling the comparison map, refuted by
 [exl ∘ (id △ 0) ≈ id] against [exr ∘ (id △ 0) ≈ 0].

 STALE PREMISES, RE-MEASURED.
 - "Neither the functor nor its target exists": FALSE.  Instance/Ab.v
 declares [Ab] and [Ab_Forget]; Instance/Ab/Free.v declares
 [FreeAb : Sets ⟶ Ab], [free_ab_adjunction] and
 [free_ab_universal] — the term
 algebra [FATerm] under the congruence [fa_eq], not finitely supported
 ℤ-valued functions.  Work bullet 1 (construct the functor with its
 universal property) was done by #400; nothing about the free abelian
 group is re-derived here.
 - The QA correction "consume #540's Construction/FreeAb.v … bridging
 to Instance/Ab.v's carrier": that file does not exist in the tree;
 the donor is Instance/Ab/Free.v, already over #256's [Ab], and no
 bridge is needed.
 - "no in-tree counterexample to continuity of any functor is
 recorded": PARTIAL.  Structure/Limit/Preservation/Separation.v's
 [sep_not_PreservesLimitCone] refutes cone-level preservation for a
 synthetic span functor, so "the library's first recorded
 discontinuity witness" is NOT claimed.  What is first, measured by a
 tree-wide search for the class names beside [False]: the first
 [ContinuousFunctor _ → False], the first [PreservesAllLimits _ →
 False], and the first refutation of [PreservesLimitCone] /
 [PreservesLimit] at a named mathematical functor.  Non-preservation
 at a named functor as such is NOT first (an earlier revision claimed
 it): Instance/Top/Forgetful.v's [indiscrete_image_not_colimiting]
 refutes a colimit cocone for [Top_Indiscrete], and
 Instance/Powerset.v's [direct_image_not_meet_preserving] refutes
 preservation of the binary product ([Subsets_Cartesian]) by the
 left adjoint [DirectImage] — neither phrased with a class name.
 - [Ab] has binary products, coproducts and biproducts
 (Instance/Ab/Coproduct.v), a zero and a terminal object
 (Instance/Ab.v), NO indexed coproducts
 (Instance/Ab/Coproduct.v and Instance/Rng/Free.v record the
 absence of [HasIndexedCoproducts Ab]), and NO indexed products or
 completeness either — measured: the tree's [HasIndexedProducts]
 instances are Sets' (Instance/Sets/Products.v), Cat's and
 StrictCat's (Instance/Cat/Limit.v), none at [Ab], and no
 [Complete Ab] exists (an earlier revision cited the two coproduct
 lines for the product half).  The countable witness below needs
 none: the competing cone
 is supplied directly, which is why that statement is cone-level.

 WHAT IS DELIVERED (33 named constants plus 1 [Program] obligation, every
 one closed under the global context).
 (1) THE INGREDIENTS.  [SetsPoint] (the terminal object of Sets),
 [ab_zero_endo A : A ~> A] (the constant-zero homomorphism, built
 directly — see UNIVERSES for why not as [Ab_zero_hom A ∘ Ab_one A]),
 [ab_zero_endo_value] ([eq_refl] in the probe), and the separation
 [free_ab_one_id_not_zero : id ≈ ab_zero_endo (FreeAb SetsPoint) →
 False].
 (2) WITNESS 1, THE EMPTY LIMIT — the free group on a point is not
 terminal in Ab.  [empty_cone_at] (a cone over the empty diagram at
 any apex; the file's only [Program] obligation), [SetsEmptyDiagram
 := From_0 Sets], [SetsPoint_empty_IsLimitCone] and
 [SetsPoint_empty_Limit] (the point is the empty limit in Sets),
 [FreeAb_not_PreservesLimitCone_empty], and — the APEX-ONLY form,
 which the product witnesses do not reach here (probe N5 pins the
 binary case; the countable apex case is unpinned, see NOT
 DELIVERED) —
 [FreeAb_not_PreservesLimit_empty : PreservesLimit SetsEmptyDiagram
 FreeAb → False] with [FreeAb_not_PreservesAllLimits].
 (3) WITNESS 2, A COUNTABLE PRODUCT IN MAC LANE'S SHAPE.  [NatOnes]
 (the constant family at the point), [NatOneDiagram : DiscreteCat
 nat ⟶ Sets]
 (Structure/Limit/Comparison.v's annotated [DiscreteCat_Functor']),
 [NatOneProduct] (the point is its own countable power in Sets),
 [NatOneCone] / [NatOneCone_IsLimitCone] (through
 [discrete_IsLimitCone_of_IsIndexedProduct]), the competing cone
 [NatCompeting] with legs [nat_legs] ([id] at 0, the zero map
 above), [fmap_one_point], and
 [FreeAb_not_PreservesLimitCone_countable_product].  The MECHANISM
 is not Mac Lane's: his argument is that the comparison
 FreeAb(∏ Xₙ) → ∏ FreeAb(Xₙ) is not surjective because every
 element on the left has finite support, which needs a normal form
 or coefficient uniqueness for [FATerm] that the tree does not have
 (the Instance/Ab/Free.v INDEX bullet says so in terms); here the
 factors are the point, the product collapses to the point, and the
 legs coincide.  The SHAPE is his; the proof is not, and the
 countability is inert: the same argument runs at any discrete
 shape with two or more objects.
 (4) WITNESS 3, THE BINARY PRODUCT THROUGH THE COMPARISON MAP (the
 issue's second work bullet).  [BinOnes], [BinDiagram],
 [FreeAb_binary_cmp := binary_comparison FreeAb BinOnes] (the
 canonical FreeAb(1 × 1) → FreeAb 1 × FreeAb 1),
 [FreeAb_binary_comparison_not_iso],
 [FreeAb_not_PreservesLimitCone_binary_product] (through
 [comparison_iso_of_PreservesLimitCone]) and
 [FreeAb_not_CartesianFunctor] (through Structure/Limit/
 Comparison.v's [cartesian_functor_iff_comparison_iso]).
 (5) THE CONCLUSION.  [FreeAb_not_continuous : ContinuousFunctor FreeAb →
 False] — the issue's pinned statement, through witness 2 — and
 [FreeAb_not_continuous_via_empty] through witness 1; see UNIVERSES
 for why the countable route is the headline.
 (6) THE POSITIVE SIDE OF THE SAME ADJUNCTION.  [Ab_Forget_Continuous]
 (RAPL: Adjunction/Continuity.v's [right_adjoint_Continuous]) and
 [FreeAb_Cocontinuous] (LAPC: [left_adjoint_Cocontinuous]), one line
 each: continuity is exactly what the left adjoint lacks.
 (7) READBACKS.  [freeab_is_left_adjoint := free_ab_adjunction],
 [free_ab_one_carrier] (the carrier of the free group on a point IS
 [FATerm SetsPoint], [eq_refl]), [bin_diagram_objects] ([eq_refl]).

 UNIVERSES (measured by [About] under [Set Printing Universes] on all 33
 constants).  No block carries an equation.  [Set] appears in exactly 12
 of the 33, from two donors, both attributed by [About] on the donor:
 - [_0@{u …} : Category@{u Set Set}] (Instance/Zero.v, declared
 bare, its hom at [Set]) pins the eight empty-shape constants:
 [empty_cone_at], [SetsEmptyDiagram], [SetsPoint_empty_IsLimitCone],
 [SetsPoint_empty_Limit], [FreeAb_not_PreservesLimitCone_empty],
 [FreeAb_not_PreservesLimit_empty], [FreeAb_not_PreservesAllLimits]
 and [FreeAb_not_continuous_via_empty] — [PreservesLimitCone]
 identifies the shape's hom with the ambient's, so through the empty
 shape the functor's hom level itself is [Set]:
 [FreeAb_not_continuous_via_empty] is stated for [FreeAb@{u10 Set …}],
 i.e. [Sets@{Set u} ⟶ Ab@{u Set}] only.  THAT is why the headline
 [FreeAb_not_continuous] goes through the countable product, whose
 shape [DiscreteCat nat] has free levels: it and
 [FreeAb_not_PreservesLimitCone_countable_product] carry no [Set] at
 all.  The apex-level refutation exists only at the empty shape, so
 [FreeAb_not_PreservesAllLimits] is stated at [Ab@{u Set}] and cannot
 be otherwise here.
 - [Ab_trivial@{} : AbObject@{Set Set Set}] (Instance/Ab.v,
 MONOMORPHIC) pins everything assembled from the trivial group —
 [Ab_one], [Ab_zero_hom], [Ab_Terminal], [Ab_Zero], [Ab_Cartesian]
 ([Set < u], [Ab@{u Set}]) — and through [Ab_Cartesian] the four
 binary-witness constants [FreeAb_binary_cmp],
 [FreeAb_binary_comparison_not_iso],
 [FreeAb_not_PreservesLimitCone_binary_product],
 [FreeAb_not_CartesianFunctor] (probe N6-N8: [Ab_trivial],
 [Ab_Terminal], [Ab_Cartesian] refused at a hom level strictly above
 [Set], [Ab] and [Ab_Forget] accepted there).  [ab_zero_endo] is built
 directly so that the core separation [free_ab_one_id_not_zero], the
 countable witness and the headline escape this pin; the composite
 [Ab_zero_hom A ∘ Ab_one A] would have carried it.  The pin is the
 donor's and is not repaired here.  ℤ itself pins nothing:
 [ab_int@{u u0 u1}] is fully polymorphic.
 - The remaining 21 constants name no [Set].

 COUNTS AND CONVENTIONS.
 - 33 [.glob] declaration heads (23 [def], 10 [prf]) plus 1 [Program]
 obligation ([empty_cone_at]), all "Closed under the global context",
 zero [Axioms:] lines; the gate carries the 33 heads, fully qualified,
 [FreeAb_not_continuous] among them ([FreeAb] itself is #400's and
 sits in Instance/Ab/Free.v's own gate entries).
 - Two [Defined] ([ab_zero_endo], [NatOneProduct]), each flipped to
 [Qed] alone in a copy of the file: [ab_zero_endo] is LOAD-BEARING
 for the whole file ([ab_zero_endo_value]'s [simpl; reflexivity]
 stops first; with that lemma removed as well, the core separation
 [free_ab_one_id_not_zero] stops, its [simpl in Hg] no longer
 reducing the zero map; the probe's [eq_refl] readback stops too —
 an earlier revision named only the two readbacks), [NatOneProduct]
 is not (library and probe compile unchanged) and stays transparent
 as data.  Eleven [Qed] tokens: the obligation, the seven refutations
 (negations; nothing downstream computes with them) and three
 equational lemmas — [ab_zero_endo_value], [fmap_one_point] and
 [SetsPoint_empty_IsLimitCone], the last consumed as data by
 [SetsPoint_empty_Limit], itself used only inside a refutation (an
 earlier revision offered the negation reason for all ten).
 - Closure 60 files excluding self: Structure/Limit/Comparison.v costs 4
 at the margin, Instance/Ab/Free.v 3, Instance/Ab/Coproduct.v 2,
 Instance/Sets/Cartesian.v 1, Instance/Zero.v 1, the other nineteen
 [Require]s 0; the binary witness accounts for 3 of the 60 (its four
 [Require]s dropped, 60 → 57; an earlier revision said 8, charging
 Structure/Limit/Comparison.v to it, but that file is witness 2's
 dependency too — [DiscreteCat_Functor'], [discrete_cone],
 [discrete_IsLimitCone_of_IsIndexedProduct]) and is kept because it
 is the issue's "comparison map" bullet.
 [Coq.ZArith.ZArith] is required explicitly (for [1%Z]; the tree's 68
 other files spell it the same way).  Name collisions: none — each of
 the 33 names has 0 word occurrences elsewhere in the tree.
 - Test/ProbeFreeAbNotContinuous430.v mirrors the [Require] list and
 carries 9 refutation commands (1 instrument + N1-N3 CONVERSION +
 N4-N5 TYPING + N6-N8 UNIVERSE), each stripped one at a time in a copy
 of the whole file and each beside its accepted controls; three
 [eq_refl] readbacks; guard coverage 37 identifier tokens inside the
 refutations / 29 also named outside, comments stripped, with eight
 exhaustive exceptions (two keywords, the five refuted declarations'
 names, the absent name); rename-simulated 15/15 ([FreeAb],
 [SetsPoint], [NatOneCone], [BinDiagram], [Ab_trivial], [Ab_Terminal],
 [Ab_Cartesian], [Ab], [Ab_Forget], [FreeAb_not_continuous],
 [FreeAb_not_PreservesLimitCone_binary_product],
 [PreservesAllLimits], [PreservesLimit], [cone_leg], [FCone]; module
 paths excluded), every first break on a positive line.  [make todo]
 grows by those 9 lines only (2246 →
 2255 over 3a387cdb, master b0d0fa63 with #429), so
 the issue's "adds no new hits" box is not met as written; disclosed.
 - "The free abelian group on a point" is never written as ℤ: no
 isomorphism [FreeAb 1 ≅ ℤ] exists in the tree (the inverse would need
 an integer scalar action on [FATerm]), and the file needs only that
 the group has a nonzero element.

 NOT DELIVERED.
 - Mac Lane's own finite-support argument (a normal form for [FATerm]
 is absent); the countable witness reaches his SHAPE by a different
 mechanism, disclosed in (3).
 - Apex-level refutations at the product shapes ([PreservesLimit
 BinDiagram FreeAb → False] would need ℤ ≇ ℤ × ℤ in Ab, the same
 normal form; the countable case would need ℤ ≇ ℤ^ℕ, whose right
 side cannot even be named in Ab — no [HasIndexedProducts Ab]); probe
 N5 pins the binary boundary, the countable one is unpinned.
 - [FreeAb 1 ≅ ℤ]; countable products in Ab; a repair of [Ab_trivial]'s
 or [_0]'s [Set] pins.
 - "The library's first recorded discontinuity witness" (false; see
 STALE PREMISES).
 - No edit to Instance/Ab.v, Instance/Ab/Free.v, Instance/Zero.v,
 Structure/Limit/Comparison.v or Structure/Limit/Preservation.v. 

 --------
 Mac Lane §V.4 练习 3（书中第 118 页；maclane:V.4:ex3）：自由阿贝尔群函子 Sets ⟶ Ab 并不保持极限——左伴随函数不必是连续的。
 nLab: https://ncatlab.org/nlab/show/continuous+functor 
 维基百科: https://en.wikipedia.org/wiki/Free_abelian_group 

 背景：自由阿贝尔群函子是一个左伴随（Instance/Ab/Free.v 的 [free_ab_adjunction : FreeAb ⊣ Ab_Forget]，#400），因此它保持余极限；Mac Lane 的练习要求给出它不保持的极限，并暗示一个可数乘积。该文件展示了在三种形状下的非连续性——空形状，Mac Lane 形状下的可数乘积，以及通过典型比较映射的二元乘积——并将其打包为该树对 [ContinuousFunctor] 和 [PreservesAllLimits] 在特定函子下的首次反驳。一个事实，仅陈述一次。以一点为自由阿贝尔群有两个不同的自同态，即恒等映射和零映射，因为它的生成元不是零（Instance/Ab/Free.v 的 [free_ab_gen_not_zero]，在 ℤ 中读取）；所以它不是零群（[free_ab_one_id_not_zero]）。下面的每一个反驳都是这个事实加上簿记：在空形状上，它立即表现为非终端性；在一个互不相连的形状上，其图恒定在该点，Sets 中的极限仍然是该点，而且每个像腿都是 [≈ id]，所以中介者必须同时等于竞争锥的每一条腿，而带有 [id] 和零映射的锥没有这样的腿；在二元形状上，同样的事实表现为 [exl ≈ exr]，在消掉比较映射后，由 [exl ∘ (id △ 0) ≈ id] 对 [exr ∘ (id △ 0) ≈ 0] 进行反驳。陈旧的前提，重新测量。- “函子及其目标不存在”：错误。Instance/Ab.v 声明了 [Ab] 和 [Ab_Forget]；Instance/Ab/Free.v 声明了 [FreeAb : Sets ⟶ Ab]、[free_ab_adjunction] 和 [free_ab_universal] —— 在同余 [fa_eq] 下的项代数 [FATerm]，不是有限支持的 ℤ 值函数。工作要点 1（用其普遍性质构造函子）由 #400 完成；这里没有重新推导任何关于自由阿贝尔群的内容。- QA 更正“使用 #540 的 Construction/FreeAb.v …… 连接到 Instance/Ab.v 的载体”：该文件在树中不存在；来源是 Instance/Ab/Free.v，已经基于 #256 的 [Ab]，没有需要桥接的部分。- “树中未记录到任何函子的连续性反例”：部分记录。Structure/Limit/Preservation/Separation.v 的 [sep_not_PreservesLimitCone] 反驳了合成跨度函子在锥级别的保持性，因此“库中记录的第一个不连续见证”并未被提出。按在类名旁边的 [False] 进行全树搜索衡量，第一个是 [ContinuousFunctor _ → False]，第一个 [PreservesAllLimits _ → False]，以及第一个在命名数学函子上反驳 [PreservesLimitCone] / [PreservesLimit] 的例子。在命名函子上的非保持性本身并非首个（早期版本曾声称过）：Instance/Top/Forgetful.v 的 [indiscrete_image_not_colimiting] 反驳了 [Top_Indiscrete] 的余锥，而 Instance/Powerset.v 的 [direct_image_not_meet_preserving] 反驳了左伴随 [DirectImage] 对二元积（[Subsets_Cartesian]）的保持——两者都没有以类名表述。- [Ab] 具有二元积、余积和双积（Instance/Ab/Coproduct.v），一个零对象和一个终对象（Instance/Ab.v），没有索引余积（Instance/Ab/Coproduct.v 和 Instance/Rng/Free.v 记录了 [HasIndexedCoproducts Ab] 的缺失），也没有索引积或完备性——衡量方式：树的 [HasIndexedProducts] 实例是集合（Sets）的（Instance/Sets/Products.v）、Cat 和 StrictCat 的（Instance/Cat/Limit.v），在 [Ab] 上没有任何实例，也不存在 [Complete Ab]（早期修订版引用了乘积部分的两个余积行）。下面的可数证据不需要任何实例：竞争锥是直接提供的，这就是为什么该声明处于锥级别。交付的内容是什么（33 个命名常量加 1 个 [Program] 义务，每一个在全局上下文中封闭）。(1) 成分。[SetsPoint]（集合的终对象），[ab_zero_endo A : A ~> A]（常量零同态，直接构建——参见 UNIVERSES 了解为什么不是作为 [Ab_zero_hom A ∘ Ab_one A]），[ab_zero_endo_value]（探针中的 [eq_refl]），以及分离条件 [free_ab_one_id_not_zero : id ≈ ab_zero_endo (FreeAb SetsPoint) → False]。 (2) 见证 1，空极限——一点的自由群在 Ab 中不是终对象。[empty_cone_at]（在任何顶点上的空图的圆锥；该文件唯一的 [Program] 义务），[SetsEmptyDiagram := From_0 Sets]，[SetsPoint_empty_IsLimitCone] 和 [SetsPoint_empty_Limit]（该点是 Sets 中的空极限），[FreeAb_not_PreservesLimitCone_empty]，以及——仅顶点形式，乘积见证在此未达（探针 N5 固定了二元情况；可数顶点情况未固定，见 NOT DELIVERED）——[FreeAb_not_PreservesLimit_empty : PreservesLimit SetsEmptyDiagram FreeAb → False] 与 [FreeAb_not_PreservesAllLimits]。（3）见证 2，MAC LANE 形状中的一个可数乘积。[NatOnes] 
 （该点处的常数族），[NatOneDiagram : DiscreteCat
 nat ⟶ Sets]
 （Structure/Limit/Comparison.v 中带注释的 [DiscreteCat_Functor']），
 [NatOneProduct] （该点在 Sets 中是其自身可数次幂），
 [NatOneCone] / [NatOneCone_IsLimitCone] （通过 [discrete_IsLimitCone_of_IsIndexedProduct]），竞争锥
 [NatCompeting]，腿为 [nat_legs]（0 处的 [id]，上方零映射），
 [fmap_one_point]，以及 [FreeAb_not_PreservesLimitCone_countable_product]。机制不是 Mac Lane 的：他的论点是比较
 FreeAb(∏ Xₙ) → ∏ FreeAb(Xₙ) 不是满射，因为左边的每个元素都有有限支撑，这需要 [FATerm] 的正规形式或系数唯一性，而树没有这种性质（Instance/Ab/Free.v INDEX 项中就是这样说的）；在这里，因子是点，积坍缩为点，并且各支重合。形状是他的；证明不是如此，而且可数性是惰性的：同样的论证在任何具有两个或更多对象的离散形状下都成立。(4) 证据 3，通过比较映射的二元积（该问题的第二项工作要点）。[BinOnes]，[BinDiagram]，
 [FreeAb_binary_cmp := binary_comparison FreeAb BinOnes]（典型的 FreeAb(1 × 1) → FreeAb 1 × FreeAb 1），
 [FreeAb_binary_comparison_not_iso]，
 [FreeAb_not_PreservesLimitCone_binary_product]（通过 [comparison_iso_of_PreservesLimitCone]）和
 [FreeAb_not_CartesianFunctor]（通过 Structure/Limit/Comparison.v 的 [cartesian_functor_iff_comparison_iso]）。（5）结论。[FreeAb_not_continuous : ContinuousFunctor FreeAb → False] —— 问题的固定陈述，通过 witness 2 —— 和 [FreeAb_not_continuous_via_empty] 通过 witness 1；参见 UNIVERSES，了解为何可数路径是重点。（6）同一对偶的积极方面。[Ab_Forget_Continuous]（RAPL: Adjunction/Continuity.v 的 [right_adjoint_Continuous]）和 [FreeAb_Cocontinuous]（LAPC: [left_adjoint_Cocontinuous]），各一行：连续性正是左伴随缺乏的。（7）回读。[freeab_is_left_adjoint := free_ab_adjunction]，[free_ab_one_carrier]（一个点上的自由群的载体是[FATerm SetsPoint]，[eq_refl]），[bin_diagram_objects]（[eq_refl]）。UNIVERSES（由 [About] 在 [Set Printing Universes] 下，在所有 33 个常数上测量）。没有区块包含方程。[Set] 出现在 33 个中的正好 12 个，由两个捐赠者提供，都由 [About] 对捐赠者进行归属：
 - [_0@{u …} : Category@{u Set Set}]（Instance/Zero.v，声明为裸的，其在 [Set] 的同态）固定了八个空形常数：
 [empty_cone_at]、[SetsEmptyDiagram]、[SetsPoint_empty_IsLimitCone]、
 [SetsPoint_empty_Limit]、[FreeAb_not_PreservesLimitCone_empty]、
 [FreeAb_not_PreservesLimit_empty]、[FreeAb_not_PreservesAllLimits]
 以及 [FreeAb_not_continuous_via_empty] — [PreservesLimitCone] 识别形状的同态与环境的同态，因此通过空形状函子自身的同态级别为 [Set]：
 [FreeAb_not_continuous_via_empty] 为 [FreeAb@{u10 Set …}] 陈述，
 即 [Sets@{Set u} ⟶ Ab@{u Set}] 仅此。这就是为什么标题 [FreeAb_not_continuous] 通过可数乘积，其形状 [DiscreteCat nat] 有自由级：它和 [FreeAb_not_PreservesLimitCone_countable_product] 根本没有 [Set]。顶层反驳仅存在于空形状，所以 [FreeAb_not_PreservesAllLimits] 在 [Ab@{u Set}] 上陈述，并且在这里不能以其他方式存在。- [Ab_trivial@{} : AbObject@{Set Set Set}]（实例/Ab.v，单态）固定了从平凡群组组装的所有内容 —— [Ab_one]、ZW105WZZ、ZW106WZZ、ZW107WZZ、ZW108WZZ（ZW109WZZ、ZW110WZZ）—— 并且通过 [Ab_Cartesian] 对四个二元见证常数 [FreeAb_binary_cmp]、ZW113WZZ、ZW114WZZ、ZW115WZZ（探针 N6-N8: [Ab_trivial]、ZW117WZZ、ZW118WZZ 在严格高于 [Set] 的 Hom 级拒绝，而 [Ab] 和 [Ab_Forget] 在那里被接受）。[ab_zero_endo] 是直接构建的，因此核心分离 [free_ab_one_id_not_zero]、可计数的证据和标题可以避开这个销；复合体 [Ab_zero_hom A ∘ Ab_one A] 本来会携带它。这个销属于捐赠者，这里没有修复。ℤ 本身不固定任何东西：[ab_int@{u u0 u1}] 完全是多态的。- 其余 21 个常量没有命名任何 [Set]。计数与约定。- 33 个 [.glob] 声明头（23 个 [def]，10 个 [prf]）加 1 个 [Program] 义务（[empty_cone_at]），全部在“全局上下文下关闭”，零 [Axioms:] 行；该门携带 33 个头，完全合格，[FreeAb_not_continuous] 其中（[FreeAb] 本身是 #400 的，并且位于 Instance/Ab/Free.v 自身的门条目中）。- 两个 [Defined]（[ab_zero_endo]，[NatOneProduct]），每个在文件副本中单独翻转为 [Qed]：[ab_zero_endo] 对整个文件都是承重的（[ab_zero_endo_value] 的 [simpl; reflexivity] 先停止；当该引理也被移除时，核心分离 [free_ab_one_id_not_zero] 停止，其 [simpl in Hg] 不再简化零映射；探针的 [eq_refl] 回读也停止——早期版本只命名了两个回读），[NatOneProduct] 不承重（库和探针编译保持不变）并作为数据保持透明。十一个 [Qed] 代币：义务、七个反驳（否定；下游没有任何计算使用它们）和三个方程引理 —— [ab_zero_endo_value]、[fmap_one_point] 和 [SetsPoint_empty_IsLimitCone]，最后一个被 [SetsPoint_empty_Limit] 作为数据使用，[SetsPoint_empty_Limit] 本身仅在反驳中使用（早期版本为所有十个提供了否定理由）。- 闭包 60 个文件（不包括自身）：Structure/Limit/Comparison.v 花费 4，边际上，Instance/Ab/Free.v 3，Instance/Ab/Coproduct.v 2，Instance/Sets/Cartesian.v 1，Instance/Zero.v 1，其余十九个 [Require] 为 0；二进制证据占据了 60 个中的 3 个（其四个 [Require] 被删除，60 → 57；早期修订为 8，将 Structure/Limit/Comparison.v 计入其中，但该文件也是证据 2 的依赖 —— [DiscreteCat_Functor']、[discrete_cone]、[discrete_IsLimitCone_of_IsIndexedProduct]），并保留它，因为它是该问题的“比较映射”条目。[Coq.ZArith.ZArith] 被显式要求（用于 [1%Z]；树中的其他 68 个文件拼写方式相同）。名称冲突：无 —— 每个 33 个名称在树的其他地方的词语出现次数为 0。- Test/ProbeFreeAbNotContinuous430.v 镜像了 [Require] 列表，并包含 9 个反驳命令（1 个仪器 + N1-N3 转换 + N4-N5 打字 + N6-N8 宇宙），每个命令在整个文件的副本中逐一剥离，并且每个都在其接受的控制旁边；三个 [eq_refl] 回读；守护覆盖在反驳中有 37 个标识符标记 / 外部也命名了 29 个，注释已剥离，有八个详尽的例外（两个关键字、五个被反驳声明的名称、缺失的名称）；重命名模拟 15/15（[FreeAb]、[SetsPoint]、[NatOneCone]、[BinDiagram]、[Ab_trivial]、[Ab_Terminal]、[Ab_Cartesian]、[Ab]、[Ab_Forget]、[FreeAb_not_continuous]、[FreeAb_not_PreservesLimitCone_binary_product]、[PreservesAllLimits]、[PreservesLimit]、[cone_leg]、[FCone]；模块路径已排除），每个第一次中断在 po 上敏感线。[make todo]
 仅增加了那9行（2246 → 2255，在3a387cdb上，master b0d0fa63，带#429），所以
 问题中的“没有新增命中”框按原文未满足；已披露。- “一个点上的自由阿贝尔群”从未写成ℤ：树中不存在同构 [FreeAb 1 ≅ ℤ]（逆同构将需要在 [FATerm] 上进行整数标量作用），并且文件只需要该群有一个非零元素。未交付。- Mac Lane 自己的有限支持论证（[FATerm] 的标准形式缺失）；可数的见证通过不同的机制达到他的形态，在（3）中揭示。- 关于乘积形态的顶点级反驳（[PreservesLimit BinDiagram FreeAb → False] 将需要 ℤ ≇ ℤ × ℤ 在 Ab 中，同样的标准形式；可数情况将需要 ℤ ≇ ℤ^ℕ，其右侧甚至在 Ab 中无法命名——不存在 [HasIndexedProducts Ab]）；探测 N5 固定了二进制边界，可数边界未固定。- [FreeAb 1 ≅ ℤ]；Ab 中的可数乘积；对 [Ab_trivial] 或 [_0] 的 [Set] 固定的修复。- “图书馆记录的第一个不连续见证”（错误；见过期前提）。- 不修改 Instance/Ab.v、Instance/Ab/Free.v、Instance/Zero.v、Structure/Limit/Comparison.v 或 Structure/Limit/Preservation.v。
*)

(* * ** The point of Sets, and the zero endomorphism of an abelian group / * ** 集合的意义，以及阿贝尔群的零自同态 *)

Definition SetsPoint : Sets := @terminal_obj Sets Sets_Terminal.

(*
 Built directly rather than as [Ab_zero_hom A ∘ Ab_one A]: the composite
 would route through [Ab_trivial], whose monomorphic [Set] universes would
 then pin this constant (see the header's UNIVERSES). 

 --------
 直接构建而不是作为 [Ab_zero_hom A ∘ Ab_one A]：复合体会通过 [Ab_trivial] 路由，其单态的 [Set] 宇宙随后会固定这个常量（参见头文件的 UNIVERSES）。
*)
Definition ab_zero_endo (A : Ab) : A ~{Ab}~> A.
Proof.
  unshelve refine {| cmon_map := {| morphism := fun _ => cmon_zero A |} |}.
  - intros x y _; reflexivity.
  - reflexivity.
  - intros a b; simpl; symmetry; apply cmon_plus_zero_l.
Defined.

Lemma ab_zero_endo_value (A : Ab) (a : carrier (cmon_setoid A)) :
  cmon_map (ab_zero_endo A) a ≈ cmon_zero A.
Proof. simpl; reflexivity. Qed.

(* * ** The one separation everything below is spent on / * ** 一切下面花费的分离 *)

(*
 The free abelian group on a point has two distinct endomorphisms, the
 identity and the zero map, because its generator is not zero
 (Instance/Ab/Free.v's [free_ab_gen_not_zero], read at ℤ).  Every
 refutation in this file is this fact plus bookkeeping. 

 --------
 一个点上的自由阿贝尔群有两个不同的自同态，分别是恒等映射和零映射，因为它的生成元不为零（Instance/Ab/Free.v 的 [free_ab_gen_not_zero]，在 ℤ 中读取）。本文件中的每个反驳都是这个事实加上记录工作。
*)
Lemma free_ab_one_id_not_zero :
  @id Ab (FreeAb SetsPoint) ≈ ab_zero_endo (FreeAb SetsPoint) → False.
Proof.
  intro H.
  pose proof (H (fa_gen (X:=SetsPoint) ttt)) as Hg; simpl in Hg.
  exact (free_ab_gen_not_zero (X:=SetsPoint) ab_int 1%Z ab_int_one_not_zero
           ttt Hg).
Qed.

(* * ** Witness 1: the empty limit — the free group on a point is not terminal in Ab / * ** 证人 1：空极限——一点上的自由群在阿贝尔群中不是终对象 *)

Program Definition empty_cone_at {C : Category} (K : _0 ⟶ C) (c : C)
  : Cone K := {|
  vertex_obj := c;
  coneFrom := {| vertex_map := fun x => match x return _ with end |}
|}.
Next Obligation. destruct x. Qed.

Definition SetsEmptyDiagram : _0 ⟶ Sets := From_0 Sets.

Lemma SetsPoint_empty_IsLimitCone :
  IsLimitCone (empty_cone_at SetsEmptyDiagram SetsPoint).
Proof.
  intro M.
  unshelve eexists.
  - exact (@one Sets Sets_Terminal _).
  - intro x; destruct x.
  - intros v _; apply (@one_unique Sets Sets_Terminal).
Qed.

Definition SetsPoint_empty_Limit : Limit SetsEmptyDiagram :=
  limitcone_limit _ SetsPoint_empty_IsLimitCone.

Theorem FreeAb_not_PreservesLimitCone_empty :
  PreservesLimitCone SetsEmptyDiagram FreeAb → False.
Proof.
  intro P.
  pose proof (P _ SetsPoint_empty_IsLimitCone) as H.
  destruct (H (empty_cone_at _ (FreeAb SetsPoint))) as [u _ Hu].
  apply free_ab_one_id_not_zero.
  transitivity u.
  - symmetry; apply Hu; intro x; destruct x.
  - apply Hu; intro x; destruct x.
Qed.

(* The apex-only form, which the product witnesses below CANNOT reach. / 仅顶点形式，产品在下面无法达到的形式。 *)
Theorem FreeAb_not_PreservesLimit_empty :
  PreservesLimit SetsEmptyDiagram FreeAb → False.
Proof.
  intro P.
  pose proof (@preserves_limit _ _ _ _ _ P SetsPoint_empty_Limit) as H.
  destruct (@ump_limit _ _ _ _ H (empty_cone_at _ (FreeAb SetsPoint)))
    as [u _ Hu].
  apply free_ab_one_id_not_zero.
  transitivity u.
  - symmetry; apply Hu; intro x; destruct x.
  - apply Hu; intro x; destruct x.
Qed.

Definition FreeAb_not_PreservesAllLimits : PreservesAllLimits FreeAb → False :=
  fun H => FreeAb_not_PreservesLimit_empty (H _ SetsEmptyDiagram).

(* * ** Witness 2: a countable product in Mac Lane's shape / * ** 证人2：Mac Lane 形状中的可数积 *)

Definition NatOnes : nat → Sets := fun _ => SetsPoint.
Definition NatOneDiagram : DiscreteCat nat ⟶ Sets := DiscreteCat_Functor' NatOnes.

Definition NatOneProduct :
  IsIndexedProduct NatOnes SetsPoint (fun _ => @one Sets Sets_Terminal SetsPoint).
Proof.
  constructor; intros c pi.
  exists (@one Sets Sets_Terminal c).
  - intro a; apply (@one_unique Sets Sets_Terminal).
  - intros v _; apply (@one_unique Sets Sets_Terminal).
Defined.

Definition NatOneCone : Cone NatOneDiagram :=
  discrete_cone NatOneDiagram SetsPoint (fun _ => @one Sets Sets_Terminal SetsPoint).

Definition NatOneCone_IsLimitCone : IsLimitCone NatOneCone :=
  discrete_IsLimitCone_of_IsIndexedProduct NatOneDiagram NatOneCone NatOneProduct.

Definition nat_legs (n : nat) : FreeAb SetsPoint ~{Ab}~> FreeAb SetsPoint :=
  match n with
  | O   => id
  | S _ => ab_zero_endo (FreeAb SetsPoint)
  end.

Definition NatCompeting : Cone (FreeAb ◯ NatOneDiagram) :=
  discrete_cone (FreeAb ◯ NatOneDiagram) (FreeAb SetsPoint) nat_legs.

Lemma fmap_one_point :
  fmap[FreeAb] (@one Sets Sets_Terminal SetsPoint) ≈ @id Ab (FreeAb SetsPoint).
Proof.
  rewrite (@one_unique Sets Sets_Terminal SetsPoint _ (@id Sets SetsPoint)).
  exact (@fmap_id Sets Ab FreeAb SetsPoint).
Qed.

Theorem FreeAb_not_PreservesLimitCone_countable_product :
  PreservesLimitCone NatOneDiagram FreeAb → False.
Proof.
  intro P.
  pose proof (P _ NatOneCone_IsLimitCone) as H.
  destruct (H NatCompeting) as [u Hu _].
  apply free_ab_one_id_not_zero.
  assert (Hone : ∀ n : nat, u ≈ nat_legs n).
  { intro n.
    rewrite <- (Hu n).
    change (cone_leg (FCone FreeAb NatOneCone) n)
      with (fmap[FreeAb] (cone_leg NatOneCone n)).
    rewrite fmap_one_point.
    now rewrite id_left. }
  rewrite <- (Hone 0%nat).
  exact (Hone 1%nat).
Qed.

(* * ** Witness 3: the binary product, through the comparison map / * ** 见证 3：通过比较映射的二元乘积 *)

Definition BinOnes : bool → Sets := binary_fam SetsPoint SetsPoint.
Definition BinDiagram : DiscreteCat bool ⟶ Sets := DiscreteCat_Functor' BinOnes.

Definition FreeAb_binary_cmp :
  FreeAb (BinOnes true × BinOnes false)
    ~{Ab}~> FreeAb (BinOnes true) × FreeAb (BinOnes false) :=
  binary_comparison FreeAb BinOnes.

Theorem FreeAb_binary_comparison_not_iso :
  IsIsomorphism FreeAb_binary_cmp → False.
Proof.
  intro Hiso.
  apply free_ab_one_id_not_zero.
  assert (Hsets : @exl Sets _ SetsPoint SetsPoint ≈ @exr Sets _ SetsPoint SetsPoint).
  { transitivity (@one Sets Sets_Terminal (SetsPoint × SetsPoint));
      [ | symmetry ]; apply (@one_unique Sets Sets_Terminal). }
  assert (Hcmp : @exl Ab _ (FreeAb SetsPoint) (FreeAb SetsPoint) ∘ FreeAb_binary_cmp
                 ≈ @exr Ab _ (FreeAb SetsPoint) (FreeAb SetsPoint) ∘ FreeAb_binary_cmp).
  { unfold FreeAb_binary_cmp.
    rewrite (binary_comparison_exl FreeAb BinOnes).
    rewrite (binary_comparison_exr FreeAb BinOnes).
    now rewrite Hsets. }
  assert (Hlr : @exl Ab _ (FreeAb SetsPoint) (FreeAb SetsPoint)
                ≈ @exr Ab _ (FreeAb SetsPoint) (FreeAb SetsPoint)).
  { destruct Hiso as [g Hgf Hfg].
    rewrite <- (id_right (@exl Ab _ (FreeAb SetsPoint) (FreeAb SetsPoint))).
    rewrite <- Hgf, comp_assoc, Hcmp, <- comp_assoc, Hgf.
    now rewrite id_right. }
  rewrite <- (@exl_fork Ab _ _ _ _
                (@id Ab (FreeAb SetsPoint)) (ab_zero_endo (FreeAb SetsPoint))).
  rewrite Hlr.
  apply (@exr_fork Ab _ _ _ _
           (@id Ab (FreeAb SetsPoint)) (ab_zero_endo (FreeAb SetsPoint))).
Qed.

Theorem FreeAb_not_PreservesLimitCone_binary_product :
  PreservesLimitCone BinDiagram FreeAb → False.
Proof.
  intro P.
  apply FreeAb_binary_comparison_not_iso.
  exact (comparison_iso_of_PreservesLimitCone FreeAb P
           (binary_image_cone_IsLimitCone FreeAb BinOnes)
           (binary_cone BinOnes)
           (binary_cone_IsLimitCone BinOnes)).
Qed.

Theorem FreeAb_not_CartesianFunctor :
  @CartesianFunctor Sets Ab FreeAb _ _ → False.
Proof.
  intro HF.
  apply FreeAb_binary_comparison_not_iso.
  exact (fst (cartesian_functor_iff_comparison_iso FreeAb) HF SetsPoint SetsPoint).
Qed.

(* * ** The conclusion of the exercise / * ** 练习的结论 *)

(*
 The headline goes through the countable product (witness 2), whose shape
 [DiscreteCat nat] carries free universes; the empty shape [_0] is
 declared at [Category@{u Set Set}] (Instance/Zero.v) and pins the
 functor's hom level to [Set] (see the header's UNIVERSES). 

 --------
 标题遍历可数乘积（证人 2），其形状 [DiscreteCat nat] 携带自由宇宙；空形状 [_0] 在 [Category@{u Set Set}]（Instance/Zero.v）中声明，并将函子同态水平固定到 [Set]（见标题的 UNIVERSES）。
*)
Definition FreeAb_not_continuous : ContinuousFunctor FreeAb → False :=
  fun H => FreeAb_not_PreservesLimitCone_countable_product (H _ NatOneDiagram).

Definition FreeAb_not_continuous_via_empty :
  ContinuousFunctor FreeAb → False :=
  fun H => FreeAb_not_PreservesLimitCone_empty (H _ SetsEmptyDiagram).

(* * ** The positive side of the same adjunction / * **相同连接的正面 *)

Definition Ab_Forget_Continuous : ContinuousFunctor Ab_Forget :=
  right_adjoint_Continuous free_ab_adjunction.

Definition FreeAb_Cocontinuous : CocontinuousFunctor FreeAb :=
  left_adjoint_Cocontinuous free_ab_adjunction.

(** ** Readbacks / ** 回读 *)

Example freeab_is_left_adjoint : FreeAb ⊣ Ab_Forget := free_ab_adjunction.

Example free_ab_one_carrier :
  carrier (Ab_Forget (FreeAb SetsPoint)) = FATerm SetsPoint := eq_refl.

Example bin_diagram_objects : BinOnes true = SetsPoint := eq_refl.
