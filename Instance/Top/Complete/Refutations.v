Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Complete.Freyd.
Require Import Category.Construction.Quotient.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.CompHaus.
Require Import Category.Instance.Top.StoneCech.Refutations.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.
Require Import Category.Instance.Top.Complete.

Generalizable All Variables.

(* * * Where completeness of spaces stops: [PTopCat], and [Top] below its homs / * * 空间完整性的终点：[PTopCat]，以及其下的[Top]的同源 *)

(*
 Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
 §V.2 Proposition 3, book p. 114 (maclane:V.2:prop3), Freyd's theorem
 that a small complete category is a preorder, consumed through
 Structure/Complete/Freyd.v; §V.9 Remark 1 as in the header of
 Instance/Top/Complete.v, whose completeness this file bounds.
 nLab: https://ncatlab.org/nlab/show/complete+small+category
 nLab: https://ncatlab.org/nlab/show/Top

 BACKGROUND.  Freyd's observation (Structure/Complete/Freyd.v's header):
 were a category with products indexed by its own arrow collection K to
 carry two distinct parallel arrows, the 2^K choices between them would
 give 2^K arrows into the K-fold power, more than the K arrows there are.
 Completeness in the book's sense is therefore a property of large
 categories, relative to the size of the shapes.  #455's Instance/Top/
 StoneCech/Refutations.v turned that into theorems about the Type-valued
 [Top] and [CompHaus], whose homs sit above their points, at every shape
 universe at or above the homs; this file runs the same argument against
 Instance/Top/Prop.v's [PTopCat@{o so}], whose homs sit AT the points'
 universe [o] and whose objects sit at [so], above it, and carries
 #455's forms over [Top] and [CompHaus] down to every shape universe
 above the points.  The two points of [PBool], [ppoint_true] and
 [ppoint_false] (Instance/Top/Subspace.v), are told apart by evaluation
 at the point ([pbool_eval_pt]), constructively.  Nothing here is an
 axiom: informative excluded middle ([IEM], Instance/Sets/Classifier/
 OneLevel.v) and decidable equality of spaces ([ObjDecEq],
 Construction/Quotient.v) are hypotheses, and under either an arrow
 index exists ([canonical_ArrowIndex], through Instance/Top/StoneCech/
 Refutations.v's [ObjDecEq_of_IEM]).

 NAMES.  The refutations here and in Instance/Top/Cocomplete/
 Refutations.v, the colimit dual, share one scheme, the same on both
 sides: [_Freyd] and [_Cantor_] name the ARGUMENT, the hypothesis suffix
 names the REACH, and [_below], on the limit side only, marks a form
 over [Top] or [CompHaus] that reaches below the hom universe [h].
 [_Freyd]           Freyd's argument from an arrow index
 ([ArrowIndex]) at the shape (or index) universe
 [s], the index being the hypothesis; nothing ties
 [s] to the points' universe [o].
 [_ObjDecEq]        decidable equality of spaces ([ObjDecEq]), at
 every [s] with [o < s], [o := Set] included.
 [_IEM]             informative excluded middle ([IEM]), at every [s]
 with [o < s], [o := Set] included.
 [_IEM_canonical]   [IEM] through the canonical index of the category's
 own objects, untransported: every [s] at or above
 the object universe ([so] for [PTopCat@{o so}],
 [h] for [Top@{h o}]).
 [_below_ObjDecEq], [_below_IEM]   (limit side, over [Top] and
 [CompHaus]) the reach of [_ObjDecEq] and [_IEM]
 (for products [o < s <= h], at the reading
 [@{s s s h h h}]),
 the shapes strictly between the points and the
 homs included, set apart from the forms of the
 same classes that stop at [h <= s]: #455's
 [Top_not_complete_IEM] and
 [CompHaus_not_complete_IEM_below], and
 [Top_iprod_refuted_IEM_canonical] here.  The
 colimit side has no form that stops at [h <= s],
 and its [Top] forms carry the plain suffixes.
 [_Cantor_ObjDecEq], [_Cantor_IEM]   (colimit side only) Cantor's
 argument under the same hypotheses and with the
 same reach, but that the [ObjDecEq] form needs
 [Set < o].
 Instance/Top/StoneCech/Refutations.v's [Top_not_complete],
 [Top_not_complete_IEM] and [CompHaus_not_complete_IEM_below] (#455)
 predate the scheme: the first is a [_Freyd] form, the second an
 [_IEM_canonical] one, and the third's [_below] means below the OBJECT
 universe [c] of [CompHaus], at [h <= s]; this file's
 [CompHaus_not_complete_below_IEM] is the form that reaches below the
 hom universe.

 WHAT IS HERE.  This is the [PTopCat] half of #1328's item 4 (re-run
 #455's refutations against the Prop-valued encoding), for limits, and
 the extension of #455's [Top] and [CompHaus] forms below the homs.
 - [PTop_not_complete_Freyd]: given an [ArrowIndex] of [PTopCat] at a
 shape universe [s], [Complete@{r s o so} PTopCat] is false.
 [PTop_not_complete_IEM_canonical]: under [IEM], every [s] with
 [so <= s], [canonical_ArrowIndex] indexing at the arrow collection,
 which sits at [so]; [PTop_not_complete_IEM] below subsumes it (its
 [o < s] follows from [so <= s]), and it stays as the untransported
 form.
 - [PTop_ArrowIndex_transport]: the objects and homs of
 [PTopCat@{o so1}] and [PTopCat@{o so2}] are the same [PTop@{o}] and
 [PMor@{o}], so an arrow index moves between them, with no equation
 in its block; through it, [PTop_not_complete_ObjDecEq] and
 [PTop_not_complete_IEM] refute completeness at EVERY shape universe
 strictly above the points, [o < s], the canonical index being built
 at [PTopCat@{o s}] and transported.  The colimit dual reuses it.
 - [PTop_no_ArrowIndex_below]: constructively, NO arrow index of
 [PTopCat@{o so}] exists at any universe [s <= o], by
 [PTop_not_complete_Freyd] against Instance/Top/Complete.v's
 [PTop_Complete]; [PTop_no_ArrowIndex_at_points] is its case
 [s = o], proved against the book's route [PTop_Complete_via_products]
 instead.
 - [PTop_iprod_refuted_IEM]: under [IEM], products indexed at any
 universe [s] strictly above the points are refuted with no
 equalizer involved, while Instance/Top/Complete.v's
 [PTop_HasIndexedProducts] builds them at every index universe at or
 below [o].
 - [Top_iprod_refuted_IEM_canonical]: under [IEM], the Type-valued
 [Top@{h o}] has no [HasIndexedProducts@{s s s s h h}] at any index
 universe [s] at or above its hom universe [h], which is also its
 object universe: the canonical index, untransported.
 - [top_rebuild] and [Top_ArrowIndex_transport]: a continuous map of
 [Top@{h1 o}] is rebuilt as one of [Top@{h2 o}], the same map of
 points with the continuity field eta-expanded, and through it an
 arrow index moves between the two hom universes; neither block
 carries an equation ([About]).  The eta-expansion is what keeps the
 two hom universes apart.  Written [continuity := continuity f], the
 field is passed through unexpanded, elaboration unifies
 [Continuous@{h1 o}] with [Continuous@{h2 o}] first-order, and the
 rebuild acquires the equation [h1 = h2] (read back by [About] under
 the binder [@{o h1 h2 | o < h1, o < h2 +}]); under
 [@{o h1 h2 | o < h1, h1 < h2 +}] it is refused ("Cannot enforce
 h1 = h2 because h1 < h2").  That equation is an artifact of the
 encoding, not a wall; Test/ProbeTopComplete458.v pins it as such
 (N29) beside the eta-expanded rebuild at [h1 < h2], accepted.
 - Through the transport, the canonical index being built at
 [Top@{s o}]: [Top_not_complete_below_ObjDecEq] and
 [Top_not_complete_below_IEM] refute [Complete@{r s h h} Top@{h o}]
 at every [s] with [o < s], the shapes strictly between the points
 and the homs included, the first at [o := Set] as well;
 [Top_iprod_refuted_below_IEM] refutes
 [HasIndexedProducts@{s s s h h h} Top@{h o}] under [IEM] at every
 [s] with [o < s <= h].  The fourth slot of [HasIndexedProducts]
 bounds its third, where these statements put the index universe
 [s], and its sixth, the homs ([About]: [u1 <= u2] and
 [u4 <= u2]), so this reading carries [s <= h] and
 [Top_iprod_refuted_IEM_canonical]'s reading [@{s s s s h h}]
 carries [h <= s]; the two meet at [s = h].
 [CompHaus_not_complete_below_IEM] is #455's
 [CompHaus_ArrowIndex_of_Top] applied to the transported index: it
 refutes [Complete@{r s h c} CompHaus] under [IEM] at every [s] with
 [o < s], below [h] included, at the instances of [CompHaus] that
 Instance/Top/StoneCech/Refutations.v's COVERAGE records for
 [CompHaus_not_complete_IEM_below] (the two blocks agree but for
 that constant's [h <= s], which is [o < s] here).

 THE BOUNDARY.  With Instance/Top/Complete.v: completeness of
 [PTopCat@{o so}] is provable at every shape universe [s <= o]
 ([PTop_Complete], with no hypothesis) and refuted under [IEM], or under
 [ObjDecEq], at every [s] with [o < s] ([PTop_not_complete_IEM],
 [PTop_not_complete_ObjDecEq]).  No shape universe lies between the
 two; without [IEM], [ObjDecEq] or an index nothing above the points is
 refuted (NOT DELIVERED).  Measured in the scratch file of
 Instance/Top/Complete.v's boundary paragraph: both refutations are
 accepted at an [s] with [o < s] and at [o := Set], and
 [PTop_not_complete_IEM] read at [Complete@{o o o so}] is refused
 ("Cannot enforce <1> = o because <1> < o", the generated universe
 written <1>).  The index side is sharp the same way: no arrow index at
 or below [o], constructively, while the proof of
 [PTop_not_complete_ObjDecEq] builds one at every [s] above it from
 [ObjDecEq] ([canonical_ArrowIndex] at [PTopCat@{o s}], transported).
 Over the Type-valued [Top@{h o}] completeness is refuted under [IEM],
 or under [ObjDecEq], at every [s] with [o < s], and at [s <= o] it is
 neither built nor refuted.  Measured in Test/ProbeTopComplete458.v:
 [Top_not_complete_below_IEM] and [CompHaus_not_complete_below_IEM]
 are accepted at an [s] with [o < s < h], and
 [Top_not_complete_below_ObjDecEq] at [o := Set];
 [Top_not_complete_below_IEM] read at [s := o], and
 [Top_iprod_refuted_below_IEM] read at the index universe [o], each by
 its universe instance, are refused ("Cannot enforce o < o because
 o = o"), and #455's
 [Top_not_complete_IEM] and
 [CompHaus_not_complete_IEM_below] read at an [s] with [o < s < h] are
 refused ("Cannot enforce <3> = h because <3> <= <2> < h", the
 generated universes numbered in order of appearance in the message).

 STRENGTHS.  Every theorem ends in [False].  [PTop_ArrowIndex_transport]
 and [Top_ArrowIndex_transport] are data whose decoding law is [≈] of
 arrows, [top_rebuild] is data, and the two [PTop_no_ArrowIndex_*] are
 [:=] terms ending in [False].  No proof ends [Defined].

 UNIVERSES, read by [About] under [Set Printing Universes], stdlib caps
 left out; [e] the level of [IEM], free.
 PTop_not_complete_Freyd@{r s o so} :
 ArrowIndex@{s so o} PTopCat@{o so} → ¬ Complete@{r s o so}
 ( * o < so, s <= r, o <= r: nothing ties s to o * )
 PTop_not_complete_IEM_canonical@{e r s o so} :
 IEM@{e} → ¬ Complete@{r s o so}      ( * so <= s, o <= s * )
 PTop_not_complete_ObjDecEq@{r s o so} :
 ObjDecEq PTopCat@{o so} → ¬ Complete@{r s o so}   ( * o < s * )
 PTop_not_complete_IEM@{e r s o so} :
 IEM@{e} → ¬ Complete@{r s o so}      ( * o < s * )
 PTop_no_ArrowIndex_below@{s o so u} :
 ¬ ArrowIndex@{s so o} PTopCat@{o so}  ( * s <= o * )
 PTop_iprod_refuted_IEM@{e s o so} :
 IEM@{e} → ¬ HasIndexedProducts@{s s s s so o} PTopCat@{o so}
 ( * o < s * )
 Top_iprod_refuted_IEM_canonical@{e s h o} :
 IEM@{e} → ¬ HasIndexedProducts@{s s s s h h} Top@{h o}
 ( * o < h, h <= s * )
 top_rebuild@{o h1 h2} :
 ContinuousMorphism@{h1 o} X Y → ContinuousMorphism@{h2 o} X Y
 ( * o < h1, o < h2: no equation * )
 Top_ArrowIndex_transport@{s o h1 h2} :
 ArrowIndex@{s h1 h1} Top@{h1 o} → ArrowIndex@{s h2 h2} Top@{h2 o}
 ( * o < h1, o < h2: no equation * )
 Top_not_complete_below_ObjDecEq@{r s h o} :
 ObjDecEq Top@{h o} → ¬ Complete@{r s h h}   ( * o < h, o < s * )
 Top_not_complete_below_IEM@{e r s h o} :
 IEM@{e} → ¬ Complete@{r s h h}       ( * o < h, o < s * )
 Top_iprod_refuted_below_IEM@{e s h o} :
 IEM@{e} → ¬ HasIndexedProducts@{s s s h h h} Top@{h o}
 ( * o < h, o < s, s <= h * )
 CompHaus_not_complete_below_IEM@{e r s c h o …} :
 IEM@{e} → ¬ Complete@{r s h c}  ( * o < h, o < s, h <= c * )
 [CompHaus_not_complete_below_IEM] carries seven further universes, the
 slots of [CompHaus] and [Top] that #455's [CompHaus_not_complete] and
 [CompHaus_ArrowIndex_of_Top] leave free; its block, stdlib caps left
 out, is #455's [CompHaus_not_complete_IEM_below]'s with [h <= s]
 replaced by [o < s], constraint for constraint.  Over the [About]
 output of all 17 of this file's constants (its [Print Module]
 listing; it declares no obligation, record or inductive), [Set] occurs
 in 10 blocks and only as a strict lower bound on an object universe of
 [PTopCat]: [Set < so] in 9, [Set < s] in the three refutations that
 transport over [PTopCat] ([PTop_not_complete_ObjDecEq],
 [PTop_not_complete_IEM], [PTop_iprod_refuted_IEM]; the [PTopCat@{o s}]
 they build the index at) and [Set < so1], [Set < so2] in
 [PTop_ArrowIndex_transport]; none of the seven constants over [Top] and
 [CompHaus] mentions [Set], and no block carries an equation.

 ROUTE AND COST.  Closure 173 [Category.*] modules excluding this file
 ([Print Libraries]).  Instance/Top/StoneCech/Refutations.v, required
 for [ObjDecEq_of_IEM], [Top_not_complete], [CompHaus_not_complete] and
 [CompHaus_ArrowIndex_of_Top] rather than restating them, costs 28 at
 the margin (dropped alone: 145); Instance/Top/CompHaus.v, required for
 the name [CompHaus], costs nothing at the margin, since the first loads
 it; dropped together they cost 31 (142).

 NOT DELIVERED.  A refutation above the points with neither an index
 nor [IEM] nor [ObjDecEq]: thinness of a small complete category is not
 constructively provable (Structure/Complete/Freyd.v's header).  The
 colimit side (Instance/Top/Cocomplete/Refutations.v).  For the
 Type-valued [Top], completeness at shapes at or below the points,
 [s <= o], is neither built nor refuted (Instance/Top/Complete.v builds
 it over [PTopCat] only), and neither are its products at index
 universes at or below [o]; nor is [CompHaus]'s completeness there.
 This file has no counterpart of the colimit side's Cantor argument. 

 --------
 麦克·莱恩，《为实际工作的数学家准备的范畴论》，第2版（GTM 5），§V.2 命题 3，书本第114页（maclane:V.2:prop3），弗雷德定理，小完备范畴是预序，通过 Structure/Complete/Freyd.v 使用；§V.9 备注 1 如 Instance/Top/Complete.v 的页眉所示，该文件限制了其完备性。
 nLab: https://ncatlab.org/nlab/show/complete+small+category
 nLab: https://ncatlab.org/nlab/show/Top背景。Freyd 的观察（Structure/Complete/Freyd.v 的标题）：如果一个范畴有由其自身箭头集合 K 索引的积，以承载两个不同的平行箭头，那么在它们之间有 2^K 种选择，这会产生 2^K 条箭头进入 K 次幂，超过了原本的 K 条箭头。因此，书中所说的完备性是大范畴的一个属性，相对于形状的大小而言。#455 的 Instance/Top/StoneCech/Refutations.v 将其转化为关于类型值 [Top] 和 [CompHaus] 的定理，其 Hom 位于它们的点之上，在所有位于 Hom 之上的形状宇宙中；这个文件对 Instance/Top/Prop.v 的 [PTopCat@{o so}] 运行同样的论证，其 Hom 位于点的宇宙 [o]，且其对象位于 [so] 之上，并将 #455 的形式从 [Top] 和 [CompHaus] 传递到高于点的每一个形状宇宙中。ZW9WZZ、ZW10WZZ 和 [ppoint_false] (Instance/Top/Subspace.v) 的两个点，通过在点 ([pbool_eval_pt]) 上的求值，可建构地区分。这里没有任何内容是公理：信息化排中律（[IEM]，Instance/Sets/Classifier/OneLevel.v）和空间的可判定相等性（[ObjDecEq]，Construction/Quotient.v）都是假设，并且在任意一个箭头指标存在的情况下（[canonical_ArrowIndex]，通过Instance/Top/StoneCech/Refutations.v的[ObjDecEq_of_IEM]）。名称。在这里以及在 Instance/Top/Cocomplete/Refutations.v 中的反驳，其余对偶的余极限，遵循相同的模式，双方相同：[_Freyd] 和 [_Cantor_] 命名论证，假设后缀命名可达性，而 [_below]（仅在极限端）标记 [Top] 或 [CompHaus] 上的一种形式，该形式可达低于同伦宇宙 [h]。[_Freyd] —— Freyd 从箭头指标（[ArrowIndex]）在形状（或指标）宇宙 [s] 的论证，其中指标是假设；没有任何东西将 [s] 与点的宇宙 [o] 绑定。[_ObjDecEq] —— 空间（[ObjDecEq]）的可判定等式，在每个 [s] 与 [o < s] 中，包括 [o := Set]。[_IEM]              信息排中（[IEM]），在每个 [s]  
 具有 [o < s] 的情况下，[o := Set] 被包含。[_IEM_canonical]     [IEM] 通过该类别自身对象的典范索引，未传输：每个 [s] 在对象宇宙之上或之上（[so] 对于 [PTopCat@{o so}]，  
 [h] 对于 [Top@{h o}]）。[_below_ObjDecEq]，[_below_IEM]（限制侧，超过[Top]和[CompHaus]）[_ObjDecEq]和[_IEM]的延伸（对于产品[o < s <= h]，在读取[@{s s s h h h}]时），这些形状严格位于这些点之间，并包含homs，与在[h <= s]处停止的同类形式区分开来：#455的[Top_not_complete_IEM]和[CompHaus_not_complete_IEM_below]，以及这里的[Top_iprod_refuted_IEM_canonical]。余极端侧没有在[h <= s]处停止的形式，其[Top]形式带有普通的后缀。[_Cantor_ObjDecEq]，[_Cantor_IEM]（仅极限侧）在相同假设下和相同范围内的康托尔论证，但[ObjDecEq]形式需要[Set < o]。《Instance/Top/StoneCech/Refutations.v》的[Top_not_complete]、[Top_not_complete_IEM]和[CompHaus_not_complete_IEM_below]（#455）早于该方案：第一个是[_Freyd]形式，第二个是[_IEM_canonical]形式，第三个的[_below]表示在对象宇宙[c]的[CompHaus]之下，在[h <= s]处；该文件的[CompHaus_not_complete_below_IEM]是达到下层同态宇宙的形式。这里是什么。这是 #1328 的第 4 项的 [PTopCat] 一半（重新运行 #455 对 Prop 值编码的反驳），用于极限，以及 #455 的 [Top] 和 [CompHaus] 形式在同态下的扩展。- [PTop_not_complete_Freyd]：给定 [PTopCat] 在形状宇宙 [s] 中的 [ArrowIndex]，ZW80WZZ 是假的。ZW81WZZ：在 [IEM] 下，每个具有 [so <= s] 的 [s]，在箭头集合上由 [canonical_ArrowIndex] 索引，它位于 [so]；ZW87WZZ 在下位包含它（其 [o < s] 来源于 [so <= s]），并且它保持未运输的形式。- [PTop_ArrowIndex_transport]：[PTopCat@{o so1}] 和 [PTopCat@{o so2}] 的对象和同态相同为 [PTop@{o}] 和 [PMor@{o}]，因此箭头索引在它们之间移动，其块中没有方程；通过它，[PTop_not_complete_ObjDecEq] 和 [PTop_not_complete_IEM] 在每一个严格高于点的形状宇宙中反驳完备性，[o < s]，规范索引在 [PTopCat@{o s}] 构建并传输。余极限对偶重复使用它。- [PTop_no_ArrowIndex_below]：构造上，在任何宇宙 [s <= o] 中，[PTopCat@{o so}] 的箭头索引都不存在，由 [PTop_not_complete_Freyd] 针对 Instance/Top/Complete.v 的 [PTop_Complete]；[PTop_no_ArrowIndex_at_points] 是它的情况 [s = o]，证明方法是针对书中路线 [PTop_Complete_via_products] 的替代方式。-  [PTop_iprod_refuted_IEM]：在 [IEM] 下，严格高于这些点的任意指数在任何宇宙 [s] 中的积被否定，无需涉及均衡器，而 Instance/Top/Complete.v 的 [PTop_HasIndexedProducts] 在每个指数宇宙 [o] 或以下构建它们。 -  [Top_iprod_refuted_IEM_canonical]：在 [IEM] 下，类型值 [Top@{h o}] 在其同构宇宙 [h]（也是其对象宇宙）或以上的任何指数宇宙 [s] 中没有 [HasIndexedProducts@{s s s s h h}]：规范指数、未传输。 -  [top_rebuild] 和 [Top_ArrowIndex_transport]：[Top@{h1 o}] 的连续映射被重建为 [Top@{h2 o}] 的连续映射，相同的点映射带有扩展连续性字段 eta，通过它箭头指数在两个同构宇宙之间移动；任一代码块都不携带方程（[About]）。η-展开就是保持这两个 hom 宇宙分离的原因。写作 [continuity := continuity f] 时，该字段未经展开直接传递，展开阶段将 [Continuous@{h1 o}] 与 [Continuous@{h2 o}] 的一阶统一，然后重建得到方程 [h1 = h2]（由 [About] 在绑定器 [@{o h1 h2 | o < h1, o < h2 +}] 下读取）；在 [@{o h1 h2 | o < h1, h1 < h2 +}] 下它被拒绝（“无法强制 h1 = h2，因为 h1 < h2”）。该方程是编码的产物，而不是障碍；Test/ProbeTopComplete458.v 将其标记为此类（N29），位于 [h1 < h2] 的 η-展开重建旁边，并被接受。- 通过运输，在 [Top@{s o}] : [Top_not_complete_below_ObjDecEq] 和 [Top_not_complete_below_IEM] 处建立的典范索引反驳 [Complete@{r s h h} Top@{h o}]，在每个 [s] 处与 [o < s]，位于这些点之间且包含同态的形状，第一个也在 [o := Set]；[Top_iprod_refuted_below_IEM] 在每个 [s] 处在 [IEM] 下与 [o < s <= h] 反驳 [HasIndexedProducts@{s s s h h h} Top@{h o}]。[HasIndexedProducts] 的第四个槽约束其第三个槽，这些陈述将索引宇宙放在 [s]，以及其第六个槽，即同态（[About] : [u1 <= u2] 和 [u4 <= u2]），因此这一读法包含 [s <= h] 和 [Top_iprod_refuted_IEM_canonical] 的读法 [@{s s s s h h}] 包含 [h <= s]；两者在 [s = h] 相交。[CompHaus_not_complete_below_IEM] 是 #455 的
 [CompHaus_ArrowIndex_of_Top] 应用于传输的索引：它
 在每个 [s] 下用 [o < s] 反驳 [Complete@{r s h c} CompHaus]，低于 [h] 包含，在 [CompHaus] 的实例中，
 Instance/Top/StoneCech/Refutations.v 的 COVERAGE 记录用于 [CompHaus_not_complete_IEM_below]（两个块一致，但该常量的 [h <= s] 不同，在这里是 [o < s]）。边界。《Instance/Top/Complete.v》: 在每个形状宇宙 [s <= o] 下，[PTopCat@{o so}] 的完整性是可以证明的（[PTop_Complete]，无假设），并且在 [IEM] 或 [ObjDecEq] 下，在每个 [s] 与 [o < s]（[PTop_not_complete_IEM]，[PTop_not_complete_ObjDecEq]）下被反驳。这两者之间没有形状宇宙；没有 [IEM]、[ObjDecEq] 或索引点之上的内容没有被反驳（未交付）。在 Instance/Top/Complete.v 的边界段的 scratch 文件中测量：两种反驳都在具有 [o < s] 的 [s] 和 [o := Set] 下被接受，而在 [Complete@{o o o so}] 上读取的 [PTop_not_complete_IEM] 被拒绝（“无法强制 <1> = o，因为 <1> < o”，生成的宇宙写为 <1>）。索引侧的尖锐性也是如此：在 [o] 或以下没有箭头索引，从建设上讲，而 [PTop_not_complete_ObjDecEq] 的证明在其上方的每个 [s] 上构建一个，从 [ObjDecEq] ([canonical_ArrowIndex] 在 [PTopCat@{o s}]，已转移)。在类型值 [Top@{h o}] 上，在 [IEM] 下或在 [ObjDecEq] 下，完整性被驳斥，在每个具有 [o < s] 的 [s] 上，而且在 [s <= o] 上，它既没有被构建也没有被驳斥。在 Test/ProbeTopComplete458.v 中测量：
 [Top_not_complete_below_IEM] 和 [CompHaus_not_complete_below_IEM] 在 [s] 上与 [o < s < h] 一起被接受，
 [Top_not_complete_below_ObjDecEq] 在 [o := Set] 上被接受；
 [Top_not_complete_below_IEM] 在 [s := o] 读取，
 [Top_iprod_refuted_below_IEM] 在索引宇宙 [o] 读取，每个由其宇宙实例执行，都被拒绝（"无法强制执行 o < o 因为 o = o"），并且 #455 的
 [Top_not_complete_IEM] 和
 [CompHaus_not_complete_IEM_below] 在 [s] 上与 [o < s < h] 读取时被拒绝（"无法强制 <3> = h 因为 <3> <= <2> < h"，生成的宇宙按消息中出现的顺序编号）。

 STRENGTHS。 每个定理都以 [False] 结束。 [PTop_ArrowIndex_transport] 和 [Top_ArrowIndex_transport] 是其解码法为 [≈] 的箭头数据，[top_rebuild] 是数据，而两个 [PTop_no_ArrowIndex_*] 是以 [False] 结束的 [:=] 项。没有证明以 [Defined] 结束。宇宙，由 [About] 在 [Set Printing Universes] 下阅读，标准库大写字母省略；[e] 的 [IEM] 水平，免费。PTop_not_complete_Freyd@{r s o so} :
 ArrowIndex@{s so o} PTopCat@{o so} → ¬ Complete@{r s o so}
 ( * o < so, s <= r, o <= r: 没有什么将 s 与 o 联系起来 * )
 PTop_not_complete_IEM_canonical@{e r s o so} :
 IEM@{e} → ¬ Complete@{r s o so}      ( * so <= s, o <= s * )
 PTop_not_complete_ObjDecEq@{r s o so} :
 ObjDecEq PTopCat@{o so} → ¬ Complete@{r s o so}   ( * o < s * )
 PTop_not_complete_IEM@{e r s o so} :
 IEM@{e} → ¬ Complete@{r s o so}      ( * o < s * )
 PTop_no_ArrowIndex_below@{s o so u} :
 ¬ ArrowIndex@{s so o} PTopCat@{o so}  ( * s <= o * )
 PTop_iprod_refuted_IEM@{e s o so} :
 IEM@{e} → ¬ HasIndexedProducts@{s s s s so o} PTopCat@{o so}
 ( * o < s * )
 Top_iprod_refuted_IEM_canonical@{e s h o} :
 IEM@{e} → ¬ HasIndexedProducts@{s s s s h h} Top@{h o}
 ( * o < h, h < * )= s * )
 top_rebuild@{o h1 h2} :
 ContinuousMorphism@{h1 o} X Y → ContinuousMorphism@{h2 o} X Y
 ( * o < h1, o < h2: 无等式 * )
 Top_ArrowIndex_transport@{s o h1 h2} :
 ArrowIndex@{s h1 h1} Top@{h1 o} → ArrowIndex@{s h2 h2} Top@{h2 o}
 ( * o < h1, o < h2: 无等式 * )
 Top_not_complete_below_ObjDecEq@{r s h o} :
 ObjDecEq Top@{h o} → ¬ Complete@{r s h h}   ( * o < h, o < s * )
 Top_not_complete_below_IEM@{e r s h o} :
 IEM@{e} → ¬ Complete@{r s h h}       ( * o < h, o < s * )
 Top_iprod_refuted_below_IEM@{e s h o} :
 IEM@{e} → ¬ HasIndexedProducts@{s s s h h h} Top@{h o}
 ( * o < h, o < s, s <= h * )
 CompHaus_not_complete_below_IEM@{e r s c h o …} :
 IEM@{e} → ¬ Complete@{r s h c}  ( * o < h, o < s, h <= c * )
 [CompHaus_not_complete_below_IEM]  包含另外七个宇宙，
 s许多 [CompHaus] 和 [Top] 是 #455 的 [CompHaus_not_complete] 和 [CompHaus_ArrowIndex_of_Top] 留下空闲的；它的块，标准库上限被省略，是 #455 的 [CompHaus_not_complete_IEM_below] 并将 [h <= s] 替换为 [o < s]，约束对约束。在 [About] 中，输出该文件所有 17 个常量（其 [Print Module] 列表；它不声明任何义务、记录或归纳）时，[Set] 出现在 10 个块中，并且仅作为 [PTopCat] 对象集合的严格下界：[Set < so] 出现在 9 个块中，[Set < s] 出现在三个跨越 [PTopCat] 的反驳中（[PTop_not_complete_ObjDecEq]、[PTop_not_complete_IEM]、[PTop_iprod_refuted_IEM]；它们在 [PTopCat@{o s}] 构建索引）以及 [Set < so1]、[Set < so2] 出现在 [PTop_ArrowIndex_transport] 中；在 [Top] 和 [CompHaus] 上的七个常量中，没有一个提到 [Set]，并且没有块包含方程。路线和成本。关闭 173 [Category.*] 模块，不包括此文件（[Print Libraries]）。实例/Top/StoneCech/Refutations.v，对于 [ObjDecEq_of_IEM]、[Top_not_complete]、[CompHaus_not_complete] 和 [CompHaus_ArrowIndex_of_Top] 是必需的，而不是重述它们，边际成本为 28（单独丢弃：145）；实例/Top/CompHaus.v，对于名称 [CompHaus] 是必需的，边际成本为零，因为第一次加载它；一起丢弃它们的成本为 31（142）。未交付。在没有索引，也没有 [IEM] 或 [ObjDecEq] 的点上方的驳斥：小的完全范畴的稀薄性在构造上是不可证的（Structure/Complete/Freyd.v 的头文件）。余极限侧（Instance/Top/Cocomplete/Refutations.v）。对于类型值 [Top]，在点上或以下的形状上的完备性 [s <= o]，既未构建也未被驳斥（Instance/Top/Complete.v 仅在 [PTopCat] 上构建它），它在索引宇宙上或以下的乘积也没有；[CompHaus] 在那里也没有完备性。该文件没有余极限侧康托尔论证的对应部分。
*)

(* * ** Evaluation at the point separates the two points of [PBool] / * ** 在该点的评估将[PBool]的两个点分开 *)

Definition pbool_eval_pt@{o so +| o < so +}
  (f : PPoint@{o} ~{PTopCat@{o so}}~> PBool@{o}) : bool :=
  pmap f ttt.

Lemma pbool_eval_pt_resp@{o so +| o < so +}
  (u v : PPoint@{o} ~{PTopCat@{o so}}~> PBool@{o}) :
  u ≈ v → pbool_eval_pt u = pbool_eval_pt v.
Proof. intro H. exact (H ttt). Qed.

(* * ** Freyd's core at an arbitrary arrow index / * ** Freyd 在任意箭头索引处的核心 *)

Theorem PTop_not_complete_Freyd@{r s o so +| o < so +}
  (AI : ArrowIndex@{s so o} PTopCat@{o so})
  (comp : @Complete@{r s o so} PTopCat@{o so}) : False.
Proof.
  exact (freyd_no_separated_pair AI (ppoint_true@{o}) (ppoint_false@{o}) _ _
           (complete_iprod comp (fun _ : ai_index AI => PBool@{o}))
           pbool_eval_pt pbool_eval_pt_resp eq_refl eq_refl).
Qed.

(* The canonical index of [PTopCat@{o so}] sits at [so]. / [PTopCat@{o so}] 的典型索引位于 [so]。 *)
Theorem PTop_not_complete_IEM_canonical@{e r s o so +| o < so +} (E : IEM@{e})
  (comp : @Complete@{r s o so} PTopCat@{o so}) : False.
Proof.
  exact (PTop_not_complete_Freyd
           (canonical_ArrowIndex (ObjDecEq_of_IEM E PTopCat@{o so})) comp).
Qed.

(*
 The objects and homs of [PTopCat@{o so1}] and [PTopCat@{o so2}] are the
 same [PTop@{o}] and [PMor@{o}], so an arrow index moves between them. 

 --------
 [PTopCat@{o so1}] 和 [PTopCat@{o so2}] 的对象和态射是相同的 [PTop@{o}] 和 [PMor@{o}]，因此箭头索引在它们之间移动。
*)
Definition PTop_ArrowIndex_transport@{s o so1 so2 +| o < so1, o < so2 +}
  (AI : ArrowIndex@{s so1 o} PTopCat@{o so1}) :
  ArrowIndex@{s so2 o} PTopCat@{o so2} :=
  @Build_ArrowIndex PTopCat@{o so2} (ai_index AI)
    (fun x y f => @ai_enc PTopCat@{o so1} AI x y f)
    (fun x y m d => @ai_dec PTopCat@{o so1} AI x y m d)
    (fun x y f d => @ai_dec_enc PTopCat@{o so1} AI x y f d).

(* Every shape universe strictly above the points: decidable equality of spaces, transported to the canonical index at [s]. / 每个形状宇宙严格位于点之上：空间的可判等性，被传输到 [s] 的规范索引。 *)
Theorem PTop_not_complete_ObjDecEq@{r s o so +| o < so, o < s +}
  (DO : ObjDecEq PTopCat@{o so})
  (comp : @Complete@{r s o so} PTopCat@{o so}) : False.
Proof.
  exact (PTop_not_complete_Freyd
           (PTop_ArrowIndex_transport@{s o s so}
              (canonical_ArrowIndex (DO : ObjDecEq PTopCat@{o s})))
           comp).
Qed.

Theorem PTop_not_complete_IEM@{e r s o so +| o < so, o < s +}
  (E : IEM@{e}) (comp : @Complete@{r s o so} PTopCat@{o so}) : False.
Proof.
  exact (PTop_not_complete_ObjDecEq (ObjDecEq_of_IEM E PTopCat@{o so}) comp).
Qed.

(* * ** No arrow index at or below the points, constructively / * ** 在这些点或以下没有箭头索引，具有建设性 *)

Definition PTop_no_ArrowIndex_at_points@{o so +| o < so +}
  (AI : ArrowIndex@{o so o} PTopCat@{o so}) : False :=
  PTop_not_complete_Freyd AI PTop_Complete_via_products.

Definition PTop_no_ArrowIndex_below@{s o so +| s <= o, o < so +}
  (AI : ArrowIndex@{s so o} PTopCat@{o so}) : False :=
  PTop_not_complete_Freyd AI PTop_Complete.

(** ** Products above the points / ** 超过积分的产品 *)

Theorem PTop_iprod_refuted_IEM@{e s o so +| o < so, o < s +}
  (E : IEM@{e})
  (HP : @HasIndexedProducts@{s s s s so o} PTopCat@{o so}) : False.
Proof.
  pose (AI := PTop_ArrowIndex_transport@{s o s so}
                (canonical_ArrowIndex
                   (ObjDecEq_of_IEM E PTopCat@{o so} : ObjDecEq PTopCat@{o s}))).
  exact (freyd_no_separated_pair AI (ppoint_true@{o}) (ppoint_false@{o}) _ _
           (@indexed_product_ump _ HP (ai_index AI) (fun _ => PBool@{o}))
           pbool_eval_pt pbool_eval_pt_resp eq_refl eq_refl).
Qed.

(* * ** The Type-valued [Top]: products at and above the hom universe / * ** 类型值 [Top]：同类宇宙及以上的乘积 *)

(*
 The canonical index of [Top@{h o}] sits at its object universe [h], and
 indexes at every [s] with [h <= s]. 

 --------
 [Top@{h o}] 的标准索引位于其对象宇宙 [h]，并在每个 [s] 上使用 [h <= s] 进行索引。
*)
Theorem Top_iprod_refuted_IEM_canonical@{e s h o +| o < h, h <= s +}
  (E : IEM@{e}) (HP : @HasIndexedProducts@{s s s s h h} Top@{h o}) : False.
Proof.
  pose (AI := canonical_ArrowIndex@{s h h} (ObjDecEq_of_IEM E Top@{h o})).
  exact (freyd_no_separated_pair AI
           (top_point Bool_Discrete true) (top_point Bool_Discrete false) _ _
           (@indexed_product_ump _ HP (ai_index AI) (fun _ => Bool_Discrete))
           (fun h => continuous_map h ttt) (fun u v H => H ttt)
           eq_refl eq_refl).
Qed.

(* * ** The Type-valued [Top]: an arrow index moves between hom universes / * ** 类型值 [Top]：箭头索引在同类宇宙之间移动 *)

(*
 A continuous map of [Top@{h1 o}] rebuilt as one of [Top@{h2 o}]: the
 same map of points, and the continuity field eta-expanded.  Written
 [continuity := continuity f] instead, the field is passed through
 unexpanded, elaboration unifies [Continuous@{h1 o}] with
 [Continuous@{h2 o}] first-order, and the block acquires [h1 = h2]; the
 eta-expanded field carries no equation. 

 --------
 将 [Top@{h1 o}] 的连续映射重建为 [Top@{h2 o}]：相同的点映射，以及连续性场的 eta 展开。改写为 [continuity := continuity f] 时，该场未展开直接传递，展开过程将 [Continuous@{h1 o}] 与 [Continuous@{h2 o}] 统一为一阶，并且该块获得 [h1 = h2]；eta 展开的场不携带方程。
*)
Definition top_rebuild@{o h1 h2 | o < h1, o < h2 +} {X Y : TopSpace@{o}}
  (f : ContinuousMorphism@{h1 o} X Y) : ContinuousMorphism@{h2 o} X Y :=
  {| continuous_map := continuous_map f;
     continuity := fun U HU => continuity f U HU |}.

(* The index never mentions a hom universe: encode and decode through the rebuild, both ways; the decoding law is pointwise. / 索引从未提到同质宇宙：通过重建进行编码和解码，双向进行；解码律是逐点的。 *)
Definition Top_ArrowIndex_transport@{s o h1 h2 | o < h1, o < h2 +}
  (AI : ArrowIndex@{s h1 h1} Top@{h1 o}) :
  ArrowIndex@{s h2 h2} Top@{h2 o} :=
  @Build_ArrowIndex Top@{h2 o} (ai_index AI)
    (fun x y f => @ai_enc Top@{h1 o} AI x y (top_rebuild@{o h2 h1} f))
    (fun x y m d => top_rebuild@{o h1 h2}
                      (@ai_dec Top@{h1 o} AI x y m (top_rebuild@{o h2 h1} d)))
    (fun x y f d z => @ai_dec_enc Top@{h1 o} AI x y (top_rebuild@{o h2 h1} f)
                        (top_rebuild@{o h2 h1} d) z).

(* Every shape universe strictly above the points, the shapes below the homs included: the canonical index is built at [Top@{s o}] and transported to [Top@{h o}]. / 每个形状宇宙严格位于这些点之上，下面的形状包含 hom：规范索引建立在 [Top@{s o}] 上并传输到 [Top@{h o}]。 *)
Theorem Top_not_complete_below_ObjDecEq@{r s h o +| o < h, o < s +}
  (DE : ObjDecEq Top@{h o}) (comp : @Complete@{r s h h} Top@{h o}) : False.
Proof.
  exact (Top_not_complete
           (Top_ArrowIndex_transport@{s o s h}
              (canonical_ArrowIndex (DE : ObjDecEq Top@{s o})))
           comp).
Qed.

Theorem Top_not_complete_below_IEM@{e r s h o +| o < h, o < s +}
  (E : IEM@{e}) (comp : @Complete@{r s h h} Top@{h o}) : False.
Proof.
  exact (Top_not_complete_below_ObjDecEq (ObjDecEq_of_IEM E Top@{h o}) comp).
Qed.

(* Products indexed strictly above the points and at or below the homs: the reading of [HasIndexedProducts] whose fourth slot is the hom universe. / 严格高于这些点且在homs或以下的产品： [HasIndexedProducts] 的读数，其第四个槽位是homs 宇宙。 *)
Theorem Top_iprod_refuted_below_IEM@{e s h o +| o < h, o < s, s <= h +}
  (E : IEM@{e}) (HP : @HasIndexedProducts@{s s s h h h} Top@{h o}) : False.
Proof.
  pose (AI := Top_ArrowIndex_transport@{s o s h}
                (canonical_ArrowIndex
                   (ObjDecEq_of_IEM E Top@{h o} : ObjDecEq Top@{s o}))).
  exact (freyd_no_separated_pair AI
           (top_point Bool_Discrete true) (top_point Bool_Discrete false) _ _
           (@indexed_product_ump _ HP (ai_index AI) (fun _ => Bool_Discrete))
           (fun h => continuous_map h ttt) (fun u v H => H ttt)
           eq_refl eq_refl).
Qed.

(* #455's [CompHaus_ArrowIndex_of_Top] after the transport: [Complete CompHaus] refuted under [IEM] at every shape universe strictly above the points, the shapes below the homs included. / #455 的 [CompHaus_ArrowIndex_of_Top] 在运输后：[Complete CompHaus] 在 [IEM] 下被驳斥，在每个形状宇宙中严格高于这些点，包括下面的 homs 形状。 *)
Theorem CompHaus_not_complete_below_IEM@{e r s c h o +| o < h, o < s +}
  (E : IEM@{e})
  (comp : @Complete@{r s h c} (CompHaus : Category@{c h h})) : False.
Proof.
  exact (CompHaus_not_complete
           (CompHaus_ArrowIndex_of_Top
              (Top_ArrowIndex_transport@{s o s h}
                 (canonical_ArrowIndex
                    (ObjDecEq_of_IEM E Top@{h o} : ObjDecEq Top@{s o}))))
           comp).
Qed.
