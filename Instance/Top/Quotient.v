Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Coequalizer.Wide.
Require Import Category.Instance.Parallel.Wide.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Subspace.TypeValued.

Generalizable All Variables.

(* * * Collapsing a subset to a point: X/A as a wide coequalizer in [Top] / * * 将一个子集塌缩为一点：X/A 作为 [Top] 中的宽共同等化子 *)

(*
 Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
 §V.9, book p. 134 (PDF p. 143), read from the page image: "Another
 coequalizer is the space X/A obtained from the space X by collapsing
 the subset A to a point.  It is the coequalizer [...] of the set of
 all the arrows sending the one point space * to one of the points
 a ∈ A.  It is used in homotopy theory." (catalog id
 maclane:V.9:construction5; the book numbers it not)
 nLab:      https://ncatlab.org/nlab/show/Top
 nLab:      https://ncatlab.org/nlab/show/quotient+space
 Wikipedia: https://en.wikipedia.org/wiki/Quotient_space_(topology)
 Book:      A. Hatcher, "Algebraic Topology", Cambridge University Press
 (2002), Chapter 0 (quotient spaces X/A, cones, suspensions,
 wedge and smash products)

 BACKGROUND.  Collapsing a subspace to a point is the basic gluing move
 of homotopy theory: Hatcher's Chapter 0 builds the cone, the
 suspension and the smash product X ∧ Y = (X × Y)/(X ∨ Y) with it.
 Wikipedia's quotient-space page lists X/A among its examples, with the
 2-sphere as the disc with its boundary collapsed, D²/∂D²; the nLab
 page on quotient spaces gives the quotient topology as the final
 topology induced by the projection.  Mac Lane places the construction
 in §V.9 among the colimits of Top, after the coequalizers and general
 colimits of catalog id maclane:V.9:remark2 (the book numbers no
 remarks) and that paragraph's open-cover example, and makes one
 categorical observation about it: X/A is a coequalizer, not of a
 parallel PAIR but of a whole parallel family of arrows * → X, one per
 point of A.  His §III.3 provides for that on book pp. 64-65 (PDF
 pp. 73-74), read from the page images.  He DEFINES the coequalizer of
 a pair elementarily, in display (6) of p. 64: an arrow u : b → e with
 uf = ug, through which every h : b → c with hf = hg factors uniquely.
 He then says that a coequalizer "can be interpreted as a universal
 arrow", and p. 65 reads it as one, "just a universal arrow from
 ⟨f, g⟩ to the functor Δ"; then "Coequalizers of any set of maps from
 a to b are defined in the same way."  For a set of maps a → b the two
 readings are Structure/Coequalizer/Wide.v's elementary record
 [IsWideCoequalizer], an arrow out of b alone, which is (6) extended
 and the reading that file's header adopts, and its colimit form
 [WideCoequalizer], a colimit over the shape that has a as a vertex.
 They agree on every nonempty set of maps.  At the empty set the
 colimit is the coproduct of a and b, and the elementary record pins
 down b itself (that file's header, which states the coproduct without
 formalizing it, and its [wide_coround_trip_needs_point]); the book
 does not treat that case.  Here a is * and b is X: read as the
 universal arrow, X/∅ is X ⊔ * (at [Top], Pairs.v's
 [pquot_wide_coequalizer_colimit_empty]); read elementarily, it is X.
 The header of Instance/Top/Cocomplete.v lists the collapse among the
 worked colimits of book p. 134 that it does not build; this file
 builds it, and Instance/Top/Quotient/Pairs.v the other half of the
 book's paragraph, the category of pairs and the adjunction.

 WHAT IS HERE.
 - The collapse along a FAMILY [p : I → X] of points, I at the points'
 universe.  [Top_collapse X I p] has the points of X, two of them
 identified when they are equal or when both lie in the image of
 [p] up to the points' equality ([collapse_image], the SATURATED
 image, so nothing is asked of [p]), with the quotient topology
 [TQuot] of Instance/Top/Subspace/TypeValued.v.  [Top_collapse_equiv]
 reads the points' equality back as [collapse_rel] at [eq_refl].
 [collapse_family X I p i] is the point-inclusion
 [top_point X (p i) : Point_Top ~> X], and
 [collapse_family_coequalizer] proves [X ~> X/A] an elementary
 [IsWideCoequalizer] of that family, over ARBITRARY spaces mapping
 out, for EVERY family, the empty one included; the mediator is the
 competing map itself on points ([collapse_desc_map_points], at
 [eq_refl]).
 - Mac Lane's subset form.  A subset is a Type-valued predicate
 [A : X → Type], indexed by its points [collapse_sub_points X A];
 [Top_collapse_sub X A] is X/A, [collapse_sub_family X A] the
 book's "set of all the arrows sending * to one of the points
 a ∈ A", and [collapse_coequalizer], the issue's pinned name,
 Construction 5 in the elementary form, for every subset.  The
 saturated image makes a properness hypothesis on [A] unnecessary
 here.  Pairs.v's pairs carry one by a design choice, a subset of a
 setoid being taken closed under the points' equality; that file's
 header names this saturation as the alternative.
 - The colimit form, the universal-arrow reading, at this file's apex,
 [collapse_family_colimit] and [collapse_colimit], takes a member of
 the family: it is Structure/Coequalizer/Wide.v's round trip
 [is_wide_coequalizer_colimit] from the elementary record, which
 takes one, and that file's [wide_coround_trip_needs_point] proves
 the member cannot be dropped from the round trip in general.  At
 this apex it cannot be dropped either: at ⟨∅, ∅⟩ no colimit's apex
 carries an elementary wide coequalizer of the family, which this
 file's X/∅ does (Pairs.v's [empty_colimit_not_elementary]).  The
 colimit itself needs no member: for every subset closed under the
 points' equality, the empty one included, it is Pairs.v's
 [pquot_wide_coequalizer_colimit], at the apex (X ⊔ {∗})/(A ∼ ∗).
 - At the empty subset the elementary X/∅ is X ([collapse_empty_iso],
 X/∅ ≅ X, through [wide_empty_id_IsWideCoequalizer]), an
 isomorphism, refused at [eq_refl] as an equation of spaces
 (Test/ProbeCollapse459.v's N9).  So at X = ∅ an elementary wide
 coequalizer of the empty family has no point at all, whatever its
 construction ([empty_wide_coequalizer_pointless]: the identity of
 the empty space descends along every one, and would carry a point
 of it into ∅).  [collapse_empty_pointless] is only a readback of
 [Empty_Top]'s carrier for this file's X/∅; a proof closes for every
 subset of ∅.  That is where the two readings of Mac Lane's
 coequalizer part.  Read as the universal arrow, his X/∅ is X ⊔ *,
 which has a point, and Pairs.v proves that coequalizer and
 Construction 6's X/A one space for every subset closed under the
 points' equality, so Constructions 5 and 6 agree at every A.  Read
 elementarily, X/∅ is X, and the two constructions part at A = ∅.
 - Small wide coequalizers of [Top].  [wcoeq_rel] is the relation a
 family of setoid maps generates (all the pairs (f_i a, f_j a)),
 the wide analogue of Instance/Sets/Coequalizer.v's [coeq_rel];
 [WSetsCoeq] is its quotient setoid; [twcoeq_obj] is [TQuot] on it,
 built directly as Instance/Top/Cocomplete/TypeValued.v builds
 [Top_HasCoequalizers]; and [Top_HasWideCoequalizers_small] is
 [HasWideCoequalizers] for [Top] at every index universe at or
 below the points', with its object read back at [eq_refl]
 ([Top_wide_coequalizer_obj]).  Before this file the tree had no
 inhabitant of [HasWideCoequalizers] (a word grep over the tree's
 .v files found the class only in its declaring file); that file's
 header carries a CORRECTION (#459).  [collapse_iso_generic] compares
 the direct collapse with the generic wide coequalizer of its family
 by [wide_coequalizer_unique]: the isomorphism is the identity on
 points in both directions ([collapse_iso_generic_to],
 [collapse_iso_generic_from], at [eq_refl]).
 - [collapse_proj_epic], from [wide_coequalizer_epic].

 THE WALLS, pinned in Test/ProbeCollapse459.v (its N1-N6), which
 carries this file's import list; each refusal was read in a copy of
 that WHOLE file with its one guarded command unguarded, each beside a
 positive control that is accepted; a universe the message generates is
 written <1>, <2>, numbered in order of first appearance.
 W-b.  [wcoeq_rel] over an index at [Type@{h}], read as a relation at
 [Type@{o}], is refused, "universe inconsistency: Cannot enforce
 o = <1> because o < h <= <2> <= <1>": the relation's index
 universe <2> sits at or below its points' universe <1>, so an index
 at [h] drags the relation above the points.  Control: the index at
 [o].  The mechanism is of the family that the header of
 Instance/Top/Cocomplete/TypeValued.v records as its W2 (a glue
 constructor quantifying over data at [h]); the two are not claimed
 to be one wall.
 W-a.  Not a wall of its own: the bound [i <= o] in the binder of
 [Top_HasWideCoequalizers_small] is W-b's, forced by the relation
 and inferred when a binder omits it.  The glue constructor
 [wcq_glue] quantifies over the index, so under the closed
 constraint list [@{i o|}] the relation is refused, "Universe
 constraints are not implied by the ones declared: i <= o", and so
 is the inductive itself declared there, while the same inductive
 without [wcq_glue] is accepted.  Read with its index at the hom
 universe the instance is refused accordingly, "Universe
 inconsistency. Cannot enforce h <= o because o < h".  Control: the
 reading at an index [i <= o].
 W-c.  [IsWideCoequalizer] is not cumulative, and the round trip
 [is_wide_coequalizer_colimit] needs the index at the hom universe
 (Structure/Coequalizer/Wide.v's header: [u0 = u1]).  Handing it the
 record read at index [o] is refused, "universe inconsistency:
 Cannot enforce o = h because o < h".  So the index universe of
 [collapse_family_coequalizer] and [collapse_coequalizer] is a
 binder of its own, [i] with [o <= i]: read at [@{o h h}] it feeds
 the round trip (the control, and [collapse_family_colimit]), read
 at [@{o h o}] it is Mac Lane's index, the points of A.
 Neither wall blocks Construction 5, whose index is the points of A, at
 [o].

 STRENGTHS.  At [eq_refl]: [Top_collapse_equiv],
 [collapse_desc_map_points], [Top_wide_coequalizer_obj],
 [collapse_iso_generic_to], [collapse_iso_generic_from].  Up to [≈]:
 the universal properties [collapse_desc] and [twcoeq_desc] and
 everything built from them.  Two [Defined], counted by token
 ([collapse_desc], [twcoeq_desc]), and both load-bearing: each closed
 [Qed] alone in a scratch copy of this file leaves an [eq_refl]
 readback refused, [collapse_iso_generic_to] ("cannot unify
 "collapse_iso_generic X I p x" and "x"") and [collapse_iso_generic_from]
 respectively.  Of the nine [Qed], counted by token in the code, seven
 are the equivalence, respect and cofork lemmas, one is the readback
 [collapse_empty_pointless] and one the refutation
 [empty_wide_coequalizer_pointless].

 UNIVERSES, read by [About] under [Set Printing Universes] on all 54
 constants of this file's [Print Module] listing (the inductive, its
 four constructors and four generated schemes included).
 - [collapse_image], [collapse_rel], [collapse_setoid],
 [collapse_carrier], [collapse_q], [Top_collapse],
 [collapse_sub_points], [collapse_sub_incl], [Top_collapse_sub]:
 [@{o}], with no constraint beyond stdlib caps (the pair-projection
 caps [TQuot] carries); X/A is a [TopSpace@{o}], an object of the
 same [Top@{h o}] as X.
 - The maps and their universal properties ([collapse_proj],
 [collapse_family], [collapse_wcofork], [collapse_med],
 [collapse_desc], [collapse_family_colimit], [collapse_proj_epic],
 [collapse_sub_proj], [collapse_sub_family], [collapse_colimit]):
 [@{o h}] with [o < h], [Top]'s own bound, and stdlib caps.
 [collapse_family_coequalizer] and
 [collapse_coequalizer]: [@{o h i}] with [o < h] and [o <= i], at
 [IsWideCoequalizer@{i h h}]; so is
 [empty_wide_coequalizer_pointless].
 - [collapse_iso_generic] and [collapse_empty_iso]: [@{o h u}] with
 [o < h] and [h < u], where [u] is not in the statement: it is
 [wide_coequalizer_unique]'s own binder [u2], bounded in that
 lemma's block by [u0 < u2] with [u0] the hom universe.  With [u]
 dropped from the binder each body is refused ("Universe <1> ... is
 unbound"; Test/ProbeCollapse459.v's N7 and N8).
 - [wcoeq_rel], its constructors and the setoid constants over it:
 [@{i o}] with [i <= o] (the generated schemes name their own
 binders: [wcoeq_rel_rect@{u u0 u1}], [wcoeq_rel_ind@{u u0}] and
 [wcoeq_rel_sind@{u u0}] carry [u <= u0], and
 [wcoeq_rel_rec@{u u0}] has an empty block, its statement being at
 [wcoeq_rel@{u u}]); [twcoeq_obj] through
 [Top_HasWideCoequalizers_small]:
 [@{i o h}] with [i <= o] and [o < h], the instance at
 [HasWideCoequalizers@{i h h} Top@{h o}].
 - [collapse_empty_pointless@{o}] and
 [empty_wide_coequalizer_pointless] carry the file's only STRICT
 stdlib cap, [o < False_rect.u0], which is [Empty_Top]'s own (its
 About: [u < False_rect.u0]).
 - No block carries an equation.  A word count of [Set] over the
 [About] output of the 54 constants reads 1: the sort of the motive
 of the generated scheme [wcoeq_rel_rec], not a universe bound.

 NOT DELIVERED.  Wide coequalizers of [Top] indexed above the points'
 universe (walled by W-b, not refuted); an instance of
 [HasWideCoequalizers] for [Sets], though [WSetsCoeq] is the setoid
 quotient it would need; the colimit form without a member of the
 family, for a family other than the point-inclusions of a subset
 closed under the points' equality (for those it is Pairs.v's
 [pquot_wide_coequalizer_colimit]); a comparison of the wide
 coequalizer at a two-element index with
 Instance/Top/Cocomplete/TypeValued.v's binary [Top_HasCoequalizers];
 X/A as a POINTED space, which is Instance/Top/Quotient/Pairs.v's; and
 any of the homotopy theory the construction serves (cones,
 suspensions, smash products, relative homology). 

 --------
 Mac Lane，《为工作中的数学家准备的范畴论》，第二版（GTM 5），§V.9，第134页（PDF第143页），从页面图像阅读："另一个余等化是通过将子集A塌缩为一点而从空间X得到的空间X/A。它是集合中所有将一个点空间*映射到A中某个点a的箭头的余等化[...]。它在同伦论中有应用。"（目录ID maclane:V.9:construction5；书中未编号）
 nLab: https://ncatlab.org/nlab/show/Top
 nLab: https://ncatlab.org/nlab/show/quotient+space
 Wikipedia: https://en.wikipedia.org/wiki/Quotient_space_(topology)
 书籍：A. Hatcher，《代数拓扑》，剑桥大学出版社（2002），第0章（商空间X/A、锥、悬吊、楔积和 smash 积）背景。将一个子空间塌缩为一个点是同伦论的基本粘合操作：Hatcher 的第 0 章用它构建了锥、悬挂和 smash 积 X ∧ Y = (X × Y)/(X ∨ Y)。维基百科的商空间页面将 X/A 列为例子之一，其中 2-球被视为将边界塌缩后的圆盘 D²/∂D²；nLab 关于商空间的页面将商拓扑给出为投影所诱导的最终拓扑。Mac Lane 将该构造放在 §V.9，列于 Top 的余等化器和一般余极限之后，并在该段的开覆盖例子中提出了一个范畴论上的观察：X/A 是一个余等化器，不是一个平行对，而是一个由每个 A 中的点对应的箭头 * → X 构成的整个平行族的余等化器。他的§III.3条款规定在书本第64-65页（PDF第73-74页）上，从页面图像中阅读。他在第64页的（6）式中对一对元素的共轭化器进行了基本定义：一个箭头 u : b → e，满足 uf = ug，通过它，每个 h : b → c（满足 hf = hg）都能唯一分解。然后他说，共轭化器“可以被解释为一个通用箭头”，第65页上也将其解读为通用箭头，“只是从⟨f, g⟩到函子Δ的一个通用箭头”；接着“从 a 到 b 的任意映射集的共轭化器也以相同方式定义。”对于从 a → b 的映射集，两个解读是 Structure/Coequalizer/Wide.v 的基本记录 [IsWideCoequalizer]，一个仅从 b 指出的箭头，这是（6）的扩展以及该文件头部采用的解读，其余极形式为 [WideCoequalizer]，是一个在 a 为顶点的形状上的余极。它们在每个非空映射集上一致。在空集处，余极限是 a 和 b 的余积，而基本记录固定了 b 本身（该文件的头部，它声明了余积但没有形式化，以及它的 [wide_coround_trip_needs_point]）；书中没有处理这种情况。这里 a 是 *，b 是 X：读作通用箭头，X/∅ 是 X ⊔ *（在 [Top]，Pairs.v 的 [pquot_wide_coequalizer_colimit_empty]）；从基本角度读，它是 X。Instance/Top/Cocomplete.v 的头部列出了书第 134 页中未构建的已处理余极限之间的塌缩；该文件构建了它，而 Instance/Top/Quotient/Pairs.v 构建了书中段落的另一半，即对的范畴及其伴随关系。这里是什么。- 沿着一个 FAMILIY [p : I → X] 的点的塌陷，我在点宇宙中的点。[Top_collapse X I p] 拥有 X 的点，其中两个在它们相等时或者当它们都位于 [p] 的像中时被识别，直到点的相等（[collapse_image]，饱和像，所以 [p] 没有要求），具有 Instance/Top/Subspace/TypeValued.v 的商拓扑 [TQuot]。[Top_collapse_equiv] 将点的相等读取回来作为 [collapse_rel] 在 [eq_refl]。[collapse_family X I p i] 是点包含 [top_point X (p i) : Point_Top ~> X]，并且 [collapse_family_coequalizer] 证明 [X ~> X/A] 是该族的一个基本 [IsWideCoequalizer]，映射出任意空间，对于每个族，包括空族；中介者是在点上的竞争映射本身（[collapse_desc_map_points]，在 [eq_refl]）。- Mac Lane 的子集形式。一个子集是一个类型值谓词 [A : X → Type]，由其点 [collapse_sub_points X A] 索引；[Top_collapse_sub X A] 是 X/A，[collapse_sub_family X A] 是书中“将 * 发送到点 a ∈ A 的所有箭头的集合”，而 [collapse_coequalizer] 是该问题的固定名称，构造 5 在初等形式下，对每个子集都适用。饱和像使得这里对 [A] 的适当性假设变得不必要。Pairs.v 中的对通过设计选择携带一个，一个 setoid 的子集在点的等价性下取闭包；该文件的头部将这种饱和命名为替代方案。- 在这个文件的顶点处，余极限形式，即通用箭头读法，[collapse_family_colimit] 和 [collapse_colimit] 接受一个族的成员：它是 Structure/Coequalizer/Wide.v 的循环回程 [is_wide_coequalizer_colimit]，从基本记录出发，它只接受一个，并且该文件的 [wide_coround_trip_needs_point] 证明该成员在一般情况下不能从循环回程中删除。在这个顶点处也不能删除它：在 ⟨∅, ∅⟩ 处，没有任何余极限的顶点携带该族的基本宽共等化子，而这个文件的 X/∅ 做到了（Pairs.v 的 [empty_colimit_not_elementary]）。余极限本身不需要成员：对于每一个在点的相等性下封闭的子集，包括空集，它就是 Pairs.v 的 [pquot_wide_coequalizer_colimit]，在顶点 (X ⊔ {∗})/(A ∼ ∗) 处。- 在空子集上，基本的 X/∅ 是 X（[collapse_empty_iso]，X/∅ ≅ X，通过 [wide_empty_id_IsWideCoequalizer]），是一个同构，在 [eq_refl] 处被拒绝作为空间的等式（Test/ProbeCollapse459.v 的 N9）。因此，在 X = ∅ 时，一个空族的基本广义余等化器根本没有点，无论它如何构造（[empty_wide_coequalizer_pointless]：空空间的恒等映射沿每个映射下降，并会将其中的一个点映射到 ∅）。[collapse_empty_pointless] 只是本文件中 X/∅ 的 [Empty_Top] 携带者的一个回读；一个证明对 ∅ 的每个子集都成立。这就是 Mac Lane 的余等化器部分的两种解读之所在。作为通用箭头来读，他的 X/∅ 是 X ⊔ *，它有一个点，而 Pairs.v 证明了 coequalizer 和构造 6 的 X/A 为每个在点的等式下封闭的子集提供了一个空间，因此构造 5 和 6 在每个 A 上都一致。从基本上理解，X/∅ 是 X，而且这两种构造在 A = ∅ 时分开。— [Top] 的小宽 coequalizer。[wcoeq_rel] 是一族集合等价映射生成的关系（所有的对 (f_i a, f_j a)），是 Instance/Sets/Coequalizer.v 中 [coeq_rel] 的广义类比；[WSetsCoeq] 是其商集合等价；[twcoeq_obj] 是它上的 [TQuot]，直接构建方式如 Instance/Top/Cocomplete/TypeValued.v 构建 [Top_HasCoequalizers]；而 [Top_HasWideCoequalizers_small] 是 [HasWideCoequalizers] 对于 [Top] 在每个指数宇宙（小于或等于这些点）处的值，并且其对象在 [eq_refl]（[Top_wide_coequalizer_obj]）中读取。在此文件之前，这棵树没有 [HasWideCoequalizers] 的元素（在树的 .v 文件中进行单词搜索发现该类只出现在其声明文件中）；该文件的头部包含一个更正（#459）。[collapse_iso_generic] 比较了直接塌缩与其族的通用宽协同化子通过 [wide_coequalizer_unique]：这个同构在两个方向上对点都是恒等的（[collapse_iso_generic_to]，[collapse_iso_generic_from]，在 [eq_refl]）。- [collapse_proj_epic]，来自 [wide_coequalizer_epic]。这些墙体，在 Test/ProbeCollapse459.v 文件中固定（其 N1-N6），承载了此文件的导入列表；每个拒绝都在该整个文件的副本中读取，其中一个受保护的命令被取消保护，每个都在一个被接受的阳性对照旁边；消息生成的宇宙被记录为 <1>、<2>，按首次出现顺序编号。W-b. [wcoeq_rel] 在 [Type@{h}] 的索引上读取，作为 [Type@{o}] 的关系被拒绝，“宇宙不一致：无法强制执行 o = <1> 因为 o < h <= <2> <= <1>”：该关系的索引宇宙 <2> 位于其点的宇宙 <1> 处或以下，因此 [h] 的索引会将关系提升到点之上。控制：[o] 的索引。该机制属于这样一个家族：Instance/Top/Cocomplete/TypeValued.v 的头部将其记录为 W2（一个在 [h] 上量化数据的粘合构造器）；两者并未声称是同一堵墙。W-a。不是它自己的墙：绑定器 [Top_HasWideCoequalizers_small] 中的绑定 [i <= o] 属于 W-b，由此关系强制，并在绑定器省略它时推断出来。粘合构造器 [wcq_glue] 对索引进行量化，因此在闭合约束列表 [@{i o|}] 下，该关系被拒绝，“宇宙约束不会由已声明的约束推出：i <= o”，因此在那里声明的归纳类型本身也被拒绝，而相同的归纳类型在没有 [wcq_glue] 时则被接受。在同伦宇宙中以其索引读取时，该实例相应地被拒绝，“宇宙不一致。”无法强制执行 h <= o 因为 o < h。索引 [i <= o] 的读取 W-c.[IsWideCoequalizer] 不是累积的，而往返 [is_wide_coequalizer_colimit] 需要同一 universe 的索引（Structure/Coequalizer/Wide.v 的头部：[u0 = u1]）。将索引 [o] 处读取的记录交给它会被拒绝，提示“universe 不一致：无法强制执行 o = h 因为 o < h”。因此 [collapse_family_coequalizer] 和 [collapse_coequalizer] 的索引 universe 是其自身的一个绑定器 [i]，带 [o <= i]：在 [@{o h h}] 处读取它为往返提供输入（控制及 [collapse_family_colimit]），在 [@{o h o}] 处读取它是 Mac Lane 的索引，即 A 的点。没有任何屏障阻止 Construction 5，其索引是 A 的点，在 [o]。优势。在 [eq_refl]：[Top_collapse_equiv]，[collapse_desc_map_points]，[Top_wide_coequalizer_obj]，[collapse_iso_generic_to]，[collapse_iso_generic_from]。最多到 [≈]：通用性质 [collapse_desc] 和 [twcoeq_desc] 以及由它们构建的一切。两个 [Defined]，按标记计数（[collapse_desc]，[twcoeq_desc]），并且都能承重：每个闭合的 [Qed] 单独在此文件的一个草稿副本中会导致 [eq_refl] 读回被拒绝，[collapse_iso_generic_to]（"无法统一 'collapse_iso_generic X I p x' 和 'x'"）和 [collapse_iso_generic_from] 分别如此。在代码中按标记计数的九个 [Qed] 中，有七个是等价性、尊重性和共分叉引理，一个是读回 [collapse_empty_pointless]，一个是反证 [empty_wide_coequalizer_pointless]。UNIVERSES，由 [About] 在 [Set Printing Universes] 下读取，涵盖此文件 [Print Module] 列表中的所有 54 个常量（包括归纳类型、其四个构造函数和四个生成的方案）。- [collapse_image]、[collapse_rel]、[collapse_setoid]、[collapse_carrier]、[collapse_q]、[Top_collapse]、[collapse_sub_points]、[collapse_sub_incl]、[Top_collapse_sub]：[@{o}]，仅受 stdlib 限制（[TQuot] 承载的对投影限制）；X/A 是 [TopSpace@{o}]，是与 X 相同 [Top@{h o}] 的对象。- 映射及其泛性质（[collapse_proj]、[collapse_family]、[collapse_wcofork]、[collapse_med]、[collapse_desc]、[collapse_family_colimit]、[collapse_proj_epic]、[collapse_sub_proj]、[collapse_sub_family]、[collapse_colimit]）：[@{o h}] 具有 [o < h]、[Top] 自身的界限，以及 stdlib 限制。[collapse_family_coequalizer] 和 [collapse_coequalizer]：[@{o h i}] 与 [o < h] 和 [o <= i]，在 [IsWideCoequalizer@{i h h}]；[empty_wide_coequalizer_pointless] 也是如此。- [collapse_iso_generic] 和 [collapse_empty_iso]：[@{o h u}] 与 [o < h] 和 [h < u]，其中 [u] 不在该语句中：它是 [wide_coequalizer_unique] 自己的绑定器 [u2]，在该引理的块中由 [u0 < u2] 与 [u0]（同类宇宙）绑定。移除绑定器中的 [u] 后，每个主体都被拒绝（“宇宙 <1> ... 未绑定”；Test/ProbeCollapse459.v 的 N7 和 N8）。- [wcoeq_rel]，它的构造函数以及在其上的等价类常量：[@{i o}] 以及 [i <= o]（生成的方案命名了它们自己 的绑定器：[wcoeq_rel_rect@{u u0 u1}]、[wcoeq_rel_ind@{u u0}] 和 [wcoeq_rel_sind@{u u0}] 携带 [u <= u0]，并且 [wcoeq_rel_rec@{u u0}] 有一个空块，其语句位于 [wcoeq_rel@{u u}]）；[twcoeq_obj] 到 [Top_HasWideCoequalizers_small]：[@{i o h}] 以及 [i <= o] 和 [o < h] 的实例位于 [HasWideCoequalizers@{i h h} Top@{h o}]。- [collapse_empty_pointless@{o}] 和 [empty_wide_coequalizer_pointless] 携带文件中唯一的 STRICT 标准库 cap，[o < False_rect.u0]，它是 [Empty_Top] 自己的（关于：[u < False_rect.u0]）。- 没有块携带方程。在 54 个常量的 [About] 输出上进行 [Set] 的字数统计为 1：生成的方案 [wcoeq_rel_rec] 的动机的类型，而不是一个宇宙绑定。未交付。上述点的宇宙中索引的 [Top] 的广义共同等化器（由 W-b 围住，未被反驳）；[Sets] 的 [HasWideCoequalizers] 实例，虽然 [WSetsCoeq] 是它所需要的集合等价类；没有家族成员的余极限形式，对于除了闭合于点相等的子集的点包含的家族以外的家族（对于那些是 Pairs.v 的 [pquot_wide_coequalizer_colimit]）；具有两元素索引的广义共同等化器与 Instance/Top/Cocomplete/TypeValued.v 的二元 [Top_HasCoequalizers] 的比较；作为一个带点空间的 X/A，这是 Instance/Top/Quotient/Pairs.v 的；以及它所服务的任何同伦理论构造（锥体、悬挂、锤积、相对同调）。
*)

#[local] Obligation Tactic := idtac.

(* * ** Small wide coequalizers of the Type-valued [Top] / * ** 类型值 [Top] 的小型广义余等化子 *)

(*
 The relation a family of setoid maps generates: the wide analogue of
 Instance/Sets/Coequalizer.v's [coeq_rel]. 

 --------
 一族集合等价映射生成的关系：Instance/Sets/Coequalizer.v 中 [coeq_rel] 的广义对应。
*)
Inductive wcoeq_rel@{i o} {I : Type@{i}} {A B : SetoidObject@{o o}}
  (fs : I → SetoidMorphism@{o o o} A B) : B → B → Type@{o} :=
  | wcq_base  : ∀ b1 b2 : B, b1 ≈ b2 → wcoeq_rel b1 b2
  | wcq_glue  : ∀ (i j : I) (a : A), wcoeq_rel (fs i a) (fs j a)
  | wcq_sym   : ∀ b1 b2 : B, wcoeq_rel b1 b2 → wcoeq_rel b2 b1
  | wcq_trans : ∀ b1 b2 b3 : B,
      wcoeq_rel b1 b2 → wcoeq_rel b2 b3 → wcoeq_rel b1 b3.

Lemma wcoeq_rel_Equivalence@{i o} {I : Type@{i}} {A B : SetoidObject@{o o}}
  (fs : I → SetoidMorphism@{o o o} A B) : Equivalence (wcoeq_rel@{i o} fs).
Proof.
  constructor.
  - intro b; apply wcq_base; reflexivity.
  - intros b1 b2 H; exact (wcq_sym _ _ _ H).
  - intros b1 b2 b3 H1 H2; exact (wcq_trans _ _ _ _ H1 H2).
Qed.

(* The quotient setoid: the points of [B] under the generated relation. / 商集群：在生成关系下 [B] 的点。 *)
Definition WSetsCoeq@{i o} {I : Type@{i}} {A B : SetoidObject@{o o}}
  (fs : I → SetoidMorphism@{o o o} A B) : SetoidObject@{o o} := {|
  carrier := carrier B;
  is_setoid := {| equiv := wcoeq_rel@{i o} fs;
                  setoid_equiv := wcoeq_rel_Equivalence@{i o} fs |}
|}.

Definition wsets_coeq_proj@{i o} {I : Type@{i}} {A B : SetoidObject@{o o}}
  (fs : I → SetoidMorphism@{o o o} A B) :
  SetoidMorphism@{o o o} B (WSetsCoeq@{i o} fs) :=
  @Build_SetoidMorphism _ (is_setoid B) _ (is_setoid (WSetsCoeq@{i o} fs))
    (fun b => b) (fun b1 b2 (e : b1 ≈ b2) => wcq_base fs b1 b2 e).

(* A map absorbing the family respects the generated relation. / 一个映射吸收家庭尊重所产生的关系。 *)
Lemma wcoeq_rel_of_cofork@{i o} {I : Type@{i}} {A B Z : SetoidObject@{o o}}
  (fs : I → SetoidMorphism@{o o o} A B) (k : SetoidMorphism@{o o o} B Z)
  (Hk : ∀ i j a, k (fs i a) ≈ k (fs j a)) :
  ∀ b1 b2, wcoeq_rel@{i o} fs b1 b2 → k b1 ≈ k b2.
Proof.
  intros b1 b2 H; induction H.
  - apply proper_morphism; assumption.
  - apply Hk.
  - symmetry; assumption.
  - transitivity (k b2); assumption.
Qed.

Section TWide.

Universes i o h.
Constraint i <= o, o < h.

Context {I : Type@{i}} {x y : Top@{h o}} (fs : I → x ~{Top@{h o}}~> y).

Definition twcoeq_obj : TopSpace@{o} :=
  TQuot y (WSetsCoeq@{i o} (fun i => continuous_map (fs i)))
    (wsets_coeq_proj@{i o} (fun i => continuous_map (fs i))).

Definition twcoeq_proj : y ~{Top@{h o}}~> twcoeq_obj := tquot_proj y _ _.

Lemma twcoeq_cofork (i j : I) : twcoeq_proj ∘ fs i ≈ twcoeq_proj ∘ fs j.
Proof. intro a; simpl. exact (wcq_glue _ i j a). Qed.

Definition twcoeq_med {z : Top@{h o}} (k : y ~{Top@{h o}}~> z)
  (Hk : ∀ i j : I, k ∘ fs i ≈ k ∘ fs j) :
  SetoidMorphism@{o o o} (WSetsCoeq@{i o} (fun i => continuous_map (fs i)))
    (top_carrier z) :=
  @Build_SetoidMorphism _
    (is_setoid (WSetsCoeq@{i o} (fun i => continuous_map (fs i))))
    _ (is_setoid (top_carrier z)) (continuous_map k)
    (wcoeq_rel_of_cofork@{i o} _ (continuous_map k) (fun i j a => Hk i j a)).

Definition twcoeq_desc {z : Top@{h o}} (k : y ~{Top@{h o}}~> z)
  (Hk : ∀ i j : I, k ∘ fs i ≈ k ∘ fs j) :
  ∃! u : twcoeq_obj ~{Top@{h o}}~> z, u ∘ twcoeq_proj ≈ k.
Proof.
  unshelve eapply Build_Unique.
  - exact (tquot_desc y _ _ z k (twcoeq_med k Hk) (fun b => reflexivity _)).
  - intro b; reflexivity.
  - intros v Hv b. simpl. symmetry. exact (Hv b).
Defined.

Definition twcoeq_IsWideCoequalizer :
  IsWideCoequalizer (C := Top@{h o}) fs twcoeq_obj twcoeq_proj :=
  @Build_IsWideCoequalizer Top@{h o} I x y fs twcoeq_obj twcoeq_proj
    twcoeq_cofork (fun z k Hk => twcoeq_desc k Hk).

End TWide.

Definition Top_HasWideCoequalizers_small@{i o h | i <= o, o < h +} :
  HasWideCoequalizers@{i h h} Top@{h o} :=
  {| wide_coeq := fun I x y fs =>
       (twcoeq_obj@{i o h} fs; (twcoeq_proj@{i o h} fs;
          twcoeq_IsWideCoequalizer@{i o h} fs)) |}.

Example Top_wide_coequalizer_obj@{i o h | i <= o, o < h +}
  {I : Type@{i}} {x y : Top@{h o}} (fs : I → x ~{Top@{h o}}~> y) :
  `1 (@wide_coeq Top@{h o} Top_HasWideCoequalizers_small@{i o h} I x y fs)
    = TQuot y (WSetsCoeq@{i o} (fun i => continuous_map (fs i)))
        (wsets_coeq_proj@{i o} (fun i => continuous_map (fs i))) := eq_refl.

(* * ** Construction 5: collapsing the image of a family of points / * ** 构造 5：塌缩一族点的图像 *)

(*
 [x] lies in the image of [p], up to the points' equality: the saturated
 image, so no properness hypothesis on the family is needed. 

 --------
 [x] 位于 [p] 的像中，直到点的相等：饱和的像，所以不需要对族作出适当性的假设。
*)
Definition collapse_image@{o} (X : TopSpace@{o}) (I : Type@{o}) (p : I → X)
  (x : X) : Type@{o} := { i : I & p i ≈ x }.

Lemma collapse_image_respects@{o} (X : TopSpace@{o}) (I : Type@{o})
  (p : I → X) (x x' : X) :
  x ≈ x' → collapse_image X I p x → collapse_image X I p x'.
Proof. intros e [i ei]. exists i. exact (transitivity ei e). Qed.

(* Two points are identified when they are equal, or when both lie in the image. / 当两点相等，或当它们都位于像中时，就会确定这两点。 *)
Definition collapse_rel@{o} (X : TopSpace@{o}) (I : Type@{o}) (p : I → X)
  (x x' : X) : Type@{o} :=
  ((x ≈ x') + (collapse_image X I p x * collapse_image X I p x'))%type.

Lemma collapse_rel_Equivalence@{o} (X : TopSpace@{o}) (I : Type@{o})
  (p : I → X) : Equivalence (collapse_rel X I p).
Proof.
  constructor.
  - intro x; left; reflexivity.
  - intros x y [e|[a b]].
    + left; symmetry; exact e.
    + right; exact (b, a).
  - intros x y z [e1|[a1 b1]] [e2|[a2 b2]].
    + left; transitivity y; assumption.
    + right; exact (collapse_image_respects X I p y x (symmetry e1) a2, b2).
    + right; exact (a1, collapse_image_respects X I p y z e2 b1).
    + right; exact (a1, b2).
Qed.

Definition collapse_setoid@{o} (X : TopSpace@{o}) (I : Type@{o}) (p : I → X) :
  Setoid@{o o} (carrier (top_carrier X)) := {|
  equiv := collapse_rel X I p;
  setoid_equiv := collapse_rel_Equivalence X I p
|}.

Definition collapse_carrier@{o} (X : TopSpace@{o}) (I : Type@{o})
  (p : I → X) : SetoidObject@{o o} := {|
  carrier := carrier (top_carrier X);
  is_setoid := collapse_setoid X I p
|}.

(* The instances are named: the collapsed carrier has the same underlying type as [X], and resolution would otherwise pick [X]'s equality. / 这些实例被命名为：塌缩的载体具有与 [X] 相同的底层类型，否则解析将选择 [X] 的相等性。 *)
Definition collapse_q@{o} (X : TopSpace@{o}) (I : Type@{o}) (p : I → X) :
  SetoidMorphism@{o o o} (top_carrier X) (collapse_carrier X I p) :=
  @Build_SetoidMorphism _ (is_setoid (top_carrier X)) _ (collapse_setoid X I p)
    (fun x => x) (fun x x' (e : x ≈ x') => (inl e : collapse_rel X I p x x')).

(* X/A: the quotient topology of Instance/Top/Subspace/TypeValued.v. / X/A：Instance/Top/Subspace/TypeValued.v 的商拓扑。 *)
Definition Top_collapse@{o} (X : TopSpace@{o}) (I : Type@{o}) (p : I → X) :
  TopSpace@{o} := TQuot X (collapse_carrier X I p) (collapse_q X I p).

(* The points of X/A are those of X, and their equality IS [collapse_rel]. / X/A 的点就是 X 的点，并且它们的相等是 [collapse_rel]。 *)
Example Top_collapse_equiv@{o} (X : TopSpace@{o}) (I : Type@{o}) (p : I → X)
  (x y : X) :
  @equiv _ (is_setoid (top_carrier (Top_collapse X I p))) x y
    = collapse_rel X I p x y := eq_refl.

Definition collapse_proj@{o h | o < h +} (X : TopSpace@{o}) (I : Type@{o})
  (p : I → X) : X ~{Top@{h o}}~> Top_collapse X I p :=
  tquot_proj X (collapse_carrier X I p) (collapse_q X I p).

(* The family of point-inclusions [* ~> X], one for each index. / 点内包含族 [* ~> X]，每个索引一个。 *)
Definition collapse_family@{o h | o < h +} (X : TopSpace@{o}) (I : Type@{o})
  (p : I → X) (i : I) : Point_Top@{o} ~{Top@{h o}}~> X :=
  top_point@{h o} X (p i).

Lemma collapse_wcofork@{o h | o < h +} (X : TopSpace@{o}) (I : Type@{o})
  (p : I → X) (i j : I) :
  collapse_proj X I p ∘ collapse_family X I p i
    ≈ collapse_proj X I p ∘ collapse_family X I p j.
Proof.
  intro t; simpl.
  right; split.
  - exists i. reflexivity.
  - exists j. reflexivity.
Qed.

Lemma collapse_med_proper@{o h | o < h +} (X : TopSpace@{o}) (I : Type@{o})
  (p : I → X) {Z : Top@{h o}} (k : X ~{Top@{h o}}~> Z)
  (Hk : ∀ i j : I, k ∘ collapse_family X I p i ≈ k ∘ collapse_family X I p j) :
  Proper (respectful (collapse_rel X I p) equiv) (continuous_map k).
Proof.
  intros x x' [e|[[i ei] [j ej]]].
  - exact (proper_morphism (continuous_map k) x x' e).
  - transitivity (continuous_map k (p i)).
    + symmetry; exact (proper_morphism (continuous_map k) _ _ ei).
    + transitivity (continuous_map k (p j)).
      * exact (Hk i j ttt).
      * exact (proper_morphism (continuous_map k) _ _ ej).
Qed.

Definition collapse_med@{o h | o < h +} (X : TopSpace@{o}) (I : Type@{o})
  (p : I → X) {Z : Top@{h o}} (k : X ~{Top@{h o}}~> Z)
  (Hk : ∀ i j : I, k ∘ collapse_family X I p i ≈ k ∘ collapse_family X I p j) :
  SetoidMorphism@{o o o} (collapse_carrier X I p) (top_carrier Z) :=
  @Build_SetoidMorphism _ (collapse_setoid X I p) _ (is_setoid (top_carrier Z))
    (continuous_map k) (collapse_med_proper X I p k Hk).

Definition collapse_desc_map@{o h | o < h +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) {Z : Top@{h o}} (k : X ~{Top@{h o}}~> Z)
  (Hk : ∀ i j : I, k ∘ collapse_family X I p i ≈ k ∘ collapse_family X I p j) :
  Top_collapse X I p ~{Top@{h o}}~> Z :=
  tquot_desc X (collapse_carrier X I p) (collapse_q X I p) Z k
    (collapse_med X I p k Hk) (fun x => reflexivity _).

(* The mediator is [k] itself on points, on the nose. / 调解人本身在要点上就是 [k]，正中要害。 *)
Example collapse_desc_map_points@{o h | o < h +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) {Z : Top@{h o}} (k : X ~{Top@{h o}}~> Z)
  (Hk : ∀ i j : I, k ∘ collapse_family X I p i ≈ k ∘ collapse_family X I p j) :
  continuous_map (collapse_desc_map X I p k Hk) = collapse_med X I p k Hk
  := eq_refl.

Definition collapse_desc@{o h | o < h +} (X : TopSpace@{o}) (I : Type@{o})
  (p : I → X) {Z : Top@{h o}} (k : X ~{Top@{h o}}~> Z)
  (Hk : ∀ i j : I, k ∘ collapse_family X I p i ≈ k ∘ collapse_family X I p j) :
  ∃! u : Top_collapse X I p ~{Top@{h o}}~> Z, u ∘ collapse_proj X I p ≈ k.
Proof.
  unshelve eapply Build_Unique.
  - exact (collapse_desc_map X I p k Hk).
  - intro x; reflexivity.
  - intros v Hv x. simpl. symmetry. exact (Hv x).
Defined.

(*
 X ~> X/A is an elementary wide coequalizer of the point-inclusions,
 for EVERY family, the empty one included.  The index universe [i] of
 the record is a binder of its own: the record is not cumulative, and
 the colimit round trip below reads it at the hom universe. 

 --------
 X ~> X/A 是点包含的一个初等宽余等化器，对于每一个族，包括空族。记录的索引宇宙 [i] 是它自己的一个绑定器：记录不是累积的，下面的余极限往返在同构宇宙中读取它。
*)
Definition collapse_family_coequalizer@{o h i | o < h, o <= i +}
  (X : TopSpace@{o}) (I : Type@{o}) (p : I → X) :
  IsWideCoequalizer@{i h h} (C := Top@{h o}) (collapse_family X I p)
    (Top_collapse X I p) (collapse_proj X I p) :=
  @Build_IsWideCoequalizer Top@{h o} I Point_Top@{o} X (collapse_family X I p)
    (Top_collapse X I p) (collapse_proj X I p)
    (collapse_wcofork X I p)
    (fun Z k Hk => collapse_desc X I p k Hk).

(*
 The colimit form at this apex, through Structure/Coequalizer/Wide.v's
 round trip, which needs a member of the family: at the empty family
 the colimit is X ⊔ *, not X (Pairs.v's [pquot_wide_coequalizer_colimit]
 and [empty_colimit_not_elementary]). 

 --------
 在这个顶点处的余极限形式，通过 Structure/Coequalizer/Wide.v 的循环操作，需要该族的一个成员：在空族上余极限是 X ⊔ *，而不是 X（Pairs.v 的 [pquot_wide_coequalizer_colimit] 和 [empty_colimit_not_elementary]）。
*)
Definition collapse_family_colimit@{o h | o < h +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) (i0 : I) :
  WideCoequalizer (AWide (C := Top@{h o}) (collapse_family X I p)) :=
  is_wide_coequalizer_colimit (collapse_family X I p) i0
    (collapse_family_coequalizer@{o h h} X I p).

(* The collapse map is epic, from the wide-coequalizer vocabulary. / 崩塌映射非常宏大，来自宽协同化器词汇。 *)
Definition collapse_proj_epic@{o h | o < h +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) : Epic (collapse_proj X I p) :=
  wide_coequalizer_epic _ (collapse_family_coequalizer@{o h o} X I p).

(*
 The direct collapse and the generic small wide coequalizer of its
 family agree, and the comparison is the identity on points. 

 --------
 它的族的直接塌缩和一般小宽余联合器是一致的，并且比较在点上是恒等的。
*)
Definition collapse_iso_generic@{o h u | o < h, h < u +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) :
  Top_collapse X I p ≅[Top@{h o}] twcoeq_obj@{o o h} (collapse_family X I p) :=
  wide_coequalizer_unique _ (collapse_family_coequalizer@{o h o} X I p)
    (twcoeq_IsWideCoequalizer@{o o h} (collapse_family X I p)).

Example collapse_iso_generic_to@{o h u | o < h, h < u +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) (x : X) :
  continuous_map (to (collapse_iso_generic X I p)) x = x := eq_refl.

Example collapse_iso_generic_from@{o h u | o < h, h < u +} (X : TopSpace@{o})
  (I : Type@{o}) (p : I → X) (x : X) :
  continuous_map (from (collapse_iso_generic X I p)) x = x := eq_refl.

(** ** Mac Lane's subset form / ** 马克·莱恩的子集形式 *)

(* A subset of the points of X, as a Type-valued predicate; its points index the family. / X 的点的一个子集，作为一个类型值谓词；它的点索引这个族。 *)
Definition collapse_sub_points@{o} (X : TopSpace@{o}) (A : X → Type@{o}) :
  Type@{o} := { x : X & A x }.

Definition collapse_sub_incl@{o} (X : TopSpace@{o}) (A : X → Type@{o})
  (a : collapse_sub_points X A) : X := projT1 a.

(* X/A. *)
Definition Top_collapse_sub@{o} (X : TopSpace@{o}) (A : X → Type@{o}) :
  TopSpace@{o} :=
  Top_collapse X (collapse_sub_points X A) (collapse_sub_incl X A).

Definition collapse_sub_proj@{o h | o < h +} (X : TopSpace@{o})
  (A : X → Type@{o}) : X ~{Top@{h o}}~> Top_collapse_sub X A :=
  collapse_proj X (collapse_sub_points X A) (collapse_sub_incl X A).

(* "the set of all the arrows sending the one point space * to one of the points a ∈ A" / 从单点空间 * 到 A 中某个点 a ∈ A 的所有箭头的集合 *)
Definition collapse_sub_family@{o h | o < h +} (X : TopSpace@{o})
  (A : X → Type@{o}) (a : collapse_sub_points X A) :
  Point_Top@{o} ~{Top@{h o}}~> X :=
  collapse_family X (collapse_sub_points X A) (collapse_sub_incl X A) a.

(* Construction 5 in the elementary form: X ~> X/A is an elementary wide coequalizer of that family, for every subset. / 初等形式下的构造 5：X ~> X/A 是该族的一个初等广义共同等化子，对于每一个子集都是如此。 *)
Definition collapse_coequalizer@{o h i | o < h, o <= i +} (X : TopSpace@{o})
  (A : X → Type@{o}) :
  IsWideCoequalizer@{i h h} (C := Top@{h o}) (collapse_sub_family X A)
    (Top_collapse_sub X A) (collapse_sub_proj X A) :=
  collapse_family_coequalizer@{o h i} X (collapse_sub_points X A)
    (collapse_sub_incl X A).

Definition collapse_colimit@{o h | o < h +} (X : TopSpace@{o})
  (A : X → Type@{o}) (a0 : collapse_sub_points X A) :
  WideCoequalizer (AWide (C := Top@{h o}) (collapse_sub_family X A)) :=
  collapse_family_colimit X (collapse_sub_points X A) (collapse_sub_incl X A)
    a0.

(* In the elementary form collapsing the empty subset changes nothing: X/∅ ≅ X ... / 在基本形式中，塌缩空子集不会改变任何东西： X/∅ ≅ X ... *)
Definition collapse_empty_iso@{o h u | o < h, h < u +} (X : TopSpace@{o}) :
  Top_collapse_sub X (fun _ => False) ≅[Top@{h o}] X :=
  wide_coequalizer_unique _ (collapse_coequalizer@{o h o} X (fun _ => False))
    (wide_empty_id_IsWideCoequalizer _
       (fun a : collapse_sub_points X (fun _ => False) => projT2 a)).

(*
 A readback of [Empty_Top]'s carrier: the collapse of the empty space has
 no point.  The proof reads the point as a point of [Empty_Top] and uses
 nothing about the subset or the coequalizer. 

 --------
 [Empty_Top] 的承载的回读：空空间的坍塌没有意义。证明将该点读作 [Empty_Top] 的一个点，并且没有使用关于子集或余等化子的任何内容。
*)
Lemma collapse_empty_pointless@{o} :
  top_carrier (Top_collapse_sub Empty_Top@{o} (fun _ => False)) → False.
Proof. intro z. exact z. Qed.

(*
 The statement about the elementary record, whatever its construction:
 no elementary wide coequalizer of the empty family at the empty space
 has a point, since the identity of the empty space descends along it.
 Every colimit of that family has one (Pairs.v's
 [collapse_colimit_point]). 

 --------
 关于初等记录的陈述，无论其构造如何：
 空空间中空族的任何初等广义余等化器
 都没有点，因为空空间的恒等映射沿它下降。
 那个族的每个余极限都有一个点（Pairs.v 的 [collapse_colimit_point]）。
*)
Lemma empty_wide_coequalizer_pointless@{o h i | o < h, o <= i +}
  (Q : Top@{h o}) (e : Empty_Top@{o} ~{Top@{h o}}~> Q) :
  IsWideCoequalizer@{i h h} (C := Top@{h o})
    (collapse_sub_family Empty_Top@{o} (fun _ => False)) Q e →
  top_carrier Q → False.
Proof.
  intros E q.
  destruct (wcoeq_desc E (@id Top@{h o} Empty_Top@{o})
              (fun a => match projT2 a with end)) as [u _ _].
  exact (continuous_map u q).
Qed.
