Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.
Require Import Category.Construction.Comma.Diagram.
Require Import Category.Structure.Pullback.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Category.Monoid.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.One.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Slice.
Require Import Category.Structure.Terminal.

Require Import Coq.Logic.Eqdep_dec.

Generalizable All Variables.

(* * * The fibre product of categories, and pullbacks of categories / * * 范畴的纤维积，以及范畴的拉回 *)

(*
 nLab:      https://ncatlab.org/nlab/show/pullback
 nLab:      https://ncatlab.org/nlab/show/comma+object
 nLab:      https://ncatlab.org/nlab/show/pseudopullback
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_small_categories

 Catalogued as Mac Lane, "Categories for the Working Mathematician", 2nd
 ed., section III.5 exercise 3 (book p. 74).  The construction is the
 evident one: given F : A ⟶ C and G : B ⟶ C, take the pairs of objects
 that AGREE under F and G, and the pairs of arrows whose images agree.
 Everything interesting here is about the word "agree", and about which
 category of categories the resulting square is a pullback IN.

 ** Which ambient category

 This library carries two categories of categories, and they answer this
 question differently.  [Cat] (Instance/Cat.v) has [Functor_Setoid]
 as its hom-setoid, which identifies functors that are merely NATURALLY
 ISOMORPHIC; its own header says so in terms -- it is the homotopy
 category Ho(Cat), "NOT the strict 1-category of categories of the
 textbooks", and an isomorphism in it is an EQUIVALENCE of categories.
 [StrictCat] (Instance/StrictCat.v) has [Functor_StrictEq_Setoid],
 under which two functors are identified by a Leibniz equality of their
 object maps together with a transported agreement of their arrow maps.

 The fibre product below is built out of Leibniz equalities [F a = G b],
 so it is a construction about the strict ambient, and that is where its
 universal property is proved:

 [FibreProduct_IsPullback] : ObjUIP C
 → IsPullback (in StrictCat) F G (FibreProduct F G) FP_fst FP_snd

 In [Cat] it is NOT a pullback, and that is measured rather than asserted:
 [FibreProduct_not_Cat_pullback] refutes it at the cospan
 1 --true--> Indiscrete bool <--false-- 1, where a competing square exists
 (an isomorphism true ≅ false supplies the natural isomorphism [Cat]'s
 square condition asks for) while the fibre product has no objects at all
 ([IB_FibreProduct_empty]), so no mediator can exist.  Read that refutation
 narrowly: [point_cospan_Cat_IsPullback] shows the SAME cospan does have a
 pullback in [Cat], namely the terminal category, so what is refuted is
 this candidate apex and not the existence of pullbacks in [Cat].  Whether
 [HasPullbacks Cat] holds is NOT settled here -- it is neither proved nor
 refuted, and no second candidate (the iso-comma, or pseudopullback, which
 is the standard replacement, or any other) was attempted.

 ** What the hypothesis is, where it is spent, and that it is necessary

 The apex's objects are dependent pairs carrying a PROOF of [F a = G b].
 Two mediators into it may therefore differ in that proof alone while
 agreeing in both coordinates, and the uniqueness clause of the pullback
 is exactly the statement that they do not.  So [ObjUIP C] -- uniqueness of
 identity proofs on the objects of the BASE, the honest hypothesis of
 Theory/Category/Monoid.v, never an axiom here -- is taken, and it is
 spent by exactly one of the pullback's fields, the uniqueness clause
 [FP_med_unique] -- literally it is destructed inside the helper
 [FP_obj_eq], which has no other consumer, so the two readings agree.
 [FP_commutes_strict], [FP_med], [FP_med_fst] and [FP_med_snd] take no
 hypothesis at all.  It is spent only on C: the
 morphism half of that proof needs the equality's two coordinate
 projections, and [FP_obj_eq] returns them alongside the object equality,
 so no hypothesis on A or on B is required.  [ObjUIP] is free for every
 category with decidable object equality, by Hedberg
 ([ObjUIP_of_ObjDecEq], and [FibreProduct_IsPullback_dec]).

 That hypothesis is NECESSARY, and this is a theorem rather than a remark:
 [FP_uniqueness_forces_UIP] shows that deriving the uniqueness clause
 uniformly -- for every cospan, with no hypothesis on the base -- entails
 UIP for every type.  The countermodel is the cospan 1 --x--> Indiscrete X
 <--x-- 1, where the fibre product's objects ARE the loops at x and each
 loop names a mediator satisfying both triangles.  This is the shape of
 [arrow_mul_respects_forces_UIP] (Theory/Category/Monoid.v) and of
 [Discrete_DiscreteRigid_forces_UIP] (Instance/Discrete/Reconstruct.v).

 Consequently [HasPullbacks StrictCat], which quantifies over EVERY
 cospan, is delivered only from the blanket hypothesis
 [∀ C : Category, ObjUIP C] ([StrictCat_HasPullbacks]).  Read the
 necessity theorem precisely before concluding more: it is about the
 uniqueness clause OF THIS APEX, so it does not refute [HasPullbacks
 StrictCat] with some other apex, and no such refutation is offered.

 ** Comma categories as pullbacks of the arrow-category projections

 Construction/Comma.v already records the framing -- comma objects
 are PIE-limits, constructible from pullbacks and the power C^2 -- and that
 framing is consumed rather than restated.  The two one-object instances
 are proved: the slice C/c is the pullback of [Arrow_cod : C^2 ⟶ C] along
 [Diagonal 1 c : 1 ⟶ C] ([Slice_IsPullback]) and the coslice c/C is the
 pullback of [Arrow_dom] along the same ([Coslice_IsPullback]), both in
 [StrictCat] and both under the same [ObjUIP C].  The hypothesis is spent
 for the same reason but NOT, as an earlier draft of this header said, at
 a single point: [slice_arrow_reflect] is where it does work nothing else
 could -- the codomain coordinate of a transported morphism equality is a
 loop at c and must be [eq_refl] (dually [coslice_arrow_reflect] for the
 domain) -- while [Slice_med_arrow] and [Slice_med_unique] spend it again
 through [fp_hom_cast_irr] -- THREE LEMMAS and FOUR USES per side, since
 [Slice_med_arrow] spends it twice (dually [Coslice_med_arrow]).  Contrast
 the fibre product, where the pullback's other three fields really are
 hypothesis-free and only [FP_med_unique] consumes it.
 The apexes here are the tree's OWN [Slice] and [Coslice]
 (Construction/Slice.v), not the fibre product, so these are genuine
 assemblies and not instances of the general theorem.

 PRIOR ART, disclosed rather than left for a reader to find: the tree
 ALREADY has a comma universal property over these same two
 arrow-category projections, and in a module this file Requires --
 [comma_diagram_ump] (Construction/Comma/Diagram.v), Mac Lane §II.6
 Exercise 5, whose own header calls it "what exhibits it as a
 'pullback'-style limit" and re-records the same PIE-limit
 framing cited above.  Nothing here is a restatement of it and nothing it
 proves is falsified: it mediates into the GENERAL comma [(S ↓ T)] over
 the [MediatesDiagram] competitor class with uniqueness at [≈[Cat]],
 whereas the two results below are about the two ONE-OBJECT cospans, use
 the pullback's own competitor class, and are stated at [≈[StrictCat]].
 The claim that nothing in the tree states an [IsPullback] or a
 [Pullback] in [Cat] or [StrictCat] is unaffected and stays true.

 ** Strengths, measured strict-first

 Measured to hold at [eq_refl]: the strict square's object component IS
 the equality each object carries and its morphism component IS the
 equation each morphism carries ([FP_commutes_strict] is a [:=] with no
 tactic); both triangles have [eq_refl] object components, and the arrow
 half is [reflexivity] ([FP_med_fst], [FP_med_snd]); the mediator's object
 action is [((q1 x, q2 x); `1 Hsq x)]; and [fobj[FP_fst ◯ FP_med]] and
 [fmap[FP_fst ◯ FP_med] f] are [fobj[q1]] and [fmap[q1] f] at LEIBNIZ
 equality.  On the comma side, [Slice_commutes] and [Coslice_commutes]
 likewise have [eq_refl] object components, and [fobj[Slice_Arrow] x] is
 [((`1 x, c); `2 x)] at Leibniz equality.

 Measured and REFUTED, both conversion failures: [FP_fst ◯ FP_med = q1] as
 a Leibniz equality of [Functor] RECORDS -- the object and arrow actions
 agree on the nose, as just recorded, but the three law fields are rebuilt
 proofs; and [Slice C c = FibreProduct Arrow_cod (Diagonal 1 c)], the two
 being different categories (the slice stores an arrow, the fibre product
 a pair with a proof).  What IS proved is that both are pullbacks of the
 same cospan; the isomorphism between them that follows from essential
 uniqueness is not built.  These are measured here; they are pinned in the
 companion probe.

 ** Universes, read off the constraint blocks

 [FibreProduct] itself is the freer constant: its block carries bounds
 only ([u <= u5], [u0 <= u4], [u2 <= u4] among others) and no identifica-
 tion between A's and B's object universes.  [FibreProduct_IsPullback]
 displays three separate category binders but its constraint block
 contains [u = u1], [u = u3], [u0 = u2] and [u0 = u4]: all three object
 universes are IDENTIFIED with one another, and so are all three
 hom-and-proof universes.  That is what stating an [IsPullback] in
 [StrictCat] costs -- the three corners of the cospan are objects of ONE
 [Category@{o h p}] instance -- and it is inherited rather than introduced
 here; it is not claimed unavoidable, and no rearrangement was attempted.
 [Slice_IsPullback] and [Coslice_IsPullback] are over
 [C : Category@{u u0 u0}] with no [Set] anywhere in their blocks.
 [FP_uniqueness_forces_UIP@{u u0 u1 u2}] has its hypothesis quantified
 over [Category@{u0 Set Set}] -- hom and proof pinned at [Set], which
 WEAKENS the hypothesis and so strengthens the theorem -- with the
 conclusion [∀ X : Type@{u}], [u <= u0]; the pin is the witnesses' doing
 ([Indiscrete] has [hom := unit], and [_1] is instantiated to match).
 [FibreProduct_not_Cat_pullback] carries [Set < u] and [Set < u3], the
 ordinary price of a concrete witness.  Every category binder above
 displays hom and proof at one level; that identification was not probed
 for its cause and no claim is made about it.

 ** Prior art, measured by shape

 Nothing in the tree states an [IsPullback] or a [Pullback] in [Cat] or in
 [StrictCat] (measured: [rg "IsPullback StrictCat|Pullback StrictCat"] and
 the [Cat] analogue return only this file), and no fibre product of
 categories is constructed anywhere -- the two "fibre/fiber product"
 occurrences elsewhere are prose, about schemes (Structure/Pullback.v)
 and about base change along a slice (Construction/Slice/Pullback.v).
 BEFORE this commit the concrete [HasPullbacks] inhabitants were
 [Sets_HasPullbacks] (Instance/Sets/Pullback.v) and [FinSet_Pullbacks]
 (Instance/FinSet/Classifier.v), with three generic conditionals
 besides; that roster, and the correction of the older "exactly one
 inhabitant" reading, are Instance/Sets/Pullback.v's own (its header),
 cited here rather than re-derived.  This commit adds a
 FOURTH conditional, [StrictCat_HasPullbacks] -- not a generic one, being
 for one named category under a blanket hypothesis.

 ** What is NOT delivered

 No [HasPullbacks Cat] and no refutation of it; only this apex is refuted,
 and only at one cospan.  No iso-comma, pseudopullback, bilimit or
 2-categorical universal property, and no comparison between any of those
 and the fibre product.  No unconditional [HasPullbacks StrictCat].  No
 isomorphism between [Slice C c] and the fibre product of its cospan, and
 no essential-uniqueness statement for pullbacks in [StrictCat] at all.
 The GENERAL comma [(S ↓ T)] as the pullback of [⟨dom, cod⟩ : C^2 ⟶ C ∏ C]
 along [S ∏⟶ T] is not built -- only the two one-object cospans.  Nothing
 about pasting, stability, or the interaction with [Cat_Cartesian]; no
 equalizers, no other finite limits, and no completeness statement for
 either category of categories; no connection to the reductions of
 Structure/Pullback/Reduction.v; and nothing is claimed about the arrow
 category as the power [C^2] beyond its use as the source of the two legs.

 108/108 constants (37 transparent, 71 opaque; 46 of them [Program]
 obligations, which the [.glob] sweep does not record and which take the
 62 the glob does count up to the 108 [Print Module] lists) report
 "Closed under the global context". 

 --------
 nLab:       https://ncatlab.org/nlab/show/pullback 
 nLab:       https://ncatlab.org/nlab/show/comma+object 
 nLab:       https://ncatlab.org/nlab/show/pseudopullback 
 Wikipedia:  https://en.wikipedia.org/wiki/Category_of_small_categories 

 编目为 Mac Lane，《为工作数学家准备的范畴论》，第2版，第III.5节练习3（书第74页）。构造是显而易见的：给定 F : A ⟶ C 和 G : B ⟶ C，取在 F 和 G 下“相符”的对象对，以及其像相符的箭头对。这里有趣的一切都在于“相符”这个词，以及所得到的平方在什么样的范畴中是一个拉回。

 ** 哪个环境范畴这个库包含两类范畴，它们对这个问题的回答不同。[Cat]（Instance/Cat.v）有[Functor_Setoid]作为其同类集合，它将仅自然同构的函子识别在一起；它自己的标题也是这么说的——它是同伦范畴Ho(Cat)，“不是教科书中的严格一范畴”，且其中的同构是范畴的等价。[StrictCat]（Instance/StrictCat.v）有[Functor_StrictEq_Setoid]，在其下，两个函子通过它们对象映射的莱布尼茨相等以及箭头映射的传递一致性来被识别。下面的纤维积是由莱布尼茨相等[F a = G b]构建的，因此它是关于严格环境的构造，并且其普适性质也在此处证明。[FibreProduct_IsPullback]  : ObjUIP C
 → IsPullback（在 StrictCat 中） F G（FibreProduct F G） FP_fst FP_snd在 [Cat] 中，这不是一个拉回（pullback），这是经过测量而非断言的：
 [FibreProduct_not_Cat_pullback] 在余顶点（cospan）处驳斥了它
 1 --true--> 不离散布尔（Indiscrete bool） <--false-- 1，其中存在一个竞争的交换方形
 （一个同构 true ≅ false 提供了自然同构 [Cat] 的
 方形条件所要求的）而纤维积（fibre product）根本没有对象
 （[IB_FibreProduct_empty]），所以不存在中介。狭义地理解该驳斥：
 [point_cospan_Cat_IsPullback] 显示相同的余顶点在 [Cat] 中确实有一个
 拉回，即终端范畴，因此被驳斥的是
 这个候选顶点，而不是 [Cat] 中拉回的存在问题。是否
 [HasPullbacks Cat] 成立在此并未解决——它既未被证明也未被
 驳斥，并且没有尝试第二个候选（同构逗号范畴 iso-comma，或伪拉回 pseudopullback，这
 是标准替代方案，或者任何其他方案）。** 假设是什么，它花在哪里，以及它是必要的顶点的对象是携带 [F a = G b] 证明的依赖对。因此，指向它的两个中介可能仅在该证明上有所不同，而在两个坐标上完全一致，而拉回的唯一性条款正是其不不同的陈述。因此，[ObjUIP C]——对基础对象的身份证明的唯一性，是 Theory/Category/Monoid.v 的诚实假设，在这里从不是公理——被采纳，并且它正好被拉回的某一个字段使用，即唯一性条款 [FP_med_unique]——字面上它在辅助 [FP_obj_eq] 内被析构，没有其他使用者，因此两种读法一致。[FP_commutes_strict]、[FP_med]、[FP_med_fst] 和 [FP_med_snd] 根本不使用任何假设。它只用于 C：该证明的态射部分需要等式的两个坐标投影，而 [FP_obj_eq] 会将它们与对象等式一起返回，因此不需要对 A 或 B 作任何假设。对于每个具有可判定对象等式的范畴，[ObjUIP] 都是自由的，根据 Hedberg （[ObjUIP_of_ObjDecEq] 和 [FibreProduct_IsPullback_dec]）。该假设是必要的，而且这是一个定理，而不是一个备注：
 [FP_uniqueness_forces_UIP] 表明，如果统一地推导唯一性条款——对于每一个余跨，没有基础上的假设——则会导致每种类型的 UIP。反例模型是余跨 1 --x--> 不离散 X <--x-- 1，其中纤维积的对象是 x 的循环，并且每个循环命名一个满足两个三角形的媒介。这是 [arrow_mul_respects_forces_UIP]（Theory/Category/Monoid.v）和 [Discrete_DiscreteRigid_forces_UIP]（Instance/Discrete/Reconstruct.v）的形状。因此，[HasPullbacks StrictCat]，它对每一个余锤进行量化，只能从通用假设[∀ C : Category, ObjUIP C]（[StrictCat_HasPullbacks]）得到。在得出更多结论之前，请准确阅读必要性定理：它关于的是此顶点的唯一性条款，因此它并不否定具有其他顶点的[HasPullbacks StrictCat]，而且也没有提出这样的反例。

 ** 逗号范畴作为箭头范畴投影的拉回Construction/Comma.v 已经记录了框架——逗号对象是 PIE 限制，可以从拉回和幂 C^2 构造——并且该框架是被使用而不是重新陈述的。两个单对象实例已经证明：切片 C/c 是沿 [Diagonal 1 c : 1 ⟶ C] ([Slice_IsPullback]) 的 [Arrow_cod : C^2 ⟶ C] 的拉回，余切片 c/C 是沿相同的 ([Coslice_IsPullback]) 的 [Arrow_dom] 的拉回，这两者都在 [StrictCat] 中并且都在相同的 [ObjUIP C] 之下。这个假设的使用原因相同，但不是像本标题的早期草稿所说的那样在单一点上：[slice_arrow_reflect] 是它起作用的地方，别的地方都不起作用——被传输的态射等式的上标坐标是 c 的一个环，必须是 [eq_refl]（对偶地，对于下标是 [coslice_arrow_reflect]）——而 [Slice_med_arrow] 和 [Slice_med_unique] 则通过 [fp_hom_cast_irr] 再次使用它——每一边三条引理和四次使用，因为 [Slice_med_arrow] 使用了两次它（对偶地 [Coslice_med_arrow]）。对比纤维积，在那里拉回的其他三个域确实是无假设的，只有 [FP_med_unique] 使用它。这里的顶点是树本身的 [Slice] 和 [Coslice]（Construction/Slice.v），而不是纤维积，因此这些是真正的组合，而不是一般定理的实例。现有技术，是公开的而不是留给读者去发现：该树在这两个箭头范畴投影上已经具有逗号（comma）通用性质，并且在一个模块中该文件需要 -- [comma_diagram_ump]（Construction/Comma/Diagram.v），Mac Lane §II.6 练习 5，其自身标题称其为“表现它作为‘拉回’式极限”的方法，并重新记录了上面引用的同一个PIE极限框架。这里没有任何内容是在重复它，也没有它所证明的内容被证伪：它在 [≈[Cat] 处以唯一性调解到 [MediatesDiagram] 竞争者类上的一般逗号 [(S ↓ T)]，而下面的两个结果是关于两个单对象余跨（ONE-OBJECT cospan），使用拉回自身的竞争者类，并在 [≈[StrictCat] 处陈述。声称树中的任何内容都不表示 [IsPullback] 或 [Pullback] 在 [Cat] 或 [StrictCat] 中不受影响并保持正确。

 ** 强度，严格优先测量

 测量在 [eq_refl] 处成立：严格平方的对象分量是每个对象所携带的等式，其态射分量是每个态射所携带的方程（[FP_commutes_strict] 是一个没有策略的 [:=]）；两个三角形都有 [eq_refl] 对象分量，箭头的一半是 [reflexivity] （[FP_med_fst]，[FP_med_snd]）；中介者的对象动作是 [((q1 x, q2 x); `1 Hsq x)]；以及 [fobj[FP_fst ◯ FP_med] ] 和 [fmap[FP_fst ◯ FP_med] f] 在 LEIBNIZ 等式下分别是 [fobj[q1] ] 和 [fmap[q1] f]。 在逗号一侧，[Slice_commutes] 和 [Coslice_commutes] 同样具有 [eq_refl] 对象分量，并且 [fobj[Slice_Arrow] x] 在 Leibniz 等式下是 [((`1 x, c); `2 x)]。测量并反驳，两个转换都是失败的：[FP_fst ◯ FP_med = q1] 作为 [Functor] 记录的莱布尼茨等式 —— 对象和箭头操作完全一致，如刚记录的，但三个律域是重建的证明；而 [Slice C c = FibreProduct Arrow_cod (Diagonal 1 c)] ，两者属于不同的范畴（slice 存储一个箭头，纤维积存储一个带证明的对）。所证明的是它们都是同一个共尖的拉回；由本质唯一性得出的它们之间的同构没有被构建。这些在这里被测量；它们在伴随探针中被固定。  ** 宇宙，从约束块中读取[FibreProduct] 本身是自由常量：它的块仅包含界限（比如 [u <= u5]、[u0 <= u4]、[u2 <= u4] 等），而不涉及 A 和 B 对象宇宙之间的任何识别。[FibreProduct_IsPullback] 显示了三个独立的类别绑定器，但其约束块包含 [u = u1]、[u = u3]、[u0 = u2] 和 [u0 = u4]：三者的对象宇宙相互识别，三者的同态与证明宇宙也相互识别。这就是在 [StrictCat] 中声明 [IsPullback] 的代价——余联的三个角是属于同一个 [Category@{o h p}] 实例的对象——而且这是继承下来的而非在此引入；并未声称这是不可避免的，也未尝试重新安排。[Slice_IsPullback] 和 [Coslice_IsPullback] 超过 [C : Category@{u u0 u0}]，其块中没有任何 [Set]。[FP_uniqueness_forces_UIP@{u u0 u1 u2}] 的假设通过 [Category@{u0 Set Set}] 进行量化——同构和证明固定在 [Set] 上，这削弱了假设，从而加强了定理——结论为 [∀ X : Type@{u}]，[u <= u0]；固定由见证者执行（[Indiscrete] 拥有 [hom := unit]，且 [_1] 被实例化以匹配）。[FibreProduct_not_Cat_pullback] 承载 [Set < u] 和 [Set < u3]，这是具体见证者的一般代价。上面每个类别绑定器在一个层次上显示同构和证明；未探讨该识别的原因，也未对此提出任何声明。  

 ** 先前艺术，以形状衡量在树中没有任何内容注明 [IsPullback] 或 [Pullback] 在 [Cat] 或 [StrictCat] 中（测量：[rg "IsPullback StrictCat|Pullback StrictCat"] 和 [Cat] 类比仅返回此文件），并且没有任何类别的纤维积被构造——其他地方的两个“纤维/ fiber 积”出现都是散文，关于方案（Structure/Pullback.v）以及关于沿切片的基变换（Construction/Slice/Pullback.v）。在此提交之前，具体的 [HasPullbacks] 成员是 [Sets_HasPullbacks]（Instance/Sets/Pullback.v）和 [FinSet_Pullbacks]（Instance/FinSet/Classifier.v），除此之外还有三个通用条件；该目录，以及对旧的“恰有一个成员”读法的修正，都是 Instance/Sets/Pullback.v 自身的内容（其头部），在此引用而非重新推导。此提交添加了第四个条件，[StrictCat_HasPullbacks]——不是通用的，而是针对在一个统一假设下的特定类别。

 ** 未提供的内容没有 [HasPullbacks Cat]，也没有对它的反驳；只有这个顶点被反驳，且仅在一个余范畴上。没有同构逗号、伪拉回、双极限或二范畴的普遍性质，也没有它们与纤维积之间的比较。没有无条件的 [HasPullbacks StrictCat]。[Slice C c] 与其余范畴的纤维积之间没有同构，并且在 [StrictCat] 中对拉回也没有本质唯一性声明。作为 [⟨dom, cod⟩ : C^2 ⟶ C ∏ C] 沿 [S ∏⟶ T] 的拉回的一般逗号 [(S ↓ T)] 没有构建——只有两个单对象的余范畴。关于粘贴、稳定性或与 [Cat_Cartesian] 的交互没有任何说明；没有均衡器，没有其他有限限制，也没有针对任何类别的完整性声明；与 Structure/Pullback/Reduction.v 的约简没有任何联系；并且对于箭头类别作为幂 [C^2]，除了用作两个分支的源之外，没有做出任何声称。

 108/108 个常量（37 个透明，71 个不透明；其中 46 个是 [Program] 义务，而 [.glob] 扫描未记录这些义务，并且需要 62 个 glob 才能计数到 108 个 [Print Module] 列表）报告“在全局上下文中封闭”。
*)

(** ** A small transport kit / ** 一个小型运输工具包 *)

(*
 Functors commute with [hom_cast], the endpoints being relabelled by
 [f_equal] of the object map.  Both sides become [fmap[P] f] once the two
 equalities are eliminated. 

 --------
 函子与 [hom_cast] 交换，端点由对象映射的 [f_equal] 重新标记。一旦消除这两个等式，双方都变为 [fmap[P] f]。
*)
Lemma fmap_hom_cast {X Y : Category} (P : X ⟶ Y) {a b a' b' : X}
      (ea : a = a') (eb : b = b') (f : a ~> b) :
  fmap[P] (hom_cast ea eb f)
    ≈ hom_cast (f_equal (fobj[P]) ea) (f_equal (fobj[P]) eb) (fmap[P] f).
Proof. destruct ea, eb; reflexivity. Qed.

(*
 Reading a [hom_cast] equation as a conjugation, in the orientation the
 natural-isomorphism coherence of [Functor_Setoid] wants. 

 --------
 将 [hom_cast] 方程作为一个共轭来阅读，在该方向上 [Functor_Setoid] 的自然同构相干性所要求的。
*)
Lemma hom_cast_shift {X : Category} {a b a' b' : X}
      (ea : a = a') (eb : b = b') (f : a ~> b) (g : a' ~> b') :
  hom_cast ea eb f ≈ g → f ≈ id_cast (eq_sym eb) ∘ g ∘ id_cast ea.
Proof. destruct ea, eb; simpl; intros Hg; rewrite <- Hg; cat. Qed.

(*
 Under uniqueness of identity proofs on objects a [hom_cast] does not
 depend on WHICH proofs of its two endpoint equations it is given. 

 --------
 在对象上身份证明的唯一性下，[hom_cast] 不依赖于所给的两个端点方程的哪一个证明。
*)
Lemma fp_hom_cast_irr {X : Category} (uip : ObjUIP X) {a b a' b' : X}
      (e1 e1' : a = a') (e2 e2' : b = b') (f : a ~> b) :
  hom_cast e1 e2 f = hom_cast e1' e2' f.
Proof. now rewrite (uip _ _ e1 e1'), (uip _ _ e2 e2'). Qed.

(* One [hom_cast] equation, read as a commuting square of [id_cast]s. / 一个 [hom_cast] 方程，读作 [id_cast] 的交换方格。 *)
Lemma cast_of_hom_cast {X : Category} {a a' b b' : X}
      (ea : a = a') (eb : b = b') (g : a ~> b) (h : a' ~> b') :
  hom_cast ea eb g ≈ h → id_cast eb ∘ g ≈ h ∘ id_cast ea.
Proof. destruct ea, eb; simpl; intros Hg; rewrite id_left, id_right; auto. Qed.

(* A [hom_cast] that relabels only the codomain is a postcomposition. / 一个仅重新标记陪域的 [hom_cast] 是一个后组合。 *)
Lemma hom_cast_left_refl {X : Category} {a b b' : X} (eb : b = b')
      (g : a ~> b) : hom_cast eq_refl eb g ≈ id_cast eb ∘ g.
Proof. destruct eb; cat. Qed.

(* An equality of comma objects transports the morphism they carry. / 逗号对象的等式传递它们所携带的函子。 *)
Lemma comma_obj_eq_inv {A B D : Category} {S : A ⟶ D} {T : B ⟶ D}
      {x y : (S ↓ T)} (E : x = y) :
  hom_cast (f_equal (fun z => fobj[S] (fst ``z)) E)
           (f_equal (fun z => fobj[T] (snd ``z)) E) (`2 x) = `2 y.
Proof. destruct E; reflexivity. Qed.

(*
 An arrow whose codomain is [d] IS the slice object over [d] it determines;
 this is the object half of the first triangle below.  It is stated at top
 level rather than inside the slice section so that eliminating [eh] does
 not have to generalize the section's own hypotheses. 

 --------
 一个箭头，其余域是 [d]，是它所确定的 [d] 上的切片对象；这是下面第一个三角形的对象的一半。它被声明在顶层而不是在切片部分中，这样消除 [eh] 时就不必推广该部分自身的假设。
*)
Lemma slice_arrow_eta {D : Category} (d : D) (h : @Arrow D)
      (eh : snd ``h = d) :
  ((fst ``h, d); hom_cast eq_refl eh (`2 h)) = h.
Proof. destruct h as [[a b] g]; simpl in *; destruct eh; reflexivity. Defined.

(* Dually, one that relabels only the domain is a precomposition. / 同样地，仅重新标记域的被称为前组合。 *)
Lemma hom_cast_right_refl {X : Category} {a a' b : X} (ea : a = a')
      (g : a ~> b) : hom_cast ea eq_refl g ≈ g ∘ id_cast (eq_sym ea).
Proof. destruct ea; cat. Qed.

(*
 An arrow whose domain is [d] IS the coslice object under [d] it
 determines. 

 --------
 一个其定义域为 [d] 的箭头是 [d] 之下的余片对象，它由此确定。
*)
Lemma coslice_arrow_eta {D : Category} (d : D) (h : @Arrow D)
      (eh : fst ``h = d) :
  ((d, snd ``h); hom_cast eh eq_refl (`2 h)) = h.
Proof. destruct h as [[a b] g]; simpl in *; destruct eh; reflexivity. Defined.

(* Turning a [hom_cast] equation around. / 把 [hom_cast] 方程反过来。 *)
Lemma hom_cast_flip {X : Category} {a a' b b' : X}
      (ea : a = a') (eb : b = b') (g : a ~> b) (h : a' ~> b') :
  hom_cast ea eb g ≈ h → hom_cast (eq_sym ea) (eq_sym eb) h ≈ g.
Proof. destruct ea, eb; simpl; intros Hg; now symmetry. Qed.

Section FibreProduct.

Context {A B C : Category}.
Context (F : A ⟶ C) (G : B ⟶ C).

#[local] Set Transparent Obligations.
#[local] Obligation Tactic := idtac.

Program Definition FibreProduct : Category := {|
  obj    := ∃ p : A ∏ B, F (fst p) = G (snd p);
  hom    := fun x y =>
    ∃ f : (fst ``x ~{A}~> fst ``y) * (snd ``x ~{B}~> snd ``y),
      hom_cast (`2 x) (`2 y) (fmap[F] (fst f)) ≈ fmap[G] (snd f);
  homset := fun _ _ =>
    {| equiv := fun f g => (fst `1 f ≈ fst `1 g) * (snd `1 f ≈ snd `1 g) |};
  id      := fun _ => ((id, id); _);
  compose := fun _ _ _ f g => ((fst `1 f ∘ fst `1 g, snd `1 f ∘ snd `1 g); _)
|}.
Next Obligation.
  intros [[]] [[]]; simpl in *; equivalence.
Qed.
Next Obligation.
  intros x; simpl.
  rewrite !fmap_id.
  apply hom_cast_id.
Qed.
Next Obligation.
  intros x y z f g; simpl.
  rewrite !fmap_comp.
  rewrite <- (hom_cast_comp (`2 x) (`2 y) (`2 z)).
  rewrite (`2 f), (`2 g).
  reflexivity.
Qed.
Next Obligation.
  intros ? ? ? ? ? [e0 e1] ? ? [e2 e3].
  split.
  - now simpl; rewrite e0, e2.
  - now simpl; rewrite e1, e3.
Qed.
Next Obligation. intros; simpl; split; now rewrite id_left. Qed.
Next Obligation. intros; simpl; split; now rewrite id_right. Qed.
Next Obligation. intros; simpl; split; apply comp_assoc. Qed.
Next Obligation. intros; simpl; split; apply comp_assoc_sym. Qed.

Program Instance FP_fst : FibreProduct ⟶ A := {|
  fobj := fun x => fst ``x;
  fmap := fun _ _ f => fst ``f
|}.
Next Obligation. now intros ? ? ? ? [e0 e1]. Qed.
Next Obligation. now repeat intro. Qed.
Next Obligation. now repeat intro. Qed.

Program Instance FP_snd : FibreProduct ⟶ B := {|
  fobj := fun x => snd ``x;
  fmap := fun _ _ f => snd ``f
|}.
Next Obligation. now intros ? ? ? ? [e0 e1]. Qed.
Next Obligation. now repeat intro. Qed.
Next Obligation. now repeat intro. Qed.

(* * ** Object equality in the fibre product / * **纤维积中的对象相等 *)

(*
 Two objects of the fibre product agreeing in both coordinates are equal --
 PROVIDED the equality proofs they carry can be identified, which is
 exactly [ObjUIP C].  The sigma also returns the two projection equations,
 so that a later [hom_cast] along this equality can be rewritten into the
 coordinate casts without a second appeal to uniqueness of proofs (in
 particular without any hypothesis on A or B). 

 --------
 纤维积的两个对象在两个坐标上都相同则它们相等——前提是它们携带的相等证明可以被识别，这正是 [ObjUIP C]。Sigma 还返回两个投影方程，因此后续沿此相等的 [hom_cast] 可以重写为坐标转换，而无需第二次调用证明的唯一性（特别是对 A 或 B 没有任何假设）。
*)
Lemma FP_obj_eq (uip : ObjUIP C) (x y : FibreProduct)
      (e1 : fst ``x = fst ``y) (e2 : snd ``x = snd ``y) :
  { e : x = y & (f_equal (fobj[FP_fst]) e = e1)
              * (f_equal (fobj[FP_snd]) e = e2) }.
Proof.
  destruct x as [[a b] p], y as [[a' b'] p']; simpl in *.
  destruct e1, e2, (uip _ _ p p').
  exists eq_refl; split; reflexivity.
Defined.

(* * ** The projection square commutes, in both ambient categories / * ** 投影平方在两个环境范畴中交换 *)

(*
 Strictly: the object component IS the equality carried by the object, and
 the morphism component IS the equation carried by the morphism. 

 --------
 严格来说：对象部分就是由对象携带的等式，而态射部分就是由态射携带的方程。
*)
Definition FP_commutes_strict :
  F ∘[StrictCat] FP_fst ≈[StrictCat] G ∘[StrictCat] FP_snd :=
  @Build_strict_eq FibreProduct C (F ◯ FP_fst) (G ◯ FP_snd)
                   (fun x : FibreProduct => `2 x)
                   (fun (x y : FibreProduct) (f : x ~> y) => `2 f).

(*
 Weakly: the same data read as a natural isomorphism, each component the
 [id_cast] of the object's equality. 

 --------
 弱地：相同的数据被读取为自然同构，每个分量都是对象等式的 [id_cast]。
*)
Program Definition FP_commutes_cat :
  F ∘[Cat] FP_fst ≈[Cat] G ∘[Cat] FP_snd :=
  (fun x => id_cast_iso (`2 x); _).
Next Obligation.
  intros x y f.
  pose proof (`2 f) as Hf; cbv beta in Hf.
  simpl.
  now apply hom_cast_shift.
Qed.

(* * ** The mediator, its triangles, and its uniqueness / * ** 中介、它的三角形及其独特性 *)

Section Mediator.

Context {Q : Category}.
Context (q1 : Q ⟶ A) (q2 : Q ⟶ B).
Context (Hsq : F ∘[StrictCat] q1 ≈[StrictCat] G ∘[StrictCat] q2).

Program Definition FP_med : Q ⟶ FibreProduct := {|
  fobj := fun x => ((q1 x, q2 x); `1 Hsq x);
  fmap := fun x y f => ((fmap[q1] f, fmap[q2] f); strict_fmap_cast Hsq f)
|}.
Next Obligation. intros x y f g Hfg; split; simpl; now rewrite Hfg. Qed.
Next Obligation. intros x; split; simpl; apply fmap_id. Qed.
Next Obligation. intros x y z f g; split; simpl; apply fmap_comp. Qed.

(*
 Both triangles hold with an [eq_refl] object component: the mediator's
 first coordinate IS [q1] and its second IS [q2], definitionally. 

 --------
 两条三角形都包含一个 [eq_refl] 对象组件：调解者的第一个坐标是 [q1]，第二个坐标是 [q2]，这是定义上的。
*)
Definition FP_med_fst : FP_fst ∘[StrictCat] FP_med ≈[StrictCat] q1.
Proof.
  refine (@Build_strict_eq Q A (FP_fst ◯ FP_med) q1 (fun _ => eq_refl) _).
  intros x y f; reflexivity.
Defined.

Definition FP_med_snd : FP_snd ∘[StrictCat] FP_med ≈[StrictCat] q2.
Proof.
  refine (@Build_strict_eq Q B (FP_snd ◯ FP_med) q2 (fun _ => eq_refl) _).
  intros x y f; reflexivity.
Defined.

(*
 Uniqueness.  This is the ONLY place a hypothesis is spent, and it is spent
 only on C: the object part needs the two proofs of [F a = G b] carried by
 the competitor and by the mediator to agree, and [FP_obj_eq] hands back
 the projection equations that make the morphism part go through with no
 hypothesis on A or B. 

 --------
 独特性。这是唯一一个假设被使用的地方，而且它仅用于C：对象部分需要由竞争者和中介携带的[F a = G b]的两个证明一致，而[FP_obj_eq]则返回投影方程，使得态射部分在A或B上没有假设的情况下成立。
*)
Lemma FP_med_unique (uip : ObjUIP C) (v : Q ⟶ FibreProduct)
      (H1 : FP_fst ∘[StrictCat] v ≈[StrictCat] q1)
      (H2 : FP_snd ∘[StrictCat] v ≈[StrictCat] q2) :
  v ≈[StrictCat] FP_med.
Proof.
  refine (@Build_strict_eq Q FibreProduct v FP_med
            (fun x => `1 (FP_obj_eq uip (v x) (FP_med x)
                                    (`1 H1 x) (`1 H2 x))) _).
  intros x y f.
  pose proof (`2 (FP_obj_eq uip (v x) (FP_med x) (`1 H1 x) (`1 H2 x)))
    as [P1x P2x].
  pose proof (`2 (FP_obj_eq uip (v y) (FP_med y) (`1 H1 y) (`1 H2 y)))
    as [P1y P2y].
  split.
  - etransitivity;
      [ exact (fmap_hom_cast FP_fst _ _ (fmap[v] f)) | ].
    rewrite P1x, P1y.
    exact (strict_fmap_cast H1 f).
  - etransitivity;
      [ exact (fmap_hom_cast FP_snd _ _ (fmap[v] f)) | ].
    rewrite P2x, P2y.
    exact (strict_fmap_cast H2 f).
Qed.

End Mediator.

(** ** The strict pullback / ** 严格回撤 *)

Definition FibreProduct_IsPullback (uip : ObjUIP C) :
  @IsPullback StrictCat A B C F G FibreProduct FP_fst FP_snd.
Proof.
  unshelve refine {| is_pullback_commutes := FP_commutes_strict |}.
  intros Q q1 q2 Hsq.
  unshelve refine {| unique_obj := FP_med q1 q2 Hsq |}.
  - split; [ exact (FP_med_fst q1 q2 Hsq) | exact (FP_med_snd q1 q2 Hsq) ].
  - intros v [Hv1 Hv2].
    symmetry.
    exact (FP_med_unique q1 q2 Hsq uip v Hv1 Hv2).
Defined.

Definition FibreProduct_Pullback (uip : ObjUIP C) :
  @Pullback StrictCat A B C F G :=
  is_pullback_pullback (FibreProduct_IsPullback uip).

End FibreProduct.

(* * ** Packaging: all pullbacks in StrictCat, under a blanket hypothesis / * ** 包装：StrictCat 中的所有回拉，在一个统一假设下 *)

(*
 [ObjUIP] is not an axiom anywhere in this library, and it is free for every
 category whose objects have decidable equality (Hedberg); [obj_uip] of
 Construction/Quotient.v is that argument. 

 --------
 [ObjUIP] 在这个库的任何地方都不是公理，并且对于每个对象具有可判定相等性的范畴都是自由的（Hedberg）；Construction/Quotient.v 中的 [obj_uip] 就是那个论证。
*)
Definition ObjUIP_of_ObjDecEq {C : Category} `{@ObjDecEq C} : ObjUIP C :=
  fun x y p q => @obj_uip C _ x y p q.

Definition FibreProduct_IsPullback_dec {A B C : Category}
           (F : A ⟶ C) (G : B ⟶ C) `{@ObjDecEq C} :
  @IsPullback StrictCat A B C F G (FibreProduct F G) (FP_fst F G) (FP_snd F G)
  := FibreProduct_IsPullback F G ObjUIP_of_ObjDecEq.

(*
 The class [HasPullbacks StrictCat] quantifies over EVERY cospan, so it can
 only be inhabited from a blanket hypothesis.  Nothing weaker will do: the
 converse below shows that the uniqueness clause, taken uniformly, is that
 hypothesis. 

 --------
 类 [HasPullbacks StrictCat] 对每个余跨度进行量化，所以它只能从一个总体假设中被占据。没有更弱的假设可以：下面的逆命题表明，一个统一地取的唯一性条款就是那个假设。
*)
Definition StrictCat_HasPullbacks (uip : ∀ C : Category, ObjUIP C) :
  HasPullbacks StrictCat.
Proof.
  constructor; intros A B C F G.
  exact (FibreProduct_Pullback F G (uip C)).
Defined.

(* * ** The weak ambient: what happens in Ho(Cat) / * ** 弱环境：Ho(Cat) 中发生的事情 *)

Section CatMeasurement.

(*
 Any two functors into the terminal category are naturally isomorphic; this
 is [one_unique] at [Cat_Terminal], and it is all the universal property of
 the cospans below needs. 

 --------
 任意两个指向终结范畴的函子都是自然同构的；这是在 [one_unique] 上的 [Cat_Terminal]，并且它满足下面余跨所需的所有普遍性质。
*)
Lemma one_functors_equiv {Q : Category} (u v : Q ⟶ _1) : u ≈[Cat] v.
Proof. now apply (@one_unique Cat Cat_Terminal). Qed.

(*
 A cospan of two points of C, with an isomorphism between them supplying
 the commuting square in Cat. 

 --------
 C 的两个点的余跨度，其中它们之间的同构提供了 Cat 中的交换方块。
*)
Program Definition point_cospan_square {C : Category} {x y : C} (i : x ≅ y) :
  Diagonal _1 x ∘[Cat] Id[_1] ≈[Cat] Diagonal _1 y ∘[Cat] Id[_1] :=
  (fun _ => i; _).
Next Obligation.
  rewrite id_right.
  symmetry; apply iso_from_to.
Qed.

(*
 Such a cospan DOES have a pullback in Cat, namely the terminal category:
 every competing square factors through [Erase], uniquely up to natural
 isomorphism, because [Cat(Q, 1)] is a singleton up to [≈]. 

 --------
 这样的余挠在Cat中确实有一个拉回，即终类别：每一个竞争方形都通过 [Erase] 唯一地（达至自然同构）分解，因为 [Cat(Q, 1)] 至 [≈] 是单例。
*)
Definition point_cospan_Cat_IsPullback {C : Category} {x y : C} (i : x ≅ y) :
  @IsPullback Cat _1 _1 C (Diagonal _1 x) (Diagonal _1 y) _1 Id[_1] Id[_1].
Proof.
  unshelve refine {| is_pullback_commutes := point_cospan_square i |}.
  intros Q q1 q2 Hsq.
  unshelve refine {| unique_obj := Erase Q |}.
  - split; apply one_functors_equiv.
  - intros v _; apply one_functors_equiv.
Defined.

(*
 The witness: two objects of a category that are isomorphic without being
 equal.  [Indiscrete bool] has exactly one arrow between any two points, so
 [true ≅ false] there, while [true = false] is empty. 

 --------
 目击者：一个类别中的两个对象，它们是同构的但不相等。[Indiscrete bool] 在任意两点之间恰好有一条箭头，所以 [true ≅ false] 存在，而 [true = false] 是空的。
*)
Definition IB : Category := Indiscrete bool.

Program Definition IB_iso : @Isomorphism IB true false := {| to := tt;
                                                             from := tt |}.

Definition IBtrue  : _1 ⟶ IB := @Diagonal IB _1 true.
Definition IBfalse : _1 ⟶ IB := @Diagonal IB _1 false.

(* The strict fibre product of that cospan has NO objects at all. / 那个余圆的严格纤维积根本没有任何对象。 *)
Lemma IB_FibreProduct_empty : obj[FibreProduct IBtrue IBfalse] → False.
Proof. intros x; pose proof (`2 x) as Hx; simpl in Hx; discriminate. Qed.

(*
 Hence the strict fibre product is not a pullback in Cat: the competing
 square built from [IB_iso] has no mediator at all, since a functor out of
 [_1] would name an object of an object-empty category.  Note what this
 does and does not say -- the SAME cospan does have a Cat-pullback, by
 [point_cospan_Cat_IsPullback]; what fails is this candidate apex. 

 --------
 因此，严格纤维积在 Cat 中不是拉回：由 [IB_iso] 构建的竞争方形根本没有中介者，因为从 [_1] 出发的函子会命名一个对象为空的范畴的对象。请注意这句话所说和未说的内容——相同的余叉确实有一个 Cat-拉回，由 [point_cospan_Cat_IsPullback] 给出；失败的是这个候选顶点。
*)
Theorem FibreProduct_not_Cat_pullback :
  @IsPullback Cat _1 _1 IB IBtrue IBfalse
              (FibreProduct IBtrue IBfalse)
              (FP_fst IBtrue IBfalse) (FP_snd IBtrue IBfalse) → False.
Proof.
  intros HP.
  destruct (is_pullback_ump HP _1 Id[_1] Id[_1] (point_cospan_square IB_iso))
    as [u _ _].
  exact (IB_FibreProduct_empty (u ttt)).
Qed.

End CatMeasurement.

(* * ** Necessity: uniform uniqueness IS the hypothesis / * ** 必要性：统一的唯一性就是假设 *)

Section Necessity.

(*
 The indiscrete category on X has object type X, so a loop at a point of X
 is literally a loop at an object.  Its homs are [unit], which keeps every
 morphism obligation below trivial. 

 --------
 X 上的不离散范畴的对象类型是 X，因此 X 上一个点的环实际上就是一个对象上的环。它的态射是 [unit]，这使得每个态射的义务保持在平凡以下。
*)
Definition IX (X : Type) : Category := Indiscrete X.

Lemma punit_eq (u : poly_unit) : ttt = u.
Proof. now destruct u. Defined.

Definition IXpt {X : Type} (x : X) : _1 ⟶ IX X := @Diagonal (IX X) _1 x.

(*
 Each loop [p : x = x] names a functor into the fibre product of the cospan
 1 --x--> IX X <--x-- 1, and every such functor satisfies both triangles. 

 --------
 每个循环 [p : x = x] 给出了一个函子，映入余锥 1 --x--> IX X <--x-- 1 的纤维积，并且每个这样的函子都满足两个三角形。
*)
Program Definition loop_functor {X : Type} {x : X} (p : x = x) :
  _1 ⟶ FibreProduct (IXpt x) (IXpt x) := {|
  fobj := fun _ => ((ttt, ttt); p);
  fmap := fun _ _ _ => ((id, id); _)
|}.
Next Obligation.
  intros; simpl.
  match goal with |- ?a = ?b => now destruct a, b end.
Qed.

Lemma loop_functor_fst {X : Type} {x : X} (p : x = x) :
  FP_fst (IXpt x) (IXpt x) ∘[StrictCat] loop_functor p ≈[StrictCat] Id[_1].
Proof.
  refine (@Build_strict_eq _1 _1
            (FP_fst (IXpt x) (IXpt x) ◯ loop_functor p) Id[_1]
            (fun o => punit_eq o) _).
  intros a b k; simpl.
  match goal with |- ?u = ?v => now destruct u, v end.
Qed.

Lemma loop_functor_snd {X : Type} {x : X} (p : x = x) :
  FP_snd (IXpt x) (IXpt x) ∘[StrictCat] loop_functor p ≈[StrictCat] Id[_1].
Proof.
  refine (@Build_strict_eq _1 _1
            (FP_snd (IXpt x) (IXpt x) ◯ loop_functor p) Id[_1]
            (fun o => punit_eq o) _).
  intros a b k; simpl.
  match goal with |- ?u = ?v => now destruct u, v end.
Qed.

Definition punit_pair_dec (a b : poly_unit * poly_unit) : {a = b} + {a <> b}.
Proof. destruct a as [[] []], b as [[] []]; now left. Defined.

(*
 Deriving the uniqueness clause of the strict pullback UNIFORMLY -- for
 every cospan, with no hypothesis on the base -- entails UIP for every type.
 So [ObjUIP C] in [FibreProduct_IsPullback] is not an artifact of the proof
 given above; it is what the statement costs.  This is the shape of
 [arrow_mul_respects_forces_UIP] (Theory/Category/Monoid.v) and
 [Discrete_DiscreteRigid_forces_UIP] (Instance/Discrete/Reconstruct.v). 

 --------
 严格拉回的唯一性条款的推导是统一的——对于每一个余跨度，在基上没有任何假设——意味着每种类型都具有 UIP。因此，[ObjUIP C] 在 [FibreProduct_IsPullback] 中不是上述证明的一个人为产物；这是该陈述的代价。这就是 [arrow_mul_respects_forces_UIP]（Theory/Category/Monoid.v）和 [Discrete_DiscreteRigid_forces_UIP]（Instance/Discrete/Reconstruct.v）的形式。
*)
Theorem FP_uniqueness_forces_UIP
        (K : ∀ (A B C : Category) (F : A ⟶ C) (G : B ⟶ C),
               @IsPullback StrictCat A B C F G (FibreProduct F G)
                           (FP_fst F G) (FP_snd F G)) :
  ∀ (X : Type) (x y : X) (p q : x = y), p = q.
Proof.
  assert (loops : ∀ (X : Type) (x : X) (p : x = x), p = eq_refl).
  { intros X x p.
    pose proof (is_pullback_ump (K _1 _1 (IX X) (IXpt x) (IXpt x))
                  _1 Id[_1] Id[_1] (reflexivity _)) as U.
    pose proof (uniqueness U (loop_functor p)
                  (loop_functor_fst p, loop_functor_snd p)) as Up.
    pose proof (uniqueness U (loop_functor (@eq_refl _ x))
                  (loop_functor_fst eq_refl, loop_functor_snd eq_refl)) as Ur.
    assert (Hpq : loop_functor p ≈[StrictCat] loop_functor (@eq_refl _ x))
      by (rewrite <- Up; exact Ur).
    exact (inj_pair2_eq_dec _ punit_pair_dec _ _ _ _ (`1 Hpq ttt)). }
  intros X x y p q; destruct p; symmetry; apply loops.
Qed.

End Necessity.


(* * ** Comma categories as pullbacks of the arrow-category projections / * ** 逗号范畴作为箭头范畴投影的拉回 *)

Section SliceAsPullback.

Context {C : Category}.
Context (c : C).
Context (uip : ObjUIP C).

#[local] Set Transparent Obligations.
#[local] Obligation Tactic := idtac.

(*
 [Default Proof Using "All"] reaches the section's [Qed]/[Defined] proofs,
 so those take [uip] positionally even where it does not appear in the
 statement (the Theory/Category/Monoid.v idiom).  It does NOT reach a
 [Program Definition]: [Slice_proj], [Slice_Arrow] and [Slice_med] -- and
 their coslice twins -- are genuinely free of [ObjUIP], as [Check] shows,
 so a consumer reusing them drags in no hypothesis. 

 --------
 [Default Proof Using "All"] 到达了该部分的 [Qed] / [Defined] 证明，因此即使在陈述中未出现，它们在位置上仍占据 [uip] 的位置（Theory/Category/Monoid.v 习惯用法）。它没有达到 [Program Definition] : [Slice_proj] , [Slice_Arrow] 和 [Slice_med] ——以及它们的余切双胞胎——它们确实不含 [ObjUIP] ，正如 [Check] 所示，因此复用它们的使用者不会引入任何假设。
*)
Local Set Default Proof Using "All".

(* The evident projection [C/c ⟶ C]; used only to read the hom-setoid of the slice as a hom-setoid of C, which is what [fmap_hom_cast] needs. / 明显的投影 [C/c ⟶ C]；仅用于将切片的同态集合体读取为 C 的同态集合体，这正是 [fmap_hom_cast] 所需要的。 *)
Program Definition Slice_proj : Slice C c ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.
Next Obligation. now repeat intro. Qed.
Next Obligation. now intros. Qed.
Next Obligation. now intros. Qed.

(* The first leg: an object of the slice IS an arrow with codomain c. / 第一步：片的一个对象就是一个余域为 c 的箭头。 *)
Program Definition Slice_Arrow : Slice C c ⟶ @Arrow C := {|
  fobj := fun x => ((`1 x, c); `2 x);
  fmap := fun _ _ f => ((`1 f, id); _)
|}.
Next Obligation. intros x y f; simpl; rewrite id_left; apply (`2 f). Qed.
Next Obligation. intros x y f g Hfg; split; [ exact Hfg | reflexivity ]. Qed.
Next Obligation. intros x; split; reflexivity. Qed.
Next Obligation.
  intros x y z f g; split; simpl; [ reflexivity | now rewrite id_left ].
Qed.

(*
 A strict functor equality into the slice is settled by its [Slice_proj]
 reading, the slice hom-setoid being that of C on the underlying arrow. 

 --------
 通过其 [Slice_proj] 读法，片上的严格函子等式得以确定，片的同态集合等价类是基于底层箭头的 C 的同态集合等价类。
*)
Lemma slice_strict_eq {Q : Category} (u v : Q ⟶ Slice C c)
      (eo : ∀ z, u z = v z)
      (em : ∀ z w (f : z ~> w),
              hom_cast (f_equal (fobj[Slice_proj]) (eo z))
                       (f_equal (fobj[Slice_proj]) (eo w))
                       (fmap[Slice_proj] (fmap[u] f))
                ≈ fmap[Slice_proj] (fmap[v] f)) :
  u ≈[StrictCat] v.
Proof.
  refine (@Build_strict_eq Q (Slice C c) u v eo _).
  intros z w f.
  change (fmap[Slice_proj] (hom_cast (eo z) (eo w) (fmap[u] f))
            ≈ fmap[Slice_proj] (fmap[v] f)).
  etransitivity;
    [ exact (fmap_hom_cast Slice_proj (eo z) (eo w) (fmap[u] f)) | ].
  exact (em z w f).
Qed.

(*
 [Slice_Arrow] is injective on objects.  This is where [ObjUIP C] does
 work that nothing else could do: the codomain coordinate of the
 transported morphism equality is a loop at c, and it must be [eq_refl].
 It is NOT the only place the hypothesis is consumed on the slice side --
 [Slice_med_arrow] and [Slice_med_unique] each spend it too, through
 [fp_hom_cast_irr] -- and the section's [Default Proof Using "All"] makes
 every [Qed]/[Defined] result here take it positionally in any case; the
 [Program Definition]s it does not reach are listed at the section head. 

 --------
 [Slice_Arrow] 在对象上是单射的。这正是 [ObjUIP C] 所做的工作，而其他方法无法做到：被传输的态射等式的余域坐标是 c 上的一个环，它必须是 [eq_refl]。它并不是在切片端唯一消耗该假设的地方——[Slice_med_arrow] 和 [Slice_med_unique] 每个也都通过 [fp_hom_cast_irr] 使用了它——并且截面的 [Default Proof Using "All"] 使这里每个 [Qed] / [Defined] 结果无论如何都以位置形式接受它；那些它未能触及的 [Program Definition] 已在截面开头列出。
*)
Lemma slice_arrow_reflect (x y : Slice C c)
      (E : Slice_Arrow x = Slice_Arrow y) : x = y.
Proof.
  pose proof (comma_obj_eq_inv E) as HE.
  set (e1 := f_equal (fun z => fobj[Id[C]] (fst ``z)) E) in HE.
  set (e2 := f_equal (fun z => fobj[Id[C]] (snd ``z)) E) in HE.
  clearbody e1 e2; clear E.
  destruct x as [a f], y as [a' g]; simpl in *.
  rewrite (uip _ _ e2 (@eq_refl _ c)) in HE.
  destruct e1, HE; reflexivity.
Qed.

Section SliceMediator.

Context {Q : Category}.
Context (q1 : Q ⟶ @Arrow C) (q2 : Q ⟶ _1).
Context (Hsq : Arrow_cod ∘[StrictCat] q1
                 ≈[StrictCat] Diagonal _1 c ∘[StrictCat] q2).

Program Definition Slice_med : Q ⟶ Slice C c := {|
  fobj := fun z => (fst ``(q1 z); hom_cast eq_refl (`1 Hsq z) (`2 (q1 z)));
  fmap := fun z w f => (fst ``(fmap[q1] f); _)
|}.
Next Obligation.
  intros z w f; simpl.
  rewrite !hom_cast_left_refl.
  rewrite <- comp_assoc.
  transitivity (id_cast (`1 Hsq w)
                  ∘ (fmap[Arrow_cod] (fmap[q1] f) ∘ `2 (q1 z))).
  { apply compose_respects;
      [ reflexivity | exact (Arrow_square _ _ (fmap[q1] f)) ]. }
  rewrite comp_assoc.
  apply compose_respects; [ | reflexivity ].
  etransitivity;
    [ exact (cast_of_hom_cast _ _ _ _ (strict_fmap_cast Hsq f)) | ].
  exact (id_left (id_cast (`1 Hsq z))).
Qed.
Next Obligation.
  intros z w f g Hfg.
  exact (fst (@fmap_respects _ _ q1 z w f g Hfg)).
Qed.
Next Obligation. intros z; exact (fst (@fmap_id _ _ q1 z)). Qed.
Next Obligation.
  intros z w u f g; exact (fst (@fmap_comp _ _ q1 z w u f g)).
Qed.

Lemma Slice_med_arrow :
  Slice_Arrow ∘[StrictCat] Slice_med ≈[StrictCat] q1.
Proof.
  refine (@Build_strict_eq Q (@Arrow C) (Slice_Arrow ◯ Slice_med) q1
            (fun z => slice_arrow_eta c (q1 z) (`1 Hsq z)) _).
  intros z w f; split.
  - etransitivity;
      [ exact (fmap_hom_cast Arrow_dom _ _
                 (fmap[Slice_Arrow ◯ Slice_med] f)) | ].
    rewrite (fp_hom_cast_irr uip _ eq_refl _ eq_refl).
    reflexivity.
  - etransitivity;
      [ exact (fmap_hom_cast Arrow_cod _ _
                 (fmap[Slice_Arrow ◯ Slice_med] f)) | ].
    rewrite (fp_hom_cast_irr uip _ (eq_sym (`1 Hsq z))
                            _ (eq_sym (`1 Hsq w))).
    exact (hom_cast_flip _ _ _ _ (strict_fmap_cast Hsq f)).
Qed.

Lemma Slice_med_erase :
  Erase (Slice C c) ∘[StrictCat] Slice_med ≈[StrictCat] q2.
Proof.
  refine (@Build_strict_eq Q _1
            (Erase (Slice C c) ◯ Slice_med) q2
            (fun z => punit_eq (q2 z)) _).
  intros z w f; simpl.
  match goal with |- ?u = ?v => now destruct u, v end.
Qed.

Lemma Slice_med_unique (v : Q ⟶ Slice C c)
      (H1 : Slice_Arrow ∘[StrictCat] v ≈[StrictCat] q1)
      (H2 : Erase (Slice C c) ∘[StrictCat] v ≈[StrictCat] q2) :
  v ≈[StrictCat] Slice_med.
Proof.
  refine (slice_strict_eq v Slice_med
            (fun z => slice_arrow_reflect (v z) (Slice_med z)
                        (eq_trans (`1 H1 z) (eq_sym (`1 Slice_med_arrow z))))
            _).
  intros z w f.
  rewrite (fp_hom_cast_irr uip _ (f_equal (fobj[Arrow_dom]) (`1 H1 z))
                          _ (f_equal (fobj[Arrow_dom]) (`1 H1 w))).
  transitivity (fmap[Arrow_dom]
                  (hom_cast (`1 H1 z) (`1 H1 w) (fmap[Slice_Arrow ◯ v] f))).
  { symmetry;
      exact (fmap_hom_cast Arrow_dom _ _ (fmap[Slice_Arrow ◯ v] f)). }
  exact (fst (strict_fmap_cast H1 f)).
Qed.

End SliceMediator.

Definition Slice_commutes :
  Arrow_cod ∘[StrictCat] Slice_Arrow
    ≈[StrictCat] Diagonal _1 c ∘[StrictCat] Erase (Slice C c).
Proof.
  refine (@Build_strict_eq (Slice C c) C
            (Arrow_cod ◯ Slice_Arrow) (Diagonal _1 c ◯ Erase (Slice C c))
            (fun _ => eq_refl) _).
  intros x y f; reflexivity.
Defined.

Definition Slice_IsPullback :
  @IsPullback StrictCat (@Arrow C) _1 C Arrow_cod (Diagonal _1 c)
              (Slice C c) Slice_Arrow (Erase (Slice C c)).
Proof.
  unshelve refine {| is_pullback_commutes := Slice_commutes |}.
  intros Q q1 q2 Hsq.
  unshelve refine {| unique_obj := Slice_med q1 q2 Hsq |}.
  - split; [ exact (Slice_med_arrow q1 q2 Hsq)
           | exact (Slice_med_erase q1 q2 Hsq) ].
  - intros v [Hv1 Hv2].
    symmetry; exact (Slice_med_unique q1 q2 Hsq v Hv1 Hv2).
Defined.

End SliceAsPullback.

Section CosliceAsPullback.

Context {C : Category}.
Context (c : C).
Context (uip : ObjUIP C).

#[local] Set Transparent Obligations.
#[local] Obligation Tactic := idtac.
Local Set Default Proof Using "All".

Program Definition Coslice_proj : Coslice C c ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.
Next Obligation. now repeat intro. Qed.
Next Obligation. now intros. Qed.
Next Obligation. now intros. Qed.

(* The first leg: an object of the coslice IS an arrow with domain c. / 第一步：余切的对象是定义域为 c 的箭头。 *)
Program Definition Coslice_Arrow : Coslice C c ⟶ @Arrow C := {|
  fobj := fun x => ((c, `1 x); `2 x);
  fmap := fun _ _ f => ((id, `1 f); _)
|}.
Next Obligation. intros x y f; simpl; rewrite id_right; apply (`2 f). Qed.
Next Obligation. intros x y f g Hfg; split; [ reflexivity | exact Hfg ]. Qed.
Next Obligation. intros x; split; reflexivity. Qed.
Next Obligation.
  intros x y z f g; split; simpl; [ now rewrite id_left | reflexivity ].
Qed.

Lemma coslice_strict_eq {Q : Category} (u v : Q ⟶ Coslice C c)
      (eo : ∀ z, u z = v z)
      (em : ∀ z w (f : z ~> w),
              hom_cast (f_equal (fobj[Coslice_proj]) (eo z))
                       (f_equal (fobj[Coslice_proj]) (eo w))
                       (fmap[Coslice_proj] (fmap[u] f))
                ≈ fmap[Coslice_proj] (fmap[v] f)) :
  u ≈[StrictCat] v.
Proof.
  refine (@Build_strict_eq Q (Coslice C c) u v eo _).
  intros z w f.
  change (fmap[Coslice_proj] (hom_cast (eo z) (eo w) (fmap[u] f))
            ≈ fmap[Coslice_proj] (fmap[v] f)).
  etransitivity;
    [ exact (fmap_hom_cast Coslice_proj (eo z) (eo w) (fmap[u] f)) | ].
  exact (em z w f).
Qed.

Lemma coslice_arrow_reflect (x y : Coslice C c)
      (E : Coslice_Arrow x = Coslice_Arrow y) : x = y.
Proof.
  pose proof (comma_obj_eq_inv E) as HE.
  set (e1 := f_equal (fun z => fobj[Id[C]] (fst ``z)) E) in HE.
  set (e2 := f_equal (fun z => fobj[Id[C]] (snd ``z)) E) in HE.
  clearbody e1 e2; clear E.
  destruct x as [a f], y as [a' g]; simpl in *.
  rewrite (uip _ _ e1 (@eq_refl _ c)) in HE.
  destruct e2, HE; reflexivity.
Qed.

Section CosliceMediator.

Context {Q : Category}.
Context (q1 : Q ⟶ @Arrow C) (q2 : Q ⟶ _1).
Context (Hsq : Arrow_dom ∘[StrictCat] q1
                 ≈[StrictCat] Diagonal _1 c ∘[StrictCat] q2).

Program Definition Coslice_med : Q ⟶ Coslice C c := {|
  fobj := fun z => (snd ``(q1 z); hom_cast (`1 Hsq z) eq_refl (`2 (q1 z)));
  fmap := fun z w f => (snd ``(fmap[q1] f); _)
|}.
Next Obligation.
  intros z w f; cbv beta.
  transitivity (`2 (q1 w) ∘ id_cast (eq_sym (`1 Hsq w))).
  { exact (hom_cast_right_refl _ _). }
  transitivity (snd ``(fmap[q1] f)
                  ∘ (`2 (q1 z) ∘ id_cast (eq_sym (`1 Hsq z)))).
  2: { apply compose_respects;
         [ reflexivity | symmetry; exact (hom_cast_right_refl _ _) ]. }
  rewrite comp_assoc.
  transitivity ((`2 (q1 w) ∘ fmap[Arrow_dom] (fmap[q1] f))
                  ∘ id_cast (eq_sym (`1 Hsq z))).
  2: { apply compose_respects;
         [ exact (Arrow_square _ _ (fmap[q1] f)) | reflexivity ]. }
  rewrite <- comp_assoc.
  apply compose_respects; [ reflexivity | ].
  etransitivity;
    [ symmetry; exact (id_right (id_cast (eq_sym (`1 Hsq w)))) | ].
  exact (cast_of_hom_cast _ _ _ _
           (hom_cast_flip _ _ _ _ (strict_fmap_cast Hsq f))).
Qed.
Next Obligation.
  intros z w f g Hfg.
  exact (snd (@fmap_respects _ _ q1 z w f g Hfg)).
Qed.
Next Obligation. intros z; exact (snd (@fmap_id _ _ q1 z)). Qed.
Next Obligation.
  intros z w u f g; exact (snd (@fmap_comp _ _ q1 z w u f g)).
Qed.

Lemma Coslice_med_arrow :
  Coslice_Arrow ∘[StrictCat] Coslice_med ≈[StrictCat] q1.
Proof.
  refine (@Build_strict_eq Q (@Arrow C) (Coslice_Arrow ◯ Coslice_med) q1
            (fun z => coslice_arrow_eta c (q1 z) (`1 Hsq z)) _).
  intros z w f; split.
  - etransitivity;
      [ exact (fmap_hom_cast Arrow_dom _ _
                 (fmap[Coslice_Arrow ◯ Coslice_med] f)) | ].
    rewrite (fp_hom_cast_irr uip _ (eq_sym (`1 Hsq z))
                            _ (eq_sym (`1 Hsq w))).
    exact (hom_cast_flip _ _ _ _ (strict_fmap_cast Hsq f)).
  - etransitivity;
      [ exact (fmap_hom_cast Arrow_cod _ _
                 (fmap[Coslice_Arrow ◯ Coslice_med] f)) | ].
    rewrite (fp_hom_cast_irr uip _ eq_refl _ eq_refl).
    reflexivity.
Qed.

Lemma Coslice_med_erase :
  Erase (Coslice C c) ∘[StrictCat] Coslice_med ≈[StrictCat] q2.
Proof.
  refine (@Build_strict_eq Q _1
            (Erase (Coslice C c) ◯ Coslice_med) q2
            (fun z => punit_eq (q2 z)) _).
  intros z w f; simpl.
  match goal with |- ?u = ?v => now destruct u, v end.
Qed.

Lemma Coslice_med_unique (v : Q ⟶ Coslice C c)
      (H1 : Coslice_Arrow ∘[StrictCat] v ≈[StrictCat] q1)
      (H2 : Erase (Coslice C c) ∘[StrictCat] v ≈[StrictCat] q2) :
  v ≈[StrictCat] Coslice_med.
Proof.
  refine (coslice_strict_eq v Coslice_med
            (fun z => coslice_arrow_reflect (v z) (Coslice_med z)
                        (eq_trans (`1 H1 z)
                                  (eq_sym (`1 Coslice_med_arrow z)))) _).
  intros z w f.
  rewrite (fp_hom_cast_irr uip _ (f_equal (fobj[Arrow_cod]) (`1 H1 z))
                          _ (f_equal (fobj[Arrow_cod]) (`1 H1 w))).
  transitivity (fmap[Arrow_cod]
                  (hom_cast (`1 H1 z) (`1 H1 w) (fmap[Coslice_Arrow ◯ v] f))).
  { symmetry;
      exact (fmap_hom_cast Arrow_cod _ _ (fmap[Coslice_Arrow ◯ v] f)). }
  exact (snd (strict_fmap_cast H1 f)).
Qed.

End CosliceMediator.

Definition Coslice_commutes :
  Arrow_dom ∘[StrictCat] Coslice_Arrow
    ≈[StrictCat] Diagonal _1 c ∘[StrictCat] Erase (Coslice C c).
Proof.
  refine (@Build_strict_eq (Coslice C c) C
            (Arrow_dom ◯ Coslice_Arrow)
            (Diagonal _1 c ◯ Erase (Coslice C c))
            (fun _ => eq_refl) _).
  intros x y f; reflexivity.
Defined.

Definition Coslice_IsPullback :
  @IsPullback StrictCat (@Arrow C) _1 C Arrow_dom (Diagonal _1 c)
              (Coslice C c) Coslice_Arrow (Erase (Coslice C c)).
Proof.
  unshelve refine {| is_pullback_commutes := Coslice_commutes |}.
  intros Q q1 q2 Hsq.
  unshelve refine {| unique_obj := Coslice_med q1 q2 Hsq |}.
  - split; [ exact (Coslice_med_arrow q1 q2 Hsq)
           | exact (Coslice_med_erase q1 q2 Hsq) ].
  - intros v [Hv1 Hv2].
    symmetry; exact (Coslice_med_unique q1 q2 Hsq v Hv1 Hv2).
Defined.

End CosliceAsPullback.
