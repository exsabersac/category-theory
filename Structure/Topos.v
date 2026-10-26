Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Subobject.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
 Elementary toposes.

 nLab:      https://ncatlab.org/nlab/show/topos
 nLab:      https://ncatlab.org/nlab/show/power+object
 Wikipedia: https://en.wikipedia.org/wiki/Topos

 An elementary topos is a category with finite limits that is cartesian
 closed and has a subobject classifier.  Finite limits are carried
 EXPLICITLY here as terminal object + binary products + pullbacks, and we
 deliberately do not add equalizers to the class.

 That redundancy is now a CHOICE rather than a gap.  The reduction of
 pullbacks to products and equalizers, and its converse, ARE formalized --
 [Structure/Pullback/Reduction.v]'s [pullback_of_equalizer] /
 [HasPullbacks_of_Cartesian_HasEqualizers] and [equalizer_of_pullback], with
 [Cartesian_of_HasPullbacks_Terminal] and
 [HasEqualizers_of_HasPullbacks_Terminal] going the other way.  The class
 keeps its components explicit anyway, so that an instance may supply
 whichever it computes with and no consumer pays for a reduction it does not
 want.

 Scope that precisely, because the redundancy claim is narrower than “finite
 limits are redundant”: what is related is the BINARY and PARALLEL-PAIR
 generators.  Equalizers ARE now derived for every topos, as
 [Structure/Topos/Monadic.v]'s [topos_HasEqualizers], and finite
 completeness is stated there at the level of the four elementary
 generators -- terminal object, binary products, pullbacks, equalizers --
 as [topos_finitely_complete].  The [Limit]-shaped reading is now
 [Structure/Limit/Finite.v]'s [FinitelyComplete], which
 [finitely_complete_of_pullbacks_terminal] derives from the class's
 terminal object and pullbacks.  Finite COLIMITS are Structure/Topos/
 Colimits.v's [topos_has_finite_colimits] -- Paré's theorem, through the
 monadic power-object functor of [Structure/Topos/Monadic.v] -- again at
 generator level: initial object, binary coproducts, coequalizers, pushouts.

 Universe note: the class is a plain record of the component classes, each
 universe-polymorphic over the ambient category; it introduces no universe
 constraints beyond those of its fields. 

 --------
 初等拓扑。 

 nLab:       https://ncatlab.org/nlab/show/topos 
 nLab:       https://ncatlab.org/nlab/show/power+object 
 维基百科:  https://en.wikipedia.org/wiki/Topos 

 初等拓扑是一个具有有限极限、笛卡尔闭且具有子对象分类器的范畴。这里显式地给出了有限极限，即终对象 + 二元积 + 拉回，并且我们特意没有将等化器加入这一类。 

 这种冗余现在是一种选择，而不是遗漏。将拉回归约为积和等化器及其逆过程已被形式化 --  [Structure/Pullback/Reduction.v] 的  [pullback_of_equalizer] / [HasPullbacks_of_Cartesian_HasEqualizers] 和 [equalizer_of_pullback] ，以及 [Cartesian_of_HasPullbacks_Terminal] 和 [HasEqualizers_of_HasPullbacks_Terminal]  的反向过程。无论如何，这一类仍保持其组成部分的显式性，以便某个实例可以提供它计算出的任意部分，而不需要的使用者不会为不需要的归约付出代价。准确界定这个范围，因为冗余声明比“有限极限是冗余的”更狭窄：相关的是二元和并行对生成器。等化器现在在每个拓扑中都被导出，如 [Structure/Topos/Monadic.v] 的 [topos_HasEqualizers]，并且有限完备性在四个基本生成器的层面上被陈述——终端对象、二元积、拉回、等化器——如 [topos_finitely_complete]。[Limit] 形状的读取现在是 [Structure/Limit/Finite.v] 的 [FinitelyComplete]，它由类的终端对象和拉回导出。有限余极限是 Structure/Topos/Colimits.v 的 [topos_has_finite_colimits]——Paré 定理，通过 [Structure/Topos/Monadic.v] 的幺半幂对象函子——仍然是在生成器层面：初始对象、二元余积、共等化器、推出。宇宙注释：该类是组件类的一个简单记录，每个组件类都在其所在类别下具有宇宙多态性；它不引入超出其字段之外的宇宙约束。
*)

(*
 Where toposes come from, and what they are for

 nLab:      https://ncatlab.org/nlab/show/topos
 Wikipedia: https://en.wikipedia.org/wiki/Lawvere%E2%80%93Tierney_topology
 Book:  Artin, Grothendieck, Verdier, “Théorie des topos et cohomologie
 étale des schémas” (SGA 4), Lecture Notes in Mathematics 269,
 270, 305, Springer, 1972-1973
 Paper: Lawvere, “Quantifiers and Sheaves”, Actes du Congrès
 International des Mathématiciens (Nice 1970), vol. 1,
 Gauthier-Villars, 1971, pp. 329-334

 An elementary topos is at once a generalized universe of sets and a
 categorical model of higher-order intuitionistic logic, and the
 tension between those two readings is why the concept repays study
 (nLab, “topos”; Mac Lane, Moerdijk, “Sheaves in Geometry and Logic”,
 Springer 1992).  Set is the prototype of the first reading: every
 construction one performs on sets — products, function spaces, power
 sets, subsets cut out by a predicate — has a counterpart in an
 arbitrary topos, an abstract context for doing mathematics.

 Two lineages converged on the definition recorded above.  Grothendieck
 and his school introduced toposes around 1963-1964 as generalized
 spaces adequate for sheaf cohomology — the étale cohomology built to
 study the Weil conjectures — a Grothendieck topos being the category
 of sheaves on a small site (SGA 4, Tome 1, exposé IV “Topos”, by
 Grothendieck and Verdier).  Independently, around 1969-1970, Lawvere
 and Tierney isolated a first-order, finitely axiomatizable description:
 a category with finite limits that is cartesian closed and carries a
 subobject classifier.  The adjective “elementary” marks exactly this,
 that the axioms pass almost directly into first-order logic, unlike the
 site-and-sheaf construction.  The description grew out of Lawvere's
 structural account of the category of sets (Lawvere, “An elementary
 theory of the category of sets”, Proc. Natl. Acad. Sci. USA 52, 1964),
 which had already isolated the properties of Set that became the
 axioms — a structural, pluralistic alternative to ZF set theory.

 The subobject classifier is the component binding the two readings.
 In Set it is the two-element set 2, and a subset is the same datum as
 its characteristic function into 2, recovered as the pullback of the
 point true : 1 ~> 2.  An arbitrary topos replaces 2 by an object Ω, so
 that subobjecthood becomes representable: every mono is the pullback
 of one generic mono [truth] : 1 ~> Ω along a unique classifying map,
 which is the content of [classifier_classifies] of
 Structure/SubobjectClassifier.v.  Exponentiating gives the power
 object [Pow] a := Ω ^ a, the categorical power set, and [relations_iso]
 reads a subobject of a × b — an element of [SubObj] (a × b), a relation
 between a and b — as a map a ~> [Pow] b, currying its classifying
 predicate through the transpose [exp_iso].

 Under the logical reading Ω is the object of truth values, and the
 subobjects of any object form a Heyting algebra rather than a Boolean
 one, so the law of excluded middle and the axiom of choice need not
 hold internally while the remainder of higher-order reasoning goes
 through.  This internal type theory is the Mitchell-Bénabou language
 of the topos, its quantifiers appearing as adjoint functors.  Lawvere
 and Tierney observed that a Grothendieck topology is encoded by an
 idempotent, finite-meet-preserving endomorphism j : Ω ~> Ω; these
 Lawvere-Tierney topologies cut out the subtoposes as categories of
 sheaves, internalizing Grothendieck's construction (Lawvere 1971;
 Tierney).  Giraud's theorem (1972) closes the circle: an elementary
 topos with a small generating set, all small colimits, coproducts
 disjoint and universal, and equivalence relations effective is exactly
 a category of sheaves on a small site.

 The library exercises both readings.  Construction/Slice.v records the
 fundamental theorem of topos theory — every slice of a topos is again
 a topos (McLarty, “Elementary Categories, Elementary Toposes”, Oxford
 University Press 1992) — and names [ElementaryTopos] as its target;
 Theory/Sheaf/Category.v carries the generalized-space side as sheaves
 inside presheaves; Adjunction/SAFT.v draws on the same subobject
 vocabulary through well-poweredness.  (CORRECTION, #451: what SAFT.v
 consumes is its [SubobjectIndex], a family of monos with no
 exhaustiveness clause, not well-poweredness; that is Structure/
 WellPowered.v's [WellPowered], which Adjunction/SAFT/WellPowered.v
 feeds to [SAFT].)  Computationally Ω is a type of
 truth values and the classifying [char] is the decision procedure of a
 subobject, so the classification isomorphism reads a subobject as its
 own membership predicate.  Skeletal FinSet makes this literal
 ([FinSet_Skeletal], Instance/FinSet/Skeleton.v): Ω is 2,
 the classifying map is a decidable finite search, and the assembled
 [ElementaryTopos] witness [FinSet_Topos] of Instance/FinSet/Topos.v
 reduces, with [Pow] 2 evaluating to 4 by eq_refl.  In Sets the
 truth-value setoid of Instance/Sets/Classifier.v lives one universe
 up, and those cross-universe theorems are still what that file
 proves; but a ONE-LEVEL classifier does exist CONDITIONALLY, in
 Instance/Sets/Classifier/OneLevel.v under [Untruncate] or
 [DecImage] (neither inhabited axiom-free in this tree), and with it
 Instance/Sets/Topos.v assembles a whole conditional
 [ElementaryTopos Sets] -- where [Pow] b is [Powerset_Prop_obj] b by
 eq_refl, Mac Lane's “P b, the set of all subsets s of b” being
 definitional there.  Instance/Fun/Topos.v does the same for presheaf
 categories over Instance/Fun/Classifier.v's sieve classifier, and
 Seven Sketches' covariant reading with it.  READ THE REACH OF THOSE
 TWO EXACTLY: both are genuine inhabitants of this class, so [Pow] and
 the results of Structure/Topos/{Monadic,Colimits}.v apply at them,
 but NEITHER [classifier_classifies] NOR [relations_iso] is statable
 at either -- both carry objects <= homs, which neither [Sets] nor a
 presheaf category satisfies -- so the FinSet witness is still the
 only one for those two, and the four refusals are pinned in
 Test/ProbeToposInstances404.v. 

 --------
 拓扑的来源及其用途

 nLab:       https://ncatlab.org/nlab/show/topos 
 维基百科:  https://en.wikipedia.org/wiki/Lawvere%E2%80%93Tierney_topology 
 书籍:  Artin, Grothendieck, Verdier, 《拓扑论与概形的Étale上同调》(SGA 4), 数学讲义 269, 270, 305, Springer, 1972-1973
 论文: Lawvere, 《量词与层》, 国际数学家大会论文集 (尼斯 1970), 第1卷, Gauthier-Villars, 1971, 页 329-334初等拓扑既是集合的广义宇宙，又是高阶直觉逻辑的范畴模型，而这两种理解之间的张力正是该概念值得研究的原因（nLab，“topos”；Mac Lane, Moerdijk，《几何与逻辑中的层》，施普林格，1992年）。Set 是第一种理解的原型：对集合进行的每一个构造——积、函数空间、幂集、由谓词切出的子集——在任意一个拓扑中都有对应物，这是做数学的一个抽象背景。两个血统汇聚于上面记录的定义。Grothendieck 及其学派在 1963-1964 年左右引入了拓扑体（toposes），作为适合于层上同调的广义空间——为了研究魏尔猜想而构建的 étale 同调——Grothendieck 拓扑体是小型站点上层的范畴（SGA 4, Tome 1, exposé IV “Topos”，由 Grothendieck 和 Verdier 编写）。独立地，在 1969-1970 年左右，Lawvere 和 Tierney 分离出一个一阶、有限公理化的描述：一个具有有限极限的范畴，它是笛卡尔闭合的，并且携带一个子对象分类器。“初等”这个形容词恰恰标记了这一点，即公理几乎可以直接转入一阶逻辑，这不同于站点-层构造。该描述源自劳威尔对集合范畴的结构性描述（Lawvere，《集合范畴的一个初等理论》，美国国家科学院院刊 52, 1964），该描述已经提炼出了成为公理的集合的性质——一种作为 ZF 集合论的结构性、多元化的替代方案。子对象分类器是将两种读法联系起来的组件。在 Set 中，它是二元集合 2，而一个子集与其进入 2 的特征函数是相同的数据，通过点 true : 1 ~> 2 的拉回可以恢复。在任意拓扑空间中，用对象 Ω 代替 2，从而子对象性质变得可表示：每个单射都是一个通用单射 [truth] : 1 ~> Ω 沿唯一的分类映射的拉回，这就是 Structure/SubobjectClassifier.v 中 [classifier_classifies] 的内容。指数化得到幂对象 [Pow] a := Ω ^ a，范畴的幂集，并且 [relations_iso] 将 a × b 的子对象——[SubObj](a × b) 的一个元素，即 a 与 b 之间的关系——解读为映射 a ~> [Pow] b，将其分类谓词通过转置 [exp_iso] 进行柯里化。在逻辑解读下，Ω 是真值的对象，而任何对象的子对象形成的是 Heyting 代数而不是布尔代数，因此排中律和选择公理在内部不必成立，而高阶推理的其余部分仍然有效。这种内部类型理论就是上题的 Mitchell-Bénabou 语言，其量词表现为伴随函子。Lawvere 和 Tierney 观察到，Grothendieck 拓扑可以通过一个幂等、保持有限交的自同态 j : Ω ~> Ω 来编码；这些 Lawvere-Tierney 拓扑切出作为层的子拓扑作为范畴，将 Grothendieck 的构造内部化（Lawvere 1971；Tierney）。吉罗定理（1972）闭合了这个循环：一个具有小生成集、所有小余极限、不可交且普遍的并积以及有效等价关系的初等拓扑正好是一个小点集上的层范畴。该图书馆同时运用了两种阅读方式。Construction/Slice.v 记录了拓扑理论的基本定理——每个拓扑的切片依然是一个拓扑（McLarty，《Elementary Categories, Elementary Toposes》，牛津大学出版社，1992）——并将 [ElementaryTopos] 指定为其目标；Theory/Sheaf/Category.v 将广义空间方面表现为预层中的层；Adjunction/SAFT.v 通过良定幂性引用了相同的子对象词汇。(更正，#451：SAFT.v 所消耗的是它的 [SubobjectIndex]，一个没有穷尽性条款的单象族，而不是良好幂性；那是 Structure/WellPowered.v 的 [WellPowered]，Adjunction/SAFT/WellPowered.v 将其传递给 [SAFT]。) 计算上，Ω 是一种真值类型，而分类 [char] 是子对象的判定过程，因此分类同构将子对象读作其自身的成员谓词。Skeletal FinSet 使这个字面意义清晰（[FinSet_Skeletal], Instance/FinSet/Skeleton.v）：Ω 是 2，分类映射是可判定的有限搜索，并且组装的 [ElementaryTopos] 证据 [FinSet_Topos]（Instance/FinSet/Topos.v）通过 eq_refl 将 [Pow] 的 2 评估为 4。在 Sets 中，Instance/Sets/Classifier.v 的真值集合模组位于高一层宇宙中，而那些跨宇宙的定理仍然是该文件所证明的；但是一个单层分类器在条件下确实存在，位于 Instance/Sets/Classifier/OneLevel.v 中，在 [Untruncate] 或 [DecImage] 下（在此树中都不是有定居主义的无公理情况），并且借助它，Instance/Sets/Topos.v 组装了一个完整的条件 [ElementaryTopos Sets]——其中 [Pow] b 通过 eq_refl 等于 [Powerset_Prop_obj] b，Mac Lane 的“P b，b 的所有子集 s 的集合”在此处为定义形式。Instance/Fun/Topos.v 对 Instance/Fun/Classifier.v 的篱笆分类器上的预层范畴做了同样的处理，并且配合 Seven Sketches 的协变解读使用。精确阅读这两个的涵盖范围：它们都是这个类别的真正成员，因此 [Pow] 以及 Structure/Topos/{Monadic,Colimits}.v 的结果在它们上都适用，但 [classifier_classifies] 和 [relations_iso] 都不能在它们上表述——它们都携带对象 <= 态射，而 [Sets] 或 presheaf 类别都不满足——所以 FinSet 的例证仍然是这两个的唯一例证，这四个拒绝情况记录在 Test/ProbeToposInstances404.v 中。
*)

Class ElementaryTopos (C : Category) := {
  topos_terminal   : @Terminal C;
  topos_cartesian  : @Cartesian C;
  topos_pullbacks  : @HasPullbacks C;
  topos_closed     : @Closed C topos_cartesian;
  topos_classifier : @SubobjectClassifier C topos_terminal
}.

#[export] Existing Instance topos_terminal.
#[export] Existing Instance topos_cartesian.
#[export] Existing Instance topos_pullbacks.
#[export] Existing Instance topos_closed.
#[export] Existing Instance topos_classifier.

(*
 The power object of a: the exponential Ω^a.  Mind the argument order of
 Structure/Cartesian/Closed.v: [exponent_obj x y] displays as y ^ x, so
 [Ω ^ a] is [exponent_obj a Ω]. 

 --------
 a 的幂对象：指数 Ω^a。注意 Structure/Cartesian/Closed.v 的参数顺序：[exponent_obj x y] 显示为 y ^ x，所以 [Ω ^ a] 是 [exponent_obj a Ω]。
*)
Definition Pow {C : Category} {H : ElementaryTopos C} (a : C) : C := Ω ^ a.

(*
 The relations isomorphism: subobjects of a × b (relations between a and b)
 correspond to morphisms a ~> Pow b, as an isomorphism of setoids in Sets.
 It is the composite of the classification isomorphism

 SubObj (a × b)  ≅  (a × b ~> Ω)       (classifier_classifies)

 with the exponential transpose

 (a × b ~> Ω)  ≅  (a ~> Ω^b)           (exp_iso)

 Orientation: the in-tree [exp_iso] of Structure/Cartesian/Closed.v curries
 the SECOND factor of the product — Hom(x × y, z) ≅ Hom(x, z^y) — so the
 relation's first leg a is the remaining source and its second leg b is the
 exponent: SubObj (a × b) ≅ (a ~> Pow b).  Both directions and the round
 trips come from composing the two isomorphisms in Sets. 

 --------
 关系同构：a × b 的子对象（a 和 b 之间的关系）对应于态射 a ~> Pow b，作为 Sets 中集合代数的同构。它是分类同构的复合

 SubObj (a × b)  ≅  (a × b ~> Ω)       (classifier_classifies)

 与指数转置

 (a × b ~> Ω)  ≅  (a ~> Ω^b)           (exp_iso)

 的组合。

 方向：Structure/Cartesian/Closed.v 中的树内 [exp_iso] 对积的第二个因子进行柯里化 — Hom(x × y, z) ≅ Hom(x, z^y) — 因此关系的第一条腿 a 是剩余的源，第二条腿 b 是指数：SubObj (a × b) ≅ (a ~> Pow b)。两个方向及循环过程来自于在 Sets 中组合这两个同构。
*)
Definition relations_iso {C : Category} {H : ElementaryTopos C} (a b : C) :
  @Isomorphism Sets {| carrier := SubObj (a × b) |}
                    {| carrier := a ~> Pow b |} :=
  iso_compose exp_iso (classifier_classifies (a × b)).
