Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Product.Limit.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.Pullback.Wide.Complete.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Discrete.Reconstruct.

Generalizable All Variables.

(* * * Well-powered and co-well-powered categories / * * 强幂范畴和共强幂范畴 *)

(*
 nLab:      https://ncatlab.org/nlab/show/well-powered+category
 nLab:      https://ncatlab.org/nlab/show/subobject
 Wikipedia: https://en.wikipedia.org/wiki/Subobject

 Mac Lane, "Categories for the Working Mathematician", 2nd ed., §V.8,
 book p. 130 (PDF p. 139): a category is WELL-POWERED when the subobjects
 of each object form a small set, and CO-WELL-POWERED when the quotient
 objects of each object do.  The notion is the size hypothesis of the
 special adjoint functor theorem: with it, a small-complete category has
 the intersection of any collection of subobjects of an object, because
 the collection can be reindexed by a small set before the wide pullback
 is taken.  mathlib states the same thing as the class [WellPowered.{w}],
 asking that [Subobject X] be [w]-small, and names [w] = the hom
 universe as the common case.

 ** The definition, and where its content lies

 A subobject of x is Theory/Subobject.v's [SubObj x], a mono into x, and
 two subobjects are the same when the setoid [SubObj_Setoid] relates
 them (an isomorphism of domains over x).  "The subobjects of x form a
 small set" is read here as a small INDEX together with maps both ways
 that EXHAUST the subobjects: [WellPoweredAt x] carries [wp_index],
 [wp_to : wp_index → SubObj x], [wp_from : SubObj x → wp_index] and the
 exhaustiveness clause [wp_to_from : wp_to (wp_from u) ≈ u].  That is a
 bijection onto the setoid of ALL subobjects: pulling [SubObj_Setoid]
 back along [wp_to] ([wp_index_setoid]) makes [wp_to] respect and
 reflect the equivalence by definition, [wp_from] respect it
 ([wp_from_resp]) and [wp_from ∘ wp_to] the identity up to it
 ([wp_from_to]).  No second record repeats those fields: the one clause
 that cannot be derived is exhaustiveness.

 Adjunction/SAFT.v's [SubobjectIndex] is the family of monos WITHOUT the
 exhaustiveness clause, and so is strictly weaker: the empty family
 inhabits it at every object (that file's [empty_SubobjectIndex] and
 [SubobjectIndex_not_exhaustive]).  The bridge from [WellPowered] to it
 is the satellite Adjunction/SAFT/WellPowered.v's
 [WellPowered_SubobjectIndex], with [SAFT_of_WellPowered] beside it.

 The content of the definition is its UNIVERSE.  Left free, the index can
 be [SubObj x] itself with [wp_to] and [wp_from] the identity
 ([wp_trivial] below), and every category is "well-powered".
 [WellPowered] therefore pins the index at or below the hom universe,
 [w <= h]: the book's small sets are the size of its hom-sets,
 mathlib's common case is the same, and Adjunction/SAFT.v's statement
 of [SAFT] already puts the bound [u3 <= h] on its [SubobjectIndex]
 datum.  The
 per-object record [WellPoweredAt] is left unpinned so that a witness
 one universe up can still be STATED, and compared with the pinned
 notion.

 "Small" is therefore relative to the category's OWN hom universe, as in
 mathlib's [WellPowered.{v}].  A category whose hom universe is a free
 parameter, as a thin category's is, can be instantiated with its homs
 raised, and then passes the pin: Structure/WellPowered/
 Counterexample.v's [AntichainTop] is refuted at the pin when its homs
 sit at or below the types its objects name, and its top object has a
 pinned datum when they sit above ([AntichainTop_WellPoweredAt_up]); the
 powerset lattices of Instance/Powerset/WellPowered.v are well-powered
 through [trivial_small] once the homs are raised to the objects.  The
 pin excludes something only where the hom universe is tied to the
 objects' carriers, as in [Sets] and the algebraic categories, or where
 a free one is instantiated low.

 [CoWellPowered C] is [WellPowered (C^op)], and its subobjects are
 Theory/Subobject/Quotient.v's quotient objects on the nose:
 [quot_obj_is_sub_op] and [quot_setoid_is_sub_setoid_op] hold by
 [eq_refl].

 ** The consequence: intersections

 The consequence named at the head of this essay -- a well-powered
 small-complete category has the intersection of any collection of
 subobjects of an object -- is proved below in two forms, and the
 difference between them is the content of well-poweredness.

 SMALL FAMILIES NEED NO WELL-POWEREDNESS.  [complete_intersection] and
 [complete_intersection_IsIntersection] intersect EVERY family
 [S : J → SubObj x] whose index lies at or below [Complete]'s
 shape-object universe, from completeness alone: the wide pullback of
 the monos comes from Structure/Pullback/Wide/Complete.v's
 [complete_wide_pullback], and Theory/Subobject/Lattice.v's
 [sub_wide_intersection] reads it as a subobject.  That reading needs a
 point of the index, so the family is first extended by [sub_top] over
 [option J] ([sub_opt_top]); adding the top changes no lower bound
 ([IsIntersection_drop_top]), so the empty family is covered too, with
 no nonemptiness hypothesis.  A statement about families indexed at
 [Complete]'s own shape universe is therefore NOT the §V.8 consequence.

 CLASSES OF SUBOBJECTS NEED IT.  A "collection of subobjects" is a
 collection of equivalence classes; in setoid discipline it is a
 predicate [P] on the large type [SubObj x] closed under ≈ ([HP]).  Its
 members form a
 family indexed by [{ m : SubObj x & P m }], which lives at the OBJECT
 universe, above the shape universe whenever objects sit above homs.
 [wellpowered_complete_has_intersections] intersects it by reindexing
 over the small [wp_class_index] = [{ i : wp_index W & P (wp_to W i) }]:
 [IsIntersection_reindex] carries membership along [wp_to (wp_from m) ≈
 m] with [HP] and the bound back with [sub_le_of_equiv].  Only the four
 fields of [WellPoweredAt] are consumed; the derived bijection is not
 needed.  The [Prop]-valued form ([_prop]) puts no size condition on
 [P]; [wellpowered_complete_intersection_all] is the class of ALL
 subobjects, indexed by [SubObj x] itself, and
 [wellpowered_complete_least_subobject] reads it as the least subobject.
 Necessity is measured, in scratch files at the regime the adjoint
 functor theorems use ([C : Category@{o h h}], [h < o],
 [comp : Complete@{h h h o}]): [complete_intersection_IsIntersection
 comp (fun k : { m : SubObj x & P m } => `1 k)] is refused with "cannot
 ensure that Type@{max(o,h)} is a subtype of Type@{...}", and so is the
 identity family on [SubObj x], while [wellpowered_complete_has_
 intersections] and [wellpowered_complete_intersection_all] are
 accepted at the same regime given [WellPowered C]; at [Sets@{o so}]
 with [Sets_Complete], the identity family on [SubObj X] is refused
 with "Cannot enforce o = ... because o < so <= ..." (the chain as
 printed with [X : Sets@{o so}] a [Section] [Context]; with [X] a
 binder of the definition, Rocq 9.1.1 prints an unnamed universe in
 the place of [so], as Test/ProbeWellPowered451.v's N7 records), and
 accepted through [wellpowered_complete_intersection_all] given
 [WellPowered Sets].

 WHY CLASSES AND NOT ARBITRARY LARGE FAMILIES.  For [S : J → SubObj x]
 with [J : Type@{o}], two readings suggest themselves, and both are
 refused (measured at the same regime).  The typed image [fun m => { j
 : J & S j ≈ m }] is as large as [J]: "Cannot enforce o <= ... because
 ... < o".  The [Prop]-truncated image [fun m => ex (fun j => inhabited
 (S j ≈ m))] is ≈-closed and IS accepted, and its intersection is a
 lower bound of every [S j]; but showing a lower bound of [S] to be below
 it needs a member of [S] out of the truncated witness, and that step is
 refused with "Incorrect elimination ... in the inductive type ex ...
 the return type has sort Type@{h} while it should be SProp or Prop"
 (as printed under [Set Printing Universes] with [h] a named universe;
 the default printing gives "Type" in place of "Type@{h}").
 That route needs unique choice to eliminate the truncated witness into
 the [Type]-valued [sub_le]; no other route was measured, and nothing
 here shows that every route needs it.  The class form is both the
 faithful reading of the book and the strongest form proved here.

 THE DUAL.  [cowellpowered_cocomplete_has_cointersections] is the
 theorem read at [C^op] through Construction/Product/Limit.v's
 [Complete_op_of_Cocomplete], in one line; [cointersection_quot_le]
 reads its lower bound in Theory/Subobject/Quotient.v's [quot_le] with no
 conversion step.  The result is called a cointersection here;
 Quotient.v calls the same greatest lower bound in [quot_le]
 [quot_wide_meet].

 STRENGTHS, measured.  The intersection is data: [IsIntersection]
 carries the [sub_le] factorizations, and every constant of this file
 that builds them is [Defined].  Not all of it computes.  The
 criterion is [eq_refl] at a category where the answer is known,
 [Indiscrete bool] completed by [Indiscrete_Complete true], every hom
 being [unit]:

 - the lower-bound half computes.  The product mediators of
 Structure/Pullback/Wide/Complete.v ([unique_obj (iprod_ump ...)])
 and the legs [wide_pullback_proj (complete_wide_pullback comp f) j]
 reduce to [tt] by [eq_refl].  Every [inter_le] of
 [complete_intersection] is such a leg, and the class form composes
 it with the isomorphism of [wp_to_from], which computes as far as
 the witness's own exhaustiveness proof does;
 - the greatest-lower-bound half does not.  The wide pullback's
 mediator [unique_obj (ump_wide_pullbacks (complete_wide_pullback
 comp f) q Hq)], from which every [inter_greatest] factorization is
 built, is refused at [eq_refl] by conversion ("cannot unify ...
 and ()"), and [Eval cbv] stops at [unique_obj (eq_desc
 (equalizer_of_pullback_awodey ...))].  Structure/Pullback/
 Reduction.v's [equalizer_of_pullback_awodey] is [Qed] and returns
 an [IsEqualizer], whose [eq_desc] is the equalizer's mediator: the
 factorization is data that reduces only up to that opaque
 constant.  Adjunction/GAFT.v's [Complete_HasEqualizers] would not
 help: at the same category its mediator stops at Structure/
 Equalizer/Fork.v's [limit_equalizer_desc], also [Qed].

 [Print Opaque Dependencies wellpowered_complete_has_intersections]
 lists 63 constants.  Besides [equalizer_of_pullback_awodey], two more
 carry data: Theory/Subobject.v's [SubObj_Setoid_obligation_1], the
 equivalence on subobjects, whose members are isomorphisms, and
 Structure/Pullback/Limit.v's [Pullback_to_Universal_obligation_2], an
 [∃!] mediator; reading the statements of the rest, they are
 ≈-equations, monicity, [Program] obligations of the shapes, and
 setoid-rewriting lemmas.  Making the factorizations compute would
 start with flipping [equalizer_of_pullback_awodey] to [Defined]; that
 is not attempted here.  The subobject that
 [wellpowered_complete_has_intersections] returns IS, by [eq_refl], the
 [complete_intersection] of the small reindexed family
 ([wellpowered_intersection_is_small]).  Uniqueness is Lattice.v's
 [IsIntersection_unique], up to ≈ and not re-proved here.

 UNIVERSES, measured with [Set Printing Universes. About ...], stdlib
 bounds omitted.  In the first, unannotated elaboration minimization
 collapsed universes the statements keep apart: the index [w] onto the
 hom universe and [r] onto [so] in [wellpowered_complete_has_
 intersections] and in [cointersection_quot_le], the family index [q]
 onto [s] in [wellpowered_complete_intersection_all], and the index [j]
 onto [so] in [complete_intersection_IsIntersection].  The binders are
 therefore load-bearing:

 wellpowered_complete_has_intersections@{o h w s t r so p q u u0 u1 u2} :
 ∀ {C : Category@{o h h}}, WellPowered@{o h w s t} C →
 Complete@{r so h o} → ∀ (x : obj[C]) (P : SubObj@{o h} x → Type@{p}),
 (∀ m m', m ≈ m' → P m → P m') →
 ∃ w, IsIntersection@{o h q} (λ k : ∃ m, P m, `1 k) w
 ( * w <= h, h < t, o <= s, h <= s, so <= r, h <= r, w <= so, p <= so,
 o <= q, h <= q, p <= q, and internal ones * )

 The two bounds that matter are [w <= so] and [p <= so]: the index and
 the class's universe must fit [Complete]'s shape objects.  Nothing ties
 [h] to [so], and at the adjoint-functor regime ([so = h]) the pin
 [w <= h] is exactly what is asked.  [complete_intersection@{o h r so j
 ...}] carries [j <= so] for the family's index [j], and nothing else of
 note.

 ** Witnesses

 [trivial_small]: a category whose objects sit at or below its homs is
 well-powered ([o <= h]), with the trivial index.  [wp_groupoid] and
 [Groupoid_WellPowered]: a category in which every arrow is invertible
 (Structure/Groupoid.v's [IsGroupoid]) is well-powered with the
 one-point index, at EVERY object universe; its opposite is again one
 ([IsGroupoid_op] of Structure/Groupoid.v), so [Groupoid_CoWellPowered] too.  Instances:
 [DiscreteCat_WellPowered], [Indiscrete_WellPowered] and their
 co-well-powered twins, and [DiscreteCat_types_WellPowered] at
 [DiscreteCat@{o j j} Type@{j}], objects strictly above homs with the
 index at [Set].  [wp_of_classifier] and [Classifier_WellPowered]: a
 subobject classifier over pullbacks indexes the subobjects of x by
 [x ~> Ω], at the hom universe with no bound between objects and homs;
 Instance/FinSet/WellPowered.v instantiates it at FinSet.  The
 refutation side is Structure/WellPowered/Counterexample.v: a thin
 category, [AntichainTop], built without axioms, that is provably not
 well-powered at the pin.

 Elsewhere in tree: Instance/Sets/WellPowered.v ([Sets] well-powered
 and co-well-powered one universe up, well-powered at the pin under
 [Untruncate], and the consequence at [Sets] under the same
 hypothesis), Instance/Grp/WellPowered.v ([Grp] well-powered one
 universe up), Instance/Powerset/WellPowered.v (the consequence at the
 powerset lattice of a setoid, unconditionally), Adjunction/SAFT/
 WellPowered.v (the bridge to Adjunction/SAFT.v's [SubobjectIndex]),
 and, since #452, Adjunction/SAFT/InitialObject.v (the special
 initial-object theorem's well-powered corollary) with its witnesses
 Adjunction/SAFT/InitialObject/Examples.v and Instance/Sets/
 SpecialInitial.v; and, since #454, Instance/Mod/WellPowered.v ([RMod R]
 well-powered and co-well-powered one universe up unconditionally, and
 both at the pin under [Untruncate]).

 ** Non-vacuity of the consequence

 The tree's [Complete] instances were searched (every definition of a
 constant named [*Complete*] with type [@Complete ...] under Instance/,
 Structure/ and Construction/) for one that is well-powered at the pin
 in a form the theorem accepts, as written.  [Sets] and [Grp] are
 shown well-powered constructively only one universe up (Instance/Sets/
 WellPowered.v's [Sets_WellPoweredAt_up], Instance/Grp/WellPowered.v's
 [Grp_WellPoweredAt_up]; this parenthesis said "the other algebraic
 categories were not measured", which is corrected here: since #454
 Instance/Mod/WellPowered.v shows [RMod R] well-powered one universe up
 unconditionally ([RMod_WellPoweredAt_up]) and at the pin under
 [Untruncate] ([RMod_WellPowered_untruncate]), and co-well-powered the
 same two ways ([RMod_CoWellPoweredAt_up],
 [RMod_CoWellPowered_untruncate]), and the remaining algebraic
 categories are still unmeasured), and [Sets] is well-powered
 at the pin only under [Untruncate] ([Sets_WellPowered_untruncate]);
 the presheaf categories of [Presheaf_Complete] have a classifier only
 under a hypothesis:
 Instance/Fun/Classifier.v's [Fun_Classifier] takes [Untruncate] and
 its [Fun_Classifier_IEM] takes [IEM].  [SmallOrd_op_Complete]
 (Instance/Ordinal/Large.v) is thin and [trivial_small] applies to it
 with the homs raised to the objects, but its shape-object universe
 lies strictly below its objects, and feeding that witness to
 [wellpowered_complete_intersection_all] is refused with "Cannot
 enforce ... = ... because ... < ..." (measured).  [Subsets_Complete]
 (Instance/Powerset.v) is written with its homs at [Set] and its
 objects above; restated at a free hom level it is Instance/Powerset/
 WellPowered.v's [Subsets_Complete_free], and that satellite applies
 the theorem at the powerset lattice of any setoid, unconditionally and
 non-degenerately ([Subsets_intersection_all_not_top]), with the
 objects at or below the homs so that [trivial_small] is the witness.
 This file supplies the instance with objects strictly above homs:
 [Indiscrete_Complete] makes every inhabited indiscrete category
 complete, and [Indiscrete_types_has_intersections] applies the theorem
 at [Indiscrete@{o j j} Type@{j}] ([j < o]), where [trivial_small] is
 out of reach.  That instance is degenerate (every subobject there is
 the top one).  Of the instances of the consequence in tree, none has
 both objects strictly above homs and a non-degenerate subobject
 lattice unconditionally; Instance/Sets/WellPowered.v's
 [Sets_wellpowered_intersection] has both under [Untruncate].

 ** Not delivered

 No well-poweredness witness for [Sets], [Grp] or any algebraic
 category in this file (they are the satellites named under Witnesses).
 No intersection theorem over [FinitelyComplete] or over a
 [HasWidePullbacks] that is not derived from [Complete];
 Theory/Subobject/Lattice.v's [sub_intersection] already covers the
 latter for small NONEMPTY families (it takes a point of the index;
 [sub_opt_top] is how this file avoids needing one).  No statement that
 a well-powered category has intersections of ARBITRARY large families,
 for the reason given above.  No wide-pushout
 vocabulary: the dual runs through [C^op], exactly as Quotient.v's
 [quot_wide_meet] does. 

 --------
 nLab:       https://ncatlab.org/nlab/show/well-powered+category 
 nLab:       https://ncatlab.org/nlab/show/subobject 
 维基百科:  https://en.wikipedia.org/wiki/Subobject 

 Mac Lane，《为工作数学家准备的范畴》，第二版，第§V.8节，
 书本第130页（PDF第139页）：当每个对象的子对象形成一个小集合时，范畴称为良有幂（WELL-POWERED），而当每个对象的商对象形成一个小集合时，称为共良有幂（CO-WELL-POWERED）。这一概念是特殊伴随函子定理的大小假设：在有了它之后，一个小完备的范畴可以对一个对象的任何子对象集合取交集，因为在进行广拉回之前可以通过一个小集合对该集合重新编号。mathlib 将其表述为类 [WellPowered.{w}] ，要求 [Subobject X] 为 [w]-小，并将 [w] 命名为同态宇宙作为常见情况。

 ** 定义及其内容所在x 的子对象是 Theory/Subobject.v 中的 [SubObj x]，它是进入 x 的单射，当集合等价 [SubObj_Setoid] 关联它们（一个在 x 上域的同构）时，两个子对象被认为是相同的。这里“x 的子对象形成一个小集合”被理解为一个小索引以及双向映射，它们覆盖了所有子对象：[WellPoweredAt x] 承载 [wp_index]、[wp_to : wp_index → SubObj x]、[wp_from : SubObj x → wp_index] 以及覆盖性条款 [wp_to_from : wp_to (wp_from u) ≈ u]。这是一个指向所有子对象集合等价的双射：沿 [wp_to] 拉回 [SubObj_Setoid]（[wp_index_setoid]）使 [wp_to] 按定义尊重并反映等价，[wp_from] 尊重它（[wp_from_resp]），[wp_from ∘ wp_to] 在其上是恒等的（[wp_from_to]）。没有第二个记录会重复这些字段：唯一无法推导的条款是覆盖性。Adjunction/SAFT.v 的 [SubobjectIndex] 是没有穷尽条款的单态族，因此严格来说更弱：空族在每个对象上都属于它（该文件的 [empty_SubobjectIndex] 和 [SubobjectIndex_not_exhaustive]）。从 [WellPowered] 到它的桥梁是卫星 Adjunction/SAFT/WellPowered.v 的 [WellPowered_SubobjectIndex]，并且旁边有 [SAFT_of_WellPowered]。定义的内容就是它的宇宙。若不受限制，索引可以是 [SubObj x] 本身，并且 [wp_to] 与 [wp_from] 是恒等的（见下文 [wp_trivial]），并且每个范畴都是“良幂”的。因此 [WellPowered] 将索引固定在同质宇宙之下或之等，[w <= h]：书中的小集合与其同质集合的大小相同，mathlib 的常见情况也是如此，而 Adjunction/SAFT.v 对 [SAFT] 的陈述已经对其 [SubobjectIndex] 数据设定了 [u3 <= h] 的界限。每个对象的记录 [WellPoweredAt] 保持未固定状态，这样可以为更高一个宇宙的证据仍然陈述并与固定的概念进行比较。因此，“小”是相对于该范畴自身的 Hom 宇宙而言的，例如 mathlib 的 [WellPowered.{v}]。一个 Hom 宇宙是自由参数的范畴（例如薄范畴），可以对其 Homs 提升后进行实例化，然后通过 pin：当其 Homs 位于或低于其对象命名的类型时，Structure/WellPowered/Counterexample.v 的 [AntichainTop] 在 pin 时被反驳，而当它们位于对象之上时，其顶层对象具有固定数据（[AntichainTop_WellPoweredAt_up]）；Instance/Powerset/WellPowered.v 的幂集格在将 Homs 提升到对象后，通过 [trivial_small] 是 well-powered 的。Pin 仅在 Hom 宇宙与对象载体绑定时排除某些内容，例如 [Sets] 和代数范畴，或者自由 Hom 的实例化位于低层时才排除。[CoWellPowered C] 是 [WellPowered (C^op)]，它的子对象是
 Theory/Subobject/Quotient.v 中的商对象本身：
 [quot_obj_is_sub_op] 和 [quot_setoid_is_sub_setoid_op] 由
 [eq_refl] 保持。

 ** 结论：交集

 本文开头提到的结论——一个良幂小完备范畴对于一个对象的任意子对象集合都有交集——将在下面以两种形式证明，它们之间的差异就是良幂性的内容。小型族不需要良好幂。[complete_intersection] 和 [complete_intersection_IsIntersection] 与每一个族 [S : J → SubObj x] 相交，其索引位于或低于 [Complete] 的形状对象宇宙，仅凭完整性即可：单射的宽拉回来自 Structure/Pullback/Wide/Complete.v 的 [complete_wide_pullback]，而 Theory/Subobject/Lattice.v 的 [sub_wide_intersection] 将其读取为子对象。该读取需要索引的一个点，因此该族首先通过 [sub_top] 在 [option J]（[sub_opt_top]）上扩展；添加顶端不会改变下界（[IsIntersection_drop_top]），因此空族也被覆盖，无需非空假设。因此，对于索引在 [Complete] 自身形状宇宙的族的陈述并非 §V.8 的结论。子对象的类需要它。“子对象的集合”是等价类的集合；在集合体（setoid）学科中，它是在大类型  [SubObj x] 上的谓词 [P]，并且在 ≈ (ZWZ61WZZ) 下封闭。它的成员形成一个由 [{ m : SubObj x & P m }] 索引的族，它位于对象（OBJECT）宇宙之中，每当对象位于霍姆（homs）之上时，高于形状（shape）宇宙。[wellpowered_complete_has_intersections] 通过对小型 [wp_class_index] = [{ i : wp_index W & P (wp_to W i) }] 重新索引与其相交：[IsIntersection_reindex] 在 [wp_to (wp_from m) ≈ m] 下沿 [HP] 传递成员关系，并通过 [sub_le_of_equiv] 绑定回传。只有 [WellPoweredAt] 的四个字段被使用；派生出的双射不需要。[Prop] -值形式 ([_prop]) 对 [P] 没有大小条件；[wellpowered_complete_intersection_all] 是所有子对象的类，由 [SubObj x] 本身索引，并且 [wellpowered_complete_least_subobject] 将其读取为最小子对象。在附属函子定理使用的体制（[C : Category@{o h h}]、[h < o]、[comp : Complete@{h h h o}]）下，通过临时文件来衡量必要性：[complete_intersection_IsIntersection comp (fun k : { m : SubObj x & P m } => `1 k)] 被拒绝，并提示“无法确保 Type@{max(o,h)} 是 Type@{...} 的子类型”，[SubObj x] 上的恒等族也是如此，而 [wellpowered_complete_has_intersections] 和 [wellpowered_complete_intersection_all] 在给定 [WellPowered C] 的相同体制下被接受；在 [Sets@{o so}] 及 [Sets_Complete] 下，[SubObj X] 上的恒等族被拒绝，提示“无法强制 o = ..."因为 o < so <= ...（如链条所示，使用 [X : Sets@{o so}] 到 [Section] [Context]；在 [X] 作为定义的绑定器时，Rocq 9.1.1 在 [so] 的位置打印了一个未命名的宇宙，正如 Test/ProbeWellPowered451.v 的 N7 记录所示），并且通过 [wellpowered_complete_intersection_all] 给出的 [WellPowered Sets] 被接受。为什么使用类，而不是任意大的族。对于 [S : J → SubObj x] 和 [J : Type@{o}]，有两种读法，并且两者都被拒绝（在相同的规则下测量）。类型化的映像 [fun m => { j : J & S j ≈ m }] 与 [J] 一样大：“无法强制执行 o <= ... 因为 ... < o”。[Prop] 截断的映像 [fun m => ex (fun j => inhabited (S j ≈ m))] 是 ≈-封闭的，并被接受，它的交集是每个 [S j] 的下界；但要显示 [S] 的下界在它之下，需要一个来自截断证人的 [S] 成员，而这一步被拒绝，提示“在归纳类型 ex 中消元不正确...”返回类型为 Type@{h}，而它本应是 SProp 或 Prop（如在 [Set Printing Universes] 下使用 [h] 命名宇宙时打印；默认打印会将 Type@{h} 显示为“Type”）。该路径需要唯一选择以消除截断的证据进入 [Type] 值的 [sub_le]；没有测量其他路径，并且这里没有显示每条路径都需要它。该类形式既是对书籍的忠实解读，也是此处证明的最强形式。双重。[cowellpowered_cocomplete_has_cointersections] 是在 [C^op] 通过 Construction/Product/Limit.v 的 [Complete_op_of_Cocomplete] 读取的定理，一行完成；[cointersection_quot_le] 在 Theory/Subobject/Quotient.v 的 [quot_le] 中读取其下界，无需转换步骤。结果在此称为共交；Quotient.v 在 [quot_le] 的 [quot_wide_meet] 中称同一最大下界。

 优势，已测量。交集是数据：[IsIntersection] 携带 [sub_le] 的分解，并且构建它们的本文件的每个常量都是 [Defined]。并非所有内容都可计算。标准是 [eq_refl]，在答案已知的范畴中，由 [Indiscrete bool] 完成 [Indiscrete_Complete true]，每个同态为 [unit]。- 下界部分进行计算。Structure/Pullback/Wide/Complete.v ([unique_obj (iprod_ump ...)]) 的积中介和边 [wide_pullback_proj (complete_wide_pullback comp f) j] 通过 [eq_refl] 约化为 [tt]。[complete_intersection] 的每个 [inter_le] 都是这样的一个边，并且类形式将其与 [wp_to_from] 的同构组合，计算直到证人的完全性证明为止；
 - 上界部分则不进行计算。宽拉回的中介 [unique_obj (ump_wide_pullbacks (complete_wide_pullback comp f) q Hq)]，每个 [inter_greatest] 的分解都是从此构建的，在 [eq_refl] 被转换拒绝（“cannot unify ... and ()”），并且 [Eval cbv] 停止于 [unique_obj (eq_desc (equalizer_of_pullback_awodey ...))]。Structure/Pullback/Reduction.v 的 [equalizer_of_pullback_awodey] 是 [Qed]，并返回一个 [IsEqualizer]，其 [eq_desc] 是均衡器的中介：因式分解是只归约到那个不透明常数的数据。Adjunction/GAFT.v 的 [Complete_HasEqualizers] 无济于事：在同一范畴中，它的中介停止在 Structure/Equalizer/Fork.v 的 [limit_equalizer_desc]，也包括 [Qed]。[Print Opaque Dependencies wellpowered_complete_has_intersections] 列出了 63 个常量。除了 [equalizer_of_pullback_awodey] 之外，还有两个携带数据：Theory/Subobject.v 的 [SubObj_Setoid_obligation_1]，即子对象上的等价关系，其成员是同构，以及 Structure/Pullback/Limit.v 的 [Pullback_to_Universal_obligation_2]，一个 [∃!] 调解器；阅读其余部分的声明，它们是 ≈-等式、单性、形状的 [Program] 义务，以及集合重写引理。使因子化可计算将从将 [equalizer_of_pullback_awodey] 翻转为 [Defined] 开始；这里没有尝试这样做。[wellpowered_complete_has_intersections] 返回的子对象是通过 [eq_refl] 得到的 [complete_intersection] 的小重索引族 ([wellpowered_intersection_is_small])。唯一性是 Lattice.v 的 [IsIntersection_unique]，仅限于 ≈，这里没有重新证明。宇宙，用 [Set Printing Universes. About ...] 测量，stdlib 边界省略。在第一个未注释的展开最小化中，坍缩的宇宙保持语句分开：索引 [w] 对应到 hom 宇宙，[r] 对应到 [so] 在 [wellpowered_complete_has_intersections] 和 [cointersection_quot_le] 中，族索引 [q] 对应到 [s] 在 [wellpowered_complete_intersection_all] 中，以及索引 [j] 对应到 [so] 在 [complete_intersection_IsIntersection] 中。因此绑定器是承重的：wellpowered_complete_has_intersections@{o h w s t r so p q u u0 u1 u2} ：
 ∀ {C : Category@{o h h}}, WellPowered@{o h w s t} C →
 Complete@{r so h o} → ∀ (x : obj [C] ) (P : SubObj@{o h} x → Type@{p}),
 (∀ m m', m ≈ m' → P m → P m') →
 ∃ w, IsIntersection@{o h q} (λ k : ∃ m, P m, `1 k) w
 ( * w <= h, h < t, o <= s, h <= s, so <= r, h <= r, w <= so, p <= so,
 o <= q, h <= q, p <= q, 以及内部的那些 * )重要的两个界限是 [w <= so] 和 [p <= so]：索引和类的宇宙必须符合 [Complete] 的形状对象。没有任何东西将 [h] 与 [so] 联系起来，并且在伴随函子机制（[so = h]）下，别针 [w <= h] 正是所要求的。[complete_intersection@{o h r so j ...}] 为族的索引 [j] 携带 [j <= so]，除此之外没有其他值得注意的东西。

 ** 见证[trivial_small]：一个其对象位于或低于其同态的范畴是良有上界的（[o <= h]），使用平凡指标。[wp_groupoid] 和 [Groupoid_WellPowered]：一个每个箭头都是可逆的范畴（Structure/Groupoid.v 的 [IsGroupoid]）在每个对象宇宙下都是用单点指标良有上界的；其对偶再次是单点的（Structure/Groupoid.v 的 [IsGroupoid_op]），所以 [Groupoid_CoWellPowered] 也是如此。实例：[DiscreteCat_WellPowered]、[Indiscrete_WellPowered] 及其共良有上界的对应物，以及 [DiscreteCat_types_WellPowered] 在 [DiscreteCat@{o j j} Type@{j}] 上，对象严格高于同态，使用 [Set] 的指标。[wp_of_classifier] 和 [Classifier_WellPowered]：一个对子对象分类器通过拉回对 x 的子对象建立索引，位于同态宇宙中，对象与同态之间没有边界；Instance/FinSet/WellPowered.v 在 FinSet 上实例化了它。反驳方是 Structure/WellPowered/Counterexample.v：一个薄范畴，[AntichainTop]，是在没有公理的情况下构建的，并且可以证明在针处不是良有界的。在其他地方的树中：Instance/Sets/WellPowered.v（[Sets]  一层宇宙上是良幂的和共良幂的，在 [Untruncate] 下的销点是良幂的，以及在相同假设下位于 [Sets] 的结论），Instance/Grp/WellPowered.v（[Grp] 一层宇宙上是良幂的），Instance/Powerset/WellPowered.v（集合上幂集格的结论，无条件），Adjunction/SAFT/WellPowered.v（桥接到 Adjunction/SAFT.v 的 [SubobjectIndex]），并且，自 #452 起，Adjunction/SAFT/InitialObject.v（特殊初始对象定理的良幂推论）及其证据 Adjunction/SAFT/InitialObject/Examples.v 和 Instance/Sets/SpecialInitial.v；并且，自 #454 起，Instance/Mod/WellPowered.v（[RMod R] 一层宇宙上无条件是良幂和共良幂的，以及两者在针脚下 [Untruncate])。** 结果的非空性搜索了树的 [Complete] 实例（Instance/、Structure/ 和 Construction/ 下所有名为 [*Complete*]、类型为 [@Complete ...] 的常量定义），以寻找一个在引脚上功率充足的实例，形式为定理接受的形式，如原文所示。[Sets] 和 [Grp] 仅在上升一个 universe 时展示了良好幂性（Instance/Sets/WellPowered.v 的 [Sets_WellPoweredAt_up], Instance/Grp/WellPowered.v 的 [Grp_WellPoweredAt_up]；此括号里写着“其他代数范畴未被测量”，在这里被更正：由于 #454 Instance/Mod/WellPowered.v 无条件展示了 [RMod R] 上升一个 universe 的良好幂性（[RMod_WellPoweredAt_up]）并在 [Untruncate] 下的针处（[RMod_WellPowered_untruncate]），并且以同样两种方式展示了余良好幂性（[RMod_CoWellPoweredAt_up], [RMod_CoWellPowered_untruncate]），而其余的代数范畴仍未被测量），并且 [Sets] 仅在 [Untruncate] 下的针处展示了良好幂性（[Sets_WellPowered_untruncate]）；[Presheaf_Complete] 的预层范畴仅在某一假设下拥有分类器：Instance/Fun/Classifier.v 的 [Fun_Classifier] 采用 [Untruncate] 及其 [Fun_Classifier_IEM] takes [IEM] 。[SmallOrd_op_Complete] 
 （Instance/Ordinal/Large.v）是薄的，并且 [trivial_small] 将其应用于它，
 其同态提升到对象，但其形状-对象宇宙
 严格位于其对象之下，将该证据传递给 [wellpowered_complete_intersection_all] 会被拒绝，提示“无法
 强制 ... = ... 因为 ... < ...”（已测量）。[Subsets_Complete] 
 （Instance/Powerset.v）写成其同态在 [Set] 处，对象在上方；
 在自由同态层重新表述，它就是 Instance/Powerset/WellPowered.v 的 [Subsets_Complete_free]，
 该卫星在任意集合体的幂集格上无条件且非退化地应用定理（[Subsets_intersection_all_not_top]），
 对象位于同态之上或之下，因此 [trivial_small] 是该证据。此文件为实例提供严格高于同态的对象：
 [Indiscrete_Complete] 使每个有元的非离散范畴完备，且 [Indiscrete_types_has_intersections] 在 [Indiscrete@{o j j} Type@{j}]（[j < o]）处应用该定理，其中 [trivial_small] 是无法到达的。该实例是退化的（其中每个子对象都是最大的）。在树状结构中该结论的实例中，没有一个同时无条件地具有严格高于同态的对象和非退化的子对象格；Instance/Sets/WellPowered.v 的 [Sets_wellpowered_intersection] 在 [Untruncate] 下同时具备这两者。

 ** 未交付在该文件中，没有适用于 [Sets]、[Grp] 或任何代数范畴的充分幂集见证（它们是在 Witnesses 下命名的卫星）。
 没有关于 [FinitelyComplete] 或关于未从 [Complete] 导出的 [HasWidePullbacks] 的交集定理；
 Theory/Subobject/Lattice.v 的 [sub_intersection] 已经涵盖了小非空族的后者（它取索引的一个点；[sub_opt_top] 是该文件避免需要一个的方式）。
 没有陈述说一个充分幂范畴具有任意大族的交集，原因如上所述。
 没有广推出（wide-pushout）词汇：其对偶过程通过 [C^op]，正如 Quotient.v 的 [quot_wide_meet] 所做的一样。
*)

Record WellPoweredAt {C : Category} (x : C) := {
  wp_index   : Type;
  wp_to      : wp_index → SubObj x;
  wp_from    : SubObj x → wp_index;
  wp_to_from : ∀ u : SubObj x, wp_to (wp_from u) ≈ u
}.

Arguments wp_index {C x} _.
Arguments wp_to {C x} _ _.
Arguments wp_from {C x} _ _.
Arguments wp_to_from {C x} _ _.

(* * ** The bijection onto all subobjects / * ** 到所有子对象的双射 *)

Section Bijection.

Context {C : Category} {x : C} (W : WellPoweredAt x).

(* The index setoid: two indices are equal when the subobjects they name are. / 指标集合等价：当它们所命名的子对象相等时，两个指标也相等。 *)
Definition wp_rel : crelation (wp_index W) :=
  fun i j => wp_to W i ≈ wp_to W j.

Lemma wp_rel_equiv : Equivalence wp_rel.
Proof.
  unfold wp_rel; constructor.
  - intro i; reflexivity.
  - intros i j H; symmetry; exact H.
  - intros i j k H1 H2; etransitivity; [exact H1 | exact H2].
Defined.

Definition wp_index_setoid : Setoid (wp_index W) :=
  {| equiv := wp_rel; setoid_equiv := wp_rel_equiv |}.

Lemma wp_to_resp (i j : wp_index W) :
  @equiv _ wp_index_setoid i j → wp_to W i ≈ wp_to W j.
Proof. intro H; exact H. Qed.

Lemma wp_from_resp (u v : SubObj x) :
  u ≈ v → @equiv _ wp_index_setoid (wp_from W u) (wp_from W v).
Proof.
  intro H; simpl; unfold wp_rel.
  etransitivity; [exact (wp_to_from W u)|].
  etransitivity; [exact H|].
  symmetry; exact (wp_to_from W v).
Qed.

Lemma wp_from_to (i : wp_index W) :
  @equiv _ wp_index_setoid (wp_from W (wp_to W i)) i.
Proof. exact (wp_to_from W (wp_to W i)). Qed.

End Bijection.

(** ** The pinned notion / ** 固定的概念 *)

(*
 [w] is the index universe, pinned at or below the hom universe [h];
 [s] and [t] are the two universes of [SubObj_Setoid].  The trailing
 [+] in both constraint lists is load-bearing on Coq 8.19 and 8.20,
 where [sigT] and [eq] carry global universes: without it both
 toolchains refuse the declaration with "Universe constraints are not
 implied by the ones declared: h <= sigT.u0, h <= sigT.u1, h <= eq.u0"
 (measured).  On Rocq 9.1 the block read back is the same four
 constraints with or without it. 

 --------
 [w] 是索引宇宙，固定在同一宇宙 [h] 或以下；
 [s] 和 [t] 是 [SubObj_Setoid] 的两个宇宙。在两个约束列表中末尾的 [+] 在 Coq 8.19 和 8.20 上是承重的，而 [sigT] 和 [eq] 承载全局宇宙：没有它，两个工具链都会拒绝声明，并提示“Universe constraints are not implied by the ones declared: h <= sigT.u0, h <= sigT.u1, h <= eq.u0”（经过测量）。在 Rocq 9.1 上，无论是否有它，块回读的都是相同的四个约束。
*)

Definition WellPowered@{o h w s t | w <= h, o <= s, h <= s, h < t +}
  (C : Category@{o h h}) :=
  ∀ x : C, WellPoweredAt@{w o s h t} x.

Definition CoWellPowered@{o h w s t | w <= h, o <= s, h <= s, h < t +}
  (C : Category@{o h h}) :=
  WellPowered@{o h w s t} (C^op).

(* * ** Co-well-powered is well-powered over the quotient objects / * ** 余商对象上是良有力的 *)

Section Quotients.

Context {C : Category} {x : C}.

Example quot_obj_is_sub_op : @QuotObj C x = @SubObj (C^op) x := eq_refl.

Example quot_setoid_is_sub_setoid_op :
  @QuotObj_Setoid C x = @SubObj_Setoid (C^op) x := eq_refl.

(* Exhaustiveness read in the quotient setoid, with no conversion step. / 在商集合等式中读取穷尽性，没有转换步骤。 *)
Lemma cowp_to_from (W : @WellPoweredAt (C^op) x) (q : QuotObj x) :
  @equiv _ (@QuotObj_Setoid C x) (wp_to W (wp_from W q)) q.
Proof. exact (wp_to_from W q). Qed.

End Quotients.

(* * ** Intersections of small families need no well-poweredness / * ** 小群体的交集不需要良好幂性 *)

(*
 Adjoining the top subobject to a family changes none of its lower
 bounds, and it gives the index a point ([None]), which Theory/Subobject/
 Lattice.v's [sub_wide_intersection] needs to read a wide pullback as a
 subobject. 

 --------
 将顶部子对象附加到一个族不会改变其下界，并且它会给索引一个点（[None]），Theory/Subobject/Lattice.v 的 [sub_wide_intersection] 需要将广拉回读取为一个子对象。
*)

Section SmallIntersections.

Context {C : Category} {x : C}.

Definition sub_opt_top {J : Type} (S : J → SubObj x) : option J → SubObj x :=
  fun o => match o with Some j => S j | None => sub_top end.

Lemma IsIntersection_drop_top {J : Type} (S : J → SubObj x) (w : SubObj x) :
  IsIntersection (sub_opt_top S) w → IsIntersection S w.
Proof.
  intros H; constructor.
  - intro j; exact (inter_le _ _ H (Some j)).
  - intros v Hv; apply (inter_greatest _ _ H).
    intros [j|]; [exact (Hv j) | exact (sub_top_greatest v)].
Defined.

End SmallIntersections.

(*
 The intersection of ANY family indexed at or below [Complete]'s
 shape-object universe, empty or not, from completeness alone. 

 --------
 仅凭完备性，任何在 [Complete] 的形状对象宇宙及以下索引的家族的交集，无论是否为空。
*)
Definition complete_intersection@{o h r so j +| so <= r, h <= r, j <= so +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C) {x : C}
  {J : Type@{j}} (S : J → SubObj x) : SubObj x :=
  sub_wide_intersection (sub_opt_top S) None
    (complete_wide_pullback comp
       (fun o => Subobject.sub_mono (sub_opt_top S o))).

Definition complete_intersection_IsIntersection@{o h r so j +|
    so <= r, h <= r, j <= so +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C) {x : C}
  {J : Type@{j}} (S : J → SubObj x) :
  IsIntersection@{o h j} S (complete_intersection comp S) :=
  IsIntersection_drop_top S _
    (sub_wide_intersection_IsIntersection (sub_opt_top S) None
       (complete_wide_pullback comp
          (fun o => Subobject.sub_mono (sub_opt_top S o)))).

(* * ** The consequence: intersections of classes of subobjects / * ** 结果：子对象类的交集 *)

(*
 A collection of subobjects is a collection of equivalence classes; in
 setoid discipline, a predicate [P] on the large type [SubObj x] that is
 closed under ≈.  Its members are intersected by reindexing them over the
 SMALL index [{ i : wp_index W & P (wp_to W i) }] and taking the wide
 pullback there. 

 --------
 子对象的集合是一组等价类的集合；在集合体（setoid）规范下，对大类型 [SubObj x] 的谓词 [P] 在 ≈ 下是封闭的。它的成员通过在小索引 [{ i : wp_index W & P (wp_to W i) }] 上重新索引并在那里取广义拉回而相交。
*)

Section ClassIntersection.

Context {C : Category} {x : C}.
Context (W : WellPoweredAt x).
Context (P : SubObj x → Type).
Context (HP : ∀ m m' : SubObj x, m ≈ m' → P m → P m').

Definition wp_class_index : Type := { i : wp_index W & P (wp_to W i) }.

Definition wp_class_family (k : wp_class_index) : SubObj x := wp_to W (`1 k).

(*
 A lower bound of the representatives is a lower bound of the class:
 [HP] carries membership along [wp_to (wp_from m) ≈ m] to the
 representative, and [sub_le_of_equiv] carries the bound back. 

 --------
 代表的下界是类的下界：
 [HP] 将成员资格沿着 [wp_to (wp_from m) ≈ m] 传递给代表，[sub_le_of_equiv] 将界限传回。
*)
Lemma IsIntersection_reindex (w : SubObj x) :
  IsIntersection wp_class_family w →
  IsIntersection (fun k : { m : SubObj x & P m } => `1 k) w.
Proof using HP.
  intros H; constructor.
  - intros [m p]; simpl.
    exact (sub_le_trans _ _ _
             (inter_le _ _ H
                (wp_from W m; HP m (wp_to W (wp_from W m))
                                (symmetry (wp_to_from W m)) p))
             (sub_le_of_equiv _ _ (wp_to_from W m))).
  - intros v Hv; apply (inter_greatest _ _ H).
    intros [i p]; exact (Hv (wp_to W i; p)).
Defined.

End ClassIntersection.

(* The per-object form: one object's well-poweredness datum suffices. / 每个对象的形式：一个对象的强能数据就足够了。 *)
Definition wp_complete_class_intersection@{o h w s t r so p q +|
    h < t, o <= s, h <= s, so <= r, h <= r, w <= so, p <= so,
    o <= q, h <= q, p <= q +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C)
  {x : C} (W : WellPoweredAt@{w o s h t} x) (P : SubObj x → Type@{p})
  (HP : ∀ m m' : SubObj x, m ≈ m' → P m → P m') :
  { w : SubObj x &
    IsIntersection@{o h q} (fun k : { m : SubObj x & P m } => `1 k) w }.
Proof.
  exists (complete_intersection comp (wp_class_family W P)).
  exact (IsIntersection_reindex W P HP _
           (complete_intersection_IsIntersection comp _)).
Defined.

(*
 §V.8, as #451 reads it: a well-powered complete category has the
 intersection of every class of subobjects of every object. 

 --------
 §V.8，如#451所述：一个有充分能力的完整范畴具有每个对象的每一子对象类的交集。
*)
Definition wellpowered_complete_has_intersections@{o h w s t r so p q +|
    w <= h, h < t, o <= s, h <= s, so <= r, h <= r, w <= so, p <= so,
    o <= q, h <= q, p <= q +}
  {C : Category@{o h h}}
  (WP : WellPowered@{o h w s t} C) (comp : @Complete@{r so h o} C) (x : C)
  (P : SubObj x → Type@{p}) (HP : ∀ m m' : SubObj x, m ≈ m' → P m → P m') :
  { w : SubObj x &
    IsIntersection@{o h q} (fun k : { m : SubObj x & P m } => `1 k) w } :=
  wp_complete_class_intersection comp (WP x) P HP.

(* The intersection IS the wide pullback over the small index. / 交叉点是小指数上的大回调。 *)
Example wellpowered_intersection_is_small {C : Category}
  (WP : WellPowered C) (comp : @Complete C) (x : C)
  (P : SubObj x → Type) (HP : ∀ m m' : SubObj x, m ≈ m' → P m → P m') :
  `1 (wellpowered_complete_has_intersections WP comp x P HP)
    = complete_intersection comp (wp_class_family (WP x) P) := eq_refl.

(* The same for a [Prop]-valued class, which carries no size condition. / 对于一个 [Prop] 值类型的类也是一样，它没有大小限制。 *)
Definition wellpowered_complete_has_intersections_prop@{o h w s t r so q +|
    w <= h, h < t, o <= s, h <= s, so <= r, h <= r, w <= so,
    o <= q, h <= q +}
  {C : Category@{o h h}}
  (WP : WellPowered@{o h w s t} C) (comp : @Complete@{r so h o} C) (x : C)
  (P : SubObj x → Prop) (HP : ∀ m m' : SubObj x, m ≈ m' → P m → P m') :
  { w : SubObj x &
    IsIntersection@{o h q} (fun k : { m : SubObj x & P m } => `1 k) w } :=
  wellpowered_complete_has_intersections WP comp x P HP.

(* The intersection of ALL subobjects, indexed by the large type [SubObj x] itself: the class [fun _ => True]. / 所有子对象的交集，由大型类型 [SubObj x] 本身索引：类 [fun _ => True]。 *)
Definition wellpowered_complete_intersection_all@{o h w s t r so q +|
    w <= h, h < t, o <= s, h <= s, so <= r, h <= r, w <= so,
    o <= q, h <= q +}
  {C : Category@{o h h}}
  (WP : WellPowered@{o h w s t} C) (comp : @Complete@{r so h o} C) (x : C) :
  { w : SubObj x & IsIntersection@{o h q} (fun m : SubObj x => m) w }.
Proof.
  pose (R := wellpowered_complete_has_intersections_prop
               WP comp x (fun _ => True) (fun _ _ _ t => t)).
  exists (`1 R); constructor.
  - intro m; exact (inter_le _ _ (`2 R) (m; I)).
  - intros v Hv; apply (inter_greatest _ _ (`2 R)).
    intros [m t]; exact (Hv m).
Defined.

(* ... which is the least subobject. / ... 这是最小的子对象。 *)
Definition wellpowered_complete_least_subobject@{o h w s t r so +|
    w <= h, h < t, o <= s, h <= s, so <= r, h <= r, w <= so +}
  {C : Category@{o h h}}
  (WP : WellPowered@{o h w s t} C) (comp : @Complete@{r so h o} C) (x : C) :
  { w : SubObj x & ∀ v : SubObj x, sub_le w v }.
Proof.
  exists (`1 (wellpowered_complete_intersection_all
                WP comp x)).
  exact (inter_le _ _
           (`2 (wellpowered_complete_intersection_all
                  WP comp x))).
Defined.

(* * ** The dual: cointersections of classes of quotient objects / * ** 对偶：商对象类的共同交集 *)

Definition cowellpowered_cocomplete_has_cointersections@{o h w s t r so qo p q
    +| w <= h, h < t, o <= s, h <= s, so <= r, h <= r, w <= so, p <= so,
    o <= qo, h <= qo, qo <= q, p <= q +}
  {C : Category@{o h h}}
  (CWP : CoWellPowered@{o h w s t} C) (cocomp : @Cocomplete@{r so h o} C)
  (x : C) (P : QuotObj@{qo o h} x → Type@{p})
  (HP : ∀ q q' : QuotObj x, q ≈ q' → P q → P q') :
  { w : QuotObj@{qo o h} x &
    @IsIntersection@{o h q} (C^op) x _
      (fun k : { q : QuotObj x & P q } => `1 k) w } :=
  wellpowered_complete_has_intersections CWP
    (Complete_op_of_Cocomplete cocomp) x P HP.

(* Read in the order of quotients, with no conversion step: the cointersection lies below every member of the class in [quot_le]. / 按照商的顺序读取，无需转换步骤：共交在 [quot_le] 中位于该类每个成员的下方。 *)
Lemma cointersection_quot_le@{o h w s t r so qo p q +|
    w <= h, h < t, o <= s, h <= s, so <= r, h <= r, w <= so, p <= so,
    o <= qo, h <= qo, qo <= q, p <= q +}
  {C : Category@{o h h}}
  (CWP : CoWellPowered@{o h w s t} C) (cocomp : @Cocomplete@{r so h o} C)
  (x : C) (P : QuotObj@{qo o h} x → Type@{p})
  (HP : ∀ q q' : QuotObj x, q ≈ q' → P q → P q')
  (q : QuotObj x) (p : P q) :
  quot_le (`1 (cowellpowered_cocomplete_has_cointersections CWP cocomp x P HP))
    q.
Proof.
  exact (inter_le _ _
           (`2 (cowellpowered_cocomplete_has_cointersections CWP cocomp x P HP))
           (q; p)).
Defined.

(** ** Witnesses / ** 证人 *)

(*
 The trivial datum: the index is [SubObj x] itself.  It exists at every
 object of every category, one universe too high to be [WellPowered] in
 general; [trivial_small] is the case where it is not too high. 

 --------
 平凡的数据：索引就是 [SubObj x] 本身。它存在于每个范畴的每个对象上，普遍来说，存在于比 [WellPowered] 高一个宇宙的情况下；[trivial_small] 是它不太高的情况。
*)
Definition wp_trivial@{o h w s t | o <= w, h <= w, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} (x : C) : WellPoweredAt@{w o s h t} x :=
  {| wp_index   := SubObj x;
     wp_to      := fun u => u;
     wp_from    := fun u => u;
     wp_to_from := fun u => Equivalence_Reflexive u |}.

(* A category whose objects sit at or below its homs is well-powered. / 一个其对象位于或低于其同态的范畴是良幂的。 *)
Definition trivial_small@{o h t | o <= h, h < t +}
  (C : Category@{o h h}) : WellPowered@{o h h h t} C :=
  fun x => wp_trivial x.

(*
 A category in which every arrow is invertible (Structure/Groupoid.v's
 [IsGroupoid]) is well-powered with the one-point index: every subobject
 is the top one. 

 --------
 一个类别，其中每个箭头都是可逆的（Structure/Groupoid.v 的 [IsGroupoid]）在单点索引下是良好支配的：每个子对象都是最大的那个。
*)
Section Groupoid.

Context {C : Category}.
Context (G : IsGroupoid C).

Definition wp_groupoid (x : C) : WellPoweredAt x.
Proof using G.
  unshelve refine {| wp_index := Datatypes.unit;
                     wp_to    := fun _ => sub_top;
                     wp_from  := fun _ => tt |}.
  intro u.
  unshelve eexists.
  - exact (iso_sym (IsIsoToIso (Subobject.sub_mono u)
                                (G _ _ (Subobject.sub_mono u)))).
  - simpl; exact is_right_inverse.
Defined.

End Groupoid.

(*
 The pinned forms.  The one-point index sits at [Set], below every hom
 universe, so no bound relates the objects to the homs. 

 --------
 固定的形式。 一点索引位于 [Set]，在每个同宇之下，因此没有界将对象与同联系起来。
*)
Definition Groupoid_WellPowered@{o h w s t | w <= h, o <= s, h <= s, h < t +}
  (C : Category@{o h h}) (G : IsGroupoid C) :
  WellPowered@{o h w s t} C :=
  fun x => wp_groupoid G x.

(* A groupoid's opposite is a groupoid, with the same inverses: Structure/Groupoid.v's [IsGroupoid_op]. / 一个群族的对偶是一个群族，具有相同的逆元： Structure/Groupoid.v 的 [IsGroupoid_op] 。 *)
Definition Groupoid_CoWellPowered@{o h w s t | w <= h, o <= s, h <= s, h < t +}
  (C : Category@{o h h}) (G : IsGroupoid C) :
  CoWellPowered@{o h w s t} C :=
  Groupoid_WellPowered@{o h w s t} (C^op) (IsGroupoid_op G).

(*
 Discrete categories: every arrow is an equality proof, inverted by
 [eq_sym]. 

 --------
 离散范畴：每个箭头都是一个等式证明，由 [eq_sym] 反转。
*)
Definition DiscreteCat_isos@{o h} (A : Type@{o})
  (a b : DiscreteCat@{o h h} A) (f : a ~> b) : IsIsomorphism f.
Proof.
  exists (eq_sym f); destruct f; reflexivity.
Defined.

Definition DiscreteCat_WellPowered@{o h w s t |
    w <= h, o <= s, h <= s, h < t +}
  (A : Type@{o}) : WellPowered@{o h w s t} (DiscreteCat@{o h h} A) :=
  Groupoid_WellPowered@{o h w s t} (DiscreteCat@{o h h} A) (DiscreteCat_isos A).

Definition DiscreteCat_CoWellPowered@{o h w s t |
    w <= h, o <= s, h <= s, h < t +}
  (A : Type@{o}) : CoWellPowered@{o h w s t} (DiscreteCat@{o h h} A) :=
  Groupoid_CoWellPowered@{o h w s t} (DiscreteCat@{o h h} A)
    (DiscreteCat_isos A).

(*
 The objects are the types of [Type@{j}], one universe above the homs,
 which sit at [j]; the index is at [Set]. 

 --------
 这些对象是[Type@{j}]类型的，一个宇宙高于homs，它们位于[j]；索引位于[Set]。
*)
Definition DiscreteCat_types_WellPowered@{j o t | j < o, j < t +} :
  WellPowered@{o j Set o t} (DiscreteCat@{o j j} Type@{j}) :=
  DiscreteCat_WellPowered@{o j Set o t} Type@{j}.

(* Indiscrete categories: every arrow is [tt], inverted by [tt]. / 不离散范畴：每条箭头都是 [tt]，由 [tt] 取反。 *)
Definition Indiscrete_isos@{o h} (A : Type@{o})
  (a b : Indiscrete@{o h h} A) (f : a ~> b) : IsIsomorphism f.
Proof.
  exists (tt : @hom (Indiscrete@{o h h} A) b a); destruct f; reflexivity.
Defined.

Definition Indiscrete_WellPowered@{o h w s t |
    w <= h, o <= s, h <= s, h < t +}
  (A : Type@{o}) : WellPowered@{o h w s t} (Indiscrete@{o h h} A) :=
  Groupoid_WellPowered@{o h w s t} (Indiscrete@{o h h} A) (Indiscrete_isos A).

Definition Indiscrete_CoWellPowered@{o h w s t |
    w <= h, o <= s, h <= s, h < t +}
  (A : Type@{o}) : CoWellPowered@{o h w s t} (Indiscrete@{o h h} A) :=
  Groupoid_CoWellPowered@{o h w s t} (Indiscrete@{o h h} A)
    (Indiscrete_isos A).

(*
 A subobject classifier over pullbacks indexes the subobjects of x by the
 arrows [x ~> Ω]: [wp_to] pulls [truth_subobject] back along the arrow,
 [wp_from] takes the characteristic map, and exhaustiveness is
 Structure/SubobjectClassifier.v's [classifier_pullback_roundtrip].  The
 index is a hom-set, so it sits at the hom universe with no bound between
 objects and homs. 

 --------
 一个关于拉回的子对象分类器通过箭头 [x ~> Ω] : [wp_to] 将 [truth_subobject] 拉回沿着该箭头来索引 x 的子对象，[wp_from] 采取特征映射，并且穷尽性是 Structure/SubobjectClassifier.v 的 [classifier_pullback_roundtrip]。索引是一个同集，因此它位于同宇宙中，对象与同之间没有界限。
*)
Definition wp_of_classifier {C : Category} `{T : @Terminal C}
  `{PB : @HasPullbacks C} `{S : @SubobjectClassifier C T} (x : C) :
  WellPoweredAt x :=
  {| wp_index   := x ~> Ω;
     wp_to      := fun f => sub_reindex f truth_subobject;
     wp_from    := fun u => char (Subobject.sub_mono u) (sub_is_monic u);
     wp_to_from := fun u => classifier_pullback_roundtrip u |}.

Definition Classifier_WellPowered@{o h s t | o <= s, h <= s, h < t +}
  (C : Category@{o h h}) `{T : @Terminal C} `{PB : @HasPullbacks C}
  `{S : @SubobjectClassifier C T} : WellPowered@{o h h s t} C :=
  fun x => wp_of_classifier x.

(* * ** Non-vacuity of the consequence / * ** 结论的非空性 *)

(*
 An inhabited indiscrete category is complete: the limit of every diagram
 is any object, with the only possible legs. 

 --------
 一个有居民的非离散范畴是完备的：每个图的极限是任意对象，并且只有可能的箭头。
*)
Definition Indiscrete_Complete@{r so h o +| so <= r, h <= r +}
  {A : Type@{o}} (a : A) : @Complete@{r so h o} (Indiscrete@{o h h} A).
Proof.
  intros D F.
  unshelve refine {| limit_cone :=
    @Build_Cone D (Indiscrete A) F a
      (@Build_ACone D (Indiscrete A) a F (fun _ => tt) _) |}.
  - intros; reflexivity.
  - intro N.
    unshelve eapply Build_Unique.
    + exact tt.
    + intro y.
      destruct (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) y); reflexivity.
    + intros v _; destruct v; reflexivity.
Defined.

(*
 Both hypotheses of [wellpowered_complete_has_intersections] at once, at a
 category whose objects, the types of [Type@{j}], sit one universe above
 its homs; the trivial witness is out of reach there. 

 --------
 [wellpowered_complete_has_intersections] 的两个假设同时存在，在一个类别上，其对象 [Type@{j}] 的类型位于其同态之上的一个宇宙中；显而易见的证据在那里是无法触及的。
*)
Definition Indiscrete_types_has_intersections@{j o t q +|
    j < o, j < t, o <= q +}
  (x : Indiscrete@{o j j} Type@{j}) (P : SubObj x → Type@{j})
  (HP : ∀ m m' : SubObj x, m ≈ m' → P m → P m') :
  { w : SubObj x &
    IsIntersection@{o j q} (fun k : { m : SubObj x & P m } => `1 k) w } :=
  wellpowered_complete_has_intersections
    (Indiscrete_WellPowered@{o j Set o t} Type@{j})
    (Indiscrete_Complete@{j j j o} (Datatypes.unit : Type@{j})) x P HP.
