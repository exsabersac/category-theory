Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Discrete.

Generalizable All Variables.

(** * [Sets] is cocomplete / * [Sets] 是完备余的 *)

(*
 nLab:      https://ncatlab.org/nlab/show/cocomplete+category
 nLab:      https://ncatlab.org/nlab/show/colimit
 Wikipedia: https://en.wikipedia.org/wiki/Limit_(category_theory)

 Mac Lane, “Categories for the Working Mathematician” 2nd ed., Springer
 GTM 5 1998, §III.3 (pp. 67-68), where the colimit of a diagram of sets
 is the disjoint union of the [F d] with the images of the connecting
 maps identified; and §V.1 Exercise 8, “Set is cocomplete”, which asks
 for the GENERAL statement -- all small colimits -- and not only the
 union of an increasing chain.  Riehl, “Category Theory in Context”,
 Dover 2016, §3.1 Example 3.1.26 is the same computation.

 [Cocomplete C] is [∀ (D : Category) (F : D ⟶ C), Colimit F]
 (Structure/Complete.v) and [Colimit F] is [Limit (F^op)]
 (Structure/Limit.v): an oracle assigning a chosen colimit to every
 diagram.  This file inhabits it at [Sets], as the mirror of
 Instance/Sets/Complete.v.  Five in-tree notes across four files record
 the absence this answers -- Instance/Sets/Complete.v,
 Instance/Sets/Coequalizer.v twice, Instance/Sets/Quotient.v,
 and Instance/Sets/Products.v, whose “cocompleteness is not
 addressed at all, here or anywhere else in the tree” is the flattest
 of the five -- and it sits in the very file that supplies
 [Sets_icoprod_obj], this construction's own donor.  None was edited
 when this file landed, and all five were STALE.  THREE have since been
 corrected in place and now point HERE (the note in Complete.v, and
 with it the first of the two in Coequalizer.v and the one in
 Quotient.v); the second Coequalizer.v note and the one in
 Products.v still read as absences.  An earlier draft counted THREE
 notes and said they “still stand as written” -- wrong twice over.

 THE CONSTRUCTION

 The colimit of [F : D ⟶ Sets] is the indexed coproduct of the diagram's
 objects, quotiented by the equivalence relation that the connecting
 maps generate.  Three named pieces:

 [Sets_colim_sum]   is [Sets_icoprod_obj (fun d : D => F d)], the sigma
 setoid of Instance/Sets/Products.v -- an element is
 a pair [(d; x)] with [x] an element of [F d];

 [colim_rel]        is the inductive relation on that carrier with two
 generating clauses, [cr_point] (the fibre
 equivalence: [x ≈ y] in [F d] relates [(d; x)] and
 [(d; y)]) and [cr_glue] (the diagram glue: [(d; x)]
 is related to [(d'; fmap[F] f x)] for every
 [f : d ~> d']), closed under [cr_sym] and
 [cr_trans], with reflexivity DERIVED as
 [colim_rel_refl] rather than taken as a fifth
 constructor -- so the induction has four cases,
 exactly the shape of [coend_eq] in
 Instance/Sets/Coend.v;

 [Sets_colim_obj]   is [SetsQuotient] (Instance/Sets/Quotient.v) of the
 first by the second: SAME CARRIER, coarser [≈].

 The leg at [d] is [Sets_colim_inj d], the injection [x ↦ (d; x)].  The
 mediator out of a competing cocone [N] is [Sets_colim_med N], which
 sends [(d; x)] to [N]'s own leg at [d] applied to [x]; that this
 respects [colim_rel] is [Sets_colim_med_respects], by induction on the
 relation, the [cr_glue] case being [N]'s cone coherence read at the
 point [x] and symmetrised.  Commuting is [reflexivity] and uniqueness
 is the symmetry of the competing map's commuting equations -- the same
 two closing moves as Instance/Sets/Complete.v.

 READING THE OBLIGATIONS THROUGH THE DUALITY

 Because [Colimit F] is [Limit (F^op)], the record built below is a
 [Cone (F^op)], i.e. a [Cocone F] (Structure/Cone.v).  Its coherence
 field at [f : d ~{D^op}~> d'] -- that is, at [f : d' ~{D}~> d] -- reads
 [ι_d ∘ fmap[F] f ≈ ι_{d'}] in [Sets], which runs opposite to the
 covariant direction [cr_glue] is stated in; the obligation is therefore
 discharged by [cr_sym] of a [cr_glue], and not by [cr_glue] itself.
 The universal property likewise unfolds so that the mediator runs OUT
 of the apex, [Sets_colim_obj ~{Sets}~> vertex_obj[N]].

 NO DUALITY SHORTCUT FROM [Sets_Complete] -- MEASURED, NOT ASSUMED

 [Sets_Complete] (Instance/Sets/Complete.v) supplies a [Limit F] for
 every [F : D ⟶ Sets].  A colimit of [F] is a limit of [F^op], and
 [F^op] is a diagram into [Sets^op]; no instantiation of [Sets_Complete]
 has that type.  Elaborating
 [Sets_Complete (Opposite D) (Opposite_Functor F)] is rejected with
 “The term ”F^op“ has type ”D^op ⟶ Sets^op“ while it is expected to have
 type ”D^op ⟶ Sets“”, against the positive control
 [Sets_Complete D F : Limit F], which is accepted.  What would produce
 the colimit is [Complete (Sets^op)], and that IS [Cocomplete Sets]
 again, so the duality is not a route.  No [Fail] probe is kept in this
 file; all three refutations are pinned in Test/ProbeCocomplete329.v.

 A probe-hygiene point, since the same trap awaits anyone rewriting that
 measurement: written as [Sets_Complete (D^op) (F^op)] it fails for the
 WRONG reason.  Functor/Opposite.v opens [functor_scope], in which
 [_ ^op] is [Opposite_Functor], so [D^op] parses as [Opposite_Functor D]
 and the error is “The term ”D“ has type ”Category“ while it is expected
 to have type ”?C ⟶ ?D“” -- a notation clash and not the mathematics.
 The measurement above spells [Opposite] and [Opposite_Functor] by name.
 This is the notation guard Instance/Rng/Mod.v records.

 HOW THIS IS *NOT* PROVED, STATED PLAINLY

 It is NOT routed through “a category with all small coproducts and
 coequalizers is cocomplete”.  That theorem is in this development in
 neither variance: on the limit side Instance/Sets/Complete.v
 already records its absence, and dually no constant here or elsewhere
 derives [Cocomplete] from [HasIndexedCoproducts] and [HasCoequalizers].
 CORRECTION (#458): since #416 the theorem exists in both variances,
 Structure/Limit/FromProducts.v's [Complete_from_products_equalizers]
 and [Cocomplete_from_coproducts_coequalizers]; [Sets_Cocomplete] is
 still not routed through it, and Instance/Top/Cocomplete.v's
 [PTop_Cocomplete_via_coproducts] consumes the second at [PTopCat].
 In particular [Sets_HasCoequalizers] (Instance/Sets/Coequalizer.v)
 is NOT consumed.  What is consumed is the layer beneath it: the two
 objects [Sets_icoprod_obj] and [SetsQuotient].  Both halves of the
 informal recipe are therefore genuine donors, but the coequalizer is
 not one of them, and Instance/Sets/Coequalizer.v's forecast that its
 hand-built object “is what a later [Cocomplete Sets] would itself need”
 is not what happened.

 Two further constants are present but OFF the path to
 [Sets_Cocomplete]: [Sets_colim_coarser] and [Sets_colim_inj_donors],
 the leg written as the donor composite
 [sets_quot_proj ∘ Sets_icoprod_inj].  They are kept because they make
 the coproduct-then-quotient provenance machine-checked rather than
 merely described -- [Sets_colim_inj_is_donor_composite] equates them
 with the leg actually used, at [eq_refl] -- and because of the universe
 measurement recorded next.

 SMALLNESS AND UNIVERSES, FROM THE CONSTRAINT BLOCKS

 [About Sets_Cocomplete] under [Set Printing Universes] prints

 Sets_Cocomplete@{uc ud uo uso} : Cocomplete@{uc ud uo uso}
 ( * uc ud uo uso |= uc < uso   ud <= uc   ud <= uo   uc = uo   ... * )

 Writing [Sets@{o so}] as Instance/Sets.v does, [uo] is [o] -- the
 universe of the CARRIERS of [Sets]' objects, and of its homs -- and
 [uso] is [so], where [obj[Sets]] itself lives.  [Cocomplete@{a b c d}]
 applies to [C : Category@{d c c}] and quantifies over
 [D : Category@{b c c}], so [c] is D's hom universe, forced equal to
 [Sets]' by the type of [Cocomplete] itself, and [b] is D's OBJECT
 universe.  The block records [ud <= uo]: the diagram category's objects
 sit at or BELOW [Sets]' carrier universe and are NOT identified with
 it.  That inequality is the smallness side condition, and it is exactly
 what the construction needs -- the sigma [{ d : D & F d }] and the
 inductive [colim_rel] both quantify over the objects and the arrows of
 [D], so they fit as a [Sets] carrier when both sit at or below [o].
 This is the universe-polymorphic stand-in for “D small relative to C”
 that Structure/Complete.v describes.

 TWO MEASURED FINDINGS ABOUT THAT BLOCK.

 (1) The four universe binders are written out deliberately.  Left to
 minimization, [Definition Sets_Cocomplete : @Cocomplete Sets :=
 fun D F => Sets_Colimit F] elaborates to
 [Sets_Cocomplete@{u u0} : Cocomplete@{u u u u0}], which sets [ud := uo]
 and so refuses a diagram category whose objects sit strictly below
 [Sets]' carriers.  The identification is minimization and not a
 constraint: the annotated form above is accepted, and instantiating it
 under a declared [Constraint pd < po] is accepted too.  The mirror
 [Sets_Complete@{u u0} : Complete@{u u u u0}] carries the identification,
 but that is minimization there as well -- the same annotation on its
 body was accepted in a scratch session -- so nothing here says that
 limits are inherently tighter than colimits, and
 Instance/Sets/Complete.v is not edited.

 (2) The identification would return if the leg were the donor
 composite.  [Sets_icoprod_inj@{u u0}] (Instance/Sets/Products.v)
 carries only two universe binders and types its family as
 [A → SetoidObject@{u u}] with [A : Type@{u}], identifying the index
 type's universe with the setoid carrier universe, whereas
 [Sets_icoprod_obj@{u u0 u1 u2}] keeps them apart under [u <= u0].
 Measured in the file as it stands: [Sets_colim_inj_donors] carries
 [u = u0] where the direct [Sets_colim_inj] carries [u <= u0].  Measured
 on an earlier revision, in which the donor composite WAS the leg: that
 identification propagates, giving [Sets_Colimit] and hence
 [Sets_Cocomplete] the pin [ud = uo].  The second half is a
 counterfactual about a revision that is not in tree, so it cannot be
 rechecked from this file alone; only the first half can.  The donor's
 restriction belongs to Instance/Sets/Products.v, is NOT repaired here,
 and is NOT claimed unavoidable.

 STRENGTHS, MEASURED STRICT-FIRST

 Holding at [eq_refl] (each an [Example] below, each a Leibniz equality
 and not an [≈]):

 [Sets_colim_carrier_is_coproduct]  the apex carrier IS the coproduct
 carrier -- the quotient leaves it
 alone;
 [Sets_colim_equiv_is_rel]          the apex's [≈] IS [colim_rel];
 [Sets_colim_inj_at]                the leg IS the sigma injection;
 [Sets_colim_inj_is_donor_composite] leg = donor composite;
 [Sets_colim_triangle]              the factorization triangle
 POINTWISE, one grade above the [≈]
 the universal property asks for;
 [Sets_Colimit_cocone]              the produced colimit's chosen cone
 IS [Sets_colim_cocone].

 REFUTED, and kept in two kinds.  Conversion negatives: [Sets_colim_obj]
 is not [Sets_colim_sum] (“cannot unify” -- the two share a carrier,
 which is the positive control, and differ in [is_setoid]); and the
 triangle as a Leibniz equality of WHOLE morphisms,
 [Sets_colim_med N ∘ Sets_colim_inj d = vertex_map[N]], is rejected,
 the composite rebuilding a [proper_morphism] certificate, while the
 pointwise form is the [Example] above.  Typing negative: the
 [Sets_Complete] instantiation quoted earlier.  None of the three is
 pinned in this file; all three are pinned in the probe.  (An earlier
 draft shipped only two: the whole-morphism triangle was measured here
 and guarded nowhere.)

 WHAT THIS UNLOCKS

 [Cocomplete] is a hypothesis of [adamek_cocomplete]
 (Theory/Adamek/Corollaries.v), of [creates_colimits_Cocomplete]
 (Structure/Limit/Creation.v) and of
 [Cocomplete_equivalence_invariant] (Instance/Proset/Limit.v).  Keep
 those two roles apart: [adamek_cocomplete] TAKES a [Cocomplete] but its
 own type is [@Initial (FAlg F)], so it is not in the list that follows.
 The constants whose TYPE is [@Cocomplete _] are exactly THREE --
 [creates_colimits_Cocomplete], [Cocomplete_equivalence_invariant] and
 [Proset_Cocomplete_of_all_joins] (Instance/Proset/Limit.v) -- and
 every one takes a hypothesis, a [Cocomplete] or a family of joins.  So
 this is the first hypothesis-free inhabitant.  (An earlier draft of
 this paragraph listed [adamek_cocomplete] among the four “constants
 whose type is [@Cocomplete _]”; that was a conflation of taking the
 class with having it as a type.)  It does NOT make [adamek_cocomplete]
 unconditional: that corollary still wants an [AdamekData], and
 Theory/Adamek/Corollaries.v records that no [AdamekData] witness
 is constructed anywhere in the tree.

 NON-VACUITY, AT ONE SHAPE -- READ THE SCOPE

 A colimit construction that identified every point would compile and
 satisfy the universal property vacuously, so the quotient is shown not
 to collapse.  **This is a witness at one shape, not a general
 non-collapse theorem**, and nothing below is claimed for any other
 diagram.

 The shape is [TwoDisc := DiscreteCat bool], whose hom type IS index
 equality ([two_disc_hom_is_eq], by [eq_refl]) -- so [cr_glue] can only
 relate an index to itself and has nothing to glue across the two
 objects, which is what makes this the sharp case.  The diagram
 [TwoPoints] puts a singleton over each object.  Then
 **[two_fibres_not_collapsed]**: the point of the fibre over [true] and
 the point of the fibre over [false] are NOT related by [colim_rel].
 [two_fibres_not_equal_in_colimit] restates it through the apex's own
 [≈], the same statement by [Sets_colim_equiv_is_rel].

 The proof is by mapping OUT, through [colim_rel_separates] at the
 cocone [TwoSep] whose leg at [b] is constant at [b] in the discrete
 setoid on [bool], landing on [discriminate].  No induction on
 [colim_rel] could have produced a negative.

 Three degeneracies are excluded by proof rather than by assertion.
 The shape has two distinct objects, so “the two fibres” names two
 things ([two_disc_objects_distinct]).  Both fibres are inhabited, and
 the theorem is stated at named inhabitants
 ([two_fibre_point_true]/[two_fibre_point_false]), each of which
 typechecks only because its fibre has an element -- so the statement is
 not vacuously true of no elements.  And the empty-shape reading, where
 the apex has no elements at all ([empty_shape_colim_empty]), is
 labelled in the file as a DEGENERATE CONTROL and deliberately does not
 stand alone: it separates for a reason unrelated to the glue.

 The complementary half -- that the quotient MERGES something the
 coproduct keeps apart -- cannot be shown at a discrete shape, there
 being no connecting maps, and is therefore not here.  It is
 Instance/Sets/Chain.v's [omega_stages_merged] together with
 [omega_stages_apart_in_coproduct], at the ω-shape.

 What the two witnesses JOINTLY establish is that NEITHER endpoint
 describes [colim_rel] uniformly: the ω pair refutes “always the
 coproduct's own relation”, the discrete witness refutes “always
 total”.  That is a statement about the FAMILY.  They do NOT show the
 relation strictly inside the interval at any one shape -- and at the
 two shapes exhibited here it is in fact AT an endpoint.  Measured, not
 shipped, since adding theorems is not what a correction is for: at
 [OmegaPoints] every fibre is a singleton and any two stages are
 ordered, so [colim_rel] is TOTAL; at [TwoPoints] the only homs are
 identities, so [cr_glue] never crosses an index and [colim_rel]
 coincides with the coproduct's own [≈].  An earlier draft said the two
 files “place [colim_rel] strictly between the coproduct's own relation
 and the total one -- each at its own shape”.  The hedge does not save
 it: no in-tree theorem supports “strictly between”, and the claim is
 refutable at both witnesses.

 WHAT IS NOT DELIVERED, SCOPED TO THIS FILE

 * No identification with any other colimit-shaped construction in
 [Sets]: no comparison with [Sets_HasCoequalizers]
 (Instance/Sets/Coequalizer.v), with [Sets_HasIndexedCoproducts]
 (Instance/Sets/Products.v) as the discrete-shape instance, with
 Instance/Sets/Pushout.v, or with [SetsCoend]
 (Instance/Sets/Coend.v), whose relation this one's shape follows.

 * No normal form for [colim_rel], hence no decision procedure, and in
 particular no theorem that two elements are related exactly when
 their images agree at a common later stage.

 * No functoriality of the colimit in [F], no preservation statement,
 and no [Complete (Sets^op)] (which would be this same statement read
 the other way round, and is not restated).

 * No ω-chain reading here.  Instance/Sets/Chain.v instantiates this
 constant at [Omega] and at Construction/Chain.v's [Chain], and proves
 the SUFFICIENT half of “the colimit is the union”; its own header
 records that the necessary half is not proved, and why.  Nothing in
 this file depends on that one.

 STATUS: axiom-free.  All 44 constants of this module -- 32 named, 8
 [Program] obligations and the 4 eliminators generated for [colim_rel]
 -- report “Closed under the global context”, enumerated by
 [Print Module] per the docs/AXIOMS.md methodology. 

 --------
 nLab:       https://ncatlab.org/nlab/show/cocomplete+category 
 nLab:       https://ncatlab.org/nlab/show/colimit 
 维基百科:  https://en.wikipedia.org/wiki/Limit_(category_theory) 

 Mac Lane，《为在职数学家准备的范畴论》第二版，Springer
 GTM 5 1998，§III.3（第67-68页），其中集合图的余极限是  [F d]  的不相交并集，并识别连接映射的像；以及 §V.1 练习8，“Set是余完备的”，要求给出一般性陈述——所有小余极限——而不仅仅是不断增加链的并集。Riehl，《情境中的范畴论》，Dover 2016，§3.1 示例3.1.26 是相同的计算。[Cocomplete C] 是 [∀ (D : Category) (F : D ⟶ C), Colimit F] （Structure/Complete.v），[Colimit F] 是 [Limit (F^op)] （Structure/Limit.v）：一个为每个图分配选定余极限的神谕。该文件在 [Sets] 中实现它，作为 Instance/Sets/Complete.v 的镜像。四个文件中的五个树内注释记录了缺失的答案——Instance/Sets/Complete.v、Instance/Sets/Coequalizer.v（两次）、Instance/Sets/Quotient.v，以及 Instance/Sets/Products.v，其“余完备性一点都没有在这里或树中的其他地方被讨论”是五个中最直白的——并且它存在于提供 [Sets_icoprod_obj] 的那个文件中，即该构造本身的源文件。当这个文件到达时，没有一个被修改过，且这五个都是陈旧的。自那以后，其中三个已在原位更正，现在指向此处（Complete.v 中的注释，以及 Coequalizer.v 中的第一个注释和 Quotient.v 中的一个注释）；Coequalizer.v 中的第二个注释和 Products.v 中的一个注释仍然显示为缺失。早期的草稿统计了三个注释，并说它们“仍按原样保留”——这其实有两处错误。

 构造

 [F : D ⟶ Sets] 的余极限是该图对象的索引余积，按连接映射生成的等价关系进行商化。三部分命名如下：

 [Sets_colim_sum] 是 [Sets_icoprod_obj (fun d : D => F d)]，即 Instance/Sets/Products.v 的 sigma 集合体——其元素是一个对 [(d; x)]，其中 [x] 是 [F d] 的元素；[colim_rel] 是在该载体上的归纳关系，它有两个生成子句，[cr_point]（纤维等价：[x ≈ y] 在 [F d] 中关联 [(d; x)] 和 [(d; y)]）和 [cr_glue]（图粘合：[(d; x)] 与 [(d'; fmap[F] f x 相关）对每个 [f : d ~> d'] 都成立，它在 [cr_sym] 和 [cr_trans] 下闭合，自反性作为 [colim_rel_refl] 推导，而不是作为第五个构造器采用——因此归纳有四种情况，正好是 Instance/Sets/Coend.v 中 [coend_eq] 的形式；[Sets_colim_obj] 是 [SetsQuotient]（实例/集合/商.v）通过第二个得到的第一个：相同的承载器，更粗的 [≈]。

 在 [d] 的腿是 [Sets_colim_inj d]，注入是 [x ↦ (d; x)]。来自竞争余锥 [N] 的中介是 [Sets_colim_med N]，它将 [(d; x)] 发送到 [N] 在 [d] 的自身腿应用于 [x]；这尊重 [colim_rel]，是通过关系的归纳，[cr_glue] 的情况是 [N] 的余锥在 [x] 点的相干性并对称化。交换性是 [reflexivity]，唯一性是竞争映射交换方程的对称性——与实例/集合/完全.v 中相同的两个闭合步骤。

 通过对偶性阅读义务因为 [Colimit F] 是 [Limit (F^op)]，下面构建的记录是一个 [Cone (F^op)]，即一个 [Cocone F]（Structure/Cone.v）。它在 [f : d ~{D^op}~> d'] 的相干场——也就是在 [f : d' ~{D}~> d]——读作 [ι_d ∘ fmap[F] f ≈ ι_{d'}] 在 [Sets] 中，这与 [cr_glue] 所述的协变方向相反；因此义务由 [cr_sym] 的一个 [cr_glue] 完成，而不是由 [cr_glue] 本身完成。普遍性质同样展开，使中介从顶点 [Sets_colim_obj ~{Sets}~> vertex_obj[N] 出来。

 来自 [Sets_Complete] 没有对偶捷径——是测量的，而非假定的[Sets_Complete]（实例/集合/完全.v）为每个 [F : D ⟶ Sets] 提供一个 [Limit F]。[F] 的余极限是 [F^op] 的极限，[F^op] 是一个到 [Sets^op] 的图；没有 [Sets_Complete] 的实例具有该类型。展开 [Sets_Complete (Opposite D) (Opposite_Functor F)] 时被拒绝，提示“项 'F^op' 的类型为 'D^op ⟶ Sets^op'，而期望类型为 'D^op ⟶ Sets'”，而正控制 [Sets_Complete D F : Limit F] 被接受。产生余极限的是 [Complete (Sets^op)]，而它再次是 [Cocomplete Sets]，因此对偶性不是一条途径。在此文件中没有保留 [Fail] 探针；所有三个反例都固定在 Test/ProbeCocomplete329.v 中。一个探针-卫生点，因为重写该测量的任何人都会遇到相同的陷阱：写作 [Sets_Complete (D^op) (F^op)] 会因为错误的原因而失败。Functor/Opposite.v 打开 [functor_scope]，其中 [_ ^op] 是 [Opposite_Functor]，因此 [D^op] 被解析为 [Opposite_Functor D]，错误是“术语 'D' 的类型为 'Category'，而预期类型为 '?C ⟶ ?D'”——这是符号冲突，而不是数学问题。上述测量按名称拼写出 [Opposite] 和 [Opposite_Functor]。这是符号保护实例 Instance/Rng/Mod.v 记录。

 这实际上*尚未*被证明，明确说明它没有通过“具有所有小型余积和余等化子的范畴是余完备的”。该定理在这个发展中并不涉及任何变异：在极限端，Instance/Sets/Complete.v 已经记录了它的缺失，反之这里或其他地方没有常量能从 [HasIndexedCoproducts] 和 [HasCoequalizers] 推导出 [Cocomplete]。更正 (#458)：自 #416 起，该定理在两种变异中都存在，Structure/Limit/FromProducts.v 的 [Complete_from_products_equalizers] 和 [Cocomplete_from_coproducts_coequalizers]；但 [Sets_Cocomplete] 仍未通过它，而 Instance/Top/Cocomplete.v 的 [PTop_Cocomplete_via_coproducts] 在 [PTopCat] 使用了第二项。特别是 [Sets_HasCoequalizers]（Instance/Sets/Coequalizer.v）未被使用。被使用的是它下面的层：两个对象 [Sets_icoprod_obj] 和 [SetsQuotient]。因此，这个非正式配方的两个部分都是实际的施体，但共同余子并不是其中之一，而且 Instance/Sets/Coequalizer.v 对其手工构建对象的预测“正是后来的 [Cocomplete Sets] 自身所需要的”并没有发生。

 还有两个常量存在，但不在通往 [Sets_Cocomplete] 的路径上：[Sets_colim_coarser] 和 [Sets_colim_inj_donors]，这条腿写作作为施体复合的 [sets_quot_proj ∘ Sets_icoprod_inj]。它们被保留下来，因为它们使得余积然后取商的来源被机器检查，而不仅仅是描述——[Sets_colim_inj_is_donor_composite] 将它们与实际使用的腿（在 [eq_refl]）等同——并且因为接下来记录的宇宙测量。

 来自约束块的小性与宇宙

 [About Sets_Cocomplete] 在 [Set Printing Universes] 下打印Sets_Cocomplete@{uc ud uo uso} : Cocomplete@{uc ud uo uso}
 ( * uc ud uo uso |= uc < uso   ud <= uc   ud <= uo   uc = uo   ... * )像 Instance/Sets.v 中那样写 [Sets@{o so}]，[uo] 是 [o] —— [Sets] 对象的 CARRIERS 的宇宙，以及它的 homs —— 并且 [uso] 是 [so]，其中 [obj[Sets] 自身存在。[Cocomplete@{a b c d}] 作用于 [C : Category@{d c c}] 并对 [D : Category@{b c c}] 进行量化，因此 [c] 是 D 的 hom 宇宙，被 [Cocomplete] 本身的类型强制等于 [Sets]，并且 [b] 是 D 的 OBJECT 宇宙。该块记录 [ud <= uo]：图表范畴的对象位于 [Sets] 的 carrier 宇宙之上或之下，并且不与之同一。那个不等式就是小性侧条件，它正是构造所需要的——sigma  [{ d : D & F d }] 和归纳  [colim_rel] 都对 [D] 的对象和箭头进行量化，因此当两者都位于 [o] 或以下时，它们可以作为 [Sets] 的载体。这是 Structure/Complete.v 描述的“D 相对于 C 小”的宇宙多态替代。 

 关于那个模块的两个测量结果。(1) 四个宇宙绑定器是刻意写出的。如果交给最小化处理，[Definition Sets_Cocomplete : @Cocomplete Sets := fun D F => Sets_Colimit F] 将展开为 [Sets_Cocomplete@{u u0} : Cocomplete@{u u u u0}]，它设定了 [ud := uo]，因此拒绝一个其对象严格位于 [Sets] 载体之下的图范畴。这个识别是最小化而不是约束：上面的带注释形式是被接受的，在声明的 [Constraint pd < po] 下实例化它也是被接受的。镜像 [Sets_Complete@{u u0} : Complete@{u u u u0}] 带有识别，但那里也是最小化——在一个试验会话中其主体上的相同注释也是被接受的——因此这里没有任何内容表明极限本质上比余极限更严格，并且 Instance/Sets/Complete.v 没有被编辑。(2) 如果该腿是捐赠组合，则该标识将返回。[Sets_icoprod_inj@{u u0}]（实例/集合/产品.v）仅携带两个宇宙绑定器，并将其族类型定为[A → SetoidObject@{u u}]，与[A : Type@{u}]一起，将索引类型的宇宙与集合载体宇宙识别在一起，而[Sets_icoprod_obj@{u u0 u1 u2}]在[u <= u0]下将它们分开。在当前文件中测量：[Sets_colim_inj_donors]携带[u = u0]，其中直接[Sets_colim_inj]携带[u <= u0]。在较早的修订版中测量，其中捐赠组合确实是该腿：该标识会传播，给[Sets_Colimit]，从而给[Sets_Cocomplete]赋予引脚[ud = uo]。后半部分是关于不在树中的修订的反事实，所以无法仅从此文件重新检查；只有前半部分可以。捐赠者的限制属于 Instance/Sets/Products.v，这里未修复，也未声称不可避免。

 强度，严格优先测量

 在 [eq_refl] 处保持（下方的每个 [Example]，每个都是莱布尼茨等式，而不是 [≈] ）:[Sets_colim_carrier_is_coproduct] 顶点载体 是 余积载体 -- 商保持不变；
 [Sets_colim_equiv_is_rel] 顶点的 [≈] 是 [colim_rel]；
 [Sets_colim_inj_at] 边 是 σ 注入；
 [Sets_colim_inj_is_donor_composite] 边 = 赠与者复合；
 [Sets_colim_triangle] 分解三角形
 逐点地，比 [≈] 的等级高一级
 普适性要求的；
 [Sets_Colimit_cocone] 产生的余极限的选定锥
 是 [Sets_colim_cocone]。已被驳回，并保留为两种类型。转换否定：[Sets_colim_obj] 不是 [Sets_colim_sum] （“无法统一”——两者共享一个载体，即阳性对照，并在 [is_setoid] 上有所不同）；以及作为整体态射的莱布尼茨等式的三角形，[Sets_colim_med N ∘ Sets_colim_inj d = vertex_map[N]] 被拒绝，复合物重建 [proper_morphism] 证书，而逐点形式是上述 [Example]。类型否定：之前引用的 [Sets_Complete] 实例化。三者在此文件中没有固定；三者在探针中均已固定。（之前的一个草稿仅发布了两个：整体态射三角形在此测量，但未在任何地方防护。）

 这将解锁的内容[Cocomplete] 是 [adamek_cocomplete]（Theory/Adamek/Corollaries.v）、[creates_colimits_Cocomplete]（Structure/Limit/Creation.v）和 [Cocomplete_equivalence_invariant]（Instance/Proset/Limit.v）的一种假设。将这两种角色区分开：[adamek_cocomplete] 需要一个 [Cocomplete]，但它自身的类型是 [@Initial (FAlg F)]，因此它不在下面的列表中。类型为 [@Cocomplete _] 的常量恰好有三个——[creates_colimits_Cocomplete]、[Cocomplete_equivalence_invariant] 和 [Proset_Cocomplete_of_all_joins]（Instance/Proset/Limit.v）——每一个都需要一个假设，即一个 [Cocomplete] 或一些联合的族。因此，这是第一个无假设的元素。（这一段的早期草稿将 [adamek_cocomplete] 列为四个“类型为 [@Cocomplete _] 的常量”之一；这是把类和它作为类型混为一谈。）它并不使 [adamek_cocomplete] 无条件成立：那个推论仍然需要一个 [AdamekData]，而 Theory/Adamek/Corollaries.v 记录了在树中的任何地方都没有构造出 [AdamekData] 的见证。

 非空性，在某一形状下——阅读范围

 一个将所有点识别在一起的余极限构造将会编译并满足平凡的泛性质，因此商对象被证明不会塌缩。**这是某一形状下的一个见证，而不是一般的非塌缩定理**，以下内容对于任何其他图形都不做声明。这个形状是 [TwoDisc := DiscreteCat bool]，其同类型是索引相等（[two_disc_hom_is_eq]，通过 [eq_refl]）——所以 [cr_glue] 只能将一个索引与自身相关联，无法在这两个对象之间建立任何联系，这正是使其成为尖锐情况的原因。图表 [TwoPoints] 将每个对象上放置了一个单元素集。然后 **[two_fibres_not_collapsed]**：[true] 上纤维的点和 [false] 上纤维的点不通过 [colim_rel] 相关联。[two_fibres_not_equal_in_colimit] 通过顶点自身的 [≈] 来重述，同样的陈述由 [Sets_colim_equiv_is_rel] 表达。证明是通过 [colim_rel_separates] 映射 OUT，在余锥 [TwoSep] 上，其在 [b] 的腿在 [bool] 的离散集合等价类上恒定为 [b]，到达 [discriminate]。对 [colim_rel] 的归纳无法得到一个否定。三种退化情况是通过证明排除的，而不是通过断言排除的。
 该形状有两个不同的对象，所以“两个纤维”指的是两个事物（[two_disc_objects_distinct]）。两个纤维都是非空的，并且定理是在命名的元素上陈述的（[two_fibre_point_true] / [two_fibre_point_false]），每个元素的类型检查之所以成立，仅仅是因为它的纤维中有元素——因此该陈述不是对没有元素的情况成立的空洞真理。而空形状的理解，即顶点根本没有元素（[empty_shape_colim_empty]），在文件中被标记为退化控制（DEGENERATE CONTROL），并且故意不单独存在：它因为与胶合无关的原因而被分开。互补的一半——即商合并了余积分开的东西——无法在离散形状上显示，因为没有连接映射，因此这里不存在。它是 Instance/Sets/Chain.v 中的 [omega_stages_merged] 以及 [omega_stages_apart_in_coproduct]，在 ω 形状上。两个见证者共同确认的是，没有一个端点能够统一描述 [colim_rel]：ω 对证伪了“总是余积自身的关系”，离散见证者证伪了“总是全体的”。这是一条关于族的陈述。他们并没有展示在任何一个形状的区间内部的严格关系——而在这里展示的两个形状上，它实际上是在端点处。测量的，而不是传送的，因为添加定理并不是修正的目的：在 [OmegaPoints] 上，每个纤维都是单元集合，任何两个阶段都是有序的，因此 [colim_rel] 是全体的；在 [TwoPoints] 上，唯一的同态是恒等映射，因此 [cr_glue] 从未跨越索引，并且 [colim_rel] 与余积自身的 [≈] 重合。早期草稿说这两个文件“将 [colim_rel] 严格地置于余积自身的关系和总体关系之间——各自保持其自身的形状”。这种保留并没有挽救它：没有任何树内定理支持“严格之间”，而且该说法在两个见证下都是可反驳的。

 本文件未完成的内容范围

 * 未与 [Sets] 中的任何其他余极限形状构造进行识别：未与 [Sets_HasCoequalizers] (Instance/Sets/Coequalizer.v) 比较，未与 [Sets_HasIndexedCoproducts] (Instance/Sets/Products.v) 作为离散形状实例比较，未与 Instance/Sets/Pushout.v 比较，也未与 [SetsCoend] (Instance/Sets/Coend.v) 比较，其关系遵循本文件的形状。* 对于 [colim_rel] 没有规范形式，因此没有判定程序，尤其是没有定理表明两个元素只有在其映像在某个后续阶段一致时才相关。  

 * 在 [F] 中没有余极的函子性，没有保持性质的陈述，也没有 [Complete (Sets^op)]（这就是将相同的陈述反过来读，但并未重述）。  

 * 这里没有 ω 链的读取。Instance/Sets/Chain.v 在 [Omega] 和 Construction/Chain.v 的 [Chain] 实例化了这个常数，并证明了“余极是并集”的充分部分；其自身标题记录了必要部分未被证明的原因。这个文件中的内容不依赖于那个文件。状态：无公理。该模块的所有44个常量——32个已命名，8个[Program]义务以及为[colim_rel]生成的4个消去器——均报告为“在全局上下文下闭合”，由[Print Module]按照docs/AXIOMS.md方法列出。
*)

#[local] Obligation Tactic := idtac.

Section SetsColimit.

Context {D : Category}.
Context (F : D ⟶ Sets).

(* * ** The indexed coproduct of the diagram's objects / * ** 图中对象的索引积 *)

Definition Sets_colim_sum : obj[Sets] := Sets_icoprod_obj (fun d : D => F d).

(* * ** The relation generated by the connecting maps / * ** 由连接映射生成的关系 *)

Inductive colim_rel :
  carrier Sets_colim_sum -> carrier Sets_colim_sum -> Type :=
  | cr_point : forall (d : D) (x y : F d), x ≈ y ->
      colim_rel (existT _ d x) (existT _ d y)
  | cr_glue  : forall (d d' : D) (f : d ~{D}~> d') (x : F d),
      colim_rel (existT _ d x) (existT _ d' (fmap[F] f x))
  | cr_sym   : forall p q, colim_rel p q -> colim_rel q p
  | cr_trans : forall p q r, colim_rel p q -> colim_rel q r -> colim_rel p r.

Lemma colim_rel_refl (p : carrier Sets_colim_sum) : colim_rel p p.
Proof. destruct p as [d x]; apply cr_point; reflexivity. Qed.

Definition colim_rel_Equivalence : Equivalence colim_rel.
Proof.
  constructor.
  - exact colim_rel_refl.
  - exact cr_sym.
  - exact cr_trans.
Defined.

(* * ** The colimit apex: the coproduct quotiented by that relation / * ** 上极点的余极限：被该关系商的余积 *)

Definition Sets_colim_obj : obj[Sets] :=
  SetsQuotient Sets_colim_sum colim_rel colim_rel_Equivalence.

Lemma Sets_colim_coarser : SetoidCoarser colim_rel.
Proof.
  intros [d x] [d' y] [e Hxy]; simpl in *.
  destruct e; simpl in *.
  now apply cr_point.
Qed.

Program Definition Sets_colim_inj (d : D) :
  F d ~{Sets}~> Sets_colim_obj := {|
  morphism := fun x => existT _ d x
|}.
Next Obligation. intros d x y Hxy; apply cr_point; exact Hxy. Qed.

Definition Sets_colim_inj_donors (d : D) : F d ~{Sets}~> Sets_colim_obj :=
  sets_quot_proj Sets_colim_sum colim_rel colim_rel_Equivalence
    Sets_colim_coarser ∘ Sets_icoprod_inj (fun d : D => F d) d.

Example Sets_colim_inj_is_donor_composite (d : D) (x : F d) :
  Sets_colim_inj d x = Sets_colim_inj_donors d x.
Proof. reflexivity. Qed.

(* * ** What the apex is, by conversion / * ** 通过转换，顶点是什么 *)

(*
 The quotient leaves the carrier alone, so the colimit carrier IS the
 coproduct carrier -- the [eq_refl] exception to the `≈` discipline that
 Instance/Sets/Quotient.v's [sets_quot_carrier] records generically. 

 --------
 商保留了承载对象本身，所以余极限承载对象就是余积承载对象——Instance/Sets/Quotient.v 的 [sets_quot_carrier] 记录在 `≈` 规范中通常情况下的 [eq_refl] 例外。
*)
Example Sets_colim_carrier_is_coproduct :
  carrier Sets_colim_obj = Sets_icoprod_carrier (fun d : D => F d).
Proof. reflexivity. Qed.

(* ... and the apex's own `≈` IS the generated relation. / ... 而顶点本身的 `≈` 就是生成的关系。 *)
Example Sets_colim_equiv_is_rel (p q : carrier Sets_colim_sum) :
  @equiv _ Sets_colim_obj p q = colim_rel p q.
Proof. reflexivity. Qed.

(* The leg at [d] is the [d]th coproduct injection on elements. / 在 [d] 上的腿是元素上的 [d] 个余积注入。 *)
Example Sets_colim_inj_at (d : D) (x : F d) :
  Sets_colim_inj d x = existT _ d x.
Proof. reflexivity. Qed.

(** ** The colimit cocone / ** 余极锥 *)

Program Definition Sets_colim_cocone : Cocone F := {|
  vertex_obj := Sets_colim_obj;
  coneFrom   := {| vertex_map := Sets_colim_inj |}
|}.
Next Obligation.
  intros d d' f x.
  exact (cr_sym _ _ (cr_glue d' d f x)).
Qed.

(* * ** The mediator into a competing cocone / * ** 进入竞争余圆锥的中介 *)

Definition Sets_colim_med_fun (N : Cocone F)
  (p : carrier Sets_colim_sum) : carrier (vertex_obj[N]) :=
  match p with
  | existT _ d x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) d x
  end.

Lemma Sets_colim_med_respects (N : Cocone F)
  (p q : carrier Sets_colim_sum) (H : colim_rel p q) :
  Sets_colim_med_fun N p ≈ Sets_colim_med_fun N q.
Proof.
  induction H as [d x y Hxy | d d' f x | p q H IH | p q r H1 IH1 H2 IH2].
  - now apply proper_morphism.
  - symmetry.
    exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) d' d f x).
  - now symmetry.
  - now transitivity (Sets_colim_med_fun N q).
Qed.

Program Definition Sets_colim_med (N : Cocone F) :
  Sets_colim_obj ~{Sets}~> vertex_obj[N] := {|
  morphism := Sets_colim_med_fun N
|}.
Next Obligation.
  intros N p q Hpq; exact (Sets_colim_med_respects N p q Hpq).
Qed.

(*
 The factorization triangle holds at LEIBNIZ equality, one grade above the
 `≈` the universal property asks for: the mediator's value on the [d]th
 injection IS the competing cocone's leg at [d], by conversion. 

 --------
 在莱布尼茨等式下，因式分解三角形成立，比 `≈` 要求的普适性高一级：通过转换，中介在 [d] 注入上的值就是竞争余锥在 [d] 上的边。
*)
Example Sets_colim_triangle (N : Cocone F) (d : D) (x : F d) :
  Sets_colim_med N (Sets_colim_inj d x)
    = @vertex_map _ _ _ _ (@coneFrom _ _ _ N) d x.
Proof. reflexivity. Qed.

(*
 Mapping OUT is how the quotient is shown not to collapse: no induction on
 [colim_rel] can yield a negative, but a cocone that separates two points
 proves they are unrelated.  It is spent at the end of this file, on
 [two_fibres_not_collapsed]. 

 --------
 映射 OUT 是展示商不坍塌的方式：对 [colim_rel] 的归纳不能产生负值，但一个分离两点的余锥证明了它们无关。它在此文件末尾用于 [two_fibres_not_collapsed]。
*)
Lemma colim_rel_separates (N : Cocone F) (p q : carrier Sets_colim_sum) :
  (Sets_colim_med_fun N p ≈ Sets_colim_med_fun N q -> False) ->
  colim_rel p q -> False.
Proof. intros Hne Hpq; exact (Hne (Sets_colim_med_respects N p q Hpq)). Qed.

(** ** The colimit / ** 共极限 *)

Program Definition Sets_Colimit : Colimit F := {|
  limit_cone := Sets_colim_cocone;
  ump_limits := fun N => {| unique_obj := Sets_colim_med N |}
|}.
Next Obligation. intros N d x; reflexivity. Qed.
Next Obligation.
  intros N v Hv p; destruct p as [d x]; symmetry; exact (Hv d x).
Qed.

(*
 The chosen cocone of the produced colimit is the one built above, by
 conversion.  (Its apex is then [Sets_colim_obj] by the same conversion;
 that reading is stated separately, in Instance/Sets/Chain.v, as
 [Sets_omega_apex].) 

 --------
 所产生余极的选定余锥是上面构建的那个，通过转换得到的。（其顶点通过相同的转换是 [Sets_colim_obj]；这个读法在 Instance/Sets/Chain.v 中单独说明为 [Sets_omega_apex]。）
*)
Example Sets_Colimit_cocone :
  @limit_cone _ _ _ Sets_Colimit = Sets_colim_cocone.
Proof. reflexivity. Qed.

End SetsColimit.

(*
 [Sets] is cocomplete: every diagram of every shape has a colimit.  The
 universe binders are written out rather than left to minimization; see the
 header for what that buys and what it does not. 

 --------
 [Sets] 是余完备的：每种形状的每个图都有余极限。宇宙绑定器是显式写出的，而不是留给最小化处理；参见标题了解它带来了什么，以及它没有带来什么。
*)
Definition Sets_Cocomplete@{uc ud uo uso} :
  @Cocomplete@{uc ud uo uso} Sets@{uo uso} := fun D F => Sets_Colimit F.

(* * * Non-vacuity, at the two-object discrete shape / * * 非空性，在二种对象的离散形态上 *)

(*
 Everything below is about ONE shape and ONE diagram.  It is a witness,
 not a general non-collapse theorem, and the header says so. 

 --------
 下面的内容都是关于一个形状和一个图表的。它是一个实例，而不是一般性的非塌陷定理，标题里也说明了这一点。
*)

Section TwoDiscreteWitness.

(*
 The two-object discrete shape.  Its hom type IS index equality, by
 conversion, which is precisely why [cr_glue] has nothing to glue across
 the two objects: a morphism can only relate an index to itself. 

 --------
 双对象离散形状。它的同构类型是指数相等，通过转换，这正是为什么 [cr_glue] 在两个对象之间没有任何可连接的东西：一个态射只能将一个指数与其自身相关联。
*)
Definition TwoDisc : Category := DiscreteCat bool.

Example two_disc_hom_is_eq (b b' : bool) :
  (b ~{TwoDisc}~> b') = (b = b').
Proof. reflexivity. Qed.

(*
 ... and the shape really does have two objects, so “the two fibres”
 below names two things and not one. 

 --------
 ...而且这个形状确实有两个物体，所以下面的“这两根纤维”指的是两件事，而不是一件。
*)
Lemma two_disc_objects_distinct : (true : TwoDisc) = (false : TwoDisc) -> False.
Proof. discriminate. Qed.

(*
 The diagram: a singleton setoid over each of the two objects.  Both
 fibres are INHABITED, by [ttt], so the separation proved below is a
 statement about actual elements and not vacuously true. 

 --------
 图表：每个两个对象上都有一个单例集合。两个纤维都是有元素的，由 [ttt]，因此下面证明的分离是关于实际元素的陈述，而不是空洞地为真。
*)
Program Definition TwoPoints : TwoDisc ⟶ Sets := {|
  fobj := fun _ => unit_setoid_object;
  fmap := fun _ _ _ => id
|}.
(*
 Measured: [fmap_respects] never surfaces as an obligation here, the
 arrow action being constant; the two that do are [fmap_id] and
 [fmap_comp]. 

 --------
 Measured: [fmap_respects] 在这里从未作为一种义务出现，箭头动作是恒定的；出现义务的两个是 [fmap_id] 和 [fmap_comp]。
*)
Next Obligation. intros x; reflexivity. Qed.
Next Obligation. intros x y z f g; symmetry; apply id_left. Qed.

(*
 The separating cocone: the leg at [b] is constant at [b] in the
 discrete setoid on [bool].  Respectfulness is free (the map ignores its
 argument) and the cocone coherence is available because a morphism of
 [TwoDisc] IS an equality of its two indices. 

 --------
 分离余锥：在  [b]  的腿在  [b]  上是恒定的，在  [bool]  的离散集合上。尊重性是免费的（映射忽略其参数），并且余锥的相干性是可用的，因为  [TwoDisc]  的一个态射是其两个指标的相等。
*)
Program Definition two_sep_leg (b : bool) :
  TwoPoints b ~{Sets}~> bool_setoid_object := {|
  morphism := fun _ => b
|}.
(*
 Measured: [proper_morphism] never surfaces as an obligation here
 either, the map being constant, so none is written out. 

 --------
 测量：[proper_morphism] 在这里也从未以义务的形式出现，地图保持不变，因此没有被写出来。
*)

Program Definition TwoSep : Cocone TwoPoints := {|
  vertex_obj := bool_setoid_object;
  coneFrom   := {| vertex_map := two_sep_leg |}
|}.
Next Obligation. intros b b' e x; exact (eq_sym e). Qed.

(*
 The two fibres are INHABITED, and these are the points the separation
 below is stated at -- so the theorem is about actual elements, not
 vacuously true.  Naming them makes that machine-checked rather than a
 remark: each definition typechecks only because the fibre it names has
 an element. 

 --------
 这两条纤维是有元素的，并且下面所述的分离点就是这些点——因此这个定理是关于实际元素的，而不是空真。命名它们使得这个过程经过机器检查，而不仅仅是一个注释：每个定义类型的检查通过，仅仅是因为它所命名的纤维有一个元素。
*)
Definition two_fibre_point_true : carrier (TwoPoints true) := ttt.
Definition two_fibre_point_false : carrier (TwoPoints false) := ttt.

(*
 THE WITNESS.  The point of the fibre over [true] and the point of the
 fibre over [false] are NOT identified by the generated relation, so
 [colim_rel] does not collapse this colimit.  Proved by mapping OUT
 through [colim_rel_separates] -- no induction on [colim_rel] could
 yield a negative -- and landing on [discriminate]. 

 --------
 证人。纤维在 [true] 上的点与纤维在 [false] 上的点没有通过生成的关系被识别，因此 [colim_rel] 不会使这个余极限塌缩。通过映射 OUT 经过 [colim_rel_separates] 进行证明——对 [colim_rel] 的任何归纳都不可能得到负结果——最终落在 [discriminate] 上。
*)
Theorem two_fibres_not_collapsed :
  colim_rel TwoPoints
    (existT _ true two_fibre_point_true)
    (existT _ false two_fibre_point_false) -> False.
Proof.
  apply (colim_rel_separates TwoPoints TwoSep).
  discriminate.
Qed.

(* Read through the apex's own `≈` rather than through [colim_rel], which is the same statement by [Sets_colim_equiv_is_rel]. / 请阅读 apex 自己的 `≈`，而不是通过 [colim_rel]，后者是 [Sets_colim_equiv_is_rel] 的相同声明。 *)
Corollary two_fibres_not_equal_in_colimit :
  @equiv _ (Sets_colim_obj TwoPoints)
    (existT _ true two_fibre_point_true)
    (existT _ false two_fibre_point_false) -> False.
Proof. exact two_fibres_not_collapsed. Qed.

(*
 DEGENERATE CONTROL, and labelled as one: over the EMPTY shape the apex
 has no elements at all, so it separates for a reason that has nothing
 to do with the glue.  This is why it does not stand alone. 

 --------
 退化控制，并被标记为一个：在空形上，顶点根本没有任何元素，所以它分离是有原因的，这个原因与胶水无关。这就是它不能单独存在的原因。
*)
Lemma empty_shape_colim_empty (F : DiscreteCat False ⟶ Sets)
  (p : carrier (Sets_colim_obj F)) : False.
Proof. destruct p as [d x]; destruct d. Qed.

End TwoDiscreteWitness.
