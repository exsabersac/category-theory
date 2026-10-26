(* * * The components functor and its right adjoint / * * 组成函子及其右伴随 *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.One.
Require Import Category.Instance.Roof.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Theory.Connected.Components.
Require Import Category.Construction.Comma.Special.

Generalizable All Variables.

(*
 Book:      Mac Lane, “Categories for the Working Mathematician”,
 Springer GTM 5, 2nd ed., §IV.2 Exercise 9, printed p. 90
 (maclane:IV.2:ex9), where the result is attributed to
 N. Smythe.
 Book:      Riehl, “Category Theory in Context”, Dover 2016, §1.5,
 printed p. 35 (connected categories) and §4.1
 nLab:      https://ncatlab.org/nlab/show/connected+component
 nLab:      https://ncatlab.org/nlab/show/discrete+category
 nLab:      https://ncatlab.org/nlab/show/adjoint+string
 nLab:      https://ncatlab.org/nlab/show/reflective+subcategory
 nLab:      https://ncatlab.org/nlab/show/Cat
 Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

 Mac Lane's exercise asks for the adjoint string carried by the functor
 sending a category to its set of objects:

 Components  ⊣  Discrete  ⊣  Objects  ⊣  Indiscrete

 This file delivers the LEFTMOST adjunction, [Pi0 ⊣ Cat_Disc], and it
 delivers it OVER A DIFFERENT PAIR OF CATEGORIES from the one its
 right-hand neighbour lives over.  That is the file's principal
 finding and §7 proves the half of it that is provable; the rest of
 this header says exactly which half.

 Delivered here:

 (a) [Cat_Disc : Sets ⟶ Cat], the discrete functor.  This is the
 FIRST functor of that type in the tree, and the claim is a
 measurement by TYPE rather than by name: no constant of type
 [Sets ⟶ Cat] or [Sets ⟶ StrictCat] is declared in any `.v`
 file, the only occurrences of those two tokens being prose --
 Theory/Connected/Components.v recording the absence, and
 Instance/Indiscrete.v's item II anticipating this file by
 name.  The only [Cat ⟶ Sets] is [Pi0] itself.

 (b) [pi0_adj_iso], the hom-setoid isomorphism, and the packaged
 record [Components_Disc_Adjunction : Pi0 ⊣ Cat_Disc].

 (c) [Cat_Disc_Full], [Cat_Disc_Faithful], and [pi0_counit_iso] --
 the counit is an isomorphism, which is Mac Lane's “the
 components of a discrete category are its objects” and which
 exhibits [Sets] as a REFLECTIVE subcategory of [Cat] with
 reflector π₀.

 (d) The refutation that fixes the right adjoint:
 [DiscreteCat_carrier_not_functorial], with its general form
 [no_skeletal_carrier_functor_Sets_Cat] and the discriminating
 [Cat_Disc_not_skeletal].

 (e) Non-vacuity over [Roof]: [Pi0_not_Faithful] and
 [unit_not_Full], so π₀ genuinely forgets and the adjunction is
 not an equivalence.

 I. A PRIOR-ART CORRECTION, ON THREE COUNTS, EACH MEASURED.

 FIRST, the catalog issue's work item 4 asks that the
 connected-components functor be defined.  That is FALSE.
 Theory/Connected/Components.v declares [Pi0 : Cat ⟶ Sets]
 with [fobj := pi0] and [fmap := pi0_fmap], and proves its three
 functor laws.  It is CONSUMED here and nothing rebuilds it: the
 names [pi0], [pi0_fmap], [ZigZag], [hom_zigzag] and [zigzag_fmap]
 are used exactly as that file and Structure/Groupoid/Connected.v
 declare them, and this file declares no zig-zag machinery of its
 own.  What was missing is the ADJUNCTION, and that absence is
 recorded in the donor's own NOT-delivered list, at
 Theory/Connected/Components.v: “NO LEFT ADJOINT.
 [Pi0 : Cat ⟶ Sets] is built, but the discrete functor
 [Sets ⟶ Cat] and the adjunction π₀ ⊣ discrete are not.”  That
 standing deferral is what this file discharges.

 SECOND, the discrete category on a SETOID already exists too:
 Construction/Comma/Special.v's [DiscreteSetoidCat], built
 there so that the comma of two constant functors could be
 identified.  It is CONSUMED here and gets its first consumer
 outside its own file (measured: before this commit the token
 [DiscreteSetoidCat] occurred in exactly one `.v` file).  What was
 absent is its arrow action and any functor built on it; both are
 new here, and the arrow action is three lines, since a morphism of
 [DiscreteSetoidCat S] IS a proof of [≈] and [proper_morphism] IS
 the required action on it.

 THIRD, the same correction the sibling module records applies:
 Instance/Discrete/Reconstruct.v's [Indiscrete] exists.  It
 plays no part below -- the indiscrete half of Mac Lane's string is
 the OTHER wing -- and is named here only so that this header does
 not appear to contradict the sibling's.

 II. THE STRING SPLITS, AND THE SPLIT IS NOT A NAMING ACCIDENT.

 Instance/Cat/Objects.v settles the middle adjunction over
 [StrictCat] and [Coq], and both of its settlements are forced by
 refutation: no objects functor exists over [Cat] into a
 Leibniz-comparing target (its §6,
 the swap endofunctor of [Indiscrete bool] being [≈] to the
 identity in [Cat] while their object maps differ), and no
 carrier-based object map [Sets → StrictCat] respects [≈] (its §7).
 Its discrete functor is therefore [StrictCat_Disc : Coq ⟶
 StrictCat], built on Instance/Discrete.v's [DiscreteCat].

 [Pi0] shares NEITHER end with that: its source is [Cat] and its
 target is [Sets].  So [Pi0 ⊣ Cat_Disc] is a statement about a
 different pair of categories, and Mac Lane's four adjoints do not
 form one string in this library -- they exist as TWO strings of
 two, meeting nowhere.  Instance/Indiscrete.v's [adjoint_string]
 packages the other one, and packages only two components for
 exactly this reason; the three headers agree, and each says so.
 (That file is cited by NAME rather than by line: it landed
 alongside this one and its line numbers were still moving.)

 What is PROVED here rather than observed is the sharper half: even
 after moving to [Cat] and [Sets], the right adjoint CANNOT be the
 plain discrete category.  [DiscreteCat_carrier_not_functorial]
 (§7) refutes the [fmap_respects] field of the only candidate,
 exhibiting [bool] under the everywhere-true setoid, where
 [id ≈ negb] holds in [Sets] while a natural isomorphism between
 the induced functors would give [true = false].  So the two
 [Discrete]s of the string are different functors on different
 categories, not one functor described twice.

 SCOPE THAT CLAIM EXACTLY.  What is refuted is the carrier-based
 DISCRETE object map.  Nothing here proves that no [Coq]-valued π₀
 exists, nor that the two wings could not be reconciled by some
 construction not attempted here; the sibling module disclaims the
 same thing from its side.  The general form
 [no_skeletal_carrier_functor_Sets_Cat] says what the obstruction
 is: a right adjoint to π₀ whose objects are the CARRIER cannot have
 SKELETAL fibres.  [Cat_Disc] escapes it, and escapes it by exactly that
 clause -- [Cat_Disc_not_skeletal] proves the skeletality hypothesis is
 the one it fails, while [cat_disc_Kobj] and [cat_disc_Kinj] discharge
 the other two (the first at [eq_refl], the second by the identity
 function).  So the refutation is not vacuous and the escape is located
 rather than assumed.

 THIS FILE DOES NOT REQUIRE Instance/Cat/Objects.v, and the reason
 is measured rather than stylistic: importing it adds 24 modules to
 a 54-module closure (among them Instance/Coq.v, Theory/Monad.v and
 the eight Structure/Monoidal ones), and it would buy nothing, the
 two developments having no category in common.  Its refutations
 are therefore CITED above, not re-derived, and the citations are
 marked as citations.

 NAMING.  [Objects], [Discrete] and [Indiscrete] are all taken -- by
 Solver/Expr.v's reification class, by Structure/Discrete.v's
 predicate and by Instance/Discrete/Reconstruct.v's category
 respectively -- so the sibling module adopted the
 Instance/Top/Forgetful.v convention of prefixing with the structured
 category.  This file follows it: [Cat_Disc] for the functor into [Cat],
 reserving [Cat_Indisc] should the indiscrete half ever be wanted at this
 pair.  [Cat_Disc], [Cat_Disc_map], [disc_setoid_iso],
 [zigzag_setoid_contract], [pi0_to], [pi0_from], [pi0_adj_iso] and
 [Components_Disc_Adjunction] were each verified to have zero tree-wide
 occurrences first.

 III. STRENGTHS, MEASURED STRICT-FIRST.

 Ten readbacks hold at [eq_refl] and are shipped as [Example]s: the
 object action of [Cat_Disc], its object type and hom type
 ([cat_disc_obj], [cat_disc_obj_carrier], [cat_disc_hom]), the object
 action of its arrow action ([cat_disc_fmap]); both legs of the
 transposition ([pi0_adj_to_at], [pi0_adj_from_at]); THE UNIT IS THE
 IDENTITY FUNCTION ON THE NOSE ([pi0_unit_is_id]) and so is the counit
 ([pi0_counit_is_id]); and both legs of [pi0_counit_iso].  Four
 FURTHER [eq_refl]s appear below as CONTROLS localizing the two
 refuted round trips and the [Kobj] clause of §7 -- eighteen
 occurrences of [:= eq_refl] in all, of which four sit inside a
 [Fail] and are refutations rather than readbacks.

 NEITHER ROUND TRIP IS STRICT, AND THE TWO FAIL FOR DIFFERENT
 REASONS, EACH LOCALIZED BY A CONTROL.

 On the [Sets] side the residue is a CERTIFICATE.
 [pi0_rt_from_to_strict] is refuted at [eq_refl], while
 [pi0_rt_from_to_at] (the value at each point) and [pi0_rt_from_to_fn]
 (the whole [morphism] FIELD) both hold on the nose.  [SetoidMorphism] is
 a [Record] under [Set Primitive Projections] (Lib/Setoid.v,
 Instance/Sets.v), so it has eta and record equality IS field
 equality: what differs is therefore exactly [proper_morphism], which
 [pi0_from] rebuilds from [zigzag_setoid_contract].

 On the [Cat] side the residue is PROOF-RELEVANT DATA, and this is the
 sharper of the two.  [pi0_rt_to_from_strict] is refuted, and the OBJECT
 action returns on the nose ([pi0_rt_to_from_obj]) while the ARROW action
 does not ([pi0_rt_to_from_map], also refuted).  The cause is structural
 rather than incidental: a morphism of [DiscreteSetoidCat S] IS a proof
 of [≈], and two proofs of one [≈] need not be Leibniz-equal, so a round
 trip through that category cannot recover a proof term.

 AND THE [≈] THAT REPLACES IT IS VACUOUS, WHICH IS WORTH SAYING RATHER
 THAN GLOSSING.  [DiscreteSetoidCat]'s hom-setoid identifies ALL parallel
 arrows ([cat_disc_hom_trivial], proof [I]), so
 [pi0_rt_to_from_map_equiv] is [I] and holds of any two parallel arrows
 whatever -- it verifies nothing about the round trip.  The whole content
 of [iso_from_to] for [pi0_adj_iso] is therefore the OBJECT family, which
 is [eq_refl].  The same observation explains why the adjunction is so
 cheap: the naturality clause of [≈] in [Cat] is [True] at a thin target.

 THE ADJUNCTION RECORD COSTS TWO OBLIGATIONS IN TOTAL and both are
 in [pi0_adj_iso]'s two [Proper] fields; the two round trips of
 the isomorphism and both naturality clauses demanded by
 [Build_Adjunction'] are discharged by the ambient obligation
 tactic.  [Build_Adjunction'] (Theory/Adjunction.v) is used
 rather than [Build_Adjunction] for the same measured economy the
 sibling module records: it asks only for the two [to]-side
 clauses.

 NO ANALOGUE OF THE Instance/Top/Forgetful.v WALL ARISES.  That
 file's [Discrete ⊣ Forget ⊣ Indiscrete] for [Top] is forced into
 transposition isomorphisms because [Top]'s homs sit strictly above
 its points, so no single [Sets] serves both directions.  Here both
 functors run between one [Cat] and one [Sets] and the packaged
 record is built.  There IS a universe restriction, but it is a
 different one and it is the donor's; see the next item.

 IV. UNIVERSES, MEASURED OFF BOTH THE BLOCK AND THE BINDER.

 EXACTLY ONE OF THE 73 CONSTRAINT BLOCKS CONTAINS A UNIVERSE EQUATION,
 and it is the PROBE of §8's third section, whose [hc = hd] is disclosed
 three paragraphs below.  Every entry of every other block is a [<] or a
 [<=]; that was checked constant by constant rather than sampled.
 [Cat_Disc@{u u0}], [pi0_to@{u u0}], [pi0_from@{u u0}], [pi0_adj_iso@{u
 u0}], [Cat_Disc_Full@{u u0}], [Cat_Disc_Faithful@{u u0}] and
 [Components_Disc_Adjunction@{u u0 u1}] all carry [u0 < u] -- which is
 [Sets]' own -- together with bounds against [compose], [projections] and
 [ID], and nothing else.

 TWO BLOCKS ARE LITERALLY EMPTY, AND FOR ONCE THAT IS NOT A TRAP:
 [disc_setoid_iso@{u u0}] and [zigzag_setoid_contract@{u u0}] have
 [( * u u0 |= * )], and their BINDERS read [Setoid@{u u0}] with the
 carrier and relation levels DISTINCT, so reading the block alone
 happens to give the right answer here.  It is recorded because the
 opposite case is the usual one.

 THE RESTRICTION IS THEREFORE NOT IN THE BLOCKS, AND IT IS REAL:
 [Pi0] accepts only categories whose object, hom and proof universes
 COINCIDE.  §8 guards this with a five-command chain that
 attributes it precisely.  At [C : Category@{co ch ch}] with
 [ch < co] declared, three controls succeed -- [C : obj[Cat]],
 [pi0 C], and [pi0_fmap] at that C -- and two commands are
 rejected: [pi0_fmap_respects] and, with it, [fobj[Pi0] C], both
 reporting “Cannot enforce ch = co because ch < co”.  So the cause
 is neither [Cat], nor [pi0], nor the arrow action, but the single
 lemma [pi0_fmap_respects] (Theory/Connected/Components.v),
 which is declared over [Category@{u0 u0 u0}].

 THAT IDENTIFICATION IS MINIMIZATION AND NOT CONTENT, AND THE CLAIM
 IS GUARDED RATHER THAN ASSERTED.  §8's last section restates that
 lemma with its binders written out -- same statement, same
 one-line proof text -- inside a section declaring the two hom
 universes STRICTLY BELOW the object universe, and it is accepted
 there.  The repair belongs to the DONOR and is NOT performed here;
 the restatement is a probe, is marked as one, and nothing below
 uses it.  Note what the repair does NOT remove: it still carries
 [hc = hd], identifying the two categories' hom universes.

 Correspondingly, the control that the sibling module's §8 can
 offer -- its adjunction TYPE formable with the inner hom universe
 strictly below the inner object universe -- has NO analogue here,
 and that is stated rather than passed over: [Pi0] exposes two
 universe binders, the inner categories' levels are determined by
 them, and the [fobj[Pi0]] probe above says which categories that
 accepts.  A positive control at [Category@{cu cu cu}] shows the
 accepted class is inhabited and is not empty.

 One further identification is inherent rather than inherited and
 is named: the objects of [Sets@{o so}] are [SetoidObject@{o o}],
 carrier and relation at one level, so every category in the image
 of [Cat_Disc] has its objects and its homs at that same level.
 That is [Sets]' own declaration, not this file's.

 NO [Set] APPEARS IN ANY CONSTRAINT BLOCK OR BINDER OF THIS FILE
 -- but that is the result of a repair, not of luck, and the
 measurement that prompted it is worth carrying.  Written without
 binders, [roof_pt] elaborated at [Functor@{u Set Set u0 u1 u1}]
 and [disc_carrier_map] at [Functor@{u0 Set Set u0 Set Set}], both
 in the BINDER with Set-free blocks, and the pin propagated into
 the blocks of [Pi0_not_Faithful] ([Set < u], with [Pi0] itself
 instantiated at [Pi0@{u Set}]) and of
 [DiscreteCat_carrier_not_functorial].  All three donors are FREE
 -- [_1@{o h p}], [Roof@{u u0}] and [DiscreteCat@{o h p}] -- so the
 pin was MINIMIZATION at this file's own two unannotated
 definitions, of the family Construction/Free/Quiver/Examples.v
 records, and writing the binders out lifts it.  Refuting
 faithfulness at a Set-level instance would have sufficed to refute
 it outright, so the repair buys generality rather than
 correctness.

 V. AUDIT.  73 constants, ALL CLOSED UNDER THE GLOBAL CONTEXT
 ([Print Module] lists 73; the file declares no [Record], [Class]
 or [Inductive], so there is no unlisted [Build_*]; each was
 queried by fully qualified name, which is what reaches the 31
 [Program] obligations a [.glob] sweep cannot see -- 42 names are
 declared in the source and 42 + 31 = 73).  ZERO of the 73
 names collides anywhere in the tree -- a sweep that FOUND TEN, all
 of which were renamed away before this file landed, and two of
 which were live rather than cosmetic: Instance/Cat/Objects.v declare [Disc_Faithful] and [Disc_Full] as
 [#[export] Program Instance]s, so a [Print Assumptions Disc_Full]
 with both modules in one scope would have audited whichever was
 imported last.  The other eight were [disc_obj]
 (Functor/Construction/Postcompose.v), [disc_adj_iso],
 [disc_map], [adj_to_forgets], [adj_from_extends], [unit_is_id] and
 [BlurBool] (all Instance/Cat/Objects.v), and [counit_is_id]
 (Instance/Indiscrete.v).

 Six [Fail] probes of TWO KINDS kept lexically apart -- four
 CONVERSION in §4 and §7, reporting “cannot unify” with no universe
 clause, and two FORMABILITY in §8, reporting “universe
 inconsistency: Cannot enforce ch = co because ch < co” -- each
 stripped once and its kind read off the whole error message,
 beside an instrument check, six [Check] controls in §8, five
 [Example] controls beside the §4 negatives, and the two §2
 readbacks that control the §7 negative.
 Rename-simulated 5/5 on an unpadded denominator (the constants a
 NEGATIVE names: [pi0_adj_iso], [Cat_Disc], [DiscreteCat],
 [pi0_fmap_respects] and [Pi0]; the two file-local ones by the
 definition-site method, since a whole-file rename is a no-op),
 every one of them breaking the file at a non-[Fail] line.  That
 exercise FOUND a vacuous guard: [pi0_fmap_respects] was named only
 inside its own [Fail], so a rename of the donor would have turned
 that probe silently green; the control that closes it is the first
 command of §8's second section, and exists for that reason.

 The three section-local [Constraint] declarations were each tested
 by DELETION and they behave differently.  §8's first is
 LOAD-BEARING: without it [ch] unifies with [co] and both negatives
 succeed, so the file stops compiling.  §8's third pair is
 meaning-giving rather than load-bearing: the restated lemma
 elaborates without them, but then the levels could collapse and
 the command would demonstrate nothing.  Stated so that a later
 reader does not delete either as redundant.

 VI. WHAT IS NOT DELIVERED.

 No [Cat_Indisc] and no [Objects ⊣ Indiscrete] at this pair: the
 right-hand wing is the sibling development's, over its own two
 categories, and nothing here claims that wing exists.

 NO ADJOINT STRING.  The three adjunctions of Mac Lane's exercise
 are not exhibited as a chain, and by item II they cannot be at the
 constants this tree has; no comparison functor between [Cat] and
 [StrictCat], or between [Sets] and [Coq], is built or used.

 No [Coq]-valued π₀, and no impossibility proof for one.

 No uniqueness of the left or the right adjoint, no idempotency,
 no (co)monad induced by the adjunction, and nothing about
 preservation or creation of limits.

 No naturality of [pi0_counit_iso] in [A] beyond its being the counit
 of a built adjunction, and no comparison of [Cat_Disc] with
 Theory/Connected/Components.v's [ComponentSub] or
 [ConnectedComponent]: nothing here decomposes a category into its
 components.

 No invariance of π₀ under equivalence, which the donor's own
 NOT-delivered list already records as open, and no repair of
 [pi0_fmap_respects], whose universe identification is guarded in
 §8 and left to the donor.

 No functoriality of the construction in the AMBIENT category:
 neither [Pi0] nor [Cat_Disc] is related to any other category of
 categories, and no 2-categorical statement is attempted. 

 --------
 书籍：      Mac Lane，《Categories for the Working Mathematician》，  
 Springer GTM 5，第2版，第§IV.2节 练习9，第90页打印版  
 (maclane:IV.2:ex9)，该结果归因于 N. Smythe。  
 书籍：      Riehl，《Category Theory in Context》，Dover 2016，第§1.5节，  
 打印页35（连通范畴）以及第§4.1节  
 nLab：       https://ncatlab.org/nlab/show/connected+component  
 nLab：       https://ncatlab.org/nlab/show/discrete+category  
 nLab：       https://ncatlab.org/nlab/show/adjoint+string  
 nLab：       https://ncatlab.org/nlab/show/reflective+subcategory  
 nLab：       https://ncatlab.org/nlab/show/Cat  
 维基百科：   https://en.wikipedia.org/wiki/Adjoint_functors  

 Mac Lane 的练习要求给出由函子携带的伴随串，该函子将一个范畴映射到其对象集合：

 Components  ⊣  Discrete  ⊣  Objects  ⊣  Indiscrete该文件提供了最左端的附加操作，[Pi0 ⊣ Cat_Disc]，并且它提供的附加操作是在一个不同的类别对上，而不是其右边邻近文件所在的类别对。这是该文件的主要发现，§7 证明了其中可证明的一半；本标题的其余部分准确地说明了哪一半是可证明的。

 此处提供：

 (a) [Cat_Disc : Sets ⟶ Cat]，离散函子。这是树中该类型的第一个函子，并且声明是按类型而非按名称进行的：在任何 `.v` 文件中都未声明任何类型为 [Sets ⟶ Cat] 或 [Sets ⟶ StrictCat] 的常量，这两个标记的唯一出现是在文本中——Theory/Connected/Components.v 记录了其缺失，Instance/Indiscrete.v 的项目 II 通过名称预示了该文件。唯一的 [Cat ⟶ Sets] 是 [Pi0] 本身。(b)  [pi0_adj_iso]，同态集合同构，以及打包的记录 [Components_Disc_Adjunction : Pi0 ⊣ Cat_Disc]。

 (c)  [Cat_Disc_Full], [Cat_Disc_Faithful] 和 [pi0_counit_iso] —— 余单位是一个同构，这就是 Mac Lane 的“离散范畴的组成部分是它的对象”，并展示 [Sets] 作为带有反射器 π₀ 的 [Cat] 的反射子范畴。

 (d)  修正右伴随的反驳：[DiscreteCat_carrier_not_functorial]，其一般形式 [no_skeletal_carrier_functor_Sets_Cat] 和区分的 [Cat_Disc_not_skeletal]。

 (e)  关于 [Roof] 的非空性：[Pi0_not_Faithful] 和 [unit_not_Full]，因此 π₀ 真正丢弃了信息，伴随不是等价的。

 I. 三方面的先前技术修正，每方面都被衡量。首先，目录问题的工作项4要求定义连通分量函子。那是错误的。Theory/Connected/Components.v 声明了 [Pi0 : Cat ⟶ Sets]，具有 [fobj := pi0] 和 [fmap := pi0_fmap]，并证明了它的三个函子法则。它在这里被使用，而没有任何东西重新构建它：名字 [pi0]、[pi0_fmap]、[ZigZag]、[hom_zigzag] 和 [zigzag_fmap] 的使用方式完全与该文件和 Structure/Groupoid/Connected.v 声明的方式相同，并且此文件没有声明自己的之字形机制。缺失的是伴随关系，这种缺失在提供者自己的未交付清单中有记录，在 Theory/Connected/Components.v: “没有左伴随。”[Pi0 : Cat ⟶ Sets] 已经构建，但离散函子 [Sets ⟶ Cat] 和伴随 π₀ ⊣ 离散尚未构建。这个待定的延迟就是这个文件要处理的。

 其次，集合同构上的离散范畴已经存在：Construction/Comma/Special.v 中的 [DiscreteSetoidCat] 已经构建，以便可以识别两个常量函子的逗号。它在这里被使用，并且在其自身文件之外首次被使用（衡量：在此提交之前，标记 [DiscreteSetoidCat] 只出现在一个 `.v` 文件中）。缺失的是其箭头作用和基于它构建的任何函子；两者在这里都是新的，并且箭头作用只有三行，因为 [DiscreteSetoidCat S] 的态射就是 [≈] 的证明，而 [proper_morphism] 就是其上所需的作用。第三，适用于兄弟模块记录的相同修正：
 Instance/Discrete/Reconstruct.v 的 [Indiscrete] 存在。它
 在下面没有任何作用——Mac Lane 字符串的不连续部分是
 另一翼——这里只是为了命名，以免此头文件
 看起来与兄弟模块的相矛盾。

 二、字符串分裂，并且分裂不是命名上的意外。Instance/Cat/Objects.v 解决了 [StrictCat] 和 [Coq] 上的中间伴随关系，并且它的两个解决方案都是通过反驳强制的：不存在从 [Cat] 到一个莱布尼茨比较目标的对象函子（其 §6，ZW44WZZ 的交换自函子为 [≈] 到 [Cat] 的恒等函数，而它们的对象映射不同），并且不存在基于承载的对象映射 [Sets → StrictCat] 能满足 [≈]（其 §7）。因此，它的离散函子为 [StrictCat_Disc : Coq ⟶ StrictCat]，建立在 Instance/Discrete.v 的 [DiscreteCat] 上。[Pi0] 与那个没有任何端点重合：它的源是 [Cat] ，目标是 [Sets] 。所以 [Pi0 ⊣ Cat_Disc] 是关于另一对范畴的陈述，而 Mac Lane 的四个伴随函子在这个库中并不形成一个连续的串 —— 它们存在为两个两两组成的串，彼此不相遇。Instance/Indiscrete.v 的 [adjoint_string] 封装了另一组，也正因为这个原因只封装了两个组件；三个标题一致，每个都这么说明。（该文件是通过名称引用而非行号：它与这个文件一起到达，其行号仍在变化。）这里被证明而不是观察到的是更尖锐的一半：即使在移到 [Cat] 和 [Sets] 之后，右伴随不能是普通的离散范畴。[DiscreteCat_carrier_not_functorial] (§7) 否定了唯一候选者的 [fmap_respects] 域，展示了 [bool] 在到处成立的集合同类下，其中 [id ≈ negb] 在 [Sets] 中成立，而诱导函子之间的自然同构将导致 [true = false]。因此，字符串的两个 [Discrete] 是不同范畴上的不同函子，而不是同一个函子被描述两次。确切地主张这一点。被反驳的是基于载体的离散对象图。这儿没有任何东西证明不存在 [Coq] 值的 π₀，也没有证明两个分支不能通过此处未尝试的某种构造得到调和；兄弟模块从其方面否定同样的事情。一般形式 [no_skeletal_carrier_functor_Sets_Cat] 表明了障碍是什么：一个 π₀ 的右伴随，其对象是 CARRIER，不可能具有 SKELETAL 纤维。[Cat_Disc] 避开了它，并且正是通过那一条款避开的——[Cat_Disc_not_skeletal] 证明了骨架性假设是它所失败的那一点，而 [cat_disc_Kobj] 和 [cat_disc_Kinj] 解决了另外两点（第一点在 [eq_refl]，第二点通过恒等函数）。所以反驳并非空洞，而是被定位的躲避，而不是假定的。此文件不需要 Instance/Cat/Objects.v，其原因是经过衡量的，而非风格上的：导入它会将 54 个模块的闭包增加 24 个模块（其中包括 Instance/Coq.v、Theory/Monad.v 以及八个 Structure/Monoidal 模块），而且没有任何好处，因为这两个开发没有共同的范畴。因此，它的反例在上文中被引用，而不是重新推导，这些引用已被标注为引用。命名。[Objects]、[Discrete] 和 [Indiscrete] 都已被使用——分别被 Solver/Expr.v 的重ification 类、Structure/Discrete.v 的谓词以及 Instance/Discrete/Reconstruct.v 的类别使用——因此兄弟模块采用了 Instance/Top/Forgetful.v 的惯例，即以结构化类别作为前缀。此文件也遵循该惯例：[Cat_Disc] 用于进入 [Cat] 的函子，如果以后在该对中需要非离散的一半，则保留 [Cat_Indisc]。[Cat_Disc]、[Cat_Disc_map]、[disc_setoid_iso]、[zigzag_setoid_contract]、[pi0_to]、[pi0_from]、[pi0_adj_iso] 和 [Components_Disc_Adjunction] 每个都首先被验证在整个树中出现次数为零。

 III. 优势，先严格测量。十个回读保持在 [eq_refl]，并作为 [Example] 发出：[Cat_Disc] 的对象动作、其对象类型和同构类型（[cat_disc_obj]、[cat_disc_obj_carrier]、[cat_disc_hom]），箭头动作的对象动作（[cat_disc_fmap]）；换位的两个部分（[pi0_adj_to_at]、[pi0_adj_from_at]）；单元是鼻子上的恒等函数（[pi0_unit_is_id]），伴随也一样（[pi0_counit_is_id]）；以及 [pi0_counit_iso] 的两个部分。下面还有四个额外的 [eq_refl]，作为控制定位两个被否定的往返和第7条的 [Kobj] 条款——[:= eq_refl] 共出现十八次，其中四次位于 [Fail] 内，是否定而非回读。

 两个往返都不是严格的，而且两个失败的原因不同，每个失败通过一个控制定位。在 [Sets] 方面，残差是一个证书。
 [pi0_rt_from_to_strict] 在 [eq_refl] 被驳斥，而
 [pi0_rt_from_to_at]（每个点的值）和 [pi0_rt_from_to_fn]
 （整个 [morphism] 域）都完全保持不变。[SetoidMorphism] 是
 一个 [Record]，根据 [Set Primitive Projections]（Lib/Setoid.v, Instance/Sets.v），因此它有 eta 和记录相等是字段相等：因此不同的正是 [proper_morphism]，[pi0_from] 从 [zigzag_setoid_contract] 重建它。在 [Cat] 方面，残留的是证明相关数据，这是两者中更尖锐的一个。[pi0_rt_to_from_strict] 已被反驳，OBJECT 操作正好返回（[pi0_rt_to_from_obj]），而 ARROW 操作则没有（[pi0_rt_to_from_map]，也被反驳）。原因是结构性的而非偶然的：[DiscreteSetoidCat S] 的一个态射就是 [≈] 的一个证明，并且一个 [≈] 的两个证明不必是 Leibniz 等价的，所以通过该范畴的往返不能恢复一个证明项。而取代它的 [≈] 是空洞的，这值得一提，而不是掩饰。[DiscreteSetoidCat] 的同态集识别所有平行箭头（[cat_disc_hom_trivial]，证明 [I]），所以 [pi0_rt_to_from_map_equiv] 就是 [I]，并且适用于任何两条平行箭头——它对来回验证没有任何内容。因此，[iso_from_to] 对 [pi0_adj_iso] 的全部内容是对象族，也就是 [eq_refl]。相同的观察也解释了为什么伴随如此廉价：[Cat] 中 [≈] 的自然性条件在一个薄目标上是 [True]。附接记录总共需要两个义务，并且两者都在 [pi0_adj_iso] 的两个 [Proper] 字段中；同构的两次往返以及 [Build_Adjunction'] 要求的两个自然性条款都通过环境义务策略得到满足。[Build_Adjunction']（Theory/Adjunction.v）被使用，而不是 [Build_Adjunction]，以实现与兄弟模块记录相同的精简：它只要求两个 [to] 方的条款。没有类似于 Instance/Top/Forgetful.v 墙出现。那个文件的 [Discrete ⊣ Forget ⊣ Indiscrete] 对 [Top] 是被强制进入换位同构的，因为 [Top] 的 hom 严格位于它的点之上，所以没有单个 [Sets] 可以同时服务于两个方向。在这里两个函子都在一个 [Cat] 和一个 [Sets] 之间运行，并且打包记录已经建立。确实存在宇宙限制，但它是不同的，并且属于供体的；见下一项。

 IV. 宇宙，同时测量块和绑定器。正好有 73 个约束块中的一个包含一个宇宙方程，
 它是第 §8 节第三部分的探测，其 [hc = hd] 在三段之后被披露。每个其他块的每个条目都是 [<] 或 [<=]；这是按常数逐个检查的，而不是通过抽样。[Cat_Disc@{u u0}]、[pi0_to@{u u0}]、[pi0_from@{u u0}]、[pi0_adj_iso@{uu0}]、[Cat_Disc_Full@{u u0}]、[Cat_Disc_Faithful@{u u0}] 和 [Components_Disc_Adjunction@{u u0 u1}] 都携带 [u0 < u]——这是 [Sets] 本身的——同时具有针对 [compose]、[projections] 和 [ID] 的界限，而没有其他内容。两个区块实际上是空的，这一次这不是陷阱：
 [disc_setoid_iso@{u u0}] 和 [zigzag_setoid_contract@{u u0}] 拥有
 [( * u u0 |= * )]，并且它们的绑定器显示 [Setoid@{u u0}]，载体和关系层级是不同的，所以单独读取这个区块恰好给出了正确的答案。它被记录下来是因为相反的情况才是常见的。因此，限制不在这些块中，而且它是真实的：
 [Pi0] 仅接受其对象、同构和证明宇宙一致的类别。§8 用一个五条命令的链条来确保这一点，并精确地归属它。在 [C : Category@{co ch ch}] 与 [ch < co] 声明时，三个控制成功——[C : obj[Cat]、[pi0 C] 和 [pi0_fmap] 在该 C 上——而两个命令被拒绝：[pi0_fmap_respects] 和随之的 [fobj[Pi0] C]，两者都报告“无法强制 ch = co，因为 ch < co”。因此，原因既不在 [Cat]，也不在 [pi0]，也不在箭头动作，而在于单一的引理 [pi0_fmap_respects]（Theory/Connected/Components.v），它是在 [Category@{u0 u0 u0}] 上声明的。该标识是最小化而非内容，并且该主张是受保护的而非被断言的。第8节的最后一部分用完整的绑定器重述了该引理——同样的陈述，同样的一行证明文本——在一个声明两个同态宇宙严格低于对象宇宙的部分中，并且在那里被接受。修复属于提供者，并未在此执行；重述是一个探测，被标记为探测，并且下面没有任何内容使用它。请注意修复未移除的内容：它仍然携带 [hc = hd]，标识两个范畴的同态宇宙。相应地，同胞模块 §8 所能提供的控制 —— 即其可以与内部同态宇宙形成的附加类型，但严格位于内部对象宇宙之下 —— 在这里没有类似物，而且这是明确说明的，而不是略过：[Pi0] 暴露了两个宇宙绑定器，内部范畴的层级由它们决定，而上文 [fobj[Pi0] 探针指出接受哪些范畴。[Category@{cu cu cu}] 的正向控制显示所接受的类是有元素的，并且非空。另一个鉴别是固有的而非继承的，并被命名为：[Sets@{o so}] 的对象是 [SetoidObject@{o o}]，在同一级别上为载体和关系，因此 [Cat_Disc] 映像中的每个类别在同一级别上都有其对象和同态。这是 [Sets] 自己的声明，而不是此文件的。在此文件的任何约束块或绑定器中都没有出现 [Set]
 -- 但这是修复的结果，而不是运气，而且促使它发生的测量值得保留。未使用绑定器时，[roof_pt] 在 [Functor@{u Set Set u0 u1 u1}] 处被详细说明，[disc_carrier_map] 在 [Functor@{u0 Set Set u0 Set Set}] 处被详细说明，二者都在带有自由块的绑定器中，并且销钉传播到 [Pi0_not_Faithful]（[Set < u]，其中 [Pi0] 本身在 [Pi0@{u Set}] 处实例化）和 [DiscreteCat_carrier_not_functorial] 的块中。三位捐赠者都是自由的 -- [_1@{o h p}]、[Roof@{u u0}] 和 [DiscreteCat@{o h p}] -- 因此销钉在此文件的两个未注释定义中是最小化的，属于 Construction/Free/Quiver/Examples.v 系列记录，将绑定器写出会提高它。反驳在集合层实例上的忠实性本来就足以彻底反驳它，因此这个修正带来的是普遍性而不是正确性。V. 审计。73 个常量，全部在全局上下文中封闭
 （[Print Module] 列出了 73 个；文件未声明 [Record]、[Class] 或 [Inductive]，因此没有未列出的 [Build_*]；每个都是通过完全限定名查询的，这就是为什么 31 个 [Program] 义务是 [.glob] 扫描无法看到的——源代码中声明了 42 个名称，而 42 + 31 = 73）。73 个名称中没有一个在树的任何地方发生冲突——一次扫描发现了十个，其中所有名称在此文件落地前都已重命名，其中两个是实际存在而非装饰性的：Instance/Cat/Objects.v 声明了 [Disc_Faithful] 和 [Disc_Full] 作为 [#[export] 程序实例，因此在一个作用域中同时存在这两个模块的 [Print Assumptions Disc_Full] 将会审计最后导入的那个模块。其他八个是 [disc_obj]（Functor/Construction/Postcompose.v）、[disc_adj_iso]、[disc_map]、[adj_to_forgets]、[adj_from_extends]、[unit_is_id] 和 [BlurBool]（都在 Instance/Cat/Objects.v），以及 [counit_is_id]（Instance/Indiscrete.v）。六个 [Fail] 探针分为两类保持词汇上的区分——四个 CONVERSION 位于 §4 和 §7，报告“无法统一”，没有 universe 条款；两个 FORMABILITY 位于 §8，报告“universe 不一致：无法强制 ch = co 因为 ch < co”——每个探针剥离一次，并从整个错误信息中读取其类型，旁边是仪器检查，六个 [Check] 控件位于 §8，五个 [Example] 控件位于 §4 否定旁边，以及控制 §7 否定的两个 §2 回读。在未填充的分母上模拟重命名 5/5（常量 a  
 负面名称：[pi0_adj_iso]、[Cat_Disc]、[DiscreteCat]、  
 [pi0_fmap_respects] 和 [Pi0]；根据定义位置方法对两个文件本地的名字进行重命名，因为整个文件的重命名是无操作的），  
 每一个都在非 [Fail] 的行上破坏了文件。这个练习发现了一个空洞的保护：[pi0_fmap_respects] 仅在其自己的 [Fail] 中命名，因此捐赠者的重命名会悄悄地将该探测变为绿色；关闭它的控制是 §8 第二部分的第一条命令，并且存在的原因正是如此。三个部分局部 [Constraint] 声明各自通过删除进行了测试，它们的行为各不相同。§8 的第一个是承重的：没有它，[ch] 会与 [co] 合并，并且两个否定都成功，所以文件会停止编译。§8 的第三对是赋予意义的，而不是承重的：重新陈述的引理即使没有它们也能详细说明，但随后层次可能会崩溃，且命令将无法展示任何内容。如此说明，以便后来的读者不会将任一声明视为多余而删除。

 VI. 未交付的内容。

 在这一对中没有 [Cat_Indisc]，也没有 [Objects ⊣ Indiscrete]：右侧翼属于兄弟开发的部分，涉及其自身的两个类别，这里没有任何内容声称该翼存在。没有伴随串。Mac Lane 练习的三个伴随关系并没有作为一个链条展示，并且根据条目 II，它们不能出现在该树的常量中；在 [Cat] 与 [StrictCat] 之间，或 [Sets] 与 [Coq] 之间，没有建立或使用任何比较函子。

 没有 [Coq] 值的 π₀，也没有关于它的不可能性证明。

 没有左伴随或右伴随的唯一性，没有幂等性，没有由伴随诱导的 (co)monad，也没有关于极限的保持或创造的内容。

 除了作为已建立伴随的余单元之外，[pi0_counit_iso] 在 [A] 中没有自然性，也没有将 [Cat_Disc] 与 Theory/Connected/Components.v 中的 [ComponentSub] 或 [ConnectedComponent] 进行比较：这里没有任何内容将一个范畴分解为其组成部分。π₀ 在等价下没有不变性，捐赠者自己尚未完成的列表已经将其记录为未完成，并且 [pi0_fmap_respects] 也没有被修复，其宇宙标识在第8节中有所说明，并交由捐赠者处理。

 在 AMBIENT 范畴中构造没有函子性：[Pi0] 和 [Cat_Disc] 都没有与任何其他范畴的范畴相关联，也未尝试任何二范畴的陈述。
*)

(* * ** §1. The discrete category on a setoid: two small lemmas / * ** §1. 集合等价类上的离散范畴：两个小引理 *)

(*
 An [≈] between two points of [DiscreteSetoidCat S] IS an arrow between
 them, so it is half of an isomorphism and symmetry supplies the other
 half.  Both inverse laws are equations in a thin category and are
 discharged by the ambient obligation tactic.  It is used three times
 below -- at the two [fmap_respects]-shaped obligations of §2 and §3,
 and again in §7's [Cat_Disc_not_skeletal] -- which is why it is
 factored out. 

 --------
 在两个 [DiscreteSetoidCat S] 点之间的 [≈] 是一个在它们之间的箭头，所以它是一种同构的一半，对称性提供了另一半。两个逆律都是薄范畴中的方程，并且由环境义务策略解决。它在下面使用了三次——在第2节和第3节的两个 [fmap_respects] 形义务上，以及在第7节的 [Cat_Disc_not_skeletal] 上——这就是为什么它被提取出来的原因。
*)
Program Definition disc_setoid_iso {A : Type} (S : Setoid A) {x y : A}
  (e : @equiv A S x y) : @Isomorphism (DiscreteSetoidCat S) x y :=
  {| to := e ; from := symmetry e |}.

(*
 The converse collapse: a zig-zag in [DiscreteSetoidCat S] contracts to
 a single [≈].  This is the only induction in the file, and it is the
 whole reason the backward transpose exists -- the [Sets]-morphism it
 produces must respect [ZigZag], and this is what turns a chain into
 the [≈] the target setoid wants.  Each of the three cases is one law
 of [S]: reflexivity, transitivity, and transitivity after symmetry. 

 --------
 相反的塌缩：[DiscreteSetoidCat S] 中的之字形收缩成一个单一的 [≈]。这是文件中唯一的归纳，也是后向换位存在的全部原因——它产生的 [Sets]-同态必须符合 [ZigZag]，而这就是将一个链转变为目标集合所需的 [≈] 的方式。三个情况中的每一个都是 [S] 的一个定律：自反性、传递性，以及对称性后的传递性。
*)
Lemma zigzag_setoid_contract {A : Type} (S : Setoid A)
  (x y : DiscreteSetoidCat S) : ZigZag x y → @equiv A S x y.
Proof.
  intro s; induction s.
  - reflexivity.
  - now transitivity y.
  - now transitivity y; [ symmetry |].
Qed.

(* * ** §2. The discrete functor Sets ⟶ Cat / * ** §2. 离散函子 Sets ⟶ Cat *)

(*
 The arrow action.  Both the object and the arrow part are READ OFF a
 [Sets]-morphism: [fobj] is its underlying function and [fmap] is its
 [proper_morphism] certificate, since an arrow of the discrete category
 on a setoid is a proof of [≈].  All three functor laws are equations
 in a thin category and cost nothing. 

 --------
 箭头动作。对象和箭头部分都是从 [Sets]-同态中读取的：[fobj] 是其底层函数，[fmap] 是其 [proper_morphism] 证书，因为集合同构上的离散范畴的箭头是 [≈] 的证明。所有三个函子定律在稀疏范畴中都是方程，不需要任何代价。
*)
Program Definition Cat_Disc_map {A B : Sets} (f : A ~> B) :
  DiscreteSetoidCat (is_setoid A) ⟶ DiscreteSetoidCat (is_setoid B) :=
  {| fobj := f
   ; fmap := fun x y (e : x ≈ y) => proper_morphism f x y e |}.

(*
 The functor.  Its ONE obligation is [fmap_respects]: two pointwise
 [≈]-equal [Sets]-morphisms induce naturally isomorphic functors, the
 component at [a] being [disc_setoid_iso] of the hypothesis at [a] and the
 naturality clause being [True].  [fmap_id] and [fmap_comp] are
 discharged by the ambient tactic for the same reason. 

 --------
 函子。它的唯一义务是：[fmap_respects]：两个逐点的[≈]-相等的[Sets]-态射自然地引出同构的函子，其中在[a]处的分量是[disc_setoid_iso]在[a]处假设，且自然性条款为[True]。[fmap_id]和[fmap_comp]因相同原因已被环境策略解决。
*)
Program Definition Cat_Disc : Sets ⟶ Cat := {|
  fobj := fun A => DiscreteSetoidCat (is_setoid A)
; fmap := fun _ _ f => Cat_Disc_map f
|}.
Next Obligation.
  intros f g H.
  exists (fun a => disc_setoid_iso (is_setoid y) (H a)); intros; exact I.
Defined.

(*
 Four readbacks, all [eq_refl].  The second and third are the ones a
 consumer needs: the objects of the discrete category ARE the carrier
 and its homs ARE the setoid's own relation. 

 --------
 四次回读，都是 [eq_refl]。第二次和第三次是消费者需要的：离散范畴的对象是载体，其态射是集合等价的自身关系。
*)
Example cat_disc_obj (A : Sets) :
  fobj[Cat_Disc] A = DiscreteSetoidCat (is_setoid A) := eq_refl.

Example cat_disc_obj_carrier (A : Sets) :
  obj[fobj[Cat_Disc] A] = carrier A := eq_refl.

Example cat_disc_hom (A : Sets) (x y : carrier A) :
  (x ~{fobj[Cat_Disc] A}~> y) = (x ≈ y) := eq_refl.

Example cat_disc_fmap (A B : Sets) (f : A ~> B) (a : carrier A) :
  fobj[fmap[Cat_Disc] f] a = f a := eq_refl.

(** ** §3. The transposition / ** §3. 转位 *)

(*
 Forward: a map on components extends to a functor.  Its object action
 IS the given map -- [carrier (pi0 C)] is [obj[C]] by
 Theory/Connected/Components.v's [pi0_carrier] -- and its arrow action
 is the map's own respectfulness certificate applied to the one-step
 chain [hom_zigzag f].  So no data is invented in this direction; the
 two ingredients are already present in the argument. 

 --------
 前言：一个关于分量的映射扩展为一个函子。它的对象作用就是给定的映射 —— [carrier (pi0 C)] 是 [obj[C] ] 由 Theory/Connected/Components.v 的 [pi0_carrier] —— 而箭头作用是映射自身的守恒性证明应用于一步链 [hom_zigzag f]。因此在这个方向上没有数据被创造；这两个成分已经在论证中存在。
*)
Program Definition pi0_to {C : Cat} {A : Sets}
  (h : fobj[Pi0] C ~{Sets}~> A) : C ~{Cat}~> fobj[Cat_Disc] A :=
  {| fobj := h
   ; fmap := fun x y (f : x ~> y) =>
       @proper_morphism _ _ _ _ h x y (hom_zigzag f) |}.

(*
 Backward: a functor into a discrete category restricts to a map on
 components.  Its underlying function is the functor's object action;
 the content is the ONE obligation, which is where [zigzag_fmap] and
 [zigzag_setoid_contract] are spent -- transport the chain along the functor,
 then contract it in the thin target. 

 --------
 向后：一个函子到离散范畴会限制为对分量的映射。它的底层函数是该函子的对象作用；内容是唯一的义务，这就是 [zigzag_fmap] 和 [zigzag_setoid_contract] 被使用的地方——沿着函子传送链条，然后在薄的目标中收缩它。
*)
Program Definition pi0_from {C : Cat} {A : Sets}
  (F : C ~{Cat}~> fobj[Cat_Disc] A) : fobj[Pi0] C ~{Sets}~> A :=
  {| morphism := fobj[F] |}.
Next Obligation.
  intros x y s.
  exact (zigzag_setoid_contract (is_setoid A) _ _ (zigzag_fmap F s)).
Defined.

(*
 The hom-setoid isomorphism.  Two obligations, both [Proper] fields;
 the two round trips are discharged by the ambient tactic, and §4
 records that the second of them is vacuous on arrows. 

 --------
 同态集合等价。两个义务，都是 [Proper] 域；两个往返由环境策略完成，第4节记录它们中的第二个在箭头上是空的。
*)
Program Definition pi0_adj_iso (C : Cat) (A : Sets) :
  @Isomorphism Sets
    {| carrier := @hom Sets (fobj[Pi0] C) A
     ; is_setoid := @homset Sets (fobj[Pi0] C) A |}
    {| carrier := @hom Cat C (fobj[Cat_Disc] A)
     ; is_setoid := @homset Cat C (fobj[Cat_Disc] A) |} :=
  {| to   := {| morphism := fun h => @pi0_to C A h |}
   ; from := {| morphism := fun F => @pi0_from C A F |} |}.
Next Obligation.
  intros h k H.
  exists (fun a => disc_setoid_iso (is_setoid A) (H a)); intros; exact I.
Defined.
Next Obligation. intros F G H a; exact (to (`1 H a)). Defined.

(** ** §4. The adjunction / ** §4. 附加 *)

(*
 Mac Lane's leftmost adjunction, packaged.  ZERO obligations: the two
 naturality clauses [Build_Adjunction'] asks for land in [Cat] at a
 thin target, where [≈] between functors is a family of isomorphisms
 together with a [True], and the object families agree definitionally. 

 --------
 麦克·莱恩的最左边的伴随，打包。零义务：两个自然性条款 [Build_Adjunction'] 要求在 [Cat] 的薄目标上着陆，其中 [≈] 是函子之间的一族同构以及一个 [True]，并且对象族在定义上是一致的。
*)
Program Definition Components_Disc_Adjunction : Pi0 ⊣ Cat_Disc :=
  Build_Adjunction' pi0_adj_iso _ _.

Example pi0_adj_to_at (C : Cat) (A : Sets)
  (h : fobj[Pi0] C ~{Sets}~> A) (x : C) :
  fobj[to (pi0_adj_iso C A) h] x = h x := eq_refl.

Example pi0_adj_from_at (C : Cat) (A : Sets)
  (F : C ~{Cat}~> fobj[Cat_Disc] A) (x : C) :
  from (pi0_adj_iso C A) F x = F x := eq_refl.

(*
 The unit and the counit are both the identity function -- on the nose.
 The unit is [C ⟶ Cat_Disc (Pi0 C)], the projection of an object to its
 component, and the carrier of [pi0 C] IS [obj[C]], so there is nothing
 for it to do on objects. 

 --------
 单位与余单位本身都是恒等函数——严格如此。
 单位是 [C ⟶ Cat_Disc (Pi0 C)]，将一个对象投影到其分量上，而 [pi0 C] 的载体是 [obj[C]，所以它在对象上没有什么可做的。
*)
Example pi0_unit_is_id (C : Cat) (x : C) :
  fobj[@unit _ _ _ _ Components_Disc_Adjunction C] x = x := eq_refl.

Example pi0_counit_is_id (A : Sets) (a : carrier A) :
  @counit _ _ _ _ Components_Disc_Adjunction A a = a := eq_refl.

(*
 NEGATIVE 1 (CONVERSION).  The [Sets]-side round trip is not strict.
 Two controls localize the failure to a single field: the value at each
 point returns on the nose, and so does the whole [morphism] FIELD, so
 -- [SetoidMorphism] being a primitive-projection record with eta --
 what differs is exactly [proper_morphism], which [pi0_from] rebuilds. 

 --------
 负面 1（转换）。[Sets] 侧的往返不是严格的。两个控制将失败定位到单个字段：每个点的值准确返回，整个 [morphism] 字段也是如此，因此——[SetoidMorphism] 是一个带有 eta 的原始投影记录——不同的正是 [proper_morphism]，[pi0_from] 重建它。
*)
Fail Example pi0_rt_from_to_strict (C : Cat) (A : Sets)
  (h : fobj[Pi0] C ~{Sets}~> A) :
  from (pi0_adj_iso C A) (to (pi0_adj_iso C A) h) = h := eq_refl.

Example pi0_rt_from_to_at (C : Cat) (A : Sets)
  (h : fobj[Pi0] C ~{Sets}~> A) (x : carrier (fobj[Pi0] C)) :
  from (pi0_adj_iso C A) (to (pi0_adj_iso C A) h) x = h x := eq_refl.

Example pi0_rt_from_to_fn (C : Cat) (A : Sets)
  (h : fobj[Pi0] C ~{Sets}~> A) :
  @morphism _ _ _ _ (from (pi0_adj_iso C A) (to (pi0_adj_iso C A) h))
    = @morphism _ _ _ _ h := eq_refl.

(*
 NEGATIVE 2 and NEGATIVE 3 (CONVERSION).  The [Cat]-side round trip is
 not strict either, and the cause is DIFFERENT: the object action does
 return on the nose (control), the ARROW action does not, and it cannot,
 because an arrow of [DiscreteSetoidCat S] is a PROOF of [≈] and the
 round trip manufactures a fresh one through [zigzag_setoid_contract]. 

 --------
 负数2和负数3（转换）。[Cat]侧的往返也不是严格的，原因不同：对象动作确实会准确返回（控制），箭头动作不会，也不能返回，因为[DiscreteSetoidCat S]的箭头是[≈]的证明，而往返通过[zigzag_setoid_contract]制造了一个新的证明。
*)
Fail Example pi0_rt_to_from_strict (C : Cat) (A : Sets)
  (F : C ~{Cat}~> fobj[Cat_Disc] A) :
  to (pi0_adj_iso C A) (from (pi0_adj_iso C A) F) = F := eq_refl.

Example pi0_rt_to_from_obj (C : Cat) (A : Sets)
  (F : C ~{Cat}~> fobj[Cat_Disc] A) :
  fobj[to (pi0_adj_iso C A) (from (pi0_adj_iso C A) F)] = fobj[F]
  := eq_refl.

Fail Example pi0_rt_to_from_map (C : Cat) (A : Sets)
  (F : C ~{Cat}~> fobj[Cat_Disc] A) (x y : C) (f : x ~> y) :
  fmap[to (pi0_adj_iso C A) (from (pi0_adj_iso C A) F)] f = fmap[F] f
  := eq_refl.

(*
 ... and the [≈] that replaces it is VACUOUS, which the next two
 commands say together rather than separately: the first holds, and the
 second shows it holds of ANY two parallel arrows, so it verifies
 nothing about the round trip.  The content of [iso_from_to] here is
 the object family, which is [pi0_rt_to_from_obj]. 

 --------
 ... 并且取代它的 [≈] 是空的，接下来的两个命令是一起说明而不是分开说明的：第一个成立，第二个显示它对任意两条平行箭头都成立，因此它并不能验证关于往返的任何内容。这里 [iso_from_to] 的内容是对象族，即 [pi0_rt_to_from_obj] 。
*)
Example pi0_rt_to_from_map_equiv (C : Cat) (A : Sets)
  (F : C ~{Cat}~> fobj[Cat_Disc] A) (x y : C) (f : x ~> y) :
  fmap[to (pi0_adj_iso C A) (from (pi0_adj_iso C A) F)] f ≈ fmap[F] f
  := I.

Example cat_disc_hom_trivial (A : Sets) (x y : carrier A)
  (p q : x ~{fobj[Cat_Disc] A}~> y) : p ≈ q := I.

(* * ** §5. Cat_Disc is fully faithful; Sets is reflective in Cat / * ** §5. Cat_Disc 是完全忠实的；Sets 在 Cat 中是反射性的 *)

(*
 [Full] asks only for a section of [fmap] with no functoriality, and
 here the section is the reverse reading of §2: the underlying function
 of the recovered [Sets]-morphism is the functor's object action and
 its certificate is the functor's arrow action.  Its ONE obligation is
 that certificate, supplied by a one-step script rather than as a field
 for the reason Theory/Connected/Components.v records at
 [sets_quot_proj] -- [Proper (equiv ==> equiv) fobj[F]] is CONVERTIBLE
 with the type of [fmap[F]], but the elaborator does not unfold
 [Proper] and [respectful] during unification, so the field assignment
 is rejected.  (Measured here too, at exactly that spot.)  [fmap_sur]
 is discharged by the ambient tactic. 

 --------
 [Full] 只要求 [fmap] 的一个没有函子性的截面，这里的截面是 §2 的逆向阅读：恢复的 [Sets] -态射的底层函数是函子的对象作用，其证书是函子的箭头作用。它的唯一义务就是那个证书，由一步脚本提供，而不是作为一个字段，原因如 Theory/Connected/Components.v 在 [sets_quot_proj] -- [Proper (equiv ==> equiv) fobj[F] ] 记录的那样，是可转换的与 [fmap[F] ] 的类型，但在统一过程中，展开器不会展开 [Proper] 和 [respectful]，所以字段赋值被拒绝。（这里也在完全相同的位置测量。）[fmap_sur] 由环境策略完成。
*)
Program Definition Cat_Disc_Full : Full Cat_Disc := {|
  prefmap := fun A B F => {| morphism := fobj[F] |}
|}.
Next Obligation. intros x y e; exact (fmap[F] e). Defined.

Definition Cat_Disc_Faithful : Faithful Cat_Disc.
Proof.
  unshelve econstructor.
  intros A B f g H a; exact (to (`1 H a)).
Defined.

(*
 Mac Lane's “the components of a discrete category are its objects”,
 in the form that carries the most: the COUNIT is an isomorphism.  With
 [Cat_Disc_Full] and [Cat_Disc_Faithful] this exhibits [Sets] as a reflective
 subcategory of [Cat] with reflector π₀ -- the inclusion is the right
 adjoint and is fully faithful.

 Both legs are the identity function; the two obligations are the
 respectfulness of the backward leg (an [≈] IS an arrow, hence a
 one-step chain) and the [ZigZag x x] the second round trip asks for,
 which is the empty chain. 

 --------
 麦克莱恩的“离散范畴的组成部分是它的对象”，以承载最多信息的形式：余单元是一个同构。通过 [Cat_Disc_Full] 和 [Cat_Disc_Faithful]，这展示了 [Sets] 作为 [Cat] 的反射子范畴，其反射子是 π₀——包含函子是右伴随并且完全忠实。

 两条边都是恒等函数；两个义务是后向边的尊重性（一个 [≈] 是一条箭头，因此是一条一步链）和 [ZigZag x x] 第二次往返所要求的，这是一条空链。
*)
Program Definition pi0_counit_iso (A : Sets) :
  @Isomorphism Sets (fobj[Pi0] (fobj[Cat_Disc] A)) A :=
  {| to   := @counit _ _ _ _ Components_Disc_Adjunction A
   ; from := {| morphism := fun a : carrier A => a |} |}.
Next Obligation.
  intros x y e.
  exact (@hom_zigzag (DiscreteSetoidCat (is_setoid A)) x y e).
Defined.
Next Obligation. exact (zz_nil _). Defined.

Example pi0_counit_iso_to (A : Sets) (a : carrier A) :
  to (pi0_counit_iso A) a = a := eq_refl.

Example pi0_counit_iso_from (A : Sets) (a : carrier A) :
  from (pi0_counit_iso A) a = a := eq_refl.

(* * ** §6. Non-vacuity: π₀ genuinely forgets / * ** §6. 非空性：π₀ 真正地遗忘 *)

(*
 The constant functors out of the terminal category.  [Roof] is the
 walking span [RNeg ← RZero → RPos]: it is CONNECTED
 ([Roof_Connected], Structure/Groupoid/Connected.v), so π₀ merges
 its three objects, while [RoofHom RNeg RPos] is EMPTY
 ([RNeg_RPos_absurd], Instance/Roof.v), so [Roof] itself does not.
 That gap is what both refutations below exploit. 

 --------
 从终端范畴出的恒等函子。[Roof] 是行走的跨度 [RNeg ← RZero → RPos]：它是连通的 ([Roof_Connected]，Structure/Groupoid/Connected.v)，因此 π₀ 会合并它的三个对象，而 [RoofHom RNeg RPos] 是空的 ([RNeg_RPos_absurd]，Instance/Roof.v)，所以 [Roof] 本身则不会。这个差距就是下面两个反驳所利用的。
*)
Program Definition roof_pt@{o h p ru rh} (r : Roof@{ru rh}) :
  _1@{o h p} ⟶ Roof@{ru rh} :=
  {| fobj := fun _ => r ; fmap := fun _ _ _ => id[r] |}.

Example roof_objs_distinct : RNeg <> RPos.
Proof. discriminate. Qed.

Example roof_pi0_merges :
  @equiv _ (fobj[Pi0] Roof) RNeg RPos := Roof_Connected RNeg RPos.

(*
 π₀ is not faithful: the two constant functors [_1 ⟶ Roof] at [RNeg]
 and at [RPos] have the SAME image under π₀ (both objects lie in one
 component) and are not [≈] in [Cat], since that would give an
 isomorphism [RNeg ≅ RPos] whose forward leg is an arrow that does not
 exist. 

 --------
 π₀ 不是忠实的：两个在 [RNeg] 和 [RPos] 上的常值函子 [_1 ⟶ Roof] 在 π₀ 下有相同的像（两个对象都位于同一个分支中）并且不在 [Cat] 中的 [≈]，因为那样会产生一个同构 [RNeg ≅ RPos]，其正向箭头是一条不存在的箭头。
*)
Theorem Pi0_not_Faithful : Faithful Pi0 → False.
Proof.
  intro H.
  destruct (@fmap_inj _ _ Pi0 H _1 Roof (roof_pt RNeg) (roof_pt RPos)
              (fun _ => Roof_Connected RNeg RPos)) as [iso _].
  exact (RNeg_RPos_absurd (to (iso ttt))).
Qed.

(*
 ... and the unit is not full, so the adjunction is not an equivalence.
 [Full]'s [prefmap] is a bare section, so applying it to the zig-zag
 arrow that exists upstairs manufactures the missing [Roof]-arrow
 directly.  Read the conclusion at exactly that strength: nothing here
 rules out an equivalence between [Roof] and some discrete category by
 OTHER maps, and no essential-surjectivity statement about [Cat_Disc]
 is proved. 

 --------
 ... 并且该单位不是满的，因此陪伴不是等价的。  
 [Full] 的 [prefmap] 是一个裸段，因此将其应用于楼上存在的之字箭头可以直接生成缺失的 [Roof] 箭头。  
 以恰好那个力度来理解结论：这里没有任何内容排除 [Roof] 与某个离散范畴通过其他映射之间的等价，也没有证明关于 [Cat_Disc] 的本质满射性声明。
*)
Theorem unit_not_Full :
  Full (@unit _ _ _ _ Components_Disc_Adjunction Roof) → False.
Proof.
  intro H.
  exact (RNeg_RPos_absurd
           (@prefmap _ _ _ H RNeg RPos (Roof_Connected RNeg RPos))).
Qed.

(* * ** §7. Why the right adjoint is not the plain discrete category / * ** §7. 为什么右伴随不是普通离散范畴 *)

(*
 [bool] under the everywhere-true setoid.  This is the witness for both
 refutations: it makes [id] and [negb] equivalent as [Sets]-morphisms
 while keeping [true] and [false] Leibniz-distinct. 

 --------
 [bool] 在普遍成立的集合等价下。这是两种反驳的证据：它使 [id] 和 [negb] 作为 [Sets]-态射等价，同时保持 [true] 和 [false] 在莱布尼茨意义上不同。
*)
Program Definition blur_bool : Sets := {|
  carrier   := bool
; is_setoid := {| equiv := fun _ _ => True |}
|}.

Program Definition blur_bool_negb : blur_bool ~{Sets}~> blur_bool :=
  {| morphism := negb |}.

Example blur_bool_id_equiv_negb : id[blur_bool] ≈ blur_bool_negb := fun _ => I.

(*
 The arrow action a carrier-based discrete functor would have to have:
 objects the CARRIER, arrows Leibniz equalities, so the action on
 arrows is [f_equal]. 

 --------
 一个基于载体的离散函子必须具有的箭头作用：
 对象是载体，箭头是莱布尼兹等式，因此箭头上的作用是 [f_equal]。
*)
Program Definition disc_carrier_map@{o so dh dp} {A B : Sets@{o so}}
  (f : A ~> B) :
  DiscreteCat@{o dh dp} (carrier A) ⟶ DiscreteCat@{o dh dp} (carrier B) :=
  {| fobj := f ; fmap := fun x y (e : x = y) => f_equal f e |}.

(*
 REFUTATION.  Its [fmap_respects] field is FALSE.  This is the theorem
 that separates the two [Discrete]s of Mac Lane's string: over [Sets]
 the right adjoint cannot be Instance/Discrete.v's [DiscreteCat] on the
 carrier, which is what the sibling development's [StrictCat_Disc] is
 built from. 

 --------
 反驳。其 [fmap_respects] 字段为 FALSE。这是将 Mac Lane 的字符串的两个 [Discrete] 区分开的定理：在 [Sets] 上，右伴随不能是 Instance/Discrete.v 的 [DiscreteCat] 在承载上，这是兄弟开发的 [StrictCat_Disc] 构建的基础。
*)
Theorem DiscreteCat_carrier_not_functorial :
  (∀ (A B : Sets) (f g : A ~> B), f ≈ g →
     @equiv _ (@homset Cat (DiscreteCat (carrier A))
                           (DiscreteCat (carrier B)))
       (disc_carrier_map f) (disc_carrier_map g)) → False.
Proof.
  intro H.
  destruct (H blur_bool blur_bool id[blur_bool] blur_bool_negb (fun _ => I))
    as [iso _].
  exact (Bool.diff_true_false (to (iso true))).
Qed.

(*
 The general form, which says WHAT the obstruction is rather than
 exhibiting one instance of it: a functor [Sets ⟶ Cat] whose objects
 carry the points of the setoid injectively and naturally cannot have
 SKELETAL fibres.  [Kskel] is Theory/Skeleton.v's [Skeletal]
 predicate ([∀ x y : C, x ≅ y → x = y]) spelled out at each fibre;
 that module is not required here, so the hypothesis is written out
 rather than imported.

 Read the argument: [id ≈ negb] gives a natural isomorphism between the
 two induced functors; evaluating it at the point [true] and rewriting
 both ends by naturality turns it into [pt true ≅ pt false];
 skeletality makes that a Leibniz equality and injectivity finishes. 

 --------
 一般形式，说明阻碍是什么而不是展示其中一个实例：一个函子 [Sets ⟶ Cat]，其对象携带集合论点的方式是单射且自然的，不能有 SKELETAL 纤维。[Kskel] 是 Theory/Skeleton.v 的 [Skeletal] 谓词（[∀ x y : C, x ≅ y → x = y]），在每个纤维处具体说明；该模块在这里不需要，因此假设被写出来而不是导入。

 阅读论证：[id ≈ negb] 给出了两个诱导函子之间的自然同构；在点 [true] 处求值并通过自然性重写两端，将其变为 [pt true ≅ pt false]；骨架性使其成为莱布尼茨等式，注入性完成证明。
*)
Theorem no_skeletal_carrier_functor_Sets_Cat
  (K : Sets ⟶ Cat)
  (pt : ∀ A : Sets, carrier A → obj[fobj[K] A])
  (Kobj : ∀ (A B : Sets) (f : A ~> B) (x : carrier A),
            fobj[fmap[K] f] (pt A x) = pt B (f x))
  (Kskel : ∀ (A : Sets) (x y : obj[fobj[K] A]), x ≅ y → x = y)
  (Kinj : ∀ (A : Sets) (x y : carrier A), pt A x = pt A y → x = y) :
  False.
Proof.
  destruct (@fmap_respects _ _ K blur_bool blur_bool
              id[blur_bool] blur_bool_negb (fun _ => I)) as [iso _].
  pose proof (iso (pt blur_bool true)) as I0.
  rewrite (Kobj blur_bool blur_bool id[blur_bool] true) in I0.
  rewrite (Kobj blur_bool blur_bool blur_bool_negb true) in I0.
  simpl in I0.
  exact (Bool.diff_true_false (Kinj blur_bool true false (Kskel _ _ _ I0))).
Qed.

(*
 ... and the refutation is not vacuous for [Cat_Disc]: it satisfies
 [Kobj] (at [eq_refl]) and [Kinj] (by the identity function), and fails
 EXACTLY [Kskel].  So the escape is located rather than assumed, and
 the general theorem is genuinely about the shape of the fibres. 

 --------
 ... 并且对于 [Cat_Disc] 来说反驳并非空洞：它满足 [Kobj]（在 [eq_refl] 时）和 [Kinj]（通过恒等函数），并且恰好在 [Kskel] 失败。因此，逃逸是被定位的而非假设的，并且一般定理确实关于纤维的形状。
*)
Definition cat_disc_pt (A : Sets) : carrier A → obj[fobj[Cat_Disc] A] :=
  fun a => a.

Example cat_disc_Kobj (A B : Sets) (f : A ~> B) (x : carrier A) :
  fobj[fmap[Cat_Disc] f] (cat_disc_pt A x) = cat_disc_pt B (f x) := eq_refl.

Definition cat_disc_Kinj (A : Sets) (x y : carrier A) :
  cat_disc_pt A x = cat_disc_pt A y → x = y := fun e => e.

Theorem Cat_Disc_not_skeletal :
  (∀ (A : Sets) (x y : obj[fobj[Cat_Disc] A]), x ≅ y → x = y) → False.
Proof.
  intro Hskel.
  refine (Bool.diff_true_false (Hskel blur_bool true false _)).
  exact (disc_setoid_iso (is_setoid blur_bool) I).
Qed.

(*
 NEGATIVE 4 (CONVERSION).  The two discrete categories are not even
 convertible, which pins at the level of terms what the refutation
 above establishes at the level of theorems.  The controls are
 [cat_disc_obj] and [cat_disc_obj_carrier] in §2: the object TYPES do
 agree. 

 --------
 负 4（转换）。这两个离散类别甚至无法转换，这在术语层面上确定了上述在定理层面上所建立的驳斥。控制是第 2 节中的 [cat_disc_obj] 和 [cat_disc_obj_carrier]：对象类型确实一致。
*)
Fail Example disc_is_DiscreteCat (A : Sets) :
  fobj[Cat_Disc] A = DiscreteCat (carrier A) := eq_refl.

(** ** §8. The universe boundary / ** §8. 宇宙边界 *)

(*
 Instrument check: [Fail] is live in this file.  Every negative above
 and below was additionally stripped once and its failure kind read off
 the whole error message -- four CONVERSION failures in §4 and §7,
 reporting “cannot unify” with no universe clause, and two FORMABILITY
 failures here, reporting “universe inconsistency: Cannot enforce ...”.
 The two kinds are kept lexically apart. 

 --------
 仪器检查：[Fail] 在此文件中为实时。上述每个正负号都额外被剥离一次，并且读取了整个错误消息的失败类型——§4 和 §7 中有四次转换失败，报告“无法统一”，没有宇宙子句，这里有两次可形成性失败，报告“宇宙不一致：无法强制……”。这两种类型在词汇上保持分开。
*)
Fail Definition probe_instrument_live : Datatypes.unit := 0.

(*
 Section-local [Universes]/[Constraint] declarations do not leak; the
 Instance/Fun/Group.v precedent applies, so these probes live in the
 library file beside the constants they guard rather than in [Test/].

 FIRST, the restriction and its attribution.  The [Constraint] here is
 LOAD-BEARING and that was measured by deletion: without it [ch]
 unifies with [co] and both negatives succeed.

 The three controls run down the chain and each removes one candidate
 culprit.  [C : obj[Cat]] shows the ambient category of categories is
 innocent -- it accepts a category whose homs sit STRICTLY BELOW its
 objects.  [pi0 C] shows the object map is innocent.  [pi0_fmap] at
 that same C shows the arrow map is innocent.  What is left is
 [pi0_fmap_respects] (Theory/Connected/Components.v), declared over
 [Category@{u0 u0 u0}], and it is rejected -- as is [fobj[Pi0] C] with
 it, on the same message.  So [Pi0], and hence every constant of this
 file that mentions it, accepts only categories whose object, hom and
 proof universes COINCIDE. 

 --------
 段本地 [Universes] / [Constraint] 声明不会泄漏；Instance/Fun/Group.v 的先例适用，因此这些探针与它们保护的常量一起存在于库文件中，而不是存在于 [Test/] 中。

 首先，限制及其归属。这里的 [Constraint] 是承载负载的，这是通过删除进行测量的：没有它，[ch] 会与 [co] 统一，并且两个否定都会成功。这三个控制沿链运行，每个控制移除一个候选肇事者。[C : obj[Cat]] 显示类别的环境类别是无辜的——它接受一个同态严格位于其对象之下的类别。[pi0 C] 显示对象映射是无辜的。[pi0_fmap] 在同一个 C 上显示箭头映射是无辜的。剩下的是 [pi0_fmap_respects]（Theory/Connected/Components.v），在 [Category@{u0 u0 u0}] 上声明，并且被拒绝——与此一起的 [fobj[Pi0] C] 也被拒绝，并显示相同的信息。所以 [Pi0]，因此该文件中所有提到它的常量，只接受对象、同态和证明宇宙一致的类别。
*)
Section Pi0Restriction.
  Universes co ch.
  Constraint ch < co.
  Context (C D : Category@{co ch ch}).

  Check (C : obj[Cat]).
  Check (pi0 C).
  Check (fun F : C ⟶ D => pi0_fmap F).

  Fail Check (fun (F G : C ⟶ D) => @pi0_fmap_respects C D F G).
  Fail Check (fobj[Pi0] C).
End Pi0Restriction.

(*
 SECOND, the accepted class is inhabited: at a category with all three
 universes at one level [pi0_fmap_respects], [Pi0] and the
 transposition are all formable, so the restriction above cuts rather
 than empties.  There is no [Constraint] here and none is wanted.

 The first control here exists because a rename simulation FOUND A
 VACUOUS GUARD: [pi0_fmap_respects] was named only inside its own
 [Fail], so a rename of the donor would have turned that negative
 silently green.  Naming it in a command that must SUCCEED closes
 that. 

 --------
 第二，所接受的类是有元素的：在一个包含三个宇宙的同级类别中 [pi0_fmap_respects]、[Pi0] 以及换位都是可以构造的，所以上述限制是削减而不是清空。这里没有 [Constraint]，也没有人需要它。

 第一个控制存在的原因是因为重命名模拟发现了一个空守卫：[pi0_fmap_respects] 只在其自身的 [Fail] 内被命名，所以如果对捐赠者进行重命名，会悄无声息地将其负值变成绿色。在一个必须成功的命令中命名它就解决了这个问题。
*)
Section Pi0Accepted.
  Universes cu.
  Context (C : Category@{cu cu cu}).
  Check (fun (F G : C ⟶ C) => @pi0_fmap_respects C C F G).
  Check (fobj[Pi0] C).
  Check (fun A : Sets => pi0_adj_iso C A).
End Pi0Accepted.

(*
 THIRD, and this is the guard item IV promised: the identification is
 MINIMIZATION AND NOT CONTENT.  The donor's lemma is restated here with
 its binders written out -- same statement, same one-line proof text,
 nothing else changed -- inside a section declaring BOTH categories'
 hom universes STRICTLY BELOW their object universe, and it is
 accepted.  The [Constraint]s are meaning-giving rather than
 load-bearing: the [Lemma] would elaborate without them, but then the
 levels could collapse and the command would demonstrate nothing.

 This is a PROBE.  The repair belongs to
 Theory/Connected/Components.v and is NOT performed here; nothing
 in this file uses the restatement, and no claim is made that [Pi0]
 itself would then be free, which would require rebuilding it.  Note
 also what the repair does not remove: the restated lemma still carries
 [hc = hd] in its own constraint block, identifying the two categories'
 hom universes with each other. 

 --------
 第三，这是 IV 承诺的保护项目：识别是最小化而不是内容。这里重新陈述了捐赠者的引理，并将其绑定器写出——相同的陈述，相同的一行证明文本，其他均未更改——在一个声明两个类别的同态宇严格低于其对象宇的部分中，并且已被接受。[Constraint] 是赋予意义的而非承重的：没有它们 [Lemma] 也可以展开，但那样的话层级可能会塌陷，命令将无法显示任何内容。这是一个探测。修复属于 Theory/Connected/Components.v，并未在此处执行；此文件中没有任何内容使用该重述，也没有声称 [Pi0] 本身因此会被释放，这将需要重建它。还要注意修复没有删除的内容：重述的引理仍然在其自身的约束块中包含 [hc = hd]，将这两类的同构宇宙彼此关联起来。
*)
Section Pi0RespectsRepairable.
  Universes o hc hd so.
  Constraint hc < o.
  Constraint hd < o.

  Lemma probe_pi0_fmap_respects_annotated
    {C : Category@{o hc hc}} {D : Category@{o hd hd}} (F G : C ⟶ D)
    (H : F ≈ G) : @pi0_fmap@{o so hc hd} C D F ≈ pi0_fmap G.
  Proof. intro x; exact (hom_zigzag (to (`1 H x))). Qed.
End Pi0RespectsRepairable.
