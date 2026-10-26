Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Two.

Generalizable All Variables.

(* * * Pointwise monos and epis in a functor category / * * 函子范畴中的逐点单态与满态 *)

(*
 SOURCES

 Mac Lane, “Categories for the Working Mathematician”, 2nd ed., §IV.3,
 printed p. 91 (p. 100 of the PDF scan), the remark between the Lemma
 on representable transformations and its proof.  Read off a 300-dpi
 render of that page and quoted here verbatim, subscripts and all:

 “Observe, also, that for functors S, T : C→B, a natural
 transformation τ : S ⇸ T is epi (respectively, monic) in B^C if
 and only if every component τ_c : S_c → T_c is epi (respectively,
 monic) in B for B = Set; this follows by Exercise III.4.4,
 computing the pushout pointwise as in Exercise III.5.5.”

 Catalog item maclane:IV.3:remark1.  Also covered: Awodey, “Category
 Theory”, 1st ed. (Carnegie Mellon pre-print, September 2005), §7.10
 Exercise 6, printed p. 187 (PDF p. 196), item awodey:7:ex6 — show
 that a natural transformation is an isomorphism in the functor
 category exactly when each component is, and decide whether the
 analogous statement holds for monomorphisms.  That page is NOT in the
 Mac Lane scan, so the exercise is taken from the issue's own
 paraphrase rather than from the book, and this header says so rather
 than presenting it as a quotation.

 nLab: https://ncatlab.org/nlab/show/functor+category
 nLab: https://ncatlab.org/nlab/show/monomorphism
 nLab: https://ncatlab.org/nlab/show/epimorphism
 nLab: https://ncatlab.org/nlab/show/kernel+pair
 nLab: https://ncatlab.org/nlab/show/category+of+presheaves

 READ THE PRINTED SENTENCE PRECISELY.  Mac Lane states the
 BICONDITIONAL for B = Set and for no other target; the clause “for
 B = Set” governs the whole “if and only if”.  So the split this file
 takes — an implication for an arbitrary target, a biconditional at
 Sets — is the print's own, not a hedge.  His stated route is the
 pointwise (co)limit computation, and that is the route taken here.

 WHAT IS DELIVERED, AND AT WHAT STRENGTH

 (A) For an ARBITRARY target D: [pointwise_monic_is_monic] and
 [pointwise_epic_is_epic].  Nothing in that section mentions Sets;
 the section binds only two categories, two functors and a
 transformation, and the two proofs consume exactly two in-tree
 facts about `[C, D]` — that its composition is componentwise
 ([nat_compose], Theory/Natural/Transformation.v, whose
 component at x is `f x ∘ g x`) and that its hom-setoid compares
 components pointwise ([Transform_Setoid]).  Both are
 definitional, so `Heq x` is already the equation in D that the
 component's cancellation property consumes, and neither proof
 rewrites anything.

 (B) For D = Sets: [sets_functor_monic_iff_pointwise] and
 [sets_functor_epic_iff_pointwise], genuine biconditionals, with
 the converse halves [sets_functor_monic_pointwise] and
 [sets_functor_epic_pointwise] available separately.  Section B
 binds D := Sets and nothing else; A and B are lexically separate
 so that no reader has to check whether the general statement
 leaked a Sets hypothesis.

 (C) Awodey's isomorphism half as a predicate on a GIVEN θ:
 [nat_iso_iff_pointwise], both directions [Defined], with
 [componentwise_iso] naming the backward construction and
 [nat_iso_pointwise] the forward one.

 (D) The presheaf corollaries: [presheaf_monic_iff_pointwise] and
 [presheaf_epic_iff_pointwise] are `:=` of (B) at C^op with no
 tactic, and [presheaf_monic_iff_injective] /
 [presheaf_epic_iff_surjective] spell out the [Instance/Sets]
 reading — monic in `[C^op, Sets]` exactly when every component is
 injective, epic exactly when every component is surjective.  These
 are the statements the subobject-classifier work wants to cite.

 THE MONOMORPHISM DECISION (Awodey's “decide whether the analogous
 statement holds”).  Componentwise monic implies monic for EVERY
 target D — that is (A), with no hypothesis on D at all.  The converse
 is delivered at Sets, by (B), and the argument shows what it needs:
 it holds wherever the kernel pair of θ can be computed pointwise, and
 over Sets it can.  For an arbitrary D the converse is NOT proved
 here, and NO separating example is built, so nothing in this file
 licenses the sentence “the converse is false in general” — the honest
 report is that it is not established in general and that this file
 offers no countermodel.

 HOW THE Sets CONVERSE IS PROVED, AND WHAT HAD TO BE BUILT

 Mac Lane's route is the pointwise computation, and the two functors
 it needs did not exist.  Measured at bbddaee2, before this file was
 added: searches for `HasPullbacks (\[`, `HasPushouts (\[` and
 `kernel.?pair.*pointwise` over every `.v` file returned nothing (the
 third now matches this header's own prose and nothing else), and a
 wider sweep of every file that mentions both a functor category and
 a pullback, pushout or kernel-pair token finds only limits of a
 DIAGRAM into a category — Adjunction/Diagonal/Finite.v's
 [PullbackFunctor] : [Roof^op, C] ⟶ C — and the arrow-category
 [CokernelPairFunctor] : Arrow C ⟶ [Parallel, C] of
 Adjunction/CokernelPair.v, neither of them a (co)limit IN a functor
 category.  So no pullback, pushout or kernel pair at a functor
 category was declared, and the two are built here as named
 [Definition]s with their functor laws proved, since they, not the
 two biconditionals, are the reusable part:

 [KerPair θ] : C ⟶ Sets, object action x ↦ [sets_ker (θ x)] —
 Instance/Sets/Pullback.v's agreement sub-setoid
 {(a,b) | θ x a ≈ θ x b}, which is [sets_pb_obj (θ x) (θ x)]
 — with arrow action `(a, b) ↦ (fmap[F] f a, fmap[F] f b)`, and its
 two projection transformations [KerFst], [KerSnd].  Naturality of θ
 is exactly what makes the arrow action land back in the kernel
 pair: [ker_map_ok] is one use of [theta_nat] on each side of the
 given agreement.  [ker_agree] says θ ∙ KerFst ≈ θ ∙ KerSnd, whose
 proof is the second projection of the sigma; left cancellation then
 equates the two projections, which at the pair ((a,b); H) IS
 injectivity of θ x, and [injectivity_is_monic]
 (Instance/Sets.v) closes.

 [CokerPair θ] : C ⟶ Sets, object action x ↦ [CKSetoid (θ x)]
 (Instance/Sets.v), two copies of G x glued along the image of
 θ x, with arrow action the image of `fmap[G] f` in each copy, and
 its two injections [CkLeft], [CkRight].  Here naturality is what
 carries an image witness forward ([ck_Im_map]).  [ck_agree_nat] is
 [ck_agree] at each component; right cancellation equates the
 two injections, and reading the resulting relation at b gives the
 preimage, exactly as [epic_implies_surjective] does one
 level down; [surjectivity_is_epic] closes.

 Note what is NOT consumed: [sets_ck_IsCokernelPair]
 (Instance/Sets/CokernelPair.v) is the universal property of that
 cokernel pair, and the argument here needs only the commuting square
 [ck_agree], so that module is not required and the file's transitive
 closure stays at 39 modules.  The construction remains a cokernel
 pair pointwise; it is simply not the part being spent.

 A Yoneda/representable route (probe θ with [Curried_Hom C c],
 Functor/Hom.v) was NOT taken.  The reviewer check on this issue
 demands the pointwise-(co)limit computation, and that is what is
 delivered; the alternative was not measured either, so this file
 makes no claim about its cost.

 PRIOR ART, AND HOW (C) DIFFERS FROM IT

 [Functor_Setoid_Nat_Iso] (Instance/Fun.v) states
 `F ≅[Fun] G ↔ F ≈ G`.  That is the EXISTENTIAL form: it says the two
 functors are isomorphic, and the isomorphism it produces in the
 backward direction is the one it builds out of the given family.  It
 does not let a reader ask whether a PARTICULAR θ already in hand is
 invertible, which is what Awodey's exercise is about and what
 [nat_iso_iff_pointwise] supplies.  The two are related here rather
 than merely contrasted: [nat_iso_family] turns a componentwise family
 of inverses into the `F ≈ G` that theorem consumes, and both legs of
 the isomorphism it then builds agree with ours on their `transform`
 FIELDS at Leibniz equality — [equiv_iso_to_is_theta] and
 [equiv_iso_from_is_nat_inverse] are [eq_refl] pointwise, and the probe
 restates both as equalities of the whole transform functions — so the
 inverse [componentwise_iso] builds IS the inverse [equiv_iso] builds,
 as a function.  Neither whole LEG is the same record as ours, and
 neither is the whole isomorphism, and Test/ProbeMorphisms369.v pins
 all three: the donor builds both legs with `abstract`ed naturality
 proofs (Instance/Fun.v), so each leg carries its own opaque
 law fields, and the two isomorphism records then carry their own
 inverse law fields on top.  The difference is therefore confined to
 opaque LAW fields — the legs' naturality fields and the record's
 inverse laws — and touches no data.  This file's first draft located
 it in the inverse law fields alone; an audit measured the legs.

 CORRECTIONS

 To the issue.  Its “Current state” is right on the absence — at
 bbddaee2, before this file was added, the command
 `rg -c 'Monic|Epic'` over Instance/Fun.v, Instance/Fun/ and
 Theory/Natural/ returned no hits at all (it now matches this file and
 nothing else in those locations) — but two of its donor
 line numbers are stale: [injectivity_is_monic] and
 [surjectivity_is_epic] are both in Instance/Sets.v, neither of them
 where the issue places it.  Both were re-checked here.

 To the OCR.  A plain `pdftotext -f 100 -l 100` of the scan mangles
 the sentence badly — it renders τ as “I”, the superscript C of B^C as
 “e”, both subscripts as “e” (“Ie: Se----> Te”), and both Roman
 numerals as “111” — so it is not usable as a quotation.  The text
 above is read from the page image instead.  Even a cleaned-up OCR
 renders the subscripted S_c and T_c as “S c” and “T c”; the printed
 page sets them as subscripts, and the quotation above keeps them.

 UNIVERSES, MEASURED OFF BOTH BINDER AND BLOCK

 Every constant of sections A-D was read with `Set Printing Universes`
 and its whole (wrapped) constraint block flattened before counting.

 The general theorems are
 `pointwise_monic_is_monic@{u u0 u1 u2 u3 u4 u5}` over
 `C : Category@{u u0 u0}` and `D : Category@{u1 u2 u2}` — hom
 identified with proof in BOTH binders, expressed by reusing the level
 variable — with the block carrying the equation `u0 = u2`, which
 identifies C's hom-and-proof level with D's.  Both OBJECT universes
 stay free: `u` and `u1` occur in bounds only, in no equation.  So a
 reader who checks only the block sees one identification and misses
 two; both must be read.

 The identifications are INHERITED and are attributed by isolating
 experiments in the probe, not by assertion.  Under a declared
 `Constraint ch < dh` the functor category `@Fun Cu Du` is rejected
 with “Cannot enforce dh = ch” while `x ~{Cu}~> y` and `a ~{Du}~> b`
 are both accepted at those very levels: [Fun] takes both categories
 at ONE hom-and-proof level, which is the source of `u0 = u2` and of
 half of each binder's hom=proof.  Independently, under
 `Constraint mh < mp` both `@Monic Du a b g` and `@Epic Du a b g` are
 rejected with “Cannot enforce mp = mh” against the same two accepted
 controls, so the classes of Theory/Morphisms.v identify hom with
 proof on their own.  Neither identification is introduced here and
 neither is claimed unavoidable.

 At Sets the picture is the same one level in:
 `sets_functor_monic_iff_pointwise` is over `C : Category@{u u0 u0}`
 with the two functors landing in `Sets@{u0 u1}` and `Sets@{u0 u2}`,
 and the block adds `u0 < u1`, `u0 < u2` and `u1 = u2` — the two
 occurrences of Sets are forced to be ONE instance, which is what
 `[C, Sets]` means, and Sets' carrier level is C's hom level, which is
 `Sets@{o so} : Category@{so o o}` meeting [Fun].

 THE WITNESS SECTION CARRIES A `Set` PIN AND THE GENERAL RESULTS DO
 NOT.  Sweeping all 74 constants for the literal token `Set` in binder
 or block, exactly 20 carry it: the 16 named constants of the witness
 section (TwoOne, TwoBool, TwoTwoX, TwoTwoY, two_pick_nat,
 two_collapse, two_arrow, pick_true_Monic, collapse_Epic and the seven
 results about them) together with four of their obligations
 (two_pick_nat_obligation_1/2, two_collapse_obligation_1/2).  The
 cause is [_2] itself: `_2@{u u0} : Category@{u Set Set}`, because
 Instance/Two.v declares `TwoHom : TwoObj → TwoObj → Set`, and [Fun]
 then forces the target's hom-and-proof level to match, so `[_2, Sets]`
 is `Sets@{Set _}`.  Sections A-D are free of it.  This is inherited,
 is the price of using the cheapest non-trivial shape in the tree, and
 is not claimed unavoidable.

 ENGINEERING FINDINGS

 1.  A [Program Definition] of a Sets-morphism that leaves
 `proper_morphism` to instance resolution can pin the carrier
 universe to `Set`.  Both new functors therefore supply their
 arrow action's respectfulness certificate BY HAND —
 [ker_fun_proper] and [ck_fun_proper] are ordinary lemmas and
 [ker_map]/[ck_map] are record literals — and the measurement
 above confirms sections A-D acquired no `Set`.

 2.  `Set Transparent Obligations` was tried at the top of this file
 and is NOT needed: both [eq_refl] comparisons with
 [Functor_Setoid_Nat_Iso] hold with the repo's ordinary opaque
 obligations, because [nat_inverse] supplies its `transform` field
 directly and only its two naturality fields become obligations.
 The line was removed after measuring that.

 3.  [Constant_Functor] already exists (Instance/Fun/Terminal.v)
 and is not reused: requiring that module would take this file's
 transitive closure from 39 modules to 74 (measured by following
 every Require line to a fixed point), which is a heavy price on
 every downstream consumer of a file whose whole purpose is to be
 cited.  A five-line witness-local [const_fun] is declared
 instead, with the duplication recorded here rather than hidden.

 4.  Applying [fmap_respects], [fmap_id] and [fmap_comp] inside Sets
 needs the pointwise reading: `fmap[F] f ≈ fmap[F] g` unfolds to
 `∀ a, ...`, so `apply fmap_id` does not match and the field must
 be applied as a term (`exact (@fmap_id _ _ F _ _)`).

 5.  The identity of `[C, D]` has component `fmap[G] id`, not `id`
 (Theory/Natural/Transformation.v), so the two inverse laws of
 [componentwise_iso] and [nat_iso_pointwise] each cost one
 `fmap_id` step; that residue is the only friction in section (C).

 6.  A name collision was found by sweeping every name this file
 introduces and was renamed away before landing: [two_pick] is
 taken by Instance/Fun/Terminal.v, and since the
 print-assumptions target loads many modules into one scope a
 shared name would have audited the wrong constant.  The witness
 here is [two_pick_nat].  Over all 95 names introduced by this
 file and its probe — 52 declaration heads, 22 [Program]
 obligations, and the probe's 12 declared and 9 rejected names —
 zero collisions remain; the sweep was instrument-checked on
 [Monic] and [Full], which must collide and do.

 NON-VACUITY

 [two_pick_nat] is monic in `[_2, Sets]` and provably not epic there,
 and [two_collapse] is epic and provably not monic — each refutation
 routed through the CONVERSE half, so section (B) is exercised and not
 merely stated, with the pointwise obstruction exhibited at the named
 component [TwoX]: [two_pick_component_not_surjective] discharges by
 `discriminate` on `true = false` in the two-element setoid.  The
 general direction is exercised at a target that is NOT Sets by
 [two_arrow_Monic] and [two_arrow_Epic] over `[_2, _2]`, on
 Instance/Two.v's [TwoXY_monic]/[TwoXY_epic].  DEGENERACY, labelled:
 all three witness transformations ([two_pick_nat], [two_collapse],
 [two_arrow]) run between CONSTANT functors, so
 their naturality squares reduce to `θ_x ≈ θ_y` and the witnesses
 exercise the hom-setoids and the cancellation arguments rather than
 naturality; and `[_2, _2]` has thin hom-setoids.  What they are for
 is the cancellation content, and that they do carry.

 NOT DELIVERED

 No converse at a general target, and no separating example refuting
 one — see THE MONOMORPHISM DECISION above.  Pullbacks for a functor
 category are now Instance/Fun/Pullback.v's [Fun_HasPullbacks], and
 pushouts are still none; the two functors HERE are unaffected by
 that — they remain the pointwise (co)limit OBJECTS with their legs,
 and no universal property is claimed for either in `[C, Sets]`.  No
 identification of [KerPair] with [Structure/Regular.v]'s generic
 [kernel_pair] one level up, and none with [CokerPair] and
 [Theory/Morphisms/CokernelPair.v]'s [cokernel_pair].  No statement
 that [KerPair] or [CokerPair] is functorial in θ.  No Yoneda or
 representability route and no comparison with one.  The subobject
 classifier for presheaves is now Instance/Fun/Classifier.v's
 [Fun_Classifier], which cites (D) at three sites — the mediator's
 respectfulness, its naturality and the uniqueness clause — and a
 fourth in its re-annotated [Fun_Classifier_small]; there is still no
 subobject lattice for presheaves.  Nothing about split monos,
 split epis, regular or effective epis, or balancedness of `[C, D]`.
 No witness at a shape other than [_2], and no witness with a
 non-constant functor. 

 --------
 来源

 Mac Lane，《为工作的数学家准备的范畴论》，第2版，§IV.3，
 印刷版第91页（PDF扫描的第100页），引理关于可表示变换及其证明之间的备注。读取该页的300-dpi渲染并逐字引用如下，包括下标在内：

 “还要注意，对于函子 S, T : C→B，自然变换 τ : S ⇸ T 当且仅当每个分量 τ_c : S_c → T_c 在 B 中是满射（分别为单射），则在 B^C 中是满射（分别为单射），其中 B = Set；这由练习 III.4.4 得出，通过按点计算推挤如练习 III.5.5 所示。”目录项 maclane:IV.3:remark1。 还涵盖：Awodey，《范畴论》，第一版（卡内基梅隆预印本，2005 年 9 月），§7.10 练习 6，打印页 187（PDF 页 196），条目 awodey:7:ex6 —— 证明自然变换在函子范畴中恰好当每个分量都是同构时才是同构，并判断对单态态射是否也适用类似结论。该页不在 Mac Lane 扫描版中，因此练习取自该期刊的自拟内容而非书本，标题也说明了这一点，而不是将其作为引用呈现。

 nLab: https://ncatlab.org/nlab/show/functor+category
 nLab: https://ncatlab.org/nlab/show/monomorphism
 nLab: https://ncatlab.org/nlab/show/epimorphism
 nLab: https://ncatlab.org/nlab/show/kernel+pair
 nLab: https://ncatlab.org/nlab/show/category+of+presheaves准确阅读印刷的句子。Mac Lane 针对 B = Set 陈述了双条件，而没有针对其他目标；“对于 B = Set”这一分句支配整个“当且仅当”。因此，本文件所采用的拆分——对任意目标的一个蕴涵，在集合上的一个双条件——就是印刷版本身的处理方式，而不是一种保留。他所陈述的方式是逐点 (co) 极限计算，这也是这里所采用的方式。

 所交付的内容是什么，以及其强度如何(A) 对于任意目标 D: [pointwise_monic_is_monic] 和 [pointwise_epic_is_epic]。该部分没有提到集合；该部分只涉及两个范畴、两个函子和一个变换，并且这两个证明正好使用了关于 ` [C, D]ZZ ` 的两个树内事实——它的组合是按分量的 ([nat_compose]，Theory/Natural/Transformation.v，其中在 x 的分量是 `f x ∘ g x`) 并且它的同集合按照分量逐点比较 ([Transform_Setoid])。两者都是定义性的，因此 `Heq x` 已经是 D 中的那个方程，该分量的消去性质使用它，并且两个证明都没有重写任何内容。(B) 对于 D = 集合: [sets_functor_monic_iff_pointwise] 和 [sets_functor_epic_iff_pointwise]，真正的双条件，对于逆半部分 [sets_functor_monic_pointwise] 和 [sets_functor_epic_pointwise] 分别提供。B 节绑定 D := 集合，除此之外没有绑定；A 和 B 在词法上是分开的，因此读者无需检查一般陈述是否泄露了集合的假设。

 (C) Awodey 的同构半作为给定 θ 的谓词: [nat_iso_iff_pointwise]，双向 [Defined]，其中 [componentwise_iso] 命名反向构造，[nat_iso_pointwise] 命名正向构造。(D) 预层推论：[presheaf_monic_iff_pointwise] 和 [presheaf_epic_iff_pointwise] 是 (B) 在 C^op 上的 `:=`，没有策略，而 [presheaf_monic_iff_injective] / [presheaf_epic_iff_surjective] 说明了 [Instance/Sets] 的读法——当且仅当每个分量都是单射时在 ` [C^op, Sets]ZZ ` 中为单态，当且仅当每个分量都是满射时为满态。这些是子对象分类器工作希望引用的陈述。单态决策（Awodey 的“决定类似命题是否成立”）。 分量单态意味着对于每一个目标 D 都是单态 —— 即（A），完全不对 D 做假设。 相反的命题在集合（Sets）中由（B）给出，且论证展示了所需条件：它在 θ 的核对可以逐点计算的地方成立，而在集合中可以。 对于任意 D，这里没有证明相反的命题，也没有构造任何分离性例子，因此本文件中没有任何内容支持“相反命题在一般情况下是错误的”这一说法 —— 诚实的报告是，它在一般情况下尚未被证明，并且本文件没有提供反例模型。

 集合中的相反命题是如何被证明的，以及必须构建的内容Mac Lane 的方法是逐点计算，而它所需的两个函子并不存在。在 bbddaee2 版本测量时，在此文件添加之前：在每个 `.v` 文件中搜索 `HasPullbacks (\[`、`HasPushouts (\[` 和 `kernel.?pair.*pointwise` 未返回任何结果（第三个现在匹配此标题本身的文字，而没有其他匹配），并且对提到函子范畴和拉回、推出或核对偶符号的每个文件进行更广泛的搜索，仅找到一个 DIAGRAM 到范畴的极限——Adjunction/Diagonal/Finite.v 的 [PullbackFunctor] : [Roof^op, C] ⟶ C——以及箭头范畴 [CokernelPairFunctor] : Arrow C ⟶ [Parallel, C] 的 Adjunction/CokernelPair.v，它们都不是函子范畴中的 (余)极限。因此，在函子范畴中没有声明拉回、推出或核对，而这里将它们构建为命名的 [Definition]，并证明了它们的函子律，因为它们，而不是两个双条件，是可重用的部分：[KerPair θ] ：C ⟶ 集合，对象作用 x ↦ [sets_ker (θ x)] — Instance/Sets/Pullback.v 的一致子等价集 {(a,b) | θ x a ≈ θ x b}，这就是 [sets_pb_obj (θ x) (θ x)] — 其箭头作用为 `(a, b) ↦ (fmap [F]ZZ  f a, fmap [F]ZZ  f b)`，并且有两个投影变换 [KerFst]，[KerSnd]。θ 的自然性正是使箭头作用返回到核对偶中：[ker_map_ok] 是在给定一致性两边对 [theta_nat] 的一次使用。[ker_agree] 表示 θ ∙ KerFst ≈ θ ∙ KerSnd，其证明是 sigma 的第二个投影；左侧消去然后等化两个投影，对 ((a,b); H) 对应的就是 θ x 的单射性，并且 [injectivity_is_monic] (Instance/Sets.v) 完成。[CokerPair θ] ：C ⟶ 集合，物体作用 x ↦ [CKSetoid (θ x)]（Instance/Sets.v），两个 G x 的副本沿 θ x 的像粘合，箭头作用是在每个副本中 `fmap [G]ZZ  f` 的像，以及它的两个插入 [CkLeft]、[CkRight]。这里的自然性是将像的见证向前传递（[ck_Im_map]）。[ck_agree_nat] 在每个分量上是 [ck_agree]；右取消将两个插入等同，并且在 b 处读取结果关系得到原像，正如 [epic_implies_surjective] 在下一级所做的；[surjectivity_is_epic] 结束。注意未被使用的部分：[sets_ck_IsCokernelPair] (Instance/Sets/CokernelPair.v) 是该余核对的泛性质，而这里的参数只需要交换方形 [ck_agree]，因此该模块并不需要，文件的传递闭包仍保持在 39 个模块。该构造在逐点上仍是余核对；只是不属于被消耗的部分。

 没有采用 Yoneda/可表述的路线（探针 θ 与 [Curried_Hom C c], Functor/Hom.v）。评审者对这个问题的检查要求逐点-(余)极限计算，而这正是提供的内容；替代方法也未被测量，因此该文件不对其成本作任何声明。

 现有技术，以及 (C) 与其的不同之处[Functor_Setoid_Nat_Iso]（Instance/Fun.v）指出 `F ≅ [Fun]ZZ  G ↔ F ≈ G`。那是存在形式：它表示两个函子是同构的，并且它在反向方向上产生的同构是它从给定族构建的同构。它不允许读者询问手头的特定 θ 是否可逆，这正是 Awodey 的练习所涉及的，也是 [nat_iso_iff_pointwise] 提供的内容。这里两者是相关的，而不仅仅是对比：[nat_iso_family] 将一种按分量的逆族转换为定理所使用的 `F ≈ G`，并且它随后构建的同构的两个分支在莱布尼茨等式上的 `transform` FIELDS 与我们的匹配——[equiv_iso_to_is_theta] 和 [equiv_iso_from_is_nat_inverse] 在每一点上都是 [eq_refl]，并且探针将两者重新表述为整体变换函数的等式——因此逆 [componentwise_iso] 构建的确实是 [equiv_iso] 构建的逆，作为一个函数。两个完整的 LEG 都不是与我们的记录相同的，完整同构也不是，而 Test/ProbeMorphisms369.v 钉住了三个：捐赠者使用 `abstract` ed 自然性证明（Instance/Fun.v）构建两条腿，因此每条腿都有自己的不透明定律字段，然后两个同构记录在其上再各自携带自己的逆定律字段。因此差异仅限于不透明的定律字段——腿的自然性字段和记录的逆定律——而不涉及任何数据。该文件的初稿只将其定位在逆定律字段中；一次审计测量了这些腿。

 更正说到这个问题。它的“当前状态”正好是不存在——在 bbddaee2 提交之前，这个文件还没有被添加，命令 `rg -c 'Monic|Epic'` 在 Instance/Fun.v, Instance/Fun/ 和 Theory/Natural/ 上完全没有匹配（现在它匹配这个文件，但在这些位置没有其他匹配）——但是它的两个来源行号已经过时：[injectivity_is_monic] 和 [surjectivity_is_epic] 都在 Instance/Sets.v 中，它们都不在问题所在的位置。这两行在这里都重新检查过了。致 OCR。一份普通的 `pdftotext -f 100 -l 100` 扫描严重破坏了句子——它将 τ 识别为“I”，将 B^C 的上标 C 识别为“e”，两个下标都识别为“e”（“Ie: Se----> Te”），两个罗马数字都识别为“111”——所以不能作为引用使用。上面的文本是直接从页面图像读取的。即使是清理过的 OCR 也将下标 S_c 和 T_c 识别为“S c”和“T c”；印刷页面将它们设置为下标，上面的引用保持了这一点。

 宇宙，既测量绑定器也测量模块

 每一节 A-D 的常数都是用 `Set Printing Universes` 读取的，并在计数前将其整个（包裹的）约束块展开。一般定理是
 `pointwise_monic_is_monic@{u u0 u1 u2 u3 u4 u5}` 关于
 `C : Category@{u u0 u0}` 和 `D : Category@{u1 u2 u2}` — 同态
 在两个资料夹中都有证明，通过重用级别变量表示 — 该区块包含方程 `u0 = u2`，
 将 C 的同态与证明级别与 D 的对应。两个 OBJECT 宇宙保持自由：
 `u` 和 `u1` 仅在界限内出现，不在任何方程中。所以仅查看该区块的读者会看到一个对应，而错过两个；必须都读。这些识别是继承的，并且是通过探针中的隔离实验得出的，而不是通过断言。在声明的 `Constraint ch < dh` 下，函子范畴 `@Fun Cu Du` 被拒绝，并显示“无法强制 dh = ch”，而 `x ~{Cu}~> y` 和 `a ~{Du}~> b` 在同一层次上均被接受：[Fun] 在一个同态与证明层级上接受这两个范畴，这也是 `u0 = u2` 和每个绑定器同态=证明的一半的来源。独立地，在 `Constraint mh < mp` 下，`@Monic Du a b g` 和 `@Epic Du a b g` 都因“无法强制 mp = mh”而被拒绝，而同时存在的两个已接受控制没有问题，因此 Theory/Morphisms.v 的类自行识别同态与证明。这里没有引入任何识别，也不声称它们是不可避免的。在 Sets 中，图在同一级别上是相同的：
 `sets_functor_monic_iff_pointwise` 在 `C : Category@{u u0 u0}` 之上，
 两个函子落在 `Sets@{u0 u1}` 和 `Sets@{u0 u2}`，
 并且该区块添加了 `u0 < u1`、`u0 < u2` 和 `u1 = u2` — Sets 的两个出现被强制为一个实例，这就是 ` [C, Sets]ZZ ` 的含义，并且 Sets 的承载层级是 C 的同态层级，即 `Sets@{o so} : Category@{so o o}` 会议 [Fun]。证人部分包含一个 `Set` 引脚，而一般结果则没有。在绑定器或块中扫描所有 74 个常量以查找字面量标记 `Set`，正好有 20 个包含它：证人部分的 16 个命名常量（TwoOne、TwoBool、TwoTwoX、TwoTwoY、two_pick_nat、two_collapse、two_arrow、pick_true_Monic、collapse_Epic 及其七个相关结果）以及它们的四个义务（two_pick_nat_obligation_1/2、two_collapse_obligation_1/2）。原因在于 [_2] 本身：`_2@{u u0} : Category@{u Set Set}`，因为 Instance/Two.v 声明了 `TwoHom : TwoObj → TwoObj → Set`，并且 [Fun] 随后强制目标的同态和证明级别匹配，因此 ` [_2, Sets]ZZ ` 是 `Sets@{Set _}`。A-D 部分不受其影响。这是继承来的，是在树中使用最便宜的非平凡形状所付出的代价，并且并未声称是不可避免的。工程发现

 1. 一个 [Program Definition] 的 Sets-态射，在实例解析时会保留 `proper_morphism`，可以将承载宇宙固定到 `Set`。因此，这两个新的函子都通过手动提供其箭头作用的恭敬性证书——[ker_fun_proper] 和 [ck_fun_proper] 是普通引理，[ker_map] / [ck_map] 是记录字面量——并且上述测量确认 A-D 部分未获取任何 `Set`。

 2. 在此文件顶部尝试了 `Set Transparent Obligations`，但不需要：两个 [eq_refl] 与 [Functor_Setoid_Nat_Iso] 的比较在仓库的普通不透明义务下仍然成立，因为 [nat_inverse] 直接提供了其 `transform` 字段，只有其两个自然性字段成为义务。在测量后，该行已被移除。3. [Constant_Functor] 已经存在（Instance/Fun/Terminal.v），并且不会被重用：引用该模块会使这个文件的传递闭包从 39 个模块增加到 74 个模块（通过追踪每一条 Require 行直到固定点来测量），这对每一个下游使用这个文件的用户来说都是很高的代价，而这个文件的全部目的是为了被引用。相反，声明了一个五行的本地见证 [const_fun]，并在这里记录重复，而不是隐藏起来。

 4. 在 Sets 内应用 [fmap_respects]、[fmap_id] 和 [fmap_comp] 需要逐点（pointwise）的解读：`fmap [F]ZZ  f ≈ fmap [F]ZZ  g` 展开为 `∀ a, ...`，所以 `apply fmap_id` 不匹配，字段必须作为一个项（`exact (@fmap_id _ _ F _ _)`）来应用。5.  ` [C, D]ZZ ` 的身份具有组件 `fmap [G]ZZ  id`，而不是 `id`（Theory/Natural/Transformation.v），因此 [componentwise_iso] 和 [nat_iso_pointwise] 的两个逆律各自消耗一个 `fmap_id` 步；该残余是 (C) 节中唯一的摩擦源。6.  通过检查此文件引入的每个名称发现了名称冲突，并在落地前已重命名：[two_pick] 已被 Instance/Fun/Terminal.v 占用，并且由于 print-assumptions 目标将多个模块加载到一个作用域中，共享名称可能会审查到错误的常量。这里的证据是 [two_pick_nat]。整个文件及其探针引入的 95 个名称——52 个声明头，22 个 [Program] 义务，以及探针的 12 个已声明和 9 个被拒绝的名称——冲突数为零；该检查已在 [Monic] 和 [Full] 上进行工具验证，它们必须碰撞并且确实碰撞。

 非空性[two_pick_nat] 在 ` [_2, Sets]ZZ ` 中是单射，并且可以证明在那里不是满射，而 [two_collapse] 是满射，并且可以证明不是单射——每个反驳都通过 CONVERSE 部分，因此（B）节被执行而不仅仅是陈述，并且在命名的分量 [TwoX] 上展示了逐点阻碍：[two_pick_component_not_surjective] 通过 `discriminate` 在双元素集合上的 `true = false` 上完成。一般方向在一个不是 Sets 的目标上被 [two_arrow_Monic] 和 [two_arrow_Epic] 在 ` [_2, _2]ZZ ` 上执行，在 Instance/Two.v 的 [TwoXY_monic] / [TwoXY_epic] 上。退化，被标记为：所有三个见证变换（[two_pick_nat]、[two_collapse]、[two_arrow]）都在常量函子之间运行，因此它们的自然性方格简化为`θ_x ≈ θ_y`，并且这些见证主要运用的是同态集合与消去论证，而不是自然性；且` [_2, _2]ZZ `具有稀薄的同态集合。它们的用途是消去内容，并且确实起到了这种作用。

 未交付没有在一般目标上进行逆向，也没有分离示例来反驳一个——见上面的《单态性判定》。函子范畴的拉回现在是 Instance/Fun/Pullback.v 的 [Fun_HasPullbacks]，而推挤仍然没有；这里的两个函子不受此影响——它们仍然是带有它们的腿的逐点（余）极对象，并且在 ` [C, Sets]ZZ ` 中没有声称任何泛性质。没有将 [KerPair] 与 [Structure/Regular.v] 的泛 [kernel_pair] 在上一层次的一一对应，也没有将 [CokerPair] 和 [Theory/Morphisms/CokernelPair.v] 的 [cokernel_pair] 做出对应。没有声明 [KerPair] 或 [CokerPair] 在 θ 中是函子性的。没有 Yoneda 或可表示性路径，也没有与其中之一进行比较。预层的子对象分类器现在是 Instance/Fun/Classifier.v 的 [Fun_Classifier]，它在三个位置引用了 (D) — 中介的尊重性，其自然性以及唯一性条款 — 并且在重新注释的 [Fun_Classifier_small] 中有第四处；但预层仍然没有子对象格。关于分裂单态、分裂满态、正规或有效的满态，或 ` [C, D]ZZ ` 的平衡性没有任何信息。除了 [_2] 之外没有任何形状的见证，也没有非恒等函子（non-constant functor）的见证。
*)

(* ------------------------------------------------------------------ *)
(* * ** (A) An arbitrary target: componentwise monic/epic suffices / * **（A）任意目标：分量上的单射/满射即可 *)

Section General.

Context {C : Category}.
Context {D : Category}.
Context {F : C ⟶ D}.
Context {G : C ⟶ D}.
Context (θ : F ⟹ G).

Theorem pointwise_monic_is_monic :
  (∀ x : C, Monic (transform[θ] x)) → @Monic ([C, D]) F G θ.
Proof.
  intros H.
  constructor; intros K g1 g2 Heq x.
  apply (@monic _ _ _ _ (H x) (K x)).
  exact (Heq x).
Defined.

Theorem pointwise_epic_is_epic :
  (∀ x : C, Epic (transform[θ] x)) → @Epic ([C, D]) F G θ.
Proof.
  intros H.
  constructor; intros K g1 g2 Heq x.
  apply (@epic _ _ _ _ (H x) (K x)).
  exact (Heq x).
Defined.

End General.

(* ------------------------------------------------------------------ *)
(* * ** (B) The target Sets: the biconditionals, by pointwise (co)limits / * ** (B) 目标集合：按逐点（余）极限的双条件语句 *)

Section SetsConverse.

Context {C : Category}.
Context {F : C ⟶ Sets}.
Context {G : C ⟶ Sets}.
Context (θ : F ⟹ G).

(* * ** The pointwise kernel-pair functor / * ** 点对点核对偶函子 *)

Lemma theta_nat {x y : C} (f : x ~{C}~> y) (a : carrier (F x)) :
  transform[θ] y (fmap[F] f a) ≈ fmap[G] f (transform[θ] x a).
Proof. exact (naturality_sym θ x y f a). Qed.

Lemma ker_map_ok {x y : C} (f : x ~{C}~> y)
      (u : carrier (sets_ker (transform[θ] x))) :
  transform[θ] y (fmap[F] f (fst `1 u))
    ≈ transform[θ] y (fmap[F] f (snd `1 u)).
Proof.
  transitivity (fmap[G] f (transform[θ] x (fst `1 u))).
  - apply theta_nat.
  - transitivity (fmap[G] f (transform[θ] x (snd `1 u))).
    + apply proper_morphism; exact (`2 u).
    + symmetry; apply theta_nat.
Qed.

Definition ker_fun {x y : C} (f : x ~{C}~> y)
  (u : carrier (sets_ker (transform[θ] x))) :
  carrier (sets_ker (transform[θ] y)) :=
  ((fmap[F] f (fst `1 u), fmap[F] f (snd `1 u)); ker_map_ok f u).

Lemma ker_fun_proper {x y : C} (f : x ~{C}~> y) :
  Proper (equiv ==> equiv) (ker_fun f).
Proof.
  intros u v H; destruct H as [H1 H2].
  split; simpl; now apply proper_morphism.
Qed.

Definition ker_map {x y : C} (f : x ~{C}~> y) :
  sets_ker (transform[θ] x) ~{Sets}~> sets_ker (transform[θ] y) :=
  {| morphism := ker_fun f; proper_morphism := ker_fun_proper f |}.

Program Definition KerPair : C ⟶ Sets := {|
  fobj := fun x => sets_ker (transform[θ] x);
  fmap := fun x y f => ker_map f
|}.
Next Obligation.
  proper; split; simpl;
    exact (@fmap_respects _ _ F _ _ _ _ X _).
Qed.
Next Obligation. split; simpl; exact (@fmap_id _ _ F _ _). Qed.
Next Obligation. split; simpl; exact (@fmap_comp _ _ F _ _ _ _ _ _). Qed.

Program Definition KerFst : KerPair ⟹ F := {|
  transform := fun x => sets_ker_fst (transform[θ] x)
|}.

Program Definition KerSnd : KerPair ⟹ F := {|
  transform := fun x => sets_ker_snd (transform[θ] x)
|}.

Lemma ker_agree : θ ∙ KerFst ≈[Fun] θ ∙ KerSnd.
Proof. intros x u; exact (`2 u). Qed.

Theorem sets_functor_monic_pointwise :
  @Monic ([C, Sets]) F G θ → ∀ x : C, Monic (transform[θ] x).
Proof.
  intros Hm x.
  apply (fst (injectivity_is_monic (transform[θ] x))).
  intros a b Hab.
  exact (@monic _ _ _ _ Hm KerPair KerFst KerSnd ker_agree x
                (sets_ker_pair (transform[θ] x) a b Hab)).
Defined.

Theorem sets_functor_monic_iff_pointwise :
  @Monic ([C, Sets]) F G θ  ↔  (∀ x : C, Monic (transform[θ] x)).
Proof.
  split.
  - exact sets_functor_monic_pointwise.
  - exact (pointwise_monic_is_monic θ).
Defined.

(* * ** The pointwise cokernel-pair functor / * ** 点态余核对偶函子 *)

Lemma ck_Im_map {x y : C} (f : x ~{C}~> y) (b : carrier (G x)) :
  Im (transform[θ] x) b → Im (transform[θ] y) (fmap[G] f b).
Proof.
  intros [z Hz]; exists (fmap[F] f z).
  transitivity (fmap[G] f (transform[θ] x z)).
  - apply theta_nat.
  - now apply proper_morphism.
Defined.

Definition ck_fun {x y : C} (f : x ~{C}~> y)
  (u : carrier (CKSetoid (transform[θ] x))) :
  carrier (CKSetoid (transform[θ] y)) :=
  match u with
  | Datatypes.inl b => Datatypes.inl (fmap[G] f b)
  | Datatypes.inr b => Datatypes.inr (fmap[G] f b)
  end.

Lemma ck_fun_proper {x y : C} (f : x ~{C}~> y) :
  Proper (equiv ==> equiv) (ck_fun f).
Proof.
  intros u v H; destruct u, v; simpl in *;
    try (now apply proper_morphism);
    destruct H as [H1 H2]; split;
    [ now apply proper_morphism | now apply ck_Im_map
    | now apply proper_morphism | now apply ck_Im_map ].
Qed.

Definition ck_map {x y : C} (f : x ~{C}~> y) :
  CKSetoid (transform[θ] x) ~{Sets}~> CKSetoid (transform[θ] y) :=
  {| morphism := ck_fun f; proper_morphism := ck_fun_proper f |}.

Program Definition CokerPair : C ⟶ Sets := {|
  fobj := fun x => CKSetoid (transform[θ] x);
  fmap := fun x y f => ck_map f
|}.
Next Obligation.
  proper; destruct x1; simpl;
    exact (@fmap_respects _ _ G _ _ _ _ X _).
Qed.
Next Obligation.
  destruct x0; simpl; exact (@fmap_id _ _ G _ _).
Qed.
Next Obligation.
  destruct x0; simpl; exact (@fmap_comp _ _ G _ _ _ _ _ _).
Qed.

Program Definition CkLeft : G ⟹ CokerPair := {|
  transform := fun x => ck_left (transform[θ] x)
|}.

Program Definition CkRight : G ⟹ CokerPair := {|
  transform := fun x => ck_right (transform[θ] x)
|}.

Lemma ck_agree_nat : CkLeft ∙ θ ≈[Fun] CkRight ∙ θ.
Proof. intros x a; exact (ck_agree (transform[θ] x) a). Qed.

Theorem sets_functor_epic_pointwise :
  @Epic ([C, Sets]) F G θ → ∀ x : C, Epic (transform[θ] x).
Proof.
  intros He x.
  apply (fst (surjectivity_is_epic (transform[θ] x))).
  intros b.
  exact (snd (@epic _ _ _ _ He CokerPair CkLeft CkRight ck_agree_nat x b)).
Defined.

Theorem sets_functor_epic_iff_pointwise :
  @Epic ([C, Sets]) F G θ  ↔  (∀ x : C, Epic (transform[θ] x)).
Proof.
  split.
  - exact sets_functor_epic_pointwise.
  - exact (pointwise_epic_is_epic θ).
Defined.

End SetsConverse.

(* ------------------------------------------------------------------ *)
(* * ** (C) Awodey §7.10 Ex 6: invertibility of a GIVEN transformation / * ** (C) Awodey §7.10 例 6：给定变换的可逆性 *)

Section Invertibility.

Context {C : Category}.
Context {D : Category}.
Context {F : C ⟶ D}.
Context {G : C ⟶ D}.
Context (θ : F ⟹ G).

Lemma nat_inv_natural (H : ∀ x : C, IsIsomorphism (transform[θ] x))
      {x y : C} (f : x ~{C}~> y) :
  fmap[F] f ∘ @two_sided_inverse _ _ _ _ (H x)
    ≈ @two_sided_inverse _ _ _ _ (H y) ∘ fmap[G] f.
Proof.
  rewrite <- (id_left (fmap[F] f ∘ _)).
  rewrite <- (@is_left_inverse _ _ _ _ (H y)).
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  rewrite comp_assoc.
  rewrite <- naturality.
  rewrite <- comp_assoc.
  rewrite (@is_right_inverse _ _ _ _ (H x)).
  now rewrite id_right.
Qed.

Program Definition nat_inverse
  (H : ∀ x : C, IsIsomorphism (transform[θ] x)) : G ⟹ F := {|
  transform := fun x => @two_sided_inverse _ _ _ _ (H x)
|}.
Next Obligation. now rewrite nat_inv_natural. Qed.
Next Obligation. now rewrite nat_inv_natural. Qed.

Definition componentwise_iso
  (H : ∀ x : C, IsIsomorphism (transform[θ] x)) :
  @IsIsomorphism ([C, D]) F G θ.
Proof.
  refine (@Build_IsIsomorphism ([C, D]) F G θ (nat_inverse H) _ _);
    intro x; simpl.
  - rewrite (@is_right_inverse _ _ _ _ (H x)).
    now rewrite fmap_id.
  - rewrite (@is_left_inverse _ _ _ _ (H x)).
    now rewrite fmap_id.
Defined.

Definition nat_iso_pointwise (H : @IsIsomorphism ([C, D]) F G θ) (x : C) :
  IsIsomorphism (transform[θ] x).
Proof.
  refine {| two_sided_inverse :=
              transform[@two_sided_inverse _ _ _ _ H] x |}.
  - etransitivity; [ exact (@is_right_inverse _ _ _ _ H x) | ].
    simpl; apply fmap_id.
  - etransitivity; [ exact (@is_left_inverse _ _ _ _ H x) | ].
    simpl; apply fmap_id.
Defined.

Theorem nat_iso_iff_pointwise :
  @IsIsomorphism ([C, D]) F G θ  ↔  (∀ x : C, IsIsomorphism (transform[θ] x)).
Proof.
  split.
  - exact nat_iso_pointwise.
  - exact componentwise_iso.
Defined.

End Invertibility.

(* ------------------------------------------------------------------ *)
(* * ** (C, continued) Comparison with [Functor_Setoid_Nat_Iso] / * **（C，续）与 [Functor_Setoid_Nat_Iso] 的比较 *)

Section EquivComparison.

Context {C : Category}.
Context {D : Category}.
Context {F : C ⟶ D}.
Context {G : C ⟶ D}.
Context (θ : F ⟹ G).

Definition nat_iso_family
  (H : ∀ x : C, IsIsomorphism (transform[θ] x)) : F ≈ G.
Proof.
  simpl.
  exists (fun x => @IsIsoToIso D (F x) (G x) (transform[θ] x) (H x)).
  intros x y f; simpl.
  symmetry.
  rewrite <- comp_assoc.
  rewrite naturality.
  rewrite comp_assoc.
  rewrite (@is_left_inverse _ _ _ _ (H y)).
  now rewrite id_left.
Defined.

Example equiv_iso_to_is_theta
  (H : ∀ x : C, IsIsomorphism (transform[θ] x)) (x : C) :
  transform[to (equiv_iso (nat_iso_family H))] x = transform[θ] x
  := eq_refl.

Example equiv_iso_from_is_nat_inverse
  (H : ∀ x : C, IsIsomorphism (transform[θ] x)) (x : C) :
  transform[from (equiv_iso (nat_iso_family H))] x
    = transform[nat_inverse θ H] x := eq_refl.

End EquivComparison.

(* ------------------------------------------------------------------ *)
(* * ** (D) Presheaves: monos are the pointwise injections / * **（D）预层：单态是逐点注入 *)

Section Presheaf.

Context {C : Category}.
Context {P : C^op ⟶ Sets}.
Context {Q : C^op ⟶ Sets}.
Context (θ : P ⟹ Q).

Definition presheaf_monic_iff_pointwise :
  @Monic ([C^op, Sets]) P Q θ  ↔  (∀ x : C^op, Monic (transform[θ] x))
  := sets_functor_monic_iff_pointwise θ.

Definition presheaf_epic_iff_pointwise :
  @Epic ([C^op, Sets]) P Q θ  ↔  (∀ x : C^op, Epic (transform[θ] x))
  := sets_functor_epic_iff_pointwise θ.

Theorem presheaf_monic_iff_injective :
  @Monic ([C^op, Sets]) P Q θ  ↔
  (∀ (x : C^op) (a b : carrier (P x)),
      transform[θ] x a ≈ transform[θ] x b → a ≈ b).
Proof.
  split.
  - intros Hm x.
    exact (snd (injectivity_is_monic (transform[θ] x))
               (sets_functor_monic_pointwise θ Hm x)).
  - intros Hi.
    apply (pointwise_monic_is_monic θ); intros x.
    exact (fst (injectivity_is_monic (transform[θ] x)) (Hi x)).
Defined.

Theorem presheaf_epic_iff_surjective :
  @Epic ([C^op, Sets]) P Q θ  ↔
  (∀ (x : C^op) (b : carrier (Q x)), ∃ a, transform[θ] x a ≈ b)%type.
Proof.
  split.
  - intros He x.
    exact (epic_implies_surjective (transform[θ] x)
             (sets_functor_epic_pointwise θ He x)).
  - intros Hs.
    apply (pointwise_epic_is_epic θ); intros x.
    exact (surjective_implies_epic (transform[θ] x) (Hs x)).
Defined.

End Presheaf.

(* ------------------------------------------------------------------ *)
(** ** Non-vacuity / ** 非空性 *)

Section Witnesses.

Definition const_fun@{co ch cp dro dh dp}
  {C : Category@{co ch cp}} {D : Category@{dro dh dp}} (d : D) : C ⟶ D :=
  {| fobj          := fun _ => d
   ; fmap          := fun _ _ _ => id
   ; fmap_respects := fun _ _ _ _ _ => reflexivity _
   ; fmap_id       := fun _ => reflexivity _
   ; fmap_comp     := fun _ _ _ _ _ => symmetry (id_left id) |}.

Definition TwoOne : _2 ⟶ Sets :=
  @const_fun _2 Sets unit_setoid_object.
Definition TwoBool : _2 ⟶ Sets :=
  @const_fun _2 Sets bool_setoid_object.

Program Definition two_pick_nat : TwoOne ⟹ TwoBool := {|
  transform := fun _ => pick_true
|}.

Program Definition two_collapse : TwoBool ⟹ TwoOne := {|
  transform := fun _ => collapse
|}.

Lemma pick_true_Monic : @Monic Sets _ _ pick_true.
Proof.
  apply (fst (injectivity_is_monic pick_true)).
  intros a b _; destruct a, b; reflexivity.
Defined.

Lemma collapse_Epic : @Epic Sets _ _ collapse.
Proof.
  apply (fst (surjectivity_is_epic collapse)).
  intros b; exists true; destruct b; reflexivity.
Defined.

Definition two_pick_Monic : @Monic ([_2, Sets]) TwoOne TwoBool two_pick_nat :=
  pointwise_monic_is_monic two_pick_nat (fun _ => pick_true_Monic).

Definition two_collapse_Epic :
  @Epic ([_2, Sets]) TwoBool TwoOne two_collapse :=
  pointwise_epic_is_epic two_collapse (fun _ => collapse_Epic).

Lemma two_pick_component_not_surjective :
  (∀ b : carrier bool_setoid_object,
      ∃ a, transform[two_pick_nat] TwoX a ≈ b)%type → False.
Proof.
  intros Hs; destruct (Hs false) as [a Ha]; simpl in Ha; discriminate.
Qed.

Lemma two_pick_not_Epic :
  @Epic ([_2, Sets]) TwoOne TwoBool two_pick_nat → False.
Proof.
  intros He.
  apply two_pick_component_not_surjective.
  exact (epic_implies_surjective (transform[two_pick_nat] TwoX)
           (sets_functor_epic_pointwise two_pick_nat He TwoX)).
Qed.

Lemma two_collapse_not_Monic :
  @Monic ([_2, Sets]) TwoBool TwoOne two_collapse → False.
Proof.
  intros Hm.
  apply collapse_not_monic.
  exact (sets_functor_monic_pointwise two_collapse Hm TwoX).
Qed.

Definition TwoTwoX : _2 ⟶ _2 := @const_fun _2 _2 TwoX.
Definition TwoTwoY : _2 ⟶ _2 := @const_fun _2 _2 TwoY.

Program Definition two_arrow : TwoTwoX ⟹ TwoTwoY := {|
  transform := fun _ => TwoXY
|}.

Definition two_arrow_Monic :
  @Monic ([_2, _2]) TwoTwoX TwoTwoY two_arrow :=
  pointwise_monic_is_monic two_arrow (fun _ => TwoXY_monic).

Definition two_arrow_Epic :
  @Epic ([_2, _2]) TwoTwoX TwoTwoY two_arrow :=
  pointwise_epic_is_epic two_arrow (fun _ => TwoXY_epic).

End Witnesses.
