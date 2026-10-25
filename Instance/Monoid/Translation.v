(* * * Translation endofunctors of a monoid, and their adjoints / * * 单体的平移终函子及其伴函子 *)

From Coq Require Import Eqdep_dec.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Product.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Discrete.
Require Import Category.Construction.Comma.Special.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.

Generalizable All Variables.

(*
 nLab:      https://ncatlab.org/nlab/show/delooping
 nLab:      https://ncatlab.org/nlab/show/adjoint+functor
 nLab:      https://ncatlab.org/nlab/show/discrete+category
 nLab:      https://ncatlab.org/nlab/show/monoid
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 GTM 5, §IV.2, printed p. 90, Exercise 5

 THE EXERCISE.  Mac Lane's §IV.2 exercise regards a monoid M as a DISCRETE
 category — elements as OBJECTS, no non-identity arrows — and its
 multiplication as a bifunctor on that category.  The two partial
 applications of that bifunctor are the left and right translation
 endofunctors, x ↦ a·x and x ↦ x·a.  When M is a group, inversion supplies
 a right adjoint for each: translation by a⁻¹.  The exercise then asks
 whether the CONVERSE holds — whether a monoid all of whose translations
 have right adjoints must be a group.  (The wording of the exercise is
 taken from the catalogued item that commissioned this file rather than
 read off the page; the mathematics below stands on its own.)

 The converse DOES hold, and it is the substance of this file.  An
 adjunction L_a ⊣ R supplies, for every x and y, an INVERSE TRANSPOSE
 carrying hom(x, R y) to hom(a·x, y); in a discrete category those hom-sets
 are the identifications between a·x and y, and between x and R y.  Feeding
 the identity of R(1) to it at x := R 1, y := 1 yields a · R(1) ≈ 1 — a
 Leibniz `=` in the strict reading — so every element of M has a RIGHT
 inverse; and a monoid in which every element has a right inverse is a
 group.  That last step is [MonInverses_of_right_inverses] below, and it is
 reusable on its own.  Note how little of the adjunction is consumed: only
 the backward leg, at one pair of objects, applied to one identity.

 ** THE FORK: WHICH DISCRETE CATEGORY?

 "The discrete category on M" has two readings in a setoid library, and
 they are not interchangeable.  This file delivers BOTH and measures the
 difference rather than choosing silently.

 (a) [MonDiscrete M] — objects the carrier of M, a morphism x ~> y being a
 proof of the monoid's own `≈`.  This is Construction/Comma/Special.v's
 [DiscreteSetoidCat], reused rather than rebuilt, and it is the reading
 that file argues for at length in its header: in a setoid library
 the identifications available between two elements are the inhabitants
 of `≈`, not of Rocq's `=`.  Over this category the development carries
 NO hypothesis on M beyond its being a monoid —
 [mon_group_iff_left_translation_adjoints] holds for an ARBITRARY
 [MonObject].

 (b) [MonDiscreteStrict M] — Instance/Discrete.v's [DiscreteCat] on the
 carrier, whose homs are proofs of Rocq's `=`.  This is the literal
 reading of "the category really is discrete (homs are equalities)".
 Over it the CONVERSE is still hypothesis-free
 ([strict_left_translation_adjoints_MonInverses]), because a Leibniz
 equality yields an `≈`; but the FORWARD direction is not, and the
 obstruction is exactly the one Construction/Comma/Special.v names.
 Building the transpose of a·x = y needs a⁻¹·(a·x) = x at LEIBNIZ
 equality, whereas the inverse laws give only `≈`.  The probe
 [probe_cancel_strict] pins that: [mon_inv_cancel_l] does not TYPE as
 the Leibniz statement, against the passing control [ctrl_cancel_equiv]
 at `≈`.  Read that probe precisely — it says conversion rejects the
 ascription at a VARIABLE monoid, NOT that no proof of the Leibniz form
 exists; for a monoid whose `≈` is `=` there of course is one, and
 [strict_cancel_l] instantiated at [Z3_MonStrict] is such a proof.

 So the forward direction is delivered under two explicit hypotheses,
 [MonStrict M] (`≈` implies `=`) and [MonUIP M] (uniqueness of identity
 proofs on the carrier), following the [HomStrict]/[HomUIP] pattern of
 Construction/Comma/Special.v.  [MonUIP] is needed because
 [DiscreteCat]'s hom-setoid is STRICT equality OF PROOFS, so both
 respectfulness proofs, both isomorphism laws and all four naturality
 clauses of [Adjunction] are equations between equality proofs.  Both
 hypotheses are free for a carrier with decidable equality
 ([MonUIP_dec], Hedberg via the stdlib's axiom-free [UIP_dec]).  THEY
 ARE SUFFICIENT AND ARE NOT SHOWN NECESSARY: no countermodel is offered
 and no forcing theorem is proved in either direction.

 The two categories are NOT convertible ([probe_categories_agree]) though
 they share their object type ([ctrl_objects_agree]); the passage
 [MonStrictToDiscrete] from (b) to (a) is hypothesis-free, while
 [MonDiscreteToStrict] the other way costs exactly [MonStrict] and
 [MonUIP] — the second of them because [fmap_id] there is an equation
 between two proofs of x = x.  No equivalence of categories is claimed.

 ** RELATION TO deloop_groupoid_iff — A DIFFERENT CATEGORIFICATION

 Structure/Groupoid.v proves [deloop_groupoid_iff]: a monoid is a group
 exactly when its DELOOPING is a groupoid.  There the elements of M are the
 ARROWS of a one-object category.  Here they are the OBJECTS of a discrete
 category and the translations are ENDOFUNCTORS.  These are two different
 categorifications of one fact about M, and NEITHER is derived from the
 other below: no theorem below mentions the category [Deloop M], and
 Structure/Groupoid.v is required only for [MonInverses] with its
 accessors and [MonInverses_of], for [nat_plus_no_inverses], and for the
 [Z3] witnesses.  What
 the two share is their conclusion, [MonInverses M], which is deliberately
 NOT redefined here.

 ** WHAT IS DELIVERED

 - [MonDiscrete], the setoid-discrete category on a monoid, with objects
 and homs pinned by [eq_refl] and thinness recorded.
 - [MonMult], multiplication as a genuine BIFUNCTOR on it, and
 [LeftTranslation]/[RightTranslation] as endofunctors.
 - [left_translation_adjunction] : L_a ⊣ L_{a⁻¹} and
 [right_translation_adjunction] : R_a ⊣ R_{a⁻¹}, for an arbitrary monoid
 carrying [MonInverses].
 - [MonInverses_of_right_inverses] and [MonInverses_of_left_inverses]: a
 monoid with all right (resp. left) inverses is a group.
 - The biconditionals [mon_group_iff_left_translation_adjoints] and
 [mon_group_iff_right_translation_adjoints], which answer the exercise's
 question in the affirmative.
 - The LEFT-handed half of that again over [DiscreteCat], as
 [mon_group_iff_left_translation_adjoints_strict].
 - Witnesses: (ℕ, +) with a DIRECT refutation
 ([nat_translation_no_right_adjoint]) as well as the one through the
 biconditional; Z/3, whose inversion moves an element, so the left
 adjoint and the right adjoint are provably different functors.

 ** WHAT IS MEASURED RATHER THAN ASSERTED

 Strengths, tried strict-first:

 eq_refl   objects of [MonDiscrete M] are the carrier
 eq_refl   homs of [MonDiscrete M] are `≈`; of the strict one, `=`
 eq_refl   object types of the two discrete categories agree
 eq_refl   [fobj] and [fmap] of [LeftTranslation M a] and of
 [Partial_r (MonMult M) a] — BOTH data fields, so the
 translations ARE partial applications of the bifunctor on
 everything a consumer can observe
 eq_refl   likewise [RightTranslation] against [Partial_l]
 eq_refl   both comparison functors are the identity on objects
 eq_refl   the Z/3 and Z/2 computations
 REFUTED   the WHOLE-RECORD equality [LeftTranslation M a =
 Partial_r (MonMult M) a] ([probe_partial_record]).  [Functor]
 has primitive projections WITH eta, so record equality IS
 field equality; two of its five fields agree by [eq_refl] as
 above, and the remaining three are law fields built as
 separate opaque [Program] obligations on the two sides.  That
 localises the difference to those three.
 REFUTED   [MonDiscrete M = MonDiscreteStrict M]
 REFUTED   the homs of [MonDiscrete M] at a VARIABLE M are Rocq's `=`
 (they are at Z/3, whose `≈` IS `=`, which is why the probe is
 stated at a variable)
 REFUTED   the `≈`-cancellation law read as a Leibniz equation

 Which route was taken for the translations, and why: reading them off the
 bifunctor is CHEAPER — [Partial_r]/[Partial_l] discharge their three
 functor laws once and for all in Functor/Bifunctor/Partial.v, so the
 definition would cost no obligation at all, whereas the direct records
 below cost three apiece (each closed by [exact I], the hom-setoid of a
 thin category being trivially true).  The direct records are nevertheless
 what is shipped, so that the arrow action is legible in the source and so
 that Mac Lane's identification of the translations with the partial
 functors becomes a MEASURED fact rather than a definition; the four
 [*_partial_*] Examples in Block B are that measurement.

 Universes, read off BOTH the binder and the constraint block:

 [mon_group_iff_left_translation_adjoints@{u u0 u1 u2 u3 u4}] carries NO
 universe equation at all, and no `Set`; the monoid's three universes are
 only bounded.

 [MonDiscrete@{u u0 u1} : MonObject@{u u0 u1} -> Category@{u u0 u0}]
 IDENTIFIES the hom and proof universes — and the identification is in
 the BINDER while the block holds only two bounds, so reading the block
 alone gets it wrong.  It is INHERITED: [DiscreteSetoidCat@{u u0}] is
 declared with two universes and returns [Category@{u u0 u0}], its own
 constraint block being empty.  Nothing here adds to it and no repair is
 attempted (that file is not this file's to edit); it is NOT claimed
 unavoidable.

 [MonDiscreteStrict] carries explicit binders, and they are
 LOAD-BEARING: written unannotated, the same body minimizes so as to
 identify the hom and proof universes, whereas the annotated form leaves
 only the bound h <= p — [DiscreteCat@{o h p}] being properly annotated
 at its own declaration.  (Measured by compiling the same body twice,
 with and without binders; that measurement is NOT guarded in this
 file.)  But read what it buys: DOWNSTREAM the two levels minimize to
 the literal Set anyway — [LeftTranslationStrict] lands at
 Functor@{u Set Set u Set Set} — so the annotation buys freedom at
 [MonDiscreteStrict] itself and none at the strict headline.

 The strict headline's block contains `Set < _`, on an INTERNAL universe:
 [DiscreteCat]'s homs are Rocq's `eq`, hence `Prop`-valued, so the
 auxiliary [Sets] in which [Adjunction] states its hom-isomorphism
 minimizes its carrier universe to `Set`.  It does NOT restrict the
 monoid, and that is guarded rather than merely observed — the probe
 section at the end declares all three of a monoid's universes strictly
 above `Set` and both headlines still elaborate there.

 [DiscreteCat_Functor] is NOT used anywhere below; the functors out of
 the strict category are hand-written records instead.  RECORDED
 CORRECTION: an earlier revision gave the reason as "(Instance/
 Discrete.v) it is unannotated and pins its source at
 [DiscreteCat@{u Set Set}]".  That held when written and does not now —
 the donor was annotated in place at Instance/Discrete.v in the PR
 "algebraic carriers are sets" (2026-09-17) and pins nothing.  The
 hand-written records are kept, and no re-measurement was made of
 whether the donor would now serve, since nothing here consumes it.

 ** AUDIT

 104/104 constants closed under the global context — 66 source-declared
 heads plus 38 [Program] obligations that no source sweep sees, each
 queried by its fully qualified name.  The two enumerations reconcile
 exactly: nothing [Print Module] lists is missing from the source heads and
 nothing among the source heads is missing from [Print Module].  The file
 declares no [Record], [Class] or [Inductive], so there is no unlisted
 [Build_*].  Read the GRADE: that is a ONE-TIME measurement of all 104,
 not a standing gate.  The only stdlib import is [Eqdep_dec], for
 [UIP_dec], which is Hedberg's argument and carries no axiom.

 Name collisions were swept two ways over all 71 identifiers this file
 introduces (the 66 declared heads plus the 5 probe names, which declare
 nothing): by declaration head with the repository's usual regex, and — the
 stronger criterion — by WHOLE-WORD token occurrence ANYWHERE in ANY `.v`
 file of the worktree, this file excluded.  Zero hits under either
 criterion, at the revision this file was written against (reported as
 master e3ab9d22).  There are no record fields to sweep separately, no
 record being declared — which matters, since a record field is a global
 constant that a declaration-head sweep cannot see.

 Two names in the tree are near neighbours and are deliberately NOT
 shadowed, both verified at the lines given: [translation_functor]
 (Construction/Deloop/Functors.v) is a functor
 [Proset Z.le_preorder ⟶ Deloop Int_Plus] out of Awodey's cocycle
 construction, not a translation endofunctor; and [grp_translate]
 (Instance/Grp/Epi.v) is left translation as a setoid MAP on a coset
 space, not a functor at all.

 [make todo] grows by the five [Fail] lines below and by nothing else: no
 TODO, FIXME or jww is added.

 ** ENGINEERING FINDINGS

 Do not name a local variable [I] in a file whose obligation tactic is
 [exact I].  Measured both ways in this file's development: an obligation
 tactic set at top level still resolved [I] to [Logic.I] inside a section
 binding [I : MonInverses M], but the SAME tactic set INSIDE such a section
 resolved it to the section variable and every obligation failed with "the
 term I has type MonInverses M".  Every inverse witness below is therefore
 named [Inv].

 [Structure/Groupoid.v]'s [MonInverses] destructures as [minv]/[minv_l]/
 [minv_r]; [Construction/Deloop.v]'s [mon_inverse_unique] is what makes
 [MonInverses_of_right_inverses] two lines rather than a chase.

 ** NOT DELIVERED

 - No equivalence, and no isomorphism, between [MonDiscrete M] and
 [MonDiscreteStrict M] under any hypothesis; only the two comparison
 functors, and only their object actions are related.
 - No necessity result for [MonStrict] or [MonUIP], in either direction.
 - No strict-category analogue of [RightTranslation], hence no strict
 right-translation adjunction and no strict right-handed biconditional.
 - No unit or counit is named, and no triangle identity is stated; the
 adjunctions are delivered in the hom-set presentation only.  Over
 [MonDiscrete M] that costs little — the category is thin, so every
 component of a unit or counit is determined up to `≈` by its endpoints —
 but over [MonDiscreteStrict M] it is a genuine omission, that category
 being thin only under [MonUIP].
 - Nothing relates this to [deloop_groupoid_iff] beyond sharing
 [MonInverses]; in particular no functor between [Deloop M] and
 [MonDiscrete M] is built.
 - Nothing is said about monoid HOMOMORPHISMS, so there is no functor
 M ↦ [MonDiscrete M] and no naturality of any identification in M.
 - No [Instance] is registered: nothing here is meant for resolution.
 - The monoid record used is Construction/Deloop.v's [MonObject].  The tree
 carries several other notions of monoid (Structure/Monoid.v's
 [MonoidObject] over a monoidal base, Theory/Coq/Monoid.v's laws-free
 class, Instance/CMon.v's commutative [CMonObject], among others); none
 is related to this development here. 

 --------
 nLab:       https://ncatlab.org/nlab/show/delooping 
 nLab:       https://ncatlab.org/nlab/show/adjoint+functor 
 nLab:       https://ncatlab.org/nlab/show/discrete+category 
 nLab:       https://ncatlab.org/nlab/show/monoid 
 书籍:      Mac Lane, 《工作数学家的范畴论》，第2版，
 GTM 5，第IV.2节，印刷第90页，练习5练习. Mac Lane 的 §IV.2 练习将一个幺半群 M 看作一个离散类别——元素作为对象，没有非恒等箭头——并把它的乘法看作该类别上的双函子。该双函子的两个偏应用分别是左平移和右平移函子，x ↦ a·x 和 x ↦ x·a。当 M 是群时，取逆运算为每个平移提供右伴随：由 a⁻¹ 平移。然后练习询问反向是否成立——一个幺半群所有平移都有右伴随是否必定是群。（练习的措辞取自委托此文件的目录项目，而不是从书页上抄录；下面的数学内容可独立理解。）逆命题确实成立，这也是本文件的实质内容。一个伴随 L_a ⊣ R 对于每个 x 和 y 提供了一个逆转置（INVERSE TRANSPOSE），将 hom(x, R y) 映射到 hom(a·x, y)；在离散范畴中，这些同态集合是 a·x 与 y 以及 x 与 R y 之间的对应。在 x := R 1, y := 1 时，将 R(1) 的恒等映射喂入它，会得到 a · R(1) ≈ 1 —— 在严格理解下是一个 Leibniz `=` ——所以 M 中的每个元素都有右逆；而每个元素都有右逆的幺半群就是一个群。最后一步在下面的 [MonInverses_of_right_inverses] 中，它可以单独重复使用。注意到伴随被使用得很少：只使用了逆向分支，在一对对象上，并应用到一个恒等映射。

 ** 分叉：是哪个离散范畴？“M上的离散范畴”在集合等价库中有两种解读，并且它们不可互换。该文件提供了两种解读，并测量它们之间的差异，而不是默默地选择其中一种。

 (a)  [MonDiscrete M]  — 对象是M的承载者，态射 x ~> y 是该幺半群自身 `≈` 的一个证明。这是 Construction/Comma/Special.v 中的 [DiscreteSetoidCat] ，重复使用而非重建，该解读是该文件在其标题中详细论证的：在集合等价库中，两个元素之间可用的等同是 `≈` 的成员，而不是 Rocq 的 `=`。在该范畴上，开发对 M 没有额外假设，除了它是一个幺半群 — [mon_group_iff_left_translation_adjoints] 对任意的 [MonObject] 成立。(b) [MonDiscreteStrict M] — Instance/Discrete.v 中关于载体的 [DiscreteCat]，其 Hom 是 Rocq 的 `=` 的证明。这是“范畴确实是离散的（Homs 是等式）”的一字面理解。在此之上，CONVERSE 仍然无需假设（[strict_left_translation_adjoints_MonInverses]），因为 Leibniz 等式产生一个 `≈`；但正向方向则不是，阻碍恰好是 Construction/Comma/Special.v 命名的那个。在 LEIBNIZ 等式下，构造 a·x = y 的转置需 a⁻¹·(a·x) = x，而逆律仅给出 `≈`。探针 [probe_cancel_strict] 指出：[mon_inv_cancel_l] 无法作为 Leibniz 语句进行 TYPE，与 `≈` 上的控制传递 [ctrl_cancel_equiv] 相反。精确地阅读那个探针——它表示转换在一个变量幺半群上拒绝归属，并不是说不存在莱布尼兹形式的证明；对于一个其 `≈` 为 `=` 的幺半群，当然是存在的，并且 [strict_cancel_l] 在 [Z3_MonStrict] 处实例化就是这样一个证明。因此，正向方向是在两个明确的假设下得出的，[MonStrict M]（`≈`蕴含`=`）和[MonUIP M]（载体上同一性的唯一性证明），遵循[HomStrict] / [HomUIP]的Construction/Comma/Special.v模式。需要[MonUIP]是因为[DiscreteCat]的hom-setoid是严格等于证明，所以两个尊重性证明、两个同构定律以及[Adjunction]的所有四条自然性条款都是等于证明之间的方程。对于具有可判定等式的载体（[MonUIP_dec]，通过stdlib的无公理[UIP_dec]的Hedberg定理），这两个假设都是自由的。它们是充分的，但未显示必要性：没有提供反例模型，也没有在任一方向中证明强制定理。这两类 **不可以转换**（[probe_categories_agree]），尽管它们共享对象类型（[ctrl_objects_agree]）；从 (b) 到 (a) 的 ZZ28WZZ 过程是无假设的，而反过来恰好需要 ZZ30WZZ 和 ZZ31WZZ —— 第二个是因为 ZZ32WZZ 在 x = x 的两个证明之间存在一个方程。未声明类的等价。

 ** 与 deloop_groupoid_iff 的关系 — 一个不同的类化**Structure/Groupoid.v 证明了 [deloop_groupoid_iff]：一个幺半群当且仅当它的 DELOOPING 是群族时，它才是一个群。在那里，M 的元素是一个单对象范畴的箭头。在这里，它们是离散范畴的对象，而翻译是自函子。这是关于 M 的一个事实的两种不同范畴化方式，并且下面没有一个是从另一个推导出来的：下面没有定理提到范畴 [Deloop M]，而 Structure/Groupoid.v 仅在 [MonInverses] 及其访问器和 [MonInverses_of]、为了 [nat_plus_no_inverses] 以及 [Z3] 的证明见证时需要。它们共有的是它们的结论 [MonInverses M]，在此处故意不重新定义。

 ** 提供内容是什么-  [MonDiscrete]，一个关于幺半群的集合离散范畴，其对象和态射由 [eq_refl] 固定，并记录单薄性。-  [MonMult]，在其上作为真正的双函子（BIFUNCTOR）的乘法，以及 [LeftTranslation] / [RightTranslation] 作为自函子。-  [left_translation_adjunction] ：L_a ⊣ L_{a⁻¹} 和 [right_translation_adjunction] ：R_a ⊣ R_{a⁻¹}，对于携带 [MonInverses] 的任意幺半群。-  [MonInverses_of_right_inverses] 和 [MonInverses_of_left_inverses] ：一个具有所有右（或左）逆元的幺半群是一个群。- 双条件语句 [mon_group_iff_left_translation_adjoints] 和 [mon_group_iff_right_translation_adjoints]，肯定地回答了习题的问题。- 关于 [DiscreteCat] 的左手半部分，再次作为 [mon_group_iff_left_translation_adjoints_strict]。- 证人：（ℕ, +）通过直接反驳 ([nat_translation_no_right_adjoint])，以及通过双条件的反驳；Z/3，其逆运算会移动一个元素，因此左伴随和右伴随被证明是不同的函子。

 ** 测量的内容，而不是断言的内容

 优点，尝试严格优先：eq_refl  [MonDiscrete M] 的对象是承载
 eq_refl  [MonDiscrete M] 的态射是 `≈`；严格的态射是 `=`
 eq_refl  两个离散范畴的对象类型一致
 eq_refl   [fobj] 和 [fmap] 对应于 [LeftTranslation M a] 和 [Partial_r (MonMult M) a] —— 都是数据字段，因此
 翻译是双函子对消费者可观察的一切的偏应用
 eq_refl  同样 [RightTranslation] 与 [Partial_l]
 eq_refl  两个比较函子在对象上都是恒等映射
 eq_refl  Z/3 和 Z/2 的计算
 REFUTED  整条记录的等式 [LeftTranslation M a =
 Partial_r (MonMult M) a] ([probe_partial_record])。[Functor] 具有带 eta 的原始投影，因此记录相等性就是字段相等性；其五个字段中有两个通过如上所述的 [eq_refl] 一致，其余三个是以独立不透明的 [Program] 义务形式在双方构建的法律字段。这将差异局限于这三个字段。反驳 [MonDiscrete M = MonDiscreteStrict M] 反驳 [MonDiscrete M] 在变量 M 上的同态是 Rocq 的 `=`（它们位于 Z/3，其 `≈` 是 `=`，这也是探针在变量上说明的原因）反驳 `≈` 的消元律以莱布尼茨方程的形式读取翻译使用了哪条路线，为什么：从双函子上读出来的翻译成本更低——[Partial_r] / [Partial_l] 在 Functor/Bifunctor/Partial.v 中一次性完成它们的三个函子律，所以该定义几乎不需要任何代价，而下面的直接记录每条都需要三次（每条由 [exact I] 封闭，一个薄范畴的同类集合本身是平凡成立的）。尽管如此，直接记录仍然是最终交付的内容，这样箭头作用在源代码中是可读的，并且使得 Mac Lane 将这些翻译与偏函子对应起来成为一个经过测量的事实，而不仅仅是定义；Block B 中的四个 [*_partial_*] 示例就是这种测量。

 Universe，从绑定器和约束块中都读出：[mon_group_iff_left_translation_adjoints@{u u0 u1 u2 u3 u4}] 完全不包含任何宇宙方程，也没有 `Set`；该幺半群的三个宇宙只是有限界的。

 [MonDiscrete@{u u0 u1} : MonObject@{u u0 u1} -> Category@{u u0 u0}] 识别了 hom 和 proof 宇宙——而识别发生在 BINDER 中，而代码块中只包含两个界限，因此仅读取该代码块会出错。它是继承的：[DiscreteSetoidCat@{u u0}] 用两个宇宙声明并返回 [Category@{u u0 u0}]，其自身的约束块为空。这里没有任何内容可以增加它，也没有进行修复（该文件不是此文件可编辑的）；它并不被认为是不可避免的。[MonDiscreteStrict] 携带显式绑定器，并且它们是承重的：未注释的写法通过最小化主体来识别 hom 和 proof 宇，而带注释的形式只保留绑定的 h <= p — [DiscreteCat@{o h p}] 在其自身声明中被正确注释。（通过编译相同主体两次进行测量，有绑定器和无绑定器；该测量在此文件中未被保护。）但看看它带来的好处：下游两个层级无论如何都会最小化为字面 Set — [LeftTranslationStrict] 最终落在 Functor@{u Set Set u Set Set} — 因此注释在 [MonDiscreteStrict] 本身提供了自由，而在严格的标题处没有提供任何自由。严格的标题块包含 `Set < _`，在一个内部宇宙中：
 [DiscreteCat] 的同类是 Rocq 的 `eq`，因此 `Prop` 具有该值，因此
 辅助 [Sets]，其内 [Adjunction] 声明其同构关系，
 将其载体宇宙最小化到 `Set`。它并不限制幺半群，并且这是被保护的，而不仅仅是被观察——结尾的探测部分声明了一个幺半群的三个宇宙严格高于 `Set`，并且两个标题仍然在那里展开。[DiscreteCat_Functor] 在下面的任何地方都未使用；严格范畴之外的函子则是手写记录。已记录的更正：早期版本给出的理由是“(Instance/Discrete.v) 它没有注释，并且将其源固定在 [DiscreteCat@{u Set Set}] 上”。当时这样写是成立的，但现在不再成立——在 PR “代数载体是集合”(2026-09-17) 中，捐赠者在 Instance/Discrete.v 中被注释在原位，并且未固定任何内容。手写记录仍然保留，没有重新评估捐赠者现在是否仍可使用，因为这里没有任何地方使用它。

 ** 审计在全局上下文下闭合的104/104个常量——66个源声明的头加上38个[Program]义务，没有任何源扫描能看到，每个都通过其完全限定名称查询。两个枚举完全一致：[Print Module]列出的内容没有缺失在源头中，源头中的内容也没有缺失在[Print Module]中。该文件没有声明[Record]、[Class]或[Inductive]，所以没有未列出的[Build_*]。查看等级：这是对所有104个的一次性测量，而不是持续的门控。唯一的标准库导入是[Eqdep_dec]，用于[UIP_dec]，这是Hedberg的论点，并且不包含公理。在这个文件引入的所有71个标识符（66个声明的头部加上5个探针名称，这些名称没有声明任何内容）中，名称冲突通过两种方式进行了检查：一种是使用存储库常用的正则表达式检查声明头；另一种——更严格的标准——是在工作树中任何`.v`文件（不包括此文件）中的任何地方的完整单词标记出现情况进行检查。在编写此文件时针对的修订版（报告为 master e3ab9d22）下，两种标准均未发现冲突。没有需要单独检查的记录字段，也没有声明任何记录——这很重要，因为记录字段是全局常量，而声明头的检查无法看到它们。树中的两个名字是相邻的邻居，并且故意不被遮蔽，都在给定的行上得到了验证：[translation_functor]（Construction/Deloop/Functors.v）是一个函子；[Proset Z.le_preorder ⟶ Deloop Int_Plus]来自Awodey的 cocycle 构造，而不是一个平移的自函子；[grp_translate]（Instance/Grp/Epi.v）作为陪集空间上的一组集等价映射的左平移，而根本不是一个函子。

 [make todo] 通过下面五行 [Fail] 增长，除此之外没有任何增加：没有 TODO、FIXME 或 jww 被添加。

 ** 工程发现不要在文件中为局部变量命名为 [I]，如果该文件的义务策略是 [exact I]。在此文件的开发中以两种方式测量：在顶层设置的义务策略仍将 [I] 解析为 [Logic.I]，在绑定 [I : MonInverses M] 的节中，但在该节内部设置的相同策略将其解析为节变量，并且每个义务都失败，出现“术语 I 的类型为 MonInverses M”。因此，下面的每个逆见证都命名为 [Inv]。 

 [Structure/Groupoid.v] 的 [MonInverses] 被拆解为 [minv] / [minv_l] / [minv_r]；[Construction/Deloop.v] 的 [mon_inverse_unique] 是使 [MonInverses_of_right_inverses] 成为两行而不是追逐的原因。

 ** 未交付- 在任何假设下，[MonDiscrete M] 与 [MonDiscreteStrict M] 之间没有等价性，也没有同构性；只有两个比较函子，以及它们在对象上的作用是相关的。 - 对于 [MonStrict] 或 [MonUIP]，没有任意方向的必要性结果。 - [RightTranslation] 没有严格范畴的对应物，因此没有严格的右平移伴随，也没有严格的右手双条件式。 - 没有命名单元或余单元，也没有陈述三角恒等式；伴随只以 H-集表示法给出。在 [MonDiscrete M] 上，这几乎不造成问题——因为该范畴是稀薄的，所以单元或余单元的每个组成部分由其端点确定，至多由 `≈` 决定——但在 [MonDiscreteStrict M] 上却是真正的缺失，因为该范畴仅在 [MonUIP] 下是稀薄的。- 除了共享 [MonInverses] 外，没有任何内容将其与 [deloop_groupoid_iff] 联系起来；特别是没有建立 [Deloop M] 和 [MonDiscrete M] 之间的函子。- 对于幺半群同态没有任何说明，因此不存在函子 M ↦ [MonDiscrete M]，也不存在 M 中任何识别的自然性。- 没有注册 [Instance]：这里没有任何内容用于求解。- 使用的幺半群记录是 Construction/Deloop.v 中的 [MonObject]。该树包含其他几种幺半群的概念（如 Structure/Monoid.v 中基于幺半群的 [MonoidObject]，Theory/Coq/Monoid.v 中无定律类，以及 Instance/CMon.v 中的交换 [CMonObject] 等）；没有一个与此开发相关。
*)

(* * ** Block A: the discrete category on a monoid / * ** 块 A：幺半群上的离散范畴 *)

(*
 The elements of M as objects, its own `≈` as the only identifications.
 [DiscreteSetoidCat] is Construction/Comma/Special.v, reused rather
 than rebuilt.  That file also explains why Instance/Proset.v's [Proset]
 was not the construction it wanted: [Proset] is stated over `Prop`-valued
 relations while `≈` is a `crelation`.  A `Prop`-squashed variant would in
 any case not obviously support the converse below, which reads an honest
 `≈` OUT of a hom-set — but that is an argument, not a measurement, and no
 squashed variant is built here. 

 --------
 M 的元素作为对象，其自身的 `≈` 作为唯一的标识。[DiscreteSetoidCat] 是 Construction/Comma/Special.v，重用而不是重建。该文件还解释了为什么 Instance/Proset.v 的 [Proset] 不是它想要的构造：[Proset] 是在 `Prop` 值关系上说明的，而 `≈` 是一个 `crelation`。`Prop` 压缩变体在任何情况下都不会显然支持下面的逆方向，它从同态集读取一个真实的 `≈`——但那是一个论证，而不是测量，这里没有构建任何压缩变体。
*)
Definition MonDiscrete (M : MonObject) : Category :=
  DiscreteSetoidCat (@is_setoid (mon_setoid M)).

Example mon_discrete_obj (M : MonObject) :
  obj[MonDiscrete M] = carrier M := eq_refl.

Example mon_discrete_hom (M : MonObject) (x y : carrier M) :
  (x ~{MonDiscrete M}~> y) = (x ≈ y) := eq_refl.

(*
 Thin: the hom-setoid identifies all parallel arrows.  This is what makes
 every law in Blocks B and D free — NOT those of the strict Block F, whose
 hom-setoid is strict equality of proofs — and it is [DiscreteSetoidCat]'s
 own property. 

 --------
 薄：同态集合组识别所有平行箭头。这正是使得 B 块和 D 块中的每条定律都是自由的原因——而不是严格的 F 块，其同态集合组是证明的严格相等——这是 [DiscreteSetoidCat] 自身的属性。
*)
Lemma MonDiscrete_thin (M : MonObject) (x y : MonDiscrete M)
  (f g : x ~> y) : f ≈ g.
Proof. exact I. Qed.

(* * ** Block B: multiplication as a bifunctor, and the translations / * ** B区块：乘法作为双函子，以及翻译 *)

#[local] Obligation Tactic := repeat intro; exact I.

(*
 Mac Lane's "multiplication as a bifunctor": a functor from the product of
 the discrete category with itself.  Its arrow action IS [mon_op_respects],
 the field that makes multiplication respect `≈`. 

 --------
 Mac Lane 的“作为双函子的乘法”：从离散范畴与自身的积出发的一个函子。它的箭头作用是 [mon_op_respects]，使乘法遵守 `≈` 的那个域。
*)
Program Definition MonMult (M : MonObject) :
  MonDiscrete M ∏ MonDiscrete M ⟶ MonDiscrete M := {|
  fobj := fun p => mon_op (fst p) (snd p);
  fmap := fun x y f => mon_op_respects M _ _ (fst f) _ _ (snd f)
|}.

Program Definition LeftTranslation (M : MonObject) (a : carrier M) :
  MonDiscrete M ⟶ MonDiscrete M := {|
  fobj := fun x => mon_op a x;
  fmap := fun x y f => mon_op_respects M a a (reflexivity a) x y f
|}.

Program Definition RightTranslation (M : MonObject) (a : carrier M) :
  MonDiscrete M ⟶ MonDiscrete M := {|
  fobj := fun x => mon_op x a;
  fmap := fun x y f => mon_op_respects M x y f a a (reflexivity a)
|}.

Example left_translation_obj (M : MonObject) (a x : carrier M) :
  fobj[LeftTranslation M a] x = mon_op a x := eq_refl.

Example right_translation_obj (M : MonObject) (a x : carrier M) :
  fobj[RightTranslation M a] x = mon_op x a := eq_refl.

(*
 The translations ARE the partial applications of the bifunctor, on both
 data fields, by [eq_refl].  Note the handedness: [Partial_r F b] fixes the
 FIRST argument, so it is LEFT translation. 

 --------
 翻译是双函子的部分应用，在两个数据字段上，作用由 [eq_refl] 完成。注意方向：[Partial_r F b] 固定第一个参数，因此它是左翻译。
*)
Example lt_partial_obj (M : MonObject) (a : carrier M) :
  fobj[LeftTranslation M a] = fobj[Partial_r (MonMult M) a] := eq_refl.

Example lt_partial_fmap (M : MonObject) (a : carrier M) :
  @fmap _ _ (LeftTranslation M a) = @fmap _ _ (Partial_r (MonMult M) a)
  := eq_refl.

Example rt_partial_obj (M : MonObject) (a : carrier M) :
  fobj[RightTranslation M a] = fobj[Partial_l (MonMult M) a] := eq_refl.

Example rt_partial_fmap (M : MonObject) (a : carrier M) :
  @fmap _ _ (RightTranslation M a) = @fmap _ _ (Partial_l (MonMult M) a)
  := eq_refl.

(* * ** Block C: the cancellation calculus of a chosen inverse / * ** C 块：所选逆元的消去演算 *)

Section Cancel.
Context (M : MonObject) (Inv : MonInverses M) (a : carrier M).

Lemma mon_inv_cancel_l (x : carrier M) :
  mon_op (minv Inv a) (mon_op a x) ≈ x.
Proof.
  rewrite mon_op_assoc, (minv_l Inv a).
  apply mon_op_unit_l.
Qed.

Lemma mon_inv_cancel_l' (x : carrier M) :
  mon_op a (mon_op (minv Inv a) x) ≈ x.
Proof.
  rewrite mon_op_assoc, (minv_r Inv a).
  apply mon_op_unit_l.
Qed.

Lemma mon_inv_cancel_r (x : carrier M) :
  mon_op (mon_op x a) (minv Inv a) ≈ x.
Proof.
  rewrite <- mon_op_assoc, (minv_r Inv a).
  apply mon_op_unit_r.
Qed.

Lemma mon_inv_cancel_r' (x : carrier M) :
  mon_op (mon_op x (minv Inv a)) a ≈ x.
Proof.
  rewrite <- mon_op_assoc, (minv_l Inv a).
  apply mon_op_unit_r.
Qed.

End Cancel.

(* * ** Block D: inversion supplies the right adjoints / * ** D块：反演提供右伴随 *)

Section Adjoints.
Context (M : MonObject) (Inv : MonInverses M) (a : carrier M).

(* hom(a·x, y) → hom(x, a⁻¹·y). / hom(a·x, y) → hom(x, a⁻¹·y). *)
Definition left_transpose (x y : carrier M) (p : mon_op a x ≈ y) :
  x ≈ mon_op (minv Inv a) y.
Proof.
  rewrite <- (mon_inv_cancel_l M Inv a x).
  now rewrite p.
Defined.

Definition left_untranspose (x y : carrier M)
  (q : x ≈ mon_op (minv Inv a) y) : mon_op a x ≈ y.
Proof.
  rewrite q.
  apply mon_inv_cancel_l'.
Defined.

(*
 Every remaining field of [Adjunction] — both isomorphism laws, both
 respectfulness proofs and all four naturality clauses — is an equation in
 a hom-setoid of [MonDiscrete M], hence trivially true; the obligation
 tactic in force discharges all eight. 

 --------
 [Adjunction] 的每一个剩余域——无论是同构律、尊重性证明还是所有四条自然性条款——都是 [MonDiscrete M] 的同类集合中的一个方程，因此显而易见为真；当前生效的义务策略解除所有八个。
*)
Program Definition left_translation_adjunction :
  LeftTranslation M a ⊣ LeftTranslation M (minv Inv a) := {|
  adj := fun x y =>
    {| to   := {| morphism := left_transpose x y |}
     ; from := {| morphism := left_untranspose x y |} |}
|}.

(* hom(x·a, y) → hom(x, y·a⁻¹). / hom(x·a, y) → hom(x, y·a⁻¹). *)
Definition right_transpose (x y : carrier M) (p : mon_op x a ≈ y) :
  x ≈ mon_op y (minv Inv a).
Proof.
  rewrite <- (mon_inv_cancel_r M Inv a x).
  now rewrite p.
Defined.

Definition right_untranspose (x y : carrier M)
  (q : x ≈ mon_op y (minv Inv a)) : mon_op x a ≈ y.
Proof.
  rewrite q.
  apply mon_inv_cancel_r'.
Defined.

Program Definition right_translation_adjunction :
  RightTranslation M a ⊣ RightTranslation M (minv Inv a) := {|
  adj := fun x y =>
    {| to   := {| morphism := right_transpose x y |}
     ; from := {| morphism := right_untranspose x y |} |}
|}.

End Adjoints.

(* * ** Block E: the converse, and the biconditionals / * ** E 块：逆命题与双条件命题 *)

(*
 The mathematical content of the converse, isolated: a monoid in which
 every element has a right inverse is a group.  With b := r a and
 c := r (r a) we have a·b ≈ 1 and b·c ≈ 1, so [mon_inverse_unique]
 (Construction/Deloop.v) gives a ≈ c, whence b·a ≈ b·c ≈ 1.

 Instance/Grp.v's [grp_mul_inv_r] is the MIRROR IMAGE of this — right
 inverses from left ones — but over that file's own [GrpObject] record, in
 which the inverse operation is a FIELD; it is a different statement over a
 different record, and no attempt is made here to derive either from the
 other. 

 --------
 逆命题的数学内容，单独来看：一个每个元素都有右逆元的幺半群是一个群。设 b := r a 且 c := r (r a)，我们有 a·b ≈ 1 且 b·c ≈ 1，因此 [mon_inverse_unique] (Construction/Deloop.v) 给出 a ≈ c，因此 b·a ≈ b·c ≈ 1。

 Instance/Grp.v 的 [grp_mul_inv_r] 是这一命题的镜像——从左逆元得到右逆元——但它是在该文件自己的 [GrpObject] 记录上，其中逆元运算是一个字段；它是一个不同记录上的不同命题，这里并没有尝试从一个推导出另一个。
*)
Lemma MonInverses_of_right_inverses (M : MonObject)
  (r : carrier M → carrier M)
  (Hr : ∀ a : carrier M, mon_op a (r a) ≈ mon_unit) : MonInverses M.
Proof.
  refine {| minv := r ; minv_r := Hr |}.
  intro a.
  transitivity (mon_op (r a) (r (r a))).
  - apply mon_op_respects; [reflexivity |].
    exact (mon_inverse_unique M (r a) a (r (r a)) (Hr a) (Hr (r a))).
  - apply Hr.
Defined.

(* The mirror, for the right translations: all left inverses gives a group. / 镜像，对于正确的翻译：所有左逆元形成一个群。 *)
Lemma MonInverses_of_left_inverses (M : MonObject)
  (l : carrier M → carrier M)
  (Hl : ∀ a : carrier M, mon_op (l a) a ≈ mon_unit) : MonInverses M.
Proof.
  unshelve refine {| minv := l ; minv_l := Hl |}.
  intro a.
  transitivity (mon_op (l (l a)) (l a)).
  - apply mon_op_respects; [| reflexivity].
    symmetry.
    exact (mon_inverse_unique M (l a) (l (l a)) a (Hl (l a)) (Hl a)).
  - apply Hl.
Defined.

(*
 "Every left translation has a right adjoint", as DATA.  The library's ∃ is
 [sigT], so this is a function and no choice principle is consumed when the
 inverse operation is read off it. 

 --------
 “每一个左翻译都有一个右伴随”，作为数据。该库的 ∃ 是 [sigT]，所以这是一个函数，当从中读出逆操作时，不会消耗选择公理。
*)
Definition LeftTranslationAdjoints (M : MonObject) : Type :=
  ∀ a : carrier M,
    { R : MonDiscrete M ⟶ MonDiscrete M & LeftTranslation M a ⊣ R }.

Definition RightTranslationAdjoints (M : MonObject) : Type :=
  ∀ a : carrier M,
    { R : MonDiscrete M ⟶ MonDiscrete M & RightTranslation M a ⊣ R }.

(*
 The answer to the exercise's question, in the affirmative.  Forward:
 inversion supplies the adjoints.  Backward: the inverse transpose applied
 to the identity of R(1) is exactly a · R(1) ≈ 1. 

 --------
 练习问题的答案是肯定的。前向：反演提供伴随矩阵。后向：逆转置作用于 R(1) 的单位元恰好是 a · R(1) ≈ 1。
*)
Theorem mon_group_iff_left_translation_adjoints (M : MonObject) :
  MonInverses M ↔ LeftTranslationAdjoints M.
Proof.
  split.
  - intros Inv a.
    exists (LeftTranslation M (minv Inv a)).
    exact (left_translation_adjunction M Inv a).
  - intro H.
    unshelve refine (MonInverses_of_right_inverses M
      (fun a => fobj[projT1 (H a)] mon_unit) _).
    intro a.
    exact (from (@adj _ _ _ _ (projT2 (H a))
                  (fobj[projT1 (H a)] mon_unit) mon_unit)
             (reflexivity _)).
Defined.

Theorem mon_group_iff_right_translation_adjoints (M : MonObject) :
  MonInverses M ↔ RightTranslationAdjoints M.
Proof.
  split.
  - intros Inv a.
    exists (RightTranslation M (minv Inv a)).
    exact (right_translation_adjunction M Inv a).
  - intro H.
    unshelve refine (MonInverses_of_left_inverses M
      (fun a => fobj[projT1 (H a)] mon_unit) _).
    intro a.
    exact (from (@adj _ _ _ _ (projT2 (H a))
                  (fobj[projT1 (H a)] mon_unit) mon_unit)
             (reflexivity _)).
Defined.

(* * ** Block F: the same over [DiscreteCat], where homs are Rocq's `=` / * ** 块 F：相同于 [DiscreteCat]，其中的同态是 Rocq 的 `=` *)

(* The two hypotheses, in the shape of Construction/Comma/Special.v's [HomStrict] and [HomUIP]. Sufficient for the forward direction below; NOT shown necessary. / 这两个假设，以 Construction/Comma/Special.v 的形式表现为 [HomStrict] 和 [HomUIP]。对于下面的正向方向足够；未显示为必要。 *)
Definition MonStrict (M : MonObject) : Type :=
  ∀ x y : carrier M, x ≈ y → x = y.

Definition MonUIP (M : MonObject) : Type :=
  ∀ (x y : carrier M) (p q : x = y), p = q.

(* Hedberg, via the stdlib's axiom-free [UIP_dec]. / Hedberg，通过 stdlib 的无公理 [UIP_dec] 。 *)
Definition MonUIP_dec (M : MonObject)
  (dec : ∀ x y : carrier M, {x = y} + {x <> y}) : MonUIP M := UIP_dec dec.

(*
 The explicit binders are load-bearing: unannotated, this body minimizes so
 as to identify the hom and proof universes of the result. 

 --------
 显式绑定器是承重的：未注释时，该主体会最小化，以识别结果的 hom 和 proof 宇宙。
*)
Definition MonDiscreteStrict@{o h p m1 m2} (M : MonObject@{o m1 m2}) :
  Category@{o h p} := DiscreteCat@{o h p} (carrier M).

Example mon_discrete_strict_hom (M : MonObject) (x y : carrier M) :
  (x ~{MonDiscreteStrict M}~> y) = (x = y) := eq_refl.

(*
 Left translation on the strict category needs NO hypothesis: the arrow
 action is [f_equal], and both remaining functor laws close by destructing
 equality proofs.  There are only TWO obligations: the third field,
 [fmap_respects], is filled by instance resolution with
 [CMorphisms.reflexive_proper], the hom-setoid there being strict
 equality. 

 --------
 严格范畴上的左翻译不需要假设：箭头动作是 [f_equal]，并且剩下的两个函子律通过析构等式证明即可闭合。只有两个义务：第三个字段 [fmap_respects] 是通过实例解析 [CMorphisms.reflexive_proper] 填充的，那里的同态集合是严格等式。
*)
#[local] Obligation Tactic := idtac.

Program Definition LeftTranslationStrict (M : MonObject) (a : carrier M) :
  MonDiscreteStrict M ⟶ MonDiscreteStrict M := {|
  fobj := fun x => mon_op a x;
  fmap := fun x y (p : x = y) => f_equal (mon_op a) p
|}.
Next Obligation. intros M a x; reflexivity. Qed.
Next Obligation. intros M a x y z p q; now destruct p, q. Qed.

Section StrictAdjoint.
Context (M : MonObject) (HS : MonStrict M) (HU : MonUIP M).
Context (Inv : MonInverses M) (a : carrier M).

(*
 Where [MonStrict] is spent.  Within this section it occurs exactly twice,
 in the two definitions immediately below; everything after them goes
 through [strict_cancel_l]/[strict_cancel_r] and never mentions [HS].  It
 is spent once more elsewhere in the file, at [MonDiscreteToStrict] in
 Block G. 

 --------
 [MonStrict] 被使用的地方。在本节中，它正好出现两次，在下面紧接的两个定义中；在它们之后的所有内容都通过 [strict_cancel_l] / [strict_cancel_r]，并且从未提到 [HS]。它在文件的其他地方还会被使用一次，在 Block G 的 [MonDiscreteToStrict]。
*)
Definition strict_cancel_l (x : carrier M) :
  mon_op (minv Inv a) (mon_op a x) = x := HS _ _ (mon_inv_cancel_l M Inv a x).

Definition strict_cancel_r (y : carrier M) :
  mon_op a (mon_op (minv Inv a) y) = y := HS _ _ (mon_inv_cancel_l' M Inv a y).

Definition left_transpose_strict (x y : carrier M) (p : mon_op a x = y) :
  x = mon_op (minv Inv a) y :=
  eq_trans (eq_sym (strict_cancel_l x)) (f_equal (mon_op (minv Inv a)) p).

Definition left_untranspose_strict (x y : carrier M)
  (q : x = mon_op (minv Inv a) y) : mon_op a x = y :=
  eq_trans (f_equal (mon_op a) q) (strict_cancel_r y).

(*
 And this is where [MonUIP] is spent: every remaining field is an equation
 between two equality proofs. 

 --------
 而这就是 [MonUIP] 被消耗的地方：每一个剩余的字段都是两个等式证明之间的一个方程。
*)
#[local] Obligation Tactic := repeat intro; now apply HU.

Program Definition left_translation_strict_adjunction :
  LeftTranslationStrict M a ⊣ LeftTranslationStrict M (minv Inv a) := {|
  adj := fun x y =>
    {| to   := {| morphism := left_transpose_strict x y |}
     ; from := {| morphism := left_untranspose_strict x y |} |}
|}.

End StrictAdjoint.

Definition LeftTranslationAdjointsStrict (M : MonObject) : Type :=
  ∀ a : carrier M,
    { R : MonDiscreteStrict M ⟶ MonDiscreteStrict M &
      LeftTranslationStrict M a ⊣ R }.

(*
 The converse over the strict category needs NO hypothesis, because a
 Leibniz equality yields an `≈` outright.  The asymmetry with the forward
 direction is the whole content of the fork described in the header. 

 --------
 严格范畴上的逆命题不需要假设，因为莱布尼茨等式直接产生了一个 `≈`。与正向方向的不对称性就是标题中描述的分叉的全部内容。
*)
Definition strict_left_translation_adjoints_MonInverses (M : MonObject)
  (H : LeftTranslationAdjointsStrict M) : MonInverses M.
Proof.
  unshelve refine (MonInverses_of_right_inverses M
    (fun a => fobj[projT1 (H a)] mon_unit) _).
  intro a.
  refine (_ (from (@adj _ _ _ _ (projT2 (H a))
                     (fobj[projT1 (H a)] mon_unit) mon_unit) eq_refl)).
  intro e; simpl in e.
  now rewrite e.
Defined.

Theorem mon_group_iff_left_translation_adjoints_strict (M : MonObject)
  (HS : MonStrict M) (HU : MonUIP M) :
  MonInverses M ↔ LeftTranslationAdjointsStrict M.
Proof.
  split.
  - intros Inv a.
    exists (LeftTranslationStrict M (minv Inv a)).
    exact (left_translation_strict_adjunction M HS HU Inv a).
  - exact (strict_left_translation_adjoints_MonInverses M).
Defined.

(* * ** Block G: comparing the two discrete categories / * ** G 块：比较这两个离散类别 *)

#[local] Obligation Tactic := repeat intro; exact I.

(* One way is free. / 一种方式是免费的。 *)
Program Definition MonStrictToDiscrete (M : MonObject) :
  MonDiscreteStrict M ⟶ MonDiscrete M := {|
  fobj := fun x => x;
  fmap := fun x y (p : x = y) =>
            match p with eq_refl => @id (MonDiscrete M) x end
|}.

Section Compare.
Context (M : MonObject) (HS : MonStrict M) (HU : MonUIP M).

(*
 The other costs exactly the two hypotheses: [MonStrict] for the arrow
 action, [MonUIP] for all three functor laws, each of which is an equation
 between equality proofs here.  (Three obligations, against two for
 [MonStrictToDiscrete], whose target is thin.) 

 --------
 其他精确计算了两个假设：箭头操作的 [MonStrict]，所有三个函子定律的 [MonUIP]，每一个都是这里等式证明之间的一个方程。（三个义务，而 [MonStrictToDiscrete] 只有两个，因为它的目标是薄的。）
*)
#[local] Obligation Tactic := repeat intro; now apply HU.

Program Definition MonDiscreteToStrict :
  MonDiscrete M ⟶ MonDiscreteStrict M := {|
  fobj := fun x => x;
  fmap := fun x y f => HS x y f
|}.

End Compare.

Example mon_strict_to_discrete_obj (M : MonObject) (x : carrier M) :
  fobj[MonStrictToDiscrete M] x = x := eq_refl.

Example mon_discrete_to_strict_obj (M : MonObject) (HS : MonStrict M)
  (HU : MonUIP M) (x : carrier M) :
  fobj[MonDiscreteToStrict M HS HU] x = x := eq_refl.

(** ** Block H: witnesses / ** H区：证人 *)

(*
 The discrete category on a monoid is not trivial: Z/3 gives two distinct
 objects with an EMPTY hom-set between them.  (This has to be checked at a
 concrete monoid: for a general M the hom x ~> y IS the type x ≈ y, which
 may perfectly well be inhabited for distinct x and y.) 

 --------
 单元上的离散范畴不是平凡的：Z/3 给出了两个不同的对象，它们之间有一个空的同态集。（这必须在具体的幺半群上进行检查：对于一般的 M，x ~> y 的同态是类型 x ≈ y，对于不同的 x 和 y，这个类型可能完全可以被占据。）
*)
Lemma Z3_two_objects : (Z3_0 : MonDiscrete Z3_Mon) <> Z3_1.
Proof. discriminate. Qed.

Lemma Z3_hom_empty : (Z3_0 ~{MonDiscrete Z3_Mon}~> Z3_1) → False.
Proof. intro p; discriminate. Qed.

(*
 (ℕ, +) is not a group, so by the biconditional its left translations
 cannot all have right adjoints.  The direct refutation is sharper: ONE
 translation suffices, and the contradiction is a computation.  From
 L_1 ⊣ R, the inverse transpose at the identity of R(0) reads
 1 + R(0) ≈ 0, that is S (R 0) = 0. 

 --------
 (ℕ, +) 不是一个群，因此根据双重条件，它的左平移不可能都有右伴随。直接反驳更为尖锐：一个平移就足够了，矛盾是一个计算结果。从 L_1 ⊣ R，在 R(0) 的单位元处的逆转置为 1 + R(0) ≈ 0，也就是 S(R 0) = 0。
*)
Lemma nat_translation_no_right_adjoint
  (R : MonDiscrete Nat_Plus ⟶ MonDiscrete Nat_Plus)
  (A : LeftTranslation Nat_Plus 1%nat ⊣ R) : False.
Proof.
  pose proof (from (@adj _ _ _ _ A (fobj[R] 0%nat) 0%nat) (reflexivity _))
    as e.
  simpl in e.
  discriminate.
Qed.

Corollary nat_no_right_adjoints : LeftTranslationAdjoints Nat_Plus → False.
Proof.
  intro H.
  exact (nat_plus_no_inverses
           (snd (mon_group_iff_left_translation_adjoints Nat_Plus) H)).
Qed.

(*
 The group witness.  Z/2 would be DEGENERATE here: every element is its own
 inverse ([bool_xor_self_adjoint]), so each left translation would be its
 own right adjoint and the adjunction would say nothing about inversion.
 Z/3 is the smallest group whose inversion moves an element
 (Structure/Groupoid.v's [Z3_inv_moves]), so over it the left adjoint and
 the right adjoint are provably different functors. 

 --------
 群见证。这里 Z/2 将是退化的：每个元素都是它自己的逆（[bool_xor_self_adjoint]），所以每个左平移都是它自己的右伴随，并且伴随关系对求逆没有任何说明。Z/3 是最小的一个群，其求逆会改变元素（Structure/Groupoid.v 中的 [Z3_inv_moves]），因此在它之上，左伴随和右伴随可以证明是不同的函子。
*)
Definition Bool_Xor_Inverses : MonInverses Bool_Xor :=
  MonInverses_of Bool_Xor_Grp.

Example bool_xor_self_adjoint (b : carrier Bool_Xor) :
  minv Bool_Xor_Inverses b = b := eq_refl.

Definition Z3_Inverses : MonInverses Z3_Mon := MonInverses_of Z3_Grp.

Definition Z3_left_adjunction (a : carrier Z3_Mon) :
  LeftTranslation Z3_Mon a ⊣ LeftTranslation Z3_Mon (minv Z3_Inverses a) :=
  left_translation_adjunction Z3_Mon Z3_Inverses a.

Example Z3_left_adjoint_at :
  fobj[LeftTranslation Z3_Mon Z3_1] Z3_0 = Z3_1 := eq_refl.

Example Z3_right_adjoint_at :
  fobj[LeftTranslation Z3_Mon (minv Z3_Inverses Z3_1)] Z3_0 = Z3_2 := eq_refl.

Lemma Z3_adjoints_differ :
  fobj[LeftTranslation Z3_Mon Z3_1] Z3_0
    <> fobj[LeftTranslation Z3_Mon (minv Z3_Inverses Z3_1)] Z3_0.
Proof. discriminate. Qed.

(*
 Z/3's carrier setoid is Leibniz equality on [Z3] (Structure/Groupoid.v),
 so it also witnesses the strict reading, with both hypotheses discharged:
 [MonStrict] by the identity function, [MonUIP] by Hedberg. 

 --------
 Z/3的承载集合等式是在[Z3]（Structure/Groupoid.v）上的莱布尼茨相等，因此它也证明了严格读法，两个假设都已解除：[MonStrict]由恒等函数，[MonUIP]由Hedberg提供。
*)
Definition Z3_MonStrict : MonStrict Z3_Mon := fun _ _ p => p.

Definition Z3_dec (x y : Z3) : {x = y} + {x <> y}.
Proof.
  destruct x, y; solve [ left; reflexivity | right; discriminate ].
Defined.

Definition Z3_MonUIP : MonUIP Z3_Mon := MonUIP_dec Z3_Mon Z3_dec.

Definition Z3_strict_adjunction (a : carrier Z3_Mon) :
  LeftTranslationStrict Z3_Mon a
    ⊣ LeftTranslationStrict Z3_Mon (minv Z3_Inverses a) :=
  left_translation_strict_adjunction Z3_Mon Z3_MonStrict Z3_MonUIP
    Z3_Inverses a.

(** ** Block I: probes / ** 第一部分：探针 *)

(*
 FOUR negatives of TWO KINDS, plus a separate instrument check.  Each of
 the five was stripped of its [Fail] and compiled alone.
 [mon_probe_instrument], [probe_partial_record],
 [probe_categories_agree] and [probe_hom_is_eq] report `cannot unify`
 between two terms of one type (CONVERSION); [probe_cancel_strict] reports
 a plain type mismatch with NO `cannot unify` clause (TYPING).  Every
 negative is stated at a VARIABLE monoid, which matters for
 [probe_hom_is_eq]: at Z/3, whose `≈` IS `=`, that statement HOLDS, so a
 probe at a concrete monoid would have measured nothing.

 No constant a negative names, other than the negative's own name, is
 absent from a command that must SUCCEED (measured mechanically over the
 token sets, zero exceptions), so no guard here is vacuous. 

 --------
 两类四个负样本，加上一个单独的仪器检查。每个五个样本都被去掉了 [Fail] 并单独编译。[mon_probe_instrument]、[probe_partial_record]、[probe_categories_agree] 和 [probe_hom_is_eq] 报告 `cannot unify` 在同一类型的两个项之间（转换）；[probe_cancel_strict] 报告一个普通类型不匹配，没有 `cannot unify` 条款（类型检查）。每个负样本都在一个变量幺半群上说明，这对于 [probe_hom_is_eq] 很重要：在 Z/3 上，其 `≈` 是 `=`，这条说明成立，所以在具体幺半群上的探测不会测量到任何东西。除了负样本自身的名称之外，没有常量负样本名称缺失于必须成功的命令中（通过令牌集机械测量，零例外），所以这里没有守卫是空的。
*)
Section Probes.
Context (M : MonObject) (Inv : MonInverses M) (a x y : carrier M).

(* Instrument check: [Fail] itself is doing something. / 仪器检查：[Fail] 本身正在做某事。 *)
Fail Definition mon_probe_instrument : True = False := eq_refl.

Fail Definition probe_partial_record :
  LeftTranslation M a = Partial_r (MonMult M) a := eq_refl.

Fail Definition probe_categories_agree :
  MonDiscrete M = MonDiscreteStrict M := eq_refl.

Definition ctrl_objects_agree :
  obj[MonDiscrete M] = obj[MonDiscreteStrict M] := eq_refl.

Fail Definition probe_hom_is_eq :
  (x ~{MonDiscrete M}~> y) = (x = y) := eq_refl.

Definition ctrl_hom_is_equiv :
  (x ~{MonDiscrete M}~> y) = (x ≈ y) := eq_refl.

Definition ctrl_strict_hom_is_eq :
  (x ~{MonDiscreteStrict M}~> y) = (x = y) := eq_refl.

Fail Definition probe_cancel_strict :
  mon_op (minv Inv a) (mon_op a x) = x := mon_inv_cancel_l M Inv a x.

Definition ctrl_cancel_equiv :
  mon_op (minv Inv a) (mon_op a x) ≈ x := mon_inv_cancel_l M Inv a x.

End Probes.

(*
 The `Set` in the strict headline's constraint block sits on an internal
 universe — the auxiliary [Sets] in which [Adjunction] states its
 hom-isomorphism, whose carrier universe minimizes to `Set` because
 [DiscreteCat]'s homs are Rocq's `eq`, hence `Prop`-valued.  It does not
 restrict the monoid, and this section is the guard rather than a remark:
 all three of a monoid's universes are declared strictly above `Set` and
 both headlines still elaborate. 

 --------
 在严格标题约束块中的 `Set` 位于一个内部宇宙——辅助 [Sets]，其中 [Adjunction] 陈述其同构性，其承载宇宙最小化为 `Set`，因为 [DiscreteCat] 的 hom 是 Rocq 的 `eq`，因此为 `Prop` 值。它不限制幺半群，本节是守护而非备注：幺半群的所有三个宇宙都严格声明在 `Set` 之上，并且两个标题仍然展开说明。
*)
Section UniverseProbe.
Universe mo mh mp.
Constraint Set < mo.
Constraint Set < mh.
Constraint Set < mp.
Context (Mu : MonObject@{mo mh mp}).

Check (mon_group_iff_left_translation_adjoints Mu).
Check (mon_group_iff_left_translation_adjoints_strict Mu).
Check (MonDiscrete Mu).
Check (MonDiscreteStrict Mu).

End UniverseProbe.
