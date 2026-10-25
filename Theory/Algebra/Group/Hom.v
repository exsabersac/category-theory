Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Semicartesian.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Structure.Monoidal.Heunen_Vicary.Cartesian.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Group.
Require Import Category.Structure.Group.Proofs.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Theory.Algebra.Monoid.Product.

Generalizable All Variables.

(** * Group homomorphisms, the category of group objects, finite products / * 群同态，群对象的范畴，有限积 *)

(*
nLab:      https://ncatlab.org/nlab/show/group+object
   Wikipedia: https://en.wikipedia.org/wiki/Group_object

   Mac Lane, Categories for the Working Mathematician, 2nd ed., Section III.6
   ("Groups in Categories"), Exercises 1 and 2, as scoped by issue #343;
   Awodey, Category Theory, 2nd ed., Section 4.1 (the Group(C) construction).

   Given group objects (x, μ_X, η_X, ι_X) and (y, μ_Y, η_Y, ι_Y) in a
   cartesian monoidal category C (Structure/Group.v), a morphism f : x ~> y
   is a homomorphism of group objects when it commutes with the
   multiplications and the units,

     multiplication square   f ∘ μ_X ≈ μ_Y ∘ (f ⨂ f)
     unit triangle           f ∘ η_X ≈ η_Y

   and NOTHING ELSE IS DEMANDED.  Commutation with the inversions,
   f ∘ ι_X ≈ ι_Y ∘ f, is a THEOREM ([GroupHom_inverse]) rather than a field:
   this is Awodey's observation in Section 4.1, and it is why [GroupHom] is
   literally [MonoidHom] of the underlying monoid objects rather than a
   record extending it.  Group objects and these morphisms form a category
   [GrpCat], with faithful forgetful functors to C and to [Mon C]; when C has
   binary products and a terminal object, [GrpCat] has them too, carried
   componentwise, and the forgetful functor to C sends them to C's own ON THE
   NOSE.

   WHAT IS PROVED HERE, IN ORDER

   (1) [group_monoid] / [group_inverse] — reading a [GroupObject] as an
       internal [Monoid] in the mu/eta presentation that [Mon] is indexed by,
       and naming the inversion of a given group object.
   (2) [GroupHom] with [group_hom_mappend] / [group_hom_mempty], and
       [GroupHom_inverse], the theorem that replaces the missing field.
   (3) [GrpCat], [GrpCat_Forget] (faithful) and [GrpCat_Mon] (faithful) —
       Exercise 2 / Awodey's Group(C).
   (4) [GroupObject_Product] and [GrpCat_Cartesian] — binary products.
   (5) [GroupObject_Terminal] and [GrpCat_Terminal] — the terminal group
       object.
   (6) [GrpCat_Forget_*] — the forgetful functor sends both to C's own, at
       Leibniz equality.
   (7) [GrpCat_Cartesian_tensor] / [GrpCat_Terminal_unit] — the same two
       structures with NO hypothesis beyond the [CartesianMonoidal] that
       [GroupObject] already demands.
   (8) A probe section: three negatives of two kinds, four universe
       negatives, and their controls.

   HOW ISSUE #503 IS CONSUMED, AND AT WHICH GRADE

   The monoid half of Exercise 1 is Theory/Algebra/Monoid/Product.v
   ([Monoid_Product], [Mon_Cartesian], [Mon_Terminal]).  It is INSTANTIATED,
   not reproved, and the instantiation worked at three separate grades, each
   machine-checked rather than asserted:

     - DEFINITIONAL.  [grp_prod_monoid] shows by [eq_refl] that the
       underlying monoid of [GroupObject_Product] IS
       [Monoid_Product (group_monoid X) (group_monoid Y)] — the whole
       record, not a comparison map — and [grp_prod_mappend] /
       [grp_prod_mempty] read its two structure maps back as
       [mon_prod_mu] / [mon_prod_eta].  This rests on #503's own
       [monoid_round], the [Monoid]/[MonoidObject] round trip that closes by
       [eq_refl].
     - CONVERTIBLE.  [grp_exl_hom], [grp_exr_hom], [grp_fork_hom] and
       [grp_one_hom] are discharged by [exact] of #503's [mon_exl_hom],
       [mon_exr_hom], [mon_fork_hom] and [mon_one_hom] with no adapter: the
       [GroupHom] goal and the [MonoidHom] goal are the SAME TYPE up to
       conversion.  Not one new obligation about multiplication or unit
       occurs anywhere below.
     - REUSED PROOF SHAPE.  [Monoid_Product]'s three monoid laws are taken
       wholesale; only the inversion and the two inverse laws
       ([grp_prod_left_inverse], [grp_prod_right_inverse]) are new work, and
       their leg lemmas follow the shape of #503's [mon_prod_assoc_leg].

   WHAT COULD NOT BE INSTANTIATED, AND WHY — MEASURED

   #503 states its half over an ARBITRARY monoidal base M.  This file cannot:
   [GroupObject] is declared over [CartesianMonoidal], because its two
   inverse laws are written in copy/discard vocabulary (∆ and [eliminate])
   that a bare [Monoidal] does not supply.  That is pinned as negative 1
   below — a TYPING failure, "The term M has type Monoidal while it is
   expected to have type CartesianMonoidal" — against a control at
   [CartesianMonoidal].  So the scope difference between the two files is a
   fact about the DEFINITION of a group object, not a weakness of this
   development, and no route around it is offered.

   The consolation is real and is delivered: since a cartesian monoidal
   category IS cartesian (Fox's theorem, [CartesianMonoidal_Cartesian],
   Structure/Monoidal/Heunen_Vicary/Cartesian.v) and its unit IS terminal
   ([SemicartesianMonoidal_Terminal]), the finite products of [GrpCat] cost
   NO hypothesis at all: [GrpCat_Cartesian_tensor] and
   [GrpCat_Terminal_unit] instantiate the general theorems at those two, and
   [grpcat_tensor_product] / [grpcat_unit_terminal] record by [eq_refl] that
   the product is then carried by the tensor and the terminal object by I.
   The general forms are kept, and are strictly more general: they take a
   [Cartesian C] and a [Terminal C] with NO assumed compatibility with ⨂,
   exactly as #503 does.

   THE INVERSE-PRESERVATION THEOREM, AND WHAT IT COST

   [GroupHom_inverse] is ten tactic lines.  Its content is the elementwise
   argument "f(a⁻¹) is a left inverse of f(a), and left inverses are unique",
   run diagrammatically: reshape (f ∘ ι_x) ⨂ f as (f ⨂ f) ∘ (ι_x ⨂ id) by
   [bimap_comp], push f out through the multiplication square, collapse what
   remains by the SOURCE object's [left_inverse], and finish with the unit
   triangle.  Uniqueness of left inverses in the TARGET is
   Structure/Group/Proofs.v's [left_inverse_unique], which is where the
   diagonal's naturality and the terminality of I are spent — that list is
   NOT exhaustive, and the omission matters: an audit found that donor's
   proof also does [rewrite <- right_inverse] (Structure/Group/Proofs.v)
   and spends [mappend_assoc_sym] and both [mempty_*_diagonal] helpers.  So
   correct a claim an earlier draft of this header made: [right_inverse] does
   not occur in [GroupHom_inverse]'s OWN tactic script, but the theorem DOES
   depend on [right_inverse] of the target through [left_inverse_unique].
   What is asymmetric is the script, not the dependency, and calling it "an
   asymmetry worth recording" was wrong.  No hypothesis beyond [MonoidHom] is
   needed.  Two right-associated readings of the inverse laws
   ([left_inverse_r], [right_inverse_r]) exist only to meet [rewrite]'s
   bracketing and carry no content.

   THE NAME.  The category is [GrpCat], not [Grp], and the reason is
   measured rather than aesthetic: Instance/Grp.v already declares
   [Grp : Category] — the concrete category of groups over [Sets] — together
   with [Grp_Cartesian], [Grp_Terminal], [Grp_Forget]
   and [Grp_Forget_Faithful], FIVE collisions found with [rg] over the
   whole tree.  An earlier draft said four; an audit found the fifth.  The
   cause is worth recording because the obvious explanation is WRONG: it is
   not the [#[export] Program Instance] shape, since [Grp_Cartesian] has
   exactly that shape and WAS found.  The list was built from four GUESSED
   names instead of being derived from this file's own declared names under
   the rename — [GrpCat_Forget_Faithful] maps to [Grp_Forget_Faithful], and
   that name was simply never searched for.  This file requires none of those
   modules, so nothing is ambiguous within it; the rename exists so that a
   consumer may import both without qualifying.

   TWO ENGINEERING FINDINGS, both about NAMES rather than mathematics.

   - [inverse] IS A KEYWORD downstream of Structure/Group.v.  Its
     notation quotes the token, [Notation "'inverse' [ G ]"], which makes
     [inverse] a terminal symbol: [@inverse _ _ _ G] is then a PARSE error
     ("Syntax error: [global] or [pattern_ident] expected after '@'"), and
     the record-literal field name is rejected too — in the realistic
     multi-field shape [{| groupobject_is_monoid := _ ; inverse := _ |}],
     with "Syntax error: ['|}'] expected after [record_declaration]".  The
     shape matters and an earlier draft of this header got it wrong by
     quoting that message against a SINGLE-field literal: with [inverse]
     first the message is instead "Syntax error: [record_declaration]
     expected after '{|'".  Both are parse errors, so no kind claim changes.
     NEITHER can be pinned as a probe: [Fail] catches elaboration failures,
     and a parse error aborts the file even inside [Fail] — which is why
     these two findings are recorded in prose rather than guarded.  The
     notation itself takes the OBJECT and leaves the instance to resolution,
     which is fine in Structure/Group/Proofs.v but not here, where several
     group objects on different objects are in scope at once.  Both are
     worked around: [group_inverse] names the instance via the qualified
     [@Category.Structure.Group.inverse] (a qualified path DOES parse after
     [@]), and [GroupObject_Product] / [GroupObject_Terminal] are built with
     [Build_GroupObject] rather than record-literal syntax.
     [group_inverse_is] records by [eq_refl] that the accessor and the
     notation agree.
   - [fork] AND [fork_respects] ARE SHADOWED.  Structure/Monoidal/Relevance.v
     declares its own [fork] (the diagonal-built pairing) and its own
     [fork_respects] instance, and [Heunen_Vicary.v] re-exports Relevance, so
     merely naming [CartesianMonoidal] brings both into scope.  Consequently
     [GrpCat_Cartesian] must write [Cartesian.fork] for its field — the same
     workaround Heunen_Vicary/Cartesian.v uses — and its respectfulness
     obligation must name [Cartesian.fork_respects].  The [△] NOTATION is
     unaffected: Structure/Cartesian.v declares it against the resolved
     constant, so it keeps meaning the product's pairing.

   STRENGTHS, MEASURED STRICT FIRST.  Twenty Examples close by [eq_refl].
   Ten are identifications: the two structure maps of [group_monoid], the
   inversion accessor, the four readings of [GroupObject_Product], the
   terminal monoid, and the two [GrpCat_Mon]/[GrpCat_Forget] agreements.
   Six record that [GrpCat_Forget] carries the product, the terminal object,
   both projections, the pairing and the unique map to C's own; two that
   [GrpCat_Mon] does the same into [Mon C]; and two that the hypothesis-free
   instances of (7) put the product at the tensor and the terminal object
   at I.  The four
   homomorphism lemmas are stronger still, being CONVERSIONS rather than
   equalities of terms.  ONE fallback, and it is a refutation rather than a
   weakening: [Mon_Forget ◯ GrpCat_Mon = GrpCat_Forget] is REJECTED at
   [eq_refl] (negative 3), diagnosed to [Compose] rebuilding its
   [fmap_respects], [fmap_id] and [fmap_comp] fields as fresh proof terms
   while BOTH data fields agree on the nose — the two controls
   [grpcat_mon_forget_obj] and [grpcat_mon_forget_map] are exactly that
   agreement.  An earlier draft of this header justified delivering no [≈]
   form by saying that stating it "needs a hom-setoid on functors" which
   "would pull a functor category into the closure of a [Theory/Algebra]
   file".  THAT WAS FALSE and an audit refuted it: [Functor_Setoid] and
   [Functor_StrictEq_Setoid] are Theory/Functor.v, which this
   file already requires, and no functor category is involved.  The
   equation is therefore DELIVERED, and at the STRICTER of the two available
   strengths: [forget_compose_strict] proves it in
   [Functor_StrictEq_Setoid] with every object component literally [eq_refl].
   So negative 3 says exactly what it says and no more — the composite is not
   the SAME RECORD, while the two functors are strictly equal as functors.

   UNIVERSES.  Measured in the constraint blocks AND read off the binders,
   and the two disagree in the way that matters.

   - THE BINDER carries the only identification in the file.  Every constant
     that binds a [C] is over [C : Category@{u u0 u0}] — C's hom and proof
     universes IDENTIFIED — and there are 110 such occurrences over the 55
     named constants (140 over all 70).  There IS exactly one other
     [Category@{...}] instance, and an earlier draft of this header wrongly
     said there was none: [GrpCat]'s own RESULT type [Category@{u2 u0 u0}],
     quoted in the [Mon]-comparison bullet below.  It identifies hom with
     proof too, so the point
     survives — every one of the 141 occurrences has 2nd level = 3rd.  Note
     the measurement trap that produced the error: [Print] WRAPS a universe
     instance across lines, so a line-based [grep -o] silently misses a split
     one; flatten whitespace before counting.  The CONSTRAINT
     BLOCKS, by contrast, contain no [=] at all: every entry is a [<=] or a
     [<].  Reading the blocks alone would report this file as carrying no
     identification whatever, which is false.
   - ATTRIBUTION IS PROBED, NOT GUESSED, and there is no single culprit.  In
     [Section UniverseDonors] below, over [C : Category@{uo uh up}] with
     [Constraint uh < up], each of [@Monoidal C], [@Cartesian C],
     [@Terminal C] and [@CartesianMonoidal C] is REJECTED with "Cannot
     enforce up = uh because uh < up", while [x ~> y] and [id[x]] are
     ACCEPTED at those very levels.  Four donors, each sufficient on its
     own — but NOT four INDEPENDENT ones, and an audit corrected that word:
     [CartesianMonoidal] contains [RelevanceMonoidal] (Heunen_Vicary.v),
     which contains [SymmetricMonoidal] (Relevance.v) and so ultimately
     [Monoidal], so its rejection is INHERITED and at most THREE are
     independent.  Nothing in this file adds to it, and it is not claimed
     unavoidable — all four are declared over unannotated
     [Context {C : Category}], the minimization family this tree records
     elsewhere.  The donor
     [GroupObject] inherits it visibly, printing as
     [GroupObject@{u u0 u1} (C : Category@{u u0 u0})].
   - THE COST OVER [Mon] IS EXACTLY ONE LEVEL, and that is measured by
     printing both AND COMPARING THE BLOCKS ENTRY FOR ENTRY — the two
     blocks below are quoted WHOLE, not sampled.  [Mon@{u u0 u1 u2}] has
     type [Category@{u u0 u0} → Monoidal@{u u0} → Category@{u1 u0 u0}] and
     a block of TEN entries: the strict [u0 < u2]; [u <= u1] and
     [u0 <= u1]; and SEVEN bounds on the universes of the sigma that
     carries the objects — [u <= Projections.u0], [u <= projections.u0],
     [u <= projections.u1], [u0 <= Projections.u0], [u0 <= Projections.u1],
     [u0 <= projections.u0] and [u0 <= projections.u1].  Those seven come
     from [sigT] — more precisely from its PROJECTIONS, [projT1]'s own
     monomorphic [Projections.u0]/[Projections.u1] and a lowercase pair,
     which an isolating probe separates from merely FORMING the pair (a bare
     [{x : obj[C] & x ~> x}] acquires no [Projections.*] entry at all).  An
     earlier draft glossed them as "both of C's levels sit below the pair's";
     that is wrong — the pair's own level is a [max] and never appears.
     [GrpCat@{u u0 u1 u2 u3}] has type
     [Category@{u u0 u0} → CartesianMonoidal@{u u0 u1} → Category@{u2 u0 u0}]
     and a block of TWELVE entries: that same ten with [u2] renamed [u3]
     and [u1] renamed [u2], PLUS EXACTLY TWO more, [u <= u1] and
     [u0 <= u1], for the extra level [CartesianMonoidal] itself carries —
     bounded by both of C's levels, identified with neither.  That
     two-entry difference is the whole cost.  Likewise [Mon_Terminal] has
     type [Terminal@{u u0} → Terminal@{u2 u0}] against [GrpCat_Terminal]'s
     [Terminal@{u u0} → Terminal@{u3 u0}], and [Mon_Cartesian] concludes
     [Cartesian@{u2 u0}] against [GrpCat_Cartesian]'s [Cartesian@{u3 u0}]:
     in each pair a NEW level carries the objects of the constructed
     category, bounded below by both of C's levels and identified with
     neither, so a consumer loses nothing.
   - The strict [u0 < ·] entry is present in [Mon], [Mon_Cartesian] and
     [Mon_Terminal] already, at the same place in the same shape, so it is
     inherited rather than introduced; #503's header isolates it to setoid
     [rewrite] inside a [Program] obligation and does not name the supplying
     constant, and no better attribution is offered here.
   - NO [Set] ANYWHERE.  No universe instance printed for any of the 70
     constants contains [Set].

   NEGATIVES.  Three in the [Probes] section, of TWO KINDS kept lexically
   apart, plus four in [Section UniverseDonors]; each was stripped of its
   [Fail] and its failure kind read off the message.

   - TYPING.  (1) [@GroupObject C M x] for [M : @Monoidal C] — "The term M
     has type Monoidal while it is expected to have type
     CartesianMonoidal".  (2) [MonoidHom] applied to the raw
     [groupobject_is_monoid] fields — "The term groupobject_is_monoid has
     type MonoidObject x", where a [Monoid x] is wanted, so #503's class
     passage is genuinely load-bearing and not a convenience.
   - CONVERSION.  (3) [Mon_Forget ◯ GrpCat_Mon = GrpCat_Forget] — "The term
     eq_refl has type Mon_Forget ◯ GrpCat_Mon = Mon_Forget ◯ GrpCat_Mon
     while it is expected to have type Mon_Forget ◯ GrpCat_Mon =
     GrpCat_Forget".
   - FORMABILITY (universe).  The four donor rejections described above.

   Controls: every constant named in a negative is also named by a positive
   command in this file, so a rename upstream breaks the build rather than
   turning a negative vacuously green.  (An earlier draft said "a SUCCEEDING
   command", which is wrong for one of them: [groupobject_is_monoid]'s guard
   is [group_monoid]'s own body, which PRECEDES negative 2.  A
   control naming it after the negative has been added as well.)  Guarded:
   [GroupObject],
   [MonoidHom], [groupobject_is_monoid], [group_monoid], [GroupHom],
   [Mon_Forget], [GrpCat_Mon], [GrpCat_Forget], [Monoidal],
   [CartesianMonoidal], [Cartesian] and [Terminal] all appear in positive
   commands, the last four as bare [Check @Name] guards in the universe
   section so that a rename cannot make those four rejections succeed on a
   reference-not-found error.  Section-local [Universes]/[Constraint] do not
   leak: they relate only three freshly declared levels to each other.

   AXIOMS.  Every constant of this file reports "Closed under the global
   context" — the named ones (from the [.glob]) plus the [Program]
   obligations, which are invisible to a [.glob] sweep and must be queried by
   fully qualified name.  READ THE GRADE: that is a ONE-TIME measurement of
   the whole file.  The [make print-assumptions] gate carries a SELECTED 25
   of them permanently, so the ungated remainder — the leg lemmas, most
   Examples, and every obligation — is verified but not guarded against
   regression.

   NOT DELIVERED, with reasons.

   - No [Cocartesian GrpCat].  The coproduct of groups is not carried by the
     coproduct of the underlying objects (it is a free product), so nothing
     here dualises; #503 records the same for monoids, quoting Mac Lane 1950
     on the asymmetry.
   - No abelian/commutative group objects, and nothing about exponentials.
     Read the second half narrowly: an audit corrected an earlier draft that
     called the [Hom_Monoid] analogue a library gap.  It is not built HERE,
     but it EXISTS — Structure/Group/Representable.v's [exp_GroupObject]
     is a group structure on the hom-object, in a file this one does not
     require.
   - No infinite or indexed products: this matches [Cartesian], which is
     binary.
   - No monoidal structure on [GrpCat], so it is NOT claimed to be cartesian
     MONOIDAL, and the Eckmann-Hilton consequence (a group object in
     [GrpCat] is abelian) is neither stated nor proved.
   - [GrpCat_Mon] is proved FULL as well as faithful ([GrpCat_Mon_Full]),
     superseding an earlier draft of this header that said fullness was
     "neither proved nor refuted": an audit observed that the two hom types
     are convertible, so the identity section discharges it in three lines.
     Nothing is claimed either way about whether it reflects or creates
     limits.
   - No concrete instantiation: [Sets], [Coq], [Instance/Grp.v] and the rest
     are untouched, and in particular the [Grp_GroupObject] /
     [GroupObject_GrpObject] reconciliation of Instance/Grp.v is neither
     used nor related to [GrpCat].  A previous attempt to route this file
     through that reconciliation was rejected because it fixes C := [Sets]
     and would build a group object per point.
   - No [Isomorphism] or uniqueness statement for the product group object
     beyond what [Cartesian] itself supplies through [ump_products].
   - [prod_ext] is a general [Cartesian] fact and is NOT new: the identical
     statement at the identical generality is Theory/Lawvere/Sets.v's
     [prod_separates] (its dual is Construction/Cospan/Bridging.v).  It
     is redeclared here only because Theory/Lawvere/Sets.v is not in this
     file's closure; an earlier draft implied no analogue existed, which an
     audit refuted.  It is likewise not moved into Structure/Cartesian.v.

--------
nLab：https://ncatlab.org/nlab/show/group+object
 维基百科：https://en.wikipedia.org/wiki/Group_object

Mac Lane，《工作数学家的范畴》，第二版，第 III.6 节
 （“范畴中的组”），练习 1 和 2，按问题#343 的范围；
 Awodey，范畴论，第二版，第 4.1 节（组（C）构造）。

给定 a 中的组对象 (x, μ_X, η_X, ι_X) 和 (y, μ_Y, η_Y, ι_Y)
 笛卡尔幺半群范畴 C (Structure/Group.v)，态射 f : x ~> y
 是群对象的同态，当它与
 乘法和单位，

乘法平方 f ∘ μ_X ≈ μ_Y ∘ (f ⨂ f)
 单位三角形 f ∘ η_X ≈ η_Y

没有其他要求。 与反演的换向，
 f ∘ ι_X ≈ ι_Y ∘ f 是一个定理 ([GroupHom_inverse]) 而不是一个域：
 这是 Awodey 在第 4.1 节中的观察，这就是为什么 [GroupHom] 是
 从字面上看，是底层幺半群对象的 [MonoidHom]，而不是
 记录延长它。 组对象和这些态射形成一个范畴
 [GrpCat]，具有 C 和 [Mon C] 的忠实健忘函子； 当C有
 二进制产品和终端对象，[GrpCat] 也有它们，携带
 组件方面，C 的健忘函子将它们发送到 C 自己的 ON THE
 鼻子。

这里按顺序证明了什么

(1) [group_monoid] / [group_inverse] — 将 [GroupObject] 读取为
 mu/eta 演示文稿中 [Mon] 索引的内部 [Monoid]，
 并命名给定组对象的反转。 
(2) [GroupHom] 与 [group_hom_mappend] / [group_hom_mempty]，以及
 [GroupHom_inverse]，替换缺失字段的定理。 
(3) [GrpCat]、[GrpCat_Forget]（忠实）和 [GrpCat_Mon]（忠实）—
 练习 2 / Awodey 小组(C)。 
(4) [GroupObject_Product] 和 [GrpCat_Cartesian] — 二进制产品。 
(5) [GroupObject_Terminal] 和 [GrpCat_Terminal] — 端子组
 对象。 
(6) [GrpCat_Forget_*] — 健忘函子将两者发送给 C 自己的，位于
 莱布尼茨平等。 
(7) [GrpCat_Cartesian_tensor] / [GrpCat_Terminal_unit] — 两个相同
 没有超越 [CartesianMonoidal] 的假设的结构
 [GroupObject] 已经提出要求。 
(8) 探测部分：三负二类、四宇宙
 底片及其对照。

如何消耗第 503 期，以及在哪个等级

练习 1 的幺半群是 Theory/Algebra/Monoid/Product.v
 （[Monoid_Product]、[Mon_Cartesian]、[Mon_Terminal]）。 它被实例化了，
 没有受到谴责，并且实例化在三个不同的等级上工作，每个等级
 机器检查而不是断言：

- 明确的。 [grp_prod_monoid] 通过 [eq_refl] 显示
 [GroupObject_Product] IS 的底层幺半群
 [Monoid_Product (group_monoid X) (group_monoid Y)] — 整体
 记录，而不是比较图 — 和 [grp_prod_mappend] /
 [grp_prod_mempty] 将其两个结构图读回为
 [mon_prod_mu] / [mon_prod_eta]。 这取决于#503自己
 [monoid_round]、[Monoid]/[MonoidObject] 往返行程即将结束
 [eq_refl]。 
- 敞篷车。 [grp_exl_hom]、[grp_exr_hom]、[grp_fork_hom] 和
 [grp_one_hom]由#503的[mon_exl_hom]的[exact]放电，
 不带适配器的 [mon_exr_hom]、[mon_fork_hom] 和 [mon_one_hom]：
 [GroupHom] 球门和 [MonoidHom] 球门的类型相同
 转换。 没有一项关于乘法或单位的新义务
 发生在下面的任何地方。 
- 重复使用的证明形状。 [Monoid_Product] 的三个幺半群定律被取
 批发； 只有逆定律和两个逆定律
 ([grp_prod_left_inverse]、[grp_prod_right_inverse])是新作品，
 他们的腿引理遵循 #503 的 [mon_prod_assoc_leg] 的形状。

什么不能被实例化，以及为什么——测量

#503 声明其一半超过任意幺半群基数 M。此文件不能：
 [GroupObject] 的声明优于 [CartesianMonoidal]，因为它有两个
 逆定律以复制/丢弃词汇书写（Δ 和 [eliminate]）
 裸露的 [Monoidal] 不提供该功能。 固定为负 1
 下面——打字失败，“术语 M 具有 Monoidal 类型，而它是
 预计具有 CartesianMonoidal 类型” — 与控制
 [CartesianMonoidal]。 所以两个文件之间的范围差异是
 关于组对象定义的事实，而不是它的弱点
 开发，并且没有提供绕过它的路线。

安慰是真实的并且被传递：因为笛卡尔幺半群
 范畴 IS 笛卡尔（福克斯定理、[CartesianMonoidal_Cartesian]、
 Structure/Monoidal/Heunen_Vicary/Cartesian.v) 及其单位 IS 终端
 ([SemicartesianMonoidal_Terminal])、[GrpCat]成本的有限积
 根本没有假设：[GrpCat_Cartesian_tensor] 和
 [GrpCat_Terminal_unit] 实例化这两个点的一般定理，并且
 [grpcat_tensor_product] / [grpcat_unit_terminal] 由 [eq_refl] 记录
 然后乘积由张量携带，终端对象由 I 携带。 
一般形式被保留，并且严格来说更一般：它们采用
 [Cartesian C] 和 [Terminal C] 不假定与 ⨂ 兼容，
 正如#503 所做的那样。

逆守恒定理及其代价

[GroupHom_inverse] 是十条战术线。 它的内容是元素级的
 参数“f(a⁻1) 是 f(a) 的左逆，并且左逆是唯一的”，
 以图解方式运行： reshape (f ∘ ι_x) ⨂ f as (f ⨂ f) ∘ (ι_x ⨂ id) by
 [bimap_comp]，将 f 通过乘法平方推出，折叠什么
 由 SOURCE 对象的 [left_inverse] 保留，并以该单元结束
 三角形。 TARGET 中左逆的唯一性是
 Structure/Group/Proofs.v 的 [left_inverse_unique]，这是
 对角线的自然性和 I 的终结性已耗尽——该列表是
 并不详尽，遗漏很重要：审计发现捐助者的
 证明也可以 [rewrite <- right_inverse] (Structure/Group/Proofs.v)
 并使用 [mappend_assoc_sym] 和 [mempty_*_diagonal] 助手。
所以
 更正此标头的早期草稿提出的声明：[right_inverse] 确实
 [GroupHom_inverse] 自己的战术脚本中没有出现，但定理却出现了
 通过 [left_inverse_unique] 依赖于目标的 [right_inverse]。 不对称的是脚本，而不是依赖关系，并将其称为“一个
 值得记录的不对称”是错误的。 [MonoidHom] 之外没有任何假设
 需要。 逆定律的两个右相关读数
 （[left_inverse_r]、[right_inverse_r]）的存在只是为了满足 [rewrite] 的要求
 括起来并且不包含任何内容。

名字。 范畴是[GrpCat]，而不是[Grp]，原因是
 衡量而不是审美：Instance/Grp.v 已经声明
 [Grp : Category] — [Sets] 之上的组的具体范畴 — 一起
 与 [Grp_Cartesian]、XPOTECT92X、[Grp_Forget]
 和 [Grp_Forget_Faithful]，发现与 [rg] 发生 5 次碰撞
 整棵树。 早期的草案说是四个； 审计发现第五个。 的
 原因值得记录，因为明显的解释是错误的：它是
 不是 [#[export] 程序实例]形状，因为 [Grp_Cartesian] 有
 正是那个形状并且被发现了。 该列表是根据四个猜测构建的
 名称而不是从该文件自己声明的名称派生出来
 重命名 — [GrpCat_Forget_Faithful] 映射到 [Grp_Forget_Faithful]，并且
 这个名字根本就没有被搜索过。 该文件不需要这些
 模块，因此其中没有任何歧义； 重命名的存在使得
 消费者可以在没有资格的情况下进口两者。

两项工程发现，都与名称有关，而不是与数学有关。

- [inverse] 是 Structure/Group.v 下游的关键字。 其
 符号引用了标记 [Notation "'inverse' [ G ]"]，这使得
 [inverse] 是一个终端符号：[@inverse _ _ _ G] 是一个 PARSE 错误
 （“语法错误：‘@’后应有 [global] 或 [pattern_ident]”），以及
 记录文字字段名称也被拒绝——在现实中
 多区域形状 [{| groupobject_is_monoid := _ ; inverse := _ |}]，
 与“语法错误：['|}'] 预计在 [record_declaration] 之后”。 的
 形状很重要，这个标题的早期草案犯了错误
 针对单字段文字引用该消息：使用 [inverse]
 首先，消息是“语法错误：[record_declaration]
 预计在“{|”之后。两者都是解析错误，因此没有任何类型的声明更改。
两者都不能作为探针固定：[Fail] 捕获精化失败，
 即使在 [Fail] 内部，解析错误也会中止文件 - 这就是为什么
 这两项发现被记录在散文中，而不是受到保护。 的
 符号本身采用 OBJECT 并将实例留给解析，
 这在 Structure/Group/Proofs.v 中很好，但在这里不行，其中有几个
 不同对象上的组对象同时在范围内。 两者都是
 解决方法：[group_inverse] 通过限定的名称命名实例
 [@Category.Structure.Group.inverse]（合格的路径在之后解析
 [@]) 和 [GroupObject_Product] / [GroupObject_Terminal] 均采用
 [Build_GroupObject] 而不是记录文字语法。 [group_inverse_is] 由 [eq_refl] 记录访问者和
 符号同意。 - [fork] 和 [fork_respects] 处于阴影状态。
结构/Monoidal/Relevance.v
 声明自己的 [fork]（对角线配对）和自己的
 [fork_respects] 实例，并且 [Heunen_Vicary.v] 重新导出 Relevance，因此
 仅仅命名 [CartesianMonoidal] 就可以将两者纳入范围内。 因此
 [GrpCat_Cartesian] 必须为其字段写入 [Cartesian.fork] — 相同
 Heunen_Vicary/Cartesian.v 使用的解决方法 - 及其尊重
 义务必须命名为 [Cartesian.fork_respects]。 [△] 符号是
 不受影响：Structure/Cartesian.v 根据已解析的结果声明它
 恒定，因此它始终表示产品的配对。

强项，首先要严格衡量。 [eq_refl] 附近有 20 个示例。 十是鉴定：[group_monoid]的两张结构图，
 反转访问器，[GroupObject_Product]的四个读数，
 终端 monoid，以及两个 [GrpCat_Mon]/[GrpCat_Forget] 协议。 [GrpCat_Forget]自带产品的六项记录，终端对象，
 两个投影、配对以及 C 自己的独特地图； 两个那个
 [GrpCat_Mon] 对 [Mon C] 执行相同的操作； 第二个是无假设的
 (7) 的实例将张量和终端对象的乘积
 在 I. 四个
 同态引理更强，是 CONVERSIONS 而不是
 项的平等性。
一个后备方案，它是一种反驳而不是一种
 弱化：[Mon_Forget ◯ GrpCat_Mon = GrpCat_Forget] 被拒绝
 [eq_refl]（阴性3），诊断为[Compose]正在重建其
 [fmap_respects]、[fmap_id] 和 [fmap_comp] 字段作为新的证明项
 虽然两个数据字段在鼻子上一致 - 两个控件
 [grpcat_mon_forget_obj] 和 [grpcat_mon_forget_map] 正是如此
 协议。 该标头的早期草案证明不提供 [≈]
 形式是说它“需要函子上的 hom-setoid”，其中
 “将函子范畴拉入 [Theory/Algebra] 的闭包中
 文件”。 那是错误的，审计驳斥了它：[Functor_Setoid] 和
 [Functor_StrictEq_Setoid] 是 Theory/Functor.v，这
 文件已经需要，并且不涉及函子范畴。
的
 因此，方程被给出，并且在两个可用的更严格的情况下
 优点：[forget_compose_strict] 证明了这一点
 [Functor_StrictEq_Setoid] 与每个对象组件字面意义上的 [eq_refl]。 所以负 3 准确地表达了它所说的内容，仅此而已 - 复合不是
 相同的记录，而两个函子作为函子严格相等。

宇宙。 在约束块中测量并读取活页夹，
 两人在重要的方面存在分歧。

- BINDER 携带文件中的唯一标识。 每个常数
 绑定 [C] 的能力优于 [C : Category@{u u0 u0}] — C 的 hom 和证明
 已确定的宇宙——在 55 年间，出现了 110 个这样的宇宙
 命名常量（总共 70 个中的 140 个）。 还有另外一个
 [Category@{...}] 实例，以及此标头的早期草稿错误
 说没有：[GrpCat]自己的RESULT类型[Category@{u2 u0 u0}]，
 下面的 [Mon] 比较项目中引用了该内容。 它将 hom 标识为
 也有证明，所以重点是
 幸存下来 — 141 次事件中的每一次都有 2 级 = 3 级。 注意事项
 产生错误的测量陷阱：[Print] WRAPS a Universe
 跨线实例，因此基于线的 [grep -o] 会默默地错过分割
 一； 在计数之前压平空白。
约束
 相比之下，块根本不包含 [=]：每个条目都是 [<=] 或
 [<]。 单独读取块会报告该文件不包含
 任何恒等证明，这是错误的。 - 归因是探查的，而不是猜测的，并且不存在单一的罪魁祸首。 在
 [Section UniverseDonors] 以下，高于 [C : Category@{uo uh up}]
 [Constraint uh < up]、[@Monoidal C]、[@Cartesian C] 中的每一个、
 [@Terminal C] 和 [@CartesianMonoidal C] 被拒绝，并显示“无法
 强制 up = uh 因为 uh < up"，而 [x ~> y] 和 [id[x]] 是
 在这些水平上被接受。
四个捐助者，每个捐助者都足够
 自己的——但不是四个独立的，审计更正了这个词：
 [CartesianMonoidal] 包含 [RelevanceMonoidal] (Heunen_Vicary.v)，
 其中包含 [SymmetricMonoidal] (Relevance.v)，所以最终
 [Monoidal]，所以它的拒绝是继承的，最多三个
 独立。 此文件中没有任何内容添加到它，并且没有声明它
 不可避免的——所有四个都被声明为未注释的
 [Context {C : Category}]，这棵树记录的最小化族
 其他地方。 捐赠者
 [GroupObject] 明显继承了它，打印为
 XPTECT180X。 - [Mon] 的成本恰好是一个级别，这是通过以下方式衡量的
 打印两者并比较 BLOCKS ENTRY FOR ENTRY — 两者
 下面的块是整体引用的，而不是采样的。
[Mon@{u u0 u1 u2}] 有
 [Category@{u u0 u0} → Monoidal@{u u0} → Category@{u1 u0 u0}] 型和
 十个条目的块：严格的 [u0 < u2]； [u <= u1] 和
 XPTECT186X； 西格玛宇宙的七个界限
 携带物体 — [u <= Projections.u0]、[u <= projections.u0]、
 [u <= projections.u1]、[u0 <= Projections.u0]、[u0 <= Projections.u1]、
 [u0 <= projections.u0] 和 [u0 <= projections.u1]。 那七个人来了
 来自 [sigT] — 更准确地说，来自 [projT1] 自己的投影
 单态 [Projections.u0]/[Projections.u1] 和一个小写字母对，
 隔离探针将其与仅仅形成该对（裸露的
 [{x : obj[C] & x ~> x}] 根本不获取 [Projections.*] 条目）。 安
 早期的草案将它们注释为“两个 C 的水平都低于这对水平”；
 这是错误的——两人各自的水平仪是 [max] 并且从未出现。
[GrpCat@{u u0 u1 u2 u3}]有类型
 保护202X
 和一组 12 个条目：与 [u2] 重命名为 [u3] 的相同 10 个条目
 [u1] 更名为 [u2]，另外还有另外两个，[u <= u1] 和
 [u0 <= u1]，[CartesianMonoidal] 本身携带的额外级别 —
 受两个 C 水平的限制，不与任何一个水平相同。 那
 两次差额就是全部成本。 同样 [Mon_Terminal] 有
 类型 [Terminal@{u u0} → Terminal@{u2 u0}] 与 [GrpCat_Terminal] 的对比
 [Terminal@{u u0} → Terminal@{u3 u0}] 和 [Mon_Cartesian] 结论
 [Cartesian@{u2 u0}] 与 [GrpCat_Cartesian] 的 [Cartesian@{u3 u0}]：
 在每一对中，一个新的级别承载所构造的对象
 范畴，由以下两个 C 级别界定并标识为
 两者都不是，所以消费者没有任何损失。
- 严格的 [u0 < ·] 条目存在于 [Mon]、[Mon_Cartesian] 和
 [Mon_Terminal] 已经在相同的位置相同的形状，所以它是
 继承而不是引入； #503 的标头将其隔离到 setoid
 [rewrite] 包含在 [Program] 义务中，并且未指定提供者
 不变，这里没有提供更好的归因。 - 任何地方都没有 [Set]。 没有为 70 个中的任何一个打印 Universe 实例
 常量包含 [Set]。

负面影响。 [Probes] 部分中的三个，按词汇方式保存的两种
 分开，再加上 [Section UniverseDonors] 中的四个； 每个都被剥夺了
 [Fail] 及其故障类型读取消息。

- 打字。 (1) [@GroupObject C M x] 对于 [M : @Monoidal C] — “术语 M
 具有 Monoidal 类型，而预期具有类型
 笛卡尔Monoidal”。 (2) [MonoidHom]应用于raw
 [groupobject_is_monoid] 字段 — “术语 groupobject_is_monoid 具有
 类型 MonoidObject x"，其中需要 [Monoid x]，所以 #503 的类
 通道是真正的承重而非便利。 
- 转换。 (3) [Mon_Forget ◯ GrpCat_Mon = GrpCat_Forget] —“术语
 eq_refl 的类型为 Mon_Forget ◯ GrpCat_Mon = Mon_Forget ◯ GrpCat_Mon
 而预期类型为 Mon_Forget ◯ GrpCat_Mon =
 GrpCat_Forget”。
 - 可成型性（宇宙）。 上述四次捐赠者拒绝。

控制：每个以负数命名的常量也以正数命名
 命令在此文件中，因此重命名上游会破坏构建而不是
 将负片变为空绿色。 （较早的草案称“一个成功的
 命令”，这对于其中之一来说是错误的：[groupobject_is_monoid] 的守卫
 是 [group_monoid] 自己的主体，位于负数 2 之前。 A
 控制在添加否定后命名它。） 受保护：
 XPTECT237X，
 [MonoidHom]、[groupobject_is_monoid]、[group_monoid]、[GroupHom]、
 [Mon_Forget]、[GrpCat_Mon]、[GrpCat_Forget]、[Monoidal]、
 [CartesianMonoidal]、[Cartesian]和[Terminal]都出现在正面
 命令，最后四个作为宇宙中裸露的 [Check @Name] 守卫
 部分，以便重命名不能使这四个拒绝在
 未找到参考错误。 局部部分 [Universes]/[Constraint] 不
 泄漏：它们仅将三个新声明的级别相互关联。

公理。 该文件的每个常量都报告“在全局下关闭”
 context" — 命名的（来自 [.glob]）加上 [Program]
 义务，对于 [.glob] 扫描来说是不可见的，必须通过以下方式查询
 完全限定名称。 阅读成绩：这是一次性测量
 整个文件。 [make print-assumptions] 门带有 SELECTED 25
 其中永久的，所以未门控的其余部分 - 腿引理，大多数
 例子和每项义务——经过验证但不加以防范
 回归。

未交付，有原因。

- 没有 [Cocartesian GrpCat]。 群的余积不由
 底层对象的余积（它是一个免费的产品），所以什么也没有
 这里双重化； #503 对于幺半群记录相同，引用 Mac Lane 1950
 关于不对称性。 - 没有阿贝尔/交换群对象，也没有关于指数的内容。 仔细阅读后半部分：审计更正了早期的草稿
 将 [Hom_Monoid] 称为库间隙模拟。 它不是在这里建造的，
 但它存在——Structure/Group/Representable.v 的 [exp_GroupObject]
 是 hom 对象上的组结构，在文件中这不是
 要求。 - 没有无限或索引产品：这与 [Cartesian] 匹配，这是
 二进制。
- [GrpCat] 上没有幺半群结构，因此不声称它是笛卡尔结构
 MONOIDAL 和 Eckmann-Hilton 推论（群对象）
 [GrpCat] 是阿贝尔算子）既没有被陈述也没有被证明。 - [GrpCat_Mon] 被证明是完整且忠实的 ([GrpCat_Mon_Full])，
 取代此标题的早期草案，该草案表示完整性是
 “既没有被证明也没有被反驳”：审计发现这两种 hom 类型
 是可转换的，因此恒等部分将其分三行释放。 对于它是反映还是创造，没有任何说法
 限制。 - 没有具体实例化：[Sets]、[Coq]、[Instance/Grp.v] 等
 未受影响，特别是 [Grp_GroupObject] /
 Instance/Grp.v 的 [GroupObject_GrpObject] 协调既不是
 使用或与 [GrpCat] 无关。
先前尝试路由此文件
 通过该协调被拒绝，因为它修复了 C := [Sets]
 并会为每个点构建一个组对象。 - 产品组对象没有 [Isomorphism] 或唯一性声明
 超出 [Cartesian] 本身通过 [ump_products] 提供的功能。 - [prod_ext] 是一般的 [Cartesian] 事实，并不是新的：相同
 具有相同一般性的声明是 Theory/Lawvere/Sets.v 的
 [prod_separates]（其双重是 Construction/Cospan/Bridging.v）。 它
 在这里重新声明只是因为 Theory/Lawvere/Sets.v 不在其中
 文件关闭； 较早的草案暗示不存在类似物，
 审计反驳。 它同样不会移至 Structure/Cartesian.v 中。
*)

Section GroupHomomorphism.

Context {C : Category}.
Context `{CM : @CartesianMonoidal C}.

(** ** Reading a group object as an internal monoid / ** 将群对象作为内部幺半群来读取 *)

(*
The underlying monoid of a group object, in the [mu]/[eta] presentation
   that [Mon] is indexed by.  [groupobject_is_monoid] lands in
   Structure/Monoid.v's [MonoidObject]; [Monoid_of_MonoidObject]
   (Theory/Algebra/Monoid/Product.v) renames its fields.  Both steps are at
   the SAME monoidal base, so no tensor changes hands.

--------
群对象的底层幺半群，在 [mu]/[eta] 的表示中由 [Mon] 索引。[groupobject_is_monoid] 落在 Structure/Monoid.v 的 [MonoidObject] 中；[Monoid_of_MonoidObject]（Theory/Algebra/Monoid/Product.v）重命名其字段。这两个步骤都在相同的幺半群基础上进行，因此没有张量交换。
*)
Definition group_monoid {x : C} (G : GroupObject x) : Monoid x :=
  Monoid_of_MonoidObject (@groupobject_is_monoid _ _ _ G).

(*
The inversion morphism of a NAMED group object.  Declared because
   Structure/Group.v's [inverse[G]] notation quotes the token [inverse],
   which makes it a keyword: [@inverse _ _ _ G] is then a parse error, and
   [inverse[x]] leaves the instance to resolution.  This accessor names the
   instance explicitly; the two agree by [eq_refl] ([group_inverse_is]).

--------
一个命名群对象的逆运算态射。声明它是因为 Structure/Group.v 的 [inverse[G]] 符号引用了标记 [inverse]，这使它成为一个关键字：[@inverse _ _ _ G] 然后是解析错误，而 [inverse[x]] 将实例交由解析。这个访问器明确命名了实例；两者通过 [eq_refl] ([group_inverse_is]) 保持一致。
*)
Definition group_inverse {x : C} (G : GroupObject x) : x ~> x :=
  @Category.Structure.Group.inverse _ _ _ G.

Example group_inverse_is {x : C} (G : GroupObject x) :
  group_inverse G = inverse[x] := eq_refl.

(*
The passage costs nothing: the multiplication and unit of [group_monoid G]
   ARE [G]'s own, at Leibniz equality.

--------
这段文字不花费任何费用：[group_monoid G] 的乘法和单位属于 [G] 自身，在莱布尼茨等式下。
*)
Example group_monoid_mu {x : C} (G : GroupObject x) :
  mu[group_monoid G] = mappend[G] := eq_refl.

Example group_monoid_eta {x : C} (G : GroupObject x) :
  eta[group_monoid G] = mempty[G] := eq_refl.

(** ** Group homomorphisms / ** 群同态 *)

(*
A homomorphism of group objects IS a homomorphism of the underlying monoid
   objects.  There is no inverse-preservation field; that it holds anyway is
   [GroupHom_inverse] below.  A plain [Definition] rather than a [Class]: the
   equality with [MonoidHom] is then definitional, so every lemma of
   Theory/Algebra/Monoid/Hom.v and Theory/Algebra/Monoid/Product.v about
   monoid homomorphisms applies to group homomorphisms with no adapter.

--------
群对象的同态是底层幺半群对象的同态。没有逆元素保持的字段；然而它仍然成立，如下面的 [GroupHom_inverse] 所示。一个普通的 [Definition] 而不是 [Class]：与 [MonoidHom] 的相等性因此是定义上的，所以 Theory/Algebra/Monoid/Hom.v 和 Theory/Algebra/Monoid/Product.v 中关于幺半群同态的每一个引理都适用于群同态，并且不需要适配器。
*)
Definition GroupHom {x y : C} (Gx : GroupObject x) (Gy : GroupObject y)
           (f : x ~> y) : Type :=
  MonoidHom (group_monoid Gx) (group_monoid Gy) f.

Lemma group_hom_mappend {x y : C} {Gx : GroupObject x} {Gy : GroupObject y}
      {f : x ~> y} (F : GroupHom Gx Gy f) :
  f ∘ mappend[Gx] ≈ mappend[Gy] ∘ f ⨂ f.
Proof. exact (@hom_mu _ _ _ _ _ _ _ F). Qed.

Lemma group_hom_mempty {x y : C} {Gx : GroupObject x} {Gy : GroupObject y}
      {f : x ~> y} (F : GroupHom Gx Gy f) :
  f ∘ mempty[Gx] ≈ mempty[Gy].
Proof. exact (@hom_eta _ _ _ _ _ _ _ F). Qed.

(** ** Preservation of the inverse is a THEOREM / ** 逆元的保持是一个定理 *)

(*
Right-associated readings of the two inverse laws, in the bracketing that
   [rewrite] leaves after [rewrite <- !comp_assoc].

--------
两个逆律的右结合解读，在 [rewrite <- !comp_assoc] 之后 [rewrite] 保留的括号中。
*)
Lemma left_inverse_r {x : C} {G : GroupObject x} :
  mappend[G] ∘ (group_inverse G ⨂ id[x] ∘ ∆x) ≈ mempty[G] ∘ eliminate.
Proof. rewrite comp_assoc; apply left_inverse. Qed.

Lemma right_inverse_r {x : C} {G : GroupObject x} :
  mappend[G] ∘ (id[x] ⨂ group_inverse G ∘ ∆x) ≈ mempty[G] ∘ eliminate.
Proof. rewrite comp_assoc; apply right_inverse. Qed.

(*
Awodey, Category Theory 2nd ed., Section 4.1: a morphism of the underlying
   monoid objects automatically commutes with the inversions, so the
   internal-group hom class needs no inverse-preservation axiom.

   The elementwise argument is "f(a⁻¹) is a left inverse of f(a), and left
   inverses are unique".  Diagrammatically: reshape (f ∘ ι_x) ⨂ f as
   (f ⨂ f) ∘ (ι_x ⨂ id) with [bimap_comp], push f out through the
   multiplication square [group_hom_mappend], collapse the remainder by the
   SOURCE object's [left_inverse], and finish with the unit triangle
   [group_hom_mempty].  Uniqueness of left inverses in the TARGET is
   Structure/Group/Proofs.v's [left_inverse_unique], which is where the
   diagonal's naturality and the terminality of I are spent.

   Note what is NOT used: [right_inverse] of either object appears nowhere in
   this proof.

--------
Awodey，《范畴论》第2版，第4.1节：底层的单子对象的态射自动与逆元交换，因此内部群类不需要逆元保持公理。

逐元素论证是“f(a⁻¹) 是 f(a) 的左逆元，并且左逆元是唯一的”。用图示表示：将 (f ∘ ι_x) ⨂ f 重排为 (f ⨂ f) ∘ (ι_x ⨂ id) 与 [bimap_comp]，通过乘法方格 [group_hom_mappend] 将 f 推出去，利用源对象的 [left_inverse] 折叠剩余部分，然后用单位三角 [group_hom_mempty] 完成。在目标对象中左逆元的唯一性可见于 Structure/Group/Proofs.v 的 [left_inverse_unique]，这是对角自然变换和 I 的终对象性被使用的地方。

注意未使用的内容：任何对象的 [right_inverse] 在此证明中未出现。
*)
Theorem GroupHom_inverse {x y : C} {Gx : GroupObject x} {Gy : GroupObject y}
        {f : x ~> y} (F : GroupHom Gx Gy f) :
  f ∘ group_inverse Gx ≈ group_inverse Gy ∘ f.
Proof.
  apply left_inverse_unique.
  assert (HB : (f ∘ group_inverse Gx) ⨂ f
                 ≈ f ⨂ f ∘ group_inverse Gx ⨂ id[x]).
  { rewrite <- bimap_comp; now rewrite id_right. }
  rewrite HB; clear HB.
  rewrite comp_assoc.
  rewrite <- (group_hom_mappend F).
  rewrite <- !comp_assoc.
  rewrite left_inverse_r.
  rewrite comp_assoc.
  now rewrite (group_hom_mempty F).
Qed.

(** ** The category of group objects / ** 群对象的范畴 *)

Lemma GroupHom_id {x : C} (G : GroupObject x) : GroupHom G G id.
Proof. exact (MonoidHom_id (group_monoid G)). Qed.

Lemma GroupHom_comp {x y z : C} {Gx : GroupObject x} {Gy : GroupObject y}
      {Gz : GroupObject z} {f : y ~> z} {g : x ~> y} :
  GroupHom Gy Gz f → GroupHom Gx Gy g → GroupHom Gx Gz (f ∘ g).
Proof. exact MonoidHom_comp. Qed.

Lemma GroupHom_equiv {x y : C} {Gx : GroupObject x} {Gy : GroupObject y}
      {f g : x ~> y} : f ≈ g → GroupHom Gx Gy f → GroupHom Gx Gy g.
Proof. exact MonoidHom_equiv. Qed.

(*
Mac Lane, CWM 2nd ed., Section III.6, Exercise 2 (as scoped by issue #343);
   Awodey Section 4.1's Group(C).  Objects are objects of C equipped with a
   group-object structure, morphisms are C-morphisms equipped with a proof of
   homomorphy, and equivalence is equivalence of the underlying morphisms —
   the same sigma packaging as [Mon] (Theory/Algebra/Monoid/Hom.v) and as
   [Sub] (Construction/Subcategory.v).

   Named [GrpCat] and not [Grp]: Instance/Grp.v already declares
   [Grp : Category], the concrete category of groups over [Sets], along with
   [Grp_Cartesian], [Grp_Terminal], [Grp_Forget] and
   [Grp_Forget_Faithful] — five collisions,
   measured with [rg] rather than guessed.  This file requires none of those
   modules, so nothing is ambiguous here; the rename exists so that a
   consumer may import both.

--------
Mac Lane, CWM 第二版，第 III.6 节，练习 2（按问题 #343 的范围）；
Awodey 第 4.1 节的 Group(C)。对象是配备了群对象结构的 C 的对象，态射是配备了同态证明的 C-态射，等价性是底层态射的等价性——与 [Mon]（Theory/Algebra/Monoid/Hom.v）和 [Sub]（Construction/Subcategory.v）中的 Sigma 封装相同。

命名为 [GrpCat] 而不是 [Grp]：Instance/Grp.v 已经声明了 [Grp : Category]，即 [Sets] 上的群的具体范畴，以及 [Grp_Cartesian]、[Grp_Terminal]、[Grp_Forget] 和 [Grp_Forget_Faithful]——五个冲突，使用 [rg] 测量而非猜测。该文件不依赖于那些模块，因此这里没有歧义；重命名存在的目的是为了使使用者可以同时导入两者。
*)
Program Definition GrpCat : Category := {|
  obj     := { x : C & GroupObject x };
  hom     := fun X Y => { f : `1 X ~> `1 Y & GroupHom `2 X `2 Y f };
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id      := fun X => (id; GroupHom_id `2 X);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; GroupHom_comp `2 f `2 g)
|}.

(*
The forgetful functor to C, faithful by construction: morphism equivalence
   in [GrpCat] IS equivalence of the underlying C-morphisms.

--------
到 C 的忘记函子，由构造可知是忠实的：在 [GrpCat] 中的态射等价就是底层 C-态射的等价。
*)
Program Definition GrpCat_Forget : GrpCat ⟶ C := {|
  fobj := fun X => `1 X;
  fmap := fun _ _ f => `1 f
|}.

#[export] Instance GrpCat_Forget_Faithful : Faithful GrpCat_Forget.
Proof. constructor; intros X Y f g E; exact E. Qed.

(*
The forgetful functor to internal monoids.  Its arrow action is the
   IDENTITY on the underlying data — that is exactly the content of
   [GroupHom] being [MonoidHom] rather than a record extending it.

--------
指向内部幺半群的遗忘函子。它在箭头上的作用是在底层数据上做恒等操作——这正是 [GroupHom] 是 [MonoidHom] 而不是扩展它的记录的内容。
*)
Program Definition GrpCat_Mon : GrpCat ⟶ Mon C := {|
  fobj := fun X => (`1 X; group_monoid `2 X);
  fmap := fun _ _ f => (`1 f; `2 f)
|}.

#[export] Instance GrpCat_Mon_Faithful : Faithful GrpCat_Mon.
Proof. constructor; intros X Y f g E; exact E. Qed.

(*
And FULL, which costs three lines because the two hom types are
   CONVERTIBLE: [fobj[GrpCat_Mon] X ~{Mon C}~> fobj[GrpCat_Mon] Y] is
   [{f & MonoidHom (group_monoid `2 X) (group_monoid `2 Y) f}], and that IS
   [X ~{GrpCat}~> Y] by [GroupHom]'s definition.  So the section is the
   identity and its coherence is [reflexivity].

--------
以及 FULL，它花费三行，因为两种同类类型是可转换的：[fobj[GrpCat_Mon] X ~{Mon C}~> fobj[GrpCat_Mon] Y] 是 [{f & MonoidHom (group_monoid `2 X) (group_monoid `2 Y) f}]，并且根据 [GroupHom] 的定义，这确实是 [X ~{GrpCat}~> Y]。因此，该段是恒等映射，其一致性是 [reflexivity]。
*)
#[export] Instance GrpCat_Mon_Full : Full GrpCat_Mon.
Proof.
  unshelve econstructor.
  - intros X Y g; exact g.
  - intros X Y g; simpl; reflexivity.
Qed.

(*
[Mon_Forget ◯ GrpCat_Mon] and [GrpCat_Forget] agree on objects and on
   morphisms, at Leibniz equality.  The whole functor RECORDS are not
   compared; see the probe section at the end of the file.

--------
[Mon_Forget ◯ GrpCat_Mon] 和 [GrpCat_Forget] 在对象和态射上都一致，在莱布尼兹等式下。整个函子 RECORDS 并未进行比较；请参见文件末尾的探针部分。
*)
Example grpcat_mon_forget_obj (X : GrpCat) :
  fobj[Mon_Forget] (fobj[GrpCat_Mon] X) = fobj[GrpCat_Forget] X := eq_refl.

Example grpcat_mon_forget_map (X Y : GrpCat) (f : X ~> Y) :
  fmap[Mon_Forget] (fmap[GrpCat_Mon] f) = fmap[GrpCat_Forget] f := eq_refl.

(*
The two functors are moreover EQUAL in [Functor_StrictEq_Setoid], with
   every object component literally [eq_refl].  What negative 3 at the end of
   the file refutes is the strictly stronger claim that the composite is the
   SAME RECORD as [GrpCat_Forget]; [Compose] rebuilds the three law fields,
   so that fails while this succeeds.  No functor category is needed —
   [Functor_StrictEq_Setoid] is Theory/Functor.v, already required.

--------
此外，这两个函子在 [Functor_StrictEq_Setoid] 中是相等的，每个对象分量字面上为 [eq_refl]。文件末尾的 -3 驳斥了一个更强的说法，即该复合函子是与 [GrpCat_Forget] 相同的记录；[Compose] 重建了三个法律字段，因此该说法失败，而这个成功。无需任何函子范畴 — [Functor_StrictEq_Setoid] 是 Theory/Functor.v，已经被需要。
*)
Example forget_compose_strict :
  @equiv _ (@Functor_StrictEq_Setoid GrpCat C)
    (Mon_Forget ◯ GrpCat_Mon) GrpCat_Forget.
Proof. exists (fun _ => eq_refl); intros; cat. Qed.

(** ** Binary products / ** 二元产品 *)

Section GrpProduct.

Context `{CA : @Cartesian C}.

(*
Two morphisms into a product agree when their components do.  A general
   [Cartesian] fact, declared here for want of a second consumer.

--------
当两个态射的各个分量相同时，它们进入一个积的态射也相同。这里声明的一个一般性事实，是因为缺少第二个使用者。
*)
Lemma prod_ext {x y z : C} (f g : z ~> x × y) :
  exl ∘ f ≈ exl ∘ g → exr ∘ f ≈ exr ∘ g → f ≈ g.
Proof.
  intros Hl Hr.
  rewrite <- (prod_fork_eta f), <- (prod_fork_eta g).
  apply fork_inv; split; assumption.
Qed.

Section GrpProductData.

Context {x y : C} (X : GroupObject x) (Y : GroupObject y).

(* The componentwise inversion. / 逐分量求逆 *)
Definition grp_prod_inverse : x × y ~> x × y :=
  split (group_inverse X) (group_inverse Y).

Notation MU := (mon_prod_mu (group_monoid X) (group_monoid Y)).
Notation ETA := (mon_prod_eta (group_monoid X) (group_monoid Y)).

(*
One component of the left inverse law.  [p] is a projection: [Hmu] says it
   commutes with the two multiplications, [Hinv] with the two inversions.
   The diagonal's naturality is what carries [p] past ∆, and the terminality
   of I ([eliminate_comp]) is what absorbs it on the other side.

--------
左逆律的一个组成部分。[p] 是一个投影：[Hmu] 表示它与两个乘法运算可交换，[Hinv] 与两个取逆运算可交换。对角线的自然性使得 [p] 可以穿过 ∆，I 的终端性 ([eliminate_comp]) 则使其在另一侧被吸收。
*)
Lemma grp_prod_left_leg {z : C} (Z : GroupObject z) (p : x × y ~> z)
      (Hmu : p ∘ MU ≈ mappend[Z] ∘ bimap p p)
      (Hinv : p ∘ grp_prod_inverse ≈ group_inverse Z ∘ p) :
  p ∘ (MU ∘ grp_prod_inverse ⨂ id[x × y] ∘ ∆(x × y))
    ≈ mempty[Z] ∘ eliminate.
Proof.
  rewrite !comp_assoc, Hmu.
  rewrite <- (comp_assoc mappend[Z] (bimap p p) _).
  rewrite <- bimap_comp, Hinv, id_right.
  assert (E : (group_inverse Z ∘ p) ⨂ p
                ≈ group_inverse Z ⨂ id[z] ∘ bimap p p)
    by (rewrite <- bimap_comp; now rewrite id_left).
  rewrite E; clear E.
  rewrite <- !comp_assoc.
  rewrite (diagonal_natural _ _ p); simpl.
  rewrite (comp_assoc (group_inverse Z ⨂ id[z]) ∆z p), comp_assoc.
  rewrite left_inverse_r.
  rewrite <- comp_assoc.
  now rewrite eliminate_comp.
Qed.

Lemma grp_prod_right_leg {z : C} (Z : GroupObject z) (p : x × y ~> z)
      (Hmu : p ∘ MU ≈ mappend[Z] ∘ bimap p p)
      (Hinv : p ∘ grp_prod_inverse ≈ group_inverse Z ∘ p) :
  p ∘ (MU ∘ id[x × y] ⨂ grp_prod_inverse ∘ ∆(x × y))
    ≈ mempty[Z] ∘ eliminate.
Proof.
  rewrite !comp_assoc, Hmu.
  rewrite <- (comp_assoc mappend[Z] (bimap p p) _).
  rewrite <- bimap_comp, Hinv, id_right.
  assert (E : p ⨂ (group_inverse Z ∘ p)
                ≈ id[z] ⨂ group_inverse Z ∘ bimap p p)
    by (rewrite <- bimap_comp; now rewrite id_left).
  rewrite E; clear E.
  rewrite <- !comp_assoc.
  rewrite (diagonal_natural _ _ p); simpl.
  rewrite (comp_assoc (id[z] ⨂ group_inverse Z) ∆z p), comp_assoc.
  rewrite right_inverse_r.
  rewrite <- comp_assoc.
  now rewrite eliminate_comp.
Qed.

Lemma grp_prod_eta_leg {z : C} (Z : GroupObject z) (p : x × y ~> z)
      (Heta : p ∘ ETA ≈ mempty[Z]) :
  p ∘ (ETA ∘ @eliminate _ _ _ (x × y))
    ≈ mempty[Z] ∘ @eliminate _ _ _ (x × y).
Proof. now rewrite comp_assoc, Heta. Qed.

Lemma grp_prod_left_inverse :
  MU ∘ grp_prod_inverse ⨂ id[x × y] ∘ ∆(x × y) ≈ ETA ∘ eliminate.
Proof.
  apply prod_ext.
  - rewrite (grp_prod_left_leg X exl (mon_prod_mu_exl _ _) (exl_split _ _)).
    now rewrite (grp_prod_eta_leg X exl (mon_prod_eta_exl _ _)).
  - rewrite (grp_prod_left_leg Y exr (mon_prod_mu_exr _ _) (exr_split _ _)).
    now rewrite (grp_prod_eta_leg Y exr (mon_prod_eta_exr _ _)).
Qed.

Lemma grp_prod_right_inverse :
  MU ∘ id[x × y] ⨂ grp_prod_inverse ∘ ∆(x × y) ≈ ETA ∘ eliminate.
Proof.
  apply prod_ext.
  - rewrite (grp_prod_right_leg X exl (mon_prod_mu_exl _ _) (exl_split _ _)).
    now rewrite (grp_prod_eta_leg X exl (mon_prod_eta_exl _ _)).
  - rewrite (grp_prod_right_leg Y exr (mon_prod_mu_exr _ _) (exr_split _ _)).
    now rewrite (grp_prod_eta_leg Y exr (mon_prod_eta_exr _ _)).
Qed.

(*
The product group object.  Its monoid half is #503's [Monoid_Product]
   CONSUMED, not reproved; only the inversion and the two inverse laws are
   new.  Built with [Build_GroupObject] rather than record-literal syntax,
   because the field name [inverse] is a keyword (see [group_inverse]).

--------
产品组对象。它的幺半群是 #503 的 [Monoid_Product] CONSUMED，而不是重新证明的；只有反演和两个逆律是新的。使用 [Build_GroupObject] 构建而不是记录字面语法，因为字段名 [inverse] 是关键字（见 [group_inverse]）。
*)
Definition GroupObject_Product : GroupObject (x × y) :=
  Build_GroupObject (x × y)
    (MonoidObject_of_Monoid
       (Monoid_Product (group_monoid X) (group_monoid Y)))
    grp_prod_inverse grp_prod_left_inverse grp_prod_right_inverse.

(*
The underlying monoid of the product group IS #503's product monoid, at
   Leibniz equality: the [Monoid]/[MonoidObject] round trip is definitional
   ([monoid_round], Theory/Algebra/Monoid/Product.v).

--------
积群的底层幺半群就是 #503 的积幺半群，在莱布尼茨等式下：[Monoid]/[MonoidObject] 往返是定义上的 ([monoid_round], Theory/Algebra/Monoid/Product.v)。
*)
Example grp_prod_monoid :
  group_monoid GroupObject_Product
    = Monoid_Product (group_monoid X) (group_monoid Y) := eq_refl.

Example grp_prod_inverse_is :
  group_inverse GroupObject_Product = grp_prod_inverse := eq_refl.

Example grp_prod_mappend :
  mappend[GroupObject_Product]
    = mon_prod_mu (group_monoid X) (group_monoid Y) := eq_refl.

Example grp_prod_mempty :
  mempty[GroupObject_Product]
    = mon_prod_eta (group_monoid X) (group_monoid Y) := eq_refl.

(*
The projections and the pairing are group homomorphisms — and each is
   #503's monoid statement applied verbatim, the two [GroupHom] goals being
   CONVERTIBLE with the corresponding [MonoidHom] ones.

--------
投影和配对是群同态——并且每个都是 #503 的幺半群命题的逐字应用，这两个 [GroupHom] 目标可以与对应的 [MonoidHom] 目标相互转换。
*)
Lemma grp_exl_hom : GroupHom GroupObject_Product X exl.
Proof. exact (mon_exl_hom (group_monoid X) (group_monoid Y)). Qed.

Lemma grp_exr_hom : GroupHom GroupObject_Product Y exr.
Proof. exact (mon_exr_hom (group_monoid X) (group_monoid Y)). Qed.

Lemma grp_fork_hom {z : C} {Z : GroupObject z} {f : z ~> x} {g : z ~> y} :
  GroupHom Z X f → GroupHom Z Y g → GroupHom Z GroupObject_Product (f △ g).
Proof. exact (@mon_fork_hom _ _ _ _ _ _ _ _ _ _ _). Qed.

End GrpProductData.

(*
Binary products in GrpCat, carried by binary products of C.  No terminal
   object of C is used, and no compatibility between × and ⨂.

--------
GrpCat 中的二元积，由 C 的二元积承载。没有使用 C 的终对象，且 × 与 ⨂ 之间没有兼容性。
*)
#[export] Program Instance GrpCat_Cartesian : @Cartesian GrpCat := {|
  product_obj := fun X Y => (`1 X × `1 Y; GroupObject_Product `2 X `2 Y);
  Cartesian.fork :=
    fun _ _ _ f g => (`1 f △ `1 g; grp_fork_hom _ _ `2 f `2 g);
  exl := fun X Y => (exl; grp_exl_hom `2 X `2 Y);
  exr := fun X Y => (exr; grp_exr_hom `2 X `2 Y)
|}.
Next Obligation. proper; now apply Cartesian.fork_respects. Qed.
Next Obligation. apply ump_products. Qed.

End GrpProduct.

(** ** The terminal group object / ** 末端组对象 *)

Section GrpTerminal.

Context `{TE : @Terminal C}.

(*
The terminal object of C carries a unique group-object structure: every
   structure map lands in 1, so [one_unique] discharges both inverse laws
   just as it discharges the three monoid laws in [Terminal_Monoid].

--------
C 的终端对象携带唯一的群对象结构：每个结构映射都落在 1 上，因此 [one_unique] 解除两条逆元定律，就像它解除 [Terminal_Monoid] 中的三条幺半群定律一样。
*)
Definition GroupObject_Terminal : GroupObject (1 : C) :=
  Build_GroupObject (1 : C) (MonoidObject_of_Monoid Terminal_Monoid)
    one (one_unique _ _) (one_unique _ _).

Example grp_terminal_monoid :
  group_monoid GroupObject_Terminal = Terminal_Monoid := eq_refl.

(* Every morphism into 1 is a group homomorphism. / 每个到1的态射都是群同态。 *)
Lemma grp_one_hom {x : C} (G : GroupObject x) :
  GroupHom G GroupObject_Terminal one.
Proof. exact (mon_one_hom (group_monoid G)). Qed.

#[export] Program Instance GrpCat_Terminal : @Terminal GrpCat := {|
  terminal_obj := ((1 : C); GroupObject_Terminal);
  one := fun X => (one; grp_one_hom `2 X)
|}.
Next Obligation. apply one_unique. Qed.

End GrpTerminal.

(** ** The forgetful functor sends the finite products to C's own / ** 忘记函子将有限积映射到 C 自身的积 *)

Section GrpForget.

Context `{CA : @Cartesian C}.
Context `{TE : @Terminal C}.

Example GrpCat_Forget_product (X Y : GrpCat) :
  fobj[GrpCat_Forget] (X × Y)
    = fobj[GrpCat_Forget] X × fobj[GrpCat_Forget] Y := eq_refl.

Example GrpCat_Forget_terminal :
  fobj[GrpCat_Forget] (@terminal_obj GrpCat GrpCat_Terminal) = (1 : C)
  := eq_refl.

Example GrpCat_Forget_exl (X Y : GrpCat) :
  fmap[GrpCat_Forget] (@exl GrpCat GrpCat_Cartesian X Y) = exl := eq_refl.

Example GrpCat_Forget_exr (X Y : GrpCat) :
  fmap[GrpCat_Forget] (@exr GrpCat GrpCat_Cartesian X Y) = exr := eq_refl.

Example GrpCat_Forget_fork (X Y Z : GrpCat) (f : X ~> Y) (g : X ~> Z) :
  fmap[GrpCat_Forget] (@Cartesian.fork GrpCat GrpCat_Cartesian _ _ _ f g)
    = fmap[GrpCat_Forget] f △ fmap[GrpCat_Forget] g := eq_refl.

Example GrpCat_Forget_one (X : GrpCat) :
  fmap[GrpCat_Forget] (@one GrpCat GrpCat_Terminal X) = one := eq_refl.

(* GrpCat_Mon likewise preserves them on the nose. / GrpCat_Mon 同样准确地保存了它们。 *)
Example GrpCat_Mon_product (X Y : GrpCat) :
  fobj[GrpCat_Mon] (X × Y) = fobj[GrpCat_Mon] X × fobj[GrpCat_Mon] Y
  := eq_refl.

Example GrpCat_Mon_terminal :
  fobj[GrpCat_Mon] (@terminal_obj GrpCat GrpCat_Terminal)
    = @terminal_obj (Mon C) Mon_Terminal := eq_refl.

End GrpForget.

End GroupHomomorphism.

Arguments GrpCat C {CM}.

Section GrpCatIntrinsic.

Context {C : Category}.
Context `{CM : @CartesianMonoidal C}.

Definition GrpCat_Cartesian_tensor : @Cartesian (GrpCat C) :=
  @GrpCat_Cartesian C CM CartesianMonoidal_Cartesian.

Definition GrpCat_Terminal_unit : @Terminal (GrpCat C) :=
  @GrpCat_Terminal C CM (@SemicartesianMonoidal_Terminal C _ _).

Example grpcat_tensor_product (X Y : GrpCat C) :
  fobj[GrpCat_Forget] (@product_obj _ GrpCat_Cartesian_tensor X Y)
    = (fobj[GrpCat_Forget] X ⨂ fobj[GrpCat_Forget] Y)%object := eq_refl.

Example grpcat_unit_terminal :
  fobj[GrpCat_Forget] (@terminal_obj _ GrpCat_Terminal_unit) = @I C _
  := eq_refl.

End GrpCatIntrinsic.

(** ** Probes / ** 探针 *)

(*
Each [Fail] below was stripped once and its failure kind read off the
   message; the kinds are kept lexically apart, TYPING first and CONVERSION
   last.  Every constant a negative names is also named by a succeeding
   command, so a rename breaks the build instead of silencing a probe.

--------
下面的每个 [Fail] 都被剥离了一次，并且从消息中读取了其失败类型；这些类型在词汇上保持分开，TYPING 放在最前，CONVERSION 放在最后。每个负名称的常量也由随后的命令命名，因此重命名会破坏构建，而不是让探测静默。
*)

Section Probes.

Context {C : Category}.
Context `{M : @Monoidal C}.
Context `{CM : @CartesianMonoidal C}.
Context {x y : C} (Gx : @GroupObject C CM x) (Gy : @GroupObject C CM y).
Context (f : x ~> y).

(*
NEGATIVE 1, TYPING.  A group object cannot be stated over a bare monoidal
   base: the inverse laws need the diagonal and the discard.  This is the
   whole of the scope difference from Theory/Algebra/Monoid/Product.v, which
   quantifies over an arbitrary [M : @Monoidal C].
     "The term "M" has type "Monoidal" while it is expected to have type
      "CartesianMonoidal"."

--------
负 1，类型输入。不能在裸单体基上声明一个群对象：逆运算律需要对角线和丢弃。这就是与 Theory/Algebra/Monoid/Product.v 的作用域差异的全部，该文件对任意 [M : @Monoidal C] 进行了量化。
“术语 ‘M’ 的类型是 ‘Monoidal’，而期望类型是 ‘CartesianMonoidal’。”
*)
Fail Check (fun z : obj[C] => @GroupObject C M z).

(* CONTROL for negative 1. / 负一的控制。 *)
Check (fun z : obj[C] => @GroupObject C CM z).

(*
NEGATIVE 2, TYPING.  [MonoidHom] is indexed by Theory/Algebra/Monoid.v's
   [Monoid], not by Structure/Monoid.v's [MonoidObject], so the raw field of
   a group object does not fit and #503's class passage
   ([Monoid_of_MonoidObject], used by [group_monoid]) is load-bearing.
     "The term "groupobject_is_monoid" has type "MonoidObject x""

--------
否定 2，输入。[MonoidHom] 是由 Theory/Algebra/Monoid.v 的 [Monoid] 索引的，而不是由 Structure/Monoid.v 的 [MonoidObject] 索引的，因此群对象的原始字段不匹配，#503 的类传递 ([Monoid_of_MonoidObject]，由 [group_monoid] 使用) 是承重的。
	“术语 'groupobject_is_monoid' 的类型是 'MonoidObject x'”
*)
Fail Check (MonoidHom (@groupobject_is_monoid _ _ _ Gx)
                      (@groupobject_is_monoid _ _ _ Gy) f).

(*
CONTROLS for negative 2, naming every constant it mentions — including
   [groupobject_is_monoid] itself, whose only other positive occurrence is
   inside [group_monoid]'s body, which PRECEDES the negative.

--------
负 2 的控制，列出它提到的每一个常量——包括 [groupobject_is_monoid] 本身，它唯一的另一次正向出现是在 [group_monoid] 的主体内，而该主体出现在负数之前。
*)
Check (@groupobject_is_monoid C CM x Gx).
Check (MonoidHom (group_monoid Gx) (group_monoid Gy) f).
Check (GroupHom Gx Gy f).
Check (eq_refl : GroupHom Gx Gy f
                   = MonoidHom (group_monoid Gx) (group_monoid Gy) f).

(*
NEGATIVE 3, CONVERSION.  The two forgetful functors agree on objects and
   on morphisms at [eq_refl] (the controls below), but the composite FUNCTOR
   RECORD is not [GrpCat_Forget]: [Compose] rebuilds [fmap_respects],
   [fmap_id] and [fmap_comp] as fresh proof terms.
     "The term "eq_refl" has type
      "Mon_Forget ◯ GrpCat_Mon = Mon_Forget ◯ GrpCat_Mon" while it is
      expected to have type "Mon_Forget ◯ GrpCat_Mon = GrpCat_Forget"."

--------
否定 3，转换。两个遗忘函子在对象上以及在 [eq_refl]（以下控制项）上的态射上是一致的，但复合函子 RECORD 不是 [GrpCat_Forget]：[Compose] 将 [fmap_respects]、[fmap_id] 和 [fmap_comp] 重建为新的证明项。
“项‘eq_refl’的类型是
‘Mon_Forget ◯ GrpCat_Mon = Mon_Forget ◯ GrpCat_Mon’，而预期类型是‘Mon_Forget ◯ GrpCat_Mon = GrpCat_Forget’。”
*)
Fail Check (eq_refl : Mon_Forget ◯ GrpCat_Mon = GrpCat_Forget).

(* CONTROLS for negative 3. / 负3的控制 *)
Check (fun (X : GrpCat C) => (eq_refl :
  fobj[Mon_Forget] (fobj[GrpCat_Mon] X) = fobj[GrpCat_Forget] X)).
Check (fun (X Y : GrpCat C) (g : X ~> Y) => (eq_refl :
  fmap[Mon_Forget] (fmap[GrpCat_Mon] g) = fmap[GrpCat_Forget] g)).

End Probes.

(** ** Where the hom/proof identification comes from / ** 同源/证据识别来自哪里 *)

(*
Four FORMABILITY negatives.  Over a category whose hom and proof levels
   are declared strictly apart, each of the four donors this file names is
   rejected, while a hom and an identity at those very levels are accepted —
   so the identification visible in every binder above is inherited from
   four sources, each sufficient on its own, and is not introduced here.
   They are NOT independent: [CartesianMonoidal] contains [Monoidal], so at
   most three are.  See the UNIVERSES section of the header.

--------
四个可形成性（FORMABILITY）负面。在一个其同构（hom）和证明（proof）级别被严格区分的范畴上，本文件列出的四个供体都被拒绝，而在相同级别上的同构和恒等被接受——因此，上面每个绑定器中可见的识别都是从四个来源继承的，每个来源单独就足够，而不是在此引入的。它们不是独立的：[CartesianMonoidal] 包含 [Monoidal]，因此最多只有三个是独立的。参见标题的 UNIVERSES 部分。
*)

Section UniverseDonors.

Universes uo uh up.
Constraint uh < up.

(* CONTROLS: the levels themselves are fine. / 控制：关卡本身没问题。 *)
Check (fun (C : Category@{uo uh up}) (a b : C) => a ~> b).
Check (fun (C : Category@{uo uh up}) (a : C) => id[a]).

(*
CONTROLS that the four donor names resolve, so that a rename cannot make
   the rejections below succeed on a reference-not-found error.

--------
控制四个捐赠者名称能够解析，以便重命名不会使下面的拒绝在参考未找到错误时成功。
*)
Check @Monoidal.
Check @Cartesian.
Check @Terminal.
Check @CartesianMonoidal.
Check @GroupObject.

(* Each reports: "Cannot enforce up = uh because uh < up". / 每个报告："无法执行 up = uh，因为 uh < up"。 *)
Fail Check (fun C : Category@{uo uh up} => @Monoidal C).
Fail Check (fun C : Category@{uo uh up} => @Cartesian C).
Fail Check (fun C : Category@{uo uh up} => @Terminal C).
Fail Check (fun C : Category@{uo uh up} => @CartesianMonoidal C).

End UniverseDonors.
