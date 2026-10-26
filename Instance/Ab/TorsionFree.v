(*
   * * Torsion-free abelian groups are a full reflective subcategory of Ab

   Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
   Springer GTM 5, §IV.3, printed p. 92, Exercise 2.  Verbatim
   from the page: “2. Show that the torsion-free abelian groups
   form a full reflective subcategory of Ab.”  The paragraph just
   above the exercises on that page supplies the vocabulary and
   is NOT this item's scope: “A coreflective subcategory of Ab is
   the full subcategory of all torsion abelian groups (a group is
   torsion if all elements have finite order); the coreflector
   sends each abelian group A to the subgroup TA of all elements
   of finite order in A.”  Catalog id: maclane:IV.3:ex2.

   ** What is delivered

   [TorsionFree_Reflective : Reflective TorsionFree_Sub] -- the record
   of Construction/Reflective.v, whose three fields are exactly the
   three things Mac Lane's phrase names: FULLNESS of the subcategory
   ([TorsionFree_Full]), a REFLECTOR ([TorsionFree_reflector]), and the
   ADJUNCTION ([TorsionFree_adj]) making it left adjoint to the
   inclusion.  Read the packaging precisely: the adjunction ALONE is
   strictly less than the record, and the mismatch is pinned as this
   development's typing negative.

   Around it: the torsion predicate [torsion_mem] with its five closure
   lemmas, the torsion subgroup [TorsionSub]/[TorsionAb] and its
   inclusion [torsion_incl], the torsion-free predicate [TorsionFree],
   the full subcategory [TorsionFree_Sub]/[TorsionFreeAb] with the
   inclusion proved Full AND Faithful, the quotient [AbModTorsion] with
   [AbModTorsion_TorsionFree], the universal property
   [torsion_universal] and its packaging [torsion_universal_arrow], and
   the counit corollary [torsionfree_reflect_iso] -- for a torsion-free
   B, B/T(B) ≅ B -- instantiated at ℤ as [ZAb_reflect_iso].

   ** The route

   Universal arrows, exactly the path Instance/Grp/Abelianize.v takes
   for §III.1 Exercise 3: state the ∃! ([torsion_universal],
   Abelianize.v's shape), package it with
   Theory/Universal/Arrow.v's [universal_arrow_from_UMP]
   ([torsion_universal_arrow], Abelianize.v), then read the functor
   and the adjunction off that same file's
   [LeftAdjointFunctorFromUniversalArrows] and
   [AdjunctionFromUniversalArrows] with no further proof.  Nothing in
   that chain is re-derived here.

   ** Reused, and what that saves

   - Instance/Ab.v: [AbObject], [AbHom], [Ab],
   [ab_map_neg], and -- the load-bearing one -- the image
   quotient [AbQuotient] with [ab_coset_eq] and
   [ab_quot_proj].  A/T(A) is that PRE-EXISTING quotient
   applied to the subgroup inclusion; NO new quotient machinery is
   built here, and no coset object is formed anywhere in this file.
   - Instance/Ab/DirectedColimit.v: [AbSubgroup],
   [AbSubgroupAb], [absub_incl].  The torsion subgroup
   is that record, not a third subgroup record; the other two in tree
   are this one and Instance/Ab/Character/Finite.v's [Subgroup],
   which additionally demands DECIDABLE membership and so cannot host
   a torsion predicate whose exponent is found rather than decided.
   - Instance/Ab/Monoidal.v: the ℕ-action [nat_smul] with
   [nat_smul_respects], [_add], [_plus],
   [_zero], [_neg], [_hom]; [ZAb],
   [ZAb_one], [nat_smul_int_one].
   - Adjunction/Unitalization.v's [nat_smul_mul] -- see the closure
   note below for why it is required rather than restated.
   - Construction/Subcategory.v: [Subcategory], [Sub],
   [Incl], [Incl_Faithful], [Full],
   [Full_Implies_Full_Functor].  The trivially-true [shom] is
   Instance/Rng.v's [CRng_Sub] pattern, and [Full] is written
   qualified for the same reason that file writes it so:
   Construction/Subcategory.v exports its OWN [Full], whose first
   argument is a Category, shadowing Theory/Functor.v's.
   - Construction/Reflective.v: [Reflective] and
   [reflective_counit_iso].

   NEW here: the torsion predicate and its five closure lemmas,
   torsion-freeness of the quotient, the mediator and the universal
   property, and the three witnesses.

   ** Exponent as data, and no choice principle

   [torsion_mem A a] is [{ k : nat & (0 < k) * (nat_smul A k a ≈ 0) }]
   -- a sigma, so the exponent is DATA and can be READ BACK, which is
   what [AbModTorsion_TorsionFree] does when it multiplies the two
   exponents.  No choice principle appears anywhere in this file.

   AN EARLIER REVISION continued: “Nothing anywhere in this file extracts a
   witness from a [Prop]-valued existential; the same design note
   Instance/Ab.v makes about [ab_coset_eq] being [Type]-valued
   applies verbatim, and it is what lets the coset witness be taken apart.”
   Since the PR “algebraic carriers are sets” (2026-09-17) that note is
   itself corrected: [ab_coset_eq] is a [Prop].  The torsion EXPONENT is
   still data -- [torsion_mem] is untouched -- but the COSET witness is not,
   so [quot_eq_elim] below is stated in continuation form, eliminating into
   an arbitrary [Prop], and its two consumers reach their own goals through
   [pequiv_to].  All 58 constants are closed under the global context.

   ** Prior art, measured at 9a1fe0f2 (the issue's “Current state” is
   stale and is corrected rather than repeated)

   The issue says the ambient category is missing (“there is no Ab, Grp
   or AbGrp instance”) and that “a whole-tree search for 'torsion'
   returns nothing”.  Both are false: [Ab] is Instance/Ab.v and
   Instance/Grp.v exists.  A case-insensitive search for 'torsion' over
   the .v files, excluding this file and its probe, returns SEVEN
   lines, in Instance/Ab/Character.v and
   Instance/Ab/Character/NonNatural.v; five
   are prose, the sixth is [ZZ_no_2_torsion], a lemma that
   ℤ has no nonzero 2-torsion -- a statement about one group at one
   exponent, not a torsion predicate -- and the seventh is that
   lemma's one use.  What IS absent, and is supplied
   here, is a torsion predicate, a torsion subgroup and a torsion-free
   predicate.

   Sharper, and this is the claim worth carrying: [rg -n
   'Build_Reflective'] over the .v files, excluding these two, returns
   exactly ONE hit, Construction/Reflective/Idempotent.v --
   inside [Idempotent_Reflective] (declared), which is over an
   ABSTRACT category with an idempotent monad; every other
   [Reflective]-typed term in tree is a HYPOTHESIS ([Context (R :
   Reflective S)] and the like, in Adjunction/FullFaithful.v,
   Adjunction/Fullness.v,
   Construction/Localization/Universal.v and Idempotent.v itself).  So
   under the criterion “a [Reflective] built at a NAMED concrete
   category” this is the tree's first inhabitant.

   ** The [nat_smul_mul] closure decision, with numbers

   Scalar multiplicativity of the action, [nat_smul (j*k) a ≈ nat_smul
   j (nat_smul k a)], is needed twice: for closure of torsion under
   addition (exponents k and l give k*l) and for torsion-freeness of
   the quotient.  It exists in tree exactly once, at
   Adjunction/Unitalization.v.  Criterion for the numbers below:
   transitive in-project .vo dependencies via [coqdep -R . Category],
   excluding the file itself.  This file's closure is 61 modules.
   Dropping [Category.Adjunction.Unitalization] gives 59 -- a delta of
   exactly TWO, [Adjunction/Unitalization.vo] and [Instance/Rg.vo],
   because the remaining 51 modules of Unitalization's own closure (52
   by the same criterion) are already inside this one.  Two is not a
   handful, so the lemma is REQUIRED rather than restated, and no
   duplicate of it is declared here.  Dropping
   [Category.Instance.Ab.Character.Finite] likewise gives 59 (delta
   two: [Instance/Ab/Character.vo] and Finite.v itself), which is why
   [ZMod2] (Finite.v) is reused as the torsion witness rather
   than a local bool group being built; dropping both gives 57, so the
   two deltas are independent.  (A first count read 62/60/60/58: it
   counted the queried module itself, which the stated criterion
   excludes.)

   ** ℤ has five names in tree

   [ring_ab Int_Ring] is named five times: [ZAb]
   (Instance/Ab/Monoidal.v), [ab_Z] (Instance/Ab/Coproduct.v),
   [Zgroup] (Instance/Ab/Graded.v), [Ab_Z]
   (Structure/Kernel/Universal/Examples.v) and [ab_int]
   (Instance/Ab/Free.v).  This file uses [ZAb] throughout and only
   [ZAb], because [nat_smul_int_one] is stated at it.

   ** Strengths, measured strict-first

   Holding at [eq_refl] (seven occurrences outside comments, all
   outside any rejection):
   the reflector's object part is the quotient
   ([torsion_reflector_obj]); the universal arrow IS [ab_quot_proj] and
   its object IS [TorsionFreeMod] ([torsion_arrow_is_proj],
   [torsion_arrow_obj] -- the Abelianize.v precedent, since
   [universal_arrow_from_UMP] stores the supplied morphism as the
   second projection of the comma object it builds); the quotient's
   zero and addition ARE the base group's ([quot_zero_strict],
   [quot_plus_strict]); the scalar action agrees at every CLOSED scalar
   ([nat_smul_quot_two]); and -- the exercise's second reviewer check
   -- the adjunction's UNIT is the quotient projection applied to any
   element ([torsion_unit_is_proj]).

   Falling back, with the cause diagnosed in each case:

   - The unit as a MORPHISM RECORD is only `≈` the projection
   ([torsion_unit_is_proj_hom]).  Cause:
   [AdjunctionFromUniversalArrows] builds ⌊−⌋ as [fun g => fmap[U] g
   ∘ arrow], so the class unit is a COMPOSITE record, [fmap[Incl] id
   ∘ ab_quot_proj …]; applied to an element that composite reduces,
   as a record it does not.  Note the precedent this development was
   pointed at, Instance/Mod/Free.v's [free_module_unit_is_insert],
   is likewise stated POINTWISE and not as a morphism equality.
   - [nat_smul] at a VARIABLE scalar is only Leibniz-equal by induction
   ([nat_smul_quot]).  Cause: the [Fixpoint] is stuck on [k], so
   conversion is left comparing the two [AbObject]s themselves, which
   are not convertible: they differ in their setoid field -- that
   difference being the entire content of the quotient -- and, being
   separately built records, in every law field as well.  The setoid
   field is NOT the discriminating cause, and an audit measured that:
   a variant of [A] agreeing with it on [cmon_setoid], [cmon_zero],
   [cmon_plus] and [ab_neg] and differing in ONE law field alone is
   rejected the same way, while it still agrees at every closed
   scalar.  This is measured rather than predicted: the expectation
   that it would hold on the nose is exactly what the closed-scalar
   case does and the variable case does not.
   - ℤ/T(ℤ) is isomorphic to ℤ but not equal to it: [ZAb_reflect_iso]
   is a pure instantiation of [reflective_counit_iso] with no tactic,
   while [AbModTorsion ZAb = ZAb] is refused.
   - The COUNIT is not read back at all.  It is the other transpose,
   i.e. [unique_obj (ump_universal_arrows …)], and
   [ump_universal_arrows] (Theory/Universal/Arrow.v) is closed
   with [Qed], so nothing on that side reduces and no [eq_refl] is
   claimed for it.

   The first THREE fallbacks above are pinned as conversion
   rejections in Test/ProbeTorsionFree371.v, together with the
   record-versus-adjunction mismatch (typing) and two universe
   rejections (formability): six negatives of three kinds, plus one
   scope-free instrument check.  The COUNIT is NOT among them --
   nothing is claimed about it in either direction, and no rejection
   naming it is stated.  This file itself carries no rejection at all,
   so it contributes nothing to [make todo].

   ** Universes

   Measured with [Set Printing Universes] on all 58 constants, reading
   BOTH the binder and the constraint block.  NO constraint block of
   any constant carries a universe EQUATION -- every entry is [<] or
   [<=].  Two identifications nevertheless sit in BINDERS, where a
   reader of the blocks alone would miss them, and both are the
   DONORS'.  First, TWENTY-FOUR of the 58 -- exactly the constants that
   mention a hom-set of [Ab] or the quotient, from [AbModTorsion] and
   [torsion_incl] through [torsion_universal_arrow] and the three
   [torsion_med] obligations, and NONE of the torsion predicate's own
   ([torsion_mem] and its five closure lemmas, [TorsionSub],
   [TorsionFree]; the witness [MixedAb] binds no group at all) -- bind
   the group at [AbObject@{u u u}], carrier, relation and proof
   universes identified: [Print Ab] with universes shows
   [obj := AbObject@{u0 u0 u0}], so an [AbObject] whose three levels
   are declared strictly apart is not an object of [Ab] (probed), and
   [AbQuotient] and [absub_incl] carry universe equations of their own
   ([u = u0 ... u = u4], and [u = u0], [u = u1]).  Second,
   the hom-with-proof identification that [Subcategory] and
   [Reflective] carry ([Category@{u u0 u0}], [Category@{u3 u5 u5}]).
   Neither is introduced here and neither is claimed unavoidable.  The
   second is guarded by the probe's two formability rejections, where
   naming a hom-set and an identity at hom-strictly-below-proof levels
   succeeds while [Subcategory] is refused; read the second rejection
   at its strength -- it names [Reflective] but fires at its
   [Subcategory] ARGUMENT with the identical message, since
   [Reflective] takes a [Subcategory] and cannot be tested apart from
   it (the trap Test/ProbeRingLattice340.v records for
   [MonoidObject]), so whether [Reflective] identifies anything OF ITS
   OWN is not measured here.

   FORTY-THREE of the 58 constants carry a [Set] token, and every one of
   the 43 carries it as a BOUND ([Set < u]) and never as an equation.

   RE-MEASURED after the PR “algebraic carriers are sets” (2026-09-17), by
   an [About] under [Set Printing Universes] on each of the 58 names
   [Print Module] lists, reading the constraint blocks.  An earlier
   revision of this paragraph counted ELEVEN, naming them: [MixedAb],
   [ZMod2_all_torsion], [ZMod2_not_TorsionFree], [ZMod2_quot_collapses],
   [mixed_gen], [mixed_gen_not_quot_zero], [mixed_gen_not_torsion],
   [mixed_quot_merges], [mixed_tors], [mixed_tors_not_zero],
   [mixed_tors_torsion] -- “exactly the ℤ/2 and mixed witness block, from
   [ZMod2]'s [bool] carrier” -- and said the general theory, the
   reflector, the adjunction, [TorsionFree_Reflective] and the whole ℤ
   block were [Set]-free.  THAT SECOND HALF NO LONGER HOLDS.  [Set < u]
   is what [PropEquiv] costs: [Prop]'s sort enters every object record
   through [cmon_prop], so the bound reaches the general theory too.
   What DID survive is the distinction the paragraph was making -- a
   bound is not a pin.  The other three sentences above still reproduce:
   58 constants, NO universe equation in any block (checked by searching
   the blocks for [u = u'] after stripping the [|=] separator; zero
   hits), and the two identifications still sitting in binders.  The
   [ZAb_one] routing is unchanged, and is
   Instance/Ab/Monoidal.v's own design note.

   ** NOT delivered

   - The COREFLECTION of the page's preceding paragraph -- torsion
   groups as a coreflective subcategory, with TA as coreflector.
   [Coreflective] is Construction/Reflective.v and the torsion
   subgroup built here is its object part, but that is a different
   catalog item and nothing here states or proves it.  CORRECTION
   (#370): Instance/Ab/Torsion.v states and proves it covariantly,
   [torsion_coreflection : Incl Ab Torsion_Sub ⊣
   torsion_coreflector], packaged as [Torsion_Coreflective], with
   this file's [TorsionAb] as the coreflection and [torsion_incl] as
   the couniversal arrow.
   - Functoriality of [TorsionSub] or of [TorsionAb] in A; no
   naturality of the torsion inclusion.  CORRECTION (#370):
   Instance/Ab/Torsion.v's [torsion_coreflector] is a functor
   [Ab ⟶ TorsionCat] whose object at A has [TorsionAb A] as its
   group at [eq_refl] ([torsion_coreflector_obj]), and the counit of
   [torsion_coreflection], natural as every counit is, is [≈] to
   [torsion_incl] at every A ([torsion_counit_is_incl]).
   [TorsionSub] is still not made functorial, and no naturality
   lemma is stated for [torsion_incl] by name.
   - The idempotent monad of the reflection.
   Construction/Reflective/Idempotent.v gives it by instantiation
   from [TorsionFree_Reflective]; that instantiation is not made.
   CORRECTION (#370): it is made in Instance/Ab/Torsion.v
   ([TorsionFree_Monad], [TorsionFree_IdempotentMonad],
   [TorsionFree_EM_MLocal]), with Riehl's Proposition 5.3.3 (ii)
   there through Construction/Reflective/Monadic.v
   ([TorsionFree_EM_Equivalence], [TorsionFree_Incl_Monadic]).
   - The [Grp] analogue, divisible groups, p-primary or p-torsion
   refinements, and any decision procedure for torsion.
   - No claim that [AbModTorsion] is the categorical cokernel of
   [torsion_incl], and no [HasCokernels]/[HasCoequalizers] instance.
   - No uniqueness statement for the reflector beyond what
   [torsion_universal] and [reflective_counit_iso] give.

   ** Corrections to the brief that guided this file

   Each is a measurement, not an opinion.  (1) The brief expected
   [nat_smul (AbModTorsion A) k x = nat_smul A k x] to hold at
   [eq_refl]; it does not at a variable [k], for the reason above --
   the brief anticipated the possibility and asked for it to be pinned,
   which is what happened.  (2) It warned that requiring
   Adjunction/Unitalization pulls “the whole Rg/Dorroh development”;
   the measured delta is two modules, so the lemma is required.  (3) It
   cited Instance/Mod/Free.v's unit readback as a MORPHISM-level
   precedent for a strict unit; that constant is pointwise, and so is
   the one here.  (4) It suggested [nat_smul_int_one] might suffice for
   torsion-freeness of ℤ; it does not, being about the generator only,
   so [nat_smul_ZAb] is proved for an arbitrary integer -- but
   [nat_smul_int_one] IS reused, in [mixed_gen_not_torsion].  Every
   other donor line number the brief gave was re-grepped here and is
   correct. 

   --------
   * * 无扭阿贝尔群是 Ab 的一个完整反射子范畴

   书籍：Mac Lane，《为工作数学家准备的范畴论》，第2版，
   Springer GTM 5，第 IV.3 节，第 92 页印刷，练习 2。逐字翻译
   自页面：“2. 证明无扭阿贝尔群
   形成 Ab 的一个完整反射子范畴。”该页练习题上方的段落提供了
   词汇，但不属于此项的范围：“Ab 的一个余反射子范畴是
   所有有扭阿贝尔群的完整子范畴（一群是有扭群，如果所有元素都有有限阶）；余反射函子
   将每个阿贝尔群 A 映射到其所有有限阶元素的子群 TA。” 目录编号：maclane:IV.3:ex2。

   ** 所提供的内容是什么[TorsionFree_Reflective : Reflective TorsionFree_Sub] —— Construction/Reflective.v 的记录，其三个字段正好是 Mac Lane 术语所命名的三件事：子范畴的完整性（[TorsionFree_Full]）、一个反射器（[TorsionFree_reflector]）、以及使其成为包含的左伴随的伴随（[TorsionFree_adj]）。精确读取这个封装：单独的伴随严格小于记录，而这种不匹配被固定为该开发的类型负面。围绕它：扭子谓词 [torsion_mem] 及其五个闭包引理，扭子子群 [TorsionSub] / [TorsionAb] 及其包含 [torsion_incl]，无扭子谓词 [TorsionFree]，全子范畴 [TorsionFree_Sub] / [TorsionFreeAb] 及包含被证明为满且忠实，商 [AbModTorsion] 与 [AbModTorsion_TorsionFree]，泛性质 [torsion_universal] 及其封装 [torsion_universal_arrow]，以及余单位推论 [torsionfree_reflect_iso] —— 对于无扭子 B，B/T(B) ≅ B —— 在 ℤ 上实例化为 [ZAb_reflect_iso]。

   ** 路线通用箭头，正是路径 Instance/Grp/Abelianize.v 所采取的方式
   对于 §III.1 练习 3：说明 ∃! ([torsion_universal]，
   Abelianize.v 的形状)，将其与
   Theory/Universal/Arrow.v 的 [universal_arrow_from_UMP]
   ([torsion_universal_arrow]，Abelianize.v) 打包，然后从同一文件的
   [LeftAdjointFunctorFromUniversalArrows] 和
   [AdjunctionFromUniversalArrows] 中读取函子和伴随，而无需进一步证明。该链中的内容在此处不再重新推导。

   ** 重用，以及它节省了什么- Instance/Ab.v:  [AbObject]，[AbHom]，[Ab]，[ab_map_neg]，以及——承重的——像商 [AbQuotient] 以及 [ab_coset_eq] 和 [ab_quot_proj]。A/T(A) 是应用于子群包含的预先存在的商；这里没有建立新的商结构，也没有在此文件的任何地方形成陪集对象。- Instance/Ab/DirectedColimit.v:  [AbSubgroup]，[AbSubgroupAb]，[absub_incl]。扭子群是该记录，而不是第三个子群记录；树中的另外两个是这个以及 Instance/Ab/Character/Finite.v 的 [Subgroup]，该记录还要求成员资格可判定，因此无法承载指数是已找到而非可判定的扭子谓词。- Instance/Ab/Monoidal.v：ℕ作用 [nat_smul] 与  
   [nat_smul_respects]、[_add]、[_plus]、  
   [_zero]、[_neg]、[_hom]；[ZAb]、  
   [ZAb_one]、[nat_smul_int_one]。- Adjunction/Unitalization.v 的 [nat_smul_mul] ——参见下方闭包说明，说明为什么需要它而不是重述。- Construction/Subcategory.v：[Subcategory]、[Sub]、  
   [Incl]、[Incl_Faithful]、[Full]、  
   [Full_Implies_Full_Functor]。显然正确的 [shom] 是  
   Instance/Rng.v 的 [CRng_Sub] 模式，而 [Full] 
   被写为限定形式，原因与该文件如此写作相同：  
   Construction/Subcategory.v 导出其自身的 [Full]，其第一个  
   参数是一个 Category，覆盖了 Theory/Functor.v 的。- Construction/Reflective.v：[Reflective] 和  
   [reflective_counit_iso]。新内容：扭力谓词及其五个闭合引理，商的无扭性，中介及其泛性质，以及三个见证者。

   ** 指数作为数据，而没有选择公理

   [torsion_mem A a] 是 [{ k : nat & (0 < k) * (nat_smul A k a ≈ 0) }]
   -- 一个 σ，因此指数是数据并且可以被读取，这正是 [AbModTorsion_TorsionFree] 在乘这两个指数时所做的操作。这个文件中没有出现任何选择公理。早期修订继续写道：“这个文件中的任何内容都没有从一个 [Prop] 值的存在量中提取出见证；Instance/Ab.v 中关于 [ab_coset_eq] 是 [Type] 值的设计说明同样适用，并且正是它让余类见证可以被拆开。” 自从 PR “代数载体是集合”（2026-09-17）之后，该说明本身被修正：[ab_coset_eq] 是一个 [Prop]。挠子指数仍然是数据——[torsion_mem] 未被触及——但余类见证没有，因此下面的 [quot_eq_elim] 以延续形式陈述，被消解为任意 [Prop]，其两个使用者通过 [pequiv_to] 各自达成目标。所有 58 个常数在全局上下文中都是封闭的。** 现有技术，测量于 9a1fe0f2（该问题的“当前状态”已过时，已被修正而非重复）问题指出环境类别缺失（“没有 Ab、Grp 或 AbGrp 实例”），并且“对 'torsion' 进行整棵树搜索没有结果”。这两点都是错误的：[Ab] 是 Instance/Ab.v，Instance/Grp.v 也存在。在 .v 文件中（不包括这个文件及其探针）对 'torsion' 进行不区分大小写的搜索，返回了七行，位于 Instance/Ab/Character.v 和 Instance/Ab/Character/NonNatural.v 中；其中五行是正文，第六行为 [ZZ_no_2_torsion]，这是一个引理，说明 ℤ 没有非零 2-挠元素——这是关于某个指数下某个群的陈述，而不是挠元素谓词——第七行是该引理的唯一使用。缺失的内容，并且在这里提供的，是挠元素谓词、挠子群以及无挠元素谓词。更尖锐，这是值得注意的主张：[rg -n 'Build_Reflective'] 在 .v 文件上搜索，排除这两个文件，恰好返回一个命中，即 Construction/Reflective/Idempotent.v -- 在 [Idempotent_Reflective] 内（已声明），它位于具有幂等单子的抽象范畴上；树中的每个其他 [Reflective] 类型的项都是一个假设（如 Adjunction/FullFaithful.v、Adjunction/Fullness.v、Construction/Localization/Universal.v 和 Idempotent.v 本身中的 [Context (R : Reflective S)] 等）。因此，根据“在命名具体范畴下构建的 [Reflective]”这一标准，这是该树的第一个成员。

   ** [nat_smul_mul] 闭包决策，附带数字作用的标量可乘性，[nat_smul (j*k) a ≈ nat_smul j (nat_smul k a)] 被需要两次：一次是为了扭转元素在加法下的封闭性（指数 k 和 l 给出 k*l），另一次是为了商群的无扭性。它在树中恰好出现一次，在 Adjunction/Unitalization.v。以下数字的标准：通过 [coqdep -R . Category] 在 .vo 文件中传递的依赖关系，不包括文件本身。该文件的闭包为 61 个模块。去掉 [Category.Adjunction.Unitalization] 后为 59 —— 差值恰好为两，[Adjunction/Unitalization.vo] 和 [Instance/Rg.vo]，因为 Unitalization 自身闭包的剩余 51 个模块（按相同标准为 52 个）已经在这个闭包中。两不是一个大数，因此该引理是必须的，而不是重新陈述，也没有在这里声明副本。删除
   [Category.Instance.Ab.Character.Finite] 同样得到 59（两个增量：[Instance/Ab/Character.vo] 和 Finite.v 本身），这就是为什么
   [ZMod2]（Finite.v）被重复用作挠子见证，而不是构建本地布尔组；同时删除两者得到 57，所以两个增量是独立的。（第一次计数为 62/60/60/58：它计算了被查询的模块本身，而所述标准将其排除）

   ** ℤ 在树中有五个名字

   [ring_ab Int_Ring] 被命名五次：[ZAb]（Instance/Ab/Monoidal.v）、[ab_Z]（Instance/Ab/Coproduct.v）、[Zgroup]（Instance/Ab/Graded.v）、[Ab_Z]（Structure/Kernel/Universal/Examples.v）和 [ab_int]（Instance/Ab/Free.v）。该文件始终使用 [ZAb]，仅使用 [ZAb]，因为 [nat_smul_int_one] 已经声明在其中。

   ** 强度，按严格优先测量保持在 [eq_refl]（七次出现于注释之外，全部不在任何拒绝中）：
   反射器的对象部分是商对象（[torsion_reflector_obj]）；全箭头是 [ab_quot_proj]，其对象是 [TorsionFreeMod]（[torsion_arrow_is_proj]，[torsion_arrow_obj] —— Abelianize.v 的先例，因为 [universal_arrow_from_UMP] 将提供的态射存储为它构建的逗号对象的第二投影）；商对象的零和加法是基群的（[quot_zero_strict]，[quot_plus_strict]）；标量作用在每个闭标量上是一致的（[nat_smul_quot_two]）；并且 —— 练习的第二审核检查 —— 伴随单位是将商投影应用于任意元素（[torsion_unit_is_proj]）。

   回退，每种情况下都诊断原因：- 单位作为一个态射记录（MORPHISM RECORD）仅为 `≈` 的投影（[torsion_unit_is_proj_hom]）。原因：[AdjunctionFromUniversalArrows] 将 ⌊−⌋ 构建为 [fun g => fmap[U] g ∘ arrow]，因此该类单位是一个复合记录（COMPOSITE record），[fmap[Incl] id ∘ ab_quot_proj …]；应用于一个复合约化的元素时，作为记录它则不约化。请注意该开发所指的先例，即 Instance/Mod/Free.v 的 [free_module_unit_is_insert]，也同样按点（POINTWISE）陈述，而非作为态射等式。- [nat_smul] 在一个变量标量（VARIABLE scalar）上仅通过归纳法为莱布尼茨相等（Leibniz-equal）（[nat_smul_quot]）。原因：[Fixpoint]卡在了[k]上，因此转换留下的是比较两个[AbObject]本身，而它们不可转换：它们在setoid字段上有所不同——这种差异就是商的全部内容——而且，它们作为单独构建的记录，在每个法律字段上也不同。setoid字段不是判别原因，并且审计已经测量了这一点：一个[A]的变体在[cmon_setoid]、[cmon_zero]、[cmon_plus]和[ab_neg]上与其一致，仅在一个法律字段上不同，同样会被拒绝，而它仍然在每个封闭标量上保持一致。这是测量得出的，而不是预测的：预期它会精确成立的想法，正是封闭标量情况下成立，而变量情况下不成立的情况。- ℤ/T(ℤ) 同构于 ℤ 但不等同于它：[ZAb_reflect_iso] 是 [reflective_counit_iso] 的纯实例化，没有任何策略，而 [AbModTorsion ZAb = ZAb] 被拒绝。 - COUNIT 完全没有被读回。它是另一个转置，即 [unique_obj (ump_universal_arrows …)]，并且 [ump_universal_arrows]（Theory/Universal/Arrow.v）已通过 [Qed] 闭合，所以那一侧没有任何东西被化简，也没有为它声明 [eq_refl]。上面前三个回退在 Test/ProbeTorsionFree371.v 中被标记为转换拒绝，连同记录与连接不匹配（类型检查）以及两个宇宙拒绝（可形成性）：三种类型的六个负面，以及一个无作用域的仪器检查。COUNIT 不在其中——无论哪个方向都没有对此提出声明，也没有提到以它命名的拒绝。该文件本身根本没有任何拒绝，因此对 [make todo] 没有任何贡献。

   ** 宇宙使用 [Set Printing Universes] 测量所有 58 个常数，同时读取绑定器和约束块。没有任何常数的约束块包含宇宙方程——每个条目都是 [<] 或 [<=]。然而，有两个标识仍然位于绑定器中，仅查看块本身的读者会错过它们，并且这两个都是捐赠者的。首先，在这 58 个常量中有 24 个——正是那些提到  [Ab] 的 Hom 集或商集的常量，从  [AbModTorsion] 和  [torsion_incl] 到  [torsion_universal_arrow] 以及三个  [torsion_med] 义务，而且没有一个属于扭转谓词自身的常量（[torsion_mem] 及其五个闭包引理，[TorsionSub]、[TorsionFree]；见证者 [MixedAb] 根本不绑定任何群）——绑定了已确定的位于 [AbObject@{u u u}] 上的群、载体、关系和证明宇宙：[Print Ab] 的宇宙显示 [obj := AbObject@{u0 u0 u0}]，因此一个三个层次被严格区分声明的 [AbObject] 并不是 [Ab]（已探测）的对象，而 [AbQuotient] 和 [absub_incl] 自身携带宇宙方程（[u = u0 ... u = u4]，以及 [u = u0]、[u = u1]）。第二，[Subcategory] 和 [Reflective] 所携带的同态-带证明的识别（[Category@{u u0 u0}]、[Category@{u3 u5 u5}]）。这里没有引入任何一个，也没有声称它们是不可避免的。第二个由探针的两个可构性拒绝来保护，其中在严格低于证明级别的同态集合和身份命名成功，而 [Subcategory] 被拒绝；以其强度来解读第二个拒绝——它命名了 [Reflective]，但在 [Subcategory] 参数上触发相同的消息，因为 [Reflective] 接受一个 [Subcategory]，并且不能被独立测试（trap Test/ProbeRingLattice340.v 为 [MonoidObject] 记录），所以 [Reflective] 是否自行识别任何东西在此不予衡量。在58个常数中，有43个携带[Set]标记，并且这43个常数中的每一个都以BOUND（[Set < u]）的形式携带它，而从不以方程的形式携带。在 PR “代数载体是集合”（2026-09-17）之后，由 [About] 在 [Set Printing Universes] 下对 58 个 [Print Module] 列表中的名字进行重新测量，读取约束块。该段落的早期修订版本统计了十一项，并命名为：[MixedAb]、[ZMod2_all_torsion]、[ZMod2_not_TorsionFree]、[ZMod2_quot_collapses]、[mixed_gen]、[mixed_gen_not_quot_zero]、[mixed_gen_not_torsion]、[mixed_quot_merges]、[mixed_tors]、[mixed_tors_not_zero]、[mixed_tors_torsion]——“正是 ℤ/2 和混合见证块，来自 [ZMod2] 的 [bool] 载体”——并说一般理论、反射器、伴随、[TorsionFree_Reflective] 以及整个 ℤ 块都是 [Set]-自由的。但后一半不再成立。[Set < u] 是 [PropEquiv] 的成本：[Prop] 的类型通过 [cmon_prop] 进入每个对象记录，因此该界限也适用于一般理论。真正保留下来的，是段落所作出的区分——约束不是销钉。上面另外三句话仍然重现：58 个常量，在任何块中都没有宇宙方程（通过在去掉 [|=] 分隔符后搜索 [u = u'] 检查块；零命中），还有两个标识仍然保存在文件夹中。[ZAb_one] 的路由没有改变，并且是 Instance/Ab/Monoidal.v 自己的设计说明。

   ** 未交付- 本页前一段的余反射 -- 扭力群作为余反射子范畴，TA作为余反射器。[Coreflective] 是 Construction/Reflective.v，这里构建的扭力子群是它的对象部分，但那是不同的目录项，这里没有陈述或证明它。更正 (#370)：Instance/Ab/Torsion.v 陈述并证明了它的协变性，[torsion_coreflection : Incl Ab Torsion_Sub ⊣ torsion_coreflector]，打包为 [Torsion_Coreflective]，本文件的 [TorsionAb] 作为余反射，[torsion_incl] 作为余通用箭。- [TorsionSub] 或 [TorsionAb] 在 A 中的函子性；扭力包含的自然性不存在。更正 (#370):
   Instance/Ab/Torsion.v 中的  [torsion_coreflector] 是一个函子
   [Ab ⟶ TorsionCat]，其在 A 上的对象具有  [TorsionAb A] 作为其在  [eq_refl] 的群 ( [torsion_coreflector_obj] )，并且每个余单位都是自然的，[torsion_coreflection] 的余单位是  [≈] 到 [torsion_incl] 在每个 A 上 ( [torsion_counit_is_incl] )。[TorsionSub] 仍未成为函子，并且没有为 [torsion_incl] 明确陈述自然性引理。- 反射的幂等单子。Construction/Reflective/Idempotent.v 通过 [TorsionFree_Reflective] 实例化给出；该实例化尚未完成。更正 (#370)：它在 Instance/Ab/Torsion.v 中完成
   ( [TorsionFree_Monad], [TorsionFree_IdempotentMonad], [TorsionFree_EM_MLocal] )，通过 Construction/Reflective/Monadic.v ( [TorsionFree_EM_Equivalence], [TorsionFree_Incl_Monadic] ) 在 Riehl 的命题 5.3.3 (ii) 中得到。- [Grp] 的类似物，可分群，p-主或 p-挠性改进，以及任何挠性判定程序。- 没有声称 [AbModTorsion] 是 [torsion_incl] 的范畴余核，也没有 [HasCokernels] / [HasCoequalizers] 的实例。- 反射器的唯一性声明仅限于 [torsion_universal] 和 [reflective_counit_iso] 所提供的内容。

   ** 对指导此文件的简报的更正每一项都是测量结果，而不是观点。(1) 简报预计 [nat_smul (AbModTorsion A) k x = nat_smul A k x] 将保持在 [eq_refl]；它在变量 [k] 上不起作用，原因如上——简报预见到了这种可能性并请求将其固定，这正是发生的情况。(2) 它警告说，要求 Adjunction/Unitalization 会牵扯“整个 Rg/Dorroh 开发”；测量的差值是两个模块，因此需要引理。(3) 它引用了 Instance/Mod/Free.v 的 unit readback 作为严格单位的一种 MORPHISM 级先例；该常数是逐点的，这里的一样。(4) 它建议 [nat_smul_int_one] 可能足以保证 ℤ 的无挠性；它不足够，因为它仅涉及生成元，因此 [nat_smul_ZAb] 对任意整数都已证明——但 [nat_smul_int_one] 在 [mixed_gen_not_torsion] 中被重新使用。简介中提供的每个其他捐赠者行号都在此重新使用 grep 命令检查过，并且是正确的。
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Instance.Ab.Monoidal.
Require Import Category.Instance.Ab.DirectedColimit.
Require Import Category.Instance.Ab.Character.Finite.
Require Import Category.Adjunction.Unitalization.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

(** * Torsion elements / * 扭转元素 *)

Definition torsion_mem (A : AbObject) (a : carrier A) : Type :=
  { k : nat & ((0 < k)%nat * (nat_smul A k a ≈ cmon_zero A))%type }.

Definition torsion_resp (A : AbObject) (a b : carrier A) :
  a ≈ b → torsion_mem A a → torsion_mem A b.
Proof.
  intros Hab [k [Hk Hka]].
  exists k; split; [ exact Hk | ].
  rewrite <- (nat_smul_respects A k a b Hab).
  exact Hka.
Defined.

Definition torsion_zero (A : AbObject) : torsion_mem A (cmon_zero A).
Proof.
  exists 1%nat; split; [ lia | ].
  apply nat_smul_zero.
Defined.

Lemma torsion_scale (A : AbObject) (j k : nat) (a : carrier A) :
  nat_smul A k a ≈ cmon_zero A →
  nat_smul A (j * k) a ≈ cmon_zero A.
Proof.
  intro Hk.
  rewrite nat_smul_mul, Hk.
  apply nat_smul_zero.
Defined.

Definition torsion_plus (A : AbObject) (a b : carrier A) :
  torsion_mem A a → torsion_mem A b →
  torsion_mem A (cmon_plus A a b).
Proof.
  intros [k [Hk Hka]] [l [Hl Hlb]].
  exists (k * l)%nat; split; [ lia | ].
  assert (Ha : nat_smul A (k * l) a ≈ cmon_zero A).
  { rewrite (Nat.mul_comm k l).
    exact (torsion_scale A l k a Hka). }
  assert (Hb : nat_smul A (k * l) b ≈ cmon_zero A).
  { exact (torsion_scale A k l b Hlb). }
  rewrite nat_smul_plus, Ha, Hb.
  apply cmon_plus_zero_l.
Defined.

Definition torsion_neg (A : AbObject) (a : carrier A) :
  torsion_mem A a → torsion_mem A (ab_neg A a).
Proof.
  intros [k [Hk Hka]].
  exists k; split; [ exact Hk | ].
  rewrite nat_smul_neg, Hka.
  apply ab_neg_zero.
Defined.

Definition TorsionSub (A : AbObject) : AbSubgroup A := {|
  absub_mem   := torsion_mem A;
  absub_resp  := torsion_resp A;
  absub_zero  := torsion_zero A;
  absub_plus  := torsion_plus A;
  absub_neg   := torsion_neg A
|}.

Definition TorsionAb (A : AbObject) : AbObject :=
  AbSubgroupAb (TorsionSub A).

Definition torsion_incl (A : AbObject) : TorsionAb A ~{Ab}~> A :=
  absub_incl (TorsionSub A).

(** * Torsion-free groups / * 无挠群 *)

Definition TorsionFree (A : AbObject) : Type :=
  ∀ (a : carrier A) (k : nat),
    (0 < k)%nat → nat_smul A k a ≈ cmon_zero A → a ≈ cmon_zero A.

Definition TorsionFree_Sub : Subcategory Ab :=
  @Build_Subcategory Ab
    TorsionFree
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition TorsionFreeAb : Category := Sub Ab TorsionFree_Sub.

Lemma TorsionFree_Full :
  Category.Construction.Subcategory.Full Ab TorsionFree_Sub.
Proof. intros x y ox oy g; exact I. Defined.

Lemma TorsionFree_Incl_Full :
  Functor.Full (Incl Ab TorsionFree_Sub).
Proof. exact (Full_Implies_Full_Functor Ab TorsionFree_Sub
                TorsionFree_Full). Defined.

Lemma TorsionFree_Incl_Faithful :
  Functor.Faithful (Incl Ab TorsionFree_Sub).
Proof. exact (Incl_Faithful Ab TorsionFree_Sub). Defined.

(* * * The quotient by the torsion subgroup / * * 通过挠曲子群的商 *)

Definition AbModTorsion (A : AbObject) : AbObject :=
  AbQuotient (torsion_incl A).

(*
 The quotient reuses [A]'s own zero and addition, so those two fields
 agree with [A]'s ON THE NOSE ([quot_zero_strict], [quot_plus_strict])
 and the scalar action agrees at every CLOSED scalar
 ([nat_smul_quot_two]).  At a VARIABLE scalar it does not: [nat_smul]
 is a [Fixpoint] stuck on [k], so conversion is left comparing the two
 [AbObject]s themselves, which differ in their setoid field and in
 every law field (one differing law field already suffices, measured
 in the header).  The agreement is therefore a one-line induction
 rather than [eq_refl] --
 measured, and the [eq_refl] form is pinned in
 Test/ProbeTorsionFree371.v. 

 --------
 商重用了 [A] 自己的零和加法，所以这两个字段与 [A] 的完全一致（[quot_zero_strict]，[quot_plus_strict]），并且在每个闭标量上标量作用也一致（[nat_smul_quot_two]）。在一个可变标量上就不一致了：[nat_smul] 是卡在 [k] 上的 [Fixpoint]，因此转换只能比较两个 [AbObject] 本身，它们在等价集字段和所有定律字段上都不同（只要有一个定律字段不同就足够了，用标题来衡量）。因此，一致性是单行归纳而不是 [eq_refl] --经衡量，[eq_refl] 形式固定在 Test/ProbeTorsionFree371.v 中。
*)

Example quot_zero_strict (A : AbObject) :
  cmon_zero (AbModTorsion A) = cmon_zero A := eq_refl.

Example quot_plus_strict (A : AbObject) (x y : carrier A) :
  cmon_plus (AbModTorsion A) x y = cmon_plus A x y := eq_refl.

Example nat_smul_quot_two (A : AbObject) (x : carrier A) :
  nat_smul (AbModTorsion A) 2 x = nat_smul A 2 x := eq_refl.

Lemma nat_smul_quot (A : AbObject) (k : nat) (x : carrier A) :
  nat_smul (AbModTorsion A) k x = nat_smul A k x.
Proof.
  induction k as [|j IH]; simpl; [ reflexivity | now rewrite IH ].
Qed.

Definition quot_eq_intro (A : AbObject) (x y t : carrier A)
    (Ht : torsion_mem A t) (H : x ≈ cmon_plus A y t) :
  @equiv (carrier (AbModTorsion A)) _ x y.
Proof. exists (existT _ t Ht); apply pequiv_from; exact H. Defined.

(*
 AN EARLIER REVISION of the eliminator returned data:

 quot_eq_elim (A) (x y) : x ≈ y in A/tors →
 { t & (torsion_mem A t * (x ≈ cmon_plus A y t))%type }

 Since the PR “algebraic carriers are sets” (2026-09-17) the coset relation
 of Instance/Ab.v is a [Prop], so the torsion witness may not be read back
 out into a [Type].  The eliminator is therefore stated in CONTINUATION
 form, eliminating into an arbitrary [Prop]: every consumer in the tree
 wanted the witness only to finish a proof, and reaches its own goal by
 [pequiv_to] first.  [torsion_mem] itself stays [Type]-valued -- nothing
 about the predicate changes. 

 --------
 较早的消除器修订版返回数据：

 quot_eq_elim (A) (x y) : x ≈ y 在 A/tors →
 { t & (torsion_mem A t * (x ≈ cmon_plus A y t))%type }

 自从 PR “代数载体是集合”（2026-09-17）以来，Instance/Ab.v 的陪集关系是一个 [Prop]，因此扭转证据可能无法读回到一个 [Type]。消除器因此以 CONTINUATION 形式陈述，消除到任意的 [Prop]：树中的每个使用者只需证据以完成证明，并通过 [pequiv_to] 首先达到自己的目标。[torsion_mem] 本身保持 [Type] 值——谓词没有任何变化。
*)
Definition quot_eq_elim (A : AbObject) (x y : carrier A) (P : Prop)
  (H : @equiv (carrier (AbModTorsion A)) _ x y)
  (k : ∀ t : carrier A,
         torsion_mem A t → x ≈ cmon_plus A y t → P) : P.
Proof.
  destruct H as [[t Ht] Hxt].
  exact (k t Ht (pequiv_to _ _ Hxt)).
Defined.

Definition AbModTorsion_TorsionFree (A : AbObject) :
  TorsionFree (AbModTorsion A).
Proof.
  intros x k Hk Hx.
  rewrite nat_smul_quot in Hx.
  apply (@pequiv_to _ _ (cmon_prop (AbModTorsion A))).
  apply (quot_eq_elim A _ _ _ Hx); intros t [l [Hl Hlt]] Hxt.
  apply pequiv_from.
  apply (quot_eq_intro A x (cmon_zero A) x).
  - exists (l * k)%nat; split; [ lia | ].
    rewrite nat_smul_mul.
    assert (Hkx : nat_smul A k x ≈ t).
    { transitivity (cmon_plus A (cmon_zero A) t).
      - exact Hxt.
      - apply cmon_plus_zero_l. }
    rewrite Hkx, Hlt.
    reflexivity.
  - symmetry; apply cmon_plus_zero_l.
Defined.

Definition TorsionFreeMod (A : AbObject) : TorsionFreeAb :=
  (AbModTorsion A; AbModTorsion_TorsionFree A).

(** * The universal property / * 泛性质 *)

Definition torsion_kills {A B : AbObject} (HB : TorsionFree B)
    (f : A ~{Ab}~> B) (t : carrier A) :
  torsion_mem A t → cmon_map f t ≈ cmon_zero B.
Proof.
  intros [k [Hk Hkt]].
  apply (HB _ k Hk).
  rewrite <- nat_smul_hom, Hkt.
  apply cmon_map_zero.
Defined.

Program Definition torsion_med {A B : AbObject} (HB : TorsionFree B)
    (f : A ~{Ab}~> B) : AbModTorsion A ~{Ab}~> B :=
  {| cmon_map := {| morphism := fun x : carrier A => cmon_map f x |} |}.
Next Obligation.
  intros x y Hxy.
  apply (@pequiv_to _ _ (cmon_prop B)).
  apply (quot_eq_elim A x y _ Hxy); intros t Ht Hxt.
  apply pequiv_from.
  rewrite Hxt, cmon_map_plus, (torsion_kills HB f t Ht).
  apply cmon_plus_zero_r.
Qed.
Next Obligation. apply cmon_map_zero. Qed.
Next Obligation. apply cmon_map_plus. Qed.

Theorem torsion_universal (A : AbObject) :
  ∀ (d : TorsionFreeAb) (f : A ~{Ab}~> Incl Ab TorsionFree_Sub d),
    ∃! g : TorsionFreeMod A ~{TorsionFreeAb}~> d,
      f ≈ fmap[Incl Ab TorsionFree_Sub] g
             ∘ ab_quot_proj (torsion_incl A).
Proof.
  intros d f.
  unshelve eexists.
  - exact (torsion_med `2 d f; I).
  - intro a; simpl; reflexivity.
  - intros g Hg a; simpl.
    exact (Hg a).
Defined.

Definition torsion_universal_arrow (A : AbObject)
  : @UniversalArrow Ab TorsionFreeAb A (Incl Ab TorsionFree_Sub) :=
  @universal_arrow_from_UMP Ab TorsionFreeAb A (Incl Ab TorsionFree_Sub)
    (TorsionFreeMod A) (ab_quot_proj (torsion_incl A))
    (torsion_universal A).

Definition TorsionFree_reflector : Ab ⟶ TorsionFreeAb :=
  LeftAdjointFunctorFromUniversalArrows (Incl Ab TorsionFree_Sub)
    torsion_universal_arrow.

Definition TorsionFree_adj
  : TorsionFree_reflector ⊣ Incl Ab TorsionFree_Sub :=
  AdjunctionFromUniversalArrows (Incl Ab TorsionFree_Sub)
    torsion_universal_arrow.

Definition TorsionFree_Reflective : Reflective TorsionFree_Sub :=
  @Build_Reflective Ab TorsionFree_Sub TorsionFree_Full
    TorsionFree_reflector TorsionFree_adj.

(** * Strict readbacks / * 严格复述 *)

Example torsion_reflector_obj (A : AbObject) :
  `1 (fobj[TorsionFree_reflector] A) = AbModTorsion A := eq_refl.

Example torsion_arrow_is_proj (A : AbObject) :
  @arrow Ab TorsionFreeAb A (Incl Ab TorsionFree_Sub)
    (torsion_universal_arrow A)
    = ab_quot_proj (torsion_incl A) := eq_refl.

Example torsion_arrow_obj (A : AbObject) :
  @arrow_obj Ab TorsionFreeAb A (Incl Ab TorsionFree_Sub)
    (torsion_universal_arrow A)
    = TorsionFreeMod A := eq_refl.

Definition torsion_unit (A : AbObject)
  : A ~{Ab}~> Incl Ab TorsionFree_Sub (fobj[TorsionFree_reflector] A) :=
  @Category.Theory.Adjunction.unit _ _ _ _ TorsionFree_adj A.

Example torsion_unit_is_proj (A : AbObject) (a : carrier A) :
  cmon_map (torsion_unit A) a = cmon_map (ab_quot_proj (torsion_incl A)) a
  := eq_refl.

Lemma torsion_unit_is_proj_hom (A : AbObject) :
  torsion_unit A ≈ ab_quot_proj (torsion_incl A).
Proof. intro a; reflexivity. Defined.

(* * * The counit at a torsion-free group / * * 在无挠群上的余单位 *)

Definition torsionfree_reflect_iso (x : TorsionFreeAb) :
  fobj[TorsionFree_reflector] (Incl Ab TorsionFree_Sub x)
    ≅[TorsionFreeAb] x :=
  reflective_counit_iso TorsionFree_Reflective x.

(** * Non-vacuity: the integers / * 非空性：整数 *)

Lemma nat_smul_ZAb (k : nat) (n : carrier ZAb) :
  nat_smul ZAb k n = Z.mul (Z.of_nat k) n.
Proof.
  induction k as [|j IH].
  - reflexivity.
  - change (nat_smul ZAb (S j) n) with (Z.add n (nat_smul ZAb j n)).
    rewrite IH; lia.
Qed.

(*
 The case split on [Z.mul_eq_0] lands in [or], which is [Prop] and
 cannot be eliminated into the [Type]-sorted [≈]; it is therefore made
 inside this [Prop]-valued lemma and consumed by [exact] below. 

 --------
 这个情况在 [Z.mul_eq_0] 土地上分裂到 [or] ，这是 [Prop] ，且无法被消除到 [Type] 排序的 [≈]；因此它是在这个 [Prop] 值的引理中产生的，并被下面的 [exact] 消耗。
*)
Lemma ZAb_torsionfree_elt (n : carrier ZAb) (k : nat) :
  (0 < k)%nat → Z.mul (Z.of_nat k) n = 0%Z → n = 0%Z.
Proof.
  intros Hk H.
  apply Z.mul_eq_0 in H.
  destruct H as [Hz|Hz]; [ lia | exact Hz ].
Qed.

Definition ZAb_TorsionFree : TorsionFree ZAb.
Proof.
  intros n k Hk H.
  assert (H' : Z.mul (Z.of_nat k) n = 0%Z).
  { rewrite <- nat_smul_ZAb; exact H. }
  exact (ZAb_torsionfree_elt n k Hk H').
Defined.

Lemma ZAb_torsion_trivial (n : carrier ZAb) :
  torsion_mem ZAb n → n = 0%Z.
Proof.
  intros [k [Hk Hkn]].
  exact (ZAb_TorsionFree n k Hk Hkn).
Qed.

Definition ZAb_TF : TorsionFreeAb := (ZAb; ZAb_TorsionFree).

(*
 ℤ/T(ℤ) ≅ ℤ, by pure instantiation of the counit isomorphism -- no
 tactic, and no fact about ℤ beyond [ZAb_TorsionFree].  The two are NOT
 equal: [AbModTorsion ZAb] carries the coarsened setoid, and the
 [eq_refl] form is pinned in Test/ProbeTorsionFree371.v. 

 --------
 ℤ/T(ℤ) ≅ ℤ，通过对余单位同构的纯实例化——不需要策略，也不需要关于 ℤ 的事实，除了 [ZAb_TorsionFree]。两者不是相等的：[AbModTorsion ZAb] 携带粗化的集合型等价关系，而 [eq_refl] 形式则固定在 Test/ProbeTorsionFree371.v 中。
*)
Definition ZAb_reflect_iso :
  fobj[TorsionFree_reflector] (Incl Ab TorsionFree_Sub ZAb_TF)
    ≅[TorsionFreeAb] ZAb_TF :=
  torsionfree_reflect_iso ZAb_TF.

(* * * Non-vacuity: ℤ/2 is all torsion / * * 非空性：ℤ/2 全部都是挠元 *)

Definition ZMod2_all_torsion (b : carrier ZMod2) : torsion_mem ZMod2 b.
Proof.
  exists 2%nat; split; [ lia | ].
  destruct b; reflexivity.
Defined.

Lemma ZMod2_not_TorsionFree : TorsionFree ZMod2 → False.
Proof.
  intro H.
  destruct (ZMod2_all_torsion true) as [k [Hk Hkt]].
  assert (Hb : true = false) by exact (H true k Hk Hkt).
  discriminate.
Qed.

Example ZMod2_quot_collapses :
  @equiv (carrier (AbModTorsion ZMod2)) _ true false.
Proof.
  apply (quot_eq_intro ZMod2 true false true).
  - exact (ZMod2_all_torsion true).
  - reflexivity.
Defined.

(** * Non-vacuity: a mixed group / * 非空性：一个混合群体 *)

Definition MixedAb : AbObject := Ab_product ZAb ZMod2.

Definition mixed_tors : carrier MixedAb := (cmon_zero ZAb, true).
Definition mixed_gen : carrier MixedAb := (ZAb_one, false).

Definition mixed_tors_torsion : torsion_mem MixedAb mixed_tors.
Proof.
  exists 2%nat; split; [ lia | ].
  split; reflexivity.
Defined.

(*
 [mixed_tors] is a torsion element that is not zero, so [TorsionSub] is
 NONTRIVIAL at [MixedAb]; [mixed_gen_not_torsion] makes it PROPER. 

 --------
 [mixed_tors] 是一个非零的扭转元，因此 [TorsionSub] 在 [MixedAb] 处是非平凡的；[mixed_gen_not_torsion] 使其成为合适的。
*)
Lemma mixed_tors_not_zero :
  @equiv (carrier MixedAb) _ mixed_tors (cmon_zero MixedAb) → False.
Proof.
  intros [_ H]; simpl in H; discriminate.
Qed.

Lemma mixed_gen_not_torsion : torsion_mem MixedAb mixed_gen → False.
Proof.
  intros [k [Hk Hkg]].
  assert (Hz : nat_smul ZAb k ZAb_one ≈ cmon_zero ZAb).
  { rewrite <- (nat_smul_hom (Ab_exl ZAb ZMod2) k mixed_gen).
    exact (fst Hkg). }
  rewrite nat_smul_int_one in Hz.
  assert (Hz' : Z.of_nat k = 0%Z) by exact Hz.
  lia.
Qed.

Example mixed_quot_merges :
  @equiv (carrier (AbModTorsion MixedAb)) _ mixed_tors
    (cmon_zero MixedAb).
Proof.
  apply (quot_eq_intro MixedAb mixed_tors (cmon_zero MixedAb) mixed_tors).
  - exact mixed_tors_torsion.
  - split; reflexivity.
Defined.

Lemma mixed_gen_not_quot_zero :
  @equiv (carrier (AbModTorsion MixedAb)) _ mixed_gen
    (cmon_zero MixedAb) → False.
Proof.
  intro H.
  (* The goal is [False], a [Prop], so the continuation-form eliminator applies directly. / 目标是 [False]，一个 [Prop]，因此直接应用连续形式消除器。 *)
  apply (quot_eq_elim MixedAb _ _ _ H); intros t Ht Hgt.
  apply mixed_gen_not_torsion.
  apply (torsion_resp MixedAb t mixed_gen).
  - rewrite Hgt; symmetry; apply cmon_plus_zero_l.
  - exact Ht.
Qed.
