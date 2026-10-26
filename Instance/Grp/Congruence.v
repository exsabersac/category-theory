Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Transform.
Require Import Category.Structure.Groupoid.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.

(*
 [Category.Instance.Grp] and its satellites are required LAST, deliberately,
 for the reason [Instance/Grp/Free.v] gives: [Construction/Deloop.v]
 also declares a record called [GrpObject], and the two names would
 otherwise collide.  With this order the unqualified [GrpObject],
 [grp_unit], [grp_mul] and [grp_inv] below are always [Instance/Grp.v]'s --
 the record [Grp] is the category of, and hence the record #313's
 [NormalSubgroup] and [QuotientGrp] are over.  Construction/Deloop.v's
 record and its projection are named in full, as
 [Category.Construction.Deloop.GrpObject] and
 [Category.Construction.Deloop.grp_monoid], on the two occasions they are
 mentioned in code (in [grp_deloop_GrpObject] and in
 [deloop_GrpObject_monoid]). 

 --------
 [Category.Instance.Grp]及其卫星必须最后声明，这是出于[Instance/Grp/Free.v]给出的原因：[Construction/Deloop.v]也声明了一个名为[GrpObject]的记录，否则这两个名称会冲突。按照这个顺序，下列未限定的[GrpObject]、[grp_unit]、[grp_mul]和[grp_inv]总是[Instance/Grp.v]的——记录[Grp]是类别，因此记录#313的[NormalSubgroup]和[QuotientGrp]已经结束。Construction/Deloop.v的记录及其投影在代码中两次提及时（在[grp_deloop_GrpObject]和[deloop_GrpObject_monoid]中），完整命名为[Category.Construction.Deloop.GrpObject]和[Category.Construction.Deloop.grp_monoid]。
*)
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Quotient.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * * Congruences on a delooped group are normal subgroups

   Mac Lane, “Categories for the Working Mathematician”, 2nd ed., §II.8
   Exercise 2, printed p. 52 [maclane:II.8:ex2]; Awodey, “Category
   Theory”, 2nd ed., §4.2 printed p. 83 [awodey:4.2:def-normal-subgroup]
   and §4.5 Exercise 1, printed p. 91 [awodey:4:ex1].
   nLab: https://ncatlab.org/nlab/show/normal+subgroup
   nLab: https://ncatlab.org/nlab/show/congruence
   Wikipedia: https://en.wikipedia.org/wiki/Normal_subgroup

   A group read as a one-object category has, for its hom-set, the group
   itself; a congruence on that category is therefore an equivalence
   relation on the group compatible with multiplication on both sides.
   Mac Lane's exercise is that such relations are exactly the normal
   subgroups: from N one takes “f and g differ by a member of N”, and
   from a congruence one takes the class of the identity.  Quotienting
   the category then returns the delooping of the factor group, so
   Awodey's group homomorphism theorem is the universal property of the
   quotient CATEGORY read at one object.

   WHY THE INTERESTING PART IS A NAMING PROBLEM.  The tree carries TWO
   records called [GrpObject], and the exercise straddles them.
   [Construction/Deloop.v] layers one on [MonObject], carrying both
   unit laws and both inverse laws as fields; that is the record
   [Deloop]'s group-case results ([Deloop_group_invertible],
   [Deloop_IsGroupoid]) are stated over.  [Instance/Grp.v] declares a
   flat one with only the left-handed laws, the right-handed ones and
   respectfulness of inversion being derived; that is the record [Grp] is
   the category of, and hence the record #313's [NormalSubgroup],
   [QuotientGrp] and [hom_theorem] are over.  A statement of this
   exercise has to reach both.

   HOW THE GAP IS CLOSED, and the measured surprise: NO RECORD
   CONVERSION IS NEEDED, because the delooping of an [Instance/Grp.v]
   group is already in tree.  [Instance/Grp/Free.v] builds
   [grp_deloop_monoid], [grp_deloop] and [grp_deloop_IsGroupoid] --
   incidentally, on its way to the free group -- and that is exactly “the
   one-object groupoid of an [Instance/Grp.v] group”.  Everything below
   is stated over [grp_deloop], so the correspondence is with congruences
   on THE delooping in tree rather than on a fresh copy of it.  (The one
   bridge the tree names, [Instance/Rep.v] [grp_mon], is a
   different thing: it lands in [MonObject] and drops the inverse.
   [Instance/Grp/Free.v] says in terms that [grp_mon] is “the only
   bridge between them in tree”, so no record-to-record converter existed
   at the parent commit -- and this file supplies one below, which is
   exactly what makes that sentence stale rather than a limitation.
   [Instance/Rng/MonoidRing.v] is cited by Free.v's neighbours for a
   RELATED but different observation: that Rep.v “had to bridge two
   identically named [GrpObject] records with [grp_mon]”, which records
   the bridge's existence, not an absence.)  What this file observes is
   that the exercise never needed the converter in the first place.

   THE CONVERSION IS SUPPLIED ANYWAY, AND MEASURED, for the readers who
   do want Construction/Deloop.v's group-case vocabulary:
   [grp_deloop_GrpObject] takes an [Instance/Grp.v] group to a
   [Category.Construction.Deloop.GrpObject], built by REUSE rather than
   by a fresh record literal -- [Structure/Groupoid.v]'s [MonInverses]
   and [GrpObject_of], which exist precisely to separate “has inverses”
   from the bundling.  It is proved NOT to be a third notion:
   [deloop_GrpObject_agrees] is [eq_refl].

   THE BRIDGE THE ISSUE'S QA CORRECTION NAMES IS A DIFFERENT ONE, and is
   deliberately not cited.  That correction directs that #255's Work item
   4 be cited as the reconciliation -- [Instance/Grp.v]'s
   [Grp_GroupObject]/[GroupObject_GrpObject].  Those relate
   [Instance/Grp.v]'s record to [Structure/Group.v]'s INTERNAL
   [GroupObject], a group object in a cartesian monoidal category, which
   is a third notion again and does not reach
   [Construction/Deloop.v]'s bare setoid record.  So it could not have
   closed this gap, and [grp_deloop_GrpObject] is supplied in its
   place.

   WHAT THE FOUR CONGRUENCE FIELDS COST: NOTHING.  [HomCongruence]
   ([Construction/Quotient.v]) asks for containment of `≈`, symmetry,
   transitivity and compatibility with composition.  At [grp_deloop G]
   with the relation “f * g⁻¹ lies in N” these are, in order, #313's
   [quot_rel_of_equiv], [quot_rel_sym], [quot_rel_trans] and
   [quot_rel_mul] -- four of the five [quot_rel] lemmas [QuotientGrp]'s
   own obligations consume (the fifth being [quot_rel_refl], needed there
   for the [Equivalence] and not here), applied verbatim, with no
   argument reordered and no new proof: [ns_congruence] is a record
   literal of four eta-expanded applications of those names.  The same
   reuse runs through the round trip: [ns_of_cong_of_ns]'s whole proof is
   [quot_rel_unit_iff] applied.

   ORIENTATION.  #313's [quot_rel N a b] is “a * b⁻¹ lies in N”, the
   orientation [Instance/Grp/Abelianization.v]'s [abel_eq] fixed; issue
   #301's text writes the condition the other way round, “g⁻¹ * f lies in
   N”.  The two agree, and [quot_rel_flip] proves it -- consuming
   NORMALITY in both directions, so the choice is not a notational one
   for a bare subgroup.

   WHAT IS DELIVERED.

   - [grp_deloop_GrpObject], the record conversion, with
   [deloop_GrpObject_agrees] ([eq_refl]) identifying its delooping
   with the tree's;
   - [ns_rel] / [ns_congruence]: the congruence of a normal subgroup,
   and [deloop_quotient] the quotient category;
   - [cong_ns]: the normal subgroup of a congruence, the class of the
   identity;
   - [ns_of_cong_of_ns] and [cong_of_ns_of_cong]: the two round trips,
   each a biconditional, packaged as [ns_cong_iso], an ISOMORPHISM OF
   SETOIDS in [Sets] between the normal subgroups of G and the
   congruences on its delooping;
   - [congruence_iff_normal]: for an arbitrary SUBGROUP S, the relation
   “f * g⁻¹ in S” is a congruence exactly when S is normal -- so the
   correspondence is with normal subgroups and not merely defined on
   them;
   - [deloop_quotient_iso]: the quotient category of the delooping is
   the delooping of #313's [QuotientGrp N], at [≅[StrictCat]];
   - [hom_theorem_via_quotient_category]: Awodey §4.5 Exercise 1 --
   #313's [hom_theorem] obtained from [Construction/Quotient.v]'s
   [QuotientLift]/[QuotientLift_unique], with the produced mediator
   identified with [quot_med] by [eq_refl] on the underlying map;
   - [kernel_ns] with [kernel_ns_iff]: Awodey §4.2's kernel clause
   given its categorical provenance -- the kernel of a group
   homomorphism is normal because the kernel congruence of a FUNCTOR
   is a congruence ([FunctorKernel_Congruence]) -- WITHOUT re-proving
   #313's [KernelNS], which is cited and left alone;
   - [coset_orientations_differ]: the two orientations of the coset
   relation are not interchangeable once normality is dropped,
   witnessed over #313's non-normal [S3_refl_sub];
   - the S3 witnesses, both signs.

   WHAT IS NOT DELIVERED.  No congruence lattice and no correspondence
   theorem (the subgroups of G/N); no functoriality of N ↦ [ns_rel N] in
   G; no comparison with [Construction/Quotient.v]'s generated congruence
   [CongClosure] (the normal closure of a subgroup is
   [Instance/Grp/Quotient/Colimit.v]'s, and no claim is made that the two
   closures agree); no CONGRUENCE or NORMAL-SUBGROUP statement over
   [Construction/Deloop.v]'s own [GrpObject], since #313's machinery is
   over [Instance/Grp.v]'s -- that record occurs in this file only in
   [grp_deloop_GrpObject]'s type and in the three constants built from
   it ([deloop_GrpObject_agrees], [deloop_GrpObject_monoid],
   [grp_deloop_IsGroupoid']), all in the conversion subsection; no monoid
   analogue -- [cong_ns] spends both inverse laws (in its
   closure-under-inverse and normality fields, and again in
   [cong_of_ns_of_cong]), so nothing below says anything about
   congruences on a delooped MONOID, and no claim is made about what they
   correspond to; and no Leibniz equality of the two categories in
   [deloop_quotient_iso].  That last one is MEASURED rather than merely
   unproved -- Test/ProbeGrpCongruence.v, negative 3, records that
   conversion rejects the identification at the current definitions --
   but it is not PROVED: no inequality is stated, here or anywhere
   (the wording follows [Theory/Universal/Arrow/Dual.v]'s).

   THE CATEGORY-LEVEL HOMOMORPHISM THEOREM EXISTS, UNDER NO SUCH NAME.
   Awodey's Exercise 1 asks for the group theorem as a SPECIALIZATION,
   which presupposes something to specialize, so the tree was searched
   before the word was used.  A case-insensitive search for the phrase
   “homomorphism theorem” over every .v file returns, outside this file's
   own prose, exactly one hit -- [Instance/Grp/Quotient.v] -- and
   that is the GROUP statement.  So nothing in the tree is NAMED the
   categorical homomorphism theorem.  The STATEMENT is nevertheless
   present, as the universal property of the quotient category:
   [Construction/Quotient.v]'s [QuotientLift] (the lift),
   [QuotientLift_factors_strict] (the triangle, at [StrictCat] strength)
   and [QuotientLift_unique] (uniqueness).  So the specialization below
   is real and is not dressing up a group result as a corollary of
   nothing; what had to be checked was that the general statement was
   there, and it is.  (A phrase search is evidence about NAMING; the
   positive claim rests on reading those three constants, not on the
   grep.)

   A MEASUREMENT ABOUT THAT UNIQUENESS, disclosed because it bounds how
   much the specialization proves.  [QuotientLift_unique]'s proof is
   [exact HG]: in a quotient category the projection is the identity on
   morphisms, so “any competitor agreeing with F after the projection
   agrees with the lift” is the hypothesis restated.  Instantiated at the
   delooping that is exactly why the group-level uniqueness comes out
   with no work -- the content sits in [QuotientLift] existing at all,
   and in #313's [kills_descends].  The route below consumes exactly two
   proofs ABOUT N -- that descent lemma, and [quot_rel_refl], which
   supplies the two functor-law fields of [quot_to_deloop] and
   [deloop_to_quot] (four sites in all).  The rest is the
   homomorphism/functor dictionary ([hom_MonHom], [Deloop_map]) together
   with [Build_GrpHom']'s [grp_map_unit_from_mul], a second
   group-theoretic proof.  All three are named here so that the smallness
   claim is not read as covering more than it does; an earlier draft said
   [kills_descends] was the ONLY one, which over-read. 

   --------
   * * 在去圈的群上的同余是正规子群

   Mac Lane，《为工作数学家而写的范畴论》，第2版，第II.8节
   练习2，印刷于第52页  [maclane:II.8:ex2]；Awodey，《范畴论》，第2版，第4.2节印刷于第83页  [awodey:4.2:def-normal-subgroup]
   以及第4.5节练习1，印刷于第91页  [awodey:4:ex1]。
   nLab:  https://ncatlab.org/nlab/show/normal+subgroup
   nLab:  https://ncatlab.org/nlab/show/congruence
   维基百科:  https://en.wikipedia.org/wiki/Normal_subgroup作为一个单对象范畴来阅读的群，其同态集就是该群本身；因此，该范畴上的同余就是一种与双方乘法兼容的群的等价关系。Mac Lane 的练习是，这种关系恰好就是正规子群：从 N 可以得到“f 和 g 相差一个 N 的元素”，而从一个同余可以得到单位元的类。然后对该范畴取商就返回了因子群的去环绕，因此 Awodey 的群同态定理就是在一个对象下阅读的商范畴的普适性质。为什么有趣的部分是命名问题。该树有两个记录，称为 [GrpObject]，而这个练习跨越了它们。[Construction/Deloop.v] 将一个层叠在 [MonObject] 上，作为字段包含了两个单位律和两个逆律；也就是说，记录 [Deloop] 的群案例结果（[Deloop_group_invertible]，[Deloop_IsGroupoid]）已被说明。[Instance/Grp.v] 声明了一个仅包含左手律的平面记录，右手律和逆运算的尊重性是派生的；也就是说，记录 [Grp] 是该类别的，因此记录 #313 的 [NormalSubgroup]、[QuotientGrp] 和 [hom_theorem] 也在其上。这个练习的陈述必须涵盖两者。如何弥合差距，以及测得的惊讶：不需要记录转换，因为一个 [Instance/Grp.v] 群的去环已经在树中。[Instance/Grp/Free.v] 构建 [grp_deloop_monoid]、[grp_deloop] 和 [grp_deloop_IsGroupoid]——顺便说一句，在它通向自由群的过程中——这正是“一个 [Instance/Grp.v] 群的一对象群体范畴”。以下所有内容都是在 [grp_deloop] 上陈述的，因此对应关系是与树中去环的同余而不是它的新副本。（树命名的唯一桥，[Instance/Rep.v] [grp_mon]，是另一件事：它降落在 [MonObject] 并去掉逆元。）[Instance/Grp/Free.v] 表示 [grp_mon] 是“它们之间在树中的唯一桥”，所以在父提交中不存在记录到记录的转换器——而这个文件在下面提供了一个，这正是使得那句话显得过时而不是限制的原因。[Instance/Rng/MonoidRing.v] 被 Free.v 的邻居引用，用于一个相关但不同的观察：Rep.v “必须用 [grp_mon] 架起两个同名的 [GrpObject] 记录之间的桥”，这记录了桥的存在，而不是其不存在。）这个文件观察到的是，这个操作根本不需要这个转换器。无论如何，转换已经提供并进行了测量，供那些确实想使用 Construction/Deloop.v 的组案例词汇的读者参考：
   [grp_deloop_GrpObject] 将一个 [Instance/Grp.v] 组转换为一个 [Category.Construction.Deloop.GrpObject]，该组由 REUSE 构建，而不是通过新的记录字面量构建——[Structure/Groupoid.v] 的 [MonInverses] 和 [GrpObject_of] 正是为了将“具有逆元”与捆绑分开而存在。已经证明这不是第三种概念：[deloop_GrpObject_agrees] 是 [eq_refl]。桥梁问题的QA更正名称是不同的，并且是故意未被引用的。该更正指示将#255的工作项4引用为调节——[Instance/Grp.v]的[Grp_GroupObject] / [GroupObject_GrpObject]。这些将[Instance/Grp.v]的记录与[Structure/Group.v]的内部[GroupObject]相关联，这是笛卡尔单体范畴中的一个群对象，这又是第三种概念，并未达到[Construction/Deloop.v]的基本集合类记录。因此它无法弥补这一差距，并且[grp_deloop_GrpObject]被替代提供。四个同余域的成本：无。   [HomCongruence]（[Construction/Quotient.v]）要求包含`≈`、对称性、传递性以及与组合的兼容性。在[grp_deloop G]中，关系“f * g⁻¹属于N”下，这些依次是#313的[quot_rel_of_equiv]、[quot_rel_sym]、[quot_rel_trans]和[quot_rel_mul]——四个[quot_rel]引理，[QuotientGrp]本人的义务消耗了（第五个是[quot_rel_refl]，在那里为[Equivalence]所需，而在这里不需要），直接照搬应用，没有重新排列论证，也没有新的证明：[ns_congruence]是对这些名称四次eta展开应用的记录字面值。同样的复用贯穿往返：[ns_of_cong_of_ns]的整个证明是[quot_rel_unit_iff]的应用。方向。#313 的 [quot_rel N a b] 是“a * b⁻¹ 位于 N”，方向 [Instance/Grp/Abelianization.v] 的 [abel_eq] 已固定；#301 的文本以相反方式写条件，“g⁻¹ * f 位于 N”。两者一致，[quot_rel_flip] 证明了这一点——在两个方向上都使用了正规性，因此对于一个普通子群，这个选择不是符号上的问题。

   已交付的内容。- [grp_deloop_GrpObject]，记录转换，使用 [deloop_GrpObject_agrees]（[eq_refl]）识别其与树的去环(looping)；
   - [ns_rel] / [ns_congruence]：正规子群的合同(congruence)，以及 [deloop_quotient] 商范畴；
   - [cong_ns]：合同的正规子群，单位元的类；
   - [ns_of_cong_of_ns] 和 [cong_of_ns_of_cong]：两个往返，每个都是双条件，封装为 [ns_cong_iso]，即 [Sets] 中 G 的正规子群与其去环合同之间的集合同构(ISOMORPHISM OF SETOIDS)；
   - [congruence_iff_normal]：对于任意子群(SUBGROUP) S，关系“f * g⁻¹ ∈ S”恰当构成合同，当且仅当 S 为正规子群——因此对应的是正规子群，而不仅仅是定义在其上的关系；
   - [deloop_quotient_iso]：的商范畴去环是对 #313 的 [QuotientGrp N] 在 [≅[StrictCat] 上进行去环；
   - [hom_theorem_via_quotient_category]：Awodey 第 4.5 节练习 1 —— #313 的 [hom_theorem] 来源于 [Construction/Quotient.v] 的 [QuotientLift] / [QuotientLift_unique]，生成的中介由 [eq_refl] 在底层映射上确定为 [quot_med]；
   - [kernel_ns] 与 [kernel_ns_iff]：给出其范畴渊源的 Awodey 第 4.2 节核条款——群同态的核是正规子群，因为函子(FUNCTOR)的核同余是一个同余 ([FunctorKernel_Congruence])——无需重新证明 #313 的 [KernelNS]，该内容被引用并保持不变；
   - [coset_orientations_differ]：一旦去掉正规性，两种陪类关系的方向不可互换，这可在 #313 的非正规 [S3_refl_sub] 上看到；
   - S3 的见证元素，两种符号。

   未交付的内容。没有同余格，也没有对应定理（G/N 的子群）；N ↦ [ns_rel N] 在 G 中没有函子性；没有与 [Construction/Quotient.v] 生成的同余 [CongClosure] 的比较（子群的正规闭包是 [Instance/Grp/Quotient/Colimit.v] 的，并且没有声称这两个闭包一致）；没有关于 [Construction/Deloop.v] 自身 [GrpObject] 的同余或正规子群声明，因为 #313 的机制是基于 [Instance/Grp.v] 的——那个记录只在这个文件中出现在 [grp_deloop_GrpObject] 的类型以及由它构建的三个常量（[deloop_GrpObject_agrees]，[deloop_GrpObject_monoid]，[grp_deloop_IsGroupoid']）中，全部在转换子部分；没有幺半群的类似物——[cong_ns] 同时用于两个逆律（在其闭包-逆与正规性字段中，以及在 [cong_of_ns_of_cong] 中再次出现），所以下面没有内容谈论去圈化幺半群上的同余。没有关于它们对应关系的任何声明；并且在 [deloop_quotient_iso] 中这两个范畴也没有莱布尼茨等价。最后一个是经过测量的，而不仅仅是未经证明的——Test/ProbeGrpCongruence.v，负3，记录了在当前定义下转换拒绝了标识——但它并未被证明：这里或任何地方都没有说明不等式（措辞遵循[Theory/Universal/Arrow/Dual.v]的）。类别级同态定理在没有这样的名称下存在。Awodey 的练习题 1 将群定理作为一种特例提出，这预设了某种可特化的对象，因此在使用该词之前搜索了树。在每个 .v 文件中对短语“homomorphism theorem”进行不区分大小写的搜索，在该文件自身的文本之外恰好返回一次命中——[Instance/Grp/Quotient.v]——且那就是群陈述。因此，树中没有任何内容被命名为类别同态定理。然而，该陈述仍然存在，作为商范畴的泛性质：[Construction/Quotient.v] 的 [QuotientLift]（提升），[QuotientLift_factors_strict]（三角形，在 [StrictCat] 强度下）以及 [QuotientLift_unique]（唯一性）。所以下面的专业化是真实的，并不是把一个群的结果包装成无中生有的推论；需要检查的是一般性的陈述是否存在，而确实存在。（短语搜索是关于命名的证据；肯定的主张依赖于阅读那三个常量，而不是依赖 grep。）关于这种独特性的一个度量，因为它限制了特化能证明的程度而被披露。[QuotientLift_unique] 的证明是 [exact HG]：在商范畴中，投影在态射上是恒等的，所以“任何在投影后与 F 一致的竞争者都与提升一致”就是重新表述的假设。在去环绕处实例化，这正是群级别唯一性无需操作就能得出的原因——内容在于 [QuotientLift] 的存在，以及在 #313 的 [kills_descends] 中。下面的路径正好消耗两个关于 N 的证明——那个下降引理，以及 [quot_rel_refl]，它提供了 [quot_to_deloop] 和 [deloop_to_quot] 的两个函子定律域（总共四个位置）。其余的是同态/函子字典（[hom_MonHom]，[Deloop_map]）以及[Build_GrpHom']的[grp_map_unit_from_mul]，第二个群论证明。这里列出所有三个的名称，以便小规模性声明不会被理解为涵盖超过实际范围；早期版本中曾说[kills_descends]是唯一的一个，这属于过度解读。
*)

(*
   * ** The record conversion, supplied and measured

   [Instance/Grp.v]'s group as a [Category.Construction.Deloop.GrpObject].
   The inverse operation and its two laws are packaged first as
   [Structure/Groupoid.v]'s [MonInverses] -- the record that file
   introduced to separate “this monoid has inverses” from the bundling --
   and [GrpObject_of] does the bundling.  The right inverse law is
   [Instance/Grp.v]'s DERIVED [grp_mul_inv_r], not a field. 

   --------
   * ** 记录转换，已提供并测量

   [Instance/Grp.v] 的组作为 [Category.Construction.Deloop.GrpObject]。
   逆运算及其两个定律首先被打包为
   [Structure/Groupoid.v] 的 [MonInverses] —— 记录文件
   引入以将“这个幺半群有逆元”与捆绑分开——
   而 [GrpObject_of] 进行捆绑。右逆定律是
   [Instance/Grp.v] 的 DERIVED [grp_mul_inv_r]，而不是域。
*)

Definition grp_MonInverses (H : GrpObject) : MonInverses (grp_deloop_monoid H) :=
  @Build_MonInverses (grp_deloop_monoid H)
    (grp_inv H) (grp_mul_inv_l H) (grp_mul_inv_r H).

Definition grp_deloop_GrpObject (H : GrpObject)
  : Category.Construction.Deloop.GrpObject :=
  GrpObject_of (grp_MonInverses H).

(*
   * The conversion introduces no third delooping: the category it produces
   IS [Instance/Grp/Free.v]'s [grp_deloop H], by convertibility -- the
   [eq_refl] exception to the `≈` discipline, and the check that
   [GrpObject_of] moved fields rather than rebuilding them. 

   --------
   * 该转换不会引入第三次去环：它产生的类别是  [Instance/Grp/Free.v] 的 [grp_deloop H]，通过可转换性—— [eq_refl] 对 `≈` 纪律的例外，以及检查 [GrpObject_of] 是移动了字段而不是重新构建它们。
*)
Example deloop_GrpObject_agrees (H : GrpObject) :
  Deloop (grp_deloop_GrpObject H) = grp_deloop H := eq_refl.

Example deloop_GrpObject_monoid (H : GrpObject) :
  Category.Construction.Deloop.grp_monoid (grp_deloop_GrpObject H)
    = grp_deloop_monoid H := eq_refl.

(*
   * Consequently [Construction/Deloop.v]'s group-case result is available
   at an [Instance/Grp.v] group, and its chosen inverse is the group
   inverse on the nose -- as is [Instance/Grp/Free.v]'s own witness.  The
   two [IsGroupoid] structures are NOT the same term (their [IsIsomorphism]
   law fields are separately proved), which is measured rather than
   assumed: Test/ProbeGrpCongruence.v, negative 1. 

   --------
   * 因此，[Construction/Deloop.v] 的群-情况结果可用于 [Instance/Grp.v] 群，并且其选择的逆元恰好是群的逆元——就像 [Instance/Grp/Free.v] 自身的证据一样。两个 [IsGroupoid] 结构并非相同的项（它们的 [IsIsomorphism] 法则字段是单独证明的），这是通过测量而不是假设得出的：Test/ProbeGrpCongruence.v, -1。
*)
Definition grp_deloop_IsGroupoid' (H : GrpObject) : IsGroupoid (grp_deloop H) :=
  Deloop_IsGroupoid (grp_deloop_GrpObject H).

Example grp_deloop_ginv (H : GrpObject) (a : carrier H) :
  ginv (grp_deloop_IsGroupoid' H) (x:=ttt) (y:=ttt) a = grp_inv H a := eq_refl.

Example grp_deloop_ginv_Free (H : GrpObject) (a : carrier H) :
  ginv (grp_deloop_IsGroupoid H) (x:=ttt) (y:=ttt) a = grp_inv H a := eq_refl.

(* * ** Arithmetic of the delooping Every one of these is [eq_refl]; they are recorded so that the congruence proofs below can be read as group computations without unfolding [Deloop]. / * ** 去圈代数 这些中的每一个都是 [eq_refl]；它们被记录下来，以便下面的同余证明可以被理解为群运算，而无需展开 [Deloop]。 *)

Section DeloopArithmetic.

Context {G : GrpObject}.

(*
   * An element of G, read as an arrow of the delooping.  Definitional in
   both directions; it exists only to give the elaborator the hom type
   when a [HomCongruence] field is applied to a group element. 

   --------
   * G 的一个元素，读作退环的箭头。在两个方向上都是定义性的；它的存在仅是为了在将 [HomCongruence] 字段应用于群元素时为展开器提供同构类型。
*)
Definition deloop_arr (a : carrier G) : ttt ~{grp_deloop G}~> ttt := a.

Example deloop_hom_type (x y : grp_deloop G) :
  (x ~{grp_deloop G}~> y) = carrier G := eq_refl.

Example deloop_id_is_unit : @id (grp_deloop G) ttt = grp_unit G := eq_refl.

Example deloop_compose_is_mul (f g : carrier G) :
  @compose (grp_deloop G) ttt ttt ttt f g = grp_mul G f g := eq_refl.

End DeloopArithmetic.

(*
   * ** From a normal subgroup to a congruence

   The relation is #313's [quot_rel], constant in the two objects (there
   is only one).  The four [HomCongruence] fields are #313's four
   [quot_rel] lemmas, verbatim. 

   --------
   * ** 从正规子群到同余

   该关系是 #313 的 [quot_rel]，在两个对象中都是常数（这里只有一个对象）。四个 [HomCongruence] 字段是 #313 的四个 [quot_rel] 引理，逐字照搬。
*)

Definition ns_rel {G : GrpObject} (N : NormalSubgroup G)
  : HomRelT (grp_deloop G) := fun _ _ f g => quot_rel N f g.

(*
   * The relation IS [quot_rel], by convertibility -- so every lemma #313
   proves about [quot_rel] is a lemma about this congruence. 

   --------
   * 这个关系是 [quot_rel]，通过可转换性——所以每个引理 #313 关于 [quot_rel] 的结论，都是关于这个同余的引理。
*)
Example ns_rel_is_quot_rel {G : GrpObject} (N : NormalSubgroup G)
  (f g : carrier G) : ns_rel N ttt ttt f g = quot_rel N f g := eq_refl.

(*
   * Mac Lane §II.8 Exercise 2, one direction.  Kept a plain [Definition]
   rather than an [Instance], following [FunctorKernel_Congruence]'s own
   convention in [Construction/Quotient.v]: nothing new enters
   typeclass search, and the witness stays transparent. 

   --------
   * Mac Lane §II.8 练习 2，一个方向。保持一个简单的 [Definition] 而不是 [Instance]，遵循 [FunctorKernel_Congruence] 在 [Construction/Quotient.v] 中自己的约定：没有新的内容进入类型类搜索，并且证人保持透明。
*)
Definition ns_congruence {G : GrpObject} (N : NormalSubgroup G)
  : @HomCongruence (grp_deloop G) (ns_rel N) :=
  @Build_HomCongruence (grp_deloop G) (ns_rel N)
    (fun x y f g H   => quot_rel_of_equiv N f g H)
    (fun x y f g H   => quot_rel_sym N f g H)
    (fun x y f g h H1 H2 => quot_rel_trans N f g h H1 H2)
    (fun x y z f f' g g' H1 H2 => quot_rel_mul N f f' g g' H1 H2).

(*
   * The PROPOSITIONAL congruence: [ns_rel] under [inhabited].

   An earlier revision built [deloop_quotient] from [ns_rel] itself.  Since
   the PR “algebraic carriers are sets” (2026-09-17) [QuotientGrp]'s own
   equality is the propositional truncation of [quot_rel] -- [sub_mem] stays
   [Type]-valued, so the quotient OBJECT must truncate -- and the quotient
   CATEGORY has to truncate in lockstep, or [deloop_quotient_iso] below is
   not merely unproved but FALSE IN ONE DIRECTION: a functor
   [grp_deloop (QuotientGrp N) ⟶ deloop_quotient N] would have to eliminate
   a [Prop] into the [Type]-valued [quot_rel].  Truncating both sides keeps
   the headline -- the quotient category of the delooping IS the delooping
   of the quotient -- at its full [≅[StrictCat]] strength, and at
   [eq_refl] on objects, arrows, identity and composition
   (Test/ProbeGrpCongruence.v).

   [ns_rel], [ns_congruence] and the whole normal-subgroup/congruence
   dictionary below are UNCHANGED: only the category built from them
   truncates, and [ns_prel_is_truncation] records the relationship at
   [eq_refl]. 

   --------
   * 命题同余：[ns_rel] 在 [inhabited] 下。

   早期的修订版本是从 [ns_rel] 本身构建 [deloop_quotient]。自从
   PR “代数载体是集合”（2026-09-17）以来，[QuotientGrp] 自身的
   等式是 [quot_rel] 的命题截断——[sub_mem] 保持
   [Type] 值，因此商对象必须截断——并且商
   范畴必须同步截断，否则下面的 [deloop_quotient_iso]
   不仅无法证明，而且在一个方向上是错误的：函子
   [grp_deloop (QuotientGrp N) ⟶ deloop_quotient N] 必须将 [Prop] 消去到 [Type] 值的 [quot_rel] 中。截断双方保持
   标题——delooping 的商范畴就是商的 delooping——在其完整的
   [≅[StrictCat] 强度下，并且在对象、箭头、恒等和复合上均为 [eq_refl]
   （Test/ProbeGrpCongruence.v）。[ns_rel]、[ns_congruence] 以及下面的整个正规子群/合同字典保持不变：只有从它们构建的类别被截断，[ns_prel_is_truncation] 记录了在 [eq_refl] 的关系。
*)
Definition ns_prel {G : GrpObject} (N : NormalSubgroup G)
  : HomRelT (grp_deloop G) := fun _ _ f g => quot_equiv N f g.

Example ns_prel_is_truncation {G : GrpObject} (N : NormalSubgroup G)
  (f g : carrier G) :
  ns_prel N ttt ttt f g = inhabited (ns_rel N ttt ttt f g) := eq_refl.

(* Built tactically rather than as a term: a bare [match] on [inhabited] is elaborated with a [Type] motive and is refused, even where the branch's result is a [Prop]. / 从战术上构建而不是作为一个术语：在 [inhabited] 上的一个裸 [match] 被用一个 [Type] 动机加以详细说明并被拒绝，即使该分支的结果是一个 [Prop]。 *)
Definition ns_prel_congruence {G : GrpObject} (N : NormalSubgroup G)
  : @HomCongruence (grp_deloop G) (ns_prel N).
Proof.
  unshelve refine (@Build_HomCongruence (grp_deloop G) (ns_prel N) _ _ _ _).
  (*
 [HomRelT] ascribes sort [Type] to each relation, so the goal is
 converted to its [inhabited] form before any elimination. 

 --------
 [HomRelT] 将 [Type] 类型归于每个关系，因此在进行任何消除之前，目标会被转换为其 [inhabited] 形式。
*)
  - intros x y f g H; exact (inhabits (quot_rel_of_equiv N f g H)).
  - intros x y f g H; unfold ns_prel, quot_equiv in *;
      destruct H as [h]; exact (inhabits (quot_rel_sym N f g h)).
  - intros x y f g h H1 H2; unfold ns_prel, quot_equiv in *;
      destruct H1 as [h1], H2 as [h2];
      exact (inhabits (quot_rel_trans N f g h h1 h2)).
  - intros x y z f f' g g' H1 H2; unfold ns_prel, quot_equiv in *;
      destruct H1 as [h1], H2 as [h2];
      exact (inhabits (quot_rel_mul N f f' g g' h1 h2)).
Defined.

(*
   * The quotient category of the delooping.  The congruence witness is
   passed explicitly, since [ns_prel_congruence] is not an instance. 

   --------
   * 悬挂的商范畴。 同余的证明显式传递，因为 [ns_prel_congruence] 不是一个实例。
*)
Definition deloop_quotient {G : GrpObject} (N : NormalSubgroup G) : Category :=
  @Quotient (grp_deloop G) (ns_prel N) (ns_prel_congruence N).

Definition deloop_quotient_proj {G : GrpObject} (N : NormalSubgroup G)
  : grp_deloop G ⟶ deloop_quotient N :=
  @QuotientProj (grp_deloop G) (ns_prel N) (ns_prel_congruence N).

(*
   * ** The orientation of the relation

   Issue #301's text states the condition as “g⁻¹ * f lies in N”; #313's
   [quot_rel], which this file reuses, states it as “f * g⁻¹ lies in N”.
   They agree, and NORMALITY is what makes them agree: each direction
   conjugates the witness, by g⁻¹ one way and by g the other.  For a
   subgroup that is not normal the two are the right- and left-coset
   relations, and they can come apart -- EXHIBITED rather than proved in
   general: [coset_orientations_differ] below separates them at one pair
   over #313's non-normal [S3_refl_sub], and no claim is made that every
   non-normal subgroup separates them. 

   --------
   * ** 关系的方向

   问题 #301 的文本将条件表述为“g⁻¹ * f 位于 N”；#313 的 [quot_rel]（本文件重复使用）则表述为“f * g⁻¹ 位于 N”。它们是一致的，而 NORMALITY（正规性）使其一致：每个方向都以不同方式通过 g⁻¹ 或 g 来共轭见证元素。对于非正规子群，两者则分别是右陪集和左陪集关系，它们可能会分离——通常是通过实例而非证明来展示：下面的 [coset_orientations_differ] 在 #313 的非正规 [S3_refl_sub] 上将它们分开，并未声称每个非正规子群都会将它们分开。
*)

Lemma quot_rel_flip {G : GrpObject} (N : NormalSubgroup G) (a b : carrier G) :
  quot_rel N a b ↔ sub_mem N (grp_mul G (grp_inv G b) a).
Proof.
  split; intro K; unfold quot_rel in *.
  - apply (sub_at N (a := grp_mul G (grp_mul G (grp_inv G b)
                                      (grp_mul G a (grp_inv G b)))
                       (grp_inv G (grp_inv G b)))).
    + rewrite (grp_inv_inv G b).
      rewrite (grp_mul_assoc G (grp_inv G b) (grp_mul G a (grp_inv G b)) b).
      rewrite (grp_mul_assoc G a (grp_inv G b) b).
      rewrite (grp_mul_inv_l G b), (grp_mul_unit_r G a).
      reflexivity.
    + exact (ns_conj N (grp_inv G b) _ K).
  - apply (sub_at N (a := grp_mul G (grp_mul G b
                                      (grp_mul G (grp_inv G b) a))
                       (grp_inv G b))).
    + rewrite <- (grp_mul_assoc G b (grp_inv G b) a).
      rewrite (grp_mul_inv_r G b), (grp_mul_unit_l G a).
      reflexivity.
    + exact (ns_conj N b _ K).
Qed.

(** Issue #301's own formula, as the congruence's relation. / 第301期的公式，作为同余关系。 *)
Corollary ns_rel_flip {G : GrpObject} (N : NormalSubgroup G) (f g : carrier G) :
  ns_rel N ttt ttt f g ↔ sub_mem N (grp_mul G (grp_inv G g) f).
Proof. exact (quot_rel_flip N f g). Qed.

(*
   * ** From a congruence to a normal subgroup: the class of the identity

   The other direction of Mac Lane's exercise.  Every field is a short
   chain of applications of the four congruence fields and their derived
   [cong_refl] -- between one and seven of them, the closure fields for
   inverse (seven) and for conjugation (six) being the long ones --
   against a unit or inverse law of G where a law is needed at all (the
   saturation and unit fields need none).  No property of the relation
   beyond the four it carries is used anywhere. 

   --------
   * ** 从同余到正规子群：单位元的类

   Mac Lane 练习题的另一个方向。 每个域都是对四个同余域及其派生 [cong_refl] 的简短应用链——其中一个至七个应用，逆运算（七个）和共轭（六个）的闭包域是较长的——针对 G 中的单位元或逆律，当在任何地方需要法则时（饱和域和单位元域不需要）。 除了它所携带的四个性质之外，关系的任何性质都未被使用。
*)

Section Converse.

Context {G : GrpObject}.
Context (R : HomRelT (grp_deloop G)).
Context `{HR : @HomCongruence (grp_deloop G) R}.

Definition cong_mem (a : carrier G) : Type :=
  R ttt ttt (deloop_arr a) (@id (grp_deloop G) ttt).

Program Definition cong_sub : Subgroup G := {|
  sub_mem := cong_mem
|}.
Next Obligation.                       (* ≈-saturation / ≈-饱和 *)
  intros a b Hab Ha; unfold cong_mem in *.
  exact (@cong_trans (grp_deloop G) R HR ttt ttt
           (deloop_arr b) (deloop_arr a) id
           (@cong_incl (grp_deloop G) R HR ttt ttt
              (deloop_arr b) (deloop_arr a) (symmetry Hab)) Ha).
Qed.
Next Obligation.                       (* the unit *)
  unfold cong_mem; apply cong_refl.
Qed.
Next Obligation.                       (* closure under product / 关于积的封闭性 *)
  intros a b Ha Hb; unfold cong_mem in *.
  exact (@cong_trans (grp_deloop G) R HR ttt ttt
           (deloop_arr (grp_mul G a b)) (id ∘ id) id
           (@cong_comp (grp_deloop G) R HR ttt ttt ttt
              (deloop_arr a) id (deloop_arr b) id Ha Hb)
           (@cong_incl (grp_deloop G) R HR ttt ttt (id ∘ id) id (id_left id))).
Qed.
Next Obligation.                       (* closure under inverse / 逆运算封闭性 *)
  intros a Ha; unfold cong_mem in *.
  apply cong_sym.
  refine (@cong_trans (grp_deloop G) R HR ttt ttt id
            (deloop_arr (grp_inv G a) ∘ deloop_arr a) _ _ _).
  - exact (@cong_incl (grp_deloop G) R HR ttt ttt id
             (deloop_arr (grp_inv G a) ∘ deloop_arr a)
             (symmetry (grp_mul_inv_l G a))).
  - refine (@cong_trans (grp_deloop G) R HR ttt ttt _
              (deloop_arr (grp_inv G a) ∘ id) _ _ _).
    + exact (@cong_comp (grp_deloop G) R HR ttt ttt ttt
               (deloop_arr (grp_inv G a)) (deloop_arr (grp_inv G a))
               (deloop_arr a) id (cong_refl _) Ha).
    + exact (@cong_incl (grp_deloop G) R HR ttt ttt
               (deloop_arr (grp_inv G a) ∘ id) (deloop_arr (grp_inv G a))
               (id_right _)).
Qed.

(*
   * Normality is the fifth field, and it is where the congruence's
   two-sided compatibility with composition is spent: t on the left and
   t⁻¹ on the right. 

   --------
   * 正常性是第五个领域，它是同余与组合的双边兼容性得以体现的地方：在左侧是 t，在右侧是 t⁻¹。
*)
Program Definition cong_ns : NormalSubgroup G := {|
  ns_sub := cong_sub
|}.
Next Obligation.
  intros t a Ha; simpl in *; unfold cong_mem in *.
  refine (@cong_trans (grp_deloop G) R HR ttt ttt _
            ((deloop_arr t ∘ id) ∘ deloop_arr (grp_inv G t)) id _ _).
  - exact (@cong_comp (grp_deloop G) R HR ttt ttt ttt
             (deloop_arr t ∘ deloop_arr a) (deloop_arr t ∘ id)
             (deloop_arr (grp_inv G t)) (deloop_arr (grp_inv G t))
             (@cong_comp (grp_deloop G) R HR ttt ttt ttt
                (deloop_arr t) (deloop_arr t) (deloop_arr a) id
                (cong_refl _) Ha)
             (cong_refl _)).
  - apply cong_incl.
    rewrite id_right.
    exact (grp_mul_inv_r G t).
Qed.

End Converse.

(*
   * Membership in the recovered subgroup IS relatedness to the identity,
   by convertibility. 

   --------
   * 恢复子群的成员资格与身份相关，通过可转换性。
*)
Example cong_mem_is_class_of_id {G : GrpObject} (R : HomRelT (grp_deloop G))
  `{HR : @HomCongruence (grp_deloop G) R} (a : carrier G) :
  sub_mem (@cong_ns G R HR) a = R ttt ttt (deloop_arr a) (@id (grp_deloop G) ttt)
  := eq_refl.

(* * ** The two maps are mutually inverse / * ** 这两个映射是互逆的 *)

(*
   * Normal subgroup, to congruence, and back: [quot_rel_unit_iff] is the
   whole proof, applied.  #313 stated it exactly because the projection's
   kernel had to be pinned down; here it is the round trip. 

   --------
   * 正规子群，关于合同关系，以及返回：[quot_rel_unit_iff] 是整个证明的应用。#313 精确地陈述了它，因为投影的核必须确定；这里就是完整的往返。
*)
Lemma ns_of_cong_of_ns {G : GrpObject} (N : NormalSubgroup G) (a : carrier G) :
  sub_mem (@cong_ns G (ns_rel N) (ns_congruence N)) a ↔ sub_mem N a.
Proof. exact (quot_rel_unit_iff N a). Qed.

(*
   * Congruence, to normal subgroup, and back: f ~ g precisely when
   f * g⁻¹ ~ e, since one can multiply through by g and by g⁻¹.  The
   backward direction is one application of compatibility with
   composition followed by one of containment of `≈`; the forward one
   needs a second containment step, to rewrite f as (f * g⁻¹) ∘ g before
   the composition field can be applied. 

   --------
   * 同余、到正规子群、再回到同余：当且仅当 f ~ g 时，有 f * g⁻¹ ~ e，因为可以通过 g 和 g⁻¹ 进行相乘。反向步骤是先应用一次与复合的相容性，然后再应用一次 `≈` 的包含关系；正向步骤则需要第二次包含步骤，将 f 重写为 (f * g⁻¹) ∘ g，然后才能应用复合域。
*)
Lemma cong_of_ns_of_cong {G : GrpObject} (R : HomRelT (grp_deloop G))
  `{HR : @HomCongruence (grp_deloop G) R}
  (x y : grp_deloop G) (f g : carrier G) :
  ns_rel (@cong_ns G R HR) x y f g ↔ R x y f g.
Proof.
  destruct x, y; split; intro K.
  - refine (@cong_trans (grp_deloop G) R HR ttt ttt (deloop_arr f)
              (deloop_arr (grp_mul G f (grp_inv G g)) ∘ deloop_arr g)
              (deloop_arr g) _ _).
    + apply cong_incl; simpl.
      rewrite (grp_mul_assoc G f (grp_inv G g) g),
              (grp_mul_inv_l G g), (grp_mul_unit_r G f).
      reflexivity.
    + refine (@cong_trans (grp_deloop G) R HR ttt ttt _
                (id ∘ deloop_arr g) _ _ _).
      * exact (@cong_comp (grp_deloop G) R HR ttt ttt ttt
                 (deloop_arr (grp_mul G f (grp_inv G g))) id
                 (deloop_arr g) (deloop_arr g) K (cong_refl _)).
      * apply cong_incl; apply id_left.
  - refine (@cong_trans (grp_deloop G) R HR ttt ttt _
              (deloop_arr g ∘ deloop_arr (grp_inv G g)) id _ _).
    + exact (@cong_comp (grp_deloop G) R HR ttt ttt ttt
               (deloop_arr f) (deloop_arr g)
               (deloop_arr (grp_inv G g)) (deloop_arr (grp_inv G g))
               K (cong_refl _)).
    + apply cong_incl; exact (grp_mul_inv_r G g).
Qed.

(*
   * ** The correspondence, packaged as a bijection of setoids

   Neither round trip is an equality of records, and neither could be
   without function extensionality together with extensionality for
   [Type]-valued families ([sub_mem] and [HomRelT] both land in [Type],
   so propositional extensionality would not reach them): a normal
   subgroup
   is a predicate carrying five proofs (four [Subgroup] closure laws and
   [ns_conj]), a congruence a relation carrying four.  The honest
   packaging is therefore a setoid isomorphism, with coextensiveness on
   the left and pointwise mutual implication on the right -- the same
   shape [Construction/Deloop/Transform.v]'s [transform_conjugator_iso]
   takes for its own correspondence, where witnesses are likewise
   compared by what they name rather than as records.  That both sides
   are objects of [Sets] is asserted by [ns_cong_iso]'s type and checked
   by the elaborator; no universe annotation was needed anywhere in this
   section.

   That the membership round trip is NOT definitional is measured, not
   inferred: Test/ProbeGrpCongruence.v, negative 2, with the positive
   control showing what it IS convertible to. 

   --------
   * ** 这种对应关系，被封装为一组同类集合之间的双射两次往返都不是记录的相等，并且在没有函数外延性以及 [Type] 值族的外延性的情况下，两者都无法实现（[sub_mem] 和 [HomRelT] 都落入 [Type]，所以命题外延性无法达到它们）：正规子群是一个包含五个证明的谓词（四个 [Subgroup] 闭合律和 [ns_conj]），而合同是一个包含四个证明的关系。因此，诚实的封装是一个集合等价同构，在左侧是共扩展的，在右侧是逐点相互蕴含的——[Construction/Deloop/Transform.v] 的 [transform_conjugator_iso] 对其自身对应也采取相同的形式，其中证据同样是通过其命名来比较，而不是作为记录。双方都是 [Sets] 的对象，这一点由 [ns_cong_iso] 的类型断言并由展开器检查；在本节的任何地方都不需要宇宙注解。

   成员归属的往返不是定义性的，这是通过测量而不是推断得出的：Test/ProbeGrpCongruence.v，负例 2，正例控制显示它可以转换成的内容。
*)

Section Packaging.

Context {G : GrpObject}.

(** A congruence, as data: the relation together with its four laws. / 一个同余，作为数据：关系及其四条定律。 *)
Definition CongData : Type :=
  { R : HomRelT (grp_deloop G) & HomCongruence R }.

Program Definition NS_Setoid : SetoidObject := {|
  carrier := NormalSubgroup G;
  is_setoid := {| equiv := fun N M =>
    (∀ a : carrier G, sub_mem N a → sub_mem M a)
      * (∀ a : carrier G, sub_mem M a → sub_mem N a) |}
|}.
Next Obligation.
  constructor.
  - intro N; split; intros a Ha; exact Ha.
  - intros N M [H1 H2]; split; assumption.
  - intros N M P [H1 H2] [H3 H4]; split; intros a Ha; auto.
Qed.

Program Definition Cong_Setoid : SetoidObject := {|
  carrier := CongData;
  is_setoid := {| equiv := fun R S =>
    ∀ (x y : grp_deloop G) (f g : x ~> y),
      (`1 R x y f g → `1 S x y f g) * (`1 S x y f g → `1 R x y f g) |}
|}.
Next Obligation.
  constructor.
  - intros R x y f g; split; intro K; exact K.
  - intros R S H x y f g; destruct (H x y f g); split; assumption.
  - intros R S T H1 H2 x y f g.
    destruct (H1 x y f g), (H2 x y f g); split; auto.
Qed.

Program Definition ns_to_cong : NS_Setoid ~{Sets}~> Cong_Setoid := {|
  morphism := fun N => existT _ (ns_rel N) (ns_congruence N)
|}.
Next Obligation.
  intros N M [H1 H2] x y f g; simpl; split; intro K.
  - exact (H1 _ K).
  - exact (H2 _ K).
Qed.

Program Definition cong_to_ns : Cong_Setoid ~{Sets}~> NS_Setoid := {|
  morphism := fun R => @cong_ns G (`1 R) (`2 R)
|}.
Next Obligation.
  intros R S H; simpl; split; intros a Ha.
  - exact (fst (H ttt ttt a (@id (grp_deloop G) ttt)) Ha).
  - exact (snd (H ttt ttt a (@id (grp_deloop G) ttt)) Ha).
Qed.

(*
   * Mac Lane §II.8 Exercise 2, as a bijection: the normal subgroups of G
   are the congruences on its delooping. 

   --------
   * Mac Lane §II.8 练习 2，作为一个双射：G 的正规子群是其去循环上的同余关系。
*)
Program Definition ns_cong_iso : NS_Setoid ≅[Sets] Cong_Setoid := {|
  to := ns_to_cong;
  from := cong_to_ns
|}.
Next Obligation.
  intros R x y f g; simpl.
  destruct x, y.
  exact (@cong_of_ns_of_cong G (`1 R) (`2 R) ttt ttt f g).
Qed.
Next Obligation.
  intros N; simpl; split; intros a Ha.
  - exact (fst (ns_of_cong_of_ns N a) Ha).
  - exact (snd (ns_of_cong_of_ns N a) Ha).
Qed.

End Packaging.

(*
   * The name issue #301's Verification block asks for, supplied as an
   alias so that block resolves.  (Its module path does not: the issue
   suggests [Instance/Group/Congruence.v], and the tree has no
   [Instance/Group/] directory -- [Grp] is the category's name and #313's
   file is [Instance/Grp/Quotient.v], so this file is
   [Instance/Grp/Congruence.v].) 

   --------
   * 名称问题 #301 的验证块要求提供，以别名形式提供，以便该块可以解决。（它的模块路径则不需要：问题中建议了 [Instance/Group/Congruence.v]，而目录树中没有 [Instance/Group/] 目录——[Grp] 是该类别的名称，#313 的文件是 [Instance/Grp/Quotient.v]，所以这个文件是 [Instance/Grp/Congruence.v]。）
*)
Definition congruence_normal_subgroup (G : GrpObject)
  : @NS_Setoid G ≅[Sets] @Cong_Setoid G := @ns_cong_iso G.

(*
   * ** Normality is necessary, not merely sufficient

   #313 has seven [quot_rel] lemmas, and TWO of them apply [ns_conj]:
   [quot_rel_mul] and [quot_rel_inv], as that file's own
   comments say (the comment on [quot_rel_mul] calls it “the first of the
   two places where NORMALITY is spent”).  Only the first is consumed by
   [ns_congruence] -- [HomCongruence] has no field about inverses -- and
   the other three fields draw on [quot_rel_of_equiv], [quot_rel_sym] and
   [quot_rel_trans], whose proofs apply [sub_at], [sub_unit],
   [sub_inv] and [sub_mul], and never [ns_conj].  So among the four [HomCongruence] fields it is the
   COMPOSITION field, and only that one, for which normality is at stake.
   That is read off those proofs and offered as a remark rather than as
   an in-tree theorem, since all seven are STATED over a
   [NormalSubgroup] and this file does not restate them.

   What IS proved is the converse, and it is what makes the
   correspondence a correspondence rather than “normal subgroups give
   congruences and we did not look at the others”: a subgroup whose
   relation is a congruence is normal.  It is obtained by feeding that
   relation to [cong_ns] and reading its fifth field back, so no second
   normality argument is written. 

   --------
   * ** 正态性是必要的，而不仅仅是充分的#313 有七个 [quot_rel] 引理，其中两个适用于 [ns_conj]：[quot_rel_mul] 和 [quot_rel_inv]，正如该文件自己的注释所说（对 [quot_rel_mul] 的注释称其为“正常性消耗的两个地方中的第一个”）。只有第一个被 [ns_congruence] 消耗——[HomCongruence] 没有关于逆元的字段——而另外三个字段依赖于 [quot_rel_of_equiv]、[quot_rel_sym] 和 [quot_rel_trans]，它们的证明适用于 [sub_at]、[sub_unit]、[sub_inv] 和 [sub_mul]，并且从不适用 [ns_conj]。因此在四个 [HomCongruence] 字段中，只有组合（COMPOSITION）字段与正常性相关。这一点可以从那些证明中读出，并作为一个备注提出，而不是作为树内定理，因为所有七个都是在 [NormalSubgroup] 上陈述的，而该文件并未重新陈述它们。已被证明的是其逆命题，这正是使得该对应关系成为对应关系而不是“正规子群给出同余关系，而我们没有考虑其他情况”的原因：一个其关系为同余关系的子群是正规子群。它是通过将该关系输入 [cong_ns] 并读取其第五字段得到的，因此没有书写第二个正规性论证。
*)

Section Necessity.

Context {G : GrpObject}.
Context (S : Subgroup G).

Definition sub_rel : HomRelT (grp_deloop G) := fun _ _ f g => quot_rel S f g.

(*
   * #313's [quot_rel_unit_iff] is stated over a [NormalSubgroup], though
   its proof consumes only [sub_at], [grp_inv_unit] and [grp_mul_unit_r]
   -- one [Subgroup] field and two group lemmas, none of them [ns_conj].
   Rather than weaken that file's statement, the subgroup-level form is
   stated here, with the same three steps; the normal case is #313's and
   is not re-derived. 

   --------
   * #313 的 [quot_rel_unit_iff] 是在 [NormalSubgroup] 上陈述的，尽管它的证明只使用了 [sub_at]、[grp_inv_unit] 和 [grp_mul_unit_r] —— 一个 [Subgroup] 域和两个群引理，它们都不是 [ns_conj]。为了不削弱该文件的陈述，这里给出子群层次的形式，包含相同的三个步骤；正规情形是 #313 的，并未重新推导。
*)
Lemma sub_rel_unit_iff (a : carrier G) :
  quot_rel S a (grp_unit G) ↔ sub_mem S a.
Proof.
  split; intro K; unfold quot_rel in *.
  - apply (sub_at S (a := grp_mul G a (grp_inv G (grp_unit G)))); [| exact K ].
    rewrite (grp_inv_unit G); apply (grp_mul_unit_r G).
  - apply (sub_at S (a := a)); [| exact K ].
    rewrite (grp_inv_unit G); symmetry; apply (grp_mul_unit_r G).
Qed.

Lemma sub_rel_congruence_normal `{HR : @HomCongruence (grp_deloop G) sub_rel} :
  ∀ t a : carrier G, sub_mem S a →
    sub_mem S (grp_mul G (grp_mul G t a) (grp_inv G t)).
Proof.
  intros t a Ha.
  apply (fst (sub_rel_unit_iff _)).
  exact (@ns_conj G (@cong_ns G sub_rel HR) t a
           (snd (sub_rel_unit_iff a) Ha)).
Qed.

End Necessity.

(*
   * Mac Lane §II.8 Exercise 2 in the sharp form: for a subgroup, being a
   congruence and being normal are the same condition.  `↔` is Lib's
   Type-valued [iffT], so the FORWARD leg is congruence ⟹ normality and
   is [sub_rel_congruence_normal]; the BACKWARD leg is normality ⟹
   congruence and is [ns_congruence] read at the normal subgroup built
   from S.  (Consumers project with [fst] for the forward leg --
   [S3_refl_sub_no_congruence] below does.) 

   --------
   * Mac Lane §II.8 锐形式的练习 2：对于一个子群，作为合同和作为正规是相同的条件。`↔` 是 Lib 的类型值 [iffT]，因此正向部分是合同 ⟹ 正规，并且是 [sub_rel_congruence_normal]；反向部分是正规 ⟹ 合同，并且是从 S 构建的正规子群中读取的 [ns_congruence]。（消费者项目的正向部分使用 [fst]——下面的 [S3_refl_sub_no_congruence] 也使用。）
*)
Theorem congruence_iff_normal {G : GrpObject} (S : Subgroup G) :
  (@HomCongruence (grp_deloop G) (sub_rel S))
    ↔ (∀ t a : carrier G, sub_mem S a →
         sub_mem S (grp_mul G (grp_mul G t a) (grp_inv G t))).
Proof.
  split.
  - intro HR; exact (@sub_rel_congruence_normal G S HR).
  - intro Hn.
    exact (ns_congruence (@Build_NormalSubgroup G S Hn)).
Qed.

(*
   * ** The corollary: quotient of the delooping = delooping of the quotient

   Mac Lane's exercise closes by identifying the quotient category with
   the delooping of the factor group.  Both categories have one object,
   the elements of G as arrows, G's unit as identity and G's
   multiplication as composition -- and those FOUR fields ([obj], [hom],
   [id], [compose]) are the ones that are convertible.  (Counted among
   the TEN a [Category] record literal supplies; the class's [uhom],
   [dom] and [cod] are [:=] definitions derived from those, not data
   either construction chooses.)  The other SIX are built twice:
   [homset] (whose two [Equivalence] witnesses are
   [Quotient_equivalence] and [QuotientGrp]'s own obligation, both
   [Qed]), and with it [compose_respects], [id_left], [id_right],
   [comp_assoc] and [comp_assoc_sym], which [Quotient] assembles from
   [cong_comp]/[cong_incl] and [Deloop] from the monoid's own law fields.
   So the categories are NOT Leibniz-equal -- measured, not assumed
   (Test/ProbeGrpCongruence.v, negative 3).

   THE STRENGTH IS [StrictCat], and that is the strong reading.
   [Instance/Cat.v] gives [Cat] the hom-setoid [Functor_Setoid], which
   identifies naturally isomorphic functors, so [≅[Cat]] in this library
   is an EQUIVALENCE of categories and says strictly less; the [Cat]
   reading below is DERIVED and labelled. 

   --------
   * ** 推论：去环的商 = 商的去环Mac Lane 的练习最后通过将商范畴与因子群的去环化联系起来进行总结。两个范畴都有一个对象，G 的元素作为箭头，G 的单位作为恒等，G 的乘法作为复合——而这四个域（[obj]、[hom]、[id]、[compose]）是可以互换的。（在十个 [Category] 记录字面供应中被计算在内；该类的 [uhom]、[dom] 和 [cod] 是从这些定义派生的 [:=] 定义，而不是任一构造选择的数据。）另外六个是构建两次的：[homset]（其两个 [Equivalence] 见证者分别是 [Quotient_equivalence] 和 [QuotientGrp] 自身的义务，都是 [Qed]），以及与之相关的 [compose_respects]、[id_left]、[id_right]、[comp_assoc] 和 [comp_assoc_sym]，[Quotient] 从 [cong_comp] / [cong_incl] 和单子自身法则字段中的 [Deloop] 组装而成。因此这些类别不是莱布尼茨等效的——是测量得到的，而非假设的（Test/ProbeGrpCongruence.v，负3）。强度是 [StrictCat]，这是强读法。
   [Instance/Cat.v] 给 [Cat] 提供了同构集 [Functor_Setoid]，它自然地识别同构函子，所以这个库中的 [≅[Cat] 是范畴的等价，并且说明得更少；下面的 [Cat] 读法是派生的并有标注。
*)

Section Corollary.

Context {G : GrpObject}.
Context (N : NormalSubgroup G).

Definition quot_to_deloop : deloop_quotient N ⟶ grp_deloop (QuotientGrp N) :=
  Build_Functor (deloop_quotient N) (grp_deloop (QuotientGrp N))
    (fun x => x)
    (fun x y f => f)
    (fun x y f g H => H)
    (fun x => inhabits (quot_rel_refl N _))
    (fun x y z f g => inhabits (quot_rel_refl N _)).

Definition deloop_to_quot : grp_deloop (QuotientGrp N) ⟶ deloop_quotient N :=
  Build_Functor (grp_deloop (QuotientGrp N)) (deloop_quotient N)
    (fun x => x)
    (fun x y f => f)
    (fun x y f g H => H)
    (fun x => inhabits (quot_rel_refl N _))
    (fun x y z f g => inhabits (quot_rel_refl N _)).

(*
   * Both functors are the identity on objects and on arrows, so both round
   trips have [eq_refl] object components. 

   --------
   * 两个函子在对象和箭头上都是恒等的，所以两次往返都有 [eq_refl] 对象分量。
*)
Lemma deloop_quotient_round_to :
  @equiv _ (@Functor_StrictEq_Setoid (deloop_quotient N) (deloop_quotient N))
    (deloop_to_quot ◯ quot_to_deloop) (Id[deloop_quotient N]).
Proof.
  exists (fun _ => eq_refl); intros x y f; simpl;
    constructor; apply quot_rel_refl.
Qed.

Lemma deloop_quotient_round_from :
  @equiv _ (@Functor_StrictEq_Setoid (grp_deloop (QuotientGrp N))
              (grp_deloop (QuotientGrp N)))
    (quot_to_deloop ◯ deloop_to_quot) (Id[grp_deloop (QuotientGrp N)]).
Proof.
  exists (fun _ => eq_refl); intros x y f; simpl;
    constructor; apply quot_rel_refl.
Qed.

Definition deloop_quotient_iso
  : deloop_quotient N ≅[StrictCat] grp_deloop (QuotientGrp N) :=
  @Build_Isomorphism StrictCat (deloop_quotient N) (grp_deloop (QuotientGrp N))
    quot_to_deloop deloop_to_quot
    deloop_quotient_round_from deloop_quotient_round_to.

(*
   * The weaker [Cat] reading, derived.  [≅[Cat]] IS equivalence of
   categories here; the [StrictCat] statement above is the strong one. 

   --------
   * 较弱的 [Cat] 阅读，衍生的。[≅[Cat] ] 在这里是范畴的等价；上面的 [StrictCat] 陈述是强的那个。
*)
Definition deloop_quotient_Cat_iso
  : deloop_quotient N ≅[Cat] grp_deloop (QuotientGrp N) :=
  @Build_Isomorphism Cat (deloop_quotient N) (grp_deloop (QuotientGrp N))
    quot_to_deloop deloop_to_quot
    (strict_equiv_implies_fun_equiv _ _ deloop_quotient_round_from)
    (strict_equiv_implies_fun_equiv _ _ deloop_quotient_round_to).

End Corollary.

(* * ** Group homomorphisms as functors between deloopings / * ** 将群同态视为延拓之间的函子 *)

Section Homomorphisms.

Context {G K : GrpObject}.

(*
   * A group homomorphism is a monoid homomorphism of the delooped
   monoids: unit and product preservation are its two fields, and
   respectfulness is the underlying setoid morphism's. 

   --------
   * 群同态是退化单元的幺半群同态：单位和乘积保持是它的两个字段，而尊重性是基础集合等价关系的态射。
*)
Definition hom_MonHom (h : G ~{Grp}~> K)
  : MonHom (grp_deloop_monoid G) (grp_deloop_monoid K) :=
  @Build_MonHom (grp_deloop_monoid G) (grp_deloop_monoid K)
    (grp_map h) (proper_morphism (grp_map h))
    (grp_map_unit h) (grp_map_mul h).

(*
   * ...hence a functor, by [Construction/Deloop/Transform.v]'s
   [Deloop_map]; nothing here is new, and the action on arrows is the
   homomorphism's action on elements by convertibility. 

   --------
   * …因此一个函子，由 [Construction/Deloop/Transform.v] 的 [Deloop_map]；这里没有新的内容，箭的作用就是同态在元素上的作用，通过可转换性。
*)
Definition deloop_hom (h : G ~{Grp}~> K) : grp_deloop G ⟶ grp_deloop K :=
  Deloop_map (hom_MonHom h).

Example deloop_hom_fmap (h : G ~{Grp}~> K) (a : carrier G) :
  @fmap _ _ (deloop_hom h) ttt ttt a = grp_map h a := eq_refl.

End Homomorphisms.

(*
   * ** Awodey §4.2's kernel clause, given its categorical provenance

   #313's [KernelNS] proves directly that the kernel of a group
   homomorphism is a normal subgroup, discharging five obligations; the
   QA correction on #301 homes that clause there and asks for a citation
   here, which this is.  What is added is the REASON, which is
   categorical and costs no group-level obligation at all: the kernel
   congruence of a FUNCTOR is a congruence ([FunctorKernel_Congruence],
   Construction/Quotient.v), and [cong_ns] turns any congruence on
   the delooping into a normal subgroup.  Composing the two gives the
   kernel of h as a normal subgroup with no FURTHER argument about
   conjugation: [cong_ns]'s fifth obligation is that argument, made once
   and generically, and nothing kernel-specific is added to it.

   The two normal subgroups are coextensive, not identical: the
   categorical one collects the a with h a ≈ h e, #313's the a with
   h a ≈ e, and [grp_map_unit] is the one step between them (measured:
   Test/ProbeGrpCongruence.v, negative 5). 

   --------
   * ** Awodey §4.2 的核心条款，鉴于其范畴来源

   #313 的 [KernelNS] 直接证明了群同态的核是一个正规子群，完成了五个义务；#301 的 QA 修改在此处确认了该条款，并要求在此处提供引用，这就是引用。新增的是理由，它是范畴性的，对群级别的义务没有任何额外要求：函子（FUNCTOR）的核同余是一个同余（[FunctorKernel_Congruence]，Construction/Quotient.v），而 [cong_ns] 将任何延拓上的同余转化为正规子群。将两者组合得到 h 的核作为一个正规子群，无需对共轭进行进一步论证：[cong_ns] 的第五个义务就是这个论证，一次性通用完成，没有对核做额外特定的补充。这两个正规子群是共同延伸的，而不是相同的：范畴的那个收集了满足 h a ≈ h e 的 a，#313 的那个收集了满足 h a ≈ e 的 a，而 [grp_map_unit] 是它们之间的一步（测量：Test/ProbeGrpCongruence.v，负 5）。
*)

Section Kernel.

Context {G K : GrpObject}.
Context (h : G ~{Grp}~> K).

Definition kernel_cong : HomRelT (grp_deloop G) := FunctorKernel (deloop_hom h).

Definition kernel_ns : NormalSubgroup G :=
  @cong_ns G kernel_cong (FunctorKernel_Congruence (deloop_hom h)).

Lemma kernel_ns_iff (a : carrier G) :
  sub_mem kernel_ns a ↔ sub_mem (KernelNS h) a.
Proof.
  simpl; unfold cong_mem, kernel_cong, FunctorKernel; simpl.
  split; intro K'.
  - rewrite K'; apply (grp_map_unit h).
  - rewrite K'; symmetry; apply (grp_map_unit h).
Qed.

(** Hence the two quotients agree, through #313's own comparison. / 因此，通过#313自身的比较，这两个商是一致的。 *)
Definition kernel_quot_congr
  : QuotientGrp kernel_ns ≅[Grp] QuotientGrp (KernelNS h) :=
  quot_congr kernel_ns (KernelNS h)
    (fun a => fst (kernel_ns_iff a)) (fun a => snd (kernel_ns_iff a)).

(*
   * ...and the congruence of #313's kernel relates exactly the arrows the
   functor merges: the kernel congruence of [deloop_hom h] and the
   congruence of [KernelNS h] are the same relation up to logical
   equivalence. 

   --------
   * …且 #313 的核的同余关系正好与函子合并的箭头相关：[deloop_hom h] 的核同余关系和 [KernelNS h] 的同余关系在逻辑等价下是相同的关系。
*)
Lemma kernel_cong_iff (f g : carrier G) :
  ns_rel (KernelNS h) ttt ttt f g ↔ kernel_cong ttt ttt f g.
Proof.
  unfold kernel_cong, FunctorKernel, ns_rel, quot_rel; simpl.
  split; intro K'.
  - apply (grp_cancel_r K (grp_inv K (grp_map h g))).
    rewrite (grp_mul_inv_r K (grp_map h g)).
    rewrite <- (grp_map_inv h g).
    rewrite <- (grp_map_mul h).
    exact K'.
  - rewrite (grp_map_mul h), (grp_map_inv h), K'.
    apply (grp_mul_inv_r K).
Qed.

End Kernel.

(*
   * ** Awodey §4.5 Exercise 1: the group theorem, specialized from the category one

   [Construction/Quotient.v]'s [QuotientLift] is the categorical
   homomorphism theorem: a functor out of C that merges R-related arrows
   lifts through C/R, the triangle holding at [StrictCat] strength
   ([QuotientLift_factors_strict]) and the lift being unique
   ([QuotientLift_unique]).  Instantiated at the delooping with
   R = [ns_rel N] it produces #313's mediator and #313's uniqueness.  The
   only proof ABOUT N it consumes is [kills_descends] -- the computation
   that a homomorphism killing N cannot tell N-congruent elements apart;
   the rest is the dictionary of [hom_MonHom]/[Deloop_map] and
   [Build_GrpHom']'s [grp_map_unit_from_mul]. 

   --------
   * ** Awodey §4.5 练习 1: 群定理，从范畴定理特化而来

   [Construction/Quotient.v] 的 [QuotientLift] 是范畴同态定理：从 C 出发的函子将 R 相关箭头合并，可以通过 C/R 提升，三角形在 [StrictCat] 强度下成立 ([QuotientLift_factors_strict])，且提升是唯一的 ([QuotientLift_unique])。在以 R = [ns_rel N] 进行去环化时实例化，它产生 #313 的中介元和 #313 的唯一性。它使用的关于 N 的唯一证明是 [kills_descends] ——一个同态消去 N 时无法区分 N 同余元素的计算；其余的是 [hom_MonHom] / [Deloop_map] 的字典以及 [Build_GrpHom'] 的 [grp_map_unit_from_mul]。
*)

Section Specialization.

Context {G K : GrpObject}.
Context (N : NormalSubgroup G).
Context (p : Kills N K).

(*
   * The hypothesis of the categorical theorem, discharged by #313's
   descent lemma with no reshaping.  It is stated over the UNTRUNCATED
   [ns_rel], which is what #313's descent lemma proves. 

   --------
   * 范畴定理的假设，由 #313 的下降引理在没有重塑的情况下解除。它是在未截断的 [ns_rel] 上陈述的，这正是 #313 的下降引理所证明的内容。
*)
Definition deloop_kills
  : ∀ x y (f g : x ~{grp_deloop G}~> y), ns_rel N x y f g →
      fmap[deloop_hom (`1 p)] f ≈ fmap[deloop_hom (`1 p)] g :=
  fun x y f g H => kills_descends N p f g H.

(*
   * ...and the same over the truncated relation [deloop_quotient] is built
   from since the PR “algebraic carriers are sets” (2026-09-17).  The
   conclusion is an `≈` at [grp_deloop K], i.e. at [K]'s own carrier, so
   the elimination goes through [K]'s [grp_prop] and nothing is assumed. 

   --------
   * ...并且在截断关系 [deloop_quotient] 上同样构建，
   自从 PR “代数载体是集合”（2026-09-17）以来。
   结论是在 [grp_deloop K] 上的 `≈`，也就是在 [K] 自身的载体上，因此
   消去通过 [K] 的 [grp_prop] 进行，而且没有假设。
*)
Definition deloop_pkills
  : ∀ x y (f g : x ~{grp_deloop G}~> y), ns_prel N x y f g →
      fmap[deloop_hom (`1 p)] f ≈ fmap[deloop_hom (`1 p)] g.
Proof.
  intros x y f g H.
  apply (@pequiv_to _ _ (grp_prop K)).
  unfold ns_prel, quot_equiv in H; destruct H as [h].
  apply (@pequiv_from _ _ (grp_prop K)).
  exact (deloop_kills x y f g h).
Defined.

Definition cat_lift : deloop_quotient N ⟶ grp_deloop K :=
  @QuotientLift (grp_deloop G) (ns_prel N) (ns_prel_congruence N)
    (grp_deloop K) (deloop_hom (`1 p)) deloop_pkills.

(*
   * The lift, read back as a homomorphism out of the factor group.  The
   functor is transported along [deloop_to_quot] -- the [StrictCat]
   isomorphism's own leg -- and then read at the single hom-set;
   [Build_GrpHom'] derives unit preservation, and multiplication
   preservation IS [fmap_comp]. 

   --------
   * 这个提升，可以理解为从因子群中读回的一个同态。函子沿着  [deloop_to_quot]  被传递——[StrictCat] 是同构自身的一条边——然后在单个 Hom-集合上读出；[Build_GrpHom'] 推导出单位保持性，而乘法保持性就是 [fmap_comp]。
*)
Definition cat_med : QuotientGrp N ~{Grp}~> K :=
  @Build_GrpHom' (QuotientGrp N) K
    {| morphism := fun a =>
         @fmap _ _ (cat_lift ◯ deloop_to_quot N) ttt ttt a
     ; proper_morphism :=
         @fmap_respects _ _ (cat_lift ◯ deloop_to_quot N) ttt ttt |}
    (fun a b => @fmap_comp _ _ (cat_lift ◯ deloop_to_quot N) ttt ttt ttt a b).

(*
   * The categorical route lands on #313's mediator: the underlying maps
   are the same term.  The comparison is with [quot_med], which is a
   transparent [Program Definition]; comparing with
   [hom_theorem_factor]'s witness instead would not reduce, that routing
   through the [Qed]-opaque [hom_theorem].  The two [GrpHom] RECORDS are
   not convertible -- their law fields are separately built -- and that
   is pinned as Test/ProbeGrpCongruence.v, negative 4. 

   --------
   * 范畴路线落在 #313 的中介上：底层映射是相同的项。比较的是 [quot_med]，它是一个透明的 [Program Definition]；与 [hom_theorem_factor] 的见证相比，不会简化，通过 [Qed] - 不透明的 [hom_theorem] 路由。两个 [GrpHom] 记录不可转换——它们的法律字段是独立构建的——并且在 Test/ProbeGrpCongruence.v 中固定，结果为负 4。
*)
Example cat_med_is_quot_med (a : carrier (QuotientGrp N)) :
  grp_map cat_med a = grp_map (quot_med N p) a := eq_refl.

(*
   * Awodey §4.5 Exercise 1.  The existence half is [QuotientLift]; the
   uniqueness half is [QuotientLift_unique], applied at the delooping's
   single object.  No group-level uniqueness argument is written. 

   --------
   * Awodey §4.5 练习 1。存在性部分是 [QuotientLift]；唯一性部分是 [QuotientLift_unique]，应用于去卷积的单个对象。没有写出群级别的唯一性论证。
*)
Definition hom_theorem_via_quotient_category
  : ∃! u : QuotientGrp N ~{Grp}~> K, u ∘ quot_proj N ≈ `1 p.
Proof.
  unshelve refine {| unique_obj := cat_med |}.
  - intro a; simpl; reflexivity.
  - intros v Hv a.
    exact (symmetry
             (@QuotientLift_unique (grp_deloop G) (ns_prel N)
                (ns_prel_congruence N)
                (grp_deloop K) (deloop_hom (`1 p)) deloop_pkills
                (deloop_hom v ◯ quot_to_deloop N)
                (fun _ => eq_refl)
                (fun x y f => Hv f)
                ttt ttt a)).
Defined.

Example hom_theorem_via_quotient_category_obj (a : carrier (QuotientGrp N)) :
  grp_map (unique_obj hom_theorem_via_quotient_category) a
    = grp_map (quot_med N p) a := eq_refl.

End Specialization.

(*
   * The same statement in [hom_theorem]'s own shape, taking the killing
   hypothesis rather than the packaged [Kills].  #313's biconditional is
   NOT re-proved: only its forward direction is re-obtained, by the
   categorical route. 

   --------
   * 在 [hom_theorem] 自身的形式中做同样的陈述，采用杀死假设而不是打包的 [Kills]。#313 的双条件没有被重新证明：只通过范畴途径重新获得了它的正向方向。
*)
Definition hom_theorem_from_category {G K : GrpObject} (N : NormalSubgroup G)
  (h : G ~{Grp}~> K)
  (Hkill : ∀ a : carrier G, sub_mem N a → grp_map h a ≈ grp_unit K) :
  ∃! u : QuotientGrp N ~{Grp}~> K, u ∘ quot_proj N ≈ h :=
  hom_theorem_via_quotient_category N (existT _ h Hkill).

(*
   * ** The projection functor is the delooped projection

   [QuotientProj] and #313's [quot_proj] are the same map: both are the
   identity on the underlying set, only the equivalence coarsening.  The
   arrow actions agree by convertibility; the object actions do NOT, and
   the reason is the one [Construction/Deloop/Transform.v]
   already records -- [poly_unit] has no definitional eta, so the
   constant function at [ttt] and the identity on a one-element type are
   different terms (Test/ProbeGrpCongruence.v, negative 6). 

   --------
   * ** 投影函子是不循环的投影

   [QuotientProj] 和 #313 的 [quot_proj] 是相同的映射：它们在底层集合上都是恒等，只是等价关系被粗化。通过可转换性箭头作用是一致的；对象作用则不一致，原因在 [Construction/Deloop/Transform.v] 中已经记录——[poly_unit] 没有定义性 eta，因此 [ttt] 上的常函数和单元素类型上的恒等函数是不同的项（Test/ProbeGrpCongruence.v，第 -6 行）。
*)

Example deloop_proj_fmap {G : GrpObject} (N : NormalSubgroup G) (a : carrier G) :
  @fmap _ _ (quot_to_deloop N ◯ deloop_quotient_proj N) ttt ttt a
    = @fmap _ _ (deloop_hom (quot_proj N)) ttt ttt a := eq_refl.

Lemma deloop_proj_fobj {G : GrpObject} (N : NormalSubgroup G)
  (x : grp_deloop G) :
  fobj[quot_to_deloop N ◯ deloop_quotient_proj N] x
    = fobj[deloop_hom (quot_proj N)] x.
Proof. destruct x; reflexivity. Qed.

(*
   * ** Non-degeneracy over S3

   Everything above holds for every group and every normal subgroup, so
   nothing yet shows the congruence separates anything or merges
   anything.  #313's witnesses are reused rather than rebuilt: S3
   ([Instance/Grp/TwoFunctors.v], the semidirect presentation over
   the decidable carrier rot * bool, proved nonabelian there), its
   rotation subgroup A3, and the reflection subgroup [S3_refl_sub], which
   #313 proves is a subgroup and is NOT normal.

   NOT [Structure/Groupoid.v] [S3_Grp], although that file is
   imported here and although its S3 is already a
   [Category.Construction.Deloop.GrpObject] and already delooped
   ([deloop_S3_groupoid]).  The tree has exactly THREE presentations of
   the symmetric group: that one, [TwoFunctors.v] semidirect S3 on
   rot * bool, and [Instance/Grp/Epi.v] [GrpSym3].
   [Instance/Grp/Center.v] counts the latter two, both being
   [Instance/Grp.v] groups; [S3_Grp] is over the OTHER record and so
   falls outside that count.  #313's [A3] and [S3_refl_sub] are over
   [TwoFunctors.v]'s S3, so using [S3_Grp] would mean rebuilding both
   subgroups and both of their proofs -- the opposite of reuse. 

   --------
   * ** 在 S3 上的非退化性

   上述内容适用于每个群和每个正规子群，所以目前还没有任何迹象表明这个合同能够区分或合并任何东西。#313 的证据被重复使用而不是重建：S3（[Instance/Grp/TwoFunctors.v]，即在可判定载体 rot * bool 上的半直积表示，在那里证明了非阿贝尔性）、它的旋转子群 A3，以及反射子群 [S3_refl_sub]，#313 证明它是子群且不是正规子群。不是 [Structure/Groupoid.v] [S3_Grp]，尽管该文件已在此处导入，并且其 S3 已经是 [Category.Construction.Deloop.GrpObject] 并已去环 ([deloop_S3_groupoid])。该树恰好有三种对称群的表示：那一个、[TwoFunctors.v] 半直积 S3 在 rot * bool 上，以及 [Instance/Grp/Epi.v] [GrpSym3]。[Instance/Grp/Center.v] 计算后两者，两者都是 [Instance/Grp.v] 群；[S3_Grp] 在另一个记录上，因此不包含在该计数中。#313 的 [A3] 和 [S3_refl_sub] 是在 [TwoFunctors.v] 的 S3 上，因此使用 [S3_Grp] 意味着需要重建两个子群及其证明——这与重用的目的相反。
*)

(*
   * The congruence merges: the rotation is related to the identity arrow
   (which is [s3_unit], since [grp_unit S3 = s3_unit] and
   [deloop_id_is_unit] holds by [eq_refl]). 

   --------
   * 全同合并：旋转与恒等箭头相关（即 [s3_unit]，因为 [grp_unit S3 = s3_unit] 和 [deloop_id_is_unit] 由 [eq_refl] 成立）。
*)
Example A3_relates_rotation : ns_rel A3 ttt ttt S3_r s3_unit := eq_refl.

(** ...and separates: the reflection is not. / ……并分开：反射不是。 *)
Theorem A3_separates_reflection : ns_rel A3 ttt ttt S3_s s3_unit → False.
Proof. simpl; discriminate. Qed.

(*
   * So the projection functor is not faithful -- which is the whole point
   of a quotient category, and Fong and Spivak's “equations merge, never
   add” read at one object. 

   --------
   * 因此投影函子并非忠实——这正是商范畴的整个意义，Fong 和 Spivak 的“方程会合并，从不增加”在单一对象上的解读。
*)
Theorem A3_proj_not_faithful :
  (∀ (x y : grp_deloop S3) (f g : x ~> y),
     ns_rel A3 x y f g → f ≈ g) → False.
Proof.
  intro Hf.
  pose proof (Hf ttt ttt S3_r s3_unit A3_relates_rotation) as E.
  discriminate E.
Qed.

(*
   * The two orientations of the coset relation genuinely differ once
   normality is dropped, which is what [quot_rel_flip]'s header claims and
   this proves.  With a := s * r and b := r over the non-normal
   [S3_refl_sub]: a * b⁻¹ is the reflection and lies in it (by [eq_refl],
   the carrier being decidable), while b⁻¹ * a is a conjugate of the
   reflection and does not. 

   --------
   * 一旦放弃正规性，陪集关系的两种取向确实会有所不同，这正是 [quot_rel_flip] 的标题所声称的，并且这也得到了证明。在非正规 [S3_refl_sub] 上，设 a := s * r 和 b := r ： a * b⁻¹ 是反射并属于其中（根据 [eq_refl]，载体是可判定的），而 b⁻¹ * a 则是该反射的共轭元素，并不属于其中。
*)
Definition coset_witness : carrier S3 := grp_mul S3 S3_s S3_r.

Example coset_right : sub_mem S3_refl_sub
  (grp_mul S3 coset_witness (grp_inv S3 S3_r)) := eq_refl.

Theorem coset_orientations_differ :
  sub_mem S3_refl_sub (grp_mul S3 (grp_inv S3 S3_r) coset_witness) → False.
Proof. simpl; discriminate. Qed.

(*
   * And normality is not decoration: the reflection subgroup's relation is
   NOT a congruence on its delooping.  This is [congruence_iff_normal]
   against #313's [S3_refl_sub_not_normal], so the refutation consumes
   the whole class rather than isolating a field; which field the
   normality sits in is the remark in the necessity section above, and it
   is a remark. 

   --------
   * 正规性不是装饰：反射子群的关系  
   并不是其解环上的同余。这是 [congruence_iff_normal]  
   与 #313 的 [S3_refl_sub_not_normal] 相对，所以反驳消耗了  
   整个类，而不是孤立一个域；正规性所在的  
   域在上述必要性部分中已有说明，并且那只是一个说明。
*)
Theorem S3_refl_sub_no_congruence :
  @HomCongruence (grp_deloop S3) (sub_rel S3_refl_sub) → False.
Proof.
  intro HR.
  exact (S3_refl_sub_not_normal
           (fst (congruence_iff_normal S3_refl_sub) HR)).
Qed.

(*
   * The recovered normal subgroup of A3's congruence has A3's members,
   at the concrete witness: both directions, computed. 

   --------
   * A3 的同余的恢复正规子群具有 A3 的成员，  
   在具体实例中：两个方向，已计算。
*)
Example A3_round_forward :
  sub_mem (@cong_ns S3 (ns_rel A3) (ns_congruence A3)) S3_r := eq_refl.

Theorem A3_round_backward :
  sub_mem (@cong_ns S3 (ns_rel A3) (ns_congruence A3)) S3_s → False.
Proof. simpl; discriminate. Qed.
