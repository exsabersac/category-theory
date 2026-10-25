Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Discrete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Adjunction.Continuity.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Monotone.
Require Import Category.Instance.Proset.Limit.

(* Same two as Instance/Proset.v and Instance/Proset/Galois.v: [relation] and [PreOrder] below are the stdlib Prop-valued ones, not [crelation]. / 与 Instance/Proset.v 和 Instance/Proset/Galois.v 中的两个相同：下面的 [relation] 和 [PreOrder] 是 stdlib 的 Prop 值类型的，不是 [crelation]。 *)
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(*
   * * The power set of a setoid, ordered by inclusion

   Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.5
   construction 2 (printed p. 96).  Transcribed from the page image, in
   ASCII:

   "If U and V are sets, the set P(U) of all subsets of U is a preorder
   under inclusion.  For each function f : U -> V the direct image f_*,
   defined by f_*(X) = {f(x) | x in X} is an order-preserving function
   and hence a functor f_* : P(U) -> P(V).  The inverse image
   f^*(Y) = {x | fx = y for some y in Y} defines a functor
   f^* : P(V) -> P(U) in the opposite direction.  Since f_* X subset Y
   if and only if X subset f^* Y, the direct image functor f_* is left
   adjoint to the inverse image functor f^*."

   and, two paragraphs earlier on the same page, the sentence this file
   reads at the Type level rather than at [equiv]:

   "The unit of the adjunction is the inequality p <= RLp for all p,
   while the counit is LRq >= q for all q."

   nLab: https://ncatlab.org/nlab/show/power+set
   nLab: https://ncatlab.org/nlab/show/Galois+connection
   nLab: https://ncatlab.org/nlab/show/direct+image
   nLab: https://ncatlab.org/nlab/show/inverse+image
   Wikipedia: https://en.wikipedia.org/wiki/Image_(mathematics)

   Awodey, *Category Theory*, §9.4 Example 9.12 names the same adjunction
   (its topological caveat is Instance/Top/Image.v); §9.9 Exercise 4 asks
   for it as a pair of monotone maps of posets, which is section (G)
   below.  Riehl, *Category Theory in Context*, §4.6.3's "left adjoints
   preserve colimits, right adjoints preserve limits" is section (F).

   ** THE ISSUE'S "Current state" IS STALE, MEASURED AT THE BASE COMMIT

   The catalog entry says the carrier is missing and that searches for
   "direct image" and "inverse image" return nothing.  Neither holds.
   Instance/Sets/Powerset.v declares [Powerset_Prop_obj], the power
   set of a setoid AT ONE UNIVERSE -- the [equiv]-respecting Prop-valued
   predicates, that is [SetoidMorphism X Powerset_Prop_truth] -- and BOTH
   operations already act on it: the direct image is
   [Powerset_Prop_image] with its functor [Powerset_Prop],
   the inverse image is [Powerset_Prop_preimage]
   (Instance/Sets/Powerset/Universal.v) with its functor
   [Powerset_Prop_op].  Those two files even prove the two operations DIFFER
   ([powerset_inverse_ne_direct]).  The two search terms occur in
   three and four files respectively, as prose.

   What was genuinely absent, and is what this file supplies, is the
   INCLUSION ORDER as a category on that carrier, monotonicity of the two
   operations for it, the Galois connection, the adjunction, and the
   meet/join consequences.  Nothing above is redefined.

   ** PRIOR ART: THE OTHER INCLUSION-ORDERED POWER SET

   Instance/Rel/Dagger.v already carries [psub], inclusion of
   BOOL-VALUED subsets of a bare [Type], and makes it a category --
   also named [Powerset] -- for Awodey §1.9 Exercise 2(c)'s self-duality
   of the power set.  That is a different object: no setoid, so no
   respectfulness condition, and decidable membership, which is what lets
   complementation be an involution there.  The category here is over
   Prop-valued [equiv]-respecting predicates on a SETOID, which is what
   the issue's "respects setoid equality" clause asks for, and its
   membership is not decidable.  A comparison functor from that one to
   this one at a discrete setoid is measured but NOT built: requiring
   Instance/Rel/Dagger.v raises this file's transitive closure from 87
   modules to 98, which is not worth an optional bridge.

   THE NAME [Subsets] IS FORCED.  [Powerset] is taken twice --
   Instance/Rel/Dagger.v and Instance/Sets/Powerset.v -- and
   `make print-assumptions` loads many modules into ONE scope, where a
   third homonym would silently audit the wrong constant.  So the issue's
   suggested `Print Assumptions Powerset.` cannot be satisfied under that
   name and the category is [Subsets].

   ** WHAT IS DELIVERED, WITH GRADES

   (A) [subset_le], [subset_le_preorder], [Subsets X] (a [Proset], hence
   thin: [Subsets_thin], stated with Instance/Proset/Galois.v's [Thin]
   -- the tree has three predicates of that name and this file cites
   that one, the only one already in scope).  [Subsets_obj_carrier]
   and [Subsets_hom_is_subset_le] read the objects and homs back at
   [eq_refl].

   (B) [image_monotone], [preimage_monotone] (Prop-valued, a few lines
   each).

   (C) [image_preimage_galois], [DirectImage], [InverseImage] and the
   pinned **[image_preimage_adjunction f : DirectImage f ⊣ InverseImage
   f]**.  #380 is CONSUMED: [GaloisFunctor_l]/[GaloisFunctor_r]/
   [GaloisAdjunction] are applied, nothing is rebuilt, and the two
   functors' object actions read back at [eq_refl]
   ([direct_image_obj], [inverse_image_obj]) as does their agreement
   with the pre-existing functors ([direct_image_is_Powerset_Prop],
   [inverse_image_is_Powerset_Prop_op]).
   [image_galois_round_trip] returns the connection at Leibniz [=] on
   the WHOLE record.  (It is NOT named [galois_round_trip]: that is
   Instance/Proset/Galois.v's own lemma, and
   `make print-assumptions` loads many modules into one scope.)

   (D) The unit and the counit, at TYPE level.  [unit_incl] and
   [counit_incl] are Mac Lane's two inclusions proved directly, and
   [adj_unit_has_incl_type]/[adj_counit_has_incl_type] ascribe the
   adjunction's own [unit]/[counit] AT those types -- an ascription
   that typechecks by conversion.  Read it at its strength: it says
   the unit inhabits the type of Mac Lane's inclusion, which any
   inhabitant of that [Prop] does, and in a thin category an [≈]
   between parallel arrows is [True] ([subsets_equiv_is_True],
   [eq_refl]) and would say no more.  A STRICTER statement IS
   available and is blocked only by this file's own opacity: an
   audit rebuilt the connection with [image_transpose_to],
   [image_transpose_from], [unit_incl] and [counit_incl] closed
   [Defined] and found [unit S = unit_incl S] and
   [counit T = counit_incl T] at [eq_refl].  The four stay [Qed]
   here, no consumer reading through them, so the Leibniz
   identification is NOT shipped; an earlier draft called the
   ascription "the strongest available statement", which was false.

   (E) Meets and joins: [subset_inter]/[subset_union] at an ARBITRARY
   index [Type] with [subset_inter_IsGLB]/[subset_union_IsLUB], the
   binary and nullary specializations, and hence [Subsets_Cartesian],
   [Subsets_Cocartesian], [Subsets_Terminal], [Subsets_Initial],
   [Subsets_Complete] and [Subsets_Cocomplete] through
   Instance/Proset/Limit.v's biconditionals.

   (F) Preservation, both routes where both exist.
   [inverse_image_preserves_meets] is two lines direct;
   [inverse_image_preserves_meets_via_RAPL] is the same statement read
   off [right_adjoint_preserves_limit] at [Proset_Limit], and
   [inverse_image_meet_routes_agree] is the [Check]-style
   confirmation that the two inhabit ONE type.  Dually
   [direct_image_preserves_joins] and
   [direct_image_preserves_joins_via_LAPC].
   [inverse_image_preserves_joins] is DIRECT ONLY: the adjoint proof
   of that half needs f^*'s RIGHT adjoint, the dual image, which is
   #384's and is not built here.  And the direct image does NOT
   preserve meets -- [direct_image_not_meet_preserving], a theorem at
   the witness of (H), with the [eq_refl] form refuted in
   Test/ProbePowerset382.v.

   (G) Awodey §9.9 Exercise 4: [image_MonotoneFun]/[preimage_MonotoneFun]
   as Instance/Proset/Monotone.v's [MonotoneFun]s, with
   [Functor_of_monotone] of each agreeing with the corresponding
   functor on objects at [eq_refl]
   ([direct_image_is_monotone_functor_obj] and its mirror); the WHOLE
   functor records are NOT compared, and the reason is measured --
   [Functor_of_monotone] is a [Program Definition] whose three law
   fields are separate opaque obligations while [GaloisFunctor_l]'s
   are its own, so the difference is confined to the three law fields
   and touches neither data field.

   (H) Non-vacuity, over Instance/Sets/Powerset/Universal.v's own
   [powerset_fin2] and [powerset_const0] (the constant map at 0 on a
   two-element carrier; REUSED, no new witness):
   [unit_not_iso] and [counit_not_iso] show the adjunction is not an
   equivalence, and [direct_image_not_meet_preserving] separates the
   image of a meet from the meet of the images.  Every negative maps
   OUT to [False]; no induction over the truncation could yield one.

   ** ROUTE

   Everything transposes through [Powerset_squash]'s impredicative
   elimination: a truncated existential may be eliminated into any [Prop],
   and [subset_le] IS a [Prop], so [image_transpose_from] can open the
   squash where a Type-valued inclusion could not.  That is the whole
   reason the ORDER is put on the Prop-valued carrier rather than on
   Instance/Sets/Powerset.v's proof-relevant [Powerset_obj], whose
   inclusion `∀ x, S x → T x` is [Type@{o}]-valued and hence not a
   [relation] at all -- so neither [Proset] nor [GaloisConnection] can
   host it.  That rejection is pinned as the probe's formability
   negative 2 -- a SORT rejection, "Cannot enforce ... <= Prop", not a
   typing error; the probe's header records the reclassification.

   ** WHAT IS NOT DELIVERED

   No dual image and no `f^* ⊣ ∀_f`: that is #384, which owns the
   quantifier adjoints of Mac Lane's next page.  No Boolean connectives
   (#383).  No group-action Galois connection (#381, which depends on
   this file).  No comparison with Instance/Rel/Dagger.v's [Powerset]
   (measured above).  No subobject-level statement: that is
   Instance/Powerset/Subobject.v, which cannot go through [Proset] at all
   because [sub_le] is Type-valued.  No idempotent monad, no
   functoriality of [Subsets] in the setoid, no naturality of any
   identification, and no antisymmetric quotient -- see the setoid note
   below.

   ** THE SETOID POINT, DISCLOSED

   The OBJECTS of [Subsets X] are the carrier TYPE of
   [Powerset_Prop_obj X], not its setoid quotient.  So two [equiv]-equal
   subsets are DISTINCT objects of the category, mutually included and
   hence isomorphic ([subsets_iso_of_equiv]).  This is exactly
   Instance/Proset.v's design -- a proset is not a poset -- and matches
   Instance/Rel/Dagger.v's [Powerset], whose objects are likewise bare
   predicates.  Mac Lane says "preorder", not "poset", and the file keeps
   his word.

   ** UNIVERSES

   Every constant is at one level [o] with [Set < o], INHERITED from
   [Powerset_Prop_truth]'s carrier [Prop : Type@{Set+1}] -- the donor's
   constraint, not one introduced here.  [Subsets@{o u}] has object level
   [o] and hom level [u] with NO relation between them (the hom is
   Prop-valued, so it fits at any [u]); the only entries in its block are
   [Set < o] and two bounds against stdlib's [relation]/[PreOrder] global
   levels.  RECORDED CORRECTION: an earlier revision continued "The RAPL
   route additionally pins the hom level to [Set], inherited from
   Instance/Discrete.v's unannotated [DiscreteCat_Functor], which fixes
   the shape at [DiscreteCat@{u Set Set}] while [IsALimit] identifies the
   shape's hom-and-proof universe with the ambient's".  The diagnosis was
   right and the donor has since been repaired: it was annotated in place
   at Instance/Discrete.v in the PR "algebraic carriers are sets"
   (2026-09-17), so the pin no longer arrives from there.  The RAPL
   constants of section (F) are still WRITTEN at hom level [Set] --
   [Subsets@{o Set} X] appears literally in their statements -- and
   whether they can now be restated at a free hom level has NOT been
   re-measured; no code changed in that PR's prose pass.  What survives
   unchanged is the ORDER and its reason: [IsALimit] still identifies the
   shape's hom-and-proof universe with the ambient's, so (F)'s DIRECT
   statements are given first and the RAPL derivations second.  Measured
   per constant in the report; no [Set] is introduced by any definition
   in this file.

   ** CLOSURE, AND WHY

   87 transitive in-project dependencies (excluding this file), measured
   with every new file fed to coqdep.  Dropping the Require of
   Instance/Proset/Limit.v alone gives 65 (it costs 22); dropping
   Adjunction/Continuity.v alone gives 87 again (it costs nothing while
   Limit is present, its modules all lying inside Limit's); dropping
   both gives 63.  An earlier draft said 56 and 31, two figures
   consistent with each other and with nothing measured.  Requiring
   Instance/Rel/Dagger.v for the optional bridge would give 98.
   That module is required rather than avoided because (E) and (F) are
   stated with ITS [IsGLB]/[IsLUB]/[HasAllMeets]/[Proset_Cartesian]/
   [proset_Complete_iff_all_meets]; restating those here would be a
   lookalike of a donor that already exists.

   ** TRANSPARENCY

   The four files of this effort close fifteen proofs with [Defined]
   (five here, five in Powerset/Subobject.v, three in FinSet/Subsets.v,
   two in Top/Image.v -- counted by token, since two of them sit inline
   after a one-line script and a line-anchored count reports thirteen).
   Five are LOAD-BEARING, measured by flipping each one to [Qed] in a
   scratch copy: here, [subset_inter] and [subset_union] (the meet and
   join must reduce for the [IsGLB]/[IsLUB] proofs to typecheck); the
   other three are in the sibling files.  The remaining ten are
   [Defined] for uniformity and each compiles as [Qed].

   ** REGISTRATION

   Nothing here is an [Instance].  [Subsets_Cartesian] and its four
   siblings are plain [Definition]s, matching Instance/Proset/Limit.v's
   own convention for [Proset_Cartesian] and [Proset_Terminal]: a chosen
   meet must not become globally resolvable. 

   --------
   * * 一个集合的幂集，按包含关系排序

   Mac Lane, 《为工作数学家准备的范畴论》，第2版，第IV.5节
   构造2（印刷版第96页）。从页面图像转录，使用ASCII：

   “如果 U 和 V 是集合，则 U 的所有子集组成的集合 P(U) 在包含关系下是一个预序集合。对于每个函数 f : U -> V，直接像 f_* 定义为 f_*(X) = {f(x) | x 属于 X}，它是一个保持序的函数，因此是一个函子 f_* : P(U) -> P(V)。逆像 f^*(Y) = {x | fx = y 且 y ∈ Y} 定义了一个从相反方向的函子 f^* : P(V) -> P(U)。由于 f_* X ⊆ Y 当且仅当 X ⊆ f^* Y，因此直接像函子 f_* 是逆像函子 f^* 的左伴随。”而在同一页的两个段落之前，这个文件在类型级别而不是在 [equiv] 上读取的句子为：

   “伴随的单位是对所有 p 都有的不等式 p <= RLp，而余单位是对所有 q 都有的 LRq >= q。”

   nLab: https://ncatlab.org/nlab/show/power+set  
   nLab: https://ncatlab.org/nlab/show/Galois+connection  
   nLab: https://ncatlab.org/nlab/show/direct+image  
   nLab: https://ncatlab.org/nlab/show/inverse+image  
   Wikipedia: https://en.wikipedia.org/wiki/Image_(mathematics)  

   Awodey，《范畴论》，§9.4 示例 9.12 给出了相同的伴随（其拓扑警告为 Instance/Top/Image.v）；§9.9 练习 4 要求将其作为偏序集的单调映射对，这在下面的 (G) 节中。Riehl，《上下文中的范畴论》，§4.6.3 的“左伴随保持余积，右伴随保持极限”是 (F) 节。

   ** 本问题的“当前状态”已经过时，以基础提交为准目录条目显示承载器缺失，并且对“direct image”和“inverse image”的搜索没有返回任何结果。两者都不成立。Instance/Sets/Powerset.v 声明了 [Powerset_Prop_obj]，即一个集族 AT ONE UNIVERSE 的幂集——即 [equiv]——满足 Prop 值谓词，也就是 [SetoidMorphism X Powerset_Prop_truth]——并且两种操作已经在其上作用：direct image 是 [Powerset_Prop_image]，其函子为 [Powerset_Prop]，inverse image 是 [Powerset_Prop_preimage]（Instance/Sets/Powerset/Universal.v）及其函子 [Powerset_Prop_op]。那两个文件甚至证明了这两种操作是不同的（[powerset_inverse_ne_direct]）。这两个搜索词分别出现在三份和四份文件中，以散文形式出现。真正缺失的，也是本文件提供的，是作为该载体的一个类别的包含顺序、两个操作的单调性、Galois 连接、伴随关系以及交/并的结果。上述内容没有被重新定义。

   ** 现有技术：另一种包含顺序的幂集Instance/Rel/Dagger.v 已经包含了 [psub]，以及一个裸 [Type] 的 BOOL 值子集，并将其构造成一个范畴——也称为 [Powerset]——用于 Awodey §1.9 练习 2(c) 的幂集自对偶性。这是一个不同的对象：没有集合类，所以没有尊重性条件，并且元素归属是可判定的，这使得补集在这里成为一个自反操作。这里的范畴是在集合类上的 Prop 值 [equiv]-尊重的谓词上，其“尊重集合类等价”条款正是所要求的，并且其成员资格是不可判定的。从那个范畴到这个范畴在离散集合类上的比较函子是可测量的，但未构建：引入 Instance/Rel/Dagger.v 会将该文件的传递闭包从 87 个模块增加到 98 个模块，这对于一个可选的桥梁来说是不值得的。名称 [Subsets] 是强制使用的。[Powerset] 被使用了两次——
   Instance/Rel/Dagger.v 和 Instance/Sets/Powerset.v——并且
   `make print-assumptions` 将许多模块加载到一个作用域中，如果有第三个同名项，会悄悄地检查错误的常量。因此，建议使用的 `Print Assumptions Powerset.` 在该名称下无法满足，并且类别是 [Subsets]。

   ** 交付内容及评分

   (A) [subset_le], [subset_le_preorder], [Subsets X]（一种 [Proset]，因此
   稀薄：[Subsets_thin]，根据 Instance/Proset/Galois.v 的 [Thin] 说明
   ——该树有三个同名谓词，本文件引用的是其中的一个，这是唯一已在作用域中的）。[Subsets_obj_carrier] 和 [Subsets_hom_is_subset_le] 在 [eq_refl] 处读取对象和同态。

   (B) [image_monotone], [preimage_monotone]（Prop 值，每个仅几行）。(C) [image_preimage_galois]、[DirectImage]、[InverseImage] 以及固定的 **[image_preimage_adjunction f : DirectImage f ⊣ InverseImage f]**。#380 已被使用：[GaloisFunctor_l] / [GaloisFunctor_r] / [GaloisAdjunction] 已被应用，没有重新构建，并且两个函子的对象作用在 [eq_refl] ([direct_image_obj]、[inverse_image_obj]) 处被读回，与已有函子 ([direct_image_is_Powerset_Prop]、[inverse_image_is_Powerset_Prop_op]) 的一致性也同样如此。[image_galois_round_trip] 返回 Leibniz [=] 上整个记录的连接。（它并没有命名为 [galois_round_trip]：那是 Instance/Proset/Galois.v 的自身引理，`make print-assumptions` 将许多模块加载到一个作用域中。）(D) 单元和余单元，在类型层次上。[unit_incl] 和 [counit_incl] 是 Mac Lane 直接证明的两个包含，而 [adj_unit_has_incl_type] / [adj_counit_has_incl_type] 归属于伴随自身的 [unit] / [counit] 在那些类型上——这个归属通过转换进行类型检查。从其强度来理解：它表示单元属于 Mac Lane 包含的类型，而 [Prop] 的任何成员也属于该类型，在薄范畴中，平行箭头之间的 [≈] 是 [True]（[subsets_equiv_is_True]，[eq_refl]），不会说更多。可以得到一个更严格的声明，并且只被此文件自身的不透明性阻挡：一次审计重建了与 [image_transpose_to]、[image_transpose_from]、[unit_incl] 和 [counit_incl] 的连接，关闭了 [Defined] 并在 [eq_refl] 发现了 [unit S = unit_incl S] 和 [counit T = counit_incl T]。这四个保持在 [Qed]，这里没有消费者读取它们，所以莱布尼茨的识别没有发布；早期草稿称这种归属是“可用的最强声明”，这是错误的。

   (E) 交集与并集：在任意索引 [Type] 上，[subset_inter] / [subset_union] 与 [subset_inter_IsGLB] / [subset_union_IsLUB] 相结合，这是二元和零元特化，因此通过 Instance/Proset/Limit.v 的双条件，得到 [Subsets_Cartesian]、[Subsets_Cocartesian]、[Subsets_Terminal]、[Subsets_Initial]、[Subsets_Complete] 和 [Subsets_Cocomplete]。(F) 保留性，在两条路径都存在的情况下。
   [inverse_image_preserves_meets] 是两行直接的；
   [inverse_image_preserves_meets_via_RAPL] 是相同的陈述，
   从 [right_adjoint_preserves_limit] 在 [Proset_Limit] 读取，并且
   [inverse_image_meet_routes_agree] 是 [Check] 风格的
   确认这两者属于同一类型。 双重地
   [direct_image_preserves_joins] 和
   [direct_image_preserves_joins_via_LAPC]。
   [inverse_image_preserves_joins] 仅限直接：那一半的伴随证明
   需要 f^* 的右伴随，即对偶像，它是
   #384 的，并且这里没有构建。 并且直接像不
   保留交 — [direct_image_not_meet_preserving]，这是一个定理，
   由 (H) 的见证，ZWZ87WZZ 形式在
   Test/ProbePowerset382.v 中被反驳。(G) Awodey §9.9 练习 4：[image_MonotoneFun] / [preimage_MonotoneFun]  
   作为 Instance/Proset/Monotone.v 的 [MonotoneFun]，带有  
   [Functor_of_monotone]，每个都与 [eq_refl] 上对象的对应函子一致  
   （[direct_image_is_monotone_functor_obj] 及其镜像）；整个函子记录不会被比较，原因已衡量——  
   [Functor_of_monotone] 是一个 [Program Definition]，其三个定律字段是独立的模糊义务，而 [GaloisFunctor_l] 的  
   则是它自己的，所以差异仅限于三个定律字段，而不涉及数据字段。(H) 非空性，关于实例/集合/幂集/全集自身  
   [powerset_fin2] 和 [powerset_const0]（在两个元素的载体上恒为 0 的常值映射；重复使用，没有新的见证）：  
   [unit_not_iso] 和 [counit_not_iso] 显示该伴随不是一个等价，而 [direct_image_not_meet_preserving] 将一个会聚的像与像的会聚区分开来。每个负映射都映射到 [False]；没有对截断进行归纳能产生其中之一。

   ** 路径一切都通过 [Powerset_squash] 的不可公理化消去进行移位：一个截断的存在量词可以被消去到任何 [Prop] 中，而 [subset_le] 是一个 [Prop]，因此 [image_transpose_from] 可以打开一个类型值包含无法打开的压缩。这就是为什么顺序被放在 Prop 值承载而不是 Instance/Sets/Powerset.v 的与证明相关的 [Powerset_obj] 上的整个原因，其包含 `∀ x, S x → T x` 是 [Type@{o}] 值，因此根本不是 [relation] ——所以 [Proset] 和 [GaloisConnection] 都无法承载它。该拒绝被标记为探针的可形成性负 2 ——一种排序拒绝，“无法强制 ... <= Prop”，而不是类型错误；探针的头部记录了重新分类。

   ** 未交付内容是什么没有双重图像，也没有 `f^* ⊣ ∀_f`：那是 #384，它拥有 Mac Lane 下一页的量词伴随。没有布尔连接词（#383）。没有群作用 Galois 连接（#381，它依赖于此文件）。没有与 Instance/Rel/Dagger.v 的 [Powerset]（上面测量过）的比较。没有子对象级别的陈述：那是 Instance/Powerset/Subobject.v，由于 [sub_le] 是类型值，无法通过 [Proset]。没有幂等单子，没有 [Subsets] 在集合等价中的函子性，没有任何标识的自然性，也没有反对称商——见下面的集合等价注释。

   ** 集合等价点，已披露[Subsets X] 的对象是 [Powerset_Prop_obj X] 的载体类型，而不是它的集合商。因此，两个 [equiv] 相等的子集在该范畴中是不同的对象，它们相互包含，因此同构（[subsets_iso_of_equiv]）。这正是 Instance/Proset.v 的设计——一个前序集不是偏序集——并且与 Instance/Rel/Dagger.v 的 [Powerset] 相符，其对象同样是基本谓词。Mac Lane 使用“preorder”，而不是“poset”，该文件也保持了他的用词。

   ** 宇宙每个常量都位于一个级别 [o]，与 [Set < o] 一致，继承自 [Powerset_Prop_truth] 的承载者 [Prop : Type@{Set+1}] —— 捐赠者的约束，而不是在此引入的。[Subsets@{o u}] 具有对象级别 [o] 和同态级别 [u]，它们之间没有关系（同态是 Prop 值，因此适合于任何 [u]）；它的块中唯一的条目是 [Set < o] 和针对 stdlib 的 [relation] / [PreOrder] 全局级别的两个界限。记录的更正：早期版本继续写道“RAPL 路径额外将同态级别固定为 [Set]，继承自 Instance/Discrete.v 中未注释的 [DiscreteCat_Functor]，这在 [DiscreteCat@{u Set Set}] 处固定了形状，而 [IsALimit] 确定了形状的同态和证明宇宙与环境的关系。”诊断是正确的，捐赠者自那以后已经被修复：它在 PR "代数载体是集合"（2026-09-17）的 Instance/Discrete.v 中被注释在原处，因此引脚不再从那里到达。（F）节的 RAPL 常量仍然在同伦级别 [Set] 上被写入——[Subsets@{o Set} X] 在他们的陈述中是字面出现的——而且它们是否现在可以在自由同伦级别上重新陈述尚未重新测量；该 PR 的文字修订中没有更改任何代码。不变的是顺序及其原因：[IsALimit] 仍然将形状的同伦-证明宇宙与环境的宇宙识别，因此（F）的直接陈述首先给出，RAPL 推导其次。报告中对每个常量进行测量；在此文件中没有任何定义引入 [Set]。

   ** 关闭，以及原因87 个及物的项目内依赖（不包括此文件），通过向 coqdep 提供每个新文件进行测量。仅移除对 Instance/Proset/Limit.v 的 Require 会得到 65（它的成本是 22）；仅移除 Adjunction/Continuity.v 会再次得到 87（当 Limit 存在时无需额外成本，其所有模块都位于 Limit 内）；同时移除两者会得到 63。早期草稿中写的是 56 和 31，这两个数字相互一致，但与实际测量无关。为了可选桥接而 Require Instance/Rel/Dagger.v 会得到 98。因为 (E) 和 (F) 用 ITS [IsGLB] / [IsLUB] / [HasAllMeets] / [Proset_Cartesian] / [proset_Complete_iff_all_meets] 陈述，所以必须需要该模块而非避免；在这里重述这些将会是已存在的 donor 的仿制品。

   ** 透明性这项工作的四个文件通过 [Defined] 关闭了十五个证明（这里五个，Powerset/Subobject.v 中五个，FinSet/Subsets.v 中三个，Top/Image.v 中两个——按 token 计算，因为其中两个位于一行脚本之后且行锚计数显示十三个）。其中五个是承载型（LOAD-BEARING），通过在一个临时副本中将每个切换为 [Qed] 来测量：这里，[subset_inter] 和 [subset_union]（因为 [IsGLB] / [IsLUB] 的证明要进行类型检查，所以 meet 和 join 必须归约）；另外三个在兄弟文件中。剩下的十个是 [Defined]，为了统一，每个都能编译为 [Qed]。

   ** 注册这里没有任何 [Instance]。[Subsets_Cartesian] 及其四个同类只是普通的 [Definition]，与 Instance/Proset/Limit.v 对 [Proset_Cartesian] 和 [Proset_Terminal] 的约定一致：被选择的 meet 不能变得全局可解析。
*)

(* ------------------------------------------------------------------------ *)
(* * ** (A) The inclusion order, and the thin category / * ** (A) 包含顺序，以及薄类别 *)

(*
 Inclusion of Prop-valued subsets.  This IS a [relation] on the carrier,
 which is what [Proset] and [GaloisConnection] require and what the
 proof-relevant carrier cannot supply. 

 --------
 包含 Prop 值子集。这是载体上的 [relation]，这正是 [Proset] 和 [GaloisConnection] 所要求的，而与证明相关的载体无法提供。
*)
Definition subset_le@{o} {X : SetoidObject@{o o}}
  (S T : carrier (Powerset_Prop_obj@{o} X)) : Prop := ∀ x, S x → T x.

Definition subset_le_preorder@{o} (X : SetoidObject@{o o}) :
  PreOrder (@subset_le@{o} X) :=
  {| PreOrder_Reflexive  := fun S x Hx => Hx
   ; PreOrder_Transitive :=
       fun S T U HST HTU x Hx => HTU x (HST x Hx) |}.

(* Mac Lane's "P(U) ... is a preorder under inclusion", as a category. / Mac Lane 的“P(U) ... 在包含关系下是一个预序”，作为一个范畴。 *)
Definition Subsets@{o u} (X : SetoidObject@{o o}) : Category@{o u u} :=
  Proset@{o u} (subset_le_preorder@{o} X).

(*
 The objects are the subsets and the homs are the inclusions, on the
 nose.  These are equalities between OBJECTS and TYPES, not between
 morphisms: the setoid discipline's sanctioned same-term exception. 

 --------
 这些对象是子集，态射是包含，完全如此。这些是对象和类型之间的等式，而不是态射之间的等式：这是集合体规范允许的同一项例外。
*)
Example Subsets_obj_carrier@{o u} (X : SetoidObject@{o o}) :
  obj[Subsets@{o u} X] = carrier (Powerset_Prop_obj@{o} X) := eq_refl.

Example Subsets_hom_is_subset_le@{o u} (X : SetoidObject@{o o})
  (S T : Subsets@{o u} X) : (S ~{Subsets@{o u} X}~> T) = subset_le S T
  := eq_refl.

(* Thin, by construction. [Thin] is Instance/Proset/Galois.v's; the tree also has Structure/Thin.v's predicate of the same name, and Instance/Proset/Limit.v deliberately introduces none. / 根据构造是稀薄的。[Thin] 是 Instance/Proset/Galois.v 的；该树也具有 Structure/Thin.v 同名的谓词，而 Instance/Proset/Limit.v 则故意没有引入任何。 *)
Definition Subsets_thin@{o u +} (X : SetoidObject@{o o}) :
  Thin (Subsets@{o u} X) := proset_thin (subset_le_preorder@{o} X).

(*
 Every equivalence of parallel arrows is [True], so nothing downstream
 can be measured at [≈] inside this category. 

 --------
 每个平行箭头的等价都是 [True]，所以在该范畴内，下游的任何东西都无法在 [≈] 处被测量。
*)
Example subsets_equiv_is_True@{o u} {X : SetoidObject@{o o}}
  {S T : Subsets@{o u} X} (f g : S ~{Subsets@{o u} X}~> T) :
  (f ≈ g) = True := eq_refl.

(*
 Two [≈]-equal subsets are DISTINCT objects, isomorphic in the category:
 the setoid point of the header, as a construction. 

 --------
 两个 [≈] -相等的子集是不同的对象，在范畴中同构：作为一种构造，头部的集合点。
*)
Definition subsets_iso_of_equiv@{o u +} {X : SetoidObject@{o o}}
  {S T : carrier (Powerset_Prop_obj@{o} X)} (H : S ≈ T) :
  @Isomorphism (Subsets@{o u} X) S T.
Proof.
  unshelve econstructor.
  - exact (fun x Hx => proj1 (H x) Hx).
  - exact (fun x Hx => proj2 (H x) Hx).
  - exact I.
  - exact I.
Defined.

(* ------------------------------------------------------------------------ *)
(* * ** (B), (C) Monotonicity, the Galois connection, the adjunction / * ** (B)、(C) 单调性、伽罗瓦连接、伴随 *)

Section Images.

Universe o so u.
Constraint o < so.

Context {X Y : SetoidObject@{o o}}.
Context (f : X ~{Sets@{o so}}~> Y).

(* The direct image is order-preserving. Opening the truncation is legal because the goal is a [Prop]. / 直接映像是保持顺序的。打开截断是合法的，因为目标是一个 [Prop]。 *)
Lemma image_monotone (S T : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le S T →
  subset_le (Powerset_Prop_image@{o} f S) (Powerset_Prop_image@{o} f T).
Proof.
  intros H y Hy Q k.
  refine (Hy Q _); intros [x [Hx Hfx]].
  exact (k (existT _ x (H x Hx, Hfx))).
Qed.

(* The inverse image is order-preserving: there is nothing to open. / 逆像是保持顺序的：没有什么需要打开的。 *)
Lemma preimage_monotone (S T : carrier (Powerset_Prop_obj@{o} Y)) :
  subset_le S T →
  subset_le (Powerset_Prop_preimage@{o} f S) (Powerset_Prop_preimage@{o} f T).
Proof. intros H x Hx; exact (H (f x) Hx). Qed.

(* Mac Lane's displayed line, left to right: from f_* S subset T infer S subset f^* T. The witness is [x] itself, at [f x], by reflexivity. / Mac Lane 显示的线，从左到右：从 f_* S ⊆ T 推出 S ⊆ f^* T。其见证是 [x] 本身，在 [f x] 处，由自反性。 *)
Lemma image_transpose_to (S : carrier (Powerset_Prop_obj@{o} X))
  (T : carrier (Powerset_Prop_obj@{o} Y)) :
  subset_le (Powerset_Prop_image@{o} f S) T →
  subset_le S (Powerset_Prop_preimage@{o} f T).
Proof.
  intros H x Hx.
  refine (H (f x) _).
  apply Powerset_squash_intro@{o}; exists x; split;
    [ exact Hx | reflexivity ].
Qed.

(* ... and right to left. This is where [T]'s own respectfulness is spent: the witness [x] gives [T (f x)], and [f x ≈ y] transports it. / ... 从右到左。这里是 [T] 自身的尊重被花费的地方：证人 [x] 给了 [T (f x)]，而 [f x ≈ y] 将其传递。 *)
Lemma image_transpose_from (S : carrier (Powerset_Prop_obj@{o} X))
  (T : carrier (Powerset_Prop_obj@{o} Y)) :
  subset_le S (Powerset_Prop_preimage@{o} f T) →
  subset_le (Powerset_Prop_image@{o} f S) T.
Proof.
  intros H y Hy.
  refine (Hy (T y) _); intros [x [Hx Hfx]].
  exact (proj1 (@proper_morphism _ _ _ _ T (f x) y Hfx) (H x Hx)).
Qed.

(* THE GALOIS CONNECTION. All six fields are supplied by name. / 伽罗瓦连接。所有六个字段都是按名称提供的。 *)
Definition image_preimage_galois :
  GaloisConnection (@subset_le@{o} X) (@subset_le@{o} Y) :=
  {| gal_l := Powerset_Prop_image@{o} f
   ; gal_r := Powerset_Prop_preimage@{o} f
   ; gal_mono_l := image_monotone
   ; gal_mono_r := preimage_monotone
   ; gal_to   := image_transpose_to
   ; gal_from := image_transpose_from |}.

(* The two functors, and the adjunction: #380 applied, nothing rebuilt. / 这两个函子，以及伴随 #380 已应用，没有重建任何内容。 *)
Definition DirectImage : Subsets@{o u} X ⟶ Subsets@{o u} Y :=
  GaloisFunctor_l (subset_le_preorder@{o} X) (subset_le_preorder@{o} Y)
    image_preimage_galois.

Definition InverseImage : Subsets@{o u} Y ⟶ Subsets@{o u} X :=
  GaloisFunctor_r (subset_le_preorder@{o} X) (subset_le_preorder@{o} Y)
    image_preimage_galois.

Definition image_preimage_adjunction : DirectImage ⊣ InverseImage :=
  GaloisAdjunction (subset_le_preorder@{o} X) (subset_le_preorder@{o} Y)
    image_preimage_galois.

(** ** Readbacks for (C) / ** (C) 的回读 *)

Example direct_image_obj (S : carrier (Powerset_Prop_obj@{o} X)) :
  fobj[DirectImage] S = Powerset_Prop_image@{o} f S := eq_refl.

Example inverse_image_obj (T : carrier (Powerset_Prop_obj@{o} Y)) :
  fobj[InverseImage] T = Powerset_Prop_preimage@{o} f T := eq_refl.

(*
 The two functors act as the pre-existing [Sets]-level ones do.  Both
 hold at Leibniz [=] because the two sides are the SAME term -- the
 Functor/Bifunctor.v precedent the donor files cite for their own
 same-term lemmas. 

 --------
 这两个函子的作用就像已有的 [Sets] 级函子一样。在 Leibniz [=] 上两者都成立，因为两边是相同的项——Functor/Bifunctor.v 先例被捐赠文件引用来证明它们自己的相同项引理。
*)
Example direct_image_is_Powerset_Prop
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  fobj[DirectImage] S = fmap[Powerset_Prop@{o so}] f S := eq_refl.

Example inverse_image_is_Powerset_Prop_op
  (T : carrier (Powerset_Prop_obj@{o} Y)) :
  fobj[InverseImage] T
    = fmap[Powerset_Prop_op@{o so}]
        (f : Y ~{(Sets@{o so})^op}~> X) T := eq_refl.

(*
 #380's backward passage returns the connection this file supplied, at
 Leibniz [=] on the WHOLE record: its six fields are read off the two
 functors and the hom-set isomorphism, all of which were built from
 those very fields. 

 --------
 #380 的逆向传递返回了这个文件提供的连接，在 Leibniz [=] 的整个记录上：它的六个字段是从两个函子和同构集合读取的，这些都是由那些字段构建的。
*)
Example image_galois_round_trip :
  GaloisOfAdjunction (subset_le_preorder@{o} X) (subset_le_preorder@{o} Y)
    DirectImage InverseImage image_preimage_adjunction
  = image_preimage_galois := eq_refl.

(* * ** (D) The unit and the counit ARE the two inclusions / * ** (D) 单位和余单位就是这两个包含 *)

(* Mac Lane's two inequalities, proved directly. / 麦克莱恩的两个不等式，直接证明。 *)
Lemma unit_incl (S : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le S
    (Powerset_Prop_preimage@{o} f (Powerset_Prop_image@{o} f S)).
Proof.
  intros x Hx.
  apply Powerset_squash_intro@{o}; exists x; split;
    [ exact Hx | reflexivity ].
Qed.

Lemma counit_incl (T : carrier (Powerset_Prop_obj@{o} Y)) :
  subset_le
    (Powerset_Prop_image@{o} f (Powerset_Prop_preimage@{o} f T)) T.
Proof.
  intros y Hy.
  refine (Hy (T y) _); intros [x [Hx Hfx]].
  exact (proj1 (@proper_morphism _ _ _ _ T (f x) y Hfx) Hx).
Qed.

(*
 The adjunction's OWN unit and counit, ascribed at those very types.
 The ascription typechecks by conversion alone and says only that the
 unit inhabits the type of [unit_incl]; a Leibniz [unit S = unit_incl S]
 holds at [eq_refl] once the two transposes and the two inclusions above
 are closed [Defined] (measured by audit, out of tree) and is blocked
 here by their [Qed]s, which is why the names say "has the type of" and
 not "is". 

 --------
 在那些类型上归属于伴随的自身单元和余单元。归属仅通过转换类型检查，并且只说明单元属于 [unit_incl] 的类型；一旦上述两个转置和两个包含被闭合 [Defined]（通过审核测量，树外），则在 [eq_refl] 上持有 Leibniz [unit S = unit_incl S]，并且在此被它们的 [Qed] 阻塞，这就是为什么名称写作“具有…的类型”而不是“是”。
*)
Definition adj_unit_has_incl_type (S : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le S
    (Powerset_Prop_preimage@{o} f (Powerset_Prop_image@{o} f S)) :=
  @unit _ _ DirectImage InverseImage image_preimage_adjunction S.

Definition adj_counit_has_incl_type
  (T : carrier (Powerset_Prop_obj@{o} Y)) :
  subset_le
    (Powerset_Prop_image@{o} f (Powerset_Prop_preimage@{o} f T)) T :=
  @counit _ _ DirectImage InverseImage image_preimage_adjunction T.

End Images.

Arguments image_monotone {X Y} f S T H.
Arguments preimage_monotone {X Y} f S T H.
Arguments image_transpose_to {X Y} f S T H.
Arguments image_transpose_from {X Y} f S T H.
Arguments image_preimage_galois {X Y} f.
Arguments DirectImage {X Y} f.
Arguments InverseImage {X Y} f.
Arguments image_preimage_adjunction {X Y} f.
Arguments unit_incl {X Y} f S.
Arguments counit_incl {X Y} f T.

(* ------------------------------------------------------------------------ *)
(** ** (E) Meets and joins / **（E）会面并加入 *)

Section Bounds.

Universe o u.

Context {X : SetoidObject@{o o}}.

(* Intersection of an arbitrary family. A universally quantified [Prop] is a [Prop], so no truncation is needed and respectfulness is the family's, pointwise. / 任意族的交集。一个全称量化的 [Prop] 是一个 [Prop]，所以不需要截断，并且尊重性是族的，逐点的。 *)
Definition subset_inter {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X)) :
  carrier (Powerset_Prop_obj@{o} X).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier X) (is_setoid X) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ x, ∀ i : Idx, S i x) _).
  intros x y Hxy; split; intros H i.
  - exact (proj1 (@proper_morphism _ _ _ _ (S i) x y Hxy) (H i)).
  - exact (proj2 (@proper_morphism _ _ _ _ (S i) x y Hxy) (H i)).
Defined.

(*
 Union of an arbitrary family.  [ex] here is stdlib's Prop-valued
 existential, NOT the library's Type-valued [sigT]: the members [S i x]
 are already [Prop]s, so the existential lands in [Prop] and NO
 [Powerset_squash] is required -- in contrast with the direct image,
 whose existential quantifies over the carrier. 

 --------
 任意族的并。[ex] 这里是 stdlib 的 Prop 值存在量词，而不是库的 Type 值 [sigT] ：成员 [S i x] 已经是 [Prop]，因此存在量词位于 [Prop] 并且不需要 [Powerset_squash] —— 与直接像不同，直接像的存在量词量化的是载体。
*)
Definition subset_union {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X)) :
  carrier (Powerset_Prop_obj@{o} X).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier X) (is_setoid X) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ x, ex (fun i : Idx => S i x)) _).
  intros x y Hxy; split; intros Hi; destruct Hi as [i Hi]; exists i.
  - exact (proj1 (@proper_morphism _ _ _ _ (S i) x y Hxy) Hi).
  - exact (proj2 (@proper_morphism _ _ _ _ (S i) x y Hxy) Hi).
Defined.

Lemma subset_inter_IsGLB {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X)) :
  IsGLB (@subset_le@{o} X) S (subset_inter S).
Proof.
  split.
  - intros i x Hx; exact (Hx i).
  - intros n Hn x Hx i; exact (Hn i x Hx).
Defined.

Lemma subset_union_IsLUB {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X)) :
  IsLUB (@subset_le@{o} X) S (subset_union S).
Proof.
  split.
  - intros i x Hx; exists i; exact Hx.
  - intros n Hn x Hi; destruct Hi as [i Hi]; exact (Hn i x Hi).
Defined.

(* The binary and nullary specializations. / 二元和零元特化。 *)
Definition subset_meet (S T : carrier (Powerset_Prop_obj@{o} X)) :
  carrier (Powerset_Prop_obj@{o} X) := subset_inter (pair_family S T).

Definition subset_join (S T : carrier (Powerset_Prop_obj@{o} X)) :
  carrier (Powerset_Prop_obj@{o} X) := subset_union (pair_family S T).

Definition subset_top : carrier (Powerset_Prop_obj@{o} X) :=
  subset_inter (@empty_family _).

Definition subset_bot : carrier (Powerset_Prop_obj@{o} X) :=
  subset_union (@empty_family _).

Lemma subset_meet_l (S T : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le (subset_meet S T) S.
Proof. exact (fst (subset_inter_IsGLB (pair_family S T)) true). Qed.

Lemma subset_meet_r (S T : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le (subset_meet S T) T.
Proof. exact (fst (subset_inter_IsGLB (pair_family S T)) false). Qed.

Lemma subset_meet_greatest (N S T : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le N S → subset_le N T → subset_le N (subset_meet S T).
Proof.
  intros H1 H2.
  refine (snd (subset_inter_IsGLB (pair_family S T)) N _).
  intros [|]; assumption.
Qed.

Lemma subset_join_l (S T : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le S (subset_join S T).
Proof. exact (fst (subset_union_IsLUB (pair_family S T)) true). Qed.

Lemma subset_join_r (S T : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le T (subset_join S T).
Proof. exact (fst (subset_union_IsLUB (pair_family S T)) false). Qed.

Lemma subset_join_least (N S T : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le S N → subset_le T N → subset_le (subset_join S T) N.
Proof.
  intros H1 H2.
  refine (snd (subset_union_IsLUB (pair_family S T)) N _).
  intros [|]; assumption.
Qed.

Lemma subset_top_greatest (S : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le S subset_top.
Proof. intros x Hx i; destruct i. Qed.

Lemma subset_bot_least (S : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le subset_bot S.
Proof. intros x Hx; destruct Hx as [i _]; destruct i. Qed.

(* The four structures, and bicompleteness. Plain [Definition]s, never [Instance]s: the donors' own convention for [Proset_Cartesian] and [Proset_Terminal]. / 四个结构，以及双完备性。普通的 [Definition]，绝不 [Instance]：捐赠者自己对 [Proset_Cartesian] 和 [Proset_Terminal] 的习惯用法。 *)
Definition Subsets_Cartesian : @Cartesian (Subsets@{o u} X) :=
  Proset_Cartesian (subset_le_preorder@{o} X)
    subset_meet subset_meet_l subset_meet_r subset_meet_greatest.

Definition Subsets_Cocartesian : @Cocartesian (Subsets@{o u} X) :=
  Proset_Cocartesian (subset_le_preorder@{o} X)
    subset_join subset_join_l subset_join_r subset_join_least.

Definition Subsets_Terminal : @Terminal (Subsets@{o u} X) :=
  Proset_Terminal (subset_le_preorder@{o} X) subset_top subset_top_greatest.

Definition Subsets_Initial : @Initial (Subsets@{o u} X) :=
  Proset_Initial (subset_le_preorder@{o} X) subset_bot subset_bot_least.

Definition Subsets_HasAllMeets : HasAllMeets (@subset_le@{o} X) :=
  fun Idx S => existT _ (subset_inter S) (subset_inter_IsGLB S).

Definition Subsets_HasAllJoins : HasAllJoins (@subset_le@{o} X) :=
  fun Idx S => existT _ (subset_union S) (subset_union_IsLUB S).

(*
 THE [Set] INSTANCE, MADE VISIBLE IN THE SOURCE.  These two -- alone
 among the constants of this section -- are about [Subsets] at hom level
 [Set], and the instance is written out rather than inferred.

 RECORDED CORRECTION TO THE REASON.  An earlier revision said the
 [Set] was a PIN: "Both biconditionals route through
 [Proset_Limit]/[DiscreteCat_Functor], and Instance/Discrete.v's
 unannotated declaration of the latter fixes the shape at
 [DiscreteCat@{u Set Set}] while [IsALimit] identifies the shape's
 hom-and-proof universe with the ambient's."  The donor was annotated in
 place at Instance/Discrete.v in the PR "algebraic carriers are sets"
 (2026-09-17), so no [Set] is forced from there any more.  The literal
 [Set] below is therefore now a CHOICE rather than a pin, and has been
 left as it stands: restating these two at a free hom level was not
 attempted or measured in that PR, which changed prose only.  [IsALimit]
 still identifies the shape's hom-and-proof universe with the ambient's,
 which is the constraint that remains. 

 --------
 [Set] 实例，在源代码中可见。这两个——在本节的常量中是唯一的——在 hom 级别上约为 [Subsets] [Set]，并且该实例是写出来的而不是推断的。对原因的记录更正。早期的修订版本指出 [Set] 是一个 PIN：“两个双条件都通过 [Proset_Limit] / [DiscreteCat_Functor]，并且 Instance/Discrete.v 中未注解的后者声明将形状固定在 [DiscreteCat@{u Set Set}]，而 [IsALimit] 将形状的同构与证明宇宙与周围环境的宇宙对齐。” 该提供者已在 PR “代数载体是集合” (2026-09-17) 中在 Instance/Discrete.v 处被注释，所以从那里不再强制  [Set]。下面的字面 [Set] 因此现在是一个 CHOICE 而非 PIN，并且已保持原样：在那个 PR 中并未尝试或评估在自由同构层面重新陈述这两个内容，该 PR 仅更改了文字表述。[IsALimit] 依然将形状的同构与证明宇宙与周围环境的宇宙对齐，这是剩下的约束条件。
*)
Definition Subsets_Complete : @Complete (Subsets@{o Set} X) :=
  snd (proset_Complete_iff_all_meets (subset_le_preorder@{o} X))
    Subsets_HasAllMeets.

Definition Subsets_Cocomplete : @Cocomplete (Subsets@{o Set} X) :=
  snd (proset_Cocomplete_iff_all_joins (subset_le_preorder@{o} X))
    Subsets_HasAllJoins.

End Bounds.

(* ------------------------------------------------------------------------ *)
(** ** (F) Preservation, directly / **（F）保存，直接 *)

Section Preservation.

Universe o so.
Constraint o < so.

Context {X Y : SetoidObject@{o o}}.
Context (f : X ~{Sets@{o so}}~> Y).

(* Riehl §4.6.3's right-adjoint half, DIRECTLY: a preimage is a substitution and a meet is a universal quantifier, so the second clause is the transpose of the family's own second clause. / Riehl §4.6.3 的右伴随半部分，直接地：一个原像是一个替换，且一个交是一个全称量词，所以第二个子句是该族自身第二个子句的转置。 *)
Theorem inverse_image_preserves_meets {Idx : Type}
  (T : Idx → carrier (Powerset_Prop_obj@{o} Y))
  (m : carrier (Powerset_Prop_obj@{o} Y))
  (H : IsGLB (@subset_le@{o} Y) T m) :
  IsGLB (@subset_le@{o} X)
    (fun i => Powerset_Prop_preimage@{o} f (T i))
    (Powerset_Prop_preimage@{o} f m).
Proof.
  split.
  - intro i; exact (preimage_monotone f m (T i) (fst H i)).
  - intros n Hn.
    refine (image_transpose_to f n m _).
    refine (snd H (Powerset_Prop_image@{o} f n) _).
    intro i; exact (image_transpose_from f n (T i) (Hn i)).
Qed.

(* Dually, the left-adjoint half, again directly. / 同样，左伴随的部分，再次直接。 *)
Theorem direct_image_preserves_joins {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X))
  (m : carrier (Powerset_Prop_obj@{o} X))
  (H : IsLUB (@subset_le@{o} X) S m) :
  IsLUB (@subset_le@{o} Y)
    (fun i => Powerset_Prop_image@{o} f (S i))
    (Powerset_Prop_image@{o} f m).
Proof.
  split.
  - intro i; exact (image_monotone f (S i) m (fst H i)).
  - intros n Hn.
    refine (image_transpose_from f m n _).
    refine (snd H (Powerset_Prop_preimage@{o} f n) _).
    intro i; exact (image_transpose_to f (S i) n (Hn i)).
Qed.

(*
 THE HALF WITH NO ADJOINT ROUTE HERE.  Riehl proves this from f^*'s own
 RIGHT adjoint -- the dual image -- which is #384's and is not built in
 this file, so it is proved directly instead.  Membership in a join is
 not decomposable, so the argument runs at the level of the ORDER: [m]
 precedes the canonical union of the family, by the family's own second
 clause, and the union does decompose. 

 --------
 这里是无伴随路径的半边。Riehl 通过 f^* 自己的 证明了这一点
 右伴随——对偶图像——是#384的，不是内置的
 该文件，因此直接证明。加入的成员身份为
 不可分解，因此该论元在 ORDER： [m]
 在家族的法定结合之前，由家族自己的副手主持
 子句，并且并集会分解。
*)
Theorem inverse_image_preserves_joins {Idx : Type}
  (T : Idx → carrier (Powerset_Prop_obj@{o} Y))
  (m : carrier (Powerset_Prop_obj@{o} Y))
  (H : IsLUB (@subset_le@{o} Y) T m) :
  IsLUB (@subset_le@{o} X)
    (fun i => Powerset_Prop_preimage@{o} f (T i))
    (Powerset_Prop_preimage@{o} f m).
Proof.
  split.
  - intro i; exact (preimage_monotone f (T i) m (fst H i)).
  - intros n Hn x Hx.
    assert (Hu : subset_le m (subset_union T))
      by exact (snd H (subset_union T) (fst (subset_union_IsLUB T))).
    destruct (Hu (f x) Hx) as [i Hi].
    exact (Hn i x Hi).
Qed.

End Preservation.

(* ------------------------------------------------------------------------ *)
(* * ** (F) again: the same two statements read off RAPL and LAPC / * **（F）再次：从 RAPL 和 LAPC 上读出的相同两条语句 *)

(*
 These are stated at the [Set] hom level discussed in the header.  An
 earlier revision called that a PIN and attributed it to
 Instance/Discrete.v's unannotated [DiscreteCat_Functor] fixing the shape
 at [DiscreteCat@{u Set Set}]; that donor was annotated in place at its
 in the PR "algebraic carriers are sets" (2026-09-17), so the [Set]
 here is now a choice carried over rather than a pin, and restating it
 was not attempted.  [IsALimit] still identifies the shape's
 hom-and-proof universe with the ambient's; the DIRECT statements above
 carry no such identification, which is why they come first. 

 --------
 这些在 header 中讨论的 [Set] 同态级别上被陈述。早期的修订将其称为 PIN，并将其归因于 Instance/Discrete.v 中未注释的 [DiscreteCat_Functor]，固定 [DiscreteCat@{u Set Set}] 上的形状；该捐赠者在 PR “代数载体是集合”（2026-09-17）中被原位注释，因此这里的 [Set] 现在是一个延续下来的选择，而不是 PIN，并且没有尝试重述它。[IsALimit] 仍然将形状的同态与证明宇宙与环境的宇宙进行识别；上面的 DIRECT 语句没有这样的识别，这也是它们排在最前面的原因。
*)

Section RAPLRoute.

Universe o so.
Constraint o < so.

Context {X Y : SetoidObject@{o o}}.
Context (f : X ~{Sets@{o so}}~> Y).

Definition inverse_image_preserves_meets_via_RAPL {Idx : Type}
  (T : Idx → carrier (Powerset_Prop_obj@{o} Y))
  (m : carrier (Powerset_Prop_obj@{o} Y))
  (H : IsGLB (@subset_le@{o} Y) T m) :
  IsGLB (@subset_le@{o} X)
    (fun i => Powerset_Prop_preimage@{o} f (T i))
    (Powerset_Prop_preimage@{o} f m) :=
  isalimit_IsGLB (subset_le_preorder@{o} X)
    (InverseImage f ◯ DiscreteCat_Functor (C:=Subsets Y) T) _
    (@preserves_limit _ _ _ _ _
       (right_adjoint_preserves_limit (image_preimage_adjunction f)
          (DiscreteCat_Functor (C:=Subsets Y) T))
       (Proset_Limit (subset_le_preorder@{o} Y) T m H)).

(* The two routes inhabit ONE type: the pair typechecks. / 这两条路线属于同一种类型：这对能够进行类型检查。 *)
Definition inverse_image_meet_routes_agree {Idx : Type}
  (T : Idx → carrier (Powerset_Prop_obj@{o} Y))
  (m : carrier (Powerset_Prop_obj@{o} Y))
  (H : IsGLB (@subset_le@{o} Y) T m) :
  IsGLB (@subset_le@{o} X)
    (fun i => Powerset_Prop_preimage@{o} f (T i))
    (Powerset_Prop_preimage@{o} f m)
  * IsGLB (@subset_le@{o} X)
      (fun i => Powerset_Prop_preimage@{o} f (T i))
      (Powerset_Prop_preimage@{o} f m) :=
  (inverse_image_preserves_meets f T m H,
   inverse_image_preserves_meets_via_RAPL T m H).

(*
 The colimit side is stated at the CANONICAL join rather than at an
 arbitrary one, because Instance/Proset/Limit.v supplies [Proset_Limit]
 but no [Colimit]-record counterpart, so the [Colimit] this route needs
 is taken from [Subsets_Cocomplete], whose apex is [subset_union]. 

 --------
 余极限定于规范连接而不是任意连接，因为 Instance/Proset/Limit.v 提供了 [Proset_Limit]，但没有 [Colimit] 记录对应项，因此这条路径所需的 [Colimit] 是从 [Subsets_Cocomplete] 获取的，其顶点是 [subset_union]。
*)
Definition direct_image_preserves_joins_via_LAPC {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X)) :
  IsLUB (@subset_le@{o} Y)
    (fun i => Powerset_Prop_image@{o} f (S i))
    (Powerset_Prop_image@{o} f (subset_union S)) :=
  isacolimit_IsLUB (subset_le_preorder@{o} Y)
    (DirectImage f ◯ DiscreteCat_Functor (C:=Subsets X) S) _
    (preserves_colimit
       (left_adjoint_preserves_colimit (image_preimage_adjunction f)
          (DiscreteCat_Functor (C:=Subsets X) S))
       (Subsets_Cocomplete (DiscreteCat Idx)
          (DiscreteCat_Functor (C:=Subsets X) S))).

Definition direct_image_join_routes_agree {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X)) :
  IsLUB (@subset_le@{o} Y)
    (fun i => Powerset_Prop_image@{o} f (S i))
    (Powerset_Prop_image@{o} f (subset_union S))
  * IsLUB (@subset_le@{o} Y)
      (fun i => Powerset_Prop_image@{o} f (S i))
      (Powerset_Prop_image@{o} f (subset_union S)) :=
  (direct_image_preserves_joins f S (subset_union S)
     (subset_union_IsLUB S),
   direct_image_preserves_joins_via_LAPC S).

End RAPLRoute.

(* ------------------------------------------------------------------------ *)
(* * ** (G) Awodey §9.9 Exercise 4: the same thing as monotone maps / * ** (G) Awodey §9.9 练习 4：与单调映射相同的东西 *)

Section MonotoneReading.

Universe o so u.
Constraint o < so.

Context {X Y : SetoidObject@{o o}}.
Context (f : X ~{Sets@{o so}}~> Y).

Definition image_MonotoneFun :
  @MonotoneFun _ (@subset_le@{o} X) _ (@subset_le@{o} Y) :=
  {| mono_map  := Powerset_Prop_image@{o} f
   ; mono_pres := image_monotone f |}.

Definition preimage_MonotoneFun :
  @MonotoneFun _ (@subset_le@{o} Y) _ (@subset_le@{o} X) :=
  {| mono_map  := Powerset_Prop_preimage@{o} f
   ; mono_pres := preimage_monotone f |}.

(*
 The functors agree on OBJECTS on the nose.  The WHOLE records are not
 compared: [Functor_of_monotone] is a [Program Definition] whose three
 law fields are its own opaque obligations while [GaloisFunctor_l]'s are
 its own, so the difference is confined to those three fields and
 touches neither data field. 

 --------
 函子在对象上完全一致。整个记录并没有被比较：[Functor_of_monotone] 是一个 [Program Definition]，其三个法则字段是它自己的不透明义务，而 [GaloisFunctor_l] 的则是它自己的，因此差异仅限于这三个字段，并且不涉及数据字段。
*)
Example direct_image_is_monotone_functor_obj
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  fobj[Functor_of_monotone (subset_le_preorder@{o} X)
         (subset_le_preorder@{o} Y) image_MonotoneFun] S
    = fobj[DirectImage f] S := eq_refl.

Example inverse_image_is_monotone_functor_obj
  (T : carrier (Powerset_Prop_obj@{o} Y)) :
  fobj[Functor_of_monotone (subset_le_preorder@{o} Y)
         (subset_le_preorder@{o} X) preimage_MonotoneFun] T
    = fobj[InverseImage f] T := eq_refl.

End MonotoneReading.

(* ------------------------------------------------------------------------ *)
(** ** (H) Non-vacuity / ** (H) 非空性 *)

(*
 The witnesses are Instance/Sets/Powerset/Universal.v's own
 [powerset_fin2] (the two-element discrete setoid) and [powerset_const0]
 (the constant map at 0), reused rather than rebuilt, together with
 [powerset_sng1] = {1}. 

 --------
 这些证人是 Instance/Sets/Powerset/Universal.v 自身的 [powerset_fin2]（双元素离散集合类）和 [powerset_const0]（在 0 处的恒等映射），重用而不是重建，以及 [powerset_sng1] = {1}。
*)

Definition powerset_sng0@{o +} :
  carrier (Powerset_Prop_obj@{o} powerset_fin2@{o}) :=
  Powerset_Prop_singleton_pred@{o} (X:=powerset_fin2@{o}) Fin.F1.

(*
 The unit at {1} is not invertible: its target f^*(f_* {1}) is the WHOLE
 two-element set, since the constant map lands everything at 0. 

 --------
 {1} 处的单位不可逆：其目标 f^*(f_* {1}) 是整个两元素集合，因为常值映射将所有元素映射到 0。
*)
Theorem unit_not_iso@{o so +} :
  subset_le
    (Powerset_Prop_preimage@{o} powerset_const0@{o so}
       (Powerset_Prop_image@{o} powerset_const0@{o so} powerset_sng1@{o}))
    powerset_sng1@{o}
  → False.
Proof.
  intro H.
  refine (H Fin.F1 _ False _).
  - apply Powerset_squash_intro@{o}; exists (Fin.FS Fin.F1); split.
    + apply Powerset_squash_intro@{o}; reflexivity.
    + reflexivity.
  - intro Heq; discriminate Heq.
Qed.

(*
 The counit at {1} is not invertible either: f^* {1} is EMPTY, so its
 direct image is empty, while {1} is not. 

 --------
 {1} 处的余单位也不是可逆的：f^* {1} 是空的，所以它的直接像是空的，而 {1} 不是空的。
*)
Theorem counit_not_iso@{o so +} :
  subset_le powerset_sng1@{o}
    (Powerset_Prop_image@{o} powerset_const0@{o so}
       (Powerset_Prop_preimage@{o} powerset_const0@{o so} powerset_sng1@{o}))
  → False.
Proof.
  intro H.
  refine (H (Fin.FS Fin.F1) _ False _).
  - apply Powerset_squash_intro@{o}; reflexivity.
  - intros [x [Hx _]]; hnf in Hx.
    refine (Hx False _); intro Heq; discriminate Heq.
Qed.

(*
 And the direct image does NOT preserve meets: {0} and {1} are disjoint,
 so the image of their meet is empty, while the meet of their images
 contains 0.  The [eq_refl] form of this inequality is refuted in
 Test/ProbePowerset382.v. 

 --------
 而直接像不保持交：{0} 和 {1} 是不相交的，因此它们的交的像是空的，而它们像的交包含 0。这个不等式的 [eq_refl] 形式在 Test/ProbePowerset382.v 中被驳斥。
*)
Theorem direct_image_not_meet_preserving@{o so +} :
  Powerset_Prop_image@{o} powerset_const0@{o so}
      (subset_meet powerset_sng0@{o} powerset_sng1@{o})
    ≈ subset_meet
        (Powerset_Prop_image@{o} powerset_const0@{o so} powerset_sng0@{o})
        (Powerset_Prop_image@{o} powerset_const0@{o so} powerset_sng1@{o})
  → False.
Proof.
  intro H.
  refine (proj2 (H Fin.F1) _ False _).
  - intros [|].
    + apply Powerset_squash_intro@{o}; exists Fin.F1; split.
      * apply Powerset_squash_intro@{o}; reflexivity.
      * reflexivity.
    + apply Powerset_squash_intro@{o}; exists (Fin.FS Fin.F1); split.
      * apply Powerset_squash_intro@{o}; reflexivity.
      * reflexivity.
  - intros [x [Hx _]].
    refine (Hx true False _); intro H0.
    refine (Hx false False _); intro H1.
    rewrite <- H0 in H1; discriminate H1.
Qed.
