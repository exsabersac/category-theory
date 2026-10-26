(*
   * * The group completion (Grothendieck group) as a left adjoint

   Riehl, “Category Theory in Context” (2nd ed.), §4.1 Example 4.1.10
   (catalogue item [riehl:4.1:example10]) lists the group completion in
   two forms: as a left adjoint [CMonoid → Ab] to the functor forgetting
   inverses, and as a left adjoint [Monoid → Group].  This file delivers
   the FIRST form in full.  What is and is not delivered of the second is
   stated precisely below; nothing here claims the general
   non-commutative construction.

   ** NOT the Grothendieck construction

   [Construction/Grothendieck.v] builds the total category of an indexed
   category — the fibration construction.  It shares only the name.  No
   definition in this file is related to it, and this file requires
   neither it nor any of its satellites.

   ** The mathematics, and why the [+ k] is necessary

   Given a commutative monoid M, the group completion K(M) has as
   elements formal differences [a - b], encoded as pairs (a, b), under

   (a, b) ~ (c, d)  iff  ∃ k, a + d + k ≈ c + b + k.

   The slack term [k] is REQUIRED, not a convenience.  Without it the
   relation reads [a + d ≈ c + b], which is transitive only when M is
   cancellative: the transitivity computation turns

   a + d + k ≈ c + b + k    and    c + f + l ≈ e + d + l

   into [a + f + (d + k + l) ≈ e + b + (d + k + l)], and cancelling the
   [d] would be exactly the cancellation law M is not assumed to have.
   [groth_naive_not_transitive] REFUTES transitivity of the slack-free
   relation over a concrete monoid, namely the booleans under
   disjunction ([rig_cmon Bool_Rig], Theory/Algebra/Rig.v's Example 5.38
   read additively), so the necessity is proved rather than argued.  The
   price is that the completion can collapse: [groth_bool_trivial] shows
   K(bool, ∨) is the one-element group, and [groth_bool_insert_collapses]
   that the insertion identifies [true] with [false] there.

   AN EARLIER REVISION of this paragraph read: “The witness [k] is DATA —
   the library's [∃] is [sigT] and the relation is written as a [sigT]
   directly — so no choice principle is consumed anywhere below, and the
   mediator never inspects a witness it did not receive.”  The first clause
   is no longer true.  Since the PR “algebraic carriers are sets”
   (2026-09-17) the completion is a [CMonObject] and so owes [cmon_prop],
   which forces its equality to be a [Prop]; [groth_rel] is therefore Coq's
   [ex] and the slack term is not data.  The rest of the sentence still
   holds: an [ex] is not a double negation, no choice principle is consumed,
   and the mediator still inspects no witness it did not receive -- it
   reaches its [Type]-valued conclusion by [pequiv_to] first
   ([groth_med_respects]).

   ** What is delivered

   - [Ab_to_CMon : Ab ⟶ CMon], the functor forgetting inverses.  It did
   not exist in tree (measured: zero hits for [Ab_to_CMon] and its
   obvious spellings).  It is very cheap because [Instance/Ab.v]
   defines [AbHom A B := CMonHom A B] as a bare [Definition] and gives
   [Ab] literally [CMon]'s identity, composition and hom-setoid: the
   arrow action is the IDENTITY function, and both functor laws are
   [reflexivity].
   - [GrothendieckObject M : AbObject], the pairs quotient.
   - [groth_insert M : M ~{CMon}~> Ab_to_CMon (GrothendieckObject M)].
   - [groth_extend] / [groth_extend_unique] / [groth_universal], the
   universal mapping property.
   - [groth_universal_arrow], [groth_AUniversalArrow], and — through
   Theory/Universal/Arrow.v's generic machinery, the route
   Instance/Ab/Free.v, Instance/Grp/Free.v and Instance/Mod/Free.v all
   take — [GrothLeft] and [grothendieck_adjunction : GrothLeft ⊣
   Ab_to_CMon].
   - [GrothendieckFunctor : CMon ⟶ Ab], built DIRECTLY with the
   computable arrow action [(a, b) ↦ (f a, f b)], and related to the
   machine-produced [GrothLeft]: the object actions agree by [eq_refl]
   ([groth_functor_obj_agrees]) and the arrow actions up to [≈]
   ([groth_fmap_agrees]).  The two are not silently identified.

   ** Riehl's second form, [Monoid → Group]: DELIVERED ELSEWHERE

   It is NOT in this file, and the paragraphs below explain why the
   construction here cannot be it.  It IS delivered, in
   Instance/Grp/Completion.v, by the presentation route of (3).
   Reason (2) is exactly why that had to be a separate
   construction rather than a reuse of this one.

   (1) CORRECTED.  An earlier revision of this header said stating the
   second form would need “a forgetful [Grp ⟶ Mon] that does not
   exist”.  That was FALSE.  The bad evidence was a search for a
   category of ordinary set-level monoids that stopped at
   [Theory/Algebra/Monoid/Hom.v]'s [Mon] (INTERNAL monoids in a
   monoidal category) and [Construction/Deloop.v]'s [MonObject]
   (a bare record with no category).  An internal monoid in
   [(Sets, ∏)] IS an ordinary setoid monoid, so [MonSets] of
   Instance/Rng/MonoidRing.v is a usable category of them --
   Instance/Mon/Free.v develops the free monoid over exactly it --
   and the forgetful functor is [Grp_MonSets : Grp ⟶ MonSets] at
   Instance/Rng/GroupRing.v.  The second form is statable.

   (2) The pairs construction is the WRONG construction there, and this
   is not a matter of proof technique.  [GrothendieckObject] produces
   an abelian group for every input — that is definitional, its
   [ab_neg] being the swap — whereas the left adjoint of
   [Group → Monoid] must produce non-abelian groups: the group
   completion of the free monoid on two letters is the free group on
   two letters, and Instance/Grp/Free.v's
   [free_group_two_generators_nonabelian] proves that group
   non-abelian.  A construction always landing in [Ab] therefore
   cannot be that adjoint.  (The in-tree lemma is CITED here, not
   re-proved, and no statement in this file depends on it.)

   (3) What the general construction needs is a presentation: the free
   group on the underlying setoid of M, quotiented by the normal
   closure of the relations identifying [ab] with [a·b] and the empty
   word with the unit.  Both halves exist in tree —
   Instance/Grp/Free.v's [FreeGrp] and Instance/Grp/Quotient/Colimit.v's
   [InNormalClosure] — so the route is available.  It is a second
   file's worth of work, is NOT attempted HERE, and nothing below
   should be read as progress toward it -- it is carried out in
   Instance/Grp/Completion.v, whose [completion_can_be_nonabelian]
   confirms the object it produces escapes (2)'s obstruction.

   ** Strengths, measured strict-first

   Strict ([eq_refl], shipped as [Example]s):

   - [Ab_to_CMon_obj], [Ab_to_CMon_fmap] — the forgetful functor's two
   actions.
   - [groth_carrier], [groth_zero], [groth_neg_computes],
   [groth_plus_computes] — the completion's underlying data.
   - [groth_insert_computes] — the insertion is [a ↦ (a, 0)].
   - [groth_extend_computes] — the mediator IS [f a - f b], on the nose.
   - [groth_arrow_is_insert] — [universal_arrow_from_UMP] stores the
   supplied morphism as the second projection of the comma object it
   builds, so the universal arrow is the insertion with no proof
   involved.
   - [GrothLeft_obj], [groth_functor_obj_agrees] — both functors' object
   actions.
   - [groth_unit_is_insert] — the UNIT computes.  [unit] is derived in
   Theory/Adjunction.v as the transpose of the identity, so this had
   to be checked rather than assumed; it is [fmap[U] id ∘ arrow] and
   [fmap[Ab_to_CMon] id] is [CMon]'s identity, so the unit is the
   insertion itself.

   Not strict.  Three refutations, each PINNED as a [Fail] probe in the
   “Measured negatives” section below (stripped once and confirmed a
   genuine “cannot unify”), each with a positive control:

   - The COUNIT does not compute.  It is
   [unique_obj (ump_universal_arrows …)] and [ump_universal_arrows]
   (Theory/Universal/Arrow.v) is [Qed], so nothing reduces
   through it.  What holds is [≈]: [groth_counit_evaluates].  The
   probe DISCRIMINATES: the UNIT at the same adjunction does close by
   [eq_refl], so the obstruction is that one constant's opacity and
   not the adjunction packaging.
   - [fmap[GrothLeft]] does not compute either, for the same reason:
   [LeftAdjointFunctorFromUniversalArrows] defines it by universal
   factorization rather than by a formula.  This is precisely why
   [GrothendieckFunctor] is built directly, and why
   [groth_fmap_agrees] is [≈] and not [eq_refl].  Their OBJECT
   actions DO agree strictly, which is the control.
   - A pair is [≈] and not [eq_refl] to the difference of the two
   inserted elements: the completion is a QUOTIENT, and [(a, b)]
   against [(a + 0, 0 + b)] is exactly the slack the relation
   absorbs.  [groth_pair_is_difference] is the [≈] statement, and it
   is what forces the mediator.

   ** An elaboration hazard, third sighting

   [nat_to_Z] and [groth_Z_to_nat] raise TWO obligations, not three:
   instance resolution closes [proper_morphism] during elaboration
   because both of their setoids are Leibniz.  That is the hazard
   Instance/Sets/Products.v records and Structure/Limit/Power.v
   reports a second sighting of.  It is harmless at these two witnesses
   — their carriers are [nat] and [Z], already concrete — and the
   general definitions are unaffected: [groth_insert] raises all three,
   its setoids being abstract.  Noted so the next reader is not puzzled
   by the obligation count.

   ** Universes, measured off the constraint blocks

   No explicit universe instance is written on any functor or adjunction
   here: [Functor]'s universe arity differs between Rocq 9.1 and
   Coq 8.19/8.20, so such an annotation is not portable.

   - [groth_rel@{u u0 u1}] and [GrothendieckObject@{u u0 u1 u2 u3}]
   carry NO equation in their constraint blocks — only [≤] bounds
   ([u0 ≤ u], [u1 ≤ u], [u0 ≤ u2], [u3 ≤ u2] and stdlib projection
   bounds).  A bound is not an identification, and these two do not
   identify anything.
   (RE-MEASURED by [About] under [Set Printing Universes] after the
   PR “algebraic carriers are sets” (2026-09-17).  An earlier
   revision gave both arities as four, [@{u u0 u1 u2}], and listed
   the bounds as [u ≤ u1], [u ≤ u2], [u0 ≤ u1], [u0 ≤ u2].  The
   arities are three and five now and the bounds run the other way;
   the CLAIM — no equation in either block — is what was being made
   and it still holds.)
   - [groth_insert], [groth_extend], [groth_universal] and everything
   downstream DO carry [u = u0] and [u = u1], collapsing the input
   [CMonObject@{u u0 u1}] to one level.  **That is [CMon]'s doing,
   not the completion's, and the attribution is PROBED rather than
   assumed**: a bare [Definition probe_hom (M : CMonObject) : Type :=
   @hom CMon M M] already elaborates at [CMonObject@{u u u}], while
   [Definition probe_obj (M : CMonObject) : Type :=
   carrier (cmon_setoid M)] leaves all three FREE.  So merely NAMING
   a [CMon] hom is what identifies them — the shape
   Instance/Grp/Pushout.v records for [Grp] — and it appears exactly
   at the first constant of this file whose type mentions a hom.
   - [Ab_to_CMon@{u u0}], [GrothendieckFunctor@{u u0 u1}], [GrothLeft]
   and [grothendieck_adjunction] carry no equation either; their
   blocks hold [Set < u] and [≤] bounds.  The [Functor] instances
   read [@{u u0 u0 u u0 u0}] and [@{u u1 u1 u u1 u1}], hom identified
   with proof — inherited from [CMon] and [Ab], which are categories
   over [Sets], and introduced nowhere here.
   (RE-MEASURED after the same PR.  An earlier revision gave
   [GrothendieckFunctor]'s arity as two and the strictness as
   [u0 < u], “which is [Sets]' own”; it reads [Set < u] now, the
   bound [PropEquiv] brings in with [Prop]'s sort.  No equation
   appears in any of the four blocks, which is the claim.)
   - [Set] appears in exactly the two concrete witnesses one would
   expect: [groth_nat_Z_iso@{u}] is over [Set] carriers with the sole
   constraint [Set < u], and [groth_bool_trivial@{u}] carries [Set]
   in a universe INSTANCE while acquiring no [Set] constraint at all
   — an instance is not a constraint.  Nothing general in this file
   is pinned to [Set].

   ** Axioms

   91/91 constants closed under the global context — 74 source
   declarations plus 17 [Program] obligations, the count taken from
   [Print Module] rather than from the [.glob], which lists only the 74.

   RE-MEASURED after the PR “algebraic carriers are sets” (2026-09-17),
   by generating one [Print Assumptions] per name from [Print Module]:
   91 commands, 91 “Closed under the global context”, zero [Axioms:]
   blocks.  The TOTAL is unchanged; only the split moved, an earlier
   revision giving it as 71 source declarations plus 20 obligations.
   The [.glob] now carries 44 [def] and 30 [prf] lines.

   ** Non-vacuity

   Proved by mapping OUT into concrete abelian groups, since no induction
   on a quotienting relation can yield a negative:

   - [groth_nat_Z_iso : GrothendieckObject groth_nat ≅[Ab] ab_Z] — the
   motivating example K(ℕ, +) ≅ ℤ, a genuine [Isomorphism] in [Ab]
   with both round trips.  [ab_Z] is Instance/Ab/Coproduct.v's,
   REUSED rather than redeclared.
   - [groth_nat_insert_injective] — the insertion is injective on ℕ
   (which is cancellative), so the completion does not collapse
   there, and [groth_nat_nontrivial] separates two of its elements.
   - [groth_bool_trivial] / [groth_bool_insert_collapses] — over the
   non-cancellative (bool, ∨) the completion IS trivial and the
   insertion is not injective, so the cancellative hypothesis in the
   previous item is doing work.
   - [groth_naive_not_transitive] — the slack-free relation is not
   transitive, over that same monoid.

   ** NOT delivered

   Nothing of Riehl's second form, which lives in
   Instance/Grp/Completion.v as detailed above.  Beyond that: no comparison
   with Instance/Ab/Free.v's free abelian group (a different left
   adjoint, to [Ab_Forget : Ab ⟶ Sets]); no identification of
   [Ab_to_CMon] with any composite through [Grp]; no [Grp]-level reading
   of the completion, so [Instance/Grp/Abelianization.v]'s [Ab_to_Grp] is
   neither required nor used; no exactness, no functoriality of the
   relation in M beyond [GrothendieckFunctor] itself, no naturality
   clauses of the adjunction restated in the completion's own vocabulary,
   and no normal form for the relation (so no decision procedure).
   [groth_sub_cross] is a general fact about abelian groups and is an
   upstreaming candidate for Instance/Ab/Subtract.v; it is declared here
   rather than there because this file adds no line to any existing
   file. 

   --------
   * * 群完成（格罗滕迪克群）作为左伴随  

   Riehl，《情境中的范畴论》（第二版），§4.1 示例 4.1.10  
   （目录项 [riehl:4.1:example10]）列出了两种形式的群完成：作为一个左伴随 [CMonoid → Ab] 对遗忘逆元的函子，以及作为一个左伴随 [Monoid → Group]。本文件完整提供了第一种形式。关于第二种形式提供了和未提供的内容在下面有精确说明；这里没有宣称一般的非交换构造。  

   ** 不是格罗滕迪克构造  

   [Construction/Grothendieck.v] 构建了索引范畴的总范畴——纤维化构造。它仅共享名称。本文件中没有定义与之相关，本文件也不要求它或其任何相关结构。  

   ** 数学原理，以及为什么 [+ k] 是必要的给定一个交换幺半群 M，其群完成 K(M) 的元素是形式差 [a - b]，编码为对 (a, b)，满足

   (a, b) ~ (c, d)  当且仅当  ∃ k, a + d + k ≈ c + b + k。

   松弛项 [k] 是必需的，而不是方便的。没有它，关系就变为 [a + d ≈ c + b]，只有当 M 是可消去的时，传递性才成立：传递性计算过程为

   a + d + k ≈ c + b + k    和    c + f + l ≈ e + d + l进入 [a + f + (d + k + l) ≈ e + b + (d + k + l)]，并取消 [d] 恰好就是 M 未被假定具有的消去律。[groth_naive_not_transitive] 否定了在具体幺半群上无松弛关系的传递性，即在析取下的布尔代数（[rig_cmon Bool_Rig]，Theory/Algebra/Rig.v 的示例 5.38，以加法方式解读），因此必要性是被证明的而不是被论证的。代价是完成可能会坍塌：[groth_bool_trivial] 表明 K(bool, ∨) 是单元素群，而 [groth_bool_insert_collapses] 则表明插入将 [true] 和 [false] 视为相同。这段的早期修订版本写道：“证人 [k] 是 DATA——图书馆的 [∃] 是 [sigT]，且关系直接写为 [sigT]——因此下面没有消耗任何选择公理，调解者也从未检查未接收到的证人。”第一句话不再成立。自从 PR “代数载体是集合” (2026-09-17) 后，完成项是一个 [CMonObject]，因此欠 [cmon_prop]，这迫使其等式成为 [Prop]；因此 [groth_rel] 是 Coq 的 [ex]，而松弛项不是数据。句子的其余部分仍然成立：一个 [ex] 不是双重否定，没有消耗选择公理，调解者仍然不检查未接收到的证人——它首先通过 [pequiv_to]（[groth_med_respects]）达到其 [Type] 值的结论。** 交付的内容是什么- [Ab_to_CMon : Ab ⟶ CMon]，遗忘逆元的函子。它在树中不存在（测量结果：[Ab_to_CMon]及其明显拼写的命中次数为零）。它非常便宜，因为[Instance/Ab.v]将[AbHom A B := CMonHom A B]定义为一个裸[Definition]，并且字面上赋予[Ab] [CMon]的单位、组合和同值类：箭头作用是恒等函数，并且两个函子律为[reflexivity]。 - [GrothendieckObject M : AbObject]，成对商。 - [groth_insert M : M ~{CMon}~> Ab_to_CMon (GrothendieckObject M)]。 - [groth_extend] / [groth_extend_unique] / [groth_universal]，泛映射性质。 - [groth_universal_arrow]，[groth_AUniversalArrow]，并且——通过Theory/Universal/Arrow.v的通用机制，Instance/Ab/Free.v、Instance/Grp/Free.v和Instance/Mod/Free.v都采用——[GrothLeft]和[grothendieck_adjunction : GrothLeft ⊣ Ab_to_CMon]。-  [GrothendieckFunctor : CMon ⟶ Ab]，直接通过可计算箭头作用 [(a, b) ↦ (f a, f b)] 构建，并与机器生成的 [GrothLeft] 相关：对象作用通过 [eq_refl]（[groth_functor_obj_agrees]）一致，箭头作用在 [≈]（[groth_fmap_agrees]）上也一致。这两者不会被默默地识别为相同。

   ** Riehl 的第二种形式，[Monoid → Group]：在其他地方提供

   它不在此文件中，下面的段落解释了为什么这里的构造不能是它。它确实是在 Instance/Grp/Completion.v 中提供的，通过 (3) 的展示路线。原因 (2) 正是为什么必须是一个独立的构造，而不是重复使用这个构造。(1) 已更正。这个标题的早期修订曾说，陈述第二种形式需要“一个不存在的遗忘的 [Grp ⟶ Mon]”。那是错误的。错误的证据是对一类普通集合级单子的搜索停在了 [Theory/Algebra/Monoid/Hom.v] 的 [Mon]（单oidal范畴中的内部单子）和 [Construction/Deloop.v] 的 [MonObject]（一个没有范畴的裸记录）。[(Sets, ∏)] 中的内部单子确实是普通集合等价单子，因此 Instance/Rng/MonoidRing.v 中的 [MonSets] 是可用的它们的范畴——Instance/Mon/Free.v 正是在它上面发展了自由单子——而遗忘函子在 Instance/Rng/GroupRing.v 的 [Grp_MonSets : Grp ⟶ MonSets] 上。第二种形式是可以陈述的。(2) 这里的成对构造是错误的构造，这不是证明技巧的问题。[GrothendieckObject] 对每个输入都生成一个阿贝尔群——这是定义性的，它的 [ab_neg] 是交换——而 [Group → Monoid] 的左伴随必须生成非阿贝尔群：两个字母的自由幺半群的群完备化是两个字母的自由群，而 Instance/Grp/Free.v 的 [free_group_two_generators_nonabelian] 证明了该群是非阿贝尔的。因此，总是落在 [Ab] 的构造不能是那个伴随。（树内引理在这里被引用，而非重新证明，并且此文件中的任何语句都不依赖于它。）(3) 一般构造所需要的是一个表示：在 M 的基础集合上构造自由群，并通过将关系的正规闭包进行商化，使  [ab] 与  [a·b] 等价，并将空字与单位元等价。两部分都存在于 tree 中——Instance/Grp/Free.v 的 [FreeGrp] 和 Instance/Grp/Quotient/Colimit.v 的 [InNormalClosure]——因此这条路径是可用的。这是一份第二个文件的工作量，在此未尝试，并且以下内容不应被视为对此有所进展——它在 Instance/Grp/Completion.v 中完成，其中 [completion_can_be_nonabelian] 确认它生成的对象避开了 (2) 的障碍。

   ** 优势，严格优先衡量

   严格 ( [eq_refl] ，作为 [Example] s 发布)：- [Ab_to_CMon_obj]、[Ab_to_CMon_fmap] — 忘记函子的两个作用。- [groth_carrier]、[groth_zero]、[groth_neg_computes]、[groth_plus_computes] — 完成的基础数据。- [groth_insert_computes] — 插入是 [a ↦ (a, 0)]。- [groth_extend_computes] — 中介者是 [f a - f b]，完全相符。- [groth_arrow_is_insert] — [universal_arrow_from_UMP] 将提供的态射存储为它构建的逗号对象的第二投影，因此通用箭头就是不涉及证明的插入。- [GrothLeft_obj]、[groth_functor_obj_agrees] — 两个函子的对象作用。- [groth_unit_is_insert] — 单位计算。[unit] 在 Theory/Adjunction.v 中被导出为恒等的转置，因此必须检查而不能假设；它是 [fmap[U] id ∘ arrow] 并且 [fmap[Ab_to_CMon] id] 是 [CMon] 的恒等，因此单位就是插入本身。不严格。三条反驳，每条都在下面“测量的阴性”部分被标记为[Fail]探针（剥离一次并确认为真正的“无法统一”），每条都有阳性对照：- COUNIT 无法计算。它是 [unique_obj (ump_universal_arrows …)]，而 [ump_universal_arrows]（Theory/Universal/Arrow.v）是 [Qed]，所以没有任何东西能通过它进行化简。成立的是 [≈] : [groth_counit_evaluates]。探针区分：在同一附加下的 UNIT 确实通过 [eq_refl] 关闭，因此阻碍的是某个常数的不透明性，而不是附加的打包。- [fmap[GrothLeft] ] 也无法计算，原因相同：[LeftAdjointFunctorFromUniversalArrows] 是通过普遍分解而不是公式定义它的。这正是 [GrothendieckFunctor] 被直接构建的原因，并且为什么 [groth_fmap_agrees] 是 [≈] 而不是 [eq_refl]。它们的 OBJECT 操作严格一致，这就是控制点。- 一对是 [≈]，而不是 [eq_refl] 来对比两个插入元素的差异：完成是一个商，并且 [(a, b)] 对 [(a + 0, 0 + b)] 是关系吸收的确切松弛。[groth_pair_is_difference] 是 [≈] 的陈述，并且它是促使调解者的原因。

   ** 一个展开的风险，第三次观察[nat_to_Z] 和 [groth_Z_to_nat] 提出两个义务，而不是三个：
   实例解析在展开过程中关闭 [proper_morphism]，因为它们的 setoid 都是 Leibniz 的。这是在 Instance/Sets/Products.v 记录和 Structure/Limit/Power.v 报告的第二次出现。这在这两个证人上是无害的——它们的载体是 [nat] 和 [Z]，已经是具体的——而且一般定义不受影响：[groth_insert] 提出了三条义务，它的 setoid 是抽象的。这样记录，以便下一个读者不会被义务计数所困惑。

   ** 宇宙，按约束块测量

   这里没有在任何函子或伴随上书写显式的宇宙实例：[Functor] 的宇宙元数在 Rocq 9.1 和 Coq 8.19/8.20 之间有所不同，因此这样的注释不可移植。-  [groth_rel@{u u0 u1}] 和 [GrothendieckObject@{u u0 u1 u2 u3}] 在它们的约束块中不包含方程 —— 只有 [≤] 的界限（[u0 ≤ u]、[u1 ≤ u]、[u0 ≤ u2]、[u3 ≤ u2] 和标准库投影界限）。界限不是标识，这两个也没有标识任何东西。（由 [About] 在 [Set Printing Universes] 下重新测量，在 PR “代数载体是集合”之后（2026-09-17）。早期的修订将两者的元数都设为四，[@{u u0 u1 u2}]，并列出了界限为 [u ≤ u1]、[u ≤ u2]、[u0 ≤ u1]、[u0 ≤ u2]。现在的算子元数是三和五，而界限方向相反；所提出的主张——两个区块中都没有方程——正是之前所提出的，并且仍然成立。
   - [groth_insert], [groth_extend], [groth_universal] 以及之后的所有内容确实携带了 [u = u0] 和 [u = u1]，将输入 [CMonObject@{u u0 u1}] 折叠到一个层次。这是 [CMon] 的作用，而不是完成的作用，并且归因是被探查的而不是被假定的：一个简单的 [Definition probe_hom (M : CMonObject) : Type := @hom CMon M M] 已经在 [CMonObject@{u u u}] 处展开，而 [Definition probe_obj (M : CMonObject) : Type := carrier (cmon_setoid M)] 则将所有三个保持为自由。所以，仅仅命名一个 [CMon] hom 就能识别它们——对于 [Grp] 的形状 Instance/Grp/Pushout.v 记录——而且它恰好出现在此文件的第一个类型提到 hom 的常量处。——[Ab_to_CMon@{u u0}]、[GrothendieckFunctor@{u u0 u1}]、[GrothLeft] 和 [grothendieck_adjunction] 也没有方程；它们的区块包含 [Set < u] 和 [≤] 的界限。[Functor] 实例读取 [@{u u0 u0 u u0 u0}] 和 [@{u u1 u1 u u1 u1}]，hom 通过证明识别——继承自 [CMon] 和 [Ab]，它们是 [Sets] 上的范畴，并且在这里没有引入。（在相同的 PR 后重新测量。早期的修订将 [GrothendieckFunctor] 的元数定为二，并将严格性定为 [u0 < u]，“这是 [Sets] 自己的”；现在读作 [Set < u]，边界 [PropEquiv] 引入了 [Prop] 的类型。在四个模块中都没有出现方程，这是声明。)
   - [Set] 恰好出现在两个具体例证中，这是人们所期望的：[groth_nat_Z_iso@{u}] 存在于 [Set] 个承载体上，唯一约束是 [Set < u]，而 [groth_bool_trivial@{u}] 在一个宇宙实例中承载 [Set]，同时没有获得任何 [Set] 约束——实例不是约束。文件中没有任何通用内容固定于 [Set]。

   ** 公理91/91 常量在全局上下文下封闭 — 74 个源声明加上 17 个 [Program] 义务，计数取自 [Print Module] 而非 [.glob]，后者仅列出 74 个。

   在 PR “代数载体是集合”(2026-09-17) 后重新测量，通过从 [Print Module] 为每个名称生成一个 [Print Assumptions]：
   91 个命令，91 个“在全局上下文下封闭”，零个 [Axioms:] 块。总数保持不变；仅分配方式发生变化，早期版本显示为 71 个源声明加 20 个义务。
   [.glob] 现在包含 44 行 [def] 和 30 行 [prf]。

   ** 非空性

   通过将 OUT 映射到具体阿贝尔群来证明，因为对商关系进行归纳不可能得到负数:-  [groth_nat_Z_iso : GrothendieckObject groth_nat ≅[Ab]  ab_Z] — 激励示例 K(ℕ, +) ≅ ℤ，在 [Ab] 中是一个真正的 [Isomorphism]，并且具有双向映射。[ab_Z] 来自 Instance/Ab/Coproduct.v，被重复使用而不是重新声明。  
   -  [groth_nat_insert_injective] — 插入在 ℕ 上是单射的（ℕ 是可消除的），因此完成在那里不会塌缩，并且 [groth_nat_nontrivial] 能区分它的两个元素。  
   -  [groth_bool_trivial] / [groth_bool_insert_collapses] — 在非可消除的 (bool, ∨) 上，完成是平凡的，并且插入不是单射的，所以前一项中的可消除性假设起作用。  
   -  [groth_naive_not_transitive] — 无松弛关系在相同的幺半群上不是传递的。  

   ** 未交付Riehl 的第二种形式，在 Instance/Grp/Completion.v 中存在，如上所述。除此之外：没有与 Instance/Ab/Free.v 中的自由交换群（不同的左伴随，指向 [Ab_Forget : Ab ⟶ Sets]）进行比较；没有将 [Ab_to_CMon] 与通过 [Grp] 的任何复合进行识别；没有对完成的 [Grp] 级别的读取，因此 [Instance/Grp/Abelianization.v] 的 [Ab_to_Grp] 既不被要求也未被使用；没有精确性，在 M 中超出 [GrothendieckFunctor] 本身的关系没有函子性质；没有在完成自身的词汇中重述伴随的自然性条款；关系没有规范形式（因此没有判定程序）。[groth_sub_cross] 是关于阿贝尔群的一般事实，并且是 Instance/Ab/Subtract.v 的上游候选；它在这里声明而不是在那里，因为此文件不会向任何现有文件添加任何行。
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Ab.Coproduct.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* * ** The functor forgetting inverses / * ** 忘记逆元的函子 *)

(*
 [AbHom A B] IS [CMonHom A B] (Instance/Ab.v's bare [Definition]), and
 [Ab]'s identity, composition and hom-setoid are [CMon]'s, so the arrow
 action of the forgetful functor is the identity function and both
 functor laws hold by [reflexivity]. 

 --------
 [AbHom A B] 是 [CMonHom A B]（实例/Ab.v 的裸 [Definition]），并且 [Ab] 的同一性、组合和同类集合是 [CMon] 的，因此遗忘函子在箭头上的作用是恒等函数，并且两个函子律由 [reflexivity] 保证成立。
*)
Program Definition Ab_to_CMon : Ab ⟶ CMon := {|
  fobj := fun A => ab_cmon A;
  fmap := fun _ _ f => f
|}.
Next Obligation. intros A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros A a; simpl; reflexivity. Qed.
Next Obligation. intros A B C f g a; simpl; reflexivity. Qed.

(* Both actions are strict. / 这两种行为都很严厉。 *)
Example Ab_to_CMon_obj (A : AbObject) :
  fobj[Ab_to_CMon] A = ab_cmon A := eq_refl.

Example Ab_to_CMon_fmap (A B : AbObject) (f : A ~{Ab}~> B) :
  fmap[Ab_to_CMon] f = f := eq_refl.

(*
   * ** A cross-multiplication lemma for abelian groups

   [x + v ≈ u + y] gives [x - y ≈ u - v].  This is the one step where the
   completion's relation is turned into an equation between formal
   differences, and it is what makes the mediator well defined.  It is a
   general fact about abelian groups; see the NOT-delivered note. 

   --------
   * ** 阿贝尔群的交叉乘法引理

   [x + v ≈ u + y] 给出 [x - y ≈ u - v]。这是将完备性的关系转换为形式差之间方程的唯一步骤，它使中介是良定义的。这是关于阿贝尔群的一个一般性事实；参见未交付的注释。
*)
Lemma groth_sub_cross (A : AbObject)
  (x y u v : carrier (cmon_setoid A)) :
  cmon_plus A x v ≈ cmon_plus A u y →
  ab_sub A x y ≈ ab_sub A u v.
Proof.
  intro H.
  apply (ab_cancel_l A (cmon_plus A y v)).
  transitivity (cmon_plus A x v).
  { rewrite (cmon_plus_assoc A y v (ab_sub A x y)).
    rewrite (cmon_plus_comm A v (ab_sub A x y)).
    rewrite <- (cmon_plus_assoc A y (ab_sub A x y) v).
    now rewrite (ab_add_sub_cancel A x y). }
  transitivity (cmon_plus A u y); [ exact H |].
  symmetry.
  rewrite (cmon_plus_comm A y v).
  rewrite (cmon_plus_assoc A v y (ab_sub A u v)).
  rewrite (cmon_plus_comm A y (ab_sub A u v)).
  rewrite <- (cmon_plus_assoc A v (ab_sub A u v) y).
  now rewrite (ab_add_sub_cancel A u v).
Qed.

(* * ** The group completion of a commutative monoid / * ** 交换幺半群的群化 *)

Section Grothendieck.

Context (M : CMonObject).

Local Notation "x ⊞ y" := (cmon_plus M x y)
  (at level 50, left associativity).

Local Notation "'MC'" := (carrier (cmon_setoid M)).

(* Elements of the completion are formal differences, encoded as pairs. / 完成的要素是形式差异，以成对编码。 *)
Definition GrothPair : Type := (MC * MC)%type.

(*
 The relation, with the slack term [k] the header explains.

 AN EARLIER REVISION said “The library's [∃] is [sigT], so [k] is DATA and
 no choice principle is consumed.”  The first clause is still true of the
 library's [∃] (Lib/Foundation.v); the relation below no longer uses
 it.  Since the PR “algebraic carriers are sets” (2026-09-17) the completion
 is a [CMonObject] and so owes [cmon_prop], which forces its equality to be
 a [Prop]; [k] is therefore existentially quantified with Coq's [ex] and is
 no longer data.  Still no choice principle is consumed -- an [ex] is not a
 double negation -- but the slack term cannot be read back out into a
 [Type]-valued goal, and every consumer below that used to destruct it now
 either lands in a [Prop] goal already or goes through [pequiv_to] first.
 The body compares through [pequiv] rather than `≈` because the body of an
 [ex] must itself be a [Prop]; [ex] is written out rather than spelled
 [(exists k, …)%type] so that the [⊞] notation stays in scope. 

 --------
 该关系，带有松弛项 [k]，标题进行了说明。早期的修订中说：“图书馆的 [∃] 是 [sigT]，因此 [k] 是 DATA，并且没有消耗选择原理。”图书馆的 [∃]（Lib/Foundation.v）第一句仍然成立；下方的关系不再使用它。自从 PR “代数载体是集合”（2026-09-17）以来，补全是一个 [CMonObject]，因此欠 [cmon_prop]，这迫使其等式成为一个 [Prop]；因此 [k] 被用 Coq 的 [ex] 存在量化，并且不再是数据。仍然没有消耗选择原理——一个 [ex] 不是双重否定——但松弛项无法重新读回成为一个 [Type] 值的目标，并且每个下方以前用来析构它的使用者，现在要么直接进入一个已经存在的 [Prop] 目标，要么先经过 [pequiv_to]。主体通过 [pequiv] 进行比较，而不是 `≈`，因为 [ex] 的主体本身必须是 [Prop]；[ex] 被写出来而不是拼写为 [(exists k, …)%type]，以便 [⊞] 符号保持在作用域内。
*)
Definition groth_rel (p q : GrothPair) : Prop :=
  ex (fun k : MC =>
        @pequiv _ _ (cmon_prop M)
          (fst p ⊞ snd q ⊞ k) (fst q ⊞ snd p ⊞ k)).

(* The slack-free relation, for the necessity argument below. / 下面必要性论证的无松弛关系。 *)
Definition groth_naive (p q : GrothPair) : Type :=
  fst p ⊞ snd q ≈ fst q ⊞ snd p.

Lemma groth_rel_refl (p : GrothPair) : groth_rel p p.
Proof. exists (cmon_zero M); apply pequiv_from; reflexivity. Qed.

Lemma groth_rel_sym (p q : GrothPair) : groth_rel p q → groth_rel q p.
Proof.
  intros [k Hk]; apply pequiv_to in Hk.
  exists k; apply pequiv_from; now symmetry.
Qed.

(*
 Three commutative-monoid rearrangements, named so that the transitivity
 argument below reads as the three rewrites it is.  Each is a
 consequence of [cmon_plus_interchange] (Instance/CMon/Biproduct.v)
 plus associativity and commutativity. 

 --------
 三个交换幺半群重排，如此命名是为了使下面的传递性论证可以作为三个重写来阅读。每一个都是 [cmon_plus_interchange] (Instance/CMon/Biproduct.v) 的推论，加上结合律和交换律。
*)
Lemma groth_ac1 (a d k f l : MC) :
  a ⊞ f ⊞ (d ⊞ k ⊞ l) ≈ a ⊞ d ⊞ k ⊞ (f ⊞ l).
Proof.
  rewrite (cmon_plus_interchange M a f (d ⊞ k) l).
  now rewrite <- (cmon_plus_assoc M a d k).
Qed.

Lemma groth_ac2 (c b k f l : MC) :
  c ⊞ b ⊞ k ⊞ (f ⊞ l) ≈ c ⊞ f ⊞ l ⊞ (b ⊞ k).
Proof.
  rewrite (cmon_plus_assoc M c b k).
  rewrite (cmon_plus_interchange M c (b ⊞ k) f l).
  rewrite (cmon_plus_comm M (b ⊞ k) l).
  now rewrite <- (cmon_plus_assoc M (c ⊞ f) l (b ⊞ k)).
Qed.

Lemma groth_ac3 (e d l b k : MC) :
  e ⊞ d ⊞ l ⊞ (b ⊞ k) ≈ e ⊞ b ⊞ (d ⊞ k ⊞ l).
Proof.
  rewrite (cmon_plus_assoc M e d l).
  rewrite (cmon_plus_interchange M e (d ⊞ l) b k).
  rewrite (cmon_plus_assoc M d l k).
  rewrite (cmon_plus_comm M l k).
  now rewrite <- (cmon_plus_assoc M d k l).
Qed.

(*
 The transitivity computation.  The produced witness is [d ⊞ k ⊞ l];
 the [d] is what a cancellative monoid would let one drop. 

 --------
 传递性计算。生成的证人是 [d ⊞ k ⊞ l]；[d] 是可消去幺半群会允许去掉的。
*)
Lemma groth_rel_trans (p q r : GrothPair) :
  groth_rel p q → groth_rel q r → groth_rel p r.
Proof.
  destruct p as [a b], q as [c d], r as [e f].
  intros [k Hk] [l Hl].
  apply pequiv_to in Hk; apply pequiv_to in Hl; simpl in Hk, Hl.
  exists (d ⊞ k ⊞ l); apply pequiv_from; simpl.
  rewrite (groth_ac1 a d k f l).
  rewrite Hk.
  rewrite (groth_ac2 c b k f l).
  rewrite Hl.
  apply (groth_ac3 e d l b k).
Qed.

#[local] Instance groth_rel_Equivalence : Equivalence groth_rel.
Proof.
  constructor.
  - exact groth_rel_refl.
  - exact groth_rel_sym.
  - exact groth_rel_trans.
Qed.

Definition groth_setoid : SetoidObject := {|
  carrier   := GrothPair;
  is_setoid := {| equiv := groth_rel;
                  setoid_equiv := groth_rel_Equivalence |}
|}.

(** *** The group operations / *** 群运算 *)

Definition groth_zero : GrothPair := (cmon_zero M, cmon_zero M).

Definition groth_plus (p q : GrothPair) : GrothPair :=
  (fst p ⊞ fst q, snd p ⊞ snd q).

Definition groth_neg (p : GrothPair) : GrothPair := (snd p, fst p).

Lemma groth_plus_respects :
  Proper (groth_rel ==> groth_rel ==> groth_rel) groth_plus.
Proof.
  (*
 [simpl] before the elimination: the goal is an application of the
 [equiv] projection, whose ascribed sort is [Type], and [groth_rel] is now
 a [Prop].  Instance/Ab.v's [AbQuotient] records the same step. 

 --------
 [simpl] 消除前：目标是 [equiv] 投影的一个应用，其指定类别是 [Type]，而 [groth_rel] 现在是一个 [Prop]。实例/Ab.v 的 [AbQuotient] 记录了相同的步骤。
*)
  intros [a b] [a' b'] Hab [c d] [c' d'] Hcd; simpl in Hab, Hcd |- *.
  destruct Hab as [k Hk], Hcd as [l Hl].
  apply pequiv_to in Hk; apply pequiv_to in Hl; simpl in Hk, Hl.
  exists (k ⊞ l); apply pequiv_from; simpl.
  rewrite (cmon_plus_interchange M a c b' d').
  rewrite (cmon_plus_interchange M (a ⊞ b') (c ⊞ d') k l).
  rewrite Hk, Hl.
  rewrite (cmon_plus_interchange M (a' ⊞ b) k (c' ⊞ d) l).
  now rewrite (cmon_plus_interchange M a' b c' d).
Qed.

Lemma groth_neg_respects : Proper (groth_rel ==> groth_rel) groth_neg.
Proof.
  intros [a b] [a' b'] Hab; simpl in Hab |- *.
  destruct Hab as [k Hk]; apply pequiv_to in Hk; simpl in Hk.
  exists k; apply pequiv_from; simpl.
  rewrite (cmon_plus_comm M b a').
  rewrite (cmon_plus_comm M b' a).
  now symmetry.
Qed.

Lemma groth_plus_assoc (p q r : GrothPair) :
  groth_rel (groth_plus (groth_plus p q) r) (groth_plus p (groth_plus q r)).
Proof.
  destruct p as [a b], q as [c d], r as [e f].
  exists (cmon_zero M); apply pequiv_from; simpl.
  now rewrite !cmon_plus_assoc.
Qed.

Lemma groth_plus_comm (p q : GrothPair) :
  groth_rel (groth_plus p q) (groth_plus q p).
Proof.
  destruct p as [a b], q as [c d].
  exists (cmon_zero M); apply pequiv_from; simpl.
  now rewrite (cmon_plus_comm M a c), (cmon_plus_comm M b d).
Qed.

Lemma groth_plus_zero_l (p : GrothPair) :
  groth_rel (groth_plus groth_zero p) p.
Proof.
  destruct p as [a b].
  exists (cmon_zero M); apply pequiv_from; simpl.
  now rewrite !cmon_plus_zero_l.
Qed.

Lemma groth_neg_left (p : GrothPair) :
  groth_rel (groth_plus (groth_neg p) p) groth_zero.
Proof.
  destruct p as [a b].
  exists (cmon_zero M); apply pequiv_from; simpl.
  rewrite !cmon_plus_zero_r.
  rewrite cmon_plus_zero_l.
  apply cmon_plus_comm.
Qed.

Definition GrothCMon : CMonObject := {|
  cmon_setoid        := groth_setoid;
  cmon_zero          := groth_zero;
  cmon_plus          := groth_plus;
  cmon_plus_respects := groth_plus_respects;
  cmon_plus_assoc    := groth_plus_assoc;
  cmon_plus_comm     := groth_plus_comm;
  cmon_plus_zero_l   := groth_plus_zero_l;
  (* [groth_rel] IS a [Prop] relation, so it is its own [Prop] mirror. / [groth_rel] 是一个 [Prop] 关系，因此它是它自己的 [Prop] 镜像。 *)
  cmon_prop          :=
    @PropEquiv_of_relation _ (is_setoid groth_setoid) groth_rel
      (fun _ _ h => h) (fun _ _ h => h)
|}.

(*
 The completion.  [ab_neg] is the swap, so the object is abelian by
 construction -- the fact item (2) of the header's second-form
 discussion turns on. 

 --------
 完成。[ab_neg] 是交换操作，所以该对象根据构造是阿贝尔的——标题第二种形式讨论的事项 (2) 就在于此。
*)
Definition GrothendieckObject : AbObject := {|
  ab_cmon         := GrothCMon;
  ab_neg          := groth_neg;
  ab_neg_respects := groth_neg_respects;
  ab_neg_left     := groth_neg_left
|}.

(** *** The insertion / *** 插入 *)

Program Definition groth_insert :
  M ~{CMon}~> Ab_to_CMon GrothendieckObject := {|
  cmon_map := {| morphism := fun a : MC => (a, cmon_zero M) |}
|}.
Next Obligation.
  intros a b Hab; simpl; exists (cmon_zero M); apply pequiv_from; simpl.
  now rewrite Hab.
Qed.
Next Obligation. simpl; apply groth_rel_refl. Qed.
Next Obligation.
  intros a b; simpl; exists (cmon_zero M); apply pequiv_from; simpl.
  now rewrite !cmon_plus_zero_l, !cmon_plus_zero_r.
Qed.

(** *** The universal property / *** 泛性质 *)

Section Extend.

Context (A : AbObject).
Context (h : M ~{CMon}~> Ab_to_CMon A).

(* The mediator: a formal difference goes to an actual difference. / 调解者：形式差异转化为实际差异。 *)
Definition groth_med (p : GrothPair) : carrier (cmon_setoid A) :=
  ab_sub A (cmon_map h (fst p)) (cmon_map h (snd p)).

Lemma groth_med_respects : Proper (groth_rel ==> equiv) groth_med.
Proof.
  (*
 The conclusion is `≈` at [A], which is [Type]-valued, so the [Prop]
 relation may not be destructed into it directly; [pequiv_to] puts a
 [Prop] goal in front of the elimination and the branch returns to `≈`
 with [pequiv_from] once the witness is in hand. 

 --------
 结论是 `≈` 在 [A] ，它是 [Type] 值，因此 [Prop] 关系可能无法直接分解为它；[pequiv_to] 在消元之前提出了一个 [Prop] 目标，一旦获取到证据，分支就会带着 [pequiv_from] 返回到 `≈` 。
*)
  intros [a b] [c d] Hpq.
  apply (@pequiv_to _ _ (cmon_prop A)).
  destruct Hpq as [k Hk].
  apply pequiv_from.
  apply pequiv_to in Hk.
  unfold groth_med; simpl in *.
  (*
 Apply h to the relation, then cancel the image of the slack term.
 [ab_cancel_l] is applied with all three arguments explicit: with the
 last two left to unification it matches the wrong pair. 

 --------
 将 h 应用于该关系，然后消去松弛项的像。[ab_cancel_l] 以所有三个参数显式使用：将最后两个参数留给统一，它匹配错误的对。
*)
  assert (Hh : cmon_plus A
                 (cmon_plus A (cmon_map h a) (cmon_map h d))
                 (cmon_map h k)
               ≈ cmon_plus A
                   (cmon_plus A (cmon_map h c) (cmon_map h b))
                   (cmon_map h k)).
  { rewrite <- !(cmon_map_plus h).
    now rewrite Hk. }
  assert (Hcan : cmon_plus A (cmon_map h a) (cmon_map h d)
                 ≈ cmon_plus A (cmon_map h c) (cmon_map h b)).
  { apply (ab_cancel_l A (cmon_map h k)
             (cmon_plus A (cmon_map h a) (cmon_map h d))
             (cmon_plus A (cmon_map h c) (cmon_map h b))).
    rewrite (cmon_plus_comm A (cmon_map h k)
               (cmon_plus A (cmon_map h a) (cmon_map h d))).
    rewrite (cmon_plus_comm A (cmon_map h k)
               (cmon_plus A (cmon_map h c) (cmon_map h b))).
    exact Hh. }
  apply groth_sub_cross.
  exact Hcan.
Qed.

Program Definition groth_extend : GrothendieckObject ~{Ab}~> A := {|
  cmon_map := {| morphism := groth_med |}
|}.
Next Obligation. exact groth_med_respects. Qed.
Next Obligation.
  unfold groth_med; simpl.
  rewrite (cmon_map_zero h).
  apply ab_sub_self.
Qed.
Next Obligation.
  intros [a b] [c d]; unfold groth_med; simpl.
  rewrite !(cmon_map_plus h).
  symmetry; apply ab_sub_plus.
Qed.

(* The triangle: restricting the mediator to the insertion recovers h. / 三角形：将中介限制在插入处可以恢复 h。 *)
Lemma groth_extend_insert (a : MC) :
  cmon_map groth_extend (cmon_map groth_insert a) ≈ cmon_map h a.
Proof.
  simpl; unfold groth_med; simpl.
  rewrite (cmon_map_zero h).
  apply ab_sub_zero_r.
Qed.

(*
 Every pair is the difference of two inserted elements.  This is what
 forces the mediator, and it is [≈] and not [eq_refl]: the two pairs
 [(a, b)] and [(a + 0, 0 + b)] are genuinely different elements of the
 underlying type, related by the quotient relation. 

 --------
 每一对都是两个插入元素的差。这就是迫使调解者的原因，并且它是 [≈] 而不是 [eq_refl]：两对 [(a, b)] 和 [(a + 0, 0 + b)] 是底层类型真正不同的元素，通过商关系关联。
*)
Lemma groth_pair_is_difference (a b : MC) :
  groth_rel (a, b)
    (ab_sub GrothendieckObject
       (cmon_map groth_insert a) (cmon_map groth_insert b)).
Proof.
  unfold ab_sub; simpl.
  exists (cmon_zero M); apply pequiv_from; simpl.
  now rewrite !cmon_plus_zero_l, !cmon_plus_zero_r.
Qed.

Lemma groth_extend_unique (g : GrothendieckObject ~{Ab}~> A)
  (Hg : ∀ a : MC, cmon_map g (cmon_map groth_insert a) ≈ cmon_map h a)
  (p : GrothPair) :
  cmon_map g p ≈ cmon_map groth_extend p.
Proof.
  destruct p as [a b].
  rewrite (proper_morphism (cmon_map g) _ _
             (groth_pair_is_difference a b)).
  rewrite (ab_map_sub g).
  rewrite (Hg a), (Hg b).
  simpl; unfold groth_med; reflexivity.
Qed.

End Extend.

Arguments groth_med {A} h p.
Arguments groth_extend {A} h.
Arguments groth_extend_insert {A} h a.
Arguments groth_extend_unique {A} h g Hg p.

(*
 The universal mapping property in the shape [universal_arrow_from_UMP]
 wants: every [h : M ~> Ab_to_CMon A] factors uniquely through the
 insertion. 

 --------
 形状 [universal_arrow_from_UMP] 中的通用映射性质希望：每个 [h : M ~> Ab_to_CMon A] 都能唯一地通过插入进行分解。
*)
Lemma groth_universal (A : Ab) (h : M ~{CMon}~> Ab_to_CMon A) :
  ∃! g : GrothendieckObject ~{Ab}~> A,
    h ≈ fmap[Ab_to_CMon] g ∘ groth_insert.
Proof.
  unshelve eexists.
  - exact (groth_extend h).
  - intro a; simpl; symmetry; exact (groth_extend_insert h a).
  - intros g Hg p; simpl.
    symmetry; apply (groth_extend_unique h g).
    intro a; symmetry; exact (Hg a).
Qed.

End Grothendieck.

(* The in-section [Arguments] above are not preserved across [End], which prepends [M] to every signature, so they are re-issued here. / 上面节中的 [Arguments] 在 [End] 中未被保留，[End] 会在每个签名前添加 [M]，因此它们在这里重新发布。 *)
Arguments groth_med {M A} h p.
Arguments groth_extend {M A} h.
Arguments groth_extend_insert {M A} h a.
Arguments groth_extend_unique {M A} h g Hg p.

Arguments GrothPair M : clear implicits.
Arguments groth_rel {M} p q.
Arguments groth_naive {M} p q.
Arguments groth_zero M : clear implicits.
Arguments groth_plus {M} p q.
Arguments groth_neg {M} p.

(** ** Strict readings of the data / ** 数据的严格解读 *)

Example groth_carrier (M : CMonObject) :
  carrier (cmon_setoid (GrothendieckObject M))
    = (carrier (cmon_setoid M) * carrier (cmon_setoid M))%type := eq_refl.

Example groth_zero_computes (M : CMonObject) :
  cmon_zero (GrothendieckObject M) = (cmon_zero M, cmon_zero M) := eq_refl.

Example groth_plus_computes (M : CMonObject)
  (a b c d : carrier (cmon_setoid M)) :
  cmon_plus (GrothendieckObject M) (a, b) (c, d)
    = (cmon_plus M a c, cmon_plus M b d) := eq_refl.

Example groth_neg_computes (M : CMonObject)
  (a b : carrier (cmon_setoid M)) :
  ab_neg (GrothendieckObject M) (a, b) = (b, a) := eq_refl.

Example groth_insert_computes (M : CMonObject)
  (a : carrier (cmon_setoid M)) :
  cmon_map (groth_insert M) a = (a, cmon_zero M) := eq_refl.

Example groth_extend_computes (M : CMonObject) (A : AbObject)
  (h : M ~{CMon}~> Ab_to_CMon A) (a b : carrier (cmon_setoid M)) :
  cmon_map (groth_extend h) (a, b)
    = ab_sub A (cmon_map h a) (cmon_map h b) := eq_refl.

(* * ** The universal arrow, the left adjoint and the adjunction / * ** 普遍箭头、左伴随和伴随 *)

Definition groth_universal_arrow (M : CMon)
  : UniversalArrow M Ab_to_CMon :=
  universal_arrow_from_UMP M Ab_to_CMon (GrothendieckObject M)
    (groth_insert M) (groth_universal M).

(*
 The same content in the direct encoding, where the universal object is
 named rather than projected out of a comma category. 

 --------
 直接编码中的相同内容，其中通用对象被命名，而不是从逗号类型中投射出来。
*)
Program Definition groth_AUniversalArrow (M : CMon)
  : AUniversalArrow M Ab_to_CMon (GrothendieckObject M) := {|
  universal_arrow := groth_insert M
|}.
Next Obligation.
  intros M A h.
  unshelve eexists.
  - exact (groth_extend h).
  - intro a; simpl; exact (groth_extend_insert h a).
  - intros g Hg p; simpl.
    (* [AUniversalArrow]'s uniqueness field is oriented the other way round from the comma-packaged one, hence the [symmetry]. / [AUniversalArrow] 的唯一性字段的方向与逗号包装的那个相反，因此是 [symmetry]。 *)
    symmetry; apply (groth_extend_unique h g).
    intro a; exact (Hg a).
Qed.

(*
 The functor and the adjunction come out of the generic machinery with
 no further proof. 

 --------
 函子和伴随由通用机制得出，无需进一步证明。
*)
Definition GrothLeft : CMon ⟶ Ab :=
  LeftAdjointFunctorFromUniversalArrows Ab_to_CMon groth_universal_arrow.

Definition grothendieck_adjunction : GrothLeft ⊣ Ab_to_CMon :=
  AdjunctionFromUniversalArrows Ab_to_CMon groth_universal_arrow.

Example GrothLeft_obj (M : CMon) :
  GrothLeft M = GrothendieckObject M := eq_refl.

(*
 [universal_arrow_from_UMP] stores the supplied morphism as the second
 projection of the comma object it builds, so the universal arrow is
 the insertion on the nose. 

 --------
 [universal_arrow_from_UMP] 将提供的态射存储为它所构建的逗号对象的第二投影，因此普遍箭头就是精确的插入。
*)
Example groth_arrow_is_insert (M : CMon) :
  @arrow _ _ M Ab_to_CMon (groth_universal_arrow M) = groth_insert M
  := eq_refl.

(* * ** The unit computes; the counit does not / * ** 单位运算；余单位不运算 *)

Definition groth_unit (M : CMon)
  : M ~{CMon}~> Ab_to_CMon (GrothLeft M) :=
  @Category.Theory.Adjunction.unit _ _ _ _ grothendieck_adjunction M.

Example groth_unit_is_insert (M : CMon) (a : carrier (cmon_setoid M)) :
  cmon_map (groth_unit M) a = (a, cmon_zero M) := eq_refl.

Definition groth_counit (A : Ab)
  : GrothLeft (Ab_to_CMon A) ~{Ab}~> A :=
  @Category.Theory.Adjunction.counit _ _ _ _ grothendieck_adjunction A.

(* The counit routes through the [Qed]-opaque [ump_universal_arrows], so no [eq_refl] is available and none is claimed. What holds is that it is the difference map. / 余单位通过 [Qed] -不透明的 [ump_universal_arrows] 路由，因此没有 [eq_refl] 可用，也没有被声明。成立的情况是它是差映射。 *)
Lemma groth_counit_generator (A : Ab)
  (a : carrier (cmon_setoid (Ab_to_CMon A))) :
  cmon_map (groth_counit A) (a, cmon_zero A) ≈ a.
Proof.
  exact (@to_adj_counit _ _ _ _ grothendieck_adjunction A a).
Qed.

Theorem groth_counit_evaluates (A : Ab)
  (p : GrothPair (Ab_to_CMon A)) :
  cmon_map (groth_counit A) p
    ≈ ab_sub A (fst p) (snd p).
Proof.
  destruct p as [a b].
  transitivity (cmon_map (groth_extend (@id CMon (Ab_to_CMon A)))
                  (a, b)).
  - apply (groth_extend_unique (@id CMon (Ab_to_CMon A))
             (groth_counit A)).
    intro x; exact (groth_counit_generator A x).
  - simpl; reflexivity.
Qed.

(*
   * ** The completion as a functor, built directly

   [LeftAdjointFunctorFromUniversalArrows] defines its arrow action by
   universal factorization, so [fmap[GrothLeft]] does not compute.  The
   componentwise action does, and it is obviously a homomorphism, so the
   functor is built directly and then RELATED to the produced one rather
   than silently substituted for it. 

   --------
   * ** 完成作为函子，直接构建

   [LeftAdjointFunctorFromUniversalArrows] 通过普适分解定义其箭头作用，因此 [fmap[GrothLeft] ] 不会被计算。分量作用可以计算，并且它显然是一个同态，所以函子是直接构建的，然后与产生的函子相关联，而不是默默地替代它。
*)

Program Definition groth_map {M N : CMonObject} (f : M ~{CMon}~> N)
  : GrothendieckObject M ~{Ab}~> GrothendieckObject N := {|
  cmon_map := {| morphism := fun p : GrothPair M =>
                   (cmon_map f (fst p), cmon_map f (snd p)) |}
|}.
Next Obligation.
  intros M N f [a b] [c d] Hpq; simpl in Hpq |- *.
  destruct Hpq as [k Hk]; apply pequiv_to in Hk; simpl in Hk.
  exists (cmon_map f k); apply pequiv_from; simpl.
  rewrite <- !(cmon_map_plus f).
  now rewrite Hk.
Qed.
Next Obligation.
  intros M N f; simpl.
  exists (cmon_zero N); apply pequiv_from; simpl.
  now rewrite !(cmon_map_zero f).
Qed.
Next Obligation.
  intros M N f [a b] [c d]; simpl.
  exists (cmon_zero N); apply pequiv_from; simpl.
  now rewrite !(cmon_map_plus f).
Qed.

Program Definition GrothendieckFunctor : CMon ⟶ Ab := {|
  fobj := GrothendieckObject;
  fmap := @groth_map
|}.
Next Obligation.
  intros M N f g Hfg [a b]; simpl.
  exists (cmon_zero N); apply pequiv_from; simpl.
  now rewrite (Hfg a), (Hfg b).
Qed.
Next Obligation.
  intros M [a b]; simpl.
  exists (cmon_zero M); apply pequiv_from; simpl; reflexivity.
Qed.
Next Obligation.
  intros M N P f g [a b]; simpl.
  exists (cmon_zero P); apply pequiv_from; simpl; reflexivity.
Qed.

Example groth_functor_obj_agrees (M : CMon) :
  fobj[GrothendieckFunctor] M = fobj[GrothLeft] M := eq_refl.

Example groth_map_computes {M N : CMonObject} (f : M ~{CMon}~> N)
  (a b : carrier (cmon_setoid M)) :
  cmon_map (groth_map f) (a, b) = (cmon_map f a, cmon_map f b) := eq_refl.

(* The arrow actions agree up to [≈]. They cannot agree strictly: [fmap[GrothLeft]] is [unique_obj (ump_universal_arrows …)] and [ump_universal_arrows] is [Qed]. / 箭头动作在 [≈] 之前是一致的。它们不能严格一致： [fmap[GrothLeft] ] 是 [unique_obj (ump_universal_arrows …)] 并且 [ump_universal_arrows] 是 [Qed]。 *)
Lemma groth_fmap_agrees {M N : CMon} (f : M ~{CMon}~> N) :
  fmap[GrothLeft] f ≈ fmap[GrothendieckFunctor] f.
Proof.
  (*
 [fmap[GrothLeft]] is [unique_obj] of the very factorization problem
 [groth_map f] solves, so [uniqueness] applies directly; the property
 to discharge is that [groth_map] commutes with the insertions. 

 --------
 [fmap[GrothLeft] 是 [unique_obj] 所解决的非常因式分解问题 [groth_map f] 的，因此 [uniqueness] 可以直接应用；需要解除的性质是 [groth_map] 与插入操作可交换。
*)
  apply (uniqueness (ump_universal_arrows (groth_universal_arrow M)
           (@arrow _ _ N Ab_to_CMon (groth_universal_arrow N) ∘ f))).
  intro a; simpl.
  exists (cmon_zero N); apply pequiv_from; simpl.
  now rewrite (cmon_map_zero f).
Qed.

(*
   * ** Measured negatives

   Three strict identifications the header claims are unavailable, pinned
   as [Fail] probes rather than merely asserted.  Each was stripped once
   and confirmed to be a genuine “cannot unify”, and each has a positive
   control above that must succeed: [groth_unit_is_insert] for the first,
   [groth_functor_obj_agrees] and [groth_map_computes] for the second,
   [groth_pair_is_difference] for the third.  The instrument check at the
   end uses a scope-free proposition. 

   --------
   * ** 测量负样本

   头部声明的三个严格识别被标记为 [Fail] 探针，而不仅仅是断言。每一个都被剥离一次，并确认是真正的“无法统一”，每一个上面都有一个必须成功的阳性对照：第一个为 [groth_unit_is_insert]，第二个为 [groth_functor_obj_agrees] 和 [groth_map_computes]，第三个为 [groth_pair_is_difference]。最后的仪器检查使用了一个无范围的命题。
*)

(*
 NEGATIVE 1 (conversion).  The counit does not compute.  Its value is
 [unique_obj (ump_universal_arrows …)] and [ump_universal_arrows] is
 [Qed], so nothing reduces through it.  This DISCRIMINATES: the unit of
 the same adjunction does close by [eq_refl] ([groth_unit_is_insert]),
 so the obstruction is that one constant's opacity and not the
 adjunction packaging. 

 --------
 负 1（转换）。余单位无法计算。它的值是 [unique_obj (ump_universal_arrows …)]，而 [ump_universal_arrows] 是 [Qed]，因此没有任何东西可以通过它化简。这区分了：同一个伴随的单位通过 [eq_refl]（[groth_unit_is_insert]）可以闭合，所以障碍在于某个常量的不透明性，而不是伴随的封装。
*)
Fail Example groth_counit_not_strict (A : Ab)
  (a : carrier (cmon_setoid (Ab_to_CMon A))) :
  cmon_map (groth_counit A) (a, cmon_zero A) = a := eq_refl.

(*
 NEGATIVE 2 (conversion).  The two functors' ARROW actions are not
 convertible, for the same reason:
 [LeftAdjointFunctorFromUniversalArrows] defines [fmap] by universal
 factorization.  Their OBJECT actions do agree strictly
 ([groth_functor_obj_agrees]), which is what makes this a statement
 about the arrow action specifically. 

 --------
 负 2（转换）。两个函子在箭头上的作用不可转换，原因相同：[LeftAdjointFunctorFromUniversalArrows] 通过普遍分解定义了 [fmap]。它们在对象上的作用确实严格一致（[groth_functor_obj_agrees]），这正说明这是关于箭头作用的陈述。
*)
Fail Example groth_fmap_not_strict (M N : CMon) (f : M ~{CMon}~> N) :
  fmap[GrothLeft] f = fmap[GrothendieckFunctor] f := eq_refl.

(*
 NEGATIVE 3 (conversion).  A pair is only [≈]-equal to the difference of
 the two inserted elements, never convertible to it: the completion is a
 QUOTIENT, and [(a, b)] against [(a + 0, 0 + b)] is exactly the slack the
 relation absorbs.  [groth_pair_is_difference] is the [≈] statement. 

 --------
 负 3（转换）。一对仅仅等于两个插入元素的差，永远无法转换成它：完成的是一个商，而对比 [(a, b)] 和 [(a + 0, 0 + b)] 正好是该关系吸收的松弛。[groth_pair_is_difference] 是 [≈] 的声明。
*)
Fail Example groth_difference_not_strict (M : CMonObject)
  (a b : carrier (cmon_setoid M)) :
  (a, b) = ab_sub (GrothendieckObject M)
             (cmon_map (groth_insert M) a) (cmon_map (groth_insert M) b)
  := eq_refl.

(* Instrument check: the [Fail]s above are firing on conversion, not on a dead command. / 仪器检查：上述 [Fail] 是在转换时发射的，而不是在一个无效指令上发射的。 *)
Fail Example groth_instrument_check : true = false := eq_refl.

(*
   * ** The slack term is necessary

   Over the booleans under disjunction -- [rig_cmon Bool_Rig], the
   additive half of Theory/Algebra/Rig.v's Example 5.38 -- the
   slack-free relation is not transitive.  The three pairs below are
   concrete and the refutation is by [discriminate]. 

   --------
   * ** 松弛项是必要的

   在析取下的布尔值之上 -- [rig_cmon Bool_Rig]，
   Theory/Algebra/Rig.v 的示例 5.38 的加法部分 -- 
   无松弛的关系不是传递的。下面的三个对是具体的，反驳是通过 [discriminate] 进行的。
*)

Definition groth_bool : CMonObject := rig_cmon Bool_Rig.

Theorem groth_naive_not_transitive :
  (∀ p q r : GrothPair groth_bool,
      @groth_naive groth_bool p q → @groth_naive groth_bool q r →
      @groth_naive groth_bool p r) → False.
Proof.
  intro Htrans.
  assert (H1 : @groth_naive groth_bool (false, false) (true, true)).
  { unfold groth_naive; simpl; reflexivity. }
  assert (H2 : @groth_naive groth_bool (true, true) (true, false)).
  { unfold groth_naive; simpl; reflexivity. }
  pose proof (Htrans _ _ _ H1 H2) as H3.
  unfold groth_naive in H3; simpl in H3.
  discriminate H3.
Qed.

(*
 And the price: with the slack term, the completion of that monoid is
 trivial -- every two pairs are related, by taking [k := true]. 

 --------
 价格：在松弛项下，该幺半群的完备是显而易见的——每两个对都是相关的，通过取 [k := true]。
*)
Theorem groth_bool_trivial (p q : GrothPair groth_bool) :
  @groth_rel groth_bool p q.
Proof.
  destruct p as [a b], q as [c d].
  exists true; apply pequiv_from; simpl.
  now rewrite !Bool.orb_true_r.
Qed.

Theorem groth_bool_insert_collapses :
  cmon_map (groth_insert groth_bool) true
    ≈ cmon_map (groth_insert groth_bool) false.
Proof. apply groth_bool_trivial. Qed.

(* * ** K(ℕ, +) ≅ ℤ The motivating example. [groth_nat] is the additive half of Theory/Algebra/Rig.v's [Nat_Rig]; [ab_Z] is Instance/Ab/Coproduct.v's ℤ, reused rather than redeclared. / * ** K(ℕ, +) ≅ ℤ 激励示例。[groth_nat] 是 Theory/Algebra/Rig.v 的 [Nat_Rig] 的加法部分；[ab_Z] 是 Instance/Ab/Coproduct.v 的 ℤ，重复使用而不是重新声明。 *)

Definition groth_nat : CMonObject := rig_cmon Nat_Rig.

(*
 The truncation identity that drives everything below: for every
 integer, the difference of the two truncations is the integer. 

 --------
 推动下面所有内容的截断恒等式：对于每一个整数，两个截断的差等于该整数。
*)
Lemma groth_Z_split (x : Z) :
  (Z.of_nat (Z.to_nat x) - Z.of_nat (Z.to_nat (- x)))%Z = x.
Proof.
  destruct x as [| p | p]; simpl.
  - reflexivity.
  - rewrite positive_nat_Z; lia.
  - rewrite positive_nat_Z; lia.
Qed.

Program Definition nat_to_Z : groth_nat ~{CMon}~> Ab_to_CMon ab_Z := {|
  cmon_map := {| morphism := fun n : nat => Z.of_nat n |}
|}.
(*
 Only TWO obligations: instance resolution closes [proper_morphism]
 during elaboration, both setoids here being Leibniz.  That is the
 hazard Instance/Sets/Products.v records and
 Structure/Limit/Power.v reports a second sighting of; this is a third.
 It is harmless at THESE two witnesses -- their carriers are [nat] and
 [Z], so nothing is pinned that was not already concrete -- and the
 general definitions above are unaffected, [groth_insert] raising all
 three obligations because its setoids are abstract. 

 --------
 只有两个义务：在推导过程中，实例解析关闭 [proper_morphism] ，这里的两个集合同构都是莱布尼兹集合。这就是 Instance/Sets/Products.v 记录的风险，以及 Structure/Limit/Power.v 报告的第二次出现；这是第三次。对于这两个见证者来说是无害的——它们的载体是 [nat] 和 [Z]，因此没有固定任何之前未具体化的内容——上述一般定义不受影响，[groth_insert] 提出所有三个义务，因为它的集合同构是抽象的。
*)
Next Obligation. reflexivity. Qed.
Next Obligation. intros a b; simpl; apply Nat2Z.inj_add. Qed.

Definition groth_nat_to_Z
  : GrothendieckObject groth_nat ~{Ab}~> ab_Z :=
  groth_extend nat_to_Z.

Program Definition groth_Z_to_nat
  : ab_Z ~{Ab}~> GrothendieckObject groth_nat := {|
  cmon_map := {| morphism := fun n : Z => (Z.to_nat n, Z.to_nat (- n)) |}
|}.
(* Two obligations again, for the same reason as [nat_to_Z]. / 再次有两个义务，原因与[nat_to_Z]相同。 *)
Next Obligation. simpl; apply groth_rel_refl. Qed.
Next Obligation.
  intros m n; simpl.
  exists 0%nat; simpl.
  apply Nat2Z.inj.
  rewrite !Nat2Z.inj_add.
  pose proof (groth_Z_split m) as Hm.
  pose proof (groth_Z_split n) as Hn.
  pose proof (groth_Z_split (m + n)%Z) as Hmn.
  simpl; lia.
Qed.

(*
 The ℕ-level identity behind the section: stated separately so that the
 isomorphism below closes by conversion rather than by hoping [simpl]
 exposes the right term. 

 --------
 本节背后的 ℕ 级别同一性：单独陈述，以便下面的同构通过转换而非寄希望于 [simpl] 暴露正确项来闭合。
*)
Lemma groth_Z_to_nat_section (a b : nat) :
  (Z.to_nat (Z.of_nat a - Z.of_nat b) + b + 0
     = a + Z.to_nat (- (Z.of_nat a - Z.of_nat b)) + 0)%nat.
Proof.
  rewrite !Nat.add_0_r.
  apply Nat2Z.inj.
  rewrite !Nat2Z.inj_add.
  pose proof (groth_Z_split (Z.of_nat a - Z.of_nat b)%Z) as Hs.
  lia.
Qed.

Theorem groth_nat_Z_iso : GrothendieckObject groth_nat ≅[Ab] ab_Z.
Proof.
  unshelve eexists.
  - exact groth_nat_to_Z.
  - exact groth_Z_to_nat.
  - intro n; simpl; unfold groth_med, ab_sub; simpl.
    pose proof (groth_Z_split n) as Hn.
    unfold Z_eqT; lia.
  - intros [a b]; simpl.
    exists 0%nat.
    apply pequiv_from.
    exact (groth_Z_to_nat_section a b).
Qed.

(* * ** Non-vacuity on the cancellative side / * ** 在可消去一侧的非空性 *)

(*
 ℕ is cancellative, so the slack term buys nothing there and the
 insertion is injective -- the completion does NOT collapse. 

 --------
 ℕ 是可抵消的，所以松弛项在那里没有作用，并且插入是单射的 —— 完成不会塌缩。
*)
Theorem groth_nat_insert_injective (a b : nat) :
  cmon_map (groth_insert groth_nat) a
    ≈ cmon_map (groth_insert groth_nat) b → a = b.
Proof.
  intros [k Hk]; apply pequiv_to in Hk; simpl in Hk.
  lia.
Qed.

Theorem groth_nat_nontrivial :
  cmon_map (groth_insert groth_nat) 0%nat
    ≈ cmon_map (groth_insert groth_nat) 1%nat → False.
Proof.
  intro H.
  pose proof (groth_nat_insert_injective 0 1 H) as Heq.
  discriminate Heq.
Qed.

(* Mapping OUT: the completion of ℕ separates a negative from a positive formal difference, because ℤ does. / 映射 OUT：ℕ 的完备性将负数与正数的形式差分开，因为 ℤ 会这样做。 *)
Example groth_nat_to_Z_computes (a b : nat) :
  cmon_map groth_nat_to_Z (a, b)
    = (Z.of_nat a - Z.of_nat b)%Z := eq_refl.

Theorem groth_nat_sign_separates :
  @groth_rel groth_nat (0%nat, 1%nat) (1%nat, 0%nat) → False.
Proof.
  intro H.
  pose proof (proper_morphism (cmon_map groth_nat_to_Z) _ _ H) as HZ.
  unfold Z_eqT in HZ; simpl in HZ.
  discriminate HZ.
Qed.
