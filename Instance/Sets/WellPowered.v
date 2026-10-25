Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.WellPowered.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.QuotObj.
Require Import Category.Instance.Sets.SubobjectLattice.
Require Import Category.Instance.Sets.Classifier.OneLevel.

Generalizable All Variables.

(* * * Sets is well-powered and co-well-powered, and at which universe / * * 集合是良有势且余良有势的，并且在哪个宇宙 *)

(*
 nLab:      https://ncatlab.org/nlab/show/well-powered+category
 nLab:      https://ncatlab.org/nlab/show/subobject
 Wikipedia: https://en.wikipedia.org/wiki/Subobject

 Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
 §V.8, book p. 130 (PDF p. 139), calls a category well-powered when the
 subobjects of each object form a small set and co-well-powered when the
 quotient objects do.  Classically [Sets] is both: the subobjects of a
 set are its subsets, named by characteristic functions, and its quotient
 objects are named by kernel relations.  mathlib's
 [CategoryTheory.WellPowered] asks that [Subobject X] be [w]-small and
 names [w] = the hom universe as the common case.
 Structure/WellPowered.v carries the definitions: the per-object record
 [WellPoweredAt x] (a small index [wp_index], maps [wp_to] and [wp_from]
 both ways, and the exhaustiveness clause [wp_to_from]), and [WellPowered],
 which PINS the index at or below the hom universe.  This file is the
 [Sets] half of the witnesses; the [Grp] one is Instance/Grp/WellPowered.v.

 WHAT IS BUILT.

 (1) [Sets] is well-powered ONE UNIVERSE UP, with nothing assumed:
 [Sets_WellPoweredAt_up X] at every setoid [X].  The index is
 [sets_pred_index X], the ≈-respecting [Type@{o}]-valued predicates on the
 carrier.  [wp_to] sends a predicate to the sub-setoid of the elements
 satisfying it, included by the first projection; [wp_from] sends a
 subobject to "has a preimage", [fun b => { a & sub_mono u a ≈ b }], with
 the preimage carried as DATA.  The domain isomorphism of [wp_to_from]
 projects that preimage, and it respects ≈ because the mono is injective
 (Instance/Sets.v's [injectivity_is_monic]).  Readback, by [eq_refl]:
 the subobject a predicate names has [{ a : carrier X & `1 P a }] as its
 carrier ([Sets_WellPoweredAt_up_carrier]).

 (2) [Sets] is co-well-powered ONE UNIVERSE UP, with nothing assumed:
 [Sets_CoWellPoweredAt_up X], a [WellPoweredAt] in [Sets^op], whose
 subobjects are Theory/Subobject/Quotient.v's [QuotObj] on the nose.  The
 index is [sets_rel_index X], the [Type@{o}]-valued equivalence relations
 coarser than ≈.  Everything is Instance/Sets/QuotObj.v's: [wp_to] is
 [SetsQuotient_QuotObj], [wp_from] is the kernel relation
 [sets_coimage_rel] of a quotient's epi, and the codomain isomorphism uses
 the preimage [Sets_quot_epi_surjective] returns -- data, because [∃] is
 [sigT] in this library.  [wp_to_from] is closed through
 [quot_equiv_iff_iso], the covariant reading of ≈ on quotient objects.

 (3) [Sets] is well-powered AT THE PIN under [Untruncate]:
 [Sets_WellPowered_untruncate : Untruncate@{o} → WellPowered Sets@{o so}].
 The index at [X] is the hom-set [X ~> Ω] of Instance/Sets/Classifier/
 OneLevel.v's conditional classifier, and it reads back by [eq_refl] as
 [X ~{Sets}~> Powerset_Omega] ([Sets_WellPoweredAt_untruncate_index]):
 Prop-valued predicates, at the carrier universe [o].  The witness IS
 Structure/WellPowered.v's generic [wp_of_classifier], applied to
 [Sets_Classifier U] over Instance/Sets/Pullback.v's [Sets_HasPullbacks]:
 [wp_to] pulls the truth subobject back along a predicate, [wp_from] is
 [char], and [wp_to_from] is Structure/SubobjectClassifier.v's
 [classifier_pullback_roundtrip], which OneLevel.v's
 [sets_pullback_roundtrip] restates at [Sets].  [untruncate_of_IEM]
 (OneLevel.v) makes this hold under informative excluded middle as
 well.
 [Untruncate@{o} := ∀ P : Type@{o}, Powerset_squash P → P] is a
 HYPOTHESIS, not an axiom: nothing is declared, and Instance/Fun/Topos.v's
 header records that it has no in-tree inhabitant and that no
 impossibility of it is proved.

 (4) The §V.8 consequence at [Sets], under the same hypothesis:
 [Sets_wellpowered_intersection U X P HP] is an [IsIntersection] (Theory/
 Subobject/Lattice.v) of the LARGE family [{ m : SubObj X & P m }], for
 any ≈-closed [Type@{o}]-valued property [P] of subobjects.  It is stated
 directly against Instance/Sets/SubobjectLattice.v's
 [Sets_HasWidePullbacks] and Lattice.v's [sub_intersection]: the wide
 pullback is taken over the SMALL index [{ i : X ~> Ω & P (wp_to i) }],
 padded with [sub_top] so that [sub_intersection]'s chosen point [None]
 always exists; the lower bound transports [P] along [wp_to_from], and
 maximality holds because the small family is a subfamily of the large
 one.  [Sets_intersection_all_empty] reads it back at [P := unit], the
 class of ALL subobjects: the intersection has an empty carrier, because
 the empty subobject [sets_sub_bot] (Instance/Sets/SubobjectLattice.v's
 [Sets_zero_monic]) is a member.

 WHY THE PINNED WITNESS USES [Untruncate]: the routes without it,
 refused.  Each refusal below was taken by appending the one command to
 a copy of this whole file and compiling it; each has an accepted
 control beside it.  They refuse particular constructions; no
 impossibility is proved (see NOT DELIVERED).

 - The index of (1) sits at [o+1] and the pin asks for [o].  Offering
 [Sets_WellPoweredAt_up X] where [WellPowered@{so o o so so}
 Sets@{o so}] is expected is refused: "The term
 "Sets_WellPoweredAt_up X" has type "WellPoweredAt@{R1.2118 R1.2117
 R1.2117 o R1.2118} X" while it is expected to have type
 "WellPoweredAt@{o so so o so} X" (universe inconsistency: Cannot
 enforce o = so because o < so)".  Control: the same witness at
 [Sets_WellPoweredAt_up@{o so so}] is accepted.
 - A [Prop]-valued index sits at [o], but it cannot rebuild the domain
 of the subobject it names: the backward map needs an ELEMENT out of
 a truncated preimage.  With [inhabited]: "Incorrect elimination of
 "proj2_sig p" in the inductive type "inhabited": the return type
 has sort "Type" while it should be SProp or Prop."  With the
 impredicative [Powerset_squash] the classifier uses: "The term "q"
 has type "∃ a : A, m a ≈ b" while it is expected to have type "?Q"
 (unable to find a well-typed instantiation for "?Q": cannot ensure
 that "Type" is a subtype of "Prop")".  Inverting exactly that
 truncation is what [Untruncate] does, and it is spent once, in
 OneLevel.v's [sce_elim].  [PropEquiv] (Lib/Setoid/Propositional.v)
 does not help: it recovers a Type-valued ≈ from a Prop one, not an
 element from an existential.
 - The consequence (4) over the index of (1) is refused where the
 pinned index is accepted: [sub_intersection] at
 [Sets_HasWidePullbacks] with the family indexed by
 [option { i : wp_index (Sets_WellPoweredAt_up X) & … }] gives
 "unable to find a well-typed instantiation for "?A": cannot ensure
 that "Type@{max(o,R3.2141)}" is a subtype of "Type@{R3.2125}"",
 and the same term over [Sets_WellPoweredAt_untruncate U X] compiles.
 The wide-pullback index of [Sets] is the carrier universe; the
 well-powered index has to fit under it, which is the pin.

 STRENGTHS.  Every comparison of subobjects and quotient objects is ≈
 (an isomorphism of domains, resp. codomains, over [X]); there is no
 Leibniz uniqueness anywhere.  The two [eq_refl] readbacks are the
 carrier of a predicate's subobject and the index of the pinned witness.

 UNIVERSES, measured with [Set Printing Universes. About …] (stdlib
 bounds such as [Projections.u0] left out):

 sets_pred_index@{o so}  : SetoidObject@{o o} → Type@{o+1}
 sets_rel_index@{o so}   : SetoidObject@{o o} → Type@{o+1}
 Sets_WellPoweredAt_up@{o so u}   : ∀ X, WellPoweredAt@{u so so o u} X
 ( * o < so, o < u * )
 Sets_CoWellPoweredAt_up@{o so u} : ∀ X, WellPoweredAt@{u so so o u} X
 ( * in Sets^op; o < so, o < u * )
 Sets_WellPoweredAt_untruncate@{o so u} :
 Untruncate@{o} → ∀ X, WellPoweredAt@{o so so o u} X
 ( * Set < o, o < so, o < u * )
 Sets_WellPowered_untruncate@{o so t} :
 Untruncate@{o} → WellPowered@{so o o so t} Sets@{o so}
 ( * Set < o, o < so, o < t * )
 Sets_wellpowered_intersection@{o so u u0} : Untruncate@{o} → …
 IsIntersection@{so o so} (λ k : ∃ m : SubObj@{so o} X, P m, `1 k) w
 ( * Set < o, o < so, o < u, o < u0 * )

 [WellPoweredAt]'s first slot is the index universe and its fourth the
 hom universe, so (1) and (2) have the index strictly above the homs and
 (3) has it equal to them.  [Set < o] in (3) and (4) comes from
 [Powerset_Omega]'s [Prop]-valued carrier; (1) and (2) carry no [Set]
 bound.  The first setoid slot [s] of the pinned witness is [so], where
 minimization put it inside the section: a top-level binder that names
 it apart gets "so = s" added back under [+].  The second, [t], is free
 above the homs, and [Sets_WellPowered_untruncate] names it.

 MEASUREMENTS.  27 constants ([.glob] heads matched by
 '^(def|prf|thm|ind|constr|proj|rec) ') and no [Program] obligation
 ([strings] on the .vo finds no [_obligation_] name); every one reports
 "Closed under the global context" under [Print Assumptions] by its
 fully qualified name.  13 [Defined] and 2 [Qed].  Flipping each
 [Defined] to [Qed] in a copy of the whole file, ten are load-bearing
 -- a later proof or readback reads their components back -- and three
 recompile green: [sets_pred_to_from], [sets_rel_to_from] and
 [Sets_wellpowered_intersection], kept transparent because ≈ on
 subobjects is an isomorphism and an intersection is an object, both
 data.  [sets_rel_of_quot] is built in tactic form rather than as an
 anonymous pair, and the two [eq_refl] readbacks sit outside the
 sections with no universe binder: both are Coq 8.19/8.20 precautions
 (the anonymous-pair trap recorded in Instance/Grp/Quotient.v's
 comment on [SubgroupGrp], and Theory/Size.v's note on [ObjEq]), taken
 before those toolchains were run; whether either is needed there was
 not measured.

 NOT DELIVERED.  [Sets] well-powered at the pin UNCONDITIONALLY: no
 construction is given and no impossibility is proved.  [Sets]
 co-well-powered at the pin, even under [Untruncate]: not attempted.  No
 witness at [Sets@{Set _}] for (3) or (4) ([Set < o] above).  The generic
 consequence over an arbitrary complete category is Structure/
 WellPowered.v's business, not this file's; (4) is its [Sets] instance
 stated directly over the wide pullbacks [Sets] already has.  No
 [Instance] is registered.  [Ab], [RMod R] and the other algebraic
 categories are not attempted here. 

 --------
 nLab：       https://ncatlab.org/nlab/show/well-powered+category
 nLab：       https://ncatlab.org/nlab/show/subobject
 维基百科：  https://en.wikipedia.org/wiki/SubobjectMac Lane，《Categories for the Working Mathematician》，第2版 (GTM 5)，§V.8，第130页（PDF第139页），称当每个对象的子对象形成一个小集合时，一个范畴是良功的（well-powered），而当商对象形成一个小集合时，是余良功的（co-well-powered）。经典上，[Sets] 两者都是：一个集合的子对象是它的子集，由特征函数命名，其商对象由核关系命名。mathlib 的 [CategoryTheory.WellPowered] 要求 [Subobject X] 是 [w]-小的，并将 [w] = 同态宇宙作为常见情况命名。Structure/WellPowered.v 包含定义：每个对象的记录 [WellPoweredAt x]（一个小索引 [wp_index]，映射 [wp_to] 和 [wp_from] 双向，以及穷尽性条款 [wp_to_from]），以及 [WellPowered]，将索引固定在或低于同态宇宙。这个文件是见证者的一半 [Sets]；另一半 [Grp] 在 Instance/Grp/WellPowered.v。

 构建的内容。

 (1) [Sets] 是在一个宇宙上升的良有幂的，没有假设任何东西：
 [Sets_WellPoweredAt_up X] 在每个集合等价类 [X] 上。索引是 [sets_pred_index X]，≈-保持的 [Type@{o}] 值谓词在载体上。
 [wp_to] 将谓词发送到满足它的子集合等价类，由第一投影包含；[wp_from] 将子对象发送到“有原像”，[fun b => { a & sub_mono u a ≈ b }]，原像作为数据携带。[wp_to_from] 的域同构投影该原像，并且它保持 ≈ 因为单态映射是单射（Instance/Sets.v 的 [injectivity_is_monic]）。通过 [eq_refl] 回读：谓词命名的子对象其载体为 [{ a : carrier X & `1 P a }] ([Sets_WellPoweredAt_up_carrier])。(2) [Sets] 是共良幂 ONE UNIVERSE UP，没有假设：[Sets_CoWellPoweredAt_up X]，是 [Sets^op] 中的 [WellPoweredAt]，其子对象恰好是 Theory/Subobject/Quotient.v 的 [QuotObj]。索引是 [sets_rel_index X]，值为 [Type@{o}] 的比 ≈ 粗的等价关系。一切都是 Instance/Sets/QuotObj.v 的：[wp_to] 是 [SetsQuotient_QuotObj]，[wp_from] 是商映射的核关系 [sets_coimage_rel]，并且值域同构使用前像 [Sets_quot_epi_surjective] 返回的数据，因为 [∃] 是该库中的 [sigT]。[wp_to_from] 在 [quot_equiv_iff_iso] 上封闭，这是商对象中 ≈ 的协变读法。(3)  [Sets] 在 [Untruncate] 下是强幂的 PIN：
 [Sets_WellPowered_untruncate : Untruncate@{o} → WellPowered Sets@{o so}]。[X] 处的指标是 Instance/Sets/Classifier/OneLevel.v 的条件分类器的同集 [X ~> Ω]，并且它通过 [eq_refl] 读回为
 [X ~{Sets}~> Powerset_Omega] ([Sets_WellPoweredAt_untruncate_index])：
 命题值谓词，在承载宇宙 [o] 上。证据是 Structure/WellPowered.v 的通用 [wp_of_classifier]，应用于
 [Sets_Classifier U]，在 Instance/Sets/Pullback.v 的 [Sets_HasPullbacks] 上：
 [wp_to] 将真子对象沿谓词拉回，[wp_from] 是 [char]，[wp_to_from] 是 Structure/SubobjectClassifier.v 的 [classifier_pullback_roundtrip]，而 OneLevel.v 的
 [sets_pullback_roundtrip] 在 [Sets] 重新表述。[untruncate_of_IEM] (OneLevel.v) 在信息化排中律下也使其成立。[Untruncate@{o} := ∀ P : Type@{o}, Powerset_squash P → P] 是一个假设，而不是公理：没有任何被声明，并且 Instance/Fun/Topos.v 的头部记录了它在树中没有成员，并且没有证明它的不可能性。(4) 在相同假设下，[Sets] 的 §V.8 后果：[Sets_wellpowered_intersection U X P HP] 是大型族 [{ m : SubObj X & P m }] 的一个 [IsIntersection]（Theory/Subobject/Lattice.v），对于任何 ≈-封闭的 [Type@{o}] 值性质 [P] 的子对象。它直接与 Instance/Sets/SubobjectLattice.v 的 [Sets_HasWidePullbacks] 以及 Lattice.v 的 [sub_intersection] 相反：宽拉回是对小指标 [{ i : X ~> Ω & P (wp_to i) }] 进行的，并用 [sub_top] 填充，以便 [sub_intersection] 的选定点 [None] 总是存在；下界沿 [wp_to_from] 传递 [P]，并且最大性成立，因为小族是大族的子族。[Sets_intersection_all_empty] 在 [P := unit] 读取它，所有子对象的类别：交集有一个空载体，因为空子对象 [sets_sub_bot]（Instance/Sets/SubobjectLattice.v 的 [Sets_zero_monic]）是其中一个成员。

 为什么固定见证使用 [Untruncate] ：没有它的路径被拒绝。下面的每个拒绝都是通过将这一条命令附加到整个文件的副本并编译来实现的；每个都有一个旁边的已接受控制。它们拒绝特定的构造；没有证明不可能性（见未交付部分）。- (1) 的索引位于 [o+1]，而引脚要求 [o]。提供 [Sets_WellPoweredAt_up X]，其中 [WellPowered@{so o o so so} Sets@{o so}] 被期望，却被拒绝：“术语 'Sets_WellPoweredAt_up X' 的类型为 'WellPoweredAt@{R1.2118 R1.2117 R1.2117 o R1.2118} X'，而它被期望的类型为 'WellPoweredAt@{o so so o so} X'（宇宙不一致：无法强制 o = so，因为 o < so）”。控制：相同的证明在 [Sets_WellPoweredAt_up@{o so so}] 被接受。- 一个 [Prop] 值的索引位于 [o]，但它无法重建它所命名的子对象的域：反向映射需要从截断的原像中取出一个元素。使用 [inhabited] ：在归纳类型 "inhabited" 中错误地去掉了 "proj2_sig p"：返回类型的 sort 是 "Type"，而它应该是 SProp 或 Prop。使用不可判定的 [Powerset_squash] 时，分类器使用："项 "q" 的类型是 "∃ a : A, m a ≈ b"，而预期的类型是 "?Q"（无法找到 "?Q" 的正确类型实例：不能确保 "Type" 是 "Prop" 的子类型）"。精确地反转该截断是 [Untruncate] 的功能，并且在 OneLevel.v 的 [sce_elim] 中使用过一次。[PropEquiv]（Lib/Setoid/Propositional.v）无济于事：它只能从 Prop 恢复出一个 Type 值的 ≈，而不是从存在量词中恢复一个元素。- 当固定的索引被接受时，(1) 的索引上的结果 (4) 被拒绝：[sub_intersection] 在 [Sets_HasWidePullbacks] 上，并由 [option { i : wp_index (Sets_WellPoweredAt_up X) & … }] 索引的族给出“无法找到 '?A' 的良型实例化：无法确保 'Type@{max(o,R3.2141)}' 是 'Type@{R3.2125}' 的子类型”，而在 [Sets_WellPoweredAt_untruncate U X] 上的同一项可以编译。[Sets] 的广拉回索引是承载宇宙；良基索引必须适配其下，这就是固定索引。

 优点。每个子对象和商对象的比较都大致相等 ≈（在 [X] 上域或余域的同构）；没有任何地方存在 Leibniz 唯一性。两个 [eq_refl] 的回读是谓词子对象的承载和固定证人的索引。宇宙，用 [Set Printing Universes. About …] 测量（标准库边界如 [Projections.u0] 被省略）：sets_pred_index@{o so}  : 集合等价对象@{o o} → 类型@{o+1}
 sets_rel_index@{o so}   : 集合等价对象@{o o} → 类型@{o+1}
 Sets_WellPoweredAt_up@{o so u}   : ∀ X, 在@{u so so o u} 上完备上确界 X
 ( * o < so, o < u * )
 Sets_CoWellPoweredAt_up@{o so u} : ∀ X, 在@{u so so o u} 上完备上确界 X
 ( * 在 Sets^op 中; o < so, o < u * )
 Sets_WellPoweredAt_untruncate@{o so u} :
 非截断@{o} → ∀ X, 在@{o so so o u} 上完备上确界 X
 ( * 集合 < o, o < so, o < u * )
 Sets_WellPowered_untruncate@{o so t} :
 非截断@{o} → 在@{so o o so t} 上完备上确界 集合@{o so}
 ( * 集合 < o, o < so, o < t * )
 Sets_wellpowered_intersection@{o so u u0} : 非截断@{o} → …
 是交集@{so"}o so} (λ k : ∃ m : SubObj@{so o} X, P m, `1 k) w
 ( * 集合 < o, o < so, o < u, o < u0 * )[WellPoweredAt] 的第一个槽是索引宇宙，它的第四个槽是同宇宙，因此 (1) 和 (2) 的索引严格高于同宇宙，而 (3) 的索引与它们相等。[Set < o] 在 (3) 和 (4) 中来自 [Powerset_Omega] 的 [Prop] 值承载器；(1) 和 (2) 没有携带 [Set] 绑定。固定证人的第一个集合位槽 [s] 是 [so]，其中最小化将其放入截面中：为其单独命名的顶级绑定器在 [+] 下会重新加上 "so = s"。第二个 [t] 在同宇宙之上是自由的，ZW114WZZ 对其命名。测量。27 个常量（[.glob] 头部匹配 '^(def|prf|thm|ind|constr|proj|rec)'）且没有 [Program] 义务（[strings] 在 .vo 上未找到 [_obligation_] 名称）；每一个都通过其完全限定名在 [Print Assumptions] 下报告“在全局上下文下封闭”。13 个 [Defined] 和 2 个 [Qed]。将每个 [Defined] 翻转为 [Qed] 在整个文件副本中，十个是承重的——后来的证明或回读会读取它们的组件——三者重新编译为绿色：[sets_pred_to_from]、[sets_rel_to_from] 和 [Sets_wellpowered_intersection]，由于≈在子对象上是同构且交集是对象，所以保持透明，两者都是数据。[sets_rel_of_quot] 是以策略形式构建的，而不是作为匿名对构建的，并且两个 [eq_refl] 读回位于没有宇宙绑定器的部分之外：两者都是 Coq 8.19/8.20 的预防措施（匿名对陷阱记录在 Instance/Grp/Quotient.v 对 [SubgroupGrp] 的注释中，以及 Theory/Size.v 对 [ObjEq] 的说明中），在运行这些工具链之前采取；是否真的需要放在那里尚未测量。未交付。[Sets] 在该节点上是良好幂的，无条件：未给出构造，也未证明不可能。[Sets] 在该节点上共同良好幂，即使在 [Untruncate] 情况下：未尝试。没有在 [Sets@{Set _}] 上对 (3) 或 (4) 的见证（如上 [Set < o]）。在任意完备范畴上的一般结论是 Structure/WellPowered.v 的工作，而不是这个文件的；(4) 是其 [Sets] 实例，直接陈述在 [Sets] 已经具有的广拉回上。没有注册 [Instance]。[Ab]、[RMod R] 以及其他代数范畴在这里未尝试。
*)

Section SetsWellPoweredUp.

Universe o so.
Constraint o < so.

(* * ** Well-powered one universe up: subobjects as Type-valued predicates / * ** 功能强大的一个宇宙提升：作为类型值谓词的子对象 *)

(* The index at [X]: the ≈-respecting [Type@{o}]-valued predicates on the carrier. It lives at [o+1]. / [X] 的索引：载体上约束 ≈ 的 [Type@{o}] 值谓词。它位于 [o+1]。 *)
Definition sets_pred_index (X : SetoidObject@{o o}) :=
  { P : carrier X → Type@{o} & ∀ a b : carrier X, a ≈ b → P a → P b }.

(* The domain of the subobject a predicate names: the elements satisfying it, compared on the first component. / 子对象谓词所命名的域：满足它的元素，在第一个分量上进行比较。 *)
Definition sets_pred_setoid (X : SetoidObject@{o o}) (P : sets_pred_index X) :
  SetoidObject@{o o}.
Proof.
  unshelve refine
    {| carrier := { a : carrier X & `1 P a } ;
       is_setoid := {| equiv := fun p q =>
                         @equiv _ (is_setoid X) (`1 p) (`1 q) |} |}.
  constructor.
  - intro p; reflexivity.
  - intros p q H; symmetry; exact H.
  - intros p q r H1 H2; etransitivity; [exact H1|exact H2].
Defined.

Definition sets_pred_incl (X : SetoidObject@{o o}) (P : sets_pred_index X) :
  sets_pred_setoid X P ~{Sets@{o so}}~> X.
Proof.
  unshelve refine {| morphism := fun p => `1 p |}.
  intros p q H; exact H.
Defined.

Lemma sets_pred_incl_monic (X : SetoidObject@{o o}) (P : sets_pred_index X) :
  @Monic Sets@{o so} _ _ (sets_pred_incl X P).
Proof.
  apply (fst (injectivity_is_monic (sets_pred_incl X P))).
  intros p q H; exact H.
Qed.

Definition sets_sub_of_pred (X : SetoidObject@{o o}) (P : sets_pred_index X) :
  @SubObj Sets@{o so} X :=
  @Build_SubObj Sets@{o so} X (sets_pred_setoid X P) (sets_pred_incl X P)
    (sets_pred_incl_monic X P).

(* The predicate a subobject names: "is in the image", as DATA -- the preimage is carried, not truncated. / 谓词一个子对象命名：“在图像中”，作为数据——原像被携带，而不是截断。 *)
Definition sets_pred_of_sub (X : SetoidObject@{o o})
  (u : @SubObj Sets@{o so} X) : sets_pred_index X.
Proof.
  exists (fun b => { a : carrier (sub_dom u) & sub_mono u a ≈ b }).
  intros b b' Hb [a Ha]; exists a; etransitivity; [exact Ha|exact Hb].
Defined.

(*
 The domain isomorphism.  Forward: project the carried preimage;
 it respects ≈ because the mono is injective. 

 --------
 域同构。正向：投影所携带的原像；它遵循≈，因为单射是单一映射。
*)
Definition sets_pred_fwd (X : SetoidObject@{o o}) (u : @SubObj Sets@{o so} X) :
  sets_pred_setoid X (sets_pred_of_sub X u) ~{Sets@{o so}}~> sub_dom u.
Proof.
  pose proof (snd (injectivity_is_monic (sub_mono u)) (sub_is_monic u)) as inj.
  unshelve refine {| morphism := fun p => `1 (`2 p) |}.
  intros [b [a Ha]] [b' [a' Ha']] H; simpl in *.
  apply inj. rewrite Ha, Ha'. exact H.
Defined.

Definition sets_pred_bwd (X : SetoidObject@{o o}) (u : @SubObj Sets@{o so} X) :
  sub_dom u ~{Sets@{o so}}~> sets_pred_setoid X (sets_pred_of_sub X u).
Proof.
  unshelve refine {| morphism := fun a =>
      existT (fun b => { a' : carrier (sub_dom u) &
                         @equiv _ (is_setoid X) (sub_mono u a') b })
             (sub_mono u a)
             (existT (fun a' => @equiv _ (is_setoid X) (sub_mono u a')
                                                     (sub_mono u a)) a
                     (@Equivalence_Reflexive _ _ (@setoid_equiv _ (is_setoid X))
                        (sub_mono u a))) |}.
  intros a a' H; simpl. apply proper_morphism; exact H.
Defined.

Definition sets_pred_iso (X : SetoidObject@{o o}) (u : @SubObj Sets@{o so} X) :
  @Isomorphism Sets@{o so} (sets_pred_setoid X (sets_pred_of_sub X u))
    (sub_dom u).
Proof.
  unshelve refine
    (@Build_Isomorphism Sets@{o so} _ _ (sets_pred_fwd X u) (sets_pred_bwd X u)
       _ _).
  - intro a; simpl; reflexivity.
  - intros [b [a Ha]]; simpl. exact Ha.
Defined.

Definition sets_pred_to_from (X : SetoidObject@{o o})
  (u : @SubObj Sets@{o so} X) :
  sets_sub_of_pred X (sets_pred_of_sub X u) ≈ u.
Proof.
  exists (sets_pred_iso X u).
  intros [b [a Ha]]; simpl. exact Ha.
Defined.

Definition Sets_WellPoweredAt_up (X : SetoidObject@{o o}) :
  @WellPoweredAt Sets@{o so} X :=
  {| wp_index   := sets_pred_index X ;
     wp_to      := sets_sub_of_pred X ;
     wp_from    := sets_pred_of_sub X ;
     wp_to_from := sets_pred_to_from X |}.

(* * ** Co-well-powered one universe up: quotients as coarser relations / * ** 共同良好支撑的单一宇宙提升：作为较粗关系的商 *)

(*
 The index at [X]: the [Type@{o}]-valued equivalence relations on the
 carrier coarser than its ≈.  It lives at [o+1]. 

 --------
 在 [X] 的指数：载体上比其 ≈ 更粗的 [Type@{o}] 值的等价关系。它位于 [o+1]。
*)
Definition sets_rel_index (X : SetoidObject@{o o}) :=
  { R : crelation@{o o} (carrier X) & (Equivalence R * SetoidCoarser R)%type }.

Definition sets_quot_of_rel (X : SetoidObject@{o o}) (R : sets_rel_index X) :
  @QuotObj Sets@{o so} X :=
  SetsQuotient_QuotObj X (`1 R) (fst (`2 R)) (snd (`2 R)).

(*
 The kernel relation of a quotient's epimorphism.  Written in tactic
 form: an anonymous pair whose expected type needs unfolding
 [sets_rel_index] down to the carrier is a known Coq 8.19/8.20 trap. 

 --------
 商的满射的核关系。以策略形式书写：一个匿名对，其期望类型需要展开。将 [sets_rel_index] 化简到载体上是已知的 Coq 8.19/8.20 陷阱。
*)
Definition sets_rel_of_quot (X : SetoidObject@{o o})
  (q : @QuotObj Sets@{o so} X) : sets_rel_index X.
Proof.
  exists (sets_coimage_rel (quot_epi q)).
  exact (sets_coimage_rel_Equivalence (quot_epi q),
         sets_coimage_rel_coarser (quot_epi q)).
Defined.

Definition sets_rel_fwd (X : SetoidObject@{o o}) (q : @QuotObj Sets@{o so} X) :
  quot_cod (sets_quot_of_rel X (sets_rel_of_quot X q))
    ~{Sets@{o so}}~> quot_cod q.
Proof.
  unshelve refine {| morphism := fun a => quot_epi q a |}.
  intros a b H; exact H.
Defined.

(*
 Backward: the preimage [Sets_quot_epi_surjective] returns is DATA,
 because [∃] is [sigT] here. 

 --------
 向后：原像 [Sets_quot_epi_surjective] 返回的是 DATA，因为 [∃] 在这里是 [sigT]。
*)
Definition sets_rel_bwd (X : SetoidObject@{o o}) (q : @QuotObj Sets@{o so} X) :
  quot_cod q
    ~{Sets@{o so}}~> quot_cod (sets_quot_of_rel X (sets_rel_of_quot X q)).
Proof.
  unshelve refine {| morphism := fun b => `1 (Sets_quot_epi_surjective q b) |}.
  intros b b' H; simpl; unfold sets_coimage_rel.
  rewrite (`2 (Sets_quot_epi_surjective q b)),
          (`2 (Sets_quot_epi_surjective q b')).
  exact H.
Defined.

Definition sets_rel_iso (X : SetoidObject@{o o}) (q : @QuotObj Sets@{o so} X) :
  @Isomorphism Sets@{o so}
    (quot_cod (sets_quot_of_rel X (sets_rel_of_quot X q))) (quot_cod q).
Proof.
  unshelve refine
    (@Build_Isomorphism Sets@{o so} _ _ (sets_rel_fwd X q) (sets_rel_bwd X q)
       _ _).
  - intro b; simpl. exact (`2 (Sets_quot_epi_surjective q b)).
  - intro a; simpl; unfold sets_coimage_rel.
    exact (`2 (Sets_quot_epi_surjective q (quot_epi q a))).
Defined.

Definition sets_rel_to_from (X : SetoidObject@{o o})
  (q : @QuotObj Sets@{o so} X) :
  sets_quot_of_rel X (sets_rel_of_quot X q) ≈ q.
Proof.
  apply (snd (quot_equiv_iff_iso _ _)).
  exists (sets_rel_iso X q).
  intro a; simpl; reflexivity.
Defined.

Definition Sets_CoWellPoweredAt_up (X : SetoidObject@{o o}) :
  @WellPoweredAt (Sets@{o so}^op) X :=
  {| wp_index   := sets_rel_index X ;
     wp_to      := sets_quot_of_rel X ;
     wp_from    := sets_rel_of_quot X ;
     wp_to_from := sets_rel_to_from X |}.

End SetsWellPoweredUp.

(*
 Readback: the subobject named by a predicate has the satisfying
 elements as its carrier, on the nose.  The two [eq_refl] readbacks of
 this file are stated outside any section and with no universe binder:
 Theory/Size.v's note on [ObjEq] records that Leibniz [eq] under a
 universe binder with a constraint clause is refused on Coq 8.19 and
 8.20, and the sections here declare constraints. 

 --------
 回读：由谓词命名的子对象其载体恰好具有满足条件的元素。本文件的两个 [eq_refl] 回读在任何章节之外声明，并且没有宇宙绑定器：Theory/Size.v 关于 [ObjEq] 的注释记录了在带有约束条款的宇宙绑定器下 Leibniz [eq] 在 Coq 8.19 和 8.20 上被拒绝，这里的章节声明了约束。
*)
Example Sets_WellPoweredAt_up_carrier (X : SetoidObject)
  (P : sets_pred_index X) :
  carrier (sub_dom (wp_to (Sets_WellPoweredAt_up X) P))
    = { a : carrier X & `1 P a } := eq_refl.

(* * ** Well-powered at the pin, under [Untruncate] / * ** 在引脚处功率充足，低于 [Untruncate] *)

Section SetsWellPoweredPinned.

Universe o so.
Constraint o < so.
Constraint Set < o.

Context (U : Untruncate@{o}).

(*
 Structure/WellPowered.v's generic [wp_of_classifier], at the
 conditional classifier [Sets_Classifier U] over [Sets_HasPullbacks]:
 the index is the hom-set [X ~> Ω], at the hom universe [o]. 

 --------
 Structure/WellPowered.v 的泛型 [wp_of_classifier]，在条件分类器 [Sets_Classifier U] 上的 [Sets_HasPullbacks]：索引是同构集 [X ~> Ω]，在同构宇宙 [o] 上。
*)
Definition Sets_WellPoweredAt_untruncate (X : SetoidObject@{o o}) :
  @WellPoweredAt Sets@{o so} X :=
  @wp_of_classifier Sets@{o so} Sets_Terminal@{so o} Sets_HasPullbacks@{so o}
    (Sets_Classifier@{o so} U) X.

End SetsWellPoweredPinned.

Example Sets_WellPoweredAt_untruncate_index (U : Untruncate)
  (X : SetoidObject) :
  wp_index (Sets_WellPoweredAt_untruncate U X)
    = (X ~{Sets}~> Powerset_Omega) := eq_refl.

Definition Sets_WellPowered_untruncate@{o so t | o < so, Set < o, o < t +}
  (U : Untruncate@{o}) : WellPowered@{so o o so t} Sets@{o so} :=
  fun X => Sets_WellPoweredAt_untruncate U X.

(* * ** The intersection of a class of subobjects, at [Sets] / * ** 在 [Sets]，子对象类的交集 *)

(*
 Mac Lane's "any set of subobjects", read as a ≈-closed property [P] of
 subobjects of [X]: the family [{ m : SubObj X & P m }] is LARGE (it sits
 at [so]), so [Sets_HasWidePullbacks], whose index lives at the carrier
 universe [o], cannot take it directly.  The pinned witness reindexes it
 over the SMALL index [{ i : X ~> Ω & P (wp_to i) }], padded with the top
 subobject so that the chosen point [None] of [sub_intersection] always
 exists. 

 --------
 Mac Lane 的“任意子对象集合”，可以理解为子对象的 ≈-闭性质 [P] ：子对象族 [{ m : SubObj X & P m }] 是大的（它位于 [so] 处），所以 [Sets_HasWidePullbacks]，其索引位于载体宇宙 [o]，不能直接取它。固定的见证通过较小索引 [{ i : X ~> Ω & P (wp_to i) }] 对它重新索引，并用顶端子对象填充，以便 [sub_intersection] 的选定点 [None] 总是存在。
*)

Section SetsIntersection.

Universe o so.
Constraint o < so.
Constraint Set < o.

Context (U : Untruncate@{o}) (X : SetoidObject@{o o}).
Context (P : @SubObj Sets@{o so} X → Type@{o}).
Context (HP : ∀ m m' : @SubObj Sets@{o so} X, m ≈ m' → P m → P m').

Definition sets_wp_family :
  option { i : wp_index (Sets_WellPoweredAt_untruncate U X)
         & P (wp_to (Sets_WellPoweredAt_untruncate U X) i) } →
  @SubObj Sets@{o so} X :=
  fun j => match j with
           | None => @sub_top Sets@{o so} X
           | Some p => wp_to (Sets_WellPoweredAt_untruncate U X) (`1 p)
           end.

Definition Sets_wellpowered_intersection :
  { w : @SubObj Sets@{o so} X &
    IsIntersection (fun k : { m : @SubObj Sets@{o so} X & P m } => `1 k) w }.
Proof using U HP.
  set (W := Sets_WellPoweredAt_untruncate U X).
  exists (@sub_intersection Sets@{o so} Sets_HasWidePullbacks@{o so} X _
            None sets_wp_family).
  pose proof (@sub_intersection_IsIntersection Sets@{o so}
                Sets_HasWidePullbacks@{o so} X _ None sets_wp_family) as H.
  constructor.
  - intros [m pm].
    pose (p := HP m _ (symmetry (wp_to_from W m)) pm).
    apply (sub_le_trans _ (sets_wp_family (Some (wp_from W m; p)))).
    + exact (inter_le _ _ H (Some (wp_from W m; p))).
    + exact (sub_le_of_equiv _ _ (wp_to_from W m)).
  - intros v Hv.
    apply (inter_greatest _ _ H).
    intros [[i pi]|]; simpl.
    + exact (Hv (wp_to W i; pi)).
    + exact (sub_top_greatest v).
Defined.

End SetsIntersection.

(* The class of ALL subobjects: its intersection is empty, because the empty subobject is a member. This reads the construction back at a case whose answer is known. / 所有子对象的类：它们的交集是空的，因为空子对象是其成员。这将构造读回到一个答案已知的情况。 *)
Definition sets_sub_bot@{o so | o < so +} (X : SetoidObject@{o o}) :
  @SubObj Sets@{o so} X :=
  @Build_SubObj Sets@{o so} X _ _ (Sets_zero_monic X).

Lemma Sets_intersection_all_empty@{o so | o < so, Set < o +}
  (U : Untruncate@{o}) (X : SetoidObject@{o o})
  (a : carrier (sub_dom (`1 (Sets_wellpowered_intersection U X
                               (fun _ => Datatypes.unit)
                               (fun _ _ _ t => t))))) : False.
Proof.
  destruct (inter_le _ _
              (`2 (Sets_wellpowered_intersection U X
                     (fun _ => Datatypes.unit) (fun _ _ _ t => t)))
              (sets_sub_bot X; tt)) as [k _].
  exact (match k a with end).
Qed.
