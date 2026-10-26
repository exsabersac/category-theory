Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Size.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Thin.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Product.Limit.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Limit.
Require Import Coq.Logic.Eqdep_dec.

Generalizable All Variables.

(* * * Freyd's collapse: a small complete category is a preorder / * * 弗雷伊德的崩溃：一个小的完备范畴是一个前序 *)

(*
 Mac Lane §V.2 Proposition 3 (book p. 114; maclane:V.2:prop3); Awodey §9.8
 Proposition 9.34 (awodey:9.8:prop34); Riehl §3.7 Proposition 3.7.3
 (riehl:3.7:prop3) and Epilogue §E.1 (riehl:E.1:thm-large-products-poset);
 Riehl's Definition 3.7.2 (riehl:3.7:def2) is the size measure Prop 3.7.3
 is stated against and is consumed here as an ORDER ([ArrowIndex]), NOT
 delivered as a cardinal — its checkbox is not met as written (see NOT
 DELIVERED).
 nLab: https://ncatlab.org/nlab/show/complete+small+category

 BACKGROUND.  Freyd's argument: were a category with products indexed by
 its own arrow collection to carry two distinct parallel arrows f, g : a
 ⇉ b, the 2^K choices “f or g at each index” would give 2^K arrows into
 the K-fold power of b, more than the K arrows there are in all — Cantor.
 So a small complete category is a preorder, and the completeness that
 matters is that of LARGE categories; Adjunction/GAFT.v and
 Instance/Poset.v record the consequence for the adjoint functor
 theorems, and Structure/Complete.v the statement.  Near-namesakes:
 Structure/Premonoidal/Freyd.v is about Freyd CATEGORIES (premonoidal),
 unrelated; Structure/Limit/FromProducts.v opens a [Section
 ArrowIndex] around its [ArrowIx] index type (section names do not
 survive [End], so there is no clash), and Theory/Size.v's [TotalMor]
 is the same idea as a Σ-type — the witness of item (2) uses it.

 STALE PREMISES, RE-MEASURED.  The issue's “Verified ABSENT” paragraph is
 wrong on three of its four clauses; both files postdate the issue text.
 - “no thin-category predicate”: Structure/Thin.v [Thin C := ∀ x y
 (f g : x ~> y), f ≈ g], with [Thin_Opposite]/[Opposite_Thin],
 [thin_preorder], [thin_PreOrder] and [HomChoice],
 all consumed here.
 - “no smallness predicate, no global arrow-set”: Theory/Size.v's
 [LocallySmall], [Small] and [TotalMor C := {x & {y & x ~> y}}];
 Adjunction/SAFT.v's “NO size / smallness machinery” is stale as to
 smallness.  [Small] is deliberately NOT consumed (below).
 - “no cardinality vocabulary beyond the finite counter”: true, and
 none is added — but the counter is Theory/Metacategory.v's
 [cardinality], which the issue cites at the wrong place, as it
 does that constant's note “counts the identity arrows” and
 [ThreeArrows_card_3]; and it counts OBJECTS, so it is not Riehl
 3.7.2 either.
 - The Cantor step is in the tree: Instance/Fun/Discrete.v's
 [cantor_predicates] and [cantor_bool] (four lines).  A Structure/
 file does not require Instance/Fun, so [freyd_cantor_bool] below is a
 named twin; relocating the original to Lib/ is surfaced, not done.
 - #422 has landed: Instance/Proset/Limit.v
 [proset_Complete_iff_all_meets], consumed by item (7).
 - Decidable object equality is in the tree: Construction/Quotient.v's
 [ObjDecEq] (a definitional class; [obj_uip] is [UIP_dec] on
 it), consumed by item (2).  An earlier revision declared a duplicate
 [DecObj] with the same statement; the audit found the twin.
 - Prose locations: the issue's pointers into Structure/Complete.v
 are stale for both the Freyd paragraph and the Hyland caveat, as
 is its pointer to Instance/Poset.v's sentence; the one into
 GAFT.v is right.  Still absent, measured: [SmallCategory]/[is_small] (0
 hits), a morphism cardinal, and any [Complete C → HasIndexedProducts]
 bridge (every consumer builds its product by hand, e.g. SAFT.v).

 WHAT IS DELIVERED (38 constants, every one closed under the global
 context).
 (1) THE SMALLNESS WITNESS.  [ArrowIndex C]: a type [ai_index] with an
 encoding of every arrow and a decoding RELATIVE TO A DEFAULT whose
 round trip is the identity up to [≈] for every default — i.e.
 |hom x y| ≤ |ai_index| for every inhabited hom-set, Riehl's
 “products of families as large as its own cardinality”, so the
 theorem covers large categories and discharges her §3.7 stronger
 hypothesis; the dual [ArrowIndex_op] is field for field the same
 data (EMPTY constraint block), through [@Build_ArrowIndex (C^op)]
 because the anonymous literal is refused (probe N2), and it is an
 involution at [eq_refl] (probe).  No cardinal ARITHMETIC is
 introduced: the proof consumes the ORDER “no bigger than K”, which
 is what Riehl's Definition 3.7.2 is used for; disclosed as such.
 Theory/Size.v's [Small] is not consumed: it resizes per hom-set
 through [ObjEq] transports, and the proof needs one index type for
 all arrows.
 (2) THE WITNESS IS NOT VACUOUS.  Over Construction/Quotient.v's
 [ObjDecEq C] (decidable object equality), [td]/[td_enc] (decode a
 bundled arrow at requested endpoints, round trip by
 Coq.Logic.Eqdep_dec's [UIP_dec] — a theorem, not an axiom),
 [canonical_ArrowIndex : ObjDecEq C → ArrowIndex C] at index
 [TotalMor C].  Every category with decidable object equality has an
 [ArrowIndex], thin or not; the strength of the theorem sits in the
 products at that index.  (The terminal category satisfies all
 three hypotheses of item (6), so they are jointly satisfiable; no
 non-trivial in-tree instance is exhibited.)
 (3) THE CONSTRUCTIVE KERNEL.  Section [FreydCore] consumes ONE
 elementary [IsIndexedProduct (fun _ : K => b) P pr] and a boolean
 separator [sep] of the pair ([sep_resp], [sep f = true], [sep g =
 false]): [fr_mk] (the 2^K arrows), [fr_decode]/[fr_decode_mk]
 (read the choice back), [fr_rd]/[fr_rd_enc] (the index surjects
 onto [a ~> P]), [fr_Fam_surjective] (hence onto [K → bool]), and
 [freyd_no_separated_pair : False] by [freyd_cantor_bool].  No
 axiom, no excluded middle, no decidability, no [Set].
 (4) THINNESS FROM DECIDABLE HOMS.  [DecHom C := ∀ x y (u v : x ~> y),
 (u ≈ v) + (u ≈ v → False)] (a [sum]: [≈] is Type-valued,
 Lib/Setoid.v), the separator [fr_sep h := if D h f then true else
 false] with [fr_sep_resp]/[fr_sep_f]/[fr_sep_g], and
 [freyd_thin : ArrowIndex C → HasIndexedProducts C → DecHom C →
 Thin C]; [freyd_thin_canonical] at [ObjDecEq]; [DecHom_op] and
 [freyd_thin_dual] (products in [C^op], Riehl §E.1's “or
 coproducts”, via [Opposite_Thin]).
 (5) THE WALL, LOCATED.  From [f ≉ g] ALONE — no separator, no
 decidability — [fr_mk_injective] (injective up to [≈]) and
 [fr_inj_injective]: an injection [(K → bool) → K] on the nose.
 Refuting it needs a left inverse, i.e. testing at each index
 whether the leg is f or g, i.e. [DecHom]; the Russell/Cantor
 no-injection argument for Prop-valued families (stated by no
 in-tree constant — Instance/Fun/Discrete.v's
 [cantor_predicates] is the surjection form) is not available
 because the family needs a BOOLEAN choice.  This is exactly
 Hyland's effective-topos
 counterexample (Structure/Complete.v): the theorem is NOT
 constructively provable without [DecHom], which is why the
 decider is an explicit hypothesis and [Print Assumptions] stays
 closed.  The probe carries the injection as a positive control
 and no refutation, since unprovability is metatheoretic.
 (6) FROM [Complete], WITHOUT A [Set] PIN.  Section [CompleteBridge]:
 [complete_iprod_obj]/[complete_iprod_proj]/[complete_iprod :
 IsIndexedProduct d …] for any [d : A → C], through
 Structure/Limit/Comparison.v's annotated [DiscreteCat_Functor'] and
 [discrete_IsIndexedProduct_of_IsLimitCone]; the unannotated route
 pins C's hom level to [Set] (probe N1, “Cannot enforce Set = uh”),
 and the carrier of that pin is Structure/Limit/Product.v's
 [limit_is_indexed_product], whose binder is [C : Category@{_ Set
 Set}] — [DiscreteCat_Functor]'s own binder leaves C free; it
 emits a shape with [Set] homs, and the limit vocabulary identifies
 the shape's hom level with the ambient's (the equations of the
 UNIVERSES section below).  This is the [Complete →
 IsIndexedProduct] bridge the tree lacked.  Then the issue's pinned
 [small_complete_is_thin : ArrowIndex C → Complete C → DecHom C →
 Thin C] and [small_cocomplete_is_thin] (Riehl §E.1's cocomplete
 half, via Construction/Product/Limit.v's
 [Complete_op_of_Cocomplete]).
 (7) THE SECOND HALF: GREATEST LOWER BOUNDS.  [complete_has_glbs :
 Complete C → HomChoice C → HasAllMeets (thin_preorder C)]: a
 product IS a greatest lower bound in the preorder reflection of
 ANY category — neither smallness nor thinness enters, which is why
 the issue's pinned NAME [small_complete_has_glbs] is not declared
 (a name asserting a hypothesis the statement does not use).  The
 one hypothesis is [HomChoice] (Structure/Thin.v): the lower
 bounds arrive [inhabited]-squashed and the mediator needs the
 arrows.  [complete_Proset_Complete : Complete C → HomChoice C →
 Complete (Proset (thin_PreOrder C))] closes the loop with #422's
 [proset_Complete_iff_all_meets].
 (8) PROSE.  Structure/Complete.v now points at
 [small_complete_is_thin]/[complete_has_glbs] and names
 [DecHom] as the constructive hypothesis — both edits
 LINE-NEUTRAL, so the citation Instance/Sets/Products.v makes
 into that file still lands on Freyd's statement.  GAFT.v and
 Poset.v are untouched (pointers surfaced, not added).

 UNIVERSES (measured by [About] under [Set Printing Universes] on all 38
 constants).
 - 35 of the 38 blocks carry no universe equation.  The three of
 section [CompleteBridge] — [complete_iprod], [complete_iprod_obj],
 [complete_iprod_proj] — each carry [o = u0], [h = p], [h = uh],
 [h = up] and [uh = up]: the limit vocabulary identifies the shape's
 hom and proof levels with C's and the shape's object level with
 [Complete]'s index, the fact Adjunction/SAFT.v records in
 prose and the FromProducts.v bullet as [u2 = u4].  No equation
 reaches the kernel, [freyd_thin], [small_complete_is_thin],
 [complete_has_glbs] or [complete_Proset_Complete].  (An earlier
 revision said “NO universe equation in any block”; the audit
 measured these five.)  [ArrowIndex@{u u0 u1} : Category@{u0 u1 u1}
 → Type@{max(u+1,u0,u1)}] and [ArrowIndex_op@{u u0 u1}] carry EMPTY
 blocks — the index level [u] is unrelated to C's levels; [DecHom],
 [DecHom_op] and [fr_sep] carry only the bounds [u0 <= u], [u1 <= u]
 placing C's levels below the result sort.
 - The kernel carries no stdlib bound at all: [freyd_no_separated_pair
 @{u u0 u1 u2} : ∀ {C : Category@{u u0 u0}} (AI : ArrowIndex@{u1 u u0}
 C) …, IsIndexedProduct@{u1 u2 u u0} …] with [u0 <= u2], [u1 <= u2]
 only.  [freyd_thin@{u u0 u1 u2 u3}] adds only [False_rect.u0].
 - The canonical witness: [td] is bounded by [eq_rect.u0/u1] and
 [Projections.u0/u1] only; [td_enc], [canonical_ArrowIndex] and
 [freyd_thin_canonical] add [Eqdep_dec.UIP_dec.u0] and [eq_rect_r.u1]
 — the price of [UIP_dec] (an earlier revision put [UIP_dec] on [td]
 too and omitted [Projections]).  [fr_inj_injective] carries
 [eq_rect.*]/[eq_rect_r.u1] (rewriting on [=]).
 - The [Complete]-fed constants ([complete_iprod_obj/proj],
 [complete_iprod], [small_complete_is_thin], [small_cocomplete_is_thin],
 [complete_has_glbs], [complete_Proset_Complete]) inherit [JMeq.u0 <=
 JMeq.u1], [EqdepFacts.eq_sigT_sig_eq.u2] and [eq_rect_r.u1] bounds
 through [DiscreteCat_Functor'] (Comparison.v's header attributes them
 to its Program auxiliary), plus [eq.u0], [eq_ind.u0],
 [Logic_lemmas.equality.u0] on the shape levels.
 - [small_complete_is_thin@{u u0 u1 u2 u3} : ∀ {C : Category@{u2 u3 u3}},
 ArrowIndex@{u0 u2 u3} C → Complete@{u u0 u3 u2} → DecHom@{u1 u2 u3} C
 → Thin@{u1 u2 u3} C] with [u0 <= u] (the index level sits below the
 shape-object level [Complete] quantifies over) and no [Set].
 - The ONLY [Set] in any block: [complete_Proset_Complete] concludes
 [Complete@{u u Set u0}] — the hom level of [Proset], whose homs are
 Props, inherited from Instance/Proset/Limit.v's statement.

 COUNTS AND CONVENTIONS.
 - 38 constants (19 [def], 14 [prf], 4 [proj], 1 [rec] DECLARATION
 entries in the [.glob]; the constructor [Build_ArrowIndex] appears
 there only as an [R … constr] reference, so it is not among the 38;
 an earlier revision counted 39 with the duplicate [DecObj]), all
 “Closed under the global context”, zero [Axioms:] lines, all gated
 fully qualified.  Thirteen [Qed]; one [Defined] ([complete_has_glbs],
 data: [HasAllMeets] is [sigT]-valued), which flips to [Qed] freely
 and is kept [Defined] by the data convention.
 - Closure 72 files excluding self: Instance/Proset/Limit.v costs 23 at
 the margin (item (7)'s vocabulary and #422's theorem),
 Structure/Limit/Comparison.v 7, Construction/Product/Limit.v 4,
 Construction/Quotient.v, Structure/Thin.v and Theory/Size.v 1 each,
 the other ten [Require]s 0 (an earlier revision also required
 Category.Theory.Functor, the one droppable [Require]; dropped).  No
 collision: each new name has 0 declaration hits elsewhere in the
 tree.
 - Test/ProbeFreyd423.v mirrors the [Require] list and carries 3
 refutation commands (1 instrument + N1 UNIVERSE + N2 TYPING), each
 stripped one at a time in a copy of the whole file; the involution
 readback at [eq_refl]; three positive controls (the canonical
 witness, the injection of item (5), [Small] coexisting with products
 over the category's own arrows); guard coverage 25 identifier tokens
 inside the refutations / 14 also named outside, comments stripped,
 with eleven exhaustive exceptions (the keyword, seven binder names
 and keywords of the record literal, the notation token [op], the
 refuted declaration's name, the absent name); rename-simulated 6/6
 ([ArrowIndex], [DiscreteCat_Functor], [limit_is_indexed_product],
 [TotalMor], [ai_dec_enc], [complete_iprod], each renamed throughout
 a copy) with every first break on a positive line.  [make todo]
 grows by those 3 lines only (2209 → 2212), so the issue's “adds no
 new hits” box is not met as written; disclosed.

 NOT DELIVERED.
 - Thinness WITHOUT [DecHom]: not provable here (Hyland), and the wall
 is pinned positively by [fr_inj_injective]; the issue's “scope it
 classically” remedy is replaced by the explicit hypothesis, which
 keeps the file axiom-free.
 - The issue's pinned [small_complete_has_glbs] under that name: the
 statement needs no smallness (item (7)), so it is [complete_has_glbs].
 - A cardinal number for a category's morphisms (Riehl 3.7.2 as
 arithmetic): only the order hypothesis [ArrowIndex] is introduced,
 so the issue's riehl:3.7:def2 checkbox is NOT met as written
 (disclosed beside the [make todo] box).
 - A non-trivial in-tree category satisfying [ArrowIndex] + [Complete]
 + [DecHom] (the terminal category does, trivially); the theorem is
 conditional, and docs/INHABITATION.md is not edited here.
 - A [HasIndexedProducts C] CLASS instance from [Complete C]: only the
 elementary [IsIndexedProduct] per family is built (item (6)), which
 is what the kernel consumes; the class's single index universe was
 not attempted.
 - Relocating Instance/Fun/Discrete.v's [cantor_bool] to Lib/; pointers
 in Adjunction/GAFT.v and Instance/Poset.v (surfaced for John).
 - No edit to Structure/Thin.v, Theory/Size.v, Instance/Proset/Limit.v,
 Structure/Limit/Comparison.v or Instance/Fun/Discrete.v. 

 --------
 Mac Lane §V.2 命题 3（书 P. 114；maclane:V.2:prop3）；Awodey §9.8 命题 9.34（awodey:9.8:prop34）；Riehl §3.7 命题 3.7.3（riehl:3.7:prop3）及结语 §E.1（riehl:E.1:thm-large-products-poset）；Riehl 的定义 3.7.2（riehl:3.7:def2）是作为大小度量的命题 3.7.3 所针对的，并在此作为一个序（[ArrowIndex]）使用，而不是作为基数提供——按原文其复选框未被满足（见“未提供”）。nLab: https://ncatlab.org/nlab/show/complete+small+category背景。Freyd 的论证：如果一个具有由自身箭头集合索引的积的范畴承载两个不同的平行箭头 f, g : a ⇉ b，那么在每个索引上选择“f 或 g”的 2^K 种情况将给出 2^K 条箭头进入 b 的 K 重幂，比总共有的 K 条箭头还多 —— Cantor 定理。因此，小的完全范畴是一个预序，而重要的完全性是针对大的范畴；Adjunction/GAFT.v 和 Instance/Poset.v 记录了对伴随函子定理的影响，而 Structure/Complete.v 则陈述了这一点。名字相近：
 Structure/Premonoidal/Freyd.v 是关于 Freyd 范畴（前单范畴），无关；
 Structure/Limit/FromProducts.v 在其 [ArrowIx] 索引类型周围打开一个 [Section ArrowIndex]（section 名称不会在 [End] 中保存，所以不会冲突），而 Theory/Size.v 的 [TotalMor] 是与 Σ 类型相同的概念——条目（2）的见证使用了它。陈旧前提，重新测量。该问题的“已验证缺席”段落在其四个条款中有三个是错误的；两个文件的发布时间都晚于该问题文本。- “无薄范畴谓词”：Structure/Thin.v [Thin C := ∀ x y (f g : x ~> y), f ≈ g]，与 [Thin_Opposite] / [Opposite_Thin], [thin_preorder], [thin_PreOrder] 和 [HomChoice]，全部在此处使用。- “无小性质谓词，无全局箭头集合”：Theory/Size.v 的 [LocallySmall], [Small] 和 [TotalMor C := {x & {y & x ~> y}}]；Adjunction/SAFT.v 的“无大小/小性质机制”在小性质方面已过时。[Small] 故意未使用（如下）。- “除有限计数器外没有基数词汇”：正确，并且没有新增——但计数器是 Theory/Metacategory.v 的 [cardinality]，该问题在错误的位置引用了它，就像它引用该常数的注释“计算恒等箭头”以及 [ThreeArrows_card_3]；并且它计算对象，所以它也不是 Riehl 3.7.2。- Cantor 步骤在树中：Instance/Fun/Discrete.v 的 [cantor_predicates] 和 [cantor_bool]（四行）。一个 Structure/ 文件不需要 Instance/Fun，所以下面的 [freyd_cantor_bool] 是一个有名的双胞胎；将原件迁移到 Lib/ 是显现出来的，并未执行。- #422 已经上线：Instance/Proset/Limit.v 的 [proset_Complete_iff_all_meets]，被第 (7) 项使用。- 可判定的对象相等性在树中：Construction/Quotient.v 的 [ObjDecEq]（一个定义性类；[obj_uip] 是其上的 [UIP_dec]），由项目（2）使用。之前的修订声明了一个重复的 [DecObj]，具有相同的陈述；审核发现了这个双胞胎。- 散文位置：问题指向 Structure/Complete.v 的指针对于 Freyd 段落和 Hyland 警告都是陈旧的，其指向 Instance/Poset.v 句子的指针也是如此；指向 GAFT.v 的是正确的。仍然缺失，已测量：[SmallCategory] / [is_small]（0 次命中），一个态射基数，以及任何 [Complete C → HasIndexedProducts] 桥（每个使用者都是手工构建其积，例如 SAFT.v）。交付的内容是什么（38 个常量，每个都在全局上下文下封闭）。(1) 小性证据。[ArrowIndex C]：一种类型 [ai_index]，带有每个箭头的编码和相对于默认值的解码，其往返变换在每个默认值上都是同一映射（高至 [≈]）——即对于每个有值的 Hom 集合，|hom x y| ≤ |ai_index|，Riehl 的“与其自身基数一样大的族的积”，因此该定理涵盖大范畴并解除她 §3.7 的更强假设；对偶 [ArrowIndex_op] 在每个字段上具有相同的数据（空约束块），通过 [@Build_ArrowIndex (C^op)]，因为匿名文字被拒绝（探针 N2），并且它在 [eq_refl] 上是一个自反映射（探针）。没有引入基数算术：该证明使用了“顺序不大于 K”，这是 Riehl 的定义 3.7.2 用途所在；如实披露。Theory/Size.v 的 [Small] 没有被使用：它通过 [ObjEq] 传输根据 Hom 集进行调整，而证明需要一个索引类型来适用于所有箭头。(2) 证明者并非空洞。在 Construction/Quotient.v 的 [ObjDecEq C]（可判定对象等式）、[td] / [td_enc]（在请求的端点上解码捆绑箭头，通过 Coq.Logic.Eqdep_dec 的 [UIP_dec] —— 一个定理，而非公理，进行往返）、[canonical_ArrowIndex : ObjDecEq C → ArrowIndex C] 在索引 [TotalMor C] 上。每个具有可判定对象等式的范畴都有一个 [ArrowIndex]，不论是稀薄还是非稀薄；定理的力量体现于该索引上的积上。(终端类别满足条目(6)的所有三条假设，因此它们是可以联合满足的；没有展示非平凡的树内实例。)
 (3) 构造核心。 [FreydCore] 节点消耗一个基本的 [IsIndexedProduct (fun _ : K => b) P pr] 和一个布尔分隔符 [sep]，作用于对 ([sep_resp], [sep f = true], [sep g = false])：[fr_mk]（2^K条箭头）、[fr_decode] / [fr_decode_mk]（读取回选择）、[fr_rd] / [fr_rd_enc]（索引覆盖 [a ~> P]）、[fr_Fam_surjective]（因此覆盖 [K → bool]）、以及通过 [freyd_cantor_bool] 的 [freyd_no_separated_pair : False]。没有公理、没有排中律、没有可判定性、没有 [Set]。 
 (4) 可判定同态的稀薄性。[DecHom C := ∀ x y (u v : x ~> y), (u ≈ v) + (u ≈ v → False)] (a [sum] : [≈] 是类型值, Lib/Setoid.v), 分隔符 [fr_sep h := if D h f then true else false] 与 [fr_sep_resp] / [fr_sep_f] / [fr_sep_g], 以及 [freyd_thin : ArrowIndex C → HasIndexedProducts C → DecHom C → Thin C]; [freyd_thin_canonical] 在 [ObjDecEq]; [DecHom_op] 和 [freyd_thin_dual] ([C^op] 中的积，Riehl §E.1 的“或余积”，通过 [Opposite_Thin]). (5) 墙，已定位。从 [f ≉ g] 单独——无分隔符，无可判定性——[fr_mk_injective] (最多到 [≈] 的单射) 和 [fr_inj_injective]: 一个精确的注入 [(K → bool) → K]。要反驳它需要一个左逆，即在每个索引处测试该腿是 f 还是 g，也就是说.[DecHom]；Russell/Cantor 对 Prop 值族的非注入论证（由树中没有常量 — Instance/Fun/Discrete.v 的 [cantor_predicates] 是满射形式）不可用，因为该族需要一个 BOOLEAN 选择。这正是 Hyland 的有效拓扑对偶反例（Structure/Complete.v）：在没有 [DecHom] 的情况下，该定理在构造上不可证明，这就是为什么判定器是一个显式假设，而 [Print Assumptions] 保持闭合。探针携带注入作为正控制，没有反驳，因为不可证明性属于元理论。（6）来自 [Complete]，在没有 [Set] 引脚的情况下。第 [CompleteBridge] 节：
 [complete_iprod_obj] / [complete_iprod_proj] /[complete_iprod :
 IsIndexedProduct d …] 对于任意 [d : A → C]，通过
 Structure/Limit/Comparison.v 中带注释的 [DiscreteCat_Functor'] 和
 [discrete_IsIndexedProduct_of_IsLimitCone]；未注释路径针脚 C 的同态层级到 [Set]（探针 N1，“无法强制 Set = uh”），
 并且该针脚的承载体是 Structure/Limit/Product.v 的 [limit_is_indexed_product]，其绑定器是 [C : Category@{_ Set Set}] —  [DiscreteCat_Functor] 自身的绑定器使 C 自由；它发出一个具有 [Set] 同态的形状，并且极限词汇表将该形状的同态层级与环境的同态层级识别（如下方 UNIVERSES 节的方程式）。这是树缺失的 [Complete → IsIndexedProduct] 桥梁。然后问题固定了
 [small_complete_is_thin : ArrowIndex C → Complete C → DecHom C →
 Thin C] 和 [small_cocomplete_is_thin] （Riehl §E.1 的完全余半，通过 Construction/Product/Limit.v 的 [Complete_op_of_Cocomplete]）。 (7) 第二部分：最大下界。[complete_has_glbs :
 Complete C → HomChoice C → HasAllMeets (thin_preorder C)]：一个积在任何范畴的前序反射中都是最大下界——既不涉及小性也不涉及稀薄性，这就是为什么问题固定的名称 [small_complete_has_glbs] 没有被声明（一个声明假设而陈述不使用该假设的名称）。
 唯一的假设是 [HomChoice] （Structure/Thin.v）：下界是 [inhabited] 压缩的，并且中介需要箭头。[complete_Proset_Complete : 完全 C → HomChoice C → 完全 (Proset (thin_PreOrder C))] 与 #422 的 [proset_Complete_iff_all_meets] 闭合了循环。(8) PROSE. Structure/Complete.v 现在指向 [small_complete_is_thin] / [complete_has_glbs] 并将 [DecHom] 命名为构造性假设 — 两个编辑都是行中性，因此引用 Instance/Sets/Products.v 转到该文件仍然对应 Freyd 的陈述。GAFT.v 和 Poset.v 未被修改（指针已显现，但未添加）。宇宙（由 [About] 在 [Set Printing Universes] 下对所有 38 个常量测量）。- 38 个块中有 35 个没有宇宙方程。[CompleteBridge] — [complete_iprod]、[complete_iprod_obj]、[complete_iprod_proj] 部分中的三个块——每个都包含 [o = u0]、[h = p]、[h = uh]、[h = up] 和 [uh = up]：极限词汇用 C 标识形状的 hom 和证明级别，用 [Complete] 的索引标识形状的对象级别，Adjunction/SAFT.v 以散文记录的事实，以及 FromProducts.v 项以 [u2 = u4] 表示。没有方程达到内核，[freyd_thin]、[small_complete_is_thin]、[complete_has_glbs] 或 [complete_Proset_Complete]。(早期的修订版本说“任何区块中都没有宇宙方程”；审计测量了这五个。) [ArrowIndex@{u u0 u1} : Category@{u0 u1 u1} → Type@{max(u+1,u0,u1)}] 和 [ArrowIndex_op@{u u0 u1}] 携带空区块——索引级别 [u] 与 C 的级别无关；[DecHom]、[DecHom_op] 和 [fr_sep] 仅携带上界 [u0 <= u]、[u1 <= u]，将 C 的级别置于结果类型之下。- 内核完全不携带标准库上界：[freyd_no_separated_pair @{u u0 u1 u2} : ∀ {C : Category@{u u0 u0}} (AI : ArrowIndex@{u1 u u0} C) …, IsIndexedProduct@{u1 u2 u u0} …] 仅有 [u0 <= u2]、[u1 <= u2]。[freyd_thin@{u u0 u1 u2 u3}] 仅增加 [False_rect.u0]。- 标准见证：[td] 仅由 [eq_rect.u0/u1] 和 [Projections.u0/u1] 限定；[td_enc]、[canonical_ArrowIndex] 和 [freyd_thin_canonical] 增加了 [Eqdep_dec.UIP_dec.u0] 和 [eq_rect_r.u1] —— [UIP_dec] 的价格（早期版本还将 [UIP_dec] 应用于 [td]，并省略了 [Projections]）。[fr_inj_injective] 携带 [eq_rect.*] / [eq_rect_r.u1]（在 [=] 上重写）。- [Complete] 提供的常数（[complete_iprod_obj/proj]、[complete_iprod]、[small_complete_is_thin]、[small_cocomplete_is_thin]、[complete_has_glbs]、[complete_Proset_Complete]）继承了 [JMeq.u0 <= JMeq.u1]，[EqdepFacts.eq_sigT_sig_eq.u2] 和 [eq_rect_r.u1] 的界限通过 [DiscreteCat_Functor']（Comparison.v 的头属性将其归于程序辅助），加上 [eq.u0]、[eq_ind.u0]、[Logic_lemmas.equality.u0] 在形状级别上。- [small_complete_is_thin@{u u0 u1 u2 u3} : ∀ {C : Category@{u2 u3 u3}},
 ArrowIndex@{u0 u2 u3} C → Complete@{u u0 u3 u2} → DecHom@{u1 u2 u3} C
 → Thin@{u1 u2 u3} C] 与 [u0 <= u]（索引层级位于形状对象层级之下 [Complete] 所量化）且没有 [Set]。- 在任何区块中唯一的 [Set]：[complete_Proset_Complete] 得出 [Complete@{u u Set u0}] — [Proset] 的同态层级，其同态继承自 Instance/Proset/Limit.v 的陈述。计数与约定。- 38 个常量（19 个 [def]，14 个 [prf]，4 个 [proj]，1 个 [rec] 在 [.glob] 中声明；构造函数 [Build_ArrowIndex] 仅作为 [R … constr] 引用出现，因此不在 38 个之中；早期版本计数为 39，包含重复的 [DecObj]），全部“在全局上下文下关闭”，零 [Axioms:] 行，全部完全限定并受控。十三个 [Qed]；一个 [Defined]（ZW174WZZ，数据：[HasAllMeets] 为 [sigT] 值），它可以自由翻转为 [Qed] 并按数据约定保持 [Defined]。- 闭包72个文件（不包括自身）：Instance/Proset/Limit.v 在边际成本为23（第7项的词汇和#422的定理），Structure/Limit/Comparison.v 7，Construction/Product/Limit.v 4，Construction/Quotient.v、Structure/Thin.v 和 Theory/Size.v 各1，其余十个 [Require] 为0（之前的修订还需要 Category.Theory.Functor，一个可删除的 [Require]；已删除）。没有冲突：每个新名称在树的其他位置的声明命中数为0。- Test/ProbeFreyd423.v 镜像了 [Require] 列表，并包含 3 个反驳命令（1 个工具 + N1 UNIVERSE + N2 TYPING），每个命令在整个文件的副本中一次性去掉；在 [eq_refl] 处进行了反演回读；三个阳性对照（规范证据、项目 (5) 的注入、[Small] 与类别自身箭头上的产物共存）；反驳中有 25 个标识符令牌受到保护覆盖 / 另外 14 个在外部也命名，注释已被去掉，有十一项详尽例外（关键字、七个绑定器名称及记录字面量的关键字、符号令牌 [op]、被反驳声明的名称、缺失的名称）；重命名模拟 6/6（[ArrowIndex]、[DiscreteCat_Functor]、[limit_is_indexed_product]、[TotalMor]、[ai_dec_enc]、[complete_iprod]，每个均已重命名整个过程中（复制）在每个正向行的第一次断裂处。[make todo] 
 只增长了那三行（2209 → 2212），所以按照原文，问题的“没有新增命中”框未满足；已披露。未交付。- 在没有 [DecHom] 的情况下的稀薄性：在此无法证明（Hyland），且该墙被 [fr_inj_injective] 正确固定；该问题的“经典范围”补救方法被显式假设取代，从而文件保持无公理。- 在该名称下固定的 [small_complete_has_glbs]：陈述不需要小性（项目 (7)），因此它是 [complete_has_glbs]。- 关于一个范畴的态射的基数（Riehl 3.7.2 作为算术）：仅引入了顺序假设 [ArrowIndex]，因此按原文书写，问题的 riehl:3.7:def2 复选框未被满足（在 [make todo] 旁边披露）。- 一个非平凡的树内范畴满足 [ArrowIndex] + [Complete] + [DecHom]（终范畴显然满足）；该定理是有条件的，docs/INHABITATION.md 在此未编辑。- 来自 [Complete C] 的 [HasIndexedProducts C] 类实例：每个族只构建了基础的 [IsIndexedProduct]（第 (6) 项），这是内核所使用的；类的单索引宇宙未尝试构建。- 将 Instance/Fun/Discrete.v 中的 [cantor_bool] 移动到 Lib/；在 Adjunction/GAFT.v 和 Instance/Poset.v 中的指针已更新（为 John 提供）。- 未修改 Structure/Thin.v、Theory/Size.v、Instance/Proset/Limit.v、Structure/Limit/Comparison.v 或 Instance/Fun/Discrete.v。
*)

(* * ** The Cantor step, as a boolean diagonal / * **康托步，作为布尔对角线 *)

(*
 Twin of Instance/Fun/Discrete.v's [cantor_bool], re-proved here
 because a Structure/ file does not require Instance/Fun.  Relocating the
 original to Lib/ is surfaced, not done. 

 --------
 Instance/Fun/Discrete.v 的 [cantor_bool] 的双胞，重新在此证明，因为 Structure/ 文件不需要 Instance/Fun。将原文件移至 Lib/ 是显示出来的，并未执行。
*)
Theorem freyd_cantor_bool {A : Type} (f : A → A → bool) :
  ¬ (∀ g : A → bool, exists a : A, ∀ x : A, f a x = g x).
Proof.
  intro H.
  destruct (H (fun x => negb (f x x))) as [a Ha].
  specialize (Ha a).
  destruct (f a a); discriminate.
Qed.

(* * ** The smallness witness the proof consumes / * ** 小小的目击了证明所消耗的 *)

(*
 [ai_index] is a single type indexing ALL the arrows of C: every hom-set
 is a retract of it RELATIVE TO A DEFAULT.  The default makes [ai_dec]
 total without asking the caller to decide anything, and the law says the
 round trip is the identity up to the hom-setoid, for every default.
 Content: |hom x y| ≤ |ai_index| for every inhabited hom-set — Riehl's
 “products of families as large as its own cardinality” (§3.7 Prop 3), so
 the theorem covers large categories.  Theory/Size.v's [Small] is
 deliberately NOT consumed: it resizes per hom-set through [ObjEq]
 transports, and the proof needs one index type for all arrows. 

 --------
 [ai_index] 是一个单一类型，用于索引 C 的所有箭头：每个同态集合都是它相对于默认值的重traction。默认值使 [ai_dec] 成为全体的，而无需调用者做任何决定，并且定律表明，对于每个默认值，往返映射在同态集合上同构下是恒等映射。内容：对于每个非空的同态集合 |hom x y| ≤ |ai_index|——Riehl 的“族的乘积与其自身基数一样大”（§3.7 命题 3），因此定理涵盖了大范畴。Theory/Size.v 中的 [Small] 是故意不被消耗的：它通过 [ObjEq] 传输在每个同态集合上重新调整大小，证明需要一个索引类型来表示所有箭头。
*)
Record ArrowIndex (C : Category) := {
  ai_index   : Type;
  ai_enc     : ∀ {x y : C}, (x ~> y) → ai_index;
  ai_dec     : ∀ {x y : C}, ai_index → (x ~> y) → (x ~> y);
  ai_dec_enc : ∀ {x y : C} (h d : x ~> y), ai_dec (ai_enc h) d ≈ h
}.

Arguments ai_index {C} _.
Arguments ai_enc {C} _ {x y} _.
Arguments ai_dec {C} _ {x y} _ _.
Arguments ai_dec_enc {C} _ {x y} _ _.

(*
 The dual is field for field the same data ([hom[C^op] x y] is [hom[C] y x]
 definitionally).  The constructor must be applied at [C^op] explicitly:
 the anonymous record literal elaborates its binders at [obj[C]] and is
 refused against [ArrowIndex (C^op)] (probe). 

 --------
 对偶在每个字段上都是相同的数据（[hom[C^op] x y] 定义上是 [hom[C] y x]）。构造函数必须在 [C^op] 显式应用：匿名记录字面量在 [obj[C] 处展开其绑定器，并且在 [ArrowIndex (C^op)]（探测）处被拒绝。
*)
Definition ArrowIndex_op {C : Category} (AI : ArrowIndex C) :
  ArrowIndex (C^op) :=
  @Build_ArrowIndex (C^op) (ai_index AI)
    (fun x y h => ai_enc AI h)
    (fun x y m d => ai_dec AI m d)
    (fun x y h d => ai_dec_enc AI h d).

(* * ** The canonical witness: decidable object equality suffices / * ** 规范的见证者：可判定的对象相等性足够 *)

(*
 Decidable object equality is Construction/Quotient.v's [ObjDecEq]
 (a definitional class: an instance IS the decider), consumed as is —
 an earlier revision declared a duplicate [DecObj]; the audit found the
 twin. 

 --------
 可判定的对象相等是 Construction/Quotient.v 的 [ObjDecEq]（一个定义类：一个实例就是判定器），原样使用——早期版本声明了一个重复的 [DecObj]；审计发现了这个双胞胎。
*)

(* Decode a bundled arrow at a requested pair of endpoints, falling back on the default when the endpoints do not match. No universe binders are written here on purpose: stdlib [eq] is pinned to a global universe on Coq 8.19/8.20 (Theory/Size.v). / 在请求的一对端点处解码一个捆绑箭头，当端点不匹配时回退到默认值。这里刻意没有写任何宇宙绑定器：stdlib [eq] 在 Coq 8.19/8.20（Theory/Size.v）中被固定到全局宇宙上。 *)
Definition td {C : Category} (DO : ObjDecEq C) {x y : obj[C]}
  (m : TotalMor C) (d : x ~> y) : x ~> y :=
  match DO (projT1 m) x with
  | left ex =>
      match DO (projT1 (projT2 m)) y with
      | left ey =>
          eq_rect (projT1 m) (fun u => u ~> y)
            (eq_rect (projT1 (projT2 m)) (fun v => projT1 m ~> v)
               (projT2 (projT2 m)) y ey)
            x ex
      | right _ => d
      end
  | right _ => d
  end.

Lemma td_enc {C : Category} (DO : ObjDecEq C) {x y : obj[C]} (h d : x ~> y) :
  td DO (existT _ x (existT _ y h)) d ≈ h.
Proof.
  unfold td; simpl.
  destruct (DO x x) as [ex | ne]; [| destruct (ne eq_refl)].
  destruct (DO y y) as [ey | ne]; [| destruct (ne eq_refl)].
  rewrite (UIP_dec DO ex eq_refl).
  rewrite (UIP_dec DO ey eq_refl).
  reflexivity.
Qed.

(*
 EVERY category with decidable object equality carries an [ArrowIndex] at
 its own total arrow collection (Theory/Size.v's [TotalMor]).  So the
 hypothesis is not disguised thinness or finiteness: the strength of the
 theorem sits in the products at that index. 

 --------
 每一个具有可判定对象等式的范畴在其自身的全箭头集合上都带有一个 [ArrowIndex]（Theory/Size.v 的 [TotalMor]）。因此，这个假设并不是伪装的稀薄性或有限性：定理的力量体现在该索引处的积上。
*)
Definition canonical_ArrowIndex {C : Category} (DO : ObjDecEq C) :
  ArrowIndex C :=
  {| ai_index   := TotalMor C
   ; ai_enc     := fun x y h => existT _ x (existT _ y h)
   ; ai_dec     := fun x y m d => td DO m d
   ; ai_dec_enc := fun x y h d => td_enc DO h d |}.

(* * ** The separated-pair core, fully constructive / * ** 分离对核心，完全构造的 *)

(*
 The core consumes ONE elementary product: the [K]-fold power of [b],
 given as an [IsIndexedProduct] of the constant family.  Both the class
 [HasIndexedProducts] and a [Complete] instance feed it below. 

 --------
 核心消耗一个基本产品：[K] 的 [b] 次幂，作为常量族的 [IsIndexedProduct] 给出。[HasIndexedProducts] 类和一个 [Complete] 实例在下面为其提供输入。
*)
Section FreydCore.

Context {C : Category}.
Context (AI : ArrowIndex C).
Context {a b : C}.
Context (f g : a ~> b).

Notation K := (ai_index AI).

Context (P : C) (pr : K → (P ~> b)).
Context (HP : IsIndexedProduct (fun _ : K => b) P pr).

(* A boolean separator for the pair, respecting the hom-setoid. / 用于该对的布尔分隔符，遵守同类集合公理。 *)
Context (sep : (a ~> b) → bool).
Context (sep_resp : ∀ u v : a ~> b, u ≈ v → sep u = sep v).
Context (sep_f : sep f = true).
Context (sep_g : sep g = false).

(*
 The [2^K]-indexed family of arrows [a ~> P]: at index [k] choose [f] or
 [g] according to [phi k]. 

 --------
 [2^K] 索引的箭头系列 [a ~> P]：在索引 [k] 处，根据 [phi k] 选择 [f] 或 [g]。
*)
Definition fr_mk (phi : K → bool) : a ~> P :=
  unique_obj (iprod_desc HP (fun k => if phi k then f else g)).

Lemma fr_mk_commutes (phi : K → bool) (k : K) :
  pr k ∘ fr_mk phi ≈ (if phi k then f else g).
Proof.
  exact (unique_property (iprod_desc HP (fun k => if phi k then f else g)) k).
Qed.

(* Reading the choice back off an arrow, one index at a time. / 逐一用手指读出箭头上的选项。 *)
Definition fr_decode (h : a ~> P) : K → bool := fun k => sep (pr k ∘ h).

Lemma fr_decode_mk (phi : K → bool) (k : K) : fr_decode (fr_mk phi) k = phi k.
Proof using sep_resp sep_f sep_g.
  unfold fr_decode.
  rewrite (sep_resp _ _ (fr_mk_commutes phi k)).
  destruct (phi k); assumption.
Qed.

(* Smallness turns [K] into a surjection onto the hom-set [a ~> P] ... / 小性将 [K] 转化为指向同态集合 [a ~> P] 的满射... *)
Definition fr_rd (k : K) : a ~> P := ai_dec AI k (fr_mk (fun _ => true)).

Lemma fr_rd_enc (h : a ~> P) : fr_rd (ai_enc AI h) ≈ h.
Proof. exact (ai_dec_enc AI h (fr_mk (fun _ => true))). Qed.

(* ... and hence into a K-indexed family of elements of [K → bool]. / ... 因此形成了一个以 K 为索引的 [K → bool] 元素族。 *)
Definition fr_Fam : K → K → bool := fun k => fr_decode (fr_rd k).

Lemma fr_Fam_surjective :
  ∀ phi : K → bool, exists k : K, ∀ i, fr_Fam k i = phi i.
Proof using sep_resp sep_f sep_g.
  intro phi.
  exists (ai_enc AI (fr_mk phi)).
  intro i.
  unfold fr_Fam, fr_decode.
  rewrite (sep_resp _ _ (compose_respects _ _ (reflexivity (pr i))
                           _ _ (fr_rd_enc (fr_mk phi)))).
  exact (fr_decode_mk phi i).
Qed.

(*
 THE CORE.  No axioms, no classical logic, no decidability: a parallel
 pair separated by a boolean predicate cannot exist in a category whose
 arrows are indexed by [K] and which has the [K]-fold power of [b]. 

 --------
 核心。没有公理，没有经典逻辑，没有可判定性：在其箭头由 [K] 索引且具有 [b] 的 [K] 次幂的范畴中，不能存在由布尔谓词分隔的一对平行箭头。
*)
Theorem freyd_no_separated_pair : False.
Proof using All.
  exact (freyd_cantor_bool fr_Fam fr_Fam_surjective).
Qed.

End FreydCore.

(* * ** Decidable hom-setoids reach thinness / * ** 可判定同值类达到稀疏性 *)

(* [≈] is Type-valued (Lib/Setoid.v), so the decider is a [sum]. / [≈] 是 Type 值（Lib/Setoid.v），所以判定器是一个 [sum]。 *)
Definition DecHom (C : Category) : Type :=
  ∀ (x y : C) (u v : x ~> y), ((u ≈ v) + ((u ≈ v) → False))%type.

Definition DecHom_op {C : Category} (D : DecHom C) : DecHom (C^op) :=
  fun x y u v => D y x u v.

(* From a decider, the separator “is it f?” and its three laws. / 来自一个决策者，分隔符“它是 f 吗？”及其三条规律。 *)
Section Separator.

Context {C : Category} (D : DecHom C) {x y : C} (f g : x ~> y)
  (Hne : (f ≈ g) → False).

Definition fr_sep (h : x ~> y) : bool := if D x y h f then true else false.

Lemma fr_sep_resp (u v : x ~> y) : u ≈ v → fr_sep u = fr_sep v.
Proof.
  intro Huv; unfold fr_sep.
  destruct (D x y u f) as [Hu | Hu]; destruct (D x y v f) as [Hv | Hv];
    try reflexivity.
  - destruct (Hv (transitivity (symmetry Huv) Hu)).
  - destruct (Hu (transitivity Huv Hv)).
Qed.

Lemma fr_sep_f : fr_sep f = true.
Proof.
  unfold fr_sep.
  destruct (D x y f f) as [Hff | Hff]; [reflexivity |].
  destruct (Hff (reflexivity f)).
Qed.

Lemma fr_sep_g : fr_sep g = false.
Proof using Hne.
  unfold fr_sep.
  destruct (D x y g f) as [Hgf | Hgf]; [| reflexivity].
  destruct (Hne (symmetry Hgf)).
Qed.

End Separator.

(*
 Mac Lane §V.2 Proposition 3 / Riehl §3.7 Proposition 3.7.3, over the
 class of indexed products: arrows indexed by [K], products over [K],
 decidable hom-setoids ⇒ thin. 

 --------
 Mac Lane §V.2 命题 3 / Riehl §3.7 命题 3.7.3，关于指标积类：箭头由 [K] 指标化，积由 [K] 指标化，可判定的同构集合 ⇒ 薄。
*)
Theorem freyd_thin {C : Category}
  (AI : ArrowIndex C) (HP : HasIndexedProducts C) (D : DecHom C) : Thin C.
Proof.
  intros x y f g.
  destruct (D x y f g) as [Heq | Hne]; [exact Heq |].
  exfalso.
  exact (freyd_no_separated_pair AI f g
           (indexed_product (fun _ : ai_index AI => y))
           (indexed_product_proj (fun _ : ai_index AI => y))
           (indexed_product_ump (fun _ : ai_index AI => y))
           (fr_sep D f) (fr_sep_resp D f) (fr_sep_f D f) (fr_sep_g D f g Hne)).
Qed.

(* Assembled at C's own arrow collection. / 在C自己的箭矢收藏中组装。 *)
Definition freyd_thin_canonical {C : Category}
  (DO : ObjDecEq C) (HP : HasIndexedProducts C) (D : DecHom C) : Thin C :=
  freyd_thin (canonical_ArrowIndex DO) HP D.

(* Riehl §E.1's “or coproducts”: products in [C^op], thinness self-dual. / Riehl §E.1 的“或余积”：在 [C^op] 中的积，自对偶的稀薄性。 *)
Definition freyd_thin_dual {C : Category}
  (AI : ArrowIndex C) (HP : HasIndexedProducts (C^op)) (D : DecHom C) : Thin C :=
  Opposite_Thin (freyd_thin (ArrowIndex_op AI) HP (DecHom_op D)).

(* * ** The constructive wall, located: an injection [(K → bool) ↣ K] from [f ≉ g] alone / * ** 建设性的墙，位置：一次注射 [(K → bool) ↣ K] 来自 [f ≉ g] 单独 *)

Section Wall.

Context {C : Category}.
Context (AI : ArrowIndex C).
Context {a b : C} (f g : a ~> b) (Hne : (f ≈ g) → False).

Notation K := (ai_index AI).

Context (P : C) (pr : K → (P ~> b)).
Context (HP : IsIndexedProduct (fun _ : K => b) P pr).

(* [fr_mk] is injective UP TO the hom-setoid, from [f ≉ g] alone — no separator, no decidability, no classical logic. / [fr_mk] 在同态集合意义上是单射的，仅从 [f ≉ g] 本身——没有分隔符，没有可判定性，没有经典逻辑。 *)
Lemma fr_mk_injective (phi psi : K → bool) :
  fr_mk AI f g P pr HP phi ≈ fr_mk AI f g P pr HP psi → ∀ k, phi k = psi k.
Proof using Hne.
  intros Heq k.
  pose proof (fr_mk_commutes AI f g P pr HP phi k) as Hp.
  pose proof (fr_mk_commutes AI f g P pr HP psi k) as Hq.
  assert (Hc : (if phi k then f else g) ≈ (if psi k then f else g)).
  { rewrite <- Hp, <- Hq.
    apply compose_respects; [reflexivity | exact Heq]. }
  destruct (phi k); destruct (psi k); try reflexivity.
  - destruct (Hne Hc).
  - destruct (Hne (symmetry Hc)).
Qed.

(* Composing with the smallness encoding gives an INJECTION [(K → bool) → K] on the nose (Leibniz equality on [K]). / 使用小型编码进行作曲会得到一个注入 [(K → bool) → K]（在 [K] 上的莱布尼茨等式）。 *)
Definition fr_inj (phi : K → bool) : K := ai_enc AI (fr_mk AI f g P pr HP phi).

Lemma fr_inj_injective (phi psi : K → bool) :
  fr_inj phi = fr_inj psi → ∀ k, phi k = psi k.
Proof using Hne.
  intro He.
  apply fr_mk_injective.
  rewrite <- (ai_dec_enc AI (fr_mk AI f g P pr HP phi) (fr_mk AI f g P pr HP phi)).
  rewrite <- (ai_dec_enc AI (fr_mk AI f g P pr HP psi) (fr_mk AI f g P pr HP phi)).
  unfold fr_inj in He; rewrite He; reflexivity.
Qed.

End Wall.

(* * ** From [Complete]: the product at any index, with no [Set] pin / * ** 来自 [Complete] ：在没有 [Set] 引脚的情况下，任何索引的产品 *)

Section CompleteBridge.

Universe o h p uo uh up.

Context {C : Category@{uo uh up}} (comp : @Complete C).

(*
 The limit of the discrete diagram on [d], through the annotated
 [DiscreteCat_Functor'] (Structure/Limit/Comparison.v) — the unannotated
 [DiscreteCat_Functor] pins C's hom and proof levels to [Set] (probe). 

 --------
 在 [d] 上离散图的极限，通过带注释的 [DiscreteCat_Functor']（Structure/Limit/Comparison.v）——未带注释的 [DiscreteCat_Functor] 将 C 的 hom 和 proof 层固定到 [Set]（探针）。
*)
Definition complete_iprod_obj {A : Type@{o}} (d : A → C) : C :=
  vertex_obj[@limit_cone _ _ _
    (comp (DiscreteCat@{o h p} A) (DiscreteCat_Functor' d))].

Definition complete_iprod_proj {A : Type@{o}} (d : A → C) (i : A) :
  complete_iprod_obj d ~> d i :=
  cone_leg (@limit_cone _ _ _
    (comp (DiscreteCat@{o h p} A) (DiscreteCat_Functor' d))) i.

Definition complete_iprod {A : Type@{o}} (d : A → C) :
  IsIndexedProduct d (complete_iprod_obj d) (complete_iprod_proj d) :=
  discrete_IsIndexedProduct_of_IsLimitCone
    (DiscreteCat_Functor' d)
    (@limit_cone _ _ _
       (comp (DiscreteCat@{o h p} A) (DiscreteCat_Functor' d)))
    (@ump_limits _ _ _
       (comp (DiscreteCat@{o h p} A) (DiscreteCat_Functor' d))).

End CompleteBridge.

(*
 The issue's pinned statement: a category whose arrows are indexed by a
 type at which it is complete, with decidable hom-setoids, is thin. 

 --------
 该问题的固定声明：一个箭头由其完全的类型索引的范畴，具有可判定的同态集合，是薄的。
*)
Theorem small_complete_is_thin {C : Category}
  (AI : ArrowIndex C) (comp : @Complete C) (D : DecHom C) : Thin C.
Proof.
  intros x y f g.
  destruct (D x y f g) as [Heq | Hne]; [exact Heq |].
  exfalso.
  exact (freyd_no_separated_pair AI f g
           (complete_iprod_obj comp (fun _ : ai_index AI => y))
           (complete_iprod_proj comp (fun _ : ai_index AI => y))
           (complete_iprod comp (fun _ : ai_index AI => y))
           (fr_sep D f) (fr_sep_resp D f) (fr_sep_f D f) (fr_sep_g D f g Hne)).
Qed.

(* Riehl §E.1's cocomplete half. / Riehl §E.1 的余完半部分。 *)
Definition small_cocomplete_is_thin {C : Category}
  (AI : ArrowIndex C) (cocomp : @Cocomplete C) (D : DecHom C) : Thin C :=
  Opposite_Thin
    (small_complete_is_thin (ArrowIndex_op AI)
       (Complete_op_of_Cocomplete cocomp) (DecHom_op D)).

(* * ** The second half: all greatest lower bounds in the preorder reflection / * ** 下半部分：前序反射中的所有最大下界 *)

(*
 A product is a greatest lower bound in the preorder reflection
 [thin_preorder C] (Structure/Thin.v) of ANY category — smallness and
 thinness play no part.  The one hypothesis is [HomChoice C]: the family
 of lower-bound witnesses is [inhabited]-squashed, and the mediator needs
 the arrows themselves. 

 --------
 一个乘积是在任意范畴的预序反射 [thin_preorder C] (Structure/Thin.v) 中的最大下界——小性和稀薄性没有作用。唯一的假设是 [HomChoice C]：下界证人的族是 [inhabited]-压缩的，且中介需要箭头本身。
*)
Definition complete_has_glbs {C : Category} (comp : @Complete C)
  (ch : HomChoice C) : HasAllMeets (thin_preorder C).
Proof.
  intros Ix d.
  exists (complete_iprod_obj comp d).
  split.
  - intro i; exact (inhabits (complete_iprod_proj comp d i)).
  - intros n Hn.
    exact (inhabits (unique_obj (iprod_desc (complete_iprod comp d)
             (fun i => ch n (d i) (Hn i))))).
Defined.

(*
 Through #422's characterisation (Instance/Proset/Limit.v), the preorder
 reflection of a complete category is itself a complete preorder. 

 --------
 通过 #422 的表征（Instance/Proset/Limit.v），一个完全范畴的预序反射本身是一个完全预序。
*)
Definition complete_Proset_Complete {C : Category} (comp : @Complete C)
  (ch : HomChoice C) : @Complete (Proset (thin_PreOrder C)) :=
  snd (proset_Complete_iff_all_meets (thin_PreOrder C))
      (complete_has_glbs comp ch).
