Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Mon.Coproduct.

Generalizable All Variables.

(* * * The free monoid on a SETOID, and its adjunction at Mon(Sets) / * * 在集合等价类上的自由幺半群，以及它在 Mon(Sets) 中的伴随 *)

(*
 nLab:      https://ncatlab.org/nlab/show/free+monoid
 nLab:      https://ncatlab.org/nlab/show/universal+morphism
 Wikipedia: https://en.wikipedia.org/wiki/Free_monoid

 Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 GTM 5, Springer 1998, §IV.8, Exercise 2 (maclane:IV.8:ex2) — the
 free ring on a set obtained as a composite of free constructions;
 §II.7 Corollary 2, printed pp. 50-51, for the free monoid itself.

 For a SETOID X — a carrier with a chosen equivalence `≈` — the free
 monoid on X is the setoid of finite words over the carrier of X,
 compared LETTERWISE UP TO `≈`, multiplied by concatenation with the
 empty word as unit.  Its universal property is that the insertion of
 one-letter words is universal among Sets-morphisms from X into the
 underlying setoid of a monoid: every h : X ~> U L extends along the
 insertion to one and only one monoid homomorphism, namely the fold
 that replaces concatenation by the multiplication of L and the empty
 word by its unit.

 Everything is developed at [@Mon Sets Sets_Product_Monoidal], the
 category of internal monoids (Theory/Algebra/Monoid.v) in the
 cartesian monoidal category of setoids, with
 [@Mon_Forget Sets Sets_Product_Monoidal] as the underlying-setoid
 functor U.  A monoid object over that base is exactly an ordinary
 setoid monoid: mu : X ∏ X ~> X, eta : 1 ~> X, and the three laws are
 associativity and the two unit laws with the cartesian associator and
 unitors inserted.  Nothing here needs function extensionality: two
 monoid homomorphisms are identified exactly when they agree at every
 word up to `≈`, which is what word induction proves.

 WHY THIS FILE EXISTS: THE Mon(Coq)/Mon(Sets) MEASUREMENT.  Issue #296
 already delivered a free monoid with its universal property and its
 adjunction — but at a DIFFERENT category.
 Instance/Coq/Monoid/Free.v abbreviates
 [MonCoq := @Mon Coq Coq_Monoidal], and it delivers
 [FreeMonoid : Coq ⟶ MonCoq] and
 [free_monoid_adjunction : FreeMonoid ⊣ UMon] over that base.  The
 monoid-ring leg that #400 wants to compose with runs from the OTHER
 category: Instance/Rng/MonoidRing.v sets
 [MonSets := @Mon Sets Sets_Product_Monoidal] and gives
 [MonoidRingFunctor : MonSets ⟶ Rng] with
 [zmring_adjunction : MonoidRingFunctor ⊣ Rng_Forget_Mon].
 Instance/Roster.v names the same category [Mon_Sets].  So the two
 legs of “Sets → Monoids → Rings” did not compose.

 That gap was re-verified here rather than taken on trust, and the
 coordinating measurement stands, with two refinements worth stating.
 (1) Searching the whole tree for a functor whose CODOMAIN is
 [Mon Sets] returns exactly three, and all three are forgetful:
 [Rig_Forget_Mon] (Theory/Algebra/Rig.v),
 [Rng_Forget_Mon] (Instance/Rng/MonoidRing.v) and [Grp_MonSets]
 (Instance/Rng/GroupRing.v); Instance/Roster.v restates the
 first of them at Roster's own name for the category and adds no
 fourth.  There was no free monoid at [Mon Sets] before this file.
 (2) There is no equivalence between [Coq] and [Sets] in tree — but
 the sharper claim “there is no functor at all between them” would be
 FALSE: Instance/Shapes.v declares
 [Trie_Functor (s : Shape) : Coq ⟶ Sets], which is unrelated to any
 comparison of the two categories, and [Sets_discrete]
 (Instance/Sets/Products.v) is an OBJECT-level discrete-setoid
 construction that is nowhere packaged as a functor.  Neither
 transports #296's adjunction, and more to the point transport along
 an arbitrary functor pair would not preserve left-adjointness
 anyway — the free monoid on a SETOID must identify `≈`-equal
 generators, which no discrete-setoid route does.
 That last sentence is an ARGUMENT, not a theorem; what IS proved here
 is the fact it rests on ([free_mon_blur_identifies] against
 [free_mon_two_generators_distinct]).

 Instance/Mon/Coproduct.v names this same wall as the reason
 Awodey §3.2 Exercise 5 (M(A) + M(B) ≅ M(A + B) by preservation of
 colimits) went undelivered there: “the only free-monoid adjunction in
 tree is Instance/Coq/Monoid/Free.v's, which is over [Coq], so no such
 adjoint exists at this category to preserve colimits”.  This file
 removes exactly that obstruction — there is now a left adjoint of
 [Mon_Forget] at [Mon Sets].  The exercise itself is NOT attempted
 here and nothing is claimed about what else its proof would need.

 THE ELEMENT-LEVEL ACCESSORS ARE REUSED, NOT REWRITTEN, AND THE CHOICE
 IS MEASURED.  Two copies of the element-level reading of [Mon Sets]
 already exist — Instance/Rng/MonoidRing.v
 ([mcar]/[mop]/[mone]/[mmap]/[mhom]) and Instance/Mon/Coproduct.v
 ([mon_ob]/[mon_mul]/[mon_one]/[mon_fun]/[mk_mon_obj]/[mk_mon_hom]) —
 and writing a third would have been the wrong move.  The Coproduct.v
 copy is the one imported, for a dependency reason and not a stylistic
 one: MonoidRing.v Requires [Instance.Rng], [Instance.Rng.Algebras],
 [Instance.Rng.Polynomial], [Instance.Rng.Algebras.Associative] and
 [Instance.Mod], so importing it would put the whole ring hierarchy
 behind every consumer of the free monoid — and would invert the
 intended dependency, since the ring-side composite is what will
 consume THIS file.  Coproduct.v Requires only Lib, Category,
 Isomorphism, Morphisms, Monoidal, Cartesian, Cocartesian, Terminal,
 Initial, Monoid, Monoid.Hom and Sets.  No new name for the category
 is introduced here — [MonS] below is a [Local Notation] that does not
 export — so requiring this file alongside MonoidRing.v produces no
 collision with its [MonSets].  A by-product of the import is that
 Coproduct.v's [ListBoolMon] is available as the concrete target for
 the non-vacuity probes, so no new monoid had to be built for them.

 STRENGTHS, MEASURED STRICT-FIRST.  Definitional (shipped as [eq_refl]
 Examples): the carrier, the multiplication, the unit, the underlying
 setoid of the free monoid; the object part of [FreeMonSets]; the
 universal arrow IS the insertion; the unit of the adjunction IS the
 insertion; the fold's value at a literal one-letter word.  Only up to
 `≈`: the counit's action (it is the evaluation of a word in L,
 [free_mon_counit_evaluates]) and the free functor's action on arrows
 ([free_mon_fmap_is_wmap]).  Two strict readings were ATTEMPTED and
 REJECTED, and both are pinned in-file as [Fail] commands with
 positive controls beside them:

 - the counit does not compute.  Its underlying map is
 [unique_obj (ump_universal_arrows ...)], and
 [ump_universal_arrows] (Theory/Universal/Arrow.v) is closed
 with [Qed], so nothing reduces through it.  The diagnosis
 DISCRIMINATES: the UNIT of the same adjunction, which routes
 through the transparent [universal_arrow_from_UMP] instead, IS
 [eq_refl] ([free_mon_unit_is_insert]), so opacity of that one
 constant is the cause and not adjunction plumbing in general.

 CORRECTION (#471): that diagnosis names one of two causes.  Two
 [Qed] constants block the counit: [ump_universal_arrows] and this
 file's own [free_mon_universal], the proof of the factorization
 that [free_mon_universal_arrow] hands to
 [universal_arrow_from_UMP] and from which the counit is read.
 Measured by #471's scout in a 40-file copy containing this file's
 32-module closure, rebuilt after each change: with
 [ump_universal_arrows] alone turned [Defined], NEGATIVE 1 below is
 still refused; with [free_mon_universal] turned [Defined] as well,
 NEGATIVE 1's statement holds, and of the eight conversions the
 monoid monad W₀ (Instance/Mon/Word.v) needs, six read off this
 counit (μ as concatenation, the counit as the fold, the comparison
 functor's values) and two off the free functor's action, all but
 one hold at [eq_refl], the exception being the action at a
 variable word, NEGATIVE 2's stuck [Fixpoint].  Neither
 constant is turned [Defined] here: [ump_universal_arrows] is shared
 by many developments, several of which pin its opacity in probes,
 and issue #1353 tracks it.  #471 adds instead the same adjunction
 in hom-set form, [free_mon_sets_adjunction_hom] below, whose
 counit IS the fold by conversion.

 - [free_mon_extend_insert] is a Leibniz equality but not a
 conversion at a VARIABLE word: [free_mon_extend] is a [Fixpoint]
 and is stuck on a variable.  The control is the same statement at
 a literal one-letter word, where it does hold by [eq_refl] — so
 the obstruction is the stuck recursion, not a mismatch of the two
 sides.  Each step of the induction closes by [reflexivity] with
 no monoid law spent, which is why the theorem is stated at
 Leibniz `=` rather than at `≈`.

 NON-VACUITY.  Two independent routes to the same separation, and the
 difference between them is worth recording.  Unlike
 Instance/Mon/Coproduct.v's [fp_eq] and the other generated
 congruences in this tree, [word_eq] is a STRUCTURAL congruence
 defined by recursion on the two words, so it is open to inversion
 and a negative IS reachable directly: [free_mon_insert_reflects] inverts
 one [we_cons] to recover `≈` of the letters, giving
 [free_mon_two_generators_distinct] in three lines.  The map-out route
 is supplied as well and shares no proof text with it
 ([free_mon_two_generators_distinct_via_probe],
 [free_mon_word2_not_letter]), evaluating in Coproduct.v's
 [ListBoolMon] through the universal property; the fold's value there
 COMPUTES ([two_probe_word2] is [eq_refl]).  The setoid half is the
 point of doing this at [Sets] rather than at [Coq]:
 [free_mon_blur_identifies] exhibits two `≈`-equal but
 Leibniz-distinct generators that the free monoid IDENTIFIES, against
 [free_mon_two_generators_distinct] over the discrete setoid on the
 same carrier, where it does not.

 UNIVERSES.  Read off the constraint blocks, not the binders:
 [FreeMonSetsObject@{u u0}], [FreeMonSets@{u u0 u1 u2 u3}] and
 [free_mon_sets_adjunction@{u u0 u1 u2 u3 u4}] contain NO [Set]
 anywhere — no [Set] universe instance and no constraint mentioning
 it — and the only strict inequality among the two levels that matter
 is [Sets]'s own [o < so] ([Instance/Sets.v] declares
 [Sets@{o so} : Category@{so o o}]).  That is guarded rather than
 merely measured: the section [FreeAboveSet] at the end of this file
 declares [Constraint Set < uo] and elaborates all three constants at
 levels strictly above [Set].  So this file introduces no size
 restriction of its own.  Note that the [Set] pin CLAUDE.md records
 for [Rig_Forget_Mon] — and hence for [Rng_Forget_Mon] — is on the
 RING side and is untouched here, but it DOES reach the composite, and
 that was measured rather than guessed: in a scratch file out of tree
 requiring both this module and Instance/Rng/MonoidRing.v, the
 composite [MonoidRingFunctor ◯ FreeMonSets] elaborates, and its
 constraint block reads [Sets@{Set u} ⟶ Rng@{u Set}] with this file's
 own functor instantiated there at [FreeMonSets@{Set u _ _ _}].  So
 the pin is inherited from the ring leg and is not required by
 anything here — but a consumer building the free ring through
 monoids will carry it.  That composite is NOT built in this file and
 nothing here is guarded against the outcome; the measurement is
 reported so that the composite's author does not have to rediscover
 it.

 THE HOM-SET FORM (#471).  Two packagings of the one adjunction
 FreeMonSets ⊣ UMonS are kept.  [free_mon_sets_adjunction], from the
 universal arrows, is the one the free ring of Instance/Rng/Free.v and
 the rest of the tree consume, and it is unchanged.
 [free_mon_sets_adjunction_hom] is Theory/Adjunction.v's
 [Build_Adjunction'] applied to the natural bijection
 [free_mon_hom_iso], with the same left adjoint [FreeMonSets], the same
 right adjoint and the same insertion: its unit and its forward
 transpose ARE those of [free_mon_sets_adjunction] at [eq_refl]
 ([free_mon_hom_unit], [free_mon_hom_to]), and its inverse transpose is
 the fold [free_mon_hom], so its counit is the fold of the identity at
 [eq_refl] ([free_mon_hom_counit]), where the other counit is that fold
 only at `≈` ([free_mon_counit_evaluates]).  It exists for the monad
 W₀ of Mac Lane's §VI.4 Exercise 1 (Instance/Mon/Word.v), whose
 multiplication U ε F and comparison functor then compute.  It is not
 a second free monoid and not a second free functor: the action on
 arrows is still [FreeMonSets]'s, the letterwise map only at `≈`
 ([free_mon_fmap_is_wmap]).  The two adjunctions are refused equal at
 [eq_refl], and so are their counits at a variable word
 (Test/ProbeWord471.v).  Its universes: [free_mon_hom_iso] and
 [free_mon_sets_adjunction_hom] bind @{o so} and the three further
 levels of [FreeMonSets] (four on Coq 8.19/8.20), with no [Set], the
 adjunction pinned to [Adjunction@{so o o so o o o o so o so}] as
 Instance/Smgrp.v pins its own.  Issue #1353 records the exit: once
 [ump_universal_arrows] and [free_mon_universal] are transparent, one
 record is kept and W₀ is rebased on it.

 WHAT IS DELIBERATELY NOT DELIVERED.  No normal form for words beyond
 the list representation itself, hence no decision procedure for
 [word_eq] beyond what a decidable letter setoid would give, and no
 length or degree invariants.  No comparison whatever with
 Instance/Coq/Monoid/Free.v's [FreeMonoid]: the two are NOT related
 here, neither is claimed to determine the other, and no functor
 between the two ambient categories is built (doing so would drag that
 file's own closure — Comma, FAlg, Funny.Comparison, Coq.Lists — into
 this one).  No naturality of the insertion as a [Transform] (#296's
 [insert_Transform] has no counterpart here); no identification of the
 free monoid with the delooping of a free category on a one-vertex
 quiver; no [Foldable]/initial-algebra bridge; no relation to
 Instance/Mon/Coproduct.v's [FreeProd] beyond sharing its accessor
 layer, so in particular the free monoid on a two-element setoid is
 NOT proved to be the free product of two copies of the free monoid on
 one generator.  And no free RING: this file supplies one leg of
 Mac Lane's §IV.8 Exercise 2 and stops there.

 LEDGER.  57 constants, all reported “Closed under the global context”
 by [Print Assumptions] — that is 31 [def] plus 19 [prf] in the [.glob]
 MINUS the three named [Fail] commands, which the [.glob] records as
 [def] although they define nothing, plus [word_eq] with its two
 constructors, its four automatically generated elimination schemes,
 and the three [Program] obligations ([free_mon_insert_obligation_1],
 [Blur_Setoid_obligation_1],
 [free_mon_AUniversalArrow_obligation_1]).  The [.glob] DOES list
 [word_eq] and its two constructors as [ind]/[constr] entries; what it
 does not list are the elimination schemes and the [Program]
 obligations, and the total below excludes [ind]/[constr] anyway, so
 the arithmetic is unaffected.  The [.glob]
 lists.  Three [Fail] commands: two CONVERSION negatives, each with a
 positive control beside it and each stripped once and its message
 read, plus one instrument check confirming that [Fail] reports
 failures in this file at all.  Every constant named inside a [Fail]
 also occurs in a positive command elsewhere in the file, so a rename
 breaks the file loudly rather than turning a negative vacuously
 green.  No separate probe file is shipped.

 CORRECTION (#471): #471 adds six constants, [free_mon_extend_pointwise],
 [free_mon_hom_iso], [free_mon_sets_adjunction_hom] and the three
 [eq_refl] readbacks [free_mon_hom_counit], [free_mon_hom_unit] and
 [free_mon_hom_to], each “Closed under the global context” and named in
 #471's print-assumptions block; the 57 above are unchanged.  The
 refusals about the hom-set form are pinned in Test/ProbeWord471.v,
 which restates the three readbacks and names the six constants in its
 guard.

 DISPLAY HAZARD.  [Print Module] and plain [Check] suppress the
 implicit first argument of the [Sets.morphism] coercion, so
 [free_mon_unit_is_insert] prints as “Sets.morphism a =
 Sets.morphism a”, which reads as a tautology and is not one:
 under [Set Printing All] the left side is the adjunction's [unit] and
 the right side is [free_mon_insert X].  The same suppression affects
 [free_mon_fmap_generators]. 

 --------
 nLab：       https://ncatlab.org/nlab/show/free+monoid
 nLab：       https://ncatlab.org/nlab/show/universal+morphism
 Wikipedia：  https://en.wikipedia.org/wiki/Free_monoid

 书籍：Mac Lane，《为实际数学家准备的范畴论》，第2版，GTM 5，Springer 1998，§IV.8，练习2 (maclane:IV.8:ex2) — 在集合上得到的自由环作为自由构造的复合；§II.7 推论2，第50-51页，关于自由半群本身。对于一个集合等价关系 X——一个带有选定等价关系 `≈` 的载体——X 上的自由幺半群是由 X 的载体上的有限单词组成的集合等价关系，按字母逐个比较至 `≈`，通过与空字的串联进行乘法运算，其单位是空字。它的泛性质是：插入单字母单词在集合-态射从 X 到幺半群的底层集合等价关系中是普遍的：每个 h : X ~> U L 都沿着插入唯一扩展为一个幺半群同态，即将串联替换为 L 的乘法，并将空字替换为其单位的折叠映射。一切都在 [@Mon Sets Sets_Product_Monoidal] 发展，即在扎伊姆集合（setoids）的笛卡尔单体范畴中内部幺半群的范畴（Theory/Algebra/Monoid.v），其中 [@Mon_Forget Sets Sets_Product_Monoidal] 作为基础集合函子 U。在该基底上的一个幺半群对象恰好是一个普通的集合幺半群：mu : X ∏ X ~> X，eta : 1 ~> X，并且三个定律是结合律以及两个单位元定律，应用了笛卡尔结合子和单位元映射。这里不需要函数外延性：当两个幺半群同态在每个单词上都一致时，它们正好被识别为相同，而这正是单词归纳所证明的。为什么存在此文件：Mon(Coq)/Mon(Sets) 测量。Issue #296 已经提供了一个带有其泛性质及其伴随函子的自由幺半群——但在不同的范畴中。
 Instance/Coq/Monoid/Free.v 缩写为 [MonCoq := @Mon Coq Coq_Monoidal]，并提供了 [FreeMonoid : Coq ⟶ MonCoq] 和 [free_monoid_adjunction : FreeMonoid ⊣ UMon] 在该基础上。
 编号#400 想要组合的幺半群环分支来自另一个范畴：Instance/Rng/MonoidRing.v 设置了 [MonSets := @Mon Sets Sets_Product_Monoidal]，并提供 [MonoidRingFunctor : MonSets ⟶ Rng] 与 [zmring_adjunction : MonoidRingFunctor ⊣ Rng_Forget_Mon]。
 Instance/Roster.v 将同一个范畴命名为 [Mon_Sets]。因此，“集合 → 幺半群 → 环”的两个分支未能组合。这个差距在这里被重新验证，而不是盲目信任，并且协调测量保持不变，有两个值得说明的改进。 (1) 在整个树中搜索一个余域为 [Mon Sets] 的函子，恰好返回三个，并且这三者都是遗忘函子：ZW13WZZ（Theory/Algebra/Rig.v）、ZW14WZZ（Instance/Rng/MonoidRing.v）和 [Grp_MonSets]（Instance/Rng/GroupRing.v）；Instance/Roster.v 以 Roster 自己类别的名称重新声明了其中第一个，并且没有增加第四个。在此文件之前，ZW16WZZ 没有自由幺半群。(2) 在树中，[Coq] 与 [Sets] 之间没有等价——但是更尖锐的说法“它们之间根本没有函子”是错误的：Instance/Shapes.v 声明了 [Trie_Functor (s : Shape) : Coq ⟶ Sets]，它与两个范畴的任何比较无关；而 [Sets_discrete]（Instance/Sets/Products.v）是一个对象级的离散集体构造，并没有任何地方被封装成函子。两者都没有传递 #296 的伴随关系，更重要的是，沿任意函子对进行传输也无法保持左伴随性——在 SETOID 上的自由单子必须识别 `≈` -相等的生成元，而没有任何离散集体的途径可以做到。最后一句是一个论证，而不是定理；这里所证明的事实是它所依赖的（[free_mon_blur_identifies] 与 [free_mon_two_generators_distinct]）。Instance/Mon/Coproduct.v 将同一堵墙命名为原因
 Awodey §3.2 练习 5（通过保持余极限 M(A) + M(B) ≅ M(A + B)）在那里未交付：“在 tree 中唯一的自由单子伴随是 Instance/Coq/Monoid/Free.v 的，它位于 [Coq] 上，因此在该范畴中不存在这样的伴随来保持余极限”。这个文件恰好移除了该障碍——现在 [Mon Sets] 上 [Mon_Forget] 有一个左伴随。练习本身在这里并未尝试，也没有声称其证明还需要其他什么。元素级访问器是重用的，而不是重写的，并且选择是经过衡量的。[Mon Sets] 的元素级读取已经存在两个副本——Instance/Rng/MonoidRing.v（[mcar] / [mop] / [mone] / [mmap] / [mhom]）和 Instance/Mon/Coproduct.v（[mon_ob] / [mon_mul] / [mon_one] / [mon_fun] / [mk_mon_obj] / [mk_mon_hom]）——再写第三个会是错误的决定。Coproduct.v 的副本是被导入的，出于依赖原因，而不是风格上的原因：MonoidRing.v 需要 [Instance.Rng]、[Instance.Rng.Algebras]、[Instance.Rng.Polynomial]、[Instance.Rng.Algebras.Associative] 和 [Instance.Mod]，因此导入它将使整个环层次结构位于自由幺半群的每个使用者之后——并且会颠倒预期的依赖关系，因为环侧组合体将会使用此文件。Coproduct.v 只需要 Lib、Category、Isomorphism、Morphisms、Monoidal、Cartesian、Cocartesian、Terminal、Initial、Monoid、Monoid.Hom 和 Sets。这里没有引入类别的新名称——下面的 [MonS] 是一个没有导出的 [Local Notation] ——因此将此文件与 MonoidRing.v 一起使用不会与它的 [MonSets] 冲突。导入的副产品是 Coproduct.v 的 [ListBoolMon] 可作为非空性探针的具体目标，因此不需要为它们创建新的单子。优势，严格优先测量。定义性（随 [eq_refl] 示例一起提供）：载体、乘法、单位、自由幺半群的基础集合等价关系；[FreeMonSets] 的对象部分；通用箭头就是插入；伴随的单位就是插入；折叠在一个字面单字上的值。仅到 `≈`：余单位的作用（它是 L 中单词的求值，[free_mon_counit_evaluates]）以及自由函子对箭头的作用（[free_mon_fmap_is_wmap]）。尝试了两种严格读法并被拒绝，两者都在文件中以 [Fail] 命令固定，并在旁边有正向控制：- 余单位无法计算。它的底层映射是 [unique_obj (ump_universal_arrows ...)]，并且 [ump_universal_arrows]（Theory/Universal/Arrow.v）与 [Qed] 闭合，所以没有任何计算能通过它。诊断区分出：相同伴随的 UNIT，通过透明的 [universal_arrow_from_UMP] 路由，实际上是 [eq_refl]（[free_mon_unit_is_insert]），所以造成问题的是那个常量的不透明性，而不是伴随的一般管道问题。更正 (#471)：该诊断指出两种原因之一。两个 [Qed] 常数阻塞余单位：[ump_universal_arrows] 和此文件自身的 [free_mon_universal]，这是因子分解的证明，[free_mon_universal_arrow] 传递给 [universal_arrow_from_UMP] ，并从中读取余单位。由#471的侦察在包含此文件32模块闭包的40文件副本中测量，在每次更改后重建：仅将[ump_universal_arrows] 转换为 [Defined] 时，NEGATIVE 1 仍然被拒绝；同时将 [free_mon_universal] 转换为 [Defined] 时，NEGATIVE 1 的声明成立，在单子模板 W₀（Instance/Mon/Word.v）需要的八次转换中，有六次从该余单元读取（μ作为连接，余单元作为折叠，比较函子值），两次从自由函子的作用读取，除了一个，在 [eq_refl] 上都成立，例外是在变量字上的作用，NEGATIVE 2 的 [Fixpoint] 被卡住。此处没有将任何常数转换为 [Defined]：[ump_universal_arrows] 被许多开发共享，其中几个在探针中固定了其不透明性，问题 #1353 对其进行了跟踪。#471 增加了相同的邻接关系，但采用同态集形式，见下方的 [free_mon_sets_adjunction_hom]，其余单位是通过换算折叠的。

 - [free_mon_extend_insert] 是一个 Leibniz 等式，但在变量词上不是换算：[free_mon_extend] 是 [Fixpoint]，并且在变量处停滞。控制是相同的陈述，只是在字面上的单字符词处，它通过 [eq_refl] 成立——因此障碍是停滞的递归，而不是两边的不匹配。归纳的每一步都通过 [reflexivity] 闭合，没有消耗任何幺半群律，这就是为什么定理是在 Leibniz `=` 上表述，而不是在 `≈` 上。非空性。通向同一分离的两条独立路径，并且它们之间的差异值得记录。与 Instance/Mon/Coproduct.v 中的 [fp_eq] 以及在此树中生成的其他同余不同，[word_eq] 是通过对两个单词的递归定义的结构性同余，因此它可以进行反演，并且可以直接到达负的 IS：[free_mon_insert_reflects] 将一个 [we_cons] 反演以恢复字母的 `≈`，从而在三行内给出 [free_mon_two_generators_distinct]。映射出的路径也提供了，并且与其没有共享的证明文本（[free_mon_two_generators_distinct_via_probe], [free_mon_word2_not_letter]），在 Coproduct.v 中通过普遍性属性进行评估 [ListBoolMon]；那里折叠的值 COMPUTES（[two_probe_word2] 为 [eq_refl]）。集合等价类的一半是在  [Sets]  而不是在  [Coq]  做这件事的关键：[free_mon_blur_identifies] 展示了两个 `≈`-相等但莱布尼茨不同的生成元，而自由幺半群识别了它们，相对于在相同载体上的离散集合等价类 [free_mon_two_generators_distinct]，它则没有这样做。宇宙。请读取约束块，而不是绑定器：
 [FreeMonSetsObject@{u u0}]、[FreeMonSets@{u u0 u1 u2 u3}] 和
 [free_mon_sets_adjunction@{u u0 u1 u2 u3 u4}] 中不包含任何 [Set]
 ——没有 [Set] 宇宙实例，也没有提到它的约束——在两个重要层次之间唯一的严格不等式是 [Sets] 自身的 [o < so]（[Instance/Sets.v] 声明 [Sets@{o so} : Category@{so o o}]）。这被保护而不是仅仅被测量：本文件末尾的 [FreeAboveSet] 部分声明了 [Constraint Set < uo]，并详细说明了在 [Set] 之上严格层次的三种常量。因此，本文件不会引入自身的大小限制。请注意，[Set] 引脚 CLAUDE.md 记录了 [Rig_Forget_Mon] —— 因此也包括 [Rng_Forget_Mon] —— 位于 RING 侧，这里未作处理，但它确实到达了复合体，并且这是经过测量而非猜测的：在一个树外的临时文件中，需要同时引用该模块和 Instance/Rng/MonoidRing.v，该复合体 [MonoidRingFunctor ◯ FreeMonSets] 可以展开，其约束块读取 [Sets@{Set u} ⟶ Rng@{u Set}]，并在 [FreeMonSets@{Set u _ _ _}] 上实例化了该文件自己的函子。因此，该引脚是从环腿继承的，这里没有任何内容需要它 —— 但是通过单子构建自由环的使用者会携带它。该复合体并未在此文件中构建，这里的任何内容都没有针对该结果进行保护；测量结果是报告出来的，以便复合体的作者无需重新发现它。HOM-集形式 (#471)。保留了单个伴随的两种封装 FreeMonSets ⊣ UMonS。[free_mon_sets_adjunction]，来自通用箭头，是 Instance/Rng/Free.v 的自由环，其余的树被消耗，并且它保持不变。[free_mon_sets_adjunction_hom] 是 Theory/Adjunction.v 的 [Build_Adjunction'] 应用于自然双射 [free_mon_hom_iso]，具有相同的左伴随 [FreeMonSets]、相同的右伴随和相同的嵌入：它的单位和正向换位是 [free_mon_sets_adjunction] 在 [eq_refl] ([free_mon_hom_unit], [free_mon_hom_to]) 的单位和正向换位，其逆换位是折叠 [free_mon_hom]，因此它的余单位是 [eq_refl] ([free_mon_hom_counit]) 上身份的折叠，而另一个余单位仅在 `≈` ([free_mon_counit_evaluates]) 上为折叠。它存在于 Mac Lane §VI.4 练习 1 (Instance/Mon/Word.v) 的单子 W₀，对于该单子的乘法 U ε F 和比较函子随后进行计算。它不是第二个自由幺半群，也不是第二个自由函子：箭头上的作用仍然是 [FreeMonSets]，字母映射仅出现在 `≈`（[free_mon_fmap_is_wmap]）。在 [eq_refl] 两个伴随不被认为相等，它们在一个变量词上的余单位也是如此 (Test/ProbeWord471.v)。它的宇宙是：[free_mon_hom_iso] 和 [free_mon_sets_adjunction_hom] 绑定 @{o so}，以及 [FreeMonSets] 的另外三层（在 Coq 8.19/8.20 中为四层），没有 [Set]，伴随固定在 [Adjunction@{so o o so o o o o so o so}]，就像 Instance/Smgrp.v 固定它自己的那样。问题 #1353 记录了退出：一旦 [ump_universal_arrows] 和 [free_mon_universal] 透明化，一个记录会被保留，W₀ 就基于它重新建立。什么是不故意交付的。超出列表表示本身之外的单词没有正常形式，因此对于 [word_eq] 没有可判定字母集扎伊多（setoid）所能给出的决策程序，也没有长度或度的不变量。与 Instance/Coq/Monoid/Free.v 的 [FreeMonoid] 完全没有比较：这里两者没有关联，也不声称其中一个可以决定另一个，并且两者所在的环境范畴之间没有建立函子（这样做会将该文件自身的闭包——Comma、FAlg、Funny.Comparison、Coq.Lists——拖入此文件中）。插入的自然性不存在，作为 [Transform]（#296 的 [insert_Transform] 在这里没有对应物）；自由幺半群与单顶点箭图上的自由范畴的弯曲没有识别；没有 [Foldable] /初始代数桥；与 Instance/Mon/Coproduct.v 的 [FreeProd] 的关系仅限于共享其访问层，因此特别地，未证明两元素集合上的自由幺半群是一个生成元的自由幺半群的两个副本的自由积。并且没有自由环：此文件只提供了 Mac Lane 第 IV.8 节练习 2 的一个部分，止步于此。账簿。57 个常量，全部由 [Print Assumptions] 报告为“在全局上下文下关闭”，即 31 个 [def] 加上 19 个 [prf] 在 [.glob] 中，减去三个名为 [Fail] 的命令，这些命令被 [.glob] 记录为 [def]，尽管它们没有定义任何内容，加上 [word_eq] 及其两个构造函数、四个自动生成的消去方案，以及三个 [Program] 义务（[free_mon_insert_obligation_1]、[Blur_Setoid_obligation_1]、[free_mon_AUniversalArrow_obligation_1]）。[.glob] 确实将 [word_eq] 及其两个构造函数列为 [ind] / [constr] 条目；它未列出的内容是消去方案和 [Program] 义务，而下面的总数无论如何不包括 [ind] / [constr]，所以算术结果不受影响。[.glob] 列出。三个 [Fail] 命令：两个 CONVERSION 否定命令，每个旁边都有一个正控制，并且每个都曾被剥离一次并读取其消息，加上一个仪器检查以确认 [Fail] 报告此文件中的失败情况。[Fail] 内部命名的每个常量也在文件的其他地方的正命令中出现，因此重命名会明显破坏文件，而不是让一个否定命令虚假地显示为绿色。不附带单独的探针文件。修正 (#471)：#471 添加了六个常量，[free_mon_extend_pointwise]、[free_mon_hom_iso]、[free_mon_sets_adjunction_hom] 以及三个读回 [eq_refl]、[free_mon_hom_counit]、[free_mon_hom_unit] 和 [free_mon_hom_to]，每个都“在全局上下文下封闭”，并在 #471 的打印假设块中命名；上述 57 个保持不变。关于同态集形式的拒绝被固定在 Test/ProbeWord471.v 中，该文件重新声明三个读回并在其保护中命名六个常量。

 显示危险。[Print Module] 和普通的 [Check] 抑制了 [Sets.morphism] 强制转换的隐式第一个参数，因此 [free_mon_unit_is_insert] 打印为 “Sets.morphism a = Sets.morphism a”，这看起来像一个恒等式，但其实不是：在 [Set Printing All] 下，左边是伴随的 [unit]，右边是 [free_mon_insert X]。同样的抑制也影响 [free_mon_fmap_generators]。
*)

#[local] Obligation Tactic := idtac.

Local Notation MonS := (@Mon Sets Sets_Product_Monoidal).
Local Notation UMonS := (@Mon_Forget Sets Sets_Product_Monoidal).

(*
   * * Words over a setoid

   The carrier is [list (carrier X)].  Concatenation is spelled out
   rather than taken from [Coq.Lists.List], following the precedent and
   the stated reason of Instance/Mon/Coproduct.v: importing that
   module brings [list_scope]'s notations into a file whose ambient
   scope is the library's, and the whole of what is needed is five
   lines. 

   --------
   * * 在等价集合上的词

   承载集是 [list (carrier X)]。连接操作被明确写出，而不是取自 [Coq.Lists.List]，根据 Instance/Mon/Coproduct.v 中的先例和说明的理由：导入该模块会将 [list_scope] 的符号引入到一个其环境范围为库的文件中，而所需的全部内容只有五行。
*)

Fixpoint wapp {X : SetoidObject} (u v : list (carrier X))
  : list (carrier X) :=
  match u with
  | Datatypes.nil        => v
  | Datatypes.cons a u'  => Datatypes.cons a (wapp u' v)
  end.

Lemma wapp_assoc {X : SetoidObject} (u v w : list (carrier X)) :
  wapp (wapp u v) w = wapp u (wapp v w).
Proof.
  induction u as [|a u IH]; simpl; [ reflexivity | now rewrite IH ].
Qed.

Lemma wapp_nil_r {X : SetoidObject} (u : list (carrier X)) :
  wapp u Datatypes.nil = u.
Proof.
  induction u as [|a u IH]; simpl; [ reflexivity | now rewrite IH ].
Qed.

(*
 Two words are equivalent when they have the same length and their
 letters are `≈`-equal in order.  This is the pointwise lifting of X's
 own equivalence, and it is [Type]-valued because `≈` in this library
 is a [crelation]: equivalence proofs carry data. 

 --------
 当两个单词长度相同且它们的字母顺序相同的时候，它们是等价的。这是 X 自身等价关系的逐点提升，并且它是值为 [Type] 的，因为在这个库中 `≈` 是一个 [crelation]：等价性证明携带数据。
*)
Inductive word_eq {X : SetoidObject}
  : list (carrier X) → list (carrier X) → Type :=
  | we_nil : word_eq Datatypes.nil Datatypes.nil
  | we_cons (a b : carrier X) (u v : list (carrier X)) :
      a ≈ b → word_eq u v →
      word_eq (Datatypes.cons a u) (Datatypes.cons b v).

Lemma word_eq_refl {X : SetoidObject} (u : list (carrier X)) :
  word_eq u u.
Proof.
  induction u as [|a u IH].
  - exact we_nil.
  - exact (we_cons a a u u (reflexivity a) IH).
Qed.

Lemma word_eq_sym {X : SetoidObject} (u v : list (carrier X)) :
  word_eq u v → word_eq v u.
Proof.
  intro H; induction H as [|a b u v Hab Huv IH].
  - exact we_nil.
  - exact (we_cons b a v u (symmetry Hab) IH).
Qed.

Lemma word_eq_trans {X : SetoidObject} (u v w : list (carrier X)) :
  word_eq u v → word_eq v w → word_eq u w.
Proof.
  intros H; revert w.
  induction H as [|a b u v Hab Huv IH]; intros w K.
  - exact K.
  - inversion K as [|b' c v' w' Hbc Hvw].
    subst.
    exact (we_cons a c u w' (transitivity Hab Hbc) (IH w' Hvw)).
Qed.

Definition word_eq_Equivalence (X : SetoidObject)
  : Equivalence (@word_eq X) :=
  {| Equivalence_Reflexive  := @word_eq_refl X
   ; Equivalence_Symmetric  := @word_eq_sym X
   ; Equivalence_Transitive := @word_eq_trans X |}.

Definition Word_Setoid (X : SetoidObject) : Setoid (list (carrier X)) :=
  {| equiv := @word_eq X ; setoid_equiv := word_eq_Equivalence X |}.

Definition WordObj (X : SetoidObject) : SetoidObject :=
  {| carrier := list (carrier X) ; is_setoid := Word_Setoid X |}.

Lemma wapp_respects {X : SetoidObject} (u u' v v' : list (carrier X)) :
  word_eq u u' → word_eq v v' → word_eq (wapp u v) (wapp u' v').
Proof.
  intros Hu Hv; induction Hu as [|a b u u' Hab Huu' IH]; simpl.
  - exact Hv.
  - exact (we_cons a b _ _ Hab IH).
Qed.

(*
   * * The free monoid on a setoid

   Mac Lane §II.7 Corollary 2: the finite words over X form a monoid
   under concatenation with the empty word as unit.  Both unit laws and
   associativity are Leibniz equalities of lists, so the three monoid
   obligations are discharged by transporting reflexivity of [word_eq]
   along them. 

   --------
   * * 关于集合等价关系的自由幺半群

   Mac Lane §II.7 推论 2：X 上的有限单词在连接运算下形成一个幺半群，空单词作为单位元。单位律和结合律都是列表的莱布尼茨等式，因此三个幺半群的条件通过沿它们传递 [word_eq] 的自反性来满足。
*)

Definition FreeMonSetsObject (X : SetoidObject) : MonS.
Proof.
  unshelve refine
    (mk_mon_obj (WordObj X) Datatypes.nil (@wapp X) _ _ _ _).
  - intros u u' Hu v v' Hv; exact (wapp_respects u u' v v' Hu Hv).
  - intros u v w; rewrite wapp_assoc; exact (word_eq_refl _).
  - intro u; exact (word_eq_refl u).
  - intro u; rewrite wapp_nil_r; exact (word_eq_refl u).
Defined.

(* The four data readings hold on the nose. / 四个数据读数正好准确。 *)
Example free_mon_carrier (X : SetoidObject) :
  mon_ob (FreeMonSetsObject X) = WordObj X := eq_refl.

Example free_mon_forget (X : SetoidObject) :
  UMonS (FreeMonSetsObject X) = WordObj X := eq_refl.

Example free_mon_mul_is_wapp (X : SetoidObject)
        (u v : list (carrier X)) :
  mon_mul (FreeMonSetsObject X) u v = wapp u v := eq_refl.

Example free_mon_one_is_nil (X : SetoidObject) :
  mon_one (FreeMonSetsObject X) = @Datatypes.nil (carrier X) := eq_refl.

(*
   * ** The insertion of generators

   A letter goes to the one-letter word.  Respectfulness is one
   application of [we_cons]: this is where the construction differs
   from the [Coq]-based one, and it is the reason `≈`-equal generators
   end up identified. 

   --------
   * ** 发电机的插入

   一封信发送到那个单字母词。尊重是一种 [we_cons] 的应用：这里的构造不同于基于 [Coq] 的构造，这也是为什么 `≈` 相等的生成元最终会被识别的原因。
*)

Program Definition free_mon_insert (X : SetoidObject)
  : X ~{Sets}~> UMonS (FreeMonSetsObject X) := {|
  morphism := fun a => Datatypes.cons a Datatypes.nil
|}.
Next Obligation.
  intros X a b Hab.
  exact (we_cons a b Datatypes.nil Datatypes.nil Hab we_nil).
Qed.

(*
   * ** The extension of a map into a monoid: the fold

   The extension of h replaces concatenation by the multiplication of L
   and the empty word by its unit, so it is the right fold of h. 

   --------
   * ** 将映射扩展到幺半群：fold

   h 的扩展将连接替换为 L 的乘法
   并将空词替换为其单位，因此它是 h 的右折叠。
*)

Fixpoint free_mon_extend {X : SetoidObject} {L : MonS}
         (h : carrier X → carrier (mon_ob L)) (l : list (carrier X))
  : carrier (mon_ob L) :=
  match l with
  | Datatypes.nil       => mon_one L
  | Datatypes.cons a l' => mon_mul L (h a) (free_mon_extend h l')
  end.

(*
 The fold respects `≈` on words as soon as h respects `≈` on letters —
 which is exactly the hypothesis a Sets-morphism carries. 

 --------
 这个折叠在单词上遵守 `≈`，只要 h 在字母上遵守 `≈`——这正是一个集合态射所具备的假设。
*)
Lemma free_mon_extend_respects {X : SetoidObject} {L : MonS}
      (h : carrier X → carrier (mon_ob L))
      (hp : Proper (equiv ==> equiv) h)
      (u v : list (carrier X)) :
  word_eq u v → free_mon_extend h u ≈ free_mon_extend h v.
Proof.
  intro H; induction H as [|a b u v Hab Huv IH]; simpl.
  - reflexivity.
  - exact (mon_mul_resp L _ _ (hp a b Hab) _ _ IH).
Qed.

(* It carries concatenation to multiplication: induction on the left word, using the left unit law at the empty word and associativity at a [cons]. / 它将连接运算推广到乘法：对左侧字进行归纳，在空字上使用左单位律，并在一个 [cons] 上使用结合律。 *)
Lemma free_mon_extend_wapp {X : SetoidObject} {L : MonS}
      (h : carrier X → carrier (mon_ob L)) (u v : list (carrier X)) :
  free_mon_extend h (wapp u v)
    ≈ mon_mul L (free_mon_extend h u) (free_mon_extend h v).
Proof.
  induction u as [|a u IH]; simpl.
  - symmetry; exact (mon_one_l L (free_mon_extend h v)).
  - transitivity
      (mon_mul L (h a)
         (mon_mul L (free_mon_extend h u) (free_mon_extend h v))).
    + exact (mon_mul_resp L _ _ (reflexivity (h a)) _ _ IH).
    + symmetry; exact (mon_mul_assoc L (h a) _ _).
Qed.

(* ...and it agrees with h on the generators, by the right unit law. / ...并且根据右单位律，它在生成元上与 h 一致。 *)
Lemma free_mon_extend_generator {X : SetoidObject} {L : MonS}
      (h : carrier X → carrier (mon_ob L)) (a : carrier X) :
  free_mon_extend h (free_mon_insert X a) ≈ h a.
Proof. exact (mon_one_r L (h a)). Qed.

(*
 Hence it is a monoid homomorphism out of the free monoid.  Its unit
 clause needs no proof at all: the unit of the free monoid IS the
 empty word, on which the fold returns the unit of L by computation. 

 --------
 因此，它是从自由幺半群出的幺半群同态。它的单位子句根本不需要证明：自由幺半群的单位就是空字，fold 在其上通过计算返回 L 的单位。
*)
Definition free_mon_hom {X : SetoidObject} {L : MonS}
      (h : carrier X → carrier (mon_ob L))
      (hp : Proper (equiv ==> equiv) h)
  : FreeMonSetsObject X ~{MonS}~> L :=
  @mk_mon_hom (FreeMonSetsObject X) L (free_mon_extend h)
    (fun u v Huv => free_mon_extend_respects h hp u v Huv)
    (fun u v => free_mon_extend_wapp h u v)
    (reflexivity (mon_one L)).

(*
   * ** Uniqueness of the extension

   Any monoid homomorphism out of the free monoid that agrees with h on
   the generators IS the fold.  The induction uses both homomorphism
   laws: the unit law at the empty word, the multiplication law at the
   [cons] split [a :: l = (a :: nil) ++ l], which is a Leibniz identity
   here rather than a rewrite. 

   --------
   * ** 扩展的唯一性

   从自由幺半群出发的任何幺半群同态，如果在生成元上与 h 一致，都是 fold。归纳使用了两个同态律：空字上的单位律，以及在 [cons] 拆分 [a :: l = (a :: nil) ++ l] 上的乘法律，这里是一个莱布尼茨恒等式，而不是重写。
*)

Lemma free_mon_extend_unique {X : SetoidObject} {L : MonS}
      (h : carrier X → carrier (mon_ob L))
      (g : FreeMonSetsObject X ~{MonS}~> L)
      (Hg : ∀ a : carrier X, mon_fun g (free_mon_insert X a) ≈ h a)
      (l : list (carrier X)) :
  mon_fun g l ≈ free_mon_extend h l.
Proof.
  induction l as [|a l IH]; simpl.
  - exact (mon_fun_one g).
  - transitivity
      (mon_mul L (mon_fun g (free_mon_insert X a)) (mon_fun g l)).
    + exact (mon_fun_mul g (free_mon_insert X a) l).
    + exact (mon_mul_resp L _ _ (Hg a) _ _ IH).
Qed.

(*
   * ** The universal property

   In the shape [Theory/Universal/Arrow.v]'s
   [universal_arrow_from_UMP] consumes: for every monoid L and every
   h : X ~> U L there is exactly one monoid homomorphism g with
   U g ∘ insert ≈ h.  Uniqueness is up to the ambient `≈`, which in
   Mon(Sets) is pointwise `≈` of the underlying setoid maps. 

   --------
   * ** 通用性质

   在形状 [Theory/Universal/Arrow.v] 中，
   [universal_arrow_from_UMP] 消耗：对于每一个幺半群 L 和每一个
   h : X ~> U L，存在且仅存在一个幺半群同态 g，使得
   U g ∘ insert ≈ h。唯一性在于环境 `≈`，
   在 Mon(Sets) 中是基础集合映射的点态 `≈`。
*)

Theorem free_mon_universal (X : Sets) :
  ∀ (L : MonS) (h : X ~{Sets}~> UMonS L),
    ∃! g : FreeMonSetsObject X ~{MonS}~> L,
      h ≈ fmap[UMonS] g ∘ free_mon_insert X.
Proof.
  intros L h.
  unshelve eexists.
  - exact (free_mon_hom (h : carrier X → carrier (mon_ob L))
             (proper_morphism h)).
  - intro a; simpl.
    symmetry; exact (free_mon_extend_generator _ a).
  - intros g Hg l; simpl.
    symmetry.
    apply (free_mon_extend_unique
             (h : carrier X → carrier (mon_ob L)) g).
    intro b; symmetry; exact (Hg b).
Qed.

(*
 The free monoid packaged as a universal arrow from X to [Mon_Forget].
 By Theory/Universal/Arrow.v this IS an initial object of the comma
 category =(X) ↓ Mon_Forget. 

 --------
 作为从 X 到 [Mon_Forget] 的通用箭头封装的自由幺半群。\n根据 Theory/Universal/Arrow.v，这确实是逗号范畴 =(X) ↓ Mon_Forget 的初对象。
*)
Definition free_mon_universal_arrow (X : Sets) : UniversalArrow X UMonS :=
  universal_arrow_from_UMP X UMonS (FreeMonSetsObject X)
                           (free_mon_insert X) (free_mon_universal X).

(*
 The same content in the direct encoding, where the universal object is
 named rather than projected. 

 --------
 直接编码中的相同内容，其中通用对象被命名而不是被投射。
*)
Program Definition free_mon_AUniversalArrow (X : Sets)
  : AUniversalArrow X UMonS (FreeMonSetsObject X) := {|
  universal_arrow := free_mon_insert X
|}.
Next Obligation.
  intros X L h.
  unshelve eexists.
  - exact (free_mon_hom (h : carrier X → carrier (mon_ob L))
             (proper_morphism h)).
  - intro a; simpl; exact (free_mon_extend_generator _ a).
  - intros g Hg l; simpl.
    symmetry.
    apply (free_mon_extend_unique
             (h : carrier X → carrier (mon_ob L)) g).
    intro b; exact (Hg b).
Qed.

(*
   * ** The free-forgetful adjunction

   Assembled by the generic machinery of Theory/Universal/Arrow.v from
   the family of universal arrows.  This is the constant the
   monoid-ring leg was missing. 

   --------
   * ** 自由-忘记伴随

   由 Theory/Universal/Arrow.v 的通用机制从一族泛箭头组装而成。这是单子-环部分缺失的常量。
*)

Definition FreeMonSets : Sets ⟶ MonS :=
  LeftAdjointFunctorFromUniversalArrows UMonS free_mon_universal_arrow.

Definition free_mon_sets_adjunction : FreeMonSets ⊣ UMonS :=
  AdjunctionFromUniversalArrows UMonS free_mon_universal_arrow.

(* * * Strengths achieved, and two rejected / * * 实现的优势，以及两个被拒绝的 *)

(* The free functor's object part is the word monoid, definitionally. / 自由函子在对象部分定义上就是单词幺半群。 *)
Example FreeMonSets_obj (X : Sets) :
  FreeMonSets X = FreeMonSetsObject X := eq_refl.

(*
 The universal arrow is the insertion on the nose:
 [universal_arrow_from_UMP] stores the supplied morphism as the second
 projection of the comma object it builds, so no proof is involved. 

 --------
 通用箭头是鼻子的插入：
 [universal_arrow_from_UMP] 将提供的态射存储为它构建的逗号对象的第二投影，所以不涉及证明。
*)
Example free_mon_arrow_is_insert (X : Sets) :
  @arrow _ _ X UMonS (free_mon_universal_arrow X) = free_mon_insert X
  := eq_refl.

(*
 Hence so is the unit of the adjunction: the transpose of the identity
 is [fmap[U] id ∘ arrow], and [fmap[U] id] is the identity setoid map,
 whose action is [Datatypes.id]. 

 --------
 因此，伴随的单位也是如此：恒等的换位是  [fmap[U]  id ∘ arrow]，而  [fmap[U]  id] 是恒等集合同构映射，其作用是  [Datatypes.id] 。
*)
Example free_mon_unit_is_insert (X : Sets) (a : carrier X) :
  @Category.Theory.Adjunction.unit _ _ _ _ free_mon_sets_adjunction X a
    = free_mon_insert X a := eq_refl.

(*
 NEGATIVE 1 (conversion).  The counit does NOT compute.  Its
 underlying map is [unique_obj (ump_universal_arrows ...)], and
 [ump_universal_arrows] is closed with [Qed], so nothing reduces
 through it.  Stripping the [Fail] reports
 “cannot unify ”mon_fun counit l“ and
 ”free_mon_extend (λ x, x) l“”.
 The control is [free_mon_unit_is_insert] immediately above: the unit
 of the SAME adjunction, which routes through the transparent
 [universal_arrow_from_UMP], does close by [eq_refl].  So the cause is
 the opacity of that one donor, not adjunction plumbing at large.
 CORRECTION (#471): one of two; this file's own [free_mon_universal] is
 the other (the header's STRENGTHS), and the counit of the hom-set
 form [free_mon_sets_adjunction_hom] below is this fold at [eq_refl]
 ([free_mon_hom_counit]). 

 --------
 负面 1（转换）。余单位无法计算。它的底层映射是 [unique_obj (ump_universal_arrows ...)]，而 [ump_universal_arrows] 与 [Qed] 已封闭，所以没有任何东西可以通过它减少。剥离 [Fail] 时报告“无法统一 'mon_fun counit l' 与 'free_mon_extend (λ x, x) l'”。控制位于紧上方的 [free_mon_unit_is_insert]：相同伴随关系的单位，通过透明的 [universal_arrow_from_UMP] 路由，确实被 [eq_refl] 闭合。所以原因是那个捐赠者的不可见性，而不是整体伴随关系的管道问题。更正 (#471)：两个中的一个；此文件自身的 [free_mon_universal] 是另一个（头部的 STRENGTHS），下方同态集合形式的余单位 [free_mon_sets_adjunction_hom] 是 [eq_refl] 处的此折叠（[free_mon_hom_counit]）。
*)
Fail Example free_mon_counit_is_not_strict
  (L : MonS) (l : list (carrier (mon_ob L))) :
  mon_fun (@counit _ _ _ _ free_mon_sets_adjunction L) l
    = free_mon_extend (fun x => x) l := eq_refl.

(*
 What does hold: the counit evaluates a word in L.  Its defining
 property is the triangle identity [fmap_counit_unit], read at a
 generator; uniqueness of the extension then identifies it with the
 fold of the identity. 

 --------
 什么是 hold：余单位在 L 中对一个词求值。它的定义性质是三角恒等式 [fmap_counit_unit]，在生成元处读出；然后扩展的唯一性将其与恒等映射的折叠对应起来。
*)
Lemma free_mon_counit_evaluates (L : MonS)
      (l : list (carrier (mon_ob L))) :
  mon_fun (@counit _ _ _ _ free_mon_sets_adjunction L) l
    ≈ free_mon_extend (fun x => x) l.
Proof.
  apply (free_mon_extend_unique (fun x : carrier (mon_ob L) => x)).
  intro a.
  exact (@fmap_counit_unit _ _ _ _ free_mon_sets_adjunction L a).
Qed.

(*
   * ** The free functor acts on arrows as [map]

   [LeftAdjointFunctorFromUniversalArrows] defines [fmap] by universal
   factorization, not by a formula, so what the functor does to a word
   has to be proved.  It is the letterwise map: the defining
   factorization says generators go to generators, and the uniqueness
   half of the universal property identifies the homomorphism with
   [wmap]. 

   --------
   * ** 自由函子作用于箭头上如 [map] 

   [LeftAdjointFunctorFromUniversalArrows]  通过普适分解定义 [fmap] ，而不是通过公式，所以必须证明函子对一个词的作用。它是逐字映射：定义分解说明生成元映射到生成元，普适性质的唯一性一部分将同态与 [wmap]  识别。
*)

Fixpoint wmap {X Y : SetoidObject} (f : carrier X → carrier Y)
         (l : list (carrier X)) : list (carrier Y) :=
  match l with
  | Datatypes.nil       => Datatypes.nil
  | Datatypes.cons a l' => Datatypes.cons (f a) (wmap f l')
  end.

Lemma free_mon_fmap_generators {X Y : Sets} (f : X ~{Sets}~> Y)
      (a : carrier X) :
  mon_fun (fmap[FreeMonSets] f) (free_mon_insert X a)
    ≈ free_mon_insert Y (f a).
Proof.
  symmetry.
  exact (unique_property
           (ump_universal_arrows (free_mon_universal_arrow X)
              (@arrow _ _ Y UMonS (free_mon_universal_arrow Y) ∘ f)) a).
Qed.

(*
 NEGATIVE 2 (conversion).  The identification below is a Leibniz
 equality (proved next), but it is NOT a conversion at a VARIABLE
 word: [free_mon_extend] is a [Fixpoint] and is stuck on a variable.
 Stripping the [Fail] reports
 “cannot unify ”free_mon_extend (λ a, free_mon_insert Y (f a)) l“ and
 ”wmap f l“”.
 The control is [free_mon_extend_insert_at_letter] just below, which
 is the same statement at a literal one-letter word and DOES close by
 [eq_refl] — so the obstruction is the stuck recursion, not a
 mismatch of the two sides. 

 --------
 负例 2（转换）。下面的等式是一个莱布尼茨等式（接下来会证明），但它不是对变量词的转换：[free_mon_extend] 是一个 [Fixpoint]，并且卡在一个变量上。去掉 [Fail] 后报告“无法统一 free_mon_extend (λ a, free_mon_insert Y (f a)) l 和 wmap f l”。控制位于稍下的 [free_mon_extend_insert_at_letter]，它是在一个单字母文字上的同一语句，并且可以通过 [eq_refl] 成功闭合——所以阻碍的是卡住的递归，而不是两边的不匹配。
*)
Fail Example free_mon_extend_insert_is_not_strict
  {X Y : Sets} (f : X ~{Sets}~> Y) (l : list (carrier X)) :
  free_mon_extend (L:=FreeMonSetsObject Y)
    (fun a => free_mon_insert Y (f a)) l = wmap f l := eq_refl.

Example free_mon_extend_insert_at_letter
  {X Y : Sets} (f : X ~{Sets}~> Y) (a : carrier X) :
  free_mon_extend (L:=FreeMonSetsObject Y)
    (fun b => free_mon_insert Y (f b))
    (Datatypes.cons a Datatypes.nil)
    = wmap f (Datatypes.cons a Datatypes.nil) := eq_refl.

(*
 Each step of the induction closes by [reflexivity] with no monoid law
 spent, which is why this is stated at Leibniz `=`. 

 --------
 归纳的每一步都以 [reflexivity] 结束，没有使用任何幺半群法则，这就是为什么在莱布尼茨 `=` 处如此说明。
*)
Lemma free_mon_extend_insert {X Y : Sets} (f : X ~{Sets}~> Y)
      (l : list (carrier X)) :
  free_mon_extend (L:=FreeMonSetsObject Y)
    (fun a => free_mon_insert Y (f a)) l = wmap f l.
Proof.
  induction l as [|a l IH]; simpl in *;
    [ reflexivity | rewrite IH; reflexivity ].
Qed.

Theorem free_mon_fmap_is_wmap {X Y : Sets} (f : X ~{Sets}~> Y)
        (l : list (carrier X)) :
  mon_fun (fmap[FreeMonSets] f) l ≈ wmap f l.
Proof.
  transitivity (free_mon_extend (L:=FreeMonSetsObject Y)
                  (fun a => free_mon_insert Y (f a)) l).
  - apply (free_mon_extend_unique
             (fun a => free_mon_insert Y (f a)) (fmap[FreeMonSets] f)).
    intro a; exact (free_mon_fmap_generators f a).
  - rewrite free_mon_extend_insert; reflexivity.
Qed.

(*
   * ** The same adjunction in hom-set form (#471)

   A second packaging of [FreeMonSets ⊣ UMonS], with the SAME left
   adjoint [FreeMonSets] and the same insertion: Theory/Adjunction.v's
   hom-set constructor [Build_Adjunction'] applied to the natural
   bijection [free_mon_hom_iso], whose forward transpose is the one of
   [free_mon_sets_adjunction] (g ↦ U g ∘ insert) and whose inverse
   transpose is the fold [free_mon_hom].  Its counit is then the fold of
   the identity by conversion ([free_mon_hom_counit]), where the counit
   of [free_mon_sets_adjunction] is that fold only up to `≈`
   ([free_mon_counit_evaluates]).  Instance/Mon/Word.v builds the monad
   W₀ on it.  No second free monoid and no second free functor: the
   action on arrows is still [FreeMonSets]'s, at `≈` the letterwise map
   ([free_mon_fmap_is_wmap]). 

   --------
   * ** 同一个同态集形式的伴随 (#471)

   [FreeMonSets ⊣ UMonS] 的第二种封装，具有相同的左伴随 [FreeMonSets] 和相同的插入：在 Theory/Adjunction.v 中使用同态集构造器 [Build_Adjunction'] 应用于自然双射 [free_mon_hom_iso]，其正向转置为 [free_mon_sets_adjunction] 的转置 (g ↦ U g ∘ insert)，反向转置为折叠 [free_mon_hom]。其余单位随后是通过转换对恒等的折叠 ([free_mon_hom_counit])，其中 [free_mon_sets_adjunction] 的余单位仅在 `≈` 的意义下是该折叠 ([free_mon_counit_evaluates])。Instance/Mon/Word.v 在其上构建了单子 W₀。没有第二个自由幺半群，也没有第二个自由函子：箭头上的作用仍是 [FreeMonSets] 的，在 `≈` 为逐字母映射 ([free_mon_fmap_is_wmap])。
*)

(* The fold respects pointwise-`≈` letter maps. / 该fold尊重逐点的`≈`字母映射。 *)
Lemma free_mon_extend_pointwise {X : SetoidObject} {L : MonS}
      (h h' : carrier X → carrier (mon_ob L))
      (H : ∀ a, h a ≈ h' a) (l : list (carrier X)) :
  free_mon_extend h l ≈ free_mon_extend h' l.
Proof.
  induction l as [|a l IH]; simpl; [ reflexivity | ].
  exact (mon_mul_resp L _ _ (H a) _ _ IH).
Qed.

(* The natural bijection Mon(F X, L) ≅ Sets(X, U L): forward g ↦ U g ∘ insert, backward the fold. / 自然双射 Mon(F X, L) ≅ Sets(X, U L)：前向 g ↦ U g ∘ insert，后向则是 fold。 *)
Definition free_mon_hom_iso@{o so +} (X : Sets@{o so}) (L : MonS) :
  @Isomorphism Sets@{o so}
    {| carrier := @hom MonS (FreeMonSets X) L
     ; is_setoid := @homset MonS (FreeMonSets X) L |}
    {| carrier := @hom Sets@{o so} X (UMonS L)
     ; is_setoid := @homset Sets@{o so} X (UMonS L) |}.
Proof.
  unshelve refine
    (@Build_Isomorphism Sets
       {| carrier := @hom MonS (FreeMonSets X) L
        ; is_setoid := @homset MonS (FreeMonSets X) L |}
       {| carrier := @hom Sets X (UMonS L)
        ; is_setoid := @homset Sets X (UMonS L) |}
       (@Build_SetoidMorphism
          (@hom MonS (FreeMonSets X) L) (@homset MonS (FreeMonSets X) L)
          (@hom Sets X (UMonS L)) (@homset Sets X (UMonS L))
          (fun g => fmap[UMonS] g ∘ free_mon_insert X) _)
       (@Build_SetoidMorphism
          (@hom Sets X (UMonS L)) (@homset Sets X (UMonS L))
          (@hom MonS (FreeMonSets X) L) (@homset MonS (FreeMonSets X) L)
          (fun h => free_mon_hom (h : carrier X → carrier (mon_ob L))
                      (proper_morphism h)) _) _ _).
  - intros g g' H a. exact (H (Datatypes.cons a Datatypes.nil)).
  - intros h h' H l. exact (free_mon_extend_pointwise h h' H l).
  - intros h a. exact (free_mon_extend_generator (L := L) h a).
  - intros g l. simpl. symmetry.
    apply (free_mon_extend_unique _ g). intro a. reflexivity.
Defined.

Definition free_mon_sets_adjunction_hom@{o so +} :
  @Adjunction@{so o o so o o o o so o so} MonS Sets@{o so}
    FreeMonSets UMonS.
Proof.
  unshelve refine
    (@Build_Adjunction' MonS Sets FreeMonSets UMonS free_mon_hom_iso _ _).
  - intros X Y L f g a. simpl.
    apply (proper_morphism (`1 f)).
    exact (free_mon_fmap_generators g a).
  - intros X L L' f g a. reflexivity.
Defined.

(* Its counit is the fold of the identity, by conversion. / 它的余单位是通过转换得到的恒等映射的折叠。 *)
Example free_mon_hom_counit (L : MonS) (l : list (carrier (mon_ob L))) :
  mon_fun (@counit _ _ _ _ free_mon_sets_adjunction_hom L) l
    = free_mon_extend (fun x => x) l := eq_refl.

(* Its unit and its forward transpose ARE those of [free_mon_sets_adjunction]. / 它的单位和它的前向转置是 [free_mon_sets_adjunction] 的单位和前向转置。 *)
Example free_mon_hom_unit (X : Sets) :
  @Category.Theory.Adjunction.unit _ _ _ _ free_mon_sets_adjunction_hom X
    = @Category.Theory.Adjunction.unit _ _ _ _ free_mon_sets_adjunction X
  := eq_refl.

Example free_mon_hom_to (X : Sets) (L : MonS)
        (g : FreeMonSets X ~{MonS}~> L) :
  to (@adj _ _ _ _ free_mon_sets_adjunction_hom X L) g
    = to (@adj _ _ _ _ free_mon_sets_adjunction X L) g := eq_refl.

(*
   * * Non-vacuity

   [word_eq] is a STRUCTURAL congruence, not a generated one, so unlike
   Instance/Mon/Coproduct.v's [fp_eq] it is open to inversion and
   negatives are reachable directly.  Both routes are given below;
   they share no proof text. 

   --------
   * * 非空性

   [word_eq] 是一个结构同构，而不是生成的同构，所以与 Instance/Mon/Coproduct.v 中的 [fp_eq] 不同，它可以直接进行反演，并且负数可以直接得到。下面给出了两条路径；它们没有共享的证明文本。
*)

(*
 The insertion reflects `≈`: it is injective on generators up to the
 source setoid, for EVERY X, with no hypothesis. 

 --------
 该插入反映了 `≈`：它在生成元上是单射的，直到源集合的等价类，对每个 X，且没有任何假设。
*)
Lemma free_mon_insert_reflects {X : SetoidObject} (a b : carrier X) :
  word_eq (Datatypes.cons a Datatypes.nil)
          (Datatypes.cons b Datatypes.nil) → a ≈ b.
Proof. intro H; inversion H; assumption. Qed.

(* Two setoids on ONE carrier, [bool]: the discrete one, and the coarsest one, which identifies everything. / 同一载体上的两个集合等价关系，[bool]：一个是离散的，另一个是最粗的，它将所有元素都视为相同。 *)
Definition MonTwoObj : SetoidObject :=
  {| carrier := bool ; is_setoid := eq_Setoid bool |}.

Program Definition Blur_Setoid : Setoid bool :=
  {| equiv := fun _ _ => True |}.
Next Obligation. constructor; repeat intro; exact Logic.I. Qed.

Definition BlurObj : SetoidObject :=
  {| carrier := bool ; is_setoid := Blur_Setoid |}.

(* Over the discrete setoid the two generators stay apart... / 在离散等价类上，这两个生成元保持分离... *)
Theorem free_mon_two_generators_distinct : @word_eq MonTwoObj
  (Datatypes.cons true Datatypes.nil)
  (Datatypes.cons false Datatypes.nil) → False.
Proof.
  intro H.
  assert (K : true = false)
    by exact (free_mon_insert_reflects (X:=MonTwoObj) true false H).
  discriminate K.
Qed.

(*
 ...and over the coarse setoid on the SAME carrier they are
 identified.  This is what doing the construction at [Sets] rather
 than at [Coq] buys, and it is the fact the header's transport
 argument rests on. 

 --------
 ...并且在相同载体上的粗集合上它们被识别。这正是选择在 [Sets] 而不是在 [Coq] 进行构造的好处，而这也是头部的传递参数所依赖的事实。
*)
Definition free_mon_blur_identifies : @word_eq BlurObj
  (Datatypes.cons true Datatypes.nil)
  (Datatypes.cons false Datatypes.nil) :=
  @we_cons BlurObj true false Datatypes.nil Datatypes.nil Logic.I
    (@we_nil BlurObj).

(*
   * ** The same separations by mapping out

   The probe sends each letter of the discrete two-element setoid to
   the corresponding one-letter list in Coproduct.v's
   (list bool, ++, nil).  No new monoid is built. 

   --------
   * ** 通过映射相同的分离

   探针将离散的双元素集合中的每个字母发送到 Coproduct.v 中对应的单字母列表
   (list bool, ++, nil)。没有构建新的幺半群。
*)

Definition two_letter : carrier MonTwoObj → carrier (mon_ob ListBoolMon) :=
  fun x => Datatypes.cons x Datatypes.nil.

Definition two_probe : FreeMonSetsObject MonTwoObj ~{MonS}~> ListBoolMon :=
  free_mon_hom two_letter (fun a b H => f_equal two_letter H).

(* The probe's value at a two-letter word COMPUTES. / 探针在一个两个字母的单词上的值会被计算。 *)
Example two_probe_word2 :
  mon_fun two_probe
    (Datatypes.cons true (Datatypes.cons false Datatypes.nil))
    = bword2 true false := eq_refl.

Theorem free_mon_two_generators_distinct_via_probe : @word_eq MonTwoObj
  (Datatypes.cons true Datatypes.nil)
  (Datatypes.cons false Datatypes.nil) → False.
Proof.
  intro H.
  assert (K : mon_fun two_probe (Datatypes.cons true Datatypes.nil)
                = mon_fun two_probe (Datatypes.cons false Datatypes.nil)).
  { exact (free_mon_extend_respects two_letter
             (fun a b E => f_equal two_letter E) _ _ H). }
  cbn in K; discriminate K.
Qed.

(*
 A two-letter word is not equivalent to any one-letter word, so the
 free monoid is not collapsed by length either. 

 --------
 一个两个字母的单词不等于任何一个字母的单词，因此自由幺半群也不会因为长度而被压缩。
*)
Theorem free_mon_word2_not_letter (c : bool) : @word_eq MonTwoObj
  (Datatypes.cons true (Datatypes.cons false Datatypes.nil))
  (Datatypes.cons c Datatypes.nil) → False.
Proof.
  intro H.
  assert (K : mon_fun two_probe
                (Datatypes.cons true (Datatypes.cons false Datatypes.nil))
                = mon_fun two_probe (Datatypes.cons c Datatypes.nil)).
  { exact (free_mon_extend_respects two_letter
             (fun a b E => f_equal two_letter E) _ _ H). }
  cbn in K; discriminate K.
Qed.

(*
   * * Universe guard

   The three headline constants carry no [Set] pin.  This is not merely
   read off their constraint blocks: the section below declares
   [Set < uo] and elaborates all three at levels strictly above it.
   The two levels are [Sets]'s own carrier and object universes, in
   that order for [FreeMonSetsObject].  The other two are stated by
   ascribing [Sets@{uo uso}] rather than by an explicit instance, for
   the portability reason recorded at the section itself.  CORRECTION
   (#471): a fourth is guarded the same way, the hom-set form
   [free_mon_sets_adjunction_hom]. 

   --------
   * * 宇宙守护

   三个主要常量不携带 [Set] 引脚。这不仅仅是从它们的约束块中读出的：下面的部分声明了 [Set < uo] 并在严格高于它的层次上详细说明了三者。两个层次是 [Sets] 自己的载体和对象宇宙，对于 [FreeMonSetsObject] 按此顺序。其他两个通过归属 [Sets@{uo uso}] 而不是显式实例来说明，这是出于该部分记录的可移植性原因。更正（#471）：第四个以相同方式受保护，同构集形式为 [free_mon_sets_adjunction_hom]。
*)

Section FreeAboveSet.

  Universe uo uso.
  Constraint Set < uo.
  Constraint uo < uso.

  Check FreeMonSetsObject@{uso uo}.
  (*
 PORTABILITY: the last two are written as ASCRIPTIONS of the SOURCE
 category rather than as explicit universe instances, because the
 number of universes a functor and an adjunction carry here is NOT
 stable across the supported versions -- [FreeMonSets] takes five on
 Rocq 9.1 and six on Coq 8.19/8.20, so a literal [@{uo uso _ _ _}]
 builds on one and fails on the others with “Universe instance
 length is 5 but should be 6”.  [Sets] has a stable two-universe
 signature, so ascribing it is version-independent and states the
 same thing.  The guard still discriminates: the same ascription
 shape applied to a [Set]-pinned functor is REJECTED (checked
 against [Rng_Forget_Mon], which cannot take a [Rng] above [Set]). 

 --------
 可移植性：最后两个被写作来源类别的注明（ASCRIPTIONS），而不是显式的宇宙实例，因为这里函子和伴随所承载的宇宙数量在支持的版本中是不稳定的——[FreeMonSets] 在 Rocq 9.1 中需要五个，在 Coq 8.19/8.20 中需要六个，所以字面上的 [@{uo uso _ _ _}] 在一个版本上可以构建，而在其他版本上会失败，报错为“宇宙实例长度为 5，但应该为 6”。[Sets] 有一个稳定的双宇宙签名，因此注明它与版本无关，并陈述相同内容。守卫仍然进行区分：相同的注明形状应用于 [Set] -固定函子会被拒绝（检查 [Rng_Forget_Mon]，它不能接受高于 [Set] 的 [Rng]）。
*)
  Check (FreeMonSets : Sets@{uo uso} ⟶ _).
  Check (free_mon_sets_adjunction : @Adjunction _ Sets@{uo uso} _ _).
  Check (free_mon_sets_adjunction_hom : @Adjunction _ Sets@{uo uso} _ _).

End FreeAboveSet.

(* Instrument check: [Fail] does report failures in this file. / 仪器检查：[Fail]在此文件中确实报告了故障。 *)
Fail Definition free_mon_instrument_check : False := Logic.I.
