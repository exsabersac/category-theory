Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Kleisli.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Mon.Coproduct.
Require Import Category.Instance.Mon.Free.
Require Import Category.Instance.Smgrp.

Generalizable All Variables.

(* * * The monoid monad W₀ and its algebras / * * 单子幺半群 W₀ 及其代数 *)

(*
 Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 Springer GTM 5, 1998, §VI.4, Exercise 1, printed p. 146 (PDF
 p. 155) — maclane:VI.4:ex1
 Book: Awodey, “Category Theory”, 1st ed., Carnegie Mellon pre-print,
 September 2005, §10.3, Example 10.7, printed p. 276 (PDF
 p. 285) — awodey:10.3:example7; §10.6, Exercise 6, printed
 p. 291 (PDF p. 300) — awodey:10:ex6
 Book: Riehl, “Category Theory in Context”, Example 5.1.4(ii), printed
 pp. 183-184 (PDF pp. 203-204) — riehl:5.1:example4;
 Example 5.2.6(iii),
 printed pp. 189-190 (PDF pp. 209-210) — riehl:5.2:example6;
 Example 5.2.11(ii), printed p. 191 (PDF p. 211) —
 riehl:5.2:example11
 nLab: https://ncatlab.org/nlab/show/free+monoid
 nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad
 nLab: https://ncatlab.org/nlab/show/monadic+functor
 nLab: https://ncatlab.org/nlab/show/Kleisli+category

 WHAT THE BOOKS SAY, read from the page image and the PDFs.
 Mac Lane, Exercise 1: “Let W₀ be the monad in Set defined by the
 forgetful functor Mon→Set.  Show that a W₀-algebra is a set M with
 a string ν₀, ν₁, … of n-ary operations νₙ, where ν₀ : * → M is the
 unit of the monoid M and νₙ is the n-fold product.”
 Awodey, Example 10.7: for the free monoid adjunction F : Sets ⇄
 Mon : U, T(X) is the “strings over X”, η “the usual 'string of
 length one' operation”, and μ of a string of strings “the string of
 their elements”; a T-algebra α : TA → A has α[a] = a and
 α(μ([[…], …, […]])) = α(α[…], …, α[…]); a monoid gives one by
 m[m1, …, mn] = m1 · … · mn, the monoid is recovered “by u = m(−)
 for the unit and x · y = m(x, y) for the multiplication”, and
 “every T-algebra is of this form for a unique monoid (exercise!)”.
 Exercise 10.6.6: “Show that any T-algebra α : TA → A for this monad
 comes from a monoid structure on A (exhibit the monoid
 multiplication and unit element).”
 Riehl, Example 5.1.4(ii): “The free monoid monad is induced by the
 free ⊣ forgetful adjunction between monoids and sets … TA = ∐_{n≥0}
 Aⁿ, that is, TA is the set of finite lists of elements in A …  The
 components of the multiplication µA : T²A → TA are the
 concatenation functions”.  Example 5.2.6(iii): an algebra is a map
 α : ∐_{n≥0} Aⁿ → A, whose unit triangle “asserts that the unary
 operation α1 is the identity”, and whose square (5.2.7) “demands
 that the result of applying the (m1 + ⋯ + mn)-ary operation to the
 concatenated list is the same as applying the n-ary operation to
 the results of applying the mi-ary operations to each sublist”;
 “the category of algebras for the free monoid monad is isomorphic
 to the category Monoid”.  Example 5.2.11(ii): in the Kleisli
 category “a map from A to B is a function A → ∐_{n≥0} Bⁿ … i.e., a
 list of elements of B”.

 THE MONAD.  The issue's QA correction asks for W₀ as the monad of an
 existing free-monoid adjunction at Sets, not a second free monoid.
 [W0F] is U ◯ F with F Instance/Mon/Free.v's [FreeMonSets] (#400, PR
 #1219) and U [Mon_Forget] at Theory/Algebra/Monoid/Hom.v's [Mon] at
 (Sets, ×); [W0] is Monad/Comparison.v's transparent
 [Adjunction_Induced_Monad] of Free.v's [free_mon_sets_adjunction_hom],
 the hom-set form of the same adjunction that #471 adds to Free.v
 (same left adjoint and insertion; its unit and forward transpose are
 those of [free_mon_sets_adjunction] at [eq_refl]), whose counit is
 the fold of the identity by conversion where the universal-arrow
 form's is not (Free.v's header, CORRECTION (#471)).  At [eq_refl]:
 W₀ X is the setoid of words ([W0_obj]) with carrier list X
 ([W0_carrier]); η is the insertion as a setoid map ([W0_ret]) and
 a ↦ ⟨a⟩ ([W0_ret_fun]); μ = U ε F ([W0_join_counit]) is the
 concatenation [wconcat] of a word of words ([W0_join_fun],
 [W0_join_literal], [W0_join_nil]).  The laws are those of the
 adjunction.  W₀ f is the letterwise map at ≈ ([W0_map]) and refused at
 [eq_refl] at a variable word and at a one-letter word
 (Test/ProbeWord471.v, R4 and R5): the free functor's action on arrows
 is read through the universal arrows.  The books' ∐_{n≥0} Xⁿ is
 [Tup0Sum X], the sigma of [Tup0 X n] (Tup0 X 0 = unit and
 Tup0 X (S n) = #470's Tup X n = X^(n+1); #470's Instance/Smgrp.v
 announces this extension under the same name, Pow being taken by
 Structure/Topos.v and Instance/Fun/Discrete.v), compared letterwise
 and False across lengths; [W0_sum_iso] is W₀ X ≅ ∐_{n≥0} Xⁿ in Sets,
 each direction at [eq_refl] (a word to its length and tuple,
 [W0_sum_iso_to]; a tuple to its word, [W0_sum_iso_from]), the round
 trip word → tuple → word refused at [eq_refl] at a variable word
 (Test/ProbeWord471.v, R3).

 AN ALGEBRA IS A MONOID (Awodey's Exercise 10.6.6; Riehl's “any
 algebra … defines a monoid”).  For an algebra α on S, [alg_mul α]
 x y = α⟨x y⟩ and [alg_one α] = α⟨⟩; associativity ([alg_mul_assoc])
 and the unit laws ([alg_one_l], [alg_one_r]) come from the unit law
 α⟨x⟩ ≈ x ([alg_unit]) and the action law read on words of words
 ([alg_action]), at ≈, and [alg_monoid α] is the monoid.  “Comes from
 a monoid structure”: α⟨m1 … mn⟩ ≈ m1 ⋯ mn, α is the fold of its
 monoid ([alg_fold]); “for a unique monoid”: a monoid on the same
 carrier whose products α computes has α's multiplication and unit,
 up to ≈ ([alg_monoid_unique]).

 EM W₀ ≅ Mon (Awodey's Example 10.7; Riehl's Example 5.2.6(iii)).
 [W0Alg] is Set^{W₀}.  [Mon_K] is Monad/Comparison.v's
 [EM_Comparison] of the adjunction: K M = ⟨M, U ε_M⟩, its structure
 map the fold of the identity ([Mon_K_alg], [Mon_K_alg_fun]), ν₀ = 1
 ([Mon_K_nu0]), ν₁ x = x · 1 ([Mon_K_nu1]), ν₂(x, y) = x · (y · 1)
 ([Mon_K_nu2]) and K f = f ([Mon_K_map]), all at [eq_refl]; ν₁ x = x
 holds at ≈ (C28) and is refused at [eq_refl] (R6).  [EM_to_Mon] sends
 an algebra to [alg_monoid] and a map to itself ([EM_to_Mon_carrier],
 [EM_to_Mon_mul], [EM_to_Mon_one], [EM_to_Mon_map]).
 [Mon_EM_iso : Mon ≅[Cat] W0Alg] has the legs [Mon_K] and [EM_to_Mon]
 ([Mon_EM_iso_to], [Mon_EM_iso_from]) and every component of both
 natural isomorphisms the identity, to and from, at [eq_refl]
 ([Mon_EM_iso_to_from_component], [Mon_EM_iso_from_to_component]).
 It is built from the two component isomorphisms, as #466 and #470
 build theirs, because through Theory/Equivalence.v's
 [Equivalence_to_Cat_Iso] the component of [iso_from_to] is refused
 (R13) while that of [iso_to_from] holds (C48).  An isomorphism in Cat
 is, by Instance/Cat.v, an equivalence of categories, which the
 identity components bring toward Riehl's “isomorphic”; a strict
 isomorphism is refused.  The round trips keep the carrier, the unit
 and the maps at [eq_refl] ([Mon_rt_carrier], [Mon_rt_one],
 [Mon_rt_hom], [EM_rt_carrier], [EM_rt_alg_hom]) and return the
 multiplication as x · (y · 1) ([Mon_rt_mul_fun]; at ≈,
 [Mon_rt_mul]) and the structure map as the fold of the derived
 monoid ([EM_rt_alg_fun]; at ≈, [alg_fold]), so the multiplication
 (R7), the structure map (R9), the whole objects (R8, R10) and the
 composites against the identity functors (R11, R12) are refused at
 [eq_refl].  [Mon_EM_equivalence] is the equivalence with the same
 components ([Mon_EM_counit_component], [Mon_EM_unit_component]), and
 [Mon_Forget_Monadic : Monadic UMonS] the monadicity of monoids over
 Set in Monad/Comparison.v's sense.

 THE FORGETFUL FUNCTORS (Awodey §10.3; the issue's appended box (a)).
 [W0_Forget] is U^{W₀}, Monad/Eilenberg/Moore/Adjunction.v's
 [EM_Forget].  [Mon_K_Forget : W0_Forget ◯ Mon_K ≈ UMonS] is Monad/
 Comparison.v's [EM_Comparison_Forget]; [EM_to_Mon_Forget :
 UMonS ◯ EM_to_Mon ≈ W0_Forget] has identity components; on objects
 and on arrows both hold at [eq_refl] ([Mon_K_Forget_obj],
 [Mon_K_Forget_map], [EM_to_Mon_Forget_obj], [EM_to_Mon_Forget_map]).

 THE KLEISLI CATEGORY (Riehl's Example 5.2.11(ii); the appended box
 (c)).  [W0Kl] is Monad/Kleisli.v's [Kleisli] at W₀, no new
 construction.  At [eq_refl] a Kleisli arrow A ⇝ B IS a setoid map
 A → W₀ B, a list of elements of B for each a ([W0Kl_hom],
 [W0Kl_homset]), and the identity sends a to ⟨a⟩ ([W0Kl_id_fun]);
 composition is the concatenated map at ≈ ([W0Kl_compose]) and refused
 at [eq_refl] (R14, through W₀ f).  Riehl's “a function A → ∐_{n≥0}
 Bⁿ” is [W0Kl_hom_iso]: the Kleisli hom-setoid is isomorphic in Sets
 to the setoid of maps A → [Tup0SumObj B], by postcomposition with
 [W0_sum_iso] ([W0Kl_hom_iso_to], at [eq_refl]).

 MAC LANE'S ν₀, ν₁, … are Instance/Mon/Word/System.v, and Riehl's
 commutative variant (the appended box (b)) Instance/CMon/Free.v.

 THE ISSUE'S PREMISES, dated.  Issue #471 was filed on 2026-07-23.
 Its “no ordinary category Mon” was false when filed: Theory/Algebra/
 Monoid/Hom.v's [Mon] and [Mon_Forget] came with PR #191 (merged
 2026-07-07), as the body's own Riehl append says.  The appends'
 “has no left adjoint” was accurate for Mon when written and has been
 stale since PR #1219 (merged 2026-08-29), whose Instance/Mon/Free.v
 gives FreeMonSets ⊣ Mon_Forget at Sets; for CMon it held until this
 change (Instance/CMon/Free.v).  Their grep “rg '⊣' Instance/CMon.v
 Instance/CMon/ → 0 hits” has been stale since PR #1220 (merged
 2026-08-29), whose Instance/CMon/Grothendieck.v declares
 [grothendieck_adjunction : GrothLeft ⊣ Ab_to_CMon], not a left
 adjoint of [CMon_Forget].  The QA correction's “#296's free-monoid
 universal arrow / adjunction” is #400's at Sets: #296 (PR #1140,
 merged 2026-08-17) delivered Instance/Coq/Monoid/Free.v at Mon Coq.
 Its “a coproduct-of-tensor-powers carrier in Sets is not
 definitionally list X” does not hold on the prescribed route, where
 the carrier of W₀ X IS list X at [eq_refl] ([W0_carrier]): stale
 since PR #1219.  [list_Monad] (Theory/Coq/List.v) is operations only
 and Theory/Coq/Monad/Proofs.v's [IsMonad] covers Identity, arrow and
 Compose alone, as the body says, then and now (both files last
 changed in c429a82b, 2026-06-17).  Its “discharge unit/associativity
 laws here” is supplied by [Adjunction_Induced_Monad] from the
 adjunction.  Of its suggested module Monad/Instance/List.v, the
 directory Monad/Instance does not exist; the files are this one
 (beside #470's Instance/Smgrp/Word.v), its satellite and
 Instance/CMon/Free.v.  Its “CLAUDE.md Key Files index” was accurate
 when filed and has been stale since PR #1284 (merged 2026-09-09),
 which moved the index to docs/INDEX.md.  The body cites constants by
 line number, which this tree replaces by their names.

 STRENGTHS.  Every [Example] holds at [eq_refl], and
 Test/ProbeWord471.v restates each one (C5 to C14, C18 to C27, C29 to
 C38, C40, C41, C43 to C47 and C49 to C56).  At ≈ only: [W0_map],
 [alg_fold], [Mon_rt_mul], [W0Kl_compose] and the inverse laws of the
 isomorphism in Cat.  Two lemmas are Leibniz equalities proved by
 induction, stronger than ≈: [tup_to_list_list_to_tup] and
 [tup0_to_list_list_to_tup0].  Nine proofs end [Defined] (counted by
 token) and eight are load-bearing, measured by closing each alone
 [Qed] in a renamed copy of #471's five files and naming the first
 command that then stops: [W0_sum_iso] ([W0_sum_iso_to]),
 [EM_mon_map] ([EM_to_Mon]), [EM_to_Mon] ([Mon_EM_counit_iso]),
 [Mon_EM_counit_iso] and [Mon_EM_unit_iso] ([Mon_EM_equivalence]),
 [Mon_EM_equivalence] ([Mon_EM_counit_component]), [Mon_EM_iso]
 ([Mon_EM_iso_to]) and [W0Kl_hom_iso] ([W0Kl_hom_iso_to]);
 [Mon_Forget_Monadic] is [Defined] by the data convention only (closed
 [Qed], nothing stops).  Twenty-five lemmas end [Qed].

 UNIVERSES, read off [About] (every name, by script).  The tuples, the
 setoid ∐_{n≥0} Xⁿ and the literal words bind @{o} with caps of the
 standard library only ([list_to_tup_tup_to_list] declares @{o +}, a
 closed @{o} being refused on Coq 8.19 and 8.20, and binds o alone on
 all three).  Everything else is in the section [W0Monad]
 over Sets@{o so} and binds o and so first, with o < so; [wconcat]
 binds them alone.  A closed @{o so} is refused, the free functor's
 internal levels being unbound, so each declares an extensible binder
 and binds after o and so the three levels [FreeMonSets] carries
 beyond Sets's (four on Coq 8.19 and 8.20, Instance/Mon/Free.v's
 PORTABILITY note) and the internal level of Theory/Functor.v's
 [Compose] (o < it): fifty-six names bind those six levels.  Fourteen
 bind five, holding the [Compose] level at so: [Mon_K],
 [Mon_EM_equivalence], [Mon_Forget_Monadic], [Mon_K_Forget], nine
 readbacks of K and [Mon_EM_counit_component], a readback of the
 equivalence.  [Mon_EM_iso] binds o, so, c (o < c, so < c, from
 Instance/Cat.v's [Cat@{c so so so o}]) and the free functor's three.
 Five readbacks comparing across a composite bind a second copy of the
 free functor's levels (eight or nine in all), the two copies never
 being identified by unification.  No [Set] and no equation in any
 block.  No explicit universe instance of a constant of this route is
 written, its binder count differing by version: compiled on Coq
 8.19.2 and 8.20.1, each name that binds the free functor's levels
 (five or more on Rocq 9.1: 76 here, 38 in the satellite and five of
 Instance/Mon/Free.v's six additions, 119 of the 250 names #471 adds)
 binds exactly one level more, and every other name binds the same
 levels, compared by [About] on all 250.

 NOT DELIVERED.  A strict identity of Mon and Set^{W₀} (refused above)
 and an isomorphism in Instance/StrictCat.v.  A computing W₀ f: the
 action on arrows is [FreeMonSets]'s, and a second free functor
 computing letterwise would be a parallel construction, not taken.
 Beck's route to monadicity.  The other exercises of the section
 (#472 to #474).  A lawful [@Monad Coq list].  A comparison of W₀
 with #470's word monad W. 

 --------
 书籍：Mac Lane，《为工作数学家准备的范畴论》，第2版，Springer GTM 5，1998年，第VI.4节，习题1，印刷页146（PDF页155）—— maclane:VI.4:ex1
 书籍：Awodey，《范畴论》，第1版，卡内基梅隆预印本，2005年9月，第10.3节，例10.7，印刷页276（PDF页285）—— awodey:10.3:example7；第10.6节，习题6，印刷页291（PDF页300）—— awodey:10:ex6
 书籍：Riehl，《语境中的范畴论》，例5.1.4(ii)，印刷页183-184（PDF页203-204）—— riehl:5.1:example4；例5.2.6(iii)，印刷页189-190（PDF页209-210）—— riehl:5.2:example6；例5.2.11(ii)，印刷页191（PDF页211）—— riehl:5.2:example11
 nLab：https://ncatlab.org/nlab/show/free+monoid
 nLab：https://ncatlab.org/nlab/show/algebra+over+a+monad
 nLab：https://ncatlab.org/nlab/show/monadic+functor
 nLab：https://ncatlab.org/nlab/show/Kleisli+category书中所说的内容，从页面图像和 PDF 中阅读。Mac Lane，练习 1：“设 W₀ 是由遗忘函子 Mon→Set 定义的 Set 中的单子。”证明 W₀-代数是一个集合 M，并带有一串 n 元运算 ν₀, ν₁, …，其中 ν₀ : * → M 是单元 M 的单位，而 νₙ 是 n 重积。

 Awodey，例 10.7：对于自由单元旁道 F : Sets ⇄ Mon : U，T(X) 是“X 上的字符串”，η 是“通常的‘长度为一的字符串’运算”，μ 是字符串的字符串映射为“它们元素的字符串”；一个 T-代数 α : TA → A 满足 α([a]) = a 并且 α(μ([[…], …, […])) = α(α([…]), …, α([…]))；一个单元给出一个 T-代数通过 m([m1, …, mn]) = m₁ · … · mₙ，单元可通过“u = m(−) 表示单位元素，x · y = m(x, y) 表示乘法”恢复，并且“每个 T-代数都可以以这种形式表示，对应唯一的单元（练习！）”。练习 10.6.6：“证明对于该单子，任意 T-代数 α : TA → A 都来源于 A 上的一个幺半群结构（展示幺半群的乘法和单位元）。”
 Riehl，第 5.1.4(ii) 例子：“自由幺半群单子是由幺半群与集合之间的自由⊣遗忘伴随产生的……TA = ∐_{n≥0} Aⁿ，即 TA 是 A 元素的有限列表的集合……乘法 µA : T²A → TA 的各个分量是连接函数。”例 5.2.6(iii)：一个代数是一个映射 α : ∐_{n≥0} Aⁿ → A，其单位三角形“断言一元运算 α1 是恒等映射”，其平方 (5.2.7)“要求将 (m1 + ⋯ + mn)-元运算应用于连接列表的结果与将 n 元运算应用于将 mi 元运算应用于每个子列表的结果相同”；“自由幺半群单子代数的范畴与 Monoid 范畴同构”。例 5.2.11(ii)：在 Kleisli 范畴中“从 A 到 B 的映射是一个函数 A → ∐_{n≥0} Bⁿ …即一个 B 元素的列表”。单子。该期问题的 QA 修正要求将 W₀ 作为在 Sets 上已有的自由幺半群伴随中的单子，而不是第二个自由幺半群。[W0F] 是 U ◯ F，其中 F 是 Instance/Mon/Free.v 的 [FreeMonSets]（#400, PR #1219），而 U 是 Theory/Algebra/Monoid/Hom.v 中的 [Mon_Forget] 在 (Sets, ×) 上的 [Mon]；[W0] 是 Monad/Comparison.v 的透明 [Adjunction_Induced_Monad]，来自 Free.v 的 [free_mon_sets_adjunction_hom]，同一伴随的同态集形式由 #471 添加到 Free.v（相同的左伴随及插入；其单位和前向换位是 [free_mon_sets_adjunction] 在 [eq_refl] 上的定义），其余单位是通过转换对身份的折叠，而通用箭头形式则不是（Free.v 的头部，修正 (#471)）。在 [eq_refl] ：
 W₀ X 是具有载体列表 X 的词（[W0_obj]）的等值类（[W0_carrier]）；η 是作为等值类映射的插入（[W0_ret]），并且 a ↦ ⟨a⟩（[W0_ret_fun]）；μ = U ε F（[W0_join_counit]）是词的词的连接 [wconcat]（[W0_join_fun], [W0_join_literal], [W0_join_nil]）。规律是伴随的规律。W₀ f 是在 ≈（[W0_map]）下逐字映射，并且在 [eq_refl] 对变量词和单字词拒绝（Test/ProbeWord471.v，R4 和 R5）：自由函子的箭头作用通过通用箭头来读取。书籍的 ∐_{n≥0} Xⁿ 是 [Tup0Sum X]，[Tup0 X n] 的 sigma（Tup0 X 0 = unit 并且 Tup0 X (S n) = #470 的 Tup X n = X^(n+1); #470 的 Instance/Smgrp.v 在同名下宣布了这个扩展，Pow 已被 Structure/Topos.v 和 Instance/Fun/Discrete.v 占用），按字母比较，并在长度上为 False；[W0_sum_iso] 在集合中是 W₀ X ≅ ∐_{n≥0} Xⁿ，每个方向在 [eq_refl]（从一个单词到其长度和元组，[W0_sum_iso_to]；从元组到其单词，[W0_sum_iso_from]），循环转换 单词 → 元组 → 单词 在 [eq_refl] 被拒绝，在一个可变单词中（Test/ProbeWord471.v, R3）。代数是一个幺半群（Awodey 的练习 10.6.6；Riehl 的“任何代数……定义一个幺半群”）。对于位于 S 上的代数 α，[alg_mul α] x y = α⟨x y⟩ 且 [alg_one α] = α⟨⟩；结合性（[alg_mul_assoc]）和单位律（[alg_one_l], [alg_one_r]）来自单位律 α⟨x⟩ ≈ x（[alg_unit]）以及在单词的单词上读取的作用律（[alg_action]），在 ≈ 下，[alg_monoid α] 是幺半群。“来自幺半群结构”：α⟨m1 … mn⟩ ≈ m1 ⋯ mn，α 是其幺半群的折叠（[alg_fold]）；“对于唯一的幺半群”：在相同载体上的幺半群，其乘积 α 所计算的具有 α 的乘法和单位，至 ≈（[alg_monoid_unique]）。EM W₀ ≅ Mon (Awodey 的例子 10.7；Riehl 的例子 5.2.6(iii))。[W0Alg] 是 Set^{W₀}。[Mon_K] 是 Monad/Comparison.v 的 [EM_Comparison] 关于伴随: K M = ⟨M, U ε_M⟩，其结构映射是恒等的折叠 ([Mon_K_alg], [Mon_K_alg_fun])，ν₀ = 1 ([Mon_K_nu0])，ν₁ x = x · 1 ([Mon_K_nu1])，ν₂(x, y) = x · (y · 1) ([Mon_K_nu2]) 并且 K f = f ([Mon_K_map])，全部在 [eq_refl]；ν₁ x = x 在 ≈ (C28) 成立，在 [eq_refl] (R6) 被拒绝。[EM_to_Mon] 将一个代数映射到 [alg_monoid] 并且将一个映射映射到其自身 ([EM_to_Mon_carrier], [EM_to_Mon_mul], [EM_to_Mon_one], [EM_to_Mon_map])。[Mon_EM_iso : Mon ≅[Cat] W0Alg] 有腿 [Mon_K] 和 [EM_to_Mon] ([Mon_EM_iso_to], [Mon_EM_iso_from])，并且两者的每个自然同构的组成部分都是恒等，从与到，在 [eq_refl] ([Mon_EM_iso_to_from_component], [Mon_EM_iso_from_to_component])它由两个分量同构构建，如 #466 和 #470 构建它们的，因为通过 Theory/Equivalence.v 的 [Equivalence_to_Cat_Iso]，[iso_from_to] 的分量被拒绝（R13），而 [iso_to_from] 的分量成立（C48）。Cat 中的同构根据 Instance/Cat.v，是一个范畴等价，这些恒等分量使其接近 Riehl 的“同构”；严格同构被拒绝。往返保持载体、单元和位于 [eq_refl]（[Mon_rt_carrier], [Mon_rt_one], [Mon_rt_hom], [EM_rt_carrier], [EM_rt_alg_hom]）上的映射，并返回乘法 x · (y · 1)（[Mon_rt_mul_fun]；在 ≈, [Mon_rt_mul]）以及派生幺半群的折叠结构映射（[EM_rt_alg_fun]；在 ≈, [alg_fold]），因此乘法（R7）、结构映射（R9）、完整对象（R8, R10）以及针对恒等函子的复合（R11, R12）在 [eq_refl] 上被拒绝。[Mon_EM_equivalence] 是具有相同分量（[Mon_EM_counit_component], [Mon_EM_unit_component]）的等价，[Mon_Forget_Monadic : Monadic UMonS] 是在 Monad/Comparison.v 意义下 Set 上幺半群的幺模性。健忘函子（Awodey §10.3；该问题附加的框(a)）。
 [W0_Forget] 是 U^{W₀}，Monad/Eilenberg/Moore/Adjunction.v 的 [EM_Forget]。[Mon_K_Forget : W0_Forget ◯ Mon_K ≈ UMonS] 是 Monad/Comparison.v 的 [EM_Comparison_Forget]；[EM_to_Mon_Forget : UMonS ◯ EM_to_Mon ≈ W0_Forget] 有恒等分量；在对象和箭头上在 [eq_refl]（[Mon_K_Forget_obj]、[Mon_K_Forget_map]、[EM_to_Mon_Forget_obj]、[EM_to_Mon_Forget_map]）都成立。KLEISLI 范畴（Riehl 的例 5.2.11(ii)；附加的方框 (c)）。[W0Kl] 是 Monad/Kleisli.v 中的 [Kleisli] 在 W₀ 处，没有新的构造。在 [eq_refl] 处，一个 Kleisli 箭头 A ⇝ B 是一个集合等价映射 A → W₀ B，每个 a 对应 B 的元素列表（[W0Kl_hom]、[W0Kl_homset]），恒等映射将 a 映射为 ⟨a⟩（[W0Kl_id_fun]）；合成是在 ≈ 处的连接映射（[W0Kl_compose]），并在 [eq_refl] 处被拒绝（R14，通过 W₀ f）。Riehl 的“一个函数 A → ∐_{n≥0} Bⁿ”是 [W0Kl_hom_iso]：Kleisli 同态集合在集合中与映射 A → [Tup0SumObj B] 的集合等价同构，通过与 [W0_sum_iso] 后合成（[W0Kl_hom_iso_to]，在 [eq_refl] 处）。

 MAC LANE 的 ν₀、ν₁、… 位于 Instance/Mon/Word/System.v，而 Riehl 的交换变体（附加的方框 (b)）位于 Instance/CMon/Free.v。该问题的前提，有日期。问题 #471 于 2026-07-23 提出。其“非普通类别 Mon”在提出时是错误的：Theory/Algebra/Monoid/Hom.v 的 [Mon] 和 [Mon_Forget] 随 PR #191（已合并，2026-07-07）一起提交，正如正文的 Riehl 附录所述。附录中“没有左伴随”的描述在编写 Mon 时是准确的，并且自 PR #1219（已合并，2026-08-29）以来已经过时，该 PR 的 Instance/Mon/Free.v 给出了 FreeMonSets ⊣ Mon_Forget 在 Sets 上；对于 CMon 这一描述一直成立，直到此更改（Instance/CMon/Free.v）。他们的 grep “rg '⊣' Instance/CMon.v Instance/CMon/ → 0 hits” 自 PR #1220（已合并，2026-08-29）以来就已过时，该 PR 的 Instance/CMon/Grothendieck.v 声明了 [grothendieck_adjunction : GrothLeft ⊣ Ab_to_CMon]，而不是 [CMon_Forget] 的左伴随。QA 修正的“#296 的自由幺半群通用箭头/伴随”是 #400 在 Sets 上的：#296（PR #1140，于 2026-08-17 合并）在 Mon Coq 中提供了 Instance/Coq/Monoid/Free.v。它的“在 Sets 中的一个张量幂的余积载体在定义上不是 list X”在规定路线下不成立，其中 W₀ X 的载体在 [eq_refl]（[W0_carrier]）上是 list X：自 PR #1219 以来已过时。[list_Monad]（Theory/Coq/List.v）仅为操作，而 Theory/Coq/Monad/Proofs.v 的 [IsMonad] 仅涵盖 Identity、arrow 和 Compose，如正文所述，当时和现在（两个文件在 c429a82b，2026-06-17 最后更改）。它的“在这里解除 unit/结合律”由 adjunction 提供的 [Adjunction_Induced_Monad] 供应。关于其建议的模块 Monad/Instance/List.v，目录 Monad/Instance 不存在；相关文件有这一文件（在 #470 的 Instance/Smgrp/Word.v 旁边）、它的附属文件以及 Instance/CMon/Free.v。其“CLAUDE.md 关键文件索引”在提交时是准确的，但自 PR #1284（2026-09-09 合并）以来已过时，该 PR 将索引移至 docs/INDEX.md。正文通过行号引用常量，而此代码树用它们的名字替代了行号。优势。每个 [Example] 在 [eq_refl] 时保持有效，并且 Test/ProbeWord471.v 重新陈述每一个（C5 到 C14，C18 到 C27，C29 到 C38，C40，C41，C43 到 C47 和 C49 到 C56）。仅在 ≈ 时：[W0_map]，[alg_fold]，[Mon_rt_mul]，[W0Kl_compose] 以及 Cat 中同构的逆律。两个引理是通过归纳法证明的莱布尼茨等式，比 ≈ 更强：[tup_to_list_list_to_tup] 和 [tup0_to_list_list_to_tup0]。九个证明以 [Defined] 结束（按标记计数），其中八个是承重的，通过在 #471 的五个文件的重命名副本中单独关闭每个 [Qed] 并命名随后停止的第一个命令来测量：[W0_sum_iso]（[W0_sum_iso_to]）、[EM_mon_map]（[EM_to_Mon]）、[EM_to_Mon]（[Mon_EM_counit_iso]）、[Mon_EM_counit_iso] 和 [Mon_EM_unit_iso]（[Mon_EM_equivalence]）、[Mon_EM_equivalence]（[Mon_EM_counit_component]）、[Mon_EM_iso]（[Mon_EM_iso_to]）以及 [W0Kl_hom_iso]（[W0Kl_hom_iso_to]）；[Mon_Forget_Monadic] 仅根据数据规范是 [Defined]（关闭 [Qed]，无任何停止）。二十五个引理以 [Qed] 结束。UNIVERSES，逐个读取 [About]（每个名字，按照脚本）。元组，集合∐_{n≥0} Xⁿ 和文字绑定 @{o}，仅使用标准库的大小写（[list_to_tup_tup_to_list] 声明 @{o +}，在 Coq 8.19 和 8.20 中拒绝闭合的 @{o}，并且在三者上仅绑定 o）。其他一切在 [W0Monad] 节中关于 Sets@{o so}，并且先绑定 o 和 so，且 o < so；[wconcat] 单独绑定它们。闭合的 @{o so} 会被拒绝，自由函子的内部层未绑定，因此每个都声明一个可扩展的绑定器，并在 o 和 so 之后绑定 [FreeMonSets] 中的三个层，这三个层超出了 Sets 的层（在 Coq 8.19 和 8.20 以及 Instance/Mon/Free.v 的可移植性说明中为四层）以及 Theory/Functor.v 的内部层 [Compose]（o < it）：五十六个名字绑定这六个层。十四
 绑定五，保持 [Compose] 的级别如下：[Mon_K]，
 [Mon_EM_equivalence]，[Mon_Forget_Monadic]，[Mon_K_Forget]，九
 个 K 和 [Mon_EM_counit_component] 的回读，以及等价的回读。[Mon_EM_iso] 绑定 o、so、c（o < c，so < c，来自 Instance/Cat.v 的 [Cat@{c so so so o}]）以及自由函子三个。五个回读比较跨复合绑定自由函子的第二个副本的级别（总共八或九个），这两个副本从未被统一识别。没有 [Set]，也没有任何块中的方程。没有为此路径的一个常量显式写入宇宙实例，其绑定器数量因版本而异：在 Coq 8.19.2 和 8.20.1 上编译，每个绑定自由函子级别的名称（在 Rocq 9.1 上为五个或更多：这里为 76，在 satellite 中为 38，以及 Instance/Mon/Free.v 的六个新增项中的五个，#471 添加的 250 个名称中的 119 个）正好绑定多一个级别，而每个其他名称绑定的级别相同，由 [About] 在所有 250 个名称上进行比较。未交付。在Instance/StrictCat.v中，有Mon和Set^{W₀}的严格同一性（上文已拒绝）以及一个同构。计算W₀ f：箭头上的作用是[FreeMonSets]的，而第二个逐字计算的自由函子将是一个平行构造，未采纳。Beck的monadic性路径。本节的其他练习（#472到#474）。一个合法的[@Monad Coq list]。将W₀与#470的词幺半群W进行比较。
*)

(* ------------------------------------------------------------------------ *)
(* * ** Tuples of every length: [Tup0 A n] is Aⁿ, n ≥ 0 / * ** 每种长度的元组：[Tup0 A n] 是 Aⁿ，n ≥ 0 *)

(* Tup0 A 0 = unit and Tup0 A (S n) = Tup A n = A^(n+1). / Tup0 A 0 = 单位, 且 Tup0 A (S n) = Tup A n = A^(n+1). *)
Definition Tup0@{o} (A : Type@{o}) (n : nat) : Type@{o} :=
  match n with
  | O => poly_unit@{o}
  | S n' => Tup@{o} A n'
  end.

(* The letters of a positive tuple, in order. / 正元组中的字母，按顺序排列。 *)
Fixpoint tup_to_list@{o} {A : Type@{o}} (n : nat) : Tup@{o} A n → list A :=
  match n as n0 return Tup A n0 → list A with
  | O => fun a => Datatypes.cons a Datatypes.nil
  | S n' => fun t => Datatypes.cons (fst t) (tup_to_list n' (snd t))
  end.

Definition tup0_to_list@{o} {A : Type@{o}} (n : nat) :
  Tup0@{o} A n → list A :=
  match n as n0 return Tup0 A n0 → list A with
  | O => fun _ => Datatypes.nil
  | S n' => tup_to_list n'
  end.

(* A non-empty list a :: l as a tuple of length (length l) + 1. / 一个非空列表 a :: l 作为长度为 (length l) + 1 的元组。 *)
Fixpoint list_to_tup@{o} {A : Type@{o}} (a : A) (l : list A) :
  Tup@{o} A (length l) :=
  match l as l0 return Tup A (length l0) with
  | Datatypes.nil => a
  | Datatypes.cons b l' => (a, list_to_tup b l')
  end.

Definition list_to_tup0@{o} {A : Type@{o}} (l : list A) :
  Tup0@{o} A (length l) :=
  match l as l0 return Tup0 A (length l0) with
  | Datatypes.nil => ttt
  | Datatypes.cons a l' => list_to_tup a l'
  end.

(* Leibniz: list → tuple → list is the identity. / 莱布尼茨：列表 → 元组 → 列表 是恒等式。 *)
Lemma tup_to_list_list_to_tup@{o} {A : Type@{o}} (a : A) (l : list A) :
  tup_to_list (length l) (list_to_tup a l) = Datatypes.cons a l.
Proof.
  revert a; induction l as [|b l IH]; intro a; simpl; [ reflexivity | ].
  now rewrite IH.
Qed.

Lemma tup0_to_list_list_to_tup0@{o} {A : Type@{o}} (l : list A) :
  tup0_to_list (length l) (list_to_tup0 l) = l.
Proof.
  destruct l as [|a l]; [ reflexivity | apply tup_to_list_list_to_tup ].
Qed.

Lemma tup_to_list_respects@{o} {X : SetoidObject@{o o}} (n m : nat)
  (t : Tup@{o} X n) (u : Tup@{o} X m) :
  tup_eq n m t u → word_eq (tup_to_list n t) (tup_to_list m u).
Proof.
  revert m t u; induction n as [|n IH]; intros [|m] t u H; simpl in *;
    try contradiction.
  - exact (we_cons _ _ _ _ H we_nil).
  - destruct H as [H1 H2]. exact (we_cons _ _ _ _ H1 (IH _ _ _ H2)).
Qed.

Lemma list_to_tup_respects@{o} {X : SetoidObject@{o o}} (a b : X)
  (l l' : list X) :
  a ≈ b → word_eq l l' →
  tup_eq (length l) (length l') (list_to_tup a l) (list_to_tup b l').
Proof.
  intros Hab H; revert a b Hab;
    induction H as [|c d u v Hcd Huv IH]; intros a b Hab; simpl;
    [ exact Hab | ].
  split; [ exact Hab | exact (IH c d Hcd) ].
Qed.

(*
 Tuple → list → tuple is the identity up to ≈, across the length, which
 is propositional only.  The binder is extensible because Coq 8.19 and
 8.20 refuse a closed @{o} here (“Universe … is unbound”); the extra
 level is minimized away, and the lemma binds o alone on every
 version. 

 --------
 元组 → 列表 → 元组 在长度上是恒等的，最大误差为≈，这只是命题性的。绑定器是可扩展的，因为 Coq 8.19 和 8.20 在这里拒绝闭合的 @{o}（“宇宙……未绑定”）；额外的层级被最小化消除，并且该引理在每个版本中仅绑定 o。
*)
Lemma list_to_tup_tup_to_list@{o +} {X : SetoidObject@{o o}} (n : nat)
  (t : Tup@{o} X n) :
  match tup_to_list n t return Type@{o} with
  | Datatypes.nil => False
  | Datatypes.cons a l => tup_eq (length l) n (list_to_tup a l) t
  end.
Proof.
  induction n as [|n IH]; simpl; [ reflexivity | ].
  destruct t as [a t']. simpl.
  specialize (IH t').
  destruct (tup_to_list n t') as [|b l]; [ contradiction | ].
  split; [ reflexivity | exact IH ].
Qed.

(* ------------------------------------------------------------------------ *)
(** ** ∐_{n≥0} Xⁿ as a setoid / ** ∐_{n≥0} Xⁿ 作为集合类 *)

(* Letterwise ≈ on tuples of every length, True on the two empty tuples and False across lengths. / Letterwise ≈ 在每个长度的元组上，两个空元组上为 True，而不同长度上为 False。 *)
Definition tup0_eq@{o} {X : SetoidObject@{o o}} (n m : nat) :
  Tup0@{o} X n → Tup0@{o} X m → Type@{o} :=
  match n as n0, m as m0 return Tup0 X n0 → Tup0 X m0 → Type@{o} with
  | O, O => fun _ _ => True
  | S n', S m' => tup_eq n' m'
  | _, _ => fun _ _ => False
  end.

Lemma tup0_eq_refl@{o} {X : SetoidObject@{o o}} (n : nat)
  (t : Tup0@{o} X n) : tup0_eq n n t t.
Proof. destruct n; [ exact Logic.I | apply tup_eq_refl ]. Qed.

Lemma tup0_eq_sym@{o} {X : SetoidObject@{o o}} (n m : nat)
  (t : Tup0@{o} X n) (u : Tup0@{o} X m) :
  tup0_eq n m t u → tup0_eq m n u t.
Proof.
  destruct n, m; simpl; try contradiction;
    [ intros _; exact Logic.I | apply tup_eq_sym ].
Qed.

Lemma tup0_eq_trans@{o} {X : SetoidObject@{o o}} (n m p : nat)
  (t : Tup0@{o} X n) (u : Tup0@{o} X m) (v : Tup0@{o} X p) :
  tup0_eq n m t u → tup0_eq m p u v → tup0_eq n p t v.
Proof.
  destruct n, m, p; simpl; try contradiction; try (intros; exact Logic.I).
  apply tup_eq_trans.
Qed.

Definition Tup0Sum@{o} (X : SetoidObject@{o o}) : Type@{o} :=
  sigT (fun n : nat => Tup0@{o} X n).

Definition Tup0Sum_Setoid@{o} (X : SetoidObject@{o o}) :
  Setoid@{o o} (Tup0Sum@{o} X) :=
  {| equiv := fun w v => tup0_eq (projT1 w) (projT1 v) (projT2 w) (projT2 v)
   ; setoid_equiv :=
       {| Equivalence_Reflexive := fun w => tup0_eq_refl _ (projT2 w)
        ; Equivalence_Symmetric := fun w v =>
            tup0_eq_sym _ _ (projT2 w) (projT2 v)
        ; Equivalence_Transitive := fun w v u =>
            tup0_eq_trans _ _ _ (projT2 w) (projT2 v) (projT2 u) |} |}.

Definition Tup0SumObj@{o} (X : SetoidObject@{o o}) : SetoidObject@{o o} :=
  {| carrier := Tup0Sum@{o} X ; is_setoid := Tup0Sum_Setoid@{o} X |}.

Definition list_to_tup0sum@{o} {X : SetoidObject@{o o}} (l : list X) :
  Tup0Sum@{o} X :=
  existT (fun n => Tup0 X n) (length l) (list_to_tup0 l).

Definition tup0sum_to_list@{o} {X : SetoidObject@{o o}} (w : Tup0Sum@{o} X) :
  list X :=
  tup0_to_list (projT1 w) (projT2 w).

Lemma list_to_tup0sum_respects@{o} {X : SetoidObject@{o o}} (l l' : list X) :
  word_eq l l' →
  tup0_eq (length l) (length l') (list_to_tup0 l) (list_to_tup0 l').
Proof.
  intro H; destruct H as [|a b u v Hab Huv]; [ exact Logic.I | ].
  exact (list_to_tup_respects a b u v Hab Huv).
Qed.

Lemma tup0sum_to_list_respects@{o} {X : SetoidObject@{o o}} (n m : nat)
  (t : Tup0@{o} X n) (u : Tup0@{o} X m) :
  tup0_eq n m t u → word_eq (tup0_to_list n t) (tup0_to_list m u).
Proof.
  destruct n, m; simpl; try contradiction; [ intros _; exact we_nil | ].
  apply tup_to_list_respects.
Qed.

Lemma tup0sum_list_tup0sum@{o} {X : SetoidObject@{o o}}
  (w : Tup0Sum@{o} X) :
  tup0_eq _ _ (list_to_tup0 (tup0sum_to_list w)) (projT2 w).
Proof.
  destruct w as [[|n] t]; [ exact Logic.I | ].
  unfold tup0sum_to_list; simpl.
  pose proof (list_to_tup_tup_to_list n t) as K.
  destruct (tup_to_list n t) as [|a l]; [ contradiction | exact K ].
Qed.

(* The literal words of length 0, 1 and 2. / 长度为0、1和2的字面词。 *)
Definition word0@{o} {A : Type@{o}} : list A := Datatypes.nil.

Definition word1@{o} {A : Type@{o}} (a : A) : list A :=
  Datatypes.cons a Datatypes.nil.

Definition word2@{o} {A : Type@{o}} (a b : A) : list A :=
  Datatypes.cons a (Datatypes.cons b Datatypes.nil).

Lemma word_eq_wapp_nil_r@{o} {X : SetoidObject@{o o}} (l : list X) :
  word_eq (wapp l Datatypes.nil) l.
Proof. rewrite wapp_nil_r. apply word_eq_refl. Qed.

(* ------------------------------------------------------------------------ *)
(* * ** W₀, the monad of the adjunction Set ⇀ Mon / * ** W₀，集合到单元范畴伴随函子的幺半群 *)

Section W0Monad.

Universes o so.

Local Notation MonOS :=
  (@Mon@{so o so so} Sets@{o so} Sets_Product_Monoidal@{so o}).
Local Notation UMonOS :=
  (@Mon_Forget@{so o so so} Sets@{o so} Sets_Product_Monoidal@{so o}).

Definition W0F@{+} : Sets@{o so} ⟶ Sets@{o so} := UMonOS ◯ FreeMonSets.

Definition W0@{+} : @Monad Sets@{o so} W0F :=
  Adjunction_Induced_Monad free_mon_sets_adjunction_hom.

(* μ_X: a word of words, concatenated; the fold of concatenation. / μ_X：一个由词组成的词；连接的折叠。 *)
Definition wconcat@{+} {X : obj[Sets@{o so}]} (ww : list (list X)) :
  list X :=
  free_mon_extend (L := (FreeMonSetsObject X : obj[MonOS])) (fun w => w) ww.

(* W₀ X is the setoid of words over X. / W₀ X 是 X 上的词的等价类。 *)
Example W0_obj@{+} (X : obj[Sets@{o so}]) : fobj[W0F] X = WordObj X
  := eq_refl.

Example W0_carrier@{+} (X : obj[Sets@{o so}]) :
  @eq Type@{o} (carrier (fobj[W0F] X)) (list X) := eq_refl.

(* η_X is the insertion of one-letter words, as a setoid map. / η_X 是一个字母词的插入，作为一个集合映射。 *)
Example W0_ret@{+} (X : obj[Sets@{o so}]) :
  @ret _ _ W0 X = free_mon_insert X := eq_refl.

Example W0_ret_fun@{+} (X : obj[Sets@{o so}]) (a : X) :
  @ret _ _ W0 X a = word1 a := eq_refl.

(* μ = U ε F. *)
Example W0_join_counit@{+} (X : obj[Sets@{o so}]) :
  @join _ _ W0 X
    = fmap[UMonOS]
        (@counit _ _ _ _ free_mon_sets_adjunction_hom (FreeMonSets X))
  := eq_refl.

(* μ concatenates. / μ 连接。 *)
Example W0_join_fun@{+} (X : obj[Sets@{o so}]) (ww : list (list X)) :
  @join _ _ W0 X ww = wconcat ww := eq_refl.

Example W0_join_literal@{+} (X : obj[Sets@{o so}]) (a b c : X) :
  @join _ _ W0 X (word2 (word2 a b) (word1 c))
    = Datatypes.cons a (word2 b c) := eq_refl.

Example W0_join_nil@{+} (X : obj[Sets@{o so}]) :
  @join _ _ W0 X word0 = word0 := eq_refl.

(* W₀ f acts letterwise, up to ≈. / W₀ f 作用于字母逐个，直到 ≈。 *)
Lemma W0_map@{+} {X Y : obj[Sets@{o so}]} (f : X ~{Sets@{o so}}~> Y)
  (l : list X) : fmap[W0F] f l ≈ wmap f l.
Proof. exact (free_mon_fmap_is_wmap f l). Qed.

(* W₀ X ≅ ∐_{n≥0} Xⁿ. *)
Definition W0_sum_iso@{+} (X : obj[Sets@{o so}]) :
  @Isomorphism Sets@{o so} (fobj[W0F] X) (Tup0SumObj X).
Proof.
  unshelve refine
    (@Build_Isomorphism Sets@{o so} (fobj[W0F] X) (Tup0SumObj X)
       {| morphism := @list_to_tup0sum X |}
       {| morphism := @tup0sum_to_list X |} _ _).
  - intros l l' H. exact (list_to_tup0sum_respects l l' H).
  - intros w v H. exact (tup0sum_to_list_respects _ _ (projT2 w) (projT2 v) H).
  - intro w. exact (tup0sum_list_tup0sum w).
  - intro l. simpl. unfold tup0sum_to_list; simpl.
    rewrite tup0_to_list_list_to_tup0. apply word_eq_refl.
Defined.

(* A word goes to its length and its tuple of letters, and back. / 一个单词取决于它的长度和它的字母元组，然后再返回。 *)
Example W0_sum_iso_to@{+} (X : obj[Sets@{o so}]) (l : list X) :
  to (W0_sum_iso X) l = existT _ (length l) (list_to_tup0 l) := eq_refl.

Example W0_sum_iso_from@{+} (X : obj[Sets@{o so}]) (n : nat)
  (t : Tup0@{o} X n) :
  from (W0_sum_iso X) (existT _ n t) = tup0_to_list n t := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** An algebra is a monoid (Awodey, Exercise 10.6.6) / * ** 一个代数是一个幺半群（Awodey，练习10.6.6） *)

Lemma alg_unit@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) (a : S) :
  t_alg[α] (word1 a) ≈ a.
Proof. exact (@t_id _ _ _ _ α a). Qed.

(* The action law read on lists: h (map h ww) ≈ h (concat ww). / 作用律在列表上读作：h (map h ww) ≈ h (concat ww)。 *)
Lemma alg_action@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) (ww : list (list S)) :
  t_alg[α] (wmap (t_alg[α]) ww) ≈ t_alg[α] (wconcat ww).
Proof.
  transitivity (t_alg[α] (fmap[W0F] (t_alg[α]) ww)).
  - apply (proper_morphism (t_alg[α])). symmetry.
    exact (@W0_map (fobj[W0F] S) S (t_alg[α]) ww).
  - exact (@t_action _ _ _ _ α ww).
Qed.

(* The multiplication x · y = α⟨x y⟩ and the unit α⟨⟩. / 乘法 x · y = α⟨x y⟩ 和单位 α⟨⟩。 *)
Definition alg_mul@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) (a b : S) : S :=
  t_alg[α] (word2 a b).

Definition alg_one@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) : S :=
  t_alg[α] word0.

Lemma alg_mul_respects@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) :
  Proper (equiv ==> equiv ==> equiv) (alg_mul α).
Proof.
  intros a a' Ha b b' Hb. unfold alg_mul.
  apply (proper_morphism (t_alg[α])).
  exact (we_cons _ _ _ _ Ha (we_cons _ _ _ _ Hb we_nil)).
Qed.

(* The laws, from the unit law and the action law at a word of words. / 法律，从单位法和行动法在一句话中的每个词。 *)
Lemma alg_mul_assoc@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) (a b c : S) :
  alg_mul α (alg_mul α a b) c ≈ alg_mul α a (alg_mul α b c).
Proof.
  unfold alg_mul.
  transitivity (t_alg[α] (word2 (t_alg[α] (word2 a b))
                            (t_alg[α] (word1 c)))).
  { apply (proper_morphism (t_alg[α])).
    refine (we_cons _ _ _ _ (reflexivity _) (we_cons _ _ _ _ _ we_nil)).
    symmetry. apply alg_unit. }
  transitivity (t_alg[α] (wconcat (word2 (word2 a b) (word1 c)))).
  { exact (alg_action α (word2 (word2 a b) (word1 c))). }
  transitivity (t_alg[α] (wconcat (word2 (word1 a) (word2 b c)))).
  { reflexivity. }
  transitivity (t_alg[α] (word2 (t_alg[α] (word1 a))
                            (t_alg[α] (word2 b c)))).
  { symmetry. exact (alg_action α (word2 (word1 a) (word2 b c))). }
  apply (proper_morphism (t_alg[α])).
  refine (we_cons _ _ _ _ _ (we_cons _ _ _ _ (reflexivity _) we_nil)).
  apply alg_unit.
Qed.

Lemma alg_one_l@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) (a : S) :
  alg_mul α (alg_one α) a ≈ a.
Proof.
  unfold alg_mul, alg_one.
  transitivity (t_alg[α] (word2 (t_alg[α] word0) (t_alg[α] (word1 a)))).
  { apply (proper_morphism (t_alg[α])).
    refine (we_cons _ _ _ _ (reflexivity _) (we_cons _ _ _ _ _ we_nil)).
    symmetry. apply alg_unit. }
  transitivity (t_alg[α] (wconcat (word2 word0 (word1 a)))).
  { exact (alg_action α (word2 word0 (word1 a))). }
  apply alg_unit.
Qed.

Lemma alg_one_r@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) (a : S) :
  alg_mul α a (alg_one α) ≈ a.
Proof.
  unfold alg_mul, alg_one.
  transitivity (t_alg[α] (word2 (t_alg[α] (word1 a)) (t_alg[α] word0))).
  { apply (proper_morphism (t_alg[α])).
    refine (we_cons _ _ _ _ _ (we_cons _ _ _ _ (reflexivity _) we_nil)).
    symmetry. apply alg_unit. }
  transitivity (t_alg[α] (wconcat (word2 (word1 a) word0))).
  { exact (alg_action α (word2 (word1 a) word0)). }
  apply alg_unit.
Qed.

(* The monoid of the algebra. / 代数的幺半群。 *)
Definition alg_monoid@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) : MonOS :=
  mk_mon_obj S (alg_one α) (alg_mul α) (alg_mul_respects α)
    (alg_mul_assoc α) (alg_one_l α) (alg_one_r α).

(* The algebra comes from its monoid: α⟨m1 … mn⟩ ≈ m1 ⋯ mn. / 代数来自它的幺半群：α⟨m1 … mn⟩ ≈ m1 ⋯ mn。 *)
Lemma alg_fold@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) (l : list S) :
  free_mon_extend (L := alg_monoid α) (fun x => x) l ≈ t_alg[α] l.
Proof.
  induction l as [|a l IH]; simpl; [ reflexivity | ].
  change (alg_mul α a (free_mon_extend (L := alg_monoid α) (fun x => x) l)
            ≈ t_alg[α] (Datatypes.cons a l)).
  unfold alg_mul.
  transitivity (t_alg[α] (word2 (t_alg[α] (word1 a)) (t_alg[α] l))).
  { apply (proper_morphism (t_alg[α])).
    refine (we_cons _ _ _ _ _ (we_cons _ _ _ _ IH we_nil)).
    symmetry. apply alg_unit. }
  transitivity (t_alg[α] (wconcat (word2 (word1 a) l))).
  { exact (alg_action α (word2 (word1 a) l)). }
  apply (proper_morphism (t_alg[α])).
  exact (we_cons _ _ _ _ (reflexivity a) (word_eq_wapp_nil_r l)).
Qed.

(*
 ...and from no other: a monoid on the same carrier whose products the
 algebra computes has the algebra's multiplication and unit. 

 --------
 ...而不是其他任何东西：在相同载体上的一个幺半群，其代数计算的乘积具有代数的乘法和单位元。
*)
Lemma alg_monoid_unique@{+} (M : MonOS)
  (α : @TAlgebra Sets@{o so} W0F W0 (mon_ob M))
  (H : ∀ l, t_alg[α] l ≈ free_mon_extend (L := M) (fun x => x) l) :
  (∀ a b, mon_mul M a b ≈ alg_mul α a b) * (mon_one M ≈ alg_one α).
Proof.
  split.
  - intros a b. unfold alg_mul. rewrite (H (word2 a b)). simpl.
    apply (mon_mul_resp M); [ reflexivity | ].
    symmetry. apply mon_one_r.
  - unfold alg_one. rewrite (H word0). reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** The Eilenberg–Moore category of W₀ is Mon / * ** W₀ 的 Eilenberg–Moore 范畴是 Mon *)

Definition W0Alg@{+} : Category@{so o o} :=
  @EilenbergMoore@{so so so o} Sets@{o so} W0F W0.

Definition EM_mon_map@{+} {x y : W0Alg} (f : x ~{W0Alg}~> y) :
  alg_monoid (projT2 x) ~{MonOS}~> alg_monoid (projT2 y).
Proof.
  refine (@mk_mon_hom (alg_monoid (projT2 x)) (alg_monoid (projT2 y))
            (t_alg_hom[f]) (proper_morphism (t_alg_hom[f])) _ _).
  - intros a b.
    transitivity (t_alg[projT2 y] (fmap[W0F] (t_alg_hom[f]) (word2 a b))).
    + exact (@t_alg_hom_commutes _ _ _ _ _ _ _ f (word2 a b)).
    + apply (proper_morphism (t_alg[projT2 y])).
      exact (W0_map (t_alg_hom[f]) (word2 a b)).
  - transitivity (t_alg[projT2 y] (fmap[W0F] (t_alg_hom[f]) word0)).
    + exact (@t_alg_hom_commutes _ _ _ _ _ _ _ f word0).
    + apply (proper_morphism (t_alg[projT2 y])).
      exact (W0_map (t_alg_hom[f]) word0).
Defined.

Definition EM_to_Mon@{+} : W0Alg ⟶ MonOS.
Proof.
  unshelve refine
    (@Build_Functor W0Alg MonOS (fun x => alg_monoid (projT2 x))
       (fun x y f => EM_mon_map f) _ _ _).
  - intros x y f g H. exact H.
  - intros x a. reflexivity.
  - intros x y z f g a. reflexivity.
Defined.

(* The comparison functor K : Mon → Set^{W₀}. / 比较函子 K : Mon → Set^{W₀}。 *)
Definition Mon_K@{+} : MonOS ⟶ W0Alg :=
  EM_Comparison free_mon_sets_adjunction_hom.

(* The algebra round trip, with the identity as its component. / 代数往返，以恒等式作为其组成部分。 *)
Definition Mon_EM_counit_iso@{+} (x : W0Alg) :
  @Isomorphism W0Alg (fobj[Mon_K ◯ EM_to_Mon] x) x.
Proof.
  unshelve refine
    (@Build_Isomorphism W0Alg (fobj[Mon_K ◯ EM_to_Mon] x) x
       (@Build_TAlgebraHom Sets@{o so} W0F W0 (projT1 x) (projT1 x)
          (projT2 (fobj[Mon_K ◯ EM_to_Mon] x)) (projT2 x)
          (@setoid_morphism_id@{o o o} (projT1 x)) _)
       (@Build_TAlgebraHom Sets@{o so} W0F W0 (projT1 x) (projT1 x)
          (projT2 x) (projT2 (fobj[Mon_K ◯ EM_to_Mon] x))
          (@setoid_morphism_id@{o o o} (projT1 x)) _) _ _).
  - intro l. simpl.
    transitivity (t_alg[projT2 x] l); [ exact (alg_fold (projT2 x) l) | ].
    apply (proper_morphism (t_alg[projT2 x])).
    symmetry. exact (@fmap_id _ _ W0F (projT1 x) l).
  - intro l. simpl.
    transitivity (t_alg[projT2 x] (fmap[W0F] id l)).
    + apply (proper_morphism (t_alg[projT2 x])).
      symmetry. exact (@fmap_id _ _ W0F (projT1 x) l).
    + symmetry. exact (alg_fold (projT2 x) _).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(*
 The monoid round trip, with the identity as its component: the
 multiplication comes back as x · (y · 1). 

 --------
 幺半群的往返，以单位元作为其组成部分：乘法表现为 x · (y · 1)。
*)
Definition Mon_EM_unit_iso@{+} (M : MonOS) :
  @Isomorphism MonOS (fobj[EM_to_Mon ◯ Mon_K] M) M.
Proof.
  unshelve refine
    (@Build_Isomorphism MonOS (fobj[EM_to_Mon ◯ Mon_K] M) M
       (@mk_mon_hom (fobj[EM_to_Mon ◯ Mon_K] M) M (fun a => a)
          (fun a b H => H) _ _)
       (@mk_mon_hom M (fobj[EM_to_Mon ◯ Mon_K] M) (fun a => a)
          (fun a b H => H) _ _) _ _).
  - intros a b. simpl.
    apply (mon_mul_resp M); [ reflexivity | apply mon_one_r ].
  - simpl. reflexivity.
  - intros a b. simpl. symmetry.
    apply (mon_mul_resp M); [ reflexivity | apply mon_one_r ].
  - simpl. reflexivity.
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(*
 Awodey Example 10.7 and Riehl Example 5.2.6(iii): K is an equivalence,
 with identity components both ways. 

 --------
 Awodey 示例 10.7 和 Riehl 示例 5.2.6(iii)：K 是一个等价，且双向的单位分量。
*)
Definition Mon_EM_equivalence@{+} :
  @EquivalenceOfCategories@{so so so so so o} MonOS W0Alg Mon_K.
Proof.
  unshelve refine
    (@Build_EquivalenceOfCategories _ _ Mon_K EM_to_Mon _ _).
  - exists (fun x => Mon_EM_counit_iso x).
    intros x y f a. reflexivity.
  - exists (fun M => iso_sym (Mon_EM_unit_iso M)).
    intros M N f a. reflexivity.
Defined.

(* Monoids are monadic over Set. / 幺半群在集合上是幺模的。 *)
Definition Mon_Forget_Monadic@{+} :
  @Monadic@{so so so so so o so so} MonOS Sets@{o so} UMonOS.
Proof.
  exists FreeMonSets.
  exists free_mon_sets_adjunction_hom.
  exact Mon_EM_equivalence.
Defined.

(* Mon ≅ Set^{W₀} in Cat, from the two component isomorphisms. / 在 Cat 中，Mon ≅ Set^{W₀}，来自两个组成同构。 *)
Definition Mon_EM_iso@{c +} : @Isomorphism Cat@{c so so so o} MonOS W0Alg.
Proof.
  unshelve refine
    (@Build_Isomorphism Cat@{c so so so o} MonOS W0Alg Mon_K EM_to_Mon _ _).
  - exists (fun x => Mon_EM_counit_iso x).
    intros x y f a. reflexivity.
  - exists (fun M => Mon_EM_unit_iso M).
    intros M N f a. reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(* * ** Commuting with the forgetful functors (Awodey §10.3) / * ** 与遗忘函子交换 (Awodey §10.3) *)

Definition W0_Forget@{+} : W0Alg ⟶ Sets@{o so} :=
  @EM_Forget Sets@{o so} W0F W0.

Theorem Mon_K_Forget@{+} : W0_Forget ◯ Mon_K ≈ UMonOS.
Proof. exact (EM_Comparison_Forget free_mon_sets_adjunction_hom). Qed.

Theorem EM_to_Mon_Forget@{+} : UMonOS ◯ EM_to_Mon ≈ W0_Forget.
Proof.
  exists (fun x => iso_id).
  intros x y f a. reflexivity.
Qed.

Example Mon_K_Forget_obj@{+} (M : MonOS) :
  fobj[W0_Forget] (fobj[Mon_K] M) = fobj[UMonOS] M := eq_refl.

Example Mon_K_Forget_map@{+} {M N : MonOS} (f : M ~{MonOS}~> N) :
  fmap[W0_Forget] (fmap[Mon_K] f) = fmap[UMonOS] f := eq_refl.

Example EM_to_Mon_Forget_obj@{+} (x : W0Alg) :
  fobj[UMonOS] (fobj[EM_to_Mon] x) = fobj[W0_Forget] x := eq_refl.

Example EM_to_Mon_Forget_map@{+} {x y : W0Alg} (f : x ~{W0Alg}~> y) :
  fmap[UMonOS] (fmap[EM_to_Mon] f) = fmap[W0_Forget] f := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** The Kleisli category of W₀ (Riehl, Example 5.2.11(ii)) / * ** W₀ 的 Kleisli 范畴（Riehl，例 5.2.11(ii)） *)

Definition W0Kl@{+} : Category@{so o o} := @Kleisli Sets@{o so} W0F W0.

(* A Kleisli arrow A ⇝ B is a setoid map A → W₀ B. / Kleisli 箭头 A ⇝ B 是一个集合等价映射 A → W₀ B。 *)
Example W0Kl_hom@{+} (A B : obj[Sets@{o so}]) :
  @eq Type@{o} (@hom W0Kl A B) (A ~{Sets@{o so}}~> fobj[W0F] B) := eq_refl.

Example W0Kl_homset@{+} (A B : obj[Sets@{o so}]) :
  @homset W0Kl A B = @homset Sets@{o so} A (fobj[W0F] B) := eq_refl.

Example W0Kl_id_fun@{+} (A : obj[Sets@{o so}]) (a : A) :
  (@id W0Kl A) a = word1 a := eq_refl.

(* Composition is concatenated mapping, up to ≈. / 复合是连接映射，最多≈。 *)
Lemma W0Kl_compose@{+} {A B C : obj[Sets@{o so}]}
  (g : B ~{W0Kl}~> C) (f : A ~{W0Kl}~> B) (a : A) :
  (g ∘[W0Kl] f) a ≈ wconcat (wmap g (f a)).
Proof.
  apply (proper_morphism (@join _ _ W0 C)). exact (W0_map g (f a)).
Qed.

(* A Kleisli arrow A ⇝ B is a setoid map A → ∐_{n≥0} Bⁿ. / Kleisli 箭头 A ⇝ B 是一个集合态射 A → ∐_{n≥0} Bⁿ。 *)
Definition W0Kl_hom_iso@{+} (A B : obj[Sets@{o so}]) :
  @Isomorphism Sets@{o so}
    {| carrier := @hom W0Kl A B; is_setoid := @homset W0Kl A B |}
    {| carrier := A ~{Sets@{o so}}~> Tup0SumObj B
     ; is_setoid := @homset Sets@{o so} A (Tup0SumObj B) |}.
Proof.
  unshelve refine
    (@Build_Isomorphism Sets@{o so}
       {| carrier := @hom W0Kl A B; is_setoid := @homset W0Kl A B |}
       {| carrier := A ~{Sets@{o so}}~> Tup0SumObj B
        ; is_setoid := @homset Sets@{o so} A (Tup0SumObj B) |}
       {| morphism := fun f => to (W0_sum_iso B) ∘ f |}
       {| morphism := fun g => from (W0_sum_iso B) ∘ g |} _ _).
  - intros f f' H a. exact (proper_morphism (to (W0_sum_iso B)) _ _ (H a)).
  - intros g g' H a. exact (proper_morphism (from (W0_sum_iso B)) _ _ (H a)).
  - intros g a. exact (iso_to_from (W0_sum_iso B) (g a)).
  - intros f a. exact (iso_from_to (W0_sum_iso B) (f a)).
Defined.

Example W0Kl_hom_iso_to@{+} (A B : obj[Sets@{o so}]) (f : A ~{W0Kl}~> B)
  (a : A) :
  to (W0Kl_hom_iso A B) f a = existT _ (length (f a)) (list_to_tup0 (f a))
  := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Readbacks / ** 回读 *)

(* The two legs of the isomorphism in Cat are the two functors. / Cat 中同构的两条腿是两个函子。 *)
Example Mon_EM_iso_to@{+} : to Mon_EM_iso = Mon_K := eq_refl.

Example Mon_EM_iso_from@{+} : from Mon_EM_iso = EM_to_Mon := eq_refl.

(* The monoid of an algebra: its carrier, x · y = α⟨x y⟩ and 1 = α⟨⟩. / 一个代数的幺半群：它的载体，x · y = α⟨x y⟩ 且 1 = α⟨⟩。 *)
Example alg_monoid_carrier@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) : mon_ob (alg_monoid α) = S
  := eq_refl.

Example alg_monoid_mul@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) (a b : S) :
  mon_mul (alg_monoid α) a b = t_alg[α] (word2 a b) := eq_refl.

Example alg_monoid_one@{+} {S : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 S) :
  mon_one (alg_monoid α) = t_alg[α] word0 := eq_refl.

(*
 K M is ⟨M, U ε_M⟩: the structure map is the fold of the identity, ν₀ the
 unit, and νₙ the n-fold product, bracketed to the right with the unit
 last. 

 --------
 K M 是 ⟨M, U ε_M⟩：结构映射是恒等映射的折叠，ν₀ 是单位，νₙ 是 n 重积，右括号与单位在最后。
*)
Example Mon_K_carrier@{+} (M : MonOS) :
  projT1 (fobj[Mon_K] M) = mon_ob M := eq_refl.

Example Mon_K_alg@{+} (M : MonOS) :
  t_alg[projT2 (fobj[Mon_K] M)]
    = fmap[UMonOS] (@counit _ _ _ _ free_mon_sets_adjunction_hom M)
  := eq_refl.

Example Mon_K_alg_fun@{+} (M : MonOS) (l : list (mon_ob M)) :
  t_alg[projT2 (fobj[Mon_K] M)] l = free_mon_extend (fun x => x) l
  := eq_refl.

Example Mon_K_nu0@{+} (M : MonOS) :
  t_alg[projT2 (fobj[Mon_K] M)] word0 = mon_one M := eq_refl.

Example Mon_K_nu1@{+} (M : MonOS) (x : mon_ob M) :
  t_alg[projT2 (fobj[Mon_K] M)] (word1 x) = mon_mul M x (mon_one M)
  := eq_refl.

Example Mon_K_nu2@{+} (M : MonOS) (x y : mon_ob M) :
  t_alg[projT2 (fobj[Mon_K] M)] (word2 x y)
    = mon_mul M x (mon_mul M y (mon_one M)) := eq_refl.

Example Mon_K_map@{+} {M N : MonOS} (f : M ~{MonOS}~> N) :
  t_alg_hom[fmap[Mon_K] f] = `1 f := eq_refl.

(* The monoid of an algebra, through the functor. / 通过函子，代数的幺半群。 *)
Example EM_to_Mon_carrier@{+} (x : W0Alg) :
  mon_ob (fobj[EM_to_Mon] x) = projT1 x := eq_refl.

Example EM_to_Mon_mul@{+} (x : W0Alg) (a b : projT1 x) :
  mon_mul (fobj[EM_to_Mon] x) a b = t_alg[projT2 x] (word2 a b) := eq_refl.

Example EM_to_Mon_one@{+} (x : W0Alg) :
  mon_one (fobj[EM_to_Mon] x) = t_alg[projT2 x] word0 := eq_refl.

Example EM_to_Mon_map@{+} {x y : W0Alg} (f : x ~{W0Alg}~> y) :
  `1 (fmap[EM_to_Mon] f) = t_alg_hom[f] := eq_refl.

(* The round trips: the carrier, the unit and the maps come back on the nose, the multiplication as x · (y · 1), so at ≈. / 往返：运载工具、单位和地图准确回来，乘法为 x · (y · 1)，所以在 ≈。 *)
Example Mon_rt_carrier@{+} (M : MonOS) :
  mon_ob (fobj[EM_to_Mon ◯ Mon_K] M) = mon_ob M := eq_refl.

Example Mon_rt_one@{+} (M : MonOS) :
  mon_one (fobj[EM_to_Mon ◯ Mon_K] M) = mon_one M := eq_refl.

Example Mon_rt_mul_fun@{+} (M : MonOS) (a b : mon_ob M) :
  mon_mul (fobj[EM_to_Mon ◯ Mon_K] M) a b
    = mon_mul M a (mon_mul M b (mon_one M)) := eq_refl.

Lemma Mon_rt_mul@{+} (M : MonOS) (a b : mon_ob M) :
  mon_mul (fobj[EM_to_Mon ◯ Mon_K] M) a b ≈ mon_mul M a b.
Proof. exact (mon_mul_resp M _ _ (reflexivity a) _ _ (mon_one_r M b)). Qed.

Example Mon_rt_hom@{+} {M N : MonOS} (f : M ~{MonOS}~> N) :
  mon_fun (fmap[EM_to_Mon ◯ Mon_K] f) = mon_fun f := eq_refl.

Example EM_rt_carrier@{+} (x : W0Alg) :
  projT1 (fobj[Mon_K ◯ EM_to_Mon] x) = projT1 x := eq_refl.

Example EM_rt_alg_fun@{+} (x : W0Alg) (l : list (projT1 x)) :
  t_alg[projT2 (fobj[Mon_K ◯ EM_to_Mon] x)] l
    = free_mon_extend (L := alg_monoid (projT2 x)) (fun s => s) l
  := eq_refl.

Example EM_rt_alg_hom@{+} {x y : W0Alg} (f : x ~{W0Alg}~> y) :
  t_alg_hom[fmap[Mon_K ◯ EM_to_Mon] f] = t_alg_hom[f] := eq_refl.

(*
 Every component of the two natural isomorphisms is the identity, at a
 variable object, to and from. 

 --------
 这两个自然同构的每个分量都是在一个变量对象上的恒等映射，来回都是如此。
*)
Example Mon_EM_iso_to_from_component@{+} (x : W0Alg) :
  (t_alg_hom[to (projT1 (iso_to_from Mon_EM_iso) x)],
   t_alg_hom[from (projT1 (iso_to_from Mon_EM_iso) x)])
    = (@setoid_morphism_id@{o o o} (projT1 x),
       @setoid_morphism_id@{o o o} (projT1 x)) := eq_refl.

Example Mon_EM_iso_from_to_component@{+} (M : MonOS) :
  (mon_fun (to (projT1 (iso_from_to Mon_EM_iso) M)),
   mon_fun (from (projT1 (iso_from_to Mon_EM_iso) M)))
    = ((fun a : mon_ob M => a), (fun a : mon_ob M => a)) := eq_refl.

Example Mon_EM_counit_component@{+} (x : W0Alg) :
  (t_alg_hom[to (projT1 (@equivalence_counit _ _ _ Mon_EM_equivalence) x)],
   t_alg_hom[from (projT1 (@equivalence_counit _ _ _
                             Mon_EM_equivalence) x)])
    = (@setoid_morphism_id@{o o o} (projT1 x),
       @setoid_morphism_id@{o o o} (projT1 x)) := eq_refl.

Example Mon_EM_unit_component@{+} (M : MonOS) :
  (mon_fun (to (projT1 (@equivalence_unit _ _ _ Mon_EM_equivalence) M)),
   mon_fun (from (projT1 (@equivalence_unit _ _ _ Mon_EM_equivalence) M)))
    = ((fun a : mon_ob M => a), (fun a : mon_ob M => a)) := eq_refl.

End W0Monad.
