Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Free.

Generalizable All Variables.

(* * * The tensor-algebra monad T on Ab, and rings as its algebras / * * Ab 上的张量代数单子 T，以及作为其代数的环 *)

(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Springer GTM 5, 1998, §VI.4, Exercise 4, printed p. 146 (PDF
 p. 155) — maclane:VI.4:ex4
 Book: Riehl, "Category Theory in Context", Example 5.5.7(ii), printed
 p. 205 (PDF p. 225) — riehl:5.5:example7
 nLab: https://ncatlab.org/nlab/show/tensor+algebra
 nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad
 nLab: https://ncatlab.org/nlab/show/monadic+functor

 WHAT THE BOOKS SAY, read from the page image and the PDF.  Mac Lane,
 Exercise 4: "The adjunction ⟨F, G, φ⟩ : Ab ⇀ Rng with G the functor
 "forget the multiplication in a ring" defines a monad T in Ab.  (a)
 Give a direct description of this monad, like that in the text for W,
 with Xⁿ replaced by the n-fold tensor power and coproduct ∐ by the
 (infinite) direct sum of abelian groups.  (b) Give the corresponding
 description of T-algebras and show that the comparison functor from
 rings to T-algebras is an isomorphism."  Riehl, Example 5.5.7(ii):
 "The proof of Corollary 5.5.3 can be adapted to show that the
 forgetful functor U : Ring → Ab is monadic.  The induced monad on Ab is
 the free monoid monad TA := ⨁_{n≥0} A^{⊗n}."  Mac Lane's Rng is the
 rings with identity, Instance/Rng.v's [Rng].  This file is T and part
 (b) through the rings; part (a) is Instance/Ab/TensorPower.v with
 Instance/Rng/FreeMonad/Words.v, and the corresponding description of
 the algebras, Mac Lane's systems ⟨A, ν₀, ν₁, …⟩, is
 Instance/Rng/FreeMonad/System.v.

 THE MONAD.  [TF] is U ◯ F with F Instance/Rng/Free.v's [FreeRngAb]
 (#400, PR #1219) and U [Rng_Forget_Ab]; [TM] is Monad/Comparison.v's
 transparent [Adjunction_Induced_Monad] of Free.v's
 [free_rng_ab_adjunction_hom], the hom-set form of the same adjunction
 that #474 adds to Free.v (same left adjoint and insertion; its unit
 and forward transpose are those of [free_rng_ab_adjunction] at
 [eq_refl]), whose counit is the evaluation of the identity by
 conversion where the universal-arrow form's is not (Free.v's header,
 CORRECTION (#474)).  The hom-set form is not only the way around that
 opacity: it is the book's own presentation, Mac Lane's ⟨F, G, φ⟩
 being an adjunction given by its natural bijection φ (§IV.1), and
 [free_rng_ab_adjunction_hom] is [Build_Adjunction'] applied to exactly
 that φ, Free.v's [free_rng_ab_hom_iso].  No second free ring and no
 second free functor.
 At [eq_refl]: T A is the abelian group of the free ring ([T_obj]), its
 carrier the formal ring expressions [FRTerm A] ([T_carrier]) and its ≈
 [fr_eq] ([T_equiv]); η is the insertion on carriers ([T_ret]),
 a ↦ ⟨a⟩ ([T_ret_fun]); μ = U ε F ([T_join_counit]) evaluates an
 expression of expressions, μ t = fr_eval id t at a variable
 ([T_join_fun]), so it removes the outer brackets: μ⟨t⟩ = t,
 μ(⟨s⟩·⟨t⟩) = s·t, μ(⟨s⟩ + ⟨t⟩) = s + t and μ1 = 1 ([T_join_gen],
 [T_join_mul], [T_join_plus], [T_join_one]).  The monad laws are those
 of the adjunction.  T f relabels the generators at ≈
 ([T_map_relabel]) and is refused at [eq_refl] at a generator and at a
 variable (Test/ProbeFreeRing474.v, R5 and R6): the free functor's
 action on arrows is read through the universal arrows.  η as the whole
 homomorphism record is refused too (R4): it is the composite U id ∘
 insert in Ab, whose proof fields are the composite's.

 ROUTE A, NOT TAKEN.  T as the monad of [free_rng_ab_adjunction]
 itself, the record Free.v already had, costs nothing there and leaves μ
 and the comparison functor's values at ≈: μ at a generator, at a
 variable, at a product and at 1, and the structure map of K R at 1, at
 a product and at a generator are refused at [eq_refl] there (R7 to
 R13; at ≈ they are the controls C19 and C20).  Its cheapest variant,
 turning the two [Qed] layers that block that counit [Defined]
 (Theory/Universal/Arrow.v's [ump_universal_arrows] and Free.v's
 [free_rng_ab_universal]), makes R7 to R13 hold (measured by flipping,
 below), and is not taken here: the first is shared by many
 developments, and issue #1353 tracks it.  Route B, the hom-set form,
 adds six constants to Free.v.

 AN ALGEBRA IS A RING.  For an algebra h : T A → A, [ralg_one α] = h 1
 and [ralg_mul α] a b = h(⟨a⟩·⟨b⟩).  The key lemma [ralg_mul_eval],
 h s ⋆ h t ≈ h(s·t), is one instance of the action law ([ralg_action],
 with T h read as the relabelling); with the unit law ([ralg_unit],
 h⟨a⟩ ≈ a) it gives associativity, both unit laws, both distributive
 laws and both annihilation laws ([ralg_mul_assoc] to
 [ralg_mul_zero_r]), and [ralg_ring α] is the ring on A's own 0, + and
 −, its carrier a set because A's is ([rig_prop] is A's [cmon_prop]).
 h is the evaluation of formal expressions in that ring, "the sum of
 the products", at ≈ ([ralg_fold]).

 Rng ≅ Ab^T (Mac Lane's (b); Riehl's 5.5.7(ii)).  [RngAlg] is Ab^T.
 [Rng_K] is Monad/Comparison.v's [EM_Comparison] of the adjunction:
 K R = ⟨U R, U ε_R⟩, its structure map the evaluation in R ([Rng_K_alg],
 [Rng_K_alg_fun]) with 1 ↦ 1, ⟨a⟩ ↦ a, ⟨a⟩·⟨b⟩ ↦ a·b and ⟨a⟩ + ⟨b⟩ ↦
 a + b ([Rng_K_alg_one], [Rng_K_alg_gen], [Rng_K_alg_mul],
 [Rng_K_alg_plus]), and K f = U f ([Rng_K_map]), all at [eq_refl].
 [EM_to_Rng] sends an algebra to its ring and a map to itself
 ([EM_to_Rng_one], [EM_to_Rng_mul], [EM_to_Rng_add], [EM_to_Rng_map]).
 [Rng_EM_iso : Rng ≅[Cat] RngAlg] has the legs [Rng_K] and [EM_to_Rng]
 ([Rng_EM_iso_to], [Rng_EM_iso_from]) and every component of both
 natural isomorphisms the identity, to and from, at [eq_refl]
 ([Rng_EM_iso_to_from_component], [Rng_EM_iso_from_to_component]).  It
 is built from the two component isomorphisms, as #466, #470 and #471
 build theirs, because through Theory/Equivalence.v's
 [Equivalence_to_Cat_Iso] the component of [iso_from_to] is refused
 (R19) while that of [iso_to_from] holds (C50).  An isomorphism in Cat
 is, by Instance/Cat.v, an equivalence of categories, which the
 identity components bring toward Mac Lane's "isomorphism"; the strict
 identity of the two composites with the identity functors is refused
 (R17, R18).  The ring round trip returns the setoid, 0, +, 1, · and −
 and the maps on the nose ([Rng_rt_setoid] to [Rng_rt_hom]: K R's
 product a·b is the structure map at ⟨a⟩·⟨b⟩, which IS a·b), the whole
 ring being refused (R14) for its law fields alone; the algebra round
 trip keeps the group and the maps ([EM_Rng_rt_carrier],
 [EM_Rng_rt_alg_hom]) and returns the structure map as the evaluation
 in the algebra's ring ([EM_Rng_rt_alg_fun]; at ≈, [ralg_fold]),
 refused at [eq_refl] at a variable (R15) and as the whole algebra
 (R16).  [Rng_EM_equivalence] is the equivalence with the same
 components ([Rng_EM_counit_component], [Rng_EM_unit_component]), and
 [Rng_Forget_Ab_Monadic : Monadic Rng_Forget_Ab] is Riehl's statement,
 in Monad/Comparison.v's sense, by an explicit quasi-inverse; her route
 through Corollary 5.5.3 (Beck) is not reproduced.  [Rng_K_Forget] and
 [EM_to_Rng_Forget] are the commutation with the two forgetful
 functors, the first Monad/Comparison.v's [EM_Comparison_Forget] and
 the second with identity components (both at ≈, read from their
 terms, both [Qed]), at [eq_refl] on objects and on arrows
 ([Rng_K_Forget_obj], [Rng_K_Forget_map], [EM_to_Rng_Forget_obj],
 [EM_to_Rng_Forget_map]).

 THE ISSUE'S PREMISES, dated.  Issue #474 was filed on 2026-07-23.
 Its "no concrete category Ab" and "no Rng" were accurate when filed
 and have been stale since PR #1074 (merged 2026-08-12, [Ab]) and PR
 #1091 (merged 2026-08-14, [Rng]); its dependencies #256, #257 and #310
 were closed on 2026-08-12, 2026-08-14 and 2026-08-18.  "No
 tensor-algebra endofunctor ⨁ₙ A^{⊗n}" held until this change in that
 no such functor was named, though U ◯ F exists since PR #1219 (merged
 2026-08-29); "no Rng → T-Alg comparison" held until this change.
 "Reusing #310's tensor-algebra universal arrow": #310 (PR #1158,
 merged 2026-08-18) delivered the tensor algebra of a module over a
 COMMUTATIVE ring, Instance/Vect/TensorAlgebra.v's [TensorAlg]; the
 universal arrow of Ab ⇀ Rng is #400's (PR #1219), which is what is
 reused.  "Discharge the Monad laws" is supplied by
 [Adjunction_Induced_Monad].  Of the suggested module
 Monad/Instance/TensorAlgebra.v, the directory Monad/Instance does not
 exist; the files are this one, its two satellites and
 Instance/Ab/TensorPower.v.  Its "CLAUDE.md Key Files index" was
 accurate when filed and has been stale since PR #1284 (merged
 2026-09-09), which moved the index to docs/INDEX.md.

 STRENGTHS.  Every [Example] holds at [eq_refl], and
 Test/ProbeFreeRing474.v restates each one (C5 to C15, C21 to C44, C46 to
 C49 and C51 to C54).  Stated at ≈: [T_map_relabel], [ralg_fold], the
 ring laws of an algebra, and the inverse laws of the isomorphism in Cat.
 [T_map_relabel] holds at [eq_refl] once both [Qed] layers behind the
 universal arrows are [Defined] (R5, R6 hold in that flipped copy), so it
 is ≈ here and not ≈ only; [ralg_fold] is at ≈ because an algebra's unit
 law h⟨a⟩ ≈ a is.  Seven proofs end [Defined] (counted by token) and
 fifteen [Qed].  Load-bearing transparency, measured by closing each
 [Defined] of #474's code alone [Qed] in a renamed copy of the five files
 and the probe, and naming the first command that then stops:
 [EM_rng_map] ([EM_to_Rng]), [EM_to_Rng] ([Rng_EM_counit_iso]),
 [Rng_EM_counit_iso] and [Rng_EM_unit_iso] ([Rng_EM_equivalence]),
 [Rng_EM_equivalence] ([Rng_EM_counit_component]) and [Rng_EM_iso]
 ([Rng_EM_iso_to]); [Rng_Forget_Ab_Monadic] is [Defined] by the data
 convention only (closed [Qed], nothing stops).  Thirty-seven of the
 thirty-nine [Defined]s of #474's code are load-bearing in this sense
 (each file's header names its own), the other one being
 Instance/Ab/TensorPower.v's [TW_is_tensor_coproduct].  Every
 refutation of the probe is still refused, and every control accepted, in
 a renamed copy with all ninety-three [Qed]s of #474's code turned
 [Defined], so none is the opacity of #474's own proofs.

 UNIVERSES, read off [About] (every name, by script).  Every name is
 universe polymorphic, in the section [TensorAlgebraMonad] over Ab@{u p}
 and Rng@{u p}, and binds u and p first, with p < u and Set < u, the two
 categories' own bounds; no [Set] but those strict lower bounds, no
 equation in any block, and caps of the standard library's global levels
 only.  A closed @{u p} is refused ("Universes … are unbound", measured
 on the bare composite U ◯ F), so each name declares an extensible
 binder.  Fifty-two names bind six levels: u, p and the four [FreeRngAb]
 carries beyond [Ab]'s ([TF], [TM], the readbacks of T, the ring of an
 algebra, [EM_to_Rng] and the round trips), [Rng_EM_iso] binding instead
 u, p, c (u < c and p < c, from Instance/Cat.v's [Cat@{c u u u p}]) and
 three of the four.  Fifteen bind five, u, p and three of the four:
 [Rng_K] and the fourteen names stated through it.  [T_carrier] and
 [T_equiv] bind seven, the extra level being that of the type at which
 their equation is stated, and five readbacks comparing across a
 composite bind a second copy of three of those four, eight or nine
 in all ([EM_Rng_rt_carrier], [EM_Rng_rt_alg_fun], [EM_Rng_rt_alg_hom],
 [Rng_EM_iso_from_to_component], [Rng_EM_unit_component]).  Compiled on
 Coq 8.19.2 and 8.20.1, each of the 296 names #474 adds binds the same
 levels as on Rocq 9.1.1, the same eleven carry the one equation, and
 [Set] appears only as a strict lower bound, compared by [About] on all
 296 in source overlays: unlike #471's free monoid, [FreeRngAb] binds the
 same levels on every version.  No explicit universe instance of a
 constant #474 adds is written anywhere (a scan of the code of every .v
 file of the tree, comments stripped, finds none).

 NOT DELIVERED.  A strict identity of Rng with Ab^T (refused above) and
 an isomorphism in Instance/StrictCat.v (#484 tracks Beck's theorem
 with an isomorphism conclusion).  A computing T f: the action on
 arrows is [FreeRngAb]'s, and a second free functor computing
 letterwise would be a parallel construction, not taken (the direct
 functor ⨁ₙ (−)^{⊗n} of Words.v computes, is naturally isomorphic to
 T, and carries Words.v's direct monad [TWMonad], isomorphic to T as a
 monad, [T_TW_monad_iso]).  Beck's route to monadicity (Riehl's
 Corollary 5.5.3).  The
 relation to #310's [TensorAlg] (Instance/Vect/TensorAlgebra.v, over a
 commutative ring): comparing it with T at ℤ needs Ab ≅ RMod ℤ, issue
 #1356. 

 --------
 书籍：Mac Lane，《为工作数学家准备的范畴论》，第2版，Springer GTM 5, 1998, 第VI.4节，练习4，第146页印刷版（PDF第155页）—— maclane:VI.4:ex4
 书籍：Riehl，《上下文中的范畴论》，示例5.5.7(ii)，第205页印刷版（PDF第225页）—— riehl:5.5:example7
 nLab：https://ncatlab.org/nlab/show/tensor+algebra
 nLab：https://ncatlab.org/nlab/show/algebra+over+a+monad
 nLab：https://ncatlab.org/nlab/show/monadic+functor书中说什么，从页面图片和 PDF 阅读。Mac Lane，练习 4：“伴随 ⟨F, G, φ⟩ : Ab ⇀ Rng，其中 G 是‘忽略环的乘法’的函子，在 Ab 中定义了一个单子 T。(a) 给出该单子的直接描述，就像文中对 W 的描述一样，将 Xⁿ 替换为 n 重张量次幂，并将余积 ∐ 替换为阿贝尔群的（无限）直和。(b) 给出对应的 T-代数描述，并证明从环到 T-代数的比较函子是同构。”  Riehl，例 5.5.7(ii)：“推论 5.5.3 的证明可以被改编以显示忘记函子 U : Ring → Ab 是单子的。在 Ab 上诱导出的单子是自由幺半群单子 TA := ⨁_{n≥0} A^{⊗n}。”  Mac Lane 的 Rng 是有单位元的环，Instance/Rng.v 的 [Rng]。此文件是 T 和部分
 (b) 通过环；部分 (a) 是 Instance/Ab/TensorPower.v 与
 Instance/Rng/FreeMonad/Words.v，以及相应的代数描述，Mac Lane 的系统 ⟨A, ν₀, ν₁, …⟩，是
 Instance/Rng/FreeMonad/System.v。单子。[TF] 是 U ◯ F，并且 F 的实例/Rng/Free.v 的 [FreeRngAb] (#400, PR #1219) 和 U [Rng_Forget_Ab]；[TM] 是 Monad/Comparison.v 的透明 [Adjunction_Induced_Monad]，用于 Free.v 的 [free_rng_ab_adjunction_hom] ，是相同伴随的 Hom 集形式，该伴随被 #474 添加到 Free.v（相同的左伴随和插入；它的单元和前向转置是 [free_rng_ab_adjunction] 在 [eq_refl] 上的形式），其余单位是通过转换对恒等进行评估，其中通用箭头形式不是这样（Free.v 的标题，纠正 (#474)）。Hom 集形式不仅是解决该不透明问题的一种方法：它也是书中自己的呈现方式，Mac Lane 的 ⟨F, G, φ⟩ 是由其自然双射 φ (§IV.1) 给出的伴随，而 [free_rng_ab_adjunction_hom] 是 [Build_Adjunction'] 精确应用于该 φ，Free.v 的 [free_rng_ab_hom_iso]。没有第二个自由环也没有第二个自由函子。在 [eq_refl]：T A 是自由环 ([T_obj]) 的阿贝尔群，其承载体是形式环表达式 [FRTerm A] ([T_carrier])，以及其 ≈ [fr_eq] ([T_equiv])；η 是承载体上的插入 ([T_ret])，a ↦ ⟨a⟩ ([T_ret_fun])；μ = U ε F ([T_join_counit]) 对表达式的表达式进行求值，μ t = fr_eval id t 在变量 ([T_join_fun]) 上，因此它去掉外层括号：μ⟨t⟩ = t，μ(⟨s⟩·⟨t⟩) = s·t，μ(⟨s⟩ + ⟨t⟩) = s + t 且 μ1 = 1 ([T_join_gen], [T_join_mul], [T_join_plus], [T_join_one])。幺半群定律是伴随的定律。T f 在 ≈ ([T_map_relabel]) 上重新标记生成元，并且在 [eq_refl] 上拒绝在生成元和变量上作用 (Test/ProbeFreeRing474.v, R5 和 R6)：自由函子在箭头上的作用通过泛箭头来读取。η 作为整体
 同态记录也被拒绝 (R4)：它是 U id ∘ 在 Ab 中插入的复合，其证明字段是该复合的。路线A，未采取。作为[free_rng_ab_adjunction]本身的单子，记录Free.v已经有，在那里不需要成本，并且保留μ及比较函子的值在≈：μ在生成元、在变量、在积和在1，以及KR的结构映射在1、在积和在生成元在[eq_refl]那里被拒绝（R7到R13；在≈它们是控制C19和C20）。其最便宜的变体，将阻塞该余单元[Defined]的两个[Qed]层（Theory/Universal/Arrow.v的[ump_universal_arrows]和Free.v的[free_rng_ab_universal]）翻转，使R7到R13成立（通过翻转测量），但这里未采取：第一个被许多开发共享，问题#1353跟踪它。路线B，同态集形式，向Free.v添加了六个常量。代数是一个环。对于代数 h : T A → A，[ralg_one α] = h 1 并且 [ralg_mul α] a b = h(⟨a⟩·⟨b⟩)。关键引理 [ralg_mul_eval]，h s ⋆ h t ≈ h(s·t)，是作用律（[ralg_action]，读取 T h 为重标记）的一个例子；结合单位律（[ralg_unit]，h⟨a⟩ ≈ a）它给出了结合律、两个单位律、两个分配律和两个幂零律（[ralg_mul_assoc] 到 [ralg_mul_zero_r]），并且 [ralg_ring α] 是基于 A 自身 0、+ 和 − 的环，其载体是一集合，因为 A 的载体是集合（[rig_prop] 是 A 的 [cmon_prop]）。h 是在该环中对形式表达式进行求值，“乘积的和”，在 ≈ 下（[ralg_fold]）。Rng ≅ Ab^T（Mac Lane 的 (b)；Riehl 的 5.5.7(ii)）。[RngAlg] 是 Ab^T。[Rng_K] 是 Monad/Comparison.v 的 [EM_Comparison]，关于伴随关系：
 K R = ⟨U R, U ε_R⟩，其结构映射是 R 中的评估（[Rng_K_alg]，
 [Rng_K_alg_fun]），1 ↦ 1，⟨a⟩ ↦ a，⟨a⟩·⟨b⟩ ↦ a·b，⟨a⟩ + ⟨b⟩ ↦
 a + b（[Rng_K_alg_one]，[Rng_K_alg_gen]，[Rng_K_alg_mul]，
 [Rng_K_alg_plus]），并且 K f = U f（[Rng_K_map]），全部在 [eq_refl]。
 [EM_to_Rng] 将一个代数映射到它的环，并将一个映射映射到其本身
 （[EM_to_Rng_one]，[EM_to_Rng_mul]，[EM_to_Rng_add]，[EM_to_Rng_map]）。[Rng_EM_iso : Rng ≅[Cat] RngAlg] 有两条腿 [Rng_K] 和 [EM_to_Rng]
 （[Rng_EM_iso_to]，[Rng_EM_iso_from]），两者的每个自然同构的分量都是身份映射，从与到，都在 [eq_refl]
 （[Rng_EM_iso_to_from_component]，[Rng_EM_iso_from_to_component]）。它是由两个组成同构构建的，就像 #466、#470 和 #471 构建它们的同构一样，因为通过 Theory/Equivalence.v 的 [Equivalence_to_Cat_Iso]，[iso_from_to] 的组成部分被拒绝 (R19)，而 [iso_to_from] 的组成部分成立 (C50)。在 Cat 中的一个同构，按照 Instance/Cat.v，是一个范畴的等价，并且身份组成部分将其引向 Mac Lane 的“同构”；与身份函子组合的两个复合的严格身份被拒绝 (R17, R18)。环的往返返回了集合类、0、+、1、· 和 − 以及精确的映射（[Rng_rt_setoid] 到 [Rng_rt_hom]：K R 的乘积 a·b 是结构映射在 ⟨a⟩·⟨b⟩ 上，它就是 a·b），整个环仅因其运算法则域而被拒绝（R14）；代数的往返保持群和映射（[EM_Rng_rt_carrier]，[EM_Rng_rt_alg_hom]）并返回结构映射，作为代数环中的求值（[EM_Rng_rt_alg_fun]；在 ≈ 处，[ralg_fold]），在 [eq_refl] 处在变量上被拒绝（R15）以及作为整个代数（R16）。[Rng_EM_equivalence] 是同一组件的等价（[Rng_EM_counit_component]，[Rng_EM_unit_component]），而 [Rng_Forget_Ab_Monadic : Monadic Rng_Forget_Ab] 是 Riehl 的陈述，在 Monad/Comparison.v 的意义下，通过显式准逆；她通过推论 5.5.3（Beck）的路线没有被复现。[Rng_K_Forget] 和 [EM_to_Rng_Forget] 是与两个遗忘函子交换的，第一个是 Monad/Comparison.v 的 [EM_Comparison_Forget]，第二个是具有恒等分量的（在 ≈ 处，从它们的项中读取，都为 [Qed]），在 [eq_refl] 处作用于对象和箭头（[Rng_K_Forget_obj]、[Rng_K_Forget_map]、[EM_to_Rng_Forget_obj]、[EM_to_Rng_Forget_map]）。问题的前提，已注明日期。第474期问题于2026-07-23提交。当提交时，其“没有具体分类 Ab”和“没有 Rng”是准确的，自从 PR #1074（合并于2026-08-12, [Ab]）和 PR #1091（合并于2026-08-14, [Rng]）之后就已过时；其依赖项 #256、#257 和 #310 分别在2026-08-12、2026-08-14 和 2026-08-18关闭。“没有张量代数自函子 ⨁ₙ A^{⊗n}”一直成立，直到此更改，因为没有这样的函子被命名，尽管 U ◯ F 自 PR #1219（合并于2026-08-29）以来存在；“没有 Rng → T-Alg 的比较”一直成立，直到此更改。“重用 #310 的张量代数通用箭头”：#310（PR #1158，合并于2026-08-18）提供了一个交换环上模的张量代数，即 Instance/Vect/TensorAlgebra.v 中的 [TensorAlg]；Ab ⇀ Rng 的通用箭头是 #400 的（PR #1219），这就是被重用的内容。“Discharge the Monad laws” 由 [Adjunction_Induced_Monad] 提供。在建议的模块 Monad/Instance/TensorAlgebra.v 中，目录 Monad/Instance 并不存在；文件只有这个文件、它的两个附属文件以及 Instance/Ab/TensorPower.v。它的“CLAUDE.md 关键文件索引”在提交时是准确的，自 PR #1284（2026-09-09 合并）之后就已过时，该 PR 将索引移动到了 docs/INDEX.md。优势。每个 [Example] 在 [eq_refl] 上成立，并且 Test/ProbeFreeRing474.v 重新说明了每一个（C5 到 C15，C21 到 C44，C46 到 C49 和 C51 到 C54）。在 ≈ 处说明：[T_map_relabel]、[ralg_fold]，代数的环律，以及 Cat 中同构的逆律。[T_map_relabel] 在 [eq_refl] 处成立，一旦普遍箭头后面的两个 [Qed] 层是 [Defined]（那份翻转副本中 R5、R6 成立），所以这里是 ≈ 而不仅仅是 ≈；[ralg_fold] 在 ≈ 处，因为代数的单位律 h⟨a⟩ ≈ a 成立。七个证明在 [Defined] 结束（按令牌计数），十五个 [Qed]。承重透明性，通过在五个文件的重命名副本中关闭 #474 的代码的每个部分并进行探测来测量，并命名随后停止的第一个命令：[EM_rng_map]（[EM_to_Rng]）、[EM_to_Rng]（[Rng_EM_counit_iso]）、[Rng_EM_counit_iso] 和 [Rng_EM_unit_iso]（[Rng_EM_equivalence]）、[Rng_EM_equivalence]（[Rng_EM_counit_component]）和 [Rng_EM_iso]（[Rng_EM_iso_to]）；[Rng_Forget_Ab_Monadic] 仅按数据约定为 [Defined]（关闭 [Qed]，无任何停止）。在这种意义下，#474 的代码的三十九个 [Defined] 中有三十七个是承重的（每个文件的头部命名其自身），另一个是 Instance/Ab/TensorPower.v 的 [TW_is_tensor_coproduct]。对探针的每一次反驳仍然被拒绝，而每一次控制都被接受，在一个重命名的副本中，#474 的代码中所有九十三个 [Qed] 都被改为 [Defined]，因此没有一个是 #474 自身证明的不透明性。宇宙，读取 [About]（每个名称，按脚本）。每个名称都是宇宙多态的，在 [TensorAlgebraMonad] 部分位于 Ab@{u p} 和 Rng@{u p} 上，并首先绑定 u 和 p，其中 p < u 且 Set < u，为两个类别自身的界限；没有 [Set]，只有那些严格的下界，任何模块中没有方程，并且仅为标准库的全局层级的上限。封闭的 @{u p} 会被拒绝（“宇宙……未绑定”，在裸组合 U ◯ F 上测量），因此每个名称都声明了可扩展的绑定器。五十二个名称绑定六个层级：u、p 和四个 [FreeRngAb]，超出 [Ab] 的（[TF]、[TM]、T 的读回、代数的环、[EM_to_Rng] 和往返），[Rng_EM_iso] 则绑定 u、p、c（u < c 且 p < c，源自 Instance/Cat.v 的 [Cat@{c u u u p}]）以及四个中的三个。十五绑定五、u、p 和四个中的三个：
 [Rng_K] 以及通过它声明的十四个名字。[T_carrier] 和
 [T_equiv] 绑定七，额外的层级是其方程声明时的类型，并且五个回读在复合绑定中比较四个中的三个的第二份副本，总共八个或九个（[EM_Rng_rt_carrier]、[EM_Rng_rt_alg_fun]、[EM_Rng_rt_alg_hom]、
 [Rng_EM_iso_from_to_component]、[Rng_EM_unit_component]）。在 Coq 8.19.2 和 8.20.1 上汇编，每个 296 个名字 #474 添加的绑定与 Rocq 9.1.1 上的层级相同，相同的十一项携带同一个方程，而 [Set] 仅作为严格下界出现，由 [About] 在所有 296 个源覆盖中比较：不同于 #471 的自由幺半群，[FreeRngAb] 在每个版本上绑定相同的层级。没有明确的宇宙实例常量 #474 被写入任何地方（扫描整个树的每个 .v 文件的代码，去掉注释，没有找到）。未交付。Rng 与 Ab^T 的严格同一（上文被拒绝）以及 Instance/StrictCat.v 中的一个同构（#484 跟踪 Beck 定理并含有同构结论）。一个计算 T f：箭头上的作用是 [FreeRngAb] 的，第二个逐字计算的自由函子将是一个平行构造，未采用（Words.v 的直接函子 ⨁ₙ (−)^{⊗n} 可以计算，且自然同构于 T，并携带 Words.v 的直接 monad [TWMonad]，作为 monad 与 T 同构，[T_TW_monad_iso]）。Beck 关于 monadicity 的路线（Riehl 的推论 5.5.3）。与 #310 的 [TensorAlg]（Instance/Vect/TensorAlgebra.v，在交换环上）的关系：将其与 ℤ 上的 T 比较需要 Ab ≅ RMod ℤ，问题 #1356。
*)

Section TensorAlgebraMonad.

Universes u p.

(* ------------------------------------------------------------------------ *)
(* * ** T, the monad of the adjunction Ab ⇀ Rng / * ** T，伴随关系 Ab ⇀ Rng 的幺半群 *)

Definition TF@{+} : Ab@{u p} ⟶ Ab@{u p} := Rng_Forget_Ab ◯ FreeRngAb.

Definition TM@{+} : @Monad Ab@{u p} TF :=
  Adjunction_Induced_Monad free_rng_ab_adjunction_hom.

(* T A is the abelian group of formal ring expressions over A. / T A 是 A 上形式环表达式的阿贝尔群。 *)
Example T_obj@{+} (A : Ab@{u p}) :
  fobj[TF] A = Rng_Forget_Ab (FreeRngAbObject A) := eq_refl.

Example T_carrier@{+} (A : Ab@{u p}) :
  carrier (cmon_setoid (fobj[TF] A)) = FRTerm A := eq_refl.

Example T_equiv@{+} (A : Ab@{u p}) (s t : FRTerm A) :
  @equiv _ (is_setoid (cmon_setoid (fobj[TF] A))) s t = fr_eq s t
  := eq_refl.

(* η_A is the insertion, as a map of carriers: a ↦ ⟨a⟩. / η_A 是插入，作为载体的映射：a ↦ ⟨a⟩。 *)
Example T_ret@{+} (A : Ab@{u p}) :
  cmon_map (@ret _ _ TM A) = cmon_map (free_rng_ab_insert A) := eq_refl.

Example T_ret_fun@{+} (A : Ab@{u p}) (a : carrier (cmon_setoid A)) :
  cmon_map (@ret _ _ TM A) a = fr_gen a := eq_refl.

(* μ = U ε F, the evaluation of a formal expression of formal expressions: it removes the outer brackets. / μ = U ε F，形式表达式的形式表达式的求值：它会去掉外层括号。 *)
Example T_join_counit@{+} (A : Ab@{u p}) :
  @join _ _ TM A
    = fmap[Rng_Forget_Ab]
        (@counit _ _ _ _ free_rng_ab_adjunction_hom (FreeRngAb A))
  := eq_refl.

Example T_join_fun@{+} (A : Ab@{u p}) (t : FRTerm (fobj[TF] A)) :
  cmon_map (@join _ _ TM A) t = fr_eval (@id Ab@{u p} (fobj[TF] A)) t
  := eq_refl.

Example T_join_gen@{+} (A : Ab@{u p}) (t : FRTerm A) :
  cmon_map (@join _ _ TM A) (@fr_gen (fobj[TF] A) t) = t := eq_refl.

Example T_join_mul@{+} (A : Ab@{u p}) (s t : FRTerm A) :
  cmon_map (@join _ _ TM A)
    (fr_mul (@fr_gen (fobj[TF] A) s) (@fr_gen (fobj[TF] A) t))
    = fr_mul s t := eq_refl.

Example T_join_plus@{+} (A : Ab@{u p}) (s t : FRTerm A) :
  cmon_map (@join _ _ TM A)
    (fr_plus (@fr_gen (fobj[TF] A) s) (@fr_gen (fobj[TF] A) t))
    = fr_plus s t := eq_refl.

Example T_join_one@{+} (A : Ab@{u p}) :
  cmon_map (@join _ _ TM A) (@fr_one (fobj[TF] A)) = @fr_one A := eq_refl.

(* T f relabels the generators, up to ≈: the action on arrows is [FreeRngAb]'s, read through the universal arrows. / T f 对生成元重新标记，最多≈：对箭头的作用是 [FreeRngAb] 的，透过通用箭头阅读。 *)
Lemma T_map_relabel@{+} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (t : FRTerm A) :
  cmon_map (fmap[TF] f) t ≈ fr_eval (free_rng_ab_insert B ∘[Ab@{u p}] f) t.
Proof.
  apply (free_rng_ab_extend_unique (FreeRngAb B)
           (free_rng_ab_insert B ∘[Ab@{u p}] f) (fmap[FreeRngAb] f)).
  intro a. exact (free_rng_ab_fmap_generators f a).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** An algebra is a ring / ** 代数是一个环 *)

Definition RngAlg@{+} : Category@{u p p} :=
  @EilenbergMoore@{u u u p} Ab@{u p} TF TM.

Section Alg.

Context {A : Ab@{u p}} (α : @TAlgebra Ab@{u p} TF TM A).

Local Notation h := (cmon_map (t_alg[α])).

Lemma ralg_unit@{+} (a : carrier (cmon_setoid A)) : h (fr_gen a) ≈ a.
Proof. exact (@t_id _ _ _ _ α a). Qed.

(* The action law, with T h read as the relabelling. / 作用定律，T h 被视为重新标记。 *)
Lemma ralg_action@{+} (t : FRTerm (fobj[TF] A)) :
  h (fr_eval (free_rng_ab_insert A ∘[Ab@{u p}] t_alg[α]) t)
    ≈ h (fr_eval (@id Ab@{u p} (fobj[TF] A)) t).
Proof.
  transitivity (h (cmon_map (fmap[TF] (t_alg[α])) t)).
  - apply (proper_morphism (cmon_map (t_alg[α]))). symmetry.
    apply T_map_relabel.
  - exact (@t_action _ _ _ _ α t).
Qed.

(* The unit h⟨⟩ = h 1 and the product a ⋆ b = h(⟨a⟩·⟨b⟩). / 单位 h⟨⟩ = h 1，积 a ⋆ b = h(⟨a⟩·⟨b⟩)。 *)
Definition ralg_one@{+} : carrier (cmon_setoid A) := h fr_one.

Definition ralg_mul@{+} (a b : carrier (cmon_setoid A)) :
  carrier (cmon_setoid A) := h (fr_mul (fr_gen a) (fr_gen b)).

(* h(s·t) ≈ h s ⋆ h t: the action law at the expression ⟨s⟩·⟨t⟩ of T T A. / h(s·t) ≈ h s ⋆ h t：在 T T A 的表达式 ⟨s⟩·⟨t⟩ 上的作用定律。 *)
Lemma ralg_mul_eval@{+} (s t : FRTerm A) :
  ralg_mul (h s) (h t) ≈ h (fr_mul s t).
Proof.
  exact (ralg_action (fr_mul (@fr_gen (fobj[TF] A) s)
                             (@fr_gen (fobj[TF] A) t))).
Qed.

Lemma ralg_mul_respects@{+} : Proper (equiv ==> equiv ==> equiv) ralg_mul.
Proof.
  intros a a' Ha b b' Hb. unfold ralg_mul.
  apply (proper_morphism (cmon_map (t_alg[α]))).
  exact (fre_mul (fre_gen Ha) (fre_gen Hb)).
Qed.

Lemma ralg_mul_assoc@{+} a b c :
  ralg_mul (ralg_mul a b) c ≈ ralg_mul a (ralg_mul b c).
Proof.
  transitivity (ralg_mul (ralg_mul a b) (h (fr_gen c))).
  { apply ralg_mul_respects; [ reflexivity | symmetry; apply ralg_unit ]. }
  transitivity (h (fr_mul (fr_mul (fr_gen a) (fr_gen b)) (fr_gen c))).
  { exact (ralg_mul_eval (fr_mul (fr_gen a) (fr_gen b)) (fr_gen c)). }
  transitivity (h (fr_mul (fr_gen a) (fr_mul (fr_gen b) (fr_gen c)))).
  { apply (proper_morphism (cmon_map (t_alg[α]))). apply fre_mul_assoc. }
  transitivity (ralg_mul (h (fr_gen a)) (h (fr_mul (fr_gen b) (fr_gen c)))).
  { symmetry. exact (ralg_mul_eval (fr_gen a) (fr_mul (fr_gen b) (fr_gen c))). }
  apply ralg_mul_respects; [ apply ralg_unit | reflexivity ].
Qed.

Lemma ralg_one_l@{+} a : ralg_mul ralg_one a ≈ a.
Proof.
  transitivity (ralg_mul ralg_one (h (fr_gen a))).
  { apply ralg_mul_respects; [ reflexivity | symmetry; apply ralg_unit ]. }
  transitivity (h (fr_mul fr_one (fr_gen a))).
  { exact (ralg_mul_eval fr_one (fr_gen a)). }
  transitivity (h (fr_gen a)).
  { apply (proper_morphism (cmon_map (t_alg[α]))). apply fre_mul_one_l. }
  apply ralg_unit.
Qed.

Lemma ralg_one_r@{+} a : ralg_mul a ralg_one ≈ a.
Proof.
  transitivity (ralg_mul (h (fr_gen a)) ralg_one).
  { apply ralg_mul_respects; [ symmetry; apply ralg_unit | reflexivity ]. }
  transitivity (h (fr_mul (fr_gen a) fr_one)).
  { exact (ralg_mul_eval (fr_gen a) fr_one). }
  transitivity (h (fr_gen a)).
  { apply (proper_morphism (cmon_map (t_alg[α]))). apply fre_mul_one_r. }
  apply ralg_unit.
Qed.

Lemma ralg_distr_l@{+} a b c :
  ralg_mul a (cmon_plus A b c) ≈ cmon_plus A (ralg_mul a b) (ralg_mul a c).
Proof.
  unfold ralg_mul. rewrite <- cmon_map_plus.
  apply (proper_morphism (cmon_map (t_alg[α]))).
  refine (fre_trans (fre_mul (fr_refl _) (fre_gen_plus b c)) _).
  apply fre_distr_l.
Qed.

Lemma ralg_distr_r@{+} a b c :
  ralg_mul (cmon_plus A a b) c ≈ cmon_plus A (ralg_mul a c) (ralg_mul b c).
Proof.
  unfold ralg_mul. rewrite <- cmon_map_plus.
  apply (proper_morphism (cmon_map (t_alg[α]))).
  refine (fre_trans (fre_mul (fre_gen_plus a b) (fr_refl _)) _).
  apply fre_distr_r.
Qed.

Lemma ralg_mul_zero_l@{+} a : ralg_mul (cmon_zero A) a ≈ cmon_zero A.
Proof.
  unfold ralg_mul.
  transitivity (h fr_zero); [ | exact (cmon_map_zero (t_alg[α])) ].
  apply (proper_morphism (cmon_map (t_alg[α]))).
  refine (fre_trans (fre_mul fre_gen_zero (fr_refl _)) _).
  apply fr_mul_zero_l.
Qed.

Lemma ralg_mul_zero_r@{+} a : ralg_mul a (cmon_zero A) ≈ cmon_zero A.
Proof.
  unfold ralg_mul.
  transitivity (h fr_zero); [ | exact (cmon_map_zero (t_alg[α])) ].
  apply (proper_morphism (cmon_map (t_alg[α]))).
  refine (fre_trans (fre_mul (fr_refl _) fre_gen_zero) _).
  apply fr_mul_zero_r.
Qed.

(* The ring of the algebra: A's own 0, + and −, with 1 and ⋆ above. Its carrier is a set because A's is. / 代数的环：A 自身的 0、+ 和 −，上面有 1 和 ⋆。它的承载集合是一个集合，因为 A 的也是。 *)
Definition ralg_rig@{+} : RigObject := {|
  rig_setoid := cmon_setoid A;
  rig_zero := cmon_zero A;
  rig_add := cmon_plus A;
  rig_one := ralg_one;
  rig_mul := ralg_mul;
  rig_add_respects := cmon_plus_respects A;
  rig_mul_respects := ralg_mul_respects;
  rig_add_assoc := cmon_plus_assoc A;
  rig_add_comm := cmon_plus_comm A;
  rig_add_zero_l := cmon_plus_zero_l A;
  rig_mul_assoc := ralg_mul_assoc;
  rig_mul_one_l := ralg_one_l;
  rig_mul_one_r := ralg_one_r;
  rig_distr_l := ralg_distr_l;
  rig_distr_r := ralg_distr_r;
  rig_mul_zero_l := ralg_mul_zero_l;
  rig_mul_zero_r := ralg_mul_zero_r;
  rig_prop := cmon_prop A
|}.

Definition ralg_ring@{+} : RingObject := {|
  ring_rig := ralg_rig;
  ring_neg := ab_neg A;
  ring_neg_respects := ab_neg_respects A;
  ring_neg_l := ab_neg_left A
|}.

(* The structure map IS the evaluation of formal expressions in the ring of the algebra, up to ≈: "the sum of the products". / 结构映射就是代数环中形式表达式的评估，直到 ≈：“乘积之和”。 *)
Lemma ralg_fold@{+} (t : FRTerm A) :
  fr_eval (R := ralg_ring) (@id Ab@{u p} A) t ≈ h t.
Proof.
  induction t as [ a | | | t1 IH1 t2 IH2 | t IH | t1 IH1 t2 IH2 ]; simpl.
  - symmetry. apply ralg_unit.
  - symmetry. exact (cmon_map_zero (t_alg[α])).
  - reflexivity.
  - rewrite IH1, IH2. symmetry. exact (cmon_map_plus (t_alg[α]) _ _).
  - rewrite IH. symmetry. exact (ab_map_neg (t_alg[α]) _).
  - transitivity (ralg_mul (h t1) (h t2)).
    + apply ralg_mul_respects; assumption.
    + apply ralg_mul_eval.
Qed.

End Alg.

Arguments ralg_one {A} α.
Arguments ralg_mul {A} α a b.
Arguments ralg_rig {A} α.
Arguments ralg_ring {A} α.

(* ------------------------------------------------------------------------ *)
(* * ** The comparison functor K and the isomorphism Rng ≅ Ab^T / * ** 比较函子 K 和同构 Rng ≅ Ab^T *)

Definition EM_rng_map@{+} {x y : RngAlg} (f : x ~{RngAlg}~> y) :
  ralg_ring (projT2 x) ~{Rng@{u p}}~> ralg_ring (projT2 y).
Proof.
  unshelve refine (@Build_RigHom (ralg_ring (projT2 x)) (ralg_ring (projT2 y))
                    (cmon_map (t_alg_hom[f])) _ _ _ _).
  - exact (cmon_map_zero (t_alg_hom[f])).
  - exact (cmon_map_plus (t_alg_hom[f])).
  - simpl. unfold ralg_one.
    transitivity (cmon_map (t_alg[projT2 y])
                    (cmon_map (fmap[TF] (t_alg_hom[f])) fr_one)).
    + exact (@t_alg_hom_commutes _ _ _ _ _ _ _ f fr_one).
    + apply (proper_morphism (cmon_map (t_alg[projT2 y]))).
      exact (rig_map_one (fmap[FreeRngAb] (t_alg_hom[f]))).
  - intros a b. simpl. unfold ralg_mul.
    transitivity (cmon_map (t_alg[projT2 y])
                    (cmon_map (fmap[TF] (t_alg_hom[f]))
                       (fr_mul (fr_gen a) (fr_gen b)))).
    + exact (@t_alg_hom_commutes _ _ _ _ _ _ _ f
               (fr_mul (fr_gen a) (fr_gen b))).
    + apply (proper_morphism (cmon_map (t_alg[projT2 y]))).
      exact (T_map_relabel (t_alg_hom[f]) (fr_mul (fr_gen a) (fr_gen b))).
Defined.

Definition EM_to_Rng@{+} : RngAlg ⟶ Rng@{u p}.
Proof.
  unshelve refine
    (@Build_Functor RngAlg Rng@{u p} (fun x => ralg_ring (projT2 x))
       (fun x y f => EM_rng_map f) _ _ _).
  - intros x y f g H. exact H.
  - intros x a. reflexivity.
  - intros x y z f g a. reflexivity.
Defined.

(* The comparison functor K : Rng → Ab^T, K R = ⟨U R, U ε_R⟩. / 比较函子 K : Rng → Ab^T，K R = ⟨U R, U ε_R⟩。 *)
Definition Rng_K@{+} : Rng@{u p} ⟶ RngAlg :=
  EM_Comparison free_rng_ab_adjunction_hom.

(* The algebra round trip, with the identity as its component. / 代数往返，以恒等式作为其组成部分。 *)
Definition Rng_EM_counit_iso@{+} (x : RngAlg) :
  @Isomorphism RngAlg (fobj[Rng_K ◯ EM_to_Rng] x) x.
Proof.
  unshelve refine
    (@Build_Isomorphism RngAlg (fobj[Rng_K ◯ EM_to_Rng] x) x
       (@Build_TAlgebraHom Ab@{u p} TF TM (projT1 x) (projT1 x)
          (projT2 (fobj[Rng_K ◯ EM_to_Rng] x)) (projT2 x)
          (@id Ab@{u p} (projT1 x)) _)
       (@Build_TAlgebraHom Ab@{u p} TF TM (projT1 x) (projT1 x)
          (projT2 x) (projT2 (fobj[Rng_K ◯ EM_to_Rng] x))
          (@id Ab@{u p} (projT1 x)) _) _ _).
  - intro t. simpl.
    transitivity (cmon_map (t_alg[projT2 x]) t);
      [ exact (ralg_fold (projT2 x) t) | ].
    apply (proper_morphism (cmon_map (t_alg[projT2 x]))).
    symmetry. exact (@fmap_id _ _ TF (projT1 x) t).
  - intro t. simpl.
    transitivity (cmon_map (t_alg[projT2 x]) (cmon_map (fmap[TF] id) t)).
    + apply (proper_morphism (cmon_map (t_alg[projT2 x]))).
      symmetry. exact (@fmap_id _ _ TF (projT1 x) t).
    + symmetry. exact (ralg_fold (projT2 x) _).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(*
 The ring round trip, with the identity as its component: every
 operation comes back on the nose. 

 --------
 环形往返，恒等作为其组成部分：每个操作都精确无误地回转。
*)
Definition Rng_EM_unit_iso@{+} (R : Rng@{u p}) :
  @Isomorphism Rng@{u p} (fobj[EM_to_Rng ◯ Rng_K] R) R.
Proof.
  unshelve refine
    (@Build_Isomorphism Rng@{u p} (fobj[EM_to_Rng ◯ Rng_K] R) R
       (@Build_RigHom (fobj[EM_to_Rng ◯ Rng_K] R) R
          (@setoid_morphism_id (rig_setoid R)) _ _ _ _)
       (@Build_RigHom R (fobj[EM_to_Rng ◯ Rng_K] R)
          (@setoid_morphism_id (rig_setoid R)) _ _ _ _) _ _);
    simpl; intros; reflexivity.
Defined.

(* K is an equivalence, with identity components both ways. / K 是一个等价关系，两边都有恒等分量。 *)
Definition Rng_EM_equivalence@{+} :
  @EquivalenceOfCategories@{u u u u u p} Rng@{u p} RngAlg Rng_K.
Proof.
  unshelve refine (@Build_EquivalenceOfCategories _ _ Rng_K EM_to_Rng _ _).
  - exists (fun x => Rng_EM_counit_iso x).
    intros x y f a. reflexivity.
  - exists (fun R => iso_sym (Rng_EM_unit_iso R)).
    intros R S f a. reflexivity.
Defined.

(* Riehl, Example 5.5.7(ii): the forgetful functor Rng → Ab is monadic. / Riehl，第 5.5.7(ii) 例：遗忘函子 Rng → Ab 是单子化的。 *)
Definition Rng_Forget_Ab_Monadic@{+} :
  @Monadic@{u u u u u p u u} Rng@{u p} Ab@{u p} Rng_Forget_Ab.
Proof.
  exists FreeRngAb.
  exists free_rng_ab_adjunction_hom.
  exact Rng_EM_equivalence.
Defined.

(*
 Mac Lane's "the comparison functor from rings to T-algebras is an
 isomorphism": Rng ≅ Ab^T in Cat, from the two component isomorphisms. 

 --------
 Mac Lane的“从环到T-代数的比较函子是一个同构”：Rng ≅ Ab^T 在Cat中，由两个分量同构得到。
*)
Definition Rng_EM_iso@{c +} :
  @Isomorphism Cat@{c u u u p} Rng@{u p} RngAlg.
Proof.
  unshelve refine
    (@Build_Isomorphism Cat@{c u u u p} Rng@{u p} RngAlg Rng_K EM_to_Rng _ _).
  - exists (fun x => Rng_EM_counit_iso x).
    intros x y f a. reflexivity.
  - exists (fun R => Rng_EM_unit_iso R).
    intros R S f a. reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(* * ** Commuting with the forgetful functors / * ** 与遗忘函子交换 *)

Definition RngAlg_Forget@{+} : RngAlg ⟶ Ab@{u p} :=
  @EM_Forget Ab@{u p} TF TM.

Theorem Rng_K_Forget@{+} : RngAlg_Forget ◯ Rng_K ≈ Rng_Forget_Ab.
Proof. exact (EM_Comparison_Forget free_rng_ab_adjunction_hom). Qed.

Theorem EM_to_Rng_Forget@{+} : Rng_Forget_Ab ◯ EM_to_Rng ≈ RngAlg_Forget.
Proof.
  exists (fun x => iso_id).
  intros x y f a. reflexivity.
Qed.

Example Rng_K_Forget_obj@{+} (R : Rng@{u p}) :
  fobj[RngAlg_Forget] (fobj[Rng_K] R) = fobj[Rng_Forget_Ab] R := eq_refl.

Example Rng_K_Forget_map@{+} {R S : Rng@{u p}} (f : R ~{Rng@{u p}}~> S) :
  fmap[RngAlg_Forget] (fmap[Rng_K] f) = fmap[Rng_Forget_Ab] f := eq_refl.

Example EM_to_Rng_Forget_obj@{+} (x : RngAlg) :
  fobj[Rng_Forget_Ab] (fobj[EM_to_Rng] x) = fobj[RngAlg_Forget] x
  := eq_refl.

Example EM_to_Rng_Forget_map@{+} {x y : RngAlg} (f : x ~{RngAlg}~> y) :
  fmap[Rng_Forget_Ab] (fmap[EM_to_Rng] f) = fmap[RngAlg_Forget] f
  := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Readbacks / ** 回读 *)

(* The two legs of the isomorphism in Cat are the two functors. / Cat 中同构的两条腿是两个函子。 *)
Example Rng_EM_iso_to@{+} : to Rng_EM_iso = Rng_K := eq_refl.

Example Rng_EM_iso_from@{+} : from Rng_EM_iso = EM_to_Rng := eq_refl.

(* K R = ⟨U R, U ε_R⟩: the structure map evaluates formal expressions in R, and so sends 1, ⟨a⟩, ⟨a⟩·⟨b⟩ and ⟨a⟩ + ⟨b⟩ to 1, a, a·b and a + b. / K R = ⟨U R, U ε_R⟩：结构映射对 R 中的形式表达式进行求值，因此将 1、⟨a⟩、⟨a⟩·⟨b⟩ 和 ⟨a⟩ + ⟨b⟩ 映射为 1、a、a·b 和 a + b。 *)
Example Rng_K_carrier@{+} (R : Rng@{u p}) :
  projT1 (fobj[Rng_K] R) = Rng_Forget_Ab R := eq_refl.

Example Rng_K_alg@{+} (R : Rng@{u p}) :
  t_alg[projT2 (fobj[Rng_K] R)]
    = fmap[Rng_Forget_Ab] (@counit _ _ _ _ free_rng_ab_adjunction_hom R)
  := eq_refl.

Example Rng_K_alg_fun@{+} (R : Rng@{u p}) (t : FRTerm (Rng_Forget_Ab R)) :
  cmon_map (t_alg[projT2 (fobj[Rng_K] R)]) t
    = fr_eval (@id Ab@{u p} (Rng_Forget_Ab R)) t := eq_refl.

Example Rng_K_alg_one@{+} (R : Rng@{u p}) :
  cmon_map (t_alg[projT2 (fobj[Rng_K] R)]) (@fr_one (Rng_Forget_Ab R))
    = rig_one R := eq_refl.

Example Rng_K_alg_gen@{+} (R : Rng@{u p}) (a : carrier (rig_setoid R)) :
  cmon_map (t_alg[projT2 (fobj[Rng_K] R)]) (@fr_gen (Rng_Forget_Ab R) a) = a
  := eq_refl.

Example Rng_K_alg_mul@{+} (R : Rng@{u p}) (a b : carrier (rig_setoid R)) :
  cmon_map (t_alg[projT2 (fobj[Rng_K] R)])
    (fr_mul (@fr_gen (Rng_Forget_Ab R) a) (@fr_gen (Rng_Forget_Ab R) b))
    = rig_mul R a b := eq_refl.

Example Rng_K_alg_plus@{+} (R : Rng@{u p}) (a b : carrier (rig_setoid R)) :
  cmon_map (t_alg[projT2 (fobj[Rng_K] R)])
    (fr_plus (@fr_gen (Rng_Forget_Ab R) a) (@fr_gen (Rng_Forget_Ab R) b))
    = rig_add R a b := eq_refl.

Example Rng_K_map@{+} {R S : Rng@{u p}} (f : R ~{Rng@{u p}}~> S) :
  t_alg_hom[fmap[Rng_K] f] = fmap[Rng_Forget_Ab] f := eq_refl.

(* The ring of an algebra: 1 = h 1, a·b = h(⟨a⟩·⟨b⟩), and A's own +. / 代数的环：1 = h 1，a·b = h(⟨a⟩·⟨b⟩)，以及 A 自身的 +。 *)
Example EM_to_Rng_one@{+} (x : RngAlg) :
  rig_one (fobj[EM_to_Rng] x) = cmon_map (t_alg[projT2 x]) fr_one
  := eq_refl.

Example EM_to_Rng_mul@{+} (x : RngAlg)
  (a b : carrier (cmon_setoid (projT1 x))) :
  rig_mul (fobj[EM_to_Rng] x) a b
    = cmon_map (t_alg[projT2 x]) (fr_mul (fr_gen a) (fr_gen b)) := eq_refl.

Example EM_to_Rng_add@{+} (x : RngAlg) :
  rig_add (fobj[EM_to_Rng] x) = cmon_plus (projT1 x) := eq_refl.

Example EM_to_Rng_map@{+} {x y : RngAlg} (f : x ~{RngAlg}~> y) :
  rig_map (fmap[EM_to_Rng] f) = cmon_map (t_alg_hom[f]) := eq_refl.

(* The ring round trip returns every operation and every map on the nose. / 环形往返返回每个操作和每个地图上的精确结果。 *)
Example Rng_rt_setoid@{+} (R : Rng@{u p}) :
  rig_setoid (fobj[EM_to_Rng ◯ Rng_K] R) = rig_setoid R := eq_refl.

Example Rng_rt_zero@{+} (R : Rng@{u p}) :
  rig_zero (fobj[EM_to_Rng ◯ Rng_K] R) = rig_zero R := eq_refl.

Example Rng_rt_add@{+} (R : Rng@{u p}) :
  rig_add (fobj[EM_to_Rng ◯ Rng_K] R) = rig_add R := eq_refl.

Example Rng_rt_one@{+} (R : Rng@{u p}) :
  rig_one (fobj[EM_to_Rng ◯ Rng_K] R) = rig_one R := eq_refl.

Example Rng_rt_mul@{+} (R : Rng@{u p}) (a b : carrier (rig_setoid R)) :
  rig_mul (fobj[EM_to_Rng ◯ Rng_K] R) a b = rig_mul R a b := eq_refl.

Example Rng_rt_neg@{+} (R : Rng@{u p}) :
  ring_neg (fobj[EM_to_Rng ◯ Rng_K] R) = ring_neg R := eq_refl.

Example Rng_rt_hom@{+} {R S : Rng@{u p}} (f : R ~{Rng@{u p}}~> S) :
  rig_map (fmap[EM_to_Rng ◯ Rng_K] f) = rig_map f := eq_refl.

(* The algebra round trip keeps the group and the maps on the nose, and returns the structure map as the evaluation in the algebra's ring. / 代数回程严格保持群和映射，并将结构映射作为代数环中的评估返回。 *)
Example EM_Rng_rt_carrier@{+} (x : RngAlg) :
  projT1 (fobj[Rng_K ◯ EM_to_Rng] x) = projT1 x := eq_refl.

Example EM_Rng_rt_alg_fun@{+} (x : RngAlg) (t : FRTerm (projT1 x)) :
  cmon_map (t_alg[projT2 (fobj[Rng_K ◯ EM_to_Rng] x)]) t
    = fr_eval (R := ralg_ring (projT2 x)) (@id Ab@{u p} (projT1 x)) t
  := eq_refl.

Example EM_Rng_rt_alg_hom@{+} {x y : RngAlg} (f : x ~{RngAlg}~> y) :
  t_alg_hom[fmap[Rng_K ◯ EM_to_Rng] f] = t_alg_hom[f] := eq_refl.

(*
 Every component of the two natural isomorphisms is the identity, at a
 variable object, to and from. 

 --------
 这两个自然同构的每个分量都是在一个变量对象上的恒等映射，来回都是如此。
*)
Example Rng_EM_iso_to_from_component@{+} (x : RngAlg) :
  (t_alg_hom[to (projT1 (iso_to_from Rng_EM_iso) x)],
   t_alg_hom[from (projT1 (iso_to_from Rng_EM_iso) x)])
    = (@id Ab@{u p} (projT1 x), @id Ab@{u p} (projT1 x)) := eq_refl.

Example Rng_EM_iso_from_to_component@{+} (R : Rng@{u p}) :
  (rig_map (to (projT1 (iso_from_to Rng_EM_iso) R)),
   rig_map (from (projT1 (iso_from_to Rng_EM_iso) R)))
    = (@setoid_morphism_id (rig_setoid R),
       @setoid_morphism_id (rig_setoid R)) := eq_refl.

Example Rng_EM_counit_component@{+} (x : RngAlg) :
  (t_alg_hom[to (projT1 (@equivalence_counit _ _ _ Rng_EM_equivalence) x)],
   t_alg_hom[from (projT1 (@equivalence_counit _ _ _
                             Rng_EM_equivalence) x)])
    = (@id Ab@{u p} (projT1 x), @id Ab@{u p} (projT1 x)) := eq_refl.

Example Rng_EM_unit_component@{+} (R : Rng@{u p}) :
  (rig_map (to (projT1 (@equivalence_unit _ _ _ Rng_EM_equivalence) R)),
   rig_map (from (projT1 (@equivalence_unit _ _ _ Rng_EM_equivalence) R)))
    = (@setoid_morphism_id (rig_setoid R),
       @setoid_morphism_id (rig_setoid R)) := eq_refl.

End TensorAlgebraMonad.
