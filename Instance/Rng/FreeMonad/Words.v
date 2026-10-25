Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Monad.Morphism.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Polynomial.
Require Import Category.Instance.Rng.Free.
Require Import Category.Instance.Rng.FreeMonad.
Require Import Category.Instance.Ab.TensorPower.
Require Import Coq.Lists.List.

Generalizable All Variables.

(* * * The tensor-algebra monad T, directly: T A ≅ ⨁ₙ A^{⊗n} / * * 张量代数单子 T，直接：T A ≅ ⨁ₙ A^{⊗n} *)

(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Springer GTM 5, 1998, §VI.4, Exercise 4(a), printed p. 146 (PDF
 p. 155) — maclane:VI.4:ex4
 Book: Riehl, "Category Theory in Context", Example 5.5.7(ii), printed
 p. 205 (PDF p. 225) — riehl:5.5:example7
 nLab: https://ncatlab.org/nlab/show/tensor+algebra

 WHAT THE BOOK ASKS, read from the page image: "(a) Give a direct
 description of this monad, like that in the text for W, with Xⁿ
 replaced by the n-fold tensor power and coproduct ∐ by the (infinite)
 direct sum of abelian groups."  The text's description of W
 (Proposition 1, p. 145) is WX = ∐ Xⁿ, η x = ⟨x⟩ and μ the
 juxtaposition of words of words.  Here, with T the monad of
 Instance/Rng/FreeMonad.v: T A ≅ ⨁ₙ A^{⊗n}, η a = the one-letter word
 ⟨a⟩ in degree one, μ the juxtaposition of words of words, and T f =
 f^{⊗n} on each word.

 THE RING ⨁ₙ A^{⊗n}.  [TWRing A] is Instance/Ab/TensorPower.v's [TWAb A]
 with the empty word as 1 and juxtaposition [tw_mul] as the product.
 Associativity and both unit laws are LEIBNIZ equations
 ([tw_mul_assoc], [tw_mul_one_l], [tw_mul_one_r]: list concatenation),
 right distributivity and 0·t = 0 hold by conversion, and ⟨u⟩·⟨v⟩ =
 ⟨u v⟩ at [eq_refl] ([tw_mul_words]).  Its abelian group IS [TWAb A]
 ([TWRing_ab], [eq_refl]).

 WHY A NEW CARRIER.  The carrier of T A is Instance/Rng/Free.v's formal
 ring expressions, and a statement that T A is the direct sum, with
 ONLY the relations of multilinearity, needs a map out of T A that
 separates what the direct sum separates; such a map is a ring map
 T A → R for some ring R carrying the sum, so the sum must be built as
 a ring first.  It is reached only through the SHARED extension: the
 forward map [tw_to_rng] is Free.v's [free_rng_ab_extend] of the
 insertion [tw_insert] of one-letter words, not a second free ring or
 free functor.  The inverse [tw_from] sends a word to the product of
 its letters, [fr_word] (⟨⟩ ↦ 1, ⟨a⟩ ↦ ⟨a⟩, ⟨a w⟩ ↦ ⟨a⟩·⟨w⟩: no factor 1
 on a non-empty word, so that ν⟨a⟩ and ν⟨a b⟩ read on the nose in
 Instance/Rng/FreeMonad/System.v).

 MAC LANE'S (a).  [T_TW_iso : T A ≅ TWAb A] in Ab.  to ∘ from is the
 identity on terms at LEIBNIZ ([tw_to_from], by induction; refused at
 [eq_refl] at a variable, R24); from ∘ to is the identity at ≈
 ([tw_from_to]) and on the nose at a generator and at a product of two
 ([T_TW_from_to_gen], [T_TW_from_to_pair]), refused at [eq_refl] at a
 variable (R22) and at (⟨a⟩·⟨b⟩)·⟨c⟩ (R23), and false at Leibniz = there
 (C105: it rebrackets to the right).  η a goes to ⟨a⟩ ([T_TW_ret]); to
 IS the evaluation through [tw_insert] and from the word product
 ([T_TW_to_fun], [T_TW_from_word]).  μ, read through the isomorphism,
 is the juxtaposition [tw_join] of the inner words of a word of words
 ([T_TW_join], at ≈; on the nose at a generator and at a product of
 two of T T A, [T_TW_join_gen], [T_TW_join_pair]; the juxtaposition of
 two words is their concatenation, [tw_join_two]); [T_TW_join] is
 refused at [eq_refl] at a variable (R25) and false at Leibniz = (C106:
 at ⟨⟨x⟩ + ⟨y⟩⟩ · 0 one side is 0 + 0 and the other 0).  T f, read
 through the isomorphism, is the letterwise map [tw_map f], f^{⊗n} on
 each word ([T_TW_map], at ≈), refused at [eq_refl] at a generator
 (R26), where T f is stuck on the universal arrows.  ⨁ₙ (−)^{⊗n} is an
 endofunctor [TWF] of Ab whose action on arrows computes letterwise
 ([TWF_obj], [TWF_map_word]), and [T_TW_natural : TF ≈ TWF] is the
 natural isomorphism with [T_TW_iso] as its components
 ([T_TW_natural_component], [eq_refl]).  With Instance/Ab/TensorPower.v's
 [TW_is_tensor_coproduct] this is the direct description: T A is the
 (infinite) direct sum of the n-fold tensor powers of A.

 THE MONAD ⨁ₙ (−)^{⊗n}, DIRECTLY.  Mac Lane's "direct description of
 this monad, like that in the text for W" is [TWMonad : Monad TWF],
 Theory/Monad.v's [Build_Monad] on the functor above with η the
 one-letter word ([tw_insert]) and μ the juxtaposition [tw_join] of a
 word of words, shown to respect ≈ ([tw_join_respects], so that μ is
 the arrow [tw_join_hom] of Ab), its laws proved by induction on terms
 with no reference to the adjunction, as #470's [WordMonad_direct]
 (Instance/Smgrp/Word.v) and #472's [FreeModMonad_direct]
 (Instance/Mod/FreeMonad.v) are for W and T_R.  Unlike theirs, whose η
 and μ ARE the adjunction monad's at [eq_refl], it lives on another
 carrier, the words, so it is compared with T as a monad:
 [T_TW_monad_hom : MonadHom TM TWMonad] (Monad/Morphism.v) has the
 components [to (T_TW_iso A)] ([T_TW_monad_hom_component]),
 [TW_T_monad_hom] the inverse components [from (T_TW_iso A)]
 ([TW_T_monad_hom_component]), and [T_TW_monad_iso] makes the two
 mutually inverse in Monad/Morphism.v's category [Monads Ab] of monads
 on Ab ([T_TW_monad_iso_to], [T_TW_monad_iso_from]): T ≅ ⨁ₙ (−)^{⊗n}
 as monads.  Read pointwise, η is the insertion as the whole record
 ([TWMonad_ret], where T's η is refused as a record, R4) and μ IS
 [tw_join] ([TWMonad_join]), on a word of words the product of the
 inner words ([TWMonad_join_word]).  Of its laws, the naturality of η
 and μ ∘ η T = 1 hold by conversion ([TWMonad_join_ret]), μ ∘ T η = 1
 and the naturality of μ at LEIBNIZ ([tw_join_letters],
 [tw_join_natural]), and the associative law at ≈ only, false at
 Leibniz = (C112: at ⟨⟨⟨x⟩ + ⟨y⟩⟩, 0⟩ one side is 0 + 0 and the other
 0).  Each morphism's unit law holds by conversion and its
 multiplication law at ≈ ([T_TW_join]; [tw_to_fr_prod]).

 STRENGTHS.  Every [Example] holds at [eq_refl], and
 Test/ProbeFreeRing474.v restates each one (C62 to C68, C71 to C73,
 C76 to C78, C108 to C111 and C113 to C116).  Stated at ≈: [tw_from_to]
 and [T_TW_join], both false at Leibniz = (C105, C106), [tw_join_prod]
 and the associative law of [TWMonad] (false at Leibniz =, C112), and
 [T_TW_map], whose Leibniz form follows from [tw_to_relabel] once T f is
 the relabelling at [eq_refl], which it is when both [Qed] layers behind
 the universal arrows are [Defined] (FreeMonad.v's ROUTE A); here it is
 ≈.  The inverse laws of [T_TW_monad_iso] are those of [T_TW_iso]: to ∘
 from at Leibniz, from ∘ to at ≈.  Leibniz equalities, stronger than ≈:
 [tw_mul_lmul], [tw_mul_assoc], [tw_mul_one_l], [tw_mul_one_r],
 [fr_eval_word], [tw_to_from], [T_TW_to_word], [tw_map_lmul],
 [tw_map_mul], [tw_to_relabel], [tw_prod_cons], [tw_prod_app],
 [tw_map_id], [tw_map_comp], [tw_prod_letters], [tw_join_letters],
 [tw_prod_map] and [tw_join_natural].  Thirteen proofs end [Defined] and
 forty-three [Qed] (counted by token); all thirteen [Defined]s are
 load-bearing, measured as Instance/Rng/FreeMonad.v's header describes:
 [tw_insert] ([fr_eval_word]), [tw_from] ([T_TW_iso]), [T_TW_iso]
 ([T_TW_ret]), [tw_map_hom] ([TWF]), [TWF] ([TWF_obj]), [T_TW_natural]
 ([T_TW_natural_component]), [tw_join_hom] ([TWMonad]), [TWMonad]
 ([TWMonad_ret]), [T_TW_transform] ([T_TW_monad_hom]), [T_TW_monad_hom]
 ([T_TW_monad_hom_component]), [TW_T_transform] ([TW_T_monad_hom]),
 [TW_T_monad_hom] ([TW_T_monad_hom_component]) and [T_TW_monad_iso]
 ([T_TW_monad_iso_to]).

 UNIVERSES, read off [About] (every name, by script).  Every name is
 universe polymorphic, with no [Set] but strict lower bounds, no equation
 in any block and caps of the standard library's global levels only.  The
 juxtaposition and the word product [fr_word] are generic over an
 [AbObject] and bind its three levels (fifteen names; [TWRing] binds five
 and [TWRing_ab] four, the further levels being Instance/Ab/TensorPower.v's
 [TWAb]'s).  The rest is in sections over Ab@{u p} and binds u and p
 first: the twenty-five names that do not mention T bind them alone
 ([tw_insert], [tw_to_rng], [tw_map], [TWF] among them); [tw_join] and
 its three lemmas bind four, the further two being those of [TWAb] at a
 group of words; the eight names through T bind six, u, p and the four
 levels [FreeRngAb] carries beyond [Ab]'s ([tw_from], [T_TW_iso],
 [T_TW_natural] and its readbacks); and the six that use T twice (μ and
 T f read through the isomorphism, and from ∘ to at a generator and at a
 product) bind a second copy of three of those four, nine levels in all,
 and [T_TW_join_pair] a third, twelve.  Of the fourteen names of the
 direct monad ([tw_prod_letter] to [TWMonad_join_ret]), eleven bind u
 and p alone, [tw_join_respects] and [tw_join_hom] four, as [tw_join],
 and [tw_join_prod] three, the third the level at which the group of
 words is an object of [Ab].  Of the eleven comparing it with T,
 [TW_T_transform] and [tw_to_fr_prod] bind six, [TW_T_natural],
 [TW_T_monad_hom] and its readback nine, [T_TW_transform] twelve,
 [T_TW_monad_hom] and its readback fifteen, and [T_TW_monad_iso] and
 its two readbacks eighteen, the levels beyond six being further copies
 of three of the four (read off the constraints).  The same levels on
 Coq 8.19.2 and 8.20.1 (FreeMonad.v's header).

 NOT DELIVERED.  T A ≅ TWRing A in Rng (the forward map is a ring map,
 [tw_to_rng]; the inverse is multiplicative at ≈, [tw_to_fr_mul]; not
 packaged).  A grading on the free ring itself. 

 --------
 书籍：Mac Lane，《Categories for the Working Mathematician》，第2版，Springer GTM 5，1998年，第VI.4节，练习4(a)，印刷版第146页（PDF第155页）—— maclane:VI.4:ex4 书籍：Riehl，《Category Theory in Context》，示例5.5.7(ii)，印刷版第205页（PDF第225页）—— riehl:5.5:example7 nLab: https://ncatlab.org/nlab/show/tensor+algebra书中要求什么，从页面图片中阅读："(a) 给出这个幺半群的直接描述，就像文本中对 W 的描述一样，将 Xⁿ 替换为 n 次张量幂，将余积 ∐ 替换为阿贝尔群的（无限）直和。" 文本中对 W 的描述（命题 1，第 145 页）是 WX = ∐ Xⁿ，η x = ⟨x⟩，μ 是字的字的并列。这里，对于 Instance/Rng/FreeMonad.v 中的幺半群 T：T A ≅ ⨁ₙ A^{⊗n}，η a = 一字单词 ⟨a⟩ 位于一次级，μ 是字的字的并列，且 T f 在每个单词上等于 f^{⊗n}。环 ⨁ₙ A^{⊗n}。[TWRing A] 是 Instance/Ab/TensorPower.v 中的 [TWAb A]，空字作为 1，连写 [tw_mul] 作为乘法。结合律和两个单位律是 LEIBNIZ 方程（[tw_mul_assoc]，[tw_mul_one_l]，[tw_mul_one_r]：列表连接），右分配律和 0·t = 0 通过转换成立，并且 ⟨u⟩·⟨v⟩ = ⟨uv⟩ 在 [eq_refl]（[tw_mul_words]）。它的阿贝尔群是 [TWAb A]（[TWRing_ab]，[eq_refl]）。为什么需要一个新的载体。T A 的载体是 Instance/Rng/Free.v 的形式环表达式，并且声明 T A 是直和，并且只有多线性关系，需要一个从 T A 到能够区分直和所区分内容的映射；这样的映射是到某个环 R 的环映射 T A → R，该环 R 承载直和，因此必须首先将直和构建为一个环。它只能通过共享扩展来实现：前向映射 [tw_to_rng] 是 Free.v 的 [free_rng_ab_extend] 对单字母单词插入 [tw_insert] 的映射，而不是第二个自由环或自由函子。逆映射 [tw_from] 将一个单词映射为其字母的乘积 [fr_word]（⟨⟩ ↦ 1, ⟨a⟩ ↦ ⟨a⟩, ⟨a w⟩ ↦ ⟨a⟩·⟨w⟩：在非空单词上不引入因子 1，因此 ν⟨a⟩ 和 ν⟨a b⟩ 在 Instance/Rng/FreeMonad/System.v 中可以直接读取）。MAC LANE 的 (a). [T_TW_iso : T A ≅ TWAb A] 在 Ab. 到 ∘ 从是 LEIBNIZ ([tw_to_from]，通过归纳) 上的恒等；在变量处 [eq_refl] 被拒绝；从 ∘ 到是 ≈ ([tw_from_to]) 上的恒等，并且在生成元和两个元素的积 ([T_TW_from_to_gen], [T_TW_from_to_pair]) 上是精确的，在变量处 [eq_refl] (R22) 和在 (⟨a⟩·⟨b⟩)·⟨c⟩ (R23) 处被拒绝，并且在 Leibniz = 那里是错误的 (C105: 它向右重新分组)。η a 映射到 ⟨a⟩ ([T_TW_ret])；到 IS 是通过 [tw_insert] 的求值，而从字词积到 ([T_TW_to_fun], [T_TW_from_word]) 的映射。μ，通过同构阅读， 是一个词的内词的并置 [tw_join]（[T_TW_join]，在 ≈；在生成元和 T T A 的两个元素的乘积上恰好如此，[T_TW_join_gen]，[T_TW_join_pair]；两个词的并置是它们的连接，[tw_join_two]）；[T_TW_join] 在变量 (R25) 处被拒绝，在 Leibniz = (C106：在 ⟨⟨x⟩+⟨y⟩⟩·0 一边是 0+0，另一边是 0) 上为假。T f，通过同构阅读，是逐字映射 [tw_map f]，在每个词上是 f^{⊗n} ([T_TW_map]，在 ≈)，在生成元 (R26) 处被拒绝，T f 在普遍箭头上被卡住。⨁ₙ (−)^{⊗n} 是 Ab 的一个自函子 [TWF]，其在态射上的作用是逐字计算 ([TWF_obj], [TWF_map_word])，而 [T_TW_natural : TF ≈ TWF] 是一个自然同构，其分量为 [T_TW_iso] ([T_TW_natural_component], [eq_refl])。在 Instance/Ab/TensorPower.v 的 [TW_is_tensor_coproduct] 中，这是直接描述：T A 是 A 的 n 次张量幂的（无限）直和。单子 ⨁ₙ (−)^{⊗n}，直接方式。Mac Lane 对这个单子的“直接描述，就像文本中对 W 的描述”是 [TWMonad : Monad TWF]，Theory/Monad.v 中的 [Build_Monad] 关于上面的函子，其中 η 是单字（[tw_insert]），μ 是字的字并置 [tw_join]，被证明尊重 ≈（[tw_join_respects]），因此 μ 是 Ab 的箭头 [tw_join_hom]，其律通过对不涉及陪集的项进行归纳证明，就像 #470 的 [WordMonad_direct]（Instance/Smgrp/Word.v）和 #472 的 [FreeModMonad_direct]（Instance/Mod/FreeMonad.v）对于 W 和 T_R 一样。不像他们的，η 和 μ 是 [eq_refl] 上伴随单子（adjunction monad）的，它存在于另一个载体——单词上，所以它作为单子与 T 进行比较：[T_TW_monad_hom : MonadHom TM TWMonad] (Monad/Morphism.v) 有组件 [to (T_TW_iso A)] ([T_TW_monad_hom_component])，[TW_T_monad_hom] 的逆组件 [from (T_TW_iso A)] ([TW_T_monad_hom_component])，并且 [T_TW_monad_iso] 使得两者在 Monad/Morphism.v 的 Ab 上单子类别 [Monads Ab] ([T_TW_monad_iso_to], [T_TW_monad_iso_from]) 中互为逆：T ≅ ⨁ₙ (−)^{⊗n} 作为单子。逐点读取时，η 是作为整个记录的插入 ([TWMonad_ret], 其中 T 的 η 被拒绝为记录，R4) 并且 μ 是 [tw_join] ([TWMonad_join])，作用在一组单词的单词上是内层单词的乘积 ([TWMonad_join_word])。关于其定律，η 的自然性以及 μ ∘ η T = 1 通过变换成立 ([TWMonad_join_ret])，μ ∘ T η = 1 以及 μ 在 LEIBNIZ 处的自然性 ([tw_join_letters], [tw_join_natural])，并且只有在 ≈ 下结合律成立，在 Leibniz 下为假 = (C112: 在 ⟨⟨⟨x⟩ + ⟨y⟩⟩, 0⟩ 时，一边是 0 + 0，另一边是 0)。每个态射的单位律通过变换成立，其乘法律在 ≈ 下成立 ([T_TW_join]; [tw_to_fr_prod])。优势。每个 [Example] 在 [eq_refl] 成立，并且 Test/ProbeFreeRing474.v 重述了每一个（C62 到 C68，C71 到 C73，C76 到 C78，C108 到 C111 和 C113 到 C116）。在 ≈: [tw_from_to] 和 [T_TW_join] 中陈述，在 Leibniz 上都为假 = (C105, C106)，[tw_join_prod] 和 [TWMonad] 的结合律（在 Leibniz 上为假 =, C112），以及 [T_TW_map]，其 Leibniz 形式可从 [tw_to_relabel] 得出，一旦 T f 在 [eq_refl] 上重标记，当 [Qed] 在通用箭头之后的两层均为 [Defined]（FreeMonad.v 的 ROUTE A）时，它就是如此 ≈。[T_TW_monad_iso] 的逆律是 [T_TW_iso] 的逆律：在 Leibniz 上为 to ∘ from，从 ∘ 到 ≈。莱布尼茨等式，比 ≈ 更强：
 [tw_mul_lmul] ， [tw_mul_assoc] ， [tw_mul_one_l] ， [tw_mul_one_r] ，
 [fr_eval_word] ， [tw_to_from] ， [T_TW_to_word] ， [tw_map_lmul] ，
 [tw_map_mul] ， [tw_to_relabel] ， [tw_prod_cons] ， [tw_prod_app] ，
 [tw_map_id] ， [tw_map_comp] ， [tw_prod_letters] ， [tw_join_letters] ，
 [tw_prod_map] 和 [tw_join_natural] 。十三个证明结束 [Defined] 和
 四十三个 [Qed] （按标记计数）；所有十三个 [Defined] 都是
 承重的，衡量方式如 Instance/Rng/FreeMonad.v 的头部所描述：
 [tw_insert] （ZWZ109WZZ）， [tw_from] （ZWZ111WZZ）， [T_TW_iso]
 （ZWZ113WZZ）， [tw_map_hom] （ZWZ115WZZ）， [TWF] （ZWZ117WZZ）， [T_TW_natural]
 （ZWZ119WZZ）， [tw_join_hom] （ZWZ121WZZ）， [TWMonad]
 （ZWZ123WZZ）， [T_TW_transform] （ZWZ125WZZ）， [T_TW_monad_hom]
 （ZWZ127WZZ）， [TW_T_transform] （ZWZ129WZZ），
 [TW_T_monad_hom] （ZWZ131WZZ） 和 [T_TW_monad_iso]
 （ZWZ133WZZ）。宇宙，按 [About] 读取（每个名称，按脚本）。每个名称都是多态的宇宙，没有 [Set] 但有严格的下界，没有任何块中的方程，并且只有标准库全局级别的上限。并置和词积 [fr_word] 对 [AbObject] 是通用的，并绑定其三个级别（十五个名称；[TWRing] 绑定五个，[TWRing_ab] 绑定四个，更高的级别是 Instance/Ab/TensorPower.v 的 [TWAb]）。其余部分分为关于 Ab@{u p} 的章节，并绑定 u 和 p
 首先：二十五个未提及 T 的名字单独绑定它们（其中包括 [tw_insert]、[tw_to_rng]、[tw_map]、[TWF]）；[tw_join] 及其三个词元绑定四个，其余两个是 [TWAb] 在一组词中的；通过 T 的八个名字绑定六个，u、p 以及 [FreeRngAb] 超过 [Ab] 的四个层次（[tw_from]、[T_TW_iso]、[T_TW_natural] 及其回读）；使用 T 两次的六个名字（μ 和 T f 通过同构读取，从 ∘ 到生成元及乘积）绑定那四个名字中三个的第二份，总共九个层次，而 [T_TW_join_pair] 绑定第三份，总共十二个。在直接单子（[tw_prod_letter] 到 [TWMonad_join_ret]）的十四个名称中，十一绑定 u 和 p 单独，[tw_join_respects] 和 [tw_join_hom] 四个，像 [tw_join]，和 [tw_join_prod] 三个，第三个是该词组作为 [Ab] 对象的级别。在将其中的十一与 T 比较时，[TW_T_transform] 和 [tw_to_fr_prod] 绑定六个，[TW_T_natural]，[TW_T_monad_hom] 及其回读九个，[T_TW_transform] 十二个，[T_TW_monad_hom] 及其回读十五个，[T_TW_monad_iso] 及其两个回读十八个，超过六级的级别是四个中三个的进一步副本（根据约束读取）。在 Coq 8.19.2 和 8.20.1（FreeMonad.v 的头部）上具有相同的级别。未交付。在环中的 T A ≅ TWRing A（正向映射是环映射，[tw_to_rng]；逆映射在 ≈ 上是乘法性的，[tw_to_fr_mul]；未打包）。自由环本身的一个分级。
*)

(* ------------------------------------------------------------------------ *)
(* * ** The ring ⨁ₙ A^{⊗n}: juxtaposition of words / * ** 环 ⨁ₙ A^{⊗n}：单词并列 *)

Section Juxtaposition.

Context (A : AbObject).

Local Notation L := (carrier (cmon_setoid A)).

Fixpoint tw_mul (s t : TWTerm A) : TWTerm A :=
  match s with
  | tw_word w => tw_lmul w t
  | tw_zero => tw_zero
  | tw_plus s1 s2 => tw_plus (tw_mul s1 t) (tw_mul s2 t)
  | tw_neg s1 => tw_neg (tw_mul s1 t)
  end.

Lemma tw_mul_respects_l (s s' t : TWTerm A) :
  tw_eq A s s' → tw_eq A (tw_mul s t) (tw_mul s' t).
Proof.
  intro H.
  induction H as [ u v a b Hab | u v a b | s s' t1 t1' _ IH1 _ IH2 | s s' _ IH
                 | s1 s2 s3 | s1 s2 | s1 | s1 | s1 s2 _ IH
                 | s1 s2 s3 _ IH1 _ IH2 ];
    simpl.
  - exact (tw_lmul_letter A u v a b Hab t).
  - exact (tw_lmul_lin A u v a b t).
  - exact (twe_plus IH1 IH2).
  - exact (twe_neg IH).
  - apply twe_assoc.
  - apply twe_comm.
  - apply twe_zero_l.
  - apply twe_neg_l.
  - exact (twe_sym IH).
  - exact (twe_trans IH1 IH2).
Qed.

Lemma tw_mul_respects_r (s t t' : TWTerm A) :
  tw_eq A t t' → tw_eq A (tw_mul s t) (tw_mul s t').
Proof.
  intro H.
  induction s as [ w | | s1 IH1 s2 IH2 | s1 IH1 ]; simpl.
  - exact (tw_lmul_respects_r A w t t' H).
  - apply tw_refl.
  - exact (twe_plus IH1 IH2).
  - exact (twe_neg IH1).
Qed.

Lemma tw_mul_lmul (w : list L) (t u : TWTerm A) :
  tw_mul (tw_lmul w t) u = tw_lmul w (tw_mul t u).
Proof.
  induction t as [ x | | s IHs t IHt | s IHs ]; simpl.
  - apply tw_lmul_app.
  - reflexivity.
  - rewrite IHs, IHt. reflexivity.
  - rewrite IHs. reflexivity.
Qed.

(* Associativity and both unit laws are LEIBNIZ equations. / 结合律和两个单位律都是莱布尼茨方程。 *)
Lemma tw_mul_assoc (s t u : TWTerm A) :
  tw_mul (tw_mul s t) u = tw_mul s (tw_mul t u).
Proof.
  induction s as [ w | | s1 IH1 s2 IH2 | s1 IH1 ]; simpl.
  - apply tw_mul_lmul.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
Qed.

Lemma tw_mul_one_l (t : TWTerm A) : tw_mul (tw_word nil) t = t.
Proof. exact (tw_lmul_nil A t). Qed.

Lemma tw_mul_one_r (s : TWTerm A) : tw_mul s (tw_word nil) = s.
Proof.
  induction s as [ w | | s1 IH1 s2 IH2 | s1 IH1 ]; simpl.
  - rewrite app_nil_r. reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
Qed.

Lemma tw_mul_distr_l (s t u : TWTerm A) :
  tw_eq A (tw_mul s (tw_plus t u)) (tw_plus (tw_mul s t) (tw_mul s u)).
Proof.
  induction s as [ w | | s1 IH1 s2 IH2 | s1 IH1 ]; simpl.
  - apply tw_refl.
  - exact (tw_zero_zero A).
  - refine (twe_trans (twe_plus IH1 IH2) _).
    exact (cmon_plus_interchange (TWAb A) _ _ _ _).
  - refine (twe_trans (twe_neg IH1) _). apply tw_neg_plus.
Qed.

Lemma tw_mul_zero_r (s : TWTerm A) : tw_eq A (tw_mul s tw_zero) tw_zero.
Proof.
  induction s as [ w | | s1 IH1 s2 IH2 | s1 IH1 ]; simpl.
  - apply tw_refl.
  - apply tw_refl.
  - exact (twe_trans (twe_plus IH1 IH2) (twe_zero_l tw_zero)).
  - exact (twe_trans (twe_neg IH1) (tw_neg_zero A)).
Qed.

(* The ring: the words' abelian group, with the empty word as 1 and juxtaposition as the product. Right distributivity and 0·t = 0 hold by conversion. / 环：文字的阿贝尔群，以空字作为1，拼接作为乘法。右分配律和0·t = 0通过转换成立。 *)
Definition TWRing : RingObject := {|
  ring_rig := {|
    rig_setoid := cmon_setoid (TWAb A);
    rig_zero := tw_zero;
    rig_add := tw_plus;
    rig_one := tw_word nil;
    rig_mul := tw_mul;
    rig_add_respects := cmon_plus_respects (TWAb A);
    rig_mul_respects := fun s s' Hs t t' Ht =>
      twe_trans (tw_mul_respects_l s s' t Hs) (tw_mul_respects_r s' t t' Ht);
    rig_add_assoc := twe_assoc;
    rig_add_comm := twe_comm;
    rig_add_zero_l := twe_zero_l;
    rig_mul_assoc := fun s t u => tw_eq_of_eq (tw_mul_assoc s t u);
    rig_mul_one_l := fun t => tw_eq_of_eq (tw_mul_one_l t);
    rig_mul_one_r := fun s => tw_eq_of_eq (tw_mul_one_r s);
    rig_distr_l := tw_mul_distr_l;
    rig_distr_r := fun s t u => tw_refl _;
    rig_mul_zero_l := fun t => tw_refl _;
    rig_mul_zero_r := tw_mul_zero_r;
    rig_prop := cmon_prop (TWAb A)
  |};
  ring_neg := tw_neg;
  ring_neg_respects := ab_neg_respects (TWAb A);
  ring_neg_l := twe_neg_l
|}.

Example TWRing_ab : Rng_Forget_Ab TWRing = TWAb A := eq_refl.

Example tw_mul_words (u v : list L) :
  tw_mul (tw_word u) (tw_word v) = tw_word (u ++ v) := eq_refl.

End Juxtaposition.

Arguments tw_mul {A} _ _.

(* ------------------------------------------------------------------------ *)
(* * ** A word as a formal ring expression / * ** 一个作为正式环状表达的词 *)

Section WordExpr.

Context (A : AbObject).

Local Notation L := (carrier (cmon_setoid A)).

(* ⟨⟩ ↦ 1, ⟨a⟩ ↦ ⟨a⟩ and ⟨a w⟩ ↦ ⟨a⟩·⟨w⟩: the product of the letters, bracketed to the right, with no factor 1 on a non-empty word. / ⟨⟩ ↦ 1，⟨a⟩ ↦ ⟨a⟩，且 ⟨a w⟩ ↦ ⟨a⟩·⟨w⟩：字母的乘积，向右加括号，在非空单词上不加因子 1。 *)
Fixpoint fr_word (w : list L) : FRTerm A :=
  match w with
  | nil => fr_one
  | a :: w' =>
      match w' with
      | nil => fr_gen a
      | _ :: _ => fr_mul (fr_gen a) (fr_word w')
      end
  end.

Lemma fr_word_cons (a : L) (w : list L) :
  fr_eq (fr_word (a :: w)) (fr_mul (fr_gen a) (fr_word w)).
Proof.
  destruct w as [ | b w ]; simpl.
  - exact (fre_sym (fre_mul_one_r (fr_gen a))).
  - apply fr_refl.
Qed.

Lemma fr_word_letter (u v : list L) (a b : L) (H : a ≈ b) :
  fr_eq (fr_word (u ++ a :: v)) (fr_word (u ++ b :: v)).
Proof.
  induction u as [ | c u IH ]; simpl.
  - destruct v; [ exact (fre_gen H) | exact (fre_mul (fre_gen H) (fr_refl _)) ].
  - destruct u; exact (fre_mul (fr_refl _) IH).
Qed.

Lemma fr_word_lin (u v : list L) (a b : L) :
  fr_eq (fr_word (u ++ cmon_plus A a b :: v))
        (fr_plus (fr_word (u ++ a :: v)) (fr_word (u ++ b :: v))).
Proof.
  induction u as [ | c u IH ]; simpl.
  - destruct v.
    + exact (fre_gen_plus a b).
    + refine (fre_trans (fre_mul (fre_gen_plus a b) (fr_refl _)) _).
      apply fre_distr_r.
  - destruct u;
      (refine (fre_trans (fre_mul (fr_refl _) IH) _); apply fre_distr_l).
Qed.

Lemma fr_word_app (w v : list L) :
  fr_eq (fr_word (w ++ v)) (fr_mul (fr_word w) (fr_word v)).
Proof.
  induction w as [ | a w IH ].
  - exact (fre_sym (fre_mul_one_l _)).
  - refine (fre_trans (fr_word_cons a (w ++ v)) _).
    refine (fre_trans (fre_mul (fr_refl _) IH) _).
    refine (fre_trans (fre_sym (fre_mul_assoc _ _ _)) _).
    exact (fre_mul (fre_sym (fr_word_cons a w)) (fr_refl _)).
Qed.

End WordExpr.

Arguments fr_word {A} _.

(* ------------------------------------------------------------------------ *)
(* * ** Mac Lane's (a): T A ≅ ⨁ₙ A^{⊗n} / * ** Mac Lane 的 (a)：T A ≅ ⨁ₙ A^{⊗n} *)

Section Iso.

Universes u p.

Context (A : Ab@{u p}).

Local Notation L := (carrier (cmon_setoid A)).

(* The one-letter word of 0 is 0. / 0 的单字母词是 0。 *)
Lemma tw_word_zero@{+} : tw_eq A (tw_word (cmon_zero A :: nil)) tw_zero.
Proof.
  set (x := tw_word (cmon_zero A :: nil)).
  assert (H : tw_eq A x (tw_plus x x)).
  { refine (twe_trans (twe_letter nil nil
                         (symmetry (cmon_plus_zero_l A (cmon_zero A)))) _).
    exact (twe_lin nil nil (cmon_zero A) (cmon_zero A)). }
  apply (ab_cancel_l (TWAb A) x).
  refine (twe_trans (twe_sym H) _).
  exact (twe_sym (cmon_plus_zero_r (TWAb A) x)).
Qed.

(* The insertion a ↦ ⟨a⟩ of A in degree one. / 将 A 在一阶中的元素 a 插入为 ⟨a⟩。 *)
Definition tw_insert@{+} : A ~{Ab@{u p}}~> Rng_Forget_Ab (TWRing A).
Proof.
  unshelve refine (@Build_CMonHom A (Rng_Forget_Ab (TWRing A))
    (@Build_SetoidMorphism L (is_setoid (cmon_setoid A))
       (TWTerm A) (tw_Setoid A) (fun a => tw_word (a :: nil)) _) _ _).
  - intros a b H. exact (twe_letter nil nil H).
  - exact tw_word_zero.
  - intros a b. exact (twe_lin nil nil a b).
Defined.

(* to : T A → ⨁, the SHARED extension of the insertion. / 到：T A → ⨁，插入的共享扩展。 *)
Definition tw_to_rng@{+} : FreeRngAbObject A ~{Rng@{u p}}~> TWRing A :=
  free_rng_ab_extend tw_insert.

(* from : ⨁ → T A, each word to the product of its letters. / 从：⨁ → T A，每个单词映射到其字母的乘积。 *)
Fixpoint tw_to_fr (t : TWTerm A) : FRTerm A :=
  match t with
  | tw_word w => fr_word w
  | tw_zero => fr_zero
  | tw_plus s t => fr_plus (tw_to_fr s) (tw_to_fr t)
  | tw_neg s => fr_neg (tw_to_fr s)
  end.

Lemma tw_to_fr_respects@{+} (s t : TWTerm A) :
  tw_eq A s t → fr_eq (tw_to_fr s) (tw_to_fr t).
Proof.
  intro H.
  induction H as [ u v a b Hab | u v a b | s s' t t' _ IH1 _ IH2 | s s' _ IH
                 | s t u | s t | s | s | s t _ IH | s t u _ IH1 _ IH2 ];
    simpl.
  - exact (fr_word_letter A u v a b Hab).
  - exact (fr_word_lin A u v a b).
  - exact (fre_plus IH1 IH2).
  - exact (fre_neg IH).
  - apply fre_add_assoc.
  - apply fre_add_comm.
  - apply fre_add_zero_l.
  - apply fre_neg_l.
  - exact (fre_sym IH).
  - exact (fre_trans IH1 IH2).
Qed.

Definition tw_from@{+} : TWAb A ~{Ab@{u p}}~> Rng_Forget_Ab (FreeRngAb A).
Proof.
  unshelve refine (@Build_CMonHom (TWAb A) (Rng_Forget_Ab (FreeRngAb A))
    (@Build_SetoidMorphism (TWTerm A) (tw_Setoid A) (FRTerm A) (fr_Setoid A)
       tw_to_fr _) _ _).
  - intros s t H. exact (tw_to_fr_respects s t H).
  - apply fr_refl.
  - intros s t. apply fr_refl.
Defined.

(* to ∘ from is the identity on terms, LEIBNIZ. / 从 ∘ 到 在项上是恒等的，莱布尼茨。 *)
Lemma fr_eval_word@{+} (w : list L) :
  fr_eval tw_insert (fr_word w) = tw_word w.
Proof.
  induction w as [ | a w IH ]; [ reflexivity | ].
  destruct w as [ | b w ]; [ reflexivity | ].
  change (tw_mul (tw_word (a :: nil)) (fr_eval tw_insert (fr_word (b :: w)))
            = tw_word (a :: b :: w)).
  rewrite IH. reflexivity.
Qed.

Lemma tw_to_from@{+} (t : TWTerm A) : rig_map tw_to_rng (tw_to_fr t) = t.
Proof.
  induction t as [ w | | s IHs t IHt | s IHs ]; simpl.
  - apply fr_eval_word.
  - reflexivity.
  - change (tw_plus (fr_eval tw_insert (tw_to_fr s))
                    (fr_eval tw_insert (tw_to_fr t)) = tw_plus s t).
    simpl in IHs, IHt. rewrite IHs, IHt. reflexivity.
  - change (tw_neg (fr_eval tw_insert (tw_to_fr s)) = tw_neg s).
    simpl in IHs. rewrite IHs. reflexivity.
Qed.

Lemma tw_to_fr_lmul@{+} (w : list L) (t : TWTerm A) :
  fr_eq (tw_to_fr (tw_lmul w t)) (fr_mul (fr_word w) (tw_to_fr t)).
Proof.
  induction t as [ v | | s IHs t IHt | s IHs ]; simpl.
  - apply fr_word_app.
  - exact (fre_sym (fr_mul_zero_r A _)).
  - refine (fre_trans (fre_plus IHs IHt) _).
    exact (fre_sym (fre_distr_l _ _ _)).
  - refine (fre_trans (fre_neg IHs) _).
    exact (fre_sym (rng_mul_neg_r (FreeRngAbObject A) _ _)).
Qed.

Lemma tw_to_fr_mul@{+} (s t : TWTerm A) :
  fr_eq (tw_to_fr (tw_mul s t)) (fr_mul (tw_to_fr s) (tw_to_fr t)).
Proof.
  induction s as [ w | | s1 IH1 s2 IH2 | s1 IH1 ]; simpl.
  - apply tw_to_fr_lmul.
  - exact (fre_sym (fr_mul_zero_l A _)).
  - refine (fre_trans (fre_plus IH1 IH2) _).
    exact (fre_sym (fre_distr_r _ _ _)).
  - refine (fre_trans (fre_neg IH1) _).
    exact (fre_sym (rng_mul_neg_l (FreeRngAbObject A) _ _)).
Qed.

(* from ∘ to is the identity up to ≈. / 从 ∘ 到 是恒等式，误差约为 ≈。 *)
Lemma tw_from_to@{+} (t : FRTerm A) :
  fr_eq (tw_to_fr (rig_map tw_to_rng t)) t.
Proof.
  induction t as [ a | | | t1 IH1 t2 IH2 | t IH | t1 IH1 t2 IH2 ]; simpl.
  - apply fr_refl.
  - apply fr_refl.
  - apply fr_refl.
  - exact (fre_plus IH1 IH2).
  - exact (fre_neg IH).
  - refine (fre_trans (tw_to_fr_mul _ _) _). exact (fre_mul IH1 IH2).
Qed.

(* Mac Lane's (a): T A ≅ ⨁ₙ A^{⊗n} in Ab. / Mac Lane 的 (a)：T A ≅ ⨁ₙ A^{⊗n} 在 Ab 中。 *)
Definition T_TW_iso@{+} : @Isomorphism Ab@{u p} (fobj[TF] A) (TWAb A).
Proof.
  unshelve refine
    (@Build_Isomorphism Ab@{u p} (fobj[TF] A) (TWAb A)
       (fmap[Rng_Forget_Ab] tw_to_rng) tw_from _ _).
  - intro t. exact (tw_eq_of_eq (tw_to_from t)).
  - intro t. exact (tw_from_to t).
Defined.

(* η a is the one-letter word, on the nose. / η a 是那个单字，恰到好处。 *)
Example T_TW_ret@{+} (a : L) :
  cmon_map (to T_TW_iso) (cmon_map (@ret _ _ TM A) a) = tw_word (a :: nil)
  := eq_refl.

Example T_TW_to_fun@{+} (t : FRTerm A) :
  cmon_map (to T_TW_iso) t = fr_eval tw_insert t := eq_refl.

Example T_TW_from_word@{+} (w : list L) :
  cmon_map (from T_TW_iso) (tw_word w) = fr_word w := eq_refl.

Lemma T_TW_to_word@{+} (w : list L) :
  cmon_map (to T_TW_iso) (fr_word w) = tw_word w.
Proof. exact (fr_eval_word w). Qed.

(*
 from ∘ to is the identity on the nose at a generator and at a product
 of two generators. 

 --------
 从 ∘ 到 在一个生成元以及两个生成元的乘积上准确地是恒等映射。
*)
Example T_TW_from_to_gen@{+} (a : L) :
  cmon_map (from T_TW_iso) (cmon_map (to T_TW_iso) (fr_gen a)) = fr_gen a
  := eq_refl.

Example T_TW_from_to_pair@{+} (a b : L) :
  cmon_map (from T_TW_iso)
    (cmon_map (to T_TW_iso) (fr_mul (fr_gen a) (fr_gen b)))
    = fr_mul (fr_gen a) (fr_gen b) := eq_refl.

End Iso.

Arguments tw_insert {A}.
Arguments tw_to_rng {A}.
Arguments tw_to_fr {A} _.
Arguments tw_from {A}.

(* ------------------------------------------------------------------------ *)
(* * ** T f is the letterwise map f^{⊗n}; μ is juxtaposition / * ** T f 是逐字映射 f^{⊗n}；μ 是并置 *)

Section Readings.

Universes u p.

Fixpoint tw_map {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B) (t : TWTerm A) :
  TWTerm B :=
  match t with
  | tw_word w => tw_word (List.map (cmon_map f) w)
  | tw_zero => tw_zero
  | tw_plus s t => tw_plus (tw_map f s) (tw_map f t)
  | tw_neg s => tw_neg (tw_map f s)
  end.

Lemma tw_map_lmul@{+} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (w : list (carrier (cmon_setoid A))) (t : TWTerm A) :
  tw_map f (tw_lmul w t) = tw_lmul (List.map (cmon_map f) w) (tw_map f t).
Proof.
  induction t as [ v | | s IHs t IHt | s IHs ]; simpl.
  - rewrite map_app. reflexivity.
  - reflexivity.
  - rewrite IHs, IHt. reflexivity.
  - rewrite IHs. reflexivity.
Qed.

Lemma tw_map_mul@{+} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (s t : TWTerm A) :
  tw_map f (tw_mul s t) = tw_mul (tw_map f s) (tw_map f t).
Proof.
  induction s as [ w | | s1 IH1 s2 IH2 | s1 IH1 ]; simpl.
  - apply tw_map_lmul.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
Qed.

(* The relabelled evaluation, read through [to], is the letterwise map. / 重新标记的评估，通过 [to] 阅读，是逐字母映射。 *)
Lemma tw_to_relabel@{+} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (t : FRTerm A) :
  rig_map (@tw_to_rng B) (fr_eval (free_rng_ab_insert B ∘[Ab@{u p}] f) t)
    = tw_map f (rig_map (@tw_to_rng A) t).
Proof.
  induction t as [ a | | | t1 IH1 t2 IH2 | t IH | t1 IH1 t2 IH2 ]; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl in IH1, IH2. rewrite IH1, IH2. reflexivity.
  - simpl in IH. rewrite IH. reflexivity.
  - simpl in IH1, IH2. rewrite IH1, IH2. symmetry. apply tw_map_mul.
Qed.

(* T f, read through the isomorphism, is f^{⊗n} on each word. / T f，通过同构来看，就是每个词上的 f^{⊗n}。 *)
Theorem T_TW_map@{+} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (t : FRTerm A) :
  tw_eq B (cmon_map (to (T_TW_iso B)) (cmon_map (fmap[TF] f) t))
          (tw_map f (cmon_map (to (T_TW_iso A)) t)).
Proof.
  refine (twe_trans (proper_morphism (cmon_map (to (T_TW_iso B))) _ _
                       (T_map_relabel f t)) _).
  exact (tw_eq_of_eq (tw_to_relabel f t)).
Qed.

(* The product of a word of elements of the ring, bracketed to the right, with no factor 1 on a non-empty word. / 环中元素的一个词的乘积，右括号括起，在非空词上没有因子1。 *)
Fixpoint tw_prod {A : Ab@{u p}} (ws : list (TWTerm A)) : TWTerm A :=
  match ws with
  | nil => tw_word nil
  | s :: ws' =>
      match ws' with
      | nil => s
      | _ :: _ => tw_mul s (tw_prod ws')
      end
  end.

(* μ on ⨁ₙ (⨁ₘ A^{⊗m})^{⊗n}: juxtapose the inner words. / μ 在 ⨁ₙ (⨁ₘ A^{⊗m})^{⊗n} 上：并排排列内部的词。 *)
Fixpoint tw_join {A : Ab@{u p}} (t : TWTerm (TWAb A)) : TWTerm A :=
  match t with
  | tw_word ws => tw_prod ws
  | tw_zero => tw_zero
  | tw_plus s t => tw_plus (tw_join s) (tw_join t)
  | tw_neg s => tw_neg (tw_join s)
  end.

Example tw_join_two@{+} {A : Ab@{u p}}
  (u v : list (carrier (cmon_setoid A))) :
  tw_join (@tw_word (TWAb A) (tw_word u :: tw_word v :: nil))
    = tw_word (u ++ v) := eq_refl.

Lemma tw_prod_cons@{+} {A : Ab@{u p}} (s : TWTerm A) (ws : list (TWTerm A)) :
  tw_prod (s :: ws) = tw_mul s (tw_prod ws).
Proof.
  destruct ws as [ | s' ws ]; simpl; [ | reflexivity ].
  symmetry. apply tw_mul_one_r.
Qed.

Lemma tw_prod_app@{+} {A : Ab@{u p}} (ws vs : list (TWTerm A)) :
  tw_prod (ws ++ vs) = tw_mul (tw_prod ws) (tw_prod vs).
Proof.
  induction ws as [ | s ws IH ].
  - simpl. symmetry. apply tw_mul_one_l.
  - simpl app. rewrite !tw_prod_cons, IH. symmetry. apply tw_mul_assoc.
Qed.

Lemma tw_join_lmul@{+} {A : Ab@{u p}} (ws : list (TWTerm A))
  (t : TWTerm (TWAb A)) :
  tw_eq A (tw_join (@tw_lmul (TWAb A) ws t)) (tw_mul (tw_prod ws) (tw_join t)).
Proof.
  induction t as [ vs | | s IHs t IHt | s IHs ]; simpl.
  - rewrite tw_prod_app. apply tw_refl.
  - exact (twe_sym (tw_mul_zero_r A _)).
  - refine (twe_trans (twe_plus IHs IHt) _).
    exact (twe_sym (tw_mul_distr_l A _ _ _)).
  - refine (twe_trans (twe_neg IHs) _).
    exact (twe_sym (rng_mul_neg_r (TWRing A) _ _)).
Qed.

Lemma tw_join_mul@{+} {A : Ab@{u p}} (s t : TWTerm (TWAb A)) :
  tw_eq A (tw_join (tw_mul s t)) (tw_mul (tw_join s) (tw_join t)).
Proof.
  induction s as [ ws | | s1 IH1 s2 IH2 | s1 IH1 ]; simpl.
  - apply tw_join_lmul.
  - apply tw_refl.
  - exact (twe_plus IH1 IH2).
  - refine (twe_trans (twe_neg IH1) _).
    exact (twe_sym (rng_mul_neg_l (TWRing A) _ _)).
Qed.

(* μ, read through the isomorphism, is juxtaposition. / μ，通过同构阅读，是并列。 *)
Theorem T_TW_join@{+} {A : Ab@{u p}} (t : FRTerm (fobj[TF] A)) :
  tw_eq A (cmon_map (to (T_TW_iso A)) (cmon_map (@join _ _ TM A) t))
          (tw_join (tw_map (to (T_TW_iso A))
                      (cmon_map (to (T_TW_iso (fobj[TF] A))) t))).
Proof.
  induction t as [ s | | | t1 IH1 t2 IH2 | t IH | t1 IH1 t2 IH2 ]; simpl.
  - apply tw_refl.
  - apply tw_refl.
  - apply tw_refl.
  - exact (twe_plus IH1 IH2).
  - exact (twe_neg IH).
  - rewrite tw_map_mul.
    refine (twe_trans _ (twe_sym (tw_join_mul _ _))).
    exact (twe_trans (tw_mul_respects_l A _ _ _ IH1)
                     (tw_mul_respects_r A _ _ _ IH2)).
Qed.

(* On the nose at a generator of T T A and at a product of two. / 正好在 T T A 的生成器上以及两个的乘积上。 *)
Example T_TW_join_gen@{+} {A : Ab@{u p}} (s : FRTerm A) :
  cmon_map (to (T_TW_iso A))
    (cmon_map (@join _ _ TM A) (@fr_gen (fobj[TF] A) s))
  = tw_join (tw_map (to (T_TW_iso A))
       (cmon_map (to (T_TW_iso (fobj[TF] A))) (@fr_gen (fobj[TF] A) s)))
  := eq_refl.

Example T_TW_join_pair@{+} {A : Ab@{u p}} (s t : FRTerm A) :
  cmon_map (to (T_TW_iso A))
    (cmon_map (@join _ _ TM A)
       (fr_mul (@fr_gen (fobj[TF] A) s) (@fr_gen (fobj[TF] A) t)))
  = tw_join (tw_map (to (T_TW_iso A))
       (cmon_map (to (T_TW_iso (fobj[TF] A)))
          (fr_mul (@fr_gen (fobj[TF] A) s) (@fr_gen (fobj[TF] A) t))))
  := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** ⨁ₙ (−)^{⊗n} as an endofunctor of Ab, naturally isomorphic to T / * ** ⨁ₙ (−)^{⊗n} 作为 Ab 的自函子，自然同构于 T *)

Lemma tw_map_respects@{+} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (s t : TWTerm A) :
  tw_eq A s t → tw_eq B (tw_map f s) (tw_map f t).
Proof.
  intro H.
  induction H as [ u v a b Hab | u v a b | s s' t t' _ IH1 _ IH2 | s s' _ IH
                 | s t u | s t | s | s | s t _ IH | s t u _ IH1 _ IH2 ];
    simpl.
  - rewrite !map_app. simpl.
    exact (twe_letter _ _ (proper_morphism (cmon_map f) _ _ Hab)).
  - rewrite !map_app. simpl.
    refine (twe_trans (twe_letter _ _ (cmon_map_plus f a b)) _).
    apply twe_lin.
  - exact (twe_plus IH1 IH2).
  - exact (twe_neg IH).
  - apply twe_assoc.
  - apply twe_comm.
  - apply twe_zero_l.
  - apply twe_neg_l.
  - exact (twe_sym IH).
  - exact (twe_trans IH1 IH2).
Qed.

Definition tw_map_hom@{+} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B) :
  TWAb A ~{Ab@{u p}}~> TWAb B.
Proof.
  unshelve refine (@Build_CMonHom (TWAb A) (TWAb B)
    (@Build_SetoidMorphism (TWTerm A) (tw_Setoid A) (TWTerm B) (tw_Setoid B)
       (tw_map f) _) _ _).
  - intros s t H. exact (tw_map_respects f s t H).
  - apply tw_refl.
  - intros s t. apply tw_refl.
Defined.

Lemma tw_word_pointwise@{+} {A B : Ab@{u p}} (f g : A ~{Ab@{u p}}~> B)
  (H : f ≈ g) (w : list (carrier (cmon_setoid A))) :
  tw_eq B (tw_word (map (cmon_map f) w)) (tw_word (map (cmon_map g) w)).
Proof.
  induction w as [ | a w IH ]; simpl.
  - apply tw_refl.
  - refine (twe_trans (twe_letter nil _ (H a)) _).
    exact (tw_lmul_respects_r B (cmon_map g a :: nil) _ _ IH).
Qed.

Lemma tw_map_id@{+} {A : Ab@{u p}} (t : TWTerm A) :
  tw_map (@id Ab@{u p} A) t = t.
Proof.
  induction t as [ w | | s IHs t IHt | s IHs ]; cbn [tw_map].
  - f_equal. exact (map_id w).
  - reflexivity.
  - rewrite IHs, IHt. reflexivity.
  - rewrite IHs. reflexivity.
Qed.

Lemma tw_map_comp@{+} {A B C : Ab@{u p}} (g : B ~{Ab@{u p}}~> C)
  (f : A ~{Ab@{u p}}~> B) (t : TWTerm A) :
  tw_map (g ∘[Ab@{u p}] f) t = tw_map g (tw_map f t).
Proof.
  induction t as [ w | | s IHs t IHt | s IHs ]; cbn [tw_map].
  - f_equal. exact (eq_sym (map_map (cmon_map f) (cmon_map g) w)).
  - reflexivity.
  - rewrite IHs, IHt. reflexivity.
  - rewrite IHs. reflexivity.
Qed.

(* ⨁ₙ (−)^{⊗n}: T f is f^{⊗n} on each word, computing. / ⨁ₙ (−)^{⊗n}：T f 在每个单词上是 f^{⊗n}，正在计算。 *)
Definition TWF@{+} : Ab@{u p} ⟶ Ab@{u p}.
Proof.
  unshelve refine (@Build_Functor Ab@{u p} Ab@{u p} TWAb
                     (fun A B f => tw_map_hom f) _ _ _).
  - intros A B f g H t. simpl.
    induction t as [ w | | s IHs t IHt | s IHs ]; simpl.
    + exact (tw_word_pointwise f g H w).
    + apply tw_refl.
    + exact (twe_plus IHs IHt).
    + exact (twe_neg IHs).
  - intros A t. exact (tw_eq_of_eq (tw_map_id t)).
  - intros A B C g f t. exact (tw_eq_of_eq (tw_map_comp g f t)).
Defined.

Example TWF_obj@{+} (A : Ab@{u p}) : fobj[TWF] A = TWAb A := eq_refl.

Example TWF_map_word@{+} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (w : list (carrier (cmon_setoid A))) :
  cmon_map (fmap[TWF] f) (tw_word w) = tw_word (map (cmon_map f) w)
  := eq_refl.

(* T ≅ ⨁ₙ (−)^{⊗n}, naturally, with [T_TW_iso] as the components. / T ≅ ⨁ₙ (−)^{⊗n}，自然地，以 [T_TW_iso] 作为组成部分。 *)
Definition T_TW_natural@{+} : TF ≈ TWF.
Proof.
  exists (fun A => T_TW_iso A).
  intros A B f t. simpl.
  refine (fre_trans (T_map_relabel f t) _).
  refine (fre_trans (fre_sym (tw_from_to B
            (fr_eval (free_rng_ab_insert B ∘[Ab@{u p}] f) t))) _).
  rewrite (tw_to_relabel f t).
  apply fr_refl.
Defined.

Example T_TW_natural_component@{+} (A : Ab@{u p}) :
  projT1 T_TW_natural A = T_TW_iso A := eq_refl.

End Readings.

Arguments tw_map {A B} f t.

(* ------------------------------------------------------------------------ *)
(* * ** ⨁ₙ (−)^{⊗n} as a monad, directly, and T ≅ it as monads / * ** ⨁ₙ (−)^{⊗n} 作为一个幺半群，直接地，并且 T ≅ 它作为幺半群 *)

Section DirectMonad.

Universes u p.

(* The word product respects ≈ in each factor... / 乘积在每个因子中都尊重≈... *)
Lemma tw_prod_letter@{+} {A : Ab@{u p}} (u v : list (TWTerm A))
  (s s' : TWTerm A) :
  tw_eq A s s' → tw_eq A (tw_prod (u ++ s :: v)) (tw_prod (u ++ s' :: v)).
Proof.
  intro H. induction u as [ | c u IH ]; simpl app.
  - rewrite !tw_prod_cons. exact (tw_mul_respects_l A _ _ _ H).
  - rewrite !tw_prod_cons. exact (tw_mul_respects_r A _ _ _ IH).
Qed.

(* ...and is additive in each. / ...而且在每一个中都是可加的。 *)
Lemma tw_prod_lin@{+} {A : Ab@{u p}} (u v : list (TWTerm A))
  (s s' : TWTerm A) :
  tw_eq A (tw_prod (u ++ tw_plus s s' :: v))
          (tw_plus (tw_prod (u ++ s :: v)) (tw_prod (u ++ s' :: v))).
Proof.
  induction u as [ | c u IH ]; simpl app.
  - rewrite !tw_prod_cons. apply tw_refl.
  - rewrite !tw_prod_cons.
    refine (twe_trans (tw_mul_respects_r A _ _ _ IH) _).
    apply tw_mul_distr_l.
Qed.

(* So juxtaposition respects ≈, and μ is an arrow of Ab. / 因此，并置尊重 ≈，并且 μ 是 Ab 的一个箭头。 *)
Lemma tw_join_respects@{+} {A : Ab@{u p}} (s t : TWTerm (TWAb A)) :
  tw_eq (TWAb A) s t → tw_eq A (tw_join s) (tw_join t).
Proof.
  intro H.
  induction H as [ u v a b Hab | u v a b | s s' t t' _ IH1 _ IH2 | s s' _ IH
                 | s t u | s t | s | s | s t _ IH | s t u _ IH1 _ IH2 ];
    simpl.
  - exact (tw_prod_letter u v a b Hab).
  - exact (tw_prod_lin u v a b).
  - exact (twe_plus IH1 IH2).
  - exact (twe_neg IH).
  - apply twe_assoc.
  - apply twe_comm.
  - apply twe_zero_l.
  - apply twe_neg_l.
  - exact (twe_sym IH).
  - exact (twe_trans IH1 IH2).
Qed.

Definition tw_join_hom@{+} (A : Ab@{u p}) :
  TWAb (TWAb A) ~{Ab@{u p}}~> TWAb A.
Proof.
  unshelve refine (@Build_CMonHom (TWAb (TWAb A)) (TWAb A)
    (@Build_SetoidMorphism (TWTerm (TWAb A)) (tw_Setoid (TWAb A))
       (TWTerm A) (tw_Setoid A) tw_join _) _ _).
  - intros s t H. exact (tw_join_respects s t H).
  - apply tw_refl.
  - intros s t. apply tw_refl.
Defined.

(* The product of the one-letter words of w is w, LEIBNIZ... / w 的单字母词的乘积是 w，莱布尼茨... *)
Lemma tw_prod_letters@{+} {A : Ab@{u p}}
  (w : list (carrier (cmon_setoid A))) :
  tw_prod (map (fun a => @tw_word A (a :: nil)) w) = tw_word w.
Proof.
  induction w as [ | a w IH ]; [ reflexivity | ].
  cbn [map]. rewrite tw_prod_cons, IH. reflexivity.
Qed.

(* ...so μ ∘ T η = 1, LEIBNIZ. / ...所以 μ ∘ T η = 1，莱布尼茨。 *)
Lemma tw_join_letters@{+} {A : Ab@{u p}} (t : TWTerm A) :
  tw_join (tw_map (@tw_insert A) t) = t.
Proof.
  induction t as [ w | | s IHs t IHt | s IHs ]; cbn [tw_map tw_join].
  - exact (tw_prod_letters w).
  - reflexivity.
  - rewrite IHs, IHt. reflexivity.
  - rewrite IHs. reflexivity.
Qed.

(* The letterwise map commutes with the word product, LEIBNIZ... / 字母映射与词乘法交换，LEIBNIZ... *)
Lemma tw_prod_map@{+} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (ws : list (TWTerm A)) :
  tw_prod (map (tw_map f) ws) = tw_map f (tw_prod ws).
Proof.
  induction ws as [ | s ws IH ]; [ reflexivity | ].
  simpl map. rewrite !tw_prod_cons, IH. symmetry. apply tw_map_mul.
Qed.

(* ...so μ is natural, LEIBNIZ. / ...所以 μ 是自然的，莱布尼茨。 *)
Lemma tw_join_natural@{+} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (t : TWTerm (TWAb A)) :
  tw_join (tw_map (tw_map_hom f) t) = tw_map f (tw_join t).
Proof.
  induction t as [ ws | | s IHs t IHt | s IHs ]; cbn [tw_map tw_join].
  - exact (tw_prod_map f ws).
  - reflexivity.
  - rewrite IHs, IHt. reflexivity.
  - rewrite IHs. reflexivity.
Qed.

(* Juxtaposing a product of words of words is the product of the juxtapositions, at ≈. / 将词语的产物并置就是并置的产物，大约在 ≈。 *)
Lemma tw_join_prod@{+} {A : Ab@{u p}} (ws : list (TWTerm (TWAb A))) :
  tw_eq A (tw_join (tw_prod ws)) (tw_prod (map tw_join ws)).
Proof.
  induction ws as [ | s ws IH ]; [ apply tw_refl | ].
  simpl map. rewrite (@tw_prod_cons (TWAb A)), (@tw_prod_cons A).
  refine (twe_trans (tw_join_mul s (tw_prod ws)) _).
  exact (tw_mul_respects_r A _ _ _ IH).
Qed.

(*
 Mac Lane's direct description, "like that in the text for W": η the
 one-letter word, μ the juxtaposition of a word of words, the laws
 proved by induction on terms without the adjunction. 

 --------
 麦克·莱恩的直接描述，“就像 W 文本中的那样”：η 是单字，μ 是词的并置，通过对不带附加项的项进行归纳证明的定律。
*)
Definition TWMonad@{+} : @Monad Ab@{u p} TWF.
Proof.
  unshelve refine (@Build_Monad Ab@{u p} TWF (fun A => @tw_insert A)
                     (fun A => tw_join_hom A) _ _ _ _ _).
  - (* η natural, by conversion / η 自然，通过转换 *)
    intros A B f a. apply tw_refl.
  - (* μ ∘ T μ ≈ μ ∘ μ T *)
    intros A t. simpl.
    induction t as [ ws | | s IHs t IHt | s IHs ]; simpl.
    + apply twe_sym. apply tw_join_prod.
    + apply tw_refl.
    + exact (twe_plus IHs IHt).
    + exact (twe_neg IHs).
  - (* μ ∘ T η ≈ 1 *)
    intros A t. exact (tw_eq_of_eq (tw_join_letters t)).
  - (* μ ∘ η T ≈ 1, by conversion / μ ∘ η T ≈ 1，由转换得出 *)
    intros A t. apply tw_refl.
  - (* μ natural *)
    intros A B f t. exact (tw_eq_of_eq (tw_join_natural f t)).
Defined.

(*
 η IS the insertion of one-letter words, as the whole record; μ IS
 juxtaposition, on a word of words the product of the inner words; and
 μ ∘ η T = 1 on the nose. 

 --------
 η 是单字词的插入，就像整个记录一样；μ 是并列，作用于多字词上的内在词的产物；并且 μ ∘ η T = 1 完全正确。
*)
Example TWMonad_ret@{+} (A : Ab@{u p}) :
  @ret _ _ TWMonad A = @tw_insert A := eq_refl.

Example TWMonad_join@{+} (A : Ab@{u p}) (t : TWTerm (TWAb A)) :
  cmon_map (@join _ _ TWMonad A) t = tw_join t := eq_refl.

Example TWMonad_join_word@{+} (A : Ab@{u p}) (ws : list (TWTerm A)) :
  cmon_map (@join _ _ TWMonad A) (@tw_word (TWAb A) ws) = tw_prod ws
  := eq_refl.

Example TWMonad_join_ret@{+} (A : Ab@{u p}) (t : TWTerm A) :
  cmon_map (@join _ _ TWMonad A)
    (cmon_map (@ret _ _ TWMonad (fobj[TWF] A)) t) = t := eq_refl.

(* The components [to (T_TW_iso A)] of (a), natural by [T_TW_map]... / (a) 的组成部分 [to (T_TW_iso A)]，自然由 [T_TW_map] … *)
Definition T_TW_transform@{+} : TF ⟹ TWF.
Proof.
  unshelve refine (@Build_Transform Ab@{u p} Ab@{u p} TF TWF
                     (fun A => to (T_TW_iso A)) _ _).
  - intros A B f t. simpl. apply twe_sym. exact (T_TW_map f t).
  - intros A B f t. simpl. exact (T_TW_map f t).
Defined.

(*
 ...form a morphism of monads T → TWMonad (Monad/Morphism.v's
 [MonadHom]): the unit law by conversion, the multiplication law from
 [T_TW_join], [T_TW_map] and [tw_join_respects]. 

 --------
 ...形成一个单子范畴 T → TWMonad (Monad/Morphism.v 的 [MonadHom])：单位律通过转换，乘法律由 [T_TW_join]、[T_TW_map] 和 [tw_join_respects] 得出。
*)
Definition T_TW_monad_hom@{+} : MonadHom TM TWMonad.
Proof.
  unshelve refine {| mh_transform := T_TW_transform |}.
  - intros A a. apply tw_refl.
  - intros A t. simpl.
    refine (twe_trans (T_TW_join t) _).
    apply tw_join_respects.
    apply twe_sym. exact (T_TW_map (to (T_TW_iso A)) t).
Defined.

Example T_TW_monad_hom_component@{+} (A : Ab@{u p}) :
  transform[mh_transform T_TW_monad_hom] A = to (T_TW_iso A) := eq_refl.

(* The inverse components [from (T_TW_iso A)] are natural, inverting a natural family... / 逆分量 [from (T_TW_iso A)] 是自然的，它反转一个自然族… *)
Lemma TW_T_natural@{+} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (t : TWTerm A) :
  fr_eq (cmon_map (fmap[TF] f) (cmon_map (from (T_TW_iso A)) t))
        (cmon_map (from (T_TW_iso B)) (tw_map f t)).
Proof.
  refine (fre_trans (fre_sym (tw_from_to B _)) _).
  refine (fre_trans (tw_to_fr_respects B _ _ (T_TW_map f (tw_to_fr t))) _).
  exact (tw_to_fr_respects B _ _
           (tw_map_respects f _ _ (tw_eq_of_eq (tw_to_from A t)))).
Qed.

Definition TW_T_transform@{+} : TWF ⟹ TF.
Proof.
  unshelve refine (@Build_Transform Ab@{u p} Ab@{u p} TWF TF
                     (fun A => from (T_TW_iso A)) _ _).
  - intros A B f t. exact (TW_T_natural f t).
  - intros A B f t. exact (fre_sym (TW_T_natural f t)).
Defined.

(*
 ...and the product of a word, sent to T, is μ of its word of images, so
 they form a morphism of monads TWMonad → T. 

 --------
 ...并且一个词发送到 T 的结果是其图像词的 μ，因此它们形成了一个单子的态射 TWMonad → T。
*)
Lemma tw_to_fr_prod@{+} {A : Ab@{u p}} (ws : list (TWTerm A)) :
  fr_eq (tw_to_fr (tw_prod ws))
        (fr_eval (@id Ab@{u p} (fobj[TF] A))
                 (@fr_word (fobj[TF] A) (map tw_to_fr ws))).
Proof.
  induction ws as [ | s ws IH ]; [ apply fr_refl | ].
  rewrite tw_prod_cons.
  refine (fre_trans (tw_to_fr_mul A _ _) _).
  refine (fre_trans (fre_mul (fr_refl _) IH) _).
  exact (fre_sym (fr_eval_respects (FreeRngAb A)
                    (@id Ab@{u p} (fobj[TF] A)) _ _
                    (fr_word_cons (fobj[TF] A) (tw_to_fr s)
                       (map tw_to_fr ws)))).
Qed.

Definition TW_T_monad_hom@{+} : MonadHom TWMonad TM.
Proof.
  unshelve refine {| mh_transform := TW_T_transform |}.
  - intros A a. apply fr_refl.
  - intros A t. simpl.
    induction t as [ ws | | s IHs t IHt | s IHs ]; simpl.
    + exact (tw_to_fr_prod ws).
    + apply fr_refl.
    + exact (fre_plus IHs IHt).
    + exact (fre_neg IHs).
Defined.

Example TW_T_monad_hom_component@{+} (A : Ab@{u p}) :
  transform[mh_transform TW_T_monad_hom] A = from (T_TW_iso A) := eq_refl.

(*
 T ≅ ⨁ₙ (−)^{⊗n} AS MONADS: the two morphisms are inverse in
 Monad/Morphism.v's category [Monads Ab] of monads on Ab. 

 --------
 T ≅ ⨁ₙ (−)^{⊗n} 作为单子：这两个态射在 Ab 上的单子范畴 Monad/Morphism.v 的类别 [Monads Ab] 中是互逆的。
*)
Definition T_TW_monad_iso@{+} :
  @Isomorphism (Monads Ab@{u p}) (existT _ TF TM) (existT _ TWF TWMonad).
Proof.
  unshelve refine (@Build_Isomorphism (Monads Ab@{u p})
                     (existT _ TF TM) (existT _ TWF TWMonad)
                     T_TW_monad_hom TW_T_monad_hom _ _).
  - intros A t. simpl. exact (tw_eq_of_eq (tw_to_from A t)).
  - intros A t. simpl. exact (tw_from_to A t).
Defined.

Example T_TW_monad_iso_to@{+} : to T_TW_monad_iso = T_TW_monad_hom
  := eq_refl.

Example T_TW_monad_iso_from@{+} : from T_TW_monad_iso = TW_T_monad_hom
  := eq_refl.

End DirectMonad.
