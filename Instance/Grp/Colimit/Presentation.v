Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Product.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Coequalizer.
Require Import Category.Adjunction.Diagonal.Coproduct.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cocartesian.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.Grp.Pushout.
Require Import Category.Instance.Grp.Colimit.

Generalizable All Variables.

(* * * The free product of groups as a coequalizer of free groups / * * 群的自由积作为自由群的等化子 *)

(*
 nLab:      https://ncatlab.org/nlab/show/free+product
 nLab:      https://ncatlab.org/nlab/show/monadic+adjunction
 nLab:      https://ncatlab.org/nlab/show/coequalizer
 Wikipedia: https://en.wikipedia.org/wiki/Free_product

 Riehl, “Category Theory in Context”, 2nd ed., §5.6, the unnumbered
 construction of the free product of groups (printed pp. 212–213, PDF
 pp. 232–233).  The forgetful functor U : Group → Set does not preserve
 coproducts, so the free product G * H cannot be computed on underlying
 sets, and Riehl works relative to the free-forgetful adjunction F ⊣ U
 instead.  The free group F(UG + UH) on the disjoint union of the two
 carriers is a first approximation, and the relations the two group
 operations impose are encoded by a parallel pair of homomorphisms

 l, r : F(UFUG + UFUH) ⇉ F(UG + UH),

 l being F applied to the disjoint union Uε_G + Uε_H of the counit
 components, and r being F of the canonical comparison
 [UF inl, UF inr] : UFUG + UFUH → UF(UG + UH) (Exercise 3.4.i, printed
 p. 108, PDF p. 128) followed by the counit at F(UG + UH).  The free
 product is the coequalizer of that pair.  Read on one letter: the letter
 [inl w], for w a word in the elements of G, goes under l to the
 one-letter word on the VALUE of w in G, and under r to the word w itself
 with every letter tagged [inl] ([Grp_riehl_l_inl], [Grp_riehl_r_inl]).
 Coequalizing l and r therefore makes the tagged letters of each factor
 multiply as they do in that factor.

 Instance/Grp/Colimit.v obtains the same coproduct from the adjoint
 functor theorem, applied at the diagonal as Instance/Grp/FreeAFT.v
 applies it at the forgetful functor, and Instance/Grp/Pushout.v builds
 it from words and relations.  This file builds Riehl's pair, proves her
 claim in both directions, and compares the result with both.

 ** WHAT IS BUILT

 (a) The canonical presentation of one group.
 [Grp_canonical_presentation]: ε_G : FUG → G is a coequalizer of ε_{FUG}
 and FUε_G.  This is Riehl's Proposition 5.4.2 (printed p. 198, PDF
 p. 218) read at the free-group adjunction and stated upstairs in [Grp].
 The cofork is counit naturality, Theory/Adjunction.v's [counit_comp]
 (Monad/Monadicity/Crude.v's [crude_unit_cofork] is the same equation).
 A coforking k descends to k on one-letter words ([Grp_canonical_desc]).
 That map is a homomorphism because the cofork, evaluated at the
 one-letter word whose single letter is the word [g][g'], identifies
 k([g][g']) with k([gg']).  Uniqueness is proved on elements.  No
 monadicity theorem and no split coequalizer in [Sets] is used: every
 step is Instance/Grp/Free.v's [free_group_counit_generator],
 [free_group_fmap_generators] or [free_grp_extend_unique], the last
 packaged here as [Grp_free_hom_ext] (two homomorphisms out of a free
 group that agree on the letters agree).

 (b) The pair and the transpose.  [Grp_riehl_comparison] is Riehl's
 comparison, and [Grp_riehl_l] and [Grp_riehl_r] are the two legs.
 [Grp_riehl_transpose f1 f2] is the transpose across
 [free_group_adjunction] of the copairing in [Sets] of the underlying
 maps of f1 : G → z and f2 : H → z.  [Grp_riehl_e CC] is the transpose of
 the two injections of a coproduct structure CC, that is Riehl's
 e : F(UG + UH) → G + H.  Every such transpose coforks the pair
 ([Grp_riehl_transpose_cofork]).

 (c) Riehl's claim in both directions, at every coproduct structure.
 - [Grp_coproduct_is_coequalizer CC]: for ANY [Cocartesian] structure
 CC on [Grp], (G +_CC H, e) is a coequalizer of (l, r).  A coforking
 k, restricted along F(inl), coforks G's canonical presentation
 ([Grp_riehl_kG_cofork]), which descends it to G ([Grp_riehl_uG]).
 The same holds for H, and the mediator is the copairing of the two
 descents ([Grp_riehl_desc]).
 - [Grp_Cocartesian_of_coequalizers HC]: conversely, for ANY choice HC
 of coequalizers in [Grp], the coequalizer of (l, r) IS a binary
 coproduct.  Its injections [Grp_riehl_inl] / [Grp_riehl_inr] are e
 restricted to each factor's words and descended through that
 factor's canonical presentation, and its copairing is
 [Grp_riehl_merge].  This is the construction in the direction Riehl
 runs it: the free product DEFINED as the coequalizer.

 (d) Agreement with the adjoint functor theorem.
 - [Grp_free_product_is_coequalizer] is (c) at Instance/Grp/Colimit.v's
 [Grp_Cocartesian_via_GAFT], passed explicitly.  The free product the
 theorem produces is the coequalizer of Riehl's pair, with Riehl's e.
 - [Grp_Cocartesian_via_riehl] is (c)'s converse run on
 Instance/Grp/Colimit.v's [Grp_HasCoequalizers_via_GAFT].  Its
 coproduct object IS, by [eq_refl], the apex of the coequalizer the
 theorem returns for (l, r) ([Grp_Cocartesian_via_riehl_obj]).
 - [Grp_free_product_coequalizer_agrees]: that apex is isomorphic to the
 theorem's coproduct G + H.  The isomorphism is compatible with the
 coequalizing maps ([Grp_free_product_coequalizer_agrees_e]:
 to ∘ e_coeq ≈ e) and carries Riehl's injections to the theorem's
 ([Grp_free_product_coequalizer_agrees_inl], [_inr]).
 [Grp_riehl_coproduct_agrees] is the functor-level statement: the two
 coproduct bifunctors agree up to natural isomorphism, by
 Theory/Adjunction.v's [left_adjoint_iso].
 - Composing with Instance/Grp/Colimit.v's [Grp_free_product_iso]
 carries the same apex to Instance/Grp/Pushout.v's words-based free
 product ([Grp_free_product_coequalizer_agrees_words], with [_e],
 [_inl] and [_inr]).  [Grp_free_product_words_is_coequalizer] is (c)
 at Pushout.v's [Grp_Cocartesian] directly, the reading of Riehl's
 construction that uses no adjoint functor theorem at all.

 ** INSTANCE DISCIPLINE

 Instance/Grp/Pushout.v's [Grp_Cocartesian] and
 Instance/Sets/Cocartesian.v's [Sets_Cocartesian] are both [#[export]],
 and both are imported here.  Every [Coprod], [inl], [inr], [merge] and
 [cover] below names its [Cocartesian] argument explicitly, so no
 statement that says “via the adjoint functor theorem” can resolve to the
 words-based instance.  Nothing here is registered as an [Instance].

 ** A TRANSPARENT TWIN OF [coequalizer_unique]

 Structure/Coequalizer.v's [coequalizer_unique] ends in [Qed] ([About]
 reports it opaque), so the isomorphism it returns cannot be shown to
 carry one coequalizing map to the other.  [coequalizer_unique_along]
 repeats its construction and ends in [Defined], and
 [coequalizer_unique_along_e] records to ∘ e1 ≈ e2.  It is generic in the
 category and belongs in Structure/Coequalizer.v; it is here only because
 it was written for this file's comparison and moving it would touch
 Structure/Coequalizer.v, and it is a merge candidate rather than
 a removal candidate.  It is not an exact copy: [About] shows it carries
 one universe more than the original, with [u0 < u1], a bound the [Qed]
 original's statement does not expose.

 ** STRENGTHS, STRICTEST FIRST

 Two readbacks hold by [eq_refl]: [Grp_Cocartesian_via_riehl_obj] (the
 coproduct object IS the apex of the theorem's coequalizer) and
 [Grp_riehl_inl_is_restriction] (the injection IS e at the image of a
 one-letter word under F(inl)).  Everything else is `≈` or `≅`.  The
 counit does not compute, and neither does [FreeGrp] on arrows, since
 both are defined by universal factorization (Instance/Grp/Free.v's
 comments above [free_group_counit] and [free_group_fmap_generators]),
 so each letter-level fact
 ([Grp_riehl_l_inl], [Grp_riehl_r_inl], [Grp_riehl_transpose_generator])
 is `≈`.  [GAFT] is opaque ([About]), so nothing about the theorem's
 coproduct or coequalizer computes, and every agreement in (d) is an
 isomorphism carried as data, with `≈` equations about it.

 ** UNIVERSES, MEASURED

 Measured by [About] under [Set Printing Universes], with the bounds on
 stdlib globals, and the local strict bounds not named below, dropped.
 [Grp_riehl_l], [Grp_riehl_r], [Grp_riehl_e] and
 [Grp_coproduct_is_coequalizer] live over [Grp@{u p}] with [Set < u] and
 [p < u] and NO lower bound on the carrier [p].
 [Grp_canonical_presentation] takes G : obj[Grp@{u1 u}] with [Set < u1]
 and [u < u1], again with no lower bound on the carrier [u].  The
 theorem-level constants of parts (c) and (d) are declared [@{u p +}] so
 that their first two universes are [Grp]'s; [Grp_canonical_presentation]
 carries no annotation, which is why its readback names [Grp]'s
 universes [u1 u].  [Grp_Cocartesian_of_coequalizers] is
 [HasCoequalizers@{u p} Grp@{u p} → @Cocartesian Grp@{u p}] with
 [Set < u] and [p < u], and [Grp_free_product_words_is_coequalizer] is
 over [Grp@{u p}] with the same two bounds.  Riehl's construction
 therefore holds at [Set] carriers too.
 [Grp_free_product_is_coequalizer], [Grp_Cocartesian_via_riehl] and every
 [_agrees] constant in (d) add [Set < p] and [p < eq_rect_r.u0].  Both
 bounds are inherited from [Grp_Cocartesian_via_GAFT] and
 [Grp_HasCoequalizers_via_GAFT], whose own readbacks carry them.  The
 side condition is the adjoint functor theorem's, not Riehl's.

 One trap is recorded.  The non-vacuity lemmas below were first written
 with no binders, and [About] read [Grp_riehl_pair_nontrivial] back at
 [Z2@{Set}] and [Grp_riehl_e_not_monic] over [@Cocartesian Grp@{u2 Set}].
 At [Set] carriers they could never meet the adjoint functor theorem's
 [Set < carrier].  They now sit in a section declaring [u p], and they
 read back at [Z2@{p}] over [Grp@{u p}] with no LOWER bound on [p] (no
 [Set < p]), [p] sitting strictly below the hom universe of [Sets].

 ** NON-VACUITY

 [Grp_riehl_pair_nontrivial]: at G = H = Z/2 (Instance/Grp.v's [Z2]),
 l ≉ r.  Take w to be the word [1][1].  The homomorphism
 F(UZ2 + UZ2) → Z2 that sends every letter to 1 takes l([inl w]) to 1 and
 r([inl w]) to 1 + 1 = 0.  Hence [Grp_riehl_e_not_monic]: at every
 coproduct structure, e at Z/2, Z/2 is not monic, so the coequalizer
 genuinely quotients.  [Grp_free_product_coequalizer_nontrivial] states
 this at the adjoint functor theorem's coproduct, above [Set].

 ** AXIOMS

 Every constant of this file reports “Closed under the global context”
 when queried by its fully qualified name.  The file uses no [Program],
 so it has no obligations.

 ** NOT DELIVERED

 Riehl's general statement is issue #1009 and is not here: the same
 construction for any monadic U : A → C over a cocomplete C, Proposition
 5.6.11 (printed p. 213, PDF p. 233), and Exercise 5.6.iii (printed
 p. 217, PDF p. 237).  Everything here is at the free-group adjunction
 and is proved on letters.  Proposition 5.4.2 in general, the canonical
 presentation of an algebra over an arbitrary monad, is not here either;
 [Grp_canonical_presentation] is its [Grp] instance only.  Free products
 are binary only; there are no I-indexed ones.

 The tree contains no choice of coequalizers in [Grp] independent of the
 adjoint functor theorem (one could be built from the normal closure of
 the image of f · g⁻¹, which is not yet here).
 [Grp_Cocartesian_of_coequalizers] takes [HasCoequalizers Grp]
 as a hypothesis, and its one inhabitant in the tree is
 [Grp_HasCoequalizers_via_GAFT] (measured by [grep -rn HasCoequalizers]
 over the [.v] files, keeping the hits that mention groups).
 Instance/Grp/Quotient/Colimit.v coequalizes pairs of the form (f, 0)
 only ([normal_closure_IsCoequalizer]), and it is not applied to Riehl's
 pair here.  So “without the adjoint functor theorem” holds only for
 [Grp_free_product_words_is_coequalizer], which starts from Pushout.v's
 words.  There is no element-level description of the coequalizer: no
 reduced words and no normal form. 

 --------
 nLab:       https://ncatlab.org/nlab/show/free+product 
 nLab:       https://ncatlab.org/nlab/show/monadic+adjunction 
 nLab:       https://ncatlab.org/nlab/show/coequalizer 
 Wikipedia:  https://en.wikipedia.org/wiki/Free_product 

 Riehl，《上下文中的范畴论》，第2版，第5.6节，自由积群的未编号构造（印刷本第212–213页，PDF第232–233页）。忘却函子 U : Group → Set 不保持余积，因此自由积 G * H 不能在底层集合上计算，Riehl 改为相对于自由-忘却伴随 F ⊣ U 来处理。对于两个载体的析取并集所生成的自由群 F(UG + UH) 是一个初步近似，并且两个群运算施加的关系由一对平行同态 

 l, r : F(UFUG + UFUH) ⇉ F(UG + UH),l 是 F 作用于余单位分量的不相交并集 Uε_G + Uε_H，而 r 是 F 作用于规范比较 [UF inl, UF inr] : UFUG + UFUH → UF(UG + UH)（练习 3.4.i，印刷页 108，PDF 页 128），随后是 F(UG + UH) 的余单位。自由积是这一对的共等化器。读作一个字母：字母 [inl w]，对于 G 中元素的一个词 w，通过 l 变为 G 中 w 的值的单字母词，通过 r 变为 w 本身的词，每个字母都带有标签 [inl]（[Grp_riehl_l_inl]，[Grp_riehl_r_inl]）。因此，对 l 和 r 进行共等化会使每个因子的标记字母按照它们在该因子中的乘法进行相乘。Instance/Grp/Colimit.v 从伴随函子定理获得相同的余积，该定理在对角线上应用，正如 Instance/Grp/FreeAFT.v 在忘记函子上应用它一样，而 Instance/Grp/Pushout.v 则从词和关系构建它。此文件构建了 Riehl 的对，并证明了她的主张的正反两个方向，并将结果与两者进行比较。

 ** 构建内容（a） 一个群的典范表示。[Grp_canonical_presentation] ： ε_G ： FUG → G 是 ε_{FUG} 的协等化子
 以及FUε_G。这就是里尔的命题5.4.2（印刷版第198页，PDF）
 第218页）在自由群伴随处读到，并在[Grp] 中上层陈述。余分叉是余单位自然性，Theory/Adjunction.v 的说法[counit_comp]
 （Monad/Monadicity/Crude.v 的[crude_unit_cofork]是相同的方程。）一个余分叉的 k 在单个字母单词（[Grp_canonical_desc]）上下降到 k。该映射是同态，因为在
 单个字母单词，其单字母为单词[g] [g']，识别
 k（ [g] [g'] ） 与 k（ [gg'] ）。唯一性在元素上被证明。没有在 [Sets] 中使用幺半群定理或分裂共等化器：每一步都是 Instance/Grp/Free.v 的 [free_group_counit_generator]、[free_group_fmap_generators] 或 [free_grp_extend_unique]，最后在此打包为 [Grp_free_hom_ext]（来自自由群的两个同态在字母上相同则一致）。

 (b) 对和转置。[Grp_riehl_comparison] 是 Riehl 的比较，[Grp_riehl_l] 和 [Grp_riehl_r] 是两个分支。[Grp_riehl_transpose f1 f2] 是 [Sets] 中 f1 : G → z 和 f2 : H → z 的底层映射的共配对在 [free_group_adjunction] 上的转置。[Grp_riehl_e CC] 是一个余积结构 CC 的两个注入的转置，即 Riehl 的 e : F(UG + UH) → G + H。每个这样的转置都会构成 ([Grp_riehl_transpose_cofork]) 的对的共岔。(c) Riehl 在每一个积结构下对两个方向的断言。- [Grp_coproduct_is_coequalizer CC]：对于任何 [Cocartesian] 结构 CC 在 [Grp] 上，(G +_CC H, e) 是 (l, r) 的一个余等化器。沿 F(inl) 限制的共分叉 k 共分叉 G 的标准表示 ([Grp_riehl_kG_cofork])，将其下降到 G ([Grp_riehl_uG])。H 也同样适用，且中介者是两个下降映射的共配对 ([Grp_riehl_desc])。- [Grp_Cocartesian_of_coequalizers HC]：反之，对于 [Grp] 中任何选择的余等化器 HC，(l, r) 的余等化器是一个二元积。它的注入 [Grp_riehl_inl] / [Grp_riehl_inr] 是 e 限制到每个因子的元素，然后通过该因子的标准表示下降，其共配对是 [Grp_riehl_merge]。这是 Riehl 所采用的构造方向：定义为余等化子的自由积。(d) 与伴随函子定理的一致性。- [Grp_free_product_is_coequalizer] 是 Instance/Grp/Colimit.v 的 [Grp_Cocartesian_via_GAFT] 上的 (c)，显式传递。该定理生成的自由积是 Riehl 对的共同化等化器，伴随 Riehl 的 e。- [Grp_Cocartesian_via_riehl] 是在 Instance/Grp/Colimit.v 的 [Grp_HasCoequalizers_via_GAFT] 上运行 (c) 的逆命题。根据 [eq_refl]，它的余积对象是定理返回的 (l, r) ([Grp_Cocartesian_via_riehl_obj]) 的共同化等化器的顶点。- [Grp_free_product_coequalizer_agrees]：该顶点同构于定理中的余积 G + H。该同构与共同化等化映射 ([Grp_free_product_coequalizer_agrees_e]：to ∘ e_coeq ≈ e) 兼容，并将 Riehl 的注入映射到定理的映射 ([Grp_free_product_coequalizer_agrees_inl], [_inr])。[Grp_riehl_coproduct_agrees] 是函子级别的声明：两个余积双函子在自然同构下是一致的，由 Theory/Adjunction.v 的 [left_adjoint_iso] 给出。- 与 Instance/Grp/Colimit.v 的 [Grp_free_product_iso] 组合会将相同的顶点传递到 Instance/Grp/Pushout.v 的基于词的自由积（[Grp_free_product_coequalizer_agrees_words]，具有 [_e]、[_inl] 和 [_inr]）。[Grp_free_product_words_is_coequalizer] 在 Pushout.v 的 [Grp_Cocartesian] 处直接为（c），这是 Riehl 的构造的读法，完全不使用伴随函子定理。

 ** 实例纪律Instance/Grp/Pushout.v 的 [Grp_Cocartesian] 和 Instance/Sets/Cocartesian.v 的 [Sets_Cocartesian] 都是 [#[export]，且两者都在此处导入。以下的每个 [Coprod]、[inl]、[inr]、[merge] 和 [cover] 都明确命名其 [Cocartesian] 参数，因此没有任何一条说“通过伴随函子定理”的声明能够解析为基于单词的实例。这里没有任何内容被注册为 [Instance]。

 ** [coequalizer_unique] 的透明双生Structure/Coequalizer.v 的 [coequalizer_unique] 以 [Qed] 结束（[About] 报告它是不可见的），因此它返回的同构无法证明会将一个共等化映射带到另一个映射。[coequalizer_unique_along] 重复其构造并以 [Defined] 结束，[coequalizer_unique_along_e] 记录到 ∘ e1 ≈ e2。它在该范畴中是通用的，属于 Structure/Coequalizer.v；它出现在这里仅是因为它是为这个文件的比较而写的，并且移动它会涉及 Structure/Coequalizer.v，它是一个合并候选而不是删除候选。它不是精确的副本：[About] 显示它比原始的携带了一个额外的 universe，[u0 < u1] 是原始 [Qed] 声明未暴露的界限。

 ** 优点，严格性由高到低由 [eq_refl] 保持的两个回读：[Grp_Cocartesian_via_riehl_obj]（余积对象是定理的余等化子的顶点）和 [Grp_riehl_inl_is_restriction]（注入是 e，在 F(inl) 下的一个字母单词的像）。其他所有的都是 `≈` 或 `≅`。余单位无法计算，箭头上的 [FreeGrp] 也无法计算，因为两者都由泛性质分解定义（Instance/Grp/Free.v 中 [free_group_counit] 和 [free_group_fmap_generators] 以上的注释），因此每个字母级别的事实（[Grp_riehl_l_inl]、[Grp_riehl_r_inl]、[Grp_riehl_transpose_generator]）都为 `≈`。[GAFT] 是不透明的（[About]），所以关于定理的余积或余等化子没有任何计算，每个 (d) 中的一致性都是作为数据携带的同构，并附有 `≈` 方程。

 ** 宇宙，测量根据 [About] 在 [Set Printing Universes] 下测量，同时对 stdlib 全局变量的界限以及未在下文命名的本地严格界限被删除。[Grp_riehl_l]、[Grp_riehl_r]、[Grp_riehl_e] 和 [Grp_coproduct_is_coequalizer] 存在于 [Grp@{u p}] 上，具有 [Set < u] 和 [p < u]，并且载体 [p] 没有下界。[Grp_canonical_presentation] 接受 G : obj [Grp@{u1 u}]，带有 [Set < u1] 和 [u < u1]，同样载体 [u] 没有下界。(c) 和 (d) 部分的定理级常量被声明为 [@{u p +}]，以便它们的前两个宇宙是 [Grp] 的；[Grp_canonical_presentation] 没有标注，这就是为什么它的回读名称是 [Grp] 的宇宙 [u1 u]。[Grp_Cocartesian_of_coequalizers] 是 [HasCoequalizers@{u p} Grp@{u p} → @Cocartesian Grp@{u p}]，带有 [Set < u] 和 [p < u]，而 [Grp_free_product_words_is_coequalizer] 存在于 [Grp@{u p}] 上，具有相同的两个界限。Riehl 的构造因此也适用于 [Set] 载体。[Grp_free_product_is_coequalizer]、[Grp_Cocartesian_via_riehl] 以及 (d) 中的每个 [_agrees] 常量增加了 [Set < p] 和 [p < eq_rect_r.u0]。两个界限都继承自 [Grp_Cocartesian_via_GAFT] 和 [Grp_HasCoequalizers_via_GAFT]，它们自身的回读值也携带了这些界限。附加条件是伴随函子定理的，而不是 Riehl 的。

 记录了一个陷阱。下面的非空引理最初是写成没有绑定器的形式，[About] 在 [Z2@{Set}] 和 [Grp_riehl_e_not_monic] 上读取 [Grp_riehl_pair_nontrivial]。对于 [Set] 载体，它们永远无法满足伴随函子定理的 [Set < carrier]。它们现在位于声明 [u p] 的一节中，并在 [Grp@{u p}] 上以 [Z2@{p}] 回读，[p] 没有 LOWER 界限（没有 [Set < p]），[p] 严格位于 [Sets] 的同伦宇宙之下。** 非空性

 [Grp_riehl_pair_nontrivial]：在 G = H = Z/2（实例/Grp.v 的 [Z2]），
 l ≉ r。取 w 为字 [1] [1]。同态
 F(UZ2 + UZ2) → Z2，将每个字母映射为 1，将 l([inl w]) 映为 1，
 r([inl w]) 映为 1 + 1 = 0。因此 [Grp_riehl_e_not_monic]：在每个
 余积结构下，Z/2, Z/2 上的 e 不是单射，所以余等化器
 真正进行商化。[Grp_free_product_coequalizer_nontrivial] 在伴随函子定理的余积上这样陈述，见 [Set]。

 ** 公理

 本文件的每个常量在使用其完全限定名称查询时都会报告“在全局上下文下封闭”。
 该文件未使用任何 [Program]，因此它没有任何义务。

 ** 未交付Riehl 的一般性陈述是问题 #1009，这里没有：对于 cocomplete C 上的任何单元 U : A → C 的相同构造，见命题 5.6.11（印刷版第 213 页，PDF 第 233 页）以及练习 5.6.iii（印刷版第 217 页，PDF 第 237 页）。这里的所有内容都在自由群伴随下，并且是在字母上证明的。命题 5.4.2 一般情况下，即任意单子上的代数的规范表示，也不在这里；[Grp_canonical_presentation] 只是它的 [Grp] 实例。自由积仅限于二元；没有 I 索引的。该树在 [Grp] 中不包含独立于伴随函子定理的余等化的选择（可以从 f · g⁻¹ 的像的正规闭包构建一个，但这里尚未出现）。
 [Grp_Cocartesian_of_coequalizers] 以 [HasCoequalizers Grp] 作为假设，并且其在树中的唯一元素是 [Grp_HasCoequalizers_via_GAFT]（通过 [grep -rn HasCoequalizers] 在 [.v] 文件上进行测量，保留提到群的命中）。
 Instance/Grp/Quotient/Colimit.v 仅对形式为 (f, 0) 的对进行余等化（[normal_closure_IsCoequalizer]），并且它在这里未应用于 Riehl 的对。因此，“没有伴随函子定理”只适用于 [Grp_free_product_words_is_coequalizer]，它从 Pushout.v 的词开始。余等化没有元素级描述：没有简化词也没有标准形式。
*)

(* * ** Homomorphisms out of a free group are determined on the letters / * ** 自由群上的同态由其字母确定 *)

Lemma Grp_free_hom_ext {X : Sets} {K : Grp} (g1 g2 : FreeGrp X ~{Grp}~> K) :
  (∀ a, g1 (fg_insert X a) ≈ g2 (fg_insert X a)) → g1 ≈ g2.
Proof.
  intros Hg w.
  transitivity (free_grp_extend (fmap[Grp_Forget] g2 ∘ fg_insert X) w).
  - exact (free_grp_extend_unique X K
             (fmap[Grp_Forget] g2 ∘ fg_insert X) g1 Hg w).
  - symmetry.
    apply (free_grp_extend_unique X K _ g2).
    intro a; reflexivity.
Qed.

(* * ** The canonical presentation of one group / * ** 一个群体的规范展示 *)

Section Canonical.

Context (G : Grp).

Lemma Grp_canonical_cofork :
  free_group_counit G ∘ free_group_counit (FreeGrp (Grp_Forget G))
    ≈ free_group_counit G
        ∘ fmap[FreeGrp] (fmap[Grp_Forget] (free_group_counit G)).
Proof.
  symmetry.
  exact (@counit_comp _ _ _ _ free_group_adjunction _ _ (free_group_counit G)).
Qed.

Context {c : Grp} (k : FreeGrp (Grp_Forget G) ~{Grp}~> c).
Context (Hk : k ∘ free_group_counit (FreeGrp (Grp_Forget G))
                ≈ k ∘ fmap[FreeGrp] (fmap[Grp_Forget] (free_group_counit G))).

Definition Grp_canonical_desc : G ~{Grp}~> c.
Proof using Hk.
  unshelve refine (@Build_GrpHom' G c
                     (fmap[Grp_Forget] k ∘ fg_insert (Grp_Forget G)) _).
  intros g g'; simpl.
  set (w := grp_mul (FreeGrpObject (Grp_Forget G))
              (fg_insert (Grp_Forget G) g) (fg_insert (Grp_Forget G) g')).
  rewrite <- (grp_map_mul k).
  fold w.
  transitivity (grp_map k (free_group_counit (FreeGrp (Grp_Forget G))
                  (fg_insert (Grp_Forget (FreeGrp (Grp_Forget G))) w))).
  2: { apply (proper_morphism (grp_map k)).
       exact (free_group_counit_generator (FreeGrp (Grp_Forget G)) w). }
  transitivity (grp_map k
                  (fmap[FreeGrp] (fmap[Grp_Forget] (free_group_counit G))
                     (fg_insert (Grp_Forget (FreeGrp (Grp_Forget G))) w))).
  2: { symmetry. exact (Hk _). }
  apply (proper_morphism (grp_map k)).
  rewrite free_group_fmap_generators.
  apply (proper_morphism (fg_insert (Grp_Forget G))).
  simpl.
  unfold w.
  rewrite (grp_map_mul (free_group_counit G)).
  rewrite !free_group_counit_generator.
  reflexivity.
Defined.

Lemma Grp_canonical_desc_commutes :
  Grp_canonical_desc ∘ free_group_counit G ≈ k.
Proof.
  apply Grp_free_hom_ext; intro a; simpl.
  apply (proper_morphism (grp_map k)).
  apply (proper_morphism (fg_insert (Grp_Forget G))).
  exact (free_group_counit_generator G a).
Qed.

Lemma Grp_canonical_desc_unique (v : G ~{Grp}~> c) :
  v ∘ free_group_counit G ≈ k → Grp_canonical_desc ≈ v.
Proof.
  intros Hv g; simpl.
  rewrite <- (Hv (fg_insert (Grp_Forget G) g)); simpl.
  apply (proper_morphism (grp_map v)).
  exact (free_group_counit_generator G g).
Qed.

End Canonical.

Definition Grp_canonical_presentation (G : Grp) :
  IsCoequalizer (free_group_counit (FreeGrp (Grp_Forget G)))
                (fmap[FreeGrp] (fmap[Grp_Forget] (free_group_counit G)))
                G (free_group_counit G).
Proof.
  unshelve econstructor.
  - exact (Grp_canonical_cofork G).
  - intros c k Hk.
    exact {| unique_obj      := Grp_canonical_desc G k Hk;
             unique_property := Grp_canonical_desc_commutes G k Hk;
             uniqueness      := Grp_canonical_desc_unique G k Hk |}.
Defined.

(** ** Riehl's parallel pair / ** 赖尔的平行对 *)

Section RiehlPair.

Universes u p.
Context (G H : Grp@{u p}).

Local Notation UGH :=
  (@Coprod Sets Sets_Cocartesian (Grp_Forget G) (Grp_Forget H)).
Local Notation UFUGH :=
  (@Coprod Sets Sets_Cocartesian (Grp_Forget (FreeGrp (Grp_Forget G)))
                                 (Grp_Forget (FreeGrp (Grp_Forget H)))).
Local Notation inlS :=
  (@inl Sets Sets_Cocartesian (Grp_Forget G) (Grp_Forget H)).
Local Notation inrS :=
  (@inr Sets Sets_Cocartesian (Grp_Forget G) (Grp_Forget H)).

(* Riehl's “canonical comparison” [UF inl, UF inr] : UFUG + UFUH → UF(UG + UH) between the coproduct of the images and the image of the coproduct. / Riehl 的“典型比较” [UF inl, UF inr] ：UFUG + UFUH → UF(UG + UH) 在像的余积与余积的像之间。 *)
Definition Grp_riehl_comparison :
  UFUGH ~{Sets}~> Grp_Forget (FreeGrp UGH) :=
  @merge Sets Sets_Cocartesian _ _ _
    (fmap[Grp_Forget] (fmap[FreeGrp] inlS))
    (fmap[Grp_Forget] (fmap[FreeGrp] inrS)).

(* The leg F(Uε_G + Uε_H). / 腿 F(Uε_G + Uε_H)。 *)
Definition Grp_riehl_l : FreeGrp UFUGH ~{Grp@{u p}}~> FreeGrp UGH :=
  fmap[FreeGrp] (@cover Sets Sets_Cocartesian _ _ _ _
                   (fmap[Grp_Forget] (free_group_counit G))
                   (fmap[Grp_Forget] (free_group_counit H))).

(* The leg ε_{F(UG+UH)} ∘ F[UF inl, UF inr]. / 腿 ε_{F(UG+UH)} ∘ F [UF inl, UF inr] 。 *)
Definition Grp_riehl_r : FreeGrp UFUGH ~{Grp@{u p}}~> FreeGrp UGH :=
  free_group_counit (FreeGrp UGH) ∘ fmap[FreeGrp] Grp_riehl_comparison.

(*
 The transpose, across the free-forgetful adjunction, of the copairing in
 [Sets] of the underlying maps of two homomorphisms out of G and H. 

 --------
 通过自由遗忘伴随作用，在 [Sets] 中将两个来自 G 和 H 的同态的基础映射的共配对的转置。
*)
Definition Grp_riehl_transpose {z : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z) :
  FreeGrp UGH ~{Grp@{u p}}~> z :=
  from (@adj _ _ _ _ free_group_adjunction _ _)
    (@merge Sets Sets_Cocartesian _ _ _ (fmap[Grp_Forget] f1)
                                        (fmap[Grp_Forget] f2)).

(* Riehl's e : F(UG + UH) → G + H, the transpose of [U inl, U inr], at a coproduct structure that is passed EXPLICITLY. / Riehl 的 e : F(UG + UH) → G + H，是 [U inl, U inr] 的转置，位于一个明确传递的余积结构上。 *)
Definition Grp_riehl_e (CC : @Cocartesian Grp@{u p}) :
  FreeGrp UGH ~{Grp@{u p}}~> @Coprod Grp@{u p} CC G H :=
  Grp_riehl_transpose (@inl Grp@{u p} CC G H) (@inr Grp@{u p} CC G H).

(** *** What the maps do to a letter / *** 地图对字母的作用 *)

Lemma Grp_riehl_transpose_generator {z : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z) (s : UGH) :
  Grp_riehl_transpose f1 f2 (fg_insert UGH s)
    ≈ @merge Sets Sets_Cocartesian _ _ _ (fmap[Grp_Forget] f1)
                                         (fmap[Grp_Forget] f2) s.
Proof.
  pose proof (@from_adj_comp_law _ _ _ _ free_group_adjunction _ _
                (@merge Sets Sets_Cocartesian _ _ _ (fmap[Grp_Forget] f1)
                                                    (fmap[Grp_Forget] f2)))
    as Hc.
  rewrite (@to_adj_unit _ _ _ _ free_group_adjunction) in Hc.
  exact (Hc s).
Qed.

Lemma Grp_riehl_l_inl (w : FGWord (Grp_Forget G)) :
  Grp_riehl_l (fg_insert UFUGH (Datatypes.inl w))
    ≈ fg_insert UGH (Datatypes.inl (free_group_counit G w)).
Proof. exact (@free_group_fmap_generators UFUGH UGH _ (Datatypes.inl w)). Qed.

Lemma Grp_riehl_l_inr (w : FGWord (Grp_Forget H)) :
  Grp_riehl_l (fg_insert UFUGH (Datatypes.inr w))
    ≈ fg_insert UGH (Datatypes.inr (free_group_counit H w)).
Proof. exact (@free_group_fmap_generators UFUGH UGH _ (Datatypes.inr w)). Qed.

Lemma Grp_riehl_r_inl (w : FGWord (Grp_Forget G)) :
  Grp_riehl_r (fg_insert UFUGH (Datatypes.inl w)) ≈ fmap[FreeGrp] inlS w.
Proof.
  transitivity (free_group_counit (FreeGrp UGH)
                  (fg_insert _ (Grp_riehl_comparison (Datatypes.inl w)))).
  - apply (proper_morphism (grp_map (free_group_counit (FreeGrp UGH)))).
    exact (@free_group_fmap_generators UFUGH _ Grp_riehl_comparison
             (Datatypes.inl w)).
  - exact (free_group_counit_generator (FreeGrp UGH) _).
Qed.

Lemma Grp_riehl_r_inr (w : FGWord (Grp_Forget H)) :
  Grp_riehl_r (fg_insert UFUGH (Datatypes.inr w)) ≈ fmap[FreeGrp] inrS w.
Proof.
  transitivity (free_group_counit (FreeGrp UGH)
                  (fg_insert _ (Grp_riehl_comparison (Datatypes.inr w)))).
  - apply (proper_morphism (grp_map (free_group_counit (FreeGrp UGH)))).
    exact (@free_group_fmap_generators UFUGH _ Grp_riehl_comparison
             (Datatypes.inr w)).
  - exact (free_group_counit_generator (FreeGrp UGH) _).
Qed.

(* * *** The transpose on each factor, and the cofork / * *** 每个因子的转置，以及协叉 *)

Section Transpose.

Context {z : Grp@{u p}} (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z).

Lemma Grp_riehl_transpose_inl :
  Grp_riehl_transpose f1 f2 ∘ fmap[FreeGrp] inlS ≈ f1 ∘ free_group_counit G.
Proof.
  apply Grp_free_hom_ext; intro g.
  transitivity (Grp_riehl_transpose f1 f2 (fg_insert UGH (Datatypes.inl g))).
  - apply (proper_morphism (grp_map (Grp_riehl_transpose f1 f2))).
    exact (@free_group_fmap_generators _ UGH _ g).
  - rewrite (Grp_riehl_transpose_generator f1 f2 (Datatypes.inl g)).
    symmetry.
    apply (proper_morphism (grp_map f1)).
    exact (free_group_counit_generator G g).
Qed.

Lemma Grp_riehl_transpose_inr :
  Grp_riehl_transpose f1 f2 ∘ fmap[FreeGrp] inrS ≈ f2 ∘ free_group_counit H.
Proof.
  apply Grp_free_hom_ext; intro g.
  transitivity (Grp_riehl_transpose f1 f2 (fg_insert UGH (Datatypes.inr g))).
  - apply (proper_morphism (grp_map (Grp_riehl_transpose f1 f2))).
    exact (@free_group_fmap_generators _ UGH _ g).
  - rewrite (Grp_riehl_transpose_generator f1 f2 (Datatypes.inr g)).
    symmetry.
    apply (proper_morphism (grp_map f2)).
    exact (free_group_counit_generator H g).
Qed.

(* Every such transpose coforks the pair: on the letter [inl w] both legs come to f1 applied to the value of the word w in G. / 每一个这样的转置都对这一对进行共分叉：在字母 [inl w] 上，两条腿都应用于 G 中单词 w 的值的 f1。 *)
Lemma Grp_riehl_transpose_cofork :
  Grp_riehl_transpose f1 f2 ∘ Grp_riehl_l
    ≈ Grp_riehl_transpose f1 f2 ∘ Grp_riehl_r.
Proof.
  apply Grp_free_hom_ext; intros [w|w].
  - transitivity (Grp_riehl_transpose f1 f2
                    (fg_insert UGH (Datatypes.inl (free_group_counit G w)))).
    { apply (proper_morphism (grp_map (Grp_riehl_transpose f1 f2))).
      exact (Grp_riehl_l_inl w). }
    rewrite (Grp_riehl_transpose_generator f1 f2).
    transitivity (Grp_riehl_transpose f1 f2 (fmap[FreeGrp] inlS w)).
    { symmetry. exact (Grp_riehl_transpose_inl w). }
    apply (proper_morphism (grp_map (Grp_riehl_transpose f1 f2))).
    symmetry. exact (Grp_riehl_r_inl w).
  - transitivity (Grp_riehl_transpose f1 f2
                    (fg_insert UGH (Datatypes.inr (free_group_counit H w)))).
    { apply (proper_morphism (grp_map (Grp_riehl_transpose f1 f2))).
      exact (Grp_riehl_l_inr w). }
    rewrite (Grp_riehl_transpose_generator f1 f2).
    transitivity (Grp_riehl_transpose f1 f2 (fmap[FreeGrp] inrS w)).
    { symmetry. exact (Grp_riehl_transpose_inr w). }
    apply (proper_morphism (grp_map (Grp_riehl_transpose f1 f2))).
    symmetry. exact (Grp_riehl_r_inr w).
Qed.

End Transpose.

(* * *** A coforking map restricts to each factor / * *** 余分叉映射限制在每个因子上 *)

Section Factors.

Context {c : Grp@{u p}} (k : FreeGrp UGH ~{Grp@{u p}}~> c).
Context (Hk : k ∘ Grp_riehl_l ≈ k ∘ Grp_riehl_r).

(* The restriction of [k] to the words in each factor's letters. / [k] 对每个因子字母中的单词的限制。 *)
Definition Grp_riehl_kG : FreeGrp (Grp_Forget G) ~{Grp@{u p}}~> c :=
  k ∘ fmap[FreeGrp] inlS.

Definition Grp_riehl_kH : FreeGrp (Grp_Forget H) ~{Grp@{u p}}~> c :=
  k ∘ fmap[FreeGrp] inrS.

(* Each restriction coforks that factor's canonical presentation. / 每个限制都会共同分叉该因子的典型表示。 *)
Lemma Grp_riehl_kG_cofork :
  Grp_riehl_kG ∘ free_group_counit (FreeGrp (Grp_Forget G))
    ≈ Grp_riehl_kG ∘ fmap[FreeGrp] (fmap[Grp_Forget] (free_group_counit G)).
Proof using Hk.
  apply Grp_free_hom_ext; intro w.
  transitivity (k (fmap[FreeGrp] inlS w)).
  { apply (proper_morphism (grp_map Grp_riehl_kG)).
    exact (free_group_counit_generator (FreeGrp (Grp_Forget G)) w). }
  transitivity (k (Grp_riehl_r (fg_insert UFUGH (Datatypes.inl w)))).
  { apply (proper_morphism (grp_map k)).
    symmetry. exact (Grp_riehl_r_inl w). }
  transitivity (k (Grp_riehl_l (fg_insert UFUGH (Datatypes.inl w)))).
  { symmetry. exact (Hk _). }
  transitivity (k (fg_insert UGH (Datatypes.inl (free_group_counit G w)))).
  { apply (proper_morphism (grp_map k)).
    exact (Grp_riehl_l_inl w). }
  transitivity (Grp_riehl_kG
                  (fg_insert (Grp_Forget G) (free_group_counit G w))).
  { apply (proper_morphism (grp_map k)).
    symmetry. exact (@free_group_fmap_generators _ UGH _ _). }
  apply (proper_morphism (grp_map Grp_riehl_kG)).
  symmetry.
  exact (@free_group_fmap_generators _ _
           (fmap[Grp_Forget] (free_group_counit G)) w).
Qed.

Lemma Grp_riehl_kH_cofork :
  Grp_riehl_kH ∘ free_group_counit (FreeGrp (Grp_Forget H))
    ≈ Grp_riehl_kH ∘ fmap[FreeGrp] (fmap[Grp_Forget] (free_group_counit H)).
Proof using Hk.
  apply Grp_free_hom_ext; intro w.
  transitivity (k (fmap[FreeGrp] inrS w)).
  { apply (proper_morphism (grp_map Grp_riehl_kH)).
    exact (free_group_counit_generator (FreeGrp (Grp_Forget H)) w). }
  transitivity (k (Grp_riehl_r (fg_insert UFUGH (Datatypes.inr w)))).
  { apply (proper_morphism (grp_map k)).
    symmetry. exact (Grp_riehl_r_inr w). }
  transitivity (k (Grp_riehl_l (fg_insert UFUGH (Datatypes.inr w)))).
  { symmetry. exact (Hk _). }
  transitivity (k (fg_insert UGH (Datatypes.inr (free_group_counit H w)))).
  { apply (proper_morphism (grp_map k)).
    exact (Grp_riehl_l_inr w). }
  transitivity (Grp_riehl_kH
                  (fg_insert (Grp_Forget H) (free_group_counit H w))).
  { apply (proper_morphism (grp_map k)).
    symmetry. exact (@free_group_fmap_generators _ UGH _ _). }
  apply (proper_morphism (grp_map Grp_riehl_kH)).
  symmetry.
  exact (@free_group_fmap_generators _ _
           (fmap[Grp_Forget] (free_group_counit H)) w).
Qed.

(* The descents through the two canonical presentations. / 通过两个典型展示的下降。 *)
Definition Grp_riehl_uG : G ~{Grp@{u p}}~> c :=
  unique_obj (coeq_desc (Grp_canonical_presentation G)
                Grp_riehl_kG Grp_riehl_kG_cofork).

Definition Grp_riehl_uH : H ~{Grp@{u p}}~> c :=
  unique_obj (coeq_desc (Grp_canonical_presentation H)
                Grp_riehl_kH Grp_riehl_kH_cofork).

Lemma Grp_riehl_uG_counit :
  Grp_riehl_uG ∘ free_group_counit G ≈ Grp_riehl_kG.
Proof using Hk.
  exact (unique_property (coeq_desc (Grp_canonical_presentation G)
                            Grp_riehl_kG Grp_riehl_kG_cofork)).
Qed.

Lemma Grp_riehl_uH_counit :
  Grp_riehl_uH ∘ free_group_counit H ≈ Grp_riehl_kH.
Proof using Hk.
  exact (unique_property (coeq_desc (Grp_canonical_presentation H)
                            Grp_riehl_kH Grp_riehl_kH_cofork)).
Qed.

End Factors.

(* * *** Every coproduct of G and H is a coequalizer of the pair / * *** G 和 H 的每个余积都是该对的余等化子 *)

Section Descent.

Context (CC : @Cocartesian Grp@{u p}).
Context {c : Grp@{u p}} (k : FreeGrp UGH ~{Grp@{u p}}~> c).
Context (Hk : k ∘ Grp_riehl_l ≈ k ∘ Grp_riehl_r).

Definition Grp_riehl_desc : @Coprod Grp@{u p} CC G H ~{Grp@{u p}}~> c :=
  @merge Grp@{u p} CC _ _ _ (Grp_riehl_uG k Hk) (Grp_riehl_uH k Hk).

Lemma Grp_riehl_desc_commutes : Grp_riehl_desc ∘ Grp_riehl_e CC ≈ k.
Proof.
  apply Grp_free_hom_ext; intros [g|g].
  - transitivity (Grp_riehl_desc (@inl Grp@{u p} CC G H g)).
    { apply (proper_morphism (grp_map Grp_riehl_desc)).
      exact (Grp_riehl_transpose_generator _ _ (Datatypes.inl g)). }
    transitivity (Grp_riehl_uG k Hk g).
    { exact (@inl_merge Grp@{u p} CC _ _ _ _ _ g). }
    transitivity (Grp_riehl_uG k Hk (free_group_counit G (fg_insert _ g))).
    { apply (proper_morphism (grp_map (Grp_riehl_uG k Hk))).
      symmetry. exact (free_group_counit_generator G g). }
    transitivity (Grp_riehl_kG k (fg_insert _ g)).
    { exact (Grp_riehl_uG_counit k Hk (fg_insert _ g)). }
    apply (proper_morphism (grp_map k)).
    exact (@free_group_fmap_generators _ UGH _ g).
  - transitivity (Grp_riehl_desc (@inr Grp@{u p} CC G H g)).
    { apply (proper_morphism (grp_map Grp_riehl_desc)).
      exact (Grp_riehl_transpose_generator _ _ (Datatypes.inr g)). }
    transitivity (Grp_riehl_uH k Hk g).
    { exact (@inr_merge Grp@{u p} CC _ _ _ _ _ g). }
    transitivity (Grp_riehl_uH k Hk (free_group_counit H (fg_insert _ g))).
    { apply (proper_morphism (grp_map (Grp_riehl_uH k Hk))).
      symmetry. exact (free_group_counit_generator H g). }
    transitivity (Grp_riehl_kH k (fg_insert _ g)).
    { exact (Grp_riehl_uH_counit k Hk (fg_insert _ g)). }
    apply (proper_morphism (grp_map k)).
    exact (@free_group_fmap_generators _ UGH _ g).
Qed.

Lemma Grp_riehl_desc_unique (v : @Coprod Grp@{u p} CC G H ~{Grp@{u p}}~> c) :
  v ∘ Grp_riehl_e CC ≈ k → Grp_riehl_desc ≈ v.
Proof.
  intro Hv.
  assert (HG : Grp_riehl_uG k Hk ≈ v ∘ @inl Grp@{u p} CC G H).
  { apply (uniqueness (coeq_desc (Grp_canonical_presentation G)
                         (Grp_riehl_kG k) (Grp_riehl_kG_cofork k Hk))).
    unfold Grp_riehl_kG.
    rewrite <- Hv.
    rewrite <- !comp_assoc.
    rewrite (Grp_riehl_transpose_inl (@inl Grp@{u p} CC G H)
                                     (@inr Grp@{u p} CC G H)).
    reflexivity. }
  assert (HH : Grp_riehl_uH k Hk ≈ v ∘ @inr Grp@{u p} CC G H).
  { apply (uniqueness (coeq_desc (Grp_canonical_presentation H)
                         (Grp_riehl_kH k) (Grp_riehl_kH_cofork k Hk))).
    unfold Grp_riehl_kH.
    rewrite <- Hv.
    rewrite <- !comp_assoc.
    rewrite (Grp_riehl_transpose_inr (@inl Grp@{u p} CC G H)
                                     (@inr Grp@{u p} CC G H)).
    reflexivity. }
  unfold Grp_riehl_desc.
  rewrite HG, HH.
  rewrite (@merge_comp Grp@{u p} CC).
  rewrite (@merge_inl_inr Grp@{u p} CC).
  exact (@id_right Grp@{u p} _ _ v).
Qed.

End Descent.

Definition Grp_coproduct_is_coequalizer (CC : @Cocartesian Grp@{u p}) :
  IsCoequalizer Grp_riehl_l Grp_riehl_r (@Coprod Grp@{u p} CC G H)
    (Grp_riehl_e CC).
Proof.
  unshelve econstructor.
  - exact (Grp_riehl_transpose_cofork _ _).
  - intros c k Hk.
    exact {| unique_obj      := Grp_riehl_desc CC k Hk;
             unique_property := Grp_riehl_desc_commutes CC k Hk;
             uniqueness      := Grp_riehl_desc_unique CC k Hk |}.
Defined.

(* * *** Every coequalizer of the pair is a coproduct of G and H / * *** 该对的每个等化子都是 G 和 H 的余积 *)

Section Construction.

Context {q : Grp@{u p}} {e : FreeGrp UGH ~{Grp@{u p}}~> q}.
Context (E : IsCoequalizer Grp_riehl_l Grp_riehl_r q e).

(* The injections: e restricted to each factor's words, descended through that factor's canonical presentation. / 注射：仅限于每个因子的词，通过该因子的规范表示下降。 *)
Definition Grp_riehl_inl : G ~{Grp@{u p}}~> q := Grp_riehl_uG e (cofork E).
Definition Grp_riehl_inr : H ~{Grp@{u p}}~> q := Grp_riehl_uH e (cofork E).

(* The injection computes: on an element g it IS e at the image of the one-letter word [g] under F(inl). / 该注射计算：在元素 g 上，它是在单字母单词 [g] 在 F(inl) 下的像处的 e。 *)
Example Grp_riehl_inl_is_restriction (g : carrier (grp_setoid G)) :
  Grp_riehl_inl g = e (fmap[FreeGrp] inlS (fg_insert (Grp_Forget G) g))
  := eq_refl.

(* The copairing: the transpose of the two maps, descended through e. / 协配：两个映射的转置，通过 e 降落。 *)
Definition Grp_riehl_merge {z : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z) : q ~{Grp@{u p}}~> z :=
  unique_obj (coeq_desc E (Grp_riehl_transpose f1 f2)
                (Grp_riehl_transpose_cofork f1 f2)).

Lemma Grp_riehl_merge_inl {z : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z) :
  Grp_riehl_merge f1 f2 ∘ Grp_riehl_inl ≈ f1.
Proof.
  apply (@epic _ _ _ _ (coequalizer_epic _ _ (Grp_canonical_presentation G))).
  rewrite <- comp_assoc.
  rewrite (Grp_riehl_uG_counit e (cofork E)).
  unfold Grp_riehl_kG.
  rewrite comp_assoc.
  rewrite (unique_property (coeq_desc E (Grp_riehl_transpose f1 f2)
                              (Grp_riehl_transpose_cofork f1 f2))).
  exact (Grp_riehl_transpose_inl f1 f2).
Qed.

Lemma Grp_riehl_merge_inr {z : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z) :
  Grp_riehl_merge f1 f2 ∘ Grp_riehl_inr ≈ f2.
Proof.
  apply (@epic _ _ _ _ (coequalizer_epic _ _ (Grp_canonical_presentation H))).
  rewrite <- comp_assoc.
  rewrite (Grp_riehl_uH_counit e (cofork E)).
  unfold Grp_riehl_kH.
  rewrite comp_assoc.
  rewrite (unique_property (coeq_desc E (Grp_riehl_transpose f1 f2)
                              (Grp_riehl_transpose_cofork f1 f2))).
  exact (Grp_riehl_transpose_inr f1 f2).
Qed.

Lemma Grp_riehl_merge_unique {z : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z)
  (h : q ~{Grp@{u p}}~> z) :
  h ∘ Grp_riehl_inl ≈ f1 → h ∘ Grp_riehl_inr ≈ f2 →
  h ≈ Grp_riehl_merge f1 f2.
Proof.
  intros H1 H2.
  symmetry.
  apply (uniqueness (coeq_desc E (Grp_riehl_transpose f1 f2)
                       (Grp_riehl_transpose_cofork f1 f2))).
  apply Grp_free_hom_ext; intros [g|g].
  - transitivity (h (Grp_riehl_inl g)).
    { apply (proper_morphism (grp_map h)).
      transitivity (e (fmap[FreeGrp] inlS (fg_insert _ g))).
      { apply (proper_morphism (grp_map e)).
        symmetry. exact (@free_group_fmap_generators _ UGH _ g). }
      transitivity (Grp_riehl_inl (free_group_counit G (fg_insert _ g))).
      { symmetry.
        exact (Grp_riehl_uG_counit e (cofork E) (fg_insert _ g)). }
      apply (proper_morphism (grp_map Grp_riehl_inl)).
      exact (free_group_counit_generator G g). }
    rewrite (H1 g).
    symmetry.
    exact (Grp_riehl_transpose_generator f1 f2 (Datatypes.inl g)).
  - transitivity (h (Grp_riehl_inr g)).
    { apply (proper_morphism (grp_map h)).
      transitivity (e (fmap[FreeGrp] inrS (fg_insert _ g))).
      { apply (proper_morphism (grp_map e)).
        symmetry. exact (@free_group_fmap_generators _ UGH _ g). }
      transitivity (Grp_riehl_inr (free_group_counit H (fg_insert _ g))).
      { symmetry.
        exact (Grp_riehl_uH_counit e (cofork E) (fg_insert _ g)). }
      apply (proper_morphism (grp_map Grp_riehl_inr)).
      exact (free_group_counit_generator H g). }
    rewrite (H2 g).
    symmetry.
    exact (Grp_riehl_transpose_generator f1 f2 (Datatypes.inr g)).
Qed.

(* Any map out of q that carries e to the transpose of (f1, f2) carries the injections to f1 and f2. / 任何将 e 映射到 (f1, f2) 转置的 q 外映射，都将注入映射到 f1 和 f2。 *)
Lemma Grp_riehl_inl_along {z : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z)
  (φ : q ~{Grp@{u p}}~> z) :
  φ ∘ e ≈ Grp_riehl_transpose f1 f2 → φ ∘ Grp_riehl_inl ≈ f1.
Proof.
  intro Hφ.
  rewrite <- (uniqueness (coeq_desc E (Grp_riehl_transpose f1 f2)
                            (Grp_riehl_transpose_cofork f1 f2)) φ Hφ).
  exact (Grp_riehl_merge_inl f1 f2).
Qed.

Lemma Grp_riehl_inr_along {z : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z)
  (φ : q ~{Grp@{u p}}~> z) :
  φ ∘ e ≈ Grp_riehl_transpose f1 f2 → φ ∘ Grp_riehl_inr ≈ f2.
Proof.
  intro Hφ.
  rewrite <- (uniqueness (coeq_desc E (Grp_riehl_transpose f1 f2)
                            (Grp_riehl_transpose_cofork f1 f2)) φ Hφ).
  exact (Grp_riehl_merge_inr f1 f2).
Qed.

End Construction.

(* Postcomposition moves inside the transpose. / 后合成移动到转置内部。 *)
Lemma Grp_riehl_transpose_post {z z' : Grp@{u p}}
  (f1 : G ~{Grp@{u p}}~> z) (f2 : H ~{Grp@{u p}}~> z)
  (f1' : G ~{Grp@{u p}}~> z') (f2' : H ~{Grp@{u p}}~> z')
  (φ : z ~{Grp@{u p}}~> z') :
  φ ∘ f1 ≈ f1' → φ ∘ f2 ≈ f2' →
  φ ∘ Grp_riehl_transpose f1 f2 ≈ Grp_riehl_transpose f1' f2'.
Proof.
  intros H1 H2.
  apply Grp_free_hom_ext; intros [g|g].
  - transitivity (φ (f1 g)).
    { apply (proper_morphism (grp_map φ)).
      exact (Grp_riehl_transpose_generator f1 f2 (Datatypes.inl g)). }
    rewrite (H1 g).
    symmetry.
    exact (Grp_riehl_transpose_generator f1' f2' (Datatypes.inl g)).
  - transitivity (φ (f2 g)).
    { apply (proper_morphism (grp_map φ)).
      exact (Grp_riehl_transpose_generator f1 f2 (Datatypes.inr g)). }
    rewrite (H2 g).
    symmetry.
    exact (Grp_riehl_transpose_generator f1' f2' (Datatypes.inr g)).
Qed.

End RiehlPair.

(* * ** Riehl's construction as a coproduct structure on [Grp] / * ** Riehl 的构造作为 [Grp] 上的余积结构 *)

(* Given coequalizers, from anywhere, the coequalizer of the pair with the injections above IS a choice of binary coproducts. / 给定共轭化子，从任何地方，带有上述单射对的共轭化子就是二元积的选择。 *)
Definition Grp_Cocartesian_of_coequalizers@{u p +}
  (HC : HasCoequalizers Grp@{u p}) : @Cocartesian Grp@{u p}.
Proof.
  unshelve refine (@Build_Cartesian (Grp^op)
    (fun G H => `1 (@coeq Grp HC _ _ (Grp_riehl_l G H) (Grp_riehl_r G H)))
    (fun x G H f1 f2 =>
       @Grp_riehl_merge G H _ _
         (`2 (`2 (@coeq Grp HC _ _ (Grp_riehl_l G H) (Grp_riehl_r G H))))
         x f1 f2)
    (fun G H =>
       @Grp_riehl_inl G H _ _
         (`2 (`2 (@coeq Grp HC _ _ (Grp_riehl_l G H) (Grp_riehl_r G H)))))
    (fun G H =>
       @Grp_riehl_inr G H _ _
         (`2 (`2 (@coeq Grp HC _ _ (Grp_riehl_l G H) (Grp_riehl_r G H)))))
    _ _).
  - intros x G H f1 f1' Hf1 f2 f2' Hf2.
    apply Grp_riehl_merge_unique.
    + rewrite (Grp_riehl_merge_inl _ _ _ f1 f2); exact Hf1.
    + rewrite (Grp_riehl_merge_inr _ _ _ f1 f2); exact Hf2.
  - intros x G H f1 f2 h; split.
    + intro Hh; split.
      * rewrite Hh. exact (Grp_riehl_merge_inl _ _ _ f1 f2).
      * rewrite Hh. exact (Grp_riehl_merge_inr _ _ _ f1 f2).
    + intros [H1 H2].
      exact (Grp_riehl_merge_unique _ _ _ f1 f2 h H1 H2).
Defined.

(* * ** At the adjoint functor theorem's coproduct and coequalizers / * ** 在伴随函子定理的余积和余等化子 *)

(*
 Riehl's statement at the coproduct Instance/Grp/Colimit.v obtains from
 the adjoint functor theorem, passed explicitly. 

 --------
 Riehl 在 coproduct Instance/Grp/Colimit.v 中的声明来源于伴随函子定理，明确地通过了。
*)
Definition Grp_free_product_is_coequalizer@{u p +} (G H : Grp@{u p}) :
  IsCoequalizer (Grp_riehl_l G H) (Grp_riehl_r G H)
    (@Coprod Grp Grp_Cocartesian_via_GAFT G H)
    (Grp_riehl_e G H Grp_Cocartesian_via_GAFT) :=
  Grp_coproduct_is_coequalizer G H Grp_Cocartesian_via_GAFT.

(* The same at Instance/Grp/Pushout.v's words-based free product. / 与 Instance/Grp/Pushout.v 的基于词的自由积相同。 *)
Definition Grp_free_product_words_is_coequalizer@{u p +} (G H : Grp@{u p}) :
  IsCoequalizer (Grp_riehl_l G H) (Grp_riehl_r G H)
    (@Coprod Grp Grp_Cocartesian G H)
    (Grp_riehl_e G H Grp_Cocartesian) :=
  Grp_coproduct_is_coequalizer G H Grp_Cocartesian.

(* Riehl's construction run on the adjoint functor theorem's coequalizers. / Riehl 的构造在伴随函子定理的共等化子上运行。 *)
Definition Grp_Cocartesian_via_riehl@{u p +} : @Cocartesian Grp@{u p} :=
  Grp_Cocartesian_of_coequalizers Grp_HasCoequalizers_via_GAFT.

Example Grp_Cocartesian_via_riehl_obj@{u p +} (G H : Grp@{u p}) :
  @Coprod Grp Grp_Cocartesian_via_riehl G H
    = `1 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _
            (Grp_riehl_l G H) (Grp_riehl_r G H)) := eq_refl.

(** ** Agreement / ** 协议 *)

(* [coequalizer_unique] of Structure/Coequalizer.v ends in [Qed], so its comparison map cannot be read back; this transparent twin carries the coequalizing maps along. / Structure/Coequalizer.v 的 [coequalizer_unique] 以 [Qed] 结尾，因此其比较映射无法被读回；这个透明的双胞胎携带了共等化映射。 *)
Section CoequalizerAlong.

Context {C : Category} {x y : C} {f g : x ~> y}.
Context {q1 q2 : C} {e1 : y ~> q1} {e2 : y ~> q2}.
Context (E1 : IsCoequalizer f g q1 e1) (E2 : IsCoequalizer f g q2 e2).

Definition coequalizer_unique_along : q1 ≅ q2.
Proof using E1 E2.
  pose proof (coeq_desc E1 e2 (cofork E2)) as D12.
  pose proof (coeq_desc E2 e1 (cofork E1)) as D21.
  pose proof (coeq_desc E1 e1 (cofork E1)) as D11.
  pose proof (coeq_desc E2 e2 (cofork E2)) as D22.
  unshelve refine {| to := unique_obj D12; from := unique_obj D21 |}.
  - transitivity (unique_obj D22).
    + symmetry.
      apply (uniqueness D22).
      rewrite <- comp_assoc.
      rewrite (unique_property D21).
      exact (unique_property D12).
    + apply (uniqueness D22).
      apply id_left.
  - transitivity (unique_obj D11).
    + symmetry.
      apply (uniqueness D11).
      rewrite <- comp_assoc.
      rewrite (unique_property D12).
      exact (unique_property D21).
    + apply (uniqueness D11).
      apply id_left.
Defined.

Lemma coequalizer_unique_along_e : to coequalizer_unique_along ∘ e1 ≈ e2.
Proof using E1 E2. exact (unique_property (coeq_desc E1 e2 (cofork E2))). Qed.

End CoequalizerAlong.

(*
 The coequalizer Instance/Grp/Colimit.v's [Grp_HasCoequalizers_via_GAFT]
 returns for Riehl's pair is the adjoint functor theorem's coproduct... 

 --------
 coequalizer Instance/Grp/Colimit.v 的 [Grp_HasCoequalizers_via_GAFT] 对于 Riehl 的对返回的是伴随函子定理的积...
*)
Definition Grp_free_product_coequalizer_agrees@{u p +} (G H : Grp@{u p}) :
  `1 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _
        (Grp_riehl_l G H) (Grp_riehl_r G H))
    ≅ @Coprod Grp Grp_Cocartesian_via_GAFT G H :=
  coequalizer_unique_along
    (`2 (`2 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _
               (Grp_riehl_l G H) (Grp_riehl_r G H))))
    (Grp_free_product_is_coequalizer G H).

(* ...compatibly with the coequalizing maps... / ...与同等化映射兼容... *)
Lemma Grp_free_product_coequalizer_agrees_e@{u p +} (G H : Grp@{u p}) :
  to (Grp_free_product_coequalizer_agrees G H)
    ∘ `1 (`2 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _
                (Grp_riehl_l G H) (Grp_riehl_r G H)))
    ≈ Grp_riehl_e G H Grp_Cocartesian_via_GAFT.
Proof.
  exact (coequalizer_unique_along_e
           (`2 (`2 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _
                      (Grp_riehl_l G H) (Grp_riehl_r G H))))
           (Grp_free_product_is_coequalizer G H)).
Qed.

(*
 ...and with the injections: Riehl's on the left, the theorem's on the
 right. 

 --------
 ...以及注射部分：左边是Riehl的，右边是定理的。
*)
Lemma Grp_free_product_coequalizer_agrees_inl@{u p +} (G H : Grp@{u p}) :
  to (Grp_free_product_coequalizer_agrees G H)
    ∘ @inl Grp Grp_Cocartesian_via_riehl G H
    ≈ @inl Grp Grp_Cocartesian_via_GAFT G H.
Proof.
  exact (Grp_riehl_inl_along G H _
           (@inl Grp Grp_Cocartesian_via_GAFT G H)
           (@inr Grp Grp_Cocartesian_via_GAFT G H) _
           (Grp_free_product_coequalizer_agrees_e G H)).
Qed.

Lemma Grp_free_product_coequalizer_agrees_inr@{u p +} (G H : Grp@{u p}) :
  to (Grp_free_product_coequalizer_agrees G H)
    ∘ @inr Grp Grp_Cocartesian_via_riehl G H
    ≈ @inr Grp Grp_Cocartesian_via_GAFT G H.
Proof.
  exact (Grp_riehl_inr_along G H _
           (@inl Grp Grp_Cocartesian_via_GAFT G H)
           (@inr Grp Grp_Cocartesian_via_GAFT G H) _
           (Grp_free_product_coequalizer_agrees_e G H)).
Qed.

(*
 The two coproduct bifunctors agree up to natural isomorphism, both being
 left adjoint to the diagonal. 

 --------
 这两个余积双函子在自然同构意义下是一致的，它们都是对角函子的左伴随。
*)
Definition Grp_riehl_coproduct_agrees@{u p +} :
  @InternalCoproductFunctor Grp@{u p} Grp_Cocartesian_via_riehl
    ≈ @InternalCoproductFunctor Grp@{u p} Grp_Cocartesian_via_GAFT :=
  left_adjoint_iso (Diagonal_Product Grp@{u p}) _ _
    (@Diagonal_Coproduct_Adjunction Grp@{u p} Grp_Cocartesian_via_riehl)
    (@Diagonal_Coproduct_Adjunction Grp@{u p} Grp_Cocartesian_via_GAFT).

(*
 Through Instance/Grp/Colimit.v's [Grp_free_product_iso], the same
 coequalizer is Instance/Grp/Pushout.v's words-based free product. 

 --------
 通过 Instance/Grp/Colimit.v 的 [Grp_free_product_iso]，相同的余等化子是 Instance/Grp/Pushout.v 的基于单词的自由积。
*)
Definition Grp_free_product_coequalizer_agrees_words@{u p +}
  (G H : Grp@{u p}) :
  `1 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _
        (Grp_riehl_l G H) (Grp_riehl_r G H))
    ≅ @Coprod Grp Grp_Cocartesian G H :=
  iso_compose (Grp_free_product_iso G H)
              (Grp_free_product_coequalizer_agrees G H).

Lemma Grp_free_product_coequalizer_agrees_words_e@{u p +}
  (G H : Grp@{u p}) :
  to (Grp_free_product_coequalizer_agrees_words G H)
    ∘ `1 (`2 (@coeq Grp Grp_HasCoequalizers_via_GAFT _ _
                (Grp_riehl_l G H) (Grp_riehl_r G H)))
    ≈ Grp_riehl_e G H Grp_Cocartesian.
Proof.
  unfold Grp_free_product_coequalizer_agrees_words; simpl to.
  rewrite <- comp_assoc.
  rewrite (Grp_free_product_coequalizer_agrees_e G H).
  apply Grp_riehl_transpose_post.
  - exact (Grp_free_product_iso_inl G H).
  - exact (Grp_free_product_iso_inr G H).
Qed.

Lemma Grp_free_product_coequalizer_agrees_words_inl@{u p +}
  (G H : Grp@{u p}) :
  to (Grp_free_product_coequalizer_agrees_words G H)
    ∘ @inl Grp Grp_Cocartesian_via_riehl G H
    ≈ @inl Grp Grp_Cocartesian G H.
Proof.
  exact (Grp_riehl_inl_along G H _
           (@inl Grp Grp_Cocartesian G H) (@inr Grp Grp_Cocartesian G H) _
           (Grp_free_product_coequalizer_agrees_words_e G H)).
Qed.

Lemma Grp_free_product_coequalizer_agrees_words_inr@{u p +}
  (G H : Grp@{u p}) :
  to (Grp_free_product_coequalizer_agrees_words G H)
    ∘ @inr Grp Grp_Cocartesian_via_riehl G H
    ≈ @inr Grp Grp_Cocartesian G H.
Proof.
  exact (Grp_riehl_inr_along G H _
           (@inl Grp Grp_Cocartesian G H) (@inr Grp Grp_Cocartesian G H) _
           (Grp_free_product_coequalizer_agrees_words_e G H)).
Qed.

(** ** Non-vacuity / ** 非空性 *)

(*
 The pair is not trivial: at Z/2 the letter [inl w], for w the word
 “1 then 1”, is sent by l to the letter [inl 0] and by r to the word
 “[inl 1] then [inl 1]”, and the homomorphism to Z/2 sending every letter
 to 1 separates the two. 

 --------
 这个对并非平凡：在 Z/2 上，字母 [inl w]，对于 w 这个词 “1 然后 1”，通过 l 映射到字母 [inl 0]，通过 r 映射到词 “[inl 1] 然后 [inl 1]”，而将每个字母映射为 1 的同态到 Z/2 能区分这两者。
*)
Section NonVacuity.

Universes u p.

Local Notation Z2 := Z2@{p}.
Local Notation Z2S :=
  (@Coprod Sets Sets_Cocartesian (Grp_Forget Z2) (Grp_Forget Z2)).
Local Notation Z2FS :=
  (@Coprod Sets Sets_Cocartesian (Grp_Forget (FreeGrp (Grp_Forget Z2)))
                                 (Grp_Forget (FreeGrp (Grp_Forget Z2)))).

Lemma Grp_riehl_pair_nontrivial :
  (Grp_riehl_l Z2 Z2 : _ ~{Grp@{u p}}~> _) ≈ Grp_riehl_r Z2 Z2 → False.
Proof.
  intro Hlr.
  pose (w := grp_mul (FreeGrpObject (Grp_Forget Z2))
               (fg_insert (Grp_Forget Z2) true)
               (fg_insert (Grp_Forget Z2) true)).
  unshelve epose (t := {| morphism := fun _ : Z2S => true |}
                         : Z2S ~{Sets}~> Grp_Forget Z2).
  { intros ? ? ?; reflexivity. }
  pose (k := free_grp_extend t).
  assert (HA : k (Grp_riehl_l Z2 Z2 (fg_insert Z2FS (Datatypes.inl w)))
                 ≈ true).
  { transitivity (k (fg_insert Z2S
                       (Datatypes.inl (free_group_counit Z2 w)))).
    - apply (proper_morphism (grp_map k)).
      exact (Grp_riehl_l_inl Z2 Z2 w).
    - exact (free_grp_extend_generators Z2S Z2 t _). }
  assert (HB : k (Grp_riehl_r Z2 Z2 (fg_insert Z2FS (Datatypes.inl w)))
                 ≈ false).
  { transitivity (k (fmap[FreeGrp]
                       (@inl Sets Sets_Cocartesian
                          (Grp_Forget Z2) (Grp_Forget Z2)) w)).
    - apply (proper_morphism (grp_map k)).
      exact (Grp_riehl_r_inl Z2 Z2 w).
    - unfold w.
      rewrite (proper_morphism (grp_map k) _ _
                 (grp_map_mul (fmap[FreeGrp]
                    (@inl Sets Sets_Cocartesian
                       (Grp_Forget Z2) (Grp_Forget Z2))) _ _)).
      rewrite (grp_map_mul k).
      rewrite (proper_morphism (grp_map k) _ _
                 (@free_group_fmap_generators (Grp_Forget Z2) Z2S _ true)).
      rewrite (free_grp_extend_generators Z2S Z2 t).
      reflexivity. }
  apply Z2_nontrivial.
  transitivity (k (Grp_riehl_l Z2 Z2 (fg_insert Z2FS (Datatypes.inl w)))).
  { symmetry; exact HA. }
  transitivity (k (Grp_riehl_r Z2 Z2 (fg_insert Z2FS (Datatypes.inl w)))).
  { apply (proper_morphism (grp_map k)); exact (Hlr _). }
  exact HB.
Qed.

(* Hence e is never monic at Z/2: the coequalizer genuinely quotients the free group on the disjoint union. / 因此 e 在 Z/2 上从不为单项：该共等化器真正地将不相交并集上的自由群取商。 *)
Corollary Grp_riehl_e_not_monic (CC : @Cocartesian Grp@{u p}) :
  Monic (Grp_riehl_e Z2 Z2 CC) → False.
Proof.
  intro Hm.
  apply Grp_riehl_pair_nontrivial.
  apply (@monic _ _ _ _ Hm).
  exact (cofork (Grp_coproduct_is_coequalizer Z2 Z2 CC)).
Qed.

End NonVacuity.

(*
 The same at the adjoint functor theorem's coproduct, which exists only
 above [Set] carriers. 

 --------
 与伴随函子定理的余积相同，它只存在于 [Set] 承载者之上。
*)
Example Grp_free_product_coequalizer_nontrivial@{u p +} :
  Monic (Grp_riehl_e Z2@{p} Z2@{p}
           (Grp_Cocartesian_via_GAFT : @Cocartesian Grp@{u p})) → False :=
  Grp_riehl_e_not_monic _.
