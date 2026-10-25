Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Hypergraph.Spider.
Require Import Category.Instance.Ab.Tensor.
Require Import Category.Instance.Ab.Monoidal.
Require Import Category.Instance.Ab.TensorPower.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Free.
Require Import Category.Instance.Rng.FreeMonad.
Require Import Category.Instance.Rng.FreeMonad.Words.
Require Import Coq.Lists.List.

Generalizable All Variables.

(* * * T-algebras as systems ⟨A, ν₀, ν₁, …⟩ of multilinear operations / * * T-代数作为多线性运算系统 ⟨A, ν₀, ν₁, …⟩ *)

(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Springer GTM 5, 1998, §VI.4, Exercise 4(b), printed p. 146 (PDF
 p. 155) — maclane:VI.4:ex4
 nLab: https://ncatlab.org/nlab/show/tensor+algebra
 nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad

 WHAT THE BOOK ASKS, read from the page image: "(b) Give the
 corresponding description of T-algebras and show that the comparison
 functor from rings to T-algebras is an isomorphism."  The
 description it corresponds to is Proposition 2 (p. 145), the
 W-algebras as systems ⟨S, ν1, ν2, …⟩ with ν1 = 1 and νk(νn1 × ⋯ ×
 νnk) = ν_{n1+⋯+nk} (2), which #470's Instance/Smgrp/Word.v delivers
 (and #471's Instance/Mon/Word/System.v with ν₀ added): here a T-algebra
 is an abelian group A with homomorphisms νₙ : A^{⊗n} → A, n ≥ 0, ν₁ =
 1 and (2), νₙ the n-fold product of a ring with unit ν₀.  The
 comparison functor and its isomorphism are
 Instance/Rng/FreeMonad.v's [Rng_K] and [Rng_EM_iso]; this file is the
 description, and the isomorphism through it.

 THE SYSTEMS.  [TSystem A] is ν on the words over A ([tnu]),
 respecting each letter ([tnu_letter]) and additive in each letter
 ([tnu_lin]), with ν₁ = 1 ([tnu_unit], ν⟨a⟩ ≈ a) and (2) read on words
 of words ([tnu_assoc]: ν of the values of the inner words ≈ ν of their
 concatenation), as #471's [nu0_assoc] reads it after Riehl's square
 (5.2.7) read on lists of lists (her Example 5.2.6(iii), printed
 pp. 189-190, cited in Instance/Mon/Word/System.v).
 A function on words respecting each letter and additive in each IS a
 family of homomorphisms out of the tensor powers: the literal νₙ :
 A^{⊗n} → A is [tsys_nu_hom σ n], ν extended additively to the sums of
 words (Instance/Ab/TensorPower.v's [tw_ext]) composed with the
 injection ιₙ, and on the pure tensor a₁ ⊗ … ⊗ aₙ ⊗ 1 it is ν⟨a₁ … aₙ⟩
 ([tsys_nu_hom_pure], at ≈); conversely TensorPower.v's
 [tw_desc_letter] and [tw_desc_lin] at c := A make any family of
 homomorphisms such a ν, the two being the same data by
 [TW_is_tensor_coproduct].  A map of systems ([TSystemHom]) is a
 homomorphism f with f νₙ = ν'ₙ f^{⊗n}, f^{⊗n} being the letterwise
 map on words.

 BOTH WAYS.  An algebra h gives the system ν w = h(word product of w)
 ([alg_system], [alg_system_nu] at [eq_refl]): ν₁ = 1 is the unit law
 and (2) the action law at the word of words, through the relabelling
 and the concatenation lemmas [fr_eval_word_map] (LEIBNIZ) and
 [fr_eval_id_word_concat]; ν₀ is the unit and ν₂ the product of the
 algebra's ring, on the nose ([alg_system_nil], [alg_system_pair]); an
 algebra map is a map of the systems ([alg_hom_TSystemHom]).  A system
 gives a ring with 1 = ν⟨⟩ and a·b = ν⟨a b⟩ ([sys_ring]: associativity
 and the unit laws from (2) at words of two words, [sys_nu_pair], and
 ν₁ = 1; distributivity from [tnu_lin]; annihilation derived), and "νₙ
 is the n-fold product": ν of a word is the product of its letters in
 that ring ([sys_nu_is_product], at ≈); a map of systems is a ring map
 ([sys_ring_map]).

 AS A CATEGORY.  [TSys], the systems ⟨A, ν₀, ν₁, …⟩ ([TSysObj]) and
 their maps, is isomorphic in Cat to Ab^T ([TSys_EM_iso]): its legs
 are [TSys_to_EM] (the system's ring, then [Rng_K]) and [EM_to_TSys]
 ([TSys_EM_iso_to], [TSys_EM_iso_from]), and every component of both
 natural isomorphisms is the identity, to and from, at [eq_refl]
 ([TSys_EM_iso_to_from_component], [TSys_EM_iso_from_to_component]).  A
 system's algebra evaluates in the system's ring, 1 ↦ ν⟨⟩ and
 ⟨a⟩·⟨b⟩ ↦ ν⟨a b⟩ ([TSys_to_EM_alg], [TSys_to_EM_one],
 [TSys_to_EM_pair]); an algebra's system has ν the structure map on the
 word product and ν₂ the product of its ring ([EM_to_TSys_nu],
 [EM_to_TSys_pair]).  The system round trip keeps the group, ν₀, ν₂ and
 the maps on the nose and returns ν₁ as the identity ([TSys_rt_ab],
 [TSys_rt_nil], [TSys_rt_pair], [TSys_rt_hom], [TSys_rt_letter]), and ν
 at every word at ≈ ([TSys_rt_nu]); refused at [eq_refl]: ν at a
 variable word (R27), ν₁ against the system's own (R28), the whole
 system (R29), the whole algebra (R30) and the composite against the
 identity functor (R31).  The algebra round trip keeps the group and
 the maps ([EM_TSys_rt_carrier], [EM_TSys_rt_alg_hom]).  Mac Lane's
 exercise as a statement about categories is [Rng_TSys_iso : Rng
 ≅[Cat] TSys], the composite of FreeMonad.v's [Rng_EM_iso] with the
 inverse of [TSys_EM_iso].  Its components are not identities at
 [eq_refl], even at a point (R32; its controls are the identity
 components of the two it composes, C47 and C98): Theory/
 Isomorphism.v's [iso_compose] builds them in its transparent
 [iso_compose_obligation_2], a chain of setoid rewrites in [Cat]
 through three opaque constants of Theory/Functor.v,
 [fun_equiv_comp_assoc], [fun_equiv_id_left] and
 [Functor_Setoid_obligation_1] (read from the term; transparency by
 [About]), so identity components are claimed for [TSys_EM_iso] and
 [Rng_EM_iso] only.  For a ring R, the system of K R has ν⟨⟩ =
 1, ν⟨a⟩ = a and ν⟨a b⟩ = a·b, and ν of a word the product of its
 letters bracketed to the right, all at [eq_refl] ([Rng_system_nil],
 [Rng_system_letter], [Rng_system_pair], [Rng_system_nu]).

 STRENGTHS.  Every [Example] holds at [eq_refl], and
 Test/ProbeFreeRing474.v restates each one (C79 to C93 and C95 to
 C102).  Stated at ≈: [sys_nu_is_product], [TSys_rt_nu], the ring laws
 of a system and the inverse laws of [TSys_EM_iso], which rest on a
 system's ν₁ = 1 and (2), at ≈; [tsys_nu_hom_pure], which rests not on
 those but on TensorPower.v's [tw_word_iota] (ι₀ adds a "+ 0", C103) and
 on the system's respect for letters and additivity in them;
 [fr_eval_id_word_concat], which has no hypothesis and is false at
 Leibniz = (C107: at ⟨⟨a⟩, ⟨⟩⟩ one side is ⟨a⟩·1 and the other ⟨a⟩);
 and the inverse laws of [Rng_TSys_iso] (R32, above).  [fr_eval_word_map] and
 [map_cmon_id] are Leibniz equalities, stronger than ≈.  Eleven proofs
 end [Defined] and sixteen [Qed] (counted by token); all eleven
 [Defined]s are load-bearing, measured as Instance/Rng/FreeMonad.v's
 header describes: [alg_system] ([alg_system_nu]), [sys_ring_map]
 ([TSys_to_Rng]), [TSysHom_Setoid], [TSys_id] and [TSys_compose]
 ([TSys]), [TSys] ([TSys_to_Rng]), [TSys_to_Rng] and [EM_to_TSys]
 ([TSys_EM_counit_iso]), [TSys_EM_counit_iso] and [TSys_EM_unit_iso]
 ([TSys_EM_iso]) and [TSys_EM_iso] ([TSys_EM_iso_to]).

 UNIVERSES, read off [About] (every name, by script).  Every name is
 universe polymorphic, in the section [Systems] over Ab@{u p} and
 Rng@{u p}, and binds u and p first, with no [Set] but strict lower
 bounds, no equation in any block and caps of the standard library's
 global levels only.  The systems are stated with no reference to T, so
 the record [TSystem] with its constructor and fields, the maps of
 systems, the ring of a system and the category [TSys] bind u and p alone
 (thirty-five names, with [tsys_sum], [fr_eval_word_map] and
 [map_cmon_id]); [tsys_nu_hom] and [tsys_nu_hom_pure] bind three,
 the further one the tensor powers'; the thirty names through T or K bind
 six, u, p and the four levels [FreeRngAb] carries beyond [Ab]'s
 ([TSys_EM_iso] binds u, p, c and three of the four, c above u and p from
 Instance/Cat.v's [Cat@{c u u u p}]); [Rng_TSys_iso] binds u, p, c and
 four; and three readbacks comparing across a composite bind a second
 copy of three of those four, nine levels in all.  The same levels on
 Coq 8.19.2 and 8.20.1 (FreeMonad.v's header).

 NOT DELIVERED.  (2) over tensors of tensors, the ⊗ analogue
 νk(νn1 ⊗ ⋯ ⊗ νnk) = ν_{n1+⋯+nk} of Mac Lane's (2) (he writes it with ×
 for W, p. 145; the ⊗ form is the reader's to supply), which needs the
 isomorphisms A^{⊗n1} ⊗ ⋯ ⊗ A^{⊗nk} ≅ A^{⊗(n1+⋯+nk)}: the reading on
 words of words stands in for it.  The analogue of Mac Lane's Corollary
 (a characterization by ν₀, an associative ν₂ and νₙ₊₁ = νₙ(ν₂ ⊗ 1)):
 the ring route of FreeMonad.v stands in for it.  A strict isomorphism
 of the systems with Ab^T (refused above).  Identity components for
 [Rng_TSys_iso] (R32): it is the composite, not rebuilt from two
 component isomorphisms as [TSys_EM_iso] is (not attempted). 

 --------
 书籍：Mac Lane，《供数学工作者使用的范畴》，第2版，Springer GTM 5, 1998, 第VI.4节，练习4(b)，印刷版第146页（PDF第155页） — maclane:VI.4:ex4
 nLab：https://ncatlab.org/nlab/show/tensor+algebra
 nLab：https://ncatlab.org/nlab/show/algebra+over+a+monad书中要求，从页图像中阅读：“(b) 给出 T-代数的对应描述，并证明从环到 T-代数的比较函子是一个同构。”它对应的描述是命题 2（第 145 页），W-代数作为系统 ⟨S, ν1, ν2, …⟩，其中 ν1 = 1，并且 νk(νn1 × ⋯ × νnk) = ν_{n1+⋯+nk} (2)，这是 #470 的 Instance/Smgrp/Word.v 提供的（以及 #471 的 Instance/Mon/Word/System.v，加入了 ν₀）：在这里，T-代数是一个阿贝尔群 A，具有同态 νₙ : A^{⊗n} → A, n ≥ 0，ν₁ = 1 并满足 (2)，νₙ 是带单位环 ν₀ 的 n 重乘积。比较函子及其同构是 Instance/Rng/FreeMonad.v 中的 [Rng_K] 和 [Rng_EM_iso]；该文件是描述，并且通过它得到同构。系统。[TSystem A] 是在字母 A 上的字词上的 ν（[tnu]），尊重每个字母（[tnu_letter]）并在每个字母中可加（[tnu_lin]），其中 ν₁ = 1（[tnu_unit]，ν⟨a⟩ ≈ a）并且（2）在字词的字词上读取（[tnu_assoc]：内部字词的值的 ν ≈ 它们拼接的 ν），正如 #471 的 [nu0_assoc] 在 Riehl 的五边形（5.2.7）之后读取它，在列表的列表上读取（她的示例 5.2.6(iii)，印刷页 189-190，引用于 Instance/Mon/Word/System.v）。在每个字母上尊重且在每个字上可加的函数是一族从张量幂出来的同态：字面上的 νₙ : A^{⊗n} → A 是 [tsys_nu_hom σ n]，ν 加法扩展到单词的和（Instance/Ab/TensorPower.v 的 [tw_ext]），再与注入 ιₙ 组成，在纯张量 a₁ ⊗ … ⊗ aₙ ⊗ 1 上为 ν⟨a₁ … aₙ⟩（[tsys_nu_hom_pure]，约在≈处）；反过来，TensorPower.v 的 [tw_desc_letter] 和 [tw_desc_lin] 在 c := A 处使任何一族同态成为这样的 ν，这两者的数据通过 [TW_is_tensor_coproduct] 是相同的。系统的映射（[TSystemHom]）是同态 f，使 f νₙ = ν'ₙ f^{⊗n}，其中 f^{⊗n} 是字对字的单词映射。双向。一个代数 h 给出了系统 ν w = h(w 的单词积) 
 ([alg_system], [alg_system_nu] 于 [eq_refl])：ν₁ = 1 是单位律
 并且 (2) 在单词的单词上的作用律，通过重新标记
 和连接引理 [fr_eval_word_map] (LEIBNIZ) 以及 [fr_eval_id_word_concat] ; ν₀ 是单位，ν₂ 是代数环的积，准确无误地 ([alg_system_nil], [alg_system_pair])；一个代数映射是系统的映射 ([alg_hom_TSystemHom])。一个系统给出了一个带 1 的环 = ν⟨⟩ 以及 a·b = ν⟨a b⟩ ([sys_ring]：来自两个单词的单词的关联律和单位律 [sys_nu_pair]，并且 ν₁ = 1；分配律来自 [tnu_lin]；消去律推导)，并且“νₙ 是 n 重积”：一个单词的 ν 是该环中字母的积 ([sys_nu_is_product], 在 ≈); 系统的映射是一个环映射 ([sys_ring_map])。作为一个范畴。[TSys]，系统 ⟨A, ν₀, ν₁, …⟩（[TSysObj]）及其映射，在范畴 Cat 中与 Ab^T（[TSys_EM_iso]）同构：它的 legs 是 [TSys_to_EM]（系统的环，然后是 [Rng_K]）和 [EM_to_TSys]（[TSys_EM_iso_to], [TSys_EM_iso_from]），且两者自然同构的每个分量在 [eq_refl]（[TSys_EM_iso_to_from_component], [TSys_EM_iso_from_to_component]）处都是恒等。系统的代数在系统的环中取值，1 ↦ ν⟨⟩，以及 ⟨a⟩·⟨b⟩ ↦ ν⟨a b⟩（[TSys_to_EM_alg], [TSys_to_EM_one], [TSys_to_EM_pair]）；代数的系统有 ν 作为单词乘积上的结构映射，以及 ν₂ 作为它环的乘法（[EM_to_TSys_nu], [EM_to_TSys_pair]）。系统往返保持群、ν₀、ν₂以及映射的准确性，并返回 ν₁ 作为恒等 ([TSys_rt_ab], [TSys_rt_nil], [TSys_rt_pair], [TSys_rt_hom], [TSys_rt_letter])，并且在每个字上 ν 约为 ([TSys_rt_nu])；在 [eq_refl] 被拒绝：ν 在一个变量字上 (R27)，ν₁ 针对系统自身 (R28)、整个系统 (R29)、整个代数 (R30) 以及复合与恒等函子 (R31)。代数往返保持群和映射 ([EM_TSys_rt_carrier], [EM_TSys_rt_alg_hom])。作为关于范畴的叙述，Mac Lane 的练习是 [Rng_TSys_iso : Rng ≅ [Cat] TSys]，FreeMonad.v 的复合 [Rng_EM_iso] 与 [TSys_EM_iso] 的逆。它的组成部分在 [eq_refl] 处不是恒等的，即使在一点 (R32；它的控制是它所组成的两个部分 C47 和 C98 的恒等组件)：Theory/Isomorphism.v 的 [iso_compose] 在其透明的 [iso_compose_obligation_2] 中构建它们，在 [Cat] 中通过 Theory/Functor.v 的三个不透明常量 [fun_equiv_comp_assoc]、[fun_equiv_id_left] 和 [Functor_Setoid_obligation_1]（从项中读取；透明性由 [About] 所示）进行一系列集合重写，因此只有 [TSys_EM_iso] 和 [Rng_EM_iso] 声称具有恒等组件。对于环 R，系统 K R 的 ν⟨⟩ = 1，ν⟨a⟩ = a，ν⟨a b⟩ = a·b，并且单词的 ν 是它的字母按右括号结合的乘积，这些都在 [eq_refl]（[Rng_system_nil]、[Rng_system_letter]、[Rng_system_pair]、[Rng_system_nu]）中。优势。每个 [Example] 在 [eq_refl] 保持成立，Test/ProbeFreeRing474.v 重申每一个（C79 到 C93 及 C95 到 C102）。在 ≈: [sys_nu_is_product], [TSys_rt_nu] 中陈述了系统的环律和 [TSys_EM_iso] 的逆律，这些基于系统的 ν₁ = 1 和 (2)，在 ≈; [tsys_nu_hom_pure] 中，这些不依赖于前者，而是依赖于 TensorPower.v 的 [tw_word_iota]（ι₀ 添加了一个“+ 0”，C103）以及系统对字母及其中的可加性的遵守；[fr_eval_id_word_concat] 没有假设，并且在莱布尼茨中为假 = (C107: 在 ⟨⟨a⟩, ⟨⟩⟩ 中一侧是 ⟨a⟩·1，另一侧是 ⟨a⟩)；以及 [Rng_TSys_iso] 的逆律（R32，如上）。[fr_eval_word_map] 和 [map_cmon_id] 是莱布尼茨等式，比 ≈ 更强。十一个证明
 结束 [Defined] 和十六个 [Qed]（按令牌计数）；所有十一
 个 [Defined] 都是承重的，根据 Instance/Rng/FreeMonad.v 的头部描述测量：[alg_system]（[alg_system_nu]）、[sys_ring_map]（[TSys_to_Rng]）、[TSysHom_Setoid]、[TSys_id] 和 [TSys_compose]（[TSys]）、[TSys]（[TSys_to_Rng]）、[TSys_to_Rng] 和 [EM_to_TSys]（[TSys_EM_counit_iso]）、[TSys_EM_counit_iso] 和 [TSys_EM_unit_iso]（[TSys_EM_iso]）以及 [TSys_EM_iso]（[TSys_EM_iso_to]）。宇宙，逐一读取 [About]（每个名称，按脚本）。每个名称都是多态宇宙，在 [Systems] 部分关于 Ab@{u p} 和 Rng@{u p}，并首先绑定 u 和 p，没有 [Set]，但有严格的下界，在任何块中没有方程，并且只在标准库的全局级别的上限。这些系统的陈述没有提及 T，因此记录 [TSystem] 及其构造函数和字段、系统映射、系统的环以及类别 [TSys] 仅绑定 u 和 p（共三十五个名称，包括 [tsys_sum]、[fr_eval_word_map] 和 [map_cmon_id]）；[tsys_nu_hom] 和 [tsys_nu_hom_pure] 绑定三个，进一步的绑定张量幂；通过 T 或 K 的三十个名称绑定六个，u、p 以及四个级别 [FreeRngAb] 超过了 [Ab] 的内容（[TSys_EM_iso] 绑定 u、p、c 以及其中四个中的三个，c 高于 u 和 p，来自 Instance/Cat.v 的 [Cat@{c u u u p}]）；[Rng_TSys_iso] 绑定 u、p、c 以及四个；并且三次回读比较跨复合绑定这四个中的另一份复本，总共九个级别。在 Coq 8.19.2 和 8.20.1 上的相同级别（FreeMonad.v 的头部）。未交付。（2）在张量的张量上，⊗ 的类似物
 νk(νn1 ⊗ ⋯ ⊗ νnk) = ν_{n1+⋯+nk} 来自 Mac Lane 的 (2)（他在 W 第 145 页用 × 写，它的 ⊗ 形式由读者提供），这需要同构
 A^{⊗n1} ⊗ ⋯ ⊗ A^{⊗nk} ≅ A^{⊗(n1+⋯+nk)}：词的词的读法代替了它。Mac Lane 推论的类似物
 （由 ν₀、一个结合的 ν₂，以及 νₙ₊₁ = νₙ(ν₂ ⊗ 1) 给出的表征）：FreeMonad.v 的环方法代替了它。与 Ab^T 系统的严格同构（上面拒绝）。
 [Rng_TSys_iso]（R32）的身份分量：它是复合的，而不是像 [TSys_EM_iso] 那样由两个分量同构重建（未尝试）。
*)

Section Systems.

Universes u p.

(* ------------------------------------------------------------------------ *)
(** ** Systems on an abelian group / ** 阿贝尔群上的系统 *)

(*
 ν on the words over A, respecting each letter and additive in each
 letter, so that its restriction to the words of length n is a
 homomorphism νₙ : A^{⊗n} → A ([tsys_nu_hom] below); with ν₁ = 1 and
 Mac Lane's (2), read on words of words. 

 --------
 ν 在 A 上的词语上，尊重每个字母以及每个字母中的加法元素，使得其对长度为 n 的词语的限制是一个同态 νₙ : A^{⊗n} → A（下面的 [tsys_nu_hom]）；且 ν₁ = 1，并且 Mac Lane 的 (2)，应用于词语的词语上阅读。
*)
Record TSystem@{+} (A : Ab@{u p}) : Type@{p} := {
  tnu : list (carrier (cmon_setoid A)) → carrier (cmon_setoid A);
  tnu_letter : ∀ (u v : list (carrier (cmon_setoid A)))
                 (a b : carrier (cmon_setoid A)),
    a ≈ b → tnu (u ++ a :: v) ≈ tnu (u ++ b :: v);
  tnu_lin : ∀ (u v : list (carrier (cmon_setoid A)))
              (a b : carrier (cmon_setoid A)),
    tnu (u ++ cmon_plus A a b :: v)
      ≈ cmon_plus A (tnu (u ++ a :: v)) (tnu (u ++ b :: v));
  tnu_unit : ∀ a : carrier (cmon_setoid A), tnu (a :: nil) ≈ a;
  tnu_assoc : ∀ ww : list (list (carrier (cmon_setoid A))),
    tnu (map tnu ww) ≈ tnu (concat ww)
}.

Arguments tnu {A} _ _.
Arguments tnu_letter {A} _ _ _ _ _ _.
Arguments tnu_lin {A} _ _ _ _ _.
Arguments tnu_unit {A} _ _.
Arguments tnu_assoc {A} _ _.

(* The literal νₙ : A^{⊗n} → A: ν extended additively to the sums of words (Instance/Ab/TensorPower.v's [tw_ext]), composed with the injection ιₙ of the n-th tensor power. / 字面量 νₙ : A^{⊗n} → A：ν 以加法方式扩展到单词的和（Instance/Ab/TensorPower.v 的 [tw_ext]），与第 n 次张量幂的注入 ιₙ 组合。 *)
Definition tsys_sum@{+} {A : Ab@{u p}} (σ : TSystem A) :
  TWAb A ~{Ab@{u p}}~> A := tw_ext A (tnu σ) (tnu_letter σ) (tnu_lin σ).

Definition tsys_nu_hom@{+} {A : Ab@{u p}} (σ : TSystem A) (n : nat) :
  A ^⨂ n ~{Ab@{u p}}~> A := tsys_sum σ ∘[Ab@{u p}] tw_iota n.

(* On the pure tensor a₁ ⊗ … ⊗ aₙ ⊗ 1 it is ν⟨a₁ … aₙ⟩. / 在纯张量 a₁ ⊗ … ⊗ aₙ ⊗ 1 上，它是 ν⟨a₁ … aₙ⟩。 *)
Lemma tsys_nu_hom_pure@{+} {A : Ab@{u p}} (σ : TSystem A)
  (w : list (carrier (cmon_setoid A))) :
  cmon_map (tsys_nu_hom σ (length w)) (tw_pure w) ≈ tnu σ w.
Proof.
  symmetry.
  exact (proper_morphism (cmon_map (tsys_sum σ)) _ _ (tw_word_iota A w)).
Qed.

(*
 A map of systems: f νₙ = ν'ₙ f^{⊗n}, f^{⊗n} being the letterwise map
 on words. 

 --------
 系统的映射：f νₙ = ν'ₙ f^{⊗n}，f^{⊗n} 是作用在单词上的逐字映射。
*)
Definition TSystemHom@{+} {A B : Ab@{u p}} (σ : TSystem A) (τ : TSystem B)
  (f : A ~{Ab@{u p}}~> B) : Type@{p} :=
  ∀ w : list (carrier (cmon_setoid A)),
    cmon_map f (tnu σ w) ≈ tnu τ (map (cmon_map f) w).

(* ------------------------------------------------------------------------ *)
(** ** An algebra gives a system / ** 一个代数提供一个系统 *)

(* T f on a word is the word of the images, on the nose. / T f 在一个词上是图像的词，正中鼻子。 *)
Lemma fr_eval_word_map@{+} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (l : list (carrier (cmon_setoid A))) :
  fr_eval (free_rng_ab_insert B ∘[Ab@{u p}] f) (fr_word l)
    = fr_word (map (cmon_map f) l).
Proof.
  induction l as [ | a l IH ]; [ reflexivity | ].
  destruct l as [ | b l ]; [ reflexivity | ].
  change (fr_mul (fr_gen (cmon_map f a))
            (fr_eval (free_rng_ab_insert B ∘[Ab@{u p}] f) (fr_word (b :: l)))
          = fr_mul (fr_gen (cmon_map f a))
              (fr_word (map (cmon_map f) (b :: l)))).
  rewrite IH. reflexivity.
Qed.

(* μ on a word of words is the word of their concatenation, up to ≈. / μ 在一组词上的作用是它们连接后的词，直到 ≈。 *)
Lemma fr_eval_id_word_concat@{+} {A : Ab@{u p}}
  (ww : list (list (carrier (cmon_setoid A)))) :
  fr_eq (fr_eval (@id Ab@{u p} (fobj[TF] A))
           (@fr_word (fobj[TF] A) (map fr_word ww)))
        (fr_word (concat ww)).
Proof.
  induction ww as [ | w ww IH ].
  - apply fr_refl.
  - refine (fre_trans (fr_eval_respects (FreeRngAb A)
                         (@id Ab@{u p} (fobj[TF] A)) _ _
                         (fr_word_cons (fobj[TF] A) (fr_word w)
                            (map fr_word ww))) _).
    simpl concat.
    refine (fre_trans (fre_mul (fr_refl _) IH) _).
    exact (fre_sym (fr_word_app A w (concat ww))).
Qed.

Section AlgSys.

Context {A : Ab@{u p}} (α : @TAlgebra Ab@{u p} TF TM A).

Local Notation h := (cmon_map (t_alg[α])).

Definition alg_nu@{+} (w : list (carrier (cmon_setoid A))) :
  carrier (cmon_setoid A) := h (fr_word w).

Definition alg_system@{+} : TSystem A.
Proof using α.
  unshelve refine {| tnu := alg_nu |}.
  - intros u v a b H. unfold alg_nu.
    apply (proper_morphism (cmon_map (t_alg[α]))).
    exact (fr_word_letter A u v a b H).
  - intros u v a b. unfold alg_nu.
    refine (transitivity (proper_morphism (cmon_map (t_alg[α])) _ _
                            (fr_word_lin A u v a b)) _).
    exact (cmon_map_plus (t_alg[α]) _ _).
  - intro a. exact (ralg_unit α a).
  - intro ww. unfold alg_nu.
    pose proof (ralg_action α (@fr_word (fobj[TF] A) (map fr_word ww))) as H.
    rewrite (fr_eval_word_map (t_alg[α]) (map fr_word ww)) in H.
    rewrite map_map in H.
    refine (transitivity H _).
    apply (proper_morphism (cmon_map (t_alg[α]))).
    exact (fr_eval_id_word_concat ww).
Defined.

End AlgSys.

(* ν of an algebra's system is the structure map on the word; ν₀ is the unit and ν₂ the product of the algebra's ring, on the nose. / 一个代数系统的 ν 是作用于字的结构映射；ν₀ 是单位，ν₂ 是代数环的乘法，正是如此。 *)
Example alg_system_nu@{+} {A : Ab@{u p}} (α : @TAlgebra Ab@{u p} TF TM A)
  (w : list (carrier (cmon_setoid A))) :
  tnu (alg_system α) w = cmon_map (t_alg[α]) (fr_word w) := eq_refl.

Example alg_system_nil@{+} {A : Ab@{u p}} (α : @TAlgebra Ab@{u p} TF TM A) :
  tnu (alg_system α) nil = ralg_one α := eq_refl.

Example alg_system_pair@{+} {A : Ab@{u p}} (α : @TAlgebra Ab@{u p} TF TM A)
  (a b : carrier (cmon_setoid A)) :
  tnu (alg_system α) (a :: b :: nil) = ralg_mul α a b := eq_refl.

(* An algebra map is a map of the systems. / 代数映射是系统的映射。 *)
Lemma alg_hom_TSystemHom@{+} {A B : Ab@{u p}}
  (α : @TAlgebra Ab@{u p} TF TM A) (β : @TAlgebra Ab@{u p} TF TM B)
  (f : A ~{Ab@{u p}}~> B) :
  f ∘ t_alg[α] ≈ t_alg[β] ∘ fmap[TF] f →
  TSystemHom (alg_system α) (alg_system β) f.
Proof.
  intros H w. simpl.
  refine (transitivity (H (fr_word w)) _). simpl.
  apply (proper_morphism (cmon_map (t_alg[β]))).
  refine (fre_trans (T_map_relabel f (fr_word w)) _).
  rewrite fr_eval_word_map. apply fr_refl.
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** A system gives a ring: 1 = ν⟨⟩ and a·b = ν⟨a b⟩ / * ** 一个系统给出一个环：1 = ν⟨⟩ 且 a·b = ν⟨a b⟩ *)

Section SysRing.

Context {A : Ab@{u p}} (σ : TSystem A).

Local Notation L := (carrier (cmon_setoid A)).

Definition sys_one@{+} : L := tnu σ nil.

Definition sys_mul@{+} (a b : L) : L := tnu σ (a :: b :: nil).

Lemma sys_mul_respects@{+} : Proper (equiv ==> equiv ==> equiv) sys_mul.
Proof.
  intros a a' Ha b b' Hb. unfold sys_mul.
  refine (transitivity (tnu_letter σ nil (b :: nil) a a' Ha) _).
  exact (tnu_letter σ (a' :: nil) nil b b' Hb).
Qed.

(* (2) at a word of two words. / (2) 在一个由两个单词组成的词处。 *)
Lemma sys_nu_pair@{+} (u v : list L) :
  tnu σ (tnu σ u :: tnu σ v :: nil) ≈ tnu σ (u ++ v).
Proof.
  pose proof (tnu_assoc σ (u :: v :: nil)) as H. simpl in H.
  rewrite app_nil_r in H. exact H.
Qed.

Lemma sys_mul_assoc@{+} a b c :
  sys_mul (sys_mul a b) c ≈ sys_mul a (sys_mul b c).
Proof.
  unfold sys_mul.
  transitivity (tnu σ (tnu σ (a :: b :: nil) :: tnu σ (c :: nil) :: nil)).
  { exact (tnu_letter σ (_ :: nil) nil _ _ (symmetry (tnu_unit σ c))). }
  refine (transitivity (sys_nu_pair (a :: b :: nil) (c :: nil)) _).
  refine (transitivity (symmetry (sys_nu_pair (a :: nil) (b :: c :: nil))) _).
  exact (tnu_letter σ nil (_ :: nil) _ _ (tnu_unit σ a)).
Qed.

Lemma sys_one_l@{+} a : sys_mul sys_one a ≈ a.
Proof.
  unfold sys_mul, sys_one.
  transitivity (tnu σ (tnu σ nil :: tnu σ (a :: nil) :: nil)).
  { exact (tnu_letter σ (_ :: nil) nil _ _ (symmetry (tnu_unit σ a))). }
  refine (transitivity (sys_nu_pair nil (a :: nil)) _).
  exact (tnu_unit σ a).
Qed.

Lemma sys_one_r@{+} a : sys_mul a sys_one ≈ a.
Proof.
  unfold sys_mul, sys_one.
  transitivity (tnu σ (tnu σ (a :: nil) :: tnu σ nil :: nil)).
  { exact (tnu_letter σ nil (_ :: nil) _ _ (symmetry (tnu_unit σ a))). }
  refine (transitivity (sys_nu_pair (a :: nil) nil) _).
  exact (tnu_unit σ a).
Qed.

Lemma sys_distr_l@{+} a b c :
  sys_mul a (cmon_plus A b c) ≈ cmon_plus A (sys_mul a b) (sys_mul a c).
Proof. exact (tnu_lin σ (a :: nil) nil b c). Qed.

Lemma sys_distr_r@{+} a b c :
  sys_mul (cmon_plus A a b) c ≈ cmon_plus A (sys_mul a c) (sys_mul b c).
Proof. exact (tnu_lin σ nil (c :: nil) a b). Qed.

Lemma sys_mul_zero_l@{+} a : sys_mul (cmon_zero A) a ≈ cmon_zero A.
Proof.
  apply (ab_cancel_l A (sys_mul (cmon_zero A) a)).
  refine (transitivity (symmetry (sys_distr_r _ _ a)) _).
  refine (transitivity (sys_mul_respects _ _ (cmon_plus_zero_l A _)
                          _ _ (reflexivity a)) _).
  exact (symmetry (cmon_plus_zero_r A _)).
Qed.

Lemma sys_mul_zero_r@{+} a : sys_mul a (cmon_zero A) ≈ cmon_zero A.
Proof.
  apply (ab_cancel_l A (sys_mul a (cmon_zero A))).
  refine (transitivity (symmetry (sys_distr_l a _ _)) _).
  refine (transitivity (sys_mul_respects _ _ (reflexivity a)
                          _ _ (cmon_plus_zero_l A _)) _).
  exact (symmetry (cmon_plus_zero_r A _)).
Qed.

Definition sys_ring@{+} : RingObject := {|
  ring_rig := {|
    rig_setoid := cmon_setoid A;
    rig_zero := cmon_zero A;
    rig_add := cmon_plus A;
    rig_one := sys_one;
    rig_mul := sys_mul;
    rig_add_respects := cmon_plus_respects A;
    rig_mul_respects := sys_mul_respects;
    rig_add_assoc := cmon_plus_assoc A;
    rig_add_comm := cmon_plus_comm A;
    rig_add_zero_l := cmon_plus_zero_l A;
    rig_mul_assoc := sys_mul_assoc;
    rig_mul_one_l := sys_one_l;
    rig_mul_one_r := sys_one_r;
    rig_distr_l := sys_distr_l;
    rig_distr_r := sys_distr_r;
    rig_mul_zero_l := sys_mul_zero_l;
    rig_mul_zero_r := sys_mul_zero_r;
    rig_prop := cmon_prop A
  |};
  ring_neg := ab_neg A;
  ring_neg_respects := ab_neg_respects A;
  ring_neg_l := ab_neg_left A
|}.

(* "νₙ is the n-fold product": ν of a word is the product of its letters in the ring of the system. / “νₙ 是 n 重乘积”：一个单词的 ν 是系统环中其字母的乘积 *)
Lemma sys_nu_is_product@{+} (w : list L) :
  fr_eval (R := sys_ring) (@id Ab@{u p} A) (fr_word w) ≈ tnu σ w.
Proof.
  induction w as [ | a w IH ]; [ reflexivity | ].
  destruct w as [ | b w ]; [ symmetry; exact (tnu_unit σ a) | ].
  change (sys_mul a (fr_eval (R := sys_ring) (@id Ab@{u p} A)
                       (fr_word (b :: w)))
            ≈ tnu σ (a :: b :: w)).
  transitivity (sys_mul a (tnu σ (b :: w))).
  { apply sys_mul_respects; [ reflexivity | exact IH ]. }
  unfold sys_mul.
  refine (transitivity (tnu_letter σ nil (_ :: nil) _ _
                          (symmetry (tnu_unit σ a))) _).
  exact (sys_nu_pair (a :: nil) (b :: w)).
Qed.

End SysRing.

(* A map of systems is a ring map of their rings. / 系统的地图是它们环的环形地图。 *)
Definition sys_ring_map@{+} {A B : Ab@{u p}} {σ : TSystem A} {τ : TSystem B}
  (f : A ~{Ab@{u p}}~> B) (Hf : TSystemHom σ τ f) :
  sys_ring σ ~{Rng@{u p}}~> sys_ring τ.
Proof.
  unshelve refine (@Build_RigHom (sys_ring σ) (sys_ring τ)
                     (cmon_map f) _ _ _ _).
  - exact (cmon_map_zero f).
  - exact (cmon_map_plus f).
  - exact (Hf nil).
  - intros a b. exact (Hf (a :: b :: nil)).
Defined.

(* ------------------------------------------------------------------------ *)
(** ** The category of systems / ** 系统类别 *)

Record TSysObj@{+} : Type@{u} := {
  tsys_ab : Ab@{u p};
  tsys_str : TSystem tsys_ab
}.

Definition TSysHom@{+} (S S' : TSysObj) : Type@{p} :=
  { f : tsys_ab S ~{Ab@{u p}}~> tsys_ab S'
  & TSystemHom (tsys_str S) (tsys_str S') f }.

Definition TSysHom_Setoid@{+} (S S' : TSysObj) :
  Setoid@{p p} (TSysHom S S').
Proof.
  refine {| equiv := fun f g =>
              @equiv _ (@homset Ab@{u p} (tsys_ab S) (tsys_ab S'))
                (`1 f) (`1 g) |}.
  constructor.
  - intros f. reflexivity.
  - intros f g H. symmetry. exact H.
  - intros f g k H1 H2. transitivity (`1 g); assumption.
Defined.

(* The standard library's [map_id], by conversion. / 标准库的 [map_id]，通过转换。 *)
Lemma map_cmon_id@{+} {A : Ab@{u p}} (w : list (carrier (cmon_setoid A))) :
  map (cmon_map (@id Ab@{u p} A)) w = w.
Proof. exact (map_id w). Qed.

Definition TSys_id@{+} (S : TSysObj) : TSysHom S S.
Proof.
  exists (@id Ab@{u p} (tsys_ab S)).
  intro w. simpl. rewrite map_cmon_id. reflexivity.
Defined.

Definition TSys_compose@{+} {S S' S'' : TSysObj}
  (g : TSysHom S' S'') (f : TSysHom S S') : TSysHom S S''.
Proof.
  exists (`1 g ∘[Ab@{u p}] `1 f).
  intro w. simpl.
  transitivity (cmon_map (`1 g) (tnu (tsys_str S') (map (cmon_map (`1 f)) w))).
  - apply (proper_morphism (cmon_map (`1 g))). exact (`2 f w).
  - refine (transitivity (`2 g _) _).
    rewrite map_map. reflexivity.
Defined.

(* The category of Mac Lane's systems ⟨A, ν₀, ν₁, …⟩. / Mac Lane 系统的范畴 ⟨A, ν₀, ν₁, …⟩。 *)
Definition TSys@{+} : Category@{u p p}.
Proof.
  unshelve refine
    {| obj     := TSysObj
     ; hom     := TSysHom
     ; homset  := TSysHom_Setoid
     ; id      := TSys_id
     ; compose := @TSys_compose |}.
  - intros S S' S'' f f' Hf g g' Hg a. simpl.
    transitivity (cmon_map (`1 f) (cmon_map (`1 g') a)).
    + apply (proper_morphism (cmon_map (`1 f))). exact (Hg a).
    + exact (Hf _).
  - intros S S' f a. reflexivity.
  - intros S S' f a. reflexivity.
  - intros S1 S2 S3 S4 f g k a. reflexivity.
  - intros S1 S2 S3 S4 f g k a. reflexivity.
Defined.

(* Systems to rings, and so to algebras through K. / 系统到环，再通过 K 到代数。 *)
Definition TSys_to_Rng@{+} : TSys ⟶ Rng@{u p}.
Proof.
  unshelve refine
    (@Build_Functor TSys Rng@{u p} (fun S => sys_ring (tsys_str S))
       (fun S S' f => sys_ring_map (`1 f) (`2 f)) _ _ _).
  - intros S S' f g H. exact H.
  - intros S a. reflexivity.
  - intros S S' S'' f g a. reflexivity.
Defined.

Definition TSys_to_EM@{+} : TSys ⟶ RngAlg := Rng_K ◯ TSys_to_Rng.

Definition EM_to_TSys@{+} : RngAlg ⟶ TSys.
Proof.
  unshelve refine
    (@Build_Functor RngAlg TSys
       (fun x => {| tsys_ab := projT1 x; tsys_str := alg_system (projT2 x) |})
       (fun x y f =>
          existT _ (t_alg_hom[f])
            (alg_hom_TSystemHom (projT2 x) (projT2 y) (t_alg_hom[f])
               (@t_alg_hom_commutes _ _ _ _ _ _ _ f)))
       _ _ _).
  - intros x y f g H a. exact (H a).
  - intros x a. reflexivity.
  - intros x y z f g a. reflexivity.
Defined.

(*
 The algebra round trip through the systems, with the identity as its
 component: the system of an algebra has the algebra's ring. 

 --------
 代数通过系统的往返，其中恒等元作为其组成部分：一个代数的系统具有该代数的环。
*)
Definition TSys_EM_counit_iso@{+} (x : RngAlg) :
  @Isomorphism RngAlg (fobj[TSys_to_EM ◯ EM_to_TSys] x) x.
Proof.
  unshelve refine
    (@Build_Isomorphism RngAlg (fobj[TSys_to_EM ◯ EM_to_TSys] x) x
       (@Build_TAlgebraHom Ab@{u p} TF TM (projT1 x) (projT1 x)
          (projT2 (fobj[TSys_to_EM ◯ EM_to_TSys] x)) (projT2 x)
          (@id Ab@{u p} (projT1 x)) _)
       (@Build_TAlgebraHom Ab@{u p} TF TM (projT1 x) (projT1 x)
          (projT2 x) (projT2 (fobj[TSys_to_EM ◯ EM_to_TSys] x))
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

(* The system round trip, with the identity as its component. / 系统往返，身份作为其组成部分。 *)
Definition TSys_EM_unit_iso@{+} (S : TSys) :
  @Isomorphism TSys (fobj[EM_to_TSys ◯ TSys_to_EM] S) S.
Proof.
  unshelve refine
    (@Build_Isomorphism TSys (fobj[EM_to_TSys ◯ TSys_to_EM] S) S
       (existT _ (@id Ab@{u p} (tsys_ab S)) _)
       (existT _ (@id Ab@{u p} (tsys_ab S)) _) _ _).
  - intro w. simpl. rewrite map_cmon_id.
    exact (sys_nu_is_product (tsys_str S) w).
  - intro w. simpl. rewrite map_cmon_id.
    symmetry. exact (sys_nu_is_product (tsys_str S) w).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(*
 Mac Lane's "corresponding description of T-algebras": the systems are
 isomorphic in Cat to Ab^T, every component of both natural isomorphisms
 the identity. 

 --------
 Mac Lane 的“关于 T-代数的对应描述”：这些系统在 Cat 中与 Ab^T 同构，两个自然同构的每个分量都是恒等映射。
*)
Definition TSys_EM_iso@{c +} :
  @Isomorphism Cat@{c u u u p} TSys RngAlg.
Proof.
  unshelve refine
    (@Build_Isomorphism Cat@{c u u u p} TSys RngAlg
       TSys_to_EM EM_to_TSys _ _).
  - exists (fun x => TSys_EM_counit_iso x).
    intros x y f a. reflexivity.
  - exists (fun S => TSys_EM_unit_iso S).
    intros S S' f a. reflexivity.
Defined.

(* The rings are the systems. / 这些环是系统。 *)
Definition Rng_TSys_iso@{c +} :
  @Isomorphism Cat@{c u u u p} Rng@{u p} TSys :=
  iso_compose (iso_sym TSys_EM_iso) Rng_EM_iso.

(* ------------------------------------------------------------------------ *)
(** ** Readbacks / ** 回读 *)

Example TSys_EM_iso_to@{+} : to TSys_EM_iso = TSys_to_EM := eq_refl.

Example TSys_EM_iso_from@{+} : from TSys_EM_iso = EM_to_TSys := eq_refl.

(* A system's algebra evaluates in the system's ring: 1 ↦ ν⟨⟩ and ⟨a⟩·⟨b⟩ ↦ ν⟨a b⟩. / 系统的代数在系统的环中计算：1 ↦ ν⟨⟩ 和 ⟨a⟩·⟨b⟩ ↦ ν⟨a b⟩。 *)
Example TSys_to_EM_alg@{+} (S : TSys) (t : FRTerm (tsys_ab S)) :
  cmon_map (t_alg[projT2 (fobj[TSys_to_EM] S)]) t
    = fr_eval (R := sys_ring (tsys_str S)) (@id Ab@{u p} (tsys_ab S)) t
  := eq_refl.

Example TSys_to_EM_one@{+} (S : TSys) :
  cmon_map (t_alg[projT2 (fobj[TSys_to_EM] S)]) fr_one
    = tnu (tsys_str S) nil := eq_refl.

Example TSys_to_EM_pair@{+} (S : TSys)
  (a b : carrier (cmon_setoid (tsys_ab S))) :
  cmon_map (t_alg[projT2 (fobj[TSys_to_EM] S)])
    (fr_mul (fr_gen a) (fr_gen b)) = tnu (tsys_str S) (a :: b :: nil)
  := eq_refl.

Example EM_to_TSys_nu@{+} (x : RngAlg)
  (w : list (carrier (cmon_setoid (projT1 x)))) :
  tnu (tsys_str (fobj[EM_to_TSys] x)) w = cmon_map (t_alg[projT2 x]) (fr_word w)
  := eq_refl.

(* ν₂ of an algebra's system is the product of its ring. / 一个代数系统的 ν₂ 是其环的乘积。 *)
Example EM_to_TSys_pair@{+} (x : RngAlg)
  (a b : carrier (cmon_setoid (projT1 x))) :
  tnu (tsys_str (fobj[EM_to_TSys] x)) (a :: b :: nil)
    = rig_mul (fobj[EM_to_Rng] x) a b := eq_refl.

(*
 The system round trip keeps the group, ν₀, ν₂ and the maps on the nose,
 and returns ν₁ as the identity. 

 --------
 系统回路保持群、ν₀、ν₂ 和映射不变，并将 ν₁ 返回为恒等映射。
*)
Example TSys_rt_ab@{+} (S : TSys) :
  tsys_ab (fobj[EM_to_TSys ◯ TSys_to_EM] S) = tsys_ab S := eq_refl.

Example TSys_rt_nil@{+} (S : TSys) :
  tnu (tsys_str (fobj[EM_to_TSys ◯ TSys_to_EM] S)) nil
    = tnu (tsys_str S) nil := eq_refl.

Example TSys_rt_letter@{+} (S : TSys) (a : carrier (cmon_setoid (tsys_ab S))) :
  tnu (tsys_str (fobj[EM_to_TSys ◯ TSys_to_EM] S)) (a :: nil) = a
  := eq_refl.

Example TSys_rt_pair@{+} (S : TSys)
  (a b : carrier (cmon_setoid (tsys_ab S))) :
  tnu (tsys_str (fobj[EM_to_TSys ◯ TSys_to_EM] S)) (a :: b :: nil)
    = tnu (tsys_str S) (a :: b :: nil) := eq_refl.

Example TSys_rt_hom@{+} {S S' : TSys} (f : S ~{TSys}~> S') :
  `1 (fmap[EM_to_TSys ◯ TSys_to_EM] f) = `1 f := eq_refl.

(* ...and ν at every word up to ≈. / ...以及在每个词上的 ν 直到 ≈。 *)
Lemma TSys_rt_nu@{+} (S : TSys) (w : list (carrier (cmon_setoid (tsys_ab S)))) :
  tnu (tsys_str (fobj[EM_to_TSys ◯ TSys_to_EM] S)) w ≈ tnu (tsys_str S) w.
Proof. exact (sys_nu_is_product (tsys_str S) w). Qed.

(* The algebra round trip keeps the group and the maps on the nose. / 代数往返保持群和映射的精确不变。 *)
Example EM_TSys_rt_carrier@{+} (x : RngAlg) :
  projT1 (fobj[TSys_to_EM ◯ EM_to_TSys] x) = projT1 x := eq_refl.

Example EM_TSys_rt_alg_hom@{+} {x y : RngAlg} (f : x ~{RngAlg}~> y) :
  t_alg_hom[fmap[TSys_to_EM ◯ EM_to_TSys] f] = t_alg_hom[f] := eq_refl.

(* Every component of the two natural isomorphisms is the identity. / 这两个自然同构的每一个组成部分都是恒等映射。 *)
Example TSys_EM_iso_to_from_component@{+} (x : RngAlg) :
  (t_alg_hom[to (projT1 (iso_to_from TSys_EM_iso) x)],
   t_alg_hom[from (projT1 (iso_to_from TSys_EM_iso) x)])
    = (@id Ab@{u p} (projT1 x), @id Ab@{u p} (projT1 x)) := eq_refl.

Example TSys_EM_iso_from_to_component@{+} (S : TSys) :
  (`1 (to (projT1 (iso_from_to TSys_EM_iso) S)),
   `1 (from (projT1 (iso_from_to TSys_EM_iso) S)))
    = (@id Ab@{u p} (tsys_ab S), @id Ab@{u p} (tsys_ab S)) := eq_refl.

(* The system of a ring R: ν⟨⟩ = 1, ν⟨a⟩ = a, ν⟨a b⟩ = a·b, and ν of a word the product of its letters, bracketed to the right. / 环 R 的系统：ν⟨⟩ = 1，ν⟨a⟩ = a，ν⟨a b⟩ = a·b，而 ν 对一个词是其字母的乘积，括号向右。 *)
Example Rng_system_nu@{+} (R : Rng@{u p})
  (w : list (carrier (rig_setoid R))) :
  tnu (tsys_str (fobj[EM_to_TSys ◯ Rng_K] R)) w
    = fr_eval (@id Ab@{u p} (Rng_Forget_Ab R))
        (@fr_word (Rng_Forget_Ab R) w) := eq_refl.

Example Rng_system_nil@{+} (R : Rng@{u p}) :
  tnu (tsys_str (fobj[EM_to_TSys ◯ Rng_K] R)) nil = rig_one R := eq_refl.

Example Rng_system_letter@{+} (R : Rng@{u p}) (a : carrier (rig_setoid R)) :
  tnu (tsys_str (fobj[EM_to_TSys ◯ Rng_K] R)) (a :: nil) = a := eq_refl.

Example Rng_system_pair@{+} (R : Rng@{u p}) (a b : carrier (rig_setoid R)) :
  tnu (tsys_str (fobj[EM_to_TSys ◯ Rng_K] R)) (a :: b :: nil)
    = rig_mul R a b := eq_refl.

End Systems.

(* An [Arguments] declared inside a section does not survive its [End]. / 在一个部分中声明的 [Arguments] 在其 [End] 之后不会保留。 *)
Arguments tnu {A} _ _.
Arguments tnu_letter {A} _ _ _ _ _ _.
Arguments tnu_lin {A} _ _ _ _ _.
Arguments tnu_unit {A} _ _.
Arguments tnu_assoc {A} _ _.
