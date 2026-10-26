Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Mon.Coproduct.
Require Import Category.Instance.Mon.Free.
Require Import Category.Instance.Smgrp.
Require Import Category.Instance.Smgrp.Word.
Require Import Category.Instance.Mon.Word.

Generalizable All Variables.

(* * * W₀-algebras as strings of operations ν₀, ν₁, … / * * W₀-代数作为操作序列 ν₀, ν₁, … *)

(*
 Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 Springer GTM 5, 1998, §VI.4, Exercise 1, printed p. 146 (PDF
 p. 155) — maclane:VI.4:ex1
 Book: Riehl, “Category Theory in Context”, Example 5.2.6(iii),
 printed pp. 189-190 (PDF pp. 209-210) — riehl:5.2:example6
 nLab: https://ncatlab.org/nlab/show/free+monoid
 nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad

 WHAT THE BOOKS SAY, read from the page image and the PDF.  Mac Lane:
 “Show that a W₀-algebra is a set M with a string ν₀, ν₁, … of n-ary
 operations νₙ, where ν₀ : * → M is the unit of the monoid M and νₙ is
 the n-fold product.”  His Proposition 2 (p. 145) gives the W-algebras
 as systems ⟨S, ν1, ν2, …⟩ with ν1 = 1 and νk(νn1 × ⋯ × νnk) =
 ν_{n1+⋯+nk} (2), which #470's Instance/Smgrp/Word.v delivers; this
 file is its W₀ analogue, with ν₀ added.  Riehl reads the square
 (5.2.7) on “a list ((a11, …, a1m1), …, (an1, …, anmn)) of n
 varying-length lists”: “the result of applying the (m1 + ⋯ + mn)-ary
 operation to the concatenated list is the same as applying the n-ary
 operation to the results of applying the mi-ary operations to each
 sublist”.

 THE FAMILIES.  [NAry0 X] is ν₀ ([nu_zero]) with #470's [NAry X] for
 ν_{n+1} : X^(n+1) → X ([nu_pos]); [nu0 ν n] : Xⁿ → X on Instance/Mon/
 Word.v's [Tup0 X n], and [nu0_list] reads the family on W₀ X = lists
 (ν on ⟨⟩, ⟨x⟩ and ⟨x y⟩ is ν₀, ν₁ x and ν₂(x, y) at [eq_refl]:
 [nu0_list_nil], [nu0_list_letter], [nu0_list_pair]).  ν₁ = 1 is
 #470's [nu_unit] of the positive part, and (2) is [nu0_assoc]: for
 every word of words, ν of the values of the inner words ≈ ν of their
 concatenation [wconcat], which IS μ (Word.v's [W0_join_fun]) — Riehl's
 reading on lists of lists.  The form over tuples of tuples, Mac
 Lane's own, would need a juxtaposition of tuples by cases on the
 lengths (n + m is not convertible through [Tup]'s S (n + m)) and more
 of the dictionary: not built.

 BOTH WAYS AND ON MORPHISMS.  An algebra gives a family
 ([alg_NAry0]: ν₀ = α⟨⟩ and ν_{n+1} = α on X^(n+1), [alg_NAry0_zero],
 [alg_NAry0_at] at [eq_refl]) satisfying ν₁ = 1 ([alg_NAry0_unit]) and
 (2) ([alg_NAry0_assoc]); a family with the two conditions is an
 algebra ([NAry0_alg]) whose structure map is [nu0_list]
 ([NAry0_alg_map], at [eq_refl]), whose unit law IS ν₁ = 1 by
 conversion and whose action law is (2) modulo W₀ f ≈ the letterwise
 map.  Family → algebra → family keeps ν₀ at [eq_refl]
 ([NAry0_rt_zero]) and ν_{n+1} at ≈ ([NAry0_rt_pos], which also holds
 at Leibniz =, STRENGTHS below; at n = 1 at [eq_refl],
 [NAry0_rt_pos_pair]): refused at [eq_refl] at a variable n and as the
 whole family (Test/ProbeWord471.v, R15 and R16), weaker than #470's
 [NAry_round_trip] at [eq_refl], because W₀'s carrier is lists and the
 family is on tuples (the length of a tuple's list is stuck on n,
 [nu0_list_tup_to_list]).  Algebra → family → algebra returns the
 structure map at ≈ ([alg_round_trip0]).  The morphism clause, f νₙ =
 ν'ₙ fⁿ for every n ≥ 0 ([NAry0_hom]), both ways: [alg_hom_NAry0_hom],
 [NAry0_hom_alg_hom].

 “ν₀ IS THE UNIT OF THE MONOID M AND νₙ THE n-FOLD PRODUCT”.  For an
 algebra α, ν₀ IS the unit of its monoid (Word.v's [alg_monoid]) and
 ν₂ its multiplication at [eq_refl] ([alg_nu0_is_unit],
 [alg_nu2_is_mul]), and νₙ is the n-fold product at ≈
 ([alg_nu_is_fold]).  For a monoid M, the system of K M has ν₀ the
 unit and ν₂(x, y) = x · (y · 1) at [eq_refl] ([Mon_system_zero],
 [Mon_system_pair]) and νₙ the n-fold product at each n by cases
 ([Mon_system_nu], refused at a variable n, R21).

 AS A CATEGORY.  [W0Sys], the systems ⟨S, ν₀, ν₁, …⟩ with ν₁ = 1 and
 (2) ([W0System]) and the maps commuting with every νₙ, is isomorphic
 in Cat to Set^{W₀} ([W0Sys_EM_iso]): its legs are [W0Sys_to_EM] and
 [EM_to_W0Sys] at [eq_refl] ([W0Sys_EM_iso_to], [W0Sys_EM_iso_from])
 and every component of both natural isomorphisms is the identity, to
 and from, at [eq_refl] ([W0Sys_EM_iso_to_from_component],
 [W0Sys_EM_iso_from_to_component]).  The system round trip keeps the
 set, ν₀ and the maps at [eq_refl] ([W0Sys_rt_set], [W0Sys_rt_zero],
 [W0Sys_rt_hom]), and the algebra round trip the carrier and the maps
 ([EM_W0Sys_rt_carrier], [EM_W0Sys_rt_alg_hom]); refused at [eq_refl]:
 the family (R17), the whole system (R18), the whole algebra (R19) and
 the composite against the identity functor (R20).  Mac Lane's
 exercise as a statement about categories is [Mon_W0Sys_iso :
 Mon ≅[Cat] W0Sys], the composite of Word.v's [Mon_EM_iso] with the
 inverse of [W0Sys_EM_iso].  An isomorphism in Cat is, by
 Instance/Cat.v, an equivalence of categories.

 STRENGTHS.  Every [Example] holds at [eq_refl], and
 Test/ProbeWord471.v restates each one (C58 to C67, C69 to C82).
 Stated at ≈: [alg_nu0_list], [alg_nu_is_fold], [NAry0_rt_pos],
 [nu0_list_tup_to_list], [alg_round_trip0], [Mon_system_nu] and the
 inverse laws of the two isomorphisms in Cat.  Five of these also hold
 at Leibniz =, as restating them with = shows (measured in #471's
 audit and review): [Mon_system_nu] and [alg_nu0_list] by their own
 scripts, [alg_round_trip0] pointwise from [alg_nu0_list], and
 [nu0_list_tup_to_list] and [NAry0_rt_pos] through a sigma equality
 between a tuple and the tuple rebuilt from its list, by induction on
 its length.  They are kept at ≈, the form their uses rewrite with;
 [eq_refl] is refused for the families' round trip (R15, R16) and for
 νₙ of K M at a variable n (R21).  [alg_nu_is_fold], through Word.v's
 [alg_fold], was not restated.  One lemma is a Leibniz equality proved
 by induction, stronger than ≈: [tmap_tup_to_list].
 Ten proofs end [Defined] (counted by token), all load-bearing,
 measured by closing each alone [Qed] in a renamed copy of #471's five
 files and naming the first command that then stops: [NAry0_alg]
 ([NAry0_alg_map]), [W0SystemHom_Setoid], [W0System_id] and
 [W0System_compose] ([W0Sys]), [W0Sys] ([W0Sys_to_EM]), [W0Sys_to_EM]
 and [EM_to_W0Sys] ([W0Sys_EM_counit_iso]), [W0Sys_EM_counit_iso] and
 [W0Sys_EM_unit_iso] ([W0Sys_EM_iso]) and [W0Sys_EM_iso]
 ([W0Sys_EM_iso_to]).  Twelve lemmas end [Qed].

 UNIVERSES, read off [About] (every name, by script).  The families,
 their constructor, fields and readbacks, [nu0_list_respects],
 [nu0_list_tup_to_list] and [tmap_tup_to_list] bind @{o} with caps of
 the standard library only; [NAry0_hom] binds @{o so} with o < so.  The
 section [W0Systems] is over Sets@{o so}; its constants bind o and so
 first and, declared extensible as Word.v's are, the free functor's
 three further levels (four on Coq 8.19 and 8.20) where they mention
 W₀, with [Compose]'s one unless it is held at so (the two functors
 between [W0Sys] and Set^{W₀} and their three readbacks hold it):
 [nu0_assoc], [W0System] with its constructor
 and fields, [W0SystemHom] and the category [W0Sys] bind o and so
 alone, since (2) is stated through [wconcat].  Three readbacks
 comparing across a composite bind a second copy (nine levels), and
 [Mon_W0Sys_iso] binds c with o < c and so < c.  No [Set] and no
 equation in any block.

 NOT DELIVERED.  (2) over tuples of tuples (above).  A strict
 isomorphism of the systems with Set^{W₀} (refused above).  The
 Corollary's analogue for W₀, a characterization by ν₀, ν₁ = 1, an
 associative ν₂ with ν₀ its unit, and νₙ₊₁ = νₙ(ν₂ × 1): the monoid
 route of Word.v ([alg_monoid], [alg_fold], [Mon_EM_iso]) stands in
 for it. 

 --------
 书籍：Mac Lane，《为工作中的数学家准备的范畴》，第2版，Springer GTM 5，1998年，第VI.4节，练习1，印刷版第146页（PDF第155页）— maclane:VI.4:ex1
 书籍：Riehl，《情境中的范畴论》，例5.2.6(iii)，印刷版第189-190页（PDF第209-210页）— riehl:5.2:example6
 nLab：https://ncatlab.org/nlab/show/free+monoid
 nLab：https://ncatlab.org/nlab/show/algebra+over+a+monad书中所述内容，从页面图像和 PDF 阅读。Mac Lane：
 “证明一个 W₀-代数是一个集合 M，具有一列 n 元运算 ν₀, ν₁, …，其中 ν₀ : * → M 是单子 M 的单位，而 νₙ 是 n 重积。” 他的命题 2（第 145 页）给出的 W-代数是系统 ⟨S, ν1, ν2, …⟩，其中 ν1 = 1 并且 νk(νn1 × ⋯ × νnk) = ν_{n1+⋯+nk} (2)，#470 的 Instance/Smgrp/Word.v 给出了此内容；该文件是其 W₀ 的对应版本，添加了 ν₀。Riehl 在“一个 n 个不同长度列表的列表 ((a11, …, a1m1), …, (an1, …, anmn))”上阅读方格 (5.2.7) 时称：“将 (m1 + ⋯ + mn)-元运算应用于拼接列表的结果，与将 n 元运算应用于将 mi-元运算应用于每个子列表的结果相同。”家庭。[NAry0 X] 是 ν₀ ([nu_zero]) ，其中 #470 的 [NAry X] 用于 ν_{n+1} : X^(n+1) → X ([nu_pos])；[nu0 ν n] : Xⁿ → X 在 Instance/Mon/Word.v 的 [Tup0 X n] 上，而 [nu0_list] 读取 W₀ X 上的家庭 = 列表（ν 在 ⟨⟩、⟨x⟩ 和 ⟨x y⟩ 上分别是 ν₀、ν₁ x 和 ν₂(x, y) 在 [eq_refl] : [nu0_list_nil]、[nu0_list_letter]、[nu0_list_pair]）。ν₁ = 1 是 #470 的 [nu_unit] 的正部分，并且 (2) 是 [nu0_assoc] ：对于每一个单词的单词，内部单词的值的 ν ≈ 它们连接的 ν [wconcat] ，这就是 μ (Word.v 的 [W0_join_fun]) —— Riehl 在列表的阅读。基于元组的形式，Mac Lane 自己的，需要按长度（n + m 不能通过 [Tup] 的 S(n + m) 转换）对元组进行并列，并更多词典内容：尚未构建。在两方面及于态射上。一个代数给出一个族
 ( [alg_NAry0] : ν₀ = α⟨⟩ 并且 ν_{n+1} = α 在 X^(n+1) 上,  [alg_NAry0_zero] ,
 [alg_NAry0_at] 在 [eq_refl] ) 满足 ν₁ = 1 ( [alg_NAry0_unit] ) 并且
 (2) ( [alg_NAry0_assoc] ); 满足这两个条件的族是一个代数 ( [NAry0_alg] )，其结构映射是 [nu0_list]
 ( [NAry0_alg_map] ，在 [eq_refl] 上 ), 其单位律为 ν₁ = 1 通过转化得到，且其作用律为 (2) 模 W₀ f ≈ 字母映射。家庭 → 代数 → 家庭保持 ν₀ 在 [eq_refl] ([NAry0_rt_zero]) 并且 ν_{n+1} 在 ≈ ([NAry0_rt_pos]，也同样适用于 Leibniz =, 以下的 STRENGTHS; 在 n = 1 时在 [eq_refl], [NAry0_rt_pos_pair])：在 [eq_refl] 在一个变量 n 处被拒绝，并作为整个家庭 (Test/ProbeWord471.v, R15 和 R16)，比 #470 的 [NAry_round_trip] 在 [eq_refl] 处弱，因为 W₀ 的载体是列表而家庭是在元组上（元组的列表长度固定为 n, [nu0_list_tup_to_list]）。代数 → 家庭 → 代数 返回结构映射在 ≈ ([alg_round_trip0])。态射条款，f νₙ = ν'ₙ fⁿ 对每个 n ≥ 0 ([NAry0_hom])，双向：[alg_hom_NAry0_hom], [NAry0_hom_alg_hom]。ν₀ 是幺半群 M 的单位，νₙ 是 n 重乘积。对于代数 α，ν₀ 是其幺半群的单位（Word.v 的 [alg_monoid]），ν₂ 是在 [eq_refl] 处的乘法（[alg_nu0_is_unit], [alg_nu2_is_mul]），νₙ 是在 ≈ ([alg_nu_is_fold]) 处的 n 重乘积。对于幺半群 M，K M 系统有 ν₀ 作为单位，ν₂(x, y) = x · (y · 1) 在 [eq_refl]（[Mon_system_zero], [Mon_system_pair]）处，νₙ 是每个 n 处按情形定义的 n 重乘积（[Mon_system_nu]，变量 n 拒绝，R21）。作为一个范畴。[W0Sys]，系统 ⟨S, ν₀, ν₁, …⟩，其中 ν₁ = 1，并且 (2) ([W0System]) 以及与每个 νₙ 交换的映射，在 Cat 中同构于 Set^{W₀} ([W0Sys_EM_iso])：它的两条腿是 [W0Sys_to_EM] 和 [EM_to_W0Sys] 在 [eq_refl] ([W0Sys_EM_iso_to], [W0Sys_EM_iso_from]) ，并且两个自然同构的每个分量都在 [eq_refl] ([W0Sys_EM_iso_to_from_component], [W0Sys_EM_iso_from_to_component]) 上是恒等的。从系统往返保持集合、ν₀ 以及在 [eq_refl] ([W0Sys_rt_set], [W0Sys_rt_zero], [W0Sys_rt_hom]) 上的映射，而代数往返保持载体和映射 ([EM_W0Sys_rt_carrier], [EM_W0Sys_rt_alg_hom])；在 [eq_refl] 拒绝：族 (R17)、整个系统 (R18)、整个代数 (R19) 以及对恒等函子复合 (R20)。麦克·莱恩关于范畴的练习是 [Mon_W0Sys_iso : Mon ≅ [Cat] W0Sys]，它是 Word.v 的 [Mon_EM_iso] 与 [W0Sys_EM_iso] 的逆的复合。在 Cat 中的同构，根据 Instance/Cat.v，是范畴的等价。优势。每个 [Example] 在 [eq_refl] 上都成立，Test/ProbeWord471.v 重新陈述了每一个（C58 到 C67，C69 到 C82）。在 ≈ 上陈述：[alg_nu0_list]、[alg_nu_is_fold]、[NAry0_rt_pos]、[nu0_list_tup_to_list]、[alg_round_trip0]、[Mon_system_nu]，以及 Cat 中两个同构的逆律。这些中的五个在 Leibniz = 上也成立，正如用 = 重新陈述所显示的（在 #471 的审计和审核中测量）：[Mon_system_nu] 和 [alg_nu0_list] 由它们自己的脚本，[alg_round_trip0] 从 [alg_nu0_list] 逐点，[nu0_list_tup_to_list] 和 [NAry0_rt_pos] 通过一个元组与从其列表重建的元组之间的 σ 等式，通过对其长度的归纳。它们保留在 ≈ 上，这是它们的使用形式重写的形式；[eq_refl] 对于族的往返（R15，R16）以及 K M 在变量 n 上的 νₙ 被拒绝。[alg_nu_is_fold] 通过 Word.v 的 [alg_fold]，未被重新陈述。一个引理是通过归纳法证明的莱布尼兹等式，比≈更强：[tmap_tup_to_list]。十个证明以[Defined]结束（按标记计算），都是承重的，通过在#471的五个文件的重命名副本中单独闭合每个证明来衡量，并命名随后停止的第一个命令：[NAry0_alg]（[NAry0_alg_map]）、[W0SystemHom_Setoid]、[W0System_id]和[W0System_compose]（[W0Sys]）、[W0Sys]（[W0Sys_to_EM]）、[W0Sys_to_EM]和[EM_to_W0Sys]（[W0Sys_EM_counit_iso]）、[W0Sys_EM_counit_iso]和[W0Sys_EM_unit_iso]（[W0Sys_EM_iso]）以及[W0Sys_EM_iso]（[W0Sys_EM_iso_to]）。十二个引理以[Qed]结束。宇宙，按 [About] 读出（每个名字，通过脚本）。各个族、它们的构造器、字段和读回值，[nu0_list_respects]、[nu0_list_tup_to_list] 和 [tmap_tup_to_list] 仅用标准库的上限绑定 @{o}；[NAry0_hom] 用 o < so 绑定 @{o so}。部分 [W0Systems] 在 Sets@{o so} 上；它的常量先绑定 o 和 so，并且，作为 Word.v 的可扩展声明，自由函子的另外三个层级（在 Coq 8.19 和 8.20 上是四个）中当它们提到 W₀ 时，以及 [Compose] 的一个，除非它在 so 上保持（[W0Sys] 和 Set^{W₀} 之间的两个函子及其三个读回值保持它）：[nu0_assoc]、[W0System] 及其构造器和字段、[W0SystemHom] 以及范畴 [W0Sys] 单独绑定 o 和 so，因为（2）通过 [wconcat] 陈述。三次回读  
 在复合绑定中比较第二个副本（九级），并且  
 [Mon_W0Sys_iso] 绑定 c 与 o < c 和 so < c。没有 [Set]，也没有  
 任何区块中的方程。  

 未交付。（2）在元组的元组上（如上）。一个系统的严格同构与 Set^{W₀}（如上拒绝）。  
 W₀ 的推论类比，由 ν₀, ν₁ = 1 表征，具有 ν₀ 为单位元的结合 ν₂，以及 νₙ₊₁ = νₙ(ν₂ × 1)：Word.v 的单子路径（[alg_monoid], [alg_fold], [Mon_EM_iso]）代表它。
*)

(* ------------------------------------------------------------------------ *)
(* * ** Families ν₀, ν₁, …: ν₀ an element, and #470's [NAry] for n ≥ 1 / * ** 家族 ν₀, ν₁, …：ν₀ 是一个元素，#470 的 [NAry] 对于 n ≥ 1 *)

Record NAry0@{o} (X : SetoidObject@{o o}) : Type@{o} := {
  nu_zero : X;
  nu_pos : NAry@{o} X
}.

Arguments nu_zero {X} _.
Arguments nu_pos {X} _.

(* νₙ : Xⁿ → X for every n ≥ 0. / νₙ ： Xⁿ → X 对于每个 n ≥ 0。 *)
Definition nu0@{o} {X : SetoidObject@{o o}} (ν : NAry0@{o} X) (n : nat) :
  Tup0@{o} X n → X :=
  match n as n0 return Tup0 X n0 → X with
  | O => fun _ => nu_zero ν
  | S n' => nu (nu_pos ν) n'
  end.

(* The family read on W₀ X = lists: the copairing ∐_{n≥0} Xⁿ → X. / 这个族读作 W₀ X = 列表：共对 ∐_{n≥0} Xⁿ → X。 *)
Definition nu0_list@{o} {X : SetoidObject@{o o}} (ν : NAry0@{o} X)
  (l : list X) : X :=
  nu0 ν (length l) (list_to_tup0 l).

Example nu0_list_nil@{o} {X : SetoidObject@{o o}} (ν : NAry0@{o} X) :
  nu0_list ν word0 = nu_zero ν := eq_refl.

Example nu0_list_letter@{o} {X : SetoidObject@{o o}} (ν : NAry0@{o} X)
  (x : X) : nu0_list ν (word1 x) = nu (nu_pos ν) 0 x := eq_refl.

Example nu0_list_pair@{o} {X : SetoidObject@{o o}} (ν : NAry0@{o} X)
  (x y : X) : nu0_list ν (word2 x y) = nu (nu_pos ν) 1 (x, y) := eq_refl.

Lemma nu0_list_respects@{o} {X : SetoidObject@{o o}} (ν : NAry0@{o} X)
  (l l' : list X) : word_eq l l' → nu0_list ν l ≈ nu0_list ν l'.
Proof.
  intro H; destruct H as [|a b u v Hab Huv]; [ reflexivity | ].
  exact (nu_respects (nu_pos ν) _ _ _ _ (list_to_tup_respects a b u v Hab Huv)).
Qed.

(* A morphism of families: f νₙ = ν'ₙ fⁿ for every n ≥ 0. / 族的态射：对于每个 n ≥ 0，有 f νₙ = ν'ₙ fⁿ。 *)
Definition NAry0_hom@{o so} {X Y : SetoidObject@{o o}} (ν : NAry0@{o} X)
  (ν' : NAry0@{o} Y) (f : X ~{Sets@{o so}}~> Y) : Type@{o} :=
  (f (nu_zero ν) ≈ nu_zero ν') * NAry_hom (nu_pos ν) (nu_pos ν') f.

(* ν on the list of a tuple is ν on the tuple, up to ≈ (the length of the list is stuck on n, so not on the nose). / 元组中列表的第 ν 个元素就是元组的第 ν 个元素，约等于（列表的长度固定为 n，所以不完全精确）。 *)
Lemma nu0_list_tup_to_list@{o} {X : SetoidObject@{o o}} (ν : NAry0@{o} X)
  (n : nat) (t : Tup@{o} X n) :
  nu0_list ν (tup_to_list n t) ≈ nu (nu_pos ν) n t.
Proof.
  unfold nu0_list.
  pose proof (list_to_tup_tup_to_list n t) as K.
  destruct (tup_to_list n t) as [|a l]; [ contradiction | ].
  exact (nu_respects (nu_pos ν) _ _ _ _ K).
Qed.

(* Leibniz: mapping the letters of a tuple. / 莱布尼茨：映射元组的字母。 *)
Lemma tmap_tup_to_list@{o} {X Y : SetoidObject@{o o}} (f : X → Y)
  (n : nat) (t : Tup@{o} X n) :
  wmap (X := X) (Y := Y) f (tup_to_list n t) = tup_to_list n (tmap f n t).
Proof. induction n as [|n IH]; simpl; [ reflexivity | now rewrite IH ]. Qed.

(* ------------------------------------------------------------------------ *)
(* * ** The two conditions, and the correspondence with W₀-algebras / * ** 两个条件，以及与 W₀-代数的对应 *)

Section W0Systems.

Universes o so.

Local Notation MonOS :=
  (@Mon@{so o so so} Sets@{o so} Sets_Product_Monoidal@{so o}).

(*
 ν₁ = 1 is #470's [nu_unit] of the positive part.  (2): for every word of
 words, ν of the values of the inner words is ν of their concatenation,
 which IS μ ([W0_join_fun]), νk(νn1 × ⋯ × νnk) = ν_{n1+⋯+nk}. 

 --------
 ν₁ = 1 是正部分的 #470 的 [nu_unit]。（2）：对于 words 的每一个单词，内部单词的 ν 值的 ν 等于它们连接的 ν，这就是 μ（[W0_join_fun]），νk(νn1 × ⋯ × νnk) = ν_{n1+⋯+nk}。
*)
Definition nu0_assoc@{+} {X : obj[Sets@{o so}]} (ν : NAry0@{o} X) :
  Type@{o} :=
  ∀ ww : list (list X),
    nu0_list ν (wmap (X := WordObj X) (Y := X) (nu0_list ν) ww)
      ≈ nu0_list ν (wconcat ww).

(* An algebra gives a family: ν₀ = α⟨⟩ and ν_{n+1}(x1, …) = α⟨x1 …⟩. / 一个代数给出一个族：ν₀ = α⟨⟩ 并且 ν_{n+1}(x1, …) = α⟨x1 …⟩。 *)
Definition alg_NAry0@{+} {X : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 X) : NAry0@{o} X :=
  {| nu_zero := t_alg[α] Datatypes.nil
   ; nu_pos := {| nu := fun n t => t_alg[α] (tup_to_list n t)
                ; nu_respects := fun n m t u H =>
                    proper_morphism (t_alg[α]) _ _
                      (tup_to_list_respects n m t u H) |} |}.

Example alg_NAry0_zero@{+} {X : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 X) :
  nu_zero (alg_NAry0 α) = t_alg[α] word0 := eq_refl.

Example alg_NAry0_at@{+} {X : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 X) (n : nat) (t : Tup@{o} X n) :
  nu (nu_pos (alg_NAry0 α)) n t = t_alg[α] (tup_to_list n t) := eq_refl.

(*
 ν₀ is the unit of the monoid of the algebra, and ν₂ its
 multiplication. 

 --------
 ν₀ 是代数幺半群的单位，ν₂ 是它的乘法。
*)
Example alg_nu0_is_unit@{+} {X : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 X) :
  nu_zero (alg_NAry0 α) = mon_one (alg_monoid α) := eq_refl.

Example alg_nu2_is_mul@{+} {X : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 X) (a b : X) :
  nu (nu_pos (alg_NAry0 α)) 1 (a, b) = mon_mul (alg_monoid α) a b
  := eq_refl.

(* The family read back on lists is the structure map, up to ≈. / 家庭回顾上的列表是结构图，直到 ≈。 *)
Lemma alg_nu0_list@{+} {X : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 X) (l : list X) :
  nu0_list (alg_NAry0 α) l ≈ t_alg[α] l.
Proof.
  destruct l as [|a l]; [ reflexivity | ].
  unfold nu0_list; simpl.
  rewrite (tup_to_list_list_to_tup a l). reflexivity.
Qed.

(* ν₁ = 1, from the unit law. / ν₁ = 1，根据单位律。 *)
Lemma alg_NAry0_unit@{+} {X : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 X) : nu_unit (nu_pos (alg_NAry0 α)).
Proof. intro x. exact (alg_unit α x). Qed.

(* (2), from the action law. / (2)，根据诉讼法。 *)
Lemma alg_NAry0_assoc@{+} {X : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 X) : nu0_assoc (alg_NAry0 α).
Proof.
  intro ww.
  transitivity
    (t_alg[α] (wmap (X := WordObj X) (Y := X) (nu0_list (alg_NAry0 α)) ww)).
  { apply alg_nu0_list. }
  transitivity (t_alg[α] (wmap (X := WordObj X) (Y := X) (t_alg[α]) ww)).
  { apply (proper_morphism (t_alg[α])).
    clear. induction ww as [|w ww IH]; simpl; [ exact we_nil | ].
    exact (we_cons _ _ _ _ (alg_nu0_list α w) IH). }
  transitivity (t_alg[α] (wconcat ww)).
  { exact (alg_action α ww). }
  symmetry. apply alg_nu0_list.
Qed.

(* “νₙ is the n-fold product” in the monoid of the algebra. / νₙ 是代数幺半群中的 n 次乘积。 *)
Lemma alg_nu_is_fold@{+} {X : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 X) (n : nat) (t : Tup0@{o} X n) :
  nu0 (alg_NAry0 α) n t
    ≈ free_mon_extend (L := alg_monoid α) (fun s => s) (tup0_to_list n t).
Proof.
  destruct n as [|n]; [ reflexivity | ].
  simpl. symmetry. exact (alg_fold α (tup_to_list n t)).
Qed.

(* A family with ν₁ = 1 and (2) is an algebra: its structure map is the copairing [nu0_list], its unit law IS ν₁ = 1 by conversion, and its action law is (2) modulo [W0_map]. / 一个具有 ν₁ = 1 和 (2) 的族是一个代数：它的结构映射是共成对 [nu0_list]，它的单位律通过换算是 ν₁ = 1，它的作用律是 (2) 模 [W0_map] 。 *)
Definition NAry0_alg@{+} {X : obj[Sets@{o so}]} (ν : NAry0@{o} X)
  (Hu : nu_unit (nu_pos ν)) (Ha : nu0_assoc ν) :
  @TAlgebra Sets@{o so} W0F W0 X.
Proof.
  unshelve refine
    (@Build_TAlgebra Sets@{o so} W0F W0 X
       {| morphism := nu0_list ν |} _ _).
  - intros l l' H. exact (nu0_list_respects ν l l' H).
  - intro x. exact (Hu x).
  - intro ww. simpl.
    transitivity
      (nu0_list ν (wmap (X := WordObj X) (Y := X) (nu0_list ν) ww)).
    + apply nu0_list_respects. exact (W0_map _ ww).
    + exact (Ha ww).
Defined.

Example NAry0_alg_map@{+} {X : obj[Sets@{o so}]} (ν : NAry0@{o} X)
  (Hu : nu_unit (nu_pos ν)) (Ha : nu0_assoc ν) (l : list X) :
  t_alg[NAry0_alg ν Hu Ha] l = nu0_list ν l := eq_refl.

(* Family → algebra → family: ν₀ on the nose, ν_{n+1} at ≈ only (the length of the list of a tuple is stuck on n). / 家庭 → 代数 → 家庭：ν₀ 准确，ν_{n+1} 仅在 ≈ 上（元组的列表长度固定为 n）。 *)
Example NAry0_rt_zero@{+} {X : obj[Sets@{o so}]} (ν : NAry0@{o} X)
  (Hu : nu_unit (nu_pos ν)) (Ha : nu0_assoc ν) :
  nu_zero (alg_NAry0 (NAry0_alg ν Hu Ha)) = nu_zero ν := eq_refl.

Example NAry0_rt_pos_pair@{+} {X : obj[Sets@{o so}]} (ν : NAry0@{o} X)
  (Hu : nu_unit (nu_pos ν)) (Ha : nu0_assoc ν) (a b : X) :
  nu (nu_pos (alg_NAry0 (NAry0_alg ν Hu Ha))) 1 (a, b)
    = nu (nu_pos ν) 1 (a, b) := eq_refl.

Lemma NAry0_rt_pos@{+} {X : obj[Sets@{o so}]} (ν : NAry0@{o} X)
  (Hu : nu_unit (nu_pos ν)) (Ha : nu0_assoc ν) (n : nat) (t : Tup@{o} X n) :
  nu (nu_pos (alg_NAry0 (NAry0_alg ν Hu Ha))) n t ≈ nu (nu_pos ν) n t.
Proof. exact (nu0_list_tup_to_list ν n t). Qed.

(* Algebra → family → algebra: the structure map, up to ≈. / 代数 → 家族 → 代数：结构映射，到 ≈ 为止。 *)
Lemma alg_round_trip0@{+} {X : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 X) :
  t_alg[NAry0_alg (alg_NAry0 α) (alg_NAry0_unit α) (alg_NAry0_assoc α)]
    ≈ t_alg[α].
Proof. intro l. exact (alg_nu0_list α l). Qed.

(*
 The morphism clause, both ways: an algebra map commutes with every νₙ,
 n ≥ 0, and conversely. 

 --------
 同态条款，双向：一个代数映射与每个 νₙ（n ≥ 0）交换，反之亦然。
*)
Lemma alg_hom_NAry0_hom@{+} {X Y : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 X) (β : @TAlgebra Sets@{o so} W0F W0 Y)
  (f : X ~{Sets@{o so}}~> Y) :
  f ∘ t_alg[α] ≈ t_alg[β] ∘ fmap[W0F] f →
  NAry0_hom (alg_NAry0 α) (alg_NAry0 β) f.
Proof.
  intro H. split.
  - transitivity (t_alg[β] (fmap[W0F] f Datatypes.nil)); [ exact (H _) | ].
    apply (proper_morphism (t_alg[β])). exact (W0_map f _).
  - intros n t. simpl.
    transitivity (t_alg[β] (fmap[W0F] f (tup_to_list n t)));
      [ exact (H _) | ].
    apply (proper_morphism (t_alg[β])).
    rewrite <- (tmap_tup_to_list f n t). exact (W0_map f _).
Qed.

Lemma NAry0_hom_alg_hom@{+} {X Y : obj[Sets@{o so}]} (ν : NAry0@{o} X)
  (ν' : NAry0@{o} Y) (Hu : nu_unit (nu_pos ν)) (Ha : nu0_assoc ν)
  (Hu' : nu_unit (nu_pos ν')) (Ha' : nu0_assoc ν')
  (f : X ~{Sets@{o so}}~> Y) :
  NAry0_hom ν ν' f →
  f ∘ t_alg[NAry0_alg ν Hu Ha] ≈ t_alg[NAry0_alg ν' Hu' Ha'] ∘ fmap[W0F] f.
Proof.
  intros [H0 Hn] l. simpl.
  transitivity (nu0_list ν' (wmap f l)).
  - destruct l as [|a l]; [ exact H0 | ].
    unfold nu0_list; simpl.
    transitivity
      (nu (nu_pos ν') (length l) (tmap f (length l) (list_to_tup a l)));
      [ exact (Hn _ _) | ].
    apply (nu_respects (nu_pos ν')).
    clear. revert a; induction l as [|b l IH]; intro a; simpl;
      [ reflexivity | ].
    split; [ reflexivity | exact (IH b) ].
  - apply nu0_list_respects. apply word_eq_sym. exact (W0_map f l).
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** The systems ⟨S, ν₀, ν₁, …⟩ as a category, isomorphic to Set^{W₀} / * ** 系统 ⟨S, ν₀, ν₁, …⟩ 作为一个范畴，与 Set^{W₀} 同构 *)

Record W0System@{+} : Type@{so} := {
  ws0_set : obj[Sets@{o so}];
  ws0_nu : NAry0@{o} ws0_set;
  ws0_unit : nu_unit (nu_pos ws0_nu);
  ws0_assoc : nu0_assoc ws0_nu
}.

Definition W0SystemHom@{+} (A B : W0System) : Type@{o} :=
  { f : ws0_set A ~{Sets@{o so}}~> ws0_set B
  & NAry0_hom (ws0_nu A) (ws0_nu B) f }.

Definition W0SystemHom_Setoid@{+} (A B : W0System) :
  Setoid@{o o} (W0SystemHom A B).
Proof.
  refine {| equiv := fun f g =>
              @equiv _ (@homset Sets@{o so} (ws0_set A) (ws0_set B))
                (`1 f) (`1 g) |}.
  constructor.
  - intros f. reflexivity.
  - intros f g H. symmetry. exact H.
  - intros f g h H1 H2. transitivity (`1 g); assumption.
Defined.

Definition W0System_id@{+} (A : W0System) : W0SystemHom A A.
Proof.
  exists (@setoid_morphism_id@{o o o} (ws0_set A)). split.
  - reflexivity.
  - intros n t. apply (nu_respects (nu_pos (ws0_nu A))).
    exact (tup_eq_sym _ _ _ _ (tmap_id n t)).
Defined.

Definition W0System_compose@{+} {A B C : W0System}
  (f : W0SystemHom B C) (g : W0SystemHom A B) : W0SystemHom A C.
Proof.
  exists (@setoid_morphism_compose@{o o o} _ _ _ (`1 f) (`1 g)). split.
  - simpl. transitivity (`1 f (nu_zero (ws0_nu B))).
    + apply (proper_morphism (`1 f)). exact (fst (`2 g)).
    + exact (fst (`2 f)).
  - intros n t. simpl.
    transitivity (`1 f (nu (nu_pos (ws0_nu B)) n (tmap (`1 g) n t))).
    + apply (proper_morphism (`1 f)). exact (snd (`2 g) n t).
    + transitivity
        (nu (nu_pos (ws0_nu C)) n (tmap (`1 f) n (tmap (`1 g) n t))).
      * exact (snd (`2 f) n _).
      * apply (nu_respects (nu_pos (ws0_nu C))).
        exact (tup_eq_sym _ _ _ _ (tmap_comp (`1 f) (`1 g) n t)).
Defined.

(* The category of Mac Lane's systems ⟨S, ν₀, ν₁, …⟩. / Mac Lane 系统的范畴 ⟨S, ν₀, ν₁, …⟩。 *)
Definition W0Sys@{+} : Category@{so o o}.
Proof.
  unshelve refine
    {| obj     := W0System
     ; hom     := W0SystemHom
     ; homset  := W0SystemHom_Setoid
     ; id      := W0System_id
     ; compose := @W0System_compose |}.
  - intros A B C f f' Hf g g' Hg a. simpl.
    transitivity (`1 f (`1 g' a)).
    + apply (proper_morphism (`1 f)). exact (Hg a).
    + exact (Hf _).
  - intros A B f a. reflexivity.
  - intros A B f a. reflexivity.
  - intros A B C D f g h a. reflexivity.
  - intros A B C D f g h a. reflexivity.
Defined.

Definition W0Sys_to_EM@{+} : W0Sys ⟶ W0Alg.
Proof.
  unshelve refine
    (@Build_Functor W0Sys W0Alg
       (fun A => existT _ (ws0_set A)
                   (NAry0_alg (ws0_nu A) (ws0_unit A) (ws0_assoc A)))
       (fun A B f =>
          @Build_TAlgebraHom Sets@{o so} W0F W0 (ws0_set A) (ws0_set B)
            (NAry0_alg (ws0_nu A) (ws0_unit A) (ws0_assoc A))
            (NAry0_alg (ws0_nu B) (ws0_unit B) (ws0_assoc B))
            (`1 f)
            (NAry0_hom_alg_hom _ _ _ _ _ _ (`1 f) (`2 f)))
       _ _ _).
  - intros A B f g H a. exact (H a).
  - intros A a. reflexivity.
  - intros A B C f g a. reflexivity.
Defined.

Definition EM_to_W0Sys@{+} : W0Alg ⟶ W0Sys.
Proof.
  unshelve refine
    (@Build_Functor W0Alg W0Sys
       (fun x => {| ws0_set := projT1 x
                  ; ws0_nu := alg_NAry0 (projT2 x)
                  ; ws0_unit := alg_NAry0_unit (projT2 x)
                  ; ws0_assoc := alg_NAry0_assoc (projT2 x) |})
       (fun x y f =>
          existT _ (t_alg_hom[f])
            (alg_hom_NAry0_hom (projT2 x) (projT2 y) (t_alg_hom[f])
               (@t_alg_hom_commutes _ _ _ _ _ _ _ f)))
       _ _ _).
  - intros x y f g H a. exact (H a).
  - intros x a. reflexivity.
  - intros x y z f g a. reflexivity.
Defined.

(*
 The algebra round trip through the systems, with the identity as its
 component. 

 --------
 通过系统的代数往返，恒等式作为其组成部分。
*)
Definition W0Sys_EM_counit_iso@{+} (x : W0Alg) :
  @Isomorphism W0Alg (fobj[W0Sys_to_EM ◯ EM_to_W0Sys] x) x.
Proof.
  unshelve refine
    (@Build_Isomorphism W0Alg (fobj[W0Sys_to_EM ◯ EM_to_W0Sys] x) x
       (@Build_TAlgebraHom Sets@{o so} W0F W0 (projT1 x) (projT1 x)
          (projT2 (fobj[W0Sys_to_EM ◯ EM_to_W0Sys] x)) (projT2 x)
          (@setoid_morphism_id@{o o o} (projT1 x)) _)
       (@Build_TAlgebraHom Sets@{o so} W0F W0 (projT1 x) (projT1 x)
          (projT2 x) (projT2 (fobj[W0Sys_to_EM ◯ EM_to_W0Sys] x))
          (@setoid_morphism_id@{o o o} (projT1 x)) _) _ _).
  - intro l. simpl.
    transitivity (t_alg[projT2 x] l);
      [ exact (alg_nu0_list (projT2 x) l) | ].
    apply (proper_morphism (t_alg[projT2 x])).
    symmetry. exact (@fmap_id _ _ W0F (projT1 x) l).
  - intro l. simpl.
    transitivity (t_alg[projT2 x] (fmap[W0F] id l)).
    + apply (proper_morphism (t_alg[projT2 x])).
      symmetry. exact (@fmap_id _ _ W0F (projT1 x) l).
    + symmetry. exact (alg_nu0_list (projT2 x) _).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(* The system round trip, with the identity as its component. / 系统往返，身份作为其组成部分。 *)
Definition W0Sys_EM_unit_iso@{+} (A : W0Sys) :
  @Isomorphism W0Sys (fobj[EM_to_W0Sys ◯ W0Sys_to_EM] A) A.
Proof.
  unshelve refine
    (@Build_Isomorphism W0Sys (fobj[EM_to_W0Sys ◯ W0Sys_to_EM] A) A
       (existT _ (@setoid_morphism_id@{o o o} (ws0_set A)) _)
       (existT _ (@setoid_morphism_id@{o o o} (ws0_set A)) _) _ _).
  - split; [ reflexivity | ].
    intros n t. simpl.
    transitivity (nu (nu_pos (ws0_nu A)) n t);
      [ exact (nu0_list_tup_to_list (ws0_nu A) n t) | ].
    apply (nu_respects (nu_pos (ws0_nu A))).
    exact (tup_eq_sym _ _ _ _ (tmap_id n t)).
  - split; [ reflexivity | ].
    intros n t. simpl.
    transitivity (nu (nu_pos (ws0_nu A)) n (tmap (fun x => x) n t)).
    + apply (nu_respects (nu_pos (ws0_nu A))).
      exact (tup_eq_sym _ _ _ _ (tmap_id n t)).
    + symmetry. exact (nu0_list_tup_to_list (ws0_nu A) n _).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(*
 The systems ⟨S, ν₀, ν₁, …⟩ with ν₁ = 1 and (2) are isomorphic in Cat to
 Set^{W₀}, every component of both natural isomorphisms the identity. 

 --------
 系统 ⟨S, ν₀, ν₁, …⟩，其中 ν₁ = 1 且 (2) 在 Cat 中同构于 Set^{W₀}，两个自然同构的每个分量都是恒等映射。
*)
Definition W0Sys_EM_iso@{c +} :
  @Isomorphism Cat@{c so so so o} W0Sys W0Alg.
Proof.
  unshelve refine
    (@Build_Isomorphism Cat@{c so so so o} W0Sys W0Alg
       W0Sys_to_EM EM_to_W0Sys _ _).
  - exists (fun x => W0Sys_EM_counit_iso x).
    intros x y f a. reflexivity.
  - exists (fun A => W0Sys_EM_unit_iso A).
    intros A B f a. reflexivity.
Defined.

(* Mac Lane's Exercise 1 as a category: the systems are the monoids. / 作为一个范畴的 Mac Lane 练习 1：系统是幺半群。 *)
Definition Mon_W0Sys_iso@{c +} :
  @Isomorphism Cat@{c so so so o} MonOS W0Sys :=
  iso_compose (iso_sym W0Sys_EM_iso) Mon_EM_iso.

(* ------------------------------------------------------------------------ *)
(** ** Readbacks / ** 回读 *)

Example W0Sys_EM_iso_to@{+} : to W0Sys_EM_iso = W0Sys_to_EM := eq_refl.

Example W0Sys_EM_iso_from@{+} : from W0Sys_EM_iso = EM_to_W0Sys
  := eq_refl.

(* A system's structure map is the copairing of its family, and an algebra's νₙ is its structure map on Sⁿ. / 一个系统的结构图是其族的共配对，而一个代数的 νₙ 是其在 Sⁿ 上的结构图。 *)
Example W0Sys_to_EM_alg@{+} (A : W0Sys) (l : list (ws0_set A)) :
  t_alg[projT2 (fobj[W0Sys_to_EM] A)] l = nu0_list (ws0_nu A) l := eq_refl.

Example EM_to_W0Sys_zero@{+} (x : W0Alg) :
  nu_zero (ws0_nu (fobj[EM_to_W0Sys] x)) = t_alg[projT2 x] word0 := eq_refl.

Example EM_to_W0Sys_nu@{+} (x : W0Alg) (n : nat) (t : Tup@{o} (projT1 x) n) :
  nu (nu_pos (ws0_nu (fobj[EM_to_W0Sys] x))) n t
    = t_alg[projT2 x] (tup_to_list n t) := eq_refl.

(* The system round trip keeps the set, ν₀ and the maps on the nose. / 系统往返保持集合、ν₀ 和映射不变。 *)
Example W0Sys_rt_set@{+} (A : W0Sys) :
  ws0_set (fobj[EM_to_W0Sys ◯ W0Sys_to_EM] A) = ws0_set A := eq_refl.

Example W0Sys_rt_zero@{+} (A : W0Sys) :
  nu_zero (ws0_nu (fobj[EM_to_W0Sys ◯ W0Sys_to_EM] A)) = nu_zero (ws0_nu A)
  := eq_refl.

Example W0Sys_rt_hom@{+} {A B : W0Sys} (f : A ~{W0Sys}~> B) :
  `1 (fmap[EM_to_W0Sys ◯ W0Sys_to_EM] f) = `1 f := eq_refl.

Example EM_W0Sys_rt_carrier@{+} (x : W0Alg) :
  projT1 (fobj[W0Sys_to_EM ◯ EM_to_W0Sys] x) = projT1 x := eq_refl.

Example EM_W0Sys_rt_alg_hom@{+} {x y : W0Alg} (f : x ~{W0Alg}~> y) :
  t_alg_hom[fmap[W0Sys_to_EM ◯ EM_to_W0Sys] f] = t_alg_hom[f] := eq_refl.

Example W0Sys_EM_iso_to_from_component@{+} (x : W0Alg) :
  (t_alg_hom[to (projT1 (iso_to_from W0Sys_EM_iso) x)],
   t_alg_hom[from (projT1 (iso_to_from W0Sys_EM_iso) x)])
    = (@setoid_morphism_id@{o o o} (projT1 x),
       @setoid_morphism_id@{o o o} (projT1 x)) := eq_refl.

Example W0Sys_EM_iso_from_to_component@{+} (A : W0Sys) :
  (`1 (to (projT1 (iso_from_to W0Sys_EM_iso) A)),
   `1 (from (projT1 (iso_from_to W0Sys_EM_iso) A)))
    = (@setoid_morphism_id@{o o o} (ws0_set A),
       @setoid_morphism_id@{o o o} (ws0_set A)) := eq_refl.

(*
 The system of a monoid M: ν₀ is the unit of M, ν₂(x, y) = x · (y · 1),
 and νₙ is the n-fold product. 

 --------
 幺半群 M 的系统：ν₀ 是 M 的单位元，ν₂(x, y) = x · (y · 1)，νₙ 是 n 次乘积。
*)
Example Mon_system_zero@{+} (M : MonOS) :
  nu_zero (ws0_nu (fobj[EM_to_W0Sys ◯ Mon_K] M)) = mon_one M := eq_refl.

Example Mon_system_pair@{+} (M : MonOS) (x y : mon_ob M) :
  nu (nu_pos (ws0_nu (fobj[EM_to_W0Sys ◯ Mon_K] M))) 1 (x, y)
    = mon_mul M x (mon_mul M y (mon_one M)) := eq_refl.

Lemma Mon_system_nu@{+} (M : MonOS) (n : nat) (t : Tup0@{o} (mon_ob M) n) :
  nu0 (ws0_nu (fobj[EM_to_W0Sys ◯ Mon_K] M)) n t
    ≈ free_mon_extend (L := M) (fun s => s) (tup0_to_list n t).
Proof. destruct n as [|n]; reflexivity. Qed.

End W0Systems.
