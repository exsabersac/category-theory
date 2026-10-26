Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Semigroup.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Smgrp.

Generalizable All Variables.

(* * * The word monad W, its algebras, and the monadicity of Smgrp / * * 单子 W、它的代数以及 Smgrp 的单子性 *)

(*
 Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 Springer GTM 5, 1998, §VI.4 “Words and Free Semigroups”, printed
 pp. 144-146 (PDF pp. 153-155): Proposition 1, pp. 144-145 —
 maclane:VI.4:prop1; Proposition 2, p. 145 — maclane:VI.4:prop2;
 the Corollary, p. 146 — maclane:VI.4:cor1; the remark on the
 comparison functor, p. 146 — maclane:VI.4:remark1
 nLab: https://ncatlab.org/nlab/show/monadic+functor
 nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad
 nLab: https://ncatlab.org/nlab/show/free+monoid

 WHAT THE BOOK SAYS, read from the page images.
 Proposition 1 (→· transliterates the page's dotted arrow of a
 natural transformation, as Monad/Eilenberg/Moore/Limit.v does, and
 ⇀ its arrow of an adjunction): “The monad on Set determined by the
 adjunction Set ⇀ Smgrp is
 W = ⟨W : Set → Set, η : I →· W, μ : W² →· W⟩ where
 WX = ∐_{n=1}^∞ Xⁿ, η_X x = ⟨x⟩ for each x ∈ X, while μ_X is
 μ_X(⟨⟨x11⟩ … ⟨x1n1⟩⟩ … ⟨⟨xk1⟩ … ⟨xknk⟩⟩) = ⟨x11⟩ … ⟨x1n1⟩ … ⟨xk1⟩ …
 ⟨xknk⟩ for all positive integers k, all k-tuples n1, …, nk of
 positive integers, and all xij ∈ X.”  From its proof: “μ = GεF …
 More briefly, μ_X applied to a word of words removes the outer pointy
 brackets.  Note that this description allows direct verification of
 the unit and associative laws for the monad W, without overt
 reference to the notion of a semi-group.”
 Proposition 2: “For the above word-monad W in Set, the W-algebras
 have the form ⟨S, ν1, ν2, …⟩: A set S equipped with one n-ary
 operation νn : Sⁿ → S for each positive integer n, such that ν1 = 1
 while for every positive k and every k-tuple of positive integers
 n1, …, nk one has the identity νk(νn1 × ⋯ × νnk) = ν_{n1+⋯+nk} :
 S^{n1+⋯+nk} → S. (2)  A morphism f : ⟨S, ν1, …⟩ → ⟨S', ν'1, …⟩ of
 W-algebras is a function f : S → S' which commutes with each νn, so
 that fνn = ν'n fⁿ : Sⁿ → S'.”
 The Corollary: “The system ⟨S, ν1, ν2, …⟩ is a W-algebra, as above,
 if and only if ν1 = 1, ν2 : S × S → S is an associative binary
 operation on S, and for all n ≥ 2, ν_{n+1} = νn(ν2 × 1) :
 S^{n+1} → S.”
 The remark: “The comparison functor K : Smgrp → Set^W is the evident
 map ⟨S, ν⟩ ↦ ⟨S, 1, ν2, …, νn, …⟩ where νn is the iterate of the
 binary ν.  In other words, K is an isomorphism, but it replaces the
 algebraic system ⟨S, ν⟩ with one associative binary operation by the
 same set with all the iterated operations derived from this binary
 operation.”

 PROPOSITION 1.  [WordF] is G ◯ F and [WordMonad] is Monad/
 Comparison.v's transparent [Adjunction_Induced_Monad Sg_adj]
 (Monad/Adjunction.v's [Adjunction_Monad], the issue's donor, is
 opaque by [About]).  At [eq_refl]: W X is the setoid of words
 ([W_obj]), its carrier the sigma ∐_{n≥1} Xⁿ ([W_carrier]); W f acts
 letterwise ([W_map]); η is the insertion as a setoid map ([W_ret]) and
 x ↦ ⟨x⟩ ([W_ret_fun]); μ = G ε F ([W_join_counit]) is the
 concatenation [pwconcat] of a word of words, the fold of juxtaposition
 ([W_join_fun]), and sends ⟨⟨x11⟩⟨x12⟩⟩⟨⟨x21⟩⟩ to ⟨x11⟩⟨x12⟩⟨x21⟩
 ([W_join_literal]).  Its laws are those of the adjunction.  “Direct
 verification”: [WordMonad_direct] is Theory/Monad.v's [Build_Monad]
 with η the insertion and μ the concatenation [pwconcat_map], its laws
 proved by induction on words without reference to the adjunction (the
 associative law, three layers of brackets, by [tfold1_tmap] and
 [tfold1_hom]; the unit laws by [tfoldl_letters] and by conversion).
 The fold and its homomorphism lemma are the free semigroup's:
 [pwconcat] folds in [FreeSg X], and [tfold1_hom], quantified over
 semigroup maps, is applied to [pwconcat_hom] and to [FreeSg_map f].
 So the proof avoids the adjunction, not, as Mac Lane's remark has it,
 “overt reference to the notion of a semi-group”.  Its unit and
 multiplication ARE W's as setoid maps ([WordMonad_direct_ret],
 [WordMonad_direct_join], at [eq_refl]); as monads the two are refused
 equal (Test/ProbeWord470.v, R6): the data agree and the law proofs do
 not.

 PROPOSITION 2.  A family is [NAry S]: [nu ν n] : S^{n+1} → S for
 each n, with [nu_respects], stated across lengths at no cost since
 [tup_eq] is False there.  ν1 = 1 is [nu_unit]; (2) is [nu_assoc], at
 each k-tuple (w1, …, wk) of words, wi in S^{ni}: ν_k of the values of
 the wi against ν of their concatenation, whose length is n1 + ⋯ + nk.
 Mac Lane reads (2) through W(WX) ≅ ∐_k ∐_n X^{n1+⋯+nk}; here (2) is
 quantified over tuples of words and needs no separate isomorphism: a
 k-tuple of words, each carrying its length, is a point of W(WX), and
 their concatenation is μ ([W_join_fun]).  An algebra ⟨S, h⟩ gives the
 family ν_n = h on Sⁿ ([alg_NAry], [alg_NAry_at] at [eq_refl]), with
 ν1 = 1 from its unit law ([alg_NAry_unit]) and (2) from its action law
 ([alg_NAry_assoc]); a family with the two conditions is an algebra
 whose structure map is the copairing [nu_sharp] and whose two laws ARE
 the two conditions, by conversion ([NAry_alg]).  Family → algebra →
 family returns the family, the whole record at [eq_refl]
 ([NAry_round_trip]); algebra → family → algebra returns h up to ≈
 ([alg_round_trip]), at each (n; t) at [eq_refl] (C31), and as a setoid
 map it is refused (R7), sigT having no η (R2).  The morphism clause,
 both ways: [alg_hom_NAry_hom], [NAry_hom_alg_hom].
 As a category: [WSys], the systems ⟨S, ν1, ν2, …⟩ with ν1 = 1 and (2)
 ([WSystem]) and the maps commuting with every νn, is isomorphic in
 [Cat] to [WordAlg], Set^W ([WSys_EM_iso]): its legs are [WSys_to_EM]
 and [EM_to_WSys] at [eq_refl], and every component of both natural
 isomorphisms is the identity, to and from, at [eq_refl].  The system
 round trip keeps the set, the family and the proof of ν1 = 1 at
 [eq_refl] ([WSys_rt_set], [WSys_rt_nu], [WSys_rt_unit]), and the maps
 ([WSys_rt_hom]); the proof of (2) comes back rebuilt (R9), so the whole
 system is refused (R8); a whole morphism is refused too (R10, well
 typed since a hom type depends on the set and the family alone, and a
 variable sigT pair against its rebuilt pair); the algebra round trip
 is refused on objects (R11), and the composite functor against the
 identity (R12).

 THE COROLLARY.  [cor_conditions ν]: ν1 = 1, ν2 associative, and
 ν_{m+3}(x, y, t) ≈ ν_{m+2}(ν2(x, y), t) for every m, Mac Lane's
 ν_{n+1} = νn(ν2 × 1) at n = m + 2 ≥ 2.  [NAry_corollary] : (ν1 = 1
 and (2)) ↔ [cor_conditions ν].  Forward ([cor_forward]): (2) at three
 k-tuples, (⟨ab⟩, ⟨c⟩), (⟨a⟩, ⟨bc⟩), and ⟨xy⟩ followed by the letters
 of t.  Backward ([cor_backward]): first [cor_iterate], νn ≈ the n-fold
 product of ν2 bracketed to the left (Mac Lane's “Similarly, νn must be
 the n-fold product”), and then (2) is the action law of the
 comparison algebra of that semigroup, Monad/Comparison.v's
 [EM_Comparison_Algebra_action]: the shared route, with no second
 induction on brackets.  In an arbitrary algebra ν3(a, b, c) is
 ν2(ν2(a, b), c) up to ≈ (C45) and not at [eq_refl] (R13); in an
 algebra K S it is at [eq_refl], at every length ([Sg_K_nu_succ]).

 THE REMARK.  [Sg_K] is Monad/Comparison.v's [EM_Comparison Sg_adj].
 Mac Lane's ⟨S, ν⟩ ↦ ⟨S, 1, ν2, …⟩ holds at [eq_refl]: the carrier is S
 ([Sg_K_carrier]); the structure map is G ε_S ([Sg_K_alg]), the product
 of the letters bracketed to the left ([Sg_K_alg_fun]); ν1 = 1
 ([Sg_K_nu1]); ν2 = ν ([Sg_K_nu2]); “νn is the iterate of the binary
 ν”, ν_{m+3}(x, y, t) = ν_{m+2}(xy, t) ([Sg_K_nu_succ]); K f is f
 ([Sg_K_map]); and so read as a system ([Sg_K_system_nu],
 [Sg_K_system_nu2]).  [EM_to_Smgrp] makes an algebra a semigroup under
 ν2(a, b) := h⟨ab⟩, associative by [cor_forward].  “K is an
 isomorphism”: [Smgrp_EM_iso : SmgrpSets ≅[Cat] WordAlg], its legs
 [Sg_K] and [EM_to_Smgrp] at [eq_refl] and every component of both
 natural isomorphisms the identity, to and from, at [eq_refl].  It is
 built from the two component isomorphisms, as #466 builds
 Instance/SupLat.v's [SupLat_EM_iso], and not as Theory/Equivalence.v's
 [Equivalence_to_Cat_Iso] of the equivalence: through that bridge the
 component of [iso_to_from] is still the identity at [eq_refl] (C67),
 and that of [iso_from_to] is refused (R21), the bridge taking it from
 the symmetry of the unit, Theory/Functor.v's
 [Functor_Setoid_obligation_1], opaque by [About]; the #470 audit
 measured that cause: with a transparent swap of the components in
 place of that symmetry, R21's statement holds at [eq_refl].
 [Smgrp_EM_equivalence] is the equivalence with the same components,
 and [Sg_Forget_Monadic : Monadic Sg_Forget] the monadicity of
 semigroups over Set in Monad/Comparison.v's sense, an equivalence
 (Barr and Wells' “triplable”, which Mac Lane's §VI.3 sets beside his
 isomorphism).  The round trips keep the carrier, the curried
 multiplication and the maps at [eq_refl] ([Smgrp_EM_rt_carrier],
 [Smgrp_EM_rt_mul], [Smgrp_EM_rt_hom], [EM_Smgrp_rt_carrier],
 [EM_Smgrp_rt_alg_hom]).  Refused at [eq_refl]: the semigroup round
 trip at a variable (R14) and at a pair (X; σ) (R15); the uncurried
 multiplication there as a function (R16; prod has no η, R3, and at
 each literal pair (a, b) it holds, C66); the algebra round trip (R17)
 and its structure map as a setoid map (R18, the iterated ν2 against
 an arbitrary h); and both composites against the identity functors
 (R19, R20).  So Mac Lane's “isomorphism” is delivered as an
 isomorphism in [Cat] with identity components.  An isomorphism in
 [Cat] is, by Instance/Cat.v, an equivalence of categories, its
 hom-setoid being Theory/Functor.v's [Functor_Setoid], natural
 isomorphism: the issue's “an isomorphism (or, minimally, an
 equivalence)” is met in its “or, minimally, an equivalence” form,
 strengthened by the identity components, which are what bring it
 toward Mac Lane's isomorphism of categories.  A strict identity of the
 two categories is refused (R19, R20).  An isomorphism in
 Instance/StrictCat.v, whose hom-setoid asks Leibniz equality of the
 object maps, would need with these legs fobj[EM_to_Smgrp ◯ Sg_K] A = A
 for every A, so the η of prod under a binder (the multiplication comes
 back as fun p => ν(fst p, snd p), R3 and R16) and the equality of
 rebuilt proof fields: extensionality, argued and not measured.

 THE ISSUE'S PREMISES, dated.  Issue #470 was filed on 2026-07-23.  Its
 “None of this is present” (no category Smgrp, no free-semigroup
 functor) was accurate when filed and held until this change (a grep
 of the .v files for a semigroup category, internal semigroups or free
 semigroups finds prose only); Theory/Category/Semi.v is semigroupoids
 and Theory/Coq/Semigroup.v an ops-only class, as the body says.  Its
 [list_Monad] (Theory/Coq/List.v, with [flatten]) is the free-monoid
 monad as operations on Coq's lists, with no [@Monad Coq list] and an
 [IsMonad] bridge (Theory/Coq/Monad/Proofs.v) covering Identity, arrow
 and Compose alone: accurate when filed and still accurate, Theory/Coq/
 List.v having last changed in c429a82b (2026-06-17); the body cites
 those constants by line, which this tree replaces by their names.  Of
 its suggested modules, Monad/Instance/ does not exist; the files are
 Instance/Smgrp.v (Mac Lane's name for the category, as Instance/Grp.v
 and Instance/SupLat.v use theirs) and this one, with Theory/Algebra/
 Semigroup.v for the internal notion.  Its “CLAUDE.md Key Files index”
 was accurate when filed and has been stale since PR #1284 (merged
 2026-09-09), which moved the index to docs/INDEX.md.

 STRENGTHS.  Every [Example] above holds at [eq_refl], and
 Test/ProbeWord470.v restates each one (C19 to C30, C33 to C44 and C46
 to C65).  At ≈ only: [alg_round_trip], [cor_iterate], and the inverse
 laws of the two isomorphisms in [Cat], natural isomorphisms with
 identity components.  Three readbacks need #1347 (Instance/Sets.v's
 identity and composite with their properness fields as terms):
 [W_ret], [WordMonad_direct_ret] and [WordMonad_direct_join] are
 refused, “cannot unify”, when this file is compiled against a built
 tree of master 687ac356, and nothing else of it is.  Nineteen proofs
 end [Defined] (counted by token).  Eighteen are load-bearing, measured
 by closing each alone [Qed] in a scratch copy of the targets and the
 probe, with the first command that then stops: [WordMonad_direct]
 ([WordMonad_direct_ret]), [alg_NAry_unit] ([WSys_rt_unit], its only
 consumer: closed [Qed] with that readback and its control C39 set
 aside, everything else compiles, so it is transparent for that
 readback alone), [NAry_alg] ([NAry_round_trip]),
 [WSystemHom_Setoid], [WSystem_id] and
 [WSystem_compose] ([WSys]), [WSys] ([WSys_to_EM]), [WSys_to_EM] and
 [EM_to_WSys] ([WSys_EM_counit_iso]), [WSys_EM_counit_iso] and
 [WSys_EM_unit_iso] ([WSys_EM_iso]), [WSys_EM_iso] ([WSys_EM_iso_to]),
 [EM_sg_map] ([EM_to_Smgrp]), [EM_to_Smgrp] ([Smgrp_EM_counit_iso]),
 [Smgrp_EM_counit_iso] and [Smgrp_EM_unit_iso]
 ([Smgrp_EM_equivalence]), [Smgrp_EM_equivalence]
 ([Smgrp_EM_counit_component]) and [Smgrp_EM_iso] ([Smgrp_EM_iso_to]);
 [Sg_Forget_Monadic] is [Defined] by the data convention only (closed
 [Qed], nothing stops).  The fifteen lemmas end [Qed].  Two of them,
 the auxiliary fold lemmas [tfoldl_tmap] and [tfold1_tmap], state a
 Leibniz equality between elements of a semigroup, proved by induction
 on the tuple: stronger than ≈, which is all that [WordMonad_direct],
 rewriting with the second, needs (Instance/Smgrp.v's [tfoldl_tapp]
 and [tfold1_tapp] are the other two, and its STRENGTHS records the
 scan that finds no fifth).  Every refutation of the probe stands,
 inside its command, in a copy of the three targets with all their
 forty-one [Qed]s turned [Defined] and [Transparent Obligations] set
 ([About] reporting there transparent what is opaque in the tree), so
 none is the opacity of these files; the dependency closure was not
 flipped, and the causes stated above (no η for sigT and prod, proofs
 rebuilt, data stuck on variables) are read from the terms, but for
 R21's, the opaque obligation, which the #470 audit measured (THE
 REMARK).

 UNIVERSES, read off [About].  The family record [NAry], its fields
 and constructor, [nu_sharp], [nu_unit], [nu2], [nu2_respects] and
 [cor_conditions] bind @{o} with caps only.  The two isomorphisms in
 [Cat] and their eight readbacks bind @{o so c} with o < so, o < c and
 so < c (Instance/Cat.v's [Cat@{c so so so o}]; [Smgrp_EM_iso] is
 [Isomorphism@{c so so}]).  Everything else binds @{o so} with the one
 constraint o < so besides caps: [WordMonad : Monad@{so o} WordF],
 [WordAlg := EilenbergMoore@{so so so o}] (a [Category@{so o o}]),
 [Smgrp_EM_equivalence : EquivalenceOfCategories@{so so so so so o}]
 and [Sg_Forget_Monadic : Monadic@{so so so so so o so so}], the
 instances of Instance/SupLat/Free.v's [SL_Forget_Monadic]; [WSystem]
 is a [Type@{so}].  The caps are the standard library's (pair and sigma
 projections, compose, ID, RelationClasses.Defs, eq_ind, eq_ind_r,
 eq_rect_r, Logic_lemmas.equality, nat_rect, False_rect, prod_rect).
 No [Set] and no equation, on Rocq 9.1.1, Coq 8.19.2 and 8.20.1 alike
 (binders and constraints between bound levels compared by script).

 NOT DELIVERED.  The section's exercises (#471 to #474: W₀ on Mon,
 R-modules, the polynomial rings, rings over Ab).  A strict identity of
 Smgrp and Set^W (refused above), and an isomorphism in
 Instance/StrictCat.v (which would need extensionality, as argued
 above).  Beck's route to monadicity (Monad/Monadicity/Beck.v), not
 taken.  The Kleisli category of W.  A lawful
 [@Monad Coq list] and the categorical laws of Theory/Coq/List.v's
 [list_Monad], the issue's background, still absent. 

 --------
 书籍：Mac Lane，《应用数学家的范畴》，第2版，Springer GTM 5，1998年，第VI.4节“词与自由半群”，印刷页144-146（PDF页153-155）：命题1，页144-145 — maclane:VI.4:prop1；命题2，页145 — maclane:VI.4:prop2；推论，页146 — maclane:VI.4:cor1；关于比较函子的备注，页146 — maclane:VI.4:remark1
 nLab: https://ncatlab.org/nlab/show/monadic+functor
 nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad
 nLab: https://ncatlab.org/nlab/show/free+monoid书中所述内容，从页面图像中读取。命题 1（→· 表示自然变换的页面虚线箭头，如 Monad/Eilenberg/Moore/Limit.v 所做，⇀ 表示伴随的箭头）：“由伴随 Set ⇀ Smgrp 决定的 Set 上的 monad 为
 W = ⟨W : Set → Set, η : I →· W, μ : W² →· W⟩，其中
 WX = ∐_{n=1}^∞ Xⁿ，η_X x = ⟨x⟩ 对每个 x ∈ X，而 μ_X 定义为
 μ_X(⟨⟨x11⟩ … ⟨x1n1⟩⟩ … ⟨⟨xk1⟩ … ⟨xknk⟩⟩) = ⟨x11⟩ … ⟨x1n1⟩ … ⟨xk1⟩ … ⟨xknk⟩ 对所有正整数 k，所有 k 元组 n1, …, nk 的正整数，以及所有 xij ∈ X。”
 根据其证明：“μ = GεF … 简言之，μ_X 作用于一个词的词时会去掉外层尖括号。”请注意，这种描述允许直接验证单子 W 的单位定律和结合律，而无需公开提及半群的概念。
 命题 2：对于上述集合上的字单子 W，W-代数具有以下形式 ⟨S, ν1, ν2, …⟩：一个集合 S 配备了每个正整数 n 对应的 n 元运算 νn : Sⁿ → S，使得 ν1 = 1，并且对于每个正整数 k 以及每个正整数 k 元组 n1, …, nk，有恒等式 νk(νn1 × ⋯ × νnk) = ν_{n1+⋯+nk} : S^{n1+⋯+nk} → S。(2) W-代数的态射 f : ⟨S, ν1, …⟩ → ⟨S', ν'1, …⟩ 是一个函数 f : S → S'，它与每个 νn 交换，即 fνn = ν'n fⁿ : Sⁿ → S'。

 推论：系统 ⟨S, ν1, ν2, …⟩ 是如上所述的 W-代数，当且仅当 ν1 = 1，ν2 : S × S → S 是 S 上的结合二元运算，并且对所有 n ≥ 2，有 ν_{n+1} = νn(ν2 × 1) : S^{n+1} → S。

 备注：比较函子 K : Smgrp → Set^W 是显而易见的映射 ⟨S, ν⟩ ↦ ⟨S, 1, ν2, …, νn, …⟩，其中 νn 是二元运算 ν 的迭代。换句话说，K 是一个同构，但它用同一个集合及从这个二元运算导出的所有迭代运算，替代了只有一个结合二元运算的代数系统 ⟨S, ν⟩。命题 1. [WordF] 是 G ◯ F，且 [WordMonad] 是 Monad/Comparison.v 的透明 [Adjunction_Induced_Monad Sg_adj]（Monad/Adjunction.v 的 [Adjunction_Monad]，议题的提供者，由 [About] 是不透明的）。在 [eq_refl]：W X 是词的集合（[W_obj]），其承载体是 sigma ∐_{n≥1} Xⁿ（[W_carrier]）；W f 按字母操作（[W_map]）；η 是作为集合映射的插入（[W_ret]），且 x ↦ ⟨x⟩（[W_ret_fun]）；μ = G ε F（[W_join_counit]）是词的词的连接 [pwconcat]，是并列的折叠（[W_join_fun]），并且将 ⟨⟨x11⟩⟨x12⟩⟩⟨⟨x21⟩⟩ 发送为 ⟨x11⟩⟨x12⟩⟨x21⟩（[W_join_literal]）。它的定律是伴随关系的定律。“直接验证”: [WordMonad_direct] 是 Theory/Monad.v 中的 [Build_Monad]，其中 η 为插入，μ 为连接 [pwconcat_map]，其定律通过对单词的归纳证明而不涉及伴随（结合律，通过三层括号 [tfold1_tmap] 和 [tfold1_hom]；单位律通过 [tfoldl_letters] 和通过换算证明）。折叠及其同态引理是自由半群的：[pwconcat] 在 [FreeSg X] 中折叠，并且 [tfold1_hom]，作用于半群映射，应用于 [pwconcat_hom] 和 [FreeSg_map f]。因此，该证明避免了使用伴随，而不是像 Mac Lane 所说的那样，“明显引用半群的概念”。它的单位和乘法作为集合等价映射是 W 的（[WordMonad_direct_ret]、[WordMonad_direct_join]，位于 [eq_refl]）；作为单子，这两个被拒绝相等（Test/ProbeWord470.v, R6）：数据一致，但定律证明不一致。命题 2. 一个族是 [NAry S] :  [nu ν n] : S^{n+1} → S 对于每个 n，带有 [nu_respects]，可以在不付出代价的情况下跨长度陈述，因为 [tup_eq] 在那里为假。ν1 = 1 是 [nu_unit]；(2) 是 [nu_assoc]，对于每个词的 k 元组 (w1, …, wk)，wi 属于 S^{ni}：ν_k 对 wi 的值与它们拼接的 ν 的值比较，其长度为 n1 + ⋯ + nk。Mac Lane 通过 W(WX) ≅ ∐_k ∐_n X^{n1+⋯+nk} 来解读 (2)；这里 (2) 被量化在词的元组上，不需要单独的同构：一个 k 元词组，每个词携带其长度，是 W(WX) 的一个点，而它们的拼接是 μ ( [W_join_fun] )。一个代数 ⟨S, h⟩ 给出了族 ν_n = h 在 Sⁿ 上（[alg_NAry]，[alg_NAry_at] 于 [eq_refl]），其中 ν1 从其单位律得到（[alg_NAry_unit]），且 (2) 来自其作用律（[alg_NAry_assoc]）；满足这两个条件的族即是一个代数，其结构映射为 copairing [nu_sharp]，其两个定律就是这两个条件，通过转换（[NAry_alg]）。从族到代数再到族会返回原来的族，完整记录在 [eq_refl]（[NAry_round_trip]）；从代数到族再到代数会返回 h 到近似 ≈（[alg_round_trip]），在每个 (n; t) 于 [eq_refl] (C31)，作为集合映射它被拒绝 (R7)，sigT 没有 η (R2)。态射条款，两种方式：[alg_hom_NAry_hom]，[NAry_hom_alg_hom]。作为一个范畴：[WSys]，由系统⟨S, ν1, ν2, …⟩组成，其中ν1 = 1并且(2)([WSystem])以及与每个νn交换的映射，在[Cat]中同构于[WordAlg]，Set^W([WSys_EM_iso])：它的腿是在[eq_refl]处的[WSys_to_EM]和[EM_to_WSys]，并且两个自然同构的每个分量在[eq_refl]处都是恒等映射，无论是去还是返回。该系统往返保持集合、族以及在 [eq_refl]（[WSys_rt_set]、[WSys_rt_nu]、[WSys_rt_unit]）处的 ν1 = 1 的证明，以及映射（[WSys_rt_hom]）；（2）的证明以重建形式返回（R9），因此整个系统被拒绝（R8）；整个态射也被拒绝（R10，类型正确，因为同态类型仅依赖于集合和族，并且变量 sigT 对与其重建对）；代数往返在对象上被拒绝（R11），以及与恒等的复合函子（R12）。推论。[cor_conditions ν]：ν1 = 1，ν2 结合，并且对于每个 m，有 ν_{m+3}(x, y, t) ≈ ν_{m+2}(ν2(x, y), t)，Mac Lane 的 ν_{n+1} = νn(ν2 × 1) 在 n = m + 2 ≥ 2 时成立。[NAry_corollary]：（ν1 = 1 并且 (2)）↔ [cor_conditions ν]。正向 ([cor_forward])：(2) 在三个 k 元组上，(⟨ab⟩, ⟨c⟩)、(⟨a⟩, ⟨bc⟩)，以及 ⟨xy⟩ 后跟 t 的字母。反向 ([cor_backward])：首先 [cor_iterate]，νn ≈ ν2 左结合的 n 重积（Mac Lane 的“同样，νn 必须是 n 重积”），然后 (2) 是该半群的比较代数的作用律，Monad/Comparison.v 的 [EM_Comparison_Algebra_action]：共有的路径，没有对括号进行第二次归纳。在任意代数中，ν3(a, b, c) 是 ν2(ν2(a, b), c) 至 ≈ (C45) 并且不在 [eq_refl] (R13)；在代数 K S 中，它在 [eq_refl]，并且在每个长度下 ([Sg_K_nu_succ]) 成立。备注。[Sg_K] 是 Monad/Comparison.v 中的 [EM_Comparison Sg_adj]。Mac Lane 的 ⟨S, ν⟩ ↦ ⟨S, 1, ν2, …⟩ 在 [eq_refl] 成立：载体是 S ([Sg_K_carrier])；结构映射是 G ε_S ([Sg_K_alg])，即括号中左侧字母的乘积 ([Sg_K_alg_fun])；ν1 = 1 ([Sg_K_nu1])；ν2 = ν ([Sg_K_nu2])；“νn 是二元 ν 的迭代”，ν_{m+3}(x, y, t) = ν_{m+2}(xy, t) ([Sg_K_nu_succ])；K f 是 f ([Sg_K_map])；作为一个系统读取时 ([Sg_K_system_nu], [Sg_K_system_nu2])。[EM_to_Smgrp] 使一个代数在 ν2(a, b) := h⟨ab⟩ 下成为半群，根据 [cor_forward] 结合。“K 是同构”：[Smgrp_EM_iso : SmgrpSets ≅[Cat] WordAlg]，它的两条腿 [Sg_K] 和 [EM_to_Smgrp] 在 [eq_refl] 及两个自然同构的每个分量上都是恒等，从及到，位于 [eq_refl]。它由两个分量同构构建，就像 #466 构建 Instance/SupLat.v 的 [SupLat_EM_iso]，而不是 Theory/Equivalence.v 的 [Equivalence_to_Cat_Iso] 的等价：通过那座桥，[iso_to_from] 的分量仍然在 [eq_refl] (C67) 上是恒等的，而 [iso_from_to] 的分量被拒绝 (R21)，桥将其从单元的对称性抽取出来，即 Theory/Functor.v 的 [Functor_Setoid_obligation_1]，由 [About] 设为不透明；#470 审计测量了该原因：用透明的组件交换代替该对称性，R21 的陈述在 [eq_refl] 上成立。[Smgrp_EM_equivalence] 是具有相同分量的等价，而 [Sg_Forget_Monadic : Monadic Sg_Forget] 是在 Monad/Comparison.v 的意义下半群在 Set 上的幺半性，一个等价 (Barr 和 Wells 的“triplable”，Mac Lane 的 §VI.3 将其置于他的同构旁边) 。往返保持了承运人、柯里化的乘法以及在 [eq_refl] 的映射（[Smgrp_EM_rt_carrier]、[Smgrp_EM_rt_mul]、[Smgrp_EM_rt_hom]、[EM_Smgrp_rt_carrier]、[EM_Smgrp_rt_alg_hom]）。在 [eq_refl] 被拒绝：在变量 (R14) 和对 (X; σ) (R15) 上的半群往返；作为函数存在的未柯里化乘法 (R16; prod 没有 η，R3，并且在每个字面对 (a, b) 上成立，C66)；代数往返 (R17) 及其作为集点映射的结构映射 (R18，对任意 h 的迭代 ν2)；以及对恒等函子作用的两个复合 (R19, R20)。因此，Mac Lane 的“同构”作为 [Cat] 中带有恒等分量的同构被给出。在 [Cat] 中的一个同构，根据 Instance/Cat.v，是一个范畴的等价，它的同态集合类型是 Theory/Functor.v 的 [Functor_Setoid]，自然同构：问题中的“一个同构（或者，至少，一个等价）”以“或者，至少，一个等价”的形式满足，由恒等组件增强，这些组件正是将其引向 Mac Lane 的范畴同构的原因。两个范畴的严格恒等被拒绝（R19, R20）。在 Instance/StrictCat.v 中的一个同构，其同态集合要求对象映射的莱布尼茨等式，需要在这些分支下 fobj [EM_to_Smgrp ◯ Sg_K] 对每个 A 都有 A = A，因此绑定器下乘积的 η（乘法作为 fun p => ν(fst p, snd p) 回来，R3 和 R16）以及重建的证明字段的等式：外延性，经过论证而未被测量。该问题的前提，已注明日期。问题 #470 于 2026-07-23 提交。当提交时，“None of this is present”（没有 Smgrp 类别，没有自由半群函子）是准确的，并且在此次更改之前一直保持准确（对 .v 文件中半群类别、内部半群或自由半群进行 grep 仅找到文本）；Theory/Category/Semi.v 是半群图，Theory/Coq/Semigroup.v 是仅包含操作的类，如正文所述。其 [list_Monad]（Theory/Coq/List.v，带有 [flatten]）是作为 Coq 列表操作的自由单子单元，没有 [@Monad Coq list]，并且有一个 [IsMonad] 桥（Theory/Coq/Monad/Proofs.v）仅涵盖 Identity、箭头和 Compose：提交时准确，现在仍然准确，Theory/Coq/List.v 最后一次更改是在 c429a82b（2026-06-17）；正文按行引用了这些常量，这个树将其替换为名称。在它建议的模块中，Monad/Instance/ 不存在；相应的文件是 Instance/Smgrp.v（Mac Lane 对该范畴的命名，因为 Instance/Grp.v 和 Instance/SupLat.v 使用了它们自己的命名）以及这个文件，内部概念用的是 Theory/Algebra/Semigroup.v。它的“CLAUDE.md 关键文件索引”在归档时是准确的，但自 PR #1284（合并日期为 2026-09-09）之后就一直没有更新，该 PR 将索引移到了 docs/INDEX.md。优势。每个 [Example] 上方都保持在 [eq_refl]，并且 Test/ProbeWord470.v 重新陈述每一个（C19 到 C30, C33 到 C44 和 C46 到 C65）。仅在 ≈ 时：[alg_round_trip]、[cor_iterate]，以及 [Cat] 中两个同构的逆律，自然同构具有恒等组件。三个回读需要 #1347（Instance/Sets.v 的恒等和与它们的正确性字段的复合作为项）：[W_ret]、[WordMonad_direct_ret] 和 [WordMonad_direct_join] 在针对主分支 687ac356 的构建树编译此文件时被拒绝，“无法统一”，除此之外没有其他问题。十九个证明以 [Defined] 结束（按标记计算）。十八个是承重的，通过单独关闭每一个 [Qed] 并在目标的临时副本和探针中测量，第一个随后停止的命令是：[WordMonad_direct] ([WordMonad_direct_ret]), [alg_NAry_unit] ([WSys_rt_unit]，其唯一的使用者：关闭 [Qed]，并将其回读及其控制 C39 放到一边，其余的都可以编译，所以仅对该回读是透明的), [NAry_alg] ([NAry_round_trip]), [WSystemHom_Setoid], [WSystem_id] 和 [WSystem_compose] ([WSys]), [WSys] ([WSys_to_EM]), [WSys_to_EM] 和 [EM_to_WSys] ([WSys_EM_counit_iso]), [WSys_EM_counit_iso] 和 [WSys_EM_unit_iso] ([WSys_EM_iso]), [WSys_EM_iso] ([WSys_EM_iso_to]), [EM_sg_map] ([EM_to_Smgrp]), [EM_to_Smgrp] ([Smgrp_EM_counit_iso]), [Smgrp_EM_counit_iso] 和 [Smgrp_EM_unit_iso] ([Smgrp_EM_equivalence]), [Smgrp_EM_equivalence] ([Smgrp_EM_counit_component]) 和 [Smgrp_EM_iso] ([Smgrp_EM_iso_to]); [Sg_Forget_Monadic] 仅由数据约定定义为 [Defined]（关闭  
 [Qed]，没有什么能阻挡)。这十五个引理以 [Qed] 结尾。其中两个，辅助折叠引理 [tfoldl_tmap] 和 [tfold1_tmap]，陈述了半群元素之间的莱布尼茨等式，通过对元组进行归纳证明：比 ≈ 更强，这就是 [WordMonad_direct] 在使用第二个重写时所需的全部（Instance/Smgrp.v 的 [tfoldl_tapp] 和 [tfold1_tapp] 是另外两个，其 STRENGTHS 记录了扫描未找到第五个的情况）。每一次对探针的反驳都存在，
 在它的指令内，在三个目标的副本中，带有它们的所有
 四十一  [Qed] 已转为  [Defined] 并设置为 [Transparent Obligations]（[About] 报告了树中不透明的部分为透明），因此
 没有一个是这些文件的不透明；依赖闭包没有被翻转，上述原因（sigT 和 prod 没有 η，证明重建，数据停留在变量上）从术语中读取，但对于
 R21 的不透明义务，#470 审计已经测量（该备注）。UNIVERSES，读取 [About]。家族记录 [NAry]，其字段和构造函数 [nu_sharp]、[nu_unit]、[nu2]、[nu2_respects] 和 [cor_conditions] 仅使用大写绑定 @{o}。[Cat] 中的两个同构及其八个回读绑定 @{o so c}，条件为 o < so，o < c 和 so < c（Instance/Cat.v 的 [Cat@{c so so so o}]；[Smgrp_EM_iso] 是 [Isomorphism@{c so so}]）。其他所有内容都绑定 @{o so}，只有一个约束 o < so，除了大写字母：[WordMonad : Monad@{so o} WordF]、[WordAlg := EilenbergMoore@{so so so o}]（一个 [Category@{so o o}]）、[Smgrp_EM_equivalence : EquivalenceOfCategories@{so so so so so o}] 和 [Sg_Forget_Monadic : Monadic@{so so so so so o so so}]，Instance/SupLat/Free.v 的实例 [SL_Forget_Monadic]；[WSystem] 是一个 [Type@{so}]。大写字母是标准库的（pair 和 sigma 投影，compose，ID，RelationClasses.Defs，eq_ind，eq_ind_r，eq_rect_r，Logic_lemmas.equality，nat_rect，False_rect，prod_rect）。没有 [Set]，也没有方程，在 Rocq 9.1.1、Coq 8.19.2 和 8.20.1 上都是如此（通过脚本比较绑定级别之间的绑定器和约束）。

 未交付。本节的练习（#471 到 #474：关于 Mon 的 W₀、R-模、多项式环、Ab 上的环）。Smgrp 和 Set^W 的严格同一性（如上所拒绝），以及 Instance/StrictCat.v 中的同构（如上所论，需要外延性）。Beck 的单子性路径（Monad/Monadicity/Beck.v）未采用。W 的 Kleisli 范畴。一个合法的 [@Monad Coq list] 以及 Theory/Coq/List.v 的 [list_Monad] 中的范畴律，该问题的背景，仍然缺失。
*)

(* ------------------------------------------------------------------------ *)
(* * ** Proposition 1: the monad W of the adjunction Set ⇀ Smgrp / * ** 命题 1：伴随函子 Set ⇀ Smgrp 的幺半群 W *)

Definition WordF@{o so} : Sets@{o so} ⟶ Sets@{o so} :=
  Sg_Forget@{o so} ◯ Sg_Free@{o so}.

Definition WordMonad@{o so} : @Monad Sets@{o so} WordF@{o so} :=
  Adjunction_Induced_Monad Sg_adj@{o so}.

(* μ_X: a word of words, its outer brackets removed. / μ_X：一个词的词，其外部括号被移除。 *)
Definition pwconcat@{o so} {X : SetoidObject@{o o}}
  (ww : PWord@{o} (PWordObj@{o} X)) : PWord@{o} X :=
  pwfold (A := FreeSg@{o so} X) (fun w => w) ww.

(* W X = ∐_{n≥1} Xⁿ *)
Example W_obj@{o so} (X : SetoidObject@{o o}) :
  fobj[WordF@{o so}] X = PWordObj@{o} X := eq_refl.

Example W_carrier@{o so} (X : SetoidObject@{o o}) :
  carrier (fobj[WordF@{o so}] X) = sigT (fun n : nat => Tup@{o} X n)
  := eq_refl.

(* W f acts letterwise. / W f 按字母逐个处理。 *)
Example W_map@{o so} {X Y : SetoidObject@{o o}} (f : X ~{Sets@{o so}}~> Y)
  (w : PWord@{o} X) : fmap[WordF@{o so}] f w = pwmap f w := eq_refl.

(* η_X x = ⟨x⟩, as a setoid map. / η_X x = ⟨x⟩，作为集合等价映射。 *)
Example W_ret@{o so} (X : SetoidObject@{o o}) :
  @ret _ _ WordMonad@{o so} X = sg_insert@{o so} X := eq_refl.

Example W_ret_fun@{o so} (X : SetoidObject@{o o}) (x : X) :
  @ret _ _ WordMonad@{o so} X x = letter x := eq_refl.

(* μ = G ε F. *)
Example W_join_counit@{o so} (X : SetoidObject@{o o}) :
  @join _ _ WordMonad@{o so} X
    = fmap[Sg_Forget@{o so}]
        (@counit _ _ _ _ Sg_adj@{o so} (fobj[Sg_Free@{o so}] X))
  := eq_refl.

(* μ removes the outer brackets. / μ 移除外层括号。 *)
Example W_join_fun@{o so} (X : SetoidObject@{o o})
  (ww : PWord@{o} (PWordObj@{o} X)) :
  @join _ _ WordMonad@{o so} X ww = pwconcat@{o so} ww := eq_refl.

(* μ⟨⟨x11⟩⟨x12⟩⟩⟨⟨x21⟩⟩ = ⟨x11⟩⟨x12⟩⟨x21⟩, on a literal word of words. / μ⟨⟨x11⟩⟨x12⟩⟩⟨⟨x21⟩⟩ = ⟨x11⟩⟨x12⟩⟨x21⟩，按字面意思逐字翻译。 *)
Example W_join_literal@{o so} (X : SetoidObject@{o o}) (x11 x12 x21 : X) :
  @join _ _ WordMonad@{o so} X
    (existT (fun n => Tup (PWordObj X) n) 1%nat
       (existT (fun n => Tup X n) 1%nat (x11, x12), letter x21))
  = existT (fun n => Tup X n) 2%nat (x11, (x12, x21)) := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** The monad laws of W, verified directly on words / * ** W的单子定律，直接在词上验证 *)

Lemma tfoldl_acc_respects@{o so} {Y : Type@{o}} {A : SmgrpSets@{o so}}
  (h : Y → sg_ob@{o so} A) (n : nat) (acc acc' : sg_ob@{o so} A)
  (t : Tup@{o} Y n) :
  acc ≈ acc' → tfoldl h acc n t ≈ tfoldl h acc' n t.
Proof.
  revert acc acc'; induction n as [|n IH]; intros acc acc' H.
  - exact (sg_mul_respects A _ _ H _ _ (reflexivity _)).
  - destruct t as [y t']. apply IH.
    exact (sg_mul_respects A _ _ H _ _ (reflexivity _)).
Qed.

(* A semigroup map commutes with the fold. / 半群映射与折叠是可交换的。 *)
Lemma tfoldl_hom@{o so} {Y : Type@{o}} {A B : SmgrpSets@{o so}}
  (g : A ~{SmgrpSets@{o so}}~> B) (h : Y → sg_ob@{o so} A)
  (acc : sg_ob@{o so} A) (n : nat) (t : Tup@{o} Y n) :
  sg_fun g (tfoldl h acc n t)
    ≈ tfoldl (fun y => sg_fun g (h y)) (sg_fun g acc) n t.
Proof.
  revert acc; induction n as [|n IH]; intro acc.
  - exact (sg_fun_mul g acc (h t)).
  - destruct t as [y t']. cbn [tfoldl fst snd].
    rewrite IH.
    apply tfoldl_acc_respects.
    exact (sg_fun_mul g acc (h y)).
Qed.

Lemma tfold1_hom@{o so} {Y : Type@{o}} {A B : SmgrpSets@{o so}}
  (g : A ~{SmgrpSets@{o so}}~> B) (h : Y → sg_ob@{o so} A) (n : nat)
  (t : Tup@{o} Y n) :
  sg_fun g (tfold1 h n t) ≈ tfold1 (fun y => sg_fun g (h y)) n t.
Proof.
  destruct n as [|n]; [ reflexivity | ].
  destruct t as [y t']. exact (tfoldl_hom g h (h y) n t').
Qed.

Lemma tfoldl_tmap@{o so} {Y Z : Type@{o}} {A : SmgrpSets@{o so}}
  (h : Z → sg_ob@{o so} A) (g : Y → Z) (acc : sg_ob@{o so} A) (n : nat)
  (t : Tup@{o} Y n) :
  tfoldl h acc n (tmap g n t) = tfoldl (fun y => h (g y)) acc n t.
Proof.
  revert acc; induction n as [|n IH]; intro acc; [ reflexivity | apply IH ].
Qed.

Lemma tfold1_tmap@{o so} {Y Z : Type@{o}} {A : SmgrpSets@{o so}}
  (h : Z → sg_ob@{o so} A) (g : Y → Z) (n : nat) (t : Tup@{o} Y n) :
  tfold1 h n (tmap g n t) = tfold1 (fun y => h (g y)) n t.
Proof.
  destruct n as [|n]; [ reflexivity | apply tfoldl_tmap ].
Qed.

(* Appending the letters of t one at a time, on the right. / 将字母 t 一个一个地附加在右侧。 *)
Lemma tfoldl_letters@{o so} (X : SetoidObject@{o o}) (m : nat)
  (acc : PWord@{o} X) (t : Tup@{o} X m) :
  tfoldl (A := FreeSg@{o so} X) (fun w => w) acc m (tmap letter m t)
    ≈ pwapp acc (existT _ m t).
Proof.
  revert acc; induction m as [|m IH]; intro acc.
  - reflexivity.
  - destruct t as [z t'].
    transitivity (pwapp (pwapp acc (letter z)) (existT _ m t')).
    + exact (IH t' (pwapp acc (letter z))).
    + exact (pwapp_assoc acc (letter z) (existT _ m t')).
Qed.

(* Concatenation as a semigroup map F(W X) → F X. / 作为半群映射 F(W X) → F X 的连接。 *)
Definition pwconcat_hom@{o so} (X : SetoidObject@{o o}) :
  FreeSg@{o so} (PWordObj@{o} X) ~{SmgrpSets@{o so}}~> FreeSg@{o so} X :=
  sg_extend@{o so} (A := FreeSg@{o so} X)
    (@setoid_morphism_id@{o o o} (PWordObj@{o} X)).

(* Concatenation as a setoid map W W X → W X. / 作为集合态射的连接 W W X → W X。 *)
Definition pwconcat_map@{o so} (X : SetoidObject@{o o}) :
  fobj[WordF@{o so}] (fobj[WordF@{o so}] X) ~{Sets@{o so}}~>
  fobj[WordF@{o so}] X :=
  {| morphism := pwconcat@{o so}
   ; proper_morphism := fun ww vv H =>
       tfold1_respects (A := FreeSg@{o so} X) (fun w => w) (fun w => w)
         (fun _ _ E => E) _ _ _ _ H |}.

(*
 Mac Lane's direct verification of the laws of W: η the one-letter
 words, μ the concatenation, the laws by induction on words, without
 reference to the adjunction.  The fold and its homomorphism lemma are
 the free semigroup's ([pwconcat] folds in [FreeSg X], and [tfold1_hom]
 is applied to [pwconcat_hom] and [FreeSg_map f]), so this is not his
 “without overt reference to the notion of a semi-group”. 

 --------
 Mac Lane 对 W 定律的直接验证：η 是单字母词，μ 是连接操作，通过对词的归纳得到定律，而不参考伴随。fold 及其同态引理属于自由半群（[pwconcat] 在 [FreeSg X] 中折叠，且 [tfold1_hom] 应用于 [pwconcat_hom] 和 [FreeSg_map f]），所以这并不是他所说的“在不公开参考半群概念的情况下”。
*)
Definition WordMonad_direct@{o so} : @Monad Sets@{o so} WordF@{o so}.
Proof.
  unshelve refine
    (@Build_Monad Sets@{o so} WordF@{o so}
       (fun X => sg_insert@{o so} X)
       (fun X => pwconcat_map@{o so} X) _ _ _ _ _).
  - (* η natural *)
    intros X Y f x. reflexivity.
  - (* μ ∘ Wμ ≈ μ ∘ μW: three layers of brackets / μ ∘ Wμ ≈ μ ∘ μW：三层括号 *)
    intros X www.
    transitivity (tfold1 (A := FreeSg X) (fun y => pwconcat y)
                    (projT1 www) (projT2 www)).
    + change (tfold1 (A := FreeSg X) (fun w => w) (projT1 www)
                (tmap pwconcat (projT1 www) (projT2 www))
              ≈ tfold1 (A := FreeSg X) (fun y => pwconcat y)
                  (projT1 www) (projT2 www)).
      rewrite tfold1_tmap.
      reflexivity.
    + symmetry.
      exact (tfold1_hom (B := FreeSg X) (pwconcat_hom X)
               (fun w => w) (projT1 www) (projT2 www)).
  - (* μ ∘ Wη ≈ 1 *)
    intros X [k t]. destruct k as [|m]; [ reflexivity | ].
    destruct t as [z t'].
    exact (tfoldl_letters X m (letter z) t').
  - (* μ ∘ ηW ≈ 1 *)
    intros X w. reflexivity.
  - (* μ natural *)
    intros X Y f ww.
    transitivity (tfold1 (A := FreeSg Y)
                    (fun y => sg_fun (FreeSg_map f) y) (projT1 ww) (projT2 ww)).
    + change (tfold1 (A := FreeSg Y) (fun w => w) (projT1 ww)
                (tmap (sg_fun (FreeSg_map f)) (projT1 ww) (projT2 ww))
              ≈ tfold1 (A := FreeSg Y) (fun y => sg_fun (FreeSg_map f) y)
                  (projT1 ww) (projT2 ww)).
      rewrite tfold1_tmap.
      reflexivity.
    + symmetry.
      exact (tfold1_hom (FreeSg_map f) (fun w => w) (projT1 ww) (projT2 ww)).
Defined.

(* Its unit and multiplication ARE those of W, as setoid maps. / 它的单位和乘法作为集合等价映射是 W 的单位和乘法。 *)
Example WordMonad_direct_ret@{o so} (X : SetoidObject@{o o}) :
  @ret _ _ WordMonad_direct@{o so} X = @ret _ _ WordMonad@{o so} X
  := eq_refl.

Example WordMonad_direct_join@{o so} (X : SetoidObject@{o o}) :
  @join _ _ WordMonad_direct@{o so} X = @join _ _ WordMonad@{o so} X
  := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** Proposition 2: the W-algebras are the systems ⟨S, ν1, ν2, …⟩ / * ** 命题 2：W-代数是系统 ⟨S, ν1, ν2, …⟩ *)

(* The category of W-algebras in Set: [WordAlg] is Set^W. / 在集合中的 W-代数的范畴：[WordAlg] 是 Set^W。 *)
Definition WordAlg@{o so} : Category@{so o o} :=
  @EilenbergMoore@{so so so o} Sets@{o so} WordF@{o so} WordMonad@{o so}.

(* One operation ν_{n+1} : S^{n+1} → S for each n, respecting ≈. The heterogeneous form of the respect law costs nothing, since [tup_eq] is False across lengths. / 对于每个 n，有一个运算 ν_{n+1} : S^{n+1} → S，遵循 ≈。尊重定律的异质形式不产生任何代价，因为 [tup_eq] 在各个长度上都是 False。 *)
Record NAry@{o} (X : SetoidObject@{o o}) : Type@{o} := {
  nu : ∀ n : nat, Tup@{o} X n → X;
  nu_respects : ∀ (n m : nat) (t : Tup@{o} X n) (u : Tup@{o} X m),
    tup_eq n m t u → nu n t ≈ nu m u
}.

Arguments nu {X} _ _ _.
Arguments nu_respects {X} _ _ _ _ _ _.

(* The copairing ∐_n S^(n+1) → S of the family. / 族的协配对 ∐_n S^(n+1) → S。 *)
Definition nu_sharp@{o} {X : SetoidObject@{o o}} (ν : NAry@{o} X)
  (p : PWord@{o} X) : X :=
  nu ν (projT1 p) (projT2 p).

(* ν1 = 1. *)
Definition nu_unit@{o} {X : SetoidObject@{o o}} (ν : NAry@{o} X) :
  Type@{o} :=
  ∀ x : X, nu ν O x ≈ x.

(*
 (2): νk (ν_{n1} × ⋯ × ν_{nk}) = ν_{n1+⋯+nk}, at each k-tuple of words
 (w1, …, wk), wi in S^{ni}: ν_k of the values of the wi is ν of their
 concatenation w1 ⋯ wk, whose length is n1 + ⋯ + nk. 

 --------
 (2)：νk (ν_{n1} × ⋯ × ν_{nk}) = ν_{n1+⋯+nk}，对于每一个 k 元组的单词 (w1, …, wk)，其中 wi 在 S^{ni}：wi 的值的 ν_k 是它们连接 w1 ⋯ wk 的 ν，长度为 n1 + ⋯ + nk。
*)
Definition nu_assoc@{o so} {X : SetoidObject@{o o}} (ν : NAry@{o} X) :
  Type@{o} :=
  ∀ (k : nat) (tt : Tup@{o} (PWordObj@{o} X) k),
    nu ν k (tmap (nu_sharp ν) k tt)
      ≈ nu_sharp ν (pwconcat@{o so} (existT _ k tt)).

(* An algebra ⟨S, h⟩ gives a family: ν_n is h on S^n. / 一个代数 ⟨S, h⟩ 提供一个族：ν_n 是 S^n 上的 h。 *)
Definition alg_NAry@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} WordF@{o so} WordMonad@{o so} X) :
  NAry@{o} X :=
  {| nu := fun n t => t_alg[α] (existT (fun n0 => Tup X n0) n t)
   ; nu_respects := fun n m t u H =>
       proper_morphism (t_alg[α]) (existT _ n t) (existT _ m u) H |}.

(* ...in which h is the copairing of its family, at each (n; t). / ...其中 h 是其族在每个 (n; t) 的共配对。 *)
Example alg_NAry_at@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} WordF@{o so} WordMonad@{o so} X) (n : nat)
  (t : Tup@{o} X n) :
  nu (alg_NAry α) n t = t_alg[α] (existT _ n t) := eq_refl.

(*
 The unit law of the algebra IS ν1 = 1.  Transparent, so that the unit
 law of a system comes back from Set^W on the nose ([WSys_rt_unit]);
 that readback is the only consumer of the transparency (the header's
 STRENGTHS). 

 --------
 代数的单位律是 ν1 = 1。透明，因此系统的单位律可以直接从 Set^W 恢复（[WSys_rt_unit]）；这种回读是透明性的唯一使用者（标题的 STRENGTHS）。
*)
Definition alg_NAry_unit@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} WordF@{o so} WordMonad@{o so} X) :
  nu_unit (alg_NAry α).
Proof. intro x. exact (@t_id _ _ _ _ α x). Defined.

(* The action law of the algebra gives (2). / 代数的作用律给出了 (2)。 *)
Lemma alg_NAry_assoc@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} WordF@{o so} WordMonad@{o so} X) :
  nu_assoc@{o so} (alg_NAry α).
Proof.
  intros k tt.
  transitivity (t_alg[α] (fmap[WordF@{o so}] (t_alg[α]) (existT _ k tt))).
  - apply (proper_morphism (t_alg[α])).
    exact (tmap_respects (X := PWordObj X) (Y := X)
             (nu_sharp (alg_NAry α)) (t_alg[α])
             (fun p q H => proper_morphism (t_alg[α])
                             (existT _ (projT1 p) (projT2 p)) q H) k k tt tt
             (tup_eq_refl (X := PWordObj X) k tt)).
  - transitivity (t_alg[α] (pwconcat@{o so} (existT _ k tt))).
    + exact (@t_action _ _ _ _ α (existT _ k tt)).
    + apply (proper_morphism (t_alg[α])).
      exact (tup_eq_refl _ (projT2 (pwconcat@{o so} (existT _ k tt)))).
Qed.

(* A family with ν1 = 1 and (2) is an algebra: its structure map is the copairing, and the two algebra laws ARE the two conditions, read at each word by conversion. / 一个具有 ν1 = 1 和 (2) 的族是一个代数：它的结构映射是共配对，并且两个代数律就是这两个条件，通过转换在每个词上读取。 *)
Definition NAry_alg@{o so} {X : SetoidObject@{o o}} (ν : NAry@{o} X)
  (Hu : nu_unit ν) (Ha : nu_assoc@{o so} ν) :
  @TAlgebra Sets@{o so} WordF@{o so} WordMonad@{o so} X.
Proof.
  unshelve refine
    (@Build_TAlgebra Sets@{o so} WordF@{o so} WordMonad@{o so} X
       {| morphism := nu_sharp ν
        ; proper_morphism := fun p q H => nu_respects ν _ _ _ _ H |} _ _).
  - intro x. exact (Hu x).
  - intro ww. exact (Ha (projT1 ww) (projT2 ww)).
Defined.

(* Family → algebra → family returns the family itself. / 家庭 → 代数 → 家庭返回家庭本身。 *)
Example NAry_round_trip@{o so} {X : SetoidObject@{o o}} (ν : NAry@{o} X)
  (Hu : nu_unit ν) (Ha : nu_assoc@{o so} ν) :
  alg_NAry (NAry_alg@{o so} ν Hu Ha) = ν := eq_refl.

(* Algebra → family → algebra returns the structure map up to ≈: the rebuilt map reads h at (projT1 p; projT2 p), and sigT has no η. / 代数 → 家族 → 代数 返回结构映射至 ≈：重建的映射在 (projT1 p; projT2 p) 处读取 h，并且 sigT 没有 η。 *)
Lemma alg_round_trip@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} WordF@{o so} WordMonad@{o so} X) :
  t_alg[NAry_alg@{o so} (alg_NAry α) (alg_NAry_unit α) (alg_NAry_assoc α)]
    ≈ t_alg[α].
Proof.
  intro p. apply (proper_morphism (t_alg[α])).
  exact (tup_eq_refl _ (projT2 p)).
Qed.

(* A morphism of systems: f νn = ν'n fⁿ for every n. / 系统的一个态射：对于每个 n，有 f νn = ν'n fⁿ。 *)
Definition NAry_hom@{o so} {X Y : SetoidObject@{o o}} (ν : NAry@{o} X)
  (ν' : NAry@{o} Y) (f : X ~{Sets@{o so}}~> Y) : Type@{o} :=
  ∀ (n : nat) (t : Tup@{o} X n), f (nu ν n t) ≈ nu ν' n (tmap f n t).

(*
 The morphism clause, both ways: an algebra map is a map commuting with
 every νn, and conversely. 

 --------
 态射子句，两方面：代数映射是与每个 νn 交换的映射，反之亦然。
*)
Lemma alg_hom_NAry_hom@{o so} {X Y : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} WordF@{o so} WordMonad@{o so} X)
  (β : @TAlgebra Sets@{o so} WordF@{o so} WordMonad@{o so} Y)
  (f : X ~{Sets@{o so}}~> Y) :
  f ∘ t_alg[α] ≈ t_alg[β] ∘ fmap[WordF@{o so}] f →
  NAry_hom@{o so} (alg_NAry α) (alg_NAry β) f.
Proof. intros H n t. exact (H (existT _ n t)). Qed.

Lemma NAry_hom_alg_hom@{o so} {X Y : SetoidObject@{o o}}
  (ν : NAry@{o} X) (ν' : NAry@{o} Y) (Hu : nu_unit ν)
  (Ha : nu_assoc@{o so} ν) (Hu' : nu_unit ν') (Ha' : nu_assoc@{o so} ν')
  (f : X ~{Sets@{o so}}~> Y) :
  NAry_hom@{o so} ν ν' f →
  f ∘ t_alg[NAry_alg@{o so} ν Hu Ha]
    ≈ t_alg[NAry_alg@{o so} ν' Hu' Ha'] ∘ fmap[WordF@{o so}] f.
Proof. intros H p. exact (H (projT1 p) (projT2 p)). Qed.

(* ------------------------------------------------------------------------ *)
(* * ** Proposition 2 as a category: systems ⟨S, ν1, ν2, …⟩ ≅ Set^W / * ** 命题 2 作为一个范畴：系统 ⟨S, ν1, ν2, …⟩ ≅ Set^W *)

Record WSystem@{o so} : Type@{so} := {
  ws_set : SetoidObject@{o o};
  ws_nu : NAry@{o} ws_set;
  ws_unit : nu_unit ws_nu;
  ws_assoc : nu_assoc@{o so} ws_nu
}.

Definition WSystemHom@{o so} (A B : WSystem@{o so}) : Type@{o} :=
  { f : ws_set A ~{Sets@{o so}}~> ws_set B
  & NAry_hom@{o so} (ws_nu A) (ws_nu B) f }.

Definition WSystemHom_Setoid@{o so} (A B : WSystem@{o so}) :
  Setoid@{o o} (WSystemHom@{o so} A B).
Proof.
  refine {| equiv := fun f g =>
                @equiv _ (@homset Sets@{o so} (ws_set A) (ws_set B))
                  (`1 f) (`1 g) |}.
  constructor.
  - intros f. reflexivity.
  - intros f g H. symmetry. exact H.
  - intros f g h H1 H2. transitivity (`1 g); assumption.
Defined.

Definition WSystem_id@{o so} (A : WSystem@{o so}) : WSystemHom@{o so} A A.
Proof.
  exists (@setoid_morphism_id@{o o o} (ws_set A)).
  intros n t. apply (nu_respects (ws_nu A)).
  exact (tup_eq_sym _ _ _ _ (tmap_id n t)).
Defined.

Definition WSystem_compose@{o so} {A B C : WSystem@{o so}}
  (f : WSystemHom@{o so} B C) (g : WSystemHom@{o so} A B) :
  WSystemHom@{o so} A C.
Proof.
  exists (@setoid_morphism_compose@{o o o} _ _ _ (`1 f) (`1 g)).
  intros n t. simpl.
  transitivity (`1 f (nu (ws_nu B) n (tmap (`1 g) n t))).
  - apply (proper_morphism (`1 f)). exact (`2 g n t).
  - transitivity (nu (ws_nu C) n (tmap (`1 f) n (tmap (`1 g) n t))).
    + exact (`2 f n _).
    + apply (nu_respects (ws_nu C)).
      exact (tup_eq_sym _ _ _ _ (tmap_comp (`1 f) (`1 g) n t)).
Defined.

(* The category of the systems of Proposition 2. / 命题2系统的类别。 *)
Definition WSys@{o so} : Category@{so o o}.
Proof.
  unshelve refine
    {| obj     := WSystem@{o so}
     ; hom     := WSystemHom@{o so}
     ; homset  := WSystemHom_Setoid@{o so}
     ; id      := WSystem_id@{o so}
     ; compose := @WSystem_compose@{o so} |}.
  - intros A B C f f' Hf g g' Hg a. simpl.
    transitivity (`1 f (`1 g' a)).
    + apply (proper_morphism (`1 f)). exact (Hg a).
    + exact (Hf _).
  - intros A B f a. reflexivity.
  - intros A B f a. reflexivity.
  - intros A B C D f g h a. reflexivity.
  - intros A B C D f g h a. reflexivity.
Defined.

(* A system is an algebra: the copairing, with the two conditions. / 一个系统是一个代数：具有两个条件的共配对。 *)
Definition WSys_to_EM@{o so} : WSys@{o so} ⟶ WordAlg@{o so}.
Proof.
  unshelve refine
    (@Build_Functor WSys@{o so} WordAlg@{o so}
       (fun A => existT _ (ws_set A)
                   (NAry_alg@{o so} (ws_nu A) (ws_unit A) (ws_assoc A)))
       (fun A B f =>
          @Build_TAlgebraHom Sets@{o so} WordF@{o so} WordMonad@{o so}
            (ws_set A) (ws_set B)
            (NAry_alg@{o so} (ws_nu A) (ws_unit A) (ws_assoc A))
            (NAry_alg@{o so} (ws_nu B) (ws_unit B) (ws_assoc B))
            (`1 f)
            (NAry_hom_alg_hom@{o so} _ _ _ _ _ _ (`1 f) (`2 f)))
       _ _ _).
  - intros A B f g H a. exact (H a).
  - intros A a. reflexivity.
  - intros A B C f g a. reflexivity.
Defined.

(* An algebra is a system: ν_n is h on S^n. / 一个代数是一个系统：ν_n 在 S^n 上是 h。 *)
Definition EM_to_WSys@{o so} : WordAlg@{o so} ⟶ WSys@{o so}.
Proof.
  unshelve refine
    (@Build_Functor WordAlg@{o so} WSys@{o so}
       (fun x => {| ws_set := projT1 x
                  ; ws_nu := alg_NAry@{o so} (projT2 x)
                  ; ws_unit := alg_NAry_unit@{o so} (projT2 x)
                  ; ws_assoc := alg_NAry_assoc@{o so} (projT2 x) |})
       (fun x y f =>
          existT _ (t_alg_hom[f])
            (alg_hom_NAry_hom@{o so} (projT2 x) (projT2 y) (t_alg_hom[f])
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
Definition WSys_EM_counit_iso@{o so} (x : WordAlg@{o so}) :
  @Isomorphism WordAlg@{o so} (fobj[WSys_to_EM@{o so} ◯ EM_to_WSys@{o so}] x)
    x.
Proof.
  unshelve refine
    (@Build_Isomorphism WordAlg@{o so}
       (fobj[WSys_to_EM@{o so} ◯ EM_to_WSys@{o so}] x) x
       (@Build_TAlgebraHom Sets@{o so} WordF@{o so} WordMonad@{o so}
          (projT1 x) (projT1 x)
          (projT2 (fobj[WSys_to_EM@{o so} ◯ EM_to_WSys@{o so}] x))
          (projT2 x) (@setoid_morphism_id@{o o o} (projT1 x)) _)
       (@Build_TAlgebraHom Sets@{o so} WordF@{o so} WordMonad@{o so}
          (projT1 x) (projT1 x) (projT2 x)
          (projT2 (fobj[WSys_to_EM@{o so} ◯ EM_to_WSys@{o so}] x))
          (@setoid_morphism_id@{o o o} (projT1 x)) _) _ _).
  - intro p. simpl. apply (proper_morphism (t_alg[projT2 x])).
    exact (tup_eq_sym _ _ _ _ (tmap_id (projT1 p) (projT2 p))).
  - intro p. simpl. apply (proper_morphism (t_alg[projT2 x])).
    exact (tup_eq_sym _ _ _ _ (tmap_id (projT1 p) (projT2 p))).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(* The system round trip, with the identity as its component. / 系统往返，身份作为其组成部分。 *)
Definition WSys_EM_unit_iso@{o so} (A : WSys@{o so}) :
  @Isomorphism WSys@{o so} (fobj[EM_to_WSys@{o so} ◯ WSys_to_EM@{o so}] A) A.
Proof.
  unshelve refine
    (@Build_Isomorphism WSys@{o so}
       (fobj[EM_to_WSys@{o so} ◯ WSys_to_EM@{o so}] A) A
       (existT _ (@setoid_morphism_id@{o o o} (ws_set A)) _)
       (existT _ (@setoid_morphism_id@{o o o} (ws_set A)) _) _ _).
  - intros n t. simpl. apply (nu_respects (ws_nu A)).
    exact (tup_eq_sym _ _ _ _ (tmap_id n t)).
  - intros n t. simpl. apply (nu_respects (ws_nu A)).
    exact (tup_eq_sym _ _ _ _ (tmap_id n t)).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(*
 Proposition 2, packaged: the category of systems is isomorphic in Cat
 to Set^W, both legs the two functors and every component of both
 natural isomorphisms the identity.  An isomorphism in Cat is, by
 Instance/Cat.v, an equivalence of categories; the identity components
 are what bring this one toward an isomorphism of categories. 

 --------
 命题 2，封装：系统的范畴在 Cat 中同构于 Set^W，两条腿都是两个函子，并且两个自然同构的每个分量都是恒等映射。Cat 中的同构，根据 Instance/Cat.v，是范畴的等价；恒等分量是使其接近范畴同构的因素。
*)
Definition WSys_EM_iso@{o so c} :
  @Isomorphism Cat@{c so so so o} WSys@{o so} WordAlg@{o so}.
Proof.
  unshelve refine
    (@Build_Isomorphism Cat@{c so so so o} WSys@{o so} WordAlg@{o so}
       WSys_to_EM@{o so} EM_to_WSys@{o so} _ _).
  - exists (fun x => WSys_EM_counit_iso@{o so} x).
    intros x y f a. reflexivity.
  - exists (fun A => WSys_EM_unit_iso@{o so} A).
    intros A B f a. reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(* * ** The Corollary: one associative binary operation, iterated / * ** 推论：一个结合二元运算，迭代 *)

Definition nu2@{o} {X : SetoidObject@{o o}} (ν : NAry@{o} X) (a b : X) : X :=
  nu ν 1%nat (a, b).

(* ν1 = 1, ν2 associative, and ν_{n+1} = ν_n (ν2 × 1) for n ≥ 2, read at n = m + 2 on the tuple (x, y, t). / ν1 = 1，ν2 可结合，并且 ν_{n+1} = ν_n (ν2 × 1) 对于 n ≥ 2，在元组 (x, y, t) 上读取时 n = m + 2。 *)
Definition cor_conditions@{o} {X : SetoidObject@{o o}} (ν : NAry@{o} X) :
  Type@{o} :=
  nu_unit ν
  * (∀ a b c : X, nu2 ν (nu2 ν a b) c ≈ nu2 ν a (nu2 ν b c))
  * (∀ (m : nat) (x y : X) (t : Tup@{o} X m),
       nu ν (S (S m)) (x, (y, t)) ≈ nu ν (S m) (nu2 ν x y, t)).

Lemma nu2_respects@{o} {X : SetoidObject@{o o}} (ν : NAry@{o} X) :
  Proper (equiv ==> equiv ==> equiv) (nu2 ν).
Proof.
  intros a a' Ha b b' Hb. unfold nu2.
  apply (nu_respects ν 1%nat 1%nat). split; assumption.
Qed.

(* (2) at three tuples: (⟨ab⟩, ⟨c⟩), (⟨a⟩, ⟨bc⟩), and ⟨xy⟩ followed by the letters of t. / (2) 在三个元组处： (⟨ab⟩, ⟨c⟩), (⟨a⟩, ⟨bc⟩), 以及 ⟨xy⟩，随后是 t 的字母。 *)
Lemma cor_forward@{o so} {X : SetoidObject@{o o}} (ν : NAry@{o} X) :
  nu_unit ν → nu_assoc@{o so} ν → cor_conditions ν.
Proof.
  intros Hu Ha. split; [ split | ].
  - exact Hu.
  - intros a b c.
    (* both sides are ν3(a, b, c) / 两边都是 ν3(a, b, c) *)
    transitivity (nu ν 2%nat (a, (b, c))).
    + pose proof (Ha 1%nat (existT _ 1%nat (a, b), letter c)) as H.
      transitivity (nu ν 1%nat (nu ν 1%nat (a, b), nu ν O c)); [ | exact H ].
      apply nu2_respects; [ reflexivity | symmetry; exact (Hu c) ].
    + pose proof (Ha 1%nat (letter a, existT _ 1%nat (b, c))) as H.
      symmetry.
      transitivity (nu ν 1%nat (nu ν O a, nu ν 1%nat (b, c))); [ | exact H ].
      apply nu2_respects; [ symmetry; exact (Hu a) | reflexivity ].
  - intros m x y t.
    pose proof (Ha (S m) (existT _ 1%nat (x, y), tmap letter m t)) as H.
    symmetry.
    transitivity (nu ν (S m) (nu ν 1%nat (x, y),
                              tmap (nu_sharp ν) m (tmap letter m t))).
    + apply (nu_respects ν (S m) (S m)). split; [ reflexivity | ].
      clear H. induction m as [|m IH]; [ cbn; symmetry; exact (Hu t) | ].
      destruct t as [z t']. split; [ symmetry; exact (Hu z) | exact (IH t') ].
    + transitivity
        (nu_sharp ν (pwconcat@{o so}
                       (existT _ (S m)
                          (existT _ 1%nat (x, y), tmap letter m t))));
        [ exact H | ].
      apply (nu_respects ν).
      exact (tfoldl_letters X m (existT _ 1%nat (x, y)) t).
Qed.

(* Given the three conditions, ν2 makes S a semigroup... / 考虑这三个条件，ν2 使 S 成为半群... *)
Definition nu2_sg@{o so} {X : SetoidObject@{o o}} (ν : NAry@{o} X)
  (Hc : cor_conditions ν) : SmgrpSets@{o so} :=
  mk_sg_obj@{o so} X (nu2 ν) (nu2_respects ν) (snd (fst Hc)).

(* ...and νn is its n-fold product: Mac Lane's “Similarly, νn must be the n-fold product”. / ...并且 νn 是它的 n 重积：Mac Lane 的“同样地，νn 必须是 n 重积”. *)
Lemma cor_iterate@{o so} {X : SetoidObject@{o o}} (ν : NAry@{o} X)
  (Hc : cor_conditions ν) (n : nat) (t : Tup@{o} X n) :
  nu ν n t ≈ tfold1 (A := nu2_sg@{o so} ν Hc) (fun s => s) n t.
Proof.
  destruct n as [|n]; [ exact (fst (fst Hc) t) | ].
  revert t; induction n as [|n IH]; intro t.
  - destruct t as [x y]. reflexivity.
  - destruct t as [x [y t']].
    transitivity (nu ν (S n) (nu2 ν x y, t')).
    + exact (snd Hc n x y t').
    + exact (IH (nu2 ν x y, t')).
Qed.

(* Backward: the iterated products satisfy (2), because the comparison algebra of that semigroup satisfies its action law ([EM_Comparison_Algebra_action], Monad/Comparison.v). / 向后：迭代的乘积满足 (2)，因为该半群的比较代数满足其作用律 ([EM_Comparison_Algebra_action]，Monad/Comparison.v)。 *)
Lemma cor_backward@{o so} {X : SetoidObject@{o o}} (ν : NAry@{o} X) :
  cor_conditions ν → nu_unit ν * nu_assoc@{o so} ν.
Proof.
  intro Hc. split; [ exact (fst (fst Hc)) | ].
  intros k tt.
  set (A := nu2_sg@{o so} ν Hc).
  pose proof (@EM_Comparison_Algebra_action _ _ _ _ Sg_adj@{o so} A
                (existT _ k tt)) as Hact.
  transitivity
    (tfold1 (A := A) (fun s => s) k
       (tmap (fun p => tfold1 (A := A) (fun s => s) (projT1 p) (projT2 p))
          k tt)).
  - transitivity
      (nu ν k (tmap (fun p => tfold1 (A := A) (fun s => s)
                                (projT1 p) (projT2 p)) k tt)).
    + apply (nu_respects ν k k).
      apply (tmap_respects (X := PWordObj X) (Y := X)).
      * intros p q Hpq. unfold nu_sharp.
        transitivity (nu ν (projT1 q) (projT2 q));
          [ exact (nu_respects ν _ _ _ _ Hpq) | exact (cor_iterate ν Hc _ _) ].
      * exact (tup_eq_refl (X := PWordObj X) k tt).
    + exact (cor_iterate ν Hc k _).
  - transitivity (tfold1 (A := A) (fun s => s) _
                    (projT2 (pwconcat@{o so} (existT _ k tt)))).
    + exact Hact.
    + symmetry. exact (cor_iterate ν Hc _ _).
Qed.

(* The Corollary: ⟨S, ν1, ν2, …⟩ is a W-algebra iff ν1 = 1, ν2 is associative and ν_{n+1} = ν_n (ν2 × 1) for n ≥ 2. / 推论：⟨S, ν1, ν2, …⟩ 是 W-代数，当且仅当 ν1 = 1，ν2 是结合的，并且对于 n ≥ 2，有 ν_{n+1} = ν_n (ν2 × 1)。 *)
Theorem NAry_corollary@{o so} {X : SetoidObject@{o o}} (ν : NAry@{o} X) :
  iffT@{o o} (nu_unit ν * nu_assoc@{o so} ν) (cor_conditions ν).
Proof.
  split.
  - intros [Hu Ha]. exact (cor_forward ν Hu Ha).
  - exact (cor_backward ν).
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** The comparison K : Smgrp → Set^W is an isomorphism / * ** 比较 K : Smgrp → Set^W 是一个同构 *)

Definition Sg_K@{o so} : SmgrpSets@{o so} ⟶ WordAlg@{o so} :=
  EM_Comparison Sg_adj@{o so}.

(* The semigroup of an algebra: ν2(a, b) = h⟨a b⟩, associative by the Corollary's forward half. / 一个代数的半群：ν2(a, b) = h⟨a b⟩，由推论的前半部分可得结合性。 *)
Definition EM_sg@{o so} (x : WordAlg@{o so}) : SmgrpSets@{o so} :=
  nu2_sg@{o so} (alg_NAry (projT2 x))
    (cor_forward (alg_NAry (projT2 x)) (alg_NAry_unit (projT2 x))
       (alg_NAry_assoc (projT2 x))).

Definition EM_sg_map@{o so} {x y : WordAlg@{o so}}
  (f : x ~{WordAlg@{o so}}~> y) : EM_sg@{o so} x ~{SmgrpSets@{o so}}~> EM_sg y.
Proof.
  refine (@mk_sg_hom@{o so} (EM_sg x) (EM_sg y) (t_alg_hom[f])
            (proper_morphism (t_alg_hom[f])) _).
  intros a b.
  exact (@t_alg_hom_commutes _ _ _ _ _ _ _ f (existT _ 1%nat (a, b))).
Defined.

Definition EM_to_Smgrp@{o so} : WordAlg@{o so} ⟶ SmgrpSets@{o so}.
Proof.
  unshelve refine
    (@Build_Functor WordAlg@{o so} SmgrpSets@{o so} EM_sg@{o so}
       (fun x y f => EM_sg_map@{o so} f) _ _ _).
  - intros x y f g H. exact H.
  - intros x a. reflexivity.
  - intros x y z f g a. reflexivity.
Defined.

(* The algebra round trip, with the identity as its component. / 代数往返，以恒等式作为其组成部分。 *)
Definition Smgrp_EM_counit_iso@{o so} (x : WordAlg@{o so}) :
  @Isomorphism WordAlg@{o so} (fobj[Sg_K@{o so} ◯ EM_to_Smgrp@{o so}] x) x.
Proof.
  set (ν := alg_NAry (projT2 x)).
  set (Hc := cor_forward ν (alg_NAry_unit (projT2 x))
               (alg_NAry_assoc (projT2 x))).
  unshelve refine
    (@Build_Isomorphism WordAlg@{o so}
       (fobj[Sg_K@{o so} ◯ EM_to_Smgrp@{o so}] x) x
       (@Build_TAlgebraHom Sets@{o so} WordF@{o so} WordMonad@{o so}
          (projT1 x) (projT1 x)
          (projT2 (fobj[Sg_K@{o so} ◯ EM_to_Smgrp@{o so}] x)) (projT2 x)
          (@setoid_morphism_id@{o o o} (projT1 x)) _)
       (@Build_TAlgebraHom Sets@{o so} WordF@{o so} WordMonad@{o so}
          (projT1 x) (projT1 x) (projT2 x)
          (projT2 (fobj[Sg_K@{o so} ◯ EM_to_Smgrp@{o so}] x))
          (@setoid_morphism_id@{o o o} (projT1 x)) _) _ _).
  - intro p. cbn.
    transitivity (nu ν (projT1 p) (projT2 p)).
    + symmetry. exact (cor_iterate ν Hc (projT1 p) (projT2 p)).
    + apply (proper_morphism (t_alg[projT2 x])).
      exact (tup_eq_sym _ _ _ _ (tmap_id (projT1 p) (projT2 p))).
  - intro p. cbn.
    transitivity (nu ν (projT1 p) (projT2 p)).
    + apply (proper_morphism (t_alg[projT2 x])).
      exact (tup_eq_refl _ (projT2 p)).
    + transitivity (tfold1 (A := EM_sg x) (fun s => s) (projT1 p) (projT2 p)).
      * exact (cor_iterate ν Hc (projT1 p) (projT2 p)).
      * apply (tfold1_respects (A := EM_sg x) (fun s => s) (fun s => s)
                 (fun a b H => H)).
        exact (tup_eq_sym _ _ _ _ (tmap_id (projT1 p) (projT2 p))).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(* The semigroup round trip, with the identity as its component. / 半群往返，其组成部分为单位元。 *)
Definition Smgrp_EM_unit_iso@{o so} (A : SmgrpSets@{o so}) :
  @Isomorphism SmgrpSets@{o so} (fobj[EM_to_Smgrp@{o so} ◯ Sg_K@{o so}] A) A.
Proof.
  unshelve refine
    (@Build_Isomorphism SmgrpSets@{o so}
       (fobj[EM_to_Smgrp@{o so} ◯ Sg_K@{o so}] A) A
       (@mk_sg_hom@{o so} (fobj[EM_to_Smgrp@{o so} ◯ Sg_K@{o so}] A) A
          (fun a => a) (fun a b H => H) _)
       (@mk_sg_hom@{o so} A (fobj[EM_to_Smgrp@{o so} ◯ Sg_K@{o so}] A)
          (fun a => a) (fun a b H => H) _) _ _).
  - intros a b. reflexivity.
  - intros a b. reflexivity.
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(* The Remark: K is an equivalence, with identity components both ways. / 备注：K 是一个等价关系，两个方向上的恒等分量都存在。 *)
Definition Smgrp_EM_equivalence@{o so} :
  @EquivalenceOfCategories@{so so so so so o} SmgrpSets@{o so}
    WordAlg@{o so} Sg_K@{o so}.
Proof.
  unshelve refine
    (@Build_EquivalenceOfCategories _ _ Sg_K@{o so} EM_to_Smgrp@{o so} _ _).
  - exists (fun x => Smgrp_EM_counit_iso@{o so} x).
    intros x y f a. reflexivity.
  - exists (fun A => iso_sym (Smgrp_EM_unit_iso@{o so} A)).
    intros A B f a. reflexivity.
Defined.

(* Semigroups are monadic over Set. / 半群在集合上是幺半的。 *)
Definition Sg_Forget_Monadic@{o so} :
  @Monadic@{so so so so so o so so} SmgrpSets@{o so} Sets@{o so}
    Sg_Forget@{o so}.
Proof.
  exists Sg_Free@{o so}.
  exists Sg_adj@{o so}.
  exact Smgrp_EM_equivalence@{o so}.
Defined.

(*
 “In other words, K is an isomorphism”: Smgrp ≅ Set^W in Cat, built from
 the two component isomorphisms so that both of its natural
 isomorphisms have the identity as every component.  An isomorphism in
 Cat is, by Instance/Cat.v, an equivalence of categories: this is the
 issue's “or, minimally, an equivalence”, strengthened by the identity
 components toward Mac Lane's isomorphism (the header's THE REMARK). 

 --------
 换句话说，K 是一个同构：Smgrp ≅ Set^W 在 Cat 中，由两个分量同构构建，因此它的两个自然同构的每个分量都是恒等的。根据 Instance/Cat.v，Cat 中的同构是类别的一个等价：这是本期的“或者，至少，一个等价”的问题，通过恒等分量加强到 Mac Lane 的同构（标题中的注释）。
*)
Definition Smgrp_EM_iso@{o so c} :
  @Isomorphism Cat@{c so so so o} SmgrpSets@{o so} WordAlg@{o so}.
Proof.
  unshelve refine
    (@Build_Isomorphism Cat@{c so so so o} SmgrpSets@{o so} WordAlg@{o so}
       Sg_K@{o so} EM_to_Smgrp@{o so} _ _).
  - exists (fun x => Smgrp_EM_counit_iso@{o so} x).
    intros x y f a. reflexivity.
  - exists (fun A => Smgrp_EM_unit_iso@{o so} A).
    intros A B f a. reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** Readbacks / ** 回读 *)

(* The two legs of each isomorphism in Cat are the two functors. / Cat 中每个同构的两个分支是两个函子。 *)
Example Smgrp_EM_iso_to@{o so c} :
  to Smgrp_EM_iso@{o so c} = Sg_K@{o so} := eq_refl.

Example Smgrp_EM_iso_from@{o so c} :
  from Smgrp_EM_iso@{o so c} = EM_to_Smgrp@{o so} := eq_refl.

Example WSys_EM_iso_to@{o so c} :
  to WSys_EM_iso@{o so c} = WSys_to_EM@{o so} := eq_refl.

Example WSys_EM_iso_from@{o so c} :
  from WSys_EM_iso@{o so c} = EM_to_WSys@{o so} := eq_refl.

(* The Remark's K ⟨S, ν⟩ = ⟨S, 1, ν2, …⟩: the carrier, the structure map G ε_S, its value the left-bracketed product, ν1 = 1, ν2 = ν, and νn the iterate of ν. / Remark的 K ⟨S, ν⟩ = ⟨S, 1, ν2, …⟩：载体，结构映射G ε_S，其值为左括号乘积，ν1 = 1，ν2 = ν，νn为ν的迭代。 *)
Example Sg_K_carrier@{o so} (A : SmgrpSets@{o so}) :
  projT1 (fobj[Sg_K@{o so}] A) = sg_ob A := eq_refl.

Example Sg_K_alg@{o so} (A : SmgrpSets@{o so}) :
  t_alg[projT2 (fobj[Sg_K@{o so}] A)]
    = fmap[Sg_Forget@{o so}] (@counit _ _ _ _ Sg_adj@{o so} A) := eq_refl.

Example Sg_K_alg_fun@{o so} (A : SmgrpSets@{o so})
  (p : PWord@{o} (sg_ob A)) :
  t_alg[projT2 (fobj[Sg_K@{o so}] A)] p = pwfold (fun s => s) p := eq_refl.

Example Sg_K_nu1@{o so} (A : SmgrpSets@{o so}) (x : sg_ob A) :
  t_alg[projT2 (fobj[Sg_K@{o so}] A)] (letter x) = x := eq_refl.

Example Sg_K_nu2@{o so} (A : SmgrpSets@{o so}) (a b : sg_ob A) :
  t_alg[projT2 (fobj[Sg_K@{o so}] A)] (existT _ 1%nat (a, b))
    = sg_mul A a b := eq_refl.

Example Sg_K_nu_succ@{o so} (A : SmgrpSets@{o so}) (m : nat)
  (x y : sg_ob A) (t : Tup@{o} (sg_ob A) m) :
  t_alg[projT2 (fobj[Sg_K@{o so}] A)] (existT _ (S (S m)) (x, (y, t)))
    = t_alg[projT2 (fobj[Sg_K@{o so}] A)]
        (existT _ (S m) (sg_mul A x y, t)) := eq_refl.

Example Sg_K_map@{o so} {A B : SmgrpSets@{o so}}
  (f : A ~{SmgrpSets@{o so}}~> B) :
  t_alg_hom[fmap[Sg_K@{o so}] f] = `1 f := eq_refl.

(* The same as a system: ⟨S, 1, ν2, …⟩ with ν2 the multiplication. / 与系统相同：⟨S, 1, ν2, …⟩，其中 ν2 是乘法。 *)
Example Sg_K_system_nu@{o so} (A : SmgrpSets@{o so}) (n : nat)
  (t : Tup@{o} (sg_ob A) n) :
  nu (ws_nu (fobj[EM_to_WSys@{o so} ◯ Sg_K@{o so}] A)) n t
    = tfold1 (fun s => s) n t := eq_refl.

Example Sg_K_system_nu2@{o so} (A : SmgrpSets@{o so}) (a b : sg_ob A) :
  nu2 (ws_nu (fobj[EM_to_WSys@{o so} ◯ Sg_K@{o so}] A)) a b = sg_mul A a b
  := eq_refl.

(* Proposition 2's functors on data. / 命题2在数据上的函子。 *)
Example WSys_to_EM_alg@{o so} (A : WSys@{o so}) (p : PWord@{o} (ws_set A)) :
  t_alg[projT2 (fobj[WSys_to_EM@{o so}] A)] p = nu_sharp (ws_nu A) p
  := eq_refl.

Example EM_to_WSys_nu@{o so} (x : WordAlg@{o so}) (n : nat)
  (t : Tup@{o} (projT1 x) n) :
  nu (ws_nu (fobj[EM_to_WSys@{o so}] x)) n t
    = t_alg[projT2 x] (existT _ n t) := eq_refl.

(* The round trips on data. / 关于数据的往返旅行。 *)
Example Smgrp_EM_rt_carrier@{o so} (A : SmgrpSets@{o so}) :
  sg_ob (fobj[EM_to_Smgrp@{o so} ◯ Sg_K@{o so}] A) = sg_ob A := eq_refl.

Example Smgrp_EM_rt_mul@{o so} (A : SmgrpSets@{o so}) :
  sg_mul (fobj[EM_to_Smgrp@{o so} ◯ Sg_K@{o so}] A) = sg_mul A := eq_refl.

Example Smgrp_EM_rt_hom@{o so} {A B : SmgrpSets@{o so}}
  (f : A ~{SmgrpSets@{o so}}~> B) :
  sg_fun (fmap[EM_to_Smgrp@{o so} ◯ Sg_K@{o so}] f) = sg_fun f := eq_refl.

Example EM_Smgrp_rt_carrier@{o so} (x : WordAlg@{o so}) :
  projT1 (fobj[Sg_K@{o so} ◯ EM_to_Smgrp@{o so}] x) = projT1 x := eq_refl.

Example EM_Smgrp_rt_alg_hom@{o so} {x y : WordAlg@{o so}}
  (f : x ~{WordAlg@{o so}}~> y) :
  t_alg_hom[fmap[Sg_K@{o so} ◯ EM_to_Smgrp@{o so}] f] = t_alg_hom[f]
  := eq_refl.

Example WSys_rt_set@{o so} (A : WSys@{o so}) :
  ws_set (fobj[EM_to_WSys@{o so} ◯ WSys_to_EM@{o so}] A) = ws_set A
  := eq_refl.

Example WSys_rt_nu@{o so} (A : WSys@{o so}) :
  ws_nu (fobj[EM_to_WSys@{o so} ◯ WSys_to_EM@{o so}] A) = ws_nu A
  := eq_refl.

Example WSys_rt_unit@{o so} (A : WSys@{o so}) :
  ws_unit (fobj[EM_to_WSys@{o so} ◯ WSys_to_EM@{o so}] A) = ws_unit A
  := eq_refl.

Example WSys_rt_hom@{o so} {A B : WSys@{o so}} (f : A ~{WSys@{o so}}~> B) :
  `1 (fmap[EM_to_WSys@{o so} ◯ WSys_to_EM@{o so}] f) = `1 f := eq_refl.

Example EM_WSys_rt_carrier@{o so} (x : WordAlg@{o so}) :
  projT1 (fobj[WSys_to_EM@{o so} ◯ EM_to_WSys@{o so}] x) = projT1 x
  := eq_refl.

Example EM_WSys_rt_alg_hom@{o so} {x y : WordAlg@{o so}}
  (f : x ~{WordAlg@{o so}}~> y) :
  t_alg_hom[fmap[WSys_to_EM@{o so} ◯ EM_to_WSys@{o so}] f] = t_alg_hom[f]
  := eq_refl.

(*
 Every component of the natural isomorphisms is the identity, at a
 variable object, to and from. 

 --------
 自然同构的每个分量都是恒等的，在一个变量对象上，来回都是如此。
*)
Example Smgrp_EM_iso_to_from_component@{o so c} (x : WordAlg@{o so}) :
  (t_alg_hom[to (projT1 (iso_to_from Smgrp_EM_iso@{o so c}) x)],
   t_alg_hom[from (projT1 (iso_to_from Smgrp_EM_iso@{o so c}) x)])
    = (@setoid_morphism_id@{o o o} (projT1 x),
       @setoid_morphism_id@{o o o} (projT1 x)) := eq_refl.

Example Smgrp_EM_iso_from_to_component@{o so c} (A : SmgrpSets@{o so}) :
  (sg_fun (to (projT1 (iso_from_to Smgrp_EM_iso@{o so c}) A)),
   sg_fun (from (projT1 (iso_from_to Smgrp_EM_iso@{o so c}) A)))
    = ((fun a : sg_ob A => a), (fun a : sg_ob A => a)) := eq_refl.

Example Smgrp_EM_counit_component@{o so} (x : WordAlg@{o so}) :
  (t_alg_hom[to (projT1 (@equivalence_counit _ _ _
                           Smgrp_EM_equivalence@{o so}) x)],
   t_alg_hom[from (projT1 (@equivalence_counit _ _ _
                             Smgrp_EM_equivalence@{o so}) x)])
    = (@setoid_morphism_id@{o o o} (projT1 x),
       @setoid_morphism_id@{o o o} (projT1 x)) := eq_refl.

Example Smgrp_EM_unit_component@{o so} (A : SmgrpSets@{o so}) :
  (sg_fun (to (projT1 (@equivalence_unit _ _ _
                         Smgrp_EM_equivalence@{o so}) A)),
   sg_fun (from (projT1 (@equivalence_unit _ _ _
                           Smgrp_EM_equivalence@{o so}) A)))
    = ((fun a : sg_ob A => a), (fun a : sg_ob A => a)) := eq_refl.

Example WSys_EM_iso_to_from_component@{o so c} (x : WordAlg@{o so}) :
  (t_alg_hom[to (projT1 (iso_to_from WSys_EM_iso@{o so c}) x)],
   t_alg_hom[from (projT1 (iso_to_from WSys_EM_iso@{o so c}) x)])
    = (@setoid_morphism_id@{o o o} (projT1 x),
       @setoid_morphism_id@{o o o} (projT1 x)) := eq_refl.

Example WSys_EM_iso_from_to_component@{o so c} (A : WSys@{o so}) :
  (`1 (to (projT1 (iso_from_to WSys_EM_iso@{o so c}) A)),
   `1 (from (projT1 (iso_from_to WSys_EM_iso@{o so c}) A)))
    = (@setoid_morphism_id@{o o o} (ws_set A),
       @setoid_morphism_id@{o o o} (ws_set A)) := eq_refl.
