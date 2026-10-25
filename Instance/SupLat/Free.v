(* * * The free complete semilattice, and the monadicity of [SupLat] / * * 自由完全半格，以及 [SupLat] 的单子性 *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Monad.
Require Import Category.Instance.SupLat.

Generalizable All Variables.

(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Springer GTM 5, 1998, §VI.2, Exercise 1(d), printed p. 142
 (PDF p. 151) — maclane:VI.2:ex1
 Book: Awodey, "Category Theory", Carnegie Mellon pre-print, September
 2005, §10.2, Example 10.5, printed p. 271 (PDF p. 280) —
 awodey:10.2:example5
 Book: Riehl, "Category Theory in Context", 2nd ed., §5.1, Example
 5.1.5(i), printed p. 185 (PDF p. 205) — riehl:5.1:example5
 nLab: https://ncatlab.org/nlab/show/suplattice
 nLab: https://ncatlab.org/nlab/show/monadic+functor

 Awodey introduces the covariant power set monad in Example 10.5 and
 goes on, from the page image: "As we see in these examples, monads can,
 and often do, arise without coming from evident adjunctions", adding
 that "the question, when does an endofunctor T arise from an
 adjunction, has the answer: just if it's the functor part of a monad."
 Riehl lists the same monad under "Monads also arise in nature", after
 the monads she has drawn from adjunctions.  The adjunction behind this
 one is the free complete semilattice.  A subset of X is the formal
 supremum of its elements, so P X ordered by inclusion, with union as
 its supremum, is the free complete join-semilattice on X: a map from X
 into a complete semilattice extends along the singletons to exactly one
 sup-preserving map out of P X.  nLab's suplattice page records the
 consequence that suplattices are monadic over Set through this monad.
 Mac Lane's Exercise VI.2.1(d), that "the category of 𝒫-algebras is the
 category of all (small) complete semi-lattices", is Instance/SupLat.v.
 The exercise does not ask for the adjunction or for monadicity, and
 none of this file is one of #466's boxes: it is built to measure how
 far the monad of the adjunction is the monad of
 Instance/Sets/Powerset/Monad.v, and because the monadicity of the
 forgetful functor then costs one quasi-inverse.

 THE ADJUNCTION.  [FreeSL X] is P X ordered by inclusion, with
 Instance/Sets/Powerset/Monad.v's union [Powerset_union] (#466's own, the
 multiplication of part (a)) as its supremum.  [SL_Free] acts on maps by
 #227's direct image, a sup-preserving map by the naturality of μ
 ([Powerset_union_natural]); [SL_Forget] keeps the carrier.  A
 sup-preserving φ : P X → A restricts along the singletons
 ([SL_restrict]), and a map ψ : X → A extends to S ↦ sup (ψ S)
 ([SL_extend]), which preserves sups by the associativity of sups along
 the union: the action law of Instance/SupLat.v's [SupLat_TAlgebra A],
 reused.  [SL_adj_iso] is the natural bijection and [SL_adj] the
 adjunction, through Theory/Adjunction.v's hom-set constructor
 [Build_Adjunction'], as Instance/Fun/Action/Monad.v builds [MSet_adj]
 (#464).  Instance/SupLat/Examples.v reads the universal property off it
 elementwise ([FreeSL_extend_singleton], [FreeSL_extend_unique]).

 THE MONAD OF THE ADJUNCTION IS NOT LITERALLY [Powerset_Monad].
 [SL_induced] is Monad/Comparison.v's [Adjunction_Induced_Monad SL_adj],
 on the composite [SL_Forget ◯ SL_Free].  It agrees with [Powerset_Monad]
 at [eq_refl] on the object and arrow maps ([SL_induced_obj],
 [SL_induced_map]) and on the unit as a function ([SL_induced_ret_fun]).
 Its join is U ε F, which is ⋃ ∘ P id, the union of the direct image of
 SS under the identity ([SL_induced_join_fun], at [eq_refl]), so it
 agrees with ⋃ up to ≈ only ([SL_induced_join_equiv]); so do the unit as
 a setoid map ([SL_induced_ret_equiv]) and the functor
 ([SL_induced_functor_equiv], a natural isomorphism whose component at
 every X is the identity isomorphism, [SL_induced_functor_component] at
 [eq_refl]).  Refused at [eq_refl], each pinned in
 Test/ProbeSupLat466.v: the whole unit (F1), the join as a function and
 at one set of subsets (F2, F2b), the composite functor as
 [Powerset_Prop] (F3), and so [Powerset_Monad] as a monad on the
 composite at all (F4, a typing refusal).  The QA correction of #466
 (reuse #227's functor and unit) therefore rules out defining
 [Powerset_Monad] as the induced monad, and Instance/Sets/Powerset/
 Monad.v builds it with [Build_Monad].
 CORRECTION (#1347): the whole unit, F1, now holds at [eq_refl], since
 Instance/Sets.v gives its identity's and composite's properness fields
 as terms; it is a control of the probe, and the unit as a setoid map
 agrees with [Powerset_Monad]'s at [eq_refl], not only up to ≈ as
 [SL_induced_ret_equiv] states.  F2 to F4 are still refused.

 WHICH REFUSALS ARE OPACITY, MEASURED.  F2 and F2b compare ⋃ (P id SS)
 with ⋃ SS at a variable SS, and P id SS is a squashed existential, not
 SS.  F3 compares the proof fields of Theory/Functor.v's [Compose], its
 Program obligations, with [Powerset_Prop]'s own lemmas.  All three,
 and F4, stand in the probe's flip, a copy of its one-hundred-module
 dependency closure with every [Qed] turned into [Defined] but those the
 probe names (Instance/Sets.v's [setoid_morphism_compose_respects] among
 them, as in Instance/SupLat.v) and [Transparent Obligations] set, and
 again in the copy described next, where no [Qed] is changed and
 Instance/Sets.v's two properness fields are written as terms.  F1 is
 different.
 The induced unit IS setoid_morphism_compose setoid_morphism_id applied
 to #227's singleton map (a control at [eq_refl] in the probe), and that
 composite's properness proof is assembled by instance resolution from
 Corelib's opaque [Reflexive_partial_app_morphism] and
 [proper_proper_proxy] (in Instance/Sets.v's [setoid_morphism_compose])
 and [subrelation_id_proper] applied to the equally opaque
 [subrelation_refl] (in its [setoid_morphism_id]).  In a copy of the
 closure with no [Qed] changed, in which only those two fields were
 written as the terms
 fun a b H => proper_morphism g _ _ (proper_morphism f a b H) and
 fun _ _ H => H, F1 holds at [eq_refl] and F2 to F4 are still refused;
 with the compose field alone rewritten, F1 is still refused.  So F1 is
 opacity outside the tree, of the kind of #464's N3 (STDLIB OPACITY in
 the probe), and the other four are not opacity.
 CORRECTION (#1347): that copy's change is now the tree's, and F1 holds
 at [eq_refl]; the attribution was right, and F2 to F4 are still
 refused.

 MONADICITY.  [SL_induced_repack] reads an algebra of the induced monad
 as an algebra of [Powerset_Monad], its structure map and unit law
 unchanged and its action law proved again, since the two joins differ.
 [EM_induced_to_SupLat] is then Instance/SupLat.v's part (b) on those
 algebras.  It is a quasi-inverse of Monad/Comparison.v's
 [EM_Comparison SL_adj] with identity components both ways
 ([SL_comparison_counit_iso], [SL_comparison_unit_iso]), whence
 [SL_comparison_equivalence] and [SL_Forget_Monadic : Monadic SL_Forget].
 This is the direct route of #464's [MSet_Forget_Monadic_direct]; Beck's
 theorem is not used.  [Monadic] asks for an equivalence of categories,
 the reading that Instance/Fun/Action/Monad.v's header sets beside Mac
 Lane's strict one, and Instance/SupLat.v's header explains why an
 identity of categories is not formable here either.

 STRENGTHS.  By [eq_refl]: [SL_induced_obj], [SL_induced_map],
 [SL_induced_ret_fun], [SL_induced_join_fun] and
 [SL_induced_functor_component]; every component of both
 natural isomorphisms of the comparison, to and from, is the identity
 map at a variable object ([SL_comparison_counit_component],
 [SL_comparison_unit_component] and their [_from] twins); in the probe,
 also the object and arrow maps of the composite as functions, and the
 unit as the composite of the identity with the singleton map.  At ≈
 only: the join as a setoid map and the functor (F2 to F4), and the two
 round trips through the comparison, as natural isomorphisms (both
 composites against the identity functors, F5 and F5b, and both
 whole-object round trips, F6 and F6b, are refused at [eq_refl], standing
 in the same copies as F2 to F4).  At ≈ here, and at [eq_refl] once
 Instance/Sets.v's two properness fields are written as terms: the unit
 as a setoid map (F1).
 CORRECTION (#1347): they are written so now, and the unit as a setoid
 map holds at [eq_refl] (F1, a control of the probe).

 UNIVERSES, read off [About].  [FreeSL] binds [@{o}] with [Set < o]; every
 other constant binds [@{o so}].  [SL_Free], [SL_Forget], [SL_extend],
 [SL_restrict], [SL_adj_iso], the two map readbacks and
 [SL_induced_functor_equiv] have the block of [SupLat@{o so}]: [Set < o],
 [o < so] (first carried by Instance/Sets.v's [Sets]) and the caps
 compose and ID of Instance/Sets.v's [setoid_morphism_compose] and
 [setoid_morphism_id]; [SL_induced_functor_component] adds to that block
 o <= Projections.u0, o <= Projections.u1, so <= Projections.u0 and
 so <= Projections.u1, from the [projT1] of the sigma type that ≈ of
 functors is.  [SL_adj] and every constant that names it add
 o <= Logic_lemmas.equality.u0, prod_rect and projections (the pair
 projections), and so <= projections.u0 and projections.u1, first
 carried by Theory/Adjunction.v's [Build_Adjunction'] at its hom level o
 and its last level, so; those that name [EilenbergMoore] add
 o <= Projections.u1 and so <= Projections.u0 (the sigma projections),
 as in Instance/SupLat.v, and the four component readbacks also
 o <= Projections.u0 and so <= Projections.u1, from the [projT1] of a
 natural isomorphism in their statements.  The adjunction is
 [Adjunction@{so o o so o o o o so o so}] and the witness
 [Monadic@{so so so so so o so so}], the pins of #464.  There is no
 equation and no strict bound beyond [Set < o] and [o < so].

 NOT DELIVERED.  Beck's route to monadicity (Monad/Monadicity/Beck.v's
 [beck_monadicity]) is not taken.  No functor between the
 Eilenberg–Moore categories of [SL_induced] and of [Powerset_Monad] is
 built: the tree has no morphisms of monads, and [SL_induced_repack] is
 the object part of one.  The Kleisli category of the monad (sets and
 relations) is not identified (Instance/Sets/Powerset/Monad.v says what
 Instance/Concrete.v's [Rel_Powerset] is, and is not), and the right
 adjoint of a sup-preserving map and the tensor product of suplattices
 are not built.

 CORRECTION (#468).  The tree now has morphisms of monads:
 Monad/Morphism.v's [MonadHom] and the category [Monads C] of monads on C,
 and Monad/Morphism/Algebra.v's θ* ([mh_EM]).  The functor named above is
 built from them, with this file unchanged, by
 Instance/SupLat/Free/Morphism.v: [SL_EM_theta], the θ* of the morphism of
 monads [SL_theta] from [Powerset_Monad] to [SL_induced], which agrees
 with [SL_induced_repack] on carriers and on structure maps as functions
 at [eq_refl]; [SL_theta_iso] makes the two monads isomorphic in [Monads
 Sets].  [SL_induced_repack] and [EM_induced_to_SupLat] are not rewired
 onto θ*. 

 --------
 书籍：Mac Lane，《为工作数学家而设的范畴论》，第二版，Springer GTM 5，1998年，第VI.2节，练习1(d)，印刷页142（PDF第151页）—— maclane:VI.2:ex1
 书籍：Awodey，《范畴论》，卡内基梅隆预印本，2005年9月，第10.2节，例10.5，印刷页271（PDF第280页）—— awodey:10.2:example5
 书籍：Riehl，《语境中的范畴论》，第二版，第5.1节，例5.1.5(i)，印刷页185（PDF第205页）—— riehl:5.1:example5
 nLab：https://ncatlab.org/nlab/show/suplattice
 nLab：https://ncatlab.org/nlab/show/monadic+functorAwodey 在例 10.5 中介绍了协变幂集单子，并继续在页面图像中提到：“正如我们在这些例子中看到的，单子可以，而且通常确实会出现，而不来源于明显的伴随”，并补充说“问题是，一个自函子 T 何时来源于伴随，其答案是：当且仅当它是一个单子的函子部分。”Riehl 在“单子也自然产生”下列出了同一个单子，在她从伴随中引出的单子之后。这个单子背后的伴随是自由完全半格。X 的一个子集是其元素的形式上确界，因此以包含关系排序的 P X，其并集作为其确界，是 X 上的自由完全并半格：从 X 到一个完全半格的映射沿单元素集扩展，正好得到一个唯一的保持确界的 P X 映射。nLab 的上格页面记录了通过这个单子，上格是 Set 上的幂等单子。Mac Lane 的练习 VI.2.1(d)，即“𝒫-代数的范畴是所有（小）完全半格的范畴”，在 Instance/SupLat.v 中。该练习没有要求建立伴随关系或单子性，并且此文件的内容都不属于 #466 的框：它是为了测量伴随关系的单子在多大程度上是 Instance/Sets/Powerset/Monad.v 的单子，并且因为忘记函子的单子性会花费一个准逆元。附加。[FreeSL X] 是按包含顺序排列的 P X，其上确立了 [Powerset_union] 作为上确界，这是 Instance/Sets/Powerset/Monad.v 的并集（#466 自身，部分 (a) 的乘法）。[SL_Free] 通过 #227 的直接像作用于映射，根据 μ 的自然性 ([Powerset_union_natural]) 是保持上确界的映射；[SL_Forget] 保持载体。保持上确界的 φ : P X → A 沿单元素 ([SL_restrict]) 限制，而映射 ψ : X → A 扩展为 S ↦ sup (ψ S) ([SL_extend])，它通过沿并集的上确界的结合性保持上确界：这是 Instance/SupLat.v 中 [SupLat_TAlgebra A] 的作用律，被重复使用。[SL_adj_iso] 是自然双射，[SL_adj] 是伴随，通过 Theory/Adjunction.v 的同态集构造器 [Build_Adjunction']，而 Instance/Fun/Action/Monad.v 构建了 [MSet_adj] (#464)。Instance/SupLat/Examples.v 从中逐元素读取其泛性质 ([FreeSL_extend_singleton], [FreeSL_extend_unique])。伴随的幺半群并不字面上等于 [Powerset_Monad]。[SL_induced] 是 Monad/Comparison.v 中的 [Adjunction_Induced_Monad SL_adj]，作用于复合 [SL_Forget ◯ SL_Free]。它在对象和箭头映射（[SL_induced_obj]、[SL_induced_map]）以及作为函数的单位（[SL_induced_ret_fun]）上与 [Powerset_Monad] 在 [eq_refl] 处一致。它的联合是 U ε F，即 ⋃ ∘ P id，是 SS 在恒等映射下的直像的并集（[SL_induced_join_fun]，在 [eq_refl] 处），因此它仅在 ≈ 下与 ⋃ 一致（[SL_induced_join_equiv]）；单位作为集合等价映射（[SL_induced_ret_equiv]）以及函子（[SL_induced_functor_equiv]，一个自然同构，其在每个 X 的分量都是恒等同构，[SL_induced_functor_component] 在 [eq_refl] 处）也是如此。在 [eq_refl] 被拒绝，每个在 Test/ProbeSupLat466.v 中固定：整个范畴单位 (F1)、作为函数的连接以及在一组子集上的连接 (F2, F2b)、复合函子作为 [Powerset_Prop] (F3)，以及 [Powerset_Monad] 作为复合上的单子 (F4，一个类型拒绝)。因此，#466 的 QA 修正（重用 #227 的函子和单位）排除了将 [Powerset_Monad] 定义为诱导单子，而 Instance/Sets/Powerset/Monad.v 使用 [Build_Monad] 构建它。修正 (#1347)：整个单位 F1 现在在 [eq_refl] 上成立，因为 Instance/Sets.v 给出了其恒等和复合的正确性字段作为项；它是探针的控制，并且作为集合映射的单位在 [eq_refl] 上与 [Powerset_Monad] 一致，而不仅仅是如 [SL_induced_ret_equiv] 所述的约等。F2 到 F4 仍然被拒绝。哪些拒绝是测量的不透明性。F2 和 F2b 比较 ⋃ (P id SS) 与一个可变 SS 上的 ⋃ SS，而 P id SS 是一个压缩存在量化，而不是 SS。F3 比较 Theory/Functor.v 的 [Compose] 的证明字段，其程序义务，与 [Powerset_Prop] 自身的引理。三者，以及 F4，都位于探针的翻转中，这是它的一百模块依赖闭包的副本，每个 [Qed] 都被转换为 [Defined]，但探针命名的那部分除外（例如 Instance/Sets.v 的 [setoid_morphism_compose_respects]，以及 Instance/SupLat.v），以及 [Transparent Obligations] 集合，再次在下一步描述的副本中，其中没有 [Qed] 被更改，并且 Instance/Sets.v 的两个正确性字段以项的形式书写。F1 是不同的。诱导的单元是 setoid_morphism_compose setoid_morphism_id 应用于 #227 的单元素映射（探针中的 [eq_refl] 控制），该复合的正确性证明通过实例解析从 Corelib 的不透明 [Reflexive_partial_app_morphism] 和 [proper_proper_proxy]（在 Instance/Sets.v 的 [setoid_morphism_compose] 中）以及 [subrelation_id_proper] 应用于同样不透明的 [subrelation_refl]（在其 [setoid_morphism_id] 中）组装而成。在没有更改 [Qed] 的闭包副本中，只有这两个字段被写为术语 fun a b H => proper_morphism g _ _ (proper_morphism f a b H) 和 fun _ _ H => H，在 [eq_refl] 上 F1 成立，而 F2 到 F4 仍被拒绝；仅重写 compose 字段时，F1 仍被拒绝。因此 F1 是树外的不透明性，属于 #464 的 N3 类型（探针中的 STDLIB 不透明性），而其他四个不是不透明性。更正 (#1347)：该副本的更改现在属于树，并且 F1 在 [eq_refl] 处成立；归属是正确的，F2 到 F4 仍然被拒绝。单子性。[SL_induced_repack] 将一个诱导单子的代数作为 [Powerset_Monad] 的代数来读取，其结构映射和单位律保持不变，而其作用律则再次被证明，因为两个结合操作不同。[EM_induced_to_SupLat] 然后是 Instance/SupLat.v 在这些代数上的部分 (b)。它是 Monad/Comparison.v 的 [EM_Comparison SL_adj] 的准逆，双向都有恒等分量 ([SL_comparison_counit_iso], [SL_comparison_unit_iso])，因此得到 [SL_comparison_equivalence] 和 [SL_Forget_Monadic : Monadic SL_Forget]。这是 #464 的 [MSet_Forget_Monadic_direct] 的直接路线；并未使用 Beck 定理。[Monadic] 要求给出范畴的等价，这与 Instance/Fun/Action/Monad.v 的标题在 Mac Lane 的严格定义旁边所设置的读取相一致，Instance/SupLat.v 的标题解释了为什么此处也不能形成范畴的恒等式。优势。作者 [eq_refl]：[SL_induced_obj]、[SL_induced_map]、[SL_induced_ret_fun]、[SL_induced_join_fun] 和 [SL_induced_functor_component]；比较的两个自然同构的每个组成部分，从和到，都是变量对象（[SL_comparison_counit_component]、[SL_comparison_unit_component] 及其 [_from] 双胞胎）的恒等映射；在探针中，复合的对象和箭头映射也作为函数，以及单位作为恒等映射与单例映射的复合。在 ≈ 上：联结作为集合映射和函子（F2 到 F4），以及通过比较的两次往返，作为自然同构（两个复合针对恒等函子 F5 和 F5b，以及整个对象的两次往返 F6 和 F6b，在 [eq_refl] 上被拒绝，与 F2 到 F4 的副本相同）。在≈这里，以及在[eq_refl]一次
 Instance/Sets.v的两个正确性字段被写为项：单位
 作为集合等价映射（F1）。更正（#1347）：它们现在被这样写，并且单位作为集合等价映射在[eq_refl]上成立（F1，对探针的控制）。UNIVERSES，读取 [About]。[FreeSL] 通过 [Set < o] 绑定 [@{o}]；其他常量绑定 [@{o so}]。[SL_Free]、[SL_Forget]、[SL_extend]、[SL_restrict]、[SL_adj_iso]、两个映射回读和 [SL_induced_functor_equiv] 拥有 [SupLat@{o so}] 的块：[Set < o]、[o < so]（最初由 Instance/Sets.v 的 [Sets] 承载）以及 Instance/Sets.v 的 [setoid_morphism_compose] 和 [setoid_morphism_id] 的组合和 ID；[SL_induced_functor_component] 向该块添加 o <= Projections.u0、o <= Projections.u1、so <= Projections.u0 和 so <= Projections.u1，这来自 sigma 类型的 [projT1]，其近似等于函子。[SL_adj] 以及命名它的每个常数添加 o <= Logic_lemmas.equality.u0、prod_rect 和 projections（对的投影），并且因此 <= projections.u0 和 projections.u1，由 Theory/Adjunction.v 的 [Build_Adjunction'] 在其同态层 o 和其最后一层 carried，如此；那些命名 [EilenbergMoore] 的添加 o <= Projections.u1 并且因此 <= Projections.u0（sigma 投影），如在 Instance/SupLat.v 中，并且四个组件回读也 o <= Projections.u0 并且因此 <= Projections.u1，从他们陈述中的自然同构的 [projT1] 得到。该伴随是 [Adjunction@{so o o so o o o o so o so}] 且见证是 [Monadic@{so so so so so o so so}]，#464 的固定。没有方程且除了 [Set < o] 和 [o < so] 之外没有严格的界限。未交付。Beck 通向单子性（Monad/Monadicity/Beck.v 的 [beck_monadicity]）未被采用。在 [SL_induced] 和 [Powerset_Monad] 的 Eilenberg–Moore 范畴之间没有构建函子：这棵树没有单子的态射，而 [SL_induced_repack] 是其中一个的对象部分。未识别单子的 Kleisli 范畴（sets 和 relations）（Instance/Sets/Powerset/Monad.v 说明了 Instance/Concrete.v 的 [Rel_Powerset] 是什么，以及不是），并且未构建保上确界映射的右伴随函数及上格的张量积。更正 (#468)。该树现在具有单子态射：
 Monad/Morphism.v 的 [MonadHom] 以及 C 上单子的范畴 [Monads C]，
 以及 Monad/Morphism/Algebra.v 的 θ* ([mh_EM])。上述命名的函子是从它们构建的，本文件保持不变，通过
 Instance/SupLat/Free/Morphism.v: [SL_EM_theta]，即从 [Powerset_Monad] 到 [SL_induced] 的单子态射 [SL_theta] 的 θ*，它在载体和结构映射上与 [SL_induced_repack] 作为函数在 [eq_refl] 上一致；[SL_theta_iso] 使这两个单子在 [Monads Sets] 中同构。[SL_induced_repack] 和 [EM_induced_to_SupLat] 没有重新连接到 θ*。
*)

(* ------------------------------------------------------------------------ *)
(* * ** The free complete semilattice P X / * ** 自由完备半格 P X *)

(* P X ordered by inclusion, with sup = union. / 按包含顺序排列的 P X，sup = 并集。 *)
Definition FreeSL@{o} (X : SetoidObject@{o o}) : SupLatObject@{o}.
Proof.
  unshelve refine
    (@Build_SupLatObject@{o} (Powerset_Prop_obj@{o} X)
       (λ S T, ∀ z, S z → T z) _ _ _ _ (@Powerset_union@{o} X) _ _).
  - intros S z Hz; exact Hz.
  - intros S T U H1 H2 z Hz; exact (H2 z (H1 z Hz)).
  - intros S S' T T' ES ET H z Hz.
    exact (proj1 (ET z) (H z (proj2 (ES z) Hz))).
  - intros S T H1 H2 z; split; [ apply H1 | apply H2 ].
  - intros SS S HS z Hz. exists S; split; assumption.
  - intros SS T H z [S [HS Hz]]. exact (H S HS z Hz).
Defined.

(*
 F : Sets ⟶ SupLat.  Its action on maps is #227's direct image, and a
 direct image preserves unions by the naturality of μ. 

 --------
 F : 集合 ⟶ 上完全格。它在映射上的作用是 #227 的直接像，而由于 μ 的自然性，直接像保留并集。
*)
Definition SL_Free@{o so} : Sets@{o so} ⟶ SupLat@{o so}.
Proof.
  unshelve refine
    (@Build_Functor Sets@{o so} SupLat@{o so} FreeSL@{o}
       (fun X Y f => @Build_SupLatHom@{o} (FreeSL@{o} X) (FreeSL@{o} Y)
                       (fmap[Powerset_Prop@{o so}] f) _)
       _ _ _).
  - intro SS. symmetry. exact (Powerset_union_natural@{o} f SS).
  - intros X Y f g H.
    exact (@fmap_respects _ _ Powerset_Prop@{o so} X Y f g H).
  - intros X. exact (@fmap_id _ _ Powerset_Prop@{o so} X).
  - intros X Y Z f g. exact (@fmap_comp _ _ Powerset_Prop@{o so} X Y Z f g).
Defined.

(* U : SupLat ⟶ Sets forgets the order and the sup. / U : SupLat ⟶ Sets 忘记顺序和上确界。 *)
Definition SL_Forget@{o so} : SupLat@{o so} ⟶ Sets@{o so}.
Proof.
  unshelve refine
    (@Build_Functor SupLat@{o so} Sets@{o so} sl_set
       (fun A B f => slh_map f) _ _ _).
  - intros A B f g H. exact H.
  - intros A a. reflexivity.
  - intros A B C f g a. reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** The free/forgetful adjunction / ** 自由/遗忘的伴随 *)

(* A map ψ : X → U A extends to the sup-preserving S ↦ sup (ψ S). / 一个映射 ψ : X → U A 扩展为保持上确界的映射 S ↦ sup (ψ S)。 *)
Definition SL_extend@{o so} {X : SetoidObject@{o o}} {A : SupLatObject@{o}}
  (ψ : X ~{Sets@{o so}}~> fobj[SL_Forget@{o so}] A) :
  fobj[SL_Free@{o so}] X ~{SupLat@{o so}}~> A.
Proof.
  unshelve refine
    (@Build_SupLatHom@{o} (FreeSL@{o} X) A
       (@setoid_morphism_compose@{o o o} _ _ _
          (sl_sup A) (Powerset_Prop_map@{o} ψ)) _).
  intro SS.
  transitivity (sl_sup A (Powerset_union_pred@{o}
                  (Powerset_Prop_image@{o} (Powerset_Prop_map@{o} ψ) SS))).
  { apply (proper_morphism (sl_sup A)). symmetry.
    exact (Powerset_union_natural@{o} ψ SS). }
  transitivity (sl_sup A (Powerset_Prop_image@{o} (sl_sup A)
                  (Powerset_Prop_image@{o} (Powerset_Prop_map@{o} ψ) SS))).
  { symmetry.
    exact (@t_action _ _ _ _ (SupLat_TAlgebra@{o so} A)
             (Powerset_Prop_image@{o} (Powerset_Prop_map@{o} ψ) SS)). }
  apply (proper_morphism (sl_sup A)). symmetry.
  exact (@Powerset_Prop_map_comp@{o} _ _ _
           (sl_sup A) (Powerset_Prop_map@{o} ψ) SS).
Defined.

(* A sup-preserving φ : F X → A restricts to x ↦ φ {x}. / 一个保持上确界的 φ : F X → A 限制为 x ↦ φ {x}。 *)
Definition SL_restrict@{o so} {X : SetoidObject@{o o}} {A : SupLatObject@{o}}
  (φ : fobj[SL_Free@{o so}] X ~{SupLat@{o so}}~> A) :
  X ~{Sets@{o so}}~> fobj[SL_Forget@{o so}] A :=
  @setoid_morphism_compose@{o o o} _ _ _
    (slh_map φ) (@Powerset_Prop_singleton_map@{o} X).

Definition SL_adj_iso@{o so} (X : SetoidObject@{o o}) (A : SupLatObject@{o}) :
  @Isomorphism Sets@{o so}
    (@Build_SetoidObject
       (@hom SupLat@{o so} (fobj[SL_Free@{o so}] X) A)
       (@homset SupLat@{o so} (fobj[SL_Free@{o so}] X) A))
    (@Build_SetoidObject
       (@hom Sets@{o so} X (fobj[SL_Forget@{o so}] A))
       (@homset Sets@{o so} X (fobj[SL_Forget@{o so}] A))).
Proof.
  unshelve refine
    (@Build_Isomorphism Sets@{o so}
       (@Build_SetoidObject
          (@hom SupLat@{o so} (fobj[SL_Free@{o so}] X) A)
          (@homset SupLat@{o so} (fobj[SL_Free@{o so}] X) A))
       (@Build_SetoidObject
          (@hom Sets@{o so} X (fobj[SL_Forget@{o so}] A))
          (@homset Sets@{o so} X (fobj[SL_Forget@{o so}] A)))
       (@Build_SetoidMorphism
          (@hom SupLat@{o so} (fobj[SL_Free@{o so}] X) A)
          (@homset SupLat@{o so} (fobj[SL_Free@{o so}] X) A)
          (@hom Sets@{o so} X (fobj[SL_Forget@{o so}] A))
          (@homset Sets@{o so} X (fobj[SL_Forget@{o so}] A))
          (fun φ => @SL_restrict@{o so} X A φ) _)
       (@Build_SetoidMorphism
          (@hom Sets@{o so} X (fobj[SL_Forget@{o so}] A))
          (@homset Sets@{o so} X (fobj[SL_Forget@{o so}] A))
          (@hom SupLat@{o so} (fobj[SL_Free@{o so}] X) A)
          (@homset SupLat@{o so} (fobj[SL_Free@{o so}] X) A)
          (fun ψ => @SL_extend@{o so} X A ψ) _) _ _).
  - intros φ φ' H x. exact (H _).
  - intros ψ ψ' H S. apply (proper_morphism (sl_sup A)).
    exact (@Powerset_Prop_map_respects@{o} _ _ ψ ψ' H S).
  - intros ψ x.
    transitivity (sl_sup A (Powerset_Prop_singleton_pred@{o} (ψ x))).
    + apply (proper_morphism (sl_sup A)).
      exact (@Powerset_Prop_image_singleton@{o} _ _ ψ x).
    + exact (@t_id _ _ _ _ (SupLat_TAlgebra@{o so} A) (ψ x)).
  - intros φ S.
    transitivity (slh_map φ (Powerset_union_pred@{o}
                    (Powerset_Prop_image@{o}
                       (@Powerset_Prop_singleton_map@{o} X) S))).
    + transitivity (sl_sup A (Powerset_Prop_image@{o} (slh_map φ)
                      (Powerset_Prop_image@{o}
                         (@Powerset_Prop_singleton_map@{o} X) S))).
      * apply (proper_morphism (sl_sup A)).
        exact (@Powerset_Prop_map_comp@{o} _ _ _ (slh_map φ)
                 (@Powerset_Prop_singleton_map@{o} X) S).
      * symmetry. exact (slh_sup φ _).
    + apply (proper_morphism (slh_map φ)).
      exact (Powerset_union_image_singleton@{o} S).
Defined.

(* The free complete semilattice: F ⊣ U, in the hom-set form. / 自由完全半格：F ⊣ U，以同态集形式表示。 *)
Definition SL_adj@{o so} :
  @Adjunction@{so o o so o o o o so o so} SupLat@{o so} Sets@{o so}
    SL_Free@{o so} SL_Forget@{o so}.
Proof.
  unshelve refine
    (@Build_Adjunction' SupLat@{o so} Sets@{o so}
       SL_Free@{o so} SL_Forget@{o so}
       (fun X A => SL_adj_iso@{o so} X A) _ _).
  - intros X Y A φ g x.
    apply (proper_morphism (slh_map φ)).
    exact (@Powerset_Prop_image_singleton@{o} _ _ g x).
  - intros X A B f φ x. reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(* * ** The monad of the adjunction, against [Powerset_Monad] / * ** 关于 [Powerset_Monad] 的伴随单子 *)

Definition SL_induced@{o so} :
  @Monad Sets@{o so} (SL_Forget@{o so} ◯ SL_Free@{o so}) :=
  Adjunction_Induced_Monad SL_adj@{o so}.

Example SL_induced_obj@{o so} (X : SetoidObject@{o o}) :
  fobj[SL_Forget@{o so} ◯ SL_Free@{o so}] X = fobj[Powerset_Prop@{o so}] X
  := eq_refl.

Example SL_induced_map@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) :
  fmap[SL_Forget@{o so} ◯ SL_Free@{o so}] f = fmap[Powerset_Prop@{o so}] f
  := eq_refl.

Example SL_induced_ret_fun@{o so} (X : SetoidObject@{o o}) :
  (fun x => @ret _ _ SL_induced@{o so} X x)
    = (fun x => @ret _ _ Powerset_Monad@{o so} X x) := eq_refl.

(*
 The induced join is U ε F, that is ⋃ ∘ P id: the union of the direct
 image of SS under the identity, not the union of SS. 

 --------
 诱导并集是 U ε F，即 ⋃ ∘ P id：是 SS 在恒等映射下的直接像的并集，而不是 SS 的并集。
*)
Example SL_induced_join_fun@{o so} (X : SetoidObject@{o o}) :
  (fun SS => @join _ _ SL_induced@{o so} X SS)
    = (fun SS => Powerset_union_pred@{o}
                   (Powerset_Prop_image@{o}
                      (@setoid_morphism_id@{o o o} (Powerset_Prop_obj@{o} X))
                      SS)) := eq_refl.

Lemma SL_induced_ret_equiv@{o so} (X : SetoidObject@{o o}) :
  @ret _ _ SL_induced@{o so} X ≈ @ret _ _ Powerset_Monad@{o so} X.
Proof. intros x. reflexivity. Qed.

Lemma SL_induced_join_equiv@{o so} (X : SetoidObject@{o o}) :
  @join _ _ SL_induced@{o so} X ≈ @join _ _ Powerset_Monad@{o so} X.
Proof.
  intros SS.
  exact (@Powerset_union_respects@{o} X _ SS
           (@Powerset_Prop_map_id@{o} (Powerset_Prop_obj@{o} X) SS)).
Qed.

(* Transparent, so that its components read back below. / 透明的，以便其组件可以在下面读回。 *)
Definition SL_induced_functor_equiv@{o so} :
  SL_Forget@{o so} ◯ SL_Free@{o so} ≈ Powerset_Prop@{o so}.
Proof.
  exists (fun X => @iso_id Sets@{o so} (fobj[Powerset_Prop@{o so}] X)).
  intros X Y f S. reflexivity.
Defined.

(* Its component at X is the identity isomorphism. / 它在 X 处的分量是恒等同构。 *)
Example SL_induced_functor_component@{o so} (X : SetoidObject@{o o}) :
  projT1 SL_induced_functor_equiv@{o so} X
    = @iso_id Sets@{o so} (fobj[Powerset_Prop@{o so}] X) := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** Monadicity of the forgetful functor / * ** 忘记函子的单子性 *)

(*
 An algebra of the induced monad is, with its data unchanged, an algebra
 of [Powerset_Monad]: only the action law is proved again, since the
 induced join is ⋃ ∘ P id rather than ⋃. 

 --------
 诱导幺半群的代数，在其数据不变的情况下，是 [Powerset_Monad] 的代数：只需再次证明作用律，因为诱导的合并是 ⋃ ∘ P id 而不是 ⋃。
*)
Definition SL_induced_repack@{o so} {X : SetoidObject@{o o}}
  (β : @TAlgebra Sets@{o so} (SL_Forget@{o so} ◯ SL_Free@{o so})
         SL_induced@{o so} X) :
  @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X.
Proof.
  unshelve refine
    (@Build_TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so}
       X (@t_alg _ _ _ _ β) (@t_id _ _ _ _ β) _).
  intro SS.
  transitivity (@t_alg _ _ _ _ β (@join _ _ SL_induced@{o so} X SS)).
  - exact (@t_action _ _ _ _ β SS).
  - apply (proper_morphism (@t_alg _ _ _ _ β)).
    exact (@Powerset_union_respects@{o} X _ SS
             (@Powerset_Prop_map_id@{o} (Powerset_Prop_obj@{o} X) SS)).
Defined.

Definition EM_induced_to_SupLat@{o so} :
  @EilenbergMoore@{so so so o} Sets@{o so}
    (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}
    ⟶ SupLat@{o so}.
Proof.
  unshelve refine
    (@Build_Functor
       (@EilenbergMoore@{so so so o} Sets@{o so}
          (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so})
       SupLat@{o so}
       (fun x => TAlgebra_SupLat@{o so} (SL_induced_repack@{o so} (projT2 x)))
       (fun x y f =>
          @Build_SupLatHom@{o}
            (TAlgebra_SupLat@{o so} (SL_induced_repack@{o so} (projT2 x)))
            (TAlgebra_SupLat@{o so} (SL_induced_repack@{o so} (projT2 y)))
            (@t_alg_hom _ _ _ _ _ _ _ f)
            (fun S => @t_alg_hom_commutes _ _ _ _ _ _ _ f S))
       _ _ _).
  - intros x y f g H a. exact (H a).
  - intros x a. reflexivity.
  - intros x y z f g a. reflexivity.
Defined.

(*
 The algebra round trip through the comparison, with the identity as its
 component. 

 --------
 通过比较进行代数往返，恒等式作为其组成部分。
*)
Definition SL_comparison_counit_iso@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  @Isomorphism
    (@EilenbergMoore@{so so so o} Sets@{o so}
       (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so})
    (fobj[EM_Comparison SL_adj@{o so} ◯ EM_induced_to_SupLat@{o so}] x) x.
Proof.
  unshelve refine
    (@Build_Isomorphism
       (@EilenbergMoore@{so so so o} Sets@{o so}
          (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so})
       (fobj[EM_Comparison SL_adj@{o so} ◯ EM_induced_to_SupLat@{o so}] x) x
       (@Build_TAlgebraHom Sets@{o so} (SL_Forget@{o so} ◯ SL_Free@{o so})
          SL_induced@{o so} (projT1 x) (projT1 x)
          (projT2 (fobj[EM_Comparison SL_adj@{o so}
                        ◯ EM_induced_to_SupLat@{o so}] x))
          (projT2 x)
          (@setoid_morphism_id@{o o o} (projT1 x)) _)
       (@Build_TAlgebraHom Sets@{o so} (SL_Forget@{o so} ◯ SL_Free@{o so})
          SL_induced@{o so} (projT1 x) (projT1 x)
          (projT2 x)
          (projT2 (fobj[EM_Comparison SL_adj@{o so}
                        ◯ EM_induced_to_SupLat@{o so}] x))
          (@setoid_morphism_id@{o o o} (projT1 x)) _) _ _).
  - intro S. reflexivity.
  - intro S. apply (proper_morphism (@t_alg _ _ _ _ (projT2 x))).
    symmetry.
    transitivity (Powerset_Prop_map@{o}
                    (@setoid_morphism_id@{o o o} (projT1 x)) S).
    + exact (@Powerset_Prop_map_id@{o} (projT1 x) _).
    + exact (@Powerset_Prop_map_id@{o} (projT1 x) S).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(*
 The semilattice round trip through the comparison, with the identity as
 its component. 

 --------
 半格通过比较进行回程，其分量为恒等映射。
*)
Definition SL_comparison_unit_iso@{o so} (A : SupLatObject@{o}) :
  @Isomorphism SupLat@{o so}
    (fobj[EM_induced_to_SupLat@{o so} ◯ EM_Comparison SL_adj@{o so}] A) A.
Proof.
  unshelve refine
    (@Build_Isomorphism SupLat@{o so}
       (fobj[EM_induced_to_SupLat@{o so} ◯ EM_Comparison SL_adj@{o so}] A) A
       (@Build_SupLatHom@{o}
          (fobj[EM_induced_to_SupLat@{o so} ◯ EM_Comparison SL_adj@{o so}] A)
          A (@setoid_morphism_id@{o o o} (sl_set A)) _)
       (@Build_SupLatHom@{o} A
          (fobj[EM_induced_to_SupLat@{o so} ◯ EM_Comparison SL_adj@{o so}] A)
          (@setoid_morphism_id@{o o o} (sl_set A)) _) _ _).
  - intro S. reflexivity.
  - intro S. apply (proper_morphism (sl_sup A)). symmetry.
    transitivity (Powerset_Prop_map@{o}
                    (@setoid_morphism_id@{o o o} (sl_set A)) S).
    + exact (@Powerset_Prop_map_id@{o} (sl_set A) _).
    + exact (@Powerset_Prop_map_id@{o} (sl_set A) S).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(*
 The comparison functor is an equivalence, with identity components both
 ways. 

 --------
 比较函子是一个等价，两边的恒等分量都是相同的。
*)
Definition SL_comparison_equivalence@{o so} :
  @EquivalenceOfCategories@{so so so so so o} SupLat@{o so}
    (@EilenbergMoore@{so so so o} Sets@{o so}
       (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so})
    (EM_Comparison SL_adj@{o so}).
Proof.
  unshelve refine
    (@Build_EquivalenceOfCategories _ _ (EM_Comparison SL_adj@{o so})
       EM_induced_to_SupLat@{o so} _ _).
  - exists (fun x => SL_comparison_counit_iso@{o so} x).
    intros x y f a. reflexivity.
  - exists (fun A => iso_sym (SL_comparison_unit_iso@{o so} A)).
    intros A B f a. reflexivity.
Defined.

Definition SL_Forget_Monadic@{o so} :
  @Monadic@{so so so so so o so so} SupLat@{o so} Sets@{o so}
    SL_Forget@{o so}.
Proof.
  exists SL_Free@{o so}.
  exists SL_adj@{o so}.
  exact SL_comparison_equivalence@{o so}.
Defined.

(*
 The components of both natural isomorphisms are identities, at a
 variable object. 

 --------
 两个自然同构的分量在一个变量对象上都是恒等映射。
*)
Example SL_comparison_counit_component@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  t_alg_hom[to (projT1 (@equivalence_counit _ _ _
                           SL_comparison_equivalence@{o so}) x)]
    = @setoid_morphism_id@{o o o} (projT1 x) := eq_refl.

Example SL_comparison_counit_component_from@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  t_alg_hom[from (projT1 (@equivalence_counit _ _ _
                             SL_comparison_equivalence@{o so}) x)]
    = @setoid_morphism_id@{o o o} (projT1 x) := eq_refl.

Example SL_comparison_unit_component@{o so} (A : SupLatObject@{o}) :
  slh_map (to (projT1 (@equivalence_unit _ _ _
                         SL_comparison_equivalence@{o so}) A))
    = @setoid_morphism_id@{o o o} (sl_set A) := eq_refl.

Example SL_comparison_unit_component_from@{o so} (A : SupLatObject@{o}) :
  slh_map (from (projT1 (@equivalence_unit _ _ _
                           SL_comparison_equivalence@{o so}) A))
    = @setoid_morphism_id@{o o o} (sl_set A) := eq_refl.
