(* * * Set-indexed coproducts of categories / * * 类别的集合指标余积 *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.

(*
 PORTABILITY, learned the hard way: this MUST be the [Coq.Logic.]
 spelling, not [From Stdlib Require Import EqdepFacts].  The tree
 builds on Coq 8.19/8.20 as well as Rocq 9.1, and the [Stdlib] prefix
 does not exist on the 8.x line -- Docker CI rejects it with "Cannot
 find a physical path bound to logical path EqdepFacts with prefix
 Stdlib".  An earlier revision of this file shipped the [Stdlib]
 spelling and was the only file in the tree to use it.  Note that the
 nix [category-theory_8_19] target ACCEPTS both spellings, so a green
 nix build is not evidence here; the tree's own convention is
 [Require Import Coq.Logic.Eqdep_dec.] (Structure/Bicartesian/Matrix.v,
 Instance/Ordinal.v, Instance/FinSet/Pushout.v) and this follows it. 

 --------
 可移植性，通过实践得出的经验：这必须是 [Coq.Logic.] 拼写，而不是 [From Stdlib Require Import EqdepFacts]。该代码树在 Coq 8.19/8.20 以及 Rocq 9.1 上均可构建，而 [Stdlib] 前缀在 8.x 系列中不存在——Docker CI 会拒绝它，并提示“Cannot find a physical path bound to logical path EqdepFacts with prefix Stdlib”。该文件的早期版本使用的是 [Stdlib] 拼写，并且是树中唯一使用它的文件。请注意，nix [category-theory_8_19] 目标接受两种拼写，因此一个成功的 nix 构建并不构成证据；代码树自身的约定是 [Require Import Coq.Logic.Eqdep_dec.]（Structure/Bicartesian/Matrix.v，Instance/Ordinal.v，Instance/FinSet/Pushout.v），这里遵循该约定。
*)
Require Import Coq.Logic.EqdepFacts.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 §III.5 Exercise 4, printed p. 74 (PDF p. 84) —
 maclane:III.5:ex4
 Book:      Riehl, "Category Theory in Context", 2nd ed., §3.6 —
 riehl:3.6:construction-cat-coproducts
 nLab:      https://ncatlab.org/nlab/show/coproduct

 The disjoint union of an [I]-indexed family of categories: objects are
 the dependent pairs [(i; x)] with [x : C i], and a morphism
 [(i; x) ~> (j; y)] is a proof [e : i = j] together with a morphism
 [ob_cast C e x ~> y] of [C j].  Across summands — [i] and [j]
 distinct — the hom is EMPTY, because [i = j] is; within a summand it
 is that summand's own hom TOGETHER WITH the loop of the index proof
 it carries, and the two coincide EXACTLY under [IdxUIP] — see point
 3, where that is what [sigma_inj_Full_forces_UIP] proves and what
 [SigmaCat_inj_Full] therefore has to assume.  (An earlier revision of
 this sentence said "up to the transport that typing forces", which
 asserts the identification point 3 shows costs a hypothesis.)
 Functors out of the coproduct are given by case analysis
 ([SigmaCat_case]), and that correspondence is the universal property
 ([SigmaCat_ump]).

 - [SigmaCat C]: the coproduct category ∐_{i:I} C i
 - [SigmaCat_inj C i]: the injection C i ⟶ ∐ C
 - [SigmaCat_case F]: the case functor ∐ C ⟶ D of a family
 [F : ∀ i, C i ⟶ D], with [SigmaCat_case_inj] the triangle,
 [SigmaCat_case_unique] the uniqueness half, and [SigmaCat_ump]
 the bundled ∃! (the packaging of Structure/Limit/Product.v's
 [iprod_ump] and Construction/Product/Indexed.v's [PiCat_ump])

 The [Cat]-level packaging — [IsIndexedCoproduct], and the
 [HasIndexedCoproducts Cat] instance — is Instance/Cat/Coproduct.v,
 which also carries the comparison with the binary coproduct of
 Construction/Coproduct.v and the concrete witnesses.

 1. THE INDEX-EQUALITY ENCODING, WHICH IS THIS FILE'S REAL CONTENT.
 To say "the hom is empty across summands and the summand's hom
 within one summand" one must say when two INDICES agree, and [I]
 is an arbitrary [Type] with no decider.  Three encodings present
 themselves and they are not equivalent:

 (a) match on a DECIDER [∀ i j : I, {i = j} + {i <> j}].  Not
 taken: the exercise grants no decider, and demanding one
 would exclude, for instance, an index type of functions.

 (b) index the hom by a Leibniz equality and transport —
 [hom (i;x) (j;y) := ∃ e : i = j, ob_cast C e x ~> y] — with
 the hom-setoid comparing the two index proofs at Leibniz
 equality and the two morphisms at [≈] after transport.  THIS
 IS THE ENCODING TAKEN.

 (c) quantify over the proof — [∀ e : i = j, …] — with the setoid
 comparing pointwise.  REFUTED, and for two independent
 reasons, neither of which is about UIP.  First, it gets the
 MATHEMATICS wrong: for [i] and [j] provably distinct the type
 [∀ e : i = j, X e] is INHABITED (by the vacuous function), so
 this reading adds a morphism between every pair of objects in
 different summands — the indiscrete category on the summands,
 not their disjoint union.  Second, it does not even define a
 category: the identity at [(i;x)] would have to be a family
 [∀ e : i = i, ob_cast C e x ~> x], and for a loop [e] the
 object [ob_cast C e x] is not [x], so no identity is
 definable.  A hybrid — pair the sigma (for emptiness) with the
 ∀-family (for a proof-independent hom) — inherits the second
 failure and is refuted with it.

 A FOURTH encoding is excluded by a different argument.  One might
 try to make the hom-setoid FINER, comparing the two index proofs
 only up to CONVERSION rather than up to Leibniz equality (an
 inductive relation whose one constructor takes a single [e]).
 That relation is an equivalence and a congruence, but the
 resulting structure is not a category: associativity of the index
 component is the associativity of proof composition, which holds
 only PROPOSITIONALLY, and — whichever way the composition of index
 proofs is made to reduce — only one of the two unit laws follows
 it (this file's [sigma_compose] matches on the OUTER proof and so
 buys [id ∘ f], leaving [f ∘ id] propositional).  So the setoid
 must tolerate propositional equality of index proofs, which is
 encoding (b).  That the remaining unit law could not be bought by
 some other arrangement is an argument, not a theorem: no
 impossibility is proved.

 2. NO HYPOTHESIS IS SPENT ON THE CONSTRUCTION OR ON ITS UNIVERSAL
 PROPERTY.  [SigmaCat], [SigmaCat_inj], [SigmaCat_case],
 [SigmaCat_case_inj], [SigmaCat_case_unique] and [SigmaCat_ump]
 take NO decidability and NO uniqueness-of-identity-proofs
 hypothesis, on [I] or on anything else.  This was not the
 expected outcome and it deserves its reason.  Every proof
 obligation quantifies over the two ENDPOINT indices, so the
 index proof [e : i = j] it must reason about relates two
 universally quantified variables and can be ELIMINATED by
 [destruct]; after that elimination every transport disappears and
 the goal is the corresponding law of one summand.  Uniqueness in
 particular goes through because a family of natural isomorphisms
 [∀ i, G ◯ inj i ≈ F i] is a DEPENDENT FUNCTION of [i], so it
 already carries whatever coherence the index type's own paths
 demand; the naturality square for the comparison is proved by
 destructing the index proof of the morphism it is stated at, and
 lands exactly on the naturality of the given family at that
 index.

 3. WHERE A HYPOTHESIS IS SPENT, AND THAT IT IS NECESSARY.  What does
 need one is the classically automatic statement that the
 injections are FULL — that every endomorphism of [(i;x)] comes
 from [C i].  A loop [e : i = i] cannot be eliminated, so a
 morphism carrying one need not be [≈] to any morphism carrying
 [eq_refl].  [SigmaCat_inj_Full] therefore takes [IdxUIP I]
 explicitly, and [sigma_inj_Full_forces_UIP] proves the hypothesis
 NECESSARY rather than convenient: fullness of a single injection,
 for a family whose [i]-summand has an object with the relevant
 hom-sets inhabited, ENTAILS uniqueness of identity proofs at that
 index.  (The pattern is this tree's: Theory/OGraph.v's
 [coarse_respectfulness_entails_UIP], Theory/Category/Monoid.v's
 [arrow_mul_respects_forces_UIP], and
 Instance/Discrete/Reconstruct.v's
 [Discrete_DiscreteUpToIso_forces_UIP].)  Faithfulness splits: for
 a CONSTANT family it is free ([SigmaCat_const_inj_Faithful], by
 the retraction [SigmaCat_case (fun _ => Id)], which is
 definitionally the identity on the summand), while for a general
 family [SigmaCat_inj_Faithful] takes [IdxUIP I] and spends it one
 level up, through the stdlib's axiom-free [UIP_shift].  NO
 necessity result is proved for faithfulness — no countermodel is
 exhibited and none is claimed.

 4. UNIVERSES, MEASURED IN THE CONSTRAINT BLOCKS.  [SigmaCat] is
 declared with explicit binders, and that is LOAD-BEARING: written
 unannotated, universe minimization IDENTIFIES the summands' hom
 and proof universes — the definitions below then read
 [(I → Category@{u2 u0 u0}) → Category@{u1 u0 u0}] — and a family
 at [Category@{uo uh up}] declared under [Constraint uh < up] is
 rejected with "Cannot enforce up = uh".  Measured for BOTH
 shapes: the single [Program Definition] this file started from,
 and the pieces below with their annotations stripped.  With the
 binders written out the block is all BOUNDS and no
 identification.  The FULL block is six constraints, not three —

 ui <= us,  uo <= us,  oh <= op,
 ui <= Projections.u0,  uo <= Projections.u1,
 oh <= Projections.u1

 — and an earlier revision of this header listed only the first
 row, which understated it.  [oh <= op] is [Class Category]'s own
 [h <= p].  The three [Projections.*] bounds are the stdlib's:
 [projT1] and [projT2] are NOT universe polymorphic ([About projT1]
 says so, and [Set < Projections.u0 < Projections.u1]), so every
 universe that passes through a sigma here is additionally capped
 below a FIXED global level.  That is nothing of this file's doing
 either, and it does not disturb the headline — no constraint in
 the block is an EQUATION — but it is part of the block and is now
 stated.  So the index universe [ui] and the summands'
 object universe [uo] bound only [us], the object universe of the
 COPRODUCT, and the summands' hom and proof universes pass through
 untouched.  [SigmaCat_inj] carries the same block, and
 [SigmaCat_case] adds only the four bounds [oh <= dh], [oh <= dp],
 [op <= dp] and [dh <= dp] relating the two categories a functor
 spans, which are [Class Functor]'s.  In particular the index
 universe does NOT bound the hom universe, and the reason is worth
 naming: [eq] is Prop-valued, so the index proof carried inside
 every hom costs nothing there.  That is the point of contrast
 with the dual construction: in Construction/Product/Indexed.v's
 [PiCat] a hom IS an [I]-indexed dependent FUNCTION, so there
 [I]'s level bounds the hom universe as well — the asymmetry is
 real, not a difference of annotation.  The minimization defect
 repaired here is of the family
 Construction/Free/Quiver/Examples.v records for
 [Build_Quiver_Standard_Eq].

 THE UMP-LEVEL LEMMAS DO NOT SHARE THAT FREEDOM, AND THE CAUSE IS
 A DONOR.  [SigmaCat_case_inj], [SigmaCat_case_unique] and
 [SigmaCat_ump] all display [C : Category@{a b b}] and
 [D : Category@{c b b}] — hom and proof identified in BOTH, and
 the two categories' hom universes identified with each other.
 That is [Functor_Setoid]'s (Theory/Functor.v, itself an
 unannotated [Program Instance]) and not this file's: under
 [Constraint uh < up], [@Functor_Setoid C D] is REJECTED for a
 source at those levels and again for a target at those levels,
 while the functor TYPE [C ⟶ D] and [@Unique _ (@homset C x y) P]
 both elaborate there as positive controls.  Since [≈] on functors
 IS that setoid, no statement of the universal property in this
 library's vocabulary can avoid it; nothing here attempts to lift
 it, and it is NOT claimed unavoidable.  What it costs a consumer
 is recorded at the point of use, in Instance/Cat/Coproduct.v.

 5. PRIOR ART, AND WHAT IS *NOT* REUSED.
 - Construction/Product/Indexed.v's [PiCat] is the dual — the
 set-indexed PRODUCT of categories, Mac Lane §II.3 Ex 3 — and is
 a STRUCTURAL precedent only, not a donor: the coproduct is not
 [PiCat] of opposites, and no definition below mentions it.  The
 numbered-discussion shape of this header, and the binary-case
 note, follow that file.
 - Construction/Coproduct.v's binary [C ∐ D] is the two-summand
 case, where the index is [bool] and the case analysis is on
 CONSTRUCTORS, so it needs no index-equality machinery at all.
 The comparison at [I := bool] is made in Instance/Cat/Coproduct.v.
 - THE GROTHENDIECK ROUTE EXISTS AND WOULD COST STRICTLY MORE.
 [Construction/Displayed/Total.v]'s [Total] has
 [obj := ∃ x : C, dobj x], and over a discrete base its total
 category is a disjoint union; the way in is
 Construction/Grothendieck/Strict.v's
 [IndexedCat_of_StrictFunctor], which takes a functor into
 [StrictCat] together with the explicit hypothesis
 [Fuip : ∀ (b : B) (x y : F b) (p q : x = y), p = q] — UIP on
 the OBJECTS of every fibre — with
 [IndexedCat_of_StrictFunctor_dec] discharging it from decidable
 fibre equality via [UIP_dec].  So that route would buy the
 construction at the price of UIP on every summand's object
 type, where the direct construction pays nothing.  This is a
 MEASUREMENT of the donor's stated hypothesis, not an attempt to
 run the route: nothing here builds a [Displayed] or an
 [IndexedCat], and it is NOT claimed that the route could not be
 rearranged to spend less.

 WHAT IS NOT DELIVERED.  No notation for the indexed coproduct (the
 binary [∐] is taken and no unambiguous indexed spelling was found).
 THE COMPANION PROBE is Test/ProbeCatCoproduct338.v, which pins the
 universe measurements of point 4 as [Fail] commands and compiles the
 inhabitedness half of point 1's encoding-(c) refutation as
 [probe_forall_encoding_inhabited].  So "refuted by argument, not by
 a compiled [Fail]" below is exact as written — that half is compiled
 there as a POSITIVE, not as a [Fail] — and a reader looking for what
 IS machine-checked should look in that file.

 No [Colimit]/[DiscreteCat_Functor] reading — see
 Instance/Cat/Coproduct.v, which explains why.  No functoriality of
 [SigmaCat] in the family [C] or in the index [I], and hence no
 comparison of [∐] over a reindexing.  No dual, no relation to
 [PiCat] beyond the header remark, and no distributivity of products
 over these coproducts.  No claim that the injections are jointly
 surjective on objects other than the definitional one.  Faithfulness
 of the injections is not shown to FORCE anything.  No countermodel
 is built for any of the refuted encodings of point 1: they are
 refuted by argument in this header — the inhabitedness of a vacuous
 function type, the non-existence of an identity, and the merely
 propositional associativity of proof composition — and not by a
 compiled [Fail]. 

 --------
 书籍：      Mac Lane，《为工作中的数学家准备的范畴》，第2版，§III.5 练习4，印刷页74（PDF页84）——
 maclane:III.5:ex4
 书籍：      Riehl，《上下文中的范畴论》，第2版，§3.6 ——
 riehl:3.6:construction-cat-coproducts
 nLab：       https://ncatlab.org/nlab/show/coproduct由一个  [I] 索引的范畴族的分离并集：对象是依赖对  [(i; x)] 与  [x : C i] ，而一个态射  [(i; x) ~> (j; y)] 是一个证明  [e : i = j] 以及  [C j] 的态射  [ob_cast C e x ~> y] 。在不同的求和范畴—— [i] 与 [j]——之间，Hom 是 EMPTY，因为 [i = j] 是空的；在同一个求和范畴内，它是该求和范畴自身的 Hom 并附带其携带的索引证明的循环，而且在 [IdxUIP] 下完全一致——参见第3点，那里的 [sigma_inj_Full_forces_UIP] 证明了这一点，因此 [SigmaCat_inj_Full] 不得不假设这一点。(这个句子的早期修订版本说“取决于打字强制的传输”，它断言识别点 3 显示成本假设。)  
 来自余积的函子由案例分析给出 ([SigmaCat_case])，并且该对应是泛性质 ([SigmaCat_ump])。

 - [SigmaCat C]: 余积范畴 ∐_{i:I} C i  
 - [SigmaCat_inj C i]: 注入 C i ⟶ ∐ C  
 - [SigmaCat_case F]: 一个族的案例函子 ∐ C ⟶ D [F : ∀ i, C i ⟶ D]，其中 [SigmaCat_case_inj] 是三角形，[SigmaCat_case_unique] 是唯一性的一半，[SigmaCat_ump] 是捆绑的 ∃!（Structure/Limit/Product.v 的 [iprod_ump] 和 Construction/Product/Indexed.v 的 [PiCat_ump] 的封装）[Cat] 级别的封装 — [IsIndexedCoproduct]，以及 [HasIndexedCoproducts Cat] 实例 — 是 Instance/Cat/Coproduct.v，它还包含了与 Construction/Coproduct.v 的二元积和具体证明的比较。

 1. 索引相等编码，这是本文件的实际内容。要说“同态在各个和子之间为空，并且某一和子中的同态也为空”，必须说明何时两个索引相等，而 [I] 是一个任意的 [Type]，没有判定器。有三种编码方式，它们并不等价：

 (a) 对 DECIDER [∀ i j : I, {i = j} + {i <> j}] 进行匹配。未采用：因为练习并不提供判定器，要求一个判定器的话，会排除例如函数类型的索引。(b) 通过莱布尼茨等式和传输对 hom 进行索引——[hom (i;x) (j;y) := ∃ e : i = j, ob_cast C e x ~> y]——使用 hom-集合比较在莱布尼茨等式下的两个索引证明，以及传输后在 [≈] 上的两个态射。这就是所采用的编码。(c) 对证明进行量化 — [∀ e : i = j, …] — 使用集合体逐点比较。被反驳，并且有两个独立的理由，这两个理由都与 UIP 无关。首先，它在数学上是错误的：对于可证明不同的 [i] 和 [j]，类型 [∀ e : i = j, X e] 是可居住的（由空函数 inhabits），所以这种理解在不同求和的每对对象之间添加了一个态射——求和上的不可分离范畴，而不是它们的离散并集。其次，它甚至没有定义一个范畴：ZWZ37WZZ 的单位元必须是一个族 [∀ e : i = i, ob_cast C e x ~> x]，对于一个环 [e] 来说，对象 [ob_cast C e x] 不是 [x]，因此无法定义单位元。一种混合——将西格玛（表示空性）与 ∀ 系列（表示与证明无关的同态）配对——继承了第二种失败并因此被驳斥。通过不同的论证排除了第四种编码。有人可能尝试让同态集（hom-setoid）更细致，只比较两个索引证明在转换（CONVERSION）下而不是在莱布尼茨相等（Leibniz equality）下——莱布尼茨相等是一个归纳关系，其一个构造器接受单个 [e]。该关系是等价关系且是合同关系，但由此得到的结构不是范畴：索引分量的结合性是证明组合的结合性，而它只在命题上成立——无论索引证明的组合以何种方式化简，两个单位律中只有一个成立（此文件的 [sigma_compose] 匹配外部证明，因此获得 [id ∘ f]，留下 [f ∘ id] 为命题性）。因此，该同态集必须容忍索引证明的命题等价性，这就是编码 (b)。剩余单位定律不能通过其他安排来获得，这是一个论点，而不是定理：没有证明任何不可能性。2. 在构造或其普遍性质上没有任何假设。[SigmaCat]、[SigmaCat_inj]、[SigmaCat_case]、[SigmaCat_case_inj]、[SigmaCat_case_unique] 和 [SigmaCat_ump] 在 [I] 或其他任何东西上不做可判定性和身份唯一性证明的假设。这不是预期的结果，它是有原因的。每个证明义务都量化在两个端点索引上，所以索引证明 [e : i = j] 必须推理的对象涉及两个普遍量化的变量，并且可以通过 [destruct] 消去；在消去之后，每个传输都会消失，目标就是对应的单个加数法则。特别是唯一性是成立的，因为一族自然同构 [∀ i, G ◯ inj i ≈ F i] 是 [i] 的一个依赖函数，所以它已经承载了索引类型自身路径所要求的任何一致性；用于比较的自然性方格通过析构它所声明的态射的索引证明来证明，并且准确落在给定族在该索引处的自然性上。3. 假设何处被使用，以及它为何是必要的。所需要的，是经典的自动陈述，即注入是完整的——即 [(i;x)] 的每个自同态都来自 [C i]。一个环 [e : i = i] 无法被消除，因此携带它的态射不必是 [≈] 对应携带 [eq_refl] 的任何态射。因此 [SigmaCat_inj_Full] 明确地采用 [IdxUIP I]，并且 [sigma_inj_Full_forces_UIP] 证明了假设是必要的而不是便利的：单个注入的完整性，对于其 [i]-直和有一个对象的族，其相关的 Hom 集是非空的，意味着该索引处身份证明的唯一性。（这个模式属于这棵树：Theory/OGraph.v 的 [coarse_respectfulness_entails_UIP]，Theory/Category/Monoid.v 的 [arrow_mul_respects_forces_UIP]，以及 Instance/Discrete/Reconstruct.v 的 [Discrete_DiscreteUpToIso_forces_UIP]。）忠实性拆分：对于一个 CONSTANT 家族，它是自由的（[SigmaCat_const_inj_Faithful]，通过重traction [SigmaCat_case (fun _ => Id)]，该重traction在直和因子上从定义上就是恒等映射），而对于一个一般的家族 [SigmaCat_inj_Faithful] 将 [IdxUIP I] 提升一个层级，通过 stdlib 的无公理 [UIP_shift]。忠实性没有证明必要性结果——没有展示反例模型，也没有宣称存在反例。4. 宇宙，按约束块测量。[SigmaCat] 使用了显式绑定器声明，这是承重的：如果不带注释地书写，宇宙最小化会识别求和项的 hom 宇宙和证明宇宙 —— 下面的定义则读作 [(I → Category@{u2 u0 u0}) → Category@{u1 u0 u0}] —— 并且在 [Category@{uo uh up}] 下声明的族在 [Constraint uh < up] 下会被拒绝，提示“无法强制 up = uh”。对两种形状进行测量：这个文件最初的单个 [Program Definition]，以及下面带注释被去掉的部分。把绑定器全部写出来后，这个块全部都是边界，没有识别。完整块有六个约束，而不是三个——

 ui <= us,  uo <= us,  oh <= op,
 ui <= Projections.u0,  uo <= Projections.u1,
 oh <= Projections.u1——而这个头文件的早期修订版只列出了第一行，这低估了它。[oh <= op] 是 [Class Category] 自身的 [h <= p]。三个 [Projections.*] 的界限是标准库的：[projT1] 和 [projT2] 不是通用多态的（[About projT1] 说明了这一点，而 [Set < Projections.u0 < Projections.u1] 亦如此），所以每一个通过这里 sigma 的 universe 额外被限制在一个固定的全局层级之下。这也不是这个文件所做的，也不影响标题——块中没有约束是方程式——但它是块的一部分，现在已被说明。因此，索引 universe [ui] 和各项的对象 universe [uo] 只限制 [us]，即 COPRODUCT 的对象 universe，而各项的 hom 和 proof universes 则保持不受影响。[SigmaCat_inj] 承载相同的模块，而 [SigmaCat_case] 仅添加了四个约束 [oh <= dh]、[oh <= dp]、[op <= dp] 和 [dh <= dp]，它们将一个函子跨越的两个范畴关联起来，这些范畴是 [Class Functor] 的。特别地，指数宇宙并不约束同态宇宙，其原因值得说明：[eq] 是 Prop 值的，因此每个同态内部携带的索引证明在那里不消耗任何资源。这正是与对偶构造的对比点：在 Construction/Product/Indexed.v 的 [PiCat] 中，一个同态确实是一个 [I] 索引的依赖函数，因此 [I] 的级别也约束了同态宇宙——这种不对称是存在的，而不仅仅是标注上的差异。这里修复的最小化缺陷属于 Construction/Free/Quiver/Examples.v 的记录，针对 [Build_Quiver_Standard_Eq]。UMP级别的引理不享有这种自由，其原因是一个捐赠者。[SigmaCat_case_inj]、[SigmaCat_case_unique] 和 [SigmaCat_ump] 都显示 [C : Category@{a b b}] 和 [D : Category@{c b b}]——在两者中都确定了 hom 和证明，并且两类的 hom 宇宙彼此对应。也就是说 [Functor_Setoid]（Theory/Functor.v，它本身是一个未注释的 [Program Instance]）而不是这个文件的：在 [Constraint uh < up] 下，[@Functor_Setoid C D] 对于这些级别的源被拒绝，同时对于这些级别的目标也被拒绝，而函子类型 [C ⟶ D] 和 [@Unique _ (@homset C x y) P] 都在此处作为正控制展开。由于 [≈] 在函子上就是那个集合同构，这个库的词汇中对泛性质的任何表述都无法避免它；这里没有试图提升它，并且并不声称它是不可避免的。消费者的成本在使用点记录，在 Instance/Cat/Coproduct.v 中。5. 现有技术，以及未重复使用的内容。- Construction/Product/Indexed.v 的 [PiCat] 是对偶——类别的集合索引积，Mac Lane §II.3 Ex 3——仅是结构性先例，而非捐献者：余积并不是 [PiCat] 的对偶，下面的定义也未提及它。此标题的编号讨论形式，以及二元情况备注，遵循该文件。- Construction/Coproduct.v 的二元 [C ∐ D] 是两项求和的情况，其中索引为 [bool]，且情况分析针对构造子（CONSTRUCTORS），因此完全不需要索引等式机制。在 [I := bool] 的比较是在 Instance/Cat/Coproduct.v 中进行的。- GROTHENDIECK 路径存在且成本绝对更高。[Construction/Displayed/Total.v] 的 [Total] 有 [obj := ∃ x : C, dobj x]，并且在离散基上它的总范畴是一个不相交的并集；进入的方法是 Construction/Grothendieck/Strict.v 的 [IndexedCat_of_StrictFunctor]，它接受一个到 [StrictCat] 的函子以及明确假设 [Fuip : ∀ (b : B) (x y : F b) (p q : x = y), p = q] ——在每个纤维的对象上 UIP——并通过 [UIP_dec] 将其从可判定的纤维等同性中解除。因此，这条路径将以每个和对象类型上的 UIP 作为代价来获得构造，而直接构造则不需要付出任何代价。这是对捐赠者所陈述假设的测量，而不是尝试执行该路线：这里没有构建 [Displayed] 或 [IndexedCat]，并且并不声称该路线无法重新安排以减少花费。未交付的内容。未对索引余积做出标注（使用了二进制 [∐]，但未找到明确的索引拼写）。
 伴随探针是 Test/ProbeCatCoproduct338.v，它将第4点的宇宙测量固定为 [Fail] 命令，并将第1点的编码-(c) 反驳的可居性部分编译为 [probe_forall_encoding_inhabited]。因此下面的“通过论证被反驳，而不是通过编译的 [Fail]”准确无误 —— 那部分在文件中被编译为 POSITIVE，而非 [Fail] —— 读者若想查看什么是机器检查的，应查看该文件。没有 [Colimit] / [DiscreteCat_Functor] 的读取——参见 Instance/Cat/Coproduct.v，其中解释了原因。在族 [C] 或索引 [I] 中，[SigmaCat] 没有函子性，因此也无法在重新索引上比较 [∐]。没有对偶，也没有与 [PiCat] 的关系，除了标题中的备注，并且这些余积上没有乘积的分配性。没有声称注入在定义之外的对象上是联合满射。注入的忠实性没有被证明能够强制任何东西。对于第 1 点被驳回的编码，没有构建任何反例模型：它们是通过标题中的论证被驳回的——空函数类型的可居性、恒等式的不存在，以及证明组合的仅命题结合性——而不是由已编译的 [Fail] 驱动。
*)

(* * ** Casting along index equalities / * **沿索引相等进行类型转换** *)

(*
 Transport an object of [C i] to [C j] along [e : i = j].  Every
 dependency on the index equality in this file goes through this one
 definition. 

 --------
 沿着 [e : i = j] 将 [C i] 的对象运输到 [C j]。这个文件中对索引相等性的每一个依赖都通过这个定义进行。
*)
Definition ob_cast@{ui uo oh op} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) {i j : I} (e : i = j) (x : C i) : C j :=
  match e in _ = k return C k with eq_refl => x end.

(*
 Transport a morphism along an equality BETWEEN two index equalities.
 This is what the hom-setoid needs in order to compare two morphisms
 whose index components are only propositionally equal. 

 --------
 沿着两个索引等式之间的等式传输一个态射。这是同调集合所需要的，以便比较两个索引分量仅在命题上相等的态射。
*)
Definition mor_cast@{ui uo oh op} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) {i j : I} {x : C i} {y : C j}
  {e1 e2 : i = j} (p : e1 = e2) (f : ob_cast C e1 x ~> y) :
  ob_cast C e2 x ~> y :=
  match p in _ = e return ob_cast C e x ~> y with eq_refl => f end.

(*
 Casting along a proof and back along its inverse is the identity —
 at LEIBNIZ equality, not merely at [≈].  Both endpoints are
 universally quantified here, which is exactly why [destruct p]
 is available; the same statement instantiated at a loop is not
 provable, and that is the content of section [Fullness] below. 

 --------
 沿着一个证明进行类型转换，然后沿其逆过程返回，就是恒等——在莱布尼茨意义上的相等，而不仅仅是在 [≈] 上。这里两个端点都是全称量化的，这正是 [destruct p] 可用的原因；将在一个循环上实例化的同一陈述是不可证明的，这就是下面 [Fullness] 节的内容。
*)
Lemma mor_cast_sym@{ui uo oh op} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) {i j : I} {x : C i} {y : C j}
  {e1 e2 : i = j} (p : e1 = e2) (f : ob_cast C e1 x ~> y) :
  mor_cast C (eq_sym p) (mor_cast C p f) = f.
Proof. destruct p; reflexivity. Qed.

(* * ** The data of the coproduct category / * ** 余积范畴的数据 *)

(*
 Objects, homs and the hom-relation are named separately so that each
 carries its own universe annotation.  A NOTE ON WHAT THAT DOES AND
 DOES NOT BUY, corrected before landing: an earlier revision of this
 comment claimed that "an explicitly annotated [Program Definition] of
 this record does not elaborate at all".  That is FALSE, and was
 refuted by compiling one — with obj, hom and the hom-relation fully
 inlined and the law fields supplied BY NAME, an annotated
 [Program Definition] elaborates and prints a constraint block
 character-for-character identical to [SigmaCat]'s.  What actually
 provokes "Universe … is unbound" is proving the obligations by
 TACTIC in place, which generates constants carrying universes the
 declared binder list cannot mention.  So what is load-bearing is
 naming the obligation PROOFS, not naming the data. 

 --------
 对象、同态以及同态关系是分别命名的，以便每个都携带自己的宇宙注解。关于这会带来什么以及不会带来什么的说明，在落地之前已修正：该评论的早期版本声称“这个记录的显式注解 [Program Definition] 根本不会展开”。这是错误的，通过编译一个实例可以驳斥——在其中对象、同态和同态关系完全内联，并且法律字段按名称提供，一个注解的 [Program Definition] 会展开并打印一个与 [SigmaCat] 字符逐字相同的约束块。实际上触发“宇宙…未绑定”的原因是在原位通过策略证明义务，这会生成携带宇宙的常量，而声明的绑定器列表无法提及这些常量。因此，关键在于命名义务证明（PROOFS），而不是命名数据。
*)
Definition sigma_obj@{ui uo oh op us} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) : Type@{us} := ∃ i : I, C i.

Definition sigma_hom@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} (X Y : sigma_obj@{ui uo oh op us} C) :
  Type@{oh} := ∃ e : `1 X = `1 Y, ob_cast C e (`2 X) ~> `2 Y.

Definition sigma_equiv@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {X Y : sigma_obj@{ui uo oh op us} C}
  (f g : sigma_hom X Y) : Type@{op} :=
  ∃ p : `1 f = `1 g, mor_cast C p (`2 f) ≈ `2 g.

Definition sigma_id@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} (X : sigma_obj@{ui uo oh op us} C) :
  sigma_hom X X := (eq_refl; id).

(*
 Composition.  The match is on the index proof of the OUTER morphism:
 in the [eq_refl] branch the middle and target indices coincide, that
 morphism's transport disappears, and the two morphisms compose in one
 summand with the inner morphism's index proof carried along
 unchanged.  Matching this way round is what makes [id ∘ f] reduce
 definitionally — see [sigma_id_left]. 

 --------
 构造。该匹配发生在外部态射的指标证明上：在 [eq_refl] 分支中，中间和目标指标重合，该态射的传输消失，两个态射在一个求和项中组合，同时内态射的指标证明保持不变。以这种方式匹配正是使 [id ∘ f] 能够定义性地化简——参见 [sigma_id_left]。
*)
Definition sigma_compose@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {X Y Z : sigma_obj@{ui uo oh op us} C}
  (f : sigma_hom Y Z) (g : sigma_hom X Y) : sigma_hom X Z :=
  (match `1 f as e0 in _ = m
     return ∀ z0 : C m, (ob_cast C e0 (`2 Y) ~> z0) →
            (∃ e : `1 X = m, ob_cast C e (`2 X) ~> z0)
   with
   | eq_refl => fun z0 h => (`1 g; h ∘ `2 g)
   end) (`2 Z) (`2 f).

(** ** The category laws / ** 类别法律 *)

Lemma sigma_equiv_Equivalence@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} (X Y : sigma_obj@{ui uo oh op us} C) :
  Equivalence (@sigma_equiv@{ui uo oh op us} I C X Y).
Proof.
  constructor.
  - intros [e f]; exists eq_refl; reflexivity.
  - intros [e1 f] [e2 g] [p Hp]; simpl in *.
    destruct p; simpl in *.
    exists eq_refl; simpl; now symmetry.
  - intros [e1 f] [e2 g] [e3 h] [p Hp] [q Hq]; simpl in *.
    destruct p, q; simpl in *.
    exists eq_refl; simpl; now transitivity g.
Qed.

Lemma sigma_compose_respects@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {X Y Z : sigma_obj@{ui uo oh op us} C}
  (f f' : sigma_hom Y Z) (Hf : sigma_equiv f f')
  (g g' : sigma_hom X Y) (Hg : sigma_equiv g g') :
  sigma_equiv (sigma_compose f g) (sigma_compose f' g').
Proof.
  destruct X as [i x], Y as [j y], Z as [k z]; simpl in *.
  destruct f as [e1 f1], f' as [e2 f2], Hf as [p Hp].
  destruct g as [d1 g1], g' as [d2 g2], Hg as [q Hq]; simpl in *.
  destruct p, q; simpl in *.
  destruct e1; simpl in *.
  exists eq_refl; simpl.
  now rewrite Hp, Hq.
Qed.

(*
 [id ∘ f] REDUCES, because [sigma_compose] matches on the index proof
 of its first argument and the identity's is [eq_refl]. 

 --------
 [id ∘ f] 被简化，因为 [sigma_compose] 在其第一个参数的索引证明上匹配，而该身份的为 [eq_refl]。
*)
Lemma sigma_id_left@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {X Y : sigma_obj@{ui uo oh op us} C}
  (f : sigma_hom X Y) : sigma_equiv (sigma_compose (sigma_id Y) f) f.
Proof.
  destruct X as [i x], Y as [j y], f as [e f]; simpl in *.
  exists eq_refl; simpl; apply id_left.
Qed.

Lemma sigma_id_right@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {X Y : sigma_obj@{ui uo oh op us} C}
  (f : sigma_hom X Y) : sigma_equiv (sigma_compose f (sigma_id X)) f.
Proof.
  destruct X as [i x], Y as [j y], f as [e f]; simpl in *.
  destruct e; simpl in *.
  exists eq_refl; simpl; apply id_right.
Qed.

Lemma sigma_comp_assoc@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}}
  {X Y Z W : sigma_obj@{ui uo oh op us} C}
  (f : sigma_hom Z W) (g : sigma_hom Y Z) (h : sigma_hom X Y) :
  sigma_equiv (sigma_compose f (sigma_compose g h))
              (sigma_compose (sigma_compose f g) h).
Proof.
  destruct X as [i x], Y as [j y], Z as [k z], W as [l w].
  destruct f as [e1 f], g as [e2 g], h as [e3 h]; simpl in *.
  destruct e1, e2, e3; simpl in *.
  exists eq_refl; simpl; apply comp_assoc.
Qed.

Lemma sigma_comp_assoc_sym@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}}
  {X Y Z W : sigma_obj@{ui uo oh op us} C}
  (f : sigma_hom Z W) (g : sigma_hom Y Z) (h : sigma_hom X Y) :
  sigma_equiv (sigma_compose (sigma_compose f g) h)
              (sigma_compose f (sigma_compose g h)).
Proof.
  destruct X as [i x], Y as [j y], Z as [k z], W as [l w].
  destruct f as [e1 f], g as [e2 g], h as [e3 h]; simpl in *.
  destruct e1, e2, e3; simpl in *.
  exists eq_refl; simpl; apply comp_assoc_sym.
Qed.

(** ** The coproduct category / ** 余积范畴 *)

(*
 The explicit universe binders are load-bearing; see header point 4. 

 --------
 显式宇宙绑定器是承重的；见标题第4点。
*)
Definition SigmaCat@{ui uo oh op us} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) : Category@{us oh op} := {|
  obj := sigma_obj@{ui uo oh op us} C;
  hom := @sigma_hom@{ui uo oh op us} I C;
  homset := fun X Y =>
    {| equiv := @sigma_equiv@{ui uo oh op us} I C X Y
     ; setoid_equiv := sigma_equiv_Equivalence@{ui uo oh op us} X Y |};
  id := @sigma_id@{ui uo oh op us} I C;
  compose := @sigma_compose@{ui uo oh op us} I C;
  compose_respects := fun X Y Z f f' Hf g g' Hg =>
    sigma_compose_respects f f' Hf g g' Hg;
  id_left := @sigma_id_left@{ui uo oh op us} I C;
  id_right := @sigma_id_right@{ui uo oh op us} I C;
  comp_assoc := @sigma_comp_assoc@{ui uo oh op us} I C;
  comp_assoc_sym := @sigma_comp_assoc_sym@{ui uo oh op us} I C
|}.

(** ** The injections / ** 注射 *)

Definition sigma_inj_obj@{ui uo oh op us} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) (i : I) (x : C i) :
  sigma_obj@{ui uo oh op us} C := (i; x).

Definition sigma_inj_map@{ui uo oh op us} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) (i : I) {x y : C i} (f : x ~> y) :
  sigma_hom (sigma_inj_obj@{ui uo oh op us} C i x)
            (sigma_inj_obj@{ui uo oh op us} C i y) := (eq_refl; f).

Lemma sigma_inj_map_respects@{ui uo oh op us} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) (i : I) {x y : C i} (f g : x ~> y) :
  f ≈ g → sigma_equiv (sigma_inj_map@{ui uo oh op us} C i f)
                      (sigma_inj_map@{ui uo oh op us} C i g).
Proof. intros H; exists eq_refl; exact H. Qed.

Lemma sigma_inj_map_id@{ui uo oh op us} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) (i : I) (x : C i) :
  sigma_equiv (sigma_inj_map@{ui uo oh op us} C i (@id (C i) x))
              (sigma_id (sigma_inj_obj@{ui uo oh op us} C i x)).
Proof. exists eq_refl; reflexivity. Qed.

Lemma sigma_inj_map_comp@{ui uo oh op us} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) (i : I) {x y z : C i}
  (f : y ~> z) (g : x ~> y) :
  sigma_equiv (sigma_inj_map@{ui uo oh op us} C i (f ∘ g))
              (sigma_compose (sigma_inj_map@{ui uo oh op us} C i f)
                             (sigma_inj_map@{ui uo oh op us} C i g)).
Proof. exists eq_refl; reflexivity. Qed.

Definition SigmaCat_inj@{ui uo oh op us} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) (i : I) :
  C i ⟶ SigmaCat@{ui uo oh op us} C :=
  @Build_Functor (C i) (SigmaCat@{ui uo oh op us} C)
    (sigma_inj_obj@{ui uo oh op us} C i)
    (fun x y f => sigma_inj_map@{ui uo oh op us} C i f)
    (fun x y f g H => sigma_inj_map_respects C i f g H)
    (fun x => sigma_inj_map_id C i x)
    (fun x y z f g => sigma_inj_map_comp C i f g).

(*
 Across summands the hom is EMPTY, and it is empty for the only
 reason it could be: the index equality it carries is. 

 --------
 在各个加数中，Hom 是空的，它之所以为空，只有唯一的原因：它所携带的指数相等性。
*)
Lemma sigma_hom_cross_empty {I : Type} (C : I → Category)
  {X Y : SigmaCat C} (H : `1 X = `1 Y → False) : (X ~> Y) → False.
Proof. intros [e _]; exact (H e). Qed.

(* An empty index leaves the coproduct with no objects at all. / 一个空索引会使余积根本没有任何对象。 *)
Lemma SigmaCat_empty_no_obj (C : Empty_set → Category) :
  obj[SigmaCat C] → False.
Proof. intros [i _]; destruct i. Qed.

(* * ** The case functor and the universal property / * ** 例词符与泛性质 *)

(*
 A family of functors out of the summands assembles into one functor
 out of the coproduct.  On a morphism the match eliminates the index
 proof: in the [eq_refl] branch source and target lie in the same
 summand and the answer is that summand's functor applied to the
 (now untransported) morphism. 

 --------
 从各个子加法项出来的函子族可以组装成一个来自直和的函子。在一个态射上，匹配会消除索引证明：在 [eq_refl] 分支中，源和目标位于同一子加法项中，答案是该子加法项的函子应用到（现在未传输的）态射上。
*)
Definition sigma_case_obj@{ui uo oh op us do dh dp} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {D : Category@{do dh dp}}
  (F : ∀ i : I, C i ⟶ D) (X : sigma_obj@{ui uo oh op us} C) : D :=
  F (`1 X) (`2 X).

Definition sigma_case_map@{ui uo oh op us do dh dp} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {D : Category@{do dh dp}}
  (F : ∀ i : I, C i ⟶ D) {X Y : sigma_obj@{ui uo oh op us} C}
  (f : sigma_hom X Y) :
  sigma_case_obj@{ui uo oh op us do dh dp} F X ~>
  sigma_case_obj@{ui uo oh op us do dh dp} F Y :=
  (match `1 f as e0 in _ = m
     return ∀ y0 : C m, (ob_cast C e0 (`2 X) ~> y0) →
            (F (`1 X) (`2 X) ~> F m y0)
   with
   | eq_refl => fun y0 h => fmap[F (`1 X)] h
   end) (`2 Y) (`2 f).

Lemma sigma_case_map_respects@{ui uo oh op us do dh dp} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {D : Category@{do dh dp}}
  (F : ∀ i : I, C i ⟶ D) {X Y : sigma_obj@{ui uo oh op us} C}
  (f g : sigma_hom X Y) (H : sigma_equiv f g) :
  sigma_case_map@{ui uo oh op us do dh dp} F f
    ≈ sigma_case_map@{ui uo oh op us do dh dp} F g.
Proof.
  destruct X as [i x], Y as [j y]; simpl in *.
  destruct f as [e1 f], g as [e2 g], H as [p Hp]; simpl in *.
  destruct p; simpl in *.
  destruct e1; simpl in *.
  exact (@fmap_respects _ _ (F i) x y f g Hp).
Qed.

Lemma sigma_case_map_id@{ui uo oh op us do dh dp} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {D : Category@{do dh dp}}
  (F : ∀ i : I, C i ⟶ D) (X : sigma_obj@{ui uo oh op us} C) :
  sigma_case_map@{ui uo oh op us do dh dp} F (sigma_id X) ≈ id.
Proof. destruct X as [i x]; simpl; apply fmap_id. Qed.

Lemma sigma_case_map_comp@{ui uo oh op us do dh dp} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {D : Category@{do dh dp}}
  (F : ∀ i : I, C i ⟶ D) {X Y Z : sigma_obj@{ui uo oh op us} C}
  (f : sigma_hom Y Z) (g : sigma_hom X Y) :
  sigma_case_map@{ui uo oh op us do dh dp} F (sigma_compose f g)
    ≈ sigma_case_map@{ui uo oh op us do dh dp} F f
        ∘ sigma_case_map@{ui uo oh op us do dh dp} F g.
Proof.
  destruct X as [i x], Y as [j y], Z as [k z]; simpl in *.
  destruct f as [e1 f], g as [e2 g]; simpl in *.
  destruct e1, e2; simpl in *.
  apply fmap_comp.
Qed.

Definition SigmaCat_case@{ui uo oh op us do dh dp} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {D : Category@{do dh dp}}
  (F : ∀ i : I, C i ⟶ D) : SigmaCat@{ui uo oh op us} C ⟶ D :=
  @Build_Functor (SigmaCat@{ui uo oh op us} C) D
    (sigma_case_obj@{ui uo oh op us do dh dp} F)
    (fun X Y f => sigma_case_map@{ui uo oh op us do dh dp} F f)
    (fun X Y f g H => sigma_case_map_respects F f g H)
    (fun X => sigma_case_map_id F X)
    (fun X Y Z f g => sigma_case_map_comp F f g).

(*
 The triangle.  Both actions of the composite are DEFINITIONALLY
 those of [F i] — the two Examples below pin that at [eq_refl] — so
 the witnessing natural isomorphism is the identity family, as in
 [PiCat_Pair_Proj]. 

 --------
 三角形。复合的两个动作在定义上都是[F i]的动作——下面的两个例子在[eq_refl]处固定了这一点——因此见证自然同构的是恒等族，如[PiCat_Pair_Proj]所示。
*)
Example sigma_case_inj_fobj {I : Type} {C : I → Category} {D : Category}
  (F : ∀ i : I, C i ⟶ D) (i : I) :
  fobj[SigmaCat_case F ◯ SigmaCat_inj C i] = fobj[F i] := eq_refl.

Example sigma_case_inj_fmap {I : Type} {C : I → Category} {D : Category}
  (F : ∀ i : I, C i ⟶ D) (i : I) (x y : C i) (f : x ~> y) :
  fmap[SigmaCat_case F ◯ SigmaCat_inj C i] f = fmap[F i] f := eq_refl.

(*
 The whole functor RECORD is not recovered, however: the composite
 rebuilds the three law fields, and they are distinct opaque terms.
 Measured, not assumed. 

 --------
 整个函子 RECORD 并未恢复，然而：复合体重建了三个律域字段，它们是不同的不透明项。经过测量，而非假设。
*)
Fail Example sigma_case_inj_strict {I : Type} {C : I → Category}
  {D : Category} (F : ∀ i : I, C i ⟶ D) (i : I) :
  SigmaCat_case F ◯ SigmaCat_inj C i = F i := eq_refl.

Lemma SigmaCat_case_inj {I : Type} {C : I → Category} {D : Category}
  (F : ∀ i : I, C i ⟶ D) (i : I) :
  SigmaCat_case F ◯ SigmaCat_inj C i ≈ F i.
Proof.
  simpl; exists (fun _ => iso_id).
  intros x y f; simpl.
  rewrite id_left, id_right; reflexivity.
Qed.

(*
 Uniqueness, up to [Cat]'s hom-equivalence.  NO hypothesis: the
 comparison's components are read off the given family, and its
 naturality square is proved by eliminating the index proof of the
 morphism it is stated at, which reduces it to the naturality of the
 given family at that index. 

 --------
 唯一性，直到 [Cat] 的同等价。无假设：比较的分量直接从给定的族中读取，其自然性方阵通过消去其所述态射的指标证明来证明，这将其归约为给定族在该指标处的自然性。
*)
Lemma SigmaCat_case_unique {I : Type} {C : I → Category} {D : Category}
  (F : ∀ i : I, C i ⟶ D) (G : SigmaCat C ⟶ D) :
  (∀ i : I, G ◯ SigmaCat_inj C i ≈ F i) → G ≈ SigmaCat_case F.
Proof.
  intros H.
  unshelve eexists.
  - intros [i x]; exact (`1 (H i) x).
  - intros [i x] [j y] [e f]; simpl in *.
    destruct e; simpl in *.
    exact (`2 (H i) x y f).
Qed.

(*
 The universal property, bundled: existence is the case functor with
 its triangle, uniqueness the lemma above. 

 --------
 通用性质，捆绑：存在性是带有其三角形的情形函子，唯一性是上面的引理。
*)
Lemma SigmaCat_ump {I : Type} {C : I → Category} {D : Category}
  (F : ∀ i : I, C i ⟶ D) :
  ∃! G : SigmaCat C ⟶ D, ∀ i : I, G ◯ SigmaCat_inj C i ≈ F i.
Proof.
  unshelve eapply Build_Unique.
  - exact (SigmaCat_case F).
  - exact (SigmaCat_case_inj F).
  - intros G HG; symmetry; exact (SigmaCat_case_unique F G HG).
Qed.

(* * ** Fullness and faithfulness of the injections / * ** 注射的充分性和忠实性 *)

(*
 Uniqueness of identity proofs on the index, in the Streicher-K form
 Theory/OGraph.v's [NodeUIP] uses — which is also the form the
 stdlib's [UIP_shift] consumes. 

 --------
 索引上身份证明的唯一性，在 Streicher-K 形式中
 Theory/OGraph.v 的 [NodeUIP] 使用——这也是 stdlib 的 [UIP_shift] 消耗的形式。
*)
Definition IdxUIP (I : Type) : Type := ∀ (i : I) (p : i = i), p = eq_refl.

Lemma IdxUIP_pair {I : Type} (U : IdxUIP I) {i j : I} (p q : i = j) : p = q.
Proof. destruct p; symmetry; apply U. Qed.

(*
 Faithfulness for a GENERAL family spends [IdxUIP] one level up: the
 hypothesis hands over an equality [p] between two proofs of [i = i],
 and only [UIP_shift] — the axiom-free "a type with unique identity
 proofs has unique identity-proof-proofs" of the stdlib's
 EqdepFacts — makes [p] itself [eq_refl], which is what erases the
 transport. 

 --------
 对于一个通用家庭的忠诚度，将 [IdxUIP] 提升一个层次：假设提供了 [p]，即 [i = i] 的两个证明之间的相等性，而只有 [UIP_shift]——stdlib 的 EqdepFacts 中无公理的 “具有唯一身份证明的类型具有唯一身份证明的证明”——使得 [p] 本身 [eq_refl]，这就是消除传输的原因。
*)
Program Definition SigmaCat_inj_Faithful {I : Type} (C : I → Category)
  (U : IdxUIP I) (i : I) : Faithful (SigmaCat_inj C i) := {|
  fmap_inj := _
|}.
Next Obligation.
  intros I C U i x y f g [p Hp]; simpl in *.
  rewrite (UIP_shift I U i eq_refl p) in Hp.
  exact Hp.
Qed.

(*
 Faithfulness for a CONSTANT family is free.  The case functor of the
 constantly-identity family retracts the injection — definitionally,
 by [sigma_case_inj_fmap] — and a functor whose composite with
 another is faithful is faithful. 

 --------
 对一个恒定家族的忠诚是免费的。恒定同一性家族的函子会抽回注入——按照定义，由 [sigma_case_inj_fmap]——并且一个与另一个复合后仍然忠实的函子本身也是忠实的。
*)
Lemma Faithful_cancel {C D E : Category} (F : C ⟶ D) (G : D ⟶ E) :
  Faithful (G ◯ F) → Faithful F.
Proof.
  intros H; construct.
  apply (@fmap_inj _ _ (G ◯ F) H); simpl.
  now rewrite X.
Qed.

Definition SigmaCat_const_retract {I : Type} (D : Category) (i : I) :
  Faithful (SigmaCat_case (fun _ : I => Id[D])
              ◯ SigmaCat_inj (fun _ : I => D) i).
Proof.
  constructor; intros x y f g H; exact H.
Defined.

Definition SigmaCat_const_inj_Faithful {I : Type} (D : Category) (i : I) :
  Faithful (SigmaCat_inj (fun _ : I => D) i) :=
  Faithful_cancel _ _ (SigmaCat_const_retract D i).

(*
 Fullness needs [IdxUIP] outright: the chosen preimage of a morphism
 is its second component read back through the index proof's collapse
 to [eq_refl]. 

 --------
 满性需要 [IdxUIP]  直接：一个态射的选定前像是其第二个分量，通过索引证明的坍塌回读到 [eq_refl] 。
*)
Program Definition SigmaCat_inj_Full {I : Type} (C : I → Category)
  (U : IdxUIP I) (i : I) : Full (SigmaCat_inj C i) := {|
  prefmap := fun x y g => mor_cast C (U i (`1 g)) (`2 g)
|}.
Next Obligation.
  intros I C U i x y g; simpl.
  exists (eq_sym (U i (`1 g))); simpl.
  rewrite mor_cast_sym; reflexivity.
Qed.

(*
 …and the hypothesis is NECESSARY, not merely convenient.  Given an
 object [x] of the [i]-summand whose hom-sets out of every
 loop-transport of [x] are inhabited — as they are for the terminal
 category, the instantiation carried out in Instance/Cat/Coproduct.v
 — fullness of the injection at [i] ENTAILS that every loop at [i] is
 [eq_refl].  The chosen preimage's own section condition supplies an
 equality [eq_refl = e] for an arbitrary loop [e], and that is
 Streicher's K at [i]. 

 --------
 ……并且这个假设是必要的，而不仅仅是方便的。给定一个对象 [x]，它是 [i]-直和的一个加和，其从 [x] 的每个环绕运输出的同态集合都是非空的——正如在终端范畴中一样，在 Instance/Cat/Coproduct.v 中进行的实例化——在 [i] 处的注入的充足性意味着 [i] 的每个环都是 [eq_refl]。所选的原像自身的截面条件为任意环 [e] 提供了一个等式 [eq_refl = e]，这就是 Streicher 在 [i] 处的 K。
*)
Theorem sigma_inj_Full_forces_UIP {I : Type} (C : I → Category) (i : I)
  (x : C i) (pt : ∀ e : i = i, ob_cast C e x ~> x)
  (H : Full (SigmaCat_inj C i)) : ∀ e : i = i, e = eq_refl.
Proof.
  intros e.
  exact (eq_sym (`1 (@fmap_sur _ _ _ H x x (e; pt e)))).
Qed.

(** ** The singleton index / ** 单例索引 *)

(*
 Over a one-element index the coproduct collapses onto its single
 summand.  The two comparison functors are the case functor of the
 constantly-identity family and the injection; one composite is the
 identity with identity components, and the other needs uniqueness of
 identity proofs on [poly_unit], which Hedberg supplies from its
 (trivial) decidable equality, so nothing is assumed. 

 --------
 在一个单元素索引上，共积会坍缩到它的单个加数上。两个比较函子是恒等族的情况函子和注入；一个复合是带有恒等分量的恒等，另一个则需要 [poly_unit] 上恒等证明的唯一性，而 Hedberg 从其（平凡的）可判定等式中提供了这一点，因此没有假设任何条件。
*)
Definition SigmaCat_unit_collapse {D : Category} :
  SigmaCat (fun _ : poly_unit => D) ⟶ D := SigmaCat_case (fun _ => Id[D]).

Definition SigmaCat_unit_expand {D : Category} :
  D ⟶ SigmaCat (fun _ : poly_unit => D) :=
  SigmaCat_inj (fun _ : poly_unit => D) ttt.

Definition sigma_poly_unit_dec (x y : poly_unit) : {x = y} + {x <> y} :=
  match x, y with ttt, ttt => left eq_refl end.

Definition poly_unit_IdxUIP : IdxUIP poly_unit :=
  fun i p => Eqdep_dec.UIP_dec sigma_poly_unit_dec p eq_refl.

Lemma SigmaCat_unit_round_l {D : Category} :
  SigmaCat_unit_collapse ◯ SigmaCat_unit_expand ≈ Id[D].
Proof.
  simpl; exists (fun _ => iso_id).
  intros x y f; simpl.
  rewrite id_left, id_right; reflexivity.
Qed.

Lemma SigmaCat_unit_round_r {D : Category} :
  SigmaCat_unit_expand ◯ SigmaCat_unit_collapse
    ≈ Id[SigmaCat (fun _ : poly_unit => D)].
Proof.
  unshelve eexists.
  - intros [u x]; destruct u; exact iso_id.
  - intros [u x] [v y] [e f]; destruct u, v; simpl in *.
    assert (He : e = eq_refl) by apply poly_unit_IdxUIP.
    subst e; simpl.
    exists eq_refl; simpl.
    rewrite id_left, id_right; reflexivity.
Qed.
