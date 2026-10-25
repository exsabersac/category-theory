Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Limit.

Generalizable All Variables.

(* * * Complete and cocomplete categories / * * 完全范畴与余完全范畴 *)

(*
 nLab:      https://ncatlab.org/nlab/show/complete+category
 Wikipedia: https://en.wikipedia.org/wiki/Complete_category

 Wikipedia: "a category C is complete if every diagram F : J → C (where J is
 small) has a limit in C." Dually, C is cocomplete if every such diagram has
 a colimit. nLab: a category "has all small limits" when "every small diagram
 F : D → C where D is a small category has a limit in C." In library notation
 the completeness condition reads:

 ∀ (D : Category) (F : D ⟶ C), Limit F,

 i.e. there is a [Limit] (a terminal/universal cone, see [Structure/Limit.v])
 for every diagram F of shape D in C. Cocompleteness is the exact dual,
 asking for a [Colimit] of every diagram; since [Colimit F := Limit (F^op)],
 C is cocomplete iff C^op is complete, matching the duality recorded by both
 sources.

 On the index class: both sources restrict J (here D) to be *small*. Wikipedia
 notes that demanding limits for *all* (proper-class-sized) diagrams "is too
 strong to be practically relevant" — such a C would be forced to be thin. The
 definitions below quantify over [∀ (D : Category)] without an explicit
 smallness hypothesis; the size discipline is instead carried implicitly by
 the library's universe polymorphism. When [Complete]/[Cocomplete] are
 instantiated, the universe levels of D become constrained relative to those
 of C, which is the universe-polymorphic stand-in for "D small relative to C".
 So these state "has a limit for every (suitably small) diagram" rather than
 the inconsistent all-diagrams reading. The morphism-level equality is the
 setoid [≈] of C, supplied inside [Limit]/[Cone]; it does not appear here. 

 --------
 nLab:       https://ncatlab.org/nlab/show/complete+category 
 维基百科:  https://en.wikipedia.org/wiki/Complete_category 

 维基百科: “一个范畴 C 是完备的，如果每个图 F : J → C（其中 J 是小范畴）在 C 中都有极限。” 对偶地，C 是余完备的，如果每个这样的图都有余极限。nLab: 当“每个小图 F : D → C（其中 D 是小范畴）在 C 中都有极限”时，一个范畴“具有所有小极限”。在库符号中，完备条件写作：

 ∀ (D : Category) (F : D ⟶ C), Limit F,

 也就是说，对于 C 中形状为 D 的每个图 F，都存在一个 [Limit]（一个终/普遍锥，见 [Structure/Limit.v]）。余完备性是完全的对偶，要求每个图都有 [Colimit]；因为 [Colimit F := Limit (F^op)]，C 余完备当且仅当 C^op 完备，这与两个来源所记录的对偶性一致。关于指标类：两个来源都将 J（此处为 D）限制为*小*。维基百科指出，对*所有*（真类大小的）图要求极限“在实际应用中太强”，这样的 C 将被迫是稀薄的。下面的定义对 [∀ (D : Category)] 进行量化，而没有明确的小性假设；相反，大小的约束是通过库的宇宙多态性隐式实现的。当实例化 [Complete] / [Cocomplete] 时，D 的宇宙层次会相对于 C 的层次受到约束，而 C 是“D 相对于 C 小”的宇宙多态替代。因此，这些定义表示“对于每个（适当小的）图都有极限”，而不是矛盾的全图解读。态射层面的等式是 C 中的集合 [≈]，在 [Limit] / [Cone] 内提供；它在这里没有出现。
*)

(*
 Completeness as a working hypothesis

 nLab:  https://ncatlab.org/nlab/show/complete+small+category
 nLab:  https://ncatlab.org/nlab/show/adjoint+functor+theorem
 Paper: Hyland, "A small complete category", Annals of Pure and Applied
 Logic 40, 1988

 [Complete] is the blanket limit hypothesis: rather than checking, per
 construction, that this pullback or that wide product exists, a
 development records once that every (small) diagram has a limit and
 then draws arbitrary limit shapes on demand.  The hypothesis is
 checkable because limits reduce to two constructions: a category with
 all small products and equalizers of parallel pairs has all small
 limits, each limit arising as an equalizer between two products
 (Mac Lane, Categories for the Working Mathematician, 1971, Theorem
 V.2.1; Riehl, Category Theory in Context, 2016, Theorem 3.4.12).  This
 is how Set, Top, Grp, Ab, and module categories are shown complete,
 and the property propagates: presheaf categories inherit all small
 limits (Instance/Fun/Limit.v's [Presheaf_Complete]) and colimits (nLab,
 "category of presheaves") from Sets, and monadic functors create limits, so
 algebras for a monad on a complete category are again complete (nLab,
 "complete category").  The reduction is Structure/Limit/FromProducts.v's
 [Complete_from_products_equalizers] over [HasIndexedProducts] and
 [HasEqualizers], each limit the equalizer [limit_of_products_equalizer].

 The smallness discipline the header describes is not decoration.
 Freyd proved that a category with products of families as large as its
 own morphism set is a preorder (Abelian Categories, Harper & Row,
 1964, exercise D of ch. 3): were some hom-set to hold two distinct
 arrows, the product indexed by all morphisms would yield a hom-set of
 cardinality at least 2^|Mor|, exceeding |Mor| by Cantor's theorem.  It
 follows that complete small categories are preorders — up to
 equivalence, complete lattices (Adámek–Herrlich–Strecker, Abstract and
 Concrete Categories, Theorem 12.7; Shulman, arXiv:0810.1279, Thm 2.1).
 Here it is Structure/Complete/Freyd.v's [small_complete_is_thin]
 (arrows indexed by a type, [Complete], a DECIDABLE hom-setoid ⇒ [Thin])
 with [complete_has_glbs]; and instantiating [Complete] forces the
 diagram category's hom universe to coincide with C's (SAFT.v's header).

 Completeness is one of the engine hypotheses of the adjoint functor
 theorems, which originate in the same exercise section of Freyd's book
 (nLab, "adjoint functor theorem"; the solution-set condition is called
 pre-adjointness in Freyd–Scedrov, Categories, Allegories, 1990).  GAFT
 concludes a left adjoint from a limit-preserving functor out of a
 complete, locally small category with a solution set; SAFT trades
 the solution set for well-poweredness and a cogenerating set.  The
 in-tree consumers apply [Complete] exactly as stated: Adjunction/GAFT.v
 derives binary equalizers by applying the hypothesis at the walking
 parallel pair ([Complete_HasEqualizers]), Construction/Comma/Limit.v
 lifts completeness along the comma construction ([Comma_Complete]),
 and Adjunction/SAFT.v builds its cogenerator products and powers
 ([cogen_prod], [cogen_power]) from the same source.  Yet
 Theory/WeaklyInitial.v deliberately takes its two products as explicit
 hypotheses rather than harvesting them from a [Complete] instance, so
 that the size of the index — and with it the universe constraints —
 remains in the caller's hands.

 Both definitions below are Type-valued data, not mere propositions: an
 inhabitant of [Complete] is a function assigning to every diagram a
 chosen limit, a limit oracle applied downstream like any other
 function.  Dually, Theory/Adamek/Corollaries.v applies [Cocomplete] at
 the ordinal ω and the chain of an endofunctor to obtain the colimit
 that Adámek's initial-algebra construction consumes
 ([adamek_cocomplete]).  Finally, Freyd's collapse is essentially
 classical.  Hyland exhibited, inside the effective topos, a complete
 small category that is not a preorder, built from partial equivalence
 relations (Hyland, "A small complete category", 1988), so the thinness
 theorem cannot be proved constructively — which is why Freyd.v takes
 the decider [DecHom] as an explicit hypothesis and stays axiom-free;
 its [freyd_no_separated_pair] is the constructive kernel.  The stake is
 the semantics of impredicative polymorphism: interpreting ∀X.T as a
 product over all objects of a small complete subcategory of Set is
 classically impossible (Reynolds 1984), yet realizably consistent —
 the PER models of System F: a type of all types closed under products. 

 --------
 作为工作假设的完备性

 nLab:   https://ncatlab.org/nlab/show/complete+small+category 
 nLab:   https://ncatlab.org/nlab/show/adjoint+functor+theorem 
 论文: Hyland, 《一个小完备范畴》，纯粹与应用逻辑年刊 40, 1988[Complete] 是全局极限假设：与其逐个检查某个拉回或某个广义积是否存在，不如开发一次记录每个（小）图都有一个极限，然后按需绘制任意极限形状。这个假设是可检验的，因为极限可以归约为两种构造：一个具有所有小积和并行对等化子的范畴拥有所有小极限，每个极限都作为两个积之间的等化子出现（Mac Lane，《为工作数学家准备的范畴论》，1971，第 V.2.1 定理；Riehl，《语境中的范畴论》，2016，第 3.4.12 定理）。这是 Set、Top、Grp、Ab 和模范畴显示为完备的方式，并且该性质是可传递的：预层范畴继承所有小极限（Instance/Fun/Limit.v 的 [Presheaf_Complete]）和余极限（nLab，“预层的范畴”）自集合，而幺半群函子会生成极限，因此一个完备范畴上的幺模的代数仍然是完备的（nLab，“完备范畴”）。其归约是 Structure/Limit/FromProducts.v 的 [Complete_from_products_equalizers] 超 [HasIndexedProducts] 和 [HasEqualizers]，每个极限都是等化子 [limit_of_products_equalizer]。标题中描述的小性不是装饰。Freyd 证明了，如果一个范畴的积的族与其自身的态射集合一样大，则该范畴是一个预序（Abelian Categories, Harper & Row, 1964，第3章练习D）：如果某个同态集合中包含两条不同的箭头，由所有态射索引的积将产生一个至少有 2^|Mor| 个元素的同态集合，根据康托尔定理超过 |Mor|。因此，完全小范畴是预序——等价意义下，是完备格（Adámek–Herrlich–Strecker, Abstract and Concrete Categories, 定理 12.7；Shulman, arXiv:0810.1279, 定理 2.1）。这是 Structure/Complete/Freyd.v 的 [small_complete_is_thin]
 （箭头按类型索引，[Complete]，一个可判定的同类集合 ⇒ [Thin]）
 与 [complete_has_glbs]；并实例化 [Complete] 会迫使图范畴的同态宇宙与 C 的同态宇宙重合（SAFT.v 的标题）。完备性是伴随函子定理的引擎假设之一，该定理起源于弗雷德（Freyd）书中的同一练习部分（nLab，“adjoint functor theorem”；解集条件在 Freyd–Scedrov，《Categories, Allegories》，1990 中被称为预伴随性）。GAFT 从一个具有解集的完备、局部小范畴中，关于极限保持函子的左伴随得出结论；SAFT 将解集条件替换为良幂性和共生集合。树内的消费者严格按照 [Complete] 的说明来应用：Adjunction/GAFT.v 通过在行走平行对 ([Complete_HasEqualizers]) 上应用假设来推导二元等化器，Construction/Comma/Limit.v 通过逗号构造 ([Comma_Complete]) 提升完备性，Adjunction/SAFT.v 则从同一个来源构建其余生成器的积和幂 ([cogen_prod], [cogen_power])。然而，Theory/WeaklyInitial.v 刻意将它的两个积作为显式假设，而不是从 [Complete] 实例中获取，因此索引的大小——以及随之的宇宙限制——保持在调用者手中。下面的两个定义都是类型值数据，而不是单纯的命题：[Complete] 的一个元素是一个函数，它为每个图指定一个选定的极限，一个极限预言机像任何其他函数一样在下游应用。相反，Theory/Adamek/Corollaries.v 在序数 ω 和一个端函子的链上应用 [Cocomplete]，以获得 Adámek 的初代数构造所使用的余极限（[adamek_cocomplete]）。最后，Freyd 的塌缩本质上是经典的。Hyland 在有效顶内展示了一个完全小范畴，它不是一个预序，构建自部分等价关系（Hyland，《A small complete category》，1988），因此薄性定理不能用构造的方法证明——这就是为什么 Freyd.v 将决策者 [DecHom] 作为一个显式假设并保持无公理；它的 [freyd_no_separated_pair] 是构造核。关键在于不可定义多态性的语义：将 ∀X.T 理解为小完全子范畴 Set 的所有对象的乘积在经典意义上是不可能的（Reynolds 1984），但在可实现意义上是一致的——System F 的 PER 模型：一个在乘积下闭合的所有类型的类型。
*)

(*
 ---------------------------------------------------------------------
 THE SIZE NOTE: solution sets, shape universes, and propositional
 equality.  AUTHORITATIVE; cite it, do not restate it.

 This is the library's single statement of why the adjoint functor
 theorems are hard to APPLY at a concrete algebraic category, and of what
 this library does about it.  docs/INHABITATION.md's preamble carries a
 two-paragraph echo and names this block as the authority; the headers of
 Adjunction/GAFT.v, Adjunction/SpanningArrow.v, Instance/Mod/TensorAFT.v
 and Instance/Grp/FreeAFT.v cite it rather than re-deriving the
 arithmetic.  What it does NOT cover is [Complete]'s own four universe
 binders: those are the block immediately below, and are not repeated
 here.

 1. THREE LINES OF SIZE ARITHMETIC.  Measured with [About] under
 [Set Printing Universes]; the readbacks and the two refusals are
 pinned in Test/ProbePropEquiv.v:

 PropRelSpace@{u}   : Type@{u} → Type@{u}
 CRelSpace@{u v}    : Type@{u} → Type@{v}     with u < v
 Setoid@{u u} A     : Type@{u+1}, one level above the carrier

 A [Prop]-valued relation on a carrier in [Type@{u}] is itself a type
 in [Type@{u}].  A [Type]-valued one is NOT: ascribing the same space
 at the carrier's own level ([CRelSpace_small], Test/ProbePropEquiv.v:
 310) is refused, "The term "A → A → Type" has type "Type@{u+1}" while
 it is expected to have type "Type@{u}"".

 This library's `≈` is [Type]-valued -- [equiv : crelation A],
 Lib/Setoid.v -- and stays so, because in [Cat] an [F ≈ G] IS a
 family of isomorphisms (Theory/Functor.v, [Functor_Setoid]):
 data, which truncation would discard.  CONSEQUENCE: for a setoid
 whose `≈` is [Type]-valued, the congruences on its carrier -- and so
 the family of quotient presentations of a term model, which is what
 Mac Lane's §V.7 solution-set argument produces -- form a type one
 universe ABOVE that carrier.

 2. THE CONSTRAINT CHAIN OF THE ADJOINT FUNCTOR THEOREM.  Three links,
 each measured.

 (a) [Complete] leaves its shape-object universe free (next block).

 (b) Adjunction/GAFT.v applies a [Complete] to the DISCRETE category
 on the solution-set index ([DiscreteCat_Functor (wif_obj W)],
 Adjunction/GAFT.v), so the index universe of a solution set
 EQUALS the shape-object universe of the completeness hypothesis.
 Measured: [GAFT] carries [@Complete@{h h h cobj} C] beside
 [SolutionSet@{h dobj cobj h}], and [representability_theorem]
 carries [Complete@{h h h cobj}] beside [ElementSolutionSet@{cobj
 h su h}] -- the same [h] in the shape-object slot and in the
 index slot.  This is not an artifact of the formalisation: it is
 the constraint mathlib states as [HasLimitsOfSize.{w,w}] with
 [ι : Type w], and the 1lab as [is-complete ℓ ℓ] with
 [{index} : Type ℓ].

 (c) The equalizer of all endomorphisms of the product, taken in the
 same proof, forces that one shape-object universe to dominate the
 AMBIENT HOM universe as well (mathlib's [LocallySmall.{w}]); the
 mechanism is written out at Adjunction/GAFT.v's [GAFT] header.

 And the cap from the other side: [Sets_Complete@{u u0} :
 Complete@{u u u u0}] (Instance/Sets/Complete.v) puts the
 shape-object universe AT the carrier universe [u], because the limit
 carrier quantifies over the shape's objects and must itself be a
 carrier.  [Ab_Complete] and [RMod_Complete] inherit that shape through
 limit creation over [Sets].

 3. CONSEQUENCE, AND THE ROUTES THAT DO NOT ESCAPE IT.  A solution set
 indexed by a Σ over the OBJECTS of a concrete algebraic category --
 [SpanningArrowsOutOf] (Adjunction/SpanningArrow.v), a record over its
 carrier -- sits one universe above where 2(b) needs it; so does one
 indexed by [Type]-valued congruences, by 1.  Each of the following
 was compiled and refused, and none removes the gap: a universe lift
 of the category (the setoid-object records are non-cumulative);
 [Set Polymorphic Inductive Cumulativity] (it moves terms up, not
 types down); an SProp-valued `≈` (an SProp relation cannot inhabit
 [crelation] at all); a [Prop]-truncated kernel eliminated into a
 [Type]-sorted goal (refused even when `≈` is [eq], because the sort
 of [equiv x y] is judged from the declared type of [equiv] --
 Test/ProbePropEquiv.v); propositional resizing (the index is not
 an hProp, and the core is axiom-free); and an index-free "large
 completeness" ([RMod@{u}] has no object-indexed products at its own
 universe).  The surviving in-tree refusal is recorded verbatim in
 Instance/Mod/TensorAFT.v and pinned in Test/ProbeModTensorAFT449.v.

 SEPARATELY, and now HISTORY: until the PR "algebraic carriers are
 sets" (2026-09-17) a literal [Set] appeared in these signatures as
 well.  It was a universe-minimization artifact of the unannotated
 [DiscreteCat_Functor] (Instance/Discrete.v), not part of the size
 condition; annotating that donor removed every such [Set] and, as
 measured beforehand, left the refusals of this paragraph exactly
 where they were.  Prose quoting a [Set]-carrying signature predates
 that PR.

 4. THE RESOLUTION ADOPTED BY THIS PR.  Concrete algebraic categories
 (CMon, Ab, RMod, Grp, Rig/Rng) are categories of SETS with structure,
 and this library now says so in their object records: each carries
 [PropEquiv] (Lib/Setoid/Propositional.v), the property that the
 carrier's `≈` is logically a [Prop]-valued relation.  By 1 the
 congruences on a term model are then [Prop]-valued and carrier-sized,
 so they index a solution set at exactly the shape-object universe
 2(b)+(c) demands.  The consumers are Instance/Mod/TensorAFT.v (the
 tensor product of modules and the balanced maps),
 Instance/Rng/AFT.v (the free ring over Sets and over Ab) and
 Instance/Grp/FreeAFT.v (the free group), which obtain their objects
 from [representability_theorem] / [GAFT] with no hypothesis beyond
 the ring or the setoid.  Mac Lane's Lemma V.7.2 -- "the spanning
 codomains are quotients of the term module, hence a set" -- becomes
 [SmallUpToIso] of the spanning family (Adjunction/GAFT/Resize.v, with
 [SmallType] in Theory/Size.v), proved through the congruence index.

 WHAT IS IN TREE: all of it.  An earlier revision of this paragraph
 was headed "WHAT IS ALREADY IN TREE AS THIS BLOCK IS WRITTEN" and
 listed the [PropEquiv] class, its transports, Test/ProbePropEquiv.v
 and the universe hygiene of item 2, saying that "the object records
 of the algebraic categories, the unconditional tensor and free group,
 and [SmallUpToIso] land in later commits of the same PR" and that a
 reader who found one of those missing should read this item as the
 plan it was.  Those commits landed, and the item is now measured
 throughout rather than planned.  Concretely: the class and its
 elimination lemma are Lib/Setoid/Propositional.v, the
 transports through Sets and [LocallyPropositional] are
 Instance/Sets/Propositional.v; the object
 records carry the field at Instance/CMon.v ([cmon_prop], reaching
 Ab, RMod, Rg and their satellites by coercion),
 Theory/Algebra/Rig.v ([rig_prop], reaching Ring, Rng, CRng and
 Field) and Instance/Grp.v ([grp_prop]); hom-setoids inherit it
 pointwise and limit vertices from their legs, with no hypothesis on
 the limit ([alim_prop], [glim_prop], [rlim_prop]); the resizing
 vocabulary is Adjunction/GAFT/Resize.v with [SmallType] at
 Theory/Size.v; and the applications named above are
 unconditional, with Mac Lane's own spanning family proved small up
 to isomorphism at Instance/Mod/TensorAFT.v and fed to the
 theorem.  Every constant of that work is reported "Closed
 under the global context" and gated.

 WHAT IS STILL NOT IN TREE, so that this item is not read as more
 than it is: a solution set indexed by a Sigma over the OBJECTS of a
 concrete algebraic category remains refused, which is item 3 and is
 unchanged.  [tensor_esols_direct] is still refused as a direct
 premise (its index carries carrier < index where the congruence
 index carries carrier <= index); Mac Lane's own [Subgroup G]-indexed
 family for the free group is not built, the congruence index
 replacing it rather than resizing it; and [GAFT_from_spanning],
 although its hand-written [Set] annotation was deleted in the same
 PR, is still refused at [RMod R], the widened statement wanting
 objects at or below homs where [RMod R] has homs strictly below
 objects.  The one new side condition the resolution costs is
 [Set] < the carrier universe -- the sort of [Prop] reaching the
 index universe -- measured slot by slot against the conditional
 forms, costing nothing in practice and nothing at all at [Ab].

 ADDENDUM (#450).  Both lists in this item are longer now.  The
 categories whose object records carry the property include
 Instance/Variety/Free.v's setoid variety [SVariety E], for every
 operation signature and set of equations: its [SetoidOpAlgebra]
 record carries [soa_prop] since #450.  The consumers include three
 more files.  Instance/Grp/Colimit.v and Instance/Rng/Colimit.v apply
 [GAFT] at the diagonal functor of every shape with homs at the
 carrier universe and objects at or below it, with solution
 sets ([Diagonal_Grp_solution_set], [Diagonal_Rng_solution_set])
 indexed by [Prop]-valued cocone congruences on a term model, the
 kernel of a cocone being a [Prop] because its target carries
 [grp_prop] or [rig_prop]; they obtain [Grp_Cocomplete_via_GAFT] and
 [Rng_Cocomplete_via_GAFT].  Instance/Variety/Colimit.v does the same
 for [SVariety E] with two congruence-indexed solution sets,
 [Diagonal_SVariety_solution_set] at the diagonal and
 [SVariety_Forget_solution_set] at the forgetful functor, whose
 kernels are [Prop]s because the target carries [soa_prop]; they give
 [SVariety_Cocomplete_via_GAFT] and Mac Lane's free algebra
 [Free_Variety_via_GAFT].  The side condition is the same [Set] <
 carrier, and at [Grp], [Rng] and [SVariety E] it is measured to be
 [GAFT]'s: the three diagonal solution sets elaborate at [Set]
 carriers, and so does [GAFT] applied to every argument but the
 solution set, while [Grp_colim_via_GAFT], [Rng_colim_via_GAFT] and
 [SVariety_colim_via_GAFT] are refused there, [GAFT] putting the
 index AT the carrier universe and the index sitting strictly above
 [Set] (the UNIVERSES sections of Instance/Grp/Colimit.v and
 Instance/Rng/Colimit.v, and Test/ProbeAlgColimit450.v's N4 and N5
 and Test/ProbeVarietyColimit450.v's N4 with their controls).

 ADDENDUM (#454).  The consumers include a fourth file.
 Instance/Mod/Colimit.v applies [GAFT] at the diagonal functor into
 [RMod R], for every ring, with the solution set
 [Diagonal_RMod_solution_set] indexed by [Prop]-valued cocone
 congruences on Instance/Mod/Free.v's term model, the kernel of a
 cocone being a [Prop] because its target module carries
 [cmon_prop]; it obtains [RMod_Cocomplete_via_GAFT].  The side
 condition is again [Set] < carrier and again [GAFT]'s: in a copy of
 that file, at a ring whose carrier universe is [Set],
 [Diagonal_RMod_solution_set] elaborates and [RMod_colim_via_GAFT] is
 refused, "Cannot enforce Set = … because Set < …" (that file's
 UNIVERSES section, where the same refusal is quoted).

 SCOPE, because the property is deliberately narrow: [PropEquiv] is a
 property of a SETOID, not a change to [Class Setoid], and internal
 algebra in an arbitrary category (the Theory/Algebra/ files) keeps the
 ambient `≈` and carries no such field.  Nothing here makes `≈` propositional
 anywhere it was not already.
 --------------------------------------------------------------------- 

 --------
 ---------------------------------------------------------------------
 尺寸说明：解集、形状宇宙和命题等价。权威性内容；请引用它，而不是重述它。

 这是本库关于为什么伴随函子定理在具体代数范畴中难以应用的唯一说明，以及本库对此的处理方式。docs/INHABITATION.md 的前言包含了两个段落的呼应，并将此块命名为权威来源；Adjunction/GAFT.v、Adjunction/SpanningArrow.v、Instance/Mod/TensorAFT.v 和 Instance/Grp/FreeAFT.v 的标题引用了它，而不是重新推导运算。但它未涵盖 [Complete] 自己的四个宇宙绑定器：那些内容在下方的那个块中，并未在此重复。1. 关于大小算术的三行内容。 使用 [About] 在 [Set Printing Universes] 下进行测量；读取的值和两个拒绝在 Test/ProbePropEquiv.v 中固定：

 PropRelSpace@{u}   : Type@{u} → Type@{u}
 CRelSpace@{u v}    : Type@{u} → Type@{v}     u < v
 Setoid@{u u} A     : Type@{u+1}，比承载类型高一级

 一个 [Prop] 值的关系在 [Type@{u}] 中的承载上本身就是 [Type@{u}] 中的一个类型。一个 [Type] 值的则不是：在承载自身的层级（[CRelSpace_small]，Test/ProbePropEquiv.v: 310）上指定相同的空间会被拒绝，"项 'A → A → Type' 的类型为 'Type@{u+1}'，而期望类型为 'Type@{u}'".该库的 `≈` 是 [Type] 值类型 -- [equiv : crelation A]，
 Lib/Setoid.v -- 并保持如此，因为在 [Cat] 中，[F ≈ G] 是一个同构族（Theory/Functor.v, [Functor_Setoid]）：
 数据，其截断将被丢弃。结果：对于一个其 `≈` 为 [Type] 值类型的集合对象，其载体上的同余关系 -- 以及术语模型的商表示族，也就是 Mac Lane §V.7 的解集论证所产生的内容 -- 形成一个位于该载体之上的类型一宇宙。

 2. 伴随函子定理的约束链。三环节，每个都可测量。

 (a) [Complete] 保持其形状对象宇宙自由（下一块）。(b) Adjunction/GAFT.v 将一个 [Complete] 应用于解集索引上的离散类别 ([DiscreteCat_Functor (wif_obj W)], Adjunction/GAFT.v)，因此解集的索引宇宙等于完备性假设的形状对象宇宙。测量：[GAFT] 在 [SolutionSet@{h dobj cobj h}] 旁边携带 [@Complete@{h h h cobj} C]，并且 [representability_theorem] 在 [ElementSolutionSet@{cobj h su h}] 旁边携带 [Complete@{h h h cobj}] ——在形状对象槽和索引槽中是相同的 [h]。这不是形式化的产物：它是 mathlib 作为 [HasLimitsOfSize.{w,w}] 用 [ι : Type w] 表示的约束，并且 1lab 作为 [is-complete ℓ ℓ] 用 [{index} : Type ℓ] 表示。(c) 在相同证明中取积的所有自同态的等化器，会迫使一个形状对象宇宙也支配环境同调宇宙（mathlib 的 [LocallySmall.{w}]）；这个机制在 Adjunction/GAFT.v 的 [GAFT] 标题中写出。

 另一边的上确界：[Sets_Complete@{u u0} : Complete@{u u u u0}]（Instance/Sets/Complete.v）将形状对象宇宙放在承载宇宙 [u]，因为极限承载体量化形状的对象，并且自身必须是承载体。[Ab_Complete] 和 [RMod_Complete] 通过在 [Sets] 上创建极限继承该形状。3. 结果及无法逃避它的路径。由具体代数范畴的对象上的 Σ 索引的解集——[SpanningArrowsOutOf]（Adjunction/SpanningArrow.v），其载体上的记录——位于比 2(b) 需要的更高的一个宇宙；由 [Type] 值的同余类索引的解集也是如此，由 1 索引。以下每一项都已编译并被拒绝，并且都不能消除间隙：类别的宇宙提升（集合体对象记录是非累积的）；[Set Polymorphic Inductive Cumulativity]（它提升项，而不是降低类型）；一个SProp值的`≈`（一个SProp关系根本不能驻留在[crelation]）；一个[Prop]-截断内核被消除到[Type]排序的目标中（即便`≈`是[eq]也被拒绝，因为[equiv x y]的排序是根据[equiv]的已声明类型判断的——Test/ProbePropEquiv.v）；命题重置（索引不是hProp，并且核心是无公理的）；以及无索引的“大充分性”（[RMod@{u}]在其自身宇宙中没有对象索引的积）。存活的树内拒绝被逐字记录在 Instance/Mod/TensorAFT.v 中，并固定在 Test/ProbeModTensorAFT449.v 中。

 分开说，现在的历史：在 PR “代数载体是集合”（2026-09-17）之前，在这些签名中也出现了字面上的 [Set]。它是未注释的 [DiscreteCat_Functor]（Instance/Discrete.v）的宇宙最小化的产物，而不是大小条件的一部分；对该捐赠者进行注释后，移除了所有此类 [Set]，并且如之前测量的那样，本段落中的拒绝位置完全保持原样。引用带有 [Set] 的签名的文字早于该 PR。4. 本公告采用的决议。具体的代数范畴（CMon, Ab, RMod, Grp, Rig/Rng）是带结构的集合范畴，并且这个库现在在它们的对象记录中说明了这一点：每个对象都携带 [PropEquiv]（Lib/Setoid/Propositional.v），该属性说明载体的 `≈` 在逻辑上是一个 [Prop] 值的关系。根据 1，项模型上的同余于是 [Prop] 值且与载体大小相同，因此它们将解集索引到恰好符合 2(b)+(c) 要求的形状-对象宇宙。消费者是 Instance/Mod/TensorAFT.v（模的张量积和平衡映射）、Instance/Rng/AFT.v（集合和阿贝尔群上的自由环）以及 Instance/Grp/FreeAFT.v（自由群），它们从 [representability_theorem] / [GAFT] 获取对象，除了环或集合论外没有其他假设。Mac Lane 的引理 V.7.2——“生成的余域是项模的商，因此是一个集合”——变为 [SmallUpToIso] 的生成族（Adjunction/GAFT/Resize.v，在 Theory/Size.v 中有 [SmallType]），通过同余指数证明。树中有什么：全部。该段落的早期版本标题为“在编写此块时树中已有的内容”，列出了 [PropEquiv] 类及其传输、Test/ProbePropEquiv.v 以及第 2 项的宇宙卫生，并说明“代数类别的对象记录、无条件张量和自由群，以及 [SmallUpToIso] 会出现在同一 PR 的后续提交中”，并且发现这些内容缺失的读者应将该项视为计划。那些提交已经完成，现在该项是按实际情况衡量的，而非计划。具体来说：该类及其消除引理在 Lib/Setoid/Propositional.v，经过 Sets 和 [LocallyPropositional] 的传输在 Instance/Sets/Propositional.v；对象记录在 Instance/CMon.v（[cmon_prop]，通过强制转换到达 Ab、RMod、Rg 及其附属结构）、Theory/Algebra/Rig.v（[rig_prop]，到达 Ring、Rng、CRng 和 Field）以及 Instance/Grp.v（[grp_prop]）携带字段；同态集点逐点继承它，并从其分支继承极限顶点，对极限没有假设（[alim_prop]、[glim_prop]、[rlim_prop]）；重整词汇在 Adjunction/GAFT/Resize.v 中，[SmallType] 位于 Theory/Size.v；上述应用都是无条件的，Mac Lane 自身的生成家族被证明至同构小，在 Instance/Mod/TensorAFT.v 中应用并传递到定理。该工作的每个常量都被报告为“在全局上下文中封闭”并受到限制。仍然不在树中，因此该项不会被读作超出其本身的内容：由具体代数范畴的对象上的Sigma索引的解集仍然被拒绝，这是第3项，未发生变化。[tensor_esols_direct] 仍作为直接前提被拒绝（其索引携带的承载量 < 索引，其中同余索引携带的承载量 <= 索引）；Mac Lane 自身为自由群建立的 [Subgroup G] 索引族尚未构建，同余索引取而代之，而不是调整其大小；并且 [GAFT_from_spanning]，尽管其手写的 [Set] 注释在同一 PR 中已被删除，仍然在 [RMod R] 被拒绝，该扩展的声明希望在 homs 或以下的对象处存在，而 [RMod R] 的 homs 严格低于对象。解析成本的一个新的附加条件是
 [Set] < 承载宇宙 —— 类似于 [Prop] 到达索引宇宙 —— 按条件形式逐槽测量，实际上在 [Ab] 上完全不花费任何成本。附录 (#450)。本条目的两个列表现在都更长了。其对象记录带有该属性的类别包括 Instance/Variety/Free.v 的集合化种类 [SVariety E]，对于每个操作符号和方程集：其 [SetoidOpAlgebra] 记录自 #450 起携带 [soa_prop]。使用者包括另外三个文件。Instance/Grp/Colimit.v 和 Instance/Rng/Colimit.v 在每个形状的对角函子上应用 [GAFT]，形状的同态位于承载类型宇宙上，对象位于该宇宙上或其以下，并且有解集 ([Diagonal_Grp_solution_set], [Diagonal_Rng_solution_set])，由 [Prop] 值的余锥同余在项模型上索引，其余锥的核是 [Prop]，因为其目标携带 [grp_prop] 或 [rig_prop]；它们获得 [Grp_Cocomplete_via_GAFT] 和 [Rng_Cocomplete_via_GAFT]。Instance/Variety/Colimit.v 对 [SVariety E] 也做了同样的事情，它有两个同余索引的解集，[Diagonal_SVariety_solution_set] 在对角线上，[SVariety_Forget_solution_set] 在遗忘函子上，其核是 [Prop]，因为目标承载 [soa_prop]；它们给出了 [SVariety_Cocomplete_via_GAFT] 和 Mac Lane 的自由代数 [Free_Variety_via_GAFT]。附加条件是在相同的 [Set] 承载体上，并且在 [Grp]、[Rng] 和 [SVariety E] 上测量为 [GAFT]：三个对角解集在 [Set] 承载体上展开，[GAFT] 对每个参数（但解集除外）也这样适用，而 [Grp_colim_via_GAFT]、[Rng_colim_via_GAFT] 和 [SVariety_colim_via_GAFT] 在那里被拒绝，[GAFT] 将索引放在承载体宇宙上，并让索引严格高于 [Set]（Instance/Grp/Colimit.v 和 Instance/Rng/Colimit.v 的 UNIVERSES 部分，以及 Test/ProbeAlgColimit450.v 的 N4 和 N5、Test/ProbeVarietyColimit450.v 的 N4 及其控制）。附录 (#454)。消费者包括第四个文件。Instance/Mod/Colimit.v 对每一个环，在对角函子进入 [RMod R] 时应用 [GAFT]，其解集为由 [Prop]-值余锥索引的 [Diagonal_RMod_solution_set]。同余关系在 Instance/Mod/Free.v 的项模型上定义，余锥的核是 [Prop]，因为其目标模携带 [cmon_prop]；它获得 [RMod_Cocomplete_via_GAFT]。附加条件再次为 [Set] < 载体，并且再次为 [GAFT]：在该文件的一个副本中，在载体宇宙为 [Set] 的环上，[Diagonal_RMod_solution_set] 被展开并且 [RMod_colim_via_GAFT] 被拒绝，“无法强制 Set = … 因为 Set < …”（该文件的 UNIVERSES 部分，其中引用了相同的拒绝信息）。范围，因为该属性是故意设定为狭窄的：[PropEquiv] 是一个集合等价类（SETOID）的属性，而不是对 [Class Setoid] 的更改，并且任意范畴中的内部代数（Theory/Algebra/ 文件）保持了环境 `≈` 并且不带有这样的字段。这里没有任何内容会使 `≈` 在它原本不是的地方变为命题性的。
 ---------------------------------------------------------------------
*)

(*
 THE FOUR UNIVERSES, NAMED, BECAUSE DOWNSTREAM STATEMENTS TURN ON WHICH
 OF THEM IS WHICH.  Read in the declared order:

 [r]   the level of the resulting [Type] (the limit datum's own),
 [so]  the SHAPE's object universe -- the level at which diagram
 categories [D] may be indexed,
 [h]   the shape's AND the ambient's hom-and-proof universe: [Limit]
 identifies the two, where [Cone] keeps them apart, and that
 identification is inherited here rather than introduced,
 [o]   the AMBIENT category's object universe.

 The two declared constraints, [so <= r] and [h <= r], are [Limit]'s own
 and say only that the datum lives above the levels it quantifies over.
 NOTHING here relates [so] to [h] or to [o]: a complete category may be
 indexed by shapes at any level.  What ties them is the APPLICATION --
 Adjunction/GAFT.v applies a [Complete] at a discrete shape whose
 objects are a solution-set index, and Adjunction/GAFT.v's own binders
 record the identification that forces there.

 The measured readback is

 Complete@{r so h o} : Category@{o h h} → Type@{max(r,so+1,h+1,o)}
 ( * r so h o |= so <= r / h <= r * )

 -- and, since Instance/Discrete.v's [DiscreteCat_Functor] was
 annotated in the PR "algebraic carriers are sets" (2026-09-17), with no
 literal [Set] in it.  An earlier revision of this file's consumers
 quoted [Complete@{Set Set Set u}] and [Complete@{u0 u0 Set u2}]; those
 [Set]s were a universe-minimization artifact of that donor and are
 gone. 

 --------
 四个宇宙，其命名是因为下游语句取决于哪个是哪个。按声明顺序阅读：

 [r]    所得到的 [Type] 的层级（限制数据自身的），
 [so]   SHAPE 的对象宇宙——在该层级可以对图表类别 [D] 进行索引，
 [h]    形状以及环境的同类与证明宇宙：[Limit] 用于识别两者，而 [Cone] 将它们区分开，这种识别在此处继承而非引入，
 [o]    AMBIENT 类别的对象宇宙。两个声明的约束 [so <= r] 和 [h <= r] 是 [Limit] 自身的，并且仅说明该数据高于它所量化的层次。这里没有任何内容将 [so] 与 [h] 或 [o] 关联：一个完整的范畴可以由任何层次的形状索引。将它们联系起来的是应用——Adjunction/GAFT.v 在一个对象是解集索引的离散形状上应用 [Complete]，并且 Adjunction/GAFT.v 自身的绑定器记录了强制存在的识别。  

 测量的回读是  

 Complete@{r so h o} : Category@{o h h} → Type@{max(r,so+1,h+1,o)}  
 ( * r so h o |= so <= r / h <= r * )-- 并且，由于 Instance/Discrete.v 的 [DiscreteCat_Functor] 在 PR “代数载体是集合”（2026-09-17）中被注释掉，里面没有字面意义的 [Set]。该文件的早期修订版本的使用者引用了 [Complete@{Set Set Set u}] 和 [Complete@{u0 u0 Set u2}]；那些 [Set] 是该捐赠者的宇宙最小化产物，现在已经不存在了。
*)

(* C is complete: every diagram F : D ⟶ C has a limit (terminal cone) in C. / C 是完备的：每个图 F : D ⟶ C 在 C 中都有极限（终锥）。 *)
(*
   【Complete / Cocomplete 定义展开】/ Definition walkthrough（薄）

   1) 完备 = 对任意小图 F : D ⟶ C 都有极限（终锥）。
      Complete = has all (small) limits: ∀ D F, Limit F.
      余完备 Cocomplete = 有全部余极限 = Complete (C^op)。
      Cocomplete = all colimits = Complete of the opposite.

   2) 宇宙 / Universes
      r/so/h/o：极限证明宇宙、形状对象宇宙、hom 宇宙、环境对象宇宙；
      约束 so<=r、h<=r 继承自 Limit。
      Same universe package as Limit; so indexes diagram shapes.

   阅读：Cone → Limit → 本 ∀ 量化；「小」由图范畴 D 的宇宙体现。
   Read: Cone → Limit → this ∀; “small” = universe of shape D.
*)

Definition Complete@{r so h o | so <= r, h <= r} {C : Category@{o h h}} :=
  ∀ (D : Category@{so h h}) (F : D ⟶ C), Limit@{r so h o} F.

(* C is cocomplete: every diagram F : D ⟶ C has a colimit in C — the dual of completeness, equivalently completeness of C^op. Same four universes in the same order. / C 是共完备的：每个图 F : D ⟶ C 在 C 中都有余极限——是完备性的对偶，等价于 C^op 的完备性。同样的四个宇宙以相同的顺序。 *)
Definition Cocomplete@{r so h o | so <= r, h <= r} {C : Category@{o h h}} :=
  ∀ (D : Category@{so h h}) (F : D ⟶ C), Colimit@{r so h o} F.
