(* * * Complete semilattices are the algebras of the power-set monad / * * 完全半格是幂集单子代数 *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Monad.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(*
 Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 Springer GTM 5, 1998, §VI.2, Exercise 1(b), (c) and (d), printed
 p. 142 (PDF p. 151) — maclane:VI.2:ex1
 nLab: https://ncatlab.org/nlab/show/suplattice
 nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad

 In §VI.2 Mac Lane gives “several examples which show that the T-algebras
 for familiar monads are the familiar algebras” (printed p. 141), and the
 first exercise of the section, “Complete semi-lattices (E. Manes;
 thesis)”, adds one more.  From the page image: “Recall that a complete
 semi-lattice is a partial order Q in which every subset S ⊂ Q has a
 supremum (least upper bound) in Q.”  With ⟨𝒫, η, μ⟩ the covariant
 power-set monad of part (a): “(b) Prove that each 𝒫-algebra ⟨X, h⟩ is a
 complete semi-lattice when x ≦ y is defined by h{x, y} = y, and sup S =
 hS for each S ⊂ X.  (c) Prove conversely that every (small) complete
 semi-lattice is a 𝒫-algebra in this way.  (d) Conclude that the category
 of 𝒫-algebras is the category of all (small) complete semi-lattices, with
 morphisms the order and sup-preserving functions.”  These complete
 join-semilattices are nLab's suplattices.  The same section's other
 examples are in the tree as well: closure operators (#463,
 Instance/Proset/Monad.v), group actions (#464,
 Instance/Fun/Action/Monad.v) and modules (#465,
 Instance/Mod/TensorMonad.v).

 WHICH CONSTANT IS WHICH PART.  (a) is Instance/Sets/Powerset/Monad.v's
 [Powerset_Monad], on #227's endofunctor [Powerset_Prop].  (b) is
 [TAlgebra_SupLat]: the order is [talg_le], with [talg_le_iff] its reading
 as Mac Lane's h{x, y} ≈ y, and the sup IS h; the functor is
 [EM_to_SupLat].  (c) is [SupLat_TAlgebra]: the structure map IS the sup,
 and “in this way” is [sl_sup_pair_le], x ≤ y iff sup {x, y} ≈ y, so that
 (b) after (c) gives back the order ([sl_talg_le_iff]); the functor is
 [SupLat_to_EM].  (d) is [SupLat_EM_equivalence] and
 [SupLat_EM_iso : SupLat ≅[Cat] EilenbergMoore Powerset_Prop].

 THE ORDER IS THE JOIN ORDER.  Mac Lane's x ≤ y iff h{x, y} = y makes
 h{x, y} the least upper bound of x and y, so sup is a join, the bottom is
 sup ∅ and nothing here mentions meets.  The pair {x, y} is
 [Powerset_Prop_pair], the union of #227's two singletons (the tree had no
 two-element subset; Instance/Powerset.v's [subset_join] is a binary
 union).

 THE RECORD, ORDER FIRST.  [SupLatObject] is Mac Lane's definition: a
 setoid [sl_set], an order [sl_le] that is reflexive, transitive, respects
 ≈ and is antisymmetric into ≈, and a supremum [sl_sup] for every subset,
 stored as a setoid map out of #227's subsets ([sl_sup_ub],
 [sl_sup_least]).  The order has its own type, carrier → carrier → Prop: a
 record whose order is the standard library's [relation], with
 Instance/Proset/Limit.v's [IsLUB] or [HasAllJoins] over it, carries the
 global cap o <= Relation_Definition.u0 and two or four extra universe
 binders, one of them unused in each, the [IsLUB] record adding
 o <= Projections.u0 from the sigma type that indexes its family
 (measured by [About] on the scouts' two such records, in this tree), so
 none of the three is used.  The order is a [Prop] because #227's
 singletons are [Prop]-valued: the unit law needs sup {x} ≤ x from a
 squashed membership, and with a [Type]-valued order that elimination is
 refused on universes, a sort refusal (N10 of Test/ProbeSupLat466.v,
 UNIVERSE: “The term ”le z x“ has type ”Type“ while it is expected to
 have type ”Prop“ (universe inconsistency: Cannot enforce o <= Prop)”).
 The sup is a setoid map rather than a bare function, since with a bare
 function the round trip rebuilds its respect for ≈ and the structure map
 comes back only as a function (N9: the rebuilt map against [sl_sup A] is
 refused at [eq_refl], its function is accepted).  A morphism [SupLatHom] is
 a setoid map preserving sups ([slh_sup]); Mac Lane's “order and
 sup-preserving” asks for monotonicity too, and it is derived
 ([SupLatHom_monotone], through [sl_sup_pair_le]), so the two classes of
 maps are the same.  Two morphisms are equal when their maps agree pointwise
 up to ≈.

 WHAT “(SMALL)” BECOMES.  A small complete semilattice is a carrier in
 [SetoidObject@{o o}], an object of [Sets@{o so}], with a sup for EVERY
 ≈-respecting [Prop]-valued predicate on it.  By the impredicativity of
 [Prop] those predicates form a type at level o, so “every subset” is the
 whole power set at the carrier's own level and no restriction of size is
 imposed on the subsets, only on the carrier.  One consequence is proved
 in Instance/SupLat/Examples.v: a complete semilattice with a decidable ≈
 and two distinct comparable points x ≤ y decides ¬Q or ¬¬Q for every
 proposition Q ([suplat_two_points_WLEM]), informatively because the
 supremum is an operation, [sl_sup], and not a mere existence, so the
 chain false < true on bool is one only under that informative weak
 excluded middle, and the witnesses of non-vacuity there are the free
 ones, P X and Prop = P 1, not a finite chain.

 THE SQUASH IN (b), AND WHY IT IS INERT.  Morphism and element equality in
 this library is [Type]-valued, so Mac Lane's condition h{x, y} = y is
 read as the [Prop] [talg_le] := squash (h{x, y} ≈ y).  Every 𝒫-algebra
 undoes the squash ([talg_unsquash]): {x} ≈ {y} in P X is a [Prop] in
 content, h respects ≈, and h{x} ≈ x.  So [talg_le_iff] states Mac Lane's
 condition exactly, and every algebra's carrier has a propositional
 equality ([talg_PropEquiv]); so does every complete semilattice's, x ≈ y
 iff x ≤ y and y ≤ x ([sl_PropEquiv]).  Both are THEOREMS: no [PropEquiv]
 field or hypothesis is needed, where the algebraic records of
 Lib/Setoid/Propositional.v's regime (CMon, Grp and the rest) carry it as
 a field.

 WHY AN ISOMORPHISM IN CAT, AND NOT THE IDENTITY.  Mac Lane writes that
 the category of 𝒫-algebras “is the category” of complete semi-lattices.
 The tree delivers [SupLat_EM_iso], an isomorphism in [Cat], whose inverse
 laws hold up to natural isomorphism (an equivalence of categories), with
 identity components: its [to] leg IS [SupLat_to_EM] and its [from] leg IS
 [EM_to_SupLat], and every component of both of its natural isomorphisms,
 [iso_to_from] and [iso_from_to], is the identity map, to and from
 ([SupLat_EM_iso_to_from_component], [SupLat_EM_iso_from_to_component]
 and their [_from] twins), as is every component of the counit and the
 unit of [SupLat_EM_equivalence] ([SupLat_EM_counit_component],
 [SupLat_EM_unit_component] and their [_from] twins).  [SupLat_EM_iso] is
 built from the two component isomorphisms, not as Theory/Equivalence.v's
 [Equivalence_to_Cat_Iso] of the equivalence: that bridge takes
 [iso_from_to] to be the [symmetry] of the unit, which is
 Theory/Functor.v's [Functor_Setoid_obligation_1], opaque in this tree
 ([About]).  In a scratch file under this file's imports, the component
 of [iso_from_to (Equivalence_to_Cat_Iso SupLat_EM_equivalence)] at A is
 refused at [eq_refl] against the identity, (cannot unify “slh_map
 (projT1 (iso_from_to (Equivalence_to_Cat_Iso SupLat_EM_equivalence)) A)”
 and “setoid_morphism_id”), while that of its [iso_to_from] holds; in
 the probe's flip, where that obligation is transparent, both hold.
 Built directly, [SupLat_EM_iso] has the universe block it had as that
 bridge ([About] before and after, compared by [diff]).
 The round trips keep the carrier, the sup,
 the structure map and the maps of morphisms at [eq_refl]
 ([SupLat_EM_rt_carrier] and the five other round-trip readbacks listed
 under STRENGTHS), but not the semilattice's order, a data
 field that comes back only logically ([sl_talg_le_iff]); and an identity
 of categories is still not formable here, for two reasons, each pinned
 in Test/ProbeSupLat466.v.  First, the objects of
 Monad/Eilenberg/Moore.v's [EilenbergMoore] are [sigT] pairs, and [sigT]
 has no eta, so a variable algebra x is never convertible to the pair its
 round trip builds (N3); the two proof fields of the rebuilt algebra,
 [t_id] and [t_action], are new proofs as well (N4, N4b), so even at a
 named algebra α the algebra round trip is refused (N7).  Second, the
 round trip on semilattices rebuilds the order as the squash of sup {x, y}
 ≈ y, which is logically but not definitionally the order it started from
 (N2, hence N1); the morphism round trip is then not even well typed at
 [eq_refl] (N6), and neither composite is the identity functor (N5, N5b).
 None of these refusals is opacity: in the probe's flip, a copy of its
 one-hundred-module dependency closure with every [Qed] turned into
 [Defined], [Transparent Obligations] set and [abstract] made
 [transparent_abstract], save the exceptions the probe's header lists
 (three [Qed]s whose flip is itself refused, Instance/Sets.v's
 [setoid_morphism_compose_respects] among them, “Universe … is
 unbound”; Structure/Cartesian/Closed.v keeping its [Qed]s, with
 [Unset Transparent Obligations] added; Structure/Limit/Preservation.v's
 [preserves_colimit] written with [all:] steps; and two [abstract cat]
 steps of Construction/Elements.v kept as they are), each of them prints
 the error it prints in this tree and all of the probe's controls hold.

 A MEASURED ALTERNATIVE, NOT ADOPTED.  Variant L (the scouts' t5; the
 helpers [p466_SupLatObjectL] of the probe) adds to this record the two
 algebra laws of the sup, sup {x} ≈ x and the associativity of sups along
 the union, as redundant fields.  Its algebra round trip then holds at
 [eq_refl] on a whole algebra and on an object written (X; α)
 ([p466_L_alg_rt], [p466_L_obj_rt]), since [TAlgebra] is a record with
 eta; at a variable object it is refused all the same (N8, [sigT] again),
 its semilattice round trip still rebuilds the order as a squash (N8b),
 and the record is no longer Mac Lane's definition, part (c) moving into a
 smart constructor.  The order-first record is kept.

 STRENGTHS.  By [eq_refl]: the two legs of [SupLat_EM_iso]
 ([SupLat_EM_iso_to], [SupLat_EM_iso_from]); for (b), the carrier, the sup
 as the whole structure map h, and the order as the squash of h{a, b} ≈ b
 ([EM_to_SupLat_carrier], [EM_to_SupLat_sup], [EM_to_SupLat_le]); for (c),
 the carrier and the structure map as the whole sup
 ([SupLat_to_EM_carrier], [SupLat_to_EM_alg]); both functors on morphisms
 ([EM_to_SupLat_map], [SupLat_to_EM_map]); the round trips on carriers,
 structure maps, sups and morphisms ([SupLat_EM_rt_carrier],
 [SupLat_EM_rt_alg], [SupLat_EM_rt_set], [SupLat_EM_rt_sup],
 [SupLat_EM_rt_hom], [SupLat_EM_rt_alg_hom]); and the identity components,
 both ways, of both natural isomorphisms of [SupLat_EM_iso] and of the
 counit and unit of [SupLat_EM_equivalence].  Logically ([iffT] or
 [iff]): the order of an algebra against
 Mac Lane's condition ([talg_le_iff]), a semilattice's order against sup
 {x, y} ≈ y ([sl_sup_pair_le]) and against the order of its algebra
 ([sl_talg_le_iff]).  At ≈ only, as natural isomorphisms with identity
 components: the two composites against the identity functors.  Refused:
 the list of the previous two paragraphs.  The law proofs inside the
 [Defined] terms (the algebra laws of [SupLat_TAlgebra], the category
 and functor laws, the inverse laws of the two isomorphisms) are left
 inline rather than moved into [Qed] lemmas: no readback reads them, and
 the flip above, which makes every proof transparent, changes no refusal.

 UNIVERSES, read off [About].  The pair, the record, its projections, the
 morphisms, [sl_sup_pair_le], [SupLatHom_monotone] and [sl_PropEquiv] bind
 [@{o}] with the one bound [Set < o], first carried by
 Instance/Sets/Powerset.v's [Powerset_Prop_truth_equiv];
 [SupLatObject@{o} : Type@{o+1}].  [SupLat_id] and [SupLat_compose] add
 the caps ID and compose of Instance/Sets.v's [setoid_morphism_id] and
 [setoid_morphism_compose].  [SupLat@{o so} : Category@{so o o}] has the
 block of [Sets@{o so}] with [Set < o] added.  Every constant that names
 the monad binds [@{o so}] with [Powerset_Monad]'s block; those that name
 [EilenbergMoore] add [o <= Projections.u1] and [so <= Projections.u0],
 its [sigT] projections, and the eight component readbacks also
 [o <= Projections.u0] and [so <= Projections.u1], from the [projT1] of a
 natural isomorphism in their statements.  [SupLat_EM_iso], its two leg
 readbacks and the four component readbacks that name it bind
 [@{o so c}] and add [o < c] and [so < c], from Instance/Cat.v's
 [Cat@{c so so so o}].  The statements with a [Type] side
 use [iffT@{o o}], Lib/Foundation.v's ↔ with its two universes named,
 which keeps them at [@{o}] and [@{o so}] with no phantom level.  A
 [simpl] in the naturality proofs of [SupLat_EM_equivalence] added the
 strict bound [o < Projections.u0] (implied by o < so and so <=
 Projections.u0); it was removed and the bound is gone.  There is no
 equation.

 NOT DELIVERED.  The strict identity of the two categories, for the
 reasons above.  The free complete semilattice, the adjunction behind the
 monad and the monadicity of the forgetful functor are
 Instance/SupLat/Free.v; its examples, and the two-point theorem, are
 Instance/SupLat/Examples.v.  Meets are not built: that every complete
 join-semilattice is a complete lattice, and that a sup-preserving map has
 a right adjoint, are not proved here.  Finite or bounded semilattices,
 and frames, are not built. 

 --------
 书籍：Mac Lane，《为在职数学家准备的范畴论》，第2版，施普林格 GTM 5，1998年，第VI.2节，练习题1(b)、(c)和(d)，印刷页142（PDF页151）—— maclane:VI.2:ex1
 nLab: https://ncatlab.org/nlab/show/suplattice
 nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad在 §VI.2 中，Mac Lane 给出了“几例显示熟悉的单子 T-代数是熟悉的代数”（印刷页 141），以及本节的第一个练习题，“完备半格（E. Manes；论文）”，又增加了一个例子。从页面图像来看：“回忆一下，完备半格是一个偏序集 Q，其中每个子集 S ⊂ Q 在 Q 中都有上确界（最小上界）。” 对于部分 (a) 的协变幂集单子 ⟨𝒫, η, μ⟩：“(b) 证明每个 𝒫-代数 ⟨X, h⟩ 是一个完备半格，当 x ≦ y 由 h{x, y} = y 定义，并且对于每个 S ⊂ X, sup S = hS。(c) 反过来证明，每个（小的）完备半格都是这样构造的 𝒫-代数。(d) 得出结论：𝒫-代数的范畴是所有（小）完全半格的范畴，态射为保持序和上确界的函数。这些完全的上联半格是 nLab 所说的上格。同一章节的其他例子也在树中：闭包算子（#463，Instance/Proset/Monad.v）、群作用（#464，Instance/Fun/Action/Monad.v）和模（#465，Instance/Mod/TensorMonad.v）。哪个常量对应哪个部分。(a) 是 Instance/Sets/Powerset/Monad.v 的 [Powerset_Monad]，在 #227 的自函子 [Powerset_Prop] 上。(b) 是 [TAlgebra_SupLat]：顺序是 [talg_le]，它的读法 [talg_le_iff] 作为 Mac Lane 的 h{x, y} ≈ y，sup 是 h；函子是 [EM_to_SupLat]。(c) 是 [SupLat_TAlgebra]：结构映射是 sup，而“以这种方式”是 [sl_sup_pair_le]，x ≤ y 当且仅当 sup {x, y} ≈ y，因此 (c) 后的 (b) 给出了顺序 ([sl_talg_le_iff])；函子是 [SupLat_to_EM]。(d) 是 [SupLat_EM_equivalence] 和 [SupLat_EM_iso : SupLat ≅[Cat]  EilenbergMoore Powerset_Prop].该顺序是并运算顺序。Mac Lane 的 x ≤ y 当且仅当 h{x, y} = y，这使得 h{x, y} 成为 x 和 y 的最小上界，因此 sup 是一个并运算，底元素是 sup ∅，此处没有提到交运算。对 {x, y} 的处理是 [Powerset_Prop_pair]，是 #227 两个单元素集合的并集（树中没有二元素子集；Instance/Powerset.v 中的 [subset_join] 是二元并运算）。记录，首先是顺序。[SupLatObject] 是 Mac Lane 的定义：一个集合类 [sl_set]，一个顺序 [sl_le]，它是自反的、传递的、尊重 ≈ 并且在 ≈ 上是反对称的，以及每个子集的上确界 [sl_sup]，以集合类映射的形式存储，来自 #227 的子集（[sl_sup_ub], [sl_sup_least]）。该顺序有其自身的类型，载体 → 载体 → 命题：一个记录，其顺序是标准库的 [relation]，带有 Instance/Proset/Limit.v 的 [IsLUB] 或 [HasAllJoins]，包含全局上界 o <= Relation_Definition.u0 和两个或四个额外的宇宙绑定器，其中每个绑定器中有一个未使用，[IsLUB] 记录从索引其族的 sigma 类型添加了 o <= Projections.u0（通过 [About] 测量，在该树的两个此类记录的侦察中），因此这三者中没有一个被使用。该顺序是一个 [Prop]，因为 #227 的单元素是 [Prop] 值的：单元律需要从压缩的成员关系中得到 sup {x} ≤ x，并且对于 [Type] 值的顺序，在宇宙上拒绝消去，这是一个类型拒绝（Test/ProbeSupLat466.v 的 N10，宇宙：“术语 'le z x' 的类型为 'Type'，而期望类型为 'Prop'（宇宙不一致：无法强制 o <= Prop）”）。sup 是一个集合等价映射，而不是裸函数，因为用裸函数时，往返重建会维持其对 ≈ 的尊重，而结构映射只会以函数形式返回（N9：重建的映射对 [sl_sup A] 在 [eq_refl] 被拒绝，但其函数形式被接受）。一个态射 [SupLatHom] 是一个保持上确界的集合映射 ([slh_sup])；Mac Lane 的“顺序和上确界保持”还要求单调性，并且它是可以推导的 ([SupLatHom_monotone]，通过 [sl_sup_pair_le])，所以这两类映射是相同的。当两个态射的映射在每个点上都一致（至≈为止）时，它们相等。“小型”变成什么。一个小型完全半格是在 [SetoidObject@{o o}] 中的载体，是 [Sets@{o so}] 的一个对象，对于每一个 ≈-保持的 [Prop] 值谓词，它都有一个上界。由于 [Prop] 的自反性，这些谓词在层级 o 上形成一个类型，因此“每一个子集”就是载体自身层级的整个幂集，对子集没有大小限制，仅对载体有限制。一个结论在 Instance/SupLat/Examples.v 中被证明：一个具有可判定 ≈ 的完全半格以及两个不同的可比较点 x ≤ y 可以决定每一个命题 Q 的 ¬Q 或 ¬¬Q（[suplat_two_points_WLEM]），信息性地，因为上确界是一个运算，[sl_sup]，而不仅仅是存在，因此 bool 上的链 false < true 在这种信息性弱排中律下是唯一的，并且那里的非空见证是自由的，即 P X 和 Prop = P 1，而不是有限链。（b）中的 squash，以及它为何是惰性的。在这个库中，态射和元素的相等性是 [Type] 值的，因此 Mac Lane 的条件 h{x, y} = y 被读作 [Prop] [talg_le] := squash (h{x, y} ≈ y)。每个 𝒫-代数都撤销 squash（[talg_unsquash]）：在 P X 中 {x} ≈ {y} 在内容上是 [Prop]，h 尊重 ≈，且 h{x} ≈ x。因此 [talg_le_iff] 精确陈述了 Mac Lane 的条件，并且每个代数的载体都有一个命题相等（[talg_PropEquiv]）；每个完全半格的也有，x ≈ y 当且仅当 x ≤ y 且 y ≤ x（[sl_PropEquiv]）。两者都是定理：不需要 [PropEquiv] 字段或假设，其中 Lib/Setoid/Propositional.v 的代数记录（CMon、Grp 及其余部分）将其作为一个字段承载。为什么在范畴论中使用同构，而不是恒等映射。Mac Lane 写道 𝒫-代数的范畴“就是”完全半格的范畴。该树提供了 [SupLat_EM_iso]，一个 [Cat] 中的同构，其逆律在自然同构（范畴等价）下成立，其恒等组成部分为：其 [to] 分支是 [SupLat_to_EM]，ZYW55WZZ 分支是 [EM_to_SupLat]，并且其两个自然同构 [iso_to_from] 和 [iso_from_to] 的每个组成部分都是恒等映射，来回作用于 ([SupLat_EM_iso_to_from_component], [SupLat_EM_iso_from_to_component] 及其 [_from] 对应项)，正如 [SupLat_EM_equivalence] 的余单元和单元的每个组成部分 ([SupLat_EM_counit_component], [SupLat_EM_unit_component] 及其 [_from] 对应项) 一样。[SupLat_EM_iso] 是由两个组件同构构建的，而不是像 Theory/Equivalence.v 的 [Equivalence_to_Cat_Iso] 那样通过等价构建的：该桥接将 [iso_from_to] 视为单位的 [symmetry]，这就是 Theory/Functor.v 的 [Functor_Setoid_obligation_1]，在此树 ([About]) 中是不透明的。在该文件导入的一个临时文件中，[iso_from_to (Equivalence_to_Cat_Iso SupLat_EM_equivalence)] 在 A 处的组件被 [eq_refl] 拒绝与单位对齐（无法统一 “slh_map (projT1 (iso_from_to (Equivalence_to_Cat_Iso SupLat_EM_equivalence)) A)” 与 “setoid_morphism_id”），而其 [iso_to_from] 的组件则成立；在探针的翻转中，该义务变为透明，两者都成立。直接构建时，[SupLat_EM_iso] 拥有它作为桥接时的宇宙屏障 ([About] 前后，通过 [diff] 进行比较) 。往返操作会保留载体、sup、结构映射以及在 [eq_refl] 的态射映射（[SupLat_EM_rt_carrier] 以及在 STRENGTHS 下列出的其他五个往返读回），但不会保留半格的顺序，这是一个只有逻辑上才会返回的数据字段（[sl_talg_le_iff]）；并且这里仍然无法形成范畴的恒等式，原因有两个，都记录在 Test/ProbeSupLat466.v 中。首先，Monad/Eilenberg/Moore.v 的 [EilenbergMoore] 的对象是 [sigT] 对，而 [sigT] 没有 eta，因此变量代数 x 永远无法转换为它的往返操作构建的对（N3）；重建代数的两个证明字段 [t_id] 和 [t_action] 也是新的证明（N4, N4b），因此即使在命名代数 α 上，代数的往返操作也会被拒绝（N7）。其次，半格上的往返重建了顺序，如 sup {x, y} 的压缩 ≈ y，从逻辑上但不是定义上仍然是它最初的顺序 (N2，因此 N1)；然后，在 [eq_refl] (N6) 上，态射的往返甚至不是良类型的，并且两个复合都不是恒等函子 (N5, N5b)。这些拒绝都不是不透明的：在探针的翻转中，其一百模块的依赖闭包的副本中，每个 [Qed] 都变成了 [Defined]，[Transparent Obligations] 被设置，[abstract] 变成 [transparent_abstract]，除非探针的头文件列出的例外（三个 [Qed] 本身的翻转被拒绝，Instance/Sets.v 中的 [setoid_morphism_compose_respects] 在其中，“Universe … 未绑定”；Structure/Cartesian/Closed.v 保留其 [Qed]，添加了 [Unset Transparent Obligations]；Structure/Limit/Preservation.v 的 [preserves_colimit] 通过 [all:] 步骤写入；Construction/Elements.v 的两个 [abstract cat] 步骤保持不变），它们中的每一个在此树中打印它打印的错误，并且探针的所有控件都保持有效。一种经过衡量的替代方案，未被采纳。变体 L（侦察者的 t5；探测器的助手 [p466_SupLatObjectL]）在该记录中增加了两个代数律——sup 的代数律，sup {x} ≈ x 以及沿并集的 sup 的结合律，作为冗余字段。于是其代数往返验证随后在 [eq_refl] 上对整个代数和写作 (X; α)（[p466_L_alg_rt], [p466_L_obj_rt]）的对象成立，因为 [TAlgebra] 是一个带有 eta 的记录；在变量对象上，它同样被拒绝 (N8, [sigT] 再次)，其半格往返仍然以压缩形式重建顺序 (N8b)，并且该记录不再是 Mac Lane 的定义，部分 (c) 被移入智能构造函数。保持了以顺序为先的记录。优势。由 [eq_refl]：[SupLat_EM_iso] 的两条腿（[SupLat_EM_iso_to]，[SupLat_EM_iso_from]）；对于 (b)，承载者、sup 作为整体结构映射 h，以及顺序作为 h{a, b} ≈ b 的压缩（[EM_to_SupLat_carrier]，[EM_to_SupLat_sup]，[EM_to_SupLat_le]）；对于 (c)，承载者和结构映射作为整体 sup（[SupLat_to_EM_carrier]，[SupLat_to_EM_alg]）；两个函子在态射上的作用（[EM_to_SupLat_map]，[SupLat_to_EM_map]）；承载者、结构映射、sup 和态射上的往返（[SupLat_EM_rt_carrier]，[SupLat_EM_rt_alg]，[SupLat_EM_rt_set]，[SupLat_EM_rt_sup]，[SupLat_EM_rt_hom]，[SupLat_EM_rt_alg_hom]）；以及 [SupLat_EM_iso] 的两个自然同构的两个方向的同一性分量，以及 [SupLat_EM_equivalence] 的余单位和单位。逻辑上（[iffT] 或 [iff]）：一个代数关于 Mac Lane 条件（[talg_le_iff]）的顺序，一个半格的顺序关于 sup {x, y} ≈ y（[sl_sup_pair_le]）以及关于其代数的顺序（[sl_talg_le_iff]）。仅在 ≈ 时，作为具有恒等分量的自然同构：两个复合映射关于恒等函子。拒绝：前两段的列表。[Defined] 项中的定律证明（[SupLat_TAlgebra] 的代数定律、范畴和函子定律、两个同构的逆定律）保持在行内而不是移到 [Qed] 引理中：没有回读会读取它们，上述翻转使每个证明透明，但不改变任何拒绝内容。宇宙，读出 [About]。该对，记录，其投影，态射，[sl_sup_pair_le]、[SupLatHom_monotone] 和 [sl_PropEquiv] 将 [@{o}] 与已经绑定的 [Set < o] 绑定，首次由 Instance/Sets/Powerset.v 的 [Powerset_Prop_truth_equiv] 承载；[SupLatObject@{o} : Type@{o+1}]、[SupLat_id] 和 [SupLat_compose] 添加了帽 ID 并组成了 Instance/Sets.v 的 [setoid_morphism_id] 和 [setoid_morphism_compose]。[SupLat@{o so} : Category@{so o o}] 具有 [Sets@{o so}] 的块，并添加了 [Set < o]。每个命名单子（monad）的常量将 [@{o so}] 与 [Powerset_Monad] 的块绑定；那些命名 [EilenbergMoore] 的添加了 [o <= Projections.u1] 和 [so <= Projections.u0]，其 [sigT] 投影，以及八个组件回读 also [o <= Projections.u0] 和 [so <= Projections.u1]，来自自然同构在其陈述中的 [projT1]。[SupLat_EM_iso]，它的两个支脚回读以及命名它的四个组件回读绑定 [@{o so c}] 并添加 [o < c] 和 [so < c]，来自 Instance/Cat.v 的 [Cat@{c so so so o}]。带有 [Type] 一侧的语句使用 [iffT@{o o}]，Lib/Foundation.v 的 ↔ 及其两个命名的宇宙，它们保持在 [@{o}] 和 [@{o so}] 上，没有虚拟等级。在 [SupLat_EM_equivalence] 的自然性证明中，[simpl] 添加了严格的边界 [o < Projections.u0]（由 o < so 和 so <= Projections.u0 推断）；它已被移除且边界消失。没有方程。未交付。出于上述原因，这两类的严格同一性。自由完全半格、单子背后的伴随和忘记函子的单子性都在 Instance/SupLat/Free.v；其示例以及两点定理在 Instance/SupLat/Examples.v。并未构建交：每个完全加半格都是完全格，加保持映射有右伴随，也未在此证明。有限或有界半格以及框架未被构建。
*)

(* ------------------------------------------------------------------------ *)
(** ** The two-element subset {x, y} / ** 两元素子集 {x, y} *)

(* The subset {x, y} of a setoid, as the union of #227's two truncated singletons. / 集合格的子集 {x, y}，作为 #227 的两个截断单集的并集。 *)
Definition Powerset_Prop_pair@{o} {X : SetoidObject@{o o}}
  (x y : carrier X) : carrier (Powerset_Prop_obj@{o} X).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier X) (is_setoid X) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ z, Powerset_squash@{o} (@equiv _ (is_setoid X) x z)
             \/ Powerset_squash@{o} (@equiv _ (is_setoid X) y z)) _).
  intros z z' E; split; intros [H|H]; [left|right|left|right];
    intros Q k; apply H; intro e; apply k.
  - now transitivity z.
  - now transitivity z.
  - transitivity z'; [exact e | now symmetry].
  - transitivity z'; [exact e | now symmetry].
Defined.

Lemma Powerset_Prop_pair_respects@{o} {X : SetoidObject@{o o}}
  (x x' y y' : carrier X)
  (Ex : @equiv _ (is_setoid X) x x') (Ey : @equiv _ (is_setoid X) y y') :
  Powerset_Prop_pair@{o} x y ≈ Powerset_Prop_pair@{o} x' y'.
Proof.
  intro z; split; intros [H|H]; [left|right|left|right];
    intros Q k; apply H; intro e; apply k.
  - transitivity x; [now symmetry | exact e].
  - transitivity y; [now symmetry | exact e].
  - transitivity x'; [exact Ex | exact e].
  - transitivity y'; [exact Ey | exact e].
Qed.

Lemma Powerset_Prop_pair_comm@{o} {X : SetoidObject@{o o}}
  (x y : carrier X) :
  Powerset_Prop_pair@{o} x y ≈ Powerset_Prop_pair@{o} y x.
Proof.
  intro z; split; intros [H|H]; [right|left|right|left]; exact H.
Qed.

(* A singleton {x} lies inside every subset that contains x. / 每个包含 x 的子集中都包含一个单元素 {x}。 *)
Lemma Powerset_Prop_singleton_sub@{o} {X : SetoidObject@{o o}}
  (x : carrier X) (S : carrier (Powerset_Prop_obj@{o} X)) (Hx : S x) :
  ∀ z, Powerset_Prop_singleton_pred@{o} x z → S z.
Proof.
  intros z Hz; apply Hz; intro e.
  exact (proj1 (proper_morphism S x z e) Hx).
Qed.

(* ⋃ {S, T} ≈ T when S ⊆ T. / 当 S ⊆ T 时，⋃ {S, T} ≈ T。 *)
Lemma Powerset_union_pair_sub@{o} {X : SetoidObject@{o o}}
  (S T : carrier (Powerset_Prop_obj@{o} X)) (HST : ∀ z, S z → T z) :
  Powerset_union_pred@{o} (Powerset_Prop_pair@{o} S T) ≈ T.
Proof.
  intro z; split.
  - intros [U [[HU|HU] Hz]]; apply HU; intro e.
    + apply HST. exact (proj2 (e z) Hz).
    + exact (proj2 (e z) Hz).
  - intro Hz. exists T; split; [ right | exact Hz ].
    apply Powerset_squash_intro; reflexivity.
Qed.

(* The family {{x, y} | x ∈ S} ∪ {{y}}, whose union is S ∪ {y}. / 这个族 {{x, y} | x ∈ S} ∪ {{y}}，其并集是 S ∪ {y}。 *)
Definition Powerset_Prop_least_family@{o} {X : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} X)) (y : carrier X) :
  carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X)).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier (Powerset_Prop_obj@{o} X))
       (is_setoid (Powerset_Prop_obj@{o} X))
       Prop (is_setoid Powerset_Prop_truth@{o})
       (λ U, Powerset_squash@{o}
               (∃ x, S x ∧ @equiv _ (is_setoid (Powerset_Prop_obj@{o} X))
                             (Powerset_Prop_pair@{o} x y) U)
             \/ Powerset_squash@{o}
                  (@equiv _ (is_setoid (Powerset_Prop_obj@{o} X))
                     (Powerset_Prop_singleton_pred@{o} y) U)) _).
  intros U U' E; split; intros [H|H]; [left|right|left|right];
    intros Q k; apply H.
  - intros [x [Hx e]]; apply k; exists x; split; [exact Hx | ].
    now transitivity U.
  - intro e; apply k; now transitivity U.
  - intros [x [Hx e]]; apply k; exists x; split; [exact Hx | ].
    transitivity U'; [exact e | now symmetry].
  - intro e; apply k; transitivity U'; [exact e | now symmetry].
Defined.

(* ------------------------------------------------------------------------ *)
(** ** Complete semilattices / ** 完全半格 *)

(*
 Mac Lane's definition, order first: a partial order in which every
 subset has a supremum.  The order is [Prop]-valued, antisymmetry lands
 in the carrier's ≈, and the supremum is a setoid map out of #227's
 subsets. 

 --------
 Mac Lane 的定义，先讨论顺序：一个偏序，其中每个子集都有一个上确界。该顺序的取值为 [Prop]，反对称性映射到载体的 ≈，且上确界是 #227 的子集的集合同态映射。
*)
Record SupLatObject@{o} := {
  sl_set : SetoidObject@{o o};
  sl_le : carrier sl_set → carrier sl_set → Prop;
  sl_le_refl x : sl_le x x;
  sl_le_trans x y z : sl_le x y → sl_le y z → sl_le x z;
  sl_le_respects x x' y y' :
    @equiv _ (is_setoid sl_set) x x' → @equiv _ (is_setoid sl_set) y y' →
    sl_le x y → sl_le x' y';
  sl_antisym x y :
    sl_le x y → sl_le y x → @equiv _ (is_setoid sl_set) x y;
  sl_sup : SetoidMorphism@{o o o} (Powerset_Prop_obj@{o} sl_set) sl_set;
  sl_sup_ub (S : carrier (Powerset_Prop_obj@{o} sl_set)) x :
    S x → sl_le x (sl_sup S);
  sl_sup_least (S : carrier (Powerset_Prop_obj@{o} sl_set)) y :
    (∀ x, S x → sl_le x y) → sl_le (sl_sup S) y
}.

(*
 A morphism preserves sups; monotonicity is derived below
 ([SupLatHom_monotone]). 

 --------
 一个同态保持上确界；单调性将在下面推导出 ( [SupLatHom_monotone] )。
*)
Record SupLatHom@{o} (A B : SupLatObject@{o}) := {
  slh_map : SetoidMorphism@{o o o} (sl_set A) (sl_set B);
  slh_sup (S : carrier (Powerset_Prop_obj@{o} (sl_set A))) :
    @equiv _ (is_setoid (sl_set B))
      (slh_map (sl_sup A S))
      (sl_sup B (Powerset_Prop_image@{o} slh_map S))
}.

Arguments slh_map {A B} _.
Arguments slh_sup {A B} _ _.

Definition SupLatHom_Setoid@{o} (A B : SupLatObject@{o}) :
  Setoid@{o o} (SupLatHom@{o} A B).
Proof.
  unshelve refine
    (@Build_Setoid@{o o} (SupLatHom@{o} A B)
       (λ f g, @equiv _ (@SetoidMorphism_Setoid@{o o o} (sl_set A) (sl_set B))
                 (slh_map f) (slh_map g)) _).
  constructor.
  - intros f; reflexivity.
  - intros f g H; now symmetry.
  - intros f g h H1 H2; now transitivity (slh_map g).
Defined.

Definition SupLat_id@{o} (A : SupLatObject@{o}) : SupLatHom@{o} A A.
Proof.
  unshelve refine
    (@Build_SupLatHom@{o} A A (@setoid_morphism_id@{o o o} (sl_set A)) _).
  intro S. apply (proper_morphism (sl_sup A)).
  symmetry. exact (@Powerset_Prop_map_id@{o} (sl_set A) S).
Defined.

Definition SupLat_compose@{o} {A B C : SupLatObject@{o}}
  (g : SupLatHom@{o} B C) (f : SupLatHom@{o} A B) : SupLatHom@{o} A C.
Proof.
  unshelve refine
    (@Build_SupLatHom@{o} A C
       (@setoid_morphism_compose@{o o o} _ _ _ (slh_map g) (slh_map f)) _).
  intro S. simpl.
  transitivity (slh_map g (sl_sup B (Powerset_Prop_image@{o} (slh_map f) S))).
  { apply proper_morphism. exact (slh_sup f S). }
  transitivity (sl_sup C (Powerset_Prop_image@{o} (slh_map g)
                            (Powerset_Prop_image@{o} (slh_map f) S))).
  { exact (slh_sup g _). }
  apply (proper_morphism (sl_sup C)). symmetry.
  exact (@Powerset_Prop_map_comp@{o} _ _ _ (slh_map g) (slh_map f) S).
Defined.

(*
 The category of (small) complete semilattices.  It sits at the same
 universes as [Sets@{o so}]. 

 --------
 (小) 完全半格的范畴。 它位于与 [Sets@{o so}] 相同的宇宙中。
*)
Definition SupLat@{o so} : Category@{so o o}.
Proof.
  unshelve refine
    (@Build_Category@{so o o}
       (SupLatObject@{o} : Type@{so})
       (λ A B, SupLatHom@{o} A B : Type@{o})
       SupLatHom_Setoid@{o} SupLat_id@{o} (@SupLat_compose@{o}) _ _ _ _ _).
  - intros A B C f f' Hf g g' Hg a; simpl.
    transitivity (slh_map f (slh_map g' a)).
    + apply proper_morphism, Hg.
    + apply Hf.
  - intros A B f a; reflexivity.
  - intros A B f a; reflexivity.
  - intros A B C D f g h a; reflexivity.
  - intros A B C D f g h a; reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(* * ** The order recovered from the sup / * ** 从 sup 中恢复的订单 *)

(* x ≤ y exactly when sup {x, y} ≈ y: part (c)'s “in this way”. / 当且仅当 sup {x, y} ≈ y 时，x ≤ y：部分 (c) 的“用这种方式” *)
Lemma sl_sup_pair_le@{o} (A : SupLatObject@{o}) (x y : carrier (sl_set A)) :
  iffT@{o o} (sl_le A x y)
    (@equiv _ (is_setoid (sl_set A)) (sl_sup A (Powerset_Prop_pair@{o} x y)) y).
Proof.
  split.
  - intro H. apply sl_antisym.
    + apply sl_sup_least. intros z [Hz|Hz]; apply Hz; intro e.
      * exact (sl_le_respects A x z y y e (reflexivity y) H).
      * exact (sl_le_respects A y z y y e (reflexivity y) (sl_le_refl A y)).
    + apply sl_sup_ub. right. apply Powerset_squash_intro. reflexivity.
  - intro E. apply (sl_le_respects A x x _ y (reflexivity x) E).
    apply sl_sup_ub. left. apply Powerset_squash_intro. reflexivity.
Qed.

(* A sup-preserving map is monotone. / 保持上确界的映射是单调的。 *)
Lemma SupLatHom_monotone@{o} {A B : SupLatObject@{o}}
  (f : SupLatHom@{o} A B) (x y : carrier (sl_set A)) :
  sl_le A x y → sl_le B (slh_map f x) (slh_map f y).
Proof.
  intro H.
  destruct (sl_sup_pair_le A x y) as [HA _].
  destruct (sl_sup_pair_le B (slh_map f x) (slh_map f y)) as [_ HB].
  apply HB. pose proof (HA H) as E.
  transitivity (slh_map f (sl_sup A (Powerset_Prop_pair@{o} x y))).
  - symmetry.
    transitivity (sl_sup B (Powerset_Prop_image@{o} (slh_map f)
                              (Powerset_Prop_pair@{o} x y))).
    + exact (slh_sup f _).
    + apply (proper_morphism (sl_sup B)). intro z; split.
      * intro Hz; apply Hz; intros [w [[Hw|Hw] Ew]];
          [left|right]; intros Q k; apply Hw; intro e; apply k;
          (transitivity (slh_map f w);
             [apply proper_morphism; exact e | exact Ew]).
      * intros [Hz|Hz]; apply Hz; intro e; intros Q k; apply k.
        -- exists x; split; [ left | exact e ].
           apply Powerset_squash_intro; reflexivity.
        -- exists y; split; [ right | exact e ].
           apply Powerset_squash_intro; reflexivity.
  - apply proper_morphism. exact E.
Qed.

(*
 A complete semilattice's carrier has a propositional equality: x ≈ y
 holds exactly when x ≤ y and y ≤ x. 

 --------
 一个完全半格的承载集合具有命题等式：x ≈ y 当且仅当 x ≤ y 且 y ≤ x 成立。
*)
Definition sl_PropEquiv@{o} (A : SupLatObject@{o}) :
  PropEquiv@{o o} (is_setoid (sl_set A)).
Proof.
  unshelve refine
    (@Build_PropEquiv@{o o} _ (is_setoid (sl_set A))
       (fun x y => sl_le A x y /\ sl_le A y x) _ _).
  - intros x y [H1 H2]. exact (sl_antisym A x y H1 H2).
  - intros x y E. split.
    + exact (sl_le_respects A x x x y (reflexivity x) E (sl_le_refl A x)).
    + exact (sl_le_respects A x y x x E (reflexivity x) (sl_le_refl A x)).
Defined.

(* ------------------------------------------------------------------------ *)
(* * ** (c): every complete semilattice is a 𝒫-algebra / * **（c）：每个完整半格都是一个 𝒫-代数 *)

(* h S := sup S. Both algebra laws follow by antisymmetry. / h S := sup S。两个代数定律都可以通过反对称性得到。 *)
Definition SupLat_TAlgebra@{o so} (A : SupLatObject@{o}) :
  @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so}
    (sl_set A).
Proof.
  unshelve refine
    (@Build_TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so}
       (sl_set A) (sl_sup A) _ _).
  - intros x. simpl. apply sl_antisym.
    + apply sl_sup_least. intros z Hz. apply Hz; intro E.
      exact (sl_le_respects A x z x x E (reflexivity x) (sl_le_refl A x)).
    + apply sl_sup_ub. apply Powerset_squash_intro; reflexivity.
  - intros SS. simpl. apply sl_antisym.
    + apply sl_sup_least. intros w Hw. apply Hw; intros [S [HS E]].
      apply (sl_le_respects A (sl_sup A S) w _ _ E (reflexivity _)).
      apply sl_sup_least. intros z Hz. apply sl_sup_ub.
      exists S; split; assumption.
    + apply sl_sup_least. intros z [S [HS Hz]].
      apply (sl_le_trans A z (sl_sup A S)).
      * apply sl_sup_ub, Hz.
      * apply sl_sup_ub. apply Powerset_squash_intro.
        exists S; split; [exact HS | reflexivity].
Defined.

(* ------------------------------------------------------------------------ *)
(* * ** (b): every 𝒫-algebra is a complete semilattice / * **（b）：每个 𝒫-代数都是一个完全半格 *)

(* h {x} ≈ x: the algebra's unit law at x. / h {x} ≈ x：代数在 x 处的单位律。 *)
Lemma talg_singleton@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X)
  (x : carrier X) :
  @equiv _ (is_setoid X) (t_alg[α] (Powerset_Prop_singleton_pred@{o} x)) x.
Proof. exact (@t_id _ _ _ _ α x). Qed.

(* An algebra's carrier has propositional equality: the unit is split mono and P X's ≈ is a [Prop] in content. / 一个代数的载体具有命题等式：单位是可分单态，并且 P X 的 ≈ 在内容上是一个 [Prop]。 *)
Lemma talg_unsquash@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X)
  (x y : carrier X) :
  Powerset_squash@{o} (@equiv _ (is_setoid X) x y) →
  @equiv _ (is_setoid X) x y.
Proof.
  intro H.
  transitivity (t_alg[α] (Powerset_Prop_singleton_pred@{o} x));
    [symmetry; apply talg_singleton|].
  transitivity (t_alg[α] (Powerset_Prop_singleton_pred@{o} y));
    [|apply talg_singleton].
  apply proper_morphism. intro z; split; intros Hz Q k; apply H;
    intro exy; apply Hz; intro e; apply k.
  - transitivity x; [now symmetry | exact e].
  - transitivity y; [exact exy | exact e].
Qed.

(* h {h S, h T} ≈ h (S ∪ T): the action law at the pair {S, T}. / h {h S, h T} ≈ h (S ∪ T)：在集合对 {S, T} 上的作用律。 *)
Lemma talg_pair@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X)
  (S T : carrier (Powerset_Prop_obj@{o} X)) :
  @equiv _ (is_setoid X)
    (t_alg[α] (Powerset_Prop_pair@{o} (t_alg[α] S) (t_alg[α] T)))
    (t_alg[α] (Powerset_union_pred@{o} (Powerset_Prop_pair@{o} S T))).
Proof.
  transitivity
    (t_alg[α] (Powerset_Prop_image@{o} t_alg[α] (Powerset_Prop_pair@{o} S T))).
  - apply proper_morphism. intro z; split.
    + intros [H|H]; apply H; intro e; intros Q k; apply k.
      * exists S; split; [ left | exact e ].
        apply Powerset_squash_intro; reflexivity.
      * exists T; split; [ right | exact e ].
        apply Powerset_squash_intro; reflexivity.
    + intro H; apply H; intros [U [[HU|HU] e]]; [left|right];
        intros Q k; apply HU; intro eU; apply k;
        (transitivity (t_alg[α] U);
           [apply proper_morphism; exact eU | exact e]).
  - exact (@t_action _ _ _ _ α (Powerset_Prop_pair@{o} S T)).
Qed.

Lemma talg_mono@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X)
  (S T : carrier (Powerset_Prop_obj@{o} X)) (HST : ∀ z, S z → T z) :
  @equiv _ (is_setoid X)
    (t_alg[α] (Powerset_Prop_pair@{o} (t_alg[α] S) (t_alg[α] T)))
    (t_alg[α] T).
Proof.
  transitivity
    (t_alg[α] (Powerset_union_pred@{o} (Powerset_Prop_pair@{o} S T))).
  - apply talg_pair.
  - apply proper_morphism. apply Powerset_union_pair_sub, HST.
Qed.

(* Mac Lane's order, x ≤ y iff h {x, y} = y, squashed into [Prop]. / Mac Lane 的序，x ≤ y 当且仅当 h {x, y} = y，被压缩成 [Prop]。 *)
Definition talg_le@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X)
  (x y : carrier X) : Prop :=
  Powerset_squash@{o}
    (@equiv _ (is_setoid X) (t_alg[α] (Powerset_Prop_pair@{o} x y)) y).

(* The squash is logically inert: [talg_le] IS Mac Lane's condition. / 南瓜在逻辑上是惰性的：[talg_le] 是 Mac Lane 的条件。 *)
Lemma talg_le_iff@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X)
  (x y : carrier X) :
  iffT@{o o} (talg_le@{o so} α x y)
    (@equiv _ (is_setoid X) (t_alg[α] (Powerset_Prop_pair@{o} x y)) y).
Proof.
  split.
  - intro H. apply (talg_unsquash α). exact H.
  - intro E. exact (Powerset_squash_intro E).
Qed.

Lemma talg_le_refl@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X)
  (x : carrier X) : talg_le@{o so} α x x.
Proof.
  apply Powerset_squash_intro.
  transitivity
    (t_alg[α] (Powerset_Prop_pair@{o}
                 (t_alg[α] (Powerset_Prop_singleton_pred@{o} x))
                 (t_alg[α] (Powerset_Prop_singleton_pred@{o} x)))).
  - apply proper_morphism, Powerset_Prop_pair_respects;
      symmetry; apply talg_singleton.
  - transitivity (t_alg[α] (Powerset_Prop_singleton_pred@{o} x));
      [|apply talg_singleton].
    apply talg_mono. intros z Hz; exact Hz.
Qed.

Lemma talg_sup_ub@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X)
  (S : carrier (Powerset_Prop_obj@{o} X)) (x : carrier X) :
  S x → talg_le@{o so} α x (t_alg[α] S).
Proof.
  intro Hx. apply Powerset_squash_intro.
  transitivity
    (t_alg[α] (Powerset_Prop_pair@{o}
                 (t_alg[α] (Powerset_Prop_singleton_pred@{o} x))
                 (t_alg[α] S))).
  - apply proper_morphism, Powerset_Prop_pair_respects;
      [symmetry; apply talg_singleton | reflexivity].
  - apply talg_mono. apply Powerset_Prop_singleton_sub, Hx.
Qed.

(* Leastness, through the family {{x, y} | x ∈ S} ∪ {{y}}. / 最小性，通过族 {{x, y} | x ∈ S} ∪ {{y}}。 *)
Lemma talg_sup_least@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X)
  (S : carrier (Powerset_Prop_obj@{o} X)) (y : carrier X) :
  (∀ x, S x → talg_le@{o so} α x y) → talg_le@{o so} α (t_alg[α] S) y.
Proof.
  intro Hle. apply Powerset_squash_intro.
  transitivity
    (t_alg[α] (Powerset_Prop_pair@{o} (t_alg[α] S)
                 (t_alg[α] (Powerset_Prop_singleton_pred@{o} y)))).
  { apply proper_morphism, Powerset_Prop_pair_respects;
      [reflexivity | symmetry; apply talg_singleton]. }
  rewrite talg_pair.
  transitivity
    (t_alg[α] (Powerset_union_pred@{o} (Powerset_Prop_least_family@{o} S y))).
  { apply proper_morphism. intro z; split.
    - intros [U [[HU|HU] Hz]]; apply HU; intro e.
      + exists (Powerset_Prop_pair@{o} z y); split.
        * left; apply Powerset_squash_intro; exists z; split;
            [exact (proj2 (e z) Hz) | reflexivity].
        * left; apply Powerset_squash_intro; reflexivity.
      + exists (Powerset_Prop_singleton_pred@{o} y); split.
        * right; apply Powerset_squash_intro; reflexivity.
        * exact (proj2 (e z) Hz).
    - intros [U [[HU|HU] Hz]]; apply HU.
      + intros [x [Hx e]]. destruct (proj2 (e z) Hz) as [Hz'|Hz'].
        * exists S; split; [left; apply Powerset_squash_intro; reflexivity|].
          apply Hz'; intro e'. exact (proj1 (proper_morphism S x z e') Hx).
        * exists (Powerset_Prop_singleton_pred@{o} y); split;
            [right; apply Powerset_squash_intro; reflexivity | exact Hz'].
      + intro e. exists (Powerset_Prop_singleton_pred@{o} y); split;
          [right; apply Powerset_squash_intro; reflexivity
          | exact (proj2 (e z) Hz)]. }
  transitivity
    (t_alg[α] (Powerset_Prop_image@{o} t_alg[α]
                 (Powerset_Prop_least_family@{o} S y))).
  { symmetry.
    exact (@t_action _ _ _ _ α (Powerset_Prop_least_family@{o} S y)). }
  transitivity (t_alg[α] (Powerset_Prop_singleton_pred@{o} y));
    [|apply talg_singleton].
  apply proper_morphism. intro w; split.
  - intro Hw; apply Hw; intros [U [[HU|HU] e]]; apply HU.
    + intros [x [Hx eU]]. apply (Hle x Hx); intro Exy.
      intros Q k; apply k.
      transitivity (t_alg[α] (Powerset_Prop_pair@{o} x y)); [now symmetry|].
      transitivity (t_alg[α] U); [apply proper_morphism; exact eU | exact e].
    + intro eU. intros Q k; apply k.
      transitivity (t_alg[α] (Powerset_Prop_singleton_pred@{o} y));
        [symmetry; apply talg_singleton|].
      transitivity (t_alg[α] U); [apply proper_morphism; exact eU | exact e].
  - intro Hw; apply Hw; intro e; intros Q k; apply k.
    exists (Powerset_Prop_singleton_pred@{o} y); split.
    + right; apply Powerset_squash_intro; reflexivity.
    + transitivity y; [apply talg_singleton | exact e].
Qed.

Lemma talg_le_trans@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X)
  (x y z : carrier X) :
  talg_le@{o so} α x y → talg_le@{o so} α y z → talg_le@{o so} α x z.
Proof.
  intros Hxy Hyz. apply Hxy; intro Exy. apply Hyz; intro Eyz.
  apply Powerset_squash_intro.
  transitivity
    (t_alg[α] (Powerset_Prop_pair@{o}
                 (t_alg[α] (Powerset_Prop_singleton_pred@{o} x))
                 (t_alg[α] (Powerset_Prop_pair@{o} y z)))).
  { apply proper_morphism, Powerset_Prop_pair_respects;
      [symmetry; apply talg_singleton | now symmetry]. }
  rewrite talg_pair.
  transitivity
    (t_alg[α] (Powerset_union_pred@{o}
                 (Powerset_Prop_pair@{o} (Powerset_Prop_pair@{o} x y)
                    (Powerset_Prop_singleton_pred@{o} z)))).
  { apply proper_morphism. intro w; split.
    - intros [U [[HU|HU] Hw]]; apply HU; intro e;
        pose proof (proj2 (e w) Hw) as Hw'.
      + exists (Powerset_Prop_pair@{o} x y); split;
          [left; apply Powerset_squash_intro; reflexivity | left; exact Hw'].
      + destruct Hw' as [Hw'|Hw'].
        * exists (Powerset_Prop_pair@{o} x y); split;
            [left; apply Powerset_squash_intro; reflexivity
            | right; exact Hw'].
        * exists (Powerset_Prop_singleton_pred@{o} z); split;
            [right; apply Powerset_squash_intro; reflexivity | exact Hw'].
    - intros [U [[HU|HU] Hw]]; apply HU; intro e;
        pose proof (proj2 (e w) Hw) as Hw'.
      + destruct Hw' as [Hw'|Hw'].
        * exists (Powerset_Prop_singleton_pred@{o} x); split;
            [left; apply Powerset_squash_intro; reflexivity | exact Hw'].
        * exists (Powerset_Prop_pair@{o} y z); split;
            [right; apply Powerset_squash_intro; reflexivity
            | left; exact Hw'].
      + exists (Powerset_Prop_pair@{o} y z); split;
          [right; apply Powerset_squash_intro; reflexivity
          | right; exact Hw']. }
  rewrite <- talg_pair.
  transitivity (t_alg[α] (Powerset_Prop_pair@{o} y z)); [|exact Eyz].
  apply proper_morphism, Powerset_Prop_pair_respects;
    [exact Exy | apply talg_singleton].
Qed.

Lemma talg_le_respects@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X)
  (x x' y y' : carrier X) :
  @equiv _ (is_setoid X) x x' → @equiv _ (is_setoid X) y y' →
  talg_le@{o so} α x y → talg_le@{o so} α x' y'.
Proof.
  intros Ex Ey H; apply H; intro E; apply Powerset_squash_intro.
  transitivity (t_alg[α] (Powerset_Prop_pair@{o} x y)).
  - apply proper_morphism, Powerset_Prop_pair_respects; now symmetry.
  - now transitivity y.
Qed.

Lemma talg_antisym@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X)
  (x y : carrier X) :
  talg_le@{o so} α x y → talg_le@{o so} α y x → @equiv _ (is_setoid X) x y.
Proof.
  intros Hxy Hyx. apply (talg_unsquash α).
  apply Hxy; intro Exy; apply Hyx; intro Eyx; apply Powerset_squash_intro.
  transitivity (t_alg[α] (Powerset_Prop_pair@{o} y x)); [now symmetry|].
  transitivity (t_alg[α] (Powerset_Prop_pair@{o} x y)); [|exact Exy].
  apply proper_morphism, Powerset_Prop_pair_comm.
Qed.

(* Part (b): (X, h) as a complete semilattice, with sup S = h S. / 第(b)部分：将(X, h)作为一个完备半格，其中sup S = h S。 *)
Definition TAlgebra_SupLat@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X) :
  SupLatObject@{o} :=
  @Build_SupLatObject@{o} X (talg_le@{o so} α)
    (talg_le_refl@{o so} α) (talg_le_trans@{o so} α)
    (talg_le_respects@{o so} α) (talg_antisym@{o so} α)
    t_alg[α] (talg_sup_ub@{o so} α) (talg_sup_least@{o so} α).

(* Every 𝒫-algebra's carrier has a propositional equality. / 每个 𝒫-代数的承载体都有命题等式。 *)
Definition talg_PropEquiv@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X) :
  PropEquiv@{o o} (is_setoid X).
Proof.
  unshelve refine
    (@Build_PropEquiv@{o o} _ (is_setoid X)
       (fun x y => Powerset_squash@{o} (@equiv _ (is_setoid X) x y)) _ _).
  - intros x y H. exact (talg_unsquash α x y H).
  - intros x y H. exact (Powerset_squash_intro H).
Defined.

(* (b) after (c) gives back the order: “in this way”. / (b) 在 (c) 之后返回顺序：“以这种方式”. *)
Lemma sl_talg_le_iff@{o so} (A : SupLatObject@{o})
  (x y : carrier (sl_set A)) :
  iff (talg_le@{o so} (SupLat_TAlgebra@{o so} A) x y) (sl_le A x y).
Proof.
  destruct (sl_sup_pair_le A x y) as [HL HR].
  destruct (talg_le_iff (SupLat_TAlgebra@{o so} A) x y) as [TL TR].
  split.
  - intro H. exact (HR (TL H)).
  - intro H. exact (TR (HL H)).
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** (d): the category of 𝒫-algebras is the category of semilattices / * ** (d)：𝒫-代数的范畴是半格的范畴 *)

Definition EM_to_SupLat@{o so} :
  @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
    Powerset_Monad@{o so} ⟶ SupLat@{o so}.
Proof.
  unshelve refine
    (@Build_Functor
       (@EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
          Powerset_Monad@{o so})
       SupLat@{o so}
       (fun x => TAlgebra_SupLat@{o so} (projT2 x))
       (fun x y f =>
          @Build_SupLatHom@{o}
            (TAlgebra_SupLat@{o so} (projT2 x))
            (TAlgebra_SupLat@{o so} (projT2 y))
            (@t_alg_hom _ _ _ _ _ _ _ f)
            (fun S => @t_alg_hom_commutes _ _ _ _ _ _ _ f S))
       _ _ _).
  - intros x y f g H a. exact (H a).
  - intros x a. reflexivity.
  - intros x y z f g a. reflexivity.
Defined.

Definition SupLat_to_EM@{o so} :
  SupLat@{o so} ⟶
  @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
    Powerset_Monad@{o so}.
Proof.
  unshelve refine
    (@Build_Functor SupLat@{o so}
       (@EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
          Powerset_Monad@{o so})
       (fun A => existT _ (sl_set A) (SupLat_TAlgebra@{o so} A))
       (fun A B f =>
          @Build_TAlgebraHom Sets@{o so} Powerset_Prop@{o so}
            Powerset_Monad@{o so} (sl_set A) (sl_set B)
            (SupLat_TAlgebra@{o so} A) (SupLat_TAlgebra@{o so} B)
            (slh_map f) (slh_sup f))
       _ _ _).
  - intros A B f g H a. exact (H a).
  - intros A a. reflexivity.
  - intros A B C f g a. reflexivity.
Defined.

(* The algebra round trip, with the identity as its component. / 代数往返，以恒等式作为其组成部分。 *)
Definition SupLat_EM_counit_iso@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) :
  @Isomorphism
    (@EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
       Powerset_Monad@{o so})
    (fobj[SupLat_to_EM@{o so} ◯ EM_to_SupLat@{o so}] x) x.
Proof.
  unshelve refine
    (@Build_Isomorphism
       (@EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
          Powerset_Monad@{o so})
       (fobj[SupLat_to_EM@{o so} ◯ EM_to_SupLat@{o so}] x) x
       (@Build_TAlgebraHom Sets@{o so} Powerset_Prop@{o so}
          Powerset_Monad@{o so} (projT1 x) (projT1 x)
          (SupLat_TAlgebra@{o so} (TAlgebra_SupLat@{o so} (projT2 x)))
          (projT2 x)
          (@setoid_morphism_id@{o o o} (projT1 x)) _)
       (@Build_TAlgebraHom Sets@{o so} Powerset_Prop@{o so}
          Powerset_Monad@{o so} (projT1 x) (projT1 x)
          (projT2 x)
          (SupLat_TAlgebra@{o so} (TAlgebra_SupLat@{o so} (projT2 x)))
          (@setoid_morphism_id@{o o o} (projT1 x)) _) _ _).
  - intro S. simpl. apply (proper_morphism (t_alg[projT2 x])).
    symmetry. exact (@Powerset_Prop_map_id@{o} (projT1 x) S).
  - intro S. simpl. apply (proper_morphism (t_alg[projT2 x])).
    symmetry. exact (@Powerset_Prop_map_id@{o} (projT1 x) S).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(* The semilattice round trip, with the identity as its component. / 半格往返，其分量为恒等元。 *)
Definition SupLat_EM_unit_iso@{o so} (A : SupLatObject@{o}) :
  @Isomorphism SupLat@{o so}
    (fobj[EM_to_SupLat@{o so} ◯ SupLat_to_EM@{o so}] A) A.
Proof.
  unshelve refine
    (@Build_Isomorphism SupLat@{o so}
       (fobj[EM_to_SupLat@{o so} ◯ SupLat_to_EM@{o so}] A) A
       (@Build_SupLatHom@{o}
          (fobj[EM_to_SupLat@{o so} ◯ SupLat_to_EM@{o so}] A) A
          (@setoid_morphism_id@{o o o} (sl_set A)) _)
       (@Build_SupLatHom@{o} A
          (fobj[EM_to_SupLat@{o so} ◯ SupLat_to_EM@{o so}] A)
          (@setoid_morphism_id@{o o o} (sl_set A)) _) _ _).
  - intro S. simpl. apply (proper_morphism (sl_sup A)).
    symmetry. exact (@Powerset_Prop_map_id@{o} (sl_set A) S).
  - intro S. simpl. apply (proper_morphism (sl_sup A)).
    symmetry. exact (@Powerset_Prop_map_id@{o} (sl_set A) S).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(* Part (d), as an equivalence of categories with identity components. / 部分 (d)，作为具有恒等分量的范畴等价。 *)
Definition SupLat_EM_equivalence@{o so} :
  @EquivalenceOfCategories@{so so so so so o} SupLat@{o so}
    (@EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
       Powerset_Monad@{o so})
    SupLat_to_EM@{o so}.
Proof.
  unshelve refine
    (@Build_EquivalenceOfCategories _ _ SupLat_to_EM@{o so}
       EM_to_SupLat@{o so} _ _).
  - exists (fun x => SupLat_EM_counit_iso@{o so} x).
    intros x y f a. reflexivity.
  - exists (fun A => iso_sym (SupLat_EM_unit_iso@{o so} A)).
    intros A B f a. reflexivity.
Defined.

(*
 Part (d), as an isomorphism in Cat, built from the two component
 isomorphisms so that both of its natural isomorphisms have the identity
 as every component at [eq_refl]: Theory/Equivalence.v's
 [Equivalence_to_Cat_Iso] would make [iso_from_to] the [symmetry] of the
 unit, which is Theory/Functor.v's opaque [Functor_Setoid_obligation_1]. 

 --------
 部分(d)，作为 Cat 中的一个同构，由两个分量同构构建，使得它的两个自然同构在 [eq_refl] : Theory/Equivalence.v 的每个分量上都是恒等映射。[Equivalence_to_Cat_Iso] 会使 [iso_from_to] 成为单位的 [symmetry]，这就是 Theory/Functor.v 的不透明 [Functor_Setoid_obligation_1]。
*)
Definition SupLat_EM_iso@{o so c} :
  @Isomorphism Cat@{c so so so o} SupLat@{o so}
    (@EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
       Powerset_Monad@{o so}).
Proof.
  unshelve refine
    (@Build_Isomorphism Cat@{c so so so o} SupLat@{o so}
       (@EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
          Powerset_Monad@{o so})
       SupLat_to_EM@{o so} EM_to_SupLat@{o so} _ _).
  - exists (fun x => SupLat_EM_counit_iso@{o so} x).
    intros x y f a. reflexivity.
  - exists (fun A => SupLat_EM_unit_iso@{o so} A).
    intros A B f a. reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** Readbacks / ** 回读 *)

(* The two legs of the isomorphism are the two functors. / 同构的两个分支是两个函子。 *)
Example SupLat_EM_iso_to@{o so c} :
  to SupLat_EM_iso@{o so c} = SupLat_to_EM@{o so} := eq_refl.

Example SupLat_EM_iso_from@{o so c} :
  from SupLat_EM_iso@{o so c} = EM_to_SupLat@{o so} := eq_refl.

(* (b): the carrier is X, sup S = h S as a setoid map, and the order is Mac Lane's h {x, y} ≈ y, squashed. / (b)：载体是 X，sup S = h S 作为集合等价映射，顺序是 Mac Lane 的 h {x, y} ≈ y，压缩。 *)
Example EM_to_SupLat_carrier@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) :
  sl_set (fobj[EM_to_SupLat@{o so}] x) = projT1 x := eq_refl.

Example EM_to_SupLat_sup@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) :
  sl_sup (fobj[EM_to_SupLat@{o so}] x) = t_alg[projT2 x] := eq_refl.

Example EM_to_SupLat_le@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) (a b : carrier (projT1 x)) :
  sl_le (fobj[EM_to_SupLat@{o so}] x) a b
    = Powerset_squash@{o}
        (@equiv _ (is_setoid (projT1 x))
           (t_alg[projT2 x] (Powerset_Prop_pair@{o} a b)) b) := eq_refl.

(* (c): the carrier is the semilattice's, and h = sup as a setoid map. / (c)：载体是半格的，并且 h = sup 作为集合映射。 *)
Example SupLat_to_EM_carrier@{o so} (A : SupLatObject@{o}) :
  projT1 (fobj[SupLat_to_EM@{o so}] A) = sl_set A := eq_refl.

Example SupLat_to_EM_alg@{o so} (A : SupLatObject@{o}) :
  t_alg[projT2 (fobj[SupLat_to_EM@{o so}] A)] = sl_sup A := eq_refl.

(* The morphisms are carried unchanged. / 态射保持不变。 *)
Example EM_to_SupLat_map@{o so}
  (x y : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
           Powerset_Monad@{o so}) (f : x ~> y) :
  slh_map (fmap[EM_to_SupLat@{o so}] f) = t_alg_hom[f] := eq_refl.

Example SupLat_to_EM_map@{o so} (A B : SupLatObject@{o})
  (f : SupLatHom@{o} A B) :
  t_alg_hom[fmap[SupLat_to_EM@{o so}] f] = slh_map f := eq_refl.

(* The round trips on data. / 关于数据的往返旅行。 *)
Example SupLat_EM_rt_carrier@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) :
  projT1 (fobj[SupLat_to_EM@{o so} ◯ EM_to_SupLat@{o so}] x) = projT1 x
  := eq_refl.

Example SupLat_EM_rt_alg@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) :
  t_alg[projT2 (fobj[SupLat_to_EM@{o so} ◯ EM_to_SupLat@{o so}] x)]
    = t_alg[projT2 x] := eq_refl.

Example SupLat_EM_rt_set@{o so} (A : SupLatObject@{o}) :
  sl_set (fobj[EM_to_SupLat@{o so} ◯ SupLat_to_EM@{o so}] A) = sl_set A
  := eq_refl.

Example SupLat_EM_rt_sup@{o so} (A : SupLatObject@{o}) :
  sl_sup (fobj[EM_to_SupLat@{o so} ◯ SupLat_to_EM@{o so}] A) = sl_sup A
  := eq_refl.

Example SupLat_EM_rt_hom@{o so} (A B : SupLatObject@{o})
  (f : SupLatHom@{o} A B) :
  slh_map (fmap[EM_to_SupLat@{o so} ◯ SupLat_to_EM@{o so}] f) = slh_map f
  := eq_refl.

Example SupLat_EM_rt_alg_hom@{o so}
  (x y : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
           Powerset_Monad@{o so}) (f : x ~> y) :
  t_alg_hom[fmap[SupLat_to_EM@{o so} ◯ EM_to_SupLat@{o so}] f]
    = t_alg_hom[f] := eq_refl.

(* The components of the equivalence's counit and unit are identities. / 等价的余单位和单位的组成部分是恒等式。 *)
Example SupLat_EM_counit_component@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) :
  t_alg_hom[to (projT1 (@equivalence_counit _ _ _
                           SupLat_EM_equivalence@{o so}) x)]
    = @setoid_morphism_id@{o o o} (projT1 x) := eq_refl.

Example SupLat_EM_unit_component@{o so} (A : SupLatObject@{o}) :
  slh_map (to (projT1 (@equivalence_unit _ _ _
                         SupLat_EM_equivalence@{o so}) A))
    = @setoid_morphism_id@{o o o} (sl_set A) := eq_refl.

Example SupLat_EM_counit_component_from@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) :
  t_alg_hom[from (projT1 (@equivalence_counit _ _ _
                             SupLat_EM_equivalence@{o so}) x)]
    = @setoid_morphism_id@{o o o} (projT1 x) := eq_refl.

Example SupLat_EM_unit_component_from@{o so} (A : SupLatObject@{o}) :
  slh_map (from (projT1 (@equivalence_unit _ _ _
                           SupLat_EM_equivalence@{o so}) A))
    = @setoid_morphism_id@{o o o} (sl_set A) := eq_refl.

(* So are those of both natural isomorphisms of the isomorphism in Cat. / 所以这些都是 Cat 中同构的自然同构的同构。 *)
Example SupLat_EM_iso_to_from_component@{o so c}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) :
  t_alg_hom[to (projT1 (iso_to_from SupLat_EM_iso@{o so c}) x)]
    = @setoid_morphism_id@{o o o} (projT1 x) := eq_refl.

Example SupLat_EM_iso_from_to_component@{o so c} (A : SupLatObject@{o}) :
  slh_map (to (projT1 (iso_from_to SupLat_EM_iso@{o so c}) A))
    = @setoid_morphism_id@{o o o} (sl_set A) := eq_refl.

Example SupLat_EM_iso_to_from_component_from@{o so c}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) :
  t_alg_hom[from (projT1 (iso_to_from SupLat_EM_iso@{o so c}) x)]
    = @setoid_morphism_id@{o o o} (projT1 x) := eq_refl.

Example SupLat_EM_iso_from_to_component_from@{o so c}
  (A : SupLatObject@{o}) :
  slh_map (from (projT1 (iso_from_to SupLat_EM_iso@{o so c}) A))
    = @setoid_morphism_id@{o o o} (sl_set A) := eq_refl.
