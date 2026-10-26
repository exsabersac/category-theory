Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lqa.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyReals.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyRealsMult.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyAbs.
Require Import Coq.Reals.Cauchy.ConstructiveRcomplete.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.
Require Import Category.Instance.Top.Circle.
Require Import Category.Instance.Top.Components.

Generalizable All Variables.

(* * * Path components: π₀ as the colimit functor after P / * * 路径分量：π₀ 作为 P 之后的余极限函子 *)

(*
 Riehl, “Category Theory in Context”, 2nd ed., §3.3, Example 3.3.2,
 printed pp. 99–100 (PDF pp. 119–120), read from the page images:
 “Recall the functor Path: Top → Set that carries a space X to the
 set Path(X) := Top(I, X), where I is the standard unit interval.
 Precomposing with the endpoint inclusions 0, 1 : ∗ ⇉ I defines a
 functor P : Top → Set^{•⇉•} that carries a space X to the parallel
 pair of functions Path(X) ≅ Top(I, X) ⇉ Top(∗, X) ≅ Point(X) that
 evaluate a path at its endpoints.  Their coequalizer [...] defines
 the set of path components of X, the quotient of the set of points
 in X by the relation that identifies any pair of points connected
 by a path.  Proposition 3.3.1 tells us that this coequalizer
 defines a functor, the path components functor
 π₀ := Top --P--> Set^{•⇉•} --colim--> Set.”  The parallel arrows
 of the page's two displays are labelled ev₀ and ev₁.  (Catalog id
 riehl:3.3:example2, Riehl's Example 3.3.2.)
 Mac Lane, “Categories for the Working Mathematician”, 2nd ed. (GTM 5),
 §V.9, Exercise 1, book p. 135 (PDF p. 144), read from the page
 image: “For the full subcategory Lconn of locally connected spaces
 in Top, prove that D: Set → Lconn has a left adjoint C, assigning
 to each space X the set of its connected components, but show that
 this functor C can have no left adjoint (because of misbehavior on
 equalizers).”  (Catalog id maclane:V.9:ex1.)
 nLab: https://ncatlab.org/nlab/show/Top
 nLab: https://ncatlab.org/nlab/show/connected+space
 Wikipedia: https://en.wikipedia.org/wiki/Locally_connected_space
 Rocq standard library: Reals/Cauchy/ConstructiveRcomplete.v

 BACKGROUND.  Issue #462 carries two quotients of the points of a
 space, and this file is about the second.  Mac Lane's exercise is
 about CONNECTED components, and only on locally connected spaces,
 where they give the left adjoint of the discrete-space functor; that
 half of the issue is Instance/Top/Components.v's.  This file requires
 it for two constants only: [swap_set], the negation of the two points
 that the bisection below composes with, and [PConnectedBool], the
 two-point form of connectedness that [interval_PConnectedBool]
 states for the interval.  [Print Libraries] on a file requiring this
 one lists 129 [Category.*] modules besides it, 109 without the
 Require of Components.v.  Riehl's example is about
 PATH components on all of Top, and its point is less the set than the
 functor: the functoriality of π₀ is not checked by hand but taken
 from the colimit functor of his Proposition 3.3.1.  The two notions
 are related as Wikipedia's article on locally connected spaces puts
 it: “Because path connected sets are connected, we have
 PC_x ⊆ C_x”, and “for a locally path connected space the components
 and path components coincide”; the topologist's sine curve is its
 example where they differ.  nLab's page on connected spaces has a
 section on the same functor, “π₀ : Top → Set be the functor which
 assigns to each space X its set of path components”, and its proof
 that π₀ preserves finite products reads it as a reflexive coequalizer
 of hom(I, −) and hom(1, −), the two functors P packages.  The same
 page warns that in constructive mathematics the classical definitions
 of connectedness “no longer need to be equivalent”, which is why the
 connectedness proved below is stated in the one form it has.

 THE ENCODING.  Spaces are Instance/Top/Prop.v's [PTop], whose homs
 sit at the points' universe, by the maintainer's standing decision
 for the Top issues: over the Type-valued [Top] the hom-sets sit above
 the points (Instance/Top/Prop.v's header), so Top(I, X) would not be
 an object of the [Sets] the points live in.  [PHomSetoid A X] is the
 hom-setoid of [PTopCat] as an object of [Sets@{o so}], so Riehl's
 Path(X) and Point(X) ARE [PHomSetoid PInterval X] and
 [PHomSetoid PPoint X] ([PPathPair_paths], [PPathPair_points]); the
 two isomorphisms of his display are identities here.  The interval I
 is [0,1] in the standard library's constructive Cauchy reals:
 [PInterval] is Instance/Top/Subspace.v's subspace [PSub] of
 Instance/Top/Circle.v's line [PRLine] on [IvalSetoid], the reals x
 with 0 ≤ x ≤ 1 under [CRealEq].  The classical [R] is not loaded:
 [Print Libraries] of a scratch file requiring this one lists eight
 standard-library reals modules, seven under Reals/Cauchy and the
 eighth Reals/Abstract/ConstructiveReals, which
 ConstructiveRcomplete.v requires.  Instance/Top/Circle.v's header
 records the axioms that Instance/Top/Interval.v's classical [I_Top]
 carries.  The endpoint
 inclusions 0, 1 : ∗ ⇉ I are [ival_end0] and [ival_end1], the maps
 out of the one-point space [PPoint] at [ival_zero] and [ival_one]
 ([ppoint_at]).

 P AND π₀, WITH THE FUNCTORIALITY DERIVED.  [PPathPair_obj X] is
 Instance/Parallel.v's [APair] of the two precompositions
 [pprecomp X ival_end0] and [pprecomp X ival_end1]: its arrow over
 [(true; ParOne)] IS ev₀ and over [(false; ParTwo)] IS ev₁
 ([PPathPair_ev0], [PPathPair_ev1]).  [PPathPair], Riehl's P, sends
 an arrow h to postcomposition with h on paths and on points
 ([PPathPair_map], [PPathPair_fmap_paths]); its codomain [ParSets] is
 Instance/Fun.v's [Fun Parallel Sets], Riehl's Set^{•⇉•}, with its
 universes written out.  P is written by hand: Riehl's text defines it
 by precomposition and keeps the colimit functor for π₀.  Deriving it
 too, as the Yoneda embedding [Curried_CoHom PTopCat] followed by
 Theory/Kan/Extension.v's precomposition [Induced] along the endpoint
 pair in [PTopCat^op], is refused: “universe inconsistency: Cannot
 enforce ... = o because o < ... <= ...”, Test/ProbeComponents462.v's
 N12, beside the accepted endpoint pair [p462_iota] and Yoneda embedding
 [p462_yoneda].  [Fun]'s block bounds its hom universe below by its
 domain's object universe ([u <= u4]), which for [PTopCat^op] is [so],
 above [o], while the composite asks for [o].
 [PPi0] is [ColimitFunctor PathColim ◯ PPathPair]: #353's colimit
 functor (Adjunction/Diagonal/Limit.v) over Instance/Sets/Cocomplete.v's
 chosen colimits at the [Parallel] shape ([PathColim]).  No functor law
 of π₀ is proved in this file.  [PPi0]'s arrow part IS
 [Colim_map PathColim (PPathPair_map h)] ([PPi0_fmap]), and its laws
 are [ColimitFunctor]'s and [PPathPair]'s, composed by [Compose].
 Riehl's remark before the proof of Proposition 3.3.1, that the
 functor “requires an arbitrary choice of a limit”, has no
 counterpart: [Sets_Cocomplete] supplies each colimit as data, and
 [Print Assumptions] finds no axiom (below).

 READBACKS: THE COLIMIT IS RIEHL'S QUOTIENT.  Instance/Sets/Cocomplete.v
 builds a colimit as the coproduct of the diagram's objects under the
 relation [colim_rel] its arrows generate, so an element of [PPi0 X]
 is a pair (ParX; a path) or (ParY; a point), and two are equal when
 [colim_rel] relates them ([PPi0_carrier], [PPi0_equiv]).  Two
 isomorphisms of [Sets] read this back as Riehl's coequalizer.
 [PPi0_coeq_iso X] identifies it with Instance/Sets/Coequalizer.v's
 [SetsCoeq] of ev₀ and ev₁ on Point(X): the forward map is the
 mediator into Structure/Coequalizer.v's [is_coequalizer_cocone] of
 [sets_coeq_IsCoequalizer], the backward map the injection at [ParY].
 [PPi0_points_iso X] identifies it with the [SetsCoeq] of the two
 evaluations [path_at X ival_zero] and [path_at X ival_one] on the
 point setoid of X itself: Riehl's “quotient of the set of points in
 X by the relation that identifies any pair of points connected by a
 path”.  That relation is [coeq_rel], the equivalence relation
 GENERATED by the pairs (γ 0, γ 1) and the points' own equality, so
 two points joined by a chain of paths are identified whether or not
 one path joins them; “joined by one path” would be transitive by the
 concatenation of paths, which is not constructed here.  On
 representatives the maps of both isomorphisms are what they should
 be ([ppi0_to_coeq_point], [ppi0_to_coeq_path],
 [ppi0_from_coeq_point], [ppi0_to_points_point],
 [ppi0_from_points_at]), and the derived action of [PPi0] on an arrow
 h IS postcomposition with h on both kinds of representative
 ([PPi0_fmap_point], [PPi0_fmap_path]): the hand-written
 functoriality, recovered by conversion.

 THE INTERVAL IS CONNECTED, FOR MAPS INTO [PBool].
 [interval_bool_endpoints]: every continuous γ : [PInterval] → [PBool]
 takes one value at the two endpoints.  The proof is bisection.  If γ
 is [false] at 0 and [true] at 1, halving [0,1] at rational points
 keeps [false] at the left end and [true] at the right ([ibis_stage],
 [ibis_inv]); the case split is on a boolean value of γ, so no
 comparison of reals is decided.  The left ends form a Cauchy sequence
 with a modulus ([ibis_seq_cauchy]); its limit is the standard
 library's [Rcauchy_complete] (Reals/Cauchy/ConstructiveRcomplete.v,
 whose [Print Assumptions] prints “Closed under the global context”,
 measured in a scratch file), and lies in [0,1] ([ibis_lim_ival]).  γ
 is constant on a ball about the limit, and the left and the right
 ends both enter that ball ([ibis_contra]); the other case, [true] at 0
 and [false] at 1, is that one after Components.v's negation
 [swap_set].  [interval_bool_constant]
 extends the statement to any two points s and t, along the segments
 [ival_segment a], t ↦ t·a, which are paths because multiplication by
 a real of absolute value at most one carries each ball into the ball
 of the same radius ([rball_scale]).  This is the two-point form of
 connectedness, maps into [PBool] only (NOT DELIVERED, below), and
 [interval_PConnectedBool] states it as Components.v's
 [PConnectedBool PInterval], by conversion.  The classical counterpart
 is Instance/Top/FundamentalGroupoid.v's
 [interval_to_discrete_constant], over the Type-valued [Top] and the
 classical reals: a least-upper-bound argument, stated there for every
 discrete target whose equality is decidable
 ([interval_to_discrete_constant_dec]), whose decider makes the
 supremum's predicate a proposition.  The bisection here splits on the
 value of γ at a rational point, which for [PBool] is a boolean, so
 its restriction to [PBool] plays the part of that decider.

 NON-VACUITY.  π₀ of the interval is one point: [PPi0_PInterval_iso]
 is an isomorphism of [Sets] with the one-point setoid, each
 representative joined to the class of 0 by the segment from 0 to it
 ([pinterval_point_rel], [pinterval_rel]).  π₀ of the two-point
 discrete space has two points: [Pi0_PBool_two] refutes that the
 classes of Instance/Top/Subspace.v's [ppoint_true] and [ppoint_false]
 agree, by mediating out of the colimit into [pi0_bool_cocone], the
 cocone to [bool] whose [ParTwo] leg coheres by
 [interval_bool_constant]; and [PPi0_PBool_iso] is an isomorphism of
 [Sets] with [bool_setoid_object].  So [PPi0] identifies the points a
 path joins and separates the two points no path joins.

 STRENGTHS.  At [eq_refl], all 18 [Example]s of the file:
 [PPathPair_paths], [PPathPair_points], [PPathPair_ev0],
 [PPathPair_ev1], [PPathPair_fmap_paths], [PPi0_fobj], [PPi0_fmap],
 [PPi0_carrier], [PPi0_equiv], [PPi0_inj_point], [PPi0_fmap_point],
 [PPi0_fmap_path], the five readbacks of the isomorphisms' maps named
 above, and [ival_segment_map].  Up to [≈] only: the functor laws of
 [PPi0]. On a representative (ParY; x) the identity law at [eq_refl] is
 refused, “cannot unify” (Test/ProbeComponents462.v's N10, beside the
 law up to [≈], [p462_pi0_id]): the underlying functions of [pcompose
 (pid X) x] and [x] agree by conversion ([p462_id_fun]), but the two
 setoid maps do not (“cannot unify ”pmap (pcompose (pid X) x)“ and ”pmap
 x“”, N11), their respectfulness proofs being built differently.
 CORRECTION (#1347): both now hold at [eq_refl], N10 and N11 being
 controls of that probe, since Instance/Sets.v gives its identity's and
 composite's properness fields as terms.  The proofs were built
 differently, but what kept the two setoid maps apart was the standard
 library's: the opaque lemmas instance resolution had put in the properness
 fields of the identity and of the composite in [pcompose (pid X) x]'s map
 part.
 Up to [≈] as well: the laws of the four isomorphisms, whose witnesses are
 [colim_rel] and [coeq_rel] data, and [ival_segment_0], [ival_segment_1]
 ([CRealEq], not conversion). [interval_bool_endpoints] and
 [interval_bool_constant] are Leibniz equalities of booleans, [PBool]'s
 equality being
 Leibniz; [Pi0_PBool_two] is a refutation.  [Print Assumptions]
 prints “Closed under the global context” for all 126 constants of
 the [Print Module] listing, its 28 [Program] obligations among them;
 the file declares no record or inductive type, so there is no
 constructor to add.

 UNIVERSES, read by [About] under [Set Printing Universes] on the 126
 constants.  Binders: 16 constants at [@{}] (the rational and real
 arithmetic: [ival_pred], its two lemmas, [rball_scale],
 [ival_mult_pred] and eleven [ibis_] constants on rationals); 44 at
 [@{o}] (the interval, its points, scalings and segments, [ppoint_at],
 [PHomSetoid], the bisection, the two connectedness theorems and
 [interval_PConnectedBool]); 10 at [@{o so}] ([pprecomp], [ppostcomp],
 [path_at], [pbool_at_zero], [pbool_at_point] and their obligations); 27
 at [@{o so p}] (the diagram [PPathPair_obj], [PathColim], the readback
 maps, and the relations of the interval's and [PBool]'s classes); 29 at
 [@{o so p f}] ([ParSets], [PPathPair], [PPi0] and everything stated
 about [PPi0]).  [o] is the points' universe and [so] the object
 universe of [PTopCat@{o so}] and [Sets@{o so}], with [o < so], the
 bound [PTopCat] and [Sets] carry.  [p] is the object universe of the
 shape [Parallel@{p o}], and [p <= o] is forced: omitted from the
 binder of a scratch copy of [PathColim], [About] reads it back,
 inferred from [Sets_Cocomplete]'s own block ([ud <= uc], [uc = uo]).
 [f] is [Fun]'s auxiliary universe, and [o < f] is forced the same
 way, [Fun]'s own [u0 < u5].  Two binders are extensible,
 [ibis_cv_ge@{o +}] and [ibis_cv_le@{o +}]: with the closed [@{o}]
 Coq 8.19.2 and 8.20.1 refuse both, “Universe ... is unbound”, at a
 universe their elaboration creates, where Rocq 9.1 accepts the
 closed form; [About] reads both back at [@{o}] on Rocq 9.1 and on
 Coq 8.19.2.  Blocks are empty on 21 constants.  No
 universe of this file is pinned at [Set].  Over the 126 blocks the
 word [Set] occurs 530 times: 28 times as [Set < so], [PTopCat]'s
 bound, in every [@{o so p f}] block but [ParSets]'s, which does not
 mention [PTopCat]; and otherwise only as a strict lower bound of a
 standard-library universe, [Set < Basics.flip.u0], [.u1] and [.u2]
 in 96 blocks, [Set < Morphisms.Proper.u0] and
 [Set < Morphisms.Relations.u0] in 93 (first carried by [PInterval],
 from Instance/Top/Circle.v's [PRLine], whose own block has all five),
 and [Set < Morphisms.GenericInstances.u0] and
 [Set < ConstructiveCauchyReals.CRealLt_morph.u0] in 14 (first
 carried by [ibis_cv_ge], whose proof term names [CRealLt_morph], the
 standard library's instance for rewriting under [CRealLt], 19 times).
 [p <= so] (29 blocks) follows from [p <= o] and [o < so].  The
 remaining caps are [<=] bounds on global universes that the donors
 carry in their own blocks: [compose.u*] and [ID.u0] (Instance/Sets.v's
 setoid maps, first on [pprecomp]'s obligation),
 [Logic_lemmas.equality.u0] (Instance/Sets.v's [unit_setoid_object]
 and [bool_setoid_object], first on [ppoint_at]), [False_rect.u0]
 ([APair]'s own cap, first on [PPathPair_obj]), [eq_rect.u0],
 [eq_rect.u1], [Projections.u0] and [Projections.u1]
 ([Sets_Cocomplete]'s, first on [PathColim]), [o <= Projections.u0]
 on the six constants built on Instance/Sets/Coequalizer.v's
 [sets_coeq_IsCoequalizer], whose own block has it (first on
 [ppi0_to_coeq]); [eq_ind.u0] and [eq_ind_r.u0], which first appear
 on this file's own proofs [ibis_contra] and [interval_bool_endpoints],
 no donor constant of theirs isolated as the carrier; and
 [eq_rect_r.u1], first on [interval_bool_endpoints] as well, which
 Instance/Top/Components.v's [swap_set] carries in its own block (nine
 blocks, [PPi0_PBool_iso]'s first obligation among them, which has it
 from its own proof).

 NOT DELIVERED.
 - The comparison π₀ → C from path components to Mac Lane's
 connected components on locally connected spaces
 (Instance/Top/Components.v's functor).  Sending a path class to
 a component needs every path to stay inside one component, that
 is, the interval connected in Instance/Top/Components.v's
 [PConnected] form (its maps into discrete spaces on propositional
 sets constant), not only for maps into [PBool]; the bisection
 above splits on the boolean value of the map, and the equality of
 a general discrete target need not be decidable.  No constructive
 proof of that form was found, and nothing about it is stated
 here.  The comparison would
 also cross a difference of codomains: [PPi0] lands in [Sets], its
 equality [colim_rel] being Type-valued, where C lands in
 Components.v's [PSets], the propositional sets.
 - Connectedness of the interval in any form but the two-point one
 ([interval_PConnectedBool]): not Components.v's [PConnected], the
 form with Prop-valued locally constant predicates, and not its
 [PConnectedSep], the absence of a separation by two disjoint
 opens.
 - Concatenation and reversal of paths, the transitivity of “joined
 by one path”, and any fundamental groupoid over [PTopCat]
 (Instance/Top/FundamentalGroupoid.v's is over the Type-valued
 [Top] and the classical reals).
 - π₀ of any other space.  No path is constructed but the segments
 of the interval, so π₀ is computed for [PInterval] and [PBool]
 only; in particular no path into a finite non-discrete space is
 built, and no π₀ of one is computed.
 - π₀ over the Type-valued [Top], and the preservation of products
 and coproducts by π₀ that nLab's page proves.
 - A derivation of P itself from the Yoneda embedding (refused, N12,
 above). 

 --------
 Riehl，《语境中的范畴论》，第2版，第3.3节，示例3.3.2，印刷页99–100（PDF页119–120），从页面图像读取：
 “回忆函子 Path: Top → Set，它将空间 X 映射到集合 Path(X) := Top(I, X)，其中 I 是标准单位区间。与端点包含映射 0, 1 : ∗ ⇉ I 进行复合定义了一个函子 P : Top → Set^{•⇉•}，它将空间 X 映射到一对平行函数 Path(X) ≅ Top(I, X) ⇉ Top(∗, X) ≅ Point(X)，它们在端点处对路径进行求值。它们的等化子 [...] 定义了 X 的路径连通分支集合，即将 X 中点的集合按由路径连接的点对等价关系进行商得到的集合。”命题 3.3.1 告诉我们，这个余等化子定义了一个函子，即路径分支函子
 π₀ := Top --P--> Set^{•⇉•} --colim--> Set。页面两个显示的平行箭头标记为 ev₀ 和 ev₁。（目录编号 riehl:3.3:example2，Riehl 的例子 3.3.2。）
 Mac Lane，《面向工作数学家的范畴》，第 2 版（GTM 5），§V.9，练习 1，书中第 135 页（PDF 页码 144)，从页面读取
 图片：“对于拓扑空间分类 Top 中局部连通空间的全子类别 Lconn，证明 D: Set → Lconn 具有一个左伴随 C，将每个空间 X 分配到其连通分支的集合，但表明该函子 C 不可能有左伴随（因为在等化器上的不良行为）。”（目录编号 maclane:V.9:ex1.）
 nLab: https://ncatlab.org/nlab/show/Top
 nLab: https://ncatlab.org/nlab/show/connected+space
 维基百科: https://en.wikipedia.org/wiki/Locally_connected_space
 Rocq 标准库: Reals/Cauchy/ConstructiveRcomplete.v背景。第462期包含一个空间的两种商，并且这个文件涉及第二种。Mac Lane 的练习是关于连通分支的，并且只适用于局部连通空间，在这些空间中，它们给出了离散空间函子左伴随的表达；该期的那一半内容在 Instance/Top/Components.v 中。本文件仅对两个常量需要它：[swap_set]，即下述二分法复合的两个点的否定，以及 [PConnectedBool]，即 [interval_PConnectedBool] 为区间陈述的连通性的两点形式。在一个需要此文件的文件中，[Print Libraries] 列出除了它之外的 129 个 [Category.*] 模块，其中有 109 个没有 Require Components.v。Riehl 的例子是关于 Top 上的 PATH 分量的，其重点不在于集合本身，而在于函子：π₀ 的函子性不是手工验证的，而是取自他命题 3.3.1 的余极限函子。这两个概念之间的关系如下维基百科关于局部连通空间的文章所述：“因为路径连通集是连通的，所以我们有 PC_x ⊆ C_x”，并且“对于局部路径连通空间，连通分量和路径分量一致”；拓扑学家所说的正弦曲线是它们不一致的例子。nLab 上关于连通空间的页面也有提到相同的函子，“π₀ : Top → Set 是一个函子，它将每个空间 X 对应到其路径分量集合”，并且其证明 π₀ 保持有限积的方式是将其视为 hom(I, −) 和 hom(1, −) 这两个函子的自反余等化器，这两个函子由 P 打包。同一页面警告说，在构造数学中，连通性的经典定义“已不再需要是等价的”，这就是下面证明的连通性以其现有形式陈述的原因。编码。空格是 Instance/Top/Prop.v 中的 [PTop]，其 homs 位于点的宇宙中，根据维护者对 Top 问题的既定决定：在类型值的 [Top] 上，hom 集位于点之上（Instance/Top/Prop.v 的头部），因此 Top(I, X) 不会是 [Sets] 中点所在的对象。[PHomSetoid A X] 是 [PTopCat] 作为 [Sets@{o so}] 的对象的 hom-setoid，因此 Riehl 的 Path(X) 和 Point(X) 是 [PHomSetoid PInterval X] 和 [PHomSetoid PPoint X]（[PPathPair_paths], [PPathPair_points]）；他展示的两个同构在这里是恒等映射。间隔 I 是标准库构造的柯西实数中的 [0,1]：[PInterval] 是 Instance/Top/Subspace.v 的子空间 [PSub]，属于 Instance/Top/Circle.v 的线 [PRLine] 上的 [IvalSetoid]，实数 x 满足 0 ≤ x ≤ 1，在 [CRealEq] 下。经典的 [R] 未加载：
 一个需要此文件的临时文件 [Print Libraries] 列出了八个标准库实数模块，其中七个在 Reals/Cauchy 下，第八个在 Reals/Abstract/ConstructiveReals 下，这是 ConstructiveRcomplete.v 所需要的。Instance/Top/Circle.v 的头部记录了 Instance/Top/Interval.v 的经典 [I_Top] 所承载的公理。端点包含 0, 1 : ∗ ⇉ I 分别是 [ival_end0] 和 [ival_end1]，从单点空间 [PPoint] 映射出的映射在 [ival_zero] 和 [ival_one]（[ppoint_at]）。P 和 π₀，以及由此得出的函子性。[PPathPair_obj X] 是 Instance/Parallel.v 的 [APair]，表示两个预组合 [pprecomp X ival_end0] 和 [pprecomp X ival_end1]：它在 [(true; ParOne)] 上的箭头是 ev₀，在 [(false; ParTwo)] 上的箭头是 ev₁（[PPathPair_ev0], [PPathPair_ev1]）。[PPathPair]，也就是 Riehl 的 P，将箭头 h 映射为在路径和点上的后组合（[PPathPair_map], [PPathPair_fmap_paths]）；它的余域 [ParSets] 是 Instance/Fun.v 的 [Fun Parallel Sets]，即 Riehl 的 Set^{•⇉•}，并显式写出了其宇宙。P 是手动编写的：Riehl 的原文通过预组合定义它，并保留 π₀ 的余极限函子。也尝试导出它作为 Yoneda 嵌入 [Curried_CoHom PTopCat] 后跟 Theory/Kan/Extension.v 的沿端点对的预组合 [Induced]，在 [PTopCat^op] 中，但被拒绝：“宇宙不一致：无法强制 ... = o 因为 o < ...”<= ...
 Test/ProbeComponents462.v 的 N12，除了被接受的端点对 [p462_iota] 和 Yoneda 嵌入 [p462_yoneda] 外。[Fun] 的块将其同态宇宙下界限制在其域的对象宇宙（[u <= u4]），对于 [PTopCat^op]，该对象宇宙是 [so]，上界为 [o]，而复合要求 [o]。[PPi0] 是 [ColimitFunctor PathColim ◯ PPathPair]：#353 的余极限函子（Adjunction/Diagonal/Limit.v）在 Instance/Sets/Cocomplete.v 所选的 [Parallel] 形状（[PathColim]）上的余极限。在此文件中没有证明 π₀ 的函子律。[PPi0] 的箭头部分是 [Colim_map PathColim (PPathPair_map h)]（[PPi0_fmap]），其律由 [ColimitFunctor] 和 [PPathPair] 构成，由 [Compose] 组合。Riehl 在命题 3.3.1 证明前的评论，即该函子“需要任意选择一个极限”，没有对应内容：[Sets_Cocomplete] 将每个余极限作为数据提供，而 [Print Assumptions] 没有找到任何公理（如下）。回读：余极限是 Riehl 的商。Instance/Sets/Cocomplete.v 构建了一个余极限，方法是将图中的对象的并集在其箭头生成的关系下进行商，因此 [PPi0 X] 的一个元素是一个对 (ParX；一条路径) 或 (ParY；一个点)，当 [colim_rel] 将它们关联时，两者相等（[PPi0_carrier]，[PPi0_equiv]）。[Sets] 的两个同构将其回读为 Riehl 的等化器。[PPi0_coeq_iso X] 将其与 Instance/Sets/Coequalizer.v 中关于 Point(X) 的 ev₀ 和 ev₁ 的 [SetsCoeq] 识别：前向映射是进入 Structure/Coequalizer.v 的 [is_coequalizer_cocone] 的中介映射，后向映射是 [ParY] 处的注入。[PPi0_points_iso X] 将其与 X 本身的点集上两个评估 [SetsCoeq]、[path_at X ival_zero] 和 [path_at X ival_one] 进行识别：Riehl 所说的“X 中点的集合关于将任何一对由路径连接的点识别的关系的商”。该关系是 [coeq_rel]，由成对的 (γ 0, γ 1) 以及点自身的相等生成的等价关系，因此无论是否存在一条路径将其连接，通过一系列路径连接的两个点都会被识别；“由一条路径连接”可以通过路径的级联来实现传递性，但这里没有构造。在代表元上，两个同构的映射如应有的那样（[ppi0_to_coeq_point]，[ppi0_to_coeq_path]，[ppi0_from_coeq_point]，[ppi0_to_points_point]，[ppi0_from_points_at]），并且[PPi0]在箭头h上的导出作用是在两种代表元（[PPi0_fmap_point]，[PPi0_fmap_path]）上进行h的后组合：通过转换恢复的手写函子性。该区间对于映射到  [PBool] 的函数是连通的。 [interval_bool_endpoints] ：每个连续的 γ ： [PInterval] → [PBool] 都在两个端点取相同的值。证明方法是二分法。如果 γ 在 0 时为 [false]，在 1 时为 [true]，在有理点处对 [0,1] 进行二分，可以保持左端为 [false]，右端为 [true]（[ibis_stage]，[ibis_inv]）；情况区分基于 γ 的布尔值，因此不涉及实数的比较。左端点形成一个具有模量的柯西序列（[ibis_seq_cauchy]）；其极限是标准库的 [Rcauchy_complete]（Reals/Cauchy/ConstructiveRcomplete.v，其 [Print Assumptions] 输出“在全局上下文下封闭”，在临时文件中测量），并且属于 [0,1]（[ibis_lim_ival]）。γ 在极限附近的一个球体上是常数，并且左端和右端都进入那个球体（[ibis_contra]）；另一种情况，[true] 在 0 处和 [false] 在 1 处，是 Components.v 取反后的情况 [swap_set]。[interval_bool_constant] 将这个陈述扩展到任意两个点 s 和 t，沿着线段 [ival_segment a]，t ↦ t·a，这些是路径，因为乘以绝对值不大于 1 的实数会把每个球体映射到相同半径的球体中（[rball_scale]）。这是连通性的两点形式，仅映射到 [PBool]（下面未给出），并且 [interval_PConnectedBool] 以 Components.v 的形式 [PConnectedBool PInterval] 陈述，通过转换得到。经典对应物是 Instance/Top/FundamentalGroupoid.v 的 [interval_to_discrete_constant]，基于 Type 值的 [Top] 和经典实数：一个最上界论证，对于每个离散目标，其等式是可判定的（[interval_to_discrete_constant_dec]），该判定器使得上确界的谓词成为一个命题。这里的二分法在有理点处根据 γ 的值进行分割，对于 [PBool]，这是一个布尔值，因此它对 [PBool] 的限制起到了该判定器的作用。非空性。区间的 π₀ 是单点：[PPi0_PInterval_iso] 是 [Sets] 与单点集合同构，每个代表通过从 0 到它的线段（[pinterval_point_rel]、[pinterval_rel]）连接到 0 的类。两点离散空间的 π₀ 有两个点：[Pi0_PBool_two] 反驳 Instance/Top/Subspace.v 的 [ppoint_true] 和 [ppoint_false] 类一致的说法，通过从余极限中到 [pi0_bool_cocone] 的中介，余锥到 [bool]，其 [ParTwo] 腿通过 [interval_bool_constant] 保持一致；并且 [PPi0_PBool_iso] 是 [Sets] 与 [bool_setoid_object] 的同构。所以 [PPi0] 标识路径连接的点，并分开两点没有路径连接的情况。优势。在 [eq_refl] 中，文件的所有 18 个 [Example]：
 [PPathPair_paths]、[PPathPair_points]、[PPathPair_ev0]、
 [PPathPair_ev1]、[PPathPair_fmap_paths]、[PPi0_fobj]、[PPi0_fmap]、
 [PPi0_carrier]、[PPi0_equiv]、[PPi0_inj_point]、[PPi0_fmap_point]、
 [PPi0_fmap_path]，上述同构映射的五个回读，以及 [ival_segment_map]。仅到 [≈]：[PPi0] 的函子定律。在一个代表性 (ParY; x) 上，[eq_refl] 处的恒等定律被拒绝，“无法统一”（Test/ProbeComponents462.v 中的 N10，与 ZZ158WZZ、ZZ159WZZ 的定律并列）：[pcompose (pid X) x] 和 [x] 的底层函数通过转换（[p462_id_fun]）是一致的，但两个集合同构映射不一致（“无法统一 pmap (pcompose (pid X) x) 和 pmap x”，N11），它们的遵守性证明构建方式不同。更正 (#1347)：现在两者都在 [eq_refl] 处保持，N10 和 N11 是该探针的控制，因为 Instance/Sets.v 将其身份和复合的正确性字段作为项给出。证明方法不同，但使两个集合映射区分开的是标准库：实例解析放入 [pcompose (pid X) x] 映射部分的身份和复合的正确性字段的不透明引理。直到 [≈] 也是如此：四个同构定律，其证人是 [colim_rel] 和 [coeq_rel] 数据，以及 [ival_segment_0]、[ival_segment_1]（[CRealEq]，不是转换）。[interval_bool_endpoints] 和 [interval_bool_constant] 是布尔值的莱布尼茨等式，[PBool] 的等式是莱布尼茨；[Pi0_PBool_two] 是反驳。[Print Assumptions] 对 [Print Module] 列表中的所有 126 个常量及其 28 个 [Program] 义务打印“在全局上下文下封闭”；该文件未声明任何记录或归纳类型，因此没有构造函数可添加。宇宙，由[About]在[Set Printing Universes]下读取，共126个常数。绑定器：[@{}]处的16个常数（有理数和实数运算：[ival_pred]，它的两个引理，[rball_scale]，[ival_mult_pred]以及11个[ibis_]有理数常数）；[@{o}]处的44个常数（区间，其点，缩放和线段，[ppoint_at]，[PHomSetoid]，二分法，两个连通性定理和[interval_PConnectedBool]）；[@{o so}]处的10个常数（[pprecomp]，[ppostcomp]，[path_at]，[pbool_at_zero]，[pbool_at_point]及其义务）；[@{o so p}]处的27个常数（图[PPathPair_obj]，[PathColim]，回读映射，以及区间和[PBool]类的关系）；[@{o so p f}]处的29个常数（[ParSets]，[PPathPair]，[PPi0]以及关于[PPi0]的所有陈述）。[o] 是点的宇宙，[so] 是 [PTopCat@{o so}] 和 [Sets@{o so}] 的对象宇宙，[o < so]、绑定的 [PTopCat] 和 [Sets] 承载它。[p] 是形状 [Parallel@{p o}] 的对象宇宙，[p <= o] 被强制：从 [PathColim] 的一个草稿副本的绑定器中省略，[About] 将其读回，从 [Sets_Cocomplete] 自己的块（[ud <= uc]、[uc = uo]）推断出来。[f] 是 [Fun] 的辅助宇宙，[o < f] 以相同方式被强制，[Fun] 自己的 [u0 < u5]。两个绑定器是可扩展的，[ibis_cv_ge@{o +}] 和 [ibis_cv_le@{o +}]：在关闭的 [@{o}] 下，Coq 8.19.2 和 8.20.1 都拒绝它们，“Universe ...”未绑定，在他们创建的宇宙中进行详细说明，其中 Rocq 9.1 接受闭合形式；[About] 在 Rocq 9.1 和 Coq 8.19.2 上在 [@{o}] 处读取两者。21 个常量的块为空。此文件的任何宇宙都未在 [Set] 固定。在这126个块中，单词[Set]出现了530次：作为[Set < so]的28次，[PTopCat]的下界，在每个[@{o so p f}]块中都有，但在[ParSets]块中没有提到[PTopCat]；除此之外，仅作为标准库宇宙的严格下界，在96个块中出现[Set < Basics.flip.u0]、[.u1]和[.u2]，在93个块中出现[Set < Morphisms.Proper.u0]和[Set < Morphisms.Relations.u0]（首次由[PInterval]携带，自Instance/Top/Circle.v的[PRLine]起，其自身块包含全部五个），在14个块中出现[Set < Morphisms.GenericInstances.u0]和[Set < ConstructiveCauchyReals.CRealLt_morph.u0]（首次由[ibis_cv_ge]携带，其证明项名称为[CRealLt_morph]，即标准库中用于[CRealLt]下重写的实例，共19次）。[p <= so]（29个块）由[p <= o]和[o < so]推导得出。剩下的上限是 [<=]，作用于捐赠者在其自身模块中携带的全局宇宙：[compose.u*] 和 [ID.u0]（Instance/Sets.v 的 setoid 映射，首先作用于 [pprecomp] 的义务），[Logic_lemmas.equality.u0]（Instance/Sets.v 的 [unit_setoid_object] 和 [bool_setoid_object]，首先作用于 [ppoint_at]），[False_rect.u0]（[APair] 自身的上限，首先作用于 [PPathPair_obj]），[eq_rect.u0]、[eq_rect.u1]、[Projections.u0] 和 [Projections.u1]（[Sets_Cocomplete] 的，首先作用于 [PathColim]），[o <= Projections.u0] 作用于 Instance/Sets/Coequalizer.v 构建的六个常量 [sets_coeq_IsCoequalizer]，其自身模块拥有它（首先作用于 [ppi0_to_coeq]）；[eq_ind.u0] 和 [eq_ind_r.u0]，首次出现在该文件自身的证明 [ibis_contra] 和 [interval_bool_endpoints] 中，没有它们的任何捐赠者常量被孤立为承载者；以及 [eq_rect_r.u1]，也首先作用于 [interval_bool_endpoints]，Instance/Top/Components.v 的[swap_set] 在它自己的区块中携带（九个区块，[PPi0_PBool_iso] 在其中的第一个义务，它从自己的证明中获得它）。

 未传送。——从路径分支到局部连通空间上 Mac Lane 连通分支的比较 π₀ → C（Instance/Top/Components.v 中的函子）。将一个路径类发送到一个分支需要每条路径保持在同一个分支中，也就是说，在 Instance/Top/Components.v 的 [PConnected] 形式中区间是连通的（它映射到命题集合的离散空间时是常数），不仅仅是映射到 [PBool]；上面的二分法在映射的布尔值上拆分，而一般离散目标的等式可能不可判定。没有找到该形式的构造性证明，这里也没有说明相关内容。比较还会跨越余域的差异：[PPi0] 落在 [Sets] 中，它的等式 [colim_rel] 是类型值，其中 C 落在 Components.v 的 [PSets] 中，即命题集。- 间隔的连通性以任何形式，但不是两点形式（[interval_PConnectedBool]）：不是 Components.v 的 [PConnected]，即带有命题值局部常量谓词的形式，也不是其 [PConnectedSep]，即不存在被两个不相交开的集合分开的情况。- 路径的连接和反转，“由一条路径连接”的传递性，以及任何在 [PTopCat] 上的基本群oid（Instance/Top/FundamentalGroupoid.v 的则是在类型值 [Top] 和经典实数之上的）。- 任何其他空间的 π₀。没有构建路径，只构建了区间的各段，因此 π₀ 仅对 [PInterval] 和 [PBool] 计算；特别地，没有构建进入有限非离散空间的路径，也没有计算其中的 π₀。——对类型值 [Top] 的 π₀，以及 nLab 页面证明的 π₀ 对积与余积的保持。——从 Yoneda 嵌入推导 P 本身（被拒绝，见上文 N12）。
*)

#[local] Obligation Tactic := idtac.

(* * ** The unit interval over the constructive reals / * ** 构造实数上的单位区间 *)

Definition ival_pred@{} (x : CReal) : Prop :=
  CRealLe (inject_Q 0) x /\ CRealLe x (inject_Q 1).

(* The points of [0,1]: reals with the two bounds, compared as reals. / [0,1] 的点：具有两个界的实数，作为实数进行比较。 *)
Program Definition IvalSetoid@{o} : SetoidObject@{o o} := {|
  carrier   := { x : CReal | ival_pred x };
  is_setoid := {| equiv := fun a b => CRealEq (proj1_sig a) (proj1_sig b) |}
|}.
Next Obligation.
  constructor.
  - intro x; exact (CRealEq_refl _).
  - intros x y H; exact (CRealEq_sym _ _ H).
  - intros x y z H1 H2; exact (CRealEq_trans _ _ _ H1 H2).
Qed.

Program Definition ival_incl@{o} :
  SetoidMorphism@{o o o} IvalSetoid@{o} RLine_setoid@{o} := {|
  morphism := fun a => proj1_sig a
|}.
Next Obligation. intros a b H; exact H. Qed.

(* Riehl's I: the subspace of the line on [0,1]. / Riehl 的 I：在 [0,1] 上的直线子空间。 *)
Definition PInterval@{o} : PTop@{o} :=
  PSub PRLine@{o} IvalSetoid@{o} ival_incl@{o}.

Lemma ival_pred_0@{} : ival_pred (inject_Q 0).
Proof. split; [apply CRealLe_refl|apply inject_Q_le; discriminate]. Qed.

Lemma ival_pred_1@{} : ival_pred (inject_Q 1).
Proof. split; [apply inject_Q_le; discriminate|apply CRealLe_refl]. Qed.

Definition ival_zero@{o} : IvalSetoid@{o} :=
  exist _ (inject_Q 0) ival_pred_0.

Definition ival_one@{o} : IvalSetoid@{o} :=
  exist _ (inject_Q 1) ival_pred_1.

(* A point of a space, as a map out of the one-point space. / 空间的一个点，作为从一点空间映射出来的地图。 *)
Definition ppoint_at@{o} (X : PTop@{o}) (x : X) : PMor@{o} PPoint@{o} X :=
  pdisc_mor unit_setoid_object@{o o} X (pconst unit_setoid_object@{o o} X x).

(* Riehl's endpoint inclusions 0, 1 : ∗ ⇉ I. / Riehl 的端点包含 0, 1 ：∗ ⇉ I。 *)
Definition ival_end0@{o} : PMor@{o} PPoint@{o} PInterval@{o} :=
  ppoint_at@{o} PInterval@{o} ival_zero@{o}.

Definition ival_end1@{o} : PMor@{o} PPoint@{o} PInterval@{o} :=
  ppoint_at@{o} PInterval@{o} ival_one@{o}.

(** ** Riehl's P : Top → Set^{•⇉•} / ** Riehl 的 P : 拓扑 → Set^{•⇉•} *)

(* A hom-set of [PTopCat], as an object of [Sets]: Top(A, X). / 作为 [Sets] 的一个对象，[PTopCat] 的同态集：Top(A, X)。 *)
Definition PHomSetoid@{o} (A X : PTop@{o}) : SetoidObject@{o o} :=
  {| carrier := PMor@{o} A X; is_setoid := PMor_Setoid@{o} A X |}.

Program Definition pprecomp@{o so | o < so +} {A B : PTop@{o}}
  (X : PTop@{o}) (k : PMor@{o} A B) :
  PHomSetoid@{o} B X ~{Sets@{o so}}~> PHomSetoid@{o} A X := {|
  morphism := fun q => pcompose q k
|}.
Next Obligation. intros A B X k q r H a; exact (H _). Qed.

Program Definition ppostcomp@{o so | o < so +} (A : PTop@{o})
  {X Y : PTop@{o}} (h : PMor@{o} X Y) :
  PHomSetoid@{o} A X ~{Sets@{o so}}~> PHomSetoid@{o} A Y := {|
  morphism := fun q => pcompose h q
|}.
Next Obligation.
  intros A X Y h q r H a. simpl. exact (proper_morphism (pmap h) _ _ (H a)).
Qed.

(* Riehl's P X: the parallel pair ev₀, ev₁ : Path(X) ⇉ Point(X), the precompositions with the two endpoint inclusions. / Riehl 的 P X：平行对 ev₀, ev₁ : Path(X) ⇉ Point(X)，与两个端点包含的预组合。 *)
Definition PPathPair_obj@{o so p | o < so, p <= o +} (X : PTop@{o}) :
  Parallel@{p o} ⟶ Sets@{o so} :=
  APair (pprecomp@{o so} X ival_end0@{o}) (pprecomp@{o so} X ival_end1@{o}).

Example PPathPair_paths@{o so p | o < so, p <= o +} (X : PTop@{o}) :
  fobj[PPathPair_obj@{o so p} X] ParX = PHomSetoid@{o} PInterval@{o} X
  := eq_refl.

Example PPathPair_points@{o so p | o < so, p <= o +} (X : PTop@{o}) :
  fobj[PPathPair_obj@{o so p} X] ParY = PHomSetoid@{o} PPoint@{o} X
  := eq_refl.

Example PPathPair_ev0@{o so p | o < so, p <= o +} (X : PTop@{o}) :
  fmap[PPathPair_obj@{o so p} X]
    ((true; ParOne) : ParX ~{Parallel@{p o}}~> ParY)
    = pprecomp@{o so} X ival_end0@{o} := eq_refl.

Example PPathPair_ev1@{o so p | o < so, p <= o +} (X : PTop@{o}) :
  fmap[PPathPair_obj@{o so p} X]
    ((false; ParTwo) : ParX ~{Parallel@{p o}}~> ParY)
    = pprecomp@{o so} X ival_end1@{o} := eq_refl.

(* The action on an arrow h: postcomposition with h, on paths and on points. / 箭头 h 的作用：在路径和点上与 h 的后合成。 *)
Program Definition PPathPair_map@{o so p | o < so, p <= o +}
  {X Y : PTop@{o}} (h : PMor@{o} X Y) :
  PPathPair_obj@{o so p} X ⟹ PPathPair_obj@{o so p} Y := {|
  transform := fun j => match j with
    | ParX => ppostcomp@{o so} PInterval@{o} h
    | ParY => ppostcomp@{o so} PPoint@{o} h
    end
|}.
Next Obligation.
  intros X Y h [] [] [[] f] q; simpl;
    first [ reflexivity
          | exact (False_rect _ (ParHom_Y_X_absurd _ f))
          | exact (False_rect _ (ParHom_Id_false_absurd _ f)) ].
Qed.
Next Obligation.
  intros X Y h [] [] [[] f] q; simpl;
    first [ reflexivity
          | exact (False_rect _ (ParHom_Y_X_absurd _ f))
          | exact (False_rect _ (ParHom_Id_false_absurd _ f)) ].
Qed.

(*
 Riehl's Set^{•⇉•}, with its universes written out: functors at [so],
 transformations at [o], the levels of [Sets@{o so}] itself. 

 --------
 Riehl 的集合^{•⇉•}，它的宇宙写出如下：在 [so] 的函子，
 在 [o] 的变换，[Sets@{o so}] 本身的层级。
*)
Definition ParSets@{o so p f | o < so, p <= o, o < f +} :
  Category@{so o o} :=
  @Fun@{p o so o so o f} Parallel@{p o} Sets@{o so}.

Program Definition PPathPair@{o so p f | o < so, p <= o, o < f +} :
  PTopCat@{o so} ⟶ ParSets@{o so p f} := {|
  fobj := PPathPair_obj@{o so p};
  fmap := fun X Y h => PPathPair_map@{o so p} h
|}.
Next Obligation.
  intros X Y f g H [] q; simpl; intro t; exact (H _).
Qed.
Next Obligation. intros X [] q t; reflexivity. Qed.
Next Obligation. intros X Y Z f g [] q t; reflexivity. Qed.

Example PPathPair_fmap_paths@{o so p f | o < so, p <= o, o < f +}
  {X Y : PTop@{o}} (h : PMor@{o} X Y) :
  transform[fmap[PPathPair@{o so p f}] h] ParX
    = ppostcomp@{o so} PInterval@{o} h := eq_refl.

(** ** π₀ := colim ∘ P *)

(* The chosen colimits of [Sets] at the walking parallel pair. / 在行走平行对上的 [Sets] 的选定余极限。 *)
Definition PathColim@{o so p | o < so, p <= o +} :
  HasColimitsOfShape Parallel@{p o} Sets@{o so} :=
  Cocomplete_HasColimitsOfShape Sets_Cocomplete Parallel@{p o}.

(*
 Riehl's path components functor.  Its functoriality is the colimit
 functor's; nothing below proves a functor law. 

 --------
 Riehl 的路径分量函子。它的函子性是余极限函子的；下面没有任何内容证明函子律。
*)
Definition PPi0@{o so p f | o < so, p <= o, o < f +} :
  PTopCat@{o so} ⟶ Sets@{o so} :=
  ColimitFunctor PathColim@{o so p} ◯ PPathPair@{o so p f}.

Example PPi0_fobj@{o so p f | o < so, p <= o, o < f +} (X : PTop@{o}) :
  fobj[PPi0@{o so p f}] X
    = colim_obj PathColim@{o so p} (PPathPair_obj@{o so p} X) := eq_refl.

Example PPi0_fmap@{o so p f | o < so, p <= o, o < f +} {X Y : PTop@{o}}
  (h : PMor@{o} X Y) :
  fmap[PPi0@{o so p f}] h
    = Colim_map PathColim@{o so p} (PPathPair_map@{o so p} h) := eq_refl.

(*
 What the colimit is, by conversion: pairs (ParX; a path) and
 (ParY; a point), under the relation the diagram's arrows generate. 

 --------
 通过转换，余极限是什么：对 (ParX; 一条路径) 和 (ParY; 一个点)，在图的箭头生成的关系下。
*)
Example PPi0_carrier@{o so p f | o < so, p <= o, o < f +} (X : PTop@{o}) :
  carrier (fobj[PPi0@{o so p f}] X)
    = { j : ParObj & carrier (fobj[PPathPair_obj@{o so p} X] j) }
  := eq_refl.

Example PPi0_equiv@{o so p f | o < so, p <= o, o < f +} (X : PTop@{o})
  (c d : carrier (fobj[PPi0@{o so p f}] X)) :
  @equiv _ (fobj[PPi0@{o so p f}] X) c d
    = colim_rel (PPathPair_obj@{o so p} X) c d := eq_refl.

Example PPi0_inj_point@{o so p | o < so, p <= o +} (X : PTop@{o})
  (x : PMor@{o} PPoint@{o} X) :
  colim_inj PathColim@{o so p} (PPathPair_obj@{o so p} X) ParY x
    = existT _ ParY x := eq_refl.

(* The derived action on representatives IS postcomposition with h. / 在代表元上的导出作用是与 h 的后合成。 *)
Example PPi0_fmap_point@{o so p f | o < so, p <= o, o < f +}
  {X Y : PTop@{o}} (h : PMor@{o} X Y) (x : PMor@{o} PPoint@{o} X) :
  fmap[PPi0@{o so p f}] h (existT _ ParY x) = existT _ ParY (pcompose h x)
  := eq_refl.

Example PPi0_fmap_path@{o so p f | o < so, p <= o, o < f +}
  {X Y : PTop@{o}} (h : PMor@{o} X Y) (q : PMor@{o} PInterval@{o} X) :
  fmap[PPi0@{o so p f}] h (existT _ ParX q) = existT _ ParX (pcompose h q)
  := eq_refl.

(* * ** Readback: the colimit is the coequalizer of ev₀ and ev₁ / * ** 回读：余极限是 ev₀ 和 ev₁ 的余等化器 *)

Definition ppi0_to_coeq@{o so p | o < so, p <= o +} (X : PTop@{o}) :
  colim_obj PathColim@{o so p} (PPathPair_obj@{o so p} X) ~{Sets@{o so}}~>
  SetsCoeq (pprecomp@{o so} X ival_end0@{o})
           (pprecomp@{o so} X ival_end1@{o}) :=
  colim_med PathColim@{o so p}
    (is_coequalizer_cocone _ _
       (sets_coeq_IsCoequalizer (pprecomp@{o so} X ival_end0@{o})
                                (pprecomp@{o so} X ival_end1@{o}))).

Program Definition ppi0_from_coeq@{o so p | o < so, p <= o +}
  (X : PTop@{o}) :
  SetsCoeq (pprecomp@{o so} X ival_end0@{o})
           (pprecomp@{o so} X ival_end1@{o})
    ~{Sets@{o so}}~>
  colim_obj PathColim@{o so p} (PPathPair_obj@{o so p} X) := {|
  morphism := fun x => existT _ ParY x
|}.
Next Obligation.
  intros X x y H; simpl in *.
  induction H as [b1 b2 Hb | a | b1 b2 _ IH | b1 b2 b3 _ IH1 _ IH2].
  - exact (cr_point (PPathPair_obj X) ParY b1 b2 Hb).
  - exact (cr_trans _ _ _ _
             (cr_sym _ _ _
                (cr_glue (PPathPair_obj X) ParX ParY (true; ParOne) a))
             (cr_glue (PPathPair_obj X) ParX ParY (false; ParTwo) a)).
  - exact (cr_sym _ _ _ IH).
  - exact (cr_trans _ _ _ _ IH1 IH2).
Qed.

Program Definition PPi0_coeq_iso@{o so p f | o < so, p <= o, o < f +}
  (X : PTop@{o}) :
  fobj[PPi0@{o so p f}] X ≅[Sets@{o so}]
  SetsCoeq (pprecomp@{o so} X ival_end0@{o})
           (pprecomp@{o so} X ival_end1@{o}) := {|
  to   := ppi0_to_coeq@{o so p} X;
  from := ppi0_from_coeq@{o so p} X
|}.
Next Obligation.
  intros X x; simpl. apply coeq_rel_refl.
Qed.
Next Obligation.
  intros X [[] x]; simpl.
  - exact (cr_sym _ _ _
             (cr_glue (PPathPair_obj X) ParX ParY (true; ParOne) x)).
  - apply colim_rel_refl.
Qed.

Example ppi0_to_coeq_point@{o so p | o < so, p <= o +} (X : PTop@{o})
  (x : PMor@{o} PPoint@{o} X) :
  ppi0_to_coeq@{o so p} X (existT _ ParY x) = x := eq_refl.

Example ppi0_to_coeq_path@{o so p | o < so, p <= o +} (X : PTop@{o})
  (q : PMor@{o} PInterval@{o} X) :
  ppi0_to_coeq@{o so p} X (existT _ ParX q) = pcompose q ival_end0@{o}
  := eq_refl.

Example ppi0_from_coeq_point@{o so p | o < so, p <= o +} (X : PTop@{o})
  (x : PMor@{o} PPoint@{o} X) :
  ppi0_from_coeq@{o so p} X x = existT _ ParY x := eq_refl.

(** ** Readback on the points of X / ** 回顾关于X的要点 *)

(* Evaluation of a path at a point of the interval. / 在区间的某一点对路径进行评估。 *)
Program Definition path_at@{o so | o < so +} (X : PTop@{o})
  (t : IvalSetoid@{o}) :
  PHomSetoid@{o} PInterval@{o} X ~{Sets@{o so}}~> pt_carrier X := {|
  morphism := fun q => pmap q t
|}.
Next Obligation. intros X t q r H; exact (H t). Qed.

Definition ppi0_to_points_fun@{o so p | o < so, p <= o +} (X : PTop@{o})
  (c : colim_obj PathColim@{o so p} (PPathPair_obj@{o so p} X)) : X :=
  match c with
  | existT _ ParX q => pmap q ival_zero@{o}
  | existT _ ParY x => pmap x ttt
  end.

(* One case per generator of [colim_rel]: the arrow [(false; ParTwo)] is the only one that joins two different points, and it joins the two ends of a path. / [colim_rel] 的每个生成元一个情况：箭头 [(false; ParTwo)] 是唯一连接两个不同点的箭头，并且它连接了一条路径的两个端点。 *)
Lemma ppi0_to_points_respects@{o so p | o < so, p <= o +} (X : PTop@{o})
  (c d : colim_obj PathColim@{o so p} (PPathPair_obj@{o so p} X)) :
  c ≈ d →
  coeq_rel (path_at@{o so} X ival_zero@{o}) (path_at@{o so} X ival_one@{o})
    (ppi0_to_points_fun@{o so p} X c) (ppi0_to_points_fun@{o so p} X d).
Proof.
  intro H; simpl in H.
  induction H as [[] x y Hxy | [] [] [[] f] x | c d _ IH | c d e _ IH1 _ IH2];
    simpl.
  - apply cq_base; exact (Hxy ival_zero@{o}).
  - apply cq_base; exact (Hxy ttt).
  - apply coeq_rel_refl.
  - exact (False_rect _ (ParHom_Id_false_absurd _ f)).
  - apply coeq_rel_refl.
  - exact (cq_glue (path_at@{o so} X ival_zero@{o})
             (path_at@{o so} X ival_one@{o}) x).
  - exact (False_rect _ (ParHom_Y_X_absurd _ f)).
  - exact (False_rect _ (ParHom_Y_X_absurd _ f)).
  - apply coeq_rel_refl.
  - exact (False_rect _ (ParHom_Id_false_absurd _ f)).
  - exact (cq_sym _ _ _ _ IH).
  - exact (cq_trans _ _ _ _ _ IH1 IH2).
Qed.

Program Definition ppi0_to_points@{o so p | o < so, p <= o +}
  (X : PTop@{o}) :
  colim_obj PathColim@{o so p} (PPathPair_obj@{o so p} X) ~{Sets@{o so}}~>
  SetsCoeq (path_at@{o so} X ival_zero@{o}) (path_at@{o so} X ival_one@{o})
  := {|
  morphism := ppi0_to_points_fun@{o so p} X
|}.
Next Obligation.
  intros X c d H. exact (ppi0_to_points_respects@{o so p} X c d H).
Qed.

Program Definition ppi0_from_points@{o so p | o < so, p <= o +}
  (X : PTop@{o}) :
  SetsCoeq (path_at@{o so} X ival_zero@{o}) (path_at@{o so} X ival_one@{o})
    ~{Sets@{o so}}~>
  colim_obj PathColim@{o so p} (PPathPair_obj@{o so p} X) := {|
  morphism := fun x => existT _ ParY (ppoint_at@{o} X x)
|}.
Next Obligation.
  intros X x y H; simpl in *.
  induction H as [a b Hab | q | a b _ IH | a b c _ IH1 _ IH2].
  - apply (cr_point (PPathPair_obj X) ParY). intro u; exact Hab.
  - refine (cr_trans (PPathPair_obj X) _
              (existT _ ParY (pcompose q ival_end0@{o})) _ _ _).
    + apply (cr_point (PPathPair_obj X) ParY). intro u; reflexivity.
    + refine (cr_trans (PPathPair_obj X) _ (existT _ ParX q) _ _ _).
      * exact (cr_sym _ _ _ (cr_glue (PPathPair_obj X) ParX ParY
                                     (true; ParOne) q)).
      * refine (cr_trans (PPathPair_obj X) _
                  (existT _ ParY (pcompose q ival_end1@{o})) _ _ _).
        -- exact (cr_glue (PPathPair_obj X) ParX ParY (false; ParTwo) q).
        -- apply (cr_point (PPathPair_obj X) ParY). intro u; reflexivity.
  - exact (cr_sym _ _ _ IH).
  - exact (cr_trans _ _ _ _ IH1 IH2).
Qed.

(*
 Riehl's “quotient of the set of points in X by the relation that
 identifies any pair of points connected by a path”, the relation
 being the equivalence relation the paths generate. 

 --------
 Riehl 的“集合 X 中点的商，按将任意由路径连接的点对识别的关系”，该关系是路径生成的等价关系。
*)
Program Definition PPi0_points_iso@{o so p f | o < so, p <= o, o < f +}
  (X : PTop@{o}) :
  fobj[PPi0@{o so p f}] X ≅[Sets@{o so}]
  SetsCoeq (path_at@{o so} X ival_zero@{o}) (path_at@{o so} X ival_one@{o})
  := {|
  to   := ppi0_to_points@{o so p} X;
  from := ppi0_from_points@{o so p} X
|}.
Next Obligation.
  intros X x; simpl. apply coeq_rel_refl.
Qed.
Next Obligation.
  intros X [[] x]; simpl.
  - refine (cr_trans (PPathPair_obj X) _
              (existT _ ParY (pcompose x ival_end0@{o})) _ _ _).
    + apply (cr_point (PPathPair_obj X) ParY). intro u; reflexivity.
    + exact (cr_sym _ _ _ (cr_glue (PPathPair_obj X) ParX ParY
                                   (true; ParOne) x)).
  - apply (cr_point (PPathPair_obj X) ParY). intros []; reflexivity.
Qed.

Example ppi0_to_points_point@{o so p | o < so, p <= o +} (X : PTop@{o})
  (x : PMor@{o} PPoint@{o} X) :
  ppi0_to_points@{o so p} X (existT _ ParY x) = pmap x ttt := eq_refl.

Example ppi0_from_points_at@{o so p | o < so, p <= o +} (X : PTop@{o})
  (x : X) :
  ppi0_from_points@{o so p} X x = existT _ ParY (ppoint_at@{o} X x)
  := eq_refl.

(* * ** The interval is connected, for maps into the two-point space / * ** 区间是连通的，对于映射到两点空间的情况 *)

Section Bisection.

Local Open Scope Q_scope.

(* Rational points of the interval, clamped into [0,1]. / 被夹入 [0,1] 的区间有理点。 *)
Definition ibis_clamp@{} (q : Q) : Q := Qmax 0 (Qmin 1 q).

Lemma ibis_clamp_lo@{} (q : Q) : 0 <= ibis_clamp q.
Proof. apply Q.le_max_l. Qed.

Lemma ibis_clamp_hi@{} (q : Q) : ibis_clamp q <= 1.
Proof. apply Q.max_lub; [discriminate|apply Q.le_min_l]. Qed.

Lemma ibis_clamp_id@{} (q : Q) : 0 <= q → q <= 1 → ibis_clamp q == q.
Proof.
  intros H0 H1. unfold ibis_clamp.
  rewrite (Q.min_r 1 q H1). apply Q.max_r. exact H0.
Qed.

Lemma ibis_clamp_ival@{} (q : Q) : ival_pred (inject_Q (ibis_clamp q)).
Proof.
  split; apply inject_Q_le; [apply ibis_clamp_lo|apply ibis_clamp_hi].
Qed.

Definition ibis_pt@{o} (q : Q) : IvalSetoid@{o} :=
  exist _ (inject_Q (ibis_clamp q)) (ibis_clamp_ival q).

(* The value of a map into [PBool] at a rational point. / 在有理点处映射到 [PBool] 的值。 *)
Definition ibis_val@{o} (γ : PMor@{o} PInterval@{o} PBool@{o}) (q : Q) :
  bool := pmap γ (ibis_pt@{o} q).

Lemma ibis_val_proper@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (q r : Q) : q == r → ibis_val@{o} γ q = ibis_val@{o} γ r.
Proof.
  intro H. unfold ibis_val.
  apply (proper_morphism (pmap γ)). simpl.
  apply inject_Q_morph_T. unfold ibis_clamp. rewrite H. reflexivity.
Qed.

(* One bisection step keeps [false] on the left and [true] on the right; the case split is on a boolean value, so nothing about the reals is decided. / 一次二分法步骤将 [false] 保留在左侧，[true] 保留在右侧；情况分裂基于布尔值，因此关于实数没有任何决定。 *)
Definition ibis_step@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (ab : Q * Q) : Q * Q :=
  let m := (fst ab + snd ab) * (1 # 2) in
  if ibis_val@{o} γ m then (fst ab, m) else (m, snd ab).

Fixpoint ibis_stage@{o} (γ : PMor@{o} PInterval@{o} PBool@{o}) (n : nat) :
  Q * Q :=
  match n with
  | O => (0, 1)
  | S n => ibis_step@{o} γ (ibis_stage γ n)
  end.

Fixpoint ibis_width@{} (n : nat) : Q :=
  match n with O => 1 | S n => ibis_width n * (1 # 2) end.

Lemma ibis_width_pos@{} (n : nat) : 0 < ibis_width n.
Proof. induction n; simpl; [reflexivity|]. lra. Qed.

Lemma ibis_width_bound@{} (n : nat) :
  ibis_width n <= 1 # Pos.of_succ_nat n.
Proof.
  induction n; simpl; [apply Qle_refl|].
  apply (Qle_trans _ ((1 # Pos.of_succ_nat n) * (1 # 2))).
  - apply Qmult_le_compat_r; [exact IHn|discriminate].
  - unfold Qle, Qmult. cbn [Qnum Qden].
    rewrite ?Pos2Z.inj_mul.
    pose proof (Zpos_P_of_succ_nat n).
    pose proof (Zpos_P_of_succ_nat (S n)).
    lia.
Qed.

Lemma ibis_width_mono@{} (n k : nat) : ibis_width (k + n) <= ibis_width n.
Proof.
  induction k; simpl; [apply Qle_refl|].
  pose proof (ibis_width_pos (k + n)). lra.
Qed.

Lemma ibis_inv@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true) (n : nat) :
  ibis_val@{o} γ (fst (ibis_stage@{o} γ n)) = false /\
  ibis_val@{o} γ (snd (ibis_stage@{o} γ n)) = true /\
  snd (ibis_stage@{o} γ n) - fst (ibis_stage@{o} γ n) == ibis_width n /\
  0 <= fst (ibis_stage@{o} γ n) /\ snd (ibis_stage@{o} γ n) <= 1.
Proof.
  induction n as [|n [Ha [Hb [Hw [H0 H1]]]]]; simpl.
  - split; [exact g0|].
    split; [exact g1|split; [reflexivity|split; discriminate]].
  - unfold ibis_step. destruct (ibis_stage γ n) as [a b]; simpl in *.
    pose proof (ibis_width_pos n).
    destruct (ibis_val γ ((a + b) * (1 # 2))) eqn:Hm; simpl.
    + split; [exact Ha|split; [exact Hm|split; [lra|split; lra]]].
    + split; [exact Hm|split; [exact Hb|split; [lra|split; lra]]].
Qed.

Lemma ibis_nest@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true)
  (n k : nat) :
  fst (ibis_stage@{o} γ n) <= fst (ibis_stage@{o} γ (k + n)) /\
  snd (ibis_stage@{o} γ (k + n)) <= snd (ibis_stage@{o} γ n).
Proof.
  induction k as [|k [IHa IHb]]; simpl; [split; apply Qle_refl|].
  pose proof (ibis_inv γ g0 g1 (k + n)) as [_ [_ [Hw _]]].
  pose proof (ibis_width_pos (k + n)).
  unfold ibis_step. destruct (ibis_stage γ (k + n)) as [a b]; simpl in *.
  destruct (ibis_val γ ((a + b) * (1 # 2))); simpl; split; lra.
Qed.

Lemma ibis_left_close@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true)
  (n i j : nat) : (n <= i)%nat → (n <= j)%nat →
  Qabs (fst (ibis_stage@{o} γ i) - fst (ibis_stage@{o} γ j))
    <= ibis_width n.
Proof.
  intros Hi Hj.
  destruct (Nat.le_exists_sub n i Hi) as [ki [-> _]].
  destruct (Nat.le_exists_sub n j Hj) as [kj [-> _]].
  pose proof (ibis_nest γ g0 g1 n ki) as [Ai Bi].
  pose proof (ibis_nest γ g0 g1 n kj) as [Aj Bj].
  pose proof (ibis_inv γ g0 g1 n) as [_ [_ [Hw _]]].
  pose proof (ibis_inv γ g0 g1 (ki + n)) as [_ [_ [Hwi _]]].
  pose proof (ibis_inv γ g0 g1 (kj + n)) as [_ [_ [Hwj _]]].
  pose proof (ibis_width_pos (ki + n)).
  pose proof (ibis_width_pos (kj + n)).
  apply Qabs_case; intros; lra.
Qed.

Lemma ibis_width_small@{} (p : positive) (n : nat) :
  (Pos.to_nat p <= n)%nat → ibis_width n <= 1 # p.
Proof.
  intro H.
  destruct (Nat.le_exists_sub _ _ H) as [k [-> _]].
  apply (Qle_trans _ (ibis_width (Pos.to_nat p))); [apply ibis_width_mono|].
  apply (Qle_trans _ _ _ (ibis_width_bound _)).
  unfold Qle; simpl. rewrite Zpos_P_of_succ_nat, positive_nat_Z. lia.
Qed.

(* The left ends, as reals, form a Cauchy sequence with a modulus. / 左端作为实数，形成一个具有模的柯西序列。 *)
Definition ibis_seq@{o} (γ : PMor@{o} PInterval@{o} PBool@{o}) (i : nat) :
  CReal := inject_Q (fst (ibis_stage@{o} γ i)).

Lemma ibis_seq_cauchy@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true) :
  Un_cauchy_mod (ibis_seq@{o} γ).
Proof.
  intro p. exists (Pos.to_nat p). intros i j Hi Hj.
  unfold ibis_seq. rewrite inject_Q_minus, <- Qabs_Rabs.
  apply inject_Q_le.
  apply (Qle_trans _ _ _ (ibis_left_close γ g0 g1 (Pos.to_nat p) i j Hi Hj)).
  apply ibis_width_small, le_n.
Qed.

Definition ibis_lim@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true) : CReal :=
  projT1 (Rcauchy_complete (ibis_seq@{o} γ) (ibis_seq_cauchy@{o} γ g0 g1)).

Definition ibis_lim_cv@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true) :
  seq_cv (ibis_seq@{o} γ) (ibis_lim@{o} γ g0 g1) :=
  projT2 (Rcauchy_complete (ibis_seq@{o} γ) (ibis_seq_cauchy@{o} γ g0 g1)).

Lemma ibis_q_pos_inv@{} (d : Q) : 0 < d → { p : positive & 1 # p <= d }.
Proof.
  destruct d as [n m]. intro H. exists m.
  unfold Qlt in H; simpl in H. unfold Qle; simpl. nia.
Qed.

Lemma ibis_cv_ge@{o +} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true) (c : Q) :
  (∀ i, c <= fst (ibis_stage@{o} γ i)) →
  CRealLe (inject_Q c) (ibis_lim@{o} γ g0 g1).
Proof.
  intros Hc Hlt.
  destruct (CRealQ_dense _ _ Hlt) as [q [Hlq Hqc]].
  pose proof (lt_inject_Q _ _ Hqc) as Hq.
  destruct (ibis_q_pos_inv (c - q)) as [p Hp]; [lra|].
  destruct (ibis_lim_cv γ g0 g1 p) as [N HN].
  specialize (HN N (le_n N)).
  assert (H1 : CRealLt (ibis_seq γ N) (inject_Q c)).
  { apply (CReal_le_lt_trans _
             (CReal_plus (ibis_lim γ g0 g1) (inject_Q (1 # p)))).
    - apply (CReal_le_trans _ (CReal_plus (ibis_lim γ g0 g1)
               (CReal_abs (CReal_minus (ibis_seq γ N) (ibis_lim γ g0 g1))))).
      + apply (CReal_le_trans _ (CReal_plus (ibis_lim γ g0 g1)
                 (CReal_minus (ibis_seq γ N) (ibis_lim γ g0 g1)))).
        * unfold CReal_minus. rewrite CReal_plus_comm, CReal_plus_assoc,
            CReal_plus_opp_l, CReal_plus_0_r. apply CRealLe_refl.
        * apply CReal_plus_le_compat_l, CReal_le_abs.
      + apply CReal_plus_le_compat_l. exact HN.
    - apply (CReal_lt_le_trans _
               (CReal_plus (inject_Q q) (inject_Q (1 # p)))).
      + rewrite !(CReal_plus_comm _ (inject_Q (1 # p))).
        apply CReal_plus_lt_compat_l. exact Hlq.
      + rewrite <- inject_Q_plus. apply inject_Q_le. lra. }
  pose proof (lt_inject_Q _ _ H1). pose proof (Hc N). lra.
Qed.

Lemma ibis_cv_le@{o +} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true) (c : Q) :
  (∀ i, fst (ibis_stage@{o} γ i) <= c) →
  CRealLe (ibis_lim@{o} γ g0 g1) (inject_Q c).
Proof.
  intros Hc Hlt.
  destruct (CRealQ_dense _ _ Hlt) as [q [Hcq Hql]].
  pose proof (lt_inject_Q _ _ Hcq) as Hq.
  destruct (ibis_q_pos_inv (q - c)) as [p Hp]; [lra|].
  destruct (ibis_lim_cv γ g0 g1 p) as [N HN].
  specialize (HN N (le_n N)).
  assert (H1 : CRealLt (inject_Q c) (ibis_seq γ N)).
  { apply (CReal_le_lt_trans _
             (CReal_plus (inject_Q q) (inject_Q (- (1 # p))))).
    - rewrite <- inject_Q_plus. apply inject_Q_le. lra.
    - apply (CReal_lt_le_trans _
               (CReal_plus (ibis_lim γ g0 g1) (inject_Q (- (1 # p))))).
      + rewrite !(CReal_plus_comm _ (inject_Q (- (1 # p)))).
        apply CReal_plus_lt_compat_l. exact Hql.
      + rewrite CReal_abs_minus_sym in HN.
        apply (CReal_le_trans _ (CReal_plus (ibis_lim γ g0 g1)
                 (CReal_opp (CReal_abs
                    (CReal_minus (ibis_lim γ g0 g1) (ibis_seq γ N)))))).
        * apply CReal_plus_le_compat_l.
          rewrite opp_inject_Q. apply CReal_opp_ge_le_contravar. exact HN.
        * apply (CReal_le_trans _ (CReal_plus (ibis_lim γ g0 g1)
                   (CReal_opp (CReal_minus (ibis_lim γ g0 g1)
                                           (ibis_seq γ N))))).
          -- apply CReal_plus_le_compat_l. apply CReal_opp_ge_le_contravar.
             apply CReal_le_abs.
          -- unfold CReal_minus.
             rewrite CReal_opp_plus_distr, CReal_opp_involutive.
             rewrite <- CReal_plus_assoc, CReal_plus_opp_r, CReal_plus_0_l.
             apply CRealLe_refl. }
  pose proof (lt_inject_Q _ _ H1). pose proof (Hc N). lra.
Qed.

Lemma ibis_lim_ival@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true) :
  ival_pred (ibis_lim@{o} γ g0 g1).
Proof.
  split.
  - apply ibis_cv_ge. intro i.
    exact (proj1 (proj2 (proj2 (proj2 (ibis_inv γ g0 g1 i))))).
  - apply ibis_cv_le. intro i.
    pose proof (ibis_inv γ g0 g1 i) as [_ [_ [Hw [H0 H1]]]].
    pose proof (ibis_width_pos i). lra.
Qed.

Definition ibis_lim_pt@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true) :
  IvalSetoid@{o} :=
  exist _ (ibis_lim@{o} γ g0 g1) (ibis_lim_ival@{o} γ g0 g1).

Lemma ibis_seq_in@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true) (N : nat) :
  CRealEq (inject_Q (ibis_clamp (fst (ibis_stage@{o} γ N))))
          (ibis_seq@{o} γ N).
Proof.
  apply inject_Q_morph_T.
  pose proof (ibis_inv γ g0 g1 N) as [_ [_ [Hw [H0 H1]]]].
  pose proof (ibis_width_pos N). apply ibis_clamp_id; lra.
Qed.

Lemma ibis_right_in@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true) (N : nat) :
  CRealEq (inject_Q (ibis_clamp (snd (ibis_stage@{o} γ N))))
          (inject_Q (snd (ibis_stage@{o} γ N))).
Proof.
  apply inject_Q_morph_T.
  pose proof (ibis_inv γ g0 g1 N) as [_ [_ [Hw [H0 H1]]]].
  pose proof (ibis_width_pos N). apply ibis_clamp_id; lra.
Qed.

(*
 The map is constant on a ball about the limit, and both the left ends
 (valued [false]) and the right ends (valued [true]) enter every such
 ball. 

 --------
 在极限附近的一个球上，映射是恒定的，并且左右两端（值为 [false] 和 [true]）都会进入每一个这样的球。
*)
Theorem ibis_contra@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (g0 : ibis_val@{o} γ 0 = false) (g1 : ibis_val@{o} γ 1 = true) : False.
Proof.
  destruct (pmap γ (ibis_lim_pt γ g0 g1)) eqn:Hl.
  - assert (Ho : POpen PBool (fun b => b = true)).
    { intros x y Hxy Hx. simpl in Hxy. congruence. }
    destruct (pcont γ _ Ho) as [U [HU HUs]].
    pose proof (proj1 (HUs (ibis_lim_pt γ g0 g1)) Hl) as Ul.
    destruct (HU (ibis_lim γ g0 g1) Ul) as [e [He Hball]].
    destruct (ibis_q_pos_inv e He) as [p Hp].
    destruct (ibis_lim_cv γ g0 g1 p) as [N HN].
    specialize (HN N (le_n N)).
    assert (Hb : rball (ibis_lim γ g0 g1)
                   (inject_Q (ibis_clamp (fst (ibis_stage γ N)))) e).
    { unfold rball. rewrite (ibis_seq_in γ g0 g1 N).
      apply (CReal_le_trans _ _ _ HN). apply inject_Q_le. exact Hp. }
    pose proof (proj2 (HUs (ibis_pt (fst (ibis_stage γ N))))
                  (Hball _ Hb)) as Hg.
    pose proof (proj1 (ibis_inv γ g0 g1 N)) as Hf. unfold ibis_val in *.
    rewrite Hf in Hg. discriminate Hg.
  - assert (Ho : POpen PBool (fun b => b = false)).
    { intros x y Hxy Hx. simpl in Hxy. congruence. }
    destruct (pcont γ _ Ho) as [U [HU HUs]].
    pose proof (proj1 (HUs (ibis_lim_pt γ g0 g1)) Hl) as Ul.
    destruct (HU (ibis_lim γ g0 g1) Ul) as [e [He Hball]].
    destruct (ibis_q_pos_inv (e * (1 # 2))) as [p Hp]; [lra|].
    destruct (ibis_lim_cv γ g0 g1 p) as [N0 HN].
    pose (N := Nat.max N0 (Pos.to_nat p)).
    specialize (HN N (Nat.le_max_l _ _)).
    pose proof (ibis_width_small p N (Nat.le_max_r _ _)) as HW.
    pose proof (ibis_inv γ g0 g1 N) as [_ [Ht [Hw [H0 H1]]]].
    assert (Hb : rball (ibis_lim γ g0 g1)
                   (inject_Q (ibis_clamp (snd (ibis_stage γ N)))) e).
    { unfold rball. rewrite (ibis_right_in γ g0 g1 N).
      assert (E : CRealEq
                (CReal_minus (inject_Q (snd (ibis_stage γ N)))
                             (ibis_lim γ g0 g1))
                (CReal_plus
                   (CReal_minus (inject_Q (snd (ibis_stage γ N)))
                                (ibis_seq γ N))
                   (CReal_minus (ibis_seq γ N) (ibis_lim γ g0 g1)))).
      { unfold CReal_minus. ring. }
      rewrite E.
      apply (CReal_le_trans _ _ _ (CReal_abs_triang _ _)).
      apply (CReal_le_trans _
               (CReal_plus (inject_Q (1 # p)) (inject_Q (1 # p)))).
      - apply CReal_plus_le_compat; [|exact HN].
        unfold ibis_seq. rewrite inject_Q_minus, <- Qabs_Rabs.
        apply inject_Q_le.
        pose proof (ibis_width_pos N).
        apply Qabs_case; intros; lra.
      - rewrite <- inject_Q_plus. apply inject_Q_le. lra. }
    pose proof (proj2 (HUs (ibis_pt (snd (ibis_stage γ N))))
                  (Hball _ Hb)) as Hg.
    unfold ibis_val in *. rewrite Ht in Hg. discriminate Hg.
Qed.

End Bisection.

(* Every continuous map from the interval to [PBool] takes one value at the two endpoints. / 从区间到 [PBool] 的每个连续映射在两个端点处取一个值。 *)
Theorem interval_bool_endpoints@{o} (γ : PMor@{o} PInterval@{o} PBool@{o}) :
  pmap γ ival_zero@{o} = pmap γ ival_one@{o}.
Proof.
  assert (E0 : pmap γ ival_zero = ibis_val γ 0).
  { apply (proper_morphism (pmap γ)). simpl.
    apply inject_Q_morph_T. reflexivity. }
  assert (E1 : pmap γ ival_one = ibis_val γ 1).
  { apply (proper_morphism (pmap γ)). simpl.
    apply inject_Q_morph_T. reflexivity. }
  rewrite E0, E1.
  destruct (ibis_val γ 0) eqn:H0, (ibis_val γ 1) eqn:H1; try reflexivity.
  - exfalso.
    pose (nγ := pcompose (pdisc_mor bool_setoid_object@{o o} PBool
                            swap_set@{o}) γ).
    apply (ibis_contra nγ).
    + unfold ibis_val in *. simpl. rewrite H0. reflexivity.
    + unfold ibis_val in *. simpl. rewrite H1. reflexivity.
  - exfalso. exact (ibis_contra γ H0 H1).
Qed.

(** ** Straight-line paths / ** 直线路径 *)

(*
 Multiplication by a real of absolute value at most one carries a ball
 into the ball of the same radius. 

 --------
 乘以绝对值最多为一的实数会将一个球映射到相同半径的球中。
*)
Lemma rball_scale@{} (x r s : CReal) (e : Q) :
  CRealLe (CReal_abs x) (inject_Q 1) → rball r s e →
  rball (CReal_mult r x) (CReal_mult s x) e.
Proof.
  unfold rball; intros Hx b.
  assert (E : CRealEq (CReal_minus (CReal_mult s x) (CReal_mult r x))
                      (CReal_mult (CReal_minus s r) x)).
  { unfold CReal_minus. ring. }
  rewrite E, CReal_abs_mult.
  apply (CReal_le_trans _
           (CReal_mult (CReal_abs (CReal_minus s r)) (inject_Q 1))).
  - apply CReal_mult_le_compat_l; [apply CReal_abs_pos|exact Hx].
  - rewrite CReal_mult_1_r. exact b.
Qed.

Program Definition line_scale@{o} (x : CReal) :
  SetoidMorphism@{o o o} RLine_setoid@{o} RLine_setoid@{o} := {|
  morphism := fun r => CReal_mult r x
|}.
Next Obligation. intros x r s H; simpl in *. rewrite H. reflexivity. Qed.

Lemma pline_scale_cont@{o} (x : CReal)
  (Hx : CRealLe (CReal_abs x) (inject_Q 1)) :
  @PCont PRLine@{o} PRLine@{o} (line_scale@{o} x).
Proof.
  intros U HU r u. destruct (HU _ u) as [e [He Hb]].
  exists e. split; [exact He|].
  intros s b. apply Hb. exact (rball_scale x r s e Hx b).
Qed.

Definition pline_scale@{o} (x : CReal)
  (Hx : CRealLe (CReal_abs x) (inject_Q 1)) :
  PMor@{o} PRLine@{o} PRLine@{o} :=
  @Build_PMor PRLine PRLine (line_scale x) (pline_scale_cont x Hx).

Lemma ival_abs_le@{o} (a : IvalSetoid@{o}) :
  CRealLe (CReal_abs (proj1_sig a)) (inject_Q 1).
Proof.
  destruct a as [a [H0 H1]]; simpl.
  rewrite (CReal_abs_right a H0). exact H1.
Qed.

Lemma ival_mult_pred@{} (t a : CReal) :
  ival_pred t → ival_pred a → ival_pred (CReal_mult t a).
Proof.
  intros [Ht0 Ht1] [Ha0 Ha1]. split.
  - apply CReal_mult_le_0_compat; [exact Ht0|exact Ha0].
  - rewrite CReal_mult_comm.
    apply (CReal_le_trans _ (CReal_mult a (inject_Q 1))).
    + apply CReal_mult_le_compat_l; [exact Ha0|exact Ht1].
    + rewrite CReal_mult_1_r. exact Ha1.
Qed.

Program Definition ival_scale_map@{o} (a : IvalSetoid@{o}) :
  SetoidMorphism@{o o o} IvalSetoid@{o} IvalSetoid@{o} := {|
  morphism := fun t =>
    exist _ (CReal_mult (proj1_sig t) (proj1_sig a))
      (ival_mult_pred _ _ (proj2_sig t) (proj2_sig a))
|}.
Next Obligation. intros a t s H; simpl in *. rewrite H. reflexivity. Qed.

(*
 The segment from 0 to [a], t ↦ t·a, a path in the interval: continuous
 because its composite with the inclusion is a scaling of the line. 

 --------
 从 0 到 [a] 的线段，t ↦ t·a，是区间中的一条路径：连续的，因为它与包含映射的复合是线的缩放。
*)
Definition ival_segment@{o} (a : IvalSetoid@{o}) :
  PMor@{o} PInterval@{o} PInterval@{o} :=
  psub_lift PRLine@{o} IvalSetoid@{o} ival_incl@{o} PInterval@{o}
    (pcompose (pline_scale (proj1_sig a) (ival_abs_le a))
       (psub_incl PRLine@{o} IvalSetoid@{o} ival_incl@{o}))
    (ival_scale_map a) (fun t => CRealEq_refl _).

Example ival_segment_map@{o} (a t : IvalSetoid@{o}) :
  proj1_sig (pmap (ival_segment@{o} a) t)
    = CReal_mult (proj1_sig t) (proj1_sig a) := eq_refl.

Lemma ival_segment_0@{o} (a : IvalSetoid@{o}) :
  pmap (ival_segment@{o} a) ival_zero@{o} ≈ ival_zero@{o}.
Proof. simpl. apply CReal_mult_0_l. Qed.

Lemma ival_segment_1@{o} (a : IvalSetoid@{o}) :
  pmap (ival_segment@{o} a) ival_one@{o} ≈ a.
Proof. simpl. apply CReal_mult_1_l. Qed.

(*
 Every continuous map from the interval to [PBool] is constant:
 [interval_bool_endpoints] along the segment from 0 to each point. 

 --------
 从区间到  [PBool]  的每一个连续映射都是常数：沿从 0 到每个点的线段是  [interval_bool_endpoints] 。
*)
Theorem interval_bool_constant@{o} (γ : PMor@{o} PInterval@{o} PBool@{o})
  (s t : IvalSetoid@{o}) : pmap γ s = pmap γ t.
Proof.
  assert (H : ∀ a : IvalSetoid@{o}, pmap γ ival_zero = pmap γ a).
  { intro a.
    pose proof (interval_bool_endpoints (pcompose γ (ival_segment a))) as E.
    transitivity (pmap γ (pmap (ival_segment a) ival_zero)).
    - apply (proper_morphism (pmap γ)). symmetry. apply ival_segment_0.
    - transitivity (pmap γ (pmap (ival_segment a) ival_one)); [exact E|].
      apply (proper_morphism (pmap γ)). apply ival_segment_1. }
  rewrite <- (H s). exact (H t).
Qed.

(*
 The same statement, as Instance/Top/Components.v's two-point form of
 connectedness. 

 --------
 同样的陈述，作为 Instance/Top/Components.v 的连通性的两点形式。
*)
Definition interval_PConnectedBool@{o} : PConnectedBool PInterval@{o} :=
  interval_bool_constant@{o}.

(* * ** π₀ of the interval is one point / * ** 区间的 π₀ 是一个点 *)

Lemma pinterval_point_rel@{o so p | o < so, p <= o +}
  (x : PMor@{o} PPoint@{o} PInterval@{o}) :
  colim_rel (PPathPair_obj@{o so p} PInterval@{o})
    (existT _ ParY ival_end0@{o}) (existT _ ParY x).
Proof.
  set (a := pmap x ttt).
  refine (cr_trans (PPathPair_obj PInterval) _
            (existT _ ParY (pcompose (ival_segment a) ival_end0)) _ _ _).
  - apply (cr_point (PPathPair_obj PInterval) ParY).
    intro u; simpl. symmetry. apply CReal_mult_0_l.
  - refine (cr_trans (PPathPair_obj PInterval) _
              (existT _ ParX (ival_segment a)) _ _ _).
    + exact (cr_sym _ _ _ (cr_glue (PPathPair_obj PInterval) ParX ParY
                                   (true; ParOne) (ival_segment a))).
    + refine (cr_trans (PPathPair_obj PInterval) _
                (existT _ ParY (pcompose (ival_segment a) ival_end1))
                _ _ _).
      * exact (cr_glue (PPathPair_obj PInterval) ParX ParY
                       (false; ParTwo) (ival_segment a)).
      * apply (cr_point (PPathPair_obj PInterval) ParY).
        intros []. exact (ival_segment_1 a).
Qed.

Lemma pinterval_rel@{o so p | o < so, p <= o +}
  (c : colim_obj PathColim@{o so p}
         (PPathPair_obj@{o so p} PInterval@{o})) :
  colim_rel (PPathPair_obj@{o so p} PInterval@{o})
    (existT _ ParY ival_end0@{o}) c.
Proof.
  destruct c as [[] x].
  - refine (cr_trans (PPathPair_obj PInterval) _
              (existT _ ParY (pcompose x ival_end0)) _ _ _).
    + exact (pinterval_point_rel _).
    + exact (cr_sym _ _ _ (cr_glue (PPathPair_obj PInterval) ParX ParY
                                   (true; ParOne) x)).
  - exact (pinterval_point_rel x).
Qed.

Program Definition PPi0_PInterval_iso@{o so p f | o < so, p <= o, o < f +} :
  fobj[PPi0@{o so p f}] PInterval@{o} ≅[Sets@{o so}] unit_setoid_object@{o o}
  := {|
  to   := {| morphism := fun _ => ttt |};
  from := {| morphism := fun _ => existT _ ParY ival_end0@{o} |}
|}.
Next Obligation. intros c d _; reflexivity. Qed.
Next Obligation. intros u v _; apply colim_rel_refl. Qed.
Next Obligation. intros []; reflexivity. Qed.
Next Obligation. intro c. exact (pinterval_rel c). Qed.

(* * ** π₀ of the two-point discrete space has two points / * ** 两点离散空间的 π₀ 有两个点 *)

Program Definition pbool_at_zero@{o so | o < so +} :
  PHomSetoid@{o} PInterval@{o} PBool@{o} ~{Sets@{o so}}~>
  bool_setoid_object@{o o} := {|
  morphism := fun q => pmap q ival_zero@{o}
|}.
Next Obligation. intros q r H. exact (H _). Qed.

Program Definition pbool_at_point@{o so | o < so +} :
  PHomSetoid@{o} PPoint@{o} PBool@{o} ~{Sets@{o so}}~>
  bool_setoid_object@{o o} := {|
  morphism := fun x => pmap x ttt
|}.
Next Obligation. intros x y H. exact (H _). Qed.

(* The cocone to the two-point set; its [ParTwo] leg coheres because the interval is connected for maps into [PBool]. / 到二点集的余锥；它的 [ParTwo] 腿是一致的，因为映射到 [PBool] 的区间是连通的。 *)
Definition pi0_bool_cocone@{o so p | o < so, p <= o +} :
  Cocone (PPathPair_obj@{o so p} PBool@{o}).
Proof.
  unshelve refine (@Cocone_of _ _ (PPathPair_obj PBool) bool_setoid_object
    (fun j => match j with
              | ParX => pbool_at_zero
              | ParY => pbool_at_point
              end) _).
  intros [] [] [[] f] q; simpl;
    first [ reflexivity
          | exact (False_rect _ (ParHom_Y_X_absurd _ f))
          | exact (False_rect _ (ParHom_Id_false_absurd _ f))
          | idtac ].
  exact (interval_bool_constant q ival_one ival_zero).
Defined.

(* The two points of [PBool], Instance/Top/Subspace.v's [ppoint_true] and [ppoint_false], lie in different path components. / [PBool] 的两个点，Instance/Top/Subspace.v 的 [ppoint_true] 和 [ppoint_false]，位于不同的路径组件中。 *)
Theorem Pi0_PBool_two@{o so p f | o < so, p <= o, o < f +} :
  @equiv _ (fobj[PPi0@{o so p f}] PBool@{o})
    (colim_inj PathColim@{o so p} (PPathPair_obj@{o so p} PBool@{o}) ParY
       ppoint_true@{o})
    (colim_inj PathColim@{o so p} (PPathPair_obj@{o so p} PBool@{o}) ParY
       ppoint_false@{o}) → False.
Proof.
  intro H.
  pose proof (proper_morphism
                (colim_med PathColim pi0_bool_cocone) _ _ H) as H'.
  exact (PBool_points_distinct (eq_sym H')).
Qed.

Program Definition PPi0_PBool_iso@{o so p f | o < so, p <= o, o < f +} :
  fobj[PPi0@{o so p f}] PBool@{o} ≅[Sets@{o so}] bool_setoid_object@{o o}
  := {|
  to   := colim_med PathColim@{o so p} pi0_bool_cocone@{o so p};
  from := {| morphism := fun b =>
               existT _ ParY (ppoint_at@{o} PBool@{o} b) |}
|}.
Next Obligation. intros b c H; simpl in H; subst; apply colim_rel_refl. Qed.
Next Obligation. intro b; reflexivity. Qed.
Next Obligation.
  intros [[] x]; simpl.
  - refine (cr_trans (PPathPair_obj PBool) _
              (existT _ ParY (pcompose x ival_end0)) _ _ _).
    + apply (cr_point (PPathPair_obj PBool) ParY). intro u; reflexivity.
    + exact (cr_sym _ _ _ (cr_glue (PPathPair_obj PBool) ParX ParY
                                   (true; ParOne) x)).
  - apply (cr_point (PPathPair_obj PBool) ParY). intros []; reflexivity.
Qed.
