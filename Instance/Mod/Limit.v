Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Mod.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* * * Limits of R-modules are created by the forgetful functor to [Ab] / * * R-模的极限由到 [Ab] 的遗忘函子创建 *)

(*
 Mac Lane: Categories for the Working Mathematician, 2nd ed. (GTM 5),
 §V.7 Construction 1, book p. 128 (PDF p. 137)
 [maclane:V.7:construction1] -- the first premise of the
 construction (“K-Mod is small-complete”)
 §V.1 Theorems 2 and 3, book pp. 111-112 (PDF pp. 120-121)
 -- the creation argument itself
 §V.6 Theorem 2, book pp. 125-126 -- Freyd's GAFT, the theorem
 Construction 1 feeds
 nLab: https://ncatlab.org/nlab/show/created+limit
 nLab: https://ncatlab.org/nlab/show/limit#limits_in_categories_of_algebras
 nLab: https://ncatlab.org/nlab/show/Mod
 nLab: https://ncatlab.org/nlab/show/adjoint+functor+theorem
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_modules
 Riehl: Category Theory in Context, §5.6 Example 5.6.8

 Mac Lane's §V.7 Construction 1 obtains the tensor product of modules
 from the adjoint functor theorem rather than from generators and
 relations.  The theorem it invokes needs three things of the bilinear-
 maps functor's source: that the source is small-complete, that the
 functor is continuous, and that it has a solution set.  THIS FILE
 DELIVERS THE FIRST, and nothing else: [RMod_Complete], “K-Mod is
 small-complete”, together with the continuity of both forgetful
 functors, which the second premise will be checked against.  The
 bilinear-maps functor [Bilin] (Instance/Mod/Tensor.v), its
 continuity, the solution set and the adjoint-functor-theorem
 application are all elsewhere -- see NOT DELIVERED.

 ** THE ROUTE: ONE LEVEL UP FROM [Ab], NOT TWO DOWN TO [Sets]

 [RMod_Forget_Ab R] (Instance/Mod.v) STRICTLY CREATES every limit,
 and the completeness of [RMod R] is read off from the completeness of
 [Ab] rather than of [Sets].  Given a limiting cone [L] of abelian
 groups over the underlying diagram, there is exactly one scalar action
 on its apex making every projection a module homomorphism
 ([mlim_smul_unique], Mac Lane's §V.1 Theorem 2 in this instance), the
 resulting cone lies over [L] ON THE NOSE ([mlim_over_obj] and
 [mlim_over_legs] are both [eq_refl], because [RMod_Forget_Ab]'s object
 map is the [rm_ab] projection and its morphism map is [rm_hom]), it is
 limiting ([mlim_created]), and a cone of modules whose image is
 limiting is itself limiting ([rmod_reflects]).  Packaged with
 Structure/Limit/Creation.v's own classes --
 [RMod_Forget_Ab_StrictlyCreatesLimit], [RMod_Forget_Ab_CreatesLimit],
 [RMod_Forget_Ab_StrictlyCreatesLimits] and
 [RMod_Forget_Ab_creates_limits] -- from which the corollaries follow by
 application: [RMod_Complete] (Mac Lane's §V.1 Theorem 3),
 [RMod_Forget_Ab_creates_continuous], [RMod_Forget_Ab_PreservesAllLimits]
 and [RMod_Forget_Ab_reflects_limits].

 WHY THAT IS THE RIGHT LEVEL, AND WHAT IT COSTS.  A module is an abelian
 group with an action: Instance/Mod.v's [RModObject] EXTENDS
 Instance/Ab.v's [AbObject] by [rm_smul] with [rm_smul_respects] and
 four laws, and [rm_ab] is a coercion.  So exactly ONE operation is
 lifted here -- the action -- where the [Ab] template lifts three
 ([cmon_plus], [cmon_zero], [ab_neg]) and Instance/Grp/Limit.v lifts
 three as well.  The apex's abelian group is not constructed at all:
 [LimitMod]'s [rm_ab] IS [vertex_obj[L]], which is what makes
 [mlim_over_obj] hold by [eq_refl] rather than by an isomorphism.

 AND IT IS CHEAPER THAN THAT SUGGESTS, because the action is built as a
 MEDIATOR IN [Ab] rather than as a function on the carrier.  For a fixed
 scalar [r] the family [fun a => r · (leg j a)] is a homomorphism of
 abelian groups at every [j] -- additive by [rm_smul_distr_l], unital by
 Instance/Mod.v's [rm_smul_zero_r] -- and coherent by
 [rm_map_smul], so it is a cone in [Ab] over the same diagram
 ([mlim_smul_cone]).  Its mediator [mlim_smul_map] is by construction an
 [Ab]-morphism, and therefore [mlim_smul_distr_l] -- distributivity over
 addition of vectors -- is not proved here at all: it is
 [cmon_map_plus (mlim_smul_map r)], one citation.  The same remark makes
 respectfulness in the SECOND argument free.  The other four clauses
 ([mlim_smul_respects] in its first argument, [mlim_smul_distr_r],
 [mlim_smul_assoc], [mlim_smul_one]) are three lines each: apply joint
 monicity, rewrite the defining triangle [mlim_smul_triangle], apply the
 law in [K j].

 ** THE ENGINE IS BORROWED, NOT COPIED -- THE ONE PLACE THIS FILE
 DEPARTS FROM ITS TEMPLATE

 Every law below rests on [mlim_ext]: two elements of the apex agreeing
 at every leg are equal.  In [Sets] that is proved from the mediator's
 uniqueness with constant maps as probes (Instance/Ab/Limit.v's
 [absets_limit_ext]).  In [Ab] the constant maps are not homomorphisms,
 so THAT ARGUMENT DOES NOT TRANSPOSE, and no elementwise joint-monicity
 lemma for [Ab] is proved here either.  Instead the statement is
 transported: [Ab_Forget] preserves limiting cones
 (Instance/Ab/Limit.v's [Ab_Forget_creates_continuous], which comes
 from creation and so from [Sets_Complete] alone), so [mlim_sets_limit]
 turns the [Ab]-limit into a [Sets]-limit on the same carrier and
 [absets_limit_ext] applies to it unchanged.  [mrefl_ext] is the same
 move for the reflection half.

 That is a deliberate contrast with the template.  Instance/Ab/Limit.v's
 header discloses that its four generic [Sets] lemmas are
 Instance/Grp/Limit.v's reproved character-for-character under different
 names, and calls factoring them into Instance/Sets/Complete.v the right
 repair.  This file adds no fifth copy: it consumes
 [absets_limit_ext] by importing Instance/Ab/Limit.v, which it must
 import anyway for [Ab_Complete].  The repair the [Ab] header asks for
 is still NOT done -- see NOT DELIVERED -- but the debt is not grown.

 ** THE TWO FORGETFUL FUNCTORS, AND WHY A BRIDGE STANDS BETWEEN THEM

 Instance/Mod.v declares two forgetful functors, [RMod_Forget_Ab] and
 [RMod_Forget], and its header records that the second
 is taken directly through the underlying setoid rather than as the
 composite of the first with [Ab_Forget].  Measured here, that record is
 exact on both sides.  The object and morphism parts DO agree
 definitionally -- [rmod_forget_obj_agrees] and
 [rmod_forget_map_agrees] are [eq_refl] -- while the two functor RECORDS
 do not: [RMod_Forget R = Ab_Forget ◯ RMod_Forget_Ab R] by [eq_refl] is
 refused with “cannot unify \”RMod_Forget R\“ and
 \”Ab_Forget ◯ RMod_Forget_Ab R\“”, the three law fields being opaque.

 The consequence is that Structure/Limit/Preservation.v's
 [continuous_compose] gives [RMod_Forget_composite_continuous :
 ContinuousFunctor (Ab_Forget ◯ RMod_Forget_Ab R)] and NOT continuity of
 [RMod_Forget]: ascribing it is refused with “cannot unify
 \”Cone.Cone (RMod_Forget R ◯ K)\“ and
 \”Cone.Cone (Ab_Forget ◯ RMod_Forget_Ab R ◯ K)\“”.  So the composite
 lemma IS used -- the question the task put -- and one three-line bridge
 stands beside it: [rmod_abcone_of] repackages a cone over
 [RMod_Forget R ◯ K] as a cone over the composite, field by field,
 exactly as Structure/Limit/Preservation.v's [cone_assoc] repackages
 across functor associativity and for exactly the same reason (the
 fields are convertible, the record types are not).
 [RMod_Forget_creates_continuous] is then a term with no tactic in it,
 and [RMod_Forget_PreservesAllLimits] follows.

 ** THE HEADLINE SENTENCE IS MACHINE-CHECKED AT [eq_refl], NOT ARGUED

 At the limits [RMod_Complete] chooses -- [Ab_Complete] over
 [Sets_Complete], hence the compatible families of
 Instance/Sets/Complete.v -- the created module is the
 COORDINATEWISE one on the nose.  [rmod_complete_carrier],
 [rmod_complete_plus], [rmod_complete_zero], [rmod_complete_neg],
 [rmod_complete_smul] and [rmod_complete_leg] are six [eq_refl]
 Examples, at an ARBITRARY ring, an ARBITRARY shape and an ARBITRARY
 diagram of modules.  The fifth is the one that is not inherited from
 the [Ab] file: it says the created ACTION is computed componentwise,
 [`1 (r · a) d = r ·[K d] (`1 a d)], and it survives even though
 [RMod_Complete]'s chosen limit reaches its mediator through
 [creates_limiting] and hence through a cone transport.  Nothing in
 these six is specific to a witness category, and no isomorphism is
 interposed; this file therefore needs no concrete witness to be
 non-vacuous, and builds none.

 ** ON THE HOUSE RULE THAT MORPHISMS ARE COMPARED WITH [≈]

 FOURTEEN statements here write [=] -- the [eq_refl]-witnessed
 [Example]s and [Definition]s outside comments, thirteen of them on one
 [:= eq_refl] line and [mlim_over_obj] with its witness on the next --
 and each does so because both sides are the SAME TERM.  Five compare
 MORPHISMS -- [mlim_over_legs], [rmod_fcone_leg], [rmod_lift_legs],
 [rmod_forget_map_agrees] and [rmod_complete_leg].  They record Mac
 Lane's [F σ = τ] at full strength, which is strictly stronger than the
 [≈] the [StrictLift] clause asks for; every law, every proof and the
 [slift_legs] clause consumed by [rmod_strict_lift] use [≈].  Five
 compare OBJECTS -- [mlim_over_obj], [rmod_fcone_apex],
 [rmod_lift_apex], [rmod_forget_obj_agrees] and
 [rmod_complete_carrier] -- and four compare ELEMENTS --
 [rmod_complete_plus], [rmod_complete_zero], [rmod_complete_neg] and
 [rmod_complete_smul].  Objects and elements are the discipline's
 sanctioned exception.

 ** WHAT WAS IN TREE BEFORE, MEASURED

 Measured on the worktree this file was written against, over all 1016
 other [.v] files by [grep -rlw]: [RMod_Complete],
 [RMod_Forget_Ab_creates], [RMod_Forget_Preserves] and
 [RMod_Forget_reflects] each returned ZERO hits, and so did
 [Complete (RMod], so no completeness, creation, preservation or
 reflection statement about [RMod R] or either forgetful functor
 existed.  Instance/Mod/Product.v has the one product ([ProdMod]) and
 records that the [HasIndexedProducts (RMod R)]
 instance itself was deliberately not attempted, the universe
 negotiation being left to the issue that needs the class.  That
 decision is untouched and remains correct: the creation route reaches
 completeness without any [HasIndexedProducts] or [HasEqualizers]
 instance at [RMod R], because [creates_limits_Complete] transports the
 whole of [Ab]'s completeness at once.  Nothing here supplies those two
 classes -- see NOT DELIVERED.

 ONE THING THIS FILE IS THE FIRST TO DO, measured by reading every
 occurrence of [creates_limits_Complete] outside Test/ and looking at
 which completeness it is handed.  Three applications name a constant,
 and all three name [Sets_Complete]: Instance/Grp/Limit.v,
 Instance/Ab/Limit.v and Instance/Rng/Limit.v.  Every other
 application takes its base completeness as a HYPOTHESIS instead --
 Construction/Arrow/Limit.v, Construction/Comma/Creation.v,
 Construction/Reflective/Limit.v,
 Construction/Subcategory/Creation.v,
 Construction/Slice/Creation.v,
 Instance/Cat/Creation.v, Instance/Fun/Creation.v and
 Monad/Eilenberg/Moore/Limit.v, several of them through a derived
 completeness such as [Product_Complete HC HC] or
 [Functor_Category_Complete HX], but none of them naming a constant.
 [RMod_Complete] is therefore the first application in the tree whose
 base is a NAMED completeness other than [Sets_Complete], stacking two
 creation results; the smallness discipline is still [Sets_Complete]'s,
 arriving one indirection further away.  The claim is about this
 application, not about novelty of the machinery, all of which is
 Structure/Limit/Creation.v's.

 ** UNIVERSES, measured off BOTH binder and block over all 68 constants

 The 68 are the 62 declaration heads (46 [def], 16 [prf] in the [.glob])
 plus the six [Program] obligations, read back with
 [Set Printing Universes] and [About].  ZERO word-bounded [Set]
 occurrences anywhere.  CORRECTION, PR “algebraic carriers are sets”
 (2026-09-17).  This read “That is worth saying because the consumer
 this file exists for does meet one”, and cited a solution set
 elaborated at [SolutionSet@{Set …}] out of Instance/Discrete.v's
 unannotated [DiscreteCat_Functor].  That artifact was repaired at
 Instance/Discrete.v and the literal [Set] is gone.  The cost the
 consumer meets now is a different and smaller one, [Set < carrier],
 measured at Instance/Grp/FreeAFT.v; nothing here narrows
 anything to [Set], and the disclosure is owed at the application.

 [RMod_Complete@{u u0 u1 u2 u3 u4} :
 ∀ R : RingObject@{u u3 u4}, Complete@{u u u u0}], with [u < u0] and
 [u < u1] and no block equation, which is [Ab_Complete@{u u0 u1} :
 Complete@{u u u u0}] ([u < u0], [u < u1]) and [Sets_Complete]'s
 discipline unchanged, one ring parameter wider.  SEVENTEEN of the 68
 carry no block equation at all, including every top-level corollary
 ([RMod_Complete], [RMod_Forget_Ab_creates_limits],
 [RMod_Forget_Ab_creates_continuous], [RMod_Forget_composite_continuous],
 [RMod_Forget_creates_continuous], [RMod_Forget_Ab_lifts_limits],
 [RMod_lift_cone_unique], the four preservation/reflection readbacks and
 the four [rmod_fcone_*]/[rmod_forget_*] ones).

 THE EQUATIONS THE SECTION CONSTANTS CARRY ARE THE CONTEXT'S, NOT THIS
 FILE'S, and that was measured by isolation rather than guessed: a
 trivial [Example ctx_only : L = L := eq_refl] placed inside the same
 [Context {R} {J} (K) (L)] ALREADY carries [u = u3] together with the
 three strict constraints [u < u4], [u < u5], [u < u7] and the stdlib
 caps [Basics.compose.u0/u1/u2] and [ID.u0].  Here [u] is the ring's
 carrier universe, which [RMod R]'s hom-and-proof universe is
 identified with, and [u3] is the shape's hom-and-proof universe; the
 three strict constraints are the module carrier level below the levels
 of the categories it is stated in, the same shape Instance/Mod/
 Product.v records for its own four constants stated inside [RMod R].

 EXACTLY ONE FURTHER IDENTIFICATION APPEARS, and it enters at one named
 place.  THIRTY-THREE constants additionally carry [u = u2] (and
 [u = u6] or [u = u7], relabellings of the [Limit]'s own level): [u2] is
 the SHAPE'S OBJECT universe.  Isolated the same way, the probe
 [limitcone_isalimit (Ab_Forget_creates_continuous J ...)] -- which is
 [mlim_sets_limit], nothing more -- already carries all three.  The
 donor is therefore [Ab_Complete]'s type [Complete@{u u u u0}]: the
 [Complete] of Structure/Complete.v quantifies over shapes whose
 object, hom and proof universes coincide, so anything that consumes
 [Ab_Forget_creates_continuous] inherits that identification.  It is
 [Sets_Complete]'s own shape, arriving through [Ab_Complete], and is not
 narrowed here.  This is the same sentence Instance/Ab/Limit.v records
 about its own [ab_complete_*] readbacks and Instance/Rng/Limit.v about
 its twelve.

 ** STATUS: axiom-free

 [Print Assumptions] reports “Closed under the global context” for ALL
 68 constants -- the 62 heads and the six obligations -- with zero
 [Axioms:] lines; the obligations answer only to their qualified names
 ([Category.Instance.Mod.Limit.mlim_hom_obligation_1] and the rest).
 All 68 are registered in the Makefile's [make print-assumptions] gate
 block, one [Print Assumptions Category.Instance.Mod.Limit.<name>] line
 each, so the report above is re-run by that target rather than only by
 the scratch file it was first measured with.

 ** MEASURED

 62 [.glob] declaration heads (46 [def], 16 [prf]) and six [Program]
 obligations; the obligation list came from
 [strings Instance/Mod/Limit.vo] filtered on [_obligation_], with the
 junk digit prefix stripped -- four of the six appear ONLY prefixed
 ([5mlim_hom_obligation_1], [5mlim_med_obligation_1],
 [6mrefl_hom_obligation_1], [9mlim_smul_fn_obligation_1]) -- and
 [Print Module Category.Instance.Mod.Limit] lists exactly the same 68
 names, neither side carrying one the other lacks.  All 68 are “Closed
 under the global context” (see STATUS).  Universes: see UNIVERSES; zero
 word-bounded [Set].

 Counted BY TOKEN over the whole file with the criterion
 [grep -o 'Qed\.'] and [grep -o 'Defined\.'] -- the trailing period is
 what keeps the words used in this paragraph out of the count -- the
 numbers are 22 proof terminators of the first kind and THREE of the
 second.  Two of the three transparent ones are LOAD-BEARING, each shown
 so by making it opaque in a copy of the WHOLE file and naming what
 stops.  [mlim_created] flipped
 stops [RMod_Forget_Ab_StrictlyCreatesLimit]'s [screates_limiting]
 clause, which needs [ump_limit] of it to be convertible with the strict
 lift's own cone.  [RMod_Forget_Ab_StrictlyCreatesLimit] flipped stops
 [rmod_lift_apex], whose [eq_refl] then has the wrong type.  The third,
 [rmod_reflects], is NOT load-bearing in this file -- flipped to [Qed]
 the file still compiles, measured -- and is kept transparent only to
 match its template [ab_reflects] (Instance/Ab/Limit.v) and to leave
 the reflection witness computable for a downstream consumer.  Said
 plainly so no later reader takes its [Defined] for a measured
 requirement.

 [Require] discipline: 15 imports, closure 53 files excluding this one
 (iterated [coqdep], counting only paths that exist in the worktree).
 At the margin only two carry anything of their own --
 Instance/Mod.v 6 files, Instance/Ab/Limit.v 1 -- and the other 13 cost
 0, being reached through those two.  NONE of the 15 is droppable: each
 was deleted in turn from a copy and the file was recompiled, and each
 deletion stops the build.  Two imports that the first draft carried,
 Theory/Isomorphism.v and Instance/Rng.v, were droppable by that test
 and are gone.

 Zero DECLARATION-HEAD COLLISIONS: none of the 68 names is declared
 anywhere else, measured by scanning every one of the 1017 other
 [.glob] files in the tree for a [def]/[prf]/[ind]/[constr]/[scheme]/
 [inst] head equal to one of them (file list from [find], fed through
 [xargs], so no [.gitignore] traversal rule applies), with
 [Ab_Complete] as the positive control (declared in
 Instance/Ab/Limit.glob, one file) and a nonexistent name as the
 negative.  MENTIONS are a different count and are not zero: over the
 1021 other [.v] files, exactly four mention any of the 68 names --
 Test/ProbeModLimit449.v 36 of them, Instance/Mod/TensorAFT.v 2 (in
 code and in header prose), Test/ProbeModTensorAFT449.v 1 and
 Instance/Mod/Spanning.v 1 (header prose).

 ** NOT DELIVERED

 The tensor product, and every other part of §V.7 Construction 1 beyond
 its first premise.  No continuity of Instance/Mod/Tensor.v's
 [Bilin V V'], no solution set, no application of Adjunction/GAFT.v, and
 no universal element obtained that way; Instance/Mod/Tensor.v's
 [tensor_UniversalElement] is built by generators and relations and is
 neither used nor compared here.  In particular NOTHING here says the
 tensor product exists, and nothing here is circular with it: the only
 inputs are [Sets_Complete] and Instance/Ab/Limit.v.

 No [HasIndexedProducts (RMod R)] and no [HasEqualizers (RMod R)]
 instance.  These are not gaps the creation route leaves: they are the
 generators one would need on the OTHER route to completeness, and
 [creates_limits_Complete] does not ask for them.  The universe
 negotiation Instance/Mod/Product.v declines is therefore still
 declined, and still open for whichever issue wants the classes
 themselves.

 No colimits and no cocompleteness for [RMod R] in this file
 (Instance/Mod/Coproduct.v has the binary biproduct [RMod_Biproducts]
 and is not touched), and no claim that [RMod_Forget_Ab] creates or
 preserves any colimit.  An earlier revision said “No colimits and no
 cocompleteness for [RMod R]” without the qualifier; since #454
 Instance/Mod/Colimit.v's [RMod_Cocomplete_via_GAFT] obtains every
 colimit within its shape discipline from [GAFT] at the diagonal, over
 this file's [RMod_Complete].  No
 comparison of the created product with Instance/Mod/Product.v's
 [ProdMod], which would go through a discrete diagram and so through
 Instance/Discrete.v's unannotated [DiscreteCat_Functor].  No
 monadicity statement and no comparison functor, so nothing here says
 [RMod R] IS an Eilenberg-Moore category over [Ab] (CORRECTION (#465):
 so in this file, but no longer in the tree: Instance/Mod/TensorMonad.v's
 [EM_RMod_iso] identifies [RMod R] with the Eilenberg-Moore category of
 R ⊗ (−) on [Ab] by the canonical comparison functor).  No whole-record
 uniqueness statement “[M = LimitMod] for any module [M] on that
 group”: [mlim_smul_unique] settles the action, which is all Mac Lane's
 Theorem 2 needs here since the group is not lifted, but the record
 statement would need a Leibniz equality of [rm_ab] and a transport in
 the type of [rm_smul].  No signature-generic statement covering [Grp],
 [Ab], [Rng] and [RMod] at once; the four-lemma duplication
 Instance/Ab/Limit.v discloses between itself and Instance/Grp/Limit.v
 is not repaired here, only not extended.  No right modules: everything
 is stated for [RMod R], and [ModR R] (Instance/Mod.v) inherits it
 only
 by being [RMod (Ring_op R)], which is not spelled out.  NOTHING is
 registered as an [Instance] -- a chosen limit must not become globally
 resolvable.  The [eq_refl] readbacks are NOT guarded only by being
 [Example]s here: Test/ProbeModLimit449.v accompanies this file,
 carrying this file's own fifteen [Require]s plus this file plus the two
 the probe itself needs, and restates all fourteen of them as [p449_r1]
 through [p449_r14] from library constants alone, beside four measured
 boundaries [p449_f1] through [p449_f4] -- all four CONVERSION, each
 followed by the term or the positive half that DOES stand there -- and
 an instrument check.  What no probe guards is the universe census and
 the [Defined] transparency measurements above, which rest on being
 re-run.

 ** HOW AN ELEMENT OF A CREATED LIMIT MODULE IS REPRESENTED

 Recorded for whoever checks a functor's continuity elementwise against
 these limits.  At [RMod_Complete R J K] the carrier is
 [Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K))]
 ([rmod_complete_carrier], [eq_refl]), whose elements are the dependent
 pairs of Instance/Sets/Complete.v: a family [x : ∀ d : J, carrier
 (K d)] paired with a proof that [fmap[K] f (x d) ≈ x d'] for every
 [f : d ~> d'].  Projection is [`1 p d]; two elements are equivalent
 exactly when their families are pointwise equivalent, the proof
 component playing no part.  Every operation is componentwise at
 [eq_refl]: [`1 (a + b) d], [`1 0 d], [`1 (- a) d] and [`1 (r · a) d]
 are [`1 a d + `1 b d], [0], [- (`1 a d)] and [r · (`1 a d)] in [K d]
 ([rmod_complete_plus], [rmod_complete_zero], [rmod_complete_neg],
 [rmod_complete_smul]), and the leg at [d] IS
 [Sets_limit_leg _ d] ([rmod_complete_leg]).  At an abstract [L] rather
 than the chosen one, the corresponding facts are the triangles
 [mlim_smul_triangle] and [mcar_med_commutes] together with
 [mlim_ext]. 

 --------
 Mac Lane：《为实际工作的数学家而作的范畴论》，第2版（GTM 5），
 §V.7 构造 1，书中第128页（PDF第137页）
 [maclane:V.7:construction1] -- 构造的第一个前提（“K-Mod 是小完备的”）
 §V.1 定理 2 和 3，书中第111-112页（PDF第120-121页）
 -- 创建论证本身
 §V.6 定理 2，书中第125-126页 -- Freyd 的 GAFT 定理
 构造 1 使用
 nLab: https://ncatlab.org/nlab/show/created+limit
 nLab: https://ncatlab.org/nlab/show/limit#limits_in_categories_of_algebras
 nLab: https://ncatlab.org/nlab/show/Mod
 nLab: https://ncatlab.org/nlab/show/adjoint+functor+theorem
 维基百科: https://en.wikipedia.org/wiki/Category_of_modules
 Riehl：《上下文中的范畴论》，§5.6 示例 5.6.8Mac Lane 的 §V.7 构造 1 是通过伴随函子定理获得模的张量积，而不是通过生成元和关系。其调用的定理需要双线性映射函子的源类型满足三个条件：其源类型是小完全的，函子是连续的，并且它有解集。这个文件提供了第一个条件，而没有提供其他条件：[RMod_Complete]，“K-Mod 是小完全的”，以及两个遗忘函子的连续性，第二个前提将依据此进行检查。双线性映射函子 [Bilin]（Instance/Mod/Tensor.v）、其连续性、解集以及伴随函子定理的应用都在其他地方——见未提供部分。

 ** 路径：从 [Ab] 向上一级，而不是向下两级到 [Sets][RMod_Forget_Ab R]（实例/模块.v）严格地创造每一个极限，并且[RMod R]的完备性是从[Ab]的完备性中读取的，而不是从[Sets]的完备性中读取的。给定一个位于底层图上的阿贝尔群的极限锥[L]，其顶点上恰好存在唯一的标量作用，使得每一个投影都是模同态（在此实例中为[mlim_smul_unique]，参见Mac Lane §V.1 定理2），由此得到的锥严格位于[L]之上（[mlim_over_obj]和[mlim_over_legs]都是[eq_refl]，因为[RMod_Forget_Ab]的对象映射是[rm_ab]投影，其态射映射是[rm_hom]），它是极限的（[mlim_created]），并且一个模的锥其像是极限的，则该锥本身也是极限的（[rmod_reflects]）。打包在 Structure/Limit/Creation.v 自身的类中 —— [RMod_Forget_Ab_StrictlyCreatesLimit]、[RMod_Forget_Ab_CreatesLimit]、[RMod_Forget_Ab_StrictlyCreatesLimits] 和 [RMod_Forget_Ab_creates_limits] —— 从中通过应用得到推论：[RMod_Complete]（Mac Lane §V.1 定理 3）、[RMod_Forget_Ab_creates_continuous]、[RMod_Forget_Ab_PreservesAllLimits] 和 [RMod_Forget_Ab_reflects_limits]。为什么这是正确的级别，以及它的代价。一个模是一个具有运算的阿贝尔群：Instance/Mod.v 的 [RModObject] 通过 [rm_smul_respects] 及四条定律，从 Instance/Ab.v 的 [AbObject] 通过 [rm_smul] 扩展而来，[rm_ab] 是一个强制转换。所以这里确切地提升了一个运算——action——而 [Ab] 模板提升了三个（[cmon_plus]、[cmon_zero]、[ab_neg]），Instance/Grp/Limit.v 也提升了三个。顶点的阿贝尔群根本没有被构造：[LimitMod] 的 [rm_ab] 是 [vertex_obj[L]，这就是使得 [mlim_over_obj] 通过 [eq_refl] 而非通过同构成立的原因。而且它比看起来更便宜，因为该操作是作为  [Ab] 中的中介者构建的，而不是作为载体上的函数。对于固定的标量 [r]，族 [fun a => r · (leg j a)] 在每个 [j] 上都是阿贝尔群的同态——通过 [rm_smul_distr_l] 加法，通过 Instance/Mod.v 的 [rm_smul_zero_r] 单位——并且通过 [rm_map_smul] 是一致的，因此它是 [Ab] 中对相同图 ([mlim_smul_cone]) 的锥。它的中介者 [mlim_smul_map] 根据构造是一个 [Ab]-态射，因此 [mlim_smul_distr_l]——向量加法的分配律——在这里根本没有证明：它是 [cmon_map_plus (mlim_smul_map r)]，一个引用。相同的说明使第二个参数的尊重性成为自由的。其他四个条款
 （[mlim_smul_respects] 在其第一个参数中，[mlim_smul_distr_r]，
 [mlim_smul_assoc]，[mlim_smul_one]）每个都是三行：应用联合单调性，重写定义三角形 [mlim_smul_triangle]，应用 [K j] 中的定律。

 ** 引擎是借用的，而不是复制的——这是该文件唯一偏离其模板的地方下面的每条定律都基于 [mlim_ext]：顶点的两个元素在每条腿上相等。在 [Sets] 中，这一点是通过使用常值映射作为探针的中介唯一性来证明的（Instance/Ab/Limit.v 的 [absets_limit_ext]）。在 [Ab] 中，常值映射不是同态，因此该论证无法移植，而且这里也未证明 [Ab] 的元素级联合单性引理。相反，该陈述是通过迁移实现的：[Ab_Forget] 保持极限锥（Instance/Ab/Limit.v 的 [Ab_Forget_creates_continuous]，来源于创造，因此仅来自 [Sets_Complete]），因此 [mlim_sets_limit] 将 [Ab]-极限转换为同一载体上的 [Sets]-极限，并且 [absets_limit_ext] 对其保持不变。[mrefl_ext] 是反射部分的相同操作。这是与模板的一个故意对比。Instance/Ab/Limit.v 的头部指出，它的四个通用 [Sets] 引理实际上是 Instance/Grp/Limit.v 按字符完全批改后的不同命名，并称将它们合并到 Instance/Sets/Complete.v 中是正确的修复。这个文件没有添加第五份副本：它通过导入 Instance/Ab/Limit.v 来使用 [absets_limit_ext]，而它无论如何都必须为 [Ab_Complete] 导入该文件。[Ab] 头部要求的修复仍未完成 —— 见未交付 —— 但债务没有增加。

 ** 两个健忘函子，以及它们之间为何有一座桥梁Instance/Mod.v 声明了两个遗忘函子，[RMod_Forget_Ab] 和 [RMod_Forget]，其头文件记录第二个函子是直接通过基础集合组而取得的，而不是作为第一个与 [Ab_Forget] 的复合。在此处测量时，该记录在两边都是精确的。对象和态射部分在定义上确实一致——[rmod_forget_obj_agrees] 和 [rmod_forget_map_agrees] 是 [eq_refl]——而两个函子记录则不一致：[RMod_Forget R = Ab_Forget ◯ RMod_Forget_Ab R] 通过 [eq_refl] 被拒绝，并显示“无法统一 'RMod_Forget R' 与 'Ab_Forget ◯ RMod_Forget_Ab R'”，三个律域是不可透明的。其结果是 Structure/Limit/Preservation.v 的 [continuous_compose] 给出了 [RMod_Forget_composite_continuous : ContinuousFunctor (Ab_Forget ◯ RMod_Forget_Ab R)]，而不是 [RMod_Forget] 的连续性：为其归属被拒绝，提示“无法统一 “Cone.Cone (RMod_Forget R ◯ K)” 和 “Cone.Cone (Ab_Forget ◯ RMod_Forget_Ab R ◯ K)””。因此复合引理确实被使用——正是任务提出的问题——并且旁边有一个三行的桥接：[rmod_abcone_of] 将 [RMod_Forget R ◯ K] 的一个圆锥重新打包成复合上的圆锥，逐字段操作，正如 Structure/Limit/Preservation.v 的 [cone_assoc] 在函子结合性下重新打包一样，并且原因完全相同（字段是可转换的，但记录类型不是）。然后 [RMod_Forget_creates_continuous] 是一个内部没有任何策略的项，[RMod_Forget_PreservesAllLimits] 由此得到。** 头条句子已在 [eq_refl] 由机器检查，而非争论在极限处，[RMod_Complete] 选择 -- [Ab_Complete] 而非 [Sets_Complete]，因此在 Instance/Sets/Complete.v 中兼容的族 -- 创建的模块正是 COORDINATEWISE 模块。[rmod_complete_carrier]、[rmod_complete_plus]、[rmod_complete_zero]、[rmod_complete_neg]、[rmod_complete_smul] 和 [rmod_complete_leg] 是六个 [eq_refl] 示例，在任意环、任意形状和任意模块图中。第五个示例不是继承自 [Ab] 文件：它表明创建的 ACTION 是按分量计算的，[`1 (r · a) d = r ·[K d] (`1 a d)]，并且即便 [RMod_Complete] 所选择的极限通过 [creates_limiting] 及其锥传输到达其中介，它仍然存在。在这六个中没有任何内容是特定于证人类别的，也没有插入同构；因此，此文件不需要具体的证人来非空，并且也没有构建任何证人。

 ** 关于房规规定的形态被与 [≈] 比较这里写了十四条声明 [=] —— [eq_refl] 目击的 [Example] 和 [Definition] 的外部评论，其中十三条在一行上，ZW119WZZ 与其见证在下一行 —— 每条都是因为双方是相同的术语。五条比较形态 —— [mlim_over_legs]、[rmod_fcone_leg]、[rmod_lift_legs]、[rmod_forget_map_agrees] 和 [rmod_complete_leg]。它们完整记录了 Mac Lane 的 [F σ = τ]，这比 [StrictLift] 条款要求的 [≈] 严格得多；每条法律、每个证明以及 [slift_legs] 条款由 [rmod_strict_lift] 消耗使用 [≈]。五条比较对象 —— [mlim_over_obj]、[rmod_fcone_apex]、[rmod_lift_apex]、[rmod_forget_obj_agrees] 和 [rmod_complete_carrier] —— 四条比较元素 —— [rmod_complete_plus]、[rmod_complete_zero]、[rmod_complete_neg] 和 [rmod_complete_smul]。对象和元素是该学科允许的例外。

 ** 树中原本的内容，已测量在针对该工作树测量的情况下，该文件在所有 1016 个其他 [.v] 文件中由 [grep -rlw]：[RMod_Complete]、[RMod_Forget_Ab_creates]、[RMod_Forget_Preserves] 和 [RMod_Forget_reflects] 检查时均返回零命中，[Complete (RMod] 也同样如此，因此不存在关于 [RMod R] 或任一忘记函子的完整性、创建、保存或反思声明。Instance/Mod/Product.v 有唯一的产品 ([ProdMod]) 并记录了 [HasIndexedProducts (RMod R)] 实例本身故意未尝试，该宇宙协商留给需要该类的问题。该决定保持不变且仍然正确：创建路径无需在 [RMod R] 处有任何 [HasIndexedProducts] 或 [HasEqualizers] 实例即可达到完整性，因为 [creates_limits_Complete] 一次性传输了整个 [Ab] 的完整性。这里没有提供那两个类别——见“未交付”。这份文件首次完成的一件事，是通过读取 Test/ 之外每一次出现的 [creates_limits_Complete]，并查看它被分配到的完整性来衡量的。三个应用程序命名了一个常量，且全部三个都命名为 [Sets_Complete]：Instance/Grp/Limit.v、Instance/Ab/Limit.v 和 Instance/Rng/Limit.v。所有其他应用程序则将其基础完整性作为假设——Construction/Arrow/Limit.v、Construction/Comma/Creation.v、Construction/Reflective/Limit.v、Construction/Subcategory/Creation.v、Construction/Slice/Creation.v、Instance/Cat/Creation.v、Instance/Fun/Creation.v 以及 Monad/Eilenberg/Moore/Limit.v，其中几个通过派生完整性如 [Product_Complete HC HC] 或 [Functor_Category_Complete HX]，但没有一个命名常量。因此，[RMod_Complete] 是树中第一个应用，其基是除 [Sets_Complete] 之外的一个命名完备性，堆叠了两个创建结果；小型性约束仍然是 [Sets_Complete] 的，距离又多了一层间接。声明是关于此应用，而不是关于机制的新颖性，所有这些都属于 Structure/Limit/Creation.v。

 ** 宇宙，测量基于绑定器和块，覆盖全部 68 个常量68是62个声明头（46个[def]，16个[prf]在[.glob]中）加上六个[Program]义务，回读[Set Printing Universes]和[About]。任何地方都没有[Set]的零字界出现。更正，PR“代数承载是集合”（2026-09-17）。这段读作“值得一说的是，因为使用这个文件的消费者确实满足一个”，并引用了在Instance/Discrete.v未注释的[DiscreteCat_Functor]中阐述的解决集[SolutionSet@{Set …}]。该工件已在Instance/Discrete.v中修复，字面上的[Set]已消失。消费者现在面临的成本是不同且更小的[Set < carrier]，在Instance/Grp/FreeAFT.v中测量；这里没有任何内容限定到[Set]，并且在申请时应披露。[RMod_Complete@{u u0 u1 u2 u3 u4} :
 ∀ R : RingObject@{u u3 u4}, Complete@{u u u u0}], 具有 [u < u0] 和
 [u < u1] 且没有块方程，其中是 [Ab_Complete@{u u0 u1} :
 Complete@{u u u u0}] ( [u < u0] ,  [u < u1] ) 并且 [Sets_Complete] 的
 学科保持不变，环参数更宽一层。在 68 个中有 17 个
 完全没有块方程，包括每个顶层推论
 ( [RMod_Complete] ,  [RMod_Forget_Ab_creates_limits] ,
 [RMod_Forget_Ab_creates_continuous] ,  [RMod_Forget_composite_continuous] ,
 [RMod_Forget_creates_continuous] ,  [RMod_Forget_Ab_lifts_limits] ,
 [RMod_lift_cone_unique] ，四个保持/反射回读和四个 [rmod_fcone_*] / [rmod_forget_*] 的)。这些方程式中节的常数是上下文的，而不是这个文件的，而且这是通过隔离测量的，而不是猜测：一个简单的 [Example ctx_only : L = L := eq_refl] 放在相同的 [Context {R} {J} (K) (L)] 内已经携带了 [u = u3]，以及三个严格约束 [u < u4]、[u < u5]、[u < u7] 和 stdlib 的上限 [Basics.compose.u0/u1/u2] 和 [ID.u0]。在这里 [u] 是环的承载宇宙，它与 [RMod R] 的同态与证明宇宙相对应，而 [u3] 是形状的同态与证明宇宙；三个严格约束是模块承载层级低于其所在类别的层级，形状实例/模块/Product.v 的相同记录也适用于它自己在 [RMod R] 中声明的四个常数。恰好出现了另一个标识，并且它出现在一个指定的地点。此外，有三十三个常量携带 [u = u2]（以及 [u = u6] 或 [u = u7]，它们是 [Limit] 自身层级的重新标记）：[u2] 是该形状的对象宇宙。以相同方式孤立时，探针 [limitcone_isalimit (Ab_Forget_creates_continuous J ...)] —— 它只是 [mlim_sets_limit] —— 已经携带了所有三个。因此，捐赠者是 [Ab_Complete] 的类型 [Complete@{u u u u0}]：Structure/Complete.v 的 [Complete] 对象量化了其对象、同态和证明宇宙一致的形状，所以任何使用 [Ab_Forget_creates_continuous] 的东西都会继承该标识。它是 [Sets_Complete] 的自身形状，通过 [Ab_Complete] 到达，并在此未被缩小。这是同一句子 Instance/Ab/Limit.v 的记录，关于它自己的 [ab_complete_*] 回读，以及 Instance/Rng/Limit.v 关于它的十二个。

 ** 状态: 无公理

 [Print Assumptions] 对所有 68 个常量——62 个头和 6 个义务——报告“在全局上下文下封闭”，没有 [Axioms:] 行；义务仅对其限定名称（[Category.Instance.Mod.Limit.mlim_hom_obligation_1] 和其余部分）作出响应。所有 68 个都在 Makefile 的 [make print-assumptions] 门块中注册，每个 [Print Assumptions Category.Instance.Mod.Limit.<name>] 一行，因此上述报告是由该目标重新运行的，而不仅仅是通过最初测量的临时文件。

 ** 测量完成62 个 [.glob] 申报单头（46 个 [def] ，16 个 [prf] ）和六个 [Program] 义务；义务清单来自 [strings Instance/Mod/Limit.vo] ，经过 [_obligation_] 筛选，并去掉了无效数字前缀——六个中有四个仅以带前缀形式出现（[5mlim_hom_obligation_1] ， [5mlim_med_obligation_1] ， [6mrefl_hom_obligation_1] ， [9mlim_smul_fn_obligation_1]）——且 [Print Module Category.Instance.Mod.Limit] 列出了完全相同的 68 个名字，两边都不缺对方的任何一个。所有 68 个都是“在全局上下文下关闭的”（参见状态）。宇宙：见宇宙；零个以单词边界分隔的 [Set] 。按标记在整个文件中计算，并使用标准 [grep -o 'Qed\.'] 和 [grep -o 'Defined\.'] ——结尾的句号是使本段中使用的单词不计入统计的原因——数字是第一类的22个证明终止符和第二类的三个。其中三个透明终止符中的两个是承重的，每个在整个文件的副本中通过使其不透明并命名其停止点来显示。[mlim_created] 翻转了 [RMod_Forget_Ab_StrictlyCreatesLimit] 的 [screates_limiting] 条款，这需要 [ump_limit] 才能与严格提升自身的锥体兼容。[RMod_Forget_Ab_StrictlyCreatesLimit] 翻转了 [rmod_lift_apex]，其 [eq_refl] 随后类型错误。第三个，[rmod_reflects]，在此文件中不是承重的 —— 翻转为[Qed]后，文件仍然可以编译，经过测量 —— 并保持透明仅是为了匹配它的模板[ab_reflects]（Instance/Ab/Limit.v）并使下游使用者能够计算反射见证。简单地说，就是避免后来的读者将其[Defined]误认为是经过测量的要求。[Require] 学科：15 个导入，闭包 53 个文件，不包括这个文件
 （迭代 [coqdep]，只计算在工作树中存在的路径）。
 在边缘上，只有两个有自己的内容——
 Instance/Mod.v 6 个文件，Instance/Ab/Limit.v 1 个——其他 13 个的成本为 0，通过这两个文件到达。15 个文件中没有一个是可删除的：每个文件都在一个副本中依次被删除并重新编译文件，每次删除都会停止构建。第一个草稿中包含的两个导入，Theory/Isomorphism.v 和 Instance/Rng.v，可以通过该测试删除，现在已经不存在了。零声明头冲突：68 个名称中没有一个在其他地方被声明，通过扫描树中另外 1017 个 [.glob] 文件，查找 [def] / [prf] / [ind] / [constr] / [scheme] / [inst] 头部是否与其中任何一个相同（文件列表来自 [find]，经 [xargs] 处理，因此不适用 [.gitignore] 遍历规则），[Ab_Complete] 作为阳性对照（在 Instance/Ab/Limit.glob 文件中声明，一个文件）以及不存在的名称作为阴性对照。提及（MENTIONS）是不同的计数，并非零：在另外 1021 个 [.v] 文件中，正好有四个提及了这 68 个名称中的任何一个——Test/ProbeModLimit449.v 提及 36 个，Instance/Mod/TensorAFT.v 提及 2 个（在代码中和头部说明中），Test/ProbeModTensorAFT449.v 提及 1 个，Instance/Mod/Spanning.v 提及 1 个（头部说明）。

 ** 未交付张量积，以及 §V.7 构造 1 除其第一个前提之外的所有部分。Instance/Mod/Tensor.v 的 [Bilin V V'] 没有连续性，没有解集，也没有应用 Adjunction/GAFT.v，也没有通过这种方式获得通用元素；Instance/Mod/Tensor.v 的 [tensor_UniversalElement] 是通过生成元和关系构建的，这里既没有使用也没有比较。特别是，这里什么都没有说明张量积存在，这里也没有与其循环依赖：唯一的输入是 [Sets_Complete] 和 Instance/Ab/Limit.v。没有 [HasIndexedProducts (RMod R)] 也没有 [HasEqualizers (RMod R)] 实例。这些不是创建路径留下的空白：它们是在另一条完整路径上所需的生成器，而 [creates_limits_Complete] 并不要求它们。因此，宇宙协商 Instance/Mod/Product.v 拒绝的状态仍然是拒绝的，并且对于任何需要这些类本身的问题仍然是开放的。在此文件中，[RMod R] 没有余极限，也没有余完备性（Instance/Mod/Coproduct.v 有二元双积 [RMod_Biproducts]，并且未被修改），并且没有声明 [RMod_Forget_Ab] 会创建或保留任何余极限。此前的一个版本说“[RMod R] 没有余极限，也没有余完备性”，但没有限定条件；自 #454 以来，Instance/Mod/Colimit.v 的 [RMod_Cocomplete_via_GAFT] 从 [GAFT] 在对角线位置获取其形态规约内的每个余极限，超过了此文件的 [RMod_Complete]。没有将所创建的积与 Instance/Mod/Product.v 的 [ProdMod] 进行比较，这将通过离散图，并因此通过 Instance/Discrete.v 的未标注 [DiscreteCat_Functor]。没有单子性声明，也没有比较函子，所以这里没有任何内容表明 [RMod R] 是 [Ab] 上的 Eilenberg-Moore 范畴（更正 (#465)：在这个文件中，但不再在树中：Instance/Mod/TensorMonad.v 的 [EM_RMod_iso] 通过典型比较函子将 [RMod R] 与 [Ab] 上 R ⊗ (−) 的 Eilenberg-Moore 范畴识别）。没有整体记录唯一性声明“[M = LimitMod] 对该群上的任何模 [M] 都成立”：[mlim_smul_unique] 决定了作用，这就是 Mac Lane 定理 2 在这里所需的全部，因为群没有被提升，但记录声明将需要 [rm_ab] 的 Leibniz 等式以及 [rm_smul] 类型中的传递。没有涵盖 [Grp]、[Ab]、[Rng] 和 [RMod] 的通用签名声明；四引理重复 Instance/Ab/Limit.v 与 Instance/Grp/Limit.v 之间的问题在此没有修复，仅仅是未扩展。没有正确的模块：一切都是针对 [RMod R] 陈述的，而 [ModR R]（Instance/Mod.v）仅仅通过成为 [RMod (Ring_op R)] 继承它，这一点没有明确说明。没有任何东西被注册为 [Instance]——被选择的极限不能成为全局可解析。[eq_refl] 的回读并不仅仅通过在这里成为 [Example] 来保护：Test/ProbeModLimit449.v 随附此文件，包含此文件自身的十五个 [Require] 加上此文件以及探头本身需要的两个，并将它们全部十四个重新表示为 [p449_r1] 到 [p449_r14]，仅通过库常数，外加四个测量边界 [p449_f1] 到 [p449_f4]——全部四个转换，每个之后跟随那个确实存在的项或者正半边——以及一个仪器检查。没有探头保护的，是宇宙普查和上述 [Defined] 透明度测量，它们依赖于重新运行。

 ** 一个已创建的限制模块元素是如何表示的记录给那些检查函子逐元素连续性是否符合这些极限的人。在 [RMod_Complete R J K] 处，载体是 [Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K))] ([rmod_complete_carrier], [eq_refl])，其元素是 Instance/Sets/Complete.v 中的依赖对：一个族 [x : ∀ d : J, carrier (K d)] 与一个证明  [fmap[K]  f (x d) ≈ x d' 配对，对于每个 [f : d ~> d']。投影是 [`1 p d]；当且仅当两个族逐点等价时，它们的元素等价，证明部分不起作用。每个运算在 [eq_refl] 上都是逐元素的：[`1 (a + b) d]、[`1 0 d]、[`1 (- a) d] 和 [`1 (r · a) d] 分别是 [`1 a d + `1 b d]、[0]、[- (`1 a d)] 和 [r · (`1 a d)] 在 [K d] ([rmod_complete_plus]、[rmod_complete_zero]、[rmod_complete_neg]、[rmod_complete_smul])，且在 [d] 的支腿是 [Sets_limit_leg _ d] ([rmod_complete_leg])。在一个抽象的 [L] 而不是被选中的，相关的事实是三角形 [mlim_smul_triangle] 和 [mcar_med_commutes] 以及 [mlim_ext]。
*)

Section ModLift.

Context {R : RingObject}.
Context {J : Category}.
Context (K : J ⟶ RMod R).
Context (L : Limit (RMod_Forget_Ab R ◯ K)).

Definition mlim_leg (j : J) : vertex_obj[L] ~{Ab}~> rm_ab (K j) :=
  limit_leg (limit_is_alimit L) j.

Lemma mlim_leg_coherence {x y : J} (f : x ~{J}~> y)
  (a : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  cmon_map (rm_hom (fmap[K] f)) (cmon_map (mlim_leg x) a)
    ≈ cmon_map (mlim_leg y) a.
Proof. exact (limit_leg_coherence (limit_is_alimit L) f a). Qed.

(*
 The engine, borrowed rather than reproved.  Constant maps are not
 homomorphisms, so Instance/Ab/Limit.v's argument does not transpose
 to [Ab] directly; instead [Ab_Forget] carries the limiting cone down to
 [Sets] on the same carrier, where that lemma applies verbatim.  The
 witness is Instance/Ab/Limit.v, which comes from creation and so
 from [Sets_Complete] alone -- no adjunction is presupposed anywhere in
 this chain. 

 --------
 引擎是借用的而不是被责备的。常量映射不是同态，所以 Instance/Ab/Limit.v 的论证不能直接转移到 [Ab]；相反，[Ab_Forget] 将极限锥带到相同载体上的 [Sets]，在那里该引理可以逐字适用。证明实例是 Instance/Ab/Limit.v，它来自创造，因此仅来自 [Sets_Complete]——在这一链条中的任何地方都没有预设伴随。
*)

Definition mlim_sets_limit :=
  limitcone_isalimit
    (Ab_Forget_creates_continuous J (RMod_Forget_Ab R ◯ K)
       (@limit_cone _ _ _ L) (limit_limitcone L)).

Lemma mlim_ext (x y : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  (∀ j : J, cmon_map (mlim_leg j) x ≈ cmon_map (mlim_leg j) y) → x ≈ y.
Proof. exact (absets_limit_ext mlim_sets_limit x y). Qed.

(** ** The scalar action / ** 标量作用 *)

(*
 For a fixed scalar [r], multiplication by [r] after the leg at [j] is an
 [Ab]-morphism -- additive by [rm_smul_distr_l], unital by
 Instance/Mod.v's [rm_smul_zero_r] -- and these assemble into a cone
 in [Ab] over the same diagram.  Taking the action to be that cone's
 MEDIATOR, rather than a bare function on the carrier, is what makes
 distributivity over vector addition and respectfulness in the second
 argument citations instead of proofs. 

 --------
 对于一个固定的标量 [r]，在 [j] 处的腿之后乘以 [r] 是一个 [Ab]-态射——由 [rm_smul_distr_l] 加法，由 Instance/Mod.v 的 [rm_smul_zero_r] 单位化——并且这些组合成 [Ab] 中的一个锥状结构，覆盖同一图。将作用视为该锥的 MEDIATOR，而不是载体上的一个简单函数，这正是实现对向量加法的分配性以及第二个参数对引用而非证明的尊重性的原因。
*)

Program Definition mlim_smul_fn (r : carrier (rig_setoid (ring_rig R)))
  (j : J) :
  cmon_setoid (ab_cmon vertex_obj[L]) ~{Sets}~> cmon_setoid (ab_cmon (K j)) :=
  {| morphism := fun a => rm_smul (K j) r (cmon_map (mlim_leg j) a) |}.
Next Obligation.
  intros r j a b Hab.
  now rewrite Hab.
Qed.

Program Definition mlim_smul_leg (r : carrier (rig_setoid (ring_rig R)))
  (j : J) : vertex_obj[L] ~{Ab}~> (RMod_Forget_Ab R ◯ K) j :=
  {| cmon_map := mlim_smul_fn r j |}.
Next Obligation.
  intros r j; simpl.
  rewrite cmon_map_zero.
  apply rm_smul_zero_r.
Qed.
Next Obligation.
  intros r j a b; simpl.
  rewrite cmon_map_plus.
  apply rm_smul_distr_l.
Qed.

Lemma mlim_smul_coherence (r : carrier (rig_setoid (ring_rig R)))
  {x y : J} (f : x ~{J}~> y) :
  fmap[RMod_Forget_Ab R ◯ K] f ∘ mlim_smul_leg r x ≈ mlim_smul_leg r y.
Proof.
  intro a; simpl.
  rewrite (rm_map_smul (fmap[K] f)).
  now rewrite mlim_leg_coherence.
Qed.

Definition mlim_smul_cone (r : carrier (rig_setoid (ring_rig R))) :
  Cone (RMod_Forget_Ab R ◯ K) :=
  @Build_Cone J Ab (RMod_Forget_Ab R ◯ K) vertex_obj[L]
    (@Build_ACone J Ab vertex_obj[L] (RMod_Forget_Ab R ◯ K)
       (mlim_smul_leg r) (@mlim_smul_coherence r)).

Definition mlim_smul_map (r : carrier (rig_setoid (ring_rig R))) :
  vertex_obj[L] ~{Ab}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) (mlim_smul_cone r).

Definition mlim_smul (r : carrier (rig_setoid (ring_rig R)))
  (a : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  carrier (cmon_setoid (ab_cmon vertex_obj[L])) :=
  cmon_map (mlim_smul_map r) a.

Lemma mlim_smul_triangle (r : carrier (rig_setoid (ring_rig R))) (j : J)
  (a : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  cmon_map (mlim_leg j) (mlim_smul r a)
    ≈ rm_smul (K j) r (cmon_map (mlim_leg j) a).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) (mlim_smul_cone r) j a).
Qed.

(* * ** The module laws, by joint monicity of the legs / * ** 模块定律，通过腿的联合单性 *)

Lemma mlim_smul_respects : Proper (equiv ==> equiv ==> equiv) mlim_smul.
Proof.
  intros r r' Hr a a' Ha.
  apply mlim_ext; intro j.
  rewrite !mlim_smul_triangle.
  rewrite Hr.
  now rewrite (proper_morphism (cmon_map (mlim_leg j)) a a' Ha).
Qed.

Lemma mlim_smul_distr_l (r : carrier (rig_setoid (ring_rig R)))
  (a b : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  mlim_smul r (cmon_plus vertex_obj[L] a b)
    ≈ cmon_plus vertex_obj[L] (mlim_smul r a) (mlim_smul r b).
(*
 Not proved: the mediator is an [Ab]-morphism, so this IS its
 [cmon_map_plus] clause. 

 --------
 未证明：中介者是一个 [Ab] -态射，所以这就是它的 [cmon_map_plus] 条款。
*)
Proof. exact (cmon_map_plus (mlim_smul_map r) a b). Qed.

Lemma mlim_smul_distr_r (r s : carrier (rig_setoid (ring_rig R)))
  (a : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  mlim_smul (rig_add (ring_rig R) r s) a
    ≈ cmon_plus vertex_obj[L] (mlim_smul r a) (mlim_smul s a).
Proof.
  apply mlim_ext; intro j.
  rewrite mlim_smul_triangle.
  rewrite (cmon_map_plus (mlim_leg j)).
  rewrite !mlim_smul_triangle.
  apply rm_smul_distr_r.
Qed.

Lemma mlim_smul_assoc (r s : carrier (rig_setoid (ring_rig R)))
  (a : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  mlim_smul (rig_mul (ring_rig R) r s) a ≈ mlim_smul r (mlim_smul s a).
Proof.
  apply mlim_ext; intro j.
  rewrite !mlim_smul_triangle.
  apply rm_smul_assoc.
Qed.

Lemma mlim_smul_one (a : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  mlim_smul (rig_one (ring_rig R)) a ≈ a.
Proof.
  apply mlim_ext; intro j.
  rewrite mlim_smul_triangle.
  apply rm_smul_one.
Qed.

(** ** The lifted module / ** 提升的模块 *)

(* The abelian group is not constructed: [rm_ab] IS the apex of [L]. That is the whole reason [mlim_over_obj] below is [eq_refl]. / 阿贝尔群未被构造：[rm_ab] 是 [L] 的顶点。这就是下面的 [mlim_over_obj] 是 [eq_refl] 的全部原因。 *)

Definition LimitMod : RModObject R :=
  {| rm_ab            := vertex_obj[L]
   ; rm_smul          := mlim_smul
   ; rm_smul_respects := mlim_smul_respects
   ; rm_smul_distr_l  := mlim_smul_distr_l
   ; rm_smul_distr_r  := mlim_smul_distr_r
   ; rm_smul_assoc    := mlim_smul_assoc
   ; rm_smul_one      := mlim_smul_one |}.

(* * ** The legs are module homomorphisms / * ** 这些腿是模同态 *)

Program Definition mlim_hom (j : J) : RModHom LimitMod (K j) :=
  {| rm_hom := mlim_leg j |}.
Next Obligation. intros j r m; apply mlim_smul_triangle. Qed.

Lemma mlim_hom_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ mlim_hom x ≈ mlim_hom y.
Proof. intro a; exact (mlim_leg_coherence f a). Qed.

Definition mlim_cone : Cone K :=
  @Build_Cone J (RMod R) K LimitMod
    (@Build_ACone J (RMod R) LimitMod K mlim_hom (@mlim_hom_coherence)).

(* * ** Strictness: the lifted cone lies over [L] on the nose / * ** 严格性：被抬起的圆锥位于鼻子上的 [L] 上 *)

Definition mlim_over_obj : RMod_Forget_Ab R LimitMod = vertex_obj[L] :=
  eq_refl.

Definition mlim_over_legs (j : J) :
  fmap[RMod_Forget_Ab R] (cone_leg mlim_cone j) = mlim_leg j := eq_refl.

(** ** The lifted cone is limiting / ** 提升的锥体是有限的 *)

Definition mcar_med (N : Cone K) :
  rm_ab vertex_obj[N] ~{Ab}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) (FCone (RMod_Forget_Ab R) N).

Lemma mcar_med_commutes (N : Cone K) (j : J)
  (a : carrier (cmon_setoid (ab_cmon (rm_ab vertex_obj[N])))) :
  cmon_map (mlim_leg j) (cmon_map (mcar_med N) a)
    ≈ cmon_map (rm_hom (cone_leg N j)) a.
Proof.
  exact (limit_med_commutes (limit_is_alimit L)
           (FCone (RMod_Forget_Ab R) N) j a).
Qed.

Lemma mcar_med_smul (N : Cone K) (r : carrier (rig_setoid (ring_rig R)))
  (a : carrier (cmon_setoid (ab_cmon (rm_ab vertex_obj[N])))) :
  cmon_map (mcar_med N) (rm_smul vertex_obj[N] r a)
    ≈ mlim_smul r (cmon_map (mcar_med N) a).
Proof.
  apply mlim_ext; intro j.
  rewrite mcar_med_commutes, mlim_smul_triangle, mcar_med_commutes.
  apply (rm_map_smul (cone_leg N j)).
Qed.

Program Definition mlim_med (N : Cone K) :
  vertex_obj[N] ~{RMod R}~> LimitMod := {| rm_hom := mcar_med N |}.
Next Obligation. intros N r m; apply mcar_med_smul. Qed.

Definition mlim_created : IsALimit K LimitMod.
Proof.
  unshelve refine {| limit_acone := @coneFrom _ _ _ mlim_cone |}.
  intro N.
  unshelve refine {| unique_obj := mlim_med N |}.
  - intros j a.
    exact (mcar_med_commutes N j a).
  - intros v Hv a.
    exact (limit_med_unique (limit_is_alimit L)
             (FCone (RMod_Forget_Ab R) N) (rm_hom v) Hv a).
Defined.

(* * ** Uniqueness of the lifted action (Mac Lane's §V.1 Theorem 2) / * ** 提升作用的唯一性（Mac Lane §V.1 定理 2） *)

(*
 The whole of the uniqueness clause AT THIS LEVEL: the abelian group is
 inherited on the nose rather than lifted, so the “exactly one structure
 making every projection a homomorphism” has ONE component here where
 the [Ab] template has three.  Note what is consumed -- only that the
 candidate satisfies the leg conditions, NO law of it -- so the
 statement is sharper than “any module structure on the apex making the
 projections homomorphisms is this one”. 

 --------
 整个唯一性条款在此层级：阿贝尔群按原样继承，而不是提升，所以“使每个投影成为同态的唯一结构”在这里只有一个组成部分，而 [Ab] 模板有三个。注意被使用的是什么——只是候选者满足腿条件，而没有其任何规律——因此该陈述比“使顶点上的任何模结构成为投影同态的结构就是这个”的陈述更精确。
*)

Lemma mlim_smul_unique
  (s : carrier (rig_setoid (ring_rig R)) →
       carrier (cmon_setoid (ab_cmon vertex_obj[L])) →
       carrier (cmon_setoid (ab_cmon vertex_obj[L])))
  (Hs : ∀ (j : J) r a,
     cmon_map (mlim_leg j) (s r a)
       ≈ rm_smul (K j) r (cmon_map (mlim_leg j) a))
  (r : carrier (rig_setoid (ring_rig R)))
  (a : carrier (cmon_setoid (ab_cmon vertex_obj[L]))) :
  s r a ≈ mlim_smul r a.
Proof.
  apply mlim_ext; intro j.
  now rewrite Hs, mlim_smul_triangle.
Qed.

End ModLift.

(* * * Reflection: a cone of modules whose image is limiting is limiting / * * 反射：一个模的圆锥，如果它的像是极限的，那么它本身也是极限的 *)

Section ModReflect.

Context {R : RingObject}.
Context {J : Category}.
Context (K : J ⟶ RMod R).
Context (M : Cone K).
Context (HM : IsLimitCone (FCone (RMod_Forget_Ab R) M)).

Definition mrefl_med (N : Cone K) :
  rm_ab vertex_obj[N] ~{Ab}~> rm_ab vertex_obj[M] :=
  limit_med (limitcone_isalimit HM) (FCone (RMod_Forget_Ab R) N).

Lemma mrefl_med_commutes (N : Cone K) (j : J)
  (a : carrier (cmon_setoid (ab_cmon (rm_ab vertex_obj[N])))) :
  cmon_map (rm_hom (cone_leg M j)) (cmon_map (mrefl_med N) a)
    ≈ cmon_map (rm_hom (cone_leg N j)) a.
Proof using All.
  exact (limit_med_commutes (limitcone_isalimit HM)
           (FCone (RMod_Forget_Ab R) N) j a).
Qed.

Definition mrefl_sets_limit :=
  limitcone_isalimit
    (Ab_Forget_creates_continuous J (RMod_Forget_Ab R ◯ K)
       (FCone (RMod_Forget_Ab R) M) HM).

Lemma mrefl_ext (x y : carrier (cmon_setoid (ab_cmon (rm_ab vertex_obj[M])))) :
  (∀ j : J, cmon_map (rm_hom (cone_leg M j)) x
              ≈ cmon_map (rm_hom (cone_leg M j)) y) → x ≈ y.
Proof using All. exact (absets_limit_ext mrefl_sets_limit x y). Qed.

Lemma mrefl_med_smul (N : Cone K) (r : carrier (rig_setoid (ring_rig R)))
  (a : carrier (cmon_setoid (ab_cmon (rm_ab vertex_obj[N])))) :
  cmon_map (mrefl_med N) (rm_smul vertex_obj[N] r a)
    ≈ rm_smul vertex_obj[M] r (cmon_map (mrefl_med N) a).
Proof using All.
  apply mrefl_ext; intro j.
  rewrite mrefl_med_commutes.
  rewrite (rm_map_smul (cone_leg N j)).
  rewrite (rm_map_smul (cone_leg M j)).
  now rewrite mrefl_med_commutes.
Qed.

Program Definition mrefl_hom (N : Cone K) :
  vertex_obj[N] ~{RMod R}~> vertex_obj[M] := {| rm_hom := mrefl_med N |}.
Next Obligation. intros N r m; apply mrefl_med_smul. Qed.

Definition rmod_reflects : IsLimitCone M.
Proof using All.
  intro N.
  unshelve refine {| unique_obj := mrefl_hom N |}.
  - intros j a.
    exact (mrefl_med_commutes N j a).
  - intros v Hv a.
    exact (limit_med_unique (limitcone_isalimit HM)
             (FCone (RMod_Forget_Ab R) N) (rm_hom v) Hv a).
Defined.

End ModReflect.

(* * * [RMod_Forget_Ab] strictly creates every limit / * * [RMod_Forget_Ab] 严格地创造每一个限制 *)

Section ModStrictlyCreates.

Context {R : RingObject}.
Context {J : Category}.
Context (K : J ⟶ RMod R).

Definition rmod_strict_lift (N : Cone (RMod_Forget_Ab R ◯ K))
  (HN : IsLimitCone N) : StrictLift K (RMod_Forget_Ab R) N :=
  @Build_StrictLift J (RMod R) Ab K (RMod_Forget_Ab R) N
    (mlim_cone K (@Build_Limit J Ab (RMod_Forget_Ab R ◯ K) N HN))
    eq_refl
    (fun x => reflexivity _).

Definition RMod_Forget_Ab_StrictlyCreatesLimit :
  StrictlyCreatesLimit K (RMod_Forget_Ab R).
Proof.
  unshelve refine {| screates := rmod_strict_lift |}.
  - intros N HN.
    exact (@ump_limit _ _ _ _
             (mlim_created K (@Build_Limit J Ab (RMod_Forget_Ab R ◯ K) N HN))).
  - intros M HM.
    exact (rmod_reflects K M HM).
Defined.

Definition RMod_Forget_Ab_CreatesLimit : CreatesLimit K (RMod_Forget_Ab R) :=
  StrictlyCreatesLimit_CreatesLimit RMod_Forget_Ab_StrictlyCreatesLimit.

End ModStrictlyCreates.

Definition RMod_Forget_Ab_StrictlyCreatesLimits (R : RingObject) :
  StrictlyCreatesLimits (RMod_Forget_Ab R) :=
  fun J K => RMod_Forget_Ab_StrictlyCreatesLimit K.

Definition RMod_Forget_Ab_creates_limits (R : RingObject) :
  CreatesAllLimits (RMod_Forget_Ab R) :=
  fun J K => RMod_Forget_Ab_CreatesLimit K.

Definition RMod_Forget_Ab_reflects_limits {R : RingObject} {J : Category}
  (K : J ⟶ RMod R) : ReflectsLimitCone K (RMod_Forget_Ab R) :=
  creates_reflects_limits (RMod_Forget_Ab_CreatesLimit K).

Definition RMod_lift_cone_unique {R : RingObject} {J : Category}
  (K : J ⟶ RMod R) (N : Cone (RMod_Forget_Ab R ◯ K)) (HN : IsLimitCone N)
  (M : Cone K) (i : ConeIso (FCone (RMod_Forget_Ab R) M) N) :
  ConeIso M (slift_cone (screates N HN)) :=
  screates_lift_unique (RMod_Forget_Ab_StrictlyCreatesLimit K) N HN M i.

(* * * The image of a cone of modules is the underlying cone of groups / * * 模块圆锥的图像是群的基础圆锥 *)

Example rmod_fcone_apex {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (N : Cone K) :
  vertex_obj[FCone (RMod_Forget_Ab R) N] = rm_ab vertex_obj[N] := eq_refl.

Example rmod_fcone_leg {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (N : Cone K) (j : J) :
  cone_leg (FCone (RMod_Forget_Ab R) N) j = rm_hom (cone_leg N j) := eq_refl.

(* * * Mac Lane's Theorem 2: the lifting half / * * 麦克雷恩定理2：提升部分 *)

Definition RMod_Forget_Ab_lifts_limits {R : RingObject} {J : Category}
  (K : J ⟶ RMod R) (L : Limit (RMod_Forget_Ab R ◯ K)) : Limit K :=
  creates_limit_lift (RMod_Forget_Ab_CreatesLimit K) L.

Example rmod_lift_apex {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (L : Limit (RMod_Forget_Ab R ◯ K)) :
  RMod_Forget_Ab R (vertex_obj[RMod_Forget_Ab_lifts_limits K L])
    = vertex_obj[L] := eq_refl.

Example rmod_lift_legs {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (L : Limit (RMod_Forget_Ab R ◯ K)) (j : J) :
  fmap[RMod_Forget_Ab R]
    (cone_leg (@limit_cone _ _ _ (RMod_Forget_Ab_lifts_limits K L)) j)
    = limit_leg (limit_is_alimit L) j := eq_refl.

(*
   * * Corollaries: [RMod R] is complete, and both forgetful functors are
   continuous 

   --------
   * * 推论：[RMod R] 是完备的，并且两个遗忘函子都是连续的
*)

Definition RMod_Complete (R : RingObject) : @Complete (RMod R) :=
  creates_limits_Complete (RMod_Forget_Ab R) Ab_Complete
    (RMod_Forget_Ab_creates_limits R).

Definition RMod_Forget_Ab_creates_continuous (R : RingObject) :
  ContinuousFunctor (RMod_Forget_Ab R) :=
  creates_limits_continuous (RMod_Forget_Ab R) Ab_Complete
    (RMod_Forget_Ab_creates_limits R).

Definition RMod_Forget_Ab_PreservesAllLimits (R : RingObject) :
  PreservesAllLimits (RMod_Forget_Ab R) :=
  creates_limits_PreservesAllLimits (RMod_Forget_Ab R) Ab_Complete
    (RMod_Forget_Ab_creates_limits R).

Definition RMod_Forget_composite_continuous (R : RingObject) :
  ContinuousFunctor (Ab_Forget ◯ RMod_Forget_Ab R) :=
  continuous_compose (RMod_Forget_Ab_creates_continuous R)
    Ab_Forget_creates_continuous.

(*
 Instance/Mod.v's header says [RMod_Forget] agrees with the composite on
 objects and morphisms but is not the same record.  Both halves, read
 back.  The negative half is not stated as an [Example] -- it is a
 refusal, quoted in the header with its exact text. 

 --------
 Instance/Mod.v 的头文件写道 [RMod_Forget] 与复合体在对象和态射上是一致的，但不是同一个记录。两个部分都能回读。负半部分没有被声明为 [Example] —— 它是一种拒绝，在头文件中以其完整文本引用。
*)

Example rmod_forget_obj_agrees {R : RingObject} (M : RMod R) :
  RMod_Forget R M = (Ab_Forget ◯ RMod_Forget_Ab R) M := eq_refl.

Example rmod_forget_map_agrees {R : RingObject} {M N : RMod R}
  (f : M ~{RMod R}~> N) :
  fmap[RMod_Forget R] f = fmap[Ab_Forget ◯ RMod_Forget_Ab R] f := eq_refl.

Section ModForgetCone.

Context {R : RingObject}.
Context {J : Category}.
Context (K : J ⟶ RMod R).

(*
 The repackaging bridge: same apex, same legs, same coherence proof, a
 different record type.  Structure/Limit/Preservation.v's
 [cone_assoc] is the same move across functor associativity. 

 --------
 重新包装桥：相同的顶点，相同的边，相同的连贯性证明，不同的记录类型。Structure/Limit/Preservation.v 的 [cone_assoc] 是在函子结合性上的相同操作。
*)

Definition rmod_abcone_of (N : Cone (RMod_Forget R ◯ K)) :
  Cone ((Ab_Forget ◯ RMod_Forget_Ab R) ◯ K) :=
  @Build_Cone J Sets ((Ab_Forget ◯ RMod_Forget_Ab R) ◯ K)
    (@vertex_obj _ _ _ N)
    (@Build_ACone J Sets (@vertex_obj _ _ _ N)
       ((Ab_Forget ◯ RMod_Forget_Ab R) ◯ K)
       (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)).

End ModForgetCone.

Definition RMod_Forget_creates_continuous (R : RingObject) :
  ContinuousFunctor (RMod_Forget R) :=
  fun J K N HN M =>
    RMod_Forget_composite_continuous R J K N HN (rmod_abcone_of K M).

Definition RMod_Forget_PreservesAllLimits (R : RingObject) :
  PreservesAllLimits (RMod_Forget R) :=
  Continuous_PreservesAllLimits (RMod_Forget_creates_continuous R).

(* * * “Limits of modules are computed componentwise”, literally / * * “模的极限是按分量计算的”，字面意思 *)

(*
 At the limits [RMod_Complete] chooses -- [Ab_Complete] over
 [Sets_Complete], hence the compatible families of
 Instance/Sets/Complete.v -- the created module is the coordinatewise
 one ON THE NOSE: carrier, addition, zero, negation, SCALAR ACTION and
 every projection are all [eq_refl], at an arbitrary ring, an arbitrary
 shape and an arbitrary diagram of modules.  The fifth is the one with
 no counterpart in the template, and it holds even though the chosen
 limit reaches its mediator through [creates_limiting]. 

 --------
 在极限处，[RMod_Complete] 选择 [Ab_Complete] 而不是 [Sets_Complete]，因此 Instance/Sets/Complete.v 的兼容族——创建的模块在各坐标上是完全一样的：载体，加法，零元，取负，标量作用以及每个投影在任意环、任意形状和任意模图中都是 [eq_refl]。第五个是模板中没有对应的，即使所选择的极限通过 [creates_limiting] 达到其中介，它依然成立。
*)

Section RModComputed.

Context {R : RingObject}.
Context {J : Category}.
Context (K : J ⟶ RMod R).

Example rmod_complete_carrier :
  cmon_setoid (ab_cmon (rm_ab (vertex_obj[RMod_Complete R J K])))
    = Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K)) := eq_refl.

Example rmod_complete_plus
  (a b : carrier (Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K))))
  (d : J) :
  `1 (cmon_plus (rm_ab (vertex_obj[RMod_Complete R J K])) a b) d
    = cmon_plus (rm_ab (K d)) (`1 a d) (`1 b d) := eq_refl.

Example rmod_complete_zero (d : J) :
  `1 (cmon_zero (rm_ab (vertex_obj[RMod_Complete R J K]))) d
    = cmon_zero (rm_ab (K d)) := eq_refl.

Example rmod_complete_neg
  (a : carrier (Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K))))
  (d : J) :
  `1 (ab_neg (rm_ab (vertex_obj[RMod_Complete R J K])) a) d
    = ab_neg (rm_ab (K d)) (`1 a d) := eq_refl.

Example rmod_complete_smul (r : carrier (rig_setoid (ring_rig R)))
  (a : carrier (Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K))))
  (d : J) :
  `1 (rm_smul (vertex_obj[RMod_Complete R J K]) r a) d
    = rm_smul (K d) r (`1 a d) := eq_refl.

Example rmod_complete_leg (d : J) :
  cmon_map (rm_hom (cone_leg (@limit_cone _ _ _ (RMod_Complete R J K)) d))
    = Sets_limit_leg (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K)) d := eq_refl.

End RModComputed.
