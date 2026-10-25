(* * * The group-action monad G × (−) and its algebras, the G-sets / * * 群作用单子 G × (−) 及其代数，G-集合 *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.Beck.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Group.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Action.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.

Generalizable All Variables.

(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Springer GTM 5, 1998, §VI.2, "Group actions", printed p. 141
 (PDF p. 150) — maclane:VI.2:remark2
 Book: Riehl, "Category Theory in Context", 2nd ed., Exercise
 5.5.iv, printed p. 208 (PDF p. 228) — riehl:5.5:exiv; with her
 Theorem 5.5.1, printed p. 202, and Definition 5.3.1, printed
 p. 196
 nLab: https://ncatlab.org/nlab/show/action
 nLab: https://ncatlab.org/nlab/show/monadicity+theorem

 Mac Lane ends §VI.2 with "several examples which show that the
 T-algebras for familiar monads are the familiar algebras".  The second
 is the group action: for a group G, TX = G × X with η x = ⟨u, x⟩ and
 μ ⟨g₁, ⟨g₂, x⟩⟩ = ⟨g₁g₂, x⟩ "define a monad ⟨T, η, μ⟩ on Set", and a
 T-algebra is a structure map h : G × X → X "such that always
 h(g₁g₂, x) = h(g₁, h(g₂, x)), h(u, x) = x.  If we write g · x for
 h(g, x), these are just the usual conditions that ⟨g, x⟩ ↦ g · x
 defines an action of the group G on the set X."  Riehl's Exercise
 5.5.iv supplies the adjunction behind the monad: the forgetful functor
 U : Set^BG → Set has a left adjoint sending a set X to "the G-set
 G × X, with G acting on the left", and the exercise is to "Prove that
 this adjunction is monadic by appealing to the monadicity theorem" —
 her Theorem 5.5.1, "A right adjoint functor U : D → C is monadic if and
 only if it creates coequalizers of U-split pairs".  This file does
 both, and proves the monadicity a second time by an explicit
 quasi-inverse.

 THE CATEGORY OF G-SETS IS NOT BUILT HERE.  Instance/Fun/Action.v has
 it: [MSet M], the actions [MSetoidAction] of Construction/Deloop/
 Functors.v with the equivariant maps, for any [MonObject] M of
 Construction/Deloop.v, and [MSet_Fun_equiv : [Deloop M, Sets] ≅[Cat]
 MSet M], which identifies it with Riehl's Set^BG (BG is [Deloop G]).
 Every statement below is over a MONOID M, since neither the monad nor
 the algebra correspondence uses inverses, and the groups come at the
 end.  [act_op], the action law of [MSetoidAction], reads
 act (g h) x ≈ act g (act h x): Mac Lane's printed law, in his
 orientation.  The file sits beside its donor category; the issue's
 suggested path, Instance/Sets/Action.v, is not used.

 THE MONAD IS THE MONAD OF AN ADJUNCTION.  [FreeAct X] is the free
 M-set on X, M × X acted on in the left factor, g · (h, x) = (g h, x),
 and [MSet_adj] is Riehl's adjunction [MSet_Free M ⊣ MSet_Forget M]: an
 equivariant φ out of M × X restricts to x ↦ φ (u, x) ([MSet_restrict]),
 and ψ extends back to (g, x) ↦ g · ψ x ([MSet_extend]).  [ActF M] is
 the composite U ◯ F and [ActMonad M] is Monad/Comparison.v's
 [Adjunction_Induced_Monad], whose ret is η and whose join is U ε F,
 both transparent; so Mac Lane's formulas are read back by [eq_refl]
 ([ActF_obj], [ActF_map], [ActMonad_ret], [ActMonad_join]).  The monad
 laws are not proved by hand: they are those of the adjunction, derived
 in Monad/Comparison.v.  A functor built by hand with the same object
 and arrow maps is ≈ to [ActF M] but not equal to it, the proof fields
 differing (measured), and no second monad is kept.  The precedent for
 the pattern is Instance/Grp/FreeAFT.v's [free_group_monad].

 ALGEBRAS ARE ACTIONS.  [EM_act] reads an algebra (X, h) as the action
 g · x := h (g, x).  Its unit law is [t_id]; its action law is the
 symmetry of [t_action], which Monad/Algebra.v states as
 t_alg ∘ fmap t_alg ≈ t_alg ∘ join, that is h(g₁, h(g₂, x)) ≈ h(g₁g₂, x),
 the two sides of Mac Lane's equation exchanged.  [EM_to_MSet] is the
 functor; with Monad/Comparison.v's comparison functor [EM_Comparison] it
 forms [MSet_comparison_equivalence], identity components both ways.
 Hence [MSet_Forget_Monadic_direct] and
 [EM_MSet_iso : MSet M ≅[Cat] EilenbergMoore (ActF M)], whose [to] leg IS
 the comparison functor ([EM_MSet_iso_to]), whose [from] leg IS
 [EM_to_MSet] ([EM_MSet_iso_from]), and whose comparison algebra at (g, a)
 is g · a ([comparison_alg_is_action]).  [Fun_EM_iso] composes
 [MSet_Fun_equiv] with it: Riehl's Set^BG is isomorphic in Cat to the
 algebras.

 RIEHL'S ROUTE, BY BECK.  [MSet_Forget_creates] is the creation of
 coequalizers of U-split pairs, in Monad/Monadicity/Beck.v's
 isomorphism-invariant sense.  Over a split coequalizer e : U B → Z,
 with sections s and t downstairs, the created M-set is Z itself with
 g · z := e (g · s z) ([CreatedAct]).  That this is an action, and that
 e is equivariant, both rest on one absorption: a map out of B that
 coforks the pair absorbs s ∘ e ([split_absorb], [created_absorb]).  The
 lift chosen is on the nose — the carrier IS Z, the action IS
 e (g · s z), the coequalizing arrow IS e and the comparison isomorphism
 IS the identity ([mset_created_carrier], [mset_created_action],
 [mset_created_arrow], [mset_created_iso]) — although the class asks
 only for an isomorphism (uniqueness of such a lift, Mac Lane's strict
 creation, is not claimed).  Beck.v's [beck_monadicity] then gives
 [MSet_beck_equivalence] and [MSet_Forget_Monadic]; it is the first use
 of [beck_monadicity] in the tree.  [MSet_Forget_reflects], a bijective
 equivariant map is an isomorphism, is Beck.v's
 [creates_split_reflects_isos] at this instance.  The two routes are
 equivalences of the same functor, on the nose ([EM_MSet_iso_beck_to],
 [beck_direct_to]); their quasi-inverses differ.  Beck's keeps the
 carrier and acts through η, g · z = h (g u, z) ([beck_carrier],
 [beck_act]), and it is ≈ to [EM_to_MSet] ([beck_vs_direct]).

 WHICH "MONADIC".  Riehl's Definition 5.3.1 calls an adjunction monadic
 when the comparison functor "defines an equivalence of categories"; that
 is Monad/Comparison.v's [Monadic], and the "if" half of her Theorem 5.5.1
 is Beck.v's [beck_monadicity], both in the equivalence form.  Mac Lane
 (§VI.3, printed p. 143) says instead that G is monadic when the
 comparison functor K "will be an isomorphism", and his Beck theorem
 (§VI.7, Theorem 1, printed p. 151) is stated for that strict form, with
 "creates" meaning a unique lift on the nose.  This file implements
 Riehl's reading.  The [≅[Cat]] above is the tree's isomorphism in Cat,
 inverse up to natural isomorphism, hence an equivalence.

 STRENGTHS.  By [eq_refl]: Mac Lane's formulas for T, η and μ, η also as a
 function ([ActMonad_ret_fun]), μ at each triple and as a function
 ([ActMonad_join_fun]); the [to] legs of both Cat isomorphisms, and the
 [from] leg of the direct one ([EM_MSet_iso_from]); the comparison algebra
 at (g, a) and as a function ([comparison_alg_fun]); [EM_act]'s action at
 (g, a); the lift the creation chooses; Beck's quasi-inverse on carriers
 and its action through η.  The pair forms are stated as Mac Lane writes
 them; the function forms are the stronger statements, since Coq's [prod]
 has no eta.  In Test/ProbeGroupAction464.v, also by [eq_refl]: the M-set
 round trip through the algebras on its carrier and on its action as a
 function, and the algebra round trip on its carrier and on its structure
 map at each pair.  At ≈ only, as natural isomorphisms with identity
 components: the two composites of [EM_Comparison] and [EM_to_MSet]
 against the identity functors, Beck's quasi-inverse against [EM_to_MSet],
 and the hand-built functor against [ActF M].  Refused by conversion, each
 pinned in that probe (its N1-N12): the law fields [act_op], [act_unit]
 and [act_respects] of the round trip, the whole M-set, the two composites
 as the identity functors, the structure map as a function (the round trip
 reads h (fst p, snd p)), the whole algebra, Beck's quasi-inverse as
 [EM_to_MSet], its action as h (g, z), the two [Monadic] witnesses as one
 term, and the hand-built functor as [ActF M].
 CORRECTION (#1347): the [act_respects] field of the round trip, the
 probe's N3, now holds at [eq_refl], since Instance/Sets.v gives its
 identity's and composite's properness fields as terms; it is a control
 there.

 WHY THE ROUND TRIP IS REFUSED.  The [act_unit] and [act_op] fields of
 the round trip are composite proofs built from the adjunction, and
 [act_op] is in addition the symmetry of [t_action].  The
 [act_respects] field is [act_respects A] itself except that its last
 argument passes through the identity map's properness proof, which is
 Corelib's opaque [subrelation_id_proper] (read off at [eq_refl] by the
 probe's control beside N3); that refusal is opacity, outside the tree.
 In a copy of the dependency closure in which only Instance/Sets.v's
 [setoid_morphism_id] was changed, its properness proof written as
 fun _ _ H => H, N3 holds at [eq_refl] and the other eleven are still
 refused.  None of those eleven rests on an opaque constant of the
 tree: with every [Qed] of this file and its closure turned into
 [Defined] and [Transparent Obligations] set (Instance/Sets.v and
 Structure/Cartesian/Closed.v, where the change is itself refused, and
 Instance/Grp.v, where it raises [grp_deloop_monoid]'s universe arity
 from 3 to 5, keeping their [Qed]s, and Structure/Limit/
 Preservation.v's [preserves_colimit], which no compared term uses,
 made opaque, its script stopping under the added transparency), all
 twelve refusals stand and their positive controls hold; eleven are
 thereby not opacity of the tree, and the twelfth, N3, is the Corelib
 opacity above, which no such change reaches.
 CORRECTION (#1347): the copy's change is now the tree's, the
 composite's field written as a term too, and N3 holds at [eq_refl];
 the other eleven are still refused.  N3's attribution to Corelib's
 opaque [subrelation_id_proper] was right.

 GROUPS.  [GAct_Monad] and [GSet_Forget_Monadic] take Construction/
 Deloop.v's [GrpObject], which is a [MonObject] by coercion.
 [GAct_Monad_Grp] and [GSet_Forget_Monadic_Grp] take Instance/Grp.v's,
 through Instance/Grp/Free.v's [grp_deloop_monoid].  Both files declare
 a [GrpObject], both are imported here, and every use is written with
 its full path.  [GAct_Monad_GroupObject] and
 [GSet_Forget_Monadic_GroupObject] take Structure/Group.v's
 [GroupObject] in (Sets, ×) through Instance/Grp.v's
 [GroupObject_GrpObject], which needs [PropEquiv] of the carrier.

 UNIVERSES, read off [About].  Every constant binds [@{o so}] ([act_prod]
 and [FreeAct] only [@{o}]), with M : MonObject@{o o o}; o is the level of
 carriers and hom-setoids (the objects of Sets live at so).  The three
 Cat isomorphisms add [c], and so do their three [to] readbacks and
 [EM_MSet_iso_from].  The only strict bounds are [o < so], on every
 constant that binds so, and [o < c, so < c] on the seven that name Cat;
 there is no [Set] and no equation.  [o < so] is first carried by
 Instance/Sets.v's [Sets], whose own block states it; [o < c] and [so < c]
 by Instance/Cat.v's [Cat@{c so so so o}].  The last universe of
 [Adjunction], which occurs in no constraint of its block, is pinned to so
 rather than bound as a third level, as
 [Adjunction@{so o o so o o o o so o so}], and the witnesses are
 [Monadic@{so so so so so o so so}].  The stdlib caps are the donors':
 compose and ID from [Sets]; prod_rect and projections (the pair
 projections) from [prod_setoid], in [act_prod], and [so <= projections]
 with Logic_lemmas.equality from Theory/Adjunction.v's
 [Build_Adjunction']; Projections (the sigma projections) from
 [EilenbergMoore], from [beck_monadicity] ([o <= Projections.u0]) and, in
 the [mset_created_*] readbacks, from the projections their statements
 apply; eq_ind and eq_ind_r from [GroupObject_GrpObject].  A [simpl] after
 [split] in [beck_vs_direct_iso]'s proof added the strict bound
 [o < Projections.u0] (already implied by o < so and
 so <= Projections.u0); it was removed and the bound is gone.

 NOT DELIVERED.  Mac Lane's strict monadicity, the comparison functor
 an isomorphism on the nose: the whole-object round trips are refused
 at [eq_refl], above.  Monadicity of Riehl's literal forgetful functor,
 evaluation [Deloop M, Sets] ⟶ Sets, is not proved in this file: no
 lemma in the tree transports [Monadic] along an equivalence such as
 [MSet_Fun_equiv], and [Fun_EM_iso] is the statement given here.
 Instance/Fun/Action/Monad/BG.v proves it on the functor category
 itself, by Beck's theorem again ([U_BG_Monadic]), and its [tie] shows
 that the comparison functor there, followed by the functor [BG_Act_EM]
 from the algebras of its monad to those of [ActMonad M], is ≈ the [to]
 leg of [Fun_EM_iso].  The tree has no general morphisms of monads, so
 no second, hand-built monad is kept here and no Eilenberg–Moore
 category is transported along one; BG.v's [BG_Act_EM] is the one such
 functor on algebras, built by hand for its instance.  The converse half
 of Riehl's theorem is Beck.v's [monadic_creates], stated at
 [EM_Forget] and not instantiated here.  No Kleisli category of
 G × (−) is identified.

 CORRECTION (#468).  The tree now has general morphisms of monads,
 Monad/Morphism.v's [MonadHom] and [Monads C], and the functor they induce
 on algebras, Monad/Morphism/Algebra.v's θ* ([mh_EM]);
 Instance/Fun/Action/Monad/BG/Morphism.v relates BG.v's [BG_Act_EM] to it.
 This file is unchanged: it keeps one monad, and no Eilenberg–Moore
 category is transported here. 

 --------
 书籍：Mac Lane, 《给工作的数学家的范畴论》, 第二版，Springer GTM 5, 1998, §VI.2, “群作用”, 印刷第141页（PDF第150页） — maclane:VI.2:remark2
 书籍：Riehl, 《范畴论在上下文中》, 第二版, 练习 5.5.iv, 印刷第208页（PDF第228页） — riehl:5.5:exiv；及其定理 5.5.1, 印刷第202页, 和定义 5.3.1, 印刷第196页
 nLab: https://ncatlab.org/nlab/show/action
 nLab: https://ncatlab.org/nlab/show/monadicity+theoremMac Lane 在 §VI.2 章节的结尾写道：“几个例子显示了熟悉的单子（monads）的 T-代数就是熟悉的代数”。第二个例子是群作用：对于一个群 G，TX = G × X，并且 η x = ⟨u, x⟩，μ ⟨g₁, ⟨g₂, x⟩⟩ = ⟨g₁g₂, x⟩，“在集合上定义一个单子 ⟨T, η, μ⟩”，而 T-代数是一个结构映射 h : G × X → X，“满足始终有 h(g₁g₂, x) = h(g₁, h(g₂, x)), h(u, x) = x。”如果我们将 g · x 写作 h(g, x)，这些只是通常的条件，即 ⟨g, x⟩ ↦ g · x 定义了群 G 在集合 X 上的一个作用。Riehl 的练习 5.5.iv 提供了单子背后的伴随关系：将遗忘函子 U : Set^BG → Set 有一个左伴随，将集合 X 映射为“G-集合 G × X，并且 G 在左侧作用”，而练习要求“通过调用单子性定理证明这个伴随是单子的”——她的定理 5.5.1，“如果右伴随函子 U : D → C 恰好能够创造 U-分裂对的上同余，那么它是单子的”。这个文件做了两件事，并通过一个显式的拟逆再次证明了单子性。这里没有构建 G-集合的范畴。Instance/Fun/Action.v 中有它：[MSet M]，Construction/Deloop/Functors.v 中的作用 [MSetoidAction] 及其等变映射，对于 Construction/Deloop.v 中的任意 [MonObject] M，以及 [MSet_Fun_equiv : [Deloop M, Sets] ≅ [Cat] MSet M]，它将其与 Riehl 的 Set^BG（BG 是 [Deloop G]）对应起来。下面的每个陈述都是基于一个单子 M，因为无论是 monad 还是代数对应都不使用逆元，群体在最后出现。[act_op]，[MSetoidAction] 的作用律为 act (g h) x ≈ act g (act h x)：Mac Lane 印刷的定律，其方向就是如此。该文件位于其来源范畴旁边；建议的路径 Instance/Sets/Action.v 未被使用。幺半群是伴随算子的幺半群。[FreeAct X] 是 X 上的自由 M-集合，M × X 在左因子上作用，g · (h, x) = (g h, x)，而 [MSet_adj] 是 Riehl 的伴随 [MSet_Free M ⊣ MSet_Forget M]：M × X 的一个等变 φ 限制为 x ↦ φ(u, x) ([MSet_restrict])，而 ψ 又扩展回 (g, x) ↦ g · ψ x ([MSet_extend])。[ActF M] 是复合 U ◦ F，[ActMonad M] 是 Monad/Comparison.v 的 [Adjunction_Induced_Monad]，其 ret 为 η，join 为 U ε F，两者均为透明；因此 Mac Lane 的公式通过 [eq_refl] 被读取回去 ([ActF_obj], [ActF_map], [ActMonad_ret], [ActMonad_join])。幺半群定律没有手工证明：它们是伴随算子的定律，在 Monad/Comparison.v 中推导得到。使用相同的对象和箭头映射手工构建的函子 ≈ [ActF M]，但不等于它，证明字段不同（已测量），且没有保留第二个单子。该模式的先例是 Instance/Grp/FreeAFT.v 的 [free_group_monad]。代数就是作用。[EM_act] 将代数 (X, h) 读作作用 g · x := h (g, x)。它的单位律是 [t_id]；它的作用律是 [t_action] 的对称性，Monad/Algebra.v 表述为 t_alg ∘ fmap t_alg ≈ t_alg ∘ join，也就是 h(g₁, h(g₂, x)) ≈ h(g₁g₂, x)，Mac Lane 方程的两边互换。[EM_to_MSet] 是函子；与 Monad/Comparison.v 的比较函子 [EM_Comparison] 一起形成 [MSet_comparison_equivalence]，两边都是恒等分量。因此 [MSet_Forget_Monadic_direct] 和 [EM_MSet_iso : MSet M ≅[Cat] EilenbergMoore (ActF M)]，其 [to] 分支是比较函子 ([EM_MSet_iso_to])，其 [from] 分支是 [EM_to_MSet] ([EM_MSet_iso_from])，且在 (g, a) 的比较代数是 g · a ([comparison_alg_is_action])。[Fun_EM_iso] 将 [MSet_Fun_equiv] 与其组合：Riehl 的 Set^BG 在 Cat 中与代数同构。RIEHL 的路径，由 BECK 提出。[MSet_Forget_creates] 是 U-拆分对的共同余等子的创造，在 Monad/Monadicity/Beck.v 的同构不变意义下。对于一个拆分共同余等子 e : U B → Z，底层有截面 s 和 t，所创建的 M-集合是 Z 本身，其作用定义为 g · z := e (g · s z) ([CreatedAct])。这是一个作用，并且 e 是等变的，这两者都依赖于一个吸收性质：一个从 B 出发的映射，如果共同分岔该对，则吸收 s ∘ e ([split_absorb], [created_absorb])。所选的提升是直接的——载体就是 Z，作用就是 e (g · s z)，共同余等箭就是 e，对应的比较同构就是恒等 ([mset_created_carrier], [mset_created_action], [mset_created_arrow], [mset_created_iso])——尽管课程只要求存在一个同构（不声称此类提升的唯一性，也就是 Mac Lane 的严格创造）。Beck.v 的 [beck_monadicity] 然后给出了 [MSet_beck_equivalence] 和 [MSet_Forget_Monadic]；这是 [beck_monadicity] 在树中首次使用。[MSet_Forget_reflects]，一个双射等变映射是同构，是 Beck.v 在此实例中的 [creates_split_reflects_isos]。两条路径是同一个函子的等价，严格相等（[EM_MSet_iso_beck_to], [beck_direct_to]）；它们的准逆不同。Beck 的保持承载并通过 η 作用，g · z = h (g u, z)（[beck_carrier], [beck_act]），并且它与 [EM_to_MSet] 近似（[beck_vs_direct]）。哪一个“单子化”。Riehl 的定义 5.3.1 说，当比较函子“定义了范畴等价”时，一个函子对是单子化的；也就是说，Monad/Comparison.v 的 [Monadic]，以及她的定理 5.5.1 的“如果”部分是 Beck.v 的 [beck_monadicity]，都是等价形式。Mac Lane（§VI.3，印刷页 143）则说，当比较函子 K“将是一个同构”时，G 是单子化的，他的 Beck 定理（§VI.7，定理 1，印刷页 151）以这种严格形式表述，其中“创建”意味着精确的唯一提升。此文件实现了 Riehl 的解读。上面的 [≅[Cat] 是 Cat 中树的同构，至多自然同构的逆，因此是一个等价。优势。由[eq_refl]：Mac Lane 关于 T、η 和 μ 的公式，η 也作为一个函数（[ActMonad_ret_fun]），μ 在每个三元组上以及作为一个函数（[ActMonad_join_fun]）；两个 Cat 同构的 [to] 边，以及直接同构的 [from] 边（[EM_MSet_iso_from]）；在 (g, a) 处以及作为函数的比较代数（[comparison_alg_fun]）；[EM_act] 在 (g, a) 处的作用；选择创建的提取；Beck 在承载上的拟逆及其通过 η 的作用。对形式如 Mac Lane 所写的陈述；函数形式是更强的陈述，因为 Coq 的 [prod] 没有 eta。在 Test/ProbeGroupAction464.v 中，也由 [eq_refl]：通过其承载上的代数以及作为函数作用的 M-集合的往返，以及它的承载和每个对的结构映射上的代数往返。在 ≈ 上仅作为具有恒等分量的自然同构：[EM_Comparison] 和 [EM_to_MSet] 对应恒等函子 的两个复合，Beck 的准逆对应 [EM_to_MSet]，以及手工构建的函子对应 [ActF M]。因转换而被拒绝，每个都固定在那个探针中（其 N1-N12）：环路法则 [act_op]、[act_unit] 和 [act_respects]，整个 M-集合，作为恒等函子的两个复合，作为函数的结构映射（环路读作 h(fst p, snd p)），整个代数，Beck 的准逆作为 [EM_to_MSet]，其作用为 h(g, z)，两个 [Monadic] 的见证作为一个项，以及手工构建的函子作为 [ActF M]。更正 (#1347)：往返行程的 [act_respects] 字段，探针的 N3，现在保持在 [eq_refl]，因为 Instance/Sets.v 提供了它的标识和复合体的适当性字段作为项；这是那里的一种控制。为什么回程被拒绝。回程的 [act_unit] 和 [act_op] 字段是由附加操作构建的复合证明，并且 [act_op] 另外是 [t_action] 的对称性。[act_respects] 字段是 [act_respects A] 本身，只是它的最后一个参数通过同一映射的正确性证明，该证明是 Corelib 的不透明 [subrelation_id_proper]（通过 N3 旁的探针控制在 [eq_refl] 读取）；这种拒绝是不透明性，位于树之外。在依赖闭包的一份副本中，其中仅更改了 Instance/Sets.v 的 [setoid_morphism_id]，其正确性证明写作 fun _ _ H => H，N3 在 [eq_refl] 保持有效，其余十一项仍被拒绝。这十一项都不依赖于树的一个不透明常量：将此文件及其闭包中的每个 [Qed] 都转换为 [Defined] 和 [Transparent Obligations] 集（Instance/Sets.v 和 Structure/Cartesian/Closed.v，其中更改本身被拒绝，以及 Instance/Grp.v，其中将 [grp_deloop_monoid] 的宇宙元数从 3 提升到 5，同时保留它们的 [Qed]s，以及 Structure/Limit/Preservation.v 的 [preserves_colimit]，未被任何比较项使用，被设为不透明，其脚本在添加的透明性下停止），所有十二次拒绝仍然成立，并且它们的正向控制保持有效；因此其中十一项不是树的不透明性，第十二项 N3 是上文提到的 Corelib 不透明性，这种更改无法触及。更正 (#1347)：副本的更改现在属于树，复合的字段也作为术语写入，并且 N3 在 [eq_refl] 上成立；其他十一项仍然被拒绝。N3 对 Corelib 的不透明 [subrelation_id_proper] 的归属是正确的。

 群组。[GAct_Monad] 和 [GSet_Forget_Monadic] 使用 Construction/Deloop.v 的 [GrpObject]，它是通过强制转换得到的 [MonObject]。[GAct_Monad_Grp] 和 [GSet_Forget_Monadic_Grp] 使用 Instance/Grp.v 的 [grp_deloop_monoid]，通过 Instance/Grp/Free.v 获取。两个文件都声明了 [GrpObject]，都在此处导入，并且每次使用都写出完整路径。[GAct_Monad_GroupObject] 和 [GSet_Forget_Monadic_GroupObject] 使用 Structure/Group.v 的 [GroupObject]，在 (Sets, ×) 中通过 Instance/Grp.v 的 [GroupObject_GrpObject]，需要载体的 [PropEquiv]。宇宙，读取 [About]。每个常量绑定 [@{o so}]（[act_prod] 和 [FreeAct] 仅 [@{o}]），M : MonObject@{o o o}；o 是载体和同构集合的层级（集合对象位于 so）。这三个类别同构增加 [c]，它们的三个 [to] 读取回和 [EM_MSet_iso_from] 也是如此。唯一严格的界限是 [o < so]，作用于绑定的每个常量，以及 [o < c, so < c] 作用于命名 Cat 的七个；没有 [Set]，也没有方程。[o < so] 首先由 Instance/Sets.v 的 [Sets] 承载，其自身代码块声明了它；[o < c] 和 [so < c] 由 Instance/Cat.v 的 [Cat@{c so so so o}] 承载。[Adjunction] 的最后一个宇宙，在其代码块的任何约束中未出现，固定为 so 而不是绑定为第三层，如 [Adjunction@{so o o so o o o o so o so}]，见证者是 [Monadic@{so so so so so o so so}]。stdlib 的上限是捐赠者的：从 [Sets] 得到的 compose 和 ID；从 [prod_setoid] 得到的 prod_rect 和 projections（配对 projections），在 [act_prod] 和 [so <= projections] 中，以及来自 Theory/Adjunction.v 的 Logic_lemmas.equality 的 [Build_Adjunction']；从 [EilenbergMoore] 得到的 Projections（σ 投影），从 [beck_monadicity]（[o <= Projections.u0]）以及在 [mset_created_*] 的读回中，从 projections 得到其语句应用；从 [GroupObject_GrpObject] 得到的 eq_ind 和 eq_ind_r。[simpl] 在 [beck_vs_direct_iso] 的证明中 [split] 后添加了严格的边界 [o < Projections.u0]（已经被 o < so 且 so <= Projections.u0 所隐含）；它已被移除，边界也不存在了。未交付。Mac Lane 的严格单子性，比较函子在本质上是一个同构：整个对象的往返在上面的 [eq_refl] 被拒绝。Riehl 的字面遗忘函子 R 的单子性，评估  [Deloop M, Sets] ⟶ Sets，在此文件中并未证明：树中的没有引理沿着类似 [MSet_Fun_equiv] 的等价传输 [Monadic]，并且 [Fun_EM_iso] 是此处给出的陈述。Instance/Fun/Action/Monad/BG.v 在函子范畴本身上通过 Beck 定理再次证明了它（[U_BG_Monadic]），并且其 [tie] 显示那里比较函子，随后是从其单子的代数到 [ActMonad M] 的代数的函子 [BG_Act_EM]，≈ [Fun_EM_iso] 的 [to] 分支。这棵树没有单子的一般态射，因此这里没有保留第二个手工构建的单子，也没有沿着单子传输Eilenberg–Moore范畴。BG.v 的 [BG_Act_EM] 是代数上此类函子之一，为其实例手工构建。Riehl 定理的逆半部分是 Beck.v 的 [monadic_creates]，在 [EM_Forget] 中陈述，但未在此实例化。G × (−) 的 Kleisli 范畴未被识别。

 更正 (#468)。现在这棵树具有单子的一般态射，Monad/Morphism.v 的 [MonadHom] 和 [Monads C] 以及它们在代数上诱导的函子，Monad/Morphism/Algebra.v 的 θ* ([mh_EM]); Instance/Fun/Action/Monad/BG/Morphism.v 将 BG.v 的 [BG_Act_EM] 与其关联。此文件未更改：它保留一个单子，并且没有 Eilenberg–Moore 范畴被传输到此处。
*)

(** ** The product M × X / ** 产品 M × X *)

(*
 The carrier of G × X, compared componentwise (Lib/Datatypes.v's
 [prod_setoid], the relation of Instance/Sets/Cartesian.v's product). 

 --------
 G × X 的载体，按分量比较（Lib/Datatypes.v 中的 [prod_setoid]，Instance/Sets/Cartesian.v 中的积的关系）。
*)
Definition act_prod@{o} (M : MonObject@{o o o}) (X : SetoidObject@{o o}) :
  SetoidObject@{o o} :=
  @Build_SetoidObject (carrier M * carrier X)%type prod_setoid.

(* G × f : G × X → G × Y, the identity on the first factor. / G × f ：G × X → G × Y，第一个因子的恒等映射。 *)
Definition act_prod_map@{o so} (M : MonObject@{o o o})
  {X Y : SetoidObject@{o o}} (f : X ~{Sets@{o so}}~> Y) :
  act_prod M X ~{Sets@{o so}}~> act_prod M Y.
Proof.
  unshelve refine
    (@Build_SetoidMorphism (carrier M * carrier X) prod_setoid
       (carrier M * carrier Y) prod_setoid (fun p => (fst p, f (snd p))) _).
  intros p q [Hg Hx].
  split; [ exact Hg | exact (proper_morphism f _ _ Hx) ].
Defined.

(* * ** The free M-set and the forgetful functor / * ** 自由 M-集与遗忘函子 *)

(* The free M-set on X: M × X with M acting on the left factor, g · (h, x) = (g h, x). / X 上的自由 M 集合：M × X，其中 M 作用于左侧因子，g · (h, x) = (g h, x)。 *)
Definition FreeAct@{o} {M : MonObject@{o o o}} (X : SetoidObject@{o o}) :
  MSetoidAction@{o o o o o o o o} M.
Proof.
  unshelve refine
    (@Build_MSetoidAction M (act_prod M X)
       (fun g p => (mon_op g (fst p), snd p)) _ _ _).
  - intros g g' Hg p q [H1 H2].
    split; simpl;
      [ exact (mon_op_respects M g g' Hg (fst p) (fst q) H1) | exact H2 ].
  - intros [g x].
    split; simpl; [ exact (mon_op_unit_l g) | reflexivity ].
  - intros g h [k x].
    split; simpl; [ exact (mon_op_assoc_sym M g h k) | reflexivity ].
Defined.

(* U : MSet M ⟶ Sets forgets the action. / U : MSet M ⟶ Sets 忘记了作用。 *)
Definition MSet_Forget@{o so} (M : MonObject@{o o o}) :
  MSet@{so so o o o o o o} M ⟶ Sets@{o so}.
Proof.
  unshelve refine
    (@Build_Functor (MSet@{so so o o o o o o} M) Sets@{o so}
       (fun A => act_setoid A) (fun A B h => equiv_map h) _ _ _).
  - intros A B h h' Hh. exact Hh.
  - intros A a. reflexivity.
  - intros A B C f g a. reflexivity.
Defined.

(* F : Sets ⟶ MSet M sends X to the free M-set M × X. / F : 集合 ⟶ M集 M 将 X 映射到自由 M-集 M × X。 *)
Definition MSet_Free@{o so} (M : MonObject@{o o o}) :
  Sets@{o so} ⟶ MSet@{so so o o o o o o} M.
Proof.
  unshelve refine
    (@Build_Functor Sets@{o so} (MSet@{so so o o o o o o} M)
       (fun X => @FreeAct M X)
       (fun X Y f => @Build_Equivariant M (@FreeAct M X) (@FreeAct M Y)
                       (act_prod_map@{o so} M f) _)
       _ _ _).
  - intros g p. split; reflexivity.
  - intros X Y f f' Hf p. split; [ reflexivity | exact (Hf (snd p)) ].
  - intros X p. split; reflexivity.
  - intros X Y Z f g p. split; reflexivity.
Defined.

(** ** The free/forgetful adjunction / ** 自由/遗忘的伴随 *)

(* A map ψ : X → U A extends to the equivariant (g, x) ↦ g · ψ x. / 映射 ψ : X → U A 扩展为等变映射 (g, x) ↦ g · ψ x。 *)
Definition MSet_extend@{o so} {M : MonObject@{o o o}}
  {X : SetoidObject@{o o}} {A : MSetoidAction@{o o o o o o o o} M}
  (ψ : X ~{Sets@{o so}}~> act_setoid A) :
  fobj[MSet_Free@{o so} M] X ~{MSet@{so so o o o o o o} M}~> A.
Proof.
  unshelve refine
    (@Build_Equivariant M (@FreeAct M X) A
       (@Build_SetoidMorphism (carrier M * carrier X) prod_setoid
          (carrier (act_setoid A)) _
          (fun p => act A (fst p) (ψ (snd p))) _) _).
  - intros p q [Hg Hx].
    exact (act_respects A _ _ Hg _ _ (proper_morphism ψ _ _ Hx)).
  - intros g [h x]; simpl. apply act_op.
Defined.

(* An equivariant φ : F X → A restricts to x ↦ φ (e, x). / 一个等变的 φ : F X → A 限制为 x ↦ φ (e, x)。 *)
Definition MSet_restrict@{o so} {M : MonObject@{o o o}}
  {X : SetoidObject@{o o}} {A : MSetoidAction@{o o o o o o o o} M}
  (φ : fobj[MSet_Free@{o so} M] X ~{MSet@{so so o o o o o o} M}~> A) :
  X ~{Sets@{o so}}~> fobj[MSet_Forget@{o so} M] A.
Proof.
  unshelve refine
    (@Build_SetoidMorphism X _ (act_setoid A) _
       (fun x => equiv_map φ (mon_unit, x)) _).
  intros x y Hxy. apply (proper_morphism (equiv_map φ)).
  split; [ reflexivity | exact Hxy ].
Defined.

Definition MSet_adj_iso@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) (A : MSetoidAction@{o o o o o o o o} M) :
  @Isomorphism Sets@{o so}
    (@Build_SetoidObject
       (@hom (MSet@{so so o o o o o o} M) (fobj[MSet_Free@{o so} M] X) A)
       (@homset (MSet@{so so o o o o o o} M) (fobj[MSet_Free@{o so} M] X) A))
    (@Build_SetoidObject
       (@hom Sets@{o so} X (fobj[MSet_Forget@{o so} M] A))
       (@homset Sets@{o so} X (fobj[MSet_Forget@{o so} M] A))).
Proof.
  unshelve refine
    (@Build_Isomorphism Sets@{o so}
       (@Build_SetoidObject
          (@hom (MSet@{so so o o o o o o} M) (fobj[MSet_Free@{o so} M] X) A)
          (@homset (MSet@{so so o o o o o o} M)
             (fobj[MSet_Free@{o so} M] X) A))
       (@Build_SetoidObject
          (@hom Sets@{o so} X (fobj[MSet_Forget@{o so} M] A))
          (@homset Sets@{o so} X (fobj[MSet_Forget@{o so} M] A)))
       (@Build_SetoidMorphism
          (@hom (MSet@{so so o o o o o o} M) (fobj[MSet_Free@{o so} M] X) A)
          (@homset (MSet@{so so o o o o o o} M)
             (fobj[MSet_Free@{o so} M] X) A)
          (@hom Sets@{o so} X (fobj[MSet_Forget@{o so} M] A))
          (@homset Sets@{o so} X (fobj[MSet_Forget@{o so} M] A))
          (fun φ => @MSet_restrict M X A φ) _)
       (@Build_SetoidMorphism
          (@hom Sets@{o so} X (fobj[MSet_Forget@{o so} M] A))
          (@homset Sets@{o so} X (fobj[MSet_Forget@{o so} M] A))
          (@hom (MSet@{so so o o o o o o} M) (fobj[MSet_Free@{o so} M] X) A)
          (@homset (MSet@{so so o o o o o o} M)
             (fobj[MSet_Free@{o so} M] X) A)
          (fun ψ => @MSet_extend M X A ψ) _) _ _).
  - intros φ φ' Hφ x. exact (Hφ (mon_unit, x)).
  - intros ψ ψ' Hψ [g x]; simpl.
    apply act_respects; [ reflexivity | exact (Hψ x) ].
  - intros ψ x; simpl. apply act_unit.
  - intros φ [g x]; simpl.
    transitivity (equiv_map φ (act (@FreeAct M X) g (mon_unit, x))).
    + symmetry. exact (equivar φ g (mon_unit, x)).
    + apply (proper_morphism (equiv_map φ)).
      split; [ exact (mon_op_unit_r g) | reflexivity ].
Defined.

(* Riehl's left adjoint X ↦ G × X, over any monoid. / Riehl 的左伴随 X ↦ G × X，对于任意幺半群。 *)
Definition MSet_adj@{o so} (M : MonObject@{o o o}) :
  @Adjunction@{so o o so o o o o so o so} (MSet@{so so o o o o o o} M)
    Sets@{o so} (MSet_Free@{o so} M) (MSet_Forget@{o so} M).
Proof.
  unshelve refine
    (@Build_Adjunction' (MSet@{so so o o o o o o} M) Sets@{o so}
       (MSet_Free@{o so} M) (MSet_Forget@{o so} M)
       (fun X A => MSet_adj_iso M X A) _ _).
  - intros X Y A f g x; simpl. reflexivity.
  - intros X A B f g x; simpl. reflexivity.
Defined.

(** ** Mac Lane's monad G × (−) / ** 麦克莱恩的单子 G × (−) *)

Definition ActF@{o so} (M : MonObject@{o o o}) :
  Sets@{o so} ⟶ Sets@{o so} :=
  MSet_Forget@{o so} M ◯ MSet_Free@{o so} M.

Definition ActMonad@{o so} (M : MonObject@{o o o}) :
  @Monad Sets@{o so} (ActF@{o so} M) :=
  Adjunction_Induced_Monad (MSet_adj@{o so} M).

(* Mac Lane's formulas, read back on the nose: T X = G × X, η x = (u, x) and μ (g₁, (g₂, x)) = (g₁ g₂, x). / 麦克·莱恩的公式，按字面朗读：T X = G × X, η x = (u, x) 和 μ (g₁, (g₂, x)) = (g₁ g₂, x)。 *)
Example ActF_obj@{o so} (M : MonObject@{o o o}) (X : SetoidObject@{o o}) :
  fobj[ActF@{o so} M] X = act_prod M X := eq_refl.

Example ActF_map@{o so} (M : MonObject@{o o o}) (X Y : SetoidObject@{o o})
  (f : X ~{Sets@{o so}}~> Y) :
  fmap[ActF@{o so} M] f = act_prod_map M f := eq_refl.

Example ActMonad_ret@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) (x : carrier X) :
  (@ret _ _ (ActMonad@{o so} M) X) x = (mon_unit, x) := eq_refl.

Example ActMonad_join@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) (g1 g2 : carrier M) (x : carrier X) :
  (@join _ _ (ActMonad@{o so} M) X) (g1, (g2, x)) = (mon_op g1 g2, x) :=
  eq_refl.

(* The point and the triple above are Mac Lane's notation. η holds as a function too, and so does μ, which is stronger than the triple, since Coq's [prod] has no eta. / 上面的点和三重数是麦克莱恩的记号。η 也作为一个函数成立，μ 也是如此，它比三重数更强，因为 Coq 的 [prod] 没有 η。 *)
Example ActMonad_ret_fun@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) :
  (fun x : carrier X => (@ret _ _ (ActMonad@{o so} M) X) x)
  = (fun x => (mon_unit, x)) := eq_refl.

Example ActMonad_join_fun@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) :
  (fun p => (@join _ _ (ActMonad@{o so} M) X) p)
  = (fun p : carrier M * (carrier M * carrier X) =>
       (mon_op (fst p) (fst (snd p)), snd (snd p))) := eq_refl.

(** ** Algebras are actions / ** 代数是作用 *)

(* Mac Lane: a T-algebra h : G × X → X is an action, g · x := h (g, x). / Mac Lane：一个 T-代数 h : G × X → X 是一个作用，g · x := h (g, x)。 *)
Definition EM_act@{o so} {M : MonObject@{o o o}}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) :
  MSetoidAction@{o o o o o o o o} M.
Proof.
  unshelve refine
    (@Build_MSetoidAction M (`1 x) (fun g a => t_alg[`2 x] (g, a)) _ _ _).
  - intros g g' Hg a a' Ha.
    apply (proper_morphism (t_alg[`2 x])). split; assumption.
  - intros a. exact (@t_id _ _ _ _ (`2 x) a).
  - intros g h a. symmetry. exact (@t_action _ _ _ _ (`2 x) (g, (h, a))).
Defined.

Definition EM_to_MSet@{o so} (M : MonObject@{o o o}) :
  @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M) (ActMonad@{o so} M)
    ⟶ MSet@{so so o o o o o o} M.
Proof.
  unshelve refine
    (@Build_Functor
       (@EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
          (ActMonad@{o so} M))
       (MSet@{so so o o o o o o} M)
       (fun x => @EM_act M x)
       (fun x y f => @Build_Equivariant M (@EM_act M x) (@EM_act M y)
                       t_alg_hom[f]
                       (fun g a => @t_alg_hom_commutes _ _ _ _ _ _ _ f (g, a)))
       _ _ _).
  - intros x y f f' Hf a. exact (Hf a).
  - intros x a. reflexivity.
  - intros x y z f g a. reflexivity.
Defined.

Definition MSet_counit_iso@{o so} {M : MonObject@{o o o}}
  (B : MSetoidAction@{o o o o o o o o} M) :
  @Isomorphism (MSet@{so so o o o o o o} M)
    (fobj[EM_to_MSet@{o so} M ◯ EM_Comparison (MSet_adj@{o so} M)] B) B.
Proof.
  unshelve refine
    (@Build_Isomorphism (MSet@{so so o o o o o o} M) _ _
       (@Build_Equivariant M
          (fobj[EM_to_MSet@{o so} M ◯ EM_Comparison (MSet_adj@{o so} M)] B) B
          (@setoid_morphism_id (act_setoid B)) _)
       (@Build_Equivariant M B
          (fobj[EM_to_MSet@{o so} M ◯ EM_Comparison (MSet_adj@{o so} M)] B)
          (@setoid_morphism_id (act_setoid B)) _) _ _).
  - intros g a. reflexivity.
  - intros g a. reflexivity.
  - intros a. reflexivity.
  - intros a. reflexivity.
Defined.

Definition MSet_unit_iso@{o so} {M : MonObject@{o o o}}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) :
  @Isomorphism
    (@EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
       (ActMonad@{o so} M))
    (fobj[EM_Comparison (MSet_adj@{o so} M) ◯ EM_to_MSet@{o so} M] x) x.
Proof.
  destruct x as [X α].
  unshelve refine
    (@Build_Isomorphism
       (@EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
          (ActMonad@{o so} M))
       (fobj[EM_Comparison (MSet_adj@{o so} M) ◯ EM_to_MSet@{o so} M] (X; α))
       (X; α)
       (@Build_TAlgebraHom Sets@{o so} (ActF@{o so} M) (ActMonad@{o so} M) X X
          (`2 (fobj[EM_Comparison (MSet_adj@{o so} M)
                    ◯ EM_to_MSet@{o so} M] (X; α))) α
          (@setoid_morphism_id X) _)
       (@Build_TAlgebraHom Sets@{o so} (ActF@{o so} M) (ActMonad@{o so} M) X X
          α (`2 (fobj[EM_Comparison (MSet_adj@{o so} M)
                      ◯ EM_to_MSet@{o so} M] (X; α)))
          (@setoid_morphism_id X) _) _ _).
  - intros [g a]. reflexivity.
  - intros [g a]. reflexivity.
  - intros a. reflexivity.
  - intros a. reflexivity.
Defined.

(*
 The direct route: [EM_to_MSet] is a quasi-inverse of the comparison
 functor, with identity components both ways. 

 --------
 直接路线：[EM_to_MSet] 是比较函子的一种准逆，其两边的组成都是恒等的。
*)
Definition MSet_comparison_equivalence@{o so} (M : MonObject@{o o o}) :
  EquivalenceOfCategories (EM_Comparison (MSet_adj@{o so} M)).
Proof.
  unshelve refine
    (@Build_EquivalenceOfCategories _ _ (EM_Comparison (MSet_adj@{o so} M))
       (EM_to_MSet@{o so} M) _ _).
  - exists (fun x => MSet_unit_iso x).
    intros [X α] [Y β] f a; simpl. reflexivity.
  - exists (fun B => iso_sym (MSet_counit_iso B)).
    intros B C h a; simpl. reflexivity.
Defined.

Definition MSet_Forget_Monadic_direct@{o so} (M : MonObject@{o o o}) :
  @Monadic@{so so so so so o so so} (MSet@{so so o o o o o o} M) Sets@{o so}
    (MSet_Forget@{o so} M).
Proof.
  exists (MSet_Free@{o so} M).
  exists (MSet_adj@{o so} M).
  exact (MSet_comparison_equivalence@{o so} M).
Defined.

(*
 G-sets ARE the algebras: an isomorphism in Cat whose [to] leg is the
 comparison functor itself. 

 --------
 G-集就是代数：在Cat中的一个同构，其[to]部分是比较函子本身。
*)
Definition EM_MSet_iso@{o so c} (M : MonObject@{o o o}) :
  @Isomorphism Cat@{c so so so o}
    (MSet@{so so o o o o o o} M)
    (@EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
       (ActMonad@{o so} M)) :=
  Equivalence_to_Cat_Iso (MSet_comparison_equivalence@{o so} M).

Example EM_MSet_iso_to@{o so c} (M : MonObject@{o o o}) :
  to (EM_MSet_iso@{o so c} M) = EM_Comparison (MSet_adj@{o so} M) := eq_refl.

(* Its [from] leg is the direct quasi-inverse itself. / 它的 [from] 腿本身就是直接准逆。 *)
Example EM_MSet_iso_from@{o so c} (M : MonObject@{o o o}) :
  from (EM_MSet_iso@{o so c} M) = EM_to_MSet@{o so} M := eq_refl.

Example EM_act_is_action@{o so} {M : MonObject@{o o o}}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) (g : carrier M) (a : carrier (`1 x)) :
  act (EM_act@{o so} x) g a = t_alg[`2 x] (g, a) := eq_refl.

Example comparison_alg_is_action@{o so} {M : MonObject@{o o o}}
  (A : MSetoidAction@{o o o o o o o o} M) (g : carrier M)
  (a : carrier (act_setoid A)) :
  t_alg[`2 (fobj[EM_Comparison (MSet_adj@{o so} M)] A)] (g, a) = act A g a :=
  eq_refl.

(* The same, as a function of the pair. / 相同，作为该对的函数。 *)
Example comparison_alg_fun@{o so} {M : MonObject@{o o o}}
  (A : MSetoidAction@{o o o o o o o o} M) :
  (fun p => t_alg[`2 (fobj[EM_Comparison (MSet_adj@{o so} M)] A)] p)
  = (fun p : carrier M * carrier (act_setoid A) => act A (fst p) (snd p)) :=
  eq_refl.

(* * ** Riehl's route: the forgetful functor creates U-split coequalizers / * ** Riehl 的路径：遗忘函子产生 U-可分的余等化器 *)

(* Absorption through a split coequalizer: a map h out of B that coforks the pair satisfies h (s (e y)) ≈ h y. / 通过分裂余等化子的吸收：从 B 出发的映射 h 协同分叉该对，满足 h (s (e y)) ≈ h y。 *)
Lemma split_absorb@{o so} {M : MonObject@{o o o}}
  {A B : MSetoidAction@{o o o o o o o o} M}
  (p q : A ~{MSet@{so so o o o o o o} M}~> B)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[MSet_Forget@{o so} M] p) (fmap[MSet_Forget@{o so} M] q))
  {W : SetoidObject@{o o}} (h : act_setoid B ~{Sets@{o so}}~> W)
  (Hh : ∀ x, h (equiv_map p x) ≈ h (equiv_map q x))
  (y : carrier (act_setoid B)) :
  h (scoeq_s S (scoeq_e S y)) ≈ h y.
Proof.
  pose proof (scoeq_law4 S y) as L4; simpl in L4.
  pose proof (scoeq_law3 S y) as L3; simpl in L3.
  transitivity (h (equiv_map q (scoeq_t S y))).
  - apply (proper_morphism h). symmetry. exact L4.
  - transitivity (h (equiv_map p (scoeq_t S y))).
    + symmetry. apply Hh.
    + apply (proper_morphism h). exact L3.
Qed.

(* The created action on the split quotient Z: g · z := e (g · s z). / 在分裂商 Z 上创建的作用：g · z := e (g · s z)。 *)
Definition created_act@{o so} {M : MonObject@{o o o}}
  {A B : MSetoidAction@{o o o o o o o o} M}
  (p q : A ~{MSet@{so so o o o o o o} M}~> B)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[MSet_Forget@{o so} M] p) (fmap[MSet_Forget@{o so} M] q)) :
  carrier M → carrier (scoeq_obj S) → carrier (scoeq_obj S) :=
  fun g z => scoeq_e S (act B g (scoeq_s S z)).

(* e ∘ (g · −) coforks the pair, so it absorbs s ∘ e. / e ∘ (g · −) 协同余并对该对，因此它吸收 s ∘ e。 *)
Lemma created_absorb@{o so} {M : MonObject@{o o o}}
  {A B : MSetoidAction@{o o o o o o o o} M}
  (p q : A ~{MSet@{so so o o o o o o} M}~> B)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[MSet_Forget@{o so} M] p) (fmap[MSet_Forget@{o so} M] q))
  (g : carrier M) (y : carrier (act_setoid B)) :
  scoeq_e S (act B g (scoeq_s S (scoeq_e S y))) ≈ scoeq_e S (act B g y).
Proof.
  pose proof (scoeq_law4 S y) as L4; simpl in L4.
  pose proof (scoeq_law3 S y) as L3; simpl in L3.
  pose proof (scoeq_law1 S (act A g (scoeq_t S y))) as L1; simpl in L1.
  transitivity (scoeq_e S (act B g (equiv_map q (scoeq_t S y)))).
  - apply (proper_morphism (scoeq_e S)).
    apply act_respects; [ reflexivity | symmetry; exact L4 ].
  - transitivity (scoeq_e S (equiv_map q (act A g (scoeq_t S y)))).
    + apply (proper_morphism (scoeq_e S)). symmetry. apply equivar.
    + transitivity (scoeq_e S (equiv_map p (act A g (scoeq_t S y)))).
      * symmetry. exact L1.
      * transitivity (scoeq_e S (act B g (equiv_map p (scoeq_t S y)))).
        -- apply (proper_morphism (scoeq_e S)). apply equivar.
        -- apply (proper_morphism (scoeq_e S)).
           apply act_respects; [ reflexivity | exact L3 ].
Qed.

Definition CreatedAct@{o so} {M : MonObject@{o o o}}
  {A B : MSetoidAction@{o o o o o o o o} M}
  (p q : A ~{MSet@{so so o o o o o o} M}~> B)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[MSet_Forget@{o so} M] p) (fmap[MSet_Forget@{o so} M] q)) :
  MSetoidAction@{o o o o o o o o} M.
Proof.
  unshelve refine
    (@Build_MSetoidAction M (scoeq_obj S) (created_act@{o so} p q S) _ _ _).
  - intros g g' Hg z z' Hz. unfold created_act.
    apply (proper_morphism (scoeq_e S)).
    apply act_respects;
      [ exact Hg | apply (proper_morphism (scoeq_s S)); exact Hz ].
  - intros z. unfold created_act.
    pose proof (scoeq_law2 S z) as L2; simpl in L2.
    transitivity (scoeq_e S (scoeq_s S z)); [ | exact L2 ].
    apply (proper_morphism (scoeq_e S)). apply act_unit.
  - intros g h z. unfold created_act.
    transitivity (scoeq_e S (act B g (act B h (scoeq_s S z)))).
    + apply (proper_morphism (scoeq_e S)). apply act_op.
    + symmetry. apply created_absorb.
Defined.

Definition CreatedE@{o so} {M : MonObject@{o o o}}
  {A B : MSetoidAction@{o o o o o o o o} M}
  (p q : A ~{MSet@{so so o o o o o o} M}~> B)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[MSet_Forget@{o so} M] p) (fmap[MSet_Forget@{o so} M] q)) :
  B ~{MSet@{so so o o o o o o} M}~> CreatedAct@{o so} p q S.
Proof.
  unshelve refine
    (@Build_Equivariant M B (CreatedAct@{o so} p q S) (scoeq_e S) _).
  intros g y. simpl. unfold created_act. symmetry. apply created_absorb.
Defined.

Definition CreatedE_is_coeq@{o so} {M : MonObject@{o o o}}
  {A B : MSetoidAction@{o o o o o o o o} M}
  (p q : A ~{MSet@{so so o o o o o o} M}~> B)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[MSet_Forget@{o so} M] p) (fmap[MSet_Forget@{o so} M] q)) :
  @IsCoequalizer (MSet@{so so o o o o o o} M) A B p q
    (CreatedAct@{o so} p q S) (CreatedE@{o so} p q S).
Proof.
  unshelve refine (@Build_IsCoequalizer _ _ _ _ _ _ _ _ _).
  - intros x. exact (scoeq_law1 S x).
  - intros W h Hh.
    unshelve eapply Build_Unique.
    + unshelve refine
        (@Build_Equivariant M (CreatedAct@{o so} p q S) W
           (@setoid_morphism_compose _ _ _ (equiv_map h) (scoeq_s S)) _).
      intros g z; simpl. unfold created_act.
      transitivity (equiv_map h (act B g (scoeq_s S z))).
      * apply (split_absorb p q S (equiv_map h) Hh).
      * apply equivar.
    + intros y; simpl. apply (split_absorb p q S (equiv_map h) Hh).
    + intros v Hv z; simpl.
      pose proof (scoeq_law2 S z) as L2; simpl in L2.
      transitivity (equiv_map v (scoeq_e S (scoeq_s S z))).
      * symmetry. exact (Hv (scoeq_s S z)).
      * apply (proper_morphism (equiv_map v)). exact L2.
Defined.

(*
 The reflection clause: a cofork lying over the splitting up to a
 compatible isomorphism downstairs is a coequalizer upstairs. 

 --------
 反射条款：位于分裂上方的联合叉映射到下方的兼容同构是上方的共同化器。
*)
Definition Reflected_is_coeq@{o so} {M : MonObject@{o o o}}
  {A B : MSetoidAction@{o o o o o o o o} M}
  (p q : A ~{MSet@{so so o o o o o o} M}~> B)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[MSet_Forget@{o so} M] p) (fmap[MSet_Forget@{o so} M] q))
  (Q : MSetoidAction@{o o o o o o o o} M)
  (e : B ~{MSet@{so so o o o o o o} M}~> Q)
  (He : e ∘ p ≈ e ∘ q)
  (i : @Isomorphism Sets@{o so} (fobj[MSet_Forget@{o so} M] Q) (scoeq_obj S))
  (Hi : to i ∘ fmap[MSet_Forget@{o so} M] e ≈ scoeq_e S) :
  @IsCoequalizer (MSet@{so so o o o o o o} M) A B p q Q e.
Proof.
  (* w ≈ e (s (i w)) *)
  assert (L0 : ∀ w, w ≈ equiv_map e (scoeq_s S (to i w))).
  { intros w.
    pose proof (Hi (scoeq_s S (to i w))) as H1; simpl in H1.
    pose proof (scoeq_law2 S (to i w)) as L2; simpl in L2.
    pose proof (iso_from_to i w) as FT; simpl in FT.
    pose proof (iso_from_to i (equiv_map e (scoeq_s S (to i w)))) as FT';
      simpl in FT'.
    transitivity (from i (to i w)); [ symmetry; exact FT | ].
    transitivity (from i (to i (equiv_map e (scoeq_s S (to i w)))));
      [ | exact FT' ].
    apply (proper_morphism (from i)).
    symmetry.
    transitivity (scoeq_e S (scoeq_s S (to i w))); [ exact H1 | exact L2 ]. }
  unshelve refine (@Build_IsCoequalizer _ _ _ _ _ _ _ _ _).
  - exact He.
  - intros W h Hh.
    unshelve eapply Build_Unique.
    + unshelve refine
        (@Build_Equivariant M Q W
           (@setoid_morphism_compose _ _ _
              (@setoid_morphism_compose _ _ _ (equiv_map h) (scoeq_s S))
              (to i)) _).
      intros g w; simpl.
      transitivity
        (equiv_map h (scoeq_s S (to i (act Q g
           (equiv_map e (scoeq_s S (to i w))))))).
      * apply (proper_morphism (equiv_map h)).
        apply (proper_morphism (scoeq_s S)).
        apply (proper_morphism (to i)).
        apply act_respects; [ reflexivity | exact (L0 w) ].
      * transitivity
          (equiv_map h (scoeq_s S (to i (equiv_map e
             (act B g (scoeq_s S (to i w))))))).
        -- apply (proper_morphism (equiv_map h)).
           apply (proper_morphism (scoeq_s S)).
           apply (proper_morphism (to i)). symmetry. apply equivar.
        -- transitivity
             (equiv_map h (scoeq_s S (scoeq_e S
                (act B g (scoeq_s S (to i w)))))).
           ++ apply (proper_morphism (equiv_map h)).
              apply (proper_morphism (scoeq_s S)).
              exact (Hi _).
           ++ transitivity (equiv_map h (act B g (scoeq_s S (to i w)))).
              ** apply (split_absorb p q S (equiv_map h) Hh).
              ** apply equivar.
    + intros y; simpl.
      transitivity (equiv_map h (scoeq_s S (scoeq_e S y))).
      * apply (proper_morphism (equiv_map h)).
        apply (proper_morphism (scoeq_s S)).
        exact (Hi y).
      * apply (split_absorb p q S (equiv_map h) Hh).
    + intros v Hv w; simpl.
      transitivity (equiv_map v (equiv_map e (scoeq_s S (to i w)))).
      * symmetry. exact (Hv (scoeq_s S (to i w))).
      * apply (proper_morphism (equiv_map v)). symmetry. exact (L0 w).
Defined.

Definition MSet_Forget_creates@{o so} (M : MonObject@{o o o}) :
  CreatesUSplitCoequalizers (MSet_Forget@{o so} M).
Proof.
  unshelve refine (@Build_CreatesUSplitCoequalizers _ _ _ _ _).
  - intros A B p q S.
    exists (CreatedAct@{o so} p q S).
    exists (CreatedE@{o so} p q S).
    split.
    + exact (CreatedE_is_coeq@{o so} p q S).
    + exists (@iso_id Sets@{o so} (scoeq_obj S)).
      intros y; simpl. reflexivity.
  - intros A B p q S Q e He i Hi.
    exact (Reflected_is_coeq@{o so} p q S Q e He i Hi).
Defined.

(*
 The lift chosen is on the nose: the created M-set has carrier Z and
 action g · z = e (g · s z), its coequalizing arrow is e, and the
 comparison isomorphism is the identity. 

 --------
 选择的提升在于鼻子：所创建的 M-集的载体是 Z，作用为 g · z = e (g · s z)，它的共等化箭头是 e，并且比较同构是恒等映射。
*)
Example mset_created_carrier@{o so} {M : MonObject@{o o o}}
  {A B : MSetoidAction@{o o o o o o o o} M}
  (p q : A ~{MSet@{so so o o o o o o} M}~> B)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[MSet_Forget@{o so} M] p) (fmap[MSet_Forget@{o so} M] q)) :
  act_setoid
    (`1 (@create_coeq _ _ _ (MSet_Forget_creates@{o so} M) A B p q S))
  = scoeq_obj S := eq_refl.

Example mset_created_action@{o so} {M : MonObject@{o o o}}
  {A B : MSetoidAction@{o o o o o o o o} M}
  (p q : A ~{MSet@{so so o o o o o o} M}~> B)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[MSet_Forget@{o so} M] p) (fmap[MSet_Forget@{o so} M] q))
  (g : carrier M) (z : carrier (scoeq_obj S)) :
  act (`1 (@create_coeq _ _ _ (MSet_Forget_creates@{o so} M) A B p q S)) g z
  = scoeq_e S (act B g (scoeq_s S z)) := eq_refl.

Example mset_created_arrow@{o so} {M : MonObject@{o o o}}
  {A B : MSetoidAction@{o o o o o o o o} M}
  (p q : A ~{MSet@{so so o o o o o o} M}~> B)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[MSet_Forget@{o so} M] p) (fmap[MSet_Forget@{o so} M] q)) :
  equiv_map
    (`1 (`2 (@create_coeq _ _ _ (MSet_Forget_creates@{o so} M) A B p q S)))
  = scoeq_e S := eq_refl.

Example mset_created_iso@{o so} {M : MonObject@{o o o}}
  {A B : MSetoidAction@{o o o o o o o o} M}
  (p q : A ~{MSet@{so so o o o o o o} M}~> B)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[MSet_Forget@{o so} M] p) (fmap[MSet_Forget@{o so} M] q)) :
  `1 (snd (`2 (`2 (@create_coeq _ _ _ (MSet_Forget_creates@{o so} M)
                     A B p q S))))
  = @iso_id Sets@{o so} (scoeq_obj S) := eq_refl.

(* * ** Riehl's Exercise 5.5.iv by the monadicity theorem / * ** 赖尔的练习 5.5.iv 根据幺半群定理 *)

Definition MSet_beck_equivalence@{o so} (M : MonObject@{o o o}) :
  EquivalenceOfCategories (EM_Comparison (MSet_adj@{o so} M)) :=
  beck_monadicity (MSet_adj@{o so} M) (MSet_Forget_creates@{o so} M).

Definition MSet_Forget_Monadic@{o so} (M : MonObject@{o o o}) :
  @Monadic@{so so so so so o so so} (MSet@{so so o o o o o o} M) Sets@{o so}
    (MSet_Forget@{o so} M).
Proof.
  exists (MSet_Free@{o so} M).
  exists (MSet_adj@{o so} M).
  exact (MSet_beck_equivalence@{o so} M).
Defined.

(* A bijective equivariant map is an isomorphism of M-sets. / 一个双射等变映射是 M-集的同构。 *)
Definition MSet_Forget_reflects@{o so} (M : MonObject@{o o o}) :
  ReflectsIsos (MSet_Forget@{o so} M) :=
  creates_split_reflects_isos _ (MSet_Forget_creates@{o so} M).

(* * ** The two routes are equivalences of the same functor / * ** 这两条路径是同一个函子等价的 *)

Definition EM_MSet_iso_beck@{o so c} (M : MonObject@{o o o}) :
  @Isomorphism Cat@{c so so so o}
    (MSet@{so so o o o o o o} M)
    (@EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
       (ActMonad@{o so} M)) :=
  Equivalence_to_Cat_Iso (MSet_beck_equivalence@{o so} M).

Example EM_MSet_iso_beck_to@{o so c} (M : MonObject@{o o o}) :
  to (EM_MSet_iso_beck@{o so c} M) = EM_Comparison (MSet_adj@{o so} M) :=
  eq_refl.

Example beck_direct_to@{o so c} (M : MonObject@{o o o}) :
  to (EM_MSet_iso_beck@{o so c} M) = to (EM_MSet_iso@{o so c} M) := eq_refl.

(* Beck's quasi-inverse keeps the carrier and acts through η: its action at g is the structure map at (g u, z). / 贝克的拟逆保持承载体，并通过 η 起作用：它在 g 处的作用是 (g u, z) 处的结构映射。 *)
Example beck_carrier@{o so} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) :
  act_setoid (fobj[@quasi_inverse _ _ _ (MSet_beck_equivalence@{o so} M)] x)
  = `1 x := eq_refl.

Example beck_act@{o so} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) (g : carrier M) (z : carrier (`1 x)) :
  act (fobj[@quasi_inverse _ _ _ (MSet_beck_equivalence@{o so} M)] x) g z
  = t_alg[`2 x] (mon_op g mon_unit, z) := eq_refl.

Definition beck_vs_direct_iso@{o so} {M : MonObject@{o o o}}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) :
  @Isomorphism (MSet@{so so o o o o o o} M)
    (fobj[@quasi_inverse _ _ _ (MSet_beck_equivalence@{o so} M)] x)
    (fobj[EM_to_MSet@{o so} M] x).
Proof.
  unshelve refine
    (@Build_Isomorphism (MSet@{so so o o o o o o} M) _ _
       (@Build_Equivariant M
          (fobj[@quasi_inverse _ _ _ (MSet_beck_equivalence@{o so} M)] x)
          (fobj[EM_to_MSet@{o so} M] x) (@setoid_morphism_id (`1 x)) _)
       (@Build_Equivariant M (fobj[EM_to_MSet@{o so} M] x)
          (fobj[@quasi_inverse _ _ _ (MSet_beck_equivalence@{o so} M)] x)
          (@setoid_morphism_id (`1 x)) _) _ _).
  - intros g z; simpl. apply (proper_morphism (t_alg[`2 x])).
    split; [ exact (mon_op_unit_r g) | reflexivity ].
  - intros g z; simpl. apply (proper_morphism (t_alg[`2 x])).
    split; [ symmetry; exact (mon_op_unit_r g) | reflexivity ].
  - intros z. reflexivity.
  - intros z. reflexivity.
Defined.

Definition beck_vs_direct@{o so} (M : MonObject@{o o o}) :
  @quasi_inverse _ _ _ (MSet_beck_equivalence@{o so} M) ≈ EM_to_MSet@{o so} M.
Proof.
  exists (fun x => beck_vs_direct_iso x).
  intros x y f z; simpl.
  exact (@t_id _ _ _ _ (`2 y) (t_alg_hom[f] z)).
Defined.

(** ** Riehl's Set^{BG} / ** Riehl 的集合^{BG} *)

(*
 Instance/Fun/Action.v's [MSet_Fun_equiv] followed by [EM_MSet_iso]:
 the functor category [Deloop M, Sets] is isomorphic in Cat to the
 Eilenberg–Moore category of G × (−). 

 --------
 Instance/Fun/Action.v 的 [MSet_Fun_equiv] 后跟 [EM_MSet_iso]：
 函子范畴 [Deloop M, Sets] 在 Cat 中同构于 G × (−) 的 Eilenberg–Moore 范畴。
*)
Definition Fun_EM_iso@{o so c} (M : MonObject@{o o o}) :
  @Isomorphism Cat@{c so so so o}
    ([Deloop@{o o} M, Sets@{o so}])
    (@EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
       (ActMonad@{o so} M)) :=
  @iso_compose@{c so so c} Cat@{c so so so o} _ _ _
    (EM_MSet_iso@{o so c} M) (MSet_Fun_equiv@{so c o} M).

(** ** Groups *)

(* A group of Construction/Deloop.v reaches [MonObject] by coercion. / 一群 Construction/Deloop.v 通过强制手段到达 [MonObject]。 *)
Definition GAct_Monad@{o so}
  (G : Category.Construction.Deloop.GrpObject@{o o o}) :
  @Monad Sets@{o so} (ActF@{o so} G) := ActMonad@{o so} G.

Definition GSet_Forget_Monadic@{o so}
  (G : Category.Construction.Deloop.GrpObject@{o o o}) :
  @Monadic@{so so so so so o so so} (MSet@{so so o o o o o o} G) Sets@{o so}
    (MSet_Forget@{o so} G) :=
  MSet_Forget_Monadic@{o so} G.

(*
 A group of Instance/Grp.v reaches it through Instance/Grp/Free.v's
 [grp_deloop_monoid]. 

 --------
 一组 Instance/Grp.v 通过 Instance/Grp/Free.v 的 [grp_deloop_monoid] 达到它。
*)
Definition GAct_Monad_Grp@{o so}
  (G : Category.Instance.Grp.GrpObject@{o o o}) :
  @Monad Sets@{o so} (ActF@{o so} (grp_deloop_monoid@{o o o} G)) :=
  ActMonad@{o so} (grp_deloop_monoid@{o o o} G).

Definition GSet_Forget_Monadic_Grp@{o so}
  (G : Category.Instance.Grp.GrpObject@{o o o}) :
  @Monadic@{so so so so so o so so}
    (MSet@{so so o o o o o o} (grp_deloop_monoid@{o o o} G)) Sets@{o so}
    (MSet_Forget@{o so} (grp_deloop_monoid@{o o o} G)) :=
  MSet_Forget_Monadic@{o so} (grp_deloop_monoid@{o o o} G).

(*
 A group of Structure/Group.v, internal to (Sets, ×), reaches it
 through Instance/Grp.v's [GroupObject_GrpObject], which asks that the
 carrier's ≈ be a proposition. 

 --------
 一个内部于 (Sets, ×) 的 Structure/Group.v 组，通过 Instance/Grp.v 的 [GroupObject_GrpObject] 达到它，该 [GroupObject_GrpObject] 要求载体的 ≈ 是一个命题。
*)
Definition GAct_Monad_GroupObject@{o so} (X : Sets@{o so})
  (PX : PropEquiv@{o o} X)
  (GO : @GroupObject@{so o so} Sets@{o so} Sets_CartesianMonoidal X) :
  @Monad Sets@{o so}
    (ActF@{o so} (grp_deloop_monoid@{o o o} (GroupObject_GrpObject X PX GO))) :=
  ActMonad@{o so} (grp_deloop_monoid@{o o o} (GroupObject_GrpObject X PX GO)).

Definition GSet_Forget_Monadic_GroupObject@{o so} (X : Sets@{o so})
  (PX : PropEquiv@{o o} X)
  (GO : @GroupObject@{so o so} Sets@{o so} Sets_CartesianMonoidal X) :
  @Monadic@{so so so so so o so so}
    (MSet@{so so o o o o o o}
       (grp_deloop_monoid@{o o o} (GroupObject_GrpObject X PX GO)))
    Sets@{o so}
    (MSet_Forget@{o so}
       (grp_deloop_monoid@{o o o} (GroupObject_GrpObject X PX GO))) :=
  MSet_Forget_Monadic@{o so}
    (grp_deloop_monoid@{o o o} (GroupObject_GrpObject X PX GO)).
