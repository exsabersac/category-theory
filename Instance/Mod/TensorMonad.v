(* * * The monad R ⊗ (−) on Ab and its algebras, the left R-modules / * * Ab 上的幺半 R ⊗ (−) 及其代数，即左 R-模 *)

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
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Tensor.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.BaseChange.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(*
 Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 Springer GTM 5, 1998, §VI.2, “Modules”, printed p. 142 (PDF
 p. 151) — maclane:VI.2:remark3; with §VI.3, printed
 pp. 142–143
 Book: Riehl, “Category Theory in Context”, 2nd ed., Example
 5.2.6(ii), printed p. 189 (PDF p. 209) — riehl:5.2:example6;
 Example 5.5.7(i), printed p. 205 (PDF p. 225) —
 riehl:5.5:example7; with her Example 4.1.10(xiii), printed
 p. 136, Definition 5.3.1, printed p. 196, and Theorem 5.5.1,
 printed p. 202
 nLab: https://ncatlab.org/nlab/show/module
 nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad
 nLab: https://ncatlab.org/nlab/show/monadicity+theorem

 Mac Lane closes §VI.2 (from printed p. 141) with “several examples
 which show that the T-algebras for familiar monads are the familiar
 algebras”.  After the closure operators and the group actions comes
 the module: “If R is a (small) ring, then for each (small) abelian
 group A the definitions TA = R⊗A, A → R⊗A, R⊗(R⊗A) → R⊗A, a ↦ 1⊗a,
 r₁⊗(r₂⊗a) ↦ r₁r₂⊗a, for a ∈ A, r₁, r₂ ∈ R, define a monad on Ab.
 Much as in the previous case, the T-algebras are exactly the left
 R-modules.”  The previous case is the group action of
 Instance/Fun/Action/Monad.v, and this file follows its pattern.
 Riehl's Example 5.2.6(ii) takes the adjunction of her Example
 4.1.10(xiii), whose forgetful functor U : _R Mod → Ab is “a special
 case of the previous example”, restriction of scalars, along the ring
 map ℤ → R, and derives from it “a monad R ⊗_ℤ − on Ab”.  An algebra's
 homomorphism R ⊗_ℤ A → A “encodes a ℤ-bilinear map (r, a) ↦ r·a”, its
 two diagrams “ensure 1·a = a and r·(r′·a) = (rr′)·a”, and so “an
 algebra for the monad R ⊗_ℤ − on Ab is precisely an R-module”.  Her
 Example 5.5.7(i) concludes: “the forgetful functor U : _R Mod → Ab is
 monadic.  The induced monad on Ab is given by R ⊗_ℤ − : Ab → Ab.”
 This file proves all of it, and the monadicity twice: by an explicit
 quasi-inverse, which is her own route in Example 5.5.7(i), and by
 Beck's theorem, her Theorem 5.5.1.

 NOTHING IS REBUILT.  The categories are Instance/Ab.v's [Ab] and
 Instance/Mod.v's [RMod R] of left modules over a [RingObject]; the
 tensor is Instance/Ab/Tensor.v's [AbTensor], the ℤ-tensor of two
 abelian groups as a term model of formal sums; the adjunction is
 Instance/Mod/BaseChange.v's
 [zext_adjunction R : ZExt R ⊣ RMod_Forget_Ab R], whose [ZExt R] sends
 A to R ⊗ A acted on by r · (s ⊗ a) = (r s) ⊗ a.  The tree has no
 equivalence between [Ab] and [RMod Int_Ring] (BaseChange.v's header
 records it), so [ZExt R] is Riehl's extension of scalars written
 directly out of [Ab].  Nothing here or there asks R to be commutative:
 Mac Lane's R is a ring and his algebras are LEFT modules.

 THE MONAD IS THE MONAD OF THE ADJUNCTION.  [TensorF R] is the composite
 [RMod_Forget_Ab R ◯ ZExt R], and [TensorMonad R] is Monad/Comparison.v's
 [Adjunction_Induced_Monad] at [zext_adjunction R], whose ret is η and
 whose join is U ε F, both transparent.  So Mac Lane's formulas are read
 back by [eq_refl]: T on objects and arrows ([TensorF_obj],
 [TensorF_map]), η a = 1 ⊗ a ([TensorMonad_ret], BaseChange.v's
 [zext_unit_is_gen] seen through the monad), μ at each triple
 r₁ ⊗ (r₂ ⊗ a) ([TensorMonad_join]), μ as the counit's own homomorphism
 ([TensorMonad_join_counit]), and over ℤ, μ (3 ⊗ (4 ⊗ a)) = 12 ⊗ a
 ([TensorMonad_join_Z]).  The monad laws are not proved here: they are
 the adjunction's, derived in Monad/Comparison.v.  The precedents are
 Instance/Fun/Action/Monad.v and Instance/Grp/FreeAFT.v's
 [free_group_monad].

 ALGEBRAS ARE MODULES.  [em_smul] reads an algebra (A, h) as the action
 r · m := h (r ⊗ m): Riehl's scalar multiplication, h after the
 universal ℤ-bilinear map [ts_gen].  Its laws cost nothing new.
 Additivity in m and in r are [te_bilin_r] and [te_bilin_l] of the
 tensor followed by [cmon_map_plus] of h; the unit law 1 · m ≈ m is
 [t_id]; associativity (r s) · m ≈ r · (s · m) is the symmetry of
 [t_action] at r ⊗ (s ⊗ m), Monad/Algebra.v stating the μ-law as
 t_alg ∘ fmap t_alg ≈ t_alg ∘ join.  [EM_to_RMod] is the functor, the
 identity on underlying homomorphisms.  With Monad/Comparison.v's
 comparison functor [EM_Comparison], the K of Mac Lane's §VI.3 Theorem
 1 (printed p. 142), it forms [RMod_comparison_equivalence], with
 identity components both ways.  On the module side both laws close by
 [reflexivity]; on the algebra side the two structure maps agree on each
 generator r ⊗ m by [reflexivity] and so, by Instance/Ab/Tensor.v's
 [tensor_hom_ext], on every formal sum.  Hence [RMod_Forget_Ab_Monadic],
 Riehl's Example 5.5.7(i) in the sense of her Definition 5.3.1: the
 canonical comparison functor of THIS adjunction is the equivalence, not
 some other functor.  Hence also
 [EM_RMod_iso : RMod R ≅[Cat] EilenbergMoore (TensorF R)], whose [to]
 leg IS the comparison functor and whose [from] leg IS [EM_to_RMod]
 ([EM_RMod_iso_to], [EM_RMod_iso_from]).  The comparison algebra on a
 module M is M's action on each generator and the counit at M as a
 homomorphism ([comparison_alg_is_smul], [comparison_alg_counit]).

 RIEHL'S THEOREM 5.5.1, BY BECK.  [RMod_Forget_Ab_creates_split] is the
 creation of coequalizers of U-split pairs, in Monad/Monadicity/Beck.v's
 isomorphism-invariant sense.  Over a split coequalizer e : U B → Z,
 with sections s and t in [Ab], the created module is Z itself with
 r · z := e (r · s z) ([rmod_created_smul], [RModCreated]).  That this
 is a module, and that e is R-linear, rest on one absorption: a map out
 of U B that coforks the pair absorbs s ∘ e ([rmod_split_absorb],
 [rmod_created_absorb]).  The lift chosen is on the nose — the group IS
 Z, the action IS e (r · s z), the coequalizing arrow IS e and the
 comparison isomorphism IS the identity ([rmod_created_carrier],
 [rmod_created_action], [rmod_created_arrow], [rmod_created_iso]) —
 although the class asks only for an isomorphism (uniqueness of such a
 lift, Mac Lane's strict creation, is not claimed).  Beck.v's
 [beck_monadicity] then gives [RMod_beck_equivalence] and
 [RMod_Forget_Ab_Monadic_beck]; Instance/Fun/Action/Monad.v and
 Instance/Fun/Action/Monad/BG.v are its two other consumers.
 [RMod_Forget_Ab_reflects], that an R-linear map invertible as a group
 homomorphism is invertible as a module map, is Beck.v's
 [creates_split_reflects_isos] at this instance.  The two routes are
 equivalences of the same functor, on the nose ([EM_RMod_iso_beck_to],
 [rmod_beck_direct_to]); their quasi-inverses differ.  Beck's keeps the
 carrier and acts through η, r · m = h ((r · 1) ⊗ m)
 ([rmod_beck_carrier], [rmod_beck_act]), and it is ≈ to [EM_to_RMod] by
 [rig_mul_one_r] in the scalar slot ([rmod_beck_vs_direct]).

 WHICH “EXACTLY”, WHICH “MONADIC”.  Mac Lane's “the T-algebras are
 exactly the left R-modules” is read here as Riehl's equivalence.  Her
 Definition 5.3.1 calls an adjunction monadic when the canonical
 comparison functor “defines an equivalence of categories”, which is
 Monad/Comparison.v's [Monadic]; the “if” half of her Theorem 5.5.1,
 “A right adjoint functor U : D → C is monadic if and only if it
 creates coequalizers of U-split pairs”, is Beck.v's [beck_monadicity],
 in that form.  Mac Lane (§VI.3, printed p. 143) says instead that G is
 monadic when the comparison functor “will be an isomorphism”.  The
 [≅[Cat]] above is the tree's isomorphism in Cat, inverse up to natural
 isomorphism, hence an equivalence; the strict reading is not delivered
 (below).

 STRENGTHS.  By [eq_refl]: T on objects and arrows; η at each a; μ at
 each triple, at each r ⊗ y ([TensorMonad_join_gen]) and as the
 counit's homomorphism; the ℤ witness; an algebra's action on each
 generator ([EM_mod_smul]); the comparison algebra on each generator and
 as the counit at M; the [to] and [from] legs of [EM_RMod_iso]; the lift
 the creation chooses; the [to] leg of [EM_RMod_iso_beck] and its
 identity with that of [EM_RMod_iso]; Beck's quasi-inverse on carriers
 and its action through η.  In Test/ProbeTensorMonad465.v, also by
 [eq_refl]: the module round trip through the algebras on its group and
 on its action as a function; the algebra round trip on its carrier and
 on its structure map at each generator r ⊗ m; T f against the tensor
 bifunctor's 1 ⊗ f at each generator; and, over ℤ at the scalar 3,
 Beck's action as h (3 ⊗ m).  At ≈ only: the algebra round trip's
 structure map and T f against 1 ⊗ f at a formal sum (by
 [tensor_hom_ext]); the two composites of [EM_Comparison] and
 [EM_to_RMod] against the identity functors, as natural isomorphisms
 with identity components; Beck's quasi-inverse against [EM_to_RMod].
 Refused by conversion, each pinned in that probe: the whole module of
 the round trip (N1) and each of its five law fields (N2-N6), the
 algebra round trip's structure map as a function (N7) and at a
 variable formal sum (N8), the whole algebra (N9), the two composites
 as the identity functors (N10, N11), T f as 1 ⊗ f at a variable formal
 sum (N12) with the two [Bilinear] records beneath it and each of their
 three law fields (N12a-N12d), Beck's action as h (r ⊗ m) (N13, and over
 ℤ at a variable integer N13Z), Beck's quasi-inverse as [EM_to_RMod]
 (N14), and the two [Monadic] witnesses as one term (N15).  The
 instruments are N0, μ with its two scalars exchanged, and N0Z,
 μ (3 ⊗ (4 ⊗ a)) over ℤ as 13 ⊗ a.

 WHY THE ROUND TRIPS ARE REFUSED.  No refusal but N12d rests on an
 opaque constant of the tree.  In a copy of this file, its satellites
 Instance/Mod/Colimit/Creation.v and
 Instance/Mod/TensorMonad/Cocontinuous.v and their joint closure of 95
 files, with every [Qed] turned into [Defined] (Instance/Sets.v too,
 which flips once [setoid_morphism_compose_respects] and its one use
 are given explicit universes), [Transparent Obligations] set and
 [abstract] made [transparent_abstract] (Structure/Cartesian/Closed.v,
 where the change is itself refused, keeping its [Qed]s;
 Structure/Limit/Preservation.v's [preserves_colimit], which no term
 the probe compares uses (Adjunction/Continuity.v's
 [lapc_is_acolimit] does use it), given bullets that tolerate the
 goals the added transparency closes; the three files' universe
 annotations dropped there, the change raising the length of
 [ZExt]'s universe instance from 8 to 24, so that the annotations,
 written for 8, no longer fit), every
 refusal of this file's part of the probe but N12d stands, each
 stripped copy stopping with “cannot unify” inside its command, and
 every control holds.  There [Print Opaque Dependencies] on
 [RMod_comparison_equivalence], [RMod_beck_equivalence], the two
 [Monadic] witnesses, [TensorF], [EM_to_RMod] and Instance/Ab/Tensor.v's
 [tensor_map] lists 13 constants, all of them Corelib's lemmas of
 generalized rewriting, where this tree lists 157; no constant of
 Structure/Cartesian/Closed.v is among them in either.
 CORRECTION (#1347): this tree lists 154 since #1347, whose properness fields
 as terms take Corelib's [subrelation_id_proper], [proper_proper_proxy] and
 [CMorphisms.compose_proper_obligation_1] out of the census.
 In a further
 copy in which Instance/Sets.v's [setoid_morphism_id] has the properness
 proof fun _ _ H => H, which takes Corelib's opaque
 [subrelation_id_proper] out of the terms, the first builder's draft of
 N0-N15 (N12a-N12d were not run there) and N0Z stand again.
 The normal forms say why.  In that copy the [rm_smul_respects] field
 of the round trip is
 pequiv_to _ _ (pequiv_from _ _ (rm_smul_respects M r r' Hr m m' Hm)),
 a round trip through the [PropEquiv] fields of M's own group, which do
 not cancel on a variable.  The other four fields, applied to
 variables, have head normal forms headed by [Equivalence_Transitive]
 or [Equivalence_Symmetric] of M's setoid or, for [rm_smul_one], by
 Corelib's opaque [trans_co_eq_inv_arrow_morphism_obligation_1], whose
 printed body is one [transitivity] step; none is headed by the field
 it is compared with.  N7 and N8 compare the tensor mediator, a
 [Fixpoint] over formal sums stuck on a variable sum, with the variable
 algebra's own map.  N12 compares two stuck mediators whose [Bilinear]
 records have the same map, by [eq_refl], but different law proofs
 (N12a); each side is, by [eq_refl], the mediator of its own record at
 the variable sum, so being stuck is not the cause.  With every [Qed]
 flipped, [bilin_respects] and [bilin_add_l] still differ (N12b, N12c),
 while [bilin_add_r] becomes convertible, so N12d is refused by opacity
 alone.  N13 is r · 1 against r in the scalar slot at a variable scalar:
 at an abstract ring [rig_mul_one_r] is a propositional law, and even at
 [Int_Ring] the product is stuck on a variable integer (N13Z), while at
 the scalar 3 the same equation holds by [eq_refl].  N1 and N9-N11
 compare records carrying those fields and maps, and N14 and N15 carry
 Beck's quasi-inverse, which N13 separates from [EM_to_RMod].

 UNIVERSES, read off [About].  Every constant binds [@{a c p o x}], with
 R : RingObject@{a c p} (roles auxiliary, carrier, proof), Ab@{o c} and
 RMod@{o x a p c}.  The six that name Cat add [k] ([EM_RMod_iso],
 [EM_RMod_iso_to], [EM_RMod_iso_from], [EM_RMod_iso_beck],
 [EM_RMod_iso_beck_to], [rmod_beck_direct_to]), and [TensorMonad_join_Z]
 binds only [@{o x}], at [Int_Ring]'s levels, all Set.  The strict bounds
 are Set < o, c < o and c < x, with c < k and o < k on the six; the
 others are a <= o, c <= a and p <= a; at the ℤ witness they read Set < o
 and Set < x.  There is no equation and no other [Set].  First carriers,
 by [About] on the donors: Set < o and c < o, Instance/Ab.v's [Ab] (its
 block Set < u, p < u); c < x and a <= o, Instance/Mod.v's [RMod]
 (u3 < u0, u1 <= u); c <= a and p <= a, [RingObject] (u0 <= u, u1 <= u);
 c < k and o < k, Instance/Cat.v's [Cat] (u3 < u, u2 < u).  Two pins are
 load-bearing, both measured.  The witnesses are
 [Monadic@{o x o o o c o a}], the instance elaboration picks when
 [Monadic] is left bare; with o in the last slot the block gains a = o.
 The Cat isomorphisms are [Cat@{k o x o c}]; with o for x the block gains
 o = x.  The adjunction is pinned throughout as
 [zext_adjunction@{a c p o o x a a}].  The stdlib caps are inherited,
 and [About] on every constant of each donor's dependency cone, as
 [Print All Dependencies] lists it, places each at its topmost carrier:
 compose and ID on Instance/Sets.v's [setoid_morphism_compose] and
 [setoid_morphism_id], which reach this file through Instance/CMon.v's
 [cmon_hom_compose] and [cmon_hom_id] and so through [Ab]; prod_rect on
 two setoid rewrites, Instance/Ab.v's [ab_cancel_l], through
 Instance/Ab/Tensor.v's [tensor_hom_ext] and BaseChange.v's [ZExtObj],
 and Theory/Isomorphism.v's [iso_to_monic], through Theory/Adjunction.v's
 [Build_Adjunction'] and [zext_adjunction]; Logic_lemmas.equality on
 Lib/Setoid.v's [eq_equivalence] and projections (the pair projections)
 on [Build_Adjunction'], both through [zext_adjunction]; and Projections
 (the sigma projections) on Monad/Eilenberg/Moore.v's [EilenbergMoore].
 The creation readbacks apply Corelib's [projT1], [projT2] and, in
 [rmod_created_iso], [snd] in their own statements.

 NOT DELIVERED.  Mac Lane's “exactly” as an isomorphism on the nose: the
 whole-object round trips are refused at [eq_refl] (above).  No Kleisli
 category of R ⊗ (−) is identified.  Riehl's Corollary 5.6.10 (printed
 p. 212), that U creates every colimit that [Ab] has, is not in this
 file: Instance/Mod/Colimit/Creation.v proves it directly
 ([RMod_Forget_Ab_creates_colimits]), and
 Instance/Mod/TensorMonad/Cocontinuous.v holds the tensor–hom adjunction
 that makes R ⊗ (−) a left adjoint and the other premises of her monadic
 proof, whose last step is not in the tree.  The converse half of her
 Theorem 5.5.1 is Beck.v's [monadic_creates], stated at [EM_Forget] and
 not instantiated here.
 The tree has no general morphisms of monads, so no second, hand-built
 monad is kept and nothing is transported along one.  No right-module
 analogue (−) ⊗ R is built; no comparison is made with
 Instance/Mod/Tensor.v's R-tensor or Instance/Mod/Extension.v's
 [ExtendScalars]; and at R := ℤ nothing identifies T A = ℤ ⊗ A with
 A.

 CORRECTION (#468).  The tree now has general morphisms of monads,
 Monad/Morphism.v's [MonadHom] and [Monads C], and the functor θ* they
 induce on algebras, Monad/Morphism/Algebra.v's [mh_EM].  This file does
 not use them: it still keeps one monad, and no morphism of monads into or
 out of [TensorMonad R] is stated. 

 --------
 书籍：Mac Lane，《工作数学家的范畴论》，第2版，Springer GTM 5，1998年，第VI.2节，“模”，印刷页142（PDF第151页）—— maclane:VI.2:remark3；与第VI.3节，印刷页142–143
 书籍：Riehl，《上下文中的范畴论》，第2版，例5.2.6(ii)，印刷页189（PDF第209页）—— riehl:5.2:example6；例5.5.7(i)，印刷页205（PDF第225页）—— riehl:5.5:example7；与她的例4.1.10(xiii)，印刷页136，定义5.3.1，印刷页196，以及定理5.5.1，印刷页202
 nLab：https://ncatlab.org/nlab/show/module
 nLab：https://ncatlab.org/nlab/show/algebra+over+a+monad
 nLab：https://ncatlab.org/nlab/show/monadicity+theoremMac Lane 在 §VI.2（印刷版第141页）中以“几个例子结束，这些例子显示了熟悉的单子（monads）的 T-代数是熟悉的代数”作结。在闭包算子和群作用之后是模：“如果 R 是一个（小的）环，那么对于每一个（小的）阿贝尔群 A，定义 TA = R⊗A，A → R⊗A，R⊗(R⊗A) → R⊗A，a ↦ 1⊗a，r₁⊗(r₂⊗a) ↦ r₁r₂⊗a，其中 a ∈ A，r₁, r₂ ∈ R，这些定义在 Ab 上给出了一个单子。就像前面的例子一样，T-代数正好就是左 R-模。”前一个例子是 Instance/Fun/Action/Monad.v 中的群作用，而这个文件遵循它的模式。Riehl 的例子 5.2.6(ii) 取自她的例子 4.1.10(xiii) 的伴随，其遗忘函子 U : _R Mod → Ab 是“前一例子的特殊情况”，沿环映射 ℤ → R 的标量限制，并由此导出“Ab 上的单子 R ⊗_ℤ −”。代数的同态 R ⊗_ℤ A → A “编码了一个 ℤ-双线性映射 (r, a) ↦ r·a”，其两个图“确保 1·a = a 且 r·(r′·a) = (rr′)·a”，因此“Ab 上单子 R ⊗_ℤ − 的代数正好是 R-模”。她的例子 5.5.7(i) 得出结论：“遗忘函子 U : _R Mod → Ab 是单子性的。在 Ab 上诱导的单子由 R ⊗_ℤ − : Ab → Ab 给出。”该文件证明了这一切，并且对单子性进行了两次证明：通过一个显式的准逆，这是她在例子 5.5.7(i) 中采用的方法；以及通过 Beck 定理，即她的定理 5.5.1。没有任何东西被重建。这些类别是左模的 Instance/Ab.v 的 [Ab] 和 Instance/Mod.v 的 [RMod R]；张量是 Instance/Ab/Tensor.v 的 [AbTensor]，即两个阿贝尔群的 ℤ 张量，作为形式和的项模型；伴随是 Instance/Mod/BaseChange.v 的 [zext_adjunction R : ZExt R ⊣ RMod_Forget_Ab R]，其 [ZExt R] 将 A 映射到 R ⊗ A，并且由 r · (s ⊗ a) = (r s) ⊗ a 作用。树中 [Ab] 和 [RMod Int_Ring] 之间没有等价关系（BaseChange.v 的头部记录了它），因此 [ZExt R] 是 Riehl 的标量扩展，直接从 [Ab] 写出。这里只或那里没有要求 R 是交换的：Mac Lane 的 R 是一个环，他的代数是左模。单子是伴随的单子。[TensorF R] 是复合 [RMod_Forget_Ab R ◯ ZExt R]，而 [TensorMonad R] 是 Monad/Comparison.v 中的 [Adjunction_Induced_Monad] 在 [zext_adjunction R] 上，其 ret 是 η，join 是 U ε F，二者都是透明的。因此 Mac Lane 的公式可以通过 [eq_refl] 读取：在对象和箭头上为 T（[TensorF_obj]，[TensorF_map]），η a = 1 ⊗ a（[TensorMonad_ret]，透过单子看到 BaseChange.v 的 [zext_unit_is_gen]），μ 在每个三重 r₁ ⊗ (r₂ ⊗ a) 上（[TensorMonad_join]），μ 作为 counit 自身的同态（[TensorMonad_join_counit]），在 ℤ 上，μ (3 ⊗ (4 ⊗ a)) = 12 ⊗ a（[TensorMonad_join_Z]）。单子律在这里未证明：它们是伴随的，由 Monad/Comparison.v 推导。先例是 Instance/Fun/Action/Monad.v 和 Instance/Grp/FreeAFT.v 的 [free_group_monad]。代数是模。[em_smul] 将一个代数 (A, h) 读取为作用 
 r · m := h (r ⊗ m)：Riehl 的标量乘法，h 在通用 ℤ-双线性映射 [ts_gen] 之后。它的定律没有引入新的内容。对 m 和 r 的加法性是张量之后的 [te_bilin_r] 和 [te_bilin_l]，再加上 h 的 [cmon_map_plus]；单位律 1 · m ≈ m 是 [t_id]；结合律 (r s) · m ≈ r · (s · m) 是 [t_action] 在 r ⊗ (s ⊗ m) 处的对称性，Monad/Algebra.v 将 μ-律表述为 t_alg ∘ fmap t_alg ≈ t_alg ∘ join。[EM_to_RMod] 是函子，对基础同态是恒等。使用 Monad/Comparison.v 的比较函子 [EM_Comparison]，即 Mac Lane §VI.3 定理 1（印刷版第 142 页）中的 K，它形成 [RMod_comparison_equivalence]，双向的分量均为恒等。在模的方面，两条律在 [reflexivity] 处闭合；在代数的方面，对每个生成元 r ⊗ m，两条结构映射在 [reflexivity] 处一致，因此，根据 Instance/Ab/Tensor.v 的 [tensor_hom_ext]，在每个形式和上也一致。因此 [RMod_Forget_Ab_Monadic]，根据 Riehl 的定义 5.3.1 的例 5.5.7(i)：这个伴随的典范比较函子是等价的，而不是其他函子。因此也有 [EM_RMod_iso : RMod R ≅[Cat] EilenbergMoore (TensorF R)]，其 [to] 腿是比较函子，其 [from] 腿是 [EM_to_RMod] (ZWZ45WZZ, ZWZ46WZZ)。对模 M 的比较代数就是 M 在每个生成元上的作用，以及作为同态的余单位在 M 处 (ZWZ47WZZ, ZWZ48WZZ)。RIEHL 定理 5.5.1，由 BECK 提出。[RMod_Forget_Ab_creates_split] 是在 Monad/Monadicity/Beck.v 的同构不变意义下创建 U-分裂对的余等化器。在一个分裂余等化器 e : U B → Z 上，具有 [Ab] 中的截面 s 和 t，所创建的模是 Z 本身，操作为 r · z := e (r · s z) ([rmod_created_smul]、[RModCreated])。这个结构是一个模，并且 e 是 R 线性的，依靠一个吸收性质：从 U B 出发的映射，如果共叉了该对，则吸收 s ∘ e ([rmod_split_absorb]、[rmod_created_absorb])。所选择的提升是直接的——群是 Z，作用是 e (r · s z)，余等化箭头是 e，比对同构是恒等 ([rmod_created_carrier]、[rmod_created_action]、[rmod_created_arrow]、[rmod_created_iso])——尽管课程只要求一个同构（此类提升的唯一性，以及 Mac Lane 的严格创建，并没有被声明）。Beck.v 的 [beck_monadicity] 然后给出了 [RMod_beck_equivalence] 和 [RMod_Forget_Ab_Monadic_beck]；Instance/Fun/Action/Monad.v 和 Instance/Fun/Action/Monad/BG.v 是它的另外两个使用者。[RMod_Forget_Ab_reflects]，即作为群同态可逆的 R-线性映射在作为模映射时也是可逆的，是 Beck.v 在此实例的 [creates_split_reflects_isos]。两条路径是同一个函子在对象上的等价（[EM_RMod_iso_beck_to]，[rmod_beck_direct_to]）；它们的拟逆不同。Beck 的保持载体，并通过 η 作用，r · m = h ((r · 1) ⊗ m)（[rmod_beck_carrier]，[rmod_beck_act]），并且它在标量位置通过 [rig_mul_one_r] 与 [EM_to_RMod] 近似（[rmod_beck_vs_direct]）。哪一个“精确”，哪一个“单子”。Mac Lane 的“the T-algebras are exactly the left R-modules”在这里被解读为 Riehl 的等价。她的定义 5.3.1 当规范比较函子“定义了范畴的等价”时称一个挨陪 adjunction 为单子性的，这正是 Monad/Comparison.v 中的 [Monadic]；她的定理 5.5.1 中的“如果”部分，“一个右伴随函子 U : D → C 当且仅当它创建 U-分裂对的共同等化子时是单子性的”，在 Beck.v 中为 [beck_monadicity]，以这种形式。Mac Lane（§VI.3，印刷页 143）则说，当比较函子“将是同构”时 G 是单子性的。上面的 [≅[Cat] 是 Cat 中树的同构，上下由自然同构逆转，因此是一个等价；严格的解读没有给出（见下文）。优势。由 [eq_refl]：在对象和箭头上的 T；在每个 a 上的 η；在每个三元组、每个 r ⊗ y ([TensorMonad_join_gen]) 上以及作为余单位的同态的 μ；ℤ 的见证；代数在每个生成元上的作用 ([EM_mod_smul])；每个生成元上的比较代数以及在 M 上作为余单位；[to] 和 [from] 在 [EM_RMod_iso] 上的分支；创造所选择的提升；[to] 在 [EM_RMod_iso_beck] 上的分支及其与 [EM_RMod_iso] 的单位的同一性；Beck 在承载对象上的准逆及其通过 η 的作用。在 Test/ProbeTensorMonad465.v 中，同样由 [eq_refl] 编写：模块通过其群上的代数及其作为函数的作用进行往返；载体上的代数往返及每个生成元 r ⊗ m 的结构映射；T f 对每个生成元的张量双函子的 1 ⊗ f；以及在标量 3 的 ℤ 上，Beck 的作用作为 h (3 ⊗ m)。仅在 ≈ 上：代数往返的结构映射以及 T f 对形式和 1 ⊗ f（由 [tensor_hom_ext] 给出）；[EM_Comparison] 与 [EM_to_RMod] 的两个复合与恒等函子作为具有恒等分量的自然同构；Beck 的拟逆对应 [EM_to_RMod]。被转换拒绝，每个探针中固定：往返模块的整体（N1）及其五个定律域（N2-N6），作为函数的代数往返结构映射（N7）和在变量形式和（N8）上的映射，整个代数（N9），作为恒等函子的两个复合（N10, N11），T f 在变量形式和上的 1 ⊗ f（N12）及其下方的两个 [Bilinear] 记录及它们各自的三个定律域（N12a-N12d），Beck 的作用作为 h (r ⊗ m)（N13，在变量整数 N13Z 上为 ℤ），Beck 的准逆 [EM_to_RMod]（N14），以及两个 [Monadic] 见证作为一个项（N15）。工具为 N0，将其两个标量交换的 μ，以及 N0Z，μ (3 ⊗ (4 ⊗ a)) 在 ℤ 上为 13 ⊗ a。为什么往返被拒绝。没有拒绝，但 N12d 依赖于树的一个不透明常数。在该文件的一个副本中，它的卫星文件
 Instance/Mod/Colimit/Creation.v 和
 Instance/Mod/TensorMonad/Cocontinuous.v 及其联合闭包的 95 个文件，
 将每个 [Qed] 都改为 [Defined]（Instance/Sets.v 也一样，
 一次性翻转 [setoid_morphism_compose_respects] 及其一次使用后给出明确的宇宙），
 [Transparent Obligations] 集合和 [abstract] 改为 [transparent_abstract]（Structure/Cartesian/Closed.v，
 其中的修改本身被拒绝，保留其 [Qed]；
 Structure/Limit/Preservation.v 的 [preserves_colimit]，没有探针比较使用的术语（Adjunction/Continuity.v 的
 [lapc_is_acolimit] 确实使用它），给出了适应目标的子弹点，被新增透明性关闭；
 三个文件的宇宙注释在那里被删除，修改将 [ZExt] 的宇宙实例长度从 8 提高到 24，
 以便注释是为 8 编写的,不再适合），每一次对该文件部分探针的拒绝，但N12d仍然成立，每个剥离的副本在其命令中以“无法统一”停止，并且每个控制都保持有效。在 [Print Opaque Dependencies] 上的 [RMod_comparison_equivalence]、[RMod_beck_equivalence]，以及两个 [Monadic] 证人 [TensorF]、[EM_to_RMod] 和 Instance/Ab/Tensor.v 的 [tensor_map] 列出了 13 个常量，它们全部是 Corelib 的广义重写引理，而这个树列出了 157 个；在任何情况下，Structure/Cartesian/Closed.v 的常量都不在其中。更正 (#1347)：自 #1347 之后，这棵树列出了 154 个，因为其正确性字段作为项将 Corelib 的 [subrelation_id_proper]、[proper_proper_proxy] 和 [CMorphisms.compose_proper_obligation_1] 从清单中移除。在另一个副本中，其中 Instance/Sets.v 的 [setoid_morphism_id] 有适当性的证明 fun _ _ H => H，这将 Corelib 的不透明 [subrelation_id_proper] 从项中移除时，第一个 N0-N15（N12a-N12d 那里未运行）和 N0Z 的构建草稿再次出现。规范形式说明了原因。在该副本中，往返的 [rm_smul_respects] 字段是 pequiv_to _ _ (pequiv_from _ _ (rm_smul_respects M r r' Hr m m' Hm))，这是通过 M 自身群的 [PropEquiv] 字段的往返，它们不会在变量上抵消。其他四个字段，应用于变量时，其头部规范形式由 M 的 setoid 的 [Equivalence_Transitive] 或 [Equivalence_Symmetric] 主导，或者对于 [rm_smul_one] 由 Corelib 的不透明 [trans_co_eq_inv_arrow_morphism_obligation_1] 主导，其打印出的主体是一步 [transitivity]；没有一个由它所比较的字段主导。N7 和 N8 比较张量中介，一个 [Fixpoint] 作用于变量和上的形式和，与变量代数自身的映射。N12 比较了两个停滞的中介者，它们的 [Bilinear] 记录具有相同的映射，由 [eq_refl] 对比，但法律证明不同（N12a）；通过 [eq_refl]，每一方都是其自身记录在变量 sum 上的中介者，因此停滞不是原因。翻转每一个 [Qed] 后，[bilin_respects] 和 [bilin_add_l] 仍然不同（N12b，N12c），而 [bilin_add_r] 变得可转换，因此 N12d 单凭不透明性就被拒绝。N13 在变量标量的标量槽上是 r · 1 对 r：在抽象环 [rig_mul_one_r] 上是命题法则，即使在 [Int_Ring] 上，乘积仍停滞于变量整数（N13Z），而在标量 3 上相同的等式通过 [eq_refl] 成立。N1 和 N9-N11 比较了携带这些字段和映射的记录，N14 和 N15 携带 Beck 的拟逆，而 N13 将其与 [EM_to_RMod] 区分开。宇宙，从 [About] 读取。每个常量绑定 [@{a c p o x}]，其中 R: RingObject@{a c p}（角色：辅助、承载、证明），Ab@{o c} 和 RMod@{o x a p c}。命名 Cat 的六个添加 [k]（[EM_RMod_iso]、[EM_RMod_iso_to]、[EM_RMod_iso_from]、[EM_RMod_iso_beck]、[EM_RMod_iso_beck_to]、[rmod_beck_direct_to]），而 [TensorMonad_join_Z] 仅绑定 [@{o x}]，在 [Int_Ring] 的级别上，全部为 Set。严格上界为 Set < o，c < o 且 c < x，六个中 c < k 且 o < k；其他为 a <= o，c <= a 且 p <= a；在 ℤ 见证上，它们读作 Set < o 和 Set < x。没有方程，也没有其他 [Set]。首批载体，
 由 [About] 在供体上：设 < o 且 c < o，实例/Ab.v 的 [Ab] （其块 Set < u, p < u）；c < x 且 a <= o，实例/Mod.v 的 [RMod] （u3 < u0, u1 <= u）；c <= a 且 p <= a，[RingObject] （u0 <= u, u1 <= u）；c < k 且 o < k，实例/Cat.v 的 [Cat] （u3 < u, u2 < u）。两个引脚承载负荷，均已测量。证人是 [Monadic@{o x o o o c o a}]，当 [Monadic] 保持裸露时实例展开；在最后一个槽中有 o 时，块获得 a = o。Cat 同构是 [Cat@{k o x o c}]；用 o 替代 x，块获得 o = x。整个伴随都是固定的，如 [zext_adjunction@{a c p o o x a a}]。stdlib 的 caps 是继承的，且 [About] 在每个捐赠者依赖锥的每个常量上，如 [Print All Dependencies] 所列，将每个常量置于其最顶层的承载者上：compose 和 ID 在 Instance/Sets.v 的 [setoid_morphism_compose] 和 [setoid_morphism_id] 上，它们通过 Instance/CMon.v 的 [cmon_hom_compose] 和 [cmon_hom_id] 到达此文件，因此通过 [Ab]；prod_rect 在两个 setoid 重写上，Instance/Ab.v 的 [ab_cancel_l]，通过 Instance/Ab/Tensor.v 的 [tensor_hom_ext] 和 BaseChange.v 的 [ZExtObj]，以及 Theory/Isomorphism.v 的 [iso_to_monic]，通过 Theory/Adjunction.v 的 [Build_Adjunction'] 和 [zext_adjunction]；Logic_lemmas.equality 在 Lib/Setoid.v 的 [eq_equivalence] 上和投影（对投影）在 [Build_Adjunction'] 上，两者均通过 [zext_adjunction]；以及 Projections（σ 投影）在 Monad/Eilenberg/Moore.v 的 [EilenbergMoore] 上。创建回读在各自的语句中应用了 Corelib 的 [projT1]、[projT2]，以及在 [rmod_created_iso] 中的 [snd]。未发送。Mac Lane 的“完全正确”作为严格同构：在 [eq_refl]（上文）处拒绝了整对象的往返操作。未识别出 R ⊗ (−) 的任何 Kleisli 范畴。Riehl 的推论 5.6.10（印刷页 212），即 U 创建 [Ab] 所有的余极限，在此文件中不存在：Instance/Mod/Colimit/Creation.v 直接证明了它（[RMod_Forget_Ab_creates_colimits]），并且 Instance/Mod/TensorMonad/Cocontinuous.v 包含了使 R ⊗ (−) 成为左伴随的张量–函子伴随关系及她的单子证明的其他前提，其最后一步不在树中。她的定理 5.5.1 的逆半部分是 Beck.v 的 [monadic_creates]，于 [EM_Forget] 陈述，此处未实例化。该树没有一般的单子态射，因此没有保留第二个手工构建的单子，也没有沿着任何单子进行传递。没有构建右模 analog (−) ⊗ R；也没有与 Instance/Mod/Tensor.v 的 R-tensor 或 Instance/Mod/Extension.v 的 [ExtendScalars] 做比较；并且在 R := ℤ 时，没有任何东西将 T A = ℤ ⊗ A 与 A 识别出来。

 修正 (#468)。该树现在具有 Monad/Morphism.v 的 [MonadHom] 和 [Monads C] 的一般单子态射，以及它们在代数上诱导的函子 θ*，见 Monad/Morphism/Algebra.v 的 [mh_EM]。该文件没有使用它们：它仍然只保留一个单子，并且没有声明任何进入或退出 [TensorMonad R] 的单子态射。
*)

(** ** The monad R ⊗ (−) on Ab / ** Ab 上的单子 R ⊗ (−) *)

(*
 T is the composite U ◯ F of the free/forgetful adjunction; the monad is
 Monad/Comparison.v's, whose ret is η and whose join is U ε F. 

 --------
 T 是自由/遗忘伴随的复合 U ◯ F；该 monad 是 Monad/Comparison.v 中的，其 ret 是 η，join 是 U ε F。
*)
Definition TensorF@{a c p o x} (R : RingObject@{a c p}) :
  Ab@{o c} ⟶ Ab@{o c} :=
  RMod_Forget_Ab@{x o o a p c} R ◯ ZExt@{a c p x o a o c} R.

Definition TensorMonad@{a c p o x} (R : RingObject@{a c p}) :
  @Monad Ab@{o c} (TensorF@{a c p o x} R) :=
  Adjunction_Induced_Monad (zext_adjunction@{a c p o o x a a} R).

(* Mac Lane's formulas, read back on the nose: TA = R ⊗ A, T f = 1 ⊗ f (BaseChange.v's [zext_map_ab]), η a = 1 ⊗ a, and μ (r₁ ⊗ (r₂ ⊗ a)) = r₁r₂ ⊗ a. / 麦克莱恩的公式，按字面读取：TA = R ⊗ A, T f = 1 ⊗ f （BaseChange.v 的 [zext_map_ab]），η a = 1 ⊗ a，以及 μ (r₁ ⊗ (r₂ ⊗ a)) = r₁r₂ ⊗ a。 *)
Example TensorF_obj@{a c p o x} (R : RingObject@{a c p}) (A : obj[Ab@{o c}]) :
  fobj[TensorF@{a c p o x} R] A = AbTensor (ring_ab R) A := eq_refl.

Example TensorF_map@{a c p o x} (R : RingObject@{a c p})
  (A B : obj[Ab@{o c}]) (f : A ~{Ab@{o c}}~> B) :
  fmap[TensorF@{a c p o x} R] f = zext_map_ab R f := eq_refl.

Example TensorMonad_ret@{a c p o x} (R : RingObject@{a c p})
  (A : obj[Ab@{o c}]) (a : carrier A) :
  cmon_map (@ret _ _ (TensorMonad@{a c p o x} R) A) a
  = @ts_gen (ring_ab R) A (rig_one (ring_rig R)) a := eq_refl.

Example TensorMonad_join@{a c p o x} (R : RingObject@{a c p})
  (A : obj[Ab@{o c}]) (r1 r2 : carrier (rig_setoid (ring_rig R)))
  (a : carrier A) :
  cmon_map (@join _ _ (TensorMonad@{a c p o x} R) A)
    (@ts_gen (ring_ab R) (AbTensor (ring_ab R) A) r1
       (@ts_gen (ring_ab R) A r2 a))
  = @ts_gen (ring_ab R) A (rig_mul (ring_rig R) r1 r2) a := eq_refl.

(*
 μ IS the adjunction's counit at the free module R ⊗ A, as a
 homomorphism of abelian groups, and on each generator r ⊗ y it is the
 free module's own action r · y. 

 --------
 μ 是在自由模 R ⊗ A 上的伴随余单位，作为阿贝尔群的同态，在每个生成元 r ⊗ y 上，它是自由模自身的作用 r · y。
*)
Example TensorMonad_join_counit@{a c p o x} (R : RingObject@{a c p})
  (A : obj[Ab@{o c}]) :
  @join _ _ (TensorMonad@{a c p o x} R) A
  = rm_hom (zext_counit@{a c p o x a o a} R (ZExtObj R A)) := eq_refl.

Example TensorMonad_join_gen@{a c p o x} (R : RingObject@{a c p})
  (A : obj[Ab@{o c}]) (r : carrier (rig_setoid (ring_rig R)))
  (y : carrier (AbTensor (ring_ab R) A)) :
  cmon_map (@join _ _ (TensorMonad@{a c p o x} R) A)
    (@ts_gen (ring_ab R) (AbTensor (ring_ab R) A) r y)
  = zext_act R A r y := eq_refl.

(* A computing witness over ℤ: μ (3 ⊗ (4 ⊗ a)) = 12 ⊗ a. / ℤ 上的计算见证：μ (3 ⊗ (4 ⊗ a)) = 12 ⊗ a。 *)
Example TensorMonad_join_Z@{o x} (a : Z) :
  cmon_map (@join _ _ (TensorMonad@{Set Set Set o x} Int_Ring)
              (ring_ab Int_Ring))
    (@ts_gen (ring_ab Int_Ring) (AbTensor (ring_ab Int_Ring) (ring_ab Int_Ring))
       3%Z (@ts_gen (ring_ab Int_Ring) (ring_ab Int_Ring) 4%Z a))
  = @ts_gen (ring_ab Int_Ring) (ring_ab Int_Ring) 12%Z a := eq_refl.

(** ** Algebras are left modules / ** 代数是左模 *)

(* An algebra (A, h) acts by r · m := h (r ⊗ m). Riehl's “ℤ-bilinear map (r, a) ↦ r·a” is h composed with the universal bilinear map. / 一个代数 (A, h) 通过 r · m := h (r ⊗ m) 作用。Riehl 的“ℤ-双线性映射 (r, a) ↦ r·a”是 h 与普遍双线性映射的复合。 *)
Definition em_smul@{a c p o x} {R : RingObject@{a c p}}
  (X : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
         (TensorMonad@{a c p o x} R))
  (r : carrier (rig_setoid (ring_rig R))) (m : carrier (`1 X)) :
  carrier (`1 X) :=
  cmon_map (t_alg[`2 X]) (@ts_gen (ring_ab R) (`1 X) r m).

Lemma em_smul_respects@{a c p o x} {R : RingObject@{a c p}}
  (X : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
         (TensorMonad@{a c p o x} R)) :
  Proper (equiv ==> equiv ==> equiv) (em_smul@{a c p o x} X).
Proof.
  intros r r' Hr m m' Hm.
  exact (proper_morphism (cmon_map (t_alg[`2 X])) _ _
           (@te_gen (ring_ab R) (`1 X) _ _ _ _ Hr Hm)).
Qed.

(* Additivity in m and in r: h is additive and ⊗ is bilinear. / 在 m 和 r 中的可加性：h 是可加的，⊗ 是双线性的。 *)
Lemma em_smul_distr_l@{a c p o x} {R : RingObject@{a c p}}
  (X : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
         (TensorMonad@{a c p o x} R))
  (r : carrier (rig_setoid (ring_rig R))) (m n : carrier (`1 X)) :
  em_smul X r (cmon_plus (`1 X) m n)
    ≈ cmon_plus (`1 X) (em_smul X r m) (em_smul X r n).
Proof.
  unfold em_smul.
  transitivity (cmon_map (t_alg[`2 X])
                  (cmon_plus (AbTensor (ring_ab R) (`1 X))
                     (@ts_gen (ring_ab R) (`1 X) r m)
                     (@ts_gen (ring_ab R) (`1 X) r n))).
  - exact (proper_morphism (cmon_map (t_alg[`2 X])) _ _
             (@te_bilin_r (ring_ab R) (`1 X) r m n)).
  - exact (cmon_map_plus (t_alg[`2 X]) _ _).
Qed.

Lemma em_smul_distr_r@{a c p o x} {R : RingObject@{a c p}}
  (X : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
         (TensorMonad@{a c p o x} R))
  (r s : carrier (rig_setoid (ring_rig R))) (m : carrier (`1 X)) :
  em_smul X (rig_add (ring_rig R) r s) m
    ≈ cmon_plus (`1 X) (em_smul X r m) (em_smul X s m).
Proof.
  unfold em_smul.
  transitivity (cmon_map (t_alg[`2 X])
                  (cmon_plus (AbTensor (ring_ab R) (`1 X))
                     (@ts_gen (ring_ab R) (`1 X) r m)
                     (@ts_gen (ring_ab R) (`1 X) s m))).
  - exact (proper_morphism (cmon_map (t_alg[`2 X])) _ _
             (@te_bilin_l (ring_ab R) (`1 X) r s m)).
  - exact (cmon_map_plus (t_alg[`2 X]) _ _).
Qed.

(* Mac Lane's μ-law of the algebra, read at r ⊗ (s ⊗ m), is associativity of the action; [t_action] states it with the two sides exchanged. / 麦克莱恩的代数 μ-律，在 r ⊗ (s ⊗ m) 处读取，是作用的结合律；[t_action] 用交换的两边来陈述它。 *)
Lemma em_smul_assoc@{a c p o x} {R : RingObject@{a c p}}
  (X : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
         (TensorMonad@{a c p o x} R))
  (r s : carrier (rig_setoid (ring_rig R))) (m : carrier (`1 X)) :
  em_smul X (rig_mul (ring_rig R) r s) m ≈ em_smul X r (em_smul X s m).
Proof.
  symmetry.
  exact (@t_action _ _ _ _ (`2 X)
           (@ts_gen (ring_ab R) (AbTensor (ring_ab R) (`1 X)) r
              (@ts_gen (ring_ab R) (`1 X) s m))).
Qed.

(* The η-law of the algebra is 1 · m ≈ m. / 代数的 η-律是 1 · m ≈ m。 *)
Lemma em_smul_one@{a c p o x} {R : RingObject@{a c p}}
  (X : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
         (TensorMonad@{a c p o x} R))
  (m : carrier (`1 X)) :
  em_smul X (rig_one (ring_rig R)) m ≈ m.
Proof. exact (@t_id _ _ _ _ (`2 X) m). Qed.

Definition EM_mod@{a c p o x} {R : RingObject@{a c p}}
  (X : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
         (TensorMonad@{a c p o x} R)) :
  obj[RMod@{o x a p c} R] :=
  @Build_RModObject R (`1 X) (em_smul X) (em_smul_respects X)
    (em_smul_distr_l X) (em_smul_distr_r X) (em_smul_assoc X)
    (em_smul_one X).

Definition EM_mod_hom@{a c p o x} {R : RingObject@{a c p}}
  {X Y : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
           (TensorMonad@{a c p o x} R)}
  (f : X ~{@EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
             (TensorMonad@{a c p o x} R)}~> Y) :
  EM_mod X ~{RMod@{o x a p c} R}~> EM_mod Y :=
  @Build_RModHom R (EM_mod X) (EM_mod Y) t_alg_hom[f]
    (fun r m => @t_alg_hom_commutes _ _ _ _ _ _ _ f
                  (@ts_gen (ring_ab R) (`1 X) r m)).

Definition EM_to_RMod@{a c p o x} (R : RingObject@{a c p}) :
  @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
    (TensorMonad@{a c p o x} R) ⟶ RMod@{o x a p c} R.
Proof.
  unshelve refine
    (@Build_Functor
       (@EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
          (TensorMonad@{a c p o x} R))
       (RMod@{o x a p c} R) (fun X => EM_mod X) (fun X Y f => EM_mod_hom f)
       _ _ _).
  - intros X Y f f' Hf m. exact (Hf m).
  - intros X m. reflexivity.
  - intros X Y Z f g m. reflexivity.
Defined.

(* The action of [EM_mod X] IS h on generators, by definition. / 根据定义，[EM_mod X] 在生成元上的作用是 h。 *)
Example EM_mod_smul@{a c p o x} {R : RingObject@{a c p}}
  (X : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
         (TensorMonad@{a c p o x} R))
  (r : carrier (rig_setoid (ring_rig R))) (m : carrier (`1 X)) :
  rm_smul (EM_mod X) r m
  = cmon_map (t_alg[`2 X]) (@ts_gen (ring_ab R) (`1 X) r m) := eq_refl.

(* * ** The comparison functor is an equivalence / * ** 比较函子是一个等价 *)

(* Module round trip: identity components, both laws by reflexivity. / 模块往返：恒等分量，两条法则都是由自反性得出。 *)
Definition RMod_counit_iso@{a c p o x} {R : RingObject@{a c p}}
  (M : obj[RMod@{o x a p c} R]) :
  @Isomorphism (RMod@{o x a p c} R)
    (fobj[EM_to_RMod@{a c p o x} R
          ◯ EM_Comparison (zext_adjunction@{a c p o o x a a} R)] M) M.
Proof.
  unshelve refine
    (@Build_Isomorphism (RMod@{o x a p c} R) _ _
       (@Build_RModHom R
          (fobj[EM_to_RMod@{a c p o x} R
                ◯ EM_Comparison (zext_adjunction@{a c p o o x a a} R)] M) M
          (@cmon_hom_id (rm_ab M)) _)
       (@Build_RModHom R M
          (fobj[EM_to_RMod@{a c p o x} R
                ◯ EM_Comparison (zext_adjunction@{a c p o o x a a} R)] M)
          (@cmon_hom_id (rm_ab M)) _) _ _).
  - intros r m. reflexivity.
  - intros r m. reflexivity.
  - intros m. reflexivity.
  - intros m. reflexivity.
Defined.

(*
 Algebra round trip: identity components; the structure maps agree on
 each generator r ⊗ m by [reflexivity] and on every formal sum by
 [tensor_hom_ext], the uniqueness half of the tensor's universal
 property. 

 --------
 代数往返：恒等分量；结构映射在每个生成元 r ⊗ m 上通过 [reflexivity] 一致，并且在每个形式和上通过 [tensor_hom_ext] 一致，这是张量的泛性质的唯一性部分。
*)
Definition RMod_unit_iso@{a c p o x} {R : RingObject@{a c p}}
  (X : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
         (TensorMonad@{a c p o x} R)) :
  @Isomorphism
    (@EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
       (TensorMonad@{a c p o x} R))
    (fobj[EM_Comparison (zext_adjunction@{a c p o o x a a} R)
          ◯ EM_to_RMod@{a c p o x} R] X) X.
Proof.
  unshelve refine
    (@Build_Isomorphism
       (@EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
          (TensorMonad@{a c p o x} R))
       (fobj[EM_Comparison (zext_adjunction@{a c p o o x a a} R)
             ◯ EM_to_RMod@{a c p o x} R] X) X
       (@Build_TAlgebraHom Ab@{o c} (TensorF@{a c p o x} R)
          (TensorMonad@{a c p o x} R) (`1 X) (`1 X)
          (`2 (fobj[EM_Comparison (zext_adjunction@{a c p o o x a a} R)
                    ◯ EM_to_RMod@{a c p o x} R] X)) (`2 X)
          (@cmon_hom_id (`1 X)) _)
       (@Build_TAlgebraHom Ab@{o c} (TensorF@{a c p o x} R)
          (TensorMonad@{a c p o x} R) (`1 X) (`1 X)
          (`2 X) (`2 (fobj[EM_Comparison (zext_adjunction@{a c p o o x a a} R)
                        ◯ EM_to_RMod@{a c p o x} R] X))
          (@cmon_hom_id (`1 X)) _) _ _).
  - intros s.
    refine (tensor_hom_ext _ _ _ s).
    intros r m. reflexivity.
  - intros s.
    refine (tensor_hom_ext _ _ _ s).
    intros r m. reflexivity.
  - intros m. reflexivity.
  - intros m. reflexivity.
Defined.

Definition RMod_comparison_equivalence@{a c p o x} (R : RingObject@{a c p}) :
  EquivalenceOfCategories (EM_Comparison (zext_adjunction@{a c p o o x a a} R)).
Proof.
  unshelve refine
    (@Build_EquivalenceOfCategories _ _
       (EM_Comparison (zext_adjunction@{a c p o o x a a} R))
       (EM_to_RMod@{a c p o x} R) _ _).
  - exists (fun X => RMod_unit_iso X).
    intros [A α] [B β] f m; simpl. reflexivity.
  - exists (fun M => iso_sym (RMod_counit_iso M)).
    intros M N h m; simpl. reflexivity.
Defined.

(*
 Riehl's Example 5.5.7(i): the forgetful functor is monadic, and the
 equivalence is the canonical comparison functor of [zext_adjunction]
 itself (her Definition 5.3.1), not some other equivalence. 

 --------
 Riehl 的例 5.5.7(i)：遗忘函子是单代的，并且等价是 [zext_adjunction] 本身的典型比较函子（她的定义 5.3.1），而不是某种其他等价。
*)
Definition RMod_Forget_Ab_Monadic@{a c p o x} (R : RingObject@{a c p}) :
  @Monadic@{o x o o o c o a} (RMod@{o x a p c} R) Ab@{o c}
    (RMod_Forget_Ab@{x o o a p c} R).
Proof.
  exists (ZExt@{a c p x o a o c} R).
  exists (zext_adjunction@{a c p o o x a a} R).
  exact (RMod_comparison_equivalence@{a c p o x} R).
Defined.

Definition EM_RMod_iso@{a c p o x k} (R : RingObject@{a c p}) :
  @Isomorphism Cat@{k o x o c}
    (RMod@{o x a p c} R)
    (@EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
       (TensorMonad@{a c p o x} R)) :=
  Equivalence_to_Cat_Iso (RMod_comparison_equivalence@{a c p o x} R).

Example EM_RMod_iso_to@{a c p o x k} (R : RingObject@{a c p}) :
  to (EM_RMod_iso@{a c p o x k} R)
  = EM_Comparison (zext_adjunction@{a c p o o x a a} R) := eq_refl.

Example EM_RMod_iso_from@{a c p o x k} (R : RingObject@{a c p}) :
  from (EM_RMod_iso@{a c p o x k} R) = EM_to_RMod@{a c p o x} R := eq_refl.

(* The comparison algebra on a module M is U ε_M: on r ⊗ m it is r · m, and as a homomorphism it IS the counit at M. / 模 M 上的比较代数是 U ε_M：在 r ⊗ m 上它是 r · m，作为同态它就是 M 上的余单位。 *)
Example comparison_alg_is_smul@{a c p o x} {R : RingObject@{a c p}}
  (M : obj[RMod@{o x a p c} R]) (r : carrier (rig_setoid (ring_rig R)))
  (m : carrier (rm_ab M)) :
  cmon_map (t_alg[`2 (fobj[EM_Comparison
                              (zext_adjunction@{a c p o o x a a} R)] M)])
    (@ts_gen (ring_ab R) (rm_ab M) r m)
  = rm_smul M r m := eq_refl.

Example comparison_alg_counit@{a c p o x} {R : RingObject@{a c p}}
  (M : obj[RMod@{o x a p c} R]) :
  t_alg[`2 (fobj[EM_Comparison (zext_adjunction@{a c p o o x a a} R)] M)]
  = rm_hom (zext_counit@{a c p o x a o a} R M) := eq_refl.

(* * ** Riehl's Theorem 5.5.1: the creation of U-split coequalizers / * ** Riehl 定理 5.5.1：U-分裂余等化子的构造 *)

(*
 Absorption: a map h out of U B coforking the pair satisfies
 h (s (e y)) ≈ h y. 

 --------
 吸收：从 U B 共分叉这对的一个映射 h 满足 h (s (e y)) ≈ h y。
*)
Lemma rmod_split_absorb@{a c p o x} {R : RingObject@{a c p}}
  {A B : obj[RMod@{o x a p c} R]} (f g : A ~{RMod@{o x a p c} R}~> B)
  (S : @SplitCoequalizer Ab@{o c} _ _
         (fmap[RMod_Forget_Ab@{x o o a p c} R] f)
         (fmap[RMod_Forget_Ab@{x o o a p c} R] g))
  {W : obj[Ab@{o c}]} (h : rm_ab B ~{Ab@{o c}}~> W)
  (Hh : ∀ y, cmon_map h (cmon_map (rm_hom f) y)
             ≈ cmon_map h (cmon_map (rm_hom g) y))
  (y : carrier (rm_ab B)) :
  cmon_map h (cmon_map (scoeq_s S) (cmon_map (scoeq_e S) y)) ≈ cmon_map h y.
Proof.
  pose proof (scoeq_law4 S y) as L4; simpl in L4.
  pose proof (scoeq_law3 S y) as L3; simpl in L3.
  transitivity (cmon_map h (cmon_map (rm_hom g) (cmon_map (scoeq_t S) y))).
  - apply (proper_morphism (cmon_map h)). symmetry. exact L4.
  - transitivity (cmon_map h (cmon_map (rm_hom f) (cmon_map (scoeq_t S) y))).
    + symmetry. apply Hh.
    + apply (proper_morphism (cmon_map h)). exact L3.
Qed.

(* The created action on the split coequalizer Z: r · z := e (r · s z). / 在分裂共同等化器 Z 上创建的动作：r · z := e (r · s z)。 *)
Definition rmod_created_smul@{a c p o x} {R : RingObject@{a c p}}
  {A B : obj[RMod@{o x a p c} R]} (f g : A ~{RMod@{o x a p c} R}~> B)
  (S : @SplitCoequalizer Ab@{o c} _ _
         (fmap[RMod_Forget_Ab@{x o o a p c} R] f)
         (fmap[RMod_Forget_Ab@{x o o a p c} R] g))
  (r : carrier (rig_setoid (ring_rig R))) (z : carrier (scoeq_obj S)) :
  carrier (scoeq_obj S) :=
  cmon_map (scoeq_e S) (rm_smul B r (cmon_map (scoeq_s S) z)).

Lemma rmod_created_absorb@{a c p o x} {R : RingObject@{a c p}}
  {A B : obj[RMod@{o x a p c} R]} (f g : A ~{RMod@{o x a p c} R}~> B)
  (S : @SplitCoequalizer Ab@{o c} _ _
         (fmap[RMod_Forget_Ab@{x o o a p c} R] f)
         (fmap[RMod_Forget_Ab@{x o o a p c} R] g))
  (r : carrier (rig_setoid (ring_rig R))) (y : carrier (rm_ab B)) :
  cmon_map (scoeq_e S) (rm_smul B r (cmon_map (scoeq_s S)
                                       (cmon_map (scoeq_e S) y)))
  ≈ cmon_map (scoeq_e S) (rm_smul B r y).
Proof.
  pose proof (scoeq_law4 S y) as L4; simpl in L4.
  pose proof (scoeq_law3 S y) as L3; simpl in L3.
  pose proof (scoeq_law1 S (rm_smul A r (cmon_map (scoeq_t S) y))) as L1;
    simpl in L1.
  transitivity (cmon_map (scoeq_e S)
                  (rm_smul B r (cmon_map (rm_hom g) (cmon_map (scoeq_t S) y)))).
  - apply (proper_morphism (cmon_map (scoeq_e S))).
    apply rm_smul_respects; [ reflexivity | symmetry; exact L4 ].
  - transitivity (cmon_map (scoeq_e S)
                    (cmon_map (rm_hom g)
                       (rm_smul A r (cmon_map (scoeq_t S) y)))).
    + apply (proper_morphism (cmon_map (scoeq_e S))).
      symmetry. apply rm_map_smul.
    + transitivity (cmon_map (scoeq_e S)
                      (cmon_map (rm_hom f)
                         (rm_smul A r (cmon_map (scoeq_t S) y)))).
      * symmetry. exact L1.
      * transitivity (cmon_map (scoeq_e S)
                        (rm_smul B r
                           (cmon_map (rm_hom f) (cmon_map (scoeq_t S) y)))).
        -- apply (proper_morphism (cmon_map (scoeq_e S))). apply rm_map_smul.
        -- apply (proper_morphism (cmon_map (scoeq_e S))).
           apply rm_smul_respects; [ reflexivity | exact L3 ].
Qed.

Definition RModCreated@{a c p o x} {R : RingObject@{a c p}}
  {A B : obj[RMod@{o x a p c} R]} (f g : A ~{RMod@{o x a p c} R}~> B)
  (S : @SplitCoequalizer Ab@{o c} _ _
         (fmap[RMod_Forget_Ab@{x o o a p c} R] f)
         (fmap[RMod_Forget_Ab@{x o o a p c} R] g)) :
  obj[RMod@{o x a p c} R].
Proof.
  unshelve refine (@Build_RModObject R (scoeq_obj S)
                     (rmod_created_smul f g S) _ _ _ _ _).
  - intros r r' Hr z z' Hz. unfold rmod_created_smul.
    apply (proper_morphism (cmon_map (scoeq_e S))).
    apply rm_smul_respects;
      [ exact Hr | apply (proper_morphism (cmon_map (scoeq_s S))); exact Hz ].
  - intros r z w. unfold rmod_created_smul.
    transitivity (cmon_map (scoeq_e S)
                    (rm_smul B r (cmon_plus (rm_ab B) (cmon_map (scoeq_s S) z)
                                              (cmon_map (scoeq_s S) w)))).
    + apply (proper_morphism (cmon_map (scoeq_e S))).
      apply rm_smul_respects; [ reflexivity | apply cmon_map_plus ].
    + transitivity (cmon_map (scoeq_e S)
                      (cmon_plus (rm_ab B)
                         (rm_smul B r (cmon_map (scoeq_s S) z))
                         (rm_smul B r (cmon_map (scoeq_s S) w)))).
      * apply (proper_morphism (cmon_map (scoeq_e S))). apply rm_smul_distr_l.
      * apply cmon_map_plus.
  - intros r r' z. unfold rmod_created_smul.
    transitivity (cmon_map (scoeq_e S)
                    (cmon_plus (rm_ab B)
                       (rm_smul B r (cmon_map (scoeq_s S) z))
                       (rm_smul B r' (cmon_map (scoeq_s S) z)))).
    + apply (proper_morphism (cmon_map (scoeq_e S))). apply rm_smul_distr_r.
    + apply cmon_map_plus.
  - intros r r' z. unfold rmod_created_smul.
    transitivity (cmon_map (scoeq_e S)
                    (rm_smul B r (rm_smul B r' (cmon_map (scoeq_s S) z)))).
    + apply (proper_morphism (cmon_map (scoeq_e S))). apply rm_smul_assoc.
    + symmetry. apply rmod_created_absorb.
  - intros z. unfold rmod_created_smul.
    pose proof (scoeq_law2 S z) as L2; simpl in L2.
    transitivity (cmon_map (scoeq_e S) (cmon_map (scoeq_s S) z));
      [ | exact L2 ].
    apply (proper_morphism (cmon_map (scoeq_e S))). apply rm_smul_one.
Defined.

Definition RModCreatedE@{a c p o x} {R : RingObject@{a c p}}
  {A B : obj[RMod@{o x a p c} R]} (f g : A ~{RMod@{o x a p c} R}~> B)
  (S : @SplitCoequalizer Ab@{o c} _ _
         (fmap[RMod_Forget_Ab@{x o o a p c} R] f)
         (fmap[RMod_Forget_Ab@{x o o a p c} R] g)) :
  B ~{RMod@{o x a p c} R}~> RModCreated f g S.
Proof.
  unshelve refine (@Build_RModHom R B (RModCreated f g S) (scoeq_e S) _).
  intros r y. simpl. unfold rmod_created_smul. symmetry.
  apply rmod_created_absorb.
Defined.

Definition RModCreatedE_is_coeq@{a c p o x} {R : RingObject@{a c p}}
  {A B : obj[RMod@{o x a p c} R]} (f g : A ~{RMod@{o x a p c} R}~> B)
  (S : @SplitCoequalizer Ab@{o c} _ _
         (fmap[RMod_Forget_Ab@{x o o a p c} R] f)
         (fmap[RMod_Forget_Ab@{x o o a p c} R] g)) :
  @IsCoequalizer (RMod@{o x a p c} R) A B f g
    (RModCreated f g S) (RModCreatedE f g S).
Proof.
  unshelve refine (@Build_IsCoequalizer _ _ _ _ _ _ _ _ _).
  - intros y. exact (scoeq_law1 S y).
  - intros W h Hh.
    unshelve eapply Build_Unique.
    + unshelve refine
        (@Build_RModHom R (RModCreated f g S) W
           (cmon_hom_compose (rm_hom h) (scoeq_s S)) _).
      intros r z; simpl. unfold rmod_created_smul.
      transitivity (cmon_map (rm_hom h) (rm_smul B r (cmon_map (scoeq_s S) z))).
      * exact (rmod_split_absorb f g S (rm_hom h) Hh _).
      * apply rm_map_smul.
    + intros y; simpl. exact (rmod_split_absorb f g S (rm_hom h) Hh y).
    + intros v Hv z; simpl.
      pose proof (scoeq_law2 S z) as L2; simpl in L2.
      transitivity (cmon_map (rm_hom v)
                      (cmon_map (scoeq_e S) (cmon_map (scoeq_s S) z))).
      * symmetry. exact (Hv (cmon_map (scoeq_s S) z)).
      * apply (proper_morphism (cmon_map (rm_hom v))). exact L2.
Defined.

Definition RModReflected_is_coeq@{a c p o x} {R : RingObject@{a c p}}
  {A B : obj[RMod@{o x a p c} R]} (f g : A ~{RMod@{o x a p c} R}~> B)
  (S : @SplitCoequalizer Ab@{o c} _ _
         (fmap[RMod_Forget_Ab@{x o o a p c} R] f)
         (fmap[RMod_Forget_Ab@{x o o a p c} R] g))
  (Q : obj[RMod@{o x a p c} R]) (e : B ~{RMod@{o x a p c} R}~> Q)
  (He : e ∘ f ≈ e ∘ g)
  (i : @Isomorphism Ab@{o c} (fobj[RMod_Forget_Ab@{x o o a p c} R] Q)
         (scoeq_obj S))
  (Hi : to i ∘ fmap[RMod_Forget_Ab@{x o o a p c} R] e ≈ scoeq_e S) :
  @IsCoequalizer (RMod@{o x a p c} R) A B f g Q e.
Proof.
  assert (L0 : ∀ w, w ≈ cmon_map (rm_hom e)
                          (cmon_map (scoeq_s S) (cmon_map (to i) w))).
  { intros w.
    pose proof (Hi (cmon_map (scoeq_s S) (cmon_map (to i) w))) as H1;
      simpl in H1.
    pose proof (scoeq_law2 S (cmon_map (to i) w)) as L2; simpl in L2.
    pose proof (iso_from_to i w) as FT; simpl in FT.
    pose proof (iso_from_to i (cmon_map (rm_hom e)
                  (cmon_map (scoeq_s S) (cmon_map (to i) w)))) as FT';
      simpl in FT'.
    transitivity (cmon_map (from i) (cmon_map (to i) w));
      [ symmetry; exact FT | ].
    transitivity (cmon_map (from i) (cmon_map (to i) (cmon_map (rm_hom e)
                    (cmon_map (scoeq_s S) (cmon_map (to i) w)))));
      [ | exact FT' ].
    apply (proper_morphism (cmon_map (from i))).
    symmetry.
    transitivity (cmon_map (scoeq_e S)
                    (cmon_map (scoeq_s S) (cmon_map (to i) w)));
      [ exact H1 | exact L2 ]. }
  unshelve refine (@Build_IsCoequalizer _ _ _ _ _ _ _ _ _).
  - exact He.
  - intros W h Hh.
    unshelve eapply Build_Unique.
    + unshelve refine
        (@Build_RModHom R Q W
           (cmon_hom_compose (cmon_hom_compose (rm_hom h) (scoeq_s S))
              (to i)) _).
      intros r w; simpl.
      transitivity
        (cmon_map (rm_hom h) (cmon_map (scoeq_s S) (cmon_map (to i)
           (rm_smul Q r (cmon_map (rm_hom e)
              (cmon_map (scoeq_s S) (cmon_map (to i) w))))))).
      * apply (proper_morphism (cmon_map (rm_hom h))).
        apply (proper_morphism (cmon_map (scoeq_s S))).
        apply (proper_morphism (cmon_map (to i))).
        apply rm_smul_respects; [ reflexivity | exact (L0 w) ].
      * transitivity
          (cmon_map (rm_hom h) (cmon_map (scoeq_s S) (cmon_map (to i)
             (cmon_map (rm_hom e)
                (rm_smul B r (cmon_map (scoeq_s S) (cmon_map (to i) w))))))).
        -- apply (proper_morphism (cmon_map (rm_hom h))).
           apply (proper_morphism (cmon_map (scoeq_s S))).
           apply (proper_morphism (cmon_map (to i))).
           symmetry. apply rm_map_smul.
        -- transitivity
             (cmon_map (rm_hom h) (cmon_map (scoeq_s S) (cmon_map (scoeq_e S)
                (rm_smul B r (cmon_map (scoeq_s S) (cmon_map (to i) w)))))).
           ++ apply (proper_morphism (cmon_map (rm_hom h))).
              apply (proper_morphism (cmon_map (scoeq_s S))).
              exact (Hi _).
           ++ transitivity (cmon_map (rm_hom h)
                 (rm_smul B r (cmon_map (scoeq_s S) (cmon_map (to i) w)))).
              ** exact (rmod_split_absorb f g S (rm_hom h) Hh _).
              ** apply rm_map_smul.
    + intros y; simpl.
      transitivity (cmon_map (rm_hom h)
                      (cmon_map (scoeq_s S) (cmon_map (scoeq_e S) y))).
      * apply (proper_morphism (cmon_map (rm_hom h))).
        apply (proper_morphism (cmon_map (scoeq_s S))).
        exact (Hi y).
      * exact (rmod_split_absorb f g S (rm_hom h) Hh y).
    + intros v Hv w; simpl.
      transitivity (cmon_map (rm_hom v) (cmon_map (rm_hom e)
                      (cmon_map (scoeq_s S) (cmon_map (to i) w)))).
      * symmetry. exact (Hv (cmon_map (scoeq_s S) (cmon_map (to i) w))).
      * apply (proper_morphism (cmon_map (rm_hom v))). symmetry. exact (L0 w).
Defined.

Definition RMod_Forget_Ab_creates_split@{a c p o x} (R : RingObject@{a c p}) :
  CreatesUSplitCoequalizers (RMod_Forget_Ab@{x o o a p c} R).
Proof.
  unshelve refine (@Build_CreatesUSplitCoequalizers _ _ _ _ _).
  - intros A B f g S.
    exists (RModCreated f g S).
    exists (RModCreatedE f g S).
    split.
    + exact (RModCreatedE_is_coeq f g S).
    + exists (@iso_id Ab@{o c} (scoeq_obj S)).
      intros y; simpl. reflexivity.
  - intros A B f g S Q e He i Hi.
    exact (RModReflected_is_coeq f g S Q e He i Hi).
Defined.

(*
 The lift chosen is on the nose: its group IS Z, its action IS
 e (r · s z), its coequalizing arrow IS e and its comparison isomorphism
 IS the identity. 

 --------
 所选择的升降机位于鼻子上：它的群是 Z，它的作用是 e (r · s z)，它的共同等化箭头是 e，它的比较同构是恒等映射。
*)
Example rmod_created_carrier@{a c p o x} {R : RingObject@{a c p}}
  {A B : obj[RMod@{o x a p c} R]} (f g : A ~{RMod@{o x a p c} R}~> B)
  (S : @SplitCoequalizer Ab@{o c} _ _
         (fmap[RMod_Forget_Ab@{x o o a p c} R] f)
         (fmap[RMod_Forget_Ab@{x o o a p c} R] g)) :
  rm_ab (`1 (@create_coeq _ _ _ (RMod_Forget_Ab_creates_split@{a c p o x} R)
               A B f g S)) = scoeq_obj S := eq_refl.

Example rmod_created_action@{a c p o x} {R : RingObject@{a c p}}
  {A B : obj[RMod@{o x a p c} R]} (f g : A ~{RMod@{o x a p c} R}~> B)
  (S : @SplitCoequalizer Ab@{o c} _ _
         (fmap[RMod_Forget_Ab@{x o o a p c} R] f)
         (fmap[RMod_Forget_Ab@{x o o a p c} R] g))
  (r : carrier (rig_setoid (ring_rig R))) (z : carrier (scoeq_obj S)) :
  rm_smul (`1 (@create_coeq _ _ _ (RMod_Forget_Ab_creates_split@{a c p o x} R)
                 A B f g S)) r z
  = cmon_map (scoeq_e S) (rm_smul B r (cmon_map (scoeq_s S) z)) := eq_refl.

Example rmod_created_arrow@{a c p o x} {R : RingObject@{a c p}}
  {A B : obj[RMod@{o x a p c} R]} (f g : A ~{RMod@{o x a p c} R}~> B)
  (S : @SplitCoequalizer Ab@{o c} _ _
         (fmap[RMod_Forget_Ab@{x o o a p c} R] f)
         (fmap[RMod_Forget_Ab@{x o o a p c} R] g)) :
  rm_hom (`1 (`2 (@create_coeq _ _ _
                   (RMod_Forget_Ab_creates_split@{a c p o x} R) A B f g S)))
  = scoeq_e S := eq_refl.

Example rmod_created_iso@{a c p o x} {R : RingObject@{a c p}}
  {A B : obj[RMod@{o x a p c} R]} (f g : A ~{RMod@{o x a p c} R}~> B)
  (S : @SplitCoequalizer Ab@{o c} _ _
         (fmap[RMod_Forget_Ab@{x o o a p c} R] f)
         (fmap[RMod_Forget_Ab@{x o o a p c} R] g)) :
  `1 (snd (`2 (`2 (@create_coeq _ _ _
                     (RMod_Forget_Ab_creates_split@{a c p o x} R)
                     A B f g S))))
  = @iso_id Ab@{o c} (scoeq_obj S) := eq_refl.

(*
 An R-linear map invertible as a group homomorphism is invertible as a
 module map. 

 --------
 作为群同态可逆的 R 线性映射作为模映射也是可逆的。
*)
Definition RMod_Forget_Ab_reflects@{a c p o x} (R : RingObject@{a c p}) :
  ReflectsIsos (RMod_Forget_Ab@{x o o a p c} R) :=
  creates_split_reflects_isos _ (RMod_Forget_Ab_creates_split@{a c p o x} R).

(** ** Beck's route to monadicity / ** 贝克到单子的路径 *)

Definition RMod_beck_equivalence@{a c p o x} (R : RingObject@{a c p}) :
  EquivalenceOfCategories
    (EM_Comparison (zext_adjunction@{a c p o o x a a} R)) :=
  beck_monadicity (zext_adjunction@{a c p o o x a a} R)
    (RMod_Forget_Ab_creates_split@{a c p o x} R).

Definition RMod_Forget_Ab_Monadic_beck@{a c p o x} (R : RingObject@{a c p}) :
  @Monadic@{o x o o o c o a} (RMod@{o x a p c} R) Ab@{o c}
    (RMod_Forget_Ab@{x o o a p c} R).
Proof.
  exists (ZExt@{a c p x o a o c} R).
  exists (zext_adjunction@{a c p o o x a a} R).
  exact (RMod_beck_equivalence@{a c p o x} R).
Defined.

Definition EM_RMod_iso_beck@{a c p o x k} (R : RingObject@{a c p}) :
  @Isomorphism Cat@{k o x o c}
    (RMod@{o x a p c} R)
    (@EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
       (TensorMonad@{a c p o x} R)) :=
  Equivalence_to_Cat_Iso (RMod_beck_equivalence@{a c p o x} R).

(* The Beck Cat iso's [to] leg IS the comparison functor. / Beck Cat iso 的 [to] 腿是比较函子。 *)
Example EM_RMod_iso_beck_to@{a c p o x k} (R : RingObject@{a c p}) :
  to (EM_RMod_iso_beck@{a c p o x k} R)
  = EM_Comparison (zext_adjunction@{a c p o o x a a} R) := eq_refl.

(* The two routes' [to] legs are one term. / 这两条线路的 [to] 段落是一个学期。 *)
Example rmod_beck_direct_to@{a c p o x k} (R : RingObject@{a c p}) :
  to (EM_RMod_iso_beck@{a c p o x k} R) = to (EM_RMod_iso@{a c p o x k} R)
  := eq_refl.

(* Beck's quasi-inverse keeps the carrier and acts through η: r · m = h ((r · 1) ⊗ m). It is ≈ to [EM_to_RMod], by [rig_mul_one_r] in the scalar slot. / 贝克的准逆保持承载并通过 η 起作用： r · m = h ((r · 1) ⊗ m)。它在标量槽中通过 [rig_mul_one_r] 与 [EM_to_RMod] 近似。 *)
Example rmod_beck_carrier@{a c p o x} {R : RingObject@{a c p}}
  (X : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
         (TensorMonad@{a c p o x} R)) :
  rm_ab (fobj[@quasi_inverse _ _ _ (RMod_beck_equivalence@{a c p o x} R)] X)
  = `1 X := eq_refl.

Example rmod_beck_act@{a c p o x} {R : RingObject@{a c p}}
  (X : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
         (TensorMonad@{a c p o x} R))
  (r : carrier (rig_setoid (ring_rig R))) (m : carrier (`1 X)) :
  rm_smul (fobj[@quasi_inverse _ _ _ (RMod_beck_equivalence@{a c p o x} R)] X)
    r m
  = cmon_map (t_alg[`2 X])
      (@ts_gen (ring_ab R) (`1 X)
         (rig_mul (ring_rig R) r (rig_one (ring_rig R))) m) := eq_refl.

Definition rmod_beck_vs_direct_iso@{a c p o x} {R : RingObject@{a c p}}
  (X : @EilenbergMoore@{o o x c} Ab@{o c} (TensorF@{a c p o x} R)
         (TensorMonad@{a c p o x} R)) :
  @Isomorphism (RMod@{o x a p c} R)
    (fobj[@quasi_inverse _ _ _ (RMod_beck_equivalence@{a c p o x} R)] X)
    (fobj[EM_to_RMod@{a c p o x} R] X).
Proof.
  unshelve refine
    (@Build_Isomorphism (RMod@{o x a p c} R) _ _
       (@Build_RModHom R
          (fobj[@quasi_inverse _ _ _ (RMod_beck_equivalence@{a c p o x} R)] X)
          (fobj[EM_to_RMod@{a c p o x} R] X) (@cmon_hom_id (`1 X)) _)
       (@Build_RModHom R (fobj[EM_to_RMod@{a c p o x} R] X)
          (fobj[@quasi_inverse _ _ _ (RMod_beck_equivalence@{a c p o x} R)] X)
          (@cmon_hom_id (`1 X)) _) _ _).
  - intros r m; simpl. apply (proper_morphism (cmon_map (t_alg[`2 X]))).
    apply te_gen; [ exact (rig_mul_one_r (ring_rig R) r) | reflexivity ].
  - intros r m; simpl. apply (proper_morphism (cmon_map (t_alg[`2 X]))).
    apply te_gen; [ symmetry; exact (rig_mul_one_r (ring_rig R) r)
                  | reflexivity ].
  - intros m. reflexivity.
  - intros m. reflexivity.
Defined.

Definition rmod_beck_vs_direct@{a c p o x} (R : RingObject@{a c p}) :
  @quasi_inverse _ _ _ (RMod_beck_equivalence@{a c p o x} R)
  ≈ EM_to_RMod@{a c p o x} R.
Proof.
  exists (fun X => rmod_beck_vs_direct_iso X).
  intros X Y f m; simpl.
  exact (@t_id _ _ _ _ (`2 Y) (cmon_map t_alg_hom[f] m)).
Defined.
