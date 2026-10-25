(* * * U : R-Mod ⟶ Ab creates every colimit: Riehl's Corollary 5.6.10 / * * U : R-Mod ⟶ Ab 创建每一个余极限：Riehl 的推论 5.6.10 *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Limit.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.AbCategory.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Ab.ModFunctor.

Generalizable All Variables.

(*
 Book: Riehl, "Category Theory in Context", 2nd ed., Corollary
 5.6.10, printed p. 212 (PDF p. 232) — riehl:5.6:cor10; with
 her Theorem 5.6.5, printed pp. 210–211 (PDF pp. 230–231),
 Exercise 5.6.ii, printed p. 217, and Definition 3.4.1, printed
 pp. 103–104
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd
 ed., Springer GTM 5, 1998, §V.1, printed pp. 111–112 (PDF
 pp. 120–121), the Definition of creation on printed p. 112
 nLab: https://ncatlab.org/nlab/show/created+limit
 nLab: https://ncatlab.org/nlab/show/monadic+functor
 nLab: https://ncatlab.org/nlab/show/Mod

 Mac Lane defines creation in §V.1.  Having built the limits of groups
 termwise out of the limits of their underlying sets, he says that "each
 forgetful functor 'creates' limits in the sense of the following
 definition" (printed p. 111, PDF p. 120), and the Definition (printed
 p. 112) reads: V : A → X creates limits for F : J → A if
 "(i) To every limiting cone τ" over VF "there is exactly one pair ⟨a, σ⟩
 consisting of an object a ∈ A with Va = x and a cone σ" over F "with
 Vσ = τ, and if, moreover, (ii) This cone" σ "is a limiting cone in A."  "V
 creates colimits" is "the above with the arrows in all cones reversed", and
 he adds that "V creates limits" means only that V produces limits for
 functors F whose composite VF already has a limit.  Riehl's Definition
 3.4.1 (printed pp. 103–104) keeps the conditional and drops the uniqueness:
 F creates the limits of K "if whenever FK has a limit in D, then K has a
 limit as well, in which case a cone over K is a limit cone if and only if
 its image under F is a limit cone", and the definition "dualizes" to
 colimits.  Structure/Limit/Creation.v implements both: [CreatesLimit] is
 Riehl's (a lift, an isomorphism of its image with the given cone, and
 reflection), [StrictlyCreatesLimit] keeps Mac Lane's lift on the nose and
 his clause (ii) and replaces his uniqueness by reflection, and
 [CreatesColimit], [StrictlyCreatesColimit] and [CreatesAllColimits] are the
 same classes read in the opposite categories.

 The algebraic forgetful functors to Set create limits and, as a rule, no
 colimits: the free product of groups is not the disjoint union of their
 sets, and Riehl records, right after the corollary this file proves, that
 U : Group → Set "does not preserve (and so, in particular, does not create)
 coproducts" (printed p. 212).  One level up the answer changes.  Her
 Corollary 5.6.10 (printed p. 212, PDF p. 232) states, in this header's
 paraphrase, that the forgetful functor U : _R Mod → Ab creates every
 colimit that Ab has.  Her proof is monadic.  U is monadic with monad
 R ⊗_ℤ − (her Example 5.5.7(i)); "By Example 4.4.15, for any pair of abelian
 groups A and B, there is a natural isomorphism" involving "the abelian
 group Hom_ℤ(R, B) of group homomorphisms R → B", so that the monad "has a
 right adjoint Hom_ℤ(R, −)" (the sibling's header records how the display
 reads); "By Theorem 4.6.2, R ⊗_ℤ − preserves all colimits and so Theorem
 5.6.5(ii) applies to all diagrams in Ab".  That theorem (printed p. 210)
 reads "A monadic functor U : A → C creates (i) any limits that C has, and
 (ii) any colimits that C has and the monad and its square preserve".  Her
 proof of clause (ii) is a sketch on printed p. 211 — the structure map on
 the nadir "is induced by the universal property of the colimit cone under T
 U^T D with nadir TL" — and Exercise 5.6.ii (printed p. 217) reads "Prove
 Theorem 5.6.5(ii)".

 TWO ROUTES, AND WHICH ONE THIS FILE TAKES.  The tree has every piece of
 Riehl's route but its last.  The monad and the monadicity are
 Instance/Mod/TensorMonad.v's; the tensor–hom adjunction and the
 cocontinuity of the monad and of its square are the sibling
 Instance/Mod/TensorMonad/Cocontinuous.v; the step they feed, her Theorem
 5.6.5(ii) at an Eilenberg–Moore forgetful functor, is issue #1008, OPEN,
 and no [CreatesColimit] at [EM_Forget] exists.  This file therefore proves
 the corollary DIRECTLY, as the colimit dual of Instance/Mod/Limit.v's
 creation of limits, and never mentions the monad: it imports neither
 TensorMonad file, and its closure is 68 files where the sibling's is 82,
 each counting the file itself.  What the monadic route adds, and what a
 follow-up must do to finish it, is recorded in the sibling's header.

 THE CREATED ACTION IS A MEDIATOR.  Let N be a colimiting cocone in Ab under
 U ◯ K — in the tree, a limiting cone in Ab^op over (RMod_Forget_Ab
 R)^op ◯ K^op, whose legs are the insertions ι_i : U (K i) → N.  For a fixed
 scalar r the family i ↦ ι_i ∘ (r ·) is again a cocone in Ab
 ([mcol_smul_cone]): each r · on K i is a homomorphism of groups
 (Instance/Ab/ModFunctor.v's [module_act], unital by Instance/Mod.v's
 [rm_smul_zero_r], additive by [rm_smul_distr_l]; importing it costs one
 file of closure, that file) and the family is coherent because the arrows
 of K are R-linear ([rm_map_smul]).  Its mediator out of the nadir,
 [mcol_smul_map], IS the created action ([mcol_smul],
 [mcol_smul_is_mediator]), and the defining triangle is
 ρ_r (ι_i m) ≈ ι_i (r · m) ([mcol_smul_triangle]).  Being a morphism of
 Ab, the mediator is additive in the vector for nothing:
 [mcol_smul_distr_l] is [cmon_map_plus], one citation.

 THE ENGINE IS JOINT EPIMORPHICITY, FROM UNIQUENESS ALONE.  [mcol_ext] says
 that two Ab maps u, v out of the nadir that agree after every insertion are
 ≈: both are mediators of the one cocone i ↦ v ∘ ι_i, so the uniqueness
 clause of the colimit identifies them.  No elementwise description of the
 colimit is needed, and none exists in the tree.  Here the dual departs from
 its template: Instance/Mod/Limit.v's [mlim_ext] cannot probe its apex with
 constant maps, which are not homomorphisms, and transports the limit to
 Sets to use [absets_limit_ext]; a colimit is tested by maps OUT of its
 nadir, which are homomorphisms already.  The other four module laws are
 each one application of [mcol_ext]: respectfulness in the scalar
 ([mcol_smul_respects]), distributivity over scalars against
 Structure/AbCategory.v's pointwise sum [ab_hom_add] ([mcol_smul_distr_r]),
 associativity against the composite ([mcol_smul_assoc]) and the unit law
 against the identity ([mcol_smul_one]).  [ColimMod] is the module,
 [mcol_hom] the insertions made R-linear, [mcol_cone] the cocone of modules.

 REFLECTION AND THE LIMITING CLAUSE ARE ONE LEMMA.  [mcol_reflect]: a cocone
 of modules whose underlying cocone is colimiting in Ab is colimiting in
 RMod R.  The mediator into another cocone P is the Ab mediator m of the
 underlying cocones; it is R-linear because, for each r, m ∘ (r ·) and (r
 ·) ∘ m agree after every insertion, which is [mcol_ext] once more; its
 uniqueness is the Ab uniqueness.  The created cocone is colimiting by the
 same lemma, since its image in Ab IS N as far as the colimit predicate can
 see: [IsLimitCone] reads a cone's vertex and legs only, never its coherence
 proof.

 PACKAGING.  [mcol_strict_lift] is Structure/Limit/Creation.v's [StrictLift]
 with [slift_eq] closed by [eq_refl] and the legs by [reflexivity]; then
 [RMod_Forget_Ab_StrictlyCreatesColimit], [RMod_Forget_Ab_CreatesColimit]
 through [StrictlyCreatesLimit_CreatesLimit], and
 [RMod_Forget_Ab_creates_colimits : CreatesAllColimits (RMod_Forget_Ab R)],
 Riehl's corollary: its scope, every colimit that Ab has (this header's
 paraphrase of her words, as above), is the class's quantification over
 every shape and diagram with the colimiting cocone in Ab as the
 hypothesis.  Every record over an opposite category is built by
 its explicit constructor with the category named — [@Build_Cone],
 [@Build_ACone], [@Build_Unique], [@Build_StrictLift],
 [@Build_StrictlyCreatesLimit] — never by the [{| |}] builder, which can
 infer the record's category from the first field typed in C^op and mistype
 the rest.  By `grep -lw` for the three colimit classes over the files of
 _CoqProject, five other files name them and none inhabits one:
 Structure/Limit/Creation.v defines them and consumes them as hypotheses,
 Construction/Reflective/Colimit.v, Monad/Eilenberg/Moore/Limit.v and this
 file's sibling Instance/Mod/TensorMonad/Cocontinuous.v mention them in
 comments, and Test/ProbeReflectiveColimit434.v refuses one.  So
 these are the tree's first inhabitants of [StrictlyCreatesColimit],
 [CreatesColimit] and [CreatesAllColimits].

 UNIQUENESS, AT THE STRENGTH THE SETTING SUPPORTS.  Mac Lane's clause (i)
 asks for exactly one lift.  The lift's group is forced — it IS the nadir —
 and its action is unique up to ≈ ([mcol_smul_unique]: any family of Ab
 endomorphisms making every insertion R-linear is ≈ the created action), the
 form uniqueness of an action takes when elements are compared by a setoid's
 ≈.  At [eq_refl] it is refused: two colimit witnesses of one cocone give
 two module terms, not convertible, whose actions agree up to ≈
 ([mcol_smul_unique]; C3 of Test/ProbeTensorMonad465.v).
 [creates_lift_unique] of Structure/Limit/Creation.v gives the canonical
 isomorphism between any two lifts.

 GENERALITY, MEASURED.  The ring is any [RingObject@{a c p}]: commutativity
 is never asked for, Mac Lane's and Riehl's modules being left modules over
 a ring.  The shape [J : Category@{j c c}] has its object universe j FREE,
 bounded only through the colimit predicate (j <= l0 <= l).  The limit side
 is narrower in the shape: About on Instance/Mod/Limit.v's
 [RMod_Forget_Ab_CreatesLimit] prints the block equations u0 = u2 and
 u0 = u3.  The shape's hom universe is the ring's carrier universe there as
 here, the creation classes pinning it; its object universe is too, which
 that file's header traces to [Ab_Complete] through its transport of the
 limit to Sets.  The sibling's tensor–hom premises hold only at
 [RingObject@{c c c}].

 A WITNESS.  The theorem is unconditional but consumes a colimit in Ab, and
 the tree has no cocompleteness of Ab (Instance/Ab/DirectedColimit.v records
 the absence).  Over any shape with a terminal object, though,
 Structure/Limit/Initial.v's [terminal_Colimit] is a colimit of any diagram
 in any category, and [rmod_terminal_colimit] lifts it: its group IS U (K 1)
 and its action at r and m IS K(!)(r · m), both by [eq_refl]
 ([rmod_terminal_group], [rmod_terminal_smul]), and the action is ≈ K 1's
 own ([rmod_terminal_smul_own]).  The precedent is
 Construction/Reflective/Colimit.v's [reflective_terminal_shape_colimit];
 the price is 10 files of closure, Structure/Limit/Initial.v's, measured by
 dropping its Require (the closure falls from 68 files to 58).

 STRENGTHS.  By [eq_refl]: the lift's group is the nadir ([mcol_over_obj])
 and its insertions are the given legs ([mcol_over_legs]); the created
 action IS the mediator ([mcol_smul_is_mediator]); the colimit read back
 through [creates_colimit_lift] has the given nadir as its group and the
 given legs as its insertions ([mcol_lift_apex], [mcol_lift_legs]), and the
 whole lifted module IS [ColimMod] of that colimit read in the opposite
 category ([mcol_lift_module]); the reflected mediator's group map IS the
 Ab mediator of the underlying cocones ([mcol_reflect_mediator]); the
 witness's group and action ([rmod_terminal_group], [rmod_terminal_smul]).
 At ≈ only: the action on an inserted element ([mcol_smul_triangle]), the
 uniqueness of the action ([mcol_smul_unique]), and the witness's action
 against K 1's ([rmod_terminal_smul_own]).  Refused by conversion, each
 pinned in Test/ProbeTensorMonad465.v beside the positive half that stands:
 the action on an inserted element at [eq_refl] (C1), the module reflected
 from a cocone M of modules as M itself (C2), the modules of two colimit
 witnesses of one cocone as one (C3), and the witness's action as K 1's own
 (C4).

 WHY THEY ARE REFUSED.  Not by opacity.  In a copy of this file, its
 sibling, Instance/Mod/TensorMonad.v and their joint closure of 95 files,
 with every [Qed] made [Defined] (Instance/Sets.v too, which flips once
 [setoid_morphism_compose_respects] and its one use are given explicit
 universes), [Transparent Obligations] set and [abstract] made
 [transparent_abstract] — Structure/Cartesian/Closed.v, where that change
 is itself refused, keeping its [Qed]s, and Structure/Limit/Preservation.v's
 [preserves_colimit] given bullets that tolerate the goals the added
 transparency closes — and with the three files' universe annotations
 dropped, all four stand, each stripped copy stopping with "cannot unify"
 inside its command, and every control holds.  There
 [Print Opaque Dependencies] on [ColimMod], [mcol_reflect],
 [rmod_terminal_colimit], [RMod_Forget_Ab_CreatesColimit] and
 [mcol_smul_triangle], with the sibling's [TensorF_left_adjoint],
 [EM_Comparison], [EM_Forget] and [RMod_Forget_Ab], lists 13 constants, all
 of them Corelib's lemmas of generalized rewriting, where this tree lists
 190; no constant of Structure/Cartesian/Closed.v is among them in either.
 CORRECTION (#1347): this tree lists 187 since #1347, whose properness fields
 as terms take Corelib's [subrelation_id_proper], [proper_proper_proxy] and
 [CMorphisms.compose_proper_obligation_1] out of the census.
 C1 and C3 compare the mediator [unique_obj (HN P)], a projection out of a
 VARIABLE colimit witness, with a leg or with another witness's; C2
 compares it with the action field of a variable module M; C4 compares K(!)
 at a variable functor and terminal object with the identity.

 TRANSPARENCY, MEASURED.  Counted by token (grep -o on each keyword with its
 closing period, which keeps this sentence out of the count), 9 [Qed] and 3
 [Defined].  All three are load-bearing, each shown so by making it [Qed]
 in a copy of the whole file: [mcol_smul_cone] opaque stops
 [mcol_smul_map], whose mediator must see the cocone's vertex as N's;
 [mcol_cone] opaque stops [mcol_strict_lift]'s [eq_refl]; and
 [mcol_reflect] opaque stops the readback [mcol_reflect_mediator], which
 pins that the reflected mediator computes, the reason it is kept
 transparent, as Instance/Mod/Limit.v keeps [rmod_reflects].

 UNIVERSES, read off [About] on all 30 constants.  Every constant binds
 R : RingObject@{a c p} (roles auxiliary, carrier, proof), Ab@{o c} and
 RMod@{o x a p c}.  [mcol_smul_cone] adds the shape's object universe j; the
 constants that take a colimit witness add j and the colimit predicate's l
 and l0 ([IsLimitCone@{l l0 j c o}]); and [RMod_Forget_Ab_creates_colimits]
 binds t (the class's own level) and s (the shape's objects) instead of j.
 The strict bounds are Set < o, c < o and c < x everywhere, with c < t and
 s < t on [RMod_Forget_Ab_creates_colimits]; the rest are a <= o, c <= a,
 p <= a and the chain c, o, j <= l, c, j <= l0 <= l, with o, l <= t and
 s <= l0 on [RMod_Forget_Ab_creates_colimits].  There is no equation and no
 other [Set].  First carriers, by [About] on the donors: Set < o and c < o,
 Instance/Ab.v's [Ab@{u p}] (Set < u, p < u); c < x and a <= o,
 Instance/Mod.v's [RMod] (u3 < u0, u1 <= u); c <= a and p <= a, [RingObject]
 (u0 <= u, u1 <= u); c < t and s < t, Structure/Limit/Creation.v's
 [CreatesAllColimits] (u7 < u, u5 < u); the l chain,
 Structure/Limit/Preservation.v's [IsLimitCone].  Two donors carry levels
 outside their statements, and each such level is pinned:
 [cone_leg_coh@{u u0 u1 u2 u3 u4}]'s u3, which neither its type nor its
 block mentions, and [terminal_Colimit@{u u0 u1 u2 u3 u4}]'s u4, bounded
 only from below.  Made a placeholder in a copy of the whole file, each is
 refused with "Universe ... is unbound"; [cone_leg_coh]'s u4, also bounded
 only from below, compiles as a placeholder and is written c with the rest
 ([cone_leg_coh@{j c o c c c}], [terminal_Colimit@{j c o c l0 l}]).  The
 stdlib caps are inherited, each placed by [About] on every constant of its
 donor's dependency cone, as [Print All Dependencies] lists it, at its
 topmost carrier: compose and ID on Instance/Sets.v's
 [setoid_morphism_compose] and [setoid_morphism_id], through
 Instance/CMon.v's [cmon_hom_compose] and [cmon_hom_id] and so through
 [Ab]; prod_rect on Instance/Ab.v's [ab_cancel_l], a setoid rewrite,
 through Instance/Mod.v's [rm_smul_zero_r] and [module_act]; Projections
 (the sigma projections) on Structure/Limit/Preservation.v's
 cone-isomorphism calculus ([coneiso_from]), through
 [creates_colimit_lift].

 NOT DELIVERED.  Riehl's own proof: this file does not go through the monad,
 and her Theorem 5.6.5(ii) is not in the tree (issue #1008; the sibling's
 header lists what finishing that route takes).  No [Cocomplete (RMod R)]
 follows from this file, the tree having no [Cocomplete Ab];
 [creates_colimits_Cocomplete] would give it from one.  No comparison of the
 created colimits with Instance/Mod/Colimit.v's, obtained from the adjoint
 functor theorem, or with Instance/Mod/Coproduct.v's direct sum.  No
 preservation or reflection corollary is restated
 ([creation_preserves_colimit] and [creates_reflects_limits] apply as they
 stand).  No uniqueness of the lift at [eq_refl] (C3).  No witness at a
 shape without a terminal object: the tree has no [Colimit] in Ab of a
 discrete or parallel diagram (Instance/Ab/Coproduct.v's [Ab_Biproduct] is a
 biproduct, and no bridge to a [Colimit] over a discrete shape is built),
 and its one other [Colimit] in Ab, Instance/Ab/DirectedColimit.v's
 [ab_fg_Colimit], is over the finitely generated subgroups of a group,
 not the image of a diagram of modules.
 No right modules, and nothing registered as an [Instance]. 

 --------
 书籍：Riehl，《上下文中的范畴论》，第2版，推论5.6.10，印刷页212（PDF第232页）——riehl:5.6:cor10；以及她的定理5.6.5，印刷页210–211（PDF第230–231页），练习5.6.ii，印刷页217，和定义3.4.1，印刷页103–104
 书籍：Mac Lane，《面向工作数学家的范畴论》，第2版，Springer GTM 5，1998，§V.1，印刷页111–112（PDF第120–121页），关于创建的定义见印刷页112
 nLab：https://ncatlab.org/nlab/show/created+limit
 nLab：https://ncatlab.org/nlab/show/monadic+functor
 nLab：https://ncatlab.org/nlab/show/ModMac Lane 在 §V.1 中定义了创造。建立了群的极限逐项取自其基础集合的极限之后，他说“每个遗忘函子‘创造’极限，其意义如下定义”（印刷版第111页，PDF 第120页），定义（印刷版第112页）如下：V : A → X 为 F : J → A 创造极限，如果“(i) 对 VF 上的每个极限锥 τ，恰好存在一对 ⟨a, σ⟩，其中对象 a ∈ A 且 Va = x，并且 σ 是 F 上的锥，使 Vσ = τ，并且如果，还有 (ii) 这个锥 σ 是 A 中的极限锥。” “V 创造余极限”就是“上述定义中将所有锥中的箭头反向”，并且他补充说“V 创造极限”仅意味着 V 为那些复合 VF 已经存在极限的函子 F 产生极限。Riehl 的定义 3.4.1（印刷版第103–104）保留条件，但去掉唯一性：
 F 创建 K 的极限“如果每当 FK 在 D 中有极限时，K 也有极限，在这种情况下，K 上的锥是极限锥当且仅当其在 F 下的像是极限锥”，并且定义“对偶化”到余极限。Structure/Limit/Creation.v 实现了两者：[CreatesLimit] 是 Riehl 的（一个提升，一个其像与给定锥的同构，以及反射），[StrictlyCreatesLimit] 精确保留 Mac Lane 的提升及其条款 (ii) 并用反射替代其唯一性，[CreatesColimit]、[StrictlyCreatesColimit] 和 [CreatesAllColimits] 是同一类在对偶范畴中的表述。代数的遗忘函子到集合创建极限，但通常不创建余极限：群的自由积并不是它们集合的并集，而Riehl在这份文件证明的推论之后记录说，U : Group → Set "不保持（因此特别地，不创建）余积"（印刷页 212）。在更高一层的答案会有所不同。她的推论 5.6.10（印刷页 212，PDF 页 232）用本标题的意译表示，遗忘函子 U : _R Mod → Ab 创建 Ab 所有的余极限。她的证明是单体的。U 是与单子 R ⊗_ℤ − 单子主义的（她的例子 5.5.7(i)）；“根据例子 4.4.15，对于任意一对阿贝尔群 A 和 B，存在一个自然同构”涉及“从 R 到 B 的群同态组成的阿贝尔群 Hom_ℤ(R, B)”，因此该单子“有一个右伴随 Hom_ℤ(R, −)”（相关标题记录了显示方式）；“根据定理 4.6.2，R ⊗_ℤ − 保留所有余极限，所以定理 5.6.5(ii) 对 Ab 中的所有图都适用。”该定理（印刷页 210）写道：“一个单子函子 U: A → C 创建 (i) C 中存在的任意极限，以及 (ii) C 中存在的任意余极限，且单子及其平方保持它们。”她对条款 (ii) 的证明在印刷页 211 是一个草图——底点上的结构映射“由余极锥在 T U^T D 下的普遍性质以及底点 TL 引出”——以及练习 5.6.ii（印刷页）。217）写着“证明 定理 5.6.5(ii)”.两条路线，以及这个文件采用哪一条。该树包含 Riehl 路线的所有部分，除了最后一部分。Monad 和 monadicity 属于 Instance/Mod/TensorMonad.v；tensor–hom 对偶和 monad 及其平方的余连续性属于其兄弟文件 Instance/Mod/TensorMonad/Cocontinuous.v；它们所提供的步骤，即她在 Eilenberg–Moore 遗忘函子上的定理 5.6.5(ii)，是问题 #1008，状态为打开，并且在 [CreatesColimit] 到 [EM_Forget] 之间不存在解决方案。因此，这个文件直接证明了推论，作为 Instance/Mod/Limit.v 创建极限的余极限对偶，并且从未提到 monad：它不导入任何 TensorMonad 文件，其闭包为 68 个文件，而兄弟文件的闭包为 82 个文件，每个文件都包括自身。单子路径所增加的内容，以及后续操作必须完成的内容，都记录在兄弟节点的头信息中。创建的作用是一个中介物。设 N 是 Ab 下的 U ◯ K 的余极限锥——在树中，是 Ab^op 上 (RMod_Forget_Ab R)^op ◯ K^op 的极限锥，其各条腿为插入 ι_i: U(K i) → N。对于固定的标量 r，族 i ↦ ι_i ∘ (r ·) 再次构成 Ab 中的余锥 ([mcol_smul_cone])：K i 上的每个 r · 是群同态（Instance/Ab/ModFunctor.v 的 [module_act]，通过 Instance/Mod.v 的 [rm_smul_zero_r] 是幺元性的，通过 [rm_smul_distr_l] 是加法性的；导入它需一个闭包文件，该文件），且该族是一致的，因为 K 的箭头是 R-线性的 ([rm_map_smul])。其从底点出的中介物 [mcol_smul_map]，就是创建的作用 ([mcol_smul], [mcol_smul_is_mediator])，定义三角形为 ρ_r(ι_i m) ≈ ι_i (r · m) ([mcol_smul_triangle])。作为 Ab 的态射，仲介在向量中是无缘无故可加的：[mcol_smul_distr_l] 是 [cmon_map_plus]，一个引用。引擎是联合上同态性，仅由唯一性决定。[mcol_ext] 说两个从最低点出的 Ab 映射 u, v 在每次插入后都一致时是≈的：它们都是统一余锥 i ↦ v ∘ ι_i 的中介，因此余极限的唯一性条款将它们识别。无需对余极限进行元素级描述，并且在树中也不存在。这里对偶偏离了其模板：Instance/Mod/Limit.v 的 [mlim_ext] 无法用常映射探测其顶点，这些映射不是同态，并将极限传送到 Sets 中以使用 [absets_limit_ext]；余极限通过从其最低点出的映射来测试，这些映射已经是同态。其他四条模律分别是 [mcol_ext] 的每一个应用：标量中的尊重性（[mcol_smul_respects]）、对 Structure/AbCategory.v 点态和的标量分配律 [ab_hom_add]（[mcol_smul_distr_r]）、对复合的结合律（[mcol_smul_assoc]）以及对单位的单位律（[mcol_smul_one]）。[ColimMod] 是模，[mcol_hom] 是使插入保持 R 线性的操作，[mcol_cone] 是模的余锥。反射和限制子句是一个引理。[mcol_reflect]：一个模的余锥，如果其底层余锥在 Ab 中是余极限的，则在 RMod R 中也是余极限的。到另一个余锥 P 的中介是底层余锥在 Ab 中的中介 m；它是 R 线性的，因为对于每个 r，m ∘ (r ·) 和 (r ·) ∘ m 在每次插入后都相同，这再次是 [mcol_ext]；它的唯一性是 Ab 中的唯一性。所创建的余锥是余极限的，根据同一个引理，因为在 Ab 中看到的其像在余极限谓词上是 N：[IsLimitCone] 仅读取锥的顶点和腿，从不读取其相干性证明。PACKAGING。[mcol_strict_lift]是Structure/Limit/Creation.v的版权[StrictLift]
 其中[slift_eq]闭合[eq_refl]，腿闭合[reflexivity];则
 [RMod_Forget_Ab_StrictlyCreatesColimit]，[RMod_Forget_Ab_CreatesColimit]
 通过[StrictlyCreatesLimit_CreatesLimit]，且
 [RMod_Forget_Ab_creates_colimits : CreatesAllColimits (RMod_Forget_Ab R)]，
 Riehl的推论：它的作用域，即Ab的每一个余极限（此头部的
 如上所述，是该类对 的量化
 每个形状和图，Ab中共极限的cocone为
 假设。每个对立范畴上的记录由
 其显式构造子，范畴名为 — [@Build_Cone]，
 [@Build_ACone]，[@Build_Unique]，[@Build_StrictLift]，
 [@Build_StrictlyCreatesLimit]——绝不是由[{| |}]建造者决定的，而该厂商可以
 从输入的第一个字段推断记录的类别，输入错误
 剩下的。作者 `grep -lw` 对 _CoqProject 文件中的三个余极限类进行操作，另外五个文件命名了它们，但没有一个实例化它们：Structure/Limit/Creation.v 定义了它们并将其作为假设使用，Construction/Reflective/Colimit.v、Monad/Eilenberg/Moore/Limit.v 以及本文件的兄弟文件 Instance/Mod/TensorMonad/Cocontinuous.v 在注释中提到它们，而 Test/ProbeReflectiveColimit434.v 拒绝其中之一。因此，这些是 [StrictlyCreatesColimit]、[CreatesColimit] 和 [CreatesAllColimits] 的树的首批实例。在设定支持的强度下的唯一性。Mac Lane 的条款(i)要求恰好一个提升。提升的群是强制的——它就是极小值——并且它的作用在≈（[mcol_smul_unique]：任何使每个插入都是R-线性的Ab自同态族）下是唯一的，这是在通过集合等价关系≈比较元素时动作所体现的形式唯一性。在[eq_refl]处它被拒绝：一个余圆锥的两个余极限证据给出了两个不可转换的模项，它们的作用在≈下是一致的（[mcol_smul_unique]；Test/ProbeTensorMonad465.v 的C3）。Structure/Limit/Creation.v 的[creates_lift_unique]给出了任意两个提升之间的典范同构。一般性，有度量。这个环是任意的 [RingObject@{a c p}]：交换性从未被要求，因为 Mac Lane 和 Riehl 的模都是环的左模。形状 [J : Category@{j c c}] 的对象宇宙是 j FREE，仅通过余极限谓词（j <= l0 <= l）来限定。形状的极限侧更窄：关于 Instance/Mod/Limit.v 的 [RMod_Forget_Ab_CreatesLimit] 打印块方程 u0 = u2 和 u0 = u3。形状的同对象宇宙是环的承载宇宙，和这里一样，由创建类固定；它的对象宇宙也是如此，该文件的头部通过将极限传输到集合追踪到 [Ab_Complete]。兄弟节点的张量–同前提仅在 [RingObject@{c c c}] 上成立。证据。该定理是无条件的，但在 Ab 中使用了一个余极限，并且该树没有 Ab 的余完备性（Instance/Ab/DirectedColimit.v 记录了其不存在）。不过，对于任何具有终对象的形状，Structure/Limit/Initial.v 的 [terminal_Colimit] 是任何范畴中任意图的余极限，并且 [rmod_terminal_colimit] 对其进行了提升：它的群是 U (K 1)，其在 r 和 m 上的作用是 K(!)(r · m)，两者均由 [eq_refl]（[rmod_terminal_group], [rmod_terminal_smul]）定义，并且该作用近似于 K 1 自身的作用（[rmod_terminal_smul_own]）。先例是 Construction/Reflective/Colimit.v 的 [reflective_terminal_shape_colimit]；代价是 10 个闭包文件，Structure/Limit/Initial.v 测量的方法是删除其 Require（闭包从 68 个文件减少到 58 个）。优势。由 [eq_refl] 提出：提升的群是最低点（[mcol_over_obj]），其插入是给定的腿（[mcol_over_legs]）；创建的作用是中介（[mcol_smul_is_mediator]）；通过 [creates_colimit_lift] 回读的余极限，其群是给定的最低点，插入是给定的腿（[mcol_lift_apex]，[mcol_lift_legs]），整个提升模块是 [ColimMod]，在相反范畴中读取该余极限（[mcol_lift_module]）；反射中介的群映射是基础上余圆锥的 Ab 中介（[mcol_reflect_mediator]）；见证的群和作用（[rmod_terminal_group]，[rmod_terminal_smul]）。仅在≈时：作用于一个插入元素的作用（[mcol_smul_triangle]）、作用的唯一性（[mcol_smul_unique]）以及见证对 K1 的作用（[rmod_terminal_smul_own]）。被转换拒绝，每个都固定在 Test/ProbeTensorMonad465.v 中，靠近立着的正半边：插入元素在 [eq_refl] (C1) 上的动作，从模的半锥 M 映射的模作为 M 本身 (C2)，一个半锥的两个余极限见证的模作为一个 (C3)，以及见证的动作作为 K 1 自身的 (C4)。他们被拒绝的原因。不是由于不透明。在这个文件的一个副本中，其同级文件 Instance/Mod/TensorMonad.v 以及它们共同闭包的 95 个文件中，每个 [Qed] 都变成了 [Defined]（Instance/Sets.v 也是如此，它在给出 [setoid_morphism_compose_respects] 及其一次使用的显式宇宙后切换一次），[Transparent Obligations] 已设置并且 [abstract] 变成了 [transparent_abstract] —— Structure/Cartesian/Closed.v，其中该更改本身被拒绝，保留其 [Qed]，Structure/Limit/Preservation.v 的 [preserves_colimit] 给出了允许增加透明性闭合目标的子弹点 —— 并且在删除三个文件的宇宙注释后，四个文件仍然存在，每个剥离的副本在其命令内部以“无法统一”停止，并且每个控制都成立。有
 [Print Opaque Dependencies] 在 [ColimMod]、[mcol_reflect]、
 [rmod_terminal_colimit]、[RMod_Forget_Ab_CreatesColimit] 和 [mcol_smul_triangle]，其中有兄弟的 [TensorF_left_adjoint]、
 [EM_Comparison]、[EM_Forget] 和 [RMod_Forget_Ab]，列出了 13 个常量，全部是 Corelib 的广义重写引理，而这个树列出了 190 个；Structure/Cartesian/Closed.v 的常量在两者中都不包含。更正（#1347）：自 #1347 起，这棵树列出了 187 个，因为其适当性字段作为项将 Corelib 的 [subrelation_id_proper]、[proper_proper_proxy] 和 [CMorphisms.compose_proper_obligation_1] 从统计中移除。C1 和 C3 将中介 [unique_obj (HN P)]（一个 VARIABLE 上极限投影的投影）与一条分支或另一个见证进行比较；C2 将其与变量模块 M 的作用字段进行比较；C4 将 K(!) 在变量函子和终对象上的作用与恒等映射进行比较。透明度，可衡量。按标记计数（使用 grep -o 对每个关键字及其结束句号进行计数，这会使本句不计入统计），9 个 [Qed] 和 3 个 [Defined]。三者都是承重的，每个都通过在整个文件的副本中将其设置为 [Qed] 来显示：[mcol_smul_cone] 不透明停顿 [mcol_smul_map]，其调解者必须将余锥的顶点视为 N 的；[mcol_cone] 不透明停顿 [mcol_strict_lift] 的 [eq_refl]；以及 [mcol_reflect] 不透明停顿读取回 [mcol_reflect_mediator]，它确定反射调解者的计算，这是它保持透明的原因，就像 Instance/Mod/Limit.v 保持 [rmod_reflects] 一样。宇宙，在所有30个常量上读取 [About]。每个常量绑定 R : RingObject@{a c p}（角色：辅助、承载、证明）、Ab@{o c} 和 RMod@{o x a p c}。[mcol_smul_cone] 添加了形状的对象宇宙 j；接受余极限证人的常量添加 j 以及余极限谓词的 l 和 l0（[IsLimitCone@{l l0 j c o}]）；而 [RMod_Forget_Ab_creates_colimits] 绑定 t（类自身的层次）和 s（形状的对象）而非 j。严格的界限在所有地方是 Set < o, c < o 且 c < x，在 [RMod_Forget_Ab_creates_colimits] 上是 c < t 且 s < t；其余的是 a <= o, c <= a, p <= a 以及链 c, o, j <= l, c, j <= l0 <= l，在 [RMod_Forget_Ab_creates_colimits] 上是 o, l <= t 和 s <= l0。没有方程，也没有其他 [Set]。首先是载体，由 [About] 在捐赠者上：设置 < o 和 c < o，
 实例/Ab.v 的 [Ab@{u p}]（设置 < u, p < u）；c < x 且 a <= o，
 实例/Mod.v 的 [RMod]（u3 < u0, u1 <= u）；c <= a 且 p <= a，[RingObject]
 （u0 <= u, u1 <= u）；c < t 且 s < t，结构/限制/创建.v 的
 [CreatesAllColimits]（u7 < u, u5 < u）；l 链，
 结构/限制/保持.v 的 [IsLimitCone]。两个捐赠者携带超出其声明的等级，且每个等级都被固定：
 [cone_leg_coh@{u u0 u1 u2 u3 u4}] 的 u3，其类型或其区块都未提及，及 [terminal_Colimit@{u u0 u1 u2 u3 u4}] 的 u4，仅有下界限制。在整个文件的副本中作为占位符，均被拒绝，显示“Universe ... is unbound”；[cone_leg_coh] 的 u4，同样仅有下界限制，作为占位符可编译，并与其余部分 ([cone_leg_coh@{j c o c c c}]，[terminal_Colimit@{j c o c l0 l}]) 一起写成 c。stdlib 的上限是继承的，每个都由 [About] 放置在其捐赠者依赖锥的每个常数上，如 [Print All Dependencies] 在其最顶层载体上列出：在 Instance/Sets.v 的 [setoid_morphism_compose] 和 [setoid_morphism_id] 上组成和 ID，通过 Instance/CMon.v 的 [cmon_hom_compose] 和 [cmon_hom_id] 并通过 [Ab]；在 Instance/Ab.v 的 [ab_cancel_l] 上的 prod_rect，一个集合等价重写，通过 Instance/Mod.v 的 [rm_smul_zero_r] 和 [module_act]；在 Structure/Limit/Preservation.v 的锥同构演算 ([coneiso_from]) 上的投影 (sigma 投影)，通过 [creates_colimit_lift]。未被交付。Riehl 自己的证明：该文件不经过单子，
 她的定理5.6.5（ii）不在家谱中（issue #1008;兄弟定理的
 头条列出了完成该路线所需的条件）。没有[Cocomplete (RMod R)]
 由此文件推导出，树没有[Cocomplete Ab];
 [creates_colimits_Cocomplete]会从一个那里给出。没有
 与 Instance/Mod/Colimit.v 创建了伴极限，这些共极限来自伴随
 函子定理，或者用 Instance/Mod/Coproduct.v 的直和。不
 保持或反射推论被重新表述
 （[creation_preserves_colimit]和[creates_reflects_limits] 按他们的方式应用
 站立）。[eq_refl]（C3）处的举重无唯一性。在没有终端对象的形状上没有见证者：树在离散或平行图中的 Ab 中没有 [Colimit]（Instance/Ab/Coproduct.v 的 [Ab_Biproduct] 是一个双积，并且没有建立到离散形状上的 [Colimit] 的桥），以及其在 Ab 中的另一个 [Colimit]（Instance/Ab/DirectedColimit.v 的 [ab_fg_Colimit]）是在一个群的有限生成子群上，而不是模块图像上。没有右模块，并且没有注册为 [Instance] 的东西。
*)

(* * ** Joint epimorphicity of a colimiting cocone / * ** 余极圆锥的联合上同态性 *)

(*
 Two maps out of the nadir that agree after every insertion are ≈: both
 mediate the cocone i ↦ v ∘ ι_i. 

 --------
 在每次插入后都一致的两个从最低点出的映射大约是相等的：它们都调解余锥 i ↦ v ∘ ι_i。
*)

Lemma mcol_ext@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  {W : obj[Ab@{o c}]} (u v : vertex_obj[N] ~{Ab@{o c}}~> W)
  (H : ∀ (i : J) (m : carrier (rm_ab (K i))),
         cmon_map u (cmon_map (cone_leg N i) m)
           ≈ cmon_map v (cmon_map (cone_leg N i) m)) :
  u ≈ v.
Proof.
  unshelve eset (P := @Build_Cone (J^op) (Ab@{o c}^op)
    ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op) W
    (@Build_ACone (J^op) (Ab@{o c}^op) W _
       (fun i => v ∘[Ab@{o c}] cone_leg N i) _)).
  - intros x y f m; simpl.
    exact (proper_morphism (cmon_map v) _ _
             (cone_leg_coh@{j c o c c c} N f m)).
  - transitivity (unique_obj (HN P)).
    + symmetry. apply (uniqueness (HN P)).
      intros i m. exact (H i m).
    + apply (uniqueness (HN P)).
      intros i m. reflexivity.
Qed.

(* * ** The created action on the nadir / * ** 在天底创建的动作 *)

(* For a fixed r, i ↦ ι_i ∘ (r ·) is a cocone in Ab; its mediator is the action. / 对于固定的 r，i ↦ ι_i ∘ (r ·) 是 Ab 中的一个余圆锥；它的中介是作用。 *)

Definition mcol_smul_cone@{a c p o x j} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (r : carrier (rig_setoid (ring_rig R))) :
  Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op).
Proof.
  unshelve refine
    (@Build_Cone (J^op) (Ab@{o c}^op)
       ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op) vertex_obj[N]
       (@Build_ACone (J^op) (Ab@{o c}^op) vertex_obj[N]
          ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op)
          (fun i => cone_leg N i ∘[Ab@{o c}] module_act (K i) r) _)).
  intros x y f m; simpl.
  transitivity (cmon_map (cone_leg N x)
                  (cmon_map (rm_hom (fmap[K] f)) (rm_smul (K y) r m))).
  - apply (proper_morphism (cmon_map (cone_leg N x))).
    symmetry. exact (rm_map_smul (fmap[K] f) r m).
  - exact (cone_leg_coh@{j c o c c c} N f (rm_smul (K y) r m)).
Defined.

Definition mcol_smul_map@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (r : carrier (rig_setoid (ring_rig R))) :
  vertex_obj[N] ~{Ab@{o c}}~> vertex_obj[N] :=
  unique_obj (HN (mcol_smul_cone N r)).

Lemma mcol_smul_triangle@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (r : carrier (rig_setoid (ring_rig R)))
  (i : J) (m : carrier (rm_ab (K i))) :
  cmon_map (mcol_smul_map N HN r) (cmon_map (cone_leg N i) m)
    ≈ cmon_map (cone_leg N i) (rm_smul (K i) r m).
Proof. exact (unique_property (HN (mcol_smul_cone N r)) i m). Qed.

Definition mcol_smul@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (r : carrier (rig_setoid (ring_rig R)))
  (b : carrier (@vertex_obj _ _ _ N)) : carrier (@vertex_obj _ _ _ N) :=
  cmon_map (mcol_smul_map N HN r) b.

Lemma mcol_smul_respects@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N) :
  Proper (equiv ==> equiv ==> equiv) (mcol_smul N HN).
Proof.
  intros r r' Hr b b' Hb. unfold mcol_smul.
  rewrite (proper_morphism (cmon_map (mcol_smul_map N HN r)) _ _ Hb).
  apply (mcol_ext N HN (mcol_smul_map N HN r) (mcol_smul_map N HN r')).
  intros i m.
  rewrite !mcol_smul_triangle.
  apply (proper_morphism (cmon_map (cone_leg N i))).
  exact (rm_smul_respects (K i) r r' Hr m m (reflexivity _)).
Qed.

Lemma mcol_smul_distr_l@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (r : carrier (rig_setoid (ring_rig R)))
  (b b' : carrier (@vertex_obj _ _ _ N)) :
  mcol_smul N HN r (cmon_plus vertex_obj[N] b b')
    ≈ cmon_plus vertex_obj[N] (mcol_smul N HN r b) (mcol_smul N HN r b').
Proof. exact (cmon_map_plus (mcol_smul_map N HN r) b b'). Qed.

Lemma mcol_smul_distr_r@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (r s : carrier (rig_setoid (ring_rig R)))
  (b : carrier (@vertex_obj _ _ _ N)) :
  mcol_smul N HN (rig_add (ring_rig R) r s) b
    ≈ cmon_plus vertex_obj[N] (mcol_smul N HN r b) (mcol_smul N HN s b).
Proof.
  unfold mcol_smul.
  refine (mcol_ext N HN (mcol_smul_map N HN (rig_add (ring_rig R) r s))
            (ab_hom_add (mcol_smul_map N HN r) (mcol_smul_map N HN s))
            _ b).
  intros i m.
  etransitivity; [ exact (mcol_smul_triangle N HN _ i m) | ].
  etransitivity;
    [ exact (proper_morphism (cmon_map (cone_leg N i)) _ _
               (rm_smul_distr_r (K i) r s m)) | ].
  etransitivity; [ exact (cmon_map_plus (cone_leg N i) _ _) | ].
  exact (cmon_plus_respects _ _ _
           (Equivalence_Symmetric _ _ (mcol_smul_triangle N HN r i m))
           _ _
           (Equivalence_Symmetric _ _ (mcol_smul_triangle N HN s i m))).
Qed.

Lemma mcol_smul_assoc@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (r s : carrier (rig_setoid (ring_rig R)))
  (b : carrier (@vertex_obj _ _ _ N)) :
  mcol_smul N HN (rig_mul (ring_rig R) r s) b
    ≈ mcol_smul N HN r (mcol_smul N HN s b).
Proof.
  unfold mcol_smul.
  refine (mcol_ext N HN (mcol_smul_map N HN (rig_mul (ring_rig R) r s))
            (mcol_smul_map N HN r ∘[Ab@{o c}] mcol_smul_map N HN s) _ b).
  intros i m; simpl.
  rewrite mcol_smul_triangle.
  rewrite (mcol_smul_triangle N HN s i m).
  rewrite mcol_smul_triangle.
  apply (proper_morphism (cmon_map (cone_leg N i))).
  apply rm_smul_assoc.
Qed.

Lemma mcol_smul_one@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (b : carrier (@vertex_obj _ _ _ N)) :
  mcol_smul N HN (rig_one (ring_rig R)) b ≈ b.
Proof.
  unfold mcol_smul.
  refine (mcol_ext N HN (mcol_smul_map N HN (rig_one (ring_rig R)))
            (@id Ab@{o c} vertex_obj[N]) _ b).
  intros i m; simpl.
  rewrite mcol_smul_triangle.
  apply (proper_morphism (cmon_map (cone_leg N i))).
  apply rm_smul_one.
Qed.

(** ** The created module and cocone / ** 已创建的模块和圆锥 *)

Definition ColimMod@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N) : obj[RMod@{o x a p c} R] :=
  @Build_RModObject R vertex_obj[N] (mcol_smul N HN)
    (mcol_smul_respects N HN) (mcol_smul_distr_l N HN)
    (mcol_smul_distr_r N HN) (mcol_smul_assoc N HN) (mcol_smul_one N HN).

Definition mcol_hom@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N) (i : J) :
  K i ~{RMod@{o x a p c} R}~> ColimMod N HN :=
  @Build_RModHom R (K i) (ColimMod N HN) (cone_leg N i)
    (fun r m => Equivalence_Symmetric _ _ (mcol_smul_triangle N HN r i m)).

Definition mcol_cone@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N) : Cone (K^op).
Proof.
  unshelve refine
    (@Build_Cone (J^op) ((RMod@{o x a p c} R)^op) (K^op) (ColimMod N HN)
       (@Build_ACone (J^op) ((RMod@{o x a p c} R)^op) (ColimMod N HN)
          (K^op) (mcol_hom N HN) _)).
  intros x y f m. exact (cone_leg_coh@{j c o c c c} N f m).
Defined.

(* * ** Reflection, and the created cocone is colimiting / * ** 反射，并且创建的余圆锥是余极限 *)

(* A cocone of modules whose underlying cocone is colimiting in Ab is colimiting; the mediator is the Ab one, R-linear by [mcol_ext]. / 一个模的余锥，其底层余锥在 Ab 中是余极限的，也是余极限；中介是 Ab 的，由 [mcol_ext] 线性。 *)

Definition mcol_reflect@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (M : Cone (K^op))
  (HM : IsLimitCone@{l l0 j c o}
          (FCone ((RMod_Forget_Ab@{x o o a p c} R)^op) M)) :
  IsLimitCone@{l l0 j c o} M.
Proof.
  intros P.
  pose (m := unique_obj
               (HM (FCone ((RMod_Forget_Ab@{x o o a p c} R)^op) P))).
  assert (Hm : ∀ (i : J) (a : carrier (rm_ab (K i))),
             cmon_map m (cmon_map (rm_hom (cone_leg M i)) a)
               ≈ cmon_map (rm_hom (cone_leg P i)) a).
  { intros i a.
    exact (unique_property
             (HM (FCone ((RMod_Forget_Ab@{x o o a p c} R)^op) P)) i a). }
  unshelve refine (@Build_Unique _ _ _ (@Build_RModHom R _ _ m _) _ _).
  - intros r b.
    refine (mcol_ext (FCone ((RMod_Forget_Ab@{x o o a p c} R)^op) M) HM
              (m ∘[Ab@{o c}] module_act vertex_obj[M] r)
              (module_act vertex_obj[P] r ∘[Ab@{o c}] m) _ b).
    intros i a; simpl.
    transitivity (cmon_map m (cmon_map (rm_hom (cone_leg M i))
                                (rm_smul (K i) r a))).
    + apply (proper_morphism (cmon_map m)).
      symmetry. exact (rm_map_smul (cone_leg M i) r a).
    + rewrite Hm.
      rewrite (rm_map_smul (cone_leg P i) r a).
      apply rm_smul_respects; [ reflexivity | ].
      symmetry. exact (Hm i a).
  - intros i a. exact (Hm i a).
  - intros v Hv b.
    exact (uniqueness
             (HM (FCone ((RMod_Forget_Ab@{x o o a p c} R)^op) P))
             (rm_hom v) Hv b).
Defined.

Definition mcol_strict_lift@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N) :
  StrictLift (K^op) ((RMod_Forget_Ab@{x o o a p c} R)^op) N :=
  @Build_StrictLift _ _ _ (K^op) ((RMod_Forget_Ab@{x o o a p c} R)^op) N
    (mcol_cone N HN) eq_refl (fun i m => reflexivity _).

(** ** Riehl's Corollary 5.6.10 / ** Riehl 的推论 5.6.10 *)

Definition RMod_Forget_Ab_StrictlyCreatesColimit@{a c p o x j l l0}
  {R : RingObject@{a c p}} {J : Category@{j c c}}
  (K : J ⟶ RMod@{o x a p c} R) :
  StrictlyCreatesColimit@{l x l l l0 j o c o} K
    (RMod_Forget_Ab@{x o o a p c} R) :=
  @Build_StrictlyCreatesLimit (J^op) ((RMod@{o x a p c} R)^op)
    (Ab@{o c}^op) (K^op) ((RMod_Forget_Ab@{x o o a p c} R)^op)
    (fun N HN => mcol_strict_lift N HN)
    (fun N HN => mcol_reflect (mcol_cone N HN) HN)
    (fun M HM => mcol_reflect M HM).

Definition RMod_Forget_Ab_CreatesColimit@{a c p o x j l l0}
  {R : RingObject@{a c p}} {J : Category@{j c c}}
  (K : J ⟶ RMod@{o x a p c} R) :
  CreatesColimit@{l x l l l0 j o c o} K (RMod_Forget_Ab@{x o o a p c} R) :=
  StrictlyCreatesLimit_CreatesLimit
    (RMod_Forget_Ab_StrictlyCreatesColimit@{a c p o x j l l0} K).

Definition RMod_Forget_Ab_creates_colimits@{a c p o x t l l0 s}
  (R : RingObject@{a c p}) :
  CreatesAllColimits@{t l x l l l0 s o c o}
    (RMod_Forget_Ab@{x o o a p c} R) :=
  fun J K => RMod_Forget_Ab_CreatesColimit@{a c p o x s l l0} K.

(* * ** Readbacks: the lift is on the nose / * ** 回读：升力在机头 *)

Example mcol_over_obj@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N) :
  rm_ab (ColimMod N HN) = vertex_obj[N] := eq_refl.

Example mcol_over_legs@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N) (i : J) :
  rm_hom (mcol_hom N HN i) = cone_leg N i := eq_refl.

Example mcol_smul_is_mediator@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (r : carrier (rig_setoid (ring_rig R))) :
  rm_smul (ColimMod N HN) r
  = cmon_map (unique_obj (HN (mcol_smul_cone N r))) := eq_refl.

Example mcol_lift_apex@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} (K : J ⟶ RMod@{o x a p c} R)
  (L : Colimit (RMod_Forget_Ab@{x o o a p c} R ◯ K)) :
  rm_ab (vertex_obj[creates_colimit_lift
           (RMod_Forget_Ab_CreatesColimit@{a c p o x j l l0} K) L])
  = vertex_obj[L] := eq_refl.

Example mcol_lift_legs@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} (K : J ⟶ RMod@{o x a p c} R)
  (L : Colimit (RMod_Forget_Ab@{x o o a p c} R ◯ K)) (i : J) :
  rm_hom (cone_leg (@limit_cone _ _ _
            (creates_colimit_lift
               (RMod_Forget_Ab_CreatesColimit@{a c p o x j l l0} K) L)) i)
  = cone_leg (@limit_cone _ _ _ L) i := eq_refl.

(*
 The whole lifted module IS [ColimMod] of the given colimit, read in the
 opposite category. 

 --------
 整个提升模块是给定余极限的 [ColimMod]，在相反范畴中读取。
*)
Example mcol_lift_module@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} (K : J ⟶ RMod@{o x a p c} R)
  (L : Colimit (RMod_Forget_Ab@{x o o a p c} R ◯ K)) :
  vertex_obj[creates_colimit_lift
     (RMod_Forget_Ab_CreatesColimit@{a c p o x j l l0} K) L]
  = ColimMod (cone_op_comp (@limit_cone _ _ _ L))
      (islimitcone_op_comp (limit_limitcone L)) := eq_refl.

(* The reflected mediator computes: its group map IS the Ab mediator of the underlying cocones. / 反射中介计算：它的群映射就是底层余锥的阿贝尔中介。 *)
Example mcol_reflect_mediator@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (M : Cone (K^op))
  (HM : IsLimitCone@{l l0 j c o}
          (FCone ((RMod_Forget_Ab@{x o o a p c} R)^op) M))
  (P : Cone (K^op)) :
  rm_hom (unique_obj (mcol_reflect M HM P))
  = unique_obj (HM (FCone ((RMod_Forget_Ab@{x o o a p c} R)^op) P))
  := eq_refl.

(* * ** Uniqueness of the created action / * ** 创建操作的独特性 *)

(*
 Any family of Ab endomorphisms making every insertion R-linear is ≈ the
 created action. 

 --------
 使每个插入都是 R 线性的任何 Ab 自同态族 ≈ 所创建的作用。
*)

Lemma mcol_smul_unique@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (s : carrier (rig_setoid (ring_rig R)) →
       vertex_obj[N] ~{Ab@{o c}}~> vertex_obj[N])
  (Hs : ∀ (i : J) r (m : carrier (rm_ab (K i))),
     cmon_map (s r) (cmon_map (cone_leg N i) m)
       ≈ cmon_map (cone_leg N i) (rm_smul (K i) r m))
  (r : carrier (rig_setoid (ring_rig R)))
  (b : carrier (@vertex_obj _ _ _ N)) :
  cmon_map (s r) b ≈ mcol_smul N HN r b.
Proof.
  refine (mcol_ext N HN (s r) (mcol_smul_map N HN r) _ b).
  intros i m. rewrite Hs. symmetry. apply mcol_smul_triangle.
Qed.

(* * ** A witness: every diagram over a shape with a terminal object / * ** 一个见证者：每个终端对象形状上的图表 *)

(* Structure/Limit/Initial.v's [terminal_Colimit] is a colimit in Ab of U ◯ K; the lift has group U (K 1) and action K(!)(r · m). / Structure/Limit/Initial.v 的 [terminal_Colimit] 是 Ab 中 U ◯ K 的余极限；提升有群 U (K 1) 和作用 K(!)(r · m)。 *)

Definition rmod_terminal_colimit@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} (T : @Terminal J) (K : J ⟶ RMod@{o x a p c} R) :
  Colimit K :=
  creates_colimit_lift (RMod_Forget_Ab_CreatesColimit@{a c p o x j l l0} K)
    (terminal_Colimit@{j c o c l0 l} T (RMod_Forget_Ab@{x o o a p c} R ◯ K)).

Example rmod_terminal_group@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} (T : @Terminal J) (K : J ⟶ RMod@{o x a p c} R) :
  rm_ab (vertex_obj[@limit_cone _ _ _
           (rmod_terminal_colimit@{a c p o x j l l0} T K)])
  = rm_ab (K (@terminal_obj J T)) := eq_refl.

Example rmod_terminal_smul@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} (T : @Terminal J) (K : J ⟶ RMod@{o x a p c} R)
  (r : carrier (rig_setoid (ring_rig R)))
  (m : carrier (rm_ab (K (@terminal_obj J T)))) :
  rm_smul (vertex_obj[@limit_cone _ _ _
             (rmod_terminal_colimit@{a c p o x j l l0} T K)]) r m
  = cmon_map (rm_hom (fmap[K] (@one J T (@terminal_obj J T))))
      (rm_smul (K (@terminal_obj J T)) r m) := eq_refl.

Lemma rmod_terminal_smul_own@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} (T : @Terminal J) (K : J ⟶ RMod@{o x a p c} R)
  (r : carrier (rig_setoid (ring_rig R)))
  (m : carrier (rm_ab (K (@terminal_obj J T)))) :
  rm_smul (vertex_obj[@limit_cone _ _ _
             (rmod_terminal_colimit@{a c p o x j l l0} T K)]) r m
  ≈ rm_smul (K (@terminal_obj J T)) r m.
Proof.
  change (cmon_map (rm_hom (fmap[K] (@one J T (@terminal_obj J T))))
            (rm_smul (K (@terminal_obj J T)) r m)
          ≈ rm_smul (K (@terminal_obj J T)) r m).
  etransitivity.
  - exact (@fmap_respects _ _ K _ _ (@one J T (@terminal_obj J T)) id
             (one_unique _ _) (rm_smul (K (@terminal_obj J T)) r m)).
  - exact (@fmap_id _ _ K _ (rm_smul (K (@terminal_obj J T)) r m)).
Qed.
