(* * * R ⊗ (−) is a left adjoint: the premises of Riehl's Corollary 5.6.10 / * * R ⊗ (−) 是一个左伴随：Riehl 推论 5.6.10 的前提 *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Continuity.
Require Import Category.Adjunction.Additive.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Structure.AbCategory.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Tensor.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.BaseChange.
Require Import Category.Instance.Mod.Coextension.
Require Import Category.Instance.Mod.TensorMonad.

Generalizable All Variables.

(*
 Book: Riehl, "Category Theory in Context", 2nd ed., Corollary
 5.6.10, printed p. 212 (PDF p. 232) — riehl:5.6:cor10; with
 her Example 4.4.15, printed p. 154 (PDF p. 174), Theorem 4.6.2,
 printed p. 165, Theorem 5.6.5, printed pp. 210–211, and
 Exercise 5.6.ii, printed p. 217
 nLab: https://ncatlab.org/nlab/show/tensor-hom+adjunction
 nLab: https://ncatlab.org/nlab/show/monadic+functor
 nLab: https://ncatlab.org/nlab/show/created+limit

 Riehl proves her Corollary 5.6.10 — the forgetful functor U : _R Mod → Ab
 creates every colimit that Ab has, in this header's paraphrase — in one
 short paragraph.  U is monadic with monad R ⊗_ℤ −.  "By Example 4.4.15, for
 any pair of abelian groups A and B, there is a natural isomorphism"
 involving "the abelian group Hom_ℤ(R, B) of group homomorphisms R → B.  In
 particular, the monad R ⊗_ℤ − : Ab → Ab has a right adjoint Hom_ℤ(R, −)."
 And "By Theorem 4.6.2, R ⊗_ℤ − preserves all colimits and so Theorem
 5.6.5(ii) applies to all diagrams in Ab."  Theorem 4.6.2 (printed p. 165)
 is "Right adjoints preserve limits, and left adjoints preserve colimits";
 Theorem 5.6.5 (printed p. 210) says that a monadic functor creates "(ii)
 any colimits that C has and the monad and its square preserve", and its
 proof asks, on printed p. 211, "the additional hypothesis that T and T²
 preserve the colimit cone in C under consideration".  This file delivers
 the premises that proof consumes and stops before the theorem it feeds,
 which the tree does not have.

 WHICH READING OF THE DISPLAY.  The natural isomorphism is displayed on
 printed p. 212 as Ab(R ⊗_ℤ A, B) ≅ Ab(A, Hom_ℤ(R, A′)), and the sentence
 that follows names the group on the right Hom_ℤ(R, B).  The tree implements
 the B reading, Ab(R ⊗_ℤ A, B) ≅ Ab(A, Hom_ℤ(R, B)), the shape of her
 Example 4.4.15's own display (4.4.16) (printed p. 154), Ab(A ⊗_ℤ B,
 C) ≅ Ab(A, Hom(B, C)), with the fixed factor R written on the left as the
 corollary writes it.

 THE TENSOR–HOM ADJUNCTION IS A COMPOSITE, NOT A NEW CONSTRUCTION.
 Instance/Mod/TensorMonad.v's [TensorF R] is U ◯ ZExt R, whose value at A is
 Instance/Ab/Tensor.v's [AbTensor (ring_ab R) A], R ⊗ A.
 [TensorF_left_adjoint] composes (Adjunction/Compose.v's
 [Adjunction_Compose]) Instance/Mod/BaseChange.v's
 [zext_adjunction R : ZExt R ⊣ U] with Instance/Mod/Coextension.v's
 [coex_adjunction R : U ⊣ Coextension R], so TensorF R ⊣ U ◯ Coextension R,
 and the right adjoint IS Hom_ℤ(R, −): [TensorF_right_adjoint_obj] reads U
 (Coextension R B) back, by [eq_refl], as Adjunction/Additive.v's
 [hom_ab Ab_AbEnriched (ring_ab R) B], the additive maps R → B under
 pointwise addition.  The bijection is Riehl's correspondence between
 homomorphisms out of the tensor and bilinear maps, read at generators.  The
 transpose of φ : R ⊗ A → B sends a to r ↦ φ ((r · 1) ⊗ a) ([tensor_hom_to],
 by [eq_refl]) — the unit enters through ZExt's own action — and so
 is ≈ r ↦ φ (r ⊗ a) ([tensor_hom_to_gen], by [rig_mul_one_r] under
 Instance/Ab/Tensor.v's [te_gen]).  The inverse transpose of
 ψ : A → Hom_ℤ(R, B) sends r ⊗ a to ψ a (1 · r) ([tensor_hom_from], by
 [eq_refl]), evaluation at 1 after Coextension's action by translation, and
 so is ≈ ψ a r ([tensor_hom_from_gen], by [rig_mul_one_l]).  Without the
 unit, both are refused at [eq_refl] (C5 and C6 of
 Test/ProbeTensorMonad465.v), at a variable scalar: r · 1 or 1 · r against
 r is a propositional law at an abstract ring, and even at [Int_Ring] the
 product is stuck on a variable integer (C5Z, C6Z), while over ℤ at the
 scalar 3 both hold by [eq_refl] (that probe's controls).

 THE SQUARE, AND BOTH FORMS OF COCONTINUITY.  [TensorF2_left_adjoint]
 composes the adjunction with itself, so T² = TensorF R ◯ TensorF R is a
 left adjoint too.  Adjunction/Continuity.v then gives
 [TensorF_cocontinuous] and [TensorF2_cocontinuous], at
 Structure/Limit/Preservation.v's [CocontinuousFunctor]: every colimiting
 COCONE is carried to a colimiting cocone, which is the form Riehl's proof
 of 5.6.5(ii) asks for ("preserve the colimit cone"); and
 [TensorF_preserves_colimits] and [TensorF2_preserves_colimits], at
 [PreservesAllColimits], the apex-level form, to which
 Structure/Limit/Preservation.v's [Cocontinuous_PreservesAllColimits]
 descends from the first.

 ONLY AT [RingObject@{c c c}], MEASURED.  Every constant of the tensor–hom
 part binds [@{c o x}] (or [@{c o x t l l0 s}]) with the ring's three
 universes one.  That is Coextension's, not this file's: About on
 [Coextension] and [coex_adjunction] prints the block equations u = u0 and
 u = u1 over [RingObject@{u u0 u1}], and Instance/Mod/Coextension.v's header
 traces them to reading a ring's additive group as the source of a
 homomorphism of abelian groups and, independently, to Instance/Mod.v's
 [Ring_RMod].  Stated at a general [RingObject@{a c p}] under an extensible
 binder, the composite elaborates with the equations a = c and a = p (that
 probe's control [p465c_ctl_ring_open]); with c < a declared in the same
 binder it is refused, "Universe inconsistency. Cannot enforce a = c because
 c < a." (C8 of that probe), and with p < a likewise on a = p (C8a).
 Instance/Mod/TensorMonad.v's monad and Instance/Mod/Colimit/Creation.v's
 direct creation hold at [RingObject@{a c p}]; this restriction is the
 monadic route's alone.

 THE THIRD TRANSPORT'S PREMISE.  Riehl's route reaches U through the
 Eilenberg–Moore forgetful functor, and U is not that functor on the nose.
 [rmod_forget_comparison_obj] and [rmod_forget_comparison_map] show, by
 [eq_refl], that EM_Forget (TensorF R) ◯ EM_Comparison (zext_adjunction R)
 agrees with RMod_Forget_Ab R on objects and arrows, at a general
 [RingObject@{a c p}]; the two functor RECORDS are refused as one term
 (C7), each of the three law fields separating on its own
 ([fmap_respects], [fmap_id], [fmap_comp]; C7a, C7b, C7c);
 and [rmod_forget_comparison] is the isomorphism of functors, in
 Theory/Functor.v's [Functor_Setoid], with identity components.

 NOT DELIVERED: RIEHL'S ROUTE ITSELF.  The step all of this feeds is her
 Theorem 5.6.5(ii) at an Eilenberg–Moore forgetful functor, issue #1008,
 OPEN; the tree has no [CreatesColimit] at [EM_Forget], only the limit
 clause (Monad/Eilenberg/Moore/Limit.v's [em_forget_StrictlyCreatesLimit]).
 The statement of the corollary is delivered directly, without the monad, by
 Instance/Mod/Colimit/Creation.v's [RMod_Forget_Ab_creates_colimits].  A
 follow-up finishing the monadic route must: (1) prove #1008's clause (ii)
 for [EM_Forget T], for a diagram K of T-algebras and a colimiting cocone
 under EM_Forget T ◯ K whose images under T and T ◯ T are colimiting (the
 [PreservesColimitCocone] form [TensorF_cocontinuous] and
 [TensorF2_cocontinuous] supply), with the structure map on the nadir
 induced by the colimit under T ◯ EM_Forget T ◯ K, as Riehl sketches; (2)
 instantiate it at Instance/Mod/TensorMonad.v's [TensorMonad R], whose
 functor is [TensorF R], at [RingObject@{c c c}]; (3) carry the creation
 back along the comparison equivalence [RMod_comparison_equivalence] of that
 file, through Theory/Equivalence/Creation.v's [equivalence_CreatesLimit] at
 the opposite equivalence (Theory/Equivalence/Limit.v's
 [EquivalenceOfCategories_op]) and Structure/Limit/Creation.v's
 [CreatesLimit_compose], repackaging the opposite of a composite as that
 file's colimit section does; (4) move it from EM_Forget ◯ EM_Comparison to
 [RMod_Forget_Ab R] along [rmod_forget_comparison], read in the opposite
 categories, with Instance/Cat/Creation.v's [CreatesLimit_transport]; and
 (5) compare the result with the direct [RMod_Forget_Ab_CreatesColimit], by
 [creates_lift_unique], recording the restriction to [RingObject@{c c c}]
 that (2) inherits.

 STRENGTHS.  By [eq_refl]: the right adjoint's value
 ([TensorF_right_adjoint_obj]); the two transposes at generators, with the
 unit ([tensor_hom_to], [tensor_hom_from]); U^T ◯ K against U on objects and
 arrows ([rmod_forget_comparison_obj], [rmod_forget_comparison_map]).
 At ≈ only: the transposes without the unit ([tensor_hom_to_gen],
 [tensor_hom_from_gen]); U^T ◯ K against U as functors
 ([rmod_forget_comparison]).  Refused, each pinned in
 Test/ProbeTensorMonad465.v beside its positive half: the transposes
 without the unit at [eq_refl] (C5, C6, and over ℤ at a variable integer
 C5Z, C6Z), the two functor records as one (C7) and each of their three law
 fields (C7a-C7c), by conversion; the tensor–hom adjunction at a ring whose
 carrier or proof universe is declared strictly below its auxiliary one
 (C8, C8a), by universes.

 WHY C5-C7 ARE REFUSED.  Not by opacity: in the copy of this file, its
 sibling, Instance/Mod/TensorMonad.v and their joint closure of 95 files
 with every [Qed] made [Defined] (Instance/Sets.v too),
 [Transparent Obligations] set and [abstract] made [transparent_abstract],
 described in Instance/Mod/Colimit/Creation.v's header, all of C5-C7, C5Z,
 C6Z and C7a-C7c stand, each stripped copy stopping with "cannot unify"
 inside its command.  C5 and C6 compare r · 1 or 1 · r with r at a variable
 scalar (propositional at an abstract ring; stuck on a variable integer
 even at [Int_Ring], C5Z and C6Z);
 C7 compares the composite functor's derived law proofs with
 [RMod_Forget_Ab]'s own.

 TRANSPARENCY, MEASURED.  Counted by token as in the sibling, 2 [Qed] and 1
 [Defined].  The [Defined] of [rmod_forget_comparison] is NOT load-bearing
 here — made [Qed] in a copy of the whole file, the file compiles — and is
 kept so that a transport along it computes with its identity components.

 UNIVERSES, read off [About] on all 14 constants.  The tensor–hom constants
 bind [@{c o x}]: R : RingObject@{c c c}, Ab@{o c}, RMod@{o x c c c}, pinned
 as Coextension@{c c c o x}, coex_adjunction@{c c c o x c},
 zext_adjunction@{c c c o o x c c} and Adjunction@{o c c o c c c c x c o}.
 The four cocontinuity constants add t (the class's level), l and l0 (the
 colimit predicate's) and s (the shape's objects).  The three comparison
 constants bind [@{a c p o x}] as Instance/Mod/TensorMonad.v does.  The
 strict bounds are Set < o, c < o and c < x everywhere, and c < t, s < t on
 the cocontinuity constants; the rest are c <= l0, s <= l0, l0 <= l, o <= l,
 l <= t and o <= t there, and a <= o, c <= a, p <= a on the comparison.
 There is no equation and no other [Set].  First carriers, by [About] on the
 donors: Set < o and c < o, Instance/Ab.v's [Ab]; c < x, Instance/Mod.v's
 [RMod]; c < t and s < t, Structure/Limit/Preservation.v's
 [CocontinuousFunctor] (u4 < u, u5 < u) and [PreservesAllColimits] (u3 < u,
 u5 < u).  Two donors carry levels outside their statements, and each
 such level is pinned rather than left outside the closed binder:
 [left_adjoint_Cocontinuous@{u u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10}]'s u5,
 which neither its type nor its block mentions, is written c, and
 [left_adjoint_preserves_colimits@{u u0 u1 u2 u3 u4 u5 u6 u7 u8 u9}]'s u4,
 likewise unmentioned, is written c and its u5, bounded only from below,
 t.  Made a placeholder in a copy of the whole file, each of the three is
 refused with "Universe ... is unbound"; the u6 of each, in its type but
 unconstrained by its block, compiles as a placeholder, the adjunction
 argument's last level fixing it, and is written o.  The stdlib caps are
 inherited, each placed by [About] on every constant of its donor's
 dependency cone, as [Print All Dependencies] lists it, at its topmost
 carrier: compose and ID on Instance/Sets.v's [setoid_morphism_compose]
 and [setoid_morphism_id], through Instance/CMon.v's [cmon_hom_compose]
 and [cmon_hom_id] and so through [Ab]; prod_rect on two setoid rewrites,
 Instance/Ab.v's [ab_cancel_l], through BaseChange.v's [ZExtObj] on the
 constants that name [TensorF] and through Coextension.v's [coex_group]
 and Structure/AbCategory.v's [Ab_AbEnriched] on
 [TensorF_right_adjoint_obj], and Theory/Isomorphism.v's [iso_to_monic],
 through Theory/Adjunction.v's [Build_Adjunction'] in both adjunctions;
 Logic_lemmas.equality on Lib/Setoid.v's [eq_equivalence] and projections
 (the pair projections) on [Build_Adjunction'], both through
 [zext_adjunction] and [coex_adjunction]; and Projections (the sigma
 projections) on Monad/Eilenberg/Moore.v's [EilenbergMoore], through
 [EM_Forget], on the comparison constants.

 NOT DELIVERED, FURTHER.  No cocontinuity of R ⊗ (−) at a general ring, by
 this or any other route.  No naturality of the bijection is restated beyond
 what [Adjunction] carries.  No comparison with the hom–tensor bijections of
 Instance/Mod/HomTensor.v and Instance/Mod/Closed.v, which tensor over R
 rather than over ℤ.  Nothing registered as an [Instance]. 

 --------
 书籍：Riehl，《上下文中的范畴论》，第二版，推论 5.6.10，印刷页 212（PDF 页 232）— riehl:5.6:cor10；以及她的例子 4.4.15，印刷页 154（PDF 页 174），定理 4.6.2，印刷页 165，定理 5.6.5，印刷页 210–211，和练习 5.6.ii，印刷页 217
 nLab: https://ncatlab.org/nlab/show/tensor-hom+adjunction
 nLab: https://ncatlab.org/nlab/show/monadic+functor
 nLab: https://ncatlab.org/nlab/show/created+limitRiehl 证明了她的推论 5.6.10 —— 即忘记函子 U : _R Mod → Ab 会生成 Ab 中的每一个余极限，用本标题的意译来说 —— 仅用一小段文字。U 是带有单子 R ⊗_ℤ − 的单子函子。“根据例 4.4.15，对于任意一对阿贝尔群 A 和 B，存在一个自然同构”，涉及“从 R 到 B 的群同态构成的阿贝尔群 Hom_ℤ(R, B)”。特别地，单子 R ⊗_ℤ − : Ab → Ab 有一个右伴随函子 Hom_ℤ(R, −)。”并且“根据定理 4.6.2，R ⊗_ℤ − 保留所有余极限，因此定理 5.6.5(ii) 适用于 Ab 中的所有图。”定理 4.6.2（印刷页 165）是“右伴随函子保留极限，左伴随函子保留余极限”；定理 5.6.5（印刷页210) 说一个单子函子生成“(ii) C 所有的余极限，并且单子及其平方保持这些余极限”，其证明在印刷的第 211 页上询问“附加假设是 T 和 T² 保持所考虑的 C 中的余极限锥”。此文件提供了证明所使用的前提，并在其所引用的定理之前停止，而该定理在该树中不存在。显示的哪种读法。自然同构在印刷的第212页上显示为 Ab(R ⊗_ℤ A, B) ≅ Ab(A, Hom_ℤ(R, A′))，紧随其后的句子将右边的群命名为 Hom_ℤ(R, B)。该树实现了 B 读法，即 Ab(R ⊗_ℤ A, B) ≅ Ab(A, Hom_ℤ(R, B))，这是她在例 4.4.15 中自己的显示（4.4.16，印刷第154页）的形式，即 Ab(A ⊗_ℤ B, C) ≅ Ab(A, Hom(B, C))，固定因子 R 在左边书写，如推论所示。张量–Hom 对偶是一个复合，而不是一个新的构造。Instance/Mod/TensorMonad.v 中的 [TensorF R] 是 U ◯ ZExt R，其在 A 上的值是 Instance/Ab/Tensor.v 中的 [AbTensor (ring_ab R) A]，即 R ⊗ A。[TensorF_left_adjoint] 复合了 (Adjunction/Compose.v 的 [Adjunction_Compose]) Instance/Mod/BaseChange.v 的 [zext_adjunction R : ZExt R ⊣ U] 与 Instance/Mod/Coextension.v 的 [coex_adjunction R : U ⊣ Coextension R]，因此 TensorF R ⊣ U ◯ Coextension R，而右伴随确实是 Hom_ℤ(R, −)：[TensorF_right_adjoint_obj]，通过 [eq_refl] 阅读 U (Coextension R B)，如 Adjunction/Additive.v 的 [hom_ab Ab_AbEnriched (ring_ab R) B] 所示，即在逐点加法下的 R → B 的加法映射。这个一一对应是 Riehl 对张量的同态和双线性映射之间的对应关系，在生成元上进行阅读。φ : R ⊗ A → B 的转置将 a 发送为 r ↦ φ((r · 1) ⊗ a)（[tensor_hom_to]，根据 [eq_refl]）——单位通过 ZExt 自身的作用进入——因此约等于 r ↦ φ(r ⊗ a)（[tensor_hom_to_gen]，根据 Instance/Ab/Tensor.v 的 [rig_mul_one_r] 下的 [te_gen]）。ψ : A → Hom_ℤ(R, B) 的逆转置将 r ⊗ a 发送为 ψ a (1 · r)（[tensor_hom_from]，根据 [eq_refl]），在 Coextension 的作用后于 1 进行求值，因此约等于 ψ a r（[tensor_hom_from_gen]，根据 [rig_mul_one_l]）。没有单位时，两者均在 [eq_refl] 被拒绝（Test/ProbeTensorMonad465.v 的 C5 和 C6），在变量标量上：r · 1 或 1 · r 与 r 对比是抽象环上的命题定律，即使在 [Int_Ring] 上，乘积在变量整数上也是停滞的（C5Z, C6Z），而在 ℤ 上的标量 3 时，两者皆成立（[eq_refl]，该探针的控制）。正方形，以及连续性的两种形式。[TensorF2_left_adjoint] 将伴随自身组合，因此 T² = TensorF R ◯ TensorF R 也是左伴随。Adjunction/Continuity.v 然后给出 [TensorF_cocontinuous] 和 [TensorF2_cocontinuous]，在 Structure/Limit/Preservation.v 的 [CocontinuousFunctor]：每个余极限 COCONE 都会被映射为余极限 cocone，这正是 Riehl 对 5.6.5(ii) 的证明所要求的形式（"保持余极限锥"）；以及 [TensorF_preserves_colimits] 和 [TensorF2_preserves_colimits]，在 [PreservesAllColimits]，顶点级别的形式，从第一个下降到 Structure/Limit/Preservation.v 的 [Cocontinuous_PreservesAllColimits]。仅在 [RingObject@{c c c}]，已测量。张量–同态部分的每个常量都绑定 [@{c o x}]（或 [@{c o x t l l0 s}]），与环的三个宇宙之一匹配。也就是说，这是 Coextension 的，而不是这个文件的：关于 [Coextension] 和 [coex_adjunction] 打印块方程 u = u0 和 u = u1 在 [RingObject@{u u0 u1}] 上，以及 Instance/Mod/Coextension.v 的头文件将它们追踪到将环的加法群读作阿贝尔群同态的源，且独立地追踪到 Instance/Mod.v 的 [Ring_RMod]。在一个可扩展绑定器下的一般 [RingObject@{a c p}] 上陈述时，复合会展开为方程 a = c 和 a = p（该探针的控制 [p465c_ctl_ring_open]）；在同一绑定器中声明 c < a 时，它会被拒绝，“宇宙不一致。无法强制 a = c，因为 c < a。”（该探针的 C8），同样地在 a = p 时 p < a 也会被拒绝（C8a）。Instance/Mod/TensorMonad.v 的单子以及 Instance/Mod/Colimit/Creation.v 的直接创造在 [RingObject@{a c p}] 处成立；这种限制仅适用于单子路径。

 第三个传递的前提。Riehl 的路径通过 Eilenberg–Moore 忘记函子到达 U，而 U 并不是该函子本身。[rmod_forget_comparison_obj] 和 [rmod_forget_comparison_map] 通过 [eq_refl] 表明，EM_Forget (TensorF R) ◯ EM_Comparison (zext_adjunction R) 在一般的 [RingObject@{a c p}] 上，在对象和箭头上与 RMod_Forget_Ab R 一致；两个函子记录作为一个项 (C7) 被拒绝，每三个律域分别独立（[fmap_respects], [fmap_id], [fmap_comp]；C7a, C7b, C7c）；并且 [rmod_forget_comparison] 是函子的同构，在 Theory/Functor.v 的 [Functor_Setoid] 中，带有恒等分量。未交付：RIEHL 本身的路径。所有这些步骤所指向的是她的定理 5.6.5(ii) 在一个 Eilenberg–Moore 遗忘函子上，第 1008 号问题，未解决；该树在 [EM_Forget] 上没有 [CreatesColimit]，只有极限子句（Monad/Eilenberg/Moore/Limit.v 的 [em_forget_StrictlyCreatesLimit]）。推论的陈述是直接给出的，没有涉及 monad，由 Instance/Mod/Colimit/Creation.v 的 [RMod_Forget_Ab_creates_colimits] 提供。必须完成单子路线的后续工作：(1) 证明 [EM_Forget T] 的 #1008 条款(ii)，对于 T-代数的图 K 和 EM_Forget T ◯ K 下的余极锥，其在 T 和 T ◯ T 下的像为余极（[PreservesColimitCocone] 形式 [TensorF_cocontinuous] 和 [TensorF2_cocontinuous] 提供），其在底部的结构映射由 T ◯ EM_Forget T ◯ K 下的极限诱导，如 Riehl 所述；(2) 在 Instance/Mod/TensorMonad.v 的 [TensorMonad R] 上实例化它，其函子为 [TensorF R]，在 [RingObject@{c c c}] 处；(3) 通过该文件的比较等价 [RMod_comparison_equivalence] 将创建带回，通过 Theory/Equivalence/Creation.v 的 [equivalence_CreatesLimit] 在对偶等价（Theory/Equivalence/Limit.v 的 [EquivalenceOfCategories_op]）和 Structure/Limit/Creation.v 的 [CreatesLimit_compose]，重新打包复合的对偶作为该文件的余极部分处理。s；（4）将其从 EM_Forget ◯ EM_Comparison 移动到 [RMod_Forget_Ab R]，沿 [rmod_forget_comparison]，按相反的类别读取，使用 Instance/Cat/Creation.v 的 [CreatesLimit_transport]；以及（5）通过 [creates_lift_unique] 将结果与直接 [RMod_Forget_Ab_CreatesColimit] 进行比较，记录对 [RingObject@{c c c}] 的限制，这是（2）继承的。优势。 由 [eq_refl] 提出：右伴随的值（[TensorF_right_adjoint_obj]）；生成元处的两个转置，以及单位（[tensor_hom_to]，[tensor_hom_from]）；U^T ◯ K 对象和箭头上的 U（[rmod_forget_comparison_obj]，[rmod_forget_comparison_map]）。
 仅在 ≈ 处：没有单位的转置（[tensor_hom_to_gen]，[tensor_hom_from_gen]）；作为函子时的 U^T ◯ K 对 U（[rmod_forget_comparison]）。 拒绝，每个都在 Test/ProbeTensorMonad465.v 中固定在其正半旁边：没有单位的转置在 [eq_refl]（C5, C6，以及在变量整数 C5Z, C6Z 上的 ℤ）；两个函子记录作为一个（C7）以及它们的三个律字段（C7a-C7c），通过转换；在载体或证明宇声明严格低于其辅助宇的环上的张量–同构伴随（C8, C8a），通过宇论。为什么 C5-C7 被拒绝。不是因为不透明：在这个文件的副本中，它的同级文件 Instance/Mod/TensorMonad.v 以及它们与 95 个文件的联合闭包中，每个 [Qed] 都被改为 [Defined]（Instance/Sets.v 也是），[Transparent Obligations] 设置并且 [abstract] 被改为 [transparent_abstract]，如 Instance/Mod/Colimit/Creation.v 的标题中所描述，所有的 C5-C7、C5Z、C6Z 和 C7a-C7c 都存在，每个被剥离的副本都在其命令中以“无法统一”结束。C5 和 C6 比较 r · 1 或 1 · r 与 r 在变量标量处（在抽象环上的命题；即使在 [Int_Ring]、C5Z 和 C6Z 上也卡在变量整数），C7 比较复合函子派生律证明与 [RMod_Forget_Ab] 自身。透明度，可测量。按照与同类相同的方式按令牌计数，2 个 [Qed] 和 1 个 [Defined]。[rmod_forget_comparison] 的 [Defined] 在这里不是承重的——在整个文件的副本中制作了 [Qed]，文件可以编译——并且保持这样，以便沿其传输时可以与其恒等组件一起计算。UNIVERSES，在所有14个常数上读取 [About]。张量–Hom 常数绑定 [@{c o x}]：R：RingObject@{c c c}, Ab@{o c}, RMod@{o x c c c}，固定为 Coextension@{c c c o x}, coex_adjunction@{c c c o x c}, zext_adjunction@{c c c o o x c c} 和 Adjunction@{o c c o c c c c x c o}。四个余连续性常数增加了 t（类的层级）、l 和 l0（余极限谓词的）以及 s（形状对象）。三个比较常数绑定 [@{a c p o x}]，就像 Instance/Mod/TensorMonad.v 一样。严格界限在所有地方都是 Set < o, c < o 和 c < x，并且在余连续性常数上 c < t, s < t；其余为 c <= l0, s <= l0, l0 <= l, o <= l, l <= t 和 o <= t，在比较上为 a <= o, c <= a, p <= a。没有方程，也没有其他 [Set]。首批载体，由 [About] 在捐赠者上：集合 < o 和 c < o，实例/Ab.v 的 [Ab]；c < x，实例/Mod.v 的 [RMod]；c < t 且 s < t，结构/限制/保持.v 的 [CocontinuousFunctor] (u4 < u, u5 < u) 和 [PreservesAllColimits] (u3 < u, u5 < u)。两个捐赠者携带其声明之外的等级，每个此类等级都是固定的，而不是留在封闭绑定器之外：[left_adjoint_Cocontinuous@{u u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10}] 的 u5，其类型或块都未提及，写作 c；[left_adjoint_preserves_colimits@{u u0 u1 u2 u3 u4 u5 u6 u7 u8 u9}] 的 u4，同样未提及，写作 c，其 u5 仅从下界受限，写作 t。在整个文件的副本中设置占位符，这三者中每一个都被拒绝，提示“Universe ... is unbound”；每个的 u6，在其类型中但未被块约束，作为占位符编译，由附加论点的最后等级固定，并写作 o。stdlib 的上限是继承而来的，每个由 [About] 放置在其 donor 的依赖锥的每个常量上，如 [Print All Dependencies] 在其最顶层载体上列出：在 Instance/Sets.v 的 [setoid_morphism_compose] 和 [setoid_morphism_id] 上的 compose 和 ID，通过 Instance/CMon.v 的 [cmon_hom_compose] 和 [cmon_hom_id]，并通过 [Ab]；prod_rect 在两个 setoid 重写上，Instance/Ab.v 的 [ab_cancel_l]，通过 BaseChange.v 的 [ZExtObj] 在命名 [TensorF] 的常量上，并通过 Coextension.v 的 [coex_group] 和 Structure/AbCategory.v 的 [Ab_AbEnriched] 在 [TensorF_right_adjoint_obj] 上，以及 Theory/Isomorphism.v 的 [iso_to_monic]，通过 Theory/Adjunction.v 的 [Build_Adjunction'] 在两个伴随中；Logic_lemmas.equality 在 Lib/Setoid.v 的 [eq_equivalence] 上以及投影（成对投影）在 [Build_Adjunction'] 上，都通过 [zext_adjunction] 和 [coex_adjunction]；以及 Projections（这个σ 投影) 在 Monad/Eilenberg/Moore.v 的 [EilenbergMoore] 上，通过 [EM_Forget]，对比常数上。未交付，进一步说明。对于一般环，R ⊗ (−) 没有连续性，无论通过此途径还是其他途径。双射的自然性没有超出 [Adjunction] 所包含的范围。没有与 Instance/Mod/HomTensor.v 和 Instance/Mod/Closed.v 的同调–张量双射进行比较，这些是在 R 上而非在 ℤ 上进行张量运算的。没有任何内容被注册为 [Instance]。
*)

(** ** The tensor–hom adjunction / ** 张量–Hom 伴随 *)

(*
 Ab(R ⊗ A, B) ≅ Ab(A, Hom_ℤ(R, B)): extension of scalars, then
 coextension, composed. 

 --------
 Ab(R ⊗ A, B) ≅ Ab(A, Hom_ℤ(R, B))：先扩展标量，然后共扩展，再组合。
*)

Definition TensorF_left_adjoint@{c o x} (R : RingObject@{c c c}) :
  @Adjunction@{o c c o c c c c x c o} Ab@{o c} Ab@{o c}
    (TensorF@{c c c o x} R)
    (RMod_Forget_Ab@{x o o c c c} R ◯ Coextension@{c c c o x} R) :=
  Adjunction_Compose (zext_adjunction@{c c c o o x c c} R)
    (coex_adjunction@{c c c o x c} R).

Example TensorF_right_adjoint_obj@{c o x} (R : RingObject@{c c c})
  (B : obj[Ab@{o c}]) :
  fobj[RMod_Forget_Ab@{x o o c c c} R ◯ Coextension@{c c c o x} R] B
  = hom_ab Ab_AbEnriched (ring_ab R) B := eq_refl.

Example tensor_hom_to@{c o x} (R : RingObject@{c c c})
  (A B : obj[Ab@{o c}])
  (φ : fobj[TensorF@{c c c o x} R] A ~{Ab@{o c}}~> B)
  (a : carrier (cmon_setoid A)) (r : carrier (rig_setoid (ring_rig R))) :
  @cmon_map (ab_cmon (ring_ab R)) (ab_cmon B)
    (cmon_map (to (@adj _ _ _ _ (TensorF_left_adjoint@{c o x} R) A B) φ) a)
    r
  = cmon_map φ (@ts_gen (ring_ab R) A
                  (rig_mul (ring_rig R) r (rig_one (ring_rig R))) a)
  := eq_refl.

Lemma tensor_hom_to_gen@{c o x} (R : RingObject@{c c c})
  (A B : obj[Ab@{o c}])
  (φ : fobj[TensorF@{c c c o x} R] A ~{Ab@{o c}}~> B)
  (a : carrier (cmon_setoid A)) (r : carrier (rig_setoid (ring_rig R))) :
  @cmon_map (ab_cmon (ring_ab R)) (ab_cmon B)
    (cmon_map (to (@adj _ _ _ _ (TensorF_left_adjoint@{c o x} R) A B) φ) a)
    r
  ≈ cmon_map φ (@ts_gen (ring_ab R) A r a).
Proof.
  apply (proper_morphism (cmon_map φ)).
  exact (@te_gen (ring_ab R) A _ _ _ _
           (rig_mul_one_r (ring_rig R) r) (reflexivity a)).
Qed.

Example tensor_hom_from@{c o x} (R : RingObject@{c c c})
  (A B : obj[Ab@{o c}])
  (ψ : A ~{Ab@{o c}}~>
         fobj[RMod_Forget_Ab@{x o o c c c} R ◯ Coextension@{c c c o x} R] B)
  (a : carrier (cmon_setoid A)) (r : carrier (rig_setoid (ring_rig R))) :
  cmon_map (from (@adj _ _ _ _ (TensorF_left_adjoint@{c o x} R) A B) ψ)
    (@ts_gen (ring_ab R) A r a)
  = @cmon_map (ab_cmon (ring_ab R)) (ab_cmon B) (cmon_map ψ a)
      (rig_mul (ring_rig R) (rig_one (ring_rig R)) r) := eq_refl.

Lemma tensor_hom_from_gen@{c o x} (R : RingObject@{c c c})
  (A B : obj[Ab@{o c}])
  (ψ : A ~{Ab@{o c}}~>
         fobj[RMod_Forget_Ab@{x o o c c c} R ◯ Coextension@{c c c o x} R] B)
  (a : carrier (cmon_setoid A)) (r : carrier (rig_setoid (ring_rig R))) :
  cmon_map (from (@adj _ _ _ _ (TensorF_left_adjoint@{c o x} R) A B) ψ)
    (@ts_gen (ring_ab R) A r a)
  ≈ @cmon_map (ab_cmon (ring_ab R)) (ab_cmon B) (cmon_map ψ a) r.
Proof.
  apply (proper_morphism
           (@cmon_map (ab_cmon (ring_ab R)) (ab_cmon B) (cmon_map ψ a))).
  exact (rig_mul_one_l (ring_rig R) r).
Qed.

(* * ** The square of the monad is a left adjoint / * ** 单子（Monad）的平方是一个左伴随 *)

Definition TensorF2_left_adjoint@{c o x} (R : RingObject@{c c c}) :
  @Adjunction@{o c c o c c c c x c o} Ab@{o c} Ab@{o c}
    (TensorF@{c c c o x} R ◯ TensorF@{c c c o x} R)
    ((RMod_Forget_Ab@{x o o c c c} R ◯ Coextension@{c c c o x} R)
       ◯ (RMod_Forget_Ab@{x o o c c c} R ◯ Coextension@{c c c o x} R)) :=
  Adjunction_Compose (TensorF_left_adjoint@{c o x} R)
    (TensorF_left_adjoint@{c o x} R).

(* * ** Cocontinuity, cone-level and apex-level / * ** 共连续性、锥体级和顶点级 *)

(*
 Left adjoints preserve colimits: Riehl's Theorem 4.6.2, here
 Adjunction/Continuity.v. 

 --------
 左伴随保持余极限：Riehl 定理 4.6.2，在这里 Adjunction/Continuity.v。
*)

Definition TensorF_cocontinuous@{c o x t l l0 s} (R : RingObject@{c c c}) :
  CocontinuousFunctor@{t l l l0 l s c o o x} (TensorF@{c c c o x} R) :=
  left_adjoint_Cocontinuous@{t l l l0 l x c o s o o c}
    (TensorF_left_adjoint@{c o x} R).

Definition TensorF2_cocontinuous@{c o x t l l0 s} (R : RingObject@{c c c}) :
  CocontinuousFunctor@{t l l l0 l s c o o x}
    (TensorF@{c c c o x} R ◯ TensorF@{c c c o x} R) :=
  left_adjoint_Cocontinuous@{t l l l0 l x c o s o o c}
    (TensorF2_left_adjoint@{c o x} R).

Definition TensorF_preserves_colimits@{c o x t l l0 s}
  (R : RingObject@{c c c}) :
  PreservesAllColimits@{t l x l0 s o c o} (TensorF@{c c c o x} R) :=
  left_adjoint_preserves_colimits@{t l x l0 o c t o s c o}
    (TensorF_left_adjoint@{c o x} R).

Definition TensorF2_preserves_colimits@{c o x t l l0 s}
  (R : RingObject@{c c c}) :
  PreservesAllColimits@{t l x l0 s o c o}
    (TensorF@{c c c o x} R ◯ TensorF@{c c c o x} R) :=
  left_adjoint_preserves_colimits@{t l x l0 o c t o s c o}
    (TensorF2_left_adjoint@{c o x} R).

(* * ** The forgetful functor against U^T ◯ K / * ** 忘记函子 对于 U^T ◯ K *)

(*
 EM_Forget ◯ EM_Comparison agrees with U on objects and arrows on the
 nose, and is isomorphic to it with identity components. 

 --------
 EM_Forget ◯ EM_Comparison 在对象和箭头上与 U 完全一致，并且与其同构且具有恒等分量。
*)

Example rmod_forget_comparison_obj@{a c p o x} (R : RingObject@{a c p})
  (M : obj[RMod@{o x a p c} R]) :
  fobj[EM_Forget (TensorF@{a c p o x} R)
         ◯ EM_Comparison (zext_adjunction@{a c p o o x a a} R)] M
  = fobj[RMod_Forget_Ab@{x o o a p c} R] M := eq_refl.

Example rmod_forget_comparison_map@{a c p o x} (R : RingObject@{a c p})
  (M N : obj[RMod@{o x a p c} R]) (f : M ~{RMod@{o x a p c} R}~> N) :
  fmap[EM_Forget (TensorF@{a c p o x} R)
         ◯ EM_Comparison (zext_adjunction@{a c p o o x a a} R)] f
  = fmap[RMod_Forget_Ab@{x o o a p c} R] f := eq_refl.

Definition rmod_forget_comparison@{a c p o x} (R : RingObject@{a c p}) :
  EM_Forget (TensorF@{a c p o x} R)
    ◯ EM_Comparison (zext_adjunction@{a c p o o x a a} R)
  ≈ RMod_Forget_Ab@{x o o a p c} R.
Proof.
  exists (fun M => @iso_id Ab@{o c} (fobj[RMod_Forget_Ab@{x o o a p c} R] M)).
  intros M N f.
  simpl. intros m. reflexivity.
Defined.
