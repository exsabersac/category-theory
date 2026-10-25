Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Mod.Free.

Generalizable All Variables.

(* * * The free R-module monad T_R on Set and its algebras, the R-modules / * * 集合上的自由 R-模幺半群 T_R 及其代数，即 R-模 *)

(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Springer GTM 5, 1998, §VI.4, Exercise 2, printed p. 146 (PDF
 p. 155) — maclane:VI.4:ex2
 Book: Riehl, "Category Theory in Context", Example 5.1.4(iii),
 printed p. 184 (PDF p. 204; the example opens on p. 183, PDF
 p. 203) — riehl:5.1:example4.  Her §5.3 opening construction,
 the case R = ℤ (riehl:5.3:construction-ab-monadic), is
 Instance/Ab/FreeMonad.v.
 nLab: https://ncatlab.org/nlab/show/free+module
 nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad
 nLab: https://ncatlab.org/nlab/show/monadic+functor

 WHAT THE BOOKS SAY, read from the page image and the PDF.  Mac Lane:
 "For any ring R with identity, the forgetful functor G: R-Mod→Set
 … has a left adjoint and so defines a monad ⟨T_R, η, μ⟩ in Set.
 (a) Prove that this monad may be described as follows: For each set
 X, T_R X is the set of all those functions f: X → R with only a
 finite number of non-zero values; for each function t: X → Y and
 each y ∈ Y, [(T_R t)f]_y = Σ′ f_x, with sum taken over all x ∈ X
 with tx = y; for each x ∈ X, η_X x: X → R is defined by
 (η_X x)x = 1, (η_X x)x′ = 0; for each k ∈ T_R(T_R X), μ_X k: X → R
 is defined for x ∈ X by (μ_X k)_x = Σ_f k_f f_x, the sum taken over
 all f ∈ T_R X.  (b) From this description, verify directly that
 ⟨T_R, η, μ⟩ is a monad.  (c) Show that the ⟨T_R, η, μ⟩-algebras are
 the usual R-modules, described not via addition and scalar multiple,
 but via all operations of linear combination (The structure map h
 assigns to each f the "linear combination with coefficients f_x for
 each x ∈ X".)"  Riehl: R[A] is "the set of finite formal R-linear
 combinations of elements of A.  Formally, … a finitely supported
 function χ : A → R"; η_A sends a to "the function χ_a : A → R that
 sends a to the multiplicative unit and every other element to zero";
 μ_A is "defined by distributing the coefficients and consolidating
 terms in a formal sum of formal sums".

 THE MONAD.  The free module and its adjunction are
 Instance/Mod/Free.v's (PR #1147), the shared route: no second free
 module and no second free functor.  [FreeModF] is U ◯ F with F
 [FreeMod R] and U [RMod_Forget R]; [FreeModMonad] is T_R,
 Monad/Comparison.v's [Adjunction_Induced_Monad] of
 [free_module_adjunction_hom], the hom-set form of the same adjunction
 #472 adds to Free.v because the universal-arrow form's counit does not
 compute (Free.v's CORRECTION (#472): two [Qed] layers).  At [eq_refl]:
 T_R X is the free module's setoid ([TR_obj]) on the formal
 combinations ([TR_carrier]); η is the insertion ([TR_ret]), x ↦ ⟨x⟩
 ([TR_ret_fun]); μ = U ε F ([TR_join_counit]) flattens ([TR_join_gen],
 [TR_join_fun], [TR_join_zero]) and sends r·⟨t⟩ + s·⟨t′⟩ to r·t + s·t′
 ([TR_join_lc]).  T_R u is the relabelling at ≈ ([TR_map_equiv]) and is
 refused at [eq_refl] (Test/ProbeFreeModule472.v, R9 to R11).

 PART (a), THREE READINGS.  (i) Unconditionally, on formal linear
 combinations Σ rᵢ·⟨xᵢ⟩ ([fv_lc] of a list of pairs; every element is
 one, Free.v's [fv_normal_form]): T_R u relabels each pair
 ([TR_map_lc]), η x ≈ 1·⟨x⟩ ([TR_ret_lc]), and μ scales each inner
 combination by its coefficient and concatenates ([TR_join_lc_flat]):
 Riehl's "distributing the coefficients".  (ii) Under a decider for
 X's ≈, the coefficient f_y is [fv_coef]: the linear extension, into R
 as a module over itself, of Free.v's indicator [fv_probe_at] (no new
 indicator).  Mac Lane's formulas: (η x)_x = 1 and (η x)_{x′} = 0 for
 x′ ≉ x, Leibniz as he writes them ([fv_coef_ret_same],
 [fv_coef_ret_other]); [(T_R t)f]_y is f evaluated on the indicator of
 the fibre over y ([fv_coef_map]), on a combination the sum Σ′ of the
 coefficients whose points t sends to y ([fv_coef_map_lc],
 [fv_fibre_sum]; the induction is [fv_eval_fibre_lc], which the
 satellite's [fv_coef_lc] shares), all three at ≈; (μ k)_x is the
 extension of f ↦ f_x evaluated at k ([fv_coef_join]) and, at
 k = Σ rᵢ·⟨fᵢ⟩, Σ rᵢ·(fᵢ)_x ([fv_coef_join_lc]), both Leibniz.  The
 coefficient respects ≈ in its point, Leibniz
 ([fv_coef_respects_point]).  Every element is finitely supported
 ([fv_coef_support]); over ℤ on Free.v's two generators the
 coefficients compute (the satellite's [TR_coef_Z_true],
 [TR_coef_Z_false], [TR_coef_Z_join]).  (iii) The satellite
 Instance/Mod/FreeMonad/FinSupp.v: T_R X ≅ the finitely supported
 X → R in Sets ([TR_FinSupp_iso]), part (a)'s literal sentence, with
 the uniqueness of coefficients ([fv_lc_unique]) and its converse
 ([fv_coef_injective]).
 WHY A DECIDER: the indicator of a point, hence f ↦ f_x and Riehl's
 χ_a, cannot be written without deciding x ≈ y (Free.v's header), and a
 functor out of [Sets] meets setoids with no decider.  Read literally,
 Mac Lane's μ sums over f ∈ T_R X with k's coefficient k_f, which needs
 a decider for T_R X's ≈, and for X inhabited that yields one for R's
 (r·⟨x⟩ ≈ s·⟨x⟩ iff r ≈ s, at any point x of X, Free.v's
 [free_module_scalars_faithful]); the list form [fv_coef_join_lc] needs
 only X's.

 PART (b).  [FreeModF_direct] is an endofunctor of Sets on the same
 objects whose action IS the relabelling ([TR_direct_map],
 [TR_direct_map_gen]); [FreeModMonad_direct] is [Build_Monad] with η the
 insertion and μ the fold of the identity, every law a Leibniz equation
 proved by induction on combinations ([fv_relabel_id],
 [fv_relabel_comp], [fv_flatten_assoc], [fv_flatten_relabel_insert],
 [fv_flatten_natural]), no adjunction cited.  Its η and μ ARE T_R's at
 [eq_refl] ([TR_direct_ret], [TR_direct_join]); its endofunctor is
 T_R's with identity components ([FreeModF_direct_iso],
 [TR_direct_iso_component]), the two actions on arrows refused equal at
 [eq_refl] (R14).  It verifies the laws on the formal combinations of
 reading (i), not on the functions of reading (iii).

 PART (c).  [TRAlg] is Set^{T_R}; [RMod_K] is Monad/Comparison.v's
 [EM_Comparison] of the hom-set form: K M = ⟨M, U ε_M⟩, its structure map
 the fold of the identity, i.e. "the linear combination" ([RMod_K_alg_fun],
 [RMod_K_alg_lc]), with ⟨x⟩ ↦ x, 0 ↦ 0, ⟨x⟩ + ⟨y⟩ ↦ x + y, −⟨x⟩ ↦ −x and
 r·⟨x⟩ ↦ r·x ([RMod_K_alg_*]) and K f = f ([RMod_K_map]), all at [eq_refl].
 K commutes with the right adjoints and with the left ones, each up to a
 natural isomorphism whose components are identities ([RMod_K_Forget],
 [RMod_K_Free]): Monad/Comparison.v's [EM_Comparison_Forget] and
 [EM_Comparison_Free] build them so (its header; [iso_id], and
 [EM_Comparison_Free_iso]'s identity arrows), and all four end [Qed]:
 that the components are identities is read from that file's source, and
 no readback pins it here.  CORRECTION (#482): [EM_Comparison_Forget]
 and [EM_Comparison_Free] end [Defined] since #482, and
 Monad/Comparison/Resolution.v reads their components back at
 [eq_refl] ([EM_Comparison_Forget_components],
 [EM_Comparison_Free_components]); [RMod_K_Forget] and [RMod_K_Free]
 still end [Qed], and no readback here pins them.
 [EM_to_RModS] (S: algebras of a monad on Sets; Instance/Mod/TensorMonad.v's
 [EM_to_RMod] is the R ⊗ − monad's on Ab) sends (A, h) to [tr_alg_rmod]: 0 =
 h⟨⟩, a + b = h(⟨a⟩ + ⟨b⟩), −a = h(−⟨a⟩), r·a = h(r·⟨a⟩) ([EM_to_RModS_*]);
 each module law is one instance of [tr_alg_eval_respects], and h IS linear
 combination in that module, at ≈ ([tr_alg_fold]).  The carrier's
 [PropEquiv] costs no hypothesis: x ≈ y iff ⟨x⟩ ≈ ⟨y⟩ in T_R A
 ([tr_alg_prop], [EM_to_RModS_prop]; #466's [talg_PropEquiv] pattern).
 [RMod_EM_iso : RMod R ≅[Cat] TRAlg] has legs K and [EM_to_RModS]
 ([RMod_EM_iso_to], [RMod_EM_iso_from]) and identity components to and from
 at [eq_refl] ([RMod_EM_iso_to_from_component],
 [RMod_EM_iso_from_to_component]; the equivalence's too,
 [RMod_EM_counit_component], [RMod_EM_unit_component]); it is built from the
 component isomorphisms [RMod_EM_counit_iso] and [RMod_EM_unit_iso], as #470
 and #471 build theirs, Theory/Equivalence.v's [Equivalence_to_Cat_Iso]
 leaving one component refused (R21).  By Instance/Cat.v an isomorphism in
 Cat is an equivalence of categories; the strict identity is refused (R15 to
 R20).  [RMod_EM_equivalence] is the equivalence and [RMod_Forget_Monadic :
 Monadic (RMod_Forget R)] the monadicity.  The round trips keep carrier,
 zero, sum, negation, action and maps at [eq_refl] ([RMod_rt_*],
 [TRAlg_rt_*]).  The argument is the one #470 and #471 make for their
 monads, and Instance/Ab/FreeMonad.v repeats it without the action;
 issue #1357 tracks a shared Eilenberg–Moore lemma for term-model monads
 that would keep the identity components.

 RIEHL'S 5.1.4(iii) is T_R itself, reading (i) her formal combinations
 and (iii) her χ, η her χ_a by (ii), μ's distribution by
 [TR_join_lc_flat] and the consolidation of terms by FinSupp.v's
 [fv_collect]; her free vector space monad is T_R at [field_ring F]
 (Instance/FdVect.v's [Vct_F F] is [RMod (field_ring F)] by definition,
 read back at [eq_refl] by Instance/Vect/Free.v's [Vct_F_is_RMod]), and
 her free abelian group monad Instance/Ab/FreeMonad.v.

 THE ISSUE'S PREMISES, dated.  Issue #472 was filed on 2026-07-23.  Its
 "no R-Mod category" was accurate when filed and has been stale since
 PR #1117 (merged 2026-08-15, Instance/Mod.v, closing #258); "no ring
 category" since PRs #1090 and #1091 (both merged 2026-08-14,
 Theory/Algebra/Rig.v's rings and Instance/Rng.v).  "No free-R-module
 monad" held until #472, the free module and its adjunction dating from
 PR #1147 (merged 2026-08-18); "no finitely-supported-function functor"
 still holds, FinSupp being a setoid for each X and not a functor.  What
 it says of Instance/CMon.v and Structure/Abelian.v is still accurate.
 Its dependencies #258 and #360 were closed on 2026-08-15 and
 2026-08-31.  Monad/Instance/ does not exist; the files are this one,
 its satellite and Instance/Ab/FreeMonad.v.  Its "CLAUDE.md Key Files
 index" was accurate when filed and has been stale since PR #1284
 (merged 2026-09-09), which moved the index to docs/INDEX.md.

 STRENGTHS.  Every [Example] holds at [eq_refl], and
 Test/ProbeFreeModule472.v restates each one (its RESTATEMENTS).  At ≈ only:
 [TR_map_equiv], [tr_alg_step], [tr_alg_fold], [tr_alg_hom_step] (the
 twins of Instance/Ab/FreeMonad.v's four), [TR_map_lc], [TR_ret_lc],
 [TR_join_lc_flat], [fv_coef_map], [fv_coef_map_lc] and the inverse laws of
 the isomorphism in Cat.  At ≈ as R's own laws are (r·1 ≈ r, r·0 ≈ 0,
 0 + s ≈ s): [fv_eval_fibre_lc].  Leibniz, by induction, stronger than ≈:
 [fv_eval_relabel], [fv_eval_flatten], [fv_relabel_lc], the five laws of
 part (b), [fv_coef_join], [fv_coef_join_lc], [fv_coef_respects_point] and
 [tr_fold_is_alg_eval]; Leibniz by cases on the decider, as Mac Lane writes
 them: [fv_coef_ret_same] and [fv_coef_ret_other].  Eleven proofs
 end [Defined] (counted by token) and ten are load-bearing, measured by
 closing each alone [Qed] in a renamed copy of #472's five files and the
 probe and naming the first command that then stops: [FreeModF_direct]
 ([FreeModMonad_direct]), [FreeModMonad_direct] ([TR_direct_ret]),
 [FreeModF_direct_iso] ([TR_direct_iso_component]), [tr_alg_prop]
 ([EM_to_RModS_prop]), [tr_alg_hom_rmod] ([EM_to_RModS]), [EM_to_RModS]
 ([RMod_EM_counit_iso]), [RMod_EM_counit_iso] and [RMod_EM_unit_iso]
 ([RMod_EM_equivalence]), [RMod_EM_equivalence] ([RMod_EM_counit_component])
 and [RMod_EM_iso] ([RMod_EM_iso_to]); [RMod_Forget_Monadic] is [Defined] by
 the data convention only (closed [Qed], nothing stops).  Thirty-four
 lemmas end [Qed].

 UNIVERSES, read off [About] (every name, by script).  The section
 [FreeModMonad] binds R : RingObject@{a c p} (roles auxiliary, carrier,
 proof) and Sets@{c so}, and every name in it binds a c p so first, with c <
 so, c <= a and p <= a.  A closed binder is refused, [FreeMod]'s internal
 levels being unbound, so each declares an extensible one.  Beyond a c p
 so, fifty-four names bind six, T_R and the names built on it other than
 those below ([RMod_K_Forget] among them): the module category's object
 level m (Set < m, c < m, a <= m, from Instance/Mod.v's [RMod]), the
 internal level of Theory/Functor.v's [Compose] (c < it) and [FreeMod]'s
 four internal levels; twelve bind m and the four: K, its ten readbacks
 ([RMod_K_carrier] to [RMod_K_alg_lc]) and [RMod_K_Free]; the fifteen
 relabelling and direct names bind m alone; [fv_lc_inner] binds m and one
 further level, bounded only by c < it; [fv_lc_map],
 [fv_lc_flat] and [fv_eq_of_eq] nothing more; six readbacks comparing across
 a composite bind a second copy of [FreeMod]'s internal levels (eleven or
 fourteen levels in all), the copies never identified by unification, and
 three names bind one level more, an equation's sort ([TR_carrier]) or the
 ring's relation ([tr_alg_smul_respects], [tr_alg_rmod]).  The isomorphism
 in Cat and its readbacks bind k (c < k, so < k, Instance/Cat.v's [Cat]),
 and there m is so (Set < so, a <= so).  The section [Coefficients] binds R
 : RingObject@{c c c}: [fv_probe_at] places [Ring_RMod R] in [RMod R], which
 identifies the ring's three levels with the generating setoid's carrier
 level; that identification is Free.v's ([About] gives [fv_probe_at] one
 level for its five), not new, and it is written in the binder rather than
 left to minimization.  [fv_coef] binds a fourth level, bounded only by
 c < it, and so do the names whose statements leave it so
 ([fv_coef_ret_same], [fv_coef_ret_other], [fv_coef_respects_point],
 [fv_lc_weighted], [fv_coef_support]).  No [Set] but bounds Set < m, and no
 equation, in any block; no explicit universe instance of a constant of
 this route is written.  On Coq 8.19.2 and 8.20.1 the 79 names of the
 section [FreeModMonad] that bind [FreeMod]'s internal levels bind exactly
 one level more, and the other 32 the same levels, compared by [About] on
 every name; no equation and no [Set] but bounds there either.

 NOT DELIVERED.  A strict identity of R-Mod and Set^{T_R} (refused) and
 an isomorphism in Instance/StrictCat.v.  A computing T_R u: the action
 on arrows is [FreeMod]'s.  The monad structure transported to the
 finitely supported functions, with Mac Lane's formulas as its
 definitions and [TR_FinSupp_iso] natural; part (b) on that
 description.  Coefficients without a decider.  Beck's route to
 monadicity, and the comparison with Instance/Mod/TensorMonad.v's
 R ⊗ − on Ab. 

 --------
 书籍：Mac Lane，《为工作数学家准备的范畴论》，第2版，斯普林格GTM 5，1998年，第VI.4节，练习2，印刷页146（PDF页155）—— maclane:VI.4:ex2
 书籍：Riehl，《上下文中的范畴论》，例5.1.4(iii)，印刷页184（PDF页204；例子开始于印刷页183，PDF页203）—— riehl:5.1:example4。她在第5.3节开头的构造，R=ℤ的情况（riehl:5.3:construction-ab-monadic），是Instance/Ab/FreeMonad.v。
 nLab: https://ncatlab.org/nlab/show/free+module
 nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad
 nLab: https://ncatlab.org/nlab/show/monadic+functor书中所说，阅读页面图片和PDF文件。麦克莱恩：
 “对于任意带恒等的环 R，遗忘函子 G： R-Mod→Set
 …有一个左伴随，因此定义了Set中的单子⟨T_R、η、μ⟩。（a） 证明该单子可以描述如下：对于每个集合
 X，T_R X 是所有仅包含 a 的函数 f： X → R 的集合
 有限个非零值;对于每个函数 t： X → Y 和
 每个y∈Y，[(T_R t)f] _y = Σ′ f_x，求和取所有x∈X的求和
 其中 tx = y;对于每个 x ∈ X，η_X x： X → R 定义为
 （η_X x）x = 1， （η_X x）x′ = 0;对于每个 k 个 ∈ T_R（T_R X），μ_X k： X 与 R →
 对于x∈X，定义为（μ_X k）_x = Σ_f k_f f_x，即取下的和
 所有 f ∈ T_R X。（b） 根据此描述，直接验证
 ⟨T_R，η，μ⟩是一个单子。(c) 证明 ⟨T_R, η, μ⟩-代数就是通常的 R-模，这里不是通过加法和标量乘法来描述，而是通过所有线性组合的运算（结构映射 h 将每个 f 分配为“对每个 x ∈ X，系数为 f_x 的线性组合”）。Riehl: R [A] 是“集合 A 的有限形式 R-线性组合。形式上 … 是一个有限支撑的函数 χ : A → R”；η_A 将 a 映射为“函数 χ_a : A → R，χ_a 将 a 映射为乘法单位，其他元素映射为零”；μ_A 定义为“通过分配系数并合并形式和的形式和中的项”.单子。自由模及其伴随是 Instance/Mod/Free.v 的（PR #1147），共享路径：没有第二个自由模，也没有第二个自由函子。[FreeModF] 是 U ◯ F，其中 F [FreeMod R] 和 U [RMod_Forget R]；[FreeModMonad] 是 T_R，Monad/Comparison.v 的 [Adjunction_Induced_Monad] 关于 [free_module_adjunction_hom] 的同调集形式的相同伴随 #472 添加到 Free.v，因为通用箭头形式的余单位不可计算（Free.v 的更正（#472）：两层 [Qed]）。在 [eq_refl]：T_R X 是自由模的集合等价类（[TR_obj]），关于形式组合（[TR_carrier]）；η 是插入（[TR_ret]），x ↦ ⟨x⟩（[TR_ret_fun]）；μ = U ε F（[TR_join_counit]）展开（[TR_join_gen]，[TR_join_fun]，[TR_join_zero]）并将 r·⟨t⟩ + s·⟨t′⟩ 映射为 r·t + s·t′（[TR_join_lc]）。T_R u 是在 ≈ ([TR_map_equiv]) 处的重新标记，并在 [eq_refl] 处被拒绝 (Test/ProbeFreeModule472.v, R9 到 R11)。部分（a），三种读法。(i) 无条件地，在形式线性组合 Σ rᵢ·⟨xᵢ⟩（[fv_lc]，一个对的列表；每个元素都是 Free.v 的 [fv_normal_form]）：T_R 重标记每一对 ([TR_map_lc])，η x ≈ 1·⟨x⟩ ([TR_ret_lc])，而 μ 按系数缩放每个内部组合并进行连接 ([TR_join_lc_flat])：Riehl 的“分配系数”。(ii) 在 X 的 ≈ 判定器下，系数 f_y 是 [fv_coef]：Free.v 的指标 [fv_probe_at] 在线性扩展到自身作为模块的 R 中（没有新的指标） 。Mac Lane 公式：（η x）_x = 1 和 （η x）_{x′} = 0 对
 x′ ≉ x，莱布尼茨如其所述（[fv_coef_ret_same]，
 [fv_coef_ret_other]）;[(T_R t)f] _y 在 的指示符上 f 被评估
 纤维在 y 上的 （[fv_coef_map]），在 的和 Σ′ 上
 点 t 映射为 y 的系数（ [fv_coef_map_lc] ，
 [fv_fibre_sum];归纳法为[fv_eval_fibre_lc]，其中
 卫星的 [fv_coef_lc] 份额），三者均为 ≈;（μ K）_x 是
 在 k （[fv_coef_join] ） 处计算 f ↦ f_x 的扩张，在
 k = Σ ri·⟨fi⟩， Σ ri·（fi）_x （[fv_coef_join_lc]），两者皆为莱布尼茨。该
 系数在其点上尊重≈，莱布尼茨
 （ [fv_coef_respects_point] ）每个元素都是有限支持的
 （[fv_coef_support]）;在Free.v的两个生成元上，Z
 系数计算（卫星[TR_coef_Z_true]，
 [TR_coef_Z_false]，[TR_coef_Z_join]）。(iii) 卫星  
 Instance/Mod/FreeMonad/FinSupp.v：T_R X ≅ 在集合中有限支持的  
 X → R（[TR_FinSupp_iso]），第 (a) 部分的字面句子，具有系数的唯一性（[fv_lc_unique]）及其逆命题（[fv_coef_injective]）。为什么需要判定器：点的指示函数，因此 f ↦ f_x 以及 Riehl 的 χ_a，不能在不判定 x ≈ y 的情况下写出（Free.v 的头部），而来自 [Sets] 的函子会遇到没有判定器的集合同态。按字面理解，Mac Lane 的 μ 对 f ∈ T_R X 的和，其中 k 的系数为 k_f，需要 T_R X 的 ≈ 判定器，而对于非空 X，这会产生一个 R 的判定器（r·⟨x⟩ ≈ s·⟨x⟩ 当且仅当 r ≈ s，对于 X 的任意点 x，Free.v 的 [free_module_scalars_faithful]）；列表形式 [fv_coef_join_lc] 仅需要 X 的判定器。部分(b)。[FreeModF_direct] 是集合的一个端函子，作用于相同的对象，其作用是重命名（[TR_direct_map]，[TR_direct_map_gen]）；[FreeModMonad_direct] 是 [Build_Monad]，η 是插入，μ 是恒等的折叠，每条定律都是通过组合归纳证明的莱布尼茨方程（[fv_relabel_id]，[fv_relabel_comp]，[fv_flatten_assoc]，[fv_flatten_relabel_insert]，[fv_flatten_natural]），未引用任何伴随。它的 η 和 μ 是 [eq_refl] 的 T_R（[TR_direct_ret]，[TR_direct_join]）；它的端函子是具有恒等分量的 T_R（[FreeModF_direct_iso]，[TR_direct_iso_component]），两个箭头上的操作在 [eq_refl] (R14) 处不被认为相等。它验证了关于阅读的形式组合 (i) 的定律，而不是关于阅读的函数 (iii) 的定律。第(c)部分。[TRAlg] 是 Set^{T_R}；[RMod_K] 是 Monad/Comparison.v 的 [EM_Comparison]，同态集形式为：K M = ⟨M, U ε_M⟩，其结构映射为恒等映射的折叠，即“线性组合”([RMod_K_alg_fun], [RMod_K_alg_lc])，其中 ⟨x⟩ ↦ x, 0 ↦ 0, ⟨x⟩ + ⟨y⟩ ↦ x + y, −⟨x⟩ ↦ −x 以及 r·⟨x⟩ ↦ r·x ([RMod_K_alg_*])，并且 K f = f ([RMod_K_map])，全部位于 [eq_refl]。K 与右伴随以及左伴随交换，每个都通过自然同构，其分量为恒等映射 ([RMod_K_Forget], [RMod_K_Free])：Monad/Comparison.v 的 [EM_Comparison_Forget] 和 [EM_Comparison_Free] 构造了它们 (其头部；[iso_id], 以及 [EM_Comparison_Free_iso] 的恒等箭头)，且所有四个都以 [Qed] 结束：组件是恒等映射的信息可从该文件源码中读取，而没有回读将其固定于此。更正 (#482)：[EM_Comparison_Forget] 和 [EM_Comparison_Free] 自 #482 以来结束 [Defined]，Monad/Comparison/Resolution.v 在 [eq_refl]（[EM_Comparison_Forget_components]，[EM_Comparison_Free_components]）回读它们的组件；[RMod_K_Forget] 和 [RMod_K_Free] 仍然结束 [Qed]，并且这里没有回读固定它们。[EM_to_RModS]（S：集合上单子的代数；Instance/Mod/TensorMonad.v 的 [EM_to_RMod] 是 Ab 上的 R ⊗ − 单子）将 (A, h) 发送到 [tr_alg_rmod]：0 = h⟨⟩，a + b = h(⟨a⟩ + ⟨b⟩)，−a = h(−⟨a⟩)，r·a = h(r·⟨a⟩)（[EM_to_RModS_*]）；每条模律都是 [tr_alg_eval_respects] 的一个实例，并且 h 是该模中的线性组合，在 ≈（[tr_alg_fold]）处。载体的 [PropEquiv] 不需要假设：x ≈ y 当且仅当 ⟨x⟩ ≈ ⟨y⟩ 在 T_R A 中（[tr_alg_prop]，[EM_to_RModS_prop]；#466 的 [talg_PropEquiv] 模式）。[RMod_EM_iso : RMod R ≅[Cat]  TRAlg] 有腿 K 和  [EM_to_RModS] （[RMod_EM_iso_to], [RMod_EM_iso_from]）以及从和到的同一分量在 [eq_refl]（[RMod_EM_iso_to_from_component], [RMod_EM_iso_from_to_component]；等价性也是，[RMod_EM_counit_component], [RMod_EM_unit_component]）；它是由分量同构 [RMod_EM_counit_iso] 和 [RMod_EM_unit_iso] 构建的，就像 #470 和 #471 构建它们的那样，Theory/Equivalence.v 的 [Equivalence_to_Cat_Iso] 保留了一个被拒绝的分量（R21）。根据 Instance/Cat.v，在 Cat 中的同构是范畴的等价；严格同一性被拒绝（R15 到 R20）。[RMod_EM_equivalence] 是等价，[RMod_Forget_Monadic : Monadic (RMod_Forget R)] 是幺半性。环回保持载体、零、和、取负、作用以及映射在 [eq_refl]（[RMod_rt_*], [TRAlg_rt_*]）。这个论证是 #470 和 #471 对它们的单子提出的论证，而 Instance/Ab/FreeMonad.v 在没有该作用的情况下重复了这个论证；问题 #1357 跟踪了一个共享的 Eilenberg–Moore 引理，用于保持身份分量的项模型单子。

 RIEHL 的 5.1.4(iii) 就是 T_R 本身，读取 (i) 她的形式组合和 (iii) 她的 χ，通过 (ii) 的 η 她的 χ_a，通过 [TR_join_lc_flat] 的 μ 分配，以及 FinSupp.v 的 [fv_collect] 的项合并；她的自由向量空间单子在 [field_ring F] 是 T_R（Instance/FdVect.v 的 [Vct_F F] 由定义是 [RMod (field_ring F)]，通过 Instance/Vect/Free.v 的 [Vct_F_is_RMod] 回读于 [eq_refl]），而她的自由阿贝尔群单子是 Instance/Ab/FreeMonad.v。问题的前提，注明日期。第472期于2026-07-23提交。其“无R-模类别”在提交时是准确的，自从PR #1117（于2026-08-15合并，Instance/Mod.v，关闭#258）之后就已过时；“无环类别”自PR #1090和#1091（均于2026-08-14合并，Theory/Algebra/Rig.v的环和Instance/Rng.v）之后就存在。“无自由R-模Monad”一直成立直到#472，自由模及其伴随关系源自PR #1147（于2026-08-18合并）；“无有限支撑函数函子”仍然成立，因为FinSupp是每个X的集合等价类而不是函子。关于Instance/CMon.v和Structure/Abelian.v的内容仍然准确。其依赖项#258和#360分别于2026-08-15和2026-08-31关闭。Monad/Instance/不存在；相关文件为此文件、其附属文件以及Instance/Ab/FreeMonad.v。它的“CLAUDE.md 关键文件索引”在归档时是准确的，但自 PR #1284（于 2026-09-09 合并）之后一直过时，该 PR 已将索引移动到 docs/INDEX.md。优势。每个 [Example] 在 [eq_refl] 都成立，并且 Test/ProbeFreeModule472.v 重述每一个（它的重述）。在 ≈ 仅有：[TR_map_equiv]、[tr_alg_step]、[tr_alg_fold]、[tr_alg_hom_step]（Instance/Ab/FreeMonad.v 的四个的双胞胎）、[TR_map_lc]、[TR_ret_lc]、[TR_join_lc_flat]、[fv_coef_map]、[fv_coef_map_lc] 以及 Cat 中同构的逆律。在 ≈ 中，作为 R 自身的律（r·1 ≈ r, r·0 ≈ 0, 0 + s ≈ s）：[fv_eval_fibre_lc]。莱布尼茨，通过归纳，比 ≈ 强：[fv_eval_relabel]、[fv_eval_flatten]、[fv_relabel_lc]、第（b）部分的五条定律、[fv_coef_join]、[fv_coef_join_lc]、[fv_coef_respects_point] 和 [tr_fold_is_alg_eval]；莱布尼茨通过判定器的情况，就像 Mac Lane 写的那样：[fv_coef_ret_same] 和 [fv_coef_ret_other]。十一个证明
 以 [Defined] 结尾（按标记计数），其中十个是承重的，通过在 #472 的五个文件的重命名副本中单独关闭每个 [Qed] 并测量探针，命名随后停止的第一个命令：[FreeModF_direct] 
 （[FreeModMonad_direct]）、[FreeModMonad_direct] （[TR_direct_ret]）、
 [FreeModF_direct_iso] （[TR_direct_iso_component]）、[tr_alg_prop] 
 （[EM_to_RModS_prop]）、[tr_alg_hom_rmod] （[EM_to_RModS]）、[EM_to_RModS] 
 （[RMod_EM_counit_iso]）、[RMod_EM_counit_iso] 和 [RMod_EM_unit_iso] 
 （[RMod_EM_equivalence]）、[RMod_EM_equivalence] （[RMod_EM_counit_component]）
 和 [RMod_EM_iso] （[RMod_EM_iso_to]）；[RMod_Forget_Monadic] 按数据约定仅是 [Defined]（关闭 [Qed]，没有任何停止）。三十四个引理以 [Qed] 结束。宇宙，逐一读取 [About]（每个名称，按脚本）。部分 [FreeModMonad] 绑定 R：RingObject@{a c p}（角色：辅助、载体、证明）和 Sets@{c so}，并且其中的每个名称首先绑定 a c p so，其中 c < so，c <= a 且 p <= a。封闭绑定器被拒绝，[FreeMod] 的内部层次未绑定，因此每个都声明一个可扩展的层次。超出 a c p 的范围，因此，五十四个名字绑定六个，T_R 及其上构建的名字（不包括下面的 [RMod_K_Forget]）：模块类别的对象级别 m（Set < m, c < m, a <= m，来源于 Instance/Mod.v 的 [RMod]）、Theory/Functor.v 的内部级别 [Compose]（c < 它）以及 [FreeMod] 的四个内部级别；十二个绑定 m 和这四个：K、它的十个回读（[RMod_K_carrier] 到 [RMod_K_alg_lc]）以及 [RMod_K_Free]；十五个重命名和直接名字仅绑定 m；[fv_lc_inner] 绑定 m 和另外一个级别，仅由 c < 它 限定；[fv_lc_map]、[fv_lc_flat] 和 [fv_eq_of_eq] 不再绑定其他内容；六个跨复合对象比较的回读绑定 [FreeMod] 内部级别的第二份副本（总共十一或十四级），这些副本从未通过统一标识，还有三个名字绑定一个额外级别，一个 equation 的类型 ([TR_carrier]) 或环的关系 ([tr_alg_smul_respects], [tr_alg_rmod])。在 Cat 中的同构及其回读绑定 k（c < k，因此 < k，Instance/Cat.v 的 [Cat]），且 there m 是 so（Set < so, a <= so）。段 [Coefficients] 绑定 R : RingObject@{c c c}：[fv_probe_at] 将 [Ring_RMod R] 放置在 [RMod R] 中，这将环的三个层级与生成的集合对象的承载层级对应；这种对应是 Free.v 的（[About] 给 [fv_probe_at] 的五个元素各一个层级），不是新的，并且它写在绑定器中而不是留给最小化。[fv_coef] 绑定第四层，仅被 c < it 限制，其声明保持这种状态的名称也如此（[fv_coef_ret_same]，[fv_coef_ret_other]，[fv_coef_respects_point]，[fv_lc_weighted]，[fv_coef_support]）。没有 [Set]，但限制了 Set < m，并且没有任何块中的方程；没有写出此路径常量的显式宇宙实例。在 Coq 8.19.2 和 8.20.1 上，绑定 [FreeMod] 内部层级的 [FreeModMonad] 部分的 79 个名称恰好绑定多一级层级，而另外 32 个名称绑定相同的层级，通过 [About] 在每个名称上进行比较；没有方程，也没有 [Set]，但那里有界限。

 未交付。在 R-Mod 和 Set^{T_R} 中严格的同一性（被拒绝）以及在 Instance/StrictCat.v 中的一个同构。计算 T_R u: 箭头上的作用是 [FreeMod] 的。单子结构被传递到有限支持函数，其定义使用 Mac Lane 的公式并且 [TR_FinSupp_iso] 自然；有关该描述的第 (b) 部分。系数没有判定器。Beck 通向单性的方法，以及与 Instance/Mod/TensorMonad.v 中 R ⊗ − 在 Ab 上的比较。
*)

(* ------------------------------------------------------------------------ *)
(* * ** T_R, the monad of the adjunction Set ⇀ R-Mod / * ** T_R，集合 ⇀ R-模的伴随函子上的幺半群 *)

Section FreeModMonad.

Universes a c p so.
Context (R : RingObject@{a c p}).

Local Notation scalar := (carrier (rig_setoid (ring_rig R))).

(* T_R = U ◯ F, with F Instance/Mod/Free.v's [FreeMod]. / T_R = U ◯ F，其中 F 是 Instance/Mod/Free.v 的 [FreeMod] 。 *)
Definition FreeModF@{+} : Sets@{c so} ⟶ Sets@{c so} :=
  RMod_Forget R ◯ FreeMod R.

(* T_R, the monad of the hom-set form of the free-forgetful adjunction. / T_R，自由-遺忘伴随的同集形式的单子。 *)
Definition FreeModMonad@{+} : @Monad Sets@{c so} FreeModF :=
  Adjunction_Induced_Monad (free_module_adjunction_hom R).

(* The relabelling of a combination along u: the fold of insert ∘ u. / 沿着 u 的组合重新标记：插入 ∘ u 的折叠。 *)
Definition fv_relabel@{+} {X Y : Sets@{c so}} (u : X ~{Sets@{c so}}~> Y)
  (t : @FVTerm R X) : @FVTerm R Y :=
  fv_eval (W := FreeModObject Y) (fv_insert Y ∘ u) t.

(* A combination of combinations, flattened: the fold of the identity. / 组合的组合，平展：身份的折叠。 *)
Definition fv_flatten@{+} {X : Sets@{c so}}
  (k : @FVTerm R (RMod_Forget R (FreeModObject X))) : @FVTerm R X :=
  fv_eval (W := FreeModObject X)
    (@id Sets@{c so} (RMod_Forget R (FreeModObject X))) k.

(* T_R X is the free module's setoid, whose carrier is the formal combinations. / T_R X 是自由模的集合归类，其承载体是形式组合。 *)
Example TR_obj@{+} (X : Sets@{c so}) :
  fobj[FreeModF] X = RMod_Forget R (FreeModObject X) := eq_refl.

Example TR_carrier@{+} (X : Sets@{c so}) :
  carrier (fobj[FreeModF] X) = @FVTerm R X := eq_refl.

(* η_X is the insertion of the basis, as a setoid map, and x ↦ ⟨x⟩. / η_X 是基的插入，作为一个集合同态映射，并且 x ↦ ⟨x⟩。 *)
Example TR_ret@{+} (X : Sets@{c so}) :
  @ret _ _ FreeModMonad X = fv_insert X := eq_refl.

Example TR_ret_fun@{+} (X : Sets@{c so}) (x : carrier X) :
  @ret _ _ FreeModMonad X x = fv_gen x := eq_refl.

(* μ = U ε F. *)
Example TR_join_counit@{+} (X : Sets@{c so}) :
  @join _ _ FreeModMonad X
    = fmap[RMod_Forget R]
        (@counit _ _ _ _ (free_module_adjunction_hom R) (FreeMod R X))
  := eq_refl.

(* μ flattens: ⟨t⟩ ↦ t, and in general the fold of the identity. / μ 扁平化：⟨t⟩ ↦ t，通常来说是单位函数的折叠。 *)
Example TR_join_gen@{+} (X : Sets@{c so}) (t : @FVTerm R X) :
  @join _ _ FreeModMonad X (@fv_gen R (RMod_Forget R (FreeModObject X)) t)
    = t := eq_refl.

Example TR_join_fun@{+} (X : Sets@{c so})
  (k : @FVTerm R (RMod_Forget R (FreeModObject X))) :
  @join _ _ FreeModMonad X k = fv_flatten k := eq_refl.

Example TR_join_zero@{+} (X : Sets@{c so}) :
  @join _ _ FreeModMonad X fv_zero = fv_zero := eq_refl.

(* μ scales and flattens: r·⟨t⟩ + s·⟨t'⟩ ↦ r·t + s·t'. / μ 进行缩放和平展：r·⟨t⟩ + s·⟨t'⟩ ↦ r·t + s·t'。 *)
Example TR_join_lc@{+} (X : Sets@{c so}) (r s : scalar)
  (t t' : @FVTerm R X) :
  @join _ _ FreeModMonad X
    (fv_plus (fv_smul r (@fv_gen R (RMod_Forget R (FreeModObject X)) t))
             (fv_smul s (@fv_gen R (RMod_Forget R (FreeModObject X)) t')))
    = fv_plus (fv_smul r t) (fv_smul s t') := eq_refl.

(*
 T_R u relabels, up to ≈: the free functor's action on arrows is read
 through the universal arrows. 

 --------
 T_R 的重新标记，最多 ≈：自由函子的箭头作用通过泛箭头来读取。
*)
Lemma TR_map_equiv@{+} {X Y : Sets@{c so}} (u : X ~{Sets@{c so}}~> Y)
  (t : @FVTerm R X) : fmap[FreeModF] u t ≈ fv_relabel u t.
Proof.
  apply (fv_extend_unique (FreeModObject Y) (fv_insert Y ∘ u)
           (fmap[FreeMod R] u)).
  intro x. exact (free_module_fmap_generators u x).
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** Part (a), first reading: formal linear combinations / * **（a部分），第一次阅读：正式线性组合 *)

(* Evaluating a relabelled combination (Leibniz, by induction). / 评估重新标记的组合（莱布尼茨，通过归纳法）。 *)
Lemma fv_eval_relabel@{+} {X Y : Sets@{c so}} {W : RMod R}
  (h : Y ~{Sets@{c so}}~> RMod_Forget R W) (u : X ~{Sets@{c so}}~> Y)
  (t : @FVTerm R X) : fv_eval h (fv_relabel u t) = fv_eval (h ∘ u) t.
Proof.
  induction t as [ x | | s IHs v IHv | s IHs | r s IHs ];
    (reflexivity || (simpl; f_equal; assumption)).
Qed.

(* Evaluating a flattened combination of combinations (Leibniz). / 评估组合的平展组合（莱布尼茨）。 *)
Lemma fv_eval_flatten@{+} {X : Sets@{c so}} {W : RMod R}
  (h : X ~{Sets@{c so}}~> RMod_Forget R W)
  (k : @FVTerm R (RMod_Forget R (FreeModObject X))) :
  fv_eval h (fv_flatten k) = fv_eval (fmap[RMod_Forget R] (fv_extend h)) k.
Proof.
  induction k as [ t | | s IHs v IHv | s IHs | r s IHs ];
    (reflexivity || (simpl; f_equal; assumption)).
Qed.

(* A list of coefficient/generator pairs, relabelled pairwise. / 系数/生成器对的列表，成对重新标记。 *)
Fixpoint fv_lc_map@{+} {X Y : Sets@{c so}} (u : X ~{Sets@{c so}}~> Y)
  (l : list (fv_pair R X)) : list (fv_pair R Y) :=
  match l with
  | nil => nil
  | cons q l' => cons (fst q, u (snd q)) (fv_lc_map u l')
  end.

(* A list of scaled lists, each inner list scaled and all concatenated. / 一个缩放列表的列表，每个内部列表被缩放后全部连接起来。 *)
Fixpoint fv_lc_flat@{+} {X : Sets@{c so}}
  (L : list (scalar * list (fv_pair R X))) : list (fv_pair R X) :=
  match L with
  | nil => nil
  | cons q L' => fv_app R X (fv_scale R X (fst q) (snd q)) (fv_lc_flat L')
  end.

(* The same list of scaled lists, read as a combination of combinations. / 相同的缩放列表列表，读作组合的组合。 *)
Fixpoint fv_lc_inner@{+} {X : Sets@{c so}}
  (L : list (scalar * list (fv_pair R X)))
  : list (fv_pair R (RMod_Forget R (FreeModObject X))) :=
  match L with
  | nil => nil
  | cons q L' => cons (fst q, fv_lc (snd q)) (fv_lc_inner L')
  end.

(* The relabelling of a combination relabels each pair (Leibniz). / 组合的重新标记会重新标记每一对（莱布尼茨）。 *)
Lemma fv_relabel_lc@{+} {X Y : Sets@{c so}} (u : X ~{Sets@{c so}}~> Y)
  (l : list (fv_pair R X)) :
  fv_relabel u (fv_lc l) = fv_lc (fv_lc_map u l).
Proof.
  induction l as [|q l IH]; [ reflexivity | ].
  simpl. f_equal. exact IH.
Qed.

(* T_R u relabels each pair. / T_R 重新标记每对。 *)
Lemma TR_map_lc@{+} {X Y : Sets@{c so}} (u : X ~{Sets@{c so}}~> Y)
  (l : list (fv_pair R X)) :
  fv_eq (fmap[FreeModF] u (fv_lc l)) (fv_lc (fv_lc_map u l)).
Proof.
  refine (fe_trans (TR_map_equiv u (fv_lc l)) _).
  rewrite fv_relabel_lc. apply fv_refl.
Qed.

(* η_X x is the one-pair combination 1·x. / η_X x 是一对组合 1·x。 *)
Lemma TR_ret_lc@{+} {X : Sets@{c so}} (x : carrier X) :
  fv_eq (@ret _ _ FreeModMonad X x)
        (fv_lc (cons (rig_one (ring_rig R), x) nil)).
Proof.
  simpl.
  refine (fe_trans (fe_sym (fe_zero_l _)) _).
  refine (fe_trans (fe_comm _ _) _).
  exact (fe_plus (fe_sym (fe_smul_one _)) (fv_refl _)).
Qed.

(*
 μ_X scales each inner combination by its coefficient and
 concatenates. 

 --------
 μ_X 将每个内部组合按其系数进行缩放并进行拼接。
*)
Lemma TR_join_lc_flat@{+} {X : Sets@{c so}}
  (L : list (scalar * list (fv_pair R X))) :
  fv_eq (@join _ _ FreeModMonad X (fv_lc (fv_lc_inner L)))
        (fv_lc (fv_lc_flat L)).
Proof.
  induction L as [|q L IH]; simpl.
  - apply fv_refl.
  - refine (fe_trans _ (fe_sym (fv_lc_app R X _ _))).
    refine (fe_plus _ IH).
    refine (fe_trans _ (fe_sym (fv_lc_scale R X _ _))).
    exact (fe_smul (reflexivity _) (fv_refl _)).
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** Part (b): the monad laws verified directly / * ** 部分(b)：直接验证的单子定律 *)

(* A Leibniz equality of combinations is an [fv_eq]. / 组合的莱布尼茨等式是 [fv_eq]。 *)
Lemma fv_eq_of_eq@{+} {X : Sets@{c so}} (s t : @FVTerm R X) :
  s = t → fv_eq s t.
Proof. intros ->. apply fv_refl. Qed.

Lemma fv_relabel_id@{+} {X : Sets@{c so}} (t : @FVTerm R X) :
  fv_relabel (@id Sets@{c so} X) t = t.
Proof.
  induction t as [ x | | s IHs v IHv | s IHs | r s IHs ];
    (reflexivity || (simpl; f_equal; assumption)).
Qed.

Lemma fv_relabel_comp@{+} {X Y Z : Sets@{c so}} (g : Y ~{Sets@{c so}}~> Z)
  (f : X ~{Sets@{c so}}~> Y) (t : @FVTerm R X) :
  fv_relabel (g ∘ f) t = fv_relabel g (fv_relabel f t).
Proof.
  induction t as [ x | | s IHs v IHv | s IHs | r s IHs ];
    (reflexivity || (simpl; f_equal; assumption)).
Qed.

Lemma fv_relabel_respects@{+} {X Y : Sets@{c so}}
  (u u' : X ~{Sets@{c so}}~> Y) (H : u ≈ u') (t : @FVTerm R X) :
  fv_eq (fv_relabel u t) (fv_relabel u' t).
Proof.
  induction t as [ x | | s IHs v IHv | s IHs | r s IHs ]; simpl.
  - exact (fe_gen (H x)).
  - apply fv_refl.
  - exact (fe_plus IHs IHv).
  - exact (fe_neg IHs).
  - exact (fe_smul (reflexivity r) IHs).
Qed.

(* μ ∘ T μ = μ ∘ μ T, on a combination of combinations of combinations. / μ ∘ T μ = μ ∘ μ T，在组合的组合的组合上。 *)
Lemma fv_flatten_assoc@{+} {X : Sets@{c so}}
  (K3 : @FVTerm R (RMod_Forget R (FreeModObject
                     (RMod_Forget R (FreeModObject X))))) :
  fv_flatten (fv_relabel (fmap[RMod_Forget R]
                (fv_extend (@id Sets@{c so}
                              (RMod_Forget R (FreeModObject X))))) K3)
  = fv_flatten (fv_flatten K3).
Proof.
  induction K3 as [ k | | s IHs v IHv | s IHs | r s IHs ];
    (reflexivity || (simpl; f_equal; assumption)).
Qed.

(* μ ∘ T η = 1. *)
Lemma fv_flatten_relabel_insert@{+} {X : Sets@{c so}} (t : @FVTerm R X) :
  fv_flatten (fv_relabel (fv_insert X) t) = t.
Proof.
  induction t as [ x | | s IHs v IHv | s IHs | r s IHs ];
    (reflexivity || (simpl; f_equal; assumption)).
Qed.

(* μ is natural. / μ是自然的。 *)
Lemma fv_flatten_natural@{+} {X Y : Sets@{c so}} (u : X ~{Sets@{c so}}~> Y)
  (K : @FVTerm R (RMod_Forget R (FreeModObject X))) :
  fv_flatten (fv_relabel (fmap[RMod_Forget R]
                            (fv_extend (fv_insert Y ∘ u))) K)
  = fv_relabel u (fv_flatten K).
Proof.
  induction K as [ k | | s IHs v IHv | s IHs | r s IHs ];
    (reflexivity || (simpl; f_equal; assumption)).
Qed.

(*
 The endofunctor of Mac Lane's description: T_R t relabels each
 generator. 

 --------
 Mac Lane 描述的函子端：T_R t 重新标记每个生成元。
*)
Definition FreeModF_direct@{+} : Sets@{c so} ⟶ Sets@{c so}.
Proof using R.
  unshelve refine
    (@Build_Functor Sets@{c so} Sets@{c so}
       (fun X => RMod_Forget R (FreeModObject X))
       (fun X Y u => fmap[RMod_Forget R] (fv_extend (fv_insert Y ∘ u)))
       _ _ _).
  - intros X Y u u' H t. exact (fv_relabel_respects u u' H t).
  - intros X t. exact (fv_eq_of_eq _ _ (fv_relabel_id t)).
  - intros X Y Z g f t. exact (fv_eq_of_eq _ _ (fv_relabel_comp g f t)).
Defined.

(*
 The monad laws, each by the Leibniz lemmas above; no adjunction is
 cited. 

 --------
 单子律，每一个都依据上述莱布尼茨引理；没有引用任何伴随关系。
*)
Definition FreeModMonad_direct@{+} : @Monad Sets@{c so} FreeModF_direct.
Proof.
  unshelve refine
    (@Build_Monad Sets@{c so} FreeModF_direct
       (fun X => fv_insert X)
       (fun X => fmap[RMod_Forget R]
                   (fv_extend (@id Sets@{c so}
                                 (RMod_Forget R (FreeModObject X)))))
       _ _ _ _ _).
  - (* η natural *) intros X Y u x. reflexivity.
  - (* μ ∘ T μ ≈ μ ∘ μ T *)
    intros X K3. exact (fv_eq_of_eq _ _ (fv_flatten_assoc K3)).
  - (* μ ∘ T η ≈ 1 *)
    intros X t. exact (fv_eq_of_eq _ _ (fv_flatten_relabel_insert t)).
  - (* μ ∘ η T ≈ 1 *) intros X t. apply fv_refl.
  - (* μ natural *)
    intros X Y u K. exact (fv_eq_of_eq _ _ (fv_flatten_natural u K)).
Defined.

(* Its unit and multiplication ARE T_R's, and its action on arrows is the relabelling. / 它的单位和乘法是 T_R 的，它对箭头的作用是重新标记。 *)
Example TR_direct_ret@{+} (X : Sets@{c so}) :
  @ret _ _ FreeModMonad_direct X = @ret _ _ FreeModMonad X := eq_refl.

Example TR_direct_join@{+} (X : Sets@{c so}) :
  @join _ _ FreeModMonad_direct X = @join _ _ FreeModMonad X := eq_refl.

Example TR_direct_obj@{+} (X : Sets@{c so}) :
  fobj[FreeModF_direct] X = fobj[FreeModF] X := eq_refl.

Example TR_direct_map@{+} {X Y : Sets@{c so}} (u : X ~{Sets@{c so}}~> Y)
  (t : @FVTerm R X) : fmap[FreeModF_direct] u t = fv_relabel u t
  := eq_refl.

Example TR_direct_map_gen@{+} {X Y : Sets@{c so}}
  (u : X ~{Sets@{c so}}~> Y) (x : carrier X) :
  fmap[FreeModF_direct] u (fv_gen x) = fv_gen (u x) := eq_refl.

(* The two endofunctors agree, with identity components. / 这两个端函子一致，并且具有相同的恒等分量。 *)
Definition FreeModF_direct_iso@{+} : FreeModF_direct ≈ FreeModF.
Proof.
  exists (fun X => @iso_id Sets@{c so} (fobj[FreeModF] X)).
  intros X Y u t.
  exact (fe_sym (TR_map_equiv u t)).
Defined.

Example TR_direct_iso_component@{+} (X : Sets@{c so}) :
  (to (projT1 FreeModF_direct_iso X), from (projT1 FreeModF_direct_iso X))
    = (@id Sets@{c so} (fobj[FreeModF] X), @id Sets@{c so} (fobj[FreeModF] X))
  := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** Part (c): the algebras of T_R are the R-modules / * ** 第(c)部分：T_R 的代数是 R-模 *)

Definition TRAlg@{+} : Category@{so c c} :=
  @EilenbergMoore@{so so so c} Sets@{c so} FreeModF FreeModMonad.

(* The comparison functor K : R-Mod → Set^{T_R}. / 比较函子 K : R-Mod → Set^{T_R}。 *)
Definition RMod_K@{+} : RMod R ⟶ TRAlg :=
  EM_Comparison (free_module_adjunction_hom R).

(*
 K commutes with the right adjoints and with the left ones: Monad/
 Comparison.v's two triangles, at this adjunction. 

 --------
 K 与右伴随子以及左伴随子交换：在此伴随下，Monad/Comparison.v 的两个三角形。
*)
Theorem RMod_K_Forget@{+} :
  @EM_Forget Sets@{c so} FreeModF FreeModMonad ◯ RMod_K ≈ RMod_Forget R.
Proof. exact (EM_Comparison_Forget (free_module_adjunction_hom R)). Qed.

Theorem RMod_K_Free@{+} :
  RMod_K ◯ FreeMod R ≈ @EM_Free Sets@{c so} FreeModF FreeModMonad.
Proof. exact (EM_Comparison_Free (free_module_adjunction_hom R)). Qed.

Section Algebra.

Context {A : Sets@{c so}}.
Context (α : @TAlgebra Sets@{c so} FreeModF FreeModMonad A).

(* The module operations of an algebra (A, h): 0 = h⟨⟩, a + b = h(⟨a⟩ + ⟨b⟩), −a = h(−⟨a⟩) and r·a = h(r·⟨a⟩). / 代数 (A, h) 的模运算：0 = h⟨⟩, a + b = h(⟨a⟩ + ⟨b⟩), −a = h(−⟨a⟩) 和 r·a = h(r·⟨a⟩)。 *)
Definition tr_alg_zero@{+} : carrier A := t_alg[α] (@fv_zero R A).

Definition tr_alg_plus@{+} (x y : carrier A) : carrier A :=
  t_alg[α] (@fv_plus R A (fv_gen x) (fv_gen y)).

Definition tr_alg_neg@{+} (x : carrier A) : carrier A :=
  t_alg[α] (@fv_neg R A (fv_gen x)).

Definition tr_alg_smul@{+} (r : scalar) (x : carrier A) : carrier A :=
  t_alg[α] (@fv_smul R A r (fv_gen x)).

(* The linear combination with the coefficients of the term, through the operations just defined. / 通过刚定义的运算，使用该项的系数进行线性组合。 *)
Fixpoint tr_alg_eval@{+} (t : @FVTerm R A) : carrier A :=
  match t with
  | fv_gen x    => x
  | fv_zero     => tr_alg_zero
  | fv_plus s u => tr_alg_plus (tr_alg_eval s) (tr_alg_eval u)
  | fv_neg s    => tr_alg_neg (tr_alg_eval s)
  | fv_smul r s => tr_alg_smul r (tr_alg_eval s)
  end.

Lemma tr_alg_unit@{+} (x : carrier A) : t_alg[α] (@fv_gen R A x) ≈ x.
Proof. exact (@t_id _ _ _ _ α x). Qed.

(* h ∘ μ ≈ h ∘ T h, read through the relabelling. / h ∘ μ ≈ h ∘ T h，通过重新标记来阅读。 *)
Lemma tr_alg_step@{+} (K : @FVTerm R (fobj[FreeModF] A)) :
  t_alg[α] (@join _ _ FreeModMonad A K) ≈ t_alg[α] (fv_relabel t_alg[α] K).
Proof.
  symmetry.
  refine (transitivity _ (@t_action _ _ _ _ α K)).
  apply (proper_morphism t_alg[α]).
  symmetry. exact (TR_map_equiv t_alg[α] K).
Qed.

Lemma tr_alg_plus_respects@{+} :
  Proper (equiv ==> equiv ==> equiv) tr_alg_plus.
Proof.
  intros x x' Hx y y' Hy.
  exact (proper_morphism t_alg[α] _ _ (fe_plus (fe_gen Hx) (fe_gen Hy))).
Qed.

Lemma tr_alg_neg_respects@{+} : Proper (equiv ==> equiv) tr_alg_neg.
Proof.
  intros x x' Hx. exact (proper_morphism t_alg[α] _ _ (fe_neg (fe_gen Hx))).
Qed.

Lemma tr_alg_smul_respects@{+} :
  Proper (equiv ==> equiv ==> equiv) tr_alg_smul.
Proof.
  intros r r' Hr x x' Hx.
  exact (proper_morphism t_alg[α] _ _ (fe_smul Hr (fe_gen Hx))).
Qed.

(* The structure map IS linear combination in the derived module. / 结构映射是在导出模中的线性组合。 *)
Lemma tr_alg_fold@{+} (t : @FVTerm R A) : t_alg[α] t ≈ tr_alg_eval t.
Proof.
  induction t as [ x | | s IHs u IHu | s IHs | r s IHs ]; simpl.
  - exact (tr_alg_unit x).
  - reflexivity.
  - refine (transitivity
              (tr_alg_step
                 (@fv_plus R (fobj[FreeModF] A)
                    (@fv_gen R (fobj[FreeModF] A) s)
                    (@fv_gen R (fobj[FreeModF] A) u))) _).
    exact (tr_alg_plus_respects _ _ IHs _ _ IHu).
  - refine (transitivity
              (tr_alg_step
                 (@fv_neg R (fobj[FreeModF] A)
                    (@fv_gen R (fobj[FreeModF] A) s))) _).
    exact (tr_alg_neg_respects _ _ IHs).
  - refine (transitivity
              (tr_alg_step
                 (@fv_smul R (fobj[FreeModF] A) r
                    (@fv_gen R (fobj[FreeModF] A) s))) _).
    exact (tr_alg_smul_respects _ _ (reflexivity r) _ _ IHs).
Qed.

Lemma tr_alg_eval_respects@{+} (s t : @FVTerm R A) :
  fv_eq s t → tr_alg_eval s ≈ tr_alg_eval t.
Proof.
  intro H.
  refine (transitivity (symmetry (tr_alg_fold s)) _).
  refine (transitivity (proper_morphism t_alg[α] _ _ H) _).
  exact (tr_alg_fold t).
Qed.

(*
 Every algebra's carrier is propositional, with no hypothesis: x ≈ y
 iff ⟨x⟩ ≈ ⟨y⟩ in T_R A, a [Prop]. 

 --------
 每个代数的载体是命题的，没有假设：x ≈ y 当且仅当 ⟨x⟩ ≈ ⟨y⟩ 在 T_R A，a [Prop]。
*)
Definition tr_alg_prop@{+} : PropEquiv (is_setoid A).
Proof using R A α.
  unshelve refine
    (@Build_PropEquiv _ (is_setoid A)
       (fun x y => @fv_eq R A (fv_gen x) (fv_gen y)) _ _).
  - intros x y H.
    refine (transitivity (symmetry (tr_alg_unit x)) _).
    refine (transitivity (proper_morphism t_alg[α] _ _ H) _).
    exact (tr_alg_unit y).
  - intros x y H. exact (fe_gen H).
Defined.

(* The R-module of the algebra: each law is one instance of [tr_alg_eval_respects] at a constructor of [fv_eq]. / 代数的 R-模：每条定律都是 [fv_eq] 构造函数上 [tr_alg_eval_respects] 的一个实例。 *)
Definition tr_alg_rmod@{+} : RModObject R := {|
  rm_ab := {|
    ab_cmon := {|
      cmon_setoid := A;
      cmon_zero := tr_alg_zero;
      cmon_plus := tr_alg_plus;
      cmon_plus_respects := tr_alg_plus_respects;
      cmon_plus_assoc := fun x y z =>
        tr_alg_eval_respects _ _ (fe_assoc (fv_gen x) (fv_gen y) (fv_gen z));
      cmon_plus_comm := fun x y =>
        tr_alg_eval_respects _ _ (fe_comm (fv_gen x) (fv_gen y));
      cmon_plus_zero_l := fun x =>
        tr_alg_eval_respects _ _ (fe_zero_l (fv_gen x));
      cmon_prop := tr_alg_prop
    |};
    ab_neg := tr_alg_neg;
    ab_neg_respects := tr_alg_neg_respects;
    ab_neg_left := fun x => tr_alg_eval_respects _ _ (fe_neg_l (fv_gen x))
  |};
  rm_smul := tr_alg_smul;
  rm_smul_respects := tr_alg_smul_respects;
  rm_smul_distr_l := fun r x y =>
    tr_alg_eval_respects _ _ (fe_smul_distr_l r (fv_gen x) (fv_gen y));
  rm_smul_distr_r := fun r s x =>
    tr_alg_eval_respects _ _ (fe_smul_distr_r r s (fv_gen x));
  rm_smul_assoc := fun r s x =>
    tr_alg_eval_respects _ _ (fe_smul_assoc r s (fv_gen x));
  rm_smul_one := fun x => tr_alg_eval_respects _ _ (fe_smul_one (fv_gen x))
|}.

End Algebra.

(* An algebra map is linear. / 代数映射是线性的。 *)
Lemma tr_alg_hom_step@{+} {x y : TRAlg} (f : x ~{TRAlg}~> y)
  (t : @FVTerm R (projT1 x)) :
  t_alg_hom[f] (t_alg[projT2 x] t)
    ≈ t_alg[projT2 y] (fv_relabel t_alg_hom[f] t).
Proof.
  refine (transitivity (@t_alg_hom_commutes _ _ _ _ _ _ _ f t) _).
  apply (proper_morphism t_alg[projT2 y]).
  exact (TR_map_equiv t_alg_hom[f] t).
Qed.

Definition tr_alg_hom_rmod@{+} {x y : TRAlg} (f : x ~{TRAlg}~> y) :
  tr_alg_rmod (projT2 x) ~{RMod R}~> tr_alg_rmod (projT2 y).
Proof.
  unshelve refine
    (@Build_RModHom R (tr_alg_rmod (projT2 x)) (tr_alg_rmod (projT2 y))
       (@Build_CMonHom (tr_alg_rmod (projT2 x)) (tr_alg_rmod (projT2 y))
          t_alg_hom[f] _ _) _).
  - exact (tr_alg_hom_step f fv_zero).
  - intros a b. exact (tr_alg_hom_step f (fv_plus (fv_gen a) (fv_gen b))).
  - intros r a. exact (tr_alg_hom_step f (fv_smul r (fv_gen a))).
Defined.

(* The functor Set^{T_R} → R-Mod. / 函子 Set^{T_R} → R-模。 *)
Definition EM_to_RModS@{+} : TRAlg ⟶ RMod R.
Proof.
  unshelve refine
    (@Build_Functor TRAlg (RMod R) (fun x => tr_alg_rmod (projT2 x))
       (fun x y f => tr_alg_hom_rmod f) _ _ _).
  - intros x y f g H. exact H.
  - intros x a. reflexivity.
  - intros x y z f g a. reflexivity.
Defined.

(*
 The fold of the identity in the derived module IS [tr_alg_eval]
 (Leibniz, by induction). 

 --------
 在导出模中的恒等式的折叠是 [tr_alg_eval] （Leibniz，通过归纳法）。
*)
Lemma tr_fold_is_alg_eval@{+} {A : Sets@{c so}}
  (α : @TAlgebra Sets@{c so} FreeModF FreeModMonad A) (t : @FVTerm R A) :
  fv_eval (W := tr_alg_rmod α)
    (@id Sets@{c so} (RMod_Forget R (tr_alg_rmod α))) t
  = tr_alg_eval α t.
Proof.
  induction t as [ x | | s IHs u IHu | s IHs | r s IHs ]; simpl;
    try rewrite IHs; try rewrite IHu; reflexivity.
Qed.

(* The algebra round trip, with the identity as its component. / 代数往返，以恒等式作为其组成部分。 *)
Definition RMod_EM_counit_iso@{+} (x : TRAlg) :
  @Isomorphism TRAlg (fobj[RMod_K ◯ EM_to_RModS] x) x.
Proof.
  unshelve refine
    (@Build_Isomorphism TRAlg (fobj[RMod_K ◯ EM_to_RModS] x) x
       (@Build_TAlgebraHom Sets@{c so} FreeModF FreeModMonad
          (projT1 x) (projT1 x)
          (projT2 (fobj[RMod_K ◯ EM_to_RModS] x)) (projT2 x)
          (@id Sets@{c so} (projT1 x)) _)
       (@Build_TAlgebraHom Sets@{c so} FreeModF FreeModMonad
          (projT1 x) (projT1 x)
          (projT2 x) (projT2 (fobj[RMod_K ◯ EM_to_RModS] x))
          (@id Sets@{c so} (projT1 x)) _) _ _).
  - intro t.
    change (fv_eval (W := tr_alg_rmod (projT2 x))
              (@id Sets@{c so} (RMod_Forget R (tr_alg_rmod (projT2 x)))) t
            ≈ t_alg[projT2 x] (fmap[FreeModF] (@id Sets@{c so} (projT1 x)) t)).
    rewrite (tr_fold_is_alg_eval (projT2 x) t).
    refine (transitivity (symmetry (tr_alg_fold (projT2 x) t)) _).
    apply (proper_morphism t_alg[projT2 x]).
    symmetry. exact (@fmap_id _ _ FreeModF (projT1 x) t).
  - intro t.
    change (t_alg[projT2 x] t
            ≈ fv_eval (W := tr_alg_rmod (projT2 x))
                (@id Sets@{c so} (RMod_Forget R (tr_alg_rmod (projT2 x))))
                (fmap[FreeModF] (@id Sets@{c so} (projT1 x)) t)).
    rewrite (tr_fold_is_alg_eval (projT2 x)).
    refine (transitivity (tr_alg_fold (projT2 x) t) _).
    apply tr_alg_eval_respects.
    exact (fe_sym (@fmap_id _ _ FreeModF (projT1 x) t)).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(*
 The module round trip, with the identity as its component: on a module
 M the derived operations ARE M's. 

 --------
 模块往返，其组件为同一性：在一个模块 M 上，派生操作是 M 的。
*)
Definition RMod_EM_unit_iso@{+} (M : RMod R) :
  @Isomorphism (RMod R) (fobj[EM_to_RModS ◯ RMod_K] M) M.
Proof.
  unshelve refine
    (@Build_Isomorphism (RMod R) (fobj[EM_to_RModS ◯ RMod_K] M) M
       (@Build_RModHom R (fobj[EM_to_RModS ◯ RMod_K] M) M
          (@Build_CMonHom (fobj[EM_to_RModS ◯ RMod_K] M) M
             (@id Sets@{c so} (RMod_Forget R M)) _ _) _)
       (@Build_RModHom R M (fobj[EM_to_RModS ◯ RMod_K] M)
          (@Build_CMonHom M (fobj[EM_to_RModS ◯ RMod_K] M)
             (@id Sets@{c so} (RMod_Forget R M)) _ _) _) _ _).
  all: simpl; intros; reflexivity.
Defined.

(* K is an equivalence, with identity components both ways. / K 是一个等价关系，两边都有恒等分量。 *)
Definition RMod_EM_equivalence@{+} :
  @EquivalenceOfCategories (RMod R) TRAlg RMod_K.
Proof.
  unshelve refine
    (@Build_EquivalenceOfCategories _ _ RMod_K EM_to_RModS _ _).
  - exists (fun x => RMod_EM_counit_iso x). intros x y f a. reflexivity.
  - exists (fun M => iso_sym (RMod_EM_unit_iso M)).
    intros M N f a. reflexivity.
Defined.

(* R-modules are monadic over Set. / R-模在集合上是单子性的。 *)
Definition RMod_Forget_Monadic@{+} : Monadic (RMod_Forget R).
Proof.
  exists (FreeMod R). exists (free_module_adjunction_hom R).
  exact RMod_EM_equivalence.
Defined.

(* R-Mod ≅ Set^{T_R} in Cat, from the two component isomorphisms. / R-Mod ≅ Set^{T_R} 在 Cat 中，由两个分量同构得到。 *)
Definition RMod_EM_iso@{k +} :
  @Isomorphism Cat@{k so so so c} (RMod R) TRAlg.
Proof.
  unshelve refine
    (@Build_Isomorphism Cat@{k so so so c} (RMod R) TRAlg
       RMod_K EM_to_RModS _ _).
  - exists (fun x => RMod_EM_counit_iso x). intros x y f a. reflexivity.
  - exists (fun M => RMod_EM_unit_iso M). intros M N f a. reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** Readbacks / ** 回读 *)

(*
 K M is ⟨M, U ε_M⟩: the structure map is the fold of the identity,
 the linear combination in M. 

 --------
 K M 是 ⟨M, U ε_M⟩：结构映射是同一映射的折叠，M 中的线性组合。
*)
Example RMod_K_carrier@{+} (M : RMod R) :
  projT1 (fobj[RMod_K] M) = RMod_Forget R M := eq_refl.

Example RMod_K_map@{+} {M N : RMod R} (f : M ~{RMod R}~> N) :
  t_alg_hom[fmap[RMod_K] f] = fmap[RMod_Forget R] f := eq_refl.

Example RMod_K_alg@{+} (M : RMod R) :
  t_alg[projT2 (fobj[RMod_K] M)]
    = fmap[RMod_Forget R] (@counit _ _ _ _ (free_module_adjunction_hom R) M)
  := eq_refl.

Example RMod_K_alg_fun@{+} (M : RMod R)
  (t : @FVTerm R (RMod_Forget R M)) :
  t_alg[projT2 (fobj[RMod_K] M)] t
    = fv_eval (@id Sets@{c so} (RMod_Forget R M)) t := eq_refl.

Example RMod_K_alg_gen@{+} (M : RMod R) (x : carrier (RMod_Forget R M)) :
  t_alg[projT2 (fobj[RMod_K] M)] (fv_gen x) = x := eq_refl.

Example RMod_K_alg_zero@{+} (M : RMod R) :
  t_alg[projT2 (fobj[RMod_K] M)] fv_zero = cmon_zero M := eq_refl.

Example RMod_K_alg_plus@{+} (M : RMod R) (x y : carrier (RMod_Forget R M)) :
  t_alg[projT2 (fobj[RMod_K] M)] (fv_plus (fv_gen x) (fv_gen y))
    = cmon_plus M x y := eq_refl.

Example RMod_K_alg_neg@{+} (M : RMod R) (x : carrier (RMod_Forget R M)) :
  t_alg[projT2 (fobj[RMod_K] M)] (fv_neg (fv_gen x)) = ab_neg M x
  := eq_refl.

Example RMod_K_alg_smul@{+} (M : RMod R) (r : scalar)
  (x : carrier (RMod_Forget R M)) :
  t_alg[projT2 (fobj[RMod_K] M)] (fv_smul r (fv_gen x)) = rm_smul M r x
  := eq_refl.

(*
 h at Σ rᵢ·⟨xᵢ⟩ is the fold of the identity there, [RMod_K_alg_fun] at
 a combination; for a given list it unfolds to the linear combination
 r₁·x₁ + (r₂·x₂ + (… + 0)) in M. 

 --------
 在 Σ rᵢ·⟨xᵢ⟩ 处的 h 是那里的恒等映射的折叠，[RMod_K_alg_fun] 在一个组合处；对于给定的列表，它展开为在 M 中的线性组合 r₁·x₁ + (r₂·x₂ + (… + 0))。
*)
Example RMod_K_alg_lc@{+} (M : RMod R)
  (l : list (fv_pair R (RMod_Forget R M))) :
  t_alg[projT2 (fobj[RMod_K] M)] (fv_lc l)
    = fv_eval (@id Sets@{c so} (RMod_Forget R M)) (fv_lc l) := eq_refl.

(* The legs of the isomorphism in Cat. / Cat 中同构的腿。 *)
Example RMod_EM_iso_to@{+} : to RMod_EM_iso = RMod_K := eq_refl.

Example RMod_EM_iso_from@{+} : from RMod_EM_iso = EM_to_RModS
  := eq_refl.

(* The module of an algebra: its carrier, its [Prop] equality and its operations. / 代数的模：它的载体、它的 [Prop] 等式及其运算。 *)
Example EM_to_RModS_prop@{+} (x : TRAlg) (a b : carrier (projT1 x)) :
  @pequiv _ _ (cmon_prop (fobj[EM_to_RModS] x)) a b
    = @fv_eq R (projT1 x) (fv_gen a) (fv_gen b) := eq_refl.

Example EM_to_RModS_carrier@{+} (x : TRAlg) :
  cmon_setoid (fobj[EM_to_RModS] x) = projT1 x := eq_refl.

Example EM_to_RModS_zero@{+} (x : TRAlg) :
  cmon_zero (fobj[EM_to_RModS] x) = t_alg[projT2 x] fv_zero := eq_refl.

Example EM_to_RModS_plus@{+} (x : TRAlg) (a b : carrier (projT1 x)) :
  cmon_plus (fobj[EM_to_RModS] x) a b
    = t_alg[projT2 x] (fv_plus (fv_gen a) (fv_gen b)) := eq_refl.

Example EM_to_RModS_neg@{+} (x : TRAlg) (a : carrier (projT1 x)) :
  ab_neg (fobj[EM_to_RModS] x) a = t_alg[projT2 x] (fv_neg (fv_gen a))
  := eq_refl.

Example EM_to_RModS_smul@{+} (x : TRAlg) (r : scalar)
  (a : carrier (projT1 x)) :
  rm_smul (fobj[EM_to_RModS] x) r a
    = t_alg[projT2 x] (fv_smul r (fv_gen a)) := eq_refl.

Example EM_to_RModS_map@{+} {x y : TRAlg} (f : x ~{TRAlg}~> y) :
  cmon_map (rm_hom (fmap[EM_to_RModS] f)) = t_alg_hom[f] := eq_refl.

(* The round trips keep every operation on the nose... / 往返保持每个操作都精准无误... *)
Example RMod_rt_carrier@{+} (M : RMod R) :
  cmon_setoid (fobj[EM_to_RModS ◯ RMod_K] M) = cmon_setoid M := eq_refl.

Example RMod_rt_zero@{+} (M : RMod R) :
  cmon_zero (fobj[EM_to_RModS ◯ RMod_K] M) = cmon_zero M := eq_refl.

Example RMod_rt_plus@{+} (M : RMod R) :
  cmon_plus (fobj[EM_to_RModS ◯ RMod_K] M) = cmon_plus M := eq_refl.

Example RMod_rt_neg@{+} (M : RMod R) :
  ab_neg (fobj[EM_to_RModS ◯ RMod_K] M) = ab_neg M := eq_refl.

Example RMod_rt_smul@{+} (M : RMod R) :
  rm_smul (fobj[EM_to_RModS ◯ RMod_K] M) = rm_smul M := eq_refl.

Example RMod_rt_hom@{+} {M N : RMod R} (f : M ~{RMod R}~> N) :
  cmon_map (rm_hom (fmap[EM_to_RModS ◯ RMod_K] f)) = cmon_map (rm_hom f)
  := eq_refl.

(* ...and so do the carrier and the maps of the algebra round trip. / ...载体和代数往返的地图也是如此。 *)
Example TRAlg_rt_carrier@{+} (x : TRAlg) :
  projT1 (fobj[RMod_K ◯ EM_to_RModS] x) = projT1 x := eq_refl.

Example TRAlg_rt_alg_fun@{+} (x : TRAlg) (t : @FVTerm R (projT1 x)) :
  t_alg[projT2 (fobj[RMod_K ◯ EM_to_RModS] x)] t
    = fv_eval (W := tr_alg_rmod (projT2 x))
        (@id Sets@{c so} (RMod_Forget R (tr_alg_rmod (projT2 x)))) t
  := eq_refl.

Example TRAlg_rt_alg_hom@{+} {x y : TRAlg} (f : x ~{TRAlg}~> y) :
  t_alg_hom[fmap[RMod_K ◯ EM_to_RModS] f] = t_alg_hom[f] := eq_refl.

(*
 Every component of the two natural isomorphisms is the identity, at a
 variable object, to and from. 

 --------
 这两个自然同构的每个分量都是在一个变量对象上的恒等映射，来回都是如此。
*)
Example RMod_EM_iso_to_from_component@{+} (x : TRAlg) :
  (t_alg_hom[to (projT1 (iso_to_from RMod_EM_iso) x)],
   t_alg_hom[from (projT1 (iso_to_from RMod_EM_iso) x)])
    = (@id Sets@{c so} (projT1 x), @id Sets@{c so} (projT1 x)) := eq_refl.

Example RMod_EM_iso_from_to_component@{+} (M : RMod R) :
  (cmon_map (rm_hom (to (projT1 (iso_from_to RMod_EM_iso) M))),
   cmon_map (rm_hom (from (projT1 (iso_from_to RMod_EM_iso) M))))
    = (@id Sets@{c so} (RMod_Forget R M), @id Sets@{c so} (RMod_Forget R M))
  := eq_refl.

(* ...and so is every component of the equivalence's counit and unit. / ...并且等价的余单位和单位的每个组成部分也是如此。 *)
Example RMod_EM_counit_component@{+} (x : TRAlg) :
  (t_alg_hom[to (projT1 (@equivalence_counit _ _ _ RMod_EM_equivalence) x)],
   t_alg_hom[from (projT1 (@equivalence_counit _ _ _
                             RMod_EM_equivalence) x)])
    = (@id Sets@{c so} (projT1 x), @id Sets@{c so} (projT1 x)) := eq_refl.

Example RMod_EM_unit_component@{+} (M : RMod R) :
  (cmon_map (rm_hom (to (projT1 (@equivalence_unit _ _ _
                                   RMod_EM_equivalence) M))),
   cmon_map (rm_hom (from (projT1 (@equivalence_unit _ _ _
                                     RMod_EM_equivalence) M))))
    = (@id Sets@{c so} (RMod_Forget R M), @id Sets@{c so} (RMod_Forget R M))
  := eq_refl.

End FreeModMonad.

(* ------------------------------------------------------------------------ *)
(*
   * ** Part (a), second reading: coefficients, under a decider for ≈

   The coefficient of y is the linear extension, into R as a module over
   itself, of Instance/Mod/Free.v's indicator [fv_probe_at] of y; no new
   indicator is written.  [fv_probe_at] puts [Ring_RMod R] in [RMod R],
   which identifies the ring's three levels with the generating setoid's
   carrier level: the section binds R at RingObject@{c c c}. 

   --------
   * ** 第（a）部分，第二次阅读：系数，在≈判定器下

   y 的系数是对 y 的 Instance/Mod/Free.v 的指示器 [fv_probe_at] 在 R 上作为自身模的线性扩展；没有写入新的指示器。[fv_probe_at] 将 [Ring_RMod R] 放入 [RMod R] 中，这将环的三个层级与生成集合组织的承载层识别：该节将 R 绑定在 RingObject@{c c c}。
*)

Section Coefficients.

Universes c so.
Context (R : RingObject@{c c c}).

Local Notation scalar := (carrier (rig_setoid (ring_rig R))).
Local Notation rzero := (rig_zero (ring_rig R)).
Local Notation rone := (rig_one (ring_rig R)).
Local Notation radd := (rig_add (ring_rig R)).
Local Notation rmul := (rig_mul (ring_rig R)).
Local Notation decider_on X :=
  (∀ x y : carrier X, (x ≈ y) + ((x ≈ y) → False)).

(* f ↦ f_y, the coefficient of y, as a setoid map T_R X → R. / f ↦ f_y，将 y 的系数作为集合化映射 T_R X → R。 *)
Definition fv_coef@{+} {X : Sets@{c so}} (Xdec : decider_on X)
  (y : carrier X) :
  RMod_Forget R (FreeModObject X) ~{Sets@{c so}}~> RMod_Forget R (Ring_RMod R)
  := fmap[RMod_Forget R] (fv_extend (fv_probe_at R X Xdec y)).

(* (η_X x)_x = 1 ... (Leibniz, as Mac Lane writes it) / (η_X x)_x = 1 ...（莱布尼茨，如麦克莱恩所写） *)
Lemma fv_coef_ret_same@{+} {X : Sets@{c so}} (Xdec : decider_on X)
  (x : carrier X) : fv_coef Xdec x (@ret _ _ (FreeModMonad R) X x) = rone.
Proof.
  simpl. destruct (Xdec x x) as [_|n]; [ reflexivity | ].
  destruct (n (reflexivity x)).
Qed.

(* ... and (η_X x)_{x'} = 0 for x' ≉ x (Leibniz). / ... 并且 (η_X x)_{x'} = 0 对于 x' ≉ x （莱布尼茨）。 *)
Lemma fv_coef_ret_other@{+} {X : Sets@{c so}} (Xdec : decider_on X)
  (x x' : carrier X) :
  (x' ≈ x → False) → fv_coef Xdec x' (@ret _ _ (FreeModMonad R) X x) = rzero.
Proof.
  intro n. simpl. destruct (Xdec x' x) as [e|_]; [ destruct (n e) | ].
  reflexivity.
Qed.

(* [(T_R t) f]_y is the linear functional "f evaluated on the indicator of the fibre t⁻¹(y)" ... / [(T_R t) f] _y 是作用在纤维 t⁻¹(y) 的指示函数上的线性泛函 f *)
Lemma fv_coef_map@{+} {X Y : Sets@{c so}} (Ydec : decider_on Y)
  (t : X ~{Sets@{c so}}~> Y) (f : @FVTerm R X) (y : carrier Y) :
  fv_coef Ydec y (fmap[FreeModF R] t f)
    ≈ fv_eval (fv_probe_at R Y Ydec y ∘ t) f.
Proof.
  refine (transitivity
            (proper_morphism (fv_coef Ydec y) _ _ (TR_map_equiv R t f)) _).
  change (fv_eval (fv_probe_at R Y Ydec y) (fv_relabel R t f)
          ≈ fv_eval (fv_probe_at R Y Ydec y ∘ t) f).
  rewrite (fv_eval_relabel R (fv_probe_at R Y Ydec y) t f).
  reflexivity.
Qed.

(* ... which on a combination is the literal sum Σ' f_x over the pairs (f_x, x) of f with t x ≈ y. / ... 对于一个组合来说，这是在 f 的 (f_x, x) 对上 f_x 的字面求和 Σ'，其中 t x ≈ y。 *)
Fixpoint fv_fibre_sum@{+} {X Y : Sets@{c so}} (Ydec : decider_on Y)
  (t : X ~{Sets@{c so}}~> Y) (y : carrier Y) (l : list (fv_pair R X))
  : scalar :=
  match l with
  | nil => rzero
  | cons q l' =>
      match Ydec y (t (snd q)) with
      | inl _ => radd (fst q) (fv_fibre_sum Ydec t y l')
      | inr _ => fv_fibre_sum Ydec t y l'
      end
  end.

(* The indicator of the fibre over y, evaluated at Σ rᵢ·⟨xᵢ⟩: the one induction that [fv_coef_map_lc] and FinSupp.v's [fv_coef_lc] share. / 在 Σ rᵢ·⟨xᵢ⟩ 处对 y 上纤维的指标：[fv_coef_map_lc] 和 FinSupp.v 的 [fv_coef_lc] 共享的那个归纳。 *)
Lemma fv_eval_fibre_lc@{+} {X Y : Sets@{c so}} (Ydec : decider_on Y)
  (t : X ~{Sets@{c so}}~> Y) (l : list (fv_pair R X)) (y : carrier Y) :
  fv_eval (fv_probe_at R Y Ydec y ∘ t) (fv_lc l) ≈ fv_fibre_sum Ydec t y l.
Proof.
  induction l as [|[r x] l IH]; simpl; [ reflexivity | ].
  destruct (Ydec y (t x)) as [e|n].
  - rewrite (rig_mul_one_r (ring_rig R) r).
    apply (rig_add_respects (ring_rig R)); [ reflexivity | exact IH ].
  - rewrite (rig_mul_zero_r (ring_rig R) r).
    rewrite (rig_add_zero_l (ring_rig R)). exact IH.
Qed.

Lemma fv_coef_map_lc@{+} {X Y : Sets@{c so}} (Ydec : decider_on Y)
  (t : X ~{Sets@{c so}}~> Y) (l : list (fv_pair R X)) (y : carrier Y) :
  fv_coef Ydec y (fmap[FreeModF R] t (fv_lc l)) ≈ fv_fibre_sum Ydec t y l.
Proof.
  exact (transitivity (fv_coef_map Ydec t (fv_lc l) y)
           (fv_eval_fibre_lc Ydec t l y)).
Qed.

(* (μ_X k)_x = Σ_f k_f f_x: the coefficient of x in μ k is the linear extension of f ↦ f_x, evaluated at k, on the nose ... / (μ_X k)_x = Σ_f k_f f_x：μ k 中 x 的系数是 f ↦ f_x 的线性扩展，在 k 上的精确求值... *)
Lemma fv_coef_join@{+} {X : Sets@{c so}} (Xdec : decider_on X)
  (x : carrier X) (k : @FVTerm R (RMod_Forget R (FreeModObject X))) :
  fv_coef Xdec x (@join _ _ (FreeModMonad R) X k)
    = fv_eval (W := Ring_RMod R) (fv_coef Xdec x) k.
Proof. exact (fv_eval_flatten R (fv_probe_at R X Xdec x) k). Qed.

(* ... which at k = Σ rᵢ·⟨fᵢ⟩ is Σ rᵢ·(fᵢ)_x. / ... 当 k = Σ rᵢ·⟨fᵢ⟩ 时，是 Σ rᵢ·(fᵢ)_x。 *)
Fixpoint fv_lc_weighted@{+} {X : Sets@{c so}} (Xdec : decider_on X)
  (x : carrier X) (L : list (fv_pair R (RMod_Forget R (FreeModObject X))))
  : scalar :=
  match L with
  | nil => rzero
  | cons q L' =>
      radd (rmul (fst q) (fv_coef Xdec x (snd q))) (fv_lc_weighted Xdec x L')
  end.

Lemma fv_coef_join_lc@{+} {X : Sets@{c so}} (Xdec : decider_on X)
  (x : carrier X) (L : list (fv_pair R (RMod_Forget R (FreeModObject X)))) :
  fv_coef Xdec x (@join _ _ (FreeModMonad R) X (fv_lc L))
    = fv_lc_weighted Xdec x L.
Proof.
  rewrite fv_coef_join.
  induction L as [|q L IH]; [ reflexivity | ].
  simpl. f_equal. exact IH.
Qed.

(* The coefficient respects ≈ in its point, Leibniz, by induction ... / 该系数在其点上遵守≈，莱布尼茨，通过归纳…… *)
Lemma fv_coef_respects_point@{+} {X : Sets@{c so}} (Xdec : decider_on X)
  (y y' : carrier X) (H : y ≈ y') (t : @FVTerm R X) :
  fv_coef Xdec y t = fv_coef Xdec y' t.
Proof.
  induction t as [ z | | s IHs v IHv | s IHs | r s IHs ]; simpl in *.
  - destruct (Xdec y z) as [e|n], (Xdec y' z) as [e'|n'].
    + reflexivity.
    + destruct (n' (transitivity (symmetry H) e)).
    + destruct (n (transitivity H e')).
    + reflexivity.
  - reflexivity.
  - f_equal; assumption.
  - f_equal; assumption.
  - f_equal; assumption.
Qed.

(* ... and vanishes at every point that no pair of a combination names: T_R X's elements are finitely supported. / ... 并且在没有成对组合的每一点上消失：T_R X 的元素是有限支持的。 *)
Fixpoint fv_avoids@{+} {X : Sets@{c so}} (y : carrier X)
  (l : list (fv_pair R X)) : Type@{c} :=
  match l with
  | nil => poly_unit@{c}
  | cons q l' => ((y ≈ snd q → False) * fv_avoids y l')%type
  end.

Lemma fv_coef_support@{+} {X : Sets@{c so}} (Xdec : decider_on X)
  (y : carrier X) (l : list (fv_pair R X)) :
  fv_avoids y l → fv_coef Xdec y (fv_lc l) ≈ rzero.
Proof.
  induction l as [|[r x] l IH]; simpl; intro Ha; [ reflexivity | ].
  destruct Ha as [n Ha].
  destruct (Xdec y x) as [e|_]; [ destruct (n e) | ].
  rewrite (rig_mul_zero_r (ring_rig R) r), (rig_add_zero_l (ring_rig R)).
  exact (IH Ha).
Qed.

End Coefficients.
