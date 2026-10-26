Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(*
   * * The free abelian group on a setoid, and the free-forgetful
   adjunction

   nLab:      https://ncatlab.org/nlab/show/free+abelian+group
   nLab:      https://ncatlab.org/nlab/show/free+object
   nLab:      https://ncatlab.org/nlab/show/universal+morphism
   Wikipedia: https://en.wikipedia.org/wiki/Free_abelian_group
   Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
   GTM 5, §IV.8, Exercise 2 -- maclane:IV.8:ex2
   Book: Mac Lane, ibid., §IV.1, printed p. 79 (a free construction
   presented as a hom-set bijection natural in each variable) --
   maclane:IV.1:construction1

   WHAT THIS IS, AND WHAT IT IS NOT.  [FreeAbObject X] is the free
   abelian group on a setoid X: formal sums of generators modulo
   exactly the abelian-group laws, together with the insertion of
   generators [free_ab_insert], the additive extension
   [free_ab_extend], its uniqueness [free_ab_extend_unique], the
   packaged universal property [free_ab_universal], the functor
   [FreeAb : Sets ⟶ Ab] and the adjunction
   [free_ab_adjunction : FreeAb ⊣ Ab_Forget].  It is ONE INPUT to
   Mac Lane's §IV.8 Exercise 2 -- which asks for the free-ring
   adjunction exhibited as a composite in two ways -- and that exercise
   is NOT formalized here: no ring, no monoid ring and no composite
   adjunction appears below.

   A GAP THE TREE RECORDED AND THIS FILE CLOSES.
   Instance/Ab/Tensor.v states, of its own construction, that
   “the tree has no free abelian group to quotient (verified across
   Construction/ and Instance/)”.  That is why the tensor product there
   is built by generators and relations bespoke to the pair (G, H).
   This file supplies the missing object.  It does NOT refactor
   Instance/Ab/Tensor.v to ride on it: that file's carrier is a
   quotient of formal sums of PAIRS, so routing it through this one
   would be a different construction rather than a citation, and no
   claim is made here that such a routing would work.

   WHY GENERATORS AND RELATIONS, NOT FINITELY SUPPORTED FUNCTIONS.  The
   classical carrier -- finitely supported ℤ-valued functions on X --
   presupposes generators with decidable equality, and
   Instance/Mod/Free.v's header locates the obstruction exactly: the
   CARRIER is not the problem (a [≈]-respecting function paired with a
   list witnessing that it vanishes outside that list is writable over
   a bare setoid), the BASIS INSERTION is.  The basis element at x is
   the function taking 1 at x and 0 elsewhere, and that function cannot
   be WRITTEN without a decision procedure for x ≈ y.  What makes this
   fatal rather than merely restrictive is that [Ab_Forget] lands in
   [Sets], whose objects are setoids, so a left adjoint must exist for
   EVERY generating setoid, decidable or not; a construction available
   only at decidable setoids yields no adjunction at all.  The
   presentation used here is therefore an inductive of formal
   expressions [FATerm] with an inductive congruence [fa_eq] closing
   under exactly the four abelian-group laws, congruence for each
   former, saturation under X's own [≈], and symmetry/transitivity.
   Reflexivity is derived ([fa_refl]), keeping the relation's induction
   principle one case shorter everywhere it is consumed.  As in
   Instance/Ab/Tensor.v and Instance/Mod/Free.v, [fa_Setoid] is NOT
   registered as a typeclass instance and element-level statements are
   written with [fa_eq]; that this IS the [≈] of the free group as an
   object of [Ab] is machine-checked by [free_ab_equiv_is_fa_eq]
   ([eq_refl]) rather than asserted, so every group-level lemma of
   Instance/Ab.v applies to it unchanged.

   RELATION TO Instance/Mod/Free.v.  Structurally this file is that one
   with the scalar former [fv_smul] and the four module laws deleted:
   five constructors of the congruence go away, leaving nine.  The
   DESIGN is copied and the debt is acknowledged; no code is shared and
   Instance/Mod/Free.v is not Required.  Nor is the construction
   DERIVED from it at R := ℤ, and that is a measurement rather than a
   preference: the free abelian group on X is the free ℤ-module on X,
   but transporting the universal property across needs a passage
   Ab → RMod ℤ giving every abelian group its ℤ-action, together with
   the proof that it inverts the forgetful direction ([RMod_Forget_Ab],
   Instance/Mod.v).  An earlier revision named only the first half, the
   passage, and said “no such passage exists” (the second half was left
   implicit); since #454 the first half is false: Instance/Mod/Cogenerator.v's [Ab_to_ZMod]
   is the passage, each group carrying its own [zsmul] action
   ([Ab_to_ZMod_group] and [Ab_to_ZMod_smul] at [eq_refl]).  What is
   still absent is the second half: no proof that every ℤ-module's
   action agrees with [zsmul], hence no equivalence [Ab ≃ RMod Int_Ring].
   Instance/Mod/BaseChange.v's [ZExt Int_Ring] also runs Ab → RMod ℤ but
   sends A to ℤ ⊗ A, not to A carrying its own ℤ-action, so it is not
   the passage wanted here -- Instance/Mod/Tensor.v's header recorded
   the same absence and carries the same #454 correction.  The reduction
   is therefore unavailable in tree; it is NOT claimed to be unavailable
   in principle.

   STRENGTHS, MEASURED STRICT-FIRST.  The mediator is a [Fixpoint] on
   formal expressions, so a great deal is definitional:

   - [eq_refl]: the carrier of the free group IS [FATerm] and its [≈]
   IS [fa_eq] ([free_ab_carrier_is_FATerm], [free_ab_equiv_is_fa_eq]);
   the insertion IS the generator former ([free_ab_insert_is_gen]);
   the additive extension agrees with the given function on
   generators ([free_ab_extend_generators]) and preserves zero,
   addition AND negation definitionally ([free_ab_extend_zero],
   [free_ab_extend_plus], [free_ab_extend_neg] -- recorded at
   Leibniz [=] on the target's CARRIER, which is the convertibility
   exception the house style sanctions, so the header's claim is
   machine-checked rather than inferred from which branch of the
   obligation tactic fired); the free functor's object part is the
   formal-sum group ([FreeAb_obj]); the universal arrow IS the
   insertion ([free_ab_arrow_is_insert]); the UNIT is the insertion
   and hence the one-generator expression ([free_ab_unit_is_insert],
   [free_ab_unit_is_generator]); and the adjunction's forward
   transpose ⌊−⌋ IS [fa_transpose] ([free_ab_transpose_is_adj]).
   - [≈] only: the COUNIT.  It is the other transpose, i.e.
   [unique_obj (ump_universal_arrows …)], and [ump_universal_arrows]
   (Theory/Universal/Arrow.v) is [Qed]-opaque, so nothing reduces
   through it.  What is proved is that it evaluates a formal sum
   ([free_ab_counit_evaluates]).
   - [≈] only: the action of [FreeAb] on an arrow.
   [LeftAdjointFunctorFromUniversalArrows] defines [fmap] by
   universal factorization rather than by a formula, so that it
   relabels generators is a theorem ([free_ab_fmap_generators]).

   CORRECTION (#472): the counit's diagnosis names one opaque
   constant, and two block it: [ump_universal_arrows] and this file's
   own [free_ab_universal], the proof of the factorization that
   [free_ab_universal_arrow] hands to [universal_arrow_from_UMP] and
   from which both the counit and [FreeAb]'s [fmap] are read.
   Measured by #472 in a rebuilt copy of the seventy-four modules its
   probe loads: with [ump_universal_arrows] alone turned [Defined], or
   with [free_ab_universal] alone, this file still builds, both
   negatives below that cite the opacity ([counit_does_not_compute],
   [fmap_generator_does_not_compute]) still refused; with both turned
   [Defined], both negatives hold, as [Example]s at [eq_refl], and so
   do Test/ProbeFreeModule472.v's refutations of ℤ[−]'s μ and [fmap]
   read off this adjunction (that probe's header; #472's scout had
   measured the counit's half).  Neither constant is turned [Defined]
   here (issue #1353 tracks [ump_universal_arrows]); #472 adds instead
   the same adjunction in hom-set form, [free_ab_adjunction_hom] (THE
   HOM-SET FORM, below), whose counit IS the fold by conversion.

   Both [≈]-only readings are GUARDED, not merely measured: the
   “Measured negatives” section at the end of the file carries a [Fail]
   for each, plus a third recording that [FreeAbObject] applied to a
   group's own carrier is not CONVERTIBLE with that group (a statement
   about conversion only -- no non-isomorphism is claimed or proved).
   Each is paired with a positive control that must succeed, and each
   was confirmed (by stripping the [Fail] in a scratch file) to be a
   genuine CONVERSION failure -- “cannot unify” -- rather
   than a missing reference.  Every constant named in a negative is
   also named in a positive command elsewhere in the file, so a rename
   at a definition site breaks the build loudly instead of turning a
   [Fail] vacuously green.  The house convention puts such probes in a
   Test/Probe*.v file; they are in-file here because this commit adds
   exactly one file (other Instance/ files already do the same).

   NATURALITY.  §IV.1 presents a free construction as a bijection
   Ab(FreeAb X, A) ≅ Sets(X, U A) natural in X and in A, “each verified
   separately”.  Both clauses are proved in the free group's own
   vocabulary ([free_ab_naturality_in_set], by evaluating at a
   generator; [free_ab_naturality_in_group], pointwise by
   [reflexivity]), and that they ARE the adjunction class's own fields
   [to_adj_nat_l] and [to_adj_nat_r] is then recorded by [eq_refl] on
   the STATEMENTS -- a conversion check, not a second derivation.

   THE HOM-SET FORM (#472).  Two packagings of the one adjunction FreeAb ⊣
   Ab_Forget are kept.  [free_ab_adjunction], from the universal arrows, is the
   one Instance/Rng/Free.v and the rest of the tree consume, and it is
   unchanged.  [free_ab_adjunction_hom] is Theory/Adjunction.v's
   [Build_Adjunction'] applied to the natural bijection [free_ab_hom_iso], with
   the same left adjoint [FreeAb], the same right adjoint and the same
   insertion: its unit and its forward transpose ARE those of
   [free_ab_adjunction] at [eq_refl] ([free_ab_hom_unit], [free_ab_hom_to]),
   its two naturality fields are the two theorems above, cited, and its inverse
   transpose is the additive extension [free_ab_extend], so its counit is the
   fold of the identity at [eq_refl] ([free_ab_hom_counit]), where the other
   counit is that fold only at `≈` ([free_ab_counit_evaluates]).  It exists for
   Riehl's monad ℤ[−] of §5.3 (Instance/Ab/FreeMonad.v), whose multiplication
   and comparison functor then compute.  It is not a second free group and not
   a second free functor.  The two adjunctions are refused equal at [eq_refl],
   and so are their counits at a variable formal sum
   (Test/ProbeFreeModule472.v, R22 and R23).  Its universes: @{c so}
   (Sets@{c so}) and the five further levels of [FreeAb] (the group category's
   object level and four internal ones), extensibly; the adjunction's own last
   level, which no constraint mentions when it is left free, is pinned to so as
   Instance/Mod/Free.v pins its own, and the two readbacks comparing with
   [free_ab_adjunction] pin that adjunction's free level by a cast.  [Set]
   appears only as the bound Set < g on the group category's object level g,
   and there is no equation.  [free_ab_hom_iso] and [free_ab_adjunction_hom]
   end [Defined], both load-bearing (each closed alone [Qed] in a renamed copy
   of #472's files, [free_ab_adjunction_hom] and [free_ab_hom_counit]
   respectively stop); [fa_eval_pointwise] ends [Qed].  On Coq 8.19.2 and
   8.20.1 the six bind the same levels (compared by [About]).

   NON-DEGENERACY, AND WHAT EACH SEPARATION COSTS.  No induction over
   [fa_eq] can yield a negative -- every constructor concludes an
   equation -- so each refutation maps OUT into a concrete abelian
   group, the technique of Instance/Grp/Free.v's
   [free_group_two_generators_nonabelian].  The general statements are
   over an ARBITRARY abelian group A with an element a ≉ 0, and they
   split by hypothesis:

   - NO decider needed: a generator is not zero
   ([free_ab_gen_not_zero]) and the group is not idempotent
   ([free_ab_gen_not_idempotent]).  The constant map at a suffices.
   The second is where the GROUP structure is spent:
   Instance/Ab.v's [ab_cancel_l] turns a + a ≈ a into a ≈ 0, and
   that cancellation is the one property separating a group from a
   monoid.
   - Decider needed: distinct generators are distinct
   ([free_ab_gen_injective]) and a sum is not one of its summands
   ([free_ab_sum_not_summand]).  Separating two DIFFERENT generators
   means exhibiting a group in which they go to different places,
   and the only such map a bare setoid supplies is the
   characteristic function of a point, which cannot be written
   without deciding [≈].  That is an ARGUMENT, not a theorem: no
   converse is machine-checked here, and the tree's precedent for
   claims of exactly this shape ([arrow_mul_respects_forces_UIP]
   and its siblings) is deliberately not followed.

   Unlike Instance/Mod/Free.v's [free_module_basis_injective] these need
   only ONE hypothesis rather than two: that file's second hypothesis is
   1 ≉ 0 in the coefficient ring, because it probes with the ring viewed
   as a module over itself and the ring may be the zero ring, whereas
   here the target's nondegeneracy is already carried by a ≉ 0.  All
   four are then instantiated at ℤ ([ring_ab Int_Ring]) and the
   two-element generating setoid, where the additive extension COMPUTES
   (e_true + e_true − e_false ↦ 3 + 3 − 5 = 1, by [eq_refl]).

   UNIVERSES, read off the constraint blocks rather than the binders.

   - [FATerm@{u u0}] and [fa_eq@{u u0}] have EMPTY constraint blocks:
   the term type sits at the generating setoid's carrier universe
   and the relation at max(u, u0), with nothing identified.
   - [FreeAbObject@{u u0 u1}] carries [u <= u1] and [u0 <= u1] -- two
   BOUNDS, no identification.  So the construction itself does not
   identify the generating setoid's carrier and relation universes.
   - That identification appears as soon as anything is stated as a
   morphism of [Sets]: [free_ab_insert] carries [u = u0], and
   [free_ab_extend], [free_ab_universal] and the four general
   non-degeneracy theorems additionally identify all three of an
   [AbObject]'s universes with it.  This is the DONORS' doing, and
   it is attributed rather than guessed: [Sets@{o so}] is declared
   as [Category@{so o o}] (Instance/Sets.v), so [obj[Sets]] is
   [SetoidObject@{o o}] with carrier and relation already
   identified, and a probe into an ARBITRARY abelian group carrying
   no free-group content at all was measured to acquire exactly the
   same block.  Nothing here adds to it, and it is not claimed
   unavoidable.
   - EXACTLY FOUR of the 76 names the file's [.glob] records (that
   count excludes the generated eliminators -- SIX of them since the
   PR “algebraic carriers are sets” (2026-09-17), not the eight an
   earlier revision wrote; see the axiom paragraph below -- and the
   4 [Program] obligations, and excludes the 4 phantom names the
   [Fail] commands put there) carry [Set] in a constraint block,
   and all
   four are the concrete two-generator witness ([ab_int_probe] and its
   three computing [Example]s), where [bool : Set] forces it.
   That took work: writing the general separations with ℤ-valued
   characteristic functions pins the generating setoid's carrier
   AND relation universes to [Set], and
   the cause was LOCATED by three probes rather than guessed -- the
   same probe with ℤ but no decidable case split is [Set]-free, and
   the same case split into an abstract target is [Set]-free, while
   the two together pin.  Abstracting the target lifts it, which is
   why the general theorems are stated over an arbitrary A.

   ZERO AXIOMS.  All 85 constants of this file -- the 72 that
   [Print Module] lists (60 definitions and proofs, SIX generated
   eliminators, 4 [Program] obligations invisible to a [.glob] sweep and
   reachable only by fully qualified name, and 2 inductive types)
   together with those types' 13 constructors -- report “Closed under
   the global context”.  [∃] in this library is [sigT], so witnesses are
   DATA and no choice principle is consumed anywhere.

   RE-MEASURED after the PR “algebraic carriers are sets” (2026-09-17),
   by generating one [Print Assumptions] per name from [Print Module]:
   72 commands, 72 “Closed under the global context”, zero [Axioms:]
   blocks; [grep -c '^constr ' Instance/Ab/Free.glob] gives 13 and
   [grep -c '^scheme '] gives 6.  An earlier revision of this paragraph
   counted 88 constants with EIGHT eliminators and 38 transparent
   definitions.  The two that went are [fa_eq_rect] and [fa_eq_rec]:
   that PR made [fa_eq] a [Prop], so Rocq generates only [fa_eq_ind] and
   [fa_eq_sind] for it.  Nothing was removed from the source, and the
   13 constructors are unchanged in both trees.

   CORRECTION (#472): #472 adds six constants, [fa_eval_pointwise],
   [free_ab_hom_iso], [free_ab_adjunction_hom] and the three [eq_refl]
   readbacks [free_ab_hom_counit], [free_ab_hom_unit] and
   [free_ab_hom_to], each “Closed under the global context” and named in
   #472's print-assumptions block; the counts above are of the file
   before them, and they were one short when written (6154fc3d, the PR
   “algebraic carriers are sets”).  [Print Module] on #472's tree lists 79
   entries, 73 of them before the six, and the source has 63 declaration
   heads before them, as it had then: 61 definitions and proofs, not 60,
   and the 2 inductive types.  So the 72 above is 73 and the 85 constants
   are 86 with the 13 constructors (92 with the six); both [fa_eq] and
   [FATerm] are “Closed under the global context”.  [Print Module]
   prints the [Inductive] keyword of [fa_eq] on a line of its own, and a
   pattern wanting the keyword and the name on one line finds 78
   entries, not 79.  Of [Set], [About] on #472's tree, on each of the 86
   names [Print Module] lists for the file before those six (constructors
   and schemes included), finds it in 49 constraint blocks, every time
   as a strict lower bound Set < u on the object level of the group
   category, the bound Instance/Ab.v's [Ab] carries since its hand pin
   in the PR “algebraic carriers are sets” (#1320, merged 2026-09-17),
   and never in an equation; so the “EXACTLY FOUR” of UNIVERSES above does not
   reproduce on this tree as a count of blocks naming [Set].  The six
   added names carry that bound and no other [Set].

   WHAT IS NOT DELIVERED.

   - No coefficient uniqueness, and -- unlike Instance/Mod/Free.v,
   which proves [fv_normal_form] -- not even the EXISTENCE of a
   normal form: nothing here says every element is a formal sum of
   generators and their negatives.  Hence no decision procedure for
   equality in the free group, no rank, and no proof that the
   insertion is injective for a general (undecidable) generating
   setoid.
   - No statement that [FreeAb] is faithful, no characterization of
   its image, no freeness of subgroups, no comparison with
   Instance/Ab/Tensor.v (see above) or with
   Instance/Ab/DirectedColimit.v's finitely generated subgroups.
   - Mac Lane §IV.8 Exercise 2 itself: no free ring, no monoid ring,
   no composite adjunction, and no comparison with
   Instance/Mon/Free.v or Instance/Rng/Free.v.
   - No [Preadditive] or [Additive] content, and no relation to
   Instance/Ab/Coproduct.v -- in particular the free group on a
   two-element setoid is NOT identified with ℤ ⊕ ℤ. 

   --------
   * * 在一个集合类上的自由阿贝尔群，以及自由-遗忘
   伴随关系

   nLab:       https://ncatlab.org/nlab/show/free+abelian+group 
   nLab:       https://ncatlab.org/nlab/show/free+object 
   nLab:       https://ncatlab.org/nlab/show/universal+morphism 
   Wikipedia:  https://en.wikipedia.org/wiki/Free_abelian_group 
   书籍: 麦克莱恩, 《工作数学家的范畴论》, 第二版,
   GTM 5, §IV.8, 练习 2 -- maclane:IV.8:ex2
   书籍: 麦克莱恩, 同上, §IV.1, 印刷页 79 (一个自由构造
   被表述为在每个变量上自然的同态集双射) --
   maclane:IV.1:construction1这是什么，以及它不是什么。[FreeAbObject X] 是集合 X 上的自由阿贝尔群：生成元的形式和，模恰好阿贝尔群定律，再加上生成元的插入 [free_ab_insert]，阿贝尔群加法的扩展 [free_ab_extend]，其唯一性 [free_ab_extend_unique]，打包的普适性质 [free_ab_universal]，函子 [FreeAb : Sets ⟶ Ab] 以及伴随 [free_ab_adjunction : FreeAb ⊣ Ab_Forget]。它是 Mac Lane §IV.8 练习 2 的一个输入——该练习要求以两种方式展示自由环的伴随关系的复合——而该练习并未在此形式化：以下没有出现环、没有出现单元环，也没有出现复合伴随关系。GAP 已记录该树，本文件随之关闭。
   Instance/Ab/Tensor.v 本身说明，
   “该树没有可商的自由阿贝尔群（在 Construction/ 和 Instance/ 中已验证）”。
   这就是为什么那里张量积是通过为 (G, H) 定制的生成元和关系来构建的原因。
   本文件提供了缺失的对象。它并没有重构 Instance/Ab/Tensor.v 以依赖它：
   那个文件的载体是形式对和的商，因此通过本文件重新构造将是一个不同的构建，而不是引用，而且这里并未声明这样的重新构造可行。为什么选择生成元和关系，而不是有限支撑函数。经典的载体——在 X 上的有限支撑 ℤ 值函数——预设了可判定相等的生成元，而 Instance/Mod/Free.v 的标题正好指出了阻碍所在：载体本身不是问题（一个遵循 [≈] 的函数与一个列表配对，证明它在列表之外为零，在一个裸集合上是可以写的），问题在于基的插入。在 x 处的基元素是一个函数，它在 x 处取 1，在其他地方取 0，而没有 x ≈ y 的判定方法，这个函数是无法写出的。使这一点致命而不仅仅是限制性的原因在于 [Ab_Forget] 落入了 [Sets]，其中的对象是集合等价体，所以对于每一个生成集合等价体，无论是否可判定，都必须存在左伴随；而仅在可判定的集合等价体上可用的构造根本无法产生伴随。因此，这里使用的表示是形式表达式 [FATerm] 的归纳式，并带有归纳同余 [fa_eq]，该同余在恰好四条阿贝尔群定律下闭合，对每个前者的同余、在 X 自身 [≈] 下的饱和，以及对称性/传递性。自反性是推导出来的（[fa_refl]），保持了关系的归纳原理在其任何使用处都比原来短一个情况。如同在 Instance/Ab/Tensor.v 和 Instance/Mod/Free.v 中，[fa_Setoid] 并未注册为类型类实例，并且元素级的语句是用 [fa_eq] 写的；这个确实是自由群作为 [Ab] 对象的 [≈]，这是由 [free_ab_equiv_is_fa_eq]（[eq_refl]）机器验证的，而不是声明的，因此 Instance/Ab.v 中的每一个群级引理都可以不变地应用于它。与 Instance/Mod/Free.v 的关系。从结构上讲，这个文件就是那个文件，只是删除了标量构造函数 [fv_smul] 和四条模律：同余关系的五个构造函数消失了，只剩下九个。设计被复制了，债务已被承认；没有共享任何代码，也不需要 Instance/Mod/Free.v。也不需要在 R := ℤ 时从它派生的构造，这是一种测量而非偏好：X 上的自由阿贝尔群就是 X 上的自由 ℤ-模，但要跨越地传递泛性质，需要一个通道 Ab → RMod ℤ，给每个阿贝尔群其 ℤ-作用，同时证明它可以反转忘记方向（[RMod_Forget_Ab]，Instance/Mod.v）。早期的修订只命名了前半部分，即该段落，并且说“没有这样的段落存在”（后半部分被省略）；自 #454 起，前半部分是错误的：Instance/Mod/Cogenerator.v 的 [Ab_to_ZMod] 是该段落，每个群都有自己的 [zsmul] 操作（在 [eq_refl] 的 [Ab_to_ZMod_group] 和 [Ab_to_ZMod_smul]）。仍然缺失的是后半部分：没有证明每个 ℤ-模的操作与 [zsmul] 一致，因此没有等价关系 [Ab ≃ RMod Int_Ring]。Instance/Mod/BaseChange.v 的 [ZExt Int_Ring] 也运行 Ab → RMod ℤ，但将 A 发送为 ℤ ⊗ A，而不是将 A 自身作为带有 ℤ 操作的对象，因此它不是这里想要的段落 -- Instance/Mod/Tensor.v 的标题记录了同样的缺失，并做出了相同的 #454 修正。因此该归约在树中不可用；原则上并未声称其不可用。优势，严格优先衡量。调解者在正式表达上是 [Fixpoint]，因此很多都是定义性的：- [eq_refl]：自由群的承载体是 [FATerm]，其 [≈] 是 [fa_eq]（[free_ab_carrier_is_FATerm]，[free_ab_equiv_is_fa_eq]）；  
   插入是生成元前者（[free_ab_insert_is_gen]）；  
   加法扩展在生成元（[free_ab_extend_generators]）上与给定函数一致，并且按定义保持零、加法和取负（[free_ab_extend_zero]，[free_ab_extend_plus]，[free_ab_extend_neg]——记录于 Leibniz [=] 在目标的承载体上，这是可转换性例外，符合内部风格，因此标题的声明是机器验证的，而非从哪个分支的义务策略触发推断出来）；  
   自由函子对象部分是形式和群（[FreeAb_obj]）；  
   泛箭头是插入（[free_ab_arrow_is_insert]）；  
   单位是插入，因此单生成器表达式 ([free_ab_unit_is_insert], [free_ab_unit_is_generator])；以及伴随的前向转置 ⌊−⌋ 是 [fa_transpose] ([free_ab_transpose_is_adj])。- 仅 [≈]：COUNIT。它是另一种转置，即 [unique_obj (ump_universal_arrows …)] 和 [ump_universal_arrows]（Theory/Universal/Arrow.v）是 [Qed] - 不透明的，因此没有东西可以通过它化简。已证明的是它对形式和（[free_ab_counit_evaluates]）的求值。- 仅 [≈]：[FreeAb] 在箭头上的作用。[LeftAdjointFunctorFromUniversalArrows] 通过通用分解而不是公式定义 [fmap]，因此重新标记生成元是一个定理（[free_ab_fmap_generators]）。更正 (#472)：counit 的诊断指出一个不透明常数，以及两个将其阻塞：[ump_universal_arrows] 和该文件自身的 [free_ab_universal]，因式分解的证明由 [free_ab_universal_arrow] 提供给 [universal_arrow_from_UMP]，并且从中读取 counit 和 [FreeAb] 的 [fmap]。在重建的七十四个模块副本中，通过 #472 测量其探针负载：仅将 [ump_universal_arrows] 转为 [Defined]，或仅将 [free_ab_universal] 使用，该文件仍然可以构建，下面引用不透明性（[counit_does_not_compute]、[fmap_generator_does_not_compute]）的两个否定仍然被拒绝；当两者都转换为 [Defined] 时，两个否定都成立，如 [Example] 在 [eq_refl] 所示，Test/ProbeFreeModule472.v 对 ℤ [−] 的 μ 和 [fmap] 的反驳也都成立，从该附加操作读取（该探针的头部；#472 的侦察测量了余单位的一半）。此处没有将任一常数转换为 [Defined]（问题 #1353 追踪 [ump_universal_arrows]）；#472 代之以在同态集形式中的相同附加操作，[free_ab_adjunction_hom]（下文的同态集形式），其余单位确实是通过转换折叠得到的。只有[≈]的读数是受保护的，而不仅仅是测量的：文件末尾的“测量的负数”部分为每个负数都包含一个[Fail]，以及第三个记录，[FreeAbObject]应用于某组自身的承载是不可以与该组转换的（仅是关于转换的说明——没有声称或证明非同构性）。每个负数都与一个必须成功的正对照配对，并且每个负数都被确认（通过在临时文件中去掉[Fail]）是一个真正的转换失败——“无法统一”——而不是缺少引用。每个在负数中命名的常量也在文件的其他地方以正命令命名，因此在定义处重命名会明显导致构建失败，而不是让[Fail]形式上变为绿色。根据惯例，这类探测器放在 Test/Probe*.v 文件中；它们之所以出现在文件中，是因为此提交正好新增了一个文件（其他 Instance/ 文件已经这样做了）。

   自然性。§IV.1 给出了一个自由构造作为双射 Ab(FreeAb X, A) ≅ Sets(X, U A)，在 X 和 A 中都是自然的，“各自单独验证”。两个条款都用自由群自身的词汇证明（[free_ab_naturality_in_set]，通过在一个生成元处求值；[free_ab_naturality_in_group]，逐点通过 [reflexivity]），而且它们确实是该对偶类本身的字段 [to_adj_nat_l] 和 [to_adj_nat_r]，随后由 [eq_refl] 在 STATEMENTS 中记录——这是一种转换检查，而不是第二次推导。HOM-SET形式 (#472)。保留了一个附属关系 FreeAb ⊣ Ab_Forget 的两个包装。[free_ab_adjunction] 来自普遍箭头，是 Instance/Rng/Free.v 的一个实例，其余的树进行消费，并且它保持不变。[free_ab_adjunction_hom] 是 Theory/Adjunction.v 的 [Build_Adjunction'] 应用于自然双射 [free_ab_hom_iso]，具有相同的左伴随 [FreeAb]、相同的右伴随和相同的插入：它的单位和前向换位是 [free_ab_adjunction] 在 [eq_refl] 上的（[free_ab_hom_unit]，[free_ab_hom_to]），它的两个自然性域是以上引用的两个定理，它的逆换位是加法扩展 [free_ab_extend]，因此它的余单位是 [eq_refl] 上恒等式的折叠（[free_ab_hom_counit]），而另一个余单位仅在 `≈` 上折叠（[free_ab_counit_evaluates]）。它存在于 Riehl 的单子 ℤ [−] §5.3（Instance/Ab/FreeMonad.v）中，其乘法和比较函子随后计算。它不是第二个自由群，也不是第二个自由函子。这两个伴随在 [eq_refl] 处被拒绝为相等，它们在一个变量形式和上的余单位也不相等（Test/ProbeFreeModule472.v，R22 和 R23）。它的宇宙层：@{c so}（Sets@{c so}）以及 [FreeAb] 的另外五个层级（群范畴的对象层级和四个内部层级），可扩展；伴随本身的最后一层，当它保持自由时没有约束，被固定为 so，就像 Instance/Mod/Free.v 固定它自己的那样，并且两个与 [free_ab_adjunction] 比较的回读通过类型转换固定了该伴随的自由层。[Set] 仅作为群范畴对象层次 g 上的绑定集合 < g 出现，并且没有方程。[free_ab_hom_iso] 和 [free_ab_adjunction_hom] 结束 [Defined]，都是承重的（每个单独闭合的 [Qed] 出现在 #472 文件的重命名副本中，[free_ab_adjunction_hom] 和 [free_ab_hom_counit] 分别停止）；[fa_eval_pointwise] 结束 [Qed]。在 Coq 8.19.2 和 8.20.1 上，这六个绑定相同的层次（通过 [About] 比较）。

   非退化性，以及每次分离的花费。没有对 [fa_eq] 的归纳可以得到负数——每个构造子结束一个方程——因此每个反证映射 OUT 到一个具体的阿贝尔群，这是 Instance/Grp/Free.v 的 [free_group_two_generators_nonabelian] 技术。一般性的陈述是针对任意阿贝尔群 A 及其元素 a ≉ 0，并且它们按假设分裂：- 不需要判定器：一个生成元不是零 ([free_ab_gen_not_zero])，并且该群不是幂等的 ([free_ab_gen_not_idempotent])。在这里，一个常数映射就足够了。第二种情况是在群结构中花费的时候：Instance/Ab.v 的 [ab_cancel_l] 将 a + a ≈ a 转化为 a ≈ 0，而这种消去性质是区分群与幺半群的唯一特性。 - 需要判定器：不同的生成元是不同的 ([free_ab_gen_injective])，并且一个和不是它的任一项的和 ([free_ab_sum_not_summand])。区分两个不同的生成元意味着需要展示一个群使它们映射到不同的位置，而裸集合提供的唯一这种映射是某一点的特征函数，而这种函数无法在不判定 [≈] 的情况下写出。那是一个论证，而不是定理：这里没有进行机器检验的逆命题，并且树对于形如 [arrow_mul_respects_forces_UIP] 及其同类的命题的先例是刻意不遵循的。

   与 Instance/Mod/Free.v 的 [free_module_basis_injective] 不同，这些只需要一个假设而不是两个：那个文件的第二个假设是在系数环中 1 ≉ 0，因为它将环视为自身的模进行探测，而环可能是零环，而这里目标的非退化性已经由 a ≉ 0 承载。那四个随后都在 ℤ 上实例化 ([ring_ab Int_Ring]) 以及二元素生成等价类上，其中加法扩展 COMPUTES (e_true + e_true − e_false ↦ 3 + 3 − 5 = 1，参见 [eq_refl])。

   宇宙（UNIVERSES），从约束块读取而不是从绑定器读取。- [FATerm@{u u0}] 和 [fa_eq@{u u0}] 有空的约束块：
   项类型位于生成的集合子载体的宇宙中，
   关系位于 max(u, u0)，没有任何识别。 
   - [FreeAbObject@{u u0 u1}] 携带 [u <= u1] 和 [u0 <= u1] -- 两个边界，没有识别。因此构造本身并没有识别生成集合子的载体和关系宇宙。 
   - 一旦任何东西被声明为 [Sets] 的态射，这种识别就会出现：[free_ab_insert] 携带 [u = u0]，和 [free_ab_extend]，[free_ab_universal] 以及四个一般非退化定理额外识别了 [AbObject] 的所有三个宇宙与它本身。这是捐助者的所为，并且这是有根据的而非猜测：[Sets@{o so}] 被声明为 [Category@{so o o}]（Instance/Sets.v），所以 [obj[Sets] 是 [SetoidObject@{o o}]，其中的载体和关系已被识别，对一个不含自由群内容的任意阿贝尔群进行的探测正好获得了相同的块。这里没有任何内容可以增加它，也没有声称这是不可避免的。- 在文件的 [.glob] 记录的 76 个名字中，恰好有四个（这个统计不包括生成的消除器——六个，因为 PR “代数载体是集合”（2026-09-17），而不是早期版本写的八个；见下面的公理段落——以及四个 [Program] 义务，也不包括 [Fail] 命令放置的四个幻影名字）在约束块中带有 [Set]，并且全部四个都是具体的双生成器见证（[ab_int_probe] 及其三个计算 [Example]），其中 [bool : Set] 强制它。这很费力：用 ℤ 值特征函数编写一般分离将生成的集合载体 AND 关系宇宙固定到 [Set]，而且原因是通过三个探针定位的，而不是猜测的——使用 ℤ 的同一个探针但没有可判定的情况分裂是 [Set] 自由的，而将同一情况分裂到抽象目标是 [Set] 自由的，而两者结合则固定。抽象目标会提升它，这就是为什么一般定理是针对任意 A 陈述的。零公理。这个文件的所有85个常量——[Print Module]列出的72个（60个定义和证明，6个生成的消去子，4个[Program]义务对[.glob]扫描不可见且只能通过完全限定名访问，以及2个归纳类型），以及这些类型的13个构造函数——都报告“在全局上下文下封闭”。在这个库中，[∃]是[sigT]，因此见证是DATA，并且在任何地方都没有消耗选择原理。在 PR “代数载体是集合”（2026-09-17）之后重新测量，通过从 [Print Module] 为每个名字生成一个 [Print Assumptions]：72 条命令，72 个“在全局上下文下封闭”，没有 [Axioms:] 块；[grep -c '^constr ' Instance/Ab/Free.glob] 给出 13 个，[grep -c '^scheme '] 给出 6 个。该段落的早期修订版本统计了 88 个常量，带有八个消解器和 38 个透明定义。移除的两个是 [fa_eq_rect] 和 [fa_eq_rec]：该 PR 使 [fa_eq] 成为 [Prop]，因此 Rocq 只为它生成 [fa_eq_ind] 和 [fa_eq_sind]。源代码中没有任何内容被移除，13 个构造函数在两棵树中保持不变。更正 (#472)：#472 添加了六个常量，[fa_eval_pointwise]、[free_ab_hom_iso]、[free_ab_adjunction_hom] 以及三个 [eq_refl] 读取值 [free_ab_hom_counit]、[free_ab_hom_unit] 和 [free_ab_hom_to]，它们都“在全局上下文下封闭”，并在 #472 的打印假设块中命名；上述计数是它们之前文件的数量，写入时少了一个（6154fc3d，PR“代数载体是集合”）。#472 的树上的 [Print Module] 列出了 79 个条目，其中 73 个在六个之前，源文件在它们之前有 63 个声明头，就像当时一样：61 个定义和证明，而不是 60 个，以及 2 个归纳类型。因此，上述 72 应为 73，85 个常量是 86 个，包括 13 个构造函数（与这六个一共为 92）；[fa_eq] 和 [FATerm] 都是“在全局上下文下封闭”的。[Print Module]
   在单独一行上打印 [Inductive] 的 [fa_eq] 关键字，而在同一行上寻找关键字和名称的模式找到了 78 个条目，而不是 79 个。在 [Set] 中，#472 的树上的 [About]，在文件中这六个名称（包括构造函数和方案）之前列出的 86 个名称中，发现它出现在 49 个约束块中，每次都作为群范畴对象层级的严格下界 Set < u，这个下界 Instance/Ab.v 的 [Ab] 自从在 PR “algebraic carriers are sets” (#1320，合并于 2026-09-17) 中手动标记以来一直存在，并且从不出现在方程中；因此，上述 UNIVERSES 的“恰好四个”并没有在这棵树上以命名 [Set] 的块的数量重新出现。新增的这六个名称承载了该下界，而没有其他 [Set]。

   未交付的是什么。- 没有系数的唯一性，并且——不像 Instance/Mod/Free.v 那样，它证明了 [fv_normal_form] ——甚至没有正规形式的存在性：这里没有任何内容说明每个元素都是生成元及其相反元素的形式和。因此，自由群中没有等式的判定程序，没有秩，也没有证明对于一般（不可判定的）生成集合，插入是单射的。 - 没有声明 [FreeAb] 是忠实的，没有描述其像的特征，没有子群的自由性，也没有与 Instance/Ab/Tensor.v（见上文）或 Instance/Ab/DirectedColimit.v 的有限生成子群进行比较。 - Mac Lane 第 IV.8 节练习 2 本身：没有自由环，没有幺半群环，没有复合伴随关系，也没有与 Instance/Mon/Free.v 或 Instance/Rng/Free.v 的比较。- 没有 [Preadditive] 或 [Additive] 内容，也与 Instance/Ab/Coproduct.v 无关——特别是二元素集合上的自由群并未被认同为 ℤ ⊕ ℤ。
*)

(*
 The file-global obligation tactic is [cat_simpl], which would run wide
 proof searches on the obligations below and has already introduced the
 parameters by the time an obligation is opened.  Switched off here --
 the Instance/Mod/Free.v idiom -- so every obligation starts with an
 explicit [intros]. 

 --------
 文件全局义务策略是 [cat_simpl]，它将对以下义务进行广泛的证明搜索，并且在打开义务时已经引入了参数。这里已关闭——Instance/Mod/Free.v 习惯——因此每个义务都以明确的 [intros] 开始。
*)
#[local] Obligation Tactic := idtac.

(* * ** Formal sums and the group quotient / * ** 正式和与群商 *)

Section FreeAbelian.

Context (X : SetoidObject).

(*
 Formal expressions over the generating setoid: generators, zero, sum,
 negation.  This is Instance/Mod/Free.v's [FVTerm] with the scalar
 former [fv_smul] deleted.  Negation is a CONSTRUCTOR rather than
 iterated addition: there is no scalar ring here to take (-1) from, and
 the abelian group being built is what a derived negation would need. 

 --------
 生成集族上的形式表达式：生成元、零、和、取负。这是 Instance/Mod/Free.v 的 [FVTerm]，已删除标量形式 [fv_smul]。取负是一个构造器，而不是迭代加法：这里没有标量环可以取 (-1)，而构造的阿贝尔群就是派生取负所需要的。
*)
Inductive FATerm : Type :=
  | fa_gen  : carrier X → FATerm
  | fa_zero : FATerm
  | fa_plus : FATerm → FATerm → FATerm
  | fa_neg  : FATerm → FATerm.

(*
 The quotienting relation: congruence for each former (saturating under
 the generating setoid's own [≈]), the four abelian-group laws,
 symmetry and transitivity.  Reflexivity is derived below, keeping the
 relation's induction principle one case shorter everywhere it is
 consumed. 

 --------
 商关系：对每个前者的合同（在生成的等价类 [≈] 下饱和）、四个阿贝尔群定律、对称性和传递性。自反性在下面推导，保持该关系的归纳原则在使用的每个地方都少一个案例。
*)
Inductive fa_eq : FATerm → FATerm → Prop :=
  | fae_gen {x y : carrier X} : x ≈ y → fa_eq (fa_gen x) (fa_gen y)
  | fae_plus {s s' t t'} :
      fa_eq s s' → fa_eq t t' → fa_eq (fa_plus s t) (fa_plus s' t')
  | fae_neg {s s'} : fa_eq s s' → fa_eq (fa_neg s) (fa_neg s')

  (* abelian group / 阿贝尔群 *)
  | fae_assoc (s t u : FATerm) :
      fa_eq (fa_plus (fa_plus s t) u) (fa_plus s (fa_plus t u))
  | fae_comm (s t : FATerm) : fa_eq (fa_plus s t) (fa_plus t s)
  | fae_zero_l (s : FATerm) : fa_eq (fa_plus fa_zero s) s
  | fae_neg_l (s : FATerm) : fa_eq (fa_plus (fa_neg s) s) fa_zero

  | fae_sym {s t} : fa_eq s t → fa_eq t s
  | fae_trans {s t u} : fa_eq s t → fa_eq t u → fa_eq s u.

Lemma fa_refl (s : FATerm) : fa_eq s s.
Proof.
  induction s.
  - exact (fae_gen (reflexivity _)).
  - exact (fae_trans (fae_sym (fae_zero_l fa_zero)) (fae_zero_l fa_zero)).
  - exact (fae_plus IHs1 IHs2).
  - exact (fae_neg IHs).
Qed.

Lemma fa_eq_Equivalence : Equivalence fa_eq.
Proof.
  constructor.
  - exact fa_refl.
  - exact (fun s t => fae_sym).
  - exact (fun s t u => fae_trans).
Qed.

(*
 Deliberately NOT registered as a typeclass instance -- the
 Instance/Ab/Tensor.v and Instance/Mod/Free.v convention.  Statements
 about elements of the free group below are written with [fa_eq]; the
 [≈] of [FreeAbObject] as an object of [Ab] IS that relation,
 definitionally, so the group-level lemmas of Instance/Ab.v apply to it
 unchanged. 

 --------
 故意不注册为类型类实例——Instance/Ab/Tensor.v 和 Instance/Mod/Free.v 的惯例。下面关于自由群元素的陈述是用 [fa_eq] 写的；作为 [Ab] 对象的 [FreeAbObject] 的 [≈] 在定义上即是该关系，因此 Instance/Ab.v 的群级引理对它仍然适用，保持不变。
*)
Definition fa_Setoid : Setoid FATerm := {|
  equiv        := fa_eq;
  setoid_equiv := fa_eq_Equivalence
|}.

(*
   * ** The free abelian group

   Every law of the group is a constructor of the relation, so the
   record is a literal with ZERO proof obligations.  It is written out in
   one piece so that the underlying setoid, the unit, the addition and
   the negation are all visible at a glance and all reduce.

   An earlier revision stopped at “ZERO proof obligations”.  That is still
   true, and since the PR “algebraic carriers are sets” (2026-09-17) the
   literal has one more field: [fa_eq] IS a [Prop]-valued relation, so it is
   its own [Prop] mirror and both implications of [cmon_prop] are the
   identity. 

   --------
   * ** 自由阿贝尔群

   群的每条定律都是该关系的构造器，因此该记录是一个字面量，无需任何证明义务。它被完整写出，以便底层的集合等价关系、单位元、加法和取反操作一目了然，并且都可以约简。

   早期的修订只停在“零证明义务”。这仍然成立，并且自从 PR “代数载体是集合”（2026-09-17）以来，该字面量多了一个字段：[fa_eq] 是一个 [Prop] 值的关系，因此它是其自身 [Prop] 的镜像，且 [cmon_prop] 的两个蕴含都是恒等式。
*)
Definition FreeAbObject : AbObject := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := FATerm; is_setoid := fa_Setoid |};
    cmon_zero := fa_zero;
    cmon_plus := fa_plus;
    cmon_plus_respects := fun _ _ Hs _ _ Ht => fae_plus Hs Ht;
    cmon_plus_assoc := fae_assoc;
    cmon_plus_comm := fae_comm;
    cmon_plus_zero_l := fae_zero_l;
    cmon_prop := @PropEquiv_of_relation _ fa_Setoid fa_eq
                   (fun _ _ h => h) (fun _ _ h => h)
  |};
  ab_neg := fa_neg;
  ab_neg_respects := fun _ _ Hs => fae_neg Hs;
  ab_neg_left := fae_neg_l
|}.

(*
 The two claims the paragraph above [fa_Setoid] makes, machine-checked
 rather than asserted: the carrier of the free group, seen through the
 forgetful functor, IS the type of formal expressions, and its [≈] IS
 the quotienting relation.  These are equations between TYPES, not
 between morphisms -- the convertibility exception the house style
 sanctions. 

 --------
 上面段落 [fa_Setoid] 提出的两个声明，是机器检查的，而不是断言的：通过遗忘函子看到的自由群的载体，本身就是形式表达的类型，并且它的 [≈] 是商关系。这些是类型之间的方程，而不是态射之间的——可转换性例外是该风格允许的。
*)
Example free_ab_carrier_is_FATerm :
  carrier (Ab_Forget FreeAbObject) = FATerm := eq_refl.

Example free_ab_equiv_is_fa_eq (s t : FATerm) :
  (@equiv _ (is_setoid (Ab_Forget FreeAbObject)) s t) = fa_eq s t
  := eq_refl.

(*
   * ** The insertion of generators

   A generator becomes the corresponding formal expression.
   Respectfulness is the congruence constructor [fae_gen], supplied by
   [exact] rather than as a record field: the target's [≈] is [fa_eq] by
   conversion but not by unification, and only [exact] will convert. 

   --------
   * ** 发电机的插入

   发电机会成为相应的形式表达式。
   尊重性是由 [exact] 提供的同余构造器 [fae_gen]，而不是作为记录字段：目标的 [≈] 通过转换而不是通过统一变为 [fa_eq]，且只有 [exact] 会进行转换。
*)
Definition free_ab_insert : X ~{Sets}~> Ab_Forget FreeAbObject.
Proof.
  unshelve refine {| morphism := fa_gen |}.
  intros x y H; exact (fae_gen H).
Defined.

(* The insertion IS the generator former on the nose. / 插入件就是鼻子上的发电机前身。 *)
Example free_ab_insert_is_gen (x : carrier X) :
  free_ab_insert x = fa_gen x := eq_refl.

(* * ** The additive extension of a function on generators / * ** 函数在生成元上的加法扩展 *)

Section Extension.

Context (A : AbObject).
Context (h : X ~{Sets}~> Ab_Forget A).

(*
 Fold a formal expression through the target group's operations.  It
 computes on constructors, which is what makes both homomorphism
 obligations below hold by [reflexivity]. 

 --------
 通过目标组的运算折叠一个形式表达式。它在构造子上进行计算，这正是使下面的同态义务通过 [reflexivity] 成立的原因。
*)
Fixpoint fa_eval (t : FATerm) : carrier (cmon_setoid A) :=
  match t with
  | fa_gen x    => h x
  | fa_zero     => cmon_zero A
  | fa_plus s t => cmon_plus A (fa_eval s) (fa_eval t)
  | fa_neg s    => ab_neg A (fa_eval s)
  end.

(*
 Respectfulness is one induction over the relation: nine cases, one per
 constructor of [fa_eq].  Four are met by the corresponding law of the
 target group; the other five are not laws -- [fae_gen] is saturation
 under X's own [≈], two are congruence for a former, and two are the
 target setoid's symmetry and transitivity. 

 --------
 尊重性是在关系上的一种归纳：九种情况，每个 [fa_eq] 的构造子对应一种情况。其中四种情况通过目标群的相应定律得到满足；另外五种情况不是定律——[fae_gen] 是在 X 自身 [≈] 下的饱和，两个是前者的合同律，另外两个是目标集合的对称性和传递性。
*)
Lemma fa_eval_respects (s t : FATerm) : fa_eq s t → fa_eval s ≈ fa_eval t.
Proof.
  intro He.
  (*
 Since the PR “algebraic carriers are sets” (2026-09-17) [fa_eq] is a
 [Prop] inductive and eliminates only into [Prop] goals, while `≈` is
 [Type]-valued.  [pequiv_to] puts a [Prop] goal in front of the
 elimination and each branch returns to `≈` with [pequiv_from]; the nine
 cases and what discharges each are exactly as before. 

 --------
 自从 PR “代数载体是集合”（2026-09-17）以来，[fa_eq] 是一个 [Prop] 归纳的，并且只消除为 [Prop] 目标，而 `≈` 是 [Type] 值。[pequiv_to] 在消除前放置一个 [Prop] 目标，每个分支返回到 `≈` 并带有 [pequiv_from]；九种情况以及每种情况的解除方法与之前完全相同。
*)
  apply pequiv_to.
  induction He as
    [ x y Hxy
    | s s' t t' _ IHs _ IHt
    | s s' _ IHs
    | s t u | s t | s | s
    | s t _ IHst
    | s t u _ IHst _ IHtu ]; simpl.
  - apply pequiv_from; exact (proper_morphism h _ _ Hxy).
  - apply pequiv_from.
    exact (cmon_plus_respects A _ _ (pequiv_to _ _ IHs)
                                _ _ (pequiv_to _ _ IHt)).
  - apply pequiv_from.
    exact (ab_neg_respects A _ _ (pequiv_to _ _ IHs)).
  - apply pequiv_from; exact (cmon_plus_assoc A _ _ _).
  - apply pequiv_from; exact (cmon_plus_comm A _ _).
  - apply pequiv_from; exact (cmon_plus_zero_l A _).
  - apply pequiv_from; exact (ab_neg_left A _).
  - exact (symmetry IHst).
  - exact (transitivity IHst IHtu).
Qed.

(*
 The extension, as a morphism of [Ab].  [AbHom] IS [CMonHom]
 (Instance/Ab.v, a bare [Definition]), so the obligations are
 respectfulness of the fold and preservation of zero and of addition --
 preservation of NEGATION is not among them, being the derived
 [ab_map_neg] rather than a field.  The last two hold by
 [reflexivity], the fixpoint's clauses BEING those two equations.  One
 uniform body is used so that the proof does not depend on the order
 [Program] emits the obligations in. 

 --------
 作为 [Ab] 的态射的扩展。[AbHom] 是 [CMonHom]（实例/Ab.v，一个空的 [Definition]），因此义务是对 fold 的尊重以及零和加法的保持——保持取反不在其中，因为它是派生的 [ab_map_neg] 而不是一个域。最后两个通过 [reflexivity] 来保持，固定点的条款就是这两个方程。使用一个统一的主体，以便证明不依赖于 [Program] 发出义务的顺序。
*)
Program Definition free_ab_extend : FreeAbObject ~{Ab}~> A := {|
  cmon_map := {| morphism := fa_eval |}
|}.
Next Obligation.
  first [ (intros s t He; exact (fa_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fa_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fa_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.

(* It agrees with [h] on the generators -- definitionally, not up to [≈]. / 它在生成元方面与 [h] 一致——从定义上来说，不取决于 [≈]。 *)
Example free_ab_extend_generators (x : carrier X) :
  cmon_map free_ab_extend (fa_gen x) = h x := eq_refl.

(*
 The two homomorphism laws, recorded at Leibniz [=] on the CARRIER so
 that the header's strength claim is machine-checked rather than
 inferred from which branch of the obligation tactic fired.  This is
 the convertibility exception the house style sanctions: these are
 equations between elements of A's carrier, not between morphisms. 

 --------
 两个同态定律，记录在莱布尼茨 [=] 上的载体，以便头部的强度声明是经过机器检查的，而不是从义务策略触发的分支推断出来的。这是可转换性例外，符合本馆风格：这些是 A 的载体元素之间的方程，而不是态射之间的方程。
*)
Example free_ab_extend_zero :
  cmon_map free_ab_extend fa_zero = cmon_zero A := eq_refl.

Example free_ab_extend_plus (s t : FATerm) :
  cmon_map free_ab_extend (fa_plus s t)
    = cmon_plus A (cmon_map free_ab_extend s)
                  (cmon_map free_ab_extend t) := eq_refl.

(*
 Preservation of negation is a THEOREM in [Ab] rather than a field, but
 for THIS homomorphism it is nevertheless definitional, the fixpoint
 having a clause for [fa_neg].  So the derived [ab_map_neg] is not
 needed on the extension's own side; it is needed on the COMPETITOR's
 side in the uniqueness proof below. 

 --------
 在 [Ab] 中，否定的保持是一个定理，而不是一个领域，但对于这个同态，它仍然是定义性的，固定点有一个 [fa_neg] 的子句。因此，派生的 [ab_map_neg] 在扩展自身一侧并不需要；它在下面唯一性证明中的竞争者一侧才需要。
*)
Example free_ab_extend_neg (s : FATerm) :
  cmon_map free_ab_extend (fa_neg s)
    = ab_neg A (cmon_map free_ab_extend s) := eq_refl.

(*
   * *** Uniqueness

   Any homomorphism out of the free group agreeing with [h] on the
   generators IS the extension.  The induction has one case per former,
   four in all: the generator case is the agreement hypothesis [Hg]
   itself, and the other three are homomorphism laws of the competitor --
   preservation of zero, of sums, and of negation (Instance/Ab.v's
   [ab_map_neg], a theorem and not a field, which is exactly the place
   that derivation earns its keep). 

   --------
   * *** 唯一性

   任何从自由群出的同态，如果在生成元上与 [h] 一致，则就是该扩展。归纳法每个原子都有一个情况，总共四种：生成元情况就是一致性假设 [Hg] 本身，其余三种是竞争者的同态法则——零的保持、和的保持、以及取负的保持（Instance/Ab.v 的 [ab_map_neg]，一个定理而非域，正是推导发挥作用的地方）。
*)
Lemma free_ab_extend_unique (g : FreeAbObject ~{Ab}~> A)
  (Hg : ∀ x : carrier X, cmon_map g (fa_gen x) ≈ h x) (t : FATerm) :
  cmon_map g t ≈ fa_eval t.
Proof.
  induction t as [ x | | t1 IHt1 t2 IHt2 | t IHt ]; simpl.
  - exact (Hg x).
  - exact (cmon_map_zero g).
  - refine (transitivity (cmon_map_plus g t1 t2) _).
    exact (cmon_plus_respects A _ _ IHt1 _ _ IHt2).
  - refine (transitivity (ab_map_neg g t) _).
    exact (ab_neg_respects A _ _ IHt).
Qed.

End Extension.

Arguments fa_eval {A} h t.
Arguments free_ab_extend {A} h.

(*
   * ** The universal property, in the shape [universal_arrow_from_UMP]
   consumes 

   --------
   * ** 通用性质，在形状 [universal_arrow_from_UMP] 中消耗
*)
Theorem free_ab_universal :
  ∀ (A : AbObject) (h : X ~{Sets}~> Ab_Forget A),
    ∃! g : FreeAbObject ~{Ab}~> A,
      h ≈ fmap[Ab_Forget] g ∘ free_ab_insert.
Proof.
  intros A h.
  unshelve eexists.
  - exact (free_ab_extend h).
  - intro x; simpl; reflexivity.
  - intros g Hg t; simpl.
    symmetry; apply (free_ab_extend_unique A h g).
    intro x; symmetry; exact (Hg x).
Qed.

End FreeAbelian.

Arguments fa_gen {X} x.
Arguments fa_zero {X}.
Arguments fa_plus {X} s t.
Arguments fa_neg {X} s.
Arguments fa_eq {X} s t.
Arguments fa_refl {X} s.
Arguments fae_gen {X x y} _.
Arguments fae_plus {X s s' t t'} _ _.
Arguments fae_neg {X s s'} _.
Arguments fae_assoc {X} s t u.
Arguments fae_comm {X} s t.
Arguments fae_zero_l {X} s.
Arguments fae_neg_l {X} s.
Arguments fae_sym {X s t} _.
Arguments fae_trans {X s t u} _ _.
Arguments fa_eval {X A} h t.
Arguments free_ab_extend {X A} h.
Arguments fa_eval_respects {X} A h s t _.
Arguments free_ab_extend_unique {X} A h g _ t.

(* * ** The universal arrow, the free functor and the adjunction / * ** 普遍箭头、自由函子与伴随 *)

(*
 The free abelian group packaged as a universal arrow.  By
 Theory/Universal/Arrow.v this IS an initial object of the comma
 category [=(X) ↓ Ab_Forget]. 

 --------
 作为一个通用箭头打包的自由阿贝尔群。根据 Theory/Universal/Arrow.v，这是余逗类 [=(X) ↓ Ab_Forget] 的一个初始对象。
*)
Definition free_ab_universal_arrow (X : Sets)
  : UniversalArrow X Ab_Forget :=
  universal_arrow_from_UMP X Ab_Forget (FreeAbObject X) (free_ab_insert X)
    (free_ab_universal X).

(*
 The same content in the direct encoding, where the universal object is
 named rather than projected out of a comma category. 

 --------
 直接编码中的相同内容，其中通用对象被命名，而不是从逗号类型中投射出来。
*)
Program Definition free_ab_AUniversalArrow (X : Sets)
  : AUniversalArrow X Ab_Forget (FreeAbObject X) := {|
  universal_arrow := free_ab_insert X
|}.
Next Obligation.
  intros X A h.
  unshelve eexists.
  - exact (free_ab_extend h).
  - intro x; simpl; reflexivity.
  - intros g Hg t; simpl.
    (* [AUniversalArrow]'s uniqueness field is oriented the other way round from the comma-packaged one, hence the [symmetry]. / [AUniversalArrow] 的唯一性字段的方向与逗号包装的那个相反，因此是 [symmetry]。 *)
    symmetry; apply (free_ab_extend_unique A h g).
    intro x; exact (Hg x).
Qed.

(*
 The functor and the adjunction come out of the generic machinery with
 no further proof -- the route Instance/Mod/Free.v, Instance/Grp/Free.v,
 Instance/Coq/Monoid/Free.v and Construction/Free/Quiver.v all take. 

 --------
 函子和伴随从通用机制中得出，无需进一步的证明——路径 Instance/Mod/Free.v、Instance/Grp/Free.v、Instance/Coq/Monoid/Free.v 和 Construction/Free/Quiver.v 都适用。
*)
Definition FreeAb : Sets ⟶ Ab :=
  LeftAdjointFunctorFromUniversalArrows Ab_Forget free_ab_universal_arrow.

Definition free_ab_adjunction : FreeAb ⊣ Ab_Forget :=
  AdjunctionFromUniversalArrows Ab_Forget free_ab_universal_arrow.

(*
   * The free functor's object part is the formal-sum group,
   definitionally. 

   --------
   * 自由函子在对象部分定义上是形式和群。
*)
Example FreeAb_obj (X : Sets) : FreeAb X = FreeAbObject X := eq_refl.

(*
   * The universal arrow is the insertion of generators on the nose:
   [universal_arrow_from_UMP] stores the supplied morphism as the second
   projection of the comma object it builds, so no proof is involved. 

   --------
   * 通用箭头是在鼻子上插入生成元：
   [universal_arrow_from_UMP] 将提供的态射存储为它构建的逗号对象的第二投影，因此不涉及证明。
*)
Example free_ab_arrow_is_insert (X : Sets) :
  @arrow _ _ X Ab_Forget (free_ab_universal_arrow X) = free_ab_insert X
  := eq_refl.

(*
   * ** The unit is the insertion of generators

   [unit] is DERIVED in Theory/Adjunction.v (it is the transpose of the
   identity), not a field, so what it computes to has to be checked.  It
   is [fmap[U] id ∘ arrow], and [fmap[Ab_Forget] id] is the identity
   setoid map, so the unit is [free_ab_insert] itself. 

   --------
   * ** 单位是生成元的插入

   [unit] 在 Theory/Adjunction.v 中被推导（它是恒等的转置），不是域，所以它的计算结果需要检查。它是 [fmap[U] id ∘ arrow]，而 [fmap[Ab_Forget] id] 是恒等的集合等价映射，因此单位是 [free_ab_insert] 本身。
*)

Definition free_ab_unit (X : Sets)
  : X ~{Sets}~> Ab_Forget (FreeAb X) :=
  @Category.Theory.Adjunction.unit _ _ _ _ free_ab_adjunction X.

Example free_ab_unit_is_insert (X : Sets) (x : carrier X) :
  free_ab_unit X x = free_ab_insert X x := eq_refl.

Example free_ab_unit_is_generator (X : Sets) (x : carrier X) :
  free_ab_unit X x = @fa_gen X x := eq_refl.

(*
   * ** The counit evaluates a formal sum

   The counit is the OTHER transpose, and it does not compute: it is
   [unique_obj (ump_universal_arrows …)] and [ump_universal_arrows]
   (Theory/Universal/Arrow.v) is [Qed]-opaque, so no [eq_refl] is
   available on this side and none is claimed.  What is available -- and
   is the content -- is that it agrees with evaluation up to [≈].
   CORRECTION (#472): one of two causes; this file's own
   [free_ab_universal] is the other (the header's STRENGTHS), and the
   counit of the hom-set form [free_ab_adjunction_hom] below is this
   fold at [eq_refl] ([free_ab_hom_counit]). 

   --------
   * ** 共单元评估形式和

   共单元是另一个转置，它不进行计算：它是
   [unique_obj (ump_universal_arrows …)] 和 [ump_universal_arrows]
   （Theory/Universal/Arrow.v）是 [Qed] -不透明的，所以在这一边没有可用的 [eq_refl]，也没有声称有。可用的——也是其内容——是它在 [≈] 范围内与评估一致。
   更正 (#472)：两个原因之一；该文件自身的
   [free_ab_universal] 是另一个（头部的 STRENGTHS），而下文同态集合形式的共单元 [free_ab_adjunction_hom] 是这个在 [eq_refl] 处的折叠（ZWZ8WZZ）。
*)

Definition free_ab_counit (A : Ab)
  : FreeAb (Ab_Forget A) ~{Ab}~> A :=
  @Category.Theory.Adjunction.counit _ _ _ _ free_ab_adjunction A.

Lemma free_ab_counit_generator (A : Ab) (a : carrier (Ab_Forget A)) :
  cmon_map (free_ab_counit A) (fa_gen a) ≈ a.
Proof.
  exact (@to_adj_counit _ _ _ _ free_ab_adjunction A a).
Qed.

Theorem free_ab_counit_evaluates (A : Ab) (t : FATerm (Ab_Forget A)) :
  cmon_map (free_ab_counit A) t ≈ fa_eval (@id Sets (Ab_Forget A)) t.
Proof.
  apply (free_ab_extend_unique A (@id Sets (Ab_Forget A))
           (free_ab_counit A)).
  intro a; exact (free_ab_counit_generator A a).
Qed.

(*
   * ** The free functor relabels generators

   [LeftAdjointFunctorFromUniversalArrows] defines [fmap] by universal
   factorization, not by a formula, so what the functor does to a
   generator has to be proved; it is [≈] and not [eq_refl]. 

   --------
   * ** 自由函子重新标记生成元

   [LeftAdjointFunctorFromUniversalArrows] 通过普适分解定义了 [fmap]，而不是通过公式定义，因此必须证明函子对生成元的作用；它是 [≈]，而不是 [eq_refl]。
*)
Lemma free_ab_fmap_generators {X Y : Sets} (u : X ~{Sets}~> Y)
  (x : carrier X) :
  cmon_map (fmap[FreeAb] u) (fa_gen x) ≈ fa_gen (u x).
Proof.
  symmetry.
  exact (unique_property
           (ump_universal_arrows (free_ab_universal_arrow X)
              (@arrow _ _ Y Ab_Forget (free_ab_universal_arrow Y) ∘ u)) x).
Qed.

(*
   * ** The adjunction bijection, and its two naturality clauses

   The forward transpose is restriction to the generators, and it IS the
   adjunction's own ⌊−⌋ -- [free_ab_transpose_is_adj] records that by
   [eq_refl] -- so the two clauses below, proved in the free group's own
   vocabulary, are the class's fields and not weaker statements about
   some other map. 

   --------
   * ** 函数对偶一一对应及其两个自然性子句

   前向转置是对生成元的限制，它就是伴随的自身 ⌊−⌋ —— [free_ab_transpose_is_adj] 通过 [eq_refl] 记录了这一点 —— 因此下面的两个子句，在自由群自身的词汇中证明，是该类的字段，而不是关于某个其他映射的较弱陈述。
*)

Definition fa_transpose {X : Sets} {A : Ab}
  (g : FreeAb X ~{Ab}~> A) : X ~{Sets}~> Ab_Forget A :=
  fmap[Ab_Forget] g ∘ free_ab_insert X.

Example free_ab_transpose_is_adj {X : Sets} {A : Ab}
  (g : FreeAb X ~{Ab}~> A) :
  to (@adj _ _ _ _ free_ab_adjunction X A) g = fa_transpose g := eq_refl.

(*
   * Restriction to the generators is a bijection: the inverse is additive
   extension.  Both round trips are [≈] statements about morphisms, and
   the first of them is [reflexivity] at every generator. 

   --------
   * 对生成元的限制是一个双射：逆映射是加法扩展。两个往返都是关于态射的 [≈] 陈述，且其中第一个在每个生成元上都是 [reflexivity]。
*)

Lemma fa_transpose_extend {X : Sets} {A : Ab}
  (h : X ~{Sets}~> Ab_Forget A) : fa_transpose (free_ab_extend h) ≈ h.
Proof. intro x; simpl; reflexivity. Qed.

Lemma fa_extend_transpose {X : Sets} {A : Ab}
  (g : FreeAb X ~{Ab}~> A) : free_ab_extend (fa_transpose g) ≈ g.
Proof.
  intro t; simpl.
  symmetry; apply (free_ab_extend_unique A (fa_transpose g) g).
  intro x; simpl; reflexivity.
Qed.

(* * *** Naturality in the generating set / * *** 生成集的自然性 *)
Theorem free_ab_naturality_in_set {X Y : Sets} {A : Ab}
  (g : FreeAb Y ~{Ab}~> A) (u : X ~{Sets}~> Y) :
  fa_transpose (g ∘ fmap[FreeAb] u) ≈ fa_transpose g ∘ u.
Proof.
  intro x; simpl.
  exact (proper_morphism (cmon_map g) _ _ (free_ab_fmap_generators u x)).
Qed.

(*
   * *** Naturality in the target group

   Both sides are the same composite of underlying functions, so this is
   [reflexivity] pointwise. 

   --------
   * *** 在目标群中的自然性

   双方都是基础函数的相同复合，因此这是点态的 [reflexivity]。
*)
Theorem free_ab_naturality_in_group {X : Sets} {A A' : Ab}
  (k : A ~{Ab}~> A') (g : FreeAb X ~{Ab}~> A) :
  fa_transpose (k ∘ g) ≈ fmap[Ab_Forget] k ∘ fa_transpose g.
Proof. intro x; simpl; reflexivity. Qed.

(*
   * The two theorems just proved ARE the adjunction's naturality fields at
   this adjunction: the statements are convertible, so these are the
   clauses and not restatements about a different map. 

   --------
   * 刚刚证明的两个定理正是该伴随下伴随的自然性领域：这些陈述是可互换的，所以这些是条款，而不是关于不同映射的重述。
*)
Example free_ab_naturality_in_set_is_to_adj_nat_l
  {X Y : Sets} {A : Ab} (g : FreeAb Y ~{Ab}~> A) (u : X ~{Sets}~> Y) :
  (to (@adj _ _ _ _ free_ab_adjunction X A) (g ∘ fmap[FreeAb] u)
     ≈ to (@adj _ _ _ _ free_ab_adjunction Y A) g ∘ u)
  = (fa_transpose (g ∘ fmap[FreeAb] u) ≈ fa_transpose g ∘ u) := eq_refl.

Example free_ab_naturality_in_group_is_to_adj_nat_r
  {X : Sets} {A A' : Ab} (k : A ~{Ab}~> A') (g : FreeAb X ~{Ab}~> A) :
  (to (@adj _ _ _ _ free_ab_adjunction X A') (k ∘ g)
     ≈ fmap[Ab_Forget] k ∘ to (@adj _ _ _ _ free_ab_adjunction X A) g)
  = (fa_transpose (k ∘ g) ≈ fmap[Ab_Forget] k ∘ fa_transpose g) := eq_refl.

(** ** The triangle identities / ** 三角形恒等式 *)

Corollary free_ab_triangle_left (X : Sets) :
  free_ab_counit (FreeAb X) ∘ fmap[FreeAb] (free_ab_unit X)
    ≈ @id Ab (FreeAb X).
Proof. exact (@counit_fmap_unit _ _ _ _ free_ab_adjunction X). Qed.

Corollary free_ab_triangle_right (A : Ab) :
  fmap[Ab_Forget] (free_ab_counit A) ∘ free_ab_unit (Ab_Forget A)
    ≈ @id Sets (Ab_Forget A).
Proof. exact (@fmap_counit_unit _ _ _ _ free_ab_adjunction A). Qed.

Arguments fa_transpose {X A} g.
Arguments free_ab_fmap_generators {X Y} u x.

(*
   * ** The same adjunction in hom-set form (#472)

   A second packaging of [FreeAb ⊣ Ab_Forget], with the SAME left adjoint
   [FreeAb] and the same insertion: Theory/Adjunction.v's hom-set
   constructor [Build_Adjunction'] applied to the natural bijection
   [free_ab_hom_iso], whose forward transpose is [fa_transpose], the
   forward transpose of [free_ab_adjunction] ([free_ab_transpose_is_adj]),
   and whose inverse transpose is the additive extension
   [free_ab_extend].  Its two naturality fields are
   [free_ab_naturality_in_set] and [free_ab_naturality_in_group], cited.
   Its counit is then the fold of the identity by conversion
   ([free_ab_hom_counit]), where the counit of [free_ab_adjunction] is
   that fold only up to `≈` ([free_ab_counit_evaluates]).
   Instance/Ab/FreeMonad.v builds Riehl's monad ℤ[−] on it.  No second
   free group and no second free functor: the action on arrows is still
   [FreeAb]'s, at `≈` the relabelling ([free_ab_fmap_generators]). 

   --------
   * ** 同样的伴随在同态集形式 (#472)[FreeAb ⊣ Ab_Forget] 的第二个封装，具有相同的左伴随 [FreeAb] 和相同的插入：Theory/Adjunction.v 的同态集合构造函数 [Build_Adjunction'] 应用于自然双射 [free_ab_hom_iso]，其前向转置为 [fa_transpose]，即 [free_ab_adjunction] ([free_ab_transpose_is_adj]) 的前向转置，其逆转置为加法扩展 [free_ab_extend]。它的两个自然性域为 [free_ab_naturality_in_set] 和 [free_ab_naturality_in_group]，已引用。其伴随余单元随后是通过转换 ([free_ab_hom_counit]) 对恒等映射的折叠，其中 [free_ab_adjunction] 的伴随余单元仅在 `≈` ([free_ab_counit_evaluates]) 上是该折叠。Instance/Ab/FreeMonad.v 在其上构建了 Riehl 的单子 ℤ [−]。没有第二个自由群和第二个自由函子：箭头上的作用仍是 [FreeAb] 的，在 `≈` 处重新标记 ([free_ab_fmap_generators])。
*)

(*
 The fold respects pointwise-`≈` maps on generators: a citation of
 [free_ab_extend_unique]. 

 --------
 该折叠尊重逐点的 `≈` 在生成元上的映射：引用 [free_ab_extend_unique]。
*)
Lemma fa_eval_pointwise@{c so +} {X : Sets@{c so}} {A : Ab}
      (h h' : X ~{Sets@{c so}}~> Ab_Forget A) (H : h ≈ h') (t : FATerm X) :
  fa_eval h t ≈ fa_eval h' t.
Proof.
  exact (free_ab_extend_unique A h' (free_ab_extend h) (fun x => H x) t).
Qed.

(* The natural bijection Ab(F X, A) ≅ Sets(X, U A): forward the restriction to the generators, backward the additive extension. / 自然双射 Ab(F X, A) ≅ Sets(X, U A)：正向为对生成元的限制，反向为加法扩展。 *)
Definition free_ab_hom_iso@{c so +} (X : Sets@{c so}) (A : Ab) :
  @Isomorphism Sets@{c so}
    {| carrier := @hom Ab (FreeAb X) A ; is_setoid := @homset Ab (FreeAb X) A |}
    {| carrier := @hom Sets@{c so} X (Ab_Forget A)
     ; is_setoid := @homset Sets@{c so} X (Ab_Forget A) |}.
Proof.
  unshelve refine
    (@Build_Isomorphism Sets
       {| carrier := @hom Ab (FreeAb X) A
        ; is_setoid := @homset Ab (FreeAb X) A |}
       {| carrier := @hom Sets X (Ab_Forget A)
        ; is_setoid := @homset Sets X (Ab_Forget A) |}
       (@Build_SetoidMorphism
          (@hom Ab (FreeAb X) A) (@homset Ab (FreeAb X) A)
          (@hom Sets X (Ab_Forget A)) (@homset Sets X (Ab_Forget A))
          (fun g => fa_transpose g) _)
       (@Build_SetoidMorphism
          (@hom Sets X (Ab_Forget A)) (@homset Sets X (Ab_Forget A))
          (@hom Ab (FreeAb X) A) (@homset Ab (FreeAb X) A)
          (fun h => free_ab_extend h) _) _ _).
  - intros g g' H x. exact (H (fa_gen x)).
  - intros h h' H t. exact (fa_eval_pointwise h h' H t).
  - intros h x. reflexivity.
  - intros g t. exact (fa_extend_transpose g t).
Defined.

(*
 The adjunction's last level, which no constraint mentions when it is
 left free, is pinned to the one of [Sets], as Instance/Mod/Free.v pins
 its own hom-set form. 

 --------
 当没有约束提到它被自由时，附加的最后一级被固定在[Sets]的一级上，就像Instance/Mod/Free.v固定它自己的同态集合形式一样。
*)
Definition free_ab_adjunction_hom@{c so +} :
  @Adjunction@{_ c c so c c c c so c so} Ab Sets@{c so} FreeAb Ab_Forget.
Proof.
  unshelve refine
    (@Build_Adjunction' Ab Sets FreeAb Ab_Forget free_ab_hom_iso _ _).
  - intros X Y A g u. exact (free_ab_naturality_in_set g u).
  - intros X A A' k g. exact (free_ab_naturality_in_group k g).
Defined.

(* Its counit is the fold of the identity, by conversion. / 它的余单位是通过转换得到的恒等映射的折叠。 *)
Example free_ab_hom_counit@{c so +} (A : Ab) (t : FATerm (Ab_Forget A)) :
  cmon_map (@counit _ _ _ _ free_ab_adjunction_hom A) t
    = fa_eval (@id Sets@{c so} (Ab_Forget A)) t := eq_refl.

(*
 Its unit and its forward transpose ARE those of [free_ab_adjunction].
 The cast pins the free level of that adjunction too, as the hom-set
 form's own is pinned above. 

 --------
 它的单位及其前向换位就是 [free_ab_adjunction] 的单位及其前向换位。铸造也固定了该附加的自由层，因为该同态集形式本身的自由层已被固定在上方。
*)
Example free_ab_hom_unit@{c so +} (X : Sets@{c so}) :
  @Category.Theory.Adjunction.unit _ _ _ _ free_ab_adjunction_hom X
    = @Category.Theory.Adjunction.unit _ _ _ _
        (free_ab_adjunction : @Adjunction@{_ c c so c c c c so c so} _ _ _ _)
        X
  := eq_refl.

Example free_ab_hom_to@{c so +} (X : Sets@{c so}) (A : Ab)
  (g : FreeAb X ~{Ab}~> A) :
  to (@adj _ _ _ _ free_ab_adjunction_hom X A) g
    = to (@adj _ _ _ _ (free_ab_adjunction
                          : @Adjunction@{_ c c so c c c c so c so} _ _ _ _)
            X A) g := eq_refl.


(*
   * ** Non-degeneracy

   A free construction is worthless if it collapses, and no induction
   over [fa_eq] can produce a negative -- every constructor concludes an
   equation.  So each refutation below maps OUT of the free group into a
   concrete abelian group and reads the answer off there, exactly as
   Instance/Grp/Free.v's [free_group_two_generators_nonabelian] does.

   The general statements are made over an ARBITRARY abelian group A
   with a distinguished element a that is not zero.  That is not
   generality for its own sake: it is what keeps them universe-free.
   Instantiating them at the integers instead -- writing the
   characteristic function with values 1 and 0 in ℤ -- pins the
   generating setoid's carrier AND relation universes to [Set], which
   was MEASURED by three probes rather than guessed: the same probe with
   ℤ but no decidable case split is free of [Set], and the same case
   split into an abstract A is free of [Set], while the two together
   pin.  So the concrete group is deferred to the two-generator witness
   at the end of the file, where [bool] forces [Set] anyway. 

   --------
   * ** 非退化性

   如果一个自由构造会塌缩，那么它是毫无价值的，并且在  [fa_eq]  上的任何归纳都无法产生负数 —— 每个构造子都得出一个方程。因此，下面的每个反驳都从自由群映射到一个具体的阿贝尔群，并从那里读取答案，就像  Instance/Grp/Free.v 的  [free_group_two_generators_nonabelian] 一样。这些一般性陈述是关于一个任意的阿贝尔群 A 的，并且该群有一个不为零的特殊元素 a。这并不是为了泛化而泛化：它使得这些陈述不依赖于宇宙。相反，如果将它们实例化到整数上——用在 ℤ 中取值为 1 和 0 的特征函数——会将生成的集合载体和关系宇宙固定到 [Set]，这个结果是通过三个探针测量得出的，而不是猜测的：相同的探针在 ℤ 上但没有可判定的情况分裂时，不依赖于 [Set]，而相同的情况分裂到抽象的 A 上时，不依赖于 [Set]，而两者结合时则固定。因此，具体的群被推迟到文件末尾的两生成元证明，在那里 [bool] 无论如何会强制 [Set]。
*)

Section NonDegeneracy.

Context (X : SetoidObject).
Context (A : AbObject).
Context (a : carrier (cmon_setoid A)).
Context (Ha : a ≈ cmon_zero A → False).

(*
   * *** Two separations that need no decider at all

   The constant map at [a] is a morphism of [Sets] with no hypothesis on
   X whatever, and it already refutes the two cheapest collapses. 

   --------
   * *** 两个完全不需要裁决者的分离

   在 [a] 上的常值映射是 [Sets] 的一个态射，对 X 没有任何假设，并且它已经驳斥了两个最廉价的塌缩。
*)

Definition fa_probe_const : X ~{Sets}~> Ab_Forget A.
Proof using X A a.
  unshelve refine {| morphism := fun _ => a |}.
  intros z z' _; reflexivity.
Defined.

(** A generator is not zero. / 一个生成元不为零。 *)
Theorem free_ab_gen_not_zero (x : carrier X) :
  fa_eq (@fa_gen X x) fa_zero → False.
Proof using X A a Ha.
  intro He.
  exact (Ha (fa_eval_respects A fa_probe_const _ _ He)).
Qed.

(*
   * The group is not idempotent: doubling a generator moves it.  This is
   where the group structure is spent -- [ab_cancel_l] (Instance/Ab.v)
   is what turns a + a ≈ a into a ≈ 0, and it is the one property that
   separates a group from a monoid. 

   --------
   * 该群不是幂等的：对生成元求两倍会移动它。这是群结构的消耗之处 —— [ab_cancel_l]（Instance/Ab.v）是将 a + a ≈ a 转化为 a ≈ 0 的关键，而它也是区分群与幺半群的唯一特性。
*)
Theorem free_ab_gen_not_idempotent (x : carrier X) :
  fa_eq (fa_plus (@fa_gen X x) (fa_gen x)) (fa_gen x) → False.
Proof using X A a Ha.
  intro He.
  pose proof (fa_eval_respects A fa_probe_const _ _ He) as Hv; simpl in Hv.
  apply Ha.
  apply (ab_cancel_l A a).
  transitivity a; [ exact Hv | ].
  symmetry; apply cmon_plus_zero_r.
Qed.

(*
   * *** Separations that need a decider on the generating setoid

   Distinguishing two DIFFERENT generators means exhibiting a group in
   which they go to different places, and the only such map a bare
   setoid supplies is the characteristic function of a point, which
   cannot be WRITTEN without a decision procedure for that setoid's
   [≈].  That is an ARGUMENT, not a theorem: no converse is proved here,
   and the tree's precedent for claims of exactly this shape
   ([arrow_mul_respects_forces_UIP] and its siblings) is deliberately
   not followed.

   Unlike Instance/Mod/Free.v's [free_module_basis_injective] this needs
   only ONE hypothesis rather than two.  That file's second hypothesis
   is 1 ≉ 0 in the coefficient ring, because it probes with the ring
   viewed as a module over itself and the ring may be the zero ring;
   here the nondegeneracy of the target is already carried by [Ha]. 

   --------
   * *** 需要在生成子集上有判定器的分离

   区分两个不同的生成元意味着展示一个群，使它们映射到不同的位置，而裸集合所提供的唯一这种映射是某一点的特征函数，而这个函数如果没有该集合的 [≈] 的判定程序，是不能被写出来的。这是一个论证，而不是定理：这里没有证明反命题，并且对于完全这种形式的论断（[arrow_mul_respects_forces_UIP] 及其兄弟命题），树的先例是刻意不遵循的。与 Instance/Mod/Free.v 的 [free_module_basis_injective] 不同，这里只需要一个假设而不是两个。那个文件的第二个假设是在系数环中 1 ≉ 0，因为它以环作为自身的模来探测，而环可能是零环；这里目标的非退化性已经由 [Ha] 承担。
*)

Context (Xdec : ∀ x y : carrier X, (x ≈ y) + ((x ≈ y) → False)).

(* The characteristic function of the generator [x]. / 生成器 [x] 的特征函数。 *)
Definition fa_probe_at (x : carrier X) : X ~{Sets}~> Ab_Forget A.
Proof using X A a Xdec.
  unshelve refine {|
    morphism := fun z => match Xdec x z with
                         | inl _ => a
                         | inr _ => cmon_zero A
                         end
  |}.
  intros z z' Hz; simpl.
  destruct (Xdec x z) as [Hxz|Hxz], (Xdec x z') as [Hxz'|Hxz'].
  - reflexivity.
  - destruct (Hxz' (transitivity Hxz Hz)).
  - destruct (Hxz (transitivity Hxz' (symmetry Hz))).
  - reflexivity.
Defined.

(** Distinct generators give distinct elements. / 不同的生成元产生不同的元素。 *)
Theorem free_ab_gen_injective (x y : carrier X) :
  fa_eq (@fa_gen X x) (fa_gen y) → x ≈ y.
Proof using X A a Ha Xdec.
  intro He.
  destruct (Xdec x y) as [Hxy|Hxy]; [ exact Hxy | ].
  destruct Ha.
  pose proof (fa_eval_respects A (fa_probe_at x) _ _ He) as Hv.
  simpl in Hv.
  destruct (Xdec x x) as [_|Hxx]; [ | destruct (Hxx (reflexivity x)) ].
  destruct (Xdec x y) as [Hc|_]; [ destruct (Hxy Hc) | ].
  exact Hv.
Qed.

(*
   * A COMPOUND element is separated from a generator: e_x + e_y is not
   e_x when x ≉ y.  Neither theorem above gives this -- both are about
   generators alone -- so it is the sharpest of the four. 

   --------
   * 当一个复合元素与生成元分开时：当 x ≉ y 时，e_x + e_y 不是 e_x。上述两个定理都没有给出这个——它们都是关于生成元本身的——所以它是四个中最严谨的。
*)
Theorem free_ab_sum_not_summand (x y : carrier X)
  (Hxy : (x ≈ y) → False) :
  fa_eq (fa_plus (@fa_gen X x) (fa_gen y)) (fa_gen x) → False.
Proof using X A a Ha Xdec.
  intro He.
  pose proof (fa_eval_respects A (fa_probe_at y) _ _ He) as Hv.
  simpl in Hv.
  destruct (Xdec y x) as [Hc|_]; [ destruct (Hxy (symmetry Hc)) | ].
  destruct (Xdec y y) as [_|Hyy]; [ | destruct (Hyy (reflexivity y)) ].
  apply Ha.
  rewrite <- Hv.
  symmetry; apply cmon_plus_zero_l.
Qed.

End NonDegeneracy.

Arguments fa_probe_const {X} A a.
Arguments fa_probe_at {X} A a Xdec x.
Arguments free_ab_gen_not_zero {X} A a Ha x _.
Arguments free_ab_gen_not_idempotent {X} A a Ha x _.
Arguments free_ab_gen_injective {X} A a Ha Xdec x y _.
Arguments free_ab_sum_not_summand {X} A a Ha Xdec x y Hxy _.

(*
   * ** A computing witness on two generators

   The integers, as [ring_ab Int_Ring]: Instance/Rng.v's [ring_ab]
   applied to Theory/Algebra/Rig.v's [Int_Ring].  This is the same
   term Instance/Ab/Coproduct.v names [ab_Z]; that file is NOT
   required here (it would drag the biproduct closure in for one
   definition), so no in-file identification with that name is stated.

   The generating setoid has TWO elements, so the free group is not ℤ
   itself and the additive extension has something to do. 

   --------
   * ** 关于两个生成元的计算见证

   整数，如 [ring_ab Int_Ring]：Instance/Rng.v 的 [ring_ab]，应用于 Theory/Algebra/Rig.v 的 [Int_Ring]。这与 Instance/Ab/Coproduct.v 中命名为 [ab_Z] 的项相同；该文件在这里不是必需的（它会因为一个定义而引入二元积闭包），因此这里没有在文件中用该名称进行标识。

   生成的集合等价类有两个元素，所以自由群不是 ℤ 本身，并且加性扩展与此有关。
*)

Definition ab_int : AbObject := ring_ab Int_Ring.

Lemma ab_int_one_not_zero : (1%Z : carrier (cmon_setoid ab_int))
  ≈ cmon_zero ab_int → False.
Proof. intro H; compute in H; discriminate H. Qed.

Definition AbTwoGens : SetoidObject := {|
  carrier   := bool;
  is_setoid := {| equiv := eq; setoid_equiv := eq_equivalence |}
|}.

Definition ab_two_gens_dec :
  ∀ x y : carrier AbTwoGens, (x ≈ y) + ((x ≈ y) → False).
Proof.
  intros x y; simpl.
  destruct x, y.
  - exact (inl eq_refl).
  - right; intro H; discriminate.
  - right; intro H; discriminate.
  - exact (inl eq_refl).
Defined.

(*
 [FATerm]'s index argument is implicit, and in a statement with no
 expected type -- an [fa_eq] between two constructor applications --
 the elaborator has nothing to propagate it from.  These are
 NOTATIONS, not definitions, so each unfolds to the constructor itself
 and nothing below is stated about a different term. 

 --------
 [FATerm] 的索引参数是隐式的，并且在没有期望类型的语句中 —— 两个构造函数应用之间的 [fa_eq] —— 推导器没有来源来传播它。这些是符号表示，而不是定义，所以每个都展开为构造函数本身，并且下面没有说明关于其他项的内容。
*)
Local Notation zgen  := (@fa_gen AbTwoGens).
Local Notation zplus := (@fa_plus AbTwoGens).
Local Notation zneg  := (@fa_neg AbTwoGens).

(* Two integers, read off the two generators. / 两个整数，从两个生成器中读出。 *)
Definition ab_int_probe : AbTwoGens ~{Sets}~> Ab_Forget ab_int.
Proof.
  unshelve refine {|
    morphism := fun b : carrier AbTwoGens => if b then 3%Z else 5%Z
  |}.
  (*
 [all:] because the respectfulness field of a map out of a setoid
 whose ≈ is Leibniz [=] may be discharged by instance resolution
 before a goal is ever opened; the carriers here are at [Set] either
 way, so nothing is pinned that was not already. 

 --------
 [all:] 因为从一个集合类的映射的尊重性域，其 ≈ 是莱布尼茨 [=]，可以在目标被打开之前通过实例解析来处理；这里的承载体在 [Set] 无论哪种方式，因此没有固定任何原本未固定的东西。
*)
  all: intros x y H; simpl in H; subst y; reflexivity.
Defined.

(*
 The additive extension computes: e_true + e_true + (−e_false)
 ↦ 3 + 3 − 5 = 1. 

 --------
 加法扩展计算：e_true + e_true + (−e_false) ↦ 3 + 3 − 5 = 1。
*)
Example int_free_ab_extend_computes :
  fa_eval ab_int_probe
    (zplus (zplus (zgen true) (zgen true)) (zneg (zgen false)))
    = 1%Z := eq_refl.

Example int_free_ab_extend_generator_true :
  fa_eval ab_int_probe (zgen true) = 3%Z := eq_refl.

Example int_free_ab_extend_zero :
  fa_eval ab_int_probe (@fa_zero AbTwoGens) = 0%Z := eq_refl.

(*
   * The four separations, instantiated at ℤ with the element 1 and at the
   decidable two-element setoid. 

   --------
   * 四个分离，在 ℤ 中由元素 1 实例化，并在可判定的两元素集合类上实例化。
*)

Theorem int_free_ab_gen_not_zero :
  fa_eq (zgen true) (@fa_zero AbTwoGens) → False.
Proof.
  exact (@free_ab_gen_not_zero AbTwoGens ab_int 1%Z
           ab_int_one_not_zero true).
Qed.

Theorem int_free_ab_gen_not_idempotent :
  fa_eq (zplus (zgen true) (zgen true)) (zgen true) → False.
Proof.
  exact (@free_ab_gen_not_idempotent AbTwoGens ab_int 1%Z
           ab_int_one_not_zero true).
Qed.

Theorem int_free_ab_gens_distinct : fa_eq (zgen true) (zgen false) → False.
Proof.
  intro He.
  pose proof (@free_ab_gen_injective AbTwoGens ab_int 1%Z
                ab_int_one_not_zero ab_two_gens_dec true false He) as Hb.
  compute in Hb; discriminate Hb.
Qed.

Theorem int_free_ab_sum_not_summand :
  fa_eq (zplus (zgen true) (zgen false)) (zgen true) → False.
Proof.
  refine (@free_ab_sum_not_summand AbTwoGens ab_int 1%Z
            ab_int_one_not_zero ab_two_gens_dec true false _).
  intro H; discriminate H.
Qed.

(*
   * ** Measured negatives

   Each [Fail] below records a strengthening that the file does NOT
   have, and each is paired with a positive control that must succeed,
   so a rename or a change of definition breaks the file loudly instead
   of turning the [Fail] vacuously green.  The house convention puts
   such probes in a Test/Probe*.v file; they are in-file here because
   this commit adds exactly one file, and moving them costs nothing. 

   --------
   * ** 测量负样本

   每个下面的 [Fail] 都记录了文件中不存在的增强，并且每个都与必须成功的阳性对照配对，因此重命名或更改定义会明显破坏文件，而不是使 [Fail] 虚假地显示为绿色。内部约定将此类探针放在 Test/Probe*.v 文件中；它们在此文件内是因为此提交正好添加了一个文件，移动它们不费任何力气。
*)

(*
 CONVERSION.  The counit does not compute.  It is
 [unique_obj (ump_universal_arrows …)] and [ump_universal_arrows]
 (Theory/Universal/Arrow.v) is [Qed]-opaque, so nothing reduces
 through it; only the [≈] statement [free_ab_counit_generator] holds.
 Control: the UNIT at the same generator DOES compute.
 CORRECTION (#472): one of two causes; with [ump_universal_arrows]
 alone turned [Defined] this negative is still refused, and with this
 file's [free_ab_universal] turned [Defined] as well its statement
 holds at [eq_refl] (the header's STRENGTHS); the counit of the hom-set
 form [free_ab_adjunction_hom] is the fold at [eq_refl]
 ([free_ab_hom_counit]). 

 --------
 转换。余单位无法计算。它是
 [unique_obj (ump_universal_arrows …)] 和 [ump_universal_arrows] 
 （Theory/Universal/Arrow.v）是 [Qed] -opaque，所以没有任何东西可以通过它进行归约；只有 [≈] 声明 [free_ab_counit_generator] 成立。
 控制：同一生成元处的 UNIT 可以计算。
 校正（#472）：两种原因之一；仅将 [ump_universal_arrows] 打开为 [Defined] 时，该否定仍被拒绝，并且将此文件的 [free_ab_universal] 也打开为 [Defined] 后，其声明在 [eq_refl] （标题的 STRENGTHS）成立；同态集形式的余单位 [free_ab_adjunction_hom] 是 [eq_refl] 处的折叠（[free_ab_hom_counit]）。
*)
Fail Example counit_does_not_compute (A : Ab) (b : carrier (Ab_Forget A)) :
  cmon_map (free_ab_counit A) (fa_gen b) = b := eq_refl.

Example ab_control_unit_computes (X : Sets) (x : carrier X) :
  free_ab_unit X x = @fa_gen X x := eq_refl.

(*
 CONVERSION.  The free functor's action on a generator does not
 compute either, for the same reason -- [fmap] of
 [LeftAdjointFunctorFromUniversalArrows] is defined by universal
 factorization, not by a formula.  Only the [≈] statement
 [free_ab_fmap_generators] holds.  Control: the object action DOES
 compute.  CORRECTION (#472): the same two causes; with both turned
 [Defined] this statement holds at [eq_refl] too (the header's
 STRENGTHS). 

 --------
 转换。自由函子在生成元上的作用也无法计算，原因相同 —— [fmap] 的 [LeftAdjointFunctorFromUniversalArrows] 是通过普遍因式分解定义的，而不是通过公式定义的。只有 [≈] 的 [free_ab_fmap_generators] 声明成立。控制：对象作用可以计算。更正（#472）：相同的两个原因；当两者都被打开时，ZW4WZZ 该声明在 [eq_refl] 也成立（标题的强度）。
*)
Fail Example fmap_generator_does_not_compute
  (X Y : Sets) (u : X ~{Sets}~> Y) (x : carrier X) :
  cmon_map (fmap[FreeAb] u) (fa_gen x) = fa_gen (u x) := eq_refl.

Example control_fobj_computes (X : Sets) : FreeAb X = FreeAbObject X
  := eq_refl.

(*
 CONVERSION.  Even when the generating setoid is the target's own
 carrier, the free group is not CONVERTIBLE with that group:
 [FreeAbObject] is an inductive of formal expressions, so nothing
 identifies its record with ℤ's.  This says nothing about
 ISOMORPHISM -- no such claim is made anywhere in this file, in either
 direction.  Control: the generators of the two-element witness really
 are inhabitants of the free group's carrier. 

 --------
 转换。即使生成的集合正是目标自身的承载，自由群也不能与该群互换：[FreeAbObject] 是形式表达式的归纳类型，因此没有任何东西将其记录与 ℤ 的记录对应。这与同构无关——在本文件的任何地方都没有提出这样的主张，无论哪个方向。控制：两个元素的见证的生成元确实是自由群承载的成员。
*)
Fail Example free_on_carrier_is_not_the_group :
  FreeAbObject (Ab_Forget ab_int) = ab_int := eq_refl.

Example control_generators_typecheck :
  carrier (Ab_Forget (FreeAbObject AbTwoGens))
  := (zgen true : FATerm AbTwoGens).

(* Instrument check: [Fail] does fire on a genuine conversion failure of the same kind as the three negatives above, so their green is not the harness reporting success on nothing. / 仪器检查：[Fail] 确实会在与上面三个否定相同类型的真实转换失败时触发，因此它们的绿色不是接线束在无事发生时报告成功。 *)
Fail Example instrument_check : (0%Z = 1%Z) := eq_refl.
