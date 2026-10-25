(* * * Dualization into a fixed object, and self-adjointness on the right / * * 对固定对象的对偶化，以及右侧的自伴性 *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.StarAutonomous.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.Right.

(*
 The hom-set isomorphisms of the closed structure and of
 [AdjointOnTheRight] both live in [Sets], so [Instance/Sets] is in
 scope; this removal keeps its product-monoidal instance out of the
 hint database so that `⨂` cannot resolve to the tensor of [Sets].
 Structure/Monoidal/Closed.v and Structure/Monoidal/StarAutonomous.v
 perform the same removal.  Here it is DEFENSIVE, and that is measured
 rather than assumed: deleting the line leaves this file compiling
 clean (rc = 0).  The reason it costs nothing is that `C` arrives with
 a [SymMonClosed] instance whose coercion [smc_is_symmetric] already
 determines the monoidal structure, so resolution is never offered a
 choice.  It is kept for consistency with the two donors, where the
 ambient category is not so constrained. 

 --------
 闭结构和 [AdjointOnTheRight] 的同态集同构都存在于 [Sets] 中，所以 [Instance/Sets] 在作用域内；这种删除会将其乘积单态实例排除在提示数据库之外，从而使 `⨂` 无法解析为 [Sets] 的张量。Structure/Monoidal/Closed.v 和 Structure/Monoidal/StarAutonomous.v 执行相同的删除。在这里它是防御性的，这是被测量的，而不是假定的：删除这一行后，本文件可以干净编译（rc = 0）。之所以不产生任何代价，是因为 `C` 随着一个 [SymMonClosed] 实例到来，其强制转换 [smc_is_symmetric] 已经确定了单态结构，因此解析永远不会被提供选择。它被保留以与两个捐赠者保持一致，在那些场景中，所处的范畴并没有如此受限。
*)
Remove Hints Sets_Product_Monoidal : typeclass_instances.

(*
 NOTATION GUARD, inherited from Adjunction/Right.v and obeyed
 here, but DEFENSIVE in this file — and that is measured on both
 halves, not assumed.  Three scopes declare [_ ^op] (category, functor
 and adjunction), and Category.Functor.Opposite and
 Category.Adjunction.Right's transitive imports open theirs, so a bare
 [C^op] can parse as the wrong one; Right.v records a site where the
 guard is genuinely REQUIRED.  Here it is not: deleting the [Open
 Scope] leaves this file compiling clean (rc = 0), and so does
 replacing every [Opposite_Functor (dual d)] by [(dual d)^op].  Both
 are nevertheless kept — the [Open Scope] because the hazard is real in
 general, the [Opposite_Functor] spelling because it is the discipline
 the donor asks consumers to follow.  Same family as the guards in
 Theory/Universal/Arrow/Dual.v and Instance/Rng/Mod.v. 

 --------
 符号守护，从 Adjunction/Right.v 继承并在此遵守，但在此文件中是防御性的——并且这是在两个半部分上测量的，而不是假设的。三个作用域声明了 [_ ^op]（类别、函子和伴随），且 Category.Functor.Opposite 和 Category.Adjunction.Right 的传递导入会打开它们的作用域，所以一个单独的 [C^op] 可能会被解析为错误的那个；Right.v 记录了确实需要该守护的地方。在这里不需要：删除 [Open Scope] 后该文件仍能干净编译（rc = 0），并且将每个 [Opposite_Functor (dual d)] 替换为 [(dual d)^op] 也同样可以。尽管如此，两者仍然保留——[Open Scope] 因为这种风险在一般情况下是真实存在的，[Opposite_Functor] 拼写因为这是捐赠者要求使用者遵循的规范。与 Theory/Universal/Arrow/Dual.v 和 Instance/Rng/Mod.v 中的守护属于同一家族。
*)
Open Scope category_scope.

Generalizable All Variables.

(*
 Book:  Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 §IV.2 Construction 3, printed p. 88 (maclane:IV.2:construction3)
 Book:  Mac Lane, op. cit., §IV.2 Definition 2, printed p. 89, where
 "adjoint on the right" is defined and attributed to Freyd
 Book:  Riehl, "Category Theory in Context", §4.4
 nLab:  https://ncatlab.org/nlab/show/star-autonomous+category
 nLab:  https://ncatlab.org/nlab/show/dualizing+object
 nLab:  https://ncatlab.org/nlab/show/mutually+left+adjoint+functors

 WHAT THIS FILE IS.  Fix an object `d` of a symmetric monoidal closed
 category `C`.  Mac Lane's §IV.2 Construction 3 observes that
 dualization into `d`,

 (- ⇒ d) : C^op ⟶ C,

 is ADJOINT TO ITSELF ON THE RIGHT: there is a bijection

 C(a, x ⇒ d)  ≅  C(x, a ⇒ d),

 natural in both variables, because both sides are the transposes of
 maps out of the tensor — one of `a ⨂ x`, the other of `x ⨂ a` — and
 the symmetry of `⨂` exchanges the two.  Everything sits on the RIGHT
 of the two hom-sets, which is the sense of Mac Lane's Definition 2 and
 of the class [AdjointOnTheRight] (Adjunction/Right.v).  The
 canonical unit of the resulting self-adjunction is the map into the
 double dual,

 η_x : x ~> (x ⇒ d) ⇒ d,

 the transpose of `eval'` through the symmetric braid.  It is what this
 file CONSTRUCTS, and it is exactly the map that
 Structure/Monoidal/StarAutonomous.v's field [star_double_dual]
 declines to pin: that class POSITS some isomorphism `x ≅ (x⇒d)⇒d`
 without requiring it to be the canonical one, and that file's own
 header records the gap in those terms.  The relationship is
 made explicit below rather than left implicit.

 THE TYPE-LEVEL FIT.  [AdjointOnTheRight {A X} (S : A^op ⟶ X)
 (T : X^op ⟶ A)] is instantiated at A := C, X := C and
 S := T := [dual d].  Both are `C^op ⟶ C`, so the class typechecks with
 no transport, and its field [aor {a x}] unfolds to precisely
 `C(a, dual d x) ≅ C(x, dual d a)`, which is Mac Lane's bijection.  The
 Adjunction/Right.v's own NOT-DELIVERED list records that it builds
 "No self-adjoint-on-the-right PREDICATE"; none is introduced here
 either — this file supplies an INSTANCE at a coinciding pair, not a
 predicate saying when one exists.

 PRIOR ART, MEASURED — AND THIS IS NOT THE CLASS'S FIRST SELF-ADJOINT
 WITNESS, WHICH AN EARLIER DRAFT OF THIS HEADER CLAIMED.  Before this
 file [AdjointOnTheRight] occurred in exactly two files tree-wide —
 Adjunction/Right.v, which declares it, and Test/ProbeRight358.v, its
 probe — and Right.v already carries THREE inhabitants:
 [Id_AdjointOnTheRight] (labelled DEGENERATE there, both functors
 being identities), [Chain3_AdjointOnTheRight] (a Galois pair on
 a three-element chain, whose partner functors differ) and
 [Powerset_AdjointOnTheRight].  The last of these is ALREADY at
 a coinciding pair — [Powerset_Prop_op] occupies both slots — so
 nothing here is the first witness with S = T, and no such claim is
 made.  What is new is the first witness arising from a MONOIDAL
 CLOSED structure rather than from a fixed concrete category, and the
 first identification of the resulting unit and counit with a
 canonical map: Right.v handles unit and counit generically
 ([aor_counit_transform] and siblings) but the words
 `double dual` occur nowhere in it, and it identifies no witness's
 unit with anything.  The identifiers [dd_unit], [double_dual_unit],
 [dual_self_adjoint_on_the_right], [dual_transpose] and [dual_uncur]
 each occurred ZERO times, and a sweep of all fifty names this file
 declares returns zero collisions tree-wide.  Two near-collisions were
 found by that sweep and are recorded rather than risked: [dual_ev] is
 TAKEN by Instance/FdVect/DoubleDual.v (a different construction,
 the evaluation map of a finite-dimensional double dual), so the
 helper here is [dual_uncur]; and [double_dual_natural] is taken, 9
 occurrences across Instance/FdVect/DoubleDual.v and
 Instance/FdVect/NonNatural.v, so the naturality lemma here is
 [dd_unit_natural].  Neither of those files is in this one's closure,
 but `make print-assumptions` loads many modules into ONE scope, where
 a shared name would silently audit the wrong constant.

 THE DONOR DEVIATION IS LOAD-BEARING, AND IT DICTATES THE WHOLE FILE.
 StarAutonomous.v's header records that [ump_exponents'] is
 stated in ∃!-form and is NOT wired to `curry' := to exp_iso`, so the
 beta law for the PACKAGED `curry'` is not derivable from the class
 fields.  Every transposition below therefore goes through the UMP
 WITNESS [dcur] (StarAutonomous.v), whose beta law [dcur_beta]
 and uniqueness [dcur_uniq] come straight from the field.
 `curry'` and `uncurry'` are not used anywhere in this file.  A second
 donor fact costs a re-declaration: [dcur_respects]
 (StarAutonomous.v) is `#[local]`, so it does not survive that
 file; [dcur_Proper] below restates it (three lines, from [dcur_uniq]
 and [dcur_beta]) because `rewrite` under [dcur] is otherwise
 unavailable.

 THE FACTORING.  Everything is routed through one helper,

 dual_uncur f := eval' ∘ (f ⨂ id) ,

 which is inverse to [dcur] by the UMP ([dual_uncur_dcur],
 [dcur_dual_uncur]).  The transposition is then literally "uncurry,
 braid, re-curry",

 dual_transpose f := dcur (dual_uncur f ∘ braid) ,

 and each of the round trip and the two naturality laws is one line of
 [dual_uncur]-algebra closed by [dcur_uniq].  Spelling the same map
 directly as `dcur (eval' ∘ braid ∘ (id ⨂ f))` would put the two-sided
 tensor action inside every rewrite instead of behind one abbreviation;
 the factoring is recorded here so a later reader does not undo it.
 No claim is made that the direct spelling fails — it was not built.

 WHAT IS DELIVERED.

 - [dual_self_adjoint_on_the_right] : an inhabitant of
 [AdjointOnTheRight (dual d) (dual d)] for an arbitrary object `d`
 of an arbitrary [SymMonClosed] category.  No field failed and no
 field was weakened; all four naturality laws are instances of the
 two lemmas [dual_transpose_nat_dom] and [dual_transpose_nat_cod],
 and the two isomorphism laws are both [dual_transpose_invol].
 - [dd_unit] : the CANONICAL map `x ~> double_dual d x`, CONSTRUCTED
 (`dual_transpose id`) and NOT assumed invertible, together with
 [dd_unit_natural] and the packaged
 [double_dual_unit : Id[C] ⟹ double_dual d].
 - [dual_adjunction] : the ordinary adjunction `(dual d)^op ⊣ dual d`
 between `C^op` and `C`, read off the class by
 [Adjunction_of_AdjointOnTheRight] (Adjunction/Right.v) rather
 than rebuilt.
 - The identification of that adjunction's UNIT and COUNIT with
 [dd_unit], and of both transposes at the identity with it.
 - [StarAutonomous_of_dd_unit] and [dual_AdjointEquivalence] : if the
 canonical map is invertible then the star-autonomous class is
 inhabited with [star_double_dual] LITERALLY [dd_unit], and the
 self-adjunction upgrades to an [AdjointEquivalence].

 STRENGTHS, MEASURED STRICT-FIRST.  These hold at `eq_refl`, and are
 shipped as `Example`s so that a later edit cannot silently weaken
 them:

 - `unit dual_adjunction x = dd_unit x`     ([unit_is_dd_unit])
 - `counit dual_adjunction x = dd_unit x`   ([counit_is_dd_unit])

 The second is Mac Lane's remark that for a self-adjunction on the
 right the counit IS the unit read in the opposite category, and it
 is not a coincidence of packaging: `to aor` and `from aor` are the
 SAME function [dual_transpose] at swapped indices, which
 [aor_to_is_from_swapped] records, again at `eq_refl` and on the
 WHOLE `SetoidMorphism`, not merely pointwise.

 - `to aor id = dd_unit x` and `from aor id = dd_unit x`
 ([dd_unit_is_to_at_id], [dd_unit_is_from_at_id])
 - `fobj[double_dual d] x = (x ⇒ d) ⇒ d` and
 `fmap[double_dual d] f = fmap[dual d] (fmap[dual d] f)`
 - `dualizer (StarAutonomous_of_dd_unit H) = d` and
 `to (star_double_dual …) = dd_unit x`
 ([star_double_dual_is_dd_unit]) — note this is the FORWARD LEG,
 the field being an [Isomorphism] and so not a morphism itself —
 the sharp form of the claim that
 invertibility of the canonical map is EXACTLY the standing
 assumption of StarAutonomous.v's third field.

 EXACTLY ONE identification falls back to `≈`, and the residue is
 exhibited rather than described.  StarAutonomous.v's header calls the
 canonical map "the transpose of `eval'` through the symmetric braid",
 i.e. `dcur (eval' ∘ braid)`; [dd_unit] is `dual_transpose id`, which
 unfolds to `dcur (eval' ∘ (id ⨂ id) ∘ braid)`.  The two differ by the
 insertion of `id ⨂ id`, and `bimap` is `fmap[tensor]` whose
 [fmap_id] is an opaque law field, so conversion does not remove it.
 [dd_unit_is_braid_transpose] states the `≈` form; the `eq_refl` form
 is REFUTED and pinned below as CONVERSION negative 1, against a
 control that closes at `eq_refl` once the residue is written out.  The
 direction of the fallback was a design choice made on a measurement,
 not on taste: spelling [dd_unit] the other way round would move the
 `≈` onto the unit/counit identifications, which are the ones Mac
 Lane's construction is actually about.

 WHAT IS NOT DELIVERED.

 - No concrete witness category.  Nothing here exhibits a
 [SymMonClosed] instance, so every result is a conditional; the
 library's [ClosedMonoidal] is cartesian and is excluded on the
 no-go grounds StarAutonomous.v's header states.  This is inherited
 from the donor, which likewise constructs no instance.
 - No CONVERSE to [StarAutonomous_of_dd_unit].  From an arbitrary
 [StarAutonomous] one cannot recover invertibility of the canonical
 map, because the class does not tie [star_double_dual] to it.
 CONVERSION negative 2 pins the sharpest available fact — that
 conversion alone does not establish
 `to (star_double_dual) = dd_unit dualizer x` for an arbitrary
 instance — against the produced instance as a passing control.
 Read that at its strength: it says conversion does not settle the
 equation, NOT that the equation is false.  No countermodel is
 exhibited, and none is claimed to exist.
 - No [EquivalenceOfCategories] record and no
 [AdjointEquivalence_to_Equivalence] composite; the upgrade stops
 at [AdjointEquivalence] (Theory/Equivalence/Adjoint.v), which
 is the class whose two extra fields are exactly invertibility of
 the derived unit and counit.
 - No self-adjointness on the LEFT, and nothing about
 [AdjointOnTheLeft]; Adjunction/Right.v's
 [right_does_not_imply_left] applies but is not instantiated here.
 - No uniqueness: nothing says the dual functor is the only functor
 self-adjoint on the right, and no analogue of [right_adjoint_iso].
 - No functoriality or naturality in `d`: [dual], [dd_unit] and the
 self-adjunction are not exhibited as varying with the dualizing
 object.
 - No triangle identities in the vocabulary of
 Adjunction/Natural/Transformation.v; the unit and counit are
 identified with [dd_unit] but the zig-zags are not restated.
 - Nothing about `⅋`, linear distributivity, or Barr coherence; that
 is StarAutonomous.v's ledger entry 4 and is untouched.
 - [StarAutonomous.v] is NOT modified.

 UNIVERSES, MEASURED off BOTH the binder and the constraint block —
 the block alone would give the wrong answer here, which is the point.
 Every constant in this file has hom IDENTIFIED with proof, expressed
 by REUSING the level variable in the BINDER rather than by any
 equation: 94 of the 100 `Category` binder occurrences print
 `C : Category@{u u0 u0}`, and the other six — the three `_ex`
 exported instances, twice each — print `C : Category@{u u2 u2}`, the
 same SHAPE under different level names.  The constraint blocks
 contain NO equation at all, only bounds; the enumeration that follows
 is NOT exhaustive, being the ones worth naming: `u0 < u1` from
 [SymMonClosed], further strict bounds (`u0 < u3`, `u0 < u4`,
 `u2 < u0`) and `≤`-bounds both against [compose], [projections],
 [prod_rect] and [ID] and between this file's own declared levels.
 A reader who checks only the block concludes "no identification" and
 is wrong.  The identification is INHERITED, and FOUR donors are each
 sufficient ON THEIR OWN: under a section declaring `Constraint
 ch < cp`, each of [Opposite], [Monoidal], [SymmetricMonoidal] and
 [SymMonClosed] is rejected ALONE at `Category@{co ch cp}` with a
 genuine `universe inconsistency: Cannot enforce cp = ch`, while
 naming a hom `a ~{Cu}~> b` and an identity `@id Cu a` at those very
 levels is ACCEPTED — and all four are ACCEPTED once the two levels
 are declared equal, so each negative fires on the constraint and not
 on the application.  READ "four" AS FOUR DONORS AND NOT AS FOUR
 INDEPENDENT CAUSES: [SymMonClosed] contains [SymmetricMonoidal]
 (field [smc_is_symmetric]) contains [BraidedMonoidal] (field
 [symmetric_is_braided]) contains [Monoidal] (field
 [braided_is_monoidal]), so three of the four are ONE cause tested at
 three strengths and at most TWO are independent — [Opposite] and the
 monoidal chain, whose weakest member [Monoidal] already suffices.
 Nothing here adds to the identification, and none of the four is
 claimed unavoidable: no re-annotated variant of any donor was
 attempted.  There is no `Set` in any binder or any block.  The four
 rejections are shipped as FORMABILITY negatives below.

 AXIOMS AND COUNT.  50/50 constants closed under the global context.
 The 50 are the 42 source-declared names plus the EIGHT [Program]
 obligations no source sweep sees — six for
 [dual_self_adjoint_on_the_right] and two for [double_dual_unit].  The
 figure is `Print Module` on the compiled module, whitespace-flattened
 before counting (the printer wraps, and a line-anchored sweep silently
 drops a wrapped entry); every one of the 50 was then queried by
 fully-qualified name.  `Print Module` renders the [Qed] constants as
 `Parameter`, which is a display convention and not an axiom.  The file
 declares no [Record], [Class] or [Inductive], so there is no unlisted
 `Build_*`. 

 --------
 书籍: Mac Lane，《为工作的数学家准备的范畴》，第2版，§IV.2 构造3，第88页 (maclane:IV.2:construction3)
 书籍: Mac Lane，上述著作，§IV.2 定义2，第89页，其中“右伴随”被定义并归功于Freyd
 书籍: Riehl，《情境中的范畴论》，§4.4
 nLab: https://ncatlab.org/nlab/show/star-autonomous+category
 nLab: https://ncatlab.org/nlab/show/dualizing+object
 nLab: https://ncatlab.org/nlab/show/mutually+left+adjoint+functors

 本文件内容。 固定一个对称单闭范畴 `C` 的对象 `d`。 Mac Lane 的 §IV.2 构造3 观察到，映射到 `d` 的对偶化，

 (- ⇒ d) : C^op ⟶ C,

 在右侧与自身伴随：存在一个双射

 C(a, x ⇒ d)  ≅  C(x, a ⇒ d)在两个变量中都是自然的，因为两边都是张量映射的转置——一个是 `a ⨂ x` 的映射，另一个是 `x ⨂ a` 的映射——而 `⨂` 的对称性交换了这两个映射。所有内容都位于两个同态集合的右侧，这正是 Mac Lane 定义 2 和类 [AdjointOnTheRight]（Adjunction/Right.v）的含义。由此自伴的典范幺元是映射到双对偶的映射，

 η_x : x ~> (x ⇒ d) ⇒ d,通过对称编织对 `eval'` 的转置。这就是该文件构建的内容，并且它正是 Structure/Monoidal/StarAutonomous.v 文件中的字段 [star_double_dual] 不愿明确指出的映射：该类提出了一些同构 `x ≅ (x⇒d)⇒d`，而不要求它是标准的那个，而该文件自己的标题也以这些术语记录了这一差距。这种关系在下面被明确表示，而不是默认留空。类型级适配。[AdjointOnTheRight {A X} (S : A^op ⟶ X) (T : X^op ⟶ A)] 在 A := C, X := C 并且 S := T := [dual d] 时被实例化。两者都是 `C^op ⟶ C`，所以该类在无需传输的情况下类型检查，其字段 [aor {a x}] 精确展开为 `C(a, dual d x) ≅ C(x, dual d a)`，即 Mac Lane 的双射。Adjunction/Right.v 自身的未完成列表记录它构建了“没有右自伴的谓词”；此处也没有引入——这个文件在一个重合的对上提供了一个实例，而不是提供一个说明何时存在的谓词。先前技术，已测量——而且这并不是该类的第一个自伴随证据，一个早期版本的标题还声称了这一点。在此文件之前，[AdjointOnTheRight]恰好出现在整个文件树的两个文件中——Adjunction/Right.v（声明它的文件）以及Test/ProbeRight358.v（其探针文件）——而Right.v中已经有三个实例：[Id_AdjointOnTheRight]（标记为退化，两个函子都是恒等函子）、[Chain3_AdjointOnTheRight]（在一个三元素链上的伽罗瓦对，其配对函子不同）以及[Powerset_AdjointOnTheRight]。最后一个已经在一个重合对中——[Powerset_Prop_op]占据了两个位置——所以这里没有任何东西是 S = T 的第一个证据，并且也没有提出这样的主张。新颖之处在于，第一个证据是源自一种单体闭结构（MONOIDAL CLOSED structure），而不是来自一个固定的具体范畴，并且首次将由此产生的单位（unit）和余单位（counit）与一个典范映射（canonical map）进行识别：Right.v 泛化地处理单位和余单位（[aor_counit_transform] 及其相关），但 `double dual` 这个词在其中完全没有出现，并且它没有将任何证据的单位与任何东西进行识别。标识符 [dd_unit]、[double_dual_unit]、[dual_self_adjoint_on_the_right]、[dual_transpose] 和 [dual_uncur] 每个都出现了零次，并且对本文件声明的所有五十个名称进行的检查显示在整个树中没有冲突。通过该扫描发现了两次接近碰撞，并记录下来而不是冒险：[dual_ev] 被 Instance/FdVect/DoubleDual.v 使用（一个不同的构造，一个有限维双重对偶的评估映射），因此这里的辅助是 [dual_uncur]；而 [double_dual_natural] 已被使用，在 Instance/FdVect/DoubleDual.v 和 Instance/FdVect/NonNatural.v 中共有 9 个出现，因此这里的自然性引理是 [dd_unit_natural]。这些文件都不在此文件的闭包中，但 `make print-assumptions` 将许多模块加载到 ONE 作用域中，在此作用域下，共享名称会悄然地审核错误的常量。捐赠者偏差是承重的，它决定了整个文件。
 StarAutonomous.v 的头部记录表明 [ump_exponents'] 以 ∃!-形式声明，并且没有连接到 `curry' := to exp_iso`，因此打包的 `curry'` 的 beta 定律无法从类字段中推导出来。因此，下面的每个置换都通过 UMP 证人 [dcur]（StarAutonomous.v），其 beta 定律 [dcur_beta] 和唯一性 [dcur_uniq] 直接来自字段。
 `curry'` 和 `uncurry'` 在该文件中未使用。第二个捐赠者事实需要重新声明：[dcur_respects]（StarAutonomous.v）是 `# [local]ZZ `，因此它不会在该文件中保留；下面的 [dcur_Proper] 重新声明它（三行，从 [dcur_uniq] 和 [dcur_beta]），因为在 [dcur] 下的 `rewrite` 否则无法获取。分解。一切都通过一个辅助函数进行处理，

 dual_uncur f := eval' ∘ (f ⨂ id) ，

 根据 UMP ([dual_uncur_dcur], [dcur_dual_uncur])，它是 [dcur] 的逆函数。然后转置就是字面上的“取消柯里化、编织、再柯里化”，

 dual_transpose f := dcur (dual_uncur f ∘ braid) ，

 而往返及两个自然性法则中的每一个都是一行 [dual_uncur] -代数，由 [dcur_uniq] 封闭。直接将相同的映射拼写为 `dcur (eval' ∘ braid ∘ (id ⨂ f))` 会将双边张量作用放在每个重写中，而不是放在一个缩写后面；这里记录了分解，以便后来的读者不会撤销它。并不声称直接拼写会失败——只是没有构建它。

 所交付的内容。- [dual_self_adjoint_on_the_right]：任意对象 `d` 在 [AdjointOnTheRight (dual d) (dual d)] 中的一个元素，属于任意 [SymMonClosed] 类别。没有字段失败，也没有字段被削弱；所有四条自然性定律都是 [dual_transpose_nat_dom] 和 [dual_transpose_nat_cod] 两个引理的实例，并且两个同构定律都是 [dual_transpose_invol]。 - [dd_unit]：标准映射 `x ~> double_dual d x`，已构造（`dual_transpose id`）但未假定可逆，与 [dd_unit_natural] 以及打包的 [double_dual_unit : Id[C] ⟹ double_dual d。 - [dual_adjunction]：普通伴随 `(dual d)^op ⊣ dual d`，在 `C^op` 和 `C` 之间，通过 [Adjunction_of_AdjointOnTheRight] (Adjunction/Right.v) 读取类，而不是重新构建。- 将该伴随的 UNIT 和 COUNIT 与 [dd_unit] 进行等同，并将两个转置在恒等映射下等同于它。- [StarAutonomous_of_dd_unit] 和 [dual_AdjointEquivalence]：如果规范映射是可逆的，那么星自伴类包含 [star_double_dual] 字面意思是 [dd_unit]，并且自伴随升级为 [AdjointEquivalence]。

 优点，以严格优先的顺序衡量。这些在 `eq_refl` 上成立，并作为 `Example` 发送，以便后续编辑不能悄悄地削弱它们：

 - `unit dual_adjunction x = dd_unit x` ([unit_is_dd_unit])
 - `counit dual_adjunction x = dd_unit x` ([counit_is_dd_unit])

 第二条是 Mac Lane 的评论，即对于右侧的自伴随，余单元就是在对立范畴中读取的单元，这并不是巧合的包装：`to aor` 和 `from aor` 是相同的函数 [dual_transpose]，只是索引交换，[aor_to_is_from_swapped] 记录了它，同样在 `eq_refl` 上并适用于整个 `SetoidMorphism`，而不仅仅是逐点的。-  `to aor id = dd_unit x` 和 `from aor id = dd_unit x` 
 （[dd_unit_is_to_at_id]，[dd_unit_is_from_at_id]）
 -  `fobj [double_dual d]ZZ  x = (x ⇒ d) ⇒ d` 和
 `fmap [double_dual d]ZZ  f = fmap [dual d]ZZ  (fmap [dual d]ZZ  f)`
 -  `dualizer (StarAutonomous_of_dd_unit H) = d` 和
 `to (star_double_dual …) = dd_unit x`
 （[star_double_dual_is_dd_unit]）——注意这是前向分支，
 该字段是一个 [Isomorphism]，因此本身不是一个态射——
 对该命题的明确形式陈述是，典范映射的可逆性正是 StarAutonomous.v 的第三个字段的固定假设。恰好有一个识别退回到 `≈`，并且残基是展示而不是描述的。StarAutonomous.v 的头部将规范映射称为“通过对称编织的 `eval'` 的转置”，即 `dcur (eval' ∘ braid)`；[dd_unit] 是 `dual_transpose id`，其展开为 `dcur (eval' ∘ (id ⨂ id) ∘ braid)`。两者不同之处在于插入了 `id ⨂ id`，并且 `bimap` 是 `fmap [tensor]ZZ `，其 [fmap_id] 是一个不透明的法则字段，因此转换并不会移除它。[dd_unit_is_braid_transpose] 陈述了 `≈` 形式；`eq_refl` 形式被反驳并在下面标记为 CONVERSION -1，相对于在残基写出之后于 `eq_refl` 闭合的控制。回退的方向是基于测量而不是基于喜好的设计选择：将 [dd_unit] 反向拼写会将 `≈` 移到单元/计数标识上，而这些正是 Mac Lane 的构造实际关注的内容。

 没有交付的内容。- 没有具体的见证类别。这里没有任何东西展示 [SymMonClosed] 实例，因此每个结果都是条件性的；库中的 [ClosedMonoidal] 是笛卡尔的，并且由于 StarAutonomous.v 的头文件所述的不可行原因而被排除。这是从捐赠者继承而来，捐赠者同样不构造任何实例。 - 没有 [StarAutonomous_of_dd_unit] 的逆命题。对于任意 [StarAutonomous]，无法恢复规范映射的可逆性，因为该类并未将 [star_double_dual] 与其关联。CONVERSION 负 2 将可用的最尖锐事实 — 转换本身并不能为任意实例确立 `to (star_double_dual) = dd_unit dualizer x` — 针对生成的实例作为一个通过控制。以其强度来理解：它说转换不能解决方程，而不是说方程是错误的。没有展示反例，也没有声称存在反例。- 没有 [EquivalenceOfCategories] 记录，也没有 [AdjointEquivalence_to_Equivalence] 复合；升级在 [AdjointEquivalence] (Theory/Equivalence/Adjoint.v) 停止，该类的两个额外字段正是导出单位和余单位的可逆性。- 在左边没有自伴性，也没有关于 [AdjointOnTheLeft] 的内容；Adjunction/Right.v 的 [right_does_not_imply_left] 适用，但在此未实例化。- 没有唯一性：没有任何内容说明对偶函子是右自伴函子唯一的函子，也没有类似 [right_adjoint_iso] 的内容。- 在 `d` 中没有函子性或自然性：[dual]、[dd_unit] 及自伴并未展示为随对偶对象变化。- 在 Adjunction/Natural/Transformation.v 的词汇中没有三角恒等式；单位和余单位被识别为 [dd_unit]，但之字形没有重新说明。 - 关于 `⅋`、线性分配性或 Barr 相干性没有任何内容；这是 StarAutonomous.v 的账目条目 4，未被触及。 - [StarAutonomous.v] 没有被修改。宇宙，同时从绑定器和约束块上测量 —— 仅使用块在这里会给出错误的答案，这正是重点。这个文件中的每一个常量都已经通过证明识别出 hom，通过在绑定器中重用层级变量来表达，而不是通过任何方程：100 次 `Category` 绑定器出现中的 94 次打印 `C : Category@{u u0 u0}`，其余六次 —— 三个 `_ex` 导出实例，每个打印两次 —— 打印 `C : Category@{u u2 u2}`，在不同的层级名称下形成相同的形状。约束块根本不包含任何方程，只有界限；随后列举的内容并不是详尽无遗的，仅包括值得命名的：从 [SymMonClosed] 的 `u0 < u1`，进一步的严格界限（`u0 < u3`、`u0 < u4`、`u2 < u0`）以及 `≤` 界限，对 [compose]、[projections]、[prod_rect] 和 [ID] 以及该文件自身声明的级别之间均有约束。仅检查该块的读者会得出“未识别”的结论，这是错误的。该识别是继承的，并且四个供体各自单独就足够：在声明 “约束 ch < cp” 的部分下，[Opposite]、[Monoidal]、[SymmetricMonoidal] 和 [SymMonClosed] 中的每一个在 `Category@{co ch cp}` 上单独被拒绝，具有真实的 `universe inconsistency: Cannot enforce cp = ch`，同时在这些级别上命名一个同质 `a ~{Cu}~> b` 和一个身份 `@id Cu a` 是被接受的——并且一旦声明这两个级别相等，所有四个都是被接受的，因此每个否定作用于约束本身，而不是应用。将“四”读作四个供体，而不是四个独立原因：[SymMonClosed] 包含 [SymmetricMonoidal]（字段 [smc_is_symmetric]）包含 [BraidedMonoidal]（字段 [symmetric_is_braided]）包含 [Monoidal]（字段 [braided_is_monoidal]），因此其中三者是同一个原因，在三种强度下进行测试，至多有两个是独立的——[Opposite] 和单值链，其最弱成员 [Monoidal] 已经足够。这里没有任何内容可以增加识别，并且没有四者中任何一个被声称是不可避免的：未尝试重新标注任何供体的变体。在任何绑定器或任何区块中都没有 `Set`。这四个拒绝被作为可形成性负面结果如下发送。公理与计数。50/50 常量在全局上下文下封闭。
 这 50 个是 42 个源声明的名称，加上八个 [Program] 的义务，源扫描看不到——[dual_self_adjoint_on_the_right] 有六个，[double_dual_unit] 有两个。
 这个数字是 `Print Module` 在已编译模块上的值，计数前已平滑空白（打印机会换行，而锚行扫描器会悄悄丢弃换行的条目）；这 50 个中的每一个随后都按全限定名称查询。`Print Module` 将 [Qed] 常量呈现为 `Parameter`，这是显示约定，而不是公理。该文件没有声明 [Record]、[Class] 或 [Inductive]，因此没有未列出的 `Build_*`。
*)

Section DualSelfAdjoint.

Context {C : Category}.
Context `{@SymMonClosed C}.
Context (d : C).

(*
   * ** Transposition helpers

   [dcur_respects] in the donor is `#[local]` and does not survive that
   file, so it is restated; [dual_uncur] is the inverse of [dcur] on the
   nose, and everything below is stated in terms of it. 

   --------
   * ** 转位辅助工具

   供体中的 [dcur_respects] 是 `# [local]ZZ `，并且不能在该文件中保留，所以它被重新说明；[dual_uncur] 是 [dcur] 在鼻子上的逆，以下所有内容都是以它为基础说明的。
*)

#[local] Instance dcur_Proper {x y z : C} :
  Proper (equiv ==> equiv) (@dcur C _ x y z).
Proof.
  intros f g Hfg; apply dcur_uniq; rewrite Hfg; apply dcur_beta.
Qed.

Definition dual_uncur {a x : C} (f : a ~> x ⇒ d) : a ⨂ x ~> d :=
  eval' ∘ (f ⨂ id).

#[local] Instance dual_uncur_Proper {a x : C} :
  Proper (equiv ==> equiv) (@dual_uncur a x).
Proof. intros f g Hfg; unfold dual_uncur; now rewrite Hfg. Qed.

Lemma dual_uncur_dcur {a x : C} (g : a ⨂ x ~> d) :
  dual_uncur (dcur g) ≈ g.
Proof. symmetry; apply dcur_beta. Qed.

Lemma dcur_dual_uncur {a x : C} (f : a ~> x ⇒ d) :
  dcur (dual_uncur f) ≈ f.
Proof. apply dcur_uniq; reflexivity. Qed.

(*
 The dual functor's arrow action IS the transpose of the one-sided
 evaluation, by CONVERSION: [dual] is a [Program Definition] whose
 `fmap` field is that term.  This is the lemma that lets the rewrites
 below fire; a bare `rewrite <- dcur_beta` will not fire through
 `fmap[dual d]` without it. 

 --------
 双函子的箭头作用通过转换就是单边求值的转置：[dual] 是一个 [Program Definition]，其 `fmap` 字段就是该项。这是使下面重写能够生效的引理；没有它，单独的 `rewrite <- dcur_beta` 不会通过 `fmap [dual d]ZZ ` 生效。
*)
Lemma dual_fmap_unfold {x x' : C} (k : x ~{C}~> x') :
  @fmap _ _ (dual d) x' x k ≈ dcur (eval' ∘ (id ⨂ k)).
Proof. reflexivity. Qed.

Lemma dual_uncur_comp {a a' x : C} (f : a ~> x ⇒ d) (g : a' ~> a) :
  dual_uncur (f ∘ g) ≈ dual_uncur f ∘ (g ⨂ id[x]).
Proof.
  unfold dual_uncur.
  rewrite bimap_comp_id_right; now rewrite comp_assoc.
Qed.

Lemma dual_uncur_dual {a x x' : C} (f : a ~> x' ⇒ d) (k : x ~{C}~> x') :
  dual_uncur (@fmap _ _ (dual d) x' x k ∘ f)
    ≈ dual_uncur f ∘ (id[a] ⨂ k).
Proof.
  unfold dual_uncur.
  transitivity (eval' ∘ (f ⨂ k)).
  - rewrite dual_fmap_unfold, bimap_comp_id_right, comp_assoc.
    rewrite <- (dcur_beta (eval' ∘ (id[x' ⇒ d] ⨂ k))).
    rewrite <- comp_assoc.
    now rewrite bimap_id_left_right.
  - rewrite <- comp_assoc. now rewrite bimap_id_right_left.
Qed.

(*
   * ** The self-transposition

   Mac Lane's bijection `C(a, x ⇒ d) ≅ C(x, a ⇒ d)`: uncurry, cross the
   two factors with the symmetric braid, re-curry.  The SAME function
   serves as both directions of the bijection, at swapped indices. 

   --------
   * ** 自我置换

   Mac Lane 的双射 `C(a, x ⇒ d) ≅ C(x, a ⇒ d)`：取消柯里化，用对称编织交换两个因子，然后重新柯里化。相同的函数在交换索引时同时作为双射的两个方向。
*)

Definition dual_transpose {a x : C} (f : a ~> x ⇒ d) : x ~> a ⇒ d :=
  dcur (dual_uncur f ∘ braid).

#[local] Instance dual_transpose_Proper {a x : C} :
  Proper (equiv ==> equiv) (@dual_transpose a x).
Proof. intros f g Hfg; unfold dual_transpose; now rewrite Hfg. Qed.

Lemma dual_uncur_transpose {a x : C} (f : a ~> x ⇒ d) :
  dual_uncur (dual_transpose f) ≈ dual_uncur f ∘ braid.
Proof. unfold dual_transpose; apply dual_uncur_dcur. Qed.

(*
 The round trip.  This is the single place where SYMMETRY of the
 braiding — [braid_invol], Structure/Monoidal/Symmetric.v — is
 spent; the two naturality laws below need only [bimap_braid], which
 holds over a bare [BraidedMonoidal] structure. 

 --------
 往返行程。这是唯一一个使用编织对称性的地方——[braid_invol]，Structure/Monoidal/Symmetric.v——下列两个自然性定律只需要[bimap_braid]，它在一个最基本的[BraidedMonoidal]结构上成立。
*)
Theorem dual_transpose_invol {a x : C} (f : a ~> x ⇒ d) :
  dual_transpose (dual_transpose f) ≈ f.
Proof.
  unfold dual_transpose at 1.
  rewrite dual_uncur_transpose, <- comp_assoc, braid_invol, id_right.
  apply dcur_dual_uncur.
Qed.

Theorem dual_transpose_nat_dom {a a' x : C}
  (f : a ~> x ⇒ d) (g : a' ~> a) :
  dual_transpose (f ∘ g)
    ≈ @fmap _ _ (dual d) a a' g ∘ dual_transpose f.
Proof.
  apply dcur_uniq.
  transitivity
    (dual_uncur (@fmap _ _ (dual d) a a' g ∘ dual_transpose f));
    [| unfold dual_uncur; reflexivity ].
  rewrite dual_uncur_dual, dual_uncur_transpose, dual_uncur_comp,
          <- !comp_assoc.
  now rewrite bimap_braid.
Qed.

Theorem dual_transpose_nat_cod {a x x' : C}
  (f : a ~> x' ⇒ d) (k : x ~{C}~> x') :
  dual_transpose (@fmap _ _ (dual d) x' x k ∘ f)
    ≈ dual_transpose f ∘ k.
Proof.
  apply dcur_uniq.
  transitivity (dual_uncur (dual_transpose f ∘ k));
    [| unfold dual_uncur; reflexivity ].
  rewrite dual_uncur_comp, dual_uncur_transpose, dual_uncur_dual,
          <- !comp_assoc.
  now rewrite bimap_braid.
Qed.

(*
   * ** Mac Lane §IV.2 Construction 3

   The dual functor is adjoint to itself on the right.  Both legs of the
   hom-set isomorphism are ONE construction at swapped indices; the two
   isomorphism laws are both [dual_transpose_invol], and the four
   naturality fields are the two lemmas above, each used twice. 

   --------
   * ** Mac Lane §IV.2 构造 3

   对偶函子在右侧与自身是伴随的。Hom 集同构的两个分支是在交换指标下的单一构造；两个同构定律都是 [dual_transpose_invol]，四个自然性字段是上面的两个引理，每个使用两次。
*)

Definition dual_transpose_morphism (a x : C) :
  SetoidMorphism {| carrier   := @hom C a (dual d x)
                  ; is_setoid := @homset C a (dual d x) |}
                 {| carrier   := @hom C x (dual d a)
                  ; is_setoid := @homset C x (dual d a) |} :=
  {| morphism       := @dual_transpose a x
   ; proper_morphism := @dual_transpose_Proper a x |}.

Program Definition dual_self_adjoint_on_the_right :
  @AdjointOnTheRight C C (dual d) (dual d) := {|
  aor := fun a x => {| to   := dual_transpose_morphism a x
                     ; from := dual_transpose_morphism x a |}
|}.
Next Obligation. simpl; apply dual_transpose_invol. Qed.
Next Obligation. simpl; apply dual_transpose_invol. Qed.
Next Obligation. apply dual_transpose_nat_dom. Qed.
Next Obligation. apply dual_transpose_nat_cod. Qed.
Next Obligation. apply dual_transpose_nat_cod. Qed.
Next Obligation. apply dual_transpose_nat_dom. Qed.

Notation "'DSA'" := dual_self_adjoint_on_the_right (only parsing).

(*
 The two legs are the same construction at swapped indices, at
 whole-[SetoidMorphism] Leibniz equality — this is the precise content
 of Mac Lane's remark that the pair is symmetric in S and T. 

 --------
 这两条腿在调换的索引处具有相同的构造，关于整体 [SetoidMorphism] Leibniz 等式——这正是 Mac Lane 所说的该对在 S 和 T 中是对称的精确内容。
*)
Example aor_to_is_from_swapped (a x : C) :
  to (@aor C C (dual d) (dual d) DSA a x)
    = from (@aor C C (dual d) (dual d) DSA x a) := eq_refl.

Example aor_from_is_to_swapped (a x : C) :
  from (@aor C C (dual d) (dual d) DSA a x)
    = to (@aor C C (dual d) (dual d) DSA x a) := eq_refl.

(*
   * ** The canonical map into the double dual

   CONSTRUCTED, not assumed invertible.  It is the value of the
   self-transposition at the identity of `x ⇒ d`; equivalently, and up
   to the `id ⨂ id` residue measured in the header, the transpose of
   `eval'` through the braid. 

   --------
   * ** 进入双对偶的典范映射

   是构造的，而非假设可逆。它是自转置在  `x ⇒ d`  的恒等映射处的值；等价地，并且在头部测量的  `id ⨂ id`  残差意义下，  `eval'`  通过编织的转置。
*)

Definition dd_unit (x : C) : x ~> double_dual d x :=
  dual_transpose (@id C (x ⇒ d)).

Example double_dual_obj (x : C) :
  fobj[double_dual d] x = ((x ⇒ d) ⇒ d) := eq_refl.

Example double_dual_fmap {a b : C} (f : a ~{C}~> b) :
  @fmap _ _ (double_dual d) a b f
    = @fmap _ _ (dual d) (a ⇒ d) (b ⇒ d) (@fmap _ _ (dual d) b a f)
  := eq_refl.

Example dd_unit_is_to_at_id (x : C) :
  to (@aor C C (dual d) (dual d) DSA (x ⇒ d) x) (@id C (x ⇒ d))
    = dd_unit x := eq_refl.

Example dd_unit_is_from_at_id (x : C) :
  from (@aor C C (dual d) (dual d) DSA x (x ⇒ d)) (@id C (x ⇒ d))
    = dd_unit x := eq_refl.

(*
 The header's spelling, at `≈`.  The residue is exactly `id ⨂ id`;
 [bimap] is `fmap[tensor]` and [fmap_id] is an opaque law field, so
 conversion does not remove it.  The `eq_refl` form is refuted and
 pinned as CONVERSION negative 1 below. 

 --------
 标题的拼写是 `≈`。残留物正好是 `id ⨂ id`；[bimap] 是 `fmap [tensor]ZZ `，[fmap_id] 是一个不透明的法律字段，因此转换不会移除它。`eq_refl` 形式被反驳，并被标注为转换负 1 以下。
*)
Lemma dd_unit_is_braid_transpose (x : C) :
  dd_unit x ≈ dcur (eval' ∘ braid).
Proof.
  unfold dd_unit, dual_transpose, dual_uncur.
  apply dcur_Proper.
  rewrite bimap_id_id, id_right.
  reflexivity.
Qed.

Theorem dd_unit_natural {a b : C} (f : a ~{C}~> b) :
  @fmap _ _ (double_dual d) a b f ∘ dd_unit a ≈ dd_unit b ∘ f.
Proof.
  unfold dd_unit.
  transitivity (dual_transpose (@fmap _ _ (dual d) b a f)).
  - rewrite <- (id_left (@fmap _ _ (dual d) b a f)) at 1.
    rewrite dual_transpose_nat_dom. reflexivity.
  - rewrite <- (id_right (@fmap _ _ (dual d) b a f)) at 1.
    rewrite dual_transpose_nat_cod. reflexivity.
Qed.

Program Definition double_dual_unit : Id[C] ⟹ double_dual d := {|
  transform := dd_unit
|}.
Next Obligation. apply dd_unit_natural. Qed.
Next Obligation. symmetry; apply dd_unit_natural. Qed.

Example double_dual_unit_component (x : C) :
  transform[double_dual_unit] x = dd_unit x := eq_refl.

(*
   * ** The ordinary adjunction, and Mac Lane's unit and counit

   Read off the class by Adjunction/Right.v rather than rebuilt.
   `Check` displays the result as `(dual d)^op ⊣ dual d`. 

   --------
   * ** 普通的伴随，以及 Mac Lane 的单位和余单位

   从 Adjunction/Right.v 中直接读取类，而不是重建。
   `Check` 显示结果为 `(dual d)^op ⊣ dual d` 。
*)

Definition dual_adjunction :
  @Adjunction (C^op) C (Opposite_Functor (dual d)) (dual d) :=
  Adjunction_of_AdjointOnTheRight DSA.

(*
 Both at `eq_refl`.  The second is Mac Lane's observation that the
 counit of a self-adjunction on the right is the unit read in the
 opposite category: the two are the SAME TERM, not merely `≈`-equal
 morphisms, and not merely equal componentwise after a transport. 

 --------
 两者都在 `eq_refl` 。第二个是 Mac Lane 的观察，即右自伴的余单位是在对立范畴中读作单位：两者是相同的项，而不仅仅是 `≈` -相等的态射，也不仅仅是在经过传输后按分量相等。
*)
Example unit_is_dd_unit (x : C) :
  @unit (C^op) C (Opposite_Functor (dual d)) (dual d) dual_adjunction x
    = dd_unit x := eq_refl.

Example counit_is_dd_unit (x : C) :
  @counit (C^op) C (Opposite_Functor (dual d)) (dual d) dual_adjunction x
    = dd_unit x := eq_refl.

(*
   * ** Relationship to the star-autonomous class

   StarAutonomous.v's [star_double_dual] POSITS an isomorphism
   `x ≅ double_dual d x` without requiring it to be the canonical map.
   The two results below say precisely what invertibility of the
   canonical map buys: the class is inhabited with [star_double_dual]
   LITERALLY [dd_unit], and the self-adjunction upgrades to an adjoint
   equivalence.  The converse is not available and is not claimed — see
   the header's NOT DELIVERED list and CONVERSION negative 2. 

   --------
   * ** 与星自自治类的关系

   StarAutonomous.v 的 [star_double_dual] 假设存在一个同构
   `x ≅ double_dual d x`，而不要求它是典范映射。
   下面的两个结果准确地说明了典范映射可逆性所带来的好处：该类包含 [star_double_dual] LITERALLY [dd_unit]，并且自伴随提升为伴随等价。相反情况不可用，也未被声明——参见标题中的“未交付”列表及 CONVERSION negative 2。
*)

Definition StarAutonomous_of_dd_unit
  (Hiso : forall x : C, IsIsomorphism (dd_unit x)) : @StarAutonomous C _.
Proof.
  refine (@Build_StarAutonomous C _ d
            (fun x y => @exp_iso C _ x y d)
            (fun x => IsIsoToIso (dd_unit x) (Hiso x)) _).
  intros a b f. simpl. symmetry. apply dd_unit_natural.
Defined.

Example star_autonomous_dualizer
  (Hiso : forall x : C, IsIsomorphism (dd_unit x)) :
  @dualizer C _ (StarAutonomous_of_dd_unit Hiso) = d := eq_refl.

Example star_double_dual_is_dd_unit
  (Hiso : forall x : C, IsIsomorphism (dd_unit x)) (x : C) :
  to (@star_double_dual C _ (StarAutonomous_of_dd_unit Hiso) x)
    = dd_unit x := eq_refl.

(*
 The upgrade.  [AdjointEquivalence] (Theory/Equivalence/Adjoint.v)
 carries an adjunction together with invertibility of its derived unit
 and counit; both are [dd_unit] here, so ONE hypothesis discharges both
 fields.  The counit field is stated in `C^op`, where the two inverse
 laws are the C-level ones with left and right exchanged — hence the
 explicit [@Build_IsIsomorphism (C^op)], a record literal `{| … |}`
 resolving to `C` instead. 

 --------
 升级。[AdjointEquivalence]（理论/等价/伴随.v）携带了一个伴随以及其派生单位和余单位的可逆性；这里两者都是[dd_unit]，因此一个假设就解决了两个字段。余单位字段在`C^op`中说明，其中两个逆律是C级的，左右互换——因此显式的[@Build_IsIsomorphism (C^op)]，一个记录字面量`{| … |}`，解析为`C`。
*)
Definition dual_AdjointEquivalence
  (Hiso : forall x : C, IsIsomorphism (dd_unit x)) :
  @AdjointEquivalence C (C^op) (Opposite_Functor (dual d)) (dual d).
Proof.
  unshelve econstructor.
  - exact dual_adjunction.
  - intro x; exact (Hiso x).
  - intro y.
    exact (@Build_IsIsomorphism (C^op) _ _ _
             (@two_sided_inverse C _ _ (dd_unit y) (Hiso y))
             (@is_left_inverse   C _ _ (dd_unit y) (Hiso y))
             (@is_right_inverse  C _ _ (dd_unit y) (Hiso y))).
Defined.

End DualSelfAdjoint.

(*
   * ** Respectfulness, exported

   The instances above are `#[local]` section hints and die at [End];
   a downstream consumer wanting to `rewrite` under [dcur],
   [dual_uncur] or [dual_transpose] needs them in the global database.
   Same shape as the donor's own `#[local] dcur_respects`, restated. 

   --------
   * ** 尊重，已导出

   上述实例是 `# [local]ZZ ` 部分提示，并在 [End] 结束；
   下游使用者希望在 [dcur] 下 `rewrite`，
   [dual_uncur] 或 [dual_transpose] 需要它们在全局数据库中。
   与捐赠者自身的 `# [local]ZZ  dcur_respects` 形状相同，重述。
*)

#[export] Instance dcur_Proper_ex {C : Category} `{@SymMonClosed C}
  {x y z : C} : Proper (equiv ==> equiv) (@dcur C _ x y z).
Proof.
  intros f g Hfg; apply dcur_uniq; rewrite Hfg; apply dcur_beta.
Qed.

#[export] Instance dual_uncur_Proper_ex {C : Category}
  `{@SymMonClosed C} {d a x : C} :
  Proper (equiv ==> equiv) (@dual_uncur C _ d a x).
Proof. intros f g Hfg; unfold dual_uncur; now rewrite Hfg. Qed.

#[export] Instance dual_transpose_Proper_ex {C : Category}
  `{@SymMonClosed C} {d a x : C} :
  Proper (equiv ==> equiv) (@dual_transpose C _ d a x).
Proof. intros f g Hfg; unfold dual_transpose; now rewrite Hfg. Qed.

(*
   * ** Probe section

   Every rejection the header reports, pinned.  The KINDS are kept
   lexically apart and labelled: FORMABILITY (universe), CONVERSION,
   TYPING.  Each negative was stripped of its [Fail] and run alone, and
   its failure kind read off the WHOLE error message.  The three kinds
   are genuinely distinguishable here, and reading only the tail would
   NOT distinguish two of them: the four FORMABILITY negatives close
   with `universe inconsistency: Cannot enforce cp = ch`; the two
   CONVERSION negatives close with `cannot unify` between two terms of
   ONE type, naming those terms (`dd_unit d x` against
   `dcur (eval' ∘ braid)`, and `to star_double_dual` against
   `dd_unit dualizer x`); the TYPING negative also closes with
   `cannot unify`, but on the OBJECT VARIABLES `x` and `a`, its body
   reporting two DIFFERENT objects of [Sets] as the expected and actual
   types — the two legs of the bijection do not share a type off the
   diagonal, so no term equation between them is statable at all.
   Every control is APPLIED: an unapplied polymorphic constant never
   meets the declared levels and would guard nothing.

   RENAME SIMULATION, 4/4 here and 3/3 in the probe.  Renaming a
   constant only inside a [Fail] would leave the guard vacuously green,
   so each of this file's own constants that a negative or a control
   actually REFERENCES was renamed AT ITS DEFINITION SITE ALONE and the
   file recompiled.  The denominator is FOUR, not the count of names
   appearing anywhere in the probe section: [dd_unit],
   [dual_self_adjoint_on_the_right] (through the `DSA` notation),
   [dd_unit_is_braid_transpose] and [StarAutonomous_of_dd_unit].  All
   four broke at a line that is NOT a [Fail], none went vacuous.  The
   control [Example]s' own declaration names and the [Fail Example]
   names are NOT in the denominator: nothing ever uses them, so renaming
   one cannot break anything and the test would be vacuous by
   construction.  Test/ProbeDual359.v scores 3/3 on the same method from
   OUTSIDE this file.  The definition-site
   method is what makes this test say anything — a whole-file rename is
   a no-op by construction, since the definition is renamed in lockstep
   with its uses, and reports a FALSE "vacuous guard" verdict for every
   constant.  The four DONOR names the formability negatives mention
   ([Opposite], [Monoidal], [SymmetricMonoidal], [SymMonClosed]) cannot
   be renamed from here; they are guarded instead by the applied control
   section immediately below, which names all four outside any
   [Fail]. 

   --------
   * ** 探针部分每一个头文件报告的拒绝，都已固定。种类在词汇上分开并标注：可形成性（宇宙）、转换、类型。每一个负面结果都被去掉了其 [Fail] 并单独运行，然后从整体错误信息中读取其失败类型。这里的三种类型确实可以区分，仅读取尾部是无法区分其中两个的：四个 FORMABILITY 否定在 `universe inconsistency: Cannot enforce cp = ch` 处闭合；两个 CONVERSION 否定在 `cannot unify` 处闭合，在相同类型的两个项之间，命名这些项（`dd_unit d x` 对 `dcur (eval' ∘ braid)`，和 `to star_double_dual` 对 `dd_unit dualizer x`）；TYPING 否定也在 `cannot unify` 处闭合，但作用在对象变量 `x` 和 `a` 上，其主体报告了两个不同的 [Sets] 对象作为期望类型和实际类型——双射的两条腿在对角线之外不共享类型，因此根本无法对它们之间的项建立方程。每个控制都被应用了：未应用的多态常量从未达到声明的层级，也无法保护任何内容。重命名模拟，4/4 在这里，探针中为 3/3。仅在 [Fail] 内重命名常量会使保护守则空置为绿色，因此该文件中每个被负值或控制实际引用的常量仅在其定义处被重命名，并重新编译了文件。分母是四，而不是探针部分中出现的名称总数：[dd_unit]、[dual_self_adjoint_on_the_right]（通过 `DSA` 标记）、[dd_unit_is_braid_transpose] 和 [StarAutonomous_of_dd_unit]。四个都在非 [Fail] 的那一行出错，没有任何一个变为空置。控制 [Example] 的自身声明名称和 [Fail Example] 名称不计入分母：没有任何内容使用它们，因此重命名其中的任何一个都不会破坏任何东西，并且测试将按照构造为空置。Test/ProbeDual359.v 在这个文件之外对同一种方法的评分是 3/3。定义位置的方法是让这个测试有任何输出的原因——整个文件的重命名在结构上是无操作的，因为定义会与其使用同步重命名，并且对于每个常量都会报告一个错误的“空保护”判断。四个 DONOR 名字在可形成性负面中提到（[Opposite]、[Monoidal]、[SymmetricMonoidal]、[SymMonClosed]）不能从这里重命名；它们被紧接在下面的应用控制段保护，该段在任何 [Fail] 之外命名了所有四个名字。
*)

(*
 Instrument check: a [Fail] that succeeds prints NOTHING under this
 repository's [coqc], so a probe file with a broken instrument would
 look green.  This one must fail for a reason having nothing to do
 with the subject matter. 

 --------
 仪器检查：一个成功的 [Fail] 在本仓库的 [coqc] 下不会打印任何内容，因此一个带有损坏仪器的探针文件看起来会是绿色的。这个必须因为与主题无关的原因失败。
*)
Fail Example dual_probe_instrument : (true = false) := eq_refl.

Section DualProbeFormabilityControl.

(*
 Positive half of the formability measurement: with the hom and proof
 universes declared EQUAL, all four donors elaborate at the very same
 applied arguments the negatives below reject.  So each negative fires
 on the CONSTRAINT and not on the application. 

 --------
 可塑性测量的正面部分：当同类和证明宇宙被声明为相等时，所有四个给体在完全相同的应用参数下展开，而下面的消极部分被拒绝。因此，每个消极部分作用于约束，而不是应用。
*)

Universes cco cch.
Context (Cv : Category@{cco cch cch}).
Context (u v : Cv).

Check (u ~{Cv}~> v).
Check (@id Cv u).
Check (@Opposite Cv).
Check (@Monoidal Cv).
Check (@SymmetricMonoidal Cv).
Check (@SymMonClosed Cv).

End DualProbeFormabilityControl.

Section DualProbeFormability.

(*
 FORMABILITY.  The hom/proof identification carried by every constant
 in this file is INHERITED.  Each of the four donors below is rejected
 ALONE at levels where naming a hom and an identity is accepted, and
 the control section above shows each ACCEPTED once the two levels are
 declared equal.  These are four DONORS, not four independent causes:
 negatives 2-4 are nested classes ([SymMonClosed] contains
 [SymmetricMonoidal] contains [BraidedMonoidal] contains [Monoidal]),
 so they test one cause at three strengths; only [Opposite] is
 independent of that chain. 

 --------
 可成型性。本文件中每个常量携带的同构/证明标识是继承的。下面的四个供体在接受命名同构和同一性的级别上单独被拒绝，而上面的控制部分显示，一旦声明两个级别相等，它们每个都被接受一次。这是四个供体，而不是四个独立的原因：负面2-4是嵌套类（[SymMonClosed]包含[SymmetricMonoidal]，[SymmetricMonoidal]包含[BraidedMonoidal]，[BraidedMonoidal]包含[Monoidal]），因此它们在三种强度下测试一个原因；只有[Opposite]独立于该链。
*)

Universes co ch cp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}).
Context (a b : Cu).

(* Controls, applied, at the very levels the negatives are rejected at. / 在否定被拒绝的同一级别上应用的控制。 *)
Check (a ~{Cu}~> b).
Check (@id Cu a).

(* FORMABILITY negative 1: the opposite category. / 可成形性 负面 1：相反的类别。 *)
Fail Check (@Opposite Cu).
(* FORMABILITY negative 2: the monoidal structure. / 可造性 负 2：单体结构。 *)
Fail Check (@Monoidal Cu).
(* FORMABILITY negative 3: its symmetric refinement. / 可成形性 负3：它的对称细化。 *)
Fail Check (@SymmetricMonoidal Cu).
(* FORMABILITY negative 4: the closed base this file is stated over. / 可成型性 负4：此文件所述的封闭底座。 *)
Fail Check (@SymMonClosed Cu).

End DualProbeFormability.

Section DualProbeConversion.

Context {C : Category}.
Context `{@SymMonClosed C}.
Context (d : C).

(* CONVERSION negative 1: [dd_unit] is not the bare braid-transpose on the nose; the residue is `id ⨂ id`, and writing it out closes the very same statement at [eq_refl]. / CONVERSION 负1：[dd_unit] 不是鼻上的裸编织换位；剩余的是 `id ⨂ id`，写出来会在 [eq_refl] 关闭完全相同的陈述。 *)
Fail Example dual_neg_braid_strict (x : C) :
  dd_unit d x = dcur (eval' ∘ braid) := eq_refl.

(* Control for negative 1, at [eq_refl], with the residue exhibited. / 在 [eq_refl] 对负1 进行控制，并显示剩余物。 *)
Example dual_ctrl_braid_residue (x : C) :
  dd_unit d x = dcur (eval' ∘ (id[x ⇒ d] ⨂ id[x]) ∘ braid) := eq_refl.

(* Control for negative 1, the `≈` form that IS delivered. / 控制负一，即交付的 `≈` 形式。 *)
Example dual_ctrl_braid_equiv (x : C) :
  dd_unit d x ≈ dcur (eval' ∘ braid).
Proof. apply dd_unit_is_braid_transpose. Qed.

(*
 CONVERSION negative 2: for an ARBITRARY [StarAutonomous] instance,
 conversion does not establish that the posited double-dual
 isomorphism is the canonical map.  This is the sharpest available
 form of "the class does not pin its iso"; it does NOT say the
 equation is false. 

 --------
 转换负 2：对于一个任意的 [StarAutonomous] 实例，转换并不能证明所假定的双对偶同构是典范映射。这是“该类未确定其同构”的最精确形式；它并没有说该方程是错误的。
*)
Fail Example dual_neg_arbitrary_star (SA : @StarAutonomous C _) (x : C) :
  to (@star_double_dual C _ SA x) = dd_unit (@dualizer C _ SA) x
  := eq_refl.

(* Control for negative 2: at the instance THIS file produces, the same equation closes at [eq_refl]. / 控制负2：在此文件生成的实例中，相同的方程在 [eq_refl] 处关闭。 *)
Example dual_ctrl_produced_star
  (Hiso : forall x : C, IsIsomorphism (dd_unit d x)) (x : C) :
  to (@star_double_dual C _ (StarAutonomous_of_dd_unit d Hiso) x)
    = dd_unit d x := eq_refl.

End DualProbeConversion.

Section DualProbeTyping.

Context {C : Category}.
Context `{@SymMonClosed C}.
Context (d : C).

Notation "'DSA'" :=
  (dual_self_adjoint_on_the_right d) (only parsing).

(* TYPING negative: off the diagonal the two legs of the bijection do not even have the same type, so "to = from" is not statable there. This is the honest form of Mac Lane's symmetry claim. / TYPING 否定：在对角线之外，双射的两条腿甚至没有相同的类型，所以在那里的“to = from”是无法表述的。这是 Mac Lane 对称性声明的真实形式。 *)
Fail Example dual_neg_offdiagonal (a x : C) :
  to (@aor C C (dual d) (dual d) DSA a x)
    = from (@aor C C (dual d) (dual d) DSA a x) := eq_refl.

(* Control: ON the diagonal the two legs ARE the same term. / 控制：在对角线上，两条边是同一项。 *)
Example dual_ctrl_diagonal (a : C) :
  to (@aor C C (dual d) (dual d) DSA a a)
    = from (@aor C C (dual d) (dual d) DSA a a) := eq_refl.

(* Control: off the diagonal what holds is the SWAP, at [eq_refl] on the whole [SetoidMorphism]. / 控制：在对角线之外保持的是交换，在整个 [SetoidMorphism] 上的 [eq_refl]。 *)
Example dual_ctrl_swapped (a x : C) :
  to (@aor C C (dual d) (dual d) DSA a x)
    = from (@aor C C (dual d) (dual d) DSA x a) := eq_refl.

End DualProbeTyping.
