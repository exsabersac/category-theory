(* * * (R-Mod, ⊗, R): the symmetric monoidal structure of a module category / * * (R-模, ⊗, R)：模范畴的对称幺半群结构 *)

(*
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 §VII.1, printed p. 163 — the roster of tensor-product monoidal
 categories, of which "K-modules over a commutative ring K" is
 the row Instance/Ab/Monoidal.v's own SCOPE note defers.
 Book:      Mac Lane, ibid., §IV.1 printed p. 80 and §IV.6 printed p. 98 —
 the tensor-hom adjunction, whose ⊗ half is what this file
 supplies.
 nLab:      https://ncatlab.org/nlab/show/tensor+product+of+modules
 nLab:      https://ncatlab.org/nlab/show/symmetric+monoidal+category
 Wikipedia: https://en.wikipedia.org/wiki/Tensor_product_of_modules

 Instance/Mod/Tensor.v built the object V ⊗ V' by generators and relations
 together with its universal property, and then said in terms what it did
 NOT build (Instance/Mod/Tensor.v):

 "NO BIFUNCTORIALITY.  Instance/Ab/Tensor.v's [AbTensor_Functor] has no
 counterpart here: nothing below makes ⊗ a functor
 [RMod R ∏ RMod R ⟶ RMod R], and no monoidal structure on [RMod R] is
 attempted.  (Both would be [tensor_hom_ext] plus computations on
 generators, exactly as there.)"

 This file discharges that, and the parenthetical forecast is accurate.
 Delivered:

 - [ModTensor : RMod R ∏ RMod R ⟶ RMod R], the tensor bifunctor
 - [ModUnitLeft], [ModUnitRight], the two unitors as isomorphisms
 - [ModAssoc] over [mod_assoc_to] / [mod_assoc_fr], the associator
 - [ModMonoidal], with both naturality directions for each structural
 isomorphism and both coherence laws
 - [ModBraid], [ModBraided], [ModSymmetric], with both hexagons and the
 involution

 GENERALITY, AND WHY THE BASE IS NOT [CRng].  Everything is stated over an
 arbitrary [RingObject] together with an EXPLICIT commutativity hypothesis

 Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
 rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

 which is, after elaboration, the predicate of Instance/Rng.v's
 [CRng_Sub], so an object of [CRng] supplies it by projection and
 Instance/Rng.v's [Int_Ring_commutative] discharges it at ℤ.  Indexing
 by [CRng] instead would have been the wrong move twice over: the module
 category the tree actually has is [RMod R] for a [RingObject] R, so a
 [CRng]-indexed statement would have to project its first component back
 out at every use, and — more to the point — carrying the hypothesis
 separately is what makes it MEASURABLE.  With commutativity a named
 variable rather than a field of the base object, the discharged signature
 of each constant records whether that constant used it, which is the
 instrument the paragraph on commutativity below relies on.

 THE PENTAGON IS DEFINITIONAL.  This is the file's most surprising fact and
 the reason the coherence half is short.  Instance/Mod/Tensor.v's mediator
 is [tensor_med_fun], a [Fixpoint] matching on the constructors of [MTerm];
 so the associator does not merely satisfy an equation on generators, it
 COMPUTES on them — [mod_assoc_to] sends the term `(a ⊗ b) ⊗ c` to the term
 `a ⊗ (b ⊗ c)` by reduction alone.  Both routes around the pentagon
 therefore carry `((a ⊗ b) ⊗ c) ⊗ d` to the very same [MTerm], namely
 `a ⊗ (b ⊗ (c ⊗ d))`, and the obligation closes with `simpl; apply mt_refl`
 once extensionality has exposed a fourfold generator.  The same holds of
 the two associator naturality squares, of braid naturality, of both
 hexagons and of the braid involution.  [mod_pentagon_computes] below
 records the collapse concretely over ℤ, as a Leibniz `eq_refl` between the
 two composites applied to `((2 ⊗ 3) ⊗ 5) ⊗ 7` — the acceptance test rather
 than the header is what checks this claim.

 Note the register precisely: [mt_refl], not [reflexivity].  `≈` on
 [TensorMod] is [mt_eq], whose reflexivity is a DERIVED lemma rather than a
 constructor, so after [simpl] the tactic [reflexivity] does not close the
 goal and names no useful culprit; [apply mt_refl] does.  An earlier
 revision called [mt_eq] "[Type]-valued"; since the PR "algebraic carriers
 are sets" (2026-09-17) it is a [Prop], which is what lets [TensorMod]
 supply its own [cmon_prop].  The register point is unaffected -- the issue
 is that reflexivity is derived, not the relation's sort.

 ONLY THREE OBLIGATIONS CARRY MATHEMATICAL CONTENT.  Of [ModMonoidal]'s
 eight fields, five close by conversion once the extensionality principles
 have reduced them to generators (`simpl; apply mt_refl`): both associator
 naturality squares, both `from`-direction unitor squares, and the
 pentagon.  What is left is exactly three:

 - [to_unit_left_natural] and [to_unit_right_natural], each of which is
 one application of Instance/Mod.v's [rm_map_smul] — the statement that
 a module homomorphism commutes with the action.  These are the only
 fields where the unitor's `to` leg, which multiplies, meets an
 arbitrary morphism.
 - [triangle_identity], which is Instance/Mod/Tensor.v's
 [tensor_balanced] — that a scalar may be moved across the tensor sign,
 `(r · a) ⊗ b ≈ a ⊗ (r · b)`.  That equation is the one place where the
 two unitors have to agree about which factor absorbs the scalar, and
 it is emphatically NOT definitional: over ℤ the two sides of the
 triangle reach the literally different terms `6 ⊗ 5` and `3 ⊗ 10`.
 [probe_balanced_conversion] pins that.

 Both the [BraidedMonoidal] and the [SymmetricMonoidal] layers add no
 content-bearing obligation at all; all four of their fields are `mt_refl`.

 THE GENERATOR-SLOT GADGET.  [tensor_hom_ext] says that two homomorphisms
 out of V ⊗ V' agreeing on generators agree everywhere, but the coherence
 laws are stated at ITERATED tensors, where the left (or right) factor of a
 generator is itself an arbitrary formal expression.  The obvious route is
 to induct through that factor, which is what Instance/Ab/Monoidal.v does:
 its [AgreeOnL] / [AgreeOnR] predicates with their eight closure lemmas
 occupy [Section GeneratorClosure] of that file, and the three principles
 that iterate them to depth two and three occupy the block that follows
 it — 98 and 67 lines, so 165 in all (measured on that file at the
 revision this one was written against).  The contiguous span covering
 both is 173 lines, but the eight lines between them belong to neither, so
 165 is the like-for-like figure and 173 would pad the denominator.

 The route taken here instead makes generator insertion a first-class
 module homomorphism.  [gen_r b : A ~> A ⊗ B] is `a ↦ a ⊗ b` and [gen_l a]
 is `b ↦ a ⊗ b`; each is a homomorphism precisely because the canonical map
 is bilinear, so its four obligations are the generator former's congruence
 rule, its additivity rule, the derived [tensor_zero_l], and one clause of
 [tensor_gen]'s bilinearity — no induction anywhere.  With them, reaching
 a nested generator becomes COMPOSITION rather than induction: to compare
 f and g on `(v ⊗ w) ⊗ x`, apply [tensor_hom_ext] once to peel the outer
 tensor and then again to `f ∘ gen_r x` and `g ∘ gen_r x`, which are
 honest module homomorphisms out of V ⊗ W.  [tensor_hom_ext_l],
 [tensor_hom_ext_r] and [tensor_hom_ext_ll] are five, five and seven lines
 of proof respectively.

 Measured on the same basis — comments and blank lines included — the
 whole gadget layer, from [mval] through [tensor_hom_ext_ll], is 129 lines
 against the Ab side's 165.  Read that comparison narrowly.  56 of the 129
 are the uniform four-way obligation body repeated across the eight
 [Program] obligations of [gen_r] and [gen_l], following
 Instance/Mod/Tensor.v's own idiom, so the substantive remainder is 73;
 and the two developments quotient by different relations, so no claim is
 made that the Ab-side machinery could have been written this way.  It was
 not re-attempted.

 WHERE COMMUTATIVITY IS SPENT.  In exactly three places, and all three have
 the same shape, `r · (s · v) ≈ s · (r · v)`:

 - [act_bilin]'s [rbl_smul_r] clause.  The action R × V → V is additive
 and R-linear in the left variable for free, but linear in the RIGHT
 variable — `r · (s · v) ≈ s · (r · v)` — only because R commutes.
 - [act_bilin_r]'s [rbl_smul_l] clause, the mirror image.
 - [rmod_hom_smul]'s [rm_map_smul] clause: `r · f(−)` is a module
 homomorphism, not merely an additive map, again only for commutative
 R.  This is what lets the associator's outer bilinear maps state their
 scalar clauses as equalities of HOMOMORPHISMS and so reduce them to
 generators via [tensor_hom_ext].

 Everything else is commutativity-free, and that is arranged structurally
 rather than asserted: [mval], [gen_r], [gen_l], the three
 [tensor_hom_ext_*] principles, [mt_bimap], [mt_fmap], [ModTensor],
 [braid_bilin], [ModBraid], and the associator's two inner legs
 ([assoc_in], [mod_assoc_fr_in]) are all declared in sections that do not
 bind [Rcomm] at all, so no proof in them could have used it.

 The consequence was VERIFIED AT THE SIGNATURES, by reading the discharged
 [Arguments] lines rather than the source: [ModUnitLeft {R} Rcomm V],
 [mod_assoc_to {R} Rcomm {V W X}], [rmod_hom_smul {R} Rcomm {M N} r f],
 [ModMonoidal {R} Rcomm] and [ModSymmetric {R} Rcomm] take the hypothesis,
 while [ModTensor {R}], [gen_r {R A B} b], [gen_l {R A B} a],
 [mval {R V W} f v], [ModBraid {R} V W], [assoc_in {R V W X} x],
 [mod_assoc_fr_in {R V W X} v] and [tensor_hom_ext_ll {R V W X Y K} f g]
 do not.  The TYPING negatives below pin the contrast from the failing
 side.  That the BRAIDING itself is commutativity-free is worth stating
 separately: the symmetry of ⊗ is a fact about the two-variable
 presentation of the tensor, not about R.

 UNIVERSES, MEASURED IN THE CONSTRAINT BLOCKS.  Nothing here is annotated,
 so what follows is what inference assigned; it was read off [About], and
 off BOTH the binder and the constraint block, since in this library the
 two routinely disagree.  The finding is an asymmetry between the
 components and the assembly.  Every component leaves the [RingObject]'s
 first two universes merely BOUNDED — [ModTensor@{u u0 u1 u2}] carries
 `u0 <= u` together with `u = u1`, and so do [gen_r], [ModBraid],
 [ModUnitLeft], [ModUnitRight] and [ModAssoc].  [rmod_hom_smul] belongs
 with them as a control but not as an instance of that shape: measured,
 its block carries NO equation at all and no `u0 <= u`, only
 `u <= u1`, `u0 <= u1` and `u1 <= u2`, so it makes the point a fortiori.
 The
 assembled [ModMonoidal@{u u0 u1 u2}] instead carries `u = u0`,
 IDENTIFYING them, and [ModBraided] and [ModSymmetric] inherit it.

 The identification belongs to no one donor, and that is measured rather
 than attributed.  Under a declared `Constraint rp < ru` — which satisfies
 the bound while violating the equation — ELEVEN separate applications
 elaborate at `RingObject@{ru rp rq}`: [RMod Ru], [Ring_RMod Ru],
 [@Monoidal (RMod Ru)], [ModTensor], [gen_r], [gen_l], [ModBraid],
 [ModUnitLeft], [ModUnitRight], [ModAssoc] and [rmod_hom_smul] — including
 the [Monoidal] class itself and the unit object, the two obvious suspects
 — while [ModMonoidal] is rejected with
 "Cannot enforce rp = ru because rp < ru".
 The equation is therefore introduced by the PACKAGING and not by any
 field it packages.  No mechanism beyond that is claimed, no annotation was
 attempted, and the identification is NOT claimed unavoidable:
 Instance/Ab/Monoidal.v's design note 5 is the in-tree precedent for
 exactly such an identification turning out to be a minimization artifact
 that explicit declarations lift.

 PLACEMENT.  The gadget layer is arguably Instance/Mod/Tensor.v's — it
 mentions nothing this file introduces, and [tensor_hom_ext] is already
 there.  It lives here only so that Tensor.v is left untouched.  A later
 editor moving [mval], [gen_r], [gen_l] and the three extensionality
 lemmas upstream would change nothing below except the import list.

 The four [Ltac]s ([tens_ext] and siblings) are declared at top level
 because tactic notations do not survive a [Section].  They are named for
 this file's idiom rather than generically, since [Ltac] names are global;
 the sweep recorded below found no other use of any of them in tree.

 ENGINEERING NOTES, each of which cost a compile cycle.

 (a) `apply tensor_hom_ext` FAILS, and NOT for the reason one first
 guesses.  The goal `f ≈ g` in [RMod R] does unfold to
 `∀ a : TensorMod V W, f a ≈ g a`, so the hom-setoid is not the
 obstacle.  What [apply] reports (measured, with the statement below
 restated in a scratch file) is
 `Unable to unify "?M ?t ≈ ?M' ?t" with "∀ a, f a ≈ g a"` — a
 HIGHER-ORDER unification failure, the lemma's `cmon_map (rm_hom ?f)`
 presenting as an applied metavariable while `f` and `g` are still
 unknown.  Supplying them makes the head rigid, so the [Ltac]s below
 use `match goal with |- ?f ≈ ?g => refine (tensor_hom_ext f g _)
 end`.
 (b) [mt_eq_Equivalence] (Instance/Mod/Tensor.v) is a [Lemma], not an
 [Instance], so setoid [rewrite] and [transitivity] cannot see it and
 the resulting error names the wrong culprit.  Nothing below needs
 it; a consumer that does should add
 `#[local] Existing Instance mt_eq_Equivalence.`
 (c) [mt_gen] and [mte_gen] at a NESTED tensor need explicit `@`
 annotation.  Measured: writing `mt_gen (mt_gen v w) x` with the
 module arguments implicit is rejected with
 `The term "mt_gen v w" has type "MTerm V W" while it is expected to
 have type "carrier ?V"` — the inner generator is elaborated before
 the outer tensor is known, and a bare [MTerm] does not unify with a
 projection out of an unknown module.  This is the same trap
 Instance/Ab/Monoidal.v records at its [tensor_hom_ext2], and it is
 pinned as a TYPING negative below.
 (d) [Program] silently discharges [rbl_respects] by instance resolution
 when the map is literally [rm_smul], because Tensor.v exports
 that field as an instance.  The obligation numbering then SHIFTS and
 the remaining proofs land on the wrong goals.  [act_bilin] therefore
 supplies [rbl_respects] explicitly; [act_bilin_r], whose map is
 [rm_smul] with its arguments swapped, is not caught by resolution
 and does not need to.
 (e) The records taking [Rcomm] are [Program Definition] and NOT
 [Instance].  Registering [ModMonoidal] would leave typeclass
 resolution an unsolvable commutativity subgoal at every use over an
 abstract ring.  (Instance/Ab/Monoidal.v's design note 4 registers
 its structures because [@Monoidal Ab] has no other inhabitant and
 needs no hypothesis; neither reason applies here.)  Consumers pass
 the structure explicitly, as the acceptance tests below do.
 (f) Name collisions found and avoided.  `assoc_to` is taken by
 Construction/Day.v, hence [mod_assoc_to] / [mod_assoc_fr];
 `rmod_hom_neg` is taken by Instance/FdVect/DoubleDual.v, hence the
 scaling map is [rmod_hom_smul] and no negation map is declared; and
 `probe_instrument`, the obvious name for the probe section's
 instrument check, is taken by Test/ProbePolynomial.v, hence
 [mod_monoidal_instrument].  That last one matters even though the
 name sits inside a [Fail] and so creates no constant: the
 `print-assumptions` gate loads many files into one scope, where a
 shared name silently audits the wrong constant.  A sweep of all 62
 names this file declares — the constants from its own `.glob`
 rather than guessed, and the four [Ltac]s read off the source,
 since the `.glob` records no [Ltac] entry at all — found no other
 occurrence of any of the rest anywhere in tree.

 MEASUREMENTS RECORDED.  123/123 constants closed under the global context
 — the count is [Print Module]'s, which lists 51 source-declared names
 together with the 72 [Program] obligations no source sweep sees, and the
 file declares no [Record], [Class] or [Inductive], so there is no unlisted
 [Build_*].  (It renders the opaque constants as [Parameter]; that is a
 display convention, not an axiom.)  Read the GRADE: that is a ONE-TIME
 measurement, not a standing gate.  The commit that lands this file
 registers it in `_CoqProject` and puts eight of its constants into the
 `print-assumptions` target, so the build compiles the file and re-audits
 those eight on every run; the other 115 were measured once, by hand.

 The probe section carries EIGHT negatives in FOUR kinds (3 typing, 2
 conversion, 1 resolution, 2 formability) together with a scope-free
 instrument check — nine [Fail] commands in all, the instrument being a
 guard rather than a negative.  Each of the eight is
 stripped of its [Fail], compiled alone and its failure kind read off the
 whole error message.  Rename-simulated 9/9 on the constants a negative
 names and this file declares — [ModUnitLeft], [mod_assoc_to], [ZMod],
 [zz2], [zz3], [zz5], [mval], [ModMonoidal], [ModSymmetric] — each renamed
 AT ITS DEFINITION SITE, since a whole-file rename is a no-op by
 construction and would report a false clean bill; all nine broke the file
 at a NON-[Fail] line, so no guard is vacuous.  The [UniverseProbe]
 section's local [Universes] and [Constraint] declarations were measured
 NOT to leak: a downstream file reusing the same level names with the
 OPPOSITE constraint still elaborates.

 WHAT IS NOT DELIVERED.

 - NO CLOSED STRUCTURE.  The internal hom, the tensor-hom adjunction and
 any [SymMonClosed] instance are a companion file's business, not this
 one's; nothing here mentions an exponent.
 - NO PROOF THAT ⊗ IS NOT THE CATEGORICAL PRODUCT.  It is not, but no
 separation is machine-checked here, so this file does NOT establish
 "the tree's first non-cartesian monoidal witness" — that phrase would
 need a refutation nobody has written.  What is claimed instead is
 narrower and is evidence of two weaker kinds: a sweep for the
 SPELLINGS `@Monoidal … RMod` and `Monoidal (RMod` returns nothing, and
 Instance/Mod/Tensor.v disclaims the structure in its own prose.
 Neither rules out some generic construction inhabiting
 [@Monoidal (RMod R)] under another name.
 - NO [Instance] REGISTRATION, for reason (e) above; [ModMonoidal],
 [ModBraided] and [ModSymmetric] are plain [Program Definition]s and do
 not participate in resolution.
 - NO NATURALITY IN R.  Nothing says how the structure varies along a
 ring homomorphism, and no comparison with Instance/Rng/Mod.v's
 restriction of scalars is attempted.
 - NO COMPARISON WITH Instance/Ab/Monoidal.v.  Over R = ℤ the two
 monoidal structures ought to agree, and no comparison functor is
 built.  An earlier revision gave the reason as "the ℤ-module
 structure of an [AbObject] is not in tree (Instance/Mod/Tensor.v
 records the same gap for the underlying tensors)"; since #454 that
 structure is Instance/Mod/Cogenerator.v's [Ab_to_ZMod], so what is
 missing is the comparison itself, not its ingredients.
 - NO UNIVERSE REPAIR.  The identification recorded above is measured and
 pinned, not lifted.  No constant in this file carries a universe
 annotation, and whether declarations in the style of
 Instance/Ab/Monoidal.v's design note 5 would free [ModMonoidal] is
 untested; so is whether the restriction bites at any category a
 consumer would want.
 - NO MONOIDS, ALGEBRAS OR BIMODULES over the structure, and no graded or
 differential-graded variants — the sibling rows of Mac Lane's §VII.1
 roster. 

 --------
 书籍：Mac Lane, 《为实际工作的数学家分类》，第2版，§VII.1，第163页——张量积单态范畴的列表，其中“交换环K上的K-模”是行 Instance/Ab/Monoidal.v 自身的范围说明延迟的。
 书籍：Mac Lane，同上，§IV.1 第80页 和 §IV.6 第98页——张量-同函子伴随，其 ⊗ 部分是此文件提供的。
 nLab: https://ncatlab.org/nlab/show/tensor+product+of+modules
 nLab: https://ncatlab.org/nlab/show/symmetric+monoidal+category
 维基百科: https://en.wikipedia.org/wiki/Tensor_product_of_modules

 Instance/Mod/Tensor.v 通过生成元与关系构建了对象 V ⊗ V' 及其泛性质，然后用术语说明它没有构建的内容（Instance/Mod/Tensor.v）:"没有双函子性。Instance/Ab/Tensor.v 中的 [AbTensor_Functor] 在这里没有对应项：下面没有任何东西使 ⊗ 成为函子 [RMod R ∏ RMod R ⟶ RMod R]，也没有尝试在 [RMod R] 上建立单体结构。（两者都将是 [tensor_hom_ext] 加上生成元上的计算，完全如那里一样。）

 此文件解决了这一点，并且括号中的预测是准确的。提供：

 - [ModTensor : RMod R ∏ RMod R ⟶ RMod R]，张量双函子
 - [ModUnitLeft], [ModUnitRight]，两个单位同构
 - [ModAssoc] 在 [mod_assoc_to] / [mod_assoc_fr] 上的结合子
 - [ModMonoidal]，对每个结构同构都有两个自然性方向，并包含两个相容律
 - [ModBraid], [ModBraided], [ModSymmetric]，包含两个六边形和反演一般性，以及为什么底是  [CRng]。所有内容都是在任意 [RingObject] 上陈述的，并且带有一个明确的交换性假设。

 上下文 (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
 rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a)。经过详细说明后，它是 Instance/Rng.v 的 [CRng_Sub] 的谓词，因此 [CRng] 的对象通过投影提供它，而 Instance/Rng.v 的 [Int_Ring_commutative] 在 ℤ 上释放它。用 [CRng] 进行索引则是两次错误的选择：该树实际拥有的模块范畴是 [RMod R] 对于一个 [RingObject] R，因此 [CRng] 索引的语句必须在每次使用时将其第一个分量投影回去，更重要的是，单独携带假设使其可测量。将交换律作为一个命名变量而不是基对象的一个字段，每个常量被释放的签名记录了该常量是否使用了它，这就是下面关于交换律段落所依赖的工具。五边形是定义性的。这是该文件中最令人惊讶的事实，也是连贯性部分很短的原因。Instance/Mod/Tensor.v 的中介是 [tensor_med_fun]，它是一个 [Fixpoint]，匹配 [MTerm] 的构造器；因此结合器不仅仅在生成元上满足一个方程，它实际上在它们上进行计算——[mod_assoc_to] 通过简化将项 `(a ⊗ b) ⊗ c` 发送到项 `a ⊗ (b ⊗ c)`。因此，绕过五边形的两条路径都将 `((a ⊗ b) ⊗ c) ⊗ d` 带到完全相同的 [MTerm]，即 `a ⊗ (b ⊗ (c ⊗ d))`，一旦外延性暴露了四倍生成元，义务就以 `simpl; apply mt_refl` 结束。两个结合器自然性方格、编织自然性、两个六边形以及编织反演同样成立。[mod_pentagon_computes] 以下具体记录了在 ℤ 上的崩溃，作为两个复合作用于 `((2 ⊗ 3) ⊗ 5) ⊗ 7` 之间的 Leibniz `eq_refl`——检查这一断言的是验收测试，而不是头部。

 注意精确记录：[mt_refl]，而不是 [reflexivity]。`≈` 在 [TensorMod] 上是 [mt_eq]，其自反性是一个 DERIVED 引理，而不是构造器，因此在 [simpl] 之后，策略 [reflexivity] 无法关闭目标，也没有指明有用的罪魁祸首；[apply mt_refl] 可以。在早期的修订版中，[mt_eq] 被称为“[Type] 值”；自从 PR “代数载体是集合”（2026-09-17）之后，它是一个 [Prop]，这让 [TensorMod] 可以提供其自身的 [cmon_prop]。注册点不受影响——问题在于自反性是推导出来的，而不是关系的类型。只有三个义务包含数学内容。在 [ModMonoidal] 的八个字段中，五个在经过外延性原理将它们化简为生成元（`simpl; apply mt_refl`）后，通过转换而关闭：两个结合子自然性方块、两个 `from` 方向的单位器方块，以及五边形。剩下的正好是三个：- [to_unit_left_natural] 和 [to_unit_right_natural]，它们中的每一个都是 Instance/Mod.v 的 [rm_map_smul] 的一个应用——即一个模块同态与作用交换的陈述。这些是唯一 unitor 的 `to` 分支（用于乘法）与任意态射相交的字段。
 - [triangle_identity]，它是 Instance/Mod/Tensor.v 的 [tensor_balanced]——即一个标量可以通过张量符号移动，ZW211WZZ。该方程是两者 unitor 必须在吸收标量的因子上达成一致的地方，而且绝对不是定义性的：在 ℤ 上，三角形的两边得到字面意义上不同的项 `6 ⊗ 5` 和 `3 ⊗ 10`。ZW50WZZ 固定了这一点。[BraidedMonoidal] 和 [SymmetricMonoidal] 两个层都没有增加任何承载内容的义务；它们的四个字段都是 `mt_refl`。发电机槽小工具。[tensor_hom_ext] 说，从 V ⊗ V' 出发的两个同态，如果在生成元上相同，则在所有地方都相同，但相干律是在迭代张量上陈述的，此时生成元的左（或右）因子本身是任意形式的表达式。显而易见的路线是对该因子进行归纳，这正是 Instance/Ab/Monoidal.v 所做的：它的 [AgreeOnL] / [AgreeOnR] 谓词及其八个闭合引理占据了该文件的 [Section GeneratorClosure]，而将它们迭代到深度二和三的三个原理占据了紧随其后的代码块——分别为 98 行和 67 行，总共 165 行（以编写本文时所对应版本的该文件为准）。覆盖两者的连续范围是173行，但它们之间的八行属于两者都不算，所以165是对应的数字，而173会使分母变大。这里采用的路线反而使生成器插入成为一个一等的模同态。[gen_r b : A ~> A ⊗ B] 是 `a ↦ a ⊗ b`，而 [gen_l a] 是 `b ↦ a ⊗ b`；每一个都是同态，正因为规范映射是双线性的，所以它的四个义务分别是生成器形成者的一致性规则、加法性规则、派生的 [tensor_zero_l]，以及 [tensor_gen] 的双线性性的一条条款——毫无归纳法。在它们的帮助下，达到嵌套生成器变成了组合操作而不是归纳法：要比较 f 和 g 在 `(v ⊗ w) ⊗ x` 上的值，先应用 [tensor_hom_ext] 一次以剥离外部张量，然后再次应用于 `f ∘ gen_r x` 和 `g ∘ gen_r x`，它们是来自 V ⊗ W 的真正的模同态。[tensor_hom_ext_l]、[tensor_hom_ext_r] 和 [tensor_hom_ext_ll] 的证明分别是五行、五行和七行。以相同的标准衡量——包括注释和空行——整个工具层，从 [mval] 到 [tensor_hom_ext_ll]，共计 129 行，而 Ab 侧为 165 行。狭义地看这个对比。129 行中有 56 行是统一的四向义务主体，在 [gen_r] 和 [gen_l] 的八个 [Program] 义务中重复，遵循 Instance/Mod/Tensor.v 自身的习惯，因此实质性剩余部分为 73；并且这两个开发按不同的关系进行划分，因此并不声称 Ab 侧的机制可以这样编写。没有重新尝试。

 ［交换律使用的地方］。正好在三个地方，并且这三处具有相同的形式，`r · (s · v) ≈ s · (r · v)`：-  [act_bilin] 的 [rbl_smul_r] 条款。操作 R × V → V 在左变量上是加法的且 R 线性的，这是免费的，但在线性右变量上 — `r · (s · v) ≈ s · (r · v)` — 仅因为 R 是交换的。
 -  [act_bilin_r] 的 [rbl_smul_l] 条款，镜像。
 -  [rmod_hom_smul] 的 [rm_map_smul] 条款：`r · f(−)` 是模同态，而不仅仅是加法映射，同样仅适用于交换 R。这就是使结合子外双线性映射能够将它们的标量条款表述为同态的等式，并因此通过 [tensor_hom_ext] 将其归约到生成元。其他一切都是无交换性的，这是通过结构安排而非断言实现的：[mval]、[gen_r]、[gen_l]、三个[tensor_hom_ext_*]原理、[mt_bimap]、[mt_fmap]、[ModTensor]、[braid_bilin]、[ModBraid]，以及结合子的两个内腿（[assoc_in]、[mod_assoc_fr_in]）都在完全不绑定[Rcomm]的章节中声明，因此其中的任何证明都无法使用它。结果在签名处得到验证，通过读取已释放的 [Arguments] 行，而不是源：[ModUnitLeft {R} Rcomm V]、[mod_assoc_to {R} Rcomm {V W X}]、[rmod_hom_smul {R} Rcomm {M N} r f]、[ModMonoidal {R} Rcomm] 和 [ModSymmetric {R} Rcomm] 采用假设，而 [ModTensor {R}]、[gen_r {R A B} b]、[gen_l {R A B} a]、[mval {R V W} f v]、[ModBraid {R} V W]、[assoc_in {R V W X} x]、[mod_assoc_fr_in {R V W X} v] 和 [tensor_hom_ext_ll {R V W X Y K} f g] 则不采用。下面的 TYPING 否定标记从失败的一侧明确了对比。值得单独说明的是，BRAIDING 本身不具交换性：⊗ 的对称性是张量的双变量表示的一个事实，而不是关于 R 的。宇宙，以约束块衡量。这里没有任何注释，因此以下内容是推理所分配的；它是从 [About] 读取的，同时读取了装订器和约束块，因为在这个库中，两者通常会不一致。研究发现组件和组装之间存在不对称。每个组件仅将 [RingObject] 的前两个宇宙保持有界——[ModTensor@{u u0 u1 u2}] 携带 `u0 <= u` 和 `u = u1`，[gen_r]、[ModBraid]、[ModUnitLeft]、[ModUnitRight] 和 [ModAssoc] 也是如此。[rmod_hom_smul] 作为控制属于它们，但不是该形状的实例：测量时，它的块完全不携带任何方程，也不携带 `u0 <= u`，只携带 `u <= u1`、`u0 <= u1` 和 `u1 <= u2`，因此它进一步论证了这一点。组装的 [ModMonoidal@{u u0 u1 u2}] 实际上携带 `u = u0`，对它们进行识别，[ModBraided] 和 [ModSymmetric] 继承它。该识别不属于任何捐赠者，并且它是被测量的而不是被归因的。在一个声明的 `Constraint rp < ru` 下——它满足界限但违反方程——有十一种单独的应用在 `RingObject@{ru rp rq}` 上展开：[RMod Ru]、[Ring_RMod Ru]、[@Monoidal (RMod Ru)]、[ModTensor]、[gen_r]、[gen_l]、[ModBraid]、[ModUnitLeft]、[ModUnitRight]、[ModAssoc] 和 [rmod_hom_smul]——包括 [Monoidal] 类本身以及单位对象，这两个显而易见的嫌疑者——而 [ModMonoidal] 被拒绝并显示“无法执行 rp = ru 因为 rp < ru”。因此，该方程是由包装引入的，而不是由其所包装的任何字段引入。除了上述机制外，没有声称其他机制，也没有尝试注释，并且该识别**不被声称为不可避免**：
 Instance/Ab/Monoidal.v 的设计注释 5 是树内前例，说明正是这样的识别最终被证明是最小化的伪影，通过显式声明可以消除。

 放置位置。这个小工具层可以说属于 Instance/Mod/Tensor.v——它未提及本文件引入的任何内容，并且 [tensor_hom_ext] 已经存在于那里。它存在于这里只是为了不修改 Tensor.v。稍后的编辑器如果将 [mval]、[gen_r]、[gen_l] 以及三个拓展性引理上移，只会改变下面的导入列表，其他都不会改变。四个 [Ltac]（[tens_ext] 和其兄弟）在顶层被声明，因为策略符号在 [Section] 中不会保留。它们以此文件的习惯用法命名，而不是通用名称，因为 [Ltac] 名称是全局的；下面记录的检查没有发现它们在树中的其他使用。

 工程说明，每个都消耗一个编译周期。(a) `apply tensor_hom_ext` 失败，而且原因并非人们最初猜测的那样。目标 `f ≈ g` 在 [RMod R] 中确实展开为 `∀ a : TensorMod V W, f a ≈ g a`，因此同类集不是障碍。[apply] 报告的内容（用下面的陈述在草稿文件中重新测量）是 `Unable to unify "?M ?t ≈ ?M' ?t" with "∀ a, f a ≈ g a"`——一个高阶统一失败，该引理的 `cmon_map (rm_hom ?f)` 表现为一个已应用的元变量，而 `f` 和 `g` 仍然未知。提供它们会使头部变得僵硬，因此下面的 [Ltac] 使用 `match goal with |- ?f ≈ ?g => refine (tensor_hom_ext f g _) end`。 (b) [mt_eq_Equivalence]（Instance/Mod/Tensor.v）是一个 [Lemma]，而不是 [Instance]，因此同类 [rewrite] 和 [transitivity] 无法看到它，导致的错误命名了错误的原因。下面没有任何需要它；需要的消费者应该在嵌套张量上添加 `# [local]ZZ  Existing Instance mt_eq_Equivalence.` (c) [mt_gen] 和 [mte_gen] 以进行显式 `@` 注解。测量时：在模块参数隐式情况下写入 `mt_gen (mt_gen v w) x` 会被拒绝，提示 `The term "mt_gen v w" has type "MTerm V W" while it is expected to have type "carrier ?V"` ——内层生成器在外层张量已知之前被展开，而裸露的 [MTerm] 无法与未知模块的投影统一。这与 Instance/Ab/Monoidal.v 在其 [tensor_hom_ext2] 中记录的陷阱相同，并且在下面被标记为 TYPING 负例。(d) [Program] 通过实例解析悄悄地释放了 [rbl_respects]，当映射字面上是 [rm_smul] 时，因为 Tensor.v 将该字段以实例导出。义务编号随后发生偏移，其余证明落在错误的目标上。因此 [act_bilin] 明确提供了 [rbl_respects]；[act_bilin_r] 的映射是 [rm_smul] 并且其参数交换，并未被解析捕获，也不需要被捕获。 (e) 接受 [Rcomm] 的记录是 [Program Definition]，而不是 [Instance]。在每次使用抽象环时，注册 [ModMonoidal] 会使类型类解析留下一个无法解决的交换性子目标。(Instance/Ab/Monoidal.v 的设计说明第 4 条登记了其结构，因为 [@Monoidal Ab] 没有其他实例，也不需要假设；这两个理由在这里都不适用。) 消费者会显式地传递该结构，就像下面的验收测试所做的那样。(f) 已发现并避免了名称冲突。Construction/Day.v 已占用 `assoc_to`，因此使用 [mod_assoc_to] / [mod_assoc_fr]；Instance/FdVect/DoubleDual.v 已占用 `rmod_hom_neg`，因此缩放映射使用 [rmod_hom_smul]，且未声明取负映射；而用于探针部分仪器检查的显而易见名称 `probe_instrument` 已被 Test/ProbePolynomial.v 占用，因此使用 [mod_monoidal_instrument]。即使名字位于 [Fail] 内并且不会创建常量，最后一个也很重要：`print-assumptions` 门将许多文件加载到一个作用域内，而共享名称会悄悄审核错误的常量。对该文件声明的所有 62 个名字进行扫查——使用其自身 `.glob` 的常量而不是猜测，并且四个 [Ltac] 从源文件读取，因为 `.glob` 根本没有记录任何 [Ltac] 条目——没有在树的其他任何地方找到剩余名字的任何其他出现。已记录测量。123/123 常量在全局上下文下封闭 —— 计数为 [Print Module] 个，其中列出了 51 个源声明的名称，以及 72 个 [Program] 义务，源扫描无法看到，并且该文件未声明 [Record]、[Class] 或 [Inductive]，因此不存在未列出的 [Build_*]。（它将不透明常量呈现为 [Parameter]；这是一种显示约定，而非公理。）读取等级：这是一次性测量，而不是固定门控。提交该文件的提交将在 `_CoqProject` 中注册它，并将其八个常量放入 `print-assumptions` 目标，因此构建会在每次运行时编译该文件并重新审核这八个常量；其余 115 个常量只测量过一次，由人工完成。探测器部分携带四种类型的八个负例（3 个类型错误，2 个转换错误，1 个解析错误，2 个可成型性错误），以及一个无作用域的仪器检查——总共九个 [Fail] 命令，其中仪器是一个守护而非负例。八个中的每一个都被去除了 [Fail]，单独编译，并从完整的错误信息中读取其失败类型。在常量上进行的重命名模拟 9/9 一个负例名称，这个文件声明了——[ModUnitLeft]、[mod_assoc_to]、[ZMod]、[zz2]、[zz3]、[zz5]、[mval]、[ModMonoidal]、[ModSymmetric]——每个在其定义位置被重命名，因为整个文件的重命名本身是无操作的，并且会报告错误地“清洁”；所有九个都在一个非 [Fail] 行打断了文件，所以没有守护是无效的。[UniverseProbe] 节的本地 [Universes] 和 [Constraint] 声明被测量为不会泄漏：下游文件重用相同的层级名称且具有相反约束时仍然可以展开。

 未交付的内容是什么。- 没有闭合结构。内部 Hom、张量-Hom 拓扑相伴以及任何 [SymMonClosed] 实例都是伴随文件的事，而不是这个文件的事；这里没有提到指数。- 没有证明 ⊗ 不是范畴乘积。它确实不是，但这里没有机器校验的区分，所以这个文件并没有建立“树的第一个非笛卡尔范畴单元证据”——那句话需要一个没有人写过的反驳。相反声称的是更狭窄的内容，并且是两种较弱的证据：对拼写 `@Monoidal … RMod` 和 `Monoidal (RMod` 的一次扫描没有返回任何结果，并且 Instance/Mod/Tensor.v 在其自述中否认了该结构。两者都不排除在另一个名字下存在位于 [@Monoidal (RMod R)] 中的某种通用构造。- 没有 [Instance] 注册，原因见上文(e)；[ModMonoidal]、[ModBraided] 和 [ModSymmetric] 只是普通的 [Program Definition]，并不参与分解。- 在 R 中没有自然性。没有说明结构如何沿环同态变化，也没有尝试与 Instance/Rng/Mod.v 的标量限制进行比较。- 没有与 Instance/Ab/Monoidal.v 的比较。在 R = ℤ 时，这两种单体结构应该是一致的，但没有构建比较函子。早期的修订将原因说明为“[AbObject] 的 ℤ-模结构不在树中（Instance/Mod/Tensor.v 为基础张量记录了相同的缺口）”；自 #454 起，该结构为 Instance/Mod/Cogenerator.v 的 [Ab_to_ZMod]，因此缺少的是比较本身，而不是其组成部分。- 不进行宇宙修复。上述记录的标识是经过测量和固定的，而非提升的。本文件中的任何常量都没有宇宙注解，是否像 Instance/Ab/Monoidal.v 的设计说明第 5 条那样声明会释放 [ModMonoidal] 尚未测试；同样也不清楚该限制是否会影响消费者想要的任何范畴。
 - 不允许在该结构上使用幺半群、代数或双模，以及不允许使用分等级或微分分等级的变体——参见 Mac Lane §VII.1 花名册中的兄弟行。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * ** The generator-slot gadget

   Nothing in this section binds a commutativity hypothesis, so nothing in
   it can have used one.  See the header's paragraph on placement: this
   layer is arguably Instance/Mod/Tensor.v's and lives here only to leave
   that file untouched. 

   --------
   * ** 发电机插槽小工具

   本节中没有任何内容绑定交换律假设，因此其中没有任何内容可能使用了它。请参阅标题段落关于位置的说明：该层可以说是 Instance/Mod/Tensor.v 的，仅放在这里是为了不修改该文件。
*)

Section GenSlots.

Context {R : RingObject}.

(* The underlying function of a module homomorphism. / 模同态的基本函数。 *)
Definition mval {V W : RModObject R} (f : V ~{RMod R}~> W)
  (v : carrier (cmon_setoid V)) : carrier (cmon_setoid W) :=
  cmon_map (rm_hom f) v.

(*
 a ↦ a ⊗ b, as a module homomorphism A ~> A ⊗ B.  One uniform body serves
 all four obligations so the proof does not depend on the order [Program]
 emits them in — the Instance/Mod/Tensor.v idiom. 

 --------
 a ↦ a ⊗ b，作为一个模同态 A ~> A ⊗ B。一个统一的主体满足所有四个义务，因此证明不依赖于 [Program] 发出它们的顺序 —— Instance/Mod/Tensor.v 的惯用法。
*)
Program Definition gen_r {A B : RModObject R}
  (b : carrier (cmon_setoid B)) : A ~{RMod R}~> TensorMod A B := {|
  rm_hom := {| cmon_map := {| morphism := fun a => mt_gen a b |} |}
|}.
Next Obligation.
  intros A B b.
  first [ intros a a' Ha; exact (mte_gen Ha (reflexivity b))
        | exact (tensor_zero_l b)
        | intros a a'; exact (mte_add_l a a' b)
        | intros r a; exact (rbl_smul_l tensor_gen r a b) ].
Qed.
Next Obligation.
  intros A B b.
  first [ intros a a' Ha; exact (mte_gen Ha (reflexivity b))
        | exact (tensor_zero_l b)
        | intros a a'; exact (mte_add_l a a' b)
        | intros r a; exact (rbl_smul_l tensor_gen r a b) ].
Qed.
Next Obligation.
  intros A B b.
  first [ intros a a' Ha; exact (mte_gen Ha (reflexivity b))
        | exact (tensor_zero_l b)
        | intros a a'; exact (mte_add_l a a' b)
        | intros r a; exact (rbl_smul_l tensor_gen r a b) ].
Qed.
Next Obligation.
  intros A B b.
  first [ intros a a' Ha; exact (mte_gen Ha (reflexivity b))
        | exact (tensor_zero_l b)
        | intros a a'; exact (mte_add_l a a' b)
        | intros r a; exact (rbl_smul_l tensor_gen r a b) ].
Qed.

(* b ↦ a ⊗ b, as a module homomorphism B ~> A ⊗ B. / b ↦ a ⊗ b，作为模同态 B ~> A ⊗ B。 *)
Program Definition gen_l {A B : RModObject R}
  (a : carrier (cmon_setoid A)) : B ~{RMod R}~> TensorMod A B := {|
  rm_hom := {| cmon_map := {| morphism := fun b => mt_gen a b |} |}
|}.
Next Obligation.
  intros A B a.
  first [ intros b b' Hb; exact (mte_gen (reflexivity a) Hb)
        | exact (tensor_zero_r a)
        | intros b b'; exact (mte_add_r a b b')
        | intros r b; exact (rbl_smul_r tensor_gen r a b) ].
Qed.
Next Obligation.
  intros A B a.
  first [ intros b b' Hb; exact (mte_gen (reflexivity a) Hb)
        | exact (tensor_zero_r a)
        | intros b b'; exact (mte_add_r a b b')
        | intros r b; exact (rbl_smul_r tensor_gen r a b) ].
Qed.
Next Obligation.
  intros A B a.
  first [ intros b b' Hb; exact (mte_gen (reflexivity a) Hb)
        | exact (tensor_zero_r a)
        | intros b b'; exact (mte_add_r a b b')
        | intros r b; exact (rbl_smul_r tensor_gen r a b) ].
Qed.
Next Obligation.
  intros A B a.
  first [ intros b b' Hb; exact (mte_gen (reflexivity a) Hb)
        | exact (tensor_zero_r a)
        | intros b b'; exact (mte_add_r a b b')
        | intros r b; exact (rbl_smul_r tensor_gen r a b) ].
Qed.

(*
 Extensionality reaching through a left-nested tensor.  Two applications
 of [tensor_hom_ext]: the outer one peels the outer factor, and the inner
 one is applied to the honest homomorphisms `f ∘ gen_r x` and `g ∘ gen_r x`
 out of V ⊗ W.  No induction. 

 --------
 外延性通过左嵌套张量达到。对 [tensor_hom_ext] 的两次应用：外层应用剥去外层因子，内层应用于来自 V ⊗ W 的真正同态 `f ∘ gen_r x` 和 `g ∘ gen_r x`。没有归纳。
*)
Lemma tensor_hom_ext_l {V W X K : RModObject R}
  (f g : TensorMod (TensorMod V W) X ~{RMod R}~> K) :
  (∀ (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid W))
     (x : carrier (cmon_setoid X)),
     mval f (@mt_gen R (TensorMod V W) X (mt_gen v w) x)
       ≈ mval g (@mt_gen R (TensorMod V W) X (mt_gen v w) x))
  → f ≈ g.
Proof.
  intros H.
  refine (tensor_hom_ext f g _).
  intros s x.
  exact (tensor_hom_ext (f ∘ gen_r x) (g ∘ gen_r x)
           (fun v w => H v w x) s).
Qed.

(* Extensionality reaching through a right-nested tensor. / 通过右嵌套张量实现外延性。 *)
Lemma tensor_hom_ext_r {V W X K : RModObject R}
  (f g : TensorMod V (TensorMod W X) ~{RMod R}~> K) :
  (∀ (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid W))
     (x : carrier (cmon_setoid X)),
     mval f (@mt_gen R V (TensorMod W X) v (mt_gen w x))
       ≈ mval g (@mt_gen R V (TensorMod W X) v (mt_gen w x)))
  → f ≈ g.
Proof.
  intros H.
  refine (tensor_hom_ext f g _).
  intros v t.
  exact (tensor_hom_ext (f ∘ gen_l v) (g ∘ gen_l v)
           (fun w x => H v w x) t).
Qed.

(*
 Extensionality reaching a fourfold left-nested generator: what the
 pentagon needs.  Three applications, still no induction. 

 --------
 扩展性达到四重左嵌套生成器：五边形所需要的。三次应用，仍然没有归纳。
*)
Lemma tensor_hom_ext_ll {V W X Y K : RModObject R}
  (f g : TensorMod (TensorMod (TensorMod V W) X) Y ~{RMod R}~> K) :
  (∀ (a : carrier (cmon_setoid V)) (b : carrier (cmon_setoid W))
     (c : carrier (cmon_setoid X)) (d : carrier (cmon_setoid Y)),
     mval f (@mt_gen R (TensorMod (TensorMod V W) X) Y
               (@mt_gen R (TensorMod V W) X (mt_gen a b) c) d)
       ≈ mval g (@mt_gen R (TensorMod (TensorMod V W) X) Y
                   (@mt_gen R (TensorMod V W) X (mt_gen a b) c) d))
  → f ≈ g.
Proof.
  intros H.
  refine (tensor_hom_ext f g _).
  intros s d.
  refine (tensor_hom_ext (f ∘ gen_r d) (g ∘ gen_r d) _ s).
  intros t c.
  exact (tensor_hom_ext (f ∘ gen_r d ∘ gen_r c) (g ∘ gen_r d ∘ gen_r c)
           (fun a b => H a b c d) t).
Qed.

End GenSlots.

(* Engineering note (a): `apply tensor_hom_ext` does not unify. These are declared at top level because [Ltac] does not survive a [Section]. / 工程说明 (a)：`apply tensor_hom_ext` 不统一。这些在顶层声明是因为 [Ltac] 无法在 [Section] 中存活。 *)
Ltac tens_ext :=
  match goal with |- ?f ≈ ?g => refine (tensor_hom_ext f g _) end.
Ltac tens_ext_l :=
  match goal with |- ?f ≈ ?g => refine (tensor_hom_ext_l f g _) end.
Ltac tens_ext_r :=
  match goal with |- ?f ≈ ?g => refine (tensor_hom_ext_r f g _) end.
Ltac tens_ext_ll :=
  match goal with |- ?f ≈ ?g => refine (tensor_hom_ext_ll f g _) end.

(*
   * ** The tensor bifunctor

   Commutativity-free, and structurally so: this section binds no [Rcomm].
   The arrow action factors the bilinear map (v, w) ↦ f v ⊗ g w through the
   tensor, and all three functor laws are computations on generators. 

   --------
   * **张量双函子

   不涉及交换性，并且在结构上也是如此：本节不绑定任何 [Rcomm]。
   箭头作用通过张量将双线性映射 (v, w) ↦ f v ⊗ g w 分解，并且所有三个函子定律都是在生成元上进行的计算。
*)

Section ModTensorFunctor.

Context {R : RingObject}.

(* The bilinear map (v, w) ↦ f v ⊗ g w. / 双线性映射 (v, w) ↦ f v ⊗ g w。 *)
Program Definition mt_bimap {V V' W W' : RModObject R}
  (f : V ~{RMod R}~> W) (g : V' ~{RMod R}~> W') :
  RBilinear V V' (TensorMod W W') := {|
  rbl_map := fun v w => mt_gen (mval f v) (mval g w)
|}.
Next Obligation.
  intros V V' W W' f g v v' Hv w w' Hw.
  exact (mte_gen (proper_morphism _ _ _ Hv) (proper_morphism _ _ _ Hw)).
Qed.
Next Obligation.
  intros V V' W W' f g v v' w.
  refine (mte_trans (mte_gen (cmon_map_plus (rm_hom f) v v')
                             (reflexivity _)) _).
  exact (mte_add_l _ _ _).
Qed.
Next Obligation.
  intros V V' W W' f g v w w'.
  refine (mte_trans (mte_gen (reflexivity _)
                             (cmon_map_plus (rm_hom g) w w')) _).
  exact (mte_add_r _ _ _).
Qed.
Next Obligation.
  intros V V' W W' f g r v w.
  refine (mte_trans (mte_gen (rm_map_smul f r v) (reflexivity _)) _).
  exact (rbl_smul_l tensor_gen r (mval f v) (mval g w)).
Qed.
Next Obligation.
  intros V V' W W' f g r v w.
  refine (mte_trans (mte_gen (reflexivity _) (rm_map_smul g r w)) _).
  exact (rbl_smul_r tensor_gen r (mval f v) (mval g w)).
Qed.

Definition mt_fmap {V V' W W' : RModObject R}
  (f : V ~{RMod R}~> W) (g : V' ~{RMod R}~> W') :
  TensorMod V V' ~{RMod R}~> TensorMod W W' :=
  tensor_med (mt_bimap f g).

Program Definition ModTensor : RMod R ∏ RMod R ⟶ RMod R := {|
  fobj := fun p => TensorMod (fst p) (snd p);
  fmap := fun p q fg => mt_fmap (fst fg) (snd fg)
|}.
Next Obligation.
  intros [V V'] [W W'] [f g] [f' g'] [Hf Hg].
  refine (tensor_hom_ext (mt_fmap f g) (mt_fmap f' g') _).
  intros v w.
  exact (mte_gen (Hf v) (Hg w)).
Qed.
Next Obligation.
  intros [V V'].
  refine (tensor_hom_ext (mt_fmap id id) id _).
  intros v w.
  exact (mt_refl _).
Qed.
Next Obligation.
  intros [V V'] [W W'] [X X'] [f g] [f' g'].
  refine (tensor_hom_ext (mt_fmap (f ∘ f') (g ∘ g'))
                         (mt_fmap f g ∘ mt_fmap f' g') _).
  intros v w.
  exact (mt_refl _).
Qed.

End ModTensorFunctor.

(*
   * ** The braiding map

   Placed here, before commutativity is ever bound, because the fact is
   worth making structural: the symmetry of ⊗ is a statement about the
   two-variable presentation of the tensor and does not use commutativity
   of R.  Only the [BraidedMonoidal] PACKAGING below needs [Rcomm], and
   only because it contains the monoidal structure. 

   --------
   * ** 编织映射

   放在这里，在交换律被绑定之前，因为这一事实值得被结构化地呈现：⊗ 的对称性是关于张量的双变量表示的声明，并不使用 R 的交换性。下面的 [BraidedMonoidal] 打包唯一需要 [Rcomm]，并且仅仅因为它包含了单体结构。
*)

Section ModBraidMap.

Context {R : RingObject}.

Program Definition braid_bilin (V W : RModObject R) :
  RBilinear V W (TensorMod W V) := {|
  rbl_map := fun a b => mt_gen b a
|}.
Next Obligation.
  intros V W a a' Ha b b' Hb; exact (mte_gen Hb Ha).
Qed.
Next Obligation.
  intros V W a a' b; exact (mte_add_r b a a').
Qed.
Next Obligation.
  intros V W a b b'; exact (mte_add_l b b' a).
Qed.
Next Obligation.
  intros V W r a b; exact (rbl_smul_r tensor_gen r b a).
Qed.
Next Obligation.
  intros V W r a b; exact (rbl_smul_l tensor_gen r b a).
Qed.

Definition ModBraid (V W : RModObject R) :
  TensorMod V W ~{RMod R}~> TensorMod W V :=
  tensor_med (braid_bilin V W).

End ModBraidMap.

(*
   * ** Scaling a homomorphism

   The first of the three places commutativity is spent.  For general R the
   map `m ↦ r · f m` is additive but need not commute with the action; the
   last obligation is `r · (s · v) ≈ s · (r · v)`, and [Rcomm] is what
   supplies it.  The associator needs this because its outer bilinear maps
   state their scalar clauses as equations between HOMOMORPHISMS, which is
   what lets [tensor_hom_ext] reduce them to generators. 

   --------
   * ** 同态的缩放

   这是三个地方中消耗交换性的第一个。对于一般的 R，映射 `m ↦ r · f m` 是可加的，但不一定与作用交换；最后的义务是 `r · (s · v) ≈ s · (r · v)`，而 [Rcomm] 是提供这一义务的。结合子需要这个，因为它的外部双线性映射将它们的标量条款表示为同态之间的方程，这正是使 [tensor_hom_ext] 能将它们化简到生成元的原因。
*)

Section HomSmul.

Context {R : RingObject}.
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
           rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

Program Definition rmod_hom_smul {M N : RModObject R}
  (r : carrier (rig_setoid (ring_rig R))) (f : M ~{RMod R}~> N) :
  M ~{RMod R}~> N := {|
  rm_hom := {| cmon_map := {|
    morphism := fun m => rm_smul N r (mval f m) |} |}
|}.
Next Obligation.
  intros M N r f a b Hab.
  exact (rm_smul_respects N _ _ (reflexivity r) _ _
           (proper_morphism _ _ _ Hab)).
Qed.
Next Obligation.
  intros M N r f; simpl.
  unfold mval.
  rewrite (cmon_map_zero (rm_hom f)).
  exact (rm_smul_zero_r N r).
Qed.
Next Obligation.
  intros M N r f a b; simpl.
  unfold mval.
  rewrite (cmon_map_plus (rm_hom f) a b).
  exact (rm_smul_distr_l N r _ _).
Qed.
(* COMMUTATIVITY, use 1 of 3. / 交换律，使用三者之一。 *)
Next Obligation.
  intros M N r f s m; simpl.
  unfold mval.
  rewrite (rm_map_smul f s m).
  rewrite <- (rm_smul_assoc N r s _).
  rewrite (Rcomm r s).
  exact (rm_smul_assoc N s r _).
Qed.

End HomSmul.

(*
   * ** The unitors

   [ModUnitLeft] factors the action R × V → V through the tensor; its
   inverse sends v to 1 ⊗ v.  One round trip is [rm_smul_one]; the other is
   [tensor_balanced] followed by [rig_mul_one_r].  The other two of the
   three uses of commutativity are here, one in each of the two bilinear
   maps, and each is the clause asserting linearity in the variable the
   action does NOT naturally act on. 

   --------
   * ** 联合体

   [ModUnitLeft]通过张量分解作用 R × V → V;其
   逆映射 v 映射为 1 ⊗ v。一个往返是[rm_smul_one];另一个是
   [tensor_balanced]紧接着是[rig_mul_one_r]。另外两个
   这里交换性有三种用法，分别在两个双线性中各有一个
   映射，每个都是断言变量线性性的子句
   行动不会自然而然地被行动起来。
*)

Section Unitors.

Context {R : RingObject}.
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
           rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

Local Notation Runit := (Ring_RMod R).

(*
 The action R × V → V as a bilinear map.  [rbl_respects] is supplied
 explicitly: see engineering note (d) — left to [Program] it is closed by
 instance resolution and the obligation numbering shifts. 

 --------
 作为双线性映射的作用 R × V → V。[rbl_respects] 明确提供：见工程说明 (d) — 留给 [Program]，它通过实例解析关闭，并且义务编号发生变化。
*)
Program Definition act_bilin (V : RModObject R) :
  RBilinear Runit V V := {|
  rbl_map := fun r v => rm_smul V r v;
  rbl_respects := rm_smul_respects V
|}.
Next Obligation. intros V r r' v; exact (rm_smul_distr_r V r r' v). Qed.
Next Obligation. intros V r v v'; exact (rm_smul_distr_l V r v v'). Qed.
Next Obligation. intros V s r v; exact (rm_smul_assoc V s r v). Qed.
(* COMMUTATIVITY, use 2 of 3. / 交换律，使用三者中的两个。 *)
Next Obligation.
  intros V s r v.
  rewrite <- (rm_smul_assoc V r s v).
  rewrite (Rcomm r s).
  exact (rm_smul_assoc V s r v).
Qed.

Program Definition ModUnitLeft (V : RModObject R) :
  @Isomorphism (RMod R) (TensorMod Runit V) V := {|
  to   := tensor_med (act_bilin V);
  from := @gen_l R Runit V (rig_one (ring_rig R))
|}.
Next Obligation.
  intros V v; simpl; exact (rm_smul_one V v).
Qed.
Next Obligation.
  intros V.
  refine (tensor_hom_ext (@gen_l R Runit V (rig_one (ring_rig R))
                            ∘ tensor_med (act_bilin V)) id _).
  intros r v; simpl.
  refine (mte_trans (mte_sym (@tensor_balanced R Runit V r
                              (rig_one (ring_rig R)) v)) _).
  exact (@mte_gen R Runit V _ _ _ _
           (rig_mul_one_r (ring_rig R) r) (reflexivity v)).
Qed.

Program Definition act_bilin_r (V : RModObject R) :
  RBilinear V Runit V := {|
  rbl_map := fun v r => rm_smul V r v
|}.
Next Obligation.
  intros V v v' Hv r r' Hr.
  exact (rm_smul_respects V _ _ Hr _ _ Hv).
Qed.
Next Obligation. intros V v v' r; exact (rm_smul_distr_l V r v v'). Qed.
Next Obligation. intros V v r r'; exact (rm_smul_distr_r V r r' v). Qed.
(* COMMUTATIVITY, use 3 of 3. / 交换律，使用3中的3。 *)
Next Obligation.
  intros V s v r.
  rewrite <- (rm_smul_assoc V r s v).
  rewrite (Rcomm r s).
  exact (rm_smul_assoc V s r v).
Qed.
Next Obligation. intros V s v r; exact (rm_smul_assoc V s r v). Qed.

Program Definition ModUnitRight (V : RModObject R) :
  @Isomorphism (RMod R) (TensorMod V Runit) V := {|
  to   := tensor_med (act_bilin_r V);
  from := @gen_r R V Runit (rig_one (ring_rig R))
|}.
Next Obligation.
  intros V v; simpl; exact (rm_smul_one V v).
Qed.
Next Obligation.
  intros V.
  refine (tensor_hom_ext (@gen_r R V Runit (rig_one (ring_rig R))
                            ∘ tensor_med (act_bilin_r V)) id _).
  intros v r; simpl.
  refine (mte_trans (@tensor_balanced R V Runit r v
                       (rig_one (ring_rig R))) _).
  exact (@mte_gen R V Runit _ _ _ _
           (reflexivity v) (rig_mul_one_r (ring_rig R) r)).
Qed.

End Unitors.

(*
   * ** The associator: the inner legs

   For a fixed third (resp. first) factor these are ordinary factorizations
   of a bilinear map, and they use no commutativity — hence a section that
   does not bind it.  Only the OUTER bilinear maps, whose scalar clauses are
   equations between homomorphisms, reach for [rmod_hom_smul]. 

   --------
   * ** 关联器：内支腿

   对于固定的第三（或第一）因子，这些是双线性映射的普通分解，并且它们不使用交换性——因此这是一个不约束它的截面。只有外部双线性映射，其标量条款是同态之间的方程，才会涉及 [rmod_hom_smul]。
*)

Section AssociatorLegs.

Context {R : RingObject}.
Context {V W X : RModObject R}.

(* Congruence for the generator former at the two nestings — engineering note (c): without the explicit indices the inner generator elaborates before the outer tensor is known. / 在两个嵌套处生成器前体的一致性 — 工程说明 (c)：没有显式索引时，内部生成器会在外部张量已知之前展开。 *)
Local Notation mgR a b :=
  (@mte_gen R V (TensorMod W X) _ _ _ _ a b).
Local Notation mgL a b :=
  (@mte_gen R (TensorMod V W) X _ _ _ _ a b).

(* For a fixed x, the bilinear map (v, w) ↦ v ⊗ (w ⊗ x). / 对于固定的 x，双线性映射 (v, w) ↦ v ⊗ (w ⊗ x)。 *)
Program Definition assoc_in_bilin (x : carrier (cmon_setoid X)) :
  RBilinear V W (TensorMod V (TensorMod W X)) := {|
  rbl_map := fun v w => mt_gen v (mt_gen w x)
|}.
Next Obligation.
  intros x v v' Hv w w' Hw.
  exact (mgR Hv (mte_gen Hw (reflexivity x))).
Qed.
Next Obligation.
  intros x v v' w; exact (mte_add_l _ _ _).
Qed.
Next Obligation.
  intros x v w w'.
  refine (mte_trans (mgR (reflexivity v) (mte_add_l w w' x)) _).
  exact (mte_add_r _ _ _).
Qed.
Next Obligation.
  intros x r v w.
  exact (rbl_smul_l (@tensor_gen R V (TensorMod W X)) r v (mt_gen w x)).
Qed.
Next Obligation.
  intros x r v w.
  refine (mte_trans (mgR (reflexivity v)
                       (rbl_smul_l tensor_gen r w x)) _).
  exact (rbl_smul_r (@tensor_gen R V (TensorMod W X)) r v (mt_gen w x)).
Qed.

Definition assoc_in (x : carrier (cmon_setoid X)) :
  TensorMod V W ~{RMod R}~> TensorMod V (TensorMod W X) :=
  tensor_med (assoc_in_bilin x).

(* For a fixed v, the bilinear map (w, x) ↦ (v ⊗ w) ⊗ x. / 对于固定的 v，双线性映射 (w, x) ↦ (v ⊗ w) ⊗ x。 *)
Program Definition mod_assoc_fr_in_bilin (v : carrier (cmon_setoid V)) :
  RBilinear W X (TensorMod (TensorMod V W) X) := {|
  rbl_map := fun w x => mt_gen (mt_gen v w) x
|}.
Next Obligation.
  intros v w w' Hw x x' Hx.
  exact (mgL (mte_gen (reflexivity v) Hw) Hx).
Qed.
Next Obligation.
  intros v w w' x.
  refine (mte_trans (mgL (mte_add_r v w w') (reflexivity x)) _).
  exact (mte_add_l _ _ _).
Qed.
Next Obligation.
  intros v w x x'; exact (mte_add_r _ _ _).
Qed.
Next Obligation.
  intros v r w x.
  refine (mte_trans (mgL (rbl_smul_r tensor_gen r v w) (reflexivity x)) _).
  exact (rbl_smul_l (@tensor_gen R (TensorMod V W) X) r (mt_gen v w) x).
Qed.
Next Obligation.
  intros v r w x.
  exact (rbl_smul_r (@tensor_gen R (TensorMod V W) X) r (mt_gen v w) x).
Qed.

Definition mod_assoc_fr_in (v : carrier (cmon_setoid V)) :
  TensorMod W X ~{RMod R}~> TensorMod (TensorMod V W) X :=
  tensor_med (mod_assoc_fr_in_bilin v).

End AssociatorLegs.

(*
   * ** The associator

   Named [mod_assoc_to] / [mod_assoc_fr] because `assoc_to` is taken by
   Construction/Day.v.  Both round trips reduce to generators through
   [tensor_hom_ext_l] and [tensor_hom_ext_r] and close by [mt_refl]: the
   two maps are mutually inverse BY COMPUTATION, not by an equational
   argument. 

   --------
   * ** 联想器

   名为 [mod_assoc_to] / [mod_assoc_fr]，因为 `assoc_to` 已被 Construction/Day.v 占用。两次往返都通过 [tensor_hom_ext_l] 和 [tensor_hom_ext_r] 简化为生成元，并由 [mt_refl] 结束：这两个映射是通过计算相互逆的，而不是通过等式论证。
*)

Section Associator.

Context {R : RingObject}.
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
           rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).
Context {V W X : RModObject R}.

Local Notation mgR a b :=
  (@mte_gen R V (TensorMod W X) _ _ _ _ a b).
Local Notation mgL a b :=
  (@mte_gen R (TensorMod V W) X _ _ _ _ a b).

Program Definition mod_assoc_to_bilin :
  RBilinear (TensorMod V W) X (TensorMod V (TensorMod W X)) := {|
  rbl_map := fun s x => mval (@assoc_in R V W X x) s
|}.
Next Obligation.
  intros s s' Hs x x' Hx.
  transitivity (mval (@assoc_in R V W X x) s').
  - exact (proper_morphism _ _ _ Hs).
  - refine (tensor_hom_ext (@assoc_in R V W X x)
              (@assoc_in R V W X x') _ s').
    intros v w.
    exact (mgR (reflexivity v) (mte_gen (reflexivity w) Hx)).
Qed.
Next Obligation.
  intros s s' x.
  exact (cmon_map_plus (rm_hom (@assoc_in R V W X x)) s s').
Qed.
Next Obligation.
  intros s x x'.
  refine (tensor_hom_ext (@assoc_in R V W X (cmon_plus X x x'))
            (rmod_hom_add (@assoc_in R V W X x)
                          (@assoc_in R V W X x')) _ s).
  intros v w; simpl.
  refine (mte_trans (mgR (reflexivity v) (mte_add_r w x x')) _).
  exact (mte_add_r _ _ _).
Qed.
Next Obligation.
  intros r s x; exact (rm_map_smul (@assoc_in R V W X x) r s).
Qed.
Next Obligation.
  intros r s x.
  refine (tensor_hom_ext (@assoc_in R V W X (rm_smul X r x))
            (rmod_hom_smul Rcomm r (@assoc_in R V W X x)) _ s).
  intros v w; simpl; unfold mval; simpl.
  refine (mte_trans (mgR (reflexivity v)
                       (rbl_smul_r tensor_gen r w x)) _).
  exact (rbl_smul_r (@tensor_gen R V (TensorMod W X)) r v (mt_gen w x)).
Qed.

Definition mod_assoc_to :
  TensorMod (TensorMod V W) X ~{RMod R}~> TensorMod V (TensorMod W X) :=
  tensor_med mod_assoc_to_bilin.

Program Definition mod_assoc_fr_bilin :
  RBilinear V (TensorMod W X) (TensorMod (TensorMod V W) X) := {|
  rbl_map := fun v t => mval (@mod_assoc_fr_in R V W X v) t
|}.
Next Obligation.
  intros v v' Hv t t' Ht.
  transitivity (mval (@mod_assoc_fr_in R V W X v) t').
  - exact (proper_morphism _ _ _ Ht).
  - refine (tensor_hom_ext (@mod_assoc_fr_in R V W X v)
              (@mod_assoc_fr_in R V W X v') _ t').
    intros w x.
    exact (mgL (mte_gen Hv (reflexivity w)) (reflexivity x)).
Qed.
Next Obligation.
  intros v v' t.
  refine (tensor_hom_ext (@mod_assoc_fr_in R V W X (cmon_plus V v v'))
            (rmod_hom_add (@mod_assoc_fr_in R V W X v)
                          (@mod_assoc_fr_in R V W X v')) _ t).
  intros w x; simpl.
  refine (mte_trans (mgL (mte_add_l v v' w) (reflexivity x)) _).
  exact (mte_add_l _ _ _).
Qed.
Next Obligation.
  intros v t t'.
  exact (cmon_map_plus (rm_hom (@mod_assoc_fr_in R V W X v)) t t').
Qed.
Next Obligation.
  intros r v t.
  refine (tensor_hom_ext (@mod_assoc_fr_in R V W X (rm_smul V r v))
            (rmod_hom_smul Rcomm r (@mod_assoc_fr_in R V W X v)) _ t).
  intros w x; simpl; unfold mval; simpl.
  refine (mte_trans (mgL (rbl_smul_l tensor_gen r v w) (reflexivity x)) _).
  exact (rbl_smul_l (@tensor_gen R (TensorMod V W) X) r (mt_gen v w) x).
Qed.
Next Obligation.
  intros r v t; exact (rm_map_smul (@mod_assoc_fr_in R V W X v) r t).
Qed.

Definition mod_assoc_fr :
  TensorMod V (TensorMod W X) ~{RMod R}~> TensorMod (TensorMod V W) X :=
  tensor_med mod_assoc_fr_bilin.

Program Definition ModAssoc :
  @Isomorphism (RMod R) (TensorMod (TensorMod V W) X)
                        (TensorMod V (TensorMod W X)) := {|
  to   := mod_assoc_to;
  from := mod_assoc_fr
|}.
Next Obligation.
  refine (tensor_hom_ext_r (mod_assoc_to ∘ mod_assoc_fr) id _).
  intros v w x; exact (mt_refl _).
Qed.
Next Obligation.
  refine (tensor_hom_ext_l (mod_assoc_fr ∘ mod_assoc_to) id _).
  intros v w x; exact (mt_refl _).
Qed.

End Associator.

(*
   * ** The monoidal structure

   Five of the eight fields close by `simpl; apply mt_refl` — both
   associator naturality squares, both `from`-direction unitor squares, and
   the PENTAGON.  The three that carry content are marked below. 

   --------
   * ** 单位范畴结构

   八个域中有五个由  `simpl; apply mt_refl`  闭合——两个结合子自然性方格、两个  `from`  方向的单位子方格，以及
   五边形方格。下面标出了三个有内容的方格。
*)

Section ModMonoidalStructure.

Context {R : RingObject}.
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
           rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

Program Definition ModMonoidal : @Monoidal (RMod R) := {|
  I            := Ring_RMod R;
  tensor       := ModTensor;
  unit_left    := fun x => ModUnitLeft Rcomm x;
  unit_right   := fun x => ModUnitRight Rcomm x;
  tensor_assoc := fun x y z => ModAssoc Rcomm
|}.
(* CONTENT 1 of 3: [to_unit_left_natural], one [rm_map_smul]. / 内容 1 共 3：[to_unit_left_natural]，一个 [rm_map_smul]。 *)
Next Obligation.
  intros x y g; tens_ext; intros r a; simpl.
  exact (rm_map_smul g r a).
Qed.
Next Obligation.
  intros x y g a; simpl; apply mt_refl.
Qed.
(* CONTENT 2 of 3: [to_unit_right_natural], one [rm_map_smul]. / 内容 2 的 3：[to_unit_right_natural]，一个 [rm_map_smul]。 *)
Next Obligation.
  intros x y g; tens_ext; intros a r; simpl.
  exact (rm_map_smul g r a).
Qed.
Next Obligation.
  intros x y g a; simpl; apply mt_refl.
Qed.
Next Obligation.
  intros x y z w v u g h i; tens_ext_l; intros a b c; simpl; apply mt_refl.
Qed.
Next Obligation.
  intros x y z w v u g h i; tens_ext_r; intros a b c; simpl; apply mt_refl.
Qed.
(*
 CONTENT 3 of 3: [triangle_identity], one [tensor_balanced].  This is the
 one place the two unitors must agree about which factor absorbs a
 scalar, and it is NOT definitional — see [probe_balanced_conversion]. 

 --------
 内容 3 的 3：[triangle_identity]，一个 [tensor_balanced]。 这是两个单元必须就哪个因子吸收标量达成一致的唯一地方，而且这不是定义性的——参见 [probe_balanced_conversion]。
*)
Next Obligation.
  intros x y; tens_ext_l; intros a r b; simpl.
  exact (tensor_balanced r a b).
Qed.
(* THE PENTAGON, definitional once the fourfold generator is exposed. / 五角大楼，一旦四重生成器被揭露，就具有定义性。 *)
Next Obligation.
  intros x y z w; tens_ext_ll; intros a b c d; simpl; apply mt_refl.
Qed.

End ModMonoidalStructure.

(*
   * ** Braided and symmetric

   Every field here is [mt_refl]: braid naturality, both hexagons and the
   involution are computations on generators.  [Rcomm] enters only through
   the contained monoidal structure — [ModBraid] itself, built above, takes
   no commutativity argument. 

   --------
   * ** 编织和对称

   这里的每个域都是 [mt_refl]：编织自然性，六边形和自反映都是基于生成元的计算。[Rcomm] 仅通过所包含的幺半群结构进入 —— [ModBraid] 本身，在上面构建的，不需要交换性参数。
*)

Section ModBraiding.

Context {R : RingObject}.
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
           rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

Program Definition ModBraided : @BraidedMonoidal (RMod R) := {|
  braided_is_monoidal := ModMonoidal Rcomm;
  braid               := ModBraid
|}.
Next Obligation.
  intros x y g z w h; tens_ext; intros a b; simpl; apply mt_refl.
Qed.
Next Obligation.
  intros x y z; tens_ext_l; intros a b c; simpl; apply mt_refl.
Qed.
Next Obligation.
  intros x y z; tens_ext_r; intros a b c; simpl; apply mt_refl.
Qed.

Program Definition ModSymmetric : @SymmetricMonoidal (RMod R) := {|
  symmetric_is_braided := ModBraided
|}.
Next Obligation.
  intros x y; tens_ext; intros a b; simpl; apply mt_refl.
Qed.

End ModBraiding.

(* * ** Acceptance tests over ℤ ℤ is a commutative ring (Instance/Rng.v's [Int_Ring_commutative]), so the whole structure is inhabited at a concrete base. Every example below closes by [eq_refl]: these are computations, not equational arguments. / * ** 关于 ℤ 的验收测试 ℤ 是一个交换环（Instance/Rng.v 中的 [Int_Ring_commutative]），所以整个结构在一个具体基础下是可用的。下面的每一个例子都以 [eq_refl] 结束：这些是计算，而不是方程论证。 *)

Definition Int_Mod_Monoidal : @Monoidal (RMod Int_Ring) :=
  ModMonoidal Int_Ring_commutative.

Definition Int_Mod_Braided : @BraidedMonoidal (RMod Int_Ring) :=
  ModBraided Int_Ring_commutative.

Definition Int_Mod_Symmetric : @SymmetricMonoidal (RMod Int_Ring) :=
  ModSymmetric Int_Ring_commutative.

Definition ZMod : RModObject Int_Ring := Ring_RMod Int_Ring.

Definition zz2 : carrier (cmon_setoid ZMod) := 2%Z.
Definition zz3 : carrier (cmon_setoid ZMod) := 3%Z.
Definition zz5 : carrier (cmon_setoid ZMod) := 5%Z.
Definition zz7 : carrier (cmon_setoid ZMod) := 7%Z.

(* The unit object is ℤ as a module over itself, on the nose. / 单位对象是 ℤ，作为其自身的模，完全如此。 *)
Example mod_unit_is_Ring_RMod :
  @I (RMod Int_Ring) Int_Mod_Monoidal = Ring_RMod Int_Ring := eq_refl.

(* The tensor bifunctor's object action is [TensorMod], on the nose. / 张量双函子的对象作用就是 [TensorMod]，正是如此。 *)
Example mod_tensor_is_TensorMod :
  fobj[@tensor (RMod Int_Ring) Int_Mod_Monoidal] (ZMod, ZMod)
    = TensorMod ZMod ZMod := eq_refl.

(* The associator computes on a concrete generator. / 关联器在具体生成器上进行计算。 *)
Example mod_assoc_computes :
  mval (@mod_assoc_to Int_Ring Int_Ring_commutative ZMod ZMod ZMod)
       (@mt_gen Int_Ring (TensorMod ZMod ZMod) ZMod
          (@mt_gen Int_Ring ZMod ZMod zz2 zz3) zz5)
  = @mt_gen Int_Ring ZMod (TensorMod ZMod ZMod) zz2 (mt_gen zz3 zz5)
  := eq_refl.

(* The left unitor computes: 2 ⊗ 7 ↦ 2 * 7 = 14. / 左单元器计算：2 ⊗ 7 ↦ 2 * 7 = 14。 *)
Example mod_unit_left_computes :
  mval (to (ModUnitLeft Int_Ring_commutative ZMod))
       (@mt_gen Int_Ring ZMod ZMod zz2 zz7) = 14%Z := eq_refl.

(* The braiding computes. / 编织正在计算。 *)
Example mod_braid_computes :
  mval (@ModBraid Int_Ring ZMod ZMod) (@mt_gen Int_Ring ZMod ZMod zz2 zz3)
  = @mt_gen Int_Ring ZMod ZMod zz3 zz2 := eq_refl.

(* The fourfold generator ((2 ⊗ 3) ⊗ 5) ⊗ 7, the pentagon's input. / 四重生成器 ((2 ⊗ 3) ⊗ 5) ⊗ 7，五边形的输入。 *)
Definition zquad :
  carrier (cmon_setoid
    (TensorMod (TensorMod (TensorMod ZMod ZMod) ZMod) ZMod)) :=
  @mt_gen Int_Ring (TensorMod (TensorMod ZMod ZMod) ZMod) ZMod
    (@mt_gen Int_Ring (TensorMod ZMod ZMod) ZMod
       (@mt_gen Int_Ring ZMod ZMod zz2 zz3) zz5) zz7.

(*
 THE PENTAGON, as a computation.  Both routes around it carry the fourfold
 generator to the very same [MTerm]; this is the header's central claim,
 checked rather than asserted. 

 --------
 五角大楼，作为一种计算。环绕它的两条路线都将四重生成器带到完全相同的 [MTerm]；这是标题的核心声明，是经过验证的，而不是简单主张的。
*)
Example mod_pentagon_computes :
  mval (mt_fmap (@id (RMod Int_Ring) ZMod)
          (@mod_assoc_to Int_Ring Int_Ring_commutative ZMod ZMod ZMod)
        ∘ @mod_assoc_to Int_Ring Int_Ring_commutative
            ZMod (TensorMod ZMod ZMod) ZMod
        ∘ mt_fmap (@mod_assoc_to Int_Ring Int_Ring_commutative
                     ZMod ZMod ZMod) (@id (RMod Int_Ring) ZMod)) zquad
  = mval (@mod_assoc_to Int_Ring Int_Ring_commutative
            ZMod ZMod (TensorMod ZMod ZMod)
        ∘ @mod_assoc_to Int_Ring Int_Ring_commutative
            (TensorMod ZMod ZMod) ZMod ZMod) zquad
  := eq_refl.

(* And the common value is the fully right-nested generator. / 而常见的值是完全右嵌套的生成器。 *)
Example mod_pentagon_value :
  mval (@mod_assoc_to Int_Ring Int_Ring_commutative
          ZMod ZMod (TensorMod ZMod ZMod)
      ∘ @mod_assoc_to Int_Ring Int_Ring_commutative
          (TensorMod ZMod ZMod) ZMod ZMod) zquad
  = @mt_gen Int_Ring ZMod (TensorMod ZMod (TensorMod ZMod ZMod))
      zz2 (@mt_gen Int_Ring ZMod (TensorMod ZMod ZMod)
             zz3 (@mt_gen Int_Ring ZMod ZMod zz5 zz7))
  := eq_refl.

(*
   * ** Probes

   Under this repo's [coqc] a [Fail] that succeeds prints NOTHING, so each
   negative below was stripped of its [Fail], compiled alone, and its
   failure kind read off the WHOLE error message before being recorded here.
   Four kinds occur and they are genuinely distinguishable by the error
   text, not merely by label:

   TYPING       — "has type … while it is expected to have type …",
   with no further clause
   CONVERSION   — the same, closing with "(cannot unify … and …)"
   RESOLUTION   — "contains unresolved implicit arguments … Cannot infer
   this placeholder"
   FORMABILITY  — "(universe inconsistency: Cannot enforce … because …)"

   They are kept lexically apart below.  Every negative sits beside an
   APPLIED control that must succeed — never a bare [Check] of an
   unapplied constant, which would elaborate at any levels and discriminate
   nothing — so a rename or a signature change breaks this section loudly
   instead of turning a guard vacuously green. 

   --------
   * ** 探针

   在这个仓库的 [coqc] 下，一个成功的 [Fail] 什么也不打印，因此下面每个负例都去掉了它的 [Fail]，单独编译，并从完整的错误信息中读取其失败类型，然后记录在这里。
   出现四种类型，它们可以通过错误文本真实区分，而不仅仅是标签：

   TYPING       — “具有类型 … 而预期类型为 …”，没有其他附加说明
   CONVERSION   — 相同，结尾为“(无法统一 … 和 …)”
   RESOLUTION   — “包含未解析的隐式参数 … 无法推断此占位符”
   FORMABILITY  — “(宇宙不一致：无法强制 … 因为 …)”它们在下面在词汇上被分开。每个否定都紧挨着一个必须成功的已应用控件——决不会是一个裸露的未应用常量的 [Check]，它会在任何层次展开而不区分任何内容——因此重命名或更改签名会大声地破坏这一部分，而不是使守卫徒然变绿。
*)

(*
 Instrument check: the [Fail] mechanism is live and scope-free in this
 file.  If this ever stops failing, every negative below is worthless.
 Named for this file rather than [probe_instrument], which
 Test/ProbePolynomial.v already declares — the collision hazard
 engineering note (f) records. 

 --------
 仪器检查：[Fail] 机制在此文件中是活动的并且无范围。如果它停止失败，下面的所有负面都毫无意义。命名为此文件而不是 [probe_instrument]，Test/ProbePolynomial.v 已经声明 — 碰撞风险工程说明 (f) 已记录。
*)
Fail Example mod_monoidal_instrument : (true = false) := eq_refl.

(*
   * *** TYPING negatives

   Three, of two subjects.  The first two are where commutativity is a real
   argument: [ModUnitLeft] and [mod_assoc_to] take [Rcomm] explicitly while
   [gen_r], [gen_l], [ModBraid], [ModTensor], [assoc_in] and
   [mod_assoc_fr_in] do not, so feeding the module where the hypothesis is
   expected is rejected.  That is the signature-level form of the header's
   claim about where commutativity is spent, and it is what makes the claim
   a measurement rather than a reading of the source.  The third is
   engineering note (c), the nested-generator annotation trap. 

   --------
   * *** 打字的否定

   三，关于两个主题的。前两个是交换性确实是一个争论点的地方：[ModUnitLeft] 和 [mod_assoc_to] 明确接受 [Rcomm]，而 [gen_r]、[gen_l]、[ModBraid]、[ModTensor]、[assoc_in] 和 [mod_assoc_fr_in] 不接受，因此在模块期望假设的地方提供输入会被拒绝。这就是标题中关于交换性应用位置的声明在签名级别的形式，它使得该声明成为一种测量，而不是对源代码的读取。第三个是工程说明(c)，嵌套生成器注解陷阱。
*)

(* Supplying the module where [Rcomm] is expected. / 提供预期的模块 [Rcomm]。 *)
Fail Check (@ModUnitLeft Int_Ring ZMod).

(* Control: the same application with [Rcomm] in place. / 控制：相同的应用程序，[Rcomm] 替代原位。 *)
Check (@ModUnitLeft Int_Ring Int_Ring_commutative ZMod).

Fail Check (@mod_assoc_to Int_Ring ZMod ZMod ZMod).

Check (@mod_assoc_to Int_Ring Int_Ring_commutative ZMod ZMod ZMod).

(*
 Engineering note (c), pinned: a nested [mt_gen] with its module arguments
 left implicit is rejected — the inner generator elaborates first and a
 bare [MTerm] does not unify with `carrier ?V`.  This is why every nested
 generator in this file is `@`-annotated. 

 --------
 工程说明 (c)，固定：一个嵌套的 [mt_gen]，其模块参数未显式给出，因此被拒绝 —— 内部生成器首先展开，而一个裸的 [MTerm] 无法与 `carrier ?V` 统一。这就是为什么本文件中的每个嵌套生成器都带有 `@` 注释的原因。
*)
Fail Check (mt_gen (@mt_gen Int_Ring ZMod ZMod zz2 zz3) zz5).

(* Control: the same term with the outer indices supplied. / 控制：提供了相同外部指标的术语。 *)
Check (@mt_gen Int_Ring (TensorMod ZMod ZMod) ZMod
         (@mt_gen Int_Ring ZMod ZMod zz2 zz3) zz5).

(* Controls on the commutativity-FREE side: these are complete applications with no [Rcomm] anywhere, at the same ring. / 对交换性无约束的一侧的控制：这些是完整的应用，在同一环上没有任何 [Rcomm]。 *)
Check (@gen_r Int_Ring ZMod ZMod zz3).
Check (@gen_l Int_Ring ZMod ZMod zz3).
Check (@ModBraid Int_Ring ZMod ZMod).
Check (@ModTensor Int_Ring).
Check (@assoc_in Int_Ring ZMod ZMod ZMod zz5).
Check (@mod_assoc_fr_in Int_Ring ZMod ZMod ZMod zz2).

(*
   * *** CONVERSION negatives — the three content-bearing obligations

   Five of [ModMonoidal]'s eight fields close by conversion.  These pin that
   the other three do not: each of the three facts they consume is refuted
   at [eq_refl] and holds only up to `≈`. 

   --------
   * *** 转换否定——三个承载内容的义务

   [ModMonoidal] 的八个字段中有五个通过转换而关闭。这些指出其他三个字段没有关闭：它们消耗的每一个事实在 [eq_refl] 被否定，并且仅在 `≈` 之前有效。
*)

(*
 [triangle_identity]'s content, [tensor_balanced].  Even at closed integer
 scalars the two sides are literally different terms — `6 ⊗ 5` against
 `3 ⊗ 10` — so the triangle is not a computation. 

 --------
 [triangle_identity] 的内容，[tensor_balanced]。即使在闭合整数标量下，双方也是字面上不同的项——`6 ⊗ 5` 对比 `3 ⊗ 10`——所以三角形不是一个计算。
*)
Fail Example probe_balanced_conversion :
  @mt_gen Int_Ring ZMod ZMod (rm_smul ZMod 2%Z zz3) zz5
    = @mt_gen Int_Ring ZMod ZMod zz3 (rm_smul ZMod 2%Z zz5)
  := eq_refl.

(*
 Control: the same statement at `≈`, which is [tensor_balanced].  The
 ascription is needed because [TensorMod]'s setoid is a projection rather
 than a registered instance, so `≈` on a bare [MTerm] has nothing to
 resolve against. 

 --------
 控制：在 `≈` 的相同语句，即 [tensor_balanced]。需要归属是因为 [TensorMod] 的集合体是一个投影，而不是注册实例，所以在裸露的 [MTerm] 上的 `≈` 无法有任何可用于解析的对象。
*)
Example probe_balanced_equiv :
  (@mt_gen Int_Ring ZMod ZMod (rm_smul ZMod 2%Z zz3) zz5
     : carrier (cmon_setoid (TensorMod ZMod ZMod)))
    ≈ @mt_gen Int_Ring ZMod ZMod zz3 (rm_smul ZMod 2%Z zz5).
Proof. exact (@tensor_balanced Int_Ring ZMod ZMod 2%Z zz3 zz5). Qed.

(* Control, sharpening the diagnosis: the two sides ARE distinct terms, the left one reducing to `6 ⊗ 5` and the right to `3 ⊗ 10`. / 控制，明确诊断：两边是不同的术语，左边简化为 `6 ⊗ 5`，右边简化为 `3 ⊗ 10`。 *)
Example probe_balanced_lhs :
  @mt_gen Int_Ring ZMod ZMod (rm_smul ZMod 2%Z zz3) zz5
    = @mt_gen Int_Ring ZMod ZMod 6%Z zz5 := eq_refl.

Example probe_balanced_rhs :
  @mt_gen Int_Ring ZMod ZMod zz3 (rm_smul ZMod 2%Z zz5)
    = @mt_gen Int_Ring ZMod ZMod zz3 10%Z := eq_refl.

(*
 The two [to_unit_*_natural] fields' content, [rm_map_smul]: a module
 homomorphism commutes with the action.  For an arbitrary [g] this is a
 proof field of the record, not a computation. 

 --------
 两个 [to_unit_*_natural] 字段的内容，[rm_map_smul]：一个模块同态与作用交换。对于任意 [g]，这是记录的证明字段，而不是计算。
*)
Fail Example probe_map_smul_conversion
  {V W : RModObject Int_Ring} (g : V ~{RMod Int_Ring}~> W)
  (r : carrier (rig_setoid (ring_rig Int_Ring)))
  (a : carrier (cmon_setoid V)) :
  mval g (rm_smul V r a) = rm_smul W r (mval g a) := eq_refl.

(* Control: the same statement at `≈`, which is [rm_map_smul]. / 控制：在 `≈` 的同一语句，即 [rm_map_smul]。 *)
Example probe_map_smul_equiv
  {V W : RModObject Int_Ring} (g : V ~{RMod Int_Ring}~> W)
  (r : carrier (rig_setoid (ring_rig Int_Ring)))
  (a : carrier (cmon_setoid V)) :
  mval g (rm_smul V r a) ≈ rm_smul W r (mval g a).
Proof. exact (rm_map_smul g r a). Qed.

(*
 Control: the SAME shape at a concrete [g], where it does reduce.  This is
 what makes the negative above about arbitrary morphisms rather than about
 the shape of the statement. 

 --------
 控制：在具体的 [g] 上相同的形状，在那里它确实会减少。这就是使上面的负面结论关于任意态射而不是关于陈述的形状的原因。
*)
Example probe_map_smul_concrete
  (r : carrier (rig_setoid (ring_rig Int_Ring)))
  (a : carrier (cmon_setoid ZMod)) :
  mval (@id (RMod Int_Ring) ZMod) (rm_smul ZMod r a)
    = rm_smul ZMod r (mval (@id (RMod Int_Ring) ZMod) a) := eq_refl.

(*
   * *** RESOLUTION negative — [Rcomm] is not found by inference

   Engineering note (e): the structures are [Program Definition]s and not
   [Instance]s, so nothing supplies the commutativity hypothesis
   automatically.  This pins that leaving it to be inferred fails at an
   abstract ring, where no commutativity is in scope.  Its error text names
   an unresolved placeholder and contains neither "cannot unify" nor
   "universe inconsistency", which is what separates it from the two
   groups above and the one below. 

   --------
   * *** 消解 负 — [Rcomm] 通过推理未被找到

   工程注释 (e)：结构是 [Program Definition] 而不是 [Instance]，因此没有任何东西自动提供交换律假设。
   这表明将其留给推理会在抽象环中失败，在该环中没有交换性。其错误文本标明了一个未解决的占位符，并且不包含“无法合并”或“宇宙不一致”，这也是它与上面两组及下面一组的区别所在。
*)

Section ResolutionProbe.

Context {R : RingObject}.

Fail Definition probe_no_resolution : @Monoidal (RMod R) := ModMonoidal _.

(* Control: with the hypothesis in hand the very same body elaborates. / 控制：手握假设，同一实体进行阐述。 *)
Definition probe_with_hypothesis
  (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
      rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a) :
  @Monoidal (RMod R) := ModMonoidal Rcomm.

(* Control: the commutativity-free half needs nothing at all, at the same abstract ring. / 控制：无需交换性的半部分根本不需要任何东西，在同一个抽象环上。 *)
Definition probe_tensor_free : RMod R ∏ RMod R ⟶ RMod R := ModTensor.

End ResolutionProbe.

(*
   * *** FORMABILITY negatives — the packaging identifies two universes

   The measurement the header records.  Under a declared `rp < ru` — which
   satisfies the bound every component carries while violating the equation
   the assembly carries — [ModMonoidal] and [ModSymmetric] are rejected with
   a genuine universe inconsistency, while ELEVEN applied controls elaborate
   at exactly those levels, and two more show the same two constants
   accepted at ℤ.  Two of the controls are the obvious suspects:
   [@Monoidal (RMod Ru)], the class being assembled, and [Ring_RMod Ru], the
   unit object it is assembled with.  Two more, [ModUnitLeft] and
   [ModAssoc], are commutativity-CONSUMING, so the rejection is not about
   [Rcomm] either.  What is left is the packaging. 

   --------
   * *** 可成形性缺点——包装识别出两个宇宙

   标头记录的测量值。在声明的 `rp < ru` 下——它满足每个组件携带的界限，同时违反组件装配携带的方程——[ModMonoidal] 和 [ModSymmetric] 被以真正的宇宙不一致性拒绝，而 ELEVEN 应用的控制正好在这些水平上进行了详细说明，还有两个显示出相同的两个常数在 ℤ 上被接受。两个控制是显而易见的嫌疑对象：[@Monoidal (RMod Ru)]，正在组装的类，以及 [Ring_RMod Ru]，它被组装的单元对象。还有两个，[ModUnitLeft] 和 [ModAssoc]，是耗费交换性的，所以拒绝也不是关于 [Rcomm]。剩下的就是包装。
*)

Section UniverseProbe.

Universes ru rp rq.
Constraint rp < ru.

Context (Ru : RingObject@{ru rp rq}).

(* Controls: the ambient category, the unit object, and the class itself. / 控制：环境类别、单位对象以及类本身。 *)
Check (RMod Ru).
Check (Ring_RMod Ru).
Check (@Monoidal (RMod Ru)).

(* Controls: every commutativity-free component. / 控制：每个无交换性的组件。 *)
Check (@ModTensor Ru).
Check (@gen_r Ru).
Check (@gen_l Ru).
Check (@ModBraid Ru).

(* Controls: every commutativity-consuming component. / 控制：每个消耗交换性的组件。 *)
Check (@rmod_hom_smul Ru).
Check (@ModUnitLeft Ru).
Check (@ModUnitRight Ru).
Check (@ModAssoc Ru).

(* The assembly, and the symmetric structure that contains it. / 组件，以及包含它的对称结构。 *)
Fail Check (@ModMonoidal Ru).

Fail Check (@ModSymmetric Ru).

(*
 Controls, sharpest form: the very same two constants, applied at ℤ, whose
 three [RingObject] universes may be identified.  So the rejection above is
 about the levels and not about the constants. 

 --------
 控制，最尖锐的形式：完全相同的两个常数，应用于 ℤ，其三个 [RingObject] 宇宙可以被识别。所以上面的拒绝是关于层次的，而不是关于常数的。
*)
Check (ModMonoidal Int_Ring_commutative).
Check (ModSymmetric Int_Ring_commutative).

End UniverseProbe.
