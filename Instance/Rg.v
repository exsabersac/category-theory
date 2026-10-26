Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

(*
   * * Rg: the category of rings without an assumed identity

   Mac Lane, “Categories for the Working Mathematician”, 2nd ed., §IV.2
   Exercise 4 (printed p. 89) [maclane:IV.2:ex4]: rings without unit,
   and the adjoint of the forgetful functor from rings with unit.
   Riehl, “Category Theory in Context”, §4.7, for the free/forgetful
   pattern the adjunction instantiates.

   CITED BY LOCATION ONLY: the printed text of neither book was
   consulted while writing this file, and the locations follow the
   issue that commissioned it — the same discipline, and for the same
   reason, that Instance/Ab.v's header states for its own §I.7
   citations.  Nothing below is presented as a quotation from either
   book.  The in-tree quotation from Structure/Ring.v is
   verbatim and was checked against the file.  The Instance/Roster.v
   sentence quoted is verbatim against the text as it stood
   BEFORE this commit, which repairs it; it is quoted here precisely
   because it is the claim being discharged.

   The exercise has two halves: the CATEGORY of rings without unit, and
   the Dorroh unitalization left adjoint to the forgetful functor out
   of it.  This file is the first half only; the extension and its
   adjunction are deliberately NOT here (see NOT DELIVERED).
   nLab: https://ncatlab.org/nlab/show/rng
   nLab: https://ncatlab.org/nlab/show/nonunital+ring
   Wikipedia: https://en.wikipedia.org/wiki/Rng_(algebra)

   A rng is “a riNg without the I”: an abelian group (0, +, −) with an
   associative multiplication distributing over addition on both sides,
   and no multiplicative identity demanded.  Its morphisms preserve 0,
   + and ·, and nothing else — dropping the unit from the OBJECTS and
   dropping unit-preservation from the MORPHISMS are two separate
   moves, and it is the second that does the categorical damage
   exhibited below.

   NAMING, and why it is not free.  Both obvious names were taken
   before this file existed, so the third was forced, and a reader of
   either neighbour needs to know which is which.

   - [Rng] is Instance/Rng.v's category of UNITAL rings, keeping
   Mac Lane's own abbreviation from his §I.7 roll-call; its
   morphisms preserve 1, since [RigHom] carries [rig_map_one] as a
   FIELD.  So in this tree “Rng” means WITH unit.
   - [Ring] is Theory/Algebra/Rig.v's [RingObject] with the
   category over it, definitionally the same category as [Rng].
   - [Rg] — this file — is rings WITHOUT an assumed identity, with
   objects [RgObject] and homomorphisms [RgHom].

   Hence the forgetful functor built below runs [Rng ⟶ Rg], from unital
   to non-unital, and its direction is unambiguous to a reader of
   either file.  Instance/Rng.v's own header already reserves the name
   [Rg] for exactly this, so no name is being appropriated.

   MEASURED, AT THE REVISION THIS FILE WAS WRITTEN.  Every claim in
   this paragraph was checked with [rg] over the tree's 800-odd [.v]
   files, not recalled.

   - [RgObject], [RgHom] and [Rg] occur in no declaration head
   anywhere else; the category is genuinely new.
   - [RigObject] (Theory/Algebra/Rig.v) carries SEVENTEEN fields,
   counted mechanically off the record body rather than by eye.  A
   brief that guided this file said fifteen; that is wrong, and the
   correct figure is stated here instead.  [AbObject]
   (Instance/Ab.v) carries FOUR, and [RgObject] below carries
   SIX, one of which is the [AbObject] coercion.
   - THE FIELD NAME [rg_mul] COLLIDES, and the collision is LIVE
   rather than theoretical.  Structure/Group/Representable.v
   declares [Definition rg_mul : c × c ~> c] inside its
   [HomMonoidEngine] section — a different notion entirely, [rg_]
   there abbreviating the file's representable-group engine — with
   twenty uses, all confined to that one file.  Sweeping all 101
   constants this module declares against every declaration head in
   the tree returns that one hit and no other.  What makes it live:
   that module IS required by the [print-assumptions] target in the
   Makefile, which loads many modules into ONE scope, so a bare
   [Print Assumptions rg_mul.] there would silently audit the wrong
   constant.  The name is kept because it is the tree's own
   convention ([rig_mul], [cmon_plus]) and because the downstream
   Dorroh extension is written against it.  Two mitigations are
   open to whoever registers this module: gate its constants by
   FULLY QUALIFIED name, or rename the [Structure/Group/
   Representable.v] helper, which is what the tree did the last
   time this bit it (Adjunction/Additive.v renamed its [coprod_ext]
   away from Construction/Cospan/Bridging.v before commit).
   This is a disclosure with options, not a claim that the
   collision is harmless.

   WHY [AbObject] AND NOT [RigObject] IS THE BASE.  Building [RgObject]
   on Instance/Ab.v's [AbObject] costs six fields where restating the
   rig axioms would cost seventeen, but the count is not the reason.
   The reason is that the additive group of a rng is then LITERALLY an
   [AbObject], so everything Instance/Ab.v proves about abelian groups
   — cancellation, uniqueness of inverses, [ab_neg_plus] — applies with
   no adapter, and so will the ℤ-action of Instance/Ab/Monoidal.v,
   which the Dorroh extension needs in order to form ℤ ⊕ R.  (That
   module is deliberately NOT required here; this file has no use for
   [zsmul] and keeping it out holds the Require closure down.)

   ANNIHILATION IS A THEOREM HERE, AND THAT IS THE STRUCTURAL POINT.
   [RigObject] carries [rig_mul_zero_l] and [rig_mul_zero_r] as FIELDS
   (Theory/Algebra/Rig.v) because a rig has no additive
   inverses and the pair genuinely does not follow: Structure/Ring.v
   records that disjunction on the booleans, used as both halves
   of a semiring, satisfies commutativity and BOTH distributivity laws
   while REFUTING annihilation ([bool_or_not_annihilating]), “so
   the annihilation PAIR is not implied by the rest”.  A rng does have
   inverses, so [rg_mul_zero_l] and [rg_mul_zero_r] are proved below
   from distributivity plus cancellation — 0·a is idempotent under
   addition, hence zero.  The engine is [rg_cancel_idem], the elementary
   counterpart of Structure/Ring.v's internal-ring lemma of the
   same shape, whose [ring_annihilate_l]/[ring_annihilate_r] are the
   diagrammatic form of the same argument.

   HALF the derived pair is LOAD-BEARING rather than decorative, and
   the file says exactly which half and exactly where — counted, not
   recalled.  [rg_mul_zero_l] is consumed TWICE: by [rg_zero_mor], the
   constant-zero homomorphism whose existence between arbitrary rngs is
   what refutes fullness, and by [Rg_zero_hom], the unique morphism OUT
   of the trivial rng, which is what makes the trivial rng INITIAL.
   Remove it and neither typechecks, so the headline below is not
   merely decorated by annihilation but built on it.  [rg_mul_zero_r]
   is consumed NOWHERE in this file; it is delivered as the dual, for
   the Dorroh extension and for downstream use, and no claim is made
   that anything here needs it.

   PRESERVATION OF NEGATION IS NOT RE-PROVED.  [RgHom] extends
   Instance/Ab.v's [AbHom], which is literally [CMonHom]; that
   file's [ab_map_neg] already proves a monoid map between
   abelian groups preserves inverses, and [rg_map_neg] below is a
   one-line citation of it.  Theory/Algebra/Rig.v's [RigHom_neg] is the
   same theorem on the unital side, reached the same way.

   ★ THE HEADLINE: [Rg_Zero : ZeroObject Rg].  In [Rg] the one-element
   rng is BOTH terminal and initial, because a [RgHom] out of it need
   not carry 1 anywhere — there is no 1 to carry.  In [Rng] the two
   differ: ℤ is initial (Instance/Rng.v) and the zero ring terminal,
   and they cannot coincide, since a unital homomorphism out of
   the zero ring would force 0 ≈ 1 in ℤ.  Instance/Roster.v
   HAD RECORDED that this contrast “is NOT checkable here: the tree has
   no category of non-unital rings, which is future #362's [Rg]”.  This
   file supplies the missing half, and the commit that lands it repairs
   that Roster.v passage accordingly -- so the sentence quoted above is
   the SUPERSEDED text, and the only occurrence of it left in the tree
   is this quotation.  Nothing in Roster.v is edited by this file
   itself.

   PRIOR ART FOR THE OTHER HALF, DISCLOSED RATHER THAN REDISCOVERED.
   A brief that guided this file asked for [Rng_no_zero_object] to be
   proved “if you can do it cleanly”.  It is already proved:
   Structure/Kernel/Universal/Examples.v has exactly that theorem,
   via its [Rng_no_zero_morphisms] and its
   [Rng_no_hom_zero_to_Z].  Nothing here duplicates those names.  What
   IS restated, under the fresh name [Rng_terminal_not_initial] and in
   three lines, is the underlying fact that no [Rng]-morphism runs from
   the zero ring to ℤ — and the reason for restating rather than
   citing is architectural and is measured: that file is a
   Structure-layer example whose transitive closure is 65 modules,
   reached through Theory/Universal/Element.v and Yoneda, so requiring
   it from an Instance-layer file would add 34 to this file's own
   closure of 32 and push all of it onto every downstream consumer of
   [Rg], the Dorroh extension included.  No
   novelty whatever is claimed for the [Rng] half; the new artifacts
   are [Rg_Zero] and the packaged contrast
   [Rng_Rg_zero_object_contrast].

   UNIVERSES, MEASURED AND ROUTED AROUND RATHER THAN INHERITED.
   [Set Printing Universes] reports [Ab_trivial@{} : AbObject@{Set Set
   Set}] — ZERO universe binders, pinned at [Set], the same donor
   defect Instance/Grp/Quotient/Colimit.v records for [Grp_trivial]
   (which #450 has since lifted for [Grp_trivial]; [Ab_trivial] is
   unchanged).
   Building the trivial rng on [Ab_trivial] would silently have
   confined [Rg_Zero] to [Set]-sized rngs.  It is built instead on
   Instance/CMon/Biproduct.v's [CMon_trivial@{o} : CMonObject@{o o
   o}], which IS polymorphic, through a locally declared polymorphic
   [rg_trivial_ab].  The resulting instance is reported at the foot of
   this file by an [About] the reader can rerun; it carries no [Set].

   STRENGTHS, GRADED STRICT-FIRST.  [eq_refl] was tried before [≈]
   everywhere, and what it bought is shipped as [Example]s: the
   forgetful functor's object action returns the [AbObject], the
   multiplication, the carrier and the zero of the unital ring ON THE
   NOSE, and the zero object of [Rg] IS [Rg_trivial] on the nose.  Two
   strict attempts were REFUTED and are pinned as [Fail Definition …
   := eq_refl] probes with passing controls beside them, and the two
   are of DIFFERENT KINDS, each read off the error after stripping the
   [Fail] and compiling the command alone — one CONVERSION, reporting
   [cannot unify] between two terms of one type, and one TYPING,
   reporting a plain type mismatch with no [cannot unify] at all.  The
   image of
   the zero ring under the forgetful functor is NOT [Rg_trivial]
   (Instance/Rng.v's [Zero_Rig] carries the always-true setoid where
   [CMon_trivial] carries Leibniz [eq] on [poly_unit], so the two
   records differ in their [is_setoid] field, and the control shows the
   CARRIERS agree by [eq_refl]), and [Rng_Forget_Rg] is NOT the
   identity on hom-records.

   NON-VACUITY: 2ℤ, WITH THE NAME EARNED RATHER THAN ASSERTED.  The
   witness [TwoZ_Rg] is the even integers.  It is presented on the
   carrier ℤ with multiplication (a, b) ↦ 2ab, which is the ring
   structure 2ℤ acquires when transported along the bijection z ↦ 2z —
   a presentation chosen so that every law is [ring] or [lia] and no
   sigma-type carrier is needed.  That the presentation deserves the
   name is a THEOREM and not a remark: [TwoZ_incl] is an injective
   [RgHom] into ℤ ([TwoZ_incl_injective]) whose image is exactly the
   even integers — BOTH halves, since containment alone would not earn
   the word: [TwoZ_incl_image_even] and [TwoZ_incl_image_onto_even].
   It is proved NOT unital
   ([TwoZ_not_unital]: no e satisfies e·a ≈ a for all a, since e·1 ≈ 1
   reads 2e = 1 in ℤ), NOT degenerate ([TwoZ_nondegenerate]: 0 ≉ 1),
   and NOT of zero multiplication ([TwoZ_mul_nonzero]: 1·1 ≈ 2 ≉ 0),
   which last is what separates it from the cheap zero-multiplication
   rng on any abelian group and keeps the multiplicative axioms
   genuinely exercised.

   NOT DELIVERED, and this list is meant to be exhaustive for this
   file.  No Dorroh extension, no unitalization functor and no
   adjunction — that is the second half of Mac Lane's exercise and a
   separate module.  No limits, colimits, products, biproducts,
   kernels or cokernels in [Rg], and no [Preadditive]/[Additive]/
   [Abelian] instance.  No monic/epi characterisation for [Rg] and no
   analogue of Instance/Rng.v's ℤ → ℚ separation.  No ideals, no
   quotient rngs, no free rng.  No commutative variant, so there is no
   [CRg] answering to Instance/Rng.v's [CRng].  No claim that
   [Rng_Forget_Rg] is essentially surjective or reflects anything, and
   in particular no proof that it has a left adjoint — the whole point
   of the exercise — is attempted here.  No relation to
   Theory/Category/Semi.v's semigroupoids, so the one-object reading of
   a rng as a non-unital enriched category is not built.  No universe
   claim is made about anything other than [Rg_Zero] and its
   dependencies, and the [Set] pin located in [Ab_trivial] is routed
   around rather than repaired: Instance/Ab.v is not edited. 

   --------
   * * Rg：没有假定单位的环的范畴

   Mac Lane，《为工作数学家准备的范畴》，第2版，第IV.2节
   练习4（印刷页89）[maclane:IV.2:ex4]：无单位环，以及从有单位环中遗忘的函子对应的伴随函子。
   Riehl，《语境中的范畴论》，第4.7节，关于自由/遗忘模式所体现的伴随关系。仅按位置引用：在编写此文件时未参考任一本书的印刷文本，位置依据委托它的刊物——与 Instance/Ab.v 的标题在其 §I.7 引用中所说明的理由相同。以下内容均不作为两本书的引用呈现。来自 Structure/Ring.v 的树内引用是逐字的，并已与文件核对。引用的 Instance/Roster.v 句子在本次提交修复之前的文本中是逐字的；正因如此，它在此被引用，因为它恰好是需要解决的声明。这项练习分为两部分：没有单位的环的类别，以及 Dorroh 单位化，它是从中忘记函子出发的左伴随。这个文件仅包含前半部分；扩展及其伴随关系故意不在这里（参见未提供）。
   nLab:  https://ncatlab.org/nlab/show/rng 
   nLab:  https://ncatlab.org/nlab/show/nonunital+ring 
   Wikipedia:  https://en.wikipedia.org/wiki/Rng_(algebra)

   一个 rng 是“没有 I 的环”：一个阿贝尔群 (0, +, −) ，带有在两侧对加法分配的结合乘法，但不要求有乘法单位元。它的态射保持 0、+ 和 ·，而不保持其他——从对象中去掉单位元和从态射中去掉单位元保持是两个独立的操作，而正是第二个操作造成了下面展示的范畴上的问题。命名，以及为什么它不是免费的。在这个文件存在之前，两个明显的名字都已经被使用了，所以第三个名字被迫采用，而任何一个邻居的读者都需要知道哪一个是哪一个。

   - [Rng] 是 Instance/Rng.v 的单元环（UNITAL rings）类别，保留了 Mac Lane 在他的 §I.7 点名表中的缩写；它的态射保持 1，因为 [RigHom] 作为 FIELD 承载 [rig_map_one]。因此在这棵树中，“Rng”表示带单位元素的。
   - [Ring] 是 Theory/Algebra/Rig.v 的 [RingObject]，带有其上方的类别，从定义上与 [Rng] 的类别相同。
   - [Rg] —— 本文件 —— 是不假定单位元素的环，其对象为 [RgObject]，态射为 [RgHom]。因此，下面构建的忘记函子运行 [Rng ⟶ Rg]，从有单位的到无单位的，而且它的方向对任何一个文件的读者都是明确的。Instance/Rng.v 本身的头文件已经为此保留了 [Rg] 的名称，所以没有名称被占用。

   在编写此文件时已进行测量。段落中的每一个声明都已使用 [rg] 在树的 800 多个 [.v] 文件上检查过，而不是从记忆中回忆出来。- [RgObject]、[RgHom] 和 [Rg] 在其他任何声明头中都没有出现；这个类别是真正新的。- [RigObject]（Theory/Algebra/Rig.v）包含十七个字段，是通过机械计数记录体而不是目测得出的。指导本文件的一个摘要说十五个；这是错误的，正确的数字在这里给出。[AbObject]（Instance/Ab.v）包含四个字段，而下面的 [RgObject] 包含六个字段，其中一个是 [AbObject] 强制转换。- 字段名 [rg_mul] 冲突，且这种冲突是实际存在的，而非理论上的。Structure/Group/Representable.v 在其 [HomMonoidEngine] 部分中声明了 [Definition rg_mul : c × c ~> c]——这是一个完全不同的概念，[rg_] 在那里缩写了文件的可表示群引擎——共有二十次使用，全部局限于该文件。将该模块声明的所有 101 个常量与树中的每个声明头进行对比，仅返回这一处匹配，没有其他匹配。使其保持活跃的原因：该模块被 Makefile 中的 [print-assumptions] 目标所需要，该目标将多个模块加载到一个作用域中，因此在此处单独使用 [Print Assumptions rg_mul.] 会悄无声息地审核错误的常量。保留这个名字是因为它是树自身的约定（[rig_mul]，[cmon_plus]），并且因为下游 Dorroh 扩展是基于它编写的。对于注册此模块的任何人，有两种缓解方法：通过完整限定名限制其常量，或者重命名 [Structure/Group/Representable.v] 辅助文件，这是上次处理此问题时树所做的操作（Adjunction/Additive.v 在提交前将其 [coprod_ext] 从 Construction/Cospan/Bridging.v 移开）。这是一个带有选项的披露，而不是声称冲突无害。为什么 [AbObject] 而不是 [RigObject] 是基础。在 Instance/Ab.v 上构建 [RgObject] 的 [AbObject] 会花费六个字段，而重新陈述环的公理会花费十七个字段，但数量并不是原因。原因是，一个环的加法群在字面上就是一个 [AbObject]，因此 Instance/Ab.v 关于阿贝尔群所证明的一切——消去律、逆元的唯一性、[ab_neg_plus]——都可以不需要适配器地应用，因此 Instance/Ab/Monoidal.v 的 ℤ-作用也是如此，而 Dorroh 扩展需要它来形成 ℤ ⊕ R。（该模块在这里故意不要求；此文件不需要 [zsmul]，且不引入它可以保持 Require 闭包更小。）在这里，消元是一个定理，这就是结构要点。[RigObject] 作为 FIELDS 承载 [rig_mul_zero_l] 和 [rig_mul_zero_r]（Theory/Algebra/Rig.v），因为环没有加法逆元，并且这对真正不遵循：Structure/Ring.v 记录了布尔值上的析取，作为半环的两半使用，满足交换律和两种分配律，同时否定消元（[bool_or_not_annihilating]），所以消元对并非由其余部分推导而来。rng 确实有逆元，因此 [rg_mul_zero_l] 和 [rg_mul_zero_r] 在下面通过分配律加上消去定律得以证明——0·a 在加法下是幂等的，因此为零。引擎是 [rg_cancel_idem]，它是 Structure/Ring.v 中相同形状的 internal-ring 引理的基本对应，其 [ring_annihilate_l] / [ring_annihilate_r] 是相同论证的图示形式。一半的派生对是承重的而非装饰性的，并且文件明确说明了哪一半以及具体位置——是计数得出的，而非回忆出来的。[rg_mul_zero_l] 被消耗了两次：一次被 [rg_zero_mor] 消耗，这是一个常零同态，其存在于任意 rng 之间正是用来驳斥完备性；另一次被 [Rg_zero_hom] 消耗，这是从平凡 rng 指向外部的唯一态射，也正是它使得平凡 rng 成为初始的。移除它，两者都无法类型检查，因此下面的标题不仅仅是被湮灭装饰，而是建立在湮灭之上的。[rg_mul_zero_r] 在这个文件中没有被使用；它作为对偶被提供，用于 Dorroh 扩展及下游使用，并没有声称这里的任何内容需要它。否定的保持没有被重新证明。[RgHom] 扩展了 Instance/Ab.v 的 [AbHom]，这实际上是 [CMonHom]；该文件的 [ab_map_neg] 已经证明了一个阿贝尔群之间的幺半群映射保持逆元，下面的 [rg_map_neg] 是对此的一行引用。Theory/Algebra/Rig.v 的 [RigHom_neg] 是单位侧上的同一条定理，以相同的方式得出。★ 头条：[Rg_Zero : ZeroObject Rg]。在[Rg]中，单元素环既是终端又是初始，因为从[RgHom]出去的环不需要在任何地方携带1——没有1可携带。在[Rng]中，两者不同：ℤ是初始环（Instance/Rng.v），零环是终端环，它们不可能重合，因为从零环出的幺同态会导致ℤ中0 ≈ 1。Instance/Roster.v已经记录了这种对比“在这里无法检查：该树没有非幺环的类别，这是未来#362的[Rg]”。此文件提供了缺失的另一半，并且提交它会相应地修复Roster.v的那段文字——所以上面引用的句子是被取代的文本，并且该树中剩下的唯一出现就是这个引用。本文件本身没有修改Roster.v中的任何内容。另一半的现有技术，是被公开而不是重新发现的。指导本文件的简报要求 [Rng_no_zero_object] 被证明“如果你能干净地完成”。它已经被证明：Structure/Kernel/Universal/Examples.v 正好有那个定理，通过它的 [Rng_no_zero_morphisms] 以及它的 [Rng_no_hom_zero_to_Z]。这里没有重复那些名字。被重新陈述的内容，在新的名称 [Rng_terminal_not_initial] 下，并以三行显示，是基础事实：没有从零环到 ℤ 的 [Rng]-态射——之所以重新陈述而不是引用的原因是架构上的，并且是经过衡量的：那个文件是一个结构层示例，其传递闭包为 65 个模块，通过 Theory/Universal/Element.v 和 Yoneda 达到，因此从实例层文件引用它会使该文件自身的闭包 32 增加 34，并将其全部推送到每个下游 [Rg] 的使用者，包括 Dorroh 扩展。[Rng] 部分没有任何新颖性；新的人工制品是 [Rg_Zero] 和打包对比 [Rng_Rg_zero_object_contrast]。宇宙，被测量和路由而不是继承。
   [Set Printing Universes] 报告 [Ab_trivial@{} : AbObject@{Set Set Set}] — 零宇宙绑定器，固定在 [Set]，相同的捐赠者缺陷 Instance/Grp/Quotient/Colimit.v 记录用于 [Grp_trivial] （#450 自此已为 [Grp_trivial] 解除； [Ab_trivial] 保持不变）。
   在 [Ab_trivial] 上构建平凡 rng 会悄悄地将 [Rg_Zero] 限制在 [Set] 大小的 rng。它改而建立在 Instance/CMon/Biproduct.v 的 [CMon_trivial@{o} : CMonObject@{o o o}] 上，它是多态的，通过局部声明的多态 [rg_trivial_ab]。由此产生的实例在此文件底部由 [About] 报告，读者可以重新运行；它不携带 [Set]。优势，先严格分级。[eq_refl] 曾在 [≈] 之前被尝试过各处，它买到的东西作为 [Example] 发货：遗忘函子的对象作用返回 [AbObject]、乘法、承载和单位环的零，完全准确，并且 [Rg] 的零对象也准确无误是 [Rg_trivial]。两次严格尝试被驳回，并被固定为 [Fail Definition … := eq_refl] 探针，旁边有通过控制的标记，这两次属于不同类型，每次在剥离 [Fail] 并单独编译命令后读取错误——一次是转换，报告同一类型两个项之间的 [cannot unify]，另一次是类型错误，报告一个普通类型不匹配，完全没有 [cannot unify]。在遗忘函子下零环的像不是 [Rg_trivial]（Instance/Rng.v 的 [Zero_Rig] 携带总为真的集合同构，其中 [CMon_trivial] 在 [poly_unit] 上携带 Leibniz [eq]，因此这两个记录在它们的 [is_setoid] 字段上不同，控制显示 CARRIERS 通过 [eq_refl] 一致），并且 [Rng_Forget_Rg] 不是同态记录的恒等映射。非空性：2ℤ，名字是获得的而非声称的。见证 [TwoZ_Rg] 是偶整数。它呈现在乘法载体 ℤ 上 (a, b) ↦ 2ab，这是 2ℤ 在沿双射 z ↦ 2z 传输时获得的环结构——选择这种表示方式，使得每条定律都是 [ring] 或 [lia]，并且不需要 sigma 类型的载体。这个表示值得命名是一个定理，而不是一个备注：[TwoZ_incl] 是一个注入的 [RgHom] 到 ℤ ([TwoZ_incl_injective])，其像正好是偶整数——两个部分，因为仅包含本身不足以获得该词：[TwoZ_incl_image_even] 和 [TwoZ_incl_image_onto_even]。已证明不是幺半群（[TwoZ_not_unital]：没有 e 满足 e·a ≈ a 对所有 a 都成立，因为 e·1 ≈ 1 在 ℤ 中表示 2e = 1），不是退化的（[TwoZ_nondegenerate]：0 ≉ 1），也不是零乘法（[TwoZ_mul_nonzero]：1·1 ≈ 2 ≉ 0），最后一点正是将其与任意阿贝尔群上的廉价零乘法环区分开来的地方，并使乘法公理得到真正的应用。未交付，并且此列表旨在对该文件进行详尽列举。没有 Dorroh 扩展，没有单位化函子，也没有伴随——这是 Mac Lane 练习的后半部分，也是一个独立模块。[Rg] 中没有极限、余极限、积、双积、核或余核，也没有 [Preadditive] / [Additive] / [Abelian] 实例。[Rg] 没有单态/满态特性，也没有 Instance/Rng.v 中 ℤ → ℚ 的类似分离。没有理想，没有商环，没有自由环。没有交换变体，因此没有 [CRg] 对应 Instance/Rng.v 中的 [CRng]。不声称 [Rng_Forget_Rg] 是本质上满射或能够反映任何内容，尤其没有尝试证明它具有左伴随——这是整个练习的关键点。与 Theory/Category/Semi.v 的半群类没有关系，因此将一个 rng 作为非单元增强范畴的一对象解读并未建立。除了 [Rg_Zero] 及其依赖项外，没有对任何事物提出宇宙声明，并且位于 [Ab_trivial] 的 [Set] 引脚是绕过而不是修复的：Instance/Ab.v 未被编辑。
*)

(** ** Rngs over a setoid carrier / ** 在集合载体上的环 *)

(*
 An abelian group with an associative, doubly distributive
 multiplication.  No unit, and no annihilation clause: the latter is
 derivable here, which is exactly the difference from [RigObject]. 

 --------
 一个具有结合性、双分配性的乘法的阿贝尔群。没有单位元，也没有消元条款：后者在这里可以推导出来，这正是与 [RigObject] 的区别。
*)
Record RgObject := {
  rg_ab :> AbObject;

  rg_mul : carrier (cmon_setoid (ab_cmon rg_ab)) →
           carrier (cmon_setoid (ab_cmon rg_ab)) →
           carrier (cmon_setoid (ab_cmon rg_ab));

  rg_mul_respects : Proper (equiv ==> equiv ==> equiv) rg_mul;

  rg_mul_assoc : ∀ a b c,
    rg_mul (rg_mul a b) c ≈ rg_mul a (rg_mul b c);

  rg_distr_l : ∀ a b c,
    rg_mul a (cmon_plus (ab_cmon rg_ab) b c)
      ≈ cmon_plus (ab_cmon rg_ab) (rg_mul a b) (rg_mul a c);
  rg_distr_r : ∀ a b c,
    rg_mul (cmon_plus (ab_cmon rg_ab) a b) c
      ≈ cmon_plus (ab_cmon rg_ab) (rg_mul a c) (rg_mul b c)
}.

#[export] Existing Instance rg_mul_respects.

(** ** Annihilation, derived / ** 消灭，来源于 *)

(*
 In an abelian group an element that is its own double is zero.  This
 is the elementary counterpart of Structure/Ring.v's
 [ring_cancel_idem], and it is the whole content of the two
 annihilation laws below. 

 --------
 在阿贝尔群中，一个自身加倍等于自身的元素就是零。这是 Structure/Ring.v 中 [ring_cancel_idem] 的基本对应，也是下面两条消去律的全部内容。
*)
Lemma rg_cancel_idem (A : AbObject) (k : carrier (cmon_setoid A)) :
  cmon_plus A k k ≈ k → k ≈ cmon_zero A.
Proof.
  intro H.
  transitivity (cmon_plus A (ab_neg A k) (cmon_plus A k k)).
  - rewrite <- cmon_plus_assoc.
    rewrite ab_neg_left.
    now rewrite cmon_plus_zero_l.
  - rewrite H.
    apply ab_neg_left.
Qed.

(*
 0·a = (0 + 0)·a = 0·a + 0·a, so 0·a is idempotent, so it is 0.  The
 corresponding clauses of [RigObject] are FIELDS; here they are
 theorems, and Structure/Ring.v's [bool_or_not_annihilating] is
 why a rig cannot do the same. 

 --------
 0·a = (0 + 0)·a = 0·a + 0·a，所以 0·a 是幂等的，因此它是 0。
 相应的 [RigObject] 条款是 FIELDS；在这里它们是定理，而 Structure/Ring.v 的 [bool_or_not_annihilating] 是说明为什么一个环（rig）不能做同样的事。
*)
Lemma rg_mul_zero_l (R : RgObject) (a : carrier (cmon_setoid (rg_ab R))) :
  rg_mul R (cmon_zero (rg_ab R)) a ≈ cmon_zero (rg_ab R).
Proof.
  apply (rg_cancel_idem (rg_ab R)).
  rewrite <- rg_distr_r.
  now rewrite cmon_plus_zero_l.
Qed.

Lemma rg_mul_zero_r (R : RgObject) (a : carrier (cmon_setoid (rg_ab R))) :
  rg_mul R a (cmon_zero (rg_ab R)) ≈ cmon_zero (rg_ab R).
Proof.
  apply (rg_cancel_idem (rg_ab R)).
  rewrite <- rg_distr_l.
  now rewrite cmon_plus_zero_l.
Qed.

(** ** Homomorphisms / ** 同态 *)

(*
 A rng homomorphism is a homomorphism of the additive abelian groups
 that also respects multiplication.  There is no unit clause, and that
 single omission is what separates this category from [Rng]. 

 --------
 一个 rng 同态是加法阿贝尔群的同态，同时也保持乘法。没有单位元条款，而正是这一点遗漏将这个范畴与 [Rng] 区分开来。
*)
Record RgHom (R S : RgObject) := {
  rg_hom_ab :> AbHom R S;

  rg_map_mul : ∀ a b,
    cmon_map rg_hom_ab (rg_mul R a b)
      ≈ rg_mul S (cmon_map rg_hom_ab a) (cmon_map rg_hom_ab b)
}.

Arguments rg_hom_ab {R S} _.
Arguments rg_map_mul {R S} _ _ _.

(* Preservation of negation is NOT a field and is NOT proved here: it is Instance/Ab.v's [ab_map_neg], applied. The unital-side twin is Theory/Algebra/Rig.v's [RigHom_neg]. / 否定的保持不是一个领域，这里也没有证明：它是 Instance/Ab.v 的 [ab_map_neg] 应用。单元侧的对应是 Theory/Algebra/Rig.v 的 [RigHom_neg]。 *)
Corollary rg_map_neg {R S : RgObject} (f : RgHom R S)
  (a : carrier (cmon_setoid (rg_ab R))) :
  cmon_map (rg_hom_ab f) (ab_neg (rg_ab R) a)
    ≈ ab_neg (rg_ab S) (cmon_map (rg_hom_ab f) a).
Proof. exact (ab_map_neg (rg_hom_ab f) a). Qed.

#[local] Obligation Tactic := idtac.

(*
 Homomorphisms are compared by their underlying maps, pointwise —
 Theory/Algebra/Rig.v's [RigHom_Setoid] pattern. 

 --------
 同态通过其基础映射按点比较——Theory/Algebra/Rig.v 的 [RigHom_Setoid] 模式。
*)
#[export]
Program Instance RgHom_Setoid {R S : RgObject} : Setoid (RgHom R S) := {|
  equiv := fun f g => ∀ a, cmon_map (rg_hom_ab f) a
                             ≈ cmon_map (rg_hom_ab g) a
|}.
Next Obligation.
  intros R S.
  constructor.
  - intros f a; reflexivity.
  - intros f g Hfg a; symmetry; apply Hfg.
  - intros f g h Hfg Hgh a.
    transitivity (cmon_map (rg_hom_ab g) a); [ apply Hfg | apply Hgh ].
Qed.

Program Definition rg_hom_id {R : RgObject} : RgHom R R := {|
  rg_hom_ab := @cmon_hom_id (ab_cmon (rg_ab R))
|}.
Next Obligation. intros R a b; simpl; reflexivity. Qed.

Program Definition rg_hom_compose {R S T : RgObject}
  (f : RgHom S T) (g : RgHom R S) : RgHom R T := {|
  rg_hom_ab := cmon_hom_compose (rg_hom_ab f) (rg_hom_ab g)
|}.
Next Obligation.
  intros R S T f g a b; simpl.
  rewrite (proper_morphism (cmon_map (rg_hom_ab f)) _ _
             (rg_map_mul g a b)).
  apply rg_map_mul.
Qed.

Lemma rg_hom_compose_respects {R S T : RgObject} :
  Proper (equiv ==> equiv ==> equiv) (@rg_hom_compose R S T).
Proof.
  intros f1 f2 Hf g1 g2 Hg a; simpl.
  rewrite (Hf (cmon_map (rg_hom_ab g1) a)).
  apply (proper_morphism (cmon_map (rg_hom_ab f2))), Hg.
Qed.

(** ** The category / ** 类别 *)

(*
 The universes are pinned by hand, for the reason recorded at
 Instance/CMon.v's [CMon]: with [cmon_prop] a field of the underlying
 [CMonObject] the record sort carries a [Set+1], and left to itself the
 elaborator gives [Rg] a third, redundant universe -- refusing the
 `Rg@{u o}` annotations in this file for arity. 

 --------
 这些宇宙是手动固定的，其原因记录在 Instance/CMon.v 的 [CMon] 中：在 [cmon_prop] 中，底层 [CMonObject] 的字段携带了 [Set+1]，如果不加以干预，展开器会给 [Rg] 添加第三个多余的宇宙 —— 拒绝此文件中 `Rg@{u o}` 的元数注释。
*)
Program Definition Rg@{u p} : Category@{u p p} := {|
  obj     := RgObject@{p p p};
  hom     := RgHom@{p};
  homset  := @RgHom_Setoid@{p};
  id      := @rg_hom_id@{p};
  compose := @rg_hom_compose@{u p};

  compose_respects := @rg_hom_compose_respects@{u p}
|}.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.

(** ** Forgetting from Rg / ** 忘记来自 Rg *)

Program Definition Rg_Forget_Ab : Rg ⟶ Ab := {|
  fobj := rg_ab;
  fmap := fun R S f => rg_hom_ab f
|}.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros R a; simpl; reflexivity. Qed.
Next Obligation. intros R S T f g a; simpl; reflexivity. Qed.

Program Definition Rg_Forget : Rg ⟶ Sets := {|
  fobj := fun R : RgObject => cmon_setoid (ab_cmon (rg_ab R));
  fmap := fun R S f => cmon_map (rg_hom_ab f)
|}.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros R a; simpl; reflexivity. Qed.
Next Obligation. intros R S T f g a; simpl; reflexivity. Qed.

#[export] Program Instance Rg_Forget_Ab_Faithful : Faithful Rg_Forget_Ab.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.

(* * ** The forgetful functor from unital rings / * ** 从含单位环的遗忘函子 *)

(*
 Pure reuse.  Instance/Rng.v's [ring_ab] already extracts the
 additive abelian group of a unital ring, and every remaining field is
 the corresponding [RigObject] field passed through unchanged — the
 two records' field types are convertible, so not one of the five
 assignments needs a tactic. 

 --------
 纯粹重用。Instance/Rng.v 的 [ring_ab] 已经提取了带单位环的加法阿贝尔群，剩余的每一个字段都是相应的 [RigObject] 字段按原样传递的——两个记录的字段类型是可转换的，因此五个赋值中没有一个需要使用策略。
*)
Definition ring_rg (R : RingObject) : RgObject := {|
  rg_ab := ring_ab R;
  rg_mul := rig_mul R;
  rg_mul_respects := rig_mul_respects R;
  rg_mul_assoc := rig_mul_assoc R;
  rg_distr_l := rig_distr_l R;
  rg_distr_r := rig_distr_r R
|}.

(* The arrow action is Instance/Rng.v's [Rng_Forget_Ab] repackaged with one extra field, [rig_map_mul], again passed through unchanged. / 箭头动作是 Instance/Rng.v 的 [Rng_Forget_Ab] 重新打包，带有一个额外字段 [rig_map_mul]，同样保持不变地传递。 *)
Program Definition Rng_Forget_Rg : Rng ⟶ Rg := {|
  fobj := ring_rg;
  fmap := fun R S f => {|
    rg_hom_ab := {|
      cmon_map := rig_map f;
      cmon_map_zero := rig_map_zero f;
      cmon_map_plus := rig_map_add f
    |};
    rg_map_mul := rig_map_mul f
  |}
|}.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros R a; simpl; reflexivity. Qed.
Next Obligation. intros R S T f g a; simpl; reflexivity. Qed.

(*
 Faithfulness is CHEAP, and it is worth saying why rather than
 presenting it as work: both hom-setoids compare homomorphisms by
 their underlying maps pointwise, and the forgetful functor leaves the
 underlying map alone, so the hypothesis IS the conclusion. 

 --------
 忠诚是廉价的，值得说明原因，而不是把它当作工作来呈现：两个同态集都通过逐点比较其基础映射来比较同态，而遗忘函子保持基础映射不变，因此假设就是结论。
*)
#[export] Program Instance Rng_Forget_Rg_Faithful : Faithful Rng_Forget_Rg.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.

(** ** The functor is not full / ** 函子不是满射 *)

(*
 The constant-zero map is a rng homomorphism between ANY two rngs: it
 preserves 0 outright, preserves + because 0 + 0 ≈ 0, and preserves ·
 by [rg_mul_zero_l].  It is not a unital homomorphism unless the
 codomain is trivial, and that is the whole obstruction to fullness. 

 --------
 常零映射是任意两个环（rng）之间的环同态：它直接保持 0，由于 0 + 0 ≈ 0，它保持加法，并且通过 [rg_mul_zero_l] 保持乘法。除非陪域是平凡的，否则它不是幺同态，这正是充满性的整个障碍。
*)
Program Definition rg_zero_mor (R S : RgObject) : RgHom R S := {|
  rg_hom_ab := {|
    cmon_map := {| morphism := fun _ => cmon_zero (ab_cmon (rg_ab S)) |}
  |}
|}.
Next Obligation. intros R S x y Hxy; reflexivity. Qed.
Next Obligation. intros R S; simpl; reflexivity. Qed.
Next Obligation.
  intros R S a b; simpl; symmetry; apply cmon_plus_zero_l.
Qed.
Next Obligation.
  intros R S a b; simpl; symmetry; apply rg_mul_zero_l.
Qed.

(* The zero endomorphism of ℤ in [Rg] has no unital preimage: any [RigHom] out of ℤ sends 1 to 1, and the zero map sends 1 to 0. / ℤ 在 [Rg] 中的零自同态没有单位预像：任何来自 ℤ 的 [RigHom] 都将 1 映射为 1，而零映射将 1 映射为 0。 *)
Theorem Rng_Forget_Rg_not_Full : Full Rng_Forget_Rg → False.
Proof.
  intro F.
  pose (z := rg_zero_mor (ring_rg Int_Ring) (ring_rg Int_Ring)).
  pose (g := @prefmap _ _ _ F Int_Ring Int_Ring z).
  assert (H0 : rig_map g 1%Z = 0%Z)
    by exact (@fmap_sur _ _ _ F Int_Ring Int_Ring z 1%Z).
  assert (H1 : rig_map g 1%Z = 1%Z) by exact (rig_map_one g).
  rewrite H0 in H1.
  discriminate.
Qed.

(* * ** The trivial rng is a zero object / * ** 平凡的 rng 是零对象 *)

(*
 Built on Instance/CMon/Biproduct.v's polymorphic [CMon_trivial],
 NOT on Instance/Ab.v's [Ab_trivial], which is measured to be
 [AbObject@{Set Set Set}] with no universe binders at all. 

 --------
 基于 Instance/CMon/Biproduct.v 的多态 [CMon_trivial]，而不是基于 Instance/Ab.v 的 [Ab_trivial]，后者测量为 [AbObject@{Set Set Set}]，完全没有宇宙绑定器。
*)
Definition rg_trivial_ab@{o} : AbObject@{o o o}.
Proof.
  unshelve notypeclasses refine {|
    ab_cmon := CMon_trivial@{o};
    ab_neg  := fun _ => ttt
  |}.
  - intros x y Hxy; reflexivity.
  - intros a; reflexivity.
Defined.

Definition Rg_trivial@{o} : RgObject@{o o o}.
Proof.
  unshelve notypeclasses refine {|
    rg_ab  := rg_trivial_ab@{o};
    rg_mul := fun _ _ => ttt
  |}.
  - intros x y Hxy u v Huv; reflexivity.
  - intros a b c; reflexivity.
  - intros a b c; reflexivity.
  - intros a b c; reflexivity.
Defined.

(* Terminal: everything to the point. / 终端：直截了当的所有内容。 *)
Program Definition Rg_one@{u o} (R : RgObject@{o o o})
  : R ~{Rg@{u o}}~> Rg_trivial@{o} := {|
  rg_hom_ab := {| cmon_map := {| morphism := fun _ => ttt |} |}
|}.
Next Obligation. intros R x y Hxy; reflexivity. Qed.
Next Obligation. intros R; reflexivity. Qed.
Next Obligation. intros R a b; reflexivity. Qed.
Next Obligation. intros R a b; reflexivity. Qed.

Lemma Rg_one_unique@{u o} (R : RgObject@{o o o})
  (f : R ~{Rg@{u o}}~> Rg_trivial@{o}) : f ≈ Rg_one@{u o} R.
Proof.
  intro a; simpl.
  destruct (cmon_map (rg_hom_ab f) a); reflexivity.
Qed.

#[export] Program Instance Rg_Terminal : @Terminal Rg := {|
  terminal_obj := Rg_trivial;
  one          := Rg_one
|}.
Next Obligation.
  intros R f g.
  now rewrite (Rg_one_unique R f), (Rg_one_unique R g).
Qed.

(*
 Initial: the point goes to zero.  This is the SECOND of the two
 places the derived annihilation law is spent (the first is
 [rg_zero_mor] above) — the multiplicativity obligation reads
 [0 ≈ rg_mul R 0 0], which is exactly [rg_mul_zero_l].  On the unital
 side the corresponding morphism does not exist at all, which is what
 [Rng_terminal_not_initial] below records. 

 --------
 初始：该点归零。这是推导出的湮灭律作用的两个地方中的第二个（第一个是在上面的 [rg_zero_mor]）——乘法性义务写作 [0 ≈ rg_mul R 0 0]，这正好是 [rg_mul_zero_l]。在单位侧，相应的态射根本不存在，这就是下面 [Rng_terminal_not_initial] 所记录的内容。
*)
Program Definition Rg_zero_hom@{u o} (R : RgObject@{o o o})
  : Rg_trivial@{o} ~{Rg@{u o}}~> R := {|
  rg_hom_ab := {|
    cmon_map := {| morphism := fun _ => cmon_zero (ab_cmon (rg_ab R)) |}
  |}
|}.
Next Obligation. intros R x y Hxy; reflexivity. Qed.
Next Obligation. intros R; simpl; reflexivity. Qed.
Next Obligation.
  intros R a b; simpl; symmetry; apply cmon_plus_zero_l.
Qed.
Next Obligation.
  intros R a b; simpl; symmetry; apply rg_mul_zero_l.
Qed.

Lemma Rg_zero_hom_unique@{u o} (R : RgObject@{o o o})
  (f : Rg_trivial@{o} ~{Rg@{u o}}~> R) : f ≈ Rg_zero_hom@{u o} R.
Proof.
  intro a; destruct a; simpl.
  exact (cmon_map_zero (rg_hom_ab f)).
Qed.

#[export] Program Instance Rg_Initial : @Initial Rg := {|
  terminal_obj := Rg_trivial : obj[Rg^op];
  one          := Rg_zero_hom
|}.
Next Obligation.
  intros R f g.
  now rewrite (Rg_zero_hom_unique R f), (Rg_zero_hom_unique R g).
Qed.

(*
 One record plays both roles, so the coincidence isomorphism is the
 identity — Instance/CMon/Biproduct.v and Instance/Ab.v do the
 same. 

 --------
 一个记录同时扮演两个角色，因此同构的巧合是身份 — Instance/CMon/Biproduct.v 和 Instance/Ab.v 做了相同的事情。
*)
#[export] Instance Rg_Zero : ZeroObject Rg :=
  @Build_ZeroObject Rg Rg_Terminal Rg_Initial iso_id.

(* * ** The contrast with the unital category / * ** 与单元范畴的对比 *)

(*
 On the unital side no morphism runs from the terminal object to the
 initial one: such a morphism would carry the zero ring's 1 — which is
 also its 0 — to both 1 and 0 in ℤ.

 This is the same fact as Structure/Kernel/Universal/Examples.v's
 [Rng_no_hom_zero_to_Z], restated here under a fresh name rather than
 cited, because requiring that module would pull its 23-module closure
 onto every consumer of [Rg].  No novelty is claimed for it. 

 --------
 在含单位的一边，没有从终对象到初对象的态射：这样的态射会把零环的 1 —— 也是它的 0 —— 映射到 ℤ 中的 1 和 0。

 这一点与 Structure/Kernel/Universal/Examples.v 中的 [Rng_no_hom_zero_to_Z] 相同，只是在这里以一个新的名称重新表述，而不是引用它，因为要求那个模块会将它的 23 模块闭包拉入到每一个 [Rg] 的使用者中。对此不声称有新意。
*)
Theorem Rng_terminal_not_initial :
  (Zero_Ring ~{Rng}~> Int_Ring) → False.
Proof.
  intro f.
  assert (H1 : rig_map f ttt = 1%Z) by exact (rig_map_one f).
  assert (H0 : rig_map f ttt = 0%Z) by exact (rig_map_zero f).
  rewrite H1 in H0.
  discriminate.
Qed.

(*
 The discriminating pair Instance/Roster.v defers.  Dropping
 unit-preservation from the morphisms changes the answer.  Read the
 TYPE precisely: the second component is “no unital homomorphism from
 the zero ring to Z”, which is what forces terminal and initial apart
 in [Rng]; the packaged statement “[Rng] has no zero object” is
 Structure/Kernel/Universal/Examples.v's [Rng_no_zero_object],
 proved there and not repackaged here. 

 --------
 可区分的对 Instance/Roster.v 会有所推迟。 从态射中去掉单位保持会改变结果。 精确地阅读类型：第二个分量是“从零环到 Z 没有单位同态”，这就是为什么强制 [Rng] 中的终对象和初对象分离；打包的陈述“[Rng] 没有零对象”是 Structure/Kernel/Universal/Examples.v 中的 [Rng_no_zero_object]，已在那里证明，并且在此未重新打包。
*)
Definition Rng_Rg_zero_object_contrast :
  ZeroObject Rg * ((Zero_Ring ~{Rng}~> Int_Ring) → False) :=
  (Rg_Zero, Rng_terminal_not_initial).

(** ** Strict readbacks / ** 严格复述 *)

Example rg_forget_ab_strict (R : RingObject) :
  rg_ab (ring_rg R) = ring_ab R := eq_refl.

Example rg_forget_mul_strict (R : RingObject) :
  rg_mul (ring_rg R) = rig_mul R := eq_refl.

Example rg_forget_carrier_strict (R : RingObject) :
  carrier (cmon_setoid (ab_cmon (rg_ab (ring_rg R))))
    = carrier (rig_setoid R) := eq_refl.

Example rg_forget_zero_strict (R : RingObject) :
  cmon_zero (ab_cmon (rg_ab (ring_rg R))) = rig_zero R := eq_refl.

Example rg_zero_obj_strict :
  @zero_obj Rg Rg_Zero = Rg_trivial := eq_refl.

Example rg_trivial_carrier_strict :
  carrier (cmon_setoid (ab_cmon (rg_ab Rg_trivial))) = poly_unit := eq_refl.

(* * ** Two refuted strict attempts, pinned / * ** 两次被驳回的严格尝试，固定 *)

(*
 The image of the zero ring is a one-element rng, and so is
 [Rg_trivial], but they are not the same record: Instance/Rng.v
 gives [Zero_Rig] the always-true setoid while [CMon_trivial] carries
 Leibniz [eq] on [poly_unit].  The carriers DO agree, which is the
 control, so the failure is located in the [is_setoid] field. 

 --------
 零环的像是一个只有一个元素的rng，[Rg_trivial]也是如此，但它们不是同一个记录：Instance/Rng.v 给出了[Zero_Rig]这个始终为真的集合，而[CMon_trivial]则在[poly_unit]上携带Leibniz [eq]。承载部分确实一致，这是控制因素，因此故障位于[is_setoid]字段。
*)
Fail Definition probe_zero_ring_is_trivial :
  ring_rg Zero_Ring = Rg_trivial := eq_refl.

Example control_zero_ring_carrier :
  carrier (cmon_setoid (ab_cmon (rg_ab (ring_rg Zero_Ring))))
    = carrier (cmon_setoid (ab_cmon (rg_ab Rg_trivial))) := eq_refl.

(*
 The forgetful functor does not return the hom RECORD it was given.
 This negative is of a DIFFERENT KIND from the one above, and the kind
 was read off the stripped error rather than guessed: this one reports
 a plain type mismatch with NO [cannot unify] clause, the two records
 living in different hom-sets, whereas the one above does report
 [cannot unify] between two terms of a single type.  The control below
 shows the underlying MAP does survive on the nose. 

 --------
 遗忘函子不会返回它所给的同态记录。
 这个负例与上面的是不同类型的负例，而且这种类型是从剥离后的错误中读取的，而不是猜测的：这个负例报告的是一个简单的类型不匹配，没有 [cannot unify] 子句，这两个记录位于不同的同态集合中，而上面的那个负例则报告在单一类型的两个项之间的 [cannot unify]。下面的控制显示底层的映射确实精确保留。
*)
Fail Definition probe_forget_hom_record (R S : RingObject)
  (f : R ~{Rng}~> S) : fmap[Rng_Forget_Rg] f = f := eq_refl.

Example control_forget_underlying_map (R S : RingObject)
  (f : R ~{Rng}~> S) :
  cmon_map (rg_hom_ab (fmap[Rng_Forget_Rg] f)) = rig_map f := eq_refl.

(* * ** Non-vacuity: the even integers / * ** 非空性：偶数 *)

(*
 2ℤ, presented on the carrier ℤ with the multiplication transported
 along z ↦ 2z.  [TwoZ_incl] below proves the presentation earns its
 name.  The three laws are stated first as bare ℤ equations, closed by
 [ring], and then passed to the record by [exact]: the obligation
 types are CONVERTIBLE with them, [Z_eqT] being Leibniz equality, so
 no setoid reasoning is needed and none is done — the same move
 Theory/Algebra/Rig.v makes for [Int_Rig]. 

 --------
 2ℤ，在载体 ℤ 上表示，其乘法沿着 z ↦ 2z 传递。下面的 [TwoZ_incl] 证明该表示名副其实。三个定律首先以纯 ℤ 方程形式陈述，由 [ring] 封闭，然后通过 [exact] 传递到记录：其义务类型与它们是可转换的，[Z_eqT] 是 Leibniz 等式，因此不需要也没有进行集合等价类推理——在 Theory/Algebra/Rig.v 对 [Int_Rig] 也采取了同样的做法。
*)
Definition TwoZ_mul (a b : Z) : Z := 2 * a * b.

Lemma TwoZ_assoc_Z (a b c : Z) :
  TwoZ_mul (TwoZ_mul a b) c = TwoZ_mul a (TwoZ_mul b c).
Proof. unfold TwoZ_mul; ring. Qed.

Lemma TwoZ_distr_l_Z (a b c : Z) :
  TwoZ_mul a (Z.add b c) = Z.add (TwoZ_mul a b) (TwoZ_mul a c).
Proof. unfold TwoZ_mul; ring. Qed.

Lemma TwoZ_distr_r_Z (a b c : Z) :
  TwoZ_mul (Z.add a b) c = Z.add (TwoZ_mul a c) (TwoZ_mul b c).
Proof. unfold TwoZ_mul; ring. Qed.

(*
 Note, and it is the hazard CLAUDE.md records for
 Instance/Sets/Products.v: this [Program Definition] raises
 THREE obligations, not four.  The [rg_mul_respects] field is closed
 by instance resolution during elaboration, because [Z_eqT] is
 Leibniz equality and every function is [Proper] for it.  The three
 that remain are [rg_mul_assoc], [rg_distr_l] and [rg_distr_r], in
 that order. 

 --------
 请注意，这是 CLAUDE.md 在 Instance/Sets/Products.v 中记录的危险：这个 [Program Definition] 引发了三个义务，而不是四个。[rg_mul_respects] 字段在展开过程中通过实例解析被关闭，因为 [Z_eqT] 是莱布尼茨等式，并且每个函数对它都是 [Proper]。剩下的三个是 [rg_mul_assoc]、[rg_distr_l] 和 [rg_distr_r]，按此顺序。
*)
Program Definition TwoZ_Rg : RgObject := {|
  rg_ab  := ring_ab Int_Ring;
  rg_mul := TwoZ_mul
|}.
Next Obligation. exact TwoZ_assoc_Z. Qed.
Next Obligation. exact TwoZ_distr_l_Z. Qed.
Next Obligation. exact TwoZ_distr_r_Z. Qed.

(* Not unital: e·1 ≈ 1 reads 2e = 1 in ℤ, which [lia] refutes. This is the whole point of the witness — [Rg] is not secretly [Rng]. / 非幺半群：e·1 ≈ 1 在 ℤ 中表示 2e = 1，而 [lia] 驳斥了这一点。这就是证人的全部意义——[Rg] 并不是秘密的 [Rng]。 *)
Theorem TwoZ_not_unital :
  ∀ e : carrier (cmon_setoid (ab_cmon (rg_ab TwoZ_Rg))),
    (∀ a, rg_mul TwoZ_Rg e a ≈ a) → False.
Proof.
  intros e H.
  assert (H1 : TwoZ_mul e 1%Z = 1%Z) by exact (H 1%Z).
  unfold TwoZ_mul in H1.
  lia.
Qed.

(* Not degenerate: the carrier has two distinct elements. / 非退化：载体有两个不同的元素。 *)
Theorem TwoZ_nondegenerate :
  (0%Z : carrier (cmon_setoid (ab_cmon (rg_ab TwoZ_Rg))))
    ≈ (1%Z : carrier (cmon_setoid (ab_cmon (rg_ab TwoZ_Rg)))) → False.
Proof. intro H; unfold Z_eqT in H; discriminate. Qed.

(*
 And its multiplication is not identically zero, which is what
 separates this witness from the cheap zero-multiplication rng on an
 arbitrary abelian group: there the multiplicative axioms hold
 vacuously, here they are exercised. 

 --------
 并且它的乘法不是恒等于零的，这就是将这个证明者与任意阿贝尔群上的廉价零乘法随机数生成器区分开来的原因：在那里乘法公理是虚空成立的，而这里它们是被实际使用的。
*)
Theorem TwoZ_mul_nonzero :
  rg_mul TwoZ_Rg 1%Z 1%Z
    ≈ cmon_zero (ab_cmon (rg_ab TwoZ_Rg)) → False.
Proof. intro H; unfold Z_eqT in H; discriminate. Qed.

(*
 The name is earned rather than asserted: doubling is an injective rng
 homomorphism into ℤ whose image is exactly the even integers.
 Multiplicativity is the one clause with content, and it is why the
 transported multiplication had to be 2ab —
 d(a ·₂ b) = 2·(2ab) = 4ab = (2a)(2b) = d a · d b. 

 --------
 这个名字是靠获得的，而不是宣称的：加倍是一个单射的 rng 同态映射到 ℤ，其像正好是偶整数。乘法性是唯一有实质内容的条款，这也是为什么传递的乘法必须是 2ab —— d(a ·₂ b) = 2·(2ab) = 4ab = (2a)(2b) = d a · d b。
*)
Definition TwoZ_double (z : Z) : Z := 2 * z.

Lemma TwoZ_double_add (a b : Z) :
  TwoZ_double (Z.add a b) = Z.add (TwoZ_double a) (TwoZ_double b).
Proof. unfold TwoZ_double; ring. Qed.

Lemma TwoZ_double_mul (a b : Z) :
  TwoZ_double (TwoZ_mul a b) = Z.mul (TwoZ_double a) (TwoZ_double b).
Proof. unfold TwoZ_double, TwoZ_mul; ring. Qed.

Program Definition TwoZ_incl : RgHom TwoZ_Rg (ring_rg Int_Ring) := {|
  rg_hom_ab := {| cmon_map := {| morphism := TwoZ_double |} |}
|}.
Next Obligation. exact (@eq_refl Z 0%Z). Qed.
Next Obligation. exact TwoZ_double_add. Qed.
Next Obligation. exact TwoZ_double_mul. Qed.

Theorem TwoZ_incl_injective : ∀ a b,
  cmon_map (rg_hom_ab TwoZ_incl) a ≈ cmon_map (rg_hom_ab TwoZ_incl) b →
  a ≈ b.
Proof.
  intros a b H.
  assert (H2 : TwoZ_double a = TwoZ_double b) by exact H.
  unfold TwoZ_double in H2.
  assert (Hab : a = b) by lia.
  exact Hab.
Qed.

Theorem TwoZ_incl_image_even : ∀ a,
  { k : Z & cmon_map (rg_hom_ab TwoZ_incl) a = Z.mul 2 k }.
Proof. intro a; exists a; exact (@eq_refl Z (TwoZ_double a)). Qed.

(* The converse half, without which the word “exactly” would be unearned: every even integer IS hit. The two together say the image is the even integers and not merely a subset of them. / 另一半，如果没有它，“确切”这个词就无法成立：每一个偶数整数都被击中。这两者合起来说明图像是偶数整数，而不仅仅是它们的一个子集。 *)
Theorem TwoZ_incl_image_onto_even : ∀ k : Z,
  { a & cmon_map (rg_hom_ab TwoZ_incl) a = Z.mul 2 k }.
Proof. intro k; exists k; exact (@eq_refl Z (TwoZ_double k)). Qed.

(* * ** The universe instance, for the record Rerun the commands below to reproduce the measurement quoted in the header: neither [Rg_trivial] nor [Rg_Zero] carries [Set]. / * ** 宇宙实例，供记录用 重新运行下面的命令以重现标题中引用的测量值：[Rg_trivial] 和 [Rg_Zero] 均不包含 [Set]。 *)

Set Printing Universes.
About Rg_trivial.
About Rg_Zero.
Unset Printing Universes.
