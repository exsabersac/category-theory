Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Image.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Pullback.

Generalizable All Variables.

(* * * Coreflexive pairs, coreflexive equalizers, and Manes' criterion / * * 核反身对，核反身等化器，以及马内斯标准 *)

(*
 Mac Lane §V.2 Exercise 1 (book p. 114; maclane:V.2:ex1).
 nLab: https://ncatlab.org/nlab/show/equalizer
 https://ncatlab.org/nlab/show/complete+category

 BACKGROUND.  Theorem 1 of §V.2 (Structure/Limit/FromProducts.v, #416)
 builds the limit of F : J ⟶ C as the equalizer of two canonical maps
 s, t : ∏_{x} F x ⇉ ∏_{f} F (cod f).  Manes' sharpening (part (a)) observes
 that this pair always has a COMMON LEFT INVERSE — the map back into the
 object product whose component at x is the arrow product's projection at
 the identity arrow of x — so a category with small products needs
 equalizers only of such "coreflexive" pairs to be complete.  Part (b) is
 the elementary characterisation, in Sets, of the pairs with a common RIGHT
 inverse: those whose induced map into the square of the codomain has an
 image containing the diagonal.  Note the two halves speak of two
 different notions: (a) is about coreflexive pairs (a common retraction),
 (b) about reflexive ones (a common section, Structure/Coequalizer/
 Reflexive.v's [ReflexivePair]).

 STALE PREMISES, RE-MEASURED.
 - "the base theorem the exercise refines is itself absent": it landed
 as Structure/Limit/FromProducts.v (#416; docs/INDEX.md) — the
 arrow index [ArrowIx] with [mk_arrow], the generating
 closure [Gen] with [gen_id] and [Generates],
 [ArrowIx_Generates], the elementary core [pe_cone] and
 [pe_limiting], the pair [pe_s]/[pe_t] with their component
 equations, [limit_of_products_equalizer] and
 [Complete_from_products_equalizers].  The core consumes an
 ELEMENTARY [IsEqualizer], never the class — the decisive fact
 here: Manes' criterion needs no [HasEqualizers] anywhere.
 - "coreflexive returns 0 hits": Structure/Topos/Monadic.v proves
 [coreflexive_equalizer_pullback] for a pair with a common retraction
 (a step of Paré's theorem; Test/ProbeToposColimits405.v guards
 it).  The NOTION is in the tree and load-bearing; what was absent is
 the packaging — no record, no class.  [common left inverse] had 0
 hits before this file (it is the phrase this header's BACKGROUND now
 uses), but Theory/Morphisms.v's [Section] is the split-mono
 record with exactly that field, and a coreflexive pair is two such
 splittings sharing one retraction.
 - "reflexive pairs appear ten times across Structure/Coequalizer/
 Reflexive.v and Monad/Monadicity/*": the token [ReflexivePair] occurs
 in four files (Reflexive.v, Monad/Lifting.v, Monad/Monadicity/
 BeckObjects.v, Monad/Monadicity/Crude.v), and with
 [HasReflexiveCoequalizers] fourteen lines sit outside those two
 places, in six files (Monad/Lifting.v 5, Structure/Topos/Monadic.v 4,
 Test/ProbeToposColimits405.v 2, Theory/Lawvere/Monad.v,
 Instance/Sets/Coequalizer.v and Structure/Topos/Colimits.v 1 each;
 an earlier revision listed five files summing to nine).

 WHAT IS DELIVERED (48 constants, every one closed under the global
 context; 45 at the audited revision, plus the three image-level
 constants of item (6) landed after the audit).
 (1) THE NOTION.  [CoreflexivePair f g] (a common retraction with its
 two laws), [HasCoreflexiveEqualizers C] (an elementary equalizer
 for every coreflexive pair), [common_retraction_coreflexive], the
 [#[export] Instance] [HasEqualizers_HasCoreflexiveEqualizers], and
 [functor_preserves_coreflexive] — mirroring Reflexive.v line
 for line.
 (2) THE DUAL, MEASURED.  A common left inverse in C is a common section
 in C^op field for field, so the pair repackages by [:=] both ways
 ([CoreflexivePair_of_op], [op_ReflexivePair_of_Coreflexive]) with
 both round trips at [eq_refl]; the record TYPES are not the same
 type, nor are the classes (probe N1, N2), whose bridges
 ([HasCoreflexiveEqualizers_of_op],
 [op_HasReflexiveCoequalizers_of_Coreflexive]) perform the
 destruct-and-repackage of Structure/Pullback/Reduction.v
 because the existential bodies are
 Structure/Equalizer/Fork.v's [IsEqualizer] and
 Structure/Coequalizer.v's [IsCoequalizer].
 The notion is therefore declared on its own — an alias of
 [ReflexivePair] at [C^op] would force the [y x] argument order and
 [∘[C^op]] on every user and be invisible to the grep that already
 misled the issue — and bridged.
 (3) MAC LANE'S HINT AS A LEMMA.  The identity arrow at x is an index of
 the FULL arrow family with codomain x on the nose ([id_index_cod],
 [id_index_dom], [id_index_arr] at [eq_refl]); [pe_retract] is the
 map into the object product with components the arrow product's
 projections at the identities; [pe_retract_s] and [pe_retract_t]
 are three lines each by FromProducts.v's [pe_iprod_ext];
 [pe_coreflexive : CoreflexivePair (pe_s HP F) (pe_t HP F)].  The
 generating-family variant is NOT stated: [Gen]'s [gen_id] closes
 the generated arrows under identities but puts no identity into the
 index TYPE, so the projection at an abstract family is refused
 (probe N4).  A variant transporting along [idx_arr (idx_id x) ≈
 id] is not stated and was not built; an earlier revision said it
 "was measured", with no artifact.
 (4) MANES' CRITERION.  [mc_equalizer], [mc_apex], [mc_incl],
 [mc_IsEqualizer], [mc_cone], [mc_limiting], [mc_limit], and
 [Complete_from_coreflexive_equalizers : HasIndexedProducts C →
 HasCoreflexiveEqualizers C → Complete C] — FromProducts.v's core fed
 the coreflexive equalizer in place of an arbitrary one; Theorem 2's
 explicit description reads back at [eq_refl] ([mc_limit_apex],
 [mc_limit_leg]) exactly as in FromProducts.v.
 (5) PART (b), THE CATEGORICAL HALF.  In any cartesian category a common
 section IS a factorization of the diagonal [id △ id] through
 [f △ g]: [fork_diagonal_of_reflexive], [reflexive_of_fork_diagonal],
 and the packaged [ReflexivePair_iff_diagonal_factors] (Type-valued
 ↔, empty constraint block).
 (6) PART (b) IN SETS.  [diagonal_in_image f g := ∀ b, ∃ a, (f a ≈ b) *
 (g a ≈ b)]; [diagonal_in_image_of_reflexive] is unconditional; the
 converse [reflexive_of_diagonal_in_image] takes a PROPERNESS
 hypothesis on the chosen witnesses, because [∃] is [sigT] — the
 choice function is present — but a Sets morphism also needs
 [proper_morphism] (probe N5; [diagonal_section]).  The morphism-
 level reading through Instance/Sets/Image.v is a BICONDITIONAL
 with no hypothesis: [diagonal_in_image_iff_through_image :
 diagonal_in_image ↔ ∃ d, Sets_Image_mono (f △ g) ∘ d ≈ id △ id]
 ([through_image_of_diagonal_in_image],
 [diagonal_in_image_of_through_image]; [diagonal_through_image] is
 the forward half from a [ReflexivePair] directly).  Both halves
 are free for the same reason the [ReflexivePair] converse is not:
 [Sets_Image]'s setoid compares codomain components only, so
 the map b ↦ ((b, b); (chosen preimage; _)) is proper in b whatever
 the choice function does.  An earlier revision of this header said
 the reverse "would split the epi leg — a choice principle"; the
 audit compiled it closed.  The choice principle sits only in the
 step to [ReflexivePair].
 (7) NON-VACUITY, AND ITS LIMIT.  [Sets_HasCoreflexiveEqualizers] and
 [Sets_Complete_via_Manes : Complete Sets] compile closed — but the
 only route to the hypothesis in the tree is the STRONGER
 [HasEqualizers Sets] (Reduction.v from [Sets_HasPullbacks]).
 No category in the tree is known to have coreflexive equalizers
 without all equalizers, so the criterion is instantiated only
 where Theorem 1's hypothesis already holds; nothing here separates
 it from [Complete_from_products_equalizers].

 UNIVERSES (measured by [About] under [Set Printing Universes] on all 48
 constants).
 - No word-bounded [Set] in any block; no [JMeq], [EqdepFacts] or
 [eq_rect_r] cap.
 - [CoreflexivePair@{u u0}], [HasCoreflexiveEqualizers@{u u0}],
 [HasCoreflexiveEqualizers_of_op@{u u0}] and
 [ReflexivePair_iff_diagonal_factors@{u u0}] carry EMPTY constraint
 blocks.  [Complete_from_coreflexive_equalizers@{u u0 u1} :
 ∀ {C : Category@{u u0 u0}}, HasIndexedProducts C →
 HasCoreflexiveEqualizers C → Complete@{u0 u0 u0 u}] carries bounds
 only, the same shape as [Complete_from_products_equalizers@{u u0 u1}].
 - Two inherited identifications: [mc_cone] and the four constants built
 on it ([mc_limiting], [mc_limit], [mc_limit_apex], [mc_limit_leg])
 carry [u = u3] and [u2 = u4] (FromProducts.v's [Core] section, where
 the products' levels meet the limit's; an earlier revision named
 [mc_cone] alone), and the eight constants of section [SetsHalf]
 carry [u = u0 = u1 = u2] with [u < u3] — the carrier and proof
 universes of the two setoids identified, the standard Sets
 discipline — four of them ([diagonal_in_image], [diagonal_section],
 [diagonal_in_image_of_through_image],
 [diagonal_in_image_iff_through_image]) also [u < u4].
 [Sets_HasCoreflexiveEqualizers@{u u0}] carries NO equation and
 [u0 < u]; an earlier revision counted "six Sets constants" under
 the equations, which was five then and mis-included this one.
 [Sets_Complete_via_Manes@{u u0} : Complete@{u u u u0}] with [u < u0]
 is the universe shape of Instance/Sets/Complete.v's
 [Sets_Complete].
 - "No stdlib cap" means exactly the three names of the first item.
 Bounds against stdlib universes DO appear: the Sets-side blocks are
 bounded by [prod_rect.u0..u2], [Projections.u0/u1],
 [Basics.compose.u0..u2], and [Sets_HasCoreflexiveEqualizers] and
 [Sets_Complete_via_Manes] additionally by [eq_ind.u0], [eq_ind_r.u0]
 and [Logic_lemmas.equality.u0] (the donor [Sets_Complete] carries none
 of the last three).

 COUNTS AND CONVENTIONS.
 - 48 constants (34 [def], 7 [prf], 1 [inst], 4 [proj], 2 [rec] in the
 [.glob]; the constructors [Build_CoreflexivePair] and
 [Build_HasCoreflexiveEqualizers] are not [.glob] entries and are not
 counted), all "Closed under the global context", zero [Axioms:]
 lines, all gated fully qualified.  Nine [Defined]: one is
 load-bearing by flipping alone to [Qed] ([diagonal_section], whose
 body [reflexive_of_diagonal_in_image] reduces); the other eight
 ([common_retraction_coreflexive], [functor_preserves_coreflexive], the
 two class bridges, [reflexive_of_diagonal_in_image],
 [diagonal_through_image], [diagonal_in_image_of_through_image],
 [through_image_of_diagonal_in_image]) flip freely and are kept
 [Defined] by the data convention.  Five [Qed].
 - Closure 50 files excluding self: Instance/Sets/Image.v and
 Instance/Sets/Products.v cost 4 each at the margin,
 Instance/Sets/Pullback.v, Structure/Limit/FromProducts.v and
 Structure/Coequalizer/Reflexive.v 1 each, the other twenty [Require]s
 0.  (Forty-one Structure/ files already require Instance/Sets; the
 Sets half sits here rather than in a second file for that reason.)
 - Test/ProbeCoreflexive421.v mirrors the [Require] list and carries 6
 refutation commands (1 instrument + 5 negatives of two kinds: three
 conversion, two typing), each stripped one at a time in a copy of the
 whole file, plus the positive TRAP that an implicit [idx_cod] makes
 the refused ascription succeed on a different product; readbacks at
 [eq_refl]; guard coverage 38 identifier tokens inside the refutations /
 31 also named outside, comments stripped, with seven exhaustive
 exceptions (the keyword, the five names the refuted declarations would
 introduce, the absent name); rename-simulated 5/5 ([CoreflexivePair],
 [HasCoreflexiveEqualizers], [HasReflexiveCoequalizers], [pe_gen_proj],
 [diagonal_in_image], each renamed throughout a copy) with every first
 break on a positive line.  [make todo] grows by those 6 lines only
 (2209 → 2215 against the rebased base 625a31ff), so the issue's
 "adds no new hits" box is not met as written; disclosed.

 NOT DELIVERED.
 - A category with coreflexive equalizers but not all equalizers: none
 is built, so the criterion's strict gain over Theorem 1 has no
 witness in the tree (docs/INHABITATION.md should record it).
 - The generating-family form of [pe_coreflexive] (transport needed,
 not stated, not built).
 - The unconditional Sets converse of part (b) from [diagonal_in_image]
 to [ReflexivePair f g] — and with it the issue's pinned NAME
 [Sets_common_section_iff_diagonal], read as [ReflexivePair f g ↔
 diagonal_in_image f g]: its reverse needs the properness hypothesis
 of [reflexive_of_diagonal_in_image] (a choice principle, not
 refuted), so no constant of that name is declared.  The image-level
 biconditional [diagonal_in_image_iff_through_image] IS delivered
 unconditionally (an earlier revision called its reverse a choice
 principle; the audit refuted that).
 - Any relocation of Structure/Topos/Monadic.v's
 [coreflexive_equalizer_pullback] onto the new record: it stays where
 it is (surfaced in the PR, not settled).
 - No edit to Structure/Coequalizer/Reflexive.v, Structure/Limit/
 FromProducts.v or Instance/Sets/Image.v. 

 --------
 Mac Lane §V.2 练习 1（书第 114 页；maclane:V.2:ex1）。
 nLab:  https://ncatlab.org/nlab/show/equalizer 
 https://ncatlab.org/nlab/show/complete+category背景。第 V.2 节定理 1（Structure/Limit/FromProducts.v，#416）构建了 F : J ⟶ C 的极限，作为两个标准映射的等化子
 s, t : ∏_{x} F x ⇉ ∏_{f} F (cod f)。Manes 的加强（部分 (a)）指出，这对映射总是具有一个公共左逆——返回对象积的映射，其在 x 处的分量是箭头积在 x 的恒等箭头处的投影——因此，具有小积的范畴只需要对这种“核心反射”对的等化子就能完备。部分 (b) 是 Sets 中具有公共右逆对的基本描述：那些其诱导映射进入陪域平方的像包含对角线的映射对。注意这两个部分讲述的是两个不同的概念：(a) 关于自反对偶对（一个常见的收缩），(b) 关于自反对偶（一个常见的截面，结构/余等化器/自反.v 的 [ReflexivePair]）。陈旧的前提，重新测量。 - “练习精炼的基础定理本身不存在”：它出现在 Structure/Limit/FromProducts.v (#416; docs/INDEX.md) — 箭头索引 [ArrowIx] 与 [mk_arrow]，生成闭包 [Gen] 与 [gen_id] 和 [Generates]，[ArrowIx_Generates]，基本核心 [pe_cone] 和 [pe_limiting]，成对 [pe_s] / [pe_t] 及其分量方程 [limit_of_products_equalizer] 和 [Complete_from_products_equalizers]。核心消耗一个 ELEMENTARY [IsEqualizer]，从不消耗类 — 这里决定性的事实：Manes 的标准不需要在任何地方使用 [HasEqualizers]。 - “自反返回0命中”：Structure/Topos/Monadic.v 证明了 [coreflexive_equalizer_pullback] 对于具有共同回缩的对（Paré 定理的一步；Test/ProbeToposColimits405.v 对其进行了保护）。这个概念存在于树中并且能承重；缺失的是包装——没有记录，没有类别。在这个文件之前，[common left inverse] 的命中为 0（这是这个标题的背景现在使用的短语），但是 Theory/Morphisms.v 的 [Section] 是具有完全该字段的 split-mono 记录，而一个核心反身对是两个共享一个收缩的这样的分裂。- “反身对在 Structure/Coequalizer/Reflexive.v 和 Monad/Monadicity/* 中出现十次”：标记 [ReflexivePair] 出现在四个文件中（Reflexive.v、Monad/Lifting.v、Monad/Monadicity/BeckObjects.v、Monad/Monadicity/Crude.v），而 [HasReflexiveCoequalizers] 有十四行位于这两个位置之外，在六个文件中（Monad/Lifting.v 5行，Structure/Topos/Monadic.v 4行，Test/ProbeToposColimits405.v 2行，Theory/Lawvere/Monad.v、Instance/Sets/Coequalizer.v 和 Structure/Topos/Colimits.v 各1行；早期修订版列出五个文件，共计九行）。交付的内容是什么（48 个常量，每一个在全局上下文下都是封闭的；审计修订版本中有 45 个，再加上审计后出现的第 (6) 项的三个图像级常量）。(1) 概念。[CoreflexivePair f g]（一个常见的反转及其两个定律），[HasCoreflexiveEqualizers C]（每个自反对的基本等化器），[common_retraction_coreflexive]，[#[export] 实例，[HasEqualizers_HasCoreflexiveEqualizers]，以及 [functor_preserves_coreflexive]——逐行反映 Reflexive.v 文件。(2) 对偶，已测量。在 C 中，一个常见的左逆是 C^op 中的一个常见截面，因此这个对通过 [:=] 以两种方式重新打包 ([CoreflexivePair_of_op], [op_ReflexivePair_of_Coreflexive])，两次往返都在 [eq_refl]；记录 TYPES 不是相同的类型，类也不是 (probe N1, N2)，它们的桥 ([HasCoreflexiveEqualizers_of_op], [op_HasReflexiveCoequalizers_of_Coreflexive]) 执行 Structure/Pullback/Reduction.v 的解构并重新打包，因为存在体是 Structure/Equalizer/Fork.v 的 [IsEqualizer] 和 Structure/Coequalizer.v 的 [IsCoequalizer]。因此，这个概念被独立声明——在 [C^op] 上的 [ReflexivePair] 的别名会强制 [y x] 的参数顺序和 [∘[C^op] 在每个用户上，并且对已经误导这个问题的 grep 来说是不可见的——并且已经建立了桥。(3) 作为引理的 MAC LANE 提示。x 处的恒等箭头是指向 x 的完整箭头族的一个指标（[id_index_cod]，[id_index_dom]，[id_index_arr] 在 [eq_refl]）；[pe_retract] 是进入对象积的映射，其分量是箭头积在恒等下的投影；[pe_retract_s] 和 [pe_retract_t] 各自由 FromProducts.v 的 [pe_iprod_ext] 定义了三条线；[pe_coreflexive : CoreflexivePair (pe_s HP F) (pe_t HP F)]。生成族的变体未说明：[Gen] 的 [gen_id] 在恒等下闭合了生成的箭头，但没有将任何恒等放入指标类型，因此拒绝抽象族处的投影（探测 N4）。沿着 [idx_arr (idx_id x) ≈ id] 传输的变体未被说明，也未建立；早期版本说它“已测量”，但没有人工制品。(4) MANES 的准则。[mc_equalizer]、[mc_apex]、[mc_incl]、[mc_IsEqualizer]、[mc_cone]、[mc_limiting]、[mc_limit]，以及 [Complete_from_coreflexive_equalizers : HasIndexedProducts C → HasCoreflexiveEqualizers C → Complete C] — FromProducts.v 的核心用来替代任意核心反射等化器；定理 2 的明确描述正如 FromProducts.v 中在 [eq_refl]（[mc_limit_apex]、[mc_limit_leg]）中回读。(5) 部分 (b)，范畴论的一半。在任何笛卡尔范畴中，一个公共截面是通过 [f △ g] 对角线 [id △ id] 的因式分解：[fork_diagonal_of_reflexive], [reflexive_of_fork_diagonal]，以及打包的 [ReflexivePair_iff_diagonal_factors]（类型值 ↔，空约束块）。(6) 部分 (b) 在集合中。[diagonal_in_image f g := ∀ b, ∃ a, (f a ≈ b) * (g a ≈ b)]; [diagonal_in_image_of_reflexive] 是无条件的；逆命题 [reflexive_of_diagonal_in_image] 需要对选定的证人有适当性假设，因为 [∃] 是 [sigT] ——选择函数存在——但一个集合态射还需要 [proper_morphism]（探针 N5；[diagonal_section]）。通过 Instance/Sets/Image.v 的态射级别阅读是一个没有假设的双条件：[diagonal_in_image_iff_through_image : diagonal_in_image ↔ ∃ d, Sets_Image_mono (f △ g) ∘ d ≈ id △ id] ([through_image_of_diagonal_in_image], [diagonal_in_image_of_through_image]；[diagonal_through_image] 是直接来自 [ReflexivePair] 的正向部分)。两半都是自由的，原因与 [ReflexivePair] 逆命题不自由相同：[Sets_Image] 的集合等价只比较陪域分量，所以映射 b ↦ ((b, b); (选择的原像; _)) 不论选择函数怎么做在 b 上都是适当的。这个标题的早期版本说反向“会分裂满射腿——一个选择原理”；审核编译时将其关闭。选择原理仅存在于到 [ReflexivePair] 的步骤中。(7) 非空性及其极限。[Sets_HasCoreflexiveEqualizers] 和 [Sets_Complete_via_Manes : Complete Sets] 编译关闭——但在树中达到假设的唯一途径是更强的 [HasEqualizers Sets]（来自 [Sets_HasPullbacks] 的 Reduction.v）。在树中，没有已知的范畴在没有所有等化器的情况下拥有自反等化器，因此该准则仅在定理 1 的假设已成立的情况下才被实例化；这里没有任何内容将其与 [Complete_from_products_equalizers] 区分开来。宇宙（由 [About] 在 [Set Printing Universes] 下针对所有 48 个常量测量）。- 在任何块中没有以单词为界的 [Set]；没有 [JMeq]、[EqdepFacts] 或 [eq_rect_r] 大写。- [CoreflexivePair@{u u0}]、[HasCoreflexiveEqualizers@{u u0}]、[HasCoreflexiveEqualizers_of_op@{u u0}] 和 [ReflexivePair_iff_diagonal_factors@{u u0}] 承载 EMPTY 约束块。[Complete_from_coreflexive_equalizers@{u u0 u1}：∀ {C : Category@{u u0 u0}}, HasIndexedProducts C → HasCoreflexiveEqualizers C → Complete@{u0 u0 u0 u}] 仅携带边界，与 [Complete_from_products_equalizers@{u u0 u1}] 形状相同。- 两个继承的标识：[mc_cone] 以及基于它构建的四个常量（[mc_limiting]、[mc_limit]、[mc_limit_apex]、[mc_limit_leg]）携带 [u = u3] 和 [u2 = u4]（来自 Products.v 的 [Core] 部分，其中产品的层级达到限制；早期版本仅命名 [mc_cone]），而 [SetsHalf] 部分的八个常量携带 [u = u0 = u1 = u2] 及 [u < u3] —— 被识别的两个集合体的承载和证明宇宙，标准 Sets 规范 —— 其中四个（[diagonal_in_image]、[diagonal_section]、[diagonal_in_image_of_through_image]、[diagonal_in_image_iff_through_image]）也 [u < u4]。[Sets_HasCoreflexiveEqualizers@{u u0}] 不携带任何方程式和 [u0 < u]；早期版本在方程式下计算“六个 Sets 常量”，当时为五个，并错误地包括了这一项。[Sets_Complete_via_Manes@{u u0} : Complete@{u u u u0}] 与 [u < u0] 是 Instance/Sets/Complete.v 的宇宙形状 [Sets_Complete]。"No stdlib cap" 的意思正好是第一个条目的三个名称。针对 stdlib 宇宙的界限确实存在：Sets 端的块受到 [prod_rect.u0..u2]、[Projections.u0/u1]、[Basics.compose.u0..u2] 和 [Sets_HasCoreflexiveEqualizers] 的限制，并且 [Sets_Complete_via_Manes] 还受到 [eq_ind.u0]、[eq_ind_r.u0] 和 [Logic_lemmas.equality.u0] 的限制（捐赠者 [Sets_Complete] 不包含后三个中的任何一个）。计数与约定。- 48 个常量（34 个 [def]、7 个 [prf]、1 个 [inst]、4 个 [proj]、2 个 [rec] 在 [.glob] 中；构造函数 [Build_CoreflexivePair] 和 [Build_HasCoreflexiveEqualizers] 不是 [.glob] 条目，因此不计入），所有“在全局上下文下封闭”，零 [Axioms:] 行，全部门控并完全限定。九个 [Defined]：其中一个仅通过翻转就承重到 [Qed]（[diagonal_section]，其主体 [reflexive_of_diagonal_in_image] 会减少）；其余八个（[common_retraction_coreflexive]、[functor_preserves_coreflexive]、两个类桥、[reflexive_of_diagonal_in_image]、[diagonal_through_image]、[diagonal_in_image_of_through_image]、[through_image_of_diagonal_in_image]）可以自由翻转，并由数据约定保持 [Defined]。五个 [Qed]。- 闭包 50 个文件（不包括自身）：Instance/Sets/Image.v 和 Instance/Sets/Products.v 在边际上的成本各为 4，Instance/Sets/Pullback.v、Structure/Limit/FromProducts.v 和 Structure/Coequalizer/Reflexive.v 各为 1，其他二十个 [Require] 为 0。（四十一个结构/文件已经需要实例/集合；集合的一半在这里，而不是在第二个文件中。）
 - Test/ProbeCoreflexive421.v 镜像 [Require] 列表，并携带 6 个反驳命令（1 个工具 + 5 个两种类型的否定：3 个转换，2 个类型），每次在整个文件的副本中逐一去掉，另外还有正向 TRAP，即隐式 [idx_cod] 使被拒绝的归属在不同产品上成功；重读于 [eq_refl]；在反驳中保护覆盖 38 个标识符标记 / 另外 31 个在外部也被命名，注释被去掉，七个详尽例外（关键词，反驳声明将引入的五个名称，缺失的名称）；重命名模拟 5/5（[CoreflexivePair]、[HasCoreflexiveEqualizers]、[HasReflexiveCoequalizers]），[pe_gen_proj]，[diagonal_in_image]，每个在整个副本中都已重新命名）在每个正线上的第一次断开处。[make todo] 仅通过那6行增长（2209 → 2215，相对于重新基准的 base 625a31ff），因此按原文所述，该问题的“未增加新命中”选项未满足；已披露。未交付。- 一个具有核心自反等化器但不是所有等化器的范畴：没有构建，因此该标准相对于定理1的严格增益在树中没有证据（docs/INHABITATION.md 应该记录它）。- [pe_coreflexive] 的生成族形式（需要迁移，未说明，未构建）。- [diagonal_in_image] 到 [ReflexivePair f g] 的部分(b) 的无条件集合逆——以及随之而来的该问题的固定名称 [Sets_common_section_iff_diagonal]，被解读为 [ReflexivePair f g ↔ diagonal_in_image f g]：其逆需要 [reflexive_of_diagonal_in_image] 的适当性假设（选择原理，未被反驳），因此未声明该名称的常量。像层面的双条件 [diagonal_in_image_iff_through_image] 无条件交付（早期修订将其逆称为选择原理；审核否认了该说法）。- 任何将 Structure/Topos/Monadic.v 的 [coreflexive_equalizer_pullback] 迁移到新记录的操作：它保持在原位（在 PR 中出现，但尚未确定）。- 不修改 Structure/Coequalizer/Reflexive.v、Structure/Limit/FromProducts.v 或 Instance/Sets/Image.v。
*)

(** ** Coreflexive pairs / ** 核心反身对 *)

(* The equational data: one map that retracts both f and g. A coreflexive pair is two split monomorphisms (Theory/Morphisms.v's [Section]) sharing one retraction. / 方程数据：一个同时重整 f 和 g 的映射。一个余反射对是两个分裂单射（Theory/Morphisms.v 的 [Section]），共享一个重整映射。 *)
Record CoreflexivePair {C : Category} {x y : C} (f g : x ~> y) := {
  corefl_retract   : y ~> x;                    (* the common retraction / 常见的收回 *)
  corefl_retract_f : corefl_retract ∘ f ≈ id;   (* it retracts f / 它缩回 f *)
  corefl_retract_g : corefl_retract ∘ g ≈ id    (* and g *)
}.

Arguments corefl_retract   {_ _ _ _ _} _.
Arguments corefl_retract_f {_ _ _ _ _} _.
Arguments corefl_retract_g {_ _ _ _ _} _.

(*
 A category has coreflexive equalizers when every coreflexive pair
 carries an elementary equalizer (Structure/Equalizer/Fork.v's
 [IsEqualizer]).  Compare [HasEqualizers], which asks the same of every
 parallel pair, and Structure/Coequalizer/Reflexive.v's
 [HasReflexiveCoequalizers], the dual. 

 --------
 一个范畴具有自反等化器，当每一个自反对都具有一个基本等化器（Structure/Equalizer/Fork.v 的 [IsEqualizer]）。比较 [HasEqualizers]，它对每一个平行对提出相同要求，以及 Structure/Coequalizer/Reflexive.v 的 [HasReflexiveCoequalizers]，它是对偶的。
*)
Class HasCoreflexiveEqualizers (C : Category) := {
  coreflexive_eq {x y : C} (f g : x ~> y) :
    CoreflexivePair f g → ∃ (q : C) (e : q ~> x), IsEqualizer f g q e
}.

Lemma common_retraction_coreflexive {C : Category} {x y : C} (f g : x ~> y)
  (r : y ~> x) (Hf : r ∘ f ≈ id) (Hg : r ∘ g ≈ id) : CoreflexivePair f g.
Proof.
  exact {| corefl_retract   := r
         ; corefl_retract_f := Hf
         ; corefl_retract_g := Hg |}.
Defined.

(* Every category with equalizers has coreflexive ones. / 每个有均衡器的类别都有自反的均衡器。 *)
#[export] Instance HasEqualizers_HasCoreflexiveEqualizers
  {C : Category} `{H : @HasEqualizers C} : HasCoreflexiveEqualizers C := {|
  coreflexive_eq := fun x y f g _ => @equalizer C H x y f g
|}.

(*
 Two equations with no quantification over the ambient category, so
 arbitrary functors preserve coreflexivity — as they do reflexivity
 (Structure/Coequalizer/Reflexive.v's [functor_preserves_reflexive]). 

 --------
 两个没有对环境范畴进行量化的方程，因此任意函子保持余自反性——正如它们保持自反性一样（Structure/Coequalizer/Reflexive.v 的 [functor_preserves_reflexive]）。
*)
Theorem functor_preserves_coreflexive {C D : Category} (F : C ⟶ D)
  {x y : C} (f g : x ~> y) :
  CoreflexivePair f g → CoreflexivePair (fmap[F] f) (fmap[F] g).
Proof.
  intros R.
  unshelve refine {| corefl_retract := fmap[F] (corefl_retract R) |}.
  - rewrite <- fmap_comp, (corefl_retract_f R); apply fmap_id.
  - rewrite <- fmap_comp, (corefl_retract_g R); apply fmap_id.
Defined.

(* * ** The dual reading: a coreflexive pair in C is a reflexive pair in C^op / * ** 双重读法：C 中的自交对在 C^op 中是一个自反对 *)

(*
 The FIELD types convert — a common left inverse in C is literally a
 common section in C^op — so the pair repackages by [:=] in both
 directions and round-trips at [eq_refl].  The record TYPES are not the
 same type, nor are the classes (the probe pins both), so the notion is
 declared on its own and bridged. 

 --------
 FIELD 类型进行转换——在 C 中，一个常见的左逆实际上在 C^op 中是一个常见的截面——因此该对由 [:=] 在两个方向上重新打包，并在 [eq_refl] 处进行往返。记录 TYPES 不是相同的类型，类也不是（探针引脚都是），所以该概念单独声明并建立桥接。
*)
Definition CoreflexivePair_of_op {C : Category} {x y : C} {f g : x ~> y}
  (R : @ReflexivePair (C^op) y x f g) : CoreflexivePair f g :=
  @Build_CoreflexivePair C x y f g
    (refl_section R) (refl_section_f R) (refl_section_g R).

Definition op_ReflexivePair_of_Coreflexive {C : Category} {x y : C}
  {f g : x ~> y} (R : CoreflexivePair f g) : @ReflexivePair (C^op) y x f g :=
  @Build_ReflexivePair (C^op) y x f g
    (corefl_retract R) (corefl_retract_f R) (corefl_retract_g R).

Example corefl_op_round {C : Category} {x y : C} {f g : x ~> y}
  (R : CoreflexivePair f g) :
  CoreflexivePair_of_op (op_ReflexivePair_of_Coreflexive R) = R := eq_refl.

Example op_corefl_round {C : Category} {x y : C} {f g : x ~> y}
  (R : @ReflexivePair (C^op) y x f g) :
  op_ReflexivePair_of_Coreflexive (CoreflexivePair_of_op R) = R := eq_refl.

(*
 The classes need the destruct-and-repackage Structure/Pullback/
 Reduction.v performs for [HasEqualizers_op_of_HasCoequalizers]: the
 existential body is [IsCoequalizer] on one side and [IsEqualizer] on
 the other. 

 --------
 这些类需要 destruct-and-repackage Structure/Pullback/Reduction.v 对 [HasEqualizers_op_of_HasCoequalizers] 执行的操作：存在体在一边是 [IsCoequalizer]，另一边是 [IsEqualizer]。
*)
Definition HasCoreflexiveEqualizers_of_op {C : Category}
  (H : HasReflexiveCoequalizers (C^op)) : HasCoreflexiveEqualizers C.
Proof.
  constructor; intros x y f g R.
  destruct (@reflexive_coeq (C^op) H y x f g
              (op_ReflexivePair_of_Coreflexive R)) as [q [e Eq]].
  exists q, e.
  exact (IsEqualizer_op_of_IsCoequalizer Eq).
Defined.

Definition op_HasReflexiveCoequalizers_of_Coreflexive {C : Category}
  (H : HasCoreflexiveEqualizers C) : HasReflexiveCoequalizers (C^op).
Proof.
  constructor; intros x y f g R.
  destruct (@coreflexive_eq C H y x f g (CoreflexivePair_of_op R))
    as [q [e Eq]].
  exists q, e.
  exact (@IsCoequalizer_of_IsEqualizer_op (C^op) x y f g q e Eq).
Defined.

(* * ** Mac Lane's pair is coreflexive / * ** 马克·莱恩的对是自反的 *)

Section Manes.

Context {C : Category} (HP : HasIndexedProducts C).
Context {J : Category} (F : J ⟶ C).

(*
 The identity arrow at x is an index of the FULL arrow family of
 Structure/Limit/FromProducts.v, and its codomain is x on the nose. 

 --------
 在 x 处的恒等箭头是 Structure/Limit/FromProducts.v 中完整箭头族的一个索引，其陪域正好是 x。
*)
Example id_index_cod (x : J) : aix_cod (mk_arrow (@id J x)) = x := eq_refl.
Example id_index_dom (x : J) : aix_dom (mk_arrow (@id J x)) = x := eq_refl.
Example id_index_arr (x : J) : aix_arr (mk_arrow (@id J x)) = @id J x := eq_refl.

(*
 Mac Lane's candidate retraction: the map into the object product whose
 component at x is the arrow product's projection at the identity of x. 

 --------
 Mac Lane 的候选收缩：映射到对象积的映射，其在 x 处的分量是箭头积在 x 的恒等映射处的投影。
*)
Definition pe_retract : pe_arrow_product HP F ~> pe_obj_product HP F :=
  unique_obj (iprod_desc (pe_obj_product_ump HP F)
    (fun x : J => pe_arrow_proj HP F (mk_arrow (@id J x)))).

Lemma pe_retract_proj (x : J) :
  pe_obj_proj HP F x ∘ pe_retract ≈ pe_arrow_proj HP F (mk_arrow (@id J x)).
Proof.
  exact (unique_property (iprod_desc (pe_obj_product_ump HP F)
    (fun x : J => pe_arrow_proj HP F (mk_arrow (@id J x)))) x).
Qed.

Lemma pe_retract_s : pe_retract ∘ pe_s HP F ≈ id.
Proof.
  apply (pe_iprod_ext (pe_obj_product_ump HP F)); intro x.
  rewrite comp_assoc, pe_retract_proj.
  rewrite (pe_s_proj HP F (mk_arrow (@id J x))).
  rewrite id_right.
  reflexivity.
Qed.

Lemma pe_retract_t : pe_retract ∘ pe_t HP F ≈ id.
Proof.
  apply (pe_iprod_ext (pe_obj_product_ump HP F)); intro x.
  rewrite comp_assoc, pe_retract_proj.
  rewrite (pe_t_proj HP F (mk_arrow (@id J x))).
  simpl.
  rewrite fmap_id, id_left, id_right.
  reflexivity.
Qed.

(* Mac Lane's hint, as a proved lemma. / 作为已证明引理的Mac Lane的提示。 *)
Definition pe_coreflexive : CoreflexivePair (pe_s HP F) (pe_t HP F) :=
  common_retraction_coreflexive _ _ pe_retract pe_retract_s pe_retract_t.

(** ** Manes' criterion / ** 马内斯标准 *)

Context (HE : HasCoreflexiveEqualizers C).

Definition mc_equalizer :=
  coreflexive_eq (pe_s HP F) (pe_t HP F) pe_coreflexive.

Definition mc_apex : C := `1 mc_equalizer.

Definition mc_incl : mc_apex ~> pe_obj_product HP F := `1 (`2 mc_equalizer).

Definition mc_IsEqualizer : IsEqualizer (pe_s HP F) (pe_t HP F) mc_apex mc_incl
  := `2 (`2 mc_equalizer).

(*
 The limit is FromProducts.v's construction fed the coreflexive
 equalizer in place of an arbitrary one; its core consumes the
 elementary [IsEqualizer], never the class. 

 --------
 极限是从 FromProducts.v 的构造馈送到自反等化器，以替代任意一个；它的核消耗基本的 [IsEqualizer]，而从不消耗类。
*)
Definition mc_cone : Cone F :=
  pe_cone F (pe_obj_proj HP F) (pe_obj_product_ump HP F) ArrowIx_Generates
    (pe_arrow_proj HP F) (pe_arrow_product_ump HP F)
    (pe_s HP F) (pe_t HP F) (pe_s_proj HP F) (pe_t_proj HP F)
    mc_incl mc_IsEqualizer.

Definition mc_limiting : IsLimitCone mc_cone :=
  pe_limiting F (pe_obj_proj HP F) (pe_obj_product_ump HP F) ArrowIx_Generates
    (pe_arrow_proj HP F) (pe_arrow_product_ump HP F)
    (pe_s HP F) (pe_t HP F) (pe_s_proj HP F) (pe_t_proj HP F)
    mc_incl mc_IsEqualizer.

Definition mc_limit : Limit F := limitcone_limit mc_cone mc_limiting.

Example mc_limit_apex :
  vertex_obj[@limit_cone _ _ _ mc_limit] = mc_apex := eq_refl.

Example mc_limit_leg (x : J) :
  cone_leg (@limit_cone _ _ _ mc_limit) x = pe_obj_proj HP F x ∘ mc_incl
  := eq_refl.

End Manes.

(*
 Mac Lane §V.2 Exercise 1(a): small products and coreflexive equalizers
 give completeness. 

 --------
 Mac Lane §V.2 练习 1(a)：小乘积和共反射等化子给出完备性。
*)
Definition Complete_from_coreflexive_equalizers {C : Category}
  (HP : HasIndexedProducts C) (HE : HasCoreflexiveEqualizers C) : @Complete C :=
  fun J F => mc_limit HP F HE.

(* * ** Exercise 1(b), the categorical half: a common section is a factorization of the diagonal through the induced map / * ** 练习 1(b)，分类的一半：一个公共部分是通过诱导映射的对角线的分解 *)

(*
 Part (b) is about REFLEXIVE pairs (a common right inverse), not the
 coreflexive pairs of part (a); in any cartesian category the section is
 exactly a factorization of the diagonal [id △ id] through [f △ g]. 

 --------
 第(b)部分是关于自反对（一个常见的右逆），而不是第(a)部分的共反对；在任何笛卡尔范畴中，截面恰好是对角线 [id △ id] 通过 [f △ g] 的分解。
*)
Section CartesianHalf.

Context {C : Category} `{@Cartesian C}.
Context {x y : C} (f g : x ~> y).

Lemma fork_diagonal_of_reflexive (s : y ~> x) (Hf : f ∘ s ≈ id)
  (Hg : g ∘ s ≈ id) : (f △ g) ∘ s ≈ id △ id.
Proof.
  rewrite <- fork_comp.
  rewrite Hf, Hg.
  reflexivity.
Qed.

Lemma reflexive_of_fork_diagonal (s : y ~> x) (Hd : (f △ g) ∘ s ≈ id △ id) :
  (f ∘ s ≈ id) * (g ∘ s ≈ id).
Proof.
  split.
  - rewrite <- (exl_fork f g), <- comp_assoc, Hd.
    apply exl_fork.
  - rewrite <- (exr_fork f g), <- comp_assoc, Hd.
    apply exr_fork.
Qed.

Definition ReflexivePair_of_diagonal_factors :
  (∃ s : y ~> x, (f △ g) ∘ s ≈ id △ id) → ReflexivePair f g :=
  fun sd => let (s, Hd) := sd in
    let (Hf, Hg) := reflexive_of_fork_diagonal s Hd in
    common_section_reflexive f g s Hf Hg.

Definition diagonal_factors_of_ReflexivePair (R : ReflexivePair f g) :
  ∃ s : y ~> x, (f △ g) ∘ s ≈ id △ id :=
  (refl_section R;
     fork_diagonal_of_reflexive (refl_section R)
       (refl_section_f R) (refl_section_g R)).

Definition ReflexivePair_iff_diagonal_factors :
  ReflexivePair f g ↔ (∃ s : y ~> x, (f △ g) ∘ s ≈ id △ id) :=
  (diagonal_factors_of_ReflexivePair, ReflexivePair_of_diagonal_factors).

End CartesianHalf.

(** ** Exercise 1(b) in Sets / ** 集合中的练习 1(b) *)

Section SetsHalf.

Context {X Y : SetoidObject}.
Context (f g : X ~{Sets}~> Y).

(* "The image of ⟨f, g⟩ contains the diagonal", pointwise: every point of Y is hit by f and g at one common point of X. / “⟨f, g⟩ 的像包含对角线”，逐点来说：Y 的每一个点都由 f 和 g 在 X 的某个共同点处映射到。 *)
Definition diagonal_in_image : Type :=
  ∀ b : Y, ∃ a : X, (f a ≈ b) * (g a ≈ b).

(* One direction is unconditional: the section supplies the witness. / 有一个方向是无条件的：该部分提供证人。 *)
Definition diagonal_in_image_of_reflexive (R : ReflexivePair f g) :
  diagonal_in_image :=
  fun b => (refl_section R b; (refl_section_f R b, refl_section_g R b)).

(*
 The converse needs the chosen witnesses to respect ≈, which the
 statement of [diagonal_in_image] does not supply: [∃] is [sigT], so a
 choice function is present, but a Sets morphism also needs
 [proper_morphism]. 

 --------
 反向需要选定的证人遵守 ≈，而 [diagonal_in_image] 的陈述没有提供：[∃] 是 [sigT]，所以存在选择函数，但集合态射还需要 [proper_morphism]。
*)
Definition diagonal_section (D : diagonal_in_image)
  (Hproper : ∀ b b' : Y, b ≈ b' → `1 (D b) ≈ `1 (D b')) : Y ~{Sets}~> X.
Proof.
  unshelve refine {| morphism := fun b => `1 (D b) |}.
  repeat intro; now apply Hproper.
Defined.

Definition reflexive_of_diagonal_in_image (D : diagonal_in_image)
  (Hproper : ∀ b b' : Y, b ≈ b' → `1 (D b) ≈ `1 (D b')) :
  ReflexivePair f g.
Proof.
  unshelve refine (common_section_reflexive f g (diagonal_section D Hproper) _ _).
  - intro b; exact (fst (`2 (D b))).
  - intro b; exact (snd (`2 (D b))).
Defined.

(*
 The morphism-level reading through Instance/Sets/Image.v: the diagonal
 factors through the mono leg of the (epi, mono) factorization of the
 induced map.  Unconditional in this direction. 

 --------
 通过 Instance/Sets/Image.v 的态射级读取：对角线通过诱导映射的（满射，单射）分解的单射部分。该方向是无条件的。
*)
Definition diagonal_through_image (R : ReflexivePair f g) :
  ∃ d : Y ~{Sets}~> Sets_Image (f △ g),
    Sets_Image_mono (f △ g) ∘ d ≈ id △ id.
Proof.
  unshelve eexists.
  - unshelve refine {| morphism := fun b =>
        ((f △ g) (refl_section R b); (refl_section R b; _)) |}.
    + reflexivity.
    + repeat intro.
      simpl.
      split; apply proper_morphism; now apply proper_morphism.
  - intro b; simpl.
    split; [exact (refl_section_f R b) | exact (refl_section_g R b)].
Defined.

(*
 The image-level statement is a biconditional with NO choice principle,
 in either direction: [Sets_Image]'s setoid compares codomain components
 only, so the map b ↦ ((b, b); (chosen preimage; _)) is proper in b
 however the choice function behaves, and the stored preimage of a
 factorization reads back as a pointwise witness.  (An earlier revision
 of this file said the reverse "would split the epi leg — a choice
 principle"; the audit compiled it closed.  The choice principle sits
 ONLY in the step from [diagonal_in_image] to a Sets morphism, i.e. to
 [ReflexivePair]: [diagonal_section]'s properness hypothesis.) 

 --------
 图像级声明是一个带有无选择公理的双条件语句，无论哪个方向：[Sets_Image] 的集合等价只比较值域成分，因此映射 b ↦ ((b, b); (选定的前像; _)) 在 b 下是适当的，无论选择函数如何行为，并且一个分解的存储前像作为逐点证据读回。（该文件的早期版本说反向“将拆分满射分支——一个选择公理”；审计编译后关闭。选择公理仅存在于从 [diagonal_in_image] 到 Sets 同态的步骤，即到 [ReflexivePair]：[diagonal_section] 的适当性假设。）
*)
Definition diagonal_in_image_of_through_image
  (d : Y ~{Sets}~> Sets_Image (f △ g))
  (Hd : Sets_Image_mono (f △ g) ∘ d ≈ id △ id) : diagonal_in_image.
Proof.
  intro b.
  exists (`1 (`2 (d b))).
  destruct (`2 (d b)) as [a Ha]; simpl in *.
  destruct (Hd b) as [H1 H2]; simpl in *.
  destruct Ha as [Ha1 Ha2]; simpl in *.
  split; [now rewrite Ha1 | now rewrite Ha2].
Defined.

Definition through_image_of_diagonal_in_image (D : diagonal_in_image) :
  ∃ d : Y ~{Sets}~> Sets_Image (f △ g),
    Sets_Image_mono (f △ g) ∘ d ≈ id △ id.
Proof.
  unshelve eexists.
  - unshelve refine {| morphism := fun b => ((b, b); (`1 (D b); _)) |}.
    + split; simpl; [exact (fst (`2 (D b))) | exact (snd (`2 (D b)))].
    + repeat intro; simpl; split; assumption.
  - intro b; simpl; split; reflexivity.
Defined.

(*
 Exercise 1(b) in Sets, stated with the image machinery as the issue
 asks: the image of ⟨f, g⟩ contains the diagonal (pointwise) exactly when
 the diagonal factors through [Sets_Image_mono (f △ g)].  This is the
 image-level reading; the issue's pinned NAME
 [Sets_common_section_iff_diagonal] would put [ReflexivePair f g] on the
 left, and that reading is delivered only with the properness hypothesis
 ([reflexive_of_diagonal_in_image]) — see the header. 

 --------
 集合中的练习 1(b)，用图像机制表示为问题，问：当且仅当对角线通过 [Sets_Image_mono (f △ g)] 映射时，⟨f, g⟩ 的像包含对角线（逐点）。这是图像层面的理解；问题中固定的名称 [Sets_common_section_iff_diagonal] 会将 [ReflexivePair f g] 放在左侧，且该理解只有在满足适当性假设（[reflexive_of_diagonal_in_image]）时才能成立——见标题。
*)
Definition diagonal_in_image_iff_through_image :
  diagonal_in_image
    ↔ (∃ d : Y ~{Sets}~> Sets_Image (f △ g),
         Sets_Image_mono (f △ g) ∘ d ≈ id △ id) :=
  (through_image_of_diagonal_in_image,
   fun dd : ∃ d : Y ~{Sets}~> Sets_Image (f △ g),
              Sets_Image_mono (f △ g) ∘ d ≈ id △ id =>
     diagonal_in_image_of_through_image (`1 dd) (`2 dd)).

End SetsHalf.

(** ** Non-vacuity, and its limit / ** 非空性及其极限 *)

(*
 [Sets] has coreflexive equalizers — but the only route in the tree is
 through the STRONGER [HasEqualizers Sets], so Manes' criterion is
 instantiated here only where Theorem 1's hypothesis already holds. 

 --------
 [Sets] 有自反等化子——但树中的唯一路径是通过更强的 [HasEqualizers Sets]，因此 Manes 的标准在此仅在定理 1 的假设已经成立的情况下才被实例化。
*)
Definition Sets_HasCoreflexiveEqualizers : HasCoreflexiveEqualizers Sets :=
  @HasEqualizers_HasCoreflexiveEqualizers Sets
    (HasEqualizers_of_HasPullbacks_Terminal Sets_HasPullbacks).

Definition Sets_Complete_via_Manes : @Complete Sets :=
  Complete_from_coreflexive_equalizers
    Sets_HasIndexedProducts Sets_HasCoreflexiveEqualizers.
