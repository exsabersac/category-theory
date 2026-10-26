Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Reals.Rseries.
Require Import Coq.Reals.SeqProp.
Require Import Coq.Reals.Rcomplete.
Require Import Coq.micromega.Lra.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Universal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Met.
Require Import Category.Instance.Met.Completion.

Generalizable All Variables.

Open Scope R_scope.

(* * * Metric spaces with uniformly continuous maps; Mac Lane §IV.3 / * * 带均匀连续映射的度量空间；Mac Lane §IV.3 *)

(*
 nLab:  https://ncatlab.org/nlab/show/reflective+subcategory
 nLab:  https://ncatlab.org/nlab/show/complete+metric+space
 nLab:  https://ncatlab.org/nlab/show/uniformly+continuous+map
 Book:  Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 GTM 5, §IV.3, printed p. 92 (PDF p. 101) — the example this
 file proves (catalog item maclane:IV.3:construction1)
 Book:  Mac Lane, same, §IV.3, printed p. 91 (PDF p. 100) — the
 universal-arrow reading of a reflection, which
 Construction/Reflective/Universal.v states
 Book:  Bishop, “Foundations of Constructive Analysis”, McGraw-Hill
 1967 — the modulus discipline, as in Instance/Met.v

 MAC LANE'S SENTENCE, quoted from the page image of p. 92:

 “Or consider the category of all metric spaces X, with arrows
 uniformly continuous functions.  The (full) subcategory of complete
 metric spaces is reflective; the reflector sends each metric space
 to its completion.”

 One chapter earlier, in §III.1, printed pp. 56-57 (PDF pp. 65-66),
 the same construction appears over a DIFFERENT category.  Quoted from
 the page image:

 “Complete Metric Spaces.  Let Met be the category of all metric
 spaces X, Y, ..., with arrows X → Y those functions which preserve
 the metric (and which therefore are necessarily injections).  The
 complete metric spaces form (the objects of) a full subcategory.
 The familiar completion X̄ of a metric space X provides an arrow
 X → X̄ which is universal for the evident forgetful functor (from
 complete metric spaces to metric spaces).”

 That is Instance/Met.v's [Met] and Instance/Met/Completion.v's
 [Completion_UniversalArrow].  Before issue #370 neither file built
 the §IV.3 category, with uniformly continuous arrows, nor the
 completion as a functor or as a reflection; their headers were
 written then, and each carries a CORRECTION (#370) note pointing
 here.  This file builds both.

 WHY UNIFORM CONTINUITY.  The completion is made of Cauchy sequences,
 so a map can act on it only if it carries Cauchy sequences to Cauchy
 sequences.  A uniformly continuous map does, with a modulus obtained
 by composing its own modulus with the sequence's ([uext_MCauchy]); a
 merely continuous map need not (x ↦ 1/x on the positive reals is the
 classical instance; it is argued here, not formalized).  So uniform
 continuity is a natural class of maps along which Cantor's
 construction is functorial, and it is the class Mac Lane names.  An
 isometry is uniformly continuous with δ := ε ([iso_umap]), so every
 arrow of [Met] is one of [MetU], and the reflection proved here
 agrees with the §III.1 one on objects.

 THE MODULUS IS DATA.  [UCont] asks, for every ε > 0, for a δ > 0 AS
 DATA (this library's `∃` is [sigT]), exactly as Instance/Met.v's
 [MCauchy] asks for its threshold.  The hom-setoid of [MetU] compares
 the underlying maps pointwise and ignores the modulus, so two moduli
 for one map give one arrow.  A map uniformly continuous only in the
 Prop-level sense (∀ ε, exists δ in [Prop]) is an arrow here only
 given a choice of moduli; no claim is made that the two readings
 agree.

 WHAT IS DELIVERED.

 - [UCont], [UMap], [MetU]: the category of Mac Lane's sentence, on
 Instance/Met.v's [MetricSpace].
 - [CompleteSpacesU], [CMetU], [CMetU_Full]: the complete spaces, a
 full subcategory on the same predicate [MComplete] as [CMet].
 - [Met_to_MetU]: the comparison, identity on objects;
 [Met_to_MetU_Faithful]; and [Met_to_MetU_not_Full], the constant
 map of [Harmonic] onto one point, which no isometry realizes
 ([isometry_injective]), so the two categories genuinely differ.
 - [uext]: the extension of a uniformly continuous map into a complete
 space along the completion, with [uext_eta] (it extends) and
 [uext_unique] (it is the only uniformly continuous extension, by
 density, [eta_dense]).
 - [CompletionU_UniversalArrow], and the headline
 [CMet_Reflective_in_MetU] with [completionU_adj], the adjunction
 made visible: Mac Lane's example, as an inhabitant of
 Construction/Reflective.v's record.
 - [CMet_Reflective_in_Met] with [completion_adj]: the isometric
 companion at §III.1's category.  It promotes to library constants
 the two terms Test/ProbeMet.v elaborates as [probe_CompletionFunctor]
 and [probe_CompletionAdj].
 - [completionU_unit_Harmonic_not_iso]: the reflection in [MetU] is
 proper.  Instance/Met.v's [Harmonic] is not complete
 ([Harmonic_not_MComplete] there), and at it the unit is not
 invertible: an inverse would carry the point of the completion that
 the embedding misses (Instance/Met/Completion.v's
 [Completion_Harmonic_adds_a_point]) to a point whose constant
 sequence is that point, the unit applied to a point being its
 constant sequence ([completionU_unit_pointwise]).

 STRENGTHS, MEASURED STRICT FIRST.  At [eq_refl]: the reflector's
 object at X IS [CompletionU X], the whole Σ-object
 ([completionU_reflector_obj]; the isometric one likewise,
 [completion_reflector_obj]); the unit applied to a point a IS the
 constant sequence [eta_seq X a] ([completionU_unit_pointwise],
 [completion_unit_pointwise]); the two reflections have the same
 carrier ([completion_reflectors_agree]); [Met_to_MetU] is the identity
 on objects ([Met_to_MetU_obj]).  Refused at [eq_refl], pinned in
 Test/ProbeReflective370.v rather than here (a negative probe line in
 this file would add to [make todo]): the unit as a whole record
 against [etaU X]
 (“cannot unify ”unit“ and ”etaU X“”, and likewise against [eta X] in
 [Met]), because the unit is the transpose [fmap[Incl] id ∘ etaU X];
 and the counit and the reflector's arrow action even pointwise at an
 embedded point.  Both are [unique_obj] of Theory/Universal/Arrow.v's
 [Qed]-closed [ump_universal_arrows], and that [Qed] blocks even their
 sequence components, but it is not the whole cause.  Measured by
 rebuilding the left adjoint over a transparent copy of the universal
 property: the arrow action's sequence component then reads back as
 the constant sequence of [f a], yet neither whole-point statement
 does, since the arrow's value carries the completion's Cauchy
 modulus and the counit is the limit chosen by the target's
 completeness witness.
 CORRECTION (#1347): the unit as a whole record against [etaU X] now
 holds at [eq_refl] (that probe's N13, now a control), since
 Instance/Sets.v gives its identity's and composite's properness fields
 as terms; the cause given above, the unit being the transpose, was
 argued, and in [MetU] the residue was the standard library's.
 Against [eta X] in [Met] it is still refused (N14), and so are the
 counit and the reflector's arrow action at an embedded point.

 THE AXIOM FOOTPRINT, per constant, by [Print Assumptions] on all 55
 constants: the 54 [Print Module] lists, [Program] obligations
 included, and the record constructor [Build_UMap].  None is closed.
 Even [UCont] carries [sig_forall_dec]: measured alone, the order
 [Rlt] and the literal [0%R] each carry it, while [R] itself is
 closed.  28 constants carry
 exactly [sig_forall_dec]: the vocabulary, the category and its
 obligations, the complete-space subcategory, [iso_umap],
 [Met_to_MetU] with its obligations, [Met_to_MetU_obj],
 [Met_to_MetU_Faithful] and [umap_MConverges].  Three carry
 [sig_forall_dec] and [functional_extensionality_dep]: [const_umap],
 [Met_to_MetU_not_Full] and [ureal_below_all_zero], through [lra] (a
 one-line [lra] proof of [0 < 1] carries that pair, measured) and, for
 the second, through [Harmonic], which carries it too.  The other 24
 carry those two and [sig_not_dec]: everything from [uext_seq] on,
 since the completion's distance is a limit taken with [R_complete]
 (Instance/Met/Completion.v, whose header prices the same three).
 They are stdlib axioms of the reals, permitted in the instance layer
 by docs/AXIOMS.md and to be enumerated there, not gated.

 UNIVERSES, read by [About] under [Set Printing Universes] on every
 constant.  [MetU@{u o} : Category@{u o o}] with the one constraint
 [o < u], the shape [About Met] prints for [Met@{u u0}] ([u0 < u]).
 [CompleteSpacesU@{u o u0 u1 u2 u3} : Subcategory@{u o u1 u0}
 MetU@{u o}], the four further universes being [MComplete]'s, as for
 [CompleteSpaces].  The headline carries thirteen:

 CMet_Reflective_in_MetU@{u o u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10} :
 Reflective@{u0 u u0 u1 u u2 o} CompleteSpacesU@{u o o u2 u3 u4}
 ( * ... |= o < u, and non-strict bounds only * )

 and [CMet_Reflective_in_Met] the same at [Met] and [CompleteSpaces].
 The subcategory's fourth universe is identified with the hom level
 [o]: that is [Reflective]'s own binder ([Subcategory@{u3 u5 u4 u5}]
 in [About Reflective]), not this file's.  Two constants carry [Set],
 both at the harmonic space.  One is [Met_to_MetU_not_Full@{u} : Full
 Met_to_MetU@{u Set} → False] with [Set < u]: the witness [Harmonic]
 has points in [nat] and [About Harmonic] prints [Harmonic@{} :
 MetricSpace@{Set}], so non-fullness is measured at that level only.
 The other is [completionU_unit_Harmonic_not_iso], stated at
 [MetU@{u Set}] with the same bound [Set < u].  The constants of
 section [Extend] take the section's [Universe o] and add those of
 [MComplete] and of [Completion] ([uext@{o u u0 u1 u2 u3}]).
 [uext_MCauchy] does not take the section's completeness hypothesis:
 its [Proof using X Y f] keeps the section's [Default Proof Using
 “All”] from attaching it, and [About] reads [∀ X Y (f : UMap X Y) x,
 MCauchy Y (uext_seq X Y f x)].

 NOT DELIVERED.

 - No comparison of the two reflections beyond their carriers: no
 natural isomorphism between [Met_to_MetU] after the isometric
 reflection and the uniform reflection after [Met_to_MetU], and no
 functor from [CMet] to [CMetU].
 - No statement about continuous maps that are not uniformly
 continuous; the example above is argued, not formalized.
 - The Prop-level reading of uniform continuity, as above.
 - Mac Lane's third example on p. 92, compact Hausdorff spaces in
 completely regular spaces with the Stone–Čech compactification, is
 not here; it is re-homed from issue #370 to issue #1329.
 - Riehl's Example 4.6.13 (printed pp. 169-170) does not list the
 metric completion among its clauses, so nothing here answers to
 her roster. 

 --------
 nLab：   https://ncatlab.org/nlab/show/reflective+subcategory
 nLab：   https://ncatlab.org/nlab/show/complete+metric+space
 nLab：   https://ncatlab.org/nlab/show/uniformly+continuous+map
 书籍：  Mac Lane，《为在职数学家而写的范畴论》，第2版，
 GTM 5，§IV.3，印刷第92页（PDF第101页）——本文件证明的示例（目录项 maclane:IV.3:construction1）
 书籍：  Mac Lane，同上，§IV.3，印刷第91页（PDF第100页）——反射的泛箭头阅读，
 Construction/Reflective/Universal.v 中说明
 书籍：  Bishop，《构造分析的基础》，McGraw-Hill，1967年——模数方法，如 Instance/Met.v 中所示

 MAC LANE 的句子，从第92页的页面图像中引用：或者考虑所有度量空间 X 的范畴，其箭头为一致连续函数。完备度量空间的（全）子范畴是反射性的；反射子将每个度量空间映射到其完备化。

 在前一章的 §III.1，第 56-57 页（PDF 第 65-66 页）中，同样的构造出现在一个不同的范畴上。从页面图像引用：完备度量空间。设 Met 为所有度量空间 X, Y, ... 的范畴，其箭头 X → Y 为保持度量的函数（因此必然是单射）。完备度量空间形成一个满子范畴（作为对象）。度量空间 X 的熟悉完备化 X̄ 提供一个箭头 X → X̄，该箭头对于从完备度量空间到度量空间的显然忘记函子是普遍的。

 即 Instance/Met.v 中的 [Met] 和 Instance/Met/Completion.v 中的 [Completion_UniversalArrow]。在 #370 问题之前，这两个文件都没有构建带有一致连续箭头的 §IV.3 范畴，也没有将完备化作为函子或反射；它们的头部早已写好，并且每个都带有指向此处的 CORRECTION (#370) 注释。该文件构建了两者。为什么选择一致连续。 完备空间是由柯西列构成的，因此一个映射只有在把柯西列映射为柯西列时才能在其上作用。 一致连续映射可以做到这一点，其调节函数可以通过将自身的调节函数与序列的调节函数组合来获得 ([uext_MCauchy])；而仅仅连续的映射不一定如此（正实数上的 x ↦ 1/x 是经典例子，这里进行了论证，但未形式化）。 因此，一致连续是 Cantor 构造沿着其函子化的自然映射类别，也是 Mac Lane 命名的类别。 一个等距映射是一致连续的，取 δ := ε ([iso_umap])，所以  [Met] 的每个箭头都是  [MetU] 的一个箭头，并且此处证明的反射在对象上与 §III.1 的一致。模量就是数据。[UCont] 要求，对于每一个 ε > 0，存在一个 δ > 0 作为数据（该库的 `∃` 是 [sigT]），完全像 Instance/Met.v 的 [MCauchy] 要求其阈值那样。[MetU] 的同态集比较底层映射的每一点，并忽略模量，因此对于一个映射的两个模量产生一个箭头。仅在 Prop 级意义下均匀连续的映射（∀ ε，存在 δ 在 [Prop] 中）在此处仅在选择了模量的情况下才是箭头；不保证两种解读一致。

 什么被提供。- [UCont]、[UMap]、[MetU]：Mac Lane 句子的范畴，在 Instance/Met.v 的 [MetricSpace] 上。- [CompleteSpacesU]、[CMetU]、[CMetU_Full]：完备空间，一个在相同谓词 [MComplete] 上的满子范畴，如 [CMet]。- [Met_to_MetU]：比较，对象上的同一性；[Met_to_MetU_Faithful]；以及 [Met_to_MetU_not_Full]，将 [Harmonic] 映射到一个点的常值映射，没有任何等距实现（[isometry_injective]），所以这两个范畴确实不同。- [uext]：沿完备化将一致连续映射扩展到完备空间，具有 [uext_eta]（它扩展了）和 [uext_unique]（它是唯一的一致连续扩展，由密度，[eta_dense]）。- [CompletionU_UniversalArrow]，以及标题 [CMet_Reflective_in_MetU] 和 [completionU_adj]，使结合显现：Mac Lane 的例子，作为 Construction/Reflective.v 的记录的一个元素。- [CMet_Reflective_in_Met] 与 [completion_adj]：位于 §III.1 类别的等距伴随。它将 Test/ProbeMet.v 阐述的两个项提升为库常量，分别是 [probe_CompletionFunctor] 和 [probe_CompletionAdj]。- [completionU_unit_Harmonic_not_iso]：在 [MetU] 中的反射是合适的。Instance/Met.v 的 [Harmonic] 并不完整（[Harmonic_not_MComplete] 在那里），并且其单位不可逆：一个逆应当将嵌入所遗漏完成的点（Instance/Met/Completion.v 的 [Completion_Harmonic_adds_a_point]）映射到其常数序列为该点的点，单位应用到一个点即为其常数序列（[completionU_unit_pointwise]）。优势，首先严格测量。在 [eq_refl]：反射器在 X 处的对象是 [CompletionU X]，整个 Σ-对象（[completionU_reflector_obj]；同构对象同样，[completion_reflector_obj]）；作用于点 a 的单位是常数序列 [eta_seq X a]（[completionU_unit_pointwise], [completion_unit_pointwise]）；两次反射具有相同的载体（[completion_reflectors_agree]）；[Met_to_MetU] 是对象上的恒等映射（[Met_to_MetU_obj]）。在 [eq_refl] 被拒绝，而固定在 Test/ProbeReflective370.v 中而非此处（此文件中的负测试行将增加到 [make todo]）：作为整个记录的单位针对 [etaU X]（“无法统一‘unit’和‘etaU X’”，同样针对 [eta X] 在 [Met] 中），因为单位是转置 [fmap[Incl] id ∘ etaU X；并且余单位和反射器的箭头作用甚至在嵌入点上逐点生效。两者都是 Theory/Universal/Arrow.v 的 [unique_obj]
 [Qed] -closed [ump_universal_arrows]，并且 [Qed] 阻止了它们甚至是序列组件，但这并不是全部原因。通过在通用性质的透明副本上重建左伴随来测量：箭头作用的序列组件随后读回为 [f a] 的恒定序列，但没有一个总体点陈述是这样，因为箭头的值携带完成的柯西模量，并且对偶算子是由目标的完备性证人选择的极限。更正 (#1347)：作为整体记录的单元现在在 [etaU X] 处保持在 [eq_refl]（该探针的 N13，现在是一个控制），因为 Instance/Sets.v 将其身份和复合的正确性字段作为项给出；上述原因是该单元是转置，已经被论证，并且在 [MetU] 中残差是标准库的。针对 [eta X] 在 [Met] 中仍被拒绝（N14），嵌入点处的余单元和反射子的箭头作用也同样被拒绝。公理足迹（THE AXIOM FOOTPRINT），按常量计算，由 [Print Assumptions] 对所有 55 个常量：54 个 [Print Module] 列表、包含的 [Program] 义务，以及记录构造函数 [Build_UMap]。没有一个是封闭的。即使 [UCont] 也包含 [sig_forall_dec]：单独测量时，顺序 [Rlt] 和文字 [0%R] 各自包含它，而 [R] 本身是封闭的。28 个常量恰好包含 [sig_forall_dec]：词汇、类别及其义务、完全空间子类别、ZW81WZZ、ZW82WZZ 及其义务、ZW83WZZ、ZW84WZZ 以及 ZW85WZZ。三个常量包含 ZW86WZZ 和 ZW87WZZ：ZW88WZZ、ZW89WZZ 和 ZW90WZZ，通过 ZW91WZZ（一行 ZW92WZZ 对 ZW93WZZ 的证明以度量方式包含该对），对于第二个，通过 ZW94WZZ，它也包含它。其他 24 个
 携带那两个和 [sig_not_dec]：从 [uext_seq] 开始的所有东西，
 因为完成的距离是通过 [R_complete] 取的一个限制
 （Instance/Met/Completion.v，其头部定价相同的三个）。它们是实数的标准库公理，在实例层中由 docs/AXIOMS.md 允许，并在其中列举，而不受阻。

 UNIVERSES，由 [About] 在 [Set Printing Universes] 下读取，每个常量都如此。  [MetU@{u o} : Category@{u o o}] 带有一个约束 [o < u]，ZW102WZZ 为 [Met@{u u0}] 打印的形状（[u0 < u]）。
 [CompleteSpacesU@{u o u0 u1 u2 u3} : Subcategory@{u o u1 u0} MetU@{u o}]，另外四个宇宙是 [MComplete] 的，正如 [CompleteSpaces] 所示。  标题包含十三个：CMet_Reflective_in_MetU@{u o u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10} ：
 Reflective@{u0 u u0 u1 u u2 o} CompleteSpacesU@{u o o u2 u3 u4}
 ( * ... |= o < u，且仅限非严格边界 * )以及 [CMet_Reflective_in_Met] 在 [Met] 和 [CompleteSpaces] 上相同。子类别的第四个宇宙由同伦层级 [o] 识别：即 [Reflective] 自己的绑定器（[Subcategory@{u3 u5 u4 u5}] 在 [About Reflective] 中），而不是此文件的。两个常量携带 [Set]，都位于谐波空间。一个是 [Met_to_MetU_not_Full@{u} : Full Met_to_MetU@{u Set} → False]，与 [Set < u] 对应：见证 [Harmonic] 在 [nat] 中有点，而 [About Harmonic] 打印 [Harmonic@{} : MetricSpace@{Set}]，因此非完全性仅在那个层级测量。另一个是 [completionU_unit_Harmonic_not_iso]，在 [MetU@{u Set}] 声明，绑定相同的 [Set < u]。第 [Extend] 节的常量取该节的 [Universe o]，并加上 [MComplete] 和 [Completion] 的（[uext@{o u u0 u1 u2 u3}]）。[uext_MCauchy] 不接受该部分的完整性假设：
 它的 [Proof using X Y f] 保留了该部分的 [使用“全部”的默认证明]，没有附加该假设，并且 [About] 读作 [∀ X Y (f : UMap X Y) x, MCauchy Y (uext_seq X Y f x)]。

 未交付。- 两个反射仅比较它们的承载物：在等距反射后的 [Met_to_MetU] 与 [Met_to_MetU] 之后的统一反射之间没有自然同构，也没有从 [CMet] 到 [CMetU] 的函子。
 - 对非一致连续的连续映射没有陈述；上述示例是通过论证而非形式化给出的。
 - 上述一致连续性的命题层次解读。
 - Mac Lane 在第 92 页的第三个例子，即完全正则空间中的紧 Hausdorff 空间与 Stone–Čech 紧化，在这里没有；它从第 #370 期移到了第 #1329 期。
 - Riehl 的例子 4.6.13（印刷在第 169-170 页）未在其条款中列出度量完备性，因此此处没有对应她的清单。
*)

(** ** Uniformly continuous maps / ** 一致连续映射 *)

Definition UCont@{o +} (X Y : MetricSpace@{o})
  (f : SetoidMorphism (met_carrier X) (met_carrier Y)) : Type@{o} :=
  ∀ eps : R, 0 < eps →
    ∃ delta : R, (0 < delta ∧
      ∀ x y : X, dist x y < delta → dist (f x) (f y) < eps).

Record UMap@{o +} (X Y : MetricSpace@{o}) : Type@{o} := {
  umap :> SetoidMorphism (met_carrier X) (met_carrier Y);
  umap_uc : UCont X Y umap
}.

Arguments umap {X Y} _.
Arguments umap_uc {X Y} _ _ _.

Definition UMap_equiv@{o +} {X Y : MetricSpace@{o}} : crelation (UMap X Y) :=
  fun f g => ∀ x : X, umap f x ≈ umap g x.

Arguments UMap_equiv {X Y} _ _ /.

#[export]
Program Instance UMap_Setoid@{o +} {X Y : MetricSpace@{o}} :
  Setoid (UMap X Y) := {| equiv := UMap_equiv |}.
Next Obligation.
  constructor.
  - intros f x; reflexivity.
  - intros f g Hfg x; symmetry; exact (Hfg x).
  - intros f g h Hfg Hgh x; transitivity (umap g x).
    + exact (Hfg x).
    + exact (Hgh x).
Qed.

(** ** The category MetU / ** 类别 MetU *)

Definition umet_id@{o +} {X : MetricSpace@{o}} : UMap X X.
Proof.
  refine {| umap := setoid_morphism_id |}.
  intros eps Heps; exists eps; split; [ exact Heps |].
  intros x y H; exact H.
Defined.

Definition umet_compose@{o +} {X Y Z : MetricSpace@{o}}
  (g : UMap Y Z) (f : UMap X Y) : UMap X Z.
Proof.
  refine {| umap := setoid_morphism_compose g f |}.
  intros eps Heps.
  destruct (umap_uc g eps Heps) as [dg [Hdg Hg]].
  destruct (umap_uc f dg Hdg) as [df [Hdf Hf]].
  exists df; split; [ exact Hdf |].
  intros x y Hxy; simpl.
  apply Hg, Hf, Hxy.
Defined.

Lemma umet_compose_respects@{o +} {X Y Z : MetricSpace@{o}} :
  Proper (equiv ==> equiv ==> equiv) (@umet_compose X Y Z).
Proof.
  intros g1 g2 Hg f1 f2 Hf x; simpl.
  rewrite (Hg (umap f1 x)).
  apply proper_morphism, Hf.
Qed.

Program Definition MetU@{u o | o < u +} : Category@{u o o} := {|
  obj     := MetricSpace@{o};
  hom     := UMap;
  homset  := @UMap_Setoid;
  id      := @umet_id;
  compose := @umet_compose;

  compose_respects := @umet_compose_respects
|}.

(* * ** The complete spaces, a full subcategory / * ** 完全空间，一个完整的子类别 *)

Definition CompleteSpacesU@{u o +} : Subcategory MetU@{u o} :=
  @Build_Subcategory MetU
    (fun X => MComplete X)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition CMetU@{u o +} : Category := Sub MetU@{u o} CompleteSpacesU.

Definition CMetU_Incl@{u o +} : Sub MetU@{u o} CompleteSpacesU ⟶ MetU@{u o} :=
  Incl MetU CompleteSpacesU.

Definition CMetU_Full@{u o +} :
  Construction.Subcategory.Full MetU@{u o} CompleteSpacesU :=
  fun _ _ _ _ _ => I.

(* * ** Isometries are uniformly continuous: the comparison Met ⟶ MetU / * ** 等距映射是均匀连续的：比较 Met ⟶ MetU *)

Definition iso_umap@{o +} {X Y : MetricSpace@{o}} (f : Isometry X Y) :
  UMap X Y.
Proof.
  refine {| umap := isometry_map f |}.
  intros eps Heps; exists eps; split; [ exact Heps |].
  intros x y H; rewrite (isometry_dist f x y); exact H.
Defined.

Program Definition Met_to_MetU@{u o | o < u +} : Met@{u o} ⟶ MetU@{u o} := {|
  fobj := fun X => X;
  fmap := fun X Y f => iso_umap f
|}.

Example Met_to_MetU_obj@{u o | o < u +} (X : Met@{u o}) :
  fobj[Met_to_MetU@{u o}] X = X := eq_refl.

Lemma Met_to_MetU_Faithful@{u o | o < u +} : Faithful Met_to_MetU@{u o}.
Proof. constructor; intros X Y f g H x; exact (H x). Qed.

(* A constant map is uniformly continuous. / 一个常量映射是统一连续的。 *)
Definition const_umap@{o +} (X Y : MetricSpace@{o}) (b : Y) : UMap X Y.
Proof.
  unshelve refine {| umap := {| morphism := fun _ => b |} |}.
  - repeat intro; reflexivity.
  - intros eps Heps; exists 1; split; [ lra |].
    intros; simpl; rewrite dist_refl; exact Heps.
Defined.

Theorem Met_to_MetU_not_Full@{u | Set < u +} :
  Functor.Full Met_to_MetU@{u Set} → False.
Proof.
  intros HF.
  pose (c := const_umap Harmonic Harmonic 0%nat).
  pose (f := @prefmap _ _ _ HF Harmonic Harmonic c).
  pose proof (@fmap_sur _ _ _ HF Harmonic Harmonic c) as Hf.
  assert (H01 : isometry_map f 0%nat ≈ isometry_map f 1%nat).
  { transitivity (umap c 0%nat).
    - exact (Hf 0%nat).
    - symmetry; exact (Hf 1%nat). }
  pose proof (isometry_injective f 0%nat 1%nat H01) as H.
  discriminate H.
Qed.

(* * ** Uniformly continuous maps preserve limits / * ** 一致连续映射保持极限 *)

Lemma umap_MConverges@{o +} {X Y : MetricSpace@{o}} (f : UMap X Y)
  (u : nat → X) (l : X) :
  MConverges X u l → MConverges Y (fun n => umap f (u n)) (umap f l).
Proof.
  intros Hl eps Heps.
  destruct (umap_uc f eps Heps) as [d [Hd Hf]].
  destruct (Hl d Hd) as [N HN].
  exists N; intros n Hn.
  apply Hf, HN, Hn.
Defined.

(* A non-negative real below every positive real is zero. / 每个正实数下面的非负实数是零。 *)
Lemma ureal_below_all_zero@{+} (r : R) :
  0 <= r → (∀ eps, 0 < eps → r < eps) → r = 0.
Proof.
  intros H0 H.
  destruct (Rle_lt_or_eq_dec 0 r H0) as [Hlt | Heq]; [| now symmetry].
  specialize (H r Hlt); lra.
Qed.

(* * ** The extension of a uniformly continuous map to the completion / * ** 均匀连续映射到完备化的延拓 *)

Section Extend.

Local Set Default Proof Using "All".

Universe o.

Context (X Y : MetricSpace@{o}).
Context (cY : MComplete Y).
Context (f : UMap X Y).

Definition uext_seq (x : Completion X) : nat → Y :=
  fun n => umap f (cs_seq X x n).

(*
 Uniform continuity alone carries a Cauchy sequence to a Cauchy
 sequence: the section's completeness hypothesis is not used, and the
 explicit [Proof using] keeps it out of the lemma's type. 

 --------
 仅有一致连续性就能将柯西序列映射为柯西序列：该部分的完备性假设未被使用，而且显式的 [Proof using] 使其不属于引理的类型。
*)
Definition uext_MCauchy (x : Completion X) : MCauchy Y (uext_seq x).
Proof using X Y f.
  intros eps Heps.
  destruct (umap_uc f eps Heps) as [d [Hd Hf]].
  destruct (cs_cauchy X x d Hd) as [N HN].
  exists N; intros m n Hm Hn.
  apply Hf, HN; assumption.
Defined.

Definition uext_val (x : Completion X) : Y := `1 (cY _ (uext_MCauchy x)).

Definition uext_spec (x : Completion X) :
  MConverges Y (uext_seq x) (uext_val x) := `2 (cY _ (uext_MCauchy x)).

Lemma uext_close (x y : Completion X) (eps : R) (Heps : 0 < eps) (d : R)
  (Hf : ∀ a b : X, dist a b < d → dist (umap f a) (umap f b) < eps / 2)
  (N : nat)
  (HN : ∀ n, (N <= n)%nat → dist (cs_seq X x n) (cs_seq X y n) < d) :
  dist (uext_val x) (uext_val y) < eps.
Proof.
  destruct (uext_spec x (eps / 8) ltac:(lra)) as [N1 H1].
  destruct (uext_spec y (eps / 8) ltac:(lra)) as [N2 H2].
  pose (n := Nat.max N (Nat.max N1 N2)).
  assert (N <= n)%nat as HnN by apply Nat.le_max_l.
  assert (N1 <= n)%nat as Hn1
    by (transitivity (Nat.max N1 N2);
        [ apply Nat.le_max_l | apply Nat.le_max_r ]).
  assert (N2 <= n)%nat as Hn2
    by (transitivity (Nat.max N1 N2);
        [ apply Nat.le_max_r | apply Nat.le_max_r ]).
  specialize (H1 n Hn1); specialize (H2 n Hn2).
  pose proof (Hf _ _ (HN n HnN)) as Hmid.
  pose proof (dist_triangle (uext_val x) (uext_seq x n) (uext_val y)) as T1.
  pose proof (dist_triangle (uext_seq x n) (uext_seq y n) (uext_val y)) as T2.
  rewrite (dist_sym (uext_val x) (uext_seq x n)) in T1.
  unfold uext_seq in *.
  lra.
Qed.

Lemma uext_proper (x y : Completion X) : x ≈ y → uext_val x ≈ uext_val y.
Proof.
  intro Hxy.
  apply dist_separates, ureal_below_all_zero; [ apply dist_nonneg |].
  intros eps Heps.
  destruct (umap_uc f (eps / 2) ltac:(lra)) as [d [Hd Hf]].
  destruct (Hxy d Hd) as [N HN].
  apply (uext_close x y eps Heps d Hf N).
  intros n Hn; specialize (HN n Hn).
  unfold R_dist, cdist_seq in HN.
  rewrite Rminus_0_r in HN.
  eapply Rle_lt_trans; [ apply Rle_abs | exact HN ].
Qed.

Definition uext_morphism :
  SetoidMorphism (met_carrier (Completion X)) (met_carrier Y).
Proof.
  unshelve refine {| morphism := uext_val |}.
  intros x y Hxy; exact (uext_proper x y Hxy).
Defined.

Definition uext_uc : UCont (Completion X) Y uext_morphism.
Proof.
  intros eps Heps.
  destruct (umap_uc f (eps / 2) ltac:(lra)) as [d [Hd Hf]].
  exists d; split; [ exact Hd |].
  intros x y Hxy; simpl.
  change (cdist X x y < d) in Hxy.
  destruct (cdist_spec X x y (d - cdist X x y) ltac:(lra)) as [N HN].
  apply (uext_close x y eps Heps d Hf N).
  intros n Hn; specialize (HN n Hn).
  unfold R_dist in HN.
  destruct (Rabs_def2 _ _ HN) as [Hhi _].
  unfold cdist_seq in Hhi.
  lra.
Defined.

Definition uext : UMap (Completion X) Y := {|
  umap := uext_morphism; umap_uc := uext_uc |}.

Lemma uext_eta (a : X) : umap uext (eta_seq X a) ≈ umap f a.
Proof.
  apply (MConverges_unique (uext_seq (eta_seq X a))).
  - exact (uext_spec (eta_seq X a)).
  - intros eps Heps.
    exists 0%nat; intros n _.
    unfold uext_seq; simpl.
    rewrite dist_refl; exact Heps.
Qed.

Lemma uext_unique (g : UMap (Completion X) Y) :
  (∀ a : X, umap g (eta_seq X a) ≈ umap f a) →
  ∀ x : Completion X, umap g x ≈ umap uext x.
Proof.
  intros Hg x.
  apply (MConverges_unique (uext_seq x)).
  - apply (MConverges_respects_seq
             (fun n => umap g (eta_seq X (cs_seq X x n))) (uext_seq x)).
    + intro n; exact (Hg (cs_seq X x n)).
    + exact (umap_MConverges g _ x (eta_dense X x)).
  - exact (uext_spec x).
Qed.

End Extend.

(* * ** The completion as a universal arrow in MetU / * ** 在 MetU 中作为通用箭头的完成 *)

Definition CompletionU@{u o +} (X : MetricSpace@{o}) :
  Sub MetU@{u o} CompleteSpacesU :=
  (Completion X; Completion_MComplete X).

Definition etaU@{o +} (X : MetricSpace@{o}) : UMap X (Completion X) :=
  iso_umap (eta X).

Definition CompletionU_UniversalArrow@{u o +} (X : MetU@{u o}) :
  UniversalArrow X (Incl MetU@{u o} CompleteSpacesU).
Proof.
  unshelve eapply (universal_arrow_from_UMP X (Incl MetU CompleteSpacesU)
                     (CompletionU X) (etaU X)).
  intros d f.
  unshelve econstructor.
  - exact (uext X (`1 d) (`2 d) f; I).
  - exact (fun a => symmetry (uext_eta X (`1 d) (`2 d) f a)).
  - intros v Hv x.
    symmetry.
    exact (uext_unique X (`1 d) (`2 d) f (`1 v) (fun a => symmetry (Hv a)) x).
Defined.

(* * ** Mac Lane §IV.3: complete spaces are reflective in MetU / * ** Mac Lane §IV.3：完备空间在 MetU 中是自反的 *)

Definition CMet_Reflective_in_MetU@{u o +} :
  @Reflective MetU@{u o} CompleteSpacesU :=
  Reflective_of_UniversalArrows CMetU_Full CompletionU_UniversalArrow.

Definition completionU_adj@{u o +} :
  @reflector MetU@{u o} _ CMet_Reflective_in_MetU
    ⊣ Incl MetU@{u o} CompleteSpacesU :=
  reflective_adj CMet_Reflective_in_MetU.

Example completionU_reflector_obj@{u o +} (X : MetU@{u o}) :
  fobj[@reflector MetU@{u o} _ CMet_Reflective_in_MetU] X = CompletionU X
  := eq_refl.

Example completionU_unit_pointwise@{u o +} (X : MetU@{u o}) (a : X) :
  umap (@unit _ _ _ _ completionU_adj X) a = eta_seq X a := eq_refl.

(* * ** The isometric companion: complete spaces reflective in Met / * ** 等距伴侣：在 Met 中反映的完整空间 *)

Definition CMet_Reflective_in_Met@{u o +} :
  @Reflective Met@{u o} CompleteSpaces :=
  Reflective_of_UniversalArrows CMet_Full
    (fun X : Met => Completion_UniversalArrow X).

Definition completion_adj@{u o +} :
  @reflector Met@{u o} _ CMet_Reflective_in_Met
    ⊣ Incl Met@{u o} CompleteSpaces :=
  reflective_adj CMet_Reflective_in_Met.

Example completion_reflector_obj@{u o +} (X : Met@{u o}) :
  fobj[@reflector Met@{u o} _ CMet_Reflective_in_Met] X = Completion_CMet X
  := eq_refl.

Example completion_unit_pointwise@{u o +} (X : Met@{u o}) (a : X) :
  isometry_map (@unit _ _ _ _ completion_adj X) a = eta_seq X a
  := eq_refl.

(* The two reflections build the same space. / 这两个反射构建了相同的空间。 *)
Example completion_reflectors_agree@{u o +} (X : MetricSpace@{o}) :
  `1 (fobj[@reflector MetU@{u o} _ CMet_Reflective_in_MetU] X)
    = `1 (fobj[@reflector Met@{u o} _ CMet_Reflective_in_Met] X) := eq_refl.

(*
 The reflection is proper: at the harmonic space, which is not
 complete (Instance/Met.v's [Harmonic_not_MComplete]), the unit is not
 invertible.  Its inverse would send the point the embedding misses
 (Instance/Met/Completion.v's [Completion_Harmonic_adds_a_point]) to a
 point whose image is that point, and the unit applied to a point IS
 its constant sequence ([completionU_unit_pointwise]). 

 --------
 反射是适当的：在调和空间中，它不是完备的（Instance/Met.v 的 [Harmonic_not_MComplete]），单位不是可逆的。它的逆会将嵌入缺失的点（Instance/Met/Completion.v 的 [Completion_Harmonic_adds_a_point]）发送到一个其像是该点的点，而单位应用于一个点就是它的常数序列（[completionU_unit_pointwise]）。
*)
Theorem completionU_unit_Harmonic_not_iso@{u +| Set < u +} :
  IsIsomorphism
    (@unit _ _ _ _ completionU_adj (Harmonic : MetU@{u Set})) → False.
Proof.
  intros [g Hfg _].
  destruct Completion_Harmonic_adds_a_point as [z Hz].
  exact (Hz (umap g z) (Hfg z)).
Qed.
