Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Reals.Rseries.
Require Import Coq.Reals.SeqProp.
Require Import Coq.Reals.Rcomplete.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.

Generalizable All Variables.

Open Scope R_scope.

(* * * Metric spaces, isometries, and the complete ones / * * 度量空间、等距映射以及完备空间 *)

(*
 nLab:      https://ncatlab.org/nlab/show/metric+space
 nLab:      https://ncatlab.org/nlab/show/complete+metric+space
 nLab:      https://ncatlab.org/nlab/show/Cauchy+sequence
 Wikipedia: https://en.wikipedia.org/wiki/Metric_space
 Wikipedia: https://en.wikipedia.org/wiki/Complete_metric_space
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 GTM 5, §III.1, printed pp. 56-57 (PDF pp. 65-66) — the
 construction this file and Instance/Met/Completion.v serve
 Book:      Fong & Spivak, "Seven Sketches in Compositionality",
 §2.3.3, Definition 2.51, printed pp. 59-60 (PDF pp. 71-72) —
 the four axioms, transcribed below
 Book:      Bishop, "Foundations of Constructive Analysis", McGraw-Hill
 1967 — the constructive discipline the moduli below follow
 Paper:     Lawvere, "Metric spaces, generalized logic, and closed
 categories", Rend. Sem. Mat. Fis. Milano 43, 1973 — the
 ROAD NOT TAKEN here; see the scope note

 ON THE CITATIONS.  No book was opened for this file, and nothing below
 quotes one; every claim about what a printed source says is a paraphrase,
 and the paraphrases of Mac Lane are taken from the in-tree book
 inventory rather than from the text.  Specifically: the §III.1 reading
 used below — "the category of metric spaces and metric-preserving
 functions (necessarily injective)", with the completion as a universal
 arrow to the inclusion of the complete ones — is
 doc/plan/books/maclane/inventory/III.json's entry
 [maclane:III.1:construction3] (book p. 56, PDF pp. 65-66), and the §IV.3
 contrast is that inventory's [maclane:IV.3:construction1] (book p. 92),
 whose summary of Mac Lane's reflective-subcategory example says "metric
 spaces with uniformly continuous maps".  The Fong & Spivak page numbers
 come from doc/plan/books/seven-sketches/pagemap.md.  A reader checking
 this file against the printed books should expect the wording to differ.

 A metric space is a set of points together with a numerical distance
 between them.  The notion is Fréchet's: his 1906 thesis "Sur quelques
 points du calcul fonctionnel" isolated what he called an *écart* — a
 symmetric, vanishing-on-the-diagonal, triangle-obeying function of two
 points — precisely so that convergence arguments from analysis could be
 run on spaces whose points are functions rather than numbers.  Hausdorff's
 "Grundzüge der Mengenlehre" (1914) named the resulting object the
 *metrischer Raum* and made it the backbone of general topology; the
 separation clause (distance zero forces equality), which Fréchet had
 assumed, is exactly what distinguishes a metric from the pseudometrics
 and the generalized distances that came later.

 COMPLETION is older than the general definition, and is the reason the
 general definition was worth making.  Cantor's 1872 construction of the
 real numbers takes Cauchy sequences of rationals and identifies two of
 them when their difference tends to zero; Hausdorff observed that the
 same recipe applies verbatim to any metric space and manufactures a
 complete space containing it.  What Mac Lane adds in §III.1 is the
 observation that the recipe is not a recipe at all but a UNIVERSAL
 PROPERTY: the embedding of a space into its completion is a universal
 arrow to the inclusion of complete spaces, so the completion is
 determined up to a unique isomorphism by a factorization property and
 not by the sequences used to build it.  That is Instance/Met/Completion.v.

 THIS FILE is the base: the four axioms, the category, and the complete
 ones as a full subcategory.

 TWO NAMES THAT ARE NOT THIS ONE.

 (1) [CauchyComplete] (Construction/Karoubi/Universal.v) is a synonym
 of [IdempotentsSplit] — CATEGORICAL Cauchy completeness, the property
 that every idempotent of a category splits.  It is a same-name trap
 and has nothing to do with the metric completeness defined here.  The
 shared word is not an accident (Lawvere's enriched reading, below,
 makes the two instances of one notion) but nothing in this file or in
 Instance/Met/Completion.v is stated in terms of it, and no theorem
 here is imported from there.  [MComplete] below is the metric notion.

 (2) LAWVERE GENERALIZED METRIC SPACES.  Lawvere's 1973 paper reads a
 metric space as a category enriched in the poset [0,∞] with addition
 as the tensor — dropping symmetry and separation, which are the two
 axioms that have no enriched counterpart.  In-tree that reading
 appears only as prose, in the background essays of
 Theory/Profunctor.v, Construction/Enriched.v, Instance/Poset.v,
 Instance/Two.v and Construction/Karoubi.v.  This file does NOT take
 that road: [MetricSpace] below is a record with a distance FUNCTION
 and Fong & Spivak's four axioms, not an [Enriched] instance, and no
 attempt is made here to identify the two presentations.  A metric
 space in this file is symmetric and separated, so it is not a
 Lawvere metric space and the enriched machinery would not apply to
 it unchanged.

 THE CODOMAIN OF THE DISTANCE is the standard library's [R].  The choice
 is forced rather than stylistic, and the header of
 Instance/Met/Completion.v gives the argument in full; in one line, the
 distance between two Cauchy sequences is the LIMIT of the distances
 between their terms, so a codomain that is not closed under limits of
 its own Cauchy sequences cannot host the completion, and the universal
 arrow would not be statable.  [Q] is not closed under such limits.  What
 is machine-checked is the forcing half — Completion.v's
 [cdist_spec]/[cdist_unique] show the completion's distance IS that limit
 and is pinned by it — while the ℚ-specific half is classical folklore
 (√2) and is labelled as ARGUED, not proved, in that file's header.

 THE AXIOM FOOTPRINT of this file is measured per constant, not sampled.
 Mentioning [R] costs nothing (the type is a definition), but any real
 ARITHMETIC costs the two standard-library axioms [sig_forall_dec] and
 [functional_extensionality_dep], and COMPLETENESS of the reals costs
 [sig_not_dec] on top.  Exactly two constants here reach for completeness:
 [R_Metric_MComplete] and the [CMet] object [R_CMet] built from it, both
 through [R_complete].  Everything else carries at most the two, and
 [R_Setoid] and [Nat_Setoid] are closed under the global context.
 Instance/Met/Completion.v, which builds the completion, necessarily
 carries all three on most of its constants; Instance/Met/Extended.v
 carries none of [sig_not_dec] at all.

 NON-NEGATIVITY IS NOT AN AXIOM HERE.  Fong & Spivak put it in the
 codomain, writing d : X × X → ℝ≥0 and then listing four conditions.  This
 file takes the codomain to be all of [R] and lists the same four
 conditions; [dist_nonneg] below then DERIVES 0 ≤ d(x,y) from them, so
 nothing is lost and the record carries one field fewer.

 THE ARROWS ARE ISOMETRIES.  Mac Lane's §III.1 says "metric spaces and
 metric-preserving functions", with the parenthetical "(necessarily
 injective)", so the arrows are the distance-PRESERVING maps
 d(fx,fy) = d(x,y) — not the short maps d(fx,fy) ≤ d(x,y), and not the
 continuous or uniformly continuous ones.  His parenthetical is
 [isometry_injective] below, proved rather than assumed, and
 [Met_all_Monic] draws the categorical consequence.  The choice matters
 for the universal property and the reader should know that Mac Lane
 himself uses a DIFFERENT category one chapter later: the §IV.3 example of
 a reflective subcategory takes metric spaces with UNIFORMLY CONTINUOUS
 maps ([maclane:IV.3:construction1]).  Both categories have the completion
 as a universal arrow — the extension of a uniformly continuous map to the
 completion is the classical statement, and an isometry is in particular
 uniformly continuous — but they are different categories with different
 hom-sets, and NO comparison between them is built here.  This file
 formalizes the §III.1 one, which is the one the issue names.
 CORRECTION (#370): "here" is this file.  The uniformly continuous
 category, [MetU], and the comparison [Met_to_MetU] (identity on
 objects, faithful, not full) are Instance/Met/Uniform.v's.

 WHAT IS DELIVERED HERE: the record [MetricSpace] (four axioms), the
 derived non-negativity and injectivity lemmas, the category [Met], a
 reusable constructor [Metric_of_injection] and the concrete spaces
 [R_Metric], [Point_Metric] and [Harmonic], the Cauchy/convergence/
 completeness vocabulary, the full subcategory [CMet] of complete spaces
 with its inclusion, the completeness of [R_Metric] and [Point_Metric],
 and the proof that [Harmonic] is NOT complete.

 WHAT IS NOT DELIVERED HERE: any limit, colimit, monoidal or enriched
 structure on [Met]; the identification of [Met] with a subcategory of
 [Top] (the metric topology is not built); short maps, uniformly
 continuous maps, or any category of metric spaces other than the
 isometric one.  The completion itself is Instance/Met/Completion.v and
 extended metric spaces are Instance/Met/Extended.v.  CORRECTION (#370):
 the uniformly continuous maps are Instance/Met/Uniform.v's [MetU];
 short maps are still not built. 

 --------
 nLab：       https://ncatlab.org/nlab/show/metric+space 
 nLab：       https://ncatlab.org/nlab/show/complete+metric+space 
 nLab：       https://ncatlab.org/nlab/show/Cauchy+sequence 
 维基百科：  https://en.wikipedia.org/wiki/Metric_space 
 维基百科：  https://en.wikipedia.org/wiki/Complete_metric_space 
 书籍：      Mac Lane，《为工作数学家准备的范畴论》，第二版，GTM 5，第III.1节，印刷页56-57（PDF页65-66）——本文件及Instance/Met/Completion.v所采用的构造
 书籍：      Fong & Spivak，《组合性中的七个草图》，§2.3.3，第2.51定义，印刷页59-60（PDF页71-72）——下面转录的四条公理
 书籍：      Bishop，《构造分析的基础》，McGraw-Hill 1967——下面模量遵循的构造性学科
 论文：      Lawvere，《度量空间、广义逻辑与闭范畴》，Rend. Sem. Mat. Fis.米兰43，1973——这里未采用的道路；参见范围说明关于引用。本文件没有查阅任何书籍，下面的内容也没有引用任何书籍；关于印刷资料内容的每一个说法都是转述，而对 Mac Lane 的转述来源于书籍库存，而非原文。具体而言：下面使用的 §III.1 阅读——“度量空间及保持度量函数（必然为单射）的范畴”，其完成作为到完全度量空间包含的普遍箭头——来自 doc/plan/books/maclane/inventory/III.json 中的条目 [maclane:III.1:construction3]（书页 56，PDF 页 65-66）；而 §IV.3 对比则来自该库存的 [maclane:IV.3:construction1]（书页 92），其中对 Mac Lane 反射子范例的总结为“具有一致连续映射的度量空间”。Fong & Spivak 的页码来自 doc/plan/books/seven-sketches/pagemap.md。读者在将此文件与印刷书籍进行核对时，应预期措辞会有所不同。度量空间是带有数值距离的一组点。这个概念来自Fréchet：他在1906年的论文《论函数分析的若干点》中提出了他所谓的*écart*——一个对称的、在对角线上为零的、遵守三角不等式的两点函数——其目的是为了使分析中的收敛性论证可以在以函数为点而不是数字的空间中进行。Hausdorff在《集合论基础》(1914)中将所得对象命名为*metrischer Raum*，并使其成为一般拓扑学的基础；分离条件（距离为零则点相等），正是Fréchet所假设的，它正好区分了度量与后来的拟度量及广义距离。完备性比一般定义更早，而且是一般定义值得提出的原因。康托尔在1872年构造实数的方法是取有理数的柯西序列，当两个序列的差趋于零时，将它们视为相同；豪斯多夫观察到，同样的方法可以完全照搬到任何度量空间，并构造一个包含它的完备空间。Mac Lane在§III.1中补充的是，这一方案根本不是一个普通的方案，而是一个普遍性质（UNIVERSAL PROPERTY）：一个空间嵌入其完备空间是完备空间包含的一个普遍箭头，因此完备性由分解性质决定，最多由唯一同构确定，而不是由用于构建它的序列决定。这就是Instance/Met/Completion.v。该文件是基础：四条公理、范畴，以及作为完全子范畴的完整范畴。

 两个不是这个名字的名称。

 (1) [CauchyComplete]（Construction/Karoubi/Universal.v）是 [IdempotentsSplit] 的同义词——范畴的柯西完备性，即每个幂等元在范畴中可以分裂。它是同名陷阱，与此处定义的度量完备性无关。共享的词汇并非偶然（下文 Lawvere 的丰富解读将两个实例视作同一概念），但该文件或 Instance/Met/Completion.v 中都没有用它来表述任何内容，而且这里没有引入任何来自那里的定理。下面的 [MComplete] 是度量概念。(2) LAWVERE 广义度量空间。Lawvere 1973 年的论文将度量空间解读为在序集 [0,∞] 中强化的范畴，其中以加法作为张量——省略了对称性和分离性，这是两个没有强化对应的公理。在 Theory/Profunctor.v、Construction/Enriched.v、Instance/Poset.v、Instance/Two.v 和 Construction/Karoubi.v 的背景文章中，这种解读仅以文字形式出现。该文件没有采用那条路：下面的 [MetricSpace] 是一个带有距离函数和 Fong & Spivak 的四条公理的记录，而不是 [Enriched] 的实例，并且这里没有尝试去识别这两种呈现方式。此文件中的度量空间是对称且分离的，因此它不是 Lawvere 度量空间，丰富的工具也无法直接应用于它。距离的余域是标准库的 [R]。这个选择是被迫的，而不是出于风格考虑，Instance/Met/Completion.v 的头文件给出了完整的论证；一句话来说，两个柯西序列之间的距离是它们项之间距离的极限，因此如果一个余域在其自身柯西序列的极限下不封闭，就无法承载完备化，并且通用箭头也无法表述。[Q] 在这种极限下不封闭。经过机器检查的部分是被迫的一半——Completion.v 的 [cdist_spec] / [cdist_unique] 展示了完备化的距离确实是该极限，并且由它固定——而特定于有理数 ℚ 的另一半是经典传说 (√2)，并在该文件头部标注为 ARGUED，而非证明。该文件的公理足迹是按常量测量的，而不是抽样的。
 提到 [R] 不会产生任何成本（该类型是一个定义），但是任何实际的算术运算都会消耗两个标准库公理 [sig_forall_dec] 和 [functional_extensionality_dep]，而实数的完备性则额外消耗 [sig_not_dec]。这里恰好有两个常量涉及完备性：[R_Metric_MComplete] 和由它构建的 [CMet] 对象 [R_CMet]，都是通过 [R_complete] 实现的。其他所有内容最多携带这两个，[R_Setoid] 和 [Nat_Setoid] 在全局上下文中是封闭的。Instance/Met/Completion.v 构建完备性时，大多数常量必然携带这三个公理；Instance/Met/Extended.v 完全不携带 [sig_not_dec]。非负性在这里不是公理。Fong 和 Spivak 将其放在值域中，写作 d : X × X → ℝ≥0，然后列出四个条件。这个文件将值域取为整个 [R]，并列出相同的四个条件；下面的 [dist_nonneg] 然后从它们推导出 0 ≤ d(x,y)，所以没有任何损失，并且记录少了一个字段。箭头是等距映射。Mac Lane 的 §III.1 说“度量空间和保持度量的函数”，并加了括号说明“（必然是单射）”，所以箭头是保持距离的映射 d(fx,fy) = d(x,y) —— 而不是满足 d(fx,fy) ≤ d(x,y) 的短映射，也不是连续或一致连续的映射。他的括号内容在下面的 [isometry_injective] 中是被证明的而非假定的，[Met_all_Monic] 推导出了范畴上的结果。这个选择对泛性质很重要，读者应该知道 Mac Lane 自己在后一章使用了不同的范畴：§IV.3 中的反射子范畴示例使用的是带一致连续映射的度量空间（[maclane:IV.3:construction1]）。两类都有作为普适箭头的完备性——将一致连续映射扩展到完备性的映射是经典说法，并且一个等距映射尤其是一致连续的——但它们是不同的范畴，具有不同的 Hom 集，并且这里没有建立它们之间的比较。这个文件形式化了 §III.1 的那一类，也就是问题中提到的那一类。更正 (#370)："这里"指的是这个文件。一致连续范畴 [MetU] 以及比较 [Met_to_MetU]（对象上为恒等，忠实，但非满射）属于 Instance/Met/Uniform.v。此处提供的内容：记录 [MetricSpace]（四条公理）、推导出的非负性和单射性引理、范畴 [Met]、可重用构造器 [Metric_of_injection]，以及具体空间 [R_Metric]、[Point_Metric] 和 [Harmonic]，柯西/收敛/完备性词汇，完备空间的全子范畴 [CMet] 及其包含、[R_Metric] 和 [Point_Metric] 的完备性，以及证明 [Harmonic] 非完备。这里没有提供的内容：在 [Met] 上的任何极限、余极限、单体或丰富结构；将 [Met] 与 [Top] 的子范畴进行识别（度量拓扑未建立）；短映射、均匀连续映射，或除等距映射之外的任何度量空间范畴。完成本身是 Instance/Met/Completion.v，扩展的度量空间是 Instance/Met/Extended.v。更正（#370）：均匀连续映射是 Instance/Met/Uniform.v 的 [MetU]；短映射仍未建立。
*)

(* * ** A missing standard-library step / * ** 缺失的标准库步骤 *)

(*
 [Rabs_no_R0] states the contrapositive; the standard library has no
 direct form, and the round trip through it needs the decidability of
 equality on [R] ([Req_dec], itself a consequence of [total_order_T]). 

 --------
 [Rabs_no_R0] 陈述了逆否命题；标准库没有直接形式，通过它的往返需要 [R] 上的等式可判定性（[Req_dec]，本身是 [total_order_T] 的一个结果）。
*)
Lemma Rabs_zero_inv (r : R) : Rabs r = 0 → r = 0.
Proof.
  intro Hr.
  destruct (Req_dec r 0) as [Hz | Hnz]; [ exact Hz |].
  now apply Rabs_no_R0 in Hnz.
Qed.

(** ** The four axioms / ** 四条公理 *)

(*
 Fong & Spivak, Definition 2.51, clause for clause.  [dist_proper] is the
 setoid bookkeeping that a Bishop-set presentation needs and that a
 set-level presentation does not state: the distance must not distinguish
 points the carrier's own equality has already identified.  Equality of
 distances is Coq's [=] because distances are real numbers, not morphisms;
 the `≈`-never-`=` discipline of this library governs its HOMS, and the
 hom-setoid of [Met] below is pointwise `≈` in the standard way. 

 --------
 Fong & Spivak，第2.51条定义，逐条说明。[dist_proper] 是 Bishop 集表示所需的集合体记账，而集合级表示则不需要声明：距离不得区分载体自身已经辨识出的点。距离的相等性是 Coq 的 [=]，因为距离是实数，而不是态射；本库的 `≈` -绝不- `=` 规则管理其 HOMS，下面的 [Met] 的同态集合体以标准方式按点 `≈`。
*)
Record MetricSpace@{o} := {
  met_carrier :> SetoidObject@{o o};      (* the setoid of points / 点的集合体 *)

  dist : met_carrier → met_carrier → R;   (* the distance / 距离 *)

  (* the distance respects the carrier's own equality / 距离尊重承运人的自身平等 *)
  dist_proper : ∀ x x' y y', x ≈ x' → y ≈ y' → dist x y = dist x' y';

  (* (a) zero self-distance / (a) 零自我距离 *)
  dist_refl : ∀ x, dist x x = 0;

  (* (b) separation / (b) 分离 *)
  dist_separates : ∀ x y, dist x y = 0 → x ≈ y;

  (* (c) symmetry / (c) 对称 *)
  dist_sym : ∀ x y, dist x y = dist y x;

  (* (d) the triangle inequality / (d) 三角不等式 *)
  dist_triangle : ∀ x y z, dist x z <= dist x y + dist y z
}.

Arguments dist {X} _ _ : rename.
Arguments dist_proper {X} _ _ _ _ _ _ : rename.
Arguments dist_refl {X} _ : rename.
Arguments dist_separates {X} _ _ _ : rename.
Arguments dist_sym {X} _ _ : rename.
Arguments dist_triangle {X} _ _ _ : rename.

(* * ** What the four axioms already give / * ** 四条公理已经提供的内容 *)

(*
 Non-negativity, which Fong & Spivak build into the codomain: run the
 triangle inequality from x to x through y, then use symmetry and the
 vanishing diagonal to read 0 ≤ 2 d(x,y). 

 --------
 非负性，这是 Fong 和 Spivak 在陪域中引入的：通过 y 从 x 到 x 运行三角不等式，然后利用对称性和消失的对角线得到 0 ≤ 2 d(x,y)。
*)
Lemma dist_nonneg {X : MetricSpace} (x y : X) : 0 <= dist x y.
Proof.
  pose proof (dist_triangle x y x) as H.
  rewrite (dist_refl x), (dist_sym y x) in H.
  lra.
Qed.

(* The converse of [dist_separates]: equal points are at distance zero. This is [dist_proper] against [dist_refl], and it is used constantly. / [dist_separates] 的逆命题：相等的点之间的距离为零。 这是 [dist_proper] 对 [dist_refl]，并且它被经常使用。 *)
Lemma dist_eq_zero {X : MetricSpace} (x y : X) : x ≈ y → dist x y = 0.
Proof.
  intro Hxy.
  rewrite (dist_proper x x y x (reflexivity x) (symmetry Hxy)).
  apply dist_refl.
Qed.

(* Distance vanishes exactly on the diagonal of the carrier's own equality: the two separation clauses packaged together. / 距离恰好在承运人自身平等的对角线上消失：两个分离条款捆绑在一起。 *)
Lemma dist_zero_iff {X : MetricSpace} (x y : X) : dist x y = 0 ↔ x ≈ y.
Proof.
  split.
  - apply dist_separates.
  - apply dist_eq_zero.
Qed.

(*
 The quadrilateral (or "four-point") inequality: distances differ by no
 more than their endpoints do.  This is the estimate that makes the
 distance function itself uniformly continuous, and it is what
 Instance/Met/Completion.v runs on — it is the reason the sequence of
 distances between two Cauchy sequences is itself Cauchy. 

 --------
 四边形（或“四点”）不等式：距离的差异不超过它们端点的差异。这是使距离函数本身一致连续的估计，也是 Instance/Met/Completion.v 运行的依据——它是两条柯西序列之间距离序列本身是柯西序列的原因。
*)
Lemma dist_quadrilateral {X : MetricSpace} (x x' y y' : X) :
  Rabs (dist x y - dist x' y') <= dist x x' + dist y y'.
Proof.
  apply Rabs_le; split.
  - pose proof (dist_triangle x' x y') as H1.
    pose proof (dist_triangle x y y') as H2.
    rewrite (dist_sym x' x) in H1.
    lra.
  - pose proof (dist_triangle x x' y) as H1.
    pose proof (dist_triangle x' y' y) as H2.
    rewrite (dist_sym y' y) in H2.
    lra.
Qed.

(** ** Isometries / ** 等距变换 *)

(*
 Mac Lane's arrows: maps that PRESERVE the distance.  The underlying map
 is a [SetoidMorphism], so it already respects the two carriers'
 equalities; distance preservation is the extra metric condition.  This is
 the same layering [Top] uses for continuity (Instance/Top.v). 

 --------
 Mac Lane的箭头：保持距离的映射。底层映射是一个[SetoidMorphism]，所以它已经满足两个承载体的等式；距离保持是额外的度量条件。这就是[Top]用于连续性的相同分层（Instance/Top.v）。
*)
Record Isometry (X Y : MetricSpace) := {
  isometry_map :> SetoidMorphism (met_carrier X) (met_carrier Y);
  isometry_dist : ∀ x y : X, dist (isometry_map x) (isometry_map y) = dist x y
}.

Arguments isometry_map {X Y} _.
Arguments isometry_dist {X Y} _ _ _.

(*
 Mac Lane's parenthetical "(necessarily injective)", proved.  If two
 points have equal images then their images are at distance zero, so the
 points are, so they are equal.  Note where each axiom enters:
 [dist_eq_zero] on the codomain, [isometry_dist] to transport, and
 [dist_separates] on the domain. 

 --------
 麦克·莱恩的括号部分“（必然是单射）”已被证明。如果两点的像相等，那么它们的像的距离为零，因此这些点的距离也为零，所以它们相等。请注意每个公理的作用：[dist_eq_zero] 在陪域上，[isometry_dist] 在传递上，[dist_separates] 在定义域上。
*)
Lemma isometry_injective {X Y : MetricSpace} (f : Isometry X Y) (x y : X) :
  isometry_map f x ≈ isometry_map f y → x ≈ y.
Proof.
  intro Hf.
  apply dist_separates.
  rewrite <- (isometry_dist f x y).
  now apply dist_eq_zero.
Qed.

(** ** The category Met / ** 类别 Met *)

(*
 The hom-setoid compares only the map part, pointwise up to the
 codomain's `≈`; the distance-preservation witness is not compared.  Two
 isometries that agree on points are the same arrow of [Met], whatever
 proofs they carry — the extensional discipline of [SetoidMorphism_equiv],
 and what makes [Met] a category with no proof-irrelevance axiom. 

 --------
 同构集只比较映射部分，在余域的 `≈` 下逐点比较；保持距离的证据不进行比较。两个在点上相同的等距映射是 [Met] 的相同箭头，无论它们携带什么证明——这是 [SetoidMorphism_equiv] 的外延规律，并且使得 [Met] 成为一个没有证明无关公理的范畴。
*)
Definition Isometry_equiv {X Y : MetricSpace} : crelation (Isometry X Y) :=
  fun f g => ∀ x : X, isometry_map f x ≈ isometry_map g x.

Arguments Isometry_equiv {X Y} _ _ /.

#[export]
Program Instance Isometry_Setoid {X Y : MetricSpace} :
  Setoid (Isometry X Y) := {| equiv := Isometry_equiv |}.
Next Obligation.
  constructor.
  - intros f x; reflexivity.
  - intros f g Hfg x; symmetry; exact (Hfg x).
  - intros f g h Hfg Hgh x; transitivity (isometry_map g x).
    + exact (Hfg x).
    + exact (Hgh x).
Qed.

Definition met_id {X : MetricSpace} : Isometry X X := {|
  isometry_map  := setoid_morphism_id;
  isometry_dist := fun x y => eq_refl
|}.

Definition met_compose {X Y Z : MetricSpace}
           (g : Isometry Y Z) (f : Isometry X Y) : Isometry X Z := {|
  isometry_map  := setoid_morphism_compose g f;
  isometry_dist := fun x y =>
    eq_trans (isometry_dist g (f x) (f y)) (isometry_dist f x y)
|}.

Lemma met_compose_respects {X Y Z : MetricSpace} :
  Proper (equiv ==> equiv ==> equiv) (@met_compose X Y Z).
Proof.
  intros g1 g2 Hg f1 f2 Hf x; simpl.
  rewrite (Hg (isometry_map f1 x)).
  apply proper_morphism, Hf.
Qed.

(*
 The category of metric spaces and metric-preserving maps.  The category
 laws hold pointwise on the map parts exactly as in [Sets]; the
 distance-preservation witnesses play no part, the hom-setoid ignoring
 them. 

 --------
 度量空间及保持度量映射的范畴。范畴定律在映射部分逐点成立，正如在 [Sets] 中一样；保持距离的证明不起作用，同态集体忽略它们。
*)
Program Definition Met : Category := {|
  obj     := MetricSpace;
  hom     := Isometry;
  homset  := @Isometry_Setoid;
  id      := @met_id;
  compose := @met_compose;

  compose_respects := @met_compose_respects
|}.

(*
 Every arrow of [Met] is monic — the categorical shadow of Mac Lane's
 parenthetical.  This makes [Met] a rather rigid category and is worth
 saying out loud: it is NOT a claim that [Met] is balanced, and no
 converse is proved here. 

 --------
 [Met] 的每一个箭头都是单射 — 是 Mac Lane 括号的范畴阴影。这使得 [Met] 成为一个相当刚性的范畴，值得大声说出来：这并不是说 [Met] 是平衡的，而且这里也没有证明其逆命题。
*)
Lemma Met_all_Monic {X Y : Met} (f : X ~> Y) : Monic f.
Proof.
  constructor; intros z g1 g2 Hg x.
  exact (isometry_injective f (isometry_map g1 x) (isometry_map g2 x) (Hg x)).
Qed.

(*
 The forgetful functor to setoids.  It is faithful by construction: the
 hom-setoid of [Met] IS pointwise `≈` of the underlying maps, so
 faithfulness is the identity implication, exactly as
 Construction/Subcategory.v's [Incl_Faithful] is. 

 --------
 到集合等价类的遗忘函子。它在构造上是忠实的：[Met] 的同态等价类是底层映射的逐点 `≈`，因此忠实性就是恒等映射的蕴含，正如 Construction/Subcategory.v 中的 [Incl_Faithful] 一样。
*)
Program Definition Met_Forget : Met ⟶ Sets := {|
  fobj := met_carrier;
  fmap := fun _ _ f => isometry_map f
|}.

Lemma Met_Forget_Faithful : Faithful Met_Forget.
Proof. constructor; intros x y f g H; exact H. Qed.

(** ** Building metric spaces / ** 构建度量空间 *)

(*
 Every injection into the reals is a metric.  This is the cheapest source
 of concrete examples and it is used three times below.  The two
 hypotheses are exactly the two halves of "[f] is injective on the
 setoid": [f_proper] makes the distance well defined, [f_injective] is
 what buys separation. 

 --------
 每一个注入实数的映射都是一种度量。这是最廉价的具体例子来源，下面使用了三次。这两个假设正好是“[f]在集合准则上是单射”的两个部分：[f_proper] 使得距离定义良好，[f_injective] 则保证了分离性。
*)
Section OfInjection.

(* The five lemmas below genuinely depend on the section variables; [Lib.v] sets [Default Proof Using "Type"], which would discard them. Same reason, same remedy, as Instance/Top/Interval.v. / 下面的五个引理确实依赖于节变量；[Lib.v] 设置了 [Default Proof Using "Type"]，这会丢弃它们。同样的原因，同样的解决方法，如 Instance/Top/Interval.v。 *)
Local Set Default Proof Using "All".

Context (A : SetoidObject).
Context (f : A → R).
Context (f_proper : ∀ x y : A, x ≈ y → f x = f y).
Context (f_injective : ∀ x y : A, f x = f y → x ≈ y).

Let inj_dist (x y : A) : R := Rabs (f x - f y).

Lemma inj_proper : ∀ x x' y y', x ≈ x' → y ≈ y' → inj_dist x y = inj_dist x' y'.
Proof.
  intros a b c d Hab Hcd; unfold inj_dist.
  now rewrite (f_proper _ _ Hab), (f_proper _ _ Hcd).
Qed.

Lemma inj_refl : ∀ x, inj_dist x x = 0.
Proof.
  intro a; unfold inj_dist.
  replace (f a - f a) with 0 by ring.
  exact Rabs_R0.
Qed.

Lemma inj_separates : ∀ x y, inj_dist x y = 0 → x ≈ y.
Proof.
  intros a b Hab; unfold inj_dist in Hab.
  apply f_injective, Rminus_diag_uniq.
  now apply Rabs_zero_inv.
Qed.

Lemma inj_sym : ∀ x y, inj_dist x y = inj_dist y x.
Proof. intros a b; apply Rabs_minus_sym. Qed.

Lemma inj_triangle : ∀ x y z, inj_dist x z <= inj_dist x y + inj_dist y z.
Proof.
  intros a b c; unfold inj_dist.
  replace (f a - f c) with ((f a - f b) + (f b - f c)) by ring.
  apply Rabs_triang.
Qed.

Definition Metric_of_injection : MetricSpace :=
  {| met_carrier    := A;
     dist           := inj_dist;
     dist_proper    := inj_proper;
     dist_refl      := inj_refl;
     dist_separates := inj_separates;
     dist_sym       := inj_sym;
     dist_triangle  := inj_triangle |}.

End OfInjection.

Arguments Metric_of_injection A f f_proper f_injective : clear implicits.

(* The real line. Its carrier is [R] under Leibniz equality. / 实数直线。它的承载体是在莱布尼茨等式下的 [R]。 *)
Definition R_Setoid : SetoidObject :=
  {| carrier := R; is_setoid := {| equiv := @eq R |} |}.

Definition R_Metric : MetricSpace :=
  Metric_of_injection R_Setoid (fun r => r)
    (fun x y H => H) (fun x y H => H).

(* Distance on [R_Metric] is the absolute difference, by conversion. This is the [eq_refl] exception: it is a statement about definitional unfolding, not about `≈`. / 在 [R_Metric] 上的距离是通过转换得到的绝对差值。这是 [eq_refl] 的例外：它是关于定义展开的陈述，而不是关于 `≈` 的。 *)
Example R_Metric_dist (x y : R_Metric) : dist x y = Rabs (x - y) := eq_refl.

(* The one-point space, over the singleton setoid [Sets_Terminal] uses. Everything is at distance zero from everything, and separation holds because the carrier has one element. / 一元空间，在单元素集合等价类 [Sets_Terminal] 上使用。所有点之间的距离都是零，分离性成立，因为承载集合只有一个元素。 *)
Definition Point_Metric : MetricSpace :=
  {| met_carrier    := unit_setoid_object;
     dist           := fun _ _ => 0;
     dist_proper    := fun _ _ _ _ _ _ => eq_refl;
     dist_refl      := fun _ => eq_refl;
     dist_separates := fun x y _ =>
       match x, y with ttt, ttt => reflexivity ttt end;
     dist_sym       := fun _ _ => eq_refl;
     dist_triangle  := fun _ _ _ => Rplus_le_le_0_compat 0 0 (Rle_refl 0) (Rle_refl 0) |}.

(** ** A concrete incomplete space / ** 一个具体的不完整空间 *)

(*
 The harmonic space: the natural numbers, with n placed at 1/(n+1) on the
 real line.  It is a metric space by [Metric_of_injection], it is NOT
 complete ([Harmonic_not_MComplete] below), and its completion adds
 exactly the missing limit point 0 — which is what makes
 Instance/Met/Completion.v's non-vacuity witness concrete rather than
 nominal.  The carrier is [nat] itself, so no subsetoid machinery is
 needed anywhere. 

 --------
 谐波空间：自然数，其中 n 被放置在实线上 1/(n+1) 的位置。通过 [Metric_of_injection] 它是一个度量空间，但它不是完全的（见下文的 [Harmonic_not_MComplete]），其完备化恰好添加了缺失的极限点 0——这使得 Instance/Met/Completion.v 中的非空性证据是具体的，而不是名义上的。载体是 [nat] 本身，因此任何地方都不需要子集体机制。
*)
Definition harm (n : nat) : R := / (INR n + 1).

Lemma harm_pos (n : nat) : 0 < harm n.
Proof.
  apply Rinv_0_lt_compat.
  pose proof (pos_INR n); lra.
Qed.

Lemma harm_injective (m n : nat) : harm m = harm n → m = n.
Proof.
  unfold harm; intro H.
  pose proof (pos_INR m); pose proof (pos_INR n).
  assert (INR m + 1 = INR n + 1) as H'.
  { rewrite <- (Rinv_inv (INR m + 1)), <- (Rinv_inv (INR n + 1)).
    now rewrite H. }
  apply INR_eq; lra.
Qed.

Definition Nat_Setoid : SetoidObject :=
  {| carrier := nat; is_setoid := {| equiv := @eq nat |} |}.

Definition Harmonic : MetricSpace :=
  Metric_of_injection Nat_Setoid harm
    (fun x y H => f_equal harm H)
    (fun x y H => harm_injective x y H).

(* * ** Cauchy sequences, limits, completeness / * ** 柯西序列，极限，完备性 *)

(*
 THE MODULUS IS DATA.  This library's `∃` is [sigT] (Lib/Foundation.v,
 66), so [MCauchy] below is TYPE-valued and a Cauchy sequence hands out
 its threshold N as a function of ε rather than merely asserting that one
 exists.  That is not decoration: Instance/Met/Completion.v proves the
 completion complete by a diagonal argument that CONSUMES one threshold
 per index, and extracting a sequence of thresholds from a sequence of
 Prop-level existentials is countable choice.  With the modulus as data no
 choice principle is used anywhere in this development.

 The reading is Bishop's, and it is worth being precise about its
 strength: "every sequence PRESENTED WITH A MODULUS converges" is
 constructively weaker than the classical "every Cauchy sequence
 converges", the two being interderivable only via countable choice.
 [MComplete] is the former.  No claim is made here that the two agree.

 THE DIRECTION MATTERS, in both places the notion is used.  Because
 [MComplete] is the WEAKER property, PROVING it — as
 [Completion_MComplete] does — is the weaker positive statement, while
 REFUTING it — as [Harmonic_not_MComplete] does — is the STRONGER negative
 one: the witnessing sequence [fun n => n] carries an explicit modulus
 ([harm_seq_MCauchy]), so the harmonic space is incomplete already in this
 restricted sense and therefore in the classical sense as well.

 Note also that the BODY of each `∃` is a Prop ([Rlt] is Prop-valued), so
 a threshold, once produced, may be shown to work by any Prop-level
 reasoning whatever — which is how [R_Metric_MComplete] below bridges to
 the standard library's Prop-valued [Un_cv]. 

 --------
 模量是数据。这个库的 `∃` 是 [sigT] （Lib/Foundation.v, 66），所以下面的 [MCauchy] 是类型值，并且一个柯西序列将其阈值 N 作为 ε 的函数给出，而不仅仅是断言存在。这不是装饰：Instance/Met/Completion.v 使用对角论证证明了完备性，这种论证在每个索引上消耗一个阈值，而从 Prop 级存在性序列中提取阈值序列需要可数选择。有了作为数据的模量，这个开发中在任何地方都没有使用选择原理。阅读材料是Bishop的，并且值得精确说明它的强度：“每个带模的序列都收敛”在构造上比经典的“每个柯西序列都收敛”要弱，它们只能通过可数选择相互推导。[MComplete] 是前者。这里没有声称两者相同。

 方向很重要，在使用该概念的两个地方都是如此。因为 [MComplete] 是较弱的性质，所以证明它——就像 [Completion_MComplete] 做的那样——是较弱的肯定陈述，而反驳它——就像 [Harmonic_not_MComplete]那样——是较强的否定陈述：见证序列 [fun n => n] 带有明确的模 ([harm_seq_MCauchy])，因此调和空间在这种受限意义下已经不完备，因此在经典意义下也不完备。还请注意，每个 `∃` 的主体都是一个命题（[Rlt] 的值为命题），因此一旦产生阈值，就可以通过任何命题级别的推理来证明其有效性——这就是下面的 [R_Metric_MComplete] 如何桥接到标准库的命题值 [Un_cv] 的方式。
*)

Definition MCauchy (X : MetricSpace) (u : nat → X) : Type :=
  ∀ eps : R, 0 < eps →
    ∃ N : nat, ∀ m n : nat, (N <= m)%nat → (N <= n)%nat → dist (u m) (u n) < eps.

Definition MConverges (X : MetricSpace) (u : nat → X) (l : X) : Type :=
  ∀ eps : R, 0 < eps →
    ∃ N : nat, ∀ n : nat, (N <= n)%nat → dist (u n) l < eps.

Definition MComplete (X : MetricSpace) : Type :=
  ∀ u : nat → X, MCauchy X u → ∃ l : X, MConverges X u l.

(* Limits are unique up to the carrier's own equality. This is where separation earns its place among the axioms: without it a sequence could converge to two genuinely different points. / 极限在载体自身的等价性下是唯一的。这就是分离性在公理中占有一席之地的原因：没有它，一个序列可能会收敛到两个真正不同的点。 *)
Lemma MConverges_unique {X : MetricSpace} (u : nat → X) (l l' : X) :
  MConverges X u l → MConverges X u l' → l ≈ l'.
Proof.
  intros Hl Hl'.
  apply dist_separates.
  (* 0 ≤ d(l,l') and d(l,l') < ε for every ε > 0, hence d(l,l') = 0. / 0 ≤ d(l,l') 并且对于每个 ε > 0 都有 d(l,l') < ε，因此 d(l,l') = 0。 *)
  assert (∀ eps : R, 0 < eps → dist l l' < eps) as Hsmall.
  { intros eps Heps.
    destruct (Hl (eps / 2) ltac:(lra)) as [N1 HN1].
    destruct (Hl' (eps / 2) ltac:(lra)) as [N2 HN2].
    pose (n := Nat.max N1 N2).
    specialize (HN1 n (Nat.le_max_l N1 N2)).
    specialize (HN2 n (Nat.le_max_r N1 N2)).
    pose proof (dist_triangle l (u n) l') as Htri.
    rewrite (dist_sym l (u n)) in Htri.
    lra. }
  pose proof (dist_nonneg l l') as Hpos.
  destruct (Rle_lt_or_eq_dec 0 (dist l l') Hpos) as [Hlt | Heq].
  - exfalso. specialize (Hsmall (dist l l') Hlt). lra.
  - now symmetry.
Qed.

(* A convergent sequence is Cauchy. The Cauchy modulus is produced from the convergence modulus at ε/2 — data from data, no choice. / 收敛序列是柯西序列。柯西模量由 ε/2 的收敛模量产生——数据来源于数据，没有选择。 *)
Lemma MConverges_MCauchy {X : MetricSpace} (u : nat → X) (l : X) :
  MConverges X u l → MCauchy X u.
Proof.
  intros Hl eps Heps.
  destruct (Hl (eps / 2) ltac:(lra)) as [N HN].
  exists N; intros m n Hm Hn.
  pose proof (dist_triangle (u m) l (u n)) as Htri.
  rewrite (dist_sym l (u n)) in Htri.
  pose proof (HN m Hm) as H1.
  pose proof (HN n Hn) as H2.
  lra.
Qed.

(*
 An isometry carries Cauchy sequences to Cauchy sequences and limits to
 limits, on the nose: the ε and the threshold are unchanged, because the
 distances themselves are unchanged.  Both are used by the completion's
 universal property. 

 --------
 等距映射将柯西序列映射为柯西序列，将极限映射为极限，完全一致：ε 和阈值保持不变，因为距离本身没有变化。两者都被完备化的普适性质所使用。
*)
Lemma isometry_MCauchy {X Y : MetricSpace} (f : Isometry X Y) (u : nat → X) :
  MCauchy X u → MCauchy Y (fun n => isometry_map f (u n)).
Proof.
  intros Hu eps Heps.
  destruct (Hu eps Heps) as [N HN].
  exists N; intros m n Hm Hn.
  rewrite (isometry_dist f (u m) (u n)).
  now apply HN.
Qed.

Lemma isometry_MConverges {X Y : MetricSpace} (f : Isometry X Y)
      (u : nat → X) (l : X) :
  MConverges X u l → MConverges Y (fun n => isometry_map f (u n)) (isometry_map f l).
Proof.
  intros Hu eps Heps.
  destruct (Hu eps Heps) as [N HN].
  exists N; intros n Hn.
  rewrite (isometry_dist f (u n) l).
  now apply HN.
Qed.

(* * ** The full subcategory of complete spaces / * ** 完备空间的全子范畴 *)

(*
 Written with [Build_Subcategory] rather than [Program] for the reason
 Construction/Subcategory/Terminal.v gives: obligations discharged by
 [Qed] are opaque to the unifier, and [shom] here has to reduce. 

 --------
 使用 [Build_Subcategory] 而不是 [Program] 编写，原因是 Construction/Subcategory/Terminal.v 显示：由 [Qed] 履行的义务对统一器是不透明的，而此处的 [shom] 必须被化简。
*)
Definition CompleteSpaces : Subcategory Met :=
  @Build_Subcategory Met
    (fun X => MComplete X)              (* the complete spaces / 完整的空间 *)
    (fun _ _ _ _ _ => True)             (* full: every isometry is kept / 完全：每一个等距映射都被保留 *)
    (fun _ _ _ _ _ _ _ _ _ _ => I)      (* closed under composition / 在复合运算下封闭 *)
    (fun _ _ => I).                     (* closed under identities / 在恒等式下封闭 *)

Definition CMet : Category := Sub Met CompleteSpaces.

Definition CMet_Incl : CMet ⟶ Met := Incl Met CompleteSpaces.

Definition CMet_Full : Construction.Subcategory.Full Met CompleteSpaces :=
  fun _ _ _ _ _ => I.

Definition CMet_Incl_Faithful : Faithful CMet_Incl :=
  Incl_Faithful Met CompleteSpaces.

Definition CMet_Incl_Full : Functor.Full CMet_Incl :=
  Full_Implies_Full_Functor Met CompleteSpaces CMet_Full.

(*
 Note that an object of [CMet] is a space TOGETHER WITH a chosen
 completeness witness, [MComplete] being proof-relevant data (it computes
 limits).  Two witnesses for one space give distinct but isomorphic
 objects of [CMet]; that is [Full_membership_iso]
 (Construction/Subcategory.v) and is the standard situation for full
 subcategories in this library, not a defect of this one. 

 --------
 请注意，[CMet] 的一个对象是一个空间以及一个选定的完备性证明，[MComplete] 是证明相关的数据（它计算极限）。同一个空间的两个证明会生成 ZZ2WZZ 中不同但同构的对象；也就是说 [Full_membership_iso]（Construction/Subcategory.v）是该库中满子范畴的标准情况，而不是这个子范畴的缺陷。
*)

(* * ** Complete and incomplete witnesses / * ** 完整和不完整的证人 *)

(* The one-point space is complete: every sequence converges to the point, with threshold 0. / 一点评空间是完备的：每个序列都收敛到该点，阈值为0。 *)
Definition Point_Metric_MComplete : MComplete Point_Metric :=
  fun u _ => (ttt; fun eps Heps => (0%nat; fun n _ => Heps)).

(*
 The real line is complete.  The limit comes from the standard library's
 [R_complete]; the CONVERGENCE MODULUS is produced here from the Cauchy
 modulus at ε/2, which is data, and the inequality it has to satisfy is a
 Prop and so may be argued with the Prop-valued [Un_cv] that [R_complete]
 returns.  This is the bridge the header describes. 

 --------
 实数轴是完备的。极限来自标准库的 [R_complete]；这里的收敛模量是由 ε/2 的柯西模量生成的，这是数据，并且它必须满足的不等式是一个命题，因此可以使用 [R_complete] 返回的命题值 [Un_cv] 进行论证。这就是标题所描述的桥梁。
*)
Lemma R_Metric_MComplete : MComplete R_Metric.
Proof.
  intros u Hu.
  (* The standard library's Cauchy criterion, from our modulus. / 标准库的柯西准则，来自我们的模数。 *)
  assert (Cauchy_crit u) as Hcc.
  { intros eps Heps.
    destruct (Hu eps ltac:(lra)) as [N HN].
    exists N; intros n m Hn Hm.
    unfold R_dist.
    exact (HN n m Hn Hm). }
  destruct (R_complete u Hcc) as [l Hl].
  exists l; intros eps Heps.
  destruct (Hu (eps / 2) ltac:(lra)) as [N HN].
  exists N; intros n Hn.
  (*
 |u n - l| ≤ |u n - u m| + |u m - l| for a suitable m ≥ N chosen by the
 Prop-level convergence; the goal is a Prop, so this is legitimate. 

 --------
 |u n - l| ≤ |u n - u m| + |u m - l|，对于一个通过命题级收敛选择的合适 m ≥ N；目标是一个命题，所以这是合理的。
*)
  destruct (Hl (eps / 2) ltac:(lra)) as [M HM].
  pose (m := Nat.max N M).
  assert (R_dist (u m) l < eps / 2) as H1 by (apply HM; apply Nat.le_max_r).
  assert (dist (u n) (u m) < eps / 2) as H2
      by (apply HN; [ exact Hn | apply Nat.le_max_l ]).
  pose proof (dist_triangle (X:=R_Metric) (u n) (u m) l) as Htri.
  unfold R_dist in H1.
  change (dist (X:=R_Metric) (u m) l) with (Rabs (u m - l)) in *.
  lra.
Qed.

(* [CMet] is inhabited, twice over. / [CMet] 有两倍的人居住。 *)
Definition R_CMet : CMet := (R_Metric; R_Metric_MComplete).
Definition Point_CMet : CMet := (Point_Metric; Point_Metric_MComplete).

(* * ** The harmonic space is not complete / * ** 谐波空间不完整 *)

(* An archimedean modulus, as DATA: [up] is a function, and [archimed] is the Prop that certifies it. / 一个阿基米德模量，作为数据：[up] 是一个函数，而 [archimed] 是证明它的命题。 *)
Definition harm_mod (eps : R) : nat := Z.to_nat (up (/ eps)).

Lemma harm_antitone (m n : nat) : (m <= n)%nat → harm n <= harm m.
Proof.
  intro Hmn; unfold harm.
  apply Rinv_le_contravar.
  - pose proof (pos_INR m); lra.
  - apply Rplus_le_compat_r, le_INR, Hmn.
Qed.

Lemma harm_mod_spec (eps : R) : 0 < eps → harm (harm_mod eps) < eps.
Proof.
  intro Heps.
  assert (0 < / eps) as Hinv by (apply Rinv_0_lt_compat, Heps).
  destruct (archimed (/ eps)) as [Hup _].
  assert (0 <= up (/ eps))%Z as Hnn.
  { apply le_IZR; simpl; lra. }
  assert (INR (harm_mod eps) = IZR (up (/ eps))) as Heq.
  { unfold harm_mod. rewrite INR_IZR_INZ, Z2Nat.id by exact Hnn. reflexivity. }
  unfold harm; rewrite Heq.
  (* / eps < IZR (up (/eps)) < IZR (up (/eps)) + 1, so the reciprocal is < eps. / / eps < IZR (up (/eps)) < IZR (up (/eps)) + 1，因此其倒数 < eps。 *)
  assert (/ eps < IZR (up (/ eps)) + 1) as Hlt by lra.
  apply (Rmult_lt_reg_l (IZR (up (/ eps)) + 1)); [ lra |].
  rewrite Rinv_r by lra.
  apply (Rmult_lt_reg_r (/ eps)); [ exact Hinv |].
  rewrite Rmult_1_l, Rmult_assoc, Rinv_r by lra.
  lra.
Qed.

(*
 Past index 2l+1 the harmonic sequence has dropped below half of harm l.
 Used both here and, in Instance/Met/Completion.v, to show that the class
 of the identity sequence is not in the image of the embedding. 

 --------
 在索引 2l+1 之后，谐波序列已经下降到 harm l 的一半以下。这里使用，同时在 Instance/Met/Completion.v 中使用，以显示恒等序列的类不在嵌入的像中。
*)
Lemma harm_half (l n : nat) : (2 * l + 1 <= n)%nat → harm n <= harm l / 2.
Proof.
  intro Hn.
  transitivity (harm (2 * l + 1)); [ now apply harm_antitone |].
  unfold harm.
  rewrite plus_INR, mult_INR.
  replace (INR 2 * INR l + INR 1 + 1) with (2 * (INR l + 1)) by (simpl; lra).
  rewrite Rinv_mult.
  pose proof (pos_INR l); lra.
Qed.

(* The identity sequence of the harmonic space is Cauchy. / 调和空间的恒等序列是柯西序列。 *)
Lemma harm_seq_MCauchy : MCauchy Harmonic (fun n => n).
Proof.
  intros eps Heps.
  exists (harm_mod eps); intros m n Hm Hn.
  pose proof (harm_mod_spec eps Heps) as Hsmall.
  pose proof (harm_antitone _ _ Hm) as Hm'.
  pose proof (harm_antitone _ _ Hn) as Hn'.
  pose proof (harm_pos m); pose proof (harm_pos n).
  change (Rabs (harm m - harm n) < eps).
  apply Rabs_def1; lra.
Qed.

(* ... and it has no limit in the space. Every point k sits at 1/(k+1) > 0, while the sequence runs down to 0; taking ε = 1/(2(k+1)) and an index past 2k+1 separates them. / ... 并且它在空间中没有限制。每个点 k 位于 1/(k+1) > 0， 而该序列下降到 0；取 ε = 1/(2(k+1)) 并选择一个超过 2k+1 的索引可以将它们分开。 *)
Lemma harm_seq_no_limit (l : Harmonic) :
  MConverges Harmonic (fun n => n) l → False.
Proof.
  intro Hl.
  pose proof (harm_pos l) as Hlpos.
  destruct (Hl (harm l / 2) ltac:(lra)) as [N HN].
  pose (n := Nat.max N (2 * l + 1)).
  assert (N <= n)%nat as Hn by apply Nat.le_max_l.
  specialize (HN n Hn).
  change (Rabs (harm n - harm l) < harm l / 2) in HN.
  pose proof (harm_half l n (Nat.le_max_r N (2 * l + 1))) as Hsmall.
  pose proof (harm_pos n).
  rewrite Rabs_left1 in HN by lra.
  lra.
Qed.

Lemma Harmonic_not_MComplete : MComplete Harmonic → False.
Proof.
  intro Hc.
  destruct (Hc (fun n => n) harm_seq_MCauchy) as [l Hl].
  exact (harm_seq_no_limit l Hl).
Qed.
