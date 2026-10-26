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
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Met.

Generalizable All Variables.

Open Scope R_scope.

(* * * The completion of a metric space, as a universal arrow / * * 度量空间的完备化，作为一个通用箭头 *)

(*
 nLab:      https://ncatlab.org/nlab/show/Cauchy+complete+metric+space
 nLab:      https://ncatlab.org/nlab/show/universal+morphism
 Wikipedia: https://en.wikipedia.org/wiki/Complete_metric_space#Completion
 Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 GTM 5, §III.1, printed pp. 56-57 (PDF pp. 65-66), the
 unnumbered third construction — the theorem of this file
 Book:      Bishop, “Foundations of Constructive Analysis”, McGraw-Hill
 1967 — the modulus discipline
 Docs:      Rocq standard library, Reals (Rcomplete.R_complete,
 SeqProp.UL_sequence)

 ON THE CITATIONS.  No book was opened for this file; the account of what
 Mac Lane's §III.1 says is a paraphrase of the in-tree book inventory
 (doc/plan/books/maclane/inventory/III.json, entry
 [maclane:III.1:construction3], book p. 56, PDF pp. 65-66), not of the
 printed text.  Instance/Met.v's header carries the same disclosure and
 the fuller citation list.

 Mac Lane's §III.1 lists the completion of a metric space among the
 examples of a universal arrow, in one sentence and with no proof: with
 Met the metric spaces and metric-preserving maps and Cmet the full
 subcategory of complete ones, the embedding X → X-bar is universal from X
 to the inclusion Cmet ⟶ Met, and the general uniqueness of universal
 arrows then delivers uniqueness of the completion up to a unique
 isomorphism.  This file is that sentence, proved.

 THE CONSTRUCTION is Cantor's, from 1872, applied to an arbitrary space
 rather than to the rationals: a point of the completion is a Cauchy
 sequence, two of them are identified when the distance between their
 terms tends to zero, and the distance between two of them is the LIMIT of
 the distances between their terms.  What Mac Lane contributes is that
 none of those choices is what makes the completion the completion; the
 factorization property does, and this file's [Completion_AUniversalArrow]
 is that property while [completion_unique] is the uniqueness it forces.

 WHY THE DISTANCE IS REAL-VALUED, AND WHY THIS FILE IS THEREFORE IN THE
 INSTANCE LAYER.  The issue behind this file offers “a rational- or
 real-valued distance” and asks for the choice to be documented.  The
 choice is FORCED, and the reason is visible in the construction: the
 distance between two Cauchy sequences is a limit of distances, so the
 codomain of the metric has to contain the limits of its own Cauchy
 sequences or the completion is not an object of the category at all and
 the universal arrow is not statable.  [Q] does not contain them.

 Two halves of that argument, kept apart on purpose:

 - MACHINE-CHECKED: that the distance on the completion IS the limit and
 is PINNED by being one.  [cdist_spec] proves the sequence of
 distances converges to [cdist], and [cdist_unique] proves that any
 real to which it converges IS [cdist].  So the limit is not one
 admissible choice of distance among others — it is the only one, and
 a codomain lacking it lacks the distance.

 - ARGUED, NOT PROVED: that [Q] is not closed under such limits.  This
 is the classical folklore fact that a Cauchy sequence of rationals
 can converge to an irrational (√2), and it is NOT formalized here or
 anywhere in this tree; the standard library has no irrationality
 result to lean on.  It is stated as an argument and the reader should
 treat it as one.

 The consequence is that this file uses the standard library's [R], and so
 inherits its axioms.  That is permitted by the issue's Definition of Done
 (“if classical reals are unavoidable the file lives in the instance
 layer”) and follows the precedent of the Instance/Top/ reals files, where
 docs/AXIOMS.md prices the reals per constant.  The stratification is
 sharp, and the numbers below are MEASURED per constant rather than
 sampled.  [R_complete] is the only door through which [sig_not_dec]
 enters.  Instance/Met/Extended.v never opens it: none of its 55 constants
 carries [sig_not_dec] and five are closed outright.  Instance/Met.v opens
 it in EXACTLY TWO constants — [R_Metric_MComplete], which is where the
 completeness of the real line is proved, and [R_CMet], the object of
 [CMet] built from it — its other 61 constants carrying at most
 [sig_forall_dec] and [functional_extensionality_dep].  THIS file opens it
 in 41 of its 66 constants, everything downstream of [cdist].

 NO CHOICE PRINCIPLE IS USED BY THE CONSTRUCTIONS BELOW.  (The three
 standard-library axioms enumerated above are inherited from [R] itself and
 are not introduced here; no claim is made in this file about their
 strength.)  Instance/Met.v's [MCauchy] is Type-valued
 (this library's `∃` is [sigT]), so a Cauchy sequence carries its modulus
 as data.  That is what makes [Completion_MComplete] below constructive:
 its diagonal argument consumes one threshold per index, and reading a
 sequence of thresholds out of a sequence of Prop-level existentials would
 be countable choice.  Correspondingly [cs_equiv], the identification of
 Cauchy sequences, is Prop-valued (it is literally the standard library's
 [Un_cv] at 0), because the completion's separation axiom has to PRODUCE
 it from an equation between reals and nothing would be gained by asking
 for a modulus there.  Both directions of that seam are deliberate.

 NOTHING HERE COMPUTES, and that is worth saying because much of this tree
 does.  [cdist] is [proj1_sig] of [R_complete], whose value is not a closed
 term, so no distance in the completion evaluates and there are no
 [eq_refl] acceptance tests of the kind Instance/FinSet/ files carry.  The
 convertibility statements that ARE made below are structural (the carrier
 of the completion is the type of Cauchy sequences) rather than numeric.
 Consistently with that, the two witnesses whose type is data but whose
 value nothing inspects — [cs_diag_MCauchy] and Instance/Met.v's
 [R_Metric_MComplete] — are left [Qed]-opaque; [Completion_MComplete],
 [Completion_AUniversalArrow] and [Completion_UniversalArrow] are
 [Defined], since the universal-arrow machinery projects out of them.

 NOT [CauchyComplete].  Construction/Karoubi/Universal.v defines
 [CauchyComplete] to be [IdempotentsSplit], a property of CATEGORIES.
 This file is about complete METRIC SPACES; the two are unrelated here and
 nothing below refers to the Karoubi notion.

 WHAT IS DELIVERED: the completion [Completion X] as an object of [Met],
 its completeness [Completion_MComplete], the isometric embedding [eta],
 the density of its image, the extension [ext] of an isometry into a
 complete space, the universal arrow in BOTH of Theory/Universal/Arrow.v's
 encodings, uniqueness of the completion up to a unique compatible
 isomorphism obtained FROM that machinery rather than by hand, and a
 non-vacuity witness: the completion of Instance/Met.v's [Harmonic] has a
 point that the embedding misses.

 WHAT IS NOT DELIVERED: the completion as a FUNCTOR, and hence the
 adjunction [Completion ⊣ CMet_Incl] that would make the complete spaces a
 reflective subcategory — the §IV.3-SHAPED reflection, over this file's
 isometric [Met] rather than Mac Lane's own, whose §IV.3 statement is about
 metric spaces with UNIFORMLY CONTINUOUS maps (a different category, as
 Instance/Met.v's header records).  Theory/Universal/
 Arrow.v's [LeftAdjointFunctorFromUniversalArrows] and
 [AdjunctionFromUniversalArrows] produce both from
 [Completion_UniversalArrow] applied at every object with no further proof
 obligation, and that they do is MACHINE-CHECKED rather than asserted —
 Test/ProbeMet.v elaborates both terms.  They are left out of the library
 surface only because the issue asks for the universal arrow and its
 uniqueness corollary and stops there; promoting them is a two-line change
 whenever it is wanted.  CORRECTION (#370): they are promoted.
 Instance/Met/Uniform.v's [CMet_Reflective_in_Met], with its adjunction
 [completion_adj], makes the complete spaces a reflective subcategory of
 Instance/Met.v's isometric [Met] by that route, and the same file builds
 Mac Lane's own §IV.3 category of uniformly continuous maps, [MetU],
 with the reflection [CMet_Reflective_in_MetU].

 Also not delivered: any comparison with the Lawvere enriched reading of
 metric spaces (see Instance/Met.v's header); and any claim that
 [Completion X] is the only complete space containing X, which would be
 false — many complete spaces contain a given one.  What is proved is the
 universal property, which picks out the completion among them by a
 factorization condition rather than by containment. 

 --------
 nLab：       https://ncatlab.org/nlab/show/Cauchy+complete+metric+space
 nLab：       https://ncatlab.org/nlab/show/universal+morphism
 Wikipedia：  https://en.wikipedia.org/wiki/Complete_metric_space#Completion
 书籍：      Mac Lane，《为工作数学家而写的范畴论》，第2版，
 GTM 5，第III.1节，印刷页56-57（PDF页65-66），
 第三个未编号的构造——本文件的定理
 书籍：      Bishop，《构造分析的基础》，McGraw-Hill 1967——模量学科
 文档：      Rocq标准库，实数（Rcomplete.R_complete，
 SeqProp.UL_sequence）关于引用。此文件未打开任何书籍；对 Mac Lane §III.1 的描述是对书内库存（doc/plan/books/maclane/inventory/III.json，条目 [maclane:III.1:construction3]，第 56 页，PDF 第 65-66 页）的意译，而非印刷文本。Instance/Met.v 的标题中也包含相同的说明和更完整的引用列表。

 Mac Lane §III.1 将度量空间的完备性列为普适箭头的例子之一，仅用一句话且没有证明：在 Met 为度量空间及度量保持映射、Cmet 为完备度量空间的全子范畴的情况下，嵌入 X → X-bar 是从 X 到包含 Cmet ⟶ Met 的普适箭头，并且普适箭头的一般唯一性随后给出了完备性的唯一性（至唯一同构）。此文件即是该句的证明。这个构造是康托尔的，来自1872年，应用于任意空间，而不仅仅是有理数：完备化的一个点是一个柯西序列，当它们的项之间的距离趋于零时，两个序列被认为是相同的，而两个序列之间的距离是它们各项之间距离的极限。麦克莱恩的贡献在于，没有任何这些选择使得完备化成为完备化；正是分解性质决定了，而本文件的 [Completion_AUniversalArrow] 就是该性质，而 [completion_unique] 则是它所强制的唯一性。为什么距离是实值的，以及为什么因此该文件位于实例层。 这个文件背后的问题提供了“有理数或实数值的距离”，并要求对选择进行记录。 该选择是强制性的，其原因在构造中可见：两个柯西序列之间的距离是距离的极限，因此度量的陪域必须包含自身柯西序列的极限，否则完备化根本不是该范畴的对象，也无法声明普遍算子。[Q]不包含它们。

 这个论点的两个部分，有意分开说明如下：- 机器验证：在完备空间上的距离就是极限，并且通过是极限而被固定。[cdist_spec] 证明了该距离序列收敛到 [cdist]，[cdist_unique] 证明了任何它收敛到的实数都是 [cdist]。因此，这个极限不是众多可接受距离中的一个选择——它是唯一的，如果一个值域缺少它，就缺少距离。

 - 讨论未证明：[Q] 在这种极限下并不封闭。这是一个经典的民间事实，即有理数的柯西序列可以收敛到一个无理数（√2），这里或该树的任何地方都未形式化；标准库中也没有可依赖的无理数结果。它被陈述为一个论证，读者应将其作为论证来看待。结果是该文件使用了标准库的 [R]，因此继承了其公理。这是该问题完成定义所允许的（“如果不可避免地使用经典实数，则文件位于实例层”），并遵循了 Instance/Top/ reals 文件的先例，其中 docs/AXIOMS.md 对每个常数对实数进行了定价。分层非常清晰，下面的数字是按常数测量的，而不是样本测量。[R_complete] 是 [sig_not_dec] 进入的唯一通道。Instance/Met/Extended.v 从未打开过它：它的 55 个常数中没有一个承载 [sig_not_dec]，并且有五个直接关闭。Instance/Met.v 以恰好两个常数打开它——[R_Metric_MComplete]，这是实数集完备性被证明的地方，以及 [R_CMet]，从中构建的 [CMet] 对象——它的其他 61 个常数最多携带 [sig_forall_dec] 和 [functional_extensionality_dep]。该文件在其 66 个常数中的 41 个中打开它，即 [cdist] 之后的所有内容。以下构造中未使用选择原理。（上面列出的三个标准库公理是从 [R] 本身继承而来的，这里并未引入；本文档中也未对它们的强度作出任何声明。）Instance/Met.v 的 [MCauchy] 是类型值（本库的 `∃` 是 [sigT]），因此柯西序列会将其模量作为数据携带。这正是使下面的 [Completion_MComplete] 具有构造性的原因：它的对角论证对每个索引使用一个阈值，而从一个 Prop 级存在性序列中读取阈值序列则需要可数选择。相应地，[cs_equiv]，即柯西序列的识别，是Prop值（它字面上是标准库中0处的[Un_cv]），因为完备性的分离公理必须从实数之间的一个方程产生它，并且在那要求一个模数不会带来任何好处。该接口的两个方向都是故意的。这里什么都不能计算，这是值得说明的，因为这棵树的大部分内容是可以计算的。[cdist] 是 [R_complete] 的 [proj1_sig]，其值不是封闭项，因此在完备性中的任何距离都无法计算，并且没有 Instance/FinSet/ 文件所含的 [eq_refl] 验收测试。下面所做的可转换性声明是结构性的（完备性的承载类型是柯西序列的类型），而不是数值的。与此一致的是，两个类型为数据但其值无法检查的见证——[cs_diag_MCauchy] 和 Instance/Met.v 的 [R_Metric_MComplete]——被保持为 [Qed] 不透明；[Completion_MComplete]、[Completion_AUniversalArrow] 和 [Completion_UniversalArrow] 为 [Defined]，因为通用箭头机制会从它们中投影出来。不是 [CauchyComplete]。Construction/Karoubi/Universal.v 定义 [CauchyComplete] 为 [IdempotentsSplit]，这是一个 CATEGORIES 的属性。这个文件是关于完备度量空间的；两者在这里无关，而且下面的内容没有涉及 Karoubi 的概念。

 交付内容：作为 [Met] 对象的完备空间 [Completion X]，其完备性 [Completion_MComplete]，等距嵌入 [eta]，其像的稠密性，等距映射扩展到完备空间 [ext]，在 Theory/Universal/Arrow.v 的两种编码中的泛箭头，通过该机制而非手工获得的完备性唯一性（存在唯一兼容的同构），以及非空性证明：Instance/Met.v 的 [Harmonic] 的完备空间拥有一个嵌入未覆盖的点。未交付的内容：作为函子（FUNCTOR）的完备，以及因此产生的调整（adjunction）[Completion ⊣ CMet_Incl]，这将使完备空间成为反射子范畴——即本文件的等距（isometric）[Met]上的§IV.3形反射，而不是Mac Lane自己的，其§IV.3陈述是关于带有一致连续（UNIFORMLY CONTINUOUS）映射的度量空间（另一类范畴，如Instance/Met.v的头部所记录）。Theory/Universal/Arrow.v的[LeftAdjointFunctorFromUniversalArrows]和[AdjunctionFromUniversalArrows]都是通过在每个对象上应用[Completion_UniversalArrow]而产生的，无需进一步证明义务，并且它们的生成是机器可检验（MACHINE-CHECKED）的，而不是断言的——Test/ProbeMet.v阐述了这两个项。它们只被排除在图书馆表面之外，因为问题要求的是通用箭头及其唯一性推论，并且到此为止；如果想要，可以通过两行修改将它们提升。更正 (#370)：它们已被提升。Instance/Met/Uniform.v 中的 [CMet_Reflective_in_Met] 及其伴随 [completion_adj]，使得完整空间通过该路径成为 Instance/Met.v 的等距 [Met] 的反射子范畴，同一文件还构建了 Mac Lane 自己的 §IV.3 的一致连续映射范畴 [MetU]，并且具有反射 [CMet_Reflective_in_MetU]。同样未涉及的内容：与 Lawvere 加强的度量空间解读的任何比较（参见 Instance/Met.v 的标题）；以及任何声称 [Completion X] 是包含 X 的唯一完全空间的说法，这是错误的 —— 许多完全空间包含给定空间。所证明的是普遍性质，它通过分解条件而非包含关系，从这些空间中选出完备化。
*)

(** ** A small toolkit for limits / ** 一个关于极限的小工具包 *)

(*
 The standard library has no “eventually below a constant implies the
 limit is below it”, so it is proved here.  Both this and [Un_cv_const]
 are used throughout; nothing about metric spaces enters. 

 --------
 标准库中没有“最终小于某常数意味着极限也小于它”，所以这里进行了证明。这个和 [Un_cv_const] 在整个过程中都被使用；与度量空间无关。
*)
Lemma Un_cv_const (c : R) : Un_cv (fun _ => c) c.
Proof.
  intros eps Heps.
  exists 0%nat; intros n _.
  unfold R_dist.
  replace (c - c) with 0 by ring.
  now rewrite Rabs_R0.
Qed.

Lemma Un_cv_le_const (u : nat → R) (l c : R) (N : nat) :
  Un_cv u l → (∀ n : nat, (N <= n)%nat → u n <= c) → l <= c.
Proof.
  intros Hl Hbound.
  destruct (Rle_or_lt l c) as [Hle | Hlt]; [ exact Hle | exfalso ].
  destruct (Hl (l - c) ltac:(lra)) as [M HM].
  pose (n := Nat.max N M).
  specialize (HM n (Nat.le_max_r N M)).
  specialize (Hbound n (Nat.le_max_l N M)).
  unfold R_dist in HM.
  destruct (Rabs_def2 _ _ HM) as [_ Hlow].
  lra.
Qed.

(* A sandwich at zero: a non-negative sequence under the sum of two null sequences is null. This is what makes [cs_equiv] transitive. / 零点的三明治：两个零序列的和下的非负序列是零序列。这就是使 [cs_equiv] 可传递的原因。 *)
Lemma Un_cv_zero_squeeze (w u v : nat → R) :
  (∀ n, 0 <= w n) → (∀ n, w n <= u n + v n) →
  Un_cv u 0 → Un_cv v 0 → Un_cv w 0.
Proof.
  intros Hpos Hle Hu Hv eps Heps.
  destruct (Hu (eps / 2) ltac:(lra)) as [N1 H1].
  destruct (Hv (eps / 2) ltac:(lra)) as [N2 H2].
  exists (Nat.max N1 N2); intros n Hn.
  assert (N1 <= n)%nat as Hn1
      by (transitivity (Nat.max N1 N2); [ apply Nat.le_max_l | exact Hn ]).
  assert (N2 <= n)%nat as Hn2
      by (transitivity (Nat.max N1 N2); [ apply Nat.le_max_r | exact Hn ]).
  specialize (H1 n Hn1); specialize (H2 n Hn2).
  unfold R_dist in *.
  rewrite Rminus_0_r in *.
  pose proof (Rle_abs (u n)); pose proof (Rle_abs (v n)).
  pose proof (Hpos n); pose proof (Hle n).
  rewrite Rabs_pos_eq by exact (Hpos n).
  lra.
Qed.

(*
 Two sequences that get arbitrarily close share their limits.  Stated with
 an explicit majorant [w] so that callers never have to rewrite under a
 lambda — this development uses no functional extensionality. 

 --------
 两个无限接近的序列拥有相同的极限。用一个显式的上界 [w] 来说明，这样调用者就不必在 lambda 下重新编写——这个发展不使用函数外延性。
*)
Lemma Un_cv_shift (u v w : nat → R) (l : R) :
  (∀ n, Rabs (u n - v n) <= w n) → Un_cv w 0 → Un_cv v l → Un_cv u l.
Proof.
  intros Hclose Hw Hv eps Heps.
  destruct (Hw (eps / 2) ltac:(lra)) as [N1 H1].
  destruct (Hv (eps / 2) ltac:(lra)) as [N2 H2].
  exists (Nat.max N1 N2); intros n Hn.
  assert (N1 <= n)%nat as Hn1
      by (transitivity (Nat.max N1 N2); [ apply Nat.le_max_l | exact Hn ]).
  assert (N2 <= n)%nat as Hn2
      by (transitivity (Nat.max N1 N2); [ apply Nat.le_max_r | exact Hn ]).
  specialize (H1 n Hn1); specialize (H2 n Hn2).
  unfold R_dist in *.
  rewrite Rminus_0_r in H1.
  pose proof (Rle_abs (w n)) as Hwabs.
  pose proof (Hclose n) as Hcn.
  replace (u n - l) with ((u n - v n) + (v n - l)) by ring.
  eapply Rle_lt_trans; [ apply Rabs_triang |].
  lra.
Qed.

(* Limits preserve eventual ≤. / 极限保持最终的≤。 *)
Lemma Un_cv_le (u v : nat → R) (a b : R) (N : nat) :
  (∀ n : nat, (N <= n)%nat → u n <= v n) → Un_cv u a → Un_cv v b → a <= b.
Proof.
  intros Hle Hu Hv.
  destruct (Rle_or_lt a b) as [H | Hlt]; [ exact H | exfalso ].
  destruct (Hu ((a - b) / 2) ltac:(lra)) as [N1 H1].
  destruct (Hv ((a - b) / 2) ltac:(lra)) as [N2 H2].
  pose (n := Nat.max N (Nat.max N1 N2)).
  assert (N <= n)%nat as HnN by apply Nat.le_max_l.
  assert (N1 <= n)%nat as Hn1.
  { transitivity (Nat.max N1 N2); [ apply Nat.le_max_l | apply Nat.le_max_r ]. }
  assert (N2 <= n)%nat as Hn2.
  { transitivity (Nat.max N1 N2); [ apply Nat.le_max_r | apply Nat.le_max_r ]. }
  specialize (Hle n HnN); specialize (H1 n Hn1); specialize (H2 n Hn2).
  unfold R_dist in *.
  destruct (Rabs_def2 _ _ H1) as [_ Hu'].
  destruct (Rabs_def2 _ _ H2) as [Hv' _].
  lra.
Qed.

(* Limits add. / 添加限制。 *)
Lemma Un_cv_plus (u v : nat → R) (a b : R) :
  Un_cv u a → Un_cv v b → Un_cv (fun n => u n + v n) (a + b).
Proof.
  intros Hu Hv eps Heps.
  destruct (Hu (eps / 2) ltac:(lra)) as [N1 H1].
  destruct (Hv (eps / 2) ltac:(lra)) as [N2 H2].
  exists (Nat.max N1 N2); intros n Hn.
  assert (N1 <= n)%nat as Hn1
      by (transitivity (Nat.max N1 N2); [ apply Nat.le_max_l | exact Hn ]).
  assert (N2 <= n)%nat as Hn2
      by (transitivity (Nat.max N1 N2); [ apply Nat.le_max_r | exact Hn ]).
  specialize (H1 n Hn1); specialize (H2 n Hn2).
  unfold R_dist in *.
  replace (u n + v n - (a + b)) with ((u n - a) + (v n - b)) by ring.
  eapply Rle_lt_trans; [ apply Rabs_triang |].
  lra.
Qed.

(*
 Convergence in a metric space, read as convergence of the distances to
 zero.  This is the standard bridge from the [MConverges] vocabulary of
 Instance/Met.v to the standard library's [Un_cv], and it is where the
 Type-valued modulus is spent down to a Prop-level statement. 

 --------
 度量空间中的收敛性，可读作距离趋向于零的收敛。这是从 Instance/Met.v 的 [MConverges] 词汇到标准库的 [Un_cv] 的标准桥梁，并且这是类型值模量被消耗到命题级别陈述的地方。
*)
Lemma MConverges_dist_cv {Z : MetricSpace} (u : nat → Z) (l : Z) :
  MConverges Z u l → Un_cv (fun n => dist (u n) l) 0.
Proof.
  intros H eps Heps.
  destruct (H eps ltac:(lra)) as [N HN].
  exists N; intros n Hn.
  unfold R_dist.
  rewrite Rminus_0_r, Rabs_pos_eq by apply dist_nonneg.
  exact (HN n Hn).
Qed.

(* Convergence only sees the sequence up to the carrier's own equality. / 收敛只看到序列直到载体自身的相等为止。 *)
Lemma MConverges_respects_seq {Z : MetricSpace} (u v : nat → Z) (l : Z) :
  (∀ n, u n ≈ v n) → MConverges Z u l → MConverges Z v l.
Proof.
  intros Huv H eps Heps.
  destruct (H eps Heps) as [N HN].
  exists N; intros n Hn.
  rewrite (dist_proper (v n) (u n) l l (symmetry (Huv n)) (reflexivity l)).
  exact (HN n Hn).
Qed.

Section Completion.

(* The proofs below genuinely depend on the space being completed; [Lib.v] sets [Default Proof Using “Type”], which would discard it. Same reason, same remedy, as Instance/Top/Interval.v and Instance/Met.v's [OfInjection] section. / 下面的证明确实依赖于空间是完备的；[Lib.v] 设置 [Default Proof Using “Type”]，这将放弃它。同样的原因，同样的补救措施，如 Instance/Top/Interval.v 和 Instance/Met.v 的 [OfInjection] 部分。 *)
Local Set Default Proof Using "All".

Context (X : MetricSpace).

(* * ** Cauchy sequences as the points of the completion / * ** 作为完备化点的柯西序列 *)

(*
 A point of the completion is a sequence TOGETHER WITH its modulus, this
 library's `∃` being [sigT].  The modulus is what
 [Completion_MComplete] consumes, one per index. 

 --------
 一个完备点是一个序列及其模数，这个库的 `∃` 是 [sigT]。模数是 [Completion_MComplete] 消耗的，每个索引消耗一个。
*)
Definition CauchySeq : Type := ∃ u : nat → X, MCauchy X u.

Definition cs_seq (x : CauchySeq) : nat → X := `1 x.
Definition cs_cauchy (x : CauchySeq) : MCauchy X (cs_seq x) := `2 x.

Definition cs_of (u : nat → X) (H : MCauchy X u) : CauchySeq := (u; H).

(* The sequence of distances between two points of the completion. / 完成的两点之间的距离序列。 *)
Definition cdist_seq (x y : CauchySeq) (n : nat) : R :=
  dist (cs_seq x n) (cs_seq y n).

Lemma cdist_seq_nonneg (x y : CauchySeq) (n : nat) : 0 <= cdist_seq x y n.
Proof. apply dist_nonneg. Qed.

(* The distances themselves form a Cauchy sequence of REALS. This is the whole reason the codomain of the metric must be complete, and the estimate that proves it is [dist_quadrilateral]. / 这些距离本身构成了实数的柯西序列。这就是度量值域必须完备的全部原因，而证明这一点的估计是 [dist_quadrilateral]。 *)
Lemma cdist_Cauchy_crit (x y : CauchySeq) : Cauchy_crit (cdist_seq x y).
Proof.
  intros eps Heps.
  destruct (cs_cauchy x (eps / 2) ltac:(lra)) as [N1 H1].
  destruct (cs_cauchy y (eps / 2) ltac:(lra)) as [N2 H2].
  exists (Nat.max N1 N2); intros n m Hn Hm.
  assert (N1 <= n)%nat as Hn1
      by (transitivity (Nat.max N1 N2); [ apply Nat.le_max_l | exact Hn ]).
  assert (N1 <= m)%nat as Hm1
      by (transitivity (Nat.max N1 N2); [ apply Nat.le_max_l | exact Hm ]).
  assert (N2 <= n)%nat as Hn2
      by (transitivity (Nat.max N1 N2); [ apply Nat.le_max_r | exact Hn ]).
  assert (N2 <= m)%nat as Hm2
      by (transitivity (Nat.max N1 N2); [ apply Nat.le_max_r | exact Hm ]).
  pose proof (H1 n m Hn1 Hm1) as Hx.
  pose proof (H2 n m Hn2 Hm2) as Hy.
  unfold R_dist, cdist_seq.
  eapply Rle_lt_trans;
    [ exact (dist_quadrilateral (cs_seq x n) (cs_seq x m)
                                (cs_seq y n) (cs_seq y m)) |].
  lra.
Qed.

(* * ** The distance on the completion / * ** 完成时的距离 *)

(*
 THE LIMIT.  [R_complete] returns it as data; this is the one call in the
 development that reaches for completeness of the reals, and the one place
 [sig_not_dec] enters the axiom footprint. 

 --------
 极限。[R_complete] 将其作为数据返回；这是开发中唯一一个追求实数完整性的调用，也是唯一一个 [sig_not_dec] 进入公理足迹的地方。
*)
Definition cdist (x y : CauchySeq) : R :=
  proj1_sig (R_complete (cdist_seq x y) (cdist_Cauchy_crit x y)).

(* The distance IS the limit of the term-wise distances ... / 距离是逐项距离的极限…… *)
Lemma cdist_spec (x y : CauchySeq) : Un_cv (cdist_seq x y) (cdist x y).
Proof. exact (proj2_sig (R_complete (cdist_seq x y) (cdist_Cauchy_crit x y))). Qed.

(*
 ... and is PINNED by being one: any real to which the term-wise distances
 converge is [cdist].  Together with [cdist_spec] this is the
 machine-checked half of the codomain argument in the header — the limit
 is not one admissible distance among several, it is the only one. 

 --------
 ... 并且通过成为一个固定：任何项-wise 距离收敛的实数是 [cdist]。与 [cdist_spec] 一起，这是标题中值域论证的机器检查过的一半——极限不是众多可接受距离中的一个，它是唯一的一个。
*)
Lemma cdist_unique (x y : CauchySeq) (r : R) :
  Un_cv (cdist_seq x y) r → cdist x y = r.
Proof.
  intro Hr.
  exact (UL_sequence (cdist_seq x y) (cdist x y) r (cdist_spec x y) Hr).
Qed.

(* Consequently the distance inherits every eventual bound. / 因此，这个距离继承了每一个最终边界。 *)
Lemma cdist_le (x y : CauchySeq) (c : R) (N : nat) :
  (∀ n : nat, (N <= n)%nat → cdist_seq x y n <= c) → cdist x y <= c.
Proof. intro H; exact (Un_cv_le_const _ _ c N (cdist_spec x y) H). Qed.

Lemma cdist_nonneg (x y : CauchySeq) : 0 <= cdist x y.
Proof.
  destruct (Rle_or_lt 0 (cdist x y)) as [Hle | Hlt]; [ exact Hle | exfalso ].
  destruct (cdist_spec x y (- cdist x y) ltac:(lra)) as [N HN].
  specialize (HN N (Nat.le_refl N)).
  unfold R_dist in HN.
  destruct (Rabs_def2 _ _ HN) as [Hhi _].
  pose proof (cdist_seq_nonneg x y N).
  lra.
Qed.

(* * ** Identification of Cauchy sequences / * ** 柯西序列的识别 *)

(*
 Two Cauchy sequences name the same point when the distance between their
 terms tends to zero.  This is PROP-VALUED — it is literally the standard
 library's [Un_cv] at 0 — and the header explains why: the separation
 axiom of the completion has to produce it out of an equation between
 reals.  A [Prop] is a [Type], so it serves as the `≈` of a
 [SetoidObject] unchanged. 

 --------
 当两个Cauchy序列的项之间的距离趋于零时，它们表示相同的点。这是PROP值的——它实际上是标准库中在0处的[Un_cv]——头部解释了原因：完备性的分离公理必须从实数之间的一个等式中产生它。一个[Prop]是一个[Type]，因此它作为[SetoidObject]保持不变的`≈`。
*)
Definition cs_equiv (x y : CauchySeq) : Prop := Un_cv (cdist_seq x y) 0.

(* Both proofs are pointwise rather than by rewriting the SEQUENCE, which would need functional extensionality: nothing in this development rewrites under a lambda. / 这两个证明都是逐点的，而不是通过重写序列，这将需要函数外延性：在这个发展中，没有任何东西会在 lambda 下重写。 *)
Lemma cs_equiv_refl (x : CauchySeq) : cs_equiv x x.
Proof.
  intros eps Heps.
  exists 0%nat; intros n _.
  unfold R_dist, cdist_seq.
  rewrite dist_refl.
  replace (0 - 0) with 0 by ring.
  now rewrite Rabs_R0.
Qed.

Lemma cs_equiv_sym (x y : CauchySeq) : cs_equiv x y → cs_equiv y x.
Proof.
  intros H eps Heps.
  destruct (H eps Heps) as [N HN].
  exists N; intros n Hn.
  unfold R_dist, cdist_seq in *.
  rewrite (dist_sym (cs_seq y n) (cs_seq x n)).
  exact (HN n Hn).
Qed.

Lemma cs_equiv_trans (x y z : CauchySeq) :
  cs_equiv x y → cs_equiv y z → cs_equiv x z.
Proof.
  unfold cs_equiv; intros Hxy Hyz.
  apply (Un_cv_zero_squeeze _ (cdist_seq x y) (cdist_seq y z)).
  - intro n; apply cdist_seq_nonneg.
  - intro n; apply dist_triangle.
  - exact Hxy.
  - exact Hyz.
Qed.

#[export] Program Instance CauchySeq_Setoid : Setoid CauchySeq := {|
  equiv := cs_equiv
|}.
Next Obligation.
  constructor.
  - exact cs_equiv_refl.
  - exact cs_equiv_sym.
  - exact cs_equiv_trans.
Qed.

Definition CauchySeq_Object : SetoidObject :=
  {| carrier := CauchySeq; is_setoid := CauchySeq_Setoid |}.

(* * ** The completion is a metric space / * ** 完备空间是一个度量空间 *)

Lemma cdist_proper (x x' y y' : CauchySeq) :
  x ≈ x' → y ≈ y' → cdist x y = cdist x' y'.
Proof.
  intros Hx Hy.
  apply cdist_unique.
  (*
 The two distance sequences differ by at most d(xₙ,x'ₙ) + d(yₙ,y'ₙ),
 which is null; so they share a limit. 

 --------
 这两个距离序列最多相差 d(xₙ,x'ₙ) + d(yₙ,y'ₙ)，而这个值为零；因此它们有相同的极限。
*)
  apply (Un_cv_shift _ (cdist_seq x' y')
                     (fun n => cdist_seq x x' n + cdist_seq y y' n)).
  - intro n; apply dist_quadrilateral.
  - replace 0 with (0 + 0) by ring.
    exact (Un_cv_plus _ _ 0 0 Hx Hy).
  - apply cdist_spec.
Qed.

Lemma cdist_refl (x : CauchySeq) : cdist x x = 0.
Proof. exact (cdist_unique x x 0 (cs_equiv_refl x)). Qed.

Lemma cdist_separates (x y : CauchySeq) : cdist x y = 0 → x ≈ y.
Proof.
  intro H.
  unfold equiv; simpl; unfold cs_equiv.
  rewrite <- H.
  apply cdist_spec.
Qed.

Lemma cdist_sym (x y : CauchySeq) : cdist x y = cdist y x.
Proof.
  apply cdist_unique.
  apply (Un_cv_shift _ (cdist_seq y x) (fun _ => 0)).
  - intro n; unfold cdist_seq.
    rewrite (dist_sym (cs_seq x n) (cs_seq y n)).
    replace (dist (cs_seq y n) (cs_seq x n) - dist (cs_seq y n) (cs_seq x n))
      with 0 by ring.
    rewrite Rabs_R0; apply Rle_refl.
  - apply Un_cv_const.
  - apply cdist_spec.
Qed.

Lemma cdist_triangle (x y z : CauchySeq) : cdist x z <= cdist x y + cdist y z.
Proof.
  apply (Un_cv_le (cdist_seq x z)
                  (fun n => cdist_seq x y n + cdist_seq y z n) _ _ 0%nat).
  - intros n _; apply dist_triangle.
  - apply cdist_spec.
  - exact (Un_cv_plus _ _ _ _ (cdist_spec x y) (cdist_spec y z)).
Qed.

(* THE COMPLETION, as an object of [Met]. / 作为 [Met] 的对象，完成。 *)
Definition Completion : MetricSpace :=
  {| met_carrier    := CauchySeq_Object;
     dist           := cdist;
     dist_proper    := cdist_proper;
     dist_refl      := cdist_refl;
     dist_separates := cdist_separates;
     dist_sym       := cdist_sym;
     dist_triangle  := cdist_triangle |}.

(** ** The isometric embedding / ** 等距嵌入 *)

Lemma const_MCauchy (a : X) : MCauchy X (fun _ => a).
Proof.
  intros eps Heps.
  exists 0%nat; intros m n _ _.
  rewrite dist_refl; exact Heps.
Qed.

Definition eta_seq (a : X) : CauchySeq := cs_of (fun _ => a) (const_MCauchy a).

(*
 The distance between two constant sequences is the distance of their
 values — this is where [Un_cv_const] is spent. 

 --------
 两个常数序列之间的距离就是它们数值的距离——这就是 [Un_cv_const] 被花费的地方。
*)
Lemma eta_dist (a b : X) : cdist (eta_seq a) (eta_seq b) = dist a b.
Proof.
  apply cdist_unique.
  (*
 [cdist_seq (eta_seq a) (eta_seq b)] IS the constant [dist a b]: the
 projection out of the sigma reduces.  This is the convertibility
 exception, and [exact] rather than [apply] is what spends it. 

 --------
 [cdist_seq (eta_seq a) (eta_seq b)] 是常数 [dist a b]：从 sigma 中的投影减少。这是可转换性例外，并且是 [exact] 而不是 [apply] 来使用它。
*)
  exact (Un_cv_const (dist a b)).
Qed.

Lemma eta_proper (a b : X) : a ≈ b → eta_seq a ≈ eta_seq b.
Proof.
  intro Hab.
  apply cdist_separates.
  rewrite eta_dist.
  now apply dist_eq_zero.
Qed.

Definition eta_morphism : SetoidMorphism (met_carrier X) (met_carrier Completion).
Proof.
  unshelve refine {| morphism := eta_seq |}.
  intros a b Hab; exact (eta_proper a b Hab).
Defined.

Definition eta : Isometry X Completion :=
  {| isometry_map := eta_morphism; isometry_dist := eta_dist |}.

(* DENSITY: every point of the completion is the limit of the embedded terms of any Cauchy sequence naming it. The threshold is the sequence's own Cauchy modulus at ε/2 — data, as always. / 密度：完备的每一点都是表示它的任何柯西序列的嵌入项的极限。阈值是序列在 ε/2 时自身的柯西模——数据，一如既往。 *)
Lemma eta_dense (x : CauchySeq) :
  MConverges Completion (fun n => eta_seq (cs_seq x n)) x.
Proof.
  intros eps Heps.
  destruct (cs_cauchy x (eps / 2) ltac:(lra)) as [N HN].
  exists N; intros n Hn.
  (* d(η xₙ, x) = limₘ d(xₙ, xₘ) ≤ ε/2 < ε / d(η xₙ, x) = limₘ d(xₙ, xₘ) ≤ ε/2 < ε *)
  apply Rle_lt_trans with (r2 := eps / 2); [| lra ].
  apply (cdist_le _ _ _ N).
  intros m Hm.
  unfold cdist_seq; simpl.
  left; exact (HN n m Hn Hm).
Qed.

(** ** The completion is complete / ** 完成已完成 *)

(*
 THE DIAGONAL ARGUMENT.  Given a Cauchy sequence ξ of points of the
 completion, each ξₖ is itself a Cauchy sequence in X CARRYING ITS OWN
 MODULUS, so a term of it may be selected at the threshold for 1/(k+1)
 with no appeal to choice — that selection is [cs_pick] below, an ordinary
 function of k.  The diagonal [cs_diag] of those selections is Cauchy in
 X, and ξ converges to its class.

 [harm], [harm_pos], [harm_antitone], [harm_mod] and [harm_mod_spec] are
 Instance/Met.v's, where they were introduced for the harmonic space; they
 are reused here as a general archimedean toolkit rather than duplicated. 

 --------
 对角论证。 给定一个完备空间点的柯西序列 ξ，每个 ξₖ 本身都是 X 中的一个柯西序列，并且携带它自己的模，因此可以在 1/(k+1) 阈值处选择它的一个项，而无需调用选择——这个选择在下面表示为 [cs_pick]，它是 k 的一个普通函数。那些选择的对角线 [cs_diag] 在 X 中是柯西的，并且 ξ 收敛到它的等价类。

 [harm]、[harm_pos]、[harm_antitone]、[harm_mod] 和 [harm_mod_spec] 是 Instance/Met.v 文件中的内容，它们最初在调和空间中引入；这里作为一般阿基米德工具集重用，而不是重复。
*)

Section Complete.

Context (xi : nat → Completion).

Definition cs_pick (k : nat) : nat :=
  `1 (cs_cauchy (xi k) (harm k) (harm_pos k)).

Lemma cs_pick_spec (k : nat) (m n : nat) :
  (cs_pick k <= m)%nat → (cs_pick k <= n)%nat →
  dist (cs_seq (xi k) m) (cs_seq (xi k) n) < harm k.
Proof. exact (`2 (cs_cauchy (xi k) (harm k) (harm_pos k)) m n). Qed.

Definition cs_diag (k : nat) : X := cs_seq (xi k) (cs_pick k).

(* Each selected term names a point within 1/(k+1) of ξₖ. / 每个选定的项都是 ξₖ 内 1/(k+1) 范围内的一个点的名称。 *)
Lemma cs_diag_close (k : nat) : cdist (eta_seq (cs_diag k)) (xi k) <= harm k.
Proof.
  apply (cdist_le _ _ _ (cs_pick k)).
  intros n Hn.
  left.
  exact (cs_pick_spec k (cs_pick k) n (Nat.le_refl _) Hn).
Qed.

Context (Hxi : MCauchy Completion xi).

Lemma cs_diag_MCauchy : MCauchy X cs_diag.
Proof.
  intros eps Heps.
  destruct (Hxi (eps / 4) ltac:(lra)) as [N2 HN2].
  (* [harm_mod (eps/4)] is written out rather than abbreviated: [lra] matches atoms syntactically, and a local abbreviation would hide the very term [harm_mod_spec] talks about. / [harm_mod (eps/4)] 是完整写出的，而不是缩写：[lra] 在语法上与原子匹配，本地缩写会隐藏 [harm_mod_spec] 正在讨论的术语。 *)
  exists (Nat.max (harm_mod (eps / 4)) N2); intros j k Hj Hk.
  assert (harm_mod (eps / 4) <= j)%nat as Hj1
      by (transitivity (Nat.max (harm_mod (eps / 4)) N2);
          [ apply Nat.le_max_l | exact Hj ]).
  assert (harm_mod (eps / 4) <= k)%nat as Hk1
      by (transitivity (Nat.max (harm_mod (eps / 4)) N2);
          [ apply Nat.le_max_l | exact Hk ]).
  assert (N2 <= j)%nat as Hj2
      by (transitivity (Nat.max (harm_mod (eps / 4)) N2);
          [ apply Nat.le_max_r | exact Hj ]).
  assert (N2 <= k)%nat as Hk2
      by (transitivity (Nat.max (harm_mod (eps / 4)) N2);
          [ apply Nat.le_max_r | exact Hk ]).
  pose proof (harm_mod_spec (eps / 4) ltac:(lra)) as Hsmall.
  pose proof (harm_antitone _ _ Hj1) as Hhj.
  pose proof (harm_antitone _ _ Hk1) as Hhk.
  (* d(diag j, diag k) = cdist (η diag j) (η diag k), then two triangles / d(diag j, diag k) = cdist (η diag j) (η diag k)，然后两个三角形 *)
  rewrite <- (eta_dist (cs_diag j) (cs_diag k)).
  pose proof (cdist_triangle (eta_seq (cs_diag j)) (xi j) (eta_seq (cs_diag k)))
    as T1.
  pose proof (cdist_triangle (xi j) (xi k) (eta_seq (cs_diag k))) as T2.
  rewrite (cdist_sym (xi k) (eta_seq (cs_diag k))) in T2.
  pose proof (cs_diag_close j) as A1.
  pose proof (cs_diag_close k) as A2.
  pose proof (HN2 j k Hj2 Hk2) as Hjk.
  change (dist (xi j) (xi k)) with (cdist (xi j) (xi k)) in Hjk.
  lra.
Qed.

Definition cs_limit : Completion := cs_of cs_diag cs_diag_MCauchy.

Lemma cs_limit_spec : MConverges Completion xi cs_limit.
Proof.
  intros eps Heps.
  destruct (cs_diag_MCauchy (eps / 4) ltac:(lra)) as [M2 HM2].
  exists (Nat.max (harm_mod (eps / 4)) M2); intros k Hk.
  assert (harm_mod (eps / 4) <= k)%nat as Hk1
      by (transitivity (Nat.max (harm_mod (eps / 4)) M2);
          [ apply Nat.le_max_l | exact Hk ]).
  assert (M2 <= k)%nat as Hk2
      by (transitivity (Nat.max (harm_mod (eps / 4)) M2);
          [ apply Nat.le_max_r | exact Hk ]).
  pose proof (harm_mod_spec (eps / 4) ltac:(lra)) as Hsmall.
  pose proof (harm_antitone _ _ Hk1) as Hhk.
  (* d(ξₖ, [diag]) ≤ d(ξₖ, η diag k) + d(η diag k, [diag]) ≤ harm k + ε/4 / d(ξₖ, [diag]) ≤ d(ξₖ, η diag k) + d(η diag k, [diag]) ≤ harm k + ε/4 *)
  change (cdist (xi k) cs_limit < eps).
  assert (cdist (eta_seq (cs_diag k)) cs_limit <= eps / 4) as Htail.
  { apply (cdist_le _ _ _ M2).
    intros n Hn.
    left; exact (HM2 k n Hk2 Hn). }
  pose proof (cdist_triangle (xi k) (eta_seq (cs_diag k)) cs_limit) as T.
  rewrite (cdist_sym (xi k) (eta_seq (cs_diag k))) in T.
  pose proof (cs_diag_close k) as A.
  lra.
Qed.

End Complete.

Definition Completion_MComplete : MComplete Completion :=
  fun xi Hxi => (cs_limit xi Hxi; cs_limit_spec xi Hxi).

(* The completion as an object of [CMet]. / 作为 [CMet] 的对象的完成。 *)
Definition Completion_CMet : CMet := (Completion; Completion_MComplete).

(* * ** Extending an isometry into a complete space / * ** 将等距映射扩展到完整空间 *)

Section Extend.

Context (Y : MetricSpace).
Context (cY : MComplete Y).
Context (f : Isometry X Y).

(* The image of a Cauchy sequence under an isometry is Cauchy, with the SAME modulus; [cY] then names its limit. / 在等距映射下，柯西序列的像仍然是柯西序列，并具有相同的模；[cY] 然后命名它的极限。 *)
Definition ext_seq (x : Completion) : nat → Y :=
  fun n => isometry_map f (cs_seq x n).

Definition ext_MCauchy (x : Completion) : MCauchy Y (ext_seq x) :=
  isometry_MCauchy f (cs_seq x) (cs_cauchy x).

Definition ext_val (x : Completion) : Y := `1 (cY (ext_seq x) (ext_MCauchy x)).

Definition ext_spec (x : Completion) : MConverges Y (ext_seq x) (ext_val x) :=
  `2 (cY (ext_seq x) (ext_MCauchy x)).

(*
 The term-wise distances of x and y converge to the distance of the two
 limits.  This single lemma yields both that [ext] is well defined and
 that it preserves the distance. 

 --------
 x 和 y 的各项距离收敛到两个极限的距离。这个单个引理既得出 [ext] 是良定义的，也得出它保持距离不变。
*)
Lemma ext_dist_cv (x y : Completion) :
  Un_cv (cdist_seq x y) (dist (ext_val x) (ext_val y)).
Proof.
  apply (Un_cv_shift _ (fun _ => dist (ext_val x) (ext_val y))
           (fun n => dist (ext_seq x n) (ext_val x)
                     + dist (ext_seq y n) (ext_val y))).
  - intro n.
    unfold cdist_seq.
    rewrite <- (isometry_dist f (cs_seq x n) (cs_seq y n)).
    exact (dist_quadrilateral (ext_seq x n) (ext_val x)
                              (ext_seq y n) (ext_val y)).
  - replace 0 with (0 + 0) by ring.
    exact (Un_cv_plus _ _ 0 0
             (MConverges_dist_cv (ext_seq x) (ext_val x) (ext_spec x))
             (MConverges_dist_cv (ext_seq y) (ext_val y) (ext_spec y))).
  - apply Un_cv_const.
Qed.

Lemma ext_isometry (x y : Completion) :
  dist (ext_val x) (ext_val y) = cdist x y.
Proof. symmetry; exact (cdist_unique x y _ (ext_dist_cv x y)). Qed.

Lemma ext_proper (x y : Completion) : x ≈ y → ext_val x ≈ ext_val y.
Proof.
  intro Hxy.
  apply dist_separates.
  rewrite ext_isometry.
  exact (cdist_unique x y 0 Hxy).
Qed.

Definition ext_morphism : SetoidMorphism (met_carrier Completion) (met_carrier Y).
Proof.
  unshelve refine {| morphism := ext_val |}.
  intros x y Hxy; exact (ext_proper x y Hxy).
Defined.

Definition ext : Isometry Completion Y :=
  {| isometry_map := ext_morphism; isometry_dist := ext_isometry |}.

(*
 THE TRIANGLE: the extension restricted along the embedding is the
 original isometry.  The image sequence is constant at [f a], so its limit
 is [f a]. 

 --------
 三角形：沿嵌入限制的扩展是原始等距映射。图像序列在 [f a] 处保持不变，因此其极限是 [f a] 。
*)
Lemma ext_eta (a : X) : ext_val (eta_seq a) ≈ isometry_map f a.
Proof.
  apply (MConverges_unique (ext_seq (eta_seq a))).
  - exact (ext_spec (eta_seq a)).
  - intros eps Heps.
    exists 0%nat; intros n _.
    rewrite dist_refl; exact Heps.
Qed.

(* UNIQUENESS: any isometry out of the completion that restricts to [f] along the embedding IS [ext]. Density does the work — the two maps agree on a dense set and both preserve limits. / 独特性：任何从完备空间外部的等距映射，如果沿嵌入 [f] 限制，都是 [ext]。密度起作用——两个映射在稠密集上相同，并且都保持极限。 *)
Lemma ext_unique (g : Isometry Completion Y) :
  (∀ a : X, isometry_map g (eta_seq a) ≈ isometry_map f a) →
  ∀ x : Completion, isometry_map g x ≈ ext_val x.
Proof.
  intros Hg x.
  apply (MConverges_unique (ext_seq x)).
  - (* g carries the embedded terms to the image sequence, and preserves the limit of the dense approximation / g 将嵌入的项传递到图像序列，并保持密集近似的极限 *)
    apply (MConverges_respects_seq
             (fun n => isometry_map g (eta_seq (cs_seq x n))) (ext_seq x)).
    + intro n; exact (Hg (cs_seq x n)).
    + exact (isometry_MConverges g _ x (eta_dense x)).
  - exact (ext_spec x).
Qed.

End Extend.

(** ** The universal arrow / ** 万能箭 *)

(*
 Mac Lane §III.1's sentence, in the direct encoding of
 Theory/Universal/Arrow.v: the embedding is a universal arrow from X to
 the inclusion of the complete spaces. 

 --------
 Mac Lane §III.1 的句子，在 Theory/Universal/Arrow.v 的直接编码中：嵌入是从 X 到完全空间包含的一个通用箭头。
*)
Definition Completion_AUniversalArrow :
  AUniversalArrow (X : Met) CMet_Incl Completion_CMet.
Proof.
  unshelve econstructor.
  - exact eta.
  - intros d f.
    unshelve econstructor.
    + exact (ext (`1 d) (`2 d) f; I).
    + exact (fun a => ext_eta (`1 d) (`2 d) f a).
    + intros v Hv x.
      symmetry.
      exact (ext_unique (`1 d) (`2 d) f (`1 v) Hv x).
Defined.

(*
 The same statement in the comma-category encoding, which is what
 [ump_universal_arrows] and the [LeftAdjointFunctorFromUniversalArrows]
 machinery consume. 

 --------
 相同的语句在逗号类别编码中，这就是 [ump_universal_arrows] 和 [LeftAdjointFunctorFromUniversalArrows] 机制所使用的。
*)
Definition Completion_UniversalArrow : UniversalArrow (X : Met) CMet_Incl.
Proof.
  unshelve eapply (universal_arrow_from_UMP (X : Met) CMet_Incl Completion_CMet eta).
  intros d f.
  unshelve econstructor.
  - exact (ext (`1 d) (`2 d) f; I).
  - exact (fun a => symmetry (ext_eta (`1 d) (`2 d) f a)).
  - intros v Hv x.
    symmetry.
    exact (ext_unique (`1 d) (`2 d) f (`1 v) (fun a => symmetry (Hv a)) x).
Defined.

End Completion.

(** ** Uniqueness of the completion / ** 完成的独特性 *)

(*
 Mac Lane's second sentence: “the uniqueness of universal arrows gives
 uniqueness of the completion up to a unique isomorphism”.  This is
 DERIVED, not reproved — the whole content is
 Theory/Universal/Arrow.v's [auniversal_arrow_unique], instantiated.

 Note what the uniqueness clause ranges over, because the bare
 isomorphism statement would be weaker: the isomorphism is unique AMONG
 THOSE COMPATIBLE WITH THE TWO EMBEDDINGS.  A completion can have
 automorphisms, and they are isomorphisms between the two candidates that
 do not commute with the embeddings; that is the point
 Theory/Universal/Arrow.v's header makes about the free monoid on two
 generators, and it applies verbatim here. 

 --------
 Mac Lane 的第二句话：“泛箭的唯一性导致了补全的唯一性，最多到一个唯一同构。”这是推导出来的，而不是重新证明——整个内容是 Theory/Universal/Arrow.v 中的 [auniversal_arrow_unique] 的实例化。

 注意唯一性条款的范围，因为裸同构的表述会更弱：同构在与两个嵌入兼容的对象中是唯一的。一个补全可能有自同构，它们是两个候选对象之间的同构，但不与嵌入交换；这正是 Theory/Universal/Arrow.v 的标题关于两个生成元的自由幺半群所指出的，并且在这里可以照搬适用。
*)
Corollary completion_unique (X : MetricSpace) (Z : CMet)
      (U : AUniversalArrow (X : Met) CMet_Incl Z) :
  ∃! i : Completion_CMet X ≅[CMet] Z,
    fmap[CMet_Incl] i ∘ eta X ≈ @universal_arrow _ _ (X : Met) CMet_Incl Z U.
Proof. exact (auniversal_arrow_unique (Completion_AUniversalArrow X) U). Qed.

(* The same statement with neither solution privileged: any two complete spaces solving X's completion problem are uniquely compatibly isomorphic. / 同样的陈述，没有任何解具有特权：任何两个完整空间解决 X 的完备性问题都是唯一兼容同构的。 *)
Corollary completions_unique (X : MetricSpace) (A B : CMet)
      (U1 : AUniversalArrow (X : Met) CMet_Incl A)
      (U2 : AUniversalArrow (X : Met) CMet_Incl B) :
  ∃! i : A ≅[CMet] B,
    fmap[CMet_Incl] i ∘ @universal_arrow _ _ (X : Met) CMet_Incl A U1
      ≈ @universal_arrow _ _ (X : Met) CMet_Incl B U2.
Proof. exact (auniversal_arrow_unique U1 U2). Qed.

(*
 THE OTHER GENERIC ROUTE WAS ATTEMPTED AND IS BLOCKED.  The library has a
 SECOND generic uniqueness theorem — [univ_property_unique_up_to_unique_iso]
 (Structure/UniversalProperty.v), which argues through representability and
 Yoneda rather than through the mediator calculus — and
 [UniversalArrowIsUniversalProperty]
 (Structure/UniversalProperty/Universal/Arrow.v) advertises itself as the
 bridge, turning “being a universal arrow from X” into a universal property
 in that sense.  Putting the completion through it would give the
 uniqueness statement a second, independent derivation.

 It does not typecheck here, and the obstruction is NOT this
 development's.  Instantiating the bridge at [CMet_Incl] is rejected for
 universe inconsistency, and so is instantiating it at the trivial control
 [Id[Sets]].  Be precise about the SCOPE of that: the bridge is NOT
 uninstantiable in general — it elaborates at small categories ([_1], [_2])
 and at [Cat].  What it is rejected at is the tree's LARGE concrete
 categories: [Sets], [Coq], and the [CMet_Incl] wanted here.  The
 rejection is therefore a property of the bridge, not of [Met]: it has no
 consumer anywhere in the tree (its name occurs only in its own file and in
 two header paragraphs), and this is the first attempt to give it one.
 Test/ProbeMet.v pins the control rejection so that the day the universes
 are repaired, the probe says so.

 Uniqueness is accordingly delivered ONLY through Theory/Universal/Arrow.v
 above — which is machinery, not a hand proof, and is the donor the issue
 names first. 

 --------
 尝试了另一条通用路径，但被阻塞。该库有第二条通用唯一性定理——[univ_property_unique_up_to_unique_iso]（Structure/UniversalProperty.v），它通过表示性和Yoneda引理来论证，而不是通过中介计算——此外[UniversalArrowIsUniversalProperty]（Structure/UniversalProperty/Universal/Arrow.v）自称是桥梁，将“作为从X出发的通用箭头”转化为在该意义下的通用性质。通过它完成操作将为唯一性陈述提供第二条独立的推导。在这里它不能进行类型检查，并且阻碍并不是这个开发的。 在 [CMet_Incl] 实例化桥因宇宙不一致而被拒绝，在平凡控制 [Id[Sets] 实例化它也同样被拒绝。 关于其范围要精确：桥并不是一般情况下无法实例化——它在小范畴（[_1], [_2]）以及 [Cat] 上可以展开。 它被拒绝的是树的大的具体范畴：[Sets], [Coq]，以及这里想要的 [CMet_Incl]。因此，这种拒绝是桥的属性，而不是 [Met] 的属性：它在树中的任何地方都没有消费者（它的名字只出现在它自己的文件和两个标题段落中），这是第一次尝试给它一个消费者。Test/ProbeMet.v 固定了控制拒绝，以便在宇宙修复的那一天，探针会指出这一点。

 因此，唯一性仅通过上面的 Theory/Universal/Arrow.v 提供——它是机械装置，而不是手动证明，并且是发布问题名称的捐赠者。
*)

(* * ** Non-vacuity: a completion that genuinely adds a point / * ** 非空性：真正增加一个观点的补充 *)

(*
 The completion would prove nothing if it could always be the identity.
 Instance/Met.v's [Harmonic] — the naturals placed at 1/(n+1) — is not
 complete ([Harmonic_not_MComplete]), and its completion contains the
 class of the identity sequence, which is at distance 1/(k+1) from the
 image of every point k and therefore is not in the image at all. 

 --------
 如果它总是可以是恒等的，那么完成什么也不能证明。  
 实例/Met.v 的 [Harmonic] —— 将自然数置于 1/(n+1) —— 不是完整的（[Harmonic_not_MComplete]），其完成包含恒等序列的类，该序列与每个点 k 的像的距离为 1/(k+1)，因此根本不在像中。
*)

Definition harm_point : Completion Harmonic :=
  cs_of Harmonic (fun n => n) harm_seq_MCauchy.

Theorem eta_Harmonic_not_surjective (k : Harmonic) :
  isometry_map (eta Harmonic) k ≈ harm_point → False.
Proof.
  intro H.
  pose proof (harm_pos k) as Hk.
  destruct (H (harm k / 2) ltac:(lra)) as [N HN].
  pose (n := Nat.max N (2 * k + 1)).
  specialize (HN n (Nat.le_max_l N (2 * k + 1))).
  (* the n-th term of the distance sequence is |harm k - harm n| / 距离序列的第 n 项是 |harm k - harm n| *)
  change (R_dist (Rabs (harm k - harm n)) 0 < harm k / 2) in HN.
  unfold R_dist in HN.
  rewrite Rminus_0_r, Rabs_pos_eq in HN by apply Rabs_pos.
  pose proof (harm_half k n (Nat.le_max_r N (2 * k + 1))) as Hsmall.
  pose proof (harm_pos n).
  rewrite Rabs_pos_eq in HN by lra.
  lra.
Qed.

(*
 Packaged: the embedding of the harmonic space into its completion misses
 a point.  Together with [Met_all_Monic] (every isometry is injective)
 this is the statement that the completion is STRICTLY larger. 

 --------
 封装：谐波空间嵌入其完备空间时遗漏了一个点。结合 [Met_all_Monic]（每个等距变换都是单射），这是说完备空间严格更大的声明。
*)
Theorem Completion_Harmonic_adds_a_point :
  ∃ z : Completion Harmonic,
    ∀ k : Harmonic, isometry_map (eta Harmonic) k ≈ z → False.
Proof. exact (harm_point; eta_Harmonic_not_surjective). Qed.
