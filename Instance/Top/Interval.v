Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.

Generalizable All Variables.

Open Scope R_scope.

(*
 The sections below quantify over the real formula being certified, so every
 proof inside them genuinely depends on its section variables.  Lib.v sets
 [Default Proof Using "Type"], which would discard them; the wider setting is
 the one already used for the same reason by
 Construction/Reflective/Idempotent.v and
 Construction/Localization/Universal.v. 

 --------
 下面的部分对被认证的实际公式进行量化，因此其中的每个证明都确实依赖于其部分变量。Lib.v 设置了 [Default Proof Using "Type"]，这会舍弃它们；更广泛的设置是 Construction/Reflective/Idempotent.v 和 Construction/Localization/Universal.v 已经出于相同原因使用的设置。
*)
Set Default Proof Using "All".

(* * * The unit interval as an object of Top / * * 单位区间作为拓扑对象 *)

(*
 nLab:      https://ncatlab.org/nlab/show/interval+object
 nLab:      https://ncatlab.org/nlab/show/metric+space
 Book:      Riehl, "Category Theory in Context", Epilogue §E.3 ("Freyd's
 characterization of the unit interval"), printed p. 255
 (PDF p. 275) — the ROAD NOT TAKEN here; see below
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 GTM 5, §I.5, printed p. 20 (the construction this file serves)
 Docs:      Rocq standard library, Reals (Rdefinitions, Raxioms, RIneq,
 Rbasic_fun) and the micromega decision procedures (Lra, Psatz)

 The unit interval, the unit square, and the little apparatus of continuous
 reparametrizations that the fundamental groupoid of
 Instance/Top/FundamentalGroupoid.v runs on.  Nothing here is specific to
 that construction beyond the choice of which formulas to certify.

 ON THE CITATIONS.  No book was opened for this file, and nothing below
 quotes one; each claim about what a printed source says is a paraphrase.
 The printed/PDF page pairs are taken from the in-tree page map
 doc/plan/books/riehl/pagemap.md (its Epilogue row fixes
 §E.3 at printed p. 255 = PDF p. 275, the offset being a uniform +20)
 and, for the section title and its contents,
 doc/plan/books/riehl/issues/drafts-E.md.  Riehl's §E.3 is FREYD'S
 CHARACTERIZATION: the interval carries a universal property — it is the
 terminal coalgebra of the wedge endofunctor on bipointed spaces, the
 halving map being the structure map — so that it need not be built out of
 the reals at all.  This file takes the other road deliberately, and builds
 the concrete stdlib-reals interval; the coalgebraic characterization is not
 formalized anywhere in this tree.

 THE INTERVAL AND WHAT IT COSTS.  There is no unique reasonable [0,1] in a
 constructive setting, and the choice has to be paid for.  This file takes
 the STANDARD LIBRARY REALS — `Rdefinitions.R` and its order — and defines

 Ipt := { a real together with proofs 0 <= r and r <= 1 }

 with `≈` comparing only the real part.  The price, measured rather than
 guessed, is exactly two stdlib axioms, and they are the ones that the
 standard library's own construction of R carries:

 ClassicalDedekindReals.sig_forall_dec
 FunctionalExtensionality.functional_extensionality_dep

 A third, `ClassicalDedekindReals.sig_not_dec`, is picked up by anything
 that goes through the least-upper-bound property (`Raxioms.completeness`);
 in this development that is the interval-connectedness argument in
 Instance/Top/FundamentalGroupoid.v, not this file.

 Two is the CEILING, not the invariable price, and the figure is measured
 per constant rather than sampled from the headlines.  `Print Assumptions`
 was run on all 160 constants defined here — there are no Program
 obligations to add to that count, every definition below being explicit —
 and the split is:

 1 constant  closed under the global context ([rf_id])
 34           carry [sig_forall_dec] ALONE — chiefly the [BallSpace]
 record with its projections and open-set lemmas, the
 [Ipt] setoid with its coordinate readers, and the two
 simplest reparametrizations [rf_zero] and [rf_rev]
 125           carry exactly the two above
 0           carry [sig_not_dec]

 All 34 are named in docs/AXIOMS.md under "Stdlib axioms", which
 is where the library's own policy puts stdlib axioms used by a concrete
 instance layer.  NO axiom is declared here, and none of the core theory
 acquires one: this file and its companion are the only two in the tree that
 import the reals at all.  CORRECTION (#410): not so, here or in the note
 on [Rcases] and [Rlin] below.  docs/AXIOMS.md, under "Stdlib axioms",
 names the development files that import the classical reals, and
 Instance/Top/Circle.v, Instance/Top/Solenoid.v and
 Instance/Top/Solenoid/Presentations.v import the standard library's
 constructive Cauchy reals (Reals/Cauchy), which carry no axiom.
 CORRECTION (#462): so does Instance/Top/Components/Paths.v.

 What the choice buys is that the interval is the real one, so the
 fundamental groupoid built on it is the classical construction and not a
 synthetic surrogate.  What it costs, besides the two axioms, is that the
 development inherits the standard library's classical real order: the
 comparisons `Rle_dec` and `total_order_T` are used freely below, and the
 pasting lemma depends on them.  A constructive-analysis treatment (Bishop
 reals, or a synthetic interval object) would avoid the axioms but would
 need a different pasting argument, since gluing along `u ≤ c` is precisely
 where decidability of the order enters.  That alternative is not attempted.

 THE TOPOLOGY.  Rather than the subspace topology of R as a set of opens,
 the file introduces [BallSpace] — a setoid with a distance satisfying three
 pseudometric laws — and generates a [TopSpace] from it by [BallTop]: a
 predicate is open when every point at which it holds carries a POSITIVE
 RADIUS inside which it still holds.  The radius is data, which is what
 discharges Instance/Top.v's type-valued union axiom with no choice
 principle.  On [0,1] this is the usual metric topology of `|x - y|`, and
 the square is the same construction over the sup distance.  That these
 coincide with the Euclidean subspace topology and with the product topology
 respectively is an identification of standard notions, made here in prose;
 neither statement is formalized in this tree, there being no other
 construction of those topologies to compare against.  Only two ball spaces
 are ever built ([BS_I] and [BS_Sq]); the general form costs nothing and is
 what lets one pasting lemma serve the interval and the square alike.

 Contents:

 BallSpace, BallTop      a distance, and the topology it generates
 lipschitz_continuous    Lipschitz maps of ball spaces are continuous
 Ipt, BS_I, I_Top        the unit interval as an object of Top
 BS_prod, BS_Sq, Sq_Top  the unit square, under the sup distance
 I_arrow, Sq_arrow,
 SqSq_arrow              arrows of Top from certified real formulas
 paste_arrow             gluing two arrows along a level set of a
 1-Lipschitz coordinate, with [paste_left] and
 [paste_right] evaluating the two halves
 rf_id ... rf_assoc      the reparametrization formulas, each Lipschitz
 with constant 2
 I_dbl, I_dbl', I_rev,
 I_assoc, I_tent         those formulas as arrows I_Top ~> I_Top
 Sq_flip, Sq_lower,
 Sq_upper, Sq_leftside,
 Sq_rightside            the reindexings of the square
 Sq_hmap                 the straight-line homotopy of parameters

 WHAT IS NOT HERE.  No metric-space theory beyond what the topology needs:
 no completeness, no compactness of [0,1], no intermediate value theorem.
 The one genuinely analytic fact the development uses — that a continuous
 map from the interval to a two-point discrete space is constant — is proved
 in the companion file, where it is needed.

 EXPORTED, WITH NO CURRENT CONSUMER.  Eight of the constants below are
 proved and exported but referenced by nothing in the tree, this file
 included.  Counted from the `.glob` reference records rather than by
 reading, they are: [bdist_nonneg] and [bdist_proper]; [RLip_max]; and the
 five evaluation lemmas [I_arrow_eval], [I_assoc_eval], [I_tent_eval],
 [Sq_arrow_eval] and [Sq_first_eval].  Most complete a pair or a family
 whose other members are genuinely used: [RLip_min] by [rf_assoc_lip] here,
 and [I_dbl_eval], [I_dbl'_eval], [I_rev_eval], [Sq_hmap_eval] and the
 [Sq_*_t]/[Sq_*_s] readers by the companion file.  The pseudometric three
 are the exception — [bdist_respects] is referenced only by [bdist_proper],
 and nothing at all references [bdist_nonneg] or [bdist_proper] — but they
 are what makes the [BallSpace] comment's claim about derived laws true, so
 they stay.  Nothing here is removed on this file's own judgement; the
 decision to keep or drop is the maintainer's. 

 --------
 nLab：       https://ncatlab.org/nlab/show/interval+object
 nLab：       https://ncatlab.org/nlab/show/metric+space
 书籍：      Riehl，《上下文中的范畴论》，尾声 §E.3（“Freyd 对单位区间的刻画”），印刷页 255（PDF 页 275）——这里未选择的道路；见下文
 书籍：      Mac Lane，《为工作中的数学家准备的范畴论》，第二版，GTM 5，§I.5，印刷页 20（本文件所用的构造）
 文档：      Rocq 标准库，实数（Rdefinitions、Raxioms、RIneq、Rbasic_fun）以及 micromega 判定过程（Lra、Psatz）

 单位区间、单位方形，以及连续重参数化的小装置，Instance/Top/FundamentalGroupoid.v 的基本群oid 在其上运行。这里的内容除了选择要认证的公式之外，并没有特定于该构造的内容。关于引用。此文件中没有翻阅任何书籍，下面也没有直接引用；每一条关于印刷源内容的说法都是意译。印刷/PDF 页码对照取自树内页码映射 doc/plan/books/riehl/pagemap.md（其结语行将 §E.3 修正为印刷第 255 页 = PDF 第 275 页，偏移量统一为 +20），以及章节标题及其内容取自 doc/plan/books/riehl/issues/drafts-E.md。Riehl 的 §E.3 是 FREYD 的表述：该区间具有一个普遍性质——它是双点空间上楔积自函子终端余代数，其中半分映射是结构映射——因此它根本不需要由实数构建。该文件故意走另一条道路，并构建具体的标准库实数区间；在此树中，余代数的刻画没有在任何地方形式化。

 区间及其代价。在构造性环境中，没有唯一合理的 [0,1]，并且必须为选择付出代价。该文件采用标准库实数——`Rdefinitions.R` 及其顺序——并定义

 Ipt := { 一个实数以及证明 0 <= r 且 r <= 1 }

 其中 `≈` 只比较实数部分。其代价，以测量而非猜测为准，恰好是两个标准库公理，而且它们正是标准库自身构造 R 所包含的：

 ClassicalDedekindReals.sig_forall_dec
 FunctionalExtensionality.functional_extensionality_dep第三个，`ClassicalDedekindReals.sig_not_dec`，会被任何通过上确界性质（`Raxioms.completeness`）的对象拾取；在这个开发中，那是在 Instance/Top/FundamentalGroupoid.v 中的区间连通性论证，而不是这个文件。

 二是天花板，而不是固定价格，并且该数值是按常量测量的，而非从头条采样。`Print Assumptions` 已在这里定义的所有 160 个常量上运行——没有 Program 义务需要增加到该计数，每一个下面的定义都是明确的——其划分如下:1 常数 在全局上下文中封闭 ([rf_id])
 34      携带 [sig_forall_dec] 仅 — 主要是 [BallSpace]
 记录及其投影和开集引理，
 [Ipt] 组态与其坐标读取器，以及两个
 最简单的重新参数化 [rf_zero] 和 [rf_rev]
 125      恰好携带上述两个
 0      携带 [sig_not_dec]所有34个都在 docs/AXIOMS.md 的“Stdlib axioms”下被命名，这是库自身的策略用于放置由具体实例层使用的标准库公理。这里没有声明任何公理，核心理论中也没有获取任何公理：这个文件及其配套文件是整个树中唯一导入实数的两个文件。更正（#410）：情况并非如此，无论是在这里还是在下面关于 [Rcases] 和 [Rlin] 的注释中。docs/AXIOMS.md 在“Stdlib axioms”下，列出了导入经典实数的发展文件，而 Instance/Top/Circle.v、Instance/Top/Solenoid.v 以及 Instance/Top/Solenoid/Presentations.v 导入了标准库的构造型柯西实数（Reals/Cauchy），这些不带任何公理。更正（#462）：Instance/Top/Components/Paths.v 也是如此。选择所带来的好处是区间是真实的，因此建立在其上的基本群oid是经典构造，而不是合成替代品。除此之外，它的代价是，除了两个公理之外，该发展继承了标准库的经典实数顺序：下面自由使用了比较 `Rle_dec` 和 `total_order_T`，并且拼接引理依赖于它们。建构分析处理（Bishop 实数，或合成区间对象）可以避免这些公理，但需要不同的拼接论证，因为沿 `u ≤ c` 拼接正是顺序可判定性起作用的地方。这种替代方案没有尝试。拓扑。文件介绍了 [BallSpace] —— 一个带有满足三条伪度量定律的距离的集合体 —— 并通过 [BallTop] 从中生成一个 [TopSpace] ：当一个谓词在每个点上成立时，如果存在一个正半径在该半径内谓词仍然成立，则该谓词是开集。半径是数据，这正是如何在没有选择公理的情况下实现 Instance/Top.v 的类型值并集公理。在 [0,1] 上，这是 `|x - y|` 的通常度量拓扑，并且平方是基于上确界距离的相同构造。这些分别与欧几里得子空间拓扑和积拓扑相一致，是对标准概念的确认，这里以散文形式表述；在此树中没有将任何陈述形式化，因为没有其他拓扑构造可供比较。仅构建了两个球空间（[BS_I] 和 [BS_Sq]）；一般形式无需额外成本，并且让一个拼接引理同时适用于区间和正方形。

 目录：BallSpace, BallTop      一个距离，以及它生成的拓扑
 lipschitz_continuous    球空间的 Lipschitz 映射是连续的
 Ipt, BS_I, I_Top        单位区间作为拓扑对象
 BS_prod, BS_Sq, Sq_Top  单位正方形，在 sup 距离下
 I_arrow, Sq_arrow,
 SqSq_arrow              来自已验证实数公式的拓扑箭头
 paste_arrow             沿 1-Lipschitz 坐标的水平集粘合两个箭头，使用 [paste_left] 和 [paste_right] 评估两半部分
 rf_id ...rf_assoc      重参数化公式，每个都是 Lipschitz 的，常数为 2
 I_dbl, I_dbl', I_rev,
 I_assoc, I_tent         那些作为箭头 I_Top ~> I_Top 的公式
 Sq_flip, Sq_lower,
 Sq_upper, Sq_leftside,
 Sq_rightside            方形的重新索引
 Sq_hmap                 参数的直线同伦

 这里没有的内容。除了拓扑所需之外，没有度量空间理论：
 没有 [0,1] 的完备性、紧性，也没有中值定理。
 发展的唯一真正分析性的事实——从区间到两个点离散空间的连续映射是常值——在伴随文件中证明，在需要时使用。已导出，但当前没有消费者。下面的八个常量已被证明并导出，但在树中没有任何引用，包括这个文件在内。它们是根据 `.glob` 的引用记录计算的，而不是通过阅读，它们是：[bdist_nonneg] 和 [bdist_proper]；[RLip_max]；以及五个评估引理 [I_arrow_eval]、[I_assoc_eval]、[I_tent_eval]、[Sq_arrow_eval] 和 [Sq_first_eval]。大多数组成了一对或一个族，其余成员确实被使用：[RLip_min] 在这里被 [rf_assoc_lip] 使用，还有 [I_dbl_eval]、[I_dbl'_eval]、[I_rev_eval]、[Sq_hmap_eval] 以及 [Sq_*_t]/[Sq_*_s] 的读取器由伴随文件使用。伪度量三是例外——[bdist_respects] 仅被 [bdist_proper] 引用，而 [bdist_nonneg] 或 [bdist_proper] 根本没有被引用——但它们正是使 [BallSpace] 评论关于派生法则的说法成立的原因，所以它们保留。这里没有任何内容是根据本文件自身判断而移除的；保留或删除的决定由维护者来做。
*)

(* * ** Case-splitting tactics for the real-number side arithmetic / * ** 实数侧算术的情况拆分策略 *)

(*
 Most real inequalities below become LINEAR once the three case-analysing
 operators of the standard library -- [Rabs], [Rmin], [Rmax] -- have been
 expanded into their underlying decisions.  [Rcases] performs exactly that
 expansion, and [Rlin] hands the resulting goals to [lra].  The exceptions
 IN THIS FILE are the four estimates that multiply two unknowns together --
 [Sq_lipschitz], [hfun_lo], [hfun_hi] and [hfun_lip] -- which call [nra]
 instead.  (The companion file has two more of its own.) 

 --------
 下面的大多数真实不等式一旦标准库的三个案例分析操作符 —— [Rabs]、[Rmin]、[Rmax] —— 被展开为其底层决策，就会变为线性。[Rcases] 完成的正是这种展开，而 [Rlin] 将结果目标交给 [lra]。这个文件中的例外是四个将两个未知数相乘的估计 —— [Sq_lipschitz]、[hfun_lo]、[hfun_hi] 和 [hfun_lip] —— 它们改为调用 [nra]。（伴随文件还有两个它自己特有的例子。）
*)
(*
 Scope note: [Rcases] splits the OUTERMOST decision it meets, so it applies
 only where [Rmin] and [Rmax] are not nested inside one another.  The one
 nested formula in this file, [rf_assoc], is handled instead by the three
 explicit branch equations [rf_assoc_first]/[rf_assoc_middle]/[rf_assoc_last],
 which rewrite the inner minimum away first. 

 --------
 范围说明：[Rcases] 分割它遇到的最外层决策，因此仅在 [Rmin] 和 [Rmax] 没有彼此嵌套的情况下适用。这个文件中唯一的嵌套公式 [rf_assoc] 则由三个显式分支方程 [rf_assoc_first] / [rf_assoc_middle] / [rf_assoc_last] 处理，它们会首先重写内部的最小值。
*)
(*
 Namespace note: both are GLOBAL [Ltac]s, not [Local] ones, and that is
 deliberate — the companion Instance/Top/FundamentalGroupoid.v calls [Rlin]
 31 times, against 49 calls here, so making them [Local] would break it.
 ([Rcases] is never invoked directly in either file; it is reached only
 through [Rlin].)  They do not live in Lib/Tactics.v, where CLAUDE.md records
 that this library's custom tactics belong, because they are built out of
 [Rabs]/[Rmin]/[Rmax] and [lra]: putting them there would pull Coq.Reals and
 micromega into Lib and hand the reals' axioms to every file in the tree,
 whereas at present this file and its companion are the only two that import
 the reals at all.  Two consequences worth stating: [Ltac] definitions are
 not recorded in the `.glob` files, so neither name is visible to a name
 sweep over glob entries and any claim of coverage from such a sweep does not
 extend to them; and both names are therefore in the global tactic namespace,
 where — checked across the tree — nothing else defines [Rcases] or [Rlin]. 

 --------
 命名空间说明：两者都是全局的 [Ltac]，而不是 [Local]，这是故意的——伴随的 Instance/Top/FundamentalGroupoid.v 文件对 [Rlin] 调用 31 次，而这里调用 49 次，因此将它们改为 [Local] 会破坏它。（[Rcases] 在任一文件中从未被直接调用；它仅通过 [Rlin] 到达。）它们不在 Lib/Tactics.v 中，CLAUDE.md 记录了该库的自定义策略属于该文件，因为它们是由 [Rabs] / [Rmin] / [Rmax] 和 [lra] 构建的；将它们放在那里会将 Coq.Reals 和 micromega 拉入 Lib，并将实数的公理提供给树中的每个文件，而目前这个文件及其伴随文件是唯一导入实数的两个文件。值得说明的两个后果：[Ltac] 的定义没有记录在 `.glob` 文件中，因此在对全局条目进行名称扫描时，这两个名称都不可见，而且任何此类扫描的覆盖声称都不适用于它们；因此，这两个名称都在全局策略命名空间中，在整个树中检查时，没有其他定义 [Rcases] 或 [Rlin] 的内容。
*)
Ltac Rcases :=
  unfold Rabs, Rmin, Rmax;
  repeat
    match goal with
    | [ |- context[Rcase_abs ?x] ]  => destruct (Rcase_abs x)
    | [ |- context[Rle_dec ?x ?y] ] => destruct (Rle_dec x y)
    end.

Ltac Rlin := Rcases; lra.

(** ** Ball spaces / ** 球空间 *)

(*
 A carrier with a distance, enough to generate a topology by balls.  The
 three laws are the pseudometric ones stated for a setoid: the distance
 vanishes on `≈`-equal points, it is symmetric, and it satisfies the
 triangle inequality.  Nonnegativity and respectfulness are derived below
 rather than demanded — [bdist_nonneg] for the first, [bdist_respects] and
 its two-sided [Proper] form [bdist_proper] for the second — and separation
 (distance zero implies `≈`) is never needed: the topology only ever moves
 outwards from a point. 

 --------
 一个具有距离的载体，足以通过球生成一个拓扑。三个定律是为集合组定义的拟度量定律：距离在  `≈` 相等的点上为零，它是对称的，并且满足三角不等式。非负性和尊重性在下面推导出来，而不是要求的 —— 第一个是 [bdist_nonneg]，第二个的形式是 [bdist_respects] 及其双边 [Proper] 形成 [bdist_proper] —— 而分离性（距离为零意味着 `≈`）从不需要：拓扑总是从一点向外扩展。
*)
Record BallSpace@{o} := {
  ball_carrier :> SetoidObject@{o o};

  bdist : ball_carrier → ball_carrier → R;

  bdist_zero : ∀ x y : ball_carrier, x ≈ y → bdist x y = 0;
  bdist_sym : ∀ x y : ball_carrier, bdist x y = bdist y x;
  bdist_tri : ∀ x y z : ball_carrier, bdist x z <= bdist x y + bdist y z
}.

Arguments bdist {_} _ _.

Lemma bdist_nonneg (A : BallSpace) (x y : A) : 0 <= bdist x y.
Proof.
  pose proof (bdist_tri A x y x) as Htri.
  rewrite (bdist_sym A y x) in Htri.
  rewrite (bdist_zero A x x (reflexivity x)) in Htri.
  lra.
Qed.

(*
 Respectfulness in the first argument: the two triangle inequalities through
 the `≈`-equal pair squeeze the two distances together, [bdist_zero] having
 collapsed the connecting term to 0 in each direction. 

 --------
 在第一个论点中的尊重：通过 `≈` -相等对的两个三角不等式将两个距离压在一起，[bdist_zero] 已将每个方向的连接项缩减为0。
*)
Lemma bdist_respects (A : BallSpace) (x x' y : A) :
  x ≈ x' → bdist x y = bdist x' y.
Proof.
  intro H.
  pose proof (bdist_tri A x x' y) as H1.
  pose proof (bdist_tri A x' x y) as H2.
  rewrite (bdist_zero A x x' H) in H1.
  rewrite (bdist_zero A x' x (symmetry H)) in H2.
  lra.
Qed.

(*
 And in both arguments at once, by symmetry.  This is the [Proper] form the
 library states respectfulness in; the target relation is Leibniz equality
 because the distance lands in R, not in a setoid. 

 --------
 并且通过对称性，同时在两个参数上。这是库中称之为 [Proper] 的形式；目标关系是莱布尼茨等价，因为距离落在 R 中，而不是在一个集体中。
*)
Lemma bdist_proper (A : BallSpace) :
  Proper (equiv ==> equiv ==> eq) (@bdist A).
Proof.
  intros x x' Hx y y' Hy.
  rewrite (bdist_respects A x x' y Hx).
  rewrite (bdist_sym A x' y), (bdist_respects A y y' x' Hy).
  exact (bdist_sym A y' x').
Qed.

(*
 A predicate is open when every point at which it holds carries a positive
 radius inside which it continues to hold.  For a metric space this is the
 usual topology; the radius is DATA, which is what lets the union axiom be
 discharged without any choice principle. 

 --------
 当一个谓词在其成立的每一个点上都有一个正半径，在该半径内它继续成立时，该谓词是开放的。对于度量空间来说，这就是通常的拓扑；半径就是数据，这使得可以在不使用任何选择公理的情况下满足并集公理。
*)
Definition ball_open (A : BallSpace) (U : A → Type) : Type :=
  ∀ x : A, U x → { d : R & ((0 < d) ∧ (∀ y : A, bdist x y < d → U y))%type }.

Lemma ball_respects (A : BallSpace) (U V : A → Type) :
  (∀ x, U x ↔ V x) → ball_open A U → ball_open A V.
Proof.
  intros HUV HU x Vx.
  destruct (HU x (snd (HUV x) Vx)) as [d [Hd Hball]].
  exists d; split.
  - exact Hd.
  - intros y Hy; exact (fst (HUV y) (Hball y Hy)).
Qed.

(* Opens respect the carrier's own equality: `≈`-equal points are at distance zero, hence inside every ball around one another. / 开口尊重承运人的自身平等：`≈` - 相等点的距离为零，因此它们位于彼此周围的每一个球内。 *)
Lemma ball_proper (A : BallSpace) (U : A → Type) :
  ball_open A U → ∀ x y : A, x ≈ y → U x → U y.
Proof.
  intros HU x y Hxy Ux.
  destruct (HU x Ux) as [d [Hd Hball]].
  apply Hball.
  rewrite (bdist_zero A x y Hxy).
  exact Hd.
Qed.

Lemma ball_union (A : BallSpace) (I : Type) (U : I → (A → Type)) :
  (∀ i, ball_open A (U i)) → ball_open A (fun x => { i : I & U i x }).
Proof.
  intros HU x w.
  destruct (HU (projT1 w) x (projT2 w)) as [d [Hd Hball]].
  exists d; split.
  - exact Hd.
  - intros y Hy; exact (projT1 w; Hball y Hy).
Qed.

Lemma ball_whole (A : BallSpace) : ball_open A (fun _ => poly_unit).
Proof.
  intros x _.
  exists 1; split.
  - lra.
  - intros y _; exact ttt.
Qed.

Lemma ball_inter (A : BallSpace) (U V : A → Type) :
  ball_open A U → ball_open A V → ball_open A (fun x => U x ∧ V x).
Proof.
  intros HU HV x w.
  destruct (HU x (fst w)) as [d1 [Hd1 Hb1]].
  destruct (HV x (snd w)) as [d2 [Hd2 Hb2]].
  exists (Rmin d1 d2); split.
  - Rlin.
  - intros y Hy; split.
    + apply Hb1; revert Hy; Rlin.
    + apply Hb2; revert Hy; Rlin.
Qed.

Definition BallTop (A : BallSpace) : TopSpace := {|
  top_carrier   := ball_carrier A;
  IsOpen        := ball_open A;
  open_respects := ball_respects A;
  open_proper   := ball_proper A;
  open_union    := ball_union A;
  open_whole    := ball_whole A;
  open_inter    := ball_inter A
|}.

(*
 A Lipschitz map of ball spaces is continuous: shrink the target radius by
 the Lipschitz constant.  This is the only route to continuity used for the
 parameter maps below; the maps that are merely piecewise Lipschitz are
 handled by [paste_arrow] instead. 

 --------
 球空间的 Lipschitz 映射是连续的：将目标半径按 Lipschitz 常数缩小。这是下文参数映射使用的唯一连续性途径；那些仅是分段 Lipschitz 的映射则由 [paste_arrow] 处理。
*)
Lemma lipschitz_continuous (A B : BallSpace)
      (f : SetoidMorphism (ball_carrier A) (ball_carrier B)) (L : R) (HL : 0 < L)
      (Hf : ∀ x y : A, bdist (f x) (f y) <= L * bdist x y) :
  Continuous (BallTop A) (BallTop B) f.
Proof.
  intros U HU x Ufx.
  destruct (HU (f x) Ufx) as [d [Hd Hball]].
  assert (HL0 : L <> 0) by lra.
  exists (d / L); split.
  - unfold Rdiv.
    apply Rmult_lt_0_compat; [ exact Hd | now apply Rinv_0_lt_compat ].
  - intros y Hy.
    apply Hball.
    apply Rle_lt_trans with (r2 := L * bdist x y).
    + exact (Hf x y).
    + replace d with (L * (d / L)) by (field; exact HL0).
      now apply Rmult_lt_compat_l.
Qed.

(** ** The interval and the square / ** 间隔与平方 *)

(*
 A point of [0,1]: a real together with its two bounds.  The bounds are
 [Prop]-valued, and the setoid equality below compares only the real part,
 so no proof irrelevance is needed anywhere. 

 --------
 [0,1] 的一个点：一个实数以及它的两个界。界是 [Prop] 值的，并且下面的集合等价只比较实部，所以任何地方都不需要证明无关性。
*)
Record Ipt := mkI {
  ival :> R;
  ipt_lo : 0 <= ival;
  ipt_hi : ival <= 1
}.

Definition Ipt_equiv (x y : Ipt) : Type := ival x = ival y.

Lemma Ipt_equiv_Equivalence : Equivalence Ipt_equiv.
Proof.
  constructor; unfold Ipt_equiv.
  - intro x; reflexivity.
  - intros x y H; now symmetry.
  - intros x y z H1 H2; now transitivity (ival y).
Qed.

Definition Ipt_Setoid : Setoid Ipt := {|
  equiv        := Ipt_equiv;
  setoid_equiv := Ipt_equiv_Equivalence
|}.

Definition Ipt_Object : SetoidObject := {|
  carrier   := Ipt;
  is_setoid := Ipt_Setoid
|}.

Lemma BS_I_zero (x y : Ipt_Object) : x ≈ y → Rabs (ival x - ival y) = 0.
Proof.
  intro H.
  assert (Heq : ival x = ival y) by exact H.
  Rlin.
Qed.

Lemma BS_I_sym (x y : Ipt_Object) :
  Rabs (ival x - ival y) = Rabs (ival y - ival x).
Proof. Rlin. Qed.

Lemma BS_I_tri (x y z : Ipt_Object) :
  Rabs (ival x - ival z) <= Rabs (ival x - ival y) + Rabs (ival y - ival z).
Proof. Rlin. Qed.

Definition BS_I : BallSpace := {|
  ball_carrier := Ipt_Object;
  bdist        := fun x y => Rabs (ival x - ival y);
  bdist_zero   := BS_I_zero;
  bdist_sym    := BS_I_sym;
  bdist_tri    := BS_I_tri
|}.

Definition I_Top : TopSpace := BallTop BS_I.

(* The two endpoints, as points of the interval. / 两个端点，作为区间的点。 *)
Definition I_zero : Ipt := mkI 0 (Rle_refl 0) Rle_0_1.
Definition I_one : Ipt := mkI 1 Rle_0_1 (Rle_refl 1).

(* The product of two ball spaces, under the sup distance. Only the square [0,1]² is needed downstream, but the construction costs nothing extra in general form. / 在上确界距离下的两个球空间的乘积。下游只需要平方 [0,1] ²，但在一般形式下，这种构造不会额外增加成本。 *)
Record BSprod_pt (A B : BallSpace) := mkP {
  bs_fst : A;
  bs_snd : B
}.

Arguments mkP {_ _} _ _.
Arguments bs_fst {_ _} _.
Arguments bs_snd {_ _} _.

Definition BSprod_equiv (A B : BallSpace) (x y : BSprod_pt A B) : Type :=
  (bs_fst x ≈ bs_fst y) ∧ (bs_snd x ≈ bs_snd y).

Lemma BSprod_equiv_Equivalence (A B : BallSpace) :
  Equivalence (BSprod_equiv A B).
Proof.
  constructor; unfold BSprod_equiv.
  - intro x; split; reflexivity.
  - intros x y H; split; symmetry; [ exact (fst H) | exact (snd H) ].
  - intros x y z H1 H2; split.
    + transitivity (bs_fst y); [ exact (fst H1) | exact (fst H2) ].
    + transitivity (bs_snd y); [ exact (snd H1) | exact (snd H2) ].
Qed.

Definition BSprod_Setoid (A B : BallSpace) : Setoid (BSprod_pt A B) := {|
  equiv        := BSprod_equiv A B;
  setoid_equiv := BSprod_equiv_Equivalence A B
|}.

Definition BSprod_Object (A B : BallSpace) : SetoidObject := {|
  carrier   := BSprod_pt A B;
  is_setoid := BSprod_Setoid A B
|}.

Definition BSprod_dist (A B : BallSpace) (x y : BSprod_Object A B) : R :=
  Rmax (bdist (bs_fst x) (bs_fst y)) (bdist (bs_snd x) (bs_snd y)).

Lemma BSprod_zero (A B : BallSpace) (x y : BSprod_Object A B) :
  x ≈ y → BSprod_dist A B x y = 0.
Proof.
  intro H.
  unfold BSprod_dist.
  rewrite (bdist_zero A _ _ (fst H)), (bdist_zero B _ _ (snd H)).
  Rlin.
Qed.

Lemma BSprod_sym (A B : BallSpace) (x y : BSprod_Object A B) :
  BSprod_dist A B x y = BSprod_dist A B y x.
Proof.
  unfold BSprod_dist.
  rewrite (bdist_sym A (bs_fst x)), (bdist_sym B (bs_snd x)).
  reflexivity.
Qed.

Lemma BSprod_tri (A B : BallSpace) (x y z : BSprod_Object A B) :
  BSprod_dist A B x z <= BSprod_dist A B x y + BSprod_dist A B y z.
Proof.
  unfold BSprod_dist.
  pose proof (bdist_tri A (bs_fst x) (bs_fst y) (bs_fst z)) as H1.
  pose proof (bdist_tri B (bs_snd x) (bs_snd y) (bs_snd z)) as H2.
  Rlin.
Qed.

Definition BS_prod (A B : BallSpace) : BallSpace := {|
  ball_carrier := BSprod_Object A B;
  bdist        := BSprod_dist A B;
  bdist_zero   := BSprod_zero A B;
  bdist_sym    := BSprod_sym A B;
  bdist_tri    := BSprod_tri A B
|}.

Definition BS_Sq : BallSpace := BS_prod BS_I BS_I.

Definition Sq_Top : TopSpace := BallTop BS_Sq.

(* The two coordinates of a point of the square, as reals. / 正方形某一点的两个坐标，作为实数。 *)
Definition sq_t (z : BS_Sq) : R := ival (bs_fst z).
Definition sq_s (z : BS_Sq) : R := ival (bs_snd z).

(** ** A small Lipschitz calculus / ** 一个小的 Lipschitz 微积分 *)

(*
 Every reparametrization used downstream is a minimum or maximum of affine
 functions, hence globally Lipschitz on all of R with an explicit constant.
 [RLip] records that constant; the three closure lemmas below are all that
 is needed to certify the concrete formulas. 

 --------
 下游使用的每个重参数化都是仿射函数的最小值或最大值，因此在整个 R 上是全局 Lipschitz，并具有明确的常数。[RLip] 记录了该常数；下面的三个封闭引理就是认证具体公式所需要的全部内容。
*)
Definition RLip (L : R) (k : R → R) : Prop :=
  ∀ a b, Rabs (k a - k b) <= L * Rabs (a - b).

Lemma Rabs_Rmin_le (a b a' b' : R) :
  Rabs (Rmin a b - Rmin a' b') <= Rmax (Rabs (a - a')) (Rabs (b - b')).
Proof. Rlin. Qed.

Lemma Rabs_Rmax_le (a b a' b' : R) :
  Rabs (Rmax a b - Rmax a' b') <= Rmax (Rabs (a - a')) (Rabs (b - b')).
Proof. Rlin. Qed.

Lemma RLip_min (L : R) (f g : R → R) :
  RLip L f → RLip L g → RLip L (fun t => Rmin (f t) (g t)).
Proof.
  intros Hf Hg a b.
  apply Rle_trans with
    (r2 := Rmax (Rabs (f a - f b)) (Rabs (g a - g b))).
  - apply Rabs_Rmin_le.
  - apply Rmax_lub; [ apply Hf | apply Hg ].
Qed.

Lemma RLip_max (L : R) (f g : R → R) :
  RLip L f → RLip L g → RLip L (fun t => Rmax (f t) (g t)).
Proof.
  intros Hf Hg a b.
  apply Rle_trans with
    (r2 := Rmax (Rabs (f a - f b)) (Rabs (g a - g b))).
  - apply Rabs_Rmax_le.
  - apply Rmax_lub; [ apply Hf | apply Hg ].
Qed.

Lemma RLip_ext (L : R) (f g : R → R) : (∀ t, f t = g t) → RLip L f → RLip L g.
Proof.
  intros Hfg Hf a b.
  rewrite <- (Hfg a), <- (Hfg b).
  apply Hf.
Qed.

Lemma RLip_affine (m q L : R) : Rabs m <= L → RLip L (fun t => m * t + q).
Proof.
  intros Hm a b.
  replace (m * a + q - (m * b + q)) with (m * (a - b)) by ring.
  rewrite Rabs_mult.
  apply Rmult_le_compat_r; [ apply Rabs_pos | exact Hm ].
Qed.

(* A convenient packaging of the two-factor product bound, used repeatedly in the square estimates below. / 两因素产品捆绑的便利包装，在下面的平方估计中反复使用。 *)
Lemma Rabs_mult_le (x y a b : R) :
  Rabs x <= a → Rabs y <= b → Rabs (x * y) <= a * b.
Proof.
  intros Hx Hy.
  rewrite Rabs_mult.
  apply Rmult_le_compat; solve [ apply Rabs_pos | assumption ].
Qed.

(* * ** Arrows of Top out of the interval and the square / * ** 箭头从区间和方形的顶部出来 *)

Section IArrow.

Context (k : R → R).
Context (L : R).
Context (HL : 0 < L).
Context (Hr0 : ∀ t, 0 <= t → t <= 1 → 0 <= k t).
Context (Hr1 : ∀ t, 0 <= t → t <= 1 → k t <= 1).
Context (Hlip : RLip L k).

Definition I_point (x : Ipt) : Ipt :=
  mkI (k (ival x)) (Hr0 _ (ipt_lo x) (ipt_hi x)) (Hr1 _ (ipt_lo x) (ipt_hi x)).

Definition I_setoid_map : SetoidMorphism Ipt_Object Ipt_Object.
Proof.
  refine {| morphism := I_point |}.
  intros x y Hxy.
  assert (Heq : ival x = ival y) by exact Hxy.
  exact (f_equal k Heq).
Defined.

Definition I_arrow : I_Top ~{Top}~> I_Top :=
  Build_ContinuousMorphism I_Top I_Top I_setoid_map
    (lipschitz_continuous BS_I BS_I I_setoid_map L HL
       (fun x y => Hlip (ival x) (ival y))).

Lemma I_arrow_eval (x : Ipt) : ival (I_arrow x) = k (ival x).
Proof. reflexivity. Qed.

End IArrow.

(* The componentwise map of the square, built from two interval formulas. All five reindexings of a homotopy used downstream have this shape. / 由两个区间公式构建的平方的分量映射。下游使用的同伦的所有五种重新索引都有这种形状。 *)
Section SqSqArrow.

Context (k1 k2 : R → R).
Context (L : R).
Context (HL : 0 < L).
Context (Hr0 : ∀ t, 0 <= t → t <= 1 → 0 <= k1 t).
Context (Hr1 : ∀ t, 0 <= t → t <= 1 → k1 t <= 1).
Context (Hs0 : ∀ t, 0 <= t → t <= 1 → 0 <= k2 t).
Context (Hs1 : ∀ t, 0 <= t → t <= 1 → k2 t <= 1).
Context (Hlip1 : RLip L k1).
Context (Hlip2 : RLip L k2).

Definition SqSq_point (z : BS_Sq) : BS_Sq :=
  @mkP BS_I BS_I (I_point k1 Hr0 Hr1 (bs_fst z)) (I_point k2 Hs0 Hs1 (bs_snd z)).

Definition SqSq_setoid_map :
  SetoidMorphism (ball_carrier BS_Sq) (ball_carrier BS_Sq).
Proof.
  refine {| morphism := SqSq_point |}.
  intros z w Hzw.
  assert (H1 : ival (bs_fst z) = ival (bs_fst w)) by exact (fst Hzw).
  assert (H2 : ival (bs_snd z) = ival (bs_snd w)) by exact (snd Hzw).
  exact (f_equal k1 H1, f_equal k2 H2).
Defined.

Lemma SqSq_lipschitz (z w : BS_Sq) :
  bdist (SqSq_point z) (SqSq_point w) <= L * bdist z w.
Proof.
  simpl; unfold BSprod_dist; simpl.
  apply Rmax_lub.
  - apply Rle_trans with (r2 := L * Rabs (ival (bs_fst z) - ival (bs_fst w))).
    + apply Hlip1.
    + apply Rmult_le_compat_l; [ lra | apply Rmax_l ].
  - apply Rle_trans with (r2 := L * Rabs (ival (bs_snd z) - ival (bs_snd w))).
    + apply Hlip2.
    + apply Rmult_le_compat_l; [ lra | apply Rmax_r ].
Qed.

Definition SqSq_arrow : Sq_Top ~{Top}~> Sq_Top :=
  Build_ContinuousMorphism Sq_Top Sq_Top SqSq_setoid_map
    (lipschitz_continuous BS_Sq BS_Sq SqSq_setoid_map L HL SqSq_lipschitz).

End SqSqArrow.

(*
 A map from the square to the interval, given by a two-variable formula.
 The Lipschitz hypothesis is stated ON THE SQUARE only: the formulas used
 below (convex combinations) are not globally Lipschitz on R², and there is
 no need for them to be. 

 --------
 从平方映射到区间的映射，由一个双变量公式给出。Lipschitz 假设仅在平方上陈述：下面使用的公式（凸组合）在 R² 上不是全局 Lipschitz 的，也不需要它们是全局 Lipschitz 的。
*)
Section SqArrow.

Context (k : R → R → R).
Context (L : R).
Context (HL : 0 < L).
Context (Hr0 : ∀ t s, 0 <= t → t <= 1 → 0 <= s → s <= 1 → 0 <= k t s).
Context (Hr1 : ∀ t s, 0 <= t → t <= 1 → 0 <= s → s <= 1 → k t s <= 1).
Context (Hlip : ∀ t s t' s',
            0 <= t → t <= 1 → 0 <= s → s <= 1 →
            0 <= t' → t' <= 1 → 0 <= s' → s' <= 1 →
            Rabs (k t s - k t' s') <= L * Rabs (t - t') + L * Rabs (s - s')).

Definition Sq_point (z : BS_Sq) : Ipt :=
  mkI (k (sq_t z) (sq_s z))
      (Hr0 _ _ (ipt_lo (bs_fst z)) (ipt_hi (bs_fst z))
             (ipt_lo (bs_snd z)) (ipt_hi (bs_snd z)))
      (Hr1 _ _ (ipt_lo (bs_fst z)) (ipt_hi (bs_fst z))
             (ipt_lo (bs_snd z)) (ipt_hi (bs_snd z))).

Definition Sq_setoid_map :
  SetoidMorphism (ball_carrier BS_Sq) (ball_carrier BS_I).
Proof.
  refine {| morphism := Sq_point |}.
  intros z w Hzw.
  assert (H1 : sq_t z = sq_t w) by exact (fst Hzw).
  assert (H2 : sq_s z = sq_s w) by exact (snd Hzw).
  assert (Hgoal : k (sq_t z) (sq_s z) = k (sq_t w) (sq_s w))
    by (rewrite H1, H2; reflexivity).
  exact Hgoal.
Defined.

Lemma Sq_lipschitz (z w : BS_Sq) :
  @bdist BS_I (Sq_point z) (Sq_point w) <= (2 * L) * @bdist BS_Sq z w.
Proof.
  simpl; unfold BSprod_dist; simpl.
  apply Rle_trans with
    (r2 := L * Rabs (sq_t z - sq_t w) + L * Rabs (sq_s z - sq_s w)).
  - apply Hlip;
      solve [ apply ipt_lo | apply ipt_hi ].
  - pose proof (Rmax_l (Rabs (ival (bs_fst z) - ival (bs_fst w)))
                       (Rabs (ival (bs_snd z) - ival (bs_snd w)))) as Hm1.
    pose proof (Rmax_r (Rabs (ival (bs_fst z) - ival (bs_fst w)))
                       (Rabs (ival (bs_snd z) - ival (bs_snd w)))) as Hm2.
    unfold sq_t, sq_s.
    nra.
Qed.

Definition Sq_arrow : Sq_Top ~{Top}~> I_Top :=
  Build_ContinuousMorphism Sq_Top I_Top Sq_setoid_map
    (lipschitz_continuous BS_Sq BS_I Sq_setoid_map (2 * L) ltac:(lra)
       Sq_lipschitz).

Lemma Sq_arrow_eval (z : BS_Sq) : ival (Sq_arrow z) = k (sq_t z) (sq_s z).
Proof. reflexivity. Qed.

End SqArrow.

(* * ** Pasting two arrows along a level set of a coordinate / * ** 沿坐标的水平集粘贴两个箭头 *)

(*
 The gluing lemma in the form the fundamental groupoid needs: A is a ball
 space carrying a 1-Lipschitz real coordinate u, and f and g are arrows of
 Top defined on ALL of A that agree wherever u takes the value c.  Their
 paste -- f where u ≤ c, g where u ≥ c -- is again continuous.
 Both maps being globally defined is what keeps subspaces out of the
 development entirely: the concatenation of paths uses [f := p ∘ I_dbl] and
 [g := q ∘ I_dbl'], whose reparametrizations are clamped rather than
 partial. 

 --------
 基本群丛所需形式的粘合引理：A 是一个带有 1-利普希茨实坐标 u 的球空间，f 和 g 是定义在整个 A 上的拓扑箭头，并且在 u 取值为 c 的地方它们一致。它们的粘贴——在 u ≤ c 时取 f，在 u ≥ c 时取 g——再次是连续的。两个映射都是全局定义的，这正是使子空间完全不涉及该发展的原因：路径的连接使用 [f := p ∘ I_dbl] 和 [g := q ∘ I_dbl']，其重新参数化是被固定的，而不是部分的。
*)

Section Paste.

Context {A : BallSpace}.
Context {X : TopSpace}.
Context (u : A → R).
Context (Hu : ∀ x y : A, Rabs (u x - u y) <= bdist x y).
Context (c : R).
Context (f g : BallTop A ~{Top}~> X).
Context (Hfg : ∀ x : A, u x = c → f x ≈ g x).

Definition paste_fun (x : A) : X := if Rle_dec (u x) c then f x else g x.

Lemma paste_coord (x y : A) : x ≈ y → u x = u y.
Proof.
  intro Hxy.
  pose proof (Hu x y) as H.
  rewrite (bdist_zero A x y Hxy) in H.
  revert H; Rlin.
Qed.

Definition paste_setoid_map : SetoidMorphism (ball_carrier A) (top_carrier X).
Proof.
  refine {| morphism := paste_fun |}.
  intros x y Hxy.
  unfold paste_fun.
  rewrite (paste_coord x y Hxy).
  destruct (Rle_dec (u y) c).
  - now apply proper_morphism.
  - now apply proper_morphism.
Defined.

Lemma paste_open (U : X → Type) (HU : IsOpen X U) :
  ball_open A (fun z => U (paste_fun z)).
Proof.
  intros x Ux.
  destruct (total_order_T (u x) c) as [[Hlt | Heq] | Hgt].
  - (* strictly below the level: the paste agrees with f nearby / 严格低于该水平：粘贴与附近的 f 一致 *)
    assert (Hfx : U (f x)).
    { revert Ux; unfold paste_fun; destruct (Rle_dec (u x) c) as [Hle | Hnle].
      - exact (fun w => w).
      - intro w; exfalso; apply Hnle; lra. }
    destruct (continuity f U HU x Hfx) as [d1 [Hd1 Hb1]].
    exists (Rmin d1 (c - u x)); split.
    + Rlin.
    + intros y Hy.
      pose proof (Hu x y) as Habs.
      assert (Huy : u y < c) by (revert Hy Habs; Rlin).
      unfold paste_fun; destruct (Rle_dec (u y) c) as [Hle | Hnle].
      * apply Hb1; revert Hy; Rlin.
      * exfalso; apply Hnle; lra.
  - (* exactly at the level: both halves are available, and they agree / 正好在这个水平：两半都可用，并且它们一致 *)
    assert (Hfx : U (f x)).
    { revert Ux; unfold paste_fun; destruct (Rle_dec (u x) c) as [Hle | Hnle].
      - exact (fun w => w).
      - intro w; exfalso; apply Hnle; lra. }
    assert (Hgx : U (g x)) by
      exact (open_proper X U HU (f x) (g x) (Hfg x Heq) Hfx).
    destruct (continuity f U HU x Hfx) as [d1 [Hd1 Hb1]].
    destruct (continuity g U HU x Hgx) as [d2 [Hd2 Hb2]].
    exists (Rmin d1 d2); split.
    + Rlin.
    + intros y Hy.
      unfold paste_fun; destruct (Rle_dec (u y) c) as [Hle | Hnle].
      * apply Hb1; revert Hy; Rlin.
      * apply Hb2; revert Hy; Rlin.
  - (* strictly above the level: the paste agrees with g nearby / 严格高于水平：糊状物与附近的 g 一致 *)
    assert (Hgx : U (g x)).
    { revert Ux; unfold paste_fun; destruct (Rle_dec (u x) c) as [Hle | Hnle].
      - intro w; exfalso; lra.
      - exact (fun w => w). }
    destruct (continuity g U HU x Hgx) as [d2 [Hd2 Hb2]].
    exists (Rmin d2 (u x - c)); split.
    + Rlin.
    + intros y Hy.
      pose proof (Hu x y) as Habs.
      assert (Huy : c < u y) by (revert Hy Habs; Rlin).
      unfold paste_fun; destruct (Rle_dec (u y) c) as [Hle | Hnle].
      * exfalso; lra.
      * apply Hb2; revert Hy; Rlin.
Qed.

Definition paste_arrow : BallTop A ~{Top}~> X :=
  Build_ContinuousMorphism (BallTop A) X paste_setoid_map paste_open.

Lemma paste_left (x : A) : u x <= c → paste_arrow x ≈ f x.
Proof.
  intro H.
  unfold paste_arrow; simpl; unfold paste_fun.
  destruct (Rle_dec (u x) c) as [Hle | Hnle].
  - reflexivity.
  - exfalso; exact (Hnle H).
Qed.

Lemma paste_right (x : A) : c <= u x → paste_arrow x ≈ g x.
Proof.
  intro H.
  unfold paste_arrow; simpl; unfold paste_fun.
  destruct (Rle_dec (u x) c) as [Hle | Hnle].
  - apply Hfg; lra.
  - reflexivity.
Qed.

End Paste.

(** ** The reparametrizations / ** 重新参数化 *)

(*
 Every reparametrization the fundamental groupoid needs, as a formula on R.
 Each is a minimum or a maximum of affine functions, hence Lipschitz with
 constant 2, and each carries [0,1] into [0,1].

 rf_id     the identity
 rf_rev    t ↦ 1 - t              reversal of a path
 rf_dbl    t ↦ min(2t, 1)         first half at double speed
 rf_dbl'   t ↦ max(2t - 1, 0)     second half at double speed
 rf_assoc  the piecewise-linear map that carries (p·q)·r to p·(q·r)
 rf_tent   t ↦ min(2t, 2 - 2t)    out and back
 rf_zero   the constant 0 

 --------
 基本群oid所需要的每一个重新参数化，都作为实数R上的公式。每一个都是仿射函数的最小值或最大值，因此具有常数为2的Lipschitz连续性，并且每一个都将[0,1]映射到[0,1]。

 rf_id     恒等映射
 rf_rev    t ↦ 1 - t              路径的反转
 rf_dbl    t ↦ min(2t, 1)         前半段以双倍速度
 rf_dbl'   t ↦ max(2t - 1, 0)     后半段以双倍速度
 rf_assoc  分段线性映射，使(p·q)·r映射为p·(q·r)
 rf_tent   t ↦ min(2t, 2 - 2t)    出去又回来
 rf_zero   常数0
*)

Definition rf_id (t : R) : R := t.
Definition rf_rev (t : R) : R := 1 - t.
Definition rf_dbl (t : R) : R := Rmin (2 * t) 1.
Definition rf_dbl' (t : R) : R := Rmax (2 * t - 1) 0.
Definition rf_assoc (t : R) : R := Rmin (2 * t) (Rmin (t + 1/4) (t / 2 + 1/2)).
Definition rf_tent (t : R) : R := Rmin (2 * t) (2 - 2 * t).
Definition rf_zero (t : R) : R := 0.

Lemma rf_id_lo (t : R) : 0 <= t → t <= 1 → 0 <= rf_id t.
Proof. unfold rf_id; Rlin. Qed.
Lemma rf_id_hi (t : R) : 0 <= t → t <= 1 → rf_id t <= 1.
Proof. unfold rf_id; Rlin. Qed.
Lemma rf_id_lip : RLip 2 rf_id.
Proof. intros a b; unfold rf_id; Rlin. Qed.

Lemma rf_rev_lo (t : R) : 0 <= t → t <= 1 → 0 <= rf_rev t.
Proof. unfold rf_rev; Rlin. Qed.
Lemma rf_rev_hi (t : R) : 0 <= t → t <= 1 → rf_rev t <= 1.
Proof. unfold rf_rev; Rlin. Qed.
Lemma rf_rev_lip : RLip 2 rf_rev.
Proof. intros a b; unfold rf_rev; Rlin. Qed.

Lemma rf_dbl_lo (t : R) : 0 <= t → t <= 1 → 0 <= rf_dbl t.
Proof. unfold rf_dbl; Rlin. Qed.
Lemma rf_dbl_hi (t : R) : 0 <= t → t <= 1 → rf_dbl t <= 1.
Proof. unfold rf_dbl; Rlin. Qed.
Lemma rf_dbl_lip : RLip 2 rf_dbl.
Proof. intros a b; unfold rf_dbl; Rlin. Qed.

Lemma rf_dbl'_lo (t : R) : 0 <= t → t <= 1 → 0 <= rf_dbl' t.
Proof. unfold rf_dbl'; Rlin. Qed.
Lemma rf_dbl'_hi (t : R) : 0 <= t → t <= 1 → rf_dbl' t <= 1.
Proof. unfold rf_dbl'; Rlin. Qed.
Lemma rf_dbl'_lip : RLip 2 rf_dbl'.
Proof. intros a b; unfold rf_dbl'; Rlin. Qed.

(*
 The three linear branches of [rf_assoc], each obtained by rewriting the
 INNER minimum away before the outer one.  These equations are what the
 associativity computation consumes; [rf_assoc] itself is never unfolded
 downstream. 

 --------
 [rf_assoc] 的三个线性分支，每个都是通过先将内部的最小项移开再处理外部的最小项得到的。这些方程是结合性计算所使用的；[rf_assoc] 本身在下游从未被展开。
*)
Lemma rf_assoc_first (t : R) : 0 <= t → t <= 1/4 → rf_assoc t = 2 * t.
Proof.
  intros H1 H2; unfold rf_assoc.
  rewrite (Rmin_left (t + 1/4) (t / 2 + 1/2)) by lra.
  rewrite (Rmin_left (2 * t) (t + 1/4)) by lra.
  reflexivity.
Qed.

Lemma rf_assoc_middle (t : R) : 1/4 <= t → t <= 1/2 → rf_assoc t = t + 1/4.
Proof.
  intros H1 H2; unfold rf_assoc.
  rewrite (Rmin_left (t + 1/4) (t / 2 + 1/2)) by lra.
  rewrite (Rmin_right (2 * t) (t + 1/4)) by lra.
  reflexivity.
Qed.

Lemma rf_assoc_last (t : R) : 1/2 <= t → t <= 1 → rf_assoc t = t / 2 + 1/2.
Proof.
  intros H1 H2; unfold rf_assoc.
  rewrite (Rmin_right (t + 1/4) (t / 2 + 1/2)) by lra.
  rewrite (Rmin_right (2 * t) (t / 2 + 1/2)) by lra.
  reflexivity.
Qed.

Lemma rf_assoc_lo (t : R) : 0 <= t → t <= 1 → 0 <= rf_assoc t.
Proof.
  intros H1 H2; unfold rf_assoc.
  apply Rmin_glb; [ lra | apply Rmin_glb; lra ].
Qed.

Lemma rf_assoc_hi (t : R) : 0 <= t → t <= 1 → rf_assoc t <= 1.
Proof.
  intros H1 H2; unfold rf_assoc.
  apply Rle_trans with (r2 := t / 2 + 1/2); [ | lra ].
  apply Rle_trans with (r2 := Rmin (t + 1/4) (t / 2 + 1/2)).
  - apply Rmin_r.
  - apply Rmin_r.
Qed.

Lemma rf_assoc_lip : RLip 2 rf_assoc.
Proof.
  apply (RLip_ext 2
           (fun t => Rmin (2 * t + 0) (Rmin (1 * t + 1/4) ((1/2) * t + 1/2)))).
  - intro t; unfold rf_assoc.
    replace (2 * t + 0) with (2 * t) by ring.
    replace (1 * t + 1/4) with (t + 1/4) by ring.
    replace ((1/2) * t + 1/2) with (t / 2 + 1/2) by field.
    reflexivity.
  - apply RLip_min.
    + apply RLip_affine; Rlin.
    + apply RLip_min; apply RLip_affine; Rlin.
Qed.

Lemma rf_tent_lo (t : R) : 0 <= t → t <= 1 → 0 <= rf_tent t.
Proof. unfold rf_tent; Rlin. Qed.
Lemma rf_tent_hi (t : R) : 0 <= t → t <= 1 → rf_tent t <= 1.
Proof. unfold rf_tent; Rlin. Qed.
Lemma rf_tent_lip : RLip 2 rf_tent.
Proof. intros a b; unfold rf_tent; Rlin. Qed.

Lemma rf_zero_lo (t : R) : 0 <= t → t <= 1 → 0 <= rf_zero t.
Proof. unfold rf_zero; Rlin. Qed.
Lemma rf_zero_hi (t : R) : 0 <= t → t <= 1 → rf_zero t <= 1.
Proof. unfold rf_zero; Rlin. Qed.
Lemma rf_zero_lip : RLip 2 rf_zero.
Proof. intros a b; unfold rf_zero; Rlin. Qed.

Lemma two_pos : 0 < 2.
Proof. lra. Qed.

(** ** The reparametrization arrows / ** 重参数化箭头 *)

Definition I_rev : I_Top ~{Top}~> I_Top :=
  I_arrow rf_rev 2 two_pos rf_rev_lo rf_rev_hi rf_rev_lip.

Definition I_dbl : I_Top ~{Top}~> I_Top :=
  I_arrow rf_dbl 2 two_pos rf_dbl_lo rf_dbl_hi rf_dbl_lip.

Definition I_dbl' : I_Top ~{Top}~> I_Top :=
  I_arrow rf_dbl' 2 two_pos rf_dbl'_lo rf_dbl'_hi rf_dbl'_lip.

Definition I_assoc : I_Top ~{Top}~> I_Top :=
  I_arrow rf_assoc 2 two_pos rf_assoc_lo rf_assoc_hi rf_assoc_lip.

Definition I_tent : I_Top ~{Top}~> I_Top :=
  I_arrow rf_tent 2 two_pos rf_tent_lo rf_tent_hi rf_tent_lip.

Lemma I_rev_eval (x : Ipt) : ival (I_rev x) = 1 - ival x.
Proof. reflexivity. Qed.
Lemma I_dbl_eval (x : Ipt) : ival (I_dbl x) = Rmin (2 * ival x) 1.
Proof. reflexivity. Qed.
Lemma I_dbl'_eval (x : Ipt) : ival (I_dbl' x) = Rmax (2 * ival x - 1) 0.
Proof. reflexivity. Qed.
Lemma I_assoc_eval (x : Ipt) : ival (I_assoc x) = rf_assoc (ival x).
Proof. reflexivity. Qed.
Lemma I_tent_eval (x : Ipt) : ival (I_tent x) = Rmin (2 * ival x) (2 - 2 * ival x).
Proof. reflexivity. Qed.

(** ** The reindexings of the square / ** 广场的重新索引 *)

Definition Sq_flip : Sq_Top ~{Top}~> Sq_Top :=
  SqSq_arrow rf_id rf_rev 2 two_pos rf_id_lo rf_id_hi rf_rev_lo rf_rev_hi
             rf_id_lip rf_rev_lip.

Definition Sq_lower : Sq_Top ~{Top}~> Sq_Top :=
  SqSq_arrow rf_id rf_dbl 2 two_pos rf_id_lo rf_id_hi rf_dbl_lo rf_dbl_hi
             rf_id_lip rf_dbl_lip.

Definition Sq_upper : Sq_Top ~{Top}~> Sq_Top :=
  SqSq_arrow rf_id rf_dbl' 2 two_pos rf_id_lo rf_id_hi rf_dbl'_lo rf_dbl'_hi
             rf_id_lip rf_dbl'_lip.

Definition Sq_leftside : Sq_Top ~{Top}~> Sq_Top :=
  SqSq_arrow rf_dbl rf_id 2 two_pos rf_dbl_lo rf_dbl_hi rf_id_lo rf_id_hi
             rf_dbl_lip rf_id_lip.

Definition Sq_rightside : Sq_Top ~{Top}~> Sq_Top :=
  SqSq_arrow rf_dbl' rf_id 2 two_pos rf_dbl'_lo rf_dbl'_hi rf_id_lo rf_id_hi
             rf_dbl'_lip rf_id_lip.

(** ** The homotopy parameter maps / ** 同伦参数映射 *)

(*
 The two-variable formula the whole development runs on:
 (t, s) ↦ (1 - s)·φ(t) + s·ψ(t), the straight-line homotopy in the
 PARAMETER between two reparametrizations.  [Sq_arrow] is applied exactly
 twice below, and this is the only one of the two formulas that mixes its
 arguments at all; the other, [Sq_first], is the first projection.  Unlike
 the interval formulas this one is not Lipschitz on all of R² -- the
 coefficient (1 - s) is unbounded -- so its estimate is stated over the
 square only. 

 --------
 整个开发所依赖的双变量公式：
 (t, s) ↦ (1 - s)·φ(t) + s·ψ(t)，在参数间的直线同伦，在两个重新参数化之间。[Sq_arrow] 在下面正好应用了两次，而这是两个公式中唯一一个真正混合其参数的；另一个 [Sq_first] 是第一个投影。不像区间公式，这个在整个 R² 上不是 Lipschitz 的——系数 (1 - s) 是无界的——所以它的估计只在方形上给出。
*)

Section HomotopyMap.

Context (phi psi : R → R).
Context (L : R).
Context (HL : 0 < L).
Context (Hphi0 : ∀ t, 0 <= t → t <= 1 → 0 <= phi t).
Context (Hphi1 : ∀ t, 0 <= t → t <= 1 → phi t <= 1).
Context (Hpsi0 : ∀ t, 0 <= t → t <= 1 → 0 <= psi t).
Context (Hpsi1 : ∀ t, 0 <= t → t <= 1 → psi t <= 1).
Context (Hphil : RLip L phi).
Context (Hpsil : RLip L psi).

Definition hfun (t s : R) : R := (1 - s) * phi t + s * psi t.

Lemma hfun_lo (t s : R) : 0 <= t → t <= 1 → 0 <= s → s <= 1 → 0 <= hfun t s.
Proof.
  intros Ht0 Ht1 Hs0 Hs1; unfold hfun.
  pose proof (Hphi0 t Ht0 Ht1).
  pose proof (Hpsi0 t Ht0 Ht1).
  nra.
Qed.

Lemma hfun_hi (t s : R) : 0 <= t → t <= 1 → 0 <= s → s <= 1 → hfun t s <= 1.
Proof.
  intros Ht0 Ht1 Hs0 Hs1; unfold hfun.
  pose proof (Hphi1 t Ht0 Ht1).
  pose proof (Hpsi1 t Ht0 Ht1).
  nra.
Qed.

Lemma hfun_lip (t s t' s' : R) :
  0 <= t → t <= 1 → 0 <= s → s <= 1 →
  0 <= t' → t' <= 1 → 0 <= s' → s' <= 1 →
  Rabs (hfun t s - hfun t' s')
    <= (2 * L + 1) * Rabs (t - t') + (2 * L + 1) * Rabs (s - s').
Proof.
  intros Ht0 Ht1 Hs0 Hs1 Ht'0 Ht'1 Hs'0 Hs'1.
  unfold hfun.
  replace ((1 - s) * phi t + s * psi t - ((1 - s') * phi t' + s' * psi t'))
    with ((1 - s) * (phi t - phi t') + s * (psi t - psi t')
            + (s - s') * (psi t' - phi t')) by ring.
  apply Rle_trans with
    (r2 := Rabs ((1 - s) * (phi t - phi t') + s * (psi t - psi t'))
             + Rabs ((s - s') * (psi t' - phi t'))).
  { apply Rabs_triang. }
  assert (H3 : Rabs ((s - s') * (psi t' - phi t')) <= Rabs (s - s') * 1).
  { apply Rabs_mult_le.
    - apply Rle_refl.
    - pose proof (Hphi0 t' Ht'0 Ht'1).
      pose proof (Hphi1 t' Ht'0 Ht'1).
      pose proof (Hpsi0 t' Ht'0 Ht'1).
      pose proof (Hpsi1 t' Ht'0 Ht'1).
      Rlin. }
  assert (H12 : Rabs ((1 - s) * (phi t - phi t') + s * (psi t - psi t'))
                  <= 2 * L * Rabs (t - t')).
  { apply Rle_trans with
      (r2 := Rabs ((1 - s) * (phi t - phi t'))
               + Rabs (s * (psi t - psi t'))).
    { apply Rabs_triang. }
    assert (H1 : Rabs ((1 - s) * (phi t - phi t')) <= 1 * (L * Rabs (t - t'))).
    { apply Rabs_mult_le; [ Rlin | apply Hphil ]. }
    assert (H2 : Rabs (s * (psi t - psi t')) <= 1 * (L * Rabs (t - t'))).
    { apply Rabs_mult_le; [ Rlin | apply Hpsil ]. }
    nra. }
  pose proof (Rabs_pos (t - t')).
  pose proof (Rabs_pos (s - s')).
  nra.
Qed.

Definition Sq_hmap : Sq_Top ~{Top}~> I_Top :=
  Sq_arrow hfun (2 * L + 1) ltac:(lra) hfun_lo hfun_hi hfun_lip.

Lemma Sq_hmap_eval (z : BS_Sq) :
  ival (Sq_hmap z) = (1 - sq_s z) * phi (sq_t z) + sq_s z * psi (sq_t z).
Proof. reflexivity. Qed.

End HomotopyMap.

(* * ** Points of the square, and its first projection / * ** 正方形的顶点及其第一投影 *)

Definition sq_pt (t s : Ipt) : BS_Sq := @mkP BS_I BS_I t s.

Lemma sq_pt_t (t s : Ipt) : sq_t (sq_pt t s) = ival t.
Proof. reflexivity. Qed.

Lemma sq_pt_s (t s : Ipt) : sq_s (sq_pt t s) = ival s.
Proof. reflexivity. Qed.

Lemma sq_first_lip (t s t' s' : R) :
  0 <= t → t <= 1 → 0 <= s → s <= 1 →
  0 <= t' → t' <= 1 → 0 <= s' → s' <= 1 →
  Rabs (t - t') <= 1 * Rabs (t - t') + 1 * Rabs (s - s').
Proof.
  intros; pose proof (Rabs_pos (s - s')); lra.
Qed.

Definition Sq_first : Sq_Top ~{Top}~> I_Top :=
  Sq_arrow (fun t _ => t) 1 Rlt_0_1
    (fun t s H0 _ _ _ => H0) (fun t s _ H1 _ _ => H1) sq_first_lip.

Lemma Sq_first_eval (z : BS_Sq) : ival (Sq_first z) = sq_t z.
Proof. reflexivity. Qed.

(* * ** Applying an arrow to points that agree on coordinates / * ** 将箭头应用于坐标一致的点 *)

(*
 The two respectfulness lemmas, in the form every computation below uses:
 an arrow out of the interval or the square only sees the real coordinates,
 so equal coordinates give `≈`-equal values. 

 --------
 这两个尊重性引理，以下每个计算使用的形式：
 来自区间或正方形的箭头只看到实数坐标，
 所以相等的坐标给出 `≈` -相等的值。
*)
Lemma Iap {X : TopSpace} (f : I_Top ~{Top}~> X) (x y : Ipt) :
  ival x = ival y → f x ≈ f y.
Proof. intro H; now apply proper_morphism. Qed.

Lemma Sqap {X : TopSpace} (F : Sq_Top ~{Top}~> X) (z w : BS_Sq) :
  sq_t z = sq_t w → sq_s z = sq_s w → F z ≈ F w.
Proof. intros H1 H2; apply proper_morphism; exact (H1, H2). Qed.

(** ** Coordinate computations / ** 坐标计算 *)

(*
 Every reindexing above acts on coordinates by its defining formula, and each
 of these equations holds by conversion.  Downstream proofs rewrite with them
 rather than unfolding the arrow constructors. 

 --------
 上述每个重新索引都通过其定义公式作用于坐标，并且通过转换每个方程都成立。下游证明使用它们进行重写，而不是展开箭头构造器。
*)

Lemma ival_I_zero : ival I_zero = 0.
Proof. reflexivity. Qed.

Lemma ival_I_one : ival I_one = 1.
Proof. reflexivity. Qed.

Lemma Sq_flip_t (z : BS_Sq) : sq_t (Sq_flip z) = sq_t z.
Proof. reflexivity. Qed.
Lemma Sq_flip_s (z : BS_Sq) : sq_s (Sq_flip z) = 1 - sq_s z.
Proof. reflexivity. Qed.

Lemma Sq_lower_t (z : BS_Sq) : sq_t (Sq_lower z) = sq_t z.
Proof. reflexivity. Qed.
Lemma Sq_lower_s (z : BS_Sq) : sq_s (Sq_lower z) = Rmin (2 * sq_s z) 1.
Proof. reflexivity. Qed.

Lemma Sq_upper_t (z : BS_Sq) : sq_t (Sq_upper z) = sq_t z.
Proof. reflexivity. Qed.
Lemma Sq_upper_s (z : BS_Sq) : sq_s (Sq_upper z) = Rmax (2 * sq_s z - 1) 0.
Proof. reflexivity. Qed.

Lemma Sq_leftside_t (z : BS_Sq) : sq_t (Sq_leftside z) = Rmin (2 * sq_t z) 1.
Proof. reflexivity. Qed.
Lemma Sq_leftside_s (z : BS_Sq) : sq_s (Sq_leftside z) = sq_s z.
Proof. reflexivity. Qed.

Lemma Sq_rightside_t (z : BS_Sq) : sq_t (Sq_rightside z) = Rmax (2 * sq_t z - 1) 0.
Proof. reflexivity. Qed.
Lemma Sq_rightside_s (z : BS_Sq) : sq_s (Sq_rightside z) = sq_s z.
Proof. reflexivity. Qed.

(* The 1-Lipschitz coordinates that [paste_arrow] is applied along. / [paste_arrow] 所应用的 1-利普希茨坐标。 *)
Lemma I_coord_lip (x y : BS_I) : Rabs (ival x - ival y) <= bdist x y.
Proof. apply Rle_refl. Qed.

Lemma Sq_t_lip (z w : BS_Sq) : Rabs (sq_t z - sq_t w) <= bdist z w.
Proof. apply Rmax_l. Qed.

Lemma Sq_s_lip (z w : BS_Sq) : Rabs (sq_s z - sq_s w) <= bdist z w.
Proof. apply Rmax_r. Qed.

(* * ** Endpoint values of the reparametrizations / * ** 重参数化的端点值 *)

Lemma rf_dbl_zero : rf_dbl 0 = 0.
Proof. unfold rf_dbl; Rlin. Qed.
Lemma rf_dbl_one : rf_dbl 1 = 1.
Proof. unfold rf_dbl; Rlin. Qed.
Lemma rf_dbl'_zero : rf_dbl' 0 = 0.
Proof. unfold rf_dbl'; Rlin. Qed.
Lemma rf_dbl'_one : rf_dbl' 1 = 1.
Proof. unfold rf_dbl'; Rlin. Qed.
Lemma rf_tent_zero : rf_tent 0 = 0.
Proof. unfold rf_tent; Rlin. Qed.
Lemma rf_tent_one : rf_tent 1 = 0.
Proof. unfold rf_tent; Rlin. Qed.
Lemma rf_assoc_zero : rf_assoc 0 = 0.
Proof. rewrite rf_assoc_first; lra. Qed.
Lemma rf_assoc_one : rf_assoc 1 = 1.
Proof. rewrite rf_assoc_last; lra. Qed.
