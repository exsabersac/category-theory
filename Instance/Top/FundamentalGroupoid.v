Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.
Require Import Coq.Bool.Bool.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Interval.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Structure.Groupoid.Basepoint.

Generalizable All Variables.

Open Scope R_scope.

(*
 Each of the five sections below quantifies over hypotheses that its proofs
 genuinely use but that do not occur in their statements -- the Lipschitz and
 endpoint constraints of [Straight], the two given homotopies of
 [HomotopyConcat], the equality decider of [IntervalConnected].  Lib.v's
 [Default Proof Using "Type"] would discard them; this is the same setting,
 for the same reason, as Instance/Top/Interval.v. 

 --------
 以下五个部分中的每一个都对其证明中实际使用但未出现在其陈述中的假设进行了量化——[Straight] 的 Lipschitz 和端点约束，[HomotopyConcat] 的两个给定的同伦，[IntervalConnected] 的等式判定器。Lib.v 的 [Default Proof Using "Type"] 会舍弃它们；这是相同的设置，原因与 Instance/Top/Interval.v 相同。
*)
Set Default Proof Using "All".

(* * * The fundamental groupoid of a topological space / * * 拓扑空间的基本群族 *)

(*
 nLab:      https://ncatlab.org/nlab/show/fundamental+groupoid
 nLab:      https://ncatlab.org/nlab/show/fundamental+group
 Wikipedia: https://en.wikipedia.org/wiki/Fundamental_groupoid
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 GTM 5, §I.5, printed p. 20 (PDF p. 30) — the construction of
 the fundamental groupoid, immediately after Definition 9
 Book:      Riehl, "Category Theory in Context", Example 1.1.13(ii),
 printed p. 8 (PDF p. 28); Corollary 1.5.14 and Remark 1.5.15,
 printed p. 36 (PDF p. 56)
 Paper:     Brown, "From groups to groupoids: a brief survey", Bulletin of
 the London Mathematical Society 19, 1987

 The fundamental groupoid π(X) of a space: its objects are the points of X,
 its arrows are the homotopy classes rel endpoints of paths, composition is
 the reparametrized concatenation and the inverse of a class is the class of
 the reversed path.  Every claim made below about what a printed source says
 is a paraphrase of the statement at the cited location; none of the books
 named above was consulted for this file, and nothing here quotes them.  The
 printed/PDF page pairs come from the in-tree page maps:
 doc/plan/books/riehl/pagemap.md, whose Riehl offset is a uniform +20, and
 doc/plan/books/maclane/pagemap.md, whose offset is +10 over the printed
 range 7-53 and is expressly NOT uniform across that book.

 Contents:

 Path X a b              a continuous map out of [0,1] with endpoints
 ArrowHomotopy a b p q   a homotopy rel endpoints between two arrows
 PathHomotopy p q        the same, between two paths
 ah_refl/ah_sym/ah_trans homotopy is an equivalence relation
 path_concat, path_rev   concatenation and reversal
 straight_homotopy       the straight-line homotopy of parameters, which
 is the single construction behind all four laws
 unit_left/right,
 assoc, inverse          the category and groupoid laws, each as an
 explicit homotopy
 path_concat_respects    concatenation is well defined on classes, by
 pasting rather than reparametrizing
 FundamentalGroupoid X   π(X) as a Category
 fundamental_groupoid_is_groupoid          IsGroupoid (π X)
 equal_points_iso        `≈`-equal points are isomorphic objects
 fundamental_group X a                     the vertex group at a
 fundamental_group_basepoint_independent   Riehl Corollary 1.5.14
 pointwise_homotopic     two paths agreeing pointwise are homotopic
 interval_to_discrete_constant_dec         every continuous map from
 [0,1] to a discrete space
 with decidable equality is
 constant
 interval_to_discrete_constant             that theorem at the two-point
 discrete space
 fundamental_group_inclusion_equivalence   Riehl Remark 1.5.15, at a
 single space only
 no_path_true_false, Bool_Discrete_pi_not_connected,
 TwoPoint_Indiscrete_pi_connected          the non-vacuity witnesses
 Bool_Discrete_loops_trivial,
 TwoPoint_Indiscrete_loops_trivial         both vertex groups trivial,
 at every base point

 THE INTERVAL, AND WHAT IT COSTS.  The unit interval, the unit square, the
 pasting lemma and the reparametrizations all come from
 Instance/Top/Interval.v, whose header states the choice in full: the
 STANDARD LIBRARY REALS, at a price of at most two stdlib axioms,

 ClassicalDedekindReals.sig_forall_dec
 FunctionalExtensionality.functional_extensionality_dep

 which is exactly what π(X) itself, [fundamental_groupoid_is_groupoid] and
 the base-point corollary [fundamental_group_basepoint_independent] each
 carry, plus a third,

 ClassicalDedekindReals.sig_not_dec

 for the results below that go through the least-upper-bound property.  Two
 is a CEILING and not an invariable charge: 34 of Interval.v's 160 constants
 carry only the first, and so does one of this file's.

 `Print Assumptions` was run on every constant of this file — all 113 of
 them, which is the 108 recorded in the `.glob` file TOGETHER WITH the five
 Program obligations [FundamentalGroupoid_obligation_1] .. [_5] that the
 [Program Definition] of π(X) generates and that no `.glob` sweep sees.  The
 split is:

 1 constant  closed under the global context ([bool_carriers_agree])
 1           carries [sig_forall_dec] ALONE ([const_arrow_eval])
 103           carry exactly the two above (98 of the glob-recorded
 constants, plus all five obligations)
 8           carry the third as well

 and the eight are the two internal lemmas of the least-upper-bound
 argument, [gval_endpoints] and [f_endpoints]; the general theorem they
 establish, [interval_to_discrete_constant_dec], with its two-point
 corollary [interval_to_discrete_constant]; and the four results about the
 discrete witness that use it — [no_path_true_false],
 [Bool_Discrete_not_pathconnected], [Bool_Discrete_pi_not_connected] and
 [Bool_Discrete_loops_trivial].  No constant of this file carries any
 further axiom, and no constant of Instance/Top/Interval.v carries the third
 at all.  These figures are measured per constant, not sampled and not
 inferred from a headline, and they are enumerated in docs/AXIOMS.md under
 "Stdlib axioms".  (An earlier revision said every remaining constant
 carried the first two; [const_arrow_eval] does not, and the direction of
 that error was to over-report the cost.)  No axiom is declared in either
 file, and the core theory is untouched: these two files are the only ones
 in the tree that import the reals.  CORRECTION (#410): not so;
 docs/AXIOMS.md, under "Stdlib axioms", names the development files that
 import the classical reals, and Instance/Top/Circle.v,
 Instance/Top/Solenoid.v and Instance/Top/Solenoid/Presentations.v
 import the standard library's constructive Cauchy reals
 (Reals/Cauchy), which carry no axiom.  CORRECTION (#462): so does
 Instance/Top/Components/Paths.v.

 WHERE THE WORK IS.  Concatenation is not associative and the constant paths
 are not units — not on the nose, and not even up to the hom-setoid of Top.
 Each law holds only up to a homotopy that has to be exhibited.  All four are
 instances of ONE construction, [straight_homotopy]: for an arrow p out of
 the interval and two reparametrizations φ, ψ that agree at 0 and at 1,

 H(t, s) = p((1 - s)·φ(t) + s·ψ(t))

 is a homotopy rel endpoints from p∘φ to p∘ψ.  The four laws then reduce to
 four POINTWISE identities, each proved by case analysis on the parameter:

 p·1_b  agrees with  p ∘ rf_dbl                 (unit_right_pointwise)
 1_a·p  agrees with  p ∘ rf_dbl'                (unit_left_pointwise)
 (p·q)·r agrees with (p·(q·r)) ∘ rf_assoc       (assoc_pointwise)
 p·p‾   agrees with  p ∘ rf_tent                (inverse_pointwise)

 where [rf_assoc] is the piecewise-linear map min(2t, t + 1/4, t/2 + 1/2).
 Well-definedness on classes ([path_concat_respects]) is separate: it pastes
 two homotopies side by side across the square rather than reparametrizing.
 The second inverse law is not proved again — it is the first applied to the
 reversed path, together with the pointwise identity p‾‾ = p.

 ON `=` VERSUS `≈`.  No morphism of any category is ever compared with `=`
 here: composition, the identity and every law are stated with `≈`, and the
 hom-setoid of π(X) is [PathHomotopy].  Two other uses of `=` do occur and
 are both deliberate.  The first is equality of REAL NUMBERS -- `ival x =
 ival y` and the arithmetic of the reparametrizations -- which is Leibniz
 equality on `R` and not a statement about morphisms.  The second is in the
 non-vacuity section, where the carrier setoid of [bool_setoid_object]
 (Instance/Top.v) takes `eq` for its `≈`, so on those two spaces the two
 relations are the same relation; this is the same remark Structure/Groupoid.v
 makes for [Deloop Nat_Plus], and it is scoped to that carrier and to no
 other.  The one further `=` is [bool_carriers_agree], an equality of
 SetoidObjects that holds by [eq_refl] and is strictly stronger than any
 statement `≈` could make.

 OBJECTS ARE POINTS, NOT CLASSES OF POINTS.  The object type is the carrier
 of X, so two `≈`-equal points are distinct objects.  They are canonically
 isomorphic — [equal_points_iso] below builds the isomorphism from the
 constant path — and a groupoid tolerates isomorphic-but-distinct objects,
 so the object type carries redundancy but no distinction that π cannot
 undo.  The alternative would need a quotient the library does not have.

 RIEHL COROLLARY 1.5.14 (base-point independence).  For a path-connected
 space the fundamental groups at any two base points are isomorphic.  It is
 derived HERE THROUGH THE STRUCTURE THEOREM for connected groupoids, not by
 an independent conjugation argument: path-connectedness makes π(X)
 connected, Structure/Groupoid/Connected.v's [connected_deloop_equiv]
 makes the delooping of each vertex group EQUIVALENT to π(X), and
 Structure/Groupoid/Basepoint.v's [deloop_ff_moniso] converts a fully
 faithful functor between one-object categories into a group ISOMORPHISM.
 The two words are used in their exact senses; the structure theorem gives
 an equivalence of categories, and what comes out at the end is a bijection
 of underlying setoids preserving unit and multiplication.

 RIEHL REMARK 1.5.15, AND WHAT IS NOT PROVED.  Riehl's remark at that
 location compares the fundamental group and the fundamental groupoid as
 parallel functors on based path-connected spaces: the inclusion of the
 former into the latter is a natural transformation each of whose components
 is an equivalence of categories, while the inverse equivalences require
 choosing, for each point, a path to the base point, and those choices are
 not preserved by based maps — so the inverses do NOT assemble into a
 natural transformation.  Only the COMPONENT is formalized here, as
 [fundamental_group_inclusion_equivalence]: at a single path-connected
 space, the inclusion of the vertex group at a is an equivalence.  Neither
 functor on based spaces is constructed, the naturality of the inclusion is
 not stated, and the negative statement about the inverses is not proved.
 Recording that asymmetry as a theorem would need a category of based
 spaces and a space where the choices genuinely differ; nothing below
 asserts it, in either direction.

 NON-VACUITY, AND ITS LIMIT.  Degenerate spaces make the whole construction
 trivially true, so a witness is supplied that separates two topologies on
 ONE set.  [Bool_Discrete] and [TwoPoint_Indiscrete] (Instance/Top.v) have the same setoid of points — [bool_setoid_object] — and π tells
 them apart: it is provably NOT connected on the discrete one
 ([Bool_Discrete_pi_not_connected]) and IS connected on the indiscrete one
 ([TwoPoint_Indiscrete_pi_connected]).  The discrete half rests on
 [interval_to_discrete_constant], the least-upper-bound argument showing
 every continuous map from the interval to the two-point discrete space is
 constant — the one genuinely topological fact about [0,1] proved anywhere
 in this development, and the reason π reads the topology rather than the
 underlying set.  CORRECTION (#462): not the only proof of it in the tree.
 Instance/Top/Components/Paths.v proves the same two-point fact for its own
 interval [PInterval], over the constructive Cauchy reals in [PTopCat]
 ([interval_bool_endpoints], [interval_bool_constant]), by bisection and
 closed under the global context; nothing here is rebuilt on it.

 That argument is proved once in the general form
 [interval_to_discrete_constant_dec]: for EVERY discrete space whose
 equality is decidable, every continuous map out of [0,1] is constant.  The
 two-point statement is that theorem at [bool_setoid_object].  What is still
 not proved is connectedness of [0,1] in the general topological sense — no
 separation of the interval by a pair of disjoint nonempty opens — nor
 constancy of maps into a discrete space whose equality is not decidable;
 the decider is what makes the supremum's defining predicate a [Prop], as
 the note above [rclamp] explains.

 The limit is worth stating plainly: NO SPACE WITH A NONTRIVIAL FUNDAMENTAL
 GROUP is exhibited.  Both witnesses have trivial vertex groups AT EVERY
 BASE POINT, both halves quantifying over the point rather than fixing it,
 and both are proved rather than assumed: [Bool_Discrete_loops_trivial] for
 the discrete one, [TwoPoint_Indiscrete_loops_trivial] for the other.  So
 the pair is a contrast in CONNECTEDNESS and in nothing else.  Producing
 one would mean building the circle and computing π₁(S¹) ≅ ℤ, which needs
 covering-space theory or a winding-number argument, and neither is
 attempted.  So the base-point-independence corollary is exercised on a
 witness where both groups happen to be trivial; what the witness
 establishes is that its HYPOTHESIS is a real restriction and that its
 derivation runs, not that the conclusion is ever interesting.

 EXPORTED, WITH NO CURRENT CONSUMER.  Counted from the `.glob` reference
 records rather than by reading, nine constants below are referenced by
 nothing in the tree.  Eight are terminal by design — this file is a leaf of
 the dependency graph, and [bool_carriers_agree],
 [Bool_Discrete_not_pathconnected], [Bool_Discrete_pi_not_connected],
 [Bool_Discrete_loops_trivial], [TwoPoint_Indiscrete_pi_connected],
 [TwoPoint_Indiscrete_basepoint_iso],
 [TwoPoint_Indiscrete_inclusion_equivalence] and
 [TwoPoint_Indiscrete_loops_trivial] are the witnesses, which exist to be the
 end of a chain.  The ninth, [equal_points_iso], is a genuine orphan: it
 discharges the header's remark on the object type by exhibiting the
 canonical isomorphism between `≈`-equal points, and nothing consumes it
 because nothing in this development needs to move along one.  It is kept;
 nothing here is removed on this file's own judgement, and the decision to
 keep or drop is the maintainer's.  (The corresponding count for
 Instance/Top/Interval.v is eight, disclosed in that file's header, and for
 Structure/Groupoid/Basepoint.v seven, disclosed in its.) 

 --------
 nLab：       https://ncatlab.org/nlab/show/fundamental+groupoid
 nLab：       https://ncatlab.org/nlab/show/fundamental+group
 维基百科：   https://en.wikipedia.org/wiki/Fundamental_groupoid
 书籍：       Mac Lane，《为工作数学家而作的范畴论》，第二版，
 GTM 5，第 I.5 节，印刷页 20（PDF 页 30）— 基本群oid 的构造，紧接定义 9 之后
 书籍：       Riehl，《语境中的范畴论》，例 1.1.13(ii)，
 印刷页 8（PDF 页 28）；推论 1.5.14 和备注 1.5.15，
 印刷页 36（PDF 页 56）
 论文：       Brown，《从群到群oid：简要概述》，伦敦数学学会公报 19，1987一个空间的基本群oid π(X)：它的对象是X的点，它的箭头是相对端点路径的同伦类，复合是重新参数化的连接，而一个类的逆是该路径反向的类。下面关于印刷来源所说内容的每一个说法都是对引用位置陈述的意译；上述书籍没有一本被用来编写此文件，并且这里没有引用它们。印刷/PDF页对来自如下树形页映射：doc/plan/books/riehl/pagemap.md，其Riehl偏移是统一的+20，以及 doc/plan/books/maclane/pagemap.md，其在印刷范围7-53的偏移是+10，并且在整本书中明确不是统一的。

 目录：路径 X a b              从 [0,1] 映射出来的一个连续映射，端点为 a 和 b
 箭头同伦 a b p q   两个箭头之间的端点保持同伦
 路径同伦 p q        同样，两条路径之间的同伦
 ah_refl/ah_sym/ah_trans 同伦是一个等价关系
 路径拼接, 路径反转   拼接和反转
 直线同伦       参数的直线同伦，这是所有四条定律背后的单一构造
 左/右单位,
 结合律, 逆律          范畴和群oid的定律，每条都是一个显式同伦
 路径拼接守恒    拼接在同类上是良定义的，通过粘贴而非重参数化
 基本群oid X   π(X) 作为一个范畴
 fundamental_groupoid_is_groupoid          IsGroupoid (π X)
 equal_points_iso         `≈` - 相等的点是同构对象
 fundamental_group X a                     在 a 的顶点群
 fundamental_group_basepoint_independent   Riehl 推论 1.5.14
 pointwise_homotopic     两条路径在每一点上相同则同伦
 interval_to_discrete_constant_dec         从 [0,1] 到具有可判等性的离散空间的每一个连续映射都是常值映射
 interval_to_discrete_constant             在两点离散空间上的该定理
 fundamental_group_inclusion_equivalence   Riehl 注释 1.5.15, at a
 仅一个空格
 no_path_true_false，Bool_Discrete_pi_not_connected，
 TwoPoint_Indiscrete_pi_connected          非空性证人
 Bool_Discrete_loops_trivial，
 TwoPoint_Indiscrete_loops_trivial         两个顶点群都平凡，
 在每个基点处区间及其成本。单位区间、单位正方形、粘贴引理和重参数化都来自 Instance/Top/Interval.v，其文件头完整说明了选择：标准库实数，其代价最多是两个标准库公理，

 ClassicalDedekindReals.sig_forall_dec
 FunctionalExtensionality.functional_extensionality_dep

 这正是 π(X) 本身、[fundamental_groupoid_is_groupoid] 以及基点推论 [fundamental_group_basepoint_independent] 所具备的，再加上第三个，

 ClassicalDedekindReals.sig_not_dec

 用于下面通过最上界性质得到的结果。两个是上限（CEILING），而非固定的费用：Interval.v 的 160 个常量中有 34 个仅具备前两个，本文件的一个常量也是如此。`Print Assumptions` 已经在此文件的每一个常量上运行——总共有 113 个常量，其中包括 `.glob` 文件中记录的 108 个常量，以及五个程序义务 [FundamentalGroupoid_obligation_1] .. [_5]，这些义务由 π(X) 的 [Program Definition] 生成，并且没有 `.glob` 扫描到。 其分类如下：

 1 个常量在全局上下文下闭合（[bool_carriers_agree]）
 1 个只携带 [sig_forall_dec]（[const_arrow_eval]）
 103 个正好携带上述两个（其中 98 个为全局记录的常量，加上所有五个义务）
 8 个也携带第三个八个是最上界论证的两个内部引理，[gval_endpoints] 和 [f_endpoints]；它们建立的一般定理 [interval_to_discrete_constant_dec]，以及它的两点推论 [interval_to_discrete_constant]；以及四个关于使用该定理的离散证明的结果——[no_path_true_false]、[Bool_Discrete_not_pathconnected]、[Bool_Discrete_pi_not_connected] 和 [Bool_Discrete_loops_trivial]。这个文件中的常量不携带任何进一步的公理，而 Instance/Top/Interval.v 中的常量根本不携带第三个公理。这些数字是按常量计算的，而不是抽样的，也不是从标题推断的，它们在 docs/AXIOMS.md 中的“Stdlib axioms”下列出。（早期修订版说每一个剩余常量都包含前两个；[const_arrow_eval] 不包含，并且该错误的方向是高估了成本。）两个文件中都没有声明公理，核心理论保持不变：这两个文件是树中唯一导入实数的文件。更正（#410）：并非如此；docs/AXIOMS.md 在“Stdlib axioms”下列出了导入经典实数的开发文件，而 Instance/Top/Circle.v、Instance/Top/Solenoid.v 和 Instance/Top/Solenoid/Presentations.v 导入标准库的构造性柯西实数（Reals/Cauchy），它们不包含任何公理。更正（#462）：Instance/Top/Components/Paths.v 也是如此。工作的所在。串联不是结合的，并且恒定路径不是单位——既不是严格意义上的单位，甚至在 Top 的同余集合上也不是。每条定律仅在必须展示的同伦下成立。所有四条都是一个构造 [straight_homotopy] 的实例：对于从区间出发的箭头 p 和在 0 与 1 处一致的两个重新参数化 φ、ψ，

 H(t, s) = p((1 - s)·φ(t) + s·ψ(t))

 是从 p∘φ 到 p∘ψ 的端点保持同伦。随后，这四条定律化简为四个逐点的恒等式，每个通过对参数的情况分析证明。p·1_b 与 p ∘ rf_dbl 一致（单位右侧逐点）
 1_a·p 与 p ∘ rf_dbl' 一致（单位左侧逐点）
 (p·q)·r 与 (p·(q·r)) ∘ rf_assoc 一致（结合律逐点）
 p·p‾ 与 p ∘ rf_tent 一致（逆元逐点）

 其中 [rf_assoc] 是分段线性映射 min(2t, t + 1/4, t/2 + 1/2)。
 在类 ([path_concat_respects]) 上的良定性是分开的：它在正方形上将两个同伦并排粘贴，而不是重新参数化。
 第二个逆律没有再次证明——它是应用于反向路径的第一个逆律，并结合逐点恒等式 p‾‾ = p。在 `=` 与 `≈` 之间。没有任何范畴的态射在此处与 `=` 进行比较：组成、恒等和每条定律都用 `≈` 表述，并且 π(X) 的同态集等价类为 [PathHomotopy]。`=` 还有其他两处使用，且都是有意的。第一处是实数的相等——`ival x = ival y` 以及重新参数化的算术——这是 `R` 上的莱布尼茨相等，而不是关于态射的陈述。第二处是在非空性部分，[bool_setoid_object] (Instance/Top.v) 的承载集合等价类采用 `eq` 作为其 `≈`，因此在这两个空间上，这两种关系是相同的关系；这是 Structure/Groupoid.v 对 [Deloop Nat_Plus] 所作的相同说明，并且它仅适用于该承载集合，而不适用于其他集合。更远的 `=` 是 [bool_carriers_agree]，这是一个 SetoidObjects 的相等，由 [eq_refl] 保证，并且严格强于任何 `≈` 可以提出的陈述。

 对象是点，而不是点的类。对象类型是 X 的承载类型，所以两个 `≈` 相等的点是不同的对象。它们在范式上同构——下面的 [equal_points_iso] 从常量路径构建同构——而群族容忍同构但不同的对象，因此对象类型携带冗余但没有 π 无法消除的区别。另一种选择需要一个库中不存在的商。RIEHL 推论 1.5.14（基点无关性）。对于路径连通空间，任何两个基点的基本群都是同构的。这里通过连通群族的结构定理推导出来的，而不是通过独立的共轭论证：路径连通性使得 π(X) 连通，Structure/Groupoid/Connected.v 的 [connected_deloop_equiv] 使每个顶点群的解环等价于 π(X)，而 Structure/Groupoid/Basepoint.v 的 [deloop_ff_moniso] 将单对象范畴之间的全忠实函子转换为群同构。这两个词按其确切含义使用；结构定理给出了范畴的等价关系，最终得出的结果是保持单位和乘法的底层集合对应关系。RIEHL 评论 1.5.15，以及未被证明的内容。在该位置，Riehl 的评论将基本群和基本群oid 比作基于路径连通空间的平行函子：前者包含到后者是一个自然变换，其每个组件都是范畴的等价，而逆等价则需要为每个点选择一条到基点的路径，而这些选择不会被基于映射所保留——因此逆变换**不**能组合成自然变换。这里只形式化了组件，即 [fundamental_group_inclusion_equivalence]：在单一路径连通空间上，顶点群 a 的包含是一个等价。没有对基点空间上的函子进行构造，没有说明包含的自然性，也没有证明关于逆元的否定陈述。将这种不对称记录为一个定理将需要一个基点空间的范畴和一个选择真正不同的空间；下文没有断言这一点，无论哪个方向都是如此。非空性及其界限。退化空间使整个构造显然成立，因此提供了一个证据来区分同一集合上的两种拓扑。[Bool_Discrete] 和 [TwoPoint_Indiscrete]（Instance/Top.v）具有相同的点集构造——[bool_setoid_object]——而 π 将它们区分开：在离散拓扑（[Bool_Discrete_pi_not_connected]）上可证明它不是连通的，而在最粗拓扑（[TwoPoint_Indiscrete_pi_connected]）上则是连通的。离散的一半依赖于 [interval_to_discrete_constant]，最上界论证显示从区间到两点离散空间的每一个连续映射都是常值的——这是在本开发中关于 [0,1] 唯一被证明的真正拓扑性质，也是 π 能读取拓扑而非底层集合的原因。更正（#462）：这并不是该树中唯一的证明。Instance/Top/Components/Paths.v 对其自身区间 [PInterval] 在构造性柯西实数 [PTopCat] ([interval_bool_endpoints], [interval_bool_constant]) 上证明了相同的两点事实，通过二分法并在全局上下文下封闭；这里没有对它进行重建。这个论证在一般形式下已被证明
 [interval_to_discrete_constant_dec]：对于每一个等式可判别的离散空间，从[0,1]出发的每一个连续映射都是常值。 
 两点陈述是在[bool_setoid_object]处的定理。 
 仍未被证明的是[0,1]在一般拓扑意义下的连通性——无法通过一对互不相交的非空开集将区间分开——以及映射到等式不可判别的离散空间的映射是否为常值； 
 判定器是使上确界的定义谓词成为[Prop]的原因，正如在[rclamp]上方的注释所解释的。限制值得明确说明：没有展示出具有非平凡基本群的空间。两个证据在每个基点的顶点群都是平凡的，两个部分都是对基点进行量化而不是固定基点，并且两者都是被证明而不是假设的：离散情况为 [Bool_Discrete_loops_trivial]，另一种情况为 [TwoPoint_Indiscrete_loops_trivial]。因此，这对是在连通性上的对比，而不涉及其他方面。要生成一个例子意味着要构建圆并计算 π₁(S¹) ≅ ℤ，这需要覆盖空间理论或绕数论证，而这些都没有尝试。因此，基点无关的推论是在一个两个群都恰好为平凡的见证上使用的；该见证所证明的是它的假设是一个真实的限制，并且其推导是可行的，而不是结论本身有趣。已导出，但当前没有使用者。从 `.glob` 参考记录进行计数，而非通过读取，下面九个常量未被树中的任何内容引用。其中八个按设计是终端——此文件是依赖图的叶子节点，[bool_carriers_agree]、[Bool_Discrete_not_pathconnected]、[Bool_Discrete_pi_not_connected]、[Bool_Discrete_loops_trivial]、[TwoPoint_Indiscrete_pi_connected]、[TwoPoint_Indiscrete_basepoint_iso]、[TwoPoint_Indiscrete_inclusion_equivalence] 和 [TwoPoint_Indiscrete_loops_trivial] 是证明存在的终结点，用于作为链的结尾。第九个 [equal_points_iso] 是真正的孤立对象：它通过展示 `≈` 相等点之间的典型同构，来解除头部对对象类型的注解，但没有任何内容使用它，因为在此开发中没有任何内容需要沿此对象移动。它被保留；在此文件自身的判断下没有被移除，保留或丢弃的决定由维护者作出。（Instance/Top/Interval.v 的相应计数为八，已在该文件的头部披露；Structure/Groupoid/Basepoint.v 的相应计数为七，已在其头部披露。）
*)

(** ** Paths *)

(* A path from a to b: a continuous map out of the interval with the two endpoint conditions, stated up to `≈` in the space's own equality. / 从 a 到 b 的路径：从区间的连续映射，满足两个端点条件，在空间自身的等式中，直到 `≈`。 *)
Record Path (X : TopSpace) (a b : X) := {
  path_map :> I_Top ~{Top}~> X;

  path_src : path_map I_zero ≈ a;
  path_tgt : path_map I_one ≈ b
}.

Arguments path_map {X a b} _.
Arguments path_src {X a b} _.
Arguments path_tgt {X a b} _.

(** ** Homotopy rel endpoints / ** 端点相对的同伦 *)

(*
 A homotopy rel endpoints between two arrows out of the interval: a map of
 the square whose bottom edge is p, whose top edge is q, and whose two
 vertical edges are constant at a and at b.  It is stated for bare arrows
 rather than for [Path] records because the reparametrization lemmas below
 produce arrows first and only then package endpoints. 

 --------
 从区间出发的两个箭头之间的端点保持同伦：一个方形映射，其下边是 p，上边是 q，两个纵向边分别在 a 和 b 处为常数。它是针对裸箭头而非 [Path] 记录来说明的，因为下面的重参数化引理首先生成箭头，然后才封装端点。
*)
Record ArrowHomotopy {X : TopSpace} (a b : X) (p q : I_Top ~{Top}~> X) := {
  ah_map :> Sq_Top ~{Top}~> X;

  ah_bot : ∀ t : Ipt, ah_map (sq_pt t I_zero) ≈ p t;
  ah_top : ∀ t : Ipt, ah_map (sq_pt t I_one) ≈ q t;
  ah_left : ∀ s : Ipt, ah_map (sq_pt I_zero s) ≈ a;
  ah_right : ∀ s : Ipt, ah_map (sq_pt I_one s) ≈ b
}.

Arguments ah_map {X a b p q} _.
Arguments ah_bot {X a b p q} _ _.
Arguments ah_top {X a b p q} _ _.
Arguments ah_left {X a b p q} _ _.
Arguments ah_right {X a b p q} _ _.

(* Homotopy of PATHS is homotopy of their underlying arrows. / 路径的同伦是其底层箭头的同伦。 *)
Definition PathHomotopy {X : TopSpace} {a b : X} (p q : Path X a b) : Type :=
  ArrowHomotopy a b (path_map p) (path_map q).

(** ** Evaluating composites / ** 评估复合材料 *)

(*
 Two rewriting lemmas used throughout: a composite arrow evaluates by
 evaluating the inner one first, and the outer arrow only sees coordinates. 

 --------
 贯穿始终使用的两个重写引理：组合箭头通过先评估内部箭头来求值，外部箭头只看到坐标。
*)
Lemma comp_eval_I {X : TopSpace} (f : I_Top ~{Top}~> X)
      (g : I_Top ~{Top}~> I_Top) (x y : Ipt) :
  ival (g x) = ival y → (f ∘[Top] g) x ≈ f y.
Proof. intro H; exact (Iap f (g x) y H). Qed.

Lemma comp_eval_Sq {X : TopSpace} (f : I_Top ~{Top}~> X)
      (g : Sq_Top ~{Top}~> I_Top) (z : BS_Sq) (y : Ipt) :
  ival (g z) = ival y → (f ∘[Top] g) z ≈ f y.
Proof. intro H; exact (Iap f (g z) y H). Qed.

Lemma comp_eval_SqSq {X : TopSpace} (F : Sq_Top ~{Top}~> X)
      (G : Sq_Top ~{Top}~> Sq_Top) (z w : BS_Sq) :
  sq_t (G z) = sq_t w → sq_s (G z) = sq_s w → (F ∘[Top] G) z ≈ F w.
Proof. intros H1 H2; exact (Sqap F (G z) w H1 H2). Qed.

(* * ** Homotopy is an equivalence relation / * ** 同伦是一种等价关系 *)

(* Reflexivity: the homotopy constant in the second coordinate. / 自反性：第二坐标中的同伦常数。 *)
Definition ah_refl {X : TopSpace} (a b : X) (p : I_Top ~{Top}~> X)
           (Ha : p I_zero ≈ a) (Hb : p I_one ≈ b) : ArrowHomotopy a b p p.
Proof.
  refine {| ah_map := p ∘[Top] Sq_first |}.
  - intro t; apply comp_eval_Sq; reflexivity.
  - intro t; apply comp_eval_Sq; reflexivity.
  - intro s.
    transitivity (p I_zero); [ | exact Ha ].
    apply comp_eval_Sq; reflexivity.
  - intro s.
    transitivity (p I_one); [ | exact Hb ].
    apply comp_eval_Sq; reflexivity.
Defined.

(* Symmetry: turn the square upside down. / 对称：把正方形倒过来。 *)
Definition ah_sym {X : TopSpace} {a b : X} {p q : I_Top ~{Top}~> X}
           (H : ArrowHomotopy a b p q) : ArrowHomotopy a b q p.
Proof.
  refine {| ah_map := ah_map H ∘[Top] Sq_flip |}.
  - intro t.
    transitivity (ah_map H (sq_pt t I_one)); [ | exact (ah_top H t) ].
    apply comp_eval_SqSq.
    + rewrite Sq_flip_t; reflexivity.
    + rewrite Sq_flip_s, !sq_pt_s, ival_I_zero, ival_I_one; lra.
  - intro t.
    transitivity (ah_map H (sq_pt t I_zero)); [ | exact (ah_bot H t) ].
    apply comp_eval_SqSq.
    + rewrite Sq_flip_t; reflexivity.
    + rewrite Sq_flip_s, !sq_pt_s, ival_I_zero, ival_I_one; lra.
  - intro s.
    transitivity (ah_map H (sq_pt I_zero (I_rev s))); [ | exact (ah_left H _) ].
    apply comp_eval_SqSq.
    + rewrite Sq_flip_t; reflexivity.
    + rewrite Sq_flip_s, !sq_pt_s, I_rev_eval; reflexivity.
  - intro s.
    transitivity (ah_map H (sq_pt I_one (I_rev s))); [ | exact (ah_right H _) ].
    apply comp_eval_SqSq.
    + rewrite Sq_flip_t; reflexivity.
    + rewrite Sq_flip_s, !sq_pt_s, I_rev_eval; reflexivity.
Defined.

(* Transitivity: stack the two squares, each run at double speed vertically. This is [paste_arrow] applied along the second coordinate of the square. / 及物性：将两个正方形堆叠，每个在垂直方向以双倍速度运行。 这是 [paste_arrow] 应用于正方形的第二坐标。 *)
Section HomotopyTrans.

Context {X : TopSpace}.
Context {a b : X}.
Context {p q r : I_Top ~{Top}~> X}.
Context (H1 : ArrowHomotopy a b p q).
Context (H2 : ArrowHomotopy a b q r).

Lemma ah_trans_agree (z : BS_Sq) : sq_s z = 1/2 →
  (ah_map H1 ∘[Top] Sq_lower) z ≈ (ah_map H2 ∘[Top] Sq_upper) z.
Proof.
  intro Hz.
  transitivity (q (bs_fst z)).
  - transitivity (ah_map H1 (sq_pt (bs_fst z) I_one)).
    + apply comp_eval_SqSq.
      * rewrite Sq_lower_t, sq_pt_t; reflexivity.
      * rewrite Sq_lower_s, sq_pt_s, ival_I_one, Hz; Rlin.
    + exact (ah_top H1 (bs_fst z)).
  - symmetry.
    transitivity (ah_map H2 (sq_pt (bs_fst z) I_zero)).
    + apply comp_eval_SqSq.
      * rewrite Sq_upper_t, sq_pt_t; reflexivity.
      * rewrite Sq_upper_s, sq_pt_s, ival_I_zero, Hz; Rlin.
    + exact (ah_bot H2 (bs_fst z)).
Qed.

Definition ah_trans_map : Sq_Top ~{Top}~> X :=
  paste_arrow (A:=BS_Sq) sq_s Sq_s_lip (1/2)
    (ah_map H1 ∘[Top] Sq_lower) (ah_map H2 ∘[Top] Sq_upper) ah_trans_agree.

Lemma ah_trans_lower (z : BS_Sq) :
  sq_s z <= 1/2 → ah_trans_map z ≈ (ah_map H1 ∘[Top] Sq_lower) z.
Proof.
  exact (paste_left (A:=BS_Sq) sq_s Sq_s_lip (1/2) _ _ ah_trans_agree z).
Qed.

Lemma ah_trans_upper (z : BS_Sq) :
  1/2 <= sq_s z → ah_trans_map z ≈ (ah_map H2 ∘[Top] Sq_upper) z.
Proof.
  exact (paste_right (A:=BS_Sq) sq_s Sq_s_lip (1/2) _ _ ah_trans_agree z).
Qed.

Definition ah_trans : ArrowHomotopy a b p r.
Proof.
  refine {| ah_map := ah_trans_map |}.
  - intro t.
    transitivity ((ah_map H1 ∘[Top] Sq_lower) (sq_pt t I_zero)).
    + apply ah_trans_lower; rewrite sq_pt_s, ival_I_zero; lra.
    + transitivity (ah_map H1 (sq_pt t I_zero)); [ | exact (ah_bot H1 t) ].
      apply comp_eval_SqSq.
      * rewrite Sq_lower_t; reflexivity.
      * rewrite Sq_lower_s, !sq_pt_s, ival_I_zero; Rlin.
  - intro t.
    transitivity ((ah_map H2 ∘[Top] Sq_upper) (sq_pt t I_one)).
    + apply ah_trans_upper; rewrite sq_pt_s, ival_I_one; lra.
    + transitivity (ah_map H2 (sq_pt t I_one)); [ | exact (ah_top H2 t) ].
      apply comp_eval_SqSq.
      * rewrite Sq_upper_t; reflexivity.
      * rewrite Sq_upper_s, !sq_pt_s, ival_I_one; Rlin.
  - intro s.
    destruct (Rle_dec (ival s) (1/2)) as [Hle | Hnle].
    + transitivity ((ah_map H1 ∘[Top] Sq_lower) (sq_pt I_zero s)).
      * apply ah_trans_lower; rewrite sq_pt_s; exact Hle.
      * transitivity (ah_map H1 (sq_pt I_zero (I_dbl s)));
          [ | exact (ah_left H1 (I_dbl s)) ].
        apply comp_eval_SqSq.
        { rewrite Sq_lower_t; reflexivity. }
        { rewrite Sq_lower_s, !sq_pt_s, I_dbl_eval; reflexivity. }
    + apply Rnot_le_lt in Hnle.
      transitivity ((ah_map H2 ∘[Top] Sq_upper) (sq_pt I_zero s)).
      * apply ah_trans_upper; rewrite sq_pt_s; lra.
      * transitivity (ah_map H2 (sq_pt I_zero (I_dbl' s)));
          [ | exact (ah_left H2 (I_dbl' s)) ].
        apply comp_eval_SqSq.
        { rewrite Sq_upper_t; reflexivity. }
        { rewrite Sq_upper_s, !sq_pt_s, I_dbl'_eval; reflexivity. }
  - intro s.
    destruct (Rle_dec (ival s) (1/2)) as [Hle | Hnle].
    + transitivity ((ah_map H1 ∘[Top] Sq_lower) (sq_pt I_one s)).
      * apply ah_trans_lower; rewrite sq_pt_s; exact Hle.
      * transitivity (ah_map H1 (sq_pt I_one (I_dbl s)));
          [ | exact (ah_right H1 (I_dbl s)) ].
        apply comp_eval_SqSq.
        { rewrite Sq_lower_t; reflexivity. }
        { rewrite Sq_lower_s, !sq_pt_s, I_dbl_eval; reflexivity. }
    + apply Rnot_le_lt in Hnle.
      transitivity ((ah_map H2 ∘[Top] Sq_upper) (sq_pt I_one s)).
      * apply ah_trans_upper; rewrite sq_pt_s; lra.
      * transitivity (ah_map H2 (sq_pt I_one (I_dbl' s)));
          [ | exact (ah_right H2 (I_dbl' s)) ].
        apply comp_eval_SqSq.
        { rewrite Sq_upper_t; reflexivity. }
        { rewrite Sq_upper_s, !sq_pt_s, I_dbl'_eval; reflexivity. }
Defined.

End HomotopyTrans.

(*
 Homotopy also transports along pointwise `≈`-equality of the arrows
 themselves, which is what lets a computation that changes a path only up
 to the hom-setoid of Top be applied inside a homotopy class. 

 --------
 同伦也沿着箭头自身的逐点 `≈` 相等进行传输，这使得仅在 Top 的同集等价类下改变路径的计算能够应用于同伦类中。
*)
Definition ah_pointwise {X : TopSpace} {a b : X} {p q p' q' : I_Top ~{Top}~> X}
           (Hp : p ≈ p') (Hq : q ≈ q') (H : ArrowHomotopy a b p q) :
  ArrowHomotopy a b p' q'.
Proof.
  refine {| ah_map := ah_map H |}.
  - intro t; rewrite (ah_bot H t); exact (Hp t).
  - intro t; rewrite (ah_top H t); exact (Hq t).
  - exact (ah_left H).
  - exact (ah_right H).
Defined.

(* * ** Constant paths, reversal, and concatenation / * ** 常量路径、反转和连接 *)

Definition const_arrow {X : TopSpace} (a : X) : I_Top ~{Top}~> X :=
  Build_ContinuousMorphism I_Top X
    (const_morphism (top_carrier I_Top) (top_carrier X) a)
    (fun U _ => open_const I_Top (U a)).

Lemma const_arrow_eval {X : TopSpace} (a : X) (x : Ipt) : const_arrow a x ≈ a.
Proof. reflexivity. Qed.

Definition const_path {X : TopSpace} (a : X) : Path X a a := {|
  path_map := const_arrow a;
  path_src := reflexivity a;
  path_tgt := reflexivity a
|}.

Lemma path_rev_src {X : TopSpace} {a b : X} (p : Path X a b) :
  (path_map p ∘[Top] I_rev) I_zero ≈ b.
Proof.
  transitivity (path_map p I_one); [ | exact (path_tgt p) ].
  apply comp_eval_I; rewrite I_rev_eval, ival_I_zero, ival_I_one; lra.
Qed.

Lemma path_rev_tgt {X : TopSpace} {a b : X} (p : Path X a b) :
  (path_map p ∘[Top] I_rev) I_one ≈ a.
Proof.
  transitivity (path_map p I_zero); [ | exact (path_src p) ].
  apply comp_eval_I; rewrite I_rev_eval, ival_I_zero, ival_I_one; lra.
Qed.

Definition path_rev {X : TopSpace} {a b : X} (p : Path X a b) : Path X b a := {|
  path_map := path_map p ∘[Top] I_rev;
  path_src := path_rev_src p;
  path_tgt := path_rev_tgt p
|}.

Section Concat.

Context {X : TopSpace}.
Context (b : X).
Context (p q : I_Top ~{Top}~> X).
Context (Hp : p I_one ≈ b).
Context (Hq : q I_zero ≈ b).

Lemma concat_agree (x : BS_I) : ival x = 1/2 →
  (p ∘[Top] I_dbl) x ≈ (q ∘[Top] I_dbl') x.
Proof.
  intro Hx.
  transitivity b.
  - transitivity (p I_one); [ | exact Hp ].
    apply comp_eval_I.
    rewrite I_dbl_eval, ival_I_one, Hx; Rlin.
  - symmetry.
    transitivity (q I_zero); [ | exact Hq ].
    apply comp_eval_I.
    rewrite I_dbl'_eval, ival_I_zero, Hx; Rlin.
Qed.

(* The reparametrized concatenation: p run at double speed on the first half of the interval, q on the second. / 重新参数化的连接：p 在区间的前半部分以双倍速度运行，q 在后半部分运行。 *)
Definition concat_arrow : I_Top ~{Top}~> X :=
  paste_arrow (A:=BS_I) ival I_coord_lip (1/2)
    (p ∘[Top] I_dbl) (q ∘[Top] I_dbl') concat_agree.

Lemma concat_first (x y : Ipt) :
  ival x <= 1/2 → ival y = 2 * ival x → concat_arrow x ≈ p y.
Proof.
  intros H1 H2.
  transitivity ((p ∘[Top] I_dbl) x).
  - exact (paste_left (A:=BS_I) ival I_coord_lip (1/2) _ _ concat_agree x H1).
  - apply comp_eval_I.
    rewrite I_dbl_eval, H2; Rlin.
Qed.

Lemma concat_second (x y : Ipt) :
  1/2 <= ival x → ival y = 2 * ival x - 1 → concat_arrow x ≈ q y.
Proof.
  intros H1 H2.
  transitivity ((q ∘[Top] I_dbl') x).
  - exact (paste_right (A:=BS_I) ival I_coord_lip (1/2) _ _ concat_agree x H1).
  - apply comp_eval_I.
    rewrite I_dbl'_eval, H2; Rlin.
Qed.

Lemma concat_src (a : X) (Ha : p I_zero ≈ a) : concat_arrow I_zero ≈ a.
Proof.
  transitivity (p I_zero); [ | exact Ha ].
  apply (concat_first I_zero I_zero); rewrite ival_I_zero; lra.
Qed.

Lemma concat_tgt (c : X) (Hc : q I_one ≈ c) : concat_arrow I_one ≈ c.
Proof.
  transitivity (q I_one); [ | exact Hc ].
  apply (concat_second I_one I_one); rewrite ival_I_one; lra.
Qed.

End Concat.

Definition path_concat {X : TopSpace} {a b c : X}
           (p : Path X a b) (q : Path X b c) : Path X a c := {|
  path_map := concat_arrow b (path_map p) (path_map q) (path_tgt p) (path_src q);
  path_src := concat_src b (path_map p) (path_map q) (path_tgt p) (path_src q)
                a (path_src p);
  path_tgt := concat_tgt b (path_map p) (path_map q) (path_tgt p) (path_src q)
                c (path_tgt q)
|}.

(* * ** The straight-line homotopy of parameters / * ** 参数的直线同宿 *)

(*
 The single homotopy construction the category laws need: given an arrow p
 out of the interval and two reparametrizations φ, ψ agreeing at 0 and at 1,
 the maps p∘φ and p∘ψ are homotopic rel endpoints, along
 H(t, s) = p((1 - s)·φ(t) + s·ψ(t)).
 The two arrows u and v are not required to BE the composites: they need only
 agree with them pointwise, which is how the concatenations below -- defined
 by pasting rather than by composition -- are fed to it. 

 --------
 单一同伦构造是类别律所需要的：给定一个从区间射出的箭头 p 和两个在 0 和 1 处一致的重新参数化 φ、ψ，映射 p∘φ 和 p∘ψ 在端点相对同伦，其同伦为 H(t, s) = p((1 - s)·φ(t) + s·ψ(t))。两个箭头 u 和 v 不需要是复合箭头：它们只需在点上与复合箭头一致，这就是下面的连接 —— 通过粘贴而不是复合定义 —— 如何被用到它的方式。
*)

Section Straight.

Context {X : TopSpace}.
Context (a b : X).
Context (p : I_Top ~{Top}~> X).
Context (phi psi : R → R).
Context (Hphi0 : ∀ t, 0 <= t → t <= 1 → 0 <= phi t).
Context (Hphi1 : ∀ t, 0 <= t → t <= 1 → phi t <= 1).
Context (Hpsi0 : ∀ t, 0 <= t → t <= 1 → 0 <= psi t).
Context (Hpsi1 : ∀ t, 0 <= t → t <= 1 → psi t <= 1).
Context (Hphil : RLip 2 phi).
Context (Hpsil : RLip 2 psi).
Context (He0 : phi 0 = psi 0).
Context (He1 : phi 1 = psi 1).
Context (Hva : ∀ y : Ipt, ival y = phi 0 → p y ≈ a).
Context (Hvb : ∀ y : Ipt, ival y = phi 1 → p y ≈ b).
Context (u v : I_Top ~{Top}~> X).
Context (Hu : ∀ x y : Ipt, ival y = phi (ival x) → u x ≈ p y).
Context (Hv : ∀ x y : Ipt, ival y = psi (ival x) → v x ≈ p y).

Definition straight_map : Sq_Top ~{Top}~> I_Top :=
  Sq_hmap phi psi 2 two_pos Hphi0 Hphi1 Hpsi0 Hpsi1 Hphil Hpsil.

Definition straight_homotopy : ArrowHomotopy a b u v.
Proof.
  refine {| ah_map := p ∘[Top] straight_map |}.
  - intro t.
    assert (Heq : ival (straight_map (sq_pt t I_zero)) = phi (ival t)).
    { unfold straight_map.
      rewrite Sq_hmap_eval, !sq_pt_t, !sq_pt_s, ival_I_zero; ring. }
    symmetry.
    exact (Hu t (straight_map (sq_pt t I_zero)) Heq).
  - intro t.
    assert (Heq : ival (straight_map (sq_pt t I_one)) = psi (ival t)).
    { unfold straight_map.
      rewrite Sq_hmap_eval, !sq_pt_t, !sq_pt_s, ival_I_one; ring. }
    symmetry.
    exact (Hv t (straight_map (sq_pt t I_one)) Heq).
  - intro s.
    assert (Heq : ival (straight_map (sq_pt I_zero s)) = phi 0).
    { unfold straight_map.
      rewrite Sq_hmap_eval, !sq_pt_t, !sq_pt_s, ival_I_zero, <- He0; ring. }
    exact (Hva (straight_map (sq_pt I_zero s)) Heq).
  - intro s.
    assert (Heq : ival (straight_map (sq_pt I_one s)) = phi 1).
    { unfold straight_map.
      rewrite Sq_hmap_eval, !sq_pt_t, !sq_pt_s, ival_I_one, <- He1; ring. }
    exact (Hvb (straight_map (sq_pt I_one s)) Heq).
Defined.

End Straight.

(* * ** Evaluating a concatenation of paths / * ** 评估路径的连接 *)

Lemma path_at_zero {X : TopSpace} {a b : X} (p : Path X a b) (y : Ipt) :
  ival y = 0 → path_map p y ≈ a.
Proof.
  intro H.
  transitivity (path_map p I_zero); [ | exact (path_src p) ].
  apply Iap; rewrite H, ival_I_zero; reflexivity.
Qed.

Lemma path_at_one {X : TopSpace} {a b : X} (p : Path X a b) (y : Ipt) :
  ival y = 1 → path_map p y ≈ b.
Proof.
  intro H.
  transitivity (path_map p I_one); [ | exact (path_tgt p) ].
  apply Iap; rewrite H, ival_I_one; reflexivity.
Qed.

Lemma path_concat_first {X : TopSpace} {a b c : X}
      (p : Path X a b) (q : Path X b c) (x y : Ipt) :
  ival x <= 1/2 → ival y = 2 * ival x →
  path_map (path_concat p q) x ≈ path_map p y.
Proof. apply concat_first. Qed.

Lemma path_concat_second {X : TopSpace} {a b c : X}
      (p : Path X a b) (q : Path X b c) (x y : Ipt) :
  1/2 <= ival x → ival y = 2 * ival x - 1 →
  path_map (path_concat p q) x ≈ path_map q y.
Proof. apply concat_second. Qed.

(* * ** The three category laws, pointwise / * ** 三类定律，逐点 *)

(*
 Right unit: p followed by the constant path at b agrees pointwise with p
 reparametrized by [rf_dbl]. 

 --------
 正确的单位：p 后跟在 b 的恒定路径与 p 在每一点上通过 [rf_dbl] 重参数化后相符合。
*)
Lemma unit_right_pointwise {X : TopSpace} {a b : X} (p : Path X a b) (x y : Ipt) :
  ival y = rf_dbl (ival x) →
  path_map (path_concat p (const_path b)) x ≈ path_map p y.
Proof.
  intro Hy.
  pose proof (ipt_lo x); pose proof (ipt_hi x).
  destruct (Rle_dec (ival x) (1/2)) as [Hle | Hnle].
  - apply path_concat_first; [ exact Hle | ].
    rewrite Hy; unfold rf_dbl; Rlin.
  - apply Rnot_le_lt in Hnle.
    transitivity (path_map (const_path b)
                    (mkI (2 * ival x - 1) ltac:(lra) ltac:(lra))).
    + apply path_concat_second; simpl; lra.
    + transitivity b.
      * exact (const_arrow_eval b _).
      * symmetry; apply (path_at_one p).
        rewrite Hy; unfold rf_dbl; Rlin.
Qed.

(*
 Left unit: the constant path at a followed by p agrees pointwise with p
 reparametrized by [rf_dbl']. 

 --------
 左单元：在 a 处的常数路径后跟 p 与通过 [rf_dbl'] 重新参数化的 p 在点上相符。
*)
Lemma unit_left_pointwise {X : TopSpace} {a b : X} (p : Path X a b) (x y : Ipt) :
  ival y = rf_dbl' (ival x) →
  path_map (path_concat (const_path a) p) x ≈ path_map p y.
Proof.
  intro Hy.
  pose proof (ipt_lo x); pose proof (ipt_hi x).
  destruct (Rle_dec (ival x) (1/2)) as [Hle | Hnle].
  - transitivity (path_map (const_path a)
                    (mkI (2 * ival x) ltac:(lra) ltac:(lra))).
    + apply path_concat_first; simpl; lra.
    + transitivity a.
      * exact (const_arrow_eval a _).
      * symmetry; apply (path_at_zero p).
        rewrite Hy; unfold rf_dbl'; Rlin.
  - apply Rnot_le_lt in Hnle.
    apply path_concat_second; [ lra | ].
    rewrite Hy; unfold rf_dbl'; Rlin.
Qed.

(*
 Associativity: the two bracketings agree pointwise after the piecewise
 linear reparametrization [rf_assoc].  This is the computation Mac Lane's
 construction turns on, and it is the reason concatenation is associative
 only up to homotopy. 

 --------
 结合性：在分段线性重参量 [rf_assoc] 之后，这两种括号安排在每一点上都是一致的。这是 Mac Lane 构造所依赖的计算，也是拼接仅在同伦意义下具有结合性的原因。
*)
Lemma assoc_pointwise {X : TopSpace} {a b c d : X}
      (p : Path X a b) (q : Path X b c) (r : Path X c d) (x y : Ipt) :
  ival y = rf_assoc (ival x) →
  path_map (path_concat (path_concat p q) r) x
    ≈ path_map (path_concat p (path_concat q r)) y.
Proof.
  intro Hy.
  pose proof (ipt_lo x); pose proof (ipt_hi x).
  destruct (Rle_dec (ival x) (1/4)) as [Hc1 | Hn1].
  - (* first quarter: both sides run p at quadruple speed / 第一节：双方以四倍速度跑 p *)
    rewrite rf_assoc_first in Hy by lra.
    transitivity (path_map p (mkI (4 * ival x) ltac:(lra) ltac:(lra))).
    + transitivity (path_map (path_concat p q)
                      (mkI (2 * ival x) ltac:(lra) ltac:(lra))).
      * apply path_concat_first; simpl; lra.
      * apply path_concat_first; simpl; lra.
    + symmetry; apply path_concat_first; simpl; lra.
  - apply Rnot_le_lt in Hn1.
    destruct (Rle_dec (ival x) (1/2)) as [Hc2 | Hn2].
    + (* second quarter: both sides run q / 第二节：双方打跑动进攻 *)
      rewrite rf_assoc_middle in Hy by lra.
      transitivity (path_map q (mkI (4 * ival x - 1) ltac:(lra) ltac:(lra))).
      * transitivity (path_map (path_concat p q)
                        (mkI (2 * ival x) ltac:(lra) ltac:(lra))).
        { apply path_concat_first; simpl; lra. }
        { apply path_concat_second; simpl; lra. }
      * symmetry.
        transitivity (path_map (path_concat q r)
                        (mkI (2 * ival x - 1/2) ltac:(lra) ltac:(lra))).
        { apply path_concat_second; simpl; lra. }
        { apply path_concat_first; simpl; lra. }
    + (* second half: both sides run r / 下半场：双方都跑r *)
      apply Rnot_le_lt in Hn2.
      rewrite rf_assoc_last in Hy by lra.
      transitivity (path_map r (mkI (2 * ival x - 1) ltac:(lra) ltac:(lra))).
      * apply path_concat_second; simpl; lra.
      * symmetry.
        transitivity (path_map (path_concat q r)
                        (mkI (ival x) ltac:(lra) ltac:(lra))).
        { apply path_concat_second; simpl; lra. }
        { apply path_concat_second; simpl; lra. }
Qed.

(* Inversion: a path followed by its reverse agrees pointwise with the path reparametrized by the tent map, which goes out and comes back. / 反转：一条路径与其反向路径逐点一致，该路径通过帐篷映射重新参数化，表现为出去又返回。 *)
Lemma inverse_pointwise {X : TopSpace} {a b : X} (p : Path X a b) (x y : Ipt) :
  ival y = rf_tent (ival x) →
  path_map (path_concat p (path_rev p)) x ≈ path_map p y.
Proof.
  intro Hy.
  pose proof (ipt_lo x); pose proof (ipt_hi x).
  destruct (Rle_dec (ival x) (1/2)) as [Hle | Hnle].
  - apply path_concat_first; [ exact Hle | ].
    rewrite Hy; unfold rf_tent; Rlin.
  - apply Rnot_le_lt in Hnle.
    transitivity (path_map (path_rev p)
                    (mkI (2 * ival x - 1) ltac:(lra) ltac:(lra))).
    + apply path_concat_second; simpl; lra.
    + apply comp_eval_I.
      rewrite I_rev_eval, Hy; simpl; unfold rf_tent; Rlin.
Qed.

(** ** The four laws as homotopies / ** 四条定律作为同宿映射 *)

Lemma unit_right_homotopy {X : TopSpace} {a b : X} (p : Path X a b) :
  PathHomotopy (path_concat p (const_path b)) p.
Proof.
  unfold PathHomotopy.
  refine (@straight_homotopy X a b (path_map p) rf_dbl rf_id
            rf_dbl_lo rf_dbl_hi rf_id_lo rf_id_hi rf_dbl_lip rf_id_lip
            _ _ _ _ _ _ _ _).
  - exact rf_dbl_zero.
  - exact rf_dbl_one.
  - intros y Hy; apply (path_at_zero p); rewrite Hy; exact rf_dbl_zero.
  - intros y Hy; apply (path_at_one p); rewrite Hy; exact rf_dbl_one.
  - exact (unit_right_pointwise p).
  - intros x y Hy; apply Iap; symmetry; exact Hy.
Defined.

Lemma unit_left_homotopy {X : TopSpace} {a b : X} (p : Path X a b) :
  PathHomotopy (path_concat (const_path a) p) p.
Proof.
  unfold PathHomotopy.
  refine (@straight_homotopy X a b (path_map p) rf_dbl' rf_id
            rf_dbl'_lo rf_dbl'_hi rf_id_lo rf_id_hi rf_dbl'_lip rf_id_lip
            _ _ _ _ _ _ _ _).
  - exact rf_dbl'_zero.
  - exact rf_dbl'_one.
  - intros y Hy; apply (path_at_zero p); rewrite Hy; exact rf_dbl'_zero.
  - intros y Hy; apply (path_at_one p); rewrite Hy; exact rf_dbl'_one.
  - exact (unit_left_pointwise p).
  - intros x y Hy; apply Iap; symmetry; exact Hy.
Defined.

Lemma assoc_homotopy {X : TopSpace} {a b c d : X}
      (p : Path X a b) (q : Path X b c) (r : Path X c d) :
  PathHomotopy (path_concat (path_concat p q) r)
               (path_concat p (path_concat q r)).
Proof.
  unfold PathHomotopy.
  refine (@straight_homotopy X a d
            (path_map (path_concat p (path_concat q r))) rf_assoc rf_id
            rf_assoc_lo rf_assoc_hi rf_id_lo rf_id_hi rf_assoc_lip rf_id_lip
            _ _ _ _ _ _ _ _).
  - exact rf_assoc_zero.
  - exact rf_assoc_one.
  - intros y Hy; apply (path_at_zero (path_concat p (path_concat q r)));
      rewrite Hy; exact rf_assoc_zero.
  - intros y Hy; apply (path_at_one (path_concat p (path_concat q r)));
      rewrite Hy; exact rf_assoc_one.
  - exact (assoc_pointwise p q r).
  - intros x y Hy; apply Iap; symmetry; exact Hy.
Defined.

Lemma inverse_homotopy {X : TopSpace} {a b : X} (p : Path X a b) :
  PathHomotopy (path_concat p (path_rev p)) (const_path a).
Proof.
  unfold PathHomotopy.
  refine (@straight_homotopy X a a (path_map p) rf_tent rf_zero
            rf_tent_lo rf_tent_hi rf_zero_lo rf_zero_hi rf_tent_lip rf_zero_lip
            _ _ _ _ _ _ _ _).
  - exact rf_tent_zero.
  - exact rf_tent_one.
  - intros y Hy; apply (path_at_zero p); rewrite Hy; exact rf_tent_zero.
  - intros y Hy; apply (path_at_zero p); rewrite Hy; exact rf_tent_one.
  - exact (inverse_pointwise p).
  - intros x y Hy.
    transitivity a.
    + exact (const_arrow_eval a x).
    + symmetry; apply (path_at_zero p); exact Hy.
Defined.

(* * ** Concatenation is well defined on homotopy classes / * ** 结合在同伦类上的定义良好 *)

Section HomotopyConcat.

Context {X : TopSpace}.
Context {a b c : X}.
Context {p p' q q' : I_Top ~{Top}~> X}.
Context (H1 : ArrowHomotopy a b p p').
Context (H2 : ArrowHomotopy b c q q').
Context (Hp : p I_one ≈ b) (Hq : q I_zero ≈ b).
Context (Hp' : p' I_one ≈ b) (Hq' : q' I_zero ≈ b).

Lemma hconcat_agree (z : BS_Sq) : sq_t z = 1/2 →
  (ah_map H1 ∘[Top] Sq_leftside) z ≈ (ah_map H2 ∘[Top] Sq_rightside) z.
Proof.
  intro Hz.
  transitivity b.
  - transitivity (ah_map H1 (sq_pt I_one (bs_snd z))); [ | exact (ah_right H1 _) ].
    apply comp_eval_SqSq.
    + rewrite Sq_leftside_t, sq_pt_t, ival_I_one, Hz; Rlin.
    + rewrite Sq_leftside_s, sq_pt_s; reflexivity.
  - symmetry.
    transitivity (ah_map H2 (sq_pt I_zero (bs_snd z))); [ | exact (ah_left H2 _) ].
    apply comp_eval_SqSq.
    + rewrite Sq_rightside_t, sq_pt_t, ival_I_zero, Hz; Rlin.
    + rewrite Sq_rightside_s, sq_pt_s; reflexivity.
Qed.

Definition hconcat_map : Sq_Top ~{Top}~> X :=
  paste_arrow (A:=BS_Sq) sq_t Sq_t_lip (1/2)
    (ah_map H1 ∘[Top] Sq_leftside) (ah_map H2 ∘[Top] Sq_rightside) hconcat_agree.

Lemma hconcat_left (z : BS_Sq) :
  sq_t z <= 1/2 → hconcat_map z ≈ (ah_map H1 ∘[Top] Sq_leftside) z.
Proof.
  exact (paste_left (A:=BS_Sq) sq_t Sq_t_lip (1/2) _ _ hconcat_agree z).
Qed.

Lemma hconcat_right (z : BS_Sq) :
  1/2 <= sq_t z → hconcat_map z ≈ (ah_map H2 ∘[Top] Sq_rightside) z.
Proof.
  exact (paste_right (A:=BS_Sq) sq_t Sq_t_lip (1/2) _ _ hconcat_agree z).
Qed.

Definition hconcat :
  ArrowHomotopy a c (concat_arrow b p q Hp Hq) (concat_arrow b p' q' Hp' Hq').
Proof.
  refine {| ah_map := hconcat_map |}.
  - intro t.
    destruct (Rle_dec (ival t) (1/2)) as [Hle | Hnle].
    + transitivity ((ah_map H1 ∘[Top] Sq_leftside) (sq_pt t I_zero)).
      * apply hconcat_left; rewrite sq_pt_t; exact Hle.
      * transitivity (ah_map H1 (sq_pt (I_dbl t) I_zero)).
        { apply comp_eval_SqSq.
          - rewrite Sq_leftside_t, !sq_pt_t, I_dbl_eval; reflexivity.
          - rewrite Sq_leftside_s, !sq_pt_s; reflexivity. }
        { transitivity (p (I_dbl t)); [ exact (ah_bot H1 (I_dbl t)) | ].
          symmetry.
          apply concat_first; [ exact Hle | rewrite I_dbl_eval; Rlin ]. }
    + apply Rnot_le_lt in Hnle.
      transitivity ((ah_map H2 ∘[Top] Sq_rightside) (sq_pt t I_zero)).
      * apply hconcat_right; rewrite sq_pt_t; lra.
      * transitivity (ah_map H2 (sq_pt (I_dbl' t) I_zero)).
        { apply comp_eval_SqSq.
          - rewrite Sq_rightside_t, !sq_pt_t, I_dbl'_eval; reflexivity.
          - rewrite Sq_rightside_s, !sq_pt_s; reflexivity. }
        { transitivity (q (I_dbl' t)); [ exact (ah_bot H2 (I_dbl' t)) | ].
          symmetry.
          apply concat_second; [ lra | rewrite I_dbl'_eval; Rlin ]. }
  - intro t.
    destruct (Rle_dec (ival t) (1/2)) as [Hle | Hnle].
    + transitivity ((ah_map H1 ∘[Top] Sq_leftside) (sq_pt t I_one)).
      * apply hconcat_left; rewrite sq_pt_t; exact Hle.
      * transitivity (ah_map H1 (sq_pt (I_dbl t) I_one)).
        { apply comp_eval_SqSq.
          - rewrite Sq_leftside_t, !sq_pt_t, I_dbl_eval; reflexivity.
          - rewrite Sq_leftside_s, !sq_pt_s; reflexivity. }
        { transitivity (p' (I_dbl t)); [ exact (ah_top H1 (I_dbl t)) | ].
          symmetry.
          apply concat_first; [ exact Hle | rewrite I_dbl_eval; Rlin ]. }
    + apply Rnot_le_lt in Hnle.
      transitivity ((ah_map H2 ∘[Top] Sq_rightside) (sq_pt t I_one)).
      * apply hconcat_right; rewrite sq_pt_t; lra.
      * transitivity (ah_map H2 (sq_pt (I_dbl' t) I_one)).
        { apply comp_eval_SqSq.
          - rewrite Sq_rightside_t, !sq_pt_t, I_dbl'_eval; reflexivity.
          - rewrite Sq_rightside_s, !sq_pt_s; reflexivity. }
        { transitivity (q' (I_dbl' t)); [ exact (ah_top H2 (I_dbl' t)) | ].
          symmetry.
          apply concat_second; [ lra | rewrite I_dbl'_eval; Rlin ]. }
  - intro s.
    transitivity ((ah_map H1 ∘[Top] Sq_leftside) (sq_pt I_zero s)).
    + apply hconcat_left; rewrite sq_pt_t, ival_I_zero; lra.
    + transitivity (ah_map H1 (sq_pt I_zero s)); [ | exact (ah_left H1 s) ].
      apply comp_eval_SqSq.
      * rewrite Sq_leftside_t, !sq_pt_t, ival_I_zero; Rlin.
      * rewrite Sq_leftside_s, !sq_pt_s; reflexivity.
  - intro s.
    transitivity ((ah_map H2 ∘[Top] Sq_rightside) (sq_pt I_one s)).
    + apply hconcat_right; rewrite sq_pt_t, ival_I_one; lra.
    + transitivity (ah_map H2 (sq_pt I_one s)); [ | exact (ah_right H2 s) ].
      apply comp_eval_SqSq.
      * rewrite Sq_rightside_t, !sq_pt_t, ival_I_one; Rlin.
      * rewrite Sq_rightside_s, !sq_pt_s; reflexivity.
Defined.

End HomotopyConcat.

Definition path_concat_respects {X : TopSpace} {a b c : X}
           {p p' : Path X a b} {q q' : Path X b c}
           (E1 : PathHomotopy p p') (E2 : PathHomotopy q q') :
  PathHomotopy (path_concat p q) (path_concat p' q') :=
  hconcat E1 E2 (path_tgt p) (path_src q) (path_tgt p') (path_src q').

(* * ** Reversal inverts, on both sides / * ** 反转在两边都进行 *)

Lemma path_rev_rev {X : TopSpace} {a b : X} (p : Path X a b) (x : Ipt) :
  path_map (path_rev (path_rev p)) x ≈ path_map p x.
Proof.
  transitivity (path_map p (I_rev (I_rev x))).
  - reflexivity.
  - apply Iap; rewrite !I_rev_eval; lra.
Qed.

Lemma concat_pointwise {X : TopSpace} (b : X) (p q p' q' : I_Top ~{Top}~> X)
      (Hp : p I_one ≈ b) (Hq : q I_zero ≈ b)
      (Hp' : p' I_one ≈ b) (Hq' : q' I_zero ≈ b)
      (Ep : ∀ x, p x ≈ p' x) (Eq : ∀ x, q x ≈ q' x) (x : Ipt) :
  concat_arrow b p q Hp Hq x ≈ concat_arrow b p' q' Hp' Hq' x.
Proof.
  destruct (Rle_dec (ival x) (1/2)) as [Hle | Hnle].
  - transitivity (p (I_dbl x)).
    + apply concat_first; [ exact Hle | rewrite I_dbl_eval; Rlin ].
    + transitivity (p' (I_dbl x)); [ exact (Ep (I_dbl x)) | ].
      symmetry; apply concat_first; [ exact Hle | rewrite I_dbl_eval; Rlin ].
  - apply Rnot_le_lt in Hnle.
    transitivity (q (I_dbl' x)).
    + apply concat_second; [ lra | rewrite I_dbl'_eval; Rlin ].
    + transitivity (q' (I_dbl' x)); [ exact (Eq (I_dbl' x)) | ].
      symmetry; apply concat_second; [ lra | rewrite I_dbl'_eval; Rlin ].
Qed.

(*
 The other inverse law comes from the first one applied to the reversed
 path, together with the pointwise identity p‾‾ = p; no second homotopy
 needs to be built. 

 --------
 另一个逆律来自于将第一个逆律应用于反向路径，同时结合逐点恒等式 p‾‾ = p；不需要构建第二个同伦。
*)
Definition path_rev_inverse_left {X : TopSpace} {a b : X} (p : Path X a b) :
  PathHomotopy (path_concat (path_rev p) p) (const_path b).
Proof.
  unfold PathHomotopy.
  refine (ah_pointwise _ _ (inverse_homotopy (path_rev p))).
  - intro x.
    apply concat_pointwise.
    + intro y; reflexivity.
    + intro y; exact (path_rev_rev p y).
  - intro x; reflexivity.
Defined.

(** ** The fundamental groupoid / ** 基本群族 *)

Definition PathHomotopy_Equivalence {X : TopSpace} (a b : X) :
  Equivalence (@PathHomotopy X a b).
Proof.
  constructor.
  - intro p; exact (ah_refl a b (path_map p) (path_src p) (path_tgt p)).
  - intros p q H; exact (ah_sym H).
  - intros p q r H1 H2; exact (ah_trans H1 H2).
Defined.

Definition Path_Setoid {X : TopSpace} (a b : X) : Setoid (Path X a b) := {|
  equiv        := @PathHomotopy X a b;
  setoid_equiv := PathHomotopy_Equivalence a b
|}.

#[local] Obligation Tactic := idtac.

(*
 Mac Lane, CWM 2nd ed., §I.5, printed p. 20: the objects are the points of
 X, the arrows are the homotopy classes of paths, composition is the
 reparametrized concatenation and the identity is the constant path.  Every
 law holds only up to homotopy, and each is witnessed by one of the four
 explicit homotopies built above. 

 --------
 Mac Lane, CWM 第二版，第 I.5 节，印刷页 20：对象是 X 的点，箭头是路径的同伦类，组合是重新参数化的连接，恒等元是常值路径。每条规律仅在同伦意义下成立，每条规律都有上面构造的四个显式同伦之一作证。
*)
Program Definition FundamentalGroupoid (X : TopSpace) : Category := {|
  obj     := carrier (top_carrier X);
  hom     := fun a b => Path X a b;
  homset  := @Path_Setoid X;
  id      := @const_path X;
  compose := fun a b c q p => path_concat p q
|}.
Next Obligation.
  intros X x y z q q' E2 p p' E1.
  exact (path_concat_respects E1 E2).
Qed.
Next Obligation.
  intros X x y f; exact (unit_right_homotopy f).
Qed.
Next Obligation.
  intros X x y f; exact (unit_left_homotopy f).
Qed.
Next Obligation.
  intros X x y z w f g h; exact (assoc_homotopy h g f).
Qed.
Next Obligation.
  intros X x y z w f g h; exact (ah_sym (assoc_homotopy h g f)).
Qed.

(* Mac Lane §I.5: every arrow of the fundamental groupoid is invertible, the inverse of a class being the class of the reversed path. / Mac Lane §I.5：基本群oid的每一个箭头都是可逆的，一个类的逆是该路径反向的类。 *)
Definition fundamental_groupoid_is_groupoid (X : TopSpace) :
  IsGroupoid (FundamentalGroupoid X).
Proof.
  intros a b f.
  refine (@Build_IsIsomorphism (FundamentalGroupoid X) a b f (path_rev f) _ _).
  - exact (path_rev_inverse_left f).
  - exact (inverse_homotopy f).
Defined.

(*
 `≈`-equal points are distinct OBJECTS of π(X), but canonically isomorphic
 ones: the constant path at a is already a path from a to a', its target
 condition being the given `≈`.  This is what the header's remark on the
 object type asserts, proved rather than left as a remark. 

 --------
 `≈` — 相等的点是 π(X) 的不同对象，但它们在范畴上同构：在 a 的恒定路径已经是从 a 到 a' 的一条路径，它的目标条件是给定的 `≈`。这就是标题对对象类型的说明所断言的内容，得到了证明，而不是仅作为注释留下。
*)
Definition equal_points_path {X : TopSpace} {a a' : X} (H : a ≈ a') :
  Path X a a' := {|
  path_map := const_arrow a;
  path_src := reflexivity a;
  path_tgt := H
|}.

Definition equal_points_iso {X : TopSpace} {a a' : X} (H : a ≈ a') :
  @Isomorphism (FundamentalGroupoid X) a a' :=
  giso (fundamental_groupoid_is_groupoid X) (equal_points_path H).

(* * ** Path-connected spaces and the fundamental group / * ** 路径连通空间与基本群 *)

Definition PathConnected (X : TopSpace) : Type := ∀ a b : X, Path X a b.

Definition pathconnected_Connected {X : TopSpace} (K : PathConnected X) :
  Connected (FundamentalGroupoid X) :=
  @arrow_connected (FundamentalGroupoid X) K.

(* The fundamental group at a base point is the vertex group of the fundamental groupoid there (Structure/Groupoid.v's [vertex_group]). / 基点处的基本群是那里基本群族的顶点群（Structure/Groupoid.v 的 [vertex_group]）。 *)
Definition fundamental_group (X : TopSpace) (a : X) : GrpObject :=
  vertex_group (fundamental_groupoid_is_groupoid X) a.

(*
 Riehl, "Category Theory in Context", §1.5 Corollary 1.5.14, printed p. 36
 (PDF p. 56).  The derivation is the one Riehl gives: the fundamental
 groupoid of a path-connected space is a CONNECTED groupoid, the structure
 theorem [connected_deloop_equiv] makes the delooping of the vertex group at
 each point EQUIVALENT to it, and an equivalence between the resulting
 one-object categories yields an ISOMORPHISM of the two groups.  That last
 step is [deloop_ff_moniso]; the assembled statement is
 [connected_vertex_moniso] in Structure/Groupoid/Basepoint.v.  Nothing here
 conjugates by a chosen path directly.

 The two words are used in their exact senses: an equivalence of categories
 is what the structure theorem produces, and a group isomorphism -- a
 bijection of underlying setoids preserving unit and multiplication, which
 is what [MonIso] is -- is what comes out. 

 --------
 Riehl，《情境中的范畴论》，§1.5 推论 1.5.14，印刷版第 36 页（PDF 第 56 页）。推导过程是 Riehl 给出的：一个路径连通空间的基本群群是一个连通群群，结构定理 [connected_deloop_equiv] 使得每个点的顶点群的去环化与其等价，而由此得到的单对象范畴之间的等价会产生两个群的同构。最后一步是 [deloop_ff_moniso]；组装后的陈述在 Structure/Groupoid/Basepoint.v 中为 [connected_vertex_moniso]。这里没有直接通过选定路径进行共轭。这两个词按其确切意义使用：范畴的等价是结构定理产生的结果，而群同构——保持单位和乘法的底层集合的双射，即 [MonIso] 所表示的——就是其最终结果。
*)
Theorem fundamental_group_basepoint_independent {X : TopSpace}
        (K : PathConnected X) (a b : X) :
  MonIso (fundamental_group X a) (fundamental_group X b).
Proof.
  exact (connected_vertex_moniso (fundamental_groupoid_is_groupoid X)
           (pathconnected_Connected K) a b).
Defined.

(* * ** Two paths that agree pointwise are homotopic / * ** 点对点一致的两条路径是同伦的 *)

Definition pointwise_homotopic {X : TopSpace} {a b : X} (p q : Path X a b)
           (E : ∀ x : Ipt, path_map p x ≈ path_map q x) : PathHomotopy p q.
Proof.
  unfold PathHomotopy.
  refine (ah_pointwise _ _ (ah_refl a b (path_map p) (path_src p) (path_tgt p))).
  - intro x; reflexivity.
  - exact E.
Defined.

(* * ** Every map from the interval to a two-point discrete space is constant / * ** 从区间到两个点离散空间的每个映射都是常值映射 *)

(*
 The one genuinely topological fact proved here about [0,1].  It is the
 least-upper-bound argument, run on the clamped composite so that the
 supremum may be taken over a predicate on all of R.  This is what makes the
 fundamental groupoid detect path components rather than merely the
 underlying set of points.

 The argument is developed once, for an ARBITRARY discrete space whose
 equality is decidable ([interval_to_discrete_constant_dec]), and the
 two-point statement this file's witnesses use
 ([interval_to_discrete_constant]) is that theorem at [bool_setoid_object]
 with [Bool.bool_dec] for the decider.  Nothing about the codomain is used
 beyond the decider: [rclamp], [clampI], [I_scale] and the supremum argument
 never mention it.

 WHY A DECIDER, AND WHY IT COSTS NOTHING.  The supremum is taken over a
 predicate on R, so the set being bounded must live in [Prop]; but this
 library's `≈` is a [crelation] (Lib/Setoid.v), hence [Type]-valued, and
 `gval t ≈ gval 0` cannot be a conjunct of a [Prop] directly.  The decider
 supplies the [Prop] shadow -- [gsame] below, with [gsame_intro] and
 [gsame_elim] crossing between the two -- and it is a HYPOTHESIS, so no
 axiom is incurred: [interval_to_discrete_constant_dec] carries exactly the
 same three axioms as the two-point corollary and no others.  For the same
 [Type]-valued reason the decider is stated with [sum] rather than with
 [sumbool]: `{x ≈ y} + {~ (x ≈ y)}` does not typecheck for a general
 [SetoidObject].

 SCOPE: what is proved is constancy of continuous maps out of [0,1] into a
 discrete space with decidable equality.  Connectedness of [0,1] in the
 general sense -- no separation by a pair of disjoint nonempty opens, or
 constancy of maps into a discrete space whose equality is not decidable --
 is neither stated nor proved here. 

 --------
 这里证明的关于 [0,1] 的唯一真正拓扑事实是：上确界论证，它作用在夹紧的复合体上，以便可以对整个 R 上的谓词取上确界。这正是使基本群oid能够检测路径分量，而不仅仅是点的底层集合的原因。

 该论证是在一个任意离散空间上发展起来的，其等式是可判定的（[interval_to_discrete_constant_dec]），而该文件的见证使用的两点陈述（[interval_to_discrete_constant]）是 [bool_setoid_object] 处的定理，其中 [Bool.bool_dec] 用作判定器。除了判定器之外，未使用关于余域的任何内容：[rclamp]、[clampI]、[I_scale] 以及上确界论证从未提到它。为什么要有决策器，以及为什么它不花任何成本。上确界是通过 R 上的谓词来取的，所以被界定的集合必须存在于 [Prop] 中；但是这个库的 `≈` 是一个 [crelation]（Lib/Setoid.v），因此是 [Type] 值的，而 `gval t ≈ gval 0` 不能直接成为 [Prop] 的一个合取。决策器提供了 [Prop] 阴影——如下的 [gsame]，其中 [gsame_intro] 和 [gsame_elim] 在两者之间交叉——并且它是一个假设，因此不会引入公理：[interval_to_discrete_constant_dec] 恰好携带与两点推论相同的三个公理，没有其他。出于相同的 [Type] 值理由，决策器是用 [sum] 而不是 [sumbool] 来表述的：对于一般的 [SetoidObject]，`{x ≈ y} + {~ (x ≈ y)}` 无法进行类型检查。范围：所证明的是从 [0,1] 到具有可判定等式的离散空间的连续映射的恒定性。[0,1] 的连通性（一般意义上的——不能被一对不相交的非空开集分开，或映射到等式不可判定的离散空间的恒定性）在此既未陈述也未证明。
*)

Definition rclamp (r : R) : R := Rmax 0 (Rmin 1 r).

Lemma rclamp_lo (r : R) : 0 <= rclamp r.
Proof. unfold rclamp; apply Rmax_l. Qed.

Lemma rclamp_hi (r : R) : rclamp r <= 1.
Proof. unfold rclamp; apply Rmax_lub; [ lra | apply Rmin_l ]. Qed.

Lemma rclamp_id (r : R) : 0 <= r → r <= 1 → rclamp r = r.
Proof.
  intros H0 H1; unfold rclamp.
  rewrite Rmin_right by lra.
  apply Rmax_right; lra.
Qed.

Lemma rclamp_lip (r r' : R) : Rabs (rclamp r - rclamp r') <= Rabs (r - r').
Proof.
  unfold rclamp.
  apply Rle_trans with
    (r2 := Rmax (Rabs (0 - 0)) (Rabs (Rmin 1 r - Rmin 1 r'))).
  - apply Rabs_Rmax_le.
  - apply Rmax_lub.
    + assert (H : Rabs (0 - 0) = 0) by Rlin.
      rewrite H; apply Rabs_pos.
    + apply Rle_trans with (r2 := Rmax (Rabs (1 - 1)) (Rabs (r - r'))).
      * apply Rabs_Rmin_le.
      * apply Rmax_lub; [ | apply Rle_refl ].
        assert (H : Rabs (1 - 1) = 0) by Rlin.
        rewrite H; apply Rabs_pos.
Qed.

Definition clampI (r : R) : Ipt := mkI (rclamp r) (rclamp_lo r) (rclamp_hi r).

Section IntervalConnected.

Context (A : SetoidObject).
Context (dec : ∀ x y : A, (x ≈ y) + ((x ≈ y) → False)).
Context (f : I_Top ~{Top}~> Discrete_Top A).

Definition gval (r : R) : A := f (clampI r).

(*
 Every predicate that respects `≈` is open in the discrete topology
 (Instance/Top.v's [discrete_open]), so the fibre through [clampI r] is
 open and continuity hands back a radius on which [gval] does not move. 

 --------
 每个符合 `≈` 的谓词在离散拓扑中都是开的（Instance/Top.v 的 [discrete_open]），因此通过 [clampI r] 的纤维是开的，并且连续性会返回一个半径，在该半径上 [gval] 不会移动。
*)
Lemma gval_locally_constant (r : R) :
  { d : R & ((0 < d) ∧ (∀ r' : R, Rabs (r - r') < d → gval r' ≈ gval r))%type }.
Proof.
  assert (HU : IsOpen (Discrete_Top A) (fun z : A => z ≈ f (clampI r))).
  { intros u v Huv Hu; rewrite <- Huv; exact Hu. }
  destruct (continuity f (fun z : A => z ≈ f (clampI r)) HU
              (clampI r) (reflexivity _)) as [d [Hd Hball]].
  exists d; split.
  - exact Hd.
  - intros r' Hr'.
    apply Hball.
    simpl.
    apply Rle_lt_trans with (r2 := Rabs (r - r')); [ | exact Hr' ].
    apply rclamp_lip.
Qed.

(*
 The [Prop] shadow of `gval t ≈ gval 0`, which is what lets [Egv] be a
 predicate on R and so be handed to [completeness].  This is the only place
 the decider is used, and the two lemmas below are the two directions of the
 translation. 

 --------
 [Prop] 的影子 `gval t ≈ gval 0`，这使得 [Egv] 可以成为 R 上的谓词，因此可以交给 [completeness]。这是唯一使用判定器的地方，下面的两个引理是翻译的两个方向。
*)
Definition gsame (t : R) : Prop :=
  if dec (gval t) (gval 0) then True else False.

Lemma gsame_intro (t : R) : gval t ≈ gval 0 → gsame t.
Proof.
  intro H; unfold gsame.
  destruct (dec (gval t) (gval 0)) as [_ | Hno]; [ exact I | exact (Hno H) ].
Qed.

Lemma gsame_elim (t : R) : gsame t → gval t ≈ gval 0.
Proof.
  unfold gsame.
  destruct (dec (gval t) (gval 0)) as [Hyes | _];
    [ intros _; exact Hyes | contradiction ].
Qed.

Definition Egv (t : R) : Prop := 0 <= t /\ t <= 1 /\ gsame t.

Lemma gval_endpoints : gval 1 ≈ gval 0.
Proof.
  assert (Hb : bound Egv).
  { exact (@ex_intro R (is_upper_bound Egv) 1
             (fun t Ht => proj1 (proj2 Ht))). }
  assert (He : ex Egv).
  { exact (@ex_intro R Egv 0
             (conj (Rle_refl 0)
                (conj Rle_0_1 (gsame_intro 0 (reflexivity _))))). }
  destruct (completeness Egv Hb He) as [m [Hub Hlub]].
  assert (Hm0 : 0 <= m).
  { exact (Hub 0 (conj (Rle_refl 0)
                    (conj Rle_0_1 (gsame_intro 0 (reflexivity _))))). }
  assert (Hm1 : m <= 1).
  { exact (Hlub 1 (fun t Ht => proj1 (proj2 Ht))). }
  destruct (gval_locally_constant m) as [d [Hd Hball]].
  (* the value at the supremum already agrees, by approximation from below / 极大值处的取值已经一致，通过从下方逼近 *)
  assert (Hgm : gval m ≈ gval 0).
  { destruct (dec (gval m) (gval 0)) as [Hyes | Hno]; [ exact Hyes | ].
    exfalso.
    assert (Hup : is_upper_bound Egv (m - d)).
    { intros t Ht.
      apply Rnot_lt_le.
      intro Hlt.
      apply Hno.
      transitivity (gval t).
      - symmetry.
        apply Hball.
        pose proof (Hub t Ht).
        Rlin.
      - exact (gsame_elim t (proj2 (proj2 Ht))). }
    pose proof (Hlub (m - d) Hup).
    lra. }
  (* and the supremum is the right endpoint / 且上确界是右端点 *)
  assert (Hm : m = 1).
  { assert (Hnot : 1 <= m).
    { apply Rnot_lt_le.
      intro Hlt.
      pose proof (Hball (Rmin 1 (m + d/2))) as Hnear.
      assert (Hlo : 0 <= Rmin 1 (m + d/2)) by (apply Rmin_glb; lra).
      assert (Hhi : Rmin 1 (m + d/2) <= 1) by apply Rmin_l.
      assert (Hgt : m < Rmin 1 (m + d/2)) by (apply Rmin_glb_lt; lra).
      assert (Hclose : Rabs (m - Rmin 1 (m + d/2)) < d).
      { pose proof (Rmin_l 1 (m + d/2)).
        pose proof (Rmin_r 1 (m + d/2)).
        Rlin. }
      pose proof (Hub (Rmin 1 (m + d/2))
                    (conj Hlo (conj Hhi
                       (gsame_intro _
                          (transitivity (Hnear Hclose) Hgm))))).
      lra. }
    lra. }
  rewrite <- Hm; exact Hgm.
Qed.

Lemma f_endpoints : f I_one ≈ f I_zero.
Proof.
  assert (Hc1 : ival (clampI 1) = ival I_one).
  { change (rclamp 1 = ival I_one).
    rewrite rclamp_id by lra.
    symmetry; exact ival_I_one. }
  assert (Hc0 : ival (clampI 0) = ival I_zero).
  { change (rclamp 0 = ival I_zero).
    rewrite rclamp_id by lra.
    symmetry; exact ival_I_zero. }
  assert (H1 : f (clampI 1) ≈ f I_one) by exact (Iap f (clampI 1) I_one Hc1).
  assert (H0 : f (clampI 0) ≈ f I_zero) by exact (Iap f (clampI 0) I_zero Hc0).
  rewrite <- H1, <- H0.
  exact gval_endpoints.
Qed.

End IntervalConnected.

(* Rescaling by the target point turns the endpoint statement into constancy on the whole interval. / 通过目标点重新缩放将端点陈述转化为整个区间上的不变性。 *)
Lemma scale_lo (c : R) (H0 : 0 <= c) (H1 : c <= 1) (t : R) :
  0 <= t → t <= 1 → 0 <= c * t.
Proof. intros; nra. Qed.

Lemma scale_hi (c : R) (H0 : 0 <= c) (H1 : c <= 1) (t : R) :
  0 <= t → t <= 1 → c * t <= 1.
Proof. intros; nra. Qed.

Lemma scale_lip (c : R) (H0 : 0 <= c) (H1 : c <= 1) : RLip 2 (fun t => c * t).
Proof.
  intros x y.
  replace (c * x - c * y) with (c * (x - y)) by ring.
  rewrite Rabs_mult.
  apply Rmult_le_compat_r; [ apply Rabs_pos | Rlin ].
Qed.

Definition I_scale (c : R) (H0 : 0 <= c) (H1 : c <= 1) : I_Top ~{Top}~> I_Top :=
  I_arrow (fun t => c * t) 2 two_pos
    (scale_lo c H0 H1) (scale_hi c H0 H1) (scale_lip c H0 H1).

Theorem interval_to_discrete_constant_dec (A : SetoidObject)
        (dec : ∀ x y : A, (x ≈ y) + ((x ≈ y) → False))
        (f : I_Top ~{Top}~> Discrete_Top A) (x : Ipt) : f x ≈ f I_zero.
Proof.
  pose (s := I_scale (ival x) (ipt_lo x) (ipt_hi x)).
  pose proof (f_endpoints A dec (f ∘[Top] s)) as H.
  assert (E1 : ival (s I_one) = ival x).
  { change (ival x * ival I_one = ival x); rewrite ival_I_one; ring. }
  assert (E0 : ival (s I_zero) = ival I_zero).
  { change (ival x * ival I_zero = ival I_zero); rewrite ival_I_zero; ring. }
  assert (H1 : (f ∘[Top] s) I_one ≈ f x) by exact (comp_eval_I f s I_one x E1).
  assert (H0 : (f ∘[Top] s) I_zero ≈ f I_zero)
    by exact (comp_eval_I f s I_zero I_zero E0).
  rewrite <- H1, <- H0; exact H.
Qed.

(*
 The two-point case, which is the one the witnesses below use.  [Bool_Discrete]
 IS [Discrete_Top bool_setoid_object] (Instance/Top.v) and that setoid
 takes [eq] for its `≈`, so the conclusion is stated with `=` here and the
 general theorem discharges it by conversion.  [Bool.bool_dec] returns a
 [sumbool], which is transported to the [sum] the general statement asks for;
 see the note above on why that statement cannot use [sumbool] itself. 

 --------
 双点情况，即下面证人使用的情况。[Bool_Discrete] 是 [Discrete_Top bool_setoid_object]（Instance/Top.v），并且该 setoid 采用 [eq] 作为其 `≈`，因此结论在这里用 `=` 表示，而一般定理通过转换来解决它。[Bool.bool_dec] 返回一个 [sumbool]，该结果被传递到一般声明所要求的 [sum]；参见上面关于为什么该声明不能使用 [sumbool] 本身的说明。
*)
Theorem interval_to_discrete_constant (f : I_Top ~{Top}~> Bool_Discrete)
        (x : Ipt) : f x = f I_zero.
Proof.
  exact (interval_to_discrete_constant_dec bool_setoid_object
           (fun a b => match Bool.bool_dec a b with
                       | left H => inl H
                       | right H => inr H
                       end) f x).
Qed.

(* * ** The vertex-group inclusion is an equivalence / * ** 顶点群包含是一个等价关系 *)

(*
 Riehl, "Category Theory in Context", §1.5 Remark 1.5.15, printed p. 36
 (PDF p. 56), COMPONENTWISE ONLY.  Riehl's remark compares two functors on
 based path-connected spaces -- the fundamental group and the fundamental
 groupoid -- and observes that the inclusion of the former into the latter is
 natural while the inverse equivalences, which depend on a choice of path
 from each point to the base point, are not.  What is proved here is only the
 statement at a single space: the inclusion of the vertex group at a is an
 equivalence of categories.  The functoriality in based maps, the naturality
 of the inclusion, and the negative statement about the inverses are NOT
 formalized here; see the header for the scope. 

 --------
 Riehl，《上下文中的范畴论》，§1.5 备注 1.5.15，印刷版第36页（PDF 第56页），仅组件级。Riehl 的备注比较了基于基点的路径连通空间上的两个函子——基本群和基本群oid——并观察到前者到后者的包含是自然的，而依赖于从每个点到基点选择的路径的逆等价则不是。这里证明的仅是在单个空间上的陈述：顶点 a 的顶点群的包含是范畴的等价。在基于映射上的函子性、包含的自然性以及关于逆的否定性陈述在这里没有形式化；详见范围标题。
*)
Definition fundamental_group_inclusion {X : TopSpace} (a : X) :
  Deloop (fundamental_group X a) ⟶ FundamentalGroupoid X :=
  vertex_incl (fundamental_groupoid_is_groupoid X) a.

Theorem fundamental_group_inclusion_equivalence {X : TopSpace}
        (K : PathConnected X) (a : X) :
  EquivalenceOfCategories (fundamental_group_inclusion a).
Proof.
  exact (connected_deloop_equiv (fundamental_groupoid_is_groupoid X)
           (pathconnected_Connected K) a).
Defined.

(* * ** Non-vacuity: the construction separates two topologies on one set / * ** 非空性：该构造将一个集合上的两种拓扑分开 *)

(*
 The two spaces below have the SAME setoid of points -- Instance/Top.v's
 [bool_setoid_object] -- and differ only in their topology.  The fundamental
 groupoid tells them apart: it is provably not connected on the discrete one
 and is connected on the indiscrete one.  So the construction is reading the
 topology, not the underlying set, and neither statement is vacuous. 

 --------
 下面的两个空间具有相同的点集（实例/Top.v 的 [bool_setoid_object]），仅在拓扑结构上有所不同。基本群oid 能够区分它们：在离散空间上它可被证明是不连通的，而在平凡空间上它是连通的。因此，这个构造是读取拓扑，而不是底层集合，并且这两个说法都不是空洞的。
*)

Example bool_carriers_agree :
  top_carrier Bool_Discrete = top_carrier TwoPoint_Indiscrete := eq_refl.

(* On the discrete two-point space every path takes one and the same value at every parameter, by [interval_to_discrete_constant]. Hence there is no path from [true] to [false]. / 在离散的两点空间中，每一条路径在每一个参数处都取相同的值，由 [interval_to_discrete_constant] 给出。因此不存在从 [true] 到 [false] 的路径。 *)
Theorem no_path_true_false : Path Bool_Discrete true false → False.
Proof.
  intro p.
  assert (H : path_map p I_one = path_map p I_zero)
    by exact (interval_to_discrete_constant (path_map p) I_one).
  assert (Hs : path_map p I_zero = true) by exact (path_src p).
  assert (Ht : path_map p I_one = false) by exact (path_tgt p).
  rewrite H, Hs in Ht.
  discriminate.
Qed.

Theorem Bool_Discrete_not_pathconnected : PathConnected Bool_Discrete → False.
Proof. intro K; exact (no_path_true_false (K true false)). Qed.

(*
 And the fundamental groupoid itself is not connected, so the hypothesis of
 [fundamental_group_basepoint_independent] is a real restriction. 

 --------
 而基本群范畴本身并不是连通的，所以 [fundamental_group_basepoint_independent] 的假设是一个真正的限制。
*)
Theorem Bool_Discrete_pi_not_connected :
  Connected (FundamentalGroupoid Bool_Discrete) → False.
Proof.
  intro K.
  exact (no_path_true_false
           (connected_arrow (fundamental_groupoid_is_groupoid Bool_Discrete)
              K true false)).
Qed.

(*
 At EVERY point of the discrete space the vertex group is trivial, the base
 point being bound rather than fixed at [true]: by
 [interval_to_discrete_constant] a loop at [a] takes the value [a] at every
 parameter, so it is homotopic to the constant loop.  The conclusion is a
 statement about HOMOTOPY CLASSES -- the hom-setoid at [a] has exactly one
 class -- and not that the type of loops has exactly one inhabitant, which is
 false: two loops with different continuity witnesses are different terms. 

 --------
 在离散空间的每一点上，顶点群都是平凡的，基点是绑定的而不是固定在 [true]：通过 [interval_to_discrete_constant] 在 [a] 处的一个环路在每个参数上取值为 [a]，因此它与恒定环路是同伦的。结论是关于同伦类的陈述——在 [a] 处的 hom-集合恰好有一个类——而不是环路类型恰好有一个元素，这并不正确：具有不同连续性证明的两个环路是不同的项。
*)
Theorem Bool_Discrete_loops_trivial (a : bool)
        (f : a ~{FundamentalGroupoid Bool_Discrete}~> a) : f ≈ id.
Proof.
  apply pointwise_homotopic.
  intro x.
  assert (H : path_map f x = path_map f I_zero)
    by exact (interval_to_discrete_constant (path_map f) x).
  assert (Hs : path_map f I_zero = a) by exact (path_src f).
  change (path_map f x = a).
  rewrite H; exact Hs.
Qed.

(* The indiscrete twin. Every setoid map into it is continuous ([into_indiscrete_continuous] in Instance/Top.v), so the step function that jumps at the right endpoint is a path from a to b. / 不离散的孪生。每个映射到它的集合映射都是连续的（[into_indiscrete_continuous] 在 Instance/Top.v 中），因此在右端点跳跃的阶梯函数是从 a 到 b 的路径。 *)
Definition two_pt_fun (a b : bool) (x : Ipt) : bool :=
  if Rle_dec 1 (ival x) then b else a.

Definition two_pt_setoid_map (a b : bool) :
  SetoidMorphism (top_carrier I_Top) bool_setoid_object.
Proof.
  refine {| morphism := two_pt_fun a b |}.
  intros x y Hxy.
  assert (H : ival x = ival y) by exact Hxy.
  unfold two_pt_fun; rewrite H; reflexivity.
Defined.

Definition two_pt_arrow (a b : bool) : I_Top ~{Top}~> TwoPoint_Indiscrete :=
  Build_ContinuousMorphism I_Top TwoPoint_Indiscrete (two_pt_setoid_map a b)
    (into_indiscrete_continuous I_Top bool_setoid_object
       (two_pt_setoid_map a b)).

Definition indiscrete_path (a b : bool) : Path TwoPoint_Indiscrete a b.
Proof.
  refine {| path_map := two_pt_arrow a b |}.
  - change (two_pt_fun a b I_zero = a).
    unfold two_pt_fun; rewrite ival_I_zero.
    destruct (Rle_dec 1 0) as [Hle | Hnle]; [ exfalso; lra | reflexivity ].
  - change (two_pt_fun a b I_one = b).
    unfold two_pt_fun; rewrite ival_I_one.
    destruct (Rle_dec 1 1) as [Hle | Hnle]; [ reflexivity | exfalso; apply Hnle; lra ].
Defined.

Definition TwoPoint_Indiscrete_pathconnected : PathConnected TwoPoint_Indiscrete :=
  indiscrete_path.

Definition TwoPoint_Indiscrete_pi_connected :
  Connected (FundamentalGroupoid TwoPoint_Indiscrete) :=
  pathconnected_Connected TwoPoint_Indiscrete_pathconnected.

(*
 Riehl's Corollary 1.5.14 at the witness: the fundamental groups of the
 indiscrete two-point space at its two distinct base points are isomorphic,
 the isomorphism obtained through the structure theorem. 

 --------
 Riehl 的推论 1.5.14 在见证点上：不可分的两点空间在其两个不同基点处的基本群是同构的，通过结构定理得到同构。
*)
Definition TwoPoint_Indiscrete_basepoint_iso :
  MonIso (fundamental_group TwoPoint_Indiscrete true)
         (fundamental_group TwoPoint_Indiscrete false) :=
  fundamental_group_basepoint_independent TwoPoint_Indiscrete_pathconnected
    true false.

(*
 And the inclusion of the fundamental group at [true] into the whole
 fundamental groupoid is an equivalence of categories there. 

 --------
 而在此，基本群在 [true] 的包含到整个基本群族是一个范畴等价。
*)
Definition TwoPoint_Indiscrete_inclusion_equivalence :
  EquivalenceOfCategories (fundamental_group_inclusion (X:=TwoPoint_Indiscrete) true) :=
  fundamental_group_inclusion_equivalence TwoPoint_Indiscrete_pathconnected true.

(*
 On the indiscrete space every homotopy is available, because every setoid
 map out of the square is continuous into it.  So any two paths with the
 same endpoints are homotopic, and its vertex groups are trivial too.  This
 is what makes the pair a contrast in CONNECTEDNESS and nothing else: both
 witnesses have trivial fundamental groups, and neither exhibits a
 nontrivial one. 

 --------
 在不离散的空间上，每个同伦都是可用的，因为从方块出的每个集合化映射到它都是连续的。所以任何两个具有相同端点的路径都是同伦的，并且它的顶点群也是平凡的。这正是使这对在连通性上形成对比而不涉及其他的原因：两个证人都有平凡的基本群，并且都没有展示非平凡的基本群。
*)
Definition indiscrete_ah_fun {a b : bool} (p q : Path TwoPoint_Indiscrete a b)
           (z : BS_Sq) : bool :=
  if Rle_dec (sq_s z) (1/2) then path_map p (bs_fst z) else path_map q (bs_fst z).

Definition indiscrete_ah_setoid_map {a b : bool}
           (p q : Path TwoPoint_Indiscrete a b) :
  SetoidMorphism (top_carrier Sq_Top) bool_setoid_object.
Proof.
  refine {| morphism := indiscrete_ah_fun p q |}.
  intros z w Hzw.
  assert (H1 : sq_t z = sq_t w) by exact (fst Hzw).
  assert (H2 : sq_s z = sq_s w) by exact (snd Hzw).
  unfold indiscrete_ah_fun.
  rewrite H2.
  destruct (Rle_dec (sq_s w) (1/2)).
  - exact (Iap (path_map p) (bs_fst z) (bs_fst w) H1).
  - exact (Iap (path_map q) (bs_fst z) (bs_fst w) H1).
Defined.

Definition indiscrete_homotopy {a b : bool} (p q : Path TwoPoint_Indiscrete a b) :
  PathHomotopy p q.
Proof.
  unfold PathHomotopy.
  refine {| ah_map :=
              Build_ContinuousMorphism Sq_Top TwoPoint_Indiscrete
                (indiscrete_ah_setoid_map p q)
                (into_indiscrete_continuous Sq_Top bool_setoid_object
                   (indiscrete_ah_setoid_map p q)) |}.
  - intro t.
    change (indiscrete_ah_fun p q (sq_pt t I_zero) = path_map p t).
    unfold indiscrete_ah_fun; rewrite sq_pt_s, ival_I_zero.
    destruct (Rle_dec 0 (1/2)) as [Hle | Hnle];
      [ reflexivity | exfalso; apply Hnle; lra ].
  - intro t.
    change (indiscrete_ah_fun p q (sq_pt t I_one) = path_map q t).
    unfold indiscrete_ah_fun; rewrite sq_pt_s, ival_I_one.
    destruct (Rle_dec 1 (1/2)) as [Hle | Hnle];
      [ exfalso; lra | reflexivity ].
  - intro s.
    change (indiscrete_ah_fun p q (sq_pt I_zero s) = a).
    unfold indiscrete_ah_fun.
    destruct (Rle_dec (sq_s (sq_pt I_zero s)) (1/2)).
    + exact (path_src p).
    + exact (path_src q).
  - intro s.
    change (indiscrete_ah_fun p q (sq_pt I_one s) = b).
    unfold indiscrete_ah_fun.
    destruct (Rle_dec (sq_s (sq_pt I_one s)) (1/2)).
    + exact (path_tgt p).
    + exact (path_tgt q).
Defined.

Theorem TwoPoint_Indiscrete_loops_trivial (a : bool)
        (f : a ~{FundamentalGroupoid TwoPoint_Indiscrete}~> a) : f ≈ id.
Proof. exact (indiscrete_homotopy f (const_path (X:=TwoPoint_Indiscrete) a)). Qed.
