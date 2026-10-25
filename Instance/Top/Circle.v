Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lqa.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyReals.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyRealsMult.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyAbs.

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.
Require Import Category.Instance.Top.Subspace.TypeValued.

Generalizable All Variables.

(* * * The real line and the circle over the constructive reals / * * 构造实数上的实数直线与圆 *)

(*
 Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
 §V.1, book p. 111 (PDF p. 120), read from the page image: in the
 p-adic solenoid's tower "take each object F_n to be a circle S^1,
 and each arrow f_n : S^1 → S^1 to be the continuous map wrapping the
 domain circle S^1 uniformly p times around the codomain circle"
 (catalog id maclane:V.1:construction3)
 Riehl, "Category Theory in Context", §3.6, Example 3.6.3, printed
 p. 116 (PDF p. 136), read from the page image: "each generating map
 is the 'pth power map,' the covering map that wraps the domain
 circle uniformly p times around the codomain circle"
 (catalog id riehl:3.6:example3)
 nLab: https://ncatlab.org/nlab/show/solenoid
 nLab: https://ncatlab.org/nlab/show/Cauchy+real+number
 Wikipedia: https://en.wikipedia.org/wiki/Solenoid_(mathematics)
 Rocq standard library: Reals/Cauchy/ConstructiveCauchyReals.v,
 ConstructiveCauchyRealsMult.v and ConstructiveCauchyAbs.v

 BACKGROUND.  The circle enters the tree as the object of a tower.
 Mac Lane's §V.1 and Riehl's §3.6 build the p-adic solenoid as the
 limit in Top of circles under the map that wraps a circle p times
 around itself (Instance/Top/Solenoid.v).  Neither page says which
 model of the circle it means.  This file takes the standard one, the
 real line modulo the integers, S^1 = R/Z, the "quotient of the reals"
 of issue #410's own text.  On R/Z Riehl's "pth power map" and Mac
 Lane's wrapping map are one map, multiplication by p: under the
 identification of R/Z with the unit circle in the complex plane by
 x ↦ e^(2πix), the power z ↦ z^p is x ↦ p·x.  nLab's solenoid page
 writes the dyadic case as e^(iθ) ↦ e^(2iθ), and Wikipedia's article
 describes the transition map as uniformly wrapping one circle around
 the next; both are the same map in these coordinates.  The
 identification with the complex circle is background only: the tree
 has no complex numbers, and nothing below uses them.

 WHICH REALS.  The reals already in the tree are the standard
 library's classical [R], and they carry axioms: [Print Assumptions] of
 Instance/Top/Interval.v's [I_Top] prints
 ClassicalDedekindReals.sig_forall_dec and
 FunctionalExtensionality.functional_extensionality_dep (measured in a
 scratch file carrying this file and that one).  This file uses the
 standard library's CONSTRUCTIVE Cauchy reals [CReal] instead: a
 record of a sequence of rationals indexed by the integers, [seq], with
 the proof [cauchy] that it converges at the fixed rate 2^k, and a
 bound; its order [CRealLt] is Set-valued and its equality [CRealEq]
 is a proposition (the library's own definitions, read in
 ConstructiveCauchyReals.v).  These are nLab's "modulated" Cauchy
 reals.  [Print Assumptions] prints "Closed under the global context"
 for every one of this file's 94 constants, listed by
 [Print Module] and including its nine [Program] obligations.  No
 classical real is loaded: [Print Libraries] of a scratch file
 requiring Instance/Top/Solenoid.v lists six standard-library reals
 modules, all under Reals/Cauchy (the three imported here, PosExtra,
 QExtra and ConstructiveExtra).  One caution, quoted from the head of
 ConstructiveCauchyReals.v: "this module is not meant to be imported
 directly, please import `Reals.Abstract.ConstructiveReals` instead",
 and "this file is experimental and likely to change in future
 releases".  The abstract interface does not name [CReal] or its
 lemmas, which this file needs, so the three modules are imported
 directly, under the logical prefix the tree already uses for the
 standard library (Coq.Reals....).  The file compiles on Rocq 9.1,
 Coq 8.19.2 and Coq 8.20.1.

 THE POINTS.  [RLine_setoid] is [CReal] under [CRealEq].
 [Circle_setoid] is [CReal] under [circ_eq]: two reals are one point
 of the circle when their difference is an integer, and the integer is
 KEPT AS DATA, [{ k : Z & x - y == k }].  The balls of the circle,
 [cball], carry their integer translate the same way.  The reason is
 the Type-valued [Top]: its opens are Type-valued predicates, and the
 forward half of [circle_open_balls] moves a point of an open along an
 integer translate [y + k] inside such a predicate, which needs [k] as
 a term; Coq does not eliminate a proof of an existential proposition
 into a type.  The quotient map [circ_q] is the identity on
 representatives, and [circ_mul p] is x ↦ p·x on points, shared by
 both circles below; it respects [circ_eq] because p times an integer
 is an integer.

 THE EQUALITY IS NONETHELESS A PROPOSITION.  The integer a witness of
 [circ_eq] carries is determined by the two points
 ([circ_eq_witness_unique]).  [circ_peq] is the same existence stated
 in [Prop], and [circ_eq_of_peq] goes back by computing the integer
 from the real: [cround d] is the floor of the rational approximation
 [seq d (-4)] plus 1/2, and [cround_between] shows it is k for every
 real within 1/4 of the integer k, the approximation lying within 1/8
 of the real ([CRealLe_not_lt] at precision 2^-4); [cround_spec] and
 [cround_ball] are the two cases used, a real equal to k and a real
 whose distance to k is at most 1/4.  No choice principle is used.  So
 [circ_PropEquiv] is the [PropEquiv] of [Circle_setoid]
 (Lib/Setoid/Propositional.v), the field an [AbObject] owes;
 Instance/Top/Solenoid/Presentations.v's circle group [CircleGroup]
 consumes it.  [circle_lift_iso] is the identity on points between
 Instance/Sets/Classifier.v's lift [Setoid_Lift Circle_setoid@{o}] and
 [Circle_setoid@{h}], an isomorphism in [Sets@{h hs}], the category
 Instance/Top/Forgetful.v's [Top_Forget] lands in.

 THE TOPOLOGIES.  An open of the line is a predicate each of whose
 points has a closed rational ball [rball] inside it, the metric
 topology: [ropen], Type-valued, gives [RLine : TopSpace]; [propen],
 Prop-valued, gives [PRLine : PTop].  The circle is the QUOTIENT of the
 line along [circ_q] in each category: [Circle] is
 Instance/Top/Subspace/TypeValued.v's [TQuot] over #259's Type-valued
 [Top], and [PCircle] is Instance/Top/Subspace.v's [PQuot] over
 [PTopCat].  One circle is built per category, and the two share their
 points and the p-fold map.  [circle_open_balls] and
 [pcircle_open_balls] identify each quotient topology with the circle's
 own ball topology, both directions, with no hypothesis.  The p-fold
 maps [wrap p] and [pwrap p] are continuous by the quotient's universal
 property ([tquot_desc], [pquot_desc]), because multiplication by p is
 continuous on the line: [rball_mul] carries a ball of radius e/p into
 one of radius e.  [cint] is the interior of a closed ball of the
 circle; [cint_open], [cint_centre] and [cint_sub] are what the
 universal properties of Instance/Top/Solenoid.v's [Solenoid p] and of
 Instance/Top/Solenoid/Presentations.v's ball subspaces [CSub] turn
 on.

 THE HYPOTHESIS ON p.  [p : positive], a positive integer.  Mac Lane's
 p is a prime (book p. 110, PDF p. 119: "The p-adic integers Z_p (with
 p a prime) illustrate this construction", the paragraph the solenoid
 paragraph follows); Riehl's is not qualified.  Nothing in this file
 uses primality.  What is used is that p is an integer, so that
 [circ_mul] respects [circ_eq], and that it is positive, so that the
 radius e/p of [rball_mul] is positive ([q_scale_pos]).  At p = 1 the
 wrapping maps are the identity up to [≈] ([wrap_one], [pwrap_one]).

 STRENGTHS.  At [eq_refl]: [Circle_points] and [PCircle_points] (the
 points of each circle ARE [Circle_setoid]), [wrap_map] and
 [pwrap_map] (the underlying map of each wrapping map IS [circ_mul p]).
 [wrap_one] and [pwrap_one] hold up to [≈] in the hom-setoids of [Top]
 and [PTopCat]: 1·x and x are equal reals, [CReal_mult_1_l], not
 convertible terms.  [circle_open_balls] is an [iffT] of Type-valued
 opens, [pcircle_open_balls] an [iff] of Prop-valued ones.
 [circle_half_not_zero] refutes 1/2 ≈ 0 on the circle, so the circle
 has two distinct points; it reduces to 1 = 2k in the integers through
 [creal_inject_Q_injective].  [circ_eq_witness_unique] and the three
 rounding lemmas are Leibniz equalities of integers, and
 [circle_lift_iso] is an isomorphism whose laws hold up to [≈].
 Test/ProbeSolenoid410.v pins the boundary of [wrap_one]: its N1
 refuses [eq_refl] for [wrap 1] at a point ("cannot unify"), and
 [p410_wrap_one] is the [≈] statement beside it.

 UNIVERSES, read by [About] under [Set Printing Universes] on all 94
 constants of the [Print Module] listing.
 - [@{}] (23 constants): the rational and real arithmetic, [posR],
 [rball] and its lemmas, the rounding [cround] with its three
 lemmas, and [circ_peq].  [@{u}] (15): [circ_eq], [cball] and their
 lemmas, [circ_eq_witness_unique], [circ_eq_of_peq] and
 [circ_peq_of_eq], [u] the sort of the integer witness.  [@{o}]
 (43): the setoids, the two lines, [circ_q], [circ_mul], [Circle],
 [PCircle], [cint], the ball characterisations,
 [circle_half_not_zero] and [circ_PropEquiv].  [@{h o}] (5) with
 the block [o < h]: [line_mul_cont], [rline_mul], [wrap],
 [wrap_map], [wrap_one], the arrows of [Top@{h o}], whose homs sit
 above the points (Instance/Top.v's [ContinuousMorphism_equiv]).
 [@{h o hs}] (5, [circle_lift_iso] and its four obligations) with
 [o < h] and [h < hs], the block of [Top_Forget].  [@{o so}] (3)
 with [Set < so] and [o < so]: [pwrap], [pwrap_map], [pwrap_one],
 the block of [PTopCat@{o so}] (Instance/Top/Prop.v's header).
 - No block carries an equation, and no universe of this file is
 pinned at [Set]: the circle and both lines exist at every points
 universe [o].  The word [Set] occurs 273 times in the output: 3
 times as [Set < so] in the three [pwrap] blocks, and otherwise
 only as a strict lower bound of the standard library's own
 monomorphic universes, [Set < Basics.flip.u0], [.u1] and [.u2] in
 61 blocks, [Set < Morphisms.Proper.u0] and
 [Set < Morphisms.Relations.u0] in 37,
 [Set < Morphisms.GenericInstances.u0] in 8 and
 [Set < eq_ind_r.u0] in 5.  These relate [Set] to global universes
 only and constrain none of this file's.  In file order they are
 first carried by [creal_inject_Z_mult] (the [flip] bounds),
 [inject_Q_minus_int_inv] ([Proper], [Relations]) and
 [cround_between] ([GenericInstances], [eq_ind_r]), each a
 [rewrite] under [CRealEq], [CRealLe] or [Qlt]; a one-line
 [rewrite] of a [CRealEq] hypothesis in a scratch file carries the
 same [flip], [Proper] and [Relations] bounds, and its proof term
 is built from [iff_flip_impl_subrelation] and [PER_morphism], the
 generalized rewriting combinators on propositions, whose type
 [Prop] has sort [Set+1].
 - The remaining caps are [<=] bounds on global universes that the
 donors carry in their own blocks: [compose.u*] and [ID.u0]
 (Instance/Sets.v's setoid maps, through [Top] and [PTopCat]) on
 [o] in 7 blocks and on [h] in the 5 of [circle_lift_iso], and
 [projections.u0] and [.u1] (Instance/Top/Subspace/TypeValued.v's
 [TQuot]) on [o] in 11 blocks and on [h] in 3 ([wrap], [wrap_map],
 [wrap_one]).

 DELIVERED ELSEWHERE.  Instance/Top/Solenoid/Presentations.v builds
 the circle as an abelian group ([CircleGroup], on [circ_PropEquiv],
 with the p-th power map [circ_pow p] in [Ab]) and proves the covering
 property Riehl's name for the wrapping map asks for: every point has
 an evenly covered neighbourhood whose p sheets are each homeomorphic
 to it by the restriction of the map ([pwrap_evenly_covered] and
 [pwrap_sheet_iso] in [PTopCat], [wrap_evenly_covered] and
 [wrap_sheet_iso] in the Type-valued [Top]).

 NOT DELIVERED.  Complex numbers and any identification of R/Z with
 the unit circle of the plane; compactness, connectedness and
 metric-space structure (Instance/Met.v's [Met] is not used);
 covering-space theory beyond evenly covered neighbourhoods (path
 lifting, the fundamental group of the circle); continuity of the
 group operations, so no topological group; and any comparison of
 [Circle] and [PCircle] across the two encodings beyond their shared
 points and map (the tree has no functor between [Top] and
 [PTopCat]). 

 --------
 麦克莱恩，《为工作中的数学家而作的范畴论》，第2版（GTM 5），§V.1，书中第111页（PDF第120页），从页面图像阅读：在p进制螺线塔中“取每个对象F_n为一个圆S^1，并将每个箭头f_n：S^1 → S^1作为连续映射，使定义域圆S^1均匀地绕值域圆旋转p次”（目录ID maclane:V.1:construction3）
 赖尔，《范畴论的语境》，§3.6，例3.6.3，印刷页第116页（PDF第136)，从页面图像中读取：“每个生成映射都是‘p次幂映射’，覆盖映射将定义域圆均匀绕着值域圆绕 p 圈” （目录 ID riehl:3.6:example3） nLab:  https://ncatlab.org/nlab/show/solenoid nLab:  https://ncatlab.org/nlab/show/Cauchy+real+number Wikipedia:  https://en.wikipedia.org/wiki/Solenoid_(mathematics) Rocq 标准库：Reals/Cauchy/ConstructiveCauchyReals.v, ConstructiveCauchyRealsMult.v 和 ConstructiveCauchyAbs.v背景。该圆作为塔的对象进入树中。Mac Lane 的 §V.1 和 Riehl 的 §3.6 将 p 进制螺旋体构建为 Top 中圆的极限，在该映射下圆自身绕自身 p 次（Instance/Top/Solenoid.v）。两页都没有说明指的是哪种圆的模型。该文件采用标准模型，即模整数的实数直线，S^1 = R/Z，也就是问题 #410 自身文本中的“实数的商”。在 R/Z 上，Riehl 的“p 次幂映射”和 Mac Lane 的缠绕映射是同一个映射，即乘以 p：通过将 R/Z 与复平面上的单位圆通过 x ↦ e^(2πix) 识别之后，幂映射 z ↦ z^p 对应于 x ↦ p·x。nLab 的螺线管页面将二元情况写为 e^(iθ) ↦ e^(2iθ)，而维基百科的文章则将过渡映射描述为均匀地将一个圆圈绕到下一个圆圈上；在这些坐标下，它们都是同一个映射。与复数圆的对应只是背景：这棵树没有复数，而且下面没有使用它们的内容。哪些实数。树中已有的实数是标准库中的经典 [R]，并且它们包含公理：Instance/Top/Interval.v 中的 [I_Top] 打印 ClassicalDedekindReals.sig_forall_dec 和 FunctionalExtensionality.functional_extensionality_dep（在包含此文件和那个文件的临时文件中测量）。该文件改用标准库中的构造性 Cauchy 实数 [CReal]：一个由整数索引的有理数序列的记录 [seq]，并带有证明 [cauchy] 其以固定速率 2^k 收敛，以及一个界限；其顺序 [CRealLt] 是集合值的，其等式 [CRealEq] 是命题（库自身定义，见 ConstructiveCauchyReals.v）。这些是 nLab 所称的“调制”Cauchy 实数。[Print Assumptions] 打印“在全局上下文下关闭”，针对该文件的每一个 94 个常量，由 [Print Module] 列出，包括其九个 [Program] 义务。没有加载经典实数：一个临时文件 [Print Libraries] 需要 Instance/Top/Solenoid.v，列出了六个标准库实数模块，全部在 Reals/Cauchy 下（这里导入的三个、PosExtra、QExtra 和 ConstructiveExtra）。一个提醒，引用自 ConstructiveCauchyReals.v 的开头：“此模块不应直接导入，请改导入 `Reals.Abstract.ConstructiveReals`”，以及“此文件是实验性的，可能在未来版本中更改”。抽象接口没有命名 [CReal] 或其引理，而本文件需要它们，因此这三个模块被直接导入，在逻辑前缀下，树已经对标准库（Coq.Reals....）使用该前缀。该文件可以在 Rocq 9.1、Coq 8.19.2 和 Coq 8.20.1 上编译。这些点。[RLine_setoid] 在 [CRealEq] 下是 [CReal]。[Circle_setoid] 在 [circ_eq] 下是 [CReal]：当两个实数的差是一个整数时，它们是圆上的一个点，并且该整数被作为数据保留，[{ k : Z & x - y == k }]。圆上的球体 [cball] 以相同的方式携带它们的整数平移。原因是类型值的 [Top]：它的开集是类型值谓词，并且 [circle_open_balls] 的前半部分沿着整数平移 [y + k] 将开集中的一个点移动到这样的谓词内部，这需要 [k] 作为一个项；Coq 不会将一个存在命题的证明消去成一个类型。商映射 [circ_q] 在代表元上是恒等映射，并且 [circ_mul p] 在点上是 x ↦ p·x，这一点被下面的两个圆共享；它尊重 [circ_eq]，因为 p 乘以整数仍然是整数。平等性无疑仍然是一个命题。整数 a 是 [circ_eq] 所携带的证据，由两个点 ([circ_eq_witness_unique]) 决定。[circ_peq] 是在 [Prop] 中陈述的相同存在，而 [circ_eq_of_peq] 通过从实数计算整数回溯：[cround d] 是有理近似 [seq d (-4)] 的下取整加 1/2，[cround_between] 显示它对于每个距离整数 k 不超过 1/4 的实数都是 k，近似值在实数 [CRealLe_not_lt] 附近 1/8（精度 2^-4）；[cround_spec] 和 [cround_ball] 是使用的两种情况，一个实数等于 k，另一个实数与 k 的距离至多为 1/4。未使用选择公理。因此 [circ_PropEquiv] 是 [Circle_setoid] （Lib/Setoid/Propositional.v）中的 [PropEquiv]，字段是 [AbObject] 所依赖的；Instance/Top/Solenoid/Presentations.v 的圆群 [CircleGroup] 使用了它。[circle_lift_iso] 是 Instance/Sets/Classifier.v 的 lift [Setoid_Lift Circle_setoid@{o}] 和 [Circle_setoid@{h}] 之间在点上的恒等映射，这是 [Sets@{h hs}] 中的一个同构，Instance/Top/Forgetful.v 的 [Top_Forget] 所落入的范畴中。拓扑。直线的一个开集是一个谓词，其每个点内部都有一个闭有理球  [rball] ，度量拓扑：[ropen]，类型值，给出 [RLine : TopSpace]； [propen]，命题值，给出 [PRLine : PTop]。圆是在每个范畴中沿 [circ_q] 对直线取商：[Circle] 是 Instance/Top/Subspace/TypeValued.v 中的 [TQuot] 在 #259 的类型值 [Top] 上的实例，[PCircle] 是 Instance/Top/Subspace.v 中的 [PQuot] 在 [PTopCat] 上的实例。每个范畴构建一个圆，这两个圆共享其点和 p 倍映射。[circle_open_balls] 和 [pcircle_open_balls] 将每个商拓扑与圆自身的球拓扑在两个方向上识别，无需假设。p-倍映射  [wrap p] 和  [pwrap p] 由于商的泛性质（[tquot_desc]，[pquot_desc]）是连续的，因为在直线上的乘以 p 是连续的：[rball_mul] 将半径为 e/p 的球映射到半径为 e 的球。[cint] 是圆的闭球的内部；[cint_open]、[cint_centre] 和 [cint_sub] 是 Instance/Top/Solenoid.v 的 [Solenoid p] 以及 Instance/Top/Solenoid/Presentations.v 的球子空间 [CSub] 的泛性质决定的。关于假设，见第 [p : positive] 页，一个正整数。Mac Lane 的 p 是一个素数（书第 110 页，PDF 第 119 页：“p-进整数 Z_p（p 为素数）说明了这一构造”，该段紧接着是螺线段段落）；Riehl 的没有限定。此文件中没有使用素数性。使用的是 p 是一个整数，因此 [circ_mul] 尊重 [circ_eq]，并且它是正数，因此 [rball_mul] 的半径 e/p 是正的（[q_scale_pos]）。当 p = 1 时，映射卷绕在 [≈] 范围内是恒等的（[wrap_one]，[pwrap_one]）。优势。在 [eq_refl]：[Circle_points] 和 [PCircle_points]（每个圆的点为 [Circle_setoid]），[wrap_map] 和 [pwrap_map]（每个包装图的基础图为 [circ_mul p]）。[wrap_one] 和 [pwrap_one] 在 [Top] 和 [PTopCat] 的同值集上保持 [≈]：1·x 和 x 是相等的实数，[CReal_mult_1_l]，不可约换项。[circle_open_balls] 是一种类型值开放的 [iffT]，[pcircle_open_balls] 是一种命题值开放的 [iff]。[circle_half_not_zero] 否定 1/2 ≈ 0 在圆上，所以圆有两个不同的点；它通过 [creal_inject_Q_injective] 归约为整数中 1 = 2k。[circ_eq_witness_unique] 和三个四舍五入引理是整数的莱布尼茨相等式，[circle_lift_iso] 是一个在 [≈] 范围内法律成立的同构。Test/ProbeSolenoid410.v 针对 [wrap_one] 的边界：它的 N1 拒绝 [eq_refl] 对 [wrap 1] 的作用于某一点（"无法统一"），并且 [p410_wrap_one] 是其旁边的 [≈] 声明。UNIVERSES，由 [About] 在 [Set Printing Universes] 下阅读，对 [Print Module] 列表中的所有 94 个常数进行处理。- [@{}]（23 个常数）：有理数和实数算术，[posR]，[rball] 及其引理，带有三个引理的舍入 [cround]，以及 [circ_peq]。[@{u}]（15 个）：[circ_eq]，[cball] 及其引理，[circ_eq_witness_unique]，[circ_eq_of_peq] 以及 [circ_peq_of_eq]，[u] 整数証人的排序。[@{o}]（43 个）：等价类，两条线，[circ_q]，[circ_mul]，[Circle]，[PCircle]，[cint]，球的表征，[circle_half_not_zero] 和 [circ_PropEquiv]。[@{h o}]（5）与块 [o < h]: [line_mul_cont], [rline_mul], [wrap], [wrap_map], [wrap_one], [Top@{h o}] 的箭头，其霍姆位于点 (Instance/Top.v 的 [ContinuousMorphism_equiv]) 之上。[@{h o hs}]（5，[circle_lift_iso] 及其四个义务）与 [o < h] 和 [h < hs]，[Top_Forget] 块。[@{o so}]（3）与 [Set < so] 和 [o < so]: [pwrap], [pwrap_map], [pwrap_one], [PTopCat@{o so}] 块（Instance/Top/Prop.v 的标题）。- 没有块携带方程式，并且本文件的任何宇宙在 [Set] 被固定：圆和两条线在每个点宇宙 [o] 中存在。单词 [Set] 在输出中出现了 273 次：在三个 [pwrap] 块中以 [Set < so] 的形式出现了 3 次，其余仅作为标准库自身单态宇的严格下界出现，[Set < Basics.flip.u0]、[.u1] 和 [.u2] 出现在 61 个块中，[Set < Morphisms.Proper.u0] 和 [Set < Morphisms.Relations.u0] 出现在 37 个块中，[Set < Morphisms.GenericInstances.u0] 出现在 8 个块中，[Set < eq_ind_r.u0] 出现在 5 个块中。这些只将 [Set] 与全局宇相关联，并且不约束此文件的任何内容。按文件顺序，它们首先由 [creal_inject_Z_mult]（界限是 [flip]）、[inject_Q_minus_int_inv]（[Proper]、[Relations]）和 [cround_between]（[GenericInstances]、[eq_ind_r]）承载，每个都是 [rewrite]，在 [CRealEq]、[CRealLe] 或 [Qlt] 下；在草稿文件中，一行 [rewrite] 的 [CRealEq] 假设承载相同的 [flip]、[Proper] 和 [Relations] 界限，其证明项由 [iff_flip_impl_subrelation] 和 [PER_morphism] 构建，即命题上的广义重写组合子，其类型 [Prop] 的种类是 [Set+1]。- 剩余的上限是 [<=] ，它们是在全局宇宙上的界限，捐赠者在自己的区块中携带：[compose.u*] 和 [ID.u0] （Instance/Sets.v 的等价类映射，通过 [Top] 和 [PTopCat]）在 7 个区块中的 [o] 上，以及在 [circle_lift_iso] 的 5 个区块中的 [h] 上，以及 [projections.u0] 和 [.u1]（Instance/Top/Subspace/TypeValued.v 的 [TQuot]）在 11 个区块中的 [o] 上，以及在 3 个（[wrap]，[wrap_map]，[wrap_one]）中的 [h] 上。在其他地方交付。Instance/Top/Solenoid/Presentations.v 构建了圆作为阿贝尔群（[CircleGroup]，在 [circ_PropEquiv] 上，带有 p 次幂映射 [circ_pow p] 在 [Ab] 上）并证明了覆盖性质，这是 Riehl 所称的包装映射所要求的：每个点都有一个均匀覆盖的邻域，其 p 个层通过映射的限制（[pwrap_evenly_covered] 和 [pwrap_sheet_iso] 在 [PTopCat] 上，[wrap_evenly_covered] 和 [wrap_sheet_iso] 在类型值 [Top] 上）各自同胚于它。未交付。复数以及任何将 R/Z 与平面单位圆相对应的识别；紧性、连通性和度量空间结构（未使用 Instance/Met.v 的 [Met]）；覆盖空间理论超出均匀覆盖邻域的部分（路径提升，圆的基本群）；群运算的连续性，因此没有拓扑群；以及在两个编码之间对 [Circle] 和 [PCircle] 的任何比较，超出它们共享的点和映射（该树在 [Top] 和 [PTopCat] 之间没有函子）。
*)

#[local] Obligation Tactic := idtac.

(* * ** Arithmetic on the constructive reals / * ** 构造实数上的算术 *)

(* [inject_Q] reflects the order, so it is injective up to [Qeq]. / [inject_Q] 反映了顺序，因此它在 [Qeq] 上是单射的。 *)
Lemma creal_inject_Q_injective@{} (q r : Q) :
  CRealEq (inject_Q q) (inject_Q r) → Qeq q r.
Proof.
  intros [H1 H2]. apply Qle_antisym; apply le_inject_Q; assumption.
Qed.

Lemma inject_Q_pos_le@{} (e : Q) :
  Qlt 0 e → CRealLe (inject_Q 0) (inject_Q e).
Proof. intro H; apply inject_Q_le; apply Qlt_le_weak; exact H. Qed.

Lemma creal_inject_Z_mult@{} (a b : Z) :
  CRealEq (inject_Z (a * b)) (CReal_mult (inject_Z a) (inject_Z b)).
Proof. unfold inject_Z. rewrite <- inject_Q_mult. reflexivity. Qed.

(* A positive integer as a real, and its nonnegativity. / 一个正整数作为实数，以及它的非负性。 *)
Definition posR@{} (p : positive) : CReal := inject_Z (Zpos p).

Lemma posR_nonneg@{} (p : positive) : CRealLe (inject_Q 0) (posR p).
Proof. unfold posR, inject_Z. apply inject_Q_le. unfold Qle; simpl; lia. Qed.

(* The difference of two equal reals is the integer zero. / 两个相等实数的差是整数零。 *)
Lemma creal_minus_self@{} (x y : CReal) :
  CRealEq x y → CRealEq (CReal_minus x y) (inject_Z 0).
Proof.
  intro H. rewrite H. unfold inject_Z, CReal_minus. apply CReal_plus_opp_r.
Qed.

(*
 A difference of rationals is an integer [k] as reals exactly when it is
 one as rationals. 

 --------
 有理数的差作为实数恰好是整数 [k] 当且仅当它作为有理数时也是整数。
*)
Lemma inject_Q_minus@{} (a b : Q) :
  CRealEq (CReal_minus (inject_Q a) (inject_Q b)) (inject_Q (a - b)).
Proof.
  unfold CReal_minus, Qminus. rewrite inject_Q_plus, opp_inject_Q.
  reflexivity.
Qed.

Lemma inject_Q_minus_int@{} (a b : Q) (k : Z) :
  Qeq (a - b) (k # 1) →
  CRealEq (CReal_minus (inject_Q a) (inject_Q b)) (inject_Z k).
Proof.
  intro H. rewrite inject_Q_minus. unfold inject_Z.
  apply inject_Q_morph_T. exact H.
Qed.

Lemma inject_Q_minus_int_inv@{} (a b : Q) (k : Z) :
  CRealEq (CReal_minus (inject_Q a) (inject_Q b)) (inject_Z k) →
  Qeq (a - b) (k # 1).
Proof.
  intro H. rewrite inject_Q_minus in H. unfold inject_Z in H.
  exact (creal_inject_Q_injective _ _ H).
Qed.

Lemma creal_inject_Z_injective@{} (a b : Z) :
  CRealEq (inject_Z a) (inject_Z b) → a = b.
Proof.
  intro H. apply creal_inject_Q_injective in H. unfold Qeq in H; simpl in H.
  lia.
Qed.

(* * ** Rounding a real that lies near an integer / * ** 将接近整数的实数取整 *)

(*
 The integer nearest the rational approximation of [d] at precision
 2^-4.  It is a function of the representative, not of the real number;
 [cround_between] is what it computes on reals within 1/4 of an integer. 

 --------
 在精度 2^-4 下，[d] 的有理逼近最接近的整数。它是代表值的函数，而非实数的函数；[cround_between] 是它在距离整数 1/4 内的实数上计算的结果。
*)
Definition cround@{} (d : CReal) : Z := Qfloor (seq d (-4) + (1 # 2)).

Lemma cround_between@{} (d : CReal) (k : Z) :
  CRealLe (inject_Q ((k # 1) - (1 # 4))) d →
  CRealLe d (inject_Q ((k # 1) + (1 # 4))) →
  cround d = k.
Proof.
  intros Hlo Hhi.
  pose proof (proj2 (CRealLe_not_lt _ _) Hlo (-4)%Z) as Lo.
  pose proof (proj2 (CRealLe_not_lt _ _) Hhi (-4)%Z) as Hi.
  clear Hlo Hhi.
  cbn [seq inject_Q] in Lo, Hi.
  assert (E : (2 * 2 ^ (-4) == 1 # 8)%Q) by reflexivity.
  rewrite E in Lo, Hi.
  unfold cround.
  set (q := (seq d (-4) + (1 # 2))%Q).
  pose proof (Qfloor_le q) as F1. pose proof (Qlt_floor q) as F2.
  rewrite QArith_base.inject_Z_plus in F2.
  change (QArith_base.inject_Z 1) with 1%Q in F2.
  change (k # 1) with (QArith_base.inject_Z k) in Lo, Hi.
  assert (Hq : (q == seq d (-4) + (1 # 2))%Q) by reflexivity.
  clearbody q.
  set (K := QArith_base.inject_Z k) in *.
  set (Fl := QArith_base.inject_Z (Qfloor q)) in *.
  set (S := seq d (-4)) in *.
  assert (A1 : (Fl < K + 1)%Q) by lra.
  assert (A2 : (K < Fl + 1)%Q) by lra.
  change 1%Q with (QArith_base.inject_Z 1) in A1, A2.
  unfold K, Fl in A1, A2.
  rewrite <- QArith_base.inject_Z_plus, <- Zlt_Qlt in A1, A2. lia.
Qed.

Lemma cround_spec@{} (d : CReal) (k : Z) :
  CRealEq d (inject_Z k) → cround d = k.
Proof.
  intros [H1 H2]. apply cround_between.
  - apply (CRealLe_proper_r _ _ _ (CRealEq_sym _ _ (conj H1 H2))).
    apply inject_Q_le. unfold Qle; simpl. lia.
  - apply (CRealLe_proper_l _ _ _ (CRealEq_sym _ _ (conj H1 H2))).
    apply inject_Q_le. unfold Qle; simpl. lia.
Qed.

Lemma cround_ball@{} (d : CReal) (j : Z) :
  CRealLe (CReal_abs (CReal_minus d (inject_Z j))) (inject_Q (1 # 4)) →
  cround d = j.
Proof.
  intro H. apply CReal_abs_def2 in H. destruct H as [H1 H2].
  assert (E : CRealEq d
                (CReal_plus (inject_Z j) (CReal_minus d (inject_Z j))))
    by (unfold CReal_minus; ring).
  apply cround_between.
  - unfold Qminus. rewrite inject_Q_plus, opp_inject_Q.
    change (inject_Q (j # 1)) with (inject_Z j).
    rewrite E. apply CReal_plus_le_compat_l. exact H2.
  - rewrite inject_Q_plus. change (inject_Q (j # 1)) with (inject_Z j).
    rewrite E at 1. apply CReal_plus_le_compat_l. exact H1.
Qed.

(* * ** The line: points, closed rational balls, the metric topology / * ** 该行：点、闭有理球、度量拓扑 *)

Program Definition creal_setoid@{o} : Setoid@{o o} CReal :=
  {| equiv := CRealEq |}.
Next Obligation.
  constructor.
  - intro x; exact (CRealEq_refl x).
  - intros x y H; exact (CRealEq_sym x y H).
  - intros x y z H1 H2; exact (CRealEq_trans x y z H1 H2).
Qed.

Definition RLine_setoid@{o} : SetoidObject@{o o} :=
  {| carrier := CReal; is_setoid := creal_setoid@{o} |}.

(* The closed ball of rational radius [e] about [x]: |y - x| <= e. / 关于 [x] 的有理半径 [e] 的闭球：|y - x| <= e。 *)
Definition rball@{} (x y : CReal) (e : Q) : Prop :=
  CRealLe (CReal_abs (CReal_minus y x)) (inject_Q e).

Lemma rball_center@{} (x y : CReal) (e : Q) :
  Qlt 0 e → CRealEq x y → rball x y e.
Proof.
  intros He Hxy. unfold rball.
  assert (H0 : CRealEq (CReal_minus y x) (inject_Q 0)).
  { rewrite Hxy. unfold CReal_minus. apply CReal_plus_opp_r. }
  rewrite H0, (CReal_abs_right (inject_Q 0) (CRealLe_refl _)).
  exact (inject_Q_pos_le e He).
Qed.

Lemma rball_mono@{} (x y : CReal) (e e' : Q) :
  Qle e e' → rball x y e → rball x y e'.
Proof.
  intros H b. unfold rball in *. apply (CReal_le_trans _ (inject_Q e)).
  - exact b.
  - apply inject_Q_le; exact H.
Qed.

(*
 Multiplication by [p] carries a ball of radius [e/p] into one of
 radius [e]. 

 --------
 乘以 [p] 会将半径为 [e/p] 的球变为半径为 [e] 的球。
*)
Lemma rball_mul@{} (p : positive) (x y : CReal) (e : Q) :
  rball x y (e * (1 # p)) →
  rball (CReal_mult (posR p) x) (CReal_mult (posR p) y) e.
Proof.
  unfold rball; intro b.
  assert (E : CRealEq
    (CReal_minus (CReal_mult (posR p) y) (CReal_mult (posR p) x))
    (CReal_mult (posR p) (CReal_minus y x))).
  { unfold CReal_minus. ring. }
  rewrite E, CReal_abs_mult, (CReal_abs_right (posR p) (posR_nonneg p)).
  apply (CReal_le_trans _ (CReal_mult (posR p) (inject_Q (e * (1 # p))))).
  - apply CReal_mult_le_compat_l; [exact (posR_nonneg p)|exact b].
  - unfold posR, inject_Z. rewrite <- inject_Q_mult. apply inject_Q_le.
    destruct e as [n d]; cbv [Qle Qmult Qnum Qden].
    rewrite !Pos2Z.inj_mul; nia.
Qed.

Lemma q_half_pos@{} (d : Q) : Qlt 0 d → Qlt 0 (d * (1 # 2)).
Proof. intro H. apply Qmult_lt_0_compat; [exact H|reflexivity]. Qed.

Lemma q_half_half@{} (d : Q) : Qle (d * (1 # 2) + d * (1 # 2)) d.
Proof.
  destruct d as [n m]; cbv [Qle Qplus Qmult Qnum Qden].
  rewrite !Pos2Z.inj_mul; nia.
Qed.

Lemma q_scale_pos@{} (p : positive) (e : Q) : Qlt 0 e → Qlt 0 (e * (1 # p)).
Proof. intro H. apply Qmult_lt_0_compat; [exact H|reflexivity]. Qed.

(* The line over the Type-valued [Top]: an open is a predicate each of whose points has a closed rational ball inside it. / 类型值 [Top] 上的线：一个开集是一个谓词，其每个点内部都有一个封闭的有理球。 *)
Definition ropen@{o} (U : RLine_setoid@{o} → Type@{o}) : Type@{o} :=
  ∀ x, U x → { e : Q & (Qlt 0 e * ∀ y, rball x y e → U y)%type }.

Lemma ropen_respects@{o} (U V : RLine_setoid@{o} → Type@{o}) :
  (∀ x, U x ↔ V x) → ropen@{o} U → ropen@{o} V.
Proof.
  intros H HU x v. destruct (HU x (snd (H x) v)) as [e [He Hb]].
  exists e; split; [exact He|]. intros y b; exact (fst (H y) (Hb y b)).
Qed.

Lemma ropen_proper@{o} (U : RLine_setoid@{o} → Type@{o}) :
  ropen@{o} U → ∀ x y : RLine_setoid@{o}, x ≈ y → U x → U y.
Proof.
  intros HU x y Hxy u. destruct (HU x u) as [e [He Hb]].
  apply Hb, rball_center; [exact He|exact Hxy].
Qed.

Lemma ropen_union@{o} (I : Type@{o}) (U : I → (RLine_setoid@{o} → Type@{o})) :
  (∀ i, ropen@{o} (U i)) → ropen@{o} (fun x => { i : I & U i x }).
Proof.
  intros HU x [i u]. destruct (HU i x u) as [e [He Hb]].
  exists e; split; [exact He|]. intros y b. exact (i; Hb y b).
Qed.

Lemma ropen_whole@{o} : ropen@{o} (fun _ => poly_unit@{o}).
Proof. intros x _. exists 1%Q. split; [reflexivity|intros; exact ttt]. Qed.

Lemma ropen_inter@{o} (U V : RLine_setoid@{o} → Type@{o}) :
  ropen@{o} U → ropen@{o} V → ropen@{o} (fun x => U x ∧ V x).
Proof.
  intros HU HV x [u v].
  destruct (HU x u) as [e1 [He1 Hb1]], (HV x v) as [e2 [He2 Hb2]].
  destruct (Qlt_le_dec e1 e2) as [Hlt|Hle].
  - exists e1; split; [exact He1|]. intros y b; split.
    + exact (Hb1 y b).
    + apply Hb2, (rball_mono _ _ e1); [apply Qlt_le_weak; exact Hlt|exact b].
  - exists e2; split; [exact He2|]. intros y b; split.
    + apply Hb1, (rball_mono _ _ e2); [exact Hle|exact b].
    + exact (Hb2 y b).
Qed.

Definition RLine@{o} : TopSpace@{o} := {|
  top_carrier   := RLine_setoid@{o};
  IsOpen        := ropen@{o};
  open_respects := ropen_respects@{o};
  open_proper   := ropen_proper@{o};
  open_union    := ropen_union@{o};
  open_whole    := ropen_whole@{o};
  open_inter    := ropen_inter@{o}
|}.

(* The same line over [PTopCat]: the same balls, Prop-valued opens. / 相同的行在 [PTopCat] 上：相同的球，取值为 Prop 的开集。 *)
Definition propen@{o} (U : RLine_setoid@{o} → Prop) : Prop :=
  ∀ x, U x → ex (fun e : Q => Qlt 0 e /\ ∀ y, rball x y e → U y).

Lemma propen_respects@{o} (U V : RLine_setoid@{o} → Prop) :
  (∀ x, U x <-> V x) → propen@{o} U → propen@{o} V.
Proof.
  intros H HU x v. destruct (HU x (proj2 (H x) v)) as [e [He Hb]].
  exists e; split; [exact He|]. intros y b; exact (proj1 (H y) (Hb y b)).
Qed.

Lemma propen_proper@{o} (U : RLine_setoid@{o} → Prop) :
  propen@{o} U → ∀ x y : RLine_setoid@{o}, x ≈ y → U x → U y.
Proof.
  intros HU x y Hxy u. destruct (HU x u) as [e [He Hb]].
  apply Hb, rball_center; [exact He|exact Hxy].
Qed.

Lemma propen_union@{o} (F : (RLine_setoid@{o} → Prop) → Prop) :
  (∀ U, F U → propen@{o} U) →
  propen@{o} (fun x => ex (fun U => F U /\ U x)).
Proof.
  intros HF x [U [FU u]]. destruct (HF U FU x u) as [e [He Hb]].
  exists e; split; [exact He|]. intros y b.
  exists U; split; [exact FU|exact (Hb y b)].
Qed.

Lemma propen_whole@{o} : propen@{o} (fun _ => True).
Proof. intros x _. exists 1%Q. split; [reflexivity|intros; exact I]. Qed.

Lemma propen_inter@{o} (U V : RLine_setoid@{o} → Prop) :
  propen@{o} U → propen@{o} V → propen@{o} (fun x => U x /\ V x).
Proof.
  intros HU HV x [u v].
  destruct (HU x u) as [e1 [He1 Hb1]], (HV x v) as [e2 [He2 Hb2]].
  destruct (Qlt_le_dec e1 e2) as [Hlt|Hle].
  - exists e1; split; [exact He1|]. intros y b; split.
    + exact (Hb1 y b).
    + apply Hb2, (rball_mono _ _ e1); [apply Qlt_le_weak; exact Hlt|exact b].
  - exists e2; split; [exact He2|]. intros y b; split.
    + apply Hb1, (rball_mono _ _ e2); [exact Hle|exact b].
    + exact (Hb2 y b).
Qed.

Definition PRLine@{o} : PTop@{o} := {|
  pt_carrier     := RLine_setoid@{o};
  POpen          := propen@{o};
  popen_respects := propen_respects@{o};
  popen_proper   := propen_proper@{o};
  popen_union    := propen_union@{o};
  popen_whole    := propen_whole@{o};
  popen_inter    := propen_inter@{o}
|}.

(* * ** Multiplication by a positive integer, continuous on the line / * **乘以正整数，在直线上连续 *)

Program Definition line_mul@{o} (p : positive) :
  SetoidMorphism@{o o o} RLine_setoid@{o} RLine_setoid@{o} := {|
  morphism := fun x => CReal_mult (posR p) x
|}.
Next Obligation. intros p x y H; simpl in *. rewrite H. reflexivity. Qed.

Lemma line_mul_cont@{h o | o < h +} (p : positive) :
  Continuous@{h o} RLine@{o} RLine@{o} (line_mul@{o} p).
Proof.
  intros U HU x u. destruct (HU _ u) as [e [He Hb]].
  exists (e * (1 # p))%Q. split; [exact (q_scale_pos p e He)|].
  intros y b. apply Hb. exact (rball_mul p x y e b).
Qed.

Definition rline_mul@{h o | o < h +} (p : positive) :
  RLine@{o} ~{Top@{h o}}~> RLine@{o} :=
  @Build_ContinuousMorphism RLine RLine (line_mul p) (line_mul_cont p).

Lemma pline_mul_cont@{o} (p : positive) :
  @PCont PRLine@{o} PRLine@{o} (line_mul@{o} p).
Proof.
  intros U HU x u. destruct (HU _ u) as [e [He Hb]].
  exists (e * (1 # p))%Q. split; [exact (q_scale_pos p e He)|].
  intros y b. apply Hb. exact (rball_mul p x y e b).
Qed.

Definition prline_mul@{o} (p : positive) : PMor@{o} PRLine@{o} PRLine@{o} :=
  @Build_PMor PRLine PRLine (line_mul p) (pline_mul_cont p).

(* * ** The circle's points: the line modulo the integers / * ** 圆的点：线的整数模 *)

(* Two reals are the same point of the circle when their difference is an integer; the integer is kept as data. / 当两个实数的差是整数时，它们是同一个圆上的点；这个整数被作为数据保留。 *)
Definition circ_eq@{u} (x y : CReal) : Type@{u} :=
  { k : Z & CRealEq (CReal_minus x y) (inject_Z k) }.

Lemma circ_eq_refl@{u} (x : CReal) : circ_eq@{u} x x.
Proof.
  exists 0%Z. apply creal_minus_self. apply CRealEq_refl.
Qed.

Lemma circ_eq_sym@{u} (x y : CReal) : circ_eq@{u} x y → circ_eq@{u} y x.
Proof.
  intros [k Hk]. exists (- k)%Z. rewrite opp_inject_Z, <- Hk.
  unfold CReal_minus. ring.
Qed.

Lemma circ_eq_trans@{u} (x y z : CReal) :
  circ_eq@{u} x y → circ_eq@{u} y z → circ_eq@{u} x z.
Proof.
  intros [k1 H1] [k2 H2]. exists (k1 + k2)%Z.
  rewrite inject_Z_plus, <- H1, <- H2. unfold CReal_minus. ring.
Qed.

Lemma circ_eq_of_creal@{u} (x y : CReal) : CRealEq x y → circ_eq@{u} x y.
Proof. intro H. exists 0%Z. exact (creal_minus_self x y H). Qed.

Program Definition circ_setoid@{o} : Setoid@{o o} CReal :=
  {| equiv := circ_eq@{o} |}.
Next Obligation.
  constructor.
  - exact circ_eq_refl.
  - exact circ_eq_sym.
  - exact circ_eq_trans.
Qed.

Definition Circle_setoid@{o} : SetoidObject@{o o} :=
  {| carrier := CReal; is_setoid := circ_setoid@{o} |}.

(* The quotient map: the identity on representatives. / 商映射：代表元上的恒等映射。 *)
Program Definition circ_q@{o} :
  SetoidMorphism@{o o o} RLine_setoid@{o} Circle_setoid@{o} := {|
  morphism := fun x => x
|}.
Next Obligation. intros x y H. exact (circ_eq_of_creal x y H). Qed.

(* The p-fold map on points, shared by both circles below. / 下面两个圆共有的点上的 p 重映射。 *)
Program Definition circ_mul@{o} (p : positive) :
  SetoidMorphism@{o o o} Circle_setoid@{o} Circle_setoid@{o} := {|
  morphism := fun x => CReal_mult (posR p) x
|}.
Next Obligation.
  intros p x y [k Hk]. exists (Zpos p * k)%Z.
  rewrite creal_inject_Z_mult, <- Hk. unfold posR, CReal_minus. ring.
Qed.

(* * ** The circle's equality is propositional / * ** 圆的等同性是命题性的 *)

(* The integer a witness of [circ_eq] carries is determined by the two points: two witnesses of one equation carry the same integer. / 整数 a 是 [circ_eq] 的一个见证，它由两个点决定：一个方程的两个见证携带相同的整数。 *)
Lemma circ_eq_witness_unique@{u} (x y : CReal) (a b : circ_eq@{u} x y) :
  projT1 a = projT1 b.
Proof.
  destruct a as [k Hk], b as [l Hl]. cbn [projT1].
  apply creal_inject_Z_injective. rewrite <- Hk, <- Hl. reflexivity.
Qed.

Definition circ_peq@{} (x y : CReal) : Prop :=
  ex (fun k : Z => CRealEq (CReal_minus x y) (inject_Z k)).

(* The integer is recomputed from the real by [cround]; no choice. / 整数通过 [cround] 从实数重新计算；没有选择。 *)
Lemma circ_eq_of_peq@{u} (x y : CReal) : circ_peq x y → circ_eq@{u} x y.
Proof.
  intro H. exists (cround (CReal_minus x y)).
  destruct H as [k Hk]. rewrite (cround_spec _ _ Hk). exact Hk.
Qed.

Lemma circ_peq_of_eq@{u} (x y : CReal) : circ_eq@{u} x y → circ_peq x y.
Proof. intros [k Hk]. exact (ex_intro _ k Hk). Qed.

Definition circ_PropEquiv@{o} :
  PropEquiv@{o o} (is_setoid Circle_setoid@{o}) :=
  @PropEquiv_of_relation _ (is_setoid Circle_setoid@{o}) circ_peq
    circ_eq_of_peq@{o} circ_peq_of_eq@{o}.

(* The circle's own balls: [y] lies within [e] of [x] up to an integer translate, the integer again kept as data. / 圆自身的球：[y] 位于 [e] 的 [x] 内，直到一个整数的转换，该整数再次作为数据保留。 *)
Definition cball@{u} (x y : CReal) (e : Q) : Type@{u} :=
  { k : Z & CRealLe
      (CReal_abs (CReal_plus (CReal_minus y x) (inject_Z k))) (inject_Q e) }.

Lemma cball_of_rball@{u} (x y : CReal) (e : Q) :
  rball x y e → cball@{u} x y e.
Proof.
  intro b. exists 0%Z. unfold rball in b.
  assert (E : CRealEq (CReal_plus (CReal_minus y x) (inject_Z 0))
                      (CReal_minus y x)).
  { unfold inject_Z. ring. }
  rewrite E. exact b.
Qed.

(* A ball of the circle is a ball of the line about a translate. / 圆的球是关于平移的直线的球。 *)
Lemma rball_of_cball@{} (x y : CReal) (e : Q) (k : Z) :
  CRealLe (CReal_abs (CReal_plus (CReal_minus y x) (inject_Z k)))
          (inject_Q e) →
  rball x (CReal_plus y (inject_Z k)) e.
Proof.
  intro b. unfold rball.
  assert (E : CRealEq (CReal_minus (CReal_plus y (inject_Z k)) x)
                      (CReal_plus (CReal_minus y x) (inject_Z k))).
  { unfold CReal_minus. ring. }
  rewrite E. exact b.
Qed.

Lemma circ_eq_translate@{u} (y : CReal) (k : Z) :
  circ_eq@{u} (CReal_plus y (inject_Z k)) y.
Proof.
  exists k. unfold CReal_minus. ring.
Qed.

Lemma cball_of_eq@{u} (x y : CReal) (e : Q) :
  Qlt 0 e → circ_eq@{u} x y → cball@{u} x y e.
Proof.
  intros He [k Hk]. exists k.
  assert (E : CRealEq (CReal_plus (CReal_minus y x) (inject_Z k))
                      (inject_Q 0)).
  { rewrite <- Hk. unfold CReal_minus. ring. }
  rewrite E, (CReal_abs_right (inject_Q 0) (CRealLe_refl _)).
  exact (inject_Q_pos_le e He).
Qed.

Lemma cball_mono@{u} (x y : CReal) (e e' : Q) :
  Qle e e' → cball@{u} x y e → cball@{u} x y e'.
Proof.
  intros H [k b]. exists k. apply (CReal_le_trans _ (inject_Q e)).
  - exact b.
  - apply inject_Q_le; exact H.
Qed.

Lemma cball_triang@{u} (x y z : CReal) (a b : Q) :
  cball@{u} x y a → cball@{u} y z b → cball@{u} x z (a + b).
Proof.
  intros [k1 H1] [k2 H2]. exists (k1 + k2)%Z.
  assert (E : CRealEq (CReal_plus (CReal_minus z x) (inject_Z (k1 + k2)))
    (CReal_plus (CReal_plus (CReal_minus y x) (inject_Z k1))
                (CReal_plus (CReal_minus z y) (inject_Z k2)))).
  { rewrite inject_Z_plus. unfold CReal_minus. ring. }
  rewrite E, inject_Q_plus.
  apply (CReal_le_trans _ _ _ (CReal_abs_triang _ _)).
  apply CReal_plus_le_compat; [exact H1|exact H2].
Qed.

Lemma cball_mul@{u} (p : positive) (x y : CReal) (e : Q) :
  cball@{u} x y (e * (1 # p)) →
  cball@{u} (CReal_mult (posR p) x) (CReal_mult (posR p) y) e.
Proof.
  intros [k b]. exists (Zpos p * k)%Z.
  assert (E : CRealEq
    (CReal_plus (CReal_minus (CReal_mult (posR p) y) (CReal_mult (posR p) x))
                (inject_Z (Zpos p * k)))
    (CReal_mult (posR p) (CReal_plus (CReal_minus y x) (inject_Z k)))).
  { rewrite creal_inject_Z_mult. unfold posR, CReal_minus. ring. }
  rewrite E, CReal_abs_mult, (CReal_abs_right (posR p) (posR_nonneg p)).
  apply (CReal_le_trans _ (CReal_mult (posR p) (inject_Q (e * (1 # p))))).
  - apply CReal_mult_le_compat_l; [exact (posR_nonneg p)|exact b].
  - unfold posR, inject_Z. rewrite <- inject_Q_mult. apply inject_Q_le.
    destruct e as [n d]; cbv [Qle Qmult Qnum Qden].
    rewrite !Pos2Z.inj_mul; nia.
Qed.

(* * ** The circle over [Top]: the quotient topology of the line / * ** [Top] 上的圆圈：直线的商拓扑 *)

Definition Circle@{o} : TopSpace@{o} :=
  TQuot@{o} RLine@{o} Circle_setoid@{o} circ_q@{o}.

Example Circle_points@{o} : top_carrier Circle@{o} = Circle_setoid@{o} :=
  eq_refl.

(* The ball topology of the circle, Type-valued. / 圆的球拓扑，类型值。 *)
Definition cball_open@{o} (V : Circle_setoid@{o} → Type@{o}) : Type@{o} :=
  ∀ x, V x → { e : Q & (Qlt 0 e * ∀ y, cball@{o} x y e → V y)%type }.

(* The quotient topology IS the ball topology: both directions. / 商拓扑就是球拓扑：两个方向都成立。 *)
Lemma circle_open_balls@{o} (V : Circle_setoid@{o} → Type@{o}) :
  IsOpen Circle@{o} V ↔ cball_open@{o} V.
Proof.
  split.
  - intros [Hp Ho] x v. destruct (Ho x v) as [e [He Hb]].
    exists e; split; [exact He|]. intros y [k b].
    apply (Hp (CReal_plus y (inject_Z k)) y (circ_eq_translate y k)).
    exact (Hb _ (rball_of_cball x y e k b)).
  - intro HV; split.
    + intros t t' e v. destruct (HV t v) as [d [Hd Hb]].
      exact (Hb t' (cball_of_eq t t' d Hd e)).
    + intros x v. destruct (HV x v) as [e [He Hb]].
      exists e; split; [exact He|]. intros y b.
      exact (Hb y (cball_of_rball x y e b)).
Qed.

(*
 The interior of a closed ball: the points having a smaller ball inside
 it.  It is open, it contains the centre and it lies in the ball; the
 solenoid's universal property (Instance/Top/Solenoid.v) turns on it. 

 --------
 闭球的内部：含有一个更小球在其内部的点。它是开集，包含中心点，并且位于该球内；螺线管的泛性质（Instance/Top/Solenoid.v）依赖于它。
*)
Definition cint@{o} (c : CReal) (e : Q) (y : Circle_setoid@{o}) : Type@{o} :=
  { d : Q & (Qlt 0 d * ∀ y', cball@{o} y y' d → cball@{o} c y' e)%type }.

Lemma cint_balls@{o} (c : CReal) (e : Q) : cball_open@{o} (cint@{o} c e).
Proof.
  intros y [d [Hd H]]. exists (d * (1 # 2))%Q.
  split; [exact (q_half_pos d Hd)|].
  intros y' b. exists (d * (1 # 2))%Q. split; [exact (q_half_pos d Hd)|].
  intros y'' b'. apply H. apply (cball_mono _ _ _ _ (q_half_half d)).
  exact (cball_triang _ _ _ _ _ b b').
Qed.

Lemma cint_open@{o} (c : CReal) (e : Q) : IsOpen Circle@{o} (cint@{o} c e).
Proof. exact (snd (circle_open_balls _) (cint_balls c e)). Qed.

Lemma cint_centre@{o} (c : CReal) (e : Q) : Qlt 0 e → cint@{o} c e c.
Proof. intro He. exists e. split; [exact He|]. intros y' b; exact b. Qed.

Lemma cint_sub@{o} (c : CReal) (e : Q) (y : CReal) :
  cint@{o} c e y → cball@{o} c y e.
Proof.
  intros [d [Hd H]]. apply H. exact (cball_of_eq y y d Hd (circ_eq_refl y)).
Qed.

(*
 The map wrapping the circle p times around itself: continuous because
 multiplication by [p] is continuous on the line, by the quotient's
 universal property (Instance/Top/Subspace/TypeValued.v's
 [tquot_desc]). 

 --------
 将圆包裹自身 p 次的映射：连续，因为在直线上乘以 [p] 是连续的，通过商的泛性质（Instance/Top/Subspace/TypeValued.v 的 [tquot_desc]）。
*)
Definition wrap@{h o | o < h +} (p : positive) :
  Circle@{o} ~{Top@{h o}}~> Circle@{o} :=
  tquot_desc RLine Circle_setoid circ_q Circle
    (top_compose (tquot_proj RLine Circle_setoid circ_q) (rline_mul p))
    (circ_mul p) (fun x => circ_eq_refl _).

Example wrap_map@{h o | o < h +} (p : positive) :
  continuous_map (wrap@{h o} p) = circ_mul@{o} p := eq_refl.

(* At p = 1 the wrapping map is the identity. / 当 p = 1 时，包裹映射是恒等映射。 *)
Lemma wrap_one@{h o | o < h +} : wrap@{h o} 1 ≈ @id Top@{h o} Circle@{o}.
Proof. intro x. apply circ_eq_of_creal. exact (CReal_mult_1_l x). Qed.

(* * ** The circle over [PTopCat]: the same quotient, Prop-valued / * ** [PTopCat] 上的圈：相同的商，命题值 *)

Definition PCircle@{o} : PTop@{o} :=
  PQuot@{o} PRLine@{o} Circle_setoid@{o} circ_q@{o}.

Example PCircle_points@{o} : pt_carrier PCircle@{o} = Circle_setoid@{o} :=
  eq_refl.

Definition pcball_open@{o} (V : Circle_setoid@{o} → Prop) : Prop :=
  ∀ x, V x → ex (fun e : Q => Qlt 0 e /\ ∀ y, cball@{o} x y e → V y).

Lemma pcircle_open_balls@{o} (V : Circle_setoid@{o} → Prop) :
  POpen PCircle@{o} V <-> pcball_open@{o} V.
Proof.
  split.
  - intros [Hp Ho] x v. destruct (Ho x v) as [e [He Hb]].
    exists e; split; [exact He|]. intros y [k b].
    apply (Hp (CReal_plus y (inject_Z k)) y (circ_eq_translate y k)).
    exact (Hb _ (rball_of_cball x y e k b)).
  - intro HV; split.
    + intros t t' e v. destruct (HV t v) as [d [Hd Hb]].
      exact (Hb t' (cball_of_eq t t' d Hd e)).
    + intros x v. destruct (HV x v) as [e [He Hb]].
      exists e; split; [exact He|]. intros y b.
      exact (Hb y (cball_of_rball x y e b)).
Qed.

Definition pwrap@{o so | o < so +} (p : positive) :
  PCircle@{o} ~{PTopCat@{o so}}~> PCircle@{o} :=
  pquot_desc PRLine Circle_setoid circ_q PCircle
    (pcompose (pquot_proj PRLine Circle_setoid circ_q) (prline_mul p))
    (circ_mul p) (fun x => circ_eq_refl _).

Example pwrap_map@{o so | o < so +} (p : positive) :
  pmap (pwrap@{o so} p) = circ_mul@{o} p := eq_refl.

Lemma pwrap_one@{o so | o < so +} :
  pwrap@{o so} 1 ≈ @id PTopCat@{o so} PCircle@{o}.
Proof. intro x. apply circ_eq_of_creal. exact (CReal_mult_1_l x). Qed.

(* * ** Two points of the circle that differ / * ** 圆上两个不同的点 *)

Lemma circle_half_not_zero@{o} :
  @equiv _ Circle_setoid@{o} (inject_Q (1 # 2)) (inject_Q 0) → False.
Proof.
  intros [k Hk]. apply inject_Q_minus_int_inv in Hk.
  unfold Qeq, Qminus, Qplus in Hk; simpl in Hk. lia.
Qed.

(** ** The circle's points, lifted / ** 圆上的点，被抬起 *)

(*
 Instance/Top/Forgetful.v's [Top_Forget] lands in the lifted
 [Sets@{h hs}], where the points of [Circle@{o}] are the lifted
 [Circle_setoid@{o}]; they are the circle's points taken at [h], by the
 identity maps. 

 --------
 Instance/Top/Forgetful.v 的 [Top_Forget] 落在提升的 [Sets@{h hs}] 中，[Circle@{o}] 的点是提升的 [Circle_setoid@{o}]；它们是圆在 [h] 处取的点，由恒等映射得到。
*)
Program Definition circle_lift_iso@{h o hs | o < h, h < hs +} :
  @Isomorphism Sets@{h hs} (Setoid_Lift@{o h} Circle_setoid@{o})
    Circle_setoid@{h} := {|
  to := {| morphism := fun x : CReal => x |};
  from := {| morphism := fun x : CReal => x |}
|}.
Next Obligation. intros x y [k Hk]. exact (k; Hk). Qed.
Next Obligation. intros x y [k Hk]. exact (k; Hk). Qed.
Next Obligation. intro x. apply circ_eq_refl. Qed.
Next Obligation. intro x. apply circ_eq_refl. Qed.
