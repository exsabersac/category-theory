Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyReals.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyRealsMult.
Require Import Coq.Reals.Cauchy.ConstructiveCauchyAbs.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.InverseLimit.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Complete.
Require Import Category.Instance.Top.Subspace.TypeValued.
Require Import Category.Instance.Top.Circle.

Generalizable All Variables.

(** * The p-adic solenoid / * p进数螺旋体 *)

(*
 Mac Lane, “Categories for the Working Mathematician”, 2nd ed. (GTM 5),
 §V.1, book p. 111 (PDF p. 120), read from the page image (catalog id
 maclane:V.1:construction3):
 “Again, in Top, take each object F_n to be a circle S^1, and each
 arrow f_n : S^1 → S^1 to be the continuous map wrapping the domain
 circle S^1 uniformly p times around the codomain circle.  The
 inverse limit set L then becomes a topological space when we
 introduce just those open sets in L necessary to make all the
 functions μ_n : L → S^1 continuous.  This L is the limit space in
 Top; it is known as the p-adic solenoid.”
 Riehl, “Category Theory in Context”, §3.6, Example 3.6.3, printed
 p. 116 (PDF p. 136), read from the page image (catalog id
 riehl:3.6:example3):
 “Any limit or colimit in Top can be constructed in the way
 prescribed in the proof of Proposition 3.6.2: by forming the limit
 or colimit of the diagram of underlying sets and then topologizing
 the resulting space with the coarsest (in the case of limits) or
 finest (in the case of colimits) topologies so that the legs of the
 limit or colimit cones are continuous.  For instance, consider the
 diagram ω^op → Top whose objects are circles S^1 and in which each
 generating map is the ”pth power map,“ the covering map that wraps
 the domain circle uniformly p times around the codomain circle:
 ... The inverse limit defines the p-adic solenoid.”
 nLab: https://ncatlab.org/nlab/show/solenoid
 nLab: https://ncatlab.org/nlab/show/initial+topology
 Wikipedia: https://en.wikipedia.org/wiki/Solenoid_(mathematics)

 BACKGROUND.  Solenoids were introduced by Vietoris in the dyadic case
 and by van Dantzig in general (Wikipedia).  They are compact
 metrizable spaces that are connected but neither locally connected
 nor path connected, one-dimensional homogeneous indecomposable
 continua that carry the structure of an abelian topological group
 (Wikipedia).  In dynamics a solenoid arises as the Smale-Williams
 attractor, a one-dimensional expanding attractor of hyperbolic
 systems (Wikipedia); in shape theory nLab records the solenoids as
 examples of non-stable spaces.  For both books the solenoid is an
 example of another kind: a limit of spaces whose topology is not
 given but forced, Mac Lane's “just those open sets in L necessary”,
 Riehl's “coarsest ... topologies so that the legs ... are
 continuous”, the initial topology of nLab's page.  In the tree its
 points are #408's matching strings (Instance/Sets/InverseLimit.v's
 [inverse_limit]), the recipe is #458's (Instance/Top/Complete.v's
 [PTop_Limit_lift]), the circle and its p-fold map are
 Instance/Top/Circle.v's, and the example that precedes it on Mac
 Lane's page, the p-adic integers as the limit of the rings Z/p^nZ, is
 Instance/Rng/Zp.v's [Zp_limit].

 THE ISSUE'S SURVEY IS STALE, re-measured on this tree.  “There is no
 category of topological spaces in the tree” is false:
 Instance/Top.v's [Top] (#259) and Instance/Top/Prop.v's [PTopCat].
 “rg -i 'coarsest|initial topology' ... return nothing usable” is
 false: Instance/Top/Complete.v's [PInit], [pinit_universal] and
 [pinit_weakest] are the initial topology and its universal property.
 The dependencies #408 and #458 have landed.  The appended Riehl item
 describes Riehl's presentation as “a diagram of covering maps rather
 than as a limit of the p-adic groups”; the page quoted above presents
 Mac Lane's solenoid as a limit of circles, the p-adic integers being
 the separate example that precedes it.  That phrase is the issue
 text's own: both books give the one diagram built here.

 THE TOWERS.  [EndoTower X w] is the tower ... → X → X → X of an
 endomorphism [w] in ANY category, a functor out of [Omega^op]; it
 sends a proof of m <= n to the (n - m)-fold composite of [w]
 ([endo_hom], Instance/Rng/Zp.v's [res_hom] idiom).  [endo_step]
 reads the generating arrow back as [id ∘ w] at [eq_refl], and
 [EndoTower_map] shows a functor carries the tower of [w] to the
 tower of [fmap w], in [Functor_Setoid], with identity components.
 The three towers of circles are [UCircleTower p] in [Sets], of
 Instance/Top/Circle.v's [circ_mul p]; [CircleTower p] in the
 Type-valued [Top], of [wrap p], Mac Lane's tower; and
 [PCircleTower p] in [PTopCat], of [pwrap p].
 [PCircleTower_points] identifies the underlying tower of the last
 with the first.  Statements write [omega_step n] where
 Instance/Sets/InverseLimit.v writes [tower_step n]; the two are one
 term ([tower_step_is_omega_step]).  [About] shows
 [tower_step@{u u0 u1 u2 u3}] with a type naming only [u2] and [u3]:
 the other three carry the block of that file's section
 [Context (F : Omega^op ⟶ Sets)] ([u0 < u1] and [Sets]' caps), and a
 statement with a closed universe list cannot bind them: the readback
 of [CircleTower_step] through [tower_step] under the closed list
 [@{s h o | o < h}] is refused, “Universes ... are unbound”
 (Test/ProbeSolenoid410.v's N6), and accepted with an extensible list
 (its [p410_tower_step]).

 THE SOLENOID IN THE TYPE-VALUED [Top], the issue's category and its
 pinned name: [solenoid_limit p : Limit (CircleTower p)].  The generic
 recipe does not reach this category.  The initial topology of a
 nat-indexed family of maps into spaces is refused at the points'
 universe in both Type-valued forms tried.  The first says V is open
 when it lies in EVERY family T of predicates on the points that
 contains the preimages of the factors' opens.  It asks no closure
 property of T, so it is not itself the intersection of all
 topologies containing those preimages; it is the quantification that
 intersection needs, over T of type (S → Type@{o}) → Type@{o}, and
 adding the closure properties to the hypothesis on T would not lower
 its universe (argued: the refusal prints the form's type as
 [Type@{max(o+1,...)}], and o+1 is the universe of T's type).  The
 second says every point of V has a factor, an open of that factor
 around its image, and the whole preimage of that open inside V; it
 quantifies over the opens of the factors.  Both are refused, “Cannot
 enforce o < o” (Test/ProbeSolenoid410.v's N2 and N3), and both are
 accepted one universe up (its [p410_init_family_up] and
 [p410_init_union_up]).
 The solenoid's own topology avoids the refusal: [sopen] quantifies
 over a stage [n : nat] and a rational radius [e], never over opens,
 so it sits at [Type@{o}].  A predicate [V] on the matching strings
 [SolPoints p] is open when every point [s] of [V] has a stage [n] and
 a radius [e > 0] such that every string within [e] of [s], on the
 circle's balls [cball], at every stage [j <= n], lies in [V].  The
 topology is not posited but characterised.  [solenoid_universal]: a
 setoid map from ANY space into the points is continuous iff every
 composite with a projection is.  [solenoid_coarsest]: every topology
 on the points (given by the closure properties of Instance/Top.v's
 [TopSpace]) in which each projection is continuous contains every
 open of [Solenoid p].  With [sol_leg_cont], by which the preimage of
 every open of the circle along a projection is in [sopen], it is
 exactly the coarsest topology making the legs continuous, Mac Lane's
 “just those open sets ... necessary”.
 The content is [sol_lift_cont]: the preimage of an open [W] along a
 map [g] is the union, over the points of [W ∘ g], of finite
 intersections ([open_bounded_inter]) of preimages of the open
 interiors of the circle's balls (Instance/Top/Circle.v's [cint_open]).
 The limit's mediator [sol_med] is the tuple of a competing cone's
 legs, continuous by [sol_lift_cont]; uniqueness is pointwise.
 [solenoid_forget_preserves]: [Top_Forget] preserves the limit cone.
 [Top_Forget] lands in the lifted [Sets@{h hs}], and
 Instance/Top/Forgetful.v's header records that cone-level
 preservation for that lifted functor is “neither claimed nor
 concluded” there, its competitors having big vertices; at this tower
 it holds directly, the mediator being the tuple of legs into the
 lifted points.

 THE SOLENOID IN [PTopCat], by #458's recipe, which is Riehl's
 sentence: [PTop_solenoid_limit p] is [PTop_Limit_lift] of the
 matching-strings limit [Sets_tower_Limit] of the underlying tower.
 Its characterisations are #458's general theorems at this tower:
 [PTop_solenoid_universal] ([pinit_universal]),
 [PTop_solenoid_coarsest] ([pinit_weakest]),
 [PTop_solenoid_open_forced] (every limiting cone over the tower
 carries the initial topology for its legs,
 [PTop_limit_open_iff_initial]) and [PTop_solenoid_forget_preserves]
 ([PForget_PreservesLimitCone], through the adjunction [PDisc_PForget]).
 The name follows #458's convention of [PTop_*] names for readings over
 [PTopCat] beside the pinned Type-valued name.

 THE POINTS, at [eq_refl].  [solenoid_points] and
 [PTop_solenoid_points]: the points of each limit ARE #408's matching
 strings, [inverse_limit] of the underlying tower; [solenoid_leg_map]
 and [PTop_solenoid_leg_map]: the legs ARE its projections
 [tower_proj]; [sol_compat]: the matching condition IS
 (∀ n, circ_eq (p · x (S n)) (x n)), Mac Lane's string condition
 read on the circle; [solenoid_points_agree]: the two limits have the
 same type of points.  As setoid objects the two point sets are not
 equal at [eq_refl]: Instance/Sets/InverseLimit.v's [tower_obj] builds
 its setoid by a [Qed] [Program] obligation applied to the functor,
 and the two underlying towers are different terms; the equation is
 refused (“cannot unify”, Test/ProbeSolenoid410.v's N4).  That is the
 donor's opacity and nothing more: the probe's [p410_tower_obj], the
 donor's definition closed [Defined], accepts [eq_refl] for the two
 towers ([p410_flip_ptop]).

 p, AND WHAT p = 1 GIVES.  [p : positive]; Mac Lane's p is a prime
 (book p. 110), Riehl's is not qualified, and nothing here uses
 primality.  No construction and no characterisation above uses any
 hypothesis on p.  Non-vacuity holds at every p:
 [solenoid_two_points] refutes the zero string ≈ the string
 (1/(2p^n))_n, whose stage-0 entries 0 and 1/2 differ on the circle,
 and [PTop_solenoid_two_points] gives the same two points of
 [PSolenoid p].  The only hypothesis in the file, [1 < p], is used
 once: [unit_string_not_zero] refutes the string (1/p^n)_n ≈ the zero
 string, while [unit_string_over_zero] puts both over the same point at
 stage 0, so for 1 < p the leg μ_0 identifies two distinct points.  At
 p = 1 the tower is the identity up to [≈] (Instance/Top/Circle.v's
 [wrap_one]) and the solenoid is isomorphic to the circle:
 [solenoid_one_iso] and [PTop_solenoid_one_iso] are isomorphisms in
 [Top] and [PTopCat] whose forward arrow is the leg μ_0 and whose
 inverse sends a point to its constant string.

 STRENGTHS.  At [eq_refl]: [endo_step], [CircleTower_step],
 [PCircleTower_step], [sol_compat], [solenoid_points],
 [solenoid_leg_map], [PTop_solenoid_points], [PTop_solenoid_leg_map],
 [solenoid_points_agree] and [half_string_coord].  Up to [≈]:
 [endo_step_equiv], [EndoTower_map] and [PCircleTower_points] (in
 [Functor_Setoid]), the iso laws of [solenoid_one_iso] and
 [PTop_solenoid_one_iso].  [endo_step] is [id ∘ w], not [w]: the
 equation with [w] is refused at [eq_refl] in an arbitrary category
 (Test/ProbeSolenoid410.v's N5).  As [iffT] and [iff]:
 [solenoid_universal], [PTop_solenoid_universal],
 [PTop_solenoid_open_forced].  [PTop_solenoid_two_points] is closed
 [Defined], so its two witnesses read back: its first projection IS
 [zero_string p] (the probe's [p410_two_points_first]).  [Print
 Assumptions] prints “Closed under the global context” for all 78
 constants of the [Print Module] listing, six [Program] obligations
 included, and for all 94 of Instance/Top/Circle.v.

 UNIVERSES, read by [About] under [Set Printing Universes] on the 78
 constants.  [EndoTower@{s o h}] takes [C : Category@{o h h}] and
 returns [Omega@{s h h}^op ⟶ C]; the solenoid constants are
 [@{s o so}] for the points and their topology, [@{s o so h}] for
 what mentions [Top@{h o}], [solenoid_limit@{s o so h r}] with its
 [Limit@{r s h h}], and [PTop_solenoid_limit@{s o so r}] with
 [Limit@{r s o so}]; statement-only lemmas carry the auxiliaries of
 [Compose], [iffT] and [IsLimitCone] besides.
 - No block carries an equation, and no universe is pinned at [Set]:
 both solenoids exist at every points universe [o].
 - Strict bounds among this file's universes: [o < h] (23 blocks,
 [Top]'s own), [o < so] (60, [Sets]' and [PTopCat]'s), [h < hs]
 (3, [Top_Forget]'s), and [o < u*] or [h < u1] in six constants,
 five whose statements compose functors ([EndoTower_map],
 [PCircleTower_points], [PTop_solenoid_points],
 [PTop_solenoid_open_forced], [PTop_solenoid_forget_preserves])
 and [PTop_solenoid_two_points], whose [Defined] body brings the
 bound with two auxiliaries (the same statement closed [Qed] in a
 scratch copy reads [@{s o so u}] without it): [Compose]'s own
 bound of the hom universe below an auxiliary ([About Compose]:
 u3 < u2).
 - [PTop_solenoid_limit] instantiates [PTop_Limit_lift] with its
 input and output limit universes both [r], its two auxiliaries
 bounded below by [so] and [r] also [r], and its [Compose]
 auxiliary [so]; the second choice adds [so <= r] to the block.
 - The word [Set] occurs 317 times in the output: [Set < so] in 18
 blocks, [PTopCat]'s own bound, and otherwise only the standard
 library's bounds [Set < Basics.flip.u*] (66 blocks, first carried
 by [UCircleTower], through Instance/Top/Circle.v's [circ_mul]),
 [Set < Morphisms.Proper.u0] and [.Relations.u0] (45, first
 [CircleTower]) and [Set < Morphisms.GenericInstances.u0] (11,
 first [sol_lift_cont]), relations between [Set] and global
 universes explained in Instance/Top/Circle.v's header.
 - [<=] caps on global universes: [eq_ind], [eq_ind_r] and
 [Logic_lemmas.equality] ([Omega]'s own block) and [eq_rect_r],
 first carried by [endo_hom_respects]; [compose] and [ID]
 ([Sets]'); [projections] ([TQuot], through [Circle]);
 [Projections] ([tower_obj], through [SolPoints]); [False_rect] and
 [nat_rect], first carried by [open_bounded_inter]; [prod_rect]
 ([PForget_PreservesLimitCone]'s own block).
 - [open_bounded_inter] and [sol_lift_cont] have extensible universe
 lists: Coq 8.19.2 and 8.20.1 refuse their closed lists
 (“unbound”), while [About] under 8.19.2 reads back the same
 universe lists after minimization ([@{o}], [@{s o so h}]).

 DELIVERED ELSEWHERE.  Instance/Top/Solenoid/Presentations.v relates
 the group presentation and the space presentation, as the appended
 Riehl item asks: the circle group in [Ab] and its tower with the same
 underlying tower as the two towers here ([towers_agree]), the group
 solenoid on the same matching strings, the fibre of μ_0 over the base
 point as the p-adic integers ([Zp_fibre_iso], in [Ab]), and the
 covering property of the wrapping map over both categories
 ([pwrap_evenly_covered], [wrap_evenly_covered]).

 NOT DELIVERED.  The fibre as a SUBSPACE homeomorphic to Z_p with its
 profinite topology; compactness, connectedness and the topological
 group structure of the solenoid; the generic initial topology over
 the Type-valued [Top] and the completeness of [Top] (the solenoid is
 a limit there by its own topology, not by a general theorem); the
 Type-valued analogue of [PTop_solenoid_open_forced]; any comparison
 functor between [Top] and [PTopCat]. 

 --------
 麦克莱恩，《为工作中的数学家准备的范畴论》，第二版（GTM 5），
 §V.1，第111页（PDF第120页），从页面图像阅读（目录编号
 maclane:V.1:construction3）：
 “同样，在Top中，取每个对象 F_n 为圆 S^1，每个箭头 f_n : S^1 → S^1 为将定义域圆 S^1 均匀绕余域圆 p 次的连续映射。引入恰好足以使所有函数 μ_n : L → S^1 连续的 L 中开集后，逆极限集合 L 就成为一个拓扑空间。这个 L 是 Top 中的极限空间；它被称为p进制螺旋体。”
 Riehl，《语境中的范畴论》，§3.6，例3.6.3，印刷本第116页（PDF第136)，从页面图像读取（目录 id riehl:3.6:example3）：
 “拓扑空间范畴 Top 中的任何极限或余极限都可以按命题 3.6.2 的证明中规定的方式构造：通过对底层集合的图形成极限或余极限，然后用最粗（对于极限）或最细（对于余极限）的拓扑对得到的空间进行拓扑，使得极限锥或余极限锥的腿（箭头）是连续的。例如，考虑图 ω^op → Top，其对象是圆 S^1，并且每个生成映射是“pth 次幂映射”，即覆盖映射，将域圆均匀地绕余域圆包裹 p 次：... 逆极限定义了 p 进制螺旋体。”
 nLab:  https://ncatlab.org/nlab/show/solenoid 
 nLab:  https://ncatlab.org/nlab/show/initial+topology 
 Wikipedia:  https://en.wikipedia.org/wiki/Solenoid_(mathematics)背景。螺线体在二进制情况下由Vietoris提出，在一般情况下由van Dantzig提出（维基百科）。它们是紧致可度量的空间，具有连通性但既不局部连通也不路径连通，是一维的同质不可分割连续体，并且具有阿贝尔拓扑群的结构（维基百科）。在动力系统中，螺线体作为Smale-Williams吸引子出现，是双曲系统的一维膨胀吸引子（维基百科）；在形状理论中，nLab将螺线体记录为非稳定空间的例子。对于两本书来说，螺线体是另一种类型的例子：由其拓扑未给出但被强制的空间的极限，Mac Lane的“L中仅必要的那些开集”，Riehl的“使得各支……的最粗拓扑”是连续的，nLab 页面上的初始拓扑。在树中，它的点是 #408 的匹配字符串（Instance/Sets/InverseLimit.v 的 [inverse_limit]），配方是 #458 的（Instance/Top/Complete.v 的 [PTop_Limit_lift]），圆及其 p 倍映射是 Instance/Top/Circle.v 的，而在 Mac Lane 页面上它前面的例子，即作为环 Z/p^nZ 的极限的 p 进整数，是 Instance/Rng/Zp.v 的 [Zp_limit]。该问题的调查已经过时，在这棵树上重新测量。“树中没有拓扑空间的类别”是错误的：Instance/Top.v 的 [Top]（#259）和 Instance/Top/Prop.v 的 [PTopCat]。“rg -i 'coarsest|initial topology' ... 没有返回任何可用内容”是错误的：Instance/Top/Complete.v 的 [PInit]、[pinit_universal] 和 [pinit_weakest] 是初始拓扑及其泛性质。依赖项 #408 和 #458 已经完成。附加的 Riehl 条目将 Riehl 的展示描述为“覆盖映射的图，而不是 p-进群的极限”；上面引用的页面将 Mac Lane 的螺线管展示为圆的极限，p-进整数是其前面的单独示例。该短语是问题文本自身的：两本书都给出了这里构建的单个图。塔楼。[EndoTower X w]是塔......→ X → X → X X
 自同态[w]在任意范畴中，是 [Omega^op] 的函子;它
 将 M <= n 的证明映射到 （n - m）-重的 [w]
 （[endo_hom]，实例/Rng/Zp.v的[res_hom]成语）。[endo_step]
 将生成箭头读回为[id ∘ w]，位于[eq_refl]，且
 [EndoTower_map]显示一个函子将[w]塔传递到
 [fmap w]塔，[Functor_Setoid]，具有单位元分量。三座圆塔[UCircleTower p]为[Sets]，的。
 实例/顶/圈.v的 [circ_mul p] ;[CircleTower p]
 类型值[Top]，[wrap p]，麦克莱恩塔楼;以及
 [PCircleTower p] [PTopCat] ，[pwrap p] 。[PCircleTower_points] 识别了最后一个塔楼的底层
 和第一个。语句写入 [omega_step n]，其中 Instance/Sets/InverseLimit.v 写入 [tower_step n]；两者是一个术语（[tower_step_is_omega_step]）。[About] 显示 [tower_step@{u u0 u1 u2 u3}] 仅以 [u2] 和 [u3] 命名类型：其他三个携带该文件部分 [Context (F : Omega^op ⟶ Sets)]（[u0 < u1] 和 [Sets] 的大写形式）的区块，并且带有封闭宇宙列表的语句无法绑定它们：在封闭列表 [@{s h o | o < h}] 下，通过 [tower_step] 读取 [CircleTower_step] 被拒绝，“宇宙……未绑定”（Test/ProbeSolenoid410.v 的 N6），并且在使用可扩展列表（其 [p410_tower_step]）时被接受。类型值 [Top] 中的电磁阀，问题的类别及其固定名称：[solenoid_limit p : Limit (CircleTower p)]。通用方案无法达到此类别。映射到空间的自然索引族的初始拓扑在两种尝试的类型值形式中都在点宇宙处被拒绝。第一种形式表示，当 V 位于包含因子开集的原像的每个谓词族 T 中时，V 是开的。它没有要求 T 的闭合性质，因此它本身不是包含那些原像的所有拓扑的交集；交集所需的是对 T 类型为 (S → Type@{o}) → Type@{o} 的量化，并且在 T 的假设中添加闭合性质不会降低其宇宙（论证：拒绝打印形式的类型为 [Type@{max(o+1,...)}]，而 o+1 是 T 类型的宇宙）。第二条说每个 V 的点都有一个因子，一个围绕其像的该因子的开集，以及该开集在 V 内的整个原像；它对因子的开集进行量化。两者都被拒绝，“无法强制 o < o”（Test/ProbeSolenoid410.v 的 N2 和 N3），但两者在一层宇宙上都被接受（其 [p410_init_family_up] 和 [p410_init_union_up]）。螺线管自身的拓扑避免了拒绝：[sopen] 对一个阶段 [n : nat] 和一个有理半径 [e] 进行量化，从不对开集进行量化，因此它位于 [Type@{o}]。匹配字符串 [SolPoints p] 上的谓词 [V] 是开集，当且仅当 [V] 的每个点 [s] 都有一个阶段 [n] 和一个半径 [e > 0]，使得在 [s] 的 [e] 内的每个字符串，在圆的球 [cball] 上，在每个阶段 [j <= n]，位于 [V] 中。拓扑不是被假定的，而是被描述的。[solenoid_universal]：一个从任意空间到点的集合映射是连续的，当且仅当它与每个投影的复合映射都是连续的。[solenoid_coarsest]：每个拓扑在点上的拓扑（由 Instance/Top.v 的闭包性质 [TopSpace] 给出）中，如果每个投影都是连续的，则包含 [Solenoid p] 的每一个开集。利用 [sol_leg_cont]，即沿投影的圆上每个开集的原像都在 [sopen] 中，它正好是使各条“腿”连续的最粗拓扑，正如 Mac Lane 所说，“仅那些开集……是必要的”。内容是 [sol_lift_cont]：沿着映射 [g] 的开集 [W] 的原像是对 [W ∘ g] 中的点进行有限交集（[open_bounded_inter]）的一种并，它由圆的球开集内部的原像形成（Instance/Top/Circle.v 的 [cint_open]）。极限的中介 [sol_med] 是一个竞争锥的各条边的元组，由 [sol_lift_cont] 保持连续；唯一性是逐点的。[solenoid_forget_preserves]：[Top_Forget] 保持极限锥。[Top_Forget] 落入升起的 [Sets@{h hs}]，并且 Instance/Top/Forgetful.v 的头部记录了这个升起函子在锥层面的保持在那里“既未声明也未推导”，其竞争者有大的顶点；在这个塔层上，它直接成立，中介就是指向升起点的各条边的元组。[PTopCat] 中的电磁阀，根据 #458 的配方，即 Riehl 的句子：[PTop_solenoid_limit p] 是 [PTop_Limit_lift] 的匹配字符串极限 [Sets_tower_Limit] 的一部分底层塔。它的表征是 #458 关于此塔的一般定理：[PTop_solenoid_universal]（[pinit_universal]）、[PTop_solenoid_coarsest]（[pinit_weakest]）、[PTop_solenoid_open_forced]（塔上的每个极限锥都携带其腿的初始拓扑，[PTop_limit_open_iff_initial]）以及 [PTop_solenoid_forget_preserves]（[PForget_PreservesLimitCone]，通过伴随关系 [PDisc_PForget]）。该名称遵循 #458 的约定，即为 [PTopCat] 上的读数命名 [PTop_*]，旁边附有固定类型值名称。在 [eq_refl]、[solenoid_points] 和 [PTop_solenoid_points] 的点：每个极限的点都是其基塔 [inverse_limit] 的 #408 匹配字符串；[solenoid_leg_map] 和 [PTop_solenoid_leg_map]：其腿是它的投影 [tower_proj]；[sol_compat]：匹配条件是 (∀ n, circ_eq (p · x (S n)) (x n))，按圆读取的 Mac Lane 字符串条件；[solenoid_points_agree]：这两个极限具有相同类型的点。作为集合等价物，这两个点集在 [eq_refl] 上不相等：Instance/Sets/InverseLimit.v 的 [tower_obj] 通过 [Qed]  [Program] 对函子应用义务来构建其集合等价物，而两个基塔是不同的项；该方程被拒绝（“无法统一”，Test/ProbeSolenoid410.v 的 N4）。那只是供体的不透明性，仅此而已：探针的 [p410_tower_obj]，供体的定义已关闭 [Defined]，接受 [eq_refl] 对于两个塔 ([p410_flip_ptop])。p，以及当 p = 1 时的结果。[p : positive]；Mac Lane 的 p 是一个素数（书第 110 页），Riehl 的未作限定，并且这里没有使用素数性。以上的任何构造和特征化都没有使用关于 p 的假设。非空性在每个 p 上都成立：[solenoid_two_points] 否定了零字符串 ≈ 字符串 (1/(2p^n))_n，其阶段 0 的项 0 和 1/2 在圆上不同，而 [PTop_solenoid_two_points] 给出了 [PSolenoid p] 的同样两个点。文件中的唯一假设，[1 < p]，仅使用了一次：[unit_string_not_zero] 否定了字符串 (1/p^n)_n ≈ 零字符串，而 [unit_string_over_zero] 在阶段 0 将两者放在同一点上，因此对于 1 < p，腿 μ_0 将两个不同的点识别为同一个点。在 p = 1 时，这个塔在  [≈]（Instance/Top/Circle.v 的 [wrap_one]） 上是恒等的，而螺线管与圆同构：[solenoid_one_iso] 和 [PTop_solenoid_one_iso] 是 [Top] 和 [PTopCat] 中的同构映射，其前向箭头是腿 μ_0，逆向箭头将一个点映射到它的常量字符串。优势。在 [eq_refl]：[endo_step]、[CircleTower_step]、[PCircleTower_step]、[sol_compat]、[solenoid_points]、[solenoid_leg_map]、[PTop_solenoid_points]、[PTop_solenoid_leg_map]、[solenoid_points_agree] 和 [half_string_coord]。到 [≈]：[endo_step_equiv]、[EndoTower_map] 和 [PCircleTower_points]（在 [Functor_Setoid] 中），[solenoid_one_iso] 和 [PTop_solenoid_one_iso] 的同类定律。[endo_step] 是 [id ∘ w]，而不是 [w]：在任意类别（Test/ProbeSolenoid410.v 的 N5）中，带有 [w] 的方程被拒绝。与 [iffT] 和 [iff] 相关：[solenoid_universal]、[PTop_solenoid_universal]、[PTop_solenoid_open_forced]。[PTop_solenoid_two_points] 已经关闭 [Defined]，因此它的两个见证返回：其第一投影是 [zero_string p]（探针的 [p410_two_points_first]）。[打印假设] 对 [Print Module] 列表的所有 78 个常量、包括六个 [Program] 义务，以及 Instance/Top/Circle.v 的所有 94 个，都打印“在全局上下文下已关闭”。UNIVERSES，由[About]在[Set Printing Universes]下读取，位于78常数上。[EndoTower@{s o h}]接受[C : Category@{o h h}]并返回[Omega@{s h h}^op ⟶ C]；电磁常数为[@{s o so}]用于点及其拓扑，[@{s o so h}]用于提到[Top@{h o}]的内容，[solenoid_limit@{s o so h r}]及其[Limit@{r s h h}]，以及[PTop_solenoid_limit@{s o so r}]及[Limit@{r s o so}]；仅语句的引理还携带[Compose]、[iffT]和[IsLimitCone]的辅助内容。- 没有块携带方程，且没有宇宙固定在[Set]：两个电磁均存在于每个点宇宙[o]。- 本文件的宇宙之间的严格界限：[o < h]（23个块，[Top]自身的），[o < so]（60个，[Sets]和[PTopCat]的），[h < hs]（3个，[Top_Forget]的），以及[o < u*]或[h < u1]在六个常量中，其中五个的语句组成函数子（[EndoTower_map]，[PCircleTower_points]，[PTop_solenoid_points]，[PTop_solenoid_open_forced]，[PTop_solenoid_forget_preserves]）和[PTop_solenoid_two_points]，其[Defined]主体通过两个辅助引入界限（在一个临时副本中相同的语句闭合为[Qed]，读作[@{s o so u}]而没有它）：[Compose]自身在辅助下的同类宇宙界限（[About Compose]：u3 < u2）。- [PTop_solenoid_limit] 用其输入和输出限制宇宙都是 [r] 来实例化 [PTop_Limit_lift]，其两个辅助变量下界为 [so] 和 [r]，也为 [r]，以及其 [Compose] 辅助 [so]；第二个选择将 [so <= r] 添加到块中。- 词 [Set] 在输出中出现 317 次：18 块中的 [Set < so]，[PTopCat] 自身的界限，以及除此之外仅标准库的界限 [Set < Basics.flip.u*]（66 块，最初由 [UCircleTower] 携带，通过 Instance/Top/Circle.v 的 [circ_mul]），[Set < Morphisms.Proper.u0] 和 [.Relations.u0]（45，最初 [CircleTower]）以及 [Set < Morphisms.GenericInstances.u0]（11，最初 [sol_lift_cont]），[Set] 与全局宇宙之间的关系在 Instance/Top/Circle.v 的头文件中解释。- [<=] 在全局宇宙的上限：[eq_ind]、[eq_ind_r] 和 [Logic_lemmas.equality]（[Omega] 自己的区块）以及 [eq_rect_r]，首次由 [endo_hom_respects] 携带；[compose] 和 [ID]（[Sets]）；[projections]（[TQuot]，通过 [Circle]）；[Projections]（[tower_obj]，通过 [SolPoints]）；[False_rect] 和 [nat_rect]，首次由 [open_bounded_inter] 携带；[prod_rect]（[PForget_PreservesLimitCone] 自己的区块）。- [open_bounded_inter] 和 [sol_lift_cont] 有可扩展的宇宙列表：Coq 8.19.2 和 8.20.1 拒绝它们的闭合列表（“未绑定”），而 [About] 在 8.19.2 下经过最小化后读取回相同的宇宙列表（[@{o}]、[@{s o so h}]）。在其他地方交付。Instance/Top/Solenoid/Presentations.v 关联了群演示和空间演示，如附加的 Riehl 项所要求：[Ab] 中的圆群及其塔，其底层塔与这里的两个塔相同（[towers_agree]），在相同匹配序列上的群螺线体，μ_0 在基点上的纤维为 p-adic 整数（[Zp_fibre_iso]，在 [Ab] 中），以及环绕映射在两个范畴上的覆盖性质（[pwrap_evenly_covered]、[wrap_evenly_covered]）。未交付。纤维作为一个与 Z_p 同胚的子空间，具有其有限生成拓扑；螺旋体的紧性、连通性以及拓扑群结构；类型值 [Top] 上的典型初始拓扑以及 [Top] 的完备性（螺旋体在此由其自身的拓扑而成为极限，而不是由一般定理得出）；[PTop_solenoid_open_forced] 的类型值类比；[Top] 与 [PTopCat] 之间的任何比较函子。
*)

Open Scope category_scope.

#[local] Obligation Tactic := idtac.

(* * ** The tower of an endomorphism, in any category / * ** 任意范畴中一个自同态的塔 *)

Section EndoTower.

Universes s o h.

Context {C : Category@{o h h}} (X : obj[C]) (w : X ~{C}~> X).

(*
 The action on an order proof, the Instance/Rng/Zp.v [res_hom] idiom:
 the proof of [m <= n] built from [n - m] successor steps is sent to
 the [n - m]-fold composite of [w]. 

 --------
 关于订单证明的操作，Instance/Rng/Zp.v  [res_hom]  成语：  
 从  [n - m]  后续步骤构建的  [m <= n]  证明被发送到  
 由  [w]  组成的  [n - m] 倍合成体。
*)
Fixpoint endo_hom {m n : nat} (f : le_t@{h} m n) : X ~{C}~> X :=
  match f with
  | le_t_n    => id
  | le_t_S f' => endo_hom f' ∘ w
  end.

Lemma endo_hom_trans {m n k : nat} (a : le_t@{h} m n) (b : le_t@{h} n k) :
  endo_hom (le_t_trans@{h} a b) ≈ endo_hom a ∘ endo_hom b.
Proof.
  induction b as [| k' b' IH].
  - cbn [endo_hom le_t_trans]. now rewrite id_right.
  - cbn [endo_hom le_t_trans]. rewrite IH. now rewrite comp_assoc.
Qed.

Lemma endo_hom_respects {x y : nat} (f g : x ~{Omega@{s h h}^op}~> y) :
  f ≈ g → endo_hom f ≈ endo_hom g.
Proof. intro H; simpl in H; subst; reflexivity. Qed.

Lemma endo_hom_id (x : nat) :
  endo_hom (@id (Omega@{s h h}^op) x) ≈ @id C X.
Proof. reflexivity. Qed.

Lemma endo_hom_comp {x y z : nat}
  (f : y ~{Omega@{s h h}^op}~> z) (g : x ~{Omega@{s h h}^op}~> y) :
  endo_hom (f ∘ g) ≈ endo_hom f ∘ endo_hom g.
Proof. exact (endo_hom_trans f g). Qed.

(*
 The tower  ... --w--> X --w--> X --w--> X  as a functor out of
 [Omega^op]. 

 --------
 塔 ... --w--> X --w--> X --w--> X 作为从 [Omega^op] 出来的函子。
*)
Definition EndoTower : Omega@{s h h}^op ⟶ C :=
  @Build_Functor (Omega@{s h h}^op) C (fun _ => X)
    (fun _ _ f => endo_hom f)
    (fun x y f g H => endo_hom_respects f g H)
    endo_hom_id
    (fun x y z f g => endo_hom_comp f g).

(* The generating arrow is sent to [w], on the nose up to the unit. / 生成箭头被发送到 [w]，正好对准单位。 *)
Example endo_step (n : nat) :
  fmap[EndoTower] (omega_step n) = id ∘ w := eq_refl.

Lemma endo_step_equiv (n : nat) : fmap[EndoTower] (omega_step n) ≈ w.
Proof. exact (id_left w). Qed.

End EndoTower.

(* A functor carries the tower of [w] to the tower of [fmap w]. / 函子将 [w] 的塔携带到 [fmap w] 的塔。 *)
Section EndoTowerMap.

Universes s oc od h.

Context {C : Category@{oc h h}} {D : Category@{od h h}} (G : C ⟶ D)
        (X : obj[C]) (w : X ~{C}~> X).

Lemma endo_hom_fmap {m n : nat} (f : le_t@{h} m n) :
  fmap[G] (endo_hom X w f) ≈ endo_hom (G X) (fmap[G] w) f.
Proof.
  induction f as [| k f' IH]; simpl.
  - apply fmap_id.
  - rewrite fmap_comp, IH. reflexivity.
Qed.

Lemma EndoTower_map@{+} :
  G ◯ EndoTower@{s oc h} X w ≈ EndoTower@{s od h} (G X) (fmap[G] w).
Proof.
  exists (fun _ => iso_id). intros x y f; simpl.
  rewrite id_left, id_right. exact (endo_hom_fmap f).
Qed.

End EndoTowerMap.

(** ** The towers of circles / ** 圆形的塔 *)

(* The tower of points: the circle's point setoid under the p-fold map, in [Sets]. / 点塔：在 [Sets] 下，圆的点集合在 p 倍映射下的集合化。 *)
Definition UCircleTower@{s o so | o < so +} (p : positive) :
  Omega@{s o o}^op ⟶ Sets@{o so} :=
  @EndoTower Sets@{o so} Circle_setoid@{o} (circ_mul@{o} p).

(* Mac Lane's tower in the Type-valued [Top]. / Mac Lane 在类型值 [Top] 中的塔。 *)
Definition CircleTower@{s h o | o < h +} (p : positive) :
  Omega@{s h h}^op ⟶ Top@{h o} :=
  @EndoTower Top@{h o} Circle@{o} (wrap@{h o} p).

(* The same tower in [PTopCat]. / 在 [PTopCat] 的同一座塔。 *)
Definition PCircleTower@{s o so | o < so +} (p : positive) :
  Omega@{s o o}^op ⟶ PTopCat@{o so} :=
  @EndoTower PTopCat@{o so} PCircle@{o} (pwrap@{o so} p).

Example CircleTower_step@{s h o + | o < h +} (p : positive) (n : nat) :
  fmap[CircleTower@{s h o} p] (omega_step n) = id ∘ wrap p := eq_refl.

Example PCircleTower_step@{s o so + | o < so +} (p : positive) (n : nat) :
  fmap[PCircleTower@{s o so} p] (omega_step n) = id ∘ pwrap p := eq_refl.

(* The underlying tower of the [PTopCat] tower is the tower of points. / [PTopCat] 塔的底层塔是点塔。 *)
Lemma PCircleTower_points@{s o so + | o < so +} (p : positive) :
  PForget@{o so} ◯ PCircleTower@{s o so} p ≈ UCircleTower@{s o so} p.
Proof. exact (EndoTower_map PForget PCircle (pwrap p)). Qed.

(* * ** The solenoid in the Type-valued [Top] / * ** Type-valued [Top] 中的电磁阀 *)

(* Its points: #408's matching strings of the tower of points. / 它的点：#408 的点塔匹配字符串。 *)
Definition SolPoints@{s o so | o < so +} (p : positive) : SetoidObject@{o o} :=
  inverse_limit@{o s o so so o} (UCircleTower@{s o so} p).

Definition sol_pr@{s o so | o < so +} (p : positive) (n : nat) :
  SetoidMorphism@{o o o} (SolPoints@{s o so} p) Circle_setoid@{o} :=
  tower_proj@{s o so o} (UCircleTower@{s o so} p) n.

(* Mac Lane's matching condition, read back: p x_(n+1) = x_n on the circle, for every n. / Mac Lane 的匹配条件，反读为：在圆上，对于每一个 n，有 p x_(n+1) = x_n。 *)
Example sol_compat@{s o so + | o < so +} (p : positive)
  (x : Sets_iprod_obj (fun n : nat => fobj[UCircleTower@{s o so} p] n)) :
  tower_compat (UCircleTower@{s o so} p) x
  = (∀ n : nat, circ_eq (CReal_mult (posR p) (x (S n))) (x n)) := eq_refl.

(* Its opens: those predicates each of whose points [s] has a finite stage [n] and a radius [e] such that every string within [e] of [s] at the stages up to [n] lies in the predicate. / 它是开放的：那些谓词，其每个点 [s] 都有一个有限阶段 [n] 和一个半径 [e] ，使得在到阶段 [n] 为止，每个位于 [s] 的 [e] 内的字符串都属于该谓词。 *)
Definition sopen@{s o so | o < so +} (p : positive)
  (V : SolPoints@{s o so} p → Type@{o}) : Type@{o} :=
  ∀ s, V s → { n : nat & { e : Q & (Qlt 0 e *
    ∀ s', (∀ j, (j <= n)%nat → cball@{o} (sol_pr p j s) (sol_pr p j s') e) →
          V s')%type } }.

Lemma sopen_respects@{s o so | o < so +} (p : positive)
  (U V : SolPoints@{s o so} p → Type@{o}) :
  (∀ x, U x ↔ V x) → sopen p U → sopen p V.
Proof.
  intros H HU s v. destruct (HU s (snd (H s) v)) as [n [e [He Hb]]].
  exists n, e; split; [exact He|]. intros s' b; exact (fst (H s') (Hb s' b)).
Qed.

Lemma sopen_proper@{s o so | o < so +} (p : positive)
  (U : SolPoints@{s o so} p → Type@{o}) :
  sopen p U → ∀ x y : SolPoints@{s o so} p, x ≈ y → U x → U y.
Proof.
  intros HU x y Hxy u. destruct (HU x u) as [n [e [He Hb]]].
  apply Hb. intros j _. apply cball_of_eq; [exact He|exact (Hxy j)].
Qed.

Lemma sopen_union@{s o so | o < so +} (p : positive) (I : Type@{o})
  (U : I → (SolPoints@{s o so} p → Type@{o})) :
  (∀ i, sopen p (U i)) → sopen p (fun x => { i : I & U i x }).
Proof.
  intros HU x [i u]. destruct (HU i x u) as [n [e [He Hb]]].
  exists n, e; split; [exact He|]. intros y b. exact (i; Hb y b).
Qed.

Lemma sopen_whole@{s o so | o < so +} (p : positive) :
  sopen@{s o so} p (fun _ => poly_unit@{o}).
Proof.
  intros x _. exists 0%nat, 1%Q. split; [reflexivity|intros; exact ttt].
Qed.

Lemma sopen_inter@{s o so | o < so +} (p : positive)
  (U V : SolPoints@{s o so} p → Type@{o}) :
  sopen p U → sopen p V → sopen p (fun x => U x ∧ V x).
Proof.
  intros HU HV x [u v].
  destruct (HU x u) as [n1 [e1 [He1 Hb1]]], (HV x v) as [n2 [e2 [He2 Hb2]]].
  exists (Nat.max n1 n2).
  destruct (Qlt_le_dec e1 e2) as [Hlt|Hle].
  - exists e1; split; [exact He1|]. intros y b; split.
    + apply Hb1. intros j Hj. apply b. lia.
    + apply Hb2. intros j Hj. apply (cball_mono _ _ e1);
        [apply Qlt_le_weak; exact Hlt|apply b; lia].
  - exists e2; split; [exact He2|]. intros y b; split.
    + apply Hb1. intros j Hj.
      apply (cball_mono _ _ e2); [exact Hle|apply b; lia].
    + apply Hb2. intros j Hj. apply b. lia.
Qed.

Definition Solenoid@{s o so | o < so +} (p : positive) : TopSpace@{o} := {|
  top_carrier   := SolPoints@{s o so} p;
  IsOpen        := sopen@{s o so} p;
  open_respects := sopen_respects@{s o so} p;
  open_proper   := sopen_proper@{s o so} p;
  open_union    := sopen_union@{s o so} p;
  open_whole    := sopen_whole@{s o so} p;
  open_inter    := sopen_inter@{s o so} p
|}.

Lemma sol_leg_cont@{s o so h | o < so, o < h +} (p : positive) (n : nat) :
  Continuous@{h o} (Solenoid@{s o so} p) Circle@{o} (sol_pr@{s o so} p n).
Proof.
  intros U HU s u. destruct (fst (circle_open_balls U) HU _ u) as [e [He Hb]].
  exists n, e. split; [exact He|]. intros s' H. apply Hb, H. lia.
Qed.

Definition sol_leg@{s o so h | o < so, o < h +} (p : positive) (n : nat) :
  Solenoid@{s o so} p ~{Top@{h o}}~> Circle@{o} :=
  @Build_ContinuousMorphism (Solenoid p) Circle (sol_pr p n)
    (sol_leg_cont@{s o so h} p n).

(* A finite intersection of opens, over the stages up to [n], is open. / 在直到 [n] 阶段上的开集的有限交是开集。 *)
Lemma open_bounded_inter@{o +} (Z : TopSpace@{o}) (P : nat → Z → Type@{o})
  (HP : ∀ j, IsOpen Z (P j)) (n : nat) :
  IsOpen Z (fun z => ∀ j, (j <= n)%nat → P j z).
Proof.
  induction n as [|n IH].
  - apply (open_respects Z (P 0%nat)); [|exact (HP 0%nat)]. intro z; split.
    + intros h j Hj. destruct j; [exact h|exfalso; lia].
    + intros h. exact (h 0%nat (le_n 0)).
  - apply (open_respects Z (fun z => (∀ j, (j <= n)%nat → P j z) ∧ P (S n) z)).
    + intro z; split.
      * intros [h1 h2] j Hj. destruct (Nat.eq_dec j (S n)) as [->|Hne];
          [exact h2|apply h1; lia].
      * intros h. split; [intros j Hj; apply h; lia|apply h; lia].
    + exact (open_inter Z _ _ IH (HP (S n))).
Qed.

(*
 The half of the universal property with content: a setoid map into the
 solenoid's points is continuous as soon as every composite with a
 projection is. 

 --------
 具有内容的通用性质的一半：只要与每个投影的复合是连续的，映射到螺线管点的集合范畴映射就是连续的。
*)
Lemma sol_lift_cont@{s o so h + | o < so, o < h +} (p : positive)
  (Z : TopSpace@{o}) (g : SetoidMorphism@{o o o} Z (SolPoints@{s o so} p))
  (Hg : ∀ j, Continuous@{h o} Z Circle@{o}
               (setoid_morphism_compose (sol_pr p j) g)) :
  Continuous@{h o} Z (Solenoid@{s o so} p) g.
Proof.
  intros W HW.
  apply (open_respects Z (fun z => { i : { z0 : Z & W (g z0) } &
     ∀ j, (j <= projT1 (HW (g (projT1 i)) (projT2 i)))%nat →
       cint (sol_pr p j (g (projT1 i)))
            (projT1 (projT2 (HW (g (projT1 i)) (projT2 i))))
            (sol_pr p j (g z)) })).
  - intro z; split.
    + intros [i b].
      destruct (HW (g (projT1 i)) (projT2 i)) as [n [e [He Hb]]] eqn:Ew.
      simpl in b. apply Hb. intros j Hj. exact (cint_sub _ _ _ (b j Hj)).
    + intros w. exists (z; w). cbn [projT1 projT2].
      destruct (HW (g z) w) as [n [e [He Hb]]]; simpl.
      intros j Hj. exact (cint_centre _ _ He).
  - apply open_union. intros [z0 w0]. cbn [projT1 projT2].
    destruct (HW (g z0) w0) as [n [e [He Hb]]]; simpl.
    apply (open_bounded_inter Z
             (fun j z => cint (sol_pr p j (g z0)) e (sol_pr p j (g z)))).
    intro j. exact (Hg j (cint (sol_pr p j (g z0)) e) (cint_open _ _)).
Qed.

(*
 The universal property of the solenoid's topology, over ANY space
 mapping in. 

 --------
 螺线管拓扑的普遍性质，对于映射到任意空间的情况。
*)
Theorem solenoid_universal@{s o so h + | o < so, o < h +} (p : positive)
  (Z : TopSpace@{o}) (g : SetoidMorphism@{o o o} Z (SolPoints@{s o so} p)) :
  Continuous@{h o} Z (Solenoid@{s o so} p) g ↔
  (∀ j, Continuous@{h o} Z Circle@{o}
          (setoid_morphism_compose (sol_pr p j) g)).
Proof.
  split.
  - intros Hg j U HU. exact (Hg _ (sol_leg_cont p j U HU)).
  - exact (sol_lift_cont p Z g).
Qed.

(* The transition maps carry every matching string to itself. / 转换映射将每个匹配的字符串映射到其自身。 *)
Lemma sol_tower_compat@{s o so h | o < so, o < h +} (p : positive)
  (x : SolPoints@{s o so} p) {m n : nat}
  (f : n ~{Omega@{s h h}^op}~> m) :
  continuous_map (fmap[CircleTower@{s h o} p] f) (sol_pr p n x)
    ≈ sol_pr p m x.
Proof.
  induction f as [| k f' IH].
  - reflexivity.
  - transitivity (continuous_map (fmap[CircleTower@{s h o} p] f')
                    (sol_pr p k x)); [|exact IH].
    apply (proper_morphism (continuous_map (fmap[CircleTower p] f'))).
    exact (`2 x k).
Qed.

Definition sol_acone@{s o so h | o < so, o < h +} (p : positive) :
  @ACone (Omega@{s h h}^op) Top@{h o} (Solenoid@{s o so} p)
    (CircleTower@{s h o} p).
Proof.
  unshelve refine (@Build_ACone (Omega@{s h h}^op) Top@{h o} (Solenoid p)
                     (CircleTower p) (sol_leg p) _).
  intros m n f s. exact (sol_tower_compat p s f).
Defined.

Definition sol_cone@{s o so h | o < so, o < h +} (p : positive) :
  Cone (CircleTower@{s h o} p) :=
  @Build_Cone (Omega^op) Top@{h o} (CircleTower p) (Solenoid@{s o so} p)
    (sol_acone p).

(* The mediator out of a competing cone: its legs, bundled at a point. / 来自竞争锥体的中介：它的腿，在一点上束成一捆。 *)
Program Definition sol_med_map@{s o so h | o < so, o < h +} (p : positive)
  (N : Cone (CircleTower@{s h o} p)) :
  SetoidMorphism@{o o o} (vertex_obj[N]) (SolPoints@{s o so} p) := {|
  morphism := fun z =>
    (fun n => continuous_map (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) n) z;
     fun n => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) (S n) n
                (omega_step n) z)
|}.
Next Obligation.
  intros p N z z' H n. exact (proper_morphism
    (continuous_map (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) n)) z z' H).
Qed.

Definition sol_med@{s o so h | o < so, o < h +} (p : positive)
  (N : Cone (CircleTower@{s h o} p)) :
  vertex_obj[N] ~{Top@{h o}}~> Solenoid@{s o so} p :=
  @Build_ContinuousMorphism (vertex_obj[N]) (Solenoid p) (sol_med_map p N)
    (sol_lift_cont p _ (sol_med_map p N)
       (fun j => continuity (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) j))).

(* The p-adic solenoid: the limit in [Top] of the tower of circles. / p-进数螺旋体：圆塔在 [Top] 中的极限。 *)
Program Definition solenoid_limit@{s o so h r | o < so, o < h +}
  (p : positive) : Limit@{r s h h} (CircleTower@{s h o} p) := {|
  limit_cone := sol_cone@{s o so h} p;
  ump_limits := fun N => {| unique_obj := sol_med p N |}
|}.
Next Obligation. intros p N n z; reflexivity. Qed.
Next Obligation. intros p N v Hv z n; symmetry; exact (Hv n z). Qed.

(* The limit's points ARE the matching strings, and its legs ARE the projections. / 极限点就是匹配的字符串，它的边就是投影。 *)
Example solenoid_points@{s o so h + | o < so, o < h +} (p : positive) :
  top_carrier (vertex_obj[@limit_cone _ _ _ (solenoid_limit@{s o so h _} p)])
  = inverse_limit (UCircleTower@{s o so} p) := eq_refl.

Example solenoid_leg_map@{s o so h + | o < so, o < h +} (p : positive)
  (n : nat) :
  continuous_map
    (cone_leg (@limit_cone _ _ _ (solenoid_limit@{s o so h _} p)) n)
  = tower_proj (UCircleTower@{s o so} p) n := eq_refl.

(* The coarsest topology making the legs continuous: every topology on the points in which each projection is continuous contains every open of the solenoid. / 使腿连续的最粗拓扑：在每个投影连续的点上的每个拓扑包含螺线管的每个开集。 *)
Lemma solenoid_coarsest@{s o so h + | o < so, o < h +} (p : positive)
  (T : (SolPoints@{s o so} p → Type@{o}) → Type@{o})
  (Tr : ∀ U V, (∀ x, U x ↔ V x) → T U → T V)
  (Tp : ∀ U, T U → ∀ x y : SolPoints p, x ≈ y → U x → U y)
  (Tu : ∀ (I : Type@{o}) (U : I → SolPoints p → Type@{o}),
          (∀ i, T (U i)) → T (fun x => { i : I & U i x }))
  (Tw : T (fun _ => poly_unit@{o}))
  (Ti : ∀ U V, T U → T V → T (fun x => U x ∧ V x))
  (Hc : ∀ n (U : Circle_setoid@{o} → Type@{o}), IsOpen Circle@{o} U →
          T (fun s => U (sol_pr p n s))) :
  ∀ V, sopen p V → T V.
Proof.
  intros V HV.
  pose (Z := @Build_TopSpace (SolPoints p) T Tr Tp Tu Tw Ti).
  exact (sol_lift_cont@{s o so h} p Z (@setoid_morphism_id (SolPoints p))
           (fun j U HU => Hc j U HU) V HV).
Qed.

(*
 The underlying-set functor preserves the limit.  [Top_Forget] lands in
 the lifted [Sets@{h hs}], where no [Adjunction] record joins it to the
 discrete-space functor (Instance/Top/Forgetful.v's header), so the
 mediator is built directly: the tuple of the legs. 

 --------
 底层集合函子保持极限。[Top_Forget] 落在提升后的 [Sets@{h hs}] 中，其中没有 [Adjunction] 记录将其与离散空间函子（Instance/Top/Forgetful.v 的头部）连接，所以中介者是直接构建的：各分支的元组。
*)
Program Definition sol_forget_med@{s o so h hs | o < so, o < h, h < hs +}
  (p : positive)
  (M : Cone (Top_Forget@{o h hs} ◯ CircleTower@{s h o} p)) :
  SetoidMorphism@{h h h} (vertex_obj[M])
    (Setoid_Lift@{o h} (SolPoints@{s o so} p)) := {|
  morphism := fun a =>
    (fun n => @vertex_map _ _ _ _ (@coneFrom _ _ _ M) n a;
     fun n => @cone_coherence _ _ _ _ (@coneFrom _ _ _ M) (S n) n
                (omega_step n) a)
|}.
Next Obligation.
  intros p M a a' H n. exact (proper_morphism
    (@vertex_map _ _ _ _ (@coneFrom _ _ _ M) n) a a' H).
Qed.

Definition solenoid_forget_preserves@{s o so h hs + | o < so, o < h, h < hs +}
  (p : positive) :
  IsLimitCone (FCone Top_Forget@{o h hs} (sol_cone@{s o so h} p)).
Proof.
  intro M.
  unshelve refine {| unique_obj := sol_forget_med p M |}.
  - intros n a; reflexivity.
  - intros v Hv a n; symmetry; exact (Hv n a).
Defined.

(* * ** The solenoid in [PTopCat], by #458's recipe / * ** [PTopCat] 中的电磁阀，由 #458 的配方 *)

Definition PTop_solenoid_limit@{s o so r | o < so +} (p : positive) :
  Limit@{r s o so} (PCircleTower@{s o so} p) :=
  PTop_Limit_lift@{s o so r r r r so} (PCircleTower@{s o so} p)
    (Sets_tower_Limit@{s o so r o} (PForget@{o so} ◯ PCircleTower@{s o so} p)).

Definition PSolenoid@{s o so r | o < so +} (p : positive) : PTop@{o} :=
  vertex_obj[@limit_cone _ _ _ (PTop_solenoid_limit@{s o so r} p)].

Definition psol_leg@{s o so r | o < so +} (p : positive) (n : nat) :
  PSolenoid@{s o so r} p ~{PTopCat@{o so}}~> PCircle@{o} :=
  cone_leg (@limit_cone _ _ _ (PTop_solenoid_limit@{s o so r} p)) n.

Example PTop_solenoid_points@{s o so + | o < so +} (p : positive) :
  pt_carrier (PSolenoid@{s o so _} p)
  = inverse_limit (PForget@{o so} ◯ PCircleTower@{s o so} p) := eq_refl.

Example PTop_solenoid_leg_map@{s o so + | o < so +} (p : positive) (n : nat) :
  pmap (psol_leg@{s o so _} p n)
  = tower_proj (PForget@{o so} ◯ PCircleTower@{s o so} p) n := eq_refl.

(* The universal property, over arbitrary spaces mapping in. / 在任意空间映射中的泛性质。 *)
Lemma PTop_solenoid_universal@{s o so + | o < so +} (p : positive)
  (Z : PTop@{o}) (g : SetoidMorphism@{o o o} Z (PSolenoid@{s o so _} p)) :
  @PCont Z (PSolenoid p) g <->
  (∀ n, @PCont Z PCircle
          (setoid_morphism_compose (pmap (psol_leg p n)) g)).
Proof. exact (pinit_universal _ nat (fun _ => PCircle) _ Z g). Qed.

(* The coarsest topology making every leg continuous. / 使每条边连续的最粗拓扑。 *)
Lemma PTop_solenoid_coarsest@{s o so + | o < so +} (p : positive)
  (T : (PSolenoid@{s o so _} p → Prop) → Prop)
  (HT : PIsTopology _ T)
  (Hc : ∀ n (U : PCircle@{o} → Prop), POpen PCircle U →
          T (fun s => U (pmap (psol_leg p n) s))) :
  ∀ V, POpen (PSolenoid p) V → T V.
Proof. exact (pinit_weakest _ nat (fun _ => PCircle) _ T HT Hc). Qed.

(* Any limiting cone over the tower carries exactly the initial topology for its legs (#458's necessity half, at this tower). / 塔上的任何限制圆锥恰好承载其腿的初始拓扑（#458 的必要性部分，在此塔上）。 *)
Lemma PTop_solenoid_open_forced@{s o so + | o < so +} (p : positive)
  (L : Cone (PCircleTower@{s o so} p)) (HL : IsLimitCone L)
  (V : vertex_obj[L] → Prop) :
  POpen (vertex_obj[L]) V <->
  POpen (vertex_obj[pinit_cone (PCircleTower p) (FCone PForget L)]) V.
Proof. exact (PTop_limit_open_iff_initial _ L HL V). Qed.

Definition PTop_solenoid_forget_preserves@{s o so + | o < so +}
  (p : positive) :
  IsLimitCone (FCone PForget@{o so}
                 (@limit_cone _ _ _ (PTop_solenoid_limit@{s o so _} p))) :=
  PForget_PreservesLimitCone _ (PCircleTower p)
    (@limit_cone _ _ _ (PTop_solenoid_limit p))
    (limit_limitcone (PTop_solenoid_limit p)).

(* * ** The two solenoids have the same points / * ** 这两个电磁线圈的接点相同 *)

Example solenoid_points_agree@{s o so + | o < so +} (p : positive) :
  carrier (SolPoints@{s o so} p) = carrier (pt_carrier (PSolenoid@{s o so _} p))
  := eq_refl.

(** ** Points of the solenoid / ** 线圈的要点 *)

Fixpoint ppow@{} (p : positive) (n : nat) : positive :=
  match n with
  | O => 1
  | S n' => p * ppow p n'
  end.

(* p times 1/(c p m) is 1/(c m). / p 乘以 1/(c p m) 等于 1/(c m)。 *)
Lemma posR_scale@{} (p c m : positive) :
  CRealEq (CReal_mult (posR p) (inject_Q (1 # (c * (p * m)))))
          (inject_Q (1 # (c * m))).
Proof.
  unfold posR, inject_Z. rewrite <- inject_Q_mult. apply inject_Q_morph_T.
  unfold Qeq, Qmult; simpl. rewrite !Pos2Z.inj_mul. ring.
Qed.

Lemma zero_compat@{u} (p : positive) :
  circ_eq@{u} (CReal_mult (posR p) (inject_Q 0)) (inject_Q 0).
Proof.
  apply circ_eq_of_creal. unfold posR, inject_Z.
  rewrite <- inject_Q_mult. apply inject_Q_morph_T. reflexivity.
Qed.

Lemma scaled_compat@{u} (p c : positive) (n : nat) :
  circ_eq@{u} (CReal_mult (posR p) (inject_Q (1 # (c * ppow p (S n)))))
              (inject_Q (1 # (c * ppow p n))).
Proof. apply circ_eq_of_creal. exact (posR_scale p c (ppow p n)). Qed.

(* The constant string at zero. / 零处的常量字符串。 *)
Definition zero_string@{s o so | o < so +} (p : positive) :
  SolPoints@{s o so} p.
Proof.
  exists (fun _ => inject_Q 0). intro n. exact (zero_compat p).
Defined.

(* The string (1/(2 p^n))_n: it starts at the half-turn 1/2, and the p-fold map carries each entry to the one before. / 数列 (1/(2 p^n))_n：它从半转 1/2 开始，且 p 倍映射将每个项映射到前一项。 *)
Definition half_string@{s o so | o < so +} (p : positive) :
  SolPoints@{s o so} p.
Proof.
  exists (fun n => inject_Q (1 # (2 * ppow p n))). intro n.
  exact (scaled_compat p 2 n).
Defined.

Example half_string_coord@{s o so + | o < so +} (p : positive) (n : nat) :
  sol_pr@{s o so} p n (half_string p) = inject_Q (1 # (2 * ppow p n))
  := eq_refl.

(* Non-vacuity: two distinct points, for every positive p. / 非空性：对于每个正的 p，存在两个不同的点。 *)
Lemma solenoid_two_points@{s o so | o < so +} (p : positive) :
  @equiv _ (SolPoints@{s o so} p) (zero_string@{s o so} p)
    (half_string@{s o so} p) → False.
Proof.
  intro H. apply circle_half_not_zero. apply circ_eq_sym. exact (H 0%nat).
Qed.

Definition PTop_solenoid_two_points@{s o so + | o < so +} (p : positive) :
  { a : PSolenoid@{s o so _} p &
    { b : PSolenoid@{s o so _} p & a ≈ b → False } }.
Proof.
  exists (zero_string p), (half_string p). exact (solenoid_two_points p).
Defined.

(* The string (1/p^n)_n lies over the base point, like the zero string; when 1 < p the two differ, so the leg at stage zero is not injective. / 序列 (1/p^n)_n 位于基点之上，就像零序列一样；当 1 < p 时，两者不同，因此零阶段的支腿不是单射的。 *)
Definition unit_string@{s o so | o < so +} (p : positive) :
  SolPoints@{s o so} p.
Proof.
  exists (fun n => inject_Q (1 # (1 * ppow p n))). intro n.
  exact (scaled_compat p 1 n).
Defined.

Lemma unit_string_over_zero@{s o so | o < so +} (p : positive) :
  sol_pr@{s o so} p 0 (unit_string@{s o so} p)
  ≈ sol_pr@{s o so} p 0 (zero_string@{s o so} p).
Proof. exists 1%Z. apply inject_Q_minus_int. reflexivity. Qed.

Lemma unit_string_not_zero@{s o so | o < so +} (p : positive) :
  (1 < p)%positive →
  @equiv _ (SolPoints@{s o so} p) (unit_string@{s o so} p)
    (zero_string@{s o so} p) → False.
Proof.
  intros Hp H. destruct (H 1%nat) as [k Hk].
  apply inject_Q_minus_int_inv in Hk.
  unfold Qeq, Qminus, Qplus, Qopp in Hk; simpl in Hk.
  rewrite !Pos.mul_1_r in Hk.
  assert (Hp1 : (1 < Z.pos p)%Z) by lia.
  destruct (Z.eq_mul_1 k (Z.pos p) (eq_sym Hk)) as [->| ->]; lia.
Qed.

(* * ** At p = 1 the solenoid is isomorphic to the circle / * ** 在 p = 1 时，螺线管与圆同构 *)

Lemma one_compat@{u} (c : CReal) : circ_eq@{u} (CReal_mult (posR 1) c) c.
Proof. apply circ_eq_of_creal. exact (CReal_mult_1_l c). Qed.

Program Definition const_string_map@{s o so | o < so +} :
  SetoidMorphism@{o o o} Circle_setoid@{o} (SolPoints@{s o so} 1) := {|
  morphism := fun c => (fun _ => c; fun n => one_compat c)
|}.
Next Obligation. intros c c' H n. exact H. Qed.

Lemma const_string_cont@{s o so h | o < so, o < h +} :
  Continuous@{h o} Circle@{o} (Solenoid@{s o so} 1)
    const_string_map@{s o so}.
Proof.
  apply sol_lift_cont. intro j.
  apply (@tcont_respects Circle Circle (@setoid_morphism_id Circle_setoid)).
  - intro x; reflexivity.
  - exact (continuity (@top_id Circle)).
Qed.

Lemma string_one_const@{s o so | o < so +} (x : SolPoints@{s o so} 1)
  (n : nat) :
  circ_eq@{o} (sol_pr 1 0 x) (sol_pr 1 n x).
Proof.
  induction n as [|n IH].
  - apply circ_eq_refl.
  - apply (circ_eq_trans _ _ _ IH). apply circ_eq_sym.
    apply (circ_eq_trans _ (CReal_mult (posR 1) (sol_pr 1 (S n) x))).
    + apply circ_eq_sym. apply one_compat.
    + exact (`2 x n).
Qed.

Definition solenoid_one_iso@{s o so h | o < so, o < h +} :
  @Isomorphism Top@{h o} (Solenoid@{s o so} 1) Circle@{o}.
Proof.
  unshelve refine {| to := sol_leg 1 0;
                     from := @Build_ContinuousMorphism Circle (Solenoid 1)
                               const_string_map const_string_cont |}.
  - intro c. apply circ_eq_refl.
  - intros x n. exact (string_one_const x n).
Defined.

(* The same identification in [PTopCat]. / 在 [PTopCat] 中的相同识别。 *)
Program Definition pconst_string_map@{s o so r | o < so +} :
  SetoidMorphism@{o o o} Circle_setoid@{o}
    (pt_carrier (PSolenoid@{s o so r} 1)) := {|
  morphism := fun c => (fun _ => c; fun n => one_compat c)
|}.
Next Obligation. intros c c' H n. exact H. Qed.

Lemma pconst_string_cont@{s o so r | o < so +} :
  @PCont PCircle@{o} (PSolenoid@{s o so r} 1) pconst_string_map@{s o so r}.
Proof.
  apply (proj2 (PTop_solenoid_universal 1 PCircle _)). intro n.
  apply (@pcont_respects PCircle PCircle (@setoid_morphism_id Circle_setoid)).
  - intro x; reflexivity.
  - exact (pcont (pid PCircle)).
Qed.

Definition PTop_solenoid_one_iso@{s o so r | o < so +} :
  @Isomorphism PTopCat@{o so} (PSolenoid@{s o so r} 1) PCircle@{o}.
Proof.
  unshelve refine {| to := psol_leg 1 0;
                     from := @Build_PMor PCircle (PSolenoid 1)
                               pconst_string_map pconst_string_cont |}.
  - intro c. apply circ_eq_refl.
  - intros x n. exact (string_one_const@{s o so} x n).
Defined.
