Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Complete.Freyd.
Require Import Category.Structure.WellPowered.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.CompHaus.
Require Import Category.Instance.Top.StoneCech.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.SAFT.Characterization.
Require Import Coq.Lists.List.

Generalizable All Variables.

(*
 Why the adjoint functor theorems give no Stone–Čech over [Top]

 Mac Lane, “Categories for the Working Mathematician”, 2nd ed. (GTM 5),
 §V.2 Proposition 3, book p. 114 (maclane:V.2:prop3), Freyd's theorem
 that a small complete category is a preorder, consumed through
 Structure/Complete/Freyd.v; §V.6 and §V.8 as in the header of
 Instance/Top/StoneCech.v, which this file completes.
 nLab: https://ncatlab.org/nlab/show/complete+small+category
 nLab: https://ncatlab.org/nlab/show/Stone-Cech+compactification

 BACKGROUND.  Freyd's observation (Structure/Complete/Freyd.v's header):
 were a category with products indexed by its own arrow collection K to
 carry two distinct parallel arrows, the 2^K choices between them would
 give 2^K arrows into the K-fold power, more than the K arrows there are.
 So completeness in the book's sense is a property of LARGE categories,
 and the adjoint functor theorems ask for it at shapes the size of the
 homs.  Instance/Top/StoneCech.v's header explains why [Top] and
 [CompHaus] are small at their own hom universe: their homs sit strictly
 above the points (o < h), and a whole space is a [TopSpace@{o}] of type
 [Type@{o+1}], at or below h.  This file turns that into theorems.
 Nothing here is an axiom.  Informative excluded middle ([IEM],
 Instance/Sets/Classifier/OneLevel.v) and arrow indices ([ArrowIndex],
 Structure/Complete/Freyd.v) are hypotheses; [IEM] holds classically,
 and under it an [ArrowIndex] exists ([canonical_ArrowIndex] of
 [ObjDecEq_of_IEM]).

 WHAT IS REFUTED.
 (1) Completeness.  [CompHaus_not_complete]: given an [ArrowIndex] of
 [CompHaus] at shape universe [s], [Complete@{r s h c} CompHaus] is
 false.  The two points [sc_pt_bool true] and [sc_pt_bool false] of
 the two-point discrete space are told apart by evaluation at the
 point ([sc_eval_pt]), constructively, and Freyd's core
 [freyd_no_separated_pair] refutes the power of [Bool_CH] at the index
 that completeness supplies ([complete_iprod]).
 [CompHaus_not_complete_IEM]: under [IEM], at every shape universe
 with [c <= s] and [h <= s], which includes the one GAFT uses at
 [CompHaus_Forget] (all four universes [h]) and every one SAFT uses at
 [CompHaus_Incl] with the tree's well-powering (see (3)), at the
 instances COVERAGE records.
 [Top_not_complete] and [Top_not_complete_IEM]: the same for [Top], at
 every [s] with [h <= s], so the hypothesis [HT : Complete Top] of
 Instance/Top/CompHaus.v's [CompHaus_Complete_of] is refuted at those
 shapes as well (that file's (D) carries the correction).
 [CompHaus_ArrowIndex_of_Top]: an arrow index of [Top] at [s] is one
 of [CompHaus] at [s], at every universe [c >= h] of its objects
 (About), because [Sub]'s homs are [Top]'s paired with [True] and the
 index never mentions an object.  Through it, applied to
 [canonical_ArrowIndex] of [Top], [CompHaus_not_complete_IEM_below]
 refutes [Complete@{r s h c} CompHaus] under [IEM] at every shape
 universe with [h <= s], the shapes below the objects included, and
 [CompHaus_not_complete_IEM_above] is its case at GAFT's shape
 [Complete@{h h h c}] with the objects at or above the homs.  COVERAGE
 below records which instances each form reaches.
 (2) The adjunction at [CompHaus_Forget].
 [large_universal_arrow_refuted]: there is no universal arrow from
 the arrow-index set [KSet AI], at the hom universe, to
 [CompHaus_Forget].  The unique extensions along it of the maps
 φ : K → bool are arrows from the universal object to [Bool_CH],
 each encoded as an element of K; reading them back at the unit
 gives a surjection K → (K → bool), which Freyd.v's
 [freyd_cantor_bool] refutes.  [StoneCech_adjunction_refuted_IEM]:
 under [IEM], at the instance with the objects of [CompHaus] at its
 hom universe [h], no functor [F : Sets@{h s} ⟶ CompHaus] is left
 adjoint to [CompHaus_Forget], which is the type
 [GAFT_CompHaus_only_complete] concludes.
 [StoneCech_adjunction_refuted_IEM_above]: the same at every object
 universe [c] at or above [h], at the instances COVERAGE records,
 through [CompHaus_ArrowIndex_of_Top]; below [h] the adjunction is
 not formable, [CompHaus_Forget] carrying [h <= c] (About).  The
 universal arrows at SMALL sets are untouched:
 Instance/Top/StoneCech.v's [StoneCech_finite] builds them at every
 finitely enumerable setoid at the points' universe; the refutation
 needs a set at the hom universe, and the domain [Sets@{h s}] of any
 left adjoint to [CompHaus_Forget] contains one.  The §V.8 adjunction
 at [CompHaus_Incl] is NOT refuted, and classically it holds: the
 domain [Top@{h o}] of a left adjoint to the inclusion has its
 points at [o], strictly below [h], so it offers no object as large
 as the arrow collection and the argument does not apply.  Only
 SAFT's route to that adjunction is vacuous, by (3).
 (3) The vacuity pairs, each consuming ONE completeness hypothesis twice:
 [GAFT_CompHaus_IEM_vacuous] ([GAFT_CompHaus_only_complete] against
 [CompHaus_not_complete_IEM]), and [SAFT_Incl_vacuous] and
 [SAFT_Incl_IEM_vacuous] (Adjunction/SAFT/Characterization.v's
 [SAFT_wellpowered] at [CompHaus_Incl], against the refutation by an
 index or by [IEM]).  The SAFT side's reduction is recorded as well:
 [CompHaus_WellPowered] is Structure/WellPowered.v's [trivial_small]
 at [CompHaus] (a category whose objects fit at its hom universe is
 well-powered by the trivial index), and [SAFT_CompHaus_Incl] is SAFT
 at the inclusion with well-poweredness discharged, three hypotheses
 remaining: completeness, continuity and a cogenerator.  Discharging
 it forces [c = h] (a block equation, measured by About with [c] and
 [h] named separately; Test/ProbeStoneCech455.v pins its
 consequences), so every shape universe SAFT accepts there satisfies
 [c <= s] and [h <= s], and (1)'s [IEM] form covers it at the
 instances COVERAGE records.  [SAFT_CompHaus_Incl] is a conditional
 at more instances than those: it is accepted with the proof slot
 below the objects' universe, and with the fourteenth and fifteenth
 slots below the points' universe, where every refutation here is
 refused (measured by #455's review), and there its completeness
 premise stays classically false, the objects' points still sitting
 at [o] (a meta-argument; NOT DELIVERED).  The two halves of the
 equation have different sources.  [c <= h] is
 [CompHaus_WellPowered]'s: Structure/WellPowered.v's [WellPowered]
 declares the objects at or below its index, and [trivial_small]
 indexes at the hom universe.  [h <= c] is the inclusion's, under ANY
 well-powering: [CompHaus_Incl] carries it (About), and SAFT at the
 inclusion with a well-powering hypothesis is refused at [c < h] as
 well (the probe's N19).  Under a well-powering other than
 [CompHaus_WellPowered] the shape can lie below the objects, and
 [SAFT_Incl_IEM_vacuous_below] covers that: it consumes (1)'s
 [CompHaus_not_complete_IEM_below], at every shape universe SAFT
 accepts at the inclusion, at the instances COVERAGE records.  On
 the GAFT side, [taut_sols] fits GAFT
 only with the objects at [h] (the probe's N9), so
 [GAFT_CompHaus_IEM_vacuous_above] takes the solution sets as a
 hypothesis and pairs GAFT at [CompHaus_Forget] against
 [CompHaus_not_complete_IEM_above] at every object universe at or
 above the homs.
 (4) An obstruction with no hypothesis beyond completeness (no [IEM],
 no arrow index).  [big_inj] and [big_inj_injective]: from
 [Complete@{r s h c} CompHaus] alone, an injection of
 [obj[CompHaus] → bool] into the points of a single space, the power
 of [Bool_CH] over all objects.  The index is the object type of the
 very category [comp] is about: the local definition [C := CompHaus]
 ties the two, and the block carries [c <= s].  Written with
 [obj[CompHaus]] in both places instead, the two elaborate at
 separate instances and the block has no [c <= s] (measured by
 About; Test/ProbeStoneCech455.v pins its consequences), so the
 index could be
 the objects of a smaller [CompHaus].  In a set-theoretic model
 where the points' universe is a Grothendieck universe V_κ, every
 inhabited set in V_κ, carried with the total equivalence, is a
 compact Hausdorff space (compact by one index, separated
 vacuously), so there are at least κ objects, while the points of
 one space form a set below κ; by Cantor no such injection exists,
 and [Complete@{r s h c} CompHaus] is false there.  That is a
 meta-argument, not a theorem of this file: the tree has no cardinal
 arithmetic, and the injection is what is proved.
 (5) The cogenerator premise.  [CompHaus_cogenerator_stable_DNE]: any
 [Cogenerator CompHaus] (Adjunction/SAFT.v) whose members have
 ¬¬-stable equality of points yields double-negation elimination for
 every proposition.  The gadget is [YP_CH P], the two-point discrete
 space whose equality is [x = y ∨ P] ([sc_YP]), compact and Hausdorff
 with no hypothesis ([Discrete_CH] of [sc_yp_FinEnum]).  Under ¬¬P the
 cogenerator cannot tell the identity of [YP_CH P] from the constant
 map [sc_yp_const], so the two agree, and at the point [false] that
 agreement is [P].  It is the [CompHaus] analogue of
 Instance/Mod/Cogenerator.v's [cogenerator_stable_DNE] for [Ab]
 (#454), and it reads the same way: classically it refutes nothing,
 but an axiom-free cogenerating family with ¬¬-stable members, the
 interval among the candidates, would prove DNE.
 [CompHaus_point_separator_stable_DNE] is the case of a single
 space: a [K] whose maps separate the points of EVERY compact
 Hausdorff space, which is the premise of Instance/Top/StoneCech.v's
 [KSeparated_of_unit_injective], yields the same principle when its
 points have ¬¬-stable equality, by the same gadget at the points
 [true] and [false] of [YP_CH P].

 STRENGTHS.  (1) and (2) end in [False], except
 [CompHaus_ArrowIndex_of_Top], which is data whose decoding law is [≈]
 of arrows; (3) are pairs whose second component is [False]; (4)
 concludes Leibniz equality of two boolean families at every object
 from [≈] of their images; both theorems of (5) conclude
 ∀ P : Prop, ¬¬P → P.

 UNIVERSES, measured with [Set Printing Universes. About …], stdlib
 bounds left out; [o] the points, [h] the homs, [c] the objects of
 [CompHaus], [s] and [r] a shape and its limit, [e] the level of [IEM].

 CompHaus_not_complete@{r s c h …} :
 ArrowIndex@{s c h} CompHaus → ¬ Complete@{r s h c}
 ( * s <= r, h <= r: nothing ties s to c * )
 CompHaus_not_complete_IEM@{e r s c h …} :
 IEM@{e} → ¬ Complete@{r s h c}     ( * c <= s, h <= s, s <= r * )
 Top_not_complete_IEM@{e r s h o} :
 IEM@{e} → ¬ Complete@{r s h h} Top@{h o}   ( * o < h <= s <= r * )
 StoneCech_adjunction_refuted_IEM@{e h s …} :
 IEM@{e} → ¬ ∃ F : Sets@{h s} ⟶ CompHaus, F ⊣ CompHaus_Forget
 ( * h < s; CompHaus's objects at h * )
 CompHaus_ArrowIndex_of_Top@{s h o c …} :
 ArrowIndex@{s h h} Top@{h o} → ArrowIndex@{s c h} CompHaus
 ( * o < h <= c; CompHaus's Top slot at h * )
 CompHaus_not_complete_IEM_below@{e r s c h o …} :
 IEM@{e} → ¬ Complete@{r s h c}  ( * o < h, h <= s <= r, h <= c * )
 CompHaus_not_complete_IEM_above@{e h c …} :
 IEM@{e} → ¬ Complete@{h h h c}     ( * h <= c * )
 StoneCech_adjunction_refuted_IEM_above@{e h s o c …} :
 IEM@{e} → ¬ ∃ F : Sets@{h s} ⟶ CompHaus, F ⊣ CompHaus_Forget
 ( * o < h < s, h <= c; CompHaus's objects at c * )
 big_inj_injective@{r s c h …} : let C := CompHaus in
 ∀ (comp : Complete@{r s h c}) (phi psi : obj[C] → bool), …
 ( * c <= s, s <= r * )

 [IEM@{e}] is free of the category's universes: a decider for [x = y],
 a [Prop], fits any level.  A word-bounded [Set] occurs in none of the
 33 readbacks of this file.

 COVERAGE, measured by applying each [IEM] form at instances of
 [CompHaus] written out slot by slot, the order of the named universes
 declared; Test/ProbeStoneCech455.v pins the boundaries below with
 refusals (N10, N12, N20-N22) and positive controls beside them.
 [CompHaus] carries fifteen universes.  Besides [c] and [h], four matter
 here: the third, [t], the hom universe of the [Top@{t o}] of which it
 is a full subcategory ([t <= c], [t <= h]); the fourth, [p], the
 universe of the proof that a space is compact Hausdorff ([p <= c]);
 and the fourteenth and fifteenth, the universes of the separating
 opens of the Hausdorff proof (Instance/Top.v's [IsHausdorff], whose
 opens are predicates at those universes).  [CompHaus_Forget] and
 [CompHaus_Incl] set [t] to [h] (About), so every statement about
 either functor has [t = h].
 - The adjunction at [CompHaus_Forget] is not formable at [c < h]
 ([CompHaus_Forget] carries [h <= c], About).  At [c = h] both
 [StoneCech_adjunction_refuted_IEM] and
 [StoneCech_adjunction_refuted_IEM_above] apply; at [c > h] only the
 latter (the former is refused there, N12).
 - [Complete@{r s h c} CompHaus]: [CompHaus_not_complete_IEM] applies
 at every [s] with [c <= s] and [h <= s], at every [t];
 [CompHaus_not_complete_IEM_below] at every [s] with [h <= s], at
 [t = h] (so [h <= c]); [CompHaus_not_complete_IEM_above] at GAFT's
 shape, [r = s = h], at [t = h].  Together they reach every [s] with
 [h <= s] except, at an instance with [t < h < c], the shapes below
 [c] (N21).  At [s < h] no [IEM] form here applies; the index forms
 of (1) apply wherever an index at [s] is given.
 - The vacuity pairs follow their refutations:
 [GAFT_CompHaus_IEM_vacuous] at [c = h] and
 [GAFT_CompHaus_IEM_vacuous_above] at every [c >= h];
 [SAFT_Incl_IEM_vacuous] at [c <= s] and
 [SAFT_Incl_IEM_vacuous_below] at every [s] that SAFT accepts at the
 inclusion ([h <= s]).
 - Every form, the older ones included, applies only at [p = c]: the
 blocks of [CompHaus_not_complete], [large_universal_arrow_refuted]
 and the helper [sc_pt_bool] set the proof slot to the objects'
 universe (About), and at [p < c] every application tried is
 refused (N20 for the adjunction).
 - And every form, the index forms included, applies only where the
 fourteenth and fifteenth slots are the points' universe [o], which
 [Bool_CH] and [Point_CH] take from [Discrete_Hausdorff@{h o}]: the
 blocks of [CompHaus_not_complete], [large_universal_arrow_refuted]
 and [sc_pt_bool] set both slots to [o] (About).  Below [o] the
 adjunction's type and the completeness hypothesis are still
 formed, and every application tried is refused (measured by #455's
 review; N22 for [StoneCech_adjunction_refuted_IEM_above], beside
 its control at [o]).

 NON-VACUITY.  [IEM] is classically true, so (1) and (2) refute their
 statements, each at the instances COVERAGE records, in every classical
 model; the [ArrowIndex] forms apply to [canonical_ArrowIndex] of any
 [ObjDecEq CompHaus], or, through [CompHaus_ArrowIndex_of_Top], of any
 [ObjDecEq Top], which is how the [IEM] forms are proved.  (3)'s
 conditionals are accepted with their hypotheses bound, and closed.
 (4) needs only the completeness hypothesis.  The premises of (5) are
 met by no family and no space in the tree, and are met classically
 ([0,1], by Urysohn).

 NOT DELIVERED.  A refutation of completeness with neither an index nor
 [IEM]: thinness of a small complete category is not constructively
 provable (Structure/Complete/Freyd.v's header).  The cardinal argument
 of (4) as a theorem.  Any refutation at an instance whose proof slot
 [p] lies below its object universe, or whose fourteenth and fifteenth
 slots, the Hausdorff proof's opens, lie below the points' universe
 [o], and one of completeness at an instance with [t < h < c] at a
 shape below [c] (COVERAGE); classically those instances are false as
 well, the objects' points still sitting at [o] (a meta-argument).
 #455's review measured what a draft of this paragraph denied: that
 something is refuted at an instance of [CompHaus] whose object
 universe [c] lies above its hom universe [h], that an arrow index at
 [h] does not need the object type itself to fit at [h], and that
 SAFT's completeness premise at [CompHaus_Incl], under a well-powering
 other than [CompHaus_WellPowered] and at a shape universe below the
 objects', is refuted as well, the draft reading the [IEM] form's
 [c <= s] as a limit.  An arrow index of [CompHaus] needs only one of
 [Top], whose objects fit at [h] ([CompHaus_ArrowIndex_of_Top]), [IEM]
 supplies that one through [Top]'s [canonical_ArrowIndex], and
 [StoneCech_adjunction_refuted_IEM_above],
 [CompHaus_not_complete_IEM_above], [CompHaus_not_complete_IEM_below]
 and [SAFT_Incl_IEM_vacuous_below] are those refutations.  What the
 draft measured stands as the scope of the two older constants,
 which apply [canonical_ArrowIndex] to [CompHaus]'s own objects:
 [StoneCech_adjunction_refuted_IEM] is refused applied at
 [CompHaus : Category@{c h h}] under [h < c] (“universe
 inconsistency: Cannot enforce c = h because h < c”), and
 [CompHaus_not_complete_IEM] is refused at GAFT's shape
 [Complete@{h h h c}], needing [c <= s].  Anything over the
 Prop-valued re-encoding (#1328), and Stone–Čech itself (#1329).
 CORRECTION (#458): the re-run of this file's completeness refutations
 over the Prop-valued [PTopCat] is Instance/Top/Complete/Refutations.v's
 and their colimit duals are Instance/Top/Cocomplete/Refutations.v's,
 with [Top_not_cocomplete_Freyd] there the dual of [Top_not_complete]
 here; [PCompHaus] and Stone–Čech stay with #1328 and #1329.  And
 Instance/Top/Complete/Refutations.v carries [Top_not_complete_IEM]
 and [CompHaus_not_complete_IEM_below] below the hom universe, where
 COVERAGE records that no [IEM] form here applies, to every shape
 universe strictly above the points: [Top_not_complete_below_IEM] and
 [CompHaus_not_complete_below_IEM], through an arrow index of [Top]
 moved between hom universes ([Top_ArrowIndex_transport]).

 COUNTS.  33 constants here (18 [Definition], 4 [Lemma], 11 [Theorem]),
 all closed under the global context by their fully qualified names,
 [Print Module] listing exactly these 33.  One proof ends [Defined], and
 it is load-bearing: flipping [sc_phi_map] alone to [Qed], the proof of
 [large_universal_arrow_refuted] is refused.  Closure 153 modules
 excluding self: Instance/Sets/Classifier/OneLevel.v costs 15 at the
 margin ([IEM] lives there), Structure/Complete/Freyd.v 11,
 Adjunction/SAFT/Characterization.v 3, Instance/Top/StoneCech.v 1, each
 of the other fifteen [Category.*] [Require]s 0 (each dropped alone). 

 --------
 为什么伴随函子定理不能在 [Top] 上给出 Stone–Čech

 Mac Lane, 《为工作数学家而作的范畴论》，第2版（GTM 5），
 §V.2 命题 3，第114页（maclane:V.2:prop3），Freyd 的定理
 表明小的完全范畴是一个预序，通过
 Structure/Complete/Freyd.v 使用；§V.6 和 §V.8 如
 Instance/Top/StoneCech.v 的标题所示，本文件完成该部分。
 nLab: https://ncatlab.org/nlab/show/complete+small+category
 nLab: https://ncatlab.org/nlab/show/Stone-Cech+compactification背景。Freyd 的观察（Structure/Complete/Freyd.v 的头部）：
 是一个带有由其自身箭头集合 K 索引的积的范畴，以
 承载两个不同的平行箭头，它们之间的 2^K 种选择会
 给出进入 K 倍积的 2^K 条箭头，超过那里存在的 K 条箭头。因此，从书中的意义上讲，完备性是大范畴的一个性质，而伴随函子定理要求它在同态的大小范围内成立。Instance/Top/StoneCech.v 的头部解释了为什么 [Top] 和 [CompHaus] 在它们自身的同态宇宙中是小的：它们的同态严格位于点之上（o < h），而整个空间是类型为 [Type@{o+1}] 的 [TopSpace@{o}]，位于 h 或以下。本文件将其转化为定理。这里没有任何内容是公理。信息性排中（[IEM]，Instance/Sets/Classifier/OneLevel.v）和箭头索引（[ArrowIndex]，Structure/Complete/Freyd.v）是假设；[IEM] 在经典逻辑下成立，并且在其条件下存在一个 [ArrowIndex]（[canonical_ArrowIndex] 的 [ObjDecEq_of_IEM]）。什么被驳斥了。(1) 完备性。[CompHaus_not_complete]：给定一个[ArrowIndex]在形状宇宙[s]的[CompHaus]，[Complete@{r s h c} CompHaus]是假的。两个点[sc_pt_bool true]和[sc_pt_bool false]的两点离散空间可以通过在点([sc_eval_pt])处的评估被区分出来，从构造上讲，Freyd的核心[freyd_no_separated_pair]在由完备性提供的索引([complete_iprod])处驳斥了[Bool_CH]的幂。[CompHaus_not_complete_IEM]：在[IEM]下，在每个具有[c <= s]和[h <= s]的形状宇宙中，其中包括GAFT在[CompHaus_Forget]使用的那个(所有四个宇宙[h])以及每个SAFT在[CompHaus_Incl]和树的良幂性(见(3))使用的宇宙，在COVERAGE记录的实例处。[Top_not_complete] 和 [Top_not_complete_IEM]：对于 [Top] 也是一样，在每个 [s] 上有 [h <= s]，因此 Instance/Top/CompHaus.v 的 [CompHaus_Complete_of] 的假设 [HT : Complete Top] 在那些形状上也被驳斥了（该文件的 (D) 包含了更正）。[CompHaus_ArrowIndex_of_Top]：在 [s] 上的 [Top] 的箭头索引是 [s] 上 [CompHaus] 的一个，在其对象 (About) 的每个宇宙 [c >= h] 上，因 [Sub] 的同态是与 [True] 配对的 [Top]，并且索引从未提到对象。通过将其应用于 [Top] 的 [canonical_ArrowIndex]，[CompHaus_not_complete_IEM_below] 在每个带有 [h <= s] 的形状宇宙下，驳斥 [Complete@{r s h c} CompHaus] 在 [IEM] 下，包括对象下的形状，而 [CompHaus_not_complete_IEM_above] 是其在 GAFT 的形状 [Complete@{h h h c}] 上的情况，其中对象位于同态的上方或同态上。覆盖范围
 以下记录了每个形式达到的实例。(2) 在 [CompHaus_Forget] . [large_universal_arrow_refuted] 处的附加：从箭头指数集 [KSet AI] 到同态宇宙 [CompHaus_Forget] 没有通用箭头。沿着它的映射 φ : K → bool 的唯一扩展是从通用对象到 [Bool_CH] 的箭头，每一个都被编码为 K 的一个元素；在单位处读取它们会得到一个 K → (K → bool) 的满射，Freyd.v 的 [freyd_cantor_bool] 否定了它。[StoneCech_adjunction_refuted_IEM]：
 在 [IEM] 下，在其同态宇宙 [h] 中具有 [CompHaus] 对象的实例中，没有函子 [F : Sets@{h s} ⟶ CompHaus] 是 [CompHaus_Forget] 的左伴随，而 [CompHaus_Forget] 是类型 [GAFT_CompHaus_only_complete] 所总结的。[StoneCech_adjunction_refuted_IEM_above]：在每个对象上都是相同的
 宇宙 [c] 在 [h] 或之上，在实例 COVERAGE 记录中，
 通过 [CompHaus_ArrowIndex_of_Top]；在 [h] 以下，伴随不可形成，[CompHaus_Forget] 携带 [h <= c]（关于）。
 小集合上的通用箭头未被触动：
 Instance/Top/StoneCech.v 的 [StoneCech_finite] 在每个有限可数的集合值上的点的宇宙中构建它们；
 驳斥需要在同态宇宙中有一个集合，[Sets@{h s}] 作为 [CompHaus_Forget] 的左伴随的定义域包含一个集合。§V.8 的伴随关系
 在 [CompHaus_Incl] 并未被驳斥，并且在经典意义上成立：包含的左伴随的域 [Top@{h o}] 的点位于 [o]，严格低于 [h]，因此它没有提供像箭头集合那样大的对象，这个论证不适用。只有 SAFT 达到该伴随关系的路线是空的，通过 (3)。（3）空性配对，每个配对消耗一个完备性假设两次：[GAFT_CompHaus_IEM_vacuous]（[GAFT_CompHaus_only_complete] 对抗 [CompHaus_not_complete_IEM]），以及 [SAFT_Incl_vacuous] 和 [SAFT_Incl_IEM_vacuous]（Adjunction/SAFT/Characterization.v 中的 [SAFT_wellpowered] 在 [CompHaus_Incl]，对抗通过索引或 [IEM] 的驳斥）。SAFT 方面的归约也被记录下来：
 [CompHaus_WellPowered] 是 Structure/WellPowered.v 中的 [trivial_small]
 于 [CompHaus]（一个其对象在同宇宙中适合的类别由平凡指标提供幂集能力），并且 [SAFT_CompHaus_Incl] 在包含时是 SAFT，已解决幂集能力，剩下三个假设：完备性、连续性和一个余生成元。解决它会强制 [c = h]（一个区块方程，由 About 用 [c] 和 [h] 分别命名测量；Test/ProbeStoneCech455.v 固定其结果），因此那里的每个形状宇宙被 SAFT 接受都满足 [c <= s] 和 [h <= s]，并且（1）的 [IEM] 形式在 COVERAGE 记录的实例上覆盖它。[SAFT_CompHaus_Incl] 是一个条件，
 在比那些更多的实例中：它在对象的宇宙下方的证明槽中被接受，
 并且在点的宇宙下方的第十四和第十五槽中被接受，这里每个反驳都被拒绝（根据 #455 的审查衡量），在那里它的完整性前提仍然是经典地错误的，对象的点仍然位于 [o]（一个元论证；未交付）。
 方程的两半来源不同。[c <= h] 是 [CompHaus_WellPowered] 的：Structure/WellPowered.v 的 [WellPowered] 声明对象位于其索引处或以下，而 [trivial_small] 在同一宇宙中建立索引。[h <= c] 是包含体，在任何
 井功条件下：[CompHaus_Incl] 携带它（关于），并且在
 具有井功假设的包含体上的 SAFT 在 [c < h] 也被拒绝（探针的 N19）。在除
 [CompHaus_WellPowered] 之外的井功下，该形状可以位于对象下方，而
 [SAFT_Incl_IEM_vacuous_below] 覆盖了这一点：它消耗 (1) 的
 [CompHaus_not_complete_IEM_below]，在每个形状宇宙中 SAFT 在包含体上接受，在实例 COVERAGE 中记录。对于
 GAFT 方面，[taut_sols] 仅在 [h] 上的对象下适配 GAFT（探针的 N9），因此
 [GAFT_CompHaus_IEM_vacuous_above] 将解集作为假设并在 [CompHaus_Forget] 与
 [CompHaus_not_complete_IEM_above] 配对 GAFT，在每个对象宇宙及以上同质映射处。(4) 一个没有超越完备性的假设的阻碍（没有 [IEM]，也没有箭头指数）。[big_inj] 和 [big_inj_injective]：仅从 [Complete@{r s h c} CompHaus] 出发，对 [obj[CompHaus] → Bool 的单射注入到单个空间的点中，即 [Bool_CH] 对所有对象的幂。指数是 [comp] 所涉及的那个范畴的对象类型：局部定义 [C := CompHaus] 将两者联系起来，而该块携带 [c <= s]。改用 [obj[CompHaus] ] 在两个地方书写时，这两个在不同实例中进行展开，并且该块没有 [c <= s]（通过 About 测量；Test/ProbeStoneCech455.v 固定其后果），因此指数可以是较小的 [CompHaus] 的对象。在一个集合论模型中，
 其中点的宇宙是一个格罗滕迪克宇宙 V_κ，V_κ 中的每个有元素的集合，配备完全等价关系，都是紧豪斯多夫空间（通过一个指标紧致，分离性空洞满足），因此至少存在 κ 个对象，而一个空间的点形成一个小于 κ 的集合；根据康托尔，没有这样的单射存在，因此 [Complete@{r s h c} CompHaus] 在那里是假的。也就是说，这是一个元论证，而不是本文件的定理：该树没有基数算术，单射是被证明的内容。 
 (5) 借助生成器前提。[CompHaus_cogenerator_stable_DNE]：任何成员具有点的 ¬¬-稳定相等性的 [Cogenerator CompHaus]（Adjunction/SAFT.v）都会导致每个命题的双重否定消去。该小工具是 [YP_CH P]，具有两个点的离散空间，其等式是 [x = y ∨ P]（[sc_YP]），紧致且 Hausdorff，无需假设（[Discrete_CH] 的 [sc_yp_FinEnum]）。在 ¬¬P 下，余生成元无法将 [YP_CH P] 的身份与常值映射 [sc_yp_const] 区分开来，因此二者相同，并且在点 [false] 上，这种一致性是 [P]。它是 Instance/Mod/Cogenerator.v 中 [cogenerator_stable_DNE] 对于 [Ab]（#454）的 [CompHaus] 类比，并且阅读方式相同：在经典情况下它并不驳斥任何东西，但一个无公理且具有 ¬¬-稳定成员的余生成族，在候选者之间的区间，将证明 DNE。[CompHaus_point_separator_stable_DNE] 是单空间的情况：一个 [K]，其映射分离每个紧豪斯多夫空间的点，这是 Instance/Top/StoneCech.v 的 [KSeparated_of_unit_injective] 的前提，当其点具有 ¬¬-稳定等式时，通过相同的装置在 [YP_CH P] 的 [true] 和 [false] 点上产生相同的原理。

 优点。(1) 和 (2) 以 [False] 结束，除了 [CompHaus_ArrowIndex_of_Top]，它是其箭头的解码法则为 [≈] 的数据；(3) 是其第二个分量为 [False] 的对；(4) 根据它们像的 [≈]，得出每个对象上两个布尔族的 Leibniz 等式；(5) 的两个定理都得出 ∀ P : Prop, ¬¬P → P。宇宙，用 [Set Printing Universes. About …] 测量，stdlib 边界被省略；[o] 点，[h] 同态，[c] [CompHaus] 的对象，[s] 和 [r] 一个形状及其极限，[e] [IEM] 的水平。CompHaus_not_complete@{r s c h …} ：
 ArrowIndex@{s c h} CompHaus → ¬ Complete@{r s h c}
 （* s <= r, h <= r: 没有什么将 s 与 c 联系起来 *）
 CompHaus_not_complete_IEM@{e r s c h …} ：
 IEM@{e} → ¬ Complete@{r s h c}     （* c <= s, h <= s, s <= r *）
 Top_not_complete_IEM@{e r s h o} ：
 IEM@{e} → ¬ Complete@{r s h h} Top@{h o}   （* o < h <= s <= r *）
 StoneCech_adjunction_refuted_IEM@{e h s …} ：
 IEM@{e} → ¬ ∃ F : Sets@{h s} ⟶ CompHaus, F ⊣ CompHaus_Forget
 （* h < s; CompHaus 在 h 层的对象 *）
 CompHaus_ArrowIndex_of_Top@{s h o c …} ：
 ArrowIndex@{s h h} Top@{h o} → ArrowIndex@{s c h} CompHaus
 （* o < h <= c; CompHaus 在 h 层的 Top 插槽 *）
 CompHaus_not_complete_IEM_below@{e r s c h o …} ：
 IEM@{e} → ¬ Complete@{r s h c}  （* o < h, h <= s <= r, h <= c *）
 CompHaus_not_complete_IEM_above@{e h c …} :
 IEM@{e} → ¬ Complete@{h h h c}     ( * h <= c * )
 StoneCech_adjunction_refuted_IEM_above@{e h s o c …} :
 IEM@{e} → ¬ ∃ F : Sets@{h s} ⟶ CompHaus, F ⊣ CompHaus_Forget
 ( * o < h < s, h <= c; CompHaus 的对象在 c * )
 big_inj_injective@{r s c h …} : let C := CompHaus in
 ∀ (comp : Complete@{r s h c}) (phi psi : obj [C]  → bool), …
 ( * c <= s, s <= r * )[IEM@{e}] 不属于该类别的任何宇宙：是 [x = y] 的决定者，[Prop]，适合任何级别。一个以单词为界的 [Set] 在本文件的 33 个回读中都没有出现。覆盖范围，通过在[CompHaus]的每一写出槽位上应用每个[IEM]形式来测量，按声明的命名宇宙顺序；Test/ProbeStoneCech455.v在下方用拒绝（N10、N12、N20-N22）和旁边的阳性对照固定边界。[CompHaus]包含十五个宇宙。除了[c]和[h]之外，这里还有四个实体：第三个，[t]，是[Top@{t o}]的同构宇宙，它是后者的完全子范畴（[t <= c]，[t <= h]）；第四个，[p]，是证明空间是紧豪斯多夫的宇宙（[p <= c]）；以及第十四和第十五个，是豪斯多夫证明的分离开集的宇宙（Instance/Top.v的[IsHausdorff]，其开集是在这些宇宙上的谓词）。[CompHaus_Forget] 和 [CompHaus_Incl] 将 [t] 设置为 [h]（关于），所以每一个关于任一函子（functor）的陈述都有 [t = h]。在 [CompHaus_Forget] 的附加（adjunction）在 [c < h] 处不可形成（[CompHaus_Forget] 带有 [h <= c]，关于）。在 [c = h]，两者 [StoneCech_adjunction_refuted_IEM] 和 [StoneCech_adjunction_refuted_IEM_above] 都适用；在 [c > h]，仅后者适用（前者在那里被拒绝，N12）。- [Complete@{r s h c} CompHaus]：[CompHaus_not_complete_IEM] 在每一个带有 [c <= s] 和 [h <= s] 的 [s] 上都适用，在每一个 [t] 上适用；[CompHaus_not_complete_IEM_below] 在每一个带有 [h <= s] 的 [s] 上适用，在 [t = h] 上适用（所以 [h <= c]）；[CompHaus_not_complete_IEM_above] 在 GAFT 的形状上，[r = s = h]，在 [t = h]。它们一起覆盖每一个带有 [h <= s] 的 [s]，但在一个带有 [t < h < c] 的实例中，[c] 以下的形状除外（N21）。在 [s < h] 处没有 [IEM] 表格适用；(1) 的索引形式在 [s] 提供索引的任何地方适用。- 空对跟随它们的反驳：[GAFT_CompHaus_IEM_vacuous] 在 [c = h] 处，以及 [GAFT_CompHaus_IEM_vacuous_above] 在每个 [c >= h] 处；[SAFT_Incl_IEM_vacuous] 在 [c <= s] 处，以及 [SAFT_Incl_IEM_vacuous_below] 在每个 [s] 处，SAFT 在包含 ([h <= s]) 时接受。- 每个表格，包括较旧的表格，仅适用于 [p = c]：[CompHaus_not_complete]、[large_universal_arrow_refuted] 的区块以及辅助 [sc_pt_bool] 将证明槽设置为对象的宇宙（About），并且在 [p < c] 处，每次尝试应用都会被拒绝（附加的 N20）。- 并且每种形式，包括索引形式，仅适用于第十四和第十五个位置是点的宇宙 [o] 的情况，而 [Bool_CH] 和 [Point_CH] 则从 [Discrete_Hausdorff@{h o}] 获取：[CompHaus_not_complete]、[large_universal_arrow_refuted] 和 [sc_pt_bool] 的块都将这两个位置设为 [o]（关于）。在 [o] 下面，附加类型和完整性假设仍然形成，并且每次尝试应用都被拒绝（由 #455 的审查衡量；对于 [StoneCech_adjunction_refuted_IEM_above] 为 N22，此外还有其在 [o] 的控制）。非空性。[IEM] 在经典上为真，因此 (1) 和 (2) 在每一个经典模型中，在 COVERAGE 记录的实例上反驳了它们的陈述；[ArrowIndex] 形式适用于任何 [ObjDecEq CompHaus] 的 [canonical_ArrowIndex]，或者通过 [CompHaus_ArrowIndex_of_Top]，适用于任何 [ObjDecEq Top]，这就是 [IEM] 形式被证明的方式。（3）的条件句在其假设被绑定并封闭的情况下被接受。（4）仅需要完备性假设。（5）的前提在树中的任何族和空间上都不满足，并且在经典上满足（[0,1]，由乌里松证明）。未交付。对完整性的反驳，没有索引，也没有
 [IEM]：一个小完全范畴的稀薄性在构造上不可证明（Structure/Complete/Freyd.v 的标题）。
 (4) 的基数论作为定理。在其实例上进行的任何反驳，其证明槽
 [p] 位于其对象宇宙下方，或其第十四和第十五槽，即 Hausdorff 证明的打开槽，位于点的宇宙
 [o] 下，并且在一个实例上对完整性进行反驳，其中 [t < h < c] 位于
 [c] 以下的形状上（覆盖范围）；从经典意义上讲，这些实例也是错误的，对象的点仍然位于 [o]（一个元论证）。#455 的评论衡量了这个段落草稿否认的内容：即在 [CompHaus] 的一个实例上某事被驳斥，其对象宇宙 [c] 位于其同类宇宙 [h] 之上，一个箭头索引在 [h] 不需要对象类型本身适配 [h]，而且 SAFT 在 [CompHaus_Incl] 的完整性前提，在一个不同于 [CompHaus_WellPowered] 的良好赋能下并且位于低于对象的形状宇宙里，也被驳斥，草稿将 [IEM] 形式的 [c <= s] 视为极限。[CompHaus] 的一个箭头索引只需要 [Top] 中的一个，其对象适配 [h]（[CompHaus_ArrowIndex_of_Top]），[IEM] 通过 [Top] 的 [canonical_ArrowIndex] 提供了那个对象，而 [StoneCech_adjunction_refuted_IEM_above]、[CompHaus_not_complete_IEM_above]、[CompHaus_not_complete_IEM_below] 和 [SAFT_Incl_IEM_vacuous_below] 就是那些驳斥。草案测量所表示的范围是两个较老常数的范围，它们将 [canonical_ArrowIndex] 应用于 [CompHaus] 自身的对象：
 [StoneCech_adjunction_refuted_IEM] 在 [CompHaus : Category@{c h h}] 下根据 [h < c] 被拒绝应用（“宇宙不一致：不能强制 c = h 因为 h < c”），并且 [CompHaus_not_complete_IEM] 在 GAFT 的形状 [Complete@{h h h c}] 被拒绝，需要 [c <= s]。超过 Prop 值重编码（#1328）以及 Stone–Čech 本身（#1329）。更正（#458）：在 Prop 值的 [PTopCat] 上重新运行此文件的完整性反驳是 Instance/Top/Complete/Refutations.v 的，及其余极对偶是 Instance/Top/Cocomplete/Refutations.v 的，[Top_not_cocomplete_Freyd] 是这里 [Top_not_complete] 的对偶；[PCompHaus] 和 Stone–Čech 保持 #1328 和 #1329。并且
 Instance/Top/Complete/Refutations.v 在同源宇宙之下携带 [Top_not_complete_IEM] 和 [CompHaus_not_complete_IEM_below]，其中
 COVERAGE 记录了此处没有 [IEM] 形式适用，适用于每个严格高于以下点的形状宇宙：[Top_not_complete_below_IEM] 和 [CompHaus_not_complete_below_IEM]，通过在同源宇宙之间移动的箭头索引 [Top]（[Top_ArrowIndex_transport]）。计数。这里有33个常量（18个[Definition]，4个[Lemma]，11个[Theorem]），
 所有这些在其完全限定名称下都在全局上下文中闭合，
 [Print Module] 列出了这33个中的每一个。一个证明以 [Defined] 结束，且它是承重的：仅将 [sc_phi_map] 翻转为 [Qed]，[large_universal_arrow_refuted] 的证明会被拒绝。闭包 153 个模块
 排除自身：Instance/Sets/Classifier/OneLevel.v 在边际花费 15（[IEM] 就在这里），Structure/Complete/Freyd.v 11，Adjunction/SAFT/Characterization.v 3，Instance/Top/StoneCech.v 1，其余十五个 [Category.*] [Require] 为 0（每个单独删除）。
*)

(* * * The two points of the discrete two-point space / * * 离散二维空间的两个点 *)

Definition sc_pt_bool@{o +} (b : bool) : Point_CH ~{CompHaus}~> Bool_CH :=
  (top_point Bool_Discrete@{o} b; I).

Definition sc_eval_pt@{c h +}
  (f : Point_CH ~{CompHaus : Category@{c h h}}~> Bool_CH) : bool :=
  continuous_map (`1 f) ttt.

Lemma sc_eval_pt_resp@{c h +}
  (u v : Point_CH ~{CompHaus : Category@{c h h}}~> Bool_CH) :
  u ≈ v → sc_eval_pt u = sc_eval_pt v.
Proof. intro H. exact (H ttt). Qed.

(* * * Completeness at the hom universe is refuted (Freyd's core) / * * Hom 宇宙的完备性被反驳（弗雷德的核心） *)

Theorem CompHaus_not_complete@{r s c h +}
  (AI : ArrowIndex@{s c h} CompHaus)
  (comp : @Complete@{r s h c} CompHaus) : False.
Proof.
  exact (freyd_no_separated_pair AI (sc_pt_bool true) (sc_pt_bool false) _ _
           (complete_iprod comp (fun _ : ai_index AI => Bool_CH))
           sc_eval_pt sc_eval_pt_resp eq_refl eq_refl).
Qed.

(* Informative excluded middle decides equality of objects. / 信息上的排中法决定对象的平等性。 *)
Definition ObjDecEq_of_IEM@{e c h +} (E : IEM@{e}) (C : Category@{c h h}) :
  ObjDecEq C :=
  fun x y => match E (x = y) with
             | inl e => left e
             | inr n => right n
             end.

Theorem CompHaus_not_complete_IEM@{e r s c h +} (E : IEM@{e})
  (comp : @Complete@{r s h c} CompHaus) : False.
Proof.
  exact (CompHaus_not_complete
           (canonical_ArrowIndex (ObjDecEq_of_IEM E CompHaus)) comp).
Qed.

Theorem Top_not_complete@{r s h o +} (AI : ArrowIndex@{s h h} Top@{h o})
  (comp : @Complete@{r s h h} Top@{h o}) : False.
Proof.
  exact (freyd_no_separated_pair AI
           (top_point Bool_Discrete true) (top_point Bool_Discrete false) _ _
           (complete_iprod comp (fun _ : ai_index AI => Bool_Discrete))
           (fun h => continuous_map h ttt) (fun u v H => H ttt)
           eq_refl eq_refl).
Qed.

Theorem Top_not_complete_IEM@{e r s h o +} (E : IEM@{e})
  (comp : @Complete@{r s h h} Top@{h o}) : False.
Proof.
  exact (Top_not_complete
           (canonical_ArrowIndex (ObjDecEq_of_IEM E Top)) comp).
Qed.

(* * * Above the hom universe: an arrow index transported from [Top] / * * 在 hom 宇宙之上：一根从 [Top] 运来的箭头索引 *)

(*
 The homs of the full subcategory are [Top]'s paired with [True]
 ([Sub]), so an arrow index of [Top] indexes the arrows of [CompHaus] at
 every universe of its objects at or above the homs: the index never
 mentions them. 

 --------
 完全集子范畴的 Hom 是  [Top] 与  [True] ( [Sub] ) 配对的，所以一个箭头索引  [Top] 对应于  [CompHaus] 的箭头在其对象所在的所有宇宙中（在 Hom 之上）：该索引从不提及它们。
*)
Definition CompHaus_ArrowIndex_of_Top@{s h o c +}
  (AIT : ArrowIndex@{s h h} Top@{h o}) :
  ArrowIndex@{s c h} (CompHaus : Category@{c h h}) :=
  @Build_ArrowIndex (CompHaus : Category@{c h h}) (ai_index AIT)
    (fun x y f => ai_enc AIT (`1 f))
    (fun x y m d => (ai_dec AIT m (`1 d); I))
    (fun x y f d => ai_dec_enc AIT (`1 f) (`1 d)).

Theorem CompHaus_not_complete_IEM_below@{e r s c h o +} (E : IEM@{e})
  (comp : @Complete@{r s h c} (CompHaus : Category@{c h h})) : False.
Proof.
  exact (CompHaus_not_complete
           (CompHaus_ArrowIndex_of_Top
              (canonical_ArrowIndex@{s h h} (ObjDecEq_of_IEM E Top@{h o})))
           comp).
Qed.

Theorem CompHaus_not_complete_IEM_above@{e h c +} (E : IEM@{e})
  (comp : @Complete@{h h h c} (CompHaus : Category@{c h h})) : False.
Proof. exact (CompHaus_not_complete_IEM_below E comp). Qed.

(* * * The adjunction itself is refuted: a universal arrow at a large set / * * 伴随本身被驳斥：一个大集合上的通用箭头 *)

(* The arrow index of [CompHaus], as a setoid with Leibniz equality. / [CompHaus] 的箭头指数，作为具有莱布尼茨等式的集合论。 *)
Definition KSet@{s c h +} (AI : ArrowIndex@{s c h} CompHaus) :
  SetoidObject@{s s} :=
  {| carrier := ai_index AI; is_setoid := eq_Setoid (ai_index AI) |}.

Definition sc_phi_map@{c h +} (AI : ArrowIndex@{h c h} CompHaus)
  (phi : ai_index AI → bool) :
  KSet AI ~{Sets}~> CompHaus_Forget Bool_CH.
Proof.
  unshelve refine {| morphism := phi |}.
  all: intros a b e; simpl in *; destruct e; reflexivity.
Defined.

Theorem large_universal_arrow_refuted@{c h +}
  (AI : ArrowIndex@{h c h} CompHaus)
  (UA : UniversalArrow (C:=Sets) (KSet AI) CompHaus_Forget) : False.
Proof.
  pose (pm := sc_phi_map AI).
  pose (ext := fun phi => unique_obj (ump_universal_arrows UA (pm phi))).
  pose (dflt := ext (fun _ => true)).
  pose (Fam := fun k i =>
         continuous_map (`1 (ai_dec AI k dflt)) (@arrow _ _ _ _ UA i) : bool).
  apply (freyd_cantor_bool Fam).
  intro phi. exists (ai_enc AI (ext phi)). intro i.
  unfold Fam.
  rewrite (ai_dec_enc AI (ext phi) dflt (@arrow _ _ _ _ UA i)).
  pose proof (unique_property (ump_universal_arrows UA (pm phi)) i) as H.
  simpl in H. symmetry. exact H.
Qed.

Theorem StoneCech_adjunction_refuted_IEM@{e h s +} (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ CompHaus & F ⊣ CompHaus_Forget }) : False.
Proof.
  pose (AI := canonical_ArrowIndex (ObjDecEq_of_IEM E CompHaus)).
  exact (large_universal_arrow_refuted AI
           (universal_arrow_of_adjunction (`2 A) (KSet AI))).
Qed.

(*
 The same at every object universe at or above the homs, through the
 index of [Top]. 

 --------
 在每个在homs及以上的物体宇宙中，通过[Top]的索引。
*)
Theorem StoneCech_adjunction_refuted_IEM_above@{e h s o c +} (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ (CompHaus : Category@{c h h})
       & F ⊣ CompHaus_Forget }) : False.
Proof.
  pose (AI := CompHaus_ArrowIndex_of_Top
                (canonical_ArrowIndex (ObjDecEq_of_IEM E Top@{h o}))).
  exact (large_universal_arrow_refuted AI
           (universal_arrow_of_adjunction (`2 A) (KSet AI))).
Qed.

(* * * GAFT and SAFT consume the refuted hypothesis / * * GAFT 和 SAFT 消耗被驳斥的假设 *)

Definition GAFT_CompHaus_IEM_vacuous@{e h s +} (E : IEM@{e})
  (comp : @Complete@{h h h h} CompHaus) :
  ({ F : Sets@{h s} ⟶ CompHaus & F ⊣ CompHaus_Forget } * False)%type :=
  (GAFT_CompHaus_only_complete comp, CompHaus_not_complete_IEM E comp).

(*
 With the objects at or above the homs [taut_sols] no longer fits GAFT,
 so the solution sets are a hypothesis. 

 --------
 当物体位于或高于homs [taut_sols]时，不再符合GAFT，因此解集是一个假设。
*)
Definition GAFT_CompHaus_IEM_vacuous_above@{e h s c +} (E : IEM@{e})
  (comp : @Complete@{h h h c} (CompHaus : Category@{c h h}))
  (sols : ∀ d : obj[Sets@{h s}], SolutionSet CompHaus_Forget d) :
  ({ F : Sets@{h s} ⟶ (CompHaus : Category@{c h h})
     & F ⊣ CompHaus_Forget } * False)%type :=
  (GAFT CompHaus_Forget comp CompHaus_Forget_PreservesImageLimit sols,
   CompHaus_not_complete_IEM_above E comp).

Definition CompHaus_WellPowered@{c h t +} :
  WellPowered@{c h h h t} (CompHaus : Category@{c h h}) :=
  trivial_small CompHaus.

(*
 SAFT at the inclusion, well-poweredness discharged: three hypotheses
 remain, and the completeness one is refuted under [IEM] at the
 instances COVERAGE records. 

 --------
 在包含时的SAFT，充分性已解除：三个假设仍然存在，而完整性假设在实例COVERAGE记录的[IEM]下被驳回。
*)
Definition SAFT_CompHaus_Incl@{s h +} (comp : @Complete@{s s h h} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl) (G : Cogenerator CompHaus) :
  { F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } :=
  SAFT_wellpowered CompHaus_Incl comp cont G CompHaus_WellPowered.

Definition SAFT_Incl_vacuous@{s c h +} (AI : ArrowIndex@{s c h} CompHaus)
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl)
  (G : Cogenerator CompHaus) (WP : WellPowered CompHaus) :
  ({ F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } * False)%type :=
  (SAFT_wellpowered CompHaus_Incl comp cont G WP,
   CompHaus_not_complete AI comp).

Definition SAFT_Incl_IEM_vacuous@{e s c h +} (E : IEM@{e})
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl)
  (G : Cogenerator CompHaus) (WP : WellPowered CompHaus) :
  ({ F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } * False)%type :=
  (SAFT_wellpowered CompHaus_Incl comp cont G WP,
   CompHaus_not_complete_IEM E comp).

(*
 The same at every shape universe SAFT accepts at the inclusion, the
 shapes below the objects included. 

 --------
 在每个形状宇宙中都是相同的，SAFT在包含时接受，下列形状属于所包含的对象。
*)
Definition SAFT_Incl_IEM_vacuous_below@{e s c h +} (E : IEM@{e})
  (comp : @Complete@{s s h c} (CompHaus : Category@{c h h}))
  (cont : @PreservesImageLimit _ _ CompHaus_Incl)
  (G : Cogenerator CompHaus) (WP : WellPowered CompHaus) :
  ({ F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } * False)%type :=
  (SAFT_wellpowered CompHaus_Incl comp cont G WP,
   CompHaus_not_complete_IEM_below E comp).

(* * * The classical-model obstruction, with no hypothesis beyond completeness / * * 经典模型的障碍，没有超出完备性的假设 *)

(*
 The index is the object type of the category [comp] is about: the local
 definition [C] makes the two one instance. 

 --------
 索引是类别 [comp] 的对象类型：本地定义 [C] 使两个成为一个实例。
*)
Definition big_inj@{r s c h +} (C := CompHaus : Category@{c h h})
  (comp : @Complete@{r s h c} C) (phi : obj[C] → bool) :
  top_carrier (`1 (complete_iprod_obj comp (fun _ : obj[C] => Bool_CH))) :=
  continuous_map
    (`1 (unique_obj
           (iprod_desc (complete_iprod comp (fun _ : obj[C] => Bool_CH))
              (fun j => sc_pt_bool (phi j))))) ttt.

Lemma big_inj_injective@{r s c h +} (C := CompHaus : Category@{c h h})
  (comp : @Complete@{r s h c} C) (phi psi : obj[C] → bool) :
  big_inj comp phi ≈ big_inj comp psi → ∀ j, phi j = psi j.
Proof.
  intros E j.
  pose proof (unique_property
    (iprod_desc (complete_iprod comp (fun _ : obj[C] => Bool_CH))
       (fun j => sc_pt_bool (phi j))) j ttt) as Hp.
  pose proof (unique_property
    (iprod_desc (complete_iprod comp (fun _ : obj[C] => Bool_CH))
       (fun j => sc_pt_bool (psi j))) j ttt) as Hq.
  simpl in Hp, Hq.
  pose proof (proper_morphism
    (continuous_map
       (`1 (complete_iprod_proj comp (fun _ : obj[C] => Bool_CH) j)))
    _ _ E) as Hm.
  simpl in Hm.
  rewrite <- Hp, <- Hq. exact Hm.
Qed.

(* * * A cogenerator of CompHaus with stable members gives DNE / * * 具有稳定成员的 CompHaus 的协同生成器给出 DNE *)

(* The two-point space whose points are identified exactly when [P]. / 这个两点空间，其点恰好在 [P] 时被识别。 *)
Definition sc_yp_equiv@{o +} (P : Prop) (x y : bool) : Type@{o} :=
  (x = y \/ P).

Lemma sc_yp_equiv_Equivalence@{o +} (P : Prop) :
  Equivalence (sc_yp_equiv@{o} P).
Proof.
  unfold sc_yp_equiv; constructor.
  - intro x; left; reflexivity.
  - intros x y [e|p]; [left; symmetry; exact e | right; exact p].
  - intros x y z [e1|p] [e2|p2]; [left; congruence | right | right | right];
      assumption.
Qed.

Definition sc_YP@{o +} (P : Prop) : SetoidObject@{o o} :=
  {| carrier := bool;
     is_setoid := {| equiv := sc_yp_equiv P;
                     setoid_equiv := sc_yp_equiv_Equivalence P |} |}.

Lemma sc_yp_FinEnum@{o +} (P : Prop) :
  FinEnum (sc_YP P : SetoidObject@{o o}).
Proof.
  exists (true :: false :: nil). intros [|].
  - exists true. split; [left; reflexivity | left; reflexivity].
  - exists false. split; [right; left; reflexivity | left; reflexivity].
Qed.

Definition YP_CH@{o +} (P : Prop) : CompHaus :=
  Discrete_CH (sc_YP P : SetoidObject@{o o}) (sc_yp_FinEnum P).

Definition sc_yp_const@{o +} (P : Prop) : YP_CH P ~{CompHaus}~> YP_CH P :=
  (Build_ContinuousMorphism (Discrete_Top@{o o} (sc_YP P))
     (Discrete_Top (sc_YP P))
     (const_morphism (sc_YP P) (sc_YP P) true)
     (fun U _ => open_const (Discrete_Top (sc_YP P)) (U true)); I).

Theorem CompHaus_cogenerator_stable_DNE@{k c h +}
  (G : Cogenerator@{k c h} CompHaus)
  (stable : ∀ j (a b : top_carrier (`1 (cog_obj G j))),
              ((a ≈ b → False) → False) → a ≈ b) :
  ∀ P : Prop, ~~P → P.
Proof.
  intros P nnP.
  assert (H : (@id CompHaus (YP_CH P)) ≈ sc_yp_const P).
  { apply (cog_separates G).
    intros j k b; simpl.
    apply stable; intro Hne.
    apply nnP; intro HP.
    apply Hne.
    apply (proper_morphism (continuous_map (`1 k))).
    right; exact HP. }
  destruct (H false) as [e|p]; [discriminate | exact p].
Qed.

(*
 The case of a single space: a [K] that separates the points of every
 compact Hausdorff space, the premise of Instance/Top/StoneCech.v's
 [KSeparated_of_unit_injective], costs the same when its points have
 ¬¬-stable equality. 

 --------
 单空间的情况：一个 [K]，它分隔每个紧豪斯多夫空间的点，Instance/Top/StoneCech.v 的前提 [KSeparated_of_unit_injective]，当它的点具有 ¬¬-稳定的相等性时，成本相同。
*)
Theorem CompHaus_point_separator_stable_DNE@{c h +}
  (K : (CompHaus : Category@{c h h}))
  (sepK : ∀ (Y : (CompHaus : Category@{c h h})) (p q : top_carrier (`1 Y)),
            (∀ k : Y ~{CompHaus}~> K,
               continuous_map (`1 k) p ≈ continuous_map (`1 k) q) → p ≈ q)
  (stable : ∀ a b : top_carrier (`1 K), ((a ≈ b → False) → False) → a ≈ b) :
  ∀ P : Prop, ~~P → P.
Proof.
  intros P nnP.
  destruct (sepK (YP_CH P) true false) as [e|p]; [| discriminate | exact p].
  intro k. apply stable. intro Hne. apply nnP. intro HP. apply Hne.
  apply (proper_morphism (continuous_map (`1 k))). right. exact HP.
Qed.
