(*
   * * Compact Hausdorff spaces, and the creation of limits

   Mac Lane, Categories for the Working Mathematician, 2nd ed., §V.1
   Exercise 2 (book p. 112, `maclane:V.1:ex2`): the underlying-set functor
   on compact Hausdorff spaces creates limits.  nLab:
   https://ncatlab.org/nlab/show/compact+Hausdorff+space and
   https://ncatlab.org/nlab/show/created+limit.  The classical argument
   has three parts: the product topology on a product of compact
   Hausdorff spaces is compact (Tychonoff) and Hausdorff; a continuous
   bijection from a compact space to a Hausdorff space is a homeomorphism,
   so any other compact Hausdorff topology making the projections
   continuous coincides with the product one; and the two together make
   the lift of a limit unique and limiting.  This file delivers what the
   library's topology can carry of that argument, MEASURES where the rest
   stops, and names the stopping points precisely.

   THREE PREMISES OF THE ISSUE ARE STALE, each re-measured.  The issue's
   "Current state" says there is no category of spaces, no compactness,
   no Hausdorff property and no creation notion.  All four exist:
   [Top] is Instance/Top.v (#259); [IsCompact], [IsHausdorff],
   [CompactHausdorff_Subcategory], [CompactHausdorffSpaces] and
   [CompactHausdorff_Full] are Instance/Top.v, whose own header scopes out exactly the theory asked for here as "out of
   scope for this file"; and [CreatesLimit] is Structure/Limit/Creation.v
   (#406).  So the issue's pinned name [CompHaus] is an ALIAS of an
   existing category, not a construction, and the substance of the
   exercise is the three parts above.

   WHAT IS DELIVERED.
   (A) [CompHaus : Category := CompactHausdorffSpaces], read back at
   [eq_refl]; its inclusion [CompHaus_Incl := Incl Top
   CompactHausdorff_Subcategory] with [CompHaus_Incl_Full] and
   [CompHaus_Incl_Faithful]; the underlying-set functor
   [CompHaus_Forget := Top_Forget ◯ CompHaus_Incl : CompHaus ⟶ Sets]
   with [CompHaus_Forget_Faithful].
   (B) THE BIJECTION THEOREM, constructively and honestly.  For
   [f : X ~{Top}~> Y] with a setoid inverse [g] ([f ∘ g] and [g ∘ f]
   pointwise the identity), [X] compact and [Y] Hausdorff:
   [inverse_open_of_decidable U HU dU : IsOpen Y (fun y => U (g y))]
   for every open [U] of [X] that is DECIDABLE ([dU : ∀ x, U x + ¬U
   x]); [inverse_continuous_of_decidable dec : Continuous Y X g] when
   every open of [X] is; and [compact_hausdorff_bijection_iso dec :
   X ≅[Top] Y].  The decidability is exactly where the classical
   argument decides membership: it covers [X] by [U] together with
   the [f]-preimages of Hausdorff-separating opens around [f c] for
   the points [c] OUTSIDE [U] ([sep_cover_covers], where [dU] decides
   membership; [nbhd_inside] uses it a second time, to decide [U (g
   y')] before deriving the contradiction), takes the finite subcover
   [IsCompact] hands over as
   a list, and intersects the matching separating opens around the
   target point ([nbhd]); that finite intersection is the required
   neighbourhood, and the union of these over the points of the
   preimage is the preimage ([inverse_open_of_decidable]).  [List.In],
   a [Prop], is eliminated only into [False] ([finite_inter_In_False]).
   [IsHausdorff] enters through [sep_nonequal], where [f c ≈ y0] for
   [c] outside [U] would put [c ≈ g y0] inside it — no double-negation
   elimination is needed, contrary to a worry recorded at
   Instance/Top/Kolmogorov.v for the Hausdorff ⟹ T0 direction.
   CAVEAT, disclosed and not claimed necessary: [dec] for ALL opens
   holds for no INHABITED space in the tree — [Discrete_Top]'s opens
   are all the [≈]-respecting predicates ([discrete_open],
   Instance/Top.v), so [dec] there is decidability of every such
   predicate — while the empty space [Empty_Top] (Instance/Top.v)
   satisfies it vacuously and does instantiate both theorems (measured
   by an audit); so the per-open lemma is the form with non-vacuous
   content, and the probe applies it at the one-point space with the
   identity and the whole open.
   (C) THE TRUNCATED PRODUCT TOPOLOGY, the furthest formable point of the
   Tychonoff half.  [Top] has no products: the natural product
   openness predicate — an existential over opens of the two factors —
   lives one universe above the points and is REFUSED at the space's
   level (Test/ProbeCoproduct.v N9, Instance/Top/Homotopy.v).
   Instance/Top/Coproduct.v names one escape hatch it did not
   try, the impredicative truncation [Powerset_squash] of
   Instance/Sets/Powerset.v.  It is tried here: [sq_open W] is "[W]
   respects [≈], and every point of [W] has a SQUASHED box datum
   ([sq_boxdata], a [Type@{o1}] with [o < o1]) inside [W]"; the squash
   is a [Prop], so [sq_open : (sq_carrier → Type@{o}) → Type@{o}] fits,
   and [Top_sq_product X Y : TopSpace@{o}] closes all five topology
   fields (unions and intersections of squashed boxes by [sq_squash_map]
   and [sq_squash_pair]).  Its projections [Top_sq_fst], [Top_sq_snd]
   are continuous (a box [U × whole]).  WHAT STOPS, compiled in the
   probe: the pairing [sq_fork_map f g] exists on points, but its
   continuity would eliminate the squash into the [Type]-valued
   [IsOpen Z] — refused, the eliminator's motive must be a [Prop]
   ("Cannot enforce o <= Prop"), while eliminating into [True] is
   accepted; and the other route, a union over ALL boxes inside [W],
   is refused because [sq_boxdata] sits at [o1] and [open_union]
   indexes at [o].  So [Top_sq_product] has projections but no
   universal property is ESTABLISHED here: the two routes tried are
   refused, and it is not shown that every encoding is refused
   (Instance/Top/Coproduct.v records the same over-read in an
   earlier draft of its own header) — and its compactness (Tychonoff)
   is NOT attempted: its finite subcovers would be [Type]-level data
   extracted from squashed boxes, so it is expected behind the same
   wall by the same argument, asserted rather than compiled. This is a
   measured refinement of Coproduct.v's note: the truncated encoding
   elaborates AND yields a space, and the wall moves to the fork.
   (D) CREATION.  Two facts, one positive and one conditional:
   - The issue's pinned statement [CreatesLimit K CompHaus_Forget] IS
   FORMABLE, for a diagram [K] out of any shape [J] (the probe checks
   it, with [J : Category] left to inference). A survey read
   Instance/Top/Forgetful.v as saying it is not, and that note's
   own last sentence did generalize its stratification claim to
   [Top_Forget] by name — false there, since [Top_Forget] lands in
   [Sets@{h so}], whose hom level is [Top]'s own, so the limit-cone
   predicates apply on both sides; the sentence is corrected in place,
   line-neutrally, in this commit. What is NOT delivered is its proof:
   [creates_lift] must produce a COMPACT HAUSDORFF apex over an
   arbitrary limiting cone of setoids, which is Tychonoff plus the
   Hausdorff property of the lift, and [creates_reflect] must make the
   mediator continuous into the lifted topology, which is the fork wall
   of (C).
   - The generic lemma Construction/Subcategory/Creation.v adds — a FULL
   subcategory whose objects are CLOSED under the ambient limits is
   created into by its inclusion ([sub_CreatesLimit], [sub_Complete]) —
   is applied at [CompactHausdorff_Subcategory] as
   [CompHaus_Incl_CreatesLimit closed K] and [CompHaus_Complete_of
   closed HT], CONDITIONALS on [closed : ClosedUnderLimits
   CompactHausdorff_Subcategory] and [HT : Complete Top]. Both
   hypotheses are unwitnessed in the tree: [Top] has no limits beyond
   [Top_Terminal] to be closed under, and no [Top_Complete] exists. They
   are the statements the exercise's conclusion would follow from,
   stated at the inclusion, not at the forgetful functor.
   CORRECTION (#410): [Top] now has a limit beyond [Top_Terminal],
   Instance/Top/Solenoid.v's [solenoid_limit] over a tower of
   circles; [closed] and [HT] stay unwitnessed.
   CORRECTION (#455): at the shapes the adjoint functor theorems
   use, [HT] is refuted, not merely unwitnessed: at every shape
   universe at or above [Top]'s hom universe, [Complete Top] is
   refuted under informative excluded middle
   (Instance/Top/StoneCech/Refutations.v's [Top_not_complete_IEM]),
   and so is [Complete CompHaus] at every shape universe at or above
   its hom universe, at the instances that file's COVERAGE records
   (the [Top] slot at the hom universe, the proof slot at the object
   universe, the Hausdorff proof's opens at the points' universe):
   [CompHaus_not_complete_IEM] at the shapes at or above its objects
   as well, and [CompHaus_not_complete_IEM_below] at every shape at
   or above the hom universe, the shapes below the objects included.
   At shapes below the hom universe neither is refuted under
   informative excluded middle; the index forms there
   ([Top_not_complete], [CompHaus_not_complete]) apply given an
   index.  #455's review measured what a draft of this correction
   denied, that [Complete CompHaus] at a shape below its object
   universe is refuted: [CompHaus_not_complete_IEM_below] refutes it,
   through an arrow index of [Top].  CORRECTION (#458): at shapes
   below the hom universe both are refuted under informative
   excluded middle as well, at every shape universe strictly above
   the points: Instance/Top/Complete/Refutations.v's
   [Top_not_complete_below_IEM] refutes [Complete Top] there, and
   [CompHaus_not_complete_below_IEM] refutes [Complete CompHaus]
   there, at the instances that Instance/Top/StoneCech/
   Refutations.v's COVERAGE records for
   [CompHaus_not_complete_IEM_below].  Both go through the first
   file's [Top_ArrowIndex_transport], which moves an arrow index
   of [Top] between hom universes; Test/ProbeTopComplete458.v pins
   both at a shape strictly between the points and the homs, where
   #455's [IEM] forms are refused.  At shapes at or below the
   points neither [HT] nor [Complete CompHaus] is refuted.

   NOT DELIVERED, in the issue's own terms.  (a) Tychonoff at ANY index
   generality — not even the binary product has its universal property
   (see (C)); (c) the PROOF of [CreatesLimit K CompHaus_Forget] (see
   (D)); (d) [CompHaus_Complete] unconditionally (the conditional
   [CompHaus_Complete_of] is what stands); a [Cartesian Top]; compactness
   of a SUBSET ([IsCompact] is whole-space); the closed-map form of (B);
   any necessity result for [dec]; any witness of [ClosedUnderLimits]
   (CORRECTION (#461): none over [Top] still; the tree's first witnesses
   are over [PTopCat], Instance/Top/Hausdorff.v's [PSep_closed] and
   [PT3_closed]), or
   an inhabited witness of [dec] for all opens; and nothing registered as
   an [Instance]
   ([CompHaus_Forget_Faithful] and [CompHaus_Incl_Faithful] are lemmas,
   following Structure/Limit/Creation.v's discipline for creation
   witnesses).  The Stone–Čech adjoint and the ultrafilter monad, the
   reasons the roster lists this category (Instance/Roster.v),
   remain as that note leaves them.  CORRECTION (#455): the first is
   settled negatively at the instances that
   Instance/Top/StoneCech/Refutations.v's COVERAGE records (the [Top]
   slot at the hom universe, the proof slot at the object universe, the
   Hausdorff proof's opens at the points' universe).  Under informative
   excluded middle, with the objects of [CompHaus] at its hom universe
   (the instance that Instance/Top/StoneCech.v's
   [GAFT_CompHaus_only_complete] produces) or above it, [CompHaus_Forget]
   has no left adjoint there (Refutations.v's
   [StoneCech_adjunction_refuted_IEM] and
   [StoneCech_adjunction_refuted_IEM_above]); below the hom universe
   the statement is not formable, and at the other instances it stays
   classically false, a meta-argument.  #455's review measured what a
   draft of this correction denied, that the statement is refuted at an
   instance whose object universe lies above the hom universe: the
   second constant refutes it there.  The Stone–Čech left adjoint to
   the inclusion [CompHaus_Incl] is not refuted at all and holds
   classically; #1329 carries it.
   Instance/Top/StoneCech.v builds the universal arrows at finitely
   enumerable sets and §V.8 Exercise 4 at the level of universal
   arrows.

   UNIVERSES, MEASURED OFF BOTH BINDER AND BLOCK OVER ALL 48 CONSTANTS
   OF THIS FILE (and the 9 of Construction/Subcategory/Creation.v).
   ZERO word-bounded [Set] in any of the 57 blocks.  The truncated-product
   constants are the small ones: [Top_sq_product@{o o1} : TopSpace@{o} →
   TopSpace@{o} → TopSpace@{o}] with the single named bound [o < o1] (the
   box datum's level) plus stdlib caps; [Top_sq_fst@{o o1 u}] adds [Top]'s
   hom level [o < u].  The bijection constants carry two block equations:
   [u3 = u1] (the two list universes, [finite_inter]'s and the
   subcover's, on [sep_subcover_covers], [nbhd_inside] — printed there as
   [u1 = u3] —,
   [inverse_open_of_decidable], [inverse_continuous_of_decidable],
   [compact_hausdorff_bijection_iso]) and [u9 = u8] (the open's level is
   the carrier's, on the last two); the forty-three others carry NONE.
   In Creation.v, [sub_lift], [sub_lift_apex], [sub_lift_leg],
   [sub_cone_iso] and [sub_CreatesLimit] carry five equations — [u0 = u11]
   identifies the ambient hom universe with the shape's
   (Structure/Limit/Preservation.v's [IsLimitCone] pin, inherited) and
   [u0 = u13] with [Sub]'s ([Compose] types its three categories at one
   hom universe, so [Incl C S ◯ K] imposes it — an audit isolated the two
   causes), and [u5 = u12], [u6 = u14], [u9 = u10] identify the closure
   hypothesis' quantified shape and [Sub] levels with the diagram's: the
   hypothesis is consumed at the diagram's own universe instance —
   [sub_ReflectsLimitCone] carries the first two only, and
   [ClosedUnderLimits], [sub_CreatesAllLimits], [sub_Complete] none.

   COUNTS.  57/57 constants (48 here: 24 [Definition], 20 [Lemma], 2
   [Theorem], 1 [Example], 1 [Fixpoint]; 9 there: 7 [Definition], 2
   [Example]) closed under the global context with ZERO [Axioms:] lines,
   all in the [make print-assumptions] gate FULLY QUALIFIED; no [Program]
   anywhere.  Seven [Defined]-terminated proofs, FIVE load-bearing by
   flipping each alone to [Qed] and recompiling both files and the probe:
   [Top_sq_product] (this file stops at [sq_fst_continuous]'s statement,
   which needs the product's carrier to unfold), [sq_fst_map] and
   [sq_snd_map] (the projections' continuity proofs unfold the morphism
   field), [compact_hausdorff_bijection_iso] (the probe's readback of its
   forward map), and Creation.v's [sub_lift] (its own [eq_refl] readbacks
   [sub_lift_apex]/[sub_lift_leg]); [sq_fork_map] and [sub_cone_iso] flip
   with everything green and are kept [Defined] by the data convention.
   Closure 52 modules excluding self — Construction/Subcategory/Creation.v
   costs 10 at the margin (it brings Theory/Equivalence/Limit.v),
   Instance/Sets/Powerset.v 3, Instance/Top/Forgetful.v 1, each of the
   other sixteen [Category.*] [Require]s 0 (nineteen in all, each dropped
   alone); Creation.v's own closure is 35 (Theory/Equivalence/Limit.v
   costs 10, Structure/Limit/Creation.v 3, Construction/Subcategory.v 1,
   the other eight 0).  Zero collisions over the 57 names (the
   section-local cover constants are prefixed [sep_] because the bare
   words [cover]/[subcover] occur in prose across the tree).

   Test/ProbeCompHaus413.v mirrors this file's [Require] list and carries
   5 refutation commands = 1 instrument check + 4 negatives of THREE kinds
   told apart by their messages — N1 and N2 both say "universe
   inconsistency", and are told apart by "expected to have type Prop"
   against "because o < …": N1 SORT/TYPING (the fork's continuity by
   eliminating the squash into [IsOpen Z]: "has type Type while it is
   expected to have type Prop", with the clause "Cannot enforce o <=
   Prop"; control: elimination into [True] accepted), N2 UNIVERSE (the
   union over all boxes: the index's level strictly above [o]; control: a
   union indexed by the points accepted), N3 TYPING ([CompHaus_Forget]
   ascribed at [CompHaus ⟶ Top], a plain has-type mismatch) and N4 TYPING
   ([compact_hausdorff_bijection_iso] without [dec] ascribed at [X ≅ Y]:
   it still has a function type) — each stripped ONE AT A TIME in a copy
   of the whole file and compiled alone with its error read; the POSITIVE
   formability of [CreatesLimit K CompHaus_Forget]; readbacks at [eq_refl]
   of the alias, the inclusion's object map, both projections on points,
   the isomorphism's forward map and the generic lift's apex and legs;
   the one-point non-vacuity of (B); guard coverage measured mechanically
   under the plain tokenization (comment-stripped, every identifier token
   inside a refutation command other than the keywords and the wildcard):
   31 identifiers inside, 29 also outside, the two exceptions exhaustively
   the instrument's absent name and the bound variable [z] of N1's lambda;
   rename-simulated 7/7 over the target constants the negatives name, each
   rename applied in THIS file only and every break landing on a [Check]
   line of the probe, none inside a refutation command.  [make todo] grows
   by 5 lines, ALL the probe's refutation commands; this file and
   Creation.v contribute ZERO. 

   --------
   * * 紧致豪斯多夫空间，以及极限的构造Mac Lane，《为工作数学家而写的范畴论》，第二版，第V.1节
   练习 2（书第112页，`maclane:V.1:ex2`）：紧致豪斯多夫空间上的基础集合函子会产生极限。nLab：https://ncatlab.org/nlab/show/compact+Hausdorff+space 和 https://ncatlab.org/nlab/show/created+limit. 传统论证有三部分：紧致豪斯多夫空间积的积拓扑是紧致的（Tychonoff定理）且是豪斯多夫的；从紧致空间到豪斯多夫空间的连续双射是同胚，因此任何使投影连续的其他紧致豪斯多夫拓扑与积拓扑一致；这两点共同保证极限的提升是唯一的并且是极限。本文件提供了图书馆拓扑理论能够承载的该论证内容，涵盖 MEASURES 到其余部分停止的地方，并精确命名了停止点。该问题的三个前提已经过时，每个都重新测量过。该问题的“当前状态”显示不存在空间类别、紧性、豪斯多夫性质和创造概念。但这四者都是存在的：[Top] 是 Instance/Top.v (#259)；[IsCompact]、[IsHausdorff]、[CompactHausdorff_Subcategory]、[CompactHausdorffSpaces] 和 [CompactHausdorff_Full] 都是 Instance/Top.v，它们各自的头部确切地概述了这里所要求的理论，标记为“超出此文件范围”；[CreatesLimit] 是 Structure/Limit/Creation.v (#406)。因此，该问题固定的名称 [CompHaus] 是现有类别的别名，而非一个构造，并且练习的实质是上述三个部分。交付内容。(A) [CompHaus : Category := CompactHausdorffSpaces]，在 [eq_refl] 回读；其包含 [CompHaus_Incl := 包含顶层紧致豪斯多夫子范畴] 与 [CompHaus_Incl_Full] 和 [CompHaus_Incl_Faithful]；基础集合函子 [CompHaus_Forget := Top_Forget ◯ CompHaus_Incl : CompHaus ⟶ Sets] 与 [CompHaus_Forget_Faithful]。(B) 双射定理，构造性且诚实地。对于 [f : X ~{Top}~> Y] 具有一集合同构逆 [g]（[f ∘ g] 和 [g ∘ f] 在点上是恒等映射），[X] 紧且 [Y] 豪斯多夫：[inverse_open_of_decidable U HU dU : IsOpen Y (fun y => U (g y))] 对于 [X] 的每个可判定开集 [U]（[dU : ∀ x, U x + ¬U x]）；当 [X] 的每个开集都是时 [inverse_continuous_of_decidable dec : Continuous Y X g]；并且 [compact_hausdorff_bijection_iso dec : X ≅ [Top] Y]。可判定性恰好在经典论证决定成员资格的地方：它通过  [U]  覆盖  [X] ，并结合围绕  [f c]  的 Hausdorff 分离开集的  [f]-原像，针对  [U] 外的点  [c]  （[sep_cover_covers]，其中 [dU] 决定成员资格；[nbhd_inside] 第二次使用它，以决定 [U (gy')] ，然后推导出矛盾），取有限子覆盖  [IsCompact]  作为列表交给，并交叉匹配目标点（[nbhd]）周围的分离开集；该有限交集就是所需的邻域，并且在原像的各个点上这些邻域的并集就是原像（[inverse_open_of_decidable]）。[List.In] ，一个 [Prop]，只被消除到 [False] （[finite_inter_In_False]）。[IsHausdorff] 通过 [sep_nonequal] 进入，其中 [f c ≈ y0] 对于 [c] 在 [U] 外部会将 [c ≈ g y0] 放入其中 —— 与 Instance/Top/Kolmogorov.v 中记录的关于 Hausdorff ⟹ T0 方向的担忧相反，不需要进行双重否定消除。警告，已披露但未声明必要：[dec] 对所有开集成立，
   不适用于树中的任何有人空间——[Discrete_Top] 的开集
   都是所有 [≈] 相关的谓词（[discrete_open]，Instance/Top.v），因此在 [dec] 中每个此类谓词都是可判定的——而空空间 [Empty_Top]（Instance/Top.v）
   则以空方式满足它并实例化这两个定理（通过审计衡量）；因此每个开集引理是具有非空内容的形式，探针在单点空间中对其应用，使用恒等映射和整个开集。(C) 截断积拓扑，Tychonoff 半的最远可形成点。[Top] 没有产品：自然积开放谓词——对两个因子的开集的存在量词——比点所在的宇宙高一层，并且在该空间层级上被拒绝（Test/ProbeCoproduct.v N9, Instance/Top/Homotopy.v）。Instance/Top/Coproduct.v 命名了一个它没有尝试的逃生路径，即 Instance/Sets/Powerset.v 的自我限制截断 [Powerset_squash]。这里尝试了它：[sq_open W] 是 "[W] 尊重 [≈]，并且 [W] 的每个点在 [W] 内都有一个压缩盒子数据（[sq_boxdata]，一个带 [o < o1] 的 [Type@{o1}]）"；这个压缩是一个 [Prop]，所以 [sq_open : (sq_carrier → Type@{o}) → Type@{o}] 适用，并且 [Top_sq_product X Y : TopSpace@{o}] 关闭所有五个拓扑字段（通过 [sq_squash_map] 和 [sq_squash_pair] 的压缩盒子的并集和交集）。它的投影 [Top_sq_fst]、[Top_sq_snd] 是连续的（一个盒子 [U × whole]）。在探针中编译的 WHAT STOPS：配对 [sq_fork_map f g] 存在于点上，但它的连续性会消除对 [Type] 值的 [IsOpen Z] 的压缩——被拒绝，消除器的动机必须是 [Prop]（“无法强制执行 o <= Prop”），而消除到 [True] 是被接受的；另一条路线，对 [W] 内所有盒子的并集，被拒绝，因为 [sq_boxdata] 位于 [o1]，[open_union] 在 [o] 索引。因此，[Top_sq_product] 有投影，但这里没有确立普遍性质：尝试的两种途径都被拒绝，并且没有显示每个编码都被拒绝（Instance/Top/Coproduct.v 在其早期版本的标题中记录了相同的过度读取）——并且其紧致性（Tychonoff 定理）没有尝试：其有限子覆盖将是从压扁盒子中提取的 [Type] 级数据，因此预期会被同样的论证挡在同一堵墙后面，是被断言而非编译的。这是对 Coproduct.v 注释的一种有度量的改进：截断的编码既展开又产生一个空间，并且墙移到了分叉处。(D) 创建。两个事实，一个是积极的，一个是有条件的：
   - 该问题的置顶声明 [CreatesLimit K CompHaus_Forget] 可以形成（FORMABLE），对于任何形状 [J] 的图表 [K]（探针会检查它，[J : Category] 留给推理）。一项调查读取 Instance/Top/Forgetful.v 时称它是不可以的，并且该注释的最后一句话确实将其分层主张概括到 [Top_Forget] 的名称——这是错误的，因为 [Top_Forget] 落入 [Sets@{h so}]，其同伦层级与 [Top] 自身相同，因此极限锥谓词在两边都适用；该句在此提交中已行内修正，行中保持中性。未交付的是其证明：
   [creates_lift] 必须在任意集合体的极限圆锥上生成一个紧豪斯多夫顶点，该顶点是 Tychonoff 且提升的空间具有豪斯多夫性质，并且 [creates_reflect] 必须使中介连续映射到提升的拓扑中，这是 (C) 的分叉墙。- 泛型引理 Construction/Subcategory/Creation.v 添加了——一个对象在环境极限下封闭的完整子范畴，通过其包含 ([sub_CreatesLimit], [sub_Complete]) 被创建——在 [CompactHausdorff_Subcategory] 上应用为 [CompHaus_Incl_CreatesLimit closed K] 和 [CompHaus_Complete_of closed HT]，条件是 [closed : ClosedUnderLimits CompactHausdorff_Subcategory] 以及 [HT : Complete Top]。两个假设在树中都没有被证明：[Top] 在 [Top_Terminal] 之外没有极限可以闭合，而且 [Top_Complete] 不存在。它们是练习结论将从中得出的陈述，在包含处说明，而不是在遗忘函子处。更正 (#410)：[Top] 现在在 [Top_Terminal] 之外有一个极限，Instance/Top/Solenoid.v 的 [solenoid_limit] 在一系列圆上；[closed] 和 [HT] 仍然没有被证明。更正 (#455)：在伴随函子定理使用的形状中，[HT] 被反驳，而不仅仅是未被证实：在每一个在 [Top] 的同构宇宙之上或及其之下的形状宇宙中，[Complete Top] 在信息排中律下被反驳（Instance/Top/StoneCech/Refutations.v 中的 [Top_not_complete_IEM]），同样在每一个在其同构宇宙之上或及其之下的形状宇宙中，[Complete CompHaus] 亦被反驳，在那份文件的 COVERAGE 记录的实例中（同构宇宙中的 [Top] 插槽，对象宇宙中的证明插槽，点宇宙中的 Hausdorff 证明的开集）：[CompHaus_not_complete_IEM] 在其对象及其之上的形状中也如此，而 [CompHaus_not_complete_IEM_below] 在每一个在同构宇宙之上或及其之下的形状中，对象所包含的以下形状中亦是如此。在同类宇宙以下的形状中，根据信息排中原则都不被否定；在给定索引的情况下，那里适用的索引形式（[Top_not_complete]，[CompHaus_not_complete]）。#455 的评审测量了本次修正草稿所否认的内容，即在其对象宇宙以下的形状 [Complete CompHaus] 被否定：[CompHaus_not_complete_IEM_below] 通过 [Top] 的箭头索引否定了它。更正 (#458)：在 hom 宇宙下方的形状中，在信息排除中间下，两者都被驳斥；在严格高于点的每个形状宇宙中：Instance/Top/Complete/Refutations.v 的 [Top_not_complete_below_IEM] 在那里驳斥了 [Complete Top]，并且 [CompHaus_not_complete_below_IEM] 在那里驳斥了 [Complete CompHaus]，在 Instance/Top/StoneCech/Refutations.v 的 COVERAGE 记录中涉及 [CompHaus_not_complete_IEM_below] 的实例。两者都通过了第一个文件的 [Top_ArrowIndex_transport]，该文件在 hom 宇宙之间移动了 [Top] 的箭头索引；Test/ProbeTopComplete458.v 将两者固定在点与 homs 之间的严格形状上，其中 #455 的 [IEM] 形式被拒绝。在点或以下的形状中，[HT] 和 [Complete CompHaus] 都未被驳斥。未交付，按照问题本身的术语。(a) Tychonoff 在任意指标下的一般性——甚至二元乘积也没有它的普遍性（见 (C)）；(c) [CreatesLimit K CompHaus_Forget] 的证明（见 (D)）；(d) 无条件的 [CompHaus_Complete]（条件的 [CompHaus_Complete_of] 是存在的）；a [Cartesian Top]；子集的紧性（[IsCompact] 是全空间）；(B) 的闭映射形式；对 [dec] 的任何必要性结果；[ClosedUnderLimits] 的任何证明人（更正 (#461)：仍没有 [Top] 的；树的第一个证明人是在 [PTopCat]、Instance/Top/Hausdorff.v 的 [PSep_closed] 和 [PT3_closed] 上），或者所有开集的 [dec] 的一个有元素的证明人；并且没有登记为 [Instance] 的（[CompHaus_Forget_Faithful] 和 [CompHaus_Incl_Faithful] 是引理，遵循 Structure/Limit/Creation.v 对创建证明人的规范）。Stone–Čech 对偶与超滤子幺半群、名册列出此类别的原因（Instance/Roster.v），依然保留在该注释中。更正 (#455)：第一个在 Instance/Top/StoneCech/Refutations.v 的 COVERAGE 记录的实例中被否定解决（同伦宇宙的 [Top] 插槽、对象宇宙中的证明插槽、点宇宙中 Hausdorff 证明的 opens）。在信息性排中律下，当 [CompHaus] 的对象位于其同伦宇宙（Instance/Top/StoneCech.v 生成的实例 [GAFT_CompHaus_only_complete]）或其上位时，[CompHaus_Forget] 在那里没有左对偶（Refutations.v 的 [StoneCech_adjunction_refuted_IEM] 和 [StoneCech_adjunction_refuted_IEM_above]）；在同伦宇宙之下，该陈述不可形成，而在其它实例中，它保持经典的假，属于元论证。#455 的评论测量了这个修正草稿所否认的内容，即该陈述在一个对象宇宙高于同宇宙的实例中被驳斥：第二个常量在那里驳斥了它。包含 [CompHaus_Incl] 的 Stone–Čech 左伴随根本未被驳斥，并且在经典意义上成立；#1329 载有它。Instance/Top/StoneCech.v 构建了有限可枚举集合上的全域箭头，以及 §V.8 练习 4 在全域箭头层次上的情况。宇宙，通过绑定器和模块对本文件的所有48个常数（以及Construction/Subcategory/Creation.v中的9个）进行了测量。在任何57个模块中，均未出现以词为界的[Set]。截断乘积常数是较小的那些：[Top_sq_product@{o o1} : TopSpace@{o} → TopSpace@{o} → TopSpace@{o}]，具有单个命名绑定[o < o1]（框数据的级别）以及stdlib上限；[Top_sq_fst@{o o1 u}]增加了[Top]的同伦级别[o < u]。双射常数包含两个模块方程：[u3 = u1]（两个列表宇宙，[finite_inter]的和子覆盖的，在[sep_subcover_covers]、[nbhd_inside] — 在此打印为[u1 = u3] —、[inverse_open_of_decidable]、[inverse_continuous_of_decidable]、[compact_hausdorff_bijection_iso]）以及[u9 = u8]（开放的级别是载体的，在最后两个上）；其他43个没有任何方程。在 Creation.v 中，[sub_lift]、[sub_lift_apex]、[sub_lift_leg]、[sub_cone_iso] 和 [sub_CreatesLimit] 包含五个方程——[u0 = u11] 将环境 hom 宇宙与形状的（Structure/Limit/Preservation.v 的 [IsLimitCone] 引脚，继承的）识别，并将 [u0 = u13] 与 [Sub] 的（[Compose] 在一个 hom 宇宙中给其三类类型，因此 [Incl C S ◯ K] 强加它——审核隔离了两个原因）联系起来，而 [u5 = u12]、[u6 = u14]、[u9 = u10] 识别闭包假设的量化形状和 [Sub] 水平与图的对应：假设在图自己的宇宙实例中被使用——[sub_ReflectsLimitCone] 仅承载前两个，而 [ClosedUnderLimits]、[sub_CreatesAllLimits]、[sub_Complete] 均不承载。计数。57/57 常量（这里 48 个：24 个 [Definition]，20 个 [Lemma]，2 个 [Theorem]，1 个 [Example]，1 个 [Fixpoint]；那里 9 个：7 个 [Definition]，2 个 [Example]）在全局上下文中关闭，零 [Axioms:] 行，全部在 [make print-assumptions] 门中完全限定；没有任何 [Program]。七个 [Defined] 终止证明，其中五个通过单独将每个翻转为 [Qed] 并重新编译两个文件和探针来承重：[Top_sq_product]（此文件在 [sq_fst_continuous] 的语句处停止，需要产品的载体展开），[sq_fst_map] 和 [sq_snd_map]（投影的连续性证明展开态射场），[compact_hausdorff_bijection_iso]（探针对其前向映射的回读），以及 Creation.v 的 [sub_lift]（它自己的 [eq_refl] 回读 [sub_lift_apex] / [sub_lift_leg]）；[sq_fork_map] 和 [sub_cone_iso] 在一切绿色状态下翻转，并由数据约定保持为 [Defined]。闭包 52 个模块（不包括自身）——Construction/Subcategory/Creation.v  
   边际成本为 10（它带来了 Theory/Equivalence/Limit.v），  
   Instance/Sets/Powerset.v 3，Instance/Top/Forgetful.v 1，其余十六个 [Category.*]   [Require] 为 0（总共十九个，每个单独删除）；Creation.v 自身的闭包为 35（Theory/Equivalence/Limit.v 成本为 10，Structure/Limit/Creation.v 3，Construction/Subcategory.v 1，其余八个为 0）。57 个名称中没有冲突（该章节本地覆盖常量前缀为 [sep_]，因为裸词 [cover] / [subcover] 在整个文中都有出现）。Test/ProbeCompHaus413.v 反映了此文件的 [Require] 列表，并包含 5 个反驳命令 = 1 个工具检查 + 4 种类型的否定，通过它们的消息区分 — N1 和 N2 都说“宇宙不一致”，并通过“预期类型为 Prop”对比“因为 o < …”加以区分：N1 SORT/TYPING（通过将 squash 消除到 [IsOpen Z] 来保持分叉的一致性：“类型为 Type，而预期类型为 Prop”，附条款“无法强制 o <= Prop”；控制：接受消除到 [True]），N2 UNIVERSE（对所有盒子的并集：索引的级别严格高于 [o]；控制：接受以点为索引的并集），N3 TYPING（在 [CompHaus ⟶ Top] 被指定类型的 [CompHaus_Forget] 出现普通类型不匹配）和 N4 TYPING（ZWZ222WZZ 在 [Top]没有被 [dec] 指定类型）24WZZ：
   它仍然具有函数类型）——在整个文件的副本中，每次剥离一个并单独编译，读取其错误；
   [CreatesLimit K CompHaus_Forget] 的正向可形成性；在 [eq_refl] 的别名、包含的对象映射、两个点上的投影、同构的前向映射以及通用提升的顶点和边上的回读；
   (B) 的单点非空性；在普通标记化下（去除注释，除了关键字和通配符之外，驳回命令内的每个标识符标记）机械测量守卫覆盖率：
   内部31个标识符，外部29个，两个例外详尽地涵盖了仪器缺失的名称和 N1 的 lambda 的绑定变量 [z]；
   对目标常量进行重命名模拟 7/7，负面名称，每个重命名应用于此文件中每一次且每一次降落在探针的 [Check] 线上，没有一次在反驳指令内部。[make todo] 增长了 5 行，包含探针的所有反驳命令；这个文件和 Creation.v 完全没有贡献。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Subcategory.Creation.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.
Require Import Coq.Lists.List.

Generalizable All Variables.

(* * * The category, under the issue's name / * * 该类别，在问题名称下 *)

Definition CompHaus : Category := CompactHausdorffSpaces.

Example CompHaus_is_CompactHausdorffSpaces :
  CompHaus = CompactHausdorffSpaces := eq_refl.

Definition CompHaus_Incl : CompHaus ⟶ Top :=
  Incl Top CompactHausdorff_Subcategory.

Lemma CompHaus_Incl_Full : Functor.Full CompHaus_Incl.
Proof. exact (Full_Implies_Full_Functor Top _ CompactHausdorff_Full). Qed.

Lemma CompHaus_Incl_Faithful : Functor.Faithful CompHaus_Incl.
Proof. exact (Incl_Faithful Top _). Qed.

(* * * A continuous bijection from a compact space to a Hausdorff space / * * 从紧空间到豪斯多夫空间的连续双射 *)

Section Bijection.
Context {X Y : TopSpace} (f : X ~{Top}~> Y)
        (g : SetoidMorphism (top_carrier Y) (top_carrier X))
        (Hfg : ∀ y : Y, continuous_map f (g y) ≈ y)
        (Hgf : ∀ x : X, g (continuous_map f x) ≈ x)
        (HX : IsCompact X) (HY : IsHausdorff Y).

(* Finite intersections of a list-indexed family of opens of [Y]. / [Y] 的列表索引开集族的有限交集。 *)
Fixpoint finite_inter {I : Type} (B : I → Y → Type) (l : list I) : Y → Type :=
  match l with
  | nil => fun _ => poly_unit
  | cons i l' => fun y => (B i y ∧ finite_inter B l' y)%type
  end.

Lemma finite_inter_open {I : Type} (B : I → Y → Type)
  (HB : ∀ i, IsOpen Y (B i)) (l : list I) : IsOpen Y (finite_inter B l).
Proof using.
  induction l; simpl.
  - apply open_whole.
  - apply open_inter; [apply HB | exact IHl].
Qed.

Lemma finite_inter_all {I : Type} (B : I → Y → Type) (l : list I) (y : Y) :
  (∀ i, B i y) → finite_inter B l y.
Proof using.
  induction l; simpl; intro H.
  - exact ttt.
  - split; [apply H | exact (IHl H)].
Qed.

(* The one use of [List.In], a [Prop], eliminated only into [False]. / [List.In] 的唯一用途是一个 [Prop]，只能消除为 [False]。 *)
Lemma finite_inter_In_False {I : Type} (B : I → Y → Type) (l : list I)
  (y : Y) :
  finite_inter B l y → ∀ i, In i l → (B i y → False) → False.
Proof using.
  induction l; simpl; intros H i Hi nb.
  - exact Hi.
  - destruct Hi as [e | Hi].
    + subst; exact (nb (fst H)).
    + exact (IHl (snd H) i Hi nb).
Qed.

Section Open.
Context (U : X → Type) (HU : IsOpen X U)
        (dU : ∀ x : X, U x + (U x → False)).

(* The complement of [U], as a type of points. / [U] 的补集，作为一种点类型。 *)
Definition compl_pts : Type := { c : X & U c → False }.

Section Point.
Context (y0 : Y) (hy0 : U (g y0)).

Lemma sep_nonequal (c : compl_pts) : continuous_map f (`1 c) ≈ y0 → False.
Proof using Hgf HU hy0.
  intro e. apply (`2 c).
  apply (open_proper X U HU (g y0) (`1 c)).
  - rewrite <- (Hgf (`1 c)). apply (proper_morphism g). symmetry. exact e.
  - exact hy0.
Qed.

Definition sepA (c : compl_pts) : Y → Type := `1 (HY _ y0 (sep_nonequal c)).
Definition sepB (c : compl_pts) : Y → Type :=
  `1 (`2 (HY _ y0 (sep_nonequal c))).

Lemma sepA_open (c : compl_pts) : IsOpen Y (sepA c).
Proof using. exact (fst (fst (`2 (`2 (HY _ y0 (sep_nonequal c)))))). Qed.
Lemma sepB_open (c : compl_pts) : IsOpen Y (sepB c).
Proof using. exact (snd (fst (`2 (`2 (HY _ y0 (sep_nonequal c)))))). Qed.
Lemma sepA_at (c : compl_pts) : sepA c (continuous_map f (`1 c)).
Proof using. exact (fst (fst (snd (`2 (`2 (HY _ y0 (sep_nonequal c))))))). Qed.
Lemma sepB_at (c : compl_pts) : sepB c y0.
Proof using. exact (snd (fst (snd (`2 (`2 (HY _ y0 (sep_nonequal c))))))). Qed.
Lemma sep_disjoint (c : compl_pts) (z : Y) : sepA c z → sepB c z → False.
Proof using. exact (snd (snd (`2 (`2 (HY _ y0 (sep_nonequal c))))) z). Qed.

(* The sep_cover of [X]: the preimages of the separating opens, plus [U]. / [X] 的 sep_cover：分离开集的原像，加上 [U]。 *)
Definition sep_cover_idx : Type := (compl_pts + poly_unit)%type.
Definition sep_cover (i : sep_cover_idx) : X → Type :=
  match i with
  | inl c => fun x => sepA c (continuous_map f x)
  | inr _ => U
  end.

(* This is where membership in [U] is decided. / 这是决定是否加入 [U] 的地方。 *)
Lemma sep_cover_covers : Covers sep_cover (fun _ => poly_unit).
Proof using HU dU f.
  split.
  - intros [c | u]; simpl.
    + exact (continuity f (sepA c) (sepA_open c)).
    + exact HU.
  - intro x; split.
    + intros _. destruct (dU x) as [u | n].
      * exists (inr ttt); exact u.
      * exists (inl (x; n)); exact (sepA_at (x; n)).
    + intros _; exact ttt.
Qed.

Definition sep_subcover : list sep_cover_idx :=
  `1 (HX sep_cover_idx sep_cover sep_cover_covers).
Definition sep_subcover_covers :
  ∀ x : X, ∃ i : sep_cover_idx, (In i sep_subcover ∧ sep_cover i x)%type :=
  `2 (HX sep_cover_idx sep_cover sep_cover_covers).

(* The [Y]-side family: the separating opens around [y0]; nothing for [U]. / [Y] 家族：分离在 [y0] 附近打开；[U] 没有任何变化。 *)
Definition sep_fam (i : sep_cover_idx) : Y → Type :=
  match i with
  | inl c => sepB c
  | inr _ => fun _ => poly_unit
  end.

Definition nbhd : Y → Type := finite_inter sep_fam sep_subcover.

Lemma nbhd_open : IsOpen Y nbhd.
Proof using.
  apply finite_inter_open. intros [c | u]; simpl.
  - exact (sepB_open c).
  - exact (open_whole Y).
Qed.

Lemma nbhd_at : nbhd y0.
Proof using.
  apply finite_inter_all. intros [c | u]; simpl.
  - exact (sepB_at c).
  - exact ttt.
Qed.

Lemma nbhd_inside (y' : Y) : nbhd y' → U (g y').
Proof using Hfg HU dU.
  intro hn. destruct (dU (g y')) as [u | n]; [exact u | exfalso].
  destruct (sep_subcover_covers (g y')) as [i [Hin w]].
  destruct i as [c | u]; simpl in w.
  - refine (finite_inter_In_False sep_fam sep_subcover y' hn (inl c) Hin _).
    intro b. apply (sep_disjoint c y').
    + apply (open_proper Y (sepA c) (sepA_open c)
               (continuous_map f (g y')) y').
      * exact (Hfg y').
      * exact w.
    + exact b.
  - exact (n w).
Qed.

End Point.

Theorem inverse_open_of_decidable : IsOpen Y (fun y => U (g y)).
Proof using Hfg Hgf HU HX HY dU f g.
  apply (open_respects Y
           (fun y => { yp : { y0 : Y & U (g y0) } & nbhd (`1 yp) (`2 yp) y })).
  - intro y; split.
    + intros [yp hn]. exact (nbhd_inside (`1 yp) (`2 yp) y hn).
    + intro v. exists (y; v). exact (nbhd_at y v).
  - apply (open_union Y { y0 : Y & U (g y0) }
             (fun yp => nbhd (`1 yp) (`2 yp))).
    intro yp. exact (nbhd_open (`1 yp) (`2 yp)).
Qed.

End Open.

Theorem inverse_continuous_of_decidable
  (dec : ∀ U : X → Type, IsOpen X U → ∀ x : X, U x + (U x → False)) :
  Continuous Y X g.
Proof using Hfg Hgf HX HY f g.
  intros U HU. exact (inverse_open_of_decidable U HU (dec U HU)).
Qed.

Definition compact_hausdorff_bijection_iso
  (dec : ∀ U : X → Type, IsOpen X U → ∀ x : X, U x + (U x → False)) :
  X ≅[Top] Y.
Proof using Hfg Hgf HX HY f g.
  unshelve refine
    {| to := f
     ; from := Build_ContinuousMorphism Y X g
                 (inverse_continuous_of_decidable dec) |}.
  - intro y; simpl. exact (Hfg y).
  - intro x; simpl. exact (Hgf x).
Defined.

End Bijection.

(* * * The truncated product topology: the furthest formable point of (a) / * * 截断积拓扑：（a）的最远可形成点 *)

Section SquashProduct.

Universe o o1.
Constraint o < o1.
Context (X Y : TopSpace@{o}).

Definition sq_carrier : SetoidObject@{o o} := {|
  carrier := (carrier (top_carrier X) * carrier (top_carrier Y))%type;
  is_setoid := prod_setoid
|}.

(* A box around [p] inside [W]: opens of the factors, data at level [o1]. / 在 [W] 内的 [p] 周围的框：打开因子，[o1] 级别的数据。 *)
Definition sq_boxdata (W : sq_carrier → Type@{o}) (p : sq_carrier) :
  Type@{o1} :=
  { U : carrier (top_carrier X) → Type@{o} &
  { V : carrier (top_carrier Y) → Type@{o} &
    (IsOpen X U ∧ IsOpen Y V ∧ U (fst p) ∧ V (snd p)
       ∧ (∀ q : sq_carrier, U (fst q) → V (snd q) → W q))%type } }.

(* Squashed into a [Prop], the box datum fits at level [o]. / 被压缩到 [Prop] 中，箱子基准适合在 [o] 级别。 *)
Definition sq_open (W : sq_carrier → Type@{o}) : Type@{o} :=
  ((∀ x y : sq_carrier, x ≈ y → W x → W y)
   ∧ (∀ p : sq_carrier, W p → Powerset_squash@{o1} (sq_boxdata W p)))%type.

Lemma sq_squash_map {A B : Type@{o1}} (f : A → B) :
  Powerset_squash@{o1} A → Powerset_squash@{o1} B.
Proof using. intros s Q k; exact (s Q (fun a => k (f a))). Qed.

Lemma sq_squash_pair {A B : Type@{o1}} :
  Powerset_squash@{o1} A → Powerset_squash@{o1} B →
  Powerset_squash@{o1} (A * B)%type.
Proof using.
  intros a b Q k; exact (a Q (fun x => b Q (fun y => k (x, y)))).
Qed.

Definition Top_sq_product : TopSpace@{o}.
Proof using X Y.
  unshelve refine {| top_carrier := sq_carrier; IsOpen := sq_open |}.
  - (* open_respects / 公开尊重 *)
    intros U V H [Hp Hb]; split.
    + intros x y e u. apply (fst (H y)). apply (Hp x y e). apply (snd (H x)).
      exact u.
    + intros p v. apply (sq_squash_map (A := sq_boxdata U p)).
      * intros [U0 [V0 [oU [oV [u0 [v0 inside]]]]]].
        exists U0; exists V0. repeat split; try assumption.
        intros q0 a0 b0. apply (fst (H q0)). exact (inside q0 a0 b0).
      * apply Hb. apply (snd (H p)). exact v.
  - (* open_proper / 打开适当的 *)
    intros U [Hp _] x y e u. exact (Hp x y e u).
  - (* open_union / 开放联盟 *)
    intros I U HU; split.
    + intros x y e [i u]. exists i. exact (fst (HU i) x y e u).
    + intros p [i u]. apply (sq_squash_map (A := sq_boxdata (U i) p)).
      * intros [U0 [V0 [oU [oV [u0 [v0 inside]]]]]].
        exists U0; exists V0. repeat split; try assumption.
        intros q0 a0 b0. exists i. exact (inside q0 a0 b0).
      * exact (snd (HU i) p u).
  - (* open_whole / 打开整个 *)
    split.
    + intros; exact ttt.
    + intros p _. apply Powerset_squash_intro.
      exists (fun _ => poly_unit); exists (fun _ => poly_unit).
      repeat split; try exact ttt; try apply open_whole.
  - (* open_inter / 打开_inter *)
    intros U V [HpU HbU] [HpV HbV]; split.
    + intros x y e [u v]. split; [exact (HpU x y e u) | exact (HpV x y e v)].
    + intros p [u v].
      apply (sq_squash_map (A := (sq_boxdata U p * sq_boxdata V p)%type)).
      * intros [[U0 [V0 [oU0 [oV0 [u0 [v0 in0]]]]]]
                [U1 [V1 [oU1 [oV1 [u1 [v1 in1]]]]]]].
        exists (fun a => (U0 a ∧ U1 a)%type);
        exists (fun b => (V0 b ∧ V1 b)%type).
        split; [apply open_inter; assumption |].
        split; [apply open_inter; assumption |].
        split; [split; assumption |].
        split; [split; assumption |].
        intros q0 [a0 a1] [b0 b1].
        split; [exact (in0 q0 a0 b0) | exact (in1 q0 a1 b1)].
      * apply sq_squash_pair; [exact (HbU p u) | exact (HbV p v)].
Defined.

Definition sq_fst_map : SetoidMorphism sq_carrier (top_carrier X).
Proof using X Y.
  unshelve notypeclasses refine {| morphism := fun p : sq_carrier => fst p |}.
  intros u v Huv; exact (fst Huv).
Defined.

Definition sq_snd_map : SetoidMorphism sq_carrier (top_carrier Y).
Proof using X Y.
  unshelve notypeclasses refine {| morphism := fun p : sq_carrier => snd p |}.
  intros u v Huv; exact (snd Huv).
Defined.

Lemma sq_fst_continuous : Continuous Top_sq_product X sq_fst_map.
Proof using X Y.
  intros U HU; split.
  - intros x y [e _] u. exact (open_proper X U HU (fst x) (fst y) e u).
  - intros p u. apply Powerset_squash_intro.
    exists U; exists (fun _ => poly_unit).
    repeat split; try assumption; try apply open_whole; try exact ttt.
    intros q0 a0 _; exact a0.
Qed.

Lemma sq_snd_continuous : Continuous Top_sq_product Y sq_snd_map.
Proof using X Y.
  intros V HV; split.
  - intros x y [_ e] v. exact (open_proper Y V HV (snd x) (snd y) e v).
  - intros p v. apply Powerset_squash_intro.
    exists (fun _ => poly_unit); exists V.
    repeat split; try assumption; try apply open_whole; try exact ttt.
    intros q0 _ b0; exact b0.
Qed.

Definition Top_sq_fst : Top_sq_product ~{Top}~> X :=
  Build_ContinuousMorphism Top_sq_product X sq_fst_map sq_fst_continuous.

Definition Top_sq_snd : Top_sq_product ~{Top}~> Y :=
  Build_ContinuousMorphism Top_sq_product Y sq_snd_map sq_snd_continuous.

(* The pairing exists at the level of setoids; its CONTINUITY is what the probe pins as refused. / 这种配对存在于集合等价类的层次；其连续性正是探针所标记为被拒绝的。 *)
Definition sq_fork_map {Z : TopSpace@{o}}
  (f : Z ~{Top}~> X) (g : Z ~{Top}~> Y) :
  SetoidMorphism (top_carrier Z) sq_carrier.
Proof using X Y.
  unshelve notypeclasses refine
    {| morphism := fun z => (continuous_map f z, continuous_map g z) |}.
  intros u v Huv; split.
  - exact (proper_morphism (continuous_map f) u v Huv).
  - exact (proper_morphism (continuous_map g) u v Huv).
Defined.

End SquashProduct.

(* * * The forgetful functor, and creation / * * 忘记函子与创生 *)

Definition CompHaus_Forget := Top_Forget ◯ CompHaus_Incl.

Lemma CompHaus_Forget_Faithful : Functor.Faithful CompHaus_Forget.
Proof.
  constructor; intros X Y h k E.
  apply (@fmap_inj _ _ _ CompHaus_Incl_Faithful X Y h k).
  apply (@fmap_inj _ _ _ Top_Forget_Faithful _ _ _ _).
  exact E.
Qed.

(*
 Creation by the INCLUSION, from the generic lemma, under closure of the
 compact Hausdorff predicate under the limits of [Top]. 

 --------
 由包含创建，从一般引理出发，在紧豪斯多夫谓词在 [Top] 的极限下的闭合下。
*)
Definition CompHaus_Incl_CreatesLimit
  (closed : ClosedUnderLimits CompactHausdorff_Subcategory)
  {J : Category} (K : J ⟶ CompHaus) : CreatesLimit K CompHaus_Incl :=
  sub_CreatesLimit CompactHausdorff_Subcategory CompactHausdorff_Full closed K.

Definition CompHaus_Complete_of
  (closed : ClosedUnderLimits CompactHausdorff_Subcategory)
  (HT : @Complete Top) : @Complete CompHaus :=
  sub_Complete CompactHausdorff_Subcategory CompactHausdorff_Full closed HT.
