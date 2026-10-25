Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Spaces with Prop-valued opens / * 带有 Prop 值的 opens 空格 *)

(*
 Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
 §V.9, book p. 132 (PDF p. 141), read from the page image: the
 category Top and its faithful underlying-set functor G : Top → Set
 (catalog id maclane:V.9:construction1)
 Fong and Spivak, "Seven Sketches in Compositionality", §7.3.2,
 Definition 7.25, printed p. 234 (PDF p. 246): a topology is a set of
 subsets containing the whole set and closed under binary intersections
 and under unions of families indexed by any set, as the catalogue
 under doc/plan/books summarizes it (that book was not consulted)
 nLab: https://ncatlab.org/nlab/show/Top
 nLab: https://ncatlab.org/nlab/show/topological+space
 nLab: https://ncatlab.org/nlab/show/initial+topology

 BACKGROUND.  A topology on a set is a family of its subsets, so a
 type-theoretic encoding has to decide what a subset is.  Instance/Top.v
 takes a subset of the points to be a Type-valued predicate at the
 points' universe [o], and its header (point 2) draws the consequence:
 the predicate on predicates [IsOpen] lives above the points, and
 [Continuous], which quantifies over the opens of the codomain, puts the
 hom-sets of [Top@{h o}] strictly above them, [o < h].  Three
 measurements downstream trace back to that one choice.
 - Instance/Top/Forgetful.v: the underlying-set functor cannot land in
 [Sets@{o so}], the Sets whose objects ARE the point setoids; it
 lands in the lifted [Sets@{h so}], so no [Adjunction] record joins
 it to a functor out of [Sets@{o so}] (that file's header).
 - Test/ProbeStoneCech455.v's N6: [ContinuousMorphism X Y] ascribed at
 [Type@{o}] is refused, and Instance/Top/StoneCech.v's header traces
 the refutation of [CompHaus]'s completeness under [IEM] to the
 homs sitting above the points.
 - Mac Lane's subspace predicate, "V is the preimage of an open of X",
 quantifies over the opens of X; over [Top] it is refused at
 [Type@{o}] and lives one universe up (Instance/Top/Subspace/
 TypeValued.v's [tsub_open]).
 The standard way out is impredicativity: a Prop-valued predicate on
 Prop-valued predicates, and a quantification over all the opens of a
 space, are again propositions.  That is this file's encoding.  Opens are
 predicates [pt_carrier X → Prop], [POpen X] is a predicate on them, and
 continuity [PCont] is a proposition, so a continuous map [PMor X Y] is a
 setoid map with a proof attached and lives at the points' universe,
 exactly as a [Sets] arrow does.  The subspace predicate is then an
 ordinary proposition and the subspace an ordinary [PTop@{o}]
 (Instance/Top/Subspace.v's [PSub], with an empty constraint block), and
 the underlying-set functor [PForget] lands in [Sets@{o so}] itself, so
 Mac Lane's sliced adjunctions of §V.9 are formable as [Adjunction]
 records (Instance/Top/Subspace.v).  What Prop costs is the usual
 restriction on eliminating a proof into data: membership in an open
 carries no computational witness, [ex] where Instance/Top.v has a
 dependent sum; nothing in this file or in Instance/Top/Subspace.v
 eliminates membership into data.

 PROVENANCE.  This file is #1328's item 1, "a Prop-valued
 topological-space record and category, with homs at the points'
 universe", landed under #457 by the maintainer's decision of 2026-09-24
 at the path #1328 suggested.  It sits beside Instance/Top.v, not in its
 place: [Top] and its consumers are unchanged.  What stays for #1328:
 [PCompHaus] (its suggested Instance/Top/Prop/CompHaus.v), the comparison
 functors between [Top] and [PTopCat] (item 2), the limit structure the
 adjoint functor theorems need, products and completeness (item 3; its
 equalizers and coequalizers are Instance/Top/Subspace.v's
 [PTop_HasEqualizers] and [PTop_HasCoequalizers]), and the re-run of
 #455's refutations against this encoding (item 4).  CORRECTION
 (#458): item 3 is delivered for [PTopCat] and item 4 for its
 completeness and cocompleteness: Instance/Top/Complete.v builds its
 products ([PTop_HasIndexedProducts]) and proves it complete
 ([PTop_Complete]), Instance/Top/Cocomplete.v builds its coproducts
 ([PTop_HasIndexedCoproducts]) and proves it cocomplete
 ([PTop_Cocomplete]), both at every shape universe at or below the
 points', and Instance/Top/Complete/Refutations.v and
 Instance/Top/Cocomplete/Refutations.v refute both above the points
 under informative excluded middle; [PCompHaus], the comparison
 functors and the rest of item 4 stay for #1328.  The
 record completes Test/ProbeStoneCech455.v's control [p455_TopP], which
 has a union axiom only, in form (a) below: it adds the other four
 axioms and restates the union axiom as (b).  Instance/Top/StoneCech.v's
 header cites that control as the encoding's first measurement.

 THE UNION AXIOM, MEASURED BOTH WAYS.  Two statements of "arbitrary
 unions" are available for Prop-valued opens:
 (a) over an index type at the points' universe,
 [∀ (I : Type@{o}) (U : I → X → Prop), (∀ i, POpen (U i)) →
 POpen (fun x => ex (fun i => U i x))], [p455_TopP]'s form;
 (b) over a family of opens given as a Prop-valued predicate on
 predicates, [∀ F, (∀ U, F U → POpen U) →
 POpen (fun x => ex (fun U => F U /\ U x))], this file's
 [popen_union].
 Both were compiled, in a scratch file carrying this file,
 Instance/Top/Subspace.v and a copy of the record with (a) in place of
 (b).  Under (a) the subspace's union is witnessed by the union of all
 the witnessing opens, indexed by pairs (index, open of X); that index
 type reads back at [Type@{max(Set+1,o)}] (About), and used as a union
 index at [o := Set] it is refused, "Cannot enforce Set+1 <= Set", while
 under a declared [Set < o] it is accepted; so the subspace built from
 that pair-indexed witness, the only route tried, carries [Set < o].
 Deriving (b) from (a) needs the index [{ U | F U }] and is refused at
 [Set] the same way, accepted under [Set < o].  Under (b)
 Instance/Top/Subspace.v's [PSub] is accepted at [PTop@{Set}] (the
 same scratch file, an empty constraint block), and (a) follows at
 EVERY index universe:
 [popen_union_indexed@{o i}], whose constraint block is empty.  (b) is
 therefore the field, for three reasons: it closes the opens under the
 union of any family of opens, with no index type to bound; it implies
 (a) at every index universe, so Seven Sketches' unions over an index
 set hold as stated (Instance/Top/Subspace.v's [ex732_part2] uses
 them); and it frees the subspace of the [Set < o] bound.  Nothing here
 shows (b) strictly stronger than (a) at [o := Set]; only the direct
 derivation is refused there.

 STRENGTHS.  [PForget_fobj] and [PForget_fmap] hold at [eq_refl]: the
 underlying setoid of a space IS its point setoid and the underlying map
 of an arrow IS its setoid map.  [PForget_Faithful] is the identity on
 hom-setoid proofs: [PMor_Setoid] compares exactly the underlying maps,
 pointwise, and ignores the continuity proofs.  [popen_const] makes every
 constant proposition open, the Prop analogue of Instance/Top.v's
 [open_const], and [popen_empty] is its case [False].  Of the concrete
 spaces below, [PDiscrete_carrier], [PDiscrete_open] and
 [pdisc_mor_map] hold at [eq_refl] as well.

 CONCRETE SPACES.  [PDiscrete S] is the discrete topology on a setoid
 [S]: its opens are the predicates respecting the points' equality
 ([pdisc_open]), which under the setoid discipline is the whole
 condition, [popen_proper] asking it of every open.  It is a record
 literal over five [Qed] lemmas, so its points and its opens read back
 at [eq_refl] ([PDiscrete_carrier], [PDiscrete_open]).  Built instead in
 proof mode by [refine] and closed [Qed], as #457's review prototyped
 it, the points' readback at [eq_refl] is refused (Coq: cannot unify
 "pt_carrier (PDiscreteQ S)" and "S", the Qed copy named [PDiscreteQ]
 in a scratch file carrying this file); measured, not pinned.  Every
 setoid map out of a discrete space is continuous ([pdisc_cont]), so
 [pdisc_mor S Y f] is [f] as an arrow of [PTopCat] ([pdisc_mor_map], at
 [eq_refl]); [pconst S Y y] is the constant setoid map at a point [y]
 of a space.  [PPoint] and [PBool] are the discrete spaces on
 Instance/Sets.v's [unit_setoid_object] and [bool_setoid_object], and
 [PBool_points_distinct] refutes [false ≈ true] in [PBool], its
 equality being Leibniz.  They are the tree's first named [PTop]s: a
 grep of the tree's .v files for [Build_PTop] and for [pt_carrier :=]
 finds that, besides [PDiscrete], only Instance/Top/Subspace.v's [PSub]
 and [PQuot] define a space with them, both built from variables.
 CORRECTION (#410): the same grep re-run on the tree of #410 also finds
 Instance/Top/Complete.v, Instance/Top/Cocomplete.v,
 Instance/Top/Separation.v and Instance/Top/Hausdorff.v, which landed
 after it, and Instance/Top/Circle.v's [PRLine], the real line.
 CORRECTION (#462): on the tree of #462 it also finds
 Instance/Top/Components.v, whose three-point space [PZig] is built
 with them.
 Instance/Top/Subspace.v takes an equalizer and a coequalizer of two
 different maps between them.

 UNIVERSES, read by [About] under [Set Printing Universes].
 - [PTop@{o} : Type@{max(Set+1,o+1)}], empty block.  The [Set+1] is
 the sort of the type of Prop-valued predicates; since [Set <= o]
 the sort is [o+1], and [PTop@{Set} : Type@{Set+1}] is accepted.
 - [PMor@{o} : PTop@{o} → PTop@{o} → Type@{o}], empty block: the homs
 sit at the points' universe, where Test/ProbeStoneCech455.v's N6
 refuses [ContinuousMorphism].  [PCont@{o}], [PMor_Setoid@{o}] (a
 [Setoid@{o o}]), [pcont_respects@{o}], [popen_const@{o}] and
 [popen_union_indexed@{o i}] have empty blocks too.
 - [pid@{o}] carries [o <= ID.u0] and [pcompose@{o}] the three
 [o <= compose.u*] caps: the stdlib caps of Instance/Sets.v's
 [setoid_morphism_id] and [setoid_morphism_compose], which carry
 them in their own blocks, and which [Sets@{o so}] carries too.
 - [PTopCat@{o so} : Category@{so o o}], block [Set < so], [o < so]
 and those four caps: [Sets@{o so}]'s block plus [Set < so], which
 [o < so] implies and which records [PTop]'s sort.
 - [PForget@{o so} : PTopCat@{o so} ⟶ Sets@{o so}], the same block;
 [PForget_Faithful@{o so} : Faithful@{so o so} PForget@{o so}].
 - [PDiscrete@{o} : SetoidObject@{o o} → PTop@{o}], empty block, as
 are [pdisc_open@{o}], its five lemmas, [PDiscrete_carrier],
 [PDiscrete_open], [pdisc_cont@{o}], [pdisc_mor@{o}],
 [pdisc_mor_map] and [pconst@{o}].  [PPoint@{o} : PTop@{o}],
 [PBool@{o} : PTop@{o}] and [PBool_points_distinct@{o}] carry the
 one cap [o <= Logic_lemmas.equality.u0], which Instance/Sets.v's
 [unit_setoid_object] and [bool_setoid_object] carry in their own
 blocks.
 No universe of this file is pinned at [Set].  Over the [About] output
 of all 51 of this file's constants (the 49 names of its [Print Module]
 listing, obligations included, and the two record constructors), the
 word [Set] occurs in [PTop]'s sort and as [Set < so] in 12 blocks:
 [PTopCat], [PForget], their seven obligations, [PForget_fobj],
 [PForget_fmap] and [PForget_Faithful].

 NOT DELIVERED.  No comparison with [Top], no [PCompHaus], and no limits
 or colimits of [PTopCat] in this file: its equalizers and coequalizers
 are Instance/Top/Subspace.v's [PTop_HasEqualizers] and
 [PTop_HasCoequalizers], and its products are not built; no
 indiscrete, empty or other non-discrete named space (the named spaces
 are discrete); no discrete or indiscrete functors and no adjoint
 triple, the analogue of
 Instance/Top/Forgetful.v, over [PTopCat]; no separation or compactness
 notions; and no claim that (b) is strictly stronger than (a) at
 [o := Set].  CORRECTION (#458): those limits, colimits and functors
 are no longer absent from the tree, only from this file.  The products
 and all small limits of [PTopCat] are Instance/Top/Complete.v's
 ([PProd], [PTop_Complete]), its coproducts and all small colimits
 Instance/Top/Cocomplete.v's ([PSigma], [PTop_Cocomplete]), both at
 every shape universe at or below the points'.  The discrete and
 indiscrete functors are [PDisc] (Instance/Top/Complete.v) and
 [PIndisc] (Instance/Top/Cocomplete.v), with the adjoint triple
 [PDisc ⊣ PForget ⊣ PIndisc] as two adjunctions, [PDisc_PForget] and
 [PForget_PIndisc], as Instance/Top/Forgetful.v states its own.  Named
 spaces that are not discrete exist there as well: the indiscrete space
 on a setoid [PIndiscrete] and the indiscrete two-point [PTwoIndisc]
 (Instance/Top/Cocomplete.v), their sum [PTwoIndiscSum], whose topology
 is neither discrete nor indiscrete ([PTwoIndiscSum_not_discrete],
 [PTwoIndiscSum_not_indiscrete]), and Instance/Top/Complete.v's
 convergent sequence [PConv], whose limit point is not open
 ([pconv_limit_point_not_open]).  CORRECTION (#461): separation
 notions over [PTopCat] now exist as well, in Instance/Top/Separation.v
 ([PT0], [PT1], the positive Hausdorff form [PHaus] and their
 reflections) and Instance/Top/Hausdorff.v (regular spaces, and the
 Hausdorff reflection by the general adjoint functor theorem);
 compactness is still absent. 

 --------
 麦克·莱恩，《为工作中的数学家而设的范畴》，第2版（GTM 5），§V.9，第132页（PDF第141页），从页图像阅读：范畴 Top 及其忠实的底层集函子 G : Top → Set（目录ID maclane:V.9:construction1）
 方康与斯皮瓦克，《组合性的七个草图》，§7.3.2，第7.25条定义，印刷版第234页（PDF第246页）：拓扑是一个包含整个集合并在二元交与任意集合索引的族的并下封闭的子集集合，如文档/计划/书籍目录所总结（该书未查阅）
 nLab: https://ncatlab.org/nlab/show/Top
 nLab: https://ncatlab.org/nlab/show/topological+space
 nLab: https://ncatlab.org/nlab/show/initial+topology背景。一组的拓扑是其子集的一个族，因此类型理论的编码必须决定什么是子集。Instance/Top.v 将点的子集视为点所属宇宙 [o] 上的类型值谓词，其头部（第 2 点）推导出如下结果：谓词上的谓词 [IsOpen] 位于点之上，而 [Continuous] 对余域开集进行量化，将 [Top@{h o}] 的同态集严格放置在它们之上，[o < h]。下游的三次测量都追溯到这一选择。- Instance/Top/Forgetful.v：基础集合函子不能落入 [Sets@{o so}]，即其对象是点集合同构的集合；它落入提升后的 [Sets@{h so}]，因此没有 [Adjunction] 记录将其与 [Sets@{o so}] 的函数联系起来（该文件的头部）。- Test/ProbeStoneCech455.v 的 N6：在 [Type@{o}] 上赋予的 [ContinuousMorphism X Y] 被拒绝，而 Instance/Top/StoneCech.v 的头部追踪 [CompHaus] 在 [IEM] 下完整性的驳斥归结于位于点上方的同态。- Mac Lane 的子空间谓词，“V 是 X 的开集的原像”，对 X 的开集进行量化；在 [Top] 上它在 [Type@{o}] 被拒绝，并位于高一个宇宙（Instance/Top/Subspace/TypeValued.v 的 [tsub_open]）。标准的解决方法是自我限制：针对 Prop 型谓词的 Prop 型谓词，以及对空间上所有开集的量化，再次是命题。这就是此文件的编码方式。开集是谓词 [pt_carrier X → Prop]，[POpen X] 是它们上的一个谓词，连续性 [PCont] 是一个命题，因此一个连续映射 [PMor X Y] 是一个带有证明的集类映射，并且存在于点的宇宙中，就像 [Sets] 箭头一样。子空间谓词随后是一个普通命题，而子空间是一个普通的 [PTop@{o}]（Instance/Top/Subspace.v 的 [PSub]，带有一个空约束块），并且基础集函子 [PForget] 落在 [Sets@{o so}] 自身中，因此 Mac Lane 在 §V.9 中的切片伴随关系可以以 [Adjunction] 记录（Instance/Top/Subspace.v）的形式构造。Prop 的代价是消除证明为数据的通常限制：属于一个开放集合没有计算上的证据，[ex]，其中 Instance/Top.v 有一个依赖和；在该文件或 Instance/Top/Subspace.v 中没有任何内容将属于关系消除为数据。来源。此文件是 #1328 的项目 1，“一个以 Prop 值为类型的拓扑空间记录和范畴，其同态位于点的宇宙中”，由维护者于 2026-09-24 决定放置在 #457 下，并采用 #1328 建议的路径。它放在 Instance/Top.v 旁边，而不是原来的位置：[Top] 及其使用者保持不变。#1328 所保留的内容包括：[PCompHaus]（其建议的 Instance/Top/Prop/CompHaus.v）、[Top] 与 [PTopCat]（项目 2）之间的比较函子、伴随函子定理所需的极限结构、乘积与完备性（项目 3；其等化子和余等化子是 Instance/Top/Subspace.v 的 [PTop_HasEqualizers] 和 [PTop_HasCoequalizers]）、以及对 #455 对该编码的反驳重新运行（项目 4）。更正
 (#458)：第3项为 [PTopCat] 提供，第4项用于其完整性和余完整性：Instance/Top/Complete.v 构建其乘积（[PTop_HasIndexedProducts]）并证明其完整性（[PTop_Complete]），Instance/Top/Cocomplete.v 构建其余积（[PTop_HasIndexedCoproducts]）并证明其余完整性（[PTop_Cocomplete]），在每个点或以下的形宇宙中均成立；Instance/Top/Complete/Refutations.v 和 Instance/Top/Cocomplete/Refutations.v 在点之上以信息排中律为前提反驳上述两者；[PCompHaus]，第4项的比较函子及其余部分属于 #1328。该记录完成了 Test/ProbeStoneCech455.v 的控制 [p455_TopP]，其仅有联合公理，形式如下(a)：它添加了另外四个公理，并重新表述联合公理为(b)。Instance/Top/StoneCech.v 的头文件将该控制引用为编码的首次测量。联合公理，以双向衡量。对于Prop值的开集，有两个“任意并”的陈述可用：
 (a) 在点的宇宙的索引类型上，[∀ (I : Type@{o}) (U : I → X → Prop), (∀ i, POpen (U i)) → POpen (fun x => ex (fun i => U i x))]，[p455_TopP]的形式；
 (b) 对于作为谓词上的Prop值谓词给出的开集族，[∀ F, (∀ U, F U → POpen U) → POpen (fun x => ex (fun U => F U /\ U x))]，这是本文件的[popen_union]。两者都已被编译，在包含本文件的临时文件Instance/Top/Subspace.v里，以及一个记录的副本中，用(a)替代了(b)。根据 (a)，子空间的并集由所有见证开的并集证明，这些开集由索引对（索引，X 的开集）索引；该索引类型在 [Type@{max(Set+1,o)}]（关于）处读取，并且在 [o := Set] 处用作并集索引时被拒绝，“无法强制 Set+1 <= Set”，而在声明的 [Set < o] 下则被接受；因此，由该对索引见证构建的子空间，这是尝试的唯一路径，携带 [Set < o]。从 (a) 推导 (b) 需要索引 [{ U | F U }]，并在 [Set] 以相同方式被拒绝，在 [Set < o] 下被接受。在 (b) 下，Instance/Top/Subspace.v 的 [PSub] 在 [PTop@{Set}] 被接受（同一个草稿文件，一个空的约束块），并且 (a) 在每个索引宇宙下成立：[popen_union_indexed@{o i}]，其约束块为空。(b) 因此是一个领域，有三个原因：它在开集的任意族的并下是闭合的，没有需要界定的索引类型；它在每一个索引宇宙上都蕴含 (a)，所以《七个草图》中关于索引集合的并如所述成立（Instance/Top/Subspace.v 的 [ex732_part2] 使用了它们）；并且它释放了 [Set < o] 的子空间约束。这里没有任何内容表明在 [o := Set] 上 (b) 严格强于 (a)；只是那里的直接推导被拒绝了。优势。[PForget_fobj] 和 [PForget_fmap] 在 [eq_refl] 上成立：空间的基础集合是其点集合，箭头的基础映射是其集合映射。[PForget_Faithful] 是同态集合证明上的恒等：[PMor_Setoid] 精确比较基础映射（逐点）并忽略连续性证明。[popen_const] 使每个常量命题都是开放的，这是 Instance/Top.v 的 [open_const] 的命题类比，[popen_empty] 是其情况 [False]。在以下具体空间中，[PDiscrete_carrier]、[PDiscrete_open] 和 [pdisc_mor_map] 在 [eq_refl] 上也成立。混凝土空间。[PDiscrete S] 是集合等价类上的离散拓扑
 [S]：它的开集是遵循点的相等性的谓词
 （[pdisc_open]），在集合等价类的纪律下，这就是整个条件，[popen_proper] 对每个开集都进行该要求。它是一个包含五个 [Qed] 引理的记录字面量，因此它的点和开集在 [eq_refl]（[PDiscrete_carrier]，[PDiscrete_open]）处可读回。相反，通过 [refine] 在证明模式中构建，并由 [Qed] 关闭，正如 #457 的评审原型所示，[eq_refl] 处的点可读回被拒绝（Coq：无法统一“pt_carrier (PDiscreteQ S)”和“S”，在一个携带该文件的草稿文件中命名为 [PDiscreteQ] 的 Qed 副本）；经过测量，但未固定。从离散空间到每个集合等价类的映射都是连续的 ([pdisc_cont])，因此 [pdisc_mor S Y f] 作为 [PTopCat] 的箭头 ([pdisc_mor_map]，在 [eq_refl]) 是 [f]；[pconst S Y y] 是空间中的一点 [y] 的常量集合等价类映射。[PPoint] 和 [PBool] 是 Instance/Sets.v 中 [unit_setoid_object] 和 [bool_setoid_object] 的离散空间，[PBool_points_distinct] 在 [PBool] 中反驳了 [false ≈ true]，其等同性为莱布尼茨。他们是树的第一个命名的 [PTop]：在树的 .v 文件中对 [Build_PTop] 和 [pt_carrier :=] 进行 grep 发现，除了 [PDiscrete]，只有 Instance/Top/Subspace.v 中的 [PSub] 和 [PQuot] 与它们一起定义了一个空间，两个都是由变量构建的。更正 (#410)：在 #410 的树上重新运行相同的 grep 也会找到 Instance/Top/Complete.v、Instance/Top/Cocomplete.v、Instance/Top/Separation.v 和 Instance/Top/Hausdorff.v，它们是在其之后加入的，以及 Instance/Top/Circle.v 的 [PRLine]，实数轴。更正 (#462)：在 #462 的树上，它还会找到 Instance/Top/Components.v，其三点空间 [PZig] 是用它们构建的。Instance/Top/Subspace.v 对它们之间的两个不同映射取了一个等化器和一个余等化器。UNIVERSES，由 [About] 在 [Set Printing Universes] 下读取。- [PTop@{o} : Type@{max(Set+1,o+1)}]，空块。[Set+1] 是 Prop 值谓词类型的排序；由于 [Set <= o] 排序是 [o+1]，并且 [PTop@{Set} : Type@{Set+1}] 被接受。- [PMor@{o} : PTop@{o} → PTop@{o} → Type@{o}]，空块：hom 位于点的宇宙，其中 Test/ProbeStoneCech455.v 的 N6 拒绝 [ContinuousMorphism]。[PCont@{o}]、[PMor_Setoid@{o}]（一个 [Setoid@{o o}]）、[pcont_respects@{o}]、[popen_const@{o}] 和 [popen_union_indexed@{o i}] 也有空块。- [pid@{o}] 载有 [o <= ID.u0] 和 [pcompose@{o}] 这三个 [o <= compose.u*] 帽：Instance/Sets.v 的 stdlib 帽 [setoid_morphism_id] 和 [setoid_morphism_compose]，它们在各自的块中携带它们，[Sets@{o so}] 也携带它们。- [PTopCat@{o so} : Category@{so o o}]，块 [Set < so]，[o < so] 以及那四个大写字母：[Sets@{o so}] 的块加上 [Set < so]， [o < so] 表示，并且记录 [PTop] 的类型。- [PForget@{o so} : PTopCat@{o so} ⟶ Sets@{o so}]，同一个块；[PForget_Faithful@{o so} : Faithful@{so o so} PForget@{o so}]。- [PDiscrete@{o} : SetoidObject@{o o} → PTop@{o}]，空块，如同 [pdisc_open@{o}]，其五个引理，[PDiscrete_carrier]，[PDiscrete_open]，[pdisc_cont@{o}]，[pdisc_mor@{o}]，[pdisc_mor_map] 和 [pconst@{o}]。[PPoint@{o} : PTop@{o}]，[PBool@{o} : PTop@{o}] 和 [PBool_points_distinct@{o}] 携带一个大写字母 [o <= Logic_lemmas.equality.u0]，Instance/Sets.v 的 [unit_setoid_object] 和 [bool_setoid_object] 在它们自己的块中携带。此文件的任何宇宙均未固定在 [Set]。在所有 51 个此文件的常量（包括其 [Print Module] 列表中的 49 个名称及义务，以及两个记录构造函数）的 [About] 输出中，单词 [Set] 出现在 [PTop] 的排序中，并且作为 [Set < so] 出现在 12 个块中：[PTopCat]、[PForget]、它们的七个义务、[PForget_fobj]、[PForget_fmap] 和 [PForget_Faithful]。未交付。此文件中没有与 [Top] 的比较，没有 [PCompHaus]，也没有 [PTopCat] 的极限或余极限：它的等化器和余等化器是 Instance/Top/Subspace.v 的 [PTop_HasEqualizers] 和 [PTop_HasCoequalizers]，并且它的积没有构建；没有非离散、空或其他非离散命名空间（命名空间是离散的）；没有离散或非离散函子，也没有伴随三重，对应 Instance/Top/Forgetful.v，在 [PTopCat] 上；没有分离性或紧性概念；并且没有声明在 [o := Set] 处 (b) 比 (a) 严格更强。更正 (#458)：那些极限、余极限和函子不再在树中缺失，只是在此文件中缺失。这些积和 [PTopCat] 的所有小极限都是 Instance/Top/Complete.v 的实例（[PProd]、[PTop_Complete]），它的余积和所有小余极限是 Instance/Top/Cocomplete.v 的实例（[PSigma]、[PTop_Cocomplete]），在每个形状宇宙中都不超过 points 。离散函子和非离散函子分别是 [PDisc]（Instance/Top/Complete.v）和 [PIndisc]（Instance/Top/Cocomplete.v），伴随三重态 [PDisc ⊣ PForget ⊣ PIndisc] 作为两个伴随，[PDisc_PForget] 和 [PForget_PIndisc] ，正如 Instance/Top/Forgetful.v 陈述其自身一样。已命名的空间中也存在非离散的空间：集合 [PIndiscrete] 上的不可离散空间，以及不可离散的两点空间 [PTwoIndisc]（Instance/Top/Cocomplete.v），它们的和 [PTwoIndiscSum]，其拓扑既非离散也非不可离散（[PTwoIndiscSum_not_discrete]、[PTwoIndiscSum_not_indiscrete]），以及 Instance/Top/Complete.v 中的收敛序列 [PConv]，其极限点不是开集（[pconv_limit_point_not_open]）。更正 (#461)：关于 [PTopCat] 的分离概念现在也存在于 Instance/Top/Separation.v（[PT0]、[PT1]、正豪斯多夫形式 [PHaus] 及其反射）和 Instance/Top/Hausdorff.v（正则空间，以及通过一般伴随函子定理得到的豪斯多夫反射）；紧性仍然不存在。
*)

#[local] Obligation Tactic := idtac.

(** ** Spaces *)

(*
 A space: a setoid of points and a Prop-valued predicate on its
 Prop-valued predicates, closed under the book's operations.  The union
 field takes a FAMILY of opens, itself a Prop-valued predicate on
 predicates, and forms its union; see the header for why it is not stated
 over an index type. 

 --------
 一个空间：一组点以及其上的一个 Prop 值谓词，对其 Prop 值谓词封闭于书中的操作。并集域接受一族开集，它本身是谓词上的 Prop 值谓词，并形成其并集；参见标题了解为什么它没有在索引类型上陈述。
*)
Record PTop@{o} := {
  pt_carrier :> SetoidObject@{o o};    (* the setoid of points / 点的集合体 *)

  (* the topology: which predicates on the points are open / 拓扑：哪些点的谓词是开放的 *)
  POpen : (pt_carrier → Prop) → Prop;

  (* being open is invariant under pointwise equivalence of predicates / 在谓词的逐点等价下，开性是不变的 *)
  popen_respects (U V : pt_carrier → Prop) :
    (∀ x, U x <-> V x) → POpen U → POpen V;

  (* every open respects the carrier's own equality on points / 每一次开放都尊重承运人在积分上的平等 *)
  popen_proper (U : pt_carrier → Prop) :
    POpen U → ∀ x y : pt_carrier, x ≈ y → U x → U y;

  (* closure under arbitrary unions: the union of every family of opens / 任意并下的封闭性：每个开集族的并 *)
  popen_union (F : (pt_carrier → Prop) → Prop) :
    (∀ U, F U → POpen U) → POpen (fun x => ex (fun U => F U /\ U x));

  (* the whole space is open / 整个空间都是开放的 *)
  popen_whole : POpen (fun _ => True);

  (* closure under binary intersection / 在二元交集下的封闭性 *)
  popen_inter (U V : pt_carrier → Prop) :
    POpen U → POpen V → POpen (fun x => U x /\ V x)
}.

(*
 The union of a family indexed by a type, at ANY universe [i]: the family
 of the predicates pointwise equivalent to some [U k] is a Prop-valued
 family of opens, and its union is the indexed one. 

 --------
 由类型索引的族的并集，在任意宇宙 [i] 上：与某个 [U k] 点对点等价的谓词族是一个取值为命题的开集族，其并集就是所索引的那个。
*)
Lemma popen_union_indexed@{o i} (X : PTop@{o}) (I : Type@{i})
  (U : I → pt_carrier X → Prop) :
  (∀ k, POpen X (U k)) → POpen X (fun x => ex (fun k => U k x)).
Proof.
  intro HU.
  apply (popen_respects X
           (fun x => ex (fun W => ex (fun k => ∀ y, W y <-> U k y) /\ W x))).
  - intro x; split.
    + intros [W [[k Hk] w]]. exists k. exact (proj1 (Hk x) w).
    + intros [k u]. exists (U k). split; [|exact u].
      exists k. intro y; exact (iff_refl _).
  - apply popen_union.
    intros W [k Hk].
    apply (popen_respects X (U k)); [|exact (HU k)].
    intro y; exact (iff_sym (Hk y)).
Qed.

(*
 Every constant proposition is open: the union of the family holding of
 the whole space exactly when [P] does. 

 --------
 每个常量命题都是开放的：当且仅当 [P] 开放时，全空间的该族并集也是开放的。
*)
Lemma popen_const@{o} (X : PTop@{o}) (P : Prop) : POpen X (fun _ => P).
Proof.
  apply (popen_respects X
           (fun x => ex (fun W => (P /\ ∀ y, W y <-> True) /\ W x))).
  - intro x; split.
    + intros [W [[p _] _]]; exact p.
    + intro p. exists (fun _ => True). split; [split; [exact p|]|exact I].
      intro y; exact (iff_refl _).
  - apply popen_union.
    intros W [_ HW].
    apply (popen_respects X (fun _ => True)); [|exact (popen_whole X)].
    intro y; exact (iff_sym (HW y)).
Qed.

(* The empty predicate is open: [popen_const] at [False]. / 空谓词是开放的：[popen_const] 在 [False]。 *)
Corollary popen_empty@{o} (X : PTop@{o}) : POpen X (fun _ => False).
Proof. exact (popen_const X False). Qed.

(** ** Continuous maps / ** 连续映射 *)

(*
 Continuity: the preimage of every open is open.  It is a proposition, so
 a continuous map is a setoid map with a proof attached, at the level of
 the points. 

 --------
 连续性：每个开集的原像是开集。这是一个命题，因此连续映射是在点的层面上附有证明的集合等价映射。
*)
Definition PCont@{o} {X Y : PTop@{o}} (f : SetoidMorphism@{o o o} X Y) :
  Prop :=
  ∀ U : Y → Prop, POpen Y U → POpen X (fun x => U (f x)).

(* Continuity depends on the map only up to pointwise [≈]: every open respects the codomain's equality. / 连续性仅依赖于点状 [≈] 的映射：每个开集都尊重值域的相等性。 *)
Lemma pcont_respects@{o} {X Y : PTop@{o}} (f g : SetoidMorphism@{o o o} X Y) :
  (∀ x, f x ≈ g x) → PCont f → PCont g.
Proof.
  intros Hfg Hf U HU.
  apply (popen_respects X (fun x => U (f x))); [|exact (Hf U HU)].
  intro x; split; intro u.
  - exact (popen_proper Y U HU (f x) (g x) (Hfg x) u).
  - exact (popen_proper Y U HU (g x) (f x) (symmetry (Hfg x)) u).
Qed.

Record PMor@{o} (X Y : PTop@{o}) : Type@{o} := {
  pmap :> SetoidMorphism@{o o o} X Y;
  pcont : PCont pmap
}.

Arguments pmap {X Y} _.
Arguments pcont {X Y} _ _ _.

(* The hom-setoid compares the map parts pointwise, as [Sets] does; the continuity proofs are not compared. / 同态集合通过逐点比较映射部分，就像 [Sets] 那样；连续性证明则不进行比较。 *)
Program Definition PMor_Setoid@{o} (X Y : PTop@{o}) :
  Setoid@{o o} (PMor@{o} X Y) := {|
  equiv := fun f g => ∀ x, pmap f x ≈ pmap g x
|}.
Next Obligation.
  intros X Y; constructor.
  - intros f x; reflexivity.
  - intros f g H x; symmetry; exact (H x).
  - intros f g k H1 H2 x; transitivity (pmap g x); [exact (H1 x)|exact (H2 x)].
Qed.

Definition pid@{o} (X : PTop@{o}) : PMor@{o} X X :=
  {| pmap := setoid_morphism_id@{o o o}; pcont := fun U H => H |}.

Definition pcompose@{o} {X Y Z : PTop@{o}} (g : PMor@{o} Y Z)
  (f : PMor@{o} X Y) : PMor@{o} X Z :=
  {| pmap := setoid_morphism_compose@{o o o} g f;
     pcont := fun U H => pcont f _ (pcont g U H) |}.

Lemma pcompose_respects@{o} {X Y Z : PTop@{o}} :
  Proper@{o o} (@equiv _ (PMor_Setoid@{o} Y Z)
                ==> @equiv _ (PMor_Setoid@{o} X Y)
                ==> @equiv _ (PMor_Setoid@{o} X Z)) (@pcompose@{o} X Y Z).
Proof.
  intros g1 g2 Hg f1 f2 Hf x; simpl.
  transitivity (pmap g1 (pmap f2 x)).
  - apply proper_morphism, Hf.
  - apply Hg.
Qed.

(* * ** The category and its underlying-set functor / * ** 类别及其底层集合函子 *)

Program Definition PTopCat@{o so | o < so +} : Category@{so o o} := {|
  obj     := PTop@{o};
  hom     := PMor@{o};
  homset  := PMor_Setoid@{o};
  id      := pid@{o};
  compose := @pcompose@{o};

  compose_respects := @pcompose_respects@{o}
|}.
Solve All Obligations with (intros; simpl; intros; reflexivity).

(* The points, into the Sets whose objects ARE the point setoids. / 这些点，进入其对象是点集的集合中。 *)
Program Definition PForget@{o so | o < so +} :
  PTopCat@{o so} ⟶ Sets@{o so} := {|
  fobj := fun X => pt_carrier X;
  fmap := fun X Y f => pmap f
|}.
Next Obligation. intros X Y f g H x; exact (H x). Qed.
Next Obligation. intros X x; reflexivity. Qed.
Next Obligation. intros X Y Z f g x; reflexivity. Qed.

Example PForget_fobj@{o so | o < so +} (X : PTop@{o}) :
  fobj[PForget@{o so}] X = pt_carrier X := eq_refl.

Example PForget_fmap@{o so | o < so +} {X Y : PTop@{o}}
  (f : X ~{PTopCat@{o so}}~> Y) :
  fmap[PForget@{o so}] f = pmap f := eq_refl.

#[export] Instance PForget_Faithful@{o so | o < so +} :
  Faithful PForget@{o so}.
Proof. constructor; intros x y f g H p; exact (H p). Qed.

(* * ** Concrete spaces: the discrete topology, the point and two points / * **具体空间：离散拓扑、单点和双点 *)

(*
 The discrete topology on a setoid: every predicate respecting the
 points' equality is open.  The setoid discipline makes that respect the
 whole condition: without it [popen_proper] could not hold. 

 --------
 集合上的离散拓扑：每个尊重点等式的谓词都是开的。集合纪律使得这种尊重成为整个条件：没有它，[popen_proper] 就无法成立。
*)
Definition pdisc_open@{o} (S : SetoidObject@{o o}) (U : S → Prop) : Prop :=
  ∀ x y : S, x ≈ y → U x → U y.

Lemma pdisc_open_respects@{o} (S : SetoidObject@{o o}) (U V : S → Prop) :
  (∀ x, U x <-> V x) → pdisc_open S U → pdisc_open S V.
Proof.
  intros HUV HU x y Hxy v.
  apply (proj1 (HUV y)), (HU x y Hxy), (proj2 (HUV x)), v.
Qed.

Lemma pdisc_open_proper@{o} (S : SetoidObject@{o o}) (U : S → Prop) :
  pdisc_open S U → ∀ x y : S, x ≈ y → U x → U y.
Proof. intro HU; exact HU. Qed.

Lemma pdisc_open_union@{o} (S : SetoidObject@{o o})
  (F : (S → Prop) → Prop) :
  (∀ U, F U → pdisc_open S U) →
  pdisc_open S (fun x => ex (fun U => F U /\ U x)).
Proof.
  intros HF x y Hxy [U [FU u]]. exists U; split; [exact FU|].
  exact (HF U FU x y Hxy u).
Qed.

Lemma pdisc_open_whole@{o} (S : SetoidObject@{o o}) :
  pdisc_open S (fun _ => True).
Proof. intros x y _ t; exact t. Qed.

Lemma pdisc_open_inter@{o} (S : SetoidObject@{o o}) (U V : S → Prop) :
  pdisc_open S U → pdisc_open S V → pdisc_open S (fun x => U x /\ V x).
Proof.
  intros HU HV x y Hxy [u v]; exact (conj (HU x y Hxy u) (HV x y Hxy v)).
Qed.

(* A record literal over the five lemmas, so that the points and the opens read back at [eq_refl]. / 在这五个引理上有一个记录字面值，这样分数和开放项就可以在 [eq_refl] 上读回。 *)
Definition PDiscrete@{o} (S : SetoidObject@{o o}) : PTop@{o} := {|
  pt_carrier     := S;
  POpen          := pdisc_open S;
  popen_respects := pdisc_open_respects S;
  popen_proper   := pdisc_open_proper S;
  popen_union    := pdisc_open_union S;
  popen_whole    := pdisc_open_whole S;
  popen_inter    := pdisc_open_inter S
|}.

Example PDiscrete_carrier@{o} (S : SetoidObject@{o o}) :
  pt_carrier (PDiscrete S) = S := eq_refl.

Example PDiscrete_open@{o} (S : SetoidObject@{o o}) (U : S → Prop) :
  POpen (PDiscrete S) U = (∀ x y : S, x ≈ y → U x → U y) := eq_refl.

(* Every setoid map out of a discrete space is continuous: the preimage of an open respects the domain's equality because the map and the open do. / 从离散空间出发的每个集合等价映射都是连续的：开集的原像遵循定义域的等价关系，因为映射和开集都遵循。 *)
Lemma pdisc_cont@{o} (S : SetoidObject@{o o}) (Y : PTop@{o})
  (f : SetoidMorphism@{o o o} S Y) : @PCont (PDiscrete S) Y f.
Proof.
  intros U HU x y Hxy u.
  exact (popen_proper Y U HU (f x) (f y) (proper_morphism f x y Hxy) u).
Qed.

Definition pdisc_mor@{o} (S : SetoidObject@{o o}) (Y : PTop@{o})
  (f : SetoidMorphism@{o o o} S Y) : PMor@{o} (PDiscrete S) Y :=
  @Build_PMor (PDiscrete S) Y f (pdisc_cont S Y f).

Example pdisc_mor_map@{o} (S : SetoidObject@{o o}) (Y : PTop@{o})
  (f : SetoidMorphism@{o o o} S Y) : pmap (pdisc_mor S Y f) = f := eq_refl.

(*
 The constant map at a point [y] of a space, as a setoid map from any
 setoid. 

 --------
 空间中某一点 [y] 的常值映射，作为从任何集合等价类到该空间的集合等价类映射。
*)
Definition pconst@{o} (S : SetoidObject@{o o}) (Y : PTop@{o}) (y : Y) :
  SetoidMorphism@{o o o} S Y :=
  {| morphism := fun _ => y; proper_morphism := fun _ _ _ => reflexivity y |}.

(* The one-point space and the two-point discrete space, on Instance/Sets.v's [unit_setoid_object] and [bool_setoid_object]. / 单点空间和两点离散空间，在 Instance/Sets.v 的 [unit_setoid_object] 和 [bool_setoid_object] 上。 *)
Definition PPoint@{o} : PTop@{o} := PDiscrete unit_setoid_object@{o o}.

Definition PBool@{o} : PTop@{o} := PDiscrete bool_setoid_object@{o o}.

(* The two points of [PBool] are distinct: its equality is Leibniz. / [PBool] 的两个点是不同的：它的等式是莱布尼茨。 *)
Lemma PBool_points_distinct@{o} : @equiv _ PBool@{o} false true → False.
Proof. intro H; discriminate H. Qed.
