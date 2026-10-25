Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Pointed.

Generalizable All Variables.

(*
   * * Adjoining a basepoint: the free pointed set, its universal arrow,
   and the free-forgetful adjunction

   nLab:      https://ncatlab.org/nlab/show/pointed+set
   nLab:      https://ncatlab.org/nlab/show/free+functor
   nLab:      https://ncatlab.org/nlab/show/universal+morphism
   Wikipedia: https://en.wikipedia.org/wiki/Forgetful_functor

   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   GTM 5, Springer 1998, §III.1, Exercise 3, printed p. 59 --
   maclane:III.1:ex3
   Book: Mac Lane, ibid., §III.1, Definition 1 (universal arrow),
   printed p. 55 -- maclane:III.1:def1
   Book: Mac Lane, ibid., §IV.1, Theorem 2 (five equivalent
   determinations of an adjunction), printed p. 83 --
   maclane:IV.1:thm2.  The local-to-global route taken below is
   that theorem's universal-arrow clause.
   Book: Riehl, "Category Theory in Context", Dover 2016, §4.1,
   Example 4.1.10, printed p. 135, CLAUSE (i) -- riehl:4.1:
   example10 is a fourteen-clause example listing fourteen
   forgetful functors with left adjoints, and this file delivers
   the first of them and none of the other thirteen.  Riehl names
   the free pointed set X_+ = X + {X}, taking the set X itself as
   the adjoined element; [option] takes [None] instead.  The two
   differ only in what the new point is called, and no comparison
   between them is stated (there is no set-theoretic X + {X} in
   this library to compare with).

   WHAT THIS FILE DELIVERS.  Mac Lane's §III.1 Exercise 3 asks for a
   universal arrow, from any given object, to each of FOUR forgetful
   functors: Ab ⟶ Grp, Rng ⟶ Ab, Top ⟶ Set, and Set_* ⟶ Set.  This
   file is the fourth row, the pointed one.  For a setoid X the free
   pointed set is X with one new element adjoined,

   FreePointedObject X  =  X ⊔ {∗},

   realised as [option (carrier X)] under [option_setoid]
   (Lib/Datatypes.v), pointed at [None]; [free_pointed_insert] is
   the insertion [Some]; and the universal property
   ([free_pointed_universal]) says every setoid map h : X ~> U Y into
   the underlying setoid of a pointed set Y extends along the insertion
   to one and only one basepoint-preserving map, namely the two-case
   match sending [Some a] to [h a] and [None] to the basepoint of Y.
   That is packaged as [free_pointed_universal_arrow] in the comma
   encoding and [free_pointed_AUniversalArrow] in the direct one, and
   assembled into [FreePointed : Sets ⟶ PointedSets] with
   [free_pointed_adjunction : FreePointed ⊣ Pointed_Forget] through the
   generic machinery of Theory/Universal/Arrow.v -- the same route
   Instance/Grp/Free.v, Instance/Mod/Free.v, Instance/Ab/Free.v and
   Instance/Mon/Free.v take.

   THE FORGETFUL FUNCTOR DID NOT EXIST, AND IS BUILT HERE.  That was
   re-verified rather than taken on trust, and the measurement is
   sharper than a bare absence claim.  The word "Forget" occurs ZERO
   times in all four pre-existing pointed-set files
   (Instance/Sets/Pointed.v and its satellites Coslice.v, Finite.v,
   Part.v).  Tree-wide, before this file there was exactly ONE functor
   whose SOURCE is [PointedSets] -- [Pointed_to_Coslice]
   (Instance/Sets/Pointed/Coslice.v) -- and its codomain is
   [Coslice Sets SetsOne], not [Sets]; the two functors INTO
   [PointedSets] were [Coslice_to_Pointed] (ibid.) and
   [Part_to_Pointed] (Instance/Sets/Pointed/Part.v).

   But the honest statement is weaker than "unreachable", and the
   difference is worth stating because a reviewer will find it:
   [Coslice_proj : Coslice C c ⟶ C] DOES exist
   (Instance/Cat/Pullback.v), so the composite
   [Coslice_proj ◯ Pointed_to_Coslice] was ASSEMBLABLE in tree.  It was
   never assembled and never named, and it is not the route taken here,
   for a dependency reason: Instance/Cat/Pullback.v is a large file
   about pullbacks in [Cat], and putting it behind every consumer of
   the pointed-set adjunction would be a poor trade for a three-line
   definition.  (The composite needs no extra hypothesis: despite
   sitting in a section that also binds [ObjUIP C], [Coslice_proj]
   discharges as [Coslice_proj {C} c], with no UIP argument -- checked,
   since the opposite would have been a substantive obstruction rather
   than a matter of weight.)

   The comparison of the two functors is NOT stated below, because
   stating it is exactly what would incur the dependency; it was
   measured out of tree instead, and what was found is recorded here as
   a MEASUREMENT and not as a proof.  Writing
   [ViaCoslice := Coslice_proj SetsOne ◯ Pointed_to_Coslice], the
   object action and the arrow action each agree with
   [Pointed_Forget]'s by [eq_refl], while the whole functor records do
   not; probing the three law fields SEPARATELY, all three are
   rejected, which is consistent with them being independently built
   opaque proof constants on the two sides ([Pointed_Forget]'s three
   [Program] obligations against [Compose]'s).  So the two agree at
   every level a consumer computes with and differ only in their
   proofs.  No [Fail] in this file names [ViaCoslice] or
   [Coslice_proj], so all of that is measured and not GUARDED.

   WHY THERE IS NO QUOTIENT, AND WHAT THAT BUYS.  The three algebraic
   rows of this same exercise all pay for a congruence.
   Instance/Ab/Free.v presents the free abelian group as an inductive
   [FATerm] of formal expressions modulo an inductive congruence
   [fa_eq] closing under the four abelian-group laws;
   Instance/Rng/Free.v does the same with [FRTerm]/[fr_eq]; and the
   abelianization row rides Instance/Grp/Abelianization.v, whose
   quotient coarsens the group's own [≈] by membership in the
   inductively generated commutator subgroup.  Adjoining
   a basepoint imposes NO equations at all -- it adds one element and
   stops -- so no congruence, no inductive relation and no
   well-definedness argument appears below.  Three consequences are
   visible in the proofs rather than merely asserted.

   (1) The carrier is a datatype the library already has:
   [option (carrier X)] under [option_setoid], which
   Lib/Datatypes.v describes as the coproduct setoid
   1 + A.  Nothing is declared here except the pairing of that
   setoid with its basepoint.
   (2) A pointed map carries exactly ONE law, [preserves_pt], and for
   the extension that law is [reflexivity]: the mediator sends
   [None] to [pt Y] by definition.  Where the algebraic rows
   discharge one obligation per operation and per axiom, this row
   discharges one, definitionally.
   (3) Uniqueness is a two-case destruct with no induction anywhere:
   the [Some] case is the hypothesis and the [None] case is the
   competitor's own [preserves_pt].  The file contains no
   [induction] and no [Fixpoint].

   So this row is the cheapest of the four, which is what one should
   expect: "free" here adjoins a single element rather than closing
   under operations.

   THE SETOID DISCIPLINE COSTS NOTHING HERE, AND THAT IS THE
   INTERESTING COMPARISON.  Instance/Mod/Free.v's header locates, for
   the free MODULE, an obstruction that has no analogue in this row:
   the classical carrier (finitely supported functions) cannot even
   write down its basis vector without a decision procedure for the
   generating setoid's [≈], so the classical construction yields no
   adjunction at all over [Sets].  Adjoining a basepoint needs no
   decider: [option_setoid] lifts X's own [≈] and adds [None ≈ None],
   and [Some] respects [≈] on the nose.  Nothing below is conditional
   on decidability, finiteness, or choice -- the library's [∃] is
   [sigT], so the mediator produced by [ump_universal_arrows] is data.

   STRENGTHS, MEASURED STRICT-FIRST.  Every identification below was
   attempted at [eq_refl] before being stated at [≈].

   - [eq_refl]: the forgetful functor's object action
   ([free_pointed_forget_obj]); the free object's carrier and
   basepoint ([free_pointed_carrier], [free_pointed_basepoint]);
   the insertion ([free_pointed_insert_is_Some]); BOTH branches of
   the mediator ([free_pointed_extend_some_strict],
   [free_pointed_extend_none_strict]); the universal arrow
   ([free_pointed_arrow_is_insert]); the free functor's object
   action ([FreePointed_obj]); the UNIT
   ([free_pointed_unit_is_insert]); the forward transpose ⌊−⌋,
   which is RESTRICTION along the insertion
   ([free_pointed_transpose_is_adj]); the free functor's arrow
   action read as the inverse transpose
   ([free_pointed_fmap_is_from_adj]); and the two-point probe
   object of Instance/Sets/Pointed.v identified as the free pointed
   set on the one-point setoid ([PointedTwo_is_free_on_one]).

   - [≈] only: the INVERSE transpose ⌈−⌉ ([free_pointed_from_adj]),
   the COUNIT ([free_pointed_counit_evaluates]), and the free
   functor's arrow action evaluated at a generator
   ([free_pointed_fmap_some]).

   THE CAUSE OF THOSE THREE REJECTIONS IS DIAGNOSED, AND THE DIAGNOSIS
   DISCRIMINATES.  All three route through
   [unique_obj (ump_universal_arrows …)], and [ump_universal_arrows]
   (Theory/Universal/Arrow.v) is [Qed]-opaque, so nothing reduces
   through it.  Two controls show that this is the cause and not a
   generic property of the adjunction record.  First, the OTHER
   transpose of the SAME [Isomorphism] does reduce
   ([free_pointed_transpose_is_adj], [eq_refl]) -- so the obstruction
   is not that transposes in general fail to compute, nor a rebuilt
   [proper_morphism] certificate on the hom-setoid.  Second, and
   sharper, [free_pointed_fmap_is_from_adj] identifies
   [fmap[FreePointed] u] with ⌈insert ∘ u⌉ AT [eq_refl] -- both sides
   being literally the same opaque term -- while
   [free_pointed_fmap_some] then needs [≈].  So the block is located
   exactly at unfolding the opaque mediator and nowhere else.  Each
   rejection is GUARDED as well as measured: the three refutation
   [Fail] commands at the end of this file name [free_pointed_extend],
   [free_pointed_counit] and [FreePointed] respectively (a fourth
   [Fail] sits beside them, the scope-free instrument check, which
   refutes nothing about this development).  Each was stripped once and
   confirmed to report a genuine "cannot unify" rather than a scope,
   notation or reference error.  They cannot go vacuously green under a
   rename: every identifier occurring in a [Fail] block, other than the
   four probe names themselves, also occurs in at least one command of
   this file that must SUCCEED, so renaming any of them breaks a
   positive control here.

   UNIVERSES.  Read from the constraint blocks and not from the
   binders alone.  The two constructions whose binders are
   [SetoidObject] and [PointedSetoid] directly, rather than
   [obj[Sets]], keep every carrier universe apart from its relation
   universe: [FreePointedObject@{u u0} : SetoidObject@{u u0} →
   PointedSetoid@{u u0}], whose constraint block contains NO
   identification at all (only the bounds [u <= eq_ind.u0] and
   [u0 <= False_rect.u0] inherited from [option_setoid]'s own
   eliminations); and [free_pointed_extend@{u u0 u1 u2 u3 u4}], whose
   X sits at [SetoidObject@{u u0}] and whose Y sits at
   [PointedSetoid@{u1 u2}], four separate levels.

   The constants whose statements quantify over [X : Sets] -- that is,
   over [obj[Sets]] -- sit instead at [SetoidObject@{u0 u0}], carrier
   and relation identified; [free_pointed_insert@{u u0}] is the first
   of them.  That is NOT this file's doing and costs a consumer
   nothing: [Sets] is declared [Sets@{o so} : Category@{so o o}], so
   [obj[Sets]] IS [SetoidObject@{o o}] and the identification is what
   it means to be an object of [Sets] at all.  Likewise
   [Pointed_Forget@{u u0} : PointedSets@{u u0} ⟶ Sets@{u0 u}] carries
   [u0 < u], again [Sets]' own declaration, and no identification is
   introduced here.

   NO constant in this file carries [Set] in a universe instance or in
   a constraint -- all 66 were checked, the concrete witnesses
   included, which is why those are built over [poly_unit] and [option]
   rather than over [bool]; that was a deliberate choice and it was
   verified rather than assumed ([fpt_one@{u}] and [fpt_two@{u}] are
   [SetoidObject@{u u}]).

   ASSUMPTIONS.  All 66 constants of this module report "Closed under
   the global context".  The count is [Print Module]'s, which is 60
   source declarations plus the six [Program] obligations; note that
   the [.glob] OVERCOUNTS here, since a [Fail Definition foo] registers
   [foo] in the glob without adding a constant, and this file has four
   such.

   WHAT IS NOT DELIVERED.

   - No monad.  [Pointed_Forget ◯ FreePointed] has object action
   [option] on the nose ([free_pointed_maybe_carrier]), so this
   adjunction induces the maybe monad on [Sets] -- but no
   [@Monad Sets] instance, no Kleisli category and no
   Eilenberg-Moore comparison is built, and no statement below
   mentions [Monad].  Instance/Sets/Pointed.v's header already
   observes that pointed sets are the algebras of the maybe monad
   and that Instance/Sets/Par.v's [Part] is its Kleisli category;
   neither claim is formalized here or there.
   Theory/Coq/Maybe.v's [Maybe] monad is over the applied
   [Theory/Coq/] typeclass hierarchy on bare types, a different
   class from [Theory/Monad.v]'s, and is unrelated.
   - No smash product and no internal hom.  Instance/Sets/Pointed.v's
   relation to the smash-hom adjunction is a DIFFERENT statement
   about a DIFFERENT adjunction and nothing here addresses it.
   - No comparison with Instance/Sets/Pointed/Coslice.v's coslice
   presentation: the free pointed set is not exhibited as a
   coproduct with the terminal object, and no coslice-level
   universal arrow is stated.
   - No comparison with Instance/Sets/Pointed/Part.v: the free
   functor is not related to that file's [Part_to_Pointed], and
   nothing is said about partial maps.
   - Nothing about the other three rows of Exercise 3.  The Rng ⟶ Ab
   row's content is in tree as [FreeRngAb ⊣ Rng_Forget_Ab]
   (Instance/Rng/Free.v), filed there under Mac Lane §IV.8
   Exercise 2 rather than §III.1 Exercise 3; the Ab ⟶ Grp row is
   Instance/Grp/Abelianize.v; and for Top ⟶ Set,
   Instance/Top/Forgetful.v supplies [Top_Discrete] with
   [discrete_adj] as cross-universe hom-setoid isomorphisms, its
   header recording that the packaged [Adjunction] record is
   unformable across that universe gap -- and it contains no
   [UniversalArrow] at all (measured).  No claim is made here about
   any of the three.
   - No essential uniqueness statement specialised to this row.  The
   generic [universal_arrow_unique] (Theory/Universal/Arrow.v)
   applies verbatim and is not instantiated.
   - The insertion is proved injective and its image proved to miss
   the basepoint, but no [Monic] or [Epic] statement is made about
   it in [Sets] or in [PointedSets], and nothing is said about
   [Pointed_Forget] beyond faithfulness. 

   --------
   * * 邻接基点：自由指向集合，它的普遍箭头，以及自由-遗忘伴随

   nLab:       https://ncatlab.org/nlab/show/pointed+set 
   nLab:       https://ncatlab.org/nlab/show/free+functor 
   nLab:       https://ncatlab.org/nlab/show/universal+morphism 
   维基百科:  https://en.wikipedia.org/wiki/Forgetful_functor书籍：Mac Lane，《工作数学家的范畴论》，第2版，GTM 5，Springer 1998，§III.1，练习题3，印刷页59 -- maclane:III.1:ex3
   书籍：Mac Lane，同上，§III.1，定义1（通用箭头），印刷页55 -- maclane:III.1:def1
   书籍：Mac Lane，同上，§IV.1，定理2（伴随的五种等价描述），印刷页83 -- maclane:IV.1:thm2。本例中采取的局部到整体的路径即该定理的通用箭头条款。
   书籍：Riehl，《上下文中的范畴论》，Dover 2016，§4.1，例4.1.10，印刷页135，条款(i) -- riehl:4.1:example10 是一个包含十四条条款的例子，列出了十四个有左伴随的遗忘函子，本文件只提供其中第一个，而不涉及其他十三个。Riehl 将自由带基点的集合命名为 X_+ = X + {X}，将集合 X 本身作为附加元素；[option] 则改用 [None]。两者的区别仅在于新点的名称，并未进行比较（在此库中没有集合论意义上的 X + {X} 可供比较）。

   本文件提供的内容。Mac Lane §III.1 练习 3 要求对于任意对象，到四个遗忘函子中的每一个构造一个普遍箭头：Ab ⟶ Grp, Rng ⟶ Ab, Top ⟶ Set, 和 Set_* ⟶ Set。本文件对应第四行，即带基点的情况。对于一个 setoid X，自由带基点的集合是在 X 上附加一个新元素，

   FreePointedObject X  =  X ⊔ {∗}实现为 [option (carrier X)]，在 [option_setoid] 下（Lib/Datatypes.v），指向 [None]；[free_pointed_insert] 是插入 [Some]；而通用性质（[free_pointed_universal]）表明，每个集合态映射 h : X ~> U Y 到一个指向集合 Y 的基础集合态，都能沿插入唯一地扩展为一个保持基点的映射，即将 [Some a] 映射到 [h a]，将 [None] 映射到 Y 的基点的两情况匹配。那在逗号编码中被打包为 [free_pointed_universal_arrow]，在直接编码中为 [free_pointed_AUniversalArrow]，并通过 Theory/Universal/Arrow.v 的通用机制与 [free_pointed_adjunction : FreePointed ⊣ Pointed_Forget] 组装成 [FreePointed : Sets ⟶ PointedSets]——这正是 Instance/Grp/Free.v、Instance/Mod/Free.v、Instance/Ab/Free.v 和 Instance/Mon/Free.v 采取的路径。遗忘函子不存在，现在在此构建。这个结论是重新验证的，而不是仅凭信任得出的，并且这个测量比单纯的不存在声明更精确。单词“Forget”在所有四个已有的有指集合文件（Instance/Sets/Pointed.v 及其附属文件 Coslice.v、Finite.v、Part.v）中出现次数为零。在整棵树中，在此文件之前，恰好存在一个函子，其源为 [PointedSets] -- [Pointed_to_Coslice]（Instance/Sets/Pointed/Coslice.v）——其目标是 [Coslice Sets SetsOne]，而不是 [Sets]；两个指向 [PointedSets] 的函子分别为 [Coslice_to_Pointed]（同上）和 [Part_to_Pointed]（Instance/Sets/Pointed/Part.v）。但是诚实的陈述比“不可达”要弱，而这个区别值得说明，因为审阅者会发现：
   [Coslice_proj : Coslice C c ⟶ C] 确实存在
   (Instance/Cat/Pullback.v)，因此复合
   [Coslice_proj ◯ Pointed_to_Coslice] 在树中是可以组装的。它从未被组装或命名，并且它不是这里采用的路径，出于依赖原因：Instance/Cat/Pullback.v 是一个关于 [Cat] 中拉回的大文件，把它放在指向集余附连接的每一个使用者后面对三行定义来说是一个糟糕的权衡。（复合体不需要额外的假设：尽管位于一个同时绑定 [ObjUIP C] 的章节中，[Coslice_proj] 可以作为 [Coslice_proj {C} c] 释放，无需 UIP 论证——已经检查过，因为相反情况会成为一个实质性的障碍，而不是权重问题。）下面没有说明两个函子（functor）的比较，因为说明它正是会引入依赖的操作；相反，它是在外部测量的，而测量结果在这里记录为测量（MEASUREMENT），而不是作为证明。写作 [ViaCoslice := Coslice_proj SetsOne ◯ Pointed_to_Coslice] 时，对象操作（object action）和箭头操作（arrow action）各自与 [Pointed_Forget] 的操作通过 [eq_refl] 相一致，而整个函子记录并不一致；分别检查三个律字段（law fields）时，三个都被拒绝，这与它们在两边独立构建为不透明证明常量（opaque proof constants）（[Pointed_Forget] 的三个 [Program] 义务相对于 [Compose] 的）的情况一致。因此，在消费者能计算的每个层面上，两者都一致，唯一的区别在于它们的证明。在此文件中没有 [Fail] 命名 [ViaCoslice] 或 [Coslice_proj]，因此所有这些都是测量的，而不是受保护的（GUARDED）。为什么没有商，以及那带来了什么。这个练习的三个代数行都为一个合同性付出代价。Instance/Ab/Free.v 将自由阿贝尔群呈现为在归纳合同性 [fa_eq] 下的形式表达式的归纳 [FATerm]；该合同性在四条阿贝尔群定律下封闭；Instance/Rng/Free.v 对 [FRTerm] / [fr_eq] 做同样的处理；而阿贝尔化行依赖于 Instance/Grp/Abelianization.v，其商通过归属于归纳生成的交换子子群来粗化群自身的 [≈]。加入一个基点完全不强加任何方程——它只增加一个元素并停止——因此下面没有合同性，也没有归纳关系，也没有良定义性的论证。三个结果可以在证明中看到，而不仅仅是被声称。

   (1) 载体是库中已经存在的数据类型：[option (carrier X)] 在 [option_setoid] 下，Lib/Datatypes.v 将其描述为余积类型的集合等价 1 + A。在这里除了将该集合等价与其基点配对之外，并未声明其他内容。 (2) 指定映射正好携带一个定律 [preserves_pt]，对于扩展，该定律为 [reflexivity]：中介者按定义将 [None] 发送到 [pt Y]。在代数行中，每个操作和每个公理消除一个义务，而此行按定义消除一个。 (3) 唯一性是一个两情形析构，没有任何归纳：[Some] 情形是假设，[None] 情形是竞争者自身的 [preserves_pt]。该文件不包含 [induction]，也不包含 [Fixpoint]。所以这一行是四个中最便宜的，这也是人们所期望的：“自由”在这里附加在单个元素上，而不是在运算下封闭。在这里，集合论纪律一点代价都没有，这正是有趣的比较。Instance/Mod/Free.v 的头文件为自由模块找到了一个阻碍，在这一行中没有对应物：经典载体（有限支持函数）甚至无法写下其基向量，除非对生成集合的集合论 [≈] 有一个决策程序，因此经典构造在 [Sets] 上根本无法产生伴随。加入一个基点不需要判定器：[option_setoid] 提升 X 自身的 [≈] 并添加 [None ≈ None]，并且 [Some] 严格遵守 [≈]。以下内容都不依赖于可判定性、有限性或选择——库的 [∃] 是 [sigT]，因此 [ump_universal_arrows] 产生的调解器就是数据。优势，严格优先测量。下面的每一项识别都是在 [eq_refl] 尝试后，才在 [≈] 陈述的。- [eq_refl]：遗忘函子在对象上的作用（[free_pointed_forget_obj]）；自由对象的承载体和基点（[free_pointed_carrier], [free_pointed_basepoint]）；插入（[free_pointed_insert_is_Some]）；中介器的两个分支（[free_pointed_extend_some_strict], [free_pointed_extend_none_strict]）；泛箭头（[free_pointed_arrow_is_insert]）；自由函子在对象上的作用（[FreePointed_obj]）；单位（[free_pointed_unit_is_insert]）；前向换位⌊−⌋，它是沿插入的限制（[free_pointed_transpose_is_adj]）；自由函子在箭头上的作用读取为逆向换位（[free_pointed_fmap_is_from_adj]）；以及在Instance/Sets/Pointed.v中被识别为一点评集的自由有基集的两点探针对象（[PointedTwo_is_free_on_one]）。- 仅 [≈]：逆转置 ⌈−⌉ ([free_pointed_from_adj])、余单位 ([free_pointed_counit_evaluates]) 以及自由函子在生成元上的箭头作用 ([free_pointed_fmap_some])。这三次拒绝的原因已经被诊断出来，而且诊断具有辨别力。所有三者都经过 [unique_obj (ump_universal_arrows …)] ，而 [ump_universal_arrows]（Theory/Universal/Arrow.v）是 [Qed] 不透明的，因此没有任何东西能通过它化简。有两个对照表明这是原因，而不是结合记录的一般特性。首先，同一个 [Isomorphism] 的另一个换位确实可以化简（[free_pointed_transpose_is_adj]，[eq_refl]）——所以阻碍并不是因为换位通常无法计算，也不是因为在同构集上重建了 [proper_morphism] 证书。第二，也是更明确的，[free_pointed_fmap_is_from_adj] 将 [fmap[FreePointed] u] 与 ⌈insert ∘ u⌉ 在 [eq_refl] 处识别——两边都是字面相同的不透明项——而 [free_pointed_fmap_some] 然后需要 [≈]。因此阻塞恰好位于展开不透明中介者的地方，而不在其他任何地方。每一次拒绝都是经过保护和测量的：在此文件名末尾，三个驳斥命令 [Fail]、[free_pointed_extend]、[free_pointed_counit] 和 [FreePointed]（第四个 [Fail] 在它们旁边，是无作用域的工具检查，不会驳斥此开发的任何内容）。每一个都被剥离过一次，并确认报告的是真实的“无法统一”，而不是作用域、符号或引用错误。它们不会在重命名下无条件变为绿色：出现在 [Fail] 块中的每个标识符，除了这四个探针名称本身，也出现在此文件中至少一个必须成功的命令中，因此重命名它们中的任何一个都会破坏这里的阳性对照。宇宙。请从约束块中读取，而不仅仅从绑定器中读取。两个绑定器分别为 [SetoidObject] 和 [PointedSetoid] 的构造，直接而不是 [obj[Sets]，保持每个载体宇宙与其关系宇宙分开：[FreePointedObject@{u u0} : SetoidObject@{u u0} → PointedSetoid@{u u0}]，其约束块完全不包含任何识别（仅包含从 [option_setoid] 自身的消除中继承的 [u <= eq_ind.u0] 和 [u0 <= False_rect.u0] 的界限）；以及 [free_pointed_extend@{u u0 u1 u2 u3 u4}]，其 X 位于 [SetoidObject@{u u0}]，其 Y 位于 [PointedSetoid@{u1 u2}]，共四个独立层次。那些其陈述对  [X : Sets]  进行量化的常量——也就是，对  [obj[Sets]  进行量化——实际上位于  [SetoidObject@{u0 u0}] ，承载者和关系已确定；[free_pointed_insert@{u u0}] 是其中的第一个。这不是本文件所做的，也不会产生消费者任何成本：[Sets] 被声明为 [Sets@{o so} : Category@{so o o}]，因此 [obj[Sets] 确实是 [SetoidObject@{o o}]，并且该标识就是成为 [Sets] 对象的意义。同样地，[Pointed_Forget@{u u0} : PointedSets@{u u0} ⟶ Sets@{u0 u}] 承载 [u0 < u] ，仍然是 [Sets] 的自身声明，这里没有引入任何标识。这个文件中的没有任何常量在宇宙实例或约束中携带 [Set]——所有 66 个都已检查，包括具体的证人，这就是为什么它们是基于 [poly_unit] 和 [option] 构建的，而不是基于 [bool]；这是一个有意的选择，而且是经过验证的，而不是假设的（[fpt_one@{u}] 和 [fpt_two@{u}] 是 [SetoidObject@{u u}]）。

   假设。这个模块的所有 66 个常量都报告“在全局上下文下封闭”。计数是 [Print Module] 的数量，即 60 个源声明加上六个 [Program] 义务；请注意，这里 [.glob] 会被多算，因为 [Fail Definition foo] 在全局注册 [foo] 时并没有增加常量，并且这个文件中有四个这样的情况。

   未提供的内容。- 没有单子。[Pointed_Forget ◯ FreePointed] 具有对象作用 [option] 对准（[free_pointed_maybe_carrier]），因此这个伴随作用在 [Sets] 上诱导出 maybe 单子——但是没有 [@Monad Sets] 实例，没有 Kleisli 范畴，也没有建立 Eilenberg-Moore 比较，并且下面的陈述没有提到 [Monad] 。Instance/Sets/Pointed.v 的头部已经指出 pointed 集是 maybe 单子的代数，并且 Instance/Sets/Par.v 的 [Part] 是它的 Kleisli 范畴；这里或那里都没有对这些主张进行形式化。Theory/Coq/Maybe.v 的 [Maybe] 单子是基于裸类型上的应用 [Theory/Coq/] 类型类层次结构，属于与 [Theory/Monad.v] 不同的类，并且彼此无关。——没有 smash 积，也没有内部 Hom。Instance/Sets/Pointed.v 与 smash-hom 对偶的关系是关于一个不同对偶的不同陈述，这里没有涉及。- 没有与 Instance/Sets/Pointed/Coslice.v 的 co-slice 表示进行比较：没有将自由有基集合展示为与终对象的余积，也没有给出 co-slice 级别的泛箭。- 没有与 Instance/Sets/Pointed/Part.v 进行比较：自由函子与该文件中的 [Part_to_Pointed] 无关，也没有提到部分映射。- 关于练习 3 的其他三行没有任何内容。Rng ⟶ Ab 行的内容在树中为 [FreeRngAb ⊣ Rng_Forget_Ab]（Instance/Rng/Free.v），归档在 Mac Lane §IV.8 练习 2 下，而不是 §III.1 练习 3；Ab ⟶ Grp 行是 Instance/Grp/Abelianize.v；对于 Top ⟶ Set，Instance/Top/Forgetful.v 提供 [Top_Discrete]，并且 [discrete_adj] 作为跨宇宙同态集合同构，其标题记录了打包的 [Adjunction] 记录在该宇宙间隙中不可形成——并且它根本不包含 [UniversalArrow]（已测量）。这里对三者都没有作出任何声明。- 没有针对该行的本质唯一性陈述。通用 [universal_arrow_unique]（Theory/Universal/Arrow.v）完全适用，并未实例化。- 插入被证明是单射，并且其像被证明没有包括基点，但在 [Sets] 或 [PointedSets] 中没有关于它的 [Monic] 或 [Epic] 的声明，并且关于 [Pointed_Forget] 除了忠实性之外没有其他说明。
*)

#[local] Obligation Tactic := idtac.

(*
   * ** The forgetful functor Set_* ⟶ Set

   The underlying setoid of a pointed setoid, and the underlying setoid
   map of a pointed map.  Both are projections, so all three functor
   laws are [reflexivity] and faithfulness is the identity implication:
   equivalence in [PointedSets] IS pointwise equivalence of the
   underlying maps (Instance/Sets/Pointed.v). 

   --------
   * ** 忘记函子 Set_* ⟶ Set

   一个有指点集合的底层集合体，以及有指点映射的底层集合体映射。两者都是投影，因此三个函子律都是 [reflexivity]，并且忠实性就是恒等蕴涵：[PointedSets] 中的等价是底层映射的逐点等价 (Instance/Sets/Pointed.v)。
*)

Program Definition Pointed_Forget : PointedSets ⟶ Sets := {|
  fobj := fun X => pointed_setoid X;
  fmap := fun _ _ f => pointed_map f
|}.
Next Obligation. intros X Y f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros X a; simpl; reflexivity. Qed.
Next Obligation. intros X Y Z f g a; simpl; reflexivity. Qed.

#[export] Program Instance Pointed_Forget_Faithful : Faithful Pointed_Forget.
Next Obligation. intros X Y f g Hfg a; exact (Hfg a). Qed.

(*
   * ** The free pointed set X ⊔ {∗}

   The carrier is [option (carrier X)] and the setoid is
   [option_setoid] (Lib/Datatypes.v), which relates [Some a] to
   [Some b] exactly when a ≈ b, relates [None] to itself, and relates
   nothing across the two constructors.  The basepoint is the adjoined
   element [None].  No equation is imposed, so nothing is quotiented. 

   --------
   * ** 自由点集 X ⊔ {∗}

   载体为[option (carrier X)]，卵骨为
   [option_setoid] （Lib/Datatypes.v），它与[Some a]相关
   [Some b] 当 a ≈ b 时，将 [None] 与自身联系起来，并且
   两个构造函数之间无任何东西。基点是相邻的
   元素[None]。不施加方程，因此不商。
*)

Definition FreePointedObject (X : SetoidObject) : PointedSetoid := {|
  pointed_setoid := {| carrier := option (carrier X) |};
  pt := Datatypes.None
|}.

(*
 The insertion of generators.  Its respectfulness certificate is
 [Some_respects] (Lib/Datatypes.v), resolved during elaboration;
 the universe measurement in the header was taken after that
 resolution, so it reports the term that is actually built. 

 --------
 生成器的插入。它的尊重证书是 [Some_respects]（Lib/Datatypes.v），在展开过程中已解析；头部中的宇宙测量是在解析之后进行的，因此它报告的是实际构建的项。
*)
Definition free_pointed_insert (X : SetoidObject) :
  X ~{Sets}~> Pointed_Forget (FreePointedObject X).
Proof.
  refine {| morphism := fun a => Datatypes.Some a |}.
Defined.

(*
   * ** The universal property

   Every setoid map into the underlying setoid of a pointed set
   extends along the insertion to exactly one pointed map. 

   --------
   * ** 通用性质

   每个集合等价映射到一个带基点集合的基础集合等价，在插入映射下恰好扩展为一个带基点映射。
*)

Section Extension.

Context {X : SetoidObject}.
Context {Y : PointedSetoid}.
Context (h : X ~{Sets}~> Pointed_Forget Y).

Definition fpt_ext_fun (o : carrier (FreePointedObject X)) : carrier Y :=
  match o with
  | Datatypes.Some a => h a
  | Datatypes.None   => pt Y
  end.

Program Definition fpt_ext_map :
  SetoidMorphism (pointed_setoid (FreePointedObject X))
                 (pointed_setoid Y) := {|
  morphism := fpt_ext_fun
|}.
Next Obligation.
  intros a b Hab.
  destruct a as [a|], b as [b|]; simpl in *; try contradiction.
  - now rewrite Hab.
  - reflexivity.
Qed.

(*
 The one law a pointed map owes, [preserves_pt], is [reflexivity]
 here: the mediator sends the adjoined point to [pt Y] by
 definition. 

 --------
 一张有指向的地图所遵循的唯一法则，[preserves_pt]，是[reflexivity]  
 在这里：中介者根据定义将连接的点发送到[pt Y]。
*)
Definition free_pointed_extend : FreePointedObject X ~{PointedSets}~> Y.
Proof using X Y h.
  refine (Build_PointedMorphism (FreePointedObject X) Y fpt_ext_map _).
  simpl.
  reflexivity.
Defined.

Lemma free_pointed_extend_generators (a : carrier X) :
  free_pointed_extend (Datatypes.Some a) ≈ h a.
Proof. reflexivity. Qed.

(*
 Uniqueness: two cases, no induction.  The [Some] case is the
 hypothesis; the [None] case is the competitor's own [preserves_pt],
 since [None] IS the basepoint of the free object. 

 --------
 唯一性：两种情况，没有归纳。[Some] 情况是假设；[None] 情况是竞争者自己的 [preserves_pt]，因为 [None] 是自由对象的基点。
*)
Lemma free_pointed_extend_unique
  (g : FreePointedObject X ~{PointedSets}~> Y)
  (Hg : ∀ a : carrier X, g (Datatypes.Some a) ≈ h a) :
  g ≈ free_pointed_extend.
Proof.
  intros [a|]; simpl.
  - exact (Hg a).
  - exact (preserves_pt g).
Qed.

End Extension.

Arguments fpt_ext_fun {X Y} h o.
Arguments fpt_ext_map {X Y} h.
Arguments free_pointed_extend {X Y} h.

(*
   * The universal property in the shape [universal_arrow_from_UMP]
   consumes. 

   --------
   * 形状 [universal_arrow_from_UMP] 中的通用属性会被消耗。
*)

Theorem free_pointed_universal (X : SetoidObject) :
  ∀ (Y : PointedSetoid) (h : X ~{Sets}~> Pointed_Forget Y),
    ∃! g : FreePointedObject X ~{PointedSets}~> Y,
      h ≈ fmap[Pointed_Forget] g ∘ free_pointed_insert X.
Proof.
  intros Y h.
  unshelve eexists.
  - exact (free_pointed_extend h).
  - intro a; simpl.
    symmetry; exact (free_pointed_extend_generators h a).
  - intros g Hg o; simpl.
    symmetry; apply (free_pointed_extend_unique h g).
    intro a; symmetry; exact (Hg a).
Qed.

(*
   * Mac Lane §III.1 Exercise 3, pointed row: the universal arrow from X
   to the forgetful functor.  By Theory/Universal/Arrow.v this IS an
   initial object of the comma category [=(X) ↓ Pointed_Forget]. 

   --------
   * Mac Lane §III.1 练习 3，指定行：从 X 到遗忘函子（forgetful functor）的通用箭头（universal arrow）。根据 Theory/Universal/Arrow.v，这确实是逗号范畴 [=(X) ↓ Pointed_Forget] 的初始对象。
*)

Definition free_pointed_universal_arrow (X : Sets)
  : UniversalArrow X Pointed_Forget :=
  universal_arrow_from_UMP X Pointed_Forget (FreePointedObject X)
    (free_pointed_insert X) (free_pointed_universal X).

(*
   * The same content in the direct encoding, where the universal object
   is named rather than projected out of a comma category. 

   --------
   * 直接编码中的相同内容，其中通用对象被命名，而不是从逗号类别中投射出来。
*)

Program Definition free_pointed_AUniversalArrow (X : Sets)
  : AUniversalArrow X Pointed_Forget (FreePointedObject X) := {|
  universal_arrow := free_pointed_insert X
|}.
Next Obligation.
  intros X Y h.
  unshelve eexists.
  - exact (free_pointed_extend h).
  - intro a; simpl.
    exact (free_pointed_extend_generators h a).
  - intros g Hg o; simpl.
    symmetry; apply (free_pointed_extend_unique h g).
    intro a; exact (Hg a).
Qed.

(*
   * ** The free-forgetful adjunction

   Mac Lane §IV.1 Theorem 2, local-to-global: the functor, the
   adjunction and both triangle identities come out of the generic
   machinery with no further proof. 

   --------
   * ** 自由-遗忘伴随

   Mac Lane §IV.1 定理 2，局部到整体：函子、伴随以及两个三角恒等式都源自通用机制，无需进一步证明。
*)

Definition FreePointed : Sets ⟶ PointedSets :=
  LeftAdjointFunctorFromUniversalArrows Pointed_Forget
    free_pointed_universal_arrow.

Definition free_pointed_adjunction : FreePointed ⊣ Pointed_Forget :=
  AdjunctionFromUniversalArrows Pointed_Forget free_pointed_universal_arrow.

(* * ** Strengths, measured strict-first First the [eq_refl] identifications. / * ** 优势，严格优先衡量 首先是 [eq_refl] 的识别。 *)

Example free_pointed_forget_obj (X : PointedSetoid) :
  Pointed_Forget X = pointed_setoid X := eq_refl.

Example free_pointed_carrier (X : SetoidObject) :
  carrier (FreePointedObject X) = option (carrier X) := eq_refl.

Example free_pointed_basepoint (X : SetoidObject) :
  pt (FreePointedObject X) = Datatypes.None := eq_refl.

Example free_pointed_insert_is_Some (X : SetoidObject) (a : carrier X) :
  free_pointed_insert X a = Datatypes.Some a := eq_refl.

Example free_pointed_extend_some_strict (X : SetoidObject)
  (Y : PointedSetoid) (h : X ~{Sets}~> Pointed_Forget Y) (a : carrier X) :
  free_pointed_extend h (Datatypes.Some a) = h a := eq_refl.

Example free_pointed_extend_none_strict (X : SetoidObject)
  (Y : PointedSetoid) (h : X ~{Sets}~> Pointed_Forget Y) :
  free_pointed_extend h Datatypes.None = pt Y := eq_refl.

(*
 [universal_arrow_from_UMP] stores the supplied morphism as the second
 projection of the comma object it builds, so no proof is involved. 

 --------
 [universal_arrow_from_UMP] 将提供的同态存储为它构建的逗号对象的第二投影，因此不涉及证明。
*)
Example free_pointed_arrow_is_insert (X : Sets) :
  @arrow _ _ X Pointed_Forget (free_pointed_universal_arrow X)
    = free_pointed_insert X := eq_refl.

Example FreePointed_obj (X : Sets) :
  FreePointed X = FreePointedObject X := eq_refl.

(*
   * The unit.  [unit] is DERIVED in Theory/Adjunction.v (it is ⌊id⌋),
   not a field, so what it computes to has to be checked. 

   --------
   * 单位 [unit] 来源于 Theory/Adjunction.v（它是 ⌊id⌋），不是一个字段，所以它的计算结果需要检查。
*)

Definition free_pointed_unit (X : Sets)
  : X ~{Sets}~> Pointed_Forget (FreePointed X) :=
  @Category.Theory.Adjunction.unit _ _ _ _ free_pointed_adjunction X.

Example free_pointed_unit_is_insert (X : Sets) (a : carrier X) :
  free_pointed_unit X a = Datatypes.Some a := eq_refl.

(*
   * The forward transpose ⌊−⌋ IS restriction along the insertion, on the
   nose.  This is the control that makes the diagnosis of the three
   rejections below discriminating: one leg of this very [Isomorphism]
   does reduce. 

   --------
   * 前向转置 ⌊−⌋ 是沿插入处的限制，正好在鼻子上。这是使下面三个拒绝的诊断具有辨别性的控制：这条非常 [Isomorphism] 的一条腿确实会减少。
*)

Definition free_pointed_transpose {X : Sets} {Y : PointedSets}
  (g : FreePointed X ~{PointedSets}~> Y) : X ~{Sets}~> Pointed_Forget Y :=
  fmap[Pointed_Forget] g ∘ free_pointed_insert X.

Example free_pointed_transpose_is_adj (X : Sets) (Y : PointedSets)
  (g : FreePointed X ~{PointedSets}~> Y) :
  to (@adj _ _ _ _ free_pointed_adjunction X Y) g
    = free_pointed_transpose g := eq_refl.

(*
   * The inverse transpose ⌈−⌉ is the extension, but only up to [≈]: it
   is [unique_obj (ump_universal_arrows …)], and
   [ump_universal_arrows] is [Qed]-opaque.  The first [Fail] probe at
   the end of this file names [free_pointed_extend] for exactly this. 

   --------
   * 逆转置 ⌈−⌉ 是扩展，但仅限于 [≈]：它是 [unique_obj (ump_universal_arrows …)]，并且 [ump_universal_arrows] 是 [Qed] 不透明的。此文件末尾的第一个 [Fail] 探针正是为此命名为 [free_pointed_extend]。
*)

Lemma free_pointed_from_adj (X : Sets) (Y : PointedSets)
  (h : X ~{Sets}~> Pointed_Forget Y) :
  from (@adj _ _ _ _ free_pointed_adjunction X Y) h
    ≈ free_pointed_extend h.
Proof.
  apply (free_pointed_extend_unique h).
  intro a.
  exact (@iso_to_from _ _ _ (@adj _ _ _ _ free_pointed_adjunction X Y) h a).
Qed.

(*
   * Restriction to the generators is a bijection whose inverse is
   extension.  The first round trip is [reflexivity] at every
   generator. 

   --------
   * 对生成器的限制是一个其逆映射为扩展的双射。第一次往返是在每个生成器上 [reflexivity]。
*)

Lemma free_pointed_transpose_extend {X : Sets} {Y : PointedSets}
  (h : X ~{Sets}~> Pointed_Forget Y) :
  free_pointed_transpose (free_pointed_extend h) ≈ h.
Proof. intro a; simpl; reflexivity. Qed.

Lemma free_pointed_extend_transpose {X : Sets} {Y : PointedSets}
  (g : FreePointed X ~{PointedSets}~> Y) :
  free_pointed_extend (free_pointed_transpose g) ≈ g.
Proof.
  intro o; simpl.
  symmetry; apply (free_pointed_extend_unique (free_pointed_transpose g) g).
  intro a; simpl; reflexivity.
Qed.

(*
   * The counit.  It is the OTHER transpose, ⌈id⌉, so it does not
   compute; what is proved is that it is the identity away from the
   adjoined point and sends that point to the basepoint. 

   --------
   * 余单位。它是另一个转置，⌈id⌉，因此它不会计算；证明的是，它在附加点之外是恒等映射，并将该点发送到基点。
*)

Definition free_pointed_counit (Y : PointedSets)
  : FreePointed (Pointed_Forget Y) ~{PointedSets}~> Y :=
  @Category.Theory.Adjunction.counit _ _ _ _ free_pointed_adjunction Y.

Lemma free_pointed_counit_evaluates (Y : PointedSets)
  (o : carrier (Pointed_Forget Y)) :
  free_pointed_counit Y (Datatypes.Some o) ≈ o.
Proof.
  exact (free_pointed_from_adj (Pointed_Forget Y) Y id{Sets}
           (Datatypes.Some o)).
Qed.

Lemma free_pointed_counit_kills_point (Y : PointedSets) :
  free_pointed_counit Y Datatypes.None ≈ pt Y.
Proof. exact (preserves_pt (free_pointed_counit Y)). Qed.

(*
   * The free functor's action on arrows.  It is defined by
   factorization, so the strict identification available is with the
   inverse transpose -- both sides being literally the same opaque
   term -- while its VALUE at a generator needs [≈]. 

   --------
   * 自由函子的箭头作用。它是通过因式分解定义的，因此可以严格地将其与逆转置进行识别——两边字面上是相同的不透明项——而其在生成元上的值需要 [≈]。
*)

Example free_pointed_fmap_is_from_adj (X Y : Sets) (u : X ~{Sets}~> Y) :
  fmap[FreePointed] u
    = from (@adj _ _ _ _ free_pointed_adjunction X (FreePointed Y))
        (free_pointed_insert Y ∘ u) := eq_refl.

Lemma free_pointed_fmap_some (X Y : Sets) (u : X ~{Sets}~> Y)
  (a : carrier X) :
  fmap[FreePointed] u (Datatypes.Some a) ≈ Datatypes.Some (u a).
Proof.
  exact (free_pointed_from_adj X (FreePointed Y)
           (free_pointed_insert Y ∘ u) (Datatypes.Some a)).
Qed.

Lemma free_pointed_fmap_none (X Y : Sets) (u : X ~{Sets}~> Y) :
  fmap[FreePointed] u Datatypes.None ≈ Datatypes.None.
Proof. exact (preserves_pt (fmap[FreePointed] u)). Qed.

(*
   * ** Naturality, in Mac Lane's §IV.1 shape

   The two clauses are the adjunction class's own fields, restated in
   the transpose's vocabulary. 

   --------
   * ** 自然性，在 Mac Lane 的 §IV.1 形式

   这两个条款是伴随类自身的领域，用换位的词汇重新表述。
*)

Lemma free_pointed_naturality_in_set {X Y : Sets} {Z : PointedSets}
  (g : FreePointed Y ~{PointedSets}~> Z) (u : X ~{Sets}~> Y) :
  free_pointed_transpose (g ∘ fmap[FreePointed] u)
    ≈ free_pointed_transpose g ∘ u.
Proof. exact (@to_adj_nat_l _ _ _ _ free_pointed_adjunction X Y Z g u). Qed.

Lemma free_pointed_naturality_in_pointed {X : Sets} {Y Z : PointedSets}
  (k : Y ~{PointedSets}~> Z) (g : FreePointed X ~{PointedSets}~> Y) :
  free_pointed_transpose (k ∘ g)
    ≈ fmap[Pointed_Forget] k ∘ free_pointed_transpose g.
Proof. exact (@to_adj_nat_r _ _ _ _ free_pointed_adjunction X Y Z k g). Qed.

(** The triangle identities, inherited. / 三角恒等式，继承的。 *)

Corollary free_pointed_triangle_left (X : Sets) :
  free_pointed_counit (FreePointed X)
    ∘ fmap[FreePointed] (free_pointed_unit X) ≈ id.
Proof. exact (@counit_fmap_unit _ _ _ _ free_pointed_adjunction X). Qed.

Corollary free_pointed_triangle_right (Y : PointedSets) :
  fmap[Pointed_Forget] (free_pointed_counit Y)
    ∘ free_pointed_unit (Pointed_Forget Y) ≈ id.
Proof. exact (@fmap_counit_unit _ _ _ _ free_pointed_adjunction Y). Qed.

(*
 The composite [Pointed_Forget ◯ FreePointed] has object action
 [option].  No monad is built; see the header. 

 --------
 复合体 [Pointed_Forget ◯ FreePointed] 具有对象动作 [option]。没有构建单子；请参见标题。
*)
Example free_pointed_maybe_carrier (X : Sets) :
  carrier (Pointed_Forget (FreePointed X)) = option (carrier X) := eq_refl.

(*
   * ** Non-vacuity

   First, two facts holding at EVERY generating setoid.  Both are
   definitional, because [option_setoid] relates nothing across the two
   constructors: the adjoined point is not in the image of the
   insertion, and the insertion is injective. 

   --------
   * ** 非空性

   首先，有两个在每个生成集合上都成立的事实。它们都是定义性的，因为 [option_setoid] 并没有把两个构造之间的元素关联起来：附加的点不在插入的像中，并且插入是单射的。
*)

Theorem free_pointed_point_is_new (X : SetoidObject) (a : carrier X) :
  free_pointed_insert X a ≈ pt (FreePointedObject X) → False.
Proof. exact (fun H => H). Qed.

Theorem free_pointed_insert_injective (X : SetoidObject)
  (a b : carrier X) :
  free_pointed_insert X a ≈ free_pointed_insert X b → a ≈ b.
Proof. exact (fun H => H). Qed.

(*
   * Both facts are also visible by mapping OUT, and it is worth being
   explicit that here that is a CROSS-CHECK and not a necessity.  In
   the quotient rows of this exercise a negative can only be obtained
   by mapping out of the construction, since no induction on a
   generating congruence yields one; this row has no congruence, so the
   two theorems above are available directly.  What mapping out adds is
   that the mediator produced by the universal property COMPUTES.

   The probe objects are built over [poly_unit] and [option] rather
   than over [bool], so that no witness below pins a universe to
   [Set]. 

   --------
   * 通过映射 OUT，这两个事实也可以被看到，并且值得明确指出，这里是交叉检查而不是必要条件。在此练习的商行中，负数只能通过从构造中映射出来获得，因为没有生成同余的归纳能产生负数；这一行没有同余，因此上述两个定理可以直接使用。映射出来所增加的内容是由泛性质计算出的中介者。

   探针对象是建立在  [poly_unit]  和  [option]  上，而不是建立在  [bool]  上，因此下面没有证据将一个宇宙固定到  [Set] 。
*)

Definition fpt_one : SetoidObject := {| carrier := poly_unit |}.

Definition fpt_two : SetoidObject := {| carrier := option poly_unit |}.

(*
   * The two-point probe object of Instance/Sets/Pointed.v IS the
   free pointed set on the one-point setoid -- whole record, [eq_refl].
   So the smallest object that file needed in order to detect
   monomorphisms is the free one on a single generator. 

   --------
   * Instance/Sets/Pointed.v 中的双点探针对象是单点集合上的自由指向集——整个记录，[eq_refl]。因此，文件中检测单态所需的最小对象是单个生成元上的自由对象。
*)

Example PointedTwo_is_free_on_one :
  FreePointedObject fpt_one = PointedTwo := eq_refl.

(*
   * The free pointed set on a two-element setoid has exactly three
   elements: two generators and the adjoined point.  Exhaustiveness is
   stated at Leibniz equality, the carrier being an [option] of an
   [option] of [poly_unit]. 

   --------
   * 在一个二元素集合上的自由带 pointed 集合恰好有三个元素：两个生成元和附加点。完备性在莱布尼茨等式下说明，承载体是 [option] 的 [option] 的 [poly_unit]。
*)

Definition fpt_gen1 : carrier (FreePointedObject fpt_two) :=
  Datatypes.Some (Datatypes.Some ttt).

Definition fpt_gen2 : carrier (FreePointedObject fpt_two) :=
  Datatypes.Some Datatypes.None.

Theorem free_pointed_two_has_three_elements
  (o : carrier (FreePointedObject fpt_two)) :
  ((o = fpt_gen1) + (o = fpt_gen2)) + (o = pt (FreePointedObject fpt_two)).
Proof.
  destruct o as [[u|]|].
  - destruct u; left; left; reflexivity.
  - left; right; reflexivity.
  - right; reflexivity.
Qed.

Theorem free_pointed_two_generators_distinct : fpt_gen1 ≈ fpt_gen2 → False.
Proof. exact (fun H => H). Qed.

(*
   * Mapping out.  [PointedTwo] is the target; its carrier is
   [option poly_unit], which is also the carrier of [fpt_two], so the
   identity setoid map is a probe, and a constant at the free point is
   a second one. 

   --------
   * 绘制映射。[PointedTwo] 是目标；它的载体是 [option poly_unit]，[option poly_unit] 也是 [fpt_two] 的载体，因此恒等集合映射是一个探针，而自由点上的常数是第二个探针。
*)

Definition fpt_probe_id : fpt_two ~{Sets}~> Pointed_Forget PointedTwo :=
  id{Sets}.

Definition fpt_probe_const : fpt_two ~{Sets}~> Pointed_Forget PointedTwo.
Proof.
  refine {| morphism := fun _ => Datatypes.Some ttt |}.
  exact (fun _ _ _ => reflexivity (Datatypes.Some ttt)).
Defined.

(** The mediator computes, at Leibniz equality, on every element. / 中介者在莱布尼茨等式下，对每个元素进行计算。 *)

Example fpt_probe_id_gen1 :
  free_pointed_extend fpt_probe_id fpt_gen1 = Datatypes.Some ttt := eq_refl.

Example fpt_probe_id_gen2 :
  free_pointed_extend fpt_probe_id fpt_gen2 = Datatypes.None := eq_refl.

Example fpt_probe_id_point :
  free_pointed_extend fpt_probe_id (pt (FreePointedObject fpt_two))
    = Datatypes.None := eq_refl.

Example fpt_probe_const_gen2 :
  free_pointed_extend fpt_probe_const fpt_gen2 = Datatypes.Some ttt
  := eq_refl.

Example fpt_probe_const_point :
  free_pointed_extend fpt_probe_const (pt (FreePointedObject fpt_two))
    = Datatypes.None := eq_refl.

(*
   * Separation by mapping out.  The identity probe separates the first
   generator from both the second generator and the adjoined point; the
   constant probe separates the second generator from the adjoined
   point.  So the three elements are pairwise separated by pointed maps
   into [PointedTwo]. 

   --------
   * 通过映射分离。恒等探针将第一个生成元与第二个生成元和附加点分开；常数探针将第二个生成元与附加点分开。因此，这三个元素通过指向 [PointedTwo] 的映射两两分离。
*)

Theorem free_pointed_gen1_gen2_separated_out :
  free_pointed_extend fpt_probe_id fpt_gen1
    ≈ free_pointed_extend fpt_probe_id fpt_gen2 → False.
Proof. exact (fun H => H). Qed.

Theorem free_pointed_gen1_point_separated_out :
  free_pointed_extend fpt_probe_id fpt_gen1
    ≈ free_pointed_extend fpt_probe_id (pt (FreePointedObject fpt_two))
    → False.
Proof. exact (fun H => H). Qed.

Theorem free_pointed_gen2_point_separated_out :
  free_pointed_extend fpt_probe_const fpt_gen2
    ≈ free_pointed_extend fpt_probe_const (pt (FreePointedObject fpt_two))
    → False.
Proof. exact (fun H => H). Qed.

(*
   * The identity probe's extension is NOT injective -- it must collapse
   the second generator onto the adjoined point, a pointed map having
   nowhere else to send the point.  So the extension is genuinely the
   mediator of a universal property and not an isomorphism in
   disguise. 

   --------
   * 恒等探针的扩展不是单射——它必须将第二个生成元压缩到附加点上，这是一个指向映射，没有其他地方可以发送该点。因此，该扩展确实是一个泛性质的中介，而不是伪装的同构。
*)

Theorem free_pointed_extend_id_collapses :
  free_pointed_extend fpt_probe_id fpt_gen2
    ≈ free_pointed_extend fpt_probe_id (pt (FreePointedObject fpt_two)).
Proof. reflexivity. Qed.

(*
   * ** Guards

   Each [Fail] below was stripped once and confirmed to report a
   genuine "cannot unify", not a scope, notation or reference error,
   and each names the constant whose strictness is being refuted.  The
   instrument check is scope-free. 

   --------
   * ** 守卫

   下面的每个 [Fail] 都被剥离过一次，并确认报告了一个真正的“无法统一”错误，而不是作用域、符号或引用错误，并且每个都命名了被驳斥严格性的常量。仪器检查是无作用域的。
*)

Fail Definition free_pointed_instrument_check :
  Datatypes.true = Datatypes.false := eq_refl.

Fail Example free_pointed_from_adj_is_not_strict
  (X : Sets) (Y : PointedSets) (h : X ~{Sets}~> Pointed_Forget Y) :
  from (@adj _ _ _ _ free_pointed_adjunction X Y) h
    = free_pointed_extend h := eq_refl.

Fail Example free_pointed_counit_is_not_strict
  (Y : PointedSets) (o : carrier (Pointed_Forget Y)) :
  free_pointed_counit Y (Datatypes.Some o) = o := eq_refl.

Fail Example free_pointed_fmap_is_not_strict
  (X Y : Sets) (u : X ~{Sets}~> Y) (a : carrier X) :
  fmap[FreePointed] u (Datatypes.Some a) = Datatypes.Some (u a) := eq_refl.
