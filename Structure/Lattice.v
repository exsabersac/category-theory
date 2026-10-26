Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Monoid.

Generalizable All Variables.

(* * * Lattice objects in a cartesian category / * * 笛卡尔范畴中的格对象 *)

(*
 Mac Lane, Categories for the Working Mathematician, 2nd ed., Section
 III.6, p. 75 (maclane:III.6:remark1); nLab:
 https://ncatlab.org/nlab/show/lattice
 https://ncatlab.org/nlab/show/internalization

 Section III.6 gives monoid and group objects by commuting diagrams and
 then observes that the same device internalizes ANY algebraic system
 presented by finitary operations and equational laws, naming rings and
 lattices as the next examples.  This file is the lattice half;
 Structure/Ring.v is the ring half, and its header carries the shared
 discussion of internalization and of the Lawvere-theory reading
 (Theory/Lawvere.v, Theory/Lawvere/Model.v's [Model] and [Models]) --
 which is a POINTER in both files and not a theorem: no bridge such as
 [MonoidObject ~= Models(Th_Mon)] is proved, and no Lawvere theory of
 lattices is constructed.

 A lattice needs the same two ambient ingredients a ring does.
 Absorption uses one variable twice, so the ambient category must copy;
 the units bottom and top are morphisms out of the terminal object, so it
 must discard.  Hence [Cartesian] + [Terminal], as in Structure/Group.v
 and Structure/Ring.v, rather than a bare [Monoidal].

 SCOPE OF THE NAME, and a forward reference this file OWNS.  Three open
 issues claim Structure/Lattice.v -- #340 (this one, Mac Lane III.6),
 #389 (Mac Lane IV.6: powerset lattices and Boolean algebras are
 cartesian closed) and #1003 (Riehl 5.5: lattices and semilattices as
 categories over Set).  Instance/Proset/Limit.v records that
 claim explicitly and DELIBERATELY RESERVES the vocabulary: it “defines
 no [Meet], [Join], [Lattice] or [BooleanAlgebra] class and creates no
 such module”, its [IsGLB] and [IsLUB] being “family-level PREDICATES
 over a bare [PreOrder], not an algebraic structure”.  As the
 lowest-numbered issue, #340 defines the vocabulary; that reservation is
 cited here rather than restated.  But read the handover precisely: the
 note goes on to call its four constructors ([Proset_Cartesian],
 [Proset_Cocartesian], [Proset_Terminal], [Proset_Initial]) “exactly the
 interface such a class would later consume”, and THIS FILE DOES NOT
 CONSUME THEM.  The classes below are internal-algebraic -- an object of
 an arbitrary cartesian category carrying two operations -- not
 order-theoretic, and the bridge between the two readings (a lattice
 object in [Sets] is a poset with all binary meets and joins) is listed
 below as not delivered.  A later effort wanting the order-theoretic
 reading will still have to build it.

 NAMING.  [InternalLattice] and [InternalSemilattice] follow
 Structure/Ring.v's [InternalRing] / [InternalSemiring]; that file
 explains why the [*Object] convention of [MonoidObject] and
 [GroupObject] could not be used (Theory/Algebra/Rig.v already takes
 [RingObject] for the set-level notion).  All four names are free
 tree-wide, as are [SetoidLattice], [Sets_Monoid_on] and the witness
 names below.

 PRIOR ART.  Nothing in the tree carries two monoid structures on one
 object AS [Monoid]-TYPED FIELDS -- and that qualifier is the whole
 claim, an earlier revision having billed this as a search “by shape
 rather than by name” when it is a sweep by the field type's NAME.  By
 SHAPE the pattern DOES occur: Theory/Algebra/Rig.v's [RigObject]
 carries [(rig_zero, rig_add)] and [(rig_one, rig_mul)] on one setoid
 carrier, elementwise rather than as internal monoid objects.
 [GroupObject] (Structure/Group.v)
 is the only record anywhere with a [MonoidObject] field, and the only
 records with a field of the sibling class [Monoid] of
 Theory/Algebra/Monoid.v are Theory/Algebra/CommutativeMonoid.v and
 Theory/Algebra/Frobenius.v, each carrying exactly one -- the latter
 pairs its monoid with a COMONOID, which is a different variance and
 carries no absorption.  (This file's [Monoid] is Structure/Monoid.v's
 [@MonoidObject C CC_Monoidal], not the identically named class of
 Theory/Algebra/Monoid.v.)  The only absorption-like
 law in tree is the zero-morphism absorption of
 Structure/Kernel/Universal.v's [ZeroMorphisms], which is about zero
 morphisms and not about two binary operations.  Existing meet/join
 vocabulary is order-theoretic and unrelated to this file's classes:
 Instance/Proset/Limit.v's [IsGLB]/[IsLUB]/[HasAllMeets]/[HasAllJoins],
 Instance/Proset/Order.v's [tmeet]/[tjoin] for total orders, and
 Instance/Two/Monoidal.v's [two_meet] on the walking arrow's objects.
 (Instance/FinSet.v's [fin_join] and
 Instance/Ab/DirectedColimit.v's [fg_join] are a coproduct decoder
 and a subgroup join; neither is lattice vocabulary.)

 WHAT IS DELIVERED, and at what strength.

 (1) [InternalSemilattice x]: a [Monoid] on x that is commutative and
 idempotent.  Idempotence is a FIELD here and must be:
 [bool_xor_not_idempotent] exhibits a commutative monoid object in
 [Sets] -- exclusive-or on the two-element setoid -- that refutes
 it, so it does not follow from the monoid laws plus commutativity.

 (2) [InternalLattice x]: a join [Monoid] and a meet [Monoid] on x, both
 commutative, plus the two absorption laws.  This is the BOUNDED
 lattice: the two monoid units are the bottom and top elements.
 Idempotence is NOT a field.

 (3) Idempotence of both operations is DERIVED from absorption alone
 ([lattice_join_idem], [lattice_meet_idem]) -- neither proof uses a
 unit, a unitor or commutativity, only the two absorption laws and
 the fork calculus.  Each half is then packaged as an
 [InternalSemilattice] ([InternalLattice_join_Semilattice],
 [InternalLattice_meet_Semilattice]).

 (4) The bounds annihilate: [lattice_bot_meet] (bottom meet a is bottom)
 and [lattice_top_join] (top join a is top), each from absorption
 plus the OTHER operation's unit law.  This is the exact parallel of
 Structure/Ring.v's derived [ring_annihilate_l]/[ring_annihilate_r],
 and the parallel is the point: in both files annihilation is a
 theorem rather than an axiom, and in both files the extra structure
 that makes it derivable (additive inverses there, absorption here)
 is what does the work.

 (5) The [Sets] instances.  [SetoidLattice] is the set-level bounded
 lattice on a setoid carrier -- declared HERE, which is off-pattern
 (set-level algebra normally lives under Theory/Algebra/, as
 Theory/Algebra/Rig.v does), because this effort may create only two
 files; a later move is a rename away.  [Sets_InternalLattice] and
 [SetoidLattice_of_InternalLattice] are the two passages.  Round
 trips are measured STRICT-FIRST: all five DATA fields return by
 [eq_refl] ([lat_round_setoid], [lat_round_bot], [lat_round_join],
 [lat_round_top], [lat_round_meet]) while the WHOLE RECORD does not,
 pinned as a [Fail]; on the internal side the unit and the operation
 agree at [eq_refl] on VALUES ([ilattice_round_bot],
 [ilattice_round_join]) while the [Monoid] record does not, also
 pinned.  Both [Fail]s were stripped and confirmed to be genuine
 CONVERSION failures (“cannot unify”).  [SetoidLattice] also
 records idempotence as a corollary of absorption
 ([sl_join_idem], [sl_meet_idem]), mirroring (3) at the set level.

 ENGINEERING FINDING, shared with Structure/Ring.v and repeated because
 it shapes every statement below.  At [CC_Monoidal] the tensor IS the
 product -- [bimap f g = split f g] and [to unit_left = exr] hold by
 [eq_refl], recorded as the two [Example]s opening the file -- but
 [mappend]'s type is [mon (x) mon ~> mon], i.e.
 [fobj tensor (mon, mon) ~> mon], only CONVERTIBLE with [mon x mon].  Two
 separately elaborated occurrences of [mappend[M] o swap] then record
 different object arguments in their [compose] nodes and [rewrite]
 cannot match one against the other.  Every [mappend] and [mempty] below
 is therefore ascribed, [(mappend[M] : x x x ~> x)] and
 [(mempty[M] : 1 ~> x)], which forces a single syntactic form.
 [Sets_Monoid_on] is the same helper Structure/Ring.v calls
 [Sets_Monoid]; it is duplicated rather than imported so that neither
 Section III.6 file depends on the other, and the name is kept distinct
 so that importing both files is unambiguous.  [bool_setoid_obj] below
 is a SECOND, undeclared duplication of the same kind: it re-declares
 the two-element setoid this file already imports as
 Instance/Sets.v's [bool_setoid_object], with which it agrees by
 [eq_refl].  It is kept only so the witness block reads self-contained,
 and it is recorded here rather than left for a reader to discover.

 UNIVERSES, measured in the constraint blocks AND in the binders.
 [InternalSemilattice@{u u0 u1}] and [InternalLattice@{u u0 u1}] are over
 [Category@{u u0 u0}]: hom and proof universes IDENTIFIED, OBJECT
 universe FREE (it occurs only in [<=] bounds).  The identification is
 the DONORS' doing and THREE force it INDEPENDENTLY -- with the levels
 declared apart under [Constraint uh < up] a control naming a hom at
 those levels is accepted while each of [@Cartesian C], [@Terminal C]
 and [@Monoidal C] is rejected with “Cannot enforce up = uh”.
 [MonoidObject] is NOT a fourth donor: [@Monoidal C] appears in its own
 signature and is rejected first, so it cannot be probed apart, and
 whether it identifies anything OF ITS OWN is UNKNOWN.
 Nothing here adds to it and it is NOT claimed unavoidable.  The derived
 results inherit exactly that and add nothing:
 [lattice_join_idem@{u u0 u1}] and [lattice_bot_meet@{u u0 u1}] have the
 same block as the class.  On the [Sets] side [Sets_InternalLattice] and
 [SetoidLattice_of_InternalLattice] carry [o < so] as their only STRICT
 constraint and no [Set] anywhere; the rest of each block is some
 fifteen [<=] bounds against donor universes ([projections],
 [prod_rect], [Basics.compose], [eq_ind]), some relating two DECLARED
 binders, so “nothing else” would be wrong even read charitably.  The
 [Set]-freedom holds only because the universe binders are written
 out; unannotated, [Sets_Monoid_on] minimizes to
 [SetoidObject@{Set Set}], which would have confined every [Sets] result
 to Set-sized carriers.  Same minimization hazard as
 Instance/Sets/Products.v and the #300 erratum.

 NON-VACUITY, proved rather than gestured at.  [Bool_Lattice] is the
 two-element bounded lattice (disjunction with bottom [false],
 conjunction with top [true]) and [Bool_ILattice] its image in [Sets];
 bottom, top, join and meet all COMPUTE by [eq_refl], and
 [bool_lattice_nondegenerate] proves bottom and top distinct, so the
 structure is not collapsed.  [Bool_Semilattice] instantiates
 [InternalSemilattice].  That the laws genuinely CONSTRAIN is proved
 twice: [bool_join_not_absorbing] takes the join monoid of that very
 lattice as BOTH halves -- two commutative monoid objects on one carrier
 ([bool_join_comm]) -- and refutes absorption, so the absorption fields are
 not automatic; and [bool_xor_not_idempotent] refutes idempotence for the
 commutative monoid object [Bool_Xor_Monoid], which is why (1) carries it
 as a field.

 WHAT IS NOT DELIVERED.
 - No unbounded lattice.  [InternalLattice] is bounded because it is
 built from two [Monoid] objects, and the tree has no semigroup-object
 notion to build the unit-free variant on; none is introduced here.
 CORRECTION (#470): the tree has one now, Theory/Algebra/
 Semigroup.v's [Semigroup], internal semigroups in a monoidal
 category, the sibling of Theory/Algebra/Monoid.v's [Monoid] rather
 than of Structure/Monoid.v's [MonoidObject]; the unit-free variant
 is still not built.
 - No distributive lattices, no complements, no Heyting or Boolean
 algebras, and no cartesian-closed structure on a lattice: that is
 #389's Mac Lane Section IV.6 item, and nothing here anticipates it.
 - No order-theoretic reading.  The relation “a <= b iff a meet b = a” is
 not defined, no partial order is extracted, and
 Instance/Proset/Limit.v's [IsGLB]/[IsLUB]/[Proset_Cartesian] are NOT
 consumed -- so the bridge between this algebraic vocabulary and that
 order-theoretic one remains open, as does #1003's reading of
 lattices as categories.
 - No category of internal lattices, no lattice homomorphisms, no
 forgetful functor, and hence no equivalence packaging the [Sets]
 round trips.
 - No instance in any ambient category other than [Sets].  In particular
 no powerset lattice (Instance/Sets/Powerset.v is not required) and no
 lattice of opens from Instance/Top.v, so “the opens of a space form a
 lattice object” stays prose.
 - No closure results: products and exponentials of lattice objects are
 not shown to be lattice objects (Structure/Monoid.v proves the monoid
 analogues [Product_Monoid] and [Hom_Monoid]; neither is lifted).
 - No duality: that a lattice object in C is one in C read with meet and
 join exchanged is not stated, and neither is the self-duality of the
 axioms.
 - No modularity, no Birkhoff-style representation, no completeness. 

 --------
 Mac Lane，《为工作数学家准备的范畴论》，第二版，第III.6节，第75页（maclane:III.6:remark1）；nLab: https://ncatlab.org/nlab/show/lattice https://ncatlab.org/nlab/show/internalization

 第III.6节通过交换图给出了幺半群和群对象，然后指出同样的手段可以内化由有限操作和方程定律呈现的任何代数系统，并以环和格作为接下来的示例。这个文件是格的一半；Structure/Ring.v 是环的一半，其头部包含了关于内化和Lawvere理论释义的共享讨论（Theory/Lawvere.v，Theory/Lawvere/Model.v 的 [Model] 和 [Models]）——在这两个文件中都是一个指针而不是定理：没有证明诸如 [MonoidObject ~= Models(Th_Mon)] 这样的桥梁，也没有构建格的Lawvere理论。一个格需要和环相同的两种环境成分。
 吸收使用了一个变量两次，所以环境范畴必须能够复制；
 单位的底和顶是从终对象出发的态射，因此它必须能够丢弃。因此是 [Cartesian] + [Terminal]，就像在 Structure/Group.v 和 Structure/Ring.v 中一样，而不是单独的 [Monoidal]。名称的范围，以及该文件拥有的前向引用。三个未解决的问题涉及 Structure/Lattice.v —— #340（这个，Mac Lane III.6）、#389（Mac Lane IV.6：幂集格与布尔代数是笛卡尔闭的）和 #1003（Riehl 5.5：作为 Set 上的范畴的格和半格）。Instance/Proset/Limit.v 明确记录了这一声明，并故意保留了该词汇：它“没有定义 [Meet]、[Join]、[Lattice] 或 [BooleanAlgebra] 类，也没有创建这样的模块”，其 [IsGLB] 和 [IsLUB] 是“在裸 [PreOrder] 上的族级谓词，而不是代数结构”。作为编号最低的问题，#340 定义了该词汇；这里引用了该保留声明，而不是重新陈述。但请仔细阅读交接说明：该说明接着称其四个构造函数（[Proset_Cartesian]、[Proset_Cocartesian]、[Proset_Terminal]、[Proset_Initial]）是“正是这样一个类后来会使用的接口”，而且本文件并未使用它们。下面的类是内部代数类——一个任意笛卡尔范畴的对象，带有两个运算——而不是序理论的，而两种解释之间的桥梁（[Sets] 中的格对象是具有所有二元交与并的偏序集）在下文列为未提供。随后希望进行序理论解释的工作仍然需要自行构建它。命名。[InternalLattice] 和 [InternalSemilattice] 遵循 Structure/Ring.v 的 [InternalRing] / [InternalSemiring]；该文件解释了为什么 [*Object] 约定不能用于 [MonoidObject] 和 [GroupObject]（Theory/Algebra/Rig.v 已经将 [RingObject] 用于集合层次的概念）。所有四个名称在整个树中都是空闲的，[SetoidLattice]、[Sets_Monoid_on] 以及下面的见证名称也是如此。先前技术。在该树中，没有任何内容在一个对象上承载两个幺半群结构 AS [Monoid] -类型字段--，而这个限定符就是整个权利要求，早期的修订将其称为按“形状而非名称”进行搜索，但实际上这是按字段类型的名称进行扫描。按形状，该模式确实存在：Theory/Algebra/Rig.v 的 [RigObject] 在一个集合载体上承载了 [(rig_zero, rig_add)] 和 [(rig_one, rig_mul)]，是逐元素的而非作为内部幺半群对象。[GroupObject] (Structure/Group.v) 是唯一一个包含 [MonoidObject] 字段的记录，并且 Theory/Algebra/Monoid.v 的兄弟类 [Monoid] 唯一包含该字段的记录是 Theory/Algebra/CommutativeMonoid.v 和 Theory/Algebra/Frobenius.v，每个记录正好携带一个 —— 后者将它的幺半群与 COMONOID 配对，后者具有不同的方差并且不包含吸收律。（此文件的 [Monoid] 是 Structure/Monoid.v 的 [@MonoidObject C CC_Monoidal]，而不是 Theory/Algebra/Monoid.v 中同名的类。）树中唯一类似吸收律的规律是 Structure/Kernel/Universal.v 的 [ZeroMorphisms] 的零态射吸收律，它关于零态射，而不是两个二元运算。现有的 meet/join 词汇是序理论的，与此文件的类无关：
 Instance/Proset/Limit.v 的 [IsGLB] / [IsLUB] / [HasAllMeets] / [HasAllJoins]，
 Instance/Proset/Order.v 的 [tmeet] / [tjoin] 用于全序，以及
 Instance/Two/Monoidal.v 的 [two_meet] 用于行箭头的对象。（Instance/FinSet.v 的 [fin_join] 和
 Instance/Ab/DirectedColimit.v 的 [fg_join] 是积和解码器
 以及子群 join；都不是格词汇。）

 交付了什么，以及强度如何。

 (1) [InternalSemilattice x]：在 x 上的 [Monoid]，它是可交换的并且
 幂等。幂等在这里是一个 FIELD 并且必须是：
 [bool_xor_not_idempotent] 展示了 [Sets] 中的一个交换幺半群对象——在二元等价集上的异或——反驳了它，
 因此它不能从幺半群定律加上可交换性推导出。(2)  [InternalLattice x]：在 x 上的一个并  [Monoid] 和一个交  [Monoid]，两者都是交换的，加上两个吸收律。这就是有界格：两个幺元分别是最小元素和最大元素。幂等性不是域。

 (3) 两个运算的幂等性完全是从吸收律推导出来的（[lattice_join_idem]，[lattice_meet_idem]）——没有任何证明使用幺元、单位元或交换律，仅使用两个吸收律和分叉演算。每一半随后被打包为一个 [InternalSemilattice]（[InternalLattice_join_Semilattice]，[InternalLattice_meet_Semilattice]）。(4) 边界湮灭：[lattice_bot_meet]（底部与 a 相交是底部）和 [lattice_top_join]（顶部与 a 合并是顶部），每一个都来自吸收律加上另一个运算的单位律。这正好对应于 Structure/Ring.v 中推导出的 [ring_annihilate_l] / [ring_annihilate_r]，并且这种对应的关键在于：在两个文件中，湮灭是一个定理而非公理，并且在两个文件中，使其可推导出的额外结构（那里是加法逆元，这里是吸收律）正是起作用的部分。(5) [Sets] 实例。[SetoidLattice] 是一个集合代数载体上的集合级有界格——在此处声明，这与常规模式不同（集合级代数通常位于 Theory/Algebra/ 下，如 Theory/Algebra/Rig.v 所示），因为此操作可能只创建两个文件；后续移动只需重命名即可。[Sets_InternalLattice] 和 [SetoidLattice_of_InternalLattice] 是两个段落。往返操作按严格优先顺序进行测量：五个 DATA 字段都由 [eq_refl]（[lat_round_setoid]、[lat_round_bot]、[lat_round_join]、[lat_round_top]、[lat_round_meet]）返回，而整个记录则不返回，固定为 [Fail]；在内部，单位和运算在 VALUES（[ilattice_round_bot]、[ilattice_round_join]）上的 [eq_refl] 上一致，而 [Monoid] 记录则不一致，也被固定。两个 [Fail] 已被剥离并确认是真正的转换失败（“无法统一”）。[SetoidLattice] 还将幂等性记录为吸收律的推论（[sl_join_idem]，[sl_meet_idem]），在集合层面上反映了(3)的情况。工程发现，与 Structure/Ring.v 共享，并重复，因为它塑造了下面的每个陈述。在 [CC_Monoidal] 处，张量就是乘积——[bimap f g = split f g] 和 [to unit_left = exr] 由 [eq_refl] 保持，记录为打开文件的两个 [Example] ——但 [mappend] 的类型是 [mon (x) mon ~> mon]，即 [fobj tensor (mon, mon) ~> mon]，只能与 [mon x mon] 进行转换。[mappend[M] 的两个单独展开的［o swap］出现记录了它们在 [compose] 节点中的不同对象参数，而 [rewrite] 无法互相匹配。因此，下面的每个 [mappend] 和 [mempty] 都被归于 [(mappend[M] ：x x x ~> x)] 和 [(mempty[M] ：1 ~> x)]，这强制了单一的句法形式。[Sets_Monoid_on] 是与 Structure/Ring.v 调用的 [Sets_Monoid] 相同的辅助结构；它是复制的而不是导入的，这样第三部分第6节的文件就不依赖于彼此，并且名称保持不同，这样导入两个文件时不会产生歧义。下面的 [bool_setoid_obj] 是第二个未声明的相同类型的重复：它重新声明了本文件已经导入的两元素集合（setoid），即 Instance/Sets.v 中的 [bool_setoid_object]，并且通过 [eq_refl] 与其一致。它之所以保留下来，仅是为了使证人（witness）块显得自成一体，并且它被记录在此，而不是留给读者去发现。宇宙，按约束块和绑定器来衡量。[InternalSemilattice@{u u0 u1}] 和 [InternalLattice@{u u0 u1}] 超过 [Category@{u u0 u0}]：同态和证明宇宙已被识别，对象宇宙是自由的（它仅出现在 [<=] 的约束中）。这种识别是捐赠者所为，并且三个独立地强制它——在 [Constraint uh < up] 下声明的各级作为控制，可以命名这些级别的同态，而每个 [@Cartesian C]、[@Terminal C] 和 [@Monoidal C] 都被拒绝，提示“无法强制 up = uh”。[MonoidObject] 不是第四个捐赠者：[@Monoidal C] 出现在它自己的签名中，并且首先被拒绝，因此无法单独探测，并且是否识别任何它自己的东西是未知的。这里没有任何内容对它有额外贡献，也不声称它是不可避免的。派生结果完全继承这一点而没有增加任何内容：
 [lattice_join_idem@{u u0 u1}] 和 [lattice_bot_meet@{u u0 u1}] 拥有与类相同的区块。在 [Sets] 方面，[Sets_InternalLattice] 和 [SetoidLattice_of_InternalLattice] 仅以 [o < so] 作为它们唯一的严格约束，并且在任何地方都没有 [Set]；每个区块的其余部分是大约十五个针对供体宇宙的 [<=] 上界（[projections]、[prod_rect]、[Basics.compose]、[eq_ind]），其中一些关系到两个已声明的绑定器，因此即使宽容地理解，“别的什么都没有”也是错误的。[Set] 自由性之所以成立，仅仅是因为宇宙绑定器被显式写出；如果没有注解，[Sets_Monoid_on] 会最小化为 [SetoidObject@{Set Set}]，这会将每个 [Sets] 结果限制在集合大小的承载体中。与 Instance/Sets/Products.v 和 #300 勘误中的最小化风险相同。非空性，已被证明而非仅仅示意。[Bool_Lattice] 是一个双元素有界格（底元素为 [false] 的析取，上元素为 [true] 的合取），而 [Bool_ILattice] 是它在 [Sets] 中的像；底元素、上元素、并和交都是由 [eq_refl] 计算的，并且 [bool_lattice_nondegenerate] 证明了底元素和上元素是不同的，因此该结构没有崩溃。[Bool_Semilattice] 实例化了 [InternalSemilattice]。规律确实施加约束这一点已被证明两次：[bool_join_not_absorbing] 将该格的并单子作为两半——在同一载体上的两个交换单子对象（[bool_join_comm]）——并反驳了吸收律，因此吸收场不是自动的；而 [bool_xor_not_idempotent] 反驳了交换单子对象 [Bool_Xor_Monoid] 的幂等性，这就是为什么（1）将其作为一个字段。未提供的内容。- 没有无界格。[InternalLattice] 是有界的，因为它是由两个 [Monoid] 对象构建的，而且该树没有半群对象的概念来构建无单位变体；这里没有引入任何内容。更正（#470）：现在该树有一个，即 Theory/Algebra/Semigroup.v 的 [Semigroup]，在一个幺半范畴中的内部半群，是 Theory/Algebra/Monoid.v 的 [Monoid] 的同级，而不是 Structure/Monoid.v 的 [MonoidObject]；无单位变体仍未构建。- 没有分配格，没有补集，没有海廷代数或布尔代数，也没有格上的笛卡尔闭结构：这是 #389 中 Mac Lane 第 IV.6 节的条目，这里没有涉及。- 没有顺序理论上的解读。关系“a <= b 当且仅当 a meet b = a”未定义，未提取任何偏序，并且 Instance/Proset/Limit.v 的 [IsGLB] / [IsLUB] / [Proset_Cartesian] 未被使用——因此这个代数词汇与该序理论词汇之间的桥梁仍然开放，#1003 中将格视为范畴的解读也是如此。- 没有内部格的范畴，没有格同态，也没有遗忘函子，因此无法封装 [Sets] 的等价往返。- 在除 [Sets] 之外的任何环境范畴中没有实例。特别地，没有幂集格（Instance/Sets/Powerset.v 未被要求）也没有来自 Instance/Top.v 的开的格，因此“空间的开集构成一个格对象”仍然只能用文字表述。- 没有封闭性结果：格对象的乘积和指数没有被证明是格对象（Structure/Monoid.v 证明了单子类比 [Product_Monoid] 和 [Hom_Monoid]；两者都未被提升）。
 - 没有对偶性：没有说明 C 中的格对象在交换交与并后仍是 C 中的对象，也没有说明公理是自对偶的。
 - 没有模性、没有 Birkhoff 风格的表示、没有完备性。
*)

Section Internalize.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

Example lat_bimap_is_split {x y z w : C} (f : x ~> y) (g : z ~> w) :
  @bimap C C C (@tensor C CC_Monoidal) _ _ _ _ f g = split f g := eq_refl.

Example lat_unit_left_is_exr {x : C} :
  to (@unit_left C CC_Monoidal x) = exr := eq_refl.

Class InternalSemilattice (x : C) := {
  isl_mon : Monoid x;

  isl_comm : (mappend[isl_mon] : x × x ~> x) ∘ swap ≈ mappend[isl_mon];
  isl_idem : (mappend[isl_mon] : x × x ~> x) ∘ (id △ id) ≈ id
}.

Class InternalLattice (x : C) := {
  il_join : Monoid x;
  il_meet : Monoid x;

  il_join_comm : (mappend[il_join] : x × x ~> x) ∘ swap ≈ mappend[il_join];
  il_meet_comm : (mappend[il_meet] : x × x ~> x) ∘ swap ≈ mappend[il_meet];

  il_absorb_meet :
    (mappend[il_meet] : x × x ~> x)
      ∘ (exl △ (mappend[il_join] : x × x ~> x)) ≈ exl;
  il_absorb_join :
    (mappend[il_join] : x × x ~> x)
      ∘ (exl △ (mappend[il_meet] : x × x ~> x)) ≈ exl
}.

End Internalize.

Section LatticeDerived.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context {x : C}.
Context `{L : @InternalLattice C _ _ x}.

Lemma lattice_join_idem :
  (mappend[il_join] : x × x ~> x) ∘ (id △ id) ≈ id.
Proof.
  assert (HI : (mappend[il_meet] : x × x ~> x)
                 ∘ (id △ ((mappend[il_join] : x × x ~> x) ∘ (id △ id)))
               ≈ id).
  { transitivity ((mappend[il_meet] : x × x ~> x)
                    ∘ (exl △ (mappend[il_join] : x × x ~> x))
                    ∘ (id △ id)).
    { rewrite <- comp_assoc, <- fork_comp.
      now rewrite exl_fork. }
    rewrite il_absorb_meet.
    now rewrite exl_fork. }
  transitivity ((mappend[il_join] : x × x ~> x)
                  ∘ (exl △ (mappend[il_meet] : x × x ~> x))
                  ∘ (id △ ((mappend[il_join] : x × x ~> x) ∘ (id △ id)))).
  { rewrite <- comp_assoc, <- fork_comp, exl_fork.
    now rewrite HI. }
  rewrite il_absorb_join.
  now rewrite exl_fork.
Qed.

Lemma lattice_meet_idem :
  (mappend[il_meet] : x × x ~> x) ∘ (id △ id) ≈ id.
Proof.
  assert (HI : (mappend[il_join] : x × x ~> x)
                 ∘ (id △ ((mappend[il_meet] : x × x ~> x) ∘ (id △ id)))
               ≈ id).
  { transitivity ((mappend[il_join] : x × x ~> x)
                    ∘ (exl △ (mappend[il_meet] : x × x ~> x))
                    ∘ (id △ id)).
    { rewrite <- comp_assoc, <- fork_comp.
      now rewrite exl_fork. }
    rewrite il_absorb_join.
    now rewrite exl_fork. }
  transitivity ((mappend[il_meet] : x × x ~> x)
                  ∘ (exl △ (mappend[il_join] : x × x ~> x))
                  ∘ (id △ ((mappend[il_meet] : x × x ~> x) ∘ (id △ id)))).
  { rewrite <- comp_assoc, <- fork_comp, exl_fork.
    now rewrite HI. }
  rewrite il_absorb_meet.
  now rewrite exl_fork.
Qed.

Lemma lattice_join_bot_left {w : C} (g : w ~> x) :
  (mappend[il_join] : x × x ~> x)
      ∘ (((mempty[il_join] : 1 ~> x) ∘ one[w]) △ g) ≈ g.
Proof.
  assert (Hu : (mappend[il_join] : x × x ~> x)
                 ∘ split (mempty[il_join] : 1 ~> x) id ≈ exr)
    by exact (@mempty_left _ _ _ il_join).
  transitivity ((mappend[il_join] : x × x ~> x)
                  ∘ split (mempty[il_join] : 1 ~> x) id ∘ (one[w] △ g)).
  { rewrite <- comp_assoc, split_fork.
    now rewrite id_left. }
  rewrite Hu.
  now rewrite exr_fork.
Qed.

Lemma lattice_meet_top_left {w : C} (g : w ~> x) :
  (mappend[il_meet] : x × x ~> x)
      ∘ (((mempty[il_meet] : 1 ~> x) ∘ one[w]) △ g) ≈ g.
Proof.
  assert (Hu : (mappend[il_meet] : x × x ~> x)
                 ∘ split (mempty[il_meet] : 1 ~> x) id ≈ exr)
    by exact (@mempty_left _ _ _ il_meet).
  transitivity ((mappend[il_meet] : x × x ~> x)
                  ∘ split (mempty[il_meet] : 1 ~> x) id ∘ (one[w] △ g)).
  { rewrite <- comp_assoc, split_fork.
    now rewrite id_left. }
  rewrite Hu.
  now rewrite exr_fork.
Qed.

(* The bottom element annihilates the meet: it is NOT a field, but a consequence of absorption together with the join unit law. / 底元素消去交：它不是一个域，而是吸收律与并单位律的一个结果。 *)
Lemma lattice_bot_meet :
  (mappend[il_meet] : x × x ~> x)
      ∘ (((mempty[il_join] : 1 ~> x) ∘ one) △ id)
    ≈ (mempty[il_join] : 1 ~> x) ∘ one.
Proof.
  transitivity ((mappend[il_join] : x × x ~> x)
                  ∘ ((((mempty[il_join] : 1 ~> x) ∘ one[x]))
                       △ ((mappend[il_meet] : x × x ~> x)
                            ∘ ((((mempty[il_join] : 1 ~> x) ∘ one[x]))
                                 △ id)))).
  { now rewrite lattice_join_bot_left. }
  transitivity ((mappend[il_join] : x × x ~> x)
                  ∘ (exl △ (mappend[il_meet] : x × x ~> x))
                  ∘ ((((mempty[il_join] : 1 ~> x) ∘ one[x])) △ id)).
  { rewrite <- comp_assoc, <- fork_comp.
    now rewrite exl_fork. }
  rewrite il_absorb_join.
  now rewrite exl_fork.
Qed.

(* Dually, the top element annihilates the join. / 对偶地，顶元素使并消失。 *)
Lemma lattice_top_join :
  (mappend[il_join] : x × x ~> x)
      ∘ (((mempty[il_meet] : 1 ~> x) ∘ one) △ id)
    ≈ (mempty[il_meet] : 1 ~> x) ∘ one.
Proof.
  transitivity ((mappend[il_meet] : x × x ~> x)
                  ∘ ((((mempty[il_meet] : 1 ~> x) ∘ one[x]))
                       △ ((mappend[il_join] : x × x ~> x)
                            ∘ ((((mempty[il_meet] : 1 ~> x) ∘ one[x]))
                                 △ id)))).
  { now rewrite lattice_meet_top_left. }
  transitivity ((mappend[il_meet] : x × x ~> x)
                  ∘ (exl △ (mappend[il_join] : x × x ~> x))
                  ∘ ((((mempty[il_meet] : 1 ~> x) ∘ one[x])) △ id)).
  { rewrite <- comp_assoc, <- fork_comp.
    now rewrite exl_fork. }
  rewrite il_absorb_meet.
  now rewrite exl_fork.
Qed.

Program Definition InternalLattice_join_Semilattice :
  @InternalSemilattice C _ _ x := {| isl_mon := il_join |}.
Next Obligation. exact il_join_comm. Qed.
Next Obligation. exact lattice_join_idem. Qed.

Program Definition InternalLattice_meet_Semilattice :
  @InternalSemilattice C _ _ x := {| isl_mon := il_meet |}.
Next Obligation. exact il_meet_comm. Qed.
Next Obligation. exact lattice_meet_idem. Qed.

End LatticeDerived.

Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.

(* * ** Bounded lattices on a setoid carrier / * ** 在集合载体上的有界格 *)

Record SetoidLattice := {
  sl_setoid :> SetoidObject;

  sl_bot  : carrier sl_setoid;
  sl_join : carrier sl_setoid → carrier sl_setoid → carrier sl_setoid;
  sl_top  : carrier sl_setoid;
  sl_meet : carrier sl_setoid → carrier sl_setoid → carrier sl_setoid;

  sl_join_respects : Proper (equiv ==> equiv ==> equiv) sl_join;
  sl_meet_respects : Proper (equiv ==> equiv ==> equiv) sl_meet;

  sl_join_assoc : ∀ a b c,
    sl_join (sl_join a b) c ≈ sl_join a (sl_join b c);
  sl_join_comm : ∀ a b, sl_join a b ≈ sl_join b a;
  sl_join_bot_l : ∀ a, sl_join sl_bot a ≈ a;

  sl_meet_assoc : ∀ a b c,
    sl_meet (sl_meet a b) c ≈ sl_meet a (sl_meet b c);
  sl_meet_comm : ∀ a b, sl_meet a b ≈ sl_meet b a;
  sl_meet_top_l : ∀ a, sl_meet sl_top a ≈ a;

  sl_absorb_meet : ∀ a b, sl_meet a (sl_join a b) ≈ a;
  sl_absorb_join : ∀ a b, sl_join a (sl_meet a b) ≈ a
}.

#[export] Existing Instance sl_join_respects.
#[export] Existing Instance sl_meet_respects.

Corollary sl_join_bot_r (L : SetoidLattice) (a : carrier (sl_setoid L)) :
  sl_join L a (sl_bot L) ≈ a.
Proof. rewrite sl_join_comm; apply sl_join_bot_l. Qed.

Corollary sl_meet_top_r (L : SetoidLattice) (a : carrier (sl_setoid L)) :
  sl_meet L a (sl_top L) ≈ a.
Proof. rewrite sl_meet_comm; apply sl_meet_top_l. Qed.

(* Idempotence is derived from the two absorption laws alone -- the set-level shadow of [lattice_join_idem] / [lattice_meet_idem]. / 幂等性仅来源于两个吸收律—— [lattice_join_idem] / [lattice_meet_idem] 的集合级影子。 *)
Corollary sl_join_idem (L : SetoidLattice) (a : carrier (sl_setoid L)) :
  sl_join L a a ≈ a.
Proof.
  rewrite <- (sl_absorb_meet L a (sl_join L a a)) at 2.
  now rewrite sl_absorb_join.
Qed.

Corollary sl_meet_idem (L : SetoidLattice) (a : carrier (sl_setoid L)) :
  sl_meet L a a ≈ a.
Proof.
  rewrite <- (sl_absorb_join L a (sl_meet L a a)) at 2.
  now rewrite sl_absorb_meet.
Qed.

Section SetsInternal.

(*
 The same helper Structure/Ring.v names [Sets_Monoid].  It is duplicated
 rather than imported so that neither Section III.6 file depends on the
 other, and the name is kept distinct so that importing both is
 unambiguous. 

 --------
 相同的辅助 Structure/Ring.v 命名为 [Sets_Monoid]。它是复制而不是导入的，因此两个第 III.6 节的文件互不依赖，并且名称保持不同，以便同时导入两者时不会产生歧义。
*)
Program Definition Sets_Monoid_on@{o so p} (A : SetoidObject@{o o})
  (u : carrier A) (op : carrier A → carrier A → carrier A)
  (opP : Proper@{o p} (equiv ==> equiv ==> equiv) op)
  (op_assoc : ∀ a b c, op (op a b) c ≈ op a (op b c))
  (unit_l : ∀ a, op u a ≈ a)
  (unit_r : ∀ a, op a u ≈ a) : @Monoid Sets@{o so} _ _ A := {|
  mempty := {| morphism := fun _ => u |};
  mappend := {| morphism := fun p => op (fst p) (snd p) |}
|}.
Next Obligation. proper; simpl in *; now apply opP. Qed.

Program Definition Sets_InternalLattice@{o so q} (L : SetoidLattice@{o o q}) :
  @InternalLattice Sets@{o so} _ _ (sl_setoid L) := {|
  il_join := Sets_Monoid_on (sl_setoid L) (sl_bot L) (sl_join L)
               (sl_join_respects L) (sl_join_assoc L) (sl_join_bot_l L)
               (sl_join_bot_r L);
  il_meet := Sets_Monoid_on (sl_setoid L) (sl_top L) (sl_meet L)
               (sl_meet_respects L) (sl_meet_assoc L) (sl_meet_top_l L)
               (sl_meet_top_r L)
|}.
Next Obligation. now rewrite sl_join_comm. Qed.
Next Obligation. now rewrite sl_meet_comm. Qed.
Next Obligation. now rewrite sl_absorb_meet. Qed.
Next Obligation. now rewrite sl_absorb_join. Qed.

Program Definition SetoidLattice_of_InternalLattice@{o so}
  {A : SetoidObject@{o o}} (L : @InternalLattice Sets@{o so} _ _ A) :
  SetoidLattice@{o o o} := {|
  sl_setoid := A;
  sl_bot  := (mempty[il_join] : _ ~{Sets}~> _) ttt;
  sl_join := fun a b => (mappend[il_join] : _ ~{Sets}~> _) (a, b);
  sl_top  := (mempty[il_meet] : _ ~{Sets}~> _) ttt;
  sl_meet := fun a b => (mappend[il_meet] : _ ~{Sets}~> _) (a, b)
|}.
Next Obligation. proper; apply proper_morphism; simpl; split; assumption. Qed.
Next Obligation. proper; apply proper_morphism; simpl; split; assumption. Qed.
Next Obligation.
  exact (@mappend_assoc _ _ _ (@il_join _ _ _ _ L) ((a, b), c)).
Qed.
Next Obligation. exact (@il_join_comm _ _ _ _ L (b, a)). Qed.
Next Obligation. exact (@mempty_left _ _ _ (@il_join _ _ _ _ L) (ttt, a)). Qed.
Next Obligation.
  exact (@mappend_assoc _ _ _ (@il_meet _ _ _ _ L) ((a, b), c)).
Qed.
Next Obligation. exact (@il_meet_comm _ _ _ _ L (b, a)). Qed.
Next Obligation. exact (@mempty_left _ _ _ (@il_meet _ _ _ _ L) (ttt, a)). Qed.
Next Obligation. exact (@il_absorb_meet _ _ _ _ L (a, b)). Qed.
Next Obligation. exact (@il_absorb_join _ _ _ _ L (a, b)). Qed.

End SetsInternal.

Section SetsRoundTrip.

Context (L : SetoidLattice).

Example lat_round_setoid :
  sl_setoid (SetoidLattice_of_InternalLattice (Sets_InternalLattice L))
    = sl_setoid L := eq_refl.
Example lat_round_bot :
  sl_bot (SetoidLattice_of_InternalLattice (Sets_InternalLattice L))
    = sl_bot L := eq_refl.
Example lat_round_join :
  sl_join (SetoidLattice_of_InternalLattice (Sets_InternalLattice L))
    = sl_join L := eq_refl.
Example lat_round_top :
  sl_top (SetoidLattice_of_InternalLattice (Sets_InternalLattice L))
    = sl_top L := eq_refl.
Example lat_round_meet :
  sl_meet (SetoidLattice_of_InternalLattice (Sets_InternalLattice L))
    = sl_meet L := eq_refl.

Fail Example lat_round_record :
  (SetoidLattice_of_InternalLattice (Sets_InternalLattice L)) = L := eq_refl.

Context {A : SetoidObject}.
Context (K : @InternalLattice Sets _ _ A).

Example ilattice_round_join (a b : carrier A) :
  (mappend[@il_join _ _ _ _
     (Sets_InternalLattice (SetoidLattice_of_InternalLattice K))]
     : _ ~{Sets}~> _) (a, b)
  = (mappend[@il_join _ _ _ _ K] : _ ~{Sets}~> _) (a, b) := eq_refl.

Example ilattice_round_bot :
  (mempty[@il_join _ _ _ _
     (Sets_InternalLattice (SetoidLattice_of_InternalLattice K))]
     : _ ~{Sets}~> _) ttt
  = (mempty[@il_join _ _ _ _ K] : _ ~{Sets}~> _) ttt := eq_refl.

Fail Example ilattice_round_monoid :
  (@il_join _ _ _ _
     (Sets_InternalLattice (SetoidLattice_of_InternalLattice K)))
    = (@il_join _ _ _ _ K) := eq_refl.

End SetsRoundTrip.

Section BoolWitness.

Definition bool_setoid_obj : SetoidObject := {|
  carrier := bool;
  is_setoid := {| equiv := @eq bool; setoid_equiv := eq_equivalence |}
|}.

#[local] Ltac bool_crush :=
  repeat intro; simpl in *;
  repeat match goal with [ b : bool |- _ ] => destruct b end;
  simpl in *; congruence.

Program Definition Bool_Lattice : SetoidLattice := {|
  sl_setoid := bool_setoid_obj;
  sl_bot  := false;
  sl_join := orb;
  sl_top  := true;
  sl_meet := andb
|}.
Next Obligation. bool_crush. Qed.
Next Obligation. bool_crush. Qed.
Next Obligation. bool_crush. Qed.
Next Obligation. bool_crush. Qed.
Next Obligation. bool_crush. Qed.
Next Obligation. bool_crush. Qed.

Definition Bool_ILattice : @InternalLattice Sets _ _ bool_setoid_obj :=
  Sets_InternalLattice Bool_Lattice.

Example bool_bot_computes :
  (mempty[@il_join _ _ _ _ Bool_ILattice] : _ ~{Sets}~> _) ttt = false
  := eq_refl.
Example bool_top_computes :
  (mempty[@il_meet _ _ _ _ Bool_ILattice] : _ ~{Sets}~> _) ttt = true
  := eq_refl.
Example bool_join_computes :
  (mappend[@il_join _ _ _ _ Bool_ILattice] : _ ~{Sets}~> _) (false, true)
    = true := eq_refl.
Example bool_meet_computes :
  (mappend[@il_meet _ _ _ _ Bool_ILattice] : _ ~{Sets}~> _) (false, true)
    = false := eq_refl.

Lemma bool_lattice_nondegenerate :
  (mempty[@il_join _ _ _ _ Bool_ILattice] : _ ~{Sets}~> _) ttt
    <> (mempty[@il_meet _ _ _ _ Bool_ILattice] : _ ~{Sets}~> _) ttt.
Proof. discriminate. Qed.

Definition Bool_Semilattice : @InternalSemilattice Sets _ _ bool_setoid_obj :=
  @InternalLattice_join_Semilattice Sets _ _ _ Bool_ILattice.

End BoolWitness.

Section LawsConstrain.

#[local] Ltac bool_crush :=
  repeat intro; simpl in *;
  repeat match goal with [ b : bool |- _ ] => destruct b end;
  simpl in *; congruence.

Definition Bool_Join_Monoid : @Monoid Sets _ _ bool_setoid_obj :=
  @il_join _ _ _ _ Bool_ILattice.

Lemma bool_join_comm :
  (mappend[Bool_Join_Monoid] : _ × _ ~{Sets}~> _) ∘ swap
    ≈ mappend[Bool_Join_Monoid].
Proof. exact (@il_join_comm _ _ _ _ Bool_ILattice). Qed.

Lemma bool_join_not_absorbing :
  ((mappend[Bool_Join_Monoid] : _ × _ ~{Sets}~> _)
      ∘ (exl △ (mappend[Bool_Join_Monoid] : _ × _ ~{Sets}~> _)) ≈ exl) → False.
Proof. intro Hx; specialize (Hx (false, true)); discriminate. Qed.

Program Definition Bool_Xor_Monoid : @Monoid Sets _ _ bool_setoid_obj :=
  Sets_Monoid_on bool_setoid_obj false xorb _ _ _ _.
Next Obligation. bool_crush. Qed.
Next Obligation. bool_crush. Qed.

Lemma bool_xor_comm :
  (mappend[Bool_Xor_Monoid] : _ × _ ~{Sets}~> _) ∘ swap
    ≈ mappend[Bool_Xor_Monoid].
Proof. intros [[|] [|]]; reflexivity. Qed.

Lemma bool_xor_not_idempotent :
  ((mappend[Bool_Xor_Monoid] : _ × _ ~{Sets}~> _) ∘ (id △ id) ≈ id) → False.
Proof. intro Hx; specialize (Hx true); discriminate. Qed.

End LawsConstrain.
