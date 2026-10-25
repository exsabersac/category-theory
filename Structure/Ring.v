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
Require Import Category.Structure.Group.

Generalizable All Variables.

(* * * Ring and semiring objects in a cartesian category / * * 笛卡尔范畴中的环与半环对象 *)

(*
 Mac Lane, Categories for the Working Mathematician, 2nd ed., Section
 III.6, p. 75 (maclane:III.6:remark1); nLab:
 https://ncatlab.org/nlab/show/ring+object
 https://ncatlab.org/nlab/show/internalization

 Mac Lane's Section III.6 defines monoid and group objects by commuting
 diagrams and then observes that the same device applies to ANY
 algebraic system given by finitary operations and equational laws --
 naming rings and lattices as the next examples.  This file carries out
 the ring half; Structure/Lattice.v carries out the lattice half.

 What "internalization" buys is that one definition, read in different
 ambient categories, is many classical theories at once: a ring object
 in Set is an ordinary ring, in Top a topological ring, in the category
 of schemes a ring scheme, in sheaves a sheaf of rings.  The ambient
 category must supply enough structure to STATE the axioms, and for
 rings that is more than a monoidal product: distributivity uses one
 variable twice (a copy), and annihilation drops a variable (a
 discard).  A cartesian category with a terminal object supplies both,
 which is why this file is developed over [Cartesian] + [Terminal]
 rather than over a bare [Monoidal] -- the same reason Structure/Group.v
 asks for [CartesianMonoidal] where Structure/Monoid.v asks for nothing.

 NAMING.  [RingObject] is ALREADY TAKEN: Theory/Algebra/Rig.v
 declares a record of that name for the SET-LEVEL notion (a ring on a
 setoid carrier), and Theory/Algebra/Rig.v likewise takes
 [RigObject].  Both are in scope here, since the [Sets] section below
 compares against them, so the names could not be reused.  The tree
 already carries four distinct "monoid" notions under four names --
 [MonoidObject] (Structure/Monoid.v, internal), [MonObject]
 (Construction/Deloop.v, a bare setoid monoid), [Monoid]
 (Theory/Algebra/Monoid.v, internal in a monoidal category) and
 [Monoid] (Theory/Coq/Monoid.v, over [Coq]) -- and the disambiguation
 there runs "full spelling = internal, abbreviation = set-level"
 ([GroupObject] vs [GrpObject]).  Rig.v inverts that convention, so it
 cannot be followed; the classes here are therefore [InternalSemiring]
 and [InternalRing], with the [Internal] prefix stating exactly what
 distinguishes them.  Both names are free tree-wide, as are
 [InternalLattice] and [InternalSemilattice] in the sibling file.

 PRIOR ART.  No in-tree class carries two monoid structures on one
 object AS [Monoid]-TYPED FIELDS -- and that qualifier is the whole
 claim, an earlier revision having billed this as a search "by shape
 rather than by name" when it is a sweep by the field type's NAME.  By
 SHAPE the pattern DOES occur, and in the very file named below: sweeping
 for record bodies with two [_assoc] axioms returns
 Theory/Algebra/Rig.v's [RigObject], which carries [(rig_zero,
 rig_add)] and [(rig_one, rig_mul)] on one setoid carrier -- elementwise
 rather than as internal monoid objects, and it is precisely the
 set-level theory this file internalizes.  [GroupObject]
 (Structure/Group.v)
 is the only record anywhere with a [MonoidObject] field, and the only
 records with a field of the sibling class [Monoid] of
 Theory/Algebra/Monoid.v are Theory/Algebra/CommutativeMonoid.v and
 Theory/Algebra/Frobenius.v -- each carrying exactly one.  (Note
 that this file's [Monoid] is Structure/Monoid.v's
 [@MonoidObject C CC_Monoidal], not Theory/Algebra/Monoid.v's
 identically named class; only the former is required here.)  The
 closest
 structural analogues are Theory/Algebra/Frobenius.v's [Frobenius] and
 Theory/Algebra/SpecialCommutativeFrobenius.v, which put a monoid and a
 COMONOID on one object -- different variance, and no distributivity.
 The tree's only distributivity is Structure/Distributive.v's
 [Distributive] and Structure/BiCCC.v, which distribute the ambient x
 over the ambient +; that is a property of the AMBIENT category, not two
 operations carried by an object.  Structure/Preadditive.v and
 Structure/Semiadditive.v enrich HOM-SETS in commutative monoids, and
 Theory/Algebra/Rig.v's [EndRig] reads a set-level rig off an
 endomorphism hom of a preadditive category -- adjacent, but a rig on a
 hom-set rather than on an object.  Theory/Algebra/Rig.v itself is the
 set-level theory this file internalizes.

 RELATION TO LAWVERE THEORIES.  Mac Lane's remark is the informal
 version of functorial semantics: an algebraic theory presented by
 finitary operations and equations is a category with finite products,
 and its models in C are the finite-product-preserving functors into C.
 The tree has that machinery -- Theory/Lawvere.v's [LawvereTheory],
 Theory/Lawvere/Model.v's [Model] record (functor + [CartesianFunctor] +
 [TerminalFunctor] witnesses) and the category [Models] built there as a
 full subcategory of the functor category.  The present classes are the
 hand-written instances of that pattern at the theories of semirings and
 rings.  NOT DELIVERED: no bridge theorem is proved -- neither
 [MonoidObject ~= Models(Th_Mon)] nor its ring analogue -- and no
 Lawvere theory of rings is constructed here.  The connection is
 recorded as a pointer, deliberately.

 WHAT IS DELIVERED, and at what strength.

 (1) [InternalSemiring r]: an additive [Monoid] on r that is
 commutative, a multiplicative [Monoid] on r, two distributivity
 laws and two annihilation laws.  This is Seven Sketches Definition
 5.36 / Theory/Algebra/Rig.v's [RigObject] clause for clause,
 internalized; multiplication is NOT assumed commutative.

 (2) [InternalRing r]: additive [Monoid] + commutativity + a negation
 [ir_neg] with the LEFT inverse law only, multiplicative [Monoid],
 and the two distributivity laws.  Annihilation is NOT a field.

 (3) The two annihilation laws are THEOREMS for a ring
 ([ring_annihilate_l], [ring_annihilate_r]), so
 [InternalRing_InternalSemiring] is a genuine derivation and not a
 repackaging.  The engine is [ring_cancel_idem]: an arrow k into r
 with k = k + k is the zero arrow.  That is the usual cancellation
 argument carried out on morphisms -- no elements anywhere -- and it
 spends the additive associativity, the additive unit law and the
 inverse law once each (the inverse law through an intermediate step
 that is then reused twice).  The right inverse law is derived
 ([ring_neg_right]), from commutativity.

 (4) The additive half of an internal ring IS a group object:
 [InternalRing_GroupObject : @GroupObject C CC_CartesianMonoidal r],
 built by passing [ir_add] through UNCHANGED, with no transport
 anywhere.  Read the inverse fields precisely: the ring's own
 [ir_neg_left] and [ring_neg_right] are REJECTED at those
 positions, [GroupObject] wanting the [bimap]/[diagonal]/
 [eliminate] spelling where the ring states the [fork]/[one] one.
 The bridging lemmas [ir_neg_left_split] and [ir_neg_right_split]
 supply the accepted statements, and it is THOSE that meet the
 field types by conversion ([bimap] = [split], [Delta] = [id fork
 id], [eliminate] = [one]).

 (5) The [Sets] instances.  [Sets_InternalSemiring] turns a [RigObject]
 into an internal semiring in [Sets] and [Rig_of_InternalSemiring]
 turns one back; likewise [Sets_InternalRing] /
 [Ring_of_InternalRing] for [RingObject].  Round trips are measured
 STRICT-FIRST.  Rig-side: all five DATA fields return by [eq_refl]
 ([rig_round_setoid], [rig_round_zero], [rig_round_add],
 [rig_round_one], [rig_round_mul]) while the WHOLE RECORD does not,
 pinned as a [Fail] -- the law fields are rebuilt proof terms.
 Internal-side: the unit and the multiplication agree at [eq_refl]
 ON VALUES ([semiring_round_zero], [semiring_round_add]) but the
 [Monoid] record does not, also pinned -- the [SetoidMorphism]s are
 rebuilt with different [proper_morphism] certificates.  Both
 [Fail]s were stripped and confirmed to be genuine CONVERSION
 failures ("cannot unify"), not typing or universe errors.

 ENGINEERING FINDING, and it shapes every statement below.  At
 [CC_Monoidal] the tensor IS the product: [bimap f g = split f g],
 [to unit_left = exr], [to unit_right = exl] and [to tensor_assoc =
 (exl o exl) /\ ((exr o exl) /\ exr)] all hold by [eq_refl], recorded as
 the four [Example]s opening the file.  But [mappend]'s type is
 [mon (x) mon ~> mon], i.e. [fobj tensor (mon, mon) ~> mon], which is
 only CONVERTIBLE with [mon x mon] and not syntactically equal: two
 separately elaborated occurrences of [mappend[M] o swap] record
 different object arguments in their [compose] nodes (one via
 [fst (r, r)], one via [product_obj r r]), and [rewrite] then cannot
 match one against the other.  Every occurrence of [mappend] and
 [mempty] below is therefore ascribed -- [(mappend[M] : r x r ~> r)],
 [(mempty[M] : 1 ~> r)] -- which forces one syntactic form throughout.
 The ascription is visible in [Print Module] output and invisible to
 [Check]; either way it is cosmetic, and the alternative (a pair of
 ascribed accessor definitions) was rejected because the sibling
 Structure/Lattice.v would then either duplicate them or acquire a
 dependency on this file.

 UNIVERSES, measured in the constraint blocks AND in the binders.
 [InternalSemiring@{u u0 u1}] and [InternalRing@{u u0 u1}] are over
 [Category@{u u0 u0}]: the hom and proof universes are IDENTIFIED while
 the OBJECT universe stays free (it appears only in [<=] bounds).  The
 identification is the DONORS' doing and THREE of them force it
 INDEPENDENTLY -- with the levels declared apart under
 [Constraint uh < up], a control naming a hom at those levels is
 accepted while each of [@Cartesian C], [@Terminal C] and
 [@Monoidal C] is rejected, each with a genuine
 "Cannot enforce up = uh".  [MonoidObject] is NOT a fourth donor: its
 signature takes a [Monoidal@{u u0}] argument over
 [C : Category@{u u0 u0}], so [@Monoidal C] is rejected before any
 field of it is consulted and it cannot be probed apart -- whether it
 identifies anything OF ITS OWN is UNKNOWN, not refuted.  Nothing here
 adds to the identification, and it is NOT claimed unavoidable.  Note
 that [dup_left@{u u0}] and
 [dup_right@{u u0}] have EMPTY constraint blocks and yet their binders
 display [Category@{u u0 u0}] -- the identification hides in the binder,
 inherited from [Cartesian].  [InternalRing_GroupObject@{u u0 u1 u2}]
 adds only the BOUNDS [u <= u2], [u0 <= u2] from [GroupObject], never an
 identification.  On the [Sets] side the four passages carry [o < so]
 as their only STRICT constraint, and no [Set] anywhere -- the rest of
 each block is some fifteen [<=] bounds against donor universes
 ([projections], [prod_rect], [Basics.compose], [eq_ind]), among them
 [o <= q], which relates two DECLARED binders, so "nothing else" would
 be wrong even read charitably.  The [Set]-freedom holds only because
 their
 universe binders are written out: unannotated, [Sets_Monoid] minimizes
 to [SetoidObject@{Set Set}] and [Sets_InternalSemiring] to
 [RigObject@{Set Set _}], which would have confined every [Sets] result
 to Set-sized carriers.  This is the minimization hazard
 Instance/Sets/Products.v and the #300 erratum record, met
 again.

 NON-VACUITY, proved rather than gestured at.  [Nat_ISemiring] and
 [Int_IRing] are the internal semiring and ring on the naturals and the
 integers, with the unit, zero, sum, product and negation all COMPUTING
 by [eq_refl], and both proved non-degenerate (zero and one are distinct
 -- [nat_semiring_nondegenerate], [int_ring_nondegenerate]), so the
 structures are not collapsed.  That the laws genuinely CONSTRAIN is
 proved two ways.  [nat_plus_not_distributive]: taking the additive
 monoid of the naturals as BOTH halves satisfies every monoid law and
 refutes left distributivity, so the distributivity fields are not
 automatic for an arbitrary pair of commutative monoid objects on one
 carrier.  And [Bool_Or_Monoid] -- disjunction on the two-element setoid
 -- used as both halves satisfies commutativity ([bool_or_comm]) AND
 BOTH distributivity laws ([bool_or_distrib_l], [bool_or_distrib_r])
 while refuting annihilation ([bool_or_not_annihilating]), so the
 annihilation PAIR is not implied by the rest, and [isr_annihilate_l]
 in particular is not.  Only the [_l] shape is refuted here; nothing
 below states [isr_annihilate_r]'s independence separately, though it
 follows from [bool_or_comm].  That much is why the pair must be
 assumed for a semiring and can be derived for a ring.

 WHAT IS NOT DELIVERED.
 - No bridge to Lawvere theories (see above); no theory of rings is
 constructed, and no equivalence with [Models] is stated.
 - No category of internal (semi)rings, no homomorphisms, no forgetful
 functor.  Only the object-level structure is defined.
 - No commutative-ring variant, no ideals, no modules over an internal
 ring, no internal-ring analogue of Instance/Mod.v.
 - No closure results: products of ring objects and exponentials of ring
 objects are NOT proved to be ring objects (Structure/Monoid.v proves
 the monoid analogues, [Product_Monoid] and [Hom_Monoid]; neither is
 lifted here).
 - No instance in any ambient category other than [Sets].  In
 particular no internal ring in [Top], [Coq] or a presheaf category,
 so "a ring object in Top is a topological ring" stays prose.
 - The [Sets] round trips are measured but NOT packaged as an
 equivalence or an isomorphism of categories; there is no category on
 either side to state one in.
 - [InternalRing_InternalSemiring] is a plain [Program Definition] and
 is deliberately NOT registered as an [Instance]: resolution would
 then be free to look for an [InternalRing] whenever an
 [InternalSemiring] is wanted, and the tree's practice (e.g.
 Structure/Biproduct/Cartesian.v) is to leave such passages
 unregistered.
 - Nothing is proved about the relation between [ir_neg] and
 multiplication (no (-a)b = -(ab)), and no uniqueness of negation. 

 --------
 Mac Lane，《为在职数学家而作的范畴论》，第二版，第 III.6 节，第 75 页（maclane:III.6:remark1）；nLab：
 https://ncatlab.org/nlab/show/ring+object
 https://ncatlab.org/nlab/show/internalization

 Mac Lane 的第 III.6 节通过交换图定义了幺半群对象和群对象，然后指出同样的方法适用于任何由有限运算和方程律给出的代数系统——接着以环和格作为下一个示例。此文件实现了环的部分；Structure/Lattice.v 实现了格的部分。“内在化”所带来的好处是，一个定义在不同的环境范畴中阅读时可以同时表示多种经典理论：在集合范畴(Set)中，一个环对象就是一个普通环，在拓扑空间范畴(Top)中是一个拓扑环，在方案范畴中是一个环方案，在层范畴中是一个环层。环境范畴必须提供足够的结构来表述公理，对于环来说，这不仅仅是一个幺半积：分配律需要一个变量使用两次（一个副本），而消去则是丢弃一个变量（一个舍弃操作）。一个带终对象的笛卡尔范畴提供了这两者，这就是为什么这个文件是在 [Cartesian] + [Terminal] 上开发的，而不是在光秃秃的 [Monoidal] 上——同样的原因是 Structure/Group.v 需要 [CartesianMonoidal]，而 Structure/Monoid.v 则什么也不要求。命名。[RingObject] 已被占用：Theory/Algebra/Rig.v 为集合类型的概念（在集合类型载体上的环）声明了一个同名记录，而 Theory/Algebra/Rig.v 同样使用了 [RigObject]。它们在此处都是可见的，因为下面的 [Sets] 部分需要与它们进行比较，所以这些名字不能被重复使用。该树已经在四个不同的名称下包含了四个不同的“幺半群”概念——[MonoidObject]（Structure/Monoid.v，内部）、[MonObject]（Construction/Deloop.v，一个简单的集合类型幺半群）、[Monoid]（Theory/Algebra/Monoid.v，单体范畴中的内部）和 [Monoid]（Theory/Coq/Monoid.v，基于 [Coq]）——并且那里的消歧运行“完整拼写 = 内部，缩写 = 集合级”（[GroupObject] vs [GrpObject]）。Rig.v 颠倒了该惯例，因此无法遵循；因此这里的类是 [InternalSemiring] 和 [InternalRing]，[Internal] 前缀准确说明了它们的区分点。两个名字在整个树中都是自由的，兄弟文件中的 [InternalLattice] 和 [InternalSemilattice] 也是如此。现有技术。没有任何树内类在单个对象上承载两个幺半群结构，如 [Monoid] -类型化字段--，这一限定构成了整个权利要求，早期修订稿曾将其描述为按“形状而非名称”搜索，但实际上这是按字段类型的名称进行扫描。按形状的话，模式确实出现了，并且在下面指定的文件中：对具有两个 [_assoc] 公理的记录体进行扫描会返回 Theory/Algebra/Rig.v 的 [RigObject]，其在一个等价类载体上承载 [(rig_zero, rig_add)] 和 [(rig_one, rig_mul)]——按元素而非作为内部幺半群对象，并且这正是该文件内部化的集合级理论。[GroupObject] 
 (Structure/Group.v)
 是唯一包含 [MonoidObject] 字段的记录，并且唯一具有理论/代数/单子.v 的兄弟类 [Monoid] 字段的记录是 Theory/Algebra/CommutativeMonoid.v 和 Theory/Algebra/Frobenius.v——每个只包含一个。（请注意，该文件的 [Monoid] 是 Structure/Monoid.v 的 [@MonoidObject C CC_Monoidal]，而不是 Theory/Algebra/Monoid.v 的同名类；这里只需要前者。）
 最接近的结构类似物是 Theory/Algebra/Frobenius.v 的 [Frobenius] 和 Theory/Algebra/SpecialCommutativeFrobenius.v，它们在一个对象上放置一个单子和一个共单子——不同的方差，并且没有分配律。这棵树唯一的分配性存在于 Structure/Distributive.v 的 [Distributive] 和 Structure/BiCCC.v，它们将环境 x 分配到环境 + 上；这是 AMBIENT 类别的一个性质，而不是某个对象承载的两个运算的性质。Structure/Preadditive.v 和 Structure/Semiadditive.v 在交换幺半群中丰富了 HOM-SET，Theory/Algebra/Rig.v 的 [EndRig] 从前加性类别的一个自同态 homo 中读取集合级别的 rig——邻近，但它是在 homo-set 上的 rig，而不是在对象上的。Theory/Algebra/Rig.v 本身是该文件内部化的集合级别理论。与 Lawvere 理论的关系。Mac Lane 的评论是函子语义的非正式版本：由有限操作和方程呈现的代数理论是一个具有有限积的范畴，它在 C 中的模型是保有限积的函子到 C。该树具有这些机制——Theory/Lawvere.v 的 [LawvereTheory]、Theory/Lawvere/Model.v 的 [Model] 记录（函子 + [CartesianFunctor] + [TerminalFunctor] 见证）以及在那里构建的范畴 [Models]，作为函子范畴的一个满子范畴。目前的类是在半环和环理论中该模式的手工实例。未提供：没有证明桥定理——无论是 [MonoidObject ~= Models(Th_Mon)] 还是它的环类比——也没有在此构建环的 Lawvere 理论。该连接被记录为一个指针，故意如此。交付的内容，以及其强度。

 (1)  [InternalSemiring r]：在 r 上的加法性 [Monoid]，是交换的，乘法性 [Monoid]，在 r 上，有两个分配律和两个零律。这是《七个草图定义》第 5.36 条 / Theory/Algebra/Rig.v 文件中的 [RigObject] 子句逐条解释；乘法不假设交换性。

 (2)  [InternalRing r]：加法性 [Monoid] + 交换性 + 一个仅具有左逆律的取负 [ir_neg]，乘法性 [Monoid]，以及两个分配律。零律不是域。(3) 两个消去律是环的定理（[ring_annihilate_l], [ring_annihilate_r]），所以[InternalRing_InternalSemiring]是真正的推导，而不是重新包装。该机制是[ring_cancel_idem]：一个箭头 k 映入 r，当 k = k + k 时，它是零箭头。也就是说，这是在态射上进行的通常的消去论证——没有涉及任何元素——并且它分别使用了一次加法结合律、加法单位律和逆元律（逆元律通过一个中间步骤然后被重复使用两次）。右逆元律由交换律推导得出（[ring_neg_right]）。(4) 内环的加法半群是一个群对象：[InternalRing_GroupObject : @GroupObject C CC_CartesianMonoidal r]，通过将[ir_add]传入UNCHANGED构建而成，且没有任何传输。在这些位置精确读取逆场：环自身的[ir_neg_left]和[ring_neg_right]在那些位置被拒绝，[GroupObject]希望使用[bimap]/[diagonal]/[eliminate]的拼写，而环声明的是[fork]/[one]的拼写。桥接引理[ir_neg_left_split]和[ir_neg_right_split]提供了被接受的陈述，并且正是这些通过转换满足字段类型（[bimap] = [split]，[Delta] = [id fork id]，[eliminate] = [one]）。(5) [Sets] 实例。[Sets_InternalSemiring] 将一个 [RigObject] 转换为 [Sets] 中的内部半环，而 [Rig_of_InternalSemiring] 将其转换回；同样 [Sets_InternalRing] / [Ring_of_InternalRing] 对于 [RingObject]。往返操作按 STRICT-FIRST 测量。Rig 侧：所有五个数据字段由 [eq_refl] 返回（[rig_round_setoid], [rig_round_zero], [rig_round_add], [rig_round_one], [rig_round_mul]），而整个记录并不返回，以 [Fail] 固定 -- 法则字段是重建的证明项。内部侧：单位元素和乘法在 [eq_refl] 上的值（[semiring_round_zero], [semiring_round_add]）上匹配，但 [Monoid] 记录不匹配，也已固定 -- [SetoidMorphism] 是使用不同的 [proper_morphism] 证书重建的。两者 [Fail] 都被剥离并确认是真正的转换失败（“无法统一”），而不是类型或宇宙错误。工程发现，并影响了以下每一个陈述。在
 [CC_Monoidal]张量即为乘积：[bimap f g = split f g]，
 [to unit_left = exr] 、 、 [to unit_right = exl] 和 [到 tensor_assoc =
 （exl o exl） /\ （（exr o exl） /\ exr）] 全部由[eq_refl]保持，记录为
 四个[Example]打开文件。但[mappend]的类型是
 [mon (x) mon ~> mon] ，即[fobj tensor (mon, mon) ~> mon] ，即
 只有 CONVERTABLE，且语法上不等于 [mon x mon]：2
 单独详细阐述的 [mappend[M] o 交换] 记录
 [compose]节点中的不同对象参数（通过
 [fst (r, r)] ，通过 [product_obj r r]），[rewrite] 则不能
 将两者对抗。每一次[mappend]和
 因此，[mempty] 归于—— [(mappend[M] ： r x r ~> r）]，
 [(mempty[M] ： 1 ~> r）] ——这强制使整个句法形式始终采用统一。这个归属在 [Print Module] 输出中是可见的，而在 [Check] 中是不可见的；无论哪种情况，它都是表面上的。替代方案（一对归属的访问器定义）被拒绝，因为关联的 Structure/Lattice.v 文件要么会重复它们，要么会因此依赖于这个文件。宇宙，在约束块和绑定器中进行测量。[InternalSemiring@{u u0 u1}] 和 [InternalRing@{u u0 u1}] 超过 [Category@{u u0 u0}]：同构宇宙和证明宇宙被识别，而对象宇宙保持自由（它仅出现在 [<=] 的界限中）。这种识别是捐赠者的行为，其中三者独立强制执行——在 [Constraint uh < up] 下声明的级别分开，一个在这些级别上命名同构的控制被接受，而 [@Cartesian C]、[@Terminal C] 和 [@Monoidal C] 均被拒绝，每个都有一个真实的“无法强制 up = uh”。[MonoidObject] 不是第四个捐赠者：它的签名采用一个 [Monoidal@{u u0}] 参数，作用于 [C : Category@{u u0 u0}]，因此在查看其任何字段之前 [@Monoidal C] 被拒绝，并且它不能单独探测——它是否识别自己的一些内容未知，尚未被否定。这里的内容
 对识别没有任何帮助，也不声称是不可避免的。请注意
 [dup_left@{u u0}] 和
 [dup_right@{u u0}] 有空的约束块，但它们的绑定器
 显示 [Category@{u u0 u0}] —— 识别隐藏在绑定器中，
 从 [Cartesian] 继承而来。[InternalRing_GroupObject@{u u0 u1 u2}] 
 仅添加了来自 [GroupObject] 的 BOUNDS [u <= u2]、[u0 <= u2]，从未添加
 识别。在 [Sets] 方面，这四个通道仅携带 [o < so] 
 作为它们唯一的 STRICT 约束，并且在任何地方都没有 [Set] —— 每个块的其余部分是大约十五个 [<=] 的界限，用于对捐赠宇宙
 ([projections]、[prod_rect]、[Basics.compose]、[eq_ind]) 进行约束，其中有
 [o <= q]，它关联两个 DECLARED 绑定器，因此即使宽容地理解，“没有其他东西”也是错误的。[Set] 的自由仅仅因为他们的宇宙绑定器被写了出来：未标注时，[Sets_Monoid] 最小化为 [SetoidObject@{Set Set}]，[Sets_InternalSemiring] 最小化为 [RigObject@{Set Set _}]，这本来会将每个 [Sets] 结果限制在集合大小的承载体上。这就是 Instance/Sets/Products.v 和 #300 勘误记录中遇到的最小化风险，再次遇到了。非空性，经过证明而非仅仅手势表示。[Nat_ISemiring] 和 [Int_IRing] 分别是自然数和整数上的内部半环和环，单位元、零、加法、乘法和取负运算都由 [eq_refl] 计算，并且两者都被证明为非退化（零和一不同——[nat_semiring_nondegenerate]、[int_ring_nondegenerate]），因此这些结构没有被塌缩。这些定律确实产生约束的事实有两种证明方式。[nat_plus_not_distributive]：将自然数的加法幺半群作为两部分，将满足每一个幺半群定律并否定左分配律，因此对于同一载体上的任意一对交换幺半群对象，分配律场并非自动成立。并且 [Bool_Or_Monoid] —— 在二元素集合上取析取运算
 —— 当两部分都采用时同时满足交换律（[bool_or_comm]）以及
 两个分配律（[bool_or_distrib_l]，[bool_or_distrib_r]），
 同时否定了零化律（[bool_or_not_annihilating]），因此零化对并不由其余部分导出，且 [isr_annihilate_l]
 尤其不被导出。这里只有 [_l] 形态被否定；下面没有单独声明 [isr_annihilate_r] 的独立性，尽管它可由 [bool_or_comm] 推导得出。这也是为什么在半环中必须假设该对，并且在环中可以导出该对的原因。未交付的内容。- 与Lawvere理论无桥接（见上文）；没有构建环的理论，也没有说明与[Models]的等价性。- 没有内部（半）环的范畴，没有同态，也没有遗忘函子。仅定义了对象层级的结构。- 没有交换环变体，没有理想，没有内部环上的模，没有内部环的Instance/Mod.v类比。- 没有闭包结果：环对象的积和环对象的指数未被证明为环对象（Structure/Monoid.v证明了单子类比，[Product_Monoid]和[Hom_Monoid]；这里都没有提升）。- 在[Sets]之外的任何环境范畴中没有实例。特别是在 [Top]、[Coq] 或预层范畴中不存在内部环，因此“Top 中的环对象是拓扑环”仍保持散文形式。- [Sets] 的来回测量了，但并未作为范畴等价或同构打包；在任一侧都没有范畴可供表述。- [InternalRing_InternalSemiring] 是一个普通的 [Program Definition]，并且刻意未注册为 [Instance]：解析时可以自由地在需要 [InternalSemiring] 时寻找 [InternalRing]，而树的做法（例如 Structure/Biproduct/Cartesian.v）是将这种情况保持未注册状态。- 关于 [ir_neg] 与乘法的关系（没有 (-a)b = -(ab)）以及取反的唯一性，没有任何证明。
*)

Section CartesianMonoid.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

Example bimap_is_split {x y z w : C} (f : x ~> y) (g : z ~> w) :
  @bimap C C C (@tensor C CC_Monoidal) _ _ _ _ f g = split f g := eq_refl.

Example unit_left_is_exr {x : C} :
  to (@unit_left C CC_Monoidal x) = exr := eq_refl.

Example unit_right_is_exl {x : C} :
  to (@unit_right C CC_Monoidal x) = exl := eq_refl.

Example tensor_assoc_is_fork {x y z : C} :
  to (@tensor_assoc C CC_Monoidal x y z)
    = (exl ∘ exl) △ ((exr ∘ exl) △ exr) := eq_refl.

Context {m : C}.
Context (M : Monoid m).

Lemma cartesian_monoid_unit_left :
  (mappend[M] : m × m ~> m) ∘ split (mempty[M] : 1 ~> m) id ≈ exr.
Proof. exact (@mempty_left _ _ _ M). Qed.

Lemma cartesian_monoid_unit_right :
  (mappend[M] : m × m ~> m) ∘ split id (mempty[M] : 1 ~> m) ≈ exl.
Proof. exact (@mempty_right _ _ _ M). Qed.

Lemma cartesian_monoid_assoc :
  (mappend[M] : m × m ~> m) ∘ split (mappend[M] : m × m ~> m) id
    ≈ (mappend[M] : m × m ~> m) ∘ split id (mappend[M] : m × m ~> m)
        ∘ ((exl ∘ exl) △ ((exr ∘ exl) △ exr)).
Proof. exact (@mappend_assoc _ _ _ M). Qed.

End CartesianMonoid.

Section Duplication.

Context {C : Category}.
Context `{@Cartesian C}.

Definition dup_left {x : C} : x × (x × x) ~> (x × x) × (x × x) :=
  second exl △ second exr.

Definition dup_right {x : C} : (x × x) × x ~> (x × x) × (x × x) :=
  first exl △ first exr.

Lemma dup_left_fork {x w : C} (a b c : w ~> x) :
  dup_left ∘ (a △ (b △ c)) ≈ (a △ b) △ (a △ c).
Proof. unfold dup_left; unfork; cat. Qed.

Lemma dup_right_fork {x w : C} (a b c : w ~> x) :
  dup_right ∘ ((a △ b) △ c) ≈ (a △ c) △ (b △ c).
Proof. unfold dup_right; unfork; cat. Qed.

Lemma prod_assoc_fork {x w : C} (a b c : w ~> x) :
  ((exl ∘ exl) △ ((exr ∘ exl) △ exr)) ∘ ((a △ b) △ c) ≈ a △ (b △ c).
Proof. unfork; cat. Qed.

End Duplication.

Section Internalize.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

Class InternalSemiring (r : C) := {
  isr_add : Monoid r;
  isr_mul : Monoid r;

  isr_add_comm :
    (mappend[isr_add] : r × r ~> r) ∘ swap ≈ mappend[isr_add];

  isr_distrib_l :
    (mappend[isr_mul] : r × r ~> r) ∘ second (mappend[isr_add] : r × r ~> r)
      ≈ (mappend[isr_add] : r × r ~> r)
          ∘ split (mappend[isr_mul] : r × r ~> r) mappend[isr_mul]
          ∘ dup_left;
  isr_distrib_r :
    (mappend[isr_mul] : r × r ~> r) ∘ first (mappend[isr_add] : r × r ~> r)
      ≈ (mappend[isr_add] : r × r ~> r)
          ∘ split (mappend[isr_mul] : r × r ~> r) mappend[isr_mul]
          ∘ dup_right;

  isr_annihilate_l :
    (mappend[isr_mul] : r × r ~> r) ∘ (((mempty[isr_add] : 1 ~> r) ∘ one) △ id)
      ≈ (mempty[isr_add] : 1 ~> r) ∘ one;
  isr_annihilate_r :
    (mappend[isr_mul] : r × r ~> r) ∘ (id △ ((mempty[isr_add] : 1 ~> r) ∘ one))
      ≈ (mempty[isr_add] : 1 ~> r) ∘ one
}.

Class InternalRing (r : C) := {
  ir_add : Monoid r;
  ir_mul : Monoid r;
  ir_neg : r ~> r;

  ir_add_comm :
    (mappend[ir_add] : r × r ~> r) ∘ swap ≈ mappend[ir_add];
  ir_neg_left :
    (mappend[ir_add] : r × r ~> r) ∘ (ir_neg △ id)
      ≈ (mempty[ir_add] : 1 ~> r) ∘ one;

  ir_distrib_l :
    (mappend[ir_mul] : r × r ~> r) ∘ second (mappend[ir_add] : r × r ~> r)
      ≈ (mappend[ir_add] : r × r ~> r)
          ∘ split (mappend[ir_mul] : r × r ~> r) mappend[ir_mul]
          ∘ dup_left;
  ir_distrib_r :
    (mappend[ir_mul] : r × r ~> r) ∘ first (mappend[ir_add] : r × r ~> r)
      ≈ (mappend[ir_add] : r × r ~> r)
          ∘ split (mappend[ir_mul] : r × r ~> r) mappend[ir_mul]
          ∘ dup_right
}.

End Internalize.

Section RingDerived.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context {r : C}.
Context `{R : @InternalRing C _ _ r}.

Lemma ring_neg_right :
  (mappend[ir_add] : r × r ~> r) ∘ (id △ ir_neg)
    ≈ (mempty[ir_add] : 1 ~> r) ∘ one.
Proof.
  rewrite <- (swap_fork ir_neg id).
  rewrite comp_assoc.
  rewrite ir_add_comm.
  apply ir_neg_left.
Qed.

Lemma ring_add_zero_left {x : C} (g : x ~> r) :
  (mappend[ir_add] : r × r ~> r)
      ∘ (((mempty[ir_add] : 1 ~> r) ∘ one[x]) △ g)
    ≈ g.
Proof.
  transitivity ((mappend[ir_add] : r × r ~> r)
                  ∘ split (mempty[ir_add] : 1 ~> r) id ∘ (one[x] △ g)).
  { rewrite <- comp_assoc, split_fork.
    now rewrite id_left. }
  rewrite cartesian_monoid_unit_left.
  now rewrite exr_fork.
Qed.

Lemma ring_cancel_idem {x : C} (k : x ~> r) :
  k ≈ (mappend[ir_add] : r × r ~> r) ∘ (k △ k) →
  k ≈ (mempty[ir_add] : 1 ~> r) ∘ one.
Proof.
  intro Hk.
  assert (HA : (mappend[ir_add] : r × r ~> r) ∘ ((ir_neg ∘ k) △ k)
                 ≈ (mempty[ir_add] : 1 ~> r) ∘ one[x]).
  { rewrite <- (id_left k) at 2.
    rewrite fork_comp, comp_assoc, ir_neg_left, <- comp_assoc.
    now rewrite one_comp. }
  assert (HB : (mappend[ir_add] : r × r ~> r)
                 ∘ (((mempty[ir_add] : 1 ~> r) ∘ one[x]) △ k)
                 ≈ (mempty[ir_add] : 1 ~> r) ∘ one[x]).
  { transitivity ((mappend[ir_add] : r × r ~> r)
                    ∘ split (mappend[ir_add] : r × r ~> r) id
                    ∘ (((ir_neg ∘ k) △ k) △ k)).
    { rewrite <- comp_assoc, split_fork, HA.
      now rewrite id_left. }
    rewrite cartesian_monoid_assoc.
    rewrite <- comp_assoc, prod_assoc_fork.
    rewrite <- comp_assoc, split_fork, id_left, <- Hk.
    exact HA. }
  now rewrite <- HB, ring_add_zero_left.
Qed.

Lemma ring_annihilate_l :
  (mappend[ir_mul] : r × r ~> r)
      ∘ (((mempty[ir_add] : 1 ~> r) ∘ one) △ id)
    ≈ (mempty[ir_add] : 1 ~> r) ∘ one.
Proof.
  apply ring_cancel_idem.
  symmetry.
  transitivity ((mappend[ir_mul] : r × r ~> r)
                  ∘ first (mappend[ir_add] : r × r ~> r)
                  ∘ (((((mempty[ir_add] : 1 ~> r) ∘ one[r])
                        △ ((mempty[ir_add] : 1 ~> r) ∘ one[r]))) △ id)).
  { rewrite ir_distrib_r.
    rewrite <- !comp_assoc, dup_right_fork.
    now rewrite split_fork. }
  rewrite <- comp_assoc, first_fork, ring_add_zero_left.
  reflexivity.
Qed.

Lemma ring_annihilate_r :
  (mappend[ir_mul] : r × r ~> r)
      ∘ (id △ ((mempty[ir_add] : 1 ~> r) ∘ one))
    ≈ (mempty[ir_add] : 1 ~> r) ∘ one.
Proof.
  apply ring_cancel_idem.
  symmetry.
  transitivity ((mappend[ir_mul] : r × r ~> r)
                  ∘ second (mappend[ir_add] : r × r ~> r)
                  ∘ (id △ ((((mempty[ir_add] : 1 ~> r) ∘ one[r])
                        △ ((mempty[ir_add] : 1 ~> r) ∘ one[r]))))).
  { rewrite ir_distrib_l.
    rewrite <- !comp_assoc, dup_left_fork.
    now rewrite split_fork. }
  rewrite <- comp_assoc, second_fork, ring_add_zero_left.
  reflexivity.
Qed.

Lemma ir_neg_left_split :
  (mappend[ir_add] : r × r ~> r) ∘ split ir_neg id ∘ (id △ id)
    ≈ (mempty[ir_add] : 1 ~> r) ∘ one[r].
Proof.
  rewrite <- comp_assoc, split_fork, id_left, id_right.
  apply ir_neg_left.
Qed.

Lemma ir_neg_right_split :
  (mappend[ir_add] : r × r ~> r) ∘ split id ir_neg ∘ (id △ id)
    ≈ (mempty[ir_add] : 1 ~> r) ∘ one[r].
Proof.
  rewrite <- comp_assoc, split_fork, id_left, id_right.
  apply ring_neg_right.
Qed.

(*
 [Structure/Group.v] declares [Notation "'inverse' [ G ]"], which makes
 [inverse] a notation keyword: neither [@inverse] nor a record-literal
 field assignment [inverse := _] parses.  The group object is therefore
 built with the constructor applied positionally. 

 --------
 [Structure/Group.v] 声明 [Notation "'inverse' [ G ]，这使得 [inverse] 成为一个记号关键字：既不是 [@inverse]，也不是记录字面值字段赋值 [inverse := _] 能被解析。因此，该组对象是通过按位置应用构造函数来构建的。
*)
Definition InternalRing_GroupObject :
  @GroupObject C CC_CartesianMonoidal r :=
  @Build_GroupObject C CC_CartesianMonoidal r ir_add ir_neg
    ir_neg_left_split ir_neg_right_split.

Program Definition InternalRing_InternalSemiring :
  @InternalSemiring C _ _ r := {|
  isr_add := ir_add;
  isr_mul := ir_mul
|}.
Next Obligation. exact ir_add_comm. Qed.
Next Obligation. exact ir_distrib_l. Qed.
Next Obligation. exact ir_distrib_r. Qed.
Next Obligation. exact ring_annihilate_l. Qed.
Next Obligation. exact ring_annihilate_r. Qed.

End RingDerived.

Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Section SetsInternal.

Program Definition Sets_Monoid@{o so p} (A : SetoidObject@{o o})
  (u : carrier A) (op : carrier A → carrier A → carrier A)
  (opP : Proper@{o p} (equiv ==> equiv ==> equiv) op)
  (op_assoc : ∀ a b c, op (op a b) c ≈ op a (op b c))
  (unit_l : ∀ a, op u a ≈ a)
  (unit_r : ∀ a, op a u ≈ a) : @Monoid Sets@{o so} _ _ A := {|
  mempty := {| morphism := fun _ => u |};
  mappend := {| morphism := fun p => op (fst p) (snd p) |}
|}.
Next Obligation. proper; simpl in *; now apply opP. Qed.

Program Definition Sets_InternalSemiring@{o so q} (R : RigObject@{o o q}) :
  @InternalSemiring Sets@{o so} _ _ (rig_setoid R) := {|
  isr_add := Sets_Monoid (rig_setoid R) (rig_zero R) (rig_add R)
               (rig_add_respects R) (rig_add_assoc R) (rig_add_zero_l R)
               (rig_add_zero_r R);
  isr_mul := Sets_Monoid (rig_setoid R) (rig_one R) (rig_mul R)
               (rig_mul_respects R) (rig_mul_assoc R) (rig_mul_one_l R)
               (rig_mul_one_r R)
|}.
Next Obligation. now rewrite rig_add_comm. Qed.
Next Obligation. now rewrite rig_distr_l. Qed.
Next Obligation. now rewrite rig_distr_r. Qed.
Next Obligation. now rewrite rig_mul_zero_l. Qed.
Next Obligation. now rewrite rig_mul_zero_r. Qed.

Program Definition Sets_InternalRing@{o so q} (R : RingObject@{o o q}) :
  @InternalRing Sets@{o so} _ _ (rig_setoid R) := {|
  ir_add := Sets_Monoid (rig_setoid R) (rig_zero R) (rig_add R)
              (rig_add_respects R) (rig_add_assoc R) (rig_add_zero_l R)
              (rig_add_zero_r R);
  ir_mul := Sets_Monoid (rig_setoid R) (rig_one R) (rig_mul R)
              (rig_mul_respects R) (rig_mul_assoc R) (rig_mul_one_l R)
              (rig_mul_one_r R);
  ir_neg := {| morphism := ring_neg R |}
|}.
Next Obligation. now rewrite rig_add_comm. Qed.
Next Obligation. now rewrite ring_neg_l. Qed.
Next Obligation. now rewrite rig_distr_l. Qed.
Next Obligation. now rewrite rig_distr_r. Qed.

(*
 [PA] is new since the PR "algebraic carriers are sets" (2026-09-17): a
 [RigObject] carries [rig_prop], and an arbitrary [SetoidObject] of [Sets]
 supplies no [Prop] mirror for its `≈` (Instance/Sets/Propositional.v's
 header says why there is no such instance in general).  It is a class
 argument, so at every in-tree call site where [A] is a rig's own carrier it
 is discharged by [rig_prop] without being written. 

 --------
 [PA] 自从 PR “代数载体是集合”(2026-09-17) 以来是新的：一个 [RigObject] 承载 [rig_prop]，而一个任意的 [SetoidObject] 属于 [Sets] 并不为其 `≈` 提供 [Prop] 镜像（Instance/Sets/Propositional.v 的头文件说明了为什么一般情况下没有这样的实例）。这是一个类参数，因此在 [A] 作为一个幺半群自身载体的每个树内调用点，它都会被 [rig_prop] 解除，而无需书写。
*)
Program Definition Rig_of_InternalSemiring@{o so} {A : SetoidObject@{o o}}
  {PA : PropEquiv@{o o} (is_setoid A)}
  (S : @InternalSemiring Sets@{o so} _ _ A) : RigObject@{o o o} := {|
  rig_setoid := A;
  rig_zero := (mempty[isr_add] : _ ~{Sets}~> _) ttt;
  rig_add  := fun a b => (mappend[isr_add] : _ ~{Sets}~> _) (a, b);
  rig_one  := (mempty[isr_mul] : _ ~{Sets}~> _) ttt;
  rig_mul  := fun a b => (mappend[isr_mul] : _ ~{Sets}~> _) (a, b);

  rig_prop := PA
|}.
Next Obligation. proper; apply proper_morphism; simpl; split; assumption. Qed.
Next Obligation. proper; apply proper_morphism; simpl; split; assumption. Qed.
Next Obligation.
  exact (cartesian_monoid_assoc (@isr_add _ _ _ _ S) ((a, b), c)).
Qed.
Next Obligation. exact (@isr_add_comm _ _ _ _ S (b, a)). Qed.
Next Obligation.
  exact (cartesian_monoid_unit_left (@isr_add _ _ _ _ S) (ttt, a)).
Qed.
Next Obligation.
  exact (cartesian_monoid_assoc (@isr_mul _ _ _ _ S) ((a, b), c)).
Qed.
Next Obligation.
  exact (cartesian_monoid_unit_left (@isr_mul _ _ _ _ S) (ttt, a)).
Qed.
Next Obligation.
  exact (cartesian_monoid_unit_right (@isr_mul _ _ _ _ S) (a, ttt)).
Qed.
Next Obligation. exact (@isr_distrib_l _ _ _ _ S (a, (b, c))). Qed.
Next Obligation. exact (@isr_distrib_r _ _ _ _ S ((a, b), c)). Qed.
Next Obligation. exact (@isr_annihilate_l _ _ _ _ S a). Qed.
Next Obligation. exact (@isr_annihilate_r _ _ _ _ S a). Qed.


Program Definition Ring_of_InternalRing@{o so} {A : SetoidObject@{o o}}
  {PA : PropEquiv@{o o} (is_setoid A)}
  (R : @InternalRing Sets@{o so} _ _ A) : RingObject@{o o o} := {|
  ring_rig := Rig_of_InternalSemiring
                (@InternalRing_InternalSemiring Sets _ _ A R);
  ring_neg := fun a => (ir_neg : _ ~{Sets}~> _) a
|}.
Next Obligation. proper; now apply proper_morphism. Qed.
Next Obligation. exact (@ir_neg_left _ _ _ _ R a). Qed.

End SetsInternal.

Section SetsRoundTrip.

Context (R : RigObject).

Example rig_round_setoid :
  rig_setoid (Rig_of_InternalSemiring (Sets_InternalSemiring R))
    = rig_setoid R := eq_refl.
Example rig_round_zero :
  rig_zero (Rig_of_InternalSemiring (Sets_InternalSemiring R))
    = rig_zero R := eq_refl.
Example rig_round_add :
  rig_add (Rig_of_InternalSemiring (Sets_InternalSemiring R))
    = rig_add R := eq_refl.
Example rig_round_one :
  rig_one (Rig_of_InternalSemiring (Sets_InternalSemiring R))
    = rig_one R := eq_refl.
Example rig_round_mul :
  rig_mul (Rig_of_InternalSemiring (Sets_InternalSemiring R))
    = rig_mul R := eq_refl.

Fail Example rig_round_record :
  (Rig_of_InternalSemiring (Sets_InternalSemiring R)) = R := eq_refl.

Context {A : SetoidObject}.
(*
 The round trip below runs at an ARBITRARY carrier, which supplies no
 [Prop] mirror of its own; [Rig_of_InternalSemiring] therefore asks for one
 and the section hands it over.  See that definition for why. 

 --------
 下面的往返运行在一个任意的载波上，该载波没有自己的[Prop]镜；因此[Rig_of_InternalSemiring]请求一个，分支就将其交出。参见该定义了解原因。
*)
Context (PA : PropEquiv (is_setoid A)).
Context (S : @InternalSemiring Sets _ _ A).

Example semiring_round_add (a b : carrier A) :
  (mappend[@isr_add _ _ _ _
     (Sets_InternalSemiring (Rig_of_InternalSemiring S))] : _ ~{Sets}~> _)
    (a, b)
  = (mappend[@isr_add _ _ _ _ S] : _ ~{Sets}~> _) (a, b) := eq_refl.

Example semiring_round_zero :
  (mempty[@isr_add _ _ _ _
     (Sets_InternalSemiring (Rig_of_InternalSemiring S))] : _ ~{Sets}~> _) ttt
  = (mempty[@isr_add _ _ _ _ S] : _ ~{Sets}~> _) ttt := eq_refl.

Fail Example semiring_round_monoid :
  (@isr_add _ _ _ _ (Sets_InternalSemiring (Rig_of_InternalSemiring S)))
    = (@isr_add _ _ _ _ S) := eq_refl.

End SetsRoundTrip.

Section SetsWitness.

Definition Nat_ISemiring : @InternalSemiring Sets _ _ nat_setoid_object :=
  Sets_InternalSemiring Nat_Rig.

Definition Int_IRing : @InternalRing Sets _ _ (rig_setoid Int_Ring) :=
  Sets_InternalRing Int_Ring.

Example nat_zero_computes :
  (mempty[@isr_add _ _ _ _ Nat_ISemiring] : _ ~{Sets}~> _) ttt = 0%nat
  := eq_refl.
Example nat_one_computes :
  (mempty[@isr_mul _ _ _ _ Nat_ISemiring] : _ ~{Sets}~> _) ttt = 1%nat
  := eq_refl.
Example nat_add_computes :
  (mappend[@isr_add _ _ _ _ Nat_ISemiring] : _ ~{Sets}~> _) (2%nat, 3%nat)
    = 5%nat := eq_refl.
Example nat_mul_computes :
  (mappend[@isr_mul _ _ _ _ Nat_ISemiring] : _ ~{Sets}~> _) (2%nat, 3%nat)
    = 6%nat := eq_refl.

Lemma nat_semiring_nondegenerate :
  (mempty[@isr_add _ _ _ _ Nat_ISemiring] : _ ~{Sets}~> _) ttt
    <> (mempty[@isr_mul _ _ _ _ Nat_ISemiring] : _ ~{Sets}~> _) ttt.
Proof. discriminate. Qed.

Example int_neg_computes :
  (@ir_neg _ _ _ _ Int_IRing : _ ~{Sets}~> _) 7%Z = (-7)%Z := eq_refl.

Lemma int_ring_nondegenerate :
  (mempty[@ir_add _ _ _ _ Int_IRing] : _ ~{Sets}~> _) ttt
    <> (mempty[@ir_mul _ _ _ _ Int_IRing] : _ ~{Sets}~> _) ttt.
Proof. discriminate. Qed.

Definition int_annihilate_instance := @ring_annihilate_l Sets _ _ _ Int_IRing.

End SetsWitness.

Section LawsConstrain.

#[local] Ltac bool_crush :=
  repeat intro; simpl in *;
  repeat match goal with [ b : bool |- _ ] => destruct b end;
  simpl in *; congruence.

(*
 [orb] on the two-element setoid is a commutative monoid with unit
 [false].  Used TWICE below, as both the additive and the multiplicative
 half, to show that annihilation is independent of the remaining
 [InternalSemiring] laws. 

 --------
 [orb] 在双元素等价集合上是一个交换幺半群，单位元为 [false]。在下面使用了两次，作为加法和乘法的一半，以显示湮灭与剩余的 [InternalSemiring] 定律无关。
*)
Program Definition Bool_Or_Monoid : @Monoid Sets _ _ bool_setoid_object :=
  Sets_Monoid bool_setoid_object false orb _ _ _ _.
Next Obligation. bool_crush. Qed.
Next Obligation. bool_crush. Qed.

Lemma bool_or_comm :
  (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _) ∘ swap
    ≈ mappend[Bool_Or_Monoid].
Proof. intros [[|] [|]]; reflexivity. Qed.

Lemma bool_or_distrib_l :
  (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
      ∘ second (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
    ≈ (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
        ∘ split (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
                mappend[Bool_Or_Monoid]
        ∘ dup_left.
Proof. intros [[|] [[|] [|]]]; reflexivity. Qed.

Lemma bool_or_distrib_r :
  (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
      ∘ first (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
    ≈ (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
        ∘ split (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
                mappend[Bool_Or_Monoid]
        ∘ dup_right.
Proof. intros [[[|] [|]] [|]]; reflexivity. Qed.

Lemma bool_or_not_annihilating :
  ((mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
      ∘ (((mempty[Bool_Or_Monoid] : 1 ~{Sets}~> _) ∘ one) △ id)
    ≈ (mempty[Bool_Or_Monoid] : 1 ~{Sets}~> _) ∘ one) → False.
Proof. intro Hx; specialize (Hx true); discriminate. Qed.

Definition Nat_Plus_Monoid : @Monoid Sets _ _ nat_setoid_object :=
  @isr_add _ _ _ _ Nat_ISemiring.

Lemma nat_plus_not_distributive :
  ((mappend[Nat_Plus_Monoid] : _ × _ ~{Sets}~> _)
      ∘ second (mappend[Nat_Plus_Monoid] : _ × _ ~{Sets}~> _)
    ≈ (mappend[Nat_Plus_Monoid] : _ × _ ~{Sets}~> _)
        ∘ split (mappend[Nat_Plus_Monoid] : _ × _ ~{Sets}~> _)
                mappend[Nat_Plus_Monoid]
        ∘ dup_left) → False.
Proof. intro Hx; specialize (Hx (1%nat, (0%nat, 0%nat))); discriminate. Qed.

End LawsConstrain.
