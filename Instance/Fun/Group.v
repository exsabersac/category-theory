Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Group.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Group.Representable.
Require Import Category.Instance.Grp.

Generalizable All Variables.

(* * * Group objects in a functor category are pointwise groups / * * 函子范畴中的群对象是逐点群 *)

(*
 nLab:      https://ncatlab.org/nlab/show/group+object
 nLab:      https://ncatlab.org/nlab/show/functor+category
 Wikipedia: https://en.wikipedia.org/wiki/Group_object
 Book:      Mac Lane, CWM 2nd ed., Section III.6 (“Groups in
 Categories”), Exercise 3, p. 76

 Mac Lane's exercise: a functor [T : B ⟶ Sets] is a group object in
 the functor category [[B, Sets]] exactly when every value [T b] is an
 ordinary group and every [T f] is a group homomorphism.  Everything
 that makes this work is that [Sets] has finite products and that
 [Instance/Fun/Cartesian.v] and [Instance/Fun/Terminal.v] compute the
 products of [[B, Sets]] POINTWISE, so that each diagrammatic law of
 [Structure/Group.v]'s [GroupObject], read at an object [b] and at an
 element, IS the corresponding elementary group law in [T b], and the
 NATURALITY of the structure maps IS the statement that each [T f] is
 a homomorphism.

 A PRIOR-ART CORRECTION, WITH ITS DATE.  The issue states that “no
 monoid or group object is ever instantiated at a functor category”.
 READ THAT IN TWO HALVES, because only one of them is newly false.
 THE MONOID HALF WAS NEVER TRUE: Monad/Monoid.v has carried
 [Monoid_Monad : @MonoidObject (Endofunctors C) Compose_Monoidal M
 <-> Monad M] since 2017-05-29, where [Endofunctors C := [C, C]] --
 a monoid object at a functor category, in the build set
 (_CoqProject), and named in Structure/Monoid.v, which THIS
 FILE Requires.  An earlier revision of this header dated the whole
 claim to f3b797fd and was wrong to; the tensor there is
 [Compose_Monoidal] rather than the pointwise cartesian one used
 here, but the absence claim is unqualified as to tensor, so the
 qualifier does not rescue it.  The alias is how the miss happened
 and is worth recording: grepping for [@MonoidObject (\[] does not
 match, because the functor category hides behind [Endofunctors].
 THE GROUP HALF is the part genuinely falsified at master f3b797fd,
 which landed issue #341 as
 Structure/Group/Representable.v: its [RepPresheaf_Group] has type
 [forall {C} (e : C), HomGroupData e -> GroupObject (RepPresheaf e)]
 and [RepPresheaf e : [C^op, Sets]], so its conclusion is literally a
 group object in a functor category, over exactly the pointwise
 [Functor_Category_Cartesian]/[Functor_Category_Terminal] structure
 used here.  [RepresentablyGroup e] is that type packaged.

 WHAT #341 SUPPLIED AND WHAT IT DID NOT, measured rather than assumed.
 No PROOF CONTENT from Structure/Group/Representable.v is reused by
 the development below -- the cross-link at the end of this file does
 consume three of its DEFINITIONS ([RepresentablyMonoid],
 [RepresentablyGroup], [RepPresheaf]), and this file Requires that
 module for them; its central record [HomGroupData e] carries a
 group structure on the hom-SETS [x ~> e], which presupposes that the
 functor in question is [C(-,e)], while [T] here is arbitrary and its
 values [T b] are plain setoids.  Its [FromPresheaf]/[FromPresheafGroup]
 sections are the closest analogue -- they decompose a monoid or group
 object of [[C^op, Sets]] into elementwise operations, exactly the
 forward direction below -- but both are stated inside a section whose
 [Context] FIXES the object to [RepPresheaf e], so neither can be
 applied to an arbitrary [T].  Its generic product-form readings of the
 diagrammatic laws ([rg_unit_left_law] and siblings) WOULD have applied
 at [C := [B, Sets]]; they are not used, because over [Sets] the laws
 evaluate at elements directly and the product form is a detour.  The
 traffic runs the other way instead: [representably_group_iff_pointwise]
 below obtains #341's presheaf statement as an INSTANCE of this one, by
 [:=] with no tactic.

 WHAT IS DELIVERED, AND AT WHAT STRENGTH.

 (A) Two records, [PointwiseMonoid T] and [PointwiseGroup T], holding
 exactly Mac Lane's data: a group (monoid) structure on each [T b],
 and the clauses saying each [T f] is a homomorphism.

 (B) The headline BICONDITIONALS -- genuine [iffT]s, not a pair of
 named passages -- [monoid_object_iff_pointwise] and
 [group_object_iff_pointwise].  Both are [Defined], so the two
 passages are the named constants [monoid_object_pointwise],
 [pointwise_MonoidObject], [group_object_pointwise] and
 [pointwise_GroupObject] and can be computed with.  The monoid
 analogue really is nearly free, and the file shows exactly how
 nearly: the group half adds one transformation, two laws and one
 naturality clause on each side, and reuses the monoid half by
 [groupobject_is_monoid] and by [pg_monoid].

 (C) The five diagrammatic laws are read off at a point BY CONVERSION:
 [fun_unit_l_raw], [fun_unit_r_raw], [fun_assoc_raw],
 [fun_inv_l_raw] and [fun_inv_r_raw] are the class fields applied
 to an explicit element, supplied by [:=] with no tactic and no
 transport.  So the elementary statements ARE the diagrammatic
 ones; nothing is compared across a bridge.

 (D) The ordinary-group reading, as a LIFT: [pointwise_GrpObject] gives
 an Instance/Grp.v [GrpObject] whose carrier is [T b] on the nose,
 [pointwise_GrpHom] gives a [GrpHom] whose underlying map is
 [fmap[T] f] on the nose (both carriers pinned by [eq_refl] in
 [pointwise_GrpObject_carrier] and [pointwise_MonObject_carrier]),
 and [PointwiseGrpFunctor P : B ⟶ Grp]
 assembles them, with [Grp_Forget ◯ PointwiseGrpFunctor P] agreeing
 with [T] on OBJECTS and on ARROWS by [eq_refl].  Conversely
 [grp_functor_PointwiseGroup] and [grp_functor_GroupObject] show
 that EVERY functor into [Grp] carries a group object on its
 underlying functor, with no hypothesis at all.

 STRENGTHS AND WEAKENINGS, each diagnosed.  Everything that survives on
 the nose is pinned as an [eq_refl] [Example]; three strict attempts
 are REFUTED, each pinned as a [Fail] beside the controls that guard
 it.  (i) [Grp_Forget ◯ PointwiseGrpFunctor P = T] is refused: the
 composite rebuilds [fmap_respects], [fmap_id] and [fmap_comp] as its
 own opaque proofs, so what fails is record equality and NOT the
 actions, which do agree ([PointwiseGrpFunctor_forgets_obj] and
 [_forgets_map] are the controls).  The lift is therefore NOT claimed
 strict, and no equality of functors is asserted anywhere.  (ii) The
 round trip on the pointwise datum returns all three OPERATIONS by
 [eq_refl] ([roundtrip_unit], [roundtrip_mul], [roundtrip_inv]) but not
 the whole record: [pw_mul_respects] is rebuilt.  (iii) The round trip
 on the object returns the VALUES of both structure maps by [eq_refl]
 ([roundtrip_obj_unit], [roundtrip_obj_mul]) but not the whole record,
 for the same reason one level up -- the naturality fields of the
 rebuilt transformations are this file's own opaque proofs.  So the two
 passages are mutually inverse ON THE DATA and nothing stronger is
 claimed; in particular neither biconditional is an equivalence of
 structures.

 One residue recurs in every proof and is worth naming: the identity
 natural transformation of [[B, Sets]] has component [fmap[F] id], not
 [id], so each law arrives with a [fmap[T] id] wrapped round one
 argument.  [T_fmap_id] discharges it.  This is the same [nat_id] fact
 already recorded at Theory/Natural/Transformation.v and consumed
 in Construction/Elements/Kan.v and Functor/Representable/Functorial.v.

 UNIVERSES, measured in the constraint block AND read off the binder,
 because here the two disagree.  [PointwiseMonoid@{bo bh bp o so}] and
 [PointwiseGroup@{bo bh bp o so}] are over [B : Category@{bo bh bp}]
 and [Sets@{o so}] and identify NOTHING: the block is [o < so] (which
 is [Sets]' own strictness) plus the bounds [bh <= bp], [bh <= o],
 [bp <= o] and four donor bounds ([o <= Basics.compose.u0/u1/u2],
 [o <= ID.u0]) -- EIGHT entries in all, not the four an earlier
 revision of this sentence listed as though exhaustive.  What matters
 is unchanged and is the point: there is NO equation anywhere in
 either record's block, and [bo] is entirely unconstrained.  Every
 constant of the file that BINDS a [B] is over
 [B : Category@{u u0 u0}] with the record instantiated at
 [PointwiseMonoid@{u u0 u0 u0 u1}] -- B's hom, B's proof and [Sets]'
 carrier universe ALL IDENTIFIED -- and that identification lives
 ENTIRELY IN THE BINDER: the constraint blocks contain [u0 < u1],
 [u <= u2], [u <= u3], [u1 <= u2] and further bounds, and NO equation,
 so reading the block alone would miss it completely.  The two OBJECT
 universes stay free throughout.  The [Witness] section's constants
 ([Und], [Z2_triv], [Und_GroupObject]) bind no [B] at all and are
 outside that description.

 RE-MEASURED after the PR “algebraic carriers are sets” (2026-09-17).
 [PointwiseMonoid]'s and [PointwiseGroup]'s own readbacks and their
 eight-entry blocks are UNCHANGED -- neither record carries a
 [PropEquiv] and neither gained an equation.  What changed is the
 [Grp]-valued layer, which now takes the presheaf's pointwise witness
 [PT] as an argument:

 pointwise_GrpObject@{u u0 u1} :
 ∀ {B : Category@{u u0 u0}} (T : Functor@{u u0 u0 u1 u0 u0}),
 (∀ b, PropEquiv@{u0 u0} (is_setoid (fobj b))) →
 PointwiseGroup@{u u0 u0 u0 u1} T → obj → GrpObject@{u0 u0 u0}
 ( * u0 < u1, plus the four donor bounds * )

 and [PointwiseGrpFunctor@{u u0 u1 u2}] likewise, its block gaining
 [Set < u2] -- a strict LOWER bound and not an identification, which
 enters with [Prop]'s own sort through [PropEquiv] and pins nothing.
 The claim that no record's block carries an equation stands.

 The cause is [Fun], and it is guarded rather than asserted: sections
 [UniverseBoundary] and [UniverseBoundary2] declare the levels apart
 and exhibit [B ⟶ Sets] and [PointwiseGroup T] as formable there while
 [[B, Sets]] is REJECTED, with the two halves separated -- [Fun] forces
 the source category's hom and proof universes to agree, AND forces the
 source's hom universe to be the target's, and neither half alone
 accounts for the collapse.  One qualification, stated rather than
 glossed: [PointwiseGrpFunctor], [pointwise_GrpObject] and
 [pointwise_GrpHom] mention no functor category, and [B ⟶ Grp] is
 formable with the levels apart, so THEIR identification is not
 [Fun]'s but the unannotated [Context {B : Category}] of the section
 they live in -- the minimization family recorded for
 [Build_Quiver_Standard_Eq].  It is repairable in principle and is NOT
 claimed unavoidable; a lift was not attempted, since the headline
 theorems mention [[B, Sets]] and so would keep the identification
 regardless.

 NON-VACUITY.  The witness index category is [Grp] itself and the
 witness functor is [Id[Grp]], so no new functor into [Grp] is built:
 [Und_GroupObject] is the underlying-set functor of [Grp] as a group
 object in [[Grp, Sets]], and the operations recovered from it COMPUTE
 at [Z2] ([und_unit_computes], [und_mul_computes], [und_inv_computes],
 all [eq_refl]).  Both degeneracies are excluded by proof rather than
 assumed: [und_nontrivial] shows the group at [Z2] has two distinct
 elements, and [und_fmap_not_id] shows the arrow action at the trivial
 endomorphism [Z2_triv] genuinely moves one, so the two homomorphism
 clauses are applied to a map that is not an identity.  A THIRD
 degeneracy is NOT excluded and is disclosed here rather than left for
 a reader to notice: the group is [Z2], where inversion IS the
 identity -- [und_inv_computes] records exactly that -- so [pg_inv],
 [pg_inv_l], [pg_inv_r] and [pg_map_inv] are never exercised at an
 element that is not its own inverse.  The index is [Grp] and the
 functor [Id[Grp]], so any in-tree group would serve; no such witness
 is built here.

 115/115 constants are Closed under the global context: [Print Module]
 lists 113, and the two unlisted names are [Build_PointwiseMonoid] and
 [Build_PointwiseGroup].  The file declares no [Axiom] and no
 [Parameter].  An earlier revision of this paragraph said “81” and
 gave as its reason that the [Program] obligations “leave no
 separately named constants behind”; BOTH were wrong -- there are 34
 such obligations and they are ordinary constants.  They are invisible
 to [Print Assumptions] under a BARE name (which is what produced the
 81) and resolve only fully qualified, e.g.
 [Category.Instance.Fun.Group.pointwise_MonoidObject_obligation_1].
 Note also that [Print Module] prints [Qed] constants as [Parameter];
 that is a display convention, not an axiom leak.

 NOT DELIVERED.  No abelian/commutative variant and no Eckmann-Hilton
 consequence.  No [Cocartesian] or coproduct story.  Nothing about a
 general target [D] in place of [Sets] -- the whole development reads
 the laws at ELEMENTS, so a general cartesian [D] would need the
 product-form route instead (which is why Structure/Group/Representable.v's
 [rg_*_law] lemmas are cited above rather than deleted).  No claim that
 [PointwiseGrpFunctor] is an equivalence between [PointwiseGroup T] and
 lifts of [T] through [Grp_Forget]: the object and arrow actions agree
 on the nose, but the strict lift is refuted and no groupoid of lifts is
 built.  The monoid analogue of the [Grp] reading stops at the OBJECT:
 [pointwise_MonObject] gives a Construction/Deloop.v [MonObject] per
 [b], but that record has no category attached, and the tree's only
 category of GENERAL monoids (Instance/CMon.v's [CMon] being
 commutative), Theory/Algebra/Monoid/Hom.v's [Mon], is a category of
 INTERNAL monoids over a chosen monoidal structure --
 [Mon Sets] is taken at [Sets_Product_Monoidal], which Instance/Grp.v's
 own note records as a distinct, NON-CONVERTIBLE term from the
 [CC_Monoidal] used here -- so no [Mon]-valued functor and no monoid
 twin of [PointwiseGrpFunctor] is built.  No naturality of
 the biconditional in [T], and no functoriality of [PointwiseGroup].
 And no witness with a NON-CONSTANT object action combined with a small
 index category: the witness's index is [Grp], which is large. 

 --------
 nLab:       https://ncatlab.org/nlab/show/group+object 
 nLab:       https://ncatlab.org/nlab/show/functor+category 
 Wikipedia:  https://en.wikipedia.org/wiki/Group_object 
 书籍:      Mac Lane, 《CWM》第二版, 第III.6节（“范畴中的群”），练习题3，第76页

 Mac Lane的练习题：一个函子 [T : B ⟶ Sets] 在函子范畴 [[B, Sets] 中恰好是一个群对象，当且仅当每个值 [T b] 是一个普通群且每个 [T f] 是一个群同态。使这一切成立的原因是 [Sets] 具有有限积，并且 [Instance/Fun/Cartesian.v] 和 [Instance/Fun/Terminal.v] 按元素计算 [[B, Sets] 的积，因此 [Structure/Group.v] 的每一个图示定律，在对象 [b] 和元素处阅读时，就是 [T b] 中对应的基本群律，而且结构映射的自然性 表明每个 [T f] 是一个同态。先前技术更正及其日期。问题中指出：“在函子范畴中从未实例化过单子或群对象。”请将其分为两半阅读，因为只有一半是新出现的错误。单子那半部分从未为真：自2017-05-29起，Monad/Monoid.v 已经包含 [Monoid_Monad : @MonoidObject (Endofunctors C) Compose_Monoidal M <-> Monad M]，其中 [Endofunctors C := [C, C] 是在构建集合 (_CoqProject) 中的函子范畴上的单子对象，并在 Structure/Monoid.v 中命名，而本文件需要它。该头文件的早期修订版将整个声明追溯到 f3b797fd，这个做法是错误的；那里使用的张量是 [Compose_Monoidal]，而非此处使用的逐点笛卡尔张量，但缺失声明对张量没有限定，所以这个限定无法挽救它。该别名是错误发生的方式，值得记录：搜索 [@MonoidObject (\[] 不匹配，因为函子类别隐藏在 [Endofunctors] 后面。GROUP HALF 是在 master f3b797fd 中真正伪造的部分，该提交包含了 issue #341，位于 Structure/Group/Representable.v：其 [RepPresheaf_Group] 类型为 [forall {C} (e : C), HomGroupData e -> GroupObject (RepPresheaf e)] 和 [RepPresheaf e : [C^op, Sets] ]，因此其结论字面上是函子类别中的一个群对象，恰好在这里使用的逐点 [Functor_Category_Cartesian] / [Functor_Category_Terminal] 结构上。[RepresentablyGroup e] 是该类型的封装形式。WHAT #341 提供了什么以及没有提供什么，是经过衡量而非假设的。下面的开发没有重用 Structure/Group/Representable.v 的任何 PROOF CONTENT —— 该文件末尾的交叉链接确实使用了它的三个定义（[RepresentablyMonoid]、[RepresentablyGroup]、[RepPresheaf]），并且本文件需要该模块以使用这些定义；它的中心记录 [HomGroupData e] 在同态集 [x ~> e] 上携带了一个群结构，这预设了相关函子是 [C(-,e)]，而这里的 [T] 是任意的，其值 [T b] 是普通的集合等价类。它的 [FromPresheaf] / [FromPresheafGroup] 章节是最接近的类比——它们将 [[C^op, Sets] ] 的幺半群或群对象分解为逐元素操作，正是下面的前向方向——但两者都在一个章节中说明，其中 [Context] 将对象固定为 [RepPresheaf e] ，因此都不能应用于任意的 [T] 。它对图示定律 ([rg_unit_left_law] 及其类似) 的通用乘积形式解读，本可以在 [C := [B, Sets] ] 使用；但未被使用，因为在 [Sets] 上，这些定律直接在元素上求值，而乘积形式是一种迂回。交通方向相反：下面的 [representably_group_iff_pointwise] 通过 [:=] ，无需任何策略，将 #341 的预层陈述作为此陈述的一个实例获得。

 提供了什么，以及其强度如何。(A) 两条记录，[PointwiseMonoid T] 和 [PointwiseGroup T]，完全包含 Mac Lane 的数据：每个 [T b] 上的群（幺半群）结构，以及每条 [T f] 是同态的条款。 

 (B) 标题为 BICONDITIONALS -- 真正的 [iffT]，而不是成对命名的段落 -- [monoid_object_iff_pointwise] 和 [group_object_iff_pointwise]。两者都是 [Defined]，因此这两段是命名常量 [monoid_object_pointwise]、[pointwise_MonoidObject]、[group_object_pointwise] 和 [pointwise_GroupObject]，并且可以进行计算。幺半群类似物确实几乎是自由的，并且文件显示了具体的近似程度：群的一半在每一侧增加了一个变换、两条定律和一个自然性条款，并通过 [groupobject_is_monoid] 和 [pg_monoid] 重用幺半群的一半。(C) 这五条图示规律是通过转换在某一点读取的：
 [fun_unit_l_raw]、[fun_unit_r_raw]、[fun_assoc_raw]、
 [fun_inv_l_raw] 和 [fun_inv_r_raw] 是应用于显式元素的类域，
 由 [:=] 提供，没有使用策略，也没有传递。因此，基本陈述就是图示陈述；没有任何内容在桥梁之间进行比较。(D) 普通群的解读，作为一个 LIFT：[pointwise_GrpObject] 给出了一个实例/群 v [GrpObject]，其载体正好是 [T b]，[pointwise_GrpHom] 给出了一个 [GrpHom]，其底层映射正好是 [fmap[T] f]（两个载体由 [eq_refl] 固定在 [pointwise_GrpObject_carrier] 和 [pointwise_MonObject_carrier] 中），并且 [PointwiseGrpFunctor P : B ⟶ Grp] 将它们组装起来，[Grp_Forget ◯ PointwiseGrpFunctor P] 在对象上以及通过 [eq_refl] 在箭头上都与 [T] 一致。相反，[grp_functor_PointwiseGroup] 和 [grp_functor_GroupObject] 表明，每一个进入 [Grp] 的函子都在其底层函子上携带一个群对象，而无需任何假设。优势与弱点，每一项都已诊断。鼻子上存活的一切都被固定为 [eq_refl] [Example]；三次严格尝试都被驳回，每次都被固定为 [Fail]，在保护它的控制旁边。(i) [Grp_Forget ◯ PointwiseGrpFunctor P = T] 被拒绝：复合体重建 [fmap_respects]、[fmap_id] 和 [fmap_comp] 作为其自身的不透明证明，所以失败的是记录相等性，而不是动作，它们确实一致 ([PointwiseGrpFunctor_forgets_obj] 和 [_forgets_map] 是控制)。因此提升不被视为严格，并且任何地方都没有断言函子相等。(ii) 点对点数据的往返操作返回了全部三个操作 [eq_refl] ([roundtrip_unit]、[roundtrip_mul]、[roundtrip_inv])，但不是整个记录：[pw_mul_respects] 被重建。(iii) 对对象的往返操作返回的是由 [eq_refl] ([roundtrip_obj_unit], [roundtrip_obj_mul]) 提供的两个结构映射的值，但不是整个记录，原因与上一层相同——重建变换的自然性字段是该文件自身的不透明证明。因此，这两个过程在数据上是相互逆的，但没有提出更强的断言；特别地，两个双条件都不是结构的等价。在每一个证明中都有一个重复出现的残留物，值得命名：[[B, Sets] 的同一性自然变换的分量是 [fmap[F] id]，而不是 [id]，因此每条定律都是由一个 [fmap[T] id] 包裹在一个参数周围得来的。[T_fmap_id] 将其释放。这与之前在 Theory/Natural/Transformation.v 中记录并在 Construction/Elements/Kan.v 和 Functor/Representable/Functorial.v 中使用的相同 [nat_id] 事实相同。宇宙，按照约束块测量并从活页夹中读取，因为这里两者不一致。[PointwiseMonoid@{bo bh bp o so}] 和 [PointwiseGroup@{bo bh bp o so}] 位于 [B : Category@{bo bh bp}] 和 [Sets@{o so}] 之上，并且没有识别任何内容：块是 [o < so]（这是 [Sets] 自身的严格性）加上界限 [bh <= bp]、[bh <= o]、[bp <= o] 以及四个捐赠界限（[o <= Basics.compose.u0/u1/u2]、[o <= ID.u0]）——总共有八条条目，而不是先前该句修订版本所列的四条，仿佛已穷尽。重要的没有改变，这就是要点：在任一记录块中都没有方程，并且 [bo] 完全没有约束。文件中每一个绑定 [B] 的常量，其值都超过 [B : Category@{u u0 u0}]，记录在 [PointwiseMonoid@{u u0 u0 u0 u1}] 实例化 —— B 的同源、B 的证明以及 [Sets] 的载体宇宙 全部已识别 —— 这种识别完全存在于绑定器中：约束块包含 [u0 < u1]、[u <= u2]、[u <= u3]、[u1 <= u2] 以及进一步的边界，并且没有任何方程，因此仅阅读该块会完全错过它。两个对象宇宙在整个过程中保持自由。[Witness] 部分的常量（[Und]、[Z2_triv]、[Und_GroupObject]）完全不绑定 [B]，并且不在该描述范围内。在 PR “代数载体是集合”（2026-09-17）之后重新测量。
 [PointwiseMonoid] 和 [PointwiseGroup] 自身的回读及它们的八条目块保持不变——没有记录携带 [PropEquiv]，也没有获得任何方程。改变的是 [Grp] 值的层，它现在将预层的逐点见证 [PT] 作为参数：

 pointwise_GrpObject@{u u0 u1} :
 ∀ {B : Category@{u u0 u0}} (T : Functor@{u u0 u0 u1 u0 u0}),
 (∀ b, PropEquiv@{u0 u0} (is_setoid (fobj b))) →
 PointwiseGroup@{u u0 u0 u0 u1} T → obj → GrpObject@{u0 u0 u0}
 ( * u0 < u1，加上四个捐赠者边界 * )以及 [PointwiseGrpFunctor@{u u0 u1 u2}] 同样，它的块获得
 [Set < u2] —— 严格的下界而不是识别，它
 通过 [PropEquiv] 与 [Prop] 自身的排序一起进入，并且不固定任何东西。
 声称没有记录的块携带方程的说法成立。原因是 [Fun]，它是被保护而不是被断言的：段落 [UniverseBoundary] 和 [UniverseBoundary2] 将级别分开，并展示 [B ⟶ Sets] 和 [PointwiseGroup T] 在那里是可形成的，而 [[B, Sets] 被拒绝，两个部分被分开——[Fun] 强制源类别的同态和证明宇宙一致，并且强制源的同态宇宙成为目标的，而单独的任何一半都不能解释崩溃。有一个限定条件，是陈述而非简化：[PointwiseGrpFunctor]、[pointwise_GrpObject] 和 [pointwise_GrpHom] 没有提到函子类别，并且 [B ⟶ Grp] 在级别分开的情况下是可形成的，所以它们的识别不是 [Fun] 的，而是它们所在段落的未注释 [Context {B : Category}]——记录用于 [Build_Quiver_Standard_Eq] 的最小化族。原则上它是可修复的，并且并未声称不可避免；没有尝试过提升，因为标题定理提到 [[B, Sets] ]，所以无论如何都会保持该标识。非空性。见证索引类别是 [Grp] 本身，见证函子是 [Id[Grp]，因此不会在 [Grp] 中构建新的函子：[Und_GroupObject] 是 [Grp] 作为 [[Grp, Sets] 中的群对象的底层集合函子，从中恢复的运算在 [Z2] 处计算（[und_unit_computes]、[und_mul_computes]、[und_inv_computes]，全部为 [eq_refl]）。两个退化性都通过证明排除，而不是假设：[und_nontrivial] 显示 [Z2] 处的群有两个不同的元素，[und_fmap_not_id] 显示在平凡自同态 [Z2_triv] 处的箭头作用确实移动了一个元素，因此两个同态条款都应用于一个不是恒等映射的映射上。第三种简并性并未被排除，并且在此披露，而不是留给读者去注意：该群是 [Z2]，其中逆元就是自身 —— [und_inv_computes] 正好记录了这一点 —— 因此 [pg_inv]、[pg_inv_l]、[pg_inv_r] 和 [pg_map_inv] 从未在非自身逆元的元素上使用。指标是 [Grp]，函子是 [Id[Grp]，因此任何树内群都可以使用；这里没有建立这样的见证。在全局上下文下，115/115 个常量是封闭的：[Print Module] 列出了 113 个，未列出的两个名称是 [Build_PointwiseMonoid] 和 [Build_PointwiseGroup]。该文件没有声明 [Axiom]，也没有 [Parameter]。该段早期版本说“81”，并给出的理由是 [Program] 的义务“不会留下单独命名的常量”；两者都是错误的——实际上有 34 个这样的义务，它们是普通常量。在 BARE 名称下（这正是产生 81 的原因），它们对于 [Print Assumptions] 是不可见的，只能通过完全限定名称解析，例如 [Category.Instance.Fun.Group.pointwise_MonoidObject_obligation_1]。还要注意，[Print Module] 将 [Qed] 常量打印为 [Parameter]；这是一种显示约定，而不是公理泄漏。未交付。没有阿贝尔/交换变体，也没有埃克曼-希尔顿的结果。没有 [Cocartesian] 或余积的内容。没有关于将一般目标 [D] 替代 [Sets] 的讨论——整个发展在元素层面读取定律，所以一个一般的笛卡尔 [D] 必须通过积形式路线（这也是为什么上面引用了 Structure/Group/Representable.v 的 [rg_*_law] 引理而不是删除它们）。没有声称 [PointwiseGrpFunctor] 是 [PointwiseGroup T] 与通过 [Grp_Forget] 提升 [T] 之间的等价：对象和箭头的作用确切一致，但严格的提升被否定，也没有构建提升的群体。[Grp] 的幺半群类比读取在 OBJECT 处停止：
 [pointwise_MonObject] 给出一个 Construction/Deloop.v  [MonObject] 每
 [b]，但该记录没有附加类别，而树的唯一
 一般幺半群的类别（Instance/CMon.v 的 [CMon] 是
 交换的），Theory/Algebra/Monoid/Hom.v 的 [Mon]，是在选定的幺半群结构上的内部幺半群的类别——
 [Mon Sets] 取自 [Sets_Product_Monoidal]，而 Instance/Grp.v 的
 自身注释记录为与此处使用的 [CC_Monoidal] 不同、不可转换的项——因此没有 [Mon] 值的函子，也没有 [PointwiseGrpFunctor] 的幺半群对应物。[T] 中双条件的自然性不存在，[PointwiseGroup] 的函子性也不存在。并且没有带有非恒定对象动作的小索引类别的见证：该见证的索引是 [Grp]，索引较大。
*)

(* ------------------------------------------------------------------ *)
(* The pointwise datum / 逐点数据 *)
(* ------------------------------------------------------------------ *)

(*
 Declared at top level with explicit universe binders rather than inside
 the section below: with an unannotated [Context {B : Category}] the
 elaborator MINIMIZES, identifying B's hom and proof universes with each
 other and with [Sets]' carrier universe.  Written out, the records keep
 all five apart -- see the UNIVERSES paragraph in the header. 

 --------
 在顶层使用显式宇宙绑定器声明，而不是在下面的部分中：使用未标注的 [Context {B : Category}] 时，展开器会最小化，识别 B 的 hom 和 proof 宇宙与彼此以及与 [Sets] 的载体宇宙。完整写出时，记录会把五个宇宙全部区分开——见标题中的 UNIVERSES 段落。
*)

Record PointwiseMonoid@{bo bh bp o so} {B : Category@{bo bh bp}}
  (T : B ⟶ Sets@{o so}) : Type := {
  pw_unit : ∀ b, carrier (T b);
  pw_mul  : ∀ b, carrier (T b) → carrier (T b) → carrier (T b);

  pw_mul_respects : ∀ b, Proper (equiv ==> equiv ==> equiv) (pw_mul b);

  pw_assoc : ∀ b u v w,
    pw_mul b (pw_mul b u v) w ≈ pw_mul b u (pw_mul b v w);
  pw_unit_l : ∀ b u, pw_mul b (pw_unit b) u ≈ u;
  pw_unit_r : ∀ b u, pw_mul b u (pw_unit b) ≈ u;

  pw_map_unit : ∀ x y (f : x ~{B}~> y), fmap[T] f (pw_unit x) ≈ pw_unit y;
  pw_map_mul : ∀ x y (f : x ~{B}~> y) u v,
    fmap[T] f (pw_mul x u v) ≈ pw_mul y (fmap[T] f u) (fmap[T] f v)
}.

Record PointwiseGroup@{bo bh bp o so} {B : Category@{bo bh bp}}
  (T : B ⟶ Sets@{o so}) : Type := {
  pg_monoid :> PointwiseMonoid@{bo bh bp o so} T;

  pg_inv : ∀ b, carrier (T b) → carrier (T b);
  pg_inv_respects : ∀ b, Proper (equiv ==> equiv) (pg_inv b);

  pg_inv_l : ∀ b u,
    pw_mul _ pg_monoid b (pg_inv b u) u ≈ pw_unit _ pg_monoid b;
  pg_inv_r : ∀ b u,
    pw_mul _ pg_monoid b u (pg_inv b u) ≈ pw_unit _ pg_monoid b;

  pg_map_inv : ∀ x y (f : x ~{B}~> y) u,
    fmap[T] f (pg_inv x u) ≈ pg_inv y (fmap[T] f u)
}.

Arguments pw_unit {B T}.
Arguments pw_mul {B T}.
Arguments pw_mul_respects {B T}.
Arguments pw_assoc {B T}.
Arguments pw_unit_l {B T}.
Arguments pw_unit_r {B T}.
Arguments pw_map_unit {B T}.
Arguments pw_map_mul {B T}.
Arguments pg_monoid {B T}.
Arguments pg_inv {B T}.
Arguments pg_inv_respects {B T}.
Arguments pg_inv_l {B T}.
Arguments pg_inv_r {B T}.
Arguments pg_map_inv {B T}.

#[export] Existing Instance pw_mul_respects.
#[export] Existing Instance pg_inv_respects.

Section Pointwise.

Context {B : Category}.
Context (T : B ⟶ Sets).

Lemma T_fmap_id (b : B) (u : carrier (T b)) : fmap[T] (id[b]) u ≈ u.
Proof. exact (@fmap_id _ _ T b u). Qed.

(* ------------------------------------------------------------------ *)
(* Forward: a monoid/group object has pointwise structure / 前言：一个幺半群/群对象具有逐点结构 *)
(* ------------------------------------------------------------------ *)

Section Forward.

Context (M : @MonoidObject ([B, Sets]) CC_Monoidal T).

Definition fun_unit (b : B) : carrier (T b) :=
  transform[@mempty _ _ _ M] b ttt.

Definition fun_mul (b : B) (u v : carrier (T b)) : carrier (T b) :=
  transform[@mappend _ _ _ M] b (u, v).

#[local] Instance fun_mul_respects (b : B) :
  Proper (equiv ==> equiv ==> equiv) (fun_mul b).
Proof.
  intros u u' Hu v v' Hv.
  unfold fun_mul.
  apply proper_morphism; split; assumption.
Qed.

(*
 The five diagrammatic laws, read off at a point.  Each is the class
 field applied to an explicit element and is accepted by CONVERSION --
 no tactic, no transport -- so the elementary statements below are the
 diagrammatic ones.  The residual [fmap[T] id] is the component of the
 identity natural transformation of [[B, Sets]], which is [fmap[F] id]
 and not [id]; it is discharged by [T_fmap_id]. 

 --------
 五个图示定律，在一点上读取。每一个都是类域应用于一个明确元素，并被 CONVERSION 接受——没有策略，没有传输——因此下面的基本语句是图示的。剩余的 [fmap[T] id] 是 [[B, Sets] 的身份自然变换的分量，它是 [fmap[F] id] 而不是 [id]；它由 [T_fmap_id] 注销。
*)

Definition fun_unit_l_raw (b : B) (u : carrier (T b)) :
  fun_mul b (fun_unit b) (fmap[T] (id[b]) u) ≈ u :=
  @mempty_left ([B, Sets]) CC_Monoidal T M b (ttt, u).

Definition fun_unit_r_raw (b : B) (u : carrier (T b)) :
  fun_mul b (fmap[T] (id[b]) u) (fun_unit b) ≈ u :=
  @mempty_right ([B, Sets]) CC_Monoidal T M b (u, ttt).

Definition fun_assoc_raw (b : B) (u v w : carrier (T b)) :
  fun_mul b (fun_mul b u v) (fmap[T] (id[b]) w)
    ≈ fun_mul b (fmap[T] (id[b]) u) (fun_mul b v w) :=
  @mappend_assoc ([B, Sets]) CC_Monoidal T M b ((u, v), w).

Lemma fun_unit_l (b : B) (u : carrier (T b)) :
  fun_mul b (fun_unit b) u ≈ u.
Proof.
  transitivity (fun_mul b (fun_unit b) (fmap[T] (id[b]) u)).
  - now rewrite T_fmap_id.
  - exact (fun_unit_l_raw b u).
Qed.

Lemma fun_unit_r (b : B) (u : carrier (T b)) :
  fun_mul b u (fun_unit b) ≈ u.
Proof.
  transitivity (fun_mul b (fmap[T] (id[b]) u) (fun_unit b)).
  - now rewrite T_fmap_id.
  - exact (fun_unit_r_raw b u).
Qed.

Lemma fun_assoc (b : B) (u v w : carrier (T b)) :
  fun_mul b (fun_mul b u v) w ≈ fun_mul b u (fun_mul b v w).
Proof.
  transitivity (fun_mul b (fun_mul b u v) (fmap[T] (id[b]) w)).
  - now rewrite T_fmap_id.
  - rewrite fun_assoc_raw.
    now rewrite T_fmap_id.
Qed.

Lemma fun_map_unit (x y : B) (f : x ~{B}~> y) :
  fmap[T] f (fun_unit x) ≈ fun_unit y.
Proof.
  unfold fun_unit.
  exact (@naturality _ _ _ _ (@mempty _ _ _ M) x y f ttt).
Qed.

Lemma fun_map_mul (x y : B) (f : x ~{B}~> y) (u v : carrier (T x)) :
  fmap[T] f (fun_mul x u v) ≈ fun_mul y (fmap[T] f u) (fmap[T] f v).
Proof.
  unfold fun_mul.
  exact (@naturality _ _ _ _ (@mappend _ _ _ M) x y f (u, v)).
Qed.

Definition monoid_object_pointwise : PointwiseMonoid T :=
  {| pw_unit         := fun_unit
   ; pw_mul          := fun_mul
   ; pw_mul_respects := fun_mul_respects
   ; pw_assoc        := fun_assoc
   ; pw_unit_l       := fun_unit_l
   ; pw_unit_r       := fun_unit_r
   ; pw_map_unit     := fun_map_unit
   ; pw_map_mul      := fun_map_mul |}.

End Forward.

Section ForwardGroup.

Context (G : @GroupObject ([B, Sets]) CC_CartesianMonoidal T).

Definition fun_gmonoid : @MonoidObject ([B, Sets]) CC_Monoidal T :=
  @groupobject_is_monoid ([B, Sets]) CC_CartesianMonoidal T G.

Definition fun_inv (b : B) (u : carrier (T b)) : carrier (T b) :=
  transform[@Category.Structure.Group.inverse _ _ _ G] b u.

#[local] Instance fun_inv_respects (b : B) :
  Proper (equiv ==> equiv) (fun_inv b).
Proof. intros u u' Hu; unfold fun_inv; now apply proper_morphism. Qed.

Definition fun_inv_l_raw (b : B) (u : carrier (T b)) :
  fun_mul fun_gmonoid b (fun_inv b (fmap[T] (id[b]) u))
          (fmap[T] (id[b]) (fmap[T] (id[b]) u))
    ≈ fun_unit fun_gmonoid b :=
  @left_inverse ([B, Sets]) CC_CartesianMonoidal T G b u.

Definition fun_inv_r_raw (b : B) (u : carrier (T b)) :
  fun_mul fun_gmonoid b (fmap[T] (id[b]) (fmap[T] (id[b]) u))
          (fun_inv b (fmap[T] (id[b]) u))
    ≈ fun_unit fun_gmonoid b :=
  @right_inverse ([B, Sets]) CC_CartesianMonoidal T G b u.

Lemma fun_inv_l (b : B) (u : carrier (T b)) :
  fun_mul fun_gmonoid b (fun_inv b u) u ≈ fun_unit fun_gmonoid b.
Proof.
  transitivity (fun_mul fun_gmonoid b (fun_inv b (fmap[T] (id[b]) u))
                  (fmap[T] (id[b]) (fmap[T] (id[b]) u))).
  - unfold fun_mul, fun_inv.
    apply proper_morphism; split; simpl.
    + apply proper_morphism; symmetry; apply T_fmap_id.
    + symmetry; transitivity (fmap[T] (id[b]) u); apply T_fmap_id.
  - exact (fun_inv_l_raw b u).
Qed.

Lemma fun_inv_r (b : B) (u : carrier (T b)) :
  fun_mul fun_gmonoid b u (fun_inv b u) ≈ fun_unit fun_gmonoid b.
Proof.
  transitivity (fun_mul fun_gmonoid b (fmap[T] (id[b]) (fmap[T] (id[b]) u))
                  (fun_inv b (fmap[T] (id[b]) u))).
  - unfold fun_mul, fun_inv.
    apply proper_morphism; split; simpl.
    + symmetry; transitivity (fmap[T] (id[b]) u); apply T_fmap_id.
    + apply proper_morphism; symmetry; apply T_fmap_id.
  - exact (fun_inv_r_raw b u).
Qed.

Lemma fun_map_inv (x y : B) (f : x ~{B}~> y) (u : carrier (T x)) :
  fmap[T] f (fun_inv x u) ≈ fun_inv y (fmap[T] f u).
Proof.
  unfold fun_inv.
  exact (@naturality _ _ _ _
           (@Category.Structure.Group.inverse _ _ _ G) x y f u).
Qed.

Definition group_object_pointwise : PointwiseGroup T :=
  {| pg_monoid       := monoid_object_pointwise fun_gmonoid
   ; pg_inv          := fun_inv
   ; pg_inv_respects := fun_inv_respects
   ; pg_inv_l        := fun_inv_l
   ; pg_inv_r        := fun_inv_r
   ; pg_map_inv      := fun_map_inv |}.

End ForwardGroup.


(* ------------------------------------------------------------------ *)
(* Backward: pointwise structure assembles a monoid/group object / 反向：逐点结构组装一个幺半群/群对象 *)
(* ------------------------------------------------------------------ *)

Section Backward.

Context (P : PointwiseMonoid T).


Program Definition pw_unit_nt : (1 : [B, Sets]) ~{[B, Sets]}~> T := {|
  transform := fun b => {| morphism := fun _ => pw_unit P b |}
|}.
Next Obligation. now apply pw_map_unit. Qed.
Next Obligation. symmetry; now apply pw_map_unit. Qed.

Program Definition pw_mul_nt :
  @product_obj ([B, Sets]) _ T T ~{[B, Sets]}~> T := {|
  transform := fun b => {| morphism := fun p => pw_mul P b (fst p) (snd p) |}
|}.
Next Obligation.
  intros p q [Hl Hr]; simpl in *; now rewrite Hl, Hr.
Qed.
Next Obligation. now apply pw_map_mul. Qed.
Next Obligation. symmetry; now apply pw_map_mul. Qed.

Program Definition pointwise_MonoidObject :
  @MonoidObject ([B, Sets]) CC_Monoidal T := {|
  mempty  := pw_unit_nt;
  mappend := pw_mul_nt
|}.
Next Obligation. rewrite T_fmap_id; apply pw_unit_l. Qed.
Next Obligation. rewrite T_fmap_id; apply pw_unit_r. Qed.
Next Obligation. rewrite !T_fmap_id; apply pw_assoc. Qed.

End Backward.


Section BackwardGroup.

Context (P : PointwiseGroup T).


Program Definition pg_inv_nt : T ~{[B, Sets]}~> T := {|
  transform := fun b => {| morphism := pg_inv P b |}
|}.
Next Obligation. now apply pg_map_inv. Qed.
Next Obligation. symmetry; now apply pg_map_inv. Qed.

Program Definition pointwise_GroupObject :
  @GroupObject ([B, Sets]) CC_CartesianMonoidal T := {|
  groupobject_is_monoid := pointwise_MonoidObject (pg_monoid P);
  Category.Structure.Group.inverse := pg_inv_nt
|}.
Next Obligation. rewrite !T_fmap_id; apply pg_inv_l. Qed.
Next Obligation. rewrite !T_fmap_id; apply pg_inv_r. Qed.

End BackwardGroup.


(* ------------------------------------------------------------------ *)
(* The headline biconditionals / 标题双条件句 *)
(* ------------------------------------------------------------------ *)

Theorem monoid_object_iff_pointwise :
  @MonoidObject ([B, Sets]) CC_Monoidal T ↔ PointwiseMonoid T.
Proof.
  split.
  - exact monoid_object_pointwise.
  - exact pointwise_MonoidObject.
Defined.

Theorem group_object_iff_pointwise :
  @GroupObject ([B, Sets]) CC_CartesianMonoidal T ↔ PointwiseGroup T.
Proof.
  split.
  - exact group_object_pointwise.
  - exact pointwise_GroupObject.
Defined.

(* ------------------------------------------------------------------ *)
(* Strength: what holds on the nose / 力量：握住鼻子的东西 *)
(* ------------------------------------------------------------------ *)

(* The extracted operations ARE the components of the structure maps. / 提取的操作就是结构图的组成部分。 *)
Example pointwise_mul_is_component
  (M : @MonoidObject ([B, Sets]) CC_Monoidal T) (b : B)
  (u v : carrier (T b)) :
  pw_mul (monoid_object_pointwise M) b u v
    = transform[@mappend _ _ _ M] b (u, v) := eq_refl.

Example pointwise_unit_is_component
  (M : @MonoidObject ([B, Sets]) CC_Monoidal T) (b : B) :
  pw_unit (monoid_object_pointwise M) b
    = transform[@mempty _ _ _ M] b ttt := eq_refl.

Example pointwise_inv_is_component
  (G : @GroupObject ([B, Sets]) CC_CartesianMonoidal T) (b : B)
  (u : carrier (T b)) :
  pg_inv (group_object_pointwise G) b u
    = transform[@Category.Structure.Group.inverse _ _ _ G] b u := eq_refl.

(*
 Round trip, pointwise datum -> object -> pointwise datum: the three
 operations return ON THE NOSE. 

 --------
 往返，逐点数据 -> 对象 -> 逐点数据：这三次操作精确返回。
*)
Example roundtrip_unit (P : PointwiseGroup T) (b : B) :
  pw_unit (monoid_object_pointwise (pointwise_MonoidObject P)) b
    = pw_unit P b := eq_refl.

Example roundtrip_mul (P : PointwiseGroup T) (b : B) (u v : carrier (T b)) :
  pw_mul (monoid_object_pointwise (pointwise_MonoidObject P)) b u v
    = pw_mul P b u v := eq_refl.

Example roundtrip_inv (P : PointwiseGroup T) (b : B) (u : carrier (T b)) :
  pg_inv (group_object_pointwise (pointwise_GroupObject P)) b u
    = pg_inv P b u := eq_refl.

(*
 Round trip, object -> pointwise datum -> object: the structure maps
 agree on VALUES, on the nose ... 

 --------
 往返，对象 -> 点状数据 -> 对象：结构映射在数值上完全一致……
*)
Example roundtrip_obj_unit
  (G : @GroupObject ([B, Sets]) CC_CartesianMonoidal T) (b : B) :
  transform[@mempty _ _ _
    (pointwise_MonoidObject (group_object_pointwise G))] b ttt
    = transform[@mempty _ _ _ (fun_gmonoid G)] b ttt := eq_refl.

Example roundtrip_obj_mul
  (G : @GroupObject ([B, Sets]) CC_CartesianMonoidal T) (b : B)
  (u v : carrier (T b)) :
  transform[@mappend _ _ _
    (pointwise_MonoidObject (group_object_pointwise G))] b (u, v)
    = transform[@mappend _ _ _ (fun_gmonoid G)] b (u, v) := eq_refl.

(* ------------------------------------------------------------------ *)
(* The ordinary-group reading: a lift through Grp_Forget / 普通群的阅读：通过 Grp_Forget 的提升 *)
(* ------------------------------------------------------------------ *)

(*
 The monoid half of the ordinary reading.  Construction/Deloop.v's
 [MonObject] is a bare setoid monoid with no category attached, so this
 is an object-level statement only -- there is no [Mon]-valued functor
 to mirror [PointwiseGrpFunctor]; see NOT DELIVERED. 

 --------
 常规阅读的幺半群部分。Construction/Deloop.v 的 [MonObject] 是一个没有附加范畴的裸集等价幺半群，因此这只是一个对象层面的陈述——没有 [Mon] 值的函子来映射 [PointwiseGrpFunctor]；见未交付。
*)
Program Definition pointwise_MonObject (P : PointwiseMonoid T) (b : B) :
  MonObject := {|
  mon_setoid := T b;
  mon_unit   := pw_unit P b;
  mon_op     := pw_mul P b
|}.
Next Obligation. symmetry; now apply pw_assoc. Qed.
Next Obligation. now apply pw_unit_l. Qed.
Next Obligation. now apply pw_unit_r. Qed.

Example pointwise_MonObject_carrier (P : PointwiseMonoid T) (b : B) :
  mon_setoid (pointwise_MonObject P b) = T b := eq_refl.

(*
 RECORDED STRENGTH CHANGE.  Since the PR “algebraic carriers are sets”
 (2026-09-17) an [Instance/Grp.v] group carries [grp_prop], so turning a
 PRESHEAF of pointwise groups into a functor into [Grp] asks that the
 presheaf take its values among the propositional setoids.  [PT] is that
 hypothesis, and it is threaded through [pointwise_GrpHom],
 [PointwiseGrpFunctor] and the two [_forgets_] Examples below.  The round
 trip discharges it for free: [grp_functor_PointwiseGroup] starts from a
 functor into [Grp], whose values carry [grp_prop] as a field, so
 [PT := fun b => grp_prop (F b)] -- which is the cleanest evidence that
 this is the right hypothesis and not an artefact. 

 --------
 记录的强度变化。自从PR “代数载体是集合” (2026-09-17) 以来，一个[Instance/Grp.v] 群携带 [grp_prop]，因此将逐点群的 PRESHEAF 转变为指向 [Grp] 的函子要求该 presheaf 的取值属于命题集合类。[PT] 是该假设，并且它贯穿于 [pointwise_GrpHom]、[PointwiseGrpFunctor] 以及下面两个 [_forgets_] 示例中。往返过程免费地消除了它：[grp_functor_PointwiseGroup] 从指向 [Grp] 的函子开始，其值携带 [grp_prop] 作为域，因此 [PT := fun b => grp_prop (F b)] —— 这是最清楚的证据表明这是正确的假设，而不是一种人为产物。
*)
Context (PT : forall b : B, PropEquiv (is_setoid (T b))).

Program Definition pointwise_GrpObject (P : PointwiseGroup T) (b : B) :
  GrpObject := {|
  grp_setoid := T b;
  grp_unit   := pw_unit P b;
  grp_mul    := pw_mul P b;
  grp_inv    := pg_inv P b;
  grp_prop   := PT b
|}.
Next Obligation. now apply pw_assoc. Qed.
Next Obligation. now apply pw_unit_l. Qed.
Next Obligation. now apply pg_inv_l. Qed.

Example pointwise_GrpObject_carrier (P : PointwiseGroup T) (b : B) :
  grp_setoid (pointwise_GrpObject P b) = T b := eq_refl.

Program Definition pointwise_GrpHom (P : PointwiseGroup T) {x y : B}
  (f : x ~{B}~> y) :
  GrpHom (pointwise_GrpObject P x) (pointwise_GrpObject P y) := {|
  grp_map := fmap[T] f
|}.
Next Obligation. now apply pw_map_unit. Qed.
Next Obligation. now apply pw_map_mul. Qed.

Program Definition PointwiseGrpFunctor (P : PointwiseGroup T) : B ⟶ Grp := {|
  fobj := pointwise_GrpObject P;
  fmap := fun x y f => pointwise_GrpHom P f
|}.
Next Obligation.
  intros f g Hfg a; simpl.
  exact (@fmap_respects _ _ T x y f g Hfg a).
Qed.
Next Obligation. now apply T_fmap_id. Qed.
Next Obligation. exact (@fmap_comp _ _ T x y z f g a). Qed.

Example PointwiseGrpFunctor_forgets_obj (P : PointwiseGroup T) (b : B) :
  fobj[Grp_Forget ◯ PointwiseGrpFunctor P] b = fobj[T] b := eq_refl.

Example PointwiseGrpFunctor_forgets_map (P : PointwiseGroup T) {x y : B}
  (f : x ~{B}~> y) :
  fmap[Grp_Forget ◯ PointwiseGrpFunctor P] f = fmap[T] f := eq_refl.

(* ------------------------------------------------------------------ *)
(* Strict attempts REFUTED, each beside a positive control / 严格的尝试被驳斥，每个都在阳性对照旁边 *)
(* ------------------------------------------------------------------ *)

(*
 (1) The lift is NOT a strict lift: the two functor records are not
 Leibniz-equal, because [Grp_Forget ◯ PointwiseGrpFunctor P] rebuilds
 [fmap_respects], [fmap_id] and [fmap_comp] as its own opaque proofs.
 Both ACTIONS do agree on the nose -- the two Examples just above are
 the controls -- so what is refuted is record equality and nothing
 about the actions. 

 --------
 (1) 提升不是严格提升：两个函子记录不完全相同，因为 [Grp_Forget ◯ PointwiseGrpFunctor P] 重建了 [fmap_respects]、[fmap_id] 和 [fmap_comp] 作为它自己的不透明证明。两者的 ACTIONS 在本质上是一致的——上面的两个例子只是参考——所以被驳斥的是记录相等性，而不是关于 actions 的任何内容。
*)
Fail Example lift_is_strict (P : PointwiseGroup T) :
  Grp_Forget ◯ PointwiseGrpFunctor P = T := eq_refl.

(*
 (2) The round trip on the pointwise datum does not close at the whole
 record either: [pw_mul_respects] is rebuilt.  Controls:
 [roundtrip_unit], [roundtrip_mul] and [roundtrip_inv] above, which do
 close on the nose. 

 --------
 (2) 对逐点数据的往返也无法在整个记录上闭合：重建了 [pw_mul_respects]。控制：上面的 [roundtrip_unit]、[roundtrip_mul] 和 [roundtrip_inv]，则可以精确闭合。
*)
Fail Example roundtrip_whole (P : PointwiseGroup T) :
  monoid_object_pointwise (pointwise_MonoidObject P) = pg_monoid P
    := eq_refl.

(*
 (3) Nor does the round trip on the object, for the same reason one
 level up: the naturality fields of the rebuilt transformations are
 this file's own opaque proofs.  Controls: [roundtrip_obj_unit] and
 [roundtrip_obj_mul] above, which close on the values. 

 --------
 (3) 物体的往返也不行，原因与上一层相同：重建变换的自然性场是此文件自身的不透明证明。 控制：上面的 [roundtrip_obj_unit] 和 [roundtrip_obj_mul]，它们在这些值上闭合。
*)
Fail Example roundtrip_obj_whole
  (G : @GroupObject ([B, Sets]) CC_CartesianMonoidal T) :
  pointwise_GroupObject (group_object_pointwise G) = G := eq_refl.

(* Positive control for the instrument itself: a true [eq_refl] of the same shape at the same types is accepted. / 仪器本身的阳性对照：接受与相同类型相同形状的真实 [eq_refl]。 *)
Example probe_instrument_control
  (G : @GroupObject ([B, Sets]) CC_CartesianMonoidal T) : G = G := eq_refl.

End Pointwise.

(* ------------------------------------------------------------------ *)
(* Every functor into Grp is a group object on its underlying functor / 每个到 Grp 的函子都是其底层函子上的群对象 *)
(* ------------------------------------------------------------------ *)

Section FromGrp.

Context {B : Category}.
Context (F : B ⟶ Grp).

Program Definition grp_functor_PointwiseMonoid :
  PointwiseMonoid (Grp_Forget ◯ F) := {|
  pw_unit := fun b => grp_unit (F b);
  pw_mul  := fun b => grp_mul (F b)
|}.
Next Obligation. now apply grp_mul_assoc. Qed.
Next Obligation. now apply grp_mul_unit_l. Qed.
Next Obligation. now apply grp_mul_unit_r. Qed.
Next Obligation. now apply grp_map_unit. Qed.
Next Obligation. now apply grp_map_mul. Qed.

Program Definition grp_functor_PointwiseGroup :
  PointwiseGroup (Grp_Forget ◯ F) := {|
  pg_monoid := grp_functor_PointwiseMonoid;
  pg_inv    := fun b => grp_inv (F b)
|}.
Next Obligation. now apply grp_mul_inv_l. Qed.
Next Obligation. now apply grp_mul_inv_r. Qed.
Next Obligation. now apply grp_map_inv. Qed.

Definition grp_functor_GroupObject :
  @GroupObject ([B, Sets]) CC_CartesianMonoidal (Grp_Forget ◯ F) :=
  pointwise_GroupObject (Grp_Forget ◯ F) grp_functor_PointwiseGroup.

End FromGrp.

(* ------------------------------------------------------------------ *)
(* Universe boundary, guarded / 宇宙边界，受守护 *)
(* ------------------------------------------------------------------ *)

(*
 The two records tolerate B's hom universe STRICTLY BELOW both B's
 proof universe and [Sets]' carrier universe; the functor category does
 not.  So the identification [bh = bp = o] visible in the BINDER of
 every headline constant is [Fun]'s doing and not the records'.  The
 three [Check]s are the positive controls: they must succeed at exactly
 the levels at which the [Fail] fires. 

 --------
 这两个记录严格位于 B 的同态宇宙之下，同时低于 B 的证明宇宙和 [Sets] 的承载宇宙；函子范畴则不如此。因此，每个标题常量的 BINDER 中可见的 [bh = bp = o] 是 [Fun] 的作用，而不是记录的作用。这三个 [Check] 是阳性对照：它们必须在 [Fail] 触发的确切水平上成功。
*)

Section UniverseBoundary.

Universes ubo ubh ubp uo uso.
Constraint ubh < ubp.
(* Deliberately ONLY this constraint: with [ubh < uo] also declared the section could not show that the first half suffices on its own. / 故意仅此约束：与 [ubh < uo] 一起声明，该部分无法显示前半部分单独足够。 *)

Context (Bu : Category@{ubo ubh ubp}).
Context (Tu : Bu ⟶ Sets@{uo uso}).

Check Bu.
Check Tu.
Check (PointwiseGroup Tu).

(*
 THE DISCRIMINATING CONTROL for the “two independent causes” claim:
 a functor INTO [Grp] is formable at these separated levels, so the
 identification carried by [PointwiseGrpFunctor] and its siblings --
 which mention no functor category -- cannot be [Fun]'s doing.  An
 earlier revision asserted this control in the header without
 carrying it. 

 --------
 针对“两个独立原因”主张的区分控制：
 在这些分离的层次上可以形成一个函子 INTO [Grp]，因此由 [PointwiseGrpFunctor] 及其同类所携带的识别——
 它们未提及任何函子类别——不能是 [Fun] 的行为。早先的修订在头部断言了这种控制，但并未具体实施。
*)
Check (Bu ⟶ Grp).

Fail Check ([Bu, Sets@{uo uso}] : Category).

End UniverseBoundary.

(*
 The two halves of [Fun]'s identification, separated.  Above, the
 rejection fires already at [ubh < ubp]: [Fun] forces the SOURCE
 category's hom and proof universes to agree.  Here the source has them
 equal by construction and only [vbh < vo] is declared, and the functor
 category is rejected again: [Fun] additionally forces the source's hom
 universe to be the target's.  So neither half alone accounts for it. 

 --------
 [Fun] 的身份的两半被分开了。上面，拒绝已经在 [ubh < ubp] 触发：[Fun] 强制 SOURCE 类别的 hom 和证明宇宙一致。这里源通过构造让它们相等，并且只有 [vbh < vo] 被声明，而函子类别再次被拒绝：[Fun] 另外强制源的 hom 宇宙与目标的相同。因此，单靠任何一半都无法解释它。
*)

Section UniverseBoundary2.

Universes vbo vbh vo vso.
Constraint vbh < vo.

Context (Bv : Category@{vbo vbh vbh}).
Context (Tv : Bv ⟶ Sets@{vo vso}).

Check Bv.
Check (PointwiseGroup Tv).

Fail Check ([Bv, Sets@{vo vso}] : Category).

End UniverseBoundary2.

(* ------------------------------------------------------------------ *)
(* Cross-link: Structure/Group/Representable.v's presheaf group / 交叉链接：Structure/Group/Representable.v 的预层群 *)
(* ------------------------------------------------------------------ *)

(*
 Issue #341's [RepresentablyGroup e] is [@GroupObject ([C^op, Sets])
 CC_CartesianMonoidal (RepPresheaf e)], i.e. THIS file's headline at
 [B := C^op] and [T := RepPresheaf e].  Both corollaries are [:=] with
 no tactic and no transport, which is the precise sense in which the
 representable case is an instance of the general one. 

 --------
 问题 #341 的 [RepresentablyGroup e] 是 [@GroupObject ([C^op, Sets] )
 CC_CartesianMonoidal (RepPresheaf e)]，即本文件在 [B := C^op] 和 [T := RepPresheaf e] 的标题。两个推论都是 [:=]，没有任何策略和传输，这正是在表示情况是一般情况一个实例的确切意义。
*)

Definition representably_monoid_iff_pointwise {C : Category} (e : C) :
  RepresentablyMonoid e ↔ PointwiseMonoid (RepPresheaf e) :=
  monoid_object_iff_pointwise (RepPresheaf e).

Definition representably_group_iff_pointwise {C : Category} (e : C) :
  RepresentablyGroup e ↔ PointwiseGroup (RepPresheaf e) :=
  group_object_iff_pointwise (RepPresheaf e).

(* ------------------------------------------------------------------ *)
(* Non-vacuity / 非空性 *)
(* ------------------------------------------------------------------ *)

Section Witness.

(*
 The trivial endomorphism of Z/2: a genuine group homomorphism that is
 not the identity.  It costs no obligations -- the constant-at-the-unit
 map preserves everything. 

 --------
 Z/2 的平凡自同态：一个真正的群同态，但不是恒等映射。它不带来任何义务——常值于单位元的映射保留一切。
*)
Program Definition Z2_triv : Z2 ~{Grp}~> Z2 := {|
  grp_map := {| morphism := fun _ => grp_unit Z2 |}
|}.

(*
 The witness index category is [Grp] itself and the witness functor is
 the identity, so the group object below is the underlying-set functor
 of [Grp] with its evident pointwise structure.  No new functor into
 [Grp] is built. 

 --------
 证人索引类别本身是 [Grp]，证人函子是恒等函子，所以下面的群对象是 [Grp] 的基础集合函子，带有其显而易见的逐点结构。没有构建新的进入 [Grp] 的函子。
*)
Definition Und : Grp ⟶ Sets := Grp_Forget ◯ Id[Grp].

Definition Und_GroupObject :
  @GroupObject ([Grp, Sets]) CC_CartesianMonoidal Und :=
  grp_functor_GroupObject Id[Grp].

Definition Und_Pointwise : PointwiseGroup Und :=
  group_object_pointwise Und Und_GroupObject.

(* The recovered pointwise operations COMPUTE, through both passages. / 恢复的逐点操作通过两个通道进行计算。 *)
Example und_unit_computes : pw_unit Und_Pointwise Z2 = false := eq_refl.

Example und_mul_computes :
  pw_mul Und_Pointwise Z2 true true = false := eq_refl.

Example und_mul_computes' :
  pw_mul Und_Pointwise Z2 true false = true := eq_refl.

Example und_inv_computes :
  pg_inv Und_Pointwise Z2 true = true := eq_refl.

(* The group at [Z2] is nontrivial: it has two distinct elements. / [Z2] 的群是非平凡的：它有两个不同的元素。 *)
Lemma und_nontrivial : (@equiv _ (Und Z2) true false) → False.
Proof. simpl; discriminate. Qed.

(*
 The arrow action is not an identity at [Z2_triv], so the two
 homomorphism clauses of [PointwiseMonoid] are not vacuous: they are
 applied to a map that genuinely moves an element. 

 --------
 箭头作用在 [Z2_triv] 上不是恒等作用，因此 [PointwiseMonoid] 的两个同态条款并非空洞：它们被应用于一个真正移动元素的映射上。
*)
Example und_fmap_computes : fmap[Und] Z2_triv true = false := eq_refl.

Lemma und_fmap_not_id :
  (@equiv _ (Und Z2) (fmap[Und] Z2_triv true) true) → False.
Proof. simpl; discriminate. Qed.

(* And the clause itself, at that arrow, is a true statement with two sides that are not syntactically equal. / 而该从句本身，在那个箭头处，是一个真正的陈述，具有两个在语法上不相等的部分。 *)
Example und_map_mul_at_triv :
  fmap[Und] Z2_triv (pw_mul Und_Pointwise Z2 true false)
    = pw_mul Und_Pointwise Z2
        (fmap[Und] Z2_triv true) (fmap[Und] Z2_triv false) := eq_refl.

End Witness.
