Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Image.
Require Import Category.Instance.Sets.Cocartesian.
Require Import Category.Instance.Sets.Products.

Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(* * * The subobject lattice of a setoid: bottom, images, wide pullbacks, and Fong and Spivak's increasing family / * * 集合等价类的子对象格：底部、像、广义拉回，以及 Fong 和 Spivak 的递增族 *)

(*
 nLab:      https://ncatlab.org/nlab/show/subobject
 nLab:      https://ncatlab.org/nlab/show/image
 nLab:      https://ncatlab.org/nlab/show/wide+pullback
 Wikipedia: https://en.wikipedia.org/wiki/Image_(category_theory)
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.
 (GTM 5), §V.7 Definition 2, printed p. 126 (PDF p. 135)
 Book:      Riehl, "Category Theory in Context", 2nd ed., §4.7
 Definition 4.7.9, printed p. 177 (PDF p. 197)
 Book:      Fong and Spivak, "Seven Sketches in Compositionality",
 §1.2.1, printed p. 8 (PDF p. 20)

 Theory/Subobject/Lattice.v states the order theory of subobjects
 abstractly: [sub_top], [sub_bot], the two Riehl 4.7.9 characterizations
 [IsIntersection] and [IsUnion], the meet by chosen pullback, the wide
 intersection by wide pullback, and the join as the image of a copairing
 given an [ImageOf].  Every one of those constructions is CONDITIONAL on
 data the ambient category may or may not carry: a monic arrow out of the
 initial object, images, wide pullbacks, indexed coproducts.  This file
 supplies all four at [Sets] and then runs Fong and Spivak's worked
 example through them.  The companion Instance/FinSet/Subobject.v does
 the finite, COMPUTING half.

 ** WHAT IS DELIVERED, WITH GRADES

 (a) [Sets_zero_monic]: the unique arrow out of the empty setoid is
 monic, so [sub_bot] is available at every object of [Sets].  This is
 NOT routed through Structure/BiCCC/Strict.v's
 [Sets_initial_strict]; the direct argument is one line, because a
 competing pair of arrows INTO the empty setoid is already absurd on
 elements (the same observation that file's
 [Sets_initial_strict_empty] makes).

 (b) [Sets_HasImages]: Instance/Sets/Image.v's factorization, read as an
 [ImageOf].  Nothing is reproved -- the object is
 Instance/Sets/Image.v's [Sets_Image], the mono that file's
 [Sets_Image_mono], its monicity [Sets_Image_mono_monic], the
 factoring arrow [Sets_Image_epi] and the triangle
 [Sets_Image_comm].  The ONE new piece of mathematics is
 [im_least]: given a competing subobject w and a factorization
 g of f through it, the comparison arrow sends an image point to
 g of its STORED preimage.  That assignment is not obviously
 respectful -- two image points with one Y-component may carry
 DIFFERENT preimages, and their g-values need identifying -- and
 what identifies them is injectivity of [sub_mono w], the BACKWARD
 leg of Instance/Sets.v's [injectivity_is_monic] applied to
 [sub_is_monic w].  Instance/Powerset/Subobject.v spends
 monicity in exactly the same place, for the same reason, and its
 header says so in terms.

 (c) [Sets_HasWidePullbacks]: THE CLASS IS INHABITED HERE FOR THE FIRST
 TIME.  Structure/Pullback/Wide.v declares [HasWidePullbacks]
 and its own header records under NOT DELIVERED that it builds no
 instance for any concrete category; docs/INDEX.md's
 Structure/Pullback/Wide.v clause said "declared but UNINHABITED".
 Both statements were true at the parent commit; both are corrected
 in place, as corrections, in the commit that lands this file, and
 both are superseded by [Sets_HasWidePullbacks] below.  The apex is the
 setoid of coherent families,

 { a : ∀ i, carrier (A i) & ∀ i j, f i (a i) ≈ f j (a j) },

 compared pointwise at every index, which is the evident
 generalization of Instance/Sets/Products.v's [Sets_iprod_obj]
 by an equation; the projections evaluate at an index, the
 commutativity field IS the second component of a point, and the
 mediator tuples a competing family and carries its own agreement
 hypothesis as the second component.  Nothing needs the index to be
 inhabited, so the empty index is covered -- see the BOUNDARIES
 paragraph for what that does and does not mean.

 (d) The Seven Sketches unit law ∅ ∪ X ≅ X at the level of subobjects
 is Theory/Subobject/Lattice.v's [sub_join_via_bot]: GENERAL, in any
 category with a cocartesian structure, an initial object whose
 arrows out are monic, and an image of the relevant copairing.  It
 was first proved in this file while the two halves of the
 development were written in parallel, and was lifted into that file
 at integration.  [fs_join_bot_left_unit] instantiates it at [Sets]
 and the three-element subobject {1,2,3} of the naturals.

 (e) The Seven Sketches §1.2.1 worked case, at the STRONGEST available
 strength.  The ambient object is [Sets_nat], the discrete setoid on
 [nat] built by Instance/Sets/Products.v's [Sets_discrete]; the
 family is [fs_seg n], the subobject {k | 1 ≤ k ≤ n}, so that
 [fs_seg 0] is empty and the family increases.  Then

 [fs_union_is_positives] : fs_union ≈ fs_pos
 [fs_inter_is_empty]     : fs_inter ≈ fs_bot

 where [fs_union] is [sub_wide_join_via] at Instance/Sets/
 Products.v's [Sets_IsIndexedCoproduct] and this file's images,
 and [fs_inter] is [sub_wide_intersection] at index 0 and this
 file's wide pullbacks.  BOTH are ≈ on [SubObj Sets_nat] -- that is
 Theory/Subobject.v's setoid, an ISOMORPHISM OF DOMAINS COMMUTING
 WITH THE MONOS -- and NOT the weaker membership-equivalence that
 Instance/Powerset/Subobject.v's [subset_le_of_sub_le] would give
 through the Prop-valued subsets.  Neither statement is routed
 through the powerset bridge at all.  Both are assembled from mutual
 [sub_le] by Theory/Subobject.v's [sub_equiv_iff_mutual].

 ** WHERE EACH HALF OF THE UNION PROOF GETS ITS CONTENT

 The union is an image, so ONE half is free: [im_least] applied to
 [fs_pos] and the arrow sending a tagged element (j, a) of the indexed
 coproduct to its value, which is positive because a is.  The OTHER half
 is the one with content and it is where the family's being INCREASING
 is spent: a positive natural k must be exhibited INSIDE some member,
 and the member chosen is [fs_seg k] itself, at which k qualifies by
 [Nat.le_refl].  A family that did not exhaust the positives would
 simply not carry that arrow.

 The intersection is the dual situation with the content in the other
 half: [sub_bot_least] gives one direction for free, and the other is
 [seg_zero_empty] -- a point of the wide pullback has a component at
 EVERY index, in particular at 0, and a member of [fs_seg 0] carries
 1 ≤ k ≤ 0.  So the intersection is empty because ONE member is, which
 is exactly why the book's family has empty intersection.

 ** UNIVERSES, read from the constraint blocks

 Reproduce with [Set Printing Universes. About Sets_HasWidePullbacks.]
 and so on.

 Sets_HasWidePullbacks@{o so} : HasWidePullbacks@{o o so o} Sets@{o so}
 ( * o so |= o < so, o <= compose.u0/u1/u2, o <= Projections.u0/u1,
 o <= ID.u0 * )

 The INDEX universe of the class is instantiated at [o], the universe of
 the CARRIERS of objects of [Sets] -- the same place
 Instance/Sets/Products.v's header shows [Sets_HasIndexedProducts]
 putting it, and for the same reason: a coherent family over
 [I : Type@{u}] lands at [Type@{max(u,o)}], which is a carrier exactly
 when u ≤ o.  Indexing by [obj[Sets@{o so}]] at the SAME universe
 instance as the family is one level too high and is refused as a
 universe inconsistency -- the stable content is that [so <= o] cannot
 be enforced because [o < so]; the exact wording depends on how the
 statement is posed (a scratch [Definition] over [Sets_WidePullback]
 prints "Cannot enforce so <= o because o < so", an instantiation of
 the class reads "cannot ensure that Type@{so} is a subtype of
 Type@{o}"), so neither sentence is quoted as THE text.  The same
 definition with its universes left free elaborates at a DIFFERENT
 instance (the index category one level below the family's), which is
 the careful form Instance/Sets/Products.v records for its own
 class, and the refusal should not be read as more.  [Sets_HasImages]
 carries the same block plus [o <= projections.u0/u1],
 [so <= projections.u0/u1] and [o <= Logic_lemmas.equality.u0], which
 come from the sigma-type projections the image carrier is built from.

 The worked case is at [Set]: [About fs_union_is_positives] prints
 [fs_union_is_positives@{u} : equiv fs_union@{u Set} fs_pos@{u Set}]
 with block [Set < u, u <= projections.u0, u <= projections.u1], because
 [nat] and the segment carriers are in [Set].  That pin is a property of
 the EXAMPLE, not of (a)-(c): none of
 [Sets_zero_monic], [Sets_HasImages] or [Sets_HasWidePullbacks] mentions
 [Set] in binder or block.  One collapse IS inherited and is disclosed
 here rather than left to be found: every constant consuming [SubObj]
 binds [Category@{u u0 u0}], hom universe identified with proof
 universe, because Theory/Subobject.v's [SubObj] record itself does
 ([About SubObj] prints
 [∀ {C : Category@{u u0 u0}}, obj[C] → Type@{max(u,u0)}])
 and [sub_le]'s block carries [h = p]; Theory/Subobject/Lattice.v's
 header attributes it the same way.  Neither that file nor this one
 introduces it.

 ** BOUNDARIES, measured

 The union is ≈ the positive naturals and NOT equal to them on the
 nose: [sub_dom fs_union = pos_obj] is refused, "cannot unify", the
 image carrier being a sigma of a point with a chosen preimage rather
 than a sig of a proof.  The empty-index wide pullback is likewise
 terminal only up to ≅ -- Structure/Pullback/Wide.v's
 [wide_pullback_empty_terminal] -- and NOT convertible with the chosen
 terminal setoid: [Sets_wpull_obj] at [I := False] against
 [terminal_obj] is refused by conversion, its carrier being the setoid
 of empty families with a vacuous coherence proof rather than
 [poly_unit].  Both refusals are conversion refusals, not universe
 ones.

 ** TRANSPARENCY, measured by flipping

 [Sets_image_least_map], [Sets_ImageOf] and [Sets_WidePullback] MUST be
 [Defined]: each was flipped to [Qed] in turn and the file then stops,
 at the [ImageOf] record's [im_least] field, at [fs_pos_to_union] and at
 [fs_inter_to_bot] respectively -- the consumers read the underlying
 function, the image carrier and the wide-pullback carrier.
 [fs_inter_le_bot] compiles as [Qed] and is written [Defined] for
 uniformity, being [sub_le] data.

 ** WHAT IS NOT DELIVERED

 No lattice structure is REGISTERED: nothing below inhabits any order or
 lattice class at [SubObj x], for the reason Instance/Powerset/
 Subobject.v's header gives -- [sub_le] is [Type]-valued and a
 [relation] is not.  No [IsIntersection]/[IsUnion] witnesses are built
 here; the greatest-lower-bound and least-upper-bound properties belong
 to Theory/Subobject/Lattice.v and are the other delegate's half.  No
 distributivity, no complement, no Heyting structure, and no comparison
 with Instance/Sets/Powerset.v's Prop-valued subsets.  The binary
 [sub_meet] is not instantiated at [Sets] -- it wants [HasPullbacks
 Sets], which Instance/Sets/Pullback.v supplies as
 [Sets_HasPullbacks], but nothing below calls for it, and the FinSet
 companion is where the binary meet is exercised instead.  The
 right unit law X ∪ ∅ ≅ X is not stated -- only the left one is, since
 the book states only the left one.  Nothing is claimed about
 preservation of unions or intersections by any functor. 

 --------
 nLab:       https://ncatlab.org/nlab/show/subobject 
 nLab:       https://ncatlab.org/nlab/show/image 
 nLab:       https://ncatlab.org/nlab/show/wide+pullback 
 维基百科:  https://en.wikipedia.org/wiki/Image_(category_theory) 
 书籍:      Mac Lane, 《工作数学家的范畴论》, 第2版
 （GTM 5），§V.7 定义 2，印刷页 126（PDF 页 135）
 书籍:      Riehl, 《上下文中的范畴论》, 第2版, §4.7
 定义 4.7.9，印刷页 177（PDF 页 197）
 书籍:      Fong 和 Spivak, 《组合性的七个草图》,
 §1.2.1，印刷页 8（PDF 页 20）Theory/Subobject/Lattice.v 抽象地说明了子对象的序理论：[sub_top]、[sub_bot]，两个 Riehl 4.7.9 的刻画 [IsIntersection] 和 [IsUnion]，通过选定的拉回得到的交，通过广泛拉回得到的广交，以及在给定 [ImageOf] 的情况下通过共配对的像得到的并。每一个这些构造都依赖于环境范畴可能或可能不具备的数据：初始对象出的单射、像、广拉回、索引余积。该文件在 [Sets] 提供了所有四个，并且随后通过它们运行了 Fong 和 Spivak 的示例。配套的 Instance/FinSet/Subobject.v 处理有限、可计算的部分。

 ** 提供的内容及评分(a) [Sets_zero_monic]：从空等价类出发的唯一箭头是单射，因此在 [Sets] 的每个对象上都可以使用 [sub_bot]。这并不是通过 Structure/BiCCC/Strict.v 中的 [Sets_initial_strict] 进行的；直接的论证只有一行，因为指向空等价类的竞争箭头对已经在元素上是荒谬的（与文件的 [Sets_initial_strict_empty] 所做的观察相同）。(b) [Sets_HasImages]：Instance/Sets/Image.v的分解，可读作[ImageOf]。没有重新证明——这个对象是Instance/Sets/Image.v的[Sets_Image]，该文件的单射[Sets_Image_mono]，它的单性[Sets_Image_mono_monic]，分解箭头[Sets_Image_epi]以及三角形[Sets_Image_comm]。唯一的新数学内容是[im_least]：给定一个竞争子对象w以及通过它的f的分解g，比较箭头将图像点发送到其存储的原像的g值。那种赋值并不明显尊重——两个具有相同Y分量的图像点可能具有不同的原像，并且它们的g值需要被识别——而识别它们的是[sub_mono w]的单射性，即Instance/Sets.v的[injectivity_is_monic]的后向分支应用于[sub_is_monic w]。Instance/Powerset/Subobject.v 在完全相同的地方花费了单调性，原因相同，其头文件也以术语说明了这一点。

 (c)  [Sets_HasWidePullbacks]：该类在此首次被实例化。Structure/Pullback/Wide.v 声明了 [HasWidePullbacks]，其头文件在“NOT DELIVERED”下记录它并未为任何具体范畴构建实例；docs/INDEX.md 的 Structure/Pullback/Wide.v 条目写着“已声明但未实例化”。这两个说法在父提交时都是正确的；在提交此文件的修改中，这两点都已就地更正，并且都被下面的 [Sets_HasWidePullbacks] 取代。顶点是相干族的集合同构，

 { a : ∀ i, carrier (A i) & ∀ i j, f i (a i) ≈ f j (a j) }在每个索引上逐点比较，这是对 Instance/Sets/Products.v 中 [Sets_iprod_obj] 的显而易见的推广，通过一个方程；投影在一个索引上求值，可交换性域是一个点的第二个分量，中介者元组一个竞争的族，并将其自身的一致性假设作为第二个分量。没有任何内容需要索引非空，因此空索引也被涵盖——有关这意味着什么和不意味着什么，请参见 BOUNDARIES 段落。(d) 在子对象层面上，七个草图单元律 ∅ ∪ X ≅ X 是 Theory/Subobject/Lattice.v 中的 [sub_join_via_bot]：GENERAL，在任何具有余笛卡尔结构、初始对象（其出箭是单射）以及相关副配对像的范畴中都成立。它最初是在本文件中证明的，当时开发的两个部分是并行编写的，并在集成时被提升到该文件中。[fs_join_bot_left_unit] 在 [Sets] 以及自然数的三元素子对象 {1,2,3} 上实例化了它。(e) 《七个草图》§1.2.1 在可用的最强强度下工作的情况。环境对象是 [Sets_nat]，由 Instance/Sets/Products.v 的 [Sets_discrete] 构建在 [nat] 上的离散集合体；族是 [fs_seg n]，子对象 {k | 1 ≤ k ≤ n}，因此 [fs_seg 0] 是空的，并且该族在增加。然后

 [fs_union_is_positives] : fs_union ≈ fs_pos
 [fs_inter_is_empty] : fs_inter ≈ fs_bot其中 [fs_union] 在 Instance/Sets/Products.v 的 [sub_wide_join_via] 和此文件的图像中，并且 [fs_inter] 在索引 0 和此文件的宽回溯中是 [sub_wide_intersection]。两者在 [SubObj Sets_nat] 上近似——也就是 Theory/Subobject.v 的集合范畴，是一个与单射交换的域同构——而不是 Instance/Powerset/Subobject.v 的 [subset_le_of_sub_le] 通过 Prop 值子集提供的较弱的成员等价。两个陈述都根本没有通过幂集桥。两者都是通过 Theory/Subobject.v 的 [sub_equiv_iff_mutual] 从相互的 [sub_le] 组装而成。

 ** 联合证明的每一半从何处获取其内容并集是一个图像，因此一半是自由的：[im_least] 应用于 [fs_pos]，以及将一个带标记元素 (j, a) 从索引余积发送到其值的箭头，其值为正，因为 a 是正的。另一半是有内容的，这正是家族的递增性所在：必须在某个成员内部展示一个正的自然数 k，并且选择的成员就是 [fs_seg k] 本身，其中 k 符合 [Nat.le_refl]。一个没有穷尽正数的家族将根本不会携带该箭头。交集是另一半内容的对偶情况：[sub_bot_least] 免费给出一个方向，而另一个是 [seg_zero_empty] ——宽回撤的一个点在每个索引都有一个分量，特别是在 0 处，并且 [fs_seg 0] 的一个成员携带 1 ≤ k ≤ 0。因此交集为空，因为恰好有一个成员为空，这正是书中集合族交集为空的原因。

 ** 宇宙，从约束块中读取

 使用 [Set Printing Universes. About Sets_HasWidePullbacks.] 及其他进行复现。

 Sets_HasWidePullbacks@{o so} : HasWidePullbacks@{o o so o} Sets@{o so}
 ( * o so |= o < so, o <= compose.u0/u1/u2, o <= Projections.u0/u1, o <= ID.u0 * )该类的 INDEX 宇宙在 [o] 处被实例化，[Sets] 对象的 CARRIERS 的宇宙——同一位置 Instance/Sets/Products.v 的头部显示 [Sets_HasIndexedProducts]，将其放置，并且出于相同原因：在 [I : Type@{u}] 上的一致族落在 [Type@{max(u,o)}]，而这恰好是一个 carrier 当 u ≤ o 时。通过 [obj[Sets@{o so}] 对同一宇宙实例的族进行索引级别过高，因此被拒绝为宇宙不一致——稳定内容是 [so <= o] 无法强制，因为 [o < so]；确切措辞取决于陈述的方式（[Sets_WidePullback] 上的 [Definition] 草稿打印 “Cannot enforce so <= o because o < so”，类的实例化读取 “cannot ensure that Type@{so} is a subtype of Type@{o}”），因此这两个句子都没有被引用为 THE 文本。相同的定义，其宇宙保持自由，在不同的实例（在家族的下一级索引类别）中展开，这是精心设计的 Instance/Sets/Products.v 为其自身类记录的形式，且拒绝不应被理解为更多。[Sets_HasImages] 携带相同的块加上 [o <= projections.u0/u1]、[so <= projections.u0/u1] 和 [o <= Logic_lemmas.equality.u0]，它们来自 sigma 类型投影，图像载体由此构建。处理过的案例在 [Set] ： [About fs_union_is_positives] 打印
 [fs_union_is_positives@{u} : equiv fs_union@{u Set} fs_pos@{u Set}]
 与块 [Set < u, u <= projections.u0, u <= projections.u1] ，因为
 [nat] 并且段承载器在 [Set] 。 该引脚是 EXAMPLE 的属性，而不是 (a)-(c) 的属性：没有
 [Sets_zero_monic] ， [Sets_HasImages] 或 [Sets_HasWidePullbacks] 在绑定器或块中提到 [Set] 。 一个折叠是继承的，并在此披露，而不是留待发现：每个消耗 [SubObj] 的常量
 绑定 [Category@{u u0 u0}] ，同一宇宙通过证明宇宙识别，因为 Theory/Subobject.v 的 [SubObj] 记录本身确实如此
 ([About SubObj] 打印
 [∀ {C : Category@{u u0 u0}}, obj[C] → Type@{max(u,u0)}])
 并且 [sub_le] 的块承载 [h = p] ；Theory/Subobject/Lattice.v 的头部也以相同方式归属它。 该文件或此文件都没有引入它。

 ** 边界，已测量该并集大约等于正自然数，但并不完全等于它们：[sub_dom fs_union = pos_obj] 被拒绝，"无法统一"，其映像承载体是一个点的 sigma 与选定的原像，而不是一个证明的 sigma。 空索引广拉回同样仅在 ≅ 之下终结 -- Structure/Pullback/Wide.v 的 [wide_pullback_empty_terminal] -- 并且与选定的终端集合类 [Sets_wpull_obj] 在 [I := False] 对比下 [terminal_obj] 不可转换，因其承载体是空族的集合类，带有空的相干性证明，而非 [poly_unit]。 两次拒绝都是由于转换失败，而非宇宙问题。

 ** 透明度，通过翻转来衡量[Sets_image_least_map]、[Sets_ImageOf] 和 [Sets_WidePullback] 必须是 [Defined]：每个依次被翻转为 [Qed]，然后文件在 [ImageOf] 记录的 [im_least] 字段、在 [fs_pos_to_union] 和在 [fs_inter_to_bot] 分别停止——消费者读取底层函数、图像载体和宽回拉载体。[fs_inter_le_bot] 编译为 [Qed]，并为一致性写为 [Defined]，是 [sub_le] 数据。

 **未交付的内容没有注册任何格结构：在 [SubObj x] 处以下的任何内容都不属于任何序或格类，原因是 Instance/Powerset/Subobject.v 的头部说明 -- [sub_le] 是 [Type] 值类型，而 [relation] 不是。在此未构建任何 [IsIntersection] / [IsUnion] 证明；最小上界和最大下界属性属于 Theory/Subobject/Lattice.v，是另一个代理的一半。没有分配性，没有补元，没有 Heyting 结构，也没有与 Instance/Sets/Powerset.v 的 Prop 值子集进行比较。二元 [sub_meet] 在 [Sets] 处未实例化 -- 它需要 [HasPullbacks Sets]，Instance/Sets/Pullback.v 提供为 [Sets_HasPullbacks]，但以下没有调用它，而二元交在 FinSet 同伴处使用。右单位律 X ∪ ∅ ≅ X 没有被陈述——只陈述了左单位律，因为书上只陈述了左单位律。关于任何函子对并集或交集的保持性，没有任何声明。
*)

(* ------------------------------------------------------------------------ *)
(* * ** (a) The map out of the empty setoid is monic / * **（a）空等价类的映射是单射 *)

Lemma Sets_zero_monic (x : Sets) : Monic (@zero Sets Sets_Initial x).
Proof.
  constructor; intros z g1 g2 _ w.
  destruct (g1 w).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** (b) Images *)

Section SetsImages.

Universe o so.
Constraint o < so.

Context {y x : SetoidObject@{o o}}.
Context (f : y ~{Sets@{o so}}~> x).

Definition Sets_im_sub : @SubObj Sets@{o so} x :=
  @Build_SubObj Sets@{o so} x
    (Sets_Image f) (Sets_Image_mono f) (Sets_Image_mono_monic f).

Lemma Sets_image_least_eq (w : @SubObj Sets@{o so} x)
  (g : y ~{Sets@{o so}}~> sub_dom w) (Hg : sub_mono w ∘ g ≈ f)
  (p : carrier (Sets_Image f)) :
  sub_mono w (g (`1 (`2 p))) ≈ `1 p.
Proof.
  transitivity (f (`1 (`2 p))).
  - exact (Hg (`1 (`2 p))).
  - exact (`2 (`2 p)).
Qed.

Definition Sets_image_least_map (w : @SubObj Sets@{o so} x)
  (g : y ~{Sets@{o so}}~> sub_dom w) (Hg : sub_mono w ∘ g ≈ f) :
  Sets_Image f ~{Sets@{o so}}~> sub_dom w.
Proof.
  unshelve refine {| morphism := fun p => g (`1 (`2 p)) |}.
  intros p q Hpq.
  apply (snd (injectivity_is_monic (sub_mono w)) (sub_is_monic w)).
  transitivity (`1 p); [ exact (Sets_image_least_eq w g Hg p) | ].
  transitivity (`1 q); [ exact Hpq | ].
  symmetry; exact (Sets_image_least_eq w g Hg q).
Defined.

Definition Sets_ImageOf : ImageOf f.
Proof.
  unshelve refine {| im_sub := Sets_im_sub
                   ; im_factor := Sets_Image_epi f |}.
  - exact (Sets_Image_comm f).
  - intros w g Hg.
    exact (existT _ (Sets_image_least_map w g Hg)
             (Sets_image_least_eq w g Hg)).
Defined.

End SetsImages.

#[export] Instance Sets_HasImages@{o so} : HasImages Sets@{o so} :=
  @Build_HasImages Sets@{o so} (@Sets_ImageOf@{o so}).

(* ------------------------------------------------------------------------ *)
(** ** (c) Wide pullbacks / **（c）大幅回撤 *)

Local Obligation Tactic := idtac.

Section SetsWidePullback.

Universe o so.
Constraint o < so.

Context {I : Type@{o}}.
Context {A : I → SetoidObject@{o o}}.
Context {z : SetoidObject@{o o}}.
Context (f : ∀ i : I, A i ~{Sets@{o so}}~> z).

Definition Sets_wpull_carrier : Type@{o} :=
  { a : ∀ i : I, carrier (A i) & ∀ i j : I, f i (a i) ≈ f j (a j) }.

Definition Sets_wpull_equiv : crelation@{o o} Sets_wpull_carrier :=
  fun p q => ∀ i : I, `1 p i ≈ `1 q i.

Program Definition Sets_wpull_obj : SetoidObject@{o o} := {|
  carrier   := Sets_wpull_carrier;
  is_setoid := {| equiv := Sets_wpull_equiv |}
|}.
Next Obligation.
  constructor.
  - intros p i; reflexivity.
  - intros p q Hpq i; symmetry; exact (Hpq i).
  - intros p q r Hpq Hqr i;
      transitivity (`1 q i); [exact (Hpq i) | exact (Hqr i)].
Qed.

Program Definition Sets_wpull_proj (i : I) :
  Sets_wpull_obj ~{Sets@{o so}}~> A i := {|
  morphism := fun p => `1 p i
|}.
Next Obligation. intros i p q Hpq; exact (Hpq i). Qed.

Program Definition Sets_wpull_tuple (Q : SetoidObject@{o o})
  (q : ∀ i : I, Q ~{Sets@{o so}}~> A i)
  (Hq : ∀ i j : I, f i ∘ q i ≈ f j ∘ q j) :
  Q ~{Sets@{o so}}~> Sets_wpull_obj := {|
  morphism := fun w => existT _ (fun i => q i w) (fun i j => Hq i j w)
|}.
Next Obligation.
  intros Q q Hq w w' Hw i; exact (proper_morphism (q i) _ _ Hw).
Qed.

Definition Sets_WidePullback : WidePullback f.
Proof.
  unshelve refine (@Build_WidePullback Sets@{o so} I A z f
                     Sets_wpull_obj Sets_wpull_proj _ _).
  - intros i j p; exact (`2 p i j).
  - intros Q q Hq.
    unshelve refine {| unique_obj := Sets_wpull_tuple Q q Hq |}.
    + intros i w; reflexivity.
    + intros v Hv w i; symmetry; exact (Hv i w).
Defined.

End SetsWidePullback.

#[export] Instance Sets_HasWidePullbacks@{o so} :
  HasWidePullbacks Sets@{o so} :=
  @Build_HasWidePullbacks Sets@{o so} (@Sets_WidePullback@{o so}).

Local Obligation Tactic := cat_simpl.

(* ------------------------------------------------------------------------ *)
(*
   * ** (d) The left unit law for the join, in any category

   That law is Theory/Subobject/Lattice.v's [sub_join_via_bot]; it was
   first proved in this file while the two halves of the development were
   written in parallel and was lifted into that file at integration.  Its
   [Sets] instance is [fs_join_bot_left_unit] under (e) below. 

   --------
   * **（d）任何范畴中并运算的左单位律

   该律在 Theory/Subobject/Lattice.v 的 [sub_join_via_bot] 中；它最初在本文件中证明，当时开发的两部分是并行编写的，并在整合时被引入到该文件中。
   它在下面(e)中的 [Sets] 实例是 [fs_join_bot_left_unit]。
*)

(* ------------------------------------------------------------------------ *)
(* * ** (e) Fong and Spivak Seven Sketches 1.2.1: the increasing family / * ** (e) Fong 和 Spivak 七个草图 1.2.1：增长的族 *)

Definition Sets_nat : obj[Sets] := Sets_discrete nat.

Definition seg_carrier (n : nat) : Type :=
  { k : nat & (1 <= k)%nat /\ (k <= n)%nat }.

Program Definition seg_obj (n : nat) : obj[Sets] := {|
  carrier   := seg_carrier n;
  is_setoid := {| equiv := fun a b : seg_carrier n => `1 a = `1 b |}
|}.

Program Definition seg_mono (n : nat) : seg_obj n ~{Sets}~> Sets_nat := {|
  morphism := fun a => `1 a
|}.

Definition seg_monic (n : nat) : Monic (seg_mono n) :=
  fst (injectivity_is_monic (seg_mono n)) (fun a b (Hab : `1 a = `1 b) => Hab).

Definition fs_seg (n : nat) : @SubObj Sets Sets_nat :=
  @Build_SubObj Sets Sets_nat (seg_obj n) (seg_mono n) (seg_monic n).

Definition pos_carrier : Type := { k : nat & (1 <= k)%nat }.

Program Definition pos_obj : obj[Sets] := {|
  carrier   := pos_carrier;
  is_setoid := {| equiv := fun a b : pos_carrier => `1 a = `1 b |}
|}.

Program Definition pos_mono : pos_obj ~{Sets}~> Sets_nat := {|
  morphism := fun a => `1 a
|}.

Definition pos_monic : Monic pos_mono :=
  fst (injectivity_is_monic pos_mono) (fun a b (Hab : `1 a = `1 b) => Hab).

Definition fs_pos : @SubObj Sets Sets_nat :=
  @Build_SubObj Sets Sets_nat pos_obj pos_mono pos_monic.

(* * *** The union of the family is the positive naturals / * *** 家庭的联合是正自然数 *)

Definition fs_coprod :
  IsIndexedCoproduct (fun j : nat => sub_dom (fs_seg j))
    (Sets_icoprod_obj (fun j : nat => sub_dom (fs_seg j)))
    (Sets_icoprod_inj (fun j : nat => sub_dom (fs_seg j))) :=
  Sets_IsIndexedCoproduct (fun j : nat => sub_dom (fs_seg j)).

Definition fs_desc :
  Sets_icoprod_obj (fun j : nat => sub_dom (fs_seg j)) ~{Sets}~> Sets_nat :=
  unique_obj (icoprod_desc fs_coprod (fun j : nat => sub_mono (fs_seg j))).

Definition fs_image : ImageOf fs_desc := image_of fs_desc.

Definition fs_union : @SubObj Sets Sets_nat :=
  sub_wide_join_via fs_seg fs_coprod fs_image.

Program Definition fs_union_to_pos :
  Sets_icoprod_obj (fun j : nat => sub_dom (fs_seg j)) ~{Sets}~> pos_obj := {|
  morphism := fun p => existT _ (`1 (`2 p)) (proj1 (`2 (`2 p)))
|}.
Next Obligation.
  intros [j a] [j' b] [e Hab]; simpl in *; destruct e; simpl in *.
  exact Hab.
Qed.

Lemma fs_union_to_pos_eq : sub_mono fs_pos ∘ fs_union_to_pos ≈ fs_desc.
Proof. intro p; reflexivity. Qed.

Definition fs_union_le_pos : sub_le fs_union fs_pos :=
  im_least fs_image fs_pos fs_union_to_pos fs_union_to_pos_eq.

Program Definition fs_pos_to_union :
  pos_obj ~{Sets}~> sub_dom fs_union := {|
  morphism := fun a =>
    existT _ (`1 a)
      (existT _ (existT _ (`1 a) (existT _ (`1 a)
                  (conj (`2 a) (Nat.le_refl (`1 a))))) eq_refl)
|}.

Definition fs_pos_le_union : sub_le fs_pos fs_union :=
  existT _ fs_pos_to_union (fun a => eq_refl).

Theorem fs_union_is_positives : fs_union ≈ fs_pos.
Proof.
  exact (snd (sub_equiv_iff_mutual fs_union fs_pos)
           (fs_union_le_pos, fs_pos_le_union)).
Qed.

(* * *** The intersection of the family is the bottom subobject / * *** 家族的交集是底子对象 *)

Definition fs_wpull : WidePullback (fun j : nat => sub_mono (fs_seg j)) :=
  Sets_WidePullback (fun j : nat => sub_mono (fs_seg j)).

Definition fs_inter : @SubObj Sets Sets_nat :=
  sub_wide_intersection fs_seg 0%nat fs_wpull.

Definition fs_bot : @SubObj Sets Sets_nat :=
  sub_bot (Sets_zero_monic Sets_nat).

Lemma seg_zero_empty (a : carrier (sub_dom (fs_seg 0%nat))) : False.
Proof.
  destruct a as [k [H1 H2]].
  exact (Nat.nle_succ_0 0 (Nat.le_trans 1 k 0 H1 H2)).
Qed.

Program Definition fs_inter_to_bot :
  sub_dom fs_inter ~{Sets}~> sub_dom fs_bot := {|
  morphism := fun p => False_rect _ (seg_zero_empty (`1 p 0%nat))
|}.
Next Obligation.
  intros p q Hpq; destruct (seg_zero_empty (`1 p 0%nat)).
Qed.

Definition fs_inter_le_bot : sub_le fs_inter fs_bot.
Proof.
  exists fs_inter_to_bot.
  intro p; destruct (seg_zero_empty (`1 p 0%nat)).
Defined.

Theorem fs_inter_is_empty : fs_inter ≈ fs_bot.
Proof.
  exact (snd (sub_equiv_iff_mutual fs_inter fs_bot)
           (fs_inter_le_bot,
            sub_bot_least (Sets_zero_monic Sets_nat) fs_inter)).
Qed.

(* * *** The unit law at a concrete subobject / * *** 具体子对象的幺单位律 *)

Definition fs_bot_join_seg3 : @SubObj Sets Sets_nat :=
  sub_join_via (sub_bot (Sets_zero_monic Sets_nat)) (fs_seg 3%nat)
    (image_of (merge (sub_mono (sub_bot (Sets_zero_monic Sets_nat)))
                 (sub_mono (fs_seg 3%nat)))).

Example fs_join_bot_left_unit : fs_bot_join_seg3 ≈ fs_seg 3%nat :=
  sub_join_via_bot (Sets_zero_monic Sets_nat) (fs_seg 3%nat) _.
