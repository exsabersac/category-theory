Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Two.
Require Import Category.Instance.Ordinal.
Require Import Category.Construction.Free.Quiver.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.Eqdep_dec.

Generalizable All Variables.

(*
   * * Concrete free categories, and the finite ordinals as free categories 

   --------
   * * 混凝土自由范畴，以及有限序数作为自由范畴
*)

(*
 nLab:      https://ncatlab.org/nlab/show/free+category
 nLab:      https://ncatlab.org/nlab/show/quiver
 nLab:      https://ncatlab.org/nlab/show/thin+category
 Book:      Mac Lane, Categories for the Working Mathematician, 2nd ed.,
 GTM 5, Springer 1998, §II.7, printed pp. 50-51

 CITED BY LOCATION; the printed text was not consulted.  The two items worked
 here are the in-tree catalog entries [maclane:II.7:remark3] (the examples of
 free categories) and [maclane:II.7:ex2] (finite ordinals are free), in
 doc/plan/books/maclane/inventory/II.json.  Everything attributed to Mac Lane
 below paraphrases the CATALOG'S summaries, which are themselves paraphrases
 and not the book's wording.

 Construction/Free/Quiver.v builds the free category on a quiver and proves
 its universal property ([FreeOnQuiver], [UniversalArrowQuiverCat],
 [FreeForgetfulAdjunction]).  What it does not do is say what any particular
 free category IS.  This file identifies three of them by name.

 THE FOUR EXAMPLES.  The catalog's [maclane:II.7:remark3] lists three, and
 the exercise [maclane:II.7:ex2] adds the fourth:

 (1) THE LOOP.  One node with a single endo-edge; the free category has
 arrows 1, f, f^2, ..., i.e. the free monoid on one generator read as a
 one-object category.  NOT BUILT HERE.  That identification belongs to
 issue #802 ("the free category on a single loop is the additive
 naturals"), which owns it together with the general fact that a free
 category has only identity isomorphisms.  Neither is in the tree yet:
 as of this file there is no Construction/Free/Quiver/Loop.v.  It is
 recapped here only so the reader knows which of Mac Lane's examples
 this file does and does not cover.

 (2) THE WALKING ARROW.  One edge with distinct endpoints; the free
 category is that arrow plus an identity at each end.  Delivered as
 [arrow_free : FreeOnQuiver ArrowQuiver ≅[StrictCat] _2].

 (3) THE COMPOSABLE PAIR.  Three nodes . -> . -> .; the free category is
 the commutative triangle -- three identities, the two generators, and
 one composite.  Delivered as
 [chain_free : FreeOnQuiver (LinQuiver 3) ≅[StrictCat] _3], an INSTANCE
 of (4) rather than a second development, together with an exhaustive
 hom-set description ([chain_hom_01] and its eight siblings) and
 [chain_e10_length = 2], which says the composite is literally the
 two-edge path and not a further generator.

 (4) THE FINITE ORDINALS.  Exercise 2.  Delivered as
 [ordinal_free m : FreeOnQuiver (LinQuiver m) ≅[StrictCat] Ordinal m],
 for EVERY m -- the empty ordinal included, through the separate
 [ordinal_free_0], since the donor [Functor_of_Steps] is stated for
 [Ordinal (S n)].

 STRENGTHS, stated precisely.  All three DELIVERED identifications above --
 (2), (3) and (4); (1) is not built here -- are isomorphisms in [StrictCat], i.e. up to [Functor_StrictEq_Setoid]: equal
 object maps on the nose, with the morphism maps agreeing after transport.
 That is the STRONGER of the two readings the library supports.  The weaker
 [Cat] reading -- where an isomorphism is only an EQUIVALENCE of categories,
 [Cat]'s hom-setoid being [Functor_Setoid] -- is recorded alongside as
 [arrow_free_Cat] and [ordinal_free_Cat], each obtained from the strict form
 through [strict_equiv_implies_fun_equiv] (Instance/StrictCat/ToCat.v).  For
 the walking arrow the strict witnesses are literally [eq_refl], both
 comparison functors being the identity on objects; for the nonempty ordinals
 they are [ord_clamp_id], the backward functor's object map being [Ordinal m]'s
 own clamping, and for the empty one they are vacuous.

 Instance/Ordinal.v's header previously recorded the [StrictCat] form of (4)
 as "a further theorem that is NOT delivered in this file and remains open".
 It is [ordinal_free] here, and that note has been updated to say so.

 THE ENGINE is one lemma, [graded_free_thin]: if a quiver carries a rank
 function on nodes such that every edge raises the rank by exactly one, the
 rank is injective on nodes, and parallel edges are unique up to the edge
 setoid, then its free category is THIN -- at most one path between any two
 nodes.  Every identification below then costs almost nothing, because each
 round trip and each functor law is an equation between parallel arrows: in
 [_2] by [Two_thin], in [Ordinal m] by [le_t_irr], and in the free category
 by [graded_free_thin] itself.  The one place with genuine content is
 [graded_het], an induction over [tlist] paths in the HETEROGENEOUS form the
 library's path equivalence uses, because two parallel paths pass through
 intermediate nodes that are only PROPOSITIONALLY equal, and the equivalence
 [tlist'_quiver_equiv] carries exactly that equality as data.

 NO UIP IS ASSUMED.  The induction needs uniqueness of identity proofs on
 nodes, and gets it: rank-injectivity makes node equality decidable
 ([graded_node_eq_dec]), and Hedberg's theorem through
 [Eqdep_dec.UIP_dec] then supplies [graded_node_uip], axiom-free.  The
 uniqueness of the linear quiver's edges is the same step at [nat]
 ([linear_edge_unique]).  No axiom, no functional extensionality, and no
 classical reasoning is used anywhere in this file; every named constant and
 every Program obligation reports "Closed under the global context".

 UNIVERSES.  ERRATUM, and the pin is GONE.  An earlier revision of this
 header recorded that every identification below in whose statement a
 quiver appears was confined to [Category@{Set Set Set}], that this was
 FORCED rather than an artifact of minimization, and that lifting the
 restriction "would mean changing [Build_Quiver_Standard_Eq] ... and is out
 of scope here".  The diagnosis was right and the pin was real:
 [Build_Quiver_Standard_Eq] elaborated to [... -> Quiver@{u u0 Set}], its
 PROOF universe silently minimized to [Set] because its edge setoid was
 built from [Corelib.Classes.CRelationClasses.eq_equivalence@{u}], which
 carries ONE universe binder and so cannot separate the carrier's level from
 the proof level.  [FreeOnQuiver@{o h p}]'s constraints [o <= h] and
 [h <= p] then pulled the whole statement down to [Set].

 That change has since been made, in the course of issue #300
 (Instance/Square.v, which needs functors out of a PRESENTED quiver into an
 arbitrary target and so met the same pin from the other side).
 [Build_Quiver_Standard_Eq@{o h p}] now names its proof universe and spends
 the polymorphism of Lib/Setoid.v's own [eq_equivalence@{t u}], which was
 introduced for exactly this purpose.

 WHAT THE LIFT DOES AND DOES NOT BUY — stated carefully, because an earlier
 draft of this very erratum overstated it and had to be corrected in turn.
 The lift is at the CONSTRUCTOR, and the probe that actually demonstrates it
 is [FreeOnQuiver@{uo uh up} (LinQuiver@{uo uh up} 3)]: accepted now,
 REJECTED before the lift with [Cannot enforce Set = up].  [LinQuiver] gains
 a third binder ([ArrowQuiver] likewise, 2 -> 3), and [linear_hom_iff], which
 carried no binders at all, now carries [@{u}] and is stated over
 [FreeOnQuiver@{u u u}] — that is a genuine change wrought BY this commit,
 not a correction of an earlier mis-measurement.

 What the lift does NOT do is move the identifications below.  Their
 STATEMENTS were not touched, so elaboration still minimizes them:
 [ordinal_free] reads [Isomorphism@{u Set Set} (FreeOnQuiver@{Set Set Set}
 (LinQuiver@{Set Set Set} m)) (Ordinal@{Set Set Set} m)] both before and
 after, and [arrow_free_Cat] likewise.  Their outer binders
 ([ordinal_free@{u u0 u1}] and so on) were instantiable above [Set] BEFORE
 the lift too, so accepting [Constraint Set < o] on them demonstrates
 nothing; the categories are hard-coded at [Set] inside the statement and no
 instantiation of the binders can move them.  So the earlier note's closing
 caveat STANDS and is repeated here deliberately: these are identifications
 of SMALL categories at the [Set] level, and a consumer wanting them at a
 larger level cannot get there by instantiation — only by restating them.
 What the lift changes is that a NEWLY WRITTEN statement over these quivers
 may now be stated at an arbitrary level, which is what Instance/Square.v
 needs and what the old constructor made impossible.

 Two further corrections to the earlier note, of different kinds.  Genuine
 error: it read [Ordinal_2_strict_iso]'s hom and proof universes as pinned by
 [_2]'s own [TwoHom : TwoObj -> TwoObj -> Set], but landing in [Set] forces
 only [Set <= h], not [h = Set], and the probe accepted a strictly larger
 instance BEFORE the lift as well.  Not an error: its record of
 [linear_hom_iff] as [@{}] was correct when written, and became stale only
 because this commit changed that constant.  [graded_free_thin@{u u0 u1}] was
 never pinned, being stated over an arbitrary [Quiver@{u u0 u1}].  Those are
 the constants measured; no claim is made about any other.

 WHAT IS NOT HERE.  The loop example, per the delegation above.  A bijection
 between paths and ordinal arrows on the nose: what is proved is that the two
 categories are isomorphic in [StrictCat], and the hom-level content is
 [linear_hom_iff] -- inhabited exactly when the indices are ordered, and
 thin -- rather than an identification of the underlying types.  And the
 agreement between [arrow_free] and [linear_2_free]: they identify the free
 categories on two DIFFERENT quivers with [_2], one whose nodes are [TwoObj]
 and one whose nodes are the objects of [Ordinal 2], so neither subsumes the
 other and no comparison between them is stated. 

 --------
 nLab:       https://ncatlab.org/nlab/show/free+category 
 nLab:       https://ncatlab.org/nlab/show/quiver 
 nLab:       https://ncatlab.org/nlab/show/thin+category 
 书籍:      Mac Lane，《为在职数学家准备的范畴论》，第2版，
 GTM 5，Springer 1998，§II.7，第50-51页印刷版

 引用的位置；未查阅印刷文本。这里处理的两个条目是树内目录条目 [maclane:II.7:remark3]（自由范畴的例子）和 [maclane:II.7:ex2]（有限序数是自由的），位于 doc/plan/books/maclane/inventory/II.json。下面所有归于 Mac Lane 的内容都概述自目录的摘要，这些摘要本身是概述，并非书中的原文。Construction/Free/Quiver.v 构建了一个箝口（quiver）上的自由范畴，并证明了它的泛性质（[FreeOnQuiver], [UniversalArrowQuiverCat], [FreeForgetfulAdjunction]）。它没有说明任何特定的自由范畴是什么。这个文件通过名称识别了其中的三个。

 四个例子。目录中的 [maclane:II.7:remark3] 列出了三个，而练习 [maclane:II.7:ex2] 添加了第四个：(1) 环。一个节点有一个自指边；自由范畴有箭头 1, f, f^2, ...，即以一个生成元形成的自由幺半群，看作一个单对象范畴。在这里未构建。这种对应属于第 #802 号议题（“单个环上的自由范畴是加法自然数”），它与自由范畴仅有恒等同构的一般事实一起归其所有。目前在树中都没有：截至此文件时，没有 Construction/Free/Quiver/Loop.v。这里重述仅为了让读者知道 Mac Lane 的哪些例子此文件覆盖，哪些不覆盖。

 (2) 行走箭头。一个边有不同的端点；自由范畴就是该箭头加上每个端点的恒等箭头。作为 [arrow_free : FreeOnQuiver ArrowQuiver ≅[StrictCat] _2 提供。(3) 可组合对。三个节点 . -> . -> .；自由范畴是可交换三角形——三个恒等态，两个生成元，以及一个复合。作为 [chain_free : FreeOnQuiver (LinQuiver 3) ≅[StrictCat] _3] 提供，是 (4) 的一个实例，而不是第二个展开，同时附有详尽的同态集描述 ([chain_hom_01] 及其八个同类) 和 [chain_e10_length = 2]，它说明复合实际上是两边路径，而不是进一步的生成元。

 (4) 有限序数。练习 2。作为 [ordinal_free m : FreeOnQuiver (LinQuiver m) ≅[StrictCat] Ordinal m] 提供，适用于每个 m——包括空序数，通过单独的 [ordinal_free_0]，因为提供者 [Functor_of_Steps] 是针对 [Ordinal (S n)] 陈述的。优势，精确陈述。上面提到的三个辨识——(2)、(3) 和 (4)；(1) 此处未构建——在 [StrictCat] 中是同构，即在 [Functor_StrictEq_Setoid] 下：在对象映射上严格相等，且在传输后态射映射也一致。这是库支持的两种解读中较强的一种。较弱的 [Cat] 解读——其中同构仅是范畴的等价，[Cat] 的 Hom-集合类型为 [Functor_Setoid]——也被记录为 [arrow_free_Cat] 和 [ordinal_free_Cat]，它们都是通过严格形式经 [strict_equiv_implies_fun_equiv]（Instance/StrictCat/ToCat.v）获得的。对于行走箭头，严格的见证者字面上是 [eq_refl]，两个比较函子在对象上都是恒等的；对于非空序数，它们是 [ord_clamp_id]，后向函子的对象映射是 [Ordinal m] 自身的固定，而对于空序数，它们是空的。

 Instance/Ordinal.v 的标题之前记录了 (4) 的 [StrictCat] 形式，说明“这是一个在该文件中未提供且仍未解决的进一步定理”。它在这里是 [ordinal_free]，并且该注释已更新为如此说明。发动机是一个引理，[graded_free_thin]：如果一个重箭筒在节点上携带一个秩函数，使得每条边恰好将秩提升一个单位，并且秩在节点上是单射的，且平行边在边集合等价下是唯一的，那么它的自由范畴是稀薄的——任意两个节点之间最多有一条路径。下面的每一个等同几乎不花成本，因为每一次往返以及每一个函子定律都是平行箭头之间的方程：在[_2] 中由[Two_thin]，在[Ordinal m] 中由[le_t_irr]，并且在自由范畴中由[graded_free_thin] 本身。唯一具有真实内容的地方是 [graded_het]，这是对 HETEROGENEOUS 形式中 [tlist] 路径的归纳，该形式是图书馆路径等价使用的形式，因为两条平行路径经过的中间节点只是命题上相等，而等价 [tlist'_quiver_equiv] 精确地将该等价性作为数据携带。不假设 UIP。归纳需要节点上身份证明的唯一性，并且得到了它：秩可注性使节点相等性可判定（[graded_node_eq_dec]），而通过 [Eqdep_dec.UIP_dec] 的 Hedberg 定理随后提供了 [graded_node_uip]，无需公理。线性箭图的边的唯一性在 [nat]（[linear_edge_unique]）是同样的步骤。在本文件中的任何地方都未使用公理、函数外延性或经典推理；每一个命名常量和每一个 Program 义务都报告“在全局上下文下闭合”。宇宙。勘误，针已经消失。之前这个标题的修订版本记录了以下每个在声明中出现振动的身份都被限制在 [Category@{Set Set Set}]，这是一种强制，而不是最小化的结果，并且解除该限制“将意味着改变 [Build_Quiver_Standard_Eq]……这超出了这里的范围”。诊断是正确的，并且针是真实的：[Build_Quiver_Standard_Eq] 拓展为 [... -> Quiver@{u u0 Set}]，其证明宇宙因其边集（edge setoid）是从 [Corelib.Classes.CRelationClasses.eq_equivalence@{u}] 构建的而被静默最小化为 [Set]，该边集携带一个宇宙绑定器，因此无法将承载者的层级与证明层级分开。[FreeOnQuiver@{o h p}] 的约束 [o <= h] 和 [h <= p] 随后将整个声明拉低到 [Set]。这个更改自那时起就已经在第300期中完成了（Instance/Square.v，需要从一个给出的箭簇中提取函子到任意目标，并因此从另一边遇到了相同的钉）。[Build_Quiver_Standard_Eq@{o h p}] 现在命名它的证明宇宙，并使用 Lib/Setoid.v 自身的 [eq_equivalence@{t u}] 的多态性，这正是为这个目的引入的。电梯能做什么和不能做什么——需要小心说明，因为早期该勘误表的草稿夸大了这一点，后来又必须进行更正。电梯位于构造器（CONSTRUCTOR），而实际上演示它的探针是 [FreeOnQuiver@{uo uh up} (LinQuiver@{uo uh up} 3)]：现在被接受，在使用 [Cannot enforce Set = up] 的电梯之前被拒绝。[LinQuiver] 获得了第三个绑定器（[ArrowQuiver] 也是如此，从 2 个变成 3 个），而 [linear_hom_iff] 原本没有任何绑定器，现在携带了 [@{u}]，并在 [FreeOnQuiver@{u u u}] 上有所声明——这是这次提交真正带来的变更，而不是对早期测量错误的更正。提升不会做的是移动下面的标识符。它们的陈述没有被触碰，所以展开仍然会最小化它们：[ordinal_free] 在提升前后都读作 [Isomorphism@{u Set Set} (FreeOnQuiver@{Set Set Set} (LinQuiver@{Set Set Set} m)) (Ordinal@{Set Set Set} m)]，[arrow_free_Cat] 也是如此。它们的外部绑定器（如 [ordinal_free@{u u0 u1}] 等）在提升前位于 [Set] 之上也是可实例化的，所以在它们上接受 [Constraint Set < o] 并不能证明任何东西；类别在陈述内部的 [Set] 被硬编码，绑定器的任何实例化都无法移动它们。因此，前面注释的结尾警告依然有效，并在此特意重复：这些是在 [Set] 级别的小类别的标识，想要在更大级别获得它们的使用者不能通过实例化来实现——只能通过重新陈述来实现。提升所改变的是，现在可以在这些箭袋上书写的新声明可以在任意级别上陈述，这正是 Instance/Square.v 所需要的，也是旧构造函数所不可能做到的。对前一条备注的另外两处不同类型的更正。真正的错误：它将 [Ordinal_2_strict_iso] 的 hom 和 proof 宇宙读作由 [_2] 自己的 [TwoHom : TwoObj -> TwoObj -> Set] 固定，但降落在 [Set] 只强制 [Set <= h]，而不是 [h = Set]，并且探针在提升之前也接受了一个严格更大的实例。不是错误：当 [linear_hom_iff] 作为 [@{}] 被记录时是正确的，之所以变得过时，只是因为此提交更改了该常量。[graded_free_thin@{u u0 u1}] 从未被固定，是在任意 [Quiver@{u u0 u1}] 上声明的。这些是被测量的常量；对于其他任何常量不作任何声明。这里没有的内容。根据上述委托的循环示例。在路径与序数箭头之间有一个一一对应关系：证明的是在  [StrictCat] 中这两个范畴是同构的，而同态级别的内容是 [linear_hom_iff] ——仅当索引有序时才存在，并且是稀疏的——而不是底层类型的识别。以及 [arrow_free] 与 [linear_2_free] 之间的一致性：它们用 [_2] 识别两个不同图（quiver）上的自由范畴，一个的节点是 [TwoObj]，另一个的节点是 [Ordinal 2] 的对象，因此彼此都不包含对方，也没有对它们进行比较。
*)

#[local] Existing Instance edgeset.

(*
 Every obligation below is discharged explicitly; no proof depends on a
 Program-generated tactic.  (Construction/Free/Quiver/Concrete.v does the
 same, for the same reason.) 

 --------
 下面的每一项义务都被明确履行；没有证据依赖于程序生成的策略。（Construction/Free/Quiver/Concrete.v 也做同样的事情，原因相同。）
*)
#[local] Obligation Tactic := idtac.

(*
 ---------- graded quivers have thin free categories ---------- 

 --------
 ---------- 分级夸克具有稀薄自由范畴 ----------
*)

Section Graded.

Context (G : Quiver).
Context (rank : @nodes G → nat).

Hypothesis edge_rank : ∀ x y : G, edges x y → rank y = S (rank x).
Hypothesis rank_inj  : ∀ x y : G, rank x = rank y → x = y.
Hypothesis edge_unique : ∀ (x y : G) (e e' : edges x y), e ≈ e'.

Definition graded_node_eq_dec (x y : G) : {x = y} + {x ≠ y} :=
  match PeanoNat.Nat.eq_dec (rank x) (rank y) with
  | left e   => left (rank_inj x y e)
  | right ne => right (fun H => ne (f_equal rank H))
  end.

Lemma graded_node_uip (x y : G) (e e' : x = y) : e = e'.
Proof using G rank rank_inj. apply (UIP_dec graded_node_eq_dec). Qed.

(*
 Every edge raises the rank by one, so a path's length is the rank
 difference of its endpoints. 

 --------
 每条边都会将等级提高一，因此一条路径的长度就是其端点的等级差。
*)
Lemma graded_len (j i : G) (p : tlist edges i j) :
  rank j = (tlist_length p + rank i)%nat.
Proof using G rank edge_rank.
  induction p as [| i0 i1 e t IH]; simpl.
  - reflexivity.
  - rewrite IH.
    rewrite (edge_rank _ _ e).
    lia.
Qed.

(*
 Hence no path returns to its source unless it is empty. 

 --------
 因此，除非路径为空，否则没有路径会返回其源头。
*)
Lemma graded_loop_nil (k : G) : ∀ (i : G) (g : tlist edges i k) (e : k = i),
  Logic.transport_r (fun z => @tlist' _ edges k z) e g = tnil.
Proof using G rank edge_rank rank_inj.
  intros i g; induction g as [| i0 i1 e t IH]; intro q.
  - now rewrite (graded_node_uip _ _ q eq_refl).
  - exfalso.
    pose proof (graded_len _ _ t) as Ht.
    rewrite (edge_rank _ _ e) in Ht.
    pose proof (f_equal rank q) as Hq.
    lia.
Qed.

(*
 The heterogeneous form of uniqueness: two paths with a common target and
 propositionally equal sources are equivalent along that equality.  This is
 the form the induction needs, since the intermediate nodes of two parallel
 paths are only propositionally equal. 

 --------
 唯一性的异质形式：具有共同目标且命题上相等的来源的两条路径沿该相等是等价的。这是归纳所需要的形式，因为两条平行路径的中间节点仅在命题上相等。
*)
Lemma graded_het (k : G) : ∀ (i : G) (f : tlist edges i k)
                                  (j : G) (g : tlist edges j k) (e : i = j),
  tlist'_quiver_equiv G k i j f g e.
Proof using G rank edge_rank rank_inj edge_unique.
  intros i f; induction f as [| i0 i1 fhead ftail IH]; intros j g e.
  - simpl; symmetry; now apply graded_loop_nil.
  - destruct g as [| j0 j1 ghead gtail].
    + (* a nonempty path cannot be parallel to the empty one / 非空路径不能与空路径平行 *)
      exfalso.
      pose proof (graded_len _ _ ftail) as Ht.
      rewrite (edge_rank _ _ fhead) in Ht.
      pose proof (f_equal rank e) as He.
      lia.
    + (* both nonempty: the intermediate nodes agree by rank / 两个都非空：中间节点按等级一致 *)
      destruct e.
      assert (q : i1 = j1).
      { apply rank_inj.
        rewrite (edge_rank _ _ fhead), (edge_rank _ _ ghead).
        reflexivity. }
      destruct q.
      exists eq_refl.
      * apply edge_unique.
      * apply IH.
Qed.

(*
 At most one path between any two nodes: the free category is thin. 

 --------
 任意两个节点之间最多只有一条路径：自由范畴是薄的。
*)
Theorem graded_free_thin (x y : FreeOnQuiver G) (p q : x ~> y) : p ≈ q.
Proof using G rank edge_rank rank_inj edge_unique.
  exact (graded_het y x p x q eq_refl).
Qed.

(* No path runs downwards. / 没有道路向下延伸。 *)
Theorem graded_no_path (x y : FreeOnQuiver G) (p : x ~> y) :
  (rank x <= rank y)%nat.
Proof using G rank edge_rank. pose proof (graded_len _ _ p); lia. Qed.

End Graded.

(* ---------- the walking arrow ---------- / ---------- 行走的箭头 ---------- *)

(*
 Two nodes, one edge between them.  The nodes are [TwoObj] itself, so both
 comparison functors below are the identity on objects. 

 --------
 两个节点，它们之间有一条边。节点本身是 [TwoObj]，因此下面的两个比较函子在对象上都是恒等的。
*)
Definition arrow_edges (x y : TwoObj) : Type :=
  match x with
  | TwoX => match y with
            | TwoX => Empty_set
            | TwoY => poly_unit
            end
  | TwoY => Empty_set
  end.

Definition ArrowQuiver : Quiver := Build_Quiver_Standard_Eq TwoObj arrow_edges.

Definition arrow_rank (x : TwoObj) : nat :=
  match x with TwoX => 0%nat | TwoY => 1%nat end.

Lemma arrow_edge_rank (x y : TwoObj) :
  @edges ArrowQuiver x y → arrow_rank y = S (arrow_rank x).
Proof. destruct x, y; simpl; intro e; try (destruct e); reflexivity. Qed.

Lemma arrow_rank_inj (x y : TwoObj) : arrow_rank x = arrow_rank y → x = y.
Proof. destruct x, y; simpl; intro H; try reflexivity; discriminate. Qed.

Lemma arrow_edge_unique (x y : TwoObj) (e e' : @edges ArrowQuiver x y) : e ≈ e'.
Proof.
  destruct x, y; simpl in e, e';
    try destruct e; try destruct e'; reflexivity.
Qed.

(*
 At most one path between any two nodes of the walking-arrow quiver. 

 --------
 在行走箭头箭袋的任意两个节点之间最多有一条路径。
*)
Theorem arrow_free_thin (x y : FreeOnQuiver ArrowQuiver) (p q : x ~> y) : p ≈ q.
Proof.
  exact (graded_free_thin ArrowQuiver arrow_rank
           arrow_edge_rank arrow_rank_inj arrow_edge_unique x y p q).
Qed.

(* The generating edge, as a path. / 生成边，作为一条路径。 *)
Definition arrow_gen : @edges ArrowQuiver TwoX TwoY := ttt.

Definition arrow_path : TwoX ~{FreeOnQuiver ArrowQuiver}~> TwoY :=
  tlist_singleton arrow_gen.

Definition arrow_map (x y : TwoObj) : @edges ArrowQuiver x y → TwoHom x y :=
  match x as x0 return @edges ArrowQuiver x0 y → TwoHom x0 y with
  | TwoX => match y as y0 return @edges ArrowQuiver TwoX y0 → TwoHom TwoX y0 with
            | TwoX => fun e => match e return TwoHom TwoX TwoX with end
            | TwoY => fun _ => TwoXY
            end
  | TwoY => fun e => match e return TwoHom TwoY y with end
  end.

Definition arrow_hom : QuiverHomomorphism ArrowQuiver (QuiverOfCat _2) :=
  Build_QuiverHomomorphism ArrowQuiver (QuiverOfCat _2)
    (fun x => x) arrow_map (fun x y e e' H => f_equal (arrow_map x y) H).

Definition Arrow_to : FreeOnQuiver ArrowQuiver ⟶ _2 :=
  InducedFunctor ArrowQuiver arrow_hom.

Definition arrow_unmap (x y : TwoObj) (f : TwoHom x y) :
  x ~{FreeOnQuiver ArrowQuiver}~> y :=
  match f in TwoHom x0 y0 return x0 ~{FreeOnQuiver ArrowQuiver}~> y0 with
  | TwoIdX => tnil
  | TwoIdY => tnil
  | TwoXY  => arrow_path
  end.

(*
 Every functor law is an equation between parallel paths, so [arrow_free_thin]
 discharges all three. 

 --------
 每个函子定律都是平行路径之间的一个等式，所以 [arrow_free_thin] 解除所有三个。
*)
Definition Arrow_from : _2 ⟶ FreeOnQuiver ArrowQuiver :=
  Build_Functor _2 (FreeOnQuiver ArrowQuiver)
    (fun x => x)
    arrow_unmap
    (fun x y f g _ => arrow_free_thin x y _ _)
    (fun x => arrow_free_thin x x _ _)
    (fun x y z f g => arrow_free_thin x z _ _).

(*
 Mac Lane's second example: the free category on one arrow with distinct
 endpoints is that arrow together with an identity at each end -- which is
 exactly the walking arrow [_2].  Both functors are the IDENTITY on objects,
 so both strict-equality witnesses are [eq_refl]. 

 --------
 Mac Lane 的第二个例子：在具有不同端点的一个箭头上的自由范畴就是该箭头以及每个端点的恒等箭头——这正是行箭头 [_2]。两个函子在对象上都是恒等的，因此两个严格相等的见证都是 [eq_refl]。
*)
Program Definition arrow_free : FreeOnQuiver ArrowQuiver ≅[StrictCat] _2 := {|
  to   := Arrow_to;
  from := Arrow_from
|}.
Next Obligation.
  exists (fun _ => eq_refl); intros x y f; apply Two_thin.
Qed.
Next Obligation.
  exists (fun _ => eq_refl); intros x y f; apply arrow_free_thin.
Qed.

(*
 The same identification read in [Cat], where functors are compared only up
 to natural isomorphism.  This is strictly weaker than the above. 

 --------
 在 [Cat] 中读到的相同识别，其中函子仅在自然同构下进行比较。这严格来说比上面更弱。
*)
Definition arrow_free_Cat : FreeOnQuiver ArrowQuiver ≅[Cat] _2 :=
  @Build_Isomorphism Cat _ _ Arrow_to Arrow_from
    (strict_equiv_implies_fun_equiv _ _ (iso_to_from arrow_free))
    (strict_equiv_implies_fun_equiv _ _ (iso_from_to arrow_free)).

(*
 ---------- every finite ordinal is free on its linear quiver ---------- 

 --------
 ---------- 每个有限序数在其线性箭谱上都是自由的 ----------
*)

(*
 Nodes are the objects of [Ordinal m] themselves, and an edge x -> y is a
 proof that y is the successor of x.  Edges are therefore unique by UIP on
 [nat] (Hedberg, through [Eqdep_dec.UIP_dec] -- no axiom is assumed), and the
 quiver has exactly the m-1 generating steps 0 -> 1 -> ... -> m-1.  The
 numbering counts NODES, matching [Ordinal m]'s own convention: [LinQuiver 0]
 is empty, [LinQuiver 2] is the walking arrow and [LinQuiver 3] the
 composable pair. 

 --------
 节点本身就是 [Ordinal m] 的对象，边 x -> y 是 y 是 x 的继承者的证明。因此，边在 [nat] 上因 UIP 是唯一的（Hedberg，通过 [Eqdep_dec.UIP_dec] —— 未假设任何公理），而该箭图恰好有 m-1 个生成步骤 0 -> 1 -> ... -> m-1。编号计算的是节点，符合 [Ordinal m] 自身的约定：[LinQuiver 0] 是空的，[LinQuiver 2] 是步行箭头，[LinQuiver 3] 是可组合对。
*)
Definition linear_edges@{o h} {m : nat} (x y : Ord_obj@{o} m) : Type@{h} :=
  (S (ord_val x) = ord_val y)%nat.

Definition LinQuiver@{o h p} (m : nat) : Quiver@{o h p} :=
  Build_Quiver_Standard_Eq@{o h p} (Ord_obj@{o} m) (@linear_edges@{o h} m).

Lemma linear_edge_rank {m} (x y : LinQuiver m) :
  @edges (LinQuiver m) x y → ord_val y = S (ord_val x).
Proof. intro e; exact (eq_sym e). Qed.

Lemma linear_rank_inj {m} (x y : LinQuiver m) : ord_val x = ord_val y → x = y.
Proof. apply ord_obj_eq. Qed.

Lemma linear_edge_unique {m} (x y : LinQuiver m)
  (e e' : @edges (LinQuiver m) x y) : e ≈ e'.
Proof. apply (UIP_dec PeanoNat.Nat.eq_dec). Qed.

(*
 At most one path between any two nodes of the linear quiver. 

 --------
 在线性箭袋的任意两个节点之间最多只有一条路径。
*)
Theorem linear_free_thin {m} (x y : FreeOnQuiver (LinQuiver m)) (p q : x ~> y) :
  p ≈ q.
Proof.
  exact (graded_free_thin (LinQuiver m) (@ord_val m)
           (@linear_edge_rank m) (@linear_rank_inj m) (@linear_edge_unique m)
           x y p q).
Qed.

(* And a path exists only upwards. / 而且道路只存在向上。 *)
Theorem linear_no_descent {m} (x y : FreeOnQuiver (LinQuiver m)) (p : x ~> y) :
  (ord_val x <= ord_val y)%nat.
Proof.
  exact (graded_no_path (LinQuiver m) (@ord_val m) (@linear_edge_rank m) x y p).
Qed.

(*
 The comparison into the ordinal: an edge is the generating step.  This half
 is uniform in m, the empty ordinal included. 

 --------
 归入序数的比较：一个极点是生成步骤。这一半在 m 中是统一的，包括空序数。
*)
Definition linear_arrow {m} {x y : LinQuiver m} (e : @edges (LinQuiver m) x y) :
  x ~{Ordinal m}~> y :=
  match e in _ = z return le_t (ord_val x) z with
  | eq_refl => le_t_S le_t_n
  end.

Definition linear_hom (m : nat) :
  QuiverHomomorphism (LinQuiver m) (QuiverOfCat (Ordinal m)) :=
  Build_QuiverHomomorphism (LinQuiver m) (QuiverOfCat (Ordinal m))
    (fun x => x) (fun x y e => linear_arrow e)
    (fun x y e e' H => f_equal (fun t => @linear_arrow m x y t) H).

Definition Linear_to (m : nat) : FreeOnQuiver (LinQuiver m) ⟶ Ordinal m :=
  InducedFunctor (LinQuiver m) (linear_hom m).

(*
 The comparison out of the ordinal is [Instance/Ordinal.v]'s [Functor_of_Steps]
 applied to the n generating edges, taken at the clamped indices.  That donor
 is stated for [Ordinal (S n)], so this half splits on whether the ordinal is
 empty. 

 --------
 序数之外的比较是 [Instance/Ordinal.v] 对 [Functor_of_Steps] 的应用，应用于生成的 n 条边，并取在固定的索引处。该供体用于 [Ordinal (S n)]，因此这一半取决于序数是否为空。
*)
Lemma linear_min_step (n k : nat) (H : le_t (S k) n) :
  (S (Nat.min k n) = Nat.min (S k) n)%nat.
Proof.
  rewrite (le_t_min_l k n (le_t_trans (le_t_S le_t_n) H)).
  now rewrite (le_t_min_l (S k) n H).
Qed.

Definition linear_step {n} (k : nat) (H : le_t (S k) n) :
  @linear_edges (S n) (@ord_clamp n k) (@ord_clamp n (S k)) := linear_min_step n k H.

Definition linear_steps (n : nat) :
  @OrdSteps (FreeOnQuiver (LinQuiver (S n))) n (fun k => @ord_clamp n k) :=
  fun k H => tlist_singleton (@linear_step n k H).

Definition Linear_from (n : nat) :
  Ordinal (S n) ⟶ FreeOnQuiver (LinQuiver (S n)) :=
  Functor_of_Steps (linear_steps n).

(*
 The nonempty case.  Both round trips are equations between parallel arrows
 -- of [Ordinal (S n)], which is thin by [le_t_irr], and of the free category,
 which is thin by [linear_free_thin] -- so the transports carry no content. 

 --------
 非空情况。两个往返都是平行箭头之间的等式——在  [Ordinal (S n)] 中，它是由  [le_t_irr] 薄化的；在自由范畴中，它是由  [linear_free_thin] 薄化的——因此传输不携带任何内容。
*)
Program Definition ordinal_free_S (n : nat) :
  FreeOnQuiver (LinQuiver (S n)) ≅[StrictCat] Ordinal (S n) := {|
  to   := Linear_to (S n);
  from := Linear_from n
|}.
Next Obligation.
  intros n.
  exists (fun x => @ord_clamp_id n x); intros x y f; apply le_t_irr.
Qed.
Next Obligation.
  intros n.
  exists (fun x => @ord_clamp_id n x); intros x y f; apply linear_free_thin.
Qed.

(*
 The empty case, where both categories have no objects at all. 

 --------
 空的情况，即两个类别都没有任何对象。
*)
Definition Linear_from_0 : Ordinal 0 ⟶ FreeOnQuiver (LinQuiver 0) :=
  Build_Functor (Ordinal 0) (FreeOnQuiver (LinQuiver 0))
    (fun x => x)
    (fun x y f => False_rect _ (ord_0_empty x))
    (fun x y f g H => False_rect _ (ord_0_empty x))
    (fun x => False_rect _ (ord_0_empty x))
    (fun x y z f g => False_rect _ (ord_0_empty x)).

Program Definition ordinal_free_0 :
  FreeOnQuiver (LinQuiver 0) ≅[StrictCat] Ordinal 0 := {|
  to   := Linear_to 0;
  from := Linear_from_0
|}.
Next Obligation.
  exists (fun x => False_rect _ (ord_0_empty x));
    intros x y f; destruct (ord_0_empty x).
Qed.
Next Obligation.
  exists (fun x => False_rect _ (ord_0_empty x));
    intros x y f; destruct (ord_0_empty x).
Qed.

(*
 Mac Lane II.7 Exercise 2, as stated: EVERY finite ordinal is a free
 category -- free on the linear quiver with the same nodes. 

 --------
 Mac Lane II.7 练习 2，如所述：每一个有限序数都是一个自由范畴——在具有相同节点的线性箭图上自由生成。
*)
Definition ordinal_free (m : nat) :
  FreeOnQuiver (LinQuiver m) ≅[StrictCat] Ordinal m :=
  match m with
  | O   => ordinal_free_0
  | S n => ordinal_free_S n
  end.

(*
 The same reading in [Cat], where functors are compared only up to natural
 isomorphism.  This is strictly weaker than the above. 

 --------
 在 [Cat] 中有相同的读法，其中函子只比较到自然同构。这比上述严格要弱。
*)
Definition ordinal_free_Cat (m : nat) :
  FreeOnQuiver (LinQuiver m) ≅[Cat] Ordinal m :=
  @Build_Isomorphism Cat _ _ (to (ordinal_free m)) (from (ordinal_free m))
    (strict_equiv_implies_fun_equiv _ _ (iso_to_from (ordinal_free m)))
    (strict_equiv_implies_fun_equiv _ _ (iso_from_to (ordinal_free m))).

(*
 ---------- existence of paths, and the exhaustive hom description ---------- 

 --------
 ---------- 路径的存在，以及穷尽的同态描述 ----------
*)

Definition free_mor_of_eq {G : Quiver} {x y : FreeOnQuiver G} (e : x = y) : x ~> y :=
  match e in _ = z return x ~{FreeOnQuiver G}~> z with
  | eq_refl => id
  end.

(*
 The converse of [linear_no_descent]: whenever the indices are ordered there
 IS a path, obtained by transporting the ordinal's own arrow back along
 [Linear_from]. 

 --------
 [linear_no_descent] 的逆命题：每当索引被排序时，存在一条路径，这条路径是通过将序数自身的箭头沿 [Linear_from] 传回而得到的。
*)
Definition linear_path_of_le {n} (x y : FreeOnQuiver (LinQuiver (S n)))
  (H : (ord_val x <= ord_val y)%nat) : x ~> y :=
  @free_mor_of_eq (LinQuiver (S n)) _ _ (@ord_clamp_id n y)
    ∘ fmap[Linear_from n] (le_t_of_le H)
    ∘ @free_mor_of_eq (LinQuiver (S n)) _ _ (eq_sym (@ord_clamp_id n x)).

(*
 Together with thinness this classifies every hom-set of the free category on
 a linear quiver: it is empty when the indices are out of order, and a
 singleton otherwise. 

 --------
 与稀疏性一起，这就对线性键图上的自由范畴的每个 Hom-集进行了分类：当指标顺序错误时，它为空，否则为单元素集。
*)
Theorem linear_hom_iff {n} (x y : FreeOnQuiver (LinQuiver (S n))) :
  ((x ~> y) → (ord_val x <= ord_val y)%nat) *
  ((ord_val x <= ord_val y)%nat → (x ~> y)) *
  (∀ p q : x ~> y, p ≈ q).
Proof.
  split; [split |].
  - exact (@linear_no_descent (S n) x y).
  - exact (@linear_path_of_le n x y).
  - exact (@linear_free_thin (S n) x y).
Qed.

(*
 ---------- the composable pair: the three-node instance ---------- 

 --------
 ---------- 可组合对：三节点实例 ----------
*)

(*
 Mac Lane's third example: the free category on . -> . -> . is the
 commutative triangle -- three identities, the two generators, and one
 composite.  This is [ordinal_free] at three nodes, whose target [Ordinal 3]
 is Instance/Ordinal.v's [_3]; it is an instance, not a second development. 

 --------
 麦克·莱恩的第三个例子：在 . -> . -> . 上的自由范畴是交换三角形——三个恒等式、两个生成元和一个复合。这是在三个节点上的 [ordinal_free]，其目标 [Ordinal 3] 是 Instance/Ordinal.v 中的 [_3]；它是一个实例，而不是二次发展。
*)
Definition chain_free : FreeOnQuiver (LinQuiver 3) ≅[StrictCat] _3 :=
  ordinal_free 3.

Definition chain_e0 : ord3_0 ~{FreeOnQuiver (LinQuiver 3)}~> ord3_1 :=
  tlist_singleton (eq_refl : @linear_edges 3 ord3_0 ord3_1).

Definition chain_e1 : ord3_1 ~{FreeOnQuiver (LinQuiver 3)}~> ord3_2 :=
  tlist_singleton (eq_refl : @linear_edges 3 ord3_1 ord3_2).

Definition chain_e10 : ord3_0 ~{FreeOnQuiver (LinQuiver 3)}~> ord3_2 :=
  chain_e1 ∘ chain_e0.

(*
 The composite is literally the two-edge path, not a further generator. 

 --------
 复合物字面上的意思是双边路径，而不是进一步的生成器。
*)
Lemma chain_e0_length : tlist_length chain_e0 = 1%nat.
Proof. reflexivity. Qed.

Lemma chain_e1_length : tlist_length chain_e1 = 1%nat.
Proof. reflexivity. Qed.

Lemma chain_e10_length : tlist_length chain_e10 = 2%nat.
Proof. reflexivity. Qed.

(* The three ascending hom-sets are singletons ... / 三个上升的同宿集是单例集 ... *)
Theorem chain_hom_01 (p : ord3_0 ~{FreeOnQuiver (LinQuiver 3)}~> ord3_1) :
  p ≈ chain_e0.
Proof. apply linear_free_thin. Qed.

Theorem chain_hom_12 (p : ord3_1 ~{FreeOnQuiver (LinQuiver 3)}~> ord3_2) :
  p ≈ chain_e1.
Proof. apply linear_free_thin. Qed.

Theorem chain_hom_02 (p : ord3_0 ~{FreeOnQuiver (LinQuiver 3)}~> ord3_2) :
  p ≈ chain_e10.
Proof. apply linear_free_thin. Qed.

(*
 ... the three diagonal ones contain only the identity ... 

 --------
 ... 三个对角线上的只包含单位元 ...
*)
Theorem chain_hom_00 (p : ord3_0 ~{FreeOnQuiver (LinQuiver 3)}~> ord3_0) :
  p ≈ id.
Proof. apply linear_free_thin. Qed.

Theorem chain_hom_11 (p : ord3_1 ~{FreeOnQuiver (LinQuiver 3)}~> ord3_1) :
  p ≈ id.
Proof. apply linear_free_thin. Qed.

Theorem chain_hom_22 (p : ord3_2 ~{FreeOnQuiver (LinQuiver 3)}~> ord3_2) :
  p ≈ id.
Proof. apply linear_free_thin. Qed.

(* ... and the three descending ones are empty. / ...而那三个下降的都是空的。 *)
Theorem chain_no_10 (p : ord3_1 ~{FreeOnQuiver (LinQuiver 3)}~> ord3_0) : False.
Proof. pose proof (linear_no_descent _ _ p) as H; simpl in H; lia. Qed.

Theorem chain_no_20 (p : ord3_2 ~{FreeOnQuiver (LinQuiver 3)}~> ord3_0) : False.
Proof. pose proof (linear_no_descent _ _ p) as H; simpl in H; lia. Qed.

Theorem chain_no_21 (p : ord3_2 ~{FreeOnQuiver (LinQuiver 3)}~> ord3_1) : False.
Proof. pose proof (linear_no_descent _ _ p) as H; simpl in H; lia. Qed.

(*
 Instance/Ordinal.v's duplicate-free count of endpoint pairs, re-exported at
 n = 3 for the reader's convenience.  NOTE what this is and is not: the
 statement mentions neither [FreeOnQuiver] nor [chain_free], and no transport
 along the isomorphism is formalized -- it is a fact about [Ordinal 3] alone,
 whose left side is TWICE the morphism count (six).  The free category's own
 six morphisms are delivered by the nine hom-set theorems above, directly. 

 --------
 Instance/Ordinal.v 中的端点对无重复计数，在 n = 3 时重新导出以方便读者。注意这是什么以及不是什么：该声明既未提到 [FreeOnQuiver]，也未提到 [chain_free]，并且沿同构的任何传输都未被形式化——它只是关于 [Ordinal 3] 本身的一个事实，其左侧是态射计数的两倍（六）。自由范畴自身的六个态射是由上面的九个 Hom 集定理直接提供的。
*)
Corollary chain_morphism_count : (2 * length (ord_pairs 3) = 3 * (3 + 1))%nat.
Proof. exact (ord_morphism_count 3). Qed.

(*
 ---------- the walking arrow, hom-set by hom-set ---------- 

 --------
 ---------- 步行箭头，按同态集 ----------
*)

Lemma arrow_path_length : tlist_length arrow_path = 1%nat.
Proof. reflexivity. Qed.

Theorem arrow_hom_XY (p : TwoX ~{FreeOnQuiver ArrowQuiver}~> TwoY) : p ≈ arrow_path.
Proof. apply arrow_free_thin. Qed.

Theorem arrow_hom_XX (p : TwoX ~{FreeOnQuiver ArrowQuiver}~> TwoX) : p ≈ id.
Proof. apply arrow_free_thin. Qed.

Theorem arrow_hom_YY (p : TwoY ~{FreeOnQuiver ArrowQuiver}~> TwoY) : p ≈ id.
Proof. apply arrow_free_thin. Qed.

Theorem arrow_no_YX (p : TwoY ~{FreeOnQuiver ArrowQuiver}~> TwoX) : False.
Proof.
  pose proof (graded_no_path ArrowQuiver arrow_rank arrow_edge_rank _ _ p) as H.
  simpl in H; lia.
Qed.

(*
 Non-degeneracy.  The generating path cannot be compared with an identity
 directly -- they inhabit different hom-sets -- so the statement is that it is
 not invertible: an inverse would be a path TwoY to TwoX, and there is none.
 The free category on one arrow is therefore not a groupoid, matching
 [TwoXY_not_iso] (Instance/Two.v) across [arrow_free].  This is one instance;
 the general fact that a free category has only identity isomorphisms is
 issue #802's, and is not proved here. 

 --------
 非退化性。生成路径不能与恒等式直接比较——它们属于不同的同态集合——所以陈述的是它不可逆：一个逆元素将是从 TwoY 到 TwoX 的路径，但不存在这样的路径。因此，一个在一条箭头上的自由范畴不是群范畴，这与 [TwoXY_not_iso]（Instance/Two.v）在 [arrow_free] 中的情况相符。这是一个实例；自由范畴仅具有恒等同构的普遍事实是问题 #802 的主题，这里没有证明。
*)
Lemma arrow_path_not_iso :
  @IsIsomorphism (FreeOnQuiver ArrowQuiver) TwoX TwoY arrow_path → False.
Proof. intros [g _ _]; exact (arrow_no_YX g). Qed.

(*
 ---------- [Ordinal 2] and [_2] agree strictly ---------- 

 --------
 ---------- [Ordinal 2] 和 [_2] 严格一致 ----------
*)

Lemma ord2_to_from_obj (a : TwoObj) : ord_two_of (ord_val (ord2_obj a)) = a.
Proof. now destruct a. Qed.

Lemma ord2_from_to_obj (x : Ord_obj 2) : ord2_obj (ord_two_of (ord_val x)) = x.
Proof. apply ord_obj_eq, ord_2_val. Qed.

(*
 Instance/Ordinal.v delivers [Ordinal_2_iso] only in [Cat].  Both categories
 are thin, so the strict form costs nothing beyond the two object equalities
 -- which are exactly the lemmas that file already proves. 

 --------
 Instance/Ordinal.v 仅在 [Cat] 中提供 [Ordinal_2_iso]。这两个类别都很薄，因此严格形式除了两个对象等式之外没有额外成本——而这正是该文件已经证明的引理。
*)
Program Definition Ordinal_2_strict_iso : Ordinal 2 ≅[StrictCat] _2 := {|
  to   := Ordinal_2_to;
  from := Ordinal_2_from
|}.
Next Obligation.
  exists ord2_to_from_obj; intros a b f; apply ord_two_thin.
Qed.
Next Obligation.
  exists ord2_from_to_obj; intros x y f; apply le_t_irr.
Qed.

(*
 The walking arrow again, reached through the general theorem at two nodes.
 The free category is built on a DIFFERENT quiver -- [LinQuiver 2], whose
 nodes are the objects of [Ordinal 2] -- so this does not subsume
 [arrow_free], whose comparison functors are the identity on objects; the two
 are separate presentations of the same shape. 

 --------
 那个行走的箭头再次，通过两个节点达到了通用定理。
 自由范畴建立在一个不同的箭图上 —— [LinQuiver 2]，其节点是 [Ordinal 2] 的对象 —— 所以这并不包括 [arrow_free]，其比较函子在对象上是恒等的；这两者是相同形状的不同表示。
*)
Definition linear_2_free : FreeOnQuiver (LinQuiver 2) ≅[StrictCat] _2 :=
  iso_compose Ordinal_2_strict_iso (ordinal_free 2).
