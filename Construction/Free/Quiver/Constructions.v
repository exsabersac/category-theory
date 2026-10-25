Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.StrictCat.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Free.Quiver.

Generalizable All Variables.

(** * Opposite and product quivers / * 对偶与乘积箭图 *)

(*
 Mac Lane, "Categories for the Working Mathematician", 2nd ed., §II.7
 Exercise 1, printed p. 51 (PDF p. 61); catalog item [maclane:II.7:ex1].  The
 exercise as the catalog records it — this is the CATALOG'S PARAPHRASE, not
 Mac Lane's own wording — asks one to

 "Define 'opposite graph' and 'product of two graphs' so as to agree with
 the corresponding definitions for categories, i.e. so that the forgetful
 functor U : Cat -> Grph preserves opposites and products."

 (doc/plan/books/maclane/inventory/II.json).  So the mathematical content is
 not the two constructions on their own — either is a two-line reindexing —
 but the AGREEMENT: the definitions are constrained by the requirement that
 the underlying-graph functor carry one to the other.  Everything below is
 therefore organised around the two comparison statements, and each is
 reported at the exact strength it achieves.

 nLab: https://ncatlab.org/nlab/show/quiver

 Mac Lane's "graph" here is what the literature now calls a quiver or a
 directed multigraph: a set of nodes together with, for each ordered pair, a
 set of edges.  [Construction/Free/Quiver.v] indexes the edges directly by
 their endpoints ([edges X Y]) rather than carrying source and target maps
 out of a single edge set, and that encoding is what makes this exercise
 cheap: reversing every edge is the reindexing [fun x y => edges y x], which
 moves no data and needs no equality on nodes, so no transport and no UIP
 hypothesis appears anywhere in this file.  A presentation with an edge set
 and two maps s, t : E -> V would instead have to exhibit the opposite graph
 as the same E with s and t exchanged, and the comparison with [C^op] would
 then be an isomorphism rather than an identity.

 WHAT IS PROVED, AND AT WHAT STRENGTH.  All measurements below were taken,
 not estimated; the file states each one as a Coq term so that the claim and
 its evidence are the same object.

 (1) Both preservation statements hold at LEIBNIZ EQUALITY OF THE WHOLE
 [Quiver] RECORD, by [eq_refl]:

 QuiverOfCat (C^op)   = QuiverOp   (QuiverOfCat C)
 QuiverOfCat (C ∏ D)  = QuiverProd (QuiverOfCat C) (QuiverOfCat D)

 and likewise when phrased through the functor itself, as
 [Forgetful_preserves_op] and [Forgetful_preserves_prod], since
 [fobj[Forgetful]] is [QuiverOfCat] on the nose ([Forgetful_fobj]).  This
 is the strongest of the three outcomes the issue asks to distinguish —
 whole-record equality, not field-by-field, and not merely an isomorphism
 in [QuiverCategory].  Three separate facts conspire to allow it:
 [QuiverOfCat] carries no [Program] obligation (it elaborates with the
 setoid field inlined as [fun X Y => homset X Y]); [Opposite] and
 [Product] are plain [Definition]s whose fields are explicit terms; and
 [Quiver] has primitive projections with eta conversion, so convertible
 fields suffice.

 (2) Preservation also holds ON ARROWS for the opposite, again by [eq_refl]
 ([Forgetful_preserves_op_fmap]): [Forgetful]'s action on a functor is
 [QuiverHomomorphismOfFunctor], and [Functor/Opposite.v]'s
 [Opposite_Functor] is a plain [Definition] with explicit fields.  On the
 product side the corresponding arrow-level statements are the images of
 the projections, and those are only [≈] — see (5).

 (3) The opposite is a DEFINITIONAL INVOLUTION, [QuiverOp_invol] by [eq_refl],
 both on quivers and on homomorphisms ([QuiverOp_map_invol]).  Contrast
 [Construction/Opposite.v]'s [op_invol], which is [Qed]-opaque; here
 record eta makes the doubly-reversed quiver convertible to the original,
 so no isomorphism is needed.

 (4) The product projections, the pairing, and BOTH TRIANGLES hold at Leibniz
 equality ([QuiverPair_Fst], [QuiverPair_Snd], by [eq_refl]), and the
 pairing satisfies the eta law [QuiverPair_eta] at [≈].  Together these
 give a genuine universal property, [QuiverPair_unique] — but read its
 hypotheses precisely: they are stated at LEIBNIZ EQUALITY of the two
 composites, not at [≈].  Upgrading them would require respectfulness of
 [QuiverPair] in its two arguments with respect to
 [QuiverHomomorphismEquivalence], which is NOT proved here (it is the
 usual transport bookkeeping over a node-equality family; nothing below
 needs it).  So: a universal property is proved, with hypotheses stronger
 than the [≈]-form a reader might assume.  No claim is made that
 [QuiverProd] is the categorical product in [QuiverCategory].

 The clause is not vacuous — [QuiverPair_Fst]/[_Snd] satisfy its
 hypotheses — and it is not trivial either: eta is NOT definitional, so
 the hypotheses do not simply reduce away (Test/ProbeQuiverConstructions.v
 pins that).  What is NOT supplied is a competitor: no homomorphism into a
 product is exhibited that FAILS the two triangles, so the clause's
 discriminating power is disclosed rather than witnessed.  Doing so needs a
 concrete quiver with two distinct nodes, which nothing here otherwise
 requires.

 (5) Two statements are measured and found NOT to reach [eq_refl], and are
 delivered at [≈] in [QuiverCategory]'s hom-setoid instead.  Both
 measurements are pinned in the build by Test/ProbeQuiverConstructions.v,
 which states each strengthening as a [Fail] command paired with a
 positive control, so the boundary this file's headline rests on is
 guarded rather than merely recorded here:

 [Forgetful_preserves_fst]/[_snd] — [Fst] and [Snd] of
 [Construction/Product.v] are [Program Instance]s, so their
 [fmap_respects] field is an opaque obligation (the tree runs
 [Unset Transparent Obligations], Lib/Tactics.v) and cannot be
 convertible to this file's explicit term.

 [QuiverSwap_invol] — the node action of the twice-swapped quiver is
 [fun x => (fst x, snd x)], and surjective pairing is not definitional
 for the standard library's [prod].

 Both negative results are checked by machine, not assumed, and both are
 re-checked on every build.  Each fails by genuine CONVERSION failure
 ("cannot unify"), not by an unrelated elaboration or scope error — the
 distinction matters, since a [Fail] passes just as happily on an
 ill-formed term, which is why the probe file pairs every negative with a
 control that must succeed.

 WHY A NEW FILE.  The issue offers "extend Quiver.v OR add
 Constructions.v".  Quiver.v is a heavily depended-on donor — it carries the
 free/forgetful adjunction, and eight files require it (Free/Quiver's own
 Concrete.v, Examples.v and Presented.v, plus Construction/Free/TwoFunctors.v,
 Instance/Roster.v, Test/Issue138.v, Theory/Diagram.v and Theory/OGraph.v) —
 so a new file keeps the blast radius at zero: nothing existing is touched
 except the [_CoqProject] line that registers this one.

 NOT THE COMPOSABLE-PAIRS PRODUCT.  Theory/OGraph.v is the other §II.7 file
 that multiplies graphs, and the two products are unrelated.  There the node
 set O is FIXED, and A ×_O B has as its arrows the composable pairs <g, f>;
 that product is not symmetric, its unit is the trivial O-graph, and its
 point is to exhibit a category as a monoid.  Here the nodes VARY and the
 product is the cartesian one, pairs of nodes and pairs of edges.  The two do
 not specialise to one another, and OGraph.v says in terms that it defines no
 varying-node product ("No [Grph]-level (varying-node) product is defined"),
 which is the gap this file fills; conversely nothing here bears on ×_O.

 A SMALL HISTORICAL NOTE the issue points out and this file finally acts on:
 Quiver.v has required [Construction.Opposite] and [Construction.Product]
 since its introduction WITHOUT USING EITHER (Quiver.v; neither name
 occurs in its body).  Those two imports are exactly what this exercise
 needs, so the requirement is at last discharged rather than removed.

 UNIVERSES.  [QuiverOp] and [QuiverProd] are declared with explicit universe
 binders, and neither collapses anything: [QuiverOp@{o h p}] preserves the
 three levels of [Quiver], and [QuiverOp_invol@{o h p}] carries an EMPTY
 constraint clause.  The two preservation lemmas, however, each carry

 h = p       (and, on the product side, also  h1 = p1  and  h2 = p2)

 identifying a category's hom and proof universes.  This is INHERITED FROM
 THE DONORS and is not introduced here: [Construction/Opposite.v]'s
 [Opposite@{u u0} : Category@{u0 u u} -> Category@{u0 u u}] already
 identifies them, as does [Construction/Product.v]'s [Product], whose two
 arguments elaborate at [Category@{u1 u2 u2}] and [Category@{u3 u4 u4}].
 Measured: the bare term [fun (C : Category@{o h p}) => C^op], mentioning
 nothing from this file, already forces [h = p], whereas
 [fun (C : Category@{o h p}) => QuiverOfCat C] carries only [h <= p].  The
 printed statements show the cause directly — [Opposite.Opposite@{h o}] takes
 two universe arguments and [Product.Product@{o h o1 h1 o2 h2}] six, where
 nine would be needed to keep the three levels of both factors apart.

 The HOMOMORPHISMS below are less universe-general than the two quivers, and
 this too is measured rather than glossed.  [QuiverFst@{o1 h1 p1 o2 h2 p2
 o h p}] carries [h1 = h] and [p1 = p], identifying the product's edge and
 proof levels with the FIRST factor's, and [QuiverPair@{u u0 u1 u2 u3 u4 u5}]
 shares one edge level and one proof level across its three quivers.  These
 are identifications AMONG EDGE LEVELS and are a different phenomenon from
 the hom/proof collapse of the preceding paragraph; nothing in this file
 needs the extra generality, and no attempt was made to recover it.  The
 scope of this whole disclosure is the constants named in it and no others.

 WHAT IS NOT BUILT.  [QuiverOp] is not packaged as an endofunctor of
 [QuiverCategory] (the object and arrow maps are here as [QuiverOp] and
 [QuiverOp_map], with the involution both ways, but no [Functor] record and
 no [Forgetful]-commutes-with-it natural comparison); [QuiverProd] is not
 packaged as a bifunctor, and no [Cartesian QuiverCategory] instance is
 claimed; and the [≈]-hypothesis form of [QuiverPair_unique] is open, per
 (4).  None of these is needed by the exercise. 

 --------
 Mac Lane，《工作数学家的范畴论》，第2版，§II.7 练习1，印刷本第51页（PDF第61页）；目录编号 [maclane:II.7:ex1]。 该练习按照目录记录的方式——这是目录的意译，并非 Mac Lane 本人的原话——要求：

 “定义‘对偶图’和‘两个图的积’，使其与范畴的相应定义一致，即使忘记函子 U : Cat -> Grph 保持对偶和积。”(doc/plan/books/maclane/inventory/II.json)。所以数学内容不是两个构造本身——任意一个都是两行重索引——而是**一致性**：定义受到基础图函子将一个映射到另一个的要求的约束。因此下面的一切都是围绕两个比较陈述组织的，每一个都按其达到的确切强度报告。

 nLab: https://ncatlab.org/nlab/show/quiver这里马克·莱恩（Mac Lane）的“图”是文献中现在称为箭图（quiver）或有向多重图的东西：一组节点，并且对于每一个有序节点对，有一组边。[Construction/Free/Quiver.v] 直接通过它们的端点（[edges X Y]）来索引边，而不是从单一的边集合中携带源和目标映射，而这种编码方式使这个练习变得简单：反转每一条边就是重新索引 [fun x y => edges y x]，它不移动任何数据，也不需要节点上的等式，因此文件中没有出现移动（transport）和 UIP 假设。具有边集合和两个映射 s, t : E -> V 的表示，将不得不以相同的 E 但交换 s 和 t 来展示对偶图，然后与 [C^op] 的比较将是同构而不是恒等。已证明的内容及其强度。下面的所有测量都是实测的，而非估计；文件将每一个测量都以 Coq 术语列出，因此声明及其证据是同一个对象。

 (1) 两个保持性声明在整个 [Quiver] 记录的 莱布尼茨等式 下成立，依据 [eq_refl]：

 QuiverOfCat (C^op)   = QuiverOp   (QuiverOfCat C)
 QuiverOfCat (C ∏ D)  = QuiverProd (QuiverOfCat C) (QuiverOfCat D)同样，当通过函子本身表达时，如 [Forgetful_preserves_op] 和 [Forgetful_preserves_prod]，因为 [fobj[Forgetful]] 完全等于 [QuiverOfCat]（[Forgetful_fobj]）。这是问题要求区分的三种结果中最强的一种——整个记录的相等，而不是按字段逐一比较，也不仅仅是在 [QuiverCategory] 中的同构。三个独立的事实共同作用使其成为可能：[QuiverOfCat] 没有 [Program] 义务（它以内联为 [fun X Y => homset X Y] 的集合字段进行详细说明）；[Opposite] 和 [Product] 是普通 [Definition]，它们的字段是显式项；并且 [Quiver] 有带有 eta 转换的原始投影，因此可转换的字段就足够了。(2) 保存性也适用于箭头的对偶，同样由 [eq_refl]（[Forgetful_preserves_op_fmap]）给出：[Forgetful] 对函子上的作用是 [QuiverHomomorphismOfFunctor]，而 [Functor/Opposite.v] 的 [Opposite_Functor] 是一个带有显式字段的普通 [Definition]。在乘积侧，相应的箭头级陈述是投影的像，并且它们只是 [≈]——见（5）。

 (3) 对偶是一个定义上的反演，由 [eq_refl] 在 [QuiverOp_invol] 上进行，无论是在图（quiver）还是在同态（[QuiverOp_map_invol]）上。对比 [Construction/Opposite.v] 的 [op_invol]，它是 [Qed] 不透明的；这里记录 eta 使得双重反转的图可转换回原始图，因此不需要同构。(4) 在莱布尼茨等式下，乘积投影、配对以及两个三角形保持不变（[QuiverPair_Fst]，[QuiverPair_Snd]，由[eq_refl]），并且配对在[≈]处满足eta律[QuiverPair_eta]。综合这些给出了一个真正的泛性质[QuiverPair_unique]——但要精确阅读其前提：它们是在两个复合的莱布尼茨等式下陈述的，而不是在[≈]下。对它们进行升级将需要[QuiverPair]在其两个参数上相对于[QuiverHomomorphismEquivalence]的相容性，这在此处没有证明（这是关于节点等式族的通常搬运账目；以下内容不需要它）。所以：证明了一个泛性质，其前提比读者可能假设的[≈]形式要强。没有声称 [QuiverProd] 是 [QuiverCategory] 中的范畴积。

 该条款并非空洞——[QuiverPair_Fst] / [_Snd] 满足其假设——也并非微不足道：eta 不是定义性的，因此假设不会简单消失（Test/ProbeQuiverConstructions.v 已验证这一点）。没有提供的是竞争者：没有展示到积的同态会违背两个三角形，因此该条款的区分能力是被揭示的，而非被证明的。要做到这一点，需要一个具有两个不同节点的具体层图，而这里没有其他地方要求这样做。(5) 两个语句被测量后发现没有达到 [eq_refl]，而是在 [QuiverCategory] 的同态集合中以 [≈] 的形式传递。两个测量都在 Test/ProbeQuiverConstructions.v 构建中被固定，该文件将每个增强声明为与正控制配对的 [Fail] 命令，因此该文件标题所在的边界是受保护的，而不仅仅是在此记录：

 [Forgetful_preserves_fst] / [_snd] — [Construction/Product.v] 的 [Fst] 和 [Snd] 是 [Program Instance]，因此它们的 [fmap_respects] 字段是一个不透明的义务（树运行 [Unset Transparent Obligations]，Lib/Tactics.v），并且不能转换为此文件的显式表达式。[QuiverSwap_invol] — 双重交换箭袋的节点操作是 [fun x => (fst x, snd x)]，而标准库的 [prod] 并没有定义满射配对。

 这两个负面结果都是由机器检查的，而非假设，并且在每次构建时都会重新检查。每个失败都是由于真正的 CONVERSION 失败（“无法统一”），而不是由于无关的展开或作用域错误——这个区别很重要，因为 [Fail] 在一个格式不正确的项上也同样能成功，这就是为什么探测文件将每个负面结果都与一个必须成功的对照配对。为什么要新建文件。这个问题提供了“扩展 Quiver.v 或添加 Constructions.v”。Quiver.v 是一个依赖非常多的源文件——它包含自由/忘记伴随，以及八个文件需要它（Free/Quiver 自己的 Concrete.v、Examples.v 和 Presented.v，加上 Construction/Free/TwoFunctors.v、Instance/Roster.v、Test/Issue138.v、Theory/Diagram.v 和 Theory/OGraph.v）——所以新建文件可以将影响范围保持为零：除了注册此文件的 [_CoqProject] 行，现有内容没有被修改。不是可组合对积（COMPOSABLE-PAIRS PRODUCT）。Theory/OGraph.v 是另一个 §II.7 文件，它用于图的乘法，这两个乘积是互不相关的。在那里，节点集合 O 是固定的，而 A ×_O B 的箭头是可组合对 <g, f>；该乘积不是对称的，它的单位是平凡的 O-图，它的目的是将一个范畴展示为一个幺半群（monoid）。这里节点是可变的，乘积是笛卡尔积，即节点对和箭头对。这两者不能互为特例，而 OGraph.v 明确表示它没有定义可变节点的乘积（“No [Grph] -level (varying-node) product is defined”），这个文件正是弥补了这一空白；反之，这里的内容与 ×_O 无关。一个小的历史说明：该问题指出，而此文件最终执行的：
 Quiver.v 自引入以来就需要 [Construction.Opposite] 和 [Construction.Product]
 但从未使用过其中任何一个（Quiver.v；这两个名字都未出现在其主体中）。这两个导入正是本练习所需要的，因此该要求最终被满足，而不是被移除。

 宇宙。[QuiverOp] 和 [QuiverProd] 被声明为显式宇宙绑定器，并且两者都没有折叠任何内容：[QuiverOp@{o h p}] 保留了 [Quiver] 的三个层级，[QuiverOp_invol@{o h p}] 具有空的约束子句。然而，这两个保持性引理各自都包含

 h = p  （在乘积侧，还包括 h1 = p1 和 h2 = p2）识别一个类别的同构和证明宇宙。这是继承自捐赠者的，并未在此引入：[Construction/Opposite.v] 的 [Opposite@{u u0} : Category@{u0 u u} -> Category@{u0 u u}] 已经识别了它们，[Construction/Product.v] 的 [Product] 也是如此，其两个参数在 [Category@{u1 u2 u2}] 和 [Category@{u3 u4 u4}] 处详细说明。测量：裸项 [fun (C : Category@{o h p}) => C^op]，没有提及此文件中的任何内容，已经迫使 [h = p]，而 [fun (C : Category@{o h p}) => QuiverOfCat C] 仅携带 [h <= p]。打印的语句直接显示了原因——[Opposite.Opposite@{h o}] 需要两个宇宙参数，而 [Product.Product@{o h o1 h1 o2 h2}] 需要六个，而为了保持两个因子的三个层次分离，需要九个。下面的同态比两个箭袋的普遍性更低，并且这也是经过测量而不是简单概述的。[QuiverFst@{o1 h1 p1 o2 h2 p2 o h p}] 具有 [h1 = h] 和 [p1 = p]，将乘积的边级别和证明级别与第一个因子的级别对应，而 [QuiverPair@{u u0 u1 u2 u3 u4 u5}] 在其三个箭袋中共享一个边级别和一个证明级别。这些是边级别之间的识别，与上一段的同态/证明坍塌现象不同；此文件中没有任何内容需要额外的通用性，也未尝试恢复它。本公开的范围仅限于其中命名的常量，而不包括其他。未构建的内容。[QuiverOp] 并未被打包为 [QuiverCategory] 的 endofunctor（对象和箭头映射在此为 [QuiverOp] 和 [QuiverOp_map]，并且双向都有反演，但没有 [Functor] 记录，也没有与 [Forgetful] 自然对比的交换）；[QuiverProd] 并未被打包为 bifunctor，并且未声明 [Cartesian QuiverCategory] 实例；并且 [≈] 形式的 [QuiverPair_unique] 假设是开放的，如 (4) 所示。这些都不是练习所需的。
*)

(*
 NOTATION GUARD.  [C^op] (category_scope, Construction/Opposite.v) and [F^op]
 (functor_scope, Functor/Opposite.v) are the same token, and importing
 Functor/Opposite.v opens functor_scope, so a bare [C^op] in an argument
 position carrying no scope annotation elaborates as the *functor* opposite
 and does not typecheck.  Following the precedent recorded in
 Instance/Rng/Mod.v, category_scope is re-opened here so that [^op] means
 [Opposite] by default, and the functor opposite is named explicitly as
 [Opposite_Functor]. 

 --------
 符号保护。[C^op]（category_scope, Construction/Opposite.v）和[F^op]（functor_scope, Functor/Opposite.v）是相同的符号，并且导入Functor/Opposite.v会打开functor_scope，因此在不带作用域注释的参数位置的裸[C^op]会被展开为*函子*对偶，并且无法进行类型检查。根据Instance/Rng/Mod.v中记录的先例，这里重新打开category_scope，因此[^op]默认意味着[Opposite]，而函子对偶则明确命名为[Opposite_Functor]。
*)
Local Open Scope category_scope.

Local Notation "Q ⇨ Q'" := (QuiverHomomorphism Q Q') (at level 40).
Local Existing Instance edgeset.

(** ** The opposite quiver / ** 相反的颤抖 *)

Section OppositeQuiver.

(*
 Same nodes, every edge reversed.  The endpoint-indexed encoding makes this a
 pure reindexing: [edges y x] is already a type, so nothing is transported
 and no equality on nodes is consumed. 

 --------
 相同的节点，每条边都反向。端点索引编码使这成为纯重索引：[edges y x] 已经是一种类型，因此没有任何内容被传输，也没有消耗节点的相等性。
*)
Definition QuiverOp@{o h p} (G : Quiver@{o h p}) : Quiver@{o h p} := {|
  nodes   := @nodes G;
  edges   := fun x y => @edges G y x;
  edgeset := fun x y => @edgeset G y x
|}.

(*
 What the three fields unfold to, recorded rather than described. 

 --------
 三块田地展开的景象，被记录而非描述。
*)
Definition QuiverOp_nodes@{o h p} (G : Quiver@{o h p}) :
  @nodes (QuiverOp G) = @nodes G := eq_refl.

Definition QuiverOp_edges@{o h p} (G : Quiver@{o h p}) (x y : @nodes G) :
  @edges (QuiverOp G) x y = @edges G y x := eq_refl.

Definition QuiverOp_edgeset@{o h p} (G : Quiver@{o h p}) (x y : @nodes G) :
  @edgeset (QuiverOp G) x y = @edgeset G y x := eq_refl.

(*
 Involution, at Leibniz equality of the whole [Quiver] record.  [Quiver] has
 primitive projections with eta conversion, so the doubly-reversed record is
 convertible to [G] itself rather than merely isomorphic to it. 

 --------
 内卷，在莱布尼茨意义上是整个 [Quiver] 记录的平等。[Quiver] 具有带有 eta 转换的原始投影，因此双重反转的记录可以转换为 [G] 本身，而不仅仅是与它同构。
*)
Definition QuiverOp_invol@{o h p} (G : Quiver@{o h p}) :
  QuiverOp (QuiverOp G) = G := eq_refl.

(*
 Reversal on homomorphisms: the node action is unchanged and the edge action
 is the same family read at swapped indices. 

 --------
 同态的逆转：节点操作保持不变，边操作是在交换的索引处读取的相同族。
*)
Definition QuiverOp_map@{o1 h1 p1 o2 h2 p2}
  {G : Quiver@{o1 h1 p1}} {G' : Quiver@{o2 h2 p2}} (F : G ⇨ G') :
  QuiverOp G ⇨ QuiverOp G' :=
  Build_QuiverHomomorphism (QuiverOp G) (QuiverOp G')
    (@fnodes _ _ F)
    (fun x y => @fedgemap _ _ F y x)
    (fun x y => @fedgemap_respects _ _ F y x).

Definition QuiverOp_map_invol@{o1 h1 p1 o2 h2 p2}
  {G : Quiver@{o1 h1 p1}} {G' : Quiver@{o2 h2 p2}} (F : G ⇨ G') :
  QuiverOp_map (QuiverOp_map F) = F := eq_refl.

End OppositeQuiver.

(** ** The product quiver / ** 产品箭袋 *)

Section ProductQuiver.

(*
 The componentwise setoid on a product of edge sets.  Two points about the
 spelling, both of them measured rather than stylistic.

 First, the three [Equivalence] fields are written out as explicit terms
 rather than discharged by a tactic or by [Program].  The tree runs
 [Unset Transparent Obligations] (Lib/Tactics.v), so an obligation-built
 equivalence proof is an opaque constant, and [Setoid] has primitive
 projections with eta — conversion therefore compares the [setoid_equiv]
 fields, and an opaque one defeats the definitional agreement recorded in
 [QuiverOfCat_Product].  The spelling deliberately mirrors
 Construction/Product.v.

 Second, this is NOT [Lib/Datatypes.v]'s [prod_setoid], which is a global
 [Program Instance] with exactly this [equiv] but an opaque [setoid_equiv];
 substituting it here breaks [QuiverOfCat_Product].  That is a deliberate
 non-reuse, so it is guarded rather than merely stated:
 Test/ProbeQuiverConstructions.v builds the [prod_setoid] variant (which is a
 perfectly good quiver — only the DEFINITIONAL agreement is lost) and pins the
 resulting failure. 

 --------
 在边集的乘积上的分量集合等价。关于拼写，有两点需要说明，它们都是从测量角度出发，而非风格上的考虑。

 首先，三个 [Equivalence] 字段是以显式项写出的，而不是通过 tactic 或 [Program] 来消解的。该树运行 [Unset Transparent Obligations]（Lib/Tactics.v），因此一个由义务构建的等价证明是一个不透明常数，而 [Setoid] 有带 eta 的原始投影——因此转换会比较 [setoid_equiv] 字段，而不透明项会破坏 [QuiverOfCat_Product] 中记录的定义性一致性。拼写故意与 Construction/Product.v 相呼应。其次，这不是 [Lib/Datatypes.v] 的 [prod_setoid]，它是一个全局的 [Program Instance]，具有完全相同的 [equiv]，但具有不透明的 [setoid_equiv]；在这里替换它会破坏 [QuiverOfCat_Product]。这是有意的不重复使用，因此它是有保护的，而不仅仅是陈述：Test/ProbeQuiverConstructions.v 构建了 [prod_setoid] 变体（它是一个完全有效的箭袋——只是丢失了定义上的一致性）并固定了由此产生的失败。
*)
Definition edgeset_prod@{h1 p1 h2 p2 h p}
  {A : Type@{h1}} {B : Type@{h2}}
  (SA : Setoid@{h1 p1} A) (SB : Setoid@{h2 p2} B) : Setoid@{h p} (A * B) := {|
  equiv := fun f g =>
    (@equiv _ SA (fst f) (fst g) * @equiv _ SB (snd f) (snd g));
  setoid_equiv :=
    {| Equivalence_Reflexive := fun x =>
         (@Equivalence_Reflexive _ _ (@setoid_equiv _ SA) (fst x),
          @Equivalence_Reflexive _ _ (@setoid_equiv _ SB) (snd x))
     ; Equivalence_Symmetric := fun x y f =>
         (@Equivalence_Symmetric _ _ (@setoid_equiv _ SA) (fst x) (fst y) (fst f),
          @Equivalence_Symmetric _ _ (@setoid_equiv _ SB) (snd x) (snd y) (snd f))
     ; Equivalence_Transitive := fun x y z f g =>
         (@Equivalence_Transitive _ _ (@setoid_equiv _ SA)
            (fst x) (fst y) (fst z) (fst f) (fst g),
          @Equivalence_Transitive _ _ (@setoid_equiv _ SB)
            (snd x) (snd y) (snd z) (snd f) (snd g)) |}
|}.

(*
 Nodes are pairs, edges are pairs of edges with matching endpoints, and the
 edge setoid is componentwise. 

 --------
 节点是成对的，边是具有匹配端点的边对，并且边集合是按组件定义的。
*)
Definition QuiverProd@{o1 h1 p1 o2 h2 p2 o h p}
  (G : Quiver@{o1 h1 p1}) (H : Quiver@{o2 h2 p2}) : Quiver@{o h p} := {|
  nodes   := (@nodes G * @nodes H)%type;
  edges   := fun x y =>
    (@edges G (fst x) (fst y) * @edges H (snd x) (snd y))%type;
  edgeset := fun x y =>
    edgeset_prod (@edgeset G (fst x) (fst y)) (@edgeset H (snd x) (snd y))
|}.

Definition QuiverProd_nodes@{o1 h1 p1 o2 h2 p2 o h p}
  (G : Quiver@{o1 h1 p1}) (H : Quiver@{o2 h2 p2}) :
  @nodes (QuiverProd@{o1 h1 p1 o2 h2 p2 o h p} G H)
    = (@nodes G * @nodes H)%type := eq_refl.

Definition QuiverProd_edges@{o1 h1 p1 o2 h2 p2 o h p}
  (G : Quiver@{o1 h1 p1}) (H : Quiver@{o2 h2 p2})
  (x y : @nodes G * @nodes H) :
  @edges (QuiverProd@{o1 h1 p1 o2 h2 p2 o h p} G H) x y
    = (@edges G (fst x) (fst y) * @edges H (snd x) (snd y))%type := eq_refl.

(* The two projections, as quiver homomorphisms. / 作为箭袋同态的两个投影。 *)
Definition QuiverFst@{o1 h1 p1 o2 h2 p2 o h p}
  {G : Quiver@{o1 h1 p1}} {H : Quiver@{o2 h2 p2}} :
  QuiverProd@{o1 h1 p1 o2 h2 p2 o h p} G H ⇨ G :=
  Build_QuiverHomomorphism (QuiverProd G H) G
    fst
    (fun x y => fst)
    (fun x y f g e => fst e).

Definition QuiverSnd@{o1 h1 p1 o2 h2 p2 o h p}
  {G : Quiver@{o1 h1 p1}} {H : Quiver@{o2 h2 p2}} :
  QuiverProd@{o1 h1 p1 o2 h2 p2 o h p} G H ⇨ H :=
  Build_QuiverHomomorphism (QuiverProd G H) H
    snd
    (fun x y => snd)
    (fun x y f g e => snd e).

(* The pairing of two homomorphisms with a common source. / 具有共同来源的两个同态的配对。 *)
Definition QuiverPair
  {K G H : Quiver} (F : K ⇨ G) (F' : K ⇨ H) : K ⇨ QuiverProd G H :=
  Build_QuiverHomomorphism K (QuiverProd G H)
    (fun x => (F x, F' x))
    (fun x y e => (@fedgemap _ _ F x y e, @fedgemap _ _ F' x y e))
    (fun x y f g e =>
       (@fedgemap_respects _ _ F x y f g e, @fedgemap_respects _ _ F' x y f g e)).

(* Exchange of the two factors. / 交换这两个因素。 *)
Definition QuiverSwap {G H : Quiver} : QuiverProd G H ⇨ QuiverProd H G :=
  Build_QuiverHomomorphism (QuiverProd G H) (QuiverProd H G)
    (fun x => (snd x, fst x))
    (fun x y e => (snd e, fst e))
    (fun x y f g e => (snd e, fst e)).

(*
 Swap is the pairing of the two projections in the other order — recorded by
 [eq_refl] rather than asserted. 

 --------
 Swap 是将两个投影以相反顺序配对 —— 由 [eq_refl] 记录而不是断言。
*)
Definition QuiverSwap_is_pair {G H : Quiver} :
  @QuiverSwap G H = QuiverPair QuiverSnd QuiverFst := eq_refl.

End ProductQuiver.

(* * ** The universal property of the product quiver / * ** 乘积向箭宿的泛性质 *)

Section ProductUniversal.

Context {K G H : Quiver}.

(*
 Both triangles hold at LEIBNIZ EQUALITY of the whole homomorphism record,
 not merely up to [≈].  The composite's [fedgemap_respects] field reduces —
 [QuiverFst]'s is [fun _ _ _ _ e => fst e] and [QuiverPair]'s is the explicit
 pair of the two given proofs, so [fst] of the pair is the first one back. 

 --------
 两个三角形在整个同态记录的莱布尼茨相等下成立，而不仅仅是在 [≈] 下。复合的 [fedgemap_respects] 字段减少——[QuiverFst] 的是 [fun _ _ _ _ e => fst e]，[QuiverPair] 的是两个给定证明的显式对，因此这对的 [fst] 是第一个返回的。
*)
Definition QuiverPair_Fst (F : K ⇨ G) (F' : K ⇨ H) :
  @compose QuiverCategory K (QuiverProd G H) G QuiverFst (QuiverPair F F') = F
  := eq_refl.

Definition QuiverPair_Snd (F : K ⇨ G) (F' : K ⇨ H) :
  @compose QuiverCategory K (QuiverProd G H) H QuiverSnd (QuiverPair F F') = F'
  := eq_refl.

(*
 The eta law.  Here [≈] is genuinely needed: the node action of the rebuilt
 pairing is [fun x => (fst (M x), snd (M x))], and surjective pairing is not
 definitional for the standard library's [prod]. 

 --------
 Eta 定律。这里真正需要 [≈]：重建配对的节点操作是 [fun x => (fst (M x), snd (M x))]，而对于标准库的 [prod]，满射配对并不是定义性的。
*)
Definition QuiverPair_eta (M : K ⇨ QuiverProd G H) :
  @equiv _ (@homset QuiverCategory K (QuiverProd G H))
    M (QuiverPair (@compose QuiverCategory K (QuiverProd G H) G QuiverFst M)
                  (@compose QuiverCategory K (QuiverProd G H) H QuiverSnd M)).
Proof.
  unshelve eexists.
  - intro x; cbn; destruct (@fnodes _ _ M x); reflexivity.
  - intros x y f; cbn.
    generalize (@fedgemap _ _ M x y f).
    destruct (@fnodes _ _ M x), (@fnodes _ _ M y).
    intro e; cbn; split; reflexivity.
Defined.

(*
 Uniqueness.  READ THE HYPOTHESES: they are Leibniz equalities of the two
 composites, which is what makes the proof a substitution into the eta law.
 The [≈]-hypothesis form would need respectfulness of [QuiverPair] in its two
 arguments, which is not proved in this file (see the header). 

 --------
 唯一性。阅读假设：它们是两个合成的莱布尼茨等式，这正是使证明成为对 eta 法则的代入。[≈] 假设形式需要 [QuiverPair] 在它的两个参数中保持尊重性，这在此文件中没有证明（见头部说明）。
*)
Definition QuiverPair_unique (M : K ⇨ QuiverProd G H) (F : K ⇨ G) (F' : K ⇨ H)
  (p : @compose QuiverCategory K (QuiverProd G H) G QuiverFst M = F)
  (q : @compose QuiverCategory K (QuiverProd G H) H QuiverSnd M = F') :
  @equiv _ (@homset QuiverCategory K (QuiverProd G H)) M (QuiverPair F F').
Proof.
  destruct p, q; exact (QuiverPair_eta M).
Defined.

End ProductUniversal.

(*
 Swapping twice is the identity, up to [≈]; see the header for why this one
 cannot be [eq_refl]. 

 --------
 交换两次是恒等操作，最多只到 [≈]；参见标题了解为什么这个不能是 [eq_refl]。
*)
Definition QuiverSwap_invol {G H : Quiver} :
  @equiv _ (@homset QuiverCategory (QuiverProd G H) (QuiverProd G H))
    (@compose QuiverCategory (QuiverProd G H) (QuiverProd H G) (QuiverProd G H)
       QuiverSwap QuiverSwap)
    (@id QuiverCategory (QuiverProd G H)).
Proof.
  unshelve eexists.
  - intro x; destruct x; reflexivity.
  - intros [a b] [c d] e; cbn; split; reflexivity.
Defined.

(* * ** Preservation by the forgetful functor / * ** 通过忘记函子保持 *)

Section Preservation.

(*
 Mac Lane's exercise proper: the underlying graph of C^op is the opposite of
 the underlying graph of C, and likewise for binary products.  Both hold at
 Leibniz equality of the whole [Quiver] record, by [eq_refl]; see the header
 for the three facts that allow it. 

 --------
 Mac Lane 的例题本身：C^op 的底层图是 C 的底层图的对偶，二元积也是如此。这些在整个 [Quiver] 记录的 Leibniz 等式下都成立，由 [eq_refl] 支持；请参阅标题以了解允许此操作的三个事实。
*)

Definition QuiverOfCat_Opposite@{o h p} (C : Category@{o h p}) :
  QuiverOfCat@{o h p} (C^op) = QuiverOp@{o h p} (QuiverOfCat@{o h p} C) := eq_refl.

Definition QuiverOfCat_Product@{o1 h1 p1 o2 h2 p2 o h p}
  (C : Category@{o1 h1 p1}) (D : Category@{o2 h2 p2}) :
  QuiverOfCat@{o h p} (C ∏ D)
    = QuiverProd@{o1 h1 p1 o2 h2 p2 o h p}
        (QuiverOfCat@{o1 h1 p1} C) (QuiverOfCat@{o2 h2 p2} D) := eq_refl.

(*
 The same two statements phrased through [Forgetful : StrictCat ⟶ Quiv]
 itself, which is what the exercise asks about.  [fobj[Forgetful]] is
 [QuiverOfCat] on the nose, so these are the lemmas above read at StrictCat's
 universe instance. 

 --------
 通过 [Forgetful : StrictCat ⟶ Quiv] 本身表达的相同两条语句，这正是练习所问的。[fobj[Forgetful] ] 正是 [QuiverOfCat]，所以这些是在 StrictCat 的宇宙实例中读取的上述引理。
*)

Definition Forgetful_fobj (C : Category) :
  fobj[Forgetful] C = QuiverOfCat C := eq_refl.

Definition Forgetful_preserves_op (C : Category) :
  fobj[Forgetful] (C^op) = QuiverOp (fobj[Forgetful] C) := eq_refl.

Definition Forgetful_preserves_prod (C D : Category) :
  fobj[Forgetful] (C ∏ D) = QuiverProd (fobj[Forgetful] C) (fobj[Forgetful] D)
  := eq_refl.

(*
 Preservation on arrows as well as objects, for the opposite.  [Forgetful]'s
 action on a functor is [QuiverHomomorphismOfFunctor], and
 [Functor/Opposite.v]'s [Opposite_Functor] is a plain [Definition] with
 explicit fields, so this too is [eq_refl]. 

 --------
 箭头以及对象的保持，对于相反的情况也是如此。[Forgetful] 对函子上的作用是 [QuiverHomomorphismOfFunctor]，并且 [Functor/Opposite.v] 的 [Opposite_Functor] 是一个具有显式字段的普通 [Definition]，所以这也是 [eq_refl]。
*)
Definition Forgetful_preserves_op_fmap
  {C D : Category} (F : C ⟶ D) :
  QuiverHomomorphismOfFunctor _ _ (Opposite_Functor F)
    = QuiverOp_map (QuiverHomomorphismOfFunctor _ _ F) := eq_refl.

(*
 On the product side the arrow-level content is that [Forgetful] carries the
 product projections of [Cat] to the product projections of [Quiv].  This is
 only [≈]: [Fst] and [Snd] are [Program Instance]s whose [fmap_respects]
 field is an opaque obligation, so no [eq_refl] is available. 

 --------
 在产品方面，箭头级内容是 [Forgetful] 将 [Cat] 的产品投影传递到 [Quiv] 的产品投影。这只是 [≈]：[Fst] 和 [Snd] 是 [Program Instance]，其 [fmap_respects] 字段是一个不透明的义务，因此没有 [eq_refl] 可用。
*)
Definition Forgetful_preserves_fst (C D : Category) :
  @equiv _ (@homset QuiverCategory (QuiverOfCat (C ∏ D)) (QuiverOfCat C))
    (QuiverHomomorphismOfFunctor _ _ (@Fst C D))
    (@QuiverFst (QuiverOfCat C) (QuiverOfCat D)).
Proof. exists (fun _ => eq_refl); intros; reflexivity. Defined.

Definition Forgetful_preserves_snd (C D : Category) :
  @equiv _ (@homset QuiverCategory (QuiverOfCat (C ∏ D)) (QuiverOfCat D))
    (QuiverHomomorphismOfFunctor _ _ (@Snd C D))
    (@QuiverSnd (QuiverOfCat C) (QuiverOfCat D)).
Proof. exists (fun _ => eq_refl); intros; reflexivity. Defined.

End Preservation.
