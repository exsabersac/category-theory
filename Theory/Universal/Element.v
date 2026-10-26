Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.UniversalProperty.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Elements.

Generalizable All Variables.

(** * Universal elements / * 普遍元素 *)

(*
nLab: https://ncatlab.org/nlab/show/universal+element
   nLab: https://ncatlab.org/nlab/show/representable+functor
   Wikipedia: https://en.wikipedia.org/wiki/Universal_property

   Mac Lane's Definition 2 of §III.1 (CWM 2nd ed., p. 57): if D is a category
   and H : D ⟶ Set a functor, a UNIVERSAL ELEMENT of H is a pair ⟨r, e⟩
   consisting of an object r of D and an element e ∈ H r such that for every
   pair ⟨d, x⟩ with x ∈ H d there is a unique arrow k : r ~> d of D with
   (H k) e = x.

   That is the ELEMENTARY form -- one element, one unique-factorization
   clause, no natural transformation in sight -- and it is the form this file
   takes as primitive ([aue_universal] / [ue_universal] below).  The library
   already carried the same content twice over in less elementary encodings:
   [Functor/Representable.v]'s [Representable] packages a natural isomorphism
   [Hom r,─] ≅ H and its header records, without proving it, that “by the
   Yoneda lemma such a Φ is determined by a single universal element of F(A),
   namely Φ_A(id A)”; and [Structure/UniversalProperty.v]'s
   [representability_by_yoneda] proves exactly that determination, but states
   the universal elements as the ANONYMOUS sigma setoid

       { x : F c & IsIsomorphism (from (Yoneda_Lemma C F c) x) },

   a predicate on x phrased in terms of the invertibility of its Yoneda mate
   rather than in terms of unique factorization.  Neither is a first-class
   [UniversalElement], and neither exhibits Mac Lane's elementary clause.
   This file supplies the class and proves the two encodings equivalent.

   Mac Lane's Remark 3 on the following page (p. 58) then asserts a two-way
   subsumption between universal elements and universal arrows, and it is the
   substance of this file:

     (a) “Since an element x ∈ H d may be described as a function x : * → H d
         from a one-point set *, this definition is a special case of that of
         a universal arrow: ⟨r, e⟩ is universal from * to H.”

     (b) “Conversely, the definition of a universal arrow ⟨r, u⟩ from c to
         S : D ⟶ C can be phrased as: ⟨r, u⟩ is a universal element of the
         functor D(c, S−) : D ⟶ Set.”

   Both halves are proved below, and then STATED TOGETHER as the single
   biconditional [universal_element_arrow_subsumption], which is the thing the
   tree lacked: the two directions existed nowhere, and a reader had no way to
   see that the two notions are interdefinable rather than merely analogous.

--------
nLab: https://ncatlab.org/nlab/show/universal+element
nLab: https://ncatlab.org/nlab/show/representable+functor
Wikipedia: https://en.wikipedia.org/wiki/Universal_property

麦克莱恩在《闭合范畴理论》第二版第57页，第III.1条的定义2：如果D是一个范畴，并且H : D ⟶ Set是一个函子，那么H的一个普遍元（UNIVERSAL ELEMENT）是一个对⟨r, e⟩，由D的一个对象r和一个元素e ∈ H r组成，使得对于每一个对⟨d, x⟩，其中x ∈ H d，存在唯一的D的箭头k : r ~> d，使得(H k) e = x。

这是最基本的形式——一个元素，一个唯一分解子句，没有自然变换可见——而这个文件就是以这种原始形式呈现的（下面的 [aue_universal] / [ue_universal]）。该库已经以不那么基本的编码方式两次包含了相同的内容：[Functor/Representable.v] 的 [Representable] 打包了一个自然同构 [Hom r,─] ≅ H 及其头记录，而没有证明它，只是说明“根据 Yoneda 引理，这样的 Φ 是由 F(A) 的单个通用元素决定的，即 Φ_A(id A)”；而 [Structure/UniversalProperty.v] 的 [representability_by_yoneda] 精确地证明了该决定，但将通用元素表示为匿名 σ 集团。

{ x : F c & IsIsomorphism (from (Yoneda_Lemma C F c) x) },

一个关于 x 的谓词，用它的 Yoneda 配对的可逆性来表述，而不是用唯一分解来表述。两者都不是一等 [UniversalElement]，并且都不展现 Mac Lane 的基本条款。该文件提供了该类并证明了这两种编码是等价的。

接下来的页面（第58页）中，Mac Lane 的备注3随后断言了普遍元素和普遍箭头之间的双向包含关系，这也是本文件的实质内容：

(a) “由于一个元素 x ∈ H d 可以被描述为一个从单点集 * 到 H d 的函数 x : * → H d，因此这个定义是‘通用箭头’定义的一个特例：⟨r, e⟩ 是从 * 到 H 的通用箭头。”

(b) “相反地，从 c 到 S : D ⟶ C 的通用箭头 ⟨r, u⟩ 的定义可以表述为：⟨r, u⟩ 是函子 D(c, S−) : D ⟶ Set 的一个通用元素。”

下面证明了两个部分，然后作为单一的双条件 [universal_element_arrow_subsumption] 一起陈述，这是树所缺少的东西：两个方向在任何地方都不存在，读者无法看到这两个概念是相互可定义的，而不仅仅是类似的。
*)

(*
Where the notion sits, and why it is the elementary one

   Text:  Mac Lane, “Categories for the Working Mathematician”, Springer 1998,
          §III.1 (pp. 55-59) and §III.2
   Text:  Riehl, “Category Theory in Context”, Dover 2016, §2.4
   Paper: Kan, “Adjoint functors”, Trans. Amer. Math. Soc. 87, 1958

   The universal element is the smallest of the universal notions: it
   mentions no comma category, no adjunction, and no natural
   transformation, only an element and a factorization.  Its interest is
   that it is nevertheless EQUIVALENT to the largest of them.  Riehl
   organises §2.4 around this observation, calling a representation of a
   functor and a universal element “the same data”, and her Proposition
   2.4.8 makes the sharpest form of the statement: a universal element of
   H is precisely an INITIAL object of the category of elements of H.
   In-tree that reading is already worked out concretely, one functor at
   a time: Instance/Coq/Nat.v's [repr_initial] derives initiality in
   [FAlg NatF] from a representation of the forgetful functor on
   endomaps, and its header explains that [FAlg NatF] is standing in for
   the category of elements.  With the general class in hand that
   argument can be run once instead of per functor, which is what
   Theory/Universal/Element/Elements.v does.

   Historically the elementary form is what the subject started from.
   Kan's 1958 paper introduces adjoints through hom-set bijections, and
   Mac Lane's chapter notes record that the universal-mapping formulation
   predates the functorial one by a decade (see the essay in
   Theory/Universal/Arrow.v).  Mac Lane's own ordering in §III.1 is
   deliberate: universal arrow first, universal element second, remark
   third, the remark being where he tells the reader that nothing new was
   introduced.  This file follows that ordering, and takes the remark
   seriously enough to prove it.

   The setoid discipline changes one word of the definition.  Mac Lane
   writes “(H k) e = x” with equality of elements of a set; here H lands
   in [Sets], whose objects are setoids, so the clause is
   [fmap[H] k e ≈ x] and uniqueness of k is uniqueness up to `≈` -- the
   [Unique] record of Lib/Setoid.v, exactly as [AUniversalArrow] uses it.
   Nothing else moves.

--------
这个概念的位置，以及为什么它是基本概念

文本：Mac Lane，“工作数学家的范畴”，Springer 1998，
 §III.1（第 55-59 页）和§III.2
 文本：Riehl，“语境中的范畴论”，Dover 2016，§2.4
 论文：Kan，“伴随”，Trans。 阿米尔。 数学。 苏克。 87, 1958

普遍元素是普遍概念中最小的：它
 没有提到逗号范畴，没有附加词，也没有自然词
 变换，只有一个元素和一个因式分解。 它的兴趣是
 但它仍然相当于其中最大的一个。 里尔
 围绕这个观察组织§2.4，调用一个表示
 函子和通用元素“相同的数据”，以及她的命题
 2.4.8 提出该陈述的最尖锐形式：a universal element of
 H 正是 H 的元素范畴的初始对象。 
阅读已经具体解决的树内，一个函子位于
 一次：Instance/Coq/Nat.v 的 [repr_initial] 派生初始值
 [FAlg NatF] 来自健忘函子的表示
 内图，其标题解释了 [FAlg NatF] 代表
 元素的范畴。 手上有普通班
 参数可以运行一次，而不是每个函子，这就是
 Theory/Universal/Element/Elements.v 可以。

从历史上看，基本形式是主题的起点。 
Kan 1958 年的论文通过本集双射介绍了伴随，并且
 Mac Lane 的章节笔记记录了通用映射公式
 比函式早了十年（见文章
 理论/通用/箭头.v)。 Mac Lane 在§III.1 中自己的排序是
 deliberate：通用箭头第一，通用元素第二，备注
 第三，这句话是他告诉读者没有什么新鲜事
 介绍了。 该文件遵循该顺序，并带有注释
 足够认真地证明这一点。

集合学科改变了定义中的一个词。 麦克莱恩
 写出“(H k) e = x”，集合中的元素相等； 这里是H地
 在 [Sets] 中，其对象是 setoid，因此该子句是
 [fmap[H] k e ≈ x] 并且 k 的唯一性是直到 `≈` 为止的唯一性——
 Lib/Setoid.v 的 [Unique] 记录，与 [AUniversalArrow] 使用它完全相同。 
其他什么也没有动。
*)

(*
WHAT IS DELIVERED

   * [AUniversalElement H r] -- the elementary definition with the object
     a PARAMETER, in the idiom of [AUniversalArrow], carrying a [Setoid]
     ([AUniversalElementEquiv]) that compares two universal elements by
     their underlying elements; and [UniversalElement H] -- Mac Lane's
     pair ⟨r, e⟩ with the object a FIELD, in the idiom of [Representable].
     The two passages copy fields, so BOTH round trips close by [eq_refl]
     on the whole record ([aue_of_ue_of_aue], [ue_of_aue_of_ue]) -- record
     eta, primitive projections being on.

   * The mediator calculus and Mac Lane's Proposition 1 for this notion:
     [ue_med] with commutes / unique / id / comp, the canonical
     isomorphism of universal objects, and uniqueness up to a UNIQUE
     isomorphism compatible with the two universal elements
     ([universal_element_unique]).

   * DELIVERABLE 2, and it is an ISOMORPHISM OF SETOIDS IN [Sets], not a
     biconditional and not a pair of mutually inverse maps up to `≈`:
     [universal_element_yoneda] inhabits

         @Isomorphism Sets (AUniversalElement H r) (ue_yoneda_obj)

     where [ue_yoneda_obj] is LITERALLY the anonymous sigma setoid that
     [representability_by_yoneda] takes as its source -- the same
     [exists_setoid] constant, re-registered locally so the two
     elaborate to the same term ([rby_agrees] checks this by ascribing
     [representability_by_yoneda] at the named setoid, which is a
     conversion check and not a proof).
     Composing gives [universal_element_representation], the
     universal-element/representation correspondence as one iso in
     [Sets].  Accessors run both ways: [aue_mate_IsIso] and
     [aue_inverse] out, [AUniversalElement_of_mate] back,
     [universal_element_of_representation] and
     [representation_of_universal_element] at the representation end.

   * A YONEDA-FREE ROUTE TO THE SAME DATA, because deliverable 2's
     statement carries a universe restriction its consumers should not:
     [Yoneda_Lemma], hence [representability_by_yoneda], hence
     [universal_element_representation], is stated over
     [C : Category@{u0 u0 u0}] -- object, hom and proof universes
     IDENTIFIED (measured, and pinned in Test/ProbeUniversalElement.v) --
     so no category whose objects sit strictly above its homs can be
     substituted, and [Instance/Coq/Nat.v]'s [Endos] is such a category.
     [ue_transform], [ue_representation] and [AUniversalElement_of_repr]
     build the same correspondence by hand, with [repr_eval] as the one
     computation; [routes_agree_elem] and [routes_agree_repr] record that
     the two routes carry the same data where both typecheck, and every
     accessor and both [Representable] passages are routed through the
     direct one.  The restriction is the DONOR'S, not one introduced
     here, and nothing here shows it unavoidable.

   * [UniversalElement_of_Representable] and
     [Representable_of_UniversalElement], with the representing object
     kept by [eq_refl] and the universal element identified as Mac Lane's
     Φ_r(id r) ([ue_of_repr_elem]).  [Functor/Representable.v] is
     therefore the SAME notion, not a competing one; its header's
     sentence “by the Yoneda lemma such a Φ is determined by a single
     universal element of F(A), namely Φ_A(id A)” is these two
     definitions.

   * DELIVERABLE 3(a): [AUniversalElement_of_AUniversalArrow] and
     [AUniversalArrow_of_AUniversalElement] between [AUniversalElement H r]
     and [AUniversalArrow SetsOne H r], mediated by the global-elements
     lemma [global_elements_iso : (1 ~> X) ≅ X] in [Sets].

   * DELIVERABLE 3(b): [AUniversalElement_of_hom] and
     [AUniversalArrow_of_hom] between [AUniversalArrow c S a] and
     [AUniversalElement ([Hom c,─] ◯ S) a].  This half is CHEAPER than it
     looks and the file says why: the two records' fields have
     CONVERTIBLE types, because [fmap] of the composite [Hom c,─] ◯ S at
     k is postcomposition with [fmap[S] k].  Both passages are therefore
     [:=] with no tactic, and both round trips are [eq_refl] on the whole
     record.

   * The composite Mac Lane asserts, as ONE theorem:
     [universal_element_arrow_subsumption].

   WHAT IS NOT DELIVERED

   * NO CLAIM THAT THE YONEDA ISO IS A BIJECTION OF TYPES.  It is an
     isomorphism in [Sets], i.e. of SETOIDS, and both setoids compare
     only the underlying element (resp. the first projection).  The full
     record round trip through the Yoneda encoding is NOT [eq_refl] --
     the uniqueness data is rebuilt -- and Test/ProbeUniversalElement.v
     pins that.  What IS [eq_refl] is the element, in both directions.

   * NO DUAL.  A couniversal element -- a universal element of a
     contravariant H : D^op ⟶ Sets, i.e. a TERMINAL object of the
     category of elements -- would be the mirror of
     Theory/Universal/Arrow/Dual.v and is left to the issue that wants
     it.  Note that the presheaf orientation IS the one
     [representability_by_yoneda] is stated in, and this file reaches the
     covariant reading by instantiating it at [D^op] rather than by
     reproving Yoneda; see [ue_mate].

   * NO NOTATION.  [Theory/Universal/Arrow.v]'s `c ⟿ F` is declared
     inside its section and does not survive; there is no exported
     spelling to mirror.

   * NO FUNCTORIALITY.  Nothing here makes [UniversalElement] an
     assignment on functors, and no comparison with
     [Construction/Elements.v]'s [Elements_proj] is stated.

   * The initial-object-of-the-category-of-elements reading (Riehl
     Proposition 2.4.8) is NOT here: it needs [Construction/Elements.v]'s
     [Elements] and [Structure/Initial.v], and lives in the satellite
     Theory/Universal/Element/Elements.v so that consumers of the theory
     do not inherit those.  Non-vacuity likewise lives in
     Theory/Universal/Element/Examples.v, which instantiates the class at
     Instance/Coq/Nat.v's representation and recovers its universal
     element [O] by [eq_refl].  Note what that witness does NOT do: it
     does not re-derive Nat.v's [repr_initial], which lands in
     [FAlg NatF], the comparison [Elements Endos_Forget ≃ FAlg NatF] not
     being in the tree.

--------
交付的内容是什么

* [AUniversalElement H r] —— 使用对象的基本定义  
     一个参数，在 [AUniversalArrow] 的习语中，携带一个 [Setoid]  
     ([AUniversalElementEquiv])，用于通过它们的底层元素比较两个通用元素；以及 [UniversalElement H] —— Mac Lane 的对 ⟨r, e⟩，对象为 FIELD，在 [Representable] 的习语中。  
     这两个片段复制字段，因此在整个记录上，两个往返都通过 [eq_refl] 关闭 ([aue_of_ue_of_aue], [ue_of_aue_of_ue]) —— 记录 eta，原始投影处于开启状态。

* 关于此概念的中介计算和 Mac Lane 的命题 1：
     [ue_med] 具有交换 / 唯一 / 单位 / 复合性质，通用对象的
     拓扑同构，以及与两个通用元素兼容的唯一同构（[universal_element_unique]）的唯一性。

* 可交付成果 2，并且它是 [Sets] 中的集合同构，而不是双条件，也不是一对在 `≈` 上互为逆映射的映射：
     [universal_element_yoneda] 存在

@同构 集合 (AUniversalElement H r) (ue_yoneda_obj)

其中 [ue_yoneda_obj] 字面上是匿名的 sigma 等值类，[representability_by_yoneda] 将其作为源 -- 相同的 [exists_setoid] 常量，在本地重新注册，因此两者会展开为相同的项（[rby_agrees] 通过在命名的等值类上归属 [representability_by_yoneda] 来检查这一点，这是一种转换检查，而不是证明）。组合后得到 [universal_element_representation]，即通用元素/表示对应作为 [Sets] 中的一种同构。访问器可以双向运行：[aue_mate_IsIso] 和 [aue_inverse] 输出，[AUniversalElement_of_mate] 返回，[universal_element_of_representation] 和 [representation_of_universal_element] 在表示端。

* 通往相同数据的YONEDA-自由路线，因为可交付成果2的声明带有一个宇宙限制，其使用者不应：[Yoneda_Lemma]，因此[representability_by_yoneda]，因此[universal_element_representation]，已在[C : Category@{u0 u0 u0}]——对象、Hom和证明宇宙中——被标识（已测量，并在Test/ProbeUniversalElement.v中固定）——所以不能替换任何其对象严格位于其Hom之上的范畴，而[Instance/Coq/Nat.v]的[Endos]就是这样的范畴。[ue_transform]、[ue_representation]和[AUniversalElement_of_repr]手工构建了相同的对应关系，其中[repr_eval]作为唯一的计算；[routes_agree_elem]和[routes_agree_repr]记录了在都类型检查通过的情况下，两条路线携带相同数据，并且每个访问器和两个[Representable]通道都通过直接路线引导。这个限制是捐赠者的，而不是这里引入的，这里没有任何内容表明它是不可避免的。

* [UniversalElement_of_Representable] 和 [Representable_of_UniversalElement]，其表示对象由 [eq_refl] 保持，并且普遍元素被识别为 Mac Lane 的 Φ_r(id r) ([ue_of_repr_elem])。因此 [Functor/Representable.v] 是相同的概念，而不是竞争的概念；它标题中的句子“根据 Yoneda 引理，这样的 Φ 由 F(A) 的单一普遍元素决定，即 Φ_A(id A)”就是这两个定义。

* 可交付成果 3(a)：[AUniversalElement_of_AUniversalArrow] 和 [AUniversalArrow_of_AUniversalElement] 之间的 [AUniversalElement H r] 和 [AUniversalArrow SetsOne H r]，由 [Sets] 中的全局元素词条 [global_elements_iso : (1 ~> X) ≅ X] 调解。

* 可交付成果 3(b)：[AUniversalElement_of_hom] 和 [AUniversalArrow_of_hom] 之间的 [AUniversalArrow c S a] 和 [AUniversalElement ([Hom c,─] ◯ S) a]。这一部分比看起来便宜，文件中说明了原因：这两个记录的字段具有可转换类型，因为复合 [Hom c,─] ◯ S 在 k 时的 [fmap] 是与 [fmap[S] k 的后组合。因此，这两个段落都是 [:=]，无需策略，并且整个记录的往返都是 [eq_refl]。

* 复合 Mac Lane 声称，作为一个定理：
     [universal_element_arrow_subsumption]。

未交付的内容

* 不声称 YONEDA ISO 是类型的双射。它是在 [Sets] 中的同构，即在集合类上，并且两个集合类仅比较底层元素（或第一个投影）。通过 Yoneda 编码的完整记录往返并不是 [eq_refl] —— 唯一性数据是重建的 —— Test/ProbeUniversalElement.v 已经证明了这一点。真正属于 [eq_refl] 的是元素，在两个方向上都是如此。

* 无对偶。一个共宇元素 —— 对一个逆变函子 H : D^op ⟶ Sets 的普遍元素，即元素范畴的终对象 —— 将是 Theory/Universal/Arrow/Dual.v 的镜像，留给有需要的部分处理。注意，预层的方向就是 [representability_by_yoneda] 中所述的那个方向，而这个文件通过在 [D^op] 处实例化它（而不是重新证明 Yoneda 定理）来得到协变的理解；参见 [ue_mate]。

* 无标注。[Theory/Universal/Arrow.v] 的 `c ⟿ F` 在其部分内部声明，并不会存活；没有可供镜像的导出拼写。

* 没有函子性。这里没有任何内容使 [UniversalElement] 成为关于函子的作业，也没有说明与 [Construction/Elements.v] 的 [Elements_proj] 的比较。

* 类元素的初始对象读取（Riehl 命题 2.4.8）不在这里：它需要 [Construction/Elements.v] 的 [Elements] 和 [Structure/Initial.v]，并且位于卫星文件 Theory/Universal/Element/Elements.v 中，以便理论的使用者不会继承那些。同样，非空性也位于 Theory/Universal/Element/Examples.v 中，该文件在 Instance/Coq/Nat.v 的表示上实例化类，并通过 [eq_refl] 恢复其通用元素 [O]。注意该证人没有做的事情：它没有重新推导 Nat.v 的 [repr_initial]，该元素落在 [FAlg NatF] 中，比较 [Elements Endos_Forget ≃ FAlg NatF] 不在树中。
*)

(*
[exists_setoid] (Structure/UniversalProperty.v) is declared there with
   [#[local]], which removes it from the instance database for importers but
   leaves the CONSTANT reachable by name.  Re-registering it here -- locally,
   so this file does not push a first-projection-only setoid on every sigma
   type in the tree -- is what makes [ue_yoneda_obj] below elaborate to the
   very term [representability_by_yoneda] has in its type, rather than to a
   copy with a different [Equivalence] proof that would not be convertible
   with it.  [rby_agrees] records that this worked.

--------
[exists_setoid]（Structure/UniversalProperty.v）在那里使用 [#[local] 声明，该声明会将其从实例数据库中删除以供导入，但仍可以通过名称访问该 CONSTANT。在这里重新注册它——在本地，所以此文件不会在树中的每个 sigma 类型上强制使用只投影第一分量的 setoid——正是使下面的 [ue_yoneda_obj] 展开为 [representability_by_yoneda] 类型中的实际项，而不是一个带有不同 [Equivalence] 证明的副本，这个副本将无法与其转换。[rby_agrees] 记录了这项操作已经成功。
*)
#[local] Existing Instance Category.Structure.UniversalProperty.exists_setoid.

(** ** Global elements of a setoid / ** 集合族的全局元素 *)

(*
Mac Lane's “an element x ∈ H d may be described as a function x : * → H d
   from a one-point set”.  [SetsOne] (Construction/Elements.v) is the
   singleton of [Sets_Terminal], the same object the elements-comma category
   =(SetsOne) ↓ K is built over there.

   A NOTE ON UNIVERSES, because it dictates the shape of the three
   definitions below.  A [Sets]-morphism out of the CONCRETE [SetsOne] whose
   [proper_morphism] is left to INSTANCE RESOLUTION -- whether by [Program]'s
   obligation tactic or by writing [reflexive_proper] out by hand -- resolves
   [Reflexive] at [SetsOne] and thereby pins the CARRIER universe of [Sets] to
   [Set], after which [global_element] cannot be applied at [fobj[H] d] for an
   [H] whose [Sets] sits anywhere else, and the whole of 3(a) is unformable.
   Writing the pointwise term [fun a b _ => reflexivity x] avoids the
   resolution and keeps all three fully polymorphic
   ([global_elements_iso@{u u0 u1 u2 u3}], measured).  Hence the record
   literals with that field spelled out, and hence [GlobalElements] is named:
   an anonymous [{| carrier := ... |}] in the [Isomorphism]'s type leaves the
   ambient category of the [to] field unresolved.

   BE PRECISE ABOUT THE CAUSE; an earlier revision of this note was wrong
   twice, and the second error would have misled a reader following it as a
   rule.  It is NOT [Program]: the same definition with a VARIABLE source
   instead of [SetsOne] stays polymorphic under [Program]
   ([∀ {X Y : obj[Sets@{u0 u}]}], measured), and a plain [Definition] with no
   [Program] anywhere is pinned identically once its [proper_morphism] is
   [reflexive_proper _].  And it is NOT that “supplying [proper_morphism]
   explicitly as a term” suffices -- that claim is FALSE, since
   [reflexive_proper (fun _ => x)] is such a term and is pinned; what matters
   is supplying THAT PARTICULAR pointwise term.  Nor is it [Universe
   Minimization ToSet], which changes nothing in either position: the pin
   appears with the flag off (its state from Lib.v) and is byte-identical
   with it on.  [reflexive_proper] itself is innocent, carrying an empty
   constraint set; [Set] is chosen when the [Reflexive] instance is resolved
   for [SetsOne]'s equivalence.  That last step is read off the elaborated
   term rather than separately proved, and is stated as the diagnosis it
   is.

--------
Mac Lane 的“元素 x ∈ H d 可以描述为函数 x : * → H d
 来自一点集”。 [SetsOne]（Construction/Elements.v）是
 [Sets_Terminal] 的单例，同一个对象的 elements-comma 范畴
 =(SetsOne) ↓ K 建在那边。

关于宇宙的注释，因为它决定了三个宇宙的形状
 定义如下。 CONCRETE [SetsOne] 中的 [Sets] 态射，其
 [proper_morphism] 留给实例分辨率——无论是 [Program] 的
 义务策略或通过手动编写 [reflexive_proper] -- 解决
 [Reflexive] 位于 [SetsOne] 上，从而将 [Sets] 的 CARRIER 宇宙固定到
 [Set]，之后 [global_element] 不能应用于 [fobj[H] d]
 [H] 的 [Sets] 位于其他任何地方，并且整个 3(a) 是不可变形的。 
编写逐点项 [fun a b _ => reflexivity x] 可以避免
 分辨率并保持所有三个完全多态
 （[global_elements_iso@{u u0 u1 u2 u3}]，测量）。 因此记录
 拼写出该字段的文字，因此 [GlobalElements] 被命名为：
 [Isomorphism] 类型中的匿名 [{| carrier := ... |}] 留下
 [to] 字段的环境范畴未解析。

准确说明原因； 此注释的早期修订版是错误的
 两次，第二个错误会误导读者，将其视为
 规则。 它不是 [Program]：与 VARIABLE 源具有相同的定义
 而不是 [SetsOne] 在 [Program] 下保持多态
 ([∀ {X Y : obj[Sets@{u0 u}]}]，测量)，和一个普通的 [Definition]，没有
 一旦 [proper_morphism] 被固定，[Program] 任何地方的固定方式都相同
 [reflexive_proper _]。 这并不是“提供 [proper_morphism]
 明确地作为一个术语”就足够了——这个说法是错误的，因为
 [reflexive_proper (fun _ => x)] 就是这样一个术语，并且被固定； 重要的是
 正在提供那个特定的逐点项。 也不是[宇宙
 最小化 ToSet]，这不会改变任何位置：引脚
 显示标志关闭（其状态来自 Lib.v）并且字节相同
 带着它。 [reflexive_proper]本身是无辜的，携带着一个空的
 约束集； 当解析 [Reflexive] 实例时选择 [Set]
 [SetsOne] 的等效项。 最后一步是从详细说明中读出的
 术语而不是单独证明，并被表述为诊断
 群岛
*)

Definition global_element {X : Sets} (x : X) : SetsOne ~{Sets}~> X :=
  {| morphism := fun _ => x ; proper_morphism := fun a b _ => reflexivity x |}.

(* The element is recovered on the nose, by conversion. / 该元素通过转换在鼻子上被回收。 *)
Lemma global_element_at {X : Sets} (x : X) : global_element x ttt = x.
Proof. reflexivity. Qed.

Definition GlobalElements (X : Sets) : Sets :=
  {| carrier := SetsOne ~{Sets}~> X |}.

Definition global_elements_to (X : Sets) : GlobalElements X ~{Sets}~> X :=
  {| morphism := fun f : SetsOne ~{Sets}~> X => f ttt ;
     proper_morphism := fun f g H => H ttt |}.

Definition global_elements_from (X : Sets) : X ~{Sets}~> GlobalElements X :=
  {| morphism := @global_element X ; proper_morphism := fun x y H _ => H |}.

(*
Hom(1, X) ≅ X in [Sets]: the global-elements lemma.  One leg is the
   identity on the underlying element by [eq_refl] ([global_element_at]); the
   other needs the singleton's [ttt] to be its only inhabitant, which is the
   [destruct] below.

--------
在 [Sets] 中，Hom(1, X) ≅ X：全局元素引理。一条腿是由 [eq_refl] ([global_element_at]) 给出的底层元素的恒等映射；另一条腿则需要单子集的 [ttt] 作为其唯一的元素，这就是下面的 [destruct]。
*)
Definition global_elements_iso (X : Sets)
  : @Isomorphism Sets (GlobalElements X) X.
Proof.
  unshelve refine {| to := global_elements_to X; from := global_elements_from X |}.
  - intro x; reflexivity.
  - intros f u; destruct u; reflexivity.
Defined.

Section UniversalElement.

Context {D : Category}.

(** ** The elementary definition / ** 基本定义 *)

(*
Mac Lane's clause, with the object r a PARAMETER -- the idiom of
   [AUniversalArrow] (Theory/Universal/Arrow.v), and the shape every
   comparison below needs, since both [representability_by_yoneda] and
   [AUniversalArrow] fix their object.  [d] and [x] are EXPLICIT, unlike
   [AUniversalArrow]'s implicit [{d} {f}]: a deliberate deviation, since
   every use site below supplies both and the implicit form forces the
   [@]-spelling throughout.

--------
Mac Lane 的子句，带有对象 r 作为参数 —— [AUniversalArrow]（Theory/Universal/Arrow.v）的习语，以及下面每个比较所需要的形式，因为 [representability_by_yoneda] 和 [AUniversalArrow] 都固定它们的对象。[d] 和 [x] 是显式的，不像 [AUniversalArrow] 的隐式 [{d} {f}]：这是一个刻意的偏差，因为下面的每个使用位置都提供了两者，而隐式形式会在整个过程中强制使用 [@] 拼写。
*)
Class AUniversalElement (H : D ⟶ Sets) (r : D) := {
  aue_elem : H r ;                             (* Mac Lane's e ∈ H r / 麦克·莱恩的 e ∈ H r *)
  aue_universal (d : D) (x : H d) :            (* (H k) e ≈ x for a unique k / (H k) e ≈ x 对于唯一的 k *)
    Unique (fun k : r ~{D}~> d => fmap[H] k aue_elem ≈ x)
}.

(*
Two universal elements at the same object are equivalent when their
   underlying elements agree; the factorization data carries nothing
   further.  This mirrors [AUniversalArrowEquiv] exactly.

--------
当两个同一对象的通用元素的底层元素相同时，它们是等价的；分解数据不包含其他内容。这完全反映了 [AUniversalArrowEquiv]。
*)
#[export] Program Instance AUniversalElementEquiv (H : D ⟶ Sets) (r : D) :
  Setoid (AUniversalElement H r) :=
  {| equiv := fun X Y => @aue_elem H r X ≈ @aue_elem H r Y |}.

(*
Mac Lane's pair ⟨r, e⟩ proper, with the object a FIELD -- the idiom of
   [Representable] (Functor/Representable.v), which bundles [repr_obj] the
   same way.  There is no setoid on this one: comparing two universal
   elements at DIFFERENT objects is not an equation but the isomorphism
   [universal_element_iso] below.

--------
Mac Lane 的对 ⟨r, e⟩ 正确，与对象 a FIELD —— [Representable] (Functor/Representable.v) 的惯用法相同，它以相同的方式捆绑 [repr_obj]。这个上没有集合类：在不同对象处比较两个泛元不是一个等式，而是下面的同构 [universal_element_iso]。
*)
Class UniversalElement (H : D ⟶ Sets) := {
  ue_obj : D ;
  ue_elem : H ue_obj ;
  ue_universal (d : D) (x : H d) :
    Unique (fun k : ue_obj ~{D}~> d => fmap[H] k ue_elem ≈ x)
}.

(* The two encodings pass into one another by copying fields. / 这两种编码通过复制字段相互传递。 *)
Definition AUniversalElement_of_UniversalElement {H : D ⟶ Sets}
  (U : UniversalElement H) : AUniversalElement H (@ue_obj H U) :=
  {| aue_elem := @ue_elem H U ; aue_universal := @ue_universal H U |}.

Definition UniversalElement_of_AUniversalElement {H : D ⟶ Sets} {r : D}
  (U : AUniversalElement H r) : UniversalElement H :=
  {| ue_obj := r ; ue_elem := @aue_elem H r U ;
     ue_universal := @aue_universal H r U |}.

(*
Both round trips are [eq_refl] ON THE WHOLE RECORD -- not merely on the
   element -- because the fields are copied verbatim and primitive
   projections give record eta.  Contrast the Yoneda passage below, where
   only the element survives.

--------
两个往返都是在整个记录上进行 [eq_refl] —— 不仅仅是在元素上 —— 因为字段是逐字复制的，并且原始投影提供记录的 eta。对比下面的 Yoneda 段落，其中只有元素得以保留。
*)
Corollary aue_of_ue_of_aue {H : D ⟶ Sets} {r : D} (U : AUniversalElement H r) :
  AUniversalElement_of_UniversalElement (UniversalElement_of_AUniversalElement U)
    = U.
Proof. reflexivity. Qed.

Corollary ue_of_aue_of_ue {H : D ⟶ Sets} (U : UniversalElement H) :
  UniversalElement_of_AUniversalElement (AUniversalElement_of_UniversalElement U)
    = U.
Proof. reflexivity. Qed.

(** ** The Yoneda mate / ** Yoneda 对偶 *)

(*
The natural transformation [Hom r,─] ⟹ H determined by an element x of
   H r: its component at d carries k : r ~> d to (H k) x.  It is supplied by
   INSTANTIATING the presheaf Yoneda lemma at D^op rather than by using
   [Covariant_Yoneda_Lemma], for one reason: [representability_by_yoneda]
   below is stated with [Yoneda_Lemma C F c], and deliverable 2 composes with
   it, so the mate must be that term.  The instantiation is free --
   (D^op)^op IS D and [Curried_CoHom (D^op) r] IS [Curried_Hom D r], both by
   conversion (Construction/Opposite.v, Functor/Hom.v) -- so no [op]
   appears in the type.

--------
由 H 的一个元素 x 决定的自然变换 [Hom r,─] ⟹ H r：它在 d 处的分量将 k : r ~> d 映射为 (H k) x。它是通过在 D^op 上实例化预屑的 Yoneda 引理提供的，而不是使用 [Covariant_Yoneda_Lemma]，原因之一是：下面的 [representability_by_yoneda] 用 [Yoneda_Lemma C F c] 表述，并且交付物 2 与之组合，所以对应项必须是那个项。该实例化是自由的——(D^op)^op 即 D，并且 [Curried_CoHom (D^op) r] 即 [Curried_Hom D r]，这两者都是通过转换（Construction/Opposite.v, Functor/Hom.v）得出的——所以类型中没有出现 [op]。
*)
Definition ue_mate (H : D ⟶ Sets) (r : D) (x : H r)
  : @Curried_Hom D r ~{[D, Sets]}~> H :=
  from (Yoneda_Lemma (D^op) H r) x.

(* Its action, by conversion: this is the [(H k) e] of Mac Lane's clause. / 它的作用，通过转换：这是麦克·莱恩条款的[(H k) e]。 *)
Lemma ue_mate_at (H : D ⟶ Sets) (r : D) (x : H r) (d : D) (k : r ~{D}~> d) :
  transform (ue_mate H r x) d k = fmap[H] k x.
Proof. reflexivity. Qed.

(*
The covariant Yoneda lemma gives the same mate -- but only up to `≈`, not
   by [eq_refl].  The two instances are separate [Program Instance]s whose
   naturality obligations are distinct opaque constants, so the two
   transformations are distinct TERMS with convertible actions;
   Test/ProbeUniversalElement.v pins the negative side.  Nothing below uses
   this lemma; it is here so that a reader reaching for the covariant lemma
   knows what is and is not available.

--------
协变Yoneda引理给出了相同的伴随——但仅在`≈`下，而不是[eq_refl]。两个实例是独立的[Program Instance]，其自然性义务是不同的不透明常数，因此这两个变换是不同的TERMS，其作用可转换；Test/ProbeUniversalElement.v确定了负面部分。下面没有使用这个引理；它存在的目的是让读者在查找协变引理时知道哪些是可用的，哪些不可用。
*)
Lemma ue_mate_covariant (H : D ⟶ Sets) (r : D) (x : H r) :
  from (Covariant_Yoneda_Lemma D H r) x ≈ ue_mate H r x.
Proof. intros d k; reflexivity. Qed.

Section MateIso.

Context (H : D ⟶ Sets).
Context (r : D).

(*
From a universal element, the inverse of its mate: the component at d
   sends x to the unique k factoring it.  Respectfulness and both naturality
   squares are uniqueness arguments, and nothing else.

--------
从一个通用元素，它的伴侣的逆元：位于 d 的分量将 x 发送到因式分解它的唯一 k。尊重性和两个自然性平方是唯一性论证，而别无其他。
*)
Program Definition aue_inverse (U : AUniversalElement H r)
  : H ~{[D, Sets]}~> @Curried_Hom D r :=
  {| transform := fun d => {| morphism := fun x => unique_obj (aue_universal d x) |} |}.
Next Obligation.
  proper.
  symmetry.
  apply (uniqueness (aue_universal d y)).
  transitivity x; [ apply (unique_property (aue_universal d x)) | exact X ].
Qed.
Next Obligation.
  simpl; intros.
  symmetry.
  apply (uniqueness (aue_universal y (fmap[H] f x0))).
  transitivity (fmap[H] f (fmap[H] (unique_obj (aue_universal x x0)) aue_elem)).
  - exact (@fmap_comp _ _ H _ _ _ f (unique_obj (aue_universal x x0)) aue_elem).
  - apply proper_morphism, (unique_property (aue_universal x x0)).
Qed.
Next Obligation.
  simpl; intros.
  apply (uniqueness (aue_universal y (fmap[H] f x0))).
  transitivity (fmap[H] f (fmap[H] (unique_obj (aue_universal x x0)) aue_elem)).
  - exact (@fmap_comp _ _ H _ _ _ f (unique_obj (aue_universal x x0)) aue_elem).
  - apply proper_morphism, (unique_property (aue_universal x x0)).
Qed.

(*
... hence the mate of a universal element is invertible.  The two inverse
   laws are [unique_property] and [uniqueness] respectively; the [fmap_id]
   and [id_left] residues are the identity of the functor category
   [D, Sets] unfolding.

--------
...因此一个幺元的伴随元是可逆的。两个逆律分别是 [unique_property] 和 [uniqueness]；[fmap_id] 和 [id_left] 的剩余是函子范畴 [D, Sets] 展开的单位元。
*)
Program Definition aue_mate_IsIso (U : AUniversalElement H r)
  : IsIsomorphism (ue_mate H r (@aue_elem H r U)) :=
  {| two_sided_inverse := aue_inverse U |}.
Next Obligation.
  simpl; intros.
  transitivity x0.
  - apply (unique_property (aue_universal x x0)).
  - symmetry; exact (@fmap_id _ _ H x x0).
Qed.
Next Obligation.
  simpl; intros.
  transitivity (unique_obj (aue_universal x (fmap[H] x0 (@aue_elem H r U)))).
  - reflexivity.
  - transitivity x0.
    + apply (uniqueness (aue_universal x (fmap[H] x0 (@aue_elem H r U)))); reflexivity.
    + symmetry; apply id_left.
Qed.

Definition ue_unmate (x : H r) (I : IsIsomorphism (ue_mate H r x))
  : H ~{[D, Sets]}~> @Curried_Hom D r :=
  @two_sided_inverse _ _ _ (ue_mate H r x) I.

(*
... and conversely, an invertible mate IS a universal element: the
   factorization is the inverse's component, its property is one inverse law
   and its uniqueness the other.

--------
... 相反，可逆的伴随就是一个泛元素：分解是逆元的分量，它的性质是一条逆元定律，它的唯一性是另一条逆元定律。
*)
Program Definition AUniversalElement_of_mate (x : H r)
  (I : IsIsomorphism (ue_mate H r x)) : AUniversalElement H r :=
  {| aue_elem := x ;
     aue_universal := fun d y =>
       {| unique_obj := transform (ue_unmate x I) d y |} |}.
Next Obligation.
  transitivity (fmap[H] id{D} y).
  - exact (@is_right_inverse _ _ _ (ue_mate H r x) I d y).
  - exact (@fmap_id _ _ H d y).
Qed.
Next Obligation.
  transitivity (transform (ue_unmate x I) d (fmap[H] v x)).
  - apply proper_morphism; symmetry; exact X.
  - transitivity (id{D} ∘ v).
    + exact (@is_left_inverse _ _ _ (ue_mate H r x) I d v).
    + apply id_left.
Qed.

(** ** The representation, built directly / ** 直接构建的表示 *)

(*
[ue_mate] is the Yoneda mate and is what deliverable 2 must be stated
   against; but it inherits a UNIVERSE CONSTRAINT from its donor that a
   consumer should not have to pay.  [Yoneda_Lemma], and hence
   [representability_by_yoneda], is stated over `C : Category@{u0 u0 u0}` --
   object, hom and proof universes all IDENTIFIED (measured, not assumed) --
   so neither can be instantiated at a category whose objects sit strictly
   above its homs.  [Instance/Coq/Nat.v]'s [Endos] is exactly such a
   category, so the entire Yoneda route is unavailable there.

   The same transformation built by hand is not so constrained: its component
   at d carries k to (H k) e, which is the action of [ue_mate] BY CONVERSION
   ([ue_mate_is_transform] below records it), but the term mentions no
   Yoneda lemma.  Everything the accessors need is therefore routed through
   these three definitions, and only [universal_element_yoneda] and
   [universal_element_representation] -- the deliverable-2 statements
   proper -- carry the constraint.  Theory/Universal/Element/Examples.v is
   the payoff: it instantiates at [Endos], which the Yoneda route cannot
   reach.

--------
[ue_mate] 是 Yoneda 配对，并且是可交付成果 2 必须针对的；但它从其捐赠者继承了一个宇宙约束，消费者不应当为此付费。[Yoneda_Lemma]，因此 [representability_by_yoneda]，是在 `C : Category@{u0 u0 u0}` 上声明的——对象、Hom 和证明宇宙都已识别（测量而非假设）——所以它们都不能在其 Hom 严格低于对象的范畴中实例化。[Instance/Coq/Nat.v] 的 [Endos] 正是这样一个范畴，因此整个 Yoneda 路径在此处不可用。

手工构建的相同变换没有那么受限：它在 d 处的分量将 k 映射到 (H k) e，这就是 [ue_mate] 通过转换的作用（下面的 [ue_mate_is_transform] 记录了它），但该项并未提到 Yoneda 引理。因此，访问器所需的一切都通过这三个定义进行路由，只有 [universal_element_yoneda] 和 [universal_element_representation] —— 可交付成果 2 的语句本身 —— 承载约束。Theory/Universal/Element/Examples.v 是回报：它在 [Endos] 处进行实例化，而 Yoneda 路径无法到达该处。
*)

Program Definition ue_transform (U : AUniversalElement H r)
  : @Curried_Hom D r ~{[D, Sets]}~> H :=
  {| transform := fun d =>
       {| morphism := fun k => fmap[H] k (@aue_elem H r U) |} |}.
Next Obligation.
  proper.
  exact (@fmap_respects _ _ H _ _ x y X (@aue_elem H r U)).
Qed.
Next Obligation.
  simpl; intros.
  symmetry.
  exact (@fmap_comp _ _ H _ _ _ f x0 (@aue_elem H r U)).
Qed.
Next Obligation.
  simpl; intros.
  exact (@fmap_comp _ _ H _ _ _ f x0 (@aue_elem H r U)).
Qed.

(*
The Yoneda mate IS this transformation, pointwise by [reflexivity] -- but
   NOT as a term: the two records carry different naturality proofs.  This is
   the same seam as [ue_mate_covariant].

--------
Yoneda 配对就是这个变换，按 [reflexivity] 点对点地进行——但不是作为一个项：两个记录携带不同的自然性证明。这与 [ue_mate_covariant] 是同一个缝隙。
*)
Lemma ue_mate_is_transform (U : AUniversalElement H r) :
  ue_mate H r (@aue_elem H r U) ≈ ue_transform U.
Proof. intros d k; reflexivity. Qed.

Program Definition ue_representation (U : AUniversalElement H r)
  : @Curried_Hom D r ≅[[D, Sets]] H :=
  {| to := ue_transform U ; from := aue_inverse U |}.
Next Obligation.
  simpl; intros.
  transitivity x0.
  - apply (unique_property (aue_universal x x0)).
  - symmetry; exact (@fmap_id _ _ H x x0).
Qed.
Next Obligation.
  simpl; intros.
  transitivity x0.
  - apply (uniqueness (aue_universal x (fmap[H] x0 (@aue_elem H r U)))); reflexivity.
  - symmetry; apply id_left.
Qed.

(*
... and back, without Yoneda: the factorization is the inverse's
   component.  The Yoneda computation Mac Lane invokes -- that Φ sends an
   arrow to the image of the universal element under it -- is run here as the
   naturality of [to Phi] evaluated at the identity, which is
   Instance/Coq/Nat.v's [repr_eval] generalized off its one functor.

--------
... 并返回，不使用 Yoneda：分解是逆元的组成部分。Mac Lane 调用的 Yoneda 计算——即 Φ 将一个箭头发送到其下的普适元素的像——在这里作为在恒等映射上计算的 [to Phi] 的自然性运行，这就是 Instance/Coq/Nat.v 中 [repr_eval] 从它的单一函子推广出来的形式。
*)
Lemma repr_eval (Phi : @Curried_Hom D r ≅[[D, Sets]] H) {d : D}
      (k : r ~{D}~> d) :
  fmap[H] k (transform (to Phi) r id{D}) ≈ transform (to Phi) d k.
Proof.
  transitivity (transform (to Phi) d (k ∘ id{D})).
  - exact (naturality (to Phi) r d k id{D}).
  - apply proper_morphism, id_right.
Qed.

Program Definition AUniversalElement_of_repr
  (Phi : @Curried_Hom D r ≅[[D, Sets]] H) : AUniversalElement H r :=
  {| aue_elem := transform (to Phi) r id{D} ;
     aue_universal := fun d x =>
       {| unique_obj := transform (from Phi) d x |} |}.
Next Obligation.
  transitivity (transform (to Phi) d (transform (from Phi) d x)).
  - apply repr_eval.
  - transitivity (fmap[H] id{D} x).
    + exact (iso_to_from Phi d x).
    + exact (@fmap_id _ _ H d x).
Qed.
Next Obligation.
  transitivity (transform (from Phi) d (transform (to Phi) d v)).
  - apply proper_morphism.
    transitivity (fmap[H] v (transform (to Phi) r id{D})).
    + symmetry; exact X.
    + apply repr_eval.
  - transitivity (id{D} ∘ v).
    + exact (iso_from_to Phi d v).
    + apply id_left.
Qed.

(** ** Deliverable 2: the two encodings, as an isomorphism of setoids / ** 可交付成果 2：作为集合同构的两个编码 *)

(* The anonymous sigma setoid [representability_by_yoneda] uses, named. / 匿名的 sigma 集合 [representability_by_yoneda] 使用，已命名。 *)
Definition ue_yoneda_obj : SetoidObject :=
  {| carrier := { x : H r & IsIsomorphism (ue_mate H r x) } |}.

(*
... and the check that naming it changed nothing: [representability_by_yoneda]
   at D^op has EXACTLY this setoid as its source, [exists_setoid] instance
   included.  [Defined]-free: the ascription is the whole content.

--------
... 并且检查重命名没有改变任何东西：[representability_by_yoneda]
在 D^op 中，它的源恰好是这个集合，包含 [exists_setoid] 实例。
[Defined]-无：该归属是全部内容。
*)
Definition rby_agrees : @Isomorphism Sets ue_yoneda_obj
  (Build_SetoidObject (Isomorphism (@Curried_Hom D r) H) _)
  := representability_by_yoneda (D^op) H r.

Program Definition ue_to_yoneda
  : Build_SetoidObject (AUniversalElement H r) (AUniversalElementEquiv H r)
      ~{Sets}~> ue_yoneda_obj :=
  {| morphism := fun U => (@aue_elem H r U; aue_mate_IsIso U) |}.

Program Definition ue_of_yoneda
  : ue_yoneda_obj ~{Sets}~>
      Build_SetoidObject (AUniversalElement H r) (AUniversalElementEquiv H r) :=
  {| morphism := fun p => AUniversalElement_of_mate (`1 p) (`2 p) |}.

(*
THE STATEMENT, and it is an isomorphism in [Sets] -- of SETOIDS.  Not a
   biconditional (which would forget the maps), and not merely a pair of
   mutually inverse maps up to `≈` (which would forget respectfulness).  The
   two setoids compare only the underlying element and the first projection
   respectively, so what the two round-trip laws say is that the ELEMENT
   survives both passages; that they say it by [eq_refl] rather than by a
   proof is recorded immediately below.

--------
该陈述，并且它是在 [Sets] 中的集合等价类的同构。不是双条件（这会忽略映射），也不仅仅是一对相互逆的映射至 `≈`（这会忽略尊重性）。这两个集合等价类仅比较底层元素和第一个投影，因此这两个往返规律所表达的是元素在两次传递中都得以保留；它们是通过 [eq_refl] 来表达，而不是通过证明，这在下面立即记录。
*)
Program Definition universal_element_yoneda
  : @Isomorphism Sets
      (Build_SetoidObject (AUniversalElement H r) (AUniversalElementEquiv H r))
      ue_yoneda_obj :=
  {| to := ue_to_yoneda ; from := ue_of_yoneda |}.

Corollary ue_yoneda_round_elem (x : H r) (I : IsIsomorphism (ue_mate H r x)) :
  `1 (ue_to_yoneda (ue_of_yoneda (x; I))) = x.
Proof. reflexivity. Qed.

Corollary ue_yoneda_round_ue (U : AUniversalElement H r) :
  @aue_elem H r (ue_of_yoneda (ue_to_yoneda U)) = @aue_elem H r U.
Proof. reflexivity. Qed.

(*
Composing with [representability_by_yoneda]: a universal element of H at r
   is the same data as a representation of H by r.  This is the theorem
   [Functor/Representable.v]'s header states in prose (“by the Yoneda lemma
   such a Φ is determined by a single universal element”) and that
   [Structure/UniversalProperty.v] proved only for the anonymous encoding.

--------
使用 [representability_by_yoneda] 进行作曲：H 在 r 处的一个通用元素与 H 由 r 的表示是相同的数据。这是 [Functor/Representable.v] 的标题在文字中陈述的定理（“根据 Yoneda 引理，这样的 Φ 由一个单一的通用元素决定”），而 [Structure/UniversalProperty.v] 只对匿名编码证明了该定理。
*)
Definition universal_element_representation
  : @Isomorphism Sets
      (Build_SetoidObject (AUniversalElement H r) (AUniversalElementEquiv H r))
      (Build_SetoidObject (Isomorphism (@Curried_Hom D r) H) _)
  := iso_compose (representability_by_yoneda (D^op) H r) universal_element_yoneda.

Definition representation_of_universal_element (U : AUniversalElement H r)
  : @Curried_Hom D r ≅[[D, Sets]] H
  := to universal_element_representation U.

Definition universal_element_of_representation
  (Phi : @Curried_Hom D r ≅[[D, Sets]] H) : AUniversalElement H r
  := from universal_element_representation Phi.

(*
The universal element read off a representation is Mac Lane's Φ_r(id r) --
   the image of the identity -- by conversion, for every H, r and Φ.

   BUT DO NOT READ THIS AS THE GENERAL FORM OF Instance/Coq/Nat.v's
   [nat_universal_element].  It is not, and the reason is this file's own
   headline finding read back on itself: [universal_element_of_representation]
   goes through the Yoneda route, so this lemma inherits the donor's universe
   identification -- [About] reports the constraint [u = u0] -- and it is
   therefore NOT instantiable at [Endos], which is the only category
   Nat.v's check lives in.  The statement that does generalize
   [nat_universal_element], and the one Theory/Universal/Element/Examples.v
   actually uses, is [ue_of_repr_elem] below, stated over the DIRECT route
   with the object universe free of the hom universe.  So this lemma is a
   second instance of the restriction rather than an escape from it.

--------
从一个表示中读取的通用元素是 Mac Lane 的 Φ_r(id r) —— 即恒等映射的像 —— 通过转换，对于每个 H、r 和 Φ 都成立。

但是不要将其解读为 Instance/Coq/Nat.v 中 [nat_universal_element] 的通用形式。它不是，原因在于该文件自身标题所发现的自我引用：[universal_element_of_representation] 通过 Yoneda 路径，因此该引理继承了提供者的宇宙识别 —— [About] 报告了约束 [u = u0] —— 因此它不能在唯一存在 Nat.v 检查的范畴 [Endos] 中实例化。能够泛化 [nat_universal_element] 的陈述，以及 Theory/Universal/Element/Examples.v 实际使用的，是下面的 [ue_of_repr_elem]，使用直接路径表述，对象宇宙不受同态宇宙约束。因此，该引理是对该限制的第二个实例，而不是对其的规避。
*)
Lemma universal_element_of_representation_at
  (Phi : @Curried_Hom D r ≅[[D, Sets]] H) :
  @aue_elem H r (universal_element_of_representation Phi)
    = transform (to Phi) r id{D}.
Proof. reflexivity. Qed.

(*
THE TWO ROUTES AGREE.  The Yoneda-composed accessors and the direct ones
   are not the same TERMS -- the Yoneda route goes through
   [representability_by_yoneda]'s [Defined] proof -- but they carry the same
   data: the same universal element, by [eq_refl], and representations that
   agree pointwise.  So nothing is lost by taking the direct route
   downstream, which is what [UniversalElement_of_Representable] does.

--------
两条路径是一致的。Yoneda 组合访问器和直接访问器不是相同的项——Yoneda 路径通过 [representability_by_yoneda] 的 [Defined] 证明——但它们携带相同的数据：同一个通用元素，由 [eq_refl]，和逐点一致的表示。因此，沿着直接路径向下游是不会丢失任何信息的，这正是 [UniversalElement_of_Representable] 所做的。
*)
Corollary routes_agree_elem (Phi : @Curried_Hom D r ≅[[D, Sets]] H) :
  @aue_elem H r (universal_element_of_representation Phi)
    = @aue_elem H r (AUniversalElement_of_repr Phi).
Proof. reflexivity. Qed.

Corollary routes_agree_repr (U : AUniversalElement H r) :
  to (representation_of_universal_element U) ≈ to (ue_representation U).
Proof. intros d k; reflexivity. Qed.

End MateIso.

(** ** The bundled form and [Representable] / ** 捆绑形式和 [Representable] *)

(*
[Functor/Representable.v]'s [Representable] bundles exactly [ue_obj] plus
   the natural isomorphism, so it is the SAME notion as [UniversalElement],
   not a competing one -- and the two pass into one another through
   [universal_element_representation] with the representing object kept on the
   nose.  That file's header says “by the Yoneda lemma such a Φ is determined
   by a single universal element of F(A), namely Φ_A(id A)” and cites
   Structure/UniversalProperty.v for it; the citation was to the anonymous
   encoding, and these two definitions are the statement in the form the
   sentence promises.

   Both are routed through the DIRECT constructions, not through
   [universal_element_representation], so that they inherit no universe
   constraint from [Yoneda_Lemma] and remain usable at categories whose
   objects sit strictly above their homs.  [routes_agree_elem] and
   [routes_agree_repr] record that the choice costs nothing.

--------
[Functor/Representable.v] 的 [Representable] 正好捆绑了 [ue_obj] 加上自然同构，所以它与 [UniversalElement] 是相同的概念，而不是竞争的概念——并且两者通过 [universal_element_representation] 相互转换，同时保持表示对象不变。该文件的头部写着“根据 Yoneda 引理，这样的 Φ 由 F(A) 的单个通用元素决定，即 Φ_A(id A)”，并引用了 Structure/UniversalProperty.v；该引用是针对匿名编码的，这两个定义就是句子所承诺的形式的陈述。

两者都通过 DIRECT 构造，而不是通过 [universal_element_representation]，因此它们不会继承 [Yoneda_Lemma] 的任何宇宙约束，并且仍可在其对象严格高于 Hom 的范畴中使用。[routes_agree_elem] 和 [routes_agree_repr] 记录了这一选择不产生任何成本。
*)

Definition UniversalElement_of_Representable {H : D ⟶ Sets}
  (R : Representable H) : UniversalElement H :=
  UniversalElement_of_AUniversalElement
    (AUniversalElement_of_repr H (@repr_obj _ _ R) (@represented _ _ R)).

Definition Representable_of_UniversalElement {H : D ⟶ Sets}
  (U : UniversalElement H) : Representable H :=
  {| repr_obj := @ue_obj H U ;
     represented := ue_representation H (@ue_obj H U)
                      (AUniversalElement_of_UniversalElement U) |}.

Corollary ue_of_repr_obj {H : D ⟶ Sets} (R : Representable H) :
  @ue_obj H (UniversalElement_of_Representable R) = @repr_obj _ _ R.
Proof. reflexivity. Qed.

Corollary repr_of_ue_obj {H : D ⟶ Sets} (U : UniversalElement H) :
  @repr_obj _ _ (Representable_of_UniversalElement U) = @ue_obj H U.
Proof. reflexivity. Qed.

(* Mac Lane's Φ_r(id r), for the bundled form. / Mac Lane 的 Φ_r(id r)，用于捆绑形式。 *)
Corollary ue_of_repr_elem {H : D ⟶ Sets} (R : Representable H) :
  @ue_elem H (UniversalElement_of_Representable R)
    = transform (to (@represented _ _ R)) (@repr_obj _ _ R) id{D}.
Proof. reflexivity. Qed.

(** ** Uniqueness up to a unique isomorphism / ** 至多唯一同构的唯一性 *)

(*
Mac Lane's Proposition 1 of §III.1 for this notion, mirroring
   [auniversal_arrow_unique] (Theory/Universal/Arrow.v) clause for clause.
   The predicate cutting the isomorphism down is compatibility with the two
   universal elements, [fmap[H] (to i) e₁ ≈ e₂]; without it the statement
   would be false for the same reason it is false for universal arrows (the
   universal object can have automorphisms).

--------
对于这个概念，Mac Lane 在 §III.1 中的命题 1，逐条对应 [auniversal_arrow_unique] (Theory/Universal/Arrow.v) 中的条款。切断同构的谓词是与两个泛元的兼容性，[fmap[H] (到 i) e₁ ≈ e₂]; 如果没有它，对于相同的原因（泛箭头为假，泛对象可能有自同构），该命题将是错误的。
*)

Section UniversalElementUnique.

Context {H : D ⟶ Sets}.

Definition ue_med {a b : D} (U1 : AUniversalElement H a)
           (U2 : AUniversalElement H b) : a ~{D}~> b :=
  unique_obj (@aue_universal H a U1 b (@aue_elem H b U2)).

Lemma ue_med_commutes {a b : D} (U1 : AUniversalElement H a)
      (U2 : AUniversalElement H b) :
  fmap[H] (ue_med U1 U2) (@aue_elem H a U1) ≈ @aue_elem H b U2.
Proof.
  exact (unique_property (@aue_universal H a U1 b (@aue_elem H b U2))).
Qed.

Lemma ue_med_unique {a b : D} (U1 : AUniversalElement H a)
      (U2 : AUniversalElement H b) (g : a ~{D}~> b) :
  fmap[H] g (@aue_elem H a U1) ≈ @aue_elem H b U2 → ue_med U1 U2 ≈ g.
Proof.
  intro Hg.
  exact (uniqueness (@aue_universal H a U1 b (@aue_elem H b U2)) g Hg).
Qed.

Lemma ue_med_id {a : D} (U1 : AUniversalElement H a) : ue_med U1 U1 ≈ id.
Proof.
  apply ue_med_unique.
  exact (@fmap_id _ _ H a (@aue_elem H a U1)).
Qed.

Lemma ue_med_comp {a b e : D} (U1 : AUniversalElement H a)
      (U2 : AUniversalElement H b) (U3 : AUniversalElement H e) :
  ue_med U2 U3 ∘ ue_med U1 U2 ≈ ue_med U1 U3.
Proof.
  symmetry.
  apply ue_med_unique.
  transitivity (fmap[H] (ue_med U2 U3) (fmap[H] (ue_med U1 U2) (@aue_elem H a U1))).
  - exact (@fmap_comp _ _ H _ _ _ (ue_med U2 U3) (ue_med U1 U2) (@aue_elem H a U1)).
  - transitivity (fmap[H] (ue_med U2 U3) (@aue_elem H b U2)).
    + apply proper_morphism, ue_med_commutes.
    + apply ue_med_commutes.
Qed.

Program Definition universal_element_iso {a b : D}
        (U1 : AUniversalElement H a) (U2 : AUniversalElement H b) : a ≅ b := {|
  to   := ue_med U1 U2;
  from := ue_med U2 U1
|}.
Next Obligation. rewrite ue_med_comp; apply ue_med_id. Qed.
Next Obligation. rewrite ue_med_comp; apply ue_med_id. Qed.

Lemma universal_element_iso_unique {a b : D} (U1 : AUniversalElement H a)
      (U2 : AUniversalElement H b) (v : a ≅ b) :
  fmap[H] (to v) (@aue_elem H a U1) ≈ @aue_elem H b U2 →
  universal_element_iso U1 U2 ≈ v.
Proof.
  intro Hv.
  apply to_equiv_implies_iso_equiv; simpl.
  now apply ue_med_unique.
Qed.

Program Definition universal_element_unique {a b : D}
        (U1 : AUniversalElement H a) (U2 : AUniversalElement H b) :
  Unique (fun i : a ≅ b =>
            fmap[H] (to i) (@aue_elem H a U1) ≈ @aue_elem H b U2) := {|
  unique_obj      := universal_element_iso U1 U2;
  unique_property := ue_med_commutes U1 U2
|}.
Next Obligation. exact (universal_element_iso_unique U1 U2 v X). Qed.

End UniversalElementUnique.

(** ** Deliverable 3(a): universal elements are universal arrows from 1 / ** 交付物 3(a)：通用元素是从 1 出发的通用箭头 *)

(*
Mac Lane's Remark 3, first half.  The passage is not definitional: an
   [AUniversalArrow SetsOne H r] quantifies over MAPS f : 1 ~> H d and states
   its clause as an equation of maps, while an [AUniversalElement H r]
   quantifies over ELEMENTS x : H d and states it as an equation of elements.
   The two are interchanged by [global_element] and evaluation at [ttt], and
   the single [destruct] on [poly_unit] in each direction is the whole
   difference.

--------
Mac Lane 的 Remark 3，前半部分。这段文字不是定义性的：一个 [AUniversalArrow SetsOne H r] 对 MAPS f : 1 ~> H d 进行量化，并以映射方程的形式陈述其子句，而一个 [AUniversalElement H r] 对 ELEMENTS x : H d 进行量化，并以元素方程的形式陈述。通过 [global_element] 和在 [ttt] 的求值可以互换这两者，并且在每个方向上，[poly_unit] 上的单个 [destruct] 就是全部差异。
*)

Section OnePoint.

Context (H : D ⟶ Sets).
Context (r : D).

Definition AUniversalElement_of_AUniversalArrow
  (U : AUniversalArrow SetsOne H r) : AUniversalElement H r.
Proof.
  unshelve econstructor.
  - exact (@universal_arrow _ _ SetsOne H r U ttt).
  - intros d x.
    unshelve eexists
      (unique_obj (@universal_arrow_universal _ _ SetsOne H r U d
                     (@global_element (fobj[H] d) x))).
    + exact (unique_property
               (@universal_arrow_universal _ _ SetsOne H r U d
                  (@global_element (fobj[H] d) x)) ttt).
    + intros v Hv.
      apply (uniqueness
               (@universal_arrow_universal _ _ SetsOne H r U d
                  (@global_element (fobj[H] d) x))).
      intros []; exact Hv.
Defined.

Definition AUniversalArrow_of_AUniversalElement
  (U : AUniversalElement H r) : AUniversalArrow SetsOne H r.
Proof.
  unshelve econstructor.
  - exact (@global_element (fobj[H] r) (@aue_elem H r U)).
  - intros d f.
    unshelve eexists (unique_obj (aue_universal d (f ttt))).
    + intros []; exact (unique_property (aue_universal d (f ttt))).
    + intros v Hv.
      apply (uniqueness (aue_universal d (f ttt))).
      exact (Hv ttt).
Defined.

(* Both passages keep the datum on the nose. / 这两个段落都保持数据在正点上。 *)
Corollary aue_of_aua_elem (U : AUniversalArrow SetsOne H r) :
  @aue_elem H r (AUniversalElement_of_AUniversalArrow U)
    = @universal_arrow _ _ SetsOne H r U ttt.
Proof. reflexivity. Qed.

Corollary aua_of_aue_arrow (U : AUniversalElement H r) :
  @universal_arrow _ _ SetsOne H r (AUniversalArrow_of_AUniversalElement U)
    = @global_element (fobj[H] r) (@aue_elem H r U).
Proof. reflexivity. Qed.

(*
... and so the element survives the element-side round trip by [eq_refl],
   while the arrow survives the arrow-side one only up to `≈` -- rebuilding a
   map out of the singleton from its value at [ttt] is [global_elements_iso]'s
   non-definitional leg, and it lands here.

--------
... 因此，该元素通过 [eq_refl] 完成元素端的往返，而箭头仅在箭头端生存到 `≈` —— 从其在 [ttt] 的值重建一个单例的映射是 [global_elements_iso] 的非定义性步骤，它落在这里。
*)
Corollary aue_aua_round (U : AUniversalElement H r) :
  @aue_elem H r
    (AUniversalElement_of_AUniversalArrow (AUniversalArrow_of_AUniversalElement U))
    = @aue_elem H r U.
Proof. reflexivity. Qed.

Corollary aua_aue_round (U : AUniversalArrow SetsOne H r) :
  @universal_arrow _ _ SetsOne H r
    (AUniversalArrow_of_AUniversalElement (AUniversalElement_of_AUniversalArrow U))
    ≈ @universal_arrow _ _ SetsOne H r U.
Proof. intros []; reflexivity. Qed.

End OnePoint.

End UniversalElement.

(** ** Deliverable 3(b): universal arrows are universal elements of D(c, S−) / ** 可交付成果 3(b)：通用箭头是 D(c, S−) 的通用元素 *)

(*
Mac Lane's Remark 3, second half, and it is CHEAPER than the first.
   [fobj[Curried_Hom C] c] is the covariant hom-functor [Hom c,─], whose
   [fmap] at h is postcomposition with h; so the composite
   [Hom c,─] ◯ S : D ⟶ Sets is Mac Lane's D(c, S−), its elements at d are the
   morphisms c ~> S d, and

       fmap[[Hom c,─] ◯ S] k u   IS   fmap[S] k ∘ u

   BY CONVERSION.  Hence [AUniversalElement ([Hom c,─] ◯ S) a] and
   [AUniversalArrow c S a] have field types that are convertible one for one,
   the two passages below are [:=] with no tactic, and -- record eta being
   available under primitive projections -- both round trips are [eq_refl] on
   the WHOLE record, not merely on the arrow.

--------
Mac Lane 的备注 3，后半部分，并且它比第一部分更便宜。
   [fobj[Curried_Hom C] c] 是协变 Hom 函子 [Hom c,─]，其
   [fmap] 在 h 上是与 h 的后置组合；因此复合
   [Hom c,─] ◯ S : D ⟶ Sets 是 Mac Lane 的 D(c, S−)，其在 d 上的元素是
   从 c 到 S d 的态射，且

       fmap[[Hom c,─] ◯ S] k u   等于   fmap[S] k ∘ u

   通过转换。因此 [AUniversalElement ([Hom c,─] ◯ S) a] 和
   [AUniversalArrow c S a] 有可逐一转换的字段类型，下面的两段是 [:=]，无需策略，且——在原始投影下可用记录 eta ——两个往返都是在整个记录上的 [eq_refl]，而不仅仅是在箭头上。
*)

Section HomFunctor.

Context {C : Category}.
Context {D : Category}.
Context (S : D ⟶ C).
Context (c : C).

(* Mac Lane's D(c, S−). / Mac Lane 的 D(c, S−)。 *)
Definition HomAfter : D ⟶ Sets := @Compose D C Sets (fobj[@Curried_Hom C] c) S.

(* The two clauses ARE the same clause. / 这两个从句是同一个从句。 *)
Lemma hom_after_fmap (d d' : D) (k : d ~{D}~> d') (u : c ~{C}~> S d) :
  fmap[HomAfter] k u = fmap[S] k ∘ u.
Proof. reflexivity. Qed.

(*
[@Build_...] rather than the `{| ... |}` literal: for a Class, the literal
   sends the elaborator looking for an instance of the head, and here it
   guesses [?H] before [HomAfter] is available to fix it.

--------
[@Build_...] 而不是 `{| ... |}` 字面值：对于一个类来说，这个字面值会让展开器去寻找头部的一个实例，而这里它在 [HomAfter] 可用来修复之前就猜测了 [?H]。
*)
Definition AUniversalElement_of_hom {a : D} (U : AUniversalArrow c S a)
  : AUniversalElement HomAfter a :=
  @Build_AUniversalElement D HomAfter a
    (@universal_arrow C D c S a U)
    (fun d x => @universal_arrow_universal C D c S a U d x).

Definition AUniversalArrow_of_hom {a : D} (U : AUniversalElement HomAfter a)
  : AUniversalArrow c S a :=
  @Build_AUniversalArrow C D c S a
    (@aue_elem D HomAfter a U)
    (fun d f => @aue_universal D HomAfter a U d f).

Corollary aue_of_hom_round {a : D} (U : AUniversalElement HomAfter a) :
  AUniversalElement_of_hom (AUniversalArrow_of_hom U) = U.
Proof. reflexivity. Qed.

Corollary aua_of_hom_round {a : D} (U : AUniversalArrow c S a) :
  AUniversalArrow_of_hom (AUniversalElement_of_hom U) = U.
Proof. reflexivity. Qed.

End HomFunctor.

(** ** The subsumption Mac Lane asserts, as one theorem / ** 麦克莱恩所断言的归纳，作为一个定理 *)

(*
Remark 3 in full.  The tree carried neither half; stating them together is
   the point, because what Mac Lane claims is that the two notions are
   INTERDEFINABLE, and that claim is visible only when both directions sit in
   one statement.  Each component is a pair of maps, not a bijection: 3(a) is
   a bijection up to the round trips recorded above, and 3(b) is one on the
   nose.

--------
完整的注释3。树既不包含任一部分；将它们一起陈述的重点在于，麦克·莱恩声称这两个概念是可以相互定义的，这一主张只有当两个方向都出现在同一陈述中时才能看出。每个组成部分都是一对映射，而不是一个双射：3(a)在上面记录的往返之下是一个双射，而3(b)则是一个严格的双射。
*)
Theorem universal_element_arrow_subsumption
  {C : Category} {D : Category} (S : D ⟶ C) (c : C) (H : D ⟶ Sets) (r : D) :
  (*
(a) a universal element of H is a universal arrow from the one-point
         setoid to H, and conversely

--------
(a) H 的一个全域元素是从单点集合到 H 的全域箭头，反之亦然
*)
  ((AUniversalArrow SetsOne H r → AUniversalElement H r) *
   (AUniversalElement H r → AUniversalArrow SetsOne H r))
  *
  (*
(b) a universal arrow from c to S is a universal element of D(c, S−),
         and conversely

--------
(b) 从 c 到 S 的一个通用箭头是 D(c, S−) 的一个通用元素，反之亦然
*)
  ((AUniversalArrow c S r → AUniversalElement (HomAfter S c) r) *
   (AUniversalElement (HomAfter S c) r → AUniversalArrow c S r)).
Proof.
  split; split.
  - exact (AUniversalElement_of_AUniversalArrow H r).
  - exact (AUniversalArrow_of_AUniversalElement H r).
  - exact (@AUniversalElement_of_hom C D S c r).
  - exact (@AUniversalArrow_of_hom C D S c r).
Defined.

(*
The two halves compose, and the composite is not vacuous: starting from a
   universal arrow ⟨a, u⟩ from c to S, reading it as a universal element of
   D(c, S−) by (b) and then back out as a universal arrow from the SINGLETON
   to that functor by (a) returns the same underlying morphism, up to the
   evaluation [global_element] performs.  This is the round trip that only
   exists once both halves are present.

--------
这两个部分组合在一起，而组合并非空洞：从一个从 c 到 S 的通用箭头 ⟨a, u⟩ 出发，通过 (b) 将其作为 D(c, S−) 的通用元素来读取，然后再通过 (a) 将其作为从 SINGLETON 到该函子（functor）的通用箭头读出，返回相同的基础态射（morphism），在 [global_element] 执行的评估下也是如此。这就是只有当两个部分都存在时才存在的往返过程。
*)
Corollary subsumption_composite {C D : Category} (S : D ⟶ C) (c : C) (a : D)
  (U : AUniversalArrow c S a) :
  (@universal_arrow _ _ SetsOne (HomAfter S c) a
     (AUniversalArrow_of_AUniversalElement (HomAfter S c) a
        (AUniversalElement_of_hom S c U)) ttt : c ~{C}~> fobj[S] a)
  = @universal_arrow C D c S a U.
Proof. reflexivity. Qed.

(** ** Naturality of the global-elements isomorphism / ** 全体元素同构的自然性 *)

(*
Riehl, _Category Theory in Context_, 2nd ed., SS3.2, printed pp. 93-94:
   the display [lim F ≅ Set( *, lim F) ≅ Cone( *, F)] that motivates the
   cone-set construction of Instance/Sets/Complete.v.  Its FIRST
   isomorphism is [global_elements_iso] above -- the OBJECT-LEVEL statement
   pre-existed this addition, was declared at the [global_elements_iso]
   above, and is already described by this file's own header.  What was
   missing, and is added here, is only Riehl's “natural in X”: nothing in
   the tree exhibited [GlobalElements] as a FUNCTOR, so the isomorphism was
   a FAMILY and not a natural one.

   [GlobalElements] IS the representable [Hom 1,─] on the nose, and
   [SetsOne] IS the terminal object on the nose -- both recorded by
   [eq_refl] below -- so the functor is already in the tree and the
   naturality statement is an isomorphism in [[Sets, Sets]] between it and
   the identity.  Five of the six clauses are closed by the file's default
   obligation tactic -- the tree-wide one, this file setting none -- and NOT
   by [reflexivity], which an earlier revision of this sentence claimed and
   did not measure; the comment at the definition itself says the weaker
   thing.  The sixth is the singleton's unique-inhabitant property, spent in
   one [destruct u] exactly as [global_elements_iso]'s own second clause
   spends it.

   THIS IS NOT NEEDED BY THE CONE-SET LIMIT, and is delivered because
   Riehl's checkbox asks for it.  Instance/Sets/Complete.v's construction
   spends the singleton directly, by the same [destruct], and does not
   Require this module; consuming it there instead would cost that file
   NINETEEN further modules of closure (33 to 52, measured by set
   difference; an earlier revision said sixteen).

--------
Riehl，《上下文中的范畴论》，第2版，第3.2节，印刷页 93-94：
   显示 [lim F ≅ Set( *, lim F) ≅ Cone( *, F)] 激发了 Instance/Sets/Complete.v 的锥集构造。它的第一个同构是上面的 [global_elements_iso]——对象级的陈述在这一补充之前就已经存在，在上面的 [global_elements_iso] 处被声明，并且已经由本文件的标题描述。缺失的、并在这里添加的，只是 Riehl 的“在 X 中自然”：在所展示的树中没有任何 [GlobalElements] 是函子，因此该同构是一个族而不是自然的。

[GlobalElements] 是 [Hom 1,─] 在鼻子上的可表示对象，而 [SetsOne] 是鼻子上的终端对象——两者都由下面的 [eq_refl] 记录——所以函子已经在树中，自然性陈述在 [[Sets, Sets] 中是它与恒等之间的同构。文件默认的义务策略关闭了六个条款中的五个——整个树范围的策略，这个文件设置为无——而不是由 [reflexivity] 关闭的，早期版本的这个句子声称它并未测量；定义本身的注释指出了较弱的情况。第六个是单元集合唯一元素的属性，在一个 [destruct u] 中花费，就像 [global_elements_iso] 的第二个条款花费它一样。

这不是由圆锥集合限制所需要的，而且是因为 Riehl 的复选框要求而提供的。Instance/Sets/Complete.v 的构造直接使用了该单例，通过相同的 [destruct]，并不需要这个模块；如果在那里消耗它，将会使该文件额外消耗十九个闭包模块（从 33 增加到 52，通过集合差异测量；之前的版本说是十六个）。
*)

(*
[SetsOne] is the terminal setoid.  Read this at its true strength: it
   holds by DELTA, not by computation -- Construction/Elements.v declares
   [SetsOne := @terminal_obj Sets Sets_Terminal], so [Print SetsOne] answers
   [1] -- so it pins that this file's [SetsOne] is still that definition and
   nothing more.  It is kept as that guard rather than presented as a
   measurement.  The next Example is not of this kind.

--------
[SetsOne] 是终端集合。以它的真正力量来阅读：它是通过 DELTA 支持的，而不是通过计算——Construction/Elements.v 声明了 [SetsOne := @terminal_obj Sets Sets_Terminal]，所以 [Print SetsOne] 回应 [1]——因此它确定这个文件的 [SetsOne] 仍然是那个定义，别无其他。它被保持为那个护卫，而不是作为测量来展示。下一个例子不是这种类型。
*)
Example setsone_is_terminal :
  SetsOne = @terminal_obj Sets Sets_Terminal := eq_refl.

(* [GlobalElements] is the representable [Hom 1,─]. / [GlobalElements] 是可表示的 [Hom 1,─]。 *)
Example global_elements_is_hom (X : obj[Sets]) :
  GlobalElements X = fobj[fobj[Curried_Hom Sets] SetsOne] X := eq_refl.

(* Riehl's first isomorphism, natural in X. / Riehl 的第一个同构，关于 X 是自然的。 *)
Program Definition global_elements_natural :
  @Isomorphism ([Sets, Sets]) (fobj[Curried_Hom Sets] SetsOne) Id[Sets] := {|
  to   := {| transform := global_elements_to |};
  from := {| transform := global_elements_from |}
|}.
(*
Five of the six obligations -- both naturality squares of each
   transformation, and one inverse law -- are closed by the file's default
   obligation tactic.  The sixth is the singleton step.

--------
六个义务中的五个——每个变换的自然平方以及一个逆律——都由文件的默认义务策略完成。第六个是单例步骤。
*)
Next Obligation.
  match goal with [ H : poly_unit |- _ ] => destruct H end; reflexivity.
Qed.

(* Its components are the pre-existing maps, on the nose. / 它的组成部分是现有的地图，正如字面意思。 *)
Example global_elements_natural_to (X : obj[Sets]) :
  transform[to global_elements_natural] X = global_elements_to X := eq_refl.

Example global_elements_natural_from (X : obj[Sets]) :
  transform[from global_elements_natural] X = global_elements_from X
  := eq_refl.
