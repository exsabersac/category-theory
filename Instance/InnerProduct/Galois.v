(* * * The orthogonal complement as a Galois connection / * * 作为伽罗瓦联系的正交补 *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Instance.Grp.Galois.
Require Import Category.Adjunction.Right.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

(*
 The same two as Instance/Powerset.v and Instance/Grp/Galois.v,
 in the same position and for the same reason: [relation] and [PreOrder]
 below must be the stdlib Prop-valued ones rather than Category.Lib's
 [crelation] ones, so they are required LAST. 

 --------
 与 Instance/Powerset.v 和 Instance/Grp/Galois.v 中的两个相同，
 位置相同，原因相同：下面的 [relation] 和 [PreOrder] 必须是 stdlib 中 Prop 值的，而不是 Category.Lib 的 [crelation]，因此它们必须最后加载。
*)
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(*
   * Mac Lane, “Categories for the Working Mathematician”, 2nd ed., §IV.5,
   book p. 97 (PDF p. 106), Exercise 1.  Item covered:
   [maclane:IV.5:ex1].  Read from the page image, verbatim:

   “1. Let H be a space with an inner product (e.g., Hilbert space).
   If P = Q is the set of all subsets S of H, ordered by inclusion,
   show that LS = RS = the orthogonal complement of S gives a Galois
   connection.”

   ** WHICH ABSTRACTION OF “INNER PRODUCT”, AND WHY

   None.  The exercise's content is the Galois connection, not the
   analysis, and the ONLY property of an inner product that the
   connection consumes is that the derived relation “x is orthogonal to
   y” is SYMMETRIC.  So the ambient structure taken here is a
   [PerpRel X]: a [Prop]-valued binary relation on the carrier of a
   setoid, symmetric, and respecting the setoid's own [≈].  Nothing
   else -- no addition, no scalars, no positivity, no completeness, no
   bilinearity -- appears anywhere below, and the issue's own Work item 1
   names this as the recommended scope (“an abstract 'orthogonality
   relation' satisfying the two properties actually used ... much
   cheaper”).

   Two remarks on the fidelity of that abstraction.  First, symmetry is
   the right demand even in the complex case: a Hermitian form is
   conjugate-symmetric rather than symmetric, but the RELATION
   “⟨x,y⟩ = 0” is symmetric all the same, since a complex number
   vanishes exactly when its conjugate does.  Second, nothing here
   demands that the relation be irreflexive, or that only the zero
   vector be orthogonal to itself: over a field of characteristic two
   the standard form has isotropic vectors, and the development is
   indifferent to that.  The ℤ² witness in section (G) is chosen
   precisely so that the non-degenerate reading can be exhibited.

   ** THE NAME COLLISION, DISCLOSED

   Theory/Orthogonality.v declares [Class Orthogonal] with the
   notation [e ⫫ m], for the unique-lifting relation between a morphism
   and a morphism in a factorization system.  That is a DIFFERENT
   notion -- a property of a commuting square in a category, with no
   perpendicularity operator and no power set anywhere near it -- and it
   is a homonym only.  Consequently no name in this file is spelled
   [Orthogonal], [orthogonal] or [⫫]; everything is spelled [perp].  At
   the base commit the tokens [perp], [Perp], [PerpRel], [perp_set],
   [ClosedPerp], [perp_galois], [PerpOp] and [InnerProduct] each occur in
   ZERO [.v] files, and the tokens “inner product”, “orthogonal
   complement” and “sesquilinear” occur in none; the only “Hilbert” hits
   are four lines of prose (Theory/Algebra/Frobenius.v,
   Structure/Dagger.v, Theory/Adjunction.v,
   Structure/Monoidal/Symmetric.v).  So the issue's “Current state” is
   accurate on the ambient structure, and its two named dependencies have
   since landed and are CONSUMED here rather than rebuilt.

   ** WHAT IS CONSUMED

   From #380 (Instance/Proset/Galois.v): the record
   [GaloisConnection] with its six fields, [gal_unit] and
   [gal_counit], the two functors
   [GaloisFunctor_l]/[GaloisFunctor_r] and [GaloisAdjunction].  From #382
   (Instance/Powerset.v): [subset_le],
   [subset_le_preorder] and the thin category [Subsets X], over
   Instance/Sets/Powerset.v's [Powerset_Prop_obj X], the
   [≈]-respecting [Prop]-valued predicates.  From
   Instance/Proset/Limit.v: [op_rel], the reversed preorder, which is
   how Mac Lane's [Q^op] is written here.  From Instance/Grp/Galois.v:
   six constants of its section (A) -- [gal_lrl_below],
   [gal_lrl_above], [GalClosed_l], [GalClosed_r],
   [gal_closed_r_image] and [gal_closed_r_iff] -- which is
   general over an arbitrary Galois connection and mentions no group,
   together with [subset_le_antisym].  Those are APPLIED at the new
   connection; not one of them is restated.  Section (A) carries four
   constants besides those six ([gal_rlr_below], [gal_rlr_above],
   [gal_closed_l_image], [gal_closed_l_iff]); this connection needs none
   of them, because [gal_l] and [gal_r] here are ONE map, so each
   left-handed statement and its right-handed twin have become the same
   statement.

   That last [Require] is the expensive one, and the header gives the
   number rather than leaving a reader to discover it.  The transitive
   in-project closure of this file, excluding itself, is 130 modules; with
   Instance/Grp/Galois dropped it is 91, so consuming #381's section (A)
   costs 39 modules, and every other [Require] in the list costs zero
   (each was dropped alone and measured).  Section (A) is group-free, so
   its natural home is Instance/Proset/Galois.v beside the record it is
   about; but [subset_le_antisym] sits OUTSIDE that section and
   is used in the proofs below, so moving section (A) alone would return
   NONE of the 39 -- the [Require] would stay for that one lemma (an
   audit caught an earlier draft saying it would return them all).
   Returning them needs [subset_le_antisym] moved too, its natural home
   being Instance/Powerset.v beside [subset_le], or written inline as
   Instance/Powerset/Quantifier.v does.  Nothing is moved
   here: editing a merged module is out of scope for this issue, and the
   alternative -- restating those six short general lemmas under fresh
   names -- is what consuming a donor is supposed to avoid.

   ** THE SELF-DUALITY, WHICH IS WHAT MAKES THIS EXERCISE SHORT

   Mac Lane writes [L S = R S].  Here that is not a remark but an
   equation between the two fields of one record: [perp_galois_l_is_r]
   closes by [eq_refl].  Three further coincidences follow and are each
   pinned, because each of them is the kind of thing a reader would
   otherwise have to take on trust.

   - The two halves of the displayed biconditional are ONE function at
   swapped arguments.  [perp_transpose] carries [S ⊆ T^perp] to
   [T ⊆ S^perp]; [gal_to] and [gal_from] of the connection are that
   same term with its two subset arguments exchanged, and
   [perp_to_is_from_swapped] records it at [eq_refl].  The whole
   content of the biconditional is one permutation of two universal
   quantifiers followed by one appeal to symmetry of the relation.

   - The unit and the counit inhabit the SAME type and are the SAME
   term ([perp_unit_is_counit], [eq_refl]).  Read at the reversed
   order the counit inequality IS the unit inequality, which is why
   [S ⊆ S^⊥⊥] is the only closure inequality this connection has.

   - [GalClosed_l] and [GalClosed_r] of the connection are the same
   proposition ([ClosedPerp_is_GalClosed_l] and [_r], both
   [eq_refl]), so there is one notion of closedness rather than two.

   ** NO TRUNCATION IS NEEDED, WHICH IS A DIFFERENCE FROM #381

   Instance/Grp/Galois.v's [fixes] has to squash its defining condition,
   because that condition is [act A s x ≈ x] and [≈] is [Type]-valued
   while a member of [Powerset_Prop_obj] must be a [Prop].  Here the
   orthogonality relation is [Prop]-valued BY DECLARATION -- that is one
   of the two design decisions the [PerpRel] record makes -- so
   [Powerset_squash] appears nowhere in this file and every membership
   argument is a plain implication.  The setoid discipline is paid for
   instead by the [perp_respects] field, which is exactly what makes
   [perp_set S] a [SetoidMorphism] and hence an element of the power
   set.

   ** WHAT THE WITNESS IS, AND WHAT IT IS NOT

   Mac Lane's Hilbert space is out of reach: the tree carries no
   inner-product structure of any kind, and building one over the
   standard library reals would buy nothing the exercise asks for while
   costing the two reals axioms.  The witness in section (G) is ℤ² with
   the ordinary dot product [⟨(a,b),(c,d)⟩ = a·c + b·d], over stdlib [Z],
   axiom-free and computing.  It is a genuine bilinear form on a free
   module of rank two; what it is not is a Hilbert space, and no claim is
   made that it is.

   The alternative [bool × bool] over the two-element field was
   considered and not used, as a matter of illustration rather than
   necessity: over ℤ the values of the form are integers a reader can
   compute, and every negative closes by arithmetic.  Over F₂ the same
   statements are provable (measured out of tree by an audit, at the
   analogue of e₁), but there the isotropic vector [(1,1)] lies in the
   complement of its own singleton, which makes that base a poorer
   picture of an orthogonal complement.  Read [zz_e1_not_self_perp] at
   its strength: it is a statement about ONE point, and over ℤ the
   origin does lie in the complement of [{(0,0)}], so no universal
   “no point lies in its own complement” is claimed on either base.
   An earlier draft of this paragraph said the F₂ statement “would be
   refuted”, contradicting the remark on isotropic vectors above; an
   audit measured it, and it was false.

   Every negative in section (G) is obtained by COMPUTATION on [Z]
   followed by [lia] or [injection], never by induction over a
   quotienting relation -- there is no such relation here, the power set
   being a predicate setoid rather than a quotient.

   ** UNIVERSES

   The general development binds [X : SetoidObject@{o o}] explicitly,
   with [Set < o] declared at section level.  That identification of a
   setoid's carrier and relation levels is the DONORS' and not this
   file's: [Powerset_Prop_obj@{o}] is declared over [SetoidObject@{o o}],
   and [Subsets] over the same, as #381 and #384 both measure.  [Set < o]
   is [Powerset_Prop_obj]'s own, its truth object having carrier [Prop].
   No constraint block below carries a universe EQUATION.

   ** WHAT IS NOT DELIVERED

   No inner product, no bilinear form as a structure, no vector space and
   no analysis; no completeness, no closed SUBSPACES (the closed elements
   here are closed subsets in the Galois sense, which over a genuine
   inner-product space would be the closed linear subspaces -- that
   identification needs the linear structure and is not attempted); no
   antisymmetric quotient, so [Subsets X] is a preorder and two
   [≈]-equal complements are distinct isomorphic objects; no lattice of
   closed elements and no orthomodularity; no naturality of any
   identification in [X] or in [P]; no functoriality of [perp_set] in the
   relation; no comparison with Structure/Dagger.v's dagger categories;
   and nothing is registered as an [Instance] -- a chosen orthogonality
   relation must not become globally resolvable, matching
   Instance/Powerset.v's own note on its meets and joins. 

   --------
   * Mac Lane，《为工作数学家准备的范畴论》，第2版，第IV.5节，书本第97页（PDF第106页），练习1。涵盖内容：[maclane:IV.5:ex1]。逐字阅读页面图片内容：

   “1. 设 H 是一个带内积的空间（例如，希尔伯特空间）。如果 P = Q 是 H 的所有子集 S 构成的集合，并按包含关系排序，证明 LS = RS = S 的正交补给出了一个 Galois 连接。”

   ** “内积”的哪种抽象，以及为什么无。这个练习的内容是伽罗瓦联系，而不是分析，并且这个联系所依赖的内积的唯一性质是派生关系“x 与 y 正交”是对称的。因此，这里考虑的环境结构是 [PerpRel X]：定义在集合的载体上的 [Prop] 值二元关系，对称，并且尊重集合自身的 [≈]。除此之外没有其他——没有加法、没有标量、没有正性、没有完备性、没有双线性——这些在下面都不会出现，并且该问题的工作项 1 自身将其命名为推荐的范围（“一个满足实际使用的两个性质的抽象‘正交关系’……更便宜”）。关于该抽象的忠实性有两点说明。首先，即使在复数情况下，对称性也是正确的要求：厄米形式是共轭对称的而非对称的，但关系“⟨x,y⟩ = 0”仍然是对称的，因为一个复数在其共轭为零时恰好为零。其次，这里没有要求该关系是无反身的，或者只有零向量与自身正交：在特征为二的域上，标准形式存在各向同性向量，而且这种发展方式对此无关紧要。第(G)节中的ℤ²示例正是为了能够展示非退化的读法而选择的。

   ** 名称冲突，已披露Theory/Orthogonality.v 使用记号 [e ⫫ m] 声明了 [Class Orthogonal]，用于表示一个态射与分解系统中态射之间的唯一提升关系。这是一个不同的概念——范畴中交换方形的一个性质，没有垂直操作符，也没有幂集——它只是一个同音异义词。因此，该文件中的任何名称都不会拼写为 [Orthogonal]、[orthogonal] 或 [⫫]；所有名称都拼写为 [perp]。在基础提交中，标记 [perp]、[Perp]、[PerpRel]、[perp_set]、[ClosedPerp]、[perp_galois]、[PerpOp] 和 [InnerProduct] 每一个都出现在零个 [.v] 文件中，而标记“inner product”“orthogonal complement”和“sesquilinear”都未出现；唯一的“Hilbert”命中是四行散文（Theory/Algebra/Frobenius.v、Structure/Dagger.v、Theory/Adjunction.v、Structure/Monoidal/Symmetric.v）。所以问题的“当前状态”在环境结构上是准确的，其两个命名依赖已经完成，并且在这里被使用而不是重新构建。

   ** 什么是已使用来自 #380 (Instance/Proset/Galois.v)：记录 [GaloisConnection] 及其六个字段，[gal_unit] 和 [gal_counit]，两个函子 [GaloisFunctor_l] / [GaloisFunctor_r] 和 [GaloisAdjunction]。来自 #382 (Instance/Powerset.v)：[subset_le]，[subset_le_preorder] 以及薄范畴 [Subsets X]，基于 Instance/Sets/Powerset.v 的 [Powerset_Prop_obj X]，[≈]-保持的 [Prop] 值谓词。来自 Instance/Proset/Limit.v：[op_rel]，逆序预序，这是这里 Mac Lane 的 [Q^op] 的写法。来自 Instance/Grp/Galois.v：其区段 (A) 的六个常数——[gal_lrl_below]，[gal_lrl_above]，[GalClosed_l]，[GalClosed_r]，[gal_closed_r_image] 和 [gal_closed_r_iff]——适用于任意 Galois 连接且未提及任何群，连同 [subset_le_antisym]。这些内容被应用于新的连接；其中没有一个被重新陈述。（A）部分除了那六个常量（[gal_rlr_below]、[gal_rlr_above]、[gal_closed_l_image]、[gal_closed_l_iff]）外，还有四个常量；此连接不需要它们中的任何一个，因为这里的[gal_l]和[gal_r]是同一张图，所以每个左手声明及其右手双胞胎已经变成相同的声明。最后那个 [Require] 是昂贵的，标题给出了数字，而不是让读者去发现它。该文件的传递性在项目内的闭包（不包括其本身）是 130 个模块；如果去掉 Instance/Grp/Galois，则是 91，所以消耗 #381 的部分 (A) 花费了 39 个模块，而列表中的每个其他 [Require] 成本为零（每个都是单独删除和测量的）。部分 (A) 是无群的，因此它的自然位置是 Instance/Proset/Galois.v，放在它所涉及的记录旁边；但 [subset_le_antisym] 位于那部分之外，并在下面的证明中使用，所以单独移动部分 (A) 不会返回那 39 个 —— 对于那个引理，[Require] 会保留（一次审核发现早期草稿说它会返回全部）。将它们返回需要 [subset_le_antisym] 也被移动，它的自然位置是 Instance/Powerset.v，位于 [subset_le] 旁边，或者像 Instance/Powerset/Quantifier.v 那样内联编写。这里没有移动任何东西：编辑合并模块超出了本问题的范围，而另一种选择——在新的名字下重新陈述那六个简短的一般引理——正是使用捐赠者所要避免的。

   ** 自对偶性，这正是使这个练习变短的原因

   Mac Lane 写了 [L S = R S]。在这里，这不是一个注释，而是一个记录的两个字段之间的方程：[perp_galois_l_is_r] 由 [eq_refl] 关闭。随后还有三个巧合，每个都被固定，因为它们每一个都是读者否则必须凭信任接受的那种东西。- 显示的双条件命题的两半是一个函数在交换的参数下。[perp_transpose] 将 [S ⊆ T^perp] 映射到 [T ⊆ S^perp]；连接的 [gal_to] 和 [gal_from] 是同一项，只是它的两个子集参数互换，[perp_to_is_from_swapped] 将其记录在 [eq_refl]。双条件的整个内容是一种排列，由两个全称量词随后一次对该关系对称性的调用组成。

   - 单元和余单元属于相同类型，并且是相同的项 ([perp_unit_is_counit], [eq_refl])。在倒序读取时，余单元不等式就是单元不等式，这就是为什么 [S ⊆ S^⊥⊥] 是该连接所具有的唯一闭合不等式。- 连接的 [GalClosed_l] 和 [GalClosed_r] 是相同的命题（[ClosedPerp_is_GalClosed_l] 和 [_r]，都为 [eq_refl]），所以只有一个闭合性的概念，而不是两个。

   ** 不需要截断，这与 #381 不同Instance/Grp/Galois.v 的 [fixes] 必须压缩其定义条件，因为该条件是 [act A s x ≈ x]，而 [≈] 是 [Type] 值的，而 [Powerset_Prop_obj] 的成员必须是 [Prop]。在这里，正交关系通过声明被定义为 [Prop] 值——这是 [PerpRel] 记录所做的两个设计决策之一——因此 [Powerset_squash] 在此文件中未出现，且每个成员论证都是一个普通的蕴涵。集合规范纪律反而由 [perp_respects] 字段体现，这正是使 [perp_set S] 成为 [SetoidMorphism] 从而成为幂集的元素的原因。

   **证据是什么，以及它不是什么麦克莱恩的希尔伯特空间无法实现：这棵树不携带任何类型的内积结构，而在标准库实数上构建一个内积结构既无法得到练习要求的结果，还会损失两个实数公理。第(G)节中的见证是带有普通点积的 ℤ² [⟨(a,b),(c,d)⟩ = a·c + b·d]，在 stdlib [Z] 上，无公理并且可计算。它是秩为二的自由模上的一个真正的双线性形式；它不是希尔伯特空间，也没有声称它是希尔伯特空间。在双元素域上考虑了备选的 [bool × bool]，但没有使用，这更多是为了说明而非必要：在 ℤ 上，形式的取值是读者可以计算的整数，并且每个负数都可以通过算术封闭。在 F₂ 上，相同的陈述也是可证明的（通过在 e₁ 的类比处进行审计从树中衡量），但在那里各向同性向量 [(1,1)] 位于其自身单例的补集内，这使得该基底成为正交补的画面更差。以其强度阅读 [zz_e1_not_self_perp]：这是关于单一点的陈述，并且在 ℤ 上原点确实位于 [{(0,0)}] 的补集中，因此在任何基底上都没有声称“没有点位于其自身的补集内”的普遍性。这段话的早期草稿说 F₂ 语句“将被驳斥”，与上面关于各向同性向量的评论相矛盾；一次审核测量了它，发现它是错误的。

   (G) 节中的每一个否定都是通过在 [Z] 上进行计算，然后再经过 [lia] 或 [injection] 得到的，从来不是通过对商关系进行归纳得到的——这里不存在这样的关系，幂集是谓词集合而不是商。

   ** 宇宙一般开发将 [X : SetoidObject@{o o}] 明确绑定，[Set < o] 在节级别声明。该集合体的载体和关系层级的识别是捐赠者的，而不是此文件的：[Powerset_Prop_obj@{o}] 在 [SetoidObject@{o o}] 上声明，[Subsets] 在同一上声明，正如 #381 和 #384 所示。[Set < o] 是 [Powerset_Prop_obj] 自己的，其真值对象的载体为 [Prop]。下面没有约束块承载宇宙方程。

   ** 未交付内容没有内积，没有作为结构的双线性形式，没有向量空间，也没有分析；没有完备性，没有闭子空间（这里的闭元素是在伽罗瓦意义下的闭子集，在真正的内积空间中，这些将是闭线性子空间——这种对应需要线性结构，但这里没有尝试）；没有反对称商，因此 [Subsets X] 是一个预序，并且两个 [≈] 相等的补集是不同的同构对象；没有闭元素的格，也没有正交模性；在 [X] 或 [P] 中的任何对应关系都没有自然性；[perp_set] 在关系中没有函子性；也没有与 Structure/Dagger.v 的匕首范畴进行比较；并且没有任何东西被注册为 [Instance] ——选定的正交关系不能变成全局性可解的，匹配的
   Instance/Powerset.v 关于其交和并的注释。
*)

(* ------------------------------------------------------------------------ *)
(* * ** (A) The orthogonality relation / * **（A）正交关系 *)

(*
 The whole of the ambient structure.  [perp] is [Prop]-valued, so a
 membership condition built from it needs no truncation; [perp_sym] is
 the one property of an inner product the exercise consumes; and
 [perp_respects] is the setoid discipline, stated as the single
 implication that suffices -- the converse implication is that same
 field read at the two SYMMETRIC equivalences, so nothing is lost, and
 [perp_respects_iff] below states the biconditional the [Proper]
 spelling would give.  Note what that derivation does NOT spend:
 symmetry of [≈], not [perp_sym], is what turns one implication into
 two. 

 --------
 整个环境结构。[perp] 是 [Prop] 值的，因此由它构建的成员条件无需截断；[perp_sym] 是该练习所用的内积唯一性质；而 [perp_respects] 是集合学科，表述为足够的单一蕴涵——反向蕴涵是在两个对称等价下读取相同的域，因此没有损失，而下面的 [perp_respects_iff] 表明 [Proper] 拼写会给出的双条件。注意该推导没有使用的内容：[≈] 的对称性，而非 [perp_sym]，是将一个蕴涵变为两个的关键。
*)
Record PerpRel@{o} (X : SetoidObject@{o o}) := {
  perp : carrier X → carrier X → Prop;
  perp_sym : ∀ x y, perp x y → perp y x;
  perp_respects : ∀ x x' y y', x ≈ x' → y ≈ y' → perp x y → perp x' y'
}.

Arguments perp {X} p x y.
Arguments perp_sym {X} p x y _.
Arguments perp_respects {X} p x x' y y' _ _ _.

(*
 The [Proper (equiv ==> equiv ==> iff)] reading, as a theorem rather
 than as a field: the record carries one implication, and both
 directions follow from it by symmetry of [≈]. 

 --------
 [Proper (equiv ==> equiv ==> iff)] 的读法，作为一个定理而不是一个领域：该记录带来一个含义，并且两个方向都可以从 [≈] 的对称性中得出。
*)
Lemma perp_respects_iff@{o +} {X : SetoidObject@{o o}} (P : PerpRel@{o} X)
  (x x' y y' : carrier X) (Hx : x ≈ x') (Hy : y ≈ y') :
  perp P x y ↔ perp P x' y'.
Proof.
  split; intro H.
  - exact (perp_respects P x x' y y' Hx Hy H).
  - refine (perp_respects P x' x y' y _ _ H); now symmetry.
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** (B) The orthogonal complement, and the transposition / * **（B）正交补和转置 *)

Section Perp.

(*
 [o] is the level at which the setoid, its power set and the inclusion
 preorder all live; [Subsets] demands [SetoidObject@{o o}], which is
 what identifies the carrier and relation levels, and [Set < o] is
 [Powerset_Prop_obj]'s.  [u] is the hom level of the thin categories,
 free of [o]. 

 --------
 [o] 是集合类、其幂集以及包含预序都存在的层级；[Subsets] 需要 [SetoidObject@{o o}]，这正是确定载体和关系层的部分，而 [Set < o] 是 [Powerset_Prop_obj] 的。[u] 是薄范畴的同态层级，不受 [o] 的约束。
*)
Universe o u.
Constraint Set < o.

Context {X : SetoidObject@{o o}}.
Context (P : PerpRel@{o} X).

(*
 Mac Lane's orthogonal complement: the points orthogonal to every member
 of [S].  Respectfulness in the point is [perp_respects] read forward and
 backward, which is where [≈] of the ambient setoid is paid for. 

 --------
 Mac Lane 的正交补：与 [S] 的每个元素正交的点。在点上的尊重是 [perp_respects] 正着读和反着读，这就是对环境集合 [≈] 的回报。
*)
Definition perp_set (S : carrier (Powerset_Prop_obj@{o} X)) :
  carrier (Powerset_Prop_obj@{o} X).
Proof using P.
  unshelve refine (@Build_SetoidMorphism@{o o o}
    (carrier X) (is_setoid X) Prop (is_setoid Powerset_Prop_truth@{o})
    (fun x => ∀ s, S s → perp P s x) _).
  intros x y Hxy; split; intros H s Hs.
  - refine (perp_respects P s s x y _ Hxy (H s Hs)); reflexivity.
  - refine (perp_respects P s s y x _ _ (H s Hs));
      [ reflexivity | now symmetry ].
Defined.

(*
 Membership, on the nose.  An equation between [Prop]s, that is between
 OBJECTS of the power set, not between morphisms. 

 --------
 成员资格，正中目标。一个关于 [Prop] 的等式，也就是关于幂集的对象的等式，而不是关于态射的等式。
*)
Example perp_set_mem (S : carrier (Powerset_Prop_obj@{o} X))
  (x : carrier X) : perp_set S x = (∀ s, S s → perp P s x) := eq_refl.

(*
 THE TRANSPOSITION.  Its whole content is a permutation of the two
 universal quantifiers followed by one appeal to [perp_sym]; supplied by
 [:=] with no tactic.  Note that the statement is symmetric in [S] and
 [T], so this ONE term serves both halves of Mac Lane's biconditional
 and both legs of every packaging below. 

 --------
 置换。其整体内容是两个全称量词的排列，随后调用一次 [perp_sym]；由 [:=] 提供，没有使用策略。注意，该语句在 [S] 和 [T] 中是对称的，因此这个单一项同时适用于 Mac Lane 的双条件的两半，以及下面每个包装的两条支路。
*)
Definition perp_transpose (S T : carrier (Powerset_Prop_obj@{o} X))
  (H : subset_le@{o} S (perp_set T)) : subset_le@{o} T (perp_set S) :=
  fun y Hy s Hs => perp_sym P y s (H s Hs y Hy).

(* Order-reversal, in the elementary form. The connection reads it at [op_rel], where it becomes the covariant field the donor record asks for. / 在基本形式下的顺序反转。连接在 [op_rel] 处读取它，在那里它变成捐赠记录所要求的协变场。 *)
Lemma perp_set_antitone (S T : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le@{o} S T → subset_le@{o} (perp_set T) (perp_set S).
Proof using P. intros H x Hx s Hs; exact (Hx s (H s Hs)). Qed.

(* Both operators of a Galois connection respect the carriers' own [≈]; here there is one operator, and order-reversal read both ways gives it. / 伽罗瓦连接的两个算子都尊重载体自身的 [≈]；这里有一个算子，双向读取的顺序反转都能得到它。 *)
Lemma perp_set_respects (S T : carrier (Powerset_Prop_obj@{o} X))
  (H : S ≈ T) : perp_set S ≈ perp_set T.
Proof using P.
  apply subset_le_antisym.
  - exact (perp_set_antitone T S (fun x Hx => proj2 (H x) Hx)).
  - exact (perp_set_antitone S T (fun x Hx => proj1 (H x) Hx)).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** (C) The Galois connection / **（C）伽罗瓦连接 *)

(*
 All six fields by name.  The second relation is the REVERSED inclusion,
 which is Mac Lane's [Q^op]: [L] and [R] are order-REVERSING maps, so
 the covariant record of #380 is inhabited only at the reversed order,
 exactly as Instance/Grp/Galois.v's connection is. 

 --------
 所有六个字段按名称列出。第二个关系是反向包含，即 Mac Lane 的 [Q^op] : [L] 和 [R] 是序列反转映射，因此 #380 的协变记录仅在反向顺序下有元素，正如 Instance/Grp/Galois.v 的连接所示。
*)
Definition perp_galois :
  GaloisConnection (@subset_le@{o} X) (op_rel (@subset_le@{o} X)) :=
  {| gal_l := perp_set
   ; gal_r := perp_set
   ; gal_mono_l := perp_set_antitone
   ; gal_mono_r := fun S T H => perp_set_antitone T S H
   ; gal_to   := fun S T H => perp_transpose T S H
   ; gal_from := fun S T H => perp_transpose S T H |}.

(* MAC LANE'S [L S = R S], as an equation between the two fields. / MAC LANE 的 [L S = R S]，作为两个域之间的一个方程。 *)
Example perp_galois_l_is_r :
  gal_l perp_galois = gal_r perp_galois := eq_refl.

Example perp_galois_l_is_perp_set :
  gal_l perp_galois = perp_set := eq_refl.

(* The two halves of the biconditional are the same function at swapped arguments -- so “if and only if” costs one term, not two. / 双条件句的两个部分在交换参数时是相同的函数——所以“当且仅当”只需一个项，而不是两个。 *)
Example perp_to_is_from_swapped (S T : carrier (Powerset_Prop_obj@{o} X))
  (H : subset_le@{o} T (perp_set S)) :
  gal_to perp_galois S T H = gal_from perp_galois T S H := eq_refl.

(* The two preorders the connection is read at. / 两个先序用于读取连接。 *)
Definition perp_PreOrder_l : PreOrder (@subset_le@{o} X) :=
  subset_le_preorder@{o} X.

Definition perp_PreOrder_r : PreOrder (op_rel (@subset_le@{o} X)) :=
  op_PreOrder (subset_le_preorder@{o} X).

(* ------------------------------------------------------------------------ *)
(* * ** (D) Mac Lane's display (2), at this connection / * ** (D) 麦克·莱恩在此连接处的展示 (2) *)

(*
 [S] is contained in its double complement.  This is #380's [gal_unit]
 applied; no argument is written here. 

 --------
 [S] 包含在它的双重补集内。这是 #380 的 [gal_unit] 应用；这里没有写任何论证。
*)
Definition perp_unit (S : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le@{o} S (perp_set (perp_set S)) :=
  gal_unit perp_galois perp_PreOrder_r S.

(*
 The counit, at the SAME type: reading [gal_counit] at the reversed
 order turns it into the very inequality [gal_unit] gives, and the two
 are the same term. 

 --------
 余单位，在相同类型：按相反顺序读取 [gal_counit] 会将其变成 [gal_unit] 所给出的不等式，而两者是相同的项。
*)
Definition perp_counit (S : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le@{o} S (perp_set (perp_set S)) :=
  gal_counit perp_galois perp_PreOrder_l S.

Example perp_unit_is_counit (S : carrier (Powerset_Prop_obj@{o} X)) :
  perp_unit S = perp_counit S := eq_refl.

(*
 The triple complement collapses.  In a preorder that is not a partial
 order the conclusion is mutual inclusion, which for these carriers IS
 the setoid's own [≈]: Instance/Grp/Galois.v converts.  Both halves
 are #381's section (A) applied. 

 --------
 三重补集崩溃。在不是偏序的预序中，结论是相互包含，对于这些载体来说，正是集合同构自身的 [≈] : Instance/Grp/Galois.v 转换。两半都是 #381 的部分 (A) 应用。
*)
Lemma perp_triple (S : carrier (Powerset_Prop_obj@{o} X)) :
  perp_set (perp_set (perp_set S)) ≈ perp_set S.
Proof using P.
  apply subset_le_antisym.
  - exact (gal_lrl_above perp_PreOrder_r perp_galois S).
  - exact (gal_lrl_below perp_PreOrder_l perp_galois S).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** (E) The closed elements / **（E）封闭元素 *)

(*
 One inclusion of [S ≈ S^⊥⊥] is free ([perp_unit]), so the predicate
 records only the direction that is not. 

 --------
 [S ≈ S^⊥⊥] 的一个包含是免费的（[perp_unit]），因此谓词只记录不是的方向。
*)
Definition ClosedPerp (S : carrier (Powerset_Prop_obj@{o} X)) : Prop :=
  subset_le@{o} (perp_set (perp_set S)) S.

(* Section (A)'s two predicates coincide here, since [gal_l] and [gal_r] are one map and the second order is the first reversed. / 这里，部分 (A) 的两个谓词重合，因为 [gal_l] 和 [gal_r] 是同一个映射，第二个顺序是第一个的反向。 *)
Example ClosedPerp_is_GalClosed_r (S : carrier (Powerset_Prop_obj@{o} X)) :
  ClosedPerp S = GalClosed_r perp_galois S := eq_refl.

Example ClosedPerp_is_GalClosed_l (S : carrier (Powerset_Prop_obj@{o} X)) :
  ClosedPerp S = GalClosed_l perp_galois S := eq_refl.

(* Every complement is closed. / 每个补集都是封闭的。 *)
Definition perp_set_closed (S : carrier (Powerset_Prop_obj@{o} X)) :
  ClosedPerp (perp_set S) :=
  gal_closed_r_image perp_PreOrder_l perp_galois S.

(*
 The characterisation: the closed subsets are EXACTLY the orthogonal
 complements.  Section (A) supplies the mutual-inclusion form and
 [subset_le_antisym] upgrades it to the carriers' own [≈]. 

 --------
 该表征：闭子集恰好是正交补。部分 (A) 提供了相互包含的形式，而 [subset_le_antisym] 将其升级为载体自身的 [≈]。
*)
Lemma closed_perp_iff (S : carrier (Powerset_Prop_obj@{o} X)) :
  ClosedPerp S ↔ ∃ T, perp_set T ≈ S.
Proof using P.
  split.
  - intro H.
    destruct (fst (gal_closed_r_iff perp_PreOrder_l perp_PreOrder_r
                     perp_galois S) H) as [T [H1 H2]].
    exists T; exact (subset_le_antisym H2 H1).
  - intros [T HT].
    refine (snd (gal_closed_r_iff perp_PreOrder_l perp_PreOrder_r
                   perp_galois S) _).
    exists T; exact (fun x Hx => proj2 (HT x) Hx,
                     fun x Hx => proj1 (HT x) Hx).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** (F) The two packagings / **（F）两种包装 *)

(*
 #380 applied: the functors and the adjunction are [:=] terms, and every
 coherence obligation of [Adjunction] is an equation between parallel
 arrows in a thin category, hence discharged uniformly there. 

 --------
 #380 应用：函子和伴随是 [:=] 项，并且 [Adjunction] 的每个相干性义务都是薄范畴中平行箭头之间的等式，因此在那里统一地被解决。
*)
Definition PerpFunctor : Subsets@{o u} X ⟶ Proset@{o u} perp_PreOrder_r :=
  GaloisFunctor_l perp_PreOrder_l perp_PreOrder_r perp_galois.

Definition PerpFunctor_r : Proset@{o u} perp_PreOrder_r ⟶ Subsets@{o u} X :=
  GaloisFunctor_r perp_PreOrder_l perp_PreOrder_r perp_galois.

Definition perp_adjunction : PerpFunctor ⊣ PerpFunctor_r :=
  GaloisAdjunction perp_PreOrder_l perp_PreOrder_r perp_galois.

Example PerpFunctor_obj (S : carrier (Powerset_Prop_obj@{o} X)) :
  fobj[PerpFunctor] S = perp_set S := eq_refl.

Example PerpFunctor_r_obj (S : carrier (Powerset_Prop_obj@{o} X)) :
  fobj[PerpFunctor_r] S = perp_set S := eq_refl.

(*
 Mac Lane's own typing.  Theorem 1 types the two maps as [L : P → Q^op]
 and [R : Q^op → P], and Adjunction/Right.v's [AdjointOnTheRight S T]
 -- for [S : A^op ⟶ X] and [T : X^op ⟶ A], with the hom-set isomorphism
 [A(a, T x) ≅ X(x, S a)] -- is exactly that shape.  With [P = Q] and
 [L = R] both slots are filled by ONE functor, so the pair is adjoint to
 itself on the right, which is the categorical reading of “LS = RS”.

 Prior art, measured, and the tree-wide list is complete: this is NOT the
 class's first inhabitant with the two slots equal.  Adjunction/Right.v
 carries three -- [Id_AdjointOnTheRight] (labelled DEGENERATE
 there, and its two slots are [Id[C^op]] and [Id[C]], which are not the
 same term), [Chain3_AdjointOnTheRight] (whose two functors
 differ) and [Powerset_AdjointOnTheRight] (at a coinciding pair);
 Structure/Monoidal/Dual.v's [dual_self_adjoint_on_the_right] is a
 fourth, also at a coinciding pair; and Instance/Grp/Galois.v's
 [group_action_AdjointOnTheRight] -- in a file this one REQUIRES -- is a
 fifth, whose slots [StabOp] and [FixedOp] differ.  So two of the five
 precede this one at a coinciding pair.  What is new here is a
 self-adjoint witness in a THIN category arising from a symmetric
 RELATION, and the observation that both legs of its hom-set isomorphism
 are one term. 

 --------
 麦克·莱恩自己的类型。定理 1 将两个映射标记为 [L : P → Q^op] 和 [R : Q^op → P]，而 Adjunction/Right.v 的 [AdjointOnTheRight S T] —— 对于 [S : A^op ⟶ X] 和 [T : X^op ⟶ A]，其同态集同构 [A(a, T x) ≅ X(x, S a)] —— 刚好就是那个形状。对于 [P = Q] 和 [L = R]，两个位置都由同一个函子填充，因此该对在右侧自伴，这是“LS = RS”的范畴论解读。现有技术、已测量，而且整个树的列表是完整的：这不是这个类中两个插槽相等的第一个实例。Adjunction/Right.v 包含三个——[Id_AdjointOnTheRight]（在那里被标记为退化，其两个插槽为 [Id[C^op]] 和 [Id[C]]，它们不是相同的项），[Chain3_AdjointOnTheRight]（其两个函子不同）以及 [Powerset_AdjointOnTheRight]（在一个重合对上）；Structure/Monoidal/Dual.v 的 [dual_self_adjoint_on_the_right] 是第四个，也是一个重合对上的；Instance/Grp/Galois.v 的 [group_action_AdjointOnTheRight] —— 在一个文件中此项是必需的 —— 是第五个，其插槽 [StabOp] 和 [FixedOp] 不同。因此，五个中的两个在一个重合对上先于此项。这里的新内容是在由对称关系产生的薄范畴中一个自伴见证，以及对其 Hom 集同构的两条边都是单一项的观察。
*)

#[local] Obligation Tactic := simpl; repeat intro; exact I.

Program Definition PerpOp :
  (Subsets@{o u} X)^op ⟶ Subsets@{o u} X := {|
  fobj := perp_set;
  fmap := fun S T f => perp_set_antitone T S f
|}.

Program Definition perp_AdjointOnTheRight :
  AdjointOnTheRight PerpOp PerpOp := {|
  aor := fun S T =>
    {| to   := {| morphism := fun h => perp_transpose S T h |}
     ; from := {| morphism := fun h => perp_transpose T S h |} |}
|}.

Example PerpOp_obj (S : carrier (Powerset_Prop_obj@{o} X)) :
  fobj[PerpOp] S = perp_set S := eq_refl.

(*
 Both legs of the hom-set isomorphism are [perp_transpose], at swapped
 indices.  Off the diagonal the two do not share a type, so this is the
 sharpest form the statement takes; compare
 Structure/Monoidal/Dual.v's [aor_to_is_from_swapped]. 

 --------
 同态集同构的两条边都是 [perp_transpose]，只是索引交换了。在对角线之外，两者不共享类型，因此这是该陈述所能达到的最精确形式；参见 Structure/Monoidal/Dual.v 的 [aor_to_is_from_swapped]。
*)
Example perp_aor_to (S T : carrier (Powerset_Prop_obj@{o} X))
  (h : subset_le@{o} S (perp_set T)) :
  @to Sets _ _ (@aor _ _ _ _ perp_AdjointOnTheRight S T) h
    = perp_transpose S T h := eq_refl.

Example perp_aor_from (S T : carrier (Powerset_Prop_obj@{o} X))
  (h : subset_le@{o} T (perp_set S)) :
  @from Sets _ _ (@aor _ _ _ _ perp_AdjointOnTheRight S T) h
    = perp_transpose T S h := eq_refl.

End Perp.

Arguments perp_set {X} P S.
Arguments ClosedPerp {X} P S.

(* ------------------------------------------------------------------------ *)
(* * ** (G) A witness: ℤ² with the dot product / * **（G）一个见证者：ℤ² 与点积 *)

(*
 The setoid of integer pairs, at ONE universe.  [eq_Setoid]
 (Lib/Setoid.v) is polymorphic in exactly the level [Subsets] needs,
 so [≈] here is Leibniz equality and every respectfulness obligation
 below is a substitution. 

 --------
 整数对的集合体，在一个宇宙中。[eq_Setoid] (Lib/Setoid.v) 的多态正好符合 [Subsets] 所需的级别，因此这里的 [≈] 是莱布尼茨等式，下面的每个尊重性义务都是一个替换。
*)
Definition zz_setoid@{wo} : SetoidObject@{wo wo} :=
  {| carrier := (Z * Z)%type ; is_setoid := eq_Setoid@{wo} (Z * Z)%type |}.

(* The ordinary dot product, and the orthogonality relation it induces. / 普通的点积，以及它所引起的正交关系。 *)
Definition zdot (p q : Z * Z) : Prop :=
  (fst p * fst q + snd p * snd q = 0)%Z.

Definition ZZPerp@{wo} : PerpRel@{wo} zz_setoid@{wo}.
Proof.
  unshelve refine (@Build_PerpRel@{wo} zz_setoid@{wo} zdot _ _).
  - intros x y H; unfold zdot in *.
    rewrite (Z.mul_comm (fst y) (fst x)), (Z.mul_comm (snd y) (snd x));
      exact H.
  - intros x x' y y' Hx Hy H; simpl in Hx, Hy; subst; exact H.
Defined.

Example zz_perp_is_dot : perp ZZPerp = zdot := eq_refl.

(* Subsets of ℤ². Respectfulness is a substitution, [≈] being [eq]. / ℤ² 的子集。尊重性是一种替换，[≈] 变为 [eq]。 *)
Definition zz_sub@{wo} (p : Z * Z → Prop) :
  carrier (Powerset_Prop_obj@{wo} zz_setoid@{wo}).
Proof.
  unshelve refine (@Build_SetoidMorphism@{wo wo wo}
    (Z * Z)%type (is_setoid zz_setoid@{wo})
    Prop (is_setoid Powerset_Prop_truth@{wo}) p _).
  intros x y Hxy; simpl in Hxy; subst; split; exact (fun h => h).
Defined.

Definition zz_e1@{wo} : carrier (Powerset_Prop_obj@{wo} zz_setoid@{wo}) :=
  zz_sub@{wo} (fun v => v = (1%Z, 0%Z)).

Definition zz_yaxis@{wo} : carrier (Powerset_Prop_obj@{wo} zz_setoid@{wo}) :=
  zz_sub@{wo} (fun v => fst v = 0%Z).

Definition zz_xaxis@{wo} : carrier (Powerset_Prop_obj@{wo} zz_setoid@{wo}) :=
  zz_sub@{wo} (fun v => snd v = 0%Z).

(* THE COMPLEMENT OF THE SINGLETON {(1,0)} IS THE SECOND AXIS. Both inclusions are one instantiation and one arithmetic step. / 单元素集合 {(1,0)} 的补集是第二坐标轴。两者的包含都是一次实例化和一次算术步骤。 *)
Lemma zz_perp_e1_is_yaxis : perp_set ZZPerp zz_e1 ≈ zz_yaxis.
Proof.
  apply subset_le_antisym.
  - intros x Hx; change (fst x = 0%Z).
    specialize (Hx (1%Z, 0%Z) eq_refl).
    change ((1 * fst x + 0 * snd x)%Z = 0%Z) in Hx; lia.
  - intros x Hx s Hs; change (fst x = 0%Z) in Hx.
    change (s = (1%Z, 0%Z)) in Hs; subst s.
    change ((1 * fst x + 0 * snd x)%Z = 0%Z); lia.
Qed.

(* Two named points, one in the complement and one out of it. / 两个有名字的点，一个在补集中，一个不在补集中。 *)
Example zz_perp_e1_contains : perp_set ZZPerp zz_e1 (0%Z, 5%Z).
Proof.
  intros s Hs; change (s = (1%Z, 0%Z)) in Hs; subst s.
  change ((1 * 0 + 0 * 5)%Z = 0%Z); reflexivity.
Qed.

Example zz_perp_e1_excludes :
  perp_set ZZPerp zz_e1 (2%Z, 0%Z) → False.
Proof.
  intro H; specialize (H (1%Z, 0%Z) eq_refl).
  change ((1 * 2 + 0 * 0)%Z = 0%Z) in H; lia.
Qed.

(*
 NON-DEGENERACY: a point is not orthogonal to itself, so the relation is
 not the total one and the connection is not the trivial one.  This is
 the statement the two-element field would refute. 

 --------
 非退化性：一个点不与自身正交，所以该关系不是全关系，连接也不是平凡连接。这是二元素域会否定的陈述。
*)
Example zz_e1_not_self_perp :
  perp_set ZZPerp zz_e1 (1%Z, 0%Z) → False.
Proof.
  intro H; specialize (H (1%Z, 0%Z) eq_refl).
  change ((1 * 1 + 0 * 0)%Z = 0%Z) in H; lia.
Qed.

(* THE SINGLETON IS NOT CLOSED: its double complement is the first axis, which contains [(2,0)]. / 单例未封闭：它的双重补集是第一轴，包含 [(2,0)]。 *)
Lemma zz_double_perp_e1_has_20 :
  perp_set ZZPerp (perp_set ZZPerp zz_e1) (2%Z, 0%Z).
Proof.
  intros s Hs.
  assert (fst s = 0%Z) as Hfs
    by (exact (proj1 (zz_perp_e1_is_yaxis s) Hs)).
  change ((fst s * 2 + snd s * 0)%Z = 0%Z); rewrite Hfs; lia.
Qed.

Theorem zz_e1_not_ClosedPerp : ClosedPerp ZZPerp zz_e1 → False.
Proof.
  intro H; pose proof (H (2%Z, 0%Z) zz_double_perp_e1_has_20) as Hin.
  change ((2%Z, 0%Z) = (1%Z, 0%Z)) in Hin.
  injection Hin; intros; lia.
Qed.

(*
 THE AXIS IS CLOSED, and the proof exercises the general
 characterisation rather than recomputing: it is a complement, and every
 complement is closed. 

 --------
 轴是闭合的，并且证明使用了一般的刻画而不是重新计算：它是一个补集，而每个补集都是闭合的。
*)
Theorem zz_yaxis_ClosedPerp : ClosedPerp ZZPerp zz_yaxis.
Proof.
  refine (snd (closed_perp_iff ZZPerp zz_yaxis) _).
  exists zz_e1; exact zz_perp_e1_is_yaxis.
Qed.

(* The complement of the second axis is the first, which pins the double complement of the singleton exactly. / 第二个轴的补轴是第一个轴，它精确地固定了单元素集合的双重补集。 *)
Lemma zz_perp_yaxis_is_xaxis : perp_set ZZPerp zz_yaxis ≈ zz_xaxis.
Proof.
  apply subset_le_antisym.
  - intros x Hx; change (snd x = 0%Z).
    specialize (Hx (0%Z, 1%Z) eq_refl).
    change ((0 * fst x + 1 * snd x)%Z = 0%Z) in Hx; lia.
  - intros x Hx s Hs; change (snd x = 0%Z) in Hx.
    change (fst s = 0%Z) in Hs.
    change ((fst s * fst x + snd s * snd x)%Z = 0%Z).
    rewrite Hs, Hx; lia.
Qed.

(* The two axes are distinct subsets, so the witness is not degenerate on the axis that matters: the complement moves. / 这两个轴是不同的子集，因此证人在重要的轴上不是退化的：补集在移动。 *)
Example zz_axes_differ : zz_yaxis ≈ zz_xaxis → False.
Proof.
  intro H; pose proof (proj1 (H (0%Z, 1%Z)) eq_refl) as Hin.
  change (1%Z = 0%Z) in Hin; lia.
Qed.
