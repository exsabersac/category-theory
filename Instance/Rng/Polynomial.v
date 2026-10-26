Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Algebras.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * * The polynomial ring K[x] as a universal arrow

   Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
   GTM 5, §III.1, printed pp. 56 and 59 — the roster of free
   constructions as universal arrows (maclane:III.1:remark2) and
   Exercise 7, which asks for K[x] with the insertion of x as a
   universal construction (maclane:III.1:ex7)
   Book: Riehl, “Category Theory in Context”, 2nd ed., §2.1
   Example 2.1.5(v), printed p. 56 — the forgetful functor from
   rings to sets is represented by ℤ[x] (riehl:2.1:example5)
   Book: Riehl, ibid., §2.3 Example 2.3.4, printed p. 68 — the same in
   element form, with the indeterminate as the universal element
   (riehl:2.3:example4)
   nLab:      https://ncatlab.org/nlab/show/polynomial+ring
   nLab:      https://ncatlab.org/nlab/show/free+functor
   nLab:      https://ncatlab.org/nlab/show/universal+morphism
   Wikipedia: https://en.wikipedia.org/wiki/Polynomial_ring

   WHY THE INDETERMINATE IS A UNIVERSAL PROPERTY.  “Let x be an
   indeterminate” is the oldest piece of mathematical hand-waving that
   category theory turned into a definition.  What a nineteenth-century
   algebraist meant by it was operational: x is a symbol one may
   calculate with, subject to no relation beyond the ring laws, and
   which may afterwards be REPLACED by any element of any ring
   containing the coefficients.  The replacement clause is the whole
   content, and it is a universal property in disguise — the pair
   (K[x], x) is universal among rings under K equipped with a chosen
   element, so that specifying a homomorphism out of K[x] is the same
   thing as specifying where x goes.  The substitution homomorphism that
   every algebra course introduces by formula, p ↦ p(a), is then not a
   construction at all but THE mediating arrow of that universal
   property, and its existence and uniqueness are one statement rather
   than two.  Mac Lane makes the point by listing the polynomial algebra
   alongside the free monoid, the free group and the free module in the
   §III.1 roster, and setting Exercise 7 to check that it belongs there.

   The reading has three faces, and all three are formalized below
   because they are what the three catalogued sources each ask for.  Mac
   Lane's is the universal arrow: (K[x], x) is initial among K-algebras
   with a chosen element.  Awodey's (§9.3, Instance/Rng/Pointed.v) is
   the adjunction: “adjoin an indeterminate” is left adjoint to
   forgetting a distinguished element, and the transposition IS
   evaluation.  Riehl's is representability: the underlying-set functor
   of rings is naturally isomorphic to Rng(ℤ[x], −), the isomorphism
   being “evaluate at x”, and x itself is the universal element.  The
   three are interderivable through Theory/Universal/Element.v's
   subsumption theorem, and the passages are taken here rather than
   re-proved.

   MAC LANE'S ROSTER, COMPLETE.  The §III.1 examples of free
   constructions as universal arrows — as issue #309 enumerates them —
   are now all in tree, and this file is the last of the five:

   - free category on a graph — [UniversalArrowQuiverCat]
   (Construction/Free/Quiver.v) with [FreeForgetfulAdjunction]
   ;
   - free monoid — [free_monoid_universal_arrow]
   (Instance/Coq/Monoid/Free.v) with [free_monoid_adjunction]
   ;
   - free group — [free_group_universal_arrow]
   (Instance/Grp/Free.v) with [free_group_adjunction];
   - free R-module — [free_module_universal_arrow]
   (Instance/Mod/Free.v) with [free_module_adjunction],
   and the vector-space case in Instance/Vect/Free.v;
   - polynomial algebra — this file.

   A CORRECTION TO THE ISSUE'S PRIOR ART, recorded here because a
   header is where a reader looks.  Issue #309 states that “the free
   R-module and the polynomial algebra have no in-tree counterpart and
   no host categories”, and its Riehl §4.1 section reports as verified
   that “rg -nw 'Ring' returns 0 hits, so there is no base ring, no
   module category, and no free module”.  Both are false as of this
   writing: Instance/Rng.v is the category of unital rings,
   Instance/Mod.v the category of R-modules, and Instance/Mod/Free.v
   the free module with exactly the universal arrow and adjunction the
   issue asks for.  Only the polynomial half was genuinely absent, and
   only that half is built here.  A third stale claim is worth naming
   for the same reason: the category of commutative K-algebras was
   ALSO already in tree, as Instance/Rng/Algebras.v's [KAlg], so
   “rings under K” needed no construction and Mac Lane's Exercise 7
   lands there directly.

   HOW K[x] IS PRESENTED, AND WHAT THAT COSTS.  The construction is by
   generators and relations, in the style of Instance/Ab/Tensor.v,
   Instance/Sets/Coend.v and Instance/Mod/Free.v: [PTerm] is a plain
   inductive of formal expressions built from constants, the
   indeterminate, sum, negation and product, and [pt_eq] is an
   inductive relation closing under exactly the commutative-ring laws,
   congruence for each former, saturation under K's own [≈], the two
   clauses making the constant inclusion a homomorphism, and symmetry
   and transitivity.  Reflexivity is derived ([pt_refl]), keeping the
   relation's induction principle one case shorter wherever it is
   consumed.  As in Instance/Ab/Tensor.v, [pt_Setoid] is not registered
   as a typeclass instance; the [≈] of [PolyRing K] IS [pt_eq]
   definitionally, so the ring-level lemmas of Theory/Algebra/Rig.v
   apply to it unchanged.

   The alternative presentation — a polynomial as a finite list of
   coefficients, with convolution for the product — was considered and
   not taken, and the reason is a design judgment rather than a
   measurement: it would buy normal forms, degree and coefficient
   extraction, at the price of proving associativity and commutativity
   of convolution, which are triple-sum reindexing arguments, and none
   of what it buys is consumed by the universal property.  What is
   therefore NOT available here is
   any notion of degree, any leading coefficient, and any decision
   procedure for equality in K[x].  What IS available, and is what a
   reader of §III.1 wants, is that the construction does not collapse:
   [poly_const_injective] proves K ↪ K[x] for every commutative K, and
   [poly_x_not_constant] proves the indeterminate is not any constant
   whenever 1 ≉ 0 in K — both by evaluating in K itself, so neither
   needs a normal form.

   THE STANDING COMMUTATIVITY ASSUMPTION, and where it bites.  [PolyRing]
   is defined for an ARBITRARY [RingObject] K, because nothing in the
   construction needs more; but [pe_mul_comm] is a constructor, and with
   [pe_const_mul] it forces const(ab) ≈ const(ba) for all a, b in K.  So
   over a non-commutative K the constant inclusion is not injective and
   [PolyRing K] is not the polynomial ring over K.  What that quotient
   IS, exactly — whether the kernel of the constant inclusion is
   precisely the commutator ideal, making [PolyRing K] the polynomial
   ring over K's largest commutative quotient — is NOT proved here and
   is not claimed; the forcing direction is immediate from the two
   constructors and the converse would need a normal form.
   Commutativity of K is load-bearing in two distinct places, not one:
   [phi_image_comm] spends it so that [peval] respects the
   [pe_mul_comm] constructor, which is what makes the fold well defined
   at all, and [poly_const_injective] spends it again for
   non-degeneracy.  It is nowhere decorative.
   Every universal-property statement below carries it.

   STRENGTHS, MEASURED, and the two halves of the extension differ.

   - [eq_refl]: evaluation restricts to the structure map on constants
   and sends the indeterminate to the chosen element
   ([poly_extend_const], [poly_extend_x]); preservation of ADDITION
   and of MULTIPLICATION are clauses of the fixpoint and close by
   [reflexivity]; the universal element of [Rng_Forget] IS the
   indeterminate ([zpoly_universal_elem_is_x]); the mediating
   homomorphism sends it to the chosen element
   ([zpoly_mediator_at_x]); and evaluation COMPUTES on closed input
   over ℤ ([zpoly_eval_at_three], and two more).
   - `≈` only: preservation of ZERO and of ONE.  The zero of K[x] is
   [pt_const (rig_zero K)], so the fold returns the image of K's
   zero and reaching the target's zero is the structure map's own
   preservation law.  This is measured, not assumed: the two
   obligations are discharged by [rig_map_zero] and [rig_map_one]
   and the other two by [reflexivity].
   - `≈` only, unavoidably: the transposes obtained from
   [ump_universal_arrows], which is [Qed]-opaque and does not
   compute.  Instance/Rng/Pointed.v records the same seam for the
   adjunction's backward transpose, as Instance/Mod/Free.v does for
   the counit of the free-module adjunction.

   WHAT IS DELIVERED.

   - [PolyRing K] for any [RingObject] K, with [poly_const],
   [poly_x] and [poly_comm];
   - [poly_extend] and [poly_extend_unique]: the substitution
   homomorphism and its uniqueness, over a hypothesis pack (K
   commutative, and the chosen element commuting with the image of
   the structure map) whose SECOND half is proved NECESSARY by
   [poly_hom_value_central] -- that lemma says nothing about K's
   own commutativity, and what a hom out of K[x] actually forces on
   the coefficients is commutativity of the IMAGE of the structure
   map, which [Kcomm] implies and which does not imply [Kcomm];
   - Mac Lane's Exercise 7: [poly_universal_element], a universal
   element at [PolyAlg K] of [KAlg_Forget], the underlying-set
   functor of Instance/Rng/Algebras.v's category [KAlg] of
   commutative K-algebras — that category is Algebras.v's, the
   functor is this file's — with the natural isomorphism
   [poly_representation], the class inhabitant [poly_representable]
   and both of Theory/Universal/Arrow.v's universal-arrow encodings;
   - ℤ[x] as the free unital ring on one generator in ALL of [Rng],
   not merely in [CRng]: [zring_central] shows the integers are
   central in every unital ring, which discharges the commutation
   hypothesis for an arbitrary target, and [zpoly_universal_element],
   [zpoly_representation] and [zpoly_representable] are Riehl's two
   examples;
   - [rng_monic_injective] and [rng_monic_iff_injective]:
   monomorphisms of rings are injective, which is the result
   Instance/Rng.v deferred pending the polynomial ring ℤ[x]
   (paraphrased -- that file's wording is “the polynomial ring
   ℤ[x], which does not exist in-tree”);
   - the non-degeneracy results above, and computing witnesses.

   WHAT IS NOT DELIVERED.  No degree, no normal form, no coefficient
   uniqueness, and hence no decision procedure for equality in K[x] and
   no division algorithm.  No several-indeterminate polynomial ring
   (K[x][y] is constructible by iterating, but is not identified with
   a two-variable ring here).  No proof that K[x] is an integral domain
   when K is, and so no connection to Instance/Rng/Frac.v's [IntDom].
   No claim that [PolyRing] is functorial in K as a stated functor —
   that content arrives as the [fmap] of the left adjoint in
   Instance/Rng/Pointed.v. 

   --------
   * * 多项式环 K [x] 作为一个通用箭头书籍：Mac Lane，《为工作中的数学家准备的范畴论》，第2版，GTM 5，第III.1节，印刷页56和59——作为泛箭的自由构造清单（maclane:III.1:remark2）以及习题7，要求插入x作为泛构造的K [x]（maclane:III.1:ex7）
   书籍：Riehl，《情境中的范畴论》，第2版，第2.1节，第2.1.5(v)例，印刷页56——从环到集合的遗忘函子由ℤ [x]表示（riehl:2.1:example5）
   书籍：Riehl，同上，第2.3节，第2.3.4例，印刷页68——以元素形式表示相同内容，以不定元作为泛元素（riehl:2.3:example4）
   nLab：https://ncatlab.org/nlab/show/polynomial+ring
   nLab：https://ncatlab.org/nlab/show/free+functor
   nLab：https://ncatlab.org/nlab/show/universal+morphism
   维基百科：https://en.wikipedia.org/wiki/Polynomial_ring为什么不定元是一个泛性质。“设 x 为一个不定元”是数学中最古老的一段含糊说法，而范畴论把它变成了一个定义。十九世纪的代数学家对它的理解是操作性的：x 是一个可以计算的符号，除了环的运算法则之外不受任何约束，并且之后可以被替换为任意包含系数的环中的任意元素。替换条款就是全部内容，它实际上是一个伪装的泛性质——(K[x], x) 对于带有选定元素的 K 下的环是泛的，因此指定一个从 K[x] 出发的同态与指定 x 被映射到何处是同样的意思。每一门代数课程通过公式 p ↦ p(a) 引入的代换同态，并不是一种构造，而是那个泛性质的中介箭头，它的存在性和唯一性是一个陈述，而不是两个。Mac Lane 在 §III.1 的列表中，将多项式代数与自由幺半群、自由群和自由模并列，并将练习7设置为检查它是否属于其中。该读法有三种方式，下面对三种方式进行了形式化，因为它们正是三个已编目来源各自要求的。Mac Lane 的方式是通用箭头：(K [x] , x) 在带有选定元素的 K-代数中是初始的。Awodey（§9.3, Instance/Rng/Pointed.v）是伴随：“添加一个未定元” 是左伴随于忘记一个特定元素，而转置即是求值。Riehl 的方式是可表示性：环的底层集合函子自然同构于 Rng(ℤ [x] , −)，同构映射为“在 x 上求值”，而 x 本身是通用元素。三者可以通过 Theory/Universal/Element.v 的蕴含定理相互推导，这里采用了这些传递方式，而没有重新证明。麦克莱恩的名单，完整。§III.1 中作为普遍箭头的自由构造示例——正如第 #309 期列举的——现在都在 tree 中，这个文件是五个文件中的最后一个：

   - 图上的自由范畴 — [UniversalArrowQuiverCat] (Construction/Free/Quiver.v) 和 [FreeForgetfulAdjunction]；
   - 自由幺半群 — [free_monoid_universal_arrow] (Instance/Coq/Monoid/Free.v) 和 [free_monoid_adjunction]；
   - 自由群 — [free_group_universal_arrow] (Instance/Grp/Free.v) 和 [free_group_adjunction]；
   - 自由 R-模 — [free_module_universal_arrow] (Instance/Mod/Free.v) 和 [free_module_adjunction]，以及 Instance/Vect/Free.v 中的向量空间情况；
   - 多项式代数 — 这个文件。对该问题现有技术的更正，这里记录是因为读者会查看标题。问题 #309 指出“自由 R-模和多项式代数在树内没有对应物，也没有宿主范畴”，其 Riehl §4.1 节报告已验证“rg -nw 'Ring' 返回 0 个命中，因此不存在基础环、模范畴，也不存在自由模”。截至本文撰写时，这两者都是错误的：Instance/Rng.v 是幺环范畴，Instance/Mod.v 是 R-模范畴，Instance/Mod/Free.v 是具有完全通用箭头和附属问题所要求的伴随的自由模。只有多项式部分确实缺失，而只有那部分是在此处构建的。第三个陈旧的说法值得提及，原因相同：交换 K-代数的类别也已经在树中，作为 Instance/Rng/Algebras.v 的 [KAlg]，因此“在 K 下的环”不需要构造，Mac Lane 的练习 7 可以直接落在那里。[x] 的表示方式以及相关成本。其构造方法是通过生成元和关系，类似于 Instance/Ab/Tensor.v、Instance/Sets/Coend.v 和 Instance/Mod/Free.v 的风格：[PTerm] 是由常数、不定项、和、取反与乘积构成的形式表达式的普通归纳类型；[pt_eq] 是一个归纳关系，恰好在交换环律、每个前者的一致性、自身的 [≈] 下闭合，这两条条款使常数包含成为同态，并且具有对称性和传递性。自反性是推导出的（[pt_refl]），在每次使用该归纳原理时，使关系的归纳原则少一条情况。正如在 Instance/Ab/Tensor.v 中，[pt_Setoid] 没有被注册为类型类实例；[PolyRing K] 的 [≈] 在定义上就是 [pt_eq]，因此 Theory/Algebra/Rig.v 的环级引理同样适用于它。另一种表示方法——将多项式表示为有限系数列表，并使用卷积进行乘法——曾被考虑过但未采用，原因是设计判断而非测量：它可以提供正规形式、次数和系数提取，但代价是需要证明卷积的结合律和交换律，这涉及三重求和重索引的论证，而且它带来的功能在通用性质中并未被使用。因此，此处不可用的是任何次数的概念、任何首项系数，以及在 K [x] 中判断相等的任何决策程序。可用的，而且是§III.1的读者所希望的，是构造不会塌陷：[poly_const_injective]证明了对每一个交换的K都有K ↪ K [x]，并且[poly_x_not_constant]证明了只要在K中1 ≉ 0，不定元就不是任何常数——两者都是通过在K本身中求值，因此都不需要标准形。固定交换性假设，以及它的问题所在。[PolyRing] 为任意 [RingObject] 代数 K 定义，因为构造中没有更多的需求；但 [pe_mul_comm] 是一个构造子，并且与 [pe_const_mul] 一起，它强制 const(ab) ≈ const(ba) 对于 K 中的所有 a, b 成立。所以在非交换性 K 上，常数包含不是单射，并且 [PolyRing K] 不是 K 上的多项式环。具体这个商是什么——即常数包含的核是否恰好是交换子理想，使 [PolyRing K] 成为 K 最大交换商上的多项式环——在这里没有证明，也没有声称；从这两个构造子立即可以得到强制方向，而逆方向则需要一个规范形式。K 的交换性在两个不同的地方起承重作用，而不是一个地方：
   [phi_image_comm] 使用它，使得 [peval] 遵守
   [pe_mul_comm] 构造函数，这正是使折叠完全定义的原因，
   而 [poly_const_injective] 再次使用它以保证非退化。它在任何地方都不是装饰性的。下面的每个泛性质陈述都包含它。

   STRENGTHS、MEASURED 和扩展的两个部分是不同的。- [eq_refl]：评估限制在常数上的结构映射，并将不确定量发送到所选元素（[poly_extend_const]，[poly_extend_x]）；加法和乘法的保持是不动点的条款，并在[reflexivity]附近完成；[Rng_Forget]的通用元素是不确定量（[zpoly_universal_elem_is_x]）；中介同态将其发送到所选元素（[zpoly_mediator_at_x]）；并且评估在ℤ上的封闭输入上计算（[zpoly_eval_at_three]，以及另外两个）。- 仅限`≈`：零和一的保持。K [x] 的零是[pt_const (rig_zero K)]，因此fold返回K的零的像，并且到达目标零是结构映射自身的保持定律。这是测量得到的，而非假设的：两个义务由 [rig_map_zero] 和 [rig_map_one] 履行，另两个由 [reflexivity] 履行。- 只有 `≈`，不可避免：从 [ump_universal_arrows] 获得的转置，它是 [Qed]-不透明且不计算。Instance/Rng/Pointed.v 记录了同样的缝隙，用于伴随的向后转置，正如 Instance/Mod/Free.v 对自由模伴随的余单元所做的那样。

   交付的内容是什么。- 对于任意的  [RingObject]  K，[PolyRing K]，其中有 [poly_const]、[poly_x] 和 [poly_comm]；
   - [poly_extend] 和 [poly_extend_unique]：代换同态及其唯一性，在假设包（K 可交换，并且选定元素与结构映射的像可交换）下，其后一半由 [poly_hom_value_central] 证明为必要——该引理并未涉及 K 自身的可交换性，而从 K 出发的 [x] 实际上对系数施加的要求是结构映射的像的可交换性，[Kcomm] 表明了这一点，但这并不意味着 [Kcomm]；
   - Mac Lane 的习题 7：[poly_universal_element]，[PolyAlg K] 处 [KAlg_Forget] 的一个通用元素，即 Instance/Rng/Algebras.v 类别 [KAlg] 的基础集合函子，该类别由可交换 K-代数组成作为——该类别属于 Algebras.v，函子属于这个文件——通过自然同构 [poly_representation]，该类的成员 [poly_representable]，以及 Theory/Universal/Arrow.v 的 universal-arrow 编码；
   - ℤ [x] 作为在 [Rng] 的所有元素上生成的自由幺环，而不仅仅是 [CRng]：[zring_central] 显示整数在每个幺环中都是中心元素，这消除了任意目标的交换假设，并且 [zpoly_universal_element]、[zpoly_representation] 和 [zpoly_representable] 是 Riehl 的两个例子；
   - [rng_monic_injective] 和 [rng_monic_iff_injective]：环的单态映射是单射，这是 Instance/Rng.v 延迟的结果，等待多项式环 ℤ [x]（意译——该文件的措辞是“多项式环 ℤ [x]，其中...不存在于树中“）;
   - 上述非简并性结果及计算见证。未提供内容。没有次数、没有标准形、没有系数唯一性，因此在 K [x] 中没有相等性判定程序，也没有除法算法。没有多不定元多项式环（K [x] [y] 可以通过迭代构造，但在这里并未与一个两变量环等同）。没有证明当 K 是整环时 K [x] 也是整环，因此与 Instance/Rng/Frac.v 的 [IntDom] 没有联系。没有声明 [PolyRing] 在 K 中作为已声明函子是函子性的——这个内容在 Instance/Rng/Pointed.v 中作为左伴随的 [fmap] 出现。
*)

(*
   * ** Two negation laws for multiplication

   Instance/Rng.v carries [rig_mul_neg_one] — the special case at
   [-1] — and Instance/Ab.v the additive facts; the two general forms
   below are used throughout and are proved the same way, by uniqueness
   of additive inverses. 

   --------
   * ** 乘法的两个否定律

   Instance/Rng.v 包含 [rig_mul_neg_one] — 特殊情况在
   [-1] — 并且 Instance/Ab.v 包含加法事实；下面的两个一般形式
   在各处使用，并通过加法逆元的唯一性以相同方式证明。
*)

Lemma rng_mul_neg_r (R : RingObject) (a b : carrier (rig_setoid R)) :
  rig_mul R a (ring_neg R b) ≈ ring_neg R (rig_mul R a b).
Proof.
  apply (ab_neg_unique (ring_ab R)); simpl.
  rewrite <- rig_distr_l.
  rewrite (ring_neg_l R b).
  apply rig_mul_zero_r.
Qed.

Lemma rng_mul_neg_l (R : RingObject) (a b : carrier (rig_setoid R)) :
  rig_mul R (ring_neg R a) b ≈ ring_neg R (rig_mul R a b).
Proof.
  apply (ab_neg_unique (ring_ab R)); simpl.
  rewrite <- rig_distr_r.
  rewrite (ring_neg_l R a).
  apply rig_mul_zero_l.
Qed.

Section Polynomial.

Context (K : RingObject).

(** ** Formal polynomial expressions / ** 正式多项式表达式 *)

Inductive PTerm : Type :=
  | pt_const : carrier (rig_setoid K) → PTerm
  | pt_x     : PTerm
  | pt_add   : PTerm → PTerm → PTerm
  | pt_neg   : PTerm → PTerm
  | pt_mul   : PTerm → PTerm → PTerm.

(*
 AN EARLIER REVISION of this inductive landed in [Type].  Since the PR
 “algebraic carriers are sets” (2026-09-17) it lands in [Prop], because
 [RigObject] now carries a [rig_prop : PropEquiv (is_setoid rig_setoid)]
 field and the [≈] of [PolyRing K] IS [pt_eq]: the relation must therefore
 BE a [Prop] for the field to be the identity pair of implications.  The
 cost is one elimination — [peval_respects] below can no longer induct
 straight into a [Type]-valued goal and goes through [pequiv_to] at the
 target ring — and nothing else in the file changes.
 Test/ProbeTermModelPropRng.v pins the refusal of the old script. 

 --------
 该归纳法的较早修订版本出现在 [Type]。由于 PR “代数载体是集合”（2026-09-17），它出现在 [Prop]，因为 [RigObject] 现在承载一个 [rig_prop : PropEquiv (is_setoid rig_setoid)] 域，而 [PolyRing K] 的 [≈] 是 [pt_eq]：因此该关系必须是 [Prop]，以便该域成为蕴含的恒等对。代价是一次消元——下面的 [peval_respects] 不再能直接归纳到 [Type] 值目标中，而是通过目标环上的 [pequiv_to] ——并且文件中没有其他变化。Test/ProbeTermModelPropRng.v 固定了旧脚本的拒绝。
*)
Inductive pt_eq : PTerm → PTerm → Prop :=
  (* congruence for each former, saturating under K's own [≈] / 每个前者的全等，在 K 自身的 [≈] 下饱和 *)
  | pe_const {a b} : a ≈ b → pt_eq (pt_const a) (pt_const b)
  | pe_add {s s' t t'} :
      pt_eq s s' → pt_eq t t' → pt_eq (pt_add s t) (pt_add s' t')
  | pe_neg {s s'} : pt_eq s s' → pt_eq (pt_neg s) (pt_neg s')
  | pe_mul {s s' t t'} :
      pt_eq s s' → pt_eq t t' → pt_eq (pt_mul s t) (pt_mul s' t')

  (* abelian group under addition / 加法下的阿贝尔群 *)
  | pe_add_assoc s t u :
      pt_eq (pt_add (pt_add s t) u) (pt_add s (pt_add t u))
  | pe_add_comm s t : pt_eq (pt_add s t) (pt_add t s)
  | pe_add_zero_l s : pt_eq (pt_add (pt_const (rig_zero K)) s) s
  | pe_add_neg_l s : pt_eq (pt_add (pt_neg s) s) (pt_const (rig_zero K))

  (* commutative monoid under multiplication / 在乘法下的交换幺半群 *)
  | pe_mul_assoc s t u :
      pt_eq (pt_mul (pt_mul s t) u) (pt_mul s (pt_mul t u))
  | pe_mul_comm s t : pt_eq (pt_mul s t) (pt_mul t s)
  | pe_mul_one_l s : pt_eq (pt_mul (pt_const (rig_one K)) s) s

  (* distributivity, on the left only: the right law is derived / 分配律，仅在左边：右边的公式是推导出来的 *)
  | pe_distr_l s t u :
      pt_eq (pt_mul s (pt_add t u)) (pt_add (pt_mul s t) (pt_mul s u))

  (* the coefficient inclusion is a homomorphism of rings / 系数包含是环的同态 *)
  | pe_const_add a b :
      pt_eq (pt_const (rig_add K a b)) (pt_add (pt_const a) (pt_const b))
  | pe_const_mul a b :
      pt_eq (pt_const (rig_mul K a b)) (pt_mul (pt_const a) (pt_const b))

  | pe_sym {s t} : pt_eq s t → pt_eq t s
  | pe_trans {s t u} : pt_eq s t → pt_eq t u → pt_eq s u.

Lemma pt_refl (s : PTerm) : pt_eq s s.
Proof.
  induction s.
  - exact (pe_const (reflexivity _)).
  - exact (pe_trans (pe_sym (pe_add_zero_l pt_x)) (pe_add_zero_l pt_x)).
  - exact (pe_add IHs1 IHs2).
  - exact (pe_neg IHs).
  - exact (pe_mul IHs1 IHs2).
Qed.

Lemma pt_eq_Equivalence : Equivalence pt_eq.
Proof.
  constructor.
  - exact pt_refl.
  - exact (fun s t => pe_sym).
  - exact (fun s t u => pe_trans).
Qed.

Definition pt_Setoid : Setoid PTerm := {|
  equiv        := pt_eq;
  setoid_equiv := pt_eq_Equivalence
|}.

(** ** Derived laws / ** 派生法律 *)

Let PZ : PTerm := pt_const (rig_zero K).
Let PO : PTerm := pt_const (rig_one K).

Lemma pe_add_zero_r (s : PTerm) : pt_eq (pt_add s PZ) s.
Proof.
  exact (pe_trans (pe_add_comm s PZ) (pe_add_zero_l s)).
Qed.

Lemma pe_add_neg_r (s : PTerm) : pt_eq (pt_add s (pt_neg s)) PZ.
Proof.
  exact (pe_trans (pe_add_comm s (pt_neg s)) (pe_add_neg_l s)).
Qed.

Lemma pe_mul_one_r (s : PTerm) : pt_eq (pt_mul s PO) s.
Proof.
  exact (pe_trans (pe_mul_comm s PO) (pe_mul_one_l s)).
Qed.

Lemma pe_distr_r (s t u : PTerm) :
  pt_eq (pt_mul (pt_add s t) u) (pt_add (pt_mul s u) (pt_mul t u)).
Proof.
  refine (pe_trans (pe_mul_comm (pt_add s t) u) _).
  refine (pe_trans (pe_distr_l u s t) _).
  exact (pe_add (pe_mul_comm u s) (pe_mul_comm u t)).
Qed.

(*
 Cancellation: adding the negative on the left is what makes the
 annihilation law below a theorem rather than a further constructor. 

 --------
 消去：在左边添加负号是使下面的湮灭律成为定理而不是进一步构造的原因。
*)
Lemma pe_add_cancel_l (s t u : PTerm) :
  pt_eq (pt_add s t) (pt_add s u) → pt_eq t u.
Proof.
  intro H.
  refine (pe_trans (pe_sym (pe_add_zero_l t)) _).
  refine (pe_trans (pe_add (pe_sym (pe_add_neg_l s)) (pt_refl t)) _).
  refine (pe_trans (pe_add_assoc (pt_neg s) s t) _).
  refine (pe_trans (pe_add (pt_refl (pt_neg s)) H) _).
  refine (pe_trans (pe_sym (pe_add_assoc (pt_neg s) s u)) _).
  refine (pe_trans (pe_add (pe_add_neg_l s) (pt_refl u)) _).
  exact (pe_add_zero_l u).
Qed.

Lemma pe_mul_zero_l (s : PTerm) : pt_eq (pt_mul PZ s) PZ.
Proof.
  (* 0·s ≈ (0+0)·s ≈ 0·s + 0·s, so 0·s ≈ 0 by cancellation. / 0·s ≈ (0+0)·s ≈ 0·s + 0·s，因此 0·s ≈ 0 通过消去法。 *)
  apply (pe_add_cancel_l (pt_mul PZ s)).
  refine (pe_trans (pe_sym (pe_distr_r PZ PZ s)) _).
  refine (pe_trans (pe_mul _ (pt_refl s)) (pe_sym (pe_add_zero_r (pt_mul PZ s)))).
  refine (pe_trans (pe_sym (pe_const_add (rig_zero K) (rig_zero K))) _).
  exact (pe_const (rig_add_zero_l K (rig_zero K))).
Qed.

Lemma pe_mul_zero_r (s : PTerm) : pt_eq (pt_mul s PZ) PZ.
Proof.
  exact (pe_trans (pe_mul_comm s PZ) (pe_mul_zero_l s)).
Qed.

(*
 The coefficient inclusion also carries negation, by uniqueness of
 additive inverses in the term ring. 

 --------
 系数的包含也带有否定性，这是由于项环中加法逆元的唯一性。
*)
Lemma pe_const_neg (a : carrier (rig_setoid K)) :
  pt_eq (pt_const (ring_neg K a)) (pt_neg (pt_const a)).
Proof.
  apply (pe_add_cancel_l (pt_const a)).
  refine (pe_trans _ (pe_sym (pe_add_neg_r (pt_const a)))).
  refine (pe_trans (pe_sym (pe_const_add a (ring_neg K a))) _).
  refine (pe_const _).
  refine (transitivity (rig_add_comm K a (ring_neg K a)) _).
  exact (ring_neg_l K a).
Qed.

(** ** The ring K[x] / ** 环 K [x] *)

Definition PolyRig : RigObject := {|
  rig_setoid := {| carrier := PTerm; is_setoid := pt_Setoid |};
  rig_zero := PZ;
  rig_add := pt_add;
  rig_one := PO;
  rig_mul := pt_mul;
  rig_add_respects := fun _ _ Hs _ _ Ht => pe_add Hs Ht;
  rig_mul_respects := fun _ _ Hs _ _ Ht => pe_mul Hs Ht;
  rig_add_assoc := pe_add_assoc;
  rig_add_comm := pe_add_comm;
  rig_add_zero_l := pe_add_zero_l;
  rig_mul_assoc := pe_mul_assoc;
  rig_mul_one_l := pe_mul_one_l;
  rig_mul_one_r := pe_mul_one_r;
  rig_distr_l := pe_distr_l;
  rig_distr_r := pe_distr_r;
  rig_mul_zero_l := pe_mul_zero_l;
  rig_mul_zero_r := pe_mul_zero_r;
  (*
 [pt_eq] IS a [Prop]-valued relation, so it is its own [Prop] mirror and
 both implications are the identity. 

 --------
 [pt_eq] 是一个 [Prop] 值的关系，因此它是其自身的 [Prop] 镜像，并且两个蕴涵都是恒等映射。
*)
  rig_prop := @PropEquiv_of_relation _ pt_Setoid pt_eq
                (fun _ _ h => h) (fun _ _ h => h)
|}.

Definition PolyRing : RingObject := {|
  ring_rig := PolyRig;
  ring_neg := pt_neg;
  ring_neg_respects := fun _ _ Hs => pe_neg Hs;
  ring_neg_l := pe_add_neg_l
|}.

Lemma poly_comm : ∀ a b : carrier (rig_setoid PolyRing),
  rig_mul PolyRing a b ≈ rig_mul PolyRing b a.
Proof. exact pe_mul_comm. Qed.

(* * ** The coefficient inclusion and the indeterminate / * ** 系数的包含与不定式 *)

Program Definition poly_const : K ~{Rng}~> PolyRing := {|
  rig_map := {| morphism := pt_const |}
|}.
Next Obligation. intros a b H; exact (pe_const H). Qed.
Next Obligation. simpl; exact (pt_refl PZ). Qed.
Next Obligation. intros a b; exact (pe_const_add a b). Qed.
Next Obligation. simpl; exact (pt_refl PO). Qed.
Next Obligation. intros a b; exact (pe_const_mul a b). Qed.

Definition poly_x : carrier (rig_setoid PolyRing) := pt_x.

End Polynomial.

Arguments PTerm {K}.
Arguments pt_const {K} a.
Arguments pt_x {K}.
Arguments pt_add {K} s t.
Arguments pt_neg {K} s.
Arguments pt_mul {K} s t.
Arguments pt_eq {K} s t.
Arguments pt_refl {K} s.
Arguments poly_x {K}.

(*
   * ** Evaluation: the universal property in element form

   Given a ring [S], a homomorphism [phi : K ~> S] and an element
   [s : S] commuting with the image of [phi], every formal polynomial
   has a value in [S].  The commutation hypothesis is exactly what makes
   the fold respect [pe_mul_comm]; over a commutative target it is free,
   and the ℤ[x] instance below discharges it from the centrality of the
   integers in every ring. 

   --------
   * ** 评估：元素形式的泛性质

   给定一个环 [S]，一个同态 [phi : K ~> S] 以及一个与 [phi] 的像交换的元素 [s : S]，每个形式多项式在 [S] 中都有一个值。交换假设正是使折叠尊重 [pe_mul_comm] 的原因；在交换目标上它是自由的，下面的 ℤ [x] 实例将其从整数在每个环中的中心性中释放出来。
*)

Section Evaluation.

Context (K : RingObject).
Context (S : RingObject).
Context (phi : K ~{Rng}~> S).
Context (s : carrier (rig_setoid S)).

(*
 [Kcomm] and [Hcs] are explicit hypotheses of the lemmas that consume
 them rather than section variables: the file inherits Lib.v's
 [Default Proof Using “Type”], under which a section variable absent
 from a lemma's STATEMENT is not available to its proof, and both of
 these are used only inside proofs. 

 --------
 [Kcomm] 和 [Hcs] 是使用它们的引理的显式假设，而不是节变量：该文件继承了 Lib.v 的 [Default Proof Using “Type”]，在其下，某个引理的陈述中缺失的节变量在其证明中不可用，并且这两者仅在证明内部使用。
*)
Notation Kcomm_hyp :=
  (∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a).
Notation Hcs_hyp :=
  (∀ a : carrier (rig_setoid K),
     rig_mul S s (rig_map phi a) ≈ rig_mul S (rig_map phi a) s).

Fixpoint peval (t : @PTerm K) : carrier (rig_setoid S) :=
  match t with
  | pt_const a => rig_map phi a
  | pt_x       => s
  | pt_add u v => rig_add S (peval u) (peval v)
  | pt_neg u   => ring_neg S (peval u)
  | pt_mul u v => rig_mul S (peval u) (peval v)
  end.

(*
   * *** The image of the evaluation is commutative

   Nothing below needs [S] itself to be commutative: what is needed is
   that any two values of [peval] commute, and that follows from the two
   hypotheses by an induction that never inspects [S] beyond its ring
   laws.  This is what lets ℤ[x] be free on one generator in the
   category of ALL unital rings, not only the commutative ones. 

   --------
   * *** 评估的图像是可交换的

   以下内容不需要 [S] 本身是可交换的：所需要的是 [peval] 的任意两个值是可交换的，而这可以通过一个归纳法从两个假设中推导出来，该归纳法从不检查 [S]，除了它的环律。这正是使 ℤ [x] 在所有有单位环的范畴中（不仅仅是可交换的环）在一个生成元上是自由的原因。
*)

(* An element commuting with every coefficient and with [s] commutes with every value. Five cases, one per former. / 一个与每个系数以及 [s] 对换的元素与每个值都对换。五种情况，每种对应一个前者。 *)
Lemma peval_comm_gen (a : carrier (rig_setoid S))
  (H1 : ∀ k, rig_mul S a (rig_map phi k) ≈ rig_mul S (rig_map phi k) a)
  (H2 : rig_mul S a s ≈ rig_mul S s a) (u : @PTerm K) :
  rig_mul S a (peval u) ≈ rig_mul S (peval u) a.
Proof.
  induction u as [ k | | u IHu v IHv | u IHu | u IHu v IHv ]; simpl.
  - exact (H1 k).
  - exact H2.
  - rewrite rig_distr_l, IHu, IHv; symmetry; apply rig_distr_r.
  - rewrite rng_mul_neg_r, IHu; symmetry; apply rng_mul_neg_l.
  - rewrite <- rig_mul_assoc, IHu, rig_mul_assoc, IHv.
    symmetry; apply rig_mul_assoc.
Qed.

(* The image of [phi] is commutative, because [K] is. / [phi] 的像是交换的，因为 [K] 是交换的。 *)
Lemma phi_image_comm (Kcomm : Kcomm_hyp) (k l : carrier (rig_setoid K)) :
  rig_mul S (rig_map phi k) (rig_map phi l)
    ≈ rig_mul S (rig_map phi l) (rig_map phi k).
Proof.
  rewrite <- !rig_map_mul.
  apply (proper_morphism (rig_map phi)), Kcomm.
Qed.

Lemma peval_comm (Kcomm : Kcomm_hyp) (Hcs : Hcs_hyp) (t u : @PTerm K) :
  rig_mul S (peval t) (peval u) ≈ rig_mul S (peval u) (peval t).
Proof.
  apply peval_comm_gen.
  - intro k.
    symmetry.
    exact (peval_comm_gen (rig_map phi k) (phi_image_comm Kcomm k)
             (symmetry (Hcs k)) t).
  - symmetry.
    exact (peval_comm_gen s Hcs (reflexivity _) t).
Qed.

(*
   * *** Evaluation respects the quotienting relation

   Sixteen cases, one per constructor of [pt_eq].  Four are congruence
   for a former, the first of them saturating under K's own [≈]; seven
   are ring laws of [S], three of those additionally spending a
   preservation law of [phi], because the zero and the one of K[x] are
   constants rather than formers of their own; two are [phi]'s
   preservation of sums and of products; one — commutativity of
   multiplication — is [peval_comm]; and the last two are the target
   setoid's symmetry and transitivity.

   AN EARLIER REVISION of this proof inducted on [pt_eq] straight into the
   [Type]-valued goal `≈`.  Since the PR “algebraic carriers are sets”
   (2026-09-17) [pt_eq] is a [Prop] inductive and eliminates only into
   [Prop], so the script opens with [apply pequiv_to] at the TARGET ring's
   own [rig_prop]: that puts the [Prop] goal [pequiv …] in front of the
   elimination, and each branch returns to `≈` with [pequiv_from].  The
   argument is unchanged case for case, no hypothesis is added (every
   [RigObject] carries the field), and the statement is the same.  The
   intro pattern is unchanged; the induction hypotheses are now
   [pequiv]-valued, so the three branches that consume one spend
   [pequiv_to] on it. 

   --------
   * *** 评估尊重商关系

   十六种情况，每个对应  [pt_eq] 的一个构造器。四种是前者的一致性，其中第一个在 K 自身的  [≈] 下饱和；七种是  [S] 的环律，其中三种额外使用了  [phi] 的保持律，因为 K 的零和一  [x] 是常量，而不是它们自身的构造器；两种是  [phi] 对和与积的保持；一种——乘法的交换性——是  [peval_comm]；最后两种是目标集合等价关系的对称性和传递性。该证明的早期修订直接在 [pt_eq] 上归纳到 [Type] 值的目标 `≈`。由于 PR “代数载体是集合”（2026-09-17） [pt_eq] 是一个 [Prop] 归纳类型，并且只可以消解到 [Prop]，因此脚本在 TARGET 环的 [rig_prop] 自身开头使用 [apply pequiv_to]：这将 [Prop] 目标 [pequiv …] 放在消解之前，每个分支返回到 `≈` 并带有 [pequiv_from]。论证逐个情况不变，没有添加假设（每个 [RigObject] 携带该域），声明也相同。引入模式不变；归纳假设现在是 [pequiv] 值，所以三个消耗一个的分支在上面使用 [pequiv_to]。
*)
Lemma peval_respects (Kcomm : Kcomm_hyp) (Hcs : Hcs_hyp) (t u : @PTerm K) :
  pt_eq t u → peval t ≈ peval u.
Proof.
  intro He.
  apply pequiv_to.
  induction He as
    [ a b Hab
    | t t' u u' _ IHt _ IHu
    | t t' _ IHt
    | t t' u u' _ IHt _ IHu
    | t u v | t u | t | t
    | t u v | t u | t
    | t u v
    | a b | a b
    | t u _ IHtu
    | t u v _ IHtu _ IHuv ]; simpl.
  - apply pequiv_from; exact (proper_morphism (rig_map phi) _ _ Hab).
  - apply pequiv_from.
    exact (rig_add_respects S _ _ (pequiv_to _ _ IHt)
                              _ _ (pequiv_to _ _ IHu)).
  - apply pequiv_from.
    exact (ring_neg_respects S _ _ (pequiv_to _ _ IHt)).
  - apply pequiv_from.
    exact (rig_mul_respects S _ _ (pequiv_to _ _ IHt)
                              _ _ (pequiv_to _ _ IHu)).
  - apply pequiv_from; exact (rig_add_assoc S _ _ _).
  - apply pequiv_from; exact (rig_add_comm S _ _).
  - apply pequiv_from; rewrite (rig_map_zero phi); apply rig_add_zero_l.
  - apply pequiv_from; rewrite (rig_map_zero phi); apply (ring_neg_l S).
  - apply pequiv_from; exact (rig_mul_assoc S _ _ _).
  - apply pequiv_from; exact (peval_comm Kcomm Hcs t u).
  - apply pequiv_from; rewrite (rig_map_one phi); apply rig_mul_one_l.
  - apply pequiv_from; exact (rig_distr_l S _ _ _).
  - apply pequiv_from; exact (rig_map_add phi a b).
  - apply pequiv_from; exact (rig_map_mul phi a b).
  - exact (symmetry IHtu).
  - exact (transitivity IHtu IHuv).
Qed.

(*
   * *** The extension, as a homomorphism of rings

   STRENGTH, MEASURED, and the two halves differ.  Preservation of
   ADDITION and of MULTIPLICATION close by [reflexivity]: those are
   clauses of the fixpoint.  Preservation of ZERO and of ONE does NOT —
   [rig_zero (PolyRing K)] is [pt_const (rig_zero K)], so the fold
   returns [phi (rig_zero K)], and reaching [rig_zero S] from there is
   [phi]'s own preservation law, an equation up to `≈`.  Only
   respectfulness has content beyond that. 

   --------
   * *** 作为环同态的扩展

   强度、测量，以及两个部分的不同。加法和乘法的保持在 [reflexivity] 附近：这些是不动点的条款。零和一的保持不成立——[rig_zero (PolyRing K)] 是 [pt_const (rig_zero K)]，所以 fold 返回 [phi (rig_zero K)]，从那里到达 [rig_zero S] 是 [phi] 自身的保持定律，一个到 `≈` 的方程。只有尊重性才具有超出这些的内容。
*)
Program Definition poly_extend (Kcomm : Kcomm_hyp) (Hcs : Hcs_hyp)
  : PolyRing K ~{Rng}~> S := {|
  rig_map := {| morphism := peval |}
|}.
Next Obligation.
  intros Kcomm Hcs t u He; exact (peval_respects Kcomm Hcs t u He).
Qed.
Next Obligation. intros Kcomm Hcs; simpl; exact (rig_map_zero phi). Qed.
Next Obligation. intros Kcomm Hcs t u; simpl; reflexivity. Qed.
Next Obligation. intros Kcomm Hcs; simpl; exact (rig_map_one phi). Qed.
Next Obligation. intros Kcomm Hcs t u; simpl; reflexivity. Qed.

(*
   * The extension restricts to [phi] along the coefficient inclusion and
   sends the indeterminate to [s] — both DEFINITIONALLY, the fixpoint's
   first two clauses being those two equations.  This is the
   convertibility exception: the equations are between elements of [S]'s
   carrier, not between morphisms. 

   --------
   * 该扩展沿着系数包含限制到 [phi]，并将未定元发送到 [s]——在定义上，固定点的前两个条款就是这两个方程。这是可转换性例外：这些方程是在 [S] 的承载元素之间，而不是在态射之间。
*)
Example poly_extend_const (Kcomm : Kcomm_hyp) (Hcs : Hcs_hyp)
  (a : carrier (rig_setoid K)) :
  rig_map (poly_extend Kcomm Hcs) (pt_const a) = rig_map phi a := eq_refl.

Example poly_extend_x (Kcomm : Kcomm_hyp) (Hcs : Hcs_hyp) :
  rig_map (poly_extend Kcomm Hcs) (@poly_x K) = s := eq_refl.

(*
   * *** Uniqueness

   Any ring homomorphism out of [K[x]] restricting to [phi] on constants
   and sending [x] to [s] IS the evaluation.  The induction has one case
   per former: the two base cases are the hypotheses, and the other
   three are the homomorphism laws of the competitor — preservation of
   sums, of negation (Rig.v's [RigHom_neg], a theorem rather than a
   field) and of products. 

   --------
   * *** 唯一性

   任何从  [K[x]  出发的环同态，如果在常数上限制为  [phi] ，并把  [x]  送到  [s] ，就是该取值映射。归纳法对每个前者有一个情况：两个基本情况是假设，另外三个是竞争者的同态定律——保持加法、保持取反（Rig.v 的  [RigHom_neg] ，是定理而非域）以及保持乘法。
*)
Lemma poly_extend_unique (g : PolyRing K ~{Rng}~> S)
  (Hconst : ∀ a, rig_map g (pt_const a) ≈ rig_map phi a)
  (Hx : rig_map g (@poly_x K) ≈ s) (t : @PTerm K) :
  rig_map g t ≈ peval t.
Proof.
  induction t as [ a | | t IHt u IHu | t IHt | t IHt u IHu ]; simpl.
  - exact (Hconst a).
  - exact Hx.
  - rewrite (rig_map_add g t u); exact (rig_add_respects S _ _ IHt _ _ IHu).
  - rewrite (RigHom_neg (PolyRing K) S g t).
    exact (ring_neg_respects S _ _ IHt).
  - rewrite (rig_map_mul g t u); exact (rig_mul_respects S _ _ IHt _ _ IHu).
Qed.

End Evaluation.

Arguments peval {K S} phi s t.
Arguments poly_extend {K S} phi s Kcomm Hcs.
Arguments poly_extend_unique {K S} phi s g Hconst Hx t.

(*
   * ** The integers are central in every ring

   The evaluation hypothesis [Hcs] is discharged for ℤ[x] by this
   lemma: an integer multiple of 1 commutes with everything, so a
   homomorphism out of ℤ[x] into an ARBITRARY unital ring is available,
   not only into a commutative one. 

   --------
   * ** 整数在每一个环中都是中心元

   对 ℤ 的评估假设 [Hcs] 被这个引理解决了：一个 1 的整数倍与所有元素交换，因此
   从 ℤ [x] 到任意含单位环的同态是可用的，而不仅仅是到交换环。
*)

Lemma rig_iter_central (S : RingObject) (n : nat)
  (b : carrier (rig_setoid S)) :
  rig_mul S (rig_iter S n) b ≈ rig_mul S b (rig_iter S n).
Proof.
  induction n as [ | n IH ]; simpl.
  - rewrite rig_mul_zero_l, rig_mul_zero_r; reflexivity.
  - rewrite rig_distr_r, rig_distr_l, IH.
    rewrite rig_mul_one_l, rig_mul_one_r; reflexivity.
Qed.

Lemma zring_central (S : RingObject) (z : Z) (b : carrier (rig_setoid S)) :
  rig_mul S (zring S z) b ≈ rig_mul S b (zring S z).
Proof.
  destruct z; simpl.
  - rewrite rig_mul_zero_l, rig_mul_zero_r; reflexivity.
  - apply rig_iter_central.
  - rewrite rng_mul_neg_l, rng_mul_neg_r, rig_iter_central; reflexivity.
Qed.

(* * * Mac Lane §III.1 Exercise 7: K[x] among K-algebras / * * Mac Lane §III.1 练习 7：K-代数中的 K [x] *)

Section KAlgebra.

Context (K : CRng).

(*
   * The polynomial ring, as a commutative K-algebra: the ring is
   [PolyRing], the commutativity is [poly_comm], and the structure map is
   the coefficient inclusion. 

   --------
   * 多项式环，作为交换 K-代数：该环是 [PolyRing]，交换性是 [poly_comm]，结构映射是系数包含。
*)
Definition PolyAlg : KAlgObject K := {|
  kalg_ring := PolyRing (`1 K);
  kalg_comm := poly_comm (`1 K);
  kalg_unit := poly_const (`1 K)
|}.

(** The underlying-set functor of the category of K-algebras. / K-代数范畴的底集合函子。 *)
Program Definition KAlg_Forget : KAlg K ⟶ Sets := {|
  fobj := fun A => rig_setoid (kalg_ring A);
  fmap := fun A B f => rig_map (`1 f)
|}.
Next Obligation. intros A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros A a; simpl; reflexivity. Qed.
Next Obligation. intros A B C f g a; simpl; reflexivity. Qed.

(** The K-algebra map evaluating at a chosen element of a K-algebra. / 在选定的 K-代数元素上进行求值的 K-代数映射。 *)
Definition kalg_eval (A : KAlgObject K) (a : carrier (rig_setoid (kalg_ring A)))
  : PolyAlg ~{KAlg K}~> A.
Proof.
  unshelve eexists.
  - refine (poly_extend (kalg_unit A) a (`2 K) _).
    intro c; exact (kalg_comm A a (rig_map (kalg_unit A) c)).
  - intro c; simpl; reflexivity.
Defined.

(*
   * Mac Lane's Exercise 7, in element form: the pair ⟨K[x], x⟩ is
   universal among K-algebras with a chosen element. 

   --------
   * Mac Lane 的习题 7，以元素形式表示：对 ⟨K [x] , x⟩ 的配对在带有选定元素的 K-代数中是通用的。
*)
Definition poly_universal_element : AUniversalElement KAlg_Forget PolyAlg.
Proof.
  unshelve econstructor.
  - exact (@poly_x (`1 K)).
  - intros A a.
    unshelve econstructor.
    + exact (kalg_eval A a).
    + simpl; reflexivity.
    + intros g Hg t; simpl.
      symmetry.
      apply (poly_extend_unique (kalg_unit A) a (`1 g)).
      * intro c; symmetry; exact (`2 g c).
      * exact Hg.
Defined.

(*
   * The same content in the bundled form, and hence as a representation:
   the underlying-set functor of K-algebras is represented by K[x]. 

   --------
   * 捆绑形式中的相同内容，因此作为一个表示：
   K-代数的基础集合函子由 K [x] 表示。
*)
Definition poly_universal_element_bundled : UniversalElement KAlg_Forget :=
  UniversalElement_of_AUniversalElement poly_universal_element.

Definition poly_representation
  : @Curried_Hom (KAlg K) PolyAlg ≅[[KAlg K, Sets]] KAlg_Forget :=
  ue_representation KAlg_Forget PolyAlg poly_universal_element.

Definition poly_representable : Representable KAlg_Forget :=
  Representable_of_UniversalElement poly_universal_element_bundled.

(*
   * ... and as a universal arrow from the one-point setoid, in both of
   Theory/Universal/Arrow.v's encodings. 

   --------
   * … 并且作为来自单点集合的通用箭头，在 Theory/Universal/Arrow.v 的两种编码中。
*)
Definition poly_auniversal_arrow
  : AUniversalArrow SetsOne KAlg_Forget PolyAlg :=
  AUniversalArrow_of_AUniversalElement KAlg_Forget PolyAlg
    poly_universal_element.

Definition poly_universal_arrow : UniversalArrow SetsOne KAlg_Forget.
Proof.
  unshelve eapply (universal_arrow_from_UMP SetsOne KAlg_Forget PolyAlg).
  - exact (@universal_arrow _ _ _ _ _ poly_auniversal_arrow).
  - intros A f.
    unshelve econstructor.
    + exact (unique_obj (@universal_arrow_universal _ _ _ _ _
                           poly_auniversal_arrow A f)).
    + symmetry.
      exact (unique_property (@universal_arrow_universal _ _ _ _ _
                                poly_auniversal_arrow A f)).
    + intros v Hv.
      exact (uniqueness (@universal_arrow_universal _ _ _ _ _
                           poly_auniversal_arrow A f) v (symmetry Hv)).
Defined.

End KAlgebra.

(* * * ℤ[x]: the free unital ring on one generator / * * ℤ [x] : 一个生成元的自由单位环 *)

Definition ZPoly : RingObject := PolyRing Int_Ring.

(*
   * Evaluation at an element of an ARBITRARY unital ring: the
   commutation hypothesis is discharged by [zring_central], so no
   commutativity of the target is required. 

   --------
   * 在任意单位环的元素上进行求值：置换假设由 [zring_central] 解除，因此不要求目标环的可交换性。
*)
Definition zpoly_eval (S : RingObject) (b : carrier (rig_setoid S))
  : ZPoly ~{Rng}~> S.
Proof.
  refine (poly_extend (rng_from_Z S) b Int_Ring_commutative _).
  intro z; simpl; symmetry; apply zring_central.
Defined.

(*
   * Every homomorphism out of ℤ[x] agrees with [zring] on the constants,
   because ℤ is initial: the restriction along [poly_const] is a
   homomorphism out of ℤ, and there is only one of those. 

   --------
   * 从 ℤ 出发的每个同态在常数上都与 [zring] 一致，因为 ℤ 是初始对象：沿着 [poly_const] 的限制是从 ℤ 出发的同态，并且只有一个这样的同态。
*)
Lemma zpoly_hom_const (S : RingObject) (g : ZPoly ~{Rng}~> S) (z : Z) :
  rig_map g (@pt_const Int_Ring z) ≈ zring S z.
Proof.
  exact (rng_from_Z_unique S (rig_hom_compose g (poly_const Int_Ring)) z).
Qed.

(*
   * Riehl §2.3 Example 2.3.4: the indeterminate as a universal element of
   the underlying-set functor of rings. 

   --------
   * Riehl §2.3 示例 2.3.4：不确定元作为环的基础集合函子的一种普遍元素。
*)
Definition zpoly_universal_element : AUniversalElement Rng_Forget ZPoly.
Proof.
  unshelve econstructor.
  - exact (@poly_x Int_Ring).
  - intros S b.
    unshelve econstructor.
    + exact (zpoly_eval S b).
    + simpl; reflexivity.
    + intros g Hg t; simpl.
      symmetry.
      apply (poly_extend_unique (rng_from_Z S) b g).
      * intro z; exact (zpoly_hom_const S g z).
      * exact Hg.
Defined.

Definition zpoly_universal_element_bundled : UniversalElement Rng_Forget :=
  UniversalElement_of_AUniversalElement zpoly_universal_element.

(*
   * Riehl §2.1 Example 2.1.5(v): the forgetful functor Rng ⟶ Sets is
   represented by ℤ[x] — a natural isomorphism in [[Rng, Sets]], not
   merely the ∃! factorization property. 

   --------
   * Riehl §2.1 示例 2.1.5(v)：忘记函子 Rng ⟶ Sets 由 ℤ [x] 表示——在 [[Rng, Sets] 中是一个自然同构，而不仅仅是 ∃! 分解性质。
*)
Definition zpoly_representation
  : @Curried_Hom Rng ZPoly ≅[[Rng, Sets]] Rng_Forget :=
  ue_representation Rng_Forget ZPoly zpoly_universal_element.

Definition zpoly_representable : Representable Rng_Forget :=
  Representable_of_UniversalElement zpoly_universal_element_bundled.

(** ... and as a universal arrow from the one-point setoid. / ... 并且作为来自单点集合的一个通用箭头。 *)
Definition zpoly_auniversal_arrow
  : AUniversalArrow SetsOne Rng_Forget ZPoly :=
  AUniversalArrow_of_AUniversalElement Rng_Forget ZPoly
    zpoly_universal_element.

Definition zpoly_universal_arrow : UniversalArrow SetsOne Rng_Forget.
Proof.
  unshelve eapply (universal_arrow_from_UMP SetsOne Rng_Forget ZPoly).
  - exact (@universal_arrow _ _ _ _ _ zpoly_auniversal_arrow).
  - intros S f.
    unshelve econstructor.
    + exact (unique_obj (@universal_arrow_universal _ _ _ _ _
                           zpoly_auniversal_arrow S f)).
    + symmetry.
      exact (unique_property (@universal_arrow_universal _ _ _ _ _
                                zpoly_auniversal_arrow S f)).
    + intros v Hv.
      exact (uniqueness (@universal_arrow_universal _ _ _ _ _
                           zpoly_auniversal_arrow S f) v (symmetry Hv)).
Defined.

(* * * Monomorphisms of rings are injective / * * 环的单态射是单射 *)

(*
   * The probe Instance/Rng.v records as missing.  Two elements of R
   are separated by the two homomorphisms out of ℤ[x] that send x to
   them; a monomorphism identifies those homomorphisms only if it
   identifies the elements. 

   --------
   * 探针 Instance/Rng.v 被记录为丢失。R 的两个元素通过两个从 ℤ [x] 出发的同态分开，这两个同态将 x 映射到它们；如果一个单射仅在它识别这些元素时识别这些同态。
*)
Theorem rng_monic_injective {R S : RingObject} (f : R ~{Rng}~> S) :
  Monic f → ∀ a b : carrier (rig_setoid R),
    rig_map f a ≈ rig_map f b → a ≈ b.
Proof.
  intros Hm a b Hab.
  destruct Hm as [Hcancel].
  assert (Heq : f ∘ zpoly_eval R a ≈ f ∘ zpoly_eval R b).
  { intro t.
    transitivity (peval (rng_from_Z S) (rig_map f a) t).
    - apply (poly_extend_unique (rng_from_Z S) (rig_map f a)
               (f ∘ zpoly_eval R a)).
      + intro z; exact (zpoly_hom_const S (f ∘ zpoly_eval R a) z).
      + simpl; reflexivity.
    - symmetry.
      apply (poly_extend_unique (rng_from_Z S) (rig_map f a)
               (f ∘ zpoly_eval R b)).
      + intro z; exact (zpoly_hom_const S (f ∘ zpoly_eval R b) z).
      + simpl; symmetry; exact Hab. }
  exact (Hcancel ZPoly (zpoly_eval R a) (zpoly_eval R b) Heq (@poly_x Int_Ring)).
Qed.

(** Both directions, the forward one being Instance/Rng.v's. / 两个方向，正向的是 Instance/Rng.v 的。 *)
Theorem rng_monic_iff_injective {R S : RingObject} (f : R ~{Rng}~> S) :
  Monic f ↔ (∀ a b : carrier (rig_setoid R),
               rig_map f a ≈ rig_map f b → a ≈ b).
Proof.
  split.
  - exact (rng_monic_injective f).
  - exact (rng_injective_monic f).
Qed.

(*
   * * The commutation hypothesis is necessary

   [poly_extend] requires the chosen element to commute with the image
   of the structure map.  That is not an artifact of the fold: the
   indeterminate is central in K[x] by construction, so its image under
   ANY ring homomorphism out of K[x] commutes with the image of every
   coefficient.  This is what makes Awodey's adjunction a statement
   about COMMUTATIVE rings (Instance/Rng/Pointed.v), and it is proved
   rather than asserted. 

   --------
   * * 交换假设是必要的

   [poly_extend] 需要所选元素与结构映射的像交换。这并不是折叠的一个人工结果：该不定元在 K [x] 中按构造是中心元，因此它在任何从 K [x] 的环同态下的像都与每个系数的像交换。这正是使 Awodey 的伴随关系成为关于交换环的陈述（Instance/Rng/Pointed.v），而且这是被证明的，而不是被断言的。
*)

Lemma poly_hom_value_central (K S : RingObject)
  (g : PolyRing K ~{Rng}~> S) (c : carrier (rig_setoid K)) :
  rig_mul S (rig_map g (@poly_x K)) (rig_map g (@pt_const K c))
    ≈ rig_mul S (rig_map g (@pt_const K c)) (rig_map g (@poly_x K)).
Proof.
  rewrite <- !rig_map_mul.
  apply (proper_morphism (rig_map g)).
  exact (pe_mul_comm K _ _).
Qed.

(*
   * The same, read through the structure map a K-algebra hom restricts
   to: the value at x commutes with everything coming from K. 

   --------
   * 同样，通过结构图阅读一个 K-代数同态的限制：在 x 处的值与来自 K 的所有元素交换。
*)
Corollary poly_extend_commutation_necessary (K S : RingObject)
  (g : PolyRing K ~{Rng}~> S) (c : carrier (rig_setoid K)) :
  rig_mul S (rig_map g (@poly_x K))
            (rig_map (rig_hom_compose g (poly_const K)) c)
    ≈ rig_mul S (rig_map (rig_hom_compose g (poly_const K)) c)
                (rig_map g (@poly_x K)).
Proof. exact (poly_hom_value_central K S g c). Qed.

(** * Non-degeneracy / * 非退化 *)

(*
   * ** The coefficient inclusion is injective

   Evaluating in K itself — [phi] the identity, [s] the zero — returns a
   constant's coefficient, so no two coefficients are identified.  The
   only hypothesis is commutativity of K, which is what makes [K[x]] the
   polynomial ring rather than a quotient of it: over a NON-commutative
   K the constructor [pe_mul_comm] forces [const (ab) ≈ const (ba)], so
   this is the one place where the standing assumption is load-bearing
   rather than decorative. 

   --------
   * ** 系数包含是单射的

   在 K 本身中求值—— [phi] 为恒等，[s] 为零——返回一个常数的系数，因此没有两个系数被识别。唯一的假设是 K 的交换性，这正是使得 [K[x] 成为多项式环而非其商环的原因：在非交换的 K 上，构造器 [pe_mul_comm] 会强制 [const (ab) ≈ const (ba)]，因此这是唯一一个现有假设起关键作用而非装饰作用的地方。
*)

Lemma poly_const_injective (K : RingObject)
  (Kcomm : ∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a)
  (a b : carrier (rig_setoid K)) :
  pt_eq (@pt_const K a) (@pt_const K b) → a ≈ b.
Proof.
  intro H.
  refine (peval_respects K K (@rig_hom_id K) (rig_zero K) Kcomm _
            (@pt_const K a) (@pt_const K b) H).
  intro c; simpl.
  rewrite rig_mul_zero_l, rig_mul_zero_r; reflexivity.
Qed.

Corollary poly_const_monic (K : CRng) : Monic (kalg_unit (PolyAlg K)).
Proof.
  apply rng_injective_monic.
  exact (poly_const_injective (`1 K) (`2 K)).
Qed.

(*
   * ** The indeterminate is not a constant

   If x were the constant k, then in EVERY commutative K-algebra every
   chosen element would equal the image of k; taking the algebra to be K
   itself and the chosen element to be 0 and then 1 collapses the ring.
   The hypothesis is exactly non-triviality of K. 

   --------
   * ** 未定元不是一个常数

   如果 x 是常数 k，那么在每一个交换 K-代数中，每一个被选中的元素都会等于 k 的像；将代数取为 K 本身，并将被选中的元素取为 0 然后取 1，会使环崩溃。假设正是 K 的非平凡性。
*)

Lemma poly_x_not_constant (K : RingObject)
  (Kcomm : ∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a)
  (Hnt : rig_one K ≈ rig_zero K → False)
  (k : carrier (rig_setoid K)) :
  pt_eq (@poly_x K) (@pt_const K k) → False.
Proof.
  intro H.
  assert (H0 : rig_zero K ≈ k).
  { refine (peval_respects K K (@rig_hom_id K) (rig_zero K) Kcomm _
              (@poly_x K) (@pt_const K k) H).
    intro c; simpl.
    rewrite rig_mul_zero_l, rig_mul_zero_r; reflexivity. }
  assert (H1 : rig_one K ≈ k).
  { refine (peval_respects K K (@rig_hom_id K) (rig_one K) Kcomm _
              (@poly_x K) (@pt_const K k) H).
    intro c; simpl.
    rewrite rig_mul_one_l, rig_mul_one_r; reflexivity. }
  apply Hnt.
  rewrite H1, <- H0; reflexivity.
Qed.

(** ** The witnesses over ℤ / ** 在 ℤ 上的证人 *)

Definition zconst (z : Z) : carrier (rig_setoid ZPoly) := @pt_const Int_Ring z.

Lemma Int_nontrivial : rig_one Int_Ring ≈ rig_zero Int_Ring → False.
Proof. simpl; unfold Z_eqT; discriminate. Qed.

Corollary zpoly_x_not_constant (k : Z) :
  pt_eq (@poly_x Int_Ring) (zconst k) → False.
Proof.
  exact (poly_x_not_constant Int_Ring Int_Ring_commutative Int_nontrivial k).
Qed.

Corollary zpoly_x_nonzero :
  pt_eq (@poly_x Int_Ring) (rig_zero ZPoly) → False.
Proof. exact (zpoly_x_not_constant 0%Z). Qed.

Corollary zpoly_x_not_one :
  pt_eq (@poly_x Int_Ring) (rig_one ZPoly) → False.
Proof. exact (zpoly_x_not_constant 1%Z). Qed.

(*
   * Evaluation COMPUTES: the polynomial x² + 2x + 1 at 3 is 16.  This is
   the convertibility exception — an equation between elements of ℤ, not
   between morphisms. 

   --------
   * 计算评估：在 3 处计算多项式 x² + 2x + 1 的值为 16。这是可转换性异常——是 ℤ 元素之间的方程，而不是态射之间的方程。
*)
Definition zpoly_sample : carrier (rig_setoid ZPoly) :=
  pt_add (pt_add (pt_mul (@poly_x Int_Ring) poly_x)
                 (pt_mul (zconst 2%Z) poly_x))
         (zconst 1%Z).

Example zpoly_eval_at_three :
  rig_map (zpoly_eval Int_Ring 3%Z) zpoly_sample = 16%Z := eq_refl.

Example zpoly_eval_at_zero :
  rig_map (zpoly_eval Int_Ring 0%Z) zpoly_sample = 1%Z := eq_refl.

Example zpoly_eval_at_neg_one :
  rig_map (zpoly_eval Int_Ring (-1)%Z) zpoly_sample = 0%Z := eq_refl.

(*
   * The universal element is the indeterminate, and the mediating
   homomorphism sends it to the chosen element — both by [eq_refl]. 

   --------
   * 普遍元素是不确定的，而中介同态将其映射到所选择的元素——两者都通过 [eq_refl] 。
*)
Example zpoly_universal_elem_is_x :
  @aue_elem Rng Rng_Forget ZPoly zpoly_universal_element = @poly_x Int_Ring
  := eq_refl.

Example zpoly_mediator_at_x (S : RingObject) (b : carrier (rig_setoid S)) :
  rig_map (zpoly_eval S b) (@poly_x Int_Ring) = b := eq_refl.
