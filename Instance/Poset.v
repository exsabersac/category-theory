Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Proset.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(* * * The category of a partially-ordered set. / * * 一个偏序集的范畴。 *)

(*
 nLab: https://ncatlab.org/nlab/show/poset
 Wikipedia: https://en.wikipedia.org/wiki/Partially_ordered_set

 A partially-ordered set forms a category directly from its preorder,
 since a poset is precisely a preorder (a [Proset]) satisfying the extra
 antisymmetry condition: x ≤ y ≤ x implies x = y. Antisymmetry adds nothing
 to the underlying [Category] construction (the hom-sets are unchanged); it
 only makes the resulting thin category skeletal, so that isomorphic objects
 are equal. nLab characterizes a poset as exactly "a skeletal thin category",
 equivalently "a skeletal (0,1)-category".  Both directions are proved as
 [Proset_Skeletal_iff_Antisymmetric] in Instance/Proset/Skeletal.v. (See Instance/Pos.v for [Pos], the
 category whose OBJECTS are posets and whose morphisms are monotone maps --
 a different construction from this one, which turns a single poset into a
 thin category.)

 Wikipedia: "Every poset (and every preorder) may be considered as a category
 in which every hom-set has at most one element. More explicitly, let
 hom(x, y) = {(x, y)} if x ≤ y (and otherwise the empty set) and
 (y, z) ∘ (x, y) = (x, z). Such categories are sometimes called thin.

 Posets are equivalent to one another if and only if they are isomorphic. In
 a poset, the smallest element, if it exists, is an initial object, and the
 largest element, if it exists, is a terminal object. Also, every preordered
 set is equivalent to a poset. Finally, every subcategory of a poset is
 isomorphism-closed." 

 --------
 nLab：https://ncatlab.org/nlab/show/poset
 Wikipedia：https://en.wikipedia.org/wiki/Partially_ordered_set

 一个偏序集合直接从其预序形成一个范畴，因为偏序集恰好是一个满足额外反对称条件的预序（[Proset]）：x ≤ y ≤ x 蕴含 x = y。反对称性对底层的 [Category] 构造没有任何新增（同态集合保持不变）；它只是使结果薄范畴成为骨架范畴，从而同构对象相等。nLab 将偏序集恰好描述为“一个骨架薄范畴”，等价于“一个骨架 (0,1)-范畴”。两个方向的证明在 Instance/Proset/Skeletal.v 中作为 [Proset_Skeletal_iff_Antisymmetric] 给出。（参见 Instance/Pos.v 获取 [Pos]，即对象为偏序集、态射为单调映射的范畴——与此构造不同，此构造将单个偏序集转换为薄范畴。）维基百科："每个偏序集（以及每个预序集）都可以被视为一个范畴，其中每个同态集最多包含一个元素。更明确地说，如果 x ≤ y，则设 hom(x, y) = {(x, y)}（否则为空集），并且定义 (y, z) ∘ (x, y) = (x, z)。这样的范畴有时称为薄范畴。

 偏序集相互等价的条件是它们同构。在一个偏序集中，如果存在最小元素，则该元素是初始对象；如果存在最大元素，则该元素是终对象。此外，每个预序集都与某个偏序集等价。最后，偏序集的每个子范畴都是同构闭合的。"
*)

(*
 Order theory as category theory: the collapse dictionary

 nLab:  https://ncatlab.org/nlab/show/Galois+connection
 Paper: Ore, "Galois connexions", Transactions of the AMS 55, 1944
 Paper: Lawvere, "Metric spaces, generalized logic, and closed
 categories", Rendiconti del Seminario Matematico e Fisico di
 Milano 43, 1973; Reprints in TAC 1, 2002

 In a thin category all parallel morphisms are equal, so every diagram
 commutes and every coherence condition holds vacuously.  Each
 categorical concept therefore collapses to its order-theoretic
 shadow, and [Poset] installs the resulting dictionary: an adjunction
 between posets is exactly a monotone Galois connection -- proved in
 both directions at Instance/Proset/Galois.v ([GaloisAdjunction],
 [GaloisOfAdjunction]), rather than only asserted here; a monad is a closure operator, the unit giving
 extensivity and the multiplication idempotency (Theory/Monad.v); a
 product is a meet, and more generally the limit of a diagram is the
 greatest lower bound of its objects (nLab, "meet"), while a coproduct
 is a join (Structure/Cocartesian.v).  The meet/join entries are no
 longer remarks: Instance/Proset/Limit.v proves both readings —
 [proset_limit_iff_glb] for limits/meets and [proset_colimit_iff_lub]
 for colimits/joins — over [Proset] at an arbitrary diagram shape, and
 they apply here since [Poset P] below is [Proset P].  Theorems proved for
 categories thereby
 specialize to classical order theory, and intuitions trained on
 orders lift to categories with proof relevance switched on.

 CORRECTION (#463).  The dictionary entry "a monad is a closure
 operator, the unit giving extensivity and the multiplication
 idempotency (Theory/Monad.v)" was asserted, and the file it cited
 only asserted it too.  It is now proved over [Proset], and so over
 [Poset], which is [Proset] with antisymmetry discarded:
 Instance/Proset/Monad.v's [closure_of_monad] and [closure_monad] are
 the two directions ([monad_closure_iff]), and [talgebra_iff_closed]
 identifies the algebras with the closed elements.  Measured against
 the entry, the multiplication gives only T(Tx) ≤ Tx (Mac Lane's
 display (3), p. 139).  Idempotency up to ≅ also uses the unit at Tx
 ([cl_idem]; in any thin category, Structure/Thin/Monad.v's
 [thin_join_IsIso]).  The equation T(Tx) = Tx needs antisymmetry,
 supplied as an explicit [Antisymmetric] hypothesis
 ([closure_idem_eq]), since the category [Poset P] does not carry it.
 The dual entry, a comonad is an interior operator whose coalgebras
 are the open elements, is Instance/Proset/Monad/Interior.v's
 [interior_of_comonad] and [wcoalgebra_iff_open].

 The dictionary predates category theory.  The name Galois connection
 honours the inclusion-reversing correspondence between intermediate
 fields and subgroups in the fundamental theorem of Galois theory; the
 abstract notion, in its antitone form, is due to Ore (1944), after
 Birkhoff's Lattice Theory (AMS Colloquium Publications 25, 1940) had
 treated the power-set polarities induced by a binary relation; the
 modern survey is Erné, Koslowski, Melton, Strecker, "A primer on
 Galois connections", Annals of the New York Academy of Sciences 704,
 1993.  Closure operators go back to E. H. Moore's Introduction to a
 Form of General Analysis (1910), and around 1930 Tarski abstracted
 logical deduction to a finitary closure operator on sets of sentences
 — the consequence operator, in this dictionary a monad on the poset
 of theories (Wikipedia, "Closure operator").  Lawvere then made the
 dictionary itself the object of study: "Adjointness in Foundations"
 (Dialectica 23, 1969) exhibits the quantifiers as the adjoint triple
 ∃ ⊣ substitution ⊣ ∀, and the 1973 paper cited above reads a poset as
 a skeletal category enriched over the truth values — realized in-tree
 by [Enriched_Two_preorder] and [EnrichedFunctor_Two_monotone] in
 Construction/Enriched/Two.v, over the walking arrow of Instance/Two.v
 — while the same recipe over ([0, ∞], ≥, +) makes a metric space a
 category whose composition law is the triangle inequality (nLab,
 "Lawvere metric space").

 Thinness also marks a size boundary in the adjoint functor theorems.
 Between small preorders, a functor that preserves all small meets
 from a complete domain has a left adjoint outright, the candidate
 value being a meet over everything (nLab, "adjoint functor theorem").
 For genuine categories that computation is out of reach: by Freyd's
 observation, any complete small category is a preorder, which is
 exactly why the general theorem in Adjunction/GAFT.v must carry a
 [SolutionSet] hypothesis.

 The working uses run through the same corner.  Abstract
 interpretation (Cousot and Cousot, "Abstract Interpretation: A
 Unified Lattice Model for Static Analysis of Programs by Construction
 or Approximation of Fixpoints", POPL 1977) takes an abstraction to be
 a Galois connection between concrete and abstract domains and reads a
 loop as a Knaster–Tarski least fixed point in a complete lattice;
 formal concept analysis organizes object–attribute data by the
 concept lattice of a power-set Galois connection (Ganter and Wille,
 1999); and the opening chapter of Fong and Spivak's Seven Sketches
 in Compositionality (2018) — "Generative Effects: Orders and Galois
 Connections" in its 2019 Cambridge edition — takes a generative
 effect to be an observation that does not preserve joins, detected
 by a Galois connection.  The computational reading beneath all of
 these is proof irrelevance: under the [Proset] construction a
 hom-set is the mere proposition x ≤ y — identity is reflexivity,
 composition is transitivity, and the trivial setoid on each hom-set
 declares all proofs of an entailment equal — so an abstract domain
 is a poset precisely because an analyzer needs only that an
 approximation holds, never a witness.  Instance/Props.v is the
 logical instance, propositions ordered by entailment;
 Instance/Rel.v sits one level up, each hom-set itself ordered by
 inclusion — locally posetal rather than posetal. 

 --------
 作为范畴论的序理论：崩溃词典

 nLab:   https://ncatlab.org/nlab/show/Galois+connection
 论文: Ore, 《Galois 关联》，美国数学学会学报 55, 1944
 论文: Lawvere, 《度量空间、广义逻辑和闭类别》，米兰数学与物理研讨会报告 43, 1973；重印于 TAC 1, 2002在薄范畴中，所有平行态射都是相等的，因此每个图表都交换，并且每个相干性条件都自然成立。因此，每个范畴概念都简化为其序理论的影子，而 [Poset] 安装了结果字典：格之间的伴随正是单调伽罗瓦连接——在 Instance/Proset/Galois.v（[GaloisAdjunction], [GaloisOfAdjunction]）中双向证明，而不仅仅是在这里断言；单体是一种闭包算子，单位给出扩张性，乘法给出幂等性（Theory/Monad.v）；积是交，更一般地，一个图表的极限是其对象的最大下界（nLab, “meet”），而余积是并（Structure/Cocartesian.v）。汇/连接条目不再是备注：Instance/Proset/Limit.v 证明了两种读法 —— [proset_limit_iff_glb] 对于极限/汇，[proset_colimit_iff_lub] 对于余极限/连接 —— 在任意图形状上的 [Proset] ，并且它们在此适用，因为下面的 [Poset P] 是 [Proset P] 。由此在范畴中证明的定理因此专门适用于经典序理论，并且在序上训练的直觉可以推广到启用证明相关性的范畴中。更正 (#463)。词典条目“一个单子是一个闭包算子，单位提供扩展性，乘法提供幂等性（Theory/Monad.v）”曾被断言，而它引用的文件也只是断言了这一点。现在已在 [Proset] 上得到证明，因此也在 [Poset] 上成立，ZWZ10WZZ 是在放弃反对称性的情况下的 [Proset]：Instance/Proset/Monad.v 的 [closure_of_monad] 和 [closure_monad] 是两个方向（[monad_closure_iff]），而 [talgebra_iff_closed] 将代数与封闭元素对应。与条目相比，乘法仅给出 T(Tx) ≤ Tx（Mac Lane 的展示 (3)，p. 139）。至同构的幂等性也使用 Tx 的单位（[cl_idem]；在任何稀薄范畴中，Structure/Thin/Monad.v 的 [thin_join_IsIso]）。方程 T(Tx) = Tx 需要反对称性，这由一个显式的 [Antisymmetric] 假设（[closure_idem_eq]）提供，因为范畴 [Poset P] 不具备它。对偶项，一个余单子是一个内算子，其余代数是开元素，是 Instance/Proset/Monad/Interior.v 的 [interior_of_comonad] 和 [wcoalgebra_iff_open]。词典早于范畴论。Galois 连接这个名称是为了纪念伽罗瓦理论基本定理中中间域和子群之间的包含逆对应关系；抽象概念在其逆单调形式上归功于 Ore（1944），此前 Birkhoff 的《格论》（AMS Colloquium Publications 25, 1940）已经处理了由二元关系引起的幂集极性；现代综述见 Erné、Koslowski、Melton、Strecker 的《Galois 连接入门》，发表于《纽约科学院年报》704，1993。闭包算子可以追溯到 E. H.摩尔的《一般分析形式导论》（1910），大约在1930年，塔尔斯基将逻辑演绎抽象为句子集合上的有限闭包算子——推论算子，在本词典中是理论偏序集上的单子（维基百科，“闭包算子”）。然后，Lawvere 将字典本身作为研究对象：《基础中的伴随性》（Dialectica 23, 1969）将量词展示为伴随三重 ∃ ⊣ 替换 ⊣ ∀，而上文引用的 1973 年论文将偏序集解读为在真值上增强的骨架范畴——通过 Construction/Enriched/Two.v 中的 [Enriched_Two_preorder] 和 [EnrichedFunctor_Two_monotone] 在树中实现，基于 Instance/Two.v 中的 walking arrow ——而在 ([0, ∞] , ≥, +) 上使用相同方式，则使度量空间成为一个组合律为三角不等式的范畴（nLab，“Lawvere 度量空间”）。稀薄性也标志着伴随函子定理中的一个大小界限。在小偏序之间，一个保持完整域中所有小交的函子可以直接具有左伴随，该候选值是对所有元素的交（nLab，“伴随函子定理”）。对于真正的范畴，这种计算是无法实现的：根据弗雷德的观察，任何完全的小范畴都是偏序，这正是为什么Adjunction/GAFT.v中的一般定理必须带有[SolutionSet]假设。施工通道经过同一个角落。摘要
 抽象解释（Cousot 和 Cousot，《Abstract Interpretation: A Unified Lattice Model for Static Analysis of Programs by Construction or Approximation of Fixpoints》，POPL 1977）将抽象视为具体域与抽象域之间的 Galois 连接，并将循环读取为完全格中的 Knaster–Tarski 最小不动点；形式概念分析通过幂集 Galois 连接的概念格来组织对象–属性数据（Ganter 和 Wille，1999）；Fong 和 Spivak 的《组合性中的七个草图》（2018）的开篇章节——2019 年剑桥版名为《生成效应：序与 Galois 连接》——认为生成效应是不能保持并的观测，可通过 Galois 连接检测。在所有这些之下的计算阅读是证明无关性：在 [Proset] 构造下，一个同态集是单纯的命题 x ≤ y — 身份是自反性，组合是传递性，而每个同态集上的平凡集合宣告所有推导的证明都是相等的 — 因此一个抽象领域恰好是一个偏序集，因为分析器只需要近似成立，而不需要证据。Instance/Props.v 是逻辑实例，由蕴涵顺序排列的命题；Instance/Rel.v 位于更高一层，每个同态集本身按包含关系排列 — 局部偏序而非全局偏序。
*)

Lemma eq_equiv {C : Type} : @Equivalence C eq.
Proof.
  split; auto. intros x y z; apply eq_trans.
Qed.

Definition Poset {C : Type} `{R : relation C}
           `(P : PreOrder C R) `{@Antisymmetric C eq eq_equiv R} : Category := Proset P.

Section Examples.
Definition LessThanEqualTo_Category : Category :=
  @Poset nat PeanoNat.Nat.le PeanoNat.Nat.le_preorder
    (partial_order_antisym PeanoNat.Nat.le_partialorder).
End Examples.
