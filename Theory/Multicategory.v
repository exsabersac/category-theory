Require Import Category.Lib.
Require Import Category.Theory.Category.

From Coq Require Import Lists.List.
From Coq Require Import Sorting.Permutation.
Import ListNotations.

Generalizable All Variables.

(** * Symmetric multicategories / * 对称多重范畴 *)

(*
nLab: https://ncatlab.org/nlab/show/multicategory
   Wikipedia: https://en.wikipedia.org/wiki/Multicategory

   A multicategory (coloured operad) has objects and MULTImorphisms
   [mhom Γ c] whose source is a finite LIST of objects rather than a single
   object.  Composition is the single-slot (partial, "circle-i") operation:
   given [f : mhom (Γ1 ++ b :: Γ2) c] and [g : mhom Δ b], splicing [g] into
   the distinguished slot [b] yields [mcomp f g : mhom (Γ1 ++ Δ ++ Γ2) c].

   ZIPPER DESIGN.  The slot is addressed by an explicit zipper
   [(Γ1, b, Γ2)] — the context split into the part before the slot, the slot
   colour, and the part after — rather than by a numeric position into the
   list.  This keeps every law a statement about lists built with [++] and
   [::], so the boundary bookkeeping is exactly the [app_assoc]/[app_nil_r]
   algebra, with no heterogeneous-list telescopes and no positional
   arithmetic.  Simultaneous (Lambek-style) composition is not a field; it
   is derivable from iterated single-slot composition.

   BOUNDARY CASTS.  The unit and associativity laws relate multimorphisms
   whose source lists are PROPOSITIONALLY but not definitionally equal
   (e.g. [[] ++ Δ ++ []] versus [Δ], or the two reassociations of a spliced
   context).  Lists of [mobj] are Type-level object data, so [=] on them is
   sanctioned (the hom_cast discipline of Construction/ColouredPROP.v);
   morphisms themselves are only ever compared by [≈].  The recasting map
   [mcast] is taken as a FIELD equipped with groupoid laws — respectfulness
   [mcast_respects], loop collapse [mcast_id] quantified over an ARBITRARY
   proof of [Γ = Γ], and composition [mcast_trans] — following the
   [dsq_coerce] pack of Theory/DoubleCategory.v (itself the Phase-10
   [dtransport] pattern of Theory/Displayed.v).  Stating [mcast_id] over an
   arbitrary loop is what makes proof irrelevance of casts DERIVABLE
   ([mcast_proof_irrel] below) with no UIP on [list mobj], which is not
   available for an arbitrary object type.

   LAW STYLE.  The unit laws are stated through [mcast] along canonical
   proofs of the boundary equations (the [splice_eq_*] kit below), with
   [_any] variants derived from cast proof irrelevance.  The two
   associativity laws — nested (the second slot lands inside the spliced
   context [Δ]) and disjoint (two slots in the same outer context) — are
   stated over ANY proofs of their boundary equations, dodging proof
   normalization entirely; the kit provides witnesses so the laws are never
   vacuous.

   SYMMETRY.  The symmetric-group action is [msym p] for
   [p : tperm Γ Δ], a TYPE-valued permutation witness defined below with
   the same four constructors as the stdlib [Permutation]
   (Sorting.Permutation; in-tree precedent for permutation reasoning:
   Construction/ColouredPROP/Linear.v).  The stdlib relation itself is
   Prop-valued with four constructors, so it has no elimination into
   [Type]: an instance whose multimorphism carriers live in [Type]
   (e.g. hom-sets of a category, as in the representable multicategory of
   Theory/Multicategory/Representable.v) could never build the action by
   recursion on such a proof.  Mathematically the symmetric action is
   indexed by permutations as DATA — which is also why the identity law
   below is pinned to the canonical reflexivity witness — so the class
   carries its own [tperm], with [tperm_Permutation] recovering the
   stdlib proposition for interop.  The action is functorial in the
   WITNESS: identity on [tperm_refl] and composition along the
   [tperm_trans] constructor.  There is deliberately NO "[msym p ≈ id]
   for any loop [p : tperm Γ Γ]" law: a nontrivial self-permutation need
   not act trivially (that is the whole content of the symmetry).
   Compatibility with composition is the tractable block form
   [mcomp_equivariant]: permuting the three blocks [Γ1], [Δ], [Γ2]
   independently commutes with splicing.

   SCOPE of the symmetry, disclosed precisely.  The laws above make
   [msym] an action of tperm WITNESSES (a functorial action of the free
   structure the four constructors generate), and no field forces that
   action to descend to the symmetric group: two witnesses realizing the
   same underlying permutation are not required to act identically — in
   particular the swap involution [msym (tperm_trans (tperm_swap ..)
   (tperm_swap ..)) f ≈ f] of the textbook notion (Leinster; nLab
   "symmetric multicategory") is not derivable from the class.  Likewise
   [mcomp_equivariant] is required only in the independent-block form,
   not the slot-crossing exchange.  The in-tree instances
   (Theory/Multicategory/Representable.v, Endomorphism.v, and the Comm
   operad of Algebra.v) build their actions from braidings and product
   symmetries and are therefore EXPECTED to satisfy both stronger
   properties, but the descent lemmas themselves are not stated in-tree.
   Requiring them as fields — descent is exactly where an instance would
   consume the braid involution of a SYMMETRIC (vs merely braided)
   monoidal base — is deferred alongside the work order's own skeleton,
   which states the class as here.

--------
nLab：https://ncatlab.org/nlab/show/multicategory
 维基百科：https://en.wikipedia.org/wiki/Multicategory

多范畴（彩色操作数）具有对象和多态性
 [mhom Γ c] 的源是对象的有限列表而不是单个
 对象。 组合是单槽（部分，“circle-i”）操作：
 给定 [f : mhom (Γ1 ++ b :: Γ2) c] 和 [g : mhom Δ b]，将 [g] 拼接成
 杰出的插槽 [b] 产生 [mcomp f g : mhom (Γ1 ++ Δ ++ Γ2) c]。

拉链设计。 该插槽由显式拉链寻址
 [(Γ1, b, Γ2)] — 上下文分为槽之前的部分，槽
 颜色，以及后面的部分 - 而不是通过数字位置进入
 列表。 这使得每条法律都有关于使用 [++] 构建的列表的声明，并且
 [::]，所以边界簿记正是[app_assoc]/[app_nil_r]
 代数，没有异构列表望远镜，也没有位置
 算术。 同时（兰贝克式）构图不是一个领域； 它
 可从迭代的单时隙组合中导出。

边界铸造。 单位定律和结合律与多态性相关
 其源列表是 PROPOSITIONALLY 但定义上不相等
 （例如 [[] ++ Δ ++ []] 与 [Δ]，或拼接的两个重新关联
 上下文）。 [mobj] 的列表是类型级别的对象数据，因此它们上的 [=] 是
 批准（建筑/ ColoredPROP.v 的 hom_cast 规则）；
 态射本身仅由 [≈] 进行比较。 重铸地图
 [mcast] 被视为一个配备了群体法则的场域——尊重
 [mcast_respects]、循环崩溃 [mcast_id] 在任意值上进行量化
 [Γ = Γ] 的证明，以及 [mcast_trans] 的组合 — 遵循
 [dsq_coerce] 包 Theory/DoubleCategory.v（本身就是 Phase-10
 Theory/Displayed.v) 的 [dtransport] 模式。 [mcast_id] 的说明
 任意循环使得证明与强制转换无关
 （下面的 [mcast_proof_irrel]）[list mobj] 上没有 UIP，这不是
 可用于任意对象类型。

法律风格。 单位定律通过 [mcast] 沿着规范进行说明
 边界方程的证明（下面的 [splice_eq_*] 套件），其中
 [_any] 变体源自铸造证明无关性。 两人
 关联性定律 — 嵌套（第二个槽落在拼接的内部）
 context [Δ]）和不相交（同一外部上下文中的两个槽）- 是
 陈述其边界方程的任何证明，躲避证明
 完全正常化； 该套件提供证人，因此法律永远不会
 空虚的。

对称。 对称组操作是 [msym p]
 [p : tperm Γ Δ]，一个类型值排列见证，定义如下
 与 stdlib [Permutation] 相同的四个构造函数
 （Sorting.Permutation；排列推理的树内先例：
 构造/ColoredPROP/Linear.v)。 stdlib 关系本身是
 Prop 值有四个构造函数，因此没有消除
 [Type]：多态性载体存在于 [Type] 中的实例
 （例如，一个范畴的 hom 集，如可表示的多范畴
 Theory/Multicategory/Representable.v) 永远无法通过
 对这样的证明进行递归。
从数学上讲，对称作用是
 通过排列作为数据索引——这也是恒等律的原因
 下面是典型的反身性见证 - 所以类
 携带自己的 [tperm]，[tperm_Permutation] 恢复
 stdlib 互操作建议。 该动作是函数式的
 证人：[tperm_refl] 上的恒等和沿线的成分
 [tperm_trans] 构造函数。 故意没有“[msym p ≈ id]
 对于任何循环 [p : tperm Γ Γ]”定律：不平凡的自排列需求
 不做琐碎的事（这就是对称性的全部内容）。 与组合物的相容性是易于处理的块形式
 [mcomp_equivariant]：排列三个块 [Γ1]、[Δ]、[Γ2]
 独立通勤与拼接。

对称性的范围，精确揭示。 上述法律规定
 [msym] tperm WITNESSES 的一个动作（自由的函数动作）
 结构四个构造函数生成），并且没有场力
 下降到对称组的行动：两个证人意识到
 相同的底层排列不需要具有相同的作用——在
 特别是交换对合 [msym (tperm_trans (tperm_swap ..)
 (tperm_swap ..)) f ≈ f] 教科书概念 (Leinster; nLab
 “对称多范畴”）不能从该类派生。 同样
 仅在独立块形式下才需要 [mcomp_equivariant]，
 不是跨时隙交换。
树内实例
 （Theory/Multicategory/Representable.v、Endomorphism.v 和 Comm
 Algebra.v 的操作）从编织和乘积构建他们的动作
 对称性，因此期望满足更强的
 属性，但下降引理本身并未在树中说明。 要求它们作为字段 - 血统正是实例所需要的地方
 消耗 SYMMETRIC 的编织层对合（相对于仅编织）
 幺半群基 — 与工作订单自己的骨架一起推迟，
 其中声明了该类，如下所示。
*)

(*
Where multicategories come from, and what they are for

   nLab:  https://ncatlab.org/nlab/show/multicategory
   nLab:  https://ncatlab.org/nlab/show/operad
   Paper: Lambek, "Deductive systems and categories II. Standard
          constructions and closed categories", Lecture Notes in
          Mathematics 86, Springer 1969
   Book:  Leinster, "Higher Operads, Higher Categories", Cambridge
          University Press 2004

   A category composes UNARY operations, one source and one target.
   Large tracts of mathematics instead concern operations of several
   inputs and one output — a multiplication A × A → A, the grafting of
   trees, a proof drawing on several hypotheses.  A multicategory
   axiomatizes that directly: a morphism [mhom Γ c] whose source Γ is a
   finite LIST of objects, composed by substituting multimorphisms into
   the input slots of another.  The notion is due to Lambek, who coined
   the word while formalizing deductive systems and closed categories
   (Lambek, "Deductive systems and categories II", LNM 86, 1969;
   revisited in "Multicategories revisited", Contemporary Mathematics 92,
   1989); he read a deduction of a formula c from an ordered context
   c₁, …, cₙ as a multimorphism into c, so the motivation was logical
   before it was higher-categorical.

   Taking arities as primitive, rather than encoding several inputs as
   one tensored input A₁ ⊗ ⋯ ⊗ Aₙ → B, is the substance of the notion: a
   tensor is extra structure, and a base need not carry one.  A
   multicategory needs no monoidal product, and when one is present the
   multimorphisms it represents recover it.  This is representability
   (Hermida, "Representable multicategories", Advances in Mathematics
   151(2), 2000): every monoidal category yields the multicategory whose
   [mhom] from A₁, …, Aₙ to B is the ordinary homset C(A₁ ⊗ ⋯ ⊗ Aₙ, B).
   The construction, carried once over an object realization, is
   Theory/Multicategory/Representable.v.

   The single-colour case is the operad, a multicategory whose one object
   leaves each multimorphism fixed by the ARITY of its source
   (Theory/Multicategory/Operad.v).  The geometry predates the word:
   Boardman and Vogt described the little n-cubes operads and a
   recognition principle for iterated loop spaces (ideas circa 1968,
   published as "Homotopy Invariant Algebraic Structures on Topological
   Spaces", LNM 347, 1973), on the PROPs and PACTs of Adams and Mac Lane;
   the name and the definition are due to May ("The Geometry of Iterated
   Loop Spaces", LNM 271, 1972), whose recognition theorem relates
   connected algebras over the little n-cubes operad to n-fold loop
   spaces.  An algebra for an operad O on X is a map into the
   endomorphism operad, whose n-ary part is X^n → X; the library builds
   this [EndOperad] in Theory/Multicategory/Endomorphism.v and takes an
   [OperadAlgebra] to be a multifunctor into it
   (Theory/Multicategory/Algebra.v), where the terminal operad's algebras
   in Sets are exactly the commutative monoids of Instance/CMon.v
   ([Comm_algebra_CMon]).

   The reach beyond topology is broad.  Multicategories stand to operads
   as multi-sorted Lawvere theories stand to single-sorted ones, and a
   finite-product (Lawvere) theory, presented without forcing its product
   objects, is exactly a Cartesian multicategory (nLab, "Lawvere theory"):
   the source list tracks arities and its copy/discard structure realizes
   the structural rules of weakening and contraction, joining the
   Theory/Lawvere.v and Construction/PROP/ spine.
   Symmetric multicategories also organize algebraic K-theory (Elmendorf,
   Mandell, "Permutative categories, multicategories, and algebraic
   K-theory", Algebraic & Geometric Topology 9(4), 2009), and Leinster's
   generalized operads recast the language of higher category theory
   (Leinster 2004), Batanin's globular operads describing weak
   ∞-categories within it.

   The computational reading returns to Lambek.  A multimorphism into c
   is a term, or a proof, in a context: Γ is the typing context of free
   variables and c the conclusion, [mid a] the bare variable, and
   single-slot composition [mcomp] the substitution of one argument into
   a chosen slot.  So read, the two associativity laws
   [mcomp_assoc_nested] and [mcomp_assoc_disjoint] are the associativity
   of substitution — into a variable itself introduced by a substitution,
   and of two independent substitutions commuting — and the symmetric
   action [msym] is exchange, the renaming of free variables.  The ordered
   case, which has no exchange rule, is resource-sensitive and forms the
   syntactic core of substructural and linear logic; the symmetric action
   restores exchange, which is why the class carries it as separate data.

--------
多范畴从何而来以及它们的用途

nLab：https://ncatlab.org/nlab/show/multicategory
 nLab：https://ncatlab.org/nlab/show/operad
 论文：Lambek，“演绎系统和范畴 II. 标准
 结构和封闭范畴”，讲义
 数学 86，施普林格 1969
 书：伦斯特，“更高的操作，更高的范畴”，剑桥
 大学出版社2004年

范畴由一元运算、一个源和一个目标组成。 
相反，大量的数学内容涉及多个运算
 输入和一个输出 — 乘法 A × A → A，嫁接
 树，基于几个假设的证明。 多范畴
 直接公理化：态射 [mhom Γ c]，其源 Γ 是
 对象的有限列表，通过将多态性替换为
 另一个的输入槽。 这个概念是兰贝克提出的，他创造了
 形式化演绎系统和封闭范畴时的单词
 （Lambek，“演绎系统和范畴 II”，LNM 86，1969；
 重新审视“多范畴重新审视”，当代数学 92，
 1989）； 他从有序上下文中读到了公式 c 的推论
 c₁, …, cₙ 作为 c 的多态性，因此动机是合乎逻辑的
 在它成为更高范畴之前。

将 arities 作为原语，而不是将多个输入编码为
 一个张量输入 A₁ ⊗ ⋯ ⊗ Aₙ → B，是这一概念的实质内容：a
 张量是额外的结构，基数不需要携带张量。 一个
 多范畴不需要幺半群积，并且当存在时
 它代表的多态性恢复它。 这就是代表性
 （赫米达，“可表示的多范畴”，数学进展
 151(2), 2000)：每个幺半群范畴都会产生多范畴，其
 [mhom] 从 A₁, …, Aₙ 到 B 是普通的 homset C(A₁ ⊗ ⋯ ⊗ Aₙ, B)。 
在对象实现上进行一次的构造是
 理论/多范畴/可表示.v.

单色情况是操作数，一个多范畴，其一个对象
 让每个多态性由其源的 ARITY 固定
 （理论/多范畴/Operad.v）。 几何学早于这个词：
 Boardman 和 Vogt 描述了小型 n 立方体操作和
 迭代循环空间的识别原理（大约 1968 年的想法，
 发表为“拓扑上的同伦不变代数结构”
 Spaces”，LNM 347，1973），关于 Adams 和 Mac Lane 的 PROP 和 PACT；
 名称和定义源自 May（“迭代的几何图形”）
 Loop Spaces”, LNM 271, 1972），其识别定理涉及
 通过小 n 立方体操作的连接代数到 n 重循环
 空间。 X 上操作数 O 的代数是到
 自同态操作数，其n元部分为X^n → X； 图书馆建立
 Theory/Multicategory/Endomorphism.v 中的 [EndOperad] 并采用
 [OperadAlgebra] 成为一个多功能器
 (Theory/Multicategory/Algebra.v)，其中终结符的代数
 in Sets 正是 Instance/CMon.v 的可交换幺半群
 ([Comm_algebra_CMon])。

拓扑之外的范围是广泛的。 多范畴站立操作
 因为多分类劳维尔理论适用于单分类理论，并且
 有限乘积（Lawvere）理论，在不强制其乘积的情况下提出
 对象，正是笛卡尔多范畴（nLab，“Lawvere 理论”）：
 源列表跟踪参数及其复制/丢弃结构实现
 弱化和收缩的结构规则，加入
 理论/Lawvere.v 和构造/PROP/脊柱。 
对称多范畴还组织代数 K 理论（Elmendorf，
 曼德尔，“置换范畴、多范畴和代数
 K 理论”，代数与几何拓扑 9(4), 2009)，以及 Leinster 的
 广义运算重塑了高级范畴论的语言
 (Leinster 2004)，巴塔宁的球状操作描述了弱
 ∞-其中的范畴。

计算读数返回兰贝克。 A 到 c 的多态性
 是一个术语，或者一个证明，在上下文中： Г 是 free 的打字上下文
 变量和 c 结论，[mid a] 裸变量，以及
 单槽组合 [mcomp] 将一个参数替换为
 一个选定的插槽。 所以读一下，两个结合律
 [mcomp_assoc_nested] 和 [mcomp_assoc_disjoint] 是关联性
 替换 - 进入通过替换引入的变量本身，
 以及两个独立的通勤替换——以及对称
 [msym] 操作是交换，即自由变量的重命名。 所订购的
 case，没有交换规则，是资源敏感的并且形成
 子结构和线性逻辑的句法核心； 对称动作
 恢复交换，这就是该类将其作为单独数据携带的原因。
*)

(**
** The splice-equation kit

    Canonical proofs of the list equations along which the laws cast.
    Pure [app]-algebra: chains of [app_assoc]/[app_nil_r]/[app_comm_cons].
    The associativity laws are quantified over ANY proof of their
    equations, so the kit lemmas are only witnesses (and the convenient
    instantiation points).

--------
** 拼接方程工具包

列方程的规范证明，以及法律所制定的方向。
纯 [app] 代数：[app_assoc]/[app_nil_r]/[app_comm_cons] 的链。
结合律对于其方程的任何证明都是量化的，因此工具包引理只是证明者（以及方便的实例点）。
*)

Section SpliceKit.

Context {A : Type}.

(**
Boundary of the left unit law: splicing into [mid] at the unique slot
    ([Γ1 = Γ2 = []]).  [[] ++ (Δ ++ [])] is definitionally [Δ ++ []], so
    this is [app_nil_r] up to conversion.

--------
左单元法的边界：在唯一的槽中拼接到 [mid]（[Γ1 = Γ2 = []]）。[[] ++ (Δ ++ [])] 在定义上是 [Δ ++ []]，所以这在转换下是 [app_nil_r]。
*)
Lemma splice_eq_unit_left (Δ : list A) : [] ++ Δ ++ [] = Δ.
Proof. apply app_nil_r. Qed.

(**
Boundary of the right unit law: splicing [mid a] into a slot.
    [[a] ++ Γ2] is definitionally [a :: Γ2], so this is [eq_refl] up to
    conversion; kept as a named lemma for uniformity.

--------
右单元律的边界：将 [mid a] 拼接到一个插槽中。[[a] ++ Γ2] 在定义上是 [a :: Γ2]，所以这是 [eq_refl]，直至转换；为了统一性，保留为一个命名引理。
*)
Lemma splice_eq_unit_right (Γ1 Γ2 : list A) (a : A) :
  Γ1 ++ [a] ++ Γ2 = Γ1 ++ a :: Γ2.
Proof. reflexivity. Qed.

(**
Nested associativity, first cast: the context of [mcomp f g] (slot
    zipper [(Δ1, a, Δ2)] spliced between [Γ1] and [Γ2]) re-expressed as a
    zipper with the slot [a] on top.

--------
嵌套结合性，第一次转换：[mcomp f g] 的上下文（插槽 [(Δ1, a, Δ2)] 在 [Γ1] 和 [Γ2] 之间拼接）重新表达为顶部有插槽 [a] 的拉链。
*)
Lemma splice_eq_nested_slot (Γ1 Δ1 : list A) (a : A) (Δ2 Γ2 : list A) :
  Γ1 ++ (Δ1 ++ a :: Δ2) ++ Γ2 = (Γ1 ++ Δ1) ++ a :: (Δ2 ++ Γ2).
Proof. rewrite app_comm_cons; now rewrite !app_assoc. Qed.

(**
Nested associativity, final cast: the two orders of splicing produce
    the same context up to reassociation.

--------
嵌套结合性，最终转换：两种拼接顺序产生的上下文在重新结合后是相同的。
*)
Lemma splice_eq_nested (Γ1 Δ1 Θ Δ2 Γ2 : list A) :
  Γ1 ++ (Δ1 ++ Θ ++ Δ2) ++ Γ2 = (Γ1 ++ Δ1) ++ Θ ++ (Δ2 ++ Γ2).
Proof. now rewrite !app_assoc. Qed.

(**
Disjoint associativity: pulling a trailing block [w] out of the suffix
    of a three-block context.

--------
不相交的结合性：将一个尾随块 [w] 从三块上下文的后缀中提取出来。
*)
Lemma splice_eq_out (x y z w : list A) :
  x ++ y ++ (z ++ w) = (x ++ y ++ z) ++ w.
Proof. now rewrite !app_assoc. Qed.

(**
Disjoint associativity: pulling a trailing block [w] out of the suffix
    of a slot zipper.

--------
分离结合性：将一个尾随块 [w] 从槽拉链的后缀中拉出。
*)
Lemma splice_eq_slot_out (x : list A) (a : A) (y w : list A) :
  x ++ a :: (y ++ w) = (x ++ a :: y) ++ w.
Proof. rewrite app_comm_cons; now rewrite !app_assoc. Qed.

(**
Inverse orientation of [splice_eq_slot_out]: pushing a trailing block
    back into the suffix of a slot zipper.

--------
[splice_eq_slot_out] 的反向取向：将一个尾随块推回槽拉链的后缀中。
*)
Lemma splice_eq_slot_in (x : list A) (a : A) (y w : list A) :
  (x ++ a :: y) ++ w = x ++ a :: (y ++ w).
Proof. symmetry; apply splice_eq_slot_out. Qed.

End SpliceKit.

(**
** Permutation witnesses as data

    The Type-valued mirror of the stdlib [Permutation], constructor for
    constructor.  Because it lives in [Type], instances may build the
    symmetric action [msym p] by structural recursion on the witness [p]
    — not possible for the Prop-valued stdlib relation, which has no
    elimination into [Type].  Everything below is a transparent Fixpoint
    so that witnesses compute on list constructors.

--------
** 置换作为数据的见证  

    stdlib [Permutation] 的类型值镜像，构造函数的构造函数。由于它存在于 [Type] 中，实例可以通过对见证 [p] 的结构递归构建对称操作 [msym p] —— 这对于 Prop 值的 stdlib 关系是不可能的，因为它无法消除到 [Type]。下面的所有内容都是透明的 Fixpoint，因此见证可以在列表构造函数上进行计算。
*)

Inductive tperm {A : Type} : list A → list A → Type :=
  | tperm_nil : tperm [] []
  | tperm_skip (x : A) {Γ Δ : list A} :
      tperm Γ Δ → tperm (x :: Γ) (x :: Δ)
  | tperm_swap (x y : A) (Γ : list A) :
      tperm (y :: x :: Γ) (x :: y :: Γ)
  | tperm_trans {Γ Δ Λ : list A} :
      tperm Γ Δ → tperm Δ Λ → tperm Γ Λ.

Arguments tperm_nil {A}.

(** The canonical reflexivity witness: a stack of [tperm_skip]s. / 典型的自反性见证：一堆 [tperm_skip]。 *)
Fixpoint tperm_refl {A : Type} (Γ : list A) : tperm Γ Γ :=
  match Γ with
  | [] => tperm_nil
  | x :: Γ' => tperm_skip x (tperm_refl Γ')
  end.

(** Soundness: every witness maps to the stdlib proposition. / 健全性：每个证人在映射到标准库命题。 *)
Fixpoint tperm_Permutation {A : Type} {Γ Δ : list A} (p : tperm Γ Δ) :
  Permutation Γ Δ :=
  match p with
  | tperm_nil => perm_nil A
  | tperm_skip x q => perm_skip x (tperm_Permutation q)
  | tperm_swap x y l => perm_swap x y l
  | tperm_trans q r => perm_trans (tperm_Permutation q) (tperm_Permutation r)
  end.

(**
** Block-permutation combinators

    The equivariance law acts on the spliced context by permuting its
    three blocks independently.  The combinators are transparent
    counterparts of the stdlib's opaque [Permutation_app]: a witness on
    the left block extends along a fixed right tail ([tperm_app_l]), a
    fixed left prefix skips over a witness on the right block
    ([tperm_app_r]), and the general parallel composition is their
    transitive composite.

--------
** 块排列组合子

    等变律通过独立排列其三个块来作用于拼接上下文。这些组合子是标准库中不透明 [Permutation_app] 的透明对应物：左块上的见证沿着固定的右尾延伸（[tperm_app_l]），固定的左前缀跳过右块上的见证（[tperm_app_r]），而一般的并行组合则是它们的传递复合。
*)

(** Whiskering a witness by a fixed tail on the right. / 用右边固定的尾巴搔弄证人。 *)
Fixpoint tperm_app_l {A : Type} {Γ Γ' : list A} (p : tperm Γ Γ')
  (Δ : list A) : tperm (Γ ++ Δ) (Γ' ++ Δ) :=
  match p in tperm Γ0 Γ0' return tperm (Γ0 ++ Δ) (Γ0' ++ Δ) with
  | tperm_nil => tperm_refl Δ
  | tperm_skip x q => tperm_skip x (tperm_app_l q Δ)
  | tperm_swap x y l => tperm_swap x y (l ++ Δ)
  | tperm_trans q r => tperm_trans (tperm_app_l q Δ) (tperm_app_l r Δ)
  end.

(** Whiskering a witness by a fixed prefix on the left. / 在左侧用固定前缀对证人进行加胡须处理。 *)
Fixpoint tperm_app_r {A : Type} (Γ : list A) {Δ Δ' : list A}
  (q : tperm Δ Δ') : tperm (Γ ++ Δ) (Γ ++ Δ') :=
  match Γ with
  | [] => q
  | x :: Γ' => tperm_skip x (tperm_app_r Γ' q)
  end.

(** Parallel composition of witnesses across [++]. / 在 [++] 上的见证者的并行组合。 *)
Definition tperm_app {A : Type} {Γ Γ' Δ Δ' : list A}
  (p : tperm Γ Γ') (q : tperm Δ Δ') : tperm (Γ ++ Δ) (Γ' ++ Δ') :=
  tperm_trans (tperm_app_l p Δ) (tperm_app_r Γ' q).

(** Blockwise permutation of a three-block context [x ++ y ++ z]. / 对三块上下文 [x ++ y ++ z] 的分块排列。 *)
Definition perm_block3 {A : Type} {x x' y y' z z' : list A}
  (p : tperm x x') (q : tperm y y') (r : tperm z z') :
  tperm (x ++ y ++ z) (x' ++ y' ++ z') :=
  tperm_app p (tperm_app q r).

(** Blockwise permutation of a slot zipper [x ++ b :: z], fixing the slot. / 对槽拉链 [x ++ b :: z] 进行分块置换，固定槽位。 *)
Definition perm_block_slot {A : Type} (b : A) {x x' z z' : list A}
  (p : tperm x x') (r : tperm z z') :
  tperm (x ++ b :: z) (x' ++ b :: z') :=
  tperm_app p (tperm_skip b r).

(** ** The class / ** 那堂课 *)

Class Multicategory : Type := {
  (* Objects (colours). / 物体（颜色）。 *)
  mobj : Type;

  (* Multimorphisms: a finite list of sources, one target. / 多态映射：有限的源列表，一个目标。 *)
  mhom : list mobj → mobj → Type;

  mhomset (Γ : list mobj) (c : mobj) : Setoid (mhom Γ c);

  (*
Boundary coherence: recast a multimorphism along a propositional
     equality of source lists (Type-level object data, so [=] is
     sanctioned).  A field with groupoid laws, not an [eq_rect]: loop
     collapse over an ARBITRARY proof of [Γ = Γ] would otherwise require
     UIP on [list mobj].

--------
边界一致性：沿着源列表的命题相等重构一个多态（类型级对象数据，因此 [=] 是被允许的）。具有群范畴法则的字段，而不是 [eq_rect]：否则，在 [Γ = Γ] 的任意证明上进行循环折叠将需要 [list mobj] 上的 UIP。
*)
  mcast {Γ Γ' : list mobj} {c : mobj} (e : Γ = Γ') : mhom Γ c → mhom Γ' c;

  mcast_respects {Γ Γ' c} (e : Γ = Γ') :
    Proper (equiv ==> equiv) (@mcast Γ Γ' c e);

  (*
Proof-irrelevance of the boundary: casting along any loop is the
     identity.

--------
边界的证明无关性：沿任意环进行投射就是恒等映射。
*)
  mcast_id {Γ c} (e : Γ = Γ) (f : mhom Γ c) : mcast e f ≈ f;

  (* Casts compose. / 演员们组成。 *)
  mcast_trans {Γ Γ' Γ'' c} (e : Γ = Γ') (e' : Γ' = Γ'') (f : mhom Γ c) :
    mcast e' (mcast e f) ≈ mcast (eq_trans e e') f;

  (* The identity multimorphism on the singleton context. / 单元素上下文上的恒等多态映射。 *)
  mid (a : mobj) : mhom [a] a;

  (*
Single-slot ("circle-i") composition, slot addressed by the zipper
     [(Γ1, b, Γ2)]: splice [g] into the [b]-slot of [f].

--------
单槽（“circle-i”）组成，槽由拉链寻址
     [(Γ1, b, Γ2)]：将 [g] 拼接到 [f] 的 [b] 槽中。
*)
  mcomp {Γ1 Γ2 Δ : list mobj} {b c : mobj} :
    mhom (Γ1 ++ b :: Γ2) c → mhom Δ b → mhom (Γ1 ++ Δ ++ Γ2) c;

  mcomp_respects {Γ1 Γ2 Δ b c} :
    Proper (equiv ==> equiv ==> equiv) (@mcomp Γ1 Γ2 Δ b c);

  (*
Left unit: splicing [g] into the unique slot of [mid b]
     ([Γ1 = Γ2 = []]) gives back [g], up to the cast normalising
     [[] ++ Δ ++ []] to [Δ].

--------
左单元：将 [g] 拼接到 [mid b] 的唯一槽中（[Γ1 = Γ2 = []]），返回 [g]，直到进行类型转换规范化 [[] ++ Δ ++ []] 为 [Δ]。
*)
  mcomp_id_left {Δ : list mobj} {b : mobj} (g : mhom Δ b) :
    mcast (splice_eq_unit_left Δ) (mcomp (Γ1:=[]) (Γ2:=[]) (mid b) g) ≈ g;

  (*
Right unit: splicing [mid a] into a slot of [f] gives back [f], up to
     the cast normalising [Γ1 ++ [a] ++ Γ2] to [Γ1 ++ a :: Γ2].

--------
正确的单元：将 [mid a] 拼接到 [f] 的一个插槽中会得到 [f]，直到将 [Γ1 ++ [a] ++ Γ2] 强制类型转换为 [Γ1 ++ a :: Γ2]。
*)
  mcomp_id_right {Γ1 Γ2 : list mobj} {a c : mobj}
    (f : mhom (Γ1 ++ a :: Γ2) c) :
    mcast (splice_eq_unit_right Γ1 Γ2 a) (mcomp f (mid a)) ≈ f;

  (*
Associativity, nested shape: the second slot lands INSIDE the spliced
     context.  Splicing [g] into [f] and then [h] into the [a]-slot that
     [g] contributed agrees with splicing [mcomp g h] into [f] directly.
     Quantified over ANY proofs of the two boundary equations (witnesses:
     [splice_eq_nested_slot], [splice_eq_nested]).

--------
结合性，嵌套形状：第二个插槽落在拼接的上下文内部。将 [g] 拼接到 [f] 中，然后将 [h] 拼接到 [a] 插槽（由 [g] 提供）中，与直接将 [mcomp g h] 拼接到 [f] 中一致。在两个边界方程的任意证明（见证：[splice_eq_nested_slot]、[splice_eq_nested]）上进行量化。
*)
  mcomp_assoc_nested {Γ1 Γ2 Δ1 Δ2 Θ : list mobj} {a b c : mobj}
    (f : mhom (Γ1 ++ b :: Γ2) c) (g : mhom (Δ1 ++ a :: Δ2) b) (h : mhom Θ a)
    (e1 : Γ1 ++ (Δ1 ++ a :: Δ2) ++ Γ2 = (Γ1 ++ Δ1) ++ a :: (Δ2 ++ Γ2))
    (e2 : Γ1 ++ (Δ1 ++ Θ ++ Δ2) ++ Γ2 = (Γ1 ++ Δ1) ++ Θ ++ (Δ2 ++ Γ2)) :
    mcomp (mcast e1 (mcomp f g)) h ≈ mcast e2 (mcomp f (mcomp g h));

  (*
Associativity, disjoint shape: two slots in the SAME outer context
     ([a] before [b] in the zipper [(Γ1, a, Γ2 ++ b :: Γ3)] respectively
     [(Γ1 ++ a :: Γ2, b, Γ3)]) may be filled in either order.  Quantified
     over ANY proofs of the four boundary equations (witnesses:
     [splice_eq_out] for [d1]/[d4], [splice_eq_slot_out] for [d2],
     [splice_eq_slot_in] for [d3]).

--------
结合性，无交集形状：同一外部上下文中的两个槽位（在拉链[(Γ1, a, Γ2 ++ b :: Γ3)]中分别是[a]在[b]之前 [(Γ1 ++ a :: Γ2, b, Γ3)]）可以以任意顺序填充。对四个边界方程的任何证明进行量化（证明者：[splice_eq_out] 对 [d1]/[d4]，[splice_eq_slot_out] 对 [d2]，[splice_eq_slot_in] 对 [d3]）。
*)
  mcomp_assoc_disjoint {Γ1 Γ2 Γ3 Δ Θ : list mobj} {a b c : mobj}
    (f : mhom (Γ1 ++ a :: Γ2 ++ b :: Γ3) c) (g : mhom Δ a) (h : mhom Θ b)
    (d1 : Γ1 ++ Δ ++ Γ2 ++ b :: Γ3 = (Γ1 ++ Δ ++ Γ2) ++ b :: Γ3)
    (d2 : Γ1 ++ a :: Γ2 ++ b :: Γ3 = (Γ1 ++ a :: Γ2) ++ b :: Γ3)
    (d3 : (Γ1 ++ a :: Γ2) ++ Θ ++ Γ3 = Γ1 ++ a :: Γ2 ++ Θ ++ Γ3)
    (d4 : Γ1 ++ Δ ++ Γ2 ++ Θ ++ Γ3 = (Γ1 ++ Δ ++ Γ2) ++ Θ ++ Γ3) :
    mcomp (mcast d1 (mcomp f g)) h
      ≈ mcast d4 (mcomp (mcast d3 (mcomp (mcast d2 f) h)) g);

  (*
The symmetric-group action: relabel the source context along a
     permutation.  The action depends on the permutation WITNESS as
     data, which is why the witness is the Type-valued [tperm].

--------
对称群作用：沿一个置换重新标记源上下文。该作用依赖于作为数据的置换证据，这就是为什么证据是类型值的 [tperm]。
*)
  msym {Γ Δ : list mobj} {c : mobj} (p : tperm Γ Δ) :
    mhom Γ c → mhom Δ c;

  msym_respects {Γ Δ c} (p : tperm Γ Δ) :
    Proper (equiv ==> equiv) (@msym Γ Δ c p);

  (*
The action of the canonical reflexivity witness is trivial.  ONLY
     the [tperm_refl] witness: a nontrivial self-permutation need not act
     trivially, so no loop-quantified variant is stated.

--------
典型反身性见证的作用是平凡的。只有 [tperm_refl] 见证：一个非平凡的自我置换不必以平凡方式作用，因此没有说明循环量化的变体。
*)
  msym_id {Γ c} (f : mhom Γ c) : msym (tperm_refl Γ) f ≈ f;

  (* The action is functorial along the [tperm_trans] constructor. / 该作用沿 [tperm_trans] 构造函数是函子性的。 *)
  msym_compose {Γ Δ Λ c} (p : tperm Γ Δ) (q : tperm Δ Λ)
    (f : mhom Γ c) :
    msym q (msym p f) ≈ msym (tperm_trans p q) f;

  (*
Equivariance of splicing, block form: permuting the three blocks
     [Γ1], [Δ], [Γ2] independently (slot fixed) commutes with [mcomp].
     Both sides land in [mhom (Γ1' ++ Δ' ++ Γ2') c] on the nose, so no
     cast is needed.

--------
拼接的等变性，块形式：独立地（槽固定）置换三个块 [Γ1]、[Δ]、[Γ2] 与 [mcomp] 交换。双方准确地落在 [mhom (Γ1' ++ Δ' ++ Γ2') c] 上，因此不需要转换。
*)
  mcomp_equivariant {Γ1 Γ1' Γ2 Γ2' Δ Δ' : list mobj} {b c : mobj}
    (p : tperm Γ1 Γ1') (q : tperm Δ Δ')
    (r : tperm Γ2 Γ2')
    (f : mhom (Γ1 ++ b :: Γ2) c) (g : mhom Δ b) :
    msym (perm_block3 p q r) (mcomp f g)
      ≈ mcomp (msym (perm_block_slot b p r) f) (msym q g)
}.

#[export] Existing Instance mhomset.
#[export] Existing Instance mcast_respects.
#[export] Existing Instance mcomp_respects.
#[export] Existing Instance msym_respects.

(**
** The derived cast lemma pack

    Mirrors the [dsq_coerce] pack of Theory/DoubleCategory.v (one index
    instead of two): cancellation, flipping across [≈], proof irrelevance,
    and the [_any] forms of the canonical-proof laws.

--------
** 派生类型转换引理包

    镜像 Theory/DoubleCategory.v 的 [dsq_coerce] 包（一个索引而非两个）：消去法，跨 [≈] 翻转，证明不可区分性，以及规范证明定律的 [_any] 形式。
*)

Section MulticategoryLemmas.

Context {M : Multicategory}.

(* Casting there and back again cancels (left orientation). / 投掷来回取消（左侧方向）。 *)
Lemma mcast_symm_l {Γ Γ' : list mobj} {c : mobj} (e : Γ = Γ')
  (f : mhom Γ c) :
  mcast (eq_sym e) (mcast e f) ≈ f.
Proof.
  rewrite mcast_trans; apply mcast_id.
Qed.

(* Casting back and there again cancels (right orientation). / 投回并再次取消（正确的方向）。 *)
Lemma mcast_symm_r {Γ Γ' : list mobj} {c : mobj} (e : Γ = Γ')
  (g : mhom Γ' c) :
  mcast e (mcast (eq_sym e) g) ≈ g.
Proof.
  rewrite mcast_trans; apply mcast_id.
Qed.

(*
Reorienting a cast equation: a cast may be moved to the other side of
   [≈] by inverting the equality it rides on.

--------
重新定向一个类型转换方程：通过反转其所依赖的等式，类型转换可以移到 [≈] 的另一侧。
*)
Lemma mcast_flip {Γ Γ' : list mobj} {c : mobj} (e : Γ = Γ')
  (f : mhom Γ c) (g : mhom Γ' c) :
  mcast e f ≈ g ↔ f ≈ mcast (eq_sym e) g.
Proof.
  split; intros H.
  - rewrite <- H.
    symmetry; apply mcast_symm_l.
  - rewrite H.
    apply mcast_symm_r.
Qed.

(*
Casting does not depend on the proof cast along: the groupoid laws
   [mcast_id]/[mcast_trans] force any two parallel proofs to cast
   identically — no UIP on [list mobj] involved.

--------
类型转换不依赖于随附的证明：群范畴定律 [mcast_id]/[mcast_trans] 强制任何两个平行证明进行相同的转换 — [list mobj] 上不涉及 UIP。
*)
Lemma mcast_proof_irrel {Γ Γ' : list mobj} {c : mobj} (e1 e2 : Γ = Γ')
  (f : mhom Γ c) :
  mcast e1 f ≈ mcast e2 f.
Proof.
  apply (snd (mcast_flip e1 f (mcast e2 f))).
  symmetry; rewrite mcast_trans; apply mcast_id.
Qed.

(*
[mcast_trans] with the composite proof replaced by any proof of the
   endpoints' equation.

--------
[mcast_trans]，复合证明被任何端点方程的证明所替代。
*)
Lemma mcast_trans_any {Γ Γ' Γ'' : list mobj} {c : mobj}
  (e1 : Γ = Γ') (e2 : Γ' = Γ'') (e3 : Γ = Γ'') (f : mhom Γ c) :
  mcast e2 (mcast e1 f) ≈ mcast e3 f.
Proof.
  rewrite mcast_trans; apply mcast_proof_irrel.
Qed.

(* The left unit law along any proof of its boundary equation. / 左单位律沿其边界方程的任何证明。 *)
Lemma mcomp_id_left_any {Δ : list mobj} {b : mobj}
  (e : [] ++ Δ ++ [] = Δ) (g : mhom Δ b) :
  mcast e (mcomp (Γ1:=[]) (Γ2:=[]) (mid b) g) ≈ g.
Proof.
  transitivity
    (mcast (splice_eq_unit_left Δ) (mcomp (Γ1:=[]) (Γ2:=[]) (mid b) g)).
  - apply mcast_proof_irrel.
  - apply mcomp_id_left.
Qed.

(* The right unit law along any proof of its boundary equation. / 沿着其边界方程的任何证明的正确单位律。 *)
Lemma mcomp_id_right_any {Γ1 Γ2 : list mobj} {a c : mobj}
  (e : Γ1 ++ [a] ++ Γ2 = Γ1 ++ a :: Γ2) (f : mhom (Γ1 ++ a :: Γ2) c) :
  mcast e (mcomp f (mid a)) ≈ f.
Proof.
  transitivity
    (mcast (splice_eq_unit_right Γ1 Γ2 a) (mcomp f (mid a))).
  - apply mcast_proof_irrel.
  - apply mcomp_id_right.
Qed.

(*
The right unit law with no cast at all: the boundary equation
   [Γ1 ++ [a] ++ Γ2 = Γ1 ++ a :: Γ2] is definitional, so the two sides
   already inhabit convertible hom-setoids.

--------
没有任何类型转换的右单位律：边界方程 [Γ1 ++ [a] ++ Γ2 = Γ1 ++ a :: Γ2] 是定义性的，所以两边已经属于可转换的同态集合。
*)
Lemma mcomp_id_right_plain {Γ1 Γ2 : list mobj} {a c : mobj}
  (f : mhom (Γ1 ++ a :: Γ2) c) :
  mcomp f (mid a) ≈ f.
Proof.
  transitivity
    (mcast (splice_eq_unit_right Γ1 Γ2 a) (mcomp f (mid a))).
  - symmetry; apply mcast_id.
  - apply mcomp_id_right.
Qed.

End MulticategoryLemmas.
