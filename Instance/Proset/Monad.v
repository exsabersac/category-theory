Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Idempotent.
Require Import Category.Structure.Thin.
Require Import Category.Structure.Thin.Monad.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Poset.
Require Import Category.Instance.Proset.Order.
Require Import Category.Instance.Proset.Monotone.
Require Import Category.Instance.Proset.Galois.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Arith.PeanoNat.
From Coq Require Import Lia.

Generalizable All Variables.

(* * * Monads on a preorder are closure operators / * * 预序上的单子是闭包算子 *)

(*
 nLab: https://ncatlab.org/nlab/show/closure+operator
 nLab: https://ncatlab.org/nlab/show/idempotent+monad
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Springer GTM 5, 1998, SS VI.1, printed p. 139, and SS VI.2,
 printed p. 141 (the example "Closure.")
 Book: Awodey, "Category Theory" (1st ed., CMU pre-print, Sept 2005),
 SS 10.2, Example 10.4, printed p. 270
 Book: Fong and Spivak, "Seven Sketches in Compositionality", arXiv v3,
 SS 1.4.4, printed pp. 33-35: Exercise 1.119, Definition 1.120,
 Examples 1.121, 1.122 and 1.123
 Book: Riehl, "Category Theory in Context", 2nd ed., SS 5.1,
 Example 5.1.7, printed p. 186

 WHAT THE BOOKS SAY.  Mac Lane, p. 139: for a preorder P, a functor
 T : P → P is a monotone function, and the unit and multiplication exist
 "precisely when x ≤ Tx, T(Tx) ≤ Tx" (display (3)); "The first equation
 of (3) gives Tx ≤ T(Tx)"; and if P is a partial order "the Eqs. (3)
 imply that T(Tx) = Tx.  Hence a monad T in a partial order P is just a
 closure operation".  On p. 141: "A closure operation T on a preorder P
 is a monad in P ...; a T-algebra is then an x ∈ P with Tx ≤ x ... a
 T-algebra is simply an element x ∈ P with x ≤ Tx ≤ x.  If P is a
 partial order, this means that x = Tx".  Awodey's Example 10.4 (p. 270)
 states the poset case and derives T² = T.  Seven Sketches,
 Definition 1.120 (pp. 33-34): a closure operator on a preorder is a
 monotone j with p ≤ j(p) and j(j(p)) ≅ j(p), idempotent only up to the
 preorder's isomorphism.  Riehl's Example 5.1.7 (p. 186) states the
 preorder conditions p ≤ Tp and T²p ≤ Tp, and T²p = Tp for a poset.

 WHERE CLOSURE OPERATORS OCCUR, as the same pages record.  Riehl
 (p. 186): the closure of a subset of a topological space, with the
 interior as the dual kernel operator (both are
 Instance/Top/Interior.v).  Awodey (p. 270): the "possibility operator"
 ◇p of modal logic.  Seven Sketches: a program that rewrites expressions
 (Example 1.121), and the modal operator "assuming B, −" on
 propositions ordered by entailment (Example 1.123; it is
 Instance/Props/Modal.v).
 In the tree, the element-level closures of a Galois connection were
 already present, as Instance/Grp/Galois.v's [GalClosed_l] and
 [GalClosed_r] and Instance/Proset/Galois/FixedPoints.v's
 [unit_fixed_iff_closed_r]; this file states the operator itself and
 its identification with a monad.

 WHICH READING THE RECORD IMPLEMENTS.  [ClosureOperator] takes Mac
 Lane's display (3) as its fields over a PREORDER: a monotone map
 [cl_fun] (Instance/Proset/Monotone.v's [MonotoneFun]), extensivity
 [cl_ext], and the multiplication inequality [cl_mult].  Seven Sketches'
 isomorphism is DERIVED as [cl_idem], its inverse being extensivity at
 cl x, which is Mac Lane's "Tx ≤ T(Tx)"; conversely [closure_of_iso]
 builds the record from Definition 1.120's form.  The two readings are
 therefore interderivable over a preorder, and the equation of Mac
 Lane, Awodey and Riehl needs antisymmetry, supplied as an explicit
 hypothesis in [closure_idem_eq].  No book is contradicted: Mac Lane
 defines a closure operation for a partial order on p. 139
 (t(tx) = tx) and on p. 141 calls a monad on a preorder a closure
 operation; he writes "=" only for a partial order, as Awodey and
 Riehl do for a poset; Seven Sketches states ≅ in Definition 1.120 and
 writes "=" in Example 1.123 for propositions under entailment, where
 it reads as mutual entailment.
 The fields are display (3) rather than Definition 1.120 for
 a measured reason: with them the round trip closure → monad → closure
 is [eq_refl] on the WHOLE record ([closure_round_trip], through
 primitive-projection eta), while a record carrying the isomorphism as a
 field is refused there, because the rebuilt inverse is ret at cl x
 and not the given one.

 THE CORRESPONDENCE.  [closure_functor] is Monotone.v's
 [Functor_of_monotone]; [closure_monad] has every law [I], since the
 hom-setoid of Instance/Proset.v's [Proset] is [True].  It IS
 Structure/Thin/Monad.v's [thin_monad] at the thin witness
 [fun _ _ _ _ => I], on the WHOLE record by [eq_refl]
 ([closure_monad_is_thin]).  It is not DEFINED through [thin_monad]:
 that route is refused bare, the sort level of Structure/Thin.v's
 [Thin] being left in the body alone; pinned to u or h it adds
 h <= u or u <= h (measured); with + the thin level stays in the block
 only.  The direct [Build_Monad] keeps u and h unrelated.
 [closure_of_monad]
 reads the monotone map off the functor and the two inequalities off ret
 and join; [monad_closure_iff] packages both directions.
 Instance/Poset.v's [Poset] is [Proset] with the antisymmetry argument
 discarded (Instance/Proset/Order.v's [Poset_is_Proset], by [eq_refl]),
 so every statement here applies to a poset unchanged
 ([poset_closure_of_monad]).

 ALGEBRAS ARE THE CLOSED ELEMENTS, by two routes.  Directly,
 [talgebra_iff_closed]: an algebra is exactly Tx ≤ x.  And by
 INSTANTIATION of Construction/Reflective/Idempotent.v, which is what
 the issue asks for: [talgebra_iff_closed_via_idem] goes through that
 file's [algebra_ret_iso] and [local_algebra] at the witness
 [thin_IdempotentMonad] of Structure/Thin/Monad.v, the derivation of
 idempotency from thinness.  [closed_iff_fixed] is Mac Lane's
 "x ≤ Tx ≤ x" as Tx ≅ x, and [mlocal_iff_closed] identifies membership
 in Idempotent.v's [MLocal_Subcategory] (ret x invertible) with
 closedness.  Instantiated at the thin witness, Idempotent.v also gives
 [proset_EM_equivalence], the Eilenberg-Moore category as the closed
 elements, and [proset_fixed_adj], the reflection onto them (Seven
 Sketches Example 1.122's adjunction, and the first of the two routes to
 Awodey's p. 271 construction), whose composite is T on objects and on
 arrows by [eq_refl] ([proset_factorisation_obj],
 [proset_factorisation_fmap]).  The second, order-theoretic
 route is Instance/Proset/Monad/Awodey.v, and that the reflection
 induces T again, for any idempotent monad, is
 Construction/Reflective/Idempotent/Induced.v.

 WITNESSES, so that the correspondence is not vacuous.
 [succ_not_monad]: the successor functor [NatSucc] of
 Instance/Proset/Galois.v is monotone and extensive but carries no
 monad, since the multiplication at 0 would be 2 ≤ 1.  [max_closure k]
 is n ↦ max k n, and [max_closed_iff] says its algebras are exactly the
 n with k ≤ n.

 STRENGTHS, measured.
 - closure → monad → closure: [eq_refl] on the whole record
 ([closure_round_trip]).
 - [closure_monad] against Structure/Thin/Monad.v's [thin_monad]:
 [eq_refl] on the whole record ([closure_monad_is_thin]).
 - monad → closure → monad: at ≈ of functors, with identity
 components ([monad_round_trip], which IS Monotone.v's
 [Functor_of_monotone_of_Functor]); [fobj] and [fmap] by [eq_refl]
 ([monad_round_trip_fobj], [monad_round_trip_fmap]), and ret and
 join by eq_refl ([monad_round_trip_ret], [monad_round_trip_join]):
 the unit and multiplication come back on the nose; the equation
 [closure_functor (closure_of_monad M) = M] is refused by conversion.
 Flipped first: with the law fields written as transparent [I]
 terms, no [Qed] anywhere, it is refused the same way, because the
 law fields of a variable M are stuck projections.  So ≈ is the
 strongest available.
 - [closure_of_iso]: the [to] leg of [cl_idem] is the given one by
 [eq_refl] ([closure_of_iso_to]); the whole isomorphism is refused
 by conversion, its [from] leg being extensivity at f x.
 - The algebra structure map round-trips by [eq_refl]
 ([talgebra_round]).
 - Under antisymmetry, ≅ becomes Leibniz [=] on elements: [closed_eq]
 and [closure_idem_eq].

 UNIVERSES, read off [About].  [ClosureOperator@{u}] lives in
 [Type@{u}]: its fields mention only the carrier's level, and the hom
 level [h] enters with the category, as in [closure_functor@{u h}].  The
 caps [u <= Defs.u0, u <= Relation_Definition.u0] are those of the
 stdlib's [PreOrder] and [relation], whose universes are global.  The
 biconditionals [@{u h +}] add one level for [iffT]: free where one side
 is a [Prop], and bounded below by u and h in [monad_closure_iff], whose
 left side is a sigma over functors; [mlocal_iff_closed] adds a second,
 the third level of [MLocal_Subcategory], free in that constant's
 block.  [monad_round_trip] adds two, with [h < u1] first carried by
 Theory/Functor.v's [Functor_Setoid].  The three instantiations of
 Idempotent.v carry one strict bound [h < ·], which several donors in
 their statements introduce in their own blocks and the elaborator
 unifies: Construction/Subcategory.v's [Sub] in all three;
 Theory/Functor.v's [Compose], the earliest in dependency order, in
 [proset_factorisation_obj]; Instance/Sets.v's [Sets], through
 [Adjunction], in [proset_fixed_adj]; and Theory/Equivalence.v's
 [EquivalenceOfCategories] with Monad/Eilenberg/Moore.v's
 [EilenbergMoore] in [proset_EM_equivalence].  The same donors bring
 stdlib caps: [u <= Projections.u0, h <= Projections.u0,
 h <= Projections.u1] from [Sub] and [Incl] in all three and in
 [proset_factorisation_fmap], and [h <= compose.u0, compose.u1,
 compose.u2, ID.u0] from [Sets] ([Sets@{o so}] has them at its level
 o) in [proset_fixed_adj].  [closure_monad_is_thin@{u h t}] adds
 [Thin]'s own block, u <= t and h <= t.  [closed_eq],
 [closure_idem_eq] and [poset_closure_of_monad] add the cap
 [u <= equality.u0] first carried by Instance/Poset.v's [eq_equiv].
 A systematic check found no level that occurs only in a body, with
 one designed exception: transparent, [talgebra_iff_closed_via_idem]
 carried four such levels (the sort of [Thin], a free level of
 [MLocal_Subcategory], and two from [algebra_ret_iso] and
 [local_algebra], one strictly above h), so it is a [Qed] lemma, and
 Private Polymorphic Universes (on; Lib.v does not unset it) keeps them
 out of its instance, which is [@{u h u0}] as for the direct route.
 [Thin] and [proset_thin] are declared twice in the tree; this file
 loads both copies (it requires Structure/Thin.v directly, which
 Instance/Proset/Order.v also requires, and Instance/Proset/Galois.v
 for [NatSucc]) and writes [Order.proset_thin], the one typed by
 Structure/Thin.v's [Thin].  No constant carries [Set].

 NOT DELIVERED.  Only [Proset] here: nothing over a setoid-valued
 order, no category of closure operators, and no functoriality in P.
 The modal operator of Example 1.123 over [Props] is
 Instance/Props/Modal.v.  No lemma that a monad on a [Proset] is
 determined by its functor, although every two with the same functor
 agree componentwise, at the trivial hom-setoid.  The dual, interior
 operators and comonads, is Instance/Proset/Monad/Interior.v, and its
 instance at the subsets of a space, with the closure of Riehl's
 Example 5.2.6 (iv), is Instance/Top/Interior.v. 

 --------
 nLab：https://ncatlab.org/nlab/show/closure+operator
 nLab：https://ncatlab.org/nlab/show/idempotent+monad
 书籍：Mac Lane，《为工作中的数学家准备的范畴论》，第二版，Springer GTM 5, 1998, 第 VI.1 节，印刷页 139，以及第 VI.2 节，印刷页 141（示例“Closure”）
 书籍：Awodey，《范畴论》（第一版，CMU 预印本，2005年9月），第 10.2 节，例 10.4，印刷页 270
 书籍：Fong 和 Spivak，《组合中的七个草图》，arXiv v3，第 1.4.4 节，印刷页 33-35：练习 1.119，定义 1.120，示例 1.121、1.122 和 1.123
 书籍：Riehl，《语境中的范畴论》，第二版，第 5.1 节，例 5.1.7，印刷页 186书中所说。Mac Lane，第139页：对于一个预序集P，一个函子
 T : P → P 是单调函数，当且仅当单位和乘法存在时，才有
 “x ≤ Tx, T(Tx) ≤ Tx”（显示式(3)）；“(3)的第一个方程给出Tx ≤ T(Tx)”；如果P是偏序集，“方程(3)表明T(Tx) = Tx。因此，在偏序集P中的单子T只是一个封闭运算”。在第141页：“在预序集P上的封闭运算T是P中的一个单子...；一个T-代数则是满足Tx ≤ x的P中的元素x... 一个T-代数只是一个满足x ≤ Tx ≤ x的P中的元素。如果P是偏序集，这意味着x = Tx”。Awodey的例子10.4（第270页）说明了偏序集情况并推导出T² = T。《七个草图》，定义1.120（第33-34）：在预序上，闭包算子是一个单调算子 j，满足 p ≤ j(p) 且 j(j(p)) ≅ j(p)，幂等性仅在预序的同构下成立。Riehl 的例子 5.1.7（第 186 页）说明了预序条件 p ≤ Tp 和 T²p ≤ Tp，并且对于偏序集有 T²p = Tp。闭包算子出现的地方，如同这些页所记。Riehl（第186页）：拓扑空间子集的闭包，其内部作为对偶核心算子（两者都是 Instance/Top/Interior.v）。Awodey（第270页）：模态逻辑中的“可能算子”◇p。Seven Sketches：一个重写表达式的程序（例子 1.121），以及顺承命题上的模态算子“假设 B，−”（例子 1.123；它是 Instance/Props/Modal.v）。
 在树中，Galois 对应的元素级闭包已存在，如 Instance/Grp/Galois.v 的 [GalClosed_l] 和 [GalClosed_r] 以及 Instance/Proset/Galois/FixedPoints.v 的 [unit_fixed_iff_closed_r]；该文件声明了算子本身及其与 monad 的对应关系。这正是《阅读记录》所实现的。[ClosureOperator] 麦克
 Lane的显示（3）作为预序下的场：单调映射
 [cl_fun]（实例/Proset/Monotone.v 的 [MonotoneFun]），扩展性
 [cl_ext]，乘法不等式[cl_mult]。七个素描
 同构可导出为[cl_idem] ，其逆函数为在 处的扩展性
 cl x，即Mac Lane的“Tx ≤ T（Tx）”;反过来也称为[closure_of_iso]
 从定义1.120的形式构建记录。两个读数分别是
 因此 在预序上可互导，以及 Mac 的方程
 Lane、Awodey 和 Riehl 需要反对称性，作为明确的
 [closure_idem_eq]假说。没有任何书被反驳：麦克莱恩
 定义了第139页偏序的闭包运算
 （t（tx） = tx）以及 p 上。141 将预序上的一个幺半群称为闭包运算；他只在偏序上写“=”，就像 Awodey 和 Riehl 在偏序集中所做的那样；《七个草图》在定义 1.120 中使用 ≅，并在例子 1.123 中对在蕴含下的命题写“=”，此时它表示相互蕴含。这些字段是 display (3) 而不是定义 1.120，这是有深思熟虑的原因的：有了它们，闭包 → 幺半群 → 闭包的往返转换在整个记录上是 [eq_refl]（[closure_round_trip]，通过原始投影 eta），而携带同构作为字段的记录在这里被拒绝，因为重建的逆在 cl x 处是 ret，而不是给定的那个。对应关系。[closure_functor] 是 Monotone.v 的 [Functor_of_monotone]；[closure_monad] 拥有每一条定律 [I]，因为 Instance/Proset.v 的同态集合 [Proset] 是 [True]。它是 Structure/Thin/Monad.v 在薄见证 [fun _ _ _ _ => I] 下的 [thin_monad]，通过 [eq_refl] 对整个记录（[closure_monad_is_thin]）。它不是通过 [thin_monad] 定义的：那条路径被直接拒绝，Structure/Thin.v 的 [Thin] 的类型层级仅保留在主体中；固定到 u 或 h 时，它增加 h <= u 或 u <= h（可度量）；加上 +，薄层级仅保留在块中。直接的 [Build_Monad] 保持 u 和 h 不相关。[closure_of_monad] 从函子读取单调映射，以及从 ret 和 join 读取两个不等式；[monad_closure_iff] 打包了这两个方向。Instance/Poset.v 的 [Poset] 是 [Proset] 且其反对称性参数被舍弃了（Instance/Proset/Order.v 的 [Poset_is_Proset]，由 [eq_refl] 所示），所以这里的每个陈述都同样适用于一个偏序集（[poset_closure_of_monad]）。代数是闭合元素，有两条途径。直接地，
 [talgebra_iff_closed]：一个代数恰好是 Tx ≤ x。还有通过
 Construction/Reflective/Idempotent.v 的实例化，这是问题所要求的：[talgebra_iff_closed_via_idem] 通过该文件的 [algebra_ret_iso] 和 [local_algebra] 在 Structure/Thin/Monad.v 的见证 [thin_IdempotentMonad] 处，从薄性推导幂等性。[closed_iff_fixed] 是 Mac Lane 的 “x ≤ Tx ≤ x”，当 Tx ≅ x 时，[mlocal_iff_closed] 将 Idempotent.v 的 [MLocal_Subcategory]（取 x 可逆）中的成员资格与闭合性联系起来。在薄见证处实例化时，Idempotent.v 还给出了 [proset_EM_equivalence]，即作为闭合元素的 Eilenberg-Moore 范畴，以及 [proset_fixed_adj]，即对它们的反射（Seven Sketches 示例 1.122 的伴随，以及通向 Awodey 的 p 的两条途径中的第一条）。271 构造），其复合在对象上是 T，在箭头上由 [eq_refl]（[proset_factorisation_obj]，[proset_factorisation_fmap]）给出。第二条顺序理论途径是 Instance/Proset/Monad/Awodey.v，并且反射诱导 T 对于任何幂等单子都是成立的，见 Construction/Reflective/Idempotent/Induced.v。

 WITNESSES，因此此对应不是空的。[succ_not_monad]：Instance/Proset/Galois.v 的后继函子 [NatSucc] 是单调且扩展的，但不携带单子，因为在 0 处的乘法将是 2 ≤ 1。[max_closure k] 是 n ↦ max k n，[max_closed_iff] 表示它的代数恰好是满足 k ≤ n 的 n。优势，已测量。- 闭包 → 单子 → 闭包：在整个记录上 [eq_refl] ([closure_round_trip])。- [closure_monad] 对 Structure/Thin/Monad.v 的 [thin_monad]：在整个记录上 [eq_refl] ([closure_monad_is_thin])。- 单子 → 闭包 → 单子：在 ≈ 的函子上，并带有恒等组件 ([monad_round_trip]，这正是 Monotone.v 的 [Functor_of_monotone_of_Functor])；[fobj] 和 [fmap] 通过 [eq_refl] ([monad_round_trip_fobj], [monad_round_trip_fmap])，以及 ret 和 join 通过 eq_refl ([monad_round_trip_ret], [monad_round_trip_join])：单位和乘法完全一致；方程 [closure_functor (closure_of_monad M) = M] 在转换时被拒绝。先翻转：将定律字段写成透明 [I] 项，没有任何 [Qed]，它同样被拒绝，因为变量 M 的定律字段是固定的投影。因此 ≈ 是可用的最强关系。- [closure_of_iso]：[cl_idem] 的 [to] 部分是由 [eq_refl]（[closure_of_iso_to]）给出的；整体同构因转换而被拒绝，其 [from] 部分在 f x 上具有扩展性。- 代数结构映射通过 [eq_refl]（[talgebra_round]）来回。- 在反对称性下，≅ 在元素上变为 Leibniz [=]：[closed_eq] 和 [closure_idem_eq] 。宇宙，读取 [About]。[ClosureOperator@{u}] 生活在 [Type@{u}]：它的字段仅提及载体的级别，以及同质级别 [h]，它随类别进入，如 [closure_functor@{u h}]。大写的 [u <= Defs.u0, u <= Relation_Definition.u0] 是 stdlib 的 [PreOrder] 和 [relation]，其宇宙是全局的。双条件 [@{u h +}] 为 [iffT] 添加一个级别：当一方是 [Prop] 时为自由，并在 [monad_closure_iff] 中由 u 和 h 下界，其左侧是对函子进行 sigma；[mlocal_iff_closed] 添加第二个级别，即 [MLocal_Subcategory] 的第三级别，在该常量的块中自由。[monad_round_trip] 添加两个级别，[h < u1] 首先由 Theory/Functor.v 的 [Functor_Setoid] 承载。Idempotent.v 的三个实例各携带一个严格绑定 [h < ·]，若干捐赠者在他们的声明中在自己的模块中引入它，并且展开器在 Construction/Subcategory.v 中统一了三个 [Sub]；Theory/Functor.v 的 [Compose]，在依赖顺序上最早，在 [proset_factorisation_obj] 中；Instance/Sets.v 的 [Sets]，通过 [Adjunction]，在 [proset_fixed_adj] 中；以及 Theory/Equivalence.v 的 [EquivalenceOfCategories] 与 Monad/Eilenberg/Moore.v 的 [EilenbergMoore] 在 [proset_EM_equivalence] 中。相同的捐赠者引入了 stdlib 上限：[u <= Projections.u0, h <= Projections.u0, h <= Projections.u1] 来自 [Sub] 和 [Incl]，在三个实例中以及在 [proset_factorisation_fmap] 中，以及 [h <= compose.u0, compose.u1, compose.u2, ID.u0] 来自 [Sets]（[Sets@{o so}] 在其层级 o 具有它们）在 [proset_fixed_adj] 中。[closure_monad_is_thin@{u h t}] 添加了 [Thin] 自己的区块，u <= t 且 h <= t。[closed_eq]、[closure_idem_eq] 和 [poset_closure_of_monad] 添加了 [u <= equality.u0] 最初由 Instance/Poset.v 的 [eq_equiv] 承载的上限。系统检查未发现仅出现在主体中的层级，有一个设计的例外：透明的 [talgebra_iff_closed_via_idem] 承载了四个这样的层级（[Thin] 的类别，[MLocal_Subcategory] 的一个自由层级，以及来自 [algebra_ret_iso] 和 [local_algebra] 的两个层级，其中一个严格高于 h），所以它是一个 [Qed] 引理，并且 Private Polymorphic Universes（开启；Lib.v 不会取消它）将它们排除在其实例之外，对于直接路径来说是 [@{u h u0}]。[Thin] 和 [proset_thin] 在树中被声明了两次；这个文件加载了两个副本（它直接需要 Structure/Thin.v，而 Instance/Proset/Order.v 也需要它，并且 Instance/Proset/Galois.v 为 [NatSucc] 需要它）并写入 [Order.proset_thin]，即由 Structure/Thin.v 的 [Thin] 输入的一个。没有常量携带 [Set]。未交付。这里只有 [Proset]：没有集合值序的上限，没有闭包算子的范畴，也没有 P 上的函子性。示例 1.123 中 [Props] 的模态算子是 Instance/Props/Modal.v。没有引理说明 [Proset] 上的单子由其函子决定，尽管每两个具有相同函子的在平凡 Hom-setoid 上分量一致。对偶、内算子和余单子是 Instance/Proset/Monad/Interior.v，其在一个空间的子集上的实例，以及 Riehl 示例 5.2.6 (iv) 的闭包，是 Instance/Top/Interior.v。
*)

(* * ** Closure operators: Mac Lane's display (3) / * ** 闭包算子：Mac Lane 的显示 (3) *)

(* Mac Lane's display (3) as the fields: a monotone map, extensivity (the unit) and the multiplication inequality. / Mac Lane 的展示 (3) 作为域：单调映射、广延性（单位）和乘法不等式。 *)
Record ClosureOperator@{u} {A : Type@{u}} {R : relation A}
  (P : PreOrder R) := {
  cl_fun  : @MonotoneFun A R A R;
  cl_ext  : ∀ x, R x (cl_fun x);
  cl_mult : ∀ x, R (cl_fun (cl_fun x)) (cl_fun x)
}.

Arguments cl_fun {A R P} _.
Arguments cl_ext {A R P} _ _.
Arguments cl_mult {A R P} _ _.

(* Seven Sketches Definition 1.120 (b), derived: the inverse of the multiplication is extensivity at cl x. / 七个素描 定义 1.120 (b)，导出：乘法的逆运算是在 cl x 的范围上的可扩展性。 *)
Definition cl_idem@{u h} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (c : ClosureOperator@{u} P) (x : A) :
  cl_fun c (cl_fun c x) ≅[Proset@{u h} P] cl_fun c x :=
  @Build_Isomorphism (Proset@{u h} P) _ _
    (cl_mult c x) (cl_ext c (cl_fun c x)) I I.

(* The smart constructor from Definition 1.120's form. / 定义 1.120 中的智能构造函数的形式。 *)
Definition closure_of_iso@{u h} {A : Type@{u}} {R : relation A}
  (P : PreOrder R) (f : @MonotoneFun A R A R) (ext : ∀ x, R x (f x))
  (idem : ∀ x, f (f x) ≅[Proset@{u h} P] f x) : ClosureOperator@{u} P :=
  {| cl_fun  := f
   ; cl_ext  := ext
   ; cl_mult := fun x => to (idem x) |}.

Example closure_of_iso_to@{u h} {A : Type@{u}} {R : relation A}
  (P : PreOrder R) (f : @MonotoneFun A R A R) (ext : ∀ x, R x (f x))
  (idem : ∀ x, f (f x) ≅[Proset@{u h} P] f x) (x : A) :
  to (cl_idem@{u h} (closure_of_iso P f ext idem) x) = to (idem x)
  := eq_refl.

(** ** The correspondence / ** 通讯 *)

(* The endofunctor of the thin category, through Monotone.v. / 通过 Monotone.v 的薄范畴的终端函子。 *)
Definition closure_functor@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) :
  Proset@{u h} P ⟶ Proset@{u h} P :=
  Functor_of_monotone P P (cl_fun c).

(* Closure → monad: every law is [I], the hom-setoid being [True]. / 闭包 → 单子：每条定律是 [I]，同态集为 [True]。 *)
Definition closure_monad@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) :
  @Monad (Proset@{u h} P) (closure_functor c) :=
  @Build_Monad (Proset@{u h} P) (closure_functor c)
    (fun x => cl_ext c x) (fun x => cl_mult c x)
    (fun _ _ _ => I) (fun _ => I) (fun _ => I) (fun _ => I)
    (fun _ _ _ => I).

(* Monad → closure: the two inequalities are ret and join. / Monad → 闭包：这两个不等式是 ret 和 join。 *)
Definition closure_of_monad@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} : ClosureOperator@{u} P :=
  {| cl_fun  := monotone_of_Functor P P M
   ; cl_ext  := fun x => @ret _ M MM x
   ; cl_mult := fun x => @join _ M MM x |}.

(* The correspondence. The pair is built with its family explicit, the 8.19/8.20 idiom recorded in Monotone.v. / 对应关系。该对是与其家族显式构建的，8.19/8.20 成语记录在 Monotone.v 中。 *)
Definition monad_closure_iff@{u h +} {A : Type@{u}} {R : relation A}
  (P : PreOrder R) :
  { M : Proset@{u h} P ⟶ Proset@{u h} P & @Monad (Proset@{u h} P) M }
    ↔ ClosureOperator@{u} P :=
  (fun p => match p with existT _ M MM => closure_of_monad M (MM := MM) end,
   fun c => existT (fun M : Proset@{u h} P ⟶ Proset@{u h} P =>
                      @Monad (Proset@{u h} P) M)
              (closure_functor c) (closure_monad c)).

(** ** Round trips / ** 往返 *)

(*
 [closure_monad] is Structure/Thin/Monad.v's [thin_monad], on the WHOLE
 record. 

 --------
 [closure_monad] 是 Structure/Thin/Monad.v 的 [thin_monad]，在整个记录上。
*)
Example closure_monad_is_thin@{u h t} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) :
  closure_monad@{u h} c
    = @thin_monad@{t u h} (Proset@{u h} P) (fun _ _ _ _ => I)
        (closure_functor@{u h} c) (cl_ext c) (cl_mult c) := eq_refl.

(* closure → monad → closure is the identity on the WHOLE record. / 闭包 → 单子 → 闭包在整个记录上是恒等的。 *)
Example closure_round_trip@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) :
  closure_of_monad@{u h} (closure_functor@{u h} c) (MM := closure_monad c)
    = c := eq_refl.

(*
 monad → closure → monad is the identity up to ≈ of functors; [=] is
 refused by conversion. 

 --------
 单子 → 闭包 → 单子在函子的大约等价下是恒等的；[=] 被转换拒绝。
*)
Definition monad_round_trip@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} :
  closure_functor (closure_of_monad M (MM := MM)) ≈ M :=
  Functor_of_monotone_of_Functor P P M.

(* ...but its object and arrow maps are M's on the nose. / ……但它的对象和箭头映射正好就是 M。 *)
Example monad_round_trip_fobj@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) :
  fobj[closure_functor (closure_of_monad M (MM := MM))] x = fobj[M] x
  := eq_refl.

Example monad_round_trip_fmap@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x y : A) (f : R x y) :
  fmap[closure_functor (closure_of_monad M (MM := MM))] f = fmap[M] f
  := eq_refl.

(* ...and the monad it rebuilds has M's unit and multiplication. / ...并且它重建的单子具有 M 的单元和乘法。 *)
Example monad_round_trip_ret@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) :
  @ret _ _ (closure_monad (closure_of_monad M (MM := MM))) x = @ret _ M MM x
  := eq_refl.

Example monad_round_trip_join@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) :
  @join _ _ (closure_monad (closure_of_monad M (MM := MM))) x
    = @join _ M MM x := eq_refl.

(* * ** Algebras are the closed elements / * ** 代数是封闭的元素 *)

(* Mac Lane p. 141: an algebra is exactly an x with Tx ≤ x. / Mac Lane 第141页：一个代数正好是一个 x，使得 Tx ≤ x。 *)
Definition talgebra_iff_closed@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) :
  @TAlgebra (Proset@{u h} P) M MM x ↔ R (M x) x :=
  (fun alg => @t_alg (Proset@{u h} P) M MM x alg,
   fun h => @Build_TAlgebra (Proset@{u h} P) M MM x h I I).

Example talgebra_round@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) (h : R (M x) x) :
  match talgebra_iff_closed M x with
  | (to_closed, of_closed) => to_closed (of_closed h)
  end = h := eq_refl.

(* "x ≤ Tx ≤ x": closed means Tx ≅ x. / “x ≤ Tx ≤ x”：闭合意味着 Tx ≅ x。 *)
Definition closed_iff_fixed@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) :
  R (M x) x ↔ (M x ≅[Proset@{u h} P] x) :=
  (fun h => @Build_Isomorphism (Proset@{u h} P) _ _ h (@ret _ M MM x) I I,
   fun i => to i).

(* Idempotent.v's M-local objects (ret x invertible) are the closed ones. / Idempotent.v 的 M-局部对象（ret x 可逆）是封闭的那些。 *)
Definition mlocal_iff_closed@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) :
  sobj (Proset@{u h} P) (@MLocal_Subcategory (Proset@{u h} P) M MM) x
    ↔ R (M x) x :=
  (fun H => @two_sided_inverse _ _ _ _ H,
   fun h => @Build_IsIsomorphism (Proset@{u h} P) x (M x)
              (@ret _ M MM x) h I I).

(* The same, by instantiating Idempotent.v at the thin witness. [Qed] keeps four body-only universe levels private (see the header). / 通过在薄证据处实例化 Idempotent.v 同样。[Qed] 保持四个仅包含主体的宇宙层级为私有（参见头部）。 *)
Lemma talgebra_iff_closed_via_idem@{u h +} {A : Type@{u}}
  {R : relation A} {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) :
  @TAlgebra (Proset@{u h} P) M MM x ↔ R (M x) x.
Proof.
  exact (let IM := thin_IdempotentMonad (Order.proset_thin P) (MM := MM) in
         let (to_closed, of_closed) := mlocal_iff_closed M x in
         (fun alg => to_closed (@algebra_ret_iso _ M MM IM x alg),
          fun h => @local_algebra _ M MM IM x (of_closed h))).
Qed.

(* * ** The Eilenberg-Moore category and the reflection, instantiated / * ** 艾伦伯-摩尔范畴与反射，实例化 *)

(* The Eilenberg-Moore category is equivalent to the closed elements. / Eilenberg-Moore 范畴等价于封闭元素。 *)
Definition proset_EM_equivalence@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} :=
  @Idempotent_EM_Equivalence (Proset@{u h} P) M MM
    (thin_IdempotentMonad (Order.proset_thin P)).

(* The reflection onto the closed elements, t ⊣ i. / 反射到闭合元素，t ⊣ i。 *)
Definition proset_fixed_adj@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} :=
  @idem_reflective_adj (Proset@{u h} P) M MM
    (thin_IdempotentMonad (Order.proset_thin P)).

(* T = i ∘ t on objects, on the nose. / T = i ∘ t 在对象上，完全如此。 *)
Example proset_factorisation_obj@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) :
  fobj[Incl (Proset@{u h} P) (@MLocal_Subcategory (Proset@{u h} P) M MM)
         ◯ @idem_reflector (Proset@{u h} P) M MM
             (thin_IdempotentMonad (Order.proset_thin P))] x = M x
  := eq_refl.

(* ...and on arrows. / ...和箭头上。 *)
Example proset_factorisation_fmap@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x y : A) (f : R x y) :
  fmap[Incl (Proset@{u h} P) (@MLocal_Subcategory (Proset@{u h} P) M MM)
         ◯ @idem_reflector (Proset@{u h} P) M MM
             (thin_IdempotentMonad (Order.proset_thin P))] f = fmap[M] f
  := eq_refl.

(* * ** Partial orders: antisymmetry turns ≅ into = / * ** 偏序：反对称性将 ≅ 变为 = *)

(* Mac Lane p. 141: in a partial order an algebra is a fixed point. / Mac Lane 第141页：在偏序中，一个代数是一个不动点。 *)
Lemma closed_eq@{u h} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (AS : @Antisymmetric A eq eq_equiv R)
  (M : Proset@{u h} P ⟶ Proset@{u h} P) {MM : @Monad (Proset@{u h} P) M}
  (x : A) : @TAlgebra (Proset@{u h} P) M MM x → M x = x.
Proof. intro alg. exact (AS _ _ (@t_alg _ _ _ _ alg) (@ret _ M MM x)). Qed.

(* Mac Lane p. 139: in a partial order T(Tx) = Tx. / Mac Lane 第 139 页：在偏序中 T(Tx) = Tx。 *)
Lemma closure_idem_eq@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (AS : @Antisymmetric A eq eq_equiv R) (c : ClosureOperator@{u} P)
  (x : A) : cl_fun c (cl_fun c x) = cl_fun c x.
Proof. exact (AS _ _ (cl_mult c x) (cl_ext c (cl_fun c x))). Qed.

(* A monad on a [Poset] is accepted as it stands. / 在 [Poset] 上的莫纳德按原样被接受。 *)
Example poset_closure_of_monad@{u h} {A : Type@{u}} {R : relation A}
  (P : PreOrder R) (AS : @Antisymmetric A eq eq_equiv R)
  (M : @Poset A R P AS ⟶ @Poset A R P AS)
  {MM : @Monad (@Poset A R P AS) M} : ClosureOperator@{u} P :=
  closure_of_monad@{u h} M (MM := MM).

(** ** Witnesses / ** 证人 *)

(* Monotone and extensive, yet not a monad: join at 0 would be 2 ≤ 1. / 单调且广泛，但不是单子：在 0 处的并会是 2 ≤ 1。 *)
Theorem succ_not_monad@{u h} :
  @Monad (Proset@{u h} Nat.le_preorder) NatSucc@{u h u} → False.
Proof.
  intro MM.
  pose proof (@join _ NatSucc MM 0%nat) as H.
  simpl in H.
  lia.
Qed.

(* n ↦ max k n, a closure operator on (ℕ, ≤)... / n ↦ max k n，一个在 (ℕ, ≤) 上的闭包算子... *)
Definition max_mono@{u} (k : nat) : @MonotoneFun@{u u} nat Nat.le nat Nat.le :=
  {| mono_map := Nat.max k
   ; mono_pres := fun x y H => Nat.max_le_compat_l x y k H |}.

Lemma max_mult@{} (k n : nat) : (Nat.max k (Nat.max k n) <= Nat.max k n)%nat.
Proof. lia. Qed.

Definition max_closure@{u} (k : nat) : ClosureOperator@{u} Nat.le_preorder :=
  {| cl_fun  := max_mono k
   ; cl_ext  := fun n => Nat.le_max_r k n
   ; cl_mult := fun n => max_mult k n |}.

(* ...whose algebras are exactly the n above k. / ...其代数恰好是上述 n 超过 k 的代数。 *)
Lemma max_closed_iff@{u h +} (k n : nat) :
  @TAlgebra (Proset@{u h} Nat.le_preorder)
    (closure_functor@{u h} (max_closure@{u} k))
    (closure_monad@{u h} (max_closure@{u} k)) n ↔ (k <= n)%nat.
Proof.
  destruct (talgebra_iff_closed (closure_functor (max_closure k))
              (MM := closure_monad (max_closure k)) n) as [to_closed of_closed].
  split.
  - intro alg. pose proof (to_closed alg) as H. simpl in H. lia.
  - intro H. apply of_closed. simpl. lia.
Qed.
