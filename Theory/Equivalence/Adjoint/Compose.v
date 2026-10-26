Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.Compose.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Equivalence.Bundled.
Require Import Category.Theory.Equivalence.Strict.
Require Import Category.Instance.One.
Require Import Category.Instance.Discrete.Reconstruct.

Generalizable All Variables.

(** * Composition of adjoint equivalences / * 伴随等价的组成 *)

(*
nLab: https://ncatlab.org/nlab/show/adjoint+equivalence
   nLab: https://ncatlab.org/nlab/show/equivalence+of+categories
   Wikipedia: https://en.wikipedia.org/wiki/Equivalence_of_categories

   Mac Lane, Categories for the Working Mathematician, SIV.4, printed
   p. 95, Exercise 2, quoted from the page (ASCII transliteration of the
   arrows):

     “2. (a) Prove: the composite of two equivalences D -> C, C -> A is
             an equivalence.
         (b) State and prove the corresponding fact for adjoint
             equivalences.”

   Clause (a) is already in the tree: Theory/Equivalence/Bundled.v
   carries [EquivalenceOfCategories_Compose], with the two comparison
   cells and the bundled [Equivalence_trans].  It
   is consumed here, never rebuilt.  This module supplies clause (b):
   the composite of two adjoint equivalences, the identity adjoint
   equivalence, the comparison of the composite's unit and counit with
   those of its two constituents, and a measurement of the groupoid
   laws.  Exercises 3, 4 and 5 of the same page belong elsewhere and are
   cited rather than delivered here: Exercise 3 is
   Theory/Equivalence/Strict.v, Exercise 4 is Adjunction/LeftInverse.v,
   Exercise 5 is Adjunction/Diagonal/Connected.v.

   PLACEMENT.  The catalog entry suggests this be an addition to
   Theory/Equivalence/Adjoint.v.  That is an existing file, and this
   development is delivered as the new sibling module
   Theory/Equivalence/Adjoint/Compose.v instead, leaving the donor
   untouched.  The naming mirrors Adjunction/Compose.v, which stands to
   Theory/Adjunction.v in exactly the same relation.

   PRIOR ART, MEASURED -- AND THE COUNT MOVES WITH THE CRITERION, SO THE
   CRITERION IS STATED.  Searching for the BARE WORD
   [AdjointEquivalence] (word boundaries on both sides) returns FIVE
   files at the base commit, its declaring one included:
   Adjunction/FullFaithful.v (prose only),
   Structure/Monoidal/Dual.v, Construction/Subcategory/Dense.v
   and Theory/Equivalence/Strict.v (inhabitants), and
   Theory/Equivalence/Adjoint.v itself.  Searching for the same string
   as a SUBSTRING returns EIGHT (again counting the declaring file), the
   three extras being
   Theory/Equivalence/Adjunction.v (prose) and
   Theory/Equivalence/Creation.v and Theory/Equivalence/Limit.v,
   which consume [AdjointEquivalence_swap_adjunction] without ever
   naming the class.  Under EITHER criterion the conclusion is the same:
   NONE of them composes two adjoint equivalences and none exhibits an
   identity one -- the strings [AdjointEquivalence_Compose],
   [AdjointEquivalence_Id] and [AdjointEquivalence Id] each occur
   nowhere outside this module and its probe.  The INVERSE, by
   contrast, already exists: [AdjointEquivalence_swap]
   (Theory/Equivalence/Adjoint.v), with its underlying swapped
   adjunction [AdjointEquivalence_swap_adjunction].  It is cited
   below and NOT rebuilt.

   THE ROUTE, AND WHY IT IS NOT THE ONE THE CATALOG ENTRY PROPOSES.
   That entry proposes reading the composite off clause (a) by
   refinement:

     Equivalence_to_AdjointEquivalence
       (EquivalenceOfCategories_Compose
          (AdjointEquivalence_to_Equivalence A)
          (AdjointEquivalence_to_Equivalence B))

   That route is BUILT here, as
   [AdjointEquivalence_Compose_via_equivalence], and one of its premises
   is confirmed by measurement: the quasi-inverse of a composite
   equivalence IS the composite of the two quasi-inverses ON THE NOSE,
   because [quasi_inverse] of a [Build_EquivalenceOfCategories] is its
   second argument definitionally, so the constant elaborates at exactly
   the type [AdjointEquivalence (F' o F) (U o U')] with no transport and
   no coercion.  It is nevertheless not taken as the definition, because
   the composite it produces does not reduce, where the direct route's
   does.  A REASON, measured and not merely asserted: the two cells of
   [EquivalenceOfCategories_Compose] (Bundled.v) are closed with
   [Qed], so the refined adjunction's transposes are behind an opaque
   constant.  Read that at its strength -- it is a reason and not an
   isolation.  An out-of-tree experiment rebuilding those two cells
   verbatim but [Defined] was run, and normalizing the refined unit
   still stops, one constructor further in, at the transposing
   isomorphism itself; so the [Qed] cells are NOT shown to be the sole
   blocker, and no experiment makes the two routes agree.  The DIRECT
   route -- take [Adjunction_Compose] of the two underlying adjunctions
   and supply the two invertibility clauses -- reduces, and that is what
   the strict readbacks below record.
   The two composites are DIFFERENT: their whole records, their
   underlying adjunctions and their unit components are each rejected at
   [eq_refl] (negatives 1-3 of Test/ProbeAdjointCompose379.v).  Nothing is
   claimed about whether the two agree up to [~], in either direction:
   an adjunction structure on a fixed adjoint pair need not be unique,
   and no proof and no counterexample is offered here.

   WHAT IS DELIVERED, WITH GRADES.

   (A) An invertibility calculus for [IsIsomorphism], four constants:
       [IsIso_id], [IsIso_along] (transport along [~]), [IsIso_comp]
       (composites) and [IsIso_fmap] (functor images).  [IsIso_fmap]
       DUPLICATES [fmap_IsIsomorphism], which already exists at
       Construction/Reflective/Idempotent.v with the same statement
       up to the explicitness of [f] and the universe annotation (the
       donor takes [f] explicit and carries no universe binders) and
       essentially the same proof.  It is restated rather than
       required, on a measurement: that module's transitive in-project
       closure is 33, and requiring it would put the whole idempotent
       monad and reflective-subcategory development behind every
       consumer of this file.  The other three have no in-tree
       counterpart, measured by NAME over every .v file and by SHAPE:
       no declaration head outside this file states [IsIsomorphism]
       of an identity, of a composite, or transported along [~],
       the only [fmap]-shaped one being the acknowledged
       [fmap_IsIsomorphism].

   (B) [AdjointEquivalence_Compose A B :
          AdjointEquivalence (F' o F) (U o U')].
       Its underlying adjunction IS [Adjunction_Compose] of the two
       constituents at [eq_refl] ([AdjointEquivalence_Compose_adjunction]),
       and each of its two invertibility clauses is the named one at
       [eq_refl] ([..._unit_clause], [..._counit_clause]).

   (C) THE COMPARISON LEMMAS -- the point of clause (b), and the thing a
       bare existence statement would leave out.  Two grades are kept
       apart, because they differ:

       * [AdjointEquivalence_Compose_unit] and [_counit] state Mac
         Lane's whiskering formulas, unit ~ fmap[U] eta' o eta and
         counit ~ epsilon' o fmap[F'] epsilon.  These are [~] and NOT
         [eq_refl]: they are their donors [Adjunction_Compose_unit] and
         [Adjunction_Compose_counit] applied, both of which are [Qed]
         corollaries proved from [to_adj_unit] / [from_adj_counit], a
         genuine rewriting step and not a conversion.  Both are supplied
         by [:=] with no tactic, since the composite's adjunction is the
         donor's on the nose.

       * [AdjointEquivalence_Compose_unit_transpose] and
         [_counit_transpose] hold at [eq_refl]: the composite's unit IS
         the A-transpose of B's unit, and the composite's counit IS the
         B-inverse-transpose of A's counit.  This is the strict form the
         whiskered one is only [~]-equal to, and it is what makes the
         direct route worth taking.

       * [AdjointEquivalence_Compose_unit_inverse] and
         [_counit_inverse] read the two-sided inverses back at
         [eq_refl]: the inverse of the composite unit is
         eta^-1 o fmap[U] (eta'^-1), and of the composite counit
         fmap[F'] (epsilon^-1) o epsilon'^-1.

   (D) [AdjointEquivalence_Id C : AdjointEquivalence Id[C] Id[C]], over
       [Adjunction_Id] (which is Instance/Adjoints.v's [adj_id] reused,
       per Adjunction/Compose.v).  Its adjunction reads back at
       [eq_refl]; its unit and counit are [~] the identity, inherited
       from [Adjunction_Id_unit] / [_counit].

   (E) THE GROUPOID LAWS, MEASURED RATHER THAN ASSUMED, and the outcome
       is finer than “not statable”.  At the level of the CLASS the
       associativity and identity equations are not even well typed:
       [Compose] of functors is not associative on the nose and [Id] is
       not a strict unit for it (the Adjunction/Pare.v measurement), so
       [AdjointEquivalence (F'' o (F' o F)) ((U o U') o U'')] and
       [AdjointEquivalence ((F'' o F') o F) (U o (U' o U''))] are
       distinct types.  Both shapes are pinned as TYPING negatives in
       the probe, and no transport is invented.  But the OBJECT actions
       of the two bracketings agree definitionally, so the units and
       counits inhabit convertible types, and there the laws hold ON THE
       NOSE: [AdjointEquivalence_Compose_assoc_unit],
       [_assoc_counit], [_id_left_unit], [_id_left_counit],
       [_id_right_unit] and [_id_right_counit] are all [eq_refl].  So
       the trio composition/identity/inverse is available together, and
       the laws relating them hold exactly as far as the type theory
       permits them to be stated.

   (F) NON-VACUITY, and it is not degenerate on the axis that matters.
       [indiscrete_square] composes [AdjointEquivalence_swap] of
       Theory/Equivalence/Strict.v's [indiscrete_adjoint_equivalence]
       with that equivalence itself, giving an adjoint equivalence of
       [Indiscrete bool] with itself whose two functors are both
       [IndT o Erase (Indiscrete bool)].  That composite functor MOVES
       an object: [indiscrete_square_moves] computes its value at
       [false] to [true] by [eq_refl], and [indiscrete_square_not_id]
       closes by [discriminate], so the composite is not an identity
       adjoint equivalence -- indeed it does not even have the type of
       one, pinned as a TYPING negative.  The unit at [false] therefore
       runs between two DIFFERENT objects.  DISCLOSED: [Indiscrete]'s
       hom family ignores its endpoints --
       Instance/Discrete/Reconstruct.v declares
       [hom := fun _ _ => unit], the stdlib [unit : Set], which is also
       where the witness block's [Set] comes from -- so every hom-set
       there is a singleton, and the morphism-level statement “the unit
       at [false] IS the identity” is well typed and TRUE, at [eq_refl]
       and not merely at [~]; a morphism-level non-degeneracy statement
       is therefore unavailable.  This is the trap
       Theory/Equivalence/Strict.v records for its own counit; the
       honest non-degeneracy is the object-level one, and that is what
       is proved.

   WHAT IS NOT DELIVERED.  No direct construction of the inverse: the
   trio's third member is [AdjointEquivalence_swap], cited, and per the
   Theory/Equivalence/Strict.v measurement its unit does not reduce
   (it is built through [EquivalenceOfCategories_sym] and
   [Equivalence_to_AdjointEquivalence]); a hand-built swap whose
   transposes reduce is not attempted.  No comparison at [~] between the
   direct composite and the refinement route.  No uniqueness statement
   for the composite.  No category of categories and adjoint
   equivalences, so the groupoid laws are not packaged as a structure.
   No transport of an adjoint equivalence along a natural isomorphism of
   either adjoint.  No 2-categorical reading and no relation to
   Theory/Bicategory/Adjunction.v.  No witness at a pair of adjoint
   equivalences with three genuinely distinct categories.

   UNIVERSES, MEASURED OFF BOTH BINDER AND BLOCK.  The four constants
   of the invertibility calculus are FREE: [IsIso_along@{o h p}] has an
   EMPTY-of-equations block carrying only [Category]'s own [h <= p], and
   [IsIso_fmap@{xo xh xp yo yh yp u}] keeps the two categories' six
   levels apart, with only [Functor]'s own bounds.  That is the explicit
   binders' doing and it is measured, not assumed: written unannotated
   the same bodies minimize so as to identify hom with proof, and are
   then rejected at a category whose two levels are declared apart,
   where the annotated forms are accepted (the probe checks all four as
   controls at exactly those levels).

   Everything downstream of the adjunction vocabulary does identify hom
   with proof -- [Category@{u u0 u0}] in the BINDER, with no such
   equation in any constraint block, the trap that reading a block alone
   gets wrong.  THREE donors are probed and the first is easy to miss:
   the IDENTITY FUNCTOR [Id] forces it ON ITS OWN, so a probe that
   writes [Id[Cu]] into an [Adjunction] is measuring [Id] and not
   [Adjunction] -- the discriminating control is an arbitrary
   endofunctor of the same category, which IS accepted, so [Functor] is
   not a donor.  Probed at two such endofunctors so that no [Id] occurs
   in the command, [Adjunction] is a donor independently; and
   [AdjointEquivalence] is a third that CANNOT be tested apart from
   [Adjunction], its first field being [F -| U], so those two are not
   independent.  [AdjointEquivalence_Id] has both [Id] and [Adjunction]
   in reach and its negative isolates neither.

   The composite additionally carries [u0 = u2], [u0 = u4], [u2 = u4] --
   the three categories' hom-and-proof universes collapsed to one, with
   all three OBJECT universes free -- and that is forced by the mere
   presence of functors in BOTH directions before any adjunction is
   formed, pinned as its own formability negative.  [AdjointEquivalence_Id]
   carries no equation at all in its block.  The witness block carries
   [Set], inherited through Theory/Equivalence/Strict.v from
   Instance/One.v and Instance/Discrete/Reconstruct.v; none of it is
   claimed unavoidable.

   CLOSURE, measured as transitive in-project .vo dependencies EXCLUDING
   this file.  39 modules; 26 with the witness section's three requires
   dropped, so the non-vacuity witness costs 13.  All 13 arrive with
   [Theory.Equivalence.Strict] (39 against 32 with its edge dropped);
   [Instance.One] and [Instance.Discrete.Reconstruct] cost nothing on
   top of it and are required only to bring the names [Erase] and
   [Indiscrete] into scope.  Of the general-theory requires, no single
   one costs anything by itself -- dropping any one of them individually
   leaves the closure at 39, each being inside the others' closures --
   against the donors' own figures of 22 (Theory/Equivalence/Adjoint.v),
   20 (Adjunction/Compose.v) and 20 (Theory/Equivalence/Bundled.v).  The
   probe's closure is 40.

   TRANSPARENCY.  The file has four [Defined.] lines, the two obligations
   each of [IsIso_comp] and [IsIso_fmap]; NONE of them is load-bearing,
   measured by flipping all four to [Qed] in a scratch copy, where the
   file still compiles with every [eq_refl] readback intact.  They are
   [Defined] by the house convention rather than by need -- each is a
   law field, and the data fields are supplied inline.  The one [Qed] in
   the file is [indiscrete_square_not_id], which produces no data.

   REGISTRATION.  Following Theory/Equivalence.v and
   Theory/Equivalence/Adjoint.v, nothing here is registered for instance
   resolution: an adjoint equivalence is a choice of data, always passed
   explicitly at use sites.

--------
nLab: https://ncatlab.org/nlab/show/adjoint+equivalence
nLab: https://ncatlab.org/nlab/show/equivalence+of+categories
Wikipedia: https://en.wikipedia.org/wiki/Equivalence_of_categories

Mac Lane，《为工作数学家准备的范畴论》，SIV.4，第95页印刷，练习2，引自该页（箭头的ASCII音译）：

2. (a) 证明：两个等价 D -> C, C -> A 的复合是一个等价。
(b) 陈述并证明关于伴随等价的对应事实。

条款 (a) 已经在树中：Theory/Equivalence/Bundled.v，携带 [EquivalenceOfCategories_Compose]，包括两个比较单元和捆绑的 [Equivalence_trans]。它在这里被使用，从未重建。该模块提供条款 (b)：两个伴随等价的复合、恒等伴随等价、复合的单位和余单位与其两个组成部分的比较，以及对群体法则的测量。同一页的练习3、4和5属于其他地方，这里引用而未提供：练习3是 Theory/Equivalence/Strict.v，练习4是 Adjunction/LeftInverse.v，练习5是 Adjunction/Diagonal/Connected.v。

放置。目录条目建议将其添加到 Theory/Equivalence/Adjoint.v。这是一个已存在的文件，而本次开发被作为新的兄弟模块 Theory/Equivalence/Adjoint/Compose.v 提供，而不修改原始文件。命名方式与 Adjunction/Compose.v 相同，它与 Theory/Adjunction.v 的关系完全一致。

先前技术，已测量——计数随标准移动，因此标准已说明。搜索裸词 [AdjointEquivalence]（两侧为词边界）在基础提交中返回五个文件，其声明包括一个：Adjunction/FullFaithful.v（仅文字描述）、Structure/Monoidal/Dual.v、Construction/Subcategory/Dense.v 和 Theory/Equivalence/Strict.v（包含内容），以及 Theory/Equivalence/Adjoint.v 本身。搜索与作为子字符串相同的字符串返回八个（再次包括声明的文件），额外的三个是 Theory/Equivalence/Adjunction.v（散文）以及 Theory/Equivalence/Creation.v 和 Theory/Equivalence/Limit.v，它们使用 [AdjointEquivalence_swap_adjunction]，但从未命名该类。根据任一标准，结论都是相同的：
   它们都不构成两个伴随等价，也都没有显示出恒等等价 —— 字符串 [AdjointEquivalence_Compose]、
   [AdjointEquivalence_Id] 和 [AdjointEquivalence Id] 仅在此模块及其探针中出现，其他地方未出现。相比之下，逆元已经存在：[AdjointEquivalence_swap]
   （Theory/Equivalence/Adjoint.v），其基础交换伴随为 [AdjointEquivalence_swap_adjunction]。它在下文被引用，并且未重新构建。

路线，以及为什么它不是目录条目建议的那条路线。
该条目建议通过细化来解读复合排除条款(a):

等价转伴随等价
       （范畴等价_组合
          （伴随等价转等价 A）
          （伴随等价转等价 B））

那条路线在这里构建为 [AdjointEquivalence_Compose_via_equivalence]，并且它的一个前提出通过测量得到确认：复合等价的拟逆在数学上正好是两个拟逆的复合，因为 [Build_EquivalenceOfCategories] 的 [quasi_inverse] 根据定义是它的第二个参数，所以常量正好在类型 [AdjointEquivalence (F' o F) (U o U')] 处展开，无需传输和强制转换。然而，它并未被视为定义，因为它产生的复合体不会化简，而直接路径的复合体会化简。有一个经过测量而非仅仅主张的理由：[EquivalenceOfCategories_Compose]（Bundled.v）的两个单元被 [Qed] 封闭，所以精炼的伴随转换被一个不透明的常数遮蔽。以其力度来理解——这是一个理由，而不是孤立的情况。一次外部实验逐字重建那两个单元，但运行了 [Defined]，并且对精炼单元进行归一化仍然在转置同构本身时停止，比一个构造函数更进一步；因此，[Qed] 单元并未被证明是唯一的阻塞因素，并且没有实验使这两条路径一致。直接路线——取两个基础伴随中的 [Adjunction_Compose] 并提供两个可逆性条款——可以简化，这就是下面严格回读记录的内容。这两个复合是不同的：它们的整体记录、基础伴随及其单位组件在 [eq_refl]（Test/ProbeAdjointCompose379.v 的负 1-3）处均被拒绝。没有声明关于两者在 [~] 之前是否一致的任何情况，无论哪一方向：在一个固定的伴侣对上的伴随结构不一定是唯一的，这里既没有提供证明，也没有提供反例。

交付的内容，以及成绩。

(A) [IsIsomorphism]的可逆性演算，四个常数：[IsIso_id]、[IsIso_along]（沿[~]传输）、[IsIso_comp]（复合）和[IsIso_fmap]（函子像）。[IsIso_fmap]
       重复了 [fmap_IsIsomorphism]，该项已存在于
       Construction/Reflective/Idempotent.v 中，其语句与 [f] 的显式性和宇宙注解的不同之外基本相同（捐赠者将 [f] 作为显式且不携带任何宇宙绑定器），证明本质上也相同。在一次测量上，它是被重述而不是被要求的：该模块在项目内的传递闭包是33，要求它将使整个幂等单子和反射子范畴的开发落后于使用该文件的每一个消费者。另外三个在树内没有对应项，通过 NAME 对每个 .v 文件以及 SHAPE 来衡量：在此文件之外没有声明头部声明标识、复合体或沿 [~] 传输的 [IsIsomorphism]，唯一的 [fmap] 形状是已确认的 [fmap_IsIsomorphism]。

(B) [AdjointEquivalence_Compose A B ：
          AdjointEquivalence (F' o F) (U o U')].
       它的底层伴随是 [Adjunction_Compose]，在 [eq_refl] ([AdjointEquivalence_Compose_adjunction]) 的两个组成部分上，
       并且它的两个可逆性条款分别是 [eq_refl] ([..._unit_clause], [..._counit_clause]) 上的命名条款。

(C) 比较引理——条款(b)的重点，以及单纯存在陈述会遗漏的内容。两个等级被区分开，因为它们不同：

* [AdjointEquivalence_Compose_unit] 和 [_counit] 陈述了 Mac-Lane 的胡须公式，单位 ~ fmap[U] eta' o eta 和余单位 ~ epsilon' o fmap[F'] epsilon。这些是 [~]，而不是 [eq_refl]：它们是其给体 [Adjunction_Compose_unit] 和 [Adjunction_Compose_counit] 的应用，两者都是 [Qed] 的推论，从 [to_adj_unit] / [from_adj_counit] 证明，这是一个真正的重写步骤，而不是一个转换。两者都由 [:=] 提供，没有策略，因为复合体的附加就是供体本身。

* [AdjointEquivalence_Compose_unit_transpose] 和 [_counit_transpose] 在 [eq_refl] 处成立：复合的单位就是 B 的单位的 A-转置，复合的余单位就是 A 的余单位的 B-逆转置。这是带须形式严格的表现，它只与 [~] 相等，也是直接路径值得采用的原因。

* [AdjointEquivalence_Compose_unit_inverse] 和 [_counit_inverse] 在 [eq_refl] 读取了双面的逆：复合单位的逆是 eta^-1 o fmap[U] (eta'^-1)，复合余单位的逆是 fmap[F'] (epsilon^-1) o epsilon'^-1。

(D) [AdjointEquivalence_Id C : AdjointEquivalence Id[C] Id[C]]，在 [Adjunction_Id] 上（它是 Instance/Adjoints.v 的 [adj_id] 被重用，根据 Adjunction/Compose.v）。它的伴随函数回读于 [eq_refl]；它的单位元和余单位元是 [~]，即同一性，从 [Adjunction_Id_unit] / [_counit] 继承而来。

(E) 群族定律，是通过测量而非假设得出的，其结果比“无法表述”更精细。在范畴的层面上，结合律和单位律方程甚至没有良好的类型：函子 [Compose] 精确上并非结合的，[Id] 也不是它的严格单位（伴随/Pare.v 测量），因此 [AdjointEquivalence (F'' o (F' o F)) ((U o U') o U'')] 和 [AdjointEquivalence ((F'' o F') o F) (U o (U' o U''))] 是不同的类型。这两种形状在探针中都被固定为 TYPING 负值，并且没有发明任何传输。但这两种括号的 OBJECT 操作在定义上是一致的，所以单位和余单位存在可转换类型，并且在这里这些定律精确成立：[AdjointEquivalence_Compose_assoc_unit]、[_assoc_counit]、[_id_left_unit]、[_id_left_counit]、[_id_right_unit] 和 [_id_right_counit] 都是 [eq_refl]。所以，三元组组合/同一性/逆元可以一起使用，并且与它们相关的定律完全成立，只要类型理论允许它们被陈述。

(F) 非空性，并且它在重要的轴上不退化。[indiscrete_square] 由 Theory/Equivalence/Strict.v 的 [indiscrete_adjoint_equivalence] 与该等价自身组成 [AdjointEquivalence_swap]，给出了 [Indiscrete bool] 与其自身的伴随等价，其两个函子都是 [IndT o Erase (Indiscrete bool)]。复合函子 MOVES 一个对象：[indiscrete_square_moves] 在 [false] 通过 [eq_refl] 计算其值到 [true]，并且 [indiscrete_square_not_id] 通过 [discriminate] 结束，所以该复合函子不是恒等伴随等价——实际上它甚至没有这种类型，被标记为 TYPING 否定。因此，[false] 处的单位在两个不同的对象之间运行。披露：[Indiscrete] 的同构族忽略了其端点——Instance/Discrete/Reconstruct.v 声明了 [hom := fun _ _ => unit]，标准库中的 [unit : Set]，这也是见证块的 [Set] 来源——因此那里每个同构集都是单例，并且在形态层面的陈述“[false] 处的单位是恒等”是类型正确且真实的，在 [eq_refl] 处成立，而不仅仅在 [~] 处成立；因此形态层面的非退化性陈述不可用。这是陷阱
       Theory/Equivalence/Strict.v 为它自己的余单位记录；
       诚实的非退化性是在对象层面的，而这正是被证明的内容。

未交付的内容。没有对逆的直接构造：三人组的第三个成员是 [AdjointEquivalence_swap]，被引用，并且根据 Theory/Equivalence/Strict.v 的测量，其单位不会简化（它是通过 [EquivalenceOfCategories_sym] 和 [Equivalence_to_AdjointEquivalence] 构建的）；未尝试手工构建调换后可简化的情况。没有在 [~] 处对直接复合和精炼路径进行比较。没有关于复合的唯一性声明。没有范畴的范畴以及伴随等价，所以群族定律没有被打包成结构。沿着任一伴随的自然同构没有伴随等价的传递。没有二范畴的理解，也没有与 Theory/Bicategory/Adjunction.v 的关系。在一对伴随等价的三个真正不同的范畴上没有见证。

宇宙，同时从绑定器和块中测量。可逆性演算的四个常数是自由的：[IsIso_along@{o h p}] 有一个空的方程块，只携带 [Category] 自己的 [h <= p]，并且 [IsIso_fmap@{xo xh xp yo yh yp u}] 保持两个范畴的六个层级分开，仅有 [Functor] 自己的界限。那是明确绑定器的行为，而且是经过测量的，而非假设的：未注释的书面形式同样使这些主体最小化，以便用证明识别它们，然后在一个声明为分开的两个层次的范畴中被拒绝，而带注释的形式被接受（探针在恰好那些层次上将所有四个作为控制进行检查）。

结合词汇下游的一切确实通过证明将 hom 与 [Category@{u u0 u0}] 在 BINDER 中识别出来，而在任何约束块中都没有这样的等式，这是单独阅读一个块时容易犯的错误陷阱。三个供体正在被探测，第一个很容易被忽略：恒等函子 [Id] 会自行强制它，因此一个探测器如果将 [Id[Cu] 写入 [Adjunction]，测量的是 [Id] 而不是 [Adjunction]——区分性的控制是同一个范畴的任意自函子，它会被接受，所以 [Functor] 不是供体。对两个这样的端函子进行探测，以便在命令中不会出现 [Id]，[Adjunction] 是一个独立的供体；而 [AdjointEquivalence] 是第三个，不能与 [Adjunction] 分开测试，其第一个字段是 [F -| U]，因此这两个不是独立的。[AdjointEquivalence_Id] 同时可达到 [Id] 和 [Adjunction]，其负极未隔离任何一方。

该复合体还携带了 [u0 = u2]、[u0 = u4]、[u2 = u4]——这三类的同源和证明宇宙合并为一个，所有三种对象宇宙都是自由的——这仅仅由于函子在任何伴随关系形成之前在两个方向上的存在而被强制，固定为其自身的可形成性负值。[AdjointEquivalence_Id] 在其块中完全不携带任何方程。证人区块携带 [Set]，通过 Theory/Equivalence/Strict.v 从 Instance/One.v 和 Instance/Discrete/Reconstruct.v 继承；没有任何部分被声明为不可避免。

闭包，测量为项目内 .vo 依赖的传递闭包，不包括此文件。39 个模块；26 个模块删除了见证部分的三个 requires，因此非空的见证成本为 13。所有 13 个都是通过 [Theory.Equivalence.Strict] 引入（39 个与删除其边的 32 个相比）；[Instance.One] 和 [Instance.Discrete.Reconstruct] 在此基础上不产生额外成本，并且仅为了将名称 [Erase] 和 [Indiscrete] 引入作用域而需要。根据一般理论的要求，没有任何一个单独的元素本身需要任何成本——单独丢弃其中任何一个，其闭包仍为39，因为每个元素都包含在其他元素的闭包中——与捐赠者自己的数据分别为22（Theory/Equivalence/Adjoint.v）、20（Adjunction/Compose.v）和20（Theory/Equivalence/Bundled.v）相比。探针的闭包为40。

透明度。文件中有四行 [Defined.]，[IsIso_comp] 和 [IsIso_fmap] 各有两个义务；它们都不是承重的，通过在一个测试副本中将所有四行翻转为 [Qed] 来衡量，在该副本中，文件仍然可以编译，并且每个 [eq_refl] 的回读数据都保持完整。它们是按照内部约定的 [Defined]，而不是出于实际需要——每个都是一个法律字段，数据字段是内联提供的。文件中的一个 [Qed] 是 [indiscrete_square_not_id]，不会产生任何数据。

注册。根据 Theory/Equivalence.v 和 Theory/Equivalence/Adjoint.v，这里没有为实例解析注册任何内容：伴随等价是一组数据的选择，总是在使用时显式传递。
*)

(** ** An invertibility calculus for [IsIsomorphism] / ** [IsIsomorphism] 的可逆性演算 *)

Section IsoCalculus.

(*
The explicit universe binders are LOAD-BEARING: written unannotated,
   the same bodies minimize so as to identify X's hom and proof
   universes, and the four constants are then rejected at a category
   whose two levels are declared apart.  Annotated they carry only
   [Category]'s own [h <= p].

--------
显式宇宙绑定器是承重的：未注释地书写，同样的主体被最小化以便识别 X 的同构和证明宇宙，然后四个常数在一个声明为分开的两级范畴中被拒绝。注释后，它们只携带 [Category] 自身的 [h <= p]。
*)
Universes o h p.
Context {X : Category@{o h p}}.

(* The identity is invertible, in the predicate form. / 恒等映射是可逆的，以谓词形式表示。 *)
Program Definition IsIso_id {x : X} : IsIsomorphism (id[x]) := {|
  two_sided_inverse := id
|}.

(*
Invertibility transports along [~]: the inverse of the [~]-target
   inverts the source as well, both laws by rewriting with the given
   equation on the one side of the composite where it occurs.

--------
可逆性沿 [~] 传输：[~] 目标的逆也会逆转源，两条定律都是通过在复合体中其出现的一侧使用给定方程重写得出的。
*)
Definition IsIso_along {x y : X} {f g : x ~> y}
  (H : f ≈ g) (Hg : IsIsomorphism g) : IsIsomorphism f :=
  {| two_sided_inverse := @two_sided_inverse X x y g Hg
   ; is_right_inverse :=
       transitivity (compose_respects _ _ H _ _ (reflexivity _))
                    (@is_right_inverse X x y g Hg)
   ; is_left_inverse :=
       transitivity (compose_respects _ _ (reflexivity _) _ _ H)
                    (@is_left_inverse X x y g Hg) |}.

(*
A composite of invertible morphisms is invertible, with the inverses
   composed in the opposite order.  This is [iso_compose]
   (Theory/Isomorphism.v) read for the predicate rather than the
   bundled form.

--------
可逆态射的复合也是可逆的，其逆按照相反的顺序组合。这是 [iso_compose]（Theory/Isomorphism.v）为谓词形式而非捆绑形式所读取的。
*)
Program Definition IsIso_comp {x y z : X} {f : y ~> z} {g : x ~> y}
  (Hf : IsIsomorphism f) (Hg : IsIsomorphism g) : IsIsomorphism (f ∘ g) := {|
  two_sided_inverse := @two_sided_inverse X x y g Hg
                         ∘ @two_sided_inverse X y z f Hf
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite (comp_assoc g).
  rewrite (@is_right_inverse X x y g Hg), id_left.
  apply is_right_inverse.
Defined.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (@two_sided_inverse X y z f Hf)).
  rewrite (@is_left_inverse X y z f Hf), id_left.
  apply is_left_inverse.
Defined.

End IsoCalculus.

(*
A functor carries invertible morphisms to invertible morphisms.  This
   restates [fmap_IsIsomorphism] (Construction/Reflective/Idempotent.v);
   see the header for why it is restated rather than required.

--------
函子将可逆态射映射为可逆态射。 这重新表述了 [fmap_IsIsomorphism]（Construction/Reflective/Idempotent.v）；参见标题了解为什么是重新表述而不是要求。
*)
Program Definition IsIso_fmap@{xo xh xp yo yh yp +}
  {X : Category@{xo xh xp}} {Y : Category@{yo yh yp}} (G : X ⟶ Y) {x y : X}
  {f : x ~> y} (Hf : IsIsomorphism f) : IsIsomorphism (fmap[G] f) := {|
  two_sided_inverse := fmap[G] (@two_sided_inverse X x y f Hf)
|}.
Next Obligation.
  rewrite <- fmap_comp.
  rewrite (@is_right_inverse X x y f Hf).
  apply fmap_id.
Defined.
Next Obligation.
  rewrite <- fmap_comp.
  rewrite (@is_left_inverse X x y f Hf).
  apply fmap_id.
Defined.

(** ** The composite of two adjoint equivalences / ** 两个伴随等价的复合 *)

Section Compose.

Context {C D E : Category}.
Context {F : C ⟶ D} {U : D ⟶ C}.
Context {F' : D ⟶ E} {U' : E ⟶ D}.
Context (A : AdjointEquivalence F U).
Context (B : AdjointEquivalence F' U').

(*
The underlying adjunction of the composite: [Adjunction_Compose]
   (Adjunction/Compose.v) of the two underlying adjunctions.

--------
复合的基础伴随：[Adjunction_Compose]（Adjunction/Compose.v）由两个基础伴随组成。
*)
Definition adjoint_equivalence_compose_adj : (F' ◯ F) ⊣ (U ◯ U') :=
  Adjunction_Compose (@adj_equivalence _ _ _ _ A) (@adj_equivalence _ _ _ _ B).

(*
The composite's unit is invertible: transport along Mac Lane's
   whiskering formula, then compose the U-image of B's unit isomorphism
   with A's own.

--------
复合体的单位是可逆的：沿着 Mac Lane 的搅拌公式进行传输，然后将 B 的单位同构的 U-像与 A 本身的单位同构进行复合。
*)
Definition adjoint_equivalence_compose_unit_iso (x : C) :
  IsIsomorphism (@unit _ _ _ _ adjoint_equivalence_compose_adj x) :=
  IsIso_along
    (@Adjunction_Compose_unit _ _ _ _ _ _ _
       (@adj_equivalence _ _ _ _ A) (@adj_equivalence _ _ _ _ B) x)
    (IsIso_comp (IsIso_fmap U (@adj_equiv_unit_iso _ _ _ _ B (F x)))
                (@adj_equiv_unit_iso _ _ _ _ A x)).

(* Dually for the counit. / 对余单位也是如此。 *)
Definition adjoint_equivalence_compose_counit_iso (y : E) :
  IsIsomorphism (@counit _ _ _ _ adjoint_equivalence_compose_adj y) :=
  IsIso_along
    (@Adjunction_Compose_counit _ _ _ _ _ _ _
       (@adj_equivalence _ _ _ _ A) (@adj_equivalence _ _ _ _ B) y)
    (IsIso_comp (@adj_equiv_counit_iso _ _ _ _ B y)
                (IsIso_fmap F' (@adj_equiv_counit_iso _ _ _ _ A (U' y)))).

(* Mac Lane SIV.4 Exercise 2(b): adjoint equivalences compose. / Mac Lane SIV.4 练习 2(b)：伴随等价可以组合。 *)
Definition AdjointEquivalence_Compose :
  AdjointEquivalence (F' ◯ F) (U ◯ U') :=
  @Build_AdjointEquivalence C E (F' ◯ F) (U ◯ U')
    adjoint_equivalence_compose_adj
    adjoint_equivalence_compose_unit_iso
    adjoint_equivalence_compose_counit_iso.

(** *** Strict readbacks of the three fields / *** 对这三个领域的严格回读 *)

Example AdjointEquivalence_Compose_adjunction :
  @adj_equivalence _ _ _ _ AdjointEquivalence_Compose
    = Adjunction_Compose (@adj_equivalence _ _ _ _ A)
                         (@adj_equivalence _ _ _ _ B) := eq_refl.

Example AdjointEquivalence_Compose_unit_clause (x : C) :
  @adj_equiv_unit_iso _ _ _ _ AdjointEquivalence_Compose x
    = adjoint_equivalence_compose_unit_iso x := eq_refl.

Example AdjointEquivalence_Compose_counit_clause (y : E) :
  @adj_equiv_counit_iso _ _ _ _ AdjointEquivalence_Compose y
    = adjoint_equivalence_compose_counit_iso y := eq_refl.

(** *** The comparison with the two constituents / *** 与这两个成分的比较 *)

(*
Mac Lane's whiskering formula for the unit, at [~].  Its donor is a
   [Qed] corollary proved from [to_adj_unit], so this grade is the
   donor's; the strict form is [AdjointEquivalence_Compose_unit_transpose]
   below.

--------
Mac Lane 关于单位的胡须公式，在 [~]。它的供体是从 [to_adj_unit] 推导出的 [Qed] 推论，因此这个等级是供体的；严格形式如下 [AdjointEquivalence_Compose_unit_transpose]。
*)
Definition AdjointEquivalence_Compose_unit (x : C) :
  @unit _ _ _ _ (@adj_equivalence _ _ _ _ AdjointEquivalence_Compose) x
    ≈ fmap[U] (@unit _ _ _ _ (@adj_equivalence _ _ _ _ B) (F x))
        ∘ @unit _ _ _ _ (@adj_equivalence _ _ _ _ A) x :=
  @Adjunction_Compose_unit _ _ _ _ _ _ _
    (@adj_equivalence _ _ _ _ A) (@adj_equivalence _ _ _ _ B) x.

Definition AdjointEquivalence_Compose_counit (y : E) :
  @counit _ _ _ _ (@adj_equivalence _ _ _ _ AdjointEquivalence_Compose) y
    ≈ @counit _ _ _ _ (@adj_equivalence _ _ _ _ B) y
        ∘ fmap[F'] (@counit _ _ _ _ (@adj_equivalence _ _ _ _ A) (U' y)) :=
  @Adjunction_Compose_counit _ _ _ _ _ _ _
    (@adj_equivalence _ _ _ _ A) (@adj_equivalence _ _ _ _ B) y.

(*
The strict form: the composite's unit IS A's forward transpose of B's
   unit, and the composite's counit IS B's inverse transpose of A's
   counit.  Both by conversion.

--------
严格形式：复合体的单位是A的余转置的B的单位，复合体的余单位是B的逆转置的A的余单位。两者都通过转换。
*)
Example AdjointEquivalence_Compose_unit_transpose (x : C) :
  @unit _ _ _ _ (@adj_equivalence _ _ _ _ AdjointEquivalence_Compose) x
    = to (@adj _ _ _ _ (@adj_equivalence _ _ _ _ A) x (U' (F' (F x))))
         (@unit _ _ _ _ (@adj_equivalence _ _ _ _ B) (F x)) := eq_refl.

Example AdjointEquivalence_Compose_counit_transpose (y : E) :
  @counit _ _ _ _ (@adj_equivalence _ _ _ _ AdjointEquivalence_Compose) y
    = from (@adj _ _ _ _ (@adj_equivalence _ _ _ _ B) (F (U (U' y))) y)
           (@counit _ _ _ _ (@adj_equivalence _ _ _ _ A) (U' y)) := eq_refl.

(* The two-sided inverses, read back on the nose. / 双边逆元，逐字读回去。 *)
Example AdjointEquivalence_Compose_unit_inverse (x : C) :
  @two_sided_inverse _ _ _ _
    (@adj_equiv_unit_iso _ _ _ _ AdjointEquivalence_Compose x)
    = @two_sided_inverse _ _ _ _ (@adj_equiv_unit_iso _ _ _ _ A x)
        ∘ fmap[U] (@two_sided_inverse _ _ _ _
                     (@adj_equiv_unit_iso _ _ _ _ B (F x))) := eq_refl.

Example AdjointEquivalence_Compose_counit_inverse (y : E) :
  @two_sided_inverse _ _ _ _
    (@adj_equiv_counit_iso _ _ _ _ AdjointEquivalence_Compose y)
    = fmap[F'] (@two_sided_inverse _ _ _ _
                  (@adj_equiv_counit_iso _ _ _ _ A (U' y)))
        ∘ @two_sided_inverse _ _ _ _
            (@adj_equiv_counit_iso _ _ _ _ B y) := eq_refl.

(** *** The refinement route, and how it compares / *** 精炼路线，以及它的比较 *)

(*
The route the catalog entry proposes: refine the composite of the two
   induced equivalences of categories.  Its premise checks out -- the
   type below is the same one [AdjointEquivalence_Compose] inhabits, with
   no transport -- but it is a different adjoint equivalence, rejected at
   [eq_refl] against the direct one on the whole record, on the
   underlying adjunction and on the unit components (negatives 1-3 of
   Test/ProbeAdjointCompose379.v).

--------
目录条目提出的路线：精炼由两个诱导的范畴等价构成的复合。它的前提是成立的——下面的类型与 [AdjointEquivalence_Compose] 所处的类型相同，没有转换——但它是一个不同的伴随等价，在 [eq_refl] 中被拒绝，对于整个记录的直接等价、基础伴随以及单位分量（Test/ProbeAdjointCompose379.v 的负数 1-3）。
*)
Definition AdjointEquivalence_Compose_via_equivalence :
  AdjointEquivalence (F' ◯ F) (U ◯ U') :=
  Equivalence_to_AdjointEquivalence
    (EquivalenceOfCategories_Compose
       (AdjointEquivalence_to_Equivalence A)
       (AdjointEquivalence_to_Equivalence B)).

(*
Its quasi-inverse is the composite of the two right adjoints on the
   nose, which is what makes the type above the right one.

--------
它的准逆是两个右伴随的组合，这正是使上面的类型成为右侧类型的原因。
*)
Example AdjointEquivalence_Compose_via_quasi_inverse :
  @quasi_inverse C E (F' ◯ F)
    (EquivalenceOfCategories_Compose
       (AdjointEquivalence_to_Equivalence A)
       (AdjointEquivalence_to_Equivalence B)) = U ◯ U' := eq_refl.

End Compose.

(** ** The identity adjoint equivalence / ** 恒等伴随等价 *)

Section Identity.

Context {C : Category}.

(*
Id[C] is adjoint-equivalent to itself, over [Adjunction_Id]
   (Adjunction/Compose.v, itself Instance/Adjoints.v's [adj_id]
   reused).  Both invertibility clauses transport along the identity.

--------
Id[C] 在 [Adjunction_Id] 上与自身伴随等价（Adjunction/Compose.v，本身 Instance/Adjoints.v 的 [adj_id] 重用）。两个可逆性条款沿着恒等映射传递。
*)
Definition AdjointEquivalence_Id : AdjointEquivalence Id[C] Id[C] :=
  @Build_AdjointEquivalence C C Id[C] Id[C] (@Adjunction_Id C)
    (fun x => IsIso_along (@Adjunction_Id_unit C x) IsIso_id)
    (fun x => IsIso_along (@Adjunction_Id_counit C x) IsIso_id).

Example AdjointEquivalence_Id_adjunction :
  @adj_equivalence _ _ _ _ AdjointEquivalence_Id = @Adjunction_Id C := eq_refl.

Definition AdjointEquivalence_Id_unit (x : C) :
  @unit _ _ _ _ (@adj_equivalence _ _ _ _ AdjointEquivalence_Id) x ≈ id[x] :=
  @Adjunction_Id_unit C x.

Definition AdjointEquivalence_Id_counit (x : C) :
  @counit _ _ _ _ (@adj_equivalence _ _ _ _ AdjointEquivalence_Id) x ≈ id[x] :=
  @Adjunction_Id_counit C x.

(* The two-sided inverses of the identity's clauses are the identity. / 恒等式条款的双面逆是恒等式。 *)
Example AdjointEquivalence_Id_unit_inverse (x : C) :
  @two_sided_inverse _ _ _ _
    (@adj_equiv_unit_iso _ _ _ _ AdjointEquivalence_Id x) = id[x] := eq_refl.

Example AdjointEquivalence_Id_counit_inverse (x : C) :
  @two_sided_inverse _ _ _ _
    (@adj_equiv_counit_iso _ _ _ _ AdjointEquivalence_Id x) = id[x] := eq_refl.

End Identity.

(** ** The inverse: cited, not rebuilt / ** 相反：被引用，而不是重建 *)

Section Inverse.

Context {C D : Category}.
Context {F : C ⟶ D} {U : D ⟶ C}.
Context (A : AdjointEquivalence F U).

(*
Theory/Equivalence/Adjoint.v already supplies the third member of
   the trio, [AdjointEquivalence_swap A : AdjointEquivalence U F], and
   its underlying swapped adjunction.  The two agree on the nose,
   the latter being defined as the former's adjunction field.  Nothing
   is rebuilt here; the readback records that the trio
   composition/identity/inverse is available together.

   DISCLOSED: [AdjointEquivalence_swap] is built through
   [EquivalenceOfCategories_sym] and [Equivalence_to_AdjointEquivalence],
   so -- by the measurement Theory/Equivalence/Strict.v records for the
   same chain -- its unit does not reduce.  A direct swap whose
   transposes reduce is not attempted here.

--------
Theory/Equivalence/Adjoint.v 已经提供了三者中的第三个成员 [AdjointEquivalence_swap A : AdjointEquivalence U F] 及其底层的交换伴随。两者完全一致，后者被定义为前者的伴随域。这里没有重新构建任何内容；回读记录显示三元组的组合/恒等/逆同时可用。

披露：[AdjointEquivalence_swap] 是通过 [EquivalenceOfCategories_sym] 和 [Equivalence_to_AdjointEquivalence] 构建的，因此——根据 Theory/Equivalence/Strict.v 对同一链的记录——其单位不会化简。这里没有尝试直接交换其转置会化简的方法。
*)
Example AdjointEquivalence_swap_readback :
  @adj_equivalence _ _ _ _ (AdjointEquivalence_swap A)
    = AdjointEquivalence_swap_adjunction A := eq_refl.

End Inverse.

(** ** The groupoid laws, as far as they are statable / ** 作为可表述的范围内，群族定律 *)

Section Laws.

Context {C1 C2 C3 C4 : Category}.
Context {F1 : C1 ⟶ C2} {U1 : C2 ⟶ C1}.
Context {F2 : C2 ⟶ C3} {U2 : C3 ⟶ C2}.
Context {F3 : C3 ⟶ C4} {U3 : C4 ⟶ C3}.
Context (A : AdjointEquivalence F1 U1).
Context (B : AdjointEquivalence F2 U2).
Context (G : AdjointEquivalence F3 U3).

(*
The two bracketings of a triple composite have DIFFERENT types --
   [Compose] of functors is not associative on the nose -- so no equation
   between them is well formed, and none is invented; the shape is
   pinned as a typing negative in the probe.  What IS well formed is the
   comparison of their units and counits, because the two bracketings
   have definitionally equal object actions; and there the law holds by
   conversion.

--------
一个三重复合的两种括号方式具有不同的类型 —— functor 的 [Compose] 并不是严格结合的 —— 因此它们之间没有一个方程是良构的，也没有被发明出来；这个形状在探针中作为类型负固定。良构的部分是比较它们的单位和余单位，因为这两种括号方式在对象作用上在定义上是相等的；在那里定律通过转换成立。
*)

Definition assoc_left :=
  AdjointEquivalence_Compose (AdjointEquivalence_Compose A B) G.

Definition assoc_right :=
  AdjointEquivalence_Compose A (AdjointEquivalence_Compose B G).

Example AdjointEquivalence_Compose_assoc_unit (x : C1) :
  @unit _ _ _ _ (@adj_equivalence _ _ _ _ assoc_left) x
    = @unit _ _ _ _ (@adj_equivalence _ _ _ _ assoc_right) x := eq_refl.

Example AdjointEquivalence_Compose_assoc_counit (y : C4) :
  @counit _ _ _ _ (@adj_equivalence _ _ _ _ assoc_left) y
    = @counit _ _ _ _ (@adj_equivalence _ _ _ _ assoc_right) y := eq_refl.

(*
The identity laws, at the same two grades: not statable at the class
   (again pinned in the probe), on the nose at the unit and counit.

--------
恒等律，在同样的两个层次上：在类上不能表述（在探针中再次被固定），在单位和余单位上则准确无误。
*)

Example AdjointEquivalence_Compose_id_left_unit (x : C1) :
  @unit _ _ _ _
    (@adj_equivalence _ _ _ _
       (AdjointEquivalence_Compose (@AdjointEquivalence_Id C1) A)) x
    = @unit _ _ _ _ (@adj_equivalence _ _ _ _ A) x := eq_refl.

Example AdjointEquivalence_Compose_id_left_counit (y : C2) :
  @counit _ _ _ _
    (@adj_equivalence _ _ _ _
       (AdjointEquivalence_Compose (@AdjointEquivalence_Id C1) A)) y
    = @counit _ _ _ _ (@adj_equivalence _ _ _ _ A) y := eq_refl.

Example AdjointEquivalence_Compose_id_right_unit (x : C1) :
  @unit _ _ _ _
    (@adj_equivalence _ _ _ _
       (AdjointEquivalence_Compose A (@AdjointEquivalence_Id C2))) x
    = @unit _ _ _ _ (@adj_equivalence _ _ _ _ A) x := eq_refl.

Example AdjointEquivalence_Compose_id_right_counit (y : C2) :
  @counit _ _ _ _
    (@adj_equivalence _ _ _ _
       (AdjointEquivalence_Compose A (@AdjointEquivalence_Id C2))) y
    = @counit _ _ _ _ (@adj_equivalence _ _ _ _ A) y := eq_refl.

End Laws.

(** ** Non-vacuity / ** 非空性 *)

(*
Theory/Equivalence/Strict.v supplies a genuine adjoint
   equivalence between the terminal category and [Indiscrete bool], via
   Mac Lane SIV.4 Exercise 3.  Swapping it and composing gives an
   adjoint equivalence of [Indiscrete bool] with itself whose two
   functors are both [IndT o Erase (Indiscrete bool)].

--------
Theory/Equivalence/Strict.v 提供了终端范畴与 [Indiscrete bool] 之间的真正伴随等价，通过 Mac Lane SIV.4 练习 3。交换它并进行复合会得到 [Indiscrete bool] 与其自身的伴随等价，其两个函子都是 [IndT o Erase (Indiscrete bool)]。
*)

Definition indiscrete_swap :
  AdjointEquivalence (Erase (Indiscrete bool)) IndT :=
  AdjointEquivalence_swap indiscrete_adjoint_equivalence.

Definition indiscrete_square :
  AdjointEquivalence (IndT ◯ Erase (Indiscrete bool))
                     (IndT ◯ Erase (Indiscrete bool)) :=
  AdjointEquivalence_Compose indiscrete_swap indiscrete_adjoint_equivalence.

(* The composite is not an identity: its functor moves an object. / 复合不是恒等式：它的函子移动一个对象。 *)
Example indiscrete_square_moves :
  (IndT ◯ Erase (Indiscrete bool)) false = true := eq_refl.

Theorem indiscrete_square_not_id :
  (IndT ◯ Erase (Indiscrete bool)) false = false → False.
Proof. discriminate. Qed.

(*
Consequently the composite's unit at [false] connects two DIFFERENT
   objects: its codomain is [true].  Recorded on the objects, because
   [Indiscrete]'s hom family ignores its endpoints -- see the header.

--------
因此，复合体在 [false] 的单元连接两个不同的对象：它的陪域是 [true]。在对象上记录，因为 [Indiscrete] 的 hom 集族忽略其端点——参见标题。
*)
Example indiscrete_square_unit_codomain :
  (IndT ◯ Erase (Indiscrete bool))
    ((IndT ◯ Erase (Indiscrete bool)) false) = true := eq_refl.

(*
The underlying adjunction of the witness is the composite of the two
   constituents', on the nose.

--------
见证的基本伴随是两个组成部分的复合，准确无误。
*)
Example indiscrete_square_adjunction :
  @adj_equivalence _ _ _ _ indiscrete_square
    = Adjunction_Compose
        (@adj_equivalence _ _ _ _ indiscrete_swap)
        (@adj_equivalence _ _ _ _ indiscrete_adjoint_equivalence) := eq_refl.
