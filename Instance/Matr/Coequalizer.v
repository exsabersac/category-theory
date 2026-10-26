(*
 [Coq.QArith.QArith] MUST precede [Category.Lib]: it exports an [equiv]
 that otherwise shadows Lib/Setoid.v's, and every [Proper] statement
 reachable from here then fails to elaborate.  This is the import-order
 gotcha Instance/FdVect.v records in its own header and
 Instance/Matr/Elimination.v measured again; the ℚ witness at the end
 of this file is why the ordering matters here too. 

 --------
 [Coq.QArith.QArith] 必须位于 [Category.Lib] 之前：它导出一个 [equiv]，否则会覆盖 Lib/Setoid.v 的同名内容，并且此处可达的每个 [Proper] 语句随后都会无法展开。这是导入顺序的陷阱，Instance/FdVect.v 在其自己的头文件中记录了这种情况，而 Instance/Matr/Elimination.v 则再次进行了测量；本文件末尾的 ℚ 见证也说明了顺序在这里的重要性。
*)
Require Import Coq.QArith.QArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Matr.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Field.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Instance.Parallel.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Instance.Matr.Elimination.
Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(*
   * * Coequalizers of matrices

   Mac Lane, “Categories for the Working Mathematician”, 2nd ed., §III.3
   Exercise 3 [maclane:III.3:ex3] asks for the coequalizer of a parallel
   pair of matrices.  This file is the CATEGORICAL half of that
   exercise.  The linear-algebra half is Instance/Matr/Elimination.v,
   which is CONSUMED here and neither extended nor re-proved: every
   proof below is one of that file's terms handed to a record field of
   Structure/Coequalizer.v, and this file contains no summation
   argument, no pivot, and no induction of its own.

   WHAT A COEQUALIZER OF MATRICES IS.  For a parallel pair A, B : n ⇉ m
   — two m × n matrices — a map h : m ~> z coforks the pair exactly when
   h·A ≈ h·B, which by Elimination.v's [mat_mul_sub_zero_iff] holds
   exactly when h·(A − B) ≈ 0, that is, exactly when every row of h lies
   in the LEFT NULL SPACE of A − B.  So a universal coforking map is a
   matrix E whose rows are a BASIS of that space: spanning is existence
   of the factorization, linear independence is its uniqueness.  The
   coequalizer OBJECT is then the number of rows of E, the dimension of
   that null space.  NO RANK FUNCTION IS DEFINED, neither here nor in
   Elimination.v, so the familiar reading “k = m − rank (A − B)” is
   neither stated nor proved anywhere in this development; it appears in
   this sentence and nowhere else.

   ORIENTATION.  Inherited verbatim from Instance/Matr.v, which follows
   Mac Lane: an arrow n ~> m of [Matr R] is an m × n matrix, and
   composition is the matrix product with no transposition.  Taking
   x := n, y := m, f := A and g := B, the record of
   Structure/Coequalizer.v asks for an object q := k and a map
   e : y ~> q, which is a k × m matrix E; its [cofork] field
   [e ∘ f ≈ e ∘ g] IS E·A ≈ E·B; a coforking h : y ~> z is a z × m
   matrix; and the mediator u : q ~> z is a z × k matrix whose triangle
   [u ∘ e ≈ h] reads u·E ≈ h.  Those are exactly the four shapes
   Elimination.v's [left_null_basis] produces.

   THE HANDOFF IS PURE CONVERSION, and that was MEASURED rather than
   assumed.  Every statement below is written in the category's own
   vocabulary — [∘] and [≈[Matr K]] — while every proof of a GENERAL
   result, that is every one of the twelve constants of the section
   below, is an Elimination.v term supplied by [:=] with NO tactic.
   (The file does contain eleven tactic scripts, all of them in the two
   witness blocks at the end, where concrete matrices are discriminated;
   the section itself has none.)  There is NO [change] and NO transport
   anywhere in the file, in either part.  What makes this work is that
   Elimination.v identified its own vocabulary with the category's by
   [eq_refl] ([matrix_is_hom]; [mat_mul_is_compose], whose object
   arguments run in the order (c, b, a); [mat_id_is_id]; and
   [mat_equiv_is_homset_equiv], the last recording that its [Setoid]
   instance on matrices IS [Matr K]'s hom-setoid rather than the
   pointwise one [fun_setoid] would otherwise supply).  That instance is
   [#[local]] to Elimination.v, so it is not in scope here — and it is
   not needed, because this file names no bare [≈] on matrices at all.

   THE DECIDABILITY HYPOTHESIS, AND WHY IT IS FORCED.  The hypothesis
   [Kdec] below is not a convenience.  Producing the coequalizing map
   means running elimination, and elimination has to DECIDE whether a
   pivot vanishes, while the class it runs over supplies no such
   decision: [FieldObject] (Instance/FdVect.v) carries [field_ring],
   [field_comm], [field_one_neq_zero], a TOTAL [finv], [finv_respects]
   and [finv_l] — and [finv_l] is GUARDED by [x ≉ 0], so the inverse law
   is unusable until non-vanishing has been established, which is the
   very thing at issue.  Over an abstract setoid carrier [≈] is not
   decidable and the value of [finv] at zero is junk.  The hypothesis is
   therefore carried as explicit DATA in exactly the shape
   Instance/Field.v's [field_dec_stable] takes, and Elimination.v's
   [F2_dec_inhabits] and [Q_dec_inhabits] record BY ASCRIPTION that
   [F2_Field_dec] and [Q_Field_dec] inhabit it, so it is the tree's own
   notion and not a new one.  THE CONSEQUENCE FOR THIS FILE is that
   [Matr_HasCoequalizers] is a plain [Definition] taking the decider as
   an argument and is deliberately NOT registered as a global
   [Instance]: typeclass resolution has no way to produce a decider for
   an abstract field, and registering a hint that can never fire would
   perturb the database for nothing.  A consumer writes
   [Matr_HasCoequalizers K Kdec] and supplies the decider by hand.

   THE RIG CONSTRAINT.  Instance/Matr.v is stated over a RIG, and
   deliberately so: the category laws need associativity, units,
   distributivity and annihilation, and never subtraction.  A
   coequalizer does need subtraction — the passage from the two-matrix
   problem h·A ≈ h·B to the one-matrix problem h·(A − B) ≈ 0 is the
   whole bridge, and it spends [ring_neg]; the pivot step spends [finv]
   on top of that.  The base of this file is therefore a FIELD, and
   NOTHING here says anything about [Matr R] for a bare rig R.  In
   particular nothing is claimed about Awodey's
   [Matr_N := Matr Nat_Rig] (Instance/Matr.v), where A − B does not
   exist: whether that category has coequalizers is a different
   question, and it is not addressed.

   MEASURED STRENGTHS, strict first.  [eq_refl] was attempted before any
   [≈] was accepted, and the artifacts were arranged so that the strict
   form would be available at all: [matr_coeq_obj], [matr_coeq_map] and
   [matr_coeq_desc] are supplied by [:=] rather than by a tactic script
   closed with [Qed], so the object, the map and the [coeq_desc] field
   of the delivered record all REDUCE.  Closing by [eq_refl] at
   [F2_Field]: the coequalizer object of the worked pair (1) and both
   entries of its coequalizing map; the common composite E·A; the
   MEDIATOR extracted from the [coeq_desc] field of the delivered
   record — that last is the one that would have been lost had
   [matr_coeq_desc] been a [Qed] lemma; and the objects of three
   further pairs, pinning k = m at a pair with itself (where the map is
   2 x 2, so it has FOUR entries; two of them are pinned here and all
   four are the identity matrix's -- an earlier draft said “both”,
   which is right for the 1 x 2 map of the worked pair and wrong here),
   k = 0 at an invertible difference, and a second non-degenerate
   k = 2 at m = 3.  At [Q_Field] the object, both entries −2 and 1 of
   the coequalizing map, and both sides of the cofork equation (each
   −1) close by [eq_refl] as well, the rational arithmetic reducing on
   closed input.  Also strict: [matr_IsEqualizer_op] IS
   Structure/Pullback/Reduction.v's [IsEqualizer_op_of_IsCoequalizer]
   applied to the record, so that bridge is definitional at this
   instantiation and not merely available.

   FIVE STRICT ATTEMPTS WERE MADE AND REFUTED.  Each was checked by
   removing the failure marker and confirming a genuine CONVERSION
   failure (each reported “cannot unify”), and each is paired with a
   positive control that succeeds at the same arguments; none is a
   universe or elaboration artifact.  They are recorded here rather
   than as probes, this file carrying no probe section.
   (i) [matr_coeq_map F2_Field f2_dec coeq_f2_A coeq_f2_A
   = mat_id F2_Field 2] — at a pair with itself the difference vanishes
   and every row vector is in the null space, but the recursion still
   passes through one [lnb_step] per column, so at this pair (which has
   one column) the basis produced is [mat_mul (mat_id 2) (mat_id 2)] and
   not [mat_id 2].  The control is that both of its entries do close by
   [eq_refl], below.  Nothing is claimed about the general shape of the
   residue at more columns; only this instance was measured.
   (ii) [coeq_f2_map = coeq_f2_h] — the coequalizing map of the
   worked F₂ pair and the coforking row vector (1, 1) are refuted equal
   at whole-function Leibniz equality, although the control
   [coeq_f2_map Fin.F1 Fin.F1 = coeq_f2_h Fin.F1 Fin.F1] closes by
   [eq_refl], so the negative is about the two TERMS and not their
   values.
   (iii) the same map against the literal [fun _ _ => true] — refuted
   for the same reason as (ii): entries reduce at CLOSED indices, while
   under binders the Kronecker [delta] is stuck on a free index, so the
   matrix does not reduce to a constant function.
   (iv) [IsCoequalizer A B q e = @IsEqualizer ((Matr K)^op) m n A B q
   e] at the concrete F₂ instance — refuted, which confirms at a
   concrete category what Structure/Pullback/Reduction.v measured
   abstractly (its negatives 6 and 7): the two are separately declared
   records and Coq's record types are nominal, so no agreement between
   their fields makes them one type.  Every FIELD type is convertible,
   which is why the bridges below are [:=] with no tactic.
   (v) [matr_coeq_obj F2_Field F2_Field_dec coeq_f2_A coeq_f2_B
   = 1%nat] — refuted with the TREE's decider in place of the
   transparent copy, which confirms that Elimination.v's opacity
   measurement propagates to this file's constants unchanged; the
   control is the same statement with [f2_dec], which closes.
   One further observation, not an attempt: the [cofork] field has no
   reduction behaviour at all, being built from Elimination.v's [Qed]
   theorem [mat_mul_sub_zero_iff].  That costs nothing — a proof of an
   [≈] carries no data this file wants — and it is worth recording only
   because the neighbouring [coeq_desc] field DOES reduce, so the two
   fields of one record differ in this respect.

   THE DECIDERS.  Elimination.v measured that Instance/Field.v's
   [F2_Field_dec] and [Q_Field_dec] are [Qed] LEMMAS, so
   no application of either reduces and the elimination engine computes
   with neither.  Every [eq_refl] witness below therefore runs on that
   file's transparent copies [f2_dec] and [q_dec], which decide the same
   relations by the same case analyses and differ only in ending with
   [Defined].  The opacity is Instance/Field.v's, is NOT repaired here,
   and nothing above depends on it being repaired: the construction is
   correct with either decider, and only the [eq_refl] checks need the
   transparent one — which is exactly what refuted attempt (v) records.

   NOT DELIVERED BY THIS FILE.  No equalizers in [Matr K]: that needs
   the RIGHT null space, which Elimination.v explicitly does not build,
   and transporting the left-handed answer along Instance/Matr.v's
   [Matr_transpose_iso] is real work that is not attempted — what IS
   delivered is [HasEqualizers ((Matr K)^op)], which is the coequalizer
   statement reread through a duality bridge and not a new theorem.  No
   claim that the coequalizer object is m − rank (A − B), there being no
   rank function.  No claim that the object is independent of the
   construction AS A NUMBER: [matr_coeq_iso] gives only that any two
   coequalizers of one pair have isomorphic OBJECTS of [Matr K], and
   concluding from k ≅ k' that k = k' would need exactly the dimension
   argument this development lacks.  No pushouts, no cokernels, no
   [Cocomplete] or [Cocartesian] statement about [Matr K], and no
   reflexive- or split-coequalizer reading.  No statement about [Matr R]
   over a bare rig, per the paragraph above.  No normal form for E: the
   coequalizing map produced is whichever basis the elimination engine
   returns, so two pairs with the same difference up to [≈] are not
   shown to receive the same matrix on the nose — refuted attempts (i)
   to (iii) are three faces of that same limitation.

   THE ASSUMPTION FOOTPRINT is nil and was measured per constant rather
   than sampled: all 58 named constants of this file — the twelve of the
   section plus the 46 of the two witness blocks — report “Closed under
   the global context”.  The file uses no [Program] and declares no
   [Instance], so it generates no obligations and the enumeration from
   its own declarations is the complete one; this is the [Print Module]
   caveat docs/AXIOMS.md records, and it does not arise here. 

   --------
   * * 矩阵的余等化子

   Mac Lane，《为工作数学家而作的范畴论》，第2版，§III.3
   练习 3 [maclane:III.3:ex3] 要求求一对并行矩阵的余等化子。这个文件是该练习的范畴论部分。线性代数部分在 Instance/Matr/Elimination.v 中，在这里被使用，但既未扩展也未重新证明：下面的每个证明都是该文件的一个项，被传递给 Structure/Coequalizer.v 的记录字段，本文件不包含任何求和论证、枢轴操作，也没有自己的归纳。矩阵的余等化器是什么。对于一个平行对 A, B : n ⇉ m — 两个 m × n 矩阵 — 一个映射 h : m ~> z 当且仅当 h·A ≈ h·B 时共叉该对，根据 Elimination.v 的 [mat_mul_sub_zero_iff]，这当且仅当 h·(A − B) ≈ 0，即当且仅当 h 的每一行都位于 A − B 的左零空间中。因此，一个通用的共叉映射是一个矩阵 E，其行是那一空间的一组基：生成对应于分解的存在性，线性无关对应于其唯一性。于是，余等化器对象就是 E 的行数，也就是该零空间的维数。在这里也好，在 Elimination.v 中也好，都没有定义秩函数，所以熟悉的表述“k = m − rank (A − B)”在本发展中既未说明也未证明；它仅出现在这一句，其余地方都没有。方向。直接继承自 Instance/Matr.v 的原文，该文件遵循 Mac Lane：[Matr R] 的一个箭头 n ~> m 是一个 m × n 矩阵，组合就是矩阵乘法而不进行转置。设 x := n, y := m, f := A, g := B，Structure/Coequalizer.v 的记录要求一个对象 q := k 和一个映射 e : y ~> q，即一个 k × m 矩阵 E；其 [cofork] 字段 [e ∘ f ≈ e ∘ g] 是 E·A ≈ E·B；一个共分叉 h : y ~> z 是一个 z × m 矩阵；中介 u : q ~> z 是一个 z × k 矩阵，其三角形 [u ∘ e ≈ h] 表示 u·E ≈ h。这些正是 Elimination.v 的 [left_null_basis] 生成的四种形式。交接是纯转换，这一点是经过测量而非假设的。下面的每个陈述都是用该类别自己的词汇书写——[∘] 和 [≈[Matr K]——而每个一般结果的证明，也就是下面部分的十二个常数中的每一个，都是由 [:=] 提供的 Elimination.v 项，没有使用任何策略。（文件确实包含十一条策略脚本，全部位于末尾的两个见证块中，用于区分具体矩阵；该部分本身没有。）文件中任何地方都没有 [change]，也没有传输，无论在哪一部分。这项工作的有效之处在于 Elimination.v 通过 [eq_refl]（[matrix_is_hom]；[mat_mul_is_compose]，其对象参数的顺序为(c, b, a)；[mat_id_is_id]；以及 [mat_equiv_is_homset_equiv]，其最后记录的 [Setoid] 矩阵实例是 [Matr K] 的同态等价集合，而不是 [fun_setoid] 可能提供的逐点集合）将其自身的词汇与类别的词汇进行了识别。该实例 [#[local] 对 Elimination.v 可见，所以在这里不可见 —— 并且不需要，因为此文件中根本没有命名任何裸 [≈] 矩阵实例。可判定性假设，以及为什么它是强制的。下面的假设 [Kdec] 并不是方便之举。生成共等化映射意味着运行消元，而消元必须决定一个支点是否消失，而它运行的类并未提供这样的决定：[FieldObject]（Instance/FdVect.v）携带 [field_ring]、[field_comm]、[field_one_neq_zero]、一个全体的 [finv]、[finv_respects] 和 [finv_l] — 并且 [finv_l] 受 [x ≉ 0] 保护，因此反演律在非消失被确认之前不可用，而这正是争论的焦点。在一个抽象的等价集合载体上，[≈] 不可判定，并且 [finv] 在零处的值是垃圾。因此，该假设以显式数据的形式携带，正好以 Instance/Field.v 中 [field_dec_stable] 所采用的形式，而 Elimination.v 中的 [F2_dec_inhabits] 和 [Q_dec_inhabits] 通过类型归属记录 [F2_Field_dec] 和 [Q_Field_dec] 属于它，所以这是该树本身的概念，而不是一个新的概念。对此文件的后果是 [Matr_HasCoequalizers] 是一个普通的 [Definition]，将决策器作为参数，并且故意不注册为全局 [Instance]：类型类解析无法为抽象字段生成决策器，注册一个永远不会触发的提示只会毫无意义地扰乱数据库。使用者编写 [Matr_HasCoequalizers K Kdec] 并手动提供决策器。刚性约束。Instance/Matr.v 是在刚性环上陈述的，而且是有意这样做的：范畴定律需要结合性、单位元、分配律和消元律，而从不需要减法。一个余等化需要减法——从双矩阵问题 h·A ≈ h·B 到单矩阵问题 h·(A − B) ≈ 0 的转变就是整个桥梁，并且它花费了 [ring_neg]；枢轴步骤在此基础上花费了 [finv]。因此，该文件的基础是一个域，并且这里没有任何内容涉及裸刚性 R 的 [Matr R]。特别地，没有对 Awodey 的 [Matr_N := Matr Nat_Rig] (Instance/Matr.v) 做任何声明，其中 A − B 不存在：这个范畴是否有余等化是另一个问题，并且没有被讨论。测量的强度，先严格。[eq_refl] 在任何 [≈] 被接受之前就已经尝试过，并且这些工件被安排得使严格的形式始终可用：[matr_coeq_obj]、[matr_coeq_map] 和 [matr_coeq_desc] 由 [:=] 提供，而不是由用 [Qed] 关闭的策略脚本提供，因此交付记录的对象、地图和 [coeq_desc] 字段都减少。由 [eq_refl] 在 [F2_Field] 处关闭：处理对 (1) 的共轭化对象及其共轭化映射的两个条目；公共复合 E·A；从交付记录的 [coeq_desc] 字段中提取的 MEDIATOR —— 最后一个是如果 [matr_coeq_desc] 是一个 [Qed] 引理时会丢失的那个；以及三个进一步对的对象，将 k = m 固定在与自身的一对上（映射为 2 x 2，因此它有四个条目；其中两个在这里被固定，并且四个都是单位矩阵 —— 早期草稿中说“两个”，这对于处理对的 1 x 2 映射来说是对的，但在这里是错的），k = 0 在可逆差上，以及第二个非退化 k = 2 在 m = 3。在 [Q_Field] 对象上，coequalizing 映射的两个条目 −2 和 1，以及 cofork 方程的两边（每个 −1）也通过 [eq_refl] 封闭，合理的算术在封闭输入上进行简化。同样严格：[matr_IsEqualizer_op] 是 Structure/Pullback/Reduction.v 的 [IsEqualizer_op_of_IsCoequalizer] 应用于该记录，因此在此实例化时桥接是定义性的，而不仅仅是可用的。进行了五次严格尝试并被驳回。每一次都通过移除失败标记并确认真正的转换失败（每次报告“无法统一”）来检查，并且每次都有一个在相同参数下成功的阳性对照；没有一个是宇宙或阐述的产物。它们记录在此而非作为探针，本文件没有探针部分。(i) [matr_coeq_map F2_Field f2_dec coeq_f2_A coeq_f2_A = mat_id F2_Field 2] — 在与自身配对时，差异消失，每一行向量都在零空间中，但递归仍然在每列通过一个 [lnb_step]，因此在这个配对（它有一列）产生的基是 [mat_mul (mat_id 2) (mat_id 2)] 而不是 [mat_id 2]。对照是它的两个条目都通过 [eq_refl] 关闭，如下所示。关于更多列的残差的整体形状没有任何声明；只测量了这一实例。(ii) [coeq_f2_map = coeq_f2_h] —— 在整体函数的莱布尼茨等价下，经过处理的 F₂ 对的共等化映射与共叉行向量 (1, 1) 被否定为相等，尽管控制 [coeq_f2_map Fin.F1 Fin.F1 = coeq_f2_h Fin.F1 Fin.F1] 通过 [eq_refl] 闭合，所以否定的是两个项而不是它们的值。(iii) 对文字 [fun _ _ => true] 的同一映射 —— 因与(ii)相同的原因被否定：条目在闭合索引处简化，而在绑定器下，克罗内克 [delta] 在自由索引上被卡住，因此矩阵无法简化为常数函数。(iv) [IsCoequalizer A B q e = @IsEqualizer ((Matr K)^op) m n A B q e] 在具体的 F₂ 实例下被驳斥，这确认了 Structure/Pullback/Reduction.v 在抽象上测量的情况（其否定为 6 和 7）：这两个是单独声明的记录，而 Coq 的记录类型是名义类型，所以它们的字段没有任何一致性就不能成为同一类型。每个 FIELD 类型都是可转换的，这就是下面的桥梁是 [:=] 而没有使用任何策略的原因。 (v) [matr_coeq_obj F2_Field F2_Field_dec coeq_f2_A coeq_f2_B = 1%nat] — 使用 TREE 的决策器代替透明副本时被驳斥，这确认了 Elimination.v 的不透明性测量会不变地传播到此文件的常量；控制是使用 [f2_dec] 的相同语句，这关闭了。还有一个观察，不是尝试：[cofork] 字段完全没有归约行为，它是由 Elimination.v 的 [Qed] 定理 [mat_mul_sub_zero_iff] 构建的。这不花费任何成本——[≈] 的证明不携带这个文件需要的数据——记录下来只是因为相邻的 [coeq_desc] 字段确实会归约，因此同一记录的两个字段在这方面有所不同。决策者。Elimination.v 测量到 Instance/Field.v 的 [F2_Field_dec] 和 [Q_Field_dec] 是 [Qed] 引理，因此任意一个的应用都不会被化简，并且消元引擎都不会使用它们。下面的每个 [eq_refl] 证人因此都在该文件的透明副本 [f2_dec] 和 [q_dec] 上运行，这些副本通过相同的情况分析决定相同的关系，仅在以 [Defined] 结尾时有所不同。不透明性属于 Instance/Field.v，这里没有修复，而且上面的任何内容都不依赖于其被修复：用任意一个决策者构造都是正确的，只有 [eq_refl] 检查需要透明副本——这正是反驳尝试 (v) 记录的内容。此文件未提供。[Matr K] 中没有等化器：那需要正确的零空间，而 Elimination.v 明确没有构建它，并且沿着 Instance/Matr.v 的 [Matr_transpose_iso] 传输左边的答案是真正的工作，而未尝试——所提供的是 [HasEqualizers ((Matr K)^op)]，这是通过对偶桥重新读取的共等化器陈述，而不是新的定理。没有声称共等化对象是 m − rank(A − B)，因为不存在秩函数。没有声称该对象作为一个数字独立于构造：[matr_coeq_iso] 仅给出了对一对的任意两个共等化器，它们的 [Matr K] 对象是同构的，而从 k ≅ k' 推出 k = k' 则需要恰恰是这个发展缺乏的维数论证。没有推出、没有余核，没有关于 [Cocomplete] 或 [Cocartesian] 的 [Matr K] 说明，也没有自反或分裂余等值器的解读。根据上面段落，没有关于 [Matr R] 在裸环上的说明。E 没有规范形式：产生的余等化映射是消元引擎返回的任意基，因此两个具有相同 [≈] 差异的对并未显示出完全相同的矩阵——被驳回的尝试 (i) 到 (iii) 是同一限制的三个体现。假设占用为零，并且是按常量测量而不是抽样：该文件的所有 58 个命名常量——该节的 12 个加上两个见证块的 46 个——都报告“在全局上下文下闭合”。该文件未使用任何 [Program]，也未声明任何 [Instance]，因此不会生成任何义务，并且其自身声明中的枚举是完整的；这是 [Print Module] 警告 docs/AXIOMS.md 记录的内容，但在此处不会出现。
*)

Section MatrCoequalizer.

(* * ** The base: a field with a zero test [Kdec] has the type Instance/Field.v's [field_dec_stable] takes; see the header for why nothing weaker will do. / * ** 基础：具有零测试的域 [Kdec] 的类型是 Instance/Field.v 中 [field_dec_stable] 所采用的类型；请参阅标题了解为什么没有更弱的类型可用。 *)

Context (K : FieldObject).
Context (Kdec : ∀ a b : carrier (rig_setoid K), (a ≈ b) + (a ≈ b → False)).

(*
   * ** The construction

   A basis of the left null space of the difference.  Everything else in
   this section reads that one record through the category's
   vocabulary. 

   --------
   * ** 构造

   差的左零空间的一个基。 本节中的其他所有内容都将该记录通过类别的词汇表读取。
*)

Definition matr_lnb {m n : nat} (A B : n ~{Matr K}~> m) :
  LeftNullBasis K (mat_sub K A B) :=
  left_null_basis K Kdec (mat_sub K A B).

(*
 The coequalizer object: the dimension of the left null space of
 A − B.  Typed as an object of [Matr K], which is [nat]. 

 --------
 余等化对象：A − B 的左零空间的维数。作为 [Matr K] 的一个对象类型，[nat]。
*)
Definition matr_coeq_obj {m n : nat} (A B : n ~{Matr K}~> m) : Matr K :=
  lnb_dim (matr_lnb A B).

(* The coequalizing map: a basis matrix with k rows and m columns, which is what an arrow [m ~> k] of [Matr K] is. / 共等化映射：一个具有 k 行 m 列的基矩阵，这就是 [Matr K] 的一个箭头 [m ~> k] 所是的。 *)
Definition matr_coeq_map {m n : nat} (A B : n ~{Matr K}~> m) :
  m ~{Matr K}~> matr_coeq_obj A B :=
  lnb_basis (matr_lnb A B).

(*
   * ** The two clauses

   Both are Elimination.v terms supplied by [:=].  The cofork is
   annihilation of the basis read through [mat_mul_sub_zero_iff]; the
   descent is the basis's own universal clause read through the same
   equivalence in the other direction. 

   --------
   * ** 这两个条款

   两者都是由 [:=] 提供的消除.v 项。共叉是通过 [mat_mul_sub_zero_iff] 读取的基的湮灭；下降是基自己通过相同等价关系在另一方向上读取的通用条款。
*)

Definition matr_coeq_cofork {m n : nat} (A B : n ~{Matr K}~> m) :
  matr_coeq_map A B ∘ A ≈[Matr K] matr_coeq_map A B ∘ B :=
  fst (mat_mul_sub_zero_iff K Kdec (matr_coeq_map A B) A B)
    (lnb_annih (matr_lnb A B)).

(*
 Kept a transparent [Definition] on purpose: this is the field whose
 reduction the computing witnesses at the end of the file use. 

 --------
 故意保留了一个透明的 [Definition]：这是文件末尾计算见证使用其约简的字段。
*)
Definition matr_coeq_desc {m n : nat} (A B : n ~{Matr K}~> m)
  (z : Matr K) (h : m ~{Matr K}~> z) (Hh : h ∘ A ≈[Matr K] h ∘ B) :
  ∃! u : matr_coeq_obj A B ~{Matr K}~> z,
    u ∘ matr_coeq_map A B ≈[Matr K] h :=
  lnb_univ (matr_lnb A B) z h
    (snd (mat_mul_sub_zero_iff K Kdec h A B) Hh).

(* * ** Mac Lane §III.3 Exercise 3 The elementary coequalizer of an arbitrary parallel pair, and then the class quantifying over every parallel pair. / * ** Mac Lane §III.3 习题 3 任意平行对的基本共等化器，然后是对每个平行对进行量化的类。 *)

Definition matr_IsCoequalizer {m n : nat} (A B : n ~{Matr K}~> m) :
  IsCoequalizer A B (matr_coeq_obj A B) (matr_coeq_map A B) :=
  {| cofork    := matr_coeq_cofork A B
   ; coeq_desc := fun z h Hh => matr_coeq_desc A B z h Hh |}.

(* Deliberately a [Definition] and not an [Instance]; see the header. / 故意是一个 [Definition] 而不是一个 [Instance]；见标题。 *)
Definition Matr_HasCoequalizers : HasCoequalizers (Matr K) :=
  {| coeq := fun x y f g =>
       existT _ (matr_coeq_obj f g)
         (existT _ (matr_coeq_map f g) (matr_IsCoequalizer f g)) |}.

(* * ** What the generic API then gives Nothing here is new content: each is an instantiation of a result of Structure/Coequalizer.v at the coequalizer just built. / * ** 通用 API 然后提供的内容 这里没有新的内容：每一项都是在刚构建的余联合上的 Structure/Coequalizer.v 结果的一个实例化。 *)

(*
 A coequalizing map is an epimorphism ([coequalizer_epic]).  So every
 basis matrix the elimination engine returns is epic in [Matr K] — a
 fact about matrices reached with no matrix proof. 

 --------
 共等映射是一个满射（[coequalizer_epic]）。因此，消元引擎返回的每个基矩阵在[Matr K]中都是满射——这是一个关于矩阵的事实，而不需要矩阵证明。
*)
Definition matr_coeq_epic {m n : nat} (A B : n ~{Matr K}~> m) :
  Epic (matr_coeq_map A B) :=
  coequalizer_epic A B (matr_IsCoequalizer A B).

(*
 Any other coequalizer of the same pair has an isomorphic object.
 Read the strength: this is an isomorphism in [Matr K], a pair of
 mutually inverse matrices, and it does NOT say the two dimensions are
 equal — see the header's not-delivered list. 

 --------
 同一对的任何其他等化器都有一个同构对象。  
 理解这一点的力度：这是在 [Matr K] 中的一个同构，是一对互为逆矩阵，它并没有说两个维度相等——参见标题中的未发送列表。
*)
Definition matr_coeq_iso {m n : nat} (A B : n ~{Matr K}~> m)
  {q : Matr K} {e : m ~{Matr K}~> q} (E : IsCoequalizer A B q e) :
  q ≅ matr_coeq_obj A B :=
  coequalizer_unique A B E (matr_IsCoequalizer A B).

(* The colimit packaging: the same data as a colimit over the walking parallel pair ([is_coequalizer_colimit]). / 余极限的打包：作为在步行平行对 ([is_coequalizer_colimit]) 上的余极限的相同数据。 *)
Definition matr_coeq_colimit {m n : nat} (A B : n ~{Matr K}~> m) :
  Coequalizer (APair A B) :=
  is_coequalizer_colimit A B (matr_IsCoequalizer A B).

(*
   * ** The dual reading

   Structure/Pullback/Reduction.v's bridges, instantiated.  Both are
   [:=] with no tactic HERE.  Do not read that back into Reduction.v:
   there, only [IsEqualizer_op_of_IsCoequalizer] is a [:=];
   [HasEqualizers_op_of_HasCoequalizers] is a tactic script.  An
   earlier draft said “as they are there”, which inverts that.  See
   refuted attempt (iv) for
   what is NOT true of them. 

   --------
   * ** 双重阅读

   Structure/Pullback/Reduction.v 的桥接，已实例化。两者都是 [:=]，并且在此没有使用战术。不要把它读回 Reduction.v：在那里，只有 [IsEqualizer_op_of_IsCoequalizer] 是 [:=]；[HasEqualizers_op_of_HasCoequalizers] 是一个战术脚本。早期草稿中写的是“如它们在那里那样”，这与实际相反。参见被驳回的尝试 (iv) 以了解它们的错误之处。
*)

Definition matr_IsEqualizer_op {m n : nat} (A B : n ~{Matr K}~> m) :
  @IsEqualizer ((Matr K)^op) m n A B
    (matr_coeq_obj A B) (matr_coeq_map A B) :=
  IsEqualizer_op_of_IsCoequalizer (matr_IsCoequalizer A B).

Definition Matr_op_HasEqualizers : @HasEqualizers ((Matr K)^op) :=
  HasEqualizers_op_of_HasCoequalizers Matr_HasCoequalizers.

End MatrCoequalizer.

(*
   * ** A worked coequalizer over F₂

   [F2_Field] (Instance/Field.v) is the cheapest base at which every
   step computes: the carrier is [bool] with Leibniz equality, addition
   is [xorb], multiplication is [andb], and negation is the identity, so
   the difference of two matrices is their entrywise exclusive or.  The
   decider used throughout is Elimination.v's transparent [f2_dec] and
   NOT Instance/Field.v's [F2_Field_dec], which is a [Qed] lemma through
   which nothing reduces; see the header, and refuted attempt (v) for
   the measurement.

   The pair is A, B : 1 ⇉ 2, that is, two columns of height 2:
   A = (1, 0)ᵀ and B = (0, 1)ᵀ.  Their difference is (1, 1)ᵀ, whose left
   null space is the line spanned by (1, 1), so the coequalizer object
   is 1 — NEITHER 0 NOR m = 2, which is what makes the example
   non-degenerate, and which is proved below rather than asserted. 

   --------
   * ** 在 F₂ 上计算的共同余核

   [F2_Field]  (Instance/Field.v) 是每一步计算的最便宜的基础：载体是  [bool]  并采用 Leibniz 等式，加法是  [xorb] ，乘法是  [andb] ，取负是恒等操作，因此两个矩阵的差是它们逐项进行异或。  
   整个过程中使用的判定器是 Elimination.v 的透明  [f2_dec] ，而不是 Instance/Field.v 的  [F2_Field_dec] ，它是一个 [Qed] 引理，通过它没有任何简化发生；参见头部，以及被否定的尝试 (v) 以进行测量。这一对是 A, B : 1 ⇉ 2，也就是两列高度为 2 的列向量：
   A = (1, 0)ᵀ，B = (0, 1)ᵀ。它们的差是 (1, 1)ᵀ，其左零空间是由 (1, 1) 生成的直线，因此余等化对象是 1 — 既不是 0 也不是 m = 2，这正是使该例子非退化的原因，并且这个结论在下文中被证明，而非仅仅被断言。
*)

Definition coeq_f2_A : 1%nat ~{Matr F2_Field}~> 2%nat :=
  fun i _ => match i with Fin.F1 => true | _ => false end.

Definition coeq_f2_B : 1%nat ~{Matr F2_Field}~> 2%nat :=
  fun i _ => match i with Fin.F1 => false | _ => true end.

Definition coeq_f2_obj : Matr F2_Field :=
  matr_coeq_obj F2_Field f2_dec coeq_f2_A coeq_f2_B.

Definition coeq_f2_map : 2%nat ~{Matr F2_Field}~> coeq_f2_obj :=
  matr_coeq_map F2_Field f2_dec coeq_f2_A coeq_f2_B.

Definition coeq_f2 :
  IsCoequalizer coeq_f2_A coeq_f2_B coeq_f2_obj coeq_f2_map :=
  matr_IsCoequalizer F2_Field f2_dec coeq_f2_A coeq_f2_B.

(* The object and both entries of the coequalizing map, COMPUTED. / 该对象及共等化映射的两个条目，已计算。 *)
Example coeq_f2_obj_computes : coeq_f2_obj = 1%nat := eq_refl.

Example coeq_f2_map_0 : coeq_f2_map Fin.F1 Fin.F1 = true := eq_refl.

Example coeq_f2_map_1 :
  coeq_f2_map Fin.F1 (Fin.FS Fin.F1) = true := eq_refl.

(*
 The common composite E·A is the 1 × 1 matrix (1): the coequalizer
 does not collapse everything in sight. 

 --------
 常见的复合 E·A 是 1 × 1 矩阵 (1)：共轭化器不会将所见的一切都压缩。
*)
Example coeq_f2_composite :
  (coeq_f2_map ∘ coeq_f2_A) Fin.F1 Fin.F1 = true := eq_refl.

(*
   * *** Non-degeneracy, proved

   Three separate facts.  First, the object is neither of the two
   degenerate answers.  Second, the pair really is a pair: A and B are
   not equivalent arrows, so this is not a coequalizer of something with
   itself.  Third — the categorical form of the same point — the
   coequalizing map is NOT monic, since it identifies those two
   inequivalent arrows, while it IS epic by [matr_coeq_epic]; so it is a
   proper quotient and not an isomorphism in disguise. 

   --------
   * *** 非退化性，已证明

   三个独立的事实。首先，该对象既不是两个退化解答中的任何一个。第二，这对确实是一对：A 和 B 不是等价箭头，因此这不是某物与自身的共等化器。第三——同一点的范畴形式——共等化映射不是单射，因为它将那两个不等价的箭头识别为相同，而根据 [matr_coeq_epic]，它是满射的；所以它是一个真正的商，而不是伪装的同构。
*)

Lemma coeq_f2_obj_not_zero : coeq_f2_obj ≠ 0%nat.
Proof. discriminate. Qed.

Lemma coeq_f2_obj_not_two : coeq_f2_obj ≠ 2%nat.
Proof. discriminate. Qed.

Lemma coeq_f2_pair_distinct :
  coeq_f2_A ≈[Matr F2_Field] coeq_f2_B → False.
Proof.
  intro H.
  specialize (H Fin.F1 Fin.F1).
  discriminate H.
Qed.

Lemma coeq_f2_map_not_monic : Monic coeq_f2_map → False.
Proof.
  intros [HM].
  apply coeq_f2_pair_distinct.
  exact (HM 1%nat coeq_f2_A coeq_f2_B (cofork coeq_f2)).
Qed.

Definition coeq_f2_map_epic : Epic coeq_f2_map :=
  matr_coeq_epic F2_Field f2_dec coeq_f2_A coeq_f2_B.

(*
   * *** The mediator computes

   The universal clause is not vacuous, and the factorization it
   produces reduces.  The row vector h = (1, 1) coforks the pair —
   h·A = 1 = h·B — so it factors through E, and the mediator the
   construction returns is the 1 × 1 matrix (1).  This is the check that
   would have been lost had [matr_coeq_desc] been closed with [Qed]. 

   --------
   * *** 调解者计算

   通用子句并非空洞，它产生的分解可以被化简。行向量 h = (1, 1) 分叉该对 — h·A = 1 = h·B — 因此它通过 E 进行分解，而调解者返回的构造是 1 × 1 矩阵 (1)。如果用 [Qed] 关闭 [matr_coeq_desc]，就会丢失这个检查。
*)

Definition coeq_f2_h : 2%nat ~{Matr F2_Field}~> 1%nat := fun _ _ => true.

Lemma coeq_f2_h_coforks :
  coeq_f2_h ∘ coeq_f2_A ≈[Matr F2_Field] coeq_f2_h ∘ coeq_f2_B.
Proof. intros i j; reflexivity. Qed.

(*
 Stated with the type left inferred, purely for brevity.

 AN EARLIER DRAFT JUSTIFIED THIS BY SAYING THAT WRITING THE [∃!] OUT
 AGAIN WOULD ELABORATE [coeq_f2] AT FRESH UNIVERSES THAT WOULD NOT
 UNIFY, CITING A MEASUREMENT ELIMINATION.V RECORDS AT ITS OWN
 [f2_mediator].  THAT MEASUREMENT IS GENUINE THERE AND DOES NOT HOLD
 HERE: an audit wrote the type out in two spellings at THIS site and
 both are accepted, the mediator still computing.  The claim was
 transferred to a site where it is false, and is recorded as bad
 evidence rather than deleted. 

 --------
 以左侧类型推断方式陈述，仅为简洁起见。

 早期草稿通过说明再次写出 [∃!] 会在无法统一的新宇宙中展开 [coeq_f2]，从而证明了这一点，并引用了其自身 [f2_mediator] 的测量消除记录。该测量在那里的确有效，而在这里则不成立：审计在此站点以两种拼写方式写出了该类型，并且两种拼写都被接受，中介仍在计算。该声明被转移到一个不成立的站点，并记录为错误证据，而非删除。
*)
Definition coeq_f2_mediator :=
  coeq_desc coeq_f2 coeq_f2_h coeq_f2_h_coforks.

Example coeq_f2_mediator_computes :
  unique_obj coeq_f2_mediator Fin.F1 Fin.F1 = true := eq_refl.

(*
 The positive control for refuted attempt (ii): the coequalizing map
 and this row vector agree ENTRYWISE by [eq_refl], so the refutation of
 [coeq_f2_map = coeq_f2_h] is about the two terms and not their
 values. 

 --------
 否定尝试 (ii) 的阳性对照：共等化映射和这个行向量在每个条目上都与 [eq_refl] 一致，所以对 [coeq_f2_map = coeq_f2_h] 的反驳是关于这两个项而不是它们的数值。
*)
Example coeq_f2_map_h_agree_at :
  coeq_f2_map Fin.F1 Fin.F1 = coeq_f2_h Fin.F1 Fin.F1 := eq_refl.

(* The positive control for refuted attempt (iv): the duality bridge is definitional at this instantiation, even though the two record TYPES are not identified. / 反驳尝试(iv)的阳性对照：在此实例化中，二重性桥是定义性的，即使这两种记录类型未被识别。 *)
Example coeq_f2_op_is_bridge :
  matr_IsEqualizer_op F2_Field f2_dec coeq_f2_A coeq_f2_B
  = IsEqualizer_op_of_IsCoequalizer coeq_f2 := eq_refl.

(*
   * *** The object responds to the pair

   Three more pairs, pinning the two degenerate answers and one further
   non-degenerate one, so that the dimension is visibly a function of
   the difference and not a constant.

   (i) A pair with itself: the difference vanishes, every row vector is
   in the left null space, and the coequalizing map computes to the
   entries of the identity matrix on m = 2 — the degenerate case,
   computed rather than assumed.  It is NOT the term [mat_id F2_Field 2]
   on the nose; see refuted attempt (i). 

   --------
   * *** 该对象对该对做出响应  

   另外三对，将两个退化解和另一个非退化解固定，使得维度明显是差异的函数，而不是一个常数。

   (i) 与自身的对：差异消失，每个行向量都在左零空间中，协同化映射计算得到 m = 2 的单位矩阵的各个条目——这是退化情况，是计算得出的而非假设的。它**不是**精确的项 [mat_id F2_Field 2]；见已驳回的尝试 (i)。
*)

Example coeq_f2_self_obj :
  matr_coeq_obj F2_Field f2_dec coeq_f2_A coeq_f2_A = 2%nat := eq_refl.

Example coeq_f2_self_map_diag :
  matr_coeq_map F2_Field f2_dec coeq_f2_A coeq_f2_A Fin.F1 Fin.F1 = true
  := eq_refl.

Example coeq_f2_self_map_off :
  matr_coeq_map F2_Field f2_dec coeq_f2_A coeq_f2_A
    Fin.F1 (Fin.FS Fin.F1) = false := eq_refl.

(*
 (ii) A difference that is invertible: the left null space is zero, so
 the coequalizer object is 0 and the coequalizing map has no rows. 

 --------
 （ii）可逆的差异：左零空间为零，因此共等化对象为0，共等化映射没有行。
*)

Definition coeq_f2_I : 2%nat ~{Matr F2_Field}~> 2%nat :=
  fun i j => delta F2_Field i j.

Definition coeq_f2_O : 2%nat ~{Matr F2_Field}~> 2%nat := fun _ _ => false.

Example coeq_f2_iden_obj :
  matr_coeq_obj F2_Field f2_dec coeq_f2_I coeq_f2_O = 0%nat := eq_refl.

(* (iii) Height 3, difference (1, 1, 0)ᵀ: the left null space is the plane {(a, b, c) : a + b = 0}, of dimension 2 — again neither 0 nor m = 3. / (iii) 高度 3，差异 (1, 1, 0)ᵀ：左零空间是平面 {(a, b, c) : a + b = 0}，维数为 2——同样既不是 0 也不是 m = 3。 *)

Definition coeq_f3_A : 1%nat ~{Matr F2_Field}~> 3%nat :=
  fun i _ => match i with
             | Fin.F1 => true
             | Fin.FS Fin.F1 => true
             | _ => false
             end.

Definition coeq_f3_B : 1%nat ~{Matr F2_Field}~> 3%nat := fun _ _ => false.

Example coeq_f3_obj :
  matr_coeq_obj F2_Field f2_dec coeq_f3_A coeq_f3_B = 2%nat := eq_refl.

Lemma coeq_f3_obj_not_zero :
  matr_coeq_obj F2_Field f2_dec coeq_f3_A coeq_f3_B ≠ 0%nat.
Proof. discriminate. Qed.

Lemma coeq_f3_obj_not_three :
  matr_coeq_obj F2_Field f2_dec coeq_f3_A coeq_f3_B ≠ 3%nat.
Proof. discriminate. Qed.

(*
   * ** A worked coequalizer over ℚ

   [Q_Field] with Elimination.v's transparent [q_dec] is a base in which
   the pivot DIVISION does something: the pair A = (3, 5)ᵀ,
   B = (2, 3)ᵀ has difference (1, 2)ᵀ, whose left null space is spanned
   by (−2, 1), and the coefficient −2 is produced by [finv] rather than
   by a case analysis.  Both sides of the cofork equation compute to the
   1 × 1 matrix (−1) — equal, as they must be, and NONZERO, so this is
   not the example in which everything is killed. 

   --------
   * ** 在 ℚ 上的一个已完成的共等化器

   [Q_Field] 使用 Elimination.v 的透明 [q_dec] 是一个基，在其中
   主划分做了某事：对 (3, 5)ᵀ 的对 A，
   对 (2, 3)ᵀ 的对 B，其差为 (1, 2)ᵀ，其左零空间由 (−2, 1) 生成，
   并且系数 −2 是由 [finv] 产生的，而不是通过情况分析产生的。共叉方程的两边计算结果都是
   1 × 1 矩阵 (−1) —— 相等，正如必须的，并且非零，因此这不是所有东西都被消去的例子。
*)

Definition coeq_q_A : 1%nat ~{Matr Q_Field}~> 2%nat :=
  fun i _ => match i with Fin.F1 => 3%Q | _ => 5%Q end.

Definition coeq_q_B : 1%nat ~{Matr Q_Field}~> 2%nat :=
  fun i _ => match i with Fin.F1 => 2%Q | _ => 3%Q end.

Definition coeq_q_obj : Matr Q_Field :=
  matr_coeq_obj Q_Field q_dec coeq_q_A coeq_q_B.

Definition coeq_q_map : 2%nat ~{Matr Q_Field}~> coeq_q_obj :=
  matr_coeq_map Q_Field q_dec coeq_q_A coeq_q_B.

Definition coeq_q :
  IsCoequalizer coeq_q_A coeq_q_B coeq_q_obj coeq_q_map :=
  matr_IsCoequalizer Q_Field q_dec coeq_q_A coeq_q_B.

Example coeq_q_obj_computes : coeq_q_obj = 1%nat := eq_refl.

Example coeq_q_map_0 : coeq_q_map Fin.F1 Fin.F1 = (-2 # 1)%Q := eq_refl.

Example coeq_q_map_1 :
  coeq_q_map Fin.F1 (Fin.FS Fin.F1) = (1 # 1)%Q := eq_refl.

(* Both legs of the cofork, computed on closed rational input. / 在封闭有理输入上计算的协叉的两条腿。 *)
Example coeq_q_left :
  (coeq_q_map ∘ coeq_q_A) Fin.F1 Fin.F1 = (-1 # 1)%Q := eq_refl.

Example coeq_q_right :
  (coeq_q_map ∘ coeq_q_B) Fin.F1 Fin.F1 = (-1 # 1)%Q := eq_refl.

Lemma coeq_q_obj_not_zero : coeq_q_obj ≠ 0%nat.
Proof. discriminate. Qed.

Lemma coeq_q_obj_not_two : coeq_q_obj ≠ 2%nat.
Proof. discriminate. Qed.

Lemma coeq_q_pair_distinct :
  coeq_q_A ≈[Matr Q_Field] coeq_q_B → False.
Proof.
  intro H.
  specialize (H Fin.F1 Fin.F1).
  discriminate H.
Qed.

Lemma coeq_q_map_not_monic : Monic coeq_q_map → False.
Proof.
  intros [HM].
  apply coeq_q_pair_distinct.
  exact (HM 1%nat coeq_q_A coeq_q_B (cofork coeq_q)).
Qed.

Definition coeq_q_map_epic : Epic coeq_q_map :=
  matr_coeq_epic Q_Field q_dec coeq_q_A coeq_q_B.
