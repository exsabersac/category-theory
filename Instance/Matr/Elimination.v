(*
 [Coq.QArith.QArith] MUST precede [Category.Lib]: it exports an [equiv]
 that otherwise shadows Lib/Setoid.v's, and every [Proper] statement
 below then fails to elaborate.  This is the import-order gotcha
 Instance/FdVect.v records in its own header; measured here too. 

 --------
 [Coq.QArith.QArith] 必须在 [Category.Lib] 之前：它导出一个 [equiv]，否则会覆盖 Lib/Setoid.v 的内容，并且下面的每一个 [Proper] 语句将无法展开。这是在 Instance/FdVect.v 的文件头中记录的导入顺序陷阱；在这里也进行了测量。
*)
Require Import Coq.QArith.QArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Matr.
Require Import Category.Instance.Matr.Determinant.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Field.
Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(*
   * * Gaussian elimination: a basis of the left null space

   Mac Lane, “Categories for the Working Mathematician”, 2nd ed., §III.3
   Exercise 3 [maclane:III.3:ex3] asks for the coequalizer of a parallel
   pair of matrices.  This file is the LINEAR-ALGEBRA half of that
   exercise and deliberately stops there.  It produces, for an arbitrary
   matrix M over a field equipped with a zero test, a basis of the LEFT
   NULL SPACE of M, packaged with exactly the universal clause such a
   colimit consumes.  Read the scope precisely: the record
   [LeftNullBasis] speaks of [mat_mul] and [mat_zero] and of nothing
   else, and NO colimit, cocone, quotient or structure class of the
   library is mentioned anywhere in this file — but [Matr K] itself IS
   used, and it is used for five things and no more: associativity, the
   two unit laws, the congruence [compose_respects], and the hom-setoid,
   which is taken as the [Setoid] instance on matrices.  All five are
   cited rather than reproved, because [mat_mul] is measured below to BE
   that category's [compose].

   WHAT IS PRODUCED.  For [M : Matrix K m n] the construction returns a
   natural number k, a matrix [E : Matrix K k m] with [E · M ≈ 0], and
   the universal clause: for every z and every [h : Matrix K z m] with
   [h · M ≈ 0] there is a UNIQUE [u : Matrix K z k] with [u · E ≈ h].
   The two halves say, in matrix terms, that the rows of E SPAN the left
   null space of M (existence of u) and are LINEARLY INDEPENDENT
   (uniqueness of u); k is the dimension of that space, so k = m - rank M
   — though no rank function is defined here and the equation is not
   stated, let alone proved.

   ORIENTATION.  Instance/Matr.v follows Mac Lane: an arrow [n ~> m] of
   [Matr R] is an m × n matrix, [Matrix R rows cols] being
   [Fin.t rows → Fin.t cols → carrier R] and [hom n m] being
   [Matrix R m n].  That convention is inherited verbatim, and it is
   MEASURED rather than assumed: [matrix_is_hom],
   [mat_mul_is_compose] and [mat_id_is_id] record by [eq_refl] that
   [Matrix K a b] IS the hom-type [b ~{Matr K}~> a], that the [mat_mul]
   of this file IS [Matr K]'s [compose] with its three object arguments
   in the order (c, b, a), and that [mat_id] IS [Matr K]'s identity.
   Consequently associativity and the two unit laws are cited from the
   category rather than proved again.

   THE DECIDABILITY HYPOTHESIS, AND WHY IT IS FORCED.  Elimination has
   to DECIDE whether a pivot vanishes, and the class it runs over
   supplies no such decision.  [FieldObject] (Instance/FdVect.v) carries
   exactly [field_ring], [field_comm], [field_one_neq_zero], a TOTAL
   [finv], [finv_respects], and [finv_l] — and [finv_l] is GUARDED by
   [x ≉ 0], so the inverse law is unusable until non-vanishing has been
   established.  Over an abstract setoid carrier [≈] is not decidable,
   and the value of [finv] at zero is junk constrained only by
   [finv_respects].  The hypothesis is therefore carried as EXPLICIT
   DATA, in the exact shape Instance/Field.v already prices it: that
   file's [field_dec_stable] takes
   [dec : ∀ a b, (a ≈ b) + (a ≈ b → False)] and discharges it at
   [Q_Field_dec] and [F2_Field_dec].  The section variable [Kdec] below
   has that type verbatim, and [F2_dec_inhabits]/[Q_dec_inhabits]
   record BY ASCRIPTION that those two constants inhabit it, so the
   hypothesis is the tree's own notion and not a new one.  This is not
   a formalization shortcut standing in for a theorem: no decider is
   derivable from [FieldObject], and the tree already treats the
   decider as data at exactly this point.  That non-derivability is
   ARGUED HERE, NOT PROVED -- this tree's convention for exactly this
   shape is to prove it ([Instance/Field.v]'s own
   [stability_is_the_conclusion] and siblings), and no such theorem
   is offered below, so the word “forced” should be read as “no route
   around it was found”, not as a proved impossibility.

   One caveat, measured rather
   than anticipated: both in-tree deciders are [Qed] LEMMAS, so neither
   reduces, and the computing witnesses at the end of this file run on
   transparent copies ([f2_dec], [q_dec]) that decide the same
   relations by the same case analyses — see the disclosure there.

   THE COERCION PATH, as measured in the code rather than guessed:
   [FieldObject] has [field_ring :> RingObject] (Instance/FdVect.v) and
   [RingObject] has [ring_rig :> RigObject] (Theory/Algebra/Rig.v), so a
   [K : FieldObject] reaches [Matr]'s parameter as
   [ring_rig (field_ring K)] and [Matrix K a b] elaborates to
   [Matrix (ring_rig (field_ring K)) a b].  SUBTRACTION comes from the
   RING layer's [ring_neg]: a bare rig has no negation, which is why
   this file is stated over a field (a ring would suffice for [mat_sub]
   alone, but not for the pivot division).

   THE ROUTE.  Recursion on the number of COLUMNS.  With no columns
   every row vector is in the left null space, so the identity matrix is
   a basis ([lnb_id], which also covers a column that vanishes
   identically).  With at least one column, split M into its first
   column and the rest: a row vector kills M exactly when it kills the
   first column AND kills the rest.  So take a basis E1 of the left null
   space of the first column, push the remaining columns through it, and
   recurse on [E1 · tail M], which has one column fewer; if E2 is a
   basis for that, then [E2 · E1] is a basis for M ([lnb_step]).  The
   whole construction therefore rests on the SINGLE-COLUMN case, which
   is the pivot step proper ([pivot_basis]): with a pivot entry
   [c p ≉ 0], the vectors [e_{d r} − (c_{d r} / c_p) · e_p], indexed by
   [r : Fin.t m'] through Determinant.v's order-preserving injection
   [fin_delete p] that misses p, are a basis.  The mediator is then
   literally RESTRICTION along [fin_delete p] — [u a r := h a (d r)] —
   and the pivot column of the equation [u · E ≈ h] is where the null
   space hypothesis on h is spent.

   REUSE.  The finite-sum library of Instance/Matr.v ([fin_sum] with its
   congruence, [fin_sum_zero], [fin_sum_add], bilinearity
   [fin_sum_mul_l]/[fin_sum_mul_r] and the Kronecker collapses
   [fin_sum_delta_l]/[fin_sum_delta_r]) and the kit of
   Instance/Matr/Determinant.v ([fin_delete] with [fin_delete_neq],
   [fin_delete_inj] and the three computation rules; the ring
   arithmetic [ring_neg_mul_l], [ring_neg_mul_r], [ring_neg_zero] and
   [ring_neg_unique]; and [fin_sum_neg]) are consumed, not
   re-derived.  What this file adds to that kit is [fin_delete_surj]
   (the complement of a deleted index is exactly the image of
   [fin_delete]) and [fin_sum_delete] (a finite sum splits as the term
   at p plus the sum over the complement of p) — the second is the one
   genuinely new summation lemma, and it is what makes the pivot column
   computable.  Instance/FdVect/Tensor.v has an unrelated lemma named
   [fin_sum_split] about splitting [Fin.t (a + b)]; that file is not
   required here and the names do not collide.

   MEASURED STRENGTHS, strict first.  Closing by [eq_refl]:
   [matrix_is_hom], [mat_mul_is_compose], [mat_id_is_id],
   [mat_equiv_is_homset_equiv] (the local [Setoid] instance on matrices
   IS [Matr K]'s hom-setoid, not a parallel pointwise one), and — the
   two that make [lnb_step] cheap — [mat_mul_col0_strict] and
   [mat_mul_tail_strict], where taking the first column of a product and
   multiplying into the first column give the SAME TERM, so no lemma is
   needed at all.  Over F₂ the dimension, every basis entry, the
   annihilation and the MEDIATOR of the worked example all close by
   [eq_refl]; over ℚ the dimension, the basis entries −2 and 1 and the
   annihilation close by [eq_refl] too, the rational arithmetic
   reducing on closed input.

   FOUR STRICT ATTEMPTS WERE MADE AND REFUTED.  They are recorded here
   rather than as [Fail] probes, this file carrying no probe section:
   (i) [mat_mul (mat_id a) A = A] — the unit law is a genuine
   finite-sum computation, not a conversion, and only [mat_mul_id_l]'s
   [≈] holds; (ii) the same for [mat_sub A A = mat_zero]; (iii) the F₂
   dimension check with the tree's [F2_Field_dec] in place of [f2_dec],
   which is what located the opacity described above; and (iv)
   [lnb_basis f2_col_lnb = lnb_basis f2_ones_lnb], which is refuted at
   whole-matrix Leibniz equality although both entries of both agree —
   the two are produced by different numbers of recursion steps, so
   they are different closed terms with the same values, and the file's
   four [f2_*_basis_*] Examples pin the values.  Each negative was
   stripped of its [Fail] and confirmed to be a genuine conversion
   failure, against a positive control at the same arguments.

   TWO ENGINEERING FINDINGS.  [Coq.QArith.QArith] must be Required
   BEFORE [Category.Lib] — see the comment above the import block; and,
   following the Determinant.v precedent, this file's section sets
   [Default Proof Using “All”], because [Kdec] occurs in proofs
   ([find_nonzero]) without occurring in the corresponding statements,
   so every [Qed] lemma below takes K and [Kdec] as its two leading
   arguments even where [Kdec] is not used.

   NOT DELIVERED BY THIS FILE.  No rank function, and so no proof that
   [lnb_dim] is [m - rank M]; no claim that [lnb_dim] is independent of
   the construction (uniqueness of the dimension is not stated, though
   it follows from the universal clause and would be a natural next
   lemma); no echelon form, no normal form and no pivot list, so nothing
   here decides matrix equivalence; no right null space and no
   transpose-based dual (the transpose functor of Instance/Matr.v would
   give it, and is not used); no statement about [Matr K] as a category
   beyond the three [eq_refl] identifications above; and no bridge to
   any colimit, cocone or quotient vocabulary — that is the next file's
   business, not this one's. 

   --------
   * * 高斯消元法：左零空间的一个基Mac Lane，《为工作数学家准备的范畴》，第2版，§III.3 练习3 [maclane:III.3:ex3] 要求求一个平行矩阵对的余等化器。这个文件是该练习的线性代数部分，并有意在此停止。它为任意带零检测的域上的矩阵 M 生成 M 的左零空间的一个基，并配备了此类余极限所需的完全通用条款。精确地阅读范围：记录 [LeftNullBasis] 讲述了 [mat_mul] 和 [mat_zero]，并且没有其他内容，本文件中没有提到库的任何余极限、余锥、商或结构类——但 [Matr K] 本身确实被使用，并且它只用于五件事：结合律、两个单位律、同余 [compose_respects]，以及同态集，它取作矩阵上的 [Setoid] 实例。所有五个都是被引用而非重新证明，因为 [mat_mul] 在下面被测定为该范畴的 [compose]。产生的内容。对于 [M : Matrix K m n]，构造返回一个自然数 k，一个矩阵 [E : Matrix K k m] 及 [E · M ≈ 0]，以及通用子句：对于每个 z 和每个 [h : Matrix K z m]，如果 [h · M ≈ 0]，则存在唯一的 [u : Matrix K z k]，使得 [u · E ≈ h]。两部分用矩阵术语表示：E 的行生成了 M 的左零空间（u 的存在性），并且线性无关（u 的唯一性）；k 是该空间的维数，因此 k = m - rank M——尽管此处没有定义秩函数，也没有陈述，更不用说证明这个等式。方向。Instance/Matr.v 遵循 Mac Lane：一个箭头 [n ~> m] 的 [Matr R] 是一个 m × n 矩阵，[Matrix R rows cols] 为 [Fin.t rows → Fin.t cols → carrier R]，[hom n m] 为 [Matrix R m n]。该约定被逐字继承，而且是测量而非假定的：[matrix_is_hom]，[mat_mul_is_compose] 和 [mat_id_is_id] 通过 [eq_refl] 记录 [Matrix K a b] 是同态类型 [b ~{Matr K}~> a]，此文件的 [mat_mul] 是 [Matr K] 的 [compose]，三个对象参数的顺序为 (c, b, a)，并且 [mat_id] 是 [Matr K] 的同一性。因此，结合律和两个单位律是从范畴中引用的，而不是再次证明。可判定性假设，以及为什么它是强制性的。消元必须决定一个主元是否为零，而它运行的类并不提供这样的决定。[FieldObject]（Instance/FdVect.v）正好包含 [field_ring]，[field_comm]，[field_one_neq_zero]，总体 [finv]，[finv_respects] 和 [finv_l] ——并且 [finv_l] 由 [x ≉ 0] 保护，因此在非零性被确认之前逆定律无法使用。在抽象集合体 [≈] 上是不可判定的，并且 [finv] 在零点的值只是受 [finv_respects] 的约束。因此，这个假设以显式数据的形式承载，正如 Instance/Field.v 文件所已经定义：该文件的 [field_dec_stable] 接受 [dec : ∀ a b, (a ≈ b) + (a ≈ b → False)] 并在 [Q_Field_dec] 和 [F2_Field_dec] 处释放它。下面的段变量 [Kdec] 拥有完全相同的类型，而 [F2_dec_inhabits] / [Q_dec_inhabits] 以记录方式表明这两个常量属于它，因此该假设是树自身的概念，而不是新的概念。这不是作为定理的形式化捷径：无法从 [FieldObject] 推导出判定器，并且树在这一点上已经将判定器视为数据。该不可推导性在此处进行论证，而非证明——该树对于这种形状的约定是证明它（[Instance/Field.v] 自身的 [stability_is_the_conclusion] 及其同类），下面没有提供这样的定理，因此“强制”一词应理解为“没有找到绕过它的途径”，而不是经过证明的不可能性。有一个警告，这是经过测量而非预期的：树内的两个决策器都是 [Qed]  引理，因此都不会简化，而本文件结尾的计算证明者在透明副本（[f2_dec]，[q_dec]）上运行，这些副本通过相同的案例分析决定相同的关系——见那里的披露。

   强制路径，在代码中测量而非猜测的情况：
   [FieldObject] 有 [field_ring :> RingObject]（Instance/FdVect.v），[RingObject] 有 [ring_rig :> RigObject]（Theory/Algebra/Rig.v），因此 [K : FieldObject] 访问 [Matr] 的参数为 [ring_rig (field_ring K)]，并且 [Matrix K a b] 展开为 [Matrix (ring_rig (field_ring K)) a b]。减法来自 RING 层的 [ring_neg]：一个裸的环没有负数，这就是为什么本文件是在域上说明（单独的 [mat_sub] 环就足够了，但对于枢轴除法则不够）。路线。按列数递归。没有列时，每个行向量都在左零空间中，因此单位矩阵就是一个基（[lnb_id]，这也包括一个完全消失的列）。至少有一列时，将 M 分成第一列和剩余列：一个行向量恰好在消去 M 时，也就是它同时消去第一列和剩余列。因此，取第一列左零空间的基 E1，将剩余列经过它，然后对 [E1 · tail M] 递归，它少一列；如果 E2 是其基，那么 [E2 · E1] 就是 M 的基（[lnb_step]）。因此，整个构造依赖于单列情况，这是正确的枢轴步骤（[pivot_basis]）：具有枢轴条目[c p ≉ 0]，通过确定式的保序注入[fin_delete p]，索引为[r : Fin.t m']的向量[e_{d r} − (c_{d r} / c_p) · e_p]（遗漏p）构成一个基。中介者实际上是沿着[fin_delete p] — [u a r := h a (d r)]的限制——方程[u · E ≈ h]的枢轴列是关于h的零空间假设被用上的地方。重用。Instance/Matr.v 的有限和库（[fin_sum] 及其同余，[fin_sum_zero]，[fin_sum_add]，双线性 [fin_sum_mul_l] / [fin_sum_mul_r] 和 Kronecker 折叠 [fin_sum_delta_l] / [fin_sum_delta_r]）以及 Instance/Matr/Determinant.v 的工具包（[fin_delete] 及 [fin_delete_neq]，[fin_delete_inj] 和三个计算规则；环算术 [ring_neg_mul_l]，[ring_neg_mul_r]，[ring_neg_zero] 和 [ring_neg_unique]；以及 [fin_sum_neg]）都已被使用，而不是重新推导。这个文件向该工具包添加了 [fin_delete_surj]（删除索引的补集正好是 [fin_delete] 的像）和 [fin_sum_delete]（有限和可以拆分为 p 点的项加上 p 的补集的和）——第二个才是真正的新求和引理，并且它使支点列可以被计算。Instance/FdVect/Tensor.v 有一个无关的引理，名为 [fin_sum_split]，关于拆分 [Fin.t (a + b)]；该文件在此不需要，并且名称不会冲突。测量的强度，严格优先。由 [eq_refl] 闭合：
   [matrix_is_hom]，[mat_mul_is_compose]，[mat_id_is_id]，
   [mat_equiv_is_homset_equiv]（矩阵上的本地 [Setoid] 实例是 [Matr K] 的同构集合，而不是并行逐点的），以及——使 [lnb_step] 变得便宜的两个——[mat_mul_col0_strict] 和 [mat_mul_tail_strict]，其中取乘积的第一列并乘入第一列给出相同的项，因此根本不需要引理。在 F₂ 上，维度、每个基条目、湮灭和所做示例的中介都由 [eq_refl] 闭合；在 ℚ 上，维度、基条目 −2 和 1 以及湮灭也由 [eq_refl] 闭合，有理数运算在闭合输入上进行约简。进行了四次严格尝试并被驳回。它们在此记录，而不是作为 [Fail] 探针，本文件不包含探针部分：
   (i) [mat_mul (mat_id a) A = A] ——该单位定律是真正的有限和计算，而不是转换，并且只有 [mat_mul_id_l] 的 [≈] 生效；(ii) [mat_sub A A = mat_zero] 同理；(iii) 使用树的 [F2_Field_dec] 替代 [f2_dec] 的 F₂ 维度检查，这正是发现上述不透明性的原因；以及 (iv) [lnb_basis f2_col_lnb = lnb_basis f2_ones_lnb]，在整体矩阵莱布尼茨等式下被驳回，尽管两者的两个条目值都相同——二者是通过不同次数的递归步骤生成的，所以它们是不同的闭合项但具有相同的值，而文件中的四个 [f2_*_basis_*] 示例固定了这些值。每个阴性样本都被去除了其 [Fail]，并确认是真正的转换失败，相对于相同参数下的阳性对照。

   两个工程发现。[Coq.QArith.QArith] 必须在 [Category.Lib] 之前要求——见导入块上方的评论；并且，按照 Determinant.v 的先例，该文件的部分设置了 [Default Proof Using “All”]，因为 [Kdec] 出现在证明（[find_nonzero]）中，但并未出现在相应的陈述中，所以下面的每个 [Qed] 引理都将 K 和 [Kdec] 作为其两个主要参数，即使 [Kdec] 未被使用。此文件未提供。没有秩函数，因此无法证明 [lnb_dim] = [m - rank M]；也没有声明 [lnb_dim] 与构造无关（维度的唯一性未说明，但可以从通用条款中推导出来，并且会是下一个自然的引理）；没有阶梯形式、标准形式以及主元列表，因此这里没有任何内容能够决定矩阵等价；没有右零空间，也没有基于转置的对偶（Instance/Matr.v 的转置函子会提供，但未使用）；关于 [Matr K] 作为一个范畴除了上面三处 [eq_refl] 的标识外，没有其他说明；也没有与任何余极限、余锥或商的词汇建立桥梁——那是下一个文件的内容，而不是这个文件的内容。
*)

(*
   * ** Index arithmetic

   Two facts about Determinant.v's [fin_delete] that its own file does
   not need.  Both are about [Fin.t] alone and mention no algebra, so
   they sit outside the section below. 

   --------
   * ** 索引算术

   关于 Determinant.v 的 [fin_delete] 有两个事实，它自身的文件不需要。
   两者都仅关于 [Fin.t]，并且不涉及任何代数，因此它们位于下面部分之外。
*)

(* [Fin.t 1] is a singleton. / [Fin.t 1] 是单例。 *)
Lemma fin1_F1 (j : Fin.t 1) : j = Fin.F1.
Proof.
  pattern j; apply (Fin.caseS' j); clear j.
  - reflexivity.
  - intro y; inversion y.
Qed.

(*
 [fin_delete p] is onto the complement of p: Determinant.v proves the
 image misses p and that the map is injective, but never that the two
 together exhaust the index set.  The witness is DATA (a [sigT]), which
 is what the pivot case analysis below consumes. 

 --------
 [fin_delete p] 映射到 p 的补集：Determinant.v 证明了像不包含 p 并且该映射是单射，但从未证明这两者一起覆盖了指标集。证明者是 DATA（一个 [sigT]），这正是下面的枢轴情况分析所使用的。
*)
Lemma fin_delete_surj {n : nat} (p j : Fin.t (S n)) :
  j ≠ p → { r : Fin.t n & fin_delete p r = j }.
Proof.
  revert p j; induction n as [|n1 IH]; intros p j.
  - intro Hne; exfalso; apply Hne.
    now rewrite (fin1_F1 j), (fin1_F1 p).
  - pattern p; apply (Fin.caseS' p); clear p.
    + pattern j; apply (Fin.caseS' j); clear j.
      * intro H; exfalso; now apply H.
      * intros y _; exists y; apply fin_delete_F1.
    + intro s.
      pattern j; apply (Fin.caseS' j); clear j.
      * intros _; exists Fin.F1; apply fin_delete_FS_F1.
      * intros y Hy.
        assert (Hys : y ≠ s) by (intro He; apply Hy; now rewrite He).
        destruct (IH s y Hys) as [r Hr].
        exists (Fin.FS r).
        now rewrite fin_delete_FS_FS, Hr.
Qed.

(* An index is either the pivot or lies in the image of [fin_delete]. / 一个索引要么是枢轴，要么位于 [fin_delete] 的像中。 *)
Lemma fin_pivot_cases {n : nat} (p j : Fin.t (S n)) :
  (j = p) + { r : Fin.t n & fin_delete p r = j }.
Proof.
  destruct (Fin.eq_dec j p) as [He|Hne].
  - left; exact He.
  - right; exact (fin_delete_surj p j Hne).
Qed.

Section Elimination.

(*
   * ** The base: a field with a zero test

   [Kdec] has the type Instance/Field.v's [field_dec_stable] takes; see
   the header for why no weaker hypothesis will do. 

   --------
   * ** 基础：带零测试的域

   [Kdec] 的类型是 Instance/Field.v 中 [field_dec_stable] 所采用的类型；请参阅标题了解为什么不采用更弱的假设。
*)

Context (K : FieldObject).
Context (Kdec : ∀ a b : carrier (rig_setoid K), (a ≈ b) + (a ≈ b → False)).

Set Default Proof Using "All".

Local Notation Kc := (carrier (rig_setoid K)).

Local Infix "⊕" := (rig_add K) (at level 50, left associativity).
Local Infix "⊗" := (rig_mul K) (at level 40, left associativity).
Local Notation "⊖ x" := (ring_neg K x) (at level 35, right associativity).
Local Notation "0K" := (rig_zero K).
Local Notation "1K" := (rig_one K).

(*
   * ** Matrix vocabulary

   Named here so that every statement below is in matrix terms; the
   three [eq_refl] identifications immediately after show that these
   names are [Matr K]'s own operations and not a parallel development. 

   --------
   * ** 矩阵词汇

   在此处命名，以便下面的每个陈述都是以矩阵术语表示的；
   紧随其后的三个 [eq_refl] 标识显示这些名称是 [Matr K] 自己的操作，而不是平行发展的结果。
*)

Definition mat_id (a : nat) : Matrix K a a := fun i j => delta K i j.

Definition mat_zero {a b : nat} : Matrix K a b := fun _ _ => 0K.

Definition mat_mul {a b c : nat} (A : Matrix K a b) (B : Matrix K b c) :
  Matrix K a c :=
  fun i j => fin_sum K (fun l : Fin.t b => A i l ⊗ B l j).

Definition mat_sub {a b : nat} (A B : Matrix K a b) : Matrix K a b :=
  fun i j => A i j ⊕ ⊖ (B i j).

(*
 Matrices are compared by [Matr K]'s own hom-setoid.  Declaring the
 instance rather than letting [fun_setoid] fire keeps the [≈] of this
 file and the [≈] of the category the SAME term.

 READ THAT PRECISELY, BECAUSE AN EARLIER DRAFT OVERSTATED IT AND AN
 AUDIT REFUTED THE OVERSTATEMENT BY EXPERIMENT.  The draft said this
 instance is NEEDED and that [matrix_is_hom]/[mat_equiv_is_homset_equiv]
 MEASURE the difference.  Neither is so.  The two setoids are
 CONVERTIBLE, so those Examples close by [eq_refl] with or without the
 instance, and deleting this declaration outright leaves the whole file
 compiling clean (rc=0, verified).  What the instance buys is that the
 two [≈]s are the same TERM rather than merely convertible ones, which
 keeps goals readable; it is a convenience, not a necessity, and
 nothing below is load-bearing on it. 

 --------
 矩阵通过 [Matr K] 自身的同态集合（hom-setoid）进行比较。声明该实例而不是让 [fun_setoid] 自动生成，可以保持该文件的 [≈] 与该范畴的 [≈] 为相同的项。仔细阅读，因为早期的草稿夸大了这一点，而一次审计通过实验驳斥了这种夸大。草稿中说这个实例是必需的，并且 [matrix_is_hom] / [mat_equiv_is_homset_equiv] 测量了差异。事实并非如此。这两个集合是可转换的，所以那些靠近 [eq_refl] 的例子无论是否有该实例都可以，而且直接删除这个声明整个文件仍能干净编译（rc=0，已验证）。该实例的作用是让两个 [≈] 是相同的项，而不仅仅是可转换的，这使得目标更加可读；它是一种便利，而非必要，以下内容并不依赖于它。
*)
#[local] Instance Matrix_Setoid {a b : nat} : Setoid (Matrix K a b) :=
  @homset (Matr K) b a.

Example matrix_is_hom (a b : nat) : Matrix K a b = (b ~{Matr K}~> a) :=
  eq_refl.

Example mat_mul_is_compose {a b c : nat}
  (A : Matrix K a b) (B : Matrix K b c) :
  mat_mul A B = @compose (Matr K) c b a A B := eq_refl.

Example mat_id_is_id (a : nat) : mat_id a = @id (Matr K) a := eq_refl.

Example mat_equiv_is_homset_equiv {a b : nat} (A B : Matrix K a b) :
  (A ≈ B) = (A ≈[Matr K] B) := eq_refl.

(*
   * ** Matrix algebra

   Associativity and the unit laws are the category's, cited by the
   identifications above.  Everything else is a finite-sum computation. 

   --------
   * ** 矩阵代数

   结合律和单位律是由上述标识引用的范畴法则。其余的一切都是有限和的计算。
*)

#[local] Instance mat_mul_respects {a b c : nat} :
  Proper (equiv ==> equiv ==> equiv) (@mat_mul a b c) :=
  @compose_respects (Matr K) c b a.

Lemma mat_mul_assoc {a b c d : nat} (A : Matrix K a b) (B : Matrix K b c)
  (C : Matrix K c d) :
  mat_mul (mat_mul A B) C ≈ mat_mul A (mat_mul B C).
Proof. exact (@comp_assoc_sym (Matr K) d c b a A B C). Qed.

Lemma mat_mul_id_l {a b : nat} (A : Matrix K a b) :
  mat_mul (mat_id a) A ≈ A.
Proof. exact (@id_left (Matr K) b a A). Qed.

Lemma mat_mul_id_r {a b : nat} (A : Matrix K a b) :
  mat_mul A (mat_id b) ≈ A.
Proof. exact (@id_right (Matr K) b a A). Qed.

Lemma mat_mul_zero_r {a b c : nat} (A : Matrix K a b) :
  mat_mul A (@mat_zero b c) ≈ mat_zero.
Proof.
  intros i j.
  transitivity (fin_sum K (fun _ : Fin.t b => 0K)).
  - apply fin_sum_respects; intro l; apply rig_mul_zero_r.
  - apply fin_sum_zero.
Qed.

Lemma mat_mul_zero_l {a b c : nat} (B : Matrix K b c) :
  mat_mul (@mat_zero a b) B ≈ mat_zero.
Proof.
  intros i j.
  transitivity (fin_sum K (fun _ : Fin.t b => 0K)).
  - apply fin_sum_respects; intro l; apply rig_mul_zero_l.
  - apply fin_sum_zero.
Qed.

(*
   * ** Finite sums: what the pivot needs beyond Instance/Matr.v

   [fin_sum_cons] is the unfolding step named as a rewrite rule (plain
   [simpl] would unfold the summand as well and leave the goal in a
   shape the [fin_sum] kit no longer matches — Determinant.v's
   [fin_sum_S] is the same device, restated here over a field so that no
   coercion has to be matched, and given a different name so that
   nothing of Determinant.v's is shadowed).  Additivity of negation
   over a finite sum is NOT restated: Determinant.v's [fin_sum_neg] is
   already stated for an arbitrary [RingObject] with an explicit
   [Proof using Type], so it costs no commutativity and is consumed as
   it stands.  [fin_sum_delete] is the genuinely new one: a sum over
   [Fin.t (S n)] splits as the term at p plus the sum over the
   complement of p, indexed through [fin_delete p]. 

   --------
   * ** 有限和：枢轴在 Instance/Matr.v 之外需要的内容

   [fin_sum_cons] 是作为重写规则命名的展开步骤（普通的 [simpl] 也会展开加数，并使目标保持在 [fin_sum] 工具包不再匹配的形态——Determinant.v 的 [fin_sum_S] 是相同的装置，这里在域上重新陈述，因此无需匹配任何强制类型转换，并且给了不同的名字，这样就不会遮蔽 Determinant.v 的任何内容）。对有限和的负号的加法性未重新陈述：Determinant.v 的 [fin_sum_neg] 已经为任意 [RingObject] 明确地陈述了 [Proof using Type]，所以它不需要交换性，并按原状使用。[fin_sum_delete] 是真正新的：对 [Fin.t (S n)] 的求和可以分为枢轴 p 的项加上对 p 的补集的求和，通过 [fin_delete p] 索引。
*)

Lemma fin_sum_cons {n : nat} (f : Fin.t (S n) → Kc) :
  fin_sum K f = f Fin.F1 ⊕ fin_sum K (fun i => f (Fin.FS i)).
Proof. reflexivity. Qed.

Lemma fin_sum_delete {n : nat} (f : Fin.t (S n) → Kc) (p : Fin.t (S n)) :
  fin_sum K f ≈ f p ⊕ fin_sum K (fun r => f (fin_delete p r)).
Proof.
  revert f p; induction n as [|n1 IH]; intros f p.
  - rewrite (fin1_F1 p); reflexivity.
  - pattern p; apply (Fin.caseS' p); clear p.
    + rewrite fin_sum_cons.
      apply rig_add_respects; [ reflexivity |].
      apply fin_sum_respects; intro r.
      now rewrite fin_delete_F1.
    + intro s.
      transitivity (f Fin.F1 ⊕ (f (Fin.FS s)
        ⊕ fin_sum K (fun r => f (Fin.FS (fin_delete s r))))).
      { rewrite fin_sum_cons.
        apply rig_add_respects; [ reflexivity |].
        exact (IH (fun i => f (Fin.FS i)) s). }
      transitivity (f (Fin.FS s) ⊕ (f Fin.F1
        ⊕ fin_sum K (fun r => f (Fin.FS (fin_delete s r))))).
      { rewrite <- !rig_add_assoc.
        apply rig_add_respects; [ apply rig_add_comm | reflexivity ]. }
      apply rig_add_respects; [ reflexivity |].
      rewrite fin_sum_cons.
      apply rig_add_respects.
      * now rewrite fin_delete_FS_F1.
      * apply fin_sum_respects; intro y.
        now rewrite fin_delete_FS_FS.
Qed.

(* Deleting the same index from both arguments leaves the Kronecker delta unchanged: injectivity of [fin_delete p] in one direction, and nothing at all in the other. / 从两个参数中删除相同的索引不会改变克罗内克δ：在一个方向上保持 [fin_delete p] 的单射性，而在另一个方向上则没有任何影响。 *)
Lemma delta_delete {n : nat} (p : Fin.t (S n)) (r s : Fin.t n) :
  delta K (fin_delete p r) (fin_delete p s) ≈ delta K r s.
Proof.
  destruct (Fin.eq_dec r s) as [He|Hne].
  - rewrite He, !delta_refl; reflexivity.
  - rewrite (delta_neq K r s Hne).
    apply delta_neq.
    intro Heq; apply Hne; exact (fin_delete_inj p r s Heq).
Qed.

(*
   * ** Searching for a pivot

   This is the ONLY place [Kdec] is consumed, and it is the whole reason
   the hypothesis is carried: elimination has to know whether a column
   vanishes identically before it can divide by anything.  The result is
   a [sum], so the pivot index is data and the search computes. 

   --------
   * ** 寻找枢轴

   这是唯一消耗 [Kdec] 的地方，也是该假设存在的全部原因：
   消元必须知道某一列是否恒为零，才能进行除法操作。结果是
   一个 [sum]，因此枢轴索引是数据，而搜索则用于计算。
*)

Definition find_nonzero : ∀ (n : nat) (c : Fin.t n → Kc),
  { i : Fin.t n & (c i ≈ 0K → False) } + (∀ i, c i ≈ 0K).
Proof.
  induction n as [|n1 IH]; intro c.
  - right; intro i; inversion i.
  - destruct (Kdec (c Fin.F1) 0K) as [Hz | Hnz].
    + destruct (IH (fun i => c (Fin.FS i))) as [[i Hi] | Hall].
      * left; exists (Fin.FS i); exact Hi.
      * right; intro i.
        pattern i; apply (Fin.caseS' i); [ exact Hz | exact Hall ].
    + left; exists Fin.F1; exact Hnz.
Defined.

(*
   * ** The pivot basis

   With a pivot entry [c p ≉ 0], the left null space of the column c is
   spanned by the m − 1 vectors [e_{d r} − (c_{d r} / c_p) · e_p], where
   [d := fin_delete p] runs over the complement of p.  Each is visibly
   killed by c, and together they are independent because the [d r]
   coordinate of the r-th one is 1 and of the others is 0. 

   --------
   * ** 基础枢轴

   对于枢轴元素 [c p ≉ 0]，列 c 的左零空间由 m − 1 个向量 [e_{d r} − (c_{d r} / c_p) · e_p] 张成，其中 [d := fin_delete p] 在 p 的补集上取值。每个向量显然被 c 消去，并且它们是独立的，因为第 r 个向量的 [d r] 坐标为 1，而其他向量的该坐标为 0。
*)

Definition pivot_coeff {m' : nat} (c : Fin.t (S m') → Kc)
  (p : Fin.t (S m')) (r : Fin.t m') : Kc :=
  c (fin_delete p r) ⊗ finv K (c p).

Definition pivot_basis {m' : nat} (c : Fin.t (S m') → Kc)
  (p : Fin.t (S m')) : Matrix K m' (S m') :=
  fun r j => delta K (fin_delete p r) j
             ⊕ ⊖ (pivot_coeff c p r ⊗ delta K p j).

(* Multiplying row r of the pivot basis into an arbitrary column g: the delta collapses pick out the [d r] and p entries of g. / 将枢轴基的第 r 行乘到任意列 g 上：delta 折叠会挑选出 g 的 [d r] 和 p 条目。 *)
Lemma fin_sum_pivot_row {m' : nat} (c : Fin.t (S m') → Kc)
  (p : Fin.t (S m')) (r : Fin.t m') (g : Fin.t (S m') → Kc) :
  fin_sum K (fun l => pivot_basis c p r l ⊗ g l)
    ≈ g (fin_delete p r) ⊕ ⊖ (pivot_coeff c p r ⊗ g p).
Proof.
  transitivity (fin_sum K (fun l => delta K (fin_delete p r) l ⊗ g l)
                ⊕ fin_sum K (fun l =>
                    ⊖ ((pivot_coeff c p r ⊗ delta K p l) ⊗ g l))).
  { rewrite <- fin_sum_add.
    apply fin_sum_respects; intro l.
    unfold pivot_basis.
    rewrite rig_distr_r.
    apply rig_add_respects; [ reflexivity |].
    apply ring_neg_mul_l. }
  apply rig_add_respects; [ apply fin_sum_delta_l |].
  assert (HX : fin_sum K (fun l =>
                 (pivot_coeff c p r ⊗ delta K p l) ⊗ g l)
               ≈ pivot_coeff c p r ⊗ g p).
  { transitivity (pivot_coeff c p r
                  ⊗ fin_sum K (fun l => delta K p l ⊗ g l)).
    - rewrite fin_sum_mul_l.
      apply fin_sum_respects; intro l.
      apply rig_mul_assoc.
    - apply rig_mul_respects; [ reflexivity |].
      apply fin_sum_delta_l. }
  rewrite fin_sum_neg, HX.
  reflexivity.
Qed.

(*
 Every row of the pivot basis kills the column it was built from —
 this is where [finv_l] is spent, and where [Hp] pays for its guard. 

 --------
 枢轴基的每一行都会消除它所构建的列——这是 [finv_l] 被消耗的地方，也是 [Hp] 为其保护付出的地方。
*)
Lemma pivot_basis_annihilates {m' : nat} (c : Fin.t (S m') → Kc)
  (p : Fin.t (S m')) (Hp : c p ≈ 0K → False) (r : Fin.t m') :
  fin_sum K (fun l => pivot_basis c p r l ⊗ c l) ≈ 0K.
Proof.
  rewrite fin_sum_pivot_row.
  unfold pivot_coeff.
  rewrite rig_mul_assoc.
  rewrite (finv_l K (c p) Hp).
  rewrite rig_mul_one_r.
  apply ring_neg_r.
Qed.

(* The pivot column of a combination of the basis rows. / 一组基行的组合的主元列。 *)
Lemma pivot_col_pivot {m' : nat} (c : Fin.t (S m') → Kc)
  (p : Fin.t (S m')) (v : Fin.t m' → Kc) :
  fin_sum K (fun r => v r ⊗ pivot_basis c p r p)
    ≈ ⊖ (fin_sum K (fun r => v r ⊗ pivot_coeff c p r)).
Proof.
  rewrite <- fin_sum_neg.
  apply fin_sum_respects; intro r.
  unfold pivot_basis.
  rewrite (delta_neq K (fin_delete p r) p (fin_delete_neq p r)).
  rewrite delta_refl, rig_mul_one_r, rig_add_zero_l.
  apply ring_neg_mul_r.
Qed.

(*
 Every other column of a combination of the basis rows reads off the
 corresponding coefficient — this is the independence half. 

 --------
 基底行组合的每隔一列都会读出对应的系数 —— 这是独立性部分。
*)
Lemma pivot_col_other {m' : nat} (c : Fin.t (S m') → Kc)
  (p : Fin.t (S m')) (v : Fin.t m' → Kc) (r0 : Fin.t m') :
  fin_sum K (fun r => v r ⊗ pivot_basis c p r (fin_delete p r0)) ≈ v r0.
Proof.
  transitivity (fin_sum K (fun r => v r ⊗ delta K r r0)).
  - apply fin_sum_respects; intro r.
    apply rig_mul_respects; [ reflexivity |].
    unfold pivot_basis.
    rewrite (delta_neq K p (fin_delete p r0)
               (fun H => fin_delete_neq p r0 (eq_sym H))).
    rewrite rig_mul_zero_r, ring_neg_zero, rig_add_zero_r.
    apply delta_delete.
  - apply fin_sum_delta_r.
Qed.

(*
 The pivot column of the mediator's image.  This is the one place the
 hypothesis “h kills the column” is spent, and it is spent through
 [fin_sum_delete]: the sum over all indices splits at p, so the sum
 over the complement is exactly the negative of the p-th term. 

 --------
 中介者图像的主柱列。这是“h 消去该列”的假设被使用的唯一地方，它是通过 [fin_sum_delete] 而使用的：对所有索引的求和在 p 处分裂，因此补集的求和正好是第 p 项的负值。
*)
Lemma pivot_mediator_pivot_col {m' z : nat} (c : Fin.t (S m') → Kc)
  (p : Fin.t (S m')) (Hp : c p ≈ 0K → False) (h : Matrix K z (S m'))
  (Hh : ∀ a, fin_sum K (fun l => h a l ⊗ c l) ≈ 0K) (a : Fin.t z) :
  fin_sum K (fun r => h a (fin_delete p r) ⊗ pivot_basis c p r p)
    ≈ h a p.
Proof.
  rewrite pivot_col_pivot.
  assert (Hsum : fin_sum K (fun r =>
                   h a (fin_delete p r) ⊗ pivot_coeff c p r)
                 ≈ ⊖ (h a p ⊗ c p) ⊗ finv K (c p)).
  { transitivity (fin_sum K (fun r =>
        (h a (fin_delete p r) ⊗ c (fin_delete p r)) ⊗ finv K (c p))).
    - apply fin_sum_respects; intro r.
      unfold pivot_coeff.
      symmetry; apply rig_mul_assoc.
    - rewrite <- fin_sum_mul_r.
      apply rig_mul_respects; [| reflexivity ].
      apply (ring_neg_unique K).
      transitivity (fin_sum K (fun l => h a l ⊗ c l)).
      + symmetry; apply (fin_sum_delete (fun l => h a l ⊗ c l) p).
      + apply Hh. }
  rewrite Hsum, ring_neg_mul_l, ring_neg_involutive, rig_mul_assoc.
  rewrite (finv_r K (c p) Hp).
  apply rig_mul_one_r.
Qed.

(*
   * ** Splitting off the first column

   A row vector kills M exactly when it kills the first column and
   kills the remaining ones; [mat_col0] and [mat_tail] name the two
   halves.  The two [eq_refl] Examples are the reason [lnb_step] is
   cheap: taking the first column of a product and multiplying into the
   first column are THE SAME TERM, not merely equivalent matrices, and
   likewise for the tail.  The [≈] restatements exist only so that
   [rewrite] has something to match. 

   --------
   * ** 分离第一列

   当一个行向量恰好能够消去第一列并且消去剩下的列时，它就消去了矩阵 M；[mat_col0] 和 [mat_tail] 表示这两个部分。两个 [eq_refl] 示例说明了 [lnb_step] 的低成本原因：取一个乘积的第一列并乘入第一列是相同的项，而不仅仅是等价矩阵，尾部的情况也是如此。[≈] 的重述存在仅仅是为了让 [rewrite] 有可匹配的对象。
*)

Definition mat_col0 {m n : nat} (M : Matrix K m (S n)) : Matrix K m 1 :=
  fun i _ => M i Fin.F1.

Definition mat_tail {m n : nat} (M : Matrix K m (S n)) : Matrix K m n :=
  fun i j => M i (Fin.FS j).

Example mat_mul_col0_strict {z m n : nat} (h : Matrix K z m)
  (M : Matrix K m (S n)) :
  mat_col0 (mat_mul h M) = mat_mul h (mat_col0 M) := eq_refl.

Example mat_mul_tail_strict {z m n : nat} (h : Matrix K z m)
  (M : Matrix K m (S n)) :
  mat_tail (mat_mul h M) = mat_mul h (mat_tail M) := eq_refl.

Lemma mat_mul_col0 {z m n : nat} (h : Matrix K z m)
  (M : Matrix K m (S n)) :
  mat_col0 (mat_mul h M) ≈ mat_mul h (mat_col0 M).
Proof. intros a j; reflexivity. Qed.

Lemma mat_mul_tail {z m n : nat} (h : Matrix K z m)
  (M : Matrix K m (S n)) :
  mat_tail (mat_mul h M) ≈ mat_mul h (mat_tail M).
Proof. intros a j; reflexivity. Qed.

Lemma col0_of_zero {a n : nat} (X : Matrix K a (S n)) :
  X ≈ mat_zero → mat_col0 X ≈ mat_zero.
Proof. intros H i j; exact (H i Fin.F1). Qed.

Lemma tail_of_zero {a n : nat} (X : Matrix K a (S n)) :
  X ≈ mat_zero → mat_tail X ≈ mat_zero.
Proof. intros H i j; exact (H i (Fin.FS j)). Qed.

Lemma zero_of_col0_tail {a n : nat} (X : Matrix K a (S n)) :
  mat_col0 X ≈ mat_zero → mat_tail X ≈ mat_zero → X ≈ mat_zero.
Proof.
  intros H0 H1 i j.
  pattern j; apply (Fin.caseS' j); clear j.
  - exact (H0 i Fin.F1).
  - intro y; exact (H1 i y).
Qed.

Lemma zero_cols {m : nat} (M : Matrix K m 0) : M ≈ mat_zero.
Proof. intros i j; inversion j. Qed.

(*
   * ** The specification

   [E] is a basis of the left null space of M: its rows are killed by M
   ([lnb_annih]) and every row vector killed by M is a UNIQUE
   combination of them ([lnb_univ]) — existence is spanning,
   uniqueness is linear independence.  Nothing here mentions a colimit,
   a cocone or a quotient; the record speaks of [mat_mul] and
   [mat_zero] and of nothing else. 

   --------
   * ** 规格

   [E] 是矩阵 M 左零空间的一个基：它的行被 M（[lnb_annih]）消去，并且被 M 消去的每一个行向量都是它们的唯一组合（[lnb_univ]）——存在性是关于张成，唯一性是线性无关。这里没有提到余极限、余锥或商；记录只谈到了 [mat_mul] 和 [mat_zero]，别无他物。
*)

Record LeftNullBasis {m n : nat} (M : Matrix K m n) : Type := {
  lnb_dim : nat;
  lnb_basis : Matrix K lnb_dim m;
  lnb_annih : mat_mul lnb_basis M ≈ mat_zero;
  lnb_univ : ∀ (z : nat) (h : Matrix K z m),
    mat_mul h M ≈ mat_zero →
    ∃! u : Matrix K z lnb_dim, mat_mul u lnb_basis ≈ h
}.

Arguments lnb_dim {m n M} _.
Arguments lnb_basis {m n M} _.
Arguments lnb_annih {m n M} _.
Arguments lnb_univ {m n M} _ _ _ _.

(*
   * ** The degenerate case: a matrix that vanishes

   If M is the zero matrix every row vector is in its left null space,
   so the identity matrix is a basis.  This covers both the
   no-columns base case of the recursion and the column that vanishes
   identically. 

   --------
   * ** 退化情况：消失的矩阵

   如果 M 是零矩阵，则每个行向量都在它的左零空间中，
   因此单位矩阵是一个基。这涵盖了递归的无列基本情况以及完全消失的一列。
*)

Definition lnb_id {m n : nat} (M : Matrix K m n) (Hz : M ≈ mat_zero) :
  LeftNullBasis M.
Proof.
  refine {| lnb_dim := m; lnb_basis := mat_id m |}.
  - rewrite mat_mul_id_l; exact Hz.
  - intros z h _.
    refine {| unique_obj := h |}.
    + apply mat_mul_id_r.
    + intros v Hv.
      transitivity (mat_mul v (mat_id m)).
      * symmetry; exact Hv.
      * apply mat_mul_id_r.
Defined.

(*
   * ** One column

   The single-column case is the whole content of elimination: either
   the column vanishes, and the identity is a basis, or a pivot exists
   and the m − 1 vectors of [pivot_basis] are one.  The mediator is
   RESTRICTION along [fin_delete p]. 

   --------
   * ** 单列

   单列情况是消元的全部内容：要么列消失，恒等式成为基， 要么存在主元，并且  [pivot_basis] 的 m − 1 个向量为一。 中介是沿  [fin_delete p] 的 RESTRICTION 。
*)

Definition col_null_basis :
  ∀ (m : nat) (C : Matrix K m 1), LeftNullBasis C.
Proof.
  intro m; destruct m as [|m']; intro C.
  - apply (lnb_id C).
    intros i j; inversion i.
  - destruct (find_nonzero (S m') (fun i => C i Fin.F1))
      as [[p Hp] | Hall].
    + refine {| lnb_dim := m';
                lnb_basis := pivot_basis (fun i => C i Fin.F1) p |}.
      * intros r j.
        rewrite (fin1_F1 j).
        exact (pivot_basis_annihilates (fun i => C i Fin.F1) p Hp r).
      * intros z h Hh.
        assert (Hcol : ∀ a, fin_sum K
                        (fun l => h a l ⊗ C l Fin.F1) ≈ 0K)
          by (intro a; exact (Hh a Fin.F1)).
        refine {| unique_obj :=
                    fun a r => h a (fin_delete p r) |}.
        -- intros a j.
           destruct (fin_pivot_cases p j) as [He | [r0 Hr0]].
           ++ rewrite He.
              exact (pivot_mediator_pivot_col
                       (fun i => C i Fin.F1) p Hp h Hcol a).
           ++ rewrite <- Hr0.
              exact (pivot_col_other (fun i => C i Fin.F1) p
                       (fun r => h a (fin_delete p r)) r0).
        -- intros v Hv a r.
           symmetry.
           transitivity (fin_sum K (fun s =>
             v a s ⊗ pivot_basis (fun i => C i Fin.F1) p s
                       (fin_delete p r))).
           ++ symmetry; apply pivot_col_other.
           ++ exact (Hv a (fin_delete p r)).
    + apply (lnb_id C).
      intros i j; rewrite (fin1_F1 j); exact (Hall i).
Defined.

(*
   * ** One column at a time

   A row vector kills M exactly when it kills the first column and the
   rest.  So if E1 is a basis for the first column and E2 is a basis
   for [E1 · tail M], then [E2 · E1] is a basis for M: annihilation is
   associativity, and the mediator for h is obtained by mediating twice,
   which is also why it is unique. 

   --------
   * ** 一次一列

   当一个行向量消去 M 时，它恰好消去了第一列和剩下的部分。因此，如果 E1 是第一列的一个基，而 E2 是 [E1 · tail M] 的一个基，那么 [E2 · E1] 是 M 的一个基：消去是结合的，h 的中介是通过两次中介得到的，这也是它唯一性的原因。
*)

Definition lnb_step {m n : nat} (M : Matrix K m (S n))
  (B1 : LeftNullBasis (mat_col0 M))
  (B2 : LeftNullBasis (mat_mul (lnb_basis B1) (mat_tail M))) :
  LeftNullBasis M.
Proof.
  refine {| lnb_dim := lnb_dim B2;
            lnb_basis := mat_mul (lnb_basis B2) (lnb_basis B1) |}.
  - apply zero_of_col0_tail.
    + rewrite mat_mul_col0, mat_mul_assoc, (lnb_annih B1).
      apply mat_mul_zero_r.
    + rewrite mat_mul_tail, mat_mul_assoc.
      exact (lnb_annih B2).
  - intros z h Hh.
    assert (H0 : mat_mul h (mat_col0 M) ≈ mat_zero).
    { rewrite <- mat_mul_col0.
      apply col0_of_zero; exact Hh. }
    assert (H1 : mat_mul (unique_obj (lnb_univ B1 z h H0))
                   (mat_mul (lnb_basis B1) (mat_tail M)) ≈ mat_zero).
    { rewrite <- mat_mul_assoc.
      rewrite (unique_property (lnb_univ B1 z h H0)).
      rewrite <- mat_mul_tail.
      apply tail_of_zero; exact Hh. }
    refine {| unique_obj := unique_obj (lnb_univ B2 z _ H1) |}.
    + rewrite <- mat_mul_assoc.
      rewrite (unique_property (lnb_univ B2 z _ H1)).
      exact (unique_property (lnb_univ B1 z h H0)).
    + intros v Hv.
      apply (uniqueness (lnb_univ B2 z _ H1)).
      symmetry.
      apply (uniqueness (lnb_univ B1 z h H0)).
      rewrite mat_mul_assoc; exact Hv.
Defined.

(*
   * ** The construction

   Recursion on the number of columns.  Every step consumes one column
   through [col_null_basis] and hands the rest, pushed through the
   basis found so far, to the recursive call. 

   --------
   * ** 构造

   对列数进行递归。每一步通过 [col_null_basis] 消耗一列
   并将剩余部分通过到目前为止找到的基底，
   然后传递给递归调用。
*)

Fixpoint lnb_rec (n : nat) :
  ∀ (m : nat) (M : Matrix K m n), LeftNullBasis M :=
  match n with
  | O => fun m M => lnb_id M (zero_cols M)
  | S n' => fun m M =>
      let B1 := col_null_basis m (mat_col0 M) in
      lnb_step M B1
        (lnb_rec n' (lnb_dim B1)
           (mat_mul (lnb_basis B1) (mat_tail M)))
  end.

(* THE HEADLINE: every matrix over a field with a zero test has a basis of its left null space, with the universal clause. / 标题：每个带有零测试的域上的矩阵都有其左零空间的一个基，并带有通用条款。 *)
Definition left_null_basis {m n : nat} (M : Matrix K m n) :
  LeftNullBasis M := lnb_rec n m M.

(*
   * ** The difference form

   A row vector h satisfies [h · A ≈ h · B] exactly when it kills
   [A − B].  That translation is what turns a basis of a left null
   space into a solution of the two-matrix problem, and it is the last
   thing this file says; the two statements are equivalent by ordinary
   matrix algebra, and no further vocabulary is introduced. 

   --------
   * ** 差分形式

   一个行向量 h 在且仅在它消去 [A − B] 时满足 [h · A ≈ h · B]。这个变换就是将左零空间的一个基变为两个矩阵问题的解，而这是本文件最后提到的内容；根据普通矩阵代数，这两个陈述是等价的，并且没有引入更多的术语。
*)

Lemma mat_mul_sub_r {a b c : nat} (h : Matrix K a b)
  (A B : Matrix K b c) :
  mat_mul h (mat_sub A B) ≈ mat_sub (mat_mul h A) (mat_mul h B).
Proof.
  intros i j.
  transitivity (fin_sum K (fun l =>
                  h i l ⊗ A l j ⊕ ⊖ (h i l ⊗ B l j))).
  - apply fin_sum_respects; intro l.
    unfold mat_sub.
    rewrite rig_distr_l.
    apply rig_add_respects; [ reflexivity |].
    apply ring_neg_mul_r.
  - rewrite fin_sum_add.
    apply rig_add_respects; [ reflexivity |].
    apply fin_sum_neg.
Qed.

Lemma mat_sub_zero {a b : nat} (A B : Matrix K a b) :
  (mat_sub A B ≈ mat_zero) ↔ (A ≈ B).
Proof.
  split.
  - intros H i j.
    assert (Hij : A i j ⊕ ⊖ (B i j) ≈ 0K) by exact (H i j).
    transitivity (A i j ⊕ (⊖ (B i j) ⊕ B i j)).
    + rewrite (ring_neg_l K (B i j)), rig_add_zero_r; reflexivity.
    + rewrite <- rig_add_assoc, Hij, rig_add_zero_l; reflexivity.
  - intros H i j.
    change (A i j ⊕ ⊖ (B i j) ≈ 0K).
    rewrite (H i j).
    apply ring_neg_r.
Qed.

Theorem mat_mul_sub_zero_iff {a b c : nat} (h : Matrix K a b)
  (A B : Matrix K b c) :
  (mat_mul h (mat_sub A B) ≈ mat_zero) ↔ (mat_mul h A ≈ mat_mul h B).
Proof.
  split; intro H.
  - apply (fst (mat_sub_zero (mat_mul h A) (mat_mul h B))).
    rewrite <- mat_mul_sub_r; exact H.
  - rewrite mat_mul_sub_r.
    apply (snd (mat_sub_zero (mat_mul h A) (mat_mul h B))); exact H.
Qed.

(*
 The two-matrix statement, packaged with no reference to [mat_sub]:
 for any parallel pair there is a matrix E equalizing them on the left
 through which every left-equalizing matrix factors uniquely.  This is
 the whole of what the elimination engine is for. 

 --------
 这个二矩阵陈述，打包时没有涉及 [mat_sub]：对于任意平行对，存在一个矩阵 E 在左侧使它们相等，通过这个矩阵，每个左侧相等化矩阵都可以唯一分解。这就是消元引擎的全部用途。
*)
Theorem left_null_basis_diff {m n : nat} (A B : Matrix K m n) :
  { k : nat & { E : Matrix K k m &
      (mat_mul E A ≈ mat_mul E B) ∧
      (∀ (z : nat) (h : Matrix K z m), mat_mul h A ≈ mat_mul h B →
        ∃! u : Matrix K z k, mat_mul u E ≈ h) } }.
Proof.
  pose (Bs := left_null_basis (mat_sub A B)).
  exists (lnb_dim Bs), (lnb_basis Bs).
  split.
  - apply (fst (mat_mul_sub_zero_iff (lnb_basis Bs) A B)).
    exact (lnb_annih Bs).
  - intros z h Hh.
    apply (lnb_univ Bs z h).
    apply (snd (mat_mul_sub_zero_iff h A B)); exact Hh.
Qed.

End Elimination.

(*
 The field is recoverable from a [LeftNullBasis] but not from a bare
 matrix ([Matrix] is indexed by the underlying RIG), so K stays
 explicit on the matrix operations and becomes implicit on the record's
 projections. 

 --------
 该字段可以从 [LeftNullBasis] 中恢复，但不能从裸矩阵中恢复（[Matrix] 是由底层 RIG 索引的），因此 K 在矩阵操作上保持显式，而在记录的投影上变为隐式。
*)
Arguments LeftNullBasis K {m n} _.
Arguments lnb_dim {K m n M} _.
Arguments lnb_basis {K m n M} _.
Arguments lnb_annih {K m n M} _.
Arguments lnb_univ {K m n M} _ _ _ _.

(*
   * ** The deciders, and why the in-tree ones are re-proved here

   [F2_Field_dec] and [Q_Field_dec] (Instance/Field.v) inhabit the
   hypothesis EXACTLY — the two ascriptions below record that, and they
   are what makes the section variable [Kdec] the tree's own notion and
   not a new one.  But both are [Qed] lemmas, so no application of
   either reduces, and the elimination engine — which matches on the
   decider's answer to find a pivot — computes with neither.  This was
   MEASURED, not anticipated: with [F2_Field_dec] supplied, the check
   [lnb_dim f2_col_lnb = 1%nat] is rejected by [eq_refl] with “cannot
   unify [lnb_dim f2_col_lnb] and [1%nat]”.  The two transparent copies
   below decide the same relations by the same case analyses and differ
   only in ending with [Defined]; they are what the computing witnesses
   run on.  The opacity is Instance/Field.v's, is NOT repaired here, and
   nothing above depends on it being repaired — the construction is
   correct with either. 

   --------
   * ** 决策者，以及为什么树内的决策者在这里被重新证明[F2_Field_dec] 和 [Q_Field_dec]（Instance/Field.v）完全符合假设——下面的两个赋值记录了这一点，它们使得区段变量 [Kdec] 成为树自身的概念，而不是一个新的概念。但两者都是 [Qed] 引理，所以无论使用哪一个都不会简化，而消除引擎——它通过匹配判定器的答案来找到枢轴——对两者都不进行计算。这是被测量的，而非预期的：在提供 [F2_Field_dec] 的情况下，检查 [lnb_dim f2_col_lnb = 1%nat] 被 [eq_refl] 拒绝，并提示“无法统一 [lnb_dim f2_col_lnb] 和 [1%nat]”。下面的两个透明副本通过相同的案例分析决定相同的关系，只是在结尾以 [Defined] 结束；它们是计算证人的运行对象。不透明度是 Instance/Field.v 的，这里没有修复，并且上面的任何东西都不依赖它被修复——无论哪种情况，构造都是正确的。
*)

Definition F2_dec_inhabits :
  ∀ a b : carrier (rig_setoid F2_Field), (a ≈ b) + (a ≈ b → False) :=
  F2_Field_dec.

Definition Q_dec_inhabits :
  ∀ a b : carrier (rig_setoid Q_Field), (a ≈ b) + (a ≈ b → False) :=
  Q_Field_dec.

Definition f2_dec (a b : carrier (rig_setoid F2_Field)) :
  (a ≈ b) + (a ≈ b → False).
Proof.
  destruct a, b; solve [ left; reflexivity | right; discriminate ].
Defined.

Definition q_dec (a b : carrier (rig_setoid Q_Field)) :
  (a ≈ b) + (a ≈ b → False).
Proof.
  destruct (Qeq_dec a b) as [H | H]; [ left | right ]; exact H.
Defined.

(*
   * ** Witnesses over F₂

   [F2_Field] (Instance/Field.v) is the cheapest base at which every
   step of the construction computes: the carrier is [bool] with
   Leibniz equality, the decider is a two-way case analysis, and the
   field operations are [xorb] and [andb].  Each check below closes by
   [eq_refl], so the elimination engine is not merely inhabited, it
   RUNS. 

   --------
   * ** F₂ 上的证人

   [F2_Field]（Instance/Field.v）是每一步构造都能计算的最便宜的基础：载体是 [bool]，并带有莱布尼茨等式，判定器是双向分支分析，域运算是 [xorb] 和 [andb]。下面的每个检查都由 [eq_refl] 结束，因此消除引擎不仅是可居住的，它还能运行。
*)

(* The 2 × 1 column (1, 1). Its left null space is the line spanned by (1, 1) — over F₂ that is the only nonzero vector killing it. / 这个 2 × 1 列向量是 (1, 1)。它的左零空间是由 (1, 1) 张成的直线——在 F₂ 上，这是唯一使它为零的非零向量。 *)
Definition f2_col : Matrix F2_Field 2 1 := fun _ _ => true.

Definition f2_col_lnb : LeftNullBasis F2_Field f2_col :=
  left_null_basis F2_Field f2_dec f2_col.

Example f2_col_dim : lnb_dim f2_col_lnb = 1%nat := eq_refl.

Example f2_col_basis_0 :
  lnb_basis f2_col_lnb Fin.F1 Fin.F1 = true := eq_refl.

Example f2_col_basis_1 :
  lnb_basis f2_col_lnb Fin.F1 (Fin.FS Fin.F1) = true := eq_refl.

(* The annihilation, COMPUTED rather than cited: 1·1 + 1·1 = 0 in F₂. / 消灭，计算得出而非引用：1·1 + 1·1 = 0 在 F₂ 中。 *)
Example f2_col_annih_computes :
  mat_mul F2_Field (lnb_basis f2_col_lnb) f2_col Fin.F1 Fin.F1 = false :=
  eq_refl.

(*
 The universal clause is not vacuous.  The row vector (1, 1) kills the
 column, so it must factor through the basis, and the mediator the
 construction produces is the 1 × 1 matrix (1) — computed. 

 --------
 全称子句不是空的。行向量 (1, 1) 消去列，因此它必须通过基底进行分解，而构造产生的中介是 1 × 1 矩阵 (1)——已计算。
*)
Definition f2_h : Matrix F2_Field 1 2 := fun _ _ => true.

Lemma f2_h_kills : mat_mul F2_Field f2_h f2_col ≈ mat_zero F2_Field.
Proof. intros i j; reflexivity. Qed.

(* Stated without an ascription: writing the [∃!] out again would elaborate [f2_col_lnb] at fresh universes and the two would not unify — measured, and the reason the type is left inferred. / 未加归属地陈述：再次写出 [∃!] 会在新的宇宙中展开 [f2_col_lnb]，而二者不会统一——经过测量，这也是类型保持推断的原因。 *)
Definition f2_mediator := lnb_univ f2_col_lnb 1 f2_h f2_h_kills.

Example f2_mediator_computes :
  unique_obj f2_mediator Fin.F1 Fin.F1 = true := eq_refl.

(*
 The dimension responds to the matrix, which is what makes the search
 for a pivot load-bearing: the 2 × 2 identity has NO nonzero row
 vector in its left null space... 

 --------
 维度对矩阵做出响应，这就是为什么寻找支点是承重的原因：2 × 2 单位矩阵在其左零空间中没有非零行向量...
*)
Definition f2_id2 : Matrix F2_Field 2 2 :=
  fun i j => delta F2_Field i j.

Example f2_id2_dim :
  lnb_dim (left_null_basis F2_Field f2_dec f2_id2) = 0%nat :=
  eq_refl.

(*
 ...while the all-ones 2 × 2 matrix, whose two columns coincide, has a
 one-dimensional one, spanned again by (1, 1). 

 --------
 ...而全为 1 的 2 × 2 矩阵，其两列相同，其一维的特征空间再次由 (1, 1) 张成。
*)
Definition f2_ones : Matrix F2_Field 2 2 := fun _ _ => true.

Definition f2_ones_lnb : LeftNullBasis F2_Field f2_ones :=
  left_null_basis F2_Field f2_dec f2_ones.

Example f2_ones_dim : lnb_dim f2_ones_lnb = 1%nat := eq_refl.

Example f2_ones_basis_0 :
  lnb_basis f2_ones_lnb Fin.F1 Fin.F1 = true := eq_refl.

Example f2_ones_basis_1 :
  lnb_basis f2_ones_lnb Fin.F1 (Fin.FS Fin.F1) = true := eq_refl.

(*
   * ** A witness over ℚ

   [Q_Field] with this file's own TRANSPARENT [q_dec] -- not the
   Qed-opaque [Q_Field_dec]; an earlier draft of this sentence named the
   latter, contradicting THE DECIDERS above -- is a base in
   which the pivot DIVISION does something: the basis vector of the
   column (1, 2) is (−2, 1), and the coefficient −2 is produced by
   [finv], not by a case analysis.  The entries close by [eq_refl] as
   well, the rational arithmetic reducing on closed input. 

   --------
   * ** 在 ℚ 上的一个证人

   [Q_Field] 使用这个文件自身的 TRANSPARENT [q_dec] —— 而不是 Qed-opaque [Q_Field_dec]；该句子的早期版本提到了后者，与上面的 DECIDERS 相矛盾 —— 是一个基础，其中枢轴 DIVISION 做了一些事情：列 (1, 2) 的基向量是 (−2, 1)，系数 −2 是由 [finv] 产生的，而不是通过案例分析。附近的条目也在 [eq_refl] 中，封闭输入上的有理算术被减少。
*)

Definition q_col : Matrix Q_Field 2 1 :=
  fun i _ => match i with
             | Fin.F1 => 1%Q
             | _ => 2%Q
             end.

Definition q_col_lnb : LeftNullBasis Q_Field q_col :=
  left_null_basis Q_Field q_dec q_col.

Example q_col_dim : lnb_dim q_col_lnb = 1%nat := eq_refl.

Example q_col_basis_0 :
  lnb_basis q_col_lnb Fin.F1 Fin.F1 = (-2 # 1)%Q := eq_refl.

Example q_col_basis_1 :
  lnb_basis q_col_lnb Fin.F1 (Fin.FS Fin.F1) = (1 # 1)%Q := eq_refl.

(* (−2)·1 + 1·2 = 0, computed in ℚ. / (-2)·1 + 1·2 = 0，在有理数 ℚ 中计算。 *)
Example q_col_annih_computes :
  mat_mul Q_Field (lnb_basis q_col_lnb) q_col Fin.F1 Fin.F1
    = (0 # 1)%Q := eq_refl.
