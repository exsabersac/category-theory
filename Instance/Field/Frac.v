Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Frac.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Field.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 NAME COLLISION, recorded because it is silent and the error it
 produces names neither culprit.  [Coq.QArith.QArith] transitively
 exports [Stdlib.setoid_ring.Field_theory.num] — the numerator of the
 [linear] datatype of the [field] tactic — which SHADOWS
 Instance/Rng/Frac.v's [num].  Its [den] is not shadowed, so the
 symptom is a type error mentioning [linear] on the numerator alone.
 Rather than depend on the order of two [Require Import]s, the
 fraction numerator is bound here explicitly; the same family as the
 [equiv] shadowing recorded in Instance/FdVect.v. 

 --------
 名称冲突，被记录下来是因为它是静默的，并且它产生的错误没有指明哪个是肇事者。[Coq.QArith.QArith] 间接导出 [Stdlib.setoid_ring.Field_theory.num] —— [field] 策略的 [linear] 数据类型的分子 —— 它遮蔽了 Instance/Rng/Frac.v 中的 [num] 。它的 [den] 没有被遮蔽，因此症状是在分子上单独提到 [linear] 的类型错误。与其依赖两个 [Require Import] 的顺序，这里的分数分子被显式绑定；与 Instance/FdVect.v 中记录的 [equiv] 遮蔽属于同一个系列。
*)
#[local] Notation num := Frac.num.

(*
   * * The field of quotients as a universal arrow, and Mac Lane's
   non-example

   Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   §III.1 (Universal Arrows), printed pp. 55-56
   [maclane:III.1:construction2]: for an integral domain D, the field
   of quotients Q(D) together with the embedding n ↦ n/1 is a
   universal arrow from D to the forgetful functor from fields to
   integral domains — PROVIDED the domain category is taken to have
   monomorphisms as its arrows.  Mac Lane's accompanying remark is the
   half with the content: over the category of integral domains and
   ALL homomorphisms there is no universal arrow from ℤ at all,
   because the reductions ℤ → ℤ/pℤ cannot be routed through one fixed
   field.
   nLab: https://ncatlab.org/nlab/show/field+of+fractions
   nLab: https://ncatlab.org/nlab/show/universal+construction

   The construction is the oldest universal property in algebra —
   Grassmann and Hamilton built ℚ from ℤ this way long before anyone
   called it universal — and it is the example by which the notion is
   usually first motivated, precisely because the wrong choice of
   morphisms destroys it.  That sensitivity is the point: the
   extension of f : D → K to Q(D) sends n/d to f(n)·(f d)⁻¹, so it
   needs f d invertible for every d ≉ 0, i.e. it needs f to REFLECT
   zero, which for a ring homomorphism is injectivity.  A homomorphism
   that collapses a nonzero denominator supports no such map, and the
   standard repair — restrict the domain category to monomorphisms —
   is what Mac Lane's Dom_m records.  Both halves are
   delivered here, against the SAME category of fields, so that the
   contrast is a theorem and not a change of subject
   ([frac_universal_over_monos_not_over_all]).

   WHAT IS ALREADY IN TREE, and a CORRECTION.  The issue's "Current
   state" paragraph says of this material "Absent … No category of
   fields or integral domains exists, and no ℤ-as-initial-ring
   machinery for the non-existence example."  That is false on every
   count, as the issue's own trailing QA-audit block records, and the
   correction is repeated here because a header is where a reader
   looks.  Already present and REUSED rather than rebuilt:
   Instance/Rng/Frac.v's [IntDom] — integral domains with injective
   ring homomorphisms, which is Mac Lane's Dom_m; the
   monic-implies-injective converse was outstanding when this was
   written, pending the free ring ℤ[x], and is now proved as
   [rng_monic_injective] in Instance/Rng/Polynomial.v, while
   injective-implies-monic is Instance/Rng/Frac.v's [DomHom_monic] —
   with [DomObject],
   [DomHom], the fraction ring [FracRing], the embedding [frac_embed]
   and its injectivity [frac_embed_inj]; Instance/Field.v's [Field]
   with [Field_Rng], [Field_Forget], the ¬¬-stability analysis, ℚ and
   F₂; and Instance/Rng.v's [ZtoQ].  Nothing of that is re-derived
   below.  Instance/Rng.v's [Rng_Initial_Z] refutes the issue's
   "no ℤ-as-initial-ring machinery" clause by existing, but it is not
   used: the non-existence proof names the two homomorphisms out of ℤ
   concretely rather than obtaining them from initiality.

   WHAT IS NEW HERE.  The forgetful functor from fields into a
   category of integral domains — no such functor existed, into either
   [IntDom] or the [Dom] built below; the universal property and its
   packaging as a [UniversalArrow]; and the whole non-existence half,
   including [Dom] itself and the reduction ℤ → F₂ that lives in it.

   THE FORGETFUL FUNCTOR, and the first hypothesis.  A field is an
   integral domain unconditionally ([field_dom]): cancellation follows
   from invertibility, and the guard on [finv_l] is a NEGATION, which
   is exactly the hypothesis [dom_cancel] already carries, so no
   decision procedure is consulted.  Morphisms are where the price is
   paid.  [DomHom] carries injectivity as DATA in the strict form
   f a ≈ f b → a ≈ b, and Instance/Field.v has already measured how
   much of that is constructively available: the unconditional
   strength is [field_hom_distinct], a ≉ b → f a ≉ f b, whose
   contrapositive yields only ¬¬(a ≈ b), and the strict form is
   [field_stable_at_zero_suffices], which consumes ¬¬-stability of the
   SOURCE at zero.  So the functor is delivered in two shapes:
   [StableField_IntDom], hypothesis-free, on the full subcategory
   [StableField] of fields carrying [FieldStableAtZero] as an object
   datum; and [Field_IntDom], on all of [Field], taking the blanket
   stability assumption as an explicit argument in the shape
   Instance/Field.v's [field_every_monic] uses.  Whether some other
   construction gives an unconditional functor on all of [Field] is
   NOT settled here and is not asserted either way — the same
   discipline Instance/Field.v follows in declining to claim that some
   field has unstable equality.  This is ARGUED from what the tree
   proves, not proved to be necessary.  What IS proved is that no such
   hypothesis is needed on the [Dom] side: [Field_Dom] is
   unconditional, since a plain ring homomorphism is asked for nothing.

   THE UNIVERSAL PROPERTY IS UNCONDITIONAL.  [frac_ump] states, for an
   ARBITRARY integral domain D and an ARBITRARY field K, that every
   [IntDom]-morphism D → K extends uniquely along the embedding to a
   ring homomorphism Q(D) → K.  No stability, no decidability, no
   choice, and no field structure on the fractions appears in it.  The
   extension is [frac_extend], its triangle [frac_extend_embed], and
   the uniqueness [frac_extend_unique] — the latter through
   [frac_embed_den], the identity saying that d/1 · n/d ≈ n/1, so that
   the extension is forced without ever asking a competitor to
   preserve inverses.  Injectivity is spent in EXACTLY ONE PLACE,
   [frac_hom_den_nonzero]: a denominator is apart from zero, and its
   image must be too, or it could not be inverted.  That single lemma
   is Mac Lane's whole reason for taking monomorphisms.

   THE SECOND HYPOTHESIS, and it is not Mac Lane's either.  Naming
   Q(D) as an OBJECT of the field category requires a [FieldObject],
   whose inverse operation [finv] is TOTAL — totality being forced by
   the setoid discipline, since a partial operation is not a setoid
   map (Instance/FdVect.v's own header says so).  A total reciprocal
   on fractions must decide what to return at zero, and that decision
   is [DomZeroDec]: ≈-comparison with zero is decidable in D.  It is
   stated at zero rather than pairwise, following [FieldStableAtZero]
   in locating the obstruction, and the two are inter-derivable
   ([dom_zero_dec_eq_dec] and [dom_eq_dec_zero_dec]).  It subsumes the
   first hypothesis on the fractions: decidability gives stability, so
   [FracField] lands in [StableField] with nothing further to check.
   Classically neither hypothesis is visible; both are disclosed here
   rather than absorbed, and ℤ discharges the second by [Z.eq_dec].

   THE NON-EXAMPLE, and how far it reaches.  [Dom] is built here with
   all ring homomorphisms as arrows, and [IntDom_Dom] includes [IntDom]
   into it as a wide, faithful, NOT full subcategory —
   [IntDom_Dom_not_Full] proves the non-fullness that
   Instance/Rng/Frac.v left unstated for want of a counterexample
   object.  The witness is reduction mod 2, which needs NO
   quotient-ring theory: F₂ is already an object, and the reduction is
   [Z.odd], whose stdlib laws [Z.odd_add] and [Z.odd_mul] ARE the two
   homomorphism clauses against F₂'s [xorb] and [andb].  It is not
   injective ([ZtoF2_not_injective]), and more sharply [IntDom] has NO
   morphism from ℤ to F₂ whatsoever ([no_DomHom_Z_F2]) — so the arrow
   that breaks the universal property is invisible to the category in
   which the universal property holds.  ONE PRIME SUFFICES, and no
   case split on the characteristic is needed: [no_field_over_Q_and_F2]
   observes that a homomorphism to ℚ forces 1 + 1 to be apart from
   zero (a NEGATIVE fact, delivered outright), whereupon
   [field_hom_nonzero] refutes a homomorphism to F₂, where 1 + 1
   vanishes.  Mac Lane's ℤ/pℤ family is therefore not needed and
   neither is a second prime; the separating pair is ℚ against F₂,
   already Instance/Field.v's pair for the absence of initial and
   terminal objects.  The refutation consumes only the EXISTENCE of
   the factorizations — uniqueness is never used, and neither is the
   universal arrow ℤ → K itself, which is why it also holds in the
   weaker form [no_field_maps_to_all_fields].  It is stated in both
   encodings ([UniversalArrow] and [AUniversalArrow]) and over BOTH
   field categories, so the obstruction is not an artifact of [Field]
   being larger than [StableField]: ℚ and F₂ are both stable, so both
   survive the restriction.

   STRENGTHS, measured.  At Leibniz equality by [eq_refl] — the
   convertibility exception, exhibited where it holds: the object and
   morphism components of [StableField_IntDom_Dom_obj] and
   [StableField_IntDom_Dom_map]; the object component of
   [Field_IntDom_agrees_obj]; and the two computations
   [frac_extend_Z_half] and [frac_extend_Z_three], where the extension
   of ℤ ↪ ℚ carries 1/2 to the rational 1#2 ON THE NOSE.  Strictness
   was attempted first and REJECTED in one place:
   [Field_IntDom_agrees_map] holds only up to ≈, because the two
   [DomHom]s carry the same underlying map but different injectivity
   proofs, and [DomHom] carries that proof as a field.  Both
   boundaries are guarded, not merely measured, by negative probes in
   Test/ProbeFieldFrac.v, each paired with a positive control.

   NON-VACUITY.  Q(ℤ) is an actual object ([Frac_Z]), ℤ ↪ ℚ an actual
   [IntDom]-morphism ([ZtoQ_Dom]), the extension computes as above,
   and the embedding is NOT onto — [frac_embed_Z_not_surjective] shows
   1/2 is not n/1 for any integer n, so the fraction field is strictly
   larger than the image of D and the universal arrow is not a
   degenerate one.

   WHAT IS NOT DELIVERED.  No isomorphism Q(ℤ) ≅ ℚ is proved; the
   computations above relate the two through the extension, not by an
   equivalence of objects.  [Dom] is defined here rather than beside
   [IntDom] in Instance/Rng/Frac.v, since it exists only to state the
   non-example.  Fullness of [IntDom_Incl] into [CRng] — a DIFFERENT
   functor from [IntDom_Dom], and the one Instance/Rng/Frac.v actually
   left open — is refuted separately as [IntDom_Incl_not_Full], on the
   same F₂ witness; the two statements are about different functors
   and neither implies the other here.  And no quotient rings are
   built: F₂ is used as the positive-characteristic witness precisely
   so that none are needed, which is exactly what makes the
   [IntDom_Incl] deferral discharge-able, since that deferral was
   conditioned on there being no counterexample OBJECT and a field is
   a domain.

   AXIOMS.  Everything here is axiom-free, counted the way
   docs/AXIOMS.md counts: all 99 constants the module declares — the
   69 source-level definitions and theorems and the 30 [Program]
   obligations, which no [.glob] sweep sees — report "Closed under the
   global context", including both principal artifacts,
   [frac_universal] and [no_universal_arrow_Z_Dom].  The
   arithmetic is Theory/Algebra/Rig.v's, the concrete carriers are
   stdlib [Z], [bool] and [QArith], and nothing here touches the
   reals. 

   --------
   * * 商域作为一个泛箭头，以及 Mac Lane 的非例子

   Mac Lane，《为工作数学家准备的范畴论》，第二版，
   §III.1（泛箭头），印刷页 55-56
   [maclane:III.1:construction2]：对于一个整环 D，商域 Q(D) 连同嵌入 n ↦ n/1 是从 D 到从域到整环的遗忘函子的一条泛箭头——前提是取域的范畴中的箭头为单射。Mac Lane 的附带说明是这样的意思：在整环及其所有同态的范畴上，根本不存在从 ℤ 出发的泛箭头，因为映射 ℤ → ℤ/pℤ 的约化不能通过一个固定的域来实现。
   nLab: https://ncatlab.org/nlab/show/field+of+fractions
   nLab: https://ncatlab.org/nlab/show/universal+construction这个构造是代数中最古老的泛性质——Grassmann 和 Hamilton 早在有人称之为“泛性质”之前就用这种方式从 ℤ 构造 ℚ——它也通常是人们最初考虑该概念的例子，正是因为错误的态射选择会破坏它。那种敏感性正是关键：f : D → K 的扩展到 Q(D) 将 n/d 映射为 f(n)·(f(d))⁻¹，因此它需要每个 d ≉ 0 的 f(d) 可逆，也就是它需要 f 反映零，对于环同态来说这就是单射。一个把非零分母压缩掉的同态不支持这样的映射，而标准的修正方法——将定义域范畴限制为单态射——就是 Mac Lane 的 Dom_m 所记录的。两部分都在此处传递，针对相同类别的字段，因此对比是一个定理，而不是主题的变化（[frac_universal_over_monos_not_over_all]）。树中已有的内容，以及一个纠正。该问题的“当前状态”段落中对该材料的描述为“缺失……不存在任何类型的域或整环，也没有用于不存在示例的作为初始环的ℤ机制。” 这在每一点上都是错误的，正如该问题自身的后续QA审计块所记录的那样，并且纠正内容在此重复，因为读者会在标题处查找信息。已经存在并被重用而不是重建：
   Instance/Rng/Frac.v 中的 [IntDom] — 拥有单射环同态的整环，这是 Mac Lane 的 Dom_m；当时写这个时，单性蕴含单射的逆命题尚未解决，等待自由环 ℤ [x]，现在在 Instance/Rng/Polynomial.v 中被证明为 [rng_monic_injective]，而单射蕴含单性的是 Instance/Rng/Frac.v 中的 [DomHom_monic] — 以及 [DomObject]、[DomHom]、分式环 [FracRing]、嵌入 [frac_embed] 及其单射性 [frac_embed_inj]；Instance/Field.v 中的 [Field] 与 [Field_Rng]、[Field_Forget]、¬¬-稳定性分析、ℚ 和 F₂；以及 Instance/Rng.v 中的 [ZtoQ]。下面没有重新推导这些内容。Instance/Rng.v 的 [Rng_Initial_Z] 通过存在本身驳斥了该问题中“没有 ℤ-作为初始环的机制”这一条款，但它并未被使用：非存在性证明具体命名了从 ℤ 出发的两个同态，而不是从初始性中获得它们。

   这里的新内容是什么？
   从域到整环范畴的遗忘函子——以前不存在这样的函子，无论是对于 [IntDom] 还是下面构建的 [Dom]；其泛性质及将其包装为 [UniversalArrow] 的方式；以及整个非存在性部分，包括 [Dom] 本身以及其中存在的 ℤ → F₂ 的规约。遗忘函子和第一个假设。一个域在无条件下是一个整环（[field_dom]）：可消性由可逆性得出，而 [finv_l] 上的守卫是一个否定，这正是假设 [dom_cancel] 已经具有的，所以没有调用任何决策程序。态射是付出代价的地方。[DomHom] 将单射性作为严格形式的数据信息 f a ≈ f b → a ≈ b，并且 Instance/Field.v 已经衡量了其中有多少是可构造地可用的：无条件的强度是 [field_hom_distinct] ， a ≉ b → f a ≉ f b，其逆命题仅得出 ¬¬(a ≈ b)，严格形式是 [field_stable_at_zero_suffices]，它在零点消耗了源的 ¬¬-稳定性。所以函子以两种形式交付：
   [StableField_IntDom]，在没有假设的情况下，在完全子范畴
   [StableField] 上的域，其携带 [FieldStableAtZero] 作为对象数据；以及 [Field_IntDom]，在整个 [Field] 上，将全面的稳定性假设作为明确参数传入 Instance/Field.v 中 [field_every_monic] 使用的形式。这里没有决定是否有其他构造能够在整个 [Field] 上提供无条件函子，并且也没有任何断言——Instance/Field.v 遵循相同的策略，不声称某个域具有不稳定的等式。这是根据树证明进行论证的，而不是被证明为必要。已证明的是，在 [Dom] 端不需要这样的假设：[Field_Dom] 是无条件的，因为一个普通环同态不要求任何额外条件。普适性是无条件的。[frac_ump] 表示，对于任意整数域 D 和任意域 K，每一个 [IntDom]-态射 D → K 都可以通过嵌入唯一地扩展为环同态 Q(D) → K。在其中没有稳定性、可判定性、选择公理，也没有分数的域结构。扩展是 [frac_extend]，其三角形是 [frac_extend_embed]，唯一性是 [frac_extend_unique] —— 后者通过 [frac_embed_den]，即恒等式 d/1 · n/d ≈ n/1，因此扩展是被迫的，而无需要求竞争者保持逆元素。单射性只在唯一一个地方发挥作用，即 [frac_hom_den_nonzero]：分母非零，其像也必须非零，否则无法求逆。这个单一引理就是 Mac Lane 选择单射的全部理由。第二个假设，而且这也不是麦克莱恩（Mac Lane）的。将 Q(D) 命名为域范畴的一个对象需要一个 [FieldObject]，其逆运算 [finv] 是全函数——全性是由集合等价关系纪律强制的，因为部分运算不是集合等价映射（Instance/FdVect.v 的标题已经说明了这一点）。分数上的全倒数必须决定在零时返回什么，而这个决定是 [DomZeroDec]：在 D 中与零的 ≈ 比较是可判定的。它在零处说明而不是成对说明，遵循 [FieldStableAtZero] 定位障碍，而这两者是可以互相推导的（[dom_zero_dec_eq_dec] 和 [dom_eq_dec_zero_dec]）。它包含了对分数的第一个假设：可判定性带来稳定性，因此 [FracField] 落在 [StableField] 中，无需进一步检查。经典上，两种假设都不可见；这里两者都是被揭示的，而不是被吸收，并且 ℤ 通过 [Z.eq_dec] 释放第二个假设。非例子，以及它的影响范围。[Dom] 在此处构建，所有环同态作为箭头，而 [IntDom_Dom] 包含 [IntDom] 作为广义、忠实但不完全的子范畴——[IntDom_Dom_not_Full] 证明了 Instance/Rng/Frac.v 因缺少反例对象而未说明的不完全性。这个示例是模 2 的约化，这不需要任何商环理论：F₂ 已经是一个对象，并且约化是 [Z.odd]，其 stdlib 法则 [Z.odd_add] 和 [Z.odd_mul] 是针对 F₂ 的 [xorb] 和 [andb] 的两个同态条款。它不是单射（[ZtoF2_not_injective]），更明确地说，[IntDom] 完全没有从 ℤ 到 F₂ 的态射（[no_DomHom_Z_F2]）——因此破坏泛性质的箭头在该泛性质成立的范畴中是不可见的。一个素数就足够了，而且不需要对特征进行情况分析：[no_field_over_Q_and_F2] 观察到一个到 ℚ 的同态会强制 1 + 1 与零不同（一个直接给出的负事实），随后 [field_hom_nonzero] 反驳了到 F₂ 的同态，在 F₂ 中 1 + 1 消失。因此，Mac Lane 的 ℤ/pℤ 系列不需要，也不需要第二个素数；分离对是 ℚ 和 F₂，这已经是 Instance/Field.v 用于初始对象和终对象不存在的分离对。反驳只消耗分解的存在性——从未使用唯一性，也未使用从 ℤ 到 K 的普遍箭头，这就是为什么它在较弱形式的 [no_field_maps_to_all_fields] 中也成立。在两种编码（[UniversalArrow] 和 [AUniversalArrow]）以及两类字段中都有说明，因此阻碍并不是因为 [Field] 比 [StableField] 大的结果：ℚ 和 F₂ 都是稳定的，因此在限制下都能存活。优势，已测量。在莱布尼茨平等下由 [eq_refl] — 可转换性例外，展示其成立的地方：[StableField_IntDom_Dom_obj] 和 [StableField_IntDom_Dom_map] 的对象和态射组件；[Field_IntDom_agrees_obj] 的对象组件；以及两个计算 [frac_extend_Z_half] 和 [frac_extend_Z_three]，其中 ℤ ↪ ℚ 的扩展将 1/2 精确地映射到有理数 1#2。严格性首先被尝试，但在一个地方被拒绝：[Field_IntDom_agrees_map] 仅在 ≈ 下成立，因为两个 [DomHom] 具有相同的底层映射但不同的单射性证明，而 [DomHom] 将该证明作为字段携带。两个边界都受到保护，而不仅仅是测量，由 Test/ProbeFieldFrac.v 中的负探针保护，每个都与一个正控制配对。非空性。Q(ℤ) 是一个实际对象 ([Frac_Z])，ℤ ↪ ℚ 是一个实际 [IntDom]-态射 ([ZtoQ_Dom])，如上所述进行扩展，且该嵌入不是满射——[frac_embed_Z_not_surjective] 说明 1/2 不是任何整数 n 的 n/1，因此分数域严格大于 D 的像，并且泛箭头不是退化的。未交付的内容。没有证明 Q(ℤ) ≅ ℚ 的同构；上面的计算是通过扩展关联两者的，而不是通过对象等价。[Dom] 在这里定义，而不是在 Instance/Rng/Frac.v 中的 [IntDom] 旁边定义，因为它的存在仅用于说明非示例。[IntDom_Incl] 到 [CRng] 的充满性——一个不同于 [IntDom_Dom] 的函子，也是 Instance/Rng/Frac.v 实际上留下悬而未决的函子——被作为 [IntDom_Incl_not_Full] 单独驳斥，使用相同的 F₂ 证据；这两条陈述是关于不同的函子，且在此处彼此都不蕴含对方。而且没有构造商环：F₂ 被用作正特征的证明对象，正是为了不需要构造任何商环，这正是使 [IntDom_Incl] 延期可解除的原因，因为该延期是建立在没有反例 OBJECT 的前提下，并且域本身是一个整环。

   公理。一切这里都是无公理的，计算方式参考 docs/AXIOMS.md 的统计：模块声明的所有 99 个常量——69 个源级定义和定理，以及 30 个 [Program] 义务，这些义务没有任何 [.glob] 扫描看到——都报告“在全局上下文下封闭”，包括两个主要的成果，[frac_universal] 和 [no_universal_arrow_Z_Dom]。
   算术使用的是 Theory/Algebra/Rig.v 的方法，具体的载体是 stdlib [Z]、[bool] 和 [QArith]，这里没有涉及实数。
*)

(* * ** Every field is an integral domain / * ** 每个域都是整环 *)

(*
 Cancellation is where the field structure is spent, and it is spent
 unconditionally: the guard on [finv_l] is exactly the hypothesis
 [dom_cancel] already carries, so c ≉ 0 licenses inverting c with no
 decision procedure consulted.  Commutativity and 1 ≉ 0 transfer
 verbatim. 

 --------
 消去（Cancellation）是指场结构被使用完，并且是无条件使用的：[finv_l] 上的守卫正好是 [dom_cancel] 已经具备的假设，因此 c ≉ 0 允许在不咨询任何判定程序的情况下对 c 进行求逆。交换律和 1 ≉ 0 的性质逐字转移。
*)
Program Definition field_dom (F : FieldObject) : DomObject := {|
  dom_ring       := field_ring F;
  dom_comm       := field_comm F;
  dom_nontrivial := field_one_neq_zero F
|}.
Next Obligation.
  intros F a b c Hc H.
  transitivity (rig_mul F (rig_mul F a c) (finv F c)).
  - rewrite rig_mul_assoc.
    rewrite (finv_r F c Hc).
    symmetry; apply rig_mul_one_r.
  - rewrite H.
    rewrite rig_mul_assoc.
    rewrite (finv_r F c Hc).
    apply rig_mul_one_r.
Qed.

(* * ** The category of integral domains and ALL homomorphisms / * ** 整环及所有同态的范畴 *)

(*
 Mac Lane's [Dom], as against Instance/Rng/Frac.v's [IntDom], which is
 his [Dom_m].  Same objects; the morphisms here are the plain ring
 homomorphisms, with no injectivity clause.  The two categories are
 what the whole file is about: the universal arrow exists over
 [IntDom] and does not exist over [Dom]. 

 --------
 Mac Lane 的 [Dom]，与 Instance/Rng/Frac.v 的 [IntDom] 相比，后者是他的 [Dom_m]。对象相同；这里的态射是普通的环同态，没有单射条件。这两个范畴就是整个文件讨论的内容：在 [IntDom] 上存在一个普遍箭，而在 [Dom] 上不存在。
*)
Program Definition Dom : Category := {|
  obj     := DomObject;
  hom     := fun D E => RigHom (dom_ring D) (dom_ring E);
  homset  := fun D E => @RigHom_Setoid (dom_ring D) (dom_ring E);
  id      := fun D => @rig_hom_id (dom_ring D);
  compose := fun _ _ _ f g => rig_hom_compose f g;

  compose_respects := fun _ _ _ => @rig_hom_compose_respects _ _ _
|}.
Next Obligation. intros D E f a; simpl; reflexivity. Qed.
Next Obligation. intros D E f a; simpl; reflexivity. Qed.
Next Obligation. intros D E F G f g h a; simpl; reflexivity. Qed.
Next Obligation. intros D E F G f g h a; simpl; reflexivity. Qed.

(*
 [IntDom] sits inside [Dom] as a WIDE subcategory: identical on
 objects, forgetting the injectivity datum on morphisms.  It is not
 full — proved below as [IntDom_Dom_not_Full], on the witness
 [no_DomHom_Z_F2]: the reduction ℤ → F₂ is a morphism of [Dom]
 between two objects of [IntDom] that no morphism of [IntDom] can
 carry. 

 --------
 [IntDom] 作为一个 WIDE 子范畴坐在  [Dom]  内部：在对象上完全相同，但忘记了态射的单射性数据。它不是满的——如下在  [IntDom_Dom_not_Full]  中证明，通过见证  [no_DomHom_Z_F2] ：归约 ℤ → F₂ 是  [Dom]  中两个  [IntDom] 对象之间的一个态射，而 [IntDom] 的任何态射都不能承载它。
*)
Program Definition IntDom_Dom : IntDom ⟶ Dom := {|
  fobj := fun D => D;
  fmap := fun _ _ f => dom_map f
|}.
Next Obligation. intros D E f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros D a; simpl; reflexivity. Qed.
Next Obligation. intros D E F f g a; simpl; reflexivity. Qed.

#[export] Instance IntDom_Dom_Faithful : Faithful IntDom_Dom.
Proof. constructor; intros D E f g H x; exact (H x). Qed.

(* * ** The forgetful functor into ALL homomorphisms, unconditionally / * ** 忘记函子到所有同态，无条件 *)

(*
 Every field is a domain and every ring homomorphism is a ring
 homomorphism, so this functor costs nothing.  Contrast
 [StableField_IntDom] below, which is the same assignment on objects
 and needs a hypothesis on morphisms; the difference between the two
 is exactly the injectivity clause of [DomHom]. 

 --------
 每个域都是一个范畴，每个环同态都是一个环同态，所以这个函子不花费任何代价。对比下面的 [StableField_IntDom]，它在对象上的分配是相同的，但在态射上需要一个假设；两者之间的区别恰好是 [DomHom] 的单射条件。
*)
Program Definition Field_Dom : Field ⟶ Dom := {|
  fobj := field_dom;
  fmap := fun _ _ f => f
|}.
Next Obligation. intros F K f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros F a; simpl; reflexivity. Qed.
Next Obligation. intros F K T f g a; simpl; reflexivity. Qed.

#[export] Instance Field_Dom_Faithful : Faithful Field_Dom.
Proof. constructor; intros F K f g H x; exact (H x). Qed.

(* * ** Fields whose equality is ¬¬-stable / * ** 平等性是 ¬¬-稳定的域 *)

(*
 The selection predicate is Instance/Field.v's [FieldStableAtZero],
 the LOCATED form of stability: ≈ is ¬¬-stable at zero.  That file
 proves it inter-derivable with the pairwise [FieldStable]
 ([field_stable_stable_at_zero], [field_stable_at_zero_stable]), so
 nothing is lost by selecting on the weaker-looking one, and it is
 what [field_stable_at_zero_suffices] consumes directly. 

 --------
 选择谓词是 Instance/Field.v 的 [FieldStableAtZero]，稳定性的 LOCATED 形式：≈ 在零点下是 ¬¬-稳定的。该文件证明了它与成对的 [FieldStable] ([field_stable_stable_at_zero], [field_stable_at_zero_stable]) 可互推，所以选择看起来较弱的一个不会丢失任何内容，并且它正是 [field_stable_at_zero_suffices] 直接使用的。
*)
Definition StableField_Sub : Subcategory Field :=
  @Build_Subcategory Field
    (fun F : FieldObject => FieldStableAtZero F)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition StableField : Category := Sub Field StableField_Sub.

(* Full: every field homomorphism between selected objects is selected. / 完整：每个选定对象之间的每个域同态都是被选定的。 *)
Lemma StableField_Full :
  Category.Construction.Subcategory.Full Field StableField_Sub.
Proof. intros F K oF oK g; exact I. Qed.

(*
 Decidable equality gives stability, so both fields of the tree are
 objects.  ℚ and F₂ are the two witnesses Instance/Field.v uses to
 separate characteristics, and they are the two witnesses the
 non-existence theorem below uses as well. 

 --------
 可判定的相等性提供了稳定性，因此树的两个字段都是对象。ℚ 和 F₂ 是 Instance/Field.v 用来区分特征的两个证人，它们也是下面的非存在定理所使用的两个证人。
*)
Definition StableField_of_dec (F : FieldObject)
  (dec : ∀ a b : carrier (rig_setoid F), (a ≈ b) + (a ≈ b → False)) :
  StableField :=
  (F; field_stable_stable_at_zero F (field_dec_stable F dec)).

Definition Q_StableField : StableField := StableField_of_dec _ Q_Field_dec.

Definition F2_StableField : StableField := StableField_of_dec _ F2_Field_dec.

(* * ** The forgetful functor into the category of MONOMORPHISMS / * ** 忘记函子到单态射范畴 *)

(*
 Deliverable one, and the reason the objects carry a stability datum.
 To land in [IntDom] a field homomorphism must supply [DomHom]'s
 [dom_map_inj], the STRICT cancellation form f a ≈ f b → a ≈ b.
 Instance/Field.v measures exactly how much of that is available: the
 unconditional strength is [field_hom_distinct], a ≉ b → f a ≉ f b,
 whose contrapositive gives only ¬¬(a ≈ b); the strict form is
 [field_stable_at_zero_suffices] and it consumes ¬¬-stability of the
 SOURCE at zero.  So the injectivity datum comes from the object's own
 stability field, and no classical ideal argument and no [frac]-style
 cancellation can replace it — see the header. 

 --------
 可交付成果一，以及对象携带稳定性数据的原因。
 要在 [IntDom] 中着陆，域同态必须提供 [DomHom] 的 [dom_map_inj]，即严格消去形式 f a ≈ f b → a ≈ b。
 Instance/Field.v 精确测量了其中可用的部分：无条件强度为 [field_hom_distinct]，即 a ≉ b → f a ≉ f b，其逆否命题只给出 ¬¬(a ≈ b)；严格形式为 [field_stable_at_zero_suffices]，并且它消耗了源对象在零点的 ¬¬-稳定性。所以单射性数据来自对象自身的稳定性域，没有经典理想论证，也没有 [frac] 风格的消去可以替代它——详见头部说明。
*)
Program Definition StableField_IntDom : StableField ⟶ IntDom := {|
  fobj := fun F => field_dom `1 F;
  fmap := fun F K f =>
    {| dom_map     := `1 f;
       dom_map_inj := field_stable_at_zero_suffices `1 f `2 F |}
|}.
Next Obligation. intros F K f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros F a; simpl; reflexivity. Qed.
Next Obligation. intros F K T f g a; simpl; reflexivity. Qed.

#[export] Instance StableField_IntDom_Faithful : Faithful StableField_IntDom.
Proof. constructor; intros F K f g H x; exact (H x). Qed.

(*
 What a forgetful functor on ALL of [Field] costs, in the shape
 Instance/Field.v's [field_every_monic] uses: the blanket stability
 assumption, taken as an explicit argument rather than smuggled.
 Restricting to [StableField] instead is what makes
 [StableField_IntDom] hypothesis-free.  The two agree on the selected
 objects, and the strengths of the two agreements DIFFER: the object
 component is [eq_refl], the morphism component only ≈ — the two
 [DomHom]s carry the same underlying map but different injectivity
 proofs ([stab F] against F's own datum), and [DomHom] carries that
 proof as a field, so they are distinct records. 

 --------
 在所有 [Field] 上，一个多么健忘的函子所消耗的代价，在 Instance/Field.v 的 [field_every_monic] 中使用：总体稳定性假设，被作为显式参数而不是偷偷传递。改为限制在 [StableField] 上正是使 [StableField_IntDom] 无假设。两者在选定对象上是一致的，但一致性的强度不同：对象部分是 [eq_refl]，态射部分只有 ≈——两个 [DomHom] 携带相同的基础映射但不同的单射性证明（[stab F] 对比 F 的自身数据），而 [DomHom] 将该证明作为一个字段携带，因此它们是不同的记录。
*)
Program Definition Field_IntDom
  (stab : ∀ F : FieldObject, FieldStableAtZero F) : Field ⟶ IntDom := {|
  fobj := field_dom;
  fmap := fun F K f =>
    Build_DomHom (field_dom F) (field_dom K) f
      (field_stable_at_zero_suffices f (stab F))
|}.
Next Obligation. intros stab F K f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros stab F a; simpl; reflexivity. Qed.
Next Obligation. intros stab F K T f g a; simpl; reflexivity. Qed.

Example Field_IntDom_agrees_obj
  (stab : ∀ F : FieldObject, FieldStableAtZero F) (F : StableField) :
  Field_IntDom stab (Incl Field StableField_Sub F) = StableField_IntDom F
  := eq_refl.

Example Field_IntDom_agrees_map
  (stab : ∀ F : FieldObject, FieldStableAtZero F) (F K : StableField)
  (f : F ~{StableField}~> K) :
  fmap[Field_IntDom stab] (fmap[Incl Field StableField_Sub] f)
    ≈ fmap[StableField_IntDom] f.
Proof. intro a; simpl; reflexivity. Qed.

(*
 The same assignment read into [Dom] instead, where no hypothesis is
 needed; the two agree, in that composing with the wide inclusion
 recovers [Field_Dom] on the selected objects.  BOTH components hold
 at Leibniz equality by [eq_refl] — the convertibility exception,
 measured rather than assumed: [IntDom_Dom] forgets exactly the
 injectivity field that [StableField_IntDom] supplied, so the
 composite's morphism component reduces to `1 f on the nose.
 Contrast [Field_IntDom_agrees_map] below, where the same shape of
 comparison is NOT strict. 

 --------
 相同的赋值反而被读入 [Dom]，其中不需要假设；两者一致，因为通过广泛包含构成可以在选定对象上恢复 [Field_Dom]。通过 [eq_refl]，两部分在莱布尼茨等式下都成立——可转换性例外，测量而非假设：[IntDom_Dom] 恰好忘记了 [StableField_IntDom] 提供的单射性字段，因此复合体的态射部分简化为 `1 f 就是这样。对比下面的 [Field_IntDom_agrees_map]，其中相同形状的比较并非严格。
*)
Definition StableField_Dom : StableField ⟶ Dom :=
  Field_Dom ◯ Incl Field StableField_Sub.

Example StableField_IntDom_Dom_obj (F : StableField) :
  IntDom_Dom (StableField_IntDom F) = StableField_Dom F := eq_refl.

Example StableField_IntDom_Dom_map (F K : StableField) (f : F ~{StableField}~> K) :
  fmap[IntDom_Dom] (fmap[StableField_IntDom] f) = fmap[StableField_Dom] f
  := eq_refl.

(** ** Division in a field / ** 田地里的划分 *)

(*
 A small kit, mirroring Instance/Rng/Frac.v's shuffle kit one layer
 up: everything below is "clear the denominator and shuffle".  Every
 lemma carries the nonzeroness hypotheses that make [finv] meaningful,
 and none consults a decision procedure — the hypotheses are
 NEGATIONS, which is exactly what [finv_l] asks for. 

 --------
 一个小工具，镜像 Instance/Rng/Frac.v 的 shuffle 工具向上一层：以下所有内容都是“清除分母并打乱”。每个引理都携带使 [finv] 有意义的非零性假设，并且没有一个依赖决策过程——这些假设都是否定，这正是 [finv_l] 所要求的。
*)

Section FieldArith.

Context (K : FieldObject).

Local Notation k0 := (rig_zero K).
Local Notation k1 := (rig_one K).
Local Infix "*" := (rig_mul K).
Local Infix "+" := (rig_add K).
Local Notation "/ x" := (finv K x).

Lemma kmulC (a b : carrier (rig_setoid K)) : a * b ≈ b * a.
Proof. apply field_comm. Qed.

Lemma kmulA (a b c : carrier (rig_setoid K)) : (a * b) * c ≈ a * (b * c).
Proof. apply rig_mul_assoc. Qed.

Lemma kmul_swap_r (a b c : carrier (rig_setoid K)) :
  (a * b) * c ≈ (a * c) * b.
Proof.
  rewrite kmulA, (kmulC b c), <- kmulA; reflexivity.
Qed.

Lemma kmul4_shuffle1 (a b c d : carrier (rig_setoid K)) :
  (a * b) * (c * d) ≈ (a * c) * (b * d).
Proof.
  rewrite kmulA, <- (kmulA b c d), (kmulC b c), (kmulA c b d), <- kmulA.
  reflexivity.
Qed.

(* Read off the domain structure of K rather than reproved: a field is an integral domain, and [dom_mul_nonzero] is that domain's. / 读出 K 的域结构，而不是纠正：一个域是一个整环，而 [dom_mul_nonzero] 是该域的。 *)
Lemma field_mul_nonzero (a b : carrier (rig_setoid K)) :
  (a ≈ k0 → False) → (b ≈ k0 → False) → a * b ≈ k0 → False.
Proof. exact (dom_mul_nonzero (field_dom K) a b). Qed.

Lemma finv_one : / k1 ≈ k1.
Proof.
  rewrite <- (rig_mul_one_r K (/ k1)).
  apply finv_l, (field_one_neq_zero K).
Qed.

(* (a/b)·b ≈ a. *)
Lemma field_div_elim (a b : carrier (rig_setoid K)) (Hb : b ≈ k0 → False) :
  (a * / b) * b ≈ a.
Proof.
  rewrite kmulA.
  rewrite (kmulC (/ b) b).
  rewrite (finv_r K b Hb).
  apply rig_mul_one_r.
Qed.

(* To prove q ≈ a/b it is enough to clear the denominator. / 要证明 q ≈ a/b，只需消去分母即可。 *)
Lemma field_div_intro (q a b : carrier (rig_setoid K)) (Hb : b ≈ k0 → False) :
  q * b ≈ a → q ≈ a * / b.
Proof.
  intro H.
  transitivity ((q * b) * / b).
  - rewrite kmulA, (finv_r K b Hb).
    symmetry; apply rig_mul_one_r.
  - now rewrite H.
Qed.

(* Cross-multiplication decides equality of quotients. / 交叉相乘决定商的相等性。 *)
Lemma field_div_eq (a b c d : carrier (rig_setoid K))
  (Hb : b ≈ k0 → False) (Hd : d ≈ k0 → False) :
  a * d ≈ c * b → a * / b ≈ c * / d.
Proof.
  intro H.
  apply (field_div_intro _ _ _ Hd).
  rewrite kmul_swap_r.
  rewrite H.
  rewrite kmulA.
  rewrite (finv_r K b Hb).
  apply rig_mul_one_r.
Qed.

Lemma field_div_add (a b c d : carrier (rig_setoid K))
  (Hb : b ≈ k0 → False) (Hd : d ≈ k0 → False) :
  a * / b + c * / d ≈ (a * d + c * b) * / (b * d).
Proof.
  apply (field_div_intro _ _ _ (field_mul_nonzero b d Hb Hd)).
  rewrite rig_distr_r.
  apply rig_add_respects.
  - rewrite <- kmulA.
    rewrite (field_div_elim a b Hb).
    reflexivity.
  - rewrite (kmulC b d), <- kmulA.
    rewrite (field_div_elim c d Hd).
    reflexivity.
Qed.

Lemma field_div_mul (a b c d : carrier (rig_setoid K))
  (Hb : b ≈ k0 → False) (Hd : d ≈ k0 → False) :
  (a * / b) * (c * / d) ≈ (a * c) * / (b * d).
Proof.
  apply (field_div_intro _ _ _ (field_mul_nonzero b d Hb Hd)).
  rewrite kmul4_shuffle1.
  rewrite (field_div_elim a b Hb).
  rewrite (field_div_elim c d Hd).
  reflexivity.
Qed.

End FieldArith.

(* * ** The extension of an injective homomorphism to the fractions / * ** 单射同态到分数的扩张 *)

(*
 This section is UNCONDITIONAL: [D] is an arbitrary integral domain,
 [K] an arbitrary field, and the only datum is an [IntDom]-morphism
 from D into K, i.e. an injective ring homomorphism.  No stability,
 no decidability, no choice, and no field structure on the fractions
 is needed to state or prove any of it. 

 --------
 本节是无条件的：[D] 是一个任意的整环，[K] 是一个任意的域，唯一的数据是一个从 D 到 K 的 [IntDom]-态射，即一个单射环同态。不需要稳定性、不需要可判定性、不需要选择，也不需要分数的域结构即可陈述或证明其中的任何内容。
*)

Section FracExtension.

Context (D : DomObject).
Context (K : FieldObject).
Context (f : DomHom D (field_dom K)).

(*
 THE ONE PLACE INJECTIVITY IS SPENT.  A denominator is apart from
 zero; its image has to be apart from zero too, or it could not be
 inverted — and that step is exactly the reflection of zero, which is
 what [dom_map_inj] supplies and what a general ring homomorphism does
 not.  This is why the domain category has monomorphisms only. 

 --------
 单射性耗尽的唯一地方。分母不能为零；它的像也必须不为零，否则无法求逆——而这一步正好是零的映射，这就是 [dom_map_inj] 提供的，而一般的环同态则不能。这就是为什么定义域范畴中只有单态射。
*)
Lemma frac_hom_den_nonzero (x : frac_carrier D) :
  dom_map f (den D x) ≈ rig_zero K → False.
Proof.
  intro H.
  apply (den_nonzero D x).
  apply (dom_map_inj f).
  rewrite H.
  symmetry.
  apply (rig_map_zero (dom_map f)).
Qed.

(* n/d ↦ f n · (f d)⁻¹. *)
Definition frac_extend_map (x : frac_carrier D) : carrier (rig_setoid K) :=
  rig_mul K (dom_map f (num D x)) (finv K (dom_map f (den D x))).

Program Definition frac_extend : RigHom (FracRing D) (field_ring K) := {|
  rig_map := {| morphism := frac_extend_map |}
|}.
Next Obligation.
  intros x y Hxy; unfold frac_extend_map.
  apply (field_div_eq K _ _ _ _
           (frac_hom_den_nonzero x) (frac_hom_den_nonzero y)).
  rewrite <- !(rig_map_mul (dom_map f)).
  exact (proper_morphism (rig_map (dom_map f)) _ _ Hxy).
Qed.
Next Obligation.
  unfold frac_extend_map, frac_zero, Frac.num, Frac.den, mk_frac; simpl.
  rewrite (rig_map_zero (dom_map f)).
  apply rig_mul_zero_l.
Qed.
Next Obligation.
  intros x y.
  unfold frac_extend_map, frac_add, Frac.num, Frac.den, mk_frac; simpl.
  rewrite (rig_map_add (dom_map f)).
  rewrite !(rig_map_mul (dom_map f)).
  symmetry.
  apply (field_div_add K _ _ _ _
           (frac_hom_den_nonzero x) (frac_hom_den_nonzero y)).
Qed.
Next Obligation.
  unfold frac_extend_map, frac_one, Frac.num, Frac.den, mk_frac; simpl.
  rewrite !(rig_map_one (dom_map f)).
  apply finv_r, (field_one_neq_zero K).
Qed.
Next Obligation.
  intros x y.
  unfold frac_extend_map, frac_mul, Frac.num, Frac.den, mk_frac; simpl.
  rewrite !(rig_map_mul (dom_map f)).
  symmetry.
  apply (field_div_mul K _ _ _ _
           (frac_hom_den_nonzero x) (frac_hom_den_nonzero y)).
Qed.

(* The triangle: the extension restricts along the embedding to f. / 三角形：延拓沿嵌入到 f 处受到限制。 *)
Lemma frac_extend_embed (a : carrier (rig_setoid D)) :
  frac_extend (frac_embed D a) ≈ dom_map f a.
Proof.
  unfold frac_extend, frac_extend_map, frac_embed, Frac.num, Frac.den, mk_frac;
    simpl.
  rewrite (rig_map_one (dom_map f)).
  rewrite (finv_one K).

  apply rig_mul_one_r.
Qed.

(*
 Every fraction is its numerator divided by its denominator, said
 inside the fraction ring: multiplying n/d by the image of d gives the
 image of n.  This is what forces the extension to be what it is, and
 it needs nothing of g beyond being a ring homomorphism — in
 particular no preservation of inverses. 

 --------
 每一个分数都是其分子除以分母，在分数环内部说：将 n/d 乘以 d 的像就得到 n 的像。这就是迫使扩张成为它自身的原因，而且它不需要 g 除了作为环同态之外的任何性质——特别是不需要保持逆元。
*)
Lemma frac_embed_den (x : frac_carrier D) :
  rig_mul (FracRing D) (frac_embed D (den D x)) x ≈ frac_embed D (num D x).
Proof.
  simpl; unfold frac_eq, frac_mul, Frac.num, Frac.den, mk_frac; simpl.
  rewrite rig_mul_one_r.
  rewrite rig_mul_one_l.
  apply dom_comm.
Qed.

Lemma frac_extend_unique (g : RigHom (FracRing D) (field_ring K))
  (Hg : ∀ a, rig_map g (frac_embed D a) ≈ dom_map f a) (x : frac_carrier D) :
  rig_map g x ≈ frac_extend x.
Proof.
  (* g of the identity above, with the embedding legs replaced by f / 上述恒等式的 g，将嵌入边替换为 f *)
  assert (Hgx : rig_mul K (dom_map f (den D x)) (rig_map g x)
                  ≈ dom_map f (num D x)).
  { transitivity (rig_map g (rig_mul (FracRing D) (frac_embed D (den D x)) x)).
    - rewrite (rig_map_mul g).
      rewrite (Hg (den D x)).
      reflexivity.
    - rewrite (proper_morphism (rig_map g) _ _ (frac_embed_den x)).
      apply Hg. }
  unfold frac_extend, frac_extend_map; simpl.
  apply (field_div_intro K _ _ _ (frac_hom_den_nonzero x)).
  rewrite (field_comm K).
  exact Hgx.
Qed.

End FracExtension.

(* * ** The universal mapping property, over EVERY field / * ** 对每一个域的泛映射性质 *)

(*
 The mathematical content of Mac Lane's construction, and it is
 unconditional: no stability of K, no decidability of D, no field
 structure on the fractions.  Everything the packaging below adds is
 bookkeeping needed to name [FracRing D] as an OBJECT of a category of
 fields; the property itself is this. 

 --------
 Mac Lane 构造的数学内容是无条件的：K 没有稳定性，D 没有可判定性，分数上没有域结构。下面的所有包装都是将 [FracRing D] 命名为一个域的范畴的对象所需的记账；性质本身就是如此。
*)
Theorem frac_ump (D : DomObject) (K : FieldObject) (f : DomHom D (field_dom K)) :
  ∃! g : RigHom (FracRing D) (field_ring K),
    ∀ a : carrier (rig_setoid D), rig_map g (frac_embed D a) ≈ dom_map f a.
Proof.
  unshelve esplit.
  - exact (frac_extend D K f).
  - exact (frac_extend_embed D K f).
  - intros g Hg x; symmetry; exact (frac_extend_unique D K f g Hg x).
Qed.

(* * ** Apartness from the zero fraction / * ** 脱离零分数 *)

Lemma frac_eq_zero (D : DomObject) (x : frac_carrier D) :
  frac_eq D x (frac_zero D) → num D x ≈ rig_zero D.
Proof.
  unfold frac_eq, frac_zero, Frac.num, Frac.den, mk_frac; simpl; intro H.
  rewrite <- (rig_mul_one_r D (fst `1 x)).
  rewrite H.
  apply rig_mul_zero_l.
Qed.

Lemma frac_zero_eq (D : DomObject) (x : frac_carrier D) :
  num D x ≈ rig_zero D → frac_eq D x (frac_zero D).
Proof.
  unfold frac_eq, frac_zero, Frac.num, Frac.den, mk_frac; simpl; intro H.
  rewrite rig_mul_one_r.
  rewrite H.
  symmetry; apply rig_mul_zero_l.
Qed.

(* * ** Testing for zero, and the fractions as an OBJECT of [Field] / * ** 测试零，以及作为 [Field] 对象的分数 *)

(*
 THE ONE HYPOTHESIS OF THIS PACKAGING STEP — the file's second, the
 first being the ¬¬-stability carried by [StableField]'s objects —
 and it is not Mac Lane's either: it is
 the price of Instance/FdVect.v's [FieldObject], whose inverse
 operation [finv] is TOTAL.  Totality is forced by the setoid
 discipline (a partial operation is not a setoid map), and a total
 reciprocal on fractions has to decide which value to return at zero;
 that decision is exactly this.  Stated at zero, following
 Instance/Field.v's [FieldStableAtZero] in locating the obstruction
 rather than assuming the pairwise form — and, as there, the two are
 inter-derivable ([dom_zero_dec_eq_dec] and its converse), the passage
 through a − b being the whole argument. 

 --------
 这个封装步骤的唯一假设——文件的第二个假设，第一个是假设由 [StableField] 的对象所携带的 ¬¬-稳定性——也不是 Mac Lane 的假设：它是 Instance/FdVect.v 的 [FieldObject] 的代价，其逆操作 [finv] 是全的。全性是由集合等价类的纪律强制的（一个部分操作不是集合等价类映射），而分数上的全互反必须决定在零处返回哪个值；这个决定恰好就是这个。在零处陈述时，遵循 Instance/Field.v 的 [FieldStableAtZero] 来定位阻碍而不是假设成对形式——并且，如同那里，两者是可相互推导的（[dom_zero_dec_eq_dec] 及其逆），通过 a − b 的过程就是整个论证。
*)
Definition DomZeroDec (D : DomObject) : Type :=
  ∀ a : carrier (rig_setoid D),
    (a ≈ rig_zero D) + (a ≈ rig_zero D → False).

Definition DomEqDec (D : DomObject) : Type :=
  ∀ a b : carrier (rig_setoid D), (a ≈ b) + (a ≈ b → False).

Definition dom_eq_dec_zero_dec (D : DomObject) (dec : DomEqDec D) :
  DomZeroDec D := fun a => dec a (rig_zero D).

Lemma dom_zero_dec_eq_dec (D : DomObject) (dec : DomZeroDec D) : DomEqDec D.
Proof.
  intros a b.
  destruct (dec (rig_add D a (ring_neg D b))) as [H | H].
  - left; exact (ring_sub_zero (dom_ring D) a b H).
  - right; intro Hab; apply H; exact (ring_zero_sub (dom_ring D) a b Hab).
Qed.

Section FracField.

Context (D : DomObject).
Context (dec : DomZeroDec D).

Definition frac_zero_dec (x : frac_carrier D) :
  (frac_eq D x (frac_zero D)) + (frac_eq D x (frac_zero D) → False) :=
  match dec (num D x) with
  | inl H => inl (frac_zero_eq D x H)
  | inr H => inr (fun Heq => H (frac_eq_zero D x Heq))
  end.

(*
 The reciprocal: flip the pair when the numerator is apart from zero,
 and return the junk value 0 otherwise — which is precisely the junk
 [FieldObject] allows, constrained by nothing but [finv_respects]. 

 --------
 倒数：当分子不为零时翻转这一对，否则返回无用值 0 —— 这正是无用 [FieldObject] 所允许的，仅受 [finv_respects] 的约束。
*)
Definition frac_finv (x : frac_carrier D) : frac_carrier D :=
  match dec (num D x) with
  | inl _  => frac_zero D
  | inr Hn => mk_frac D (den D x) (num D x) Hn
  end.

Program Definition FracField : FieldObject := {|
  field_ring         := FracRing D;
  field_comm         := FracRing_comm D;
  finv               := frac_finv
|}.
Next Obligation.
  (*
 1 ≉ 0 in the fractions, since 1 ≉ 0 in D.  The hypothesis is a
 cross-multiplication equation by conversion, and is read as one. 

 --------
 在分数中 1 ≉ 0，因为在 D 中 1 ≉ 0。假设是通过转换得到的交叉相乘方程，并读作一。
*)
  intro H.
  assert (H' : rig_mul D (rig_one D) (rig_one D)
                 ≈ rig_mul D (rig_zero D) (rig_one D)) by exact H.
  apply (dom_nontrivial D).
  rewrite <- (rig_mul_one_r D (rig_one D)).
  rewrite H'.
  apply rig_mul_zero_l.
Qed.
Next Obligation.
  (*
 [finv] respects ≈.  The two mixed cases are impossible — a fraction
 with vanishing numerator cannot be equivalent to one whose
 numerator is apart from zero — and the surviving case is a
 commutation.  Each goal is read as its cross-multiplication
 equation by conversion. 

 --------
 [finv] 尊重 ≈。这两种混合情况是不可能的——分子为零的分数不可能等于分子不为零的分数——而剩下的情况是一个换位。每个目标都通过转换被读取为其交叉相乘方程。
*)
  intros x y Hxy.
  assert (Hxy' : rig_mul D (num D x) (den D y) ≈ rig_mul D (num D y) (den D x))
    by exact Hxy.
  unfold frac_finv.
  destruct (dec (num D x)) as [Hx | Hx]; destruct (dec (num D y)) as [Hy | Hy].
  - reflexivity.
  - exfalso; apply Hy.
    apply (dom_cancel D _ _ (den D x) (den_nonzero D x)).
    rewrite rig_mul_zero_l.
    rewrite <- Hxy'.
    rewrite Hx.
    apply rig_mul_zero_l.
  - exfalso; apply Hx.
    apply (dom_cancel D _ _ (den D y) (den_nonzero D y)).
    rewrite rig_mul_zero_l.
    rewrite Hxy'.
    rewrite Hy.
    apply rig_mul_zero_l.
  - assert (Hres : rig_mul D (den D x) (num D y)
                     ≈ rig_mul D (den D y) (num D x)).
    { rewrite (dom_comm D (den D x) (num D y)).
      rewrite <- Hxy'.
      apply dom_comm. }
    exact Hres.
Qed.
Next Obligation.
  (* [finv_l] away from zero: the numerator cannot vanish there, and flipping the pair back gives 1/1. / [finv_l] 远离零：分子在那里不能为零，翻转该对又得到 1/1。 *)
  intros x Hx; unfold frac_finv.
  destruct (dec (num D x)) as [Hn | Hn].
  - destruct (Hx (frac_zero_eq D x Hn)).
  - assert (Hres : rig_mul D (rig_mul D (den D x) (num D x)) (rig_one D)
                     ≈ rig_mul D (rig_one D) (rig_mul D (num D x) (den D x))).
    { rewrite rig_mul_one_r, rig_mul_one_l; apply dom_comm. }
    exact Hres.
Qed.

(*
 Decidability at zero passes to the fractions, hence so does
 ¬¬-stability, so [FracField] is an object of [StableField]. 

 --------
 在零处的可判定性传递到分数，因此 ¬¬-稳定性也传递，因此 [FracField] 是 [StableField] 的一个对象。
*)
Definition FracField_stable : FieldStableAtZero FracField :=
  fun a Hnn =>
    match frac_zero_dec a with
    | inl H => H
    | inr H => match Hnn H with end
    end.

Definition FracStableField : StableField := (FracField; FracField_stable).

(* The unit: n ↦ n/1, with the injectivity datum [IntDom] demands. / 单位：n ↦ n/1，带有单射数据 [IntDom] 的要求。 *)
Definition frac_unit : D ~{IntDom}~> StableField_IntDom FracStableField :=
  Build_DomHom D (field_dom FracField) (frac_embed D) (frac_embed_inj D).

(* * ** ⟨Q(D), n ↦ n/1⟩ is a universal arrow / * ** ⟨Q(D), n ↦ n/1⟩ 是一个通用箭头 *)

Program Instance frac_universal_arrow :
  AUniversalArrow (D : IntDom) StableField_IntDom FracStableField := {|
  universal_arrow := frac_unit
|}.
Next Obligation.
  intros K f.
  unshelve esplit.
  - exact (frac_extend D `1 K f; I).
  - exact (frac_extend_embed D `1 K f).
  - intros g Hg x; symmetry; exact (frac_extend_unique D `1 K f `1 g Hg x).
Qed.

(*
 The same, in the comma-category packaging: an initial object of
 =(D) ↓ U.  Note the reversed orientation of the factorization
 equation in [universal_arrow_from_UMP], whence the [symmetry]s. 

 --------
 同样，在逗号类别的封装中：
 =(D) ↓ U 的初始对象。注意在 [universal_arrow_from_UMP] 中分解方程的方向被颠倒，因此产生了 [symmetry]。
*)
Definition frac_universal : UniversalArrow (D : IntDom) StableField_IntDom.
Proof using D dec.
  unshelve eapply (universal_arrow_from_UMP (D : IntDom) StableField_IntDom
                     FracStableField frac_unit).
  intros K f.
  unshelve esplit.
  - exact (frac_extend D `1 K f; I).
  - intro x; symmetry; exact (frac_extend_embed D `1 K f x).
  - intros g Hg x.
    assert (Hg' : ∀ a : carrier (rig_setoid D),
               rig_map `1 g (frac_embed D a) ≈ dom_map f a).
    { intro a; symmetry; exact (Hg a). }
    symmetry; exact (frac_extend_unique D `1 K f `1 g Hg' x).
Defined.

End FracField.

(* * ** Reduction mod 2, the morphism [IntDom] does not have / * ** 在模 2 的约简下，态射 [IntDom] 不存在 *)

(*
 No quotient-ring theory is needed to name ℤ → ℤ/2ℤ: F₂ is already an
 object (Instance/Field.v), and reduction mod 2 is [Z.odd], whose
 stdlib laws [Z.odd_add] and [Z.odd_mul] ARE the two homomorphism
 clauses against F₂'s [xorb] and [andb].  Preservation of 0 and 1
 holds by computation. 

 --------
 命名 ℤ → ℤ/2ℤ 不需要商环理论：F₂ 已经是一个对象（Instance/Field.v），取模 2 的约简是 [Z.odd]，其标准库定律 [Z.odd_add] 和 [Z.odd_mul] 就是针对 F₂ 的 [xorb] 和 [andb] 的两个同态分句。0 和 1 的保持性通过计算即可成立。
*)
(*
 Only FOUR obligations are generated: both setoids here carry Leibniz
 equality, so [Proper (equiv ==> equiv) Z.odd] is discharged by
 instance resolution during elaboration and never becomes one. 

 --------
 只生成四个义务：这里的两个集合都携带莱布尼茨等式，因此 [Proper (equiv ==> equiv) Z.odd] 在细化过程中通过实例解析被解除，从未变成一个义务。
*)
Program Definition ZtoF2 : Int_Ring ~{Rng}~> F2_Ring := {|
  rig_map := {| morphism := Z.odd |}
|}.
Next Obligation. reflexivity. Qed.
Next Obligation. intros a b; apply Z.odd_add. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros a b; apply Z.odd_mul. Qed.

(*
 It is not injective — 0 and 2 collide — which is exactly why it is a
 morphism of [Dom] and not of [IntDom]. 

 --------
 它不是单射——0 和 2 相撞——这正是它是  [Dom]  的态射而不是  [IntDom]  的原因。
*)
Theorem ZtoF2_not_injective :
  (∀ a b : carrier (rig_setoid Int_Ring),
     rig_map ZtoF2 a ≈ rig_map ZtoF2 b → a ≈ b) → False.
Proof.
  intro Hinj.
  assert (H : (0%Z : carrier (rig_setoid Int_Ring)) ≈ 2%Z)
    by (apply Hinj; reflexivity).
  discriminate H.
Qed.

(*
 Stronger, and this is the load-bearing statement: [IntDom] has NO
 morphism from ℤ to F₂ whatsoever, not merely that this one is
 excluded.  An injective ring homomorphism would identify 0 with 2,
 since 1 + 1 vanishes in F₂.  So the wide inclusion [IntDom_Dom] is
 not full, and the arrow the non-existence proof below uses is
 invisible to the category the universal arrow lives in. 

 --------
 更强的是，这是关键论断：[IntDom] 完全没有从 ℤ 到 F₂ 的同态，不仅仅是排除这一种。一个单射环同态会把 0 与 2 认同，因为 1 + 1 在 F₂ 中消失。因此，广义包含 [IntDom_Dom] 不是满的，而且下面用于非存在性证明的箭头在通用箭头所在的范畴中是不可见的。
*)
Theorem no_DomHom_Z_F2 : DomHom Int_Dom (field_dom F2_Field) → False.
Proof.
  intro f.
  assert (H : (0%Z : carrier (rig_setoid Int_Dom)) ≈ 2%Z).
  { apply (dom_map_inj f).
    transitivity (rig_zero F2_Field).
    - apply (rig_map_zero (dom_map f)).
    - symmetry.
      transitivity (rig_add F2_Field (rig_map (dom_map f) (rig_one Int_Dom))
                      (rig_map (dom_map f) (rig_one Int_Dom))).
      + apply (rig_map_add (dom_map f) 1%Z 1%Z).
      + rewrite (rig_map_one (dom_map f)).
        exact F2_ftwo_zero. }
  discriminate H.
Qed.

(* * ** No field lies over both ℚ and F₂ / * ** 没有任何域同时位于 ℚ 和 F₂ 之上 *)

(*
 The engine of the non-existence half, and it needs NO case split on
 the characteristic of K: the ℚ-side delivers the NEGATIVE fact
 "1 + 1 is apart from zero in K" outright, and [field_hom_nonzero]
 then refutes the F₂-side.  Same shape as Instance/Field.v's
 [Field_no_initial], and constructive for the same reason — the guard
 on [finv_l] is a negation, so a negative fact is a licence to
 invert. 

 --------
 不存在的一半的引擎，而且它在 K 的特性上不需要分情况：ℚ 端直接给出了负面事实“1 + 1 在 K 中不为零”，然后 [field_hom_nonzero] 驳斥了 F₂ 端。形状与 Instance/Field.v 的 [Field_no_initial] 相同，原因相同地具有构造性——[finv_l] 上的保护是一个否定，所以一个负面事实就是反转的许可。
*)
Theorem no_field_over_Q_and_F2 (K : FieldObject)
  (u : RigHom K Q_Field) (v : RigHom K F2_Field) : False.
Proof.
  assert (Hnz : ftwo K ≈ rig_zero K → False).
  { intro H.
    apply Q_ftwo_nonzero.
    rewrite <- (ftwo_map u).
    rewrite H.
    apply (rig_map_zero u). }
  apply (field_hom_nonzero v _ Hnz).
  rewrite (ftwo_map v).
  exact F2_ftwo_zero.
Qed.

(*
 Restated for the strength the theorems below actually consume: no
 field receives a homomorphism into every field.  Neither the arrow
 out of ℤ nor uniqueness of any factorization plays a part. 

 --------
 重新表述以下定理实际所消耗的力量：没有任何域能接收一个映射到每个域的同态。也没有ℤ的箭头或者任意分解的唯一性起作用。
*)
Corollary no_field_maps_to_all_fields (K : FieldObject)
  (h : ∀ L : FieldObject, RigHom K L) : False.
Proof. exact (no_field_over_Q_and_F2 K (h Q_Field) (h F2_Field)). Qed.

(*
 The two domain categories are genuinely different, as a theorem
 rather than as an expectation: the inclusion of [IntDom] into [Dom]
 is wide, faithful and NOT full, [ZtoF2] being a [Dom]-morphism
 between two objects of [IntDom] whose [IntDom]-hom-set is empty.
 Instance/Rng/Frac.v left non-fullness of [IntDom_Incl] unstated for
 want of a counterexample object; F₂ supplies one, and that statement
 is discharged below as [IntDom_Incl_not_Full] rather than merely
 gestured at here.  ([Full] is qualified because Construction/Subcategory.v
 exports a different, category-indexed [Full] that shadows the
 functor one — the same collision family as [num] above.) 

 --------
 这两个范畴实际上是不同的，作为一个定理而不是期望：将 [IntDom] 包含到 [Dom] 中是宽的、忠实的但不是满的，[ZtoF2] 是 [Dom] 的一个态射，介于 [IntDom] 的两个对象之间，而 [IntDom] 的同态集是空的。Instance/Rng/Frac.v 因缺少反例对象而未说明 [IntDom_Incl] 的非满性；F₂ 提供了一个，并且该陈述在下文中以 [IntDom_Incl_not_Full] 的形式得到解决，而不仅仅是在这里有所暗示。（[Full] 是有限制的，因为 Construction/Subcategory.v 导出了一个不同的、以范畴索引的 [Full]，覆盖了函子版本 —— 与上文 [num] 相同的碰撞族。）
*)
Theorem IntDom_Dom_not_Full :
  Category.Theory.Functor.Full IntDom_Dom → False.
Proof.
  intros [pre _].
  exact (no_DomHom_Z_F2 (@pre Int_Dom (field_dom F2_Field) ZtoF2)).
Qed.

(*
   * And the same witness settles a question Instance/Rng/Frac.v left
   open about a DIFFERENT functor.  That file expects fullness of
   [IntDom_Incl : IntDom ⟶ CRng] to be refutable — a non-injective
   homomorphism between domains has no preimage — but leaves it
   unstated rather than asserted, on the ground that "the tree has no
   quotient rings yet, so no counterexample object is available"
   (Instance/Rng/Frac.v, the comment above [IntDom_Incl]).  The
   counterexample object does not have to be a quotient ring: F₂ is a
   FIELD, hence a domain, and [ZtoF2] is a homomorphism into it that
   [no_DomHom_Z_F2] shows has no [IntDom] preimage.  [CRng]'s
   morphism predicate is trivially [True], so the [CRng] arrow is
   [ZtoF2] paired with [I]. 

   --------
   * 同一个证人解决了关于不同函子的问题 Instance/Rng/Frac.v 留下的未决问题。该文件期望 [IntDom_Incl : IntDom ⟶ CRng] 的充足性是可反驳的——域之间的非单射同态没有原像——但它没有明确声明，而是基于“该树还没有商环，因此没有可用的反例对象”（Instance/Rng/Frac.v 中 [IntDom_Incl] 之上的注释）。反例对象不必是商环：F₂ 是一个域，因此是一个整环，而 [ZtoF2] 是映射到它的同态，[no_DomHom_Z_F2] 显示它没有 [IntDom] 的原像。[CRng] 的态射谓词在逻辑上是 [True]，因此 [CRng] 箭头与 [I] 成对的 [ZtoF2]。
*)
Theorem IntDom_Incl_not_Full :
  Category.Theory.Functor.Full IntDom_Incl → False.
Proof.
  intros [pre _].
  exact (no_DomHom_Z_F2 (@pre Int_Dom (field_dom F2_Field) (existT _ ZtoF2 I))).
Qed.

(* * ** maclane:III.1: no universal arrow from ℤ over ALL homomorphisms / * ** maclane:III.1：不存在从ℤ到所有同态的通用箭头 *)

(*
 Mac Lane's non-example.  Over [Dom] the reduction ℤ → F₂ is a legal
 arrow, so a universal arrow at ℤ would have to factor it through one
 fixed field K — and K would then lie over both ℚ and F₂.  The
 factorizations are the ONLY thing used; their uniqueness is not, nor
 is the universal arrow ℤ → K itself. 

 --------
 Mac Lane 的非例子。在 [Dom] 上，约化 ℤ → F₂ 是一个合法的箭头，因此在 ℤ 上的一个通用箭头必须通过一个固定的域 K 对其进行分解——然后 K 必须同时位于 ℚ 和 F₂ 之上。唯一使用的是这些分解；它们的唯一性没有被使用，通用箭头 ℤ → K 本身也没有被使用。
*)
Theorem no_universal_arrow_Z_Dom
  (U : UniversalArrow (Int_Dom : Dom) Field_Dom) : False.
Proof.
  eapply no_field_over_Q_and_F2.
  - exact (unique_obj (ump_universal_arrows U
             (ZtoQ : Int_Dom ~{Dom}~> Field_Dom Q_Field))).
  - exact (unique_obj (ump_universal_arrows U
             (ZtoF2 : Int_Dom ~{Dom}~> Field_Dom F2_Field))).
Qed.

Theorem no_auniversal_arrow_Z_Dom (K : Field)
  (U : AUniversalArrow (Int_Dom : Dom) Field_Dom K) : False.
Proof.
  eapply no_field_over_Q_and_F2.
  - exact (unique_obj (@universal_arrow_universal _ _ _ _ _ U Q_Field
             (ZtoQ : Int_Dom ~{Dom}~> Field_Dom Q_Field))).
  - exact (unique_obj (@universal_arrow_universal _ _ _ _ _ U F2_Field
             (ZtoF2 : Int_Dom ~{Dom}~> Field_Dom F2_Field))).
Qed.

(*
 And the same over the SMALLER field category the positive half uses,
 so the obstruction is not an artifact of [Field] being too large:
 both ℚ and F₂ are stable, so both remain available as targets. 

 --------
 在较小的域类别中也是一样，正半部分被使用，
 因此障碍不是由于 [Field] 太大造成的：
 ℚ 和 F₂ 都是稳定的，所以两者仍然可以作为目标。
*)
Theorem no_universal_arrow_Z_Dom_stable
  (U : UniversalArrow (Int_Dom : Dom) StableField_Dom) : False.
Proof.
  eapply no_field_over_Q_and_F2.
  - exact `1 (unique_obj (ump_universal_arrows U
             (ZtoQ : Int_Dom ~{Dom}~> StableField_Dom Q_StableField))).
  - exact `1 (unique_obj (ump_universal_arrows U
             (ZtoF2 : Int_Dom ~{Dom}~> StableField_Dom F2_StableField))).
Qed.

Theorem no_auniversal_arrow_Z_Dom_stable (K : StableField)
  (U : AUniversalArrow (Int_Dom : Dom) StableField_Dom K) : False.
Proof.
  eapply no_field_over_Q_and_F2.
  - exact `1 (unique_obj (@universal_arrow_universal _ _ _ _ _ U Q_StableField
             (ZtoQ : Int_Dom ~{Dom}~> StableField_Dom Q_StableField))).
  - exact `1 (unique_obj (@universal_arrow_universal _ _ _ _ _ U F2_StableField
             (ZtoF2 : Int_Dom ~{Dom}~> StableField_Dom F2_StableField))).
Qed.

(* * ** ℤ: the witness, and the two halves side by side / * ** ℤ：见证者，以及并排的两半 *)

Definition Int_zero_dec : DomZeroDec Int_Dom :=
  fun a => match Z.eq_dec a 0%Z with
           | left H  => inl H
           | right H => inr H
           end.

(* Q(ℤ), as an object of the field category. / Q(ℤ)，作为域范畴的一个对象。 *)
Definition Frac_Z : StableField := FracStableField Int_Dom Int_zero_dec.

(*
 The inclusion ℤ ↪ ℚ as a morphism of [IntDom]: [inject_Z] is
 injective because a · 1 ≈ b · 1 in ℤ. 

 --------
 作为  [IntDom] :  [inject_Z]  的态射，包含 ℤ ↪ ℚ 是单射的，因为 a · 1 ≈ b · 1 在 ℤ 中。
*)
Definition ZtoQ_Dom : DomHom Int_Dom (field_dom Q_Field).
Proof.
  refine (Build_DomHom Int_Dom (field_dom Q_Field) ZtoQ _).
  intros a b H.
  assert (H' : (inject_Z a == inject_Z b)%Q) by exact H.
  unfold Qeq, inject_Z in H'; simpl in H'.
  now rewrite !Z.mul_1_r in H'.
Defined.

(*
 THE CONTRAST, at one object and one field category.  Left: over
 [IntDom], whose morphisms are the monomorphisms, ℤ has a universal
 arrow.  Right: over [Dom], whose morphisms are ALL homomorphisms, NO
 object of the same field category carries one.  The categories of
 fields agree; the objects agree; only the domain-side morphisms
 differ, and that decides the question — which is what Mac Lane's
 remark says. 

 --------
 对比，在同一个对象和同一个域的范畴下。左图：在 [IntDom] 上，其态射是单射，ℤ 有一个普适箭头。右图：在 [Dom] 上，其态射是所有同态，没有同一域范畴的对象拥有一个。域的范畴是一致的；对象是一致的；只有域一侧的态射不同，而这决定了问题——这正是 Mac Lane 的评论所说明的。
*)
Theorem frac_universal_over_monos_not_over_all :
  AUniversalArrow (Int_Dom : IntDom) StableField_IntDom Frac_Z
  * (∀ K : StableField,
       AUniversalArrow (Int_Dom : Dom) StableField_Dom K → False).
Proof.
  split.
  - exact (frac_universal_arrow Int_Dom Int_zero_dec).
  - exact no_auniversal_arrow_Z_Dom_stable.
Qed.

(* * ** The extension computes, and the embedding is not onto / * ** 扩展进行了计算，并且嵌入不是满射 *)

(*
 1/2 goes to the rational 1/2: the extension is 1 · (2)⁻¹ in ℚ, which
 reduces on the nose.  Leibniz equality, not [Qeq] — the convertibility
 exception, and it is exhibited because it holds. 

 --------
 1/2 归于有理数 1/2：扩展是 1 · (2)⁻¹ 在 ℚ 中，它恰好化简了。莱布尼茨等式，而不是 [Qeq] —— 可转换性例外，并且它被展示出来，因为它成立。
*)
Example frac_extend_Z_half :
  rig_map (frac_extend Int_Dom Q_Field ZtoQ_Dom)
    (mk_frac Int_Dom 1%Z 2%Z two_nonzero) = (1 # 2)%Q := eq_refl.

Example frac_extend_Z_three :
  rig_map (frac_extend Int_Dom Q_Field ZtoQ_Dom)
    (frac_embed Int_Dom 3%Z) = (3 # 1)%Q := eq_refl.

(*
 The embedding is not onto: 1/2 is not n/1 for any integer n, since
 that would need 2n = 1.  So the fraction field is strictly larger
 than the image of D and the universal arrow is not a degenerate one. 

 --------
 嵌入不是满射：1/2 不是 n/1 对于任何整数 n，因为那样的话需要 2n = 1。所以分数域严格大于 D 的像，并且通用箭头不是退化箭头。
*)
Theorem frac_embed_Z_not_surjective (n : carrier (rig_setoid Int_Dom)) :
  frac_eq Int_Dom (frac_embed Int_Dom n)
    (mk_frac Int_Dom 1%Z 2%Z two_nonzero) → False.
Proof.
  intro H.
  assert (H' : (n * 2)%Z = (1 * 1)%Z) by exact H.
  assert (Hodd : Z.odd (n * 2) = Z.odd (1 * 1)) by (now rewrite H').
  rewrite Z.odd_mul in Hodd; simpl in Hodd.
  destruct (Z.odd n); discriminate Hodd.
Qed.
