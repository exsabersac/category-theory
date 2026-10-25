Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(*
 The global obligation tactic is [cat_simpl], which would run wide proof
 searches on the module obligations below and has already introduced the
 parameters by the time an obligation is opened.  Switched off here, the
 Instance/Mod.v idiom, so every obligation starts with an explicit
 [intros]. 

 --------
 全局义务策略是 [cat_simpl]，它会对下面的模块义务进行广泛的证明搜索，并且在打开义务时已经引入了参数。在此处已关闭 Instance/Mod.v 习惯用法，因此每个义务都以明确的 [intros] 开始。
*)
#[local] Obligation Tactic := idtac.

(*
   * * The free module on a set, and the free-forgetful adjunction

   nLab:      https://ncatlab.org/nlab/show/free+module
   nLab:      https://ncatlab.org/nlab/show/free+object
   nLab:      https://ncatlab.org/nlab/show/universal+morphism
   Wikipedia: https://en.wikipedia.org/wiki/Free_module
   Wikipedia: https://en.wikipedia.org/wiki/Basis_(linear_algebra)
   Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
   GTM 5, §III.1, printed p. 56 (the free vector space on a set as
   the paradigm universal arrow) — maclane:III.1:construction1
   Book: Mac Lane, ibid., §IV.1, printed p. 79 (the same content in
   adjunction form, opening the adjunctions chapter) —
   maclane:IV.1:construction1
   Book: Riehl, Category Theory in Context, §4.0, printed p. 131 (k[S],
   its functoriality in S, and its universal property stated as a
   left adjoint to the underlying-set functor) —
   riehl:4.0:construction-free-vector-space

   WHY THIS CONSTRUCTION OPENS TWO CHAPTERS.  A basis is the oldest
   universal property in mathematics that nobody called universal.  The
   nineteenth-century statement — every vector is uniquely a finite
   linear combination of basis vectors — is exactly the assertion that a
   function defined on the basis extends to a linear map in one and only
   one way, which is to say that the pair (k[S], insertion of the basis)
   solves a universal mapping problem.  Mac Lane opens §III.1 with this
   example because it is the one every reader already knows, and returns
   to it at the head of §IV.1 because the two-variable bijection

   Vect_k(k[S], W)  ≅  Set(S, U W)

   natural in S and in W is the shortest honest description of what an
   adjunction is.  Riehl opens her chapter 4 the same way.  The reason
   the example carries so much weight is that it is *not* about vector
   spaces: the argument uses only that a module is an abelian group with
   a scalar action, so it runs verbatim over an arbitrary ring, and the
   field-specific content of linear algebra (every module is free, every
   basis has the same size) plays no part.  That is why this file is
   stated over Instance/Mod.v's [RMod R] for an arbitrary [RingObject],
   with the vector-space reading — which is the literal content of all
   three catalogued items — split off into Instance/Vect/Free.v, where
   [Vct_F F] is [RMod (field_ring F)] by DEFINITION
   (Instance/FdVect.v) and the specializations are therefore
   conversions rather than transports.

   HOW THE FREE MODULE IS PRESENTED, AND HOW THAT DIFFERS FROM THE
   ISSUE'S SKETCH.  The classical description — "finitely supported
   K-valued functions on X" — presupposes a set of generators with
   decidable equality, and it is worth being exact about WHERE.  The
   CARRIER is not the obstruction: a [≈]-respecting function paired with
   a list witnessing that it vanishes outside that list is writable over
   a bare setoid, and carries zero, pointwise addition and the scalar
   action with no decider anywhere.  The obstruction is the BASIS
   INSERTION, which is what a universal arrow needs: the basis vector at
   x is the function taking 1 at x and 0 elsewhere, and that function
   cannot be WRITTEN without a decision procedure for x ≈ y.  What makes
   this fatal rather than merely restrictive is that [RMod_Forget] lands
   in [Sets], whose objects are setoids, so the left adjoint must exist
   for EVERY generating setoid, decidable or not — a construction
   available only at decidable setoids yields no adjunction at all.  The
   presentation used here is therefore by generators and relations, in
   the style of
   Instance/Ab/Tensor.v and Instance/Sets/Coend.v: [FVTerm] is a plain
   inductive of formal expressions and the equality [fv_eq] is an
   inductive relation closing under exactly the abelian-group laws, the
   four module laws, congruence for each former, saturation under the
   generating setoid's own [≈] and under the ring's, and
   symmetry/transitivity.  Reflexivity is derived ([fv_refl]), keeping
   the relation's induction principle one case shorter everywhere it is
   consumed.  As in Instance/Ab/Tensor.v, [fv_Setoid] is NOT registered
   as a typeclass instance and statements about elements of the free
   module are written with [fv_eq] rather than [≈]; the [≈] of the free
   module as an object of [RMod R] is that relation, definitionally, so
   the module-level lemmas of Instance/Mod.v apply to it unchanged.

   What is lost by not using functions is coefficient uniqueness; what
   is kept is everything the universal property needs, and the classical
   description is recovered in the direction that does not need
   decidability: [fv_normal_form] proves that EVERY element of the free
   module is [fv_eq] to a finite formal linear combination
   r₁·e_{x₁} + … + rₙ·e_{xₙ} of basis vectors ([fv_lc] of a list), which
   is the "finitely supported" half of the classical statement.  The
   other half — that the list is unique up to rearrangement and
   combination of like terms — is exactly what needs a decider on X, and
   it is NOT proved here.  CORRECTION (#472): under that decider it is
   proved, in Instance/Mod/FreeMonad/FinSupp.v, as [fv_lc_unique] (two
   lists denoting the same element have the same collected
   coefficients), whose converse is [fv_coef_injective] (built from
   [fv_collect], which collects like terms), the two packaged as
   [TR_FinSupp_iso] (WHAT IS NOT DELIVERED, below).
   Three non-degeneracy results measure how far
   that leaves the construction from collapsing, and they cost different
   things: [free_module_scalars_faithful] (distinct scalars give
   distinct multiples of a basis vector) needs NO hypothesis at all;
   [free_module_two_independent] (the basis is linearly independent —
   if r·e_x + s·e_y vanishes and x ≉ y then both coefficients vanish,
   which is the statement a reader of §III.1 wants) needs only a decider
   for X's [≈]; and [free_module_basis_injective] (distinct generators
   give distinct basis vectors) needs that decider together with 1 ≉ 0
   in R.  The section header there ARGUES — it does not prove; no
   converse is machine-checked — why hypotheses are needed at all:
   separating two generators means mapping into a module in which they
   go to different places, and building such a map out of a bare setoid
   is the decision procedure.

   STRENGTHS, MEASURED.  The mediator is a [Fixpoint] on formal
   expressions, so:

   - [eq_refl]: the linear extension preserves zero, addition and the
   scalar action DEFINITIONALLY (all three homomorphism obligations
   close by [reflexivity]); it agrees with the given function on
   generators definitionally ([free_module_extend_generators], an
   [eq_refl] on carriers); the free functor's object part is the
   formal-sum module ([FreeMod_obj]); the universal arrow IS the
   basis insertion ([free_module_arrow_is_insert]); the UNIT is the
   one-generator expression ([free_module_unit_is_insert]); and the
   adjunction's forward transpose ⌊−⌋ IS [fv_transpose]
   ([free_module_transpose_is_adj]) — which is what lets the two
   naturality clauses below be stated in the transpose's own
   vocabulary and still be the class's fields verbatim.
   - [≈] only: the COUNIT.  It is the other transpose, i.e.
   [unique_obj (ump_universal_arrows …)], and [ump_universal_arrows]
   (Theory/Universal/Arrow.v) is [Qed]-opaque, so it does not
   compute and no [eq_refl] is claimed on that side.  What is proved
   is that it evaluates a formal linear combination in the module
   ([free_module_counit_evaluates]).
   - [≈] only, and NOT for want of trying: the action of the free
   functor on an arrow.  [LeftAdjointFunctorFromUniversalArrows]
   defines [fmap] by universal factorization rather than by a
   formula, so that it relabels generators is a theorem
   ([free_module_fmap_generators]), not a computation.

   CORRECTION (#472): the counit's diagnosis names one opaque
   constant, and two block it: [ump_universal_arrows] and this file's
   own [free_module_universal], the proof of the factorization that
   [free_module_universal_arrow] hands to [universal_arrow_from_UMP]
   and from which both the counit and the free functor's [fmap] are
   read.  Measured by #472's scout in a rebuilt copy of the seventy
   modules its prototype loads, on nine conversions the monad T_R
   would read off this adjunction (U ε F at a basis vector, at a
   variable combination and at zero; [fmap] at the same three; the
   comparison functor's structure map at a variable combination, at a
   sum of two basis vectors and at a basis vector): with
   [ump_universal_arrows] alone turned [Defined], all nine are still
   refused; with [free_module_universal] alone, all nine; with both,
   all nine hold at [eq_refl], [fmap] at a variable combination
   included.  #472 measured the same on Test/ProbeFreeModule472.v's
   refutations (its header).  Neither constant is turned [Defined]
   here: [ump_universal_arrows] is shared by many developments, several
   of which pin its opacity in probes, and issue #1353 tracks it.  #472
   adds instead the same adjunction in hom-set form,
   [free_module_adjunction_hom] (THE HOM-SET FORM, below), whose counit
   IS the fold by conversion; the free functor's [fmap] is unchanged,
   and stays [≈]-only on both forms.

   THE TWO NATURALITY CLAUSES.  §IV.1 asks for naturality of the
   bijection in each variable separately, and both are stated and proved
   here in the free module's own vocabulary rather than by citing the
   class: [free_module_naturality_in_set] (in the generating set, proved
   by evaluating on generators through [free_module_fmap_generators])
   and [free_module_naturality_in_module] (in the target module, proved
   pointwise by [reflexivity], both sides being the same composite of
   underlying functions).  That they are the class's own fields
   [to_adj_nat_l] and [to_adj_nat_r] at this adjunction is then recorded
   by [eq_refl] on the STATEMENTS
   ([free_module_naturality_in_set_is_to_adj_nat_l] and its sibling) —
   a conversion check that the independently proved theorems are the
   fields, not a second derivation of them.

   THE HOM-SET FORM (#472).  Two packagings of the one adjunction FreeMod R ⊣
   RMod_Forget R are kept.  [free_module_adjunction], from the universal
   arrows, is the one the rest of the tree consumes (Instance/Vect/Free.v,
   Instance/Mod/Representable.v, Instance/Rng/Polynomial.v and
   Instance/Rng/AFT.v name it), and it is unchanged.
   [free_module_adjunction_hom] is Theory/Adjunction.v's [Build_Adjunction']
   applied to the natural bijection [free_module_hom_iso], with the same left
   adjoint [FreeMod R], the same right adjoint and the same insertion: its
   unit and its forward transpose ARE those of [free_module_adjunction] at
   [eq_refl] ([free_module_hom_unit], [free_module_hom_to]), its two
   naturality fields are the two theorems above, cited, and its inverse
   transpose is the linear extension [fv_extend], so its counit is the fold
   of the identity at [eq_refl] ([free_module_hom_counit]), where the other
   counit is that fold only at `≈` ([free_module_counit_evaluates]).  It
   exists for the free R-module monad T_R of Mac Lane's §VI.4 Exercise 2
   (Instance/Mod/FreeMonad.v), whose multiplication U ε F and comparison
   functor then compute.  It is not a second free module and not a second
   free functor.  The two adjunctions are refused equal at [eq_refl], and so
   are their counits at a variable combination (Test/ProbeFreeModule472.v, R1
   and R2).  Its universes: the hom-set form binds @{a c p so} (R :
   RingObject@{a c p}, Sets@{c so}) and the five levels [FreeMod] carries
   beyond them, extensibly, a closed binder being refused for those internal
   levels; the adjunction's own last level, which no constraint mentions when
   left free, is pinned to so ([Adjunction@{_ c c so c c c c so c so}], the
   pin of Instance/Mon/Free.v's hom-set form), and the two readbacks
   comparing with [free_module_adjunction] pin that adjunction's free level
   the same way, by a cast.  No [Set] but the bound Set < m on the module
   category's object level m (Instance/Mod.v's [RMod]), and no equation.
   [free_module_hom_iso] and [free_module_adjunction_hom] end [Defined], both
   load-bearing (each closed alone [Qed] in a renamed copy of #472's files,
   [free_module_adjunction_hom] and [free_module_hom_counit] respectively
   stop); [fv_eval_pointwise] ends [Qed].  The six are "Closed under the
   global context" and named in #472's print-assumptions block.  On Coq
   8.19.2 and 8.20.1 the five that bind [FreeMod]'s levels bind exactly one
   level more and [fv_eval_pointwise] the same, compared by [About].

   WHAT IS NOT DELIVERED.

   - No uniqueness of coefficients.  [fv_normal_form] IS proved —
   every element is [fv_eq] to some [fv_lc l] — so what is missing
   is not the existence of a linear-combination form but its
   CANONICITY: the list is not unique up to rearrangement and
   collection of like terms, and nothing here says two lists
   denoting the same element are related.  Hence also no decision
   procedure for equality in the free module, no dimension, and no
   proof that the basis insertion is injective for a GENERAL
   generating setoid (see above for why).
   CORRECTION (#472): coefficient uniqueness is proved under a
   decider for X's [≈], by Instance/Mod/FreeMonad/FinSupp.v's
   [fv_lc_unique]: two lists denoting the same element have, at
   every point, the same collected coefficient, the sum of the
   coefficients of their pairs at points [≈] to it ([fv_coef_lc]).
   It is the respectfulness of the coefficient map, the coefficient
   of y being the linear extension of this file's own indicator
   [fv_probe_at] into R (Instance/Mod/FreeMonad.v's [fv_coef]).  Its
   converse, injectivity, is [fv_coef_injective] (a combination is
   [fv_eq] to any other with the same coefficients), built from
   [fv_collect], which collects like terms; and [TR_FinSupp_iso]
   packages both, the free module's setoid isomorphic in [Sets] to
   the finitely supported functions X → R.  For a GENERAL generating
   setoid it is still not proved, and the decision procedure, the
   dimension and the comparison below are still absent.
   - No statement that [FreeMod] is faithful, and no characterization
   of its image; no proof that a free module is projective; no
   invariant basis number.
   - No comparison with Instance/FdVect.v's [StdVect] (which carries a
   chosen coordinate isomorphism to Fⁿ), and so no proof that the
   free module on [Fin.t n] is finite-dimensional in that file's
   sense — that comparison needs the coefficient uniqueness just
   disclaimed. 

   --------
   * * 集合上的自由模以及自由-忘记伴随关系

   nLab:       https://ncatlab.org/nlab/show/free+module 
   nLab:       https://ncatlab.org/nlab/show/free+object 
   nLab:       https://ncatlab.org/nlab/show/universal+morphism 
   Wikipedia:  https://en.wikipedia.org/wiki/Free_module 
   Wikipedia:  https://en.wikipedia.org/wiki/Basis_(linear_algebra) 
   书籍: Mac Lane, 《为工作数学家准备的范畴论》，第2版,
   GTM 5, §III.1, 第56页印刷版（作为范例的集合上自由向量空间
   的泛箭） — maclane:III.1:construction1
   书籍: Mac Lane, 同上, §IV.1, 第79页印刷版（以伴随形式呈现的相同内容，
   开启伴随章节） — maclane:IV.1:construction1
   书籍: Riehl, 《背景下的范畴论》，§4.0, 第131页印刷版 (k [S] ,
   它在 S 上的函子性，以及其作为基础集合函子的左伴随所表述的
   泛性质) — riehl:4.0:construction-free-vector-space为什么这种结构展开了两章。基是数学中最古老的普遍性质，但没有人称之为普遍性质。十九世纪的表述——每个向量都唯一地是基向量的有限线性组合——恰好是断言定义在基上的函数以一种且仅有一种方式扩展为线性映射，也就是说，(k [S], 基的插入) 这对解决了一个普遍映射问题。Mac Lane 在 §III.1 开始时用这个例子，因为这是每位读者已经知道的例子，并在 §IV.1 开头再次提到它，因为这个二变量双射

   Vect_k(k [S] , W)  ≅  Set(S, U W)在 S 和 W 中自然，是对伴随是什么的最简诚实描述。Riehl 在她的第四章也是以同样的方式开篇的。这个例子之所以如此重要，是因为它*不是*关于向量空间的：论证只使用了一个模是具有标量作用的阿贝尔群这一事实，因此它可以逐字适用于任意环，而线性代数中特定于域的内容（每个模都是自由的，每个基的大小都相同）并不起作用。这就是为什么该文件在任意 [RingObject] 的情况下被声明在 Instance/Mod.v 的 [RMod R] 上，并且向量空间的读法——这是所有三个已编目的条目的字面内容——被拆分到 Instance/Vect/Free.v，其中 [Vct_F F] 根据定义 (Instance/FdVect.v) 是 [RMod (field_ring F)]，因此这些特化是转换而不是搬运。自由模是如何呈现的，以及这与问题的草图有何不同。经典描述——“X 上的有限支撑 K 值函数”——预设了一组具有可判等性的生成元，并且值得准确说明是在什么地方。承载体不是障碍：一个遵守 [≈] 的函数，配合一个列表来证明它在该列表之外为零，是可以在一个裸集合之上书写的，并且可以承载零、逐点加法以及标量作用，而无需任何判定器。障碍是基的插入，这也是泛箭所需要的：在 x 处的基向量是一个函数，它在 x 处取 1，其他地方取 0，而没有 x ≈ y 的判定程序，这个函数无法被书写。使这个问题致命而不仅仅是限制性的是 [RMod_Forget] 落在 [Sets] 中，其对象是集合等价物，因此左伴随必须针对每一个生成的集合等价物存在，无论是否可判定——仅在可判定集合等价物上可用的构造根本无法产生伴随。因此，这里使用的表达方式是通过生成元和关系的方式，类似于 Instance/Ab/Tensor.v 和 Instance/Sets/Coend.v：[FVTerm] 是一个形式表达式的普通归纳类型，而等式 [fv_eq] 是一个归纳关系，严格按照阿贝尔群法则、四个模律、每个前者的相容性、在生成集合等价物自身的 [≈] 以及环的饱和性、对称性/传递性闭合。反身性是派生的（[fv_refl]），在每个使用该关系的地方，使关系的归纳原理少一例。如在 Instance/Ab/Tensor.v 中，[fv_Setoid] 并未注册为类型类实例，且关于自由模元素的陈述是用 [fv_eq] 而不是 [≈] 写的；自由模作为 [RMod R] 的对象的 [≈] 在定义上就是该关系，因此 Instance/Mod.v 的模级引理对其保持不变。不使用函数所失去的是系数的唯一性；保留下来的则是通用性质所需要的一切，并且在不需要可判定性的方向上恢复了经典描述：[fv_normal_form] 证明自由模的每个元素都可以表示为基向量（[fv_lc] 列表的元素）的有限形式线性组合 r₁·e_{x₁} + … + rₙ·e_{xₙ}（[fv_eq]），这是经典说法中“有限支撑”的一半。另一半——即列表在重新排列和合并同类项后是唯一的——正是需要对 X 进行判定的内容，而这里并未证明。更正 (#472)：在该决策器下，它在 Instance/Mod/FreeMonad/FinSupp.v 中被证明为 [fv_lc_unique]（表示相同元素的两个列表具有相同的收集系数），其逆为 [fv_coef_injective]（由 [fv_collect] 构建，后者收集同类项），两者打包为 [TR_FinSupp_iso]（如下未提供）。三个非退化结果衡量了构造离崩塌的距离，它们各自的代价不同：[free_module_scalars_faithful]（不同的标量给出基向量的不同倍数）完全不需要假设；[free_module_two_independent]（基是线性无关的——如果 r·e_x + s·e_y 消失且 x ≉ y，则两个系数都消失，这是§III.1读者想要的陈述）只需要对 X 的 [≈] 有一个判定器；而 [free_module_basis_injective]（不同的生成元给出不同的基向量）则需要该判定器以及 R 中的 1 ≉ 0。那里小节标题是论证——它并不证明；没有进行逆向机器检查——为什么根本需要假设：分离两个生成元意味着将它们映射到一个在其中它们去向不同的模上，而从一个裸集合构建这样的映射就是判定过程。

   优点，已衡量。中介是一个作用于形式表达式的  [Fixpoint]，因此：-  [eq_refl]：线性扩展在定义上保持零、加法和标量作用（所有三个同态条件由 [reflexivity] 完成）；它在生成元上与给定函数在定义上相同（[free_module_extend_generators]，以及载体上的 [eq_refl]）；自由函子的对象部分是形式和模块（[FreeMod_obj]）；通用箭头是基的插入（[free_module_arrow_is_insert]）；单位是单生成元表达式（[free_module_unit_is_insert]）；伴随的前向转置 ⌊−⌋ 是 [fv_transpose]（[free_module_transpose_is_adj]）——这使得下面的两个自然性条款可以用转置自身的词汇来表示，并且仍然逐字对应类的字段。- 仅 [≈]：余单位。它是另一个转置，即。[unique_obj (ump_universal_arrows …)]，和 [ump_universal_arrows]（Theory/Universal/Arrow.v）是 [Qed] 不透明的，因此它不会计算，也没有在该方面声称 [eq_refl]。所证明的是它在模 ([free_module_counit_evaluates]) 中求解形式线性组合。- 仅 [≈]，而不是由于没有尝试：自由函子在箭头上的作用。[LeftAdjointFunctorFromUniversalArrows] 通过普遍分解而不是公式来定义 [fmap]，因此它重新标记生成元是一个定理 ([free_module_fmap_generators])，而不是计算。更正 (#472)：余单位的诊断列出了一个不透明常量，以及两个屏蔽它的常量：[ump_universal_arrows] 和这个文件自己的 [free_module_universal]，因式分解的证明是 [free_module_universal_arrow] 交给 [universal_arrow_from_UMP] 的，从中可以读取余单位和自由函子的 [fmap]。由 #472 在重建的七十模块原型载入副本中测量，其侦测器在九次转换中，单子 T_R 会读出这个伴随（U ε F 在基向量、变量组合和零处；[fmap] 在同三个处；比较函子在变量组合、两个基向量的和及一个基向量处的结构映射）：仅使用 [ump_universal_arrows] 时变为 [Defined]，九次仍全部被拒绝；仅使用 [free_module_universal] 时，九次仍然如此；两者同时使用时，所有九次在 [eq_refl] 处成立，[fmap] 在包括变量组合的情况下也成立。#472 在 Test/ProbeFreeModule472.v 的反例（其头文件）中测量到了相同结果。这里没有一个常量被转动 [Defined]：[ump_universal_arrows] 被许多开发共享，其中几个在探针中固定了它的透明度，并且问题 #1353 正在跟踪它。#472 取而代之的是在同构集形式中添加相同的附加，[free_module_adjunction_hom]（下面的同构集形式），其余单位是通过转换的折叠；自由函子 [fmap] 保持不变，并且在两种形式上保持仅 [≈]。两个自然性条款。§IV.1 要求双射在每个变量上分别具有自然性，并且这里都用自由模自身的表述来说明和证明，而不是引用类：[free_module_naturality_in_set]（在生成集上，通过在生成元上评估 [free_module_fmap_generators] 证明）和 [free_module_naturality_in_module]（在目标模上，通过 [reflexivity] 对每一点逐一证明，双方都是基础函数的相同复合）。它们是该陪集的类自身字段 [to_adj_nat_l] 和 [to_adj_nat_r] 这一点随后由 [eq_refl] 在陈述（[free_module_naturality_in_set_is_to_adj_nat_l] 及其对应项）中记录——这是一个转换检查，确认独立证明的定理确实是这些字段，而不是对它们的第二次推导。同构集形式 (#472)。保留了同一个伴随函子 FreeMod R ⊣ RMod_Forget R 的两个封装。[free_module_adjunction]，从通用箭头中，是树的其余部分使用的那个（Instance/Vect/Free.v、Instance/Mod/Representable.v、Instance/Rng/Polynomial.v 和 Instance/Rng/AFT.v 给它命名），并且它保持不变。[free_module_adjunction_hom] 是 Theory/Adjunction.v 的 [Build_Adjunction']，应用于自然双射 [free_module_hom_iso]，具有相同的左伴随 [FreeMod R]、相同的右伴随和相同的插入：它的单元及其正向转置是 [free_module_adjunction] 在 [eq_refl]（[free_module_hom_unit]，[free_module_hom_to]）的单元及转置，它的两个自然性域是上面引用的两个定理，而其逆转置是线性扩展 [fv_extend]，因此它的余单元是 [eq_refl]（[free_module_hom_counit]）上的恒等映射的折叠，而另一个余单元仅在 `≈`（[free_module_counit_evaluates]）上是该折叠。它存在于 Mac Lane §VI.4 练习 2（Instance/Mod/FreeMonad.v）的自由 R-模单子 T_R 中，其乘法 U ε F 和比较函子随后进行计算。它不是第二个自由模，也不是第二个自由函子。这两个伴随在 [eq_refl] 处被拒绝相等，因此它们在一个变量组合 (Test/ProbeFreeModule472.v, R1 和 R2) 处的余单位也是如此。其宇宙：同态集形式绑定 @{a c p so} (R : RingObject@{a c p}, Sets@{c so})，而五个层次 [FreeMod] 在它们之外扩展地承载了一个被拒绝用于这些内部层次的封闭绑定器；伴随自身的最后一层，当保持自由时没有任何约束提到，被固定为 so ([Adjunction@{_ c c so c c c c so c so}]，Instance/Mon/Free.v 的 hom-set 形式的固定点)，两个读取回比对 [free_module_adjunction]，以同样的方式通过类型转换固定该伴随的自由层。除了模块范畴对象层 m (Instance/Mod.v 的 [RMod]) 上绑定的集合 < m，没有其他 [Set]，也没有方程。[free_module_hom_iso] 和 [free_module_adjunction_hom] 结束于 [Defined]，两者均承载重量（每个单独关闭 [Qed] 在 #472 文件的重命名副本中，ZW102WZZ 和 [free_module_hom_counit] 分别停止）；[fv_eval_pointwise] 结束于 [Qed]。这六个是“在全局上下文下关闭”的，并在 #472 的打印假设块中命名。在 Coq 8.19.2 和 8.20.1 上，绑定 [FreeMod] 的五个绑定恰好多一个层次，而 [fv_eval_pointwise] 保持不变，通过 [About] 进行比较。

   未交付的内容是什么。- 系数没有唯一性。[fv_normal_form] 已被证明——每个元素都是某个 [fv_lc l] 的 [fv_eq] ——所以缺失的不是线性组合形式的存在性，而是它的规范性：列表在重新排列和同类项合并下不是唯一的，这里也没有说明表示同一元素的两个列表之间有关系。因此，自由模中也没有判等的决策程序，没有维度，并且没有证明对于一般的生成集（见上文原因）基的插入是单射的。更正 (#472)：在 X 的 [≈] 的判定器下证明了系数的唯一性，由 Instance/Mod/FreeMonad/FinSupp.v 的 [fv_lc_unique]：表示相同元素的两个列表在每一点上具有相同的累积系数，它们在 [≈] 点的成对系数之和（[fv_coef_lc]）。这是系数映射的恭敬性，y 的系数是将此文件自身的指示器 [fv_probe_at] 线性扩展到 R（Instance/Mod/FreeMonad.v 的 [fv_coef]）。它的逆命题，即单射性，是 [fv_coef_injective]（一个组合是 [fv_eq] 对于任何具有相同系数的其他组合），由 [fv_collect] 构建，它收集同类项；而 [TR_FinSupp_iso] 同时打包两者，自由模的集合同构在 [Sets] 中到有限支持函数 X → R。对于一个一般的生成集合，仍未被证明，并且决策过程、维数和下面的比较仍然缺失。- 没有说明 [FreeMod] 是忠实的，也没有其像的表征；没有证明自由模是投射模；没有不变基数。- 没有与 Instance/FdVect.v 中的 [StdVect] 进行比较（它携带一个选定的坐标同构到 Fⁿ），因此也没有证明在该文件的意义下 [Fin.t n] 上的自由模是有限维的——这种比较需要刚刚否认的系数唯一性。
*)

(* * ** Formal linear combinations and the module quotient / * ** 形式线性组合与模商 *)

Section FreeModule.

Context (R : RingObject).
Context (X : SetoidObject).

(*
 Formal expressions over the generating setoid: generators, zero, sum,
 negation, scalar multiple.  Negation is a CONSTRUCTOR rather than the
 derived (−1)·(−): deriving it would need 0·t ≈ 0 in the free module,
 whose usual proof cancels [0·t] against itself and so already needs
 the group structure being built. 

 --------
 在生成的集合等价类上的形式表达式：生成元、零、和、取反、标量倍数。取反是一个构造子，而不是派生的 (−1)·(−)：若要派生它，需要在自由模中 0·t ≈ 0，其通常的证明会将 [0·t] 自身互相抵消，因此已经需要建立群结构。
*)
Inductive FVTerm : Type :=
  | fv_gen  : carrier X → FVTerm
  | fv_zero : FVTerm
  | fv_plus : FVTerm → FVTerm → FVTerm
  | fv_neg  : FVTerm → FVTerm
  | fv_smul : carrier (rig_setoid (ring_rig R)) → FVTerm → FVTerm.

(*
 The quotienting relation: congruence for each former (saturating under
 the generating setoid's [≈] and the ring's), the abelian-group laws,
 the four module laws, symmetry and transitivity.  Reflexivity is
 derived below. 

 --------
 商关系：每个前者的同余（在生成集合的 [≈] 和环下饱和）、阿贝尔群定律、四条模定律、对称性和传递性。自反性将在下文推导。
*)
Inductive fv_eq : FVTerm → FVTerm → Prop :=
  | fe_gen {x y : carrier X} : x ≈ y → fv_eq (fv_gen x) (fv_gen y)
  | fe_plus {s s' t t'} :
      fv_eq s s' → fv_eq t t' → fv_eq (fv_plus s t) (fv_plus s' t')
  | fe_neg {s s'} : fv_eq s s' → fv_eq (fv_neg s) (fv_neg s')
  | fe_smul {r r' : carrier (rig_setoid (ring_rig R))} {s s'} :
      r ≈ r' → fv_eq s s' → fv_eq (fv_smul r s) (fv_smul r' s')

  (* abelian group / 阿贝尔群 *)
  | fe_assoc (s t u : FVTerm) :
      fv_eq (fv_plus (fv_plus s t) u) (fv_plus s (fv_plus t u))
  | fe_comm (s t : FVTerm) : fv_eq (fv_plus s t) (fv_plus t s)
  | fe_zero_l (s : FVTerm) : fv_eq (fv_plus fv_zero s) s
  | fe_neg_l (s : FVTerm) : fv_eq (fv_plus (fv_neg s) s) fv_zero

  (* module *)
  | fe_smul_distr_l (r : carrier (rig_setoid (ring_rig R))) (s t : FVTerm) :
      fv_eq (fv_smul r (fv_plus s t))
            (fv_plus (fv_smul r s) (fv_smul r t))
  | fe_smul_distr_r (r r' : carrier (rig_setoid (ring_rig R))) (s : FVTerm) :
      fv_eq (fv_smul (rig_add (ring_rig R) r r') s)
            (fv_plus (fv_smul r s) (fv_smul r' s))
  | fe_smul_assoc (r r' : carrier (rig_setoid (ring_rig R))) (s : FVTerm) :
      fv_eq (fv_smul (rig_mul (ring_rig R) r r') s)
            (fv_smul r (fv_smul r' s))
  | fe_smul_one (s : FVTerm) :
      fv_eq (fv_smul (rig_one (ring_rig R)) s) s

  | fe_sym {s t} : fv_eq s t → fv_eq t s
  | fe_trans {s t u} : fv_eq s t → fv_eq t u → fv_eq s u.

Lemma fv_refl (s : FVTerm) : fv_eq s s.
Proof.
  induction s.
  - exact (fe_gen (reflexivity _)).
  - exact (fe_trans (fe_sym (fe_zero_l fv_zero)) (fe_zero_l fv_zero)).
  - exact (fe_plus IHs1 IHs2).
  - exact (fe_neg IHs).
  - exact (fe_smul (reflexivity _) IHs).
Qed.

Lemma fv_eq_Equivalence : Equivalence fv_eq.
Proof.
  constructor.
  - exact fv_refl.
  - exact (fun s t => fe_sym).
  - exact (fun s t u => fe_trans).
Qed.

Definition fv_Setoid : Setoid FVTerm := {|
  equiv        := fv_eq;
  setoid_equiv := fv_eq_Equivalence
|}.

(*
   * ** The free module

   Every law of the module is a constructor of the relation; nothing is
   proved.  The record is written out in one literal so that the
   underlying setoid, the group operations and the action are all
   visible at a glance and all reduce.  An earlier revision stopped there; the record now
   carries one more field, [cmon_prop], and it too is a one-liner: the
   relation IS a [Prop] since the PR "algebraic carriers are sets"
   (2026-09-17), so it is its own [Prop] mirror and both implications are
   the identity. 

   --------
   * ** 自由模

   模的每条定律都是关系的构造；没有什么被证明。记录以一个字面量写出，以便基本的集扎、群运算和作用一目了然，并且都可以简化。早期的修订停在这里；现在记录增加了一个字段 [cmon_prop]，它也是一行代码：该关系是一个 [Prop]，因为 PR "代数载体是集合"（2026-09-17），所以它本身就是它的 [Prop] 镜像，而且两个蕴含都是恒等式。
*)
Definition FreeModObject : RModObject R := {|
  rm_ab := {|
    ab_cmon := {|
      cmon_setoid := {| carrier := FVTerm; is_setoid := fv_Setoid |};
      cmon_zero := fv_zero;
      cmon_plus := fv_plus;
      cmon_plus_respects := fun _ _ Hs _ _ Ht => fe_plus Hs Ht;
      cmon_plus_assoc := fe_assoc;
      cmon_plus_comm := fe_comm;
      cmon_plus_zero_l := fe_zero_l;
      (* [fv_eq] IS a [Prop] relation, so it is its own [Prop] mirror. / [fv_eq] 是一个 [Prop] 关系，因此它是它自己的 [Prop] 镜像。 *)
      cmon_prop := @PropEquiv_of_relation _ fv_Setoid fv_eq
                     (fun _ _ h => h) (fun _ _ h => h)
    |};
    ab_neg := fv_neg;
    ab_neg_respects := fun _ _ Hs => fe_neg Hs;
    ab_neg_left := fe_neg_l
  |};
  rm_smul := fv_smul;
  rm_smul_respects := fun _ _ Hr _ _ Hs => fe_smul Hr Hs;
  rm_smul_distr_l := fe_smul_distr_l;
  rm_smul_distr_r := fe_smul_distr_r;
  rm_smul_assoc := fe_smul_assoc;
  rm_smul_one := fe_smul_one
|}.

(*
   * ** The insertion of the basis

   A generator becomes the corresponding formal expression.
   Respectfulness is the congruence constructor [fe_gen], supplied by
   [exact] rather than as a record field: the target's [≈] is [fv_eq]
   by conversion but not by unification, and only [exact] will convert. 

   --------
   * ** 基的插入

   一个生成器变为相应的形式表达式。
   遵从性是由 [exact] 提供的同余构造器 [fe_gen]，而不是作为记录字段：目标的 [≈] 是通过转换而非同一化得到的 [fv_eq]，并且只有 [exact] 会转换。
*)
Definition fv_insert : X ~{Sets}~> RMod_Forget R FreeModObject.
Proof.
  unshelve refine {| morphism := fv_gen |}.
  intros x y H; exact (fe_gen H).
Defined.

(* * ** The linear extension of a function on generators / * ** 函数在生成元上的线性扩展 *)

Section Extension.

Context (W : RModObject R).
Context (h : X ~{Sets}~> RMod_Forget R W).

(*
 Fold a formal expression through the target module's operations.  It
 computes on constructors, which is what makes all three homomorphism
 obligations below hold by [reflexivity]. 

 --------
 通过目标模块的操作折叠一个形式表达式。它在构造子上进行计算，这正是使下面的三个同态义务通过 [reflexivity] 成立的原因。
*)
Fixpoint fv_eval (t : FVTerm) : carrier (cmon_setoid W) :=
  match t with
  | fv_gen x    => h x
  | fv_zero     => cmon_zero W
  | fv_plus s t => cmon_plus W (fv_eval s) (fv_eval t)
  | fv_neg s    => ab_neg W (fv_eval s)
  | fv_smul r s => rm_smul W r (fv_eval s)
  end.

(*
 Respectfulness is one induction over the relation: 14 cases, one per
 constructor of [fv_eq].  Eight are met by the corresponding law of the
 target module (four abelian-group, four module); the other six are
 not laws — [fe_gen] is saturation under X's own [≈], three are
 congruence for a former, and two are the target setoid's symmetry and
 transitivity. 

 --------
 尊重性是关于关系的一种归纳：14种情况，每种对应  [fv_eq] 的一个构造子。其中八种情况由目标模的相应定律满足（四个阿贝尔群，四个模）；其他六种情况不是定律——[fe_gen] 是在 X 自身的 [≈] 下的饱和，三种是前者的同余，另外两种是目标集合等价关系的对称性和传递性。
*)
Lemma fv_eval_respects (s t : FVTerm) : fv_eq s t → fv_eval s ≈ fv_eval t.
Proof.
  intro He.
  (*
 Since the PR "algebraic carriers are sets" (2026-09-17) [fv_eq] is a
 [Prop] inductive and eliminates only into [Prop] goals, while `≈` is
 [Type]-valued.  [pequiv_to] puts a [Prop] goal in front of the
 elimination; each branch returns to `≈` with [pequiv_from].  The 14 cases
 and what discharges each are exactly as before. 

 --------
 自从 PR “代数承载是集合”（2026-09-17）以来，[fv_eq] 是一个 [Prop] 归纳，并且只消除到 [Prop] 目标，而 `≈` 是 [Type] 值。[pequiv_to] 在消除前放置了一个 [Prop] 目标；每个分支都带着 [pequiv_from] 返回到 `≈`。14 种情况以及每种情况的处理方式与以前完全相同。
*)
  apply pequiv_to.
  induction He as
    [ x y Hxy
    | s s' t t' _ IHs _ IHt
    | s s' _ IHs
    | r r' s s' Hr _ IHs
    | s t u | s t | s | s
    | r s t | r r' s | r r' s | s
    | s t _ IHst
    | s t u _ IHst _ IHtu ]; simpl.
  - apply pequiv_from; exact (proper_morphism h _ _ Hxy).
  - apply pequiv_from.
    exact (cmon_plus_respects W _ _ (pequiv_to _ _ IHs)
                                _ _ (pequiv_to _ _ IHt)).
  - apply pequiv_from.
    exact (ab_neg_respects W _ _ (pequiv_to _ _ IHs)).
  - apply pequiv_from.
    exact (rm_smul_respects W _ _ Hr _ _ (pequiv_to _ _ IHs)).
  - apply pequiv_from; exact (cmon_plus_assoc W _ _ _).
  - apply pequiv_from; exact (cmon_plus_comm W _ _).
  - apply pequiv_from; exact (cmon_plus_zero_l W _).
  - apply pequiv_from; exact (ab_neg_left W _).
  - apply pequiv_from; exact (rm_smul_distr_l W _ _ _).
  - apply pequiv_from; exact (rm_smul_distr_r W _ _ _).
  - apply pequiv_from; exact (rm_smul_assoc W _ _ _).
  - apply pequiv_from; exact (rm_smul_one W _).
  - exact (symmetry IHst).
  - exact (transitivity IHst IHtu).
Qed.

(*
 The extension, as a morphism of [RMod R].  The four obligations are
 respectfulness of the fold and preservation of zero, of addition and
 of the action; the last three hold by [reflexivity], the fixpoint's
 clauses BEING those three equations.  One uniform body is used so that
 the proof does not depend on the order [Program] emits them in.  Still
 four after the PR "algebraic carriers are sets" (2026-09-17),
 re-counted from the [_obligation_] names [Print Module] lists. 

 --------
 该扩展作为  [RMod R] 的一个态射。四个义务是对折叠的尊重以及零、加法和作用的保持；后三个由  [reflexivity] 保证，定点的条款是那三个方程。使用一个统一的主体，以便证明不依赖于 [Program] 发出它们的顺序。仍然是四个，在 PR “代数载体是集合”（2026-09-17）之后，根据 [_obligation_] 名称 [Print Module] 列表重新计算。
*)
Program Definition fv_extend : FreeModObject ~{RMod R}~> W := {|
  rm_hom := {| cmon_map := {| morphism := fv_eval |} |}
|}.
Next Obligation.
  first [ (intros s t He; exact (fv_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fv_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fv_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fv_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.

(* It agrees with [h] on the basis — definitionally, not up to [≈]. / 它在基础上同意 [h] 的观点——从定义上讲，而不是依据 [≈]。 *)
Example free_module_extend_generators (x : carrier X) :
  cmon_map (rm_hom fv_extend) (fv_gen x) = h x := eq_refl.

(*
 The three homomorphism laws, recorded at Leibniz [=] on the CARRIER so
 that the header's strength claim is machine-checked rather than
 inferred from which branch of the obligation tactic fired.  This is
 the convertibility exception: these are equations between elements of
 [W]'s carrier, not between morphisms. 

 --------
 三个同态定律，记录在 Leibniz [=] 上的 CARRIER 上，以便头部的强度声明是经过机器检查的，而不是从义务策略触发的分支推断出来的。这是可转换性例外：这些是 [W] 的承载元素之间的方程，而不是态射之间的方程。
*)
Example free_module_extend_zero :
  cmon_map (rm_hom fv_extend) fv_zero = cmon_zero W := eq_refl.

Example free_module_extend_plus (s t : FVTerm) :
  cmon_map (rm_hom fv_extend) (fv_plus s t)
    = cmon_plus W (cmon_map (rm_hom fv_extend) s)
                  (cmon_map (rm_hom fv_extend) t) := eq_refl.

Example free_module_extend_smul
  (r : carrier (rig_setoid (ring_rig R))) (s : FVTerm) :
  cmon_map (rm_hom fv_extend) (fv_smul r s)
    = rm_smul W r (cmon_map (rm_hom fv_extend) s) := eq_refl.

(*
   * *** Uniqueness

   Any module homomorphism out of the free module agreeing with [h] on
   the basis IS the extension.  The induction has one case per former,
   five in all: the generator case is the agreement hypothesis [Hg]
   itself, and the other four are homomorphism laws of the competitor —
   preservation of zero, of sums, of negation (Instance/Mod.v's
   [rmod_map_neg], which is Instance/Ab.v's [ab_map_neg] and not a
   field) and of the action. 

   --------
   * *** 唯一性

   从自由模出发的任何模同态，只要在基上与 [h] 一致，就是该扩展。归纳法每一种先前情况有一个分支，总共五个：生成元情况就是一致性假设 [Hg] 本身，而其他四个则是竞争者的同态定律——保持零元、保持和、保持取反（Instance/Mod.v 的 [rmod_map_neg]，即 Instance/Ab.v 的 [ab_map_neg]，并非域）以及保持作用。
*)
Lemma fv_extend_unique (g : FreeModObject ~{RMod R}~> W)
  (Hg : ∀ x : carrier X, cmon_map (rm_hom g) (fv_gen x) ≈ h x) (t : FVTerm) :
  cmon_map (rm_hom g) t ≈ fv_eval t.
Proof.
  induction t as [ x | | t1 IHt1 t2 IHt2 | t IHt | r t IHt ]; simpl.
  - exact (Hg x).
  - exact (cmon_map_zero (rm_hom g)).
  - refine (transitivity (cmon_map_plus (rm_hom g) t1 t2) _).
    exact (cmon_plus_respects W _ _ IHt1 _ _ IHt2).
  - refine (transitivity (rmod_map_neg g t) _).
    exact (ab_neg_respects W _ _ IHt).
  - refine (transitivity (rm_map_smul g r t) _).
    exact (rm_smul_respects W _ _ (reflexivity r) _ _ IHt).
Qed.

End Extension.

Arguments fv_eval {W} h t.
Arguments fv_extend {W} h.

(*
   * ** The universal property, in the shape [universal_arrow_from_UMP]
   consumes 

   --------
   * ** 通用性质，在形状 [universal_arrow_from_UMP] 中消耗
*)
Theorem free_module_universal :
  ∀ (W : RModObject R) (h : X ~{Sets}~> RMod_Forget R W),
    ∃! g : FreeModObject ~{RMod R}~> W,
      h ≈ fmap[RMod_Forget R] g ∘ fv_insert.
Proof.
  intros W h.
  unshelve eexists.
  - exact (fv_extend h).
  - intro x; simpl; reflexivity.
  - intros g Hg t; simpl.
    symmetry; apply (fv_extend_unique W h g).
    intro x; symmetry; exact (Hg x).
Qed.

End FreeModule.

Arguments FVTerm {R X}.
Arguments fv_gen {R X} x.
Arguments fv_zero {R X}.
Arguments fv_plus {R X} s t.
Arguments fv_neg {R X} s.
Arguments fv_smul {R X} r s.
Arguments fv_eq {R X} s t.
Arguments fv_refl {R X} s.
Arguments fe_gen {R X x y} _.
Arguments fe_plus {R X s s' t t'} _ _.
Arguments fe_neg {R X s s'} _.
Arguments fe_smul {R X r r' s s'} _ _.
Arguments fe_assoc {R X} s t u.
Arguments fe_comm {R X} s t.
Arguments fe_zero_l {R X} s.
Arguments fe_neg_l {R X} s.
Arguments fe_smul_distr_l {R X} r s t.
Arguments fe_smul_distr_r {R X} r r' s.
Arguments fe_smul_assoc {R X} r r' s.
Arguments fe_smul_one {R X} s.
Arguments fe_sym {R X s t} _.
Arguments fe_trans {R X s t u} _ _.
Arguments FreeModObject {R} X.
Arguments fv_insert {R} X.
Arguments fv_eval {R X W} h t.
Arguments fv_extend {R X W} h.
Arguments fv_eval_respects {R X} W h s t _.
Arguments fv_extend_unique {R X} W h g _ t.
Arguments free_module_universal {R} X W h.

(* * ** The universal arrow, the free functor and the adjunction / * ** 普遍箭头、自由函子与伴随 *)

Section FreeModuleAdjunction.

Context (R : RingObject).

(*
 The free module packaged as a universal arrow.  By
 Theory/Universal/Arrow.v this IS an initial object of the comma
 category [=(X) ↓ RMod_Forget R]. 

 --------
 作为一个通用箭头打包的自由模。根据 Theory/Universal/Arrow.v，这确实是逗号范畴 [=(X) ↓ RMod_Forget R] 的初始对象。
*)
Definition free_module_universal_arrow (X : Sets)
  : UniversalArrow X (RMod_Forget R) :=
  universal_arrow_from_UMP X (RMod_Forget R) (FreeModObject X) (fv_insert X)
    (free_module_universal X).

(*
 The same content in the direct encoding, where the universal object is
 named rather than projected out of a comma category. 

 --------
 直接编码中的相同内容，其中通用对象被命名，而不是从逗号类型中投射出来。
*)
Program Definition free_module_AUniversalArrow (X : Sets)
  : AUniversalArrow X (RMod_Forget R) (FreeModObject X) := {|
  universal_arrow := fv_insert X
|}.
Next Obligation.
  intros X W h.
  unshelve eexists.
  - exact (fv_extend h).
  - intro x; simpl; reflexivity.
  - intros g Hg t; simpl.
    (* [AUniversalArrow]'s uniqueness field is oriented the other way round from the comma-packaged one, hence the [symmetry]. / [AUniversalArrow] 的唯一性字段的方向与逗号包装的那个相反，因此是 [symmetry]。 *)
    symmetry; apply (fv_extend_unique W h g).
    intro x; exact (Hg x).
Qed.

(*
 The functor and the adjunction come out of the generic machinery with
 no further proof — the route Instance/Grp/Free.v,
 Instance/Coq/Monoid/Free.v and Construction/Free/Quiver.v all take. 

 --------
 函子和伴随由通用机制得出，无需进一步证明 —— 路径 Instance/Grp/Free.v、Instance/Coq/Monoid/Free.v 和 Construction/Free/Quiver.v 都采用这种方式。
*)
Definition FreeMod : Sets ⟶ RMod R :=
  LeftAdjointFunctorFromUniversalArrows (RMod_Forget R)
    free_module_universal_arrow.

Definition free_module_adjunction : FreeMod ⊣ RMod_Forget R :=
  AdjunctionFromUniversalArrows (RMod_Forget R) free_module_universal_arrow.

(*
   * The free functor's object part is the formal-sum module,
   definitionally. 

   --------
   * 自由函子在对象部分定义上是形式和模。
*)
Example FreeMod_obj (X : Sets) : FreeMod X = FreeModObject X := eq_refl.

(*
   * The universal arrow is the basis insertion on the nose:
   [universal_arrow_from_UMP] stores the supplied morphism as the second
   projection of the comma object it builds, so no proof is involved. 

   --------
   * 通用箭头是鼻子的基础插入：
   [universal_arrow_from_UMP] 将提供的态射存储为它构建的逗号对象的第二投影，因此不涉及证明。
*)
Example free_module_arrow_is_insert (X : Sets) :
  @arrow _ _ X (RMod_Forget R) (free_module_universal_arrow X) = fv_insert X
  := eq_refl.

(*
   * ** The unit is the basis insertion

   [unit] is DERIVED in Theory/Adjunction.v (it is the transpose of the
   identity), not a field, so what it computes to has to be checked.  It
   is [fmap[U] id ∘ arrow], and [fmap[RMod_Forget R] id] is the identity
   setoid map, so the unit is [fv_insert] itself.
   CORRECTION (#1347): read as an equation of setoid morphisms, "the unit
   is [fv_insert] itself" held only pointwise, as the two examples below
   state it, until Instance/Sets.v gave its identity's and composite's
   properness fields as terms; it now holds whole at [eq_refl] (control
   C9 of Test/ProbeSetsTerms1347.v), and is refused at master 687ac356. 

   --------
   * ** 单元是基础插入

   [unit] 是在 Theory/Adjunction.v 中派生的（它是恒等的转置），不是一个域，因此它计算出的结果必须检查。它是 [fmap[U] id ∘ arrow]，而 [fmap[RMod_Forget R] id] 是恒等集合同态映射，所以单元是 [fv_insert] 本身。
   更正 (#1347)：作为集合同态的方程来读取时，“单元是 [fv_insert] 本身”仅在点上成立，如下面两个例子所示，直到 Instance/Sets.v 提供其恒等和复合的适当性字段作为项；现在在 [eq_refl]（Test/ProbeSetsTerms1347.v 的控制 C9）上整体成立，但在 master 687ac356 上被拒绝。
*)

Definition free_module_unit (X : Sets)
  : X ~{Sets}~> RMod_Forget R (FreeMod X) :=
  @Category.Theory.Adjunction.unit _ _ _ _ free_module_adjunction X.

Example free_module_unit_is_insert (X : Sets) (x : carrier X) :
  free_module_unit X x = fv_insert X x := eq_refl.

Example free_module_unit_is_generator (X : Sets) (x : carrier X) :
  free_module_unit X x = @fv_gen R X x := eq_refl.

(*
   * ** The counit evaluates a formal linear combination

   The counit is the OTHER transpose, and it does not compute: it is
   [unique_obj (ump_universal_arrows …)] and [ump_universal_arrows] is
   [Qed]-opaque, so no [eq_refl] is available on this side and none is
   claimed.  What is available — and is the content — is that it agrees
   with evaluation up to [≈].  CORRECTION (#472): one of two causes;
   this file's own [free_module_universal] is the other (the header's
   STRENGTHS), and the counit of the hom-set form
   [free_module_adjunction_hom] below is this fold at [eq_refl]
   ([free_module_hom_counit]). 

   --------
   * **余元评估形式线性组合

   余元是另一种转置，它不进行计算：它是 [unique_obj (ump_universal_arrows …)]，而 [ump_universal_arrows] 是 [Qed] -不透明，因此这一侧没有 [eq_refl] 可用，也没有被声称。可用的内容——也是内容本身——是它与评估在 [≈] 上一致。修正 (#472)：两个原因中的一个；该文件自身的 [free_module_universal] 是另一个（头文件的 STRENGTHS），而下方同态集形式的余元 [free_module_adjunction_hom] 是在 [eq_refl] 的这个折叠（[free_module_hom_counit]）。
*)

Definition free_module_counit (W : RMod R)
  : FreeMod (RMod_Forget R W) ~{RMod R}~> W :=
  @Category.Theory.Adjunction.counit _ _ _ _ free_module_adjunction W.

Lemma free_module_counit_generator (W : RMod R)
  (m : carrier (RMod_Forget R W)) :
  cmon_map (rm_hom (free_module_counit W)) (fv_gen m) ≈ m.
Proof.
  exact (@to_adj_counit _ _ _ _ free_module_adjunction W m).
Qed.

Theorem free_module_counit_evaluates (W : RMod R)
  (t : @FVTerm R (RMod_Forget R W)) :
  cmon_map (rm_hom (free_module_counit W)) t
    ≈ fv_eval (@id Sets (RMod_Forget R W)) t.
Proof.
  apply (fv_extend_unique W (@id Sets (RMod_Forget R W))
           (free_module_counit W)).
  intro m; exact (free_module_counit_generator W m).
Qed.

(*
   * ** The free functor relabels basis vectors

   Riehl's "functoriality on maps of generating sets".
   [LeftAdjointFunctorFromUniversalArrows] defines [fmap] by universal
   factorization, not by a formula, so what the functor does to a
   generator has to be proved. 

   --------
   * ** 自由函子重新标记基向量

   Riehl 的“生成集合映射上的函子性”。
   [LeftAdjointFunctorFromUniversalArrows] 通过普遍分解定义了 [fmap]，而不是通过公式，因此必须证明函子对生成元的作用。
*)
Lemma free_module_fmap_generators {X Y : Sets} (u : X ~{Sets}~> Y)
  (x : carrier X) :
  cmon_map (rm_hom (fmap[FreeMod] u)) (fv_gen x) ≈ fv_gen (u x).
Proof.
  symmetry.
  exact (unique_property
           (ump_universal_arrows (free_module_universal_arrow X)
              (@arrow _ _ Y (RMod_Forget R)
                 (free_module_universal_arrow Y) ∘ u)) x).
Qed.

(*
   * ** The adjunction bijection, and its two naturality clauses

   Mac Lane §IV.1 presents the free construction as the bijection

   RMod(FreeMod X, W)  ≅  Sets(X, U W)

   natural in X and in W, "each verified separately".  The forward
   transpose is restriction to the basis, and it IS the adjunction's own
   ⌊−⌋ — [free_module_transpose_is_adj] records that by [eq_refl] — so
   the two clauses below, proved in the free module's own vocabulary,
   are the class's fields and not weaker statements about some other
   map. 

   --------
   * ** 伴随双射及其两个自然性条款

   Mac Lane §IV.1 将自由构造表示为双射：

   RMod(FreeMod X, W)  ≅  Sets(X, U W)

   在 X 和 W 中都是自然的，“各自单独验证”。正向的转置是对基的限制，它确实是伴随的 ⌊−⌋ —— [free_module_transpose_is_adj] 通过 [eq_refl] 记录了这一点 —— 因此下面的两个条款，在自由模自身的词汇中证明，是类的字段，而不是关于某个其他映射的更弱陈述。
*)

Definition fv_transpose {X : Sets} {W : RMod R}
  (g : FreeMod X ~{RMod R}~> W) : X ~{Sets}~> RMod_Forget R W :=
  fmap[RMod_Forget R] g ∘ fv_insert X.

Example free_module_transpose_is_adj {X : Sets} {W : RMod R}
  (g : FreeMod X ~{RMod R}~> W) :
  to (@adj _ _ _ _ free_module_adjunction X W) g = fv_transpose g := eq_refl.

(*
   * Restriction to the basis is a bijection: the inverse is linear
   extension.  Both round trips are [≈] statements about morphisms, and
   the first of them is [reflexivity] at every generator. 

   --------
   * 限制到基是一个双射：逆是线性扩展。两个往返都是关于态射的 [≈]  命题，并且它们中的第一个在每个生成元上都是 [reflexivity] 。
*)

Lemma fv_transpose_extend {X : Sets} {W : RMod R}
  (h : X ~{Sets}~> RMod_Forget R W) : fv_transpose (fv_extend h) ≈ h.
Proof. intro x; simpl; reflexivity. Qed.

Lemma fv_extend_transpose {X : Sets} {W : RMod R}
  (g : FreeMod X ~{RMod R}~> W) : fv_extend (fv_transpose g) ≈ g.
Proof.
  intro t; simpl.
  symmetry; apply (fv_extend_unique W (fv_transpose g) g).
  intro x; simpl; reflexivity.
Qed.

(*
   * *** Naturality in the generating set

   For u : X ~> Y in [Sets], restricting to the basis after
   precomposing with the relabelling [fmap[FreeMod] u] is the same as
   restricting and then precomposing with u.  The proof evaluates both
   sides at a generator and uses [free_module_fmap_generators]; it does
   not cite the adjunction. 

   --------
   * *** 生成集合中的自然性

   对于  u : X ~> Y 在  [Sets] 中，在与重新标记  [fmap[FreeMod]  u] 预组合后限制到基上，与先限制再与 u 预组合是相同的。证明在生成元上评估双方并使用  [free_module_fmap_generators]；它没有引用伴随关系。
*)
Theorem free_module_naturality_in_set {X Y : Sets} {W : RMod R}
  (g : FreeMod Y ~{RMod R}~> W) (u : X ~{Sets}~> Y) :
  fv_transpose (g ∘ fmap[FreeMod] u) ≈ fv_transpose g ∘ u.
Proof.
  intro x; simpl.
  exact (proper_morphism (cmon_map (rm_hom g)) _ _
           (free_module_fmap_generators u x)).
Qed.

(*
   * *** Naturality in the target module

   For k : W ~> W' linear, restricting to the basis after postcomposing
   with k is the same as restricting and then postcomposing with the
   underlying function of k.  Both sides are the same composite of
   underlying functions, so this is [reflexivity] pointwise. 

   --------
   * *** 目标模中的自然性

   对于线性映射 k : W ~> W'，在与 k 后合成之后再限制到基上，与先限制然后再与 k 的底层函数后合成是相同的。两边都是底层函数的同样复合，因此这是逐点的 [reflexivity]。
*)
Theorem free_module_naturality_in_module {X : Sets} {W W' : RMod R}
  (k : W ~{RMod R}~> W') (g : FreeMod X ~{RMod R}~> W) :
  fv_transpose (k ∘ g) ≈ fmap[RMod_Forget R] k ∘ fv_transpose g.
Proof. intro x; simpl; reflexivity. Qed.

(*
   * The two theorems just proved ARE the adjunction's naturality fields
   at this adjunction: the statements are convertible, so these are the
   clauses Mac Lane asks for and not restatements about a different
   map. 

   --------
   * 刚刚证明的两个定理正是该陪范畴在此陪范畴下的自然性领域：这些陈述是可以互换的，因此它们是 Mac Lane 所要求的条款，而不是关于不同映射的重述。
*)
Example free_module_naturality_in_set_is_to_adj_nat_l
  {X Y : Sets} {W : RMod R} (g : FreeMod Y ~{RMod R}~> W)
  (u : X ~{Sets}~> Y) :
  (to (@adj _ _ _ _ free_module_adjunction X W) (g ∘ fmap[FreeMod] u)
     ≈ to (@adj _ _ _ _ free_module_adjunction Y W) g ∘ u)
  = (fv_transpose (g ∘ fmap[FreeMod] u) ≈ fv_transpose g ∘ u) := eq_refl.

Example free_module_naturality_in_module_is_to_adj_nat_r
  {X : Sets} {W W' : RMod R} (k : W ~{RMod R}~> W')
  (g : FreeMod X ~{RMod R}~> W) :
  (to (@adj _ _ _ _ free_module_adjunction X W') (k ∘ g)
     ≈ fmap[RMod_Forget R] k ∘ to (@adj _ _ _ _ free_module_adjunction X W) g)
  = (fv_transpose (k ∘ g) ≈ fmap[RMod_Forget R] k ∘ fv_transpose g) := eq_refl.

(*
   * ** The triangle identities

   Both are instances of Theory/Adjunction.v's derived corollaries; they
   are named here because they are what makes the unit/counit
   presentation of this adjunction usable. 

   --------
   * **三角恒等式

   两者都是 Theory/Adjunction.v 中派生推论的实例；它们在这里被命名，是因为它们使得该伴随关系的单位/余单位表示可用。
*)

Corollary free_module_triangle_left (X : Sets) :
  free_module_counit (FreeMod X) ∘ fmap[FreeMod] (free_module_unit X)
    ≈ @id (RMod R) (FreeMod X).
Proof. exact (@counit_fmap_unit _ _ _ _ free_module_adjunction X). Qed.

Corollary free_module_triangle_right (W : RMod R) :
  fmap[RMod_Forget R] (free_module_counit W)
    ∘ free_module_unit (RMod_Forget R W)
    ≈ @id Sets (RMod_Forget R W).
Proof. exact (@fmap_counit_unit _ _ _ _ free_module_adjunction W). Qed.

End FreeModuleAdjunction.

Arguments free_module_universal_arrow {R} X.
Arguments fv_transpose {R X W} g.
Arguments free_module_fmap_generators {R X Y} u x.

(*
   * ** The same adjunction in hom-set form (#472)

   A second packaging of [FreeMod R ⊣ RMod_Forget R], with the SAME left
   adjoint [FreeMod R] and the same insertion: Theory/Adjunction.v's
   hom-set constructor [Build_Adjunction'] applied to the natural
   bijection [free_module_hom_iso], whose forward transpose is
   [fv_transpose], the forward transpose of [free_module_adjunction]
   ([free_module_transpose_is_adj]), and whose inverse transpose is the
   linear extension [fv_extend].  Its two naturality fields are
   [free_module_naturality_in_set] and
   [free_module_naturality_in_module], cited.  Its counit is then the
   fold of the identity by conversion ([free_module_hom_counit]), where
   the counit of [free_module_adjunction] is that fold only up to `≈`
   ([free_module_counit_evaluates]).  Instance/Mod/FreeMonad.v builds
   the free R-module monad T_R of Mac Lane's §VI.4 Exercise 2 on it.  No
   second free module and no second free functor: the action on arrows
   is still [FreeMod]'s, at `≈` the relabelling
   ([free_module_fmap_generators]). 

   --------
   * ** 同样的伴随在同态集形式 (#472)[FreeMod R ⊣ RMod_Forget R] 的第二次打包，具有相同的左伴随 [FreeMod R] 和相同的插入：Theory/Adjunction.v 的 hom-set 构造器 [Build_Adjunction'] 应用于自然双射 [free_module_hom_iso]，其前向转置为 [fv_transpose]，[free_module_adjunction] ([free_module_transpose_is_adj]) 的前向转置，以及其逆转置为线性扩展 [fv_extend]。它的两个自然性字段是 [free_module_naturality_in_set] 和 [free_module_naturality_in_module]，如引用。然后它的余单位是通过转换折叠的恒等 [free_module_hom_counit]，其中 [free_module_adjunction] 的余单位仅在 `≈` ([free_module_counit_evaluates]) 下是该折叠。Instance/Mod/FreeMonad.v 构建了 Mac Lane §VI.4 练习 2 中的自由 R-模幺半群 T_R。没有第二个自由模，也没有第二个自由函子：箭头的作用仍然是 [FreeMod] 的，在 `≈` 为重标记 ([free_module_fmap_generators])。
*)

(*
 The fold respects pointwise-`≈` maps on generators: a citation of
 [fv_extend_unique]. 

 --------
 该折叠尊重生成元上的逐点 `≈` 映射：引用 [fv_extend_unique]。
*)
Lemma fv_eval_pointwise@{a c p so +} (R : RingObject@{a c p})
      {X : Sets@{c so}} {W : RMod R}
      (h h' : X ~{Sets@{c so}}~> RMod_Forget R W) (H : h ≈ h')
      (t : @FVTerm R X) :
  fv_eval h t ≈ fv_eval h' t.
Proof. exact (fv_extend_unique W h' (fv_extend h) (fun x => H x) t). Qed.

(* The natural bijection RMod(F X, W) ≅ Sets(X, U W): forward the restriction to the basis, backward the linear extension. / 自然双射 RMod(F X, W) ≅ Sets(X, U W)：向前是限制到基，向后是线性扩展。 *)
Definition free_module_hom_iso@{a c p so +} (R : RingObject@{a c p})
  (X : Sets@{c so}) (W : RMod R) :
  @Isomorphism Sets@{c so}
    {| carrier := @hom (RMod R) (FreeMod R X) W
     ; is_setoid := @homset (RMod R) (FreeMod R X) W |}
    {| carrier := @hom Sets@{c so} X (RMod_Forget R W)
     ; is_setoid := @homset Sets@{c so} X (RMod_Forget R W) |}.
Proof.
  unshelve refine
    (@Build_Isomorphism Sets
       {| carrier := @hom (RMod R) (FreeMod R X) W
        ; is_setoid := @homset (RMod R) (FreeMod R X) W |}
       {| carrier := @hom Sets X (RMod_Forget R W)
        ; is_setoid := @homset Sets X (RMod_Forget R W) |}
       (@Build_SetoidMorphism
          (@hom (RMod R) (FreeMod R X) W) (@homset (RMod R) (FreeMod R X) W)
          (@hom Sets X (RMod_Forget R W)) (@homset Sets X (RMod_Forget R W))
          (fun g => fv_transpose g) _)
       (@Build_SetoidMorphism
          (@hom Sets X (RMod_Forget R W)) (@homset Sets X (RMod_Forget R W))
          (@hom (RMod R) (FreeMod R X) W) (@homset (RMod R) (FreeMod R X) W)
          (fun h => fv_extend h) _) _ _).
  - intros g g' H x. exact (H (fv_gen x)).
  - intros h h' H t. exact (fv_eval_pointwise R h h' H t).
  - intros h x. reflexivity.
  - intros g t. exact (fv_extend_transpose R g t).
Defined.

(*
 The adjunction's last level, which no constraint mentions when it is
 left free, is pinned to the one of [Sets], as Instance/Smgrp.v and
 Instance/Mon/Free.v pin theirs. 

 --------
 当附加的最后一级自由时，没有约束提及时，它被固定到 [Sets] 的一个级别，就像 Instance/Smgrp.v 和 Instance/Mon/Free.v 固定它们的一样。
*)
Definition free_module_adjunction_hom@{a c p so +} (R : RingObject@{a c p}) :
  @Adjunction@{_ c c so c c c c so c so} (RMod R) Sets@{c so}
    (FreeMod R) (RMod_Forget R).
Proof.
  unshelve refine
    (@Build_Adjunction' (RMod R) Sets (FreeMod R) (RMod_Forget R)
       (free_module_hom_iso R) _ _).
  - intros X Y W g u. exact (free_module_naturality_in_set R g u).
  - intros X W W' k g. exact (free_module_naturality_in_module R k g).
Defined.

(* Its counit is the fold of the identity, by conversion. / 它的余单位是通过转换得到的恒等映射的折叠。 *)
Example free_module_hom_counit@{a c p so +} (R : RingObject@{a c p})
  (W : RMod R) (t : @FVTerm R (RMod_Forget R W)) :
  cmon_map (rm_hom (@counit _ _ _ _ (free_module_adjunction_hom R) W)) t
    = fv_eval (@id Sets@{c so} (RMod_Forget R W)) t := eq_refl.

(*
 Its unit and its forward transpose ARE those of
 [free_module_adjunction].  The cast pins the free level of that
 adjunction too, as the hom-set form's own is pinned above. 

 --------
 它的单位及其前向转置是 [free_module_adjunction] 的。该作法也固定了该附加的自由层次，因为同态集形式本身的层次已经被固定在上方。
*)
Example free_module_hom_unit@{a c p so +} (R : RingObject@{a c p})
  (X : Sets@{c so}) :
  @Category.Theory.Adjunction.unit _ _ _ _ (free_module_adjunction_hom R) X
    = @Category.Theory.Adjunction.unit _ _ _ _
        (free_module_adjunction R
           : @Adjunction@{_ c c so c c c c so c so} _ _ _ _) X
  := eq_refl.

Example free_module_hom_to@{a c p so +} (R : RingObject@{a c p})
  (X : Sets@{c so}) (W : RMod R) (g : FreeMod R X ~{RMod R}~> W) :
  to (@adj _ _ _ _ (free_module_adjunction_hom R) X W) g
    = to (@adj _ _ _ _ (free_module_adjunction R
                          : @Adjunction@{_ c c so c c c c so c so} _ _ _ _)
            X W) g := eq_refl.

(*
   * ** Every element is a finite linear combination of basis vectors

   The classical description of the free module — "finitely supported
   K-valued functions on X" — has two halves.  The half that does not
   need a decider on X is proved here: every formal expression is
   [fv_eq] to a sum r₁·e_{x₁} + … + rₙ·e_{xₙ} indexed by a list of
   scalar/generator pairs.  The other half, that the list is unique up
   to rearrangement and combination of like terms, is exactly what a
   decider buys and is NOT proved.  CORRECTION (#472): it is proved
   under the decider in Instance/Mod/FreeMonad/FinSupp.v, as
   [fv_lc_unique] (its converse is [fv_coef_injective]).

   The three list operations are defined here rather than imported so
   that this file takes no dependency on [Coq.Lists.List]; [list],
   [nil] and [cons] are [Coq.Init.Datatypes]'. 

   --------
   * ** 每个元素都是基向量的有限线性组合

   自由模的经典描述——“X 上的有限支持 K 值函数”——有两个部分。这里证明了不需要 X 上判定器的一半：每个形式表达式都是按标量/生成元对的列表索引到和 r₁·e_{x₁} + … + rₙ·e_{xₙ} 的形式。另一半，即该列表在重新排列和同类项组合下是唯一的，正是一个判定器可以提供的，并未在此证明。更正 (#472)：在 Instance/Mod/FreeMonad/FinSupp.v 的判定器下已经证明，如  [fv_lc_unique] （其逆命题为  [fv_coef_injective] ）。

   这里定义了三个列表操作，而不是导入，以便此文件不依赖于  [Coq.Lists.List] ；  [list] 、 [nil] 和  [cons]  是  [Coq.Init.Datatypes] '。
*)

Section NormalForm.

Context (R : RingObject).
Context (X : SetoidObject).

Definition fv_pair : Type :=
  (carrier (rig_setoid (ring_rig R)) * carrier X)%type.

Fixpoint fv_lc (l : list fv_pair) : @FVTerm R X :=
  match l with
  | nil       => fv_zero
  | cons p l' => fv_plus (fv_smul (fst p) (fv_gen (snd p))) (fv_lc l')
  end.

Fixpoint fv_app (l l' : list fv_pair) : list fv_pair :=
  match l with
  | nil       => l'
  | cons p l0 => cons p (fv_app l0 l')
  end.

Fixpoint fv_negate (l : list fv_pair) : list fv_pair :=
  match l with
  | nil       => nil
  | cons p l0 => cons (ring_neg R (fst p), snd p) (fv_negate l0)
  end.

Fixpoint fv_scale (r : carrier (rig_setoid (ring_rig R)))
         (l : list fv_pair) : list fv_pair :=
  match l with
  | nil       => nil
  | cons p l0 => cons (rig_mul (ring_rig R) r (fst p), snd p) (fv_scale r l0)
  end.

Lemma fv_lc_app (l l' : list fv_pair) :
  fv_eq (fv_lc (fv_app l l')) (fv_plus (fv_lc l) (fv_lc l')).
Proof.
  induction l as [|p l IHl]; simpl.
  - exact (fe_sym (fe_zero_l _)).
  - exact (fe_trans (fe_plus (fv_refl _) IHl) (fe_sym (fe_assoc _ _ _))).
Qed.

(* Negating a combination negates each coefficient. / 对一个组合取反会使每个系数都取反。 *)
Lemma fv_lc_negate (l : list fv_pair) :
  fv_eq (fv_lc (fv_negate l)) (fv_neg (fv_lc l)).
Proof.
  induction l as [|p l IHl]; simpl.
  - exact (fe_sym (ab_neg_zero (FreeModObject X))).
  - refine (fe_trans (fe_plus (rm_smul_neg_l (FreeModObject X) _ _) IHl) _).
    exact (fe_sym (ab_neg_plus (FreeModObject X) _ _)).
Qed.

(* Scaling a combination scales each coefficient. / 对一个组合进行缩放会缩放每个系数。 *)
Lemma fv_lc_scale (r : carrier (rig_setoid (ring_rig R))) (l : list fv_pair) :
  fv_eq (fv_lc (fv_scale r l)) (fv_smul r (fv_lc l)).
Proof.
  induction l as [|p l IHl]; simpl.
  - exact (fe_sym (rm_smul_zero_r (FreeModObject X) r)).
  - exact (fe_trans (fe_plus (fe_smul_assoc _ _ _) IHl)
             (fe_sym (fe_smul_distr_l _ _ _))).
Qed.

Theorem fv_normal_form (t : @FVTerm R X) :
  ∃ l : list fv_pair, fv_eq t (fv_lc l).
Proof.
  induction t as [ x | | t1 IHt1 t2 IHt2 | t IHt | r t IHt ].
  - exists (cons (rig_one (ring_rig R), x) nil); simpl.
    refine (fe_trans (fe_sym (fe_zero_l _)) _).
    refine (fe_trans (fe_comm _ _) _).
    exact (fe_plus (fe_sym (fe_smul_one _)) (fv_refl _)).
  - exists nil; exact (fv_refl _).
  - destruct IHt1 as [l1 H1], IHt2 as [l2 H2].
    exists (fv_app l1 l2).
    exact (fe_trans (fe_plus H1 H2) (fe_sym (fv_lc_app l1 l2))).
  - destruct IHt as [l Hl].
    exists (fv_negate l).
    exact (fe_trans (fe_neg Hl) (fe_sym (fv_lc_negate l))).
  - destruct IHt as [l Hl].
    exists (fv_scale r l).
    exact (fe_trans (fe_smul (reflexivity r) Hl) (fe_sym (fv_lc_scale r l))).
Qed.

End NormalForm.

Arguments fv_lc {R X} l.
Arguments fv_normal_form {R X} t.

(*
   * ** Non-degeneracy

   A free module on the empty or a one-element generating set would
   demonstrate nothing about the quotient: what has to be ruled out is
   that the generated congruence collapses the construction.  Three
   separations are proved, and they cost different things.  The only
   tool used is that any function on generators extends, so evaluating
   the extension separates formal expressions. 

   --------
   * ** 非退化性

   一个在空生成集或单元素生成集上的自由模不能展示关于商结构的任何信息：必须排除的情况是生成的同余会使构造退化。证明了三种分离情况，并且它们的代价各不相同。唯一使用的工具是任何生成元上的函数都可以扩展，因此对扩展进行求值可以分离形式表达式。
*)

Section NonDegeneracy.

Context (R : RingObject).
Context (X : SetoidObject).

(*
   * *** Distinct scalars give distinct multiples of a basis vector

   This needs NO hypothesis on X and none on R beyond what
   [RingObject] already carries.  Map every generator to 1 in R viewed
   as a module over itself (Instance/Mod.v's [Ring_RMod]); then r·e_x
   evaluates to r·1 ≈ r. 

   --------
   * *** 不同的标量给出基向量的不同倍数

   这对 X 不需要任何假设，对 R 也不需要超出
   [RingObject] 已经包含的假设。将每个生成元映射为在 R 中的 1，
   并将 R 视为它自身的模（Instance/Mod.v 中的 [Ring_RMod]）；那么 r·e_x
   的值就是 r·1 ≈ r。
*)

Definition fv_probe_one : X ~{Sets}~> RMod_Forget R (Ring_RMod R).
Proof.
  unshelve refine {| morphism := fun _ => rig_one (ring_rig R) |}.
  intros a b _; exact (reflexivity (rig_one (ring_rig R))).
Defined.

Theorem free_module_scalars_faithful
  (r s : carrier (rig_setoid (ring_rig R))) (x : carrier X) :
  fv_eq (@fv_smul R X r (fv_gen x)) (fv_smul s (fv_gen x)) → r ≈ s.
Proof.
  intro He.
  pose proof (fv_eval_respects (Ring_RMod R) fv_probe_one _ _ He) as Hv.
  simpl in Hv.
  rewrite (rig_mul_one_r (ring_rig R) r) in Hv.
  rewrite (rig_mul_one_r (ring_rig R) s) in Hv.
  exact Hv.
Qed.

(*
   * *** Distinct generators give distinct basis vectors

   This one is NOT hypothesis-free.  Why the hypotheses are not an
   artifact of the proof is ARGUED here, not proved — neither converse
   is machine-checked below, and the tree's precedent for exactly this
   shape of claim ([arrow_mul_respects_forces_UIP],
   [skeleton0_skeletal_forces_UIP], [faithful_QuiverElements_implies_UIP])
   is deliberately not followed.  The argument: separating two
   generators means exhibiting a module in which they go to different
   places; the only maps into a module that a bare setoid supplies are
   the ones that can be WRITTEN, and the characteristic function of a
   point cannot be written without a decision procedure for that
   setoid's [≈].  For the other hypothesis the argument is shorter and
   firmer — a ring in which 1 ≈ 0 is the zero ring, over which every
   module is trivial, so [fv_gen x] and [fv_gen y] are [fv_eq] for ALL
   x and y and the conclusion does not hold at all — but it too is left
   as an argument rather than a refutation. 

   --------
   * *** 不同的生成元给出不同的基向量这个并非没有假设。在这里讨论了为什么假设不是证明的产物，而不是证明——下面没有对任一逆命题进行机器检查，并且该树对恰好这种形式的主张（[arrow_mul_respects_forces_UIP]、[skeleton0_skeletal_forces_UIP]、[faithful_QuiverElements_implies_UIP]）的先例特意没有遵循。论点是：分离两个生成元意味着展示一个在其中它们会到不同位置的模；一个简单集合代数提供的进入模的唯一路径是那些可以被写出的，而一个点的特征函数如果没有该集合代数的[≈]的判定程序是无法写出的。对于另一个假设，论证更短且更有力——一个环中如果 1 ≈ 0，则它是零环，在这个环上每个模都是平凡的，因此  [fv_gen x] 和  [fv_gen y] 对于所有 x 和 y 都是 [fv_eq]，结论根本不成立——但它也只是作为一个论证，而不是反驳。
*)

Context (Xdec : ∀ x y : carrier X, (x ≈ y) + ((x ≈ y) → False)).
Context (Rnz : rig_one (ring_rig R) ≈ rig_zero (ring_rig R) → False).

(* The characteristic function of the generator [x], with values in R viewed as a module over itself. / 生成元 [x] 的特征函数，其值在 R 中，被视为自身的模。 *)
Definition fv_probe_at (x : carrier X)
  : X ~{Sets}~> RMod_Forget R (Ring_RMod R).
Proof using R X Xdec.
  unshelve refine {|
    morphism := fun z => match Xdec x z with
                         | inl _ => rig_one (ring_rig R)
                         | inr _ => rig_zero (ring_rig R)
                         end
  |}.
  intros z z' Hz; simpl.
  destruct (Xdec x z) as [Hxz|Hxz], (Xdec x z') as [Hxz'|Hxz'].
  - reflexivity.
  - destruct (Hxz' (transitivity Hxz Hz)).
  - destruct (Hxz (transitivity Hxz' (symmetry Hz))).
  - reflexivity.
Defined.

Theorem free_module_basis_injective (x y : carrier X) :
  fv_eq (@fv_gen R X x) (fv_gen y) → x ≈ y.
Proof using R X Xdec Rnz.
  intro He.
  destruct (Xdec x y) as [Hxy|Hxy]; [ exact Hxy | ].
  destruct Rnz.
  pose proof (fv_eval_respects (Ring_RMod R) (fv_probe_at x) _ _ He) as Hv.
  simpl in Hv.
  destruct (Xdec x x) as [_|Hxx]; [ | destruct (Hxx (reflexivity x)) ].
  destruct (Xdec x y) as [Hc|_]; [ destruct (Hxy Hc) | ].
  exact Hv.
Qed.

(*
   * *** The basis is linearly independent

   The statement a reader of §III.1 actually wants, at two generators:
   if r·e_x + s·e_y vanishes and x ≉ y then both coefficients vanish.
   Only the decider is spent — NOT [Rnz], which is why this is the
   stronger of the two separations: over the zero ring it degenerates to
   a truth rather than to a falsehood.  The proof evaluates through the
   characteristic function of one generator, which sends the other's
   basis vector to 0. 

   --------
   * *** 基是线性无关的

   §III.1 的读者实际上希望的陈述，在两个生成元上：
   如果 r·e_x + s·e_y 消失且 x ≉ y，那么两个系数都消失。
   只有判定器被消耗 —— 而不是 [Rnz]，这就是为什么这是两个分离中更强的一个：在零环上它退化为真而不是假。证明通过一个生成元的特征函数进行评估，该函数将另一个的基向量映射为 0。
*)
Theorem free_module_two_independent (x y : carrier X)
  (Hxy : (x ≈ y) → False) (r s : carrier (rig_setoid (ring_rig R))) :
  fv_eq (fv_plus (@fv_smul R X r (fv_gen x)) (fv_smul s (fv_gen y))) fv_zero →
  (r ≈ rig_zero (ring_rig R)) * (s ≈ rig_zero (ring_rig R)).
(* [Rnz] is deliberately absent: this separation does not need it, and naming the section variables keeps that visible in the signature. / [Rnz] 是故意缺席的：这种分离不需要它，而且命名部分变量可以在签名中保持可见。 *)
Proof using R X Xdec.
  intro He.
  split.
  - pose proof (fv_eval_respects (Ring_RMod R) (fv_probe_at x) _ _ He) as Hv.
    simpl in Hv.
    destruct (Xdec x x) as [_|Hxx]; [ | destruct (Hxx (reflexivity x)) ].
    destruct (Xdec x y) as [Hc|_]; [ destruct (Hxy Hc) | ].
    (* r·1 + s·0 ≈ 0 *)
    rewrite (rig_mul_one_r (ring_rig R) r) in Hv.
    rewrite (rig_mul_zero_r (ring_rig R) s) in Hv.
    rewrite (rig_add_zero_r (ring_rig R) r) in Hv.
    exact Hv.
  - pose proof (fv_eval_respects (Ring_RMod R) (fv_probe_at y) _ _ He) as Hv.
    simpl in Hv.
    destruct (Xdec y x) as [Hc|_];
      [ destruct (Hxy (symmetry Hc)) | ].
    destruct (Xdec y y) as [_|Hyy]; [ | destruct (Hyy (reflexivity y)) ].
    (* r·0 + s·1 ≈ 0 *)
    rewrite (rig_mul_zero_r (ring_rig R) r) in Hv.
    rewrite (rig_mul_one_r (ring_rig R) s) in Hv.
    rewrite (rig_add_zero_l (ring_rig R) s) in Hv.
    exact Hv.
Qed.

End NonDegeneracy.

Arguments fv_probe_one {R} X.
Arguments free_module_scalars_faithful {R X} r s x _.
Arguments free_module_basis_injective {R X} Xdec Rnz x y _.
Arguments free_module_two_independent {R X} Xdec x y Hxy r s _.

(*
   * ** A computing witness over the integers

   ℤ is the cheapest ring in tree whose action computes
   (Theory/Algebra/Rig.v's [Int_Ring], Instance/Mod.v's [Int_RMod]).
   The generating setoid has TWO elements, so the free module is not the
   ring itself and the linear extension has something to do. 

   --------
   * ** 整数上的计算见证

   ℤ 是树中最便宜的环，其作用计算了
   (Theory/Algebra/Rig.v 的 [Int_Ring], Instance/Mod.v 的 [Int_RMod])。
   生成的集合体有两个元素，因此自由模不是环本身，线性扩展有一定的关联。
*)

Definition TwoGens : SetoidObject := {|
  carrier   := bool;
  is_setoid := {| equiv := eq; setoid_equiv := eq_equivalence |}
|}.

Definition two_gens_dec :
  ∀ x y : carrier TwoGens, (x ≈ y) + ((x ≈ y) → False).
Proof.
  intros x y; simpl.
  destruct x, y.
  - exact (inl eq_refl).
  - right; intro H; discriminate.
  - right; intro H; discriminate.
  - exact (inl eq_refl).
Defined.

(*
 The two generators are distinct.  Like [two_gens_dec] this is a fact
 about the generating setoid alone — nothing about any ring enters —
 so it is stated here rather than beside either scalar witness, and
 Instance/Vect/Free.v consumes this one rather than restating it. 

 --------
 这两个生成器是不同的。像 [two_gens_dec] 一样，这是仅关于生成集合的一个事实——与任何环无关——所以它在这里说明，而不是在任意标量证据旁边说明，并且 Instance/Vect/Free.v 使用这个事实，而不是重复说明它。
*)
Lemma two_gens_distinct : @equiv _ (is_setoid TwoGens) true false → False.
Proof. intro H; discriminate H. Qed.

(*
 [FVTerm]'s two index arguments are implicit, and in a statement with
 no expected type — an [fv_eq] between two constructor applications —
 the elaborator has nothing to propagate them from.  These are
 NOTATIONS, not definitions, so each unfolds to the constructor itself
 and nothing below is stated about a different term. 

 --------
 [FVTerm] 的两个索引参数是隐含的，并且在没有期望类型的语句中——即两个构造函数应用之间的 [fv_eq] ——展开器没有来源来传播它们。这些是符号表示，而不是定义，因此每个都展开为构造函数本身，并且没有说明其他术语。
*)
Local Notation zgen  := (@fv_gen Int_Ring TwoGens).
Local Notation zsmul := (@fv_smul Int_Ring TwoGens).
Local Notation zplus := (@fv_plus Int_Ring TwoGens).

(* Two integers, read off the two generators. / 两个整数，从两个生成器中读出。 *)
Definition int_probe : TwoGens ~{Sets}~> RMod_Forget Int_Ring Int_RMod.
Proof.
  unshelve refine {| morphism := fun b : carrier TwoGens => if b then 3%Z else 5%Z |}.
  (*
 [all:] because the respectfulness field of a map out of a setoid
 whose ≈ is Leibniz [=] may be discharged by instance resolution
 before a goal is ever opened; the carriers here are at [Set]
 either way, so nothing is pinned that was not already. 

 --------
 [all:] 因为从一个集合子类的映射的尊重性域，其 ≈ 是莱布尼茨 [=]，可以在目标被打开之前通过实例解析来处理；这里的承载体在 [Set] 无论哪种方式，因此没有固定任何原本未固定的东西。
*)
  all: intros x y H; simpl in H; subst y; reflexivity.
Defined.

(* The linear extension computes: 2·e_true + e_false ↦ 2·3 + 5 = 11. / 线性扩展计算：2·e_true + e_false ↦ 2·3 + 5 = 11。 *)
Example int_free_extend_computes :
  fv_eval int_probe
    (zplus (zsmul 2%Z (zgen true)) (zgen false)) = 11%Z := eq_refl.

Example int_free_extend_generator_true :
  fv_eval int_probe (zgen true) = 3%Z := eq_refl.

(*
 ℤ is not the zero ring, so the basis insertion is injective on this
 generating setoid. 

 --------
 ℤ 不是零环，因此基插入在这个生成集合上是单射的。
*)
Lemma int_one_neq_zero :
  rig_one (ring_rig Int_Ring) ≈ rig_zero (ring_rig Int_Ring) → False.
Proof. intro H; compute in H; discriminate H. Qed.

Theorem int_free_basis_distinct :
  fv_eq (zgen true) (zgen false) → False.
Proof.
  intro He.
  pose proof (free_module_basis_injective two_gens_dec int_one_neq_zero
                true false He) as Hb.
  compute in Hb; discriminate Hb.
Qed.

(*
 The basis is linearly independent over ℤ too.  This one spends the
 decider but NOT [int_one_neq_zero] — the ℚ reading of the same
 theorem is [free_vect_basis_independent]. 

 --------
 该基也是在 ℤ 上线性无关的。这个用于决策者，但不是 [int_one_neq_zero] ——同一条定理在 ℚ 上的表述是 [free_vect_basis_independent]。
*)
Theorem int_free_two_independent
  (r s : carrier (rig_setoid (ring_rig Int_Ring))) :
  fv_eq (zplus (zsmul r (zgen true)) (zsmul s (zgen false)))
        (@fv_zero Int_Ring TwoGens) →
  ((@equiv _ (rig_setoid (ring_rig Int_Ring)) r (rig_zero (ring_rig Int_Ring))) *
   (@equiv _ (rig_setoid (ring_rig Int_Ring)) s (rig_zero (ring_rig Int_Ring))))%type.
Proof.
  exact (@free_module_two_independent Int_Ring TwoGens two_gens_dec
           true false two_gens_distinct r s).
Qed.

(* ...and the scalars embed, with no decidability spent. / ...并且标量被嵌入，没有花费任何可判定性。 *)
Theorem int_free_scalars_distinct :
  fv_eq (zsmul 2%Z (zgen true)) (zsmul 3%Z (zgen true)) → False.
Proof.
  intro He.
  pose proof (@free_module_scalars_faithful Int_Ring TwoGens 2%Z 3%Z true He)
    as Hz.
  compute in Hz; discriminate Hz.
Qed.
