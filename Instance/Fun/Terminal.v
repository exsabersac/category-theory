Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Product.Finite.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Two.

Generalizable All Variables.

(* * * Pointwise terminal object and indexed products in a functor category / * * 函子范畴中的逐点终对象和指数量 *)

(*
 nLab:      https://ncatlab.org/nlab/show/functor+category
 nLab:      https://ncatlab.org/nlab/show/terminal+object
 nLab:      https://ncatlab.org/nlab/show/product
 Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)
 Book:      Mac Lane, CWM 2nd ed., §III.5 Exercise 5, p. 74
 ([maclane:III.5:ex5]): if D has (finite) products, so does
 the functor category [C, D], computed pointwise.

 WHAT IS DELIVERED, AND AT WHAT STRENGTH

 [Functor_Category_Terminal T : @Terminal ([C, D])] for any
 [T : @Terminal D] -- the constant functor at 1, with the unique
 natural transformation into it.  This is the nullary half of the
 exercise.

 [Fun_HasIndexedProducts HP : @HasIndexedProducts ([C, D])] for any
 [HP : @HasIndexedProducts D] -- pointwise indexed products at an
 ARBITRARY index [Type], not merely a finite one.  This is the
 substantial half.

 Everything is stated FIRST at the elementary, apex-pinned level and only
 then packaged.  [Fun_iprod]/[Fun_iprod_proj]/[Fun_IsIndexedProduct] are
 the elementary datum -- an object of [C, D], a family of natural
 transformations out of it, and [Structure/Limit/Product.v]'s
 [IsIndexedProduct] record for that family -- and
 [Fun_HasIndexedProducts] is [Build_HasIndexedProducts] applied to
 exactly those three.  No [Limit], no [Cone] and no [DiscreteCat] occurs
 anywhere in this file; see NOT DELIVERED for the measured reason.

 HOW THE TWO HALVES FIT TOGETHER.  They are one phenomenon:
 [Fun_empty_iprod_terminal] exhibits the terminal functor as the
 pointwise indexed product over an empty index, canonically.  It is an
 ISOMORPHISM in [C, D] and nothing stronger, because the empty
 [indexed_product] of D is whatever [HasIndexedProducts D] chose and
 nothing forces that choice to be [terminal_obj].  The enabling piece is
 [terminal_empty_IsIndexedProduct], stated over an arbitrary [A] with an
 [A -> False] rather than over a named empty type, so that no index
 universe is pinned.

 WHERE EACH HYPOTHESIS IS SPENT

 [Terminal D] supplies the object ([Constant_Terminal_Functor]) and,
 through [one_unique], the obligations of the [Terminal] record.  An
 earlier revision of this sentence said “exactly twice ... Nothing
 else uses it”, which is FALSE: it is consumed again by
 [terminal_empty_IsIndexedProduct], [Fun_empty_iprod_terminal],
 [Two_Sets_Terminal] and [two_pick].

 [HasIndexedProducts D] supplies the object, the projections and the
 universal property -- all three fields of Structure/Limit/Product.v's
 class -- and its UMP is also applied directly in places.  What ONE
 derived lemma carries is the ROUTING: every functor law of
 [Fun_iprod] and every naturality square below is “compose with the
 projections and compute” through [iprod_jointly_monic], two
 morphisms into an indexed product that agree after every projection
 being equal.  Note that lemma takes [IsIndexedProduct], not the
 class.  (An earlier revision said the class was spent in that one
 lemma alone; that was false.)

 [iprod_jointly_monic] is NOT new, and an earlier revision of this
 header claimed it was on the strength of a search for the NAME
 [jointly_monic] -- the exact trap this tree's own conventions warn
 against.  Structure/Bicartesian/Matrix.v already has
 [iprod_ext], the same statement for indexed products with
 essentially the same proof, plus the dual [icoprod_ext].  What is
 true, and is the honest reason for restating it, is that
 [iprod_ext]'s type carries a spurious [IsIndexedCoproduct] argument
 inherited from its section, so it cannot be applied here without
 supplying a coproduct that has nothing to do with the statement.
 The natural home for a hypothesis-free version is
 Structure/Limit/Product.v; it is declared here because this issue's
 deliverable is this file.

 PRIOR ART -- CITED, NOT DUPLICATED

 The BINARY case is [Functor_Category_Cartesian]
 (Instance/Fun/Cartesian.v).  It is not re-proved and not
 subsumed; it is COMPARED, see below.

 The general pointwise-limits fact was stated in PROSE in at least
 three places (since repointed at Instance/Fun/Limit.v, which proves it):
 Structure/Cartesian/Product.v (“the general fact that limits
 in a functor category [J, D] are computed pointwise whenever D has
 them”), Instance/Fun.v, and
 Instance/Fun/Cartesian.v, which quotes the nLab for it.  What
 was absent at that time was any Coq statement beyond the binary product:
 re-verified on this commit, no [Terminal] instance existed for ANY
 functor category (sweep of every declaration whose name or type
 mentions [Terminal]), and no pointwise indexed products existed
 anywhere -- [HasIndexedProducts] had exactly one instance,
 [Sets_HasIndexedProducts] (Instance/Sets/Products.v), plus the
 [C^op] repackaging in Structure/Limit/Coproduct.v.

 [Functor/Diagonal.v]'s [Diagonal] already carries a constant functor
 as its object action, and [Constant_Functor] is NOT defined as
 [fobj[Diagonal C] d].  Both actions agree ON THE NOSE
 ([constant_functor_diagonal_obj], [constant_functor_diagonal_fmap],
 both [eq_refl]); the two RECORDS do not
 ([constant_functor_is_diagonal], a pinned conversion negative --
 [Diagonal] is a [Program Instance], so its three law fields are
 opaque obligation constants).  The reason for not routing through it
 is a UNIVERSE measurement, not taste; see below.

 THE BINARY COMPARISON, MEASURED RATHER THAN ASSUMED

 [Fun_bool_iprod_iso] relates the pointwise indexed product at a
 two-element index to [Functor_Category_Cartesian]'s pointwise binary
 product.  The strength is an ISOMORPHISM in [C, D] and NOT [eq_refl]:
 [bool_iprod_is_binary_product] is a pinned conversion negative, with
 [ctl_bool_iprod_obj] the passing control at the same arguments.  The
 obstruction is not presentational -- [HasIndexedProducts D] and
 [Cartesian D] choose their objects independently, and nothing relates
 the two choices -- so an isomorphism is the strongest available
 statement.  It carries its leg equations
 ([Fun_bool_iprod_iso_commutes] and [Fun_bool_iprod_iso_inv_commutes],
 both leg families rather than one); a bare [≅] would be the weak form.

 The comparison is affordable because the enabling piece is generic:
 [cartesian_bool_IsIndexedProduct] proves that in ANY cartesian
 category the binary product is an indexed product over [bool], with
 [exl]/[exr] as the two projections.  Instantiated at
 [Functor_Category_Cartesian] it gives a second [IsIndexedProduct] of
 the same family, and [iprod_unique_iso]
 (Structure/Limit/Product/Finite.v) does the rest.  Its own
 constraint block is character-for-character [IsIndexedProduct]'s, so
 it adds no universe content.

 STRICTNESS, MEASURED STRICT-FIRST

 Holding at [eq_refl]: the terminal functor's object action, its arrow
 action, and the component of its unique arrow ([fun_terminal_obj],
 [fun_terminal_fmap], [fun_terminal_one_component]); the pointwise
 product's object action and the components of its projections
 ([fun_iprod_obj_computes], [fun_iprod_proj_component]); the mediator
 extracted from the packaged class IS [fun_iprod_tuple]
 ([fun_iprod_class_mediator]); and both actions of [Constant_Functor]
 against [Diagonal].

 REFUTED, each pinned as a [Fail] with a passing control alongside:
 the pointwise indexed product at a [bool] index is not the pointwise
 binary product, and [Constant_Functor d] is not the [Diagonal]
 record.  Both are genuine CONVERSION failures (“cannot unify”), read
 off the stripped commands rather than inferred.

 UNIVERSES -- BLOCKS READ IN FULL, DONORS TESTED SEPARATELY

 Four donors were each rejected at a section declaring
 [Constraint uh < up] against passing controls at the same levels, so
 the following are guarded rather than merely read off a printed
 binder.  [Terminal@{u u0}], [HasIndexedProducts], [IsIndexedProduct]
 and [Cartesian] each take their category as [Category@{o h h}]:
 every one of them identifies hom with proof.  [Fun] does more --
 [Fun@{...} : Category@{u u0 u0} -> Category@{u1 u2 u2} ->
 Category@{u3 u4 u4}] with [u0 = u2] -- so it identifies hom with
 proof in BOTH arguments AND the two hom levels with each other.

 [Constant_Functor@{co ch cp dro dh dp}] identifies NOTHING: its block
 is the five bounds [ch <= cp], [ch <= dh], [ch <= dp], [cp <= dp],
 [dh <= dp], which is [Functor]'s own block character for character.
 [Constant_Terminal_Functor@{co ch cp dro dh}] takes D at
 [Category@{dro dh dh}] -- [Terminal]'s doing -- while C's hom and
 proof stay APART ([ch <= cp]).  Both are hand-written record literals
 with explicit universe binders precisely to keep that: written as
 [Program Definition]s in an unannotated [Section] they minimize to
 [C : Category@{u u0 u0}], and the annotated form is then rejected
 because [Program] introduces an obligation universe that no [@{...}]
 list can bind.

 ROUTING THROUGH [Diagonal] WOULD COST THAT, AND THAT IS MEASURED:
 [fobj[@Diagonal D C] d] is REJECTED at [C : Category@{co ch cp}] with
 [ch < cp] (“Cannot enforce cp = dh”), against two passing controls,
 because [Diagonal]'s type mentions [C, D] and so inherits [Fun]'s
 identification even when only a bare constant functor is wanted.

 [Functor_Category_Terminal@{u u0 u1 u2 u3 u4}] is over
 [C : Category@{u2 u4 u4}] and [D : Category@{u3 u4 u4}] -- both
 identified, and both hom levels the SAME level [u4].  That is [Fun]'s
 doing and it lives in the BINDER: the constraint block is six bounds
 ([u4 < u], [u2 <= u0], [u2 <= u1], [u3 <= u0], [u4 <= u0],
 [u4 <= u1]) with NO equation in it, so reading the block alone would
 miss the identification entirely.

 [Fun_iprod@{u u0 u1 u2 u3 u4 u5 u6}] is over [C : Category@{u u0 u0}]
 and [D : Category@{u1 u2 u2}] -- the two hom levels stay DISTINCT
 ([u0 <= u2], a bound, not an equation), and the INDEX universe [u5]
 is only bounded ([u5 <= u3], [u5 <= u4]), never identified.  D's
 hom = proof is [HasIndexedProducts]'s doing.  C's is NOT
 donor-forced: [Functor] keeps them apart, as [Constant_Functor]
 above demonstrates, so it is the unannotated [Context {C : Category}]
 of the section, the minimization family recorded for
 [Build_Quiver_Standard_Eq].  It is repairable in principle and is NOT
 claimed unavoidable; a full lift was not attempted, and it costs a
 consumer nothing at the packaged level, where [Fun] identifies the
 two anyway.  The file's only EQUATION is [Fun]'s [u0 = u2], and it is
 carried by EIGHT constants, not one: [Fun_IsIndexedProduct]
 together with [fun_terminal_obj], [fun_terminal_fmap],
 [fun_terminal_one_component], [fun_iprod_tuple],
 [constant_functor_diagonal_obj], [constant_functor_diagonal_fmap]
 and [ctl_bool_iprod_obj] -- every constant whose statement is at
 [C, D].  It is the SAME equation each time, so the conclusion is
 unchanged, but an earlier revision of this sentence named one
 constant and read as a count, in a file that elsewhere insists a
 universe block be read IN FULL.
 [iprod_jointly_monic@{u u0 u1 u2}] leaves its index universe bounded
 ([u <= u1]) and never identified.

 THE WITNESSES CARRY A [Set], AND IT IS THE SHAPE'S:
 [Two_Sets_HasIndexedProducts] elaborates at
 [Fun@{u0 Set u1 Set u u0 u1}] -- [Instance/Two.v] declares
 [TwoHom : ... -> Set], and [Fun] identifies the shape's hom level
 with the target's, so [Sets] is cut to [Sets@{Set u1}], carriers in
 [Set].  That is the price of using [_2] as the shape, not a property
 of the general theorems, which carry no [Set] at all.

 NON-VACUITY

 Terminal half: [two_pick true] and [two_pick false] are two provably
 DISTINCT natural transformations INTO a functor of [_2, Sets]
 ([two_pick_distinct]), while [two_sets_one_unique] has arrows OUT of
 any functor into the terminal one unique.  So the category is not
 collapsed and terminality is a real, asymmetric constraint rather
 than a consequence of every hom-setoid being a singleton -- the
 Bool argument Structure/Terminal.v's own header cites.

 Indexed half: over [_2, Sets] the pointwise product of the constant
 [bool]-indexed family has carrier [forall _ : bool, bool] by
 [eq_refl], contains two provably inequivalent elements
 ([two_bool_prod_separates]), and its projections compute.  The
 universal property is EXERCISED, not merely stated: [two_pick_med]
 is the mediator the class produces for the competing family
 [two_pick], it satisfies the triangle ([two_pick_med_commutes]), and
 it COMPUTES -- [two_pick_med_true] and [two_pick_med_false] are
 [eq_refl].

 STATUS.  72/72 constants report “Closed under the global context”,
 counted over [Print Module] so that the eighteen [Program] obligations --
 invisible to a [.glob] sweep, and queried by fully-qualified name --
 are included.

 REGISTRATION.  [Functor_Category_Terminal] is an [#[export] Instance],
 matching [Functor_Category_Cartesian], whose premise has the identical
 shape.  [Fun_HasIndexedProducts] is deliberately a plain [Definition],
 and the reason is an UNTESTED PRECAUTION rather than a measurement,
 which this sentence now says: the only other inhabitant of that class,
 [Sets_HasIndexedProducts], is a leaf, and registering a
 premise-carrying one could let resolution unify an unknown category
 with [Fun ?C ?D] and recurse.  That argument does NOT distinguish its
 own neighbours -- [Functor_Category_Cartesian] and this file's
 [Functor_Category_Terminal] are both premise-carrying [#[export]]
 instances with [Fun]-headed conclusions -- and no divergence has been
 exhibited either way.  Flipping it is a one-word change if a consumer
 wants it.

 WHAT IS NOT DELIVERED

 No [Limit]-shaped corollary, and the reason is measured here rather
 than inherited.  [Cone@{u0 u1 u2 u3 u4 u5}] is INNOCENT -- it takes
 [J : Category@{u0 u1 u2}] and [C : Category@{u3 u4 u5}], all six
 apart.  [IsALimit] and [Limit] are not: both are over
 [J : Category@{u0 u1 u1}] and [C : Category@{u2 u1 u1}], identifying
 the shape's hom and proof with the ambient's.  RECORDED CORRECTION:
 an earlier revision continued “[DiscreteCat_Functor]
 (Instance/Discrete.v) is unannotated and instantiates
 [DiscreteCat@{u Set Set}] while leaving C's hom free.  It takes BOTH
 to bite: [Limit (DiscreteCat_Functor f)] elaborates only at
 [C : Category@{u1 Set Set}], measured on this commit.  So the [Set]
 pin is not the functor's alone.”  The functor was annotated in place
 at Instance/Discrete.v in the PR “algebraic carriers are sets”
 (2026-09-17), and measured after it [iprod@{u u0 u1 u2 u3}] is
 stated over [C : Category@{u1 u2 u2}] -- no [Set] remains, and
 [Limit (DiscreteCat_Functor f)] elaborates with C's hom universe
 free.  What SURVIVES is the other half of the same diagnosis: the
 [IsALimit]/[Limit] identification above still ties the discrete
 shape's hom and proof universes to the ambient's, and that
 identification, not a [Set] floor, is now the whole content of this
 paragraph.  Read the [Cone] half NARROWLY: the
 RECORD is innocent, but that licenses no claim that [IsALimit] and
 [Limit] are the only other donors, and they are not --
 [cone_leg] (Structure/Limit/Preservation.v) and [IsLimitCone]
 identify the shape's hom and proof with the ambient's in
 exactly the same way, so CONE VOCABULARY is among the donors even
 though the record is not.  Structure/Limit/Initial.v's own header
 already warns that an [ACone] control rules out only [ACone]/[Cone];
 an earlier revision of this section ran that control and drew the
 broader conclusion anyway.
 [DiscreteCat] itself is properly annotated [@{o h p}].

 The general “limits in [C, D] are pointwise” theorem is now
 Instance/Fun/Limit.v's; this file has products only.  No colimits, no
 equalizers, no exponentials (pullbacks are now
 Instance/Fun/Pullback.v).  No [Cartesian] or
 [Complete] instance is derived for [C, D] from these.  No
 functoriality or naturality of [Fun_iprod] in the family or the
 index.  No proof that [HasIndexedProducts D] alone yields
 [Terminal D] (that needs a chosen empty index type, which would pin
 an index universe; [terminal_empty_IsIndexedProduct] takes the
 emptiness as a hypothesis instead).  Preservation is stated for
 POINTWISE limits only — Instance/Fun/Limit.v's [Eval_PreservesLimitCone],
 not connected to these products here.  And the general
 left fold of [Structure/Limit/Product/Finite.v] is consumed
 ([iprod_unique_iso]) but not extended. 

 --------
 nLab:       https://ncatlab.org/nlab/show/functor+category 
 nLab:       https://ncatlab.org/nlab/show/terminal+object 
 nLab:       https://ncatlab.org/nlab/show/product 
 维基百科:  https://en.wikipedia.org/wiki/Product_(category_theory) 
 书籍:      Mac Lane, CWM 第二版, §III.5 练习 5, 第 74 页
 ([maclane:III.5:ex5]): 如果 D 有（有限）积，则函子范畴 [C, D] 也有积，按点计算。

 提供的内容及其强度

 [Functor_Category_Terminal T : @Terminal ([C, D] )] 对于任何
 [T : @Terminal D] -- 常函子到 1，带有唯一的自然变换进它。这是练习的零元部分。

 [Fun_HasIndexedProducts HP : @HasIndexedProducts ([C, D] )] 对于任何
 [HP : @HasIndexedProducts D] -- 在任意索引 [Type] 点计算的积，而不仅仅是有限索引。这是练习的实质部分。所有内容首先在基础的、顶点固定的级别上陈述，然后才被打包。[Fun_iprod] / [Fun_iprod_proj] / [Fun_IsIndexedProduct] 是基础数据——一个 [C, D] 的对象，它的一族自然变换，以及 [Structure/Limit/Product.v] 的 [IsIndexedProduct] 对那一族的记录——而 [Fun_HasIndexedProducts] 是 [Build_HasIndexedProducts] 正好应用于这三者。文件中的任何地方都没有 [Limit]、[Cone] 和 [DiscreteCat]；关于测量原因，请参见未交付。两个部分如何组合在一起。它们是同一个现象：
 [Fun_empty_iprod_terminal] 表现为终端函子，作为一个空索引上的逐点索引积，具有规范性。在 [C, D] 中它是一个同构，而不是更强的，因为 D 的空 [indexed_product] 是 [HasIndexedProducts D] 所选择的，且没有任何东西强制该选择为 [terminal_obj]。使之成立的部分是 [terminal_empty_IsIndexedProduct]，它是在任意 [A] 上陈述的，带有 [A -> False]，而不是在一个具名的空类型上，因此没有索引宇宙被固定。

 每个假设都已被使用[Terminal D] 提供对象 ([Constant_Terminal_Functor])，并且通过 [one_unique] 履行 [Terminal] 记录的义务。这个句子的早期版本说“正好两次……没有其他使用”，这是错误的：它还被 [terminal_empty_IsIndexedProduct]、[Fun_empty_iprod_terminal]、[Two_Sets_Terminal] 和 [two_pick] 消耗。[HasIndexedProducts D]提供对象、投影和
 普适性质——Structure/Limit/Product.v 的三个字段
 类别——其UMP也直接应用于某些地方。什么ONE？
 导出引理携带的引理是路由：每个函子定律
 [Fun_iprod]，下面的每个自然性方格都是“与
 投影和计算“通过[iprod_jointly_monic]，二
 态射映射为索引积，且在每次投影后都一致
 相等。注意引理取[IsIndexedProduct]，而非
 课堂。（早期修订说课堂时间都在那一节课上
 仅凭引理;那是假的。）[iprod_jointly_monic] 不是新的，这个标题的早期修订版声称它是新的，原因是搜索了名称 [jointly_monic]——恰恰是该树自身约定所警告的陷阱。Structure/Bicartesian/Matrix.v 已经有 [iprod_ext]，对于带索引的乘积有相同的陈述，基本上证明也相同，并且还有对偶的 [icoprod_ext]。真正正确的，也是重新陈述它的真正原因，是 [iprod_ext] 的类型携带了一个虚假的 [IsIndexedCoproduct] 参数，这是从其节继承来的，因此如果不提供一个与该陈述无关的余积，就无法在这里应用它。一个无假设版本的自然归宿是 Structure/Limit/Product.v；它在这里被声明是因为这个问题的可交付成果就是这个文件。

 先前技术——已引用，未重复BINARY 情况是 [Functor_Category_Cartesian]
 (Instance/Fun/Cartesian.v)。 它没有被重新证明，也没有被包含；它是被比较的，见下文。一般的逐点极限事实至少在三个地方以散文形式陈述过（自从在 Instance/Fun/Limit.v 中重新指出，它证明了该事实）：Structure/Cartesian/Product.v（“当 D 存在极限时，函子范畴中的极限逐点计算的普遍事实”）、Instance/Fun.v 和 Instance/Fun/Cartesian.v，其中引用了 nLab。 当时缺失的是超出二元积的任何 Coq 声明：在此提交上重新验证，没有任何函子范畴的实例存在（检查了每一个名称或类型提到 [Terminal] 的声明），任何地方也不存在逐点索引乘积——[HasIndexedProducts] 仅有一个实例，[Sets_HasIndexedProducts]（Instance/Sets/Products.v），以及在 Structure/Limit/Coproduct.v 中的 [C^op] 重新包装。[Functor/Diagonal.v] 的 [Diagonal] 已经携带了一个恒定函子作为其对象作用，并且 [Constant_Functor] 并未定义为 [fobj[Diagonal C] d]。两个作用完全一致（[constant_functor_diagonal_obj]，[constant_functor_diagonal_fmap]，均为 [eq_refl]）；这两个记录则不一致（[constant_functor_is_diagonal]，一个固定转换为负 -- [Diagonal] 是一个 [Program Instance]，因此它的三个定律字段是透明的义务常量）。不通过它的原因是一个宇宙测量，而不是偏好；见下文。

 二进制比较，是测量而非假设[Fun_bool_iprod_iso] 将在两个元素索引下的逐点索引乘积与 [Functor_Category_Cartesian] 的逐点二元乘积联系起来。这个强度在 [C, D] 中是一个同构，而在 [eq_refl] 中不是：[bool_iprod_is_binary_product] 是一个固定转换的负式，[ctl_bool_iprod_obj] 在相同参数下是传递控制。这个障碍不是表现性的——[HasIndexedProducts D] 和 [Cartesian D] 独立选择它们的对象，并且没有任何东西将两者的选择联系起来——因此同构是可用的最强陈述。它携带其腿方程（[Fun_bool_iprod_iso_commutes] 和 [Fun_bool_iprod_iso_inv_commutes]，都是腿族而不是单个）；一个裸露的 [≅] 将是弱形式。这个比较是可行的，因为启用部分是通用的：
 [cartesian_bool_IsIndexedProduct] 证明在任意笛卡尔范畴中二元积是 [bool] 上的一个索引积，
 并且有 [exl] / [exr] 作为两个投影。在 [Functor_Category_Cartesian] 下实例化，它给出相同族的第二个 [IsIndexedProduct]，
 而 [iprod_unique_iso] (Structure/Limit/Product/Finite.v) 处理其余部分。其自身的约束块与 [IsIndexedProduct] 完全相同，因此它没有增加任何宇宙内容。

 严格性，按严格优先度测量在 [eq_refl] 上保持：终端函子（terminal functor）的对象作用，它的箭头作用，以及其唯一箭头（[fun_terminal_obj]、[fun_terminal_fmap]、[fun_terminal_one_component]）的分量；逐点积的对象作用及其投影的分量（[fun_iprod_obj_computes]、[fun_iprod_proj_component]）；从打包类中提取的中介者是 [fun_iprod_tuple]（[fun_iprod_class_mediator]）；以及 [Constant_Functor] 对 [Diagonal] 的两个作用。

 已被反驳，每个都被固定为 [Fail]，并附有一个通过控制：在 [bool] 索引处的逐点索引积不是逐点二元积，且 [Constant_Functor d] 不是 [Diagonal] 记录。两者都是真正的转换失败（“无法统一”），从剥离的命令中读取，而不是推断得出。

 宇宙——块已全部读取，捐献者单独测试四位捐赠者在一个部分被拒绝，该部分声明 [Constraint uh < up] 未通过相同级别的控制，因此以下内容是受保护的，而不仅仅是从打印的活页夹中读取。[Terminal@{u u0}]、[HasIndexedProducts]、[IsIndexedProduct] 和 [Cartesian] 每个都将其类别作为 [Category@{o h h}]：他们每个人都用证明确认了同态。[Fun] 做得更多——[Fun@{...} : Category@{u u0 u0} -> Category@{u1 u2 u2} -> Category@{u3 u4 u4}] 和 [u0 = u2] ——因此它在两个参数中以及两个同态级别之间都用证明确认了同态。[Constant_Functor@{co ch cp dro dh dp}] 不识别任何内容：它的区块是五个界限 [ch <= cp]、[ch <= dh]、[ch <= dp]、[cp <= dp]、[dh <= dp]，这正是 [Functor] 自己的区块，一字不差。[Constant_Terminal_Functor@{co ch cp dro dh}] 接受 D 于 [Category@{dro dh dh}] —— 这是 [Terminal] 的操作 —— 而 C 的同质和证明保持分离（[ch <= cp]）。两者都是手写的记录字面量，带有显式的宇宙绑定器，正是为保持这种状态：在未注释的 [Section] 中写作 [Program Definition] 时，它们最小化为 [C : Category@{u u0 u0}]，而注释形式随后被拒绝，因为 [Program] 引入了一个义务宇宙，而没有任何 [@{...}] 列表能够绑定它。通过 [Diagonal] 路由会花费那个费用，并且这是测量的：
 [fobj[@Diagonal D C] d] 在 [C : Category@{co ch cp}] 被拒绝，伴随 [ch < cp] （“无法执行 cp = dh”），在两个通过的控制下，
 因为 [Diagonal] 的类型提到了 [C, D]，因此即使只需要一个纯常量函子，也会继承 [Fun] 的标识。

 [Functor_Category_Terminal@{u u0 u1 u2 u3 u4}] 位于 [C : Category@{u2 u4 u4}] 和 [D : Category@{u3 u4 u4}] 上——两者都被标识，并且两个 hom 层级是相同的 [u4]。这是 [Fun] 的操作，它存在于 BINDER 中：约束块有六个界限（[u4 < u], [u2 <= u0], [u2 <= u1], [u3 <= u0], [u4 <= u0], [u4 <= u1]），其中没有任何方程，因此仅阅读该块会完全错过标识。[Fun_iprod@{u u0 u1 u2 u3 u4 u5 u6}] 位于 [C : Category@{u u0 u0}] 和 [D : Category@{u1 u2 u2}] 之上——这两个同类水平保持独立（[u0 <= u2] 是一个界，不是方程），而 INDEX 宇宙 [u5] 只是有界的（[u5 <= u3]、[u5 <= u4]），从未被识别。D 的同类=证明是 [HasIndexedProducts] 做的。C 的不是由 donor 强制的：[Functor] 使它们保持分离，正如上面的 [Constant_Functor] 所示，所以它是该部分未注释的 [Context {C : Category}]，是为 [Build_Quiver_Standard_Eq] 记录的最小化族。原则上它是可以修复的，并且并不声称不可避免；没有尝试完整提升，在打包级别上对消费者没有任何费用，因为 [Fun] 无论如何都识别了两者。该文件唯一的方程是 [Fun] 的 [u0 = u2]，并且它由八个常量携带，而不是一个：[Fun_IsIndexedProduct] 连同 [fun_terminal_obj]、[fun_terminal_fmap]、[fun_terminal_one_component]、[fun_iprod_tuple]、[constant_functor_diagonal_obj]、[constant_functor_diagonal_fmap] 和 [ctl_bool_iprod_obj]——每个常量的语句在 [C, D]。每次都是同一个方程，因此结论不变，但该句的早期修订版本只提到一个常量，并且以计数形式读取，而在文件的其他地方则坚持要求完整读取一个宇宙块。[iprod_jointly_monic@{u u0 u1 u2}] 保留其索引宇宙边界（[u <= u1]）且从未被识别。证人携带 [Set]，并且这是形状的：
 [Two_Sets_HasIndexedProducts] 详细说明于
 [Fun@{u0 Set u1 Set u u0 u1}] -- [Instance/Two.v] 声明
 [TwoHom : ... -> Set]，并且 [Fun] 确认形状的同级别与目标的相同，所以 [Sets] 被截断为 [Sets@{Set u1}]，载体在 [Set]。 这是使用 [_2] 作为形状的代价，而不是一般定理的属性，后者根本不含 [Set]。

 非空性终端半：[two_pick true] 和 [two_pick false] 是两个可证明不同的自然变换，进入 [_2, Sets]（[two_pick_distinct]）的函子，而 [two_sets_one_unique] 对于任何函子都有箭头指向终端函子且唯一。因此，该范畴并未崩塌，终端性是一个真实的、非对称的约束，而不是每个 hom-集都是单元素集的结果——Structure/Terminal.v 的头部对 Bool 参数的论述提及了这一点。索引的一半：在 [_2, Sets] 上，常数 [bool] 索引族的点乘的承载体为 [forall _ : bool, bool]，由 [eq_refl] 组成，包含两个可证明的不等价元素（[two_bool_prod_separates]），其投影可以计算。这个普遍性性质是被实际应用的，而不仅仅是陈述：[two_pick_med] 是类为竞争族 [two_pick] 生成的中介器，它满足三角形（[two_pick_med_commutes]），并且它可以计算——[two_pick_med_true] 和 [two_pick_med_false] 是 [eq_refl]。 状态。72/72 个常数报告“在全局上下文下封闭”，在 [Print Module] 上计数，以便十八个 [Program] 义务——对 [.glob] 扫描不可见，并通过完全限定名称查询——也包括在内。注册。[Functor_Category_Terminal] 是一个 [#[export] 实例，匹配 [Functor_Category_Cartesian]，其前提具有相同的形状。[Fun_HasIndexedProducts] 故意是一个普通的 [Definition]，其原因是一种未经测试的预防措施而不是度量，本句现在这样说明：该类的唯一其他成员 [Sets_HasIndexedProducts] 是叶子，而注册一个带前提的实例可能让归结法将一个未知类别与 [Fun ?C ?D] 统一并递归。该论点并没有区分它自己的邻居——[Functor_Category_Cartesian] 和此文件的 [Functor_Category_Terminal] 均为带前提的 [#[export] 实例，且带 [Fun] 头的结论——无论哪种方式都未显示出分歧。如果用户想要，可以通过一个单词的修改来翻转它。

 未交付的内容是什么没有[Limit]形的推论，原因是这里进行测量，而不是继承。[Cone@{u0 u1 u2 u3 u4 u5}]是无辜的——它接受[J : Category@{u0 u1 u2}]和[C : Category@{u3 u4 u5}]，六个都分开。[IsALimit]和[Limit]不是：两者都在[J : Category@{u0 u1 u1}]和[C : Category@{u2 u1 u1}]上，识别形状的同态和证明与环境的相同。记录的更正：早期版本继续“[DiscreteCat_Functor]（Instance/Discrete.v）未标注并实例化[DiscreteCat@{u Set Set}]，同时保留C的同态为空。它需要两个才能处理：[Limit (DiscreteCat_Functor f)]只在[C : Category@{u1 Set Set}] elaborates，这里进行测量的提交。所以 [Set] 引脚并非仅属于函子。函子已在 PR “代数承载体是集合” (2026-09-17) 中于 Instance/Discrete.v 处进行了原地标注，并在其之后测量 [iprod@{u u0 u1 u2 u3}] 被声明在 [C : Category@{u1 u2 u2}] 上——没有 [Set] 剩下，而 [Limit (DiscreteCat_Functor f)] 则在 C 的 hom 宇宙中进行扩展。存留下来的部分是同一诊断的另一半：上述 [IsALimit] / [Limit] 的识别仍然将离散形状的 hom 和证明宇宙绑定到环境的宇宙中，而该识别，而非 [Set] 底层，现在是本段的全部内容。仔细阅读 [Cone] 半窄：记录是无辜的，但这并不能证明 [IsALimit] 和 [Limit] 是唯一的其他捐赠者，而且它们并不是——[cone_leg]（Structure/Limit/Preservation.v）和 [IsLimitCone] 以完全相同的方式将形状的 hom 和证明与环境的相匹配，因此 CONE VOCABULARY 也在捐赠者之中，即使记录中没有。Structure/Limit/Initial.v 本身的标题已经警告说 [ACone] 控制只排除了 [ACone] / [Cone]；该部分的早期修订版本运行了该控制，并无论如何得出了更广泛的结论。[DiscreteCat] 本身已被正确标注为 [@{o h p}]。一般的“[C, D]中的极限是点态的”定理现在在Instance/Fun/Limit.v中；该文件只有积。没有余极限，没有等化器，没有指数（拉回现在在Instance/Fun/Pullback.v中）。没有从这些派生[C, D]的[Cartesian]或[Complete]实例。[Fun_iprod]在族或指标上的函子性或自然性没有说明。没有证明单独的[HasIndexedProducts D]可以得到[Terminal D]（那需要一个选定的空索引类型，这会固定一个索引宇宙；[terminal_empty_IsIndexedProduct]则将空性作为假设）。只陈述了点态极限的保持性——Instance/Fun/Limit.v中的[Eval_PreservesLimitCone]，与此处的这些积无关。[Structure/Limit/Product/Finite.v]的一般左折叠被使用（[iprod_unique_iso]），但没有被扩展。
*)

(* * ** Joint monicity of a family of product projections / * ** 一族乘积投影的联合单调性 *)

(*
 Two morphisms into an indexed product that agree after every projection
 are equal.  This is the only place [HasIndexedProducts D] is spent below:
 every functor law and every naturality square of the pointwise product is
 “compose with the projections and compute” through it.  It is stated for
 the elementary [IsIndexedProduct] record, so it applies equally to a
 product harvested from the class. 

 --------
 两个映射到索引积的同态，如果在每个投影之后都相等，则它们相等。下面唯一使用 [HasIndexedProducts D] 的地方就是：点积的每个函子规律和每个自然性方形都是“与投影组合并通过它计算”。它是为基本的 [IsIndexedProduct] 记录而陈述的，因此同样适用于从类中获取的积。
*)
Lemma iprod_jointly_monic {C : Category} {A : Type} (f : A → C)
  (p : C) (proj : ∀ a : A, p ~> f a)
  (HP : IsIndexedProduct f p proj)
  {c : C} (u v : c ~> p) :
  (∀ a : A, proj a ∘ u ≈ proj a ∘ v) → u ≈ v.
Proof.
  intros Heq.
  pose proof (iprod_desc HP (fun a => proj a ∘ u)) as U.
  transitivity (unique_obj U).
  - symmetry.
    apply (uniqueness U).
    intros a; reflexivity.
  - apply (uniqueness U).
    intros a; symmetry; apply Heq.
Qed.

(* * ** The constant functor, and the terminal functor / * ** 常量函子，以及终端函子 *)

(*
 The constant functor at [d]: every object goes to [d], every morphism to
 [id].  Written as an explicit record literal, rather than as a [Program
 Definition] in a [Section], so that its universe binders can be spelled
 out and C's hom and proof universes stay apart; see the header. 

 --------
 在 [d] 上的常量函子：每个对象都映射到 [d]，每个态射映射到 [id]。以显式记录字面量的形式写出，而不是在 [Section] 中作为 [Program Definition]，这样它的宇宙绑定器可以被明确表示，并且 C 的 hom 和证明宇宙保持分离；见标题。
*)
Definition Constant_Functor@{co ch cp dro dh dp}
  {C : Category@{co ch cp}} {D : Category@{dro dh dp}} (d : D) : C ⟶ D :=
  {| fobj          := fun _ => d
   ; fmap          := fun _ _ _ => id
   ; fmap_respects := fun _ _ _ _ _ => reflexivity _
   ; fmap_id       := fun _ => reflexivity _
   ; fmap_comp     := fun _ _ _ _ _ => symmetry (id_left id) |}.

(*
 The terminal object of [C, D]: the constant functor at 1.  D's hom and
 proof universes are identified here, and that is [Terminal]'s doing. 

 --------
 [C, D] 的终端对象：常数函子在 1。这里标识了 D 的同态和证明宇宙，这是 [Terminal] 的作用。
*)
Definition Constant_Terminal_Functor@{co ch cp dro dh}
  {C : Category@{co ch cp}} {D : Category@{dro dh dh}}
  (T : @Terminal D) : C ⟶ D :=
  Constant_Functor@{co ch cp dro dh dh} (@terminal_obj D T).

(*
 Mac Lane §III.5 Ex 5, nullary case.  The unique arrow [F ⟹ 1] has the
 unique arrow of D at every component; all three obligations -- the two
 naturality orientations and uniqueness -- are [one_unique]. 

 --------
 Mac Lane §III.5 练习 5，无元情况。唯一的箭头 [F ⟹ 1] 在每个分量上都有 D 的唯一箭头；所有三个义务——两个自然性的方向和唯一性——都是 [one_unique]。
*)
#[export]
Program Instance Functor_Category_Terminal {C D : Category}
  (T : @Terminal D) : @Terminal ([C, D]) := {|
  terminal_obj := Constant_Terminal_Functor T;
  one := fun F => {| transform := fun _ => one |}
|}.
Next Obligation. apply one_unique. Qed.
Next Obligation. apply one_unique. Qed.
Next Obligation. apply one_unique. Qed.

(** ** Pointwise indexed products / ** 点对点索引的乘积 *)

Section FunIndexedProducts.

Context {C : Category}.
Context {D : Category}.
Context (HP : @HasIndexedProducts D).
Context {A : Type}.
Context (F : A → (C ⟶ D)).

Definition fun_iprod_fam (c : C) : A → D := fun a => fobj[F a] c.

Definition fun_iprod_obj (c : C) : D := indexed_product (fun_iprod_fam c).

Definition fun_iprod_pr (c : C) (a : A) : fun_iprod_obj c ~> F a c :=
  indexed_product_proj (fun_iprod_fam c) a.

Definition fun_iprod_ump (c : C) :
  IsIndexedProduct (fun_iprod_fam c) (fun_iprod_obj c) (fun_iprod_pr c) :=
  indexed_product_ump (fun_iprod_fam c).

(*
 The arrow action: the unique map into the product at [c'] induced by the
 family whose [a]th leg is [fmap[F a] g] after the [a]th projection. 

 --------
 箭头作用：由其第 [a] 条腿在第 [a] 次投影之后变为 [fmap[F a] g] 的族所诱导的映射到积 [c'] 的唯一映射。
*)
Definition fun_iprod_fmap {c c' : C} (g : c ~> c') :
  fun_iprod_obj c ~> fun_iprod_obj c' :=
  unique_obj (iprod_desc (fun_iprod_ump c')
                (fun a => fmap[F a] g ∘ fun_iprod_pr c a)).

Lemma fun_iprod_fmap_commutes {c c' : C} (g : c ~> c') (a : A) :
  fun_iprod_pr c' a ∘ fun_iprod_fmap g
    ≈ fmap[F a] g ∘ fun_iprod_pr c a.
Proof.
  exact (unique_property
           (iprod_desc (fun_iprod_ump c')
              (fun a => fmap[F a] g ∘ fun_iprod_pr c a)) a).
Qed.

(*
 The pointwise product as a functor.  Each of the three laws is proved by
 composing with the projections and appealing to [iprod_jointly_monic]. 

 --------
 逐点乘积作为一个函子。每一条定律都通过与投影相组合并引用 [iprod_jointly_monic] 来证明。
*)
Program Definition Fun_iprod : C ⟶ D := {|
  fobj := fun_iprod_obj;
  fmap := fun c c' g => fun_iprod_fmap g
|}.
Next Obligation.
  proper.
  apply (iprod_jointly_monic _ _ _ (fun_iprod_ump y)).
  intros a.
  rewrite (fun_iprod_fmap_commutes x0 a).
  rewrite (fun_iprod_fmap_commutes y0 a).
  now rewrite X.
Qed.
Next Obligation.
  apply (iprod_jointly_monic _ _ _ (fun_iprod_ump x)).
  intros a.
  rewrite (fun_iprod_fmap_commutes (@id C x) a).
  rewrite fmap_id, id_left, id_right.
  reflexivity.
Qed.
Next Obligation.
  apply (iprod_jointly_monic _ _ _ (fun_iprod_ump z)).
  intros a.
  rewrite (fun_iprod_fmap_commutes (f ∘ g) a).
  rewrite fmap_comp.
  rewrite (comp_assoc (fun_iprod_pr z a)
             (fun_iprod_fmap f) (fun_iprod_fmap g)).
  rewrite (fun_iprod_fmap_commutes f a).
  rewrite <- (comp_assoc (fmap[F a] f) (fun_iprod_pr y a)
                (fun_iprod_fmap g)).
  rewrite (fun_iprod_fmap_commutes g a).
  rewrite (comp_assoc (fmap[F a] f) (fmap[F a] g) (fun_iprod_pr x a)).
  reflexivity.
Qed.

(*
 The [a]th projection is a natural transformation: its naturality square
 IS the defining equation of the arrow action. 

 --------
 [a] th 投影是一个自然变换：它的自然性方格就是箭头作用的定义方程。
*)
Program Definition Fun_iprod_proj (a : A) : Fun_iprod ⟹ F a := {|
  transform := fun c => fun_iprod_pr c a
|}.
Next Obligation. symmetry; apply fun_iprod_fmap_commutes. Qed.
Next Obligation. apply fun_iprod_fmap_commutes. Qed.

Definition fun_iprod_tuple_at (Q : C ⟶ D) (pi : ∀ a, Q ⟹ F a) (c : C) :
  Q c ~> fun_iprod_obj c :=
  unique_obj (iprod_desc (fun_iprod_ump c) (fun a => transform (pi a) c)).

Lemma fun_iprod_tuple_commutes (Q : C ⟶ D) (pi : ∀ a, Q ⟹ F a)
  (c : C) (a : A) :
  fun_iprod_pr c a ∘ fun_iprod_tuple_at Q pi c ≈ transform (pi a) c.
Proof.
  exact (unique_property
           (iprod_desc (fun_iprod_ump c) (fun a => transform (pi a) c)) a).
Qed.

(*
 The mediating transformation.  Its naturality is where the naturality of
 the competing family [pi] is spent, and nowhere else. 

 --------
 中介变换。它的自然性就在于竞争族 [pi] 的自然性被消耗的地方，而不在其他地方。
*)
Program Definition fun_iprod_tuple (Q : C ⟶ D) (pi : ∀ a, Q ⟹ F a) :
  Q ⟹ Fun_iprod := {|
  transform := fun c => fun_iprod_tuple_at Q pi c
|}.
Next Obligation.
  apply (iprod_jointly_monic _ _ _ (fun_iprod_ump y)).
  intros a.
  rewrite (comp_assoc (fun_iprod_pr y a) (fun_iprod_fmap f)
             (fun_iprod_tuple_at Q pi x)).
  rewrite (fun_iprod_fmap_commutes f a).
  rewrite <- (comp_assoc (fmap[F a] f) (fun_iprod_pr x a)
                (fun_iprod_tuple_at Q pi x)).
  rewrite (fun_iprod_tuple_commutes Q pi x a).
  rewrite (comp_assoc (fun_iprod_pr y a) (fun_iprod_tuple_at Q pi y)
             (fmap[Q] f)).
  rewrite (fun_iprod_tuple_commutes Q pi y a).
  apply naturality.
Qed.
Next Obligation.
  symmetry.
  apply (iprod_jointly_monic _ _ _ (fun_iprod_ump y)).
  intros a.
  rewrite (comp_assoc (fun_iprod_pr y a) (fun_iprod_fmap f)
             (fun_iprod_tuple_at Q pi x)).
  rewrite (fun_iprod_fmap_commutes f a).
  rewrite <- (comp_assoc (fmap[F a] f) (fun_iprod_pr x a)
                (fun_iprod_tuple_at Q pi x)).
  rewrite (fun_iprod_tuple_commutes Q pi x a).
  rewrite (comp_assoc (fun_iprod_pr y a) (fun_iprod_tuple_at Q pi y)
             (fmap[Q] f)).
  rewrite (fun_iprod_tuple_commutes Q pi y a).
  apply naturality.
Qed.

(*
 The elementary universal property, in [C, D].  Existence is
 [fun_iprod_tuple]; the triangle and the uniqueness clause are the
 corresponding facts in D, taken at each object. 

 --------
 基本的泛性质，在 [C, D] 中。存在性是 [fun_iprod_tuple]；三角形以及唯一性条款是在 D 中对应的事实，对每个对象都适用。
*)
Program Definition Fun_IsIndexedProduct :
  @IsIndexedProduct ([C, D]) A F Fun_iprod Fun_iprod_proj := {|
  iprod_desc := fun Q pi => {| unique_obj := fun_iprod_tuple Q pi |}
|}.
Next Obligation. apply fun_iprod_tuple_commutes. Qed.
Next Obligation.
  apply (uniqueness
           (iprod_desc (fun_iprod_ump x) (fun a => transform (pi a) x))).
  intros a.
  apply X.
Qed.

End FunIndexedProducts.

(*
 Mac Lane §III.5 Ex 5, the substantial case, packaged with the class's own
 constructor from exactly the elementary datum above.  Deliberately a plain
 [Definition] rather than an [Instance]; see the header. 

 --------
 Mac Lane §III.5 练习 5，实质性情况，与类自身的构造函数一起打包，正好来自上面的基本数据。故意是一个普通的 [Definition] 而不是 [Instance]；参见标题。
*)
Definition Fun_HasIndexedProducts {C D : Category}
  (HP : @HasIndexedProducts D) : @HasIndexedProducts ([C, D]) :=
  @Build_HasIndexedProducts ([C, D])
    (fun A F => @Fun_iprod C D HP A F)
    (fun A F a => @Fun_iprod_proj C D HP A F a)
    (fun A F => @Fun_IsIndexedProduct C D HP A F).

(* * ** The binary case: a product is an indexed product over [bool] / * ** 二元情况：一个积是 [bool] 上的索引积 *)

Definition bool_fam {C : Category} (x y : C) : bool → C :=
  fun b => if b then x else y.

Definition cartesian_bool_proj {C : Category} (CP : @Cartesian C) (x y : C)
  (b : bool) : @product_obj C CP x y ~> bool_fam x y b :=
  match b with
  | true  => exl
  | false => exr
  end.

Program Definition cartesian_bool_IsIndexedProduct {C : Category}
  (CP : @Cartesian C) (x y : C) :
  IsIndexedProduct (bool_fam x y) (@product_obj C CP x y)
    (cartesian_bool_proj CP x y) := {|
  iprod_desc := fun c pi => {| unique_obj := pi true △ pi false |}
|}.
Next Obligation.
  destruct a; simpl.
  - apply exl_fork.
  - apply exr_fork.
Qed.
Next Obligation.
  symmetry.
  apply ump_products.
  split.
  - exact (X true).
  - exact (X false).
Qed.

(*
   * The pointwise indexed product at a two-element index, compared with the
   pointwise binary product of Instance/Fun/Cartesian.v. 

   --------
   * 在两元素索引处的逐点索引乘积，与 Instance/Fun/Cartesian.v 的逐点二元乘积相比。
*)

Definition Fun_bool_iprod_iso {C D : Category}
  (HP : @HasIndexedProducts D) (CD : @Cartesian D) (F G : C ⟶ D) :
  @Isomorphism ([C, D])
    (Fun_iprod HP (@bool_fam ([C, D]) F G))
    (@product_obj ([C, D]) (Functor_Category_Cartesian C D CD) F G) :=
  iprod_unique_iso (@bool_fam ([C, D]) F G) _ _ _ _
    (Fun_IsIndexedProduct HP (@bool_fam ([C, D]) F G))
    (cartesian_bool_IsIndexedProduct
       (Functor_Category_Cartesian C D CD) F G).

Definition Fun_bool_iprod_iso_commutes {C D : Category}
  (HP : @HasIndexedProducts D) (CD : @Cartesian D) (F G : C ⟶ D) (b : bool) :
  cartesian_bool_proj (Functor_Category_Cartesian C D CD) F G b
    ∘ to (Fun_bool_iprod_iso HP CD F G)
    ≈ Fun_iprod_proj HP (@bool_fam ([C, D]) F G) b :=
  iprod_compare_commutes (@bool_fam ([C, D]) F G) _ _ _ _
    (cartesian_bool_IsIndexedProduct
       (Functor_Category_Cartesian C D CD) F G) b.

Definition Fun_bool_iprod_iso_inv_commutes {C D : Category}
  (HP : @HasIndexedProducts D) (CD : @Cartesian D) (F G : C ⟶ D) (b : bool) :
  @compose ([C, D]) _ _ _
      (Fun_iprod_proj HP (@bool_fam ([C, D]) F G) b)
      (from (Fun_bool_iprod_iso HP CD F G))
    ≈ cartesian_bool_proj (Functor_Category_Cartesian C D CD) F G b :=
  iprod_compare_inv_commutes (@bool_fam ([C, D]) F G) _ _ _ _
    (Fun_IsIndexedProduct HP (@bool_fam ([C, D]) F G)) b.

(* * ** What computes, and what does not / * ** 什么可以计算，什么不可以计算 *)

Section Strictness.

Context {C : Category}.
Context {D : Category}.
Context (T : @Terminal D).
Context (HP : @HasIndexedProducts D).

Example fun_terminal_obj (c : C) :
  fobj[@terminal_obj ([C, D]) (Functor_Category_Terminal T)] c
    = @terminal_obj D T := eq_refl.

Example fun_terminal_fmap (c c' : C) (f : c ~> c') :
  fmap[@terminal_obj ([C, D]) (Functor_Category_Terminal T)] f
    = @id D (@terminal_obj D T) := eq_refl.

Example fun_terminal_one_component (F : C ⟶ D) (c : C) :
  transform (@one ([C, D]) (Functor_Category_Terminal T) F) c
    = @one D T (F c) := eq_refl.

Example fun_iprod_obj_computes {A : Type} (F : A → (C ⟶ D)) (c : C) :
  fobj[Fun_iprod HP F] c = indexed_product (fun a => fobj[F a] c) := eq_refl.

Example fun_iprod_proj_component {A : Type} (F : A → (C ⟶ D))
  (a : A) (c : C) :
  transform (Fun_iprod_proj HP F a) c
    = indexed_product_proj (fun a => fobj[F a] c) a := eq_refl.

End Strictness.

Section StrictnessNegatives.

Context {C : Category}.
Context {D : Category}.
Context (HP : @HasIndexedProducts D).
Context (CD : @Cartesian D).
Context (F G : C ⟶ D) (c : C).

(*
 CONTROL: the object action of the pointwise indexed product is the
 indexed product of the pointwise family, on the nose. 

 --------
 控制：逐点索引积的对象作用是逐点族的索引积，完全相等。
*)
Example ctl_bool_iprod_obj :
  fobj[Fun_iprod HP (@bool_fam ([C, D]) F G)] c
    = indexed_product (fun b : bool => fobj[@bool_fam ([C, D]) F G b] c)
  := eq_refl.

(*
 NEGATIVE (conversion): it is NOT the pointwise binary product.  The two
 are related by [Fun_bool_iprod_iso] and by nothing stronger, because
 [HasIndexedProducts D] and [Cartesian D] choose their objects
 independently. 

 --------
 否定（转换）：它不是逐点的二元积。两者通过  [Fun_bool_iprod_iso]  相关，但没有更强的关系，因为  [HasIndexedProducts D]  和  [Cartesian D]  独立选择它们的对象。
*)
Fail Example bool_iprod_is_binary_product :
  fobj[Fun_iprod HP (@bool_fam ([C, D]) F G)] c
    = fobj[@product_obj ([C, D]) (Functor_Category_Cartesian C D CD) F G] c
  := eq_refl.

(* The mediator extracted from the class IS [fun_iprod_tuple], on the nose. / 从类中提取的中介是 [fun_iprod_tuple]，正中目标。 *)
Example fun_iprod_class_mediator {A : Type} (Fm : A → (C ⟶ D))
  (Q : C ⟶ D) (pi : ∀ a, Q ⟹ Fm a) :
  unique_obj (iprod_desc (Fun_IsIndexedProduct HP Fm) pi)
    = fun_iprod_tuple HP Fm Q pi := eq_refl.

End StrictnessNegatives.

(* * ** Relation to the diagonal functor / * ** 与对角函子相关 *)

Section DiagonalComparison.

Context {C : Category}.
Context {D : Category}.
Context (d : D) (c : C).

(*
 Object and arrow actions agree with [Functor/Diagonal.v]'s constant
 functor ON THE NOSE. 

 --------
 对象和箭头动作与[Functor/Diagonal.v]的常量函子完全一致。
*)
Example constant_functor_diagonal_obj :
  fobj[@Constant_Functor C D d] c = fobj[fobj[@Diagonal D C] d] c := eq_refl.

Example constant_functor_diagonal_fmap (f : c ~> c) :
  fmap[@Constant_Functor C D d] f = fmap[fobj[@Diagonal D C] d] f := eq_refl.

(*
 NEGATIVE (conversion): the two functor RECORDS are not the same term.
 [Diagonal] is a [Program Instance], so its three law fields are opaque
 obligation constants, while [Constant_Functor] supplies them as explicit
 terms. 

 --------
 否定（转换）：两个函子 RECORDS 不是相同的项。[Diagonal] 是一个 [Program Instance]，因此它的三个法域字段是不可见的义务常量，而 [Constant_Functor] 则将它们作为显式项提供。
*)
Fail Example constant_functor_is_diagonal :
  @Constant_Functor C D d = fobj[@Diagonal D C] d := eq_refl.

End DiagonalComparison.

(** ** Witnesses over [_2, Sets] / ** 目击者超过 [_2, Sets] *)

Definition FunBoolSet : SetoidObject := {|
  carrier   := bool
; is_setoid := eq_Setoid bool
|}.

Definition Two_Bool : _2 ⟶ Sets := @Constant_Functor _2 Sets FunBoolSet.

Definition Two_Sets_Terminal : @Terminal ([_2, Sets]) :=
  Functor_Category_Terminal Sets_Terminal.

Example two_sets_terminal_obj (o : _2) :
  fobj[@terminal_obj ([_2, Sets]) Two_Sets_Terminal] o
    = @terminal_obj Sets Sets_Terminal := eq_refl.

Program Definition two_pick (b : bool) :
  @terminal_obj ([_2, Sets]) Two_Sets_Terminal ⟹ Two_Bool := {|
  transform := fun _ => {| morphism := fun _ => b |}
|}.

(*
 Non-degeneracy of the terminal object: arrows OUT of the terminal functor
 are unique, arrows INTO a functor are not.  So [_2, Sets] is not
 collapsed, and terminality is a real constraint rather than a
 consequence of every hom-setoid being a singleton. 

 --------
 终对象的非退化性：从终函子发出的箭是唯一的，箭射向一个函子则不唯一。因此，[_2, Sets] 不是被压缩的，终端性是真正的约束，而不是每个同态集合都是单例的结果。
*)
Theorem two_pick_distinct : two_pick true ≈ two_pick false → False.
Proof.
  intros Heq.
  exact (match Heq TwoX ttt with eq_refl => I end).
Qed.

Theorem two_sets_one_unique (F : _2 ⟶ Sets)
  (u v : F ~{[_2, Sets]}~> @terminal_obj ([_2, Sets]) Two_Sets_Terminal) :
  u ≈ v.
Proof. exact (@one_unique ([_2, Sets]) Two_Sets_Terminal F u v). Qed.

Definition Two_Sets_HasIndexedProducts : @HasIndexedProducts ([_2, Sets]) :=
  Fun_HasIndexedProducts Sets_HasIndexedProducts.

Definition two_bool_fam : bool → (_2 ⟶ Sets) := fun _ => Two_Bool.

Definition two_bool_prod : _2 ⟶ Sets :=
  @indexed_product ([_2, Sets]) Two_Sets_HasIndexedProducts bool two_bool_fam.

Example two_bool_prod_carrier :
  carrier (fobj[two_bool_prod] TwoX) = (∀ _ : bool, bool) := eq_refl.

Definition two_all_true : carrier (fobj[two_bool_prod] TwoX) :=
  fun _ => true.

Definition two_all_false : carrier (fobj[two_bool_prod] TwoX) :=
  fun _ => false.

(* The pointwise product does not collapse: it has at least two elements. / 逐点积不会塌缩：它至少有两个元素。 *)
Theorem two_bool_prod_separates : two_all_true ≈ two_all_false → False.
Proof.
  intros Heq.
  exact (match Heq true with eq_refl => I end).
Qed.

(* Its projections compute. / 它的预测正在计算。 *)
Example two_bool_proj_computes (b : bool) :
  transform
    (@indexed_product_proj ([_2, Sets]) Two_Sets_HasIndexedProducts
       bool two_bool_fam b) TwoX two_all_true = true := eq_refl.

(*
 The universal property is exercised, and its mediator COMPUTES.  The
 competing family is [two_pick], whose component at [b] picks [b]; the
 induced map into the product therefore sends [ttt] to the identity
 function on [bool]. 

 --------
 普遍性质被行使，其中介者进行计算。竞争的族是  [two_pick] ，其在  [b]  的分量选择了  [b] ；因此，诱导映射到积将  [ttt]  发送到  [bool]  上的恒等函数。
*)
Definition two_pick_family (b : bool) :
  @terminal_obj ([_2, Sets]) Two_Sets_Terminal ⟹ two_bool_fam b :=
  two_pick b.

Definition two_pick_med :
  @terminal_obj ([_2, Sets]) Two_Sets_Terminal ~{[_2, Sets]}~> two_bool_prod :=
  unique_obj
    (iprod_desc
       (@indexed_product_ump ([_2, Sets]) Two_Sets_HasIndexedProducts
          bool two_bool_fam)
       two_pick_family).

Example two_pick_med_true :
  transform two_pick_med TwoX ttt true = true := eq_refl.

Example two_pick_med_false :
  transform two_pick_med TwoX ttt false = false := eq_refl.

Theorem two_pick_med_commutes (b : bool) :
  @indexed_product_proj ([_2, Sets]) Two_Sets_HasIndexedProducts
    bool two_bool_fam b ∘ two_pick_med ≈ two_pick_family b.
Proof.
  exact (unique_property
           (iprod_desc
              (@indexed_product_ump ([_2, Sets]) Two_Sets_HasIndexedProducts
                 bool two_bool_fam)
              two_pick_family) b).
Qed.

(* * ** The nullary case: the terminal functor as an empty pointwise product / * ** 零元情况：作为空点积的终端函子 *)

Program Definition terminal_empty_IsIndexedProduct {C : Category}
  (T : @Terminal C) {A : Type} (Hempty : A → False) (f : A → C)
  (proj : ∀ a : A, @terminal_obj C T ~> f a) :
  IsIndexedProduct f (@terminal_obj C T) proj := {|
  iprod_desc := fun c pi => {| unique_obj := one |}
|}.
Next Obligation. destruct (Hempty a). Qed.
Next Obligation. apply one_unique. Qed.

(*
 Over an empty index the pointwise indexed product IS the terminal functor,
 canonically.  This is an isomorphism and nothing stronger: the empty
 [indexed_product] of [D] is whatever [HasIndexedProducts D] chose, and
 nothing forces that choice to be [terminal_obj]. 

 --------
 在空索引上，逐点索引的积在范畴论中是终极函子，这是自然的。这是一个同构，并没有更强的性质：[D] 的空 [indexed_product] 是 [HasIndexedProducts D] 所选择的任何东西，没有任何东西强制将该选择设为 [terminal_obj]。
*)
Definition Fun_empty_iprod_terminal {C D : Category}
  (HP : @HasIndexedProducts D) (T : @Terminal D)
  {A : Type} (Hempty : A → False) (F : A → (C ⟶ D)) :
  @Isomorphism ([C, D])
    (Fun_iprod HP F)
    (@terminal_obj ([C, D]) (Functor_Category_Terminal T)) :=
  @iprod_unique_iso ([C, D]) A F _ _ _ _
    (Fun_IsIndexedProduct HP F)
    (terminal_empty_IsIndexedProduct
       (Functor_Category_Terminal T) Hempty F
       (fun a => False_rect _ (Hempty a))).
