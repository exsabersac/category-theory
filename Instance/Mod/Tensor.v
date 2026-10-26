Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Universal.Element.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(*
 The global obligation tactic is [cat_simpl], which runs wide proof
 searches on module obligations and has already introduced the
 parameters by the time an obligation is opened.  Switched off here,
 the Instance/Mod.v idiom, so every obligation starts with an
 explicit [intros]. 

 --------
 全球义务策略是 [cat_simpl]，它对模块义务进行广泛的证明搜索，并且在义务被打开时已经引入了参数。在这里关闭，即 Instance/Mod.v 习语，因此每个义务以一个明确的 [intros] 开始。
*)
#[local] Obligation Tactic := idtac.

(*
   * * The tensor product of modules, as a universal element

   nLab:      https://ncatlab.org/nlab/show/tensor+product+of+modules
   nLab:      https://ncatlab.org/nlab/show/universal+element
   Wikipedia: https://en.wikipedia.org/wiki/Tensor_product_of_modules
   Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
   GTM 5, §III.1, printed p. 58 (the tensor product presented as a
   universal element of the functor of bilinear maps) —
   maclane:III.1:construction6
   Book: Riehl, Category Theory in Context, Dover 2016, §2.3, printed
   p. 58 (the same content as a representation: the functor
   carrying W to the set of bilinear maps V × V' → W is
   represented by V ⊗ V') — riehl:2.3:example8

   WHY THE TENSOR PRODUCT IS THE EXAMPLE.  A bilinear map is not a
   linear map, so the assignment W ↦ Bilin(V, V'; W) is visibly not a
   hom-functor; and yet it is naturally isomorphic to one.  That is the
   entire content of the tensor product, and it is why Mac Lane reaches
   for it immediately after defining universal elements: the reader
   already knows the object, and what the definition supplies is the
   reason it exists.  Bilinearity is a two-variable notion, linearity a
   one-variable notion, and V ⊗ V' is the object that converts the first
   into the second — “the” object, because a representing object is
   determined up to a unique compatible isomorphism, which is what makes
   the familiar identifications (associativity, commutativity, the unit
   law) theorems rather than choices.  The historical order was the
   reverse: the construction is nineteenth-century, the universal
   property is Bourbaki-era, and the observation that the property is
   what matters is exactly the observation category theory contributed.

   Elementwise the object is a quotient of formal expressions, and every
   calculation with tensors is a calculation modulo bilinearity.  That
   is what is built below: the carrier [MTerm] is a plain inductive of
   formal expressions, the equality [mt_eq] is an inductive relation
   closing under exactly the abelian-group laws, the four module laws,
   additivity in each variable, the two scalar rules on generators,
   congruence for each former, saturation under the point setoids and
   under the ring's own [≈], and symmetry and transitivity.
   Reflexivity is derived ([mt_refl]).  The presentation is
   Instance/Ab/Tensor.v's, extended with a scalar former in the manner
   of Instance/Mod/Free.v's [FVTerm], and it is a setoid quotient in the
   style of Instance/Sets/Coend.v: no free module is quotiented a second
   time.  That choice is discussed under GENERALITY below.

   WHAT IS DELIVERED

   * [RBilinear V V' W] — R-bilinear maps of modules: additive in each
   variable and commuting with the scalar action in each variable.
   Respectfulness is a field; preservation of zero and of negation in
   each variable is not, being derivable exactly as for the group case
   ([rbl_zero_l], [rbl_zero_r], [rbl_neg_l], [rbl_neg_r] below are
   those four derivations).

   * [Bilin V V' : RMod R ⟶ Sets] — the bilinear-maps FUNCTOR, not
   merely the type.  Its object part is the setoid of bilinear maps
   compared pointwise; its arrow part is postcomposition.  Both
   functor laws — identity and composition — hold pointwise by
   [reflexivity].  The other two obligations, [fmap_respects] and
   respectfulness of the arrow map itself, do not: each consumes its
   hypothesis.  (Four in all, RE-COUNTED from the [_obligation_] names
   [Print Module] lists after the PR “algebraic carriers are sets”
   (2026-09-17); unchanged, [cmon_prop] being supplied inline in the
   record literals rather than left to [Program].)

   * [TensorMod V V' : RModObject R] with the canonical bilinear map
   [tensor_gen : RBilinear V V' (TensorMod V V')] — the generator
   former itself.

   * THE HEADLINE: [tensor_universal_element], the statement that
   ⟨V ⊗ V', ⊗⟩ is a universal element of [Bilin V V'] in the sense of
   Theory/Universal/Element.v's [AUniversalElement], together with
   [tensor_UniversalElement], the same data in the bundled
   [UniversalElement] form (Mac Lane's pair ⟨r, e⟩).  Unique
   factorization is then the class's own [aue_universal]; it is
   restated elementwise as [tensor_factor] with
   [tensor_factor_commutes] and [tensor_factor_unique], for readers
   who want the equation f = f̄ ∘ ⊗ without unfolding the class.
   Nothing is reproved there: [tensor_factor_is_med] records by
   [eq_refl] that the mediator extracted from the class IS the
   fixpoint below.

   * The engine room: [tensor_med] (the factorizing homomorphism, whose
   underlying map is the [Fixpoint] [tensor_med_fun], so it COMPUTES —
   and so preservation of zero, of addition and of the action all hold
   by [reflexivity]), [tensor_hom_ext] (two homomorphisms out of the
   tensor agreeing on generators agree — the uniqueness half, and the
   workhorse), and the elementary consequences [tensor_zero_l],
   [tensor_zero_r], [tensor_neg_l], [tensor_neg_r], [tensor_balanced].

   * Non-degeneracy over ℤ, which is where the construction is measured
   rather than described: [Int_mul_bilinear] is multiplication as a
   bilinear map, the factorization of it through the tensor COMPUTES
   on closed generators ([int_tensor_med_computes], by [eq_refl]),
   two generators that ought to differ do ([int_tensor_gen_distinct]:
   1 ⊗ 1 is not 2 ⊗ 1), the canonical map is not the zero map
   ([int_tensor_gen_nonzero]: 1 ⊗ 1 is not 0), and
   the whole object is pinned: [Int_tensor_iso] is an isomorphism
   ℤ ⊗_ℤ ℤ ≅ ℤ in [RMod Int_Ring].

   GENERALITY, AND WHAT IT COSTS

   The construction and the universal property are stated over an
   ARBITRARY [RingObject], and commutativity of R is a hypothesis of none
   of them: it appears in neither [RBilinear], [TensorMod], [Bilin],
   [tensor_med], [tensor_hom_ext] nor [tensor_universal_element].  (The
   one general statement below that DOES assume it is
   [rbl_commutator_from_commutativity], which exists precisely to
   measure what the absence is worth, and the ℤ witnesses of course use
   ℤ's own commutativity.)

   That is a fact about the statements, and it must not be read as a
   strengthening of the classical theorem.  It is the opposite: the
   universal property holds unconditionally because the object
   constructed here satisfies MORE relations over a non-commutative ring
   than a reader of the commutative case would expect — the identity
   below is imposed on it, and nothing here says the resulting object is
   the classical one.  What gains relations is the OBJECT; the
   universal property itself is unchanged.  How much is thereby lost is
   NOT measured: see the deferral below, which records that the identity
   is never exhibited as non-vacuous at a concrete ring.

   Precisely — and this is proved, not argued: [rbl_commutator] shows
   that for EVERY R-bilinear β into ANY R-module,

   (r·s) · β(v, v')  ≈  (s·r) · β(v, v')

   since both sides equal β(r·v, s·v'); written with subtraction
   ([rbl_commutator_annihilates]) that says every commutator of R
   annihilates the image of every bilinear map.  [tensor_commutator] is
   that identity at the tensor itself, where it says that V ⊗ V' is a
   module on which the commutators of R act as zero.  Over a commutative
   ring the identity is empty, and that is also proved rather than
   asserted: [rbl_commutator_from_commutativity] derives the same
   conclusion from commutativity of R ALONE, using no bilinearity and no
   module beyond respectfulness of the action.  So the correct reading is
   that the hypothesis is absent because the object absorbs it, not that
   the theorem has been strengthened by removing it.
   Over a commutative ring — hence over a field, which is the case both
   catalogued sources state — [TensorMod] is the classical tensor
   product of modules, presented by exactly the classical generators and
   relations.

   ONE DEFERRAL BELONGS HERE.  The collapse is proved as a general
   identity and is NOT witnessed at a concrete non-commutative ring,
   because the tree has none: the only closed [RingObject]s in it are
   [Int_Ring], [Q_Ring], [Zero_Ring], [F2_Ring], [FracRing] and
   [CRingOb], all commutative; [EndRig] produces a rig rather than a
   ring, and no endomorphism-RING construction exists.  (Two
   [RingObject]-valued FORMERS also exist — [Ring_op] and [field_ring] —
   but neither can introduce non-commutativity from these inputs, the
   opposite of a commutative ring being commutative and a field being
   commutative by definition.)  So no claim is made here that
   the collapse is ever strict — only that it holds, and that it is
   vacuous wherever R is commutative.  (The converse of that last
   implication is not proved and is not true as stated: over any ring
   the identity is also vacuous when the modules are trivial.)

   WHAT WAS ALREADY IN THE TREE, since issue #306 says otherwise.  The
   issue's “Current state” reads “Absent … `rg 'bilinear|Bilin'` finds
   only prose … there is no category of vector spaces or modules … no
   bilinear-map type, and no tensor-product-by-universal-property
   construction”.  Measured against this file's parent, that is wrong on
   every count but the last two words: [Record Bilinear (K : AbObject)]
   is at Instance/Ab/Tensor.v, with [tensor_ump], [tensor_hom_ext],
   [AbTensor] and [AbTensor_Functor] beside it, and [tensor_ump] is
   CONSUMED at Construction/Enriched/Ab.v — so a bilinear-map type
   and a tensor-by-universal-property already existed for abelian
   groups.  Instance/Mod.v, Instance/Ab.v and Instance/Rng.v all exist,
   and [Vct_F] is at Instance/FdVect.v.  Nothing of that is rebuilt
   here.  What was genuinely absent, and is what this file supplies, is
   the module-level bilinear map over an arbitrary ring, the bilinear
   functor into [Sets], the tensor object, and the universal element.

   NAME OVERLAP WITH Instance/Ab/Tensor.v, recorded rather than
   renamed.  Four names are declared in both files — [tensor_gen],
   [tensor_hom_ext], [tensor_med_fun] and [tensor_med_respects].  No
   code is shared (this file does not [Require] that one, and only the
   design pattern is borrowed), and nothing in the tree imports both, so
   nothing is shadowed today; the overlap is recorded here because it is
   a hazard for any future file that wants both.  Instance/FdVect/Tensor.v
   ([TensorSq], the diagonal square endofunctor) shares no name with
   this file at all.

   WHAT IS NOT DELIVERED

   * NOT the balanced tensor product.  For a RIGHT module V and a LEFT
   module V' over a non-commutative ring the standard object is the
   abelian group V ⊗_R V' universal among BALANCED maps
   (β(v·r, v') ≈ β(v, r·v')), which is a different universal property
   into a different category ([Ab], not [RMod R]) and would have the
   universal element living somewhere other than where V and V' do.
   Neither catalogued source states that version, and Instance/Mod.v's
   [ModR]/[Bimodule] are left untouched by this file.  Note that
   balancedness is nevertheless AVAILABLE here as a consequence:
   [tensor_balanced] proves (r·v) ⊗ v' ≈ v ⊗ (r·v') in [TensorMod],
   which is what makes the canonical map bilinear in the two-sided
   sense at all.

   * NO BIFUNCTORIALITY.  Instance/Ab/Tensor.v's [AbTensor_Functor]
   has no counterpart here: nothing below makes ⊗ a functor
   [RMod R ∏ RMod R ⟶ RMod R], and no monoidal structure on [RMod R]
   is attempted.  (Both would be [tensor_hom_ext] plus computations on
   generators, exactly as there.)

   * NO COEFFICIENT UNIQUENESS, and no basis theory.  As in
   Instance/Mod/Free.v, the presentation is by generators and
   relations, so an element of V ⊗ V' is a formal expression up to the
   congruence and NOT a normal form; nothing here proves that a tensor
   has a unique expression as a sum of simple tensors, which is false
   in general anyway.

   * NO COMPARISON WITH Instance/Ab/Tensor.v.  Over R = ℤ the two
   constructions have the same universal property, but no
   isomorphism between [AbTensor] and [TensorMod] is stated or proved
   here.  An earlier revision added “the ℤ-module structure of an
   [AbObject] is not in the tree”; since #454 it is, as
   Instance/Mod/Cogenerator.v's [Ab_to_ZMod] (through [zsmul]), and no
   comparison of the two tensors is built on it.

   * NO RELATION TO Instance/FdVect/Tensor.v, which despite its name is
   the diagonal square endofunctor V ↦ StdVect F (n²) of Riehl
   Ex 1.4.4(vii) and not a tensor product of two modules at all. 

   --------
   * * 模的张量积，作为一个普遍元素

   nLab:       https://ncatlab.org/nlab/show/tensor+product+of+modules 
   nLab:       https://ncatlab.org/nlab/show/universal+element 
   Wikipedia:  https://en.wikipedia.org/wiki/Tensor_product_of_modules 
   书籍: Mac Lane, 《为在职数学家准备的范畴论》，第二版，
   GTM 5, §III.1, 印刷页 58（张量积作为双线性映射函子的一
   个普遍元素呈现）—— maclane:III.1:construction6
   书籍: Riehl, 《情境中的范畴论》，Dover 2016, §2.3, 印刷
   页 58（相同内容作为表示：将 W 映射到双线性映射集合 V × V' → W 的函子由 V ⊗ V' 表示）—— riehl:2.3:example8为什么张量积是例子。一个双线性映射不是线性映射，因此赋值 W ↦ Bilin(V, V'; W) 显然不是一个函子；然而，它自然同构于一个函子。这就是张量积的全部内容，这也是为什么在定义了泛元素之后，Mac Lane 立即引用它：读者已经知道这个对象，而定义提供的是它存在的理由。双线性是一个双变量的概念，线性是一个单变量的概念，而 V ⊗ V' 是将前者转换为后者的对象——“那个”对象，因为一个代表对象是由唯一的兼容同构决定的，这也正是使得熟悉的恒等式（结合律、交换律、单位律）成为定理而非选择的原因。历史顺序是相反的：构造是十九世纪的，泛性质是布尔巴基时期的，而观察到性质才是重要的正是范畴论所贡献的观察。从元素的角度来看，该对象是形式表达式的商，每一个张量的计算都是模双线性计算。这就是下面构建的内容：承载体  [MTerm]  是形式表达式的普通归纳类型，等式  [mt_eq]  是一个归纳关系，完全遵循阿贝尔群定律、四个模定律、每个变量的可加性、生成元的两个标量规则、每个前者的一致性、在点集合下饱和以及在环自身的  [≈] 下饱和，并且具有对称性和传递性。自反性是导出的 ( [mt_refl] )。该演示文稿是 Instance/Ab/Tensor.v 的扩展，其通过类似 Instance/Mod/Free.v 的方式添加了一个标量形式 [FVTerm]，并且它是 Instance/Sets/Coend.v 风格的集合等价类商：没有自由模被第二次商化。这个选择在下文的“通用性”部分中讨论。

   交付物

   * [RBilinear V V' W] — 模的 R-双线性映射：在每个变量中都是可加的，并与每个变量中的标量作用交换。可敬性是一个字段；每个变量中零元和取负的保持性不是字段，因为它们可以像群的情况一样推导出来（下文 [rbl_zero_l]、[rbl_zero_r]、[rbl_neg_l]、[rbl_neg_r] 是这四个推导）。*  [Bilin V V' : RMod R ⟶ Sets] — 双线性映射函子，而不仅仅是类型。它的对象部分是按点比较的双线性映射等价集合；它的箭头部分是后组合。两个函子律——恒等和组合——都按照 [reflexivity] 在点上成立。其他两个义务，[fmap_respects] 和箭头映射本身的可敬性，则不成立：每个都消耗其假设。（总共四个，从 [_obligation_] 名称 [Print Module] 在 PR “代数载体是集合” (2026-09-17) 后列出的列表重新计数；保持不变，[cmon_prop] 在记录字面量中内联提供，而不是留给 [Program]。）

   *  [TensorMod V V' : RModObject R] 及其标准双线性映射 [tensor_gen : RBilinear V V' (TensorMod V V')] — 生成器本身的前身。* 标题:  [tensor_universal_element]，即关于 ⟨V ⊗ V', ⊗⟩ 是 [Bilin V V'] 的一个通用元素的声明，这里 [Bilin V V'] 的意义来自 Theory/Universal/Element.v 的 [AUniversalElement]，同时 [tensor_UniversalElement] 是以捆绑的 [UniversalElement] 形式表示的相同数据（Mac Lane 的对 ⟨r, e⟩）。唯一分解随后就是该类自身的 [aue_universal]；它以元素形式重新表述为 [tensor_factor]，配合 [tensor_factor_commutes] 和 [tensor_factor_unique]，供希望在不展开类的情况下得到方程 f = f̄ ∘ ⊗ 的读者使用。那里没有重新证明任何东西：[tensor_factor_is_med] 通过 [eq_refl] 记录了从类中提取的中介确实是下面的固定点。* 发动机房：[tensor_med]（因式分解同态，其基础映射为[Fixpoint] [tensor_med_fun]，因此它进行计算——并且零的保持、加法的保持以及作用的保持都通过[reflexivity] 成立）、[tensor_hom_ext]（从张量出的两个同态在生成元上相同——唯一性部分，以及主要工作部分），以及基本结果[tensor_zero_l]、[tensor_zero_r]、[tensor_neg_l]、[tensor_neg_r]、[tensor_balanced]。* 在ℤ上的非退化性，这是构造被衡量而非描述的地方：[Int_mul_bilinear] 是作为双线性映射的乘法，它通过张量的分解在闭生成元上进行计算（[int_tensor_med_computes]，通过 [eq_refl]），两个本应不同的生成元确实不同（[int_tensor_gen_distinct]：1 ⊗ 1 不是 2 ⊗ 1），典范映射不是零映射（[int_tensor_gen_nonzero]：1 ⊗ 1 不是 0），整个对象是固定的：[Int_tensor_iso] 是同构 ℤ ⊗_ℤ ℤ ≅ ℤ 在 [RMod Int_Ring] 中。

   一般性及其代价构造和泛性质是在一个任意的 [RingObject] 上陈述的，而且 R 的交换性不是它们的任何假设：它既不出现在 [RBilinear]、[TensorMod]、[Bilin]、[tensor_med]、[tensor_hom_ext] 也不出现在 [tensor_universal_element]。（下面唯一一个确实假设它的一般陈述是 [rbl_commutator_from_commutativity]，它的存在正是为了衡量缺失的价值，而且 ℤ 的证据当然使用了 ℤ 自身的交换性。）这是关于这些陈述的一个事实，而且不能被解读为对经典定理的加强。恰恰相反：因为这里构造的对象在非交换环上满足的关系比读者在交换情形下预期的更多，所以它的泛性质是无条件成立的——下面的恒等式被强加于它，而这里没有任何内容表明由此得到的对象是经典对象。获得更多关系的是对象本身；泛性质本身没有改变。由此失去多少没有被衡量：见下文的延期说明，它记录了该恒等式从未在具体环上表现为非平凡。

   确切地说——而这是被证明的，而非争论的：[rbl_commutator] 表明，对于每一个 R-双线性 β 进入任意 R-模，(r·s) · β(v, v')  ≈  (s·r) · β(v, v')由于两边都等于 β(r·v, s·v')；用减法写作 ([rbl_commutator_annihilates])，它表示 R 的每个对易子都消去每个双线性映射的像。[tensor_commutator] 是在张量本身上的恒等式，它表示 V ⊗ V' 是一个模块，在其中 R 的对易子作用为零。在一个交换环上，该恒等式是空的，这也是被证明的而不是被断言的：[rbl_commutator_from_commutativity] 仅利用 R 的交换性就得出相同的结论，没有使用任何双线性性，也没有超出作用的尊重之外的模块。因此，正确的理解是，假设的缺失是因为对象吸收了它，而不是定理通过移除假设而被加强。在交换环上——因此在域上，这是两个已列出的来源都说明的情况——[TensorMod]是模的经典张量积，由完全经典的生成元和关系表示。这里属于一个延迟。坍塌被证明为一般恒等式，并未在具体的非交换环中被观察到，因为该树中没有：其中唯一封闭的 [RingObject] 是 [Int_Ring]、[Q_Ring]、[Zero_Ring]、[F2_Ring]、[FracRing] 和 [CRingOb]，都是交换的；[EndRig] 生成的是一个幺半环而不是环，而且不存在端同态-环构造。（还存在两个 [RingObject] 值的 FORMER——[Ring_op] 和 [field_ring]——但它们都不能从这些输入引入非交换性，而一个交换环的相反性质是交换的，域的定义也是交换的。）因此此处并未声称坍塌在任何情况下是严格的——仅声称它成立，并且在 R 交换的地方是空泛的。（最后一个推论的逆命题没有被证明，并且按所述并不成立：在任意环上，当模是平凡的时候，恒等式也是无效的。）树中已经存在的内容，因为第306期指出情况并非如此。该期刊的“当前状态”写着“缺失……`rg 'bilinear|Bilin'` 只发现了散文……没有向量空间或模范畴……没有双线性映射类型，也没有通过普遍性质构造的张量积”。与此文件的父级相比，这在所有方面都是错误的，除了最后两个词：[Record Bilinear (K : AbObject)] 在 Instance/Ab/Tensor.v 中，旁边有 [tensor_ump]、[tensor_hom_ext]、[AbTensor] 和 [AbTensor_Functor]，而 [tensor_ump] 已在 Construction/Enriched/Ab.v 中使用——因此阿贝尔群已经存在双线性映射类型和通过普遍性质构造的张量积。Instance/Mod.v、Instance/Ab.v 和 Instance/Rng.v 都存在，[Vct_F] 在 Instance/FdVect.v。这里没有重新构建这些内容。真正缺失的，也是这个文件提供的，是任意环上的模块级双线性映射、到 [Sets] 的双线性函子、张量对象以及通用元素。

   与 Instance/Ab/Tensor.v 的名称重叠，记录而非重命名。两个文件中声明了四个相同的名称——[tensor_gen]、[tensor_hom_ext]、[tensor_med_fun] 和 [tensor_med_respects]。没有共享代码（这个文件不 [Require] 那个文件，仅借用了设计模式），树结构中没有任何东西同时导入两个文件，因此今天没有被遮蔽；在这里记录重叠是因为它对未来任何想同时使用两个文件的文件都是一个潜在风险。Instance/FdVect/Tensor.v（[TensorSq]，对角平方自函子）与这个文件完全没有共享名称。

   未提供的内容* 不是平衡张量积。对于非交换环上的右模 V 和左模 V'，标准对象是阿贝尔群 V ⊗_R V'，它在平衡映射（β(v·r, v') ≈ β(v, r·v')）中是通用的，这具有不同的通用性质，属于不同的范畴（[Ab]，而不是 [RMod R]），其通用元素会存在于除了 V 和 V' 之外的某个位置。这种版本在任何已编目的来源中都没有说明，并且 Instance/Mod.v 的 [ModR] / [Bimodule] 也不受此文件影响。注意，平衡性在此仍然是可用的作为结果：[tensor_balanced] 证明了 (r·v) ⊗ v' ≈ v ⊗ (r·v') 在 [TensorMod] 中成立，这正是使得典范映射在双边意义上是双线性的原因。* 没有双函子性。 Instance/Ab/Tensor.v 的 [AbTensor_Functor] 在这里没有对应部分：下面没有任何内容使 ⊗ 成为函子 [RMod R ∏ RMod R ⟶ RMod R]，也没有尝试在 [RMod R] 上建立幺半群结构。（两者都会是 [tensor_hom_ext] 加上生成元的计算，就像那里一样。）

   * 没有系数唯一性，也没有基理论。正如在 Instance/Mod/Free.v 中一样，这里的表示方法是通过生成元和关系，所以 V ⊗ V' 的元素是模同余的形式表达，而不是规范形式；这里没有证明张量能够唯一表示为简单张量的和，而且在一般情况下这也是不成立的。* 不与 Instance/Ab/Tensor.v 比较。在 R = ℤ 上，这两个构造具有相同的泛性质，但这里没有声明或证明 [AbTensor] 与 [TensorMod] 之间的同构关系。早期的修订版添加了“[AbObject] 的 ℤ-模结构不在树中”；自 #454 起，它确实存在，如 Instance/Mod/Cogenerator.v 的 [Ab_to_ZMod]（通过 [zsmul]），并且没有基于它来比较两个张量。

   * 不与 Instance/FdVect/Tensor.v 有关，尽管名称如此，它实际上是 Riehl Ex 1.4.4(vii) 中的对角平方自函子 V ↦ StdVect F (n²)，根本不是两个模的张量积。
*)

(** ** Bilinear maps / ** 双线性映射 *)

Section Bilinear.

Context (R : RingObject).
Context (V V' : RModObject R).

(*
   * An R-bilinear map into an R-module W: respectful in each variable,
   additive in each variable, and commuting with the scalar action in
   each variable.  Preservation of zero and of negation in each variable
   is derived below rather than demanded, as always for maps between
   groups. 

   --------
   * 映射到 R-模 W 的 R-双线性映射：在每个变量中都是线性的，对每个变量是可加的，并且与每个变量中的标量作用交换。 对每个变量中零元素和取反的保持性下面推导而来，而不是直接要求，就像群之间的映射一样。
*)
Record RBilinear (W : RModObject R) := {
  rbl_map : carrier (cmon_setoid V) →
            carrier (cmon_setoid V') → carrier (cmon_setoid W);

  rbl_respects : Proper (equiv ==> equiv ==> equiv) rbl_map;

  (* (v + v') ⊗ w = v ⊗ w + v' ⊗ w *)
  rbl_add_l (v v' : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
    rbl_map (cmon_plus V v v') w
      ≈ cmon_plus W (rbl_map v w) (rbl_map v' w);
  (* v ⊗ (w + w') = v ⊗ w + v ⊗ w' *)
  rbl_add_r (v : carrier (cmon_setoid V)) (w w' : carrier (cmon_setoid V')) :
    rbl_map v (cmon_plus V' w w')
      ≈ cmon_plus W (rbl_map v w) (rbl_map v w');
  (* (r·v) ⊗ w = r·(v ⊗ w) *)
  rbl_smul_l (r : carrier (rig_setoid (ring_rig R)))
             (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
    rbl_map (rm_smul V r v) w ≈ rm_smul W r (rbl_map v w);
  (* v ⊗ (r·w) = r·(v ⊗ w) *)
  rbl_smul_r (r : carrier (rig_setoid (ring_rig R)))
             (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
    rbl_map v (rm_smul V' r w) ≈ rm_smul W r (rbl_map v w)
}.

End Bilinear.

Arguments RBilinear {R} V V' W.
Arguments rbl_map {R V V' W} _ _ _.
Arguments rbl_respects {R V V' W} _.
Arguments rbl_add_l {R V V' W} _ _ _ _.
Arguments rbl_add_r {R V V' W} _ _ _ _.
Arguments rbl_smul_l {R V V' W} _ _ _ _.
Arguments rbl_smul_r {R V V' W} _ _ _ _.

#[export] Existing Instance rbl_respects.

Section BilinearFacts.

Context {R : RingObject}.
Context {V V' W : RModObject R}.
Context (β : RBilinear V V' W).

(*
   * 0 ⊗ w ≈ 0, by cancelling [0 ⊗ w] against itself — the argument of
   Instance/Mod.v's [rm_smul_zero_l], one level up. 

   --------
   * 0 ⊗ w ≈ 0，通过将 [0 ⊗ w] 对自身进行抵消 —— 这是 Instance/Mod.v 中 [rm_smul_zero_l] 的参数，上升一层。
*)
Lemma rbl_zero_l (w : carrier (cmon_setoid V')) :
  rbl_map β (cmon_zero V) w ≈ cmon_zero W.
Proof.
  apply (ab_cancel_l W (rbl_map β (cmon_zero V) w)).
  rewrite <- (rbl_add_l β (cmon_zero V) (cmon_zero V) w).
  rewrite (cmon_plus_zero_l V (cmon_zero V)).
  symmetry.
  apply (cmon_plus_zero_r W (rbl_map β (cmon_zero V) w)).
Qed.

(** v ⊗ 0 ≈ 0, dually. *)
Lemma rbl_zero_r (v : carrier (cmon_setoid V)) :
  rbl_map β v (cmon_zero V') ≈ cmon_zero W.
Proof.
  apply (ab_cancel_l W (rbl_map β v (cmon_zero V'))).
  rewrite <- (rbl_add_r β v (cmon_zero V') (cmon_zero V')).
  rewrite (cmon_plus_zero_l V' (cmon_zero V')).
  symmetry.
  apply (cmon_plus_zero_r W (rbl_map β v (cmon_zero V'))).
Qed.

(*
   * (−v) ⊗ w ≈ −(v ⊗ w): the left-hand side IS an additive inverse of
   v ⊗ w, and Instance/Ab.v's [ab_neg_unique] says that is enough. 

   --------
   * (−v) ⊗ w ≈ −(v ⊗ w)：左边是 v ⊗ w 的加法逆元，而 Instance/Ab.v 的 [ab_neg_unique] 说这已经足够了。
*)
Lemma rbl_neg_l (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  rbl_map β (ab_neg V v) w ≈ ab_neg W (rbl_map β v w).
Proof.
  apply ab_neg_unique.
  rewrite <- (rbl_add_l β (ab_neg V v) v w).
  rewrite (ab_neg_left V v).
  apply rbl_zero_l.
Qed.

Lemma rbl_neg_r (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  rbl_map β v (ab_neg V' w) ≈ ab_neg W (rbl_map β v w).
Proof.
  apply ab_neg_unique.
  rewrite <- (rbl_add_r β v (ab_neg V' w) w).
  rewrite (ab_neg_left V' w).
  apply rbl_zero_r.
Qed.

(*
   * THE COMMUTATOR IDENTITY, and the reason the construction below needs
   no commutativity hypothesis.  Both sides are β(r·v, s·w): the left by
   peeling r off the first variable and s off the second, the right by
   peeling them off in the other order.  Stated with subtraction it says
   that every commutator of R annihilates the image of every bilinear
   map ([rbl_commutator_annihilates]), and over a non-commutative ring
   that is a genuine collapse — see the header, and
   [rbl_commutator_from_commutativity] for the proof that the identity
   says nothing when R is commutative. 

   --------
   * 交换子恒等式，以及下面的构造为何不需要交换性假设的原因。两边都是 β(r·v, s·w)：左边通过从第一个变量中剥离 r，从第二个变量中剥离 s，右边则以相反的顺序剥离它们。用减法表述时，它表示 R 的每个交换子都会消去每个双线性映射 ([rbl_commutator_annihilates]) 的像，而在非交换环上，这确实是一种真正的崩塌——参见标题，以及 [rbl_commutator_from_commutativity] 中关于该恒等式在 R 可交换时不产生任何意义的证明。
*)
Lemma rbl_commutator (r s : carrier (rig_setoid (ring_rig R)))
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  rm_smul W (rig_mul (ring_rig R) r s) (rbl_map β v w)
    ≈ rm_smul W (rig_mul (ring_rig R) s r) (rbl_map β v w).
Proof.
  transitivity (rbl_map β (rm_smul V r v) (rm_smul V' s w)).
  - rewrite (rm_smul_assoc W r s (rbl_map β v w)).
    rewrite <- (rbl_smul_r β s v w).
    symmetry; apply (rbl_smul_l β r v (rm_smul V' s w)).
  - rewrite (rm_smul_assoc W s r (rbl_map β v w)).
    rewrite <- (rbl_smul_l β r v w).
    apply (rbl_smul_r β s (rm_smul V r v) w).
Qed.

(*
   * The same identity written with subtraction: the commutator
   r·s − s·r acts as zero on every value of β.  This is the form the
   header's word “annihilates” refers to; it needs the ambient module's
   negation, which is why it is stated here and not for rigs. 

   --------
   * 用减法写出的相同恒等式：对易子
   r·s − s·r 在 β 的每个取值上都表现为零。这就是标题中“湮灭”一词所指的形式；它需要环境模的取负，这就是为什么这里说明而在幺半环中没有说明的原因。
*)
Lemma rbl_commutator_annihilates (r s : carrier (rig_setoid (ring_rig R)))
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  rm_smul W (rig_add (ring_rig R) (rig_mul (ring_rig R) r s)
               (ring_neg R (rig_mul (ring_rig R) s r)))
    (rbl_map β v w)
    ≈ cmon_zero W.
Proof.
  rewrite (rm_smul_distr_r W _ _ (rbl_map β v w)).
  rewrite (rm_smul_neg_l W (rig_mul (ring_rig R) s r) (rbl_map β v w)).
  rewrite (rbl_commutator r s v w).
  apply (ab_neg_right W).
Qed.

End BilinearFacts.

(*
   * The other direction, measuring what [rbl_commutator] is worth: over a
   commutative ring its conclusion follows from commutativity alone —
   no bilinear map, no additivity, nothing but respectfulness of the
   action.  So the identity is informative only where R is
   non-commutative, which is exactly where it is a collapse. 

   --------
   * 另一个方向，衡量 [rbl_commutator] 的价值：在交换环上，它的结论仅仅依靠交换性即可得出——不需要双线性映射，不需要可加性，除了作用的相容性之外什么都不需要。因此，该恒等式只有在 R 是非交换的情况下才有启发性，这正是它发生崩溃的地方。
*)
Lemma rbl_commutator_from_commutativity {R : RingObject}
  (Rcomm : ∀ a b, rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a)
  (W : RModObject R) (r s : carrier (rig_setoid (ring_rig R)))
  (x : carrier (cmon_setoid W)) :
  rm_smul W (rig_mul (ring_rig R) r s) x
    ≈ rm_smul W (rig_mul (ring_rig R) s r) x.
Proof.
  now rewrite (Rcomm r s).
Qed.

(*
   * ** The tensor product

   Formal expressions in the two carriers, with zero, sum, negation and
   a formal scalar action; the equality is generated by exactly the laws
   the object must satisfy.  Nothing below is proved by hand: every
   module law of [TensorMod] is a constructor of [mt_eq], and so is
   every clause of bilinearity of the canonical map. 

   --------
   * ** 张量积

   在两个载体中的形式表达式，具有零、加法、取负和形式标量作用；等式完全由对象必须满足的定律生成。下面没有任何内容是手工证明的：  [TensorMod]  的每一条模律都是  [mt_eq]  的构造器，典范映射的双线性每一条条款也是如此。
*)

Section Tensor.

Context {R : RingObject}.
Context (V V' : RModObject R).

Inductive MTerm : Type :=
  | mt_gen  : carrier (cmon_setoid V) → carrier (cmon_setoid V') → MTerm
  | mt_zero : MTerm
  | mt_plus : MTerm → MTerm → MTerm
  | mt_neg  : MTerm → MTerm
  | mt_smul : carrier (rig_setoid (ring_rig R)) → MTerm → MTerm.

(*
 The quotienting relation.  Congruence for each former (saturating
 under the two point setoids and under the ring's own [≈]), the
 abelian-group laws, the four module laws, additivity of the generator
 former in each variable, and the two rules that make the formal scalar
 action agree with the actions of V and of V' on a generator.
 Reflexivity is derived ([mt_refl]), keeping the induction principle
 one case shorter everywhere it is consumed. 

 --------
 商化关系。对每一个前体的同余（在两点集体下以及在环自身的 [≈] 下饱和），阿贝尔群法则，四条模法则，每个变量中生成元前体的加性，以及使形式标量作用与 V 和 V' 在生成元上的作用一致的两条规则。自反性是推导出来的（[mt_refl]），在每处使用时保持归纳原理少一个情形。
*)
Inductive mt_eq : MTerm → MTerm → Prop :=
  (* congruence / 全等 *)
  | mte_gen {v v' : carrier (cmon_setoid V)} {w w' : carrier (cmon_setoid V')} :
      v ≈ v' → w ≈ w' → mt_eq (mt_gen v w) (mt_gen v' w')
  | mte_plus {s s' t t'} :
      mt_eq s s' → mt_eq t t' → mt_eq (mt_plus s t) (mt_plus s' t')
  | mte_neg {s s'} : mt_eq s s' → mt_eq (mt_neg s) (mt_neg s')
  | mte_smul {r r' : carrier (rig_setoid (ring_rig R))} {s s'} :
      r ≈ r' → mt_eq s s' → mt_eq (mt_smul r s) (mt_smul r' s')

  (* abelian group / 阿贝尔群 *)
  | mte_assoc (s t u : MTerm) :
      mt_eq (mt_plus (mt_plus s t) u) (mt_plus s (mt_plus t u))
  | mte_comm (s t : MTerm) : mt_eq (mt_plus s t) (mt_plus t s)
  | mte_zero_l (s : MTerm) : mt_eq (mt_plus mt_zero s) s
  | mte_neg_l (s : MTerm) : mt_eq (mt_plus (mt_neg s) s) mt_zero

  (* module *)
  | mte_smul_distr_l (r : carrier (rig_setoid (ring_rig R))) (s t : MTerm) :
      mt_eq (mt_smul r (mt_plus s t)) (mt_plus (mt_smul r s) (mt_smul r t))
  | mte_smul_distr_r (r r' : carrier (rig_setoid (ring_rig R))) (s : MTerm) :
      mt_eq (mt_smul (rig_add (ring_rig R) r r') s)
            (mt_plus (mt_smul r s) (mt_smul r' s))
  | mte_smul_assoc (r r' : carrier (rig_setoid (ring_rig R))) (s : MTerm) :
      mt_eq (mt_smul (rig_mul (ring_rig R) r r') s)
            (mt_smul r (mt_smul r' s))
  | mte_smul_one (s : MTerm) :
      mt_eq (mt_smul (rig_one (ring_rig R)) s) s

  (* bilinearity: additivity in each variable / 双线性：每个变量的可加性 *)
  | mte_add_l (v v' : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
      mt_eq (mt_gen (cmon_plus V v v') w)
            (mt_plus (mt_gen v w) (mt_gen v' w))
  | mte_add_r (v : carrier (cmon_setoid V)) (w w' : carrier (cmon_setoid V')) :
      mt_eq (mt_gen v (cmon_plus V' w w'))
            (mt_plus (mt_gen v w) (mt_gen v w'))

  (* bilinearity: the scalar action, on each variable / 双线性：每个变量的标量作用 *)
  | mte_act_l (r : carrier (rig_setoid (ring_rig R)))
              (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
      mt_eq (mt_smul r (mt_gen v w)) (mt_gen (rm_smul V r v) w)
  | mte_act_r (r : carrier (rig_setoid (ring_rig R)))
              (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
      mt_eq (mt_smul r (mt_gen v w)) (mt_gen v (rm_smul V' r w))

  | mte_sym {s t} : mt_eq s t → mt_eq t s
  | mte_trans {s t u} : mt_eq s t → mt_eq t u → mt_eq s u.

Lemma mt_refl (s : MTerm) : mt_eq s s.
Proof.
  induction s.
  - exact (mte_gen (reflexivity _) (reflexivity _)).
  - exact (mte_trans (mte_sym (mte_zero_l mt_zero)) (mte_zero_l mt_zero)).
  - exact (mte_plus IHs1 IHs2).
  - exact (mte_neg IHs).
  - exact (mte_smul (reflexivity _) IHs).
Qed.

Lemma mt_eq_Equivalence : Equivalence mt_eq.
Proof.
  constructor.
  - exact mt_refl.
  - exact (fun s t => mte_sym).
  - exact (fun s t u => mte_trans).
Qed.

Definition mt_Setoid : Setoid MTerm := {|
  equiv        := mt_eq;
  setoid_equiv := mt_eq_Equivalence
|}.

(*
   * The tensor product as an object of [RMod R].  Every law is a
   constructor; nothing is proved.  An earlier revision stopped there; the record now
   carries one more field, [cmon_prop], and it too is a one-liner: the
   relation IS a [Prop] since the PR “algebraic carriers are sets”
   (2026-09-17), so it is its own [Prop] mirror and both implications are
   the identity. 

   --------
   * 张量积作为 [RMod R] 的对象。每条定律都是一个构造子；没有任何东西被证明。早期的修订停在这里；现在的记录多了一个字段 [cmon_prop]，它同样是一行代码：该关系是一个 [Prop]，因为 PR “代数承载体是集合”（2026-09-17），所以它是自身的 [Prop] 镜像，并且两个蕴含都是恒等的。
*)
Definition TensorMod : RModObject R := {|
  rm_ab := {|
    ab_cmon := {|
      cmon_setoid := {| carrier := MTerm; is_setoid := mt_Setoid |};
      cmon_zero := mt_zero;
      cmon_plus := mt_plus;
      cmon_plus_respects := fun _ _ Hs _ _ Ht => mte_plus Hs Ht;
      cmon_plus_assoc := mte_assoc;
      cmon_plus_comm := mte_comm;
      cmon_plus_zero_l := mte_zero_l;
      (* [mt_eq] IS a [Prop] relation, so it is its own [Prop] mirror. / [mt_eq] 是一个 [Prop] 关系，因此它是它自己的 [Prop] 镜像。 *)
      cmon_prop := @PropEquiv_of_relation _ mt_Setoid mt_eq
                     (fun _ _ h => h) (fun _ _ h => h)
    |};
    ab_neg := mt_neg;
    ab_neg_respects := fun _ _ Hs => mte_neg Hs;
    ab_neg_left := mte_neg_l
  |};
  rm_smul          := mt_smul;
  rm_smul_respects := fun _ _ Hr _ _ Hs => mte_smul Hr Hs;
  rm_smul_distr_l  := mte_smul_distr_l;
  rm_smul_distr_r  := mte_smul_distr_r;
  rm_smul_assoc    := mte_smul_assoc;
  rm_smul_one      := mte_smul_one
|}.

(*
   * The canonical bilinear map: the generator former itself.  Both scalar
   clauses are the two action rules read backwards, which is precisely
   the point at which the tensor is BALANCED — see [tensor_balanced]. 

   --------
   * 规范双线性映射：生成子形式本身。两个标量条款是两个动作规则的逆向读取，这正是张量平衡的点——参见 [tensor_balanced]。
*)
Definition tensor_gen : RBilinear V V' TensorMod :=
  @Build_RBilinear R V V' TensorMod mt_gen
    (fun _ _ Hv _ _ Hw => mte_gen Hv Hw)
    mte_add_l
    mte_add_r
    (fun r v w => mte_sym (mte_act_l r v w))
    (fun r v w => mte_sym (mte_act_r r v w)).

(*
   * (r·v) ⊗ w ≈ v ⊗ (r·w): the balanced law, by composing the two action
   rules through the formal scalar.  It is a THEOREM here rather than a
   generating relation, and it is what a reader coming from the
   non-commutative theory will look for. 

   --------
   * (r·v) ⊗ w ≈ v ⊗ (r·w)：平衡律，通过形式标量将两个作用规则组合在一起。这里它是一个定理，而不是生成关系，对于来自非交换理论的读者来说，这是他们会寻找的内容。
*)
Lemma tensor_balanced (r : carrier (rig_setoid (ring_rig R)))
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  mt_eq (mt_gen (rm_smul V r v) w) (mt_gen v (rm_smul V' r w)).
Proof.
  exact (mte_trans (mte_sym (mte_act_l r v w)) (mte_act_r r v w)).
Qed.

(** The elementary consequences of bilinearity, at the canonical map. / 双线性在典型映射下的基本结果。 *)
Lemma tensor_zero_l (w : carrier (cmon_setoid V')) :
  mt_eq (mt_gen (cmon_zero V) w) mt_zero.
Proof. exact (rbl_zero_l tensor_gen w). Qed.

Lemma tensor_zero_r (v : carrier (cmon_setoid V)) :
  mt_eq (mt_gen v (cmon_zero V')) mt_zero.
Proof. exact (rbl_zero_r tensor_gen v). Qed.

Lemma tensor_neg_l (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  mt_eq (mt_gen (ab_neg V v) w) (mt_neg (mt_gen v w)).
Proof. exact (rbl_neg_l tensor_gen v w). Qed.

Lemma tensor_neg_r (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  mt_eq (mt_gen v (ab_neg V' w)) (mt_neg (mt_gen v w)).
Proof. exact (rbl_neg_r tensor_gen v w). Qed.

(*
   * [rbl_commutator] at the tensor itself: V ⊗ V' is a module on which
   r·s and s·r act alike — equivalently, on which every commutator acts
   as zero, by instantiating [rbl_commutator_annihilates] at
   [tensor_gen].  Over a commutative ring the conclusion already follows
   from [rbl_commutator_from_commutativity] and so carries no
   information; over a non-commutative one it is the collapse the header
   describes. 

   --------
   *  在张量本身上：V ⊗ V' 是一个模，其中 r·s 和 s·r 的作用相同——等价地，在其中每个交换子都作为零作用，这是通过在 [tensor_gen] 上实例化 [rbl_commutator_annihilates] 得到的。在交换环上，结论已经可以由 [rbl_commutator_from_commutativity] 得出，因此没有提供任何信息；在非交换环上，它就是标题所描述的崩溃。
*)
Lemma tensor_commutator (r s : carrier (rig_setoid (ring_rig R)))
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  mt_eq (mt_smul (rig_mul (ring_rig R) r s) (mt_gen v w))
        (mt_smul (rig_mul (ring_rig R) s r) (mt_gen v w)).
Proof. exact (rbl_commutator tensor_gen r s v w). Qed.

End Tensor.

Arguments MTerm {R} V V'.
Arguments mt_gen {R V V'} v w.
Arguments mt_zero {R V V'}.
Arguments mt_plus {R V V'} s t.
Arguments mt_neg {R V V'} s.
Arguments mt_smul {R V V'} r s.
Arguments mt_eq {R V V'} s t.
Arguments mt_refl {R V V'} s.
Arguments mte_gen {R V V' v v' w w'} _ _.
Arguments mte_plus {R V V' s s' t t'} _ _.
Arguments mte_neg {R V V' s s'} _.
Arguments mte_smul {R V V' r r' s s'} _ _.
Arguments mte_assoc {R V V'} s t u.
Arguments mte_comm {R V V'} s t.
Arguments mte_zero_l {R V V'} s.
Arguments mte_neg_l {R V V'} s.
Arguments mte_smul_distr_l {R V V'} r s t.
Arguments mte_smul_distr_r {R V V'} r r' s.
Arguments mte_smul_assoc {R V V'} r r' s.
Arguments mte_smul_one {R V V'} s.
Arguments mte_add_l {R V V'} v v' w.
Arguments mte_add_r {R V V'} v w w'.
Arguments mte_act_l {R V V'} r v w.
Arguments mte_act_r {R V V'} r v w.
Arguments mte_sym {R V V' s t} _.
Arguments mte_trans {R V V' s t u} _ _.
Arguments TensorMod {R} V V'.
Arguments tensor_gen {R V V'}.
Arguments tensor_balanced {R V V'} r v w.
Arguments tensor_zero_l {R V V'} w.
Arguments tensor_zero_r {R V V'} v.
Arguments tensor_neg_l {R V V'} v w.
Arguments tensor_neg_r {R V V'} v w.
Arguments tensor_commutator {R V V'} r s v w.

(** ** The factorization / ** 因式分解 *)

Section Mediator.

Context {R : RingObject}.
Context {V V' : RModObject R}.
Context {W : RModObject R}.
Context (β : RBilinear V V' W).

(*
 Fold a formal expression through the target module's operations.  It
 computes on constructors, which is what makes the three homomorphism
 obligations and the scalar clause below hold by [reflexivity]. 

 --------
 通过目标模块的运算折叠一个形式表达式。它在构造子上进行计算，这就是使下面的三个同态义务和标量条款通过 [reflexivity] 成立的原因。
*)
Fixpoint tensor_med_fun (t : MTerm V V') : carrier (cmon_setoid W) :=
  match t with
  | mt_gen v w  => rbl_map β v w
  | mt_zero     => cmon_zero W
  | mt_plus s t => cmon_plus W (tensor_med_fun s) (tensor_med_fun t)
  | mt_neg s    => ab_neg W (tensor_med_fun s)
  | mt_smul r s => rm_smul W r (tensor_med_fun s)
  end.

(*
 Respectfulness is one induction over the relation: eighteen cases,
 one per constructor of [mt_eq].  Eight are met by the corresponding
 law of the target module (four abelian-group, four module), four by
 the corresponding clause of bilinearity of β, and the other six are
 not laws — [mte_gen] is saturation under the two point setoids, three
 are congruence for a former, and two are the target setoid's symmetry
 and transitivity. 

 --------
 尊重性是在关系上的一种归纳：十八种情况，每个构造器 [mt_eq] 一个。八种由目标模的相应定律满足（四个阿贝尔群，四个模），四种由 β 的双线性相应条款满足，其余六种不是定律——[mte_gen] 是在两个点集体下的饱和，三种是前者的合同性，另外两种是目标集体的对称性和传递性。
*)
Lemma tensor_med_respects (s t : MTerm V V') :
  mt_eq s t → tensor_med_fun s ≈ tensor_med_fun t.
Proof.
  intro He.
  (*
 Since the PR “algebraic carriers are sets” (2026-09-17) [mt_eq] is a
 [Prop] inductive and eliminates only into [Prop] goals, while `≈` is
 [Type]-valued.  [pequiv_to] puts a [Prop] goal in front of the
 elimination; each branch returns to `≈` with [pequiv_from].  The eighteen
 cases and what discharges each are exactly as before.  The intro pattern
 is NAMED because the extra [apply] changes the automatic names. 

 --------
 自从 PR “代数载体是集合”（2026-09-17）以来，[mt_eq] 是一个 [Prop] 归纳类型，并且只消解到 [Prop] 目标，而 `≈` 是 [Type] 值。[pequiv_to] 在消解之前放置了一个 [Prop] 目标；每个分支带着 [pequiv_from] 返回到 `≈`。这十八种情况及其各自的消解方式与以前完全相同。引入模式被命名为 NAMED，因为额外的 [apply] 改变了自动生成的名称。
*)
  apply pequiv_to.
  induction He as
    [ v v' w w' Hv Hw
    | s s' t t' _ IH1 _ IH2
    | s s' _ IH
    | r r' s s' Hr _ IH
    | s t u | s t | s | s
    | r s t | r r' s | r r' s | s
    | v v' w | v w w'
    | r v w | r v w
    | s t _ IH
    | s t u _ IH1 _ IH2 ]; simpl.
  - apply pequiv_from; exact (rbl_respects β _ _ Hv _ _ Hw).
  - apply pequiv_from.
    exact (cmon_plus_respects W _ _ (pequiv_to _ _ IH1)
                                _ _ (pequiv_to _ _ IH2)).
  - apply pequiv_from.
    exact (ab_neg_respects W _ _ (pequiv_to _ _ IH)).
  - apply pequiv_from.
    exact (rm_smul_respects W _ _ Hr _ _ (pequiv_to _ _ IH)).
  - apply pequiv_from; exact (cmon_plus_assoc W _ _ _).
  - apply pequiv_from; exact (cmon_plus_comm W _ _).
  - apply pequiv_from; exact (cmon_plus_zero_l W _).
  - apply pequiv_from; exact (ab_neg_left W _).
  - apply pequiv_from; exact (rm_smul_distr_l W _ _ _).
  - apply pequiv_from; exact (rm_smul_distr_r W _ _ _).
  - apply pequiv_from; exact (rm_smul_assoc W _ _ _).
  - apply pequiv_from; exact (rm_smul_one W _).
  - apply pequiv_from; exact (rbl_add_l β _ _ _).
  - apply pequiv_from; exact (rbl_add_r β _ _ _).
  - apply pequiv_from; exact (symmetry (rbl_smul_l β _ _ _)).
  - apply pequiv_from; exact (symmetry (rbl_smul_r β _ _ _)).
  - exact (symmetry IH).
  - exact (transitivity IH1 IH2).
Qed.

(*
   * The factorizing homomorphism.  Preservation of zero, of addition and
   of the action all hold by [reflexivity], the fixpoint's clauses BEING
   those equations; only respectfulness has content.  One uniform body
   is used for the four obligations so that the proof does not depend on
   the order [Program] emits them in (the Instance/Mod/Free.v
   idiom).  Still four after the PR “algebraic carriers are sets”
   (2026-09-17), re-counted from [Print Module]. 

   --------
   * 因式分解同态。通过 [reflexivity]，零的保持、加法的保持以及作用的保持都成立，固定点的子句就是这些方程；只有尊重性有实质内容。四个义务使用了一个统一的主体，因此证明不依赖于 [Program] 发出它们的顺序（Instance/Mod/Free.v 的方式）。在 PR “代数载体是集合” (2026-09-17) 之后仍然是四个，从 [Print Module] 重新计算。
*)
Program Definition tensor_med : TensorMod V V' ~{RMod R}~> W := {|
  rm_hom := {| cmon_map := {| morphism := tensor_med_fun |} |}
|}.
Next Obligation.
  first [ (intros s t He; exact (tensor_med_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (tensor_med_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (tensor_med_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (tensor_med_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.

(* It agrees with β on generators — definitionally, not up to [≈]. / 它在生成元上与 β 一致——从定义上来说，而不是在 [≈] 上一致。 *)
Example tensor_med_gen (v : carrier (cmon_setoid V))
  (w : carrier (cmon_setoid V')) :
  cmon_map (rm_hom tensor_med) (mt_gen v w) = rbl_map β v w := eq_refl.

End Mediator.

Arguments tensor_med_fun {R V V' W} β t.
Arguments tensor_med {R V V' W} β.

(*
   * Uniqueness, in its most consumable form: two homomorphisms out of the
   tensor that agree on generators agree everywhere.  The [mt_neg] case
   is Instance/Ab.v's [ab_map_neg] and the [mt_smul] case is
   Instance/Mod.v's [rm_map_smul] — which is exactly why this statement
   is about MODULE homomorphisms and would be false for maps of the
   underlying setoids. 

   --------
   * 唯一性，在最易理解的形式下：张量的两个同态在生成元上相同，那么它们在任何地方都相同。[mt_neg] 的情况是 Instance/Ab.v 的 [ab_map_neg]，而 [mt_smul] 的情况是 Instance/Mod.v 的 [rm_map_smul]——这正是为什么这个陈述关于的是 MODULE 同态，并且对于底层集合结构的映射来说是错误的。
*)
Lemma tensor_hom_ext {R : RingObject} {V V' W : RModObject R}
  (f g : TensorMod V V' ~{RMod R}~> W) :
  (∀ (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')),
      cmon_map (rm_hom f) (mt_gen v w) ≈ cmon_map (rm_hom g) (mt_gen v w)) →
  ∀ t : MTerm V V', cmon_map (rm_hom f) t ≈ cmon_map (rm_hom g) t.
Proof.
  intros Hgen t; induction t.
  - exact (Hgen c c0).
  - exact (transitivity (cmon_map_zero (rm_hom f))
             (symmetry (cmon_map_zero (rm_hom g)))).
  - refine (transitivity (cmon_map_plus (rm_hom f) t1 t2) _).
    refine (transitivity _ (symmetry (cmon_map_plus (rm_hom g) t1 t2))).
    exact (cmon_plus_respects W _ _ IHt1 _ _ IHt2).
  - refine (transitivity (ab_map_neg (rm_hom f) t) _).
    refine (transitivity _ (symmetry (ab_map_neg (rm_hom g) t))).
    exact (ab_neg_respects W _ _ IHt).
  - refine (transitivity (rm_map_smul f c t) _).
    refine (transitivity _ (symmetry (rm_map_smul g c t))).
    exact (rm_smul_respects W _ _ (reflexivity c) _ _ IHt).
Qed.

(*
   * ** The bilinear-maps functor

   Bilin(V, V'; −) : RMod R ⟶ Sets — the FUNCTOR, which is what makes
   the tensor product a universal ELEMENT rather than merely an object
   with a mapping property.  The object part is the setoid of bilinear
   maps compared pointwise; the arrow part is postcomposition, and it is
   a bilinear map again because a module homomorphism is additive and
   commutes with the action, which is exactly the two pairs of clauses
   below. 

   --------
   * **双线性映射函子

   Bilin(V, V'; −) : RMod R ⟶ Sets — 这个函子，使得张量积成为一个普遍元（universal ELEMENT），而不仅仅是具有映射性质的一个对象。对象部分是按点比较的双线性映射集合；箭头部分是后合成，它再次是一个双线性映射，因为模同态是可加的并且与作用交换，这正好对应下面的两对条款。
*)

Section BilinFunctor.

Context {R : RingObject}.
Context (V V' : RModObject R).

Program Definition RBilinear_Setoid (W : RModObject R) :
  Setoid (RBilinear V V' W) := {|
  equiv := fun β γ => ∀ v w, rbl_map β v w ≈ rbl_map γ v w
|}.
Next Obligation.
  intros W.
  constructor.
  - intros β v w; reflexivity.
  - intros β γ Hβγ v w; symmetry; apply Hβγ.
  - intros β γ δ H1 H2 v w.
    transitivity (rbl_map γ v w); [ apply H1 | apply H2 ].
Qed.

Definition Bilin_obj (W : RModObject R) : SetoidObject := {|
  carrier   := RBilinear V V' W;
  is_setoid := RBilinear_Setoid W
|}.

(* Postcomposition with a module homomorphism. / 与模同态的后复合。 *)
Program Definition Bilin_post {W W' : RModObject R} (f : W ~{RMod R}~> W')
  (β : RBilinear V V' W) : RBilinear V V' W' := {|
  rbl_map := fun v w => cmon_map (rm_hom f) (rbl_map β v w)
|}.
Next Obligation.
  intros W W' f β v v0 Hv w w0 Hw; simpl.
  now rewrite Hv, Hw.
Qed.
Next Obligation.
  intros W W' f β v v0 w; simpl.
  rewrite (rbl_add_l β v v0 w).
  apply (cmon_map_plus (rm_hom f)).
Qed.
Next Obligation.
  intros W W' f β v w w0; simpl.
  rewrite (rbl_add_r β v w w0).
  apply (cmon_map_plus (rm_hom f)).
Qed.
Next Obligation.
  intros W W' f β r v w; simpl.
  rewrite (rbl_smul_l β r v w).
  apply (rm_map_smul f r (rbl_map β v w)).
Qed.
Next Obligation.
  intros W W' f β r v w; simpl.
  rewrite (rbl_smul_r β r v w).
  apply (rm_map_smul f r (rbl_map β v w)).
Qed.

Program Definition Bilin : RMod R ⟶ Sets := {|
  fobj := Bilin_obj;
  fmap := fun W W' f => {| morphism := Bilin_post f |}
|}.
Next Obligation.
  intros W W' f β γ Hβγ v w; simpl.
  now rewrite (Hβγ v w).
Qed.
Next Obligation.
  intros W W' f g Hfg β v w; simpl.
  exact (Hfg (rbl_map β v w)).
Qed.
Next Obligation.
  intros W β v w; simpl; reflexivity.
Qed.
Next Obligation.
  intros W W' W'' f g β v w; simpl; reflexivity.
Qed.

(*
   * ** The headline: ⟨V ⊗ V', ⊗⟩ is a universal element of Bilin(V, V'; −)

   Mac Lane's clause “(H k) e = x for a unique k” is, unfolded here,
   “k agrees with β on generators, for a unique module homomorphism k”:
   the existence half is [tensor_med] (and the equation holds by
   [reflexivity], the mediator's underlying map being a fixpoint), the
   uniqueness half is [tensor_hom_ext]. 

   --------
   * **标题：⟨V ⊗ V', ⊗⟩ 是 Bilin(V, V'; −) 的一个泛元素

   Mac Lane 的条款“(H k) e = x 对于唯一的 k”在这里展开为：
   “k 在生成元上与 β 一致，对于唯一的模同态 k”：
   存在性部分是 [tensor_med]（并且该方程通过 [reflexivity] 成立，调解器的基础映射是一个不动点），
   唯一性部分是 [tensor_hom_ext]。
*)
Program Definition tensor_universal_element :
  AUniversalElement Bilin (TensorMod V V') := {|
  aue_elem      := tensor_gen;
  aue_universal := fun W β => {| unique_obj := tensor_med β |}
|}.
Next Obligation.
  intros W β v w; simpl; reflexivity.
Qed.
Next Obligation.
  intros W β k Hk t.
  apply (tensor_hom_ext (tensor_med β) k).
  intros v w.
  exact (symmetry (Hk v w)).
Qed.

(* Mac Lane's pair ⟨r, e⟩, the same data with the object as a field. / Mac Lane 的对 ⟨r, e⟩，同样的数据，带有对象作为字段。 *)
Definition tensor_UniversalElement : UniversalElement Bilin :=
  UniversalElement_of_AUniversalElement tensor_universal_element.

(* The representing object is the tensor, by [eq_refl]. / 表示对象是张量，由 [eq_refl] 表示。 *)
Example tensor_UniversalElement_obj :
  @ue_obj (RMod R) Bilin tensor_UniversalElement = TensorMod V V' := eq_refl.

(*
   * *** Unique factorization, read off the class

   These three are the class's own fields at [tensor_universal_element],
   restated for a reader who wants f = f̄ ∘ ⊗ without unfolding
   [AUniversalElement].  Nothing is reproved: [tensor_factor] IS
   [tensor_med] by [eq_refl] ([tensor_factor_is_med]), so the
   factorization still computes. 

   --------
   * *** 唯一分解，从类中读取

   这三个是类在 [tensor_universal_element] 的自身域，
   重新表述给希望 f = f̄ ∘ ⊗ 而不展开 [AUniversalElement] 的读者。没有重新证明：[tensor_factor] 通过 [eq_refl] （[tensor_factor_is_med]）是 [tensor_med]，所以分解仍然可计算。
*)
Definition tensor_factor {W : RModObject R} (β : RBilinear V V' W) :
  TensorMod V V' ~{RMod R}~> W :=
  unique_obj (@aue_universal (RMod R) Bilin (TensorMod V V')
                tensor_universal_element W β).

Example tensor_factor_is_med {W : RModObject R} (β : RBilinear V V' W) :
  tensor_factor β = tensor_med β := eq_refl.

Lemma tensor_factor_commutes {W : RModObject R} (β : RBilinear V V' W)
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  cmon_map (rm_hom (tensor_factor β)) (mt_gen v w) ≈ rbl_map β v w.
Proof.
  exact (unique_property (@aue_universal (RMod R) Bilin (TensorMod V V')
                            tensor_universal_element W β) v w).
Qed.

Lemma tensor_factor_unique {W : RModObject R} (β : RBilinear V V' W)
  (k : TensorMod V V' ~{RMod R}~> W) :
  (∀ (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')),
      cmon_map (rm_hom k) (mt_gen v w) ≈ rbl_map β v w) →
  tensor_factor β ≈ k.
Proof.
  intro Hk.
  exact (uniqueness (@aue_universal (RMod R) Bilin (TensorMod V V')
                       tensor_universal_element W β) k Hk).
Qed.

End BilinFunctor.

Arguments RBilinear_Setoid {R} V V' W.
Arguments Bilin_obj {R} V V' W.
Arguments Bilin_post {R} V V' {W W'} f β.
Arguments Bilin {R} V V'.
Arguments tensor_universal_element {R} V V'.
Arguments tensor_UniversalElement {R} V V'.
Arguments tensor_factor {R V V' W} β.
Arguments tensor_factor_commutes {R V V' W} β v w.
Arguments tensor_factor_unique {R V V' W} β k _.

(*
   * ** Non-degeneracy: ℤ ⊗_ℤ ℤ

   A universal property proved over a quotient says nothing until the
   quotient is shown not to collapse, and a factorization theorem says
   nothing until some factorization is exhibited.  Both are done here at
   the cheapest non-trivial pair of modules in the tree: ℤ over ℤ, where
   the archetypal bilinear map is multiplication.

   Three separate things are measured, because they are separate.
   First, the factorization COMPUTES: the mediator is a fixpoint, so its
   value on a closed generator reduces, by [eq_refl], and it reduces
   through the CLASS as well as through [tensor_med].  Second, the
   quotient does not collapse: distinct generators stay distinct and the
   canonical map is not the zero map — proved by mapping OUT of the
   quotient, through [tensor_med_respects].  That route is taken because
   a direct structural induction on [mt_eq] supplies no usable
   invariant, [mte_sym] and [mte_trans] quantifying over an
   unconstrained intermediate term; no claim is made that no induction
   could work, which would be an impossibility statement and is not
   proved here.  Third, the object is pinned exactly:
   [Int_tensor_iso] identifies ℤ ⊗_ℤ ℤ with ℤ in [RMod Int_Ring]. 

   --------
   * ** 非退化性：ℤ ⊗_ℤ ℤ

   在一个商上的普遍性质证明之前，如果商没有被证明不会退化，它什么也不能说明；而一个分解定理在没有展示某个分解之前，也什么也不能说明。这里在树中最便宜的非平凡模对上完成了这两个步骤：ℤ 在 ℤ 上，其中典型的双线性映射是乘法。测量了三件不同的事物，因为它们是分开的。首先，因式分解计算：中介是一个不动点，因此它在封闭生成元上的值，通过 [eq_refl] 约简，而且它通过 CLASS 以及 [tensor_med] 也约简。其次，商不坍塌：不同的生成元保持不同，并且规范映射不是零映射——通过将 OUT 映射出商，再经过 [tensor_med_respects] 证明。之所以采取这条路径，是因为对 [mt_eq] 进行直接的结构归纳没有提供可用的不变量，[mte_sym] 和 [mte_trans] 量化在一个无约束的中间项上；没有声称没有归纳能够奏效，这将是一个不可能性陈述，并且在这里没有证明。第三，对象被精确固定：[Int_tensor_iso] 在 [RMod Int_Ring] 中将 ℤ ⊗_ℤ ℤ 与 ℤ 识别。
*)

(*
 Multiplication as a bilinear map.  Every clause is a ring law of ℤ;
 the [rbl_smul_r] clause is the one that spends commutativity of ℤ —
 as it must, being the statement that the scalar can be moved out of
 the SECOND variable. 

 --------
 乘法作为双线性映射。每个条款都是 ℤ 的环律；[rbl_smul_r] 条款是花费 ℤ 交换律的那一条——因为它必须如此，这是标量可以从第二个变量中移动出来的声明。
*)
Definition Int_mul_bilinear : RBilinear Int_RMod Int_RMod Int_RMod.
Proof.
  unshelve notypeclasses refine
    (@Build_RBilinear Int_Ring Int_RMod Int_RMod Int_RMod Z.mul _ _ _ _ _).
  - (* rbl_respects / rbl_尊重 *)
    intros a b Hab c d Hcd; simpl in *; unfold Rig.Z_eqT in *; now subst.
  - (* rbl_add_l *)
    intros v v' w; simpl; unfold Rig.Z_eqT; ring.
  - (* rbl_add_r *)
    intros v w w'; simpl; unfold Rig.Z_eqT; ring.
  - (* rbl_smul_l / rbl_smul_l *)
    intros r v w; simpl; unfold Rig.Z_eqT; ring.
  - (* rbl_smul_r: the clause that spends commutativity of ℤ / rbl_smul_r：这个子句涉及 ℤ 的交换性 *)
    intros r v w; simpl; unfold Rig.Z_eqT; ring.
Defined.

(* Index arguments supplied once, as NOTATIONS (so each unfolds to the constructor itself) — the device Instance/Mod/Free.v uses for its own witnesses. / 索引参数只提供一次，作为符号（NOTATIONS）（因此每个都会展开为构造函数本身）——这是设备 Instance/Mod/Free.v 用于其自身见证的方法。 *)
Local Notation zgen  := (@mt_gen Int_Ring Int_RMod Int_RMod).
Local Notation zzero := (@mt_zero Int_Ring Int_RMod Int_RMod).
Local Notation zplus := (@mt_plus Int_Ring Int_RMod Int_RMod).
Local Notation zneg  := (@mt_neg Int_Ring Int_RMod Int_RMod).
Local Notation zsmul := (@mt_smul Int_Ring Int_RMod Int_RMod).

(* The factorization computes, through [tensor_med] and through the universal element's own mediator alike. / 分解通过 [tensor_med] 以及通过通用元自身的中介者进行计算。 *)
Example int_tensor_med_computes :
  cmon_map (rm_hom (tensor_med Int_mul_bilinear)) (zgen 2%Z 3%Z) = 6%Z
  := eq_refl.

Example int_tensor_factor_computes :
  cmon_map (rm_hom (tensor_factor Int_mul_bilinear)) (zgen 2%Z 3%Z) = 6%Z
  := eq_refl.

(* And it computes on a compound tensor, where the fold does real work. / 它在一个复合张量上进行计算，其中折叠执行实际的工作。 *)
Example int_tensor_med_computes_sum :
  cmon_map (rm_hom (tensor_med Int_mul_bilinear))
    (zplus (zsmul 5%Z (zgen 2%Z 3%Z)) (zneg (zgen 4%Z 1%Z)))
  = 26%Z := eq_refl.

(*
   * The quotient does not collapse.  Both statements are proved by
   mapping OUT through [tensor_med_respects]: an inhabitant of [mt_eq]
   would give an equation in ℤ that [discriminate] refutes. 

   --------
   * 商不坍缩。两个声明都通过将 OUT 映射到 [tensor_med_respects] 得以证明：[mt_eq] 的一个元素会给出一个在 ℤ 中的方程，而 [discriminate] 予以反驳。
*)
Lemma int_tensor_gen_nonzero : mt_eq (zgen 1%Z 1%Z) zzero → False.
Proof.
  intro He.
  pose proof (tensor_med_respects Int_mul_bilinear _ _ He) as Hz.
  simpl in Hz; unfold Rig.Z_eqT in Hz.
  discriminate Hz.
Qed.

Lemma int_tensor_gen_distinct :
  mt_eq (zgen 1%Z 1%Z) (zgen 2%Z 1%Z) → False.
Proof.
  intro He.
  pose proof (tensor_med_respects Int_mul_bilinear _ _ He) as Hz.
  simpl in Hz; unfold Rig.Z_eqT in Hz.
  discriminate Hz.
Qed.

(*
   * The inverse comparison n ↦ n ⊗ 1.  It is a module homomorphism
   because 0 ⊗ 1 ≈ 0 ([tensor_zero_l]), because the generator former is
   additive ([mte_add_l]), and because the scalar rule [mte_act_l] is
   exactly linearity of n ↦ n ⊗ 1. 

   --------
   * 逆向比较 n ↦ n ⊗ 1。它是一个模同态，因为 0 ⊗ 1 ≈ 0（[tensor_zero_l]），因为生成器形式是可加的（[mte_add_l]），并且因为标量法则 [mte_act_l] 恰好是 n ↦ n ⊗ 1 的线性性。
*)
(*
 Respectfulness is supplied as a term ([mte_gen] with the second
 component reflexive) rather than left to [Program], which would fill
 it by [reflexive_proper] — sound here only because ℤ's setoid
 equality happens to be Leibniz, and not a habit worth forming.  The
 three remaining obligations are preservation of zero, of addition and
 of the action, in that order. 

 --------
 尊重被作为一个术语提供（[mte_gen]，第二个组件为反身的），而不是留给[Program]，由[reflexive_proper]来填充——这里的声音只是因为ℤ的集合等价巧合地是莱布尼兹等价，而不是值得形成的习惯。剩下的三个义务分别是保持零、保持加法和保持作用，按此顺序。
*)
Program Definition int_tensor_unit :
  Int_RMod ~{RMod Int_Ring}~> TensorMod Int_RMod Int_RMod := {|
  rm_hom := {| cmon_map := {|
    morphism        := fun n => zgen n 1%Z;
    proper_morphism := fun a b Hab => mte_gen Hab (reflexivity 1%Z) |} |}
|}.
Next Obligation.
  exact (@tensor_zero_l Int_Ring Int_RMod Int_RMod 1%Z).
Qed.
Next Obligation.
  intros a b; exact (@mte_add_l Int_Ring Int_RMod Int_RMod a b 1%Z).
Qed.
Next Obligation.
  intros r n; exact (mte_sym (@mte_act_l Int_Ring Int_RMod Int_RMod r n 1%Z)).
Qed.

(*
   * ℤ ⊗_ℤ ℤ ≅ ℤ in [RMod Int_Ring].  One leg is multiplication, the
   other is n ↦ n ⊗ 1; the round trip on the tensor is [tensor_hom_ext]
   plus the balanced law, which is where the whole quotient is used. 

   --------
   * ℤ ⊗_ℤ ℤ ≅ ℤ 在 [RMod Int_Ring] 中。一个映射是乘法，另一个是 n ↦ n ⊗ 1；张量上的往返映射是 [tensor_hom_ext] 加上平衡律，这就是整个商被使用的地方。
*)
Program Definition Int_tensor_iso :
  @Isomorphism (RMod Int_Ring) (TensorMod Int_RMod Int_RMod) Int_RMod := {|
  to   := tensor_med Int_mul_bilinear;
  from := int_tensor_unit
|}.
Next Obligation.
  intro n; simpl; unfold Rig.Z_eqT; apply Z.mul_1_r.
Qed.
Next Obligation.
  refine (tensor_hom_ext
            (int_tensor_unit ∘ tensor_med Int_mul_bilinear)
            (@id (RMod Int_Ring) (TensorMod Int_RMod Int_RMod)) _).
  intros v w; simpl.
  (* (v·w) ⊗ 1 ≈ (w·v) ⊗ 1 ≈ w·(v ⊗ 1) ≈ v ⊗ (w·1) ≈ v ⊗ w: the middle two steps are the two action rules, i.e. the balanced law. / (v·w) ⊗ 1 ≈ (w·v) ⊗ 1 ≈ w·(v ⊗ 1) ≈ v ⊗ (w·1) ≈ v ⊗ w：中间两步是两个作用规则，即平衡律。 *)
  refine (mte_trans (@mte_gen Int_Ring Int_RMod Int_RMod _ _ _ _
                       (Z.mul_comm v w) (reflexivity 1%Z)) _).
  refine (mte_trans (mte_sym (@mte_act_l Int_Ring Int_RMod Int_RMod w v 1%Z)) _).
  refine (mte_trans (@mte_act_r Int_Ring Int_RMod Int_RMod w v 1%Z) _).
  exact (@mte_gen Int_Ring Int_RMod Int_RMod _ _ _ _
           (reflexivity v) (Z.mul_1_r w)).
Qed.
