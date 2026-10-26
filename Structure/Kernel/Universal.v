Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Kernel.
Require Import Category.Theory.Universal.Element.

Generalizable All Variables.

(** * Kernels as universal elements / * 核心作为通用元素 *)

(*
 nLab:      https://ncatlab.org/nlab/show/kernel
 https://ncatlab.org/nlab/show/universal+element
 https://ncatlab.org/nlab/show/representable+functor
 https://ncatlab.org/nlab/show/category+with+zero+morphisms
 Wikipedia: https://en.wikipedia.org/wiki/Kernel_(category_theory)

 [Structure/Kernel.v] defines the kernel of f : x ~> y as an equalizer of
 f against the zero morphism, and states its universal property in the
 zero-composite phrasing ([kernel_desc]): any h : d ~> x with f ∘ h ≈ 0
 factors uniquely through the kernel inclusion.  Read that clause with the
 quantifier over d out front and it is no longer a statement about one
 object but about a PRESHEAF: for each d the set

 Kill_f(d)  =  { h : d ~> x  |  f ∘ h ≈ 0 }

 of maps into x that f kills, contravariant in d by precomposition
 (nLab, “kernel”: “the kernel of f is the representing object of the
 functor sending d to the set of morphisms h : d → x such that
 f ∘ h = 0”).  [kernel_desc] then says exactly that the pair ⟨k, i⟩ --
 the kernel object together with its inclusion, which is an ELEMENT of
 Kill_f(k) because f ∘ i ≈ 0 -- is a universal element of that presheaf
 in the sense of Mac Lane's Definition 2 of §III.1 (CWM 2nd ed., p. 57):
 every element of every Kill_f(d) is (Kill_f u)(i) for a unique
 u : d ~> k.

 This file proves the two readings equivalent, using the class
 [AUniversalElement] of Theory/Universal/Element.v (issue #303) rather
 than a bespoke unique-factorization clause.  “Equivalent” is delivered
 at three different strengths, which are three different claims and are
 kept apart below: the two passages with their round trips (no universe
 restriction), the representability statement Hom(─, k) ≅ Kill_f in
 [C^op, Sets] (no universe restriction), and the bundling of the two
 record types as an isomorphism of SETOIDS in [Sets] (which carries
 one, and which the concrete witnesses therefore do not use).  The
 catalog files the result as maclane:III.1:remark4.  NOTE ON
 ATTRIBUTION: nothing below quotes the wording of that remark, and no
 claim is made here about what Mac Lane wrote at that spot; what is
 cited above is §III.1's Definition 2, which the file does use, and the
 nLab's statement of the kernel's universal property, which is what the
 file proves.

 Where the notion sits, and why the presheaf packaging is the durable one

 Text:  Mac Lane, “Categories for the Working Mathematician”, Springer
 1998, §III.1 (pp. 55-59), §VIII.1
 Text:  Riehl, “Category Theory in Context”, Dover 2016, §2.4
 Text:  Awodey, “Category Theory”, Oxford 2010, §2.9
 Paper: Kan, “Adjoint functors”, Trans. Amer. Math. Soc. 87, 1958

 The kernel is the oldest universal construction in algebra and the one
 whose element-free rendering cost the most.  In group theory a kernel
 is a SUBSET -- the preimage of the identity -- and the categorical
 definition has to say the same thing without mentioning elements or
 the identity.  Two moves accomplish it.  The first is to replace “the
 identity of the target” by the zero morphism, which requires the
 ambient category to have one; the second is to replace “the subset of
 things sent to zero” by the universal property of the equalizer.  The
 present file performs a third: it puts the quantifier over the probing
 object back in front, which turns the universal property into the
 assertion that ONE presheaf is representable.

 That third move is not decoration.  A universal property stated as a
 factorization clause is a statement about the chosen object k; stated
 as representability it is a statement about the functor Kill_f, which
 exists whether or not k does.  So the presheaf is defined for every f
 in every category with zero morphisms, and “f has a kernel” becomes
 “Kill_f is representable” -- a property of an object of the presheaf
 category rather than a piece of data attached to f.  This is the form
 in which kernels generalize: the kernel presheaf of a map of sheaves is
 already a sheaf (a kernel is a limit, and limits of sheaves are
 computed presheaf-wise), and in a general topos the subobject it names
 is defined by exactly this representability -- Mac Lane's §VIII.1
 subobject classifier being the same device applied to monomorphisms
 rather than to killed maps.

 And it is the form that survives the loss of the zero morphism.  Mac
 Lane's Rng -- unital rings with unit-preserving homomorphisms -- has
 no zero object and no zero morphisms at all: a ring homomorphism must
 send 1 to 1, so the constant-zero map is a homomorphism only into the
 trivial ring, and there is no morphism whatever from the trivial ring
 to Z.  (Those are theorems, not remarks: [Rng_no_hom_zero_to_Z],
 [Rng_no_zero_morphisms] and [Rng_no_zero_object] in the companion file
 Structure/Kernel/Universal/Examples.v.)  Kernels in the categorical
 sense therefore do not exist in Rng; what does exist, for any parallel
 pair f, g, is the presheaf of maps on which f and g agree, and its
 representing object is the equalizer.  The two presheaves below --
 [KillPresheaf] over a zero-morphism structure and [ForkPresheaf] over
 a bare parallel pair -- are that observation made into definitions,
 and the [kill_fork_iso] between them is the exact statement of how
 much the zero morphism buys. 

 --------
 nLab:       https://ncatlab.org/nlab/show/kernel 
 https://ncatlab.org/nlab/show/universal+element 
 https://ncatlab.org/nlab/show/representable+functor 
 https://ncatlab.org/nlab/show/category+with+zero+morphisms 
 维基百科:  https://en.wikipedia.org/wiki/Kernel_(category_theory) 

 [Structure/Kernel.v] 定义了 f : x ~> y 的核作为 f 与零态射的等化器，并在零复合表述中说明了其泛性质 ([kernel_desc])：任何 h : d ~> x 满足 f ∘ h ≈ 0 的映射都可唯一地通过核包含映射分解。将这个条款中的量词作用于前面的 d，就不再是关于单个对象的陈述，而是关于一个预上层结构：对于每个 d，有集合

 Kill_f(d)  =  { h : d ~> x  |  f ∘ h ≈ 0 }将映射到 x 的映射中由 f 消去的，按 d 通过预组合是反变的（nLab，“kernel”: “f 的核是函子代表对象，该函子将 d 发送到满足 f ∘ h = 0 的形态 h : d → x 的集合”）。[kernel_desc] 然后恰恰说这个对 ⟨k, i⟩ —— 核对象及其包含，它是 Kill_f(k) 的一个元素，因为 f ∘ i ≈ 0 —— 在这种预层的意义下，是一个泛元素，根据 Mac Lane 的 §III.1 定义 2（CWM 第二版，第 57 页）：每个 Kill_f(d) 的元素都是 (Kill_f u)(i) 对于唯一的 u : d ~> k。该文件使用 Theory/Universal/Element.v 中的 [AUniversalElement] 类（问题 #303）证明了两种读法是等价的，而不是使用定制的唯一分解条款。“等价”在三种不同强度下给出，这三种是不同的命题，并在下面分开说明：两段及其往返转换（没有宇宙限制），可表示性陈述 Hom(─, k) ≅ Kill_f 在 [C^op, Sets] 中（没有宇宙限制），以及将两种记录类型捆绑为 [Sets] 中 SETOIDS 的同构（它携带一个，因此具体的见证者不使用它）。该目录将结果归档为 maclane:III.1:remark4。关于归属的说明：下面的内容没有引用该评论的措辞，也没有在此提出关于 Mac Lane 在该位置所写内容的任何主张；上面引用的是 §III.1 的定义 2，该文件确实使用了该定义，以及 nLab 关于核的泛性质的陈述，这正是该文件所证明的内容。

 该概念所在的位置，以及为什么预层包封方式是持久的方式

 参考文献：
 文本：Mac Lane，《为在职数学家准备的范畴论》，Springer，1998年，§III.1（第55-59页），§VIII.1
 文本：Riehl，《语境中的范畴论》，Dover，2016年，§2.4
 文本：Awodey，《范畴论》，Oxford，2010年，§2.9
 论文：Kan，《伴随函子》，美数学学会学报 87，1958年核是代数中最古老的通用结构，也是无元素表达代价最高的结构。在群论中，核是一个子集——单位元的原像——而范畴论的定义必须在不提及元素或单位元的情况下表达同样的意思。有两个步骤可以实现这一点。第一步是将“目标的单位元”替换为零态射，这要求所属范畴必须存在零态射；第二步是将“映射到零的元素子集”替换为等化子的普遍性性质。本文件执行了第三步：它将量词重新放回到探测对象之前，这将普遍性性质转化为断言一个预层是可表示的。第三个动作不是装饰。作为分解条款陈述的普遍性质，是关于所选对象 k 的陈述；作为可表示性陈述，它是关于函子 Kill_f 的陈述，无论 k 是否存在，Kill_f 都存在。因此，预层对于每个具有零态射的范畴中的每个 f 都是定义良好的，并且“f 有一个核”变成了“Kill_f 可表示”——这是预层范畴中一个对象的性质，而不是附加到 f 的数据。这就是核泛化的形式：一个层映射的核预层已经是一个层（核是极限，而层的极限是按预层计算的），在一般的拓扑中，它所命名的子对象正是由这种可表示性定义的——Mac Lane §VIII.1 中的子对象分类器是将相同的装置应用于单态射而不是被杀映射。它是能在零态射丢失后依然存在的形式。Mac Lane 的 Rng——带有单位保持同态的幺环——没有零对象，也完全没有零态射：环同态必须将 1 映射为 1，因此常零映射仅能作为到平凡环的同态，而且从平凡环到 Z 根本不存在态射。（这些是定理，不是备注：见伴随文件 Structure/Kernel/Universal/Examples.v 中的 [Rng_no_hom_zero_to_Z]、[Rng_no_zero_morphisms] 和 [Rng_no_zero_object]。）因此，在范畴意义上，Rng 中不存在核；对于任何平行对 f, g，存在的是 f 与 g 相同的映射的预层，而其代表对象是等化子。下面的两个预层——在零态射结构上的 [KillPresheaf] 和在裸并行对上的 [ForkPresheaf]——是将该观察转化为定义，而它们之间的 [kill_fork_iso] 精确地说明了零态射的作用有多大。
*)

(*
 WHAT IS DELIVERED

 * [ZeroMorphisms], the pointed-hom structure: a chosen family
 [zmor : x ~> y] absorbing composition on both sides, i.e. a category
 with zero morphisms (nLab), a strictly weaker hypothesis than a zero
 object.  [ZeroMorphisms_of_ZeroObject] derives it from
 [Structure/ZeroObject.v]'s [ZeroObject], and the derivation is
 TRANSPARENT: [zmor] at the derived structure IS [zero_mor] by
 [eq_refl] ([zmor_is_zero_mor]), so [Structure/Kernel.v]'s [IsKernel]
 and this file's [IsKernelOf] are THE SAME TYPE by [eq_refl]
 ([IsKernel_is_IsKernelOf]) and every result below applies to the
 tree's existing kernels with no adapter.

 * DELIVERABLE 1.  [KillPresheaf f : C^op ⟶ Sets], the kill-f presheaf
 d ↦ { h : d ~> x | f ∘ h ≈ 0 } with precomposition as its action and
 a hom-setoid comparing only the underlying morphism; the two
 passages [kernel_aue] and [aue_kernel]; and the equivalence, at
 THREE DIFFERENT STRENGTHS, which are three different claims and are
 labelled as such:

 (1) UNIVERSE-FREE, and the form consumers should use: the two
 passages, with the underlying morphism surviving BOTH
 directions by [eq_refl] ([kernel_aue_morphism],
 [aue_kernel_morphism]) and the mediator surviving both up to
 `≈` ([kernel_round_mediator], [aue_kernel_round_mediator]).
 [kernel_aue_mediator] records the sharper fact that in one
 direction the mediator is the SAME TERM.  Nothing here
 restricts C.

 (2) THE REPRESENTABILITY STATEMENT, also universe-free:
 [kernel_representation], the natural isomorphism
 [Hom ─,k] ≅ [KillPresheaf f] in [C^op, Sets], and
 [kernel_Representable].  This is the issue's own phrasing of
 deliverable 1 and it DOES instantiate at [Ab].

 (3) BUNDLED AS AN ISOMORPHISM OF SETOIDS in [Sets] between
 { i : k ~> x & IsKernelOf i } and
 [AUniversalElement (KillPresheaf f) k]:
 [kernel_universal_element_iso].  Strongest as a statement --
 not a biconditional (which forgets the maps), not merely a
 pair of mutually inverse maps up to `≈` (which forgets
 respectfulness) -- but it CARRIES A UNIVERSE RESTRICTION, and
 the restriction excludes [Ab].  The measured signature and its
 structural cause are set out at the definition; the short form
 is that [obj[Sets]] identifies a setoid's carrier and relation
 universes while [KernelData]'s sit at C's object and proof
 universes respectively, and [Ab] is declared with its objects
 STRICTLY ABOVE its homs.  The restriction enters at THIS step
 and at no earlier one -- neither the presheaf nor the
 representation carries it, measured at [KillPresheaf] -- which
 is what makes (1) and (2) usable exactly where (3) is not.

 In neither direction does the WHOLE RECORD survive a round trip, and
 the file says exactly why: the kill shape (f ∘ h ≈ 0) and the fork
 shape (f ∘ h ≈ 0 ∘ h) are interchanged by [kill_fork] / [fork_kill],
 two [Qed]-opaque proof transformations, and [eq_desc] is
 proof-RELEVANT in its hypothesis, so the composite is not the
 identity term.  Pinned in Test/ProbeKernelUniversal.v.

 * The representability reading the issue asks for:
 [kernel_Representable] (an instance of [Functor/Representable.v]'s
 class at [KillPresheaf f], with [repr_obj] the kernel object by
 [eq_refl]) and [kernel_representation], the natural isomorphism
 [Hom ─,k] ≅ [KillPresheaf f] in [C^op, Sets] whose component at d
 carries u to i ∘ u by [eq_refl] ([kernel_representation_at]).  Both
 are routed through Theory/Universal/Element.v's DIRECT
 (Yoneda-free) constructions, for the reason that file's header
 gives: [Yoneda_Lemma] identifies the object, hom and proof universes
 of its category, and nothing here should inherit that.
 [kernel_iff_representable] is the biconditional “f has a kernel iff
 Kill_f is representable”.

 * DELIVERABLE 2, in two grades.  [KillPresheaf] itself already needs
 only [ZeroMorphisms], hence no zero OBJECT.  Below that,
 [ForkPresheaf f g] needs nothing at all -- an arbitrary parallel
 pair in an arbitrary category -- and
 [equalizer_universal_element_iso] is the same theorem for
 equalizers.  [kill_fork_iso] is the natural isomorphism
 [KillPresheaf f] ≅ [ForkPresheaf f zmor] relating the two.

 * A MEASURED DIFFERENCE BETWEEN THE TWO PACKAGINGS, and it is the
 file's one genuinely delicate finding.  On the fork side one whole
 round trip IS [eq_refl] on the whole record
 ([aue_equalizer_round]) -- the two records' field types are
 convertible one for one, so both passages are [:=] with no tactic --
 while the other is not, and the ONLY obstruction is that [sigT] has
 no eta: [aue_equalizer_round_universal] records that the universal
 clause survives up to repacking p as (`1 p; `2 p), and the element
 survives outright.  On the kill side NEITHER round trip is
 [eq_refl], and the extra obstruction is precisely the [zmor ∘ h]
 reshaping.  So the fork packaging is definitionally tighter than the
 kill packaging, which is the opposite of what the naming suggests.

 WHAT IS NOT DELIVERED

 * NO COKERNEL DUAL.  Everything here would dualize to
 [Structure/Coequalizer.v]'s [IsCoequalizer] and a COpresheaf
 d ↦ { h : y ~> d | h ∘ f ≈ 0 }, whose universal element is a
 COUNIVERSAL element in the sense of Theory/Universal/Arrow/Dual.v.
 Theory/Universal/Element.v's header records that it delivers no
 dual of [AUniversalElement], and this file inherits that gap rather
 than filling it.

 * NO CLAIM THAT THE ISO IS A BIJECTION OF TYPES.  It is an
 isomorphism of SETOIDS, and both setoids compare only the
 underlying morphism.  The record-level negatives above are what
 that costs.

 * NO CLAIM THAT THE BUNDLED ISO'S UNIVERSE RESTRICTION IS
 UNAVOIDABLE.  What is measured is that THIS packaging does not
 instantiate at [Ab] or [Rng]; whether some other packaging of the
 same content would is not addressed, and the two universe-free forms
 above make the question moot for consumers.

 * NO SMALLNESS OR SIZE ANALYSIS.  [KillPresheaf] lands in whichever
 [Sets] the ambient universes force; nothing here is stated about
 local smallness (see Theory/Size.v).

 * NO UNIQUENESS-UP-TO-UNIQUE-ISO COROLLARY IN C.  Instantiating
 Theory/Universal/Element.v's [universal_element_unique] at
 [KillPresheaf f] yields the statement over C^op, where the
 isomorphism is an [@Isomorphism (C^op) k k'] rather than an
 isomorphism of C; restating it in C is a transport this file does
 not perform.  [equalizer_unique] (Structure/Equalizer/Fork.v)
 already supplies the bare isomorphism.

 * NO INSTANCE OF [HasKernels] IS BUILT for any category; the [Ab]
 witness in the companion file is a kernel of one morphism at a
 time, which is what [kernel_aue] consumes. 

 --------
 交付的内容

 * [ZeroMorphisms]，尖点-
 同构结构：一个已选择的族
 [zmor : x ~> y] 在两侧吸收的复合，即一个带零态射的范畴（nLab），这个假设严格比零对象弱。[ZeroMorphisms_of_ZeroObject] 从 [Structure/ZeroObject.v] 的 [ZeroObject] 推导而来，并且推导是透明的：在派生结构上的 [zmor] 通过 [eq_refl]（[zmor_is_zero_mor]）就是 [zero_mor]，所以 [Structure/Kernel.v] 的 [IsKernel] 和这个文件的 [IsKernelOf] 通过 [eq_refl]（[IsKernel_is_IsKernelOf]）是同一类型，并且以下每个结果都适用于树中现有的核而无需适配器。* 可交付成果 1. [KillPresheaf f : C^op ⟶ Sets]，kill-f 预层 
 d ↦ { h : d ~> x | f ∘ h ≈ 0 }，其作用是前置组合，并且
 使用仅比较底层态射的同态集族；两个通道 [kernel_aue] 和 [aue_kernel]；以及在
 三种不同强度下的等价性，这三种不同主张被如此标记：

 (1) 无宇宙限制，消费者应使用的形式：两个通道，其底层态射在 [eq_refl]（[kernel_aue_morphism]，[aue_kernel_morphism]）中在两个方向上都存活，并且中介者在 `≈`（[kernel_round_mediator]，[aue_kernel_round_mediator]）上在两个方向上也存活。
 [kernel_aue_mediator] 记录了更精确的事实，即在一个方向上中介者是相同的项。此处没有任何内容限制 C。(2) 可表示性陈述，同时无限制宇宙：
 [kernel_representation]，自然同构
 [Hom ─,k] ≅ [KillPresheaf f] 在 [C^op, Sets] 中，以及
 [kernel_Representable]。 这是本期刊对可交付成果1的表述，并且确实在 [Ab] 上实例化。(3) 在  [Sets] 中，被捆绑为集合等价关系的同构，介于
 { i : k ~> x & IsKernelOf i } 和
 [AUniversalElement (KillPresheaf f) k] ：
 [kernel_universal_element_iso] 。作为陈述最强形式 --
 不是一个双条件（它会忽略映射），也不仅仅是一个
 互为逆映射的对直到 `≈` （它会忽略对尊重性）-- 但它携带了一个宇宙限制，
 并且该限制排除了 [Ab] 。测量签名及其结构原因在定义中列出；简短形式是
 [obj[Sets] ] 将一个集合等价关系的承载体和关系宇宙识别出来，而 [KernelData] 的则分别位于 C 的对象和证明宇宙中，
 并且 [Ab] 被声明其对象严格高于其态射。限制在此步骤进入
 而在更早的步骤中不会——预层或表示都没有携带它，在 [KillPresheaf] 处测得——这正是使得 (1) 和 (2) 可用而 (3) 不可用的原因。

 在任一方向上，完整记录都无法在往返操作中保留，文件里明确说明了原因：杀形 (f ∘ h ≈ 0) 与分叉形 (f ∘ h ≈ 0 ∘ h) 被 [kill_fork] / [fork_kill] 互换，
 这是两个 [Qed] 不透明的证明变换，并且 [eq_desc] 在其假设中是相关证明的，因此复合不是恒等项。固定在 Test/ProbeKernelUniversal.v 中。* 可表示性阅读问题要求：
 [kernel_Representable]（[Functor/Representable.v] 在 [KillPresheaf f] 的类的一个实例，
 [repr_obj] 为由 [eq_refl] 定义的核对象）以及 [kernel_representation]，自然同构
 [Hom ─,k] ≅ [KillPresheaf f] 在 [C^op, Sets] 中，其在 d 点的分量
 通过 [eq_refl]（[kernel_representation_at]）将 u 送到 i ∘ u。两者
 都通过 Theory/Universal/Element.v 的 DIRECT
 （Yoneda 免费）构造处理，原因是那份文件的头部
 给出：[Yoneda_Lemma] 识别其类别的对象、Hom 和证明宇宙，
 此处不应继承这些。[kernel_iff_representable] 是双条件陈述“f 有核当且仅当
 Kill_f 可表示”。* 可交付成果 2，有两个等级。[KillPresheaf] 本身已经只需要 [ZeroMorphisms]，因此没有零对象。在此之下，[ForkPresheaf f g] 根本不需要任何东西——在任意类别中的任意平行对——而 [equalizer_universal_element_iso] 是关于等化器的相同定理。[kill_fork_iso] 是自然同构 [KillPresheaf f] ≅ [ForkPresheaf f zmor]，关联这两者。* 两种包装之间的一个测量差异，这是该文件真正微妙的发现。在分支侧，一个完整的往返是 [eq_refl]，在整个记录上（[aue_equalizer_round]）——两个记录的字段类型可以一一转换，因此两个通道都是 [:=]，没有策略——而另一个则不是，且唯一的阻碍是 [sigT] 没有 eta：[aue_equalizer_round_universal] 记录通用子句在重新打包 p 作为 (`1 p; ` 2 p) 时仍然存在，并且元素完全保留。在删除侧，两个往返均不是 [eq_refl]，额外的阻碍恰好是 [zmor ∘ h] 的重塑。因此，分支包装在定义上比删除包装更紧密，这与名称所暗示的正好相反。

 未交付的内容是什么* 没有 COKERNEL DUAL。这里的所有内容都会对 [Structure/Coequalizer.v] 的 [IsCoequalizer] 以及一个余预层  
 d ↦ { h : y ~> d | h ∘ f ≈ 0 } 进行对偶化，其通用元素在 Theory/Universal/Arrow/Dual.v 的意义上是一个 COUNIVERSAL 元素。  
 Theory/Universal/Element.v 的头部记录了它不提供 [AUniversalElement] 的对偶，而这个文件继承了这一缺失，而不是去填补它。

 * 没有声明该同构是类型上的双射。它是一个 SETOIDS 的同构，并且两个集合体只比较底层的态射。上面记录级别的负面情况正是这个的代价。* 没有声称捆绑的 ISO 的宇宙限制是不可避免的。所测量的是此包装在 [Ab] 或 [Rng] 中没有实例化；是否其他某些相同内容的包装会实例化则未涉及，上述两个无宇宙限制的形式使消费者对此问题无关紧要。

 * 没有小性或大小分析。[KillPresheaf] 会降到环境宇宙强制的任何 [Sets]；这里未说明局部小性（参见 Theory/Size.v）。* 在 C 中没有 UNIQUENESS-UP-TO-UNIQUE-ISO 推论。在 [KillPresheaf f] 处实例化 Theory/Universal/Element.v 的 [universal_element_unique] 会得出 C^op 上的陈述，其中同构是一个 [@Isomorphism (C^op) k k']，而不是 C 的同构；在 C 中重新表述它是一个传输，此文件未执行此操作。[equalizer_unique] (Structure/Equalizer/Fork.v) 已经提供了裸同构。

 * 对于任何范畴都没有构建 [HasKernels] 的实例；配套文件中的 [Ab] 见证者是一次处理一个态射的核，这正是 [kernel_aue] 消耗的。
*)

(* * ** Zero morphisms without a zero object / * ** 没有零对象的零态射 *)

(*
 A category with zero morphisms (nLab): a chosen morphism between every
 pair of objects, absorbing composition on both sides.  Equivalently a
 category enriched in pointed sets; the enrichment is not what is needed
 below, so the structure is stated elementarily.

 This is weaker than [ZeroObject]: a zero object supplies such a family by
 tunnelling ([zero_mor], and the two absorption laws are [zero_mor_left] /
 [zero_mor_right]), so [ZeroMorphisms_of_ZeroObject] gives one direction.
 BE PRECISE ABOUT THE OTHER: the converse non-implication -- a category
 with zero morphisms and no zero object -- is TRUE but is NOT WITNESSED
 here, and no such witness exists in the tree.  What the companion file
 proves for Rng is the different and weaker statement that a category can
 have NEITHER.  A cheap witness is available for anyone who wants it
 ([Construction/Deloop.v]'s [Deloop M] at a two-element monoid with an
 absorbing element has zero morphisms, and its single object has two
 endomorphisms so it is not a zero object); it is not built here, and
 until it is, “weaker” should be read as “not known here to be
 equivalent” rather than as a proved separation.

 The class is declared HERE rather than in a file of its own because
 nothing else in the tree consumes it yet; promoting it to
 Structure/ZeroMorphisms.v when a second consumer appears would be a
 move, not a redesign. 

 --------
 一个零态射的范畴 (nLab)：在每一对对象之间选择一个态射，该态射在两边的复合中都是吸收的。等价地，这是一个在点集上富化的范畴；下面所需的并不是这种富化，因此结构以基本方式陈述。这比 [ZeroObject] 弱：一个零对象通过隧穿 ([zero_mor]) 提供这样一个族，并且两个吸收律是 [zero_mor_left] / [zero_mor_right]，因此 [ZeroMorphisms_of_ZeroObject] 给出了一个方向。关于另一个方向要精确：逆非蕴含——一个具有零态射但没有零对象的范畴——是真的，但在这里没有体现，也没有这样的见证存在于树中。伴随文件为 Rng 证明的是一个不同且更弱的陈述，即一个范畴可以既没有零对象也没有零态射。任何想要的人都可以得到一个便宜的证人
 （[Construction/Deloop.v] 在一个具有吸收元的二元单体上的 [Deloop M] 有零态射，并且它的单个对象有两个自同态，因此它不是零对象）；它在这里没有构建，在它构建之前，“更弱”应理解为“在此未知是否等价”，而不是作为已证明的区分。

 该类在这里声明，而不是在它自己的文件中，是因为树中的其他部分尚未使用它；当出现第二个使用者时，将其提升到 Structure/ZeroMorphisms.v 会是一种迁移，而不是重新设计。
*)
Class ZeroMorphisms (C : Category) := {
  zmor {x y : C} : x ~> y;
  zmor_absorb_l {x y z : C} (g : y ~> z) : g ∘ @zmor x y ≈ @zmor x z;
  zmor_absorb_r {x y z : C} (g : x ~> y) : @zmor y z ∘ g ≈ @zmor x z
}.

(*
 Given as a term rather than through [Program], so that the [zmor]
 projection reduces: [zmor_is_zero_mor] below is [eq_refl], and that is
 what makes [IsKernel] and [IsKernelOf] the same type. 

 --------
 作为一个术语给出，而不是通过 [Program]，因此 [zmor] 投影减少：[zmor_is_zero_mor] 在下方是 [eq_refl]，这就是使 [IsKernel] 和 [IsKernelOf] 属于同一类型的原因。
*)
#[export] Instance ZeroMorphisms_of_ZeroObject {C : Category}
  (Z : @ZeroObject C) : ZeroMorphisms C :=
  @Build_ZeroMorphisms C
    (fun x y => @zero_mor C Z x y)
    (fun x y z g => @zero_mor_left C Z x y z g)
    (fun x y z g => @zero_mor_right C Z x y z g).

(** ** The kill-f presheaf / ** 杀-f预层 *)

Section KernelUniversal.

Context {C : Category}.
Context {ZM : ZeroMorphisms C}.
Context {x y : C}.
Context (f : x ~> y).

(*
 The elements of the presheaf at d: the maps into x that f kills.  The
 witness is DATA (`∃` is [sigT] in this library, Lib/Foundation.v), so
 [Kills d] is a type of PAIRS and the setoid below is what forgets the
 second component. 

 --------
 预层在 d 处的元素：被 f 消去的映射到 x 的那些映射。证据是 DATA（在这个库 Lib/Foundation.v 中，`∃` 是 [sigT]），所以 [Kills d] 是一类 PAIRS 类型，而下面的集合化类型就是忘记第二个分量的内容。
*)
Definition Kills (d : C) : Type := { h : d ~> x & f ∘ h ≈ zmor }.

(*
 Two elements are identified when their underlying morphisms are: the
 proof that f kills them carries no further information.  This is
 Structure/UniversalProperty.v's [exists_setoid] shape, spelled out
 locally rather than imported, since that instance is declared
 [#[local]] there and re-exporting it would push a
 first-projection-only setoid onto every sigma in scope. 

 --------
 当两个元素的底层态射被识别时：证明 f 消去它们不会提供更多信息。这是 Structure/UniversalProperty.v 中的 [exists_setoid] 形状，本地展开而不是导入，因为该实例在 [#[local] 中声明，而重新导出它会将仅包含第一投影的等价类推到作用域中的每个 sigma 上。
*)
Program Definition Kills_Setoid (d : C) : Setoid (Kills d) := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.

(*
 Contravariant by precomposition: if f kills h then it kills h ∘ u, by
 associativity and absorption. 

 --------
 通过前合成的反变性：如果 f 消去 h，那么它也消去 h ∘ u，这是由结合律和吸收律得出的。
*)
Program Definition KillPresheaf : C^op ⟶ Sets := {|
  fobj := fun d => {| carrier := Kills d ; is_setoid := Kills_Setoid d |};
  fmap := fun d d' (u : d ~{C^op}~> d') =>
            {| morphism := fun p : Kills d => (`1 p ∘ u; _) |}
|}.
Next Obligation.
  rewrite comp_assoc, (`2 p).
  apply zmor_absorb_r.
Qed.

(*
 THE PRESHEAF'S OWN UNIVERSE BEHAVIOUR, measured rather than assumed,
 because two known hazards live in this neighbourhood and a reader
 arriving from either will want to know which one applies.  [About]
 under [Set Printing Universes] reports

 KillPresheaf@{u u0 u1}
 : ∀ {C : Category@{u u0 u0}}, … → Functor@{u u0 u0 u1 u0 u0}
 ( * u u0 u1 |= u0 < u1, u0 <= compose.u{0,1,2},
 u0 <= Projections.u{0,1}, u0 <= ID.u0 * )

 and three things follow.

 FIRST, THERE IS NO [u <= u0].  The presheaf places no ordering between
 C's OBJECT universe u and its hom universe u0, and neither does
 [kernel_representation] below (same binder, same absence).  Its
 codomain is [Sets@{u0 u1}] -- carrier universe EQUAL to C's hom/proof
 universe u0, object universe u1 strictly above.  This is exactly why
 the universe-free forms and the representability statement instantiate
 at [Ab] while [kernel_universal_element_iso] does not: the ordering
 constraint is not present here, and enters only at that one step (the
 diagnosis is spelled out at its definition).

 SECOND, THE CONCRETE-OBJECT [Set] PIN OF Theory/Universal/Element.v
 DOES NOT FIRE HERE, and this is worth recording as a negative result
 rather than left for the next reader to re-derive.  That file's header
 warns that a [Sets]-morphism out of a CONCRETE object whose
 [proper_morphism] is left to instance resolution pins the carrier
 universe of [Sets] to [Set].  [fmap[KillPresheaf f] u] is such a
 morphism with [proper_morphism] discharged by the obligation tactic --
 but its source is [fobj] at a VARIABLE d, not a concrete object, which
 is precisely the condition that donor note identifies.  Measured: no
 [Set] appears anywhere in the constraints of [KillPresheaf], [Kills],
 [Kills_Setoid], [ForkPresheaf], or that [fmap], and the morphism is
 fully polymorphic.  Nothing had to be done to avoid the pin.

 THIRD, AND THE ONE NOBODY WOULD REDISCOVER WITHOUT LOOKING: the
 binder is [Category@{u u0 u0}], so the presheaf IDENTIFIES C's hom and
 proof universes.  It costs nothing today -- every category in this
 library satisfies h <= p, and [Ab] and [Rng] are already declared with
 h = p, so no in-tree consumer can feel it -- but it is a genuine
 narrowing and it is stated here so that a future category with h
 strictly below p is not debugged from scratch. 

 --------
 预层本身的宇宙行为，是被测量而非假设的，因为在这个邻域里存在两个已知的风险，而来自其中任何一个的读者都想知道哪个适用。[About] 在 [Set Printing Universes] 下报告

 KillPresheaf@{u u0 u1}
 : ∀ {C : Category@{u u0 u0}}, … → Functor@{u u0 u0 u1 u0 u0}
 ( * u u0 u1 |= u0 < u1, u0 <= compose.u{0,1,2},
 u0 <= Projections.u{0,1}, u0 <= ID.u0 * )

 接着有三件事情发生。首先，没有 [u <= u0]。该预层在 C 的对象宇宙 u 与其 Hom 宇宙 u0 之间没有任何顺序约束，下面的 [kernel_representation] 也没有（相同的绑定器，相同的缺失）。它的余域是 [Sets@{u0 u1}] ——承载宇宙等于 C 的 Hom/证明宇宙 u0，对象宇宙 u1 严格在其之上。这正是为什么无宇宙形式和可表示性声明在 [Ab] 上实例化，而 [kernel_universal_element_iso] 上不实例化：这里没有顺序约束，这一约束仅在那一步出现（其定义中明确说明了诊断）。其次，Theory/Universal/Element.v 的具体对象 [Set] 引脚在这里没有触发，这值得记录为一个负面结果，而不是留给下一位读者重新推导。该文件的头部警告说，从一个具体对象中发出的 [Sets] -态射，其 [proper_morphism] 留给实例解析，会将 [Sets] 的承载宇宙固定为 [Set]。[fmap[KillPresheaf f] u] 是这样一个态射，[proper_morphism] 由义务策略解除——但是它的源是 VARIABLE d 的 [fobj]，而不是具体对象，这正是捐赠者注释所指出的条件。测量：在 [KillPresheaf]、[Kills]、[Kills_Setoid]、[ForkPresheaf] 或该 [fmap] 的约束中没有出现 [Set]，且该态射是完全多态的。不需要做任何操作来避免引脚。第三，也是如果不去查没人会重新发现的：这个绑定器是 [Category@{u u0 u0}]，因此预层识别了 C 的 hom 和证明宇宙。今天它不花钱——这个库中的每个范畴都满足 h <= p，并且 [Ab] 和 [Rng] 已经声明了 h = p，所以树内的任何消费者都不会感受到它——但它确实是一种真正的缩窄，并且在这里说明，以便未来有 h 严格小于 p 的范畴时，不会从零开始调试。
*)

(*
 The action, by conversion: this is what makes the universal-element
 clause below literally the descent clause of [kernel_desc]. 

 --------
 通过转换的动作：这就是使下面的通用元素条款字面上成为 [kernel_desc] 的下降条款的原因。
*)
Lemma kill_fmap (d d' : C) (u : d' ~{C}~> d) (p : Kills d) :
  `1 (fmap[KillPresheaf] u p) = `1 p ∘ u.
Proof. reflexivity. Qed.

(* * ** The two shapes of the kernel equation / * ** 核方程的两种形状 *)

(*
 [IsEqualizer]'s fork equation compares f ∘ h with (zmor ∘ h); the kill
 presheaf compares it with zmor.  The two are interchanged by absorption,
 and these two lemmas are the entire difference between the kernel
 packaging and the fork packaging of the next section.  They are [Qed],
 hence opaque, so their composite is not the identity term -- and that
 is why the record-level round trips below are not [eq_refl].  Making
 them [Defined] would not repair that: the composite would still be a
 [rewrite]-built term rather than the original proof, so the round trip
 would remain a genuine equation up to `≈` and nothing beyond
 readability would change. 

 --------
 [IsEqualizer] 的叉形方程将 f ∘ h 与 (zmor ∘ h) 进行比较；kill presheaf 将其与 zmor 进行比较。通过吸收律，这两者是可以互换的，并且这两个引理就是下一节内核封装和叉形封装之间的全部区别。它们是 [Qed]，因此是不透明的，所以它们的组合不是恒等项——这就是为什么下面的记录级往返不是 [eq_refl]。将它们变为 [Defined] 并不能修复这一点：组合仍然是一个 [rewrite] 构建的项，而不是原始证明，因此往返仍然是一个真正的方程，直到 `≈`，并且可读性之外不会有任何变化。
*)
Lemma kill_fork {d : C} {h : d ~> x} (Hh : f ∘ h ≈ zmor) :
  f ∘ h ≈ zmor ∘ h.
Proof. rewrite Hh; symmetry; apply zmor_absorb_r. Qed.

Lemma fork_kill {d : C} {h : d ~> x} (Hh : f ∘ h ≈ zmor ∘ h) :
  f ∘ h ≈ zmor.
Proof. rewrite Hh; apply zmor_absorb_r. Qed.

(*
 [Structure/Kernel.v]'s [IsKernel] restated over [ZeroMorphisms].  When
 the structure comes from a zero object the two are THE SAME TYPE; see
 [IsKernel_is_IsKernelOf] below. 

 --------
 [Structure/Kernel.v] 的 [IsKernel] 在 [ZeroMorphisms] 上被重述。当结构来自零对象时，两者是相同类型；见下文的 [IsKernel_is_IsKernelOf]。
*)
Definition IsKernelOf {k : C} (i : k ~> x) : Type := IsEqualizer f zmor k i.

(** ** The two passages / ** 这两段 *)

(*
 A kernel is a universal element of the kill-f presheaf.  The element is
 the inclusion, carrying the proof that f kills it; the universal clause
 IS [eq_desc], with the hypothesis reshaped.

 Both passages are [:=] with no tactic: the fields' types are convertible
 one for one, since [k ~{C^op}~> d] IS [d ~{C}~> k] (Construction/
 Opposite.v takes [homset] on the nose) and the presheaf's `≈` unfolds to
 an equation between underlying morphisms.  What is NOT convertible is
 the pair of PROOFS, which is why the round trips below are stated up to
 `≈`. 

 --------
 核是 kill-f 预层的一个通用元素。该元素是包含映射，携带 f 将其消去的证明；通用子句是 [eq_desc]，并且假设已重新调整格式。

 两个段落都是 [:=]，没有使用策略：字段的类型可以一一互相转换，因为 [k ~{C^op}~> d] 是 [d ~{C}~> k]（Construction/Opposite.v 精确使用 [homset]），并且预层的 `≈` 展开为底层态射之间的等式。不可转换的是证明对，这就是下面的往返操作仅在 `≈` 意义下成立的原因。
*)
Definition kernel_aue {k : C} {i : k ~> x} (K : IsKernelOf i)
  : AUniversalElement KillPresheaf k :=
  @Build_AUniversalElement (C^op) KillPresheaf k
    (existT _ i (fork_kill (fork_eq K)))
    (fun d p => eq_desc K (`1 p) (kill_fork (`2 p))).

Definition aue_kernel {k : C} (U : AUniversalElement KillPresheaf k)
  : IsKernelOf (`1 (@aue_elem (C^op) KillPresheaf k U)) :=
  {| fork_eq := kill_fork (`2 (@aue_elem (C^op) KillPresheaf k U))
   ; eq_desc := fun z h Hh =>
       @aue_universal (C^op) KillPresheaf k U z (existT _ h (fork_kill Hh)) |}.

(* The underlying morphism survives both passages on the nose. / 底层同态在两个过程中都严格保持不变。 *)
Corollary kernel_aue_morphism {k : C} {i : k ~> x} (K : IsKernelOf i) :
  `1 (@aue_elem (C^op) KillPresheaf k (kernel_aue K)) = i.
Proof. reflexivity. Qed.

Corollary aue_kernel_morphism {k : C} (U : AUniversalElement KillPresheaf k) :
  `1 (@aue_elem (C^op) KillPresheaf k
        (kernel_aue (aue_kernel U)))
    = `1 (@aue_elem (C^op) KillPresheaf k U).
Proof. reflexivity. Qed.

(* ... and so does the mediator: the unique factorization the universal element produces IS the one [eq_desc] produces, as a term. / ... 调解者也是如此：唯一分解所产生的通用元素就是 [eq_desc] 所产生的那个项。 *)
Corollary kernel_aue_mediator {k : C} {i : k ~> x} (K : IsKernelOf i)
  (d : C) (h : d ~> x) (Hh : f ∘ h ≈ zmor) :
  unique_obj (@aue_universal (C^op) KillPresheaf k (kernel_aue K) d (h; Hh))
    = unique_obj (eq_desc K h (kill_fork Hh)).
Proof. reflexivity. Qed.

(* * ** The equivalence, universe-free: the two round trips / * ** 等值，无宇宙限制：两次往返 *)

(*
 THE FORM CONSUMERS SHOULD USE.  These say everything the setoid
 isomorphism below says -- the morphism survives both passages
 ([kernel_aue_morphism] and [aue_kernel_morphism] above, by [eq_refl]) and
 the mediator survives both passages up to `≈` -- WITHOUT packaging the
 two record types as objects of [Sets], which is where the universe
 restriction documented at [kernel_universal_element_iso] comes from.
 Nothing in this pair restricts C, and the [Ab] instantiation in
 Structure/Kernel/Universal/Examples.v uses exactly these. 

 --------
 消费者应使用的表单。它们表达了下面集合等价所表达的所有内容——这个态射在两次传递（上面的 [kernel_aue_morphism] 和 [aue_kernel_morphism]，通过 [eq_refl]）中都保持不变，中介在两次传递中也保持不变直到 `≈` ——而无需将两个记录类型打包为 [Sets] 的对象，这正是 [kernel_universal_element_iso] 中文档化的宇宙限制的来源。这对中没有任何内容限制 C，而 Structure/Kernel/Universal/Examples.v 中的 [Ab] 实例正是使用这些。
*)

Lemma kernel_round_mediator {k : C} {i : k ~> x} (K : IsKernelOf i)
  {z : C} (h : z ~> x) (Hh : f ∘ h ≈ zmor ∘ h) :
  unique_obj (eq_desc (aue_kernel (kernel_aue K)) h Hh)
    ≈ unique_obj (eq_desc K h Hh).
Proof.
  apply (uniqueness (eq_desc (aue_kernel (kernel_aue K)) h Hh)).
  exact (unique_property (eq_desc K h Hh)).
Qed.

Lemma aue_kernel_round_mediator {k : C} (U : AUniversalElement KillPresheaf k)
  (d : C) (p : Kills d) :
  unique_obj (@aue_universal (C^op) KillPresheaf k
                (kernel_aue (aue_kernel U)) d p)
    ≈ unique_obj (@aue_universal (C^op) KillPresheaf k U d p).
Proof.
  apply (uniqueness (@aue_universal (C^op) KillPresheaf k
                       (kernel_aue (aue_kernel U)) d p)).
  exact (unique_property (@aue_universal (C^op) KillPresheaf k U d p)).
Qed.

(* * ** The equivalence, as an isomorphism of setoids / * ** 作为集合类的同构的等价性 *)

Definition KernelData (k : C) : Type := { i : k ~> x & IsKernelOf i }.

Program Definition KernelData_Setoid (k : C) : Setoid (KernelData k) := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.

Definition KernelSetoid (k : C) : SetoidObject :=
  {| carrier := KernelData k ; is_setoid := KernelData_Setoid k |}.

Definition AUEKernelSetoid (k : C) : SetoidObject :=
  {| carrier := AUniversalElement KillPresheaf k
   ; is_setoid := @AUniversalElementEquiv (C^op) KillPresheaf k |}.

(*
 DELIVERABLE 1, BUNDLED.  An isomorphism in [Sets], i.e. of SETOIDS.  Both
 respectfulness obligations and both round-trip laws are the identity on
 the underlying morphism, so all four are discharged by the file's
 obligation tactic; [kernel_aue_morphism] and [aue_kernel_morphism]
 above record what they say.

 READ THE UNIVERSE SIGNATURE BEFORE REACHING FOR THIS.  Measured:

 kernel_universal_element_iso@{u u0 u1}
 : ∀ {C : Category@{u u0 u0}} …,  with  u <= u0

 -- the object universe of C must sit AT OR BELOW its hom universe, and
 the hom and proof universes must coincide.  That is a restriction on
 this packaging, and its cause is structural rather than incidental:
 [obj[Sets@{o so}]] is [SetoidObject@{o o}] (Instance/Sets.v), which
 IDENTIFIES a setoid's carrier universe with its relation universe, while
 [KernelData k]'s carrier sits at C's OBJECT universe (through [eq_desc]'s
 quantifier over the probing object) and its relation at C's PROOF
 universe.  Equating them forces o(C) <= p(C).

 THE CONSTRAINT ENTERS HERE AND NOWHERE EARLIER, which is the part
 worth knowing.  Neither [KillPresheaf] nor [kernel_representation]
 carries any [u <= u0] (measured; see the note at [KillPresheaf]), and
 the presheaf's codomain [Sets@{u0 u1}] already has its carrier universe
 fixed at C's HOM universe u0.  What this definition does is force
 [KernelSetoid], whose carrier sits at C's OBJECT universe, into that
 same [Sets] -- and the two can only be reconciled by u <= u0.  So the
 wall is not a property of the kernel/universal-element correspondence;
 it is the price of bundling the two record types as objects of ONE
 [Sets], and it is why the universe-free forms above are the ones the
 concrete witnesses use.

 Concrete categories generally do not satisfy it.  [Ab@{u u0} : Category@{u u0 u0}]
 is declared with [u0 < u] -- objects strictly above homs -- so this
 isomorphism does NOT instantiate at [Ab], and neither does its equalizer
 twin at [Rng]; both negatives are pinned in Test/ProbeKernelUniversal.v
 with a positive control at a category whose universes coincide.  Use
 [kernel_aue] / [aue_kernel] with [kernel_round_mediator] /
 [aue_kernel_round_mediator] instead, or [kernel_representation], none of
 which carry the restriction.  NOTE what is and is not shown: that this
 packaging does not reach [Ab] is measured; that no packaging could is
 NOT claimed. 

 --------
 可交付成果 1，捆绑。 在 [Sets] 中的同构，即 SETOIDS 的同构。 两种尊重义务和两条往返定律在底层态射上都是恒等，因此四者都通过文件的义务策略得到解决；上述 [kernel_aue_morphism] 和 [aue_kernel_morphism] 记录了它们的内容。

 在接触此内容之前，请先阅读宇宙签名。 测量：

 kernel_universal_element_iso@{u u0 u1}
 : ∀ {C : Category@{u u0 u0}} …, 且 u <= u0-- C 的对象宇宙必须位于或低于其同态宇宙，并且同态和证明宇宙必须重合。也就是说，这是对这种封装的限制，其原因是结构性的而非偶然的：[obj[Sets@{o so}] 是 [SetoidObject@{o o}]（Instance/Sets.v），它将集合组织的承载宇宙与其关系宇宙等同起来，而 [KernelData k] 的承载位于 C 的对象宇宙（通过 [eq_desc] 对被探测对象的量化）而其关系位于 C 的证明宇宙。将它们等同迫使 o(C) <= p(C)。约束在此刻出现，而不是更早，这是值得了解的部分。[KillPresheaf] 和 [kernel_representation] 都不携带任何 [u <= u0]（可测；参见 [KillPresheaf] 的注释），并且预层的陪域 [Sets@{u0 u1}] 的承载宇宙已经固定在 C 的 HOM 宇宙 u0。这个定义所做的是将承载位于 C 的对象宇宙的 [KernelSetoid] 强制到同一个 [Sets]——而两者只能通过 u <= u0 来调和。因此，这道墙不是核/万能元素对应的属性；它是将这两种记录类型捆绑为一个 [Sets] 对象的代价，这也是为什么上面的无宇宙形式是具体实例使用的形式。具体范畴通常不满足它。[Ab@{u u0} : Category@{u u0 u0}] 被声明为 [u0 < u] ——对象严格高于 Hom——所以这个同构在 [Ab] 上不实例化，其在 [Rng] 上的等化子对偶也不实例化；这两个否定在 Test/ProbeKernelUniversal.v 中被固定，同时提供了一个在范畴其宇宙相同的正控制。使用 [kernel_aue] / [aue_kernel] 以及 [kernel_round_mediator] / [aue_kernel_round_mediator]，或者 [kernel_representation]，以上都不带有该限制。注意显示的内容和未显示的内容：测量显示这个封装无法达到 [Ab]，但并未声称没有任何封装能够做到。
*)
Program Definition kernel_universal_element_iso (k : C)
  : @Isomorphism Sets (KernelSetoid k) (AUEKernelSetoid k) := {|
  to   := {| morphism := fun p : KernelData k => kernel_aue (`2 p) |};
  from := {| morphism := fun U : AUniversalElement KillPresheaf k =>
               (`1 (@aue_elem (C^op) KillPresheaf k U); aue_kernel U) |}
|}.

(** ** Representability / ** 可表示性 *)

(*
 The bundled form, and then [Functor/Representable.v]'s class.  Both are
 routed through Theory/Universal/Element.v's direct constructions rather
 than through [universal_element_representation], which inherits
 [Yoneda_Lemma]'s identification of the object, hom and proof universes
 (that file's header, measured there). 

 --------
 捆绑形式，然后是 [Functor/Representable.v] 的类。两者都是通过 Theory/Universal/Element.v 的直接构造进行路由，而不是通过 [universal_element_representation]，后者继承了 [Yoneda_Lemma] 对对象、同态和证明宇宙的识别（该文件的头部，在那里测量）。
*)
Definition kernel_UniversalElement {k : C} {i : k ~> x} (K : IsKernelOf i)
  : UniversalElement KillPresheaf :=
  UniversalElement_of_AUniversalElement (kernel_aue K).

Definition kernel_Representable {k : C} {i : k ~> x} (K : IsKernelOf i)
  : Representable KillPresheaf :=
  Representable_of_UniversalElement (kernel_UniversalElement K).

Corollary kernel_repr_obj {k : C} {i : k ~> x} (K : IsKernelOf i) :
  @repr_obj (C^op) KillPresheaf (kernel_Representable K) = k.
Proof. reflexivity. Qed.

(*
 The natural isomorphism itself: Hom(─, k) ≅ Kill_f in [C^op, Sets].
 [@Curried_Hom (C^op) k] IS [Hom ─,k], the presheaf Hom(─, k)
 (Functor/Hom.v defines [Curried_CoHom C] as [Curried_Hom C^op]). 

 --------
 自然同构本身：Hom(─, k) ≅ Kill_f 在 [C^op, Sets] 中。
 [@Curried_Hom (C^op) k] 是 [Hom ─,k]，余预层 Hom(─, k)
 （Functor/Hom.v 定义 [Curried_CoHom C] 为 [Curried_Hom C^op]）。
*)
Definition kernel_representation {k : C} {i : k ~> x} (K : IsKernelOf i)
  : @Curried_Hom (C^op) k ≅[[C^op, Sets]] KillPresheaf :=
  ue_representation KillPresheaf k (kernel_aue K).

(*
 Its component at d carries u : d ~> k to i ∘ u, on the nose -- the
 comparison map of the kernel's universal property. 

 --------
 它在 d 处的分量携带 u：d ~> k 到 i ∘ u，完全一致——核的泛性质的比较映射。
*)
Corollary kernel_representation_at {k : C} {i : k ~> x} (K : IsKernelOf i)
  (d : C) (u : d ~{C}~> k) :
  `1 (transform (to (kernel_representation K)) d u) = i ∘ u.
Proof. reflexivity. Qed.

(*
 “f has a kernel” iff “the kill-f presheaf is representable”.  The
 backward leg reads the universal element off the representation by
 Mac Lane's Φ_r(id r) computation ([AUniversalElement_of_repr]) and then
 applies [aue_kernel]. 

 --------
 “f 有核” 当且仅当 “kill-f 预层是可表示的”。
 反向部分通过 Mac Lane 的 Φ_r(id r) 计算 ([AUniversalElement_of_repr]) 从表示中读取泛元素，然后应用 [aue_kernel]。
*)
Definition kernel_of_representable (R : Representable KillPresheaf)
  : { k : C & { i : k ~> x & IsKernelOf i } } :=
  ( @repr_obj (C^op) KillPresheaf R
  ; ( `1 (@aue_elem (C^op) KillPresheaf (@repr_obj (C^op) KillPresheaf R)
            (AUniversalElement_of_repr KillPresheaf
               (@repr_obj (C^op) KillPresheaf R)
               (@represented (C^op) KillPresheaf R)))
    ; aue_kernel (AUniversalElement_of_repr KillPresheaf
                    (@repr_obj (C^op) KillPresheaf R)
                    (@represented (C^op) KillPresheaf R)) )).

Definition kernel_iff_representable
  : { k : C & { i : k ~> x & IsKernelOf i } } ↔ Representable KillPresheaf.
Proof.
  split.
  - intros [k [i K]]; exact (kernel_Representable K).
  - exact kernel_of_representable.
Defined.

End KernelUniversal.

Arguments Kills {C ZM x y} f d.
Arguments KillPresheaf {C ZM x y} f.
Arguments IsKernelOf {C ZM x y} f {k} i.

(* * ** The zero-object case: [Structure/Kernel.v]'s kernels, unchanged / * ** 零对象情况：[Structure/Kernel.v] 的核，不变 *)

Section KernelUniversalZeroObject.

Context {C : Category}.
Context {Z : @ZeroObject C}.
Context {x y : C}.
Context (f : x ~> y).

(*
 The derived zero-morphism family IS the tunnelled zero morphism, by
 conversion -- the projection reduces because
 [ZeroMorphisms_of_ZeroObject] is a term, not a [Program] instance with
 opaque obligation fields. 

 --------
 派生零态射族是隧道零态射，通过转换——投影减少，因为 [ZeroMorphisms_of_ZeroObject] 是一个项，而不是具有不透明义务字段的 [Program] 实例。
*)
Corollary zmor_is_zero_mor :
  @zmor C (ZeroMorphisms_of_ZeroObject Z) x y = @zero_mor C Z x y.
Proof. reflexivity. Qed.

(*
 ... hence the two kernel predicates are THE SAME TYPE, not merely
 equivalent ones.  Everything in the previous section therefore applies
 to [Structure/Kernel.v]'s kernels with no adapter; the two definitions
 below record that by taking an [IsKernel] where an [IsKernelOf] is
 expected. 

 --------
 ... 因此这两个核心谓词是相同类型的，而不仅仅是等价的。因此前一节中的所有内容都适用于没有适配器的 [Structure/Kernel.v] 的核心；下面的两个定义通过在预期 [IsKernelOf] 的地方使用 [IsKernel] 来记录这一点。
*)
Corollary IsKernel_is_IsKernelOf {k : C} (i : k ~> x) :
  @IsKernel C Z x y k f i = @IsKernelOf C (ZeroMorphisms_of_ZeroObject Z) x y f k i.
Proof. reflexivity. Qed.

Definition kernel_universal_element {k : C} {i : k ~> x} (K : IsKernel f i)
  : AUniversalElement (@KillPresheaf C (ZeroMorphisms_of_ZeroObject Z) x y f) k
  := kernel_aue f K.

Definition kernel_representable {k : C} {i : k ~> x} (K : IsKernel f i)
  : Representable (@KillPresheaf C (ZeroMorphisms_of_ZeroObject Z) x y f)
  := kernel_Representable f K.

End KernelUniversalZeroObject.

(* * ** The zero-free packaging: an arbitrary parallel pair / * ** 零损包装：任意的并行对 *)

(*
 Deliverable 2 at full strength.  Nothing in this section mentions a zero
 object, a zero morphism or any structure on C: [ForkPresheaf f g] is
 defined for any parallel pair, and its universal elements are exactly
 the equalizers of that pair.  This is the packaging that reaches Rng,
 where no zero morphism exists at all
 ([Rng_no_zero_morphisms], Structure/Kernel/Universal/Examples.v). 

 --------
 可交付成果 2 全力以赴。本节中没有提到零对象、零态射或 C 上的任何结构：[ForkPresheaf f g] 对任何平行对都是定义好的，其通用元素正是该对的等化器。这是到达 Rng 的打包形式，在那里根本不存在零态射（[Rng_no_zero_morphisms]，Structure/Kernel/Universal/Examples.v）。
*)

Section EqualizerUniversal.

Context {C : Category}.
Context {x y : C}.
Context (f g : x ~> y).

Definition Forks (d : C) : Type := { h : d ~> x & f ∘ h ≈ g ∘ h }.

Program Definition Forks_Setoid (d : C) : Setoid (Forks d) := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.

Program Definition ForkPresheaf : C^op ⟶ Sets := {|
  fobj := fun d => {| carrier := Forks d ; is_setoid := Forks_Setoid d |};
  fmap := fun d d' (u : d ~{C^op}~> d') =>
            {| morphism := fun p : Forks d => (`1 p ∘ u; _) |}
|}.
Next Obligation. rewrite !comp_assoc; now rewrite (`2 p). Qed.

(* Here the sigma's property IS the fork equation and the universal clause IS [eq_desc], with NO reshaping: both passages are [:=] and the field types are convertible one for one. / 这里 sigma 的属性是分叉方程，通用子句是 [eq_desc]，没有重塑：两个段落都是 [:=]，并且字段类型是一一可转换的。 *)
Definition equalizer_aue {k : C} {i : k ~> x} (E : IsEqualizer f g k i)
  : AUniversalElement ForkPresheaf k :=
  @Build_AUniversalElement (C^op) ForkPresheaf k
    (existT _ i (fork_eq E))
    (fun d p => eq_desc E (`1 p) (`2 p)).

Definition aue_equalizer {k : C} (U : AUniversalElement ForkPresheaf k)
  : IsEqualizer f g k (`1 (@aue_elem (C^op) ForkPresheaf k U)) :=
  {| fork_eq := `2 (@aue_elem (C^op) ForkPresheaf k U)
   ; eq_desc := fun z h Hh =>
       @aue_universal (C^op) ForkPresheaf k U z (existT _ h Hh) |}.

(*
 ... and so ONE round trip is [eq_refl] ON THE WHOLE RECORD, which the
 kernel packaging cannot manage in either direction.  [IsEqualizer] is
 a record with primitive projections, so record eta applies; the
 [eq_desc] field closes by function eta. 

 --------
 ... 所以一次往返就是整个记录上的 [eq_refl]，而内核包装在任一方向上都无法处理。[IsEqualizer] 是一个带有原始投影的记录，因此适用记录 eta；[eq_desc] 字段通过函数 eta 结束。
*)
Corollary aue_equalizer_round {k : C} {i : k ~> x} (E : IsEqualizer f g k i) :
  aue_equalizer (equalizer_aue E) = E.
Proof. reflexivity. Qed.

(*
 The other round trip is NOT [eq_refl], and the ONLY obstruction is that
 [sigT] has no eta: the universal clause survives up to repacking the
 argument as (`1 p; `2 p), which this corollary states.  Both of the
 ELEMENT's projections survive too, though the packaged pair does not --
 [aue_equalizer_round_elem] states the first-projection equality, and the
 whole-element form is one of the pinned negatives, for exactly the same
 want of eta.  The negative is pinned in
 Test/ProbeKernelUniversal.v. 

 --------
 另一次往返不是 [eq_refl]，唯一的障碍是 [sigT] 没有 eta：通用条款在将参数重新打包为 (`1 p; ` 2 p) 之前仍然有效，本推论即指出此点。ELEMENT 的两个投影也都仍然有效，但打包后的对不再如此——[aue_equalizer_round_elem] 表示第一投影等式，整个元素形式是固定的否定之一，原因正是缺少 eta。该否定在 Test/ProbeKernelUniversal.v 中被固定。
*)
Corollary aue_equalizer_round_universal {k : C}
  (U : AUniversalElement ForkPresheaf k) :
  @aue_universal (C^op) ForkPresheaf k (equalizer_aue (aue_equalizer U))
    = fun d p => @aue_universal (C^op) ForkPresheaf k U d (`1 p; `2 p).
Proof. reflexivity. Qed.

Corollary aue_equalizer_round_elem {k : C}
  (U : AUniversalElement ForkPresheaf k) :
  `1 (@aue_elem (C^op) ForkPresheaf k (equalizer_aue (aue_equalizer U)))
    = `1 (@aue_elem (C^op) ForkPresheaf k U).
Proof. reflexivity. Qed.

(*
 The mediator survives that round trip too -- and here at LEIBNIZ
 equality, not merely up to `≈`, which is the sharper reading and the
 one the strict form was tried at first.  The kill-side analogue
 [aue_kernel_round_mediator] is only `≈`, and the gap between the two is
 exactly the [kill_fork] / [fork_kill] reshaping. 

 --------
 调解者也在那次往返中生存下来——在莱布尼茨这里，平等，不仅仅是到 `≈`，这是更严格的读法，也是最初尝试严格形式时的读法。杀方的类似物 [aue_kernel_round_mediator] 仅为 `≈`，而两者之间的差距正是 [kill_fork] / [fork_kill] 的重塑。
*)
Lemma aue_equalizer_round_mediator {k : C}
  (U : AUniversalElement ForkPresheaf k) (d : C) (p : Forks d) :
  unique_obj (@aue_universal (C^op) ForkPresheaf k
                (equalizer_aue (aue_equalizer U)) d p)
    = unique_obj (@aue_universal (C^op) ForkPresheaf k U d p).
Proof.
  (* [destruct p] and not [reflexivity]: the two sides differ ONLY by the repacking (`1 p; `2 p), which is [sigT]'s missing eta -- and which the [destruct] supplies. / [destruct p] 而不是 [reflexivity]：双方唯一的区别在于重新打包（`1 p; ` 2 p），这是 [sigT] 缺失的 eta —— 而 [destruct] 提供了它。 *)
  destruct p; reflexivity.
Qed.

Definition EqualizerData (k : C) : Type := { i : k ~> x & IsEqualizer f g k i }.

Program Definition EqualizerData_Setoid (k : C) : Setoid (EqualizerData k) := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.

Definition EqualizerSetoid (k : C) : SetoidObject :=
  {| carrier := EqualizerData k ; is_setoid := EqualizerData_Setoid k |}.

Definition AUEEqualizerSetoid (k : C) : SetoidObject :=
  {| carrier := AUniversalElement ForkPresheaf k
   ; is_setoid := @AUniversalElementEquiv (C^op) ForkPresheaf k |}.

Program Definition equalizer_universal_element_iso (k : C)
  : @Isomorphism Sets (EqualizerSetoid k) (AUEEqualizerSetoid k) := {|
  to   := {| morphism := fun p : EqualizerData k => equalizer_aue (`2 p) |};
  from := {| morphism := fun U : AUniversalElement ForkPresheaf k =>
               (`1 (@aue_elem (C^op) ForkPresheaf k U); aue_equalizer U) |}
|}.

(* The equalizer's representability, for symmetry with the kernel case. / 为了与核情况的对称性，均衡器的可表示性。 *)
Definition equalizer_Representable {k : C} {i : k ~> x}
  (E : IsEqualizer f g k i) : Representable ForkPresheaf :=
  Representable_of_UniversalElement
    (UniversalElement_of_AUniversalElement (equalizer_aue E)).

Corollary equalizer_repr_obj {k : C} {i : k ~> x} (E : IsEqualizer f g k i) :
  @repr_obj (C^op) ForkPresheaf (equalizer_Representable E) = k.
Proof. reflexivity. Qed.

End EqualizerUniversal.

Arguments Forks {C x y} f g d.
Arguments ForkPresheaf {C x y} f g.

(* * ** How much the zero morphism buys / * ** 零态射能买多少 *)

(*
 The two presheaves are naturally isomorphic when a zero-morphism family
 is available: both components are the identity on the underlying
 morphism, and the only content is [kill_fork] / [fork_kill].  This is
 the exact statement of the relationship -- the kill shape is not more
 general, and not less; it is the fork shape at g := zmor, transported
 across a proof reshaping that costs the record-level round trips. 

 --------
 当存在零态射族时，这两个预层本身自然同构：两个分量在底层态射上都是恒等映射，唯一的内容是 [kill_fork] / [fork_kill]。这就是关系的准确表述——kill 形态既不更一般，也不更少；它是在 g := zmor 处的叉形态，通过一个重塑证明传输，这个重塑证明消耗了记录层的往返。
*)

Program Definition kill_fork_iso {C : Category} {ZM : ZeroMorphisms C}
  {x y : C} (f : x ~> y)
  : KillPresheaf f ≅[[C^op, Sets]] ForkPresheaf f zmor := {|
  to   := {| transform := fun d =>
               {| morphism := fun p : Kills f d => (`1 p; kill_fork f (`2 p)) |} |};
  from := {| transform := fun d =>
               {| morphism := fun p : Forks f zmor d => (`1 p; fork_kill f (`2 p)) |} |}
|}.
