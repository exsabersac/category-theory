Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Limit.
Require Import Category.Instance.Parallel.

Generalizable All Variables.

(* * * Equalizer of a parallel pair (a limit over the shape [Parallel]) / * * 并行对的等化器（形状 [Parallel] 的极限） *)

(*
 nLab:      https://ncatlab.org/nlab/show/equalizer
 Wikipedia: https://en.wikipedia.org/wiki/Equaliser_(mathematics)

 Given a parallel pair f, g : x ~> y in C, an equalizer is an object e
 together with an equalizing map i : e ~> x that equalizes the pair,

 f ∘ i ≈ g ∘ i,

 and is universal with this property: for every object n and every map
 m : n ~> x with f ∘ m ≈ g ∘ m there is a unique u : n ~> e with i ∘ u ≈ m
 (Wikipedia; nLab calls i the "equalizing map" and e the universal such
 object). Equivalently the equalizer is the limit of the parallel-pair
 diagram

 e ~> x ⇉ y,

 i.e. the limit over the two-object/two-arrow shape [Parallel] (see
 [Instance/Parallel.v]). That is exactly how it is defined here: an
 [Equalizer] is a [Limit] of a functor F : Parallel ⟶ C.

 This file does not restate the equalizing map or the universal property as
 fresh fields; they are inherited from [Limit] (see [Structure/Limit.v]).
 Under the shape [Parallel] the limit cone's two legs are the equalizing map
 i (the leg over [ParX], landing in x) and its composite with the pair (the
 leg over [ParY], landing in y); the leg-coherence law forces f ∘ i ≈ g ∘ i,
 and [ump_limits] supplies the unique mediating u for every competing cone.
 Use [APair f g : Parallel ⟶ C] from [Instance/Parallel.v] to obtain the
 diagram F from an actual parallel pair f, g. 

 --------
 nLab：       https://ncatlab.org/nlab/show/equalizer 
 维基百科：  https://en.wikipedia.org/wiki/Equaliser_(mathematics) 

 给定一个在 C 中的平行对 f, g : x ~> y，等化器是一个对象 e
 以及一个等化映射 i : e ~> x，使这对映射等化，

 f ∘ i ≈ g ∘ i，

 并且具有以下普遍性：对于每一个对象 n 以及每一个映射
 m : n ~> x，满足 f ∘ m ≈ g ∘ m，存在唯一的 u : n ~> e
 使得 i ∘ u ≈ m（维基百科；nLab 称 i 为“等化映射”，e 为具有这种普遍性的对象）。
 等价地，等化器是平行对图的极限

 e ~> x ⇉ y，

 即两个对象/两条箭头形状 [Parallel] 的极限（参见 [Instance/Parallel.v]）。
 这正是这里的定义方式：一个 [Equalizer] 是函子 F : Parallel ⟶ C 的 [Limit]。此文件不会将等化映射或普遍性质重新声明为新字段；它们是从 [Limit] 继承的（见 [Structure/Limit.v]）。在形状 [Parallel] 下，极限锥的两条腿是等化映射 i（位于 [ParX] 上的腿，落在 x）及其与对 (位于 [ParY] 上的腿，落在 y) 的复合；腿的一致性律迫使 f ∘ i ≈ g ∘ i，而 [ump_limits] 为每一个竞争锥提供唯一的中介 u。使用 [APair f g : Parallel ⟶ C] 从 [Instance/Parallel.v] 获得实际平行对 f, g 的图 F。
*)

(*
 Where equalizers come from, and what they are for

 nLab:  https://ncatlab.org/nlab/show/coequalizer
 nLab:  https://ncatlab.org/nlab/show/regular+category
 Paper: Eckmann, Hilton, "Group-like structures in general categories
 II. Equalizers, limits, lengths", Mathematische Annalen 151, 1963
 Blog:  Milewski, "Limits and Colimits", Category Theory for
 Programmers, 2015

 Equalizers entered category theory in the second installment of Eckmann
 and Hilton's "Group-like structures" series (Mathematische Annalen 151,
 1963), which defined them for arbitrary finite families of parallel
 morphisms under the name "left equalizers", with coequalizers as "right
 equalizers" (nLab).  The same paper already contains the basic fact of
 the subject: the equalizing map is always a monomorphism (their
 Prop. 1.3), since the mediating morphism of the universal property is
 unique.  The older algebraic name "difference kernel" records the
 additive case: where morphisms subtract, the equalizer of f and g is
 the kernel of f − g, and conversely the kernel of f is the equalizer of
 f with zero (Wikipedia).  Structure/Kernel.v performs exactly that
 specialization, defining [IsKernel] as [IsEqualizer] against [zero_mor]
 and deriving [kernel_monic] from [equalizer_monic].

 The equalizer is the categorical solution set of an equation.  In Set
 it is the subset {s | f s = g s} together with its inclusion (nLab),
 and the universal property says that morphisms into the equalizer are
 the same thing as morphisms into x satisfying the equation: the
 equalizer represents solutions.  It follows from monicity that
 equalizers are a canonical source of subobjects — those carved out by
 an equation — and monomorphisms arising this way are called regular
 (Wikipedia).  In type theory the same object is the dependent sum over
 the identity type, Σ (a : A), f a = g a (nLab), which is the subset
 type {a : A | f a = g a} of Coq itself.  Milewski's programming
 account works over precisely this file's two-object shape: the cone
 condition collapses to a single equation, and "an equalizer can thus
 be used to solve equations of the type f x = g x" (Milewski, "Limits
 and Colimits", 2015).

 Two structural theorems give this one limit shape its weight.  First,
 completeness reduces to it: a category has all (finite) limits as soon
 as it has (finite) products and equalizers, every limit arising as an
 equalizer of two maps between products (Mac Lane, Categories for the
 Working Mathematician, 2nd ed. 1998, §V.2, "Limits by Products and
 Equalizers"), and a functor preserves all limits as soon as it
 preserves both primitives (nLab, "limit").  Second, the shape carries
 Freyd's adjoint functor theorem (Freyd, Abelian Categories, 1964; Mac
 Lane §V.6): a weakly initial family becomes an initial object by
 taking the product and then the joint equalizer of all its
 endomorphisms, monicity of the equalizer supplying the uniqueness half
 (nLab, "adjoint functor theorem").  Both arguments run in this
 library.  The reduction is Structure/Limit/FromProducts.v: each limit
 is the equalizer [limit_of_products_equalizer] between the product over
 the objects and the product over the arrows of the shape,
 [Complete_from_products_equalizers] packages that as [Complete], and a
 functor preserving both primitives is continuous
 ([continuous_from_products_equalizers]).  Freyd's step is
 [initial_from_weakly_initial] in Theory/WeaklyInitial.v, which
 consumes [HasEqualizers], and Adjunction/GAFT.v extracts that supply
 from completeness as [Complete_HasEqualizers], the reduction's
 converse.

 Dually, [Coequalizer] is the categorical quotient.  In Set the
 coequalizer of f and g is the quotient of y by the equivalence relation
 generated by f x ∼ g x, and epimorphisms arising as coequalizers are
 the regular ones (nLab).  The interplay between coequalizers and kernel
 pairs — a regular epimorphism with a kernel pair is the coequalizer of
 that kernel pair — is what a regular category axiomatizes (Barr,
 Grillet, van Osdol, Exact Categories and Categories of Sheaves,
 Springer LNM 236, 1971), yielding the (regular epi, mono) image
 factorization; see Structure/Regular.v and the packaged [Regular_OFS]
 in Structure/Regular/Factorization.v.  The sheaf condition is likewise
 an equalizer diagram — local data glue exactly when they agree on
 overlaps (nLab, "sheaf") — and Beck's monadicity theorem runs on the
 split and reflexive coequalizers of Structure/Coequalizer/Split.v and
 Structure/Coequalizer/Reflexive.v, consumed throughout
 Monad/Monadicity/.

 This file supplies only the limit-form definitions [Equalizer] and
 [Coequalizer].  The elementary fork presentation [IsEqualizer], with
 [equalizer_monic], [equalizer_unique], the supply class
 [HasEqualizers], and round trips to the bundled form here, lives in
 Structure/Equalizer/Fork.v; the dual cofork API is
 Structure/Coequalizer.v. 

 --------
 等化子来自哪里，以及它们的作用

 nLab:   https://ncatlab.org/nlab/show/coequalizer 
 nLab:   https://ncatlab.org/nlab/show/regular+category 
 论文: Eckmann, Hilton, “一般范畴中的类似群结构 II. 等化子, 极限, 长度”, 数学年刊 151, 1963
 博客: Milewski, “极限与余极限”, 面向程序员的范畴论, 2015在Eckmann和Hilton《类群结构》系列的第二部分（Mathematische Annalen 151, 1963）中，等化器进入了范畴论，该文将其定义为任意有限族平行态射的“左等化器”，并将余等化器称为“右等化器”（nLab）。同一篇论文已经包含了该主题的基本事实：等化映射总是单态射（他们的命题1.3），因为泛性质的中介态射是唯一的。较早的代数名称“差核”记录了加法情形：在态射可相减的情况下，f和g的等化器是f − g的核，反之，f的核是f与零的等化器（Wikipedia）。Structure/Kernel.v 正是执行了那种特化，定义 [IsKernel] 为相对于 [zero_mor] 的 [IsEqualizer]，并从 [equalizer_monic] 推导出 [kernel_monic]。等化器是一个方程的范畴解集。在集合论中，它是子集 {s | f s = g s} 及其包含 (nLab)，并且其泛性质表明，指向等化器的态射与指向 x 且满足该方程的态射是相同的：等化器表示解。从单射性可以推出，等化器是子对象的规范来源——那些由方程划定的子对象——通过这种方式产生的单态射称为正规单射 (Wikipedia)。在类型理论中，同一对象是对等式类型的依赖和，即 Σ (a : A), f a = g a (nLab)，它是 Coq 本身的子集类型 {a : A | f a = g a}。Milewski 的编程方法正好适用于这个文件的两对象形状：锥条件简化为一个方程，因此“可以使用均衡器来求解类型为 f x = g x 的方程”（Milewski，《极限与余极限》，2015）。有两个结构定理赋予了这个极限形状它的权重。首先，完备性可以归约到它：一个范畴一旦具有（有限）积和等化器，就具有所有（有限）极限，每个极限都可以作为两个积之间映射的等化器（Mac Lane，《为工作数学家准备的范畴论》，第2版，1998年，第V.2节，“通过积和等化器的极限”），而一个函子一旦保持这两个基本元就保持所有极限（nLab，“极限”）。其次，这个形状承载Freyd的伴随函子定理（Freyd，《阿贝尔范畴》，1964年；Mac Lane §V.6）：一个弱初始族通过取其积然后对所有自同态的联合等化器，可以变成初始对象，等化器的单性提供了唯一性部分（nLab，“伴随函子定理”）。这两个论证都在此库中运行。约简位于 Structure/Limit/FromProducts.v：每个极限都是形状中对象的积与箭头的积之间的等化器 [limit_of_products_equalizer]，[Complete_from_products_equalizers] 将其打包为 [Complete]，并且保留这两种原始操作的函子是连续的（[continuous_from_products_equalizers]）。Freyd 的步骤在 Theory/WeaklyInitial.v 中是 [initial_from_weakly_initial]，它使用 [HasEqualizers]，而 Adjunction/GAFT.v 从完备性中提取该供给作为 [Complete_HasEqualizers]，即约简的逆向过程。同样地，[Coequalizer] 是范畴商。在集合中，f 和 g 的余等化子是 y 关于由 f x ∼ g x 生成的等价关系的商，而作为余等化子出现的满射是正规满射（nLab）。余等化子与核对的相互作用——具有核对的正规满射就是该核对的余等化子——正是正规范畴公理化的内容（Barr, Grillet, van Osdol, Exact Categories and Categories of Sheaves, Springer LNM 236, 1971），由此得到（正规满射, 单射）像分解；参见 Structure/Regular.v 以及 Structure/Regular/Factorization.v 中打包的 [Regular_OFS]。层条件同样是一个等化器图——当局部数据在重叠部分一致时，它们可以粘合 (nLab, "sheaf")——而 Beck 的幺半单性定理依赖于 Structure/Coequalizer/Split.v 和 Structure/Coequalizer/Reflexive.v 中的分裂和自反等化器，在 Monad/Monadicity/ 中被广泛使用。

 这个文件仅提供极限形式的定义 [Equalizer] 和 [Coequalizer]。基础叉表示法 [IsEqualizer]，配合 [equalizer_monic]、[equalizer_unique]、供应类 [HasEqualizers]，以及到捆绑形式的往返操作，存在于 Structure/Equalizer/Fork.v；对偶的共叉 API 则在 Structure/Coequalizer.v。
*)

(*
 The equalizer of the parallel-pair diagram F: a terminal cone over the
 shape [Parallel], whose limit-cone leg over [ParX] is the equalizing map
 and whose universal property is the equalizer's unique factorization. 

 --------
 平行对图 F 的等化器：一个位于形状 [Parallel] 上的末端锥，其在 [ParX] 上的极限锥支腿是等化映射，其泛性质是等化器的唯一分解。
*)
Definition Equalizer {C : Category} (F : Parallel ⟶ C) := Limit F.

(*
 The coequalizer is the dual notion (nLab, Wikipedia: "obtained by reversing
 the arrows"): a colimit over the same shape [Parallel], i.e. a limit of the
 opposite diagram. Dually it is an object q with a coequalizing map
 q : y ~> q satisfying q ∘ f ≈ q ∘ g, universal among such maps. 

 --------
 余等化子是对偶概念（nLab, 维基百科：“通过反转箭头获得”）：它是相同形状 [Parallel] 上的余极限，即对偶图的极限。对偶地，它是一个对象 q 以及一个余等化映射 q : y ~> q，满足 q ∘ f ≈ q ∘ g，并且在所有此类映射中是普遍的。
*)
Definition Coequalizer {C : Category} (F : Parallel ⟶ C) := Colimit F.
