Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.
Require Import Category.Instance.Top.Cocomplete.

Generalizable All Variables.

(* * * The separation axioms T0, T1, T2 over [PTopCat], and their reflections / * * 分离公理 T0、T1、T2 在 [PTopCat] 上及其反射 *)

(*
 Mac Lane, “Categories for the Working Mathematician”, 2nd ed. (GTM 5),
 §V.9, book p. 136 (PDF p. 145), read from the page image, Exercise 4:
 “Construct left adjoints for each of the inclusion functors
 Top_{n+1} → Top_n, n = 0, 1, 2, 3, where Top_n denotes the full
 subcategory of all T_n-spaces in Top, with T_4 = Normal,
 T_3 = Regular, T_2 = Hausdorff, etc.” (catalog id maclane:V.9:ex4).
 The rungs n = 0 and n = 1 are here; Instance/Top/Hausdorff.v
 delivers n = 2 and discusses the book's n = 3 in its header.
 nLab:      https://ncatlab.org/nlab/show/separation+axioms
 nLab:      https://ncatlab.org/nlab/show/Hausdorff+space
 Wikipedia: https://en.wikipedia.org/wiki/Separation_axiom

 BACKGROUND.  The separation axioms grade how well the opens of a space
 tell its points apart.  Wikipedia's separation-axiom page states them
 classically: T0, distinct points are topologically distinguishable;
 T1, distinct points are separated; T2 (Hausdorff), distinct points
 are separated by neighbourhoods.  The same page records that “the
 precise definitions of the separation axioms have varied over time”,
 the meanings of “normal” and “T4”, and of “regular” and “T3”, being
 sometimes interchanged.  nLab's separation-axioms page proves, for
 n ∈ {0, 1, 2}, that every space has a closest T_n approximation from
 the left, the T_n-reflection, and constructs it once as the quotient
 identifying two points exactly when every surjection onto a T_n space
 identifies them.  Mac Lane's Exercise 4 asks for these reflections
 one rung at a time.  nLab's Hausdorff-space page gives, beside the
 classical definition, a constructive one: if every neighbourhood of x
 meets (has inhabited intersection with) every neighbourhood of y,
 then x = y.  That page reads it as saying that equality is closed in
 S × S.

 THE POSITIVE FORMS.  Each axiom here says that a relation read off
 the opens forces the points' equality, [PSep prem X] for a premise
 [prem : SepPremise]:
 - [prem_T0]: the two points lie in the same opens;
 - [prem_T1]: every open containing the first contains the second;
 - [prem_T2], read at a space as [PNotSep]: every open about the
 first meets every open about the second.
 [PT0], [PT1] and [PHaus] are the three axioms, and [PHaus] is nLab's
 constructive definition, read with open neighbourhoods
 ([PHaus_unfold]).  The classical form, distinct points have disjoint
 neighbourhoods, which Mac Lane uses without defining it (book p. 158,
 §VI.9), is [PIsHausdorff], the negative form that Instance/Top.v's
 [IsHausdorff] takes over [Top].
 Four bridges relate them: [PIsHausdorff_PHaus], negative to positive,
 given that the points' equality is stable under double negation;
 [PHaus_PIsHausdorff], positive to negative, given excluded middle for
 propositions as a hypothesis; and, with no hypothesis, only
 [PIsHausdorff_PHaus_nn] (for points no two opens separate, the
 negative form refutes that they differ) and
 [PHaus_distinct_not_notsep] (for distinct points, the positive form
 refutes that no two opens separate them).  The positive form is the
 one the constructions need: its conclusion is the points' equality,
 so a limit inherits it through legs that are jointly injective
 (Instance/Top/Complete.v's [plimit_points_jointly_monic]), and it is
 what the reflection below forces; the negative form concludes an
 existential over opens.  The chain T2 ⇒ T1 ⇒ T0 ([PHaus_PT1],
 [PT1_PT0]) is constructive.  Over [Top], Instance/Top/Kolmogorov.v's
 [Hausdorff_T0_nn] gets only a double negation from the negative
 form.  [PHaus_PropEquiv]: a Hausdorff space's equality is
 propositional, [PNotSep] being a proposition equivalent to it.

 THE REFLECTION.  A premise with three laws ([SepLaws]: [sl_anti],
 [sl_pull], [sl_equiv]) determines [sepeq prem X], the intersection of
 the separating relations on X's points ([SepRel]: equivalences
 coarser than the points' equality that the premise, read in the opens
 saturated for them, forces), a proposition by impredicativity.
 [SepQuot prem X] is X's points under [sepeq] with the quotient
 topology of Instance/Top/Subspace.v's [PQuot], separated by
 [SepQuot_sep].  A map into a separated space factors through it by
 [sepquot_med], whose respect for [sepeq] reads the map's kernel through
 the premise ([sep_ker]), a proposition, where the target's own
 equality is Type-valued.  [PSep_Reflective prem L : Reflective
 (PSepSub prem)] assembles the reflection from universal arrows, with
 [PSepSub prem] the full subcategory [PFullSub (PSep prem)] of
 [PTopCat].  [PT0_Reflective], [PT1_Reflective] and [PT2_Reflective]
 are its instances, the largest T0, T1 and Hausdorff quotients.  No
 classical premise is used anywhere.  [PT0_Reflective] is the
 counterpart over [PTopCat] of Instance/Top/Kolmogorov.v's
 [T0_Reflective_in_Top] over [Top]; the two are not compared.

 EXERCISE 4 AT n = 0 AND n = 1.  [restrict_Reflective] is general: if
 B ⊆ A are full subcategories of a category C and B is reflective in C,
 then B read inside A ([restrict_sub]) is reflective in A, by
 reflecting in C.  At B = T1, A = T0 it is [PT1_in_PT0_Reflective],
 Mac Lane's Top_1 → Top_0; at B = T2, A = T1 it is
 [PHaus_in_PT1_Reflective], his Top_2 → Top_1.  Instance/Top/
 Hausdorff.v applies the same lemma to the reflections it obtains by
 the adjoint functor theorem, for the rungs n = 0, 1 and 2.

 STRICTNESS OF EVERY INCLUSION.  [PTwoIndisc_not_PT0] (the indiscrete
 two points of Instance/Top/Cocomplete.v); [PSierpinski_PT0] and
 [PSierpinski_not_PT1] (Sierpiński space, [true] open);
 [PCofinite_PT1] and [PCofinite_not_PHaus] (the cofinite topology on
 the naturals, stated as “a nonempty open contains a tail [N, ∞)”,
 which needs no finiteness predicate).  Inhabitation: [PBool_PHaus]
 (the discrete two points are Hausdorff; the proof states the goal as
 a Leibniz equality before eliminating the premise's [ex], which into
 the setoid's Type-valued equality is refused, Test/
 ProbeHausdorff461.v's N10).  The arithmetic is four lemmas proved
 from the prelude ([sep_le_trans], [sep_le_add_r], [sep_le_add_l],
 [sep_not_succ_le]), so that the file requires no standard-library
 module of its own.  [PSep_retract]: a retract of a separated space is
 separated.

 STRENGTHS.  At [eq_refl]: [PHaus_unfold]; [SepQuot_carrier] and
 [SepQuot_equiv] (the quotient keeps X's points, and its equality IS
 [sepeq]); [PSep_reflector_obj] and [PSep_unit_point] (the reflector's
 object is [SepQuot], and its unit is the identity on points);
 [PT1_in_PT0_obj] and [PT1_in_PT0_unit_point] (the same for the
 restricted reflection).  The action on maps is not at [eq_refl]:
 [pmap (`1 (fmap[PSep_reflector prem L] f)) x = pmap f x] at [eq_refl]
 is refused, pinned as Test/ProbeHausdorff461.v's N9 (cannot unify
 “projT1 (fmap[PSep_reflector prem L] f) x” and “f x”), and no such
 readback is claimed; up to the reflection's equality it holds, by the
 unit's naturality (that file's [p461_fmap_equiv]).  Two [Defined],
 counted by token ([sep_universal], [restrict_universal]), chosen by
 the data convention, a mediator being data.  Neither is
 load-bearing: each flipped alone to [Qed], in scratch copies of the
 development's three files and of Test/ProbeHausdorff461.v, leaves
 every readback of the four accepted.  45 [Qed], counted by token.

 UNIVERSES, read by [About] under [Set Printing Universes] on all 105
 constants of this file's [Print Module] listing (the record
 constructor [Build_SepLaws] among them; the file has no [Program]
 obligation and no inductive type).
 - The premises, axioms, laws, bridges, the quotient and its
 mediator, [PSep_retract]: [@{o}] with an empty block, except
 [sepquot_med], with three [o <= compose.u*] stdlib caps, which
 Instance/Top/Subspace.v's [pquot_desc] carries in its own block.
 [SepPremise@{o} : Type@{max(Set+1,o+1)}], the sort of a family of
 Prop-valued predicates on [Type@{o}].
 - The named spaces and their lemmas: [@{o}] with the one stdlib cap
 [o <= Logic_lemmas.equality.u0], [eq_Setoid]'s own.
 - [PFullSub], [PFullSub_Full], [PSepSub]: [@{o so}] with [o < so]
 and [Set < so], [PTopCat]'s block (Instance/Top/Prop.v's header:
 the [Set < so] records [PTop]'s sort).
 - [PSepSpaces], [PSepObj], [sep_proj], [sep_universal]: [@{o so u}],
 adding [o < u], Construction/Subcategory.v's [Sub]'s auxiliary
 above the hom universe (its own block's [u0 < u5]).
 - The reflections ([PSep_reflector], [PSep_adj], [PSep_Reflective],
 its three instances, the restricted two, and the readbacks over
 them): that block plus auxiliaries related only by [<=] (seven
 universes for [PSep_Reflective], eleven for the restricted two),
 and the strict stdlib caps [Set < Projections.u0] and
 [o < Projections.u0], first carried, in dependency order, by
 [sep_universal]: the first projection of an object of the
 subcategory, a dependent pair over [PTop@{o}], whose sort is
 [Type@{max(Set+1,o+1)}] (measured: a bare [projT1] of such a pair
 carries exactly these two caps).
 - [restrict_sub] through [restrict_Reflective]: generic in the
 category and its two subcategories.  The section declares the ten
 universes of its hypotheses, [co] through [rd], and each constant
 adds its own, up to 22 in all ([restrict_Reflective]); no [Set]
 and no strict stdlib cap.
 - The four arithmetic lemmas: [@{}].
 - No block carries an equation.  A word count of [Set] over the
 [About] output of the 105 constants reads 35: [SepPremise]'s sort
 once, [Set < so] in 20 blocks, [Set < Projections.u0] in 14.  No
 block carries [Set < o]: [PT2_Reflective] and
 [PT1_in_PT0_Reflective] are accepted with their points in [Set]
 (Test/ProbeHausdorff461.v's [p461_direct_set] and
 [p461_n0_direct_set]).

 NOT DELIVERED.  Exercise 4 at n = 2 (delivered in Instance/Top/
 Hausdorff.v, by the adjoint functor theorem) and at n = 3 (not
 formalized; that file's header); a direct construction of a regular
 reflection;
 a comparison of [PT0] with Instance/Top/Kolmogorov.v's [IsT0], or of
 [PHaus] with Instance/Top.v's [IsHausdorff], across the two encodings
 (the tree has no functor between [Top] and [PTopCat]); the
 reflectors' action on maps at [eq_refl]; a proof that the positive
 and negative Hausdorff forms part constructively (only the bridges
 under the stated hypotheses are here); negative forms of T0 and T1. 

 --------
 Mac Lane，《面向工作数学家的范畴论》，第2版（GTM 5），§V.9，第136页（PDF第145页），根据页面图像阅读，练习4：
 “为每个包含函子构造左伴随函子
 Top_{n+1} → Top_n，n = 0, 1, 2, 3，其中Top_n表示Top中所有T_n空间的完全子范畴，T_4 = 正规空间，
 T_3 = 正则空间，T_2 = 豪斯多夫空间，等等。”（目录编号 maclane:V.9:ex4）。
 这里涉及阶 n = 0 和 n = 1；Instance/Top/Hausdorff.v 提供 n = 2，并在其标题中讨论书中的 n = 3。
 nLab：https://ncatlab.org/nlab/show/separation+axioms
 nLab：https://ncatlab.org/nlab/show/Hausdorff+space
 维基百科：https://en.wikipedia.org/wiki/Separation_axiom背景。分离公理衡量一个空间的开集在多大程度上能够区分其点。维基百科的分离公理页面以经典方式陈述它们：T0，不同的点在拓扑上可区分；T1，不同的点被分离；T2（豪斯多夫），不同的点可通过邻域分离。同一页面记录说“分离公理的精确定义随着时间有所不同”，而“正规”和“T4”，以及“正则”和“T3”的含义有时会互换。nLab的分离公理页面证明，对于 n ∈ {0, 1, 2}，每个空间都存在一个来自左边的最接近的 T_n 近似，即 T_n 反射，并通过商空间构造它：仅当每个到 T_n 空间的满射将两个点识别为同一点时才将它们等同起来。麦克·莱恩的练习 4 要求对这些反思逐步进行。nLab 的豪斯多夫空间页面除了提供经典定义外，还提供了一个构造性定义：如果 x 的每一个邻域都与 y 的每一个邻域相交（有非空交集），那么 x = y。该页面将其理解为在 S × S 中等式是闭合的。正形式。这里的每个公理都说，从开集读取的关系会强制点的相等性，对于前提 [prem : SepPremise] ：
 - [prem_T0] ：两个点位于相同的开集中；
 - [prem_T1] ：包含第一个点的每个开集都包含第二个点；
 - [prem_T2]，在一个空间中读作 [PNotSep] ：每个关于第一个点的开集都与每个关于第二个点的开集相交。[PT0]、[PT1] 和 [PHaus] 是三个公理，而 [PHaus] 是 nLab 的构造性定义，用开邻域 ([PHaus_unfold]) 来阅读。经典形式，互异点有不相交的邻域，Mac Lane 在书中第 158 页 §VI.9 中使用而未定义它，是 [PIsHausdorff]，Instance/Top.v 的负形式 [IsHausdorff] 接管 [Top]。四座桥将它们联系起来：[PIsHausdorff_PHaus]，从负到正，假设点的相等在双重否定下是稳定的；[PHaus_PIsHausdorff]，从正到负，假设命题采排中律；并且在没有假设下，只有[PIsHausdorff_PHaus_nn]（对于没有两个开集可以将其分离的点，负形式否定它们不同）和[PHaus_distinct_not_notsep]（对于不同的点，正形式否定没有两个开集可以分离它们）。正形式是构造所需要的：其结论是点的相等，因此极限通过共同单射的腿继承它（Instance/Top/Complete.v 的 [plimit_points_jointly_monic]），并且这是下面反射强制的；负形式的结论是关于开集的存在量词。链 T2 ⇒ T1 ⇒ T0（[PHaus_PT1], [PT1_PT0]）是构造性的。在 [Top] ，实例/顶/Kolmogorov.v 中，
 [Hausdorff_T0_nn]  只从否定形式中得到双重否定。[PHaus_PropEquiv] ：豪斯多夫空间的相等是命题性的，[PNotSep]  是一个与之等价的命题。反映。一个具有三条定律的前提（[SepLaws] ： [sl_anti], [sl_pull], [sl_equiv]）决定了 [sepeq prem X]，即 X 的点上的分离关系的交集（[SepRel]：比点相等更粗糙的等价关系，前提在它们的开饱和下解读时所强制的），这是一个通过不可定义性得到的命题。[SepQuot prem X] 是在 [sepeq] 下的 X 的点，带有 Instance/Top/Subspace.v 的 [PQuot] 的商拓扑，由 [SepQuot_sep] 分离。映射到一个分离空间的映射可以通过 [sepquot_med] 因式分解，其对 [sepeq] 的尊重通过前提（[sep_ker]）解读映射的核，该命题的目标自身的相等性是类型值的。[PSep_Reflective prem L : Reflective (PSepSub prem)] 从通用箭头组装反射，[PSepSub prem] 是 [PTopCat] 的全子范畴 [PFullSub (PSep prem)]。[PT0_Reflective]、[PT1_Reflective] 和 [PT2_Reflective] 是它的实例，即最大的 T0、T1 和 Hausdorff 商。任何地方都没有使用经典前提。[PT0_Reflective] 是 Instance/Top/Kolmogorov.v 中 [T0_Reflective_in_Top] 在 [Top] 上的对应物在 [PTopCat] 上；两者未进行比较。练习 4 在 n = 0 和 n = 1。[restrict_Reflective] 是一般性的：如果 B ⊆ A 是一个范畴 C 的满子范畴，并且 B 在 C 中是反射的，那么在 A 中读取的 B（[restrict_sub]）在 A 中是反射的，通过在 C 中反射。当 B = T1，A = T0 时，它是 [PT1_in_PT0_Reflective]，Mac Lane 的 Top_1 → Top_0；当 B = T2，A = T1 时，它是 [PHaus_in_PT1_Reflective]，他的 Top_2 → Top_1。Instance/Top/Hausdorff.v 将相同的引理应用于它通过伴随函子定理获得的反射，对于阶梯 n = 0、1 和 2。每个包含的严格性。[PTwoIndisc_not_PT0]（Instance/Top/Cocomplete.v中的不离散两点）；[PSierpinski_PT0] 和 [PSierpinski_not_PT1]（Sierpiński 空间，[true] 开）；[PCofinite_PT1] 和 [PCofinite_not_PHaus]（自然数上的余有限拓扑，表述为“非空开集包含一个尾 [N, ∞)”，这不需要有限性谓词）。存在性：[PBool_PHaus]（离散两点是豪斯多夫的；证明在消除前提的 [ex] 之前将目标陈述为莱布尼茨等式，这在集合等价的类型值等式中被拒绝，见 Test/ProbeHausdorff461.v 的 N10）。算术是从前导证明的四个引理（[sep_le_trans]、[sep_le_add_r]、[sep_le_add_l]、[sep_not_succ_le]），因此该文件不需要自己的标准库模块。[PSep_retract]：分离空间的一个重traction是分离的。优势。在 [eq_refl]：[PHaus_unfold]；[SepQuot_carrier] 和 [SepQuot_equiv]（商保持 X 的点，且其等式为 [sepeq]）；[PSep_reflector_obj] 和 [PSep_unit_point]（反射器的对象是 [SepQuot]，其单位是点上的恒等映射）；[PT1_in_PT0_obj] 和 [PT1_in_PT0_unit_point]（受限反射的情况相同）。在映射上的作用不在 [eq_refl]：[pmap (`1 (fmap[PSep_reflector prem L] f)) x = pmap f x] 在 [eq_refl] 被拒绝，标记为 Test/ProbeHausdorff461.v 的 N9（无法将 “projT1 (fmap [PSep_reflector prem L] f) x” 与 “f x” 统一），且没有此类回读被声称；根据反射等式，通过单位的自然性（该文件的 [p461_fmap_equiv]），这一点成立。两个 [Defined]，由标记（[sep_universal], [restrict_universal]）计数，按数据约定选择，中介是数据。两者都不是承重的：每个单独翻转到 [Qed]，在开发的三个文件和 Test/ProbeHausdorff461.v 的草稿副本中，都使四个读取回来的内容被接受。45 [Qed]，以标记计数。宇宙，由 [About] 在 [Set Printing Universes] 下读取，在此文件的所有 105 个常量的 [Print Module] 列表中（记录构造函数 [Build_SepLaws] 也在其中；该文件没有 [Program] 义务且没有归纳类型）。- 前提、公理、定律、桥梁、商及其中介，[PSep_retract]：[@{o}] 带有一个空块，除了 [sepquot_med]，带有三个 [o <= compose.u*] 标准库上限，其中 Instance/Top/Subspace.v 的 [pquot_desc] 在其自己的块中。[SepPremise@{o} : Type@{max(Set+1,o+1)}]，值为 [Type@{o}] 的 Prop 型谓词族的类型。- 命名空间及其引理：[@{o}] 带有一个标准库上限 [o <= Logic_lemmas.equality.u0]，[eq_Setoid] 自身。-  [PFullSub]、[PFullSub_Full]、[PSepSub]：[@{o so}] 具有 [o < so] 和 [Set < so]、[PTopCat] 的块（Instance/Top/Prop.v 的头部：[Set < so] 记录 [PTop] 的类型）。-  [PSepSpaces]、[PSepObj]、[sep_proj]、[sep_universal]：[@{o so u}]，添加 [o < u]，Construction/Subcategory.v 的 [Sub] 的辅助在同宇宙之上（其自身块的 [u0 < u5]）。- 反射（[PSep_reflector], [PSep_adj], [PSep_Reflective]，其三个实例，被限制的两个，以及对它们的回读）：该块加上仅通过[<=]相关的辅助（[PSep_Reflective]的七个宇宙，被限制的两个的十一），以及严格的stdlib上限[Set < Projections.u0]和[o < Projections.u0]，首先由[sep_universal]以依赖顺序携带：子类别对象的第一个投影，一个关于[PTop@{o}]的依赖对，其类别是[Type@{max(Set+1,o+1)}]（测量：这样一个对的裸[projT1]正好携带这两个上限）。- [restrict_sub]到[restrict_Reflective]：在该类别及其两个子类别中是通用的。该部分声明了其假设的十个宇宙，从 [co] 到 [rd]，每个常量都增加了自己的，总计达 22 个（[restrict_Reflective]）；没有 [Set]，也没有严格的标准库上限。- 四个算术引理：[@{}]。- 没有区块包含方程。105 个常量的 [About] 输出中的 [Set] 字数统计为 35：[SepPremise] 的排序为一次，[Set < so] 在 20 个区块中，[Set < Projections.u0] 在 14 个区块中。没有区块包含 [Set < o]：[PT2_Reflective] 和 [PT1_in_PT0_Reflective] 被接受，并在 [Set] 中标出它们的点（Test/ProbeHausdorff461.v 的 [p461_direct_set] 和 [p461_n0_direct_set]）。未交付。在 n = 2 时的练习 4（通过伴随函子定理在 Instance/Top/Hausdorff.v 中交付）以及 n = 3 时（未形式化；那个文件的头部）；一个正则反射的直接构造；将 [PT0] 与 Instance/Top/Kolmogorov.v 的 [IsT0] 进行比较，或者将 [PHaus] 与 Instance/Top.v 的 [IsHausdorff] 在两种编码之间进行比较（该树在 [Top] 与 [PTopCat] 之间没有函子）；反射器对 [eq_refl] 中映射的作用；证明正 Hausdorff 和负 Hausdorff 构造性组成部分（这里只涉及在指定假设下的桥）；T0 和 T1 的负形式。
*)

(* * ** Separation premises and the positive separation axioms / * ** 分离公理与正分离公理 *)

(*
 A separation premise reads a relation between two points off a family
 of opens on a type of points.  The positive separation axiom it
 determines says that the premise forces the points' equality. 

 --------
 一个分离前提读作在一类点的某种类型上，两个点之间的开放族关系。它确定的正分离公理表示该前提强制这些点相等。
*)
Definition SepPremise@{o} :=
  ∀ S : Type@{o}, ((S → Prop) → Prop) → S → S → Prop.

(* T0: the two points lie in the same opens. / T0: 这两个点位于相同的开集内。 *)
Definition prem_T0@{o} : SepPremise@{o} :=
  fun S O x y => ∀ U, O U → (U x <-> U y).

(* T1: every open containing the first point contains the second. / T1：包含第一个点的每个开集都包含第二个点。 *)
Definition prem_T1@{o} : SepPremise@{o} :=
  fun S O x y => ∀ U, O U → U x → U y.

(* T2: no two opens separate the points: every open about the first meets every open about the second. / T2：没有两个开集能将这两点分开：关于第一点的每个开集都与关于第二点的每个开集相交。 *)
Definition prem_T2@{o} : SepPremise@{o} :=
  fun S O x y => ∀ U V, O U → O V → U x → V y → ex (fun z => U z /\ V z).

Definition PSep@{o} (prem : SepPremise@{o}) (X : PTop@{o}) : Type@{o} :=
  ∀ x y : X, prem _ (POpen X) x y → x ≈ y.

Definition PT0@{o} (X : PTop@{o}) : Type@{o} := PSep@{o} prem_T0@{o} X.
Definition PT1@{o} (X : PTop@{o}) : Type@{o} := PSep@{o} prem_T1@{o} X.

(* The two points of a space cannot be separated by disjoint opens. / 空间中的两点不能被不相交的开集分开。 *)
Definition PNotSep@{o} (X : PTop@{o}) (x y : X) : Prop :=
  prem_T2@{o} _ (POpen X) x y.

(* Hausdorff, in the positive form: points that no two opens separate are equal. / 豪斯多夫，正形式：没有两个开集能将其分开的点是相等的。 *)
Definition PHaus@{o} (X : PTop@{o}) : Type@{o} := PSep@{o} prem_T2@{o} X.

Example PHaus_unfold@{o} (X : PTop@{o}) :
  PHaus X = (∀ x y : X, PNotSep X x y → x ≈ y) := eq_refl.

(* The classical Hausdorff axiom, the negative form, which Mac Lane uses without defining it (book p. 158, §VI.9): distinct points have disjoint neighbourhoods. / 经典的豪斯多夫公理，否定形式，Mac Lane 在书中未定义便使用（书第158页，第VI.9节）：不同的点有不相交的邻域。 *)
Definition PIsHausdorff@{o} (X : PTop@{o}) : Prop :=
  ∀ x y : X, (x ≈ y → False) →
    ex (fun U => ex (fun V => POpen X U /\ POpen X V /\ U x /\ V y /\
                              ∀ z, U z → V z → False)).

(** ** The chain T2 ⇒ T1 ⇒ T0 / ** 链 T2 ⇒ T1 ⇒ T0 *)

Lemma PSep_mono@{o} (pa pb : SepPremise@{o})
  (h : ∀ S O x y, pa S O x y → pb S O x y) (X : PTop@{o}) :
  PSep pb X → PSep pa X.
Proof. intros Hb x y p. exact (Hb x y (h _ _ x y p)). Qed.

Lemma prem_T0_T1@{o} S O x y : prem_T0@{o} S O x y → prem_T1@{o} S O x y.
Proof. intros H U HU. exact (proj1 (H U HU)). Qed.

Lemma prem_T1_T2@{o} S O x y : prem_T1@{o} S O x y → prem_T2@{o} S O x y.
Proof. intros H U V HU HV u v. exists y. exact (conj (H U HU u) v). Qed.

Corollary PHaus_PT1@{o} (X : PTop@{o}) : PHaus X → PT1 X.
Proof. exact (PSep_mono prem_T1 prem_T2 prem_T1_T2 X). Qed.

Corollary PT1_PT0@{o} (X : PTop@{o}) : PT1 X → PT0 X.
Proof. exact (PSep_mono prem_T0 prem_T1 prem_T0_T1 X). Qed.

(** ** The laws a premise needs / ** 一个前提所需的法律 *)

(*
 [sl_anti]: fewer opens relate more pairs.  [sl_pull]: the premise read
 through the opens pulled back along a function is carried forward by
 it.  [sl_equiv]: equal points satisfy the premise. 

 --------
 [sl_anti]：较少的开放与更多的配对相关。[sl_pull]：前提出过的通过沿函数拉回的开放被其传递。[sl_equiv]：相等的点满足前提。
*)
Record SepLaws@{o} (prem : SepPremise@{o}) : Prop := {
  sl_anti : ∀ (S : Type@{o}) (O O' : (S → Prop) → Prop),
      (∀ U, O U → O' U) → ∀ x y, prem S O' x y → prem S O x y;
  sl_pull : ∀ (S S' : Type@{o}) (f : S → S') (O' : (S' → Prop) → Prop)
      (x y : S),
      prem S (fun U => ex (fun W => O' W /\ ∀ s, U s <-> W (f s))) x y →
      prem S' O' (f x) (f y);
  sl_equiv : ∀ (X : PTop@{o}) (x y : X), x ≈ y → prem _ (POpen X) x y
}.

Lemma prem_T0_laws@{o} : SepLaws@{o} prem_T0@{o}.
Proof.
  constructor.
  - intros S O O' sub x y H U HU. exact (H U (sub U HU)).
  - intros S S' f O' x y H W HW.
    exact (H (fun s => W (f s)) (ex_intro _ W (conj HW (fun s => iff_refl _)))).
  - intros X x y e U HU; split; intro u.
    + exact (popen_proper X U HU x y e u).
    + exact (popen_proper X U HU y x (symmetry e) u).
Qed.

Lemma prem_T1_laws@{o} : SepLaws@{o} prem_T1@{o}.
Proof.
  constructor.
  - intros S O O' sub x y H U HU. exact (H U (sub U HU)).
  - intros S S' f O' x y H W HW.
    exact (H (fun s => W (f s)) (ex_intro _ W (conj HW (fun s => iff_refl _)))).
  - intros X x y e U HU u. exact (popen_proper X U HU x y e u).
Qed.

Lemma prem_T2_laws@{o} : SepLaws@{o} prem_T2@{o}.
Proof.
  constructor.
  - intros S O O' sub x y H U V HU HV. exact (H U V (sub U HU) (sub V HV)).
  - intros S S' f O' x y H W1 W2 H1 H2 w1 w2.
    destruct (H (fun s => W1 (f s)) (fun s => W2 (f s))
                (ex_intro _ W1 (conj H1 (fun s => iff_refl _)))
                (ex_intro _ W2 (conj H2 (fun s => iff_refl _))) w1 w2)
      as [z [a b]].
    exists (f z). exact (conj a b).
  - intros X x y e U V HU HV u v. exists y.
    exact (conj (popen_proper X U HU x y e u) v).
Qed.

(* The premise pulled back along a continuous map: what [sl_pull] and [sl_anti] give together, for the opens of two spaces. / 沿着连续映射拉回的前提：[sl_pull] 和 [sl_anti] 一起提供的内容，对于两个空间的开集。 *)
Lemma sep_pull_cont@{o} (prem : SepPremise@{o}) (L : SepLaws@{o} prem)
  (X Y : PTop@{o}) (f : PMor@{o} X Y) (x y : X) :
  prem _ (POpen X) x y → prem _ (POpen Y) (pmap f x) (pmap f y).
Proof.
  intro Hp.
  apply (sl_pull _ L _ _ (fun s => pmap f s) (POpen Y) x y).
  apply (sl_anti _ L _ _ (POpen X)); [|exact Hp].
  intros U [W [HW HUW]].
  apply (popen_respects X (fun s => W (pmap f s))).
  - intro s; exact (iff_sym (HUW s)).
  - exact (pcont f W HW).
Qed.

(** ** Full subcategories of spaces / ** 空间的完整子类别 *)

(* The full subcategory of [PTopCat] on the spaces with a property. / 在具有某种性质的空间上的 [PTopCat] 的完全子范畴。 *)
Definition PFullSub@{o so | o < so +} (Pr : PTop@{o} → Type@{o}) :
  Subcategory@{so o o o} PTopCat@{o so} :=
  @Build_Subcategory@{so o o o} PTopCat@{o so} Pr
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Lemma PFullSub_Full@{o so | o < so +} (Pr : PTop@{o} → Type@{o}) :
  Construction.Subcategory.Full@{so o o o so} PTopCat@{o so} (PFullSub Pr).
Proof. intros x y ox oy g; exact I. Qed.

(* * ** The largest separated quotient, directly / * ** 最大的分离商，直接 *)

Section Quot.

Universe o.

Variable prem : SepPremise@{o}.
Variable L : SepLaws@{o} prem.

Context (X : PTop@{o}).

Local Notation P := (carrier (pt_carrier X)).

(* The opens of X saturated for a relation. / X 的开集为了一个关系被饱和。 *)
Definition sep_qopen (R : P → P → Prop) (U : P → Prop) : Prop :=
  POpen X U /\ ∀ a b, R a b → U a → U b.

(*
 A separating relation: an equivalence coarser than the points' own,
 which the premise read in the saturated opens forces. 

 --------
 一个分离关系：一种比点自身更粗的等价关系，它由前提在饱和开集中的读取所迫使。
*)
Definition SepRel (R : P → P → Prop) : Prop :=
  (∀ a, R a a) /\ (∀ a b, R a b → R b a) /\
  (∀ a b c, R a b → R b c → R a c) /\
  (∀ a b : P, a ≈ b → R a b) /\
  (∀ a b, prem P (sep_qopen R) a b → R a b).

(* Their intersection, a proposition by impredicativity. / 它们的交集，是一个由不可定义性提出的命题。 *)
Definition sepeq (a b : P) : Prop := ∀ R, SepRel R → R a b.

Lemma sepeq_refl (a : P) : sepeq a a.
Proof. intros R HR. exact (proj1 HR a). Qed.

Lemma sepeq_sym (a b : P) : sepeq a b → sepeq b a.
Proof. intros e R HR. exact (proj1 (proj2 HR) a b (e R HR)). Qed.

Lemma sepeq_trans (a b c : P) : sepeq a b → sepeq b c → sepeq a c.
Proof.
  intros e1 e2 R HR.
  exact (proj1 (proj2 (proj2 HR)) a b c (e1 R HR) (e2 R HR)).
Qed.

Lemma sepeq_of_equiv (a b : P) : a ≈ b → sepeq a b.
Proof. intros e R HR. exact (proj1 (proj2 (proj2 (proj2 HR))) a b e). Qed.

Definition sep_setoid : SetoidObject@{o o} :=
  {| carrier := P;
     is_setoid := {| equiv := sepeq;
                     setoid_equiv := Build_Equivalence sepeq sepeq_refl
                                       sepeq_sym sepeq_trans |} |}.

Definition sep_q :
  @SetoidMorphism@{o o o} _ (is_setoid (pt_carrier X)) _
    (is_setoid sep_setoid) :=
  @Build_SetoidMorphism _ (is_setoid (pt_carrier X)) _ (is_setoid sep_setoid)
    (fun x => x) sepeq_of_equiv.

(* The quotient: X's points under [sepeq], with the quotient topology. / 商空间：在 [sepeq] 下 X 的点，带商拓扑。 *)
Definition SepQuot : PTop@{o} := PQuot X sep_setoid sep_q.

Lemma SepQuot_sep : PSep prem SepQuot.
Proof using L.
  intros x y H R HR.
  apply (proj2 (proj2 (proj2 (proj2 HR)))).
  apply (sl_anti _ L P (sep_qopen R) (POpen SepQuot)); [|exact H].
  intros U [HU HsU]. split.
  - intros t t' e u. exact (HsU t t' (e R HR) u).
  - exact HU.
Qed.

Section Med.

Context (H : PTop@{o}) (HH : PSep prem H) (f : PMor@{o} X H).

(*
 The kernel of [f], read through the premise: a proposition, and
 equivalent to [pmap f a ≈ pmap f b] since [H] is separated. 

 --------
 [f] 的核心，通过前提阅读：一个命题，并且等同于 [pmap f a ≈ pmap f b]，因为 [H] 被分开。
*)
Definition sep_ker (a b : P) : Prop :=
  prem _ (POpen H) (pmap f a) (pmap f b).

Lemma sep_ker_to (a b : P) : sep_ker a b → pmap f a ≈ pmap f b.
Proof using HH. exact (HH _ _). Qed.

Lemma sep_ker_of (a b : P) : pmap f a ≈ pmap f b → sep_ker a b.
Proof using L. exact (sl_equiv _ L H _ _). Qed.

Lemma sep_ker_SepRel : SepRel sep_ker.
Proof using L HH.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - intro a. apply sep_ker_of. reflexivity.
  - intros a b e. apply sep_ker_of. symmetry. exact (sep_ker_to a b e).
  - intros a b c e1 e2. apply sep_ker_of.
    transitivity (pmap f b);
      [exact (sep_ker_to _ _ e1)|exact (sep_ker_to _ _ e2)].
  - intros a b e. apply sep_ker_of. exact (proper_morphism (pmap f) a b e).
  - intros a b Hp. unfold sep_ker.
    apply (sl_pull _ L P _ (fun s => pmap f s) (POpen H) a b).
    apply (sl_anti _ L P _ (sep_qopen sep_ker)); [|exact Hp].
    intros U [W [HW HUW]]. split.
    + apply (popen_respects X (fun s => W (pmap f s))).
      * intro s; exact (iff_sym (HUW s)).
      * exact (pcont f W HW).
    + intros a' b' e u. apply (proj2 (HUW b')). apply (proj1 (HUW a')) in u.
      exact (popen_proper H W HW _ _ (sep_ker_to a' b' e) u).
Qed.

Lemma sepquot_med_resp (a b : P) : sepeq a b → pmap f a ≈ pmap f b.
Proof using L HH.
  intro e. exact (sep_ker_to a b (e sep_ker sep_ker_SepRel)).
Qed.

Definition sepquot_med_setoid :
  @SetoidMorphism@{o o o} _ (is_setoid sep_setoid) _
    (is_setoid (pt_carrier H)) :=
  @Build_SetoidMorphism _ (is_setoid sep_setoid) _ (is_setoid (pt_carrier H))
    (fun a => pmap f a) sepquot_med_resp.

Definition sepquot_med : PMor@{o} SepQuot H :=
  pquot_desc X sep_setoid sep_q H f sepquot_med_setoid
    (fun x => reflexivity (pmap f x)).

End Med.

End Quot.

Section Reflection.

Universes o so.
Constraint o < so.

Variable prem : SepPremise@{o}.
Variable L : SepLaws@{o} prem.

(* The full subcategory of separated spaces, and the reflection into it. / 分离空间的完整子范畴，以及对它的反射。 *)
Definition PSepSub : Subcategory PTopCat@{o so} := PFullSub (PSep prem).

Definition PSepSpaces : Category := Sub PTopCat@{o so} PSepSub.

Definition PSepObj (X : PTopCat@{o so}) : PSepSpaces :=
  (SepQuot prem X; SepQuot_sep prem L X).

Definition sep_proj (X : PTopCat@{o so}) :
  X ~{PTopCat@{o so}}~> Incl PTopCat@{o so} PSepSub (PSepObj X) :=
  pquot_proj X (sep_setoid prem X) (sep_q prem X).

Definition sep_universal (X : PTopCat@{o so}) :
  ∀ (d : PSepSpaces) (f : X ~{PTopCat@{o so}}~> Incl PTopCat@{o so} PSepSub d),
    ∃! g : PSepObj X ~{PSepSpaces}~> d,
      f ≈ fmap[Incl PTopCat@{o so} PSepSub] g ∘ sep_proj X.
Proof using L.
  intros d f.
  unshelve eexists.
  - exact (sepquot_med prem L X (`1 d) (`2 d) f; I).
  - intro x; simpl; reflexivity.
  - intros g Hg x; simpl. exact (Hg x).
Defined.

Definition sep_ua (X : PTopCat@{o so}) :
  @UniversalArrow PTopCat@{o so} PSepSpaces X (Incl PTopCat@{o so} PSepSub) :=
  @universal_arrow_from_UMP PTopCat@{o so} PSepSpaces X
    (Incl PTopCat@{o so} PSepSub) (PSepObj X) (sep_proj X) (sep_universal X).

Definition PSep_reflector : PTopCat@{o so} ⟶ PSepSpaces :=
  LeftAdjointFunctorFromUniversalArrows (Incl PTopCat@{o so} PSepSub) sep_ua.

Definition PSep_adj : PSep_reflector ⊣ Incl PTopCat@{o so} PSepSub :=
  AdjunctionFromUniversalArrows (Incl PTopCat@{o so} PSepSub) sep_ua.

Definition PSep_Reflective : Reflective PSepSub :=
  @Build_Reflective PTopCat@{o so} PSepSub (PFullSub_Full _) PSep_reflector
    PSep_adj.

End Reflection.

(* * ** Restricting a reflection to an intermediate full subcategory / * ** 将反射限制到中间全子范畴 *)

(* If B ⊆ A are full subcategories of C and B is reflective in C, then B, read as a full subcategory of A, is reflective in A: reflect in C and read the result back in A. / 如果 B ⊆ A 是 C 的完全子范畴，并且 B 在 C 中是反射的，那么 B，作为 A 的完全子范畴，可以在 A 中反射：在 C 中反射然后将结果读回 A。 *)
Section Restrict.

(*
 [co], [ch]: the objects and homs of C; [sa], [sah]: A's predicates on
 objects and on arrows; [sb]: B's on objects; [fa]: A's fullness; [ra]
 through [rd]: the auxiliaries of B's reflection. 

 --------
 [co]，[ch]：C 的对象和态射；[sa]，[sah]：A 在对象和态射上的谓词；[sb]：B 在对象上的谓词；[fa]：A 的满性；[ra] 到 [rd]：B 反射的辅助构件。
*)
Universes co ch sa sah sb fa ra rb rc rd.

Context {C : Category@{co ch ch}} (SA : Subcategory@{co ch sa sah} C)
  (SB : Subcategory@{co ch sb ch} C)
  (fullA : Construction.Subcategory.Full@{co ch sa sah fa} C SA)
  (sub : ∀ x : C, sobj C SB x → sobj C SA x)
  (RB : Reflective@{ra rb rc rd co sb ch} SB).

Definition restrict_sub : Subcategory (Sub C SA) :=
  @Build_Subcategory (Sub C SA) (fun X => sobj C SB (`1 X))
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Lemma restrict_full : Construction.Subcategory.Full (Sub C SA) restrict_sub.
Proof. intros x y ox oy g; exact I. Qed.

Definition restrict_obj (X : Sub C SA) : Sub (Sub C SA) restrict_sub :=
  ((`1 (reflector RB (`1 X)); sub _ (`2 (reflector RB (`1 X))));
   `2 (reflector RB (`1 X))).

Definition restrict_unit (X : Sub C SA) :
  X ~{Sub C SA}~> Incl (Sub C SA) restrict_sub (restrict_obj X) :=
  (@unit _ _ _ _ (reflective_adj RB) (`1 X); fullA _ _ _ _ _).

Definition restrict_universal (X : Sub C SA) :
  ∀ (d : Sub (Sub C SA) restrict_sub)
    (f : X ~{Sub C SA}~> Incl (Sub C SA) restrict_sub d),
    ∃! g : restrict_obj X ~{Sub (Sub C SA) restrict_sub}~> d,
      f ≈ fmap[Incl (Sub C SA) restrict_sub] g ∘ restrict_unit X.
Proof using fullA.
  intros d f.
  pose (dB := (`1 (`1 d); `2 d) : Sub C SB).
  pose (g0 := from (@adj _ _ _ _ (reflective_adj RB) (`1 X) dB) (`1 f)).
  unshelve eexists.
  - exact ((`1 g0; fullA _ _ _ _ _); I).
  - change (`1 f ≈ `1 g0 ∘ @unit _ _ _ _ (reflective_adj RB) (`1 X)).
    transitivity (to (@adj _ _ _ _ (reflective_adj RB) (`1 X) dB) g0).
    + symmetry.
      exact (@from_adj_comp_law _ _ _ _ (reflective_adj RB) _ dB (`1 f)).
    + exact (@to_adj_unit _ _ _ _ (reflective_adj RB) _ _ g0).
  - intros g' Hg'.
    pose (g'B := (`1 (`1 g'); reflective_full RB _ _ _ _ _)
                 : reflector RB (`1 X) ~{Sub C SB}~> dB).
    assert (E : g'B ≈ g0).
    { apply (snd (@adj_univ _ _ _ _ (reflective_adj RB) _ _ g'B (`1 f))).
      transitivity (`1 (`1 g') ∘ @unit _ _ _ _ (reflective_adj RB) (`1 X)).
      - exact (@to_adj_unit _ _ _ _ (reflective_adj RB) _ _ g'B).
      - symmetry. exact Hg'. }
    symmetry. exact E.
Defined.

Definition restrict_ua (X : Sub C SA) :
  @UniversalArrow (Sub C SA) (Sub (Sub C SA) restrict_sub) X
    (Incl (Sub C SA) restrict_sub) :=
  @universal_arrow_from_UMP (Sub C SA) (Sub (Sub C SA) restrict_sub) X
    (Incl (Sub C SA) restrict_sub) (restrict_obj X) (restrict_unit X)
    (restrict_universal X).

Definition restrict_reflector : Sub C SA ⟶ Sub (Sub C SA) restrict_sub :=
  LeftAdjointFunctorFromUniversalArrows (Incl (Sub C SA) restrict_sub)
    restrict_ua.

Definition restrict_adj :
  restrict_reflector ⊣ Incl (Sub C SA) restrict_sub :=
  AdjunctionFromUniversalArrows (Incl (Sub C SA) restrict_sub) restrict_ua.

Definition restrict_Reflective : Reflective restrict_sub :=
  @Build_Reflective (Sub C SA) restrict_sub restrict_full restrict_reflector
    restrict_adj.

End Restrict.

(* * ** The reflections into T0, T1 and T2 spaces, and Exercise 4 at n = 0, 1 / * ** 对 T0、T1 和 T2 空间的反射，以及 n = 0, 1 时的练习 4 *)

Definition PT0_Reflective@{o so +} :
  Reflective (PSepSub@{o so} prem_T0@{o}) :=
  PSep_Reflective prem_T0 prem_T0_laws.

Definition PT1_Reflective@{o so +} :
  Reflective (PSepSub@{o so} prem_T1@{o}) :=
  PSep_Reflective prem_T1 prem_T1_laws.

Definition PT2_Reflective@{o so +} :
  Reflective (PSepSub@{o so} prem_T2@{o}) :=
  PSep_Reflective prem_T2 prem_T2_laws.

(* Mac Lane's Exercise 4 at n = 0: Top_1 → Top_0, T1 spaces in T0 spaces. / Mac Lane 的练习 4 在 n = 0: Top_1 → Top_0，T1 空间在 T0 空间中。 *)
Definition PT1_in_PT0_Reflective@{o so +} :
  Reflective (restrict_sub (PSepSub@{o so} prem_T0@{o})
                           (PSepSub@{o so} prem_T1@{o})) :=
  restrict_Reflective (PSepSub prem_T0) (PSepSub prem_T1)
    (PFullSub_Full _) PT1_PT0 PT1_Reflective.

(*
 Mac Lane's Exercise 4 at n = 1: Top_2 → Top_1, Hausdorff spaces in T1
 spaces. 

 --------
 Mac Lane 的练习 4，在 n = 1 时：Top_2 → Top_1，T1 空间中的豪斯多夫空间。
*)
Definition PHaus_in_PT1_Reflective@{o so +} :
  Reflective (restrict_sub (PSepSub@{o so} prem_T1@{o})
                           (PSepSub@{o so} prem_T2@{o})) :=
  restrict_Reflective (PSepSub prem_T1) (PSepSub prem_T2)
    (PFullSub_Full _) PHaus_PT1 PT2_Reflective.

(* * ** Readbacks of the direct reflection / * ** 直接反射的回读 *)

(* The quotient keeps X's points, coarsens their equality to [sepeq], and the reflector and its unit compute to it on the nose. / 商保持X的点，将它们的平等粗化为[sepeq]，并且反射器及其单位精确地对其进行计算。 *)
Example SepQuot_carrier@{o} (prem : SepPremise@{o}) (X : PTop@{o}) :
  carrier (pt_carrier (SepQuot prem X)) = carrier (pt_carrier X) := eq_refl.

Example SepQuot_equiv@{o} (prem : SepPremise@{o}) (X : PTop@{o})
  (a b : carrier (pt_carrier X)) :
  @equiv _ (is_setoid (pt_carrier (SepQuot prem X))) a b = sepeq prem X a b
  := eq_refl.

Example PSep_reflector_obj@{o so +} (prem : SepPremise@{o})
  (L : SepLaws@{o} prem) (X : PTopCat@{o so}) :
  `1 (fobj[PSep_reflector prem L] X) = SepQuot prem X := eq_refl.

Example PSep_unit_point@{o so +} (prem : SepPremise@{o})
  (L : SepLaws@{o} prem) (X : PTopCat@{o so}) (x : carrier (pt_carrier X)) :
  pmap (@unit _ _ _ _ (PSep_adj prem L) X) x = x := eq_refl.

(*
 The restricted reflection computes the same way: Exercise 4's reflector
 at n = 0 sends a T0 space to its largest T1 quotient, and its unit is
 the identity on points. 

 --------
 受限反射的计算方式相同：练习4的反射器在 n = 0 时将一个 T0 空间映射到其最大的 T1 商空间，其单位映射是点上的恒等映射。
*)
Example PT1_in_PT0_obj@{o so +}
  (X : Sub PTopCat@{o so} (PSepSub@{o so} prem_T0@{o})) :
  `1 (`1 (fobj[reflector PT1_in_PT0_Reflective] X)) = SepQuot prem_T1 (`1 X)
  := eq_refl.

Example PT1_in_PT0_unit_point@{o so +}
  (X : Sub PTopCat@{o so} (PSepSub@{o so} prem_T0@{o}))
  (x : carrier (pt_carrier (`1 X))) :
  pmap (`1 (@unit _ _ _ _ (reflective_adj PT1_in_PT0_Reflective) X)) x = x
  := eq_refl.

(* * ** A retract of a separated space is separated / * ** 分离空间的收缩是分离的 *)

Lemma PSep_retract@{o} (prem : SepPremise@{o}) (L : SepLaws@{o} prem)
  (X R : PTop@{o}) (u : PMor@{o} X R) (e : PMor@{o} R X)
  (Heu : ∀ x, pmap e (pmap u x) ≈ x) : PSep prem R → PSep prem X.
Proof.
  intros HR x y Hp.
  transitivity (pmap e (pmap u x)); [symmetry; exact (Heu x)|].
  transitivity (pmap e (pmap u y)); [|exact (Heu y)].
  refine (proper_morphism (pmap e) _ _ (HR _ _ _)).
  exact (sep_pull_cont prem L X R u x y Hp).
Qed.

(** ** Every inclusion is strict / ** 每一个包含都是严格的 *)

(* Not T0: the indiscrete two-point space of Instance/Top/Cocomplete.v. / Not T0：Instance/Top/Cocomplete.v 的不可分二点空间。 *)
Lemma PTwoIndisc_not_PT0@{o} : PT0 PTwoIndisc@{o} → False.
Proof.
  intro H.
  assert (Hp : prem_T0 _ (POpen PTwoIndisc@{o}) true false).
  { intros U HU; split; intro u; exact (HU _ _ u). }
  pose proof (H _ _ Hp) as e. simpl in e. discriminate e.
Qed.

(* T0 but not T1: Sierpiński space, the two points with [true] open. / T0 但不是 T1：谢尔平斯基空间，两个点的开集为 [true]。 *)
Section Sierpinski.

Universe o.

Definition sier_open (U : bool_setoid_object@{o o} → Prop) : Prop :=
  U false → U true.

Lemma sier_open_respects (U V : bool_setoid_object@{o o} → Prop) :
  (∀ x, U x <-> V x) → sier_open U → sier_open V.
Proof. intros H HU v. apply (proj1 (H true)), HU, (proj2 (H false)), v. Qed.

Lemma sier_open_proper (U : bool_setoid_object@{o o} → Prop) :
  sier_open U → ∀ x y : bool_setoid_object@{o o}, x ≈ y → U x → U y.
Proof. intros _ x y e u. simpl in e. subst y. exact u. Qed.

Lemma sier_open_union (F : (bool_setoid_object@{o o} → Prop) → Prop) :
  (∀ U, F U → sier_open U) → sier_open (fun x => ex (fun U => F U /\ U x)).
Proof. intros HF [U [FU u]]. exists U. exact (conj FU (HF U FU u)). Qed.

Lemma sier_open_whole : sier_open (fun _ => True).
Proof. intros _; exact I. Qed.

Lemma sier_open_inter (U V : bool_setoid_object@{o o} → Prop) :
  sier_open U → sier_open V → sier_open (fun x => U x /\ V x).
Proof. intros HU HV [u v]. exact (conj (HU u) (HV v)). Qed.

Definition PSierpinski : PTop@{o} := {|
  pt_carrier     := bool_setoid_object@{o o};
  POpen          := sier_open;
  popen_respects := sier_open_respects;
  popen_proper   := sier_open_proper;
  popen_union    := sier_open_union;
  popen_whole    := sier_open_whole;
  popen_inter    := sier_open_inter
|}.

Lemma PSierpinski_PT0 : PT0 PSierpinski.
Proof.
  intros x y H. change (x = y).
  assert (Ho : POpen PSierpinski (fun z => z = true))
    by (intros _; reflexivity).
  destruct (H _ Ho) as [a b].
  destruct x, y; try reflexivity.
  - symmetry. exact (a eq_refl).
  - exact (b eq_refl).
Qed.

Lemma PSierpinski_not_PT1 : PT1 PSierpinski → False.
Proof.
  intro H.
  assert (Hp : prem_T1 _ (POpen PSierpinski) false true).
  { intros U HU u. exact (HU u). }
  pose proof (H _ _ Hp) as e. simpl in e. discriminate e.
Qed.

End Sierpinski.

(* T1 but not T2: the cofinite topology on the naturals, whose nonempty opens are the sets containing a tail [N, ∞). The arithmetic is proved from the prelude alone. / T1 但不是 T2：自然数上的共有限拓扑，其中非空开集是包含尾集 [N, ∞) 的集合。算术仅从前奏即可证明。 *)
Section NatArith.

Local Open Scope nat_scope.

Lemma sep_le_trans@{} (a b c : nat) : a <= b → b <= c → a <= c.
Proof.
  intros H1 H2. induction H2 as [|c _ IH]; [exact H1|exact (le_S _ _ IH)].
Qed.

Lemma sep_le_add_r@{} (n m : nat) : n <= n + m.
Proof.
  induction n as [|n IH]; simpl; [exact (le_0_n m)|exact (le_n_S _ _ IH)].
Qed.

Lemma sep_le_add_l@{} (n m : nat) : m <= n + m.
Proof. induction n as [|n IH]; simpl; [exact (le_n m)|exact (le_S _ _ IH)]. Qed.

Lemma sep_not_succ_le@{} (n : nat) : S n <= n → False.
Proof.
  induction n as [|n IH]; intro H.
  - inversion H.
  - exact (IH (le_S_n _ _ H)).
Qed.

End NatArith.

Section Cofinite.

Universe o.

Local Open Scope nat_scope.

Definition pnat_setoid : SetoidObject@{o o} :=
  {| carrier := nat; is_setoid := eq_Setoid nat |}.

Definition cof_open (U : pnat_setoid → Prop) : Prop :=
  ∀ x, U x → ex (fun N => ∀ z, N <= z → U z).

Lemma cof_open_respects (U V : pnat_setoid → Prop) :
  (∀ x, U x <-> V x) → cof_open U → cof_open V.
Proof.
  intros H HU x v. destruct (HU x (proj2 (H x) v)) as [N HN].
  exists N. intros z Hz. exact (proj1 (H z) (HN z Hz)).
Qed.

Lemma cof_open_proper (U : pnat_setoid → Prop) :
  cof_open U → ∀ x y : pnat_setoid, x ≈ y → U x → U y.
Proof. intros _ x y e u. simpl in e. subst y. exact u. Qed.

Lemma cof_open_union (F : (pnat_setoid → Prop) → Prop) :
  (∀ U, F U → cof_open U) → cof_open (fun x => ex (fun U => F U /\ U x)).
Proof.
  intros HF x [U [FU u]]. destruct (HF U FU x u) as [N HN].
  exists N. intros z Hz. exists U. exact (conj FU (HN z Hz)).
Qed.

Lemma cof_open_whole : cof_open (fun _ => True).
Proof. intros x _. exists 0. intros; exact I. Qed.

Lemma cof_open_inter (U V : pnat_setoid → Prop) :
  cof_open U → cof_open V → cof_open (fun x => U x /\ V x).
Proof.
  intros HU HV x [u v].
  destruct (HU x u) as [N HN], (HV x v) as [M HM].
  exists (N + M). intros z Hz. split.
  - exact (HN z (sep_le_trans _ _ _ (sep_le_add_r N M) Hz)).
  - exact (HM z (sep_le_trans _ _ _ (sep_le_add_l N M) Hz)).
Qed.

Definition PCofinite : PTop@{o} := {|
  pt_carrier     := pnat_setoid;
  POpen          := cof_open;
  popen_respects := cof_open_respects;
  popen_proper   := cof_open_proper;
  popen_union    := cof_open_union;
  popen_whole    := cof_open_whole;
  popen_inter    := cof_open_inter
|}.

(* The open “x, or the tail above x + y”: if it must contain y, then y = x, the tail lying strictly above y. / 开口“x，或 x + y 上方的尾巴”：如果它必须包含 y，那么 y = x，尾巴严格位于 y 上方。 *)
Lemma PCofinite_PT1 : PT1 PCofinite.
Proof.
  intros x y H. change (x = y).
  assert (Ho : POpen PCofinite (fun z => x = z \/ S (x + y) <= z)).
  { intros w _. exists (S (x + y)). intros z Hz. right. exact Hz. }
  destruct (H _ Ho (or_introl eq_refl)) as [e|l]; [exact e|].
  exfalso. apply (sep_not_succ_le y).
  exact (sep_le_trans _ _ _ (le_n_S _ _ (sep_le_add_l x y)) l).
Qed.

(* Any two nonempty opens meet, above both tails. / 任意两个非空开集相交，都在两个尾部之上。 *)
Lemma PCofinite_not_PHaus : PHaus PCofinite → False.
Proof.
  intro H.
  assert (Hp : PNotSep PCofinite 0 1).
  { intros U V HU HV u v.
    destruct (HU 0 u) as [N HN], (HV 1 v) as [M HM].
    exists (N + M). split.
    - exact (HN _ (sep_le_add_r N M)).
    - exact (HM _ (sep_le_add_l N M)). }
  pose proof (H _ _ Hp) as e. simpl in e. discriminate e.
Qed.

End Cofinite.

(* The discrete two-point space is Hausdorff: its equality is Leibniz, and the two singletons are open. / 离散的两点空间是豪斯多夫空间：它的相等是莱布尼茨相等，并且两个单点集是开的。 *)
Lemma PBool_PHaus@{o} : PHaus PBool@{o}.
Proof.
  intros a b H. change (a = b).
  destruct (H (fun z => z = a) (fun z => z = b)) as [z [za zb]].
  - intros x y e hx. change (x = y) in e. congruence.
  - intros x y e hx. change (x = y) in e. congruence.
  - reflexivity.
  - reflexivity.
  - congruence.
Qed.

(* * ** The classical negative Hausdorff axiom against the positive one / * ** 反对正的古典负豪斯多夫公理 *)

(* Negative to positive, given that the points' equality is stable under double negation. / 由负到正，假设在双重否定下点的等式是稳定的。 *)
Lemma PIsHausdorff_PHaus@{o} (X : PTop@{o})
  (stab : ∀ x y : X, ((x ≈ y → False) → False) → x ≈ y) :
  PIsHausdorff X → PHaus X.
Proof.
  intros H x y Hp. apply stab. intro ne.
  destruct (H x y ne) as [U [V [HU [HV [u [v d]]]]]].
  destruct (Hp U V HU HV u v) as [z [a b]].
  exact (d z a b).
Qed.

(*
 Positive to negative, given excluded middle for propositions, as a
 hypothesis. 

 --------
 从正到负，假设命题存在排中律。
*)
Lemma PHaus_PIsHausdorff@{o} (lem : ∀ P : Prop, P \/ (P → False))
  (X : PTop@{o}) : PHaus X → PIsHausdorff X.
Proof.
  intros H x y ne.
  destruct (lem (ex (fun U => ex (fun V => POpen X U /\ POpen X V /\ U x /\
                                  V y /\ ∀ z, U z → V z → False))))
    as [e|n]; [exact e|].
  exfalso. apply ne. apply H. intros U V HU HV u v.
  destruct (lem (ex (fun z => U z /\ V z))) as [e|m]; [exact e|].
  exfalso. apply n. exists U, V. repeat split; auto.
  intros z a b. apply m. exists z. auto.
Qed.

(*
 Unconditionally, each form gives the other's conclusion only under a
 negation. 

 --------
 无条件地，每种形式只有在否定下才给出另一种形式的结论。
*)
Lemma PIsHausdorff_PHaus_nn@{o} (X : PTop@{o}) (H : PIsHausdorff X)
  (x y : X) : PNotSep X x y → (x ≈ y → False) → False.
Proof.
  intros Hp ne.
  destruct (H x y ne) as [U [V [HU [HV [u [v d]]]]]].
  destruct (Hp U V HU HV u v) as [z [a b]].
  exact (d z a b).
Qed.

Lemma PHaus_distinct_not_notsep@{o} (X : PTop@{o}) (H : PHaus X) (x y : X) :
  (x ≈ y → False) → PNotSep X x y → False.
Proof. intros ne Hp. exact (ne (H x y Hp)). Qed.

(*
 A Hausdorff space's equality is propositional: [PNotSep] is a
 proposition equivalent to it. 

 --------
 豪斯多夫空间的相等性是命题性的：[PNotSep] 是与之等价的命题。
*)
Definition PHaus_PropEquiv@{o} (X : PTop@{o}) (hX : PHaus X) :
  PropEquiv (is_setoid (pt_carrier X)) :=
  {| pequiv := PNotSep X;
     pequiv_to := hX;
     pequiv_from := sl_equiv _ prem_T2_laws X |}.
