Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Product.Limit.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Complete.Freyd.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.
Require Import Category.Instance.Top.StoneCech.Refutations.
Require Import Category.Instance.Top.Cocomplete.
Require Import Category.Instance.Top.Complete.Refutations.
From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(* * * Cocompleteness of spaces refuted above the points / * * 空间的完备性在上述点中被驳斥 *)

(*
 Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
 §V.2 Proposition 3, book p. 114 (maclane:V.2:prop3), Freyd's theorem
 that a small complete category is a preorder, consumed dually
 through Structure/Complete/Freyd.v; and §V.9, book p. 134 (PDF
 p. 143), whose "general colimits in Top" (maclane:V.9:remark2) this
 file bounds, as Instance/Top/StoneCech/Refutations.v bounds the
 completeness of [Top] and [CompHaus]
 nLab: https://ncatlab.org/nlab/show/complete+small+category
 nLab: https://ncatlab.org/nlab/show/Cantor%27s+theorem

 BACKGROUND.  Freyd's observation (Structure/Complete/Freyd.v's header)
 is that completeness in the book's sense is a property of LARGE
 categories: a category with products indexed by its own arrows and two
 distinct parallel arrows cannot exist.  Its dual bounds cocompleteness
 the same way.  For a category of spaces there is a second, more direct
 bound, Cantor's theorem at the points of ONE coproduct.  Let [K] be
 the type of pairs of a space [X] and a predicate on the points of [X];
 it quantifies over all spaces, so it sits strictly above the points'
 universe.  If the coproduct [Q] of [K]-many one-point spaces exists,
 every predicate [U] on the points of [Q] has a code in [Q], the point
 of the summand at the pair [(Q, U)].  A continuous map out of [Q] into
 a space of truth values, the copairing of "is this summand the one at
 [k0]?", tells the codes apart, and with decidable equality of spaces
 the dependent pair injectivity [inj_pair2_eq_dec] turns "the same
 summand" into "the same predicate".  So predicates on the points of
 [Q] inject into the points of [Q], which Cantor's diagonal forbids.
 Over [PTopCat] and over the Type-valued [Top] alike the two arguments
 reach the same shapes, because an arrow index moves between the object
 universes of [PTopCat] and between the hom universes of [Top]
 (Instance/Top/Complete/Refutations.v's [PTop_ArrowIndex_transport] and
 [Top_ArrowIndex_transport]).  Nothing here is an axiom: decidable
 equality of spaces
 (Construction/Quotient.v's [ObjDecEq]), informative excluded middle
 ([IEM], Instance/Sets/Classifier/OneLevel.v) and arrow indices
 ([ArrowIndex], Structure/Complete/Freyd.v) are hypotheses; [IEM] holds
 classically and yields the other two.

 NAMES.  The scheme of Instance/Top/Complete/Refutations.v's header,
 shared with this file, the colimit dual: [_Freyd] and [_Cantor_] name
 the argument, and the hypothesis suffix names the reach.  [_Freyd]:
 Freyd's argument from an arrow index at the shape universe [s],
 nothing tying [s] to the points' [o]; [_ObjDecEq] and [_IEM]:
 decidable equality of spaces and informative excluded middle, each at
 every [s] with [o < s], [o := Set] included; [_Cantor_ObjDecEq] and
 [_Cantor_IEM]: Cantor's argument under the same hypotheses and with
 the same reach, but that the [ObjDecEq] form needs [Set < o].  The
 limit side's [_below] does not occur here: no form of this file stops
 at the hom universe of [Top], and [Top_not_cocomplete_ObjDecEq] and
 [Top_not_cocomplete_IEM] reach below it under the plain suffixes.

 WHAT IS REFUTED.
 - Freyd's form over [PTopCat], dualized: [PTop_not_cocomplete_Freyd],
 an [ArrowIndex] of [PTopCat] at the shape universe refutes
 cocompleteness there.  The separated pair is Instance/Top/
 Subspace.v's [ppoint_true] and [ppoint_false], told apart by
 evaluation at the point.  [PTop_not_cocomplete_ObjDecEq] and
 [PTop_not_cocomplete_IEM]: under [ObjDecEq PTopCat], or under
 [IEM], no [Cocomplete@{r s o so} PTopCat@{o so}] at any shape
 universe [s] strictly above the points, [o < s], [o := Set]
 included: Structure/Complete/Freyd.v's [canonical_ArrowIndex] of
 [PTopCat@{o s}], transported, as the limit side does.
 - [Sets_not_cocomplete_IEM]: under [IEM], [Sets@{o so}] is not
 cocomplete at any shape universe above its carriers.  Were it,
 Instance/Top/Cocomplete.v's recipe [PTop_Colimit_lift] would make
 [PTopCat] cocomplete there, against [PTop_not_cocomplete_IEM].
 - Over the Type-valued [Top@{h o}]: [Top_not_cocomplete_Freyd] is
 the exact dual of Instance/Top/StoneCech/Refutations.v's
 [Top_not_complete] (an [ArrowIndex@{s h h}] refutes
 [Cocomplete@{r s h h}]).  The canonical index of [Top@{h o}] sits
 at [h]; the one of [Top@{s o}], moved to [Top@{h o}] by
 Instance/Top/Complete/Refutations.v's [Top_ArrowIndex_transport],
 indexes at [s].  Through it [Top_not_cocomplete_ObjDecEq] and
 [Top_not_cocomplete_IEM], under [ObjDecEq Top] or under [IEM],
 refute [Cocomplete@{r s h h} Top@{h o}] at every [s] with [o < s],
 the shapes strictly between the points and the homs included and
 [o := Set] as well.
 - Cantor's argument, a second and independent proof.  The engine:
 [cocomp_cantor_diagonal], no map from the predicates on a type into
 it is injective up to a reflexive relation; [pcc_contradiction]
 (over [PTopCat]) and [tcc_contradiction] (over [Top]) run the
 argument above against an abstract separator: a space [Om] and a
 family [c k0 k] of its points with [c k0 k ≈ c k0 k0] only at
 [k = k0]; [pcc_index] and [tcc_index] are [K].  Over [PTopCat],
 [PTop_not_cocomplete_Cantor_ObjDecEq] (the separator the discrete
 space on the truth values under [<->], [pcc_Prop], with
 [c k0 k := (k = k0)], whence [Set < o]) and
 [PTop_not_cocomplete_Cantor_IEM] (the separator Instance/Top/
 Prop.v's two-point [PBool], [c] deciding [k = k0] by [IEM], no
 [Set < o]); both reach no shape the Freyd forms above do not.  Over
 [Top], [Top_not_cocomplete_Cantor_ObjDecEq] and
 [Top_not_cocomplete_Cantor_IEM], the separators Instance/Top.v's
 [Discrete_Top] of [pcc_Prop] and [Bool_Discrete], at every
 [o < s], below [h] as well; they too reach no shape the transported
 Freyd forms do not, and the [ObjDecEq] one reaches fewer, needing
 [Set < o].

 THE BOUNDARY.  Cocompleteness of [PTopCat@{o so}] is provable at every
 shape universe [s <= o] (Instance/Top/Cocomplete.v's [PTop_Cocomplete],
 with no hypothesis) and refuted under [IEM], or under [ObjDecEq], at
 every [s] with [o < s] ([PTop_not_cocomplete_IEM],
 [PTop_not_cocomplete_ObjDecEq]); no shape universe lies between, and
 without one of the hypotheses or an index nothing above the points is
 refuted.  Measured in the scratch file of Instance/Top/Complete.v's
 boundary paragraph (the six files of #458 after the union of their
 import lists): [PTop_not_cocomplete_IEM] and
 [PTop_not_cocomplete_ObjDecEq] are accepted at an [s] with [o < s] and
 at [o := Set]; [PTop_not_cocomplete_IEM] and [Sets_not_cocomplete_IEM]
 read at [Cocomplete@{o o o so}] are refused ("Cannot enforce <1> = o
 because <1> < o", the generated universe written <1>), so the
 refutations do not reach the proved statement; at [o := Set]
 [PTop_not_cocomplete_Cantor_ObjDecEq] is refused ("Cannot enforce
 Set = <1> because Set < <1>"), its separator carrying [Set < o], and
 [PTop_not_cocomplete_Cantor_IEM] accepted.  Over the Type-valued [Top]
 [Top_not_cocomplete_IEM] and [Top_not_cocomplete_ObjDecEq] refute every
 [o < s], and at [s <= o] the question is open, walled as
 Instance/Top/Cocomplete/TypeValued.v records.  Measured in
 Test/ProbeTopComplete458.v: [Top_not_cocomplete_IEM] and
 [Top_not_cocomplete_Cantor_IEM] are accepted at an [s] with
 [o < s < h], and [Top_not_cocomplete_ObjDecEq] at [o := Set], where
 [Top_not_cocomplete_Cantor_ObjDecEq] is refused ("Cannot enforce
 Set = <2> because Set < <2>", the generated universes numbered in
 order of appearance in the message); [Top_not_cocomplete_IEM] read at
 [s := o], by its universe instance, is refused ("Cannot enforce o < o
 because o = o").

 STRENGTHS.  Every theorem concludes [False]; [cocomp_cantor_diagonal]
 concludes [False] from its hypotheses.  [ObjDecEq] is used only at
 [canonical_ArrowIndex] and [inj_pair2_eq_dec], and [IEM] only to decide
 equality of spaces and of indices.  No proof ends [Defined].

 UNIVERSES, read by [About] under [Set Printing Universes], stdlib caps
 left out; [o] the points, [so] the objects of [PTopCat], [h] the homs
 of [Top], [s] and [r] a shape and its colimit record, [e] the level of
 [IEM], which is free.
 PTop_not_cocomplete_Freyd@{r s o so} :
 ArrowIndex@{s so o} PTopCat@{o so} → ¬ Cocomplete@{r s o so}
 ( * o < so; nothing ties s to o * )
 PTop_not_cocomplete_ObjDecEq@{r s o so} :
 ObjDecEq PTopCat@{o so} → ¬ Cocomplete@{r s o so}  ( * o < s * )
 PTop_not_cocomplete_IEM@{e r s o so} :
 IEM@{e} → ¬ Cocomplete@{r s o so}         ( * o < so, o < s * )
 Sets_not_cocomplete_IEM@{e r s o so} :
 IEM@{e} → ¬ Cocomplete@{r s o so} (at Sets@{o so})
 ( * o < so, o < s * )
 Top_not_cocomplete_Freyd@{r s h o} :
 ArrowIndex@{s h h} Top@{h o} → ¬ Cocomplete@{r s h h}  ( * o < h * )
 Top_not_cocomplete_ObjDecEq@{r s h o} :
 ObjDecEq Top@{h o} → ¬ Cocomplete@{r s h h}  ( * o < h, o < s * )
 Top_not_cocomplete_IEM@{e r s h o} :
 IEM@{e} → ¬ Cocomplete@{r s h h}         ( * o < h, o < s * )
 PTop_not_cocomplete_Cantor_ObjDecEq@{r s o so},
 PTop_not_cocomplete_Cantor_IEM@{e r s o so}: as the [PTopCat] forms
 above, the first with [Set < o].
 Top_not_cocomplete_Cantor_ObjDecEq@{r s h o},
 Top_not_cocomplete_Cantor_IEM@{e r s h o}: as the [Top] forms above,
 the first with [Set < o].
 [pcc_index@{o s}] and [tcc_index@{o s}] are declared outside the
 sections, so they carry only [o < s] and [Set < s]; the constants
 declared inside the sections carry the sections' universes and the
 bounds [s <= r] and [o <= r] (or [h <= r]) of the [Cocomplete]
 hypothesis in their [Context], whether or not their statements
 mention it.  Over the [About] output of all 32 of this file's
 constants (its [Print Module] listing, the one [Program] obligation
 included; it declares no record or inductive), [Set] occurs in no
 equation and pins no universe, and it occurs in no block of the three
 Freyd forms over [Top].  It occurs only as bounds, each implied by a
 declared one or recording a sort: [Set < s] in 25 blocks (the sort of
 [K], whose fibre [X → Prop] sits at [Set+1], and the [PTopCat@{o s}]
 the transported [PTopCat] forms build the index at; implied by
 [o < s]); [Set < so] in 14 ([PTopCat]'s); [Set < eq_ind_r.u0] in 7
 ([cocomp_cantor_diagonal]'s [subst] at the type of predicates
 [A → Prop], whose sort is at least [Set+1]);
 [Set < Logic_lemmas.equality.u0] and
 [Set < Eqdep_dec.inj_pair2_eq_dec.u1] in 8 each ([inj_pair2_eq_dec]
 at the same family of predicates, first in [pcc_enc_inj] and
 [tcc_enc_inj]); and [Set < o] in 4: [pcc_Prop], whose carrier [Prop]
 sits at [Set+1], its obligation, and the two [_Cantor_ObjDecEq] forms
 that use it, which are therefore stated for [o] above [Set]; no other
 form is.

 ROUTE AND COST.  Closure 176 [Category.*] modules excluding this file
 ([Print Libraries] on a file requiring it).  Instance/Top/Complete/
 Refutations.v (for [PTop_ArrowIndex_transport] and
 [Top_ArrowIndex_transport]) and Instance/Top/
 StoneCech/Refutations.v (for [ObjDecEq_of_IEM]) are required rather
 than restating either; dropped together from the import list they cost
 34 at the margin (142 without them); dropped singly, the first costs
 3 and the second nothing, the first loading the second.

 NOT DELIVERED.  No refutation, and no proof, of cocompleteness of the
 Type-valued [Top] at shapes at or below its points; nothing about
 completeness, which is the limit side's (Instance/Top/StoneCech/
 Refutations.v and Instance/Top/Complete/Refutations.v for [Top], the
 second for [PTopCat]); and no statement
 that an arrow index of [PTopCat] at the points' universe is refuted by
 pairing [PTop_not_cocomplete_Freyd] with [PTop_Cocomplete] (that
 reading is Instance/Top/Complete/Refutations.v's
 [PTop_no_ArrowIndex_at_points], from completeness).  The four
 [_Cantor_] forms are subsumed by the Freyd forms and kept as an
 independent second argument. 

 --------
 Mac Lane，《为在职数学家而作的范畴论》，第2版（GTM 5），§V.2 命题 3，书中第114页（maclane:V.2:prop3），Freyd 定理指出小完全范畴是一个预序范畴，通过 Structure/Complete/Freyd.v 以对偶方式使用；以及 §V.9，书中第134页（PDF 第143页），其“Top 中的一般余极限”（maclane:V.9:remark2）由此文件限制，就像 Instance/Top/StoneCech/Refutations.v 限制了 [Top] 和 [CompHaus] 的完备性一样。nLab: https://ncatlab.org/nlab/show/complete+small+category nLab: https://ncatlab.org/nlab/show/Cantor%27s+theorem背景。Freyd 的观察（Structure/Complete/Freyd.v 的头文件）是，书中所说的完备性是大型范畴的一个性质：一个由其自身箭头索引的积以及两个不同平行箭头组成的范畴是不存在的。其对偶以同样的方式界定余完备性。对于空间的一个范畴，有第二种更直接的界定，即 Cantor 定理作用于单个余积的点。设 [K] 为空间 [X] 与 [X] 点上的一个谓词的一对类型；它对所有空间进行量化，因此它严格位于点的宇宙之上。如果存在 [K] 个单点空间的余积 [Q]，则 [Q] 的每个点上的谓词 [U] 在 [Q] 中都有一个编码，即在对 [(Q, U)] 的该对求和的构成点。从 [Q] 到一个真值空间的连续映射，即“这个加数是 [k0] 处的那个吗？”的共对映射，将这些代码区分开来，并且在空间的可判等下，依赖对的单射性 [inj_pair2_eq_dec] 将“相同的加数”转化为“相同的谓词”。因此 [Q] 点上的谓词可以注入到 [Q] 的点中，而康托尔对角线定理禁止这种情况。在 [PTopCat] 上以及在类型值的 [Top] 上，这两个参数达到相同的形状，因为一个箭头索引在 [PTopCat] 的对象宇宙之间移动，并在 [Top] 的 Hom 宇宙之间移动（Instance/Top/Complete/Refutations.v 的 [PTop_ArrowIndex_transport] 和 [Top_ArrowIndex_transport]）。这里没有任何东西是公理：空间的可判定等式（Construction/Quotient.v 的 [ObjDecEq]）、信息化排中律（[IEM]，Instance/Sets/Classifier/OneLevel.v）和箭头索引（[ArrowIndex]，Structure/Complete/Freyd.v）都是假设；[IEM] 在经典逻辑下成立，并推出另外两个。名称。Instance/Top/Complete/Refutations.v 头文件的方案，与此文件共享，余极对偶：[_Freyd] 和 [_Cantor_] 命名论证，而假设后缀命名覆盖范围。[_Freyd]：Freyd 在形状宇宙 [s] 上的箭头索引的论证，没有将 [s] 与点的 [o] 关联；[_ObjDecEq] 和 [_IEM]：空间的可判定相等性和信息化排中律，每个在 [s] 上，包含 [o < s]、[o := Set]；[_Cantor_ObjDecEq] 和 [_Cantor_IEM]：在相同假设下和同一覆盖范围的 Cantor 论证，但 [ObjDecEq] 形式需要 [Set < o]。极限侧的 [_below] 并未在此处出现：此文件的任何形式均不在 [Top] 的同伦宇宙停止，[Top_not_cocomplete_ObjDecEq] 和 [Top_not_cocomplete_IEM] 在普通后缀下覆盖它之下。什么被驳斥。- Freyd 的形式在 [PTopCat] 上双重化：[PTop_not_cocomplete_Freyd]，[PTopCat] 在形状宇宙中的一个 [ArrowIndex] 驳斥了那里的余完备性。分离的对是 Instance/Top/Subspace.v 的 [ppoint_true] 和 [ppoint_false]，通过在该点的求值来区分。[PTop_not_cocomplete_ObjDecEq] 和 [PTop_not_cocomplete_IEM]：在 [ObjDecEq PTopCat] 或在 [IEM] 下，在任何形状宇宙 [s] 中都没有 [Cocomplete@{r s o so} PTopCat@{o so}] 严格高于这些点，[o < s]、[o := Set] 包括：Structure/Complete/Freyd.v 的 [canonical_ArrowIndex] 从 [PTopCat@{o s}] 传输，就像极限边所做的那样。- [Sets_not_cocomplete_IEM]：在 [IEM] 下，[Sets@{o so}] 在其承载之上的任何形状宇宙中都不是余完备的。如果它是，Instance/Top/Cocomplete.v 的配方 [PTop_Colimit_lift] 将使 [PTopCat] 在那里余完备，这与 [PTop_not_cocomplete_IEM] 相悖。- 在类型值 [Top@{h o}] 上：[Top_not_cocomplete_Freyd] 是 Instance/Top/StoneCech/Refutations.v 的 [Top_not_complete]（一个 [ArrowIndex@{s h h}] 反驳 [Cocomplete@{r s h h}]）的精确对偶。[Top@{h o}] 的典型索引位于 [h]；[Top@{s o}] 的索引通过 Instance/Top/Complete/Refutations.v 的 [Top_ArrowIndex_transport] 移动到 [Top@{h o}]，索引位于 [s]。通过它，[Top_not_cocomplete_ObjDecEq] 和 [Top_not_cocomplete_IEM]，在 [ObjDecEq Top] 下或 [IEM] 下，在每个具有 [o < s] 的 [s] 上反驳 [Cocomplete@{r s h h} Top@{h o}]，包括点和 Homs 之间的严格形状及 [o := Set]。- 康托尔的论证，第二个独立的证明。引擎：
 [cocomp_cantor_diagonal]，没有将类型上的谓词映射到它的映射是至多在自反关系下单射的；[pcc_contradiction]（在[PTopCat]上）和[tcc_contradiction]（在[Top]上）针对抽象分离器运行上述论证：一个空间[Om]及其点族[c k0 k]，其中[c k0 k ≈ c k0 k0]仅在[k = k0]处；[pcc_index]和[tcc_index]是[K]。在[PTopCat]上，[PTop_not_cocomplete_Cantor_ObjDecEq]（分离器，真值上的离散空间，在[<->]下，[pcc_Prop]，带有[c k0 k := (k = k0)]，因此[Set < o]）和[PTop_not_cocomplete_Cantor_IEM]（分离器Instance/Top/Prop.v的两点[PBool]，[c]通过[IEM]决定[k = k0]，没有[Set < o]）；两者都达不到Freyd上述形式所未形成的形状。在 [Top]、[Top_not_cocomplete_Cantor_ObjDecEq] 和 [Top_not_cocomplete_Cantor_IEM] 上，分隔符 Instance/Top.v 的 [Discrete_Top] 以及 [pcc_Prop] 和 [Bool_Discrete]，在每一个 [o < s] 下，下面的 [h] 也是如此；它们也无法达到所传输的 Freyd 形式的形状，而 [ObjDecEq] 的一个到达较少，需要 [Set < o]。边界。[PTopCat@{o so}] 的余完备性在每一个形宇宙 [s <= o]（Instance/Top/Cocomplete.v 的 [PTop_Cocomplete]，无假设下）是可证明的，而在 [IEM] 下，或在 [ObjDecEq] 下，在每一个 [s] 具有 [o < s]（[PTop_not_cocomplete_IEM]，[PTop_not_cocomplete_ObjDecEq]）时是被驳斥的；没有形宇宙在其之间，并且在没有这些假设之一或索引的情况下，点以上的内容不会被驳斥。在 Instance/Top/Complete.v 的 scratch 文件的边界段（导入列表合并后的 #458 六个文件中）中测量：[PTop_not_cocomplete_IEM] 和 [PTop_not_cocomplete_ObjDecEq] 在 [s] 时被接受，并且在 [o < s] 和 [o := Set] 时也被接受；[PTop_not_cocomplete_IEM] 和 [Sets_not_cocomplete_IEM] 在 [Cocomplete@{o o o so}] 读取时被拒绝（"无法强制执行 <1> = o 因为 <1> < o"，生成的 universe 写为 <1>），因此反驳未能达到已证明的语句；在 [o := Set]，[PTop_not_cocomplete_Cantor_ObjDecEq] 被拒绝（"无法强制 Set = <1> 因为 Set < <1>"），其分隔符携带 [Set < o] ，而 [PTop_not_cocomplete_Cantor_IEM] 被接受。在类型值 [Top] 上，[Top_not_cocomplete_IEM] 和 [Top_not_cocomplete_ObjDecEq] 反驳每个 [o < s] ，在 [s <= o] 时问题仍然开放，如 Instance/Top/Cocomplete/TypeValued.v 所记录。以...衡量
 Test/ProbeTopComplete458.v:  [Top_not_cocomplete_IEM] 和
 [Top_not_cocomplete_Cantor_IEM] 在 [s] 时被接受，伴随 [o < s < h] ，而 [Top_not_cocomplete_ObjDecEq] 在 [o := Set] 时被接受，其中
 [Top_not_cocomplete_Cantor_ObjDecEq] 被拒绝（"无法强制执行 Set = <2> 因为 Set < <2>"，在消息中出现顺序编号的生成宇宙）； [Top_not_cocomplete_IEM] 在 [s := o] 被其宇宙实例读取时被拒绝（"无法强制执行 o < o 因为 o = o"）。

 强项。每个定理都以 [False] 结束； [cocomp_cantor_diagonal] 根据其假设得出 [False] 。 [ObjDecEq] 仅在 [canonical_ArrowIndex] 和 [inj_pair2_eq_dec] 使用，而 [IEM] 仅用于决定空间和索引的相等性。没有证明以 [Defined] 结束。宇宙，由 [About] 在 [Set Printing Universes] 下读取，标准库大写字母省略；[o] 点，[so] [PTopCat] 的对象，[h] [Top] 的同态，[s] 和 [r] 一个形状及其余极记录，[e] [IEM] 的层级，自由的。PTop_not_cocomplete_Freyd@{r s o so} :
 ArrowIndex@{s so o} PTopCat@{o so} → ¬ Cocomplete@{r s o so}
 ( * o < so; 没有什么将 s 与 o 联系起来 * )
 PTop_not_cocomplete_ObjDecEq@{r s o so} :
 ObjDecEq PTopCat@{o so} → ¬ Cocomplete@{r s o so}  ( * o < s * )
 PTop_not_cocomplete_IEM@{e r s o so} :
 IEM@{e} → ¬ Cocomplete@{r s o so}         ( * o < so, o < s * )
 Sets_not_cocomplete_IEM@{e r s o so} :
 IEM@{e} → ¬ Cocomplete@{r s o so} (在 Sets@{o so} 上)
 ( * o < so, o < s * )
 Top_not_cocomplete_Freyd@{r s h o} :
 ArrowIndex@{s h h} Top@{h o} → ¬ Cocomplete@{r s h h}  ( * o < h * )
 Top_not_cocomplete_ObjDecEq@{r s h o} :
 ObjDecEq Top@{h o} → ¬ Cocomplete@{r s h h}  ( * o < h, o < s * )
 Top_not_cocomplete_IEM@{e r s h o} :
 IEM@{e} → ¬ Cocomplete@{r s h h}         ( * o < h, o < s * )PTop_non_cocomplete_Cantor_ObjDecEq@{r s o so},
 PTop_non_cocomplete_Cantor_IEM@{e r s o so}: 如上面的 [PTopCat] 形式，第一种带有 [Set < o] 。Top_not_cocomplete_Cantor_ObjDecEq@{r s h o},
 Top_not_cocomplete_Cantor_IEM@{e r s h o}：如上所示的 [Top] 形式，
 第一个带有 [Set < o]。[pcc_index@{o s}] 和 [tcc_index@{o s}] 在部分之外声明，
 因此它们只携带 [o < s] 和 [Set < s]；在部分内声明的常量携带部分的 universes 以及
 [Cocomplete] 假设中 [s <= r] 和 [o <= r]（或 [h <= r]）的界限，无论它们的陈述中是否提及。
 在该文件的所有 32 个常量的 [About] 输出中（它的 [Print Module] 列表，包括 [Program] 义务；它没有声明记录或归纳），
 [Set] 在任何方程中都没有出现，也没有固定任何 universe，并且它没有出现在 [Top] 上三种 Freyd 形式的任何块中。它仅以界限形式出现，每个界限由一个已声明的界限暗示或记录一个类型：[Set < s] 在 25 个块中（[K] 的类型，其纤维 [X → Prop] 位于 [Set+1]，和 [PTopCat@{o s}] 运输的 [PTopCat] 形成索引；由 [o < s] 暗示）；[Set < so] 在 14 个（[PTopCat] 的）；[Set < eq_ind_r.u0] 在 7 个（[cocomp_cantor_diagonal] 的 [subst] 位于谓词类型 [A → Prop]，类型至少为 [Set+1]）；[Set < Logic_lemmas.equality.u0] 和 [Set < Eqdep_dec.inj_pair2_eq_dec.u1] 各 8 个（[inj_pair2_eq_dec] 在相同的谓词族中，首先在 [pcc_enc_inj] 和 [tcc_enc_inj]）；以及 [Set < o] 在 4 个：[pcc_Prop]，承载者 [Prop] 位于 [Set+1]，其义务，以及使用它的两个 [_Cantor_ObjDecEq] 形式，因此在 [o] 上方为 [Set] 陈述；没有其他形式。路线和成本。关闭176 [Category.*]模块，排除此文件（[Print Libraries]在需要它的文件上）。Instance/Top/Complete/Refutations.v（用于[PTop_ArrowIndex_transport]和[Top_ArrowIndex_transport]）以及Instance/Top/StoneCech/Refutations.v（用于[ObjDecEq_of_IEM]）是必需的，而不是重复任何一个；从导入列表中一起删除，它们的边际成本为34（没有它们则为142）；单独删除时，第一个成本为3，第二个没有成本，第一个会加载第二个。未交付。没有对类型值 [Top] 在其点及以下形状的协完备性进行反驳或证明；没有关于完备性的任何内容，这是极限端的（[Top] 的 Instance/Top/StoneCech/Refutations.v 和 Instance/Top/Complete/Refutations.v，第二个用于 [PTopCat]）；也没有说明 [PTopCat] 在点的宇宙上的箭头指标是否被将 [PTop_not_cocomplete_Freyd] 与 [PTop_Cocomplete] 配对所反驳（这种解读来自完备性的 Instance/Top/Complete/Refutations.v 的 [PTop_no_ArrowIndex_at_points]）。四种 [_Cantor_] 形式被 Freyd 形式包含，并作为独立的第二个参数保留。
*)

#[local] Obligation Tactic := idtac.

(* * ** [PTopCat]: Freyd's form, dualized, and transported above the points / * ** [PTopCat]：弗雷德形式，双重化，并传输到点的上方 *)

(*
 Freyd's form, dualized: an arrow index at the shape universe refutes
 cocompleteness there. 

 --------
 弗雷德的形式，对偶化：形状宇宙中的箭头索引反驳了那里的一致完备性。
*)
Theorem PTop_not_cocomplete_Freyd@{r s o so +| o < so +}
  (AI : ArrowIndex@{s so o} PTopCat@{o so})
  (cocomp : @Cocomplete@{r s o so} PTopCat@{o so}) : False.
Proof.
  exact (freyd_no_separated_pair (ArrowIndex_op AI)
           (a:=PBool) (b:=PPoint) ppoint_true ppoint_false _ _
           (complete_iprod (Complete_op_of_Cocomplete cocomp)
              (fun _ : ai_index (ArrowIndex_op AI) => PPoint))
           (fun h => pmap h ttt) (fun u v H => H ttt) eq_refl eq_refl).
Qed.

(*
 Every shape universe strictly above the points, under decidable
 equality of spaces: the canonical index is built at [PTopCat@{o s}]
 and transported by Instance/Top/Complete/Refutations.v's
 [PTop_ArrowIndex_transport], as the limit side does. 

 --------
 每个形状宇宙严格在点之上，在空间可判定的等式下：典型索引构建于 [PTopCat@{o s}]，并通过 Instance/Top/Complete/Refutations.v 的 [PTop_ArrowIndex_transport] 进行传输，就像极限端一样。
*)
Theorem PTop_not_cocomplete_ObjDecEq@{r s o so +| o < so, o < s +}
  (DE : ObjDecEq PTopCat@{o so})
  (cocomp : @Cocomplete@{r s o so} PTopCat@{o so}) : False.
Proof.
  exact (PTop_not_cocomplete_Freyd
           (PTop_ArrowIndex_transport@{s o s so}
              (canonical_ArrowIndex (DE : ObjDecEq PTopCat@{o s})))
           cocomp).
Qed.

Theorem PTop_not_cocomplete_IEM@{e r s o so +| o < so, o < s +}
  (E : IEM@{e}) (cocomp : @Cocomplete@{r s o so} PTopCat@{o so}) : False.
Proof.
  exact (PTop_not_cocomplete_ObjDecEq (ObjDecEq_of_IEM E PTopCat@{o so})
           cocomp).
Qed.

(*
 Through the recipe, the same boundary for the points: were [Sets]
 cocomplete at a shape universe above its carriers, Instance/Top/
 Cocomplete.v's [PTop_Colimit_lift] would make [PTopCat] cocomplete
 there. 

 --------
 通过该配方，相同的点边界是：[Sets] 在其承载者之上的形状宇宙中是完备的，Instance/Top/Cocomplete.v 的 [PTop_Colimit_lift] 会使 [PTopCat] 在那里完备。
*)
Theorem Sets_not_cocomplete_IEM@{e r s o so +| o < so, o < s +}
  (E : IEM@{e}) (cocomp : @Cocomplete@{r s o so} Sets@{o so}) : False.
Proof.
  exact (PTop_not_cocomplete_IEM E
           (fun D F => PTop_Colimit_lift F (cocomp D (PForget ◯ F)))).
Qed.

(* * ** The Type-valued [Top]: Freyd's form, and transported below the homs / * ** 类型值 [Top] ：Freyd 形式，并在下方传递了 homs *)

(*
 Freyd's form, the exact dual of Instance/Top/StoneCech/Refutations.v's
 [Top_not_complete]. 

 --------
 弗雷德的形式，即 Instance/Top/StoneCech/Refutations.v 的 [Top_not_complete] 的精确对偶。
*)
Theorem Top_not_cocomplete_Freyd@{r s h o +}
  (AI : ArrowIndex@{s h h} Top@{h o})
  (cocomp : @Cocomplete@{r s h h} Top@{h o}) : False.
Proof.
  exact (freyd_no_separated_pair (ArrowIndex_op AI)
           (a:=Bool_Discrete) (b:=Point_Top)
           (top_point Bool_Discrete true) (top_point Bool_Discrete false) _ _
           (complete_iprod (Complete_op_of_Cocomplete cocomp)
              (fun _ : ai_index (ArrowIndex_op AI) => Point_Top))
           (fun h => continuous_map h ttt) (fun u v H => H ttt)
           eq_refl eq_refl).
Qed.

(*
 Every shape universe strictly above the points, the shapes below the
 homs included, under decidable equality of spaces: the canonical index
 is built at [Top@{s o}] and transported by Instance/Top/Complete/
 Refutations.v's [Top_ArrowIndex_transport], as the limit side does. 

 --------
 每个形状宇宙严格位于这些点之上，形状低于同类的包括在内，在空间的可判定等式下：规范索引在 [Top@{s o}] 处构建，并通过 Instance/Top/Complete/Refutations.v 的 [Top_ArrowIndex_transport] 传送，就像极限端一样。
*)
Theorem Top_not_cocomplete_ObjDecEq@{r s h o +| o < h, o < s +}
  (DE : ObjDecEq Top@{h o})
  (cocomp : @Cocomplete@{r s h h} Top@{h o}) : False.
Proof.
  exact (Top_not_cocomplete_Freyd
           (Top_ArrowIndex_transport@{s o s h}
              (canonical_ArrowIndex (DE : ObjDecEq Top@{s o})))
           cocomp).
Qed.

Theorem Top_not_cocomplete_IEM@{e r s h o +| o < h, o < s +}
  (E : IEM@{e}) (cocomp : @Cocomplete@{r s h h} Top@{h o}) : False.
Proof.
  exact (Top_not_cocomplete_ObjDecEq (ObjDecEq_of_IEM E Top@{h o}) cocomp).
Qed.

(* * ** A second argument: Cantor's diagonal at the points of one coproduct / * ** 第二个论点：康托在一个余积点上的对角线 *)

(* No map from the predicates on a type into it is injective up to a reflexive relation: the predicate "encodes a predicate it does not hold of" holds of its own code exactly when it does not. / 没有从一个类型上的谓词到它自身的映射，在自反关系下是单射的：谓词“编码一个它不成立的谓词”正好在它自身的代码上成立，当且仅当它不成立时。 *)
Lemma cocomp_cantor_diagonal@{u} {A : Type@{u}} (R : A → A → Type@{u})
  (R_refl : ∀ a, R a a) (enc : (A → Prop) → A)
  (enc_inj : ∀ U V, R (enc U) (enc V) → U = V) : False.
Proof.
  pose (Dg := fun p : A => ex (fun U => inhabited (R (enc U) p) /\ ~ U p)).
  assert (N : ~ Dg (enc Dg)).
  { intros [U [[HU] nU]]. pose proof (enc_inj U Dg HU) as E.
    subst U. apply nU. exists Dg. split; [constructor; exact HU|exact nU]. }
  apply N. exists Dg. split; [constructor; exact (R_refl _)|exact N].
Qed.

(* * ** [PTopCat]: Cantor at the points of one coproduct / * ** [PTopCat] ：在一个余积的点上的康托尔 *)

(* The index of the coproduct: a space with a predicate on its points. It quantifies over the spaces, so it sits strictly above the points. / 余积的指标：一个其点上带有谓词的空间。它对空间进行量化，因此它严格位于点之上。 *)
Definition pcc_index@{o s | o < s +} : Type@{s} :=
  { X : PTop@{o} & pt_carrier X → Prop }.

Section PCantor.

Universes o so s r.
Constraint o < so.
Constraint o < s.

Context (DE : ObjDecEq PTopCat@{o so}).
Context (cocomp : @Cocomplete@{r s o so} PTopCat@{o so}).

#[local] Notation K := (pcc_index@{o s}).

(* A space [Om] and a family of its points [c k0 k] that recognizes [k0]: [c k0 k] is equivalent to [c k0 k0] only at [k = k0]. / 一个空间 [Om] 及其点族 [c k0 k]，识别 [k0]：[c k0 k] 仅在 [k = k0] 时等价于 [c k0 k0]。 *)
Context (Om : PTop@{o}) (c : K → K → pt_carrier Om).
Context (c_spec : ∀ k0 k, c k0 k ≈ c k0 k0 → k = k0).

Let CC := Complete_op_of_Cocomplete cocomp.

(*
 The coproduct of [pcc_index]-many points, which cocompleteness at [s]
 supplies. 

 --------
 [pcc_index] 许多点的余积，由 [s] 提供的余完备性。
*)
Definition pcc_sum : PTop@{o} :=
  complete_iprod_obj CC (fun _ : K => PPoint@{o}).

Definition pcc_inj (k : K) : PPoint@{o} ~{PTopCat@{o so}}~> pcc_sum :=
  complete_iprod_proj CC (fun _ : K => PPoint@{o}) k.

Definition pcc_leg (k0 k : K) : PPoint@{o} ~{PTopCat@{o so}}~> Om :=
  pdisc_mor unit_setoid_object Om (pconst unit_setoid_object Om (c k0 k)).

(* The copairing of the legs at [k0]. / 在 [k0] 的腿部配对。 *)
Definition pcc_sep (k0 : K) : pcc_sum ~{PTopCat@{o so}}~> Om :=
  unique_obj (iprod_desc (complete_iprod CC (fun _ : K => PPoint@{o}))
                (c:=Om) (pcc_leg k0)).

Lemma pcc_sep_at (k0 k : K) :
  pmap (pcc_sep k0) (pmap (pcc_inj k) ttt) ≈ c k0 k.
Proof.
  exact (unique_property
           (iprod_desc (complete_iprod CC (fun _ : K => PPoint@{o}))
              (c:=Om) (pcc_leg k0)) k ttt).
Qed.

(* A predicate on the points of the coproduct encodes to the point of its own summand. / 余积的点上的谓词编码到其自身子项的点上。 *)
Definition pcc_enc (U : pt_carrier pcc_sum → Prop) : pt_carrier pcc_sum :=
  pmap (pcc_inj (existT _ pcc_sum U)) ttt.

Lemma pcc_enc_inj (U V : pt_carrier pcc_sum → Prop) :
  pcc_enc U ≈ pcc_enc V → U = V.
Proof using All.
  intro H.
  pose proof (proper_morphism (pmap (pcc_sep (existT _ pcc_sum U))) _ _ H)
    as H1.
  assert (E : existT (fun X : PTop@{o} => pt_carrier X → Prop) pcc_sum V
              = existT _ pcc_sum U).
  { apply c_spec.
    transitivity (pmap (pcc_sep (existT _ pcc_sum U)) (pcc_enc V));
      [symmetry; exact (pcc_sep_at _ _)|].
    transitivity (pmap (pcc_sep (existT _ pcc_sum U)) (pcc_enc U));
      [symmetry; exact H1|exact (pcc_sep_at _ _)]. }
  symmetry. exact (inj_pair2_eq_dec _ DE _ _ _ _ E).
Qed.

Lemma pcc_contradiction : False.
Proof using All.
  exact (cocomp_cantor_diagonal (@equiv _ (pt_carrier pcc_sum))
           (fun p => reflexivity p) pcc_enc pcc_enc_inj).
Qed.

End PCantor.

(* The truth values, under [<->], as a setoid at the points' universe. / 在 [<->] 下的真值，作为点的宇宙中的集合型。 *)
Program Definition pcc_Prop@{o | Set < o} : SetoidObject@{o o} := {|
  carrier := Prop;
  is_setoid := {| equiv := fun P Q => P <-> Q |}
|}.
Next Obligation.
  constructor.
  - intro P; exact (iff_refl P).
  - intros P Q H; exact (iff_sym H).
  - intros P Q R H1 H2; exact (iff_trans H1 H2).
Qed.

(* Cocompleteness of [PTopCat] is refuted at every shape universe strictly above the points, under decidable equality of spaces: the separator is the discrete space of truth values. / [PTopCat] 的共完备性在每个严格高于点的形状宇宙中都被驳斥，在空间的可判等性下：分离器是真值的离散空间。 *)
Theorem PTop_not_cocomplete_Cantor_ObjDecEq@{r s o so +| o < so, o < s,
                                               Set < o +}
  (DE : ObjDecEq PTopCat@{o so})
  (cocomp : @Cocomplete@{r s o so} PTopCat@{o so}) : False.
Proof.
  apply (pcc_contradiction DE cocomp (PDiscrete pcc_Prop@{o})
           (fun k0 k => k = k0)).
  intros k0 k H. exact (proj2 H eq_refl).
Qed.

(* The same under informative excluded middle, with [PBool] as the separator, so that no [Set < o] is needed. / 在信息排除中间项下相同，使用 [PBool] 作为分隔符，因此不需要 [Set < o]。 *)
Theorem PTop_not_cocomplete_Cantor_IEM@{e r s o so +| o < so, o < s +}
  (E : IEM@{e}) (cocomp : @Cocomplete@{r s o so} PTopCat@{o so}) : False.
Proof.
  apply (pcc_contradiction
           (fun x y => match E (x = y) with
                       | inl e => left e
                       | inr n => right n
                       end) cocomp PBool@{o}
           (fun k0 k => match E (k = k0) with
                        | inl _ => true
                        | inr _ => false
                        end)).
  intros k0 k H. simpl in H.
  destruct (E (k = k0)) as [e|n]; [exact e|].
  destruct (E (k0 = k0)) as [_|n0]; [discriminate H|].
  destruct (n0 eq_refl).
Qed.

(* * ** The Type-valued [Top]: Cantor's argument / * ** 类型值 [Top] ：康托尔的论证 *)

Definition tcc_index@{o s | o < s +} : Type@{s} :=
  { X : TopSpace@{o} & top_carrier X → Prop }.

Section TCantor.

Universes o h s r.
Constraint o < h.
Constraint o < s.

Context (DE : ObjDecEq Top@{h o}).
Context (cocomp : @Cocomplete@{r s h h} Top@{h o}).

#[local] Notation K := (tcc_index@{o s}).

Context (Om : TopSpace@{o}) (c : K → K → top_carrier Om).
Context (c_spec : ∀ k0 k, c k0 k ≈ c k0 k0 → k = k0).

Let CC := Complete_op_of_Cocomplete cocomp.

Definition tcc_sum : TopSpace@{o} :=
  complete_iprod_obj CC (fun _ : K => Point_Top).

Definition tcc_inj (k : K) : Point_Top ~{Top@{h o}}~> tcc_sum :=
  complete_iprod_proj CC (fun _ : K => Point_Top) k.

Definition tcc_leg (k0 k : K) : Point_Top ~{Top@{h o}}~> Om :=
  top_point Om (c k0 k).

Definition tcc_sep (k0 : K) : tcc_sum ~{Top@{h o}}~> Om :=
  unique_obj (iprod_desc (complete_iprod CC (fun _ : K => Point_Top))
                (c:=Om) (tcc_leg k0)).

Lemma tcc_sep_at (k0 k : K) :
  continuous_map (tcc_sep k0) (continuous_map (tcc_inj k) ttt) ≈ c k0 k.
Proof.
  exact (unique_property
           (iprod_desc (complete_iprod CC (fun _ : K => Point_Top))
              (c:=Om) (tcc_leg k0)) k ttt).
Qed.

Definition tcc_enc (U : top_carrier tcc_sum → Prop) : top_carrier tcc_sum :=
  continuous_map (tcc_inj (existT _ tcc_sum U)) ttt.

Lemma tcc_enc_inj (U V : top_carrier tcc_sum → Prop) :
  tcc_enc U ≈ tcc_enc V → U = V.
Proof using All.
  intro H.
  pose proof (proper_morphism (continuous_map (tcc_sep (existT _ tcc_sum U)))
                _ _ H) as H1.
  assert (E : existT (fun X : TopSpace@{o} => top_carrier X → Prop) tcc_sum V
              = existT _ tcc_sum U).
  { apply c_spec.
    transitivity (continuous_map (tcc_sep (existT _ tcc_sum U)) (tcc_enc V));
      [symmetry; exact (tcc_sep_at _ _)|].
    transitivity (continuous_map (tcc_sep (existT _ tcc_sum U)) (tcc_enc U));
      [symmetry; exact H1|exact (tcc_sep_at _ _)]. }
  symmetry. exact (inj_pair2_eq_dec _ DE _ _ _ _ E).
Qed.

Lemma tcc_contradiction : False.
Proof using All.
  exact (cocomp_cantor_diagonal (@equiv _ (top_carrier tcc_sum))
           (fun p => reflexivity p) tcc_enc tcc_enc_inj).
Qed.

End TCantor.

Theorem Top_not_cocomplete_Cantor_ObjDecEq@{r s h o +| o < h, o < s,
                                              Set < o +}
  (DE : ObjDecEq Top@{h o})
  (cocomp : @Cocomplete@{r s h h} Top@{h o}) : False.
Proof.
  apply (tcc_contradiction DE cocomp (Discrete_Top pcc_Prop@{o})
           (fun k0 k => k = k0)).
  intros k0 k H. exact (proj2 H eq_refl).
Qed.

Theorem Top_not_cocomplete_Cantor_IEM@{e r s h o +| o < h, o < s +}
  (E : IEM@{e}) (cocomp : @Cocomplete@{r s h h} Top@{h o}) : False.
Proof.
  apply (tcc_contradiction
           (fun x y => match E (x = y) with
                       | inl e => left e
                       | inr n => right n
                       end) cocomp Bool_Discrete
           (fun k0 k => match E (k = k0) with
                        | inl _ => true
                        | inr _ => false
                        end)).
  intros k0 k H. simpl in H.
  destruct (E (k = k0)) as [e|n]; [exact e|].
  destruct (E (k0 = k0)) as [_|n0]; [discriminate H|].
  destruct (n0 eq_refl).
Qed.
