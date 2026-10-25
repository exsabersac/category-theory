Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Limit.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Fun.Exponential.
Require Import Category.Instance.Omega.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Skeleton.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Monoidal.

Require Import Coq.Vectors.Fin.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Generalizable All Variables.

(* * * Cartesian closure is NOT inherited by functor categories / * * 笛卡尔闭包并不继承于函子范畴 *)

(*
 Book:      Mac Lane, CWM 2nd ed., §IV.6 "Cartesian Closed Categories",
 Exercise 5, printed p. 98 ([maclane:IV.6:ex5]).  Verbatim:

 "5. Show that A cartesian closed need not imply A^J
 cartesian closed."

 Book:      Awodey, Category Theory, §8.7 "Exponentials in categories
 of diagrams", printed pp. 207-208
 (Awodey's unnumbered remark there that the pointwise
 formula does not define an exponential of presheaves;
 the catalog identifier for it is quoted verbatim in
 Test/ProbeFunClosed392.v, which carries it in full).
 Verbatim, with the question-mark-over-equals rendered as
 "=?":

 "Now suppose we have functors P, Q and we want Q^P.
 The reader should try to construct the exponential
 'pointwise',

 Q^P(C) =? Q(C)^{P(C)}

 to see that it does not work (it's not functorial)."

 nLab:      https://ncatlab.org/nlab/show/functor+category
 nLab:      https://ncatlab.org/nlab/show/cartesian+closed+category
 Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category

 The issue this file answers describes [Functor_Category_Cartesian]
 (Instance/Fun/Cartesian.v) as the only structure lemma for
 functor categories in the tree.  That is stale.  Sweeping the
 declaration heads that put a structure CLASS on a functor category
 as a whole, inherited from the target, returns five, and every one
 of them is POSITIVE and POINTWISE: that one, plus
 [Functor_Category_Terminal] and [Fun_HasIndexedProducts]
 (Instance/Fun/Terminal.v, both landed with #339),
 [Thin_Fun] (Instance/Proset/Closure.v) and [Fun_IsGroupoid]
 (Construction/Deloop/Transform.v).  Read the criterion, since
 the same sweep also returns constants of a DIFFERENT shape that are
 not counted among the five: subcategories OF a functor category
 ([ReprSubcat], [Models_sub]), structures on particular OBJECTS or
 MORPHISMS of one ([fun_gmonoid], [pare_idem_Idempotent],
 [pare_SplitIdempotent], [two_pick_Monic]), and instantiations of the
 five at a fixed pair ([Two_Sets_Terminal],
 [Two_Sets_HasIndexedProducts], [Deloop_Fun_IsGroupoid] of
 Construction/Deloop/Transform.v), and structures on a functor
 category as a whole that are NOT inherited from the target
 ([Compose_Monoidal], Structure/Monoidal/Compose.v, which is
 monoidal under COMPOSITION rather than pointwise).

 Exponentials are where that pattern stops, in two distinct senses,
 and this file separates them:

 (i)  the CONCLUSION can be false -- [A] cartesian closed and [J] a
 perfectly ordinary index category (small in the ordinary
 sense, its objects being the naturals; Theory/Size.v's
 [Class Small] is the tree's formal reading of the word and
 is not consumed here), yet [A^J] carries no
 cartesian closed structure at all; and

 (ii) even when [A^J] IS cartesian closed, its exponential is not
 computed objectwise -- the objectwise VALUE is already the
 wrong object, so no action on that family of values, however
 chosen, can be the exponential.

 WHAT DRIVES BOTH IS ONE LEMMA, and it is elementary.  In any
 cartesian closed category the transposition at the terminal object
 reads

 Hom(P, Q)  ~  Hom(1 x P, Q)  ~  Hom(1, Q^P),

 so morphisms P -> Q are (at least) as few as the points of Q^P.
 Section A gives that as an INJECTION [ccc_point] with an explicit
 injectivity proof; no bijection is claimed, and none is needed.
 Section B specialises the ambient to a functor category [J, A] whose
 INDEX has an initial object j0: the terminal object of [J, A] is the
 constant functor at 1_A ([Functor_Category_Terminal]), whose arrow
 action is the identity, so naturality of a transformation out of it
 at the unique arrow j0 -> j forces

 alpha_j  ~  fmap[E] (zero j) o alpha_{j0},

 and alpha is determined by its component at j0.  Section C composes
 the two into [fun_hom_point], the engine:

 if [J, A] is cartesian closed and J has an initial object j0,
 then Hom_{[J,A]}(P, Q) injects into Hom_A(1_A, (Q^P) j0).

 Sections E and F are the two applications.

 APPLICATION ONE (Mac Lane, Exercise 5).  Take A := skeletal [FinSet],
 which IS cartesian closed ([FinSet_Closed], Instance/FinSet/Closed.v),
 and J := [Omega], the ordinal omega, which HAS an initial object
 ([Omega_Initial], Structure/Limit/Initial.v).  In [FinSet] the
 hom-set Hom(1, n) is the maps [Fin.t 1 -> Fin.t n], and two of them
 agree as soon as they agree at [Fin.F1], so that hom-set has at most
 n elements: it is FINITE.  The engine therefore makes every hom-set
 of [Omega, FinSet] finite, as soon as that category is cartesian
 closed.  Section E exhibits a single functor [TwoFun] whose
 endomorphism monoid in [Omega, FinSet] is infinite -- an explicit
 family [Alpha k], k : nat, pairwise distinct -- and concludes
 [fun_not_cartesian_closed].

 THE STRENGTHENING LANDED.  [fun_not_cartesian_closed] quantifies over
 an ARBITRARY [@Cartesian ([Omega, FinSet])], not merely the pointwise
 one, so it is the strict reading of "not cartesian closed".  It costs
 nothing: the engine takes the cartesian structure as a parameter, and
 the only structure it pins is the TERMINAL object, which it supplies
 itself as [Functor_Category_Terminal FinSet_Terminal] rather than
 reading off the given [Cartesian] (that class carries no terminal
 object; see Instance/Fun/Cartesian.v).  So the given product
 structure is genuinely arbitrary throughout.

 APPLICATION TWO (Awodey's objectwise no-go).  Presheaves on the
 walking arrow, [_2^op, Sets].  The initial object of [_2^op] is
 [TwoY], because [TwoY] is terminal in [_2] ([Two_Terminal],
 Instance/Two/Monoidal.v); this needs no transport, since
 [Initial C] is NOTATION for [@Terminal (C^op)] and [(C^op)^op] is [C]
 definitionally.  [PresheafP] takes [TwoX] to the terminal setoid and
 [TwoY] to the initial (empty) one -- the representable at [TwoX],
 built directly rather than through Yoneda, whose in-tree statement
 carries a universe restriction this argument does not need.
 [PresheafQ] is constant at a two-element setoid.  Then
 Hom(P, Q) has (at least) TWO elements: the component at [TwoY] is a
 map out of the empty setoid, so it is unique and naturality is
 vacuous, while the component at [TwoX] may be either point of Q.  By
 the engine, (Q^P) TwoY then has two distinct points.  The objectwise
 candidate Q(TwoY)^{P(TwoY)} is the exponential IN [Sets] of a
 two-element setoid by the EMPTY one, and any two of its points are
 equivalent.  Hence [awodey_pointwise_not_exponential].

 BE PRECISE ABOUT WHAT THAT DOES AND DOES NOT SAY.  Awodey's stated
 reason is that the objectwise assignment "is not functorial".  Read
 literally, "there is no contravariant action on this family of sets"
 would be FALSE for the family at hand, which does carry an action --
 though NOT because every family does: over [_2] the family that is a
 singleton at [TwoX] and empty at [TwoY] carries none.  What is proved
 here is different in kind, and stronger in the way that matters: the
 objectwise VALUES are already the wrong objects, so NO action
 whatsoever on them can produce the exponential.  This file does not
 formalize the sentence "it is not functorial"; it formalizes a
 statement that makes the sentence moot.

 THAT SECOND THEOREM IS STATED CONDITIONALLY, AND ITS HYPOTHESIS IS
 NOW DISCHARGED.  It is stated for an arbitrary
 [@Closed ([_2^op, Sets]) CC].  When this file was written nothing in
 tree witnessed that hypothesis; issue #718 has since landed the
 witness, in Instance/Fun/Exponential.v, whose
 [Functor_Category_Closed] gives a genuine cartesian closed structure
 on any presheaf category.  Section G below instantiates section F at
 it, so [awodey_pointwise_not_exponential_unconditional] carries no
 hypothesis at all.  Nothing in sections A-F changed: the conditional
 statements are kept exactly as they were, and the instantiation is
 additive.  Application one had no such caveat to begin with: it is
 unconditional.

 UNIVERSES, MEASURED.  Both ambient categories elaborate, and the
 measurement was made before any content was written.
 [Omega@{o h p}] is fully polymorphic and [FinSet@{u u0 u1 u2}] has
 hom and proof at one free level, so [Omega, FinSet] carries no [Set]
 beyond [FinSet]'s own [Set < u1].  By contrast [_2@{u u0}] is
 declared [Category@{u Set Set}] -- its homs are the literal [Set] --
 and [Fun] identifies its source and target hom universes, while
 [Sets@{o so} : Category@{so o o}] has its hom universe EQUAL to its
 carrier universe.  So [_2^op, Sets] elaborates only at
 [Sets@{Set _}]: the presheaves of section F take values in setoids
 whose CARRIER lives in [Set].  That attribution is measured, not
 guessed -- replacing [_2^op] by the polymorphic [Omega] leaves
 [Sets]'s carrier universe free ([Omega, Sets] elaborates at
 [Sets@{u u0}] with [u] unconstrained) -- and the pin is [_2]'s, not
 introduced here, and is not claimed unavoidable.  It restricts the
 CONTENT of section F, not merely its presentation: the theorem there
 is about presheaves valued in small setoids.  The three witnesses
 used are all of that size.

 LOCAL LEMMA.  Section D proves a pigeonhole principle for
 [Fin.t]: there is no injective family [nat -> Fin.t N].  It is local
 because the tree has none.  The nearest thing is the [assert] inside
 the proof of [fin_bijection_index] (Instance/FinSet/Skeleton.v),
 which runs the same counting argument but is sealed by [Qed] and so
 cannot be reused; the [pigeon] of Instance/Ab/Character/Finite.v
 is a different statement, over a setoid with a decider, in a section
 whose context this file does not have.  The ingredients [fin_enum],
 [fin_enum_length], [fin_enum_full], [fin_enum_nodup] and
 [length_of_map] ARE taken from Skeleton.v, and only
 [List.NoDup_incl_length] comes from the standard library -- the same
 lemma Skeleton.v already uses, so the portability across the
 supported Coq/Rocq versions is the one that file already relies on.

 SETOID DISCIPLINE.  Morphism equality is written [~] everywhere
 except where the ambient hom-setoid IS Leibniz equality and the goal
 has already been unfolded to it: [FinSet]'s hom-setoid is
 [fun_setoid], i.e. pointwise [=] on functions [Fin.t m -> Fin.t n],
 and [Omega]'s and [_2]'s are [Morphism_equality], i.e. Leibniz [=] on
 arrows.  Most [=] below are between ELEMENTS -- of [Fin.t n], of
 [nat], of a carrier -- and not between morphisms at all; the ones
 that do relate morphisms are exactly the [FinSet] obligations, whose
 [=] IS that category's [~], and they are flagged in place.

 WHAT IS NOT DELIVERED -- read this as the scope of the file.

 * The POSITIVE companion IN ITS GENERAL FORM is NOT here.  Nothing
 below proves that [C] small and [D] cartesian closed and COMPLETE
 gives [C, D] cartesian closed, and no attempt is made at it.

 * The PRESHEAF case of that positive theorem -- [D := Sets] -- is
 issue #718's, and it landed in Instance/Fun/Exponential.v rather
 than in this file, on a measured closure argument.  Before that
 file existed this one's transitive dependency closure was 81
 modules and Instance/Fun/Exponential.v's is 62; twenty modules
 lie in the first and not the second (the chains beneath
 Instance/FinSet with its Closed, Product and Skeleton satellites
 -- Theory/Skeleton, Instance/StrictCat and the equivalence
 modules arrive through the last -- and beneath Instance/Omega,
 Structure/Limit/Initial and Instance/Two/Monoidal, which sections
 D, E and F need and the positive theorem does not) and exactly
 one lies in the second and not the first
 (Functor/Hom.v), so a consumer of the exponential would have paid
 19 net extra modules to get it from here.  Requiring it from here
 instead takes this file's closure from 81 to 83 -- the new file
 plus Functor/Hom.v.  The two negative theorems here scope the
 positive one (they say which hypotheses may not be dropped)
 rather than colliding with it, and section G below consumes it.

 * No end formula, limit formula, or any other construction of
 exponentials in a functor category is built.

 * Nothing here says which pairs (J, A) DO give a cartesian closed
 [J, A].  Only one pair is examined.

 * The counterexample of section E uses ONE pair, ([Omega],
 [FinSet]).  No characterisation is claimed, and no other pair is
 tested.  In particular nothing is proved about [Omega] with a
 complete target, or about [FinSet] over a different index.

 * Whether [FinSet] is locally cartesian closed is not touched, and
 neither is the classical statement that [A^2] is cartesian closed
 exactly when [A] is locally cartesian closed.

 * Section B proves an INJECTION and no more.  The reverse map
 (every point of E j0 extends to a transformation) is not built,
 so nothing here is a bijection, and none is needed.

 * That [FinSet] is not COMPLETE is nowhere proved.  What the
 counterexample establishes is that the conclusion of the positive
 theorem can be false when C is small and D is cartesian closed;
 relative to that theorem it follows that completeness of D is
 doing real work, but the incompleteness of this particular D is
 an inference and not a theorem in tree.

 * The count of Hom(P, Q) in section F is a lower bound: TWO
 distinct transformations are exhibited, and nothing proves there
 are no others.  Two is all the argument uses.

 * Nothing below is registered as an [Instance].

 * This file contributes NO lines to [make todo].  The Awodey
 remark is cited by name rather than by its catalog identifier,
 precisely because that identifier contains letters the target
 greps for; the identifier itself is quoted in
 Test/ProbeFunClosed392.v.  That probe does contribute lines to
 the report, as every probe in this tree does. 

 --------
 书籍：      Mac Lane, CWM 第二版，§IV.6 “笛卡尔闭范畴”，练习 5，印刷第 98 页（[maclane:IV.6:ex5]）。原文逐字：

 “5. 证明一个笛卡尔闭范畴不一定意味着 A^J 也是笛卡尔闭范畴。”

 书籍：      Awodey，《范畴论》，§8.7 “图范畴中的指数对象”，印刷第 207-208 页（Awodey 在那里未编号的备注指出逐点公式并不定义预层的指数；其目录标识符在 Test/ProbeFunClosed392.v 中逐字引用，该文件完整保留了它）。逐字翻译，问号上方的等号呈现为 “=?”：现在假设我们有函子 P、Q，并且我们想要 Q^P。读者应该尝试构造指数
 “逐点”，

 Q^P(C) =? Q(C)^{P(C)}

 以看看它为什么不可行（它不是函子性的）。

 nLab: https://ncatlab.org/nlab/show/functor+category
 nLab: https://ncatlab.org/nlab/show/cartesian+closed+category
 Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category本文件所回答的问题描述了 [Functor_Category_Cartesian] （Instance/Fun/Cartesian.v）作为树中函子范畴的唯一结构引理。那已经过时。扫描将结构 CLASS 施加在整个函子范畴上的声明头（继承自目标）会返回五个，每一个都是 POSITIVE 并且是 POINTWISE：那一个，加上 [Functor_Category_Terminal] 和 [Fun_HasIndexedProducts] （Instance/Fun/Terminal.v，均收录于 #339），[Thin_Fun] （Instance/Proset/Closure.v）和 [Fun_IsGroupoid] （Construction/Deloop/Transform.v）。阅读标准，因为相同的遍历还会返回不同形状的常数，这些常数不算在五个之内：函子范畴的子类 ([ReprSubcat], [Models_sub])、特定对象或一个对象的态射上的结构 ([fun_gmonoid], [pare_idem_Idempotent], [pare_SplitIdempotent], [two_pick_Monic])，以及在固定对上的五个实例化 ([Two_Sets_Terminal], [Two_Sets_HasIndexedProducts], [Deloop_Fun_IsGroupoid]，来自 Construction/Deloop/Transform.v)，以及整个函子范畴上的结构，这些结构不是从目标继承的 ([Compose_Monoidal], Structure/Monoidal/Compose.v，该结构在组合下是幺半群性的，而非逐点的)。

 指数是该模式停止的地方，有两种不同的意义，并且该文件将它们区分开来：(i) 结论可能是错误的——[A] 是笛卡尔闭的，而 [J] 是一个完全普通的指标范畴（在通常意义下是小的，它的对象是自然数；Theory/Size.v 中的 [Class Small] 是该词在树上的形式读取，在这里未被使用），尽管如此 [A^J] 完全不具有笛卡尔闭结构；并且

 (ii) 即使 [A^J] 是笛卡尔闭的，其指数也不是按对象计算的——按对象计算的值已经是错误的对象，所以对那组值的任何操作，无论如何选择，都不能成为指数。

 导致这两者的原因是一个引理，它是基本的。在任何笛卡尔闭范畴中，终对象处的转置可表示为

 Hom(P, Q)  ~  Hom(1 x P, Q)  ~  Hom(1, Q^P),所以函子 P -> Q 的态射至少和 Q^P 的点一样少。
 A 节给出了 [ccc_point] 作为一个单射，并提供了一个明确的单射性证明；没有声称存在双射，也不需要双射。
 B 节将环境特化为函子范畴 [J, A]，其指标有一个初始对象 j0：[J, A] 的终对象是常值函子在 1_A ([Functor_Category_Terminal]) 上，其箭头作用是恒等映射，因此从它出发的变换在唯一箭头 j0 -> j 上的自然性迫使：

 alpha_j  ~  fmap [E]  (zero j) o alpha_{j0},

 alpha 由其在 j0 上的分量决定。C 节将两者合成为 [fun_hom_point]，即核心引擎：

 如果 [J, A] 是笛卡尔闭范畴且 J 有初始对象 j0，那么 Hom_{[J,A]}(P, Q) 可以注入到 Hom_A(1_A, (Q^P) j0) 中。E 和 F 节是两个应用。

 应用一（Mac Lane，练习 5）。取 A := 骨架 [FinSet]，它是笛卡尔闭合的（[FinSet_Closed]，Instance/FinSet/Closed.v），并取 J := [Omega]，即序数 omega，它有一个初始对象（[Omega_Initial]，Structure/Limit/Initial.v）。在 [FinSet] 中，Hom(1, n) 的同态集是映射 [Fin.t 1 -> Fin.t n]，并且只要它们在 [Fin.F1] 上一致，两者就一致，所以该同态集最多有 n 个元素：它是有限的。因此，该引擎使得 [Omega, FinSet] 的每个同态集都是有限的，只要该范畴是笛卡尔闭合的。E 节展示了一个单一函子 [TwoFun]，其在 [Omega, FinSet] 中的自同态幺半群是无限的——一个显式的族 [Alpha k]，k : nat，彼此不同——并得出结论 [fun_not_cartesian_closed]。加强已经落实。[fun_not_cartesian_closed] 在一个任意的 [@Cartesian ([Omega, FinSet] 上进行量化，而不仅仅是逐点的那个，因此这是“非笛卡尔闭合”的严格解读。它不花费任何代价：引擎将笛卡尔结构作为参数，并且它固定的唯一结构是终对象，它自己提供为 [Functor_Category_Terminal FinSet_Terminal]，而不是从给定的 [Cartesian] 中读取（该类不包含终对象；参见 Instance/Fun/Cartesian.v）。因此，给定的乘积结构在整个过程中都是完全任意的。应用二（Awodey 的对象级不可行定理）。在行箭头上的预层，[_2^op, Sets]。[_2^op] 的初始对象是 [TwoY]，因为 [TwoY] 在 [_2] 中是终对象（[Two_Terminal]，Instance/Two/Monoidal.v）；这不需要迁移，因为 [Initial C] 是 [@Terminal (C^op)] 的符号表示，并且 [(C^op)^op] 在定义上是 [C]。[PresheafP] 将 [TwoX] 映射到终集合同态，将 [TwoY] 映射到初始（空）同态——在 [TwoX] 上可表示，直接构造而非通过 Yoneda，其树内陈述携带一个宇宙限制，而此论证不需要。[PresheafQ] 在一个两元素集合同态上是常数。那么
 Hom(P, Q) 至少有两个元素：在 [TwoY] 处的分量是一个从空集合到的映射，因此它是唯一的，并且自然性是空的，而在 [TwoX] 处的分量可以是 Q 的任意一个点。根据引擎，(Q^P) TwoY 则有两个不同的点。按对象的候选 Q(TwoY)^{P(TwoY)} 是在 [Sets] 中的指数，即一个两元素集合由空集合构成的指数，它的任意两个点都是等价的。因此 [awodey_pointwise_not_exponential]。要精确说明这句话说了什么和没说什么。Awodey 所陈述的理由是，按对象分配“不是函子性的”。字面理解，“在这组集合族上没有逆变作用”对于当前这个集合族来说是错误的，因为它确实带有作用——尽管不是因为每个集合族都有：在 [_2] 上，那族在 [TwoX] 是单元素而在 [TwoY] 是空的，则不带任何作用。此处证明的内容在性质上不同，而且在关键方式上更强：按对象的值本身已经是错误的对象，因此对它们进行任何操作都无法产生指数。这个文件并没有形式化“它不是函子性”的句子；它形式化了一个使该句子变得无关紧要的陈述。第二个定理是有条件陈述的，其假设现在已经解除。它针对一个任意的 [@Closed ([_2^op, Sets] ) CC] 陈述。当这个文件编写时，树中没有任何东西能证明该假设；问题 #718 后来提供了见证，在 Instance/Fun/Exponential.v 中，其 [Functor_Category_Closed] 在任何预层范畴上给出一个真正的笛卡尔闭结构。下面的 G 节将 F 节实例化于它，因此 [awodey_pointwise_not_exponential_unconditional] 完全不携带任何假设。A-F 节中没有任何改变：条件性陈述完全保留原样，实例化是附加的。最初的应用没有这样的限制：它是无条件的。宇宙，被测量。两种环境类别都得到了展开，并且测量是在任何内容被写入之前进行的。[Omega@{o h p}] 是完全多态的，而 [FinSet@{u u0 u1 u2}] 在一个自由层级上具有同态和证明，因此 [Omega, FinSet] 不携带任何超出 [FinSet] 自身 [Set < u1] 的 [Set]。相比之下，[_2@{u u0}] 被声明为 [Category@{u Set Set}] ——它的同态是字面意义上的 [Set]——而 [Fun] 指明其源和目标同态宇宙，而 [Sets@{o so} : Category@{so o o}] 的同态宇宙等于其承载宇宙。因此 [_2^op, Sets] 仅在 [Sets@{Set _}] 处展开：F 节的预层取值于其承载者存在于 [Set] 的集合同类中。这种归属是经过测量的，而不是猜测的——将 [_2^op] 替换为多态的 [Omega] 会让 [Sets] 的载体宇宙保持自由（[Omega, Sets] 在 [Sets@{u u0}] 处详细说明，[u] 不受约束）——而且引脚是 [_2] 的，而不是在此引入，并且并不声称不可避免。它限制的是 F 部分的内容，而不仅仅是其呈现形式：那里的定理关于取值于小型集合类的预层。使用的三个见证者都是那个大小。本地引理。第D节证明了[Fin.t]的鸽笼原理：不存在注入族[nat -> Fin.t N]。之所以称为本地，是因为该树没有。最接近的类似内容是[fin_bijection_index]（Instance/FinSet/Skeleton.v）的证明中的[assert]，它运行相同的计数论证，但被[Qed]封存，因此无法重用；Instance/Ab/Character/Finite.v中的[pigeon]是不同的陈述，涉及一个带有判定器的等值类集合，在本文件没有的上下文段落中。成分[fin_enum]、[fin_enum_length]、[fin_enum_full]、[fin_enum_nodup]和[length_of_map]取自Skeleton.v，只有[List.NoDup_incl_length]来自标准库——这是Skeleton.v已经使用的相同引理，因此不同Coq/Rocq版本间的可移植性正是该文件已经依赖的。集合等价纪律。态射的等式到处写作 [~]，除了当所在的同态集合是莱布尼茨等式且目标已经被展开到它时：[FinSet] 的同态集合是 [fun_setoid]，即函数 [Fin.t m -> Fin.t n] 上的逐点 [=]，而 [Omega] 和 [_2] 的则是 [Morphism_equality]，即箭头上的莱布尼茨 [=]。以下大多数 [=] 是在元素之间——[Fin.t n]、[nat]、载体的元素之间——而根本不是在态射之间；那些确实涉及态射的，正是 [FinSet] 的义务，其 [=] 是该范畴的 [~]，并且在原处标记出来。未提供的内容——可将其理解为文件的范围。* 一般形式下的正伴随不存在于此。以下内容没有证明 [C] 是小的，并且 [D] 是笛卡尔闭合且完备的，因此 [C, D] 是笛卡尔闭合的，也没有尝试去证明。* 关于那个正定定理的 PRESHEAF 情况——[D := Sets]——属于第718期的问题，它最终出现在 Instance/Fun/Exponential.v 文件中，而不是这个文件中，这是基于一个测度闭包的论证。在那之前，这个文件存在时，它的传递依赖闭包是 81 个模块，而 Instance/Fun/Exponential.v 的依赖闭包是 62 个模块；有二十个模块存在于第一个而不在第二个（在 Instance/FinSet 及其 Closed、Product 和 Skeleton 附属模块下的链 —— Theory/Skeleton、Instance/StrictCat 和等价模块通过最后一个到达 —— 以及在 Instance/Omega、Structure/Limit/Initial 和 Instance/Two/Monoidal 下，这些部分 D、E 和 F 需要，而正向定理不需要），而正好有一个模块存在于第二个而不在第一个（Functor/Hom.v），因此指数函数的使用者需要额外支付 19 个净模块才能从这里获得它。从这里要求它
 反而将此文件的闭包从81扩展到83 -- 新文件
 以及Functor/Hom.v。这里的两个否定定理限制了
 肯定定理的范围（它们说明哪些假设不能被删除），
 而不会与其冲突，下文G节使用了它。

 * 没有构建结尾公式、极限公式，或函子范畴中指数的任何其他构造。

 * 这里没有说明哪些对 (J, A) 确实给出了笛卡儿闭合的
 [J, A]。只检查了一个对。

 * E节的反例使用了一个对，([Omega], [FinSet])。
 没有声称有任何特征化，也没有测试其他对。特别是，
 对于 [Omega] 具有完备目标，或者 [FinSet] 在不同索引下，
 都没有证明任何内容。* 是否 [FinSet] 是局部笛卡尔封闭没有涉及，  
 经典结论 [A^2] 当且仅当 [A] 是局部笛卡尔封闭也没有涉及。

 * B 节只证明了一个单射，并没有更多。反向映射（E j0 的每个点都可以扩展为一个变换）没有建立，因此这里没有任何是双射，并且也不需要。

 * [FinSet] 不是完备的在任何地方都没有被证明。反例所确立的是，当 C 很小且 D 是笛卡尔封闭时，正定理的结论可能是假的；相对于该定理，这表明 D 的完备性起到了真正作用，但这个特定 D 的不完备性只是一个推论，并不是树中的定理。* 第 F 节中 Hom(P, Q) 的计数是一个下界：展示了两个不同的变换，并没有证明确实不存在其他变换。论证仅使用这两个。

 * 以下内容未被注册为 [Instance]。

 * 本文件未向 [make todo] 输出任何行。Awodey 的批注是以名字引用而非目录标识符引用的，正是因为该标识符包含目标 grep 查找的字母；该标识符本身在 Test/ProbeFunClosed392.v 中被引用。该探针确实为报告贡献了行，就像该树中的每个探针一样。
*)

(* * ** A: points of an exponential, in any cartesian closed category / * ** A：指数的点，在任意笛卡尔闭范畴中 *)

Section CCCPoints.

Context {C : Category}.
Context {CC : @Cartesian C}.
Context {CT : @Terminal C}.
Context {CL : @Closed C CC}.

(*
 The transpose of [f o exr : 1 x P ~> Q].  This is the composite

 Hom(P, Q) -> Hom(1 x P, Q) -> Hom(1, Q^P)

 of precomposition with the projection [exr : 1 x P ~> P] and the
 currying isomorphism.  The second map is invertible; the first is
 left-cancellable because [exr] is split epi, its section being the
 pairing of [one] with the identity.  Hence the composite is
 injective. 

 --------
 [f o exr : 1 x P ~> Q] 的转置。这是由投影 [exr : 1 x P ~> P] 的前合成以及柯里化同构组成的复合映射

 Hom(P, Q) -> Hom(1 x P, Q) -> Hom(1, Q^P)

 第二个映射是可逆的；第一个映射是左可抵消的，因为 [exr] 是分裂满射，它的截面是 [one] 与恒等映射的配对。因此该复合映射是单射的。
*)
Definition ccc_point {P Q : C} (f : P ~> Q) :
  @terminal_obj C CT ~> @exponent_obj C CC CL P Q :=
  @curry C CC CL _ P Q (f ∘ exr).

(*
 Distinct morphisms have distinct points.  Uncurrying undoes [curry]
 ([uncurry_curry]), and [exr o (one /\ id) ~ id] ([exr_fork]) cancels
 the projection. 

 --------
 不同的态射有不同的点。展开函数可以撤销 [curry] ([uncurry_curry])，而 [exr o (one /\ id) ~ id] ([exr_fork]) 取消了投影。
*)
Lemma ccc_point_inj {P Q : C} (f g : P ~> Q) :
  ccc_point f ≈ ccc_point g -> f ≈ g.
Proof.
  intro H.
  unfold ccc_point in H.
  assert (Hu : f ∘ (@exr C CC (@terminal_obj C CT) P) ≈ g ∘ exr).
  { rewrite <- (uncurry_curry (f ∘ exr)).
    rewrite <- (uncurry_curry (g ∘ exr)).
    now rewrite H. }
  rewrite <- (id_right f), <- (id_right g).
  rewrite <- (exr_fork (@one C CT P) (id[P])).
  rewrite !comp_assoc.
  now rewrite Hu.
Qed.

End CCCPoints.

(*
   * ** B: a transformation out of the constant functor is determined at
   the initial index 

   --------
   * ** B: 从初始索引可以确定一个常量函子之外的变换
*)

Section ConstantPoints.

Context {J A : Category}.
Context {JI : @Initial J}.
Context {AT : @Terminal A}.

(*
 [Functor_Category_Terminal AT]'s object is [Constant_Terminal_Functor
 AT], the constant functor at 1_A, so a component of [a] at [j] has
 type [1_A ~> E j] on the nose -- no transport is involved. 

 --------
 [Functor_Category_Terminal AT] 的对象是 [Constant_Terminal_Functor AT]，即 1_A 处的常量函子，因此 [a] 在 [j] 处的一个分量的类型正好是 [1_A ~> E j]——不涉及任何迁移。
*)
Definition fun_const_point {E : J ⟶ A}
  (a : @terminal_obj ([J, A]) (Functor_Category_Terminal AT)
         ~{[J, A]}~> E) :
  @terminal_obj A AT ~{A}~> E (@initial_obj J JI) :=
  @transform _ _ _ _ a (@initial_obj J JI).

(*
 The arrow action of the constant functor is the identity, so the
 naturality square at [zero j : 0 ~> j] reads
 [fmap[E] (zero j) o a_0 ~ a_j o id], and the component at [j] is
 forced by the component at [0]. 

 --------
 恒等函子（constant functor）的箭头作用是恒等映射，所以在 [zero j : 0 ~> j] 上的自然性方形为 [fmap[E] (zero j) o a_0 ~ a_j o id]，而在 [j] 上的分量由在 [0] 上的分量所决定。
*)
Lemma fun_const_point_inj {E : J ⟶ A}
  (a b : @terminal_obj ([J, A]) (Functor_Category_Terminal AT)
           ~{[J, A]}~> E) :
  fun_const_point a ≈ fun_const_point b -> a ≈ b.
Proof.
  intros H j.
  pose proof (@naturality _ _ _ _ a _ _ (@zero J JI j)) as Na.
  pose proof (@naturality _ _ _ _ b _ _ (@zero J JI j)) as Nb.
  simpl in Na, Nb.
  rewrite id_right in Na, Nb.
  rewrite <- Na, <- Nb.
  unfold fun_const_point in H.
  now rewrite H.
Qed.

End ConstantPoints.

(** ** C: the engine / ** C：发动机 *)

Section Engine.

Context {J A : Category}.
Context {JI : @Initial J}.
Context {AT : @Terminal A}.
Context {CC : @Cartesian ([J, A])}.
Context {CL : @Closed ([J, A]) CC}.

(*
 Hom_{[J,A]}(P, Q) injects into Hom_A(1_A, (Q^P) 0).  The [Cartesian]
 structure [CC] is arbitrary; the TERMINAL object is supplied here as
 the pointwise one, which is what makes section B applicable. 

 --------
 Hom_{ [J,A] }(P, Q) 注入到 Hom_A(1_A, (Q^P) 0) 中。[Cartesian] 结构 [CC] 是任意的；这里提供的终端对象是逐点的那个，这正是使 B 节适用的原因。
*)
Definition fun_hom_point {P Q : [J, A]} (f : P ~{[J, A]}~> Q) :
  @terminal_obj A AT
    ~{A}~> (@exponent_obj _ CC CL P Q) (@initial_obj J JI) :=
  @fun_const_point J A JI AT (@exponent_obj _ CC CL P Q)
    (@ccc_point ([J, A]) CC (Functor_Category_Terminal AT) CL P Q f).

Lemma fun_hom_point_inj {P Q : [J, A]} (f g : P ~{[J, A]}~> Q) :
  fun_hom_point f ≈ fun_hom_point g -> f ≈ g.
Proof.
  intro H.
  apply (@ccc_point_inj ([J, A]) CC (Functor_Category_Terminal AT) CL).
  apply (@fun_const_point_inj J A JI AT).
  exact H.
Qed.

End Engine.

(*
   * ** D: a local pigeonhole principle for [Fin.t]

   Neither statement below exists in the tree; see the header for what
   was searched and what was reused.  The nearest prior art for
   [nodup_map_inj] is [map_FS_NoDup] (Instance/Matr/Determinant.v),
   which is its instance at [h := Fin.FS]; the general statement is
   absent. 

   --------
   * ** D: 关于 [Fin.t] 的局部鸽巢原理  

   树中不存在以下任一语句；请参阅标题以查看搜索内容及重用内容。  
   [nodup_map_inj] 最近的现有成果是 [map_FS_NoDup]（Instance/Matr/Determinant.v），  
   它在 [h := Fin.FS] 处的实例；一般语句不存在。
*)

Lemma nodup_map_inj {A B : Type} (h : A -> B) (l : list A) :
  (forall x y, h x = h y -> x = y) ->
  List.NoDup l -> List.NoDup (List.map h l).
Proof.
  intros Hinj Hnd.
  induction Hnd as [| a l Hnin Hnd IH]; simpl.
  - constructor.
  - constructor; [ | exact IH ].
    intro Hin.
    apply List.in_map_iff in Hin.
    destruct Hin as [b [Hb Hb']].
    apply Hinj in Hb; subst.
    contradiction.
Qed.

(*
 There is no injective family [nat -> Fin.t N]: restrict it along
 [Fin.to_nat] to get [S N] distinct elements of an [N]-element type. 

 --------
 没有单射族 [nat -> Fin.t N]：沿着 [Fin.to_nat] 限制它以获得 [S N] 个不同的 [N] 元素类型。
*)
Lemma fin_no_nat_injection {N : nat} (w : nat -> Fin.t N)
  (winj : forall i j, w i = w j -> i = j) : False.
Proof.
  pose (v := fun i : Fin.t (S N) => w (proj1_sig (Fin.to_nat i))).
  assert (vinj : forall i j, v i = v j -> i = j).
  { intros i j Hij; apply Fin.to_nat_inj; now apply winj. }
  assert (Hnd : List.NoDup (List.map v (fin_enum (S N))))
    by (apply nodup_map_inj; [ exact vinj | apply fin_enum_nodup ]).
  assert (Hincl : List.incl (List.map v (fin_enum (S N))) (fin_enum N))
    by (intros x _; apply fin_enum_full).
  pose proof (List.NoDup_incl_length Hnd Hincl) as Hle.
  rewrite length_of_map, !fin_enum_length in Hle.
  exact (Nat.nle_succ_diag_l N Hle).
Qed.

(** ** E: Mac Lane §IV.6 Exercise 5 / ** E: Mac Lane §IV.6 练习 5 *)

(*
 The hypothesis of the exercise, consumed by name so that the theorem
 below is visibly about a cartesian closed TARGET: skeletal [FinSet]
 is cartesian closed, with n^m the canonical (n^m)-element set. 

 --------
 练习的假设，被命名以便下面的定理明显关于笛卡尔闭合的目标：skeletal  [FinSet] 是笛卡尔闭合的，其中 n^m 是规范的 (n^m)-元素集合。
*)
Definition FinSet_is_cartesian_closed : @Closed FinSet FinSet_Cartesian :=
  FinSet_Closed.

(*
 An arrow of [Omega] is a derivation of [le_t n m]; it is the identity
 exactly in the [le_t_n] branch.  [two_map] sends the identity to the
 identity of the two-element set and every genuine step to the
 constant map at [Fin.F1].  Both equalities below are in [FinSet]'s
 hom-setoid [fun_setoid], which is pointwise Leibniz equality of
 functions [Fin.t 2 -> Fin.t 2], and in [Omega]'s [Morphism_equality],
 which is Leibniz equality of arrows -- so [fmap_respects] is
 discharged by substitution. 

 --------
 [Omega] 的一个箭头是 [le_t n m] 的一个推导；它在 [le_t_n] 分支中是恒等的。[two_map] 将恒等映射到两元素集合的恒等映射，并将每个真正的步骤映射到常值映射 [Fin.F1]。下面的两个等式都在 [FinSet] 的同态集合 [fun_setoid] 中，它是函数 [Fin.t 2 -> Fin.t 2] 的逐点莱布尼茨等式，并且在 [Omega] 的 [Morphism_equality] 中，它是箭头的莱布尼茨等式——因此 [fmap_respects] 可以通过替代消去。
*)
Definition two_map@{h} {n m : nat} (f : le_t@{h} n m) : Fin.t 2 -> Fin.t 2 :=
  match f with
  | le_t_n   => fun i => i
  | le_t_S _ => fun _ => Fin.F1
  end.

(*
 Functoriality.  Composition in [Omega] is [compose f g = le_t_trans g
 f], and [le_t_trans] recurses on its SECOND argument, so a case split
 on [f] reduces both sides at once.

 THE UNIVERSE BINDERS HERE ARE LOAD-BEARING, and that is measured:
 written without them the same body minimizes to
 [Omega@{_ Set Set} ⟶ FinSet@{...}], pinning [Omega]'s hom and proof
 universes to the literal [Set], and the section below -- where
 [Omega, FinSet] is elaborated once, for the [Cartesian] parameter --
 then declines the resulting object.  Spelling the binders out leaves
 both categories free.  Test/ProbeFunClosed392.v pins the rejection
 against the annotated form as its control. 

 --------
 函子性。在  [Omega] 中的复合是 [compose f g = le_t_trans g f]，并且 [le_t_trans] 对其第二个参数进行递归，因此在 [f] 上进行情况拆分会同时简化两边。

 这里的宇宙绑定器是承重的，而且这是有衡量的：如果没有它们写出来，相同的主体会简化为 [Omega@{_ Set Set} ⟶ FinSet@{...}]，将 [Omega] 的同态和证明宇宙固定为字面上的 [Set]，下面的部分——其中 [Omega, FinSet] 为 [Cartesian] 参数展开一次——随后会拒绝生成的对象。明确写出绑定器会让两个范畴都保持自由。Test/ProbeFunClosed392.v 将其拒绝与带注释的形式作为对照。
*)
Program Definition TwoFun@{o h p u u0 u1 u2 +}
  : Omega@{o h p} ⟶ FinSet@{u u0 u1 u2} := {|
  fobj := fun _ => 2%nat;
  fmap := fun _ _ f => two_map f
|}.
Next Obligation. now destruct f. Qed.

(*
 The k-th family: the identity at stage [S k], the constant map at
 [Fin.F1] everywhere else. 

 --------
 第 k 个族：在阶段 [S k] 上的恒等映射，在 [Fin.F1] 上的常值映射，在其他地方。
*)
Definition alpha_fam (k n : nat) : Fin.t 2 -> Fin.t 2 :=
  match Nat.eq_dec n (S k) with
  | left  _ => fun i => i
  | right _ => fun _ => Fin.F1
  end.

Lemma alpha_fam_F1 (k n : nat) : alpha_fam k n Fin.F1 = Fin.F1.
Proof. unfold alpha_fam; destruct (Nat.eq_dec n (S k)); reflexivity. Qed.

(*
 Naturality.  At [le_t_n] the square is an identity; at [le_t_S _]
 both sides reduce to [Fin.F1], because every component of
 [alpha_fam k] preserves [Fin.F1]. 

 --------
 自然性。在 [le_t_n]，平方是恒等；在 [le_t_S _]，双方都化简为 [Fin.F1]，因为 [alpha_fam k] 的每个分量都保持 [Fin.F1]。
*)
Program Definition Alpha@{o h p u u0 u1 u2 +} (k : nat)
  : TwoFun@{o h p u u0 u1 u2} ⟹ TwoFun@{o h p u u0 u1 u2} := {|
  transform := fun n => alpha_fam k n
|}.
Next Obligation.
  destruct f; simpl; [ reflexivity | symmetry; apply alpha_fam_F1 ].
Qed.
Next Obligation.
  destruct f; simpl; [ reflexivity | apply alpha_fam_F1 ].
Qed.

(* The family is injective: [Alpha k] and [Alpha j] already differ at stage [S k], applied to the second element of the two-element set. / 这个族是单射的：[Alpha k] 和 [Alpha j] 在阶段 [S k] 上已经不同，应用于两个元素集合的第二个元素。 *)
Lemma Alpha_distinct (k j : nat) : Alpha k ≈ Alpha j -> k = j.
Proof.
  intro H.
  destruct (Nat.eq_dec k j) as [Hkj | Hkj]; [ exact Hkj | ].
  exfalso.
  specialize (H (S k) (Fin.FS Fin.F1)).
  simpl in H; unfold alpha_fam in H.
  destruct (Nat.eq_dec (S k) (S k)) as [_ | Hne]; [ | now apply Hne ].
  destruct (Nat.eq_dec (S k) (S j)) as [He | _].
  - apply Hkj; now injection He.
  - discriminate H.
Qed.

(*
 In [FinSet] every element of the one-element object is [Fin.F1]
 ([fin1_unique]), so a morphism [1 ~> n] is determined by its value
 there.  The [=] is [fun_setoid]'s pointwise Leibniz equality. 

 --------
 在 [FinSet] 中，一个单元素对象的每个元素都是 [Fin.F1] ([fin1_unique])，因此一个态射 [1 ~> n] 由其在那里的值决定。[=] 是 [fun_setoid] 的逐点 Leibniz 相等。
*)
Lemma finset_point_eq {n : nat}
  (u v : @hom FinSet 1%nat n) : u Fin.F1 = v Fin.F1 -> u ≈ v.
Proof.
  intros H i.
  now rewrite (fin1_unique i).
Qed.

Section MacLaneEx5.

(*
 An ARBITRARY cartesian structure on the functor category, and an
 arbitrary cartesian closed structure over it. 

 --------
 在函子范畴上的任意笛卡尔结构，以及其上的任意笛卡尔闭结构。
*)
Context (CC : @Cartesian ([Omega, FinSet])).
Context (CL : @Closed ([Omega, FinSet]) CC).

(*
 The object of [FinSet] -- a natural number -- at which the engine
 lands: the value at stage 0 of the exponential of [TwoFun] by
 itself. 

 --------
 [FinSet] 的对象——一个自然数——发动机着陆的位置：[TwoFun] 自身指数在第 0 阶段的值。
*)
Definition exp_card : nat :=
  (@exponent_obj _ CC CL TwoFun TwoFun)
    (@initial_obj Omega Omega_Initial).

(* Each [Alpha k] becomes an element of an [exp_card]-element set. / 每个 [Alpha k] 都成为一个 [exp_card] 元素集合的一个元素。 *)
Definition alpha_index (k : nat) : Fin.t exp_card :=
  @fun_hom_point Omega FinSet Omega_Initial FinSet_Terminal CC CL
    TwoFun TwoFun (Alpha k) Fin.F1.

Lemma alpha_index_inj (k j : nat) : alpha_index k = alpha_index j -> k = j.
Proof.
  intro H.
  apply Alpha_distinct.
  apply (@fun_hom_point_inj Omega FinSet Omega_Initial FinSet_Terminal
           CC CL TwoFun TwoFun).
  now apply finset_point_eq.
Qed.

End MacLaneEx5.

(*
 Mac Lane §IV.6 Exercise 5: [FinSet] is cartesian closed, [Omega] is a
 small category, and the functor category is not cartesian closed --
 under ANY cartesian structure on it, not merely the pointwise one. 

 --------
 Mac Lane §IV.6 练习 5：[FinSet] 是笛卡尔闭的，[Omega] 是一个小范畴，并且函子范畴在它上面的任何笛卡尔结构下（不仅仅是逐点的）都不是笛卡尔闭的。
*)
Theorem fun_not_cartesian_closed
  (CC : @Cartesian ([Omega, FinSet])) :
  @Closed ([Omega, FinSet]) CC -> False.
Proof.
  intro CL.
  exact (fin_no_nat_injection (alpha_index CC CL) (alpha_index_inj CC CL)).
Qed.

(*
 The hypothesis of the theorem is not vacuous for want of a cartesian
 structure: the pointwise one exists.  What is refuted is the
 existence of a [Closed] structure over it, or over any other. 

 --------
 该定理的假设并非因为缺乏笛卡尔结构而空洞：逐点结构是存在的。被否定的是其上，或任何其他结构上的 [Closed] 结构的存在。
*)
Corollary fun_pointwise_not_cartesian_closed :
  @Closed ([Omega, FinSet])
    (Functor_Category_Cartesian Omega FinSet FinSet_Cartesian) -> False.
Proof. exact (fun_not_cartesian_closed _). Qed.

(* * ** F: Awodey §8.7 -- the objectwise formula gives the wrong object / * ** F: Awodey §8.7 -- 按对象的公式给出了错误的对象 *)

(*
 Presheaves on the walking arrow.  [_2^op]'s initial object is [TwoY],
 which is [Two_Terminal] read in the opposite category: [Initial C] is
 notation for [@Terminal (C^op)] and [(C^op)^op] is [C], so no
 transport is needed and the constant below typechecks by conversion. 

 --------
 关于行箭头的预层。[_2^op] 的初始对象是 [TwoY]，
 它是在对偶范畴中阅读的 [Two_Terminal]：[Initial C] 是 [@Terminal (C^op)] 的符号，[(C^op)^op] 是 [C]，因此不需要传输，下面的常量通过转换即可类型检查。
*)
Definition TwoOpInitial : @Initial (_2^op) := Two_Terminal.

(*
 [PresheafP] is the representable at [TwoX], built directly.  Its
 value at [TwoX] is the terminal setoid and at [TwoY] the initial
 (empty) one, so that the unique arrow [TwoY ~> TwoX] of [_2^op] acts
 as the empty map. 

 --------
 [PresheafP] 在 [TwoX] 上是可表示的，直接构建。它在 [TwoX] 的值是终端集合，而在 [TwoY] 的值是初始（空）集合，因此 [_2^op] 的唯一箭头 [TwoY ~> TwoX] 充当空映射。
*)
Definition PObj (x : TwoObj) : Sets :=
  match x with
  | TwoX => @terminal_obj Sets Sets_Terminal
  | TwoY => @initial_obj Sets Sets_Initial
  end.

Definition PMap (a b : TwoObj) :
  @hom (_2^op) a b -> (PObj a ~{Sets}~> PObj b).
Proof.
  destruct a, b; intro f.
  - exact id.
  - exact (False_rect _ (TwoHom_Y_X_absurd f)).
  - exact (@zero Sets Sets_Initial _).
  - exact id.
Defined.

(*
 Any two morphisms out of the empty setoid agree, which discharges
 every case of [fmap_comp] that is not an identity. 

 --------
 空等价集合的任意两个态射都相同，这消除了 [fmap_comp] 中不是恒等的每一种情况。
*)
Program Definition PresheafP : _2^op ⟶ Sets := {|
  fobj := PObj;
  fmap := PMap
|}.
Next Obligation. now destruct x. Qed.
Next Obligation.
  destruct x, y, z; simpl;
    solve [ reflexivity | now destruct x0
          | contradiction (TwoHom_Y_X_absurd f)
          | contradiction (TwoHom_Y_X_absurd g) ].
Qed.

(* The two-element setoid, under Leibniz equality on [bool]. / 在 [bool] 上，两个元素的集合，在莱布尼茨等式下。 *)
Definition two_elt : Sets :=
  {| carrier := bool ; is_setoid := eq_Setoid bool |}.

Definition PresheafQ : _2^op ⟶ Sets := Constant_Functor two_elt.

(*
 A transformation [PresheafP ==> PresheafQ] for each boolean: the
 component at [TwoX] picks a point of [two_elt], the component at
 [TwoY] is the unique map out of the empty setoid, and the single
 naturality square is an equation between maps out of that setoid. 

 --------
 对每个布尔值的变换 [PresheafP ==> PresheafQ]：位于 [TwoX] 的分量选择 [two_elt] 的一个点，位于 [TwoY] 的分量是空集合的一种唯一映射，而唯一的自然性方框是一个关于从该集合映射出来的映射的方程。
*)
Program Definition PQNat (b : bool) : PresheafP ⟹ PresheafQ := {|
  transform := fun x =>
    match x return PObj x ~{Sets}~> two_elt with
    | TwoX => {| morphism := fun _ => b
               ; proper_morphism := fun _ _ _ => reflexivity b |}
    | TwoY => @zero Sets Sets_Initial two_elt
    end
|}.
Next Obligation.
  destruct x, y; simpl;
    solve [ reflexivity | now destruct x0
          | contradiction (TwoHom_Y_X_absurd f) ].
Qed.
Next Obligation.
  destruct x, y; simpl;
    solve [ reflexivity | now destruct x0
          | contradiction (TwoHom_Y_X_absurd f) ].
Qed.

Lemma PQNat_distinct : PQNat true ≈ PQNat false -> False.
Proof.
  intro H.
  exact (Bool.diff_true_false (H TwoX ttt)).
Qed.

Section AwodeyPointwise.

Context (CC : @Cartesian ([_2^op, Sets])).
Context (CL : @Closed ([_2^op, Sets]) CC).

(*
 The engine at the presheaf category: two distinct points of
 (Q^P) TwoY. 

 --------
 预层范畴中的引擎：（Q^P）TwoY 的两个不同点。
*)
Definition pq_point (b : bool) :
  @terminal_obj Sets Sets_Terminal
    ~{Sets}~> (@exponent_obj _ CC CL PresheafP PresheafQ) TwoY :=
  @fun_hom_point (_2^op) Sets TwoOpInitial Sets_Terminal CC CL
    PresheafP PresheafQ (PQNat b).

Lemma pq_point_distinct : pq_point true ≈ pq_point false -> False.
Proof.
  intro H.
  apply PQNat_distinct.
  exact (@fun_hom_point_inj (_2^op) Sets TwoOpInitial Sets_Terminal
           CC CL PresheafP PresheafQ (PQNat true) (PQNat false) H).
Qed.

(*
 The objectwise candidate Q(TwoY)^{P(TwoY)}: in [Sets], the
 exponential of the two-element setoid by the empty one.  Any two of
 its points are equivalent, because two of its elements are maps out
 of the empty setoid. 

 --------
 对象候选 Q(TwoY)^{P(TwoY)}：在 [Sets] 中，二元集合的指数由空集合构成。它的任意两点都是等价的，因为它的两个元素是从空集合映射出的映射。
*)
Definition objectwise_candidate : Sets :=
  @exponent_obj Sets Sets_Cartesian Sets_Closed
    (PresheafP TwoY) (PresheafQ TwoY).

Lemma objectwise_candidate_subsingleton
  (u v : @terminal_obj Sets Sets_Terminal ~{Sets}~> objectwise_candidate) :
  u ≈ v.
Proof. intros x; simpl; intros []. Qed.

(*
 Awodey's objectwise formula, refuted at the level of OBJECTS: there
 is no isomorphism in [Sets] between the true value of the
 exponential at [TwoY] and the objectwise candidate.  Since the
 argument uses only that the two objects are isomorphic, no
 contravariant action on the objectwise family can repair it. 

 --------
 Awodey 的逐对象公式，在对象层面被驳斥：在 [Sets] 中，指数在 [TwoY] 处的真实值与逐对象候选之间不存在同构。由于该论证仅使用了两个对象是同构的事实，对逐对象族的逆变作用无法修复它。
*)
Theorem awodey_pointwise_not_exponential :
  @Isomorphism Sets
    ((@exponent_obj _ CC CL PresheafP PresheafQ) TwoY)
    objectwise_candidate -> False.
Proof.
  intro i.
  apply pq_point_distinct.
  apply (@monic Sets _ _ (to i) (iso_to_monic i)).
  apply objectwise_candidate_subsingleton.
Qed.

End AwodeyPointwise.

(** ** G: section F, unconditionally / ** G：F部分，无条件 *)

(*
 Instance/Fun/Exponential.v supplies the hypothesis section F is
 stated over.  Both constants below are the section's theorems applied
 to the pointwise cartesian structure and to that file's cartesian
 closed structure over it; neither re-proves anything, and section F is
 untouched.

 THE UNIVERSE PIN IS [_2]'s, NOT INTRODUCED HERE.  The header records
 that [_2^op, Sets] elaborates only at [Sets@{Set _}], because [_2]'s
 homs are the literal [Set] and [Fun] identifies source and target hom
 universes.  Instance/Fun/Exponential.v's instance is polymorphic
 enough to be instantiated there -- measured: [Psh2_Closed] elaborates
 at [Closed@{u Set u}] with [Set < u] its only strict constraint -- so
 the corollary below is about presheaves valued in setoids whose
 carrier lives in [Set], exactly as section F already was. 

 --------
 Instance/Fun/Exponential.v 提供了假设部分 F 的陈述。下面的两个常量是该部分定理，分别应用于逐点笛卡尔结构以及该文件上的笛卡尔闭结构；都没有重新证明任何内容，并且部分 F 保持不变。宇宙 PIN 是 [_2] 的，而不是在此引入。头文件记录 [_2^op, Sets] 仅在 [Sets@{Set _}] 处展开，因为 [_2] 的 hom 是字面上的 [Set]，并且 [Fun] 标识源和目标 hom 宇宙。Instance/Fun/Exponential.v 的实例是多态的，足以在那里实例化——测量显示：[Psh2_Closed] 在 [Closed@{u Set u}] 处展开，[Set < u] 是它唯一的严格约束——因此下面的推论关于取值于集体的屈代数 presheaf，其承载体位于 [Set] 中，正如 F 节已经讲过的一样。
*)

Definition Psh2_Cart : @Cartesian ([_2^op, Sets]) :=
  @Functor_Category_Cartesian (_2^op) Sets Sets_Cartesian.

Definition Psh2_Closed : @Closed ([_2^op, Sets]) Psh2_Cart :=
  Functor_Category_Closed _2.

(* Two provably distinct points of (Q^P) TwoY, with no hypothesis. / (Q^P) TwoY 的两个可证明不同的点，没有假设。 *)
Definition pq_point_distinct_unconditional :
  pq_point Psh2_Cart Psh2_Closed true
    ≈ pq_point Psh2_Cart Psh2_Closed false -> False
  := pq_point_distinct Psh2_Cart Psh2_Closed.

(*
 Awodey's objectwise no-go, with no hypothesis: the value at [TwoY] of
 the ACTUAL exponential of the presheaf category is not isomorphic to
 the objectwise candidate Q(TwoY)^{P(TwoY)}.  Note that
 [objectwise_candidate] takes no argument -- it mentions neither
 section variable, being built entirely in [Sets] -- so only the left
 side of the comparison moves when the hypothesis is discharged. 

 --------
 Awodey 的逐对象不可行定理，没有假设：预层范畴的实际指数在 [TwoY] 处的值与逐对象候选 Q(TwoY)^{P(TwoY)} 不同构。注意 [objectwise_candidate] 不接受任何参数——它没有提到截面变量——完全在 [Sets] 中构建——因此只有比较的左侧会在假设被解除时发生变化。
*)
Definition awodey_pointwise_not_exponential_unconditional :
  @Isomorphism Sets
    ((@exponent_obj _ Psh2_Cart Psh2_Closed PresheafP PresheafQ) TwoY)
    objectwise_candidate -> False
  := awodey_pointwise_not_exponential Psh2_Cart Psh2_Closed.
