Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.

Generalizable All Variables.

(* * * Contractible pairs, and the coequalizers that are split / * * 可缩对，以及被分裂的等同化子 *)

(*
 Book:   Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 Springer GTM 5, 1998, §VI.6 “Split Coequalizers”, Exercise 2,
 printed p. 150 (PDF p. 159) — maclane:VI.6:ex2; the definitions
 of fork and split fork, printed p. 149 (PDF p. 158)
 nLab:   https://ncatlab.org/nlab/show/split+coequalizer, the section
 “Contractible pairs”

 WHAT THE BOOK SAYS, read from the page images.  On p. 149 a split fork
 is a fork a ⇉ b → c, the pair ∂₀, ∂₁ and the arrow e, “with two more
 arrows” t : b → a and s : c → b satisfying “e∂₀ = e∂₁, es = 1, ∂₀t = 1,
 ∂₁t = se. (3)”.  On p. 150: “By a split coequalizer of ∂₀ and ∂₁ we
 shall mean the arrow e of such a split fork on ∂₀ and ∂₁.  It is
 possible to characterize those parallel pairs ∂₀, ∂₁ for which any
 (and hence every) coequalizer is split (Exercise 2).”  Exercise 2: “A
 parallel pair ∂₀, ∂₁ : a ⇉ b is said to be contractible (Beck) if
 there is an arrow t : b → a with ∂₀t = 1 and ∂₁t∂₀ = ∂₁t∂₁.  (a) In
 any split fork (1), prove ∂₀, ∂₁ contractible; (b) If a contractible
 pair has a coequalizer, prove that this coequalizer is split.”

 WHAT IS HERE.  ∂₀ and ∂₁ are f and g, as in Structure/Coequalizer/
 Split.v, whose [SplitCoequalizer] carries Mac Lane's (3) as its laws 1
 to 4, in his order.
 - [ContractiblePair f g]: a contraction [contr_t] with
 [contr_section], f ∘ t ≈ id, and [contr_cofork],
 g ∘ t ∘ f ≈ g ∘ t ∘ g.  Composition associates to the left, so the
 second equation reads (g ∘ t) ∘ f ≈ (g ∘ t) ∘ g: g ∘ t coforks the
 pair, in the form Structure/Coequalizer.v's [coeq_desc] consumes.
 - (a) [split_coequalizer_contractible]: the pair of every split fork
 is contracted by the fork's own t ([split_coequalizer_contractible_t],
 at [eq_refl]).  The first equation is law 3; the second is nLab's
 chain g t f = s e f = s e g = g t g, by laws 4, 1 and 4.
 - (b) [contractible_coequalizer_split]: a contractible pair with an
 elementary coequalizer [IsCoequalizer f g q e] has a split
 coequalizer on the same object and arrow, its t the contraction
 and its s the descent of g ∘ t through e (all four at [eq_refl]:
 [contractible_coequalizer_split_obj], [_e], [_s], [_t]).  Law 4,
 s e ≈ g t, is the descent's triangle; law 2, e s ≈ 1, follows from
 e s e ≈ e g t ≈ e f t ≈ e because e is epic, by
 Structure/Coequalizer.v's [coequalizer_epic].  This is the argument
 nLab gives.  [contractible_coequalizer_split_s_unique]: given e and
 the contraction, s is the only arrow up to ≈ satisfying law 4, by
 the uniqueness clause of the descent.
 - “Any (and hence every)”: [every_coequalizer_split] reads a
 contraction off one split coequalizer by (a) and feeds it to (b),
 so if a pair has one split coequalizer then EVERY coequalizer of it
 is split, on its own object and arrow and by the given fork's t
 ([every_coequalizer_split_obj], [_e], [_t], at [eq_refl]).
 - The characterization the book announces,
 [split_coequalizer_iff_contractible]: a pair has a split
 coequalizer exactly when it is contractible and has a coequalizer,
 by (a) and Split.v's [split_coequalizer_is_coequalizer], Mac Lane's
 Lemma, one way and by (b) the other.
 - The pair (1, i) of an idempotent i (Theory/Morphisms.v's
 [Idempotent]) is contracted by 1 ([idempotent_contractible]), and
 every coequalizer r of it splits i through r
 ([coequalizer_splits_idempotent], a [SplitIdempotent] whose
 idempotent is i and whose retraction is r, both at [eq_refl]:
 [coequalizer_splits_idempotent_idem], [_r]), its section the s of
 (b).
 - [functor_preserves_contractible]: every functor carries a
 contractible pair to one, contracted by the image of t
 ([functor_preserves_contractible_t], at [eq_refl]).  The
 definition is equational, and the proof goes equation by equation
 through [fmap_comp], [fmap_id] and [fmap_respects], as those of
 Split.v's [functor_preserves_split] and Reflexive.v's
 [functor_preserves_reflexive] do.
 - Structure/Coequalizer/Absolute.v's
 [contractible_coequalizer_absolute]: every coequalizer of a
 contractible pair is absolute, its [split_coequalizer_absolute]
 (#477) applied to (b).  It is stated there, Absolute.v requiring
 this file, so that this file does not load Absolute.v's closure
 (CLOSURE, below).
 The issue asks for the definition, (a) and (b).  The rest is beyond
 it: “any (and hence every)” and the characterization read the book's
 sentence of p. 150; the idempotent pair and the two corollaries are
 not asked for.

 THE CONVERSE DIRECTION, measured in Test/ProbeContractible480.v.
 (b) after (a), at the coequalizer of Mac Lane's Lemma
 ([split_coequalizer_is_coequalizer]), returns the split fork's object,
 e and t at [eq_refl] (C1 to C3) and its s only up to ≈ (C4, from
 [contractible_coequalizer_split_s_unique] and law 4); [eq_refl] is
 refused (R1).  R1 is not opacity: in a scratch file with transparent
 copies of Split.v's [Qed]-closed [split_coeq_desc] and of Mac Lane's
 Lemma, the round trip's s computes to (g ∘ t) ∘ s at [eq_refl], the
 Lemma's descent h ∘ s at h := g ∘ t, which is s only up to ≈, and
 [eq_refl] against s is still refused.  (a) after (b) returns the
 contraction and the proof of the first equation at [eq_refl] (C5,
 C6), but not the proof of the second (R2): (a) rebuilds it from the
 laws of the split fork (b) builds.  Nor is R2 opacity: the normal
 form of the rebuilt proof ([Eval cbv], in a scratch file) names no
 constant but projections of the variables C, P and E, its head
 ([Eval hnf]) the transitivity of C's own hom-setoid, where
 [contr_cofork P] is a projection of the variable P.

 BOUNDARIES.  NOT EVERY PAIR WITH A COEQUALIZER IS CONTRACTIBLE, NOR
 EVERY REFLEXIVE ONE.  Mac Lane's own pair G ×₀ N ⇉ G of p. 150 at Z/4
 over {0, 2} (#479, Instance/Grp/Coequalizer.v) is reflexive by #479's
 [semidirect_reflexive], whose common section [semidirect_refl] is
 x ↦ ⟨x, 0⟩ there, and has the coequalizer p; a contraction would
 split p by (b), and #479's [Z4_two_not_split_in_Grp] refutes that (C16
 to C19 of the probe).  The pair at A₃ ◁ S₃, which #479 splits in Grp,
 is contractible by (a) (C24).
 NOR HAS EVERY CONTRACTIBLE PAIR A COEQUALIZER, NOR IS IT REFLEXIVE.
 In Instance/Presented/Cyclic.v's [IdemCat], Awodey's one-object
 category of an idempotent s ∘ s = s, the pair (1, s) is contracted by 1
 ([idempotent_contractible], C20), and it has no coequalizer: a
 coequalizer e would split s, e ∘ s' ≈ 1 and s' ∘ e ≈ s
 ([coequalizer_splits_idempotent]), and no two of the category's
 arrows, which are 1 and s alone ([idem_exhaust]), form such a pair
 (C21).  The pair (s, s) has a coequalizer there, 1 (C23).  Nor is
 (1, s) reflexive: a common section r would have s ∘ r ≈ 1 (C22).  So
 [ContractiblePair] and Structure/Coequalizer/Reflexive.v's
 [ReflexivePair] are incomparable.  The last two sections of the probe
 alone require #479's module and Cyclic.v.

 STRENGTHS.  At [eq_refl]: the eleven readbacks named above.  At ≈, the
 category's own equality: the two equations of a contraction, the four
 laws of each split coequalizer, the two laws of the split idempotent
 and the uniqueness of s.

 UNIVERSES, read off [About] for every name.  [ContractiblePair], its
 constructor and its three projections are [@{u u0}] over
 C : Category@{u u0 u0}, with no constraint, the record in [Type@{u0}],
 the shape of Reflexive.v's [ReflexivePair].  Every other name but
 three binds C's two levels and nothing else: (a), (b),
 [every_coequalizer_split], [contractible_coequalizer_split_s_unique],
 the idempotent pair's two constants and ten of the eleven readbacks.
 [split_coequalizer_iff_contractible] binds one more level, the sort of
 the biconditional, at or above both of C's: its right side quantifies
 over C's objects and arrows.  [functor_preserves_contractible] and its
 readback bind [@{co ch do dh}] with “ch <= dh” alone, [Functor]'s own
 bound (its block carries h1 <= h2); Split.v's [functor_preserves_split],
 proved by [rewrite], binds one more level, above D's hom level.
 Without the binders D's hom level was identified with C's (measured),
 and C15 accepts ch < dh strict; Reflexive.v's
 [functor_preserves_reflexive], whose bare binders make that
 identification, is among the carriers #1363 tracks.
 The proofs of (a), (b) and [functor_preserves_contractible] use
 [transitivity], [symmetry], [compose_respects], [fmap_respects] and
 the laws of categories and functors, and no [rewrite]: proved by
 [rewrite]s of one side at a time, as in this file's first version,
 (a) and (b) bound a further level strictly above C's hom level and
 the functor corollary one above D's, and so did every name that then
 mentioned them (measured).  A [rewrite] of both sides of an ≈ in one
 step adds caps at the standard library's [prod_rect] besides (#1371).
 On Rocq 9.1.1 no block carries an equation, a [Set] or a
 standard-library universe cap.  On Coq 8.19.2 and 8.20.1 ([About] in
 a source overlay of the changed files' closure with the probe and a
 scratch file, 155 files, under each) every name binds as many levels
 as on Rocq 9.1.1, and the blocks add caps at the standard library's
 [eq.u0], identically on the two versions: none on the record's five
 names, on (a), on [idempotent_contractible] or on
 [functor_preserves_contractible]; on C's hom level in the fourteen
 other names that bind C's two levels alone, and on its object level
 as well in the two [_obj] readbacks; on D's hom level in
 [functor_preserves_contractible_t]; on C's and the target's hom
 levels in Absolute.v's [contractible_coequalizer_absolute], where
 [split_coequalizer_absolute] caps the target's alone; and at [eq],
 [prod] and [sigT] on C's levels and on its own in
 [split_coequalizer_iff_contractible].  No explicit universe instance
 of a new constant is written.

 CLOSURE.  A [Require] of this file loads 25 [Category] modules, this
 one included ([Print Libraries], counting the lines that name a
 [Category] module).  Stated here, the absolute corollary would load
 Absolute.v's closure, 23 modules more; stated in Absolute.v, which
 requires this file, it costs Absolute.v this one module (47 to 48, by
 the same count).  Monad/Monadicity/Beck.v, the consumer named under
 NOT DELIVERED, loads every module this file loads but this one.

 STALE PREMISES, dated from gh.  Issue #480 (filed 2026-07-23) says
 that no contractible-pair definition exists, that “contractible”
 occurs only for terminal-hom and [poly_unit] contractibility and never
 for a parallel pair, and that part (b) has no counterpart.  The
 definition and part (b) were absent until this file: at #479's
 commit, this development's base, no [.v] file names any of the
 twenty-five names it declares (its twenty-four constants and the
 record's constructor), nor does any [.glob] file outside it; and a
 [Search], over the thirteen modules outside Test/ that name both, for
 declarations that take an [IsCoequalizer] and return a
 [SplitCoequalizer] finds only (b) and [every_coequalizer_split].  The
 survey of the word was accurate when filed.  Since PR #1041 (merged
 2026-08-08) it has also been used of groupoids, and later of loop and
 path spaces and of topological spaces; #479's Instance/Grp/
 Coequalizer.v names this exercise among the things it does not
 deliver.  At #479's commit the eleven .v files that use the word
 besides that one (git grep -il contractib) say it of hom-sets, types,
 groupoids and spaces, and none defines a contractible pair.

 NOT DELIVERED.  The characterization through the idempotent g ∘ t (a
 contractible pair has a coequalizer, and then a split one, exactly
 when g ∘ t splits; nLab's second argument), and with it the split
 coequalizer of every contractible pair in a category whose
 idempotents split (Construction/Karoubi/Universal.v's
 [IdempotentsSplit]).  Of it, the pair (1, i) above gives one
 direction at that pair, a coequalizer splitting i; the other, a split
 coequalizer of (1, s ∘ r) from a splitting (r, s) of i, is item 2 of
 #957 (Riehl's split idempotents).  Monad/Monadicity/Beck.v's creation
 of coequalizers is stated for U-split pairs
 ([CreatesUSplitCoequalizers]) and is not restated for contractible
 ones. 

 --------
 书籍：Mac Lane，《为工作数学家准备的范畴》，第2版，Springer GTM 5, 1998，第VI.6节“可分同余子”，练习2，印刷页150（PDF页159）——maclane:VI.6:ex2；叉与可分叉的定义，印刷页149（PDF页158）
 nLab：https://ncatlab.org/nlab/show/split+coequalizer, 章节“可收缩对”书中所述内容，从页面图片中阅读。在第149页，分裂叉是一个叉 a ⇉ b → c，即一对 ∂₀, ∂₁ 和箭头 e，“还有两个箭头” t : b → a 和 s : c → b，满足“e∂₀ = e∂₁, es = 1, ∂₀t = 1, ∂₁t = se。（3）”。在第150页：“我们所说的 ∂₀ 和 ∂₁ 的分裂余等化器，是指这种关于 ∂₀ 和 ∂₁ 的分裂叉中的箭头 e。可以刻画那些平行对 ∂₀, ∂₁，其任何（因此每一个）余等化器都是分裂的（练习2）。” 练习2：“一个平行对 ∂₀, ∂₁ : a ⇉ b 被称为可收缩的（Beck），如果存在箭头 t : b → a，使得 ∂₀t = 1 且 ∂₁t∂₀ = ∂₁t∂₁。（a）在任何分裂叉（1）中，证明 ∂₀, ∂₁ 可收缩；（b）如果一个可收缩对有余等化器，证明该余等化器是分裂的。”这里是什么。∂₀ 和 ∂₁ 分别是 f 和 g，如在 Structure/Coequalizer/Split.v 中，其 [SplitCoequalizer] 拥有 Mac Lane 的 (3) 作为其第 1 到第 4 条定律，按他的顺序。- [ContractiblePair f g]：一个收缩 [contr_t] 与 [contr_section]，f ∘ t ≈ id，以及 [contr_cofork]，g ∘ t ∘ f ≈ g ∘ t ∘ g。组合向左结合，因此第二个方程读作 (g ∘ t) ∘ f ≈ (g ∘ t) ∘ g：g ∘ t 共叉该对，形式如 Structure/Coequalizer.v 中 [coeq_desc] 所使用。- (a) [split_coequalizer_contractible]：每个分叉叉的对都由叉本身的 t ([split_coequalizer_contractible_t]，在 [eq_refl]) 收缩。第一个方程是定律 3；第二个是 nLab 的链 g t f = s e f = s e g = g t g，依靠定律 4、1 和 4。- (b) [contractible_coequalizer_split] ：一个带有初等等化器 [IsCoequalizer f g q e] 的可收缩对在同一对象和箭头上有一个拆分等化器，它的 t 是收缩，而它的 s 是 g ∘ t 通过 e 的下降（四个都在 [eq_refl] ：[contractible_coequalizer_split_obj]、[_e]、[_s]、[_t]）。律 4，s e ≈ g t，是下降的三角形；律 2，e s ≈ 1，来自 e s e ≈ e g t ≈ e f t ≈ e 因为 e 是满射，由 Structure/Coequalizer.v 的 [coequalizer_epic]。这是 nLab 给出的论证。[contractible_coequalizer_split_s_unique] ：给定 e 和收缩，s 是唯一一个满足律 4 的箭头（至 ≈），根据下降的唯一性条款。- “任意（因此是所有）”：[every_coequalizer_split] 从一个分裂的共同等化器读取一个收缩由 (a) 并将其传递给 (b)，因此如果一对有一个分裂的共同等化器，那么它的每一个共同等化器都是分裂的，在它自身的对象和箭头上，并且通过给定叉的 t ([every_coequalizer_split_obj], [_e], [_t], 在 [eq_refl]) 。- 书中宣布的表征，[split_coequalizer_iff_contractible]：一对恰好当它是可收缩的并且有一个共同等化器时，才有分裂共同等化器，通过 (a) 和 Split.v 的 [split_coequalizer_is_coequalizer]，Mac Lane 引理，一种方式，以及通过 (b) 另一种方式。- 幂等元 i 的对 (1, i)（位于 Theory/Morphisms.v 的 [Idempotent]）被 1 收缩（[idempotent_contractible]），并且它的每一个共同等化子 r 都通过 r 分解 i（[coequalizer_splits_idempotent]，一个 [SplitIdempotent]，其幂等元为 i 且重tractions 为 r，均在 [eq_refl]：[coequalizer_splits_idempotent_idem]，[_r]），其在 (b) 中的截面 s。- [functor_preserves_contractible]：每个函子都会将一个可收缩对映射为一个被 t 的像收缩的对（[functor_preserves_contractible_t]，位于 [eq_refl]）。定义是方程形式的，证明通过 [fmap_comp]、[fmap_id] 和 [fmap_respects] 的逐个方程进行，就像 Split.v 中的 [functor_preserves_split] 和 Reflexive.v 中的 [functor_preserves_reflexive] 的证明一样。- Structure/Coequalizer/Absolute.v 的 [contractible_coequalizer_absolute]：每个可收缩对的共同等化子都是绝对的，其 [split_coequalizer_absolute]（#477）应用于 (b)。那里说明了，Absolute.v 需要这个文件，这样这个文件就不会加载 Absolute.v 的闭包（下文的 CLOSURE）。这个问题要求给出定义，（a）和（b）。其余部分超出了要求：“任何（因此每一个）”以及描述请阅读书中第 150 页的句子；幂等对和两个推论不在要求范围内。相反方向，在 Test/ProbeContractible480.v 中测量。(b) 在 (a) 之后，于 Mac Lane 引理的余等化器处 ([split_coequalizer_is_coequalizer])，返回分叉的对象，e 和 t 于 [eq_refl] (从 C1 到 C3)，其 s 仅至 ≈ (C4，从 [contractible_coequalizer_split_s_unique] 和定律 4); [eq_refl] 被拒绝 (R1)。R1 不是不透明性：在含有 Split.v 的 [Qed] 关闭的 [split_coeq_desc] 的透明副本以及 Mac Lane 引理的草稿文件中，往返的 s 计算为 (g ∘ t) ∘ s 于 [eq_refl]，引理的下降 h ∘ s 于 h := g ∘ t，仅至 ≈ 的 s，并且 [eq_refl] 仍然被拒绝 (相对于 s)。(a) 于 (b) 之后返回收缩及第一条方程的证明于 [eq_refl] (C5, C6)，但不包括第二条的证明 (R2)：(a) 从分叉的定律重建它，(b) 构建它。R2 也不是不透明的：重建证明的正常形式（[Eval cbv]，在一个临时文件中）没有命名任何常量，而是对变量 C、P 和 E 的投影，它的头部（[Eval hnf]）是 C 自身的同集合的传递性，其中 [contr_cofork P] 是变量 P 的一个投影。界限。并非每一对具有并行化子的对都是可收缩的，也并非每一对具有自反性的对都是可收缩的。Mac Lane 在第150页的对 G ×₀ N ⇉ G 关于 Z/4 对 {0, 2} (#479, Instance/Grp/Coequalizer.v) 是自反的，由 #479 的 [semidirect_reflexive] 表明，其公共截面 [semidirect_refl] 在那里是 x ↦ ⟨x, 0⟩，并且具有并行化子 p；通过 (b) 一个收缩会分裂 p，而 #479 的 [Z4_two_not_split_in_Grp] 驳斥了这一点（探针的 C16 到 C19）。在 A₃ ◁ S₃ 的那个对，在 #479 的 Grp 中被分裂，根据 (a) 是可收缩的 (C24)。同样，并非每一个可收缩的对都有并行化子，也并非每一个都是自反的。在 Instance/Presented/Cyclic.v 的 [IdemCat] 中，Awodey 的幺对象范畴中有一个幂等元 s ∘ s = s，成对 (1, s) 被 1 收缩 ([idempotent_contractible], C20)，并且它没有共等化子：一个共等化子 e 会分裂 s，即 e ∘ s' ≈ 1 并且 s' ∘ e ≈ s ([coequalizer_splits_idempotent])，而范畴中的任意两条箭头，也就是仅有的 1 和 s ([idem_exhaust])，都无法形成这样的对 (C21)。成对 (s, s) 在那里有一个共等化子，即 1 (C23)。同时，(1, s) 也不是自反的：一个共同的截面 r 会有 s ∘ r ≈ 1 (C22)。因此 [ContractiblePair] 和 Structure/Coequalizer/Reflexive.v 的 [ReflexivePair] 之间是不可比较的。探针的最后两节本身就需要 #479 的模块和 Cyclic.v。优势。在[eq_refl]处：上述十一条回读。在≈处，该类别自身的等式：收缩的两个方程，每个分裂共同等化器的四条规律，分裂幂等的两条规律以及s的唯一性。宇宙，对于每个名称读取 [About]。[ContractiblePair]、它的构造函数及其三个投影是在 C : Category@{u u0 u0} 上的 [@{u u0}]，没有任何约束，在 [Type@{u0}] 中的记录，Reflexive.v 的形状 [ReflexivePair]。除三个绑定 C 的两个层级外，其他每个名称什么也不绑定：(a)、(b)、[every_coequalizer_split]、[contractible_coequalizer_split_s_unique]、幂等对的两个常量以及十个十一的回读。[split_coequalizer_iff_contractible] 再绑定一个层级，即双条件的类型，在 C 的两个层级之上或相等：它的右边对 C 的对象和箭头进行量化。[functor_preserves_contractible] 及其回读绑定 [@{co ch do dh}]，仅带“ch <= dh”，[Functor] 自身的绑定（其块包含 h1 <= h2）；Split.v 的 [functor_preserves_split]，由 [rewrite] 证明，绑定再多一个层级，高于 D 的同伦层级。在没有绑定器的情况下，D 的同质层被识别为与 C 的（已测量）相同，且 C15 接受 ch < dh 严格；Reflexive.v 的 [functor_preserves_reflexive]，其裸绑定器使该识别成立，属于载体 #1363 轨道。 (a)、(b) 和 [functor_preserves_contractible] 的证明使用了 [transitivity]、[symmetry]、[compose_respects]、[fmap_respects] 以及范畴和函子定律，并且没有 [rewrite]：由 [rewrite] 单边逐步证明，就像本文件的第一个版本中那样，(a) 和 (b) 在 C 的同质层之上严格绑定了一个更高层级，而函子推论则在 D 的以上层级绑定了一个层次，每一个随后提到它们的名称（已测量）也是如此。一次在 ≈ 两边同时应用 [rewrite] 会在标准库的 [prod_rect] 之外添加覆盖物（#1371）。在 Rocq 9.1.1 中，没有任何块携带方程、[Set] 或标准库宇宙覆盖物。在 Coq 8.19.2 和 8.20.1（[About] 在更改文件闭包的源覆盖中与探针和临时文件一起，155 个文件，每个文件下）中，每个名称绑定的层数与 Rocq 9.1.1 相同，并且块在标准库的 [eq.u0] 上增加了上限，在两个版本中完全一致：在记录的五个名称上没有，在 (a)、[idempotent_contractible] 或 [functor_preserves_contractible] 上没有；在 C 的同构层上，在十四个只绑定 C 两层的其他名称上，并且在两个 [_obj] 读取回来的对象层上也有；在 [functor_preserves_contractible_t] 上的 D 的同构层；在 Absolute.v 的 [contractible_coequalizer_absolute] 上，C 和目标的同构层，其中 [split_coequalizer_absolute] 仅将目标的层加上上限；在 [eq]、[prod] 和 [sigT] 上增加 C 的层以及在 [split_coequalizer_iff_contractible] 上其自身的层。不会写入新常量的显式宇宙实例。封闭。此文件的 [Require] 加载了 25 个 [Category] 模块，其中包括这个（[Print Libraries]，计算命名 [Category] 模块的行数）。在此说明的话，绝对对应关系将加载 Absolute.v 的封闭，比这多 23 个模块；在 Absolute.v 中说明，它需要此文件，对于 Absolute.v 来说额外增加了这个模块（按同样的计数从 47 到 48）。Monad/Monadicity/Beck.v，在未交付下命名的消费者，加载了此文件加载的每个模块，但不包括这个。过时的前提，来源于 gh. Issue #480（归档于 2026-07-23），指出不存在可收缩对的定义，“可收缩”仅用于终端同态和 [poly_unit] 的可收缩性，从未用于平行对，并且部分 (b) 没有对应项。该定义和部分 (b) 在此文件之前不存在：在 #479 的提交中，即该开发的基础，没有任何 [.v] 文件包含其声明的二十五个名字（其二十四个常量和记录的构造函数），其外部也没有 [.glob] 文件；而 [Search] 在 Test/ 之外的十三个模块中，对声明接受 [IsCoequalizer] 并返回 [SplitCoequalizer] 的内容，只找到了 (b) 和 [every_coequalizer_split]。该词条的调查在提交时是准确的。自从 PR #1041（合并于 2026-08-08）以来，它也被用于群类，后来用于环和道路空间以及拓扑空间；#479 的 Instance/Grp/Coequalizer.v 将这个练习列为它未实现的内容。在 #479 的提交中，除了那个文件外，另外十一份 .v 文件使用了这个词（git grep -il contractib），用于描述同态集、类型、群类和空间，并且没有一个定义了可收缩对。未交付。通过幂等 g ∘ t 的表征（一个可收缩对有一个等化子，然后有一个拆分的等化子，当且仅当 g ∘ t 可拆分；nLab 的第二个论证），以及在其上每个在幂等可拆分的范畴中的可收缩对的拆分等化子（Construction/Karoubi/Universal.v 的 [IdempotentsSplit]）。对于它，上述对 (1, i) 给出该对的一个方向，即一个拆分 i 的等化子；另一个，从 i 的拆分 (r, s) 得到 (1, s ∘ r) 的拆分等化子，是 #957（Riehl 的拆分幂等）的第 2 项。Monad/Monadicity/Beck.v 中等化子的建立是针对 U-拆分对（[CreatesUSplitCoequalizers]）陈述的，而对于可收缩对则未重新陈述。
*)

(** ** The definition / ** 定义 *)

(*
 A contraction t of the pair: a section of f through which g ∘ t
 coforks the pair. 

 --------
 对 (a pair) 的一个收缩 t：f 的一个截面，通过该截面 g ∘ t 对 pair 进行共分叉。
*)
Record ContractiblePair {C : Category} {x y : C} (f g : x ~> y) := {
  contr_t : y ~> x;                                (* the contraction / 收缩 *)

  contr_section : f ∘ contr_t ≈ id;                (* ∂₀ t = 1 *)
  contr_cofork  : g ∘ contr_t ∘ f ≈ g ∘ contr_t ∘ g
                                                   (* ∂₁ t ∂₀ = ∂₁ t ∂₁ *)
}.

Arguments contr_t       {_ _ _ _ _} _.
Arguments contr_section {_ _ _ _ _} _.
Arguments contr_cofork  {_ _ _ _ _} _.

(* * ** (a) The pair of a split fork is contractible / * **（a）分叉对是可收缩的 *)

(*
 t is the split fork's t: law 3 is ∂₀ t = 1, and g t f = s e f = s e g
 = g t g by laws 4, 1 and 4. 

 --------
 t 是分叉叉的 t：定律 3 是 ∂₀ t = 1，并且 g t f = s e f = s e g = g t g 根据定律 4、1 和 4。
*)
Definition split_coequalizer_contractible {C : Category} {x y : C}
  {f g : x ~> y} (S : SplitCoequalizer f g) : ContractiblePair f g.
Proof.
  unshelve refine {| contr_t := scoeq_t S; contr_section := scoeq_law3 S |}.
  transitivity (scoeq_s S ∘ scoeq_e S ∘ f).
  { (* law 4 *)
    refine (compose_respects _ _ (scoeq_law4 S) _ _ _).
    reflexivity. }
  transitivity (scoeq_s S ∘ scoeq_e S ∘ g).
  { (* law 1, under s / 法律 1，根据第 s 条 *)
    transitivity (scoeq_s S ∘ (scoeq_e S ∘ f)).
    { symmetry.
      apply comp_assoc. }
    transitivity (scoeq_s S ∘ (scoeq_e S ∘ g)).
    { refine (compose_respects _ _ _ _ _ (scoeq_law1 S)).
      reflexivity. }
    apply comp_assoc. }
  (* law 4 *)
  refine (compose_respects _ _ _ _ _ _).
  - symmetry.
    exact (scoeq_law4 S).
  - reflexivity.
Defined.

Example split_coequalizer_contractible_t {C : Category} {x y : C}
  {f g : x ~> y} (S : SplitCoequalizer f g) :
  contr_t (split_coequalizer_contractible S) = scoeq_t S := eq_refl.

(* * ** (b) A coequalizer of a contractible pair is split / * ** (b) 可缩对的余等化子是分裂的 *)

(*
 On the same object and arrow: s is the descent of g ∘ t through e,
 which the second equation makes possible; then s e = g t is law 4, and
 e s e = e g t = e f t = e gives law 2, e being epic. 

 --------
 在同一个对象和箭头上：s 是 g ∘ t 通过 e 的下降，第二个方程使之成为可能；然后 s e = g t 是定律 4，而 e s e = e g t = e f t = e 给出定律 2，e 是满射。
*)
Definition contractible_coequalizer_split {C : Category} {x y : C}
  {f g : x ~> y} (P : ContractiblePair f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) : SplitCoequalizer f g.
Proof.
  unshelve refine
    {| scoeq_obj := q
     ; scoeq_e   := e
     ; scoeq_s   := unique_obj (coeq_desc E (g ∘ contr_t P) (contr_cofork P))
     ; scoeq_t   := contr_t P |}.
  - (* law 1 *)
    exact (cofork E).
  - (* law 2: (e ∘ s) ∘ e ≈ id ∘ e, then e is epic / 定律 2：(e ∘ s) ∘ e ≈ id ∘ e，则 e 是满射 *)
    apply (@epic _ _ _ e (coequalizer_epic f g E)).
    transitivity
      (e ∘ (unique_obj (coeq_desc E (g ∘ contr_t P) (contr_cofork P)) ∘ e)).
    { symmetry.
      apply comp_assoc. }
    transitivity (e ∘ (g ∘ contr_t P)).
    { refine (compose_respects _ _ _ _ _
                (unique_property
                   (coeq_desc E (g ∘ contr_t P) (contr_cofork P)))).
      reflexivity. }
    transitivity (e ∘ g ∘ contr_t P).
    { apply comp_assoc. }
    transitivity (e ∘ f ∘ contr_t P).
    { refine (compose_respects _ _ _ _ _ _).
      - symmetry.
        exact (cofork E).
      - reflexivity. }
    transitivity (e ∘ (f ∘ contr_t P)).
    { symmetry.
      apply comp_assoc. }
    transitivity (e ∘ id).
    { refine (compose_respects _ _ _ _ _ (contr_section P)).
      reflexivity. }
    transitivity e.
    { apply id_right. }
    symmetry.
    apply id_left.
  - (* law 3 *)
    exact (contr_section P).
  - (* law 4 *)
    symmetry.
    exact (unique_property (coeq_desc E (g ∘ contr_t P) (contr_cofork P))).
Defined.

Example contractible_coequalizer_split_obj {C : Category} {x y : C}
  {f g : x ~> y} (P : ContractiblePair f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  scoeq_obj (contractible_coequalizer_split P E) = q := eq_refl.

Example contractible_coequalizer_split_e {C : Category} {x y : C}
  {f g : x ~> y} (P : ContractiblePair f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  scoeq_e (contractible_coequalizer_split P E) = e := eq_refl.

Example contractible_coequalizer_split_s {C : Category} {x y : C}
  {f g : x ~> y} (P : ContractiblePair f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  scoeq_s (contractible_coequalizer_split P E)
    = unique_obj (coeq_desc E (g ∘ contr_t P) (contr_cofork P)) := eq_refl.

Example contractible_coequalizer_split_t {C : Category} {x y : C}
  {f g : x ~> y} (P : ContractiblePair f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  scoeq_t (contractible_coequalizer_split P E) = contr_t P := eq_refl.

(*
 Given the coequalizer and the contraction, s is unique up to ≈: any s'
 satisfying law 4 is the descent of g ∘ t. 

 --------
 给定余等化子和收缩，s 在 ≈ 下是唯一的：任何满足定律4的 s' 都是 g ∘ t 的下降。
*)
Lemma contractible_coequalizer_split_s_unique {C : Category} {x y : C}
  {f g : x ~> y} (P : ContractiblePair f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) (s : q ~> y) (Hs : g ∘ contr_t P ≈ s ∘ e) :
  scoeq_s (contractible_coequalizer_split P E) ≈ s.
Proof.
  exact (uniqueness (coeq_desc E (g ∘ contr_t P) (contr_cofork P)) s
           (symmetry Hs)).
Qed.

(* * ** “Any (and hence every) coequalizer is split” / * ** “任何（因此每一个）等同化都是可分的” *)

Definition every_coequalizer_split {C : Category} {x y : C}
  {f g : x ~> y} (S : SplitCoequalizer f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) : SplitCoequalizer f g :=
  contractible_coequalizer_split (split_coequalizer_contractible S) E.

Example every_coequalizer_split_obj {C : Category} {x y : C}
  {f g : x ~> y} (S : SplitCoequalizer f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  scoeq_obj (every_coequalizer_split S E) = q := eq_refl.

Example every_coequalizer_split_e {C : Category} {x y : C}
  {f g : x ~> y} (S : SplitCoequalizer f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  scoeq_e (every_coequalizer_split S E) = e := eq_refl.

(* Every coequalizer of the pair is split by the same t. / 该对的每个余等化子都被同一个 t 拆分。 *)
Example every_coequalizer_split_t {C : Category} {x y : C}
  {f g : x ~> y} (S : SplitCoequalizer f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  scoeq_t (every_coequalizer_split S E) = scoeq_t S := eq_refl.

(** ** The characterization / ** 人物刻画 *)

(*
 A pair has a split coequalizer exactly when it is contractible and has
 a coequalizer: (a) and Mac Lane's Lemma one way, (b) the other. 

 --------
 当且仅当一个对是可收缩的并且有一个共同余核时，它才有分裂共同余核：（a）Mac Lane的引理在一边，（b）另一边。
*)
Definition split_coequalizer_iff_contractible {C : Category} {x y : C}
  (f g : x ~> y) :
  SplitCoequalizer f g ↔
  (ContractiblePair f g ∧ ∃ (q : C) (e : y ~> q), IsCoequalizer f g q e).
Proof.
  split.
  - intros S.
    split.
    + exact (split_coequalizer_contractible S).
    + exists (scoeq_obj S), (scoeq_e S).
      exact (split_coequalizer_is_coequalizer f g S).
  - intros [P [q [e E]]].
    exact (contractible_coequalizer_split P E).
Defined.

(* * ** The pair (1, i) of an idempotent / * ** 幂等元的对 (1, i) *)

(*
 Contracted by 1: the second equation is i ∘ 1 ∘ 1 ≈ i ∘ 1 ∘ i, both
 sides being i up to ≈, the right one by idempotence. 

 --------
 通过 1 收缩：第二个方程是 i ∘ 1 ∘ 1 ≈ i ∘ 1 ∘ i，双方在 ≈ 下都是 i，右边是通过幂等性得到的。
*)
Definition idempotent_contractible {C : Category} {x : C} (i : x ~> x)
  (I : Idempotent i) : ContractiblePair id i.
Proof.
  unshelve refine {| contr_t := id; contr_section := id_left id |}.
  transitivity i.
  - transitivity (i ∘ id).
    + apply id_right.
    + apply id_right.
  - transitivity (i ∘ i).
    + symmetry.
      exact idem.
    + refine (compose_respects _ _ _ _ _ _).
      * symmetry.
        apply id_right.
      * reflexivity.
Defined.

(*
 A coequalizer r of (1, i) splits i through r: s ∘ r ≈ i is law 4 of
 (b), i ∘ 1 ≈ s ∘ r, and r ∘ s ≈ 1 is its law 2. 

 --------
 (1, i) 的一个共同余等化子 r 通过 r 拆分 i：s ∘ r ≈ i 是 (b) 的法则 4，i ∘ 1 ≈ s ∘ r，且 r ∘ s ≈ 1 是它的法则 2。
*)
Definition coequalizer_splits_idempotent {C : Category} {x : C}
  (i : x ~> x) (I : Idempotent i) {q : C} {r : x ~> q}
  (E : IsCoequalizer id i q r) : @SplitIdempotent C x q.
Proof.
  unshelve refine
    {| split_idem   := i
     ; split_idem_r := r
     ; split_idem_s := scoeq_s (contractible_coequalizer_split
                                  (idempotent_contractible i I) E) |}.
  - (* s ∘ r ≈ i *)
    symmetry.
    transitivity (i ∘ id).
    + symmetry.
      apply id_right.
    + exact (scoeq_law4 (contractible_coequalizer_split
                           (idempotent_contractible i I) E)).
  - (* r ∘ s ≈ 1 *)
    exact (scoeq_law2 (contractible_coequalizer_split
                         (idempotent_contractible i I) E)).
Defined.

Example coequalizer_splits_idempotent_idem {C : Category} {x : C}
  (i : x ~> x) (I : Idempotent i) {q : C} {r : x ~> q}
  (E : IsCoequalizer id i q r) :
  @split_idem C x q (coequalizer_splits_idempotent i I E) = i := eq_refl.

Example coequalizer_splits_idempotent_r {C : Category} {x : C}
  (i : x ~> x) (I : Idempotent i) {q : C} {r : x ~> q}
  (E : IsCoequalizer id i q r) :
  @split_idem_r C x q (coequalizer_splits_idempotent i I E) = r := eq_refl.

(* * ** Functors preserve contractible pairs / * **函子保持可约对 *)

Theorem functor_preserves_contractible@{co ch do dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D)
  {x y : C} (f g : x ~> y) :
  ContractiblePair f g → ContractiblePair (fmap[F] f) (fmap[F] g).
Proof.
  intros P.
  unshelve refine {| contr_t := fmap[F] (contr_t P) |}.
  - (* F f ∘ F t ≈ F (f ∘ t) ≈ F id ≈ id / F f ∘ F t ≈ F (f ∘ t) ≈ F id ≈ id *)
    transitivity (fmap[F] (f ∘ contr_t P)).
    + symmetry.
      apply fmap_comp.
    + transitivity (fmap[F] (@id C y)).
      * apply fmap_respects.
        exact (contr_section P).
      * apply fmap_id.
  - (* F g ∘ F t ∘ F f ≈ F (g ∘ t ∘ f) ≈ F (g ∘ t ∘ g) ≈ F g ∘ F t ∘ F g / F g ∘ F t ∘ F f ≈ F (g ∘ t ∘ f) ≈ F (g ∘ t ∘ g) ≈ F g ∘ F t ∘ F g *)
    transitivity (fmap[F] (g ∘ contr_t P ∘ f)).
    { transitivity (fmap[F] (g ∘ contr_t P) ∘ fmap[F] f).
      - refine (compose_respects _ _ _ _ _ _).
        + symmetry.
          apply fmap_comp.
        + reflexivity.
      - symmetry.
        apply fmap_comp. }
    transitivity (fmap[F] (g ∘ contr_t P ∘ g)).
    { apply fmap_respects.
      exact (contr_cofork P). }
    transitivity (fmap[F] (g ∘ contr_t P) ∘ fmap[F] g).
    { apply fmap_comp. }
    refine (compose_respects _ _ _ _ _ _).
    + apply fmap_comp.
    + reflexivity.
Defined.

Example functor_preserves_contractible_t@{co ch do dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D)
  {x y : C} {f g : x ~> y} (P : ContractiblePair f g) :
  contr_t (functor_preserves_contractible F f g P) = fmap[F] (contr_t P)
  := eq_refl.
