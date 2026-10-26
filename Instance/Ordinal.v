Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Omega.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Eqdep_dec.

Generalizable All Variables.

(* * * The finite ordinals as categories / * * 有限序数作为范畴 *)

(*
 nLab:      https://ncatlab.org/nlab/show/thin+category
 nLab:      https://ncatlab.org/nlab/show/simplex+category
 nLab:      https://ncatlab.org/nlab/show/interval+category
 Wikipedia: https://en.wikipedia.org/wiki/Posetal_category
 Book:      Mac Lane, Categories for the Working Mathematician, 2nd ed.,
 §I.2 (the roster of small examples, printed p. 11)
 Book:      Fong and Spivak, Seven Sketches in Compositionality, §3.2.1
 Book:      Riehl, Category Theory in Context, §1.6

 Every finite ordinal is a category.  The ordinal with n elements,
 {0 < 1 < ... < n-1}, has those elements as objects and exactly one
 arrow i ~> j whenever i ≤ j; identities are reflexivity and
 composition is transitivity.  Mac Lane lists these among the first
 examples of categories in CWM §I.2, and the pattern is the one
 Instance/Proset.v states in general: any preorder is a category, and
 the resulting category is THIN, meaning any two parallel arrows
 coincide.  This file supplies the whole family at once, uniformly in
 n, together with the structure that makes the family useful as a
 supply of diagram shapes.

 The three smallest members already existed in the tree as bespoke
 constructions — Instance/Zero.v's [_0] (objects [Empty_set]),
 Instance/One.v's [_1] (the single object [ttt] of [poly_unit]), and
 Instance/Two.v's [_2] (the inductives [TwoObj] and [TwoHom], the
 walking arrow) — and the family stops there.  It resumes past the
 finite stages in Instance/Omega.v's [Omega], the ordinal ω on all of
 [nat].  This file builds the general [Ordinal n] and reconnects it to
 all four: [Ordinal 0 ≅ _0], [Ordinal 1 ≅ _1], [Ordinal 2 ≅ _2] in
 [Cat], and an embedding [Ordinal n ⟶ Omega] exhibiting each finite
 stage inside ω.  (That ω is the colimit of the finite stages is true
 and standard, but it is not proven here — Construction/Chain.v's
 chains are the nearest in-tree machinery, and they are the
 initial-algebra chain over a functor rather than general ω-colimit
 apparatus.)

 NAMING, stated loudly because the sources differ.  [Ordinal n] has n
 OBJECTS.  So [Ordinal 0] is empty, [Ordinal 1] is the point,
 [Ordinal 2] is the walking arrow, [Ordinal 3] (exported as [_3])
 has three objects and two generating steps, and [Ordinal 4]
 (exported as [_4]) has four objects and three generating steps.
 This is the convention already fixed by the names [_0], [_1], [_2].
 When a text speaks of “diagrams of shape 4” — as Riehl §1.6 does, in
 the passage issue #224 cites — it means the ordinal on four objects,
 which is [_4] here, and which is free on THREE composable arrows.
 No bracket notation [n] is introduced: [[C, D]] is already the
 functor category (Instance/Fun.v).

 THE CARRIER.  An object of [Ordinal n] is a natural number together
 with a proof that it is smaller than n — von Neumann's reading of an
 ordinal as the set of its predecessors, which is exactly what the
 embedding [Ord_Incl : Ordinal n ⟶ Ordinal (S n)] expresses.  The
 standard alternative is the stdlib's [Fin.t n], which
 Instance/FinSet.v uses as the n-element set its objects denote; the
 two carriers are the same up to a bijection, and that bijection is
 proven below ([ord_of_fin], [fin_of_ord] and both round trips).  The
 record is taken as primary for a computational reason:
 [ord_val (ord_incl x)] reduces to [ord_val x] on a variable [x],
 whereas a weakening [Fin.t n → Fin.t (S n)] has to recurse on the
 constructor and so leaves the numeric value stuck on a variable.
 That single reduction is what lets the embedding functors act as the
 IDENTITY on morphisms, and what lets the universal property below be
 STATED without transporting morphisms along equalities of objects.
 (The statements are transport-free; some proofs behind the
 every-functor-comes-from-a-path half do rewrite along object
 equalities internally -- [ord_clamp_step] and [ord_functor_iso] --
 and that is disclosed where they occur.)

 THE ORDER is Instance/Omega.v's [le_t], applied to the underlying
 values, and not the standard library's [le].  The reasons are the
 ones that file's header records: [le] is [Prop]-valued and so cannot
 eliminate into the [Type]-valued hom-sets of an arbitrary target
 category, and staying off the stdlib keeps lemma names portable
 across Coq 8.19/8.20 and Rocq 9.1.  Reusing [le_t] verbatim, rather
 than re-deriving an order on the carrier, is what makes
 [Ord_Omega : Ordinal n ⟶ Omega] the identity on morphisms.  It also
 rules out Instance/Proset.v as the donor: [Proset] is parameterized
 by a [PreOrder R] over a [relation A], hence by a [Prop]-valued
 order.

 THINNESS is proven, not assumed.  [le_t m n] has at most one
 inhabitant ([le_t_irr] below, axiom-free: it uses only UIP on [nat],
 which [Eqdep_dec] derives from decidable equality).  The hom-setoid
 is therefore strict equality, [Morphism_equality], exactly as in
 [_0], [_1], [_2] and [Omega] — and NOT the always-true setoid
 [fun _ _ => True] that Instance/Proset.v installs for a general
 preorder.  The distinction earns its keep twice over.  Coherence
 obligations become one-liners, since any equation between parallel
 arrows of [Ordinal n] is closed by [le_t_irr].  And the count of
 morphisms below is a statement about the arrows themselves rather
 than about ≈-classes: under Proset's trivial hom-setoid every
 hom-set is a single class whatever its underlying type, so counting
 there would say nothing.

 WHAT IS PROVEN.  (1) the family [Ordinal n] and its thinness;
 (2) [Ordinal 0 ≅ _0], [Ordinal 1 ≅ _1], [Ordinal 2 ≅ _2] in [Cat],
 with [_3] and [_4] exported; (3) the embeddings
 [Ord_Incl : Ordinal n ⟶ Ordinal (S n)] and
 [Ord_Omega : Ordinal n ⟶ Omega], both full and faithful, commuting
 in the evident triangle; (4) a morphism count — the arrows of
 [Ordinal n] are in bijection with their pairs of endpoint indices,
 those pairs are enumerated by a duplicate-free list, and its length
 t satisfies [2 * t = n * (n + 1)], proven by induction on n rather
 than checked case by case (the exercise issue #224 cites from
 Fong and Spivak, Seven Sketches, §3.2.1); (5) the universal property
 making [Ordinal (S n)] the free category on the linear quiver with n
 edges (Riehl §1.6), stated directly at the level of [Cat]; (6) its
 specialization to shape 4.

 UNIVERSES.  The explicit annotations on [Ord_obj] and [Ordinal] are
 there because, left to inference, Coq collapses the three parameters
 of [Category] into one and the family is issued as [Ordinal@{u}]
 (measured, not asserted -- an unannotated copy elaborates at
 [Category@{u Set Set}]).  Instance/Omega.v annotates [Omega@{o h p}]
 for its own, different reason, recorded in its header: under the
 library-wide [Set Universe Polymorphism] a strictly-bound family must
 instantiate every polymorphic constant it mentions.  Unannotated,
 [Ordinal@{u}] would still
 serves as a diagram shape but is strictly less general than the
 [_1@{o h p}] and [Omega@{o h p}] it is meant to sit beside.  With
 them the family is [Ordinal@{o h p}], and it is usable as a shape
 over targets of any size, [Cat] included.

 ON THE STRENGTH OF (5).  The tree DOES carry free-category
 machinery -- Construction/Free/Quiver.v has [FreeOnQuiver] with its
 universal arrow ([UniversalArrowQuiverCat]) and the free/forgetful
 adjunction ([FreeForgetfulAdjunction]), and Construction/Free.v has the
 path category -- but that universal property lives in [StrictCat] under
 [Functor_StrictEq_Setoid], on-the-nose equality of functors.  The
 property proved HERE is the [Cat]-level one, up to [Functor_Setoid],
 which the StrictCat development does not provide; the literal
 identification [FreeOnQuiver (linear quiver) ≅ Ordinal (S n)] in
 StrictCat is a further theorem, still not delivered in THIS file, but
 it is no longer open: it is [ordinal_free] in
 Construction/Free/Quiver/Examples.v, which proves
 [FreeOnQuiver (LinQuiver m) ≅[StrictCat] Ordinal m] for every m, the
 empty ordinal included.  That statement is pinned to
 [Category@{Set Set Set}] -- the free side's universes are forced there
 by [Build_Quiver_Standard_Eq] (Construction/Free/Quiver.v), whose
 result type is [Quiver@{u u0 Set}] -- whereas [Ordinal@{o h p}] here
 stays polymorphic, so the identification does not narrow this family.
 Over a fixed
 assignment of objects [X : nat → C], a “path of n composable arrows”
 is an [OrdSteps n X], and the functorial actions on morphisms over
 the same [X] are the [OrdArrows n X] satisfying the two functor laws.
 [arrows_of_steps] and [steps_of_arrows] are mutually inverse up to
 pointwise ≈ ([steps_arrows_steps], [arrows_steps_arrows]); this is
 the free property at the level of raw actions, and it is
 transport-free; it is a self-contained reading, and the functor-level
 results below are proved directly rather than through it.
 [Functor_of_Steps] turns a path into a functor
 [Ordinal (S n) ⟶ C] whose action on the generating steps is the path
 ([Functor_of_Steps_step]); [Functor_of_Steps_of_Functor] shows every
 functor out of [Ordinal (S n)] is [Functor_Setoid]-equivalent to one
 so obtained; and [ord_functor_equiv_from_steps] gives the uniqueness
 half in its usable form — a family of isomorphisms that is natural on
 the n generating steps is natural on every morphism.  What is NOT
 claimed is a bijection between functors and paths on the nose: the
 object part of a path is a function on all of [nat], so paths
 agreeing below n but differing above it induce the same functor.  The
 equivalence [Functor_of_Steps_of_Functor] is up to [Functor_Setoid],
 the library's natural-isomorphism equality of functors. 

 --------
 nLab：       https://ncatlab.org/nlab/show/thin+category
 nLab：       https://ncatlab.org/nlab/show/simplex+category
 nLab：       https://ncatlab.org/nlab/show/interval+category
 Wikipedia：  https://en.wikipedia.org/wiki/Posetal_category
 书籍：      Mac Lane, 《为工作数学家准备的范畴论》，第二版，§I.2（小例子名录，印刷在第11页）
 书籍：      Fong 和 Spivak，《组合性中的七个素描》，§3.2.1
 书籍：      Riehl，《语境中的范畴论》，§1.6每个有限序数都是一个范畴。具有 n 个元素的序数 {0 < 1 < ... < n-1}，以这些元素为对象，当 i ≤ j 时恰好有一个箭头 i ~> j；恒等映射是自反性，复合是传递性。Mac Lane 在《Categories for the Working Mathematician》第 I.2 节中将这些列为范畴的首批例子，这一模式就是 Instance/Proset.v 中一般说明的：任意预序是一个范畴，并且由此得到的范畴是稀薄的（THIN），也就是说任意两条平行箭头是相同的。该文件一次性提供了整个家族，并且在 n 上是统一的，同时提供了使该家族作为图形结构来源有用的结构。三个最小的成员已经以定制构造的形式存在于树中——Instance/Zero.v 的 [_0]（对象 [Empty_set]），Instance/One.v 的 [_1]（[poly_unit] 的单个对象 [ttt]），以及 Instance/Two.v 的 [_2]（归纳对象 [TwoObj] 和 [TwoHom]，行走箭头）——家族到此为止。它在有限阶段之后在 Instance/Omega.v 的 [Omega] 中恢复，[nat] 上的序数 ω。此文件构建了通用的 [Ordinal n] 并将其重新连接到所有四个：[Ordinal 0 ≅ _0]、[Ordinal 1 ≅ _1]、[Cat] 中的 [Ordinal 2 ≅ _2]，以及展示 ω 内每个有限阶段的嵌入 [Ordinal n ⟶ Omega]。（那个 ω 是有限阶段的余极限这一点是正确且标准的，但在这里没有证明——Construction/Chain.v 的链是最接近的树内机制，它们是关于一个函子而非一般 ω-余极限装置的初代代数链。）命名，大声说明，因为来源不同。   [Ordinal n] 有 n 个对象。 所以 [Ordinal 0] 是空的，[Ordinal 1] 是点，[Ordinal 2] 是行走箭头，[Ordinal 3]（导出为 [_3]）有三个对象和两个生成步骤，而 [Ordinal 4]（导出为 [_4]）有四个对象和三个生成步骤。这是由名称 [_0]、[_1]、[_2] 已经确定的约定。当文本提到“形状 4 的图表”——如 Riehl §1.6 所做的，在问题 #224 引用的段落中——它意味着四个对象上的序数，这里是 [_4]，并且它在三个可组合箭头上自由。未引入括号符号 [n]：[[C, D]] 已经是函子范畴（Instance/Fun.v）。载体。[Ordinal n] 的一个对象是一个自然数，同时附带一个证明它小于 n——冯·诺依曼对序数的理解，即其前驱的集合，这正是嵌入 [Ord_Incl : Ordinal n ⟶ Ordinal (S n)] 所表达的意思。标准的替代方法是 stdlib 的 [Fin.t n]，Instance/FinSet.v 使用它来表示 n 元集合的对象；这两个载体在双射下是相同的，并且这个双射在下面被证明（[ord_of_fin]、[fin_of_ord] 以及两个往返）。由于计算原因，该记录被视为主要形式：[ord_val (ord_incl x)] 在变量 [x] 上简化为 [ord_val x]，而弱化 [Fin.t n → Fin.t (S n)] 不得不在构造子上递归，因此会使数值停留在变量上。那一次简化正是使得嵌入函子可以在态射上作为恒等作用的原因，也使得下面的泛性质可以在不沿对象的相等性传输态射的情况下被陈述。（这些陈述是无需传输的；在每个函子都来自路径的部分背后的某些证明中，确实在内部沿对象相等性进行重写——[ord_clamp_step] 和 [ord_functor_iso]——并且在出现的地方会有说明。）该顺序是 Instance/Omega.v 的 [le_t]，应用于底层值，而不是标准库的 [le]。原因在于该文件的头部记录：[le] 是 [Prop] 值的，因此无法简化为任意目标范畴的 [Type] 值的同态集，并且不使用标准库可以让引理名称在 Coq 8.19/8.20 和 Rocq 9.1 中可移植。逐字重复使用 [le_t]，而不是在承载对象上重新导出顺序，是使 [Ord_Omega : Ordinal n ⟶ Omega] 在态射上是恒等映射的原因。它还排除了 Instance/Proset.v 作为捐赠者：[Proset] 由 [relation A] 上的 [PreOrder R] 参数化，因此由 [Prop] 值的顺序参数化。稀薄性是被证明的，而非假设的。[le_t m n] 至多只有一个居民（见下文 [le_t_irr]，无公理：它只在 [nat] 上使用 UIP，而 [Eqdep_dec] 从可判定的相等性中推导出）。因此，同态集同构是严格相等，[Morphism_equality]，正如在 [_0]、[_1]、[_2] 和 [Omega] 中一样——而不是 Instance/Proset.v 对一般预序安装的始终为真的同态集 [fun _ _ => True]。这个区别的重要性不止一次体现。相干性义务变成了一行代码，因为 [Ordinal n] 的平行箭头之间的任何方程都由 [le_t_irr] 完成。下面的态射计数是关于箭头本身的陈述，而不是关于 ≈ 类的：在 Proset 的平凡同态集中，每个同态集无论其基础类型如何都是单一类，因此在那里计数不会有任何意义。什么是已证明的。(1) 家族 [Ordinal n] 及其稀疏性；(2) [Ordinal 0 ≅ _0]、[Ordinal 1 ≅ _1]、[Ordinal 2 ≅ _2] 在 [Cat] 中，以及 [_3] 和 [_4] 被导出；(3) 嵌入 [Ord_Incl : Ordinal n ⟶ Ordinal (S n)] 和 [Ord_Omega : Ordinal n ⟶ Omega]，均为完全且忠实的，在明显的三角形中可交换；(4) 一个态射计数——[Ordinal n] 的箭头与它们的端点指标对一一对应，这些指标对由不重复的列表列举，并且其长度 t 满足 [2 * t = n * (n + 1)]，通过对 n 进行归纳证明，而不是逐个情况检查（练习问题 #224 引自 Fong 和 Spivak，《七个草图》，§3.2.1）；(5) 使 [Ordinal (S n)] 成为具有 n 条边的线性拟阵的自由范畴的泛性质（Riehl §1.6），直接在 [Cat] 水平陈述；(6) 它对形状 4 的特化。宇宙。对 [Ord_obj] 和 [Ordinal] 的显式注释存在，是因为如果依赖推断，Coq 会将 [Category] 的三个参数合并成一个，并将该族发布为 [Ordinal@{u}]（测量过的，而非断言 —— 一个未注释的副本会在 [Category@{u Set Set}] 处展开）。Instance/Omega.v 出于其自身不同的原因对 [Omega@{o h p}] 进行了注释，该原因记录在其头部：在整个库范围内的 [Set Universe Polymorphism] 下，一个严格绑定的族必须实例化它提到的每一个多态常量。如果未注释，[Ordinal@{u}] 仍然可以作为图形形状，但比它要配合的 [_1@{o h p}] 和 [Omega@{o h p}] 严格而言不够通用。与它们一起，该族变为 [Ordinal@{o h p}]，并且可以作为任意大小目标的形状使用，包括 [Cat]。根据（5）的力量。该树确实包含自由范畴的机制——Construction/Free/Quiver.v 拥有 [FreeOnQuiver] 及其通用箭头（[UniversalArrowQuiverCat]）和自由/忘记伴随（[FreeForgetfulAdjunction]），而 Construction/Free.v 拥有路径范畴——但是该通用性质存在于 [StrictCat] 下的 [Functor_StrictEq_Setoid]，函子完全相等。这里证明的性质是 [Cat] 级别的，至 [Functor_Setoid] 为止，而 StrictCat 开发并未提供；在 StrictCat 中的字面识别 [FreeOnQuiver (linear quiver) ≅ Ordinal (S n)] 是另一条定理，在此文件中仍未提供，但它不再是开放的：它是 Construction/Free/Quiver/Examples.v 中的 [ordinal_free]，它证明了对于每个 m，包括空序数，[FreeOnQuiver (LinQuiver m) ≅[StrictCat] Ordinal m]。该声明固定在
 [Category@{Set Set Set}] —— 自由侧的宇宙被 [Build_Quiver_Standard_Eq]（Construction/Free/Quiver.v）强制在那里，
 其结果类型是 [Quiver@{u u0 Set}] —— 而这里的 [Ordinal@{o h p}] 保持多态，因此该识别不会缩小此族。在固定对象分配 [X : nat → C] 的情况下，
 “n 个可组合箭头的路径” 是 [OrdSteps n X]，并且在相同的 [X] 上对态射的函子作用是满足两个函子律的 [OrdArrows n X]。[arrows_of_steps] 和 [steps_of_arrows] 在点态 ≈（[steps_arrows_steps]，[arrows_steps_arrows]）下互为逆；这是原始作用层面的自由属性，并且它是无需传输的；它是一个自包含的读法，下面的函子级结果是直接证明的，而不是通过它证明的。[Functor_of_Steps] 将一条路径变为函子
 [Ordinal (S n) ⟶ C] 其在生成步骤上的作用是路径
 ( [Functor_of_Steps_step] ); [Functor_of_Steps_of_Functor] 表明从 [Ordinal (S n)] 出发的每个
 函子都与这样得到的函子在 [Functor_Setoid] 下是等价的; 并且 [ord_functor_equiv_from_steps] 给出了其可用形式下的唯一性——一个在 n 个生成步骤上自然的同构族在每个态射上都是自然的。没有声称的是函子与路径之间的精确一一对应：路径的对象部分是 [nat] 上所有元素的一个函数，所以在 n 以下一致但在 n 以上不同的路径会引出相同的函子。等价 [Functor_of_Steps_of_Functor] 是在 [Functor_Setoid] 下的，即库中函子的自然同构等价。
*)

(* ---------- [le_t] is a subsingleton ---------- / ---------- [le_t] 是一个子单例 ---------- *)

Lemma nat_succ_add_neq (d m : nat) : (S (d + m) = m)%nat → False.
Proof.
  induction m as [| m' IH]; simpl; intro H.
  - discriminate.
  - apply IH.
    injection H; intro E.
    now rewrite PeanoNat.Nat.add_succ_r in E.
Qed.

Lemma le_t_sum {m n} (f : le_t m n) : ex (fun d : nat => (n = d + m)%nat).
Proof.
  induction f as [| k f' [d Hd]].
  - exists 0%nat; reflexivity.
  - exists (S d); simpl; now rewrite Hd.
Qed.

Lemma le_t_no_desc {m} (f : le_t (S m) m) : False.
Proof.
  destruct (le_t_sum f) as [d Hd].
  rewrite PeanoNat.Nat.add_succ_r in Hd.
  exact (nat_succ_add_neq d m (eq_sym Hd)).
Qed.

Lemma le_t_zero_absurd {m} (f : le_t (S m) 0) : False.
Proof.
  destruct (le_t_sum f) as [d Hd].
  rewrite PeanoNat.Nat.add_succ_r in Hd.
  discriminate.
Qed.

(*
 A derivation of [le_t n m] is either the reflexive one — which forces
 m = n — or a successor step.  [destruct] suffices because the index is a
 variable; the equality proofs it leaves behind are killed below by UIP on
 [nat], which is a theorem of decidable equality, not an axiom. 

 --------
 [le_t n m] 的一个推导要么是自反的——这会强制 m = n——要么是一个后继步骤。[destruct] 足够，因为索引是一个变量；它留下的等式证明在下面被 UIP 在 [nat] 上消解，[nat] 是可判定等式的定理，而不是公理。
*)
Lemma le_t_inv {n m} (g : le_t n m) :
  ({ e : n = m & g = eq_rect n (le_t n) le_t_n m e } +
   { m' : nat & { e : m = S m' &
       { g' : le_t n m' & g = eq_rect (S m') (le_t n) (le_t_S g') m (eq_sym e) } } })%type.
Proof.
  destruct g as [| m' g'].
  - left; exists eq_refl; reflexivity.
  - right; exists m', eq_refl, g'; reflexivity.
Qed.

(* Thinness, in its raw form: [le_t m n] has at most one inhabitant. / 瘦，原始形式：[le_t m n] 最多只有一个居住者。 *)
Lemma le_t_irr {m n} (f g : le_t m n) : f = g.
Proof.
  induction f as [| k f' IH].
  - destruct (le_t_inv g) as [[e He] | [m' [e [g' Hg]]]].
    + rewrite He.
      now rewrite (UIP_dec PeanoNat.Nat.eq_dec e eq_refl).
    + subst m.
      now destruct (le_t_no_desc g').
  - destruct (le_t_inv g) as [[e He] | [m' [e [g' Hg]]]].
    + subst m.
      now destruct (le_t_no_desc f').
    + injection e; intro E; subst m'.
      rewrite (UIP_dec PeanoNat.Nat.eq_dec e eq_refl) in Hg.
      simpl in Hg; subst g.
      now rewrite (IH g').
Qed.

(* ---------- derived arithmetic on [le_t] ---------- / ---------- 在 [le_t] 上推导的算术 ---------- *)

Definition le_t_pred_self (a : nat) : le_t (Nat.pred a) a :=
  match a with
  | O   => le_t_n
  | S k => le_t_S le_t_n
  end.

Definition le_t_pred {a b} (f : le_t a b) : le_t (Nat.pred a) (Nat.pred b) :=
  match f in le_t _ b' return le_t (Nat.pred a) (Nat.pred b') with
  | le_t_n    => le_t_n
  | le_t_S f' => le_t_trans (le_t_pred_self a) f'
  end.

Definition le_t_SS_inv {a b} (f : le_t (S a) (S b)) : le_t a b := le_t_pred f.

Fixpoint le_t_SS {a b} (f : le_t a b) : le_t (S a) (S b) :=
  match f in le_t _ b' return le_t (S a) (S b') with
  | le_t_n    => le_t_n
  | le_t_S f' => le_t_S (le_t_SS f')
  end.

Definition le_t_zero (b : nat) : le_t O b :=
  nat_rect (fun k => le_t O k) le_t_n (fun _ ih => le_t_S ih) b.

(* ---------- the ordinal on n objects, as a category ---------- / ---------- n 个对象的序数，作为一个范畴 ---------- *)

(*
 An object is one of the predecessors of n: a value, and a proof that the
 value is below n.  [ord_val] is a primitive projection, so it reduces on
 any constructor application — that is the reduction the embeddings and the
 universal property below rely on. 

 --------
 一个对象是 n 的前驱之一：一个值，以及证明该值小于 n 的证明。[ord_val] 是一个原始投影，所以它在任何构造函数应用下都会约简——这就是下面嵌入和普遍性质依赖的约简。
*)
Record Ord_obj@{u} (n : nat) : Type@{u} := ord_at {
  ord_val   : nat;
  ord_bound : le_t@{u} (S ord_val) n
}.

Arguments ord_at {n} _ _.
Arguments ord_val {n} _.
Arguments ord_bound {n} _.

(*
 The category laws are Omega's, transported along [ord_val]; the proof
 script is the one Instance/Omega.v uses for [Omega] itself. 

 --------
 类别定律是 Omega 的，通过 [ord_val] 传输；证明脚本是 Instance/Omega.v 用于 [Omega] 本身的脚本。
*)
Program Definition Ordinal@{o h p} (n : nat) : Category@{o h p} := {|
  obj     := Ord_obj@{o} n;
  hom     := fun x y => le_t@{h} (ord_val x) (ord_val y);
  homset  := Morphism_equality@{o h p};
  id      := fun _ => le_t_n@{h};
  compose := fun _ _ _ f g => le_t_trans@{h} g f
|}.
Solve All Obligations with
  (simpl; intros; try subst;
   rewrite ?le_t_trans_id_l, ?le_t_trans_id_r, ?le_t_trans_assoc;
   try reflexivity).

(*
 Thinness of [Ordinal n]: any two parallel arrows are equal, on the nose.
 This one lemma discharges essentially every coherence obligation below. 

 --------
 [Ordinal n] 的薄性：任意两条平行箭头完全相等，准确无误。这个引理基本上解决了下面的每一个一致性义务。
*)
Lemma ord_thin {n} {x y : Ordinal n} (f g : x ~> y) : f = g.
Proof. exact (le_t_irr f g). Qed.

(* Objects, too, are determined by their values, the bound being irrelevant. / 对象也是由它们的值来决定的，界限无关紧要。 *)
Lemma ord_obj_eq {n} {x y : Ord_obj n} : ord_val x = ord_val y → x = y.
Proof.
  destruct x as [i Hi], y as [j Hj]; simpl; intro e.
  subst j.
  now rewrite (le_t_irr Hi Hj).
Qed.

Definition ord_iso_of_eq {n} {x y : Ord_obj n} (e : x = y) :
  @Isomorphism (Ordinal n) x y :=
  match e in _ = z return @Isomorphism (Ordinal n) x z with
  | eq_refl => iso_id
  end.

Definition ord_iso {n} {x y : Ord_obj n} (e : ord_val x = ord_val y) :
  @Isomorphism (Ordinal n) x y := ord_iso_of_eq (ord_obj_eq e).

(* ---------- distinguished objects and the generating steps ---------- / ---------- 区分的对象和生成步骤 ---------- *)

(*
 [ord_incl x] is x viewed in the next ordinal, [ord_succ x] its successor
 there; both have the same [ord_val] as the evident numeral, definitionally,
 which is why [ord_step] can be the bare derivation [le_t_S le_t_n]. 

 --------
 [ord_incl x] 在下一个序数中被视为 x，[ord_succ x] 是其继任者；两者都有相同的 [ord_val] 作为明显的数字，从定义上讲，这就是为什么 [ord_step] 可以是简单派生的 [le_t_S le_t_n]。
*)
Definition ord_incl {n} (x : Ord_obj n) : Ord_obj (S n) :=
  ord_at (ord_val x) (le_t_S (ord_bound x)).

Definition ord_succ {n} (x : Ord_obj n) : Ord_obj (S n) :=
  ord_at (S (ord_val x)) (le_t_SS (ord_bound x)).

Definition ord_step {n} (k : Ord_obj n) :
  @hom (Ordinal (S n)) (ord_incl k) (ord_succ k) := le_t_S le_t_n.

(* ---------- the embedding functors ---------- / ---------- 嵌入函子 ---------- *)

(*
 “An ordinal is the set of its predecessors”: [Ordinal n] sits inside
 [Ordinal (S n)] as the objects below n, and inside [Omega] as the naturals
 below n.  Both functors are the identity on morphisms. 

 --------
 “一个序数是其前驱的集合”：[Ordinal n] 作为 n 以下的对象包含在 [Ordinal (S n)] 中，并且作为 n 以下的自然数包含在 [Omega] 中。这两个函子在态射上都是恒等的。
*)
Program Definition Ord_Incl (n : nat) : Ordinal n ⟶ Ordinal (S n) := {|
  fobj := ord_incl;
  fmap := fun _ _ f => f
|}.

Program Definition Ord_Omega (n : nat) : Ordinal n ⟶ Omega := {|
  fobj := ord_val;
  fmap := fun _ _ f => f
|}.

#[export] Program Instance Ord_Incl_Faithful (n : nat) : Faithful (Ord_Incl n) := {|
  fmap_inj := fun _ _ _ _ H => H
|}.
#[export] Program Instance Ord_Incl_Full (n : nat) : Full (Ord_Incl n) := {|
  prefmap := fun _ _ g => g
|}.
#[export] Program Instance Ord_Omega_Faithful (n : nat) : Faithful (Ord_Omega n) := {|
  fmap_inj := fun _ _ _ _ H => H
|}.
#[export] Program Instance Ord_Omega_Full (n : nat) : Full (Ord_Omega n) := {|
  prefmap := fun _ _ g => g
|}.

Theorem Ord_Omega_Incl (n : nat) :
  Ord_Omega (S n) ◯ Ord_Incl n ≈ Ord_Omega n.
Proof.
  exists (fun _ => iso_id).
  simpl; intros.
  apply le_t_irr.
Qed.

(* ---------- freeness: [Ordinal (S n)] is free on n composable arrows ---------- / ---------- 自由性：[Ordinal (S n)] 在 n 个可组合箭头上是自由的 ---------- *)

(*
 Fix an assignment [X] of objects to indices.  A path of n composable arrows
 over [X] is a family of steps; a functorial action on the morphisms of the
 ordinal is a family of arrows.  Both are stated over the same [X], which is
 what keeps the correspondence free of transports. 

 --------
 将对象分配给索引的作业 [X]。 在 [X] 上的 n 个可组合箭头的路径是一族步骤；对序数的态射进行函子作用是一族箭头。 两者都在相同的 [X] 上陈述，这正是使对应关系免于搬运的原因。
*)
Definition OrdSteps {C : Category} (n : nat) (X : nat → C) : Type :=
  ∀ k : nat, le_t (S k) n → X k ~> X (S k).

Definition OrdArrows {C : Category} (n : nat) (X : nat → C) : Type :=
  ∀ i j : nat, le_t j n → le_t i j → X i ~> X j.

(*
 The arrow i ~> j is sent to the composite of the steps between them; the
 recursion is on the derivation of i ≤ j, and the bound on j is threaded
 along so that only the n available steps are ever consulted. 

 --------
 箭头 i ~> j 被发送到它们之间步骤的复合；递归作用于 i ≤ j 的推导，并且 j 的界限被传递下去，以便只参考可用的 n 个步骤。
*)
Fixpoint chain_fmap {C : Category} {n : nat} {X : nat → C} (s : OrdSteps n X)
  {i j : nat} (f : le_t i j) {struct f} : le_t j n → X i ~> X j :=
  match f in le_t _ j' return le_t j' n → X i ~> X j' with
  | le_t_n    => fun _ => id
  | le_t_S f' => fun H => s _ H ∘ chain_fmap s f' (le_t_trans (le_t_S le_t_n) H)
  end.

(*
 Definitional sanity pin (unused below; the [eq_refl]-style check that the
 fold sends reflexivity to the identity, kept so a refactor that breaks it
 is caught here rather than downstream). 

 --------
 定义性健全别针（在下面未使用；[eq_refl] 风格的检查，确保折叠将自反性发送到恒等，保留它以便如果重构破坏它，可以在这里而不是下游被捕获）。
*)
Lemma chain_fmap_id {C : Category} {n} {X : nat → C} (s : OrdSteps n X)
  (i : nat) (H : le_t i n) : chain_fmap s (@le_t_n i) H ≈ id.
Proof. reflexivity. Qed.

Lemma chain_fmap_comp {C : Category} {n} {X : nat → C} (s : OrdSteps n X)
  {i j k : nat} (g : le_t i j) (f : le_t j k) :
  ∀ (Hj : le_t j n) (Hk : le_t k n),
    chain_fmap s (le_t_trans g f) Hk ≈ chain_fmap s f Hk ∘ chain_fmap s g Hj.
Proof.
  induction f as [| m f' IH]; simpl; intros Hj Hk.
  - rewrite id_left.
    now rewrite (le_t_irr Hk Hj).
  - rewrite <- comp_assoc.
    now rewrite (IH Hj (le_t_trans (le_t_S le_t_n) Hk)).
Qed.

(*
 A path of n arrows gives a genuine functor out of the ordinal on n+1
 objects, whose action on objects is [X] read off the index. 

 --------
 一条由 n 支箭头组成的路径给出了一个从包含 n+1 个对象的序数出的真正函子，其在对象上的作用是根据索引读作 [X]。
*)
Program Definition Functor_of_Steps {C : Category} {n : nat} {X : nat → C}
  (s : OrdSteps n X) : Ordinal (S n) ⟶ C := {|
  fobj := fun x => X (ord_val x);
  fmap := fun _ y f => chain_fmap s f (le_t_SS_inv (ord_bound y))
|}.
Next Obligation. apply chain_fmap_comp. Qed.

Theorem Functor_of_Steps_step {C : Category} {n : nat} {X : nat → C}
  (s : OrdSteps n X) (k : Ord_obj n) :
  fmap[Functor_of_Steps s] (ord_step k) ≈ s (ord_val k) (ord_bound k).
Proof.
  simpl.
  rewrite id_right.
  now rewrite (le_t_irr (le_t_SS_inv (le_t_SS (ord_bound k))) (ord_bound k)).
Qed.

Definition steps_of_arrows {C : Category} {n} {X : nat → C} (u : OrdArrows n X) :
  OrdSteps n X := fun k H => u k (S k) H (le_t_S le_t_n).

Definition arrows_of_steps {C : Category} {n} {X : nat → C} (s : OrdSteps n X) :
  OrdArrows n X := fun i j H f => chain_fmap s f H.

(* Restricting the generated action back to the steps returns the path. / 将生成的动作限制回步骤会返回路径。 *)
Theorem steps_arrows_steps {C : Category} {n} {X : nat → C} (s : OrdSteps n X) :
  ∀ k H, steps_of_arrows (arrows_of_steps s) k H ≈ s k H.
Proof.
  intros k H; unfold steps_of_arrows, arrows_of_steps; simpl.
  now rewrite id_right.
Qed.

(* And a functorial action is determined by its steps: this is the freeness. / 函子作用由其步骤决定：这就是自由性。 *)
Theorem arrows_steps_arrows {C : Category} {n} {X : nat → C} (u : OrdArrows n X)
  (Hid : ∀ i (H : le_t i n), u i i H le_t_n ≈ id)
  (Hcomp : ∀ i j k (Hj : le_t j n) (Hk : le_t k n) (g : le_t i j) (f : le_t j k),
      u i k Hk (le_t_trans g f) ≈ u j k Hk f ∘ u i j Hj g) :
  ∀ i j (f : le_t i j) (H : le_t j n),
    arrows_of_steps (steps_of_arrows u) i j H f ≈ u i j H f.
Proof.
  unfold arrows_of_steps, steps_of_arrows.
  intros i j f; induction f as [| m f' IH]; simpl; intro H.
  - now rewrite Hid.
  - rewrite IH.
    assert (E : u i (S m) H (le_t_S f')
                  ≈ u m (S m) H (le_t_S le_t_n)
                      ∘ u i m (le_t_trans (le_t_S le_t_n) H) f')
      by apply (Hcomp i m (S m) (le_t_trans (le_t_S le_t_n) H) H f' (le_t_S le_t_n)).
    now rewrite E.
Qed.

(*
 Record eta on [Ord_obj]: an object is its value paired with its bound,
 definitionally.  This is what lets the value-indexed naturality lemma below
 be applied at an arbitrary object. 

 --------
 在 [Ord_obj] 上记录 eta：一个对象在定义上是它的值与其绑定的配对。这就是使下面的以值为索引的自然性引理能够应用于任意对象的原因。
*)
Example ord_eta {n} (x : Ord_obj n) : ord_at (ord_val x) (ord_bound x) = x := eq_refl.

(*
 The uniqueness half of freeness, in the form the setoid discipline wants:
 naturality need only be checked on the n generating steps. 

 --------
 自由性的一半独特性，以集合论规范所希望的形式：自然性只需要在 n 个生成步骤上进行检查。
*)
Theorem ord_naturality_from_steps {C : Category} {n : nat}
  (F G : Ordinal (S n) ⟶ C) (θ : ∀ x : Ord_obj (S n), F x ≅ G x)
  (Hgen : ∀ k : Ord_obj n,
      to (θ (ord_succ k)) ∘ fmap[F] (ord_step k)
        ≈ fmap[G] (ord_step k) ∘ to (θ (ord_incl k))) :
  ∀ (i j : nat) (f : le_t i j) (Hi : le_t (S i) (S n)) (Hj : le_t (S j) (S n)),
    to (θ (ord_at j Hj)) ∘ @fmap _ _ F (ord_at i Hi) (ord_at j Hj) f
      ≈ @fmap _ _ G (ord_at i Hi) (ord_at j Hj) f ∘ to (θ (ord_at i Hi)).
Proof.
  intros i j f; induction f as [| m f' IH]; intros Hi Hj.
  - rewrite (le_t_irr Hj Hi).
    assert (EF : @fmap _ _ F (ord_at i Hi) (ord_at i Hi) le_t_n ≈ id)
      by exact (@fmap_id _ _ F (ord_at i Hi)).
    assert (EG : @fmap _ _ G (ord_at i Hi) (ord_at i Hi) le_t_n ≈ id)
      by exact (@fmap_id _ _ G (ord_at i Hi)).
    rewrite EF, EG.
    now rewrite id_left, id_right.
  - pose (Hm := le_t_SS_inv Hj : le_t (S m) n).
    rewrite (le_t_irr Hj (le_t_SS Hm)).
    assert (Estep : @fmap _ _ F (ord_at i Hi) (ord_at (S m) (le_t_SS Hm)) (le_t_S f')
              ≈ fmap[F] (ord_step (ord_at m Hm))
                  ∘ @fmap _ _ F (ord_at i Hi) (ord_at m (le_t_S Hm)) f').
    { rewrite <- fmap_comp.
      apply fmap_respects, le_t_irr. }
    assert (Estep' : @fmap _ _ G (ord_at i Hi) (ord_at (S m) (le_t_SS Hm)) (le_t_S f')
              ≈ fmap[G] (ord_step (ord_at m Hm))
                  ∘ @fmap _ _ G (ord_at i Hi) (ord_at m (le_t_S Hm)) f').
    { rewrite <- fmap_comp.
      apply fmap_respects, le_t_irr. }
    rewrite Estep, Estep'.
    rewrite comp_assoc.
    rewrite (Hgen (ord_at m Hm)).
    rewrite <- comp_assoc.
    rewrite (IH Hi (le_t_S Hm)).
    now rewrite comp_assoc.
Qed.

Lemma ord_iso_natural_flip {C : Category} {a b c d : C}
  (i : a ≅ c) (j : b ≅ d) (u : a ~> b) (v : c ~> d)
  (H : to j ∘ u ≈ v ∘ to i) : u ≈ from j ∘ v ∘ to i.
Proof.
  rewrite <- comp_assoc.
  rewrite <- H.
  rewrite comp_assoc.
  rewrite iso_from_to.
  now rewrite id_left.
Qed.

Theorem ord_functor_equiv_from_steps {C : Category} {n : nat}
  (F G : Ordinal (S n) ⟶ C) (θ : ∀ x : Ord_obj (S n), F x ≅ G x)
  (Hgen : ∀ k : Ord_obj n,
      to (θ (ord_succ k)) ∘ fmap[F] (ord_step k)
        ≈ fmap[G] (ord_step k) ∘ to (θ (ord_incl k))) :
  F ≈ G.
Proof.
  exists θ.
  intros x y f.
  apply (ord_iso_natural_flip (θ x) (θ y)).
  exact (ord_naturality_from_steps F G θ Hgen
           (ord_val x) (ord_val y) f (ord_bound x) (ord_bound y)).
Qed.

(* ---------- every functor out of [Ordinal (S n)] comes from a path ---------- / ---------- [Ordinal (S n)] 的每个函子都来自一条路径 ---------- *)

Fixpoint le_t_min (k n : nat) {struct k} : le_t (Nat.min k n) n :=
  match k as k0 return le_t (Nat.min k0 n) n with
  | O => le_t_zero n
  | S k' => match n as n0 return le_t (Nat.min (S k') n0) n0 with
            | O => le_t_n
            | S n' => le_t_SS (le_t_min k' n')
            end
  end.

Lemma le_t_min_l (k n : nat) : le_t k n → (Nat.min k n = k)%nat.
Proof.
  revert n; induction k as [| k' IH]; intros n H.
  - reflexivity.
  - destruct n as [| n'].
    + destruct (le_t_zero_absurd H).
    + simpl; f_equal.
      exact (IH n' (le_t_SS_inv H)).
Qed.

(*
 An index of [Ordinal (S n)], read off a natural number by clamping.  The
 clamping is what makes the object part of a path total on [nat]; on the
 indices that matter it is the identity ([ord_clamp_id]). 

 --------
 [Ordinal (S n)] 的一个索引，通过夹取读取一个自然数。夹取使对象成为 [nat] 上路径总和的一部分；在重要的索引上，它是恒等的（[ord_clamp_id]）。
*)
Definition ord_clamp {n : nat} (k : nat) : Ord_obj (S n) :=
  ord_at (Nat.min k n) (le_t_SS (le_t_min k n)).

Lemma ord_clamp_id {n} (x : Ord_obj (S n)) : ord_clamp (ord_val x) = x.
Proof.
  apply ord_obj_eq; simpl.
  apply le_t_min_l.
  exact (le_t_SS_inv (ord_bound x)).
Qed.

Definition ord_mor_of_eq {n} {x y : Ord_obj n} (e : x = y) :
  @hom (Ordinal n) x y :=
  match e in _ = z return @hom (Ordinal n) x z with
  | eq_refl => le_t_n
  end.

(*
 Equal objects of a thin category have a canonical isomorphism, and a functor
 carries it over; the inverse laws follow from thinness alone. 

 --------
 薄范畴中的相等对象具有一个典型的同构，并且函子会将其传递过去；逆律仅从薄性本身即可得到。
*)
Program Definition ord_functor_iso {n} {C : Category} (F : Ordinal n ⟶ C)
  {x y : Ord_obj n} (e : x = y) : F x ≅ F y := {|
  to   := fmap[F] (ord_mor_of_eq e);
  from := fmap[F] (ord_mor_of_eq (eq_sym e))
|}.
Solve All Obligations with
  (intros; rewrite <- fmap_comp; rewrite <- (@fmap_id _ _ F _);
   apply fmap_respects, le_t_irr).

Lemma ord_clamp_eq {n} (k : nat) (H : le_t k n) :
  @ord_clamp n k = ord_at k (le_t_SS H).
Proof. apply ord_obj_eq; simpl; now apply le_t_min_l. Qed.

Definition ord_clamp_step {n} (k : nat) (H : le_t (S k) n) :
  @hom (Ordinal (S n)) (@ord_clamp n k) (@ord_clamp n (S k)).
Proof.
  rewrite (ord_clamp_eq k (le_t_trans (le_t_S le_t_n) H)).
  rewrite (ord_clamp_eq (S k) H).
  exact (le_t_S le_t_n).
Defined.

(*
 The path underlying a functor: its objects at the clamped indices, its
 arrows at the n generating steps. 

 --------
 函子下的路径：其在固定指标上的对象，其在 n 个生成步骤上的箭头。
*)
Definition steps_of_functor {n} {C : Category} (F : Ordinal (S n) ⟶ C) :
  OrdSteps n (fun k => F (@ord_clamp n k)) :=
  fun k H => fmap[F] (ord_clamp_step k H).

Theorem Functor_of_Steps_of_Functor {n} {C : Category} (F : Ordinal (S n) ⟶ C) :
  Functor_of_Steps (steps_of_functor F) ≈ F.
Proof.
  apply (ord_functor_equiv_from_steps
           (Functor_of_Steps (steps_of_functor F)) F
           (fun x => ord_functor_iso F (ord_clamp_id x))).
  intro k.
  rewrite (Functor_of_Steps_step (steps_of_functor F) k).
  unfold steps_of_functor; simpl.
  rewrite <- !fmap_comp.
  apply fmap_respects, le_t_irr.
Qed.

(* ---------- counting the morphisms ---------- / ---------- 计数同态 ---------- *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

(*
 Bridges between the [Type]-valued [le_t] and the [Prop]-valued stdlib order.
 The direction into [Type] goes through the boolean test, since a [Prop]
 cannot be eliminated into [Type] directly. 

 --------
 在 [Type] 值的 [le_t] 和 [Prop] 值的 stdlib 顺序之间的桥梁。进入 [Type] 的方向需要通过布尔测试，因为 [Prop] 不能直接被消除到 [Type]。
*)
Definition le_t_of_leb : ∀ (m n : nat), (Nat.leb m n = true) → le_t m n.
Proof.
  induction m as [| m' IH]; intros n H.
  - exact (le_t_zero n).
  - destruct n as [| n'].
    + simpl in H; discriminate.
    + exact (le_t_SS (IH n' H)).
Defined.

Definition le_t_of_le {m n : nat} (H : (m <= n)%nat) : le_t m n :=
  le_t_of_leb m n (proj2 (PeanoNat.Nat.leb_le m n) H).

Lemma le_t_to_le {m n : nat} (f : le_t m n) : (m <= n)%nat.
Proof.
  destruct (le_t_sum f) as [d Hd].
  lia.
Qed.

(* The total space of all morphisms of [Ordinal n], bundled with endpoints. / 所有 [Ordinal n] 的态射的总空间，连同端点一起捆绑。 *)
Definition OrdMor (n : nat) : Type :=
  { x : Ord_obj n & { y : Ord_obj n & @hom (Ordinal n) x y } }.

Definition ord_coords {n} (m : OrdMor n) : (nat * nat)%type :=
  (ord_val (projT1 m), ord_val (projT1 (projT2 m))).

(*
 A morphism is determined by its pair of endpoint indices: both the objects
 (their bounds being irrelevant) and the arrow between them (thinness). 

 --------
 一个态射由它的端点索引对决定：两个对象（它们的界限无关紧要）以及它们之间的箭头（单薄性）。
*)
Theorem ord_coords_inj {n} (a b : OrdMor n) : ord_coords a = ord_coords b → a = b.
Proof.
  destruct a as [x [y f]], b as [x' [y' f']].
  unfold ord_coords; simpl; intro E.
  assert (E1 : ord_val x = ord_val x') by (now inversion E).
  assert (E2 : ord_val y = ord_val y') by (now inversion E).
  pose proof (ord_obj_eq E1) as Ex.
  pose proof (ord_obj_eq E2) as Ey.
  subst x' y'.
  now rewrite (le_t_irr f f').
Qed.

(* Conversely the pairs that arise are exactly those with i ≤ j < n. / 相反地，产生的对应正好是那些满足 i ≤ j < n 的情况。 *)
Theorem ord_coords_range {n} (m : OrdMor n) :
  (le_t (fst (ord_coords m)) (snd (ord_coords m)) *
   le_t (S (snd (ord_coords m))) n)%type.
Proof.
  destruct m as [x [y f]]; simpl.
  exact (f, ord_bound y).
Qed.

Definition ord_mor_of_coords {n} (i j : nat) (f : le_t i j) (H : le_t (S j) n) :
  OrdMor n :=
  existT _ (ord_at i (le_t_trans (le_t_SS f) H))
           (existT _ (ord_at j H) f).

(* Definitional sanity pin for the coordinate round trip (unused below; [ord_mor_of_pair] re-derives the fact inline where it is consumed). / 用于坐标往返的定义性安全销（以下未使用；[ord_mor_of_pair] 在使用时重新在线推导该事实）。 *)
Theorem ord_coords_onto {n} (i j : nat) (f : le_t i j) (H : le_t (S j) n) :
  ord_coords (ord_mor_of_coords i j f H) = (i, j).
Proof. reflexivity. Qed.

(* The enumeration of those pairs. [ord_downto k] lists k, k-1, ..., 0, and [ord_pairs n] lists, for each target k < n, every source i ≤ k. / 这些对的枚举。[ord_downto k] 列出 k, k-1, ..., 0，而 [ord_pairs n] 对于每个目标 k < n，列出每个源 i ≤ k。 *)
Fixpoint ord_downto (k : nat) : list nat :=
  match k with
  | O    => cons O nil
  | S k' => cons (S k') (ord_downto k')
  end.

Fixpoint ord_tri (n : nat) : nat :=
  match n with
  | O   => O
  | S k => (S k + ord_tri k)%nat
  end.

Fixpoint ord_pairs (n : nat) : list (nat * nat) :=
  match n with
  | O   => nil
  | S k => app (map (fun i => (i, k)) (ord_downto k)) (ord_pairs k)
  end.

(*
 These two list lemmas are proven locally rather than imported: the stdlib
 renamed [app_length]/[map_length] to [length_app]/[length_map] in 8.20.
 The old names still resolve (deprecated) on 9.1, but the new ones are
 absent on 8.19, and depending on either pair ties this file to one end of
 the supported range; a local two-liner does not.
 Construction/ColouredPROP/UnitBridge.v carries the same lemma as
 [len_app] with the same rationale. 

 --------
 这两个列表引理是在本地证明的，而不是导入的：stdlib 在 8.20 中将 [app_length] / [map_length] 重命名为 [length_app] / [length_map]。旧名称在 9.1 中仍然可解析（已弃用），但新名称在 8.19 中不存在，并且依赖任意一对都会将此文件绑定到支持范围的一端；本地的两行代码则不会。Construction/ColouredPROP/UnitBridge.v 拥有与 [len_app] 相同的引理，并具有相同的理由。
*)
Lemma ord_len_app {A} (l l' : list A) :
  (length (app l l') = length l + length l')%nat.
Proof. induction l as [| a l IH]; simpl; auto. Qed.

Lemma ord_len_map {A B} (f : A → B) (l : list A) :
  (length (map f l) = length l)%nat.
Proof. induction l as [| a l IH]; simpl; auto. Qed.

Lemma ord_downto_length (k : nat) : (length (ord_downto k) = S k)%nat.
Proof. induction k as [| k' IH]; simpl; auto. Qed.

Lemma ord_downto_le (k i : nat) : In i (ord_downto k) → (i <= k)%nat.
Proof.
  induction k as [| k' IH]; simpl; intros [H | H].
  - lia.
  - contradiction.
  - lia.
  - pose proof (IH H); lia.
Qed.

Lemma ord_downto_complete (k i : nat) : (i <= k)%nat → In i (ord_downto k).
Proof.
  induction k as [| k' IH]; simpl; intro H.
  - left; lia.
  - destruct (PeanoNat.Nat.eq_dec i (S k')) as [E | E].
    + left; lia.
    + right; apply IH; lia.
Qed.

Lemma ord_downto_nodup (k : nat) : NoDup (ord_downto k).
Proof.
  induction k as [| k' IH]; simpl.
  - constructor; [ simpl; tauto | constructor ].
  - constructor.
    + intro Hin.
      pose proof (ord_downto_le k' (S k') Hin); lia.
    + exact IH.
Qed.

Lemma ord_nodup_app {A} (l l' : list A) :
  NoDup l → NoDup l' → (∀ x, In x l → In x l' → False) → NoDup (app l l').
Proof.
  induction l as [| a l IH]; simpl; intros H1 H2 Hd.
  - exact H2.
  - inversion H1 as [| a' l'' Hnin Hnd]; subst.
    constructor.
    + intro Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      * contradiction.
      * exact (Hd a (or_introl eq_refl) Hin).
    + apply IH; auto.
      intros x Hx Hx'.
      exact (Hd x (or_intror Hx) Hx').
Qed.

Lemma ord_nodup_map_inj {A B} (f : A → B) (l : list A) :
  (∀ x y, f x = f y → x = y) → NoDup l → NoDup (map f l).
Proof.
  intros Hinj Hnd.
  induction Hnd as [| a l Hnin Hnd IH]; simpl.
  - constructor.
  - constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [b [Hb Hbin]].
      apply Hinj in Hb; subst b.
      contradiction.
    + exact IH.
Qed.

Lemma ord_pairs_length (n : nat) : (length (ord_pairs n) = ord_tri n)%nat.
Proof.
  induction n as [| k IH]; simpl; auto.
  now rewrite ord_len_app, ord_len_map, ord_downto_length, IH.
Qed.

(* The closed formula, by induction on n rather than case by case. It is stated in the doubled form because n * (n + 1) / 2 in [nat] would have to divide by hand. / 闭合公式，是通过对 n 的归纳而不是逐个情况得出的。它以双倍形式表示，因为在 [nat] 中 n * (n + 1) / 2 必须手动除法。 *)
Theorem ord_tri_closed (n : nat) : (2 * ord_tri n = n * (n + 1))%nat.
Proof.
  induction n as [| k IH]; simpl; [ reflexivity |].
  nia.
Qed.

Lemma ord_pairs_sound (n i j : nat) :
  In (i, j) (ord_pairs n) → ((i <= j)%nat /\ (j < n)%nat).
Proof.
  induction n as [| k IH]; simpl; intro Hin.
  - contradiction.
  - apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + apply in_map_iff in Hin.
      destruct Hin as [i0 [E Hi0]].
      assert (Ei : i0 = i) by (now inversion E).
      assert (Ej : k = j) by (now inversion E).
      subst i0.
      pose proof (ord_downto_le k i Hi0); lia.
    + destruct (IH Hin); lia.
Qed.

Lemma ord_pairs_complete (n i j : nat) :
  (i <= j)%nat → (j < n)%nat → In (i, j) (ord_pairs n).
Proof.
  revert i j; induction n as [| k IH]; simpl; intros i j Hij Hj.
  - lia.
  - apply in_or_app.
    destruct (PeanoNat.Nat.eq_dec j k) as [E | E].
    + left; subst j.
      apply in_map_iff.
      exists i; split; [ reflexivity |].
      apply ord_downto_complete; lia.
    + right; apply IH; lia.
Qed.

Theorem ord_pairs_nodup (n : nat) : NoDup (ord_pairs n).
Proof.
  induction n as [| k IH]; simpl.
  - constructor.
  - apply ord_nodup_app.
    + apply ord_nodup_map_inj.
      * intros x y E; now inversion E.
      * apply ord_downto_nodup.
    + exact IH.
    + intros [i j] Hin1 Hin2.
      apply in_map_iff in Hin1.
      destruct Hin1 as [i0 [E _]].
      assert (Ej : k = j) by (now inversion E).
      subst j.
      destruct (ord_pairs_sound k i k Hin2); lia.
Qed.

(*
 The count, assembled: [ord_coords] is an injection from the morphisms of
 [Ordinal n] ONTO the elements of [ord_pairs n], a list without repetitions
 whose length t satisfies 2t = n(n+1). 

 --------
 计数，组装：[ord_coords] 是一个从 [Ordinal n] 的态射到 [ord_pairs n] 元素的单射，一个无重复的列表，其长度 t 满足 2t = n(n+1)。
*)
Theorem ord_coords_in_pairs {n} (m : OrdMor n) : In (ord_coords m) (ord_pairs n).
Proof.
  destruct (ord_coords_range m) as [Hle Hlt].
  destruct (ord_coords m) as [i j] eqn:E; simpl in *.
  apply ord_pairs_complete.
  - exact (le_t_to_le Hle).
  - pose proof (le_t_to_le Hlt); lia.
Qed.

Theorem ord_mor_of_pair {n} (i j : nat) (Hij : (i <= j)%nat) (Hj : (j < n)%nat) :
  { m : OrdMor n & ord_coords m = (i, j) }.
Proof.
  exists (ord_mor_of_coords i j (le_t_of_le Hij) (le_t_of_le Hj)).
  reflexivity.
Qed.

Theorem ord_morphism_count (n : nat) :
  (2 * length (ord_pairs n) = n * (n + 1))%nat.
Proof. now rewrite ord_pairs_length, ord_tri_closed. Qed.

Example ord_tri_3 : ord_tri 3 = 6%nat := eq_refl.
Example ord_pairs_3 : length (ord_pairs 3) = 6%nat := eq_refl.
Example ord_tri_4 : ord_tri 4 = 10%nat := eq_refl.

(* ---------- the carrier is the standard finite ordinal [Fin.t n] ---------- / ---------- 载体是标准有限序数 [Fin.t n] ---------- *)

Require Import Coq.Vectors.Fin.

Fixpoint fin_val {n} (i : Fin.t n) : nat :=
  match i with
  | Fin.F1   => O
  | Fin.FS j => S (fin_val j)
  end.

Fixpoint fin_bound {n} (i : Fin.t n) : le_t (S (fin_val i)) n :=
  match i as i0 in Fin.t n0 return le_t (S (fin_val i0)) n0 with
  | Fin.F1   => le_t_SS (le_t_zero _)
  | Fin.FS j => le_t_SS (fin_bound j)
  end.

Definition ord_of_fin {n} (i : Fin.t n) : Ord_obj n :=
  ord_at (fin_val i) (fin_bound i).

Fixpoint fin_of_nat (k n : nat) : le_t (S k) n → Fin.t n :=
  match n as n0 return le_t (S k) n0 → Fin.t n0 with
  | O    => fun H => False_rect _ (le_t_zero_absurd H)
  | S n' =>
      match k as k0 return le_t (S k0) (S n') → Fin.t (S n') with
      | O    => fun _ => Fin.F1
      | S k' => fun H => Fin.FS (fin_of_nat k' n' (le_t_SS_inv H))
      end
  end.

Definition fin_of_ord {n} (x : Ord_obj n) : Fin.t n :=
  fin_of_nat (ord_val x) n (ord_bound x).

Lemma fin_val_of_nat (k n : nat) (H : le_t (S k) n) :
  fin_val (fin_of_nat k n H) = k.
Proof.
  revert k H; induction n as [| n' IH]; intros k H.
  - destruct (le_t_zero_absurd H).
  - destruct k as [| k']; simpl.
    + reflexivity.
    + now rewrite IH.
Qed.

Theorem ord_of_fin_of_ord {n} (x : Ord_obj n) : ord_of_fin (fin_of_ord x) = x.
Proof.
  apply ord_obj_eq; simpl.
  apply fin_val_of_nat.
Qed.

Theorem fin_of_ord_of_fin {n} (i : Fin.t n) : fin_of_ord (ord_of_fin i) = i.
Proof.
  unfold fin_of_ord, ord_of_fin; simpl.
  induction i as [n' | n' i' IH]; simpl.
  - reflexivity.
  - f_equal.
    rewrite (le_t_irr (le_t_SS_inv (le_t_SS (fin_bound i'))) (fin_bound i')).
    exact IH.
Qed.

(* ---------- agreement with the hand-built small ordinals ---------- / ---------- 与手工构建的小序数一致 ---------- *)

(*
 Instance/Zero.v and Instance/One.v install the notations “0” and “1” in
 [category_scope] for [_0] and [_1], so from here on the numerals 0 and 1
 are written [0%nat] and [1%nat] when a natural number is meant.  The three
 requires are deliberately placed here, after the arithmetic, exactly as
 Instance/Two.v places its require of Instance/Sets.v. 

 --------
 Instance/Zero.v 和 Instance/One.v 在 [category_scope] 中为 [_0] 和 [_1] 安装了符号“0”和“1”，因此从此处开始，当表示自然数时，数字 0 和 1 被写作 [0%nat] 和 [1%nat]。三个 require 被故意放在这里，在算术之后，正如 Instance/Two.v 对 Instance/Sets.v 的 require 放置方式一样。
*)
Require Import Category.Instance.Cat.
Require Import Category.Instance.Zero.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.

Lemma ord_0_empty (x : Ord_obj 0%nat) : False.
Proof. exact (le_t_zero_absurd (ord_bound x)). Qed.

Program Definition Ordinal_0_to : Ordinal 0%nat ⟶ _0 := {|
  fobj := fun x => False_rect _ (ord_0_empty x);
  fmap := fun x _ _ => False_rect _ (ord_0_empty x)
|}.
Solve All Obligations with (intros; destruct (ord_0_empty x)).

Program Definition Ordinal_0_iso : Ordinal 0%nat ≅[Cat] _0 := {|
  to   := Ordinal_0_to;
  from := From_0 (Ordinal 0%nat)
|}.
Solve All Obligations with
  (unshelve refine (existT _ _ _);
   [ intro x | intros x y f ];
   first [ destruct (ord_0_empty x) | destruct x ]).

Lemma ord_1_val (x : Ord_obj 1%nat) : (ord_val x = 0)%nat.
Proof.
  destruct x as [i H]; simpl.
  destruct i as [| i']; [ reflexivity |].
  destruct (le_t_zero_absurd (le_t_SS_inv H)).
Qed.

Program Definition Ordinal_1_from : _1 ⟶ Ordinal 1%nat := {|
  fobj := fun _ => ord_at 0%nat le_t_n;
  fmap := fun _ _ _ => le_t_n
|}.

Program Definition Ordinal_1_iso : Ordinal 1%nat ≅[Cat] _1 := {|
  to   := Erase (Ordinal 1%nat);
  from := Ordinal_1_from
|}.
Next Obligation.
  unshelve refine (existT _ _ _).
  - intro x; destruct x; exact iso_id.
  - intros x y f; destruct x, y; simpl; reflexivity.
Qed.
Next Obligation.
  exists (fun x => @ord_iso 1%nat (ord_at 0%nat le_t_n) x (eq_sym (ord_1_val x))).
  intros x y f; simpl.
  apply le_t_irr.
Qed.

(*
 Thinness of [_2].  Instance/Two/Monoidal.v proves the same statement, under
 the name [two_thin]; it is reproven here in three lines from
 Instance/Two.v's [TwoHom_inv] -- the inversion principle both proofs rest
 on -- so that Instance/Ordinal.v need not require the monoidal tower. 

 --------
 [_2] 的薄性。Instance/Two/Monoidal.v 在名为 [two_thin] 的情况下证明了相同的命题；这里从 Instance/Two.v 的 [TwoHom_inv] 出发，用三行再次证明 —— 两个证明都依赖的反演原理 —— 因此 Instance/Ordinal.v 无需依赖单调塔。
*)
Lemma ord_two_thin {a b : TwoObj} (f g : TwoHom a b) : f = g.
Proof.
  pose proof (TwoHom_inv a b f) as Hf.
  pose proof (TwoHom_inv a b g) as Hg.
  destruct a, b; simpl in *; try contradiction; congruence.
Qed.

Definition ord_two_of (i : nat) : TwoObj :=
  match i with
  | O   => TwoX
  | S _ => TwoY
  end.

Definition ord2_map (i j : nat) : le_t i j → TwoHom (ord_two_of i) (ord_two_of j) :=
  match i as i0, j as j0
    return le_t i0 j0 → TwoHom (ord_two_of i0) (ord_two_of j0) with
  | O, O     => fun _ => TwoIdX
  | O, S _   => fun _ => TwoXY
  | S _, O   => fun f => False_rect _ (le_t_zero_absurd f)
  | S _, S _ => fun _ => TwoIdY
  end.

Program Definition Ordinal_2_to : Ordinal 2 ⟶ _2 := {|
  fobj := fun x => ord_two_of (ord_val x);
  fmap := fun x y f => ord2_map (ord_val x) (ord_val y) f
|}.
Solve All Obligations with (intros; apply ord_two_thin).

Definition ord2_obj (a : TwoObj) : Ord_obj 2 :=
  match a with
  | TwoX => ord_at 0%nat (le_t_S le_t_n)
  | TwoY => ord_at 1%nat le_t_n
  end.

Definition ord2_hom {a b : TwoObj} (f : TwoHom a b) :
  @hom (Ordinal 2) (ord2_obj a) (ord2_obj b) :=
  match f with
  | TwoIdX => le_t_n
  | TwoIdY => le_t_n
  | TwoXY  => le_t_S le_t_n
  end.

Program Definition Ordinal_2_from : _2 ⟶ Ordinal 2 := {|
  fobj := ord2_obj;
  fmap := fun _ _ f => ord2_hom f
|}.
Solve All Obligations with (intros; apply le_t_irr).

Lemma ord_2_val (x : Ord_obj 2) :
  ord_val (ord2_obj (ord_two_of (ord_val x))) = ord_val x.
Proof.
  destruct x as [i H]; simpl.
  destruct i as [| i']; [ reflexivity |].
  destruct i' as [| i'']; [ reflexivity |].
  destruct (le_t_zero_absurd (le_t_SS_inv (le_t_SS_inv H))).
Qed.

Program Definition Ordinal_2_iso : Ordinal 2 ≅[Cat] _2 := {|
  to   := Ordinal_2_to;
  from := Ordinal_2_from
|}.
Next Obligation.
  unshelve refine (existT _ _ _).
  - intro a; destruct a; exact iso_id.
  - intros a b f; apply ord_two_thin.
Qed.
Next Obligation.
  exists (fun x => ord_iso (ord_2_val x)).
  intros x y f; apply le_t_irr.
Qed.

(* ---------- the next two ordinals, and diagrams of shape 4 ---------- / ---------- 接下来的两个序数，以及形状4的图示 ---------- *)

(*
 [_3] continues the sequence [_0], [_1], [_2]: three objects, two generating
 steps.  [_4] is the shape Riehl §1.6 calls 4 — four objects, three
 generating steps, and the composites they generate. 

 --------
 [_3] 继续了序列 [_0]、[_1]、[_2]：三个对象，两个生成步骤。[_4] 是 Riehl §1.6 所称的 4 的形状——四个对象，三个生成步骤，以及它们生成的复合物。
*)
(*
 Full @{o h p} profiles, so the exported shapes sit beside _1@{o h p} and
 Omega@{o h p} rather than collapsing h and p as inference would.  (A
 related construction exists in tree: Theory/Metacategory.v's [Three],
 built arrows-only from a composition table.  It is NOT a rival
 three-object category: under that file's unguarded [identity] field no
 arrow of its table is an identity, so [Three] has no objects at all --
 a machine-checked fact recorded in that file's header.  No comparison
 is attempted here.) 

 --------
 完整的 @{o h p} 配置文件，因此导出的形状位于 _1@{o h p} 和 Omega@{o h p} 旁边，而不是像推理那样折叠 h 和 p。（在 tree: Theory/Metacategory.v 中有一个相关构造 [Three]，是从组合表中仅构建箭头而得的。它不是一个竞争性的三对象范畴：在该文件未受保护的 [identity] 字段下，其表中的箭头没有一个是恒等箭头，因此 [Three] 根本没有对象——这是该文件头部记录的机器检验事实。这里不进行比较。）
*)
Definition _3@{o h p} : Category@{o h p} := Ordinal@{o h p} 3.
Definition _4@{o h p} : Category@{o h p} := Ordinal@{o h p} 4.

Definition three_steps {C : Category} (X : nat → C)
  (f0 : X 0%nat ~> X 1%nat) (f1 : X 1%nat ~> X 2%nat) (f2 : X 2%nat ~> X 3%nat) :
  OrdSteps 3 X :=
  fun k =>
    match k as k0 return le_t (S k0) 3 → X k0 ~> X (S k0) with
    | O            => fun _ => f0
    | S O          => fun _ => f1
    | S (S O)      => fun _ => f2
    | S (S (S k')) => fun H =>
        False_rect _ (le_t_zero_absurd
                        (le_t_SS_inv (le_t_SS_inv (le_t_SS_inv H))))
    end.

(* Three composable morphisms give a diagram of shape 4 ... / 三个可组合的态射给出一个形状为 4 的图表... *)
Definition Functor_of_Triple {C : Category} (X : nat → C)
  (f0 : X 0%nat ~> X 1%nat) (f1 : X 1%nat ~> X 2%nat) (f2 : X 2%nat ~> X 3%nat) :
  _4 ⟶ C := Functor_of_Steps (three_steps X f0 f1 f2).

Definition ord3_0 : Ord_obj 3 := ord_at 0%nat (le_t_S (le_t_S le_t_n)).
Definition ord3_1 : Ord_obj 3 := ord_at 1%nat (le_t_S le_t_n).
Definition ord3_2 : Ord_obj 3 := ord_at 2%nat le_t_n.

(* ... which restricts on the three generating steps to the three morphisms. / ... 将三个生成步骤限制在三个态射上。 *)
Theorem Functor_of_Triple_step0 {C : Category} (X : nat → C)
  (f0 : X 0%nat ~> X 1%nat) (f1 : X 1%nat ~> X 2%nat) (f2 : X 2%nat ~> X 3%nat) :
  fmap[Functor_of_Triple X f0 f1 f2] (ord_step ord3_0) ≈ f0.
Proof. exact (Functor_of_Steps_step (three_steps X f0 f1 f2) ord3_0). Qed.

Theorem Functor_of_Triple_step1 {C : Category} (X : nat → C)
  (f0 : X 0%nat ~> X 1%nat) (f1 : X 1%nat ~> X 2%nat) (f2 : X 2%nat ~> X 3%nat) :
  fmap[Functor_of_Triple X f0 f1 f2] (ord_step ord3_1) ≈ f1.
Proof. exact (Functor_of_Steps_step (three_steps X f0 f1 f2) ord3_1). Qed.

Theorem Functor_of_Triple_step2 {C : Category} (X : nat → C)
  (f0 : X 0%nat ~> X 1%nat) (f1 : X 1%nat ~> X 2%nat) (f2 : X 2%nat ~> X 3%nat) :
  fmap[Functor_of_Triple X f0 f1 f2] (ord_step ord3_2) ≈ f2.
Proof. exact (Functor_of_Steps_step (three_steps X f0 f1 f2) ord3_2). Qed.

(* And conversely every diagram of shape 4 arises this way. / 反过来，形状为 4 的每个图都是这样产生的。 *)
Corollary shape_4_from_diagram {C : Category} (F : _4 ⟶ C) :
  Functor_of_Steps (steps_of_functor F) ≈ F.
Proof. exact (Functor_of_Steps_of_Functor F). Qed.

(* The composites are forced, and every triangle in a shape-4 diagram commutes automatically: the source is thin, so any two parallel arrows of [_4] are equal and have the same image. / 复合是强制的，并且形状-4 图中的每个三角形都会自动交换：源是薄的，所以 [_4] 的任意两条平行箭头是相等的，并且具有相同的像。 *)
Theorem ord_4_commutes {C : Category} (F : _4 ⟶ C) (x y : Ord_obj 4)
  (f g : @hom (Ordinal 4) x y) : fmap[F] f ≈ fmap[F] g.
Proof. now rewrite (le_t_irr f g). Qed.

Theorem ord_4_triangle {C : Category} (F : _4 ⟶ C) (x y z : Ord_obj 4)
  (f : @hom (Ordinal 4) x y) (g : @hom (Ordinal 4) y z)
  (h : @hom (Ordinal 4) x z) :
  fmap[F] g ∘ fmap[F] f ≈ fmap[F] h.
Proof.
  rewrite <- fmap_comp.
  apply ord_4_commutes.
Qed.
