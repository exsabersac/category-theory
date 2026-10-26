Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.FinSet.

Require Import Coq.Vectors.Fin.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

(* * * Simplex, the simplicial category Δ / * * Simplex，单纯形范畴 Δ *)

(*
 nLab:      https://ncatlab.org/nlab/show/simplex+category
 Wikipedia: https://en.wikipedia.org/wiki/Simplicial_category
 Book:      Mac Lane, “Categories for the Working Mathematician”,
 2nd ed., §I.2 (p. 12) and §VII.5, “The Simplicial Category”

 The simplicial category: objects are the natural numbers, with [n]
 standing for the canonical n-element ordinal [Fin.t n] carried by its
 linear order, and the morphisms [m ~> n] are the ORDER-PRESERVING
 functions [Fin.t m → Fin.t n].  A morphism is a function together with
 a monotonicity witness; the hom-setoid compares only the FUNCTION part,
 pointwise, exactly as Instance/FinSet.v compares its morphisms
 through [fun_setoid].  The witness is proof data carried along, never
 compared — two morphisms with the same underlying function are equal in
 this category whatever their monotonicity proofs.

 WHICH Δ.  This is the “algebraist's Δ”, which includes the empty
 ordinal [0]: the objects are ALL the finite ordinals, so what is built
 here is also called the AUGMENTED simplex category.  This is Mac Lane's
 Δ — §I.2 (p. 12) puts the finite ordinals and their monotone maps among
 the first examples of a category, and §VII.5 develops Δ with objects
 the finite ordinals indexed by n ∈ ℕ, the empty one among them.  It is
 the variant for which Δ is the free monoidal category containing a
 monoid, with [0] the tensor unit, which is what makes including [0]
 worth the trouble.  The “topologist's Δ” drops [0], keeping only the
 nonempty ordinals, because a simplex has at least one vertex; that is
 the shape category of simplicial sets proper, it is the full
 subcategory of this one on the positive naturals, and it is not
 separately built here.  Both conventions are in print under the name Δ,
 so the reading is stated rather than assumed.

 WHAT IS AND IS NOT PROVEN HERE.  The category, the inclusion into
 FinSet with faithfulness and a witnessed statement of non-fullness, the
 face and degeneracy generators, and ALL FIVE simplicial identities are
 proven below.  What is NOT proven is the converse, generating half of
 Mac Lane's §VII.5 theorem: that the faces and degeneracies GENERATE Δ,
 and that the five identities are a complete set of relations presenting
 it.  That is the Eilenberg–Zilber normal-form argument (every morphism
 of Δ factors uniquely as a composite of degeneracies followed by a
 composite of faces), and it is deferred; nothing below depends on it,
 and no statement below is weakened by its absence.  Simplicial sets
 (presheaves on this category), the nerve, and geometric realization are
 likewise out of scope. 

 --------
 nLab：       https://ncatlab.org/nlab/show/simplex+category
 Wikipedia：  https://en.wikipedia.org/wiki/Simplicial_category
 书籍：      Mac Lane, 《为工作数学家准备的范畴论》，
 第二版，§I.2（第12页）和 §VII.5，“单纯形范畴”

 单纯形范畴：对象是自然数，[n] 代表由其线性顺序承载的规范 n 元序数 [Fin.t n]，
 而态射 [m ~> n] 是保持顺序的函数 [Fin.t m → Fin.t n]。态射是一个带有单调性证明的函数；
 同态集族仅比较函数部分，逐点比较，正如 Instance/FinSet.v 通过 [fun_setoid] 比较其态射一样。
 该证明数据随函数携带，从不参与比较——在该范畴中，两个具有相同底层函数的态射无论其单调性证明如何都是相等的。哪个 Δ。这是“代数家的 Δ”，包括空序数 [0]：对象是所有有限序数，因此这里构建的也被称为增强单体范畴。这是 Mac Lane 的 Δ——§I.2（第12页）将有限序数及其单调映射列为范畴的首批例子之一，而 §VII.5 用对象为有限序数（由 n ∈ ℕ 索引，其中包括空序数）的方式发展了 Δ。这是 Δ 作为包含一个幺半群的自由幺半范畴的变体，其中 [0] 是张量单位，这正是让包括 [0] 值得费事的原因。“拓扑学家的 Δ” 放弃了 [0]，只保留非空序数，因为单形至少有一个顶点；那是单纯集合的形状范畴，它是此范畴在正整数上的全子范畴，这里没有单独构建。两种约定都以 Δ 的名义出版，因此阅读是陈述的，而不是假设的。这里证明了什么和没有证明什么。该范畴、以忠实性包含到 FinSet 中及非满性有证声称的语句、面与退化生成元，以及所有五个单纯形恒等式均在下文中得到证明。尚未证明的是其逆命题，即生成 Mac Lane §VII.5 定理的一半：面和退化生成 Δ，并且这五个恒等式是呈现它的完整关系集合。那是 Eilenberg–Zilber 正规形式论证（Δ 的每个态射可以唯一分解为先退化再复合面的形式），此部分被推迟；下文的内容不依赖于它，其缺失也不会削弱下文的任何陈述。单纯集（该范畴上的预层）以及神经、几何实现同样不在讨论范围内。
*)

(*
 Why Δ, and where it leads

 nLab: https://ncatlab.org/nlab/show/simplex+category
 nLab: https://ncatlab.org/nlab/show/simplicial+set

 Δ is the shape category of homotopy theory.  Presheaves on its full
 subcategory of NONEMPTY ordinals are the simplicial sets — presheaves
 on the whole of the category built here, empty ordinal included, are
 the AUGMENTED simplicial sets — and the passage between simplicial sets
 and topological spaces, geometric realization on the left and the
 singular complex on the right, is the adjunction that makes them a
 combinatorial model for spaces.  That adjunction is the reason Kan
 wrote “Adjoint functors” (1958) in the first place: as
 Theory/Kan/Extension.v records, Kan introduced adjoints “to
 codify the formal properties of the passage between spaces and
 simplicial sets”, and Theory/Kan/Extension.v adds that geometric
 realization is “the left Kan extension of a cosimplicial space along
 the Yoneda embedding, the nerve its restricted-Yoneda right adjoint”.
 Structure/Coend.v records the same realization as a single coend.
 Each of those three passages is prose about a category that, until now,
 the library did not have; this file supplies it.

 The algebraic reading is equally load-bearing.  Δ is the free monoidal
 category containing a monoid: ordinal addition is the tensor, [0] is
 the unit, and [1] carries the universal monoid, whose multiplication is
 the unique map [2 ~> 1] and whose unit is the unique map [0 ~> 1]
 (nLab, “simplex category”).  Consequently a monoid in any monoidal
 category is a strict monoidal functor out of Δ, which is why Mac Lane
 places §VII.5 inside the chapter on monoids rather than in a chapter on
 topology.  Dually Δ^op is the walking comonoid, and the bar resolution
 of a monad — the simplicial object whose face maps are built from the
 multiplication and whose degeneracies are built from the unit — is
 exactly a functor out of it; Comonad/Core.v cites that
 “simplicial bar resolution of a comonad” as founding cotriple
 cohomology (Barr–Beck, Springer LNM 80, 1969).

 Within this library Δ arrives as a subcategory of the skeletal finite
 sets already in tree.  Instance/FinSet.v anticipates precisely
 this, noting “the simplex category Δ embedding into FinSet” in its
 discussion of Grandis's symmetric simplicial sets (“Finite sets and
 symmetric simplicial sets”, Theory and Applications of Categories 8,
 2001); the inclusion [Simplex_FinSet] below realizes that remark, and the
 accompanying non-fullness result measures the gap — FinSet has all
 functions between finite ordinals, Δ keeps only the monotone ones, and
 the swap on the two-element set is the smallest witness that the
 difference is real.

 NOTE on names: the name this category usually gets is Δ, and THAT is the
 collision that matters -- [Δ] in this tree is the diagonal functor
 (Functor/Diagonal.v, with notations Δ[J](c) and Δ(c)).
 Lowercase [delta] is also taken, by comonoid comultiplication
 (Theory/Algebra/Comonoid.v), though capitalization would keep them
 apart.  The generators here are therefore [sface] and [sdegen] at the
 categorical level and [fin_skip], [fin_dup] at the level of underlying
 functions, and the category itself is [Simplex].  (No ASCII [Delta]
 identifier exists in tree, and none is introduced -- but that spelling
 was never the live conflict.) 

 --------
 为什么是Δ，它会引向何处

 nLab:  https://ncatlab.org/nlab/show/simplex+category 
 nLab:  https://ncatlab.org/nlab/show/simplicial+setΔ 是同伦论的形状范畴。其非空序数的全子范畴上的预层是单纯集合 —— 在此建立的整个范畴上（包括空序数）的预层是增广单纯集合 —— 而单纯集合和拓扑空间之间的转换，即左侧的几何 realiz 以及右侧的奇异复形，是使它们成为空间组合模型的伴随关系。这个伴随是 Kan 最初撰写《Adjoint functors》（1958 年）的原因：正如 Theory/Kan/Extension.v 所记录的，Kan 引入伴随“是为了编码空间与单纯复形之间过渡的形式性质”，并且 Theory/Kan/Extension.v 还补充说几何实现是“沿 Yoneda 嵌入的余单纯空间的左 Kan 延伸，其神经是其受限 Yoneda 的右伴随”。Structure/Coend.v 以单个共端记录了相同的实现。上述三个段落都是关于一个类别的散文，而在此之前库中并未拥有该类别；该文件提供了它。代数的解读同样具有承重作用。Δ 是包含一个幺半群的自由幺半范畴：序数加法是张量，[0] 是单位，[1] 携带通用幺半群，其乘法是唯一映射 [2 ~> 1]，单位是唯一映射 [0 ~> 1]（nLab，“单纯形范畴”）。因此，任何幺半范畴中的幺半群都是从 Δ 出来的严格幺半范函子，这就是为什么 Mac Lane 将 §VII.5 放在关于幺半群的章节中，而不是放在拓扑章节中的原因。对偶地，Δ^op 是行走余单子，而一个单子的 bar 分解——其面映射由乘法构建，其退化映射由单位构建——正好是一个从它出发的函子；Comonad/Core.v 引用“余单子的单纯条形分解”作为构建余三元同调的基础（Barr–Beck，Springer LNM 80，1969）。在这个库中，Δ 作为已经在 tree 中的骨架有限集合的一个子范畴出现。Instance/FinSet.v 正是预见到了这一点，在讨论 Grandis 的对称单纯集合（“有限集合与对称单纯集合”，《范畴理论及其应用》8, 2001）时，指出了“单纯范畴 Δ 嵌入到 FinSet 中”；下面的包含 [Simplex_FinSet] 实现了这一注释，随附的非满性结果衡量了差距——FinSet 拥有有限序数之间的所有函数，而 Δ 只保留单调函数，而在两元素集合上的交换是最小的证据，表明这种差异是真实存在的。关于名称的注意事项：这个类别通常被命名为 Δ，而真正重要的碰撞是那个——在这棵树中 [Δ] 是对角函子（Functor/Diagonal.v，记法为 Δ [J] (c) 和 Δ(c)）。小写的 [delta] 也被使用，由于余单子复乘（Theory/Algebra/Comonoid.v），虽然大写会将它们区分开。因此，这里的生成元在范畴层次上是 [sface] 和 [sdegen]，在底层函数层次上是 [fin_skip]、[fin_dup]，而类别本身是 [Simplex]。（树中不存在 ASCII [Delta] 标识符，也没有引入它——但这种拼写从未成为实际冲突。）
*)

(*
   * ** The order on a finite ordinal

   Monotonicity is stated through [Fin.to_nat] and the standard library's
   order on [nat], rather than through a bespoke inductive relation.  Two
   reasons.  First, a [Prop]-valued relation is adequate HERE, unlike in
   Instance/Omega.v, whose [le_t] must be [Type]-valued precisely because
   there the order proofs ARE the morphisms and must eliminate into the
   [Type]-valued hom-sets of an arbitrary target category; here the order
   proof is a side condition on a morphism, is never eliminated into, and
   is never compared, so [Prop] costs nothing.  Second, routing through
   [Fin.to_nat] puts every obligation in reach of [lia] after a single
   rewrite, which is what makes the simplicial identities tractable
   below. 

   --------
   * ** 有限序数的序

   单调性是通过 [Fin.to_nat]  和标准库中 [nat] 的顺序来表述的，而不是通过定制的归纳关系来表述。有两个原因。第一，在这里 [Prop] 值的关系是足够的，不像在 Instance/Omega.v 中，其 [le_t] 必须是 [Type] 值的，正是因为在那里顺序证明就是态射，必须消元到任意目标范畴的 [Type] 值的同态集合；而在这里顺序证明只是态射的附加条件，从不进行消元，也从不进行比较，因此 [Prop] 没有任何代价。第二，通过 [Fin.to_nat] 转路可以在一次重写之后让 [lia] 访问每个义务，这就是使下面单纯形恒等式可处理的原因。
*)

Definition fin_nat {n : nat} (i : Fin.t n) : nat := proj1_sig (Fin.to_nat i).

Definition fin_bound {n : nat} (i : Fin.t n) : Nat.lt (fin_nat i) n :=
  proj2_sig (Fin.to_nat i).

Definition fin_le {n : nat} (i j : Fin.t n) : Prop :=
  Nat.le (fin_nat i) (fin_nat j).

Lemma fin_nat_inj {n : nat} (i j : Fin.t n) : fin_nat i = fin_nat j → i = j.
Proof. apply Fin.to_nat_inj. Qed.

Lemma fin_nat_FS {n : nat} (i : Fin.t n) : fin_nat (Fin.FS i) = S (fin_nat i).
Proof. unfold fin_nat; simpl; now destruct (Fin.to_nat i). Qed.

Lemma fin_nat_F1 {n : nat} : fin_nat (@Fin.F1 n) = 0%nat.
Proof. reflexivity. Qed.

(*
   * ** Monotone maps

   A morphism of Δ is a function on ordinals together with a proof that
   it preserves the order.  The coercion lets a [Monotone m n] be applied
   directly to an element. 

   --------
   * ** 单调映射

   Δ 的一个态射是一个关于序数的函数，同时附带一个证明，证明它保持顺序。强制转换允许直接将一个 [Monotone m n] 应用于一个元素。
*)

Record Monotone (m n : nat) : Type := {
  mono_map :> Fin.t m → Fin.t n;
  mono_ord : ∀ i j : Fin.t m, fin_le i j → fin_le (mono_map i) (mono_map j)
}.

Arguments mono_map {m n} _ _.
Arguments mono_ord {m n} _ {i j} _.

(*
   * ** The category

   Identity and composition of functions preserve monotonicity, so the
   underlying-function category structure of Instance/FinSet.v lifts
   verbatim; the equivalence, being pointwise equality of the function
   parts, makes composition a congruence for the same reason it does
   there. 

   --------
   * ** 类别

   函数的恒等和复合保持单调性，因此 Instance/FinSet.v 的基础函数类别结构可以逐字提升；而等价性，由于函数部分的逐点相等，使得复合在此处也因同样的原因成为合同映射。
*)

Program Definition Simplex : Category := {|
  obj := nat;
  hom := Monotone;
  homset := fun m n =>
    {| equiv := fun f g => ∀ i, mono_map f i = mono_map g i |};
  id := fun _ => {| mono_map := fun i => i |};
  compose := fun _ _ _ f g =>
    {| mono_map := fun i => mono_map f (mono_map g i) |}
|}.
Next Obligation.
  (* Pointwise equality of function parts is an equivalence. / 函数部分的逐点相等是一种等价关系。 *)
  constructor.
  - intros f i; reflexivity.
  - intros f g Hfg i; symmetry; apply Hfg.
  - intros f g h Hfg Hgh i; transitivity (mono_map g i);
      [ apply Hfg | apply Hgh ].
Qed.
Next Obligation.
  (* A composite of monotone maps is monotone. / 单调映射的复合是单调的。 *)
  now apply mono_ord, mono_ord.
Qed.
Next Obligation.
  (* Composition respects pointwise equality in both arguments. / 组合在两个参数中都尊重逐点相等性。 *)
  intros f f' Hf g g' Hg i; simpl.
  rewrite (Hg i); apply Hf.
Qed.

(*
   * ** The inclusion into FinSet

   Forgetting monotonicity is a functor into the skeletal finite sets of
   Instance/FinSet.v.  It is the identity on objects, so it is wide;
   it is injective on hom-sets, so it is faithful; and it is not full,
   for which see [Simplex_FinSet_not_Full] below. 

   --------
   * ** 包含到 FinSet 中

   忘记单调性是到 Instance/FinSet.v 中骨架有限集合的一个函子。它在对象上是恒等的，所以它是宽的；它在 Hom 集上是单射的，所以它是忠实的；但它不是满射的，详见下面的 [Simplex_FinSet_not_Full]。
*)

Program Definition Simplex_FinSet : Simplex ⟶ FinSet := {|
  fobj := fun n => n;
  fmap := fun m n f => mono_map f
|}.

(*
 Wide: the inclusion is the identity on objects, so every object of
 FinSet is hit, and hit exactly once. 

 --------
 宽：包含在对象上的映射是恒等映射，因此 FinSet 的每个对象都被覆盖，并且只被覆盖一次。
*)
Lemma Simplex_FinSet_wide (n : nat) : Simplex_FinSet n = n.
Proof. reflexivity. Qed.

(*
 Faithful: the hom-setoid of [Simplex] compares exactly the data the
 inclusion retains, so its hom-maps are injective on the nose. 

 --------
 忠实：[Simplex] 的同态集等价比较了包含保留的数据，因此它的同态映射是严格单射的。
*)
Lemma Simplex_fmap_inj {m n : nat} (f g : @hom Simplex m n) :
  (∀ i, mono_map f i = mono_map g i) → f ≈ g.
Proof. intro H; exact H. Qed.

#[export] Program Instance Simplex_FinSet_Faithful : Faithful Simplex_FinSet.

(*
   * ** Not full

   The inclusion is a wide subcategory that is genuinely non-full: FinSet
   has morphisms between ordinals that Δ does not.  The smallest witness
   is the swap on the two-element set, which is a bijection [Fin.t 2 →
   Fin.t 2] and therefore a morphism [2 ~> 2] of FinSet, but reverses the
   order and so is not the image of any morphism of [Simplex].

   [Full] (Theory/Functor.v) packages fullness as a chosen preimage
   [prefmap] together with [fmap_sur], the proof that it is a section of
   [fmap].  Given such a preimage for the swap, its monotonicity applied
   to [0 ≤ 1] would give [1 ≤ 0] in the ordinal [2]. 

   --------
   * ** 不是满的

   包含是一个真正非满的广泛子类别：FinSet 在Δ没有的序数之间有态射。最小的例子是在两元素集合上的交换，它是一个双射 [Fin.t 2 → Fin.t 2]，因此是 FinSet 的一个态射 [2 ~> 2]，但它会颠倒顺序，因此不是 [Simplex] 中任何态射的像。

   [Full]（Theory/Functor.v）将满性封装为一个选定的原像 [prefmap] 以及 [fmap_sur]，即证明它是 [fmap] 的一个节。对于交换的原像，其单调性应用于 [0 ≤ 1] 将在序数 [2] 中得到 [1 ≤ 0]。
*)

Definition fin2_swap (i : Fin.t 2%nat) : Fin.t 2%nat :=
  Fin.caseS' i (fun _ => Fin.t 2%nat) (Fin.FS Fin.F1) (fun _ => Fin.F1).

Example fin2_swap_F1 : fin2_swap Fin.F1 = Fin.FS Fin.F1 := eq_refl.
Example fin2_swap_FS : fin2_swap (Fin.FS Fin.F1) = Fin.F1 := eq_refl.

(*
 The sharp content, independent of how fullness is packaged: no
 morphism of [Simplex] has the swap as its underlying function.
 Monotonicity applied to 0 ≤ 1 would give swap 0 ≤ swap 1, i.e. 1 ≤ 0. 

 --------
 尖锐内容，与充实的包装方式无关：没有  [Simplex]  的同态映射以交换作为其基础函数。单调性应用于 0 ≤ 1 会得到交换 0 ≤ 交换 1，即 1 ≤ 0。
*)
Lemma no_monotone_swap (f : @hom Simplex 2%nat 2%nat) :
  (∀ i, mono_map f i = fin2_swap i) → False.
Proof.
  intro Hf.
  assert (Hle : fin_le (mono_map f Fin.F1) (mono_map f (Fin.FS Fin.F1))).
  { apply mono_ord; unfold fin_le, fin_nat; simpl; lia. }
  rewrite (Hf Fin.F1), (Hf (Fin.FS Fin.F1)) in Hle.
  unfold fin_le, fin_nat in Hle; simpl in Hle; lia.
Qed.

(*
 Non-fullness follows: a [Full] structure would supply exactly such a
 morphism as the chosen preimage of the swap. 

 --------
 非完全性随之而来：一个 [Full] 结构将恰好提供这样的一个态射，作为交换的选定原像。
*)
Lemma Simplex_FinSet_not_Full : Full Simplex_FinSet → False.
Proof.
  intro H.
  pose (g := fin2_swap
             : @hom FinSet (Simplex_FinSet 2%nat) (Simplex_FinSet 2%nat)).
  exact (no_monotone_swap (@prefmap _ _ _ H 2%nat 2%nat g)
                          (@fmap_sur _ _ _ H 2%nat 2%nat g)).
Qed.

(*
   * ** Faces and degeneracies

   The generators of Δ.  On underlying functions, the i-th face
   [fin_skip i] is the monotone injection [Fin.t n → Fin.t (S n)] whose
   image omits [i], and the i-th degeneracy [fin_dup i] is the monotone
   surjection [Fin.t (S n) → Fin.t n] that takes the value [i] twice.
   [fin_weak] is the order-preserving inclusion [Fin.t n → Fin.t (S n)]
   that keeps the numeral fixed; it is how an index that the textbook
   identities reuse at two consecutive ordinals is transported.

   All three are built through [Fin.of_nat_lt] from an explicit numeral,
   rather than by structural recursion on [Fin.t].  The point is that
   [Fin.to_nat_of_nat] then computes [fin_nat] of each generator in one
   rewrite, turning every law below into [nat] arithmetic that [lia]
   discharges — where a recursive definition would need a nested
   [Fin.caseS'] induction for each of the five identities.  The terms
   still evaluate on closed input, because [Fin.of_nat_lt] recurses on
   the numeral and the ordinal, never on the bound proof (see the
   computing Examples below). 

   --------
   * ** 面与退化

   Δ 的生成元。在底层函数上，第 i 个面
   [fin_skip i] 是单调注入 [Fin.t n → Fin.t (S n)]，其像省略了 [i]；第 i 个退化 [fin_dup i] 是单调满射 [Fin.t (S n) → Fin.t n]，它将值 [i] 重复两次。
   [fin_weak] 是保持顺序的包含 [Fin.t n → Fin.t (S n)]，它保持数字不变；这是教科书恒等式在两个连续序数中重用索引的传递方式。这三者都是通过 [Fin.of_nat_lt] 从一个明确的数字构建的，而不是通过对 [Fin.t] 的结构递归。重点是 [Fin.to_nat_of_nat] 随后在一次重写中计算每个生成元的 [fin_nat]，将下面的每条定律都转换为 [nat] 算术，而 [lia] 负责执行 — 如果使用递归定义，则需要对每一个五个恒等式进行嵌套的 [Fin.caseS'] 归纳。术语在封闭输入上仍然可以求值，因为 [Fin.of_nat_lt] 递归于数字和序数，从不递归于绑定的证明（参见下面的计算示例）。
*)

Program Definition fin_weak {n : nat} (i : Fin.t n) : Fin.t (S n) :=
  Fin.of_nat_lt (p := fin_nat i) _.
Next Obligation. pose proof (fin_bound i); lia. Qed.

Program Definition fin_skip {n : nat} (i : Fin.t (S n)) (x : Fin.t n) :
  Fin.t (S n) :=
  Fin.of_nat_lt
    (p := if Nat.ltb (fin_nat x) (fin_nat i)
          then fin_nat x else S (fin_nat x)) _.
Next Obligation.
  pose proof (fin_bound x); destruct (Nat.ltb (fin_nat x) (fin_nat i)); lia.
Qed.

Program Definition fin_dup {n : nat} (i : Fin.t n) (x : Fin.t (S n)) :
  Fin.t n :=
  Fin.of_nat_lt
    (p := if Nat.leb (fin_nat x) (fin_nat i)
          then fin_nat x else Nat.pred (fin_nat x)) _.
Next Obligation.
  pose proof (fin_bound i); pose proof (fin_bound x).
  destruct (Nat.leb (fin_nat x) (fin_nat i)) eqn:E.
  - apply Nat.leb_le in E; lia.
  - apply Nat.leb_gt in E; lia.
Qed.

Lemma fin_nat_weak {n : nat} (i : Fin.t n) : fin_nat (fin_weak i) = fin_nat i.
Proof. unfold fin_nat, fin_weak; now rewrite Fin.to_nat_of_nat. Qed.

Lemma fin_nat_skip {n : nat} (i : Fin.t (S n)) (x : Fin.t n) :
  fin_nat (fin_skip i x)
    = if Nat.ltb (fin_nat x) (fin_nat i) then fin_nat x else S (fin_nat x).
Proof. unfold fin_nat, fin_skip; now rewrite Fin.to_nat_of_nat. Qed.

Lemma fin_nat_dup {n : nat} (i : Fin.t n) (x : Fin.t (S n)) :
  fin_nat (fin_dup i x)
    = if Nat.leb (fin_nat x) (fin_nat i)
      then fin_nat x else Nat.pred (fin_nat x).
Proof. unfold fin_nat, fin_dup; now rewrite Fin.to_nat_of_nat. Qed.

(*
 The uniform decision procedure for every law about the generators:
 reduce the goal to an equation between ordinals, push each generator
 through to its numeral, split every boolean comparison, and close the
 resulting arithmetic with [lia].  Rewriting is repeated after each
 split because the comparisons of one generator have the numerals of
 another nested inside them. 

 --------
 关于生成元的每条定律的统一判定程序：将目标化简为序数之间的方程，将每个生成元推导到它的数字形式，拆分每个布尔比较，并用 [lia] 完成由此产生的算术。每次拆分后都重复重写，因为一个生成元的比较中嵌入了另一个生成元的数字。
*)
Ltac fin_arith :=
  apply fin_nat_inj;
  repeat (rewrite ?fin_nat_skip, ?fin_nat_dup, ?fin_nat_weak, ?fin_nat_FS);
  repeat (match goal with
          | [ |- context[Nat.ltb ?a ?b] ] => destruct (Nat.ltb_spec a b)
          | [ |- context[Nat.leb ?a ?b] ] => destruct (Nat.leb_spec a b)
          end;
          rewrite ?fin_nat_skip, ?fin_nat_dup, ?fin_nat_weak, ?fin_nat_FS);
  lia.

Lemma fin_weak_monotone {n : nat} (x y : Fin.t n) :
  fin_le x y → fin_le (fin_weak x) (fin_weak y).
Proof. unfold fin_le; now rewrite !fin_nat_weak. Qed.

Lemma fin_skip_monotone {n : nat} (i : Fin.t (S n)) (x y : Fin.t n) :
  fin_le x y → fin_le (fin_skip i x) (fin_skip i y).
Proof.
  unfold fin_le; rewrite !fin_nat_skip.
  destruct (Nat.ltb_spec (fin_nat x) (fin_nat i));
    destruct (Nat.ltb_spec (fin_nat y) (fin_nat i)); lia.
Qed.

Lemma fin_dup_monotone {n : nat} (i : Fin.t n) (x y : Fin.t (S n)) :
  fin_le x y → fin_le (fin_dup i x) (fin_dup i y).
Proof.
  unfold fin_le; rewrite !fin_nat_dup.
  destruct (Nat.leb_spec (fin_nat x) (fin_nat i));
    destruct (Nat.leb_spec (fin_nat y) (fin_nat i)); lia.
Qed.

(* The generators as morphisms of [Simplex]. / 生成元作为 [Simplex] 的态射。 *)

Definition sface {n : nat} (i : Fin.t (S n)) : @hom Simplex n (S n) :=
  {| mono_map := fin_skip i; mono_ord := @fin_skip_monotone n i |}.

Definition sdegen {n : nat} (i : Fin.t n) : @hom Simplex (S n) n :=
  {| mono_map := fin_dup i; mono_ord := @fin_dup_monotone n i |}.

(*
 The generators evaluate on closed input, by [eq_refl].  The values are
 chosen to pin down the intended combinatorics rather than merely to
 witness that something reduces: δ_1 : 2 ~> 3 is checked at BOTH points
 of its domain, so the Examples certify that its image omits exactly the
 value 1, and σ_1 : 3 ~> 2 is checked at all three points, so they
 certify that it takes the value 1 exactly twice. 

 --------
 生成器在封闭输入上进行评估，由 [eq_refl] 给出。选择这些值是为了确定预期的组合结构，而不仅仅是为了证明某些东西可以约化：δ_1 : 2 ~> 3 在其域的两个点上都进行了检查，因此示例证明其像恰好省略值 1；而 σ_1 : 3 ~> 2 在所有三个点上都进行了检查，因此它们证明该函数恰好取值 1 两次。
*)

(* δ_1 : 2 ~> 3 omits the value 1 — it sends 0 ↦ 0 and 1 ↦ 2. / δ_1 : 2 ~> 3 忽略值 1 — 它将 0 ↦ 0 且 1 ↦ 2。 *)
Example sface_skips_at_0 :
  fin_nat (mono_map (@sface 2%nat (Fin.FS Fin.F1)) Fin.F1) = 0%nat := eq_refl.

Example sface_skips_at_1 :
  fin_nat (mono_map (@sface 2%nat (Fin.FS Fin.F1)) (Fin.FS Fin.F1))
    = 2%nat := eq_refl.

(* σ_1 : 3 ~> 2 repeats the value 1 — it sends 0 ↦ 0, 1 ↦ 1 and 2 ↦ 1. / σ_1 : 3 ~> 2 重复值 1 — 它将 0 映射到 0，1 映射到 1，2 映射到 1。 *)
Example sdegen_repeats_at_0 :
  fin_nat (mono_map (@sdegen 2%nat (Fin.FS Fin.F1)) Fin.F1) = 0%nat := eq_refl.

Example sdegen_repeats_at_1 :
  fin_nat (mono_map (@sdegen 2%nat (Fin.FS Fin.F1)) (Fin.FS Fin.F1))
    = 1%nat := eq_refl.

Example sdegen_repeats_at_2 :
  fin_nat (mono_map (@sdegen 2%nat (Fin.FS Fin.F1)) (Fin.FS (Fin.FS Fin.F1)))
    = 1%nat := eq_refl.

(*
   * ** The five simplicial identities

   The nLab (“simplex category”) states them, in the cosimplicial form
   appropriate to Δ itself, as

   (1)  δ_j ∘ δ_i = δ_i ∘ δ_{j-1}        for i < j
   (2)  σ_j ∘ σ_i = σ_i ∘ σ_{j+1}        for i ≤ j
   (3)  σ_j ∘ δ_i = δ_i ∘ σ_{j-1}        for i < j
   (4)  σ_j ∘ δ_j = id = σ_j ∘ δ_{j+1}
   (5)  σ_j ∘ δ_i = δ_{i-1} ∘ σ_j        for i > j+1

   Subtraction on indices does not survive the passage to [Fin.t], where
   an index carries the size of the ordinal it indexes.  Each identity is
   therefore reindexed to its equivalent shift-free form, substituting
   [j := j+1] in (1) and (3) and [i := i+1] in (5), which replaces every
   [_-1] by an increment on the other side.  The reindexed (1) below is
   not a departure from the book: it is Mac Lane's own equation (11) of
   §VII.5 (delta_i delta_j = delta_{j+1} delta_i for i <= j) on the nose,
   and the reindexed (2)-(5) likewise match his (12)-(13):

   (1)  δ_i ∘ δ_j = δ_{j+1} ∘ δ_i        for i ≤ j
   (2)  σ_j ∘ σ_i = σ_i ∘ σ_{j+1}        for i ≤ j
   (3)  σ_{j+1} ∘ δ_i = δ_i ∘ σ_j        for i ≤ j
   (4)  σ_j ∘ δ_j = id = σ_j ∘ δ_{j+1}
   (5)  σ_j ∘ δ_{i+1} = δ_i ∘ σ_j        for j < i

   In these statements an index reused at two consecutive ordinals is
   transported by [fin_weak] (same numeral, next ordinal), and an index
   incremented by one is [Fin.FS] — so the side conditions are stated on
   [fin_nat], which both transports respect ([fin_nat_weak],
   [fin_nat_FS]).  All five are proven. 

   --------
   * ** 五个单纯形恒等式

   nLab（“单纯形范畴”）以余单纯形形式给出了它们，这种形式适用于 Δ 本身，如下所示：

   (1)  δ_j ∘ δ_i = δ_i ∘ δ_{j-1}        对于 i < j
   (2)  σ_j ∘ σ_i = σ_i ∘ σ_{j+1}        对于 i ≤ j
   (3)  σ_j ∘ δ_i = δ_i ∘ σ_{j-1}        对于 i < j
   (4)  σ_j ∘ δ_j = id = σ_j ∘ δ_{j+1}
   (5)  σ_j ∘ δ_i = δ_{i-1} ∘ σ_j        对于 i > j+1在指数上的减法不能在传递到 [Fin.t] 时保留，其中一个指数表示它所索引的序数的大小。因此，每个恒等式都被重新索引为其等效的无移位形式，在 (1) 和 (3) 中替换为 [j := j+1]，在 (5) 中替换为 [i := i+1]，这会将每个 [_-1] 替换为另一侧的增量。下面重新索引的 (1) 并不偏离书本：它正是 Mac Lane 在 §VII.5 中的方程 (11)（delta_i delta_j = delta_{j+1} delta_i 对于 i ≤ j），重新索引的 (2)-(5) 同样匹配他的 (12)-(13)：

   (1)  δ_i ∘ δ_j = δ_{j+1} ∘ δ_i        对于 i ≤ j
   (2)  σ_j ∘ σ_i = σ_i ∘ σ_{j+1}        对于 i ≤ j
   (3)  σ_{j+1} ∘ δ_i = δ_i ∘ σ_j        对于 i ≤ j
   (4)  σ_j ∘ δ_j = id = σ_j ∘ δ_{j+1}
   (5)  σ_j ∘ δ_{i+1} = δ_i ∘ σ_j        对于 j < i在这些语句中，一个在两个连续序数中重复使用的索引由 [fin_weak]（相同数字，下一个序数）传递，而索引增加一则是 [Fin.FS]——所以附加条件是在 [fin_nat] 上说明的，这两个传递都遵守（[fin_nat_weak]，[fin_nat_FS]）。五个都已被证明。
*)

(* (1) δ_i ∘ δ_j = δ_{j+1} ∘ δ_i for i ≤ j. / (1) δ_i ∘ δ_j = δ_{j+1} ∘ δ_i 对于 i ≤ j。 *)
Theorem simplicial_face_face {n : nat} (i j : Fin.t (S n)) (H : fin_le i j) :
  sface (fin_weak i) ∘ sface j ≈ sface (Fin.FS j) ∘ sface i.
Proof. intro x; simpl; unfold fin_le in H; fin_arith. Qed.

(* (2) σ_j ∘ σ_i = σ_i ∘ σ_{j+1} for i ≤ j. / (2) σ_j ∘ σ_i = σ_i ∘ σ_{j+1} 对于 i ≤ j。 *)
Theorem simplicial_degen_degen {n : nat} (i j : Fin.t n) (H : fin_le i j) :
  sdegen j ∘ sdegen (fin_weak i) ≈ sdegen i ∘ sdegen (Fin.FS j).
Proof. intro x; simpl; unfold fin_le in H; fin_arith. Qed.

(* (3) σ_{j+1} ∘ δ_i = δ_i ∘ σ_j for i ≤ j. / (3) σ_{j+1} ∘ δ_i = δ_i ∘ σ_j 对于 i ≤ j. *)
Theorem simplicial_degen_face_lt {n : nat} (j : Fin.t n) (i : Fin.t (S n))
  (H : Nat.le (fin_nat i) (fin_nat j)) :
  sdegen (Fin.FS j) ∘ sface (fin_weak i) ≈ sface i ∘ sdegen j.
Proof. intro x; simpl; fin_arith. Qed.

(* (4a) σ_j ∘ δ_j = id. *)
Theorem simplicial_degen_face_eq {n : nat} (j : Fin.t n) :
  sdegen j ∘ sface (fin_weak j) ≈ @id Simplex n.
Proof. intro x; simpl; fin_arith. Qed.

(* (4b) σ_j ∘ δ_{j+1} = id. *)
Theorem simplicial_degen_face_succ {n : nat} (j : Fin.t n) :
  sdegen j ∘ sface (Fin.FS j) ≈ @id Simplex n.
Proof. intro x; simpl; fin_arith. Qed.

(* (5) σ_j ∘ δ_{i+1} = δ_i ∘ σ_j for j < i. / (5) 当 j < i 时，σ_j ∘ δ_{i+1} = δ_i ∘ σ_j。 *)
Theorem simplicial_degen_face_gt {n : nat} (j : Fin.t n) (i : Fin.t (S n))
  (H : Nat.lt (fin_nat j) (fin_nat i)) :
  sdegen (fin_weak j) ∘ sface (Fin.FS i) ≈ sface i ∘ sdegen j.
Proof. intro x; simpl; fin_arith. Qed.
