Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.SubobjectClassifier.Natural.
Require Import Category.Structure.Topos.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Topos.
Require Import Category.Theory.Universal.Element.

Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(* * * The contravariant power-set functor on skeletal [FinSet], computably / * * 在骨架 [FinSet] 上的逆变幂集函子，可计算地 *)

(*
 nLab:      https://ncatlab.org/nlab/show/universal+element
 nLab:      https://ncatlab.org/nlab/show/subobject+classifier
 Wikipedia: https://en.wikipedia.org/wiki/Power_set

 Mac Lane asks (CWM 2nd ed., §III.1, Exercise 2, printed p. 59) for a
 universal element of the contravariant power-set functor, and the
 classical answer is the pair ⟨2, {1}⟩.  Riehl states the same example
 (Category Theory in Context, 2nd ed., §2.3 Example 2.3.6, printed
 p. 68) with the emphasis that the universal element is the SUBSET
 {⊤} ∈ P(Ω), an element of the functor's VALUE at Ω, and not the POINT
 ⊤ ∈ Ω, the isomorphism sending f : A ⟶ Ω to the subset f⁻¹(⊤) ⊆ A.
 Awodey runs the correspondence for Sets (Category Theory, §5.3
 Example 5.14, printed pp. 104-106), where the punchline is that it is
 NATURAL in the object.

 ATTRIBUTION.  The section-and-page coordinates above, and the one-line
 summaries of what those passages contain, are reproduced from the
 catalogue entry of the issue this file answers
 (jwiegley/category-theory#311, items maclane:III.1:ex2,
 riehl:2.3:example6, awodey:5.3:example14); the printed texts were not
 consulted while writing the file, so every statement here about their
 content is the issue's characterization rather than a reading of the
 books.  The mathematics stands on its own proofs.

 WHY THIS FILE EXISTS ALONGSIDE Instance/Sets/Powerset/Universal.v.
 That file answers the same exercise over [Sets], where a subset of A
 is a [Prop]-valued predicate on A and is therefore, by construction,
 already a map A ⟶ Ω; the correspondence there is genuine but its
 content is thin, being the single equivalence “membership in {⊤}
 detects truth”.  Here nothing is definitional: the power set of the
 n-element set is the 2^n-element set, subsets are ELEMENTS of it, and
 the passage between a subset and its characteristic map is the digit
 codec of Instance/FinSet/Closed.v.  Both round trips of that codec hold
 at LEIBNIZ equality ([fin_apply_tabulate], [fin_tabulate_apply]), which
 is what lets the universal property below be proved without a single
 setoid manoeuvre, and lets the whole correspondence COMPUTE — the
 acceptance tests at the end are [eq_refl] on closed data.

 WHAT THIS FILE DELIVERS, AND AT WHICH STRENGTH.

 (1) [FinPowerset : FinSet^op ⟶ FinSet] — the contravariant power-set
 functor INSIDE [FinSet], object action n ↦ 2^n, arrow action the
 inverse image.  Both functor laws close at Leibniz equality of
 codes through [fin_tabulate_apply] and [fin_apply_tabulate];
 [FinSet]'s hom-setoid is pointwise [=] ([fun_setoid]), so those
 are the honest statements, not weakenings.

 (2) [FinPowerset_Sets : FinSet^op ⟶ Sets] — the same functor read
 into [Sets], which is the shape [AUniversalElement] requires of
 its [H].  [finpowerset_sets_agrees] records by [eq_refl] that the
 two have the same arrow action, so (2) is (1) retyped and not a
 second construction.

 (3) [FinPowerset_universal_element] — Mac Lane's §III.1 clause, the
 pair ⟨2, {⊤}⟩, through Theory/Universal/Element.v's
 [AUniversalElement].  The universal element is
 [finpow_truth_subset : Fin.t 4], an element of P(2), NOT the
 point [fin_true : Fin.t 2]; the two have different types, and
 Test/ProbePowersetUniversal.v pins the substitution as a type
 error against a positive control.

 (4) Riehl's preimage description, PROVED and not merely asserted:
 [finpow_fmap_is_preimage] says that the i-th digit of
 [P k {⊤}] is [k i] itself, so [finpow_preimage_iff] reads off
 that i belongs to [P k {⊤}] exactly when [k i] is [fin_true] —
 that is, that the functor's action on k applied to the universal
 element IS k⁻¹(⊤).  [finpow_preimage_of_truth] collects the
 digits: pulling {⊤} back along k returns the CODE of k.

 (5) [FinSet_Sub_natural] — Awodey's naturality clause instantiated at
 [FinSet_Classifier]: the subobject presheaf of [FinSet] is
 naturally isomorphic to [Hom(─, 2)].  This is
 Structure/SubobjectClassifier/Natural.v applied, not reproved.

 (6) [FinSet_Sub_powerset] — the two are joined:
 [Sub ≅ FinPowerset_Sets] in [[FinSet^op, Sets]].  So on [FinSet]
 the power-set functor of (2) and the subobject functor of
 Theory/Subobject/Functor.v are the same presheaf, naturally.  The
 middle term is [Hom(─,2)] and the second leg is the codec.

 THE PRIOR ART, measured against the parent commit rather than restated
 from the issue.  There was no [Instance/FinSet/PowerSet.v] and no
 power-set functor of any kind over [FinSet]; the only power-set
 functors over a Sets-like category at one level were the four in
 Instance/Sets/Powerset.v, none of them contravariant at a single
 universe level (Instance/Concrete.v's [Rel_Powerset : Rel ⟶ Sets]
 is a fifth, but it is COVARIANT and out of [Rel], so it bears on
 neither), and no universal
 element was stated for any of them.  Instance/Sets/Powerset/Universal.v
 carries the fuller correction, including why the issue's “no power-set
 functor” reading of the prior art would be wrong.

 (7) [finpow_is_topos_Pow] — the object action AGREES with
 Structure/Topos.v's internal power object [Pow a := Ω ^ a] at
 [FinSet_Topos], by [eq_refl].  ([exponent_obj m n] of
 [FinSet_Closed] is [n ^ m], so [Ω ^ n] at Ω = 2 is [2 ^ n].)

 WHAT IS NOT DELIVERED.  No claim is made that [FinPowerset] is a monad.
 [finpow_is_topos_Pow] identifies the OBJECT actions with the internal
 power object and nothing further: no comparison morphism is built, and
 the internal version has no arrow action to compare with — that is
 exactly the gap Instance/Sets/Powerset.v's header records about
 [Structure/Topos.v].  Nothing here is stated for a general topos,
 and the [Sub ≅ FinPowerset_Sets] comparison lives in [[FinSet^op, Sets]]
 rather than inside [FinSet]. 

 --------
 nLab:       https://ncatlab.org/nlab/show/universal+element 
 nLab:       https://ncatlab.org/nlab/show/subobject+classifier 
 维基百科:  https://en.wikipedia.org/wiki/Power_set 

 Mac Lane 在《CWM》第2版，第III.1节，练习2（印刷版第59页）中询问了对向幂集函子（contravariant power-set functor）的一个泛元素，经典答案是对 ⟨2, {1}⟩。Riehl 在《情境中的范畴论》第2版，第2.3节，例2.3.6（印刷版第68页）中给出了相同的例子，强调泛元素是子集 {⊤} ∈ P(Ω)，即函子在 Ω 上的值的元素，而不是点 ⊤ ∈ Ω，它是将 f: A ⟶ Ω 映射到子集 f⁻¹(⊤) ⊆ A 的同构。Awodey 在《范畴论》第5.3节，例5.14（印刷版第104-106页）中对集合作用进行了对应，其关键点是它在对象中是自然的。归属。 上述章节和页码坐标，以及对这些段落内容的一行总结，是从本文件所回答的问题的目录条目中复制的（jwiegley/category-theory#311，条目 maclane:III.1:ex2，riehl:2.3:example6，awodey:5.3:example14）；在编写本文件时未参考印刷文本，因此这里关于其内容的每一条陈述都是该问题的描述，而非对书籍的阅读。数学内容依靠自身的证明成立。为什么这个文件会与 Instance/Sets/Powerset/Universal.v 一起存在。那个文件在 [Sets] 上回答了相同的练习，其中 A 的子集是 A 上一个 [Prop] 值的谓词，因此，根据构造，它已经是一个映射 A ⟶ Ω；那里的对应关系是真实的，但内容很少，仅仅是单个等价“属于 {⊤} 检测真值”。在这里没有定义性内容：n 元集合的幂集是 2^n 元集合，子集是它的元素，从子集到它的特征映射的转换是 Instance/FinSet/Closed.v 的数字编解码。该编解码器的两个往返都保持在莱布尼茨等式 ([fin_apply_tabulate], [fin_tabulate_apply]) 下，这使得下面的泛性质可以在不使用任何集合等价操作的情况下被证明，并且让整个对应关系可以计算 —— 末尾的验收测试是在闭合数据上的 [eq_refl]。

 该文件提供的内容，以及其强度。

 (1) [FinPowerset : FinSet^op ⟶ FinSet] —— [FinSet] 内的对变幂集函子，对象动作 n ↦ 2^n，箭头动作为逆像。两个函子定律通过 [fin_tabulate_apply] 和 [fin_apply_tabulate] 在代码的莱布尼茨等式下闭合；[FinSet] 的同态集合是按点 [=] ([fun_setoid])，所以这些是真实的陈述，而不是弱化形式。(2) [FinPowerset_Sets : FinSet^op ⟶ Sets] — 相同的函子读入 [Sets]，这是 [AUniversalElement] 对其 [H] 的要求。[finpowerset_sets_agrees] 通过 [eq_refl] 记录了两者具有相同的箭头作用，因此 (2) 是 (1) 的重新输入类型，而不是第二个构造。

 (3) [FinPowerset_universal_element] — Mac Lane 的 §III.1 条款，通过 Theory/Universal/Element.v 的 [AUniversalElement] 得到的对 ⟨2, {⊤}⟩。该通用元素是 [finpow_truth_subset : Fin.t 4]，属于 P(2) 的一个元素，而不是点 [fin_true : Fin.t 2]；两者的类型不同，Test/ProbePowersetUniversal.v 将替换固定为针对阳性对照的类型错误。(4) Riehl 的原像描述，已证明而不仅仅是断言：
 [finpow_fmap_is_preimage] 说 [P k {⊤}] 的第 i 位数字是 [k i] 本身，因此 [finpow_preimage_iff] 读取 i 是否属于 [P k {⊤}] 正当且仅当 [k i] 是 [fin_true] —— 即函子的作用在 k 上应用于通用元素就是 k⁻¹(⊤)。[finpow_preimage_of_truth] 收集这些数字：沿 k 拉回 {⊤} 返回 k 的代码。

 (5) [FinSet_Sub_natural] —— Awodey 的自然性条款在 [FinSet_Classifier] 上实例化：[FinSet] 的子对象 presheaf 与 [Hom(─, 2)] 自然同构。这是应用了 Structure/SubobjectClassifier/Natural.v，而不是重新证明。(6)  [FinSet_Sub_powerset] — 两者连接在一起：
 [Sub ≅ FinPowerset_Sets] 在 [[FinSet^op, Sets] 中]. 因此在 [FinSet] 
 上，(2) 的幂集函子和 Theory/Subobject/Functor.v 的子对象函子自然是相同的预层。中间项是 [Hom(─,2)]，第二条支线是编解码器。与父提交相比衡量的现有技术，而不是从问题中重述。没有 [Instance/FinSet/PowerSet.v]，也没有任何形式的 [FinSet] 上的幂集函子；在某一级别上，类似集合的范畴上唯一的幂集函子是 Instance/Sets/Powerset.v 中的四个，它们在单个宇宙层上都不是逆变的（Instance/Concrete.v 的 [Rel_Powerset : Rel ⟶ Sets] 是第五个，但它是协变的，并且不属于 [Rel]，因此与它们无关），并且没有为其中任何一个指出通用元素。Instance/Sets/Powerset/Universal.v 包含更完整的更正，包括说明为什么问题中“没有幂集函子”的现有技术理解是错误的。(7)  [finpow_is_topos_Pow] — 对象动作与 Structure/Topos.v 的内部幂对象 [Pow a := Ω ^ a] 在 [FinSet_Topos] 处，通过 [eq_refl] 一致。([FinSet_Closed] 的 [exponent_obj m n] 是 [n ^ m]，所以在 Ω = 2 时 [Ω ^ n] 是 [2 ^ n]。)

 未交付的内容。不主张 [FinPowerset] 是一个单子。[finpow_is_topos_Pow] 将对象动作与内部幂对象对应起来，仅此而已：没有建立比较态射，内部版本也没有可供比较的箭头动作——这恰好是 Instance/Sets/Powerset.v 的头文件在 [Structure/Topos.v] 上记录的空白。这里并没有针对一般拓扑声明任何内容，而 [Sub ≅ FinPowerset_Sets] 的比较存在于 [[FinSet^op, Sets] 中，而不是在 [FinSet] 内。
*)

(* ------------------------------------------------------------------------ *)
(* * ** The power set of a finite set, and the inverse image / * ** 有限集的幂集，以及逆像 *)

(*
 The power set of the n-element set is the 2^n-element set: a subset is a
 digit string, one binary digit per element.  The codec
 [fin_tabulate] / [fin_apply] of Instance/FinSet/Closed.v is exactly the
 passage between such a string and the characteristic function it
 encodes, so no new encoding is introduced here. 

 --------
 n 元集合的幂集是 2^n 元集合：一个子集是一个数字字符串，每个元素对应一个二进制位。Instance/FinSet/Closed.v 中的编码器 [fin_tabulate] / [fin_apply] 恰好就是这种字符串与其所编码的特征函数之间的转换，因此这里没有引入新的编码。
*)

Definition finpow (n : nat) : nat := Nat.pow 2 n.

(*
 Membership, as a decidable test: i belongs to the subset coded by S when
 the i-th digit of S is [fin_true].  ([fin_true] is [Fin.F1] and
 [fin_false] is [Fin.FS Fin.F1] — Instance/FinSet/Classifier.v's
 convention, adopted here unchanged so that the classifier connection
 below needs no translation.) 

 --------
 作为可判定测试的隶属关系：当 S 的第 i 位数字是 [fin_true] 时，i 属于 S 编码的子集。（[fin_true] 是 [Fin.F1]，[fin_false] 是 [Fin.FS Fin.F1] —— Instance/FinSet/Classifier.v 的约定，这里保持不变，以便下面的分类器连接无需翻译。）
*)
Definition finpow_mem {n : nat} (S : Fin.t (finpow n)) (i : Fin.t n) : bool :=
  fin_eqb (fin_apply S i) fin_true.

(* The inverse image: the subset of the domain whose i-th digit is the digit of S at [f i]. / 逆像：定义域的子集，其第 i 位数字是 S 在 [f i] 处的数字。 *)
Definition finpow_map {m n : nat} (f : Fin.t n → Fin.t m)
  (S : Fin.t (finpow m)) : Fin.t (finpow n) :=
  fin_tabulate (fun i : Fin.t n => fin_apply S (f i)).

Lemma finpow_map_mem {m n : nat} (f : Fin.t n → Fin.t m)
  (S : Fin.t (finpow m)) (i : Fin.t n) :
  finpow_mem (finpow_map f S) i = finpow_mem S (f i).
Proof. unfold finpow_mem, finpow_map; now rewrite fin_apply_tabulate. Qed.

(*
 The two functor laws.  Both are Leibniz equations between codes, which
 is exactly the pointwise [=] that [FinSet]'s hom-setoid IS (see the
 header note above: [fun_setoid] over the discrete [Fin_Setoid]), not a
 strengthening of it, and each is one rewrite with a codec round trip. 

 --------
 两个函子定律。两者都是代码之间的莱布尼茨方程，这正是 [FinSet] 的同态集（见上方标题注释：离散的 [Fin_Setoid] 上的 [fun_setoid]）的逐点 [=]，而不是对它的加强，每一个都是通过编解码循环的一次重写。
*)

Lemma finpow_map_id {n : nat} (S : Fin.t (finpow n)) :
  finpow_map (fun i : Fin.t n => i) S = S.
Proof. unfold finpow_map; apply fin_tabulate_apply. Qed.

Lemma finpow_map_comp {m n p : nat}
  (f : Fin.t n → Fin.t m) (g : Fin.t p → Fin.t n) (S : Fin.t (finpow m)) :
  finpow_map (fun i => f (g i)) S = finpow_map g (finpow_map f S).
Proof.
  unfold finpow_map.
  apply fin_tabulate_ext; intro i.
  now rewrite fin_apply_tabulate.
Qed.

Lemma finpow_map_ext {m n : nat} (f g : Fin.t n → Fin.t m)
  (H : ∀ i, f i = g i) (S : Fin.t (finpow m)) :
  finpow_map f S = finpow_map g S.
Proof. unfold finpow_map; apply fin_tabulate_ext; intro i; now rewrite H. Qed.

(* ------------------------------------------------------------------------ *)
(** ** The functor, twice / ** 函子，twice *)

(*
 Inside [FinSet].  An arrow x ~> y of [FinSet^op] is an arrow y ~> x of
 [FinSet], so the action on it lands where it should. 

 --------
 在 [FinSet] 内。[FinSet^op] 的箭头 x ~> y 是 [FinSet] 的箭头 y ~> x，所以它的作用落在了它应该落的地方。
*)
Program Definition FinPowerset : FinSet^op ⟶ FinSet := {|
  fobj := finpow ;
  fmap := fun x y (f : x ~{FinSet^op}~> y) => finpow_map f
|}.
Next Obligation. repeat intro; now apply finpow_map_ext. Qed.
Next Obligation. now apply finpow_map_id. Qed.
Next Obligation. now apply finpow_map_comp. Qed.

(*
 ... and into [Sets], which is what [AUniversalElement] needs of its
 functor.  The carrier setoid is the discrete one on [Fin.t (2^n)]; it is
 Instance/Sets/Powerset.v's universe-polymorphic [Powerset_Prop_fin_object]
 rather than a third private copy of the same three-line record. 

 --------
 ... 并进入 [Sets]，这正是 [AUniversalElement] 对其函子所需的。载体集合等价类是 [Fin.t (2^n)] 上的离散集合；它是 Instance/Sets/Powerset.v 的宇宙多态 [Powerset_Prop_fin_object]，而不是同一个三行记录的第三个私有副本。
*)
Program Definition FinPowerset_Sets : FinSet^op ⟶ Sets := {|
  fobj := fun n => Powerset_Prop_fin_object (finpow n) ;
  fmap := fun x y (f : x ~{FinSet^op}~> y) =>
            {| morphism := finpow_map f |}
|}.
Next Obligation.
  (*
 [exact] rather than [apply]: the goal is a projection out of a record
 literal, which [apply]'s unifier declines to reduce here. 

 --------
 [exact] 而不是 [apply]：目标是从记录字面量中投影，[apply] 的统一器在这里拒绝简化。
*)
  repeat intro; exact (finpow_map_ext x0 y0 H x1).
Qed.
Next Obligation. now apply finpow_map_id. Qed.
Next Obligation. now apply finpow_map_comp. Qed.

(* The two carry the same arrow action, by [eq_refl] — the convertibility exception, flagged as such. So (2) is (1) retyped. / 这两者具有相同的箭头操作，由 [eq_refl] —— 可转换性异常，标记为此。因此 (2) 是 (1) 重新输入类型。 *)
Example finpowerset_sets_agrees {x y : FinSet} (f : x ~{FinSet^op}~> y)
  (S : Fin.t (finpow x)) :
  fmap[FinPowerset_Sets] f S = fmap[FinPowerset] f S := eq_refl.

Example finpowerset_obj (n : nat) : fobj[FinPowerset] n = Nat.pow 2 n := eq_refl.

Example finpowerset_two : fobj[FinPowerset] 2%nat = 4%nat := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** Ω, the point ⊤, and the SUBSET {⊤} / * ** Ω，点 ⊤，以及子集 {⊤} *)

(*
 The truth-value object of [FinSet_Classifier] is 2, and its point is
 [fin_true].  The universal element is NOT that point: it is the subset
 {⊤} ⊆ 2, an element of P(2) = 4, namely the digit string whose
 [fin_true] digit is [fin_true] and whose [fin_false] digit is
 [fin_false] — that is, the code of the identity function on 2. 

 --------
 [FinSet_Classifier] 的真值对象是 2，它的点是 [fin_true]。全体元素不是那个点：它是子集 {⊤} ⊆ 2，属于 P(2) = 4，即数字字符串，其 [fin_true] 位是 [fin_true]，[fin_false] 位是 [fin_false] — 也就是说，它是 2 上恒等函数的编码。
*)

Definition finpow_truth_point : Fin.t 2 := fin_true.

Definition finpow_truth_subset : Fin.t (finpow 2) :=
  fin_tabulate (fun i : Fin.t 2 => i).

(* It really is {⊤}: ⊤ is in it and ⊥ is not, by computation. / 它确实是 {⊤}：通过计算，⊤ 在其中而 ⊥ 不在其中。 *)
Example finpow_truth_has_true :
  finpow_mem finpow_truth_subset fin_true = true := eq_refl.

Example finpow_truth_lacks_false :
  finpow_mem finpow_truth_subset fin_false = false := eq_refl.

(*
 ... and the digit at j is j itself, for every j — the general form of the
 two computations above, which is what the universal property consumes. 

 --------
 ... 并且每个 j 的数字就是 j 本身——这是上面两种计算的一般形式，也是通用性质所使用的。
*)
Lemma finpow_truth_digit (j : Fin.t 2) : fin_apply finpow_truth_subset j = j.
Proof. unfold finpow_truth_subset; apply fin_apply_tabulate. Qed.

(* ------------------------------------------------------------------------ *)
(* * ** Mac Lane's §III.1 universal element ⟨2, {⊤}⟩ / * ** 麦克莱恩 §III.1 通用元素 ⟨2, {⊤}⟩ *)

(*
 THE PREIMAGE DESCRIPTION, PROVED FIRST, because it is what makes the
 universal property mean what Riehl says it means: the action of the
 functor on k, applied to {⊤}, is the preimage k⁻¹(⊤). 

 --------
 预像描述，首先被证明，因为它是让普遍性意义正如 Riehl 所说的那样：函子在 k 上的作用，应用于 {⊤}，就是预像 k⁻¹(⊤)。
*)

Lemma finpow_fmap_is_preimage {n : nat} (k : Fin.t n → Fin.t 2)
  (i : Fin.t n) :
  fin_apply (finpow_map k finpow_truth_subset) i = k i.
Proof.
  unfold finpow_map; rewrite fin_apply_tabulate; apply finpow_truth_digit.
Qed.

Lemma finpow_preimage_iff {n : nat} (k : Fin.t n → Fin.t 2) (i : Fin.t n) :
  finpow_mem (finpow_map k finpow_truth_subset) i = fin_eqb (k i) fin_true.
Proof. unfold finpow_mem; now rewrite finpow_fmap_is_preimage. Qed.

(*
 Pulling {⊤} back along k recovers the code of k on the nose — this is the
 preimage law with the digits collected, and it is the whole universal
 property once [fin_tabulate]/[fin_apply] are known to be inverse. 

 --------
 沿着 k 拉回 {⊤} 可以精确地恢复 k 的代码——这是带有收集的数字的原像律，并且一旦已知 [fin_tabulate] / [fin_apply] 是逆的，这就是完整的普遍性质。
*)
Lemma finpow_preimage_of_truth {n : nat} (k : Fin.t n → Fin.t 2) :
  finpow_map k finpow_truth_subset = fin_tabulate k.
Proof.
  unfold finpow_map; apply fin_tabulate_ext; intro i; apply finpow_truth_digit.
Qed.

(*
 Mac Lane's clause at D := FinSet^op and H := FinPowerset_Sets: for every
 object n and every subset S of n there is a UNIQUE arrow
 k : 2 ~{FinSet^op}~> n — that is, a unique function n → 2 — with
 k⁻¹(⊤) = S.  The witness is [fin_apply S], the characteristic function
 read off the digit string. 

 --------
 Mac Lane 在 D := FinSet^op 和 H := FinPowerset_Sets 的条款：对于每一个对象 n 以及 n 的每一个子集 S，都存在一个唯一的箭头 k : 2 ~{FinSet^op}~> n——也就是说，存在一个唯一的函数 n → 2——使得 k⁻¹(⊤) = S。证据是 [fin_apply S]，即通过数字字符串读出的特征函数。
*)
Program Definition FinPowerset_universal_element :
  @AUniversalElement (FinSet^op) FinPowerset_Sets 2%nat := {|
  aue_elem := finpow_truth_subset ;
  aue_universal := fun n S => {| unique_obj := fin_apply S |}
|}.
Next Obligation.
  rewrite finpow_preimage_of_truth; apply fin_tabulate_apply.
Qed.
Next Obligation.
  (* Uniqueness. [Program] has already substituted S by k⁻¹(⊤) and introduced the point, so the goal IS the preimage law. / 独特性。[Program] 已经用 k⁻¹(⊤) 替代了 S 并引入了该点，因此目标是原像律。 *)
  apply finpow_fmap_is_preimage.
Qed.

(* The element of the pair is {⊤} and the mediating arrow of a subset is its characteristic function, both by [eq_refl]. / 这个对的元素是 {⊤}，子集的中介箭头是它的特征函数，均由 [eq_refl] 给出。 *)
Example finpow_aue_elem :
  @aue_elem (FinSet^op) FinPowerset_Sets 2%nat FinPowerset_universal_element
    = finpow_truth_subset := eq_refl.

Example finpow_aue_med (n : nat) (S : Fin.t (finpow n)) :
  unique_obj (@aue_universal (FinSet^op) FinPowerset_Sets 2%nat
                FinPowerset_universal_element n S)
    = fin_apply S := eq_refl.

(*
 The representation, through the Yoneda-FREE route of
 Theory/Universal/Element.v.  (The Yoneda route is unavailable at [Sets]
 for universe reasons recorded in Instance/Sets/Powerset/Universal.v; it
 is not taken here either, so that both files go the same way and the
 comparison between them is not confounded.) 

 --------
 通过 Theory/Universal/Element.v 的 Yoneda-FREE 路径的表示。（由于在 Instance/Sets/Powerset/Universal.v 中记录的宇宙原因，[Sets] 无法使用 Yoneda 路径；此处也没有采用该路径，因此两个文件都使用相同的方式，使它们之间的比较不被混淆。）
*)
Definition FinPowerset_representation :
  @Curried_Hom (FinSet^op) 2%nat
    ≅[[(FinSet^op), Sets]] FinPowerset_Sets :=
  ue_representation FinPowerset_Sets 2%nat FinPowerset_universal_element.

Example finpow_representation_to_is_preimage (n : nat)
  (k : n ~{FinSet}~> 2%nat) :
  transform (to FinPowerset_representation) n k
    = finpow_map k finpow_truth_subset := eq_refl.

Definition FinPowerset_Representable : Representable FinPowerset_Sets :=
  Representable_of_UniversalElement
    (UniversalElement_of_AUniversalElement FinPowerset_universal_element).

Example finpow_repr_obj :
  @repr_obj (FinSet^op) FinPowerset_Sets FinPowerset_Representable = 2%nat
  := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** Awodey's naturality clause at [FinSet_Classifier] / * ** Awodey 在 [FinSet_Classifier] 的自然性条款 *)

(* Structure/SubobjectClassifier/Natural.v applied — nothing is reproved. [Ω] of [FinSet_Classifier] is 2 on the nose, so the target is literally [Hom(─, 2)]. / Structure/SubobjectClassifier/Natural.v 已应用 — 没有被重新证明。 [Ω] 的 [FinSet_Classifier] 恰好是 2，所以目标字面上是 [Hom(─, 2)] 。 *)
Definition FinSet_Sub_natural :
  @Isomorphism ([(FinSet^op), Sets])
    (@Sub FinSet FinSet_Pullbacks) (@Curried_CoHom FinSet 2%nat)
  := @Sub_classifier_natural FinSet FinSet_Terminal FinSet_Pullbacks
       FinSet_Classifier.

Definition FinSet_Sub_Representable : Representable (@Sub FinSet FinSet_Pullbacks)
  := @Sub_Representable FinSet FinSet_Terminal FinSet_Pullbacks
       FinSet_Classifier.

Example FinSet_Sub_repr_obj :
  @repr_obj (FinSet^op) (@Sub FinSet FinSet_Pullbacks) FinSet_Sub_Representable
    = 2%nat := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** The subobject presheaf of [FinSet] IS the power-set functor / * ** [FinSet] 的子对象预层是幂集函子 *)

(*
 The codec, as a natural isomorphism [Hom(─,2) ≅ FinPowerset_Sets].  Its
 naturality is one application of [fin_apply_tabulate]; both round trips
 are the codec's own Leibniz equations. 

 --------
 该编解码器，作为一个自然同构 [Hom(─,2) ≅ FinPowerset_Sets]。它的自然性是 [fin_apply_tabulate] 的一个应用；两次往返都是编解码器自身的莱布尼兹方程。
*)

(*
 The two naturality equations of the codec, isolated so that the seven
 obligations below — six of which reach a [Next Obligation] — can be
 discharged by one tactic that tries each in both
 orientations — [Program] emits them in an order that is not worth
 predicting, and a mis-guessed order is the only thing a hand-written list
 would be recording. 

 --------
 编解码器的两个自然性方程被孤立出来，以便以下七个义务——其中六个达到 [Next Obligation]——可以通过一种策略来完成，该策略对每个方程都尝试两种方向——[Program] 以一个不值得预测的顺序输出它们，而唯一会被手写列表记录的只是猜错的顺序。
*)

Lemma codec_natural_to {m n : nat} (f : Fin.t n → Fin.t m)
  (k : Fin.t m → Fin.t 2) :
  finpow_map f (fin_tabulate k) = fin_tabulate (fun i => k (f i)).
Proof.
  unfold finpow_map; apply fin_tabulate_ext; intro i.
  now rewrite fin_apply_tabulate.
Qed.

Lemma codec_natural_from {m n : nat} (f : Fin.t n → Fin.t m)
  (S : Fin.t (finpow m)) (i : Fin.t n) :
  fin_apply (finpow_map f S) i = fin_apply S (f i).
Proof. unfold finpow_map; now rewrite fin_apply_tabulate. Qed.

Local Ltac codec :=
  simpl; repeat intro;
  first [ exact (codec_natural_from _ _ _)
        | symmetry; exact (codec_natural_from _ _ _)
        | exact (codec_natural_to _ _)
        | symmetry; exact (codec_natural_to _ _)
        | apply fin_tabulate_apply
        | symmetry; apply fin_tabulate_apply
        | apply fin_apply_tabulate
        | symmetry; apply fin_apply_tabulate
        | apply fin_tabulate_ext; assumption
        | symmetry; apply fin_tabulate_ext; assumption
        | subst; reflexivity
        | reflexivity ].

Program Definition finpow_codec :
  @Isomorphism ([(FinSet^op), Sets])
    (@Curried_CoHom FinSet 2%nat) FinPowerset_Sets := {|
  to   := {| transform := fun n => {| morphism := fun k : Fin.t n -> Fin.t 2 =>
                                        fin_tabulate k |} |} ;
  from := {| transform := fun n => {| morphism := fun S : Fin.t (finpow n) =>
                                        fin_apply S |} |}
|}.
Next Obligation. codec. Qed.
Next Obligation. codec. Qed.
Next Obligation. codec. Qed.
Next Obligation. codec. Qed.
Next Obligation. codec. Qed.
Next Obligation. codec. Qed.

(* THE CAPSTONE. Subobjects of a finite set are its subsets, naturally. / 顶石。有限集合的子对象自然是它的子集。 *)
Definition FinSet_Sub_powerset :
  @Isomorphism ([(FinSet^op), Sets])
    (@Sub FinSet FinSet_Pullbacks) FinPowerset_Sets :=
  iso_compose finpow_codec FinSet_Sub_natural.

(* ------------------------------------------------------------------------ *)
(* * ** Non-vacuity: the correspondence computing on a concrete subset / * ** 非空性：在具体子集上的对应计算 *)

(* The subset {0, 2} ⊆ 3, as a digit string. / 子集 {0, 2} ⊆ 3，作为一个数字字符串。 *)
Definition finpow_sub02 : Fin.t (finpow 3) :=
  fin_tabulate (fun i : Fin.t 3 =>
    match i with
    | Fin.F1 => fin_true
    | Fin.FS Fin.F1 => fin_false
    | _ => fin_true
    end).

(* Its three membership digits, by computation. / 它的三个会员数字，通过计算。 *)
Example finpow_sub02_at_0 : finpow_mem finpow_sub02 Fin.F1 = true := eq_refl.
Example finpow_sub02_at_1 :
  finpow_mem finpow_sub02 (Fin.FS Fin.F1) = false := eq_refl.
Example finpow_sub02_at_2 :
  finpow_mem finpow_sub02 (Fin.FS (Fin.FS Fin.F1)) = true := eq_refl.

(*
 The mediating arrow produced by the universal property is its
 characteristic function, and it takes the expected values — computed
 through the class accessor, not through [fin_apply] directly, so what is
 being checked is the universal element and not the codec. 

 --------
 由泛性质产生的中介箭头是其特征函数，它获取期望值——通过类访问器计算，而不是直接通过 [fin_apply]，所以被检查的是泛元素而不是编解码器。
*)
Definition finpow_char02 : Fin.t 3 → Fin.t 2 :=
  unique_obj (@aue_universal (FinSet^op) FinPowerset_Sets 2%nat
                FinPowerset_universal_element 3%nat finpow_sub02).

Example finpow_char02_at_0 : finpow_char02 Fin.F1 = fin_true := eq_refl.
Example finpow_char02_at_1 :
  finpow_char02 (Fin.FS Fin.F1) = fin_false := eq_refl.
Example finpow_char02_at_2 :
  finpow_char02 (Fin.FS (Fin.FS Fin.F1)) = fin_true := eq_refl.

(* The round trip: the preimage of {⊤} along that characteristic map is the subset again, by computation on closed data. / 往返：沿着那个特征映射的 {⊤} 的原像再次是该子集，通过对闭合集的计算得到。 *)
Example finpow_round02 :
  finpow_map finpow_char02 finpow_truth_subset = finpow_sub02 := eq_refl.

(* A DEGENERACY EXCLUDED BY PROOF: distinct subsets have distinct characteristic maps, so the correspondence is not collapsing anything. The witness is {0,2} against the EMPTY subset. / 通过证明排除的退化情况：不同的子集有不同的特征映射，因此这种对应关系不会压缩任何东西。证据是 {0,2} 对 EMPTY 子集。 *)
Definition finpow_empty : Fin.t (finpow 3) :=
  fin_tabulate (fun _ : Fin.t 3 => fin_false).

Example finpow_empty_has_nothing (i : Fin.t 3) :
  finpow_mem finpow_empty i = false.
Proof. unfold finpow_mem, finpow_empty; now rewrite fin_apply_tabulate. Qed.

Example finpow_sub02_ne_empty : finpow_sub02 = finpow_empty → False.
Proof. discriminate. Qed.

Example finpow_chars_distinct :
  fin_apply finpow_sub02 = fin_apply finpow_empty → False.
Proof.
  intro Heq.
  assert (H0 : fin_apply finpow_sub02 Fin.F1 = fin_apply finpow_empty Fin.F1)
    by now rewrite Heq.
  discriminate H0.
Qed.

(*
 A SECOND DEGENERACY EXCLUDED: the functor's action genuinely MOVES
 subsets, so it is not the identity in disguise.  Along the constant map
 at 0 the inverse image of {0,2} is all of 3 — every i has [const0 i = 0],
 which is in the subset — and the inverse image of the empty subset is
 empty, so the two are separated. 

 --------
 排除第二种退化情况：函子作用确实移动了子集，因此它不是伪装的恒等。在 0 处的常值映射沿线，{0,2} 的逆像是整个 3 — 每个 i 都有 [const0 i = 0]，它在该子集中 — 而空子集的逆像是空的，因此两者是分开的。
*)
Definition finpow_const0 : Fin.t 3 → Fin.t 3 := fun _ => Fin.F1.

Example finpow_inverse_of_sub02_is_full :
  finpow_map finpow_const0 finpow_sub02
    = fin_tabulate (fun _ : Fin.t 3 => fin_true) := eq_refl.

Example finpow_inverse_of_empty_is_empty :
  finpow_map finpow_const0 finpow_empty = finpow_empty := eq_refl.

Example finpow_inverse_moves :
  finpow_map finpow_const0 finpow_sub02 = finpow_sub02 → False.
Proof. discriminate. Qed.

(* ------------------------------------------------------------------------ *)
(** ** The internal power object / ** 内部力量对象 *)

(*
 Structure/Topos.v defines the power object of a topos as the exponential
 [Pow a := Ω ^ a], an assignment on OBJECTS with no action on morphisms —
 the gap Instance/Sets/Powerset.v's header records.  At [FinSet_Topos]
 its object action is this file's, on the nose: [exponent_obj m n] is
 [n ^ m], so [Ω ^ n] at Ω = 2 is [2 ^ n], which is [finpow n].  What
 [FinPowerset] adds over it is the arrow action; no comparison morphism
 is claimed, because there is nothing on the other side to compare. 

 --------
 Structure/Topos.v 将一个拓扑的幂对象定义为指数对象 [Pow a := Ω ^ a]，这是在对象上的一个赋值，对态射没有作用——Instance/Sets/Powerset.v 的头部记录有这个空缺。在 [FinSet_Topos] 处，它的对象作用正是该文件中的：[exponent_obj m n] 是 [n ^ m]，所以在 Ω = 2 时的 [Ω ^ n] 是 [2 ^ n]，而 [2 ^ n] 是 [finpow n]。[FinPowerset] 在其上增加的是箭头的作用；没有声称有比较态射，因为另一边没有可比较的东西。
*)

Example finpow_is_topos_Pow (n : nat) :
  @Pow FinSet FinSet_Topos n = finpow n := eq_refl.

(* This numeric instance is the pre-existing [FinSet_Pow_two] (Instance/FinSet/Topos.v) restated; the general [finpow_is_topos_Pow] above is what is new here. / 这个数字实例是预先存在的 [FinSet_Pow_two] (Instance/FinSet/Topos.v) 的重述；上面的通用 [finpow_is_topos_Pow] 是这里的新内容。 *)
Example finpow_topos_Pow_two :
  @Pow FinSet FinSet_Topos 2%nat = 4%nat := eq_refl.
