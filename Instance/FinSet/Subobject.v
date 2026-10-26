Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.Topos.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Powerset.
Require Import Category.Instance.FinSet.Topos.


Generalizable All Variables.

(* * * Subobjects of a skeletal finite set: images that compute, and Fong and Spivak's merging-versus-tagging exercise / * * 骨架有限集合的子对象：计算的图像，以及 Fong 和 Spivak 的合并与标记练习 *)

(*
 nLab:      https://ncatlab.org/nlab/show/subobject
 nLab:      https://ncatlab.org/nlab/show/image
 Wikipedia: https://en.wikipedia.org/wiki/Image_(category_theory)
 Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.
 (GTM 5), §V.7 Definition 2, printed p. 126 (PDF p. 135)
 Book:      Fong and Spivak, “Seven Sketches in Compositionality”,
 §1.2.1 including Exercise 1.11, printed p. 8 (PDF p. 20)

 Theory/Subobject/Lattice.v's [sub_meet] and [sub_join] are conditional
 constructions: the meet wants chosen pullbacks, the join wants a
 cocartesian structure and images.  [FinSet] already has the first two
 -- Instance/FinSet/Classifier.v's [FinSet_Pullbacks] and
 Instance/FinSet.v's [FinSet_Cocartesian] -- and this file adds the
 third.  What that buys is not merely inhabitation but COMPUTATION:
 objects of [FinSet] are literal natural numbers and every codec in
 play reduces on closed input, so the meet and the join of two named
 subobjects can be EVALUATED, and Fong and Spivak's exercise -- the
 union of two subsets of a four-element set has four elements where
 their disjoint union has five -- becomes a pair of [eq_refl]s rather
 than a pair of isomorphisms.

 ** THE IMAGE, AND WHY THE DECISION PROCEDURE MUST RETURN A WITNESS

 For f : m ~> n the image is cut out by the HIT PREDICATE [finset_hit],
 “some a of the domain is carried to k”, decided by
 Instance/FinSet/Classifier.v's [fin_existsb].  The image object is
 [fin_countP] of it, the mono is [fin_select] of it with
 monicity read straight off [fin_select_inj], and the factoring
 arrow is [fin_rank] at the hit witness supplied by
 [fin_existsb_complete].  The whole shape is
 Instance/FinSet/Limit.v's [FinSet_IsEqualizer] one construction over:
 a decidable predicate, its count, its tabulation, its ranking.

 [im_least] is where the choice of decision procedure is forced.  Given
 a competing subobject w and a factorization g of f through it, the
 comparison arrow must send the q-th selected image point to g of SOME
 a with f a = that point.  A boolean test alone cannot produce that a.
 Classifier.v's [fin_existsb_sound] can, because it is written to
 return the least witness as DATA -- a sigT, and it ends in [Defined]
 for exactly this kind of consumer.  [finset_image_witness] is that
 projection and [finset_image_witness_eq] its defining equation, by
 [fin_eqb_eq].  No injectivity of [sub_mono w] is spent here, unlike in
 the [Sets] companion: [FinSet]'s hom-setoid is pointwise Leibniz
 equality, so the equation transports with no respectfulness side
 condition at all.

 ** EXERCISE 1.11, CONCRETE AND COMPUTING

 The ambient object is 4.  [ex11_u] is {0,1} and [ex11_v] is {1,2,3},
 each presented as the count-codec subobject of an explicit boolean
 predicate, so that monicity is [fin_select_inj] and the domain is a
 count that reduces.  Then, all by [eq_refl]:

 [ex11_u_size]          sub_dom ex11_u                = 2
 [ex11_v_size]          sub_dom ex11_v                = 3
 [ex11_union_four]      sub_dom (sub_join ex11_u ex11_v) = 4
 [ex11_coproduct_five]  Coprod 2 3                    = 5
 [ex11_meet_one]        sub_dom (sub_meet ex11_u ex11_v) = 1

 The third is the book's MERGING reading and the fourth its TAGGING
 reading, side by side on the same two subsets, which is the whole
 point of the exercise.  The union number is not put in by hand: it is
 [fin_countP] of the hit predicate of the copairing out of
 [Fin.t (2 + 3)], evaluated.  The meet number is the count of the
 agreement predicate over the encoded pairs in [Fin.t (2 * 3)],
 evaluated through [FinSet_Pullbacks].

 The arithmetic clauses of the same exercise, which the tree asserted
 nowhere at these instances, are [finset_pow_three] (Pow 3 = 8) and
 [finset_product_two_three] (2 × 3 = 6), in the style of
 Instance/FinSet/Topos.v's [FinSet_Pow_two]; the third, 2 + 3 = 5, is
 [ex11_coproduct_five] above and is not restated.  Seventeen [eq_refl]
 Examples in all -- [grep -c ':= eq_refl'] over this file.

 ** THE ELEMENTS OF Pow 2, AND A CORRECTION TO THE ISSUE'S PRIOR-ART CLAIM

 The catalog issue says the [fin_tabulate]/[fin_apply] codec elements
 “are never listed”.  MEASURED, that is too strong.  Running
 [grep -c “^Example .*_at_”] over Instance/FinSet/Subsets.v and
 Instance/FinSet/Powerset.v and reading the [finpow_mem] ones out finds
 NINE membership bits already recorded: six in Subsets.v and three in Powerset.v.

 What is genuinely absent is narrower, and it is what the block below
 supplies.  First, every one of those nine names its code by
 [fin_tabulate] of a characteristic function ([empty1], [full1],
 [sub2_10], [sub2_01], [finpow_sub02] -- checked at their defining
 lines); NOT ONE names a code by its POSITION in [Fin.t (finpow n)].
 Second, at n = 2 the four codes are all defined (Subsets.v) but only two of them are read out, so four of the eight
 bits were listed and four were not.  [powcode2_0] through
 [powcode2_3] are the four positions and the eight [powcode2_i_at_j]
 Examples are the complete bit table, which is the enumeration the
 issue asks for.  [finpow_two_is_Pow] pins [finpow 2] to
 Structure/Topos.v's [Pow] at [FinSet_Topos] by [eq_refl], so the
 positions really are positions in the topos-internal power object and
 not merely in a same-sized set.

 ** BOUNDARIES, measured

 Both computed numbers are pinned by their neighbours being refused.
 [sub_dom (sub_join ex11_u ex11_v) = 5%nat] is refused with “cannot
 unify sub_dom (sub_join ex11_u ex11_v) and 5%nat”, and [sub_dom
 (sub_meet ex11_u ex11_v) = 2%nat] likewise against 2 -- conversion
 refusals, not typing or universe ones, which is what makes the
 positive [eq_refl]s evidence that the codecs reduced rather than that
 the statement was vacuous.

 ** TRANSPARENCY, measured by flipping

 [finset_image_least] is the only [Defined] here, and it was flipped to
 [Qed] and the file recompiled clean, so the transparency is for
 uniformity with the [Sets] companion rather than forced: the [eq_refl]
 Examples read [finset_image_obj] and [finset_image_mono], never
 [im_least].  Those two, and [finset_image_sub], [FinSet_ImageOf] and
 [finset_image_witness], are plain [Definition]s and MUST stay
 transparent for the Examples to reduce.

 ** UNIVERSES

 [About FinSet_HasImages] prints
 [FinSet_HasImages@{u u0 u1 u2 u3} : HasImages@{u u0} FinSet@{u u0 u1 u2}]
 with the single-line block [Set < u1], inherited from [FinSet] itself
 (objects are [nat]).  Nothing here introduces a constraint of its own.

 ** WHAT IS NOT DELIVERED

 No [HasWidePullbacks FinSet] -- the wide case is delivered at [Sets]
 only, and the count codec does not obviously extend to an arbitrary
 index type.  No [IsMeet]/[IsJoin] witnesses: the greatest-lower-bound
 and least-upper-bound properties of the computed objects are
 Theory/Subobject/Lattice.v's business, and nothing below states them.
 No lattice or order instance on [SubObj n], for the [Type]-versus-[Prop]
 reason Instance/Powerset/Subobject.v's header gives.  No comparison
 between the count-codec subobjects here and
 Instance/FinSet/Subsets.v's [finpow_le] order on power-object codes,
 and no claim that [FinSet_HasImages] agrees with any orthogonal
 factorization system or with Structure/Regular.v's image.  Nothing
 below mentions Instance/FinSet/Regular.v, which builds regular
 MORPHISMS and their splittings rather than a factorization.  The union
 and the coproduct are compared only at the level of OBJECT SIZES; no
 comparison arrow between them is built. 

 --------
 nLab：       https://ncatlab.org/nlab/show/subobject
 nLab：       https://ncatlab.org/nlab/show/image
 Wikipedia：  https://en.wikipedia.org/wiki/Image_(category_theory)
 书籍：       Mac Lane，《为在职数学家而作的范畴论》，第2版
 （GTM 5），§V.7 定义2，印刷页126（PDF页135）
 书籍：       Fong 和 Spivak，《组合性中的七个素描》，
 §1.2.1 包括练习题1.11，印刷页8（PDF页20）Theory/Subobject/Lattice.v 的 [sub_meet] 和 [sub_join] 是条件构造：meet 需要选定的 pullbacks，join 需要一个 cocartesian 结构和像。[FinSet] 已经有了前两个——Instance/FinSet/Classifier.v 的 [FinSet_Pullbacks] 和 Instance/FinSet.v 的 [FinSet_Cocartesian]——而这个文件添加了第三个。这带来的不仅是存在性，而是计算能力：[FinSet] 的对象是字面上的自然数，每个使用到的 codec 在闭合输入上都会归约，所以两个命名子对象的 meet 和 join 可以被计算，并且 Fong 和 Spivak 的练习——一个四元素集合的两个子集的并集有四个元素，而它们的 disjoint union 有五个元素——变成了一对 [eq_refl]，而不是一对同构。

 ** 像，以及为什么决策过程必须返回一个见证对于 f : m ~> n, 其像由 HIT PREDICATE [finset_hit] 切出，
 “定义域中的某个 a 被映射到 k”，由 Instance/FinSet/Classifier.v 的 [fin_existsb] 决定。像对象是 [fin_countP]，它的单射是 [fin_select]，其单射性直接从 [fin_select_inj] 读取，而分解箭头是在 [fin_existsb_complete] 提供的 HIT 证人处的 [fin_rank]。整个结构是 Instance/FinSet/Limit.v 的 [FinSet_IsEqualizer]，一个构造在以下内容之上：可判定谓词、它的计数、它的分类表、它的排序。[im_least] 是必须选择决策过程的位置。给定一个竞争的子对象 w 以及 f 通过它的分解 g，比较箭头必须将第 q 个选定的像点发送到 g 的某个 a，使得 f a = 该点。仅靠布尔测试无法生成该 a。Classifier.v 的 [fin_existsb_sound] 可以做到这一点，因为它被编写为返回最小的证据作为 DATA —— 一个 sigT，并且它正是为这种类型的使用者以 [Defined] 结束。[finset_image_witness] 是该投影，而 [finset_image_witness_eq] 是它的定义方程，由 [fin_eqb_eq] 指出。这里没有花费 [sub_mono w] 的单射性，不像在 [Sets] 伴随中：[FinSet] 的 hom-setoid 是逐点的 Leibniz 相等，因此该方程传输时根本不需要任何尊重性附加条件。

 ** 练习 1.11，具体和计算环境对象是 4。[ex11_u] 是 {0,1}，[ex11_v] 是 {1,2,3}，每个都作为显式布尔谓词的计数编解码子对象呈现，因此单射性是 [fin_select_inj]，且域是一个可约计数。然后，全部由 [eq_refl]：

 [ex11_u_size]           子域 ex11_u                = 2
 [ex11_v_size]           子域 ex11_v                = 3
 [ex11_union_four]       子域 (子连接 ex11_u ex11_v) = 4
 [ex11_coproduct_five]   余积 2 3                    = 5
 [ex11_meet_one]         子域 (子交 ex11_u ex11_v) = 1第三个是书中的合并阅读，第四个是标记阅读，它们在同样的两个子集上并排进行，这是练习的整个重点。联合数不是手动输入的：它是 [fin_countP]，在 [Fin.t (2 + 3)] 中的共配对出发命题的命中，经过评估。交数是经过 [FinSet_Pullbacks] 评估的 [Fin.t (2 * 3)] 编码对上的一致谓词的计数。

 同一练习的算术条款，在这些实例中树没有在任何地方断言，是 [finset_pow_three]（3 的幂 = 8）和 [finset_product_two_three]（2 × 3 = 6），风格类似 Instance/FinSet/Topos.v 的 [FinSet_Pow_two]；第三个，2 + 3 = 5，是上面的 [ex11_coproduct_five]，并未重述。总共有十七个 [eq_refl] 示例——[grep -c ':= eq_refl'] 在此文件中。** Pow 2 的元素，以及对该期刊先前专利主张的更正

 该目录条目称 [fin_tabulate] / [fin_apply] 编解码器元素“从未列出”。测量来看，这说法太绝对了。在 Instance/FinSet/Subsets.v 和 Instance/FinSet/Powerset.v 上运行 [grep -c “^Example .*_at_”] 并读取 [finpow_mem] 的结果，发现已经记录了九个成员位：Subsets.v 中有六个，Powerset.v 中有三个。真正缺失的是更狭义的东西，它正是下面区块提供的。首先，这九个名字中的每一个都通过特征函数（[empty1]、[full1]、[sub2_10]、[sub2_01]、[finpow_sub02]——在它们的定义行已检查）来命名其代码；没有一个是通过在[Fin.t (finpow n)]中的位置来命名代码的。其次，当 n = 2 时，四个代码都已定义（Subsets.v），但只有两个被读出，因此八个比特中的四个被列出，四个没有。[powcode2_0] 到 [powcode2_3] 是四个位置，而八个 [powcode2_i_at_j] 示例是完整的比特表，这是该问题所要求的枚举。[finpow_two_is_Pow] 钉住 [finpow 2] 到 Structure/Topos.v 的 [Pow] 在 [FinSet_Topos] 由 [eq_refl] ，因此这些位置确实是在拓扑内部幂对象中的位置，而不仅仅是在一个同样大小的集合中。

 ** 边界，已测量

 两个计算得出的数字都被它们的邻居拒绝钉住。[sub_dom (sub_join ex11_u ex11_v) = 5%nat] 被拒绝，提示“无法统一 sub_dom (sub_join ex11_u ex11_v) 和 5%nat”，并且 [sub_dom (sub_meet ex11_u ex11_v) = 2%nat] 同样被 2 拒绝——这是转换拒绝，而不是类型或宇宙拒绝，这就是为什么正的 [eq_refl] 是编解码器已化简的证据，而不是语句无效的证据。

 ** 透明度，通过翻转测量[finset_image_least] 是这里唯一的 [Defined]，并且它被翻转为 [Qed] 并且文件重新编译干净，因此透明性是为了与 [Sets] 同伴保持一致，而不是强制性的：[eq_refl] 示例读取 [finset_image_obj] 和 [finset_image_mono]，从不读取 [im_least]。那两个，以及 [finset_image_sub]、[FinSet_ImageOf] 和 [finset_image_witness]，都是普通的 [Definition] 并且必须保持透明，以便示例可以缩小。

 ** 宇宙

 [About FinSet_HasImages] 打印 [FinSet_HasImages@{u u0 u1 u2 u3} : HasImages@{u u0} FinSet@{u u0 u1 u2}]，使用单行块 [Set < u1]，继承自 [FinSet] 自身（对象是 [nat]）。这里只是没有引入任何自己的约束。

 ** 未交付的内容没有 [HasWidePullbacks FinSet] —— 宽泛情况只在 [Sets] 处提供，而且计数编解码器显然不会扩展到任意索引类型。没有 [IsMeet] / [IsJoin] 的见证：计算对象的最大下界和最小上界属性属于 Theory/Subobject/Lattice.v 的范畴，下面没有任何内容陈述它们。在 [SubObj n] 上没有格或序实例，原因见 [Type] 与 [Prop] 在 Instance/Powerset/Subobject.v 头部的比较。这里的计数编解码子对象与 Instance/FinSet/Subsets.v 中 [finpow_le] 的幂对象代码顺序之间没有任何比较，也没有声明 [FinSet_HasImages] 与任何正交分解系统或 Structure/Regular.v 的像一致。下面没有提到 Instance/FinSet/Regular.v，它构建的是正规 MORPHISMS 及其拆分，而不是因式分解。并集和余积仅在对象大小的层面上进行比较；它们之间没有构建比较箭头。
*)

(* ------------------------------------------------------------------------ *)
(* * ** (a) The map out of the empty finite set is monic / * **（a）空有限集的映射是单射 *)

Lemma FinSet_zero_monic (x : FinSet) : Monic (@zero FinSet FinSet_Initial x).
Proof.
  constructor; intros z g1 g2 _ i.
  exact (Fin.case0 (fun _ => g1 i = g2 i) (g1 i)).
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** (b) Images by the counted-subset codec / * **（b）由计数子集编解码器生成的图像 *)

Section FinSetImages.

Context {m n : nat}.
Context (f : Fin.t m → Fin.t n).

(*
 The hit predicate: k is in the image when some a of the domain is
 carried to it.  [fin_existsb] decides this, and its soundness lemma
 returns the least witness as DATA, which is what [im_least] consumes. 

 --------
 命中谓词：当域中的某个 a 被映射到它时，k 在图像中。[fin_existsb] 决定这一点，并且它的可靠性引理返回最小的证据作为 DATA，这正是 [im_least] 使用的。
*)
Definition finset_hit : Fin.t n → bool :=
  fun k => fin_existsb (fun a : Fin.t m => fin_eqb (f a) k).

Definition finset_image_obj : nat := fin_countP finset_hit.

Definition finset_image_mono : Fin.t finset_image_obj → Fin.t n :=
  fin_select finset_hit.

Lemma finset_image_monic : Monic (finset_image_mono : _ ~{FinSet}~> _).
Proof.
  constructor; intros z g1 g2 Hg i.
  exact (fin_select_inj finset_hit (g1 i) (g2 i) (Hg i)).
Qed.

Definition finset_image_sub : @SubObj FinSet n :=
  @Build_SubObj FinSet n finset_image_obj finset_image_mono
    finset_image_monic.

Lemma finset_hit_value (a : Fin.t m) : finset_hit (f a) = true.
Proof.
  exact (fin_existsb_complete (fun b : Fin.t m => fin_eqb (f b) (f a)) a
           (fin_eqb_refl (f a))).
Qed.

Definition finset_image_factor : Fin.t m → Fin.t finset_image_obj :=
  fun a => fin_rank finset_hit (f a) (finset_hit_value a).

Lemma finset_image_commutes :
  (finset_image_mono : _ ~{FinSet}~> _) ∘ finset_image_factor ≈ f.
Proof. intro a; apply fin_select_rank. Qed.

(* The chosen preimage of the q-th selected element of the image. / 所选图像的第 q 个元素的选定原像。 *)
Definition finset_image_witness (q : Fin.t finset_image_obj) : Fin.t m :=
  `1 (fin_existsb_sound
        (fun a : Fin.t m => fin_eqb (f a) (fin_select finset_hit q))
        (fin_select_sat finset_hit q)).

Lemma finset_image_witness_eq (q : Fin.t finset_image_obj) :
  f (finset_image_witness q) = fin_select finset_hit q.
Proof.
  apply fin_eqb_eq.
  exact (`2 (fin_existsb_sound
               (fun a : Fin.t m => fin_eqb (f a) (fin_select finset_hit q))
               (fin_select_sat finset_hit q))).
Qed.

Lemma finset_image_least (w : @SubObj FinSet n)
  (g : Fin.t m → Fin.t (sub_dom w)) (Hg : sub_mono w ∘ g ≈ f) :
  sub_le finset_image_sub w.
Proof.
  exists (fun q => g (finset_image_witness q)).
  intro q; simpl.
  transitivity (f (finset_image_witness q)).
  - exact (Hg (finset_image_witness q)).
  - exact (finset_image_witness_eq q).
Defined.

Definition FinSet_ImageOf : ImageOf (f : _ ~{FinSet}~> _) :=
  @Build_ImageOf FinSet m n f finset_image_sub finset_image_factor
    finset_image_commutes finset_image_least.

End FinSetImages.

#[export] Instance FinSet_HasImages : HasImages FinSet :=
  @Build_HasImages FinSet (@FinSet_ImageOf).

(* ------------------------------------------------------------------------ *)
(* * ** (c) Seven Sketches Exercise 1.11: merging versus tagging / * **（c）七个素描 练习1.11：合并与标记 *)

Definition fin4_0 : Fin.t 4 := Fin.F1.
Definition fin4_1 : Fin.t 4 := Fin.FS Fin.F1.
Definition fin4_2 : Fin.t 4 := Fin.FS (Fin.FS Fin.F1).
Definition fin4_3 : Fin.t 4 := Fin.FS (Fin.FS (Fin.FS Fin.F1)).

(*
 {0,1} and {1,2,3} inside the 4-element ambient object, cut out by
 decidable predicates so that [fin_select_inj] supplies monicity and the
 domains are counts that REDUCE. 

 --------
 {0,1} 和 {1,2,3} 位于 4 元素的环境对象内，由可判定谓词切割，以便 [fin_select_inj] 提供单射性，并且域是可以减少的计数。
*)
Definition ex11_u_pred : Fin.t 4 → bool :=
  fun i => (fin_eqb i fin4_0 || fin_eqb i fin4_1)%bool.

Definition ex11_v_pred : Fin.t 4 → bool :=
  fun i => (fin_eqb i fin4_1 || fin_eqb i fin4_2 || fin_eqb i fin4_3)%bool.

Lemma ex11_u_monic : Monic (fin_select ex11_u_pred : _ ~{FinSet}~> _).
Proof.
  constructor; intros z g1 g2 Hg i.
  exact (fin_select_inj ex11_u_pred (g1 i) (g2 i) (Hg i)).
Qed.

Lemma ex11_v_monic : Monic (fin_select ex11_v_pred : _ ~{FinSet}~> _).
Proof.
  constructor; intros z g1 g2 Hg i.
  exact (fin_select_inj ex11_v_pred (g1 i) (g2 i) (Hg i)).
Qed.

Definition ex11_u : @SubObj FinSet 4%nat :=
  @Build_SubObj FinSet 4%nat (fin_countP ex11_u_pred)
    (fin_select ex11_u_pred) ex11_u_monic.

Definition ex11_v : @SubObj FinSet 4%nat :=
  @Build_SubObj FinSet 4%nat (fin_countP ex11_v_pred)
    (fin_select ex11_v_pred) ex11_v_monic.

Example ex11_u_size : sub_dom ex11_u = 2%nat := eq_refl.
Example ex11_v_size : sub_dom ex11_v = 3%nat := eq_refl.

(*
 MERGING: the union inside the ambient 4-element object has four
 elements. 

 --------
 合并：环境四元素对象内部的并集有四个元素。
*)
Example ex11_union_four :
  sub_dom (sub_join ex11_u ex11_v) = 4%nat := eq_refl.

(* TAGGING: the coproduct of the two domains has five. / 标记：这两个领域的积对象有五个。 *)
Example ex11_coproduct_five :
  @Coprod FinSet FinSet_Cocartesian 2%nat 3%nat = 5%nat := eq_refl.

(* The intersection has one element. / 交集只有一个元素。 *)
Example ex11_meet_one :
  sub_dom (sub_meet ex11_u ex11_v) = 1%nat := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** (d) The arithmetic of Exercise 1.11, and the elements of Pow 2 / * **（d）练习 1.11 的算术，以及 Pow 2 的元素 *)

Example finset_pow_three : @Pow FinSet FinSet_Topos 3%nat = 8%nat := eq_refl.

Example finset_product_two_three :
  @product_obj FinSet FinSet_Cartesian 2%nat 3%nat = 6%nat := eq_refl.

(* The third arithmetic clause, 2 + 3 = 5, is [ex11_coproduct_five] above and is not restated here. / 第三个算术条款，2 + 3 = 5，如上所示 [ex11_coproduct_five]，并未在此重复说明。 *)

(*
 The four codes of the power object of 2, named by their POSITIONS in
 [Fin.t (Pow 2)] rather than by [fin_tabulate] of a characteristic
 function, and each read out through [finpow_mem] at both elements of
 the base.  [finpow_two_is_Pow] pins the two readings of the index type
 together.  The bit table is the enumeration:

 position 0 -> {0,1}   position 1 -> {0}
 position 2 -> {1}     position 3 -> {} 

 --------
 2 的幂对象的四个码，根据它们在 [Fin.t (Pow 2)] 中的位置命名，而不是根据特征函数的 [fin_tabulate] 命名，每个码通过 [finpow_mem] 在基的两个元素处读取。[finpow_two_is_Pow] 将索引类型的两个读取结果固定在一起。位表的枚举如下：

 位置 0 -> {0,1}   位置 1 -> {0}
 位置 2 -> {1}     位置 3 -> {}
*)

Example finpow_two_is_Pow : finpow 2%nat = @Pow FinSet FinSet_Topos 2%nat
  := eq_refl.

Definition powcode2_0 : Fin.t (finpow 2) := Fin.F1.
Definition powcode2_1 : Fin.t (finpow 2) := Fin.FS Fin.F1.
Definition powcode2_2 : Fin.t (finpow 2) := Fin.FS (Fin.FS Fin.F1).
Definition powcode2_3 : Fin.t (finpow 2) := Fin.FS (Fin.FS (Fin.FS Fin.F1)).

Definition fin2_0 : Fin.t 2 := Fin.F1.
Definition fin2_1 : Fin.t 2 := Fin.FS Fin.F1.

Example powcode2_0_at_0 : finpow_mem powcode2_0 fin2_0 = true  := eq_refl.
Example powcode2_0_at_1 : finpow_mem powcode2_0 fin2_1 = true  := eq_refl.
Example powcode2_1_at_0 : finpow_mem powcode2_1 fin2_0 = true  := eq_refl.
Example powcode2_1_at_1 : finpow_mem powcode2_1 fin2_1 = false := eq_refl.
Example powcode2_2_at_0 : finpow_mem powcode2_2 fin2_0 = false := eq_refl.
Example powcode2_2_at_1 : finpow_mem powcode2_2 fin2_1 = true  := eq_refl.
Example powcode2_3_at_0 : finpow_mem powcode2_3 fin2_0 = false := eq_refl.
Example powcode2_3_at_1 : finpow_mem powcode2_3 fin2_1 = false := eq_refl.
