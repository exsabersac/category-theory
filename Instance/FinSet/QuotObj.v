Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Pushout.
Require Import Category.Instance.FinSet.Regular.
Require Import Category.Instance.FinSet.Subobject.

Generalizable All Variables.

(* * * Quotient objects of a finite set: the meet that computes / * * 有限集合的商对象：计算的交 *)

(*
 nLab:      https://ncatlab.org/nlab/show/quotient+object
 nLab:      https://ncatlab.org/nlab/show/coimage
 nLab:      https://ncatlab.org/nlab/show/FinSet
 Wikipedia: https://en.wikipedia.org/wiki/Quotient_object

 Mac Lane, “Categories for the Working Mathematician”, 2nd ed. (GTM 5),
 §V.7, book p. 126 (PDF p. 135), Definition 3.  Theory/Subobject/
 Quotient.v carries the definition; Instance/Sets/QuotObj.v carries the
 setoid witness and Instance/Grp/QuotObj.v Mac Lane's group
 illustration.  What the SKELETON adds, and what neither of the other
 two can, is COMPUTATION: the objects of FinSet are natural numbers and
 its morphisms are plain functions on [Fin.t], so a quotient object's
 codomain is a number that reduces and the binary meet can be read back
 by [eq_refl] with no tactic.

 WHAT IS DELIVERED.

 (1) The onto clause, both ways and unconditionally, from
 Instance/FinSet/Classifier.v's [finset_epic_iff_surjective].  No
 stability hypothesis, unlike [Grp]: the probe there is the
 classifier's own characteristic map into Ω = 2 and the search over a
 finite set is decidable, so the backward leg hands back the preimage.
 [finset_no_quot_of_const] records the other side -- not every map out
 of an object presents a quotient object -- positively, by naming
 Instance/FinSet/Classifier.v's refutation for the constant map
 1 → 2, because a refutation probe on [mk_quot f _] would report an
 uninstantiated evar and not the mathematical fact.

 (2) COIMAGES, as [ImageOf]s in [FinSet^op], with [FinSet_HasCoimages]
 the class form -- an [#[export] Instance], so that
 [HasImages (FinSet^op)] resolves by class search; an audit found the
 first draft a plain [Definition].  FinSet is balanced, and the
 construction says so
 concretely: the coimage of f IS the image object of
 Instance/FinSet/Subobject.v with the image FACTOR as its
 epi and the image MONO as the map to the codomain, so
 [finset_coimage_commutes] is that file's [finset_image_commutes]
 VERBATIM -- the image factorization of f read in [FinSet^op] is
 already its coimage factorization, with no transport at all.  Only
 [im_least] does work, and only because it must choose preimages under
 a competing epi; [fin_rank_resp] (Instance/FinSet/Pushout.v)
 discharges the proof argument of [fin_rank] from decidable equality of
 booleans, so no proof irrelevance and no axiom enters.

 (3) A MEET THAT COMPUTES.  [quot_meet] at FinSet is the PUSHOUT of the
 two epis, supplied by Instance/FinSet/Pushout.v's union-find
 [FinSet_HasPushouts].  Take the two surjections 4 ↠ 3 that identify
 {0,1} and {1,2} respectively; their pushout identifies {0,1,2} and
 leaves 3 alone, and [finset_quot_meet_two] states
 [quot_cod finset_q_meet = 2%nat] by [eq_refl] -- no [vm_compute], no
 tactic.  [finset_quot_meet_merges_0_2] and
 [finset_quot_meet_merges_1_2] read the identifications off the EPI of
 the meet, again by [eq_refl], and [finset_quot_meet_separates_0_3]
 refutes the collapse by [discriminate].  Both factors are pinned at 3
 ([finset_q01_three], [finset_q12_three]) so the meet is visibly a
 coarsening of each.  Two coimage cardinalities are pinned the same
 way.  Leibniz equality is the right relation for every one of these:
 the claims are about DATA -- a natural number, an element of
 [Fin.t 2] -- and FinSet's hom-setoid is pointwise Leibniz in any case.
 Nothing about a [QuotObj] itself is claimed at `=`; the [QuotObj]
 setoid has no antisymmetry here any more than at [Sets], and the
 corresponding readback is measured REFUSED (CONVERSION).

 MEASUREMENTS, each re-runnable.  24 constants
 (grep -E '^(def|prf|thm|ind|constr|proj|class|inst|meth|rec|corec|ax|
 defax) ' on the .glob), no [Program] so
 [strings … .vo | grep obligation] returns nothing, and all 24 report
 “Closed under the global context” under [Print Assumptions] -- the
 union-find pushout, the rank/select codec and the classifier probe all
 stay axiom-free.  0 [Defined] and 6 [Qed]: nothing here needs to be
 transparent, because every computing readback goes through
 [Definition]s and record projections and not through a proof term.
 The requirement closure is 91 files (iterated over .Makefile.coq.d),
 of which Instance/FinSet/Regular.v contributes exactly ONE -- it is
 required only for its [fin3_cases], whose own requirements (Lib,
 Theory/Category, Theory/Morphisms, Theory/Isomorphism,
 Instance/FinSet) are already here.  No name introduced here occurs
 anywhere else in the tree (swept over all .glob files with
 '^[a-z]+ [0-9:]+ [^ ]* NAME$', instrument-checked on [sub_le]; a first
 draft named the three codomain elements [fin3_0], [fin3_1], [fin3_2]
 and restated [fin3_cases], and the sweep found
 Structure/Limit/Power/Hom.v and Instance/FinSet/Regular.v,
 so the elements are now written with bare constructors and the case
 analysis is required rather than duplicated).  Universes, by [About]:
 [finset_q_meet] binds [FinSet] and carries a [Set <] bound, which is
 FinSet's own -- its objects are [nat] -- and not introduced here; the
 [SubObj] hom-equals-proof collapse is inherited from
 Theory/Subobject.v exactly as at [Sets] and [Grp].

 NOT DELIVERED.  No JOIN of quotient objects at FinSet, and no lattice
 laws: those are transports of Theory/Subobject/Lattice.v at
 [FinSet^op] and belong wherever that transport lands.  No general
 count of the quotient objects of [n] (the Bell numbers), and no
 enumeration of them.  No claim that [FinSet_HasCoimages] and
 Instance/FinSet/Subobject.v's [FinSet_HasImages] assemble a
 factorization system, nor that the coimage is ISOMORPHIC to the image
 as a general theorem -- here the two share an object by construction,
 which is a fact about this particular presentation of the image and
 not a statement of balancedness.  No wide (indexed) meet.  No
 [Decategorify] reading of a quotient object as a partition, though
 Instance/FinSet/Decategorify.v exists.  No timing claim: that the
 [eq_refl]s above typecheck is measured, that they are fast is not. 

 --------
 nLab：       https://ncatlab.org/nlab/show/quotient+object 
 nLab：       https://ncatlab.org/nlab/show/coimage 
 nLab：       https://ncatlab.org/nlab/show/FinSet 
 维基百科：  https://en.wikipedia.org/wiki/Quotient_object 

 Mac Lane，《为工作数学家准备的范畴论》，第二版（GTM 5），
 §V.7，第126页（PDF第135页），定义3。Theory/Subobject/
 Quotient.v 包含定义；Instance/Sets/QuotObj.v 包含集合证据，Instance/Grp/QuotObj.v 包含 Mac Lane 的群示例。SKELETON 所增加的，以及其他两个都无法提供的，是计算：FinSet 的对象是自然数，其态射是 [Fin.t] 上的普通函数，因此商对象的余域是可化简的数字，且二元交可以通过 [eq_refl] 读回，无需策略。

 所提供的内容。(1) 全射子句，无条件且双向地，从 Instance/FinSet/Classifier.v 的 [finset_epic_iff_surjective]。没有稳定性假设，不同于 [Grp]：那里的探针是分类器自身的特征映射到 Ω = 2，并且对有限集合的搜索是可判定的，因此回溯部分会返回原像。[finset_no_quot_of_const] 记录了另一面——并非每个从对象出的映射都呈现出商对象——通过命名 Instance/FinSet/Classifier.v 对常数映射 1 → 2 的反证方式来积极地表示，因为在 [mk_quot f _] 上的反证探针会报告一个未实例化的 evar，而不是数学事实。(2) COIMAGES，如同在 [FinSet^op] 中的 [ImageOf]，带有 [FinSet_HasCoimages] 类形式——一个 [#[export] 实例，因此 [HasImages (FinSet^op)] 通过类搜索来解析；一次审计发现初稿是一个普通的 [Definition]。FinSet 是平衡的，并且构造明确说明了这一点：f 的余像是 Instance/FinSet/Subobject.v 的像对象，其像因子作为其 epi，而像单射作为到余域的映射，因此 [finset_coimage_commutes] 是该文件的 [finset_image_commutes] 原文——在 [FinSet^op] 中读取的 f 的像分解已经是其余像分解，完全不需要任何转换。只有 [im_least] 有效，而且仅仅因为它必须在竞争的满射下选择原像；[fin_rank_resp]（Instance/FinSet/Pushout.v）依赖布尔值的可判等性来处理 [fin_rank] 的证明论证，因此没有使用证明无关性，也没有使用公理。(3) 一个会计算的会合。[quot_meet] 在 FinSet 中是两个满射的推积，由 Instance/FinSet/Pushout.v 的并查集 [FinSet_HasPushouts] 提供。取两个满射 4 ↠ 3，分别将 {0,1} 和 {1,2} 识别；它们的推积将 {0,1,2} 识别在一起，并保持 3 独立，[finset_quot_meet_two] 说明 [quot_cod finset_q_meet = 2%nat] 通过 [eq_refl] ——没有 [vm_compute]，也没有策略。[finset_quot_meet_merges_0_2] 和 [finset_quot_meet_merges_1_2] 根据 [eq_refl] 再次从会合的 EPI 中读取识别，而 [finset_quot_meet_separates_0_3] 通过 [discriminate] 反驳了塌缩。两个因子都固定在 3（[finset_q01_three]、[finset_q12_three]），因此该会合显然是每个的一个粗化。两个余像的基数以相同方式固定。莱布尼兹等式是以下每一项的正确关系：这些主张是关于数据的——一个自然数，一个 [Fin.t 2] 的元素——而且 FinSet 的同态集合无论如何都是逐点莱布尼兹的。在 `=` 上并没有关于 [QuotObj] 本身的主张；[QuotObj] 集合在这里没有反对称性，就像在 [Sets] 上一样，而且相应的读回被测量为拒绝（转换）。测量，每个都可以重新运行。24 个常量（在 .glob 上使用 grep -E '^(def|prf|thm|ind|constr|proj|class|inst|meth|rec|corec|ax|defax) '），没有 [Program]，因此 [strings … .vo | grep obligation] 返回空，并且所有 24 个在 [Print Assumptions] 下都报告“在全局上下文下封闭”——并查集 pushout、秩/选择编解码器和分类器探测器都保持无公理。0 [Defined] 和 6 [Qed]：这里没有需要透明的，因为每次计算回读都通过 [Definition] 和记录投影，而不是通过证明项。需求闭包是91个文件（在.Makefile.coq.d中迭代），其中Instance/FinSet/Regular.v正好贡献了一个——它只为其[fin3_cases]所需要，其自身的需求（Lib、Theory/Category、Theory/Morphisms、Theory/Isomorphism、Instance/FinSet）已经在这里。这里引入的任何名称在树的其他地方都不存在（在所有.glob文件上扫描 '^ [a-z] +  [0-9:] +  [^ ] * NAME$'，在[sub_le]上进行了工具检查；一个初稿将三个伴随域元素命名为[fin3_0]、[fin3_1]、[fin3_2]并重述[fin3_cases]，并且扫描结果找到Structure/Limit/Power/Hom.v和Instance/FinSet/Regular.v，因此这些元素现在以裸构造器形式书写，并且案例分析是必需的而不是重复的）。宇宙，由 [About] ：
 [finset_q_meet] 绑定 [FinSet] 并携带一个 [Set <] 绑定，它是 FinSet 自有的 —— 它的对象是 [nat] —— 并未在此引入；
 [SubObj] 同构等价证明的崩溃继承自 Theory/Subobject.v，正如在 [Sets] 和 [Grp] 所示。未交付。在 FinSet 中没有商对象的 JOIN，也没有格律：那些是 Theory/Subobject/Lattice.v 在 [FinSet^op] 的搬运，并且属于该搬运到达的任何地方。没有 [n] 的商对象的一般计数（贝尔数），也没有对它们的枚举。没有声称 [FinSet_HasCoimages] 和 Instance/FinSet/Subobject.v 的 [FinSet_HasImages] 组成一个分解系统，也没有声称余像作为一般定理与像同构——这里两者通过构造共享一个对象，这是关于这个图像特定呈现的事实，而不是平衡性的陈述。没有宽（索引）交。没有将商对象作为分割的 [Decategorify] 阅读，尽管 Instance/FinSet/Decategorify.v 存在。不作时间声明：上面的 [eq_refl] 类型检查是有测量的，但它们速度快则没有测量。
*)

(* * ** “Epis are onto” in the skeleton / * ** “Epis 已经准备好” 在骨架里 *)

(*
 Instance/FinSet/Classifier.v's biconditional, both legs.  Unlike
 [Grp], FinSet needs no stability hypothesis: the probe is the
 classifier's own characteristic map into Ω = 2 and the search over a
 finite set is decidable, so the preimage comes back as data. 

 --------
 Instance/FinSet/Classifier.v 的双条件，两边。不同于 [Grp]，FinSet 不需要稳定性假设：探针是分类器自身映射到 Ω = 2 的特征映射，并且对有限集合的搜索是可判定的，所以原像会作为数据返回。
*)
Definition finset_quot_epi_surjective {m : nat} (q : @QuotObj FinSet m) :
  ∀ b : Fin.t (quot_cod q), ∃ a : Fin.t m, quot_epi q a = b :=
  snd (finset_epic_iff_surjective (quot_epi q)) (quot_is_epic q).

Definition finset_quot_of_surjection {m n : nat} (e : m ~{FinSet}~> n)
  (Hs : ∀ b : Fin.t n, ∃ a : Fin.t m, e a = b) : @QuotObj FinSet m :=
  mk_quot e (fst (finset_epic_iff_surjective e) Hs).

(*
 Not every map presents a quotient object.  Stated positively, because
 a refutation probe on [mk_quot f _] would report an uninstantiated
 evar and not the mathematical refusal: the constant map 1 → 2 is not epic
 (Instance/FinSet/Classifier.v).  This is a verbatim RE-EXPORT of
 that lemma under a name saying what it is used for here; it proves
 nothing new. 

 --------
 并非每个映射都呈现出商对象。积极地说，因为对 [mk_quot f _] 的反驳探针会报告一个未实例化的 evar，而不是数学上的拒绝：常数映射 1 → 2 不是满射 (Instance/FinSet/Classifier.v)。这是该引理的逐字重导出，用一个说明其在此处用途的名字；它并未证明任何新的内容。
*)
Definition finset_no_quot_of_const :
  Epic ((fun _ => fin_true) : 1%nat ~{FinSet}~> 2%nat) → False :=
  finset_const_true_not_epic.

(* * ** Coimages: FinSet is balanced, so the coimage is the image / * ** 余像：FinSet 是平衡的，因此余像就是像 *)

Section FinSetCoimages.

Context {m n : nat}.
Context (f : Fin.t m → Fin.t n).

(*
 Instance/FinSet/Subobject.v's [finset_image_factor] is surjective
 onto the image object: the q-th selected element has a preimage
 (that file's [finset_image_witness], with its defining equation), and
 ranking after selecting is the identity
 (Instance/FinSet/Pushout.v's [fin_rank_select]).  [fin_rank_resp]
 discharges the proof argument, so no proof irrelevance and no
 axiom is needed. 

 --------
 Instance/FinSet/Subobject.v 的 [finset_image_factor] 是到像对象的满射：第 q 个选中的元素有一个原像（该文件的 [finset_image_witness] 及其定义方程），并且选择后的排序是恒等映射（Instance/FinSet/Pushout.v 的 [fin_rank_select]）。[fin_rank_resp] 解除证明论证，因此不需要证明无关性，也不需要公理。
*)
Lemma finset_coimage_epic :
  Epic (finset_image_factor f : m ~{FinSet}~> finset_image_obj f).
Proof.
  apply (fst (finset_epic_iff_surjective _)).
  intro q.
  exists (finset_image_witness f q).
  unfold finset_image_factor.
  transitivity (fin_rank (finset_hit f) (fin_select (finset_hit f) q)
                  (fin_select_sat (finset_hit f) q)).
  - apply fin_rank_resp.
    exact (finset_image_witness_eq f q).
  - apply fin_rank_select.
Qed.

Definition finset_coimage : @QuotObj FinSet m :=
  mk_quot (finset_image_factor f : m ~{FinSet}~> finset_image_obj f)
    finset_coimage_epic.

(* The triangle is Instance/FinSet/Subobject.v's [finset_image_commutes] VERBATIM: the image factorization read in [FinSet^op] is the coimage factorization, no transport. / 三角形是 Instance/FinSet/Subobject.v 的 [finset_image_commutes] VERBATIM: 读取的像分解 [FinSet^op] 是余像分解，没有传输。 *)
Lemma finset_coimage_commutes :
  sub_mono finset_coimage ∘[FinSet^op] (finset_image_mono f) ≈ f.
Proof. exact (finset_image_commutes f). Qed.

(*
 Minimality.  A competing quotient e : m ↠ Q through which f factors
 is surjective, so a preimage of each of its points can be chosen; two
 preimages of the same point have the same f-value, hence the same
 rank, and [fin_rank_resp] turns that into the required equation. 

 --------
 最小性。一个竞争商 e : m ↠ Q，通过它 f 可以分解，是满射的，因此可以为其每个点选择一个原像；同一点的两个原像具有相同的 f 值，因此具有相同的秩，而 [fin_rank_resp] 将其变为所需的方程。
*)
Lemma finset_coimage_least (w : @QuotObj FinSet m)
  (g : n ~{FinSet^op}~> quot_cod w)
  (Hg : sub_mono w ∘[FinSet^op] g ≈ f) :
  @sub_le (FinSet^op) m finset_coimage w.
Proof.
  exists (fun p => finset_image_factor f
            (`1 (finset_quot_epi_surjective w p))).
  intro a; simpl.
  unfold finset_image_factor.
  apply fin_rank_resp.
  transitivity (g (quot_epi w (`1 (finset_quot_epi_surjective w
                                     (quot_epi w a))))).
  - symmetry; exact (Hg _).
  - rewrite (`2 (finset_quot_epi_surjective w (quot_epi w a))).
    exact (Hg a).
Qed.

Definition FinSet_CoimageOf : @ImageOf (FinSet^op) n m f :=
  @Build_ImageOf (FinSet^op) n m f finset_coimage (finset_image_mono f)
    finset_coimage_commutes finset_coimage_least.

End FinSetCoimages.

(*
 As at [Sets], the anonymous record literal is refused here and the
 constructor is named with its category argument explicit. 

 --------
 截至 [Sets]，这里的匿名记录字面量被拒绝，并且构造函数用其类别参数显式命名。
*)
#[export] Instance FinSet_HasCoimages : @HasImages (FinSet^op) :=
  @Build_HasImages (FinSet^op) (fun n m f => @FinSet_CoimageOf m n f).

(* * ** Two quotients of the four-element set, and a meet that computes / * ** 四元素集合的两个商，以及一个计算交的操作 *)

(*
 The three-element codomain is written with bare [Fin] constructors:
 naming its elements [fin3_0], [fin3_1], [fin3_2] would collide with
 Structure/Limit/Power/Hom.v, and the exhaustive case analysis
 is Instance/FinSet/Regular.v's [fin3_cases], required rather than
 restated (it adds exactly ONE file to this file's closure, its own
 requirements being a subset of what is already here). 

 --------
 三元素余域使用裸的 [Fin] 构造器表示：
 为其元素命名 [fin3_0]、[fin3_1]、[fin3_2] 会与 Structure/Limit/Power/Hom.v 冲突，而穷尽情况分析
 则在 Instance/FinSet/Regular.v 的 [fin3_cases] 中进行，需要使用而不是重新说明（它只向此文件的闭包中添加了一个文件，其自身的依赖是已经存在内容的子集）。
*)

(* Identify 0 with 1, keeping 2 and 3 apart. / 将0与1认作一体，保持2和3分开。 *)
Definition finset_merge01 : Fin.t 4 → Fin.t 3 := fun i =>
  if fin_eqb i fin4_0 then Fin.F1
  else if fin_eqb i fin4_1 then Fin.F1
  else if fin_eqb i fin4_2 then Fin.FS Fin.F1
  else Fin.FS (Fin.FS Fin.F1).

(* ... and identify 1 with 2, keeping 0 and 3 apart. / ... 并将 1 与 2 配对，同时将 0 和 3 分开。 *)
Definition finset_merge12 : Fin.t 4 → Fin.t 3 := fun i =>
  if fin_eqb i fin4_0 then Fin.F1
  else if fin_eqb i fin4_1 then Fin.FS Fin.F1
  else if fin_eqb i fin4_2 then Fin.FS Fin.F1
  else Fin.FS (Fin.FS Fin.F1).

Lemma finset_merge01_surj :
  ∀ b : Fin.t 3, ∃ a : Fin.t 4, finset_merge01 a = b.
Proof.
  intro b; destruct (fin3_cases b) as [H|[H|H]]; subst.
  - exists fin4_0; reflexivity.
  - exists fin4_2; reflexivity.
  - exists fin4_3; reflexivity.
Qed.

Lemma finset_merge12_surj :
  ∀ b : Fin.t 3, ∃ a : Fin.t 4, finset_merge12 a = b.
Proof.
  intro b; destruct (fin3_cases b) as [H|[H|H]]; subst.
  - exists fin4_0; reflexivity.
  - exists fin4_1; reflexivity.
  - exists fin4_3; reflexivity.
Qed.

Definition finset_q01 : @QuotObj FinSet 4%nat :=
  finset_quot_of_surjection finset_merge01 finset_merge01_surj.

Definition finset_q12 : @QuotObj FinSet 4%nat :=
  finset_quot_of_surjection finset_merge12 finset_merge12_surj.

(* The stub's [quot_meet] at FinSet, which is the PUSHOUT of the two epis (Instance/FinSet/Pushout.v, apex by union-find on the 3 + 3 tagged elements over the four span edges). / 该存根在 FinSet 中的 [quot_meet]，是两个 epi 的推挤积（Instance/FinSet/Pushout.v，通过对四个跨度边上的 3 + 3 个标记元素使用并查集求顶点）。 *)
Definition finset_q_meet : @QuotObj FinSet 4%nat :=
  @quot_meet FinSet FinSet_HasPushouts 4%nat finset_q01 finset_q12.

(*
 And it COMPUTES.  Merging {0,1} and merging {1,2} together merge
 {0,1,2}, leaving 3 alone: two classes, by [eq_refl] with no tactic.
 This is a statement about the DATA (a natural number), which is why
 Leibniz equality is the right relation here. 

 --------
 它会计算。将 {0,1} 合并并将 {1,2} 合并在一起得到 {0,1,2}，将 3 单独留下：由 [eq_refl] 无策略的两个类。这是关于数据（一个自然数）的陈述，这就是为什么莱布尼茨等式在这里是正确的关系。
*)
Example finset_quot_meet_two : quot_cod finset_q_meet = 2%nat := eq_refl.

(* The epi of the meet computes too, on elements of [Fin.t 4]. / 该会面的终极同态也在 [Fin.t 4] 的元素上进行计算。 *)
Example finset_quot_meet_merges_0_2 :
  quot_epi finset_q_meet fin4_0 = quot_epi finset_q_meet fin4_2 := eq_refl.

Example finset_quot_meet_merges_1_2 :
  quot_epi finset_q_meet fin4_1 = quot_epi finset_q_meet fin4_2 := eq_refl.

(* ... and it does not collapse everything: 3 stays apart from 0. / ... 它不会将所有内容都塌缩：3 与 0 保持分开。 *)
Lemma finset_quot_meet_separates_0_3 :
  quot_epi finset_q_meet fin4_0 = quot_epi finset_q_meet fin4_3 → False.
Proof. intro H; discriminate H. Qed.

(*
 Neither factor alone has two elements, so the meet is a genuine
 coarsening of both. 

 --------
 单独的任何一个因子都没有两个元素，所以它们的交集是两者的真正粗化。
*)
Example finset_q01_three : quot_cod finset_q01 = 3%nat := eq_refl.
Example finset_q12_three : quot_cod finset_q12 = 3%nat := eq_refl.

(*
 The coimage of a collapsing map, computed: [finset_merge01] hits all
 three elements of its codomain, so its coimage has three elements and
 is the map itself up to the identification of the image with 3. 

 --------
 一个塌缩映射的共像，计算得出：[finset_merge01] 命中其陪域的所有三个元素，所以它的共像有三个元素，并且是该映射本身，直到将像与 3 进行对应。
*)
Example finset_coimage_merge01_three :
  quot_cod (finset_coimage finset_merge01) = 3%nat := eq_refl.

(*
 ... while a map that misses a value has a smaller coimage than its
 codomain: the constant map 4 → 3 has a one-element coimage. 

 --------
 ……而一个缺少某个值的映射，其余像比其陪域要小：常值映射 4 → 3 的余像只有一个元素。
*)
Example finset_coimage_const_one :
  quot_cod (finset_coimage (fun _ : Fin.t 4 => (Fin.FS Fin.F1 : Fin.t 3)))
  = 1%nat := eq_refl.
