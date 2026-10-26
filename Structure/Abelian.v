Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Classes.
Require Import Category.Theory.Orthogonality.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Additive.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Kernel.
Require Import Category.Structure.Factorization.
Require Import Category.Structure.Factorization.StrongEpi.
Require Import Category.Structure.Regular.

Generalizable All Variables.

(** * Abelian categories / * 阿贝尔范畴 *)

(*
 nLab:      https://ncatlab.org/nlab/show/abelian+category
 Wikipedia: https://en.wikipedia.org/wiki/Abelian_category

 An abelian category is an additive category in which every morphism has
 a kernel and a cokernel, every monomorphism is normal (it is a kernel),
 and every epimorphism is conormal (it is a cokernel).  [Abelian]
 packages exactly these data over the additive structure of
 Structure/Additive.v and the kernel/cokernel vocabulary of
 Structure/Kernel.v.  The normality fields pin each monomorphism as a
 kernel of its chosen cokernel and each epimorphism as a cokernel of its
 chosen kernel, spelled with the sigma projections of the
 [HasKernels]/[HasCokernels] choices; that this carries full generality
 is a theorem, not a remark: a kernel of anything is a kernel of every
 cokernel of itself ([kernel_of_any_cokernel] and its dual and their
 chosen-instance corollaries, Structure/Kernel.v).

 The development follows the classical route (Freyd, “Abelian
 Categories”; Borceux vol. 2, ch. 1):

 - [monic_iff_kernel_pzero] / [epic_iff_cokernel_pzero]: additivity
 turns the cancellation property into a vanishing test — a morphism f
 is monic exactly when every composite f ∘ u ≈ 0 forces u ≈ 0, and
 dually for epimorphisms.

 - The image factorization: for f : x ~> y, the kernel of the chosen
 cokernel of f is the image of f; f factors through it by kernel
 descent, the inclusion is monic, and the mediator is epic
 ([image_mediator_epic], the Freyd/Borceux diagram chase).  Hence
 every morphism factors as an epimorphism followed by a monomorphism
 ([abelian_epi_mono_factorization]).

 - [Abelian_OFS]: (Epi, Mono) is an orthogonal factorization system in
 the sense of Structure/Factorization.v.  The lifting half routes
 through Phase 8: every epimorphism is conormal, hence a regular
 epimorphism ([cokernel_regular_epi]), hence a strong one
 ([regular_epi_strong]), and strong epimorphisms lift uniquely
 against monomorphisms. 

 --------
 nLab：https://ncatlab.org/nlab/show/abelian+category
 维基百科：https://en.wikipedia.org/wiki/Abelian_category

 阿贝尔范畴是一种加法范畴，其中每个态射都满足
 一个核和一个余核，每个单射都是正规的（它是核），
 每个满射都是余正规的（它是余核）。[Abelian]
 将这些数据完全打包在 的加法结构上
 Structure/Additive.v 以及 的 kernel/cokernel 词汇表
 结构/核.v.正规性域将每个单射钉住为
 其所选余核的核，以及每个满态射作为其余核的余核
 选定核，用 的 σ 投影拼写
 [HasKernels] / [HasCokernels]选择;这具有完全的普遍性
 是一个定理，不是注释：任何事物的核都是每个的核
 自身的余核（[kernel_of_any_cokernel]及其对偶和它们
 选择实例推论，Structure/Kernel.v）。发展遵循经典路线 (Freyd, “Abelian Categories”；Borceux 第2卷，第1章) ：

 - [monic_iff_kernel_pzero] / [epic_iff_cokernel_pzero]：加法性
 将消去性质转化为消失测试——一个态射 f 当且仅当每个复合态射 f ∘ u ≈ 0 时强迫 u ≈ 0 时是单态射，对于满态射亦然。

 - 像分解：对于 f : x ~> y，选定余核的核是 f 的像；f 通过核下降因子分解，包含为单态射，中介态射为满态射 ([image_mediator_epic]，Freyd/Borceux 图表追踪)。因此，每个态射都可以分解为先满态射后单态射 ([abelian_epi_mono_factorization])。- [Abelian_OFS]：(Epi, Mono) 是 Structure/Factorization.v 意义下的一个正交分解系统。提举的半部分经过 Phase 8：每个满射都是余正规，因此是正规满射（[cokernel_regular_epi]），因此是强满射（[regular_epi_strong]），并且强满射相对于单射可以唯一提举。
*)

(*
 Where abelian categories come from, and what they are for

 nLab:      https://ncatlab.org/nlab/show/abelian+category
 Wikipedia: https://en.wikipedia.org/wiki/Grothendieck%27s_T%C3%B4hoku_paper

 Abelian categories are the axiomatic home of homological algebra: the
 common structure of the category Ab of abelian groups, the module
 categories R-Mod, vector spaces, and sheaves of abelian groups, in
 which one writes exact sequences, chain complexes, and derived functors
 (Wikipedia, “Abelian category”).  The notion accrued in three steps.
 Mac Lane observed that group-theoretic notions, reformulated purely
 through homomorphisms and their composition, exhibit a duality, and
 proposed an axiomatic context to exploit it, with the stated aim of
 making the proofs of homology exactly dual to those of cohomology (Mac
 Lane, “Duality for groups”, Bull. AMS 56, 1950).  Buchsbaum then gave
 essentially the modern definition under the name “exact category”, so
 that the Cartan-Eilenberg construction of derived functors carried over
 verbatim (Buchsbaum, “Exact categories and duality”, Trans. AMS 80(1),
 1955).  Grothendieck named the notion in the Tôhoku paper and organized
 it by the AB-axiom hierarchy, AB1 through AB5 and their formal duals
 (Grothendieck, “Sur quelques points d'algèbre homologique”, Tôhoku
 Math. J. 9(2), 1957).

 The axioms are invariant under C ↦ C^op, so every theorem has a dual
 for free — precisely Mac Lane's original goal, and the reason the
 normality clauses of [Abelian] come in mirror-image pairs.  The clause
 this file enforces, that every monomorphism is a kernel and every
 epimorphism is a cokernel, is what forces the canonical comparison from
 the coimage to the image of a morphism to be an isomorphism.  It follows
 that every morphism has an honest image and factors as an epimorphism
 followed by a monomorphism ([abelian_epi_mono_factorization], with
 [abelian_image_obj] the image object); that factorization is the engine
 of exactness.

 The decisive motivation was Grothendieck's.  Sheaf categories generally
 lack enough projectives, so the classical projective-resolution
 machinery does not apply there.  They do have injective resolutions,
 however, and these, in a Grothendieck category, meaning an AB5 category
 with a generator, put sheaf cohomology and module homology on one
 footing as derived functors (Wikipedia, “Grothendieck's Tôhoku paper”).
 On this base rest the Grothendieck spectral sequence for a composite of
 derived functors, the derived and triangulated categories of
 Grothendieck and Verdier, coherent duality announced at the 1958 ICM,
 and the Gabriel-Popescu theorem (1964) that every Grothendieck category
 is a localization of a module category.

 That module categories are the universal examples is itself a theorem.
 The Freyd-Mitchell embedding (Freyd, “Abelian Categories”, Thm 7.34,
 1964) places every small abelian category, by a full, faithful, exact
 functor, inside R-Mod for some ring R.  The consequence is a working
 method: an element-wise diagram chase valid in modules transfers
 verbatim to any small abelian category, which is the classical warrant
 for the diagram-chasing style in which the epic mediator
 [image_mediator_epic] and its neighbours are argued.

 The computational content sits in the additive substrate this file rests
 on ([abelian_additive], over Structure/Additive.v), not in the exactness
 clauses.  In any category with biproducts a morphism between direct sums
 is a matrix whose (k, j) entry is pₖ ∘ f ∘ iⱼ, composition is matrix
 multiplication over the addition on hom-setoids, and the biproduct
 relations pₖ ∘ iⱼ ≈ δₖⱼ and Σ iₖ ∘ pₖ ≈ id are the Kronecker-delta and
 completeness relations of linear algebra (nLab, “Biproduct”).  This
 enrichment is not extra data: by an Eckmann-Hilton argument a
 bicartesian category whose canonical comparison a ⊔ b ≅ a × b is
 invertible is already preadditive — one of the two semiadditivity
 theorems of Structure/Semiadditive.v — and the mere existence of any
 natural such isomorphism already forces that comparison to be invertible
 (Lack, 2009), with Instance/CMon.v the concrete matrix-calculus witness.
 The vanishing tests [monic_iff_kernel_pzero] and
 [epic_iff_cokernel_pzero] are the exact place where the abelian-group
 structure on homs — addition [padd] and zero [pzero] from
 Structure/Preadditive.v, negation [pneg] and difference [psub] from
 Structure/Additive.v — turns categorical cancellation into an algebraic
 computation against [zero_mor]. 

 --------
 阿贝尔范畴的来源以及它们的用途

 nLab:       https://ncatlab.org/nlab/show/abelian+category 
 维基百科:  https://en.wikipedia.org/wiki/Grothendieck%27s_T%C3%B4hoku_paper阿贝尔范畴是同调代数的公理化起点：是阿贝尔群范畴Ab、模范畴R-Mod、向量空间以及阿贝尔群层的共同结构，在这些范畴中可以书写正合序列、链复形和导出函子（维基百科，“阿贝尔范畴”）。这一概念经历了三个阶段的积累。麦克莱恩注意到，通过同态及其复合纯粹重述的群论概念展现出一种对偶性，并提出了一个公理化的背景以加以利用，其明确目标是使同调的证明与上同调的证明完全对偶（Mac Lane, “Duality for groups”, Bull. AMS 56, 1950）。然后，Buchsbaum 在“精确范畴”这个名称下给出了基本上现代的定义，从而 Cartan-Eilenberg 的导出函子构造可以逐字沿用（Buchsbaum，《精确范畴与对偶性》，Trans. AMS 80(1)，1955）。Grothendieck 在 Tôhoku 论文中命名了这一概念，并按 AB 公理层次 AB1 到 AB5 及其形式对偶进行组织（Grothendieck，《论同调代数的一些问题》，Tôhoku Math. J. 9(2)，1957）。公理在 C ↦ C^op 下保持不变，因此每一个定理都有一个免费的对偶——这正是 Mac Lane 最初的目标，也是 [Abelian] 的正规性条款成镜像配对的原因。本文件强制执行的条款是，每个单态射都是核，每个满态射都是余核，这就迫使从一个态射的余像到像的自然比较成为同构。因此，每个态射都有一个真实的像，并且可以分解为先是满态射再是单态射（[abelian_epi_mono_factorization]，其中 [abelian_image_obj] 为像对象）；这种分解是正合性的引擎。决定性的动机是格罗滕迪克的。层范畴通常缺乏足够的投射对象，因此经典的投射分解方法不适用于那里。然而，它们确实具有单射分解，并且在格罗滕迪克范畴中，即具有生成元的 AB5 范畴，这些单射分解将层上同调和模上同调作为导出函子置于同一立场（维基百科，“格罗滕迪克的 Tôhoku 论文”）。在此基础上建立了格罗滕迪克谱序列，用于导出函子的复合，格罗滕迪克和韦尔迪耶的导出及三角范畴，1958 年国际数学家大会宣布的相干对偶，以及加布里埃尔-波佩斯库定理（1964 年），即每个格罗滕迪克范畴都是模范畴的局部化。模范范畴是通用例子的这一点本身就是一个定理。Freyd-Mitchell 嵌入（Freyd，《阿贝尔范畴》，定理 7.34，1964）通过一个满且忠实的正合函子，将每个小阿贝尔范畴置于某个环 R 的 R-Mod 中。其结果是一个可行的方法：在模范中有效的逐元素图论推演可以原样转移到任何小阿贝尔范畴中，这也是在讨论其史诗般的媒介 [image_mediator_epic] 及其邻居时使用图论推演风格的经典依据。计算内容位于该文件所依赖的加性底层（[abelian_additive]，位于 Structure/Additive.v），而不在精确性条款中。在任何具有双积的范畴中，直接和之间的态射是一个矩阵，其 (k, j) 元为 pₖ ∘ f ∘ iⱼ，组成是基于同态集合上的加法的矩阵乘法，而双积关系 pₖ ∘ iⱼ ≈ δₖⱼ 和 Σ iₖ ∘ pₖ ≈ id 是线性代数的克罗内克δ和完备性关系（nLab，“Biproduct”）。这种
 丰富性并不是额外的数据：根据 Eckmann-Hilton 定理，一个正对偶范畴，其典型比较 a ⊔ b ≅ a × b 是可逆的，已经是预加性的——这是 Structure/Semiadditive.v 中两个半加性定理之一——而任何自然此类同构的存在已经迫使该比较是可逆的（Lack, 2009），Instance/CMon.v 是具体的矩阵计算实例。消失测试 [monic_iff_kernel_pzero] 和 [epic_iff_cokernel_pzero] 是恰恰在这里，态射上的阿贝尔群结构——来自 Structure/Preadditive.v 的加法 [padd] 和零元素 [pzero]，来自 Structure/Additive.v 的取负 [pneg] 和差 [psub]——将范畴论的消去转化为针对 [zero_mor] 的代数运算。
*)

Class Abelian (C : Category) := {
  abelian_additive : @Additive C;

  abelian_kernels :
    @HasKernels C (@additive_zero C abelian_additive);
  abelian_cokernels :
    @HasCokernels C (@additive_zero C abelian_additive);

  (* Every monomorphism is normal: a kernel of its chosen cokernel. / 每个单态射都是正规态射：它是其所选余核的核。 *)
  abelian_monic_normal {x y : C} (f : x ~> y) :
    Monic f → IsKernel (`1 (`2 (cokernel f))) f;

  (* Every epimorphism is conormal: a cokernel of its chosen kernel. / 每个上同态都是共法的：它是其所选核的余核。 *)
  abelian_epic_normal {x y : C} (f : x ~> y) :
    Epic f → IsCokernel (`1 (`2 (kernel f))) f
}.

#[export] Existing Instance abelian_additive.
#[export] Existing Instance abelian_kernels.
#[export] Existing Instance abelian_cokernels.

Section AbelianFacts.

Context {C : Category}.
Context `{A : @Abelian C}.

(* * ** Monic and epic as vanishing tests / * ** 单调而史诗般的逐渐消失的测试 *)

(*
 A morphism is monic exactly when its only vanishing test morphism is
 zero.  Forward: f ∘ u ≈ 0 ≈ f ∘ 0, cancel f.  Backward: if
 f ∘ g1 ≈ f ∘ g2 then f absorbs the difference g1 - g2, which the
 hypothesis then identifies with zero, and cancellation in the abelian
 group of homs recovers g1 ≈ g2. 

 --------
 当且仅当一个态射的唯一消失测试态射为零时，该态射是单射。正向：f ∘ u ≈ 0 ≈ f ∘ 0，消去 f。反向：如果 f ∘ g1 ≈ f ∘ g2，那么 f 吸收差 g1 - g2，而假设将其识别为零，并且在同态的阿贝尔群中消去可以恢复 g1 ≈ g2。
*)
Lemma monic_iff_kernel_pzero {x y : C} (f : x ~> y) :
  Monic f ↔ (∀ (z : C) (u : z ~> x), f ∘ u ≈ zero_mor → u ≈ zero_mor).
Proof.
  split.
  - intros Hm z u Hu.
    apply (@monic C x y f Hm z u zero_mor).
    rewrite Hu.
    symmetry.
    apply zero_mor_left.
  - intros H.
    constructor.
    intros z g1 g2 Hg.
    assert (Hd : f ∘ psub g1 g2 ≈ zero_mor).
    { unfold psub.
      rewrite compose_padd_left.
      rewrite compose_pneg_left.
      rewrite Hg.
      rewrite padd_pneg.
      apply pzero_zero_mor. }
    specialize (H z (psub g1 g2) Hd).
    unfold psub in H.
    apply (padd_cancel_right g1 g2 (pneg g2)).
    rewrite padd_pneg.
    rewrite H.
    symmetry.
    apply pzero_zero_mor.
Qed.

(*
 Dually, a morphism is epic exactly when its only vanishing test
 morphism out of its codomain is zero. 

 --------
 同样，当且仅当从其余域出的唯一消失的测试态射为零时，态射才是满射。
*)
Lemma epic_iff_cokernel_pzero {x y : C} (f : x ~> y) :
  Epic f ↔ (∀ (z : C) (u : y ~> z), u ∘ f ≈ zero_mor → u ≈ zero_mor).
Proof.
  split.
  - intros He z u Hu.
    apply (@epic C x y f He z u zero_mor).
    rewrite Hu.
    symmetry.
    apply zero_mor_right.
  - intros H.
    constructor.
    intros z g1 g2 Hg.
    assert (Hd : psub g1 g2 ∘ f ≈ zero_mor).
    { unfold psub.
      rewrite compose_padd_right.
      rewrite compose_pneg_right.
      rewrite Hg.
      rewrite padd_pneg.
      apply pzero_zero_mor. }
    specialize (H z (psub g1 g2) Hd).
    unfold psub in H.
    apply (padd_cancel_right g1 g2 (pneg g2)).
    rewrite padd_pneg.
    rewrite H.
    symmetry.
    apply pzero_zero_mor.
Qed.

(* * ** The chosen kernel, cokernel, and image / * ** 选定的核、余核和像 *)

Definition abelian_coker_obj {x y : C} (f : x ~> y) : C :=
  `1 (cokernel f).

Definition abelian_coker {x y : C} (f : x ~> y) : y ~> abelian_coker_obj f :=
  `1 (`2 (cokernel f)).

Definition abelian_coker_is {x y : C} (f : x ~> y) :
  IsCokernel f (abelian_coker f) :=
  `2 (`2 (cokernel f)).

Definition abelian_kernel_obj {x y : C} (f : x ~> y) : C :=
  `1 (kernel f).

Definition abelian_kernel {x y : C} (f : x ~> y) :
  abelian_kernel_obj f ~> x :=
  `1 (`2 (kernel f)).

Definition abelian_kernel_is {x y : C} (f : x ~> y) :
  IsKernel f (abelian_kernel f) :=
  `2 (`2 (kernel f)).

(* The normality fields, restated through the named accessors. / 通过命名访问器重新表达的正规性字段。 *)
Definition abelian_monic_is_kernel {x y : C} (f : x ~> y) (Hm : Monic f) :
  IsKernel (abelian_coker f) f :=
  abelian_monic_normal f Hm.

Definition abelian_epic_is_cokernel {x y : C} (f : x ~> y) (He : Epic f) :
  IsCokernel (abelian_kernel f) f :=
  abelian_epic_normal f He.

(* The image of f: the kernel of its chosen cokernel. / f 的像：其选定余核的核。 *)
Definition abelian_image_obj {x y : C} (f : x ~> y) : C :=
  abelian_kernel_obj (abelian_coker f).

Definition abelian_image {x y : C} (f : x ~> y) :
  abelian_image_obj f ~> y :=
  abelian_kernel (abelian_coker f).

Definition abelian_image_is {x y : C} (f : x ~> y) :
  IsKernel (abelian_coker f) (abelian_image f) :=
  abelian_kernel_is (abelian_coker f).

Lemma abelian_image_monic {x y : C} (f : x ~> y) : Monic (abelian_image f).
Proof. exact (kernel_monic (abelian_image_is f)). Qed.

(* f is absorbed by its cokernel, so it factors uniquely through the kernel of that cokernel: the mediator onto the image. / f 被它的余核吸收，因此它唯一地通过该余核的核因子分解：即指向像的中介。 *)
Definition abelian_image_med_ex {x y : C} (f : x ~> y) :
  ∃! w : x ~> abelian_image_obj f, abelian_image f ∘ w ≈ f :=
  kernel_desc (abelian_image_is f) f
    (cokernel_comp_zero (abelian_coker_is f)).

Definition abelian_image_med {x y : C} (f : x ~> y) :
  x ~> abelian_image_obj f :=
  unique_obj (abelian_image_med_ex f).

Lemma abelian_image_med_comm {x y : C} (f : x ~> y) :
  abelian_image f ∘ abelian_image_med f ≈ f.
Proof. exact (unique_property (abelian_image_med_ex f)). Qed.

(* * ** The mediator onto the image is epic / * ** 映像中的调解者很史诗 *)

(*
 The engine of [image_mediator_epic], with the auxiliary kernel and
 cokernel data abstracted.  Given t out of the image with
 t ∘ mediator ≈ 0, given a kernel j of t through which the mediator
 factors (via u), and given a cokernel r of the composite
 abelian_image f ∘ j of which that same composite is in turn the kernel
 (normality of the monomorphism abelian_image f ∘ j), conclude t ≈ 0.
 The instantiation with the chosen data happens in
 [image_mediator_epic] below. 

 --------
 [image_mediator_epic] 的引擎，包含抽象化的辅助核和余核数据。假设 t 在像中满足 t ∘ 中介 ≈ 0，且存在一个核 j 使 t 可以通过 j 经过中介（通过 u）因式分解，并且存在一个余核 r 对复合阿贝尔像 f ∘ j，使该复合又是其核（单态阿贝尔像 f ∘ j 的正规性），则可得出 t ≈ 0。带有所选数据的实例化发生在下面的 [image_mediator_epic] 中。
*)
Lemma image_mediator_epic_aux {x y : C} (f : x ~> y)
  {z : C} (t : abelian_image_obj f ~> z)
  {kt : C} (j : kt ~> abelian_image_obj f) (KJ : IsKernel t j)
  (u : x ~> kt) (Hu : j ∘ u ≈ abelian_image_med f)
  {c : C} (r : y ~> c)
  (CR : IsCokernel (abelian_image f ∘ j) r)
  (KN : IsKernel r (abelian_image f ∘ j)) :
  t ≈ zero_mor.
Proof.
  (*
 r absorbs f: f factors through abelian_image f ∘ j, which r
 coequalizes against zero. 

 --------
 r 吸收 f：f 通过 abelian_image f ∘ j 进行分解，而 r 对零进行等化。
*)
  assert (Hrf : r ∘ f ≈ zero_mor).
  { rewrite <- (abelian_image_med_comm f).
    rewrite <- Hu.
    rewrite comp_assoc.
    rewrite comp_assoc.
    rewrite <- (comp_assoc r (abelian_image f) j).
    rewrite (cokernel_comp_zero CR).
    apply zero_mor_right. }
  (* hence r descends through the chosen cokernel of f / 因此 r 通过 f 的选定余核下降 *)
  pose proof (cokernel_desc (abelian_coker_is f) r Hrf) as S.
  (* r absorbs the image inclusion as well, across the descent / r 也吸收图像的包含，在下降过程中 *)
  assert (Hrm : r ∘ abelian_image f ≈ zero_mor).
  { rewrite <- (unique_property S).
    rewrite <- comp_assoc.
    rewrite (kernel_comp_zero (abelian_image_is f)).
    apply zero_mor_left. }
  (*
 so the image inclusion factors through the kernel of r, which is
 abelian_image f ∘ j itself; cancelling the monic inclusion splits j 

 --------
 因此，像的包含通过 r 的核，它本身就是阿贝尔像 f ∘ j；消去单射包含就分裂了 j
*)
  pose proof (kernel_desc KN (abelian_image f) Hrm) as V.
  assert (Hjv : j ∘ unique_obj V ≈ id).
  { apply (@monic C (abelian_image_obj f) y (abelian_image f)
             (abelian_image_monic f)).
    rewrite comp_assoc.
    rewrite (unique_property V).
    rewrite id_right.
    reflexivity. }
  (* finally, t is absorbed by its own kernel's splitting / 最后，t 被其自身内核的分裂吸收 *)
  rewrite <- (id_right t).
  rewrite <- Hjv.
  rewrite comp_assoc.
  rewrite (kernel_comp_zero KJ).
  apply zero_mor_right.
Qed.

(*
 The mediator onto the image is an epimorphism (Freyd; Borceux vol. 2,
 Proposition 1.5.5).  Test t with t ∘ mediator ≈ 0; the mediator
 factors through the kernel j of t; the composite image ∘ j is monic,
 hence — by normality — the kernel of its own chosen cokernel r; r
 absorbs f, so it descends through the chosen cokernel of f and
 therefore absorbs the image inclusion; the inclusion then factors back
 through image ∘ j, splitting j; and a split-epic kernel of t forces
 t ≈ 0.  The vanishing test [epic_iff_cokernel_pzero] concludes. 

 --------
 该映像上的中介是一个满同态 (Freyd; Borceux 第2卷，第1.5.5命题)。用 t 测试 t ∘ 中介 ≈ 0；中介通过 t 的核 j 分解；复合映像 ∘ j 是单态，因此——根据正规性——是其自身选定余核 r 的核；r 吸收 f，所以它通过 f 的选定余核下降，因此吸收映像的包含；然后该包含再次通过映像 ∘ j 分解，使 j 分裂；而 t 的一个分裂满同态核迫使 t ≈ 0。消失测试 [epic_iff_cokernel_pzero] 结束。
*)
Lemma image_mediator_epic {x y : C} (f : x ~> y) :
  Epic (abelian_image_med f).
Proof.
  apply (snd (epic_iff_cokernel_pzero (abelian_image_med f))).
  intros z t Ht.
  destruct (kernel t) as [kt [j KJ]].
  pose proof (kernel_desc KJ (abelian_image_med f) Ht) as U.
  pose proof (monic_compose (abelian_image_monic f) (kernel_monic KJ))
    as Hmj.
  exact (image_mediator_epic_aux f t j KJ (unique_obj U)
           (unique_property U)
           (`1 (`2 (cokernel (abelian_image f ∘ j))))
           (`2 (`2 (cokernel (abelian_image f ∘ j))))
           (abelian_monic_normal (abelian_image f ∘ j) Hmj)).
Qed.

(** ** The epi–mono factorization / ** 上－单因子分解 *)

Theorem abelian_epi_mono_factorization {x y : C} (f : x ~> y) :
  ∃ (i : C) (e : x ~> i) (m : i ~> y),
    (Epic e) ∧ (Monic m) ∧ (m ∘ e ≈ f).
Proof using A C.
  exists (abelian_image_obj f), (abelian_image_med f), (abelian_image f).
  split.
  - exact (image_mediator_epic f).
  - split.
    + exact (abelian_image_monic f).
    + exact (abelian_image_med_comm f).
Qed.

(* * ** The (Epi, Mono) orthogonal factorization system / * ** （Epi，Mono）正交分解系统 *)

(* Epimorphisms transport along ≈: rewrite inside the cancellation. / 上同态沿 ≈ 传递：在消去中重写。 *)
Lemma epic_respects_equiv {x y : C} (f g : x ~> y) :
  f ≈ g → Epic f → Epic g.
Proof.
  intros Hfg He.
  constructor.
  intros z g1 g2 Hg.
  apply (@epic C x y f He z g1 g2).
  rewrite Hfg.
  exact Hg.
Qed.

(* Monomorphisms transport along ≈, dually. / 单射沿 ≈ 传递，反之亦然。 *)
Lemma monic_respects_equiv {x y : C} (f g : x ~> y) :
  f ≈ g → Monic f → Monic g.
Proof.
  intros Hfg Hm.
  constructor.
  intros z g1 g2 Hg.
  apply (@monic C x y f Hm z g1 g2).
  rewrite Hfg.
  exact Hg.
Qed.

(* The image factorization, packaged for the factorization system. / 图像分解，封装用于分解系统。 *)
Definition abelian_factorization {x y : C} (f : x ~> y) :
  Factorization f (@EpiClass C) (@MonoClass C) := {|
  fact_mid  := abelian_image_obj f;
  fact_e    := abelian_image_med f;
  fact_e_in := image_mediator_epic f;
  fact_m    := abelian_image f;
  fact_m_in := abelian_image_monic f;
  fact_comm := abelian_image_med_comm f
|}.

(*
 Every epimorphism is strong: it is conormal, hence a regular
 epimorphism, hence a strong one — the Phase 8 bridge. 

 --------
 每个上射都是强的：它是余正规，因此是正规上射，因此是强上射——第8阶段的桥梁。
*)
Lemma abelian_epic_strong {x y : C} (f : x ~> y) :
  Epic f → StrongEpi f.
Proof using A C.
  intros He.
  apply regular_epi_strong.
  exact (cokernel_regular_epi (abelian_epic_normal f He)).
Qed.

(* Epimorphisms lift uniquely against monomorphisms. / 上同态可以唯一地对单同态进行提升。 *)
Lemma abelian_epi_mono_ortho {a b u v : C} (e : a ~> b) (m : u ~> v) :
  Epic e → Monic m → e ⫫ m.
Proof using A C.
  intros He Hm.
  destruct (abelian_epic_strong e He) as [He' Hlift].
  exact (Hlift _ _ m Hm).
Qed.

(*
 The (Epi, Mono) orthogonal factorization system on an abelian
 category. 

 --------
 阿贝尔范畴上的 (Epi, Mono) 正交分解系统。
*)
Definition Abelian_OFS : OFS (@EpiClass C) (@MonoClass C) := {|
  ofs_e_respects := fun x y f g Hfg He => epic_respects_equiv f g Hfg He;
  ofs_m_respects := fun x y f g Hfg Hm => monic_respects_equiv f g Hfg Hm;
  ofs_factor     := fun x y f => abelian_factorization f;
  ofs_orth       := fun a b u v e m He Hm => abelian_epi_mono_ortho e m He Hm
|}.

End AbelianFacts.
