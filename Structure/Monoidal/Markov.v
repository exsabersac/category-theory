Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Semicartesian.
Require Import Category.Structure.Monoidal.CopyDiscard.
Require Import Category.Structure.Monoidal.CopyDiscard.Proofs.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.CommutativeComonoid.

Generalizable All Variables.

(*
   * * Markov categories

   A Markov category (Fritz, arXiv:1908.07021, §2) is a copy-discard
   (gs-monoidal) category whose monoidal unit [I] is terminal: a symmetric
   monoidal category equipped with a coherent commutative-comonoid supply
   [copy]/[discard] on every object ([CopyDiscard]) together with a
   [SemicartesianMonoidal] structure — a morphism [eliminate : x ~> I] for
   every [x], any two such morphisms agreeing ([unit_terminal]).

   Reading: a morphism [x ~> y] is a synthetic Markov kernel (a “channel”)
   from [x] to [y]; a morphism [I ~> x] is a state (a “distribution”) on
   [x]; [copy] duplicates and [discard] deletes an input.

   The class is redundancy-free, following Fritz's formulation: it carries
   NO axiom identifying [discard] with [eliminate] and NO naturality axiom
   for [discard].  In a semicartesian category ANY two morphisms into [I]
   agree, so both facts are corollaries ([markov_discard_eliminate],
   [discard_natural]), not axioms.

   What is deliberately absent is naturality of [copy]: a morphism [f]
   satisfying [copy ∘ f ≈ (f ⨂ f) ∘ copy] is precisely a DETERMINISTIC
   morphism (Cho–Jacobs; see CopyDiscard/Deterministic.v), and by Fox's
   theorem demanding this of every morphism collapses the category to a
   cartesian monoidal one (see Markov/Fox.v).  Conversely every cartesian
   monoidal category is a Markov category — [Markov_of_Cartesian] below —
   in which “all kernels are deterministic”: the degenerate, probability-
   free case.

   nLab:      https://ncatlab.org/nlab/show/Markov+category
   Reference: Fritz, “A synthetic approach to Markov kernels, conditional
   independence and theorems on sufficient statistics”,
   Adv. Math. 370:107239, 2020 (arXiv:1908.07021), §2
   Reference: Cho & Jacobs, “Disintegration and Bayesian inversion via
   string diagrams”, MSCS 29(7):938–971, 2019
   (arXiv:1709.00322) 

   --------
   * * 马尔可夫范畴

   马尔可夫范畴（Fritz, arXiv:1908.07021, §2）是一个拷贝-丢弃（gs-单体）范畴，其单体单位  [I]  是终对象：一个对称单体范畴，配备了在每个对象  [CopyDiscard]  上的相干交换余幺半群结构  [copy] / [discard] ，以及一个  [SemicartesianMonoidal]  结构——对于每个  [x]  的态射  [eliminate : x ~> I] ，任何两个这样的态射都一致（ [unit_terminal] ）。

   说明：态射  [x ~> y]  是从  [x]  到  [y] 的综合马尔可夫核（“通道”）；态射  [I ~> x]  是  [x] 上的状态（“分布”）；[copy]  复制输入，[discard]  删除输入。该类是无冗余的，遵循Fritz的表述：它不包含将[discard]与[eliminate]识别的公理，也不包含[discard]的自然性公理。在半笛卡尔范畴中，任意两个到[I]的态射都相等，因此这两个事实都是推论（[markov_discard_eliminate]，[discard_natural]），而非公理。

   刻意缺失的是[copy]的自然性：满足[copy ∘ f ≈ (f ⨂ f) ∘ copy]的态射[f]正是确定性态射（Cho–Jacobs；参见CopyDiscard/Deterministic.v），根据Fox定理，如果要求每个态射都满足这一点，则范畴会塌缩为笛卡尔幺半群范畴（参见Markov/Fox.v）。反之，每个笛卡尔幺半群范畴都是一个Markov范畴——下面的[Markov_of_Cartesian]——其中“所有核都是确定性的”：即简化的、无概率的情况。nLab:       https://ncatlab.org/nlab/show/Markov+category 
   参考文献: Fritz, “A synthetic approach to Markov kernels, conditional independence and theorems on sufficient statistics”, Adv. Math. 370:107239, 2020 (arXiv:1908.07021), §2
   参考文献: Cho & Jacobs, “Disintegration and Bayesian inversion via string diagrams”, MSCS 29(7):938–971, 2019 (arXiv:1709.00322)
*)

(*
 Where Markov categories come from, and what they are for

 nLab:  https://ncatlab.org/nlab/show/Stoch
 nLab:  https://ncatlab.org/nlab/show/Giry+monad

 The category that gives the subject its name is Stoch: objects are
 measurable spaces, morphisms are Markov kernels, identities are Dirac
 kernels, and composition is Chapman–Kolmogorov integration.  It precedes
 the axiomatics by decades: Lawvere circulated “The category of
 probabilistic mappings” as a manuscript in 1962, and Chentsov built the
 same category independently for statistics (Chentsov, “The categories of
 mathematical statistics”, Dokl. Akad. Nauk SSSR 164, 1965).  Stoch is
 the Kleisli category of the Giry monad (Giry, 1982, following Lawvere),
 and Kleisli categories of probability monads remain the standard source
 of models, alongside FinStoch for discrete probability and Gauss for
 Gaussian maps.  None of these is formalized in this library; the sole
 in-tree instance route is [Markov_of_Cartesian], so Stoch stands here as
 the intended model rather than a constructed one.

 The axiomatics was discovered twice before it was named, for unrelated
 ends.  Golubtsov axiomatized “categories of information transformers” —
 monoidal categories containing a deterministic subcategory with finite
 products — for informativeness comparison and decision problems
 (Golubtsov, “Axiomatic description of categories of information
 transformers”, Problemy Peredachi Informatsii 35(3):80–98, 1999), while
 Corradini and Gadducci reached the same copy/discard structure from
 term-graph rewriting, with no probabilistic intent (the gs-monoidal
 citation in Structure/Monoidal/CopyDiscard.v).  Cho and Jacobs then made
 the structure carry probability proper, expressing disintegration and
 Bayesian inversion as string diagrams (their paper cited above, first
 posted 2017), and Fritz's paper coined the name and set the program; its
 abstract presents the framework as following work of Golubtsov as well
 as Cho and Jacobs.  The boundary theorem predates the field: Fox proved
 in 1976 that natural coherent copying forces cartesianness (Fox,
 “Coalgebras and cartesian categories”, Comm. Algebra 4(7):665–667, 1976;
 Structure/Monoidal/Markov/Fox.v), which is why the absent naturality of
 [copy] noted above is the load-bearing design decision.

 The program the name announces is synthetic probability: a theorem
 proved once from the axioms holds in every model — discrete,
 measure-theoretic, Gaussian — with the measure theory quarantined inside
 the model construction.  Fritz's founding paper derives the
 Fisher–Neyman factorization theorem and the theorems of Basu and Bahadur
 on sufficient statistics; later work recovers the Kolmogorov and
 Hewitt–Savage zero-one laws (Fritz & Rischel, “Infinite products and
 zero-one laws in categorical probability”, Compositionality 2:3, 2020),
 de Finetti's theorem on exchangeable sequences (Fritz, Gonda & Perrone,
 “De Finetti's theorem in categorical probability”, J. Stochastic
 Analysis 2(4):6, 2021), and the ergodic decomposition theorem (Moss &
 Perrone, “A category-theoretic proof of the ergodic decomposition
 theorem”, Ergodic Theory Dynam. Systems 2023).  Beyond probability
 itself, an abstract form of the d-separation criterion of graphical
 causal models is proved at this generality, for possibilistic and
 deterministic networks alongside probabilistic ones (Fritz & Klingler,
 “The d-separation criterion in categorical probability”, JMLR
 24(46):1–49, 2023); a probabilistic language with exact conditioning
 takes its denotational semantics in categories built from the Markov
 categories Gauss and FinStoch (Stein & Staton, “Compositional semantics
 for probabilistic programs with exact conditioning”, LICS 2021); and
 Shannon and Rényi entropy are characterized as measures of how far a
 morphism is from being deterministic (Perrone, “Markov categories and
 entropy”, IEEE Trans. Inf. Theory 70(3), 2024).

 Computationally, a morphism is a call to a randomized procedure, and
 the two halves of the structure say what may be reordered around the
 call.  The discard half — running a computation and ignoring its result
 is the same as not running it — holds for every morphism by
 [discard_natural] and is the discard square of thunkability in
 Monad/Thunkable.v.  The copy half separates let x = f a in (x, x) from
 (f a, f a): one sample shared between two uses against two samples
 drawn independently.  Morphisms for which the two agree are exactly the
 deterministic ones ([deterministic] in
 Structure/Monoidal/CopyDiscard/Deterministic.v, with the wide
 subcategory [Det]), and the [state]/[marginal_left]/[marginal_right]
 vocabulary below makes the distinction speakable: copying a state
 yields a perfectly correlated joint, both of whose marginals return the
 original state ([marginal_left_copy], [marginal_right_copy]), not an
 independent pair. 

 --------
 马尔可夫范畴的来源及其用途

 nLab:   https://ncatlab.org/nlab/show/Stoch 
 nLab:   https://ncatlab.org/nlab/show/Giry+monad给该学科命名的范畴是 Stoch：对象是可测空间，态射是马尔可夫核，恒等映射是狄拉克核，复合是 Chapman–Kolmogorov 积分。它比公理化早几十年：Lawvere 在 1962 年散发了《概率映射的范畴》手稿，而 Chentsov 独立为统计学建立了相同的范畴（Chentsov，《数学统计的范畴》，Dokl. Akad. Nauk SSSR 164, 1965）。Stoch 是 Giry 上单子的 Kleisli 范畴（Giry, 1982，沿袭 Lawvere），而概率上单子的 Kleisli 范畴仍然是模型的标准来源，同时还有用于离散概率的 FinStoch 和用于高斯映射的 Gauss。这些在此库中都没有形式化；唯一的树内实例路径是 [Markov_of_Cartesian]，因此 Stoch 在这里作为预期的模型，而不是构建的模型。该公理体系在命名之前已经被发现过两次，用于无关的目的。Golubtsov为信息转换器的类别——包含具有有限积的确定性子类别的幺半群类别——建立了公理化，以用于信息量比较和决策问题（Golubtsov，《信息转换器类别的公理描述》，Problemy Peredachi Informatsii 35(3):80–98, 1999），而Corradini和Gadducci则通过项图重写得出了相同的复制/丢弃结构，但没有概率意图（参见Structure/Monoidal/CopyDiscard.v中的gs-monoidal引用）。Cho 和 Jacobs 随后使该结构具备适当的概率特性，将解体和贝叶斯逆转表示为字符串图（他们在上文引用的论文，首次发表于 2017 年），而 Fritz 的论文创造了该名称并制定了该计划；其摘要将该框架呈现为继承 Golubtsov 以及 Cho 和 Jacobs 的工作。边界定理早于该领域：Fox 在 1976 年证明，自然一致的复制强制笛卡尔性（Fox，“Coalgebras and cartesian categories”，Comm. Algebra 4(7):665–667, 1976；Structure/Monoidal/Markov/Fox.v），这就是为什么上文提到的 [copy] 的自然性缺失是承重的设计决策。该计划名称所宣称的是合成概率：一个从公理中一次性证明的定理在每个模型中都成立——离散的、测度理论的、高斯的——测度论被隔离在模型构造内部。Fritz 的奠基性论文推导了 Fisher–Neyman 分解定理以及 Basu 和 Bahadur 关于充分统计量的定理；后续工作恢复了 Kolmogorov 和 Hewitt–Savage 的零一律定理（Fritz & Rischel，“范畴概率中的无限积与零一律”，Compositionality 2:3, 2020），de Finetti 关于可交换序列的定理（Fritz, Gonda & Perrone，“范畴概率中的 de Finetti 定理”，J。随机分析 2(4):6, 2021)，以及遍历分解定理（Moss & Perrone，《遍历分解定理的范畴论证明》，遍历理论与动力系统 2023）。超越概率本身，对于图因果模型的 d 分离准则的抽象形式在这种普遍性下得到了证明，适用于可能性网络和确定性网络以及概率网络（Fritz & Klingler，《范畴概率中的 d 分离准则》，JMLR 24(46):1–49, 2023）；具有精确条件的概率语言在由马尔可夫范畴 Gauss 和 FinStoch 构建的范畴中获得其指称语义（Stein & Staton，《具有精确条件的概率程序的组合语义》，LICS 2021）；Shannon 熵和 Rényi 熵被表征为衡量一个态射偏离确定性的程度的量度（Perrone，《马尔可夫范畴与熵》，IEEE 信息论学报 70(3), 2024）。在计算上，态射是对随机化过程的调用，而结构的两半部分说明了调用周围可以重新排列的内容。丢弃部分——运行一个计算并忽略其结果与不运行它是相同的——对每个态射都成立，由 [discard_natural] 给出，并且是 Monad/Thunkable.v 中可延迟性的丢弃图。复制部分将 let x = f a in (x, x) 与 (f a, f a) 区分开：一个样本共享在两次使用之间，而不是两次独立抽取的样本。对于两者一致的态射，正是那些确定性的态射（在 Structure/Monoidal/CopyDiscard/Deterministic.v 中的 [deterministic]，以及其广子范畴 [Det]），而下列 [state] / [marginal_left] / [marginal_right] 词汇可以清楚地区分：复制一个状态会产生完全相关的联合状态，其边缘分布都返回原始状态（[marginal_left_copy]，[marginal_right_copy]），而不是独立的对。
*)

Section Markov.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Class MarkovCategory : Type := {
  (*
 The copy-discard structure: a commutative comonoid on every object,
 coherent with the tensor and the unit (but NOT natural). 

 --------
 复制-丢弃结构：每个对象上的交换余单子，与张量和单位相容（但不是自然的）。
*)
  markov_is_cd : @CopyDiscard C S;

  (*
 The unit [I] is terminal (the category is semicartesian / affine):
 synthetically, “probability distributions are normalized”. 

 --------
 单元 [I] 是终端的（类别是半笛卡尔/仿射的）：综合来看，“概率分布是归一化的”。
*)
  markov_semicartesian :
    @SemicartesianMonoidal C
      (@braided_is_monoidal C (@symmetric_is_braided C S))
}.
#[export] Existing Instance markov_is_cd.

Coercion markov_is_cd : MarkovCategory >-> CopyDiscard.

(* [markov_semicartesian] is deliberately NOT an [Existing Instance]: downstream files select it explicitly (mirroring how [cd_comonoid] is accessed by projection), keeping typeclass resolution from picking a semicartesian structure the caller did not ask for. / [markov_semicartesian] 故意不是 [Existing Instance]：下游文件明确选择它（类似于 [cd_comonoid] 被投影访问的方式），从而防止类型类解析选择调用者未请求的半笛卡尔结构。 *)

Context `{M : MarkovCategory}.

(*
 Discarding IS eliminating: both are morphisms into the terminal [I].
 Some presentations of Markov categories take this identification as an
 axiom; in Fritz's redundancy-free formulation it is a corollary of
 terminality. 

 --------
 丢弃就是消除：两者都是到终对象 [I] 的态射。一些马克洛夫范畴的表述将这种同一性作为公理；在 Fritz 的无冗余表述中，它是终性（terminality）的一个推论。
*)
Corollary markov_discard_eliminate {x : C} :
  discard[x] ≈ @eliminate C _ markov_semicartesian x.
Proof. apply (@unit_terminal C _ markov_semicartesian). Qed.

(*
 Naturality of discard — “delete after doing anything is delete” — is
 likewise a corollary of terminality, never an axiom. 

 --------
 丢弃的自然性——“做完任何事情后删除就是删除”——同样是终结性的推论，绝不是公理。
*)
Corollary discard_natural {x y : C} (f : x ~> y) :
  discard[y] ∘ f ≈ discard[x].
Proof. apply (@unit_terminal C _ markov_semicartesian). Qed.

(*
   * ** States and marginals

   Vocabulary for the probability track: a [state] on [x] is a morphism
   out of the unit, and the marginals of a joint state are obtained by
   discarding one factor of the tensor (the projections of
   Semicartesian.v).  The lemmas below are phrased through [state]. 

   --------
   * ** 状态和边缘分布

   概率部分的词汇：在 [x] 上的 [state] 是一个从单位出发的态射，联合状态的边缘通过舍弃张量的一个因子（Semicartesian.v 的投影）来获得。下面的引理是通过 [state] 表述的。
*)

Definition state (x : C) : Type := I ~> x.

(* Normalization: every state has total mass one. / 归一化：每个状态的总质量为一。 *)
Lemma state_discard {x : C} (s : state x) :
  discard[x] ∘ s ≈ id[I].
Proof. apply (@unit_terminal C _ markov_semicartesian). Qed.

Definition marginal_left {x y : C} (s : state (x ⨂ y)%object) : state x :=
  @proj_left C _ markov_semicartesian x y ∘ s.

Definition marginal_right {x y : C} (s : state (x ⨂ y)%object) : state y :=
  @proj_right C _ markov_semicartesian x y ∘ s.

#[export] Program Instance marginal_left_respects {x y : C} :
  Proper (equiv ==> equiv) (@marginal_left x y).
Next Obligation.
  proper.
  unfold marginal_left.
  rewrites.
  reflexivity.
Qed.

#[export] Program Instance marginal_right_respects {x y : C} :
  Proper (equiv ==> equiv) (@marginal_right x y).
Next Obligation.
  proper.
  unfold marginal_right.
  rewrites.
  reflexivity.
Qed.

(*
 Copying then discarding one of the two copies is the identity: the
 comonoid counit laws, with [eliminate] traded for [discard] by
 terminality of [I]. 

 --------
 复制然后丢弃其中一个副本就是恒等式：余单元的余模律，通过  [I] 的终端性，将  [eliminate]  换成  [discard] 。
*)

Lemma proj_left_copy {x : C} :
  @proj_left C _ markov_semicartesian x x ∘ copy[x] ≈ id[x].
Proof.
  unfold proj_left.
  rewrite <- markov_discard_eliminate.
  rewrite <- comp_assoc.
  unfold copy, discard, ccomon_delta, ccomon_epsilon.
  rewrite delta_counit_right.
  apply iso_to_from.
Qed.

Lemma proj_right_copy {x : C} :
  @proj_right C _ markov_semicartesian x x ∘ copy[x] ≈ id[x].
Proof.
  unfold proj_right.
  rewrite <- markov_discard_eliminate.
  rewrite <- comp_assoc.
  unfold copy, discard, ccomon_delta, ccomon_epsilon.
  rewrite delta_counit_left.
  apply iso_to_from.
Qed.

(*
 Both marginals of a copied state recover the state: copying is a
 (synthetic) diagonal coupling. 

 --------
 被复制状态的两个边际恢复该状态：复制是一种（综合的）对角耦合。
*)

Lemma marginal_left_copy {x : C} (s : state x) :
  marginal_left (copy[x] ∘ s) ≈ s.
Proof.
  unfold marginal_left.
  rewrite comp_assoc.
  rewrite proj_left_copy.
  apply id_left.
Qed.

Lemma marginal_right_copy {x : C} (s : state x) :
  marginal_right (copy[x] ∘ s) ≈ s.
Proof.
  unfold marginal_right.
  rewrite comp_assoc.
  rewrite proj_right_copy.
  apply id_left.
Qed.

End Markov.

Arguments MarkovCategory C {S}.

Section MarkovCartesian.

Context {C : Category}.
Context `{H : @CartesianMonoidal C}.

(*
 Every cartesian monoidal category is a Markov category: Fox's
 projection laws make the diagonal and [eliminate] a coherent comonoid
 supply ([CD_of_Cartesian]), and the unit is terminal by definition. 

 --------
 每个笛卡尔单范畴都是马尔可夫范畴：福克斯的投影律使对角图和 [eliminate] 成为一个相容的余单体提供（[CD_of_Cartesian]），并且单位根据定义是终端的。
*)
Program Definition Markov_of_Cartesian :
  @MarkovCategory C
    (@relevance_is_symmetric C (@cartesian_is_relevance C H)) := {|
  markov_is_cd := @CD_of_Cartesian C H;
  markov_semicartesian := @cartesian_is_semicartesian C H
|}.

End MarkovCartesian.
