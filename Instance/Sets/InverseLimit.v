Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Chain.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cone.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cartesian.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Streams.

Generalizable All Variables.

(*
 Category.Functor.Opposite opens [functor_scope], after which a bare
 [Omega^op] in an ASCRIPTION (no expected type to bind the scope)
 parses as [Opposite_Functor Omega] and dies naming neither culprit.
 Reopening [category_scope] is the tree's guard for this. 

 --------
 Category.Functor.Opposite 打开 [functor_scope]，之后在 ASCRIPTION 中的一个裸 [Omega^op]（没有用于绑定作用域的期望类型）被解析为 [Opposite_Functor Omega] 并在没有指出责任者的情况下出错。重新打开 [category_scope] 是此树的保护措施。
*)
Open Scope category_scope.

(* Obligations are written out rather than left to the tree default, so that each [intros] pattern is predictable -- the Instance/Sets/Cone.v idiom. / 义务是明确写出的，而不是依赖树的默认值，这样每个 [intros] 模式都是可预测的——Instance/Sets/Cone.v 习语。 *)
#[local] Obligation Tactic := idtac.

(* * * Inverse limits of towers of sets / * * 集合塔的逆极限 *)

(*
 Mac Lane, _Categories for the Working Mathematician_, 2nd ed. (GTM 5),
 Springer 1998, §V.1, book p. 109 (PDF pp. 118-119), construction 1.
 Riehl, _Category Theory in Context_, Dover 2016, §3.1 Definition 3.1.21
 (printed p. 88) and §3.2 Example 3.2.8 (printed p. 95).

 nLab:      https://ncatlab.org/nlab/show/inverse+limit
 Wikipedia: https://en.wikipedia.org/wiki/Inverse_limit

 A TOWER of sets is a diagram indexed by the opposite of the ordinal
 omega,

 F 0  <--  F 1  <--  F 2  <--  ...

 and Mac Lane's inverse (projective) limit of it is the set of MATCHING
 STRINGS: sequences [x] with [x n : F n] whose successive entries are
 carried to one another by the transition maps.  His observation is that
 a matching string is exactly a cone from the one-point set, which is
 why the general cone-set formula of §V.1 Theorem 1 specialises to the
 familiar description.  Both halves are delivered here: the matching
 strings as an object with its projections and universal property, and
 the identification with the cone set.

 WHAT WAS ALREADY IN TREE, AND THE ISSUE'S OWN SURVEY IS STALE ON THREE
 COUNTS.  Issue #408's “Current state” says (a) that [Sets] has no
 indexed products and that [HasIndexedProducts] “has zero instances
 tree-wide”, (b) that the compatible-family idiom “exists only at the
 end/wedge shape”, and (c) that no functor out of [Omega^op] into [Sets]
 is anywhere shown to have a limit.  Re-measured at 067ee4eb: (a) and
 (b) are FALSE and (c) is accurate but answered by one application.
 [Instance/Sets/Products.v] declares
 [Sets_HasIndexedProducts : @HasIndexedProducts Sets] -- one of THREE
 UNCONDITIONAL inhabitants at a named category, with
 [Two_Sets_HasIndexedProducts] and [One_HasIndexedProducts]; the
 criterion matters, since a fourth constant,
 [Instance/Fun/Terminal.v]'s [Fun_HasIndexedProducts], concludes
 [HasIndexedProducts] CONDITIONALLY on one.  [Instance/Sets/Complete.v]'s
 [Sets_limit_compatible] and [Sets_limit_obj] are the compatible-family
 predicate and setoid AT ARBITRARY SHAPE, not only at the end/wedge.
 And (c) is right about what the tree
 STATES -- no constant of type [Limit F] for [F : Omega^op ⟶ Sets]
 existed -- but it costs NO WORK, [Sets_Complete (Omega^op) F]
 elaborating as it stands.

 SO THE INCREMENT IS NOT EXISTENCE, IT IS THE PRESENTATION.  What no
 in-tree statement had was the tower's own description -- compatibility
 at the SUCCESSOR STEPS ONLY -- and the theorem that it agrees with the
 general one, which quantifies over EVERY arrow of [Omega^op], i.e. over
 every proof of an inequality.  That bridge is [tower_compat_all], one
 induction on [Instance/Omega.v]'s [le_t], and it is the exact
 analogue of Instance/Sets/Cone.v's [tuple_compat_paths] (generators to
 paths) one shape along.

 READ THAT AT ITS SCOPE.  It is the only proof with content in sections
 (A)-(D) EXCEPT for [tower_obj]'s own [Equivalence] obligation, which is
 a short script and not an evident map; and section (H) adds two further
 inductions of its own, [stream_trunc_compat] and
 [stream_trunc_respects].  Counted by tactic, exactly FOUR scripts in
 the file run to more than three tactics and every other one is a single
 [exact] or [reflexivity].  An “only new proof content in the file”
 claim would be false, and the sibling file Instance/Sets/Cone.v carried
 exactly that defect until an audit caught it.

 THE STEP DECOMPOSITION IS DEFINITIONAL, WHICH IS WHY THE BRIDGE IS
 SHORT.  [Omega]'s composition is [le_t_trans g f] and [le_t_trans]
 recurses on its SECOND argument, so in [Omega^op] the composite
 [f' ∘ tower_step k] reduces by two iota steps to [le_t_S f'] -- the
 very constructor the induction is peeling.  [fmap_comp] therefore
 applies with no rewriting of the index, and the successor case is one
 [fmap_comp], one step hypothesis and the induction hypothesis.

 [Cochain] STOPS BEING DEAD CODE.  Construction/Chain.v declares
 [Cochain F := (Chain (F^op))^op : Omega^op ⟶ C], the tower
 [1 <- F 1 <- F² 1 <- ...] of an endofunctor with a terminal object, and
 before this file it was used NOWHERE -- [rg -l Cochain] returned that
 file alone.  Section (E) gives it its first consumer.

 WHAT IS NOT SPECIAL ABOUT TOWERS, said plainly so no reader infers
 otherwise: nothing below uses any property of [Omega] except that its
 arrows are generated by the steps.  The general limit
 [Sets_Limit F : Limit F] applies at every shape, this one included; the
 tower case adds a presentation, not a construction.  The corresponding
 statement at an ARBITRARY index category is [Sets_Limit] itself, and
 [tower_iso] is the comparison between the two presentations at this
 shape.

 STREAMS, AND WHAT IS AND IS NOT CLAIMED ABOUT THEM.  Riehl's §3.2
 Example 3.2.8 names the compatible-sequence description; the canonical
 instance of it is the stream tower [1 <- A <- A² <- ...], which is
 [Cochain (StreamF A)].  Section (H) builds that tower's inverse limit
 and the comparison map [stream_to_tower], a stream to its string of
 truncations, with its coordinates read back at [eq_refl].  It is NOT
 proved invertible: the inverse is a corecursive assembly of a stream
 from a matching string plus two round trips up to bisimilarity, a
 larger development, so nothing here says the inverse limit IS
 Instance/Sets/Streams.v's final coalgebra [Stream_final].  The
 closure cost of reaching the streams at all is THREE modules (89 to
 92, measured), so the deferral is about proof content and not about
 dependencies.

 THREE SCOPE NOTES, each recording a reading NOT delivered.

 * Riehl's Definition 3.1.21 phrases a cone over a tower as a diagram of
 shape [(ω+1)^op], the tower extended by a new bottom object.  That
 reading is NOT built here: the library's generic [Cone]/[ACone]
 (Structure/Cone.v) is used instead, whose apex is an object of the
 target rather than an extra index.  The two agree in the sense that a
 cone in either sense is the same data -- an apex with a leg at each
 [n] commuting with the transitions -- but no functor [(ω+1)^op ⟶ Sets]
 is formed and no comparison is proved, because [Instance/Omega.v]
 carries no [ω+1].

 * Riehl adds that the same holds for any limit ordinal in place of ω.
 [Instance/Omega.v] is nat-indexed only and the tree has no
 TRANSFINITE machinery -- [Instance/Ordinal.v]'s [Ordinal n] is the
 FINITE ordinals and [Omega] is omega, so the issue's own “no ordinal
 machinery”, which an earlier revision of this note copied, is too
 broad -- and the generalisation is not statable here, nor attempted.

 * The tower is over [Sets].  Nothing here is claimed for a general
 target category: the construction reads elements, which is what the
 compatible-family presentation of [Instance/Sets/Complete.v] gives
 and what an arbitrary category does not. 

 --------
 Mac Lane，《为工作数学家准备的范畴论》，第2版（GTM 5），施普林格 1998，第V.1节，书本第109页（PDF第118-119页），构造1。
 Riehl，《语境中的范畴论》，多佛 2016，第3.1节 定义3.1.21（印刷第88页）和第3.2节 示例3.2.8（印刷第95页）。

 nLab：https://ncatlab.org/nlab/show/inverse+limit
 维基百科：https://en.wikipedia.org/wiki/Inverse_limit

 一个集合的塔是由序数ω的对偶索引的图：

 F 0  <--  F 1  <--  F 2  <--  ...而 Mac Lane 的逆（射影）极限就是这些匹配字符串的集合：序列 [x] 与 [x n : F n]，其中的连续项通过过渡映射相互对应。他的观察是，匹配字符串恰好是来自单点集合的余锥，这就是为什么 §V.1 定理 1 的一般余锥集合公式特化为熟悉的描述。在这里呈现了两部分内容：匹配字符串作为具有其投影和泛性质的对象，以及与余锥集合的对应关系。树中已经存在的内容，以及问题自身的调查在三个方面已经过时。问题 #408 的“当前状态”指出 (a) [Sets] 没有被索引的产品，并且 [HasIndexedProducts] “在整个树中没有实例”，(b) 兼容族习语“仅存在于末端/楔形”，以及 (c) 从 [Omega^op] 到 [Sets] 的函子没有显示有极限。在 067ee4eb 进行重新测量后：(a) 和 (b) 是错误的，而 (c) 是准确的，但仅通过一个应用得出。[Instance/Sets/Products.v] 声明了 [Sets_HasIndexedProducts : @HasIndexedProducts Sets] —— 在命名范畴中三个无条件元素之一，还有 [Two_Sets_HasIndexedProducts] 和 [One_HasIndexedProducts]；该标准很重要，因为第四个常量 [Instance/Fun/Terminal.v] 的 [Fun_HasIndexedProducts] 条件地得出 [HasIndexedProducts]。[Instance/Sets/Complete.v] 的 [Sets_limit_compatible] 和 [Sets_limit_obj] 是任意形状下的兼容族谓词和集合体，而不仅仅是在末端/楔形。而且 (c) 关于树所陈述的内容是正确的——不存在类型为 [Limit F] 的 [F : Omega^op ⟶ Sets] 常量——但是按现状展开 [Sets_Complete (Omega^op) F] 并不费力。

 因此增量不是存在性，而是表述。树内没有的一点是塔自身的描述——仅在后继步兼容——以及它与一般描述一致的定理，该描述量化于 [Omega^op] 的每条箭头，即量化于每个不等式证明。这个桥梁是 [tower_compat_all]，对 [Instance/Omega.v] 的 [le_t] 进行一次归纳，它正是 Instance/Sets/Cone.v 中 [tuple_compat_paths]（从生成元到路径）沿单一形状的对应物。按照其范围阅读。 它是唯一在 (A)-(D) 节中有内容的证明，除了 [tower_obj] 自己的 [Equivalence] 义务，这是一个短脚本，并不是明显的映射；而 (H) 节又增加了它自己的两个归纳，[stream_trunc_compat] 和 [stream_trunc_respects]。按策略计算，文件中恰好有四个脚本超过三个策略运行，而其他的都是单个 [exact] 或 [reflexivity]。声称“文件中只有新的证明内容”是错误的，兄弟文件 Instance/Sets/Cone.v 就存在这个缺陷，直到审计发现它为止。步骤分解是定义性的，这就是桥短的原因。[Omega] 的组成是 [le_t_trans g f] 和 [le_t_trans] 对其第二个参数进行递归，因此在 [Omega^op] 中，复合的 [f' ∘ tower_step k] 经过两个 iota 步骤简化为 [le_t_S f'] ——正是归纳正在剥离的构造器。因此，[fmap_comp] 应用时无需重写索引，后继情况是一个 [fmap_comp]、一步假设和归纳假设。

 [Cochain] 不再是死代码。Construction/Chain.v 声明了 [Cochain F := (Chain (F^op))^op : Omega^op ⟶ C]，一个具有终对象的自函子塔 [1 <- F 1 <- F² 1 <- ...]，并且在此文件之前，它从未被使用 —— [rg -l Cochain] 仅返回了那个文件。(E) 节给了它第一个使用者。塔没有什么特别之处，明说以免读者产生误解：下面没有使用 [Omega] 的任何特性，除了它的箭头是由步骤生成的。一般的限制 [Sets_Limit F : Limit F] 适用于每一个形状，包括这一种；塔的情况增加了一种呈现，而不是一种构造。在任意指标范畴下对应的陈述是 [Sets_Limit] 本身，而 [tower_iso] 是该形状下两种呈现之间的比较。流，以及关于它们的声明与非声明。Riehl的§3.2
 例子3.2.8给出了兼容序列描述；它的典型实例是流塔 [1 <- A <- A² <- ...]，它是
 [Cochain (StreamF A)]。部分(H)构建了该塔的逆极限和比较映射 [stream_to_tower]，一个流到它的截断串的映射，其坐标在 [eq_refl] 处被读取。它未被证明可逆：逆映射是从匹配字符串加两次双向往返形成流的核心递归组装，一个更大的发展，因此这里没有说明逆极限就是 Instance/Sets/Streams.v 的终结余代数 [Stream_final]。
 到达这些流的闭包代价为三个模块（测量为89到92），所以推迟的是关于证明内容，而不是关于依赖性。三个范围注释，每个都记录了一个未给出的解释。

 * Riehl 的定义 3.1.21 将塔上的圆锥表述为形状为 [(ω+1)^op] 的图表，即塔通过一个新的底部对象扩展。这里没有构建该解释：而是使用库中通用的 [Cone] / [ACone]（Structure/Cone.v），其顶点是目标中的一个对象，而不是额外的索引。两者在意义上是一致的，即无论哪种方式的圆锥都是相同的数据——一个顶点以及在每个 [n] 处的一个边与转换相交换——但没有形成函子 [(ω+1)^op ⟶ Sets]，也没有证明比较关系，因为 [Instance/Omega.v] 不携带 [ω+1]。* Riehl 补充说，对于将 ω 替换为任何极限序数的情况也是成立的。  
 [Instance/Omega.v] 仅是自然数索引的，并且该树没有跨越顺序的机制——[Instance/Ordinal.v] 的 [Ordinal n] 是有限序数，[Omega] 是 ω，因此其本身的“无序数机制”问题（本注释的早期版本也有引用）过于宽泛——而且这里无法表述一般化，也未尝试。  

 * 该塔位于 [Sets] 上。此处并未对一般目标范畴提出任何声明：构造读取元素，这正是 [Instance/Sets/Complete.v] 的兼容族表述提供的，而任意范畴并不提供。
*)

(* * ** (A) The tower's own compatibility condition / * ** (A) 塔自身的兼容性条件 *)

Section Tower.

Context (F : Omega^op ⟶ Sets).

(*
 The generating arrow of the tower, read in [Omega^op]: it runs DOWN,
 from stage [S n] to stage [n].  It IS [Instance/Omega.v]'s
 [omega_step], the same proof term read in the opposite category. 

 --------
 塔的生成箭头，在 [Omega^op] 中读取：它向下运行，从阶段 [S n] 到阶段 [n]。它是 [Instance/Omega.v] 的 [omega_step]，在相反的范畴中读取的相同证明项。
*)
Definition tower_step (n : nat) : @hom (Omega^op) (S n) n := omega_step n.

(*
 Read this at its true strength: [tower_step] is DEFINED as
 [omega_step], so the readback holds by DELTA and pins that the
 definition is unchanged, not that anything computes.  It is kept as
 that guard, on the Theory/Universal/Element.v precedent
 ([setsone_is_terminal], disclosed there the same way). 

 --------
 以其真实的力度阅读此内容：[tower_step] 被定义为 [omega_step]，因此通过 DELTA 的回读成立，并且确认定义未改变，而不是说有什么被计算。它被保留为该守卫，依据 Theory/Universal/Element.v 的先例（[setsone_is_terminal]，也以相同的方式在那里披露）。
*)
Example tower_step_is_omega_step (n : nat) :
  tower_step n = omega_step n := eq_refl.

(*
 THE MECHANISM THE BRIDGE BELOW TURNS ON, MACHINE-CHECKED RATHER THAN
 ASSERTED: composing an arrow of [Omega^op] with the step is the [le_t_S]
 constructor, ON THE NOSE.  [Omega]'s composition is [le_t_trans g f] and
 [le_t_trans] recurses on its SECOND argument, so two iota steps do it. 

 --------
 下面桥梁启动的机制，是机器检查而非断言：将 [Omega^op] 的箭头与步骤组合，是 [le_t_S] 构造函数，就在鼻子上。[Omega] 的组合是 [le_t_trans g f]，而 [le_t_trans] 在其第二个参数上递归，所以两个 iota 步骤就完成了它。
*)
Example step_is_le_t_S (m k : nat) (f : @hom (Omega^op) k m) :
  @compose (Omega^op) (S k) k m f (tower_step k) = le_t_S f := eq_refl.

(*
 Mac Lane's matching-string condition: successive entries are carried to
 one another.  Compare [Sets_limit_compatible] (Instance/Sets/
 Complete.v), which quantifies over EVERY arrow of the shape. 

 --------
 Mac Lane 的匹配字符串条件：连续的条目相互传递。比较 [Sets_limit_compatible]（Instance/Sets/Complete.v），它对该形状的每一条箭头进行量化。
*)
Definition tower_compat (x : Sets_iprod_obj (fun n : nat => F n)) : Type :=
  ∀ n : nat, fmap[F] (tower_step n) (x (S n)) ≈ x n.

(* The product the two presentations are cut out of is one and the same. / 这两个演示所裁切的产品是同一个。 *)
Example tower_inner_strict :
  Sets_iprod_obj (fun d : Omega^op => F d)
  = Sets_iprod_obj (fun n : nat => F n) := eq_refl.

(*
 THE BRIDGE -- see the header for its scope: it is the only proof with
 content in sections (A)-(D) apart from [tower_obj]'s setoid obligation,
 and section (H) adds two more.  A family
 family matching at each step matches along every arrow.  The successor
 case turns on the definitional identity
 [f' ∘ tower_step k = le_t_S f'] described in the header. 

 --------
 桥——请参见标题了解其范围：在 (A)-(D) 节中，它是唯一有内容的证明，除了 [tower_obj] 的集合公理义务外，(H) 节又增加了两个。每一步的族匹配沿每个箭头进行匹配。后继情况取决于标题中描述的 [f' ∘ tower_step k = le_t_S f'] 的定义性同一性。
*)
Lemma tower_compat_all (x : Sets_iprod_obj (fun n : nat => F n))
  (H : tower_compat x) {m n : nat} (f : @hom (Omega^op) n m) :
  fmap[F] f (x n) ≈ x m.
Proof.
  induction f as [| k f' IH].
  - exact (@fmap_id _ _ F m (x m)).
  - transitivity (fmap[F] f' (fmap[F] (tower_step k) (x (S k)))).
    + exact (@fmap_comp _ _ F (S k) k m f' (tower_step k) (x (S k))).
    + transitivity (fmap[F] f' (x k)).
      * apply proper_morphism; exact (H k).
      * exact IH.
Qed.

(* * ** (B) The set of matching strings, and its projections / * **（B）匹配字符串的集合及其投影 *)

Program Definition tower_obj : obj[Sets] := {|
  carrier   := { x : Sets_iprod_obj (fun n : nat => F n) & tower_compat x };
  is_setoid := {| equiv := fun p q => `1 p ≈ `1 q |}
|}.
Next Obligation.
  constructor.
  - intros p n; reflexivity.
  - intros p q Hpq n; symmetry; exact (Hpq n).
  - intros p q r Hpq Hqr n; transitivity (`1 q n);
    [exact (Hpq n)|exact (Hqr n)].
Qed.

(* “with the coordinate projections as the legs”. / “以坐标投影作为边” *)
Program Definition tower_proj (n : nat) : tower_obj ~{Sets}~> F n := {|
  morphism := fun p => `1 p n
|}.
Next Obligation. intros n p q Hpq; exact (Hpq n). Qed.

(*
 An element of the inverse limit is determined by its coordinates: this
 is the definition of [tower_obj]'s setoid, restated in the form a
 consumer wants. 

 --------
 逆极限的一个元素由其坐标决定：这是 [tower_obj] 的集合类型的定义，以消费者想要的形式重新表述。
*)
Lemma tower_ext (p q : tower_obj) :
  (∀ n : nat, tower_proj n p ≈ tower_proj n q) → p ≈ q.
Proof. intros Hn n; exact (Hn n). Qed.

(* * ** (C) The two presentations agree / * ** (C) 这两个呈现一致 *)

Program Definition tower_fwd :
  Sets_limit_obj F ~{Sets}~> tower_obj := {|
  morphism := fun p => (`1 p ; fun n => _)
|}.
Next Obligation. intros p n; exact (`2 p (S n) n (tower_step n)). Defined.
Next Obligation. intros p q Hpq n; exact (Hpq n). Qed.

Program Definition tower_bwd :
  tower_obj ~{Sets}~> Sets_limit_obj F := {|
  morphism := fun p => (`1 p ; fun m n f => _)
|}.
Next Obligation.
  intros p m n f; exact (tower_compat_all (`1 p) (`2 p) f).
Defined.
Next Obligation. intros p q Hpq n; exact (Hpq n). Qed.

(* The compatible-family limit IS the set of matching strings. / 兼容家庭的极限是匹配字符串的集合。 *)
Program Definition tower_iso :
  @Isomorphism Sets (Sets_limit_obj F) tower_obj := {|
  to := tower_fwd; from := tower_bwd
|}.
Next Obligation. intros p n; reflexivity. Qed.
Next Obligation. intros p n; reflexivity. Qed.

(* * ** (D) The matching strings are a limit / * ** (D) 匹配的字符串是一个限制 *)

Program Definition tower_acone : ACone tower_obj F := {|
  vertex_map := tower_proj
|}.
Next Obligation. intros m n f p; exact (tower_compat_all (`1 p) (`2 p) f). Qed.

Definition tower_cone : Cone F :=
  {| vertex_obj := tower_obj; coneFrom := tower_acone |}.

(* The mediator out of a competing cone: bundle its legs at a point, whose step compatibility is the cone's own coherence read at [tower_step]. / 来自竞争锥体的中介：将其腿在一点上捆绑，其步长兼容性是锥体在 [tower_step] 上自身的相干性读数。 *)
Program Definition tower_med (N : Cone F) :
  vertex_obj[N] ~{Sets}~> tower_obj := {|
  morphism := fun e =>
    (fun n => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) n e;
     fun n => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) (S n) n
                (tower_step n) e)
|}.
Next Obligation.
  intros N e e' Hee' n.
  exact (proper_morphism (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) n)
                         e e' Hee').
Qed.

Lemma tower_med_commutes (N : Cone F) (n : nat) :
  tower_proj n ∘ tower_med N
    ≈ @vertex_map _ _ _ _ (@coneFrom _ _ _ N) n.
Proof. intros e; reflexivity. Qed.

Lemma tower_med_unique (N : Cone F)
  (v : vertex_obj[N] ~{Sets}~> tower_obj)
  (Hv : ∀ n : nat,
          tower_proj n ∘ v ≈ @vertex_map _ _ _ _ (@coneFrom _ _ _ N) n) :
  v ≈ tower_med N.
Proof. intros e n; exact (Hv n e). Qed.

Program Definition Sets_tower_limit : IsALimit F tower_obj := {|
  limit_acone := tower_acone;
  ump_limit := fun N => {| unique_obj := tower_med N |}
|}.
Next Obligation. intros N n e; reflexivity. Qed.
Next Obligation. intros N v Hv e n; symmetry; exact (Hv n e). Qed.

Program Definition Sets_tower_Limit : Limit F := {|
  limit_cone := tower_cone;
  ump_limits := fun N => {| unique_obj := tower_med N |}
|}.
Next Obligation. intros N n e; reflexivity. Qed.
Next Obligation. intros N v Hv e n; symmetry; exact (Hv n e). Qed.

(*
 Mac Lane's own sentence: a matching string IS a cone from the one-point
 set.  The cone set is Instance/Sets/Complete.v's [cone_apex]; the two
 are identified by the general essential-uniqueness theorem, so this
 carries both leg families rather than being a bare isomorphism. 

 --------
 麦克·莱恩自己的句子：一个匹配的字符串就是从单点集合出发的一个余锥。余锥集合是 Instance/Sets/Complete.v 中的 [cone_apex]；通过一般的本质唯一性定理，这两者被识别，所以它承载了两条腿族，而不仅仅是一个空的同构。
*)
Definition Sets_tower_limit_iso_cone_limit : tower_obj ≅ cone_apex F :=
  limit_unique_iso Sets_tower_limit (cone_set_IsALimit F).

End Tower.

(* * ** (E) The named notion, its notation, and [Cochain]'s first consumer / * **（E）该命名概念、其符号，以及 [Cochain] 的第一个消费者 *)

Definition inverse_limit (F : Omega^op ⟶ Sets) : SetoidObject := tower_obj F.

(* By DELTA, like [tower_step_is_omega_step] above: [inverse_limit] is defined as [tower_obj], so this guards the name against drift and measures nothing. / 通过 DELTA，就像上面的 [tower_step_is_omega_step]：[inverse_limit] 被定义为 [tower_obj]，因此这可以防止名称漂移，并且不会测量任何东西。 *)
Example inverse_limit_is_tower (F : Omega^op ⟶ Sets) :
  inverse_limit F = tower_obj F := eq_refl.

(* An OPT-IN scope, on the [power_scope] precedent of Structure/Limit/Power.v: the token is not forced on any consumer. / 一个选择加入的范围，根据 [power_scope] 在 Structure/Limit/Power.v 的先例：该代币不会强制用于任何消费者。 *)
Declare Scope inverse_limit_scope.
Delimit Scope inverse_limit_scope with invlim.
Notation "'lim←' F" := (inverse_limit F)
  (at level 9, format "'lim←'  F") : inverse_limit_scope.

(*
 [Construction/Chain.v]'s [Cochain G] is the tower
 [1 <- G 1 <- G² 1 <- ...] of an endofunctor with a terminal object, and
 before this file NOTHING in the tree consumed it ([rg -l Cochain]
 returned that file alone).  It is a tower, so it has an inverse limit.

 A DONOR UNIVERSE PIN, MEASURED AND DISCLOSED.  [Cochain] is declared
 without universe annotations and minimizes to

 Cochain@{u u0} : forall {C : Category@{u0 Set Set}},
 Terminal@{u0 Set} -> C ⟶ C -> Omega@{u Set Set}^op ⟶ C

 -- C's hom AND proof universes pinned to the literal [Set] -- where
 [Chain@{u u0 u1}], one line above it, leaves its TARGET category FREE
 ([C : Category@{u u0 u0}]) where [Cochain] pins it.  Read that
 precisely: [Chain] is NOT free of [Set] -- its own printed type carries
 [Omega@{u1 Set Set}] -- so BOTH constants pin [Omega]'s hom and proof to
 [Set], and what separates them is the TARGET alone.  [Omega@{o h p}]
 itself is free in all three.  So the consumer below is
 confined to [Sets@{Set su}], setoids whose CARRIER lives in [Set]; the
 general section (A)-(D) above carries no [Set] at all
 ([tower_obj@{u u0 u1 u2 u3 u4} : Omega@{u u0 u0}^op ⟶ Sets@{u0 u1} ->
 obj[Sets@{u4 u2}]]).  The pin is the donor's, is NOT repaired here, and
 is NOT claimed unavoidable. 

 --------
 [Construction/Chain.v] 的 [Cochain G] 是一个终对象的 endofunctor 的塔，而在此文件之前，树中没有任何东西使用它（[rg -l Cochain] 只返回了该文件）。它是一个塔，所以它有一个逆极限。

 一个捐赠者宇宙针，已测量并公开。[Cochain] 被声明时没有宇宙注释，并最小化为

 Cochain@{u u0} : 对于所有 {C : Category@{u0 Set Set}},
 Terminal@{u0 Set} -> C ⟶ C -> Omega@{u Set Set}^op ⟶ C-- C 的同态和证明宇宙固定在字面 [Set] 上 -- 其中 [Chain@{u u0 u1}]，在它上面一行，使其 TARGET 分类保持自由 ([C : Category@{u u0 u0}]) 而 [Cochain] 将其固定。精确地阅读：[Chain] 并非自由于 [Set] —— 它自己的打印类型带有 [Omega@{u1 Set Set}] —— 因此这两个常量都将 [Omega] 的同态和证明固定在 [Set] 上，而它们之间的区别仅在于 TARGET。[Omega@{o h p}] 本身在三者中都是自由的。因此下面的使用者被限制在 [Sets@{Set su}] 内，其 CARRIER 存在于 [Set]；上面的通用部分 (A)-(D) 完全不包含 [Set] ([tower_obj@{u u0 u1 u2 u3 u4} : Omega@{u u0 u0}^op ⟶ Sets@{u0 u1} -> obj [Sets@{u4 u2}] ])。固定点属于捐赠者，这里没有修复，也不会被认为是不可避免的。
*)

Definition cochain_inverse_limit@{su +}
  (G : Sets@{Set su} ⟶ Sets@{Set su}) : obj[Sets@{Set su}] :=
  inverse_limit (Cochain G).

Definition cochain_tower_limit@{su +}
  (G : Sets@{Set su} ⟶ Sets@{Set su}) :
  IsALimit (Cochain G) (cochain_inverse_limit G) :=
  Sets_tower_limit (Cochain G).

(* The tower's stages are the iterated images of the terminal object. / 这座塔的各个阶段是终对象的迭代映像。 *)
Example cochain_stage_zero@{su +} (G : Sets@{Set su} ⟶ Sets@{Set su}) :
  fobj[Cochain G] 0%nat = @terminal_obj Sets@{Set su} Sets_Terminal
  := eq_refl.

Example cochain_stage_succ@{su +} (G : Sets@{Set su} ⟶ Sets@{Set su})
  (n : nat) : fobj[Cochain G] (S n) = G (fobj[Cochain G] n) := eq_refl.

(* * ** (F) What the two identifications read back / * **（F）两份身份证的读回内容 *)

(* The legs of the tower limit ARE the coordinate projections. / 塔的腿的极限是坐标投影。 *)
Example tower_limit_leg (F : Omega^op ⟶ Sets) (n : nat) :
  limit_leg (Sets_tower_limit F) n = tower_proj F n := eq_refl.

(*
 And the comparison with the cone set is not a bare [≅]: it carries both
 leg families, by the general essential-uniqueness theorem. 

 --------
 与锥体集合的比较并不是一个单纯的 [≅]：根据一般的本质唯一性定理，它携带了两个腿族。
*)
Definition Sets_tower_limit_iso_cone_limit_legs (F : Omega^op ⟶ Sets) :
  (∀ n : nat, cone_leg_at F n ∘ to (Sets_tower_limit_iso_cone_limit F)
                ≈ tower_proj F n) *
  (∀ n : nat, tower_proj F n ∘ from (Sets_tower_limit_iso_cone_limit F)
                ≈ cone_leg_at F n) :=
  limit_unique_iso_legs (Sets_tower_limit F) (cone_set_IsALimit F).

(*
 Both legs of [tower_iso] are the identity on the underlying family: the
 two presentations differ in what they CARRY (a step condition against a
 condition at every arrow), never in the string itself. 

 --------
 [tower_iso] 的两条腿在底层族上都是恒等的：这两个表示的区别在于它们携带的内容（一个针对每个箭头的步条件），而不是字符串本身。
*)
Example tower_fwd_underlying (F : Omega^op ⟶ Sets)
  (p : Sets_limit_obj F) : `1 (tower_fwd F p) = `1 p := eq_refl.

Example tower_bwd_underlying (F : Omega^op ⟶ Sets)
  (p : tower_obj F) : `1 (tower_bwd F p) = `1 p := eq_refl.

(* * ** (G) A tower whose limit is not a singleton / * ** (G) 一个极限不是单点的塔 *)

(*
 The constant tower.  Its transitions are identities, so a matching
 string is an arbitrary constant sequence and the limit has exactly as
 many points as the stage.  Read the scope: this witness shows the
 inverse limit does NOT collapse, and exercises the projections and the
 mediator on closed input.  THIS witness's transitions are identities
 and so lose nothing; section (H)'s [StreamTower] is genuinely lossy (two
 distinct stage-2 points share a stage-1 image), so the FILE does contain
 a lossy tower and it is only this section's witness that does not.  What
 no witness here has is an EMPTY inverse limit: that phenomenon is not
 exhibited and is not claimed. 

 --------
 恒塔。它的变换都是恒等映射，因此一个匹配的字符串是任意的常数序列，极限正好有与阶段相同数量的点。请注意范围：这个见证表明逆极限不会塌缩，并且在封闭输入上验证了投影和中介。这个见证的变换都是恒等的，因此不会丢失任何信息；而(H)节的 [StreamTower] 是真正有损的（两个不同的阶段2点共享一个阶段1的像），因此这个文件确实包含一个有损塔，只有这一节的见证不会有损。这里没有任何见证具有空的逆极限：这种现象没有被展示，也没有被声称存在。
*)

(*
 The constant tower is [Functor/Diagonal.v]'s diagonal at the shape,
 consumed rather than rebuilt: its arrow action is [id] at every arrow,
 which is exactly the identity system. 

 --------
 常数塔是 [Functor/Diagonal.v] 在形状上的对角线，消耗而非重建：它的箭头作用在每个箭头上是 [id]，这恰好是恒等系统。
*)
Definition ConstTower (X : obj[Sets]) : Omega^op ⟶ Sets :=
  Diagonal (Omega^op) X.

Example const_tower_fmap (X : obj[Sets]) (n : nat) :
  fmap[ConstTower X] (tower_step n) = id[X] := eq_refl.

(*
 The compatibility witness is proved as a lemma rather than written
 inline as [fun _ => reflexivity _]: the bare [_] leaves the relation an
 unresolved implicit on Coq 8.19 and 8.20 (it elaborates on Rocq 9.1),
 where the TACTIC [reflexivity] has the goal to work from.  Measured on
 both legacy versions. 

 --------
 兼容性证明被作为引理证明，而不是内联写作 [fun _ => reflexivity _]：仅仅写 [_] 会在 Coq 8.19 和 8.20（在 Rocq 9.1 上展开）中使该关系成为未解决的隐式项，其中策略 [reflexivity] 的目标是从中工作。在两个旧版本中都进行了测量。
*)
Lemma const_string_compat (b : bool) :
  tower_compat (ConstTower bool_setoid_object) (fun _ : nat => b).
Proof. intros n; reflexivity. Qed.

Definition const_string (b : bool) :
  inverse_limit (ConstTower bool_setoid_object) :=
  (fun _ => b; const_string_compat b).

Example const_string_coord (b : bool) (n : nat) :
  tower_proj (ConstTower bool_setoid_object) n (const_string b) = b
  := eq_refl.

(* Two provably distinct points of the inverse limit. / 逆极限的两个可证明不同的点。 *)
Lemma const_string_separates :
  const_string true ≈ const_string false → False.
Proof. intros H; specialize (H 0%nat); discriminate H. Qed.

(* * ** (H) Streams: the classical tower, and the comparison map / * **（H）流：经典塔和比较映射 *)


Section StreamTower.

Context (A : SetoidObject@{Set Set}).

Definition StreamTower : Omega^op ⟶ Sets@{Set _} := Cochain (StreamF A).

Example stream_tower_zero :
  fobj[StreamTower] 0%nat = @terminal_obj Sets Sets_Terminal := eq_refl.

Example stream_tower_succ (n : nat) :
  fobj[StreamTower] (S n)
  = @product_obj Sets Sets_Cartesian A (fobj[StreamTower] n) := eq_refl.

Fixpoint stream_trunc (n : nat) (s : Stream A) : fobj[StreamTower] n :=
  match n as m return fobj[StreamTower] m with
  | O   => ttt
  | S k => (shead A s, stream_trunc k (stail A s))
  end.

Lemma stream_trunc_compat (s : Stream A) :
  tower_compat StreamTower (fun n => stream_trunc n s).
Proof.
  intros n; revert s.
  induction n as [| k IH]; intros s; simpl.
  - destruct (fmap[StreamTower] (tower_step 0%nat) (stream_trunc 1%nat s)).
    reflexivity.
  - split; [reflexivity | exact (IH (stail A s))].
Qed.

Lemma stream_trunc_respects (n : nat) (s t : Stream A)
  (H : bisim A s t) : stream_trunc n s ≈ stream_trunc n t.
Proof.
  revert s t H.
  induction n as [| k IH]; intros s t H; simpl.
  - destruct (stream_trunc 0%nat s), (stream_trunc 0%nat t); reflexivity.
  - split; [exact (bisim_head A H) | exact (IH _ _ (bisim_tail A H))].
Qed.

(*
 The comparison map: a stream to its string of truncations.  Read its
 strength exactly -- this is a MORPHISM, and it is NOT proved
 invertible.  The inverse would be a corecursive assembly of a stream
 from a matching string together with two round trips up to
 bisimilarity, which is a different and larger development; nothing here
 claims the inverse limit IS [Instance/Sets/Streams.v]'s final
 coalgebra, only that the canonical map exists. 

 --------
 比较映射：一个流与其截断字符串的对应关系。精确读取它的强度——这是一个态射，并且尚未证明可逆。其逆将是从匹配字符串的核心递归组装流，并经过两次往返达到双模拟相似性，这是一个不同且更大的发展；这里没有宣称逆极限是 [Instance/Sets/Streams.v] 的终结余代数，只是说明该典型映射存在。
*)
Program Definition stream_to_tower :
  Stream_SO A ~{Sets}~> inverse_limit StreamTower := {|
  morphism := fun s => (fun n => stream_trunc n s ; stream_trunc_compat s)
|}.
Next Obligation. intros s t Hst n; exact (stream_trunc_respects n s t Hst). Qed.

(* Its coordinates are the truncations, on the nose. / 它的坐标就是截断的部分，正好如此。 *)
Example stream_to_tower_coord (s : Stream A) (n : nat) :
  tower_proj StreamTower n (stream_to_tower s) = stream_trunc n s := eq_refl.

Example stream_to_tower_one (s : Stream A) :
  tower_proj StreamTower 1%nat (stream_to_tower s) = (shead A s, ttt)
  := eq_refl.

End StreamTower.
