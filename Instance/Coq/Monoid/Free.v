Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Comma.
Require Import Category.Construction.FAlg.
Require Import Category.Construction.Funny.Comparison.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Coq.Lists.
Require Import List.

Generalizable All Variables.

(* * * The free monoid on a type, and its universal property / * * 一种类型上的自由幺半群及其普遍性性质 *)

(*
 nLab:      https://ncatlab.org/nlab/show/free+monoid
 Wikipedia: https://en.wikipedia.org/wiki/Free_monoid

 For a type [X], the free monoid on [X] is the type [list X] of finite words
 over [X], multiplied by concatenation with the empty word as unit, together
 with the insertion of generators [p : X → list X] sending a letter to the
 one-letter word.  Its universal property is that [p] is universal among maps
 from [X] into (the underlying set of) a monoid: every [h : X → U L] extends
 along [p] to one and only one monoid homomorphism [list X → L], namely the
 fold that replaces concatenation by the multiplication of [L] and the empty
 word by its unit.

 Everything here is developed at [Mon Coq], the category of monoid objects
 (Theory/Algebra/Monoid.v) in the cartesian monoidal category of Coq types
 (Instance/Coq.v, [Coq_Monoidal]), with [Mon_Forget] as the underlying-type
 functor U.  A monoid object over that base is exactly an ordinary monoid:
 [mu : x * x → x], [eta : unit → x], and the three laws are associativity and
 the two unit laws with the cartesian associator and unitors — which over
 [Coq] are the evident reassociation and projections — inserted to make the
 maps composable.  Morphism equivalence in [Coq] is pointwise Leibniz
 equality, so no function extensionality is needed anywhere below: two
 monoid homomorphisms are identified exactly when they agree at every word,
 which is what list induction proves.

 The book statements this file discharges are quoted from the catalog
 inventories under doc/plan/books/{maclane,awodey,7sketches}/inventory/, and
 the wordings paraphrased here are the CATALOG'S PARAPHRASE, not the books'
 own wording.  A recap mapping each catalog item to the constants that
 deliver it closes this header. 

 --------
 nLab：https://ncatlab.org/nlab/show/free+monoid
 维基百科：https://en.wikipedia.org/wiki/Free_monoid

 对于类型 [X]，[X] 上的自由幺半群是有限单词的类型 [list X]，这些单词取自 [X]，通过连接相乘，空单词作为单位，并且包括生成元 [p : X → list X] 的插入，将一个字母映射为单字单词。它的泛性质是 [p] 在从 [X] 到（幺半群的底层集合）的映射中具有普遍性：每个 [h : X → U L] 沿 [p] 延拓成一个且唯一的幺半群同态 [list X → L]，即将连接替换为 [L] 的乘法、空单词替换为其单位的折叠。这里的一切都是在 [Mon Coq] 中开发的，即笛卡尔幺半群范畴的幺半群对象类别（Theory/Algebra/Monoid.v），在 Coq 类型的笛卡尔幺半群范畴中（Instance/Coq.v, [Coq_Monoidal]），并且 [Mon_Forget] 作为底层类型函子 U。该基上的一个幺半群对象正是一个普通的幺半群：[mu : x * x → x]、[eta : unit → x]，并且三条定律是结合律以及两个单位律，使用笛卡尔结合子和单位子——在 [Coq] 上就是显然的重关联和投影——插入以使映射可组合。在 [Coq] 中的态射等价是逐点 Leibniz 等式，因此下面任何地方都不需要函数外延性：当两个幺半群同态在每个字上都一致时，它们正好被识别，这是列表归纳所证明的。本文件中说明的书籍内容摘自目录清单，位于 doc/plan/books/{maclane,awodey,7sketches}/inventory/，此处的表述为目录的释义，而非书籍原文。 本头部分的结尾提供了每个目录条目与对应输出常量的映射总结。
*)

(*
 Free constructions, folds, and why the monoid case is the one everyone
 meets first

 nLab:      https://ncatlab.org/nlab/show/free+monoid
 nLab:      https://ncatlab.org/nlab/show/universal+morphism
 Wikipedia: https://en.wikipedia.org/wiki/Free_monoid
 Wikipedia: https://en.wikipedia.org/wiki/Kleene_star

 The free monoid is the oldest surviving example of a universal mapping
 problem and, by some distance, the most heavily used.  Under the name
 “Kleene star” it is the closure operation of formal language theory:
 Kleene introduced A* while analysing the events representable in nerve
 nets, and the star of an alphabet is precisely the underlying set of the
 free monoid on that alphabet (Kleene, “Representation of events in nerve
 nets and finite automata”, in Shannon and McCarthy, Automata Studies,
 Princeton 1956; Wikipedia, “Kleene star”).  Every statement about strings
 — concatenation is associative, the empty string is neutral, a
 substitution is determined by its action on single letters — is a
 statement about this monoid, and the last of those is exactly the
 universal property proved below.

 Mac Lane presents it as a corollary rather than a construction.  The free
 category on a graph is built in CWM §II.7, and the free monoid falls out
 by reading a monoid as a one-object category: a graph with one vertex is a
 set of loops, and the free category on it has the words in those loops as
 arrows (Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 Springer 1998, §II.7 Corollary 2, pp. 50–51).  Awodey goes the other way,
 constructing A* directly in §1.7 and using it as the first non-trivial
 universal property in the book, then returning to it in §9.1 as the
 motivating adjunction (Awodey, “Category Theory”, 1st ed., Carnegie Mellon
 pre-print, September 2005, §1.7 pp. 19–22, §9.1 pp. 213–214).  Fong and
 Spivak reach the same object through the free category on the one-vertex
 loop graph and ask for its elements at a two-letter alphabet (Fong and
 Spivak, “An Invitation to Applied Category Theory: Seven Sketches in
 Compositionality”, CUP 2019, §5.2.3 Exercise 5.24).  In-tree both routes
 exist: Construction/Free/Quiver.v carries the free category on a quiver
 with its universal arrow, and this file carries the monoid case directly.
 The identification of the two — free monoid as the delooping of the free
 category on a one-vertex quiver — is NOT proved here; see the deferral
 note at the end of this header.

 The programming-language reading is the fold.  A [Foldable] container is
 one that maps into any monoid, and the fold of a list is the unique monoid
 homomorphism out of the free monoid determined by the element map; this is
 why [foldMap] takes a function into a monoid and nothing more.  In-tree
 Theory/Coq/Foldable.v states that correspondence in prose over an ops-only
 class, and Instance/Coq/Lists.v proves the sibling fact that [list A] is
 the initial algebra of [ListF A X = 1 + A × X], whose unique algebra map is
 the same fold.  The bridge between the two universal properties — the
 monoid-homomorphism extension IS the [ListF]-algebra fold — is proved
 below ([free_ext_is_fold], [free_ext_is_the_unique_algebra_map]), which is
 the sense in which “structural recursion over lists” and “the free monoid”
 are one fact seen twice.

 Finally, the adjunction.  Free-forgetful adjunctions are the paradigm case
 of Kan's notion, and this one is the example every introduction uses: the
 left adjoint of the underlying-set functor on monoids.  Its unit is the
 insertion of generators, natural because a homomorphism out of a free
 monoid is determined by its action on generators (Awodey §7.5 Example
 7.7); its counit at a monoid L is the evaluation of words in L, and the
 fact that the counit's underlying map splits — every element is the value
 of its own one-letter word — is the categorical form of “every monoid is a
 quotient of a free one” (Awodey §9.9 Exercise 2).  The pattern generalises
 verbatim to groups, rings, modules and algebras, which is why Samuel could
 already see one problem behind all of them (Theory/Universal/Arrow.v's
 header tells that story). 

 --------
 自由构造、folds，以及为什么单子情况是每个人首先遇到的案例

 nLab:       https://ncatlab.org/nlab/show/free+monoid
 nLab:       https://ncatlab.org/nlab/show/universal+morphism
 Wikipedia:  https://en.wikipedia.org/wiki/Free_monoid
 Wikipedia:  https://en.wikipedia.org/wiki/Kleene_star自由幺半群是现存最古老的通用映射问题的例子，并且在使用频率上毫无疑问是最广泛的。在“克莱尼星号”（Kleene star）的名义下，它是形式语言理论中的闭包运算：克莱尼在分析神经网络中可表示的事件时引入了 A*，而字母表的星号恰好是该字母表上自由幺半群的基础集合（Kleene，《神经网络和有限自动机中事件的表示》，收录于 Shannon 和 McCarthy 的《自动机研究》，普林斯顿 1956；Wikipedia，“Kleene star”）。关于字符串的每一个陈述——连接是结合的、空字符串是中性的、替换由其在单个字母上的作用决定——都是关于这个幺半群的陈述，而最后一条恰好就是下面证明的通用性质。麦克莱恩把它作为一个推论而不是一个构造来呈现。在《CWM》第II.7节中构建了图上的自由范畴，自由幺半群则通过将幺半群视为单对象范畴而得出：一个只有一个顶点的图是一组环，自由范畴在其上的箭头就是这些环中的字（麦克莱恩，《为工作中的数学家而写的范畴论》，第2版，施普林格 1998，第II.7节 推论2，第50–51页）。阿沃迪则采取相反的方法，在第1.7节直接构造A*，并将其作为本书中第一个非平凡的普适性质，然后在第9.1节回到它作为动机伴随（阿沃迪，《范畴论》，第1版，卡内基梅隆预印本，2005年9月，第1.7节 第19–22页，第9.1节 第213–214页）。Fong 和 Spivak 通过单顶点环图上的自由范畴达到相同的对象，并在一个两字母字母表下要求其元素（Fong 和 Spivak，《应用范畴论入门：组合性中的七个草稿》，CUP 2019，第5.2.3节 练习 5.24）。在 in-tree 中两条路径都存在：Construction/Free/Quiver.v 承载着带有其通用箭头的 quiver 上的自由范畴，而该文件直接承载了单子情形。两者的识别 —— 自由单子作为单顶点 quiver 上自由范畴的去环 —— 在此处未证明；请参见本页眉末尾的延后说明。编程语言中的读取是 fold。一个 [Foldable] 容器是一个映射到任意幺半群的容器，而列表的 fold 是从由元素映射确定的自由幺半群生成的唯一幺半群同态；这就是为什么 [foldMap] 仅接受一个映射到幺半群的函数而不做其他操作的原因。在 In-tree Theory/Coq/Foldable.v 中，以散文形式阐述了只包含操作的类中的对应关系，而 Instance/Coq/Lists.v 证明了一个相关事实，即 [list A] 是 [ListF A X = 1 + A × X] 的初始代数，其唯一的代数映射就是相同的 fold。这两个普遍性质之间的桥梁——幺半群同态扩展就是 [ListF] 代数 fold——在下文 ([free_ext_is_fold], [free_ext_is_the_unique_algebra_map]) 中被证明，这是“列表上的结构递归”和“自由幺半群”被两次观察到为同一个事实的意义所在。最后，附加。自由-遗忘附加是 Kan 概念的典型案例，这个例子也是每本入门书都会用的：单元上的基础集合函子（underlying-set functor）的左伴随函子。它的单位是生成元的插入，这是自然的，因为从自由单元出发的同态由其在生成元上的作用决定（Awodey §7.5 例子 7.7）；在单元 L 上的余单位是对 L 中单词的求值，而余单位的基础映射可分解 —— 每个元素都是其自身单字单词的值 —— 这是“每个单元都是自由单元的商”的范畴形式（Awodey §9.9 练习 2）。这个模式可以逐字推广到群、环、模和代数，这就是为什么 Samuel 能够预见它们背后的一个问题（Theory/Universal/Arrow.v 的标题说明了这个故事）。
*)

#[local] Notation MonCoq := (@Mon Coq Coq_Monoidal).
#[local] Notation UMon := (@Mon_Forget Coq Coq_Monoidal).

#[local] Obligation Tactic := idtac.

(*
   * ** An element-level view of a monoid object over [Coq]

   The three [Monoid] laws are stated with the cartesian associator and
   unitors inserted.  Over [Coq] those are the evident reassociation and
   projections, so each law instantiated at an explicit tuple is an ordinary
   equation between elements.  Naming those instances once keeps every proof
   below free of tensor bookkeeping. 

   --------
   * ** 关于  [Coq] 的幺半群对象的元素级视图

   三条  [Monoid] 公理是在插入笛卡尔结合子和单位子后陈述的。在  [Coq] 上，这些就是显然的重关联和投影，因此在显式元组上实例化的每条公理都是元素之间的普通方程。为这些实例命名一次，能使下面的每个证明不受张量记账影响。
*)

Section Elements.

Context (L : MonCoq).

Definition mmul (a b : `1 L) : `1 L := mu[`2 L] (a, b).
Definition mone : `1 L := eta[`2 L] tt.

Lemma mmul_assoc (a b c : `1 L) : mmul (mmul a b) c = mmul a (mmul b c).
Proof. exact (@mu_assoc Coq Coq_Monoidal _ (`2 L) ((a, b), c)). Qed.

Lemma mone_left (a : `1 L) : mmul mone a = a.
Proof. exact (@mu_unit_left Coq Coq_Monoidal _ (`2 L) (tt, a)). Qed.

Lemma mone_right (a : `1 L) : mmul a mone = a.
Proof. exact (@mu_unit_right Coq Coq_Monoidal _ (`2 L) (a, tt)). Qed.

End Elements.

Arguments mmul {L} a b.
Arguments mone {L}.

(* The two homomorphism laws in the same element-level form. / 同一元素层次形式下的两个同态法则。 *)
Lemma hom_mmul {L N : MonCoq} (g : L ~{MonCoq}~> N) (a b : `1 L) :
  `1 g (mmul a b) = mmul (`1 g a) (`1 g b).
Proof. exact (@hom_mu Coq Coq_Monoidal _ _ _ _ _ (`2 g) (a, b)). Qed.

Lemma hom_mone {L N : MonCoq} (g : L ~{MonCoq}~> N) :
  `1 g (@mone L) = @mone N.
Proof. exact (@hom_eta Coq Coq_Monoidal _ _ _ _ _ (`2 g) tt). Qed.

(*
   * ** The free monoid: words under concatenation

   Mac Lane §II.7 Corollary 2 and Awodey §1.7: for a type [X] the finite
   words over [X] form a monoid under concatenation with the empty word as
   unit.  The unit laws hold on the nose in one direction ([nil ++ l] is
   [l] by computation) and by [app_nil_r] in the other. 

   --------
   * ** 自由幺半群：在连接运算下的词

   Mac Lane §II.7 推论 2 和 Awodey §1.7：对于类型 [X]，上的有限词
   在连接运算下形成一个幺半群，空词作为单位元。在一个方向上单位定律严格成立（[nil ++ l]通过计算等于[l]），在另一个方向上则通过[app_nil_r]成立。
*)

Program Definition FreeMonoidStructure (X : Type) :
  @Monoid Coq Coq_Monoidal (list X) := {|
  mu  := fun p => (fst p ++ snd p)%list;
  eta := fun _ => @nil X
|}.
Next Obligation.
  intros X p; destruct p as [[a b] c]; simpl.
  symmetry; apply app_assoc.
Qed.
Next Obligation.
  intros X p; destruct p as [u a]; destruct u; reflexivity.
Qed.
Next Obligation.
  intros X p; destruct p as [a u]; simpl.
  apply app_nil_r.
Qed.

(* The free monoid on [X] as an object of [Mon Coq]. / 作为 [Mon Coq] 的一个对象， [X] 上的自由幺半群。 *)
Definition FreeMon (X : Coq) : MonCoq := (list X; FreeMonoidStructure X).

(* Its multiplication and unit are concatenation and the empty word, on the nose. / 它的乘法和单位分别是连接和空字，就像描述的那样。 *)
Example free_mmul_is_app (X : Coq) (u v : list X) :
  mmul (L:=FreeMon X) u v = (u ++ v)%list := eq_refl.

Example free_mone_is_nil (X : Coq) : @mone (FreeMon X) = @nil X := eq_refl.

(*
   * ** The insertion of generators

   Awodey's [i : A → A*], sending a letter to the one-letter word. 

   --------
   * ** 发电机的插入

   Awodey 的 [i : A → A*]，向那个单字母词寄送一封信。
*)

Definition insert (X : Coq) : X ~{Coq}~> UMon (FreeMon X) :=
  fun a => (a :: nil)%list.

(*
   * ** The extension of a map into a monoid: the fold

   Awodey §1.7 Proposition 1.9 computes the extension of [h : A → |N|] as
   [f(a₁…aᵢ) = h(a₁) * … * h(aᵢ)], the empty word going to the unit.  That
   is the right fold. 

   --------
   * ** 将映射扩展到幺半群：折叠

   Awodey §1.7 命题 1.9 计算了  [h : A → |N|]  的扩展，得到
   [f(a₁…aᵢ) = h(a₁) * … * h(aᵢ)] ，空字被映射为单位元。也就是右折叠。
*)

Fixpoint free_ext {X : Coq} {L : MonCoq} (h : X → `1 L) (l : list X)
  : `1 L :=
  match l with
  | nil       => @mone L
  | cons a l' => mmul (h a) (free_ext h l')
  end.

(* The extension carries concatenation to multiplication: induction on the left word, using the left unit law at [nil] and associativity at [cons]. / 该扩展将连接推广到乘法：对左边的词进行归纳，在 [nil] 上使用左单位律，在 [cons] 上使用结合律。 *)
Lemma free_ext_app {X : Coq} {L : MonCoq} (h : X → `1 L) (u v : list X) :
  free_ext h (u ++ v)%list = mmul (free_ext h u) (free_ext h v).
Proof.
  induction u as [|a u IH]; simpl.
  - symmetry; apply mone_left.
  - rewrite IH; symmetry; apply mmul_assoc.
Qed.

(* ... and it agrees with [h] on the generators, by computation. / ... 并且通过计算，它在生成元上与 [h] 一致。 *)
Lemma free_ext_generators {X : Coq} {L : MonCoq} (h : X → `1 L) (a : X) :
  free_ext h (insert X a) = h a.
Proof. simpl; apply mone_right. Qed.

(* Hence it is a monoid homomorphism out of the free monoid. / 因此它是从自由幺半群到幺半群的同态映射。 *)
Program Definition free_ext_MonoidHom {X : Coq} {L : MonCoq} (h : X → `1 L) :
  @MonoidHom Coq Coq_Monoidal (list X) (`1 L)
             (FreeMonoidStructure X) (`2 L) (free_ext h) := {|
  hom_mu  := _;
  hom_eta := _
|}.
Next Obligation.
  intros X L h p; destruct p as [u v]; simpl.
  apply free_ext_app.
Qed.
Next Obligation. intros X L h u; destruct u; reflexivity. Qed.

Definition free_hom {X : Coq} {L : MonCoq} (h : X → `1 L)
  : FreeMon X ~{MonCoq}~> L :=
  (free_ext h; free_ext_MonoidHom h).

(*
 Uniqueness: any monoid homomorphism out of the free monoid agreeing with
 [h] on the generators IS the fold.  This is the list induction of Awodey
 §1.7 Proposition 1.9, and it uses both homomorphism laws — the unit law at
 the empty word, the multiplication law at the [cons] split
 [a :: l = (a :: nil) ++ l]. 

 --------
 唯一性：从自由幺半群到其他幺半群的任何幺半群同态，只要在生成元上与 [h] 一致，就一定是折叠。这是 Awodey §1.7 命题 1.9 的列表归纳，并且它使用了两个同态定律——空单词处的单位定律，以及在 [cons] 拆分的 [a :: l = (a :: nil) ++ l] 处的乘法定律。
*)
Lemma free_ext_unique {X : Coq} {L : MonCoq} (h : X → `1 L)
      (g : FreeMon X ~{MonCoq}~> L)
      (Hg : forall a : X, `1 g (insert X a) = h a) (l : list X) :
  `1 g l = free_ext h l.
Proof.
  induction l as [|a l IH]; simpl.
  - exact (hom_mone g).
  - rewrite <- IH, <- (Hg a).
    exact (hom_mmul g (a :: nil)%list l).
Qed.

(*
   * ** The universal property

   Awodey §1.7 Proposition 1.9, in the shape
   [Theory/Universal/Arrow.v]'s [universal_arrow_from_UMP] consumes: for
   every monoid [L] and every [h : X → U L] there is exactly one monoid
   homomorphism [g] with [U g ∘ insert ≈ h].  Uniqueness is up to the
   ambient [≈], which in [Mon Coq] is pointwise equality of the underlying
   functions. 

   --------
   * ** 通用性质

   Awodey §1.7 命题 1.9，其形式为
   [Theory/Universal/Arrow.v] 的 [universal_arrow_from_UMP] 消耗：对于每一个幺半群 [L] 和每一个 [h : X → U L]，存在唯一一个幺半群同态 [g] 使得 [U g ∘ insert ≈ h] 成立。唯一性是在环境 [≈] 下的，在 [Mon Coq] 中是底层函数的逐点相等。
*)

Theorem free_monoid_universal (X : Coq) :
  forall (L : MonCoq) (h : X ~{Coq}~> UMon L),
    ∃! g : FreeMon X ~{MonCoq}~> L, h ≈ fmap[UMon] g ∘ insert X.
Proof.
  intros L h.
  unshelve eexists.
  - exact (free_hom h).
  - intro a; simpl.
    symmetry; apply free_ext_generators.
  - intros g Hg a; simpl.
    symmetry; apply free_ext_unique.
    intro b; symmetry; exact (Hg b).
Qed.

(*
 The free monoid packaged as a universal arrow from [X] to [Mon_Forget].
 By [Theory/Universal/Arrow.v] this IS an initial object of the comma
 category [=(X) ↓ Mon_Forget]. 

 --------
 将自由幺半群作为从 [X] 到 [Mon_Forget] 的一个通用箭头打包。通过 [Theory/Universal/Arrow.v]，这是逗号范畴 [=(X) ↓ Mon_Forget] 的一个初始对象。
*)
Definition free_monoid_universal_arrow (X : Coq) : UniversalArrow X UMon :=
  universal_arrow_from_UMP X UMon (FreeMon X) (insert X)
                           (free_monoid_universal X).

(*
 The same content in the direct encoding, where the universal object is
 named rather than projected. 

 --------
 直接编码中的相同内容，其中通用对象被命名而不是被投射。
*)
Program Definition free_monoid_AUniversalArrow (X : Coq)
  : AUniversalArrow X UMon (FreeMon X) := {|
  universal_arrow := insert X
|}.
Next Obligation.
  intros X L h.
  unshelve eexists.
  - exact (free_hom h).
  - intro a; simpl; apply free_ext_generators.
  - intros g Hg a; simpl.
    symmetry; apply free_ext_unique.
    intro b; exact (Hg b).
Qed.

(*
   * ** The free-forgetful adjunction

   Awodey §9.1.  The free functor and the adjunction are assembled by the
   generic machinery of Theory/Universal/Arrow.v from the family of
   universal arrows. 

   --------
   * ** 自由-遗忘伴随

   Awodey §9.1。自由函子和伴随由 Theory/Universal/Arrow.v 的通用机制从一族通用箭头组装而成。
*)

Definition FreeMonoid : Coq ⟶ MonCoq :=
  LeftAdjointFunctorFromUniversalArrows UMon free_monoid_universal_arrow.

Definition free_monoid_adjunction : FreeMonoid ⊣ UMon :=
  AdjunctionFromUniversalArrows UMon free_monoid_universal_arrow.

(* The free functor's object part is the word monoid, definitionally. / 自由函子在对象部分定义上就是单词幺半群。 *)
Example FreeMonoid_obj (X : Coq) : FreeMonoid X = FreeMon X := eq_refl.

(*
 The universal arrow of [free_monoid_universal_arrow] is the insertion of
 generators on the nose: [universal_arrow_from_UMP] stores the supplied
 morphism as the second projection of the comma object it builds, so no
 proof is involved. 

 --------
 [free_monoid_universal_arrow] 的通用箭头是在鼻子上插入生成元：[universal_arrow_from_UMP] 将提供的态射存储为它构建的逗号对象的第二投影，因此不涉及任何证明。
*)
Example free_arrow_is_insert (X : Coq) :
  @arrow _ _ X UMon (free_monoid_universal_arrow X) = insert X := eq_refl.

(*
 Hence so is the unit of the adjunction: the transpose of the identity is
 [fmap[U] id ∘ arrow], and [fmap[U] id] is the identity function. 

 --------
 因此伴随的单位也是如此：恒等式的转置是 [fmap[U]  id ∘ arrow]，而 [fmap[U]  id] 是恒等函数。
*)
Example free_monoid_unit_is_insert (X : Coq) (a : X) :
  @Category.Theory.Adjunction.unit _ _ _ _ free_monoid_adjunction X a
    = insert X a := eq_refl.

(*
   * ** The free functor acts on arrows as [List.map]

   [LeftAdjointFunctorFromUniversalArrows] defines [fmap] by universal
   factorization, not by a formula, so what the functor does to a word has to
   be proved.  It is [map]: the defining factorization says exactly that
   generators go to generators, and the uniqueness half of the universal
   property then identifies the homomorphism with [map]. 

   --------
   * ** 自由函子作用于箭头为  [List.map] 

   [LeftAdjointFunctorFromUniversalArrows]  通过普遍分解定义  [fmap] ，而不是通过一个公式，因此必须证明该函子对一个词的作用是什么。它是  [map] ：定义的分解恰好说明生成元映射到生成元，然后普遍性唯一性的一半将同态识别为  [map] 。
*)

Lemma free_fmap_generators {X Y : Coq} (f : X ~{Coq}~> Y) (a : X) :
  `1 (fmap[FreeMonoid] f) (insert X a) = insert Y (f a).
Proof.
  symmetry.
  exact (unique_property
           (ump_universal_arrows (free_monoid_universal_arrow X)
              (@arrow _ _ Y UMon (free_monoid_universal_arrow Y) ∘ f)) a).
Qed.

(* The fold of [a ↦ [f a]] into the free monoid on Y is [map f]. / [a ↦ [f a] 到 Y 上自由幺半群的折叠是 [map f]。 *)
Lemma free_ext_insert {X Y : Coq} (f : X ~{Coq}~> Y) (l : list X) :
  free_ext (L:=FreeMon Y) (fun a => insert Y (f a)) l = map f l.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity|now rewrite IH].
Qed.

Theorem free_fmap_is_map {X Y : Coq} (f : X ~{Coq}~> Y) (l : list X) :
  `1 (fmap[FreeMonoid] f) l = map f l.
Proof.
  etransitivity.
  - apply (free_ext_unique (L:=FreeMon Y) (fun a => insert Y (f a))
             (fmap[FreeMonoid] f) (free_fmap_generators f) l).
  - apply free_ext_insert.
Qed.

(*
   * ** The insertion of generators as a natural transformation

   Awodey §7.5 Example 7.7: [η_X : X → U M(X)] is natural in X, “because the
   induced homomorphism M(f) is determined by its action on generators”.
   That sentence is [free_fmap_generators], and it is the whole naturality
   square. 

   --------
   * ** 将生成元插入作为自然变换

   Awodey §7.5 示例 7.7：[η_X : X → U M(X)] 在 X 中是自然的，“因为诱导的同态 M(f) 是由它在生成元上的作用决定的”。那句话是 [free_fmap_generators]，并且它构成了整个自然性交换图。
*)

Program Definition insert_Transform : Id[Coq] ⟹ UMon ◯ FreeMonoid := {|
  transform := insert
|}.
Next Obligation. intros X Y f a; apply free_fmap_generators. Qed.
Next Obligation. intros X Y f a; symmetry; apply free_fmap_generators. Qed.

(*
 It is the unit of the adjunction, componentwise on the nose — so the
 instance asked for by Awodey's example and the generic transformation
 produced from any adjunction by [Adjunction_to_Transform]
 (Adjunction/Natural/Transformation/Universal.v) agree. 

 --------
 它是陪伴的单位，逐分量地严格对应——因此 Awodey 示例中要求的实例与由 [Adjunction_to_Transform]（Adjunction/Natural/Transformation/Universal.v）从任何陪伴产生的通用变换是一致的。
*)
Example insert_Transform_is_adjunction_unit (X : Coq) (a : X) :
  transform[insert_Transform] X a
    = transform[@unit _ _ _ _
                  (@Adjunction_to_Transform _ _ _ _ free_monoid_adjunction)] X a
  := eq_refl.

(*
   * ** The transposition formula

   Awodey §9.1 asks for the bijection between monoid homomorphisms out of
   the free monoid and functions into the underlying set.  That bijection is
   [adj] of [free_monoid_adjunction]; the formula for its forward direction
   is the generic [to_adj_unit] read at this adjunction, and unwinds to
   “restrict the homomorphism to the one-letter words”. 

   --------
   * ** 换位公式

   Awodey §9.1 讨论了从自由幺半群到幺半群同态之间，以及到基础集合的函数之间的双射。这个双射是 [adj] 的 [free_monoid_adjunction]；其正向公式是该伴随中读取的通用 [to_adj_unit]，并展开为“将同态限制在单字母词上”。
*)

Corollary free_monoid_transposition {X : Coq} {L : MonCoq}
      (g : FreeMonoid X ~{MonCoq}~> L) :
  to (@adj _ _ _ _ free_monoid_adjunction X L) g
    ≈ fmap[UMon] g ∘ insert X.
Proof. exact (@to_adj_unit _ _ _ _ free_monoid_adjunction X L g). Qed.

Corollary free_monoid_transposition_at {X : Coq} {L : MonCoq}
      (g : FreeMonoid X ~{MonCoq}~> L) (a : X) :
  to (@adj _ _ _ _ free_monoid_adjunction X L) g a = `1 g (insert X a).
Proof. exact (free_monoid_transposition g a). Qed.

(* The inverse direction is the fold: transposing a function back gives the homomorphism that extends it. / 逆方向是折叠：将一个函数转置回去会得到扩展它的同态。 *)
Corollary free_monoid_transposition_inv {X : Coq} {L : MonCoq}
      (h : X ~{Coq}~> UMon L) (l : list X) :
  `1 (from (@adj _ _ _ _ free_monoid_adjunction X L) h) l = free_ext h l.
Proof.
  apply free_ext_unique.
  intro a.
  etransitivity.
  - symmetry.
    exact (@free_monoid_transposition_at X L
             (from (@adj _ _ _ _ free_monoid_adjunction X L) h) a).
  - exact (@from_adj_comp_law _ _ _ _ free_monoid_adjunction X L h a).
Qed.

(*
   * ** The counit, and “every monoid is a quotient of a free one”

   Awodey §9.9 Exercise 2.  Two statements have to be kept apart, and the
   library had neither: [Theory/Adjunction.v]'s [adj_monic] is the mono-side
   result and has no epi counterpart.

   (a) The counit's IMAGE under U is a SPLIT epimorphism, split by the unit.
   This holds for every adjunction with no hypothesis at all: it is one
   of the two triangle identities, [fmap_counit_unit].

   (b) The counit ITSELF is an epimorphism, provided U is faithful.  This
   does need the hypothesis, and [Mon_Forget_Faithful] supplies it here.

   What is NOT claimed is that the counit is a split epimorphism in Mon: a
   section would have to be a monoid homomorphism [L → M(U L)], and the
   evident candidate [m ↦ [m]] is not one (it sends a product to a
   one-letter word, not to a two-letter one).  Whether some other section
   exists depends on L, so no general statement of that shape is available,
   and none is needed: the exercise's “quotient” is the surjection of
   underlying sets, which is (a). 

   --------
   * ** 余单位，以及“每个幺半群都是自由幺半群的商半群”

   Awodey §9.9 练习 2。两个陈述必须加以区分，图书馆中都没有：[Theory/Adjunction.v] 的 [adj_monic] 是关于幺半群的结果，并没有对应的满射版本。

   (a) 余单位在 U 下的像是一个可分裂的满射，被单位分裂。
   对于任何伴随对，这一点都成立，无需任何假设：它是两个三角恒等式之一，[fmap_counit_unit]。

   (b) 余单位本身是一个满射，前提是 U 是忠实的。
   这确实需要该假设，而 [Mon_Forget_Faithful] 在这里提供了它。没有声称的是 counit 在 Mon 中是一个分裂的上射：一个截面必须是一个幺半群同态 [L → M(U L)]，而明显的候选 [m ↦ [m] 并不是（它将一个积映射到一个单字母词，而不是两个字母的词）。是否存在其他截面取决于 L，因此没有可用的此类一般性陈述，也不需要：练习中的“商”是底层集合的满射，即 (a)。
*)

Section AdjunctionCounit.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

(* (a) [U ε] splits, with the unit as its section. / (a) [U ε] 分裂，以单位作为其部分。 *)
Program Definition adjunction_counit_underlying_retraction (x : C) :
  Retraction (fmap[U] (@Category.Theory.Adjunction.counit _ _ _ _ A x)) := {|
  retract := @Category.Theory.Adjunction.unit _ _ _ _ A (U x)
|}.
Next Obligation.
  intro x.
  exact (@Category.Theory.Adjunction.fmap_counit_unit _ _ _ _ A x).
Qed.

(*
 (b) A faithful right adjoint makes the counit epic: transport the
 cancellation through U, where the split from (a) does the work. 

 --------
 (b) 一个忠实的右伴随使得余单位是显著的：通过 U 传递消去，其中 (a) 的分裂完成了工作。
*)
Program Definition adjunction_counit_epic (FU : Faithful U) (x : C) :
  Epic (@Category.Theory.Adjunction.counit _ _ _ _ A x) := {| epic := _ |}.
Next Obligation.
  intros FU x z g1 g2 Heq.
  apply (fmap_inj (F:=U)).
  rewrite <- (id_right (fmap[U] g1)), <- (id_right (fmap[U] g2)).
  rewrite <- (@Category.Theory.Adjunction.fmap_counit_unit _ _ _ _ A x).
  rewrite !comp_assoc, <- !fmap_comp.
  now rewrite Heq.
Qed.

End AdjunctionCounit.

(* The free-monoid instances. / 自由单子实例。 *)
Definition free_monoid_counit_underlying_retraction (L : MonCoq) :
  Retraction (fmap[UMon]
                (@Category.Theory.Adjunction.counit _ _ _ _
                   free_monoid_adjunction L)) :=
  adjunction_counit_underlying_retraction free_monoid_adjunction L.

Definition free_monoid_counit_epic (L : MonCoq) :
  Epic (@Category.Theory.Adjunction.counit _ _ _ _ free_monoid_adjunction L) :=
  adjunction_counit_epic free_monoid_adjunction
    (@Mon_Forget_Faithful Coq Coq_Monoidal) L.

(* Concretely: every element of L is the value of its own one-letter word, so the underlying map of the counit is surjective with a chosen preimage. / 具体来说：L 的每个元素都是其自身单字母词的值，因此余单位的底层映射是满射，并具有一个选定的原像。 *)
Corollary free_monoid_counit_surjective (L : MonCoq) (m : `1 L) :
  `1 (@Category.Theory.Adjunction.counit _ _ _ _ free_monoid_adjunction L)
     (insert (UMon L) m) = m.
Proof. exact (@Category.Theory.Adjunction.fmap_counit_unit _ _ _ _ free_monoid_adjunction L m). Qed.

(*
 And the counit is the evaluation of a word in L: the fold of the identity
 map on the underlying type. 

 --------
 余单位是对 L 中一个词的评估：在底层类型上对恒等映射的折叠。
*)
Theorem free_monoid_counit_is_free_ext (L : MonCoq) (w : list (`1 L)) :
  `1 (@Category.Theory.Adjunction.counit _ _ _ _ free_monoid_adjunction L) w
    = free_ext (fun m : `1 L => m) w.
Proof.
  apply free_ext_unique.
  exact (free_monoid_counit_surjective L).
Qed.

(*
   * ** Uniqueness of the free monoid

   Awodey §1.7 Proposition 1.10: two monoids satisfying the free-monoid
   universal property on the same generating type are related by a unique
   isomorphism commuting with the generator insertions.  The generic lemma
   is [auniversal_arrow_unique] (Theory/Universal/Arrow.v, added for this
   purpose); what is specific here is only that [FreeMon X] inhabits the
   hypothesis. 

   --------
   * ** 自由幺半群的唯一性

   Awodey §1.7 命题 1.10：两个满足在相同生成类型上自由幺半群普遍性质的幺半群，通过一个唯一的同构互相关联，并与生成器的插入操作交换。通用引理是  [auniversal_arrow_unique]  （Theory/Universal/Arrow.v，为此目的而添加）；这里特定的只是  [FreeMon X]  满足假设。
*)

Definition free_monoid_unique {X : Coq} {M N : MonCoq}
      (UM : AUniversalArrow X UMon M) (UN : AUniversalArrow X UMon N) :
  Unique (fun i : M ≅ N =>
            fmap[UMon] (to i) ∘ @universal_arrow _ _ X UMon M UM
              ≈ @universal_arrow _ _ X UMon N UN) :=
  auniversal_arrow_unique UM UN.

(*
 At the word monoid: any monoid with the free-monoid UMP on X is uniquely
 isomorphic to [FreeMon X] over the insertion of generators. 

 --------
 关于单子：任何在 X 上具有自由单子 UMP 的单子，在生成元插入上都唯一同构于 [FreeMon X]。
*)
Definition free_monoid_unique_iso {X : Coq} {N : MonCoq}
      (UN : AUniversalArrow X UMon N) :
  Unique (fun i : FreeMon X ≅ N =>
            fmap[UMon] (to i) ∘ insert X
              ≈ @universal_arrow _ _ X UMon N UN) :=
  auniversal_arrow_unique (free_monoid_AUniversalArrow X) UN.

(*
   * ** The comma presentation: Awodey's category A-Mon

   Awodey §2.9 Exercise 4 defines A-**Mon**: objects are monoids M together
   with a function A → U M, arrows are monoid homomorphisms commuting with
   those structure maps, and the exercise is to show that an initial object
   of A-**Mon** is the same thing as a free monoid on A.

   That category IS the comma category [=(X) ↓ Mon_Forget] — its objects are
   triples (ttt, L, h : X ~> U L), and a morphism to (ttt, N, k) is a pair
   consisting of the unique arrow of the one-object category and a monoid
   homomorphism g with k ∘ id ≈ U g ∘ h.  The “same thing” is then not a
   theorem to prove but the DEFINITION of [UniversalArrow] in
   Theory/Universal/Arrow.v, whose only field is an initial object of that
   comma category; both directions are recorded below as named constants so
   that the identification is stated rather than left implicit. 

   --------
   * ** 逗号表示法：Awodey 的范畴 A-Mon

   Awodey §2.9 练习 4 定义了 A-**Mon**：对象是带有函数 A → U M 的幺半群 M，箭头是与这些结构映射交换的幺半群同态，练习是证明 A-**Mon** 的初始对象与 A 上的自由幺半群是同一个概念。该范畴就是逗号范畴 [=(X) ↓ Mon_Forget] —— 它的对象是三元组 (ttt, L, h : X ~> U L)，到 (ttt, N, k) 的态射是由单对象范畴的唯一箭头和一个幺半群同态 g 组成的对，满足 k ∘ id ≈ U g ∘ h。然后，“同一事物”就不是一个需要证明的定理，而是 Theory/Universal/Arrow.v 中 [UniversalArrow] 的定义，其唯一的字段是该逗号范畴的初始对象；两个方向都以命名常量的形式记录在下面，以便明确地说明该对应关系，而不是让其隐含存在。
*)

Definition AMon (X : Coq) : Category := (=(X) ↓ UMon).

Definition AMon_ob {X : Coq} (L : MonCoq) (h : X ~{Coq}~> UMon L) : AMon X :=
  ((ttt, L); h).

Program Definition AMon_hom {X : Coq} {L N : MonCoq}
        {h : X ~{Coq}~> UMon L} {k : X ~{Coq}~> UMon N}
        (g : L ~{MonCoq}~> N) (Hg : k ≈ fmap[UMon] g ∘ h) :
  AMon_ob L h ~{AMon X}~> AMon_ob N k := ((id, g); _).
Next Obligation.
  intros X L N h k g Hg.
  simpl.
  rewrite ?fmap_id, ?id_right.
  assumption.
Qed.

(* Forward: the free monoid is an initial object of A-Mon. / 前言：自由幺半群是 A-Mon 的初始对象。 *)
Definition free_monoid_initial (X : Coq) : @Initial (AMon X) :=
  @arrow_initial _ _ X UMon (free_monoid_universal_arrow X).

Example free_monoid_initial_obj (X : Coq) :
  @initial_obj (AMon X) (free_monoid_initial X) = AMon_ob (FreeMon X) (insert X)
  := eq_refl.

(*
 Backward: an initial object of A-Mon is a universal arrow, hence a free
 monoid on X together with its insertion of generators. 

 --------
 向后：A-莫诺的一个初始对象是一个泛箭，因此是X上的自由单子以及其生成元的插入。
*)
Definition AMon_initial_universal_arrow (X : Coq) (I : @Initial (AMon X))
  : UniversalArrow X UMon := {| arrow_initial := I |}.

Example AMon_initial_round (X : Coq) :
  @arrow_initial _ _ X UMon
    (AMon_initial_universal_arrow X (free_monoid_initial X))
  = free_monoid_initial X := eq_refl.

(*
   * ** Words over a two-element set, and [ListMon]

   Fong and Spivak, Seven Sketches §5.2.3 Exercise 5.24(3), asks for the
   elements of the free monoid on a two-element set: the words over {a, b}.
   Taking [bool] as that set, [FreeMon bool] has [list bool] as its
   underlying type, multiplication is concatenation, and the unit is the
   empty word — all by computation.

   [ListMon] (Construction/Funny/Comparison.v) is the one-object category
   with [list bool] as its hom-set, built there as a discriminating target
   for the funny tensor product and never identified as a free monoid.  It
   is one: its hom-set IS the underlying type of [FreeMon bool], its
   identity IS the unit, and its composition IS the multiplication with the
   arguments in diagrammatic order — the file's own header notes that
   “words read source-to-target while composition reads right-to-left”, and
   the equations below pin that down. 

   --------
   * ** 两元素集合上的词，以及 [ListMon] 

   Fong 和 Spivak，《七个素描》第5.2.3节练习5.24(3)要求给出两元素集合上的自由单半群的元素：{a, b}上的词。
   将 [bool] 作为该集合，[FreeMon bool] 的基础类型是 [list bool]，乘法是连接，单位元是空词——所有这些都是通过计算得出的。[ListMon]（Construction/Funny/Comparison.v）是一元对象范畴，其同态集为 [list bool]，构建时作为幽默张量积的判别目标，从未被识别为自由幺半群。它是单一的：其同态集即 [FreeMon bool] 的底层类型，其恒等元即单位元，其复合即按照图示顺序的乘法——文件自身的头部注释说明“词语从源到目标读取，而复合从右到左读取”，下方的方程明确了这一点。
*)

Example ListMon_hom_is_free_carrier :
  (ttt ~{ListMon}~> ttt) = UMon (FreeMon bool) := eq_refl.

Example ListMon_id_is_free_unit :
  @id ListMon ttt = @mone (FreeMon bool) := eq_refl.

Example ListMon_compose_is_free_mul (u v : list bool) :
  @compose ListMon ttt ttt ttt u v = mmul (L:=FreeMon bool) v u := eq_refl.

(* Two letters, and words in them. / 两个字母，以及其中的单词。 *)
Definition wa : list bool := (true :: nil)%list.
Definition wb : list bool := (false :: nil)%list.

Example wa_is_generator : wa = insert bool true := eq_refl.
Example wb_is_generator : wb = insert bool false := eq_refl.

Example word_ab :
  mmul (L:=FreeMon bool) wa wb = (true :: false :: nil)%list := eq_refl.
Example word_ba :
  mmul (L:=FreeMon bool) wb wa = (false :: true :: nil)%list := eq_refl.
Example word_noncommutative :
  mmul (L:=FreeMon bool) wa wb <> mmul (L:=FreeMon bool) wb wa.
Proof. discriminate. Qed.
Example word_assoc :
  mmul (L:=FreeMon bool) (mmul (L:=FreeMon bool) wa wb) wa
    = mmul (L:=FreeMon bool) wa (mmul (L:=FreeMon bool) wb wa) := eq_refl.
Example word_unit_left :
  mmul (L:=FreeMon bool) (@mone (FreeMon bool)) wa = wa := eq_refl.
Example word_unit_right :
  mmul (L:=FreeMon bool) wa (@mone (FreeMon bool)) = wa := eq_refl.

(*
 A target monoid to fold into, so the universal property is exercised on
 closed data rather than merely stated: [bool] under exclusive or, with
 [false] as unit.  (Deliberately not (ℕ, +): the reading of ℕ as the free
 monoid on one generator is issue #802's, not this file's.) 

 --------
 一个要折叠成的目标幺半群，因此普适性质是在封闭数据上运用的，而不仅仅是陈述：在异或下的 [bool]，其中 [false] 作为单位。（刻意没有使用 (ℕ, +)：将 ℕ 视为一个生成元的自由幺半群是问题 #802 的内容，而不是本文件的内容。）
*)

Program Definition XorMonoidStructure : @Monoid Coq Coq_Monoidal bool := {|
  mu  := fun p => xorb (fst p) (snd p);
  eta := fun _ => false
|}.
Next Obligation.
  intros p; destruct p as [[a b] c]; simpl.
  apply Bool.xorb_assoc_reverse.
Qed.
Next Obligation. intros p; destruct p as [u a]; destruct u; reflexivity. Qed.
Next Obligation.
  intros p; destruct p as [a u]; simpl; apply Bool.xorb_false_r.
Qed.

Definition XorMon : MonCoq := (bool; XorMonoidStructure).

(*
 The extension of the identity map on letters counts the parity of the word,
 and computes. 

 --------
 字母上的恒等映射的扩展计算了单词的奇偶性，并进行运算。
*)
Example fold_into_xor_1 :
  free_ext (L:=XorMon) (fun b : bool => b) (true :: false :: true :: nil)%list
    = false := eq_refl.

Example fold_into_xor_2 :
  `1 (free_hom (L:=XorMon) (fun b : bool => b))
     (mmul (L:=FreeMon bool) wa wb) = true := eq_refl.

(*
 And it really is a monoid homomorphism out of the word monoid, computed on
 a concatenation. 

 --------
 它确实是一个从单词幺半群出的幺半群同态，作用在一个连接上计算。
*)
Example fold_into_xor_hom :
  `1 (free_hom (L:=XorMon) (fun b : bool => b))
     (mmul (L:=FreeMon bool) (mmul (L:=FreeMon bool) wa wa) wb)
    = mmul (L:=XorMon)
        (`1 (free_hom (L:=XorMon) (fun b : bool => b))
            (mmul (L:=FreeMon bool) wa wa))
        (`1 (free_hom (L:=XorMon) (fun b : bool => b)) wb) := eq_refl.

(*
   * ** Bridge to the initial [ListF]-algebra

   Instance/Coq/Lists.v proves [list A] initial among [ListF A]-algebras,
   the unique algebra map being the fold.  A monoid L together with a map
   [h : X → U L] induces such an algebra — [None ↦ unit], [Some (a, m) ↦
   h a * m] — and the free-monoid extension of h IS the fold determined by
   it.  So the two universal properties of [list X] produce the same
   function, and “structural recursion over lists” and “the free monoid on
   X” are the same fact seen twice. 

   --------
   * ** 初始 [ListF] 代数的桥接

   Instance/Coq/Lists.v 证明了 [list A] 在 [ListF A] 代数中是初始的，
   唯一的代数映射是 fold。一个单子 L 连同一个映射
   [h : X → U L] 诱导出这样的代数——[None ↦ unit]，[Some (a, m) ↦
   h a * m]——h 的自由单子扩展正是由它确定的 fold。因此 [list X]
   的两个泛性质产生了相同的函数，而“对列表的结构递归”和“X 上的自由单子”
   是同一个事实的两次表现。
*)

Definition monoid_ListF_alg {X : Coq} {L : MonCoq} (h : X → `1 L)
  : ListF X (`1 L) ~{Coq}~> `1 L :=
  fun o => match o with
           | None          => @mone L
           | Some (a, m)   => mmul (h a) m
           end.

Definition monoid_FAlg {X : Coq} {L : MonCoq} (h : X → `1 L) : FAlg (ListF X) :=
  existT (FAlgebra (ListF X)) (`1 L) (monoid_ListF_alg h).

Theorem free_ext_is_fold {X : Coq} {L : MonCoq} (h : X → `1 L) (l : list X) :
  free_ext h l = fold (monoid_ListF_alg h) l.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity|now rewrite IH].
Qed.

(*
 The unique [ListF X]-algebra map out of [(list X, alg X)] into the induced
 algebra is the free-monoid extension. 

 --------
 从 [(list X, alg X)] 到诱导代数的唯一 [ListF X]-代数映射是自由单子扩展。
*)
Theorem free_ext_is_initial_algebra_map {X : Coq} {L : MonCoq}
        (h : X → `1 L) (l : list X) :
  falg_hom[@zero (FAlg (ListF X)) (list_initial X) (monoid_FAlg h)] l
    = free_ext h l.
Proof. symmetry; apply free_ext_is_fold. Qed.

(* Stated without the [FAlg] packaging: any map satisfying the algebra square is the extension. / 不考虑 [FAlg] 包装声明：任何满足代数平方的映射都是扩展。 *)
Corollary free_ext_is_the_unique_algebra_map {X : Coq} {L : MonCoq}
        (h : X → `1 L) (g : list X → `1 L)
        (Hg : forall o, g (alg X o) = monoid_ListF_alg h (fmap[ListF X] g o))
        (l : list X) : g l = free_ext h l.
Proof.
  rewrite (hom_is_fold (monoid_ListF_alg h) g Hg l).
  symmetry; apply free_ext_is_fold.
Qed.

(*
   * ** Recap: what discharges which catalog item

   - [maclane:II.7:cor2] and [awodey:1.7:construction-free-monoid] — the free
   monoid on X as an object of [Mon Coq] with its insertion of generators:
   [FreeMonoidStructure], [FreeMon], [insert] (with [free_mmul_is_app],
   [free_mone_is_nil] pinning the operations by computation).

   - [awodey:1.7:prop9] — the universal property, extension by the fold and
   its uniqueness: [free_ext], [free_ext_MonoidHom], [free_ext_unique],
   and the packaged [free_monoid_universal] (the ∃! statement),
   [free_monoid_universal_arrow], [free_monoid_AUniversalArrow].

   - [awodey:9.1:construction-free-monoid-adjunction] — the adjunction:
   [FreeMonoid], [free_monoid_adjunction], with the transposition formula
   [free_monoid_transposition] / [free_monoid_transposition_at] and its
   inverse [free_monoid_transposition_inv].

   - [awodey:7.5:example7] — the insertion of generators as a natural
   transformation: [insert_Transform], whose naturality square is
   [free_fmap_generators]; [insert_Transform_is_adjunction_unit] records
   that it agrees componentwise with the transformation the generic
   [Adjunction_to_Transform] produces.

   - [awodey:9:ex2] — the counit: [adjunction_counit_underlying_retraction]
   (generic, hypothesis-free) and [adjunction_counit_epic] (generic, needs
   a faithful right adjoint), instantiated as
   [free_monoid_counit_underlying_retraction], [free_monoid_counit_epic],
   with the concrete [free_monoid_counit_surjective] and the computation
   [free_monoid_counit_is_free_ext].  Split-epi-ness IN Mon is not claimed;
   see the discussion above that section.

   - [awodey:1.7:prop10] and the QA scope increment — uniqueness up to a
   unique isomorphism: the generic lemmas [universal_arrow_unique] and
   [auniversal_arrow_unique] were ADDED to Theory/Universal/Arrow.v, and
   are specialised here as [free_monoid_unique] and
   [free_monoid_unique_iso].

   - [awodey:2:ex4] — the A-Mon comma presentation: [AMon], [AMon_ob],
   [AMon_hom], with [free_monoid_initial] one way and
   [AMon_initial_universal_arrow] the other.

   - [7sketches:5.2.3:ex5.24] — words over a two-element set and the
   [ListMon] identification: [ListMon_hom_is_free_carrier],
   [ListMon_id_is_free_unit], [ListMon_compose_is_free_mul], plus the
   computing witnesses [word_ab] … [word_unit_right] and the folds
   [fold_into_xor_1] … [fold_into_xor_hom].

   Bridges (issue work item 4): [free_ext_is_fold],
   [free_ext_is_initial_algebra_map] and
   [free_ext_is_the_unique_algebra_map] relate the extension to
   Instance/Coq/Lists.v's [list_initial].

   NOT BUILT, deliberately.

   - The (ℕ, +)-as-free-monoid-on-one-generator consequence is owned by
   issue #802 and nothing here anticipates it; the only monoid used as a
   fold target is [XorMon].

   - The one-object-graph reading is recorded but not transferred: Mac Lane
   obtains the free monoid as the free category on a one-vertex graph, and
   Construction/Free/Quiver.v carries that theorem
   ([UniversalArrowQuiverCat], [FreeForgetfulAdjunction]) with its
   universal property stated in StrictCat under strict functor equality.
   Identifying [FreeMon X] with the hom-monoid of [FreeOnQuiver] at a
   one-vertex quiver needs the delooping dictionary at functor level
   (Construction/Deloop.v defers exactly that step, and its transport is
   issue #220); it is NOT proved here, and no file
   Construction/Free/Quiver/Loop.v exists to cite.  What IS proved is the
   free-monoid universal property directly, which is what the citing
   issues ask for. 

   --------
   * ** 回顾：哪个项目对应哪个目录条目

   - [maclane:II.7:cor2] 和 [awodey:1.7:construction-free-monoid] — 作为 [Mon Coq] 对象的 X 上的自由幺半群及其生成元插入：[FreeMonoidStructure]、[FreeMon]、[insert]（其中 [free_mmul_is_app]、[free_mone_is_nil] 通过计算固定操作）。

   - [awodey:1.7:prop9] — 泛性质，通过折叠的扩展及其唯一性：[free_ext]、[free_ext_MonoidHom]、[free_ext_unique]，以及打包的 [free_monoid_universal]（∃! 表述）、[free_monoid_universal_arrow]、[free_monoid_AUniversalArrow]。

   - [awodey:9.1:construction-free-monoid-adjunction] — 拔 adjunction：[FreeMonoid]、[free_monoid_adjunction]，具有换位公式 [free_monoid_transposition] / [free_monoid_transposition_at] 及其逆 [free_monoid_transposition_inv]。- [awodey:7.5:example7] — 作为自然变换的生成元插入：[insert_Transform]，其自然性方格为[free_fmap_generators]；[insert_Transform_is_adjunction_unit]记录了它在各分量上与通用[Adjunction_to_Transform]生成的变换一致。

   - [awodey:9:ex2] — 余单位：[adjunction_counit_underlying_retraction]（通用，无假设）和[adjunction_counit_epic]（通用，需要忠实的右伴随），实例化为[free_monoid_counit_underlying_retraction]、[free_monoid_counit_epic]，具体为[free_monoid_counit_surjective]及计算[free_monoid_counit_is_free_ext]。在Mon中不声称为分裂额映；参见该节上方的讨论。

   - [awodey:1.7:prop10]和QA范围增加——至唯一同构的唯一性：通用引理[universal_arrow_unique]和[auniversal_arrow_unique]已被添加到Theory/Universal/Arrow.v，并在此专门化为[free_monoid_unique]和[free_monoid_unique_iso]。- [awodey:2:ex4] — A-Mon逗号表示法：[AMon], [AMon_ob], [AMon_hom]，其中[free_monoid_initial]为一种方式，[AMon_initial_universal_arrow]为另一种方式。

   - [7sketches:5.2.3:ex5.24] — 在两元素集合上的词以及[ListMon]的识别：[ListMon_hom_is_free_carrier], [ListMon_id_is_free_unit], [ListMon_compose_is_free_mul]，加上计算证明者[word_ab]…[word_unit_right]和折叠[fold_into_xor_1]…[fold_into_xor_hom]。

   桥接（问题工作项4）：[free_ext_is_fold], [free_ext_is_initial_algebra_map]和[free_ext_is_the_unique_algebra_map]将扩展关联到Instance/Coq/Lists.v的[list_initial]。

   未构建，故意如此。

   - (ℕ, +)作为单生成元自由幺半群的结果归属于问题#802，这里没有预期；唯一用作折叠目标的幺半群是[XorMon]。- 单对象图的读法已被记录，但未被转移：Mac Lane 将自由单子视为单顶点图上的自由范畴，而 Construction/Free/Quiver.v 在 StrictCat 下以严格函子等价形式携带了该定理 ([UniversalArrowQuiverCat], [FreeForgetfulAdjunction]) 及其普适性质。将 [FreeMon X] 识别为单顶点 quiver 上 [FreeOnQuiver] 的 Hom-单子需要函子层面的 deloop 字典 (Construction/Deloop.v 恰好推迟了这一步，其传输在 issue #220 中讨论)；此处并未证明，并且没有文件 Construction/Free/Quiver/Loop.v 可供引用。真正被证明的是自由单子的普适性质，这正是引用问题所需的内容。
*)

