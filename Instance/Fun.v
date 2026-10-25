Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Sets.

Generalizable All Variables.

Section Fun.

Context {C : Category}.
Context {D : Category}.

(*
 nLab: https://ncatlab.org/nlab/show/functor+category
 Wikipedia: https://en.wikipedia.org/wiki/Functor_category

 The functor category `[C, D]` (also written `D^C`) has functors `C ⟶ D` as
 objects and natural transformations as morphisms. Composition is vertical
 composition of natural transformations (`nat_compose`), the identity is the
 identity natural transformation (`nat_id`), and the hom-setoid is
 componentwise: two natural transformations are equal exactly when their
 components agree at every object (this is the [Transform_Setoid] of
 [Theory.Natural.Transformation]). The unit and associativity laws hold
 componentwise, inherited from D, and are discharged by [Program] below.

 When D carries pointwise structure (limits, colimits, cartesian, closed),
 `[C, D]` inherits it pointwise from D; those instances live in their own
 files (e.g. under Structure) rather than here. 

 --------
 nLab: https://ncatlab.org/nlab/show/functor+category
 Wikipedia: https://en.wikipedia.org/wiki/Functor_category

 函子范畴 ` [C, D]ZZ `（也写作 `D^C`）以函子 `C ⟶ D` 为对象，以自然变换为态射。复合是自然变换的垂直复合（`nat_compose`），恒等元是恒等自然变换（`nat_id`），而齐次集代数是分量式的：两个自然变换仅当它们在每个对象上的分量相同时才相等（这是 [Transform_Setoid] 的 [Theory.Natural.Transformation]）。单位律和结合律在分量上成立，由 D 继承，并通过下面的 [Program] 得到验证。

 当 D 具有逐点结构（极限、余极限、笛卡尔闭结构）时，` [C, D]ZZ ` 继承 D 的逐点结构；这些实例存在于它们自己的文件中（例如在 Structure 下），而不是在这里。
*)

(*
 Where the functor category comes from, and what it is for

 nLab:  https://ncatlab.org/nlab/show/category+of+presheaves
 nLab:  https://ncatlab.org/nlab/show/Yoneda+embedding
 nLab:  https://ncatlab.org/nlab/show/Godement+product
 SEP:   https://plato.stanford.edu/entries/category-theory/
 Paper: Eilenberg, Mac Lane, "General Theory of Natural Equivalences",
 Transactions of the AMS 58, 1945

 The functor category is as old as category theory itself.  The founding
 paper of the subject already contains a section II.8 titled "Categories
 of functors", though a category of categories is nowhere mentioned in
 it, and its authors regarded everything beneath this level as
 scaffolding: "the whole concept of a category is essentially an
 auxiliary one; our basic concepts are essentially those of a functor
 and of natural transformation" (Eilenberg–Mac Lane 1945, p. 247, as
 quoted by the Stanford Encyclopedia of Philosophy).  Freyd compressed
 the genesis into a slogan — categories are what one must define in
 order to define functors, and functors are what one must define in
 order to define natural transformations (Freyd, "Abelian Categories",
 1964, introduction).  [Fun] realizes the construction as a first-class
 Category, so the ambient machinery of isomorphism, limit, and
 adjunction applies to functors one level up: "natural isomorphism" is
 nothing other than isomorphism in `[C, D]`, and
 [Functor_Setoid_Nat_Iso] (with standalone directions [iso_equiv] and
 [equiv_iso]) reduces such an isomorphism to a componentwise family, so
 invertibility of a transformation is checked one object at a time.

 Three canonical uses organize the applications.  Presheaf categories
 `[C^op, Sets]` are the leading case: their limits, colimits, epis and
 monos are computed objectwise, they are cartesian closed, and the
 Yoneda embedding into them is fully faithful — for a small category,
 its free cocompletion — so every category embeds into a functor
 category built from itself (nLab, "category of presheaves" and "Yoneda
 embedding"); in-tree, Functor/Hom/Yoneda.v develops the lemma and the
 embedding over exactly these hom-setoids, and Theory/Sheaf.v defines
 `Presheaves` as literally `[U^op, C]`.  Diagram categories are the
 domain of limit-taking: a J-shaped diagram in C is an object of
 `[J, C]`, a cone is a morphism out of a constant functor, and
 completeness is the adjoint sandwich colim ⊣ Δ ⊣ lim around the
 diagonal Δ : C ⟶ [J, C] of Functor/Diagonal.v.  And `[C, D]` is the
 exponential witnessing that Cat is cartesian closed
 (Instance/Cat/Cartesian/Closed.v); equivalently, functor categories
 are the hom-categories of the 2-category Cat (nLab, "functor
 category").  Representation theory rides the same construction: a
 representation is a functor out of a one-object domain, and an
 intertwiner between representations is a natural transformation
 (nLab, "representation").

 The 2-categorical reading explains the middle of this file.  The
 whiskering laws and the coherence isomorphisms [nat_λ], [nat_ρ], and
 [nat_α] are precisely the unitor and associator data that
 Instance/Cat/Bicategory.v consumes to make Cat a bicategory with
 `bicat C D ≡ [C, D]` definitionally, reconciling the reversed naming
 noted below (`hunit_left := nat_ρ`, `hunit_right := nat_λ`).
 Horizontal composition of natural transformations is the Godement
 product, named after Roger Godement, and the agreement of its two
 defining formulas IS the interchange law (nLab, "Godement product");
 [whisker_left_right] states its whiskered form here.  One level down,
 the endofunctor category `[C, C]` is monoidal under composition, and a
 monad is exactly a monoid in it (Monad/Monoid.v, [Compose_Monoidal]);
 the classes [Pointed] and [WellPointed] below live at the same
 address.

 The computational reading rests on parametricity.  In a polymorphic
 language a natural transformation is a function of type
 `forall a. F a -> G a`, and parametricity yields the naturality square
 as a free theorem, so functors and polymorphic functions form a
 functor category whose vertical composition is componentwise program
 composition (Milewski, "Natural Transformations", 2015).  Throughout,
 the governing principle is pointwise inheritance: when D has limits (or
 colimits, nLab) of a shape, so does `[C, D]`, pointwise (for limits,
 Instance/Fun/Limit.v's theorem; an incomplete D can have limits
 not pointwise), and when C is small and D is cartesian closed and
 complete, `[C, D]` is cartesian closed (nLab, "functor category").
 That last clause alone is not inherited, and its hypothesis on D is
 not decorative: Instance/Fun/Closed.v exhibits a C (small in the
 ordinary sense -- its objects are the naturals) and a
 cartesian closed D for which `[C, D]` carries no cartesian closed
 structure at all, so completeness of D may not simply be dropped;
 and it shows besides that where such an exponential does exist it
 need not be computed pointwise.  The nLab clause in its GENERAL form
 is still cited rather than proved here; what IS proved, for the
 presheaf case D := Sets, is Instance/Fun/Exponential.v's
 `Functor_Category_Closed`, the first clause of Awodey's Theorem 8.14
 and Riehl's Lemma 4.4.11, whose exponential is the display-(8.5)
 formula `Q^P(c) = Nat(y c × P, Q)` and is NOT computed pointwise.
 Smallness is not a class here but a measured universe bound -- that
 file's constants carry C's object universe at or below the carrier
 universe of `Sets`, which is what Awodey's "for any small category C"
 comes to in this library -- and there is besides a `Class Small` in
 Theory/Size.v, so the two readings of the word are kept apart rather
 than said to be absent.  The structure that IS inherited pointwise is
 instantiated in Instance/Fun/Cartesian.v (binary products) and in
 Instance/Fun/Terminal.v (the terminal object and indexed products). 

 --------
 函子范畴的来源及其用途

 nLab:   https://ncatlab.org/nlab/show/category+of+presheaves 
 nLab:   https://ncatlab.org/nlab/show/Yoneda+embedding 
 nLab:   https://ncatlab.org/nlab/show/Godement+product 
 SEP:    https://plato.stanford.edu/entries/category-theory/ 
 论文: Eilenberg, Mac Lane，《自然等价的一般理论》，美国数学会会报 58, 1945函子范畴和范畴论本身一样古老。该学科的创始论文已经包含一个标题为“函子的范畴”的第 II.8 节，尽管文中并未提到范畴的范畴，而且其作者将所有低于此级别的内容视为脚手架：“范畴的整体概念本质上是辅助性的；我们的基本概念本质上是函子和自然变换的概念”（埃伦伯格–麦克莱恩 1945，第 247 页，斯坦福哲学百科全书引述）。弗莱德将其起源浓缩为一句口号——范畴是必须定义以便定义函子的，而函子是必须定义以便定义自然变换的（弗莱德，《阿贝尔范畴》，1964，引言）。[Fun] 将该构造实现为一类一级范畴，因此同构、极限和伴随的环境机制同样适用于上一级的函子：“自然同构”无非就是 ` [C, D]ZZ ` 中的同构，而 [Functor_Setoid_Nat_Iso]（带有独立的方向 [iso_equiv] 和 [equiv_iso]）将这样的同构化简为逐分量的族，因此变换的可逆性可以逐个对象进行检查。三种典型的用途组织了这些应用。预层范畴 ` [C^op, Sets]ZZ ` 是主要的情况：它们的极限、余极限、满射和单射通过对象逐一计算，它们是笛卡尔闭的，并且向它们的 Yoneda 嵌入是完全忠实的——对于一个小范畴，它的自由余完备——所以每一个范畴都嵌入到由自身构建的函子范畴中（nLab，“预层范畴”与“Yoneda 嵌入”）；在 in-tree, Functor/Hom/Yoneda.v 中严格针对这些 Hom-集合体发展了引理和嵌入，而 Theory/Sheaf.v 则将 `Presheaves` 定义为字面意义上的 ` [U^op, C]ZZ `。图表类别是取极限的领域：在 C 中的 J 形图是 ` [J, C]ZZ ` 的一个对象，圆锥是从恒等函子出发的一个态射，而完备性则是环绕对角线 Δ : C ⟶ [J, C] 的伴随三明治 colim ⊣ Δ ⊣ lim（参见 Functor/Diagonal.v）。而 ` [C, D]ZZ ` 是指数对象，表明 Cat 是笛卡尔闭的（参见 Instance/Cat/Cartesian/Closed.v）；等价地，函子类别是 2-范畴 Cat 的态射类别（参见 nLab，“functor category”）。表示论使用的是相同的构造：一个表示是从单对象域出发的函子，而表示之间的交错映射是自然变换（参见 nLab，“representation”）。二范畴的阅读解释了此文件的中间部分。鞭状律和相干同构 [nat_λ]、[nat_ρ] 和 [nat_α] 恰恰是 Instance/Cat/Bicategory.v 使用的数据，使 Cat 在定义上成为一个二范畴，`bicat C D ≡  [C, D]ZZ ` 调和了下面提到的反向命名（`hunit_left := nat_ρ`、`hunit_right := nat_λ`）。自然变换的水平复合是 Godement 积，以 Roger Godement 命名，其两个定义公式的一致性本身就是交换律（nLab，“Godement product”）；[whisker_left_right] 在此处陈述了其鞭状形式。下一层，函子范畴 ` [C, C]ZZ ` 在组合下是单oidal的，一个单子恰好是其中的一个幺半群（Monad/Monoid.v, [Compose_Monoidal]）；下面的类 [Pointed] 和 [WellPointed] 位于相同的地址。计算阅读依赖于参数性。在多态语言中，自然变换是类型为 `forall a. F a -> G a` 的函数，参数性产生自然性方格作为自由定理，因此函子和多态函数形成一个函子范畴，其垂直合成是按组成部分的程序合成（Milewski，《自然变换》，2015）。在整个过程中，支配原则是按点继承：当 D 对某种形状具有极限（或余极限，nLab）时，` [C, D]ZZ ` 也按点具有极限（对于极限，参见 Instance/Fun/Limit.v 定理；不完全的 D 可以具有非按点的极限），并且当 C 是小范畴而 D 是笛卡尔闭并完备时，` [C, D]ZZ ` 是笛卡尔闭的（nLab，“函子范畴”）。仅最后一条条款不是继承的，而且它对 D 的假设也不是装饰性的：Instance/Fun/Closed.v 展示了一个 C（在普通意义上是小的——它的对象是自然数）和一个笛卡尔闭合的 D，对于该 D，` [C, D]ZZ ` 完全不承载任何笛卡尔闭合结构，因此 D 的完备性不能简单地被省略；此外，它还表明，即使存在这样的指数对象，它也不一定是按点计算的。nLab 中的一般形式条款在此仍然被引用，而不是证明；对于预层情况 D := Sets 所证明的是 Instance/Fun/Exponential.v 的 `Functor_Category_Closed`，即 Awodey 定理 8.14 的第一条款和 Riehl 的引理 4.4.11，其指数对象是显示公式 (8.5) 的 `Q^P(c) = Nat(y c × P, Q)`，并且不是按点计算的。在这里，小是指一个有界的度量宇宙，而不是一个类——该文件的常量携带 C 的对象宇宙，在 `Sets` 的承载宇宙上或之下，这就是 Awodey 所说的“对任何小范畴 C”在此库中的含义——此外，在 Theory/Size.v 中还有一个 `Class Small`，因此这个词的两种读法被区分开，而不是说不存在。继承的结构是按点继承的，在 Instance/Fun/Cartesian.v（二元积）和 Instance/Fun/Terminal.v（终对象和索引积）中被实例化。
*)

(*
   【Fun / [C,D] 函子范畴实例展开】/ Functor category walkthrough
   （口吻对齐 Theory/Functor.v；受众：Coq 小白 + Haskell）

   1) 这是什么 / What this is
      Fun = [C,D]：对象是函子 C⟶D；态射是自然变换；复合是垂直复合。
      Functor category: objects=functors, morphisms=natural transformations.
      Haskell 对照：forall a. F a → G a 的多态函数 + 自由定理≈自然性；
      这里自然性是真正证明字段。预层 [C^op,Sets]、图 [J,C] 都是特例。
      Analogy: polymorphic F a→G a; naturality is a real proof here.

   2) 关键字段 / Key fields
      - obj := C ⟶ D；hom := Transform（自然变换）
      - id := nat_id；compose := nat_compose（垂直）
      - ≈ 分量逐点取 D 的 ≈；同构 = 自然同构

   3) 记号 / Notation
      [ C , D ] := Fun；Cat 的指数对象即此（笛卡尔闭）。

   阅读：Fun 记录 → 垂直复合定律 → Pointed / iso_equiv 等。
   Read: Fun → vertical laws → Pointed / nat-iso helpers.
*)
Program Definition Fun : Category := {|
  obj     := C ⟶ D;                 (* objects are functors C ⟶ D / 对象是函子 C ⟶ D *)
  hom     := @Transform C D;        (* morphisms are natural transformations / 态射是自然变换 *)
  id      := @nat_id C D;           (* identity natural transformation / 恒等自然变换 *)
  compose := @nat_compose C D;      (* vertical composition of nat-transes / nat-transes 的垂直组成 *)

  compose_respects := @nat_compose_respects C D
|}.

End Fun.

Notation "[ C , D ]" := (@Fun C D)
  (at level 90, right associativity, format "[ C ,  D ]") : category_scope.

Notation "[[[ C , D ]]]( F , G )" := ({| carrier   := @hom (@Fun C D) F G
                                       ; is_setoid := @homset (@Fun C D) F G |})
  (at level 90, right associativity, format "[[[ C ,  D ]]]( F , G )") : homset_scope.

(*
 The category laws restated directly for `[C, D]`: left/right identity and
 associativity of vertical composition, each holding componentwise in D. 

 --------
 类别定律直接重述对于 ` [C, D]ZZ `：左/右恒等性以及垂直组合的结合律，每一条在 D 中按分量成立。
*)

Corollary nat_id_left C D (F G : C ⟶ D) (N : F ⟹ G) :
  nat_id ∙ N ≈[Fun] N.
Proof. unfold nat_id, nat_compose; simpl; intros; cat. Qed.

Corollary nat_id_right C D (F G : C ⟶ D) (N : F ⟹ G) :
  N ∙ nat_id ≈[Fun] N.
Proof. unfold nat_id, nat_compose; simpl; intros; cat. Qed.

Corollary nat_comp_assoc C D (F G H J : C ⟶ D)
          (M : H ⟹ J) (N : G ⟹ H) (O : F ⟹ G) :
  M ∙ (N ∙ O) ≈[Fun] (M ∙ N) ∙ O.
Proof. unfold nat_compose; simpl; intros; cat. Qed.

(*
 Whiskering and coherence laws for natural transformations viewed in the
 functor category: whiskering the identity yields an identity, whiskering
 distributes over vertical composition, and the interchange law relates left
 and right whiskering (see Theory/Natural/Transformation.v for `⊲`/`⊳`). 

 --------
 在函子范畴中观察自然变换的刷边（whiskering）和相干律：刷边单位自然变换会得到单位自然变换，刷边对垂直复合分配，并且交换律将左刷边和右刷边联系起来（参见 Theory/Natural/Transformation.v 中的 `⊲` / `⊳`）。
*)

Lemma whisker_right_id A B C (F : A ⟶ B) (G : B ⟶ C) : id{Fun} ⊲ F ≈ id{Fun}.
Proof. simpl; intros; cat. Qed.

Lemma whisker_left_id A B C (F : A ⟶ B) (G : B ⟶ C) : G ⊳ id{Fun} ≈ id{Fun}.
Proof. simpl; intros; cat. Qed.

Lemma whisker_left_dist A B C (F : A ⟶ B) (G H J : B ⟶ C)
      (η : G ⟹ H) (θ : H ⟹ J) : (θ ⊲ F) ∙ (η ⊲ F) ≈ (θ ∙ η) ⊲ F.
Proof. simpl; intros; cat. Qed.

Lemma whisker_right_dist A B C (F G H : A ⟶ B) (J : B ⟶ C)
      (η : F ⟹ G) (θ : G ⟹ H) : (J ⊳ θ) ∙ (J ⊳ η) ≈ J ⊳ (θ ∙ η).
Proof. simpl; intros; cat. now rewrite fmap_comp. Qed.

(*
 The unitors and associator as natural isomorphisms in `[A, B]` (resp.
 `[A, _]`), witnessing functor-composition coherence. Note the orientation:
 `nat_λ` is the right-unit isomorphism `F ◯ Id ≅ F` (identity on the right)
 and `nat_ρ` is the left-unit isomorphism `Id ◯ F ≅ F` (identity on the
 left); these names are local conventions and do not follow the usual
 monoidal left-/right-unitor naming (λ for `I ⊗ A`, ρ for `A ⊗ I`). 

 --------
 在  ` [A, B]ZZ `  （分别为 ` [A, _]ZZ ` ）中，单位子和结合子作为自然同构，见证函子组合的相干性。注意方向：`nat_λ` 是右单位同构 `F ◯ Id ≅ F`（右侧的恒等映射），而 `nat_ρ` 是左单位同构 `Id ◯ F ≅ F`（左侧的恒等映射）；这些名称是局部约定，并不遵循通常的单体左右单位子命名（λ 对应 `I ⊗ A`，ρ 对应 `A ⊗ I`）。
*)

Definition nat_λ {A B} (F : A ⟶ B) : F ◯ Id ≅[Fun] F.
Proof.
  construct.
  - apply fun_id_right.
  - apply fun_id_right_sym.
  - apply fun_id_right_and_sym.
  - apply fun_id_right_sym_and.
Defined.

Definition nat_ρ {A B} (F : A ⟶ B) : Id ◯ F ≅[Fun] F.
Proof.
  construct.
  - apply fun_id_left.
  - apply fun_id_left_sym.
  - apply fun_id_left_and_sym.
  - apply fun_id_left_sym_and.
Defined.

Definition nat_α {A B C D} (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) :
  H ◯ (G ◯ F) ≅[Fun] (H ◯ G) ◯ F.
Proof.
  construct.
  - apply fun_comp_assoc.
  - apply fun_comp_assoc_sym.
  - apply fun_comp_assoc_and_sym.
  - apply fun_comp_assoc_sym_and.
Defined.

Lemma whisker_left_right A B C (F G : A ⟶ B) (H J : B ⟶ C)
      (η : F ⟹ G) (θ : H ⟹ J) :
  (J ⊳ η) ∙ (θ ⊲ F) ≈ (θ ⊲ G) ∙ (H ⊳ η).
Proof. simpl; intros; cat; apply naturality. Qed.

Lemma whisker_flip A B C (F : A ⟶ B) (G : B ⟶ C) :
  (to (nat_λ G) ⊲ F) ∙ to (nat_α F Id G) ≈ G ⊳ (to (nat_ρ F)).
Proof. simpl; intros; cat. Qed.

Lemma nat_α_whisker_right_comp
      A B C D (F : A ⟶ B) (G : B ⟶ C) (H J : C ⟶ D) (η : H ⟹ J) :
  to (nat_α F G J) ∙ η ⊲ (G ◯ F) ≈ (η ⊲ G) ⊲ F ∙ to (nat_α F G H).
Proof. simpl; intros; cat. Qed.

Lemma nat_α_whisker_left_comp
      A B C D (F G : A ⟶ B) (H : B ⟶ C) (J : C ⟶ D) (η : F ⟹ G) :
  to (nat_α G H J) ∙ J ⊳ (H ⊳ η) ≈ (J ◯ H) ⊳ η ∙ to (nat_α F H J).
Proof. simpl; intros; cat. Qed.

Lemma nat_α_whisker_assoc
      A B C D (F : A ⟶ B) (G H : B ⟶ C) (J : C ⟶ D) (η : G ⟹ H) :
  to (nat_α F H J) ∙ J ⊳ (η ⊲ F) ≈ (J ⊳ η) ⊲ F ∙ to (nat_α F G J).
Proof. simpl; intros; cat. Qed.

Lemma nat_α_nat_α A B C D E (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) (J : D ⟶ E) :
  (to (nat_α G H J) ⊲ F ∙ to (nat_α F (H ◯ G) J)) ∙ (J ⊳ (to (nat_α F G H)))
    ≈ to (nat_α F G (J ◯ H)) ∙ to (nat_α (G ◯ F) H J).
Proof. simpl; intros; cat. Qed.

(*
 nLab: https://ncatlab.org/nlab/show/pointed+endofunctor

 A pointed endofunctor is an endofunctor `F : C ⟶ C` equipped with a natural
 transformation `point : Id ⟹ F` from the identity functor. 

 --------
 nLab：https://ncatlab.org/nlab/show/pointed+endofunctor

 一个指向的端函子是一个端函子`F : C ⟶ C`，配备了一个从恒等函子出发的自然变换`point : Id ⟹ F`。
*)

Class Pointed {C : Category} (F : C ⟶ C) := {
  point : Id ⟹ F                        (* the point η : Id ⟹ F / 点 η : Id ⟹ F *)
}.

(*
 A pointed endofunctor is well-pointed when the two whiskerings of `point`
 with `F` agree as natural transformations `F ⟹ F ◯ F`, i.e. `F point` and
 `point F` coincide; the unitor isomorphisms `nat_λ`/`nat_ρ` reconcile the
 `F ◯ Id`/`Id ◯ F` source types with `F`. (A monad is well-pointed via its
 unit exactly when it is idempotent.) 

 --------
 当两个 ``point`` 的胡须作用与 ``F`` 作为自然变换 ``F ⟹ F ◯ F`` 一致时，一个尖端的终函子是良点的，即 ``F point`` 和 ``point F`` 重合；单位同构 ``nat_λ` / `nat_ρ`` 调和了 ``F ◯ Id` / `Id ◯ F`` 的源类型与 ``F``。（一个单子通过其单位是良点的，当且仅当它是幂等的。）
*)

Class WellPointed `{@Pointed C F} := {
  well_pointed :
    (F ⊳ point) ∙ from (nat_λ _) ≈ (point ⊲ F) ∙ from (nat_ρ _)
}.

(*
 nLab: https://ncatlab.org/nlab/show/natural+isomorphism
 Wikipedia: https://en.wikipedia.org/wiki/Natural_transformation#Natural_isomorphism

 Isomorphisms in `[C, D]` are exactly natural isomorphisms, and a natural
 transformation is invertible iff each of its components is invertible in D.
 Here that pointwise-iso characterization is packaged as an equivalence with
 the functor setoid-equality `F ≈ G`: an iso in `[C, D]` yields a family of
 componentwise isomorphisms `F x ≅ G x` (the forward direction builds it),
 and conversely such a family assembles into a natural isomorphism. 

 --------
 nLab：https://ncatlab.org/nlab/show/natural+isomorphism
 Wikipedia：https://en.wikipedia.org/wiki/Natural_transformation#Natural_isomorphism

 在` [C, D]ZZ `中的同构正好是自然同构，而自然变换是可逆的当且仅当它的每个分量在D中都是可逆的。这里的逐点同构的表征以与函子集合等价`F ≈ G`的等价形式打包：` [C, D]ZZ `中的一个同构会产生一族按分量的同构`F x ≅ G x`（正方向构造它），反之，这样的一族可以组装成一个自然同构。
*)

Theorem Functor_Setoid_Nat_Iso `(F : C ⟶ D) (G : C ⟶ D) :
  F ≅[Fun] G  ↔  F ≈ G.
Proof.
  split; intros; simpl.
  - given (iso : ∀ x : C, F x ≅ G x). {
      intros; isomorphism; simpl; intros.
      - apply X.
      - apply (X⁻¹).
      - abstract (srewrite (iso_to_from X); cat).
      - abstract (srewrite (iso_from_to X); cat).
    }
    exists iso; simpl in *; intros.
    abstract
      (rewrite <- comp_assoc;
       rewrite (naturality[to X]);
       rewrite comp_assoc;
       srewrite (iso_from_to X); cat).
  - destruct X.
    isomorphism; simpl; intros.
    + transform; simpl; intros.
      * apply x.
      * abstract
          (rewrite e; simpl;
           rewrite !comp_assoc;
           rewrite iso_to_from; cat).
      * abstract
          (rewrite e; simpl;
           rewrite !comp_assoc;
           rewrite iso_to_from; cat).
    + transform; simpl; intros.
      * apply x.
      * abstract
          (rewrite e; simpl;
           rewrite <- !comp_assoc;
           rewrite iso_to_from; cat).
      * abstract
          (rewrite e; simpl;
           rewrite <- !comp_assoc;
           rewrite iso_to_from; cat).
    + abstract
        (rewrite fmap_id;
         apply iso_to_from).
    + abstract
        (rewrite fmap_id;
         apply iso_from_to).
Defined.

(*
 The two directions of [Functor_Setoid_Nat_Iso] as standalone conversions:
 a natural isomorphism gives functor equality, and vice versa. 

 --------
 [Functor_Setoid_Nat_Iso] 作为独立转换的两个方向：一个自然同构给出函子等价，反之亦然。
*)

Definition iso_equiv {C D : Category} {f g : C ⟶ D} :
  f ≅[Fun] g → f ≈ g := fst (Functor_Setoid_Nat_Iso _ _).

Definition equiv_iso {C D : Category} {f g : C ⟶ D} :
  f ≈ g → f ≅[Fun] g := snd (Functor_Setoid_Nat_Iso _ _).
