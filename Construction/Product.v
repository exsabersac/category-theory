Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** The product of two categories. / 两个类别的乘积。 *)

(*
 nLab: https://ncatlab.org/nlab/show/product+category
 Wikipedia: https://en.wikipedia.org/wiki/Product_category

 The product category C ∏ D has as objects the pairs (c, d) with c : C and
 d : D, and as morphisms (c, d) ~> (c', d') the pairs (f, g) of a morphism
 f : c ~> c' in C and a morphism g : d ~> d' in D. Identity and composition
 are componentwise: id := (id, id) and (f, g) ∘ (f', g') := (f ∘ f', g ∘ g').
 Equivalence of morphisms is the componentwise conjunction of ≈ in C and ≈
 in D, and the unit and associativity laws hold componentwise because they
 hold in each factor.

 This is the cartesian product in Cat, the category of categories: the
 projection functors Fst and Snd (π₁, π₂ below) exhibit C ∏ D as the
 categorical product of C and D, so a functor E ⟶ C ∏ D is the same as a
 pair of functors E ⟶ C and E ⟶ D. This is the product *of categories*, and
 is distinct from a product *object* inside a single category, formed via a
 universal cone in Structure/Cartesian.v.

 All of the methods are spelled out here to ease simplification. 

 --------
 nLab: https://ncatlab.org/nlab/show/product+category
 Wikipedia: https://en.wikipedia.org/wiki/Product_category

 积范畴 C ∏ D 的对象是形如 (c, d) 的对，其中 c : C，d : D；其态射 (c, d) ~> (c', d') 是由一对态射 (f, g) 组成，其中 f : c ~> c' 在 C 中，g : d ~> d' 在 D 中。恒等态射和复合操作按分量进行：id := (id, id)，(f, g) ∘ (f', g') := (f ∘ f', g ∘ g')。态射的等价性是 C 中 ≈ 和 D 中 ≈ 的分量结合，而且单位律与结合律在每个分量上成立，因为它们在每个因子中都成立。这是 Cat 中的笛卡尔积，即范畴的范畴：投影函子 Fst 和 Snd（下文的 π₁, π₂）将 C ∏ D 显示为 C 和 D 的范畴积，因此一个函子 E ⟶ C ∏ D 与一对函子 E ⟶ C 和 E ⟶ D 是相同的。这是*范畴*的积，与在单个范畴中通过 Structure/Cartesian.v 中的广义锥形成的*对象*的积不同。

 这里列出了所有方法以便于简化。
*)

(*
 Bifunctors, interchange, and the product's place in Cat

 nLab (the rival tensor): https://ncatlab.org/nlab/show/funny+tensor+product

 The product category exists so that a functor of several variables
 requires no theory of its own.  In the founding paper of the subject
 (Eilenberg and Mac Lane, "General Theory of Natural Equivalences",
 Transactions of the AMS 1945), functors in two arguments are axiomatized
 directly: its §3 posits an object-function and a mapping-function subject
 to an identity condition and to an interchange condition equating the
 image of a pair of composites with the interleaved composite of images —
 stated with no product category in sight, for the paper never constructs
 one.  The packaging is the textbook consolidation of Mac Lane,
 Categories for the Working Mathematician, §II.3 (1971), which defines
 C × D, redefines a bifunctor as an ordinary functor out of it, and
 characterizes such functors by two families of partial functors agreeing
 on objects and satisfying interchange.  Riehl introduces the product for
 the same reason, so that the covariant and contravariant represented
 functors "assemble into a single bifunctor, which is the name for a
 functor of two variables" (Riehl, Category Theory in Context, Dover
 2016, Definition 1.3.12).  Once [Product] is in hand, every general
 theorem about functors — naturality, composition, adjunctions, limits —
 applies verbatim to multivariable ones.

 The definition packages the interchange law once and for all.
 Functoriality of F : C ∏ D ⟶ E at a composable pair of pair-morphisms IS
 middle-four exchange: Functor/Bifunctor.v reads it off as [bimap_comp],
 where [bimap] applied to f and g is literally fmap at the pair (f, g)
 ([bimap_fmap] holds at Leibniz equality), and factoring (f, g) through
 (f, id) and (id, g) in either order recovers Mac Lane's two partial
 functors ([bimap_comp_id_left], [bimap_comp_id_right]) together with
 their commutation ([bimap_id_right_left], [bimap_id_left_right]).
 Haskell's Data.Bifunctor class is the same content in type-class form,
 where the default bimap composes the two one-sided actions and is lawful
 precisely because they commute; separate functoriality does not in
 general yield joint functoriality, and the categories where the two
 notions come apart are the premonoidal categories of
 Structure/Premonoidal.v (Milewski, "Functoriality", 2015).  The
 companion construction classifying separately-functorial maps with no
 interchange at all is the funny tensor product of Construction/Funny.v;
 indeed Cat carries exactly two symmetric closed monoidal structures —
 this cartesian product and the funny tensor — and no others (Foltz,
 Lair and Kelly, "Algebraic categories with few monoidal biclosed
 structures or none", Journal of Pure and Applied Algebra 1980).

 Mixed variance is handled through opposites: contravariance in one slot
 is covariance from the opposite category in that slot, and
 [Product_Opposite] makes the bookkeeping free of transport.  The leading
 example is the hom bifunctor [Hom] : C^op ∏ C ⟶ Sets of Functor/Hom.v,
 whose curried form [Curried_Hom] underlies the Yoneda development;
 further consumers include the tensor ⊗ : C ∏ C ⟶ C of
 Structure/Monoidal.v, horizontal composition [hcompose] in
 Theory/Bicategory.v, profunctors C ⇸ D as functors C^op ∏ D ⟶ Sets in
 Theory/Profunctor.v, and the dinatural transformations of
 Theory/Dinatural.v.  The tensor bifunctor also carries the physical
 reading of monoidal categories, modelling composite systems in quantum
 foundations and quantum informatics (Coecke and Paquette, "Categories
 for the practising physicist", 2009); the ZX-calculus instance
 Instance/ZX.v imports this file for exactly that tensor.  Double
 diagrams are functors from a product of index categories, and [Swap] is
 the symmetry through which limits over them are interchanged (Riehl
 2016, Theorem 3.8.1).  Within Cat itself, Instance/Cat/Cartesian.v
 takes this construction as the product object,
 Functor/Construction/Product.v supplies its action on functors F ∏⟶ G,
 and Instance/Cat/Cartesian/Closed.v adds the currying isomorphism,
 exhibiting Cat as cartesian closed. 

 --------
 双函子、交换以及积在Cat中的位置

 nLab（竞争张量）：https://ncatlab.org/nlab/show/funny+tensor+product产品范畴的存在是为了使多个变量的函子不需要自身的理论。在该学科的创始论文（Eilenberg 和 Mac Lane，《自然同构的一般理论》，美国数学会学报 1945 年）中，两个参数的函子被直接公理化：其第 3 节设定了一个对象函数和一个映射函数，并遵循一个恒等条件和一个交换条件，将一对复合的像与像的交错复合相等 — 文中没有出现产品范畴，因为该论文从未构造过它。这个包装是 Mac Lane 《为工作中的数学家而写的范畴论》第 II.3 节（1971 年）的教材式总结，该书定义了 C × D，将双函子重新定义为从它出发的普通函子，并通过两族在对象上相符且满足交换律的部分函子来刻画这样的函子。Riehl 引入乘积的原因也是相同的，以便协变和逆变的表象函子“组合成一个单一的双函子，这就是二元函子的名称”（Riehl，《语境中的范畴论》，Dover 2016，第 1.3.12 定义）。一旦掌握了 [Product]，每一个关于函子的一般定理——自然性、复合、伴随、极限——都可以直接应用于多变量函子。这个定义一次性地封装了交换律。函子 F : C ∏ D ⟶ E 在一对可组合的对态射上的函子性是中间四交换：Functor/Bifunctor.v 将其读作 [bimap_comp]，其中 [bimap] 应用于 f 和 g 时字面上就是在对 (f, g) 上的 fmap（[bimap_fmap] 在 Leibniz 等式下成立），并且通过任意顺序将 (f, g) 分解为 (f, id) 和 (id, g) 可以恢复 Mac Lane 的两个部分函子（[bimap_comp_id_left], [bimap_comp_id_right]）及其对换性（[bimap_id_right_left], [bimap_id_left_right]）。Haskell 的 Data.Bifunctor 类在类型类形式中包含相同的内容，其中默认的 bimap 组合了两个单侧操作，并且这是合乎规律的，因为它们是可交换的；单独的函子性通常不能产生联合函子性，而这两种概念分离的范畴是 Structure/Premonoidal.v 中的前单元范畴（Milewski，“Functoriality”，2015）。分类完全没有交替的单独函子映射的伴随构造是 Construction/Funny.v 中的有趣张量积；实际上 Cat 恰好具有两种对称闭单范畴结构——这个笛卡尔积和有趣张量——而没有其他结构（Foltz、Lair 和 Kelly，“代数范畴中具有很少或没有单范畴闭结构”，Journal of Pure and Applied Algebra 1980）。混合变差通过对立来处理：一个槽中的逆变是该槽中来自相对范畴的协变，而 [Product_Opposite] 使得记账无需传输。主要示例是函子/Hom.v 中的同态双函子 [Hom] : C^op ∏ C ⟶ Sets，其柯里化形式 [Curried_Hom] 是 Yoneda 展开的基础；进一步的使用者包括 Structure/Monoidal.v 中的张量 ⊗ : C ∏ C ⟶ C，Theory/Bicategory.v 中的水平组合 [hcompose]，作为函子 C^op ∏ D ⟶ Sets 的 Profunctors C ⇸ D 在 Theory/Profunctor.v 中，以及 Theory/Dinatural.v 中的双自然变换。张量双函子也承载着单体范畴的物理解读，在量子基础和量子信息学中对复合系统建模（Coecke 和 Paquette，《Categories for the practising physicist》，2009）；ZX-演算的实例 Instance/ZX.v 正是为了该张量而导入此文件。双图是从指标范畴的积出的函子，而 [Swap] 是通过它们交换极限的对称性（Riehl 2016，第 3.8.1 定理）。在 Cat 本身中，Instance/Cat/Cartesian.v 将此构造作为积对象，Functor/Construction/Product.v 提供其在函子 F ∏⟶ G 上的作用，Instance/Cat/Cartesian/Closed.v 增加了柯里化同构，展示了 Cat 作为笛卡尔闭范畴。
*)

(*
   【Product 范畴定义展开】/ Product walkthrough
   （口吻对齐 Theory/Category.v；受众：Coq 小白 + 范畴论小白的 Haskell 程序员）

   1) 这是什么 / What this is
      Product C D = C ∏ D：对象是对 (c,d)，态射是对 (f,g)，运算分量做。
      Product of categories (in Cat), not a product *object* inside one category
      (that is Structure/Cartesian.v).
      Haskell 对照：Data.Bifunctor 的「两个参数一起变」—— bifunctor = 出积范畴的函子。
      Haskell: Bifunctor ≈ ordinary Functor out of C ∏ D.

   2) 关键字段 / Key fields
      - obj  := C * D
      - hom  := 分量 Hom 的积 / product of component homs
      - ≈    := 分量 ≈ 的合取 / componentwise ≈
      - id   := (id, id)；compose 分量复合 / componentwise compose

   3) 投影 / Projections
      Fst / Snd（π₁, π₂）：忘掉另一分量；E ⟶ C ∏ D ≃ 一对函子 E ⟶ C 与 E ⟶ D。
      A map into the product is a pair of maps.

   阅读：对象对 → 态射对 → 分量 ≈ → id/compose → Fst/Snd。
   Read: object pairs → morphism pairs → componentwise ≈ → ops → projections.
*)

Definition Product (C D : Category) : Category := {|
  obj     := C * D;
  hom     := fun x y => (fst x ~> fst y) * (snd x ~> snd y);
  homset  := fun x y =>
    let setoid_C := @homset C (fst x) (fst y) in
    let setoid_D := @homset D (snd x) (snd y) in
    {| equiv := fun f g =>
         (@equiv _ setoid_C (fst f) (fst g) *
          @equiv _ setoid_D (snd f) (snd g))
     ; setoid_equiv := _
         {| Equivalence_Reflexive  := fun x =>
              (@Equivalence_Reflexive _ _ (@setoid_equiv _ setoid_C) (fst x),
               @Equivalence_Reflexive _ _ (@setoid_equiv _ setoid_D) (snd x))
          ; Equivalence_Symmetric  := fun x y f =>
              (@Equivalence_Symmetric
                 _ _ (@setoid_equiv _ setoid_C) (fst x) (fst y) (fst f),
               @Equivalence_Symmetric
                 _ _ (@setoid_equiv _ setoid_D) (snd x) (snd y) (snd f))
          ; Equivalence_Transitive := fun x y z f g =>
              (@Equivalence_Transitive
                 _ _ (@setoid_equiv _ setoid_C) (fst x) (fst y) (fst z)
                 (fst f) (fst g),
               @Equivalence_Transitive
                 _ _ (@setoid_equiv _ setoid_D) (snd x) (snd y) (snd z)
                 (snd f) (snd g)) |} |};
  id      := fun _ => (id, id);
  compose := fun _ _ _ f g => (fst f ∘ fst g, snd f ∘ snd g);

  compose_respects := fun x y z f g fg h i hi =>
    (compose_respects (fst f) (fst g) (fst fg) (fst h) (fst i) (fst hi),
     compose_respects (snd f) (snd g) (snd fg) (snd h) (snd i) (snd hi));

  id_left  := fun x y f =>
    (@id_left C (fst x) (fst y) (fst f),
     @id_left D (snd x) (snd y) (snd f));
  id_right := fun x y f =>
    (@id_right C (fst x) (fst y) (fst f),
     @id_right D (snd x) (snd y) (snd f));

  comp_assoc := fun x y z w f g h =>
    (@comp_assoc C (fst x) (fst y) (fst z) (fst w) (fst f) (fst g) (fst h),
     @comp_assoc D (snd x) (snd y) (snd z) (snd w) (snd f) (snd g) (snd h));
  comp_assoc_sym := fun x y z w f g h =>
    (@comp_assoc_sym C (fst x) (fst y) (fst z) (fst w) (fst f) (fst g) (fst h),
     @comp_assoc_sym D (snd x) (snd y) (snd z) (snd w) (snd f) (snd g) (snd h))
|}.

Notation "C ∏ D" := (@Product C D) (at level 90) : category_scope.

Require Import Category.Theory.Functor.

(*
 First projection functor π₁ : C ∏ D ⟶ C, taking (c, d) to c on objects and
 (f, g) to f on morphisms. 

 --------
 第一个投影函子 π₁ : C ∏ D ⟶ C，将对象 (c, d) 映射为 c，将态射 (f, g) 映射为 f。
*)
#[export]
Program Instance Fst {C D : Category} : C ∏ D ⟶ C := {
  fobj := fst;                          (* (c, d) ↦ c *)
  fmap := fun _ _ => fst                (* (f, g) ↦ f *)
}.

(*
 Second projection functor π₂ : C ∏ D ⟶ D, taking (c, d) to d on objects and
 (f, g) to g on morphisms. 

 --------
 第二投影函子 π₂ : C ∏ D ⟶ D，在对象上将 (c, d) 映射到 d，在态射上将 (f, g) 映射到 g。
*)
#[export]
Program Instance Snd {C D : Category} : C ∏ D ⟶ D := {
  fobj := snd;                          (* (c, d) ↦ d *)
  fmap := fun _ _ => snd                (* (f, g) ↦ g *)
}.

(*
 The symmetry functor C ∏ D ⟶ D ∏ C exchanging the two factors, witnessing
 that the product of categories is commutative up to isomorphism. 

 --------
 对称函子 C ∏ D ⟶ D ∏ C 交换两个因子，表明类别的乘积在同构意义下是交换的。
*)
Program Definition Swap
        {C : Category} {D : Category} : (C ∏ D) ⟶ (D ∏ C) := {|
  fobj := fun x => (snd x, fst x);      (* (c, d) ↦ (d, c) *)
  fmap := fun _ _ f => (snd f, fst f);  (* (f, g) ↦ (g, f) *)
|}.

Corollary fst_comp {C : Category} {D : Category} x y z
          (f : y ~{C ∏ D}~> z) (g : x ~{C ∏ D}~> y) :
  fst f ∘ fst g ≈ fst (f ∘ g).
Proof. reflexivity. Qed.

Corollary snd_comp {C : Category} {D : Category} x y z
          (f : y ~{C ∏ D}~> z) (g : x ~{C ∏ D}~> y) :
  snd f ∘ snd g ≈ snd (f ∘ g).
Proof. reflexivity. Qed.

Require Import Category.Construction.Opposite.

(*
 The opposite of a product is the product of the opposites, on the nose:
 both Opposite and Product act componentwise, so the two categories are
 definitionally equal (hence the proof by reflexivity, using =). 

 --------
 乘积的对立面是对立面的乘积，恰好如此：
 对立和乘积都是按组件作用的，因此这两个范畴在定义上是相等的（因此通过自反性使用 = 进行证明）。
*)
Corollary Product_Opposite {C D : Category} : (C ∏ D) ^op = (C^op ∏ D^op).
Proof. reflexivity. Qed.
