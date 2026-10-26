Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.

Generalizable All Variables.

Reserved Infix "×" (at level 41, right associativity).

Section Cartesian.

Context `{C : Category}.

(*
 nLab: https://ncatlab.org/nlab/show/cartesian+category
 nLab: https://ncatlab.org/nlab/show/product
 nLab: https://ncatlab.org/nlab/show/universal+property
 Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)

 A cartesian category is a category equipped with finite products. This
 class axiomatizes the binary product; the nullary product (the terminal
 object 1) is supplied separately by [Terminal] and used below for the
 unitor isomorphisms [prod_one_l] and [prod_one_r].

 The product x × y is characterized by its universal mapping property. It
 comes with two projections,

 exl : x × y ~> x        exr : x × y ~> y,

 and for any object x with morphisms f : x ~> y and g : x ~> z there is a
 pairing ⟨f, g⟩ (written [fork f g], notation f △ g) factoring f and g
 through the projections. The UMP records this factorization together with
 its uniqueness as the biconditional [ump_products]:

 h ≈ ⟨f, g⟩  ↔  exl ∘ h ≈ f  ∧  exr ∘ h ≈ g.

 Read left-to-right, h = ⟨f, g⟩ satisfies the two projection equations
 (existence). Read right-to-left, any h satisfying both equations is equal
 to ⟨f, g⟩ (uniqueness of the mediating morphism). The familiar identities
 exl ∘ ⟨f, g⟩ ≈ f and exr ∘ ⟨f, g⟩ ≈ g ([exl_fork], [exr_fork]) and the
 eta law ⟨exl, exr⟩ ≈ id ([fork_exl_exr]) are corollaries derived below. 

 --------
 nLab:  https://ncatlab.org/nlab/show/cartesian+category 
 nLab:  https://ncatlab.org/nlab/show/product 
 nLab:  https://ncatlab.org/nlab/show/universal+property 
 维基百科:  https://en.wikipedia.org/wiki/Product_(category_theory) 

 笛卡尔范畴是一个配备有限积的范畴。这个类公理化了二元积；零元积（终对象 1）由  [Terminal]  单独提供，并在下面用于幺元同构  [prod_one_l]  和  [prod_one_r] 。

 积 x × y 由其泛映射性质（universal mapping property）特征化。它配备有两个投影：

 exl : x × y ~> x        exr : x × y ~> y,

 对于任何对象 x 以及态射 f : x ~> y 和 g : x ~> z，都存在一个配对 ⟨f, g⟩（写作  [fork f g] ，符号 f △ g）使 f 和 g 通过投影分解。UMP 表示该分解及其唯一性，形式为双条件  [ump_products] ：

 h ≈ ⟨f, g⟩  ↔  exl ∘ h ≈ f  ∧  exr ∘ h ≈ g。从左到右读，h = ⟨f, g⟩ 满足两个投影方程（存在性）。从右到左读，任何满足这两个方程的 h 都等于 ⟨f, g⟩（中介态射的唯一性）。熟悉的恒等式 exl ∘ ⟨f, g⟩ ≈ f 和 exr ∘ ⟨f, g⟩ ≈ g（[exl_fork], [exr_fork]）以及 eta 法则 ⟨exl, exr⟩ ≈ id（[fork_exl_exr]）是下面推导的推论。
*)

(*
 Where the product comes from, and what it is for

 nLab: https://ncatlab.org/nlab/show/cartesian+monoidal+category
 nLab: https://ncatlab.org/nlab/show/Fox%27s+theorem
 nLab: https://ncatlab.org/nlab/show/Markov+category

 The universal mapping property never mentions elements.  Objects of a
 general category are opaque, so x × y cannot be assembled from
 coordinates; [ump_products] instead characterizes the product by how
 every object maps into it — two projections and a unique pairing — and
 the same three pieces of data make sense in any category whatsoever.
 Uniqueness comes with the definition rather than after it: every
 candidate with projections factors uniquely through the true product,
 so any two witnesses are canonically isomorphic (Milewski, “Products
 and Coproducts”, 2015) — which is why [IsCartesianProduct] witnesses
 can be compared by the setoid [CartesianProductStructuresEquiv].

 The element-free formulation was hard won.  Eilenberg and Mac Lane's
 founding paper treats cartesian products only as examples of functors
 (Eilenberg, Mac Lane, “General theory of natural equivalences”, Trans.
 AMS 58, 1945); the general notion of a universal mapping is due to
 Samuel — “the bold step of really formulating the general notion of a
 universal arrow was taken by Samuel in 1948”, in Mac Lane's own words
 (quoted in Porst, “The history of the General Adjoint Functor
 Theorem”, 2024).  Mac Lane's “Duality for groups” (Bull. AMS 56, 1950)
 is the classic early source recasting the direct product of groups
 purely in the language of homomorphisms and composition, so that
 reversing every arrow turns its description into the free product; the
 library collects that dividend in Structure/Cocartesian.v, where the
 coproduct is this class instantiated in the opposite category.  After
 Kan (“Adjoint functors”, Trans. AMS 87(2), 1958), the standard reading
 is adjointness: pairing and unpairing form the hom-set bijection of an
 adjunction between the diagonal and the product, with the diagonal
 morphism as unit and the projections as counit — in-tree as
 [Diagonal_Product_Adjunction] in Adjunction/Diagonal/Product.v, whose
 obligations discharge by this file's [unfork] and [fork_comp].

 Finite products are moreover a doctrine.  A Lawvere theory is a
 category with finite products whose objects are the powers of a single
 generic object, and its models are the product-preserving functors out
 of it (Lawvere, “Functorial Semantics of Algebraic Theories”,
 dissertation 1963); Theory/Lawvere.v carries this class as its
 [law_cartesian] field.  The binary product is the limit of a two-object
 discrete diagram — Structure/Limit/Product.v treats the indexed case —
 it induces the symmetric monoidal structure [CC_CartesianMonoidal] of
 Structure/Monoidal/Internal/Product.v, and it is the base on which
 Structure/Cartesian/Closed.v builds exponentials, extended with
 coproducts in Structure/BiCCC.v.

 Computationally, [fork], [exl] and [exr] form a point-free calculus of
 tuples, and the derived combinators are the arrow vocabulary of
 functional programming: [fork] is the fanout of Hughes' arrow interface
 and [split] routes the input between two arrows (Hughes, “Generalising
 Monads to Arrows”, Science of Computer Programming 37, 2000), with
 [first], [second] and [swap] alongside.  Elliott's translation of
 Haskell into categorical vocabulary turns pattern matching on pairs
 into projections and pair construction into forks, then simplifies
 with the equations proved below (Elliott, “Compiling to Categories”,
 Proc. ACM Program. Lang. 1, ICFP 2017); Tools/Abstraction.v performs
 the same reification for Coq programs, and [Coq_Cartesian] in
 Instance/Coq.v realizes the interface as fst, snd and pairing.

 Fox's theorem locates the cartesian case among tensor products: a
 symmetric monoidal category is cartesian precisely when every object
 carries a unique cocommutative comonoid structure — a copy and a
 discard morphism — with every morphism a homomorphism for it (Fox,
 “Coalgebras and cartesian categories”, Communications in Algebra 4(7),
 1976).  Through [CC_CartesianMonoidal], [CD_of_Cartesian] in
 Structure/Monoidal/CopyDiscard/Proofs.v derives that supply from this
 class, copy being id △ id and discard the terminal map, and
 Structure/Monoidal/Markov/Fox.v proves both directions
 ([all_deterministic_cartesian], [cartesian_all_deterministic]).
 Relaxing naturality of copy is what allows probability: in the Markov
 categories of Cho and Jacobs (2019) and Fritz (2020) every object
 still copies and discards, but a stochastic morphism need not commute
 with copying — flipping a coin and copying its outcome differs from
 flipping two coins — and the cartesian categories are exactly the
 Markov categories whose morphisms are all deterministic. 

 --------
 产品的来源及用途

 nLab: https://ncatlab.org/nlab/show/cartesian+monoidal+category
 nLab: https://ncatlab.org/nlab/show/Fox%27s+theorem
 nLab: https://ncatlab.org/nlab/show/Markov+category

 泛映射性质从未提到元素。一般范畴的对象是不可透视的，因此 x × y 不能从坐标组装而成；[ump_products] 反而通过每个对象如何映射到它来刻画积 —— 两个投影和一个唯一配对 —— 并且同样的三条数据在任何范畴中都是有意义的。唯一性随定义而来，而不是之后：每一个具有投影的候选对象都能唯一地通过真积进行分解，所以任何两个证明者都是自然同构的（Milewski, “Products and Coproducts”, 2015）——这就是为什么 [IsCartesianProduct] 证明者可以通过等价类 [CartesianProductStructuresEquiv] 进行比较的原因。无元素的表述是来之不易的。Eilenberg 和 Mac Lane 的开创性论文仅将笛卡尔积作为函子示例来处理（Eilenberg, Mac Lane, “自然等价的一般理论”, Trans. AMS 58, 1945）；普遍映射的一般概念则归功于 Samuel —— 用 Mac Lane 自己的话说，“真正提出普遍箭的一般概念的大胆步骤是在 1948 年由 Samuel 采取的”（引自 Porst, “一般伴随函子定理的历史”, 2024）。Mac Lane 的《群的对偶性》（Bull.AMS 56, 1950) 是经典的早期文献，将群的直积完全用同态和组合的语言重新表述，因此反转每一条箭头就将其描述转变为自由积；库在 Structure/Cocartesian.v 中收集了这个收益，其中的余积是在对偶范畴中实例化的该类。继 Kan（“伴随函子”，Trans. AMS 87(2), 1958）之后，标准理解是伴随性：配对与拆对构成对角与积之间伴随的 Hom 集双射，对角映射作为单位，投影作为辅单位——在 Adjunction/Diagonal/Product.v 中树内为 [Diagonal_Product_Adjunction]，其义务由本文件的 [unfork] 和 [fork_comp] 解除。有限积进一步是一种学说。Lawvere 理论是一个具有有限积的范畴，其对象是单一通用对象的幂，其模型是从中导出的保持积的函子（Lawvere，《代数理论的函子语义》，1963 年论文）；Theory/Lawvere.v 将这个类作为其 [law_cartesian] 字段。二元积是两个对象离散图的极限——Structure/Limit/Product.v 处理索引情况——它引入了 Structure/Monoidal/Internal/Product.v 的对称幺半结构 [CC_CartesianMonoidal]，并且它是 Structure/Cartesian/Closed.v 构建指数的基础，在 Structure/BiCCC.v 中通过陪积进行扩展。在计算上，[fork]、[exl] 和 [exr] 形成了一个无点元组演算，而派生的组合子则是函数式编程的箭头词汇：[fork] 是 Hughes 箭头接口的分发，而 [split] 将输入在两个箭头之间路由（Hughes，《将单子推广到箭头》，《计算机程序科学》37, 2000），同时还有 [first]、[second] 和 [swap]。Elliott 将 Haskell 翻译成范畴词汇，将对对偶的模式匹配转换为投影，将对偶构造转为分叉，然后用下面证明的方程进行简化（Elliott，《编译到范畴》，《ACM 程序语言学报》）。1，ICFP 2017）；Tools/Abstraction.v 对 Coq 程序执行相同的具体化，[Coq_Cartesian] 在 Instance/Coq.v 中实现了接口，如 fst、snd 和配对。福克斯定理将笛卡尔情况定位于张量积中：当且仅当每个对象都携带唯一的余交换余单子结构——一个复制和一个丢弃态射——并且每个态射都是其同态时，对称单模范畴才是笛卡尔的（Fox，“Coalgebras and cartesian categories”，Communications in Algebra 4(7)，1976）。通过 [CC_CartesianMonoidal]、[CD_of_Cartesian] 在 Structure/Monoidal/CopyDiscard/Proofs.v 中得出来自此类的 supply，其中复制为 id △ id，丢弃为终态射，并且 Structure/Monoidal/Markov/Fox.v 证明了两个方向（[all_deterministic_cartesian]、[cartesian_all_deterministic]）。复制的放松自然性正是允许概率存在的原因：在 Cho 和 Jacobs（2019）以及 Fritz（2020）的马尔可夫范畴中，每个对象仍然可以复制和丢弃，但一个随机态射不必与复制交换——掷一个硬币并复制其结果与掷两个硬币不同——而笛卡尔范畴正是那些所有态射都是确定性的马尔可夫范畴。
*)

(*
   【Class Cartesian 语法与字段展开】/ Syntax & field walkthrough

   1) Class Cartesian：给已有范畴 C 加「二元积」结构。
      Equips C with binary products.

   2) 数据 / Data
      - product_obj / ×  —— 对象 x × y / the product object
      - fork / △         —— 配对 ⟨f,g⟩ : x ~> y×z / pairing
      - exl, exr         —— 左右投影 / left & right projections

   3) 尊重 ≈ / Respect
      - fork_respects : Proper … fork —— f≈f' 且 g≈g' ⇒ ⟨f,g⟩≈⟨f',g'⟩

   4) 普遍性质 / UMP（双条件）
      ump_products : h ≈ ⟨f,g⟩  ↔  (exl∘h ≈ f) * (exr∘h ≈ g)
      左→右：配对满足投影方程；右→左：满足方程的 h 必等于配对（唯一性）。
      Left→right: pairing satisfies projections; right→left: uniqueness.

   5) 常见推论（下文）：exl_fork、exr_fork、fork_exl_exr（η 律）。
      Corollaries below: projection laws and η.

   阅读顺序：product_obj → exl/exr → fork → ump_products。
   Read: product_obj → exl/exr → fork → ump_products.
*)

Class Cartesian := {
  product_obj : obj → obj → obj       (* the product object x × y / 乘积对象 x × y *)
    where "x × y" := (product_obj x y);

  fork {x y z} (f : x ~> y) (g : x ~> z) : x ~> y × z;  (* pairing ⟨f, g⟩ / 配对 ⟨f, g⟩ *)

  exl {x y} : x × y ~> x;             (* first projection (left) / 第一投影（左） *)
  exr {x y} : x × y ~> y;             (* second projection (right) / 第二个投影（右） *)

  fork_respects : ∀ x y z,            (* ⟨-, -⟩ respects ≈ / ⟨-, -⟩ 尊重 ≈ *)
    Proper (equiv ==> equiv ==> equiv) (@fork x y z);

  (*
 ump_products: the universal mapping property of the product. The
 mediating morphism ⟨f, g⟩ is the unique h factoring f and g through the
 projections exl and exr. 

 --------
 ump_products：乘积的通用映射性质。中介态射 ⟨f, g⟩ 是唯一的 h，通过投影 exl 和 exr 分解 f 和 g。
*)
  ump_products {x y z} (f : x ~> y) (g : x ~> z) (h : x ~> y × z) :
    h ≈ fork f g ↔ (exl ∘ h ≈ f) * (exr ∘ h ≈ g)
  }.

(*
 IsCartesianProduct x y z witnesses that the object z is a product of x and
 y, i.e. z plays the role of x × y. It packages the same universal mapping
 property as [Cartesian] but for one designated triple, so that “being a
 product” can be asserted of a specific object rather than a chosen
 operation. 

 --------
 IsCartesianProduct x y z 证明对象 z 是 x 和 y 的乘积，即 z 扮演 x × y 的角色。它封装了与 [Cartesian] 相同的通用映射性质，但针对一个指定的三元组，因此“作为乘积”可以断言特定对象，而不是一个选定的操作。
*)
Class IsCartesianProduct (x y z : C) := {
  fork' {a} (f : a ~> x) (g : a ~> y) : a ~> z;  (* pairing into z / 配对到 z *)

  exl'  : z ~> x;                     (* first projection (left) / 第一投影（左） *)
  exr'  : z ~> y;                     (* second projection (right) / 第二个投影（右） *)

  fork'_respects : ∀ a,               (* ⟨-, -⟩ respects ≈ / ⟨-, -⟩ 尊重 ≈ *)
    Proper (equiv ==> equiv ==> equiv) (@fork' a);

  (*
 ump_product: the universal mapping property for the designated product z. 

 --------
 ump_product：指定积 z 的通用映射性质。
*)
  ump_product {a} (f : a ~> x) (g : a ~> y) (h : a ~> z) :
    h ≈ fork' f g ↔ (exl' ∘ h ≈ f) * (exr' ∘ h ≈ g)
  }.

Program Instance CartesianProductStructuresEquiv (x y z : C) :
  Setoid (IsCartesianProduct x y z) :=
  ({|
             equiv := fun p q => (@exl' _ _ _ p) ≈ (@exl' _ _ _ q) ∧
                                 (@exr' _ _ _ p) ≈ (@exr' _ _ _ q) |}).

#[export] Existing Instance fork_respects.

Infix "×" := product_obj (at level 41, right associativity) : object_scope.
Infix "△" := fork (at level 28) : morphism_scope.

Context `{@Cartesian}.

Definition first  {x y z : C} (f : x ~> y) : x × z ~> y × z :=
  (f ∘ exl) △ exr.

Definition second  {x y z : C} (f : x ~> y) : z × x ~> z × y :=
  exl △ (f ∘ exr).

Definition split  {x y z w : C} (f : x ~> y) (g : z ~> w) :
  x × z ~> y × w :=
  (f ∘ exl) △ (g ∘ exr).

#[export] Program Instance first_respects {a b c : C} :
  Proper (equiv ==> equiv) (@first a b c).
Next Obligation.
  proper.
  unfold first.
  rewrites.
  reflexivity.
Qed.

#[export] Program Instance second_respects {a b c : C} :
  Proper (equiv ==> equiv) (@second a b c).
Next Obligation.
  proper.
  unfold second.
  rewrites.
  reflexivity.
Qed.

#[export] Program Instance split_respects {a b c d : C} :
  Proper (equiv ==> equiv ==> equiv) (@split a b c d).
Next Obligation.
  proper.
  unfold split.
  rewrites.
  reflexivity.
Qed.

Definition swap {x y : C} : x × y ~> y × x := exr △ exl.

Corollary exl_fork {x z w : C} (f : x ~> z) (g : x ~> w) :
  exl ∘ f △ g ≈ f.
Proof.
  intros.
  now apply (ump_products f g (f △ g)).
Qed.

#[local] Hint Rewrite @exl_fork : categories.

Corollary exr_fork {x z w : C} (f : x ~> z) (g : x ~> w) :
  exr ∘ f △ g ≈ g.
Proof.
  intros.
  now apply (ump_products f g (f △ g)).
Qed.

#[local] Hint Rewrite @exr_fork : categories.

Corollary exl_fork_assoc {x y z w} (f : x ~> z) (g : z ~> w) (h : x ~> y) :
  g ∘ exl ∘ (f △ h) ≈ g ∘ f.
Proof.
  rewrite <- comp_assoc.
  apply compose_respects; try reflexivity.
  apply exl_fork.
Qed.

Corollary exr_fork_assoc {x y z w} (f : x ~> z) (g : y ~> w) (h : x ~> y) :
  g ∘ exr ∘ (f △ h) ≈ g ∘ h.
Proof.
  rewrite <- comp_assoc.
  apply compose_respects; try reflexivity.
  apply exr_fork.
Qed.

Corollary exl_fork_comp {x y z w} (f : x ~> y) (g : x ~> z) (h : w ~> x) :
  exl ∘ ((f △ g) ∘ h) ≈ f ∘ h.
Proof.
  rewrite comp_assoc.
  rewrite exl_fork.
  reflexivity.
Qed.

Corollary exr_fork_comp {x y z w} (f : x ~> y) (g : x ~> z) (h : w ~> x) :
  exr ∘ ((f △ g) ∘ h) ≈ g ∘ h.
Proof.
  rewrite comp_assoc.
  rewrite exr_fork.
  reflexivity.
Qed.

Corollary fork_exl_exr {x y : C} :
  exl △ exr ≈ @id C (x × y).
Proof.
  intros.
  symmetry.
  apply ump_products; split; cat.
Qed.

#[local] Hint Rewrite @fork_exl_exr : categories.

Corollary fork_inv {x y z : C} (f h : x ~> y) (g i : x ~> z) :
  f △ g ≈ h △ i ↔ f ≈ h ∧ g ≈ i.
Proof.
  pose proof (ump_products h i (f △ g)) as HA;
  simplify; intuition.
  - now rewrite exl_fork in a.
  - now rewrite exr_fork in b.
  - apply X0; cat.
Qed.

Corollary fork_comp {x y z w : C}
          (f : y ~> z) (h : y ~> w) (g : x ~> y) :
  (f ∘ g) △ (h ∘ g) ≈ f △ h ∘ g.
Proof.
  intros.
  symmetry.
  apply ump_products; split;
  rewrite !comp_assoc; cat.
Qed.

Ltac unfork :=
  unfold swap, split, first, second; simpl;
  repeat (rewrite <- !fork_comp; cat;
          rewrite <- !comp_assoc; cat).

#[local] Obligation Tactic := cat_simpl; unfork.

Definition swap_invol {x y : C} :
  swap ∘ swap ≈ @id C (x × y).
Proof. unfork. Qed.

#[local] Hint Rewrite @swap_invol : categories.

Definition swap_inj_l {x y z : C} (f g : x ~> y × z) :
  swap ∘ f ≈ swap ∘ g → f ≈ g.
Proof.
  intro HA.
  rewrite <- id_left.
  rewrite <- (id_left g).
  rewrite <- swap_invol.
  rewrite <- !comp_assoc.
  now apply compose_respects.
Qed.

Definition swap_inj_r {x y z : C} (f g : x × y ~> z) :
  f ∘ swap ≈ g ∘ swap → f ≈ g.
Proof.
  intro HA.
  rewrite <- id_right.
  rewrite <- (id_right g).
  rewrite <- swap_invol.
  rewrite !comp_assoc.
  now apply compose_respects.
Qed.

Theorem first_id {x y : C} :
  first (id[x]) ≈ id[x × y].
Proof. unfold first; cat. Qed.

#[local] Hint Rewrite @first_id : categories.

Theorem first_comp {x y z w : C} (f : y ~> z) (g : x ~> y) :
  first (z:=w) (f ∘ g) ≈ first f ∘ first g.
Proof. unfork. Qed.

Theorem first_fork {x y z w : C} (f : x ~> y) (g : x ~> z) (h : y ~> w) :
  first h ∘ f △ g ≈ (h ∘ f) △ g.
Proof. unfork. Qed.

Theorem second_id {x y : C} :
  second (id[y]) ≈ id[x × y].
Proof. unfold second; cat. Qed.

#[local] Hint Rewrite @second_id : categories.

Theorem second_comp {x y z w : C} (f : y ~> z) (g : x ~> y) :
  second (z:=w) (f ∘ g) ≈ second f ∘ second g.
Proof. unfork. Qed.

Theorem second_fork {x y z w : C} (f : x ~> y) (g : x ~> z) (h : z ~> w) :
  second h ∘ f △ g ≈ f △ (h ∘ g).
Proof. unfork. Qed.

Corollary exl_first {x y z : C} (f : x ~> y) :
  @exl _ y z ∘ first f ≈ f ∘ exl.
Proof. unfold first; cat. Qed.

#[local] Hint Rewrite @exl_first : categories.

Corollary exr_first {x y z : C} (f : x ~> y) :
  @exr _ y z ∘ first f ≈ exr.
Proof. unfold first; cat. Qed.

#[local] Hint Rewrite @exr_first : categories.

Corollary exl_second {x y z : C} (f : x ~> y) :
  @exl _ z y ∘ second f ≈ exl.
Proof. unfold second; cat. Qed.

#[local] Hint Rewrite @exl_second : categories.

Corollary exr_second {x y z : C} (f : x ~> y) :
  @exr _ z y ∘ second f ≈ f ∘ exr.
Proof. unfold second; cat. Qed.

#[local] Hint Rewrite @exr_second : categories.

Theorem swap_first {x y z : C} (f : x ~> y) :
  swap ∘ first (z:=z) f ≈ second f ∘ swap.
Proof. unfork. Qed.

Theorem swap_second {x y z : C} (f : x ~> y) :
  swap ∘ second f ≈ first (z:=z) f ∘ swap.
Proof. unfork. Qed.

Theorem first_second {x y z w : C} (f : x ~> y) (g : z ~> w) :
  first f ∘ second g ≈ second g ∘ first f.
Proof. unfork. Qed.

Theorem swap_fork {x y z : C} (f : x ~> y) (g : x ~> z) :
  swap ∘ f △ g ≈ g △ f.
Proof. unfork. Qed.

Theorem split_id {x y : C} :
  split (id[x]) (id[y]) ≈ id[x × y].
Proof. unfork; cat. Qed.

#[local] Hint Rewrite @split_id : categories.

Theorem split_comp {x y z w v u : C}
        (f : y ~> z) (h : x ~> y) (g : v ~> u) (i : w ~> v) :
  split f g ∘ split h i ≈ split (f ∘ h) (g ∘ i).
Proof. unfork. Qed.

Theorem split_first {x y z v u : C}
        (f : y ~> z) (h : x ~> y) (g : v ~> u) :
  split f g ∘ first h ≈ split (f ∘ h) g.
Proof. unfork. Qed.

Theorem first_split {x y z v u : C}
        (f : y ~> z) (h : x ~> y) (g : v ~> u) :
  first f ∘ split h g ≈ split (f ∘ h) g.
Proof. unfork. Qed.

Theorem split_second {x y z v u : C}
        (f : y ~> z) (h : x ~> y) (g : v ~> u) :
  split g f ∘ second h ≈ split g (f ∘ h).
Proof. unfork. Qed.

Theorem second_split {x y z v u : C}
        (f : y ~> z) (h : x ~> y) (g : v ~> u) :
  second f ∘ split g h ≈ split g (f ∘ h).
Proof. unfork. Qed.

Theorem exl_split {x y z w : C} (f : x ~> y) (g : z ~> w):
  exl ∘ split f g ≈ f ∘ exl.
Proof. unfork; cat. Qed.

Theorem exr_split {x y z w : C} (f : x ~> y) (g : z ~> w):
  exr ∘ split f g ≈ g ∘ exr.
Proof. unfork; cat. Qed.

Theorem split_fork {x y z w v : C}
          (f : y ~> w) (h : z ~> v) (g : x ~> y) (i : x ~> z):
  split f h ∘ g △ i ≈ (f ∘ g) △ (h ∘ i).
Proof. unfork. Qed.

#[export] Program Instance prod_respects_iso :
  Proper (Isomorphism ==> Isomorphism ==> Isomorphism) product_obj.
Next Obligation.
  proper.
  construct.
  - exact (split (to X) (to X0)).
  - exact (split (from X) (from X0)).
  - now rewrite split_comp, !iso_to_from, split_id.
  - now rewrite split_comp, !iso_from_to, split_id.
Defined.

Context `{@Terminal C}.

#[export] Program Instance prod_one_l  {x : C} :
  1 × x ≅ x := {
  to   := exr;
  from := one △ id
}.
Next Obligation.
  rewrite <- fork_comp.
  rewrite <- fork_exl_exr.
  apply fork_respects; cat.
  apply one_unique.
Qed.

#[local] Hint Rewrite @prod_one_l : isos.

#[export] Program Instance prod_one_r  {x : C} :
  x × 1 ≅ x := {
  to   := exl;
  from := id △ one
}.
Next Obligation.
  rewrite <- fork_comp; cat.
  rewrite <- fork_exl_exr.
  apply fork_respects; cat.
  apply one_unique.
Qed.

#[local] Hint Rewrite @prod_one_r : isos.

#[export] Program Instance prod_comm  {x y : C} :
  x × y ≅ y × x := {
  to   := swap;
  from := swap
}.

#[export] Program Instance prod_assoc  {x y z : C} :
  (x × y) × z ≅ x × (y × z) := {
  to   := (exl ∘ exl) △ ((exr ∘ exl) △ exr);
  from := (exl △ (exl ∘ exr)) △ (exr ∘ exr)
}.
Next Obligation. rewrite fork_comp; cat. Qed.
Next Obligation. rewrite fork_comp; cat. Qed.

Definition toggle {x y : C} : (x × y) × (x × y) ~> (x × x) × (y × y) :=
  split exl exl △ split exr exr.

(* Theorem toggle_fork_fork : / 定理 toggle_fork_fork ： *)
(* toggle ∘ (f △ g) △ (h △ i) ≈ / 切换 ∘ (f △ g) △ (h △ i) ≈ *)

End Cartesian.

Infix "×" := (@product_obj _ _) (at level 41, right associativity) : object_scope.
Notation "x ×[ C ] y" := (@product_obj C _ x y)
  (at level 41, right associativity, only parsing) : object_scope.
Infix "△" := (@fork _ _ _ _ _) (at level 28) : morphism_scope.

#[export] Hint Rewrite @exl_fork : categories.
#[export] Hint Rewrite @exr_fork : categories.
#[export] Hint Rewrite @fork_exl_exr : categories.
#[export] Hint Rewrite @swap_invol : categories.
#[export] Hint Rewrite @prod_one_l : isos.
#[export] Hint Rewrite @prod_one_r : isos.

Ltac unfork :=
  unfold swap, split, first, second; simpl;
  repeat (rewrite <- !fork_comp; cat;
          rewrite <- !comp_assoc; cat).

Section ACartesian.
  Proposition exl'_fork {C : Category} {w x y z: C} {H : IsCartesianProduct x y z}
    (f : w ~> x) (g : w ~> y) :
    exl' ∘ fork' f g ≈ f.
  Proof.
    intros. now apply (ump_product f g ).
  Qed.

  Proposition exr'_fork {C : Category} {w x y z: C} {H : IsCartesianProduct x y z}
    (f : w ~> x) (g : w ~> y) :
    exr' ∘ fork' f g ≈ g.
  Proof.
    intros. now apply (ump_product f g).
  Qed.

  Proposition fork'_natural (C: Category) (v w x y z: C) (H: IsCartesianProduct x y z)
    (f : v ~> w) (a : w ~> x) (b : w ~> y) :
    fork' a b ∘ f ≈ fork' (a ∘ f) (b ∘ f).
  Proof.
    apply ump_product; split; rewrite comp_assoc.
    - now rewrite exl'_fork.
    - now rewrite exr'_fork.
  Qed.

End ACartesian.
