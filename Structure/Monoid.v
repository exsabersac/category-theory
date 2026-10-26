Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* * * Monoid objects in a monoidal category / * * 单含范畴中的幺半群对象 *)

(*
 nLab:      https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category
 Wikipedia: https://en.wikipedia.org/wiki/Monoid_(category_theory)

 Given a monoidal category (C, ⨂, I), a monoid object on an object [mon : C]
 is a triple (mon, mappend, mempty) consisting of a multiplication
 [mappend : mon ⨂ mon ~> mon] and a unit [mempty : I ~> mon] subject to the
 associativity and left/right unit laws, with the associator and unitors
 inserted so the maps compose:

 associativity  mappend ∘ (mappend ⨂ id) ≈ mappend ∘ (id ⨂ mappend) ∘ α
 left unit      mappend ∘ (mempty ⨂ id)  ≈ λ
 right unit     mappend ∘ (id ⨂ mempty)  ≈ ρ

 Here ⨂ on morphisms is [bimap], α = [to tensor_assoc] is the associator
 (mon ⨂ mon) ⨂ mon ≅ mon ⨂ (mon ⨂ mon), and λ = [to unit_left],
 ρ = [to unit_right] are the left/right unitors I ⨂ mon ≅ mon and
 mon ⨂ I ≅ mon. This is exactly the nLab/Wikipedia definition (the names
 [mempty]/[mappend] echo Haskell's [Monoid] type class).

 Relationship to [Theory.Algebra.Monoid]: that file defines the very same
 structure under the name [Monoid] with fields [mu]/[eta], as a standalone
 abstract building block (used for Frobenius algebras and dualised to give
 comonoids). This file is the older, richer development: it specialises the
 monoid object to a cartesian monoidal category (giving an ordinary monoid)
 and proves closure under products ([Product_Monoid]) and exponentials
 ([Hom_Monoid]). The two definitions are equivalent up to field renaming. 

 --------
 nLab：https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category
 Wikipedia：https://en.wikipedia.org/wiki/Monoid_(category_theory)

 给定一个单体范畴 (C, ⨂, I)，在对象 [mon : C] 上的单体对象是一个三元组 (mon, mappend, mempty)，它由一个乘法 [mappend : mon ⨂ mon ~> mon] 和一个单位 [mempty : I ~> mon] 组成，并满足结合律及左/右单位律，其中插入了结合子和单位子以使映射可组合：

 结合律：mappend ∘ (mappend ⨂ id) ≈ mappend ∘ (id ⨂ mappend) ∘ α
 左单位律：mappend ∘ (mempty ⨂ id) ≈ λ
 右单位律：mappend ∘ (id ⨂ mempty) ≈ ρ这里 ⨂ 在态射上是 [bimap]，α = [to tensor_assoc] 是结合子
 (mon ⨂ mon) ⨂ mon ≅ mon ⨂ (mon ⨂ mon)，而 λ = [to unit_left]，
 ρ = [to unit_right] 是左/右幺元子 I ⨂ mon ≅ mon 和
 mon ⨂ I ≅ mon。这正是 nLab/Wikipedia 的定义（名称
 [mempty] / [mappend] 呼应 Haskell 的 [Monoid] 类型类）。与 [Theory.Algebra.Monoid] 的关系：该文件以 [Monoid] 的名称定义了完全相同的结构，包含字段 [mu] / [eta]，作为一个独立的抽象构建模块（用于 Frobenius 代数并进行对偶化以生成余单元）。该文件是较早、更完善的开发版本：它将幺半群对象专门化到笛卡尔幺半群范畴（生成普通幺半群）并证明了乘积（[Product_Monoid]）和指数（[Hom_Monoid]）的封闭性。这两个定义在字段重命名后是等价的。
*)

(*
 One definition, many algebras: what internalization is for

 nLab:  https://ncatlab.org/nlab/show/microcosm+principle
 nLab:  https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
 nLab:  https://ncatlab.org/nlab/show/Day+convolution
 Paper: Eckmann, Hilton, “Group-like structures in general categories
 I. Multiplications and comultiplications”, Mathematische
 Annalen 145, 1962
 Paper: Bénabou, “Algèbre élémentaire dans les catégories”, C. R.
 Acad. Sci. Paris 258, 1964
 Paper: Rivas, Jaskelioff, “Notions of Computation as Monoids”, 2014

 The systematic study of algebraic structure carried by an OBJECT of
 a category, rather than by a set, begins with Eckmann and Hilton
 (Math. Ann. 145, 1962), whose motivation was homotopy theory: to
 explain why group structures arise on homotopy classes and why they
 are natural.  nLab cites Bénabou (1964) for the definition of a
 monoid in a monoidal category itself; the textbook treatment is
 Mac Lane, Categories for the Working Mathematician, Sections III.6
 and VII.3.

 A monoidal category is exactly enough structure to state the monoid
 axioms, and each choice of ambient category then instantiates a
 different classical theory.  In Set with the cartesian product,
 [MonoidObject] yields ordinary monoids; in abelian groups under the
 tensor product, rings; in R-modules, associative unital R-algebras;
 in endofunctors under composition, monads; and in C^op, comonoids in
 C (nLab, “monoid in a monoidal category”).  It follows that a
 theorem proved once at this generality — closure under products,
 transport along lax monoidal functors, free monoids — specializes
 everywhere at once.  The library proves the canonical instance one
 directory away: Mac Lane's dictum that a monad “is just a monoid in
 the category of endofunctors” (op. cit., 2nd ed., p. 138) is
 [Monoid_Monad] in Monad/Monoid.v, a logical equivalence between
 [MonoidObject] at the composition tensor and a [Monad].  Yet the
 tensor is genuinely a parameter: a monoid object in StrictCat under
 the funny tensor is a strict premonoidal category
 (Instance/StrictCat/Premonoid.v), so changing the tensor changes
 what a monoid is.

 Two structural principles govern the tower.  Downward, the fact that
 a monoid object can only be stated inside a categorified monoid — a
 monoidal category — is the prototype of the microcosm principle of
 Baez and Dolan (“Higher-Dimensional Algebra III”, 1997): certain
 algebraic structures can be defined in any category equipped with a
 categorified version of the same structure.  Upward, the
 Eckmann–Hilton argument shows that iterating the definition adds no
 generality: a monoid object in the category of monoids is already a
 commutative monoid, so the next rung is braided or symmetric
 structure rather than a second multiplication.  The same argument
 appears in this library at Structure/Semiadditive.v, where the two
 convolutions on hom-sets satisfy interchange and therefore coincide,
 commute, and associate.

 The computational reading is direct: the header already notes that
 [mempty] and [mappend] are borrowed from Haskell's Monoid class, and
 the cartesian section below supplies the categorical semantics of
 two standard library instances — [Product_Monoid] is the
 componentwise monoid on pairs, and [Hom_Monoid] is the pointwise
 monoid on functions into a monoid, with [doppel] distributing the
 shared argument to both evaluations, obtained internally via
 currying.  Rivas and Jaskelioff (“Notions of Computation as
 Monoids”, 2014) carry the pattern further: monads, applicative
 functors, and arrows are all monoids in suitable monoidal
 categories, so free constructions and Cayley representations
 transfer uniformly.  On nLab's account of Day convolution, monoids
 for the Day tensor are the lax monoidal functors underlying
 Applicative; Construction/Day.v builds that tensor in-tree, though
 this correspondence is not yet proved here.  Within the library,
 [MonoidObject] is also the base of a tower of one-object structures:
 [GroupObject] in Structure/Group.v extends it with an inverse, and
 Theory/Algebra/Frobenius.v pairs the sibling definition of
 Theory/Algebra/Monoid.v with a comonoid on the same carrier to form
 Frobenius algebras. 

 --------
 一个定义，许多代数：内在化的作用

 nLab:   https://ncatlab.org/nlab/show/microcosm+principle 
 nLab:   https://ncatlab.org/nlab/show/Eckmann-Hilton+argument 
 nLab:   https://ncatlab.org/nlab/show/Day+convolution 
 论文: Eckmann, Hilton, “一般范畴中的类群结构 I. 乘法和余乘法”, 数学年刊 145, 1962
 论文: Bénabou, “范畴中的初等代数”, 巴黎科学院院刊 258, 1964
 论文: Rivas, Jaskelioff, “作为模的计算概念”, 2014对一个范畴中的对象而不是一个集合所携带的代数结构的系统研究，始于 Eckmann 和 Hilton（Math. Ann. 145, 1962），他们的动机是同伦理论：解释为什么群结构会出现在同伦类上以及它们为何是自然的。nLab 引用 Bénabou (1964) 来定义单幺半群在幺半群范畴中的定义；教材的处理是 Mac Lane 《为工作数学家而写的范畴论》，第 III.6 和 VII.3 节。一个幺半范畴恰好具有陈述幺半群公理的结构，然后每个所选的环境范畴就会实例化一个不同的经典理论。在集合范畴（Set）中使用笛卡尔积时，[MonoidObject] 产生普通的幺半群；在阿贝尔群范畴下使用张量积时，产生环；在 R-模中，产生结合并有单位的 R-代数；在自函子范畴下使用复合时，产生单子；在 C^op 中，产生 C 中的余幺半群（nLab，“幺半范畴中的幺半群”）。因此，一个在这种一般性下证明过的定理——关于乘积的封闭性、沿松幺半函子的迁移、自由幺半群——可以同时在各处特化。该库证明了一个典型实例，仅在一个目录之外：Mac Lane 的格言，即单子“只是自函子范畴中的一个幺半群”（同上，第 2 版，第 页）。138) 是在 Monad/Monoid.v 中的 [Monoid_Monad]，一个逻辑等价于在组合张量下的 [MonoidObject] 和 [Monad]。然而，张量实际上是一个参数：在 StrictCat 下的有趣张量下的幺半群对象是一个严格的前模范范畴 (Instance/StrictCat/Premonoid.v)，所以改变张量就会改变幺半群的定义。塔由两个结构原则支配。向下看，单元对象只能在一个范畴化的单元——一个幺半群范畴中表述——这是 Baez 和 Dolan 的微观原则的原型（“Higher-Dimensional Algebra III”, 1997）：某些代数结构可以在任何配备了其范畴化版本的同一结构的范畴中定义。向上看，Eckmann–Hilton 论证表明，迭代定义不会增加一般性：在单元范畴中的单元对象已经是交换幺半群，因此下一阶是编织或对称结构，而不是第二次乘法。这个论证在本库的 Structure/Semiadditive.v 中也出现过，在那里同态集上的两个卷积满足交换律，因此它们一致、可交换且满足结合律。

 计算性阅读是直接的：标题已经指出 [mempty] 和 [mappend] 借鉴自 Haskell 的 Monoid 类，下面的笛卡尔部分提供了两个标准库实例的范畴语义 —— [Product_Monoid] 是对对偶的分量单子，[Hom_Monoid] 是对映射到单子的函数的逐点单子，[doppel] 将共享参数分发到两个求值中，通过柯里化在内部获得。Rivas 和 Jaskelioff（“Notions of Computation as Monoids”，2014）进一步扩展了这一模式：单子、应用函子和箭头在适当的单子范畴中都是单子，因此自由构造和 Cayley 表示可以统一转移。在 nLab 对 Day 卷积的描述中，Day 张量的幺半群是支撑 Applicative 的松单态函子；Construction/Day.v 在树内构建该张量，尽管这种对应关系在此还未被证明。在库中，[MonoidObject] 也是一组一对象结构的基础：Structure/Group.v 中的 [GroupObject] 为其增加了逆元，而 Theory/Algebra/Frobenius.v 将 Theory/Algebra/Monoid.v 的兄弟定义与同一载体上的余幺半群配对，形成 Frobenius 代数。
*)

Section MonoidObject.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class MonoidObject (mon : C) := {
  mempty  : I ~> mon;             (* unit η : I ~> mon / 单位 η : I ~> 蒙 *)
  mappend : mon ⨂ mon ~> mon;     (* multiplication μ : mon ⨂ mon ~> mon / 乘法 μ : mon ⨂ mon ~> mon *)

  (* left unit law: mappend ∘ (mempty ⨂ id) ≈ λ (left unitor I ⨂ mon ≅ mon) / 左单位律：mappend ∘ (mempty ⨂ id) ≈ λ (左单元元 I ⨂ mon ≅ mon) *)
  mempty_left : mappend ∘ bimap mempty id ≈ to (@unit_left C _ mon);
  (* right unit law: mappend ∘ (id ⨂ mempty) ≈ ρ (right unitor mon ⨂ I ≅ mon) / 右单位律：mappend ∘ (id ⨂ mempty) ≈ ρ (右单位子单 ⨂ I ≅ 单) *)
  mempty_right : mappend ∘ bimap id mempty ≈ to (@unit_right C _ mon);

  (* associativity, with the associator α reassociating the triple tensor: (mon ⨂ mon) ⨂ mon ≅ mon ⨂ (mon ⨂ mon) / 结合性，结合子 α 对三重张量进行重新结合： (mon ⨂ mon) ⨂ mon ≅ mon ⨂ (mon ⨂ mon) *)
  mappend_assoc :
    mappend ∘ bimap mappend id ≈ mappend ∘ bimap id mappend ∘ to tensor_assoc
}.

Context (mon : C).
Context `{@MonoidObject mon}.

(* Symmetric form of [mappend_assoc], reassociating in the opposite direction by composing with the inverse associator [tensor_assoc ⁻¹]. / [mappend_assoc] 的对称形式，通过与逆结合算子 [tensor_assoc ⁻¹] 组合，在相反方向上重新结合。 *)
Lemma mappend_assoc_sym :
  mappend ∘ bimap id mappend ≈ mappend ∘ bimap mappend id ∘ (tensor_assoc ⁻¹).
Proof.
  rewrite mappend_assoc.
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  cat.
Qed.

End MonoidObject.

(* Projections to the unit and multiplication of a given monoid object [M]. / 到单位的投影以及给定幺半群对象 [M] 的乘法。 *)
Notation "mempty[ M ]" := (@mempty _ _ _ M)
  (at level 9, format "mempty[ M ]") : category_scope.
Notation "mappend[ M ]" := (@mappend _ _ _ M)
  (at level 9, format "mappend[ M ]") : category_scope.

Section Monoid.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

(*
 A monoid object for the cartesian monoidal structure [CC_Monoidal] (tensor
 = categorical product ×, unit = terminal object 1) is a monoid in the usual
 sense, with [mappend] reducing a product of two objects to one.

 nLab: “Classical monoids are of course just monoids in Set with the
 cartesian product.” 

 --------
 笛卡尔单幺半群结构 [CC_Monoidal]（张量 = 范畴积 ×，单位 = 终对象 1）的单幺半群对象，在通常意义下就是一个单幺半群，其中 [mappend] 将两个对象的积化为一个对象。

 nLab：“经典单幺半群当然就是具有笛卡尔积的 Set 中的单幺半群。”
*)
Definition Monoid := @MonoidObject C CC_Monoidal.

(*
 The categorical product of two monoids is again a monoid, multiplying and
 uniting componentwise; [toggle] rearranges (x × y) × (x × y) into the
 (x × x) × (y × y) form expected by the componentwise [split] of the
 two multiplications. 

 --------
 两个幺半群的范畴积仍然是一个幺半群，通过分量逐一相乘和联合；[toggle] 将 (x × y) × (x × y) 重排为 (x × x) × (y × y) 的形式，这是两个乘法的分量逐一 [split] 所期待的形式。
*)
#[export] Program Instance Product_Monoid `(X : Monoid x) `(Y : Monoid y) :
  @MonoidObject C CC_Monoidal (x × y) := {|
  mempty  := @mempty _ _ _ X △ @mempty _ _ _ Y;
  mappend := split (@mappend _ _ _ X) (@mappend _ _ _ Y) ∘ toggle
|}.
Next Obligation.
  spose (@mempty_left _ _ _ X) as HX.
  spose (@mempty_left _ _ _ Y) as HY.
  assert ((mempty[X] △ mempty[Y] ∘ exl) △ (id[x × y] ∘ exr)
            ≈ split (mempty[X] △ mempty[Y]) id[x × y])
    by (unfork; cat).
  rewrite X0; clear X0.
  unfold toggle.
  rewrite <- !comp_assoc.
  rewrite <- fork_comp.
  rewrite !split_comp.
  rewrite exl_fork, exr_fork.
  rewrite !id_right.
  rewrite <- (id_right mempty[X]).
  rewrite <- (id_left exl).
  rewrite <- (id_right mempty[Y]).
  rewrite <- (id_left exr).
  rewrite <- !split_comp.
  rewrite split_fork.
  rewrite !comp_assoc.
  rewrite HX, HY.
  unfold split; cat.
  now rewrite fork_comp; cat.
Qed.
Next Obligation.
  spose (@mempty_right _ _ _ X) as HX.
  spose (@mempty_right _ _ _ Y) as HY.
  assert ((id[x × y] ∘ exl) △ (mempty[X] △ mempty[Y] ∘ exr)
            ≈ split id[x × y] (mempty[X] △ mempty[Y]))
    by (unfork; cat).
  rewrite X0; clear X0.
  unfold toggle.
  rewrite <- !comp_assoc.
  rewrite <- fork_comp.
  rewrite !split_comp.
  rewrite exl_fork, exr_fork.
  rewrite !id_right.
  rewrite <- (id_right mempty[X]).
  rewrite <- (id_left exl).
  rewrite <- (id_right mempty[Y]).
  rewrite <- (id_left exr).
  rewrite <- !split_comp.
  rewrite split_fork.
  rewrite !comp_assoc.
  rewrite HX, HY.
  unfold split; cat.
  now rewrite fork_comp; cat.
Qed.
Next Obligation.
  spose (@mappend_assoc _ _ _ X) as HX.
  spose (@mappend_assoc _ _ _ Y) as HY.
  assert ((split mappend[X] mappend[Y] ∘ toggle ∘ exl) △ (id[x × y] ∘ exr)
            ≈ split (split mappend[X] mappend[Y] ∘ toggle) id[x × y])
    by (unfork; cat).
  rewrite X0; clear X0.
  assert ((id[x × y] ∘ exl) △ (split mappend[X] mappend[Y] ∘ toggle ∘ exr)
            ≈ split id[x × y] (split mappend[X] mappend[Y] ∘ toggle))
    by (unfork; cat).
  rewrite X0; clear X0.
  unfold toggle.
  rewrite !split_fork.
  rewrite <- !fork_comp.
  rewrite <- !comp_assoc.
  rewrite !split_fork.
  rewrite !id_left.
  rewrite !comp_assoc.
  rewrite !exl_fork.
  rewrite !exr_fork.
  rewrite <- !comp_assoc.
  rewrite !split_comp.
  rewrite !exl_fork.
  rewrite !exr_fork.
  rewrite !id_right.
  rewrite <- (id_left (exl (x:=x) (y:=y))) at 1.
  rewrite <- (id_left (exr (x:=x) (y:=y))) at 1.
  rewrite <- !split_comp.
  rewrite !comp_assoc.
  rewrite HX, HY.
  rewrite !id_left.
  apply fork_respects; clear;
  now unfold split; unfork; cat.
Qed.

Context `{@Closed C _}.

(*
 Duplicate the [z] component across both halves of a product:
 (x × y) × z ~> (x × z) × (y × z). Used to feed the shared argument to both
 pointwise multiplications in [Hom_Monoid]. 

 --------
 在产品的两半中复制[z]组件：
 (x × y) × z ~> (x × z) × (y × z)。用于将共享参数提供给[Hom_Monoid]中的两个逐点乘法。
*)
Definition doppel {x y z : C} : (x × y) × z ~> (x × z) × (y × z) :=
  first exl △ first exr.

(*
 The pair of uncurried projections equals evaluating both function arguments
 at the shared point, after distributing that point via [doppel]. 

 --------
 这对非柯里化投影等于在通过 [doppel] 分配该点之后，在共享点上评估两个函数参数。
*)
Lemma uncurry_exl_fork_exr {x y : C} :
  uncurry exl △ uncurry exr ≈ split eval eval ∘ @doppel (y ^ x) (y ^ x) x.
Proof.
  unfold doppel.
  rewrite split_fork.
  now rewrite !eval_first.
Qed.

(*
 The exponential [y ^ x] inherits a monoid structure pointwise from a monoid
 [Y] on [y]: the unit is the constant function at [mempty[Y]], and two
 functions are combined by evaluating each at the same point and multiplying
 the results with [mappend[Y]]. This is the “monoid of functions into a
 monoid”, obtained here internally via currying. 

 --------
 指数 [y ^ x] 从 [y] 上的幺半群 [Y] 按点继承幺半群结构：单位元是值为 [mempty[Y] 的常函数，而两个函数通过在同一点上分别求值并用 [mappend[Y] 相乘来组合。这是“映入一个幺半群的函数的幺半群”，在此通过内部的柯里化得到。
*)
#[export] Program Instance Hom_Monoid {x} `(Y : Monoid y) :
  @MonoidObject C CC_Monoidal (y ^ x) := {
  mempty  := curry (@mempty _ _ _ Y ∘ exl);
  mappend := curry (@mappend _ _ _ Y ∘ uncurry exl △ uncurry exr)
}.
Next Obligation.
  spose (@mempty_left _ _ _ Y) as HY.
  remember ((curry _ ∘ exl) △ (id[y ^ x] ∘ exr)) as h.
  assert (h ≈ split (curry (mempty[Y] ∘ exl)) id[y ^ x])
    by (rewrite Heqh; unfork; cat).
  rewrite X; clear X Heqh h.
  rewrite uncurry_exl_fork_exr.
  unfold doppel.
  rewrite split_fork.
  rewrite curry_comp_l.
  rewrite <- comp_assoc.
  rewrite <- fork_comp.
  rewrite <- !comp_assoc.
  rewrite <- !first_comp.
  rewrite exl_split.
  rewrite exr_split.
  rewrite !eval_first.
  rewrite !uncurry_comp.
  rewrite !uncurry_curry.
  rewrite <- !comp_assoc.
  rewrite !exl_first.
  rewrite <- split_fork.
  rewrite <- (id_right mempty[Y]) at 1.
  rewrite <- (id_left (uncurry id[y ^ x])).
  rewrite <- split_comp.
  rewrite !comp_assoc.
  rewrite HY; clear HY.
  rewrite <- comp_assoc.
  rewrite split_fork.
  rewrite exr_fork.
  rewrite eval_first.
  now rewrite curry_uncurry.
Qed.
Next Obligation.
  spose (@mempty_right _ _ _ Y) as HY.
  remember ((id[y ^ x] ∘ exl) △ (curry _ ∘ exr)) as h.
  assert (h ≈ split id[y ^ x] (curry (mempty[Y] ∘ exl)))
    by (rewrite Heqh; unfork; cat).
  rewrite X; clear X Heqh h.
  rewrite uncurry_exl_fork_exr.
  unfold doppel.
  rewrite split_fork.
  rewrite curry_comp_l.
  rewrite <- comp_assoc.
  rewrite <- fork_comp.
  rewrite <- !comp_assoc.
  rewrite <- !first_comp.
  rewrite exl_split.
  rewrite exr_split.
  rewrite !eval_first.
  rewrite !uncurry_comp.
  rewrite !uncurry_curry.
  rewrite <- !comp_assoc.
  rewrite !exl_first.
  rewrite <- split_fork.
  rewrite <- (id_right mempty[Y]) at 1.
  rewrite <- (id_left (uncurry id[y ^ x])).
  rewrite <- split_comp.
  rewrite !comp_assoc.
  rewrite HY; clear HY.
  rewrite <- comp_assoc.
  rewrite split_fork.
  rewrite exl_fork.
  rewrite eval_first.
  now rewrite curry_uncurry.
Qed.
Next Obligation.
  spose (@mappend_assoc _ _ _ Y) as HY.
  rewrite uncurry_exl_fork_exr.
  remember ((curry _ ∘ exl) △ (id[y ^ x] ∘ exr)) as h.
  assert (h ≈ split (curry (mappend[Y] ∘ split eval eval ∘ doppel)) id[y ^ x])
    by (rewrite Heqh; unfork; cat).
  rewrite X; clear X Heqh h.
  remember ((id[y ^ x] ∘ exl) △ (curry _ ∘ exr)) as h.
  assert (h ≈ split id[y ^ x] (curry (mappend[Y] ∘ split eval eval ∘ doppel)))
    by (rewrite Heqh; unfork; cat).
  rewrite X; clear X Heqh h.
  unfold doppel.
  rewrite <- !comp_assoc.
  rewrite !split_fork.
  rewrite !eval_first.
  simpl.
  rewrite split_fork.
  rewrite !eval_first.
  unfold split.
  rewrite !id_left.
  rewrite !curry_comp_l.
  rewrite <- !comp_assoc.
  rewrite <- !fork_comp.
  rewrite <- !uncurry_comp.
  rewrite exl_fork.
  rewrite exr_fork.
  rewrite !uncurry_curry.
  rewrite <- (id_left (uncurry exr)).
  rewrite <- split_fork.
  rewrite comp_assoc.
  rewrite HY; clear HY.
  rewrite id_left.
  rewrite <- !comp_assoc.
  rewrite <- !fork_comp.
  rewrite <- !comp_assoc.
  rewrite !exl_fork.
  rewrite !exr_fork.
  now rewrite uncurry_curry.
Qed.

End Monoid.
