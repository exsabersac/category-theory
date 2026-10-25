Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Functor.Strong.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.BiCCC.
Require Import Category.Structure.Constant.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Closed.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** The category COQ of types and functions. / 类型和函数的 COQ 类别。 *)

(*
 nLab: https://ncatlab.org/nlab/show/Set
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_sets

 This is the strict-function model of the "category of sets" built from
 Coq's universe Type: objects are types `A : Type`, morphisms `A ~> B` are
 functions `A → B`, identity is `λ x, x` and composition is `λ x, g (f x)`.
 Morphism equivalence is pointwise (extensional) equality of functions,
 `f ≈ g  :=  ∀ x, f x = g x`; unlike Instance/Sets.v (the setoid model),
 the underlying `=` here is Coq's Leibniz equality on the codomain.

 The category laws and the cartesian/cocartesian/terminal/initial structure
 below hold with no axioms (pointwise `=` needs none). The closed structure
 (exponentials) does invoke functional_extensionality, which is the expected,
 pre-existing funext axiom of this layer and lies outside the core
 zero-axiom guarantee. 

 --------
 nLab:  https://ncatlab.org/nlab/show/Set 
 维基百科:  https://en.wikipedia.org/wiki/Category_of_sets 

 这是从 Coq 的 universe Type 构建的“集合范畴”的严格函数模型：对象是类型 `A : Type`，态射 `A ~> B` 是函数 `A → B`，恒等映射是 `λ x, x`，复合是 `λ x, g (f x)`。态射等价是函数的逐点（外延）相等，`f ≈ g  :=  ∀ x, f x = g x`；与 Instance/Sets.v（集合模型）不同，这里的底层 `=` 是 Coq 在值域上的 Leibniz 相等。

 以下范畴律以及笛卡尔/余笛卡尔/终/初结构在没有公理的情况下成立（逐点 `=` 不需要任何公理）。闭结构（指数对象）确实调用了 function_extensionality，这是该层预期存在的 funext 公理，并且位于零公理保证的核心之外。
*)

(*
 Types and functions as the category of sets: history and applications

 nLab:  https://ncatlab.org/nlab/show/ETCS
 nLab (type theory and category theory):
 https://ncatlab.org/nlab/show/relation+between+type+theory+and+category+theory
 Blog:  https://math.andrej.com/2016/08/06/hask-is-not-a-category/

 Reading types and functions as a category enacts the structural stance
 that Lawvere took when he axiomatized the category of sets directly —
 objects and composites first, membership a derived notion (Lawvere, "An
 elementary theory of the category of sets", PNAS 52, 1964, the origin
 of ETCS).  On that view a set is whatever composes, and [Coq] is the
 stance implemented over the universe Type, machine-checked rather than
 postulated.

 The instance is one half of Curry–Howard–Lambek.  Lambek's "Deductive
 systems and categories" series (II, LNM 86, 1969; III, LNM 274, 1972)
 recast deductive systems as categories, Part III pairing cartesian
 closed categories with intuitionist propositional calculus and
 combinatory logic; the polished equivalence between typed λ-calculi
 and cartesian closed categories is Part I of Lambek and Scott,
 "Introduction to Higher Order Categorical Logic", CUP 1986.  In-tree
 the correspondence runs in both directions: Instance/Lambda.v builds
 the simply typed λ-calculus as a syntactic cartesian closed category,
 and Instance/Lambda/Sem.v interprets that syntax into this category —
 the standard model meeting its own internal language.  What is
 folklore in Haskell is a theorem here: Bauer observed that no rigorous
 morphism equality was ever fixed for the supposed category of Haskell
 types and functions, and that under the natural candidates the
 identity law does not survive seq (Bauer, "Hask is not a category",
 2016).  Coq functions are total, and the header above fixes the
 morphism equivalence exactly.

 The division of labour with Instance/Sets.v follows a known fault line
 in intensional type theory.  Hofmann showed that the intensional
 identity type does not identify pointwise-equal functions and yields
 no quotient types, and that setoid models restore both (Hofmann,
 "Extensional concepts in intensional type theory", Edinburgh thesis,
 1995); the Rocq standard library accordingly states
 functional_extensionality_dep as an Axiom rather than a theorem.  The
 two instances occupy the two sides of that line: Instance/Sets.v pays
 with respectfulness bookkeeping on every morphism yet obtains
 exponentials without axioms (Instance/Sets/Cartesian/Closed.v), while
 here the category laws and the structure of [Coq_Terminal],
 [Coq_Initial], [Coq_Cartesian] and [Coq_Cocartesian] hold by Leibniz
 rewriting alone, and exactly one axiom is spent, in [Coq_Closed],
 where currying must respect the pointwise equivalence before
 [exp_iso] can be an isomorphism of hom-setoids.  The setoid side has
 its own boundary: the canonical truth-value object for Instance/Sets.v
 cannot fit at a single universe level — its carrier is the universe
 itself, which the predicative Type hierarchy places one level up, the
 universe-constraint graph staying acyclic (Rocq reference manual,
 sorts) — so Instance/Sets/Classifier.v develops the classifier
 theorems cross-universe instead.

 The payoff here is computational: composition is literally
 λ x, g (f x), so a categorical equation over [Coq] is a runnable
 program equivalence, and developments that stay out of the
 exponentials stay axiom-free.  Instance/Coq/Lists.v proves list A the
 initial algebra of its base functor with pointwise equality and list
 induction alone; Theory/Coq/Monad/Proofs.v defines lawfulness of the
 Haskell-style Monad class as arising from a monad on this category.
 The boundary is itself machine-checked: Instance/Coq/Comonad/Store.v
 shows that the respectfulness field a store functor hosted here would
 require already entails functional extensionality, and hosts Store
 over Instance/Sets.v instead — a live marker of where the Leibniz
 model stops and the setoid model takes over.

 The applications run through the cartesian closed structure.  Because
 the simply typed λ-calculus is modeled by any cartesian closed
 category, a typed program written against this category can be
 reinterpreted in others — the method of Elliott, "Compiling to
 categories" (PACMPL 1, ICFP 2017), practised in-tree by
 Tools/Abstraction.v.  The programmer-facing picture of types as
 objects and functions as morphisms (Milewski, "Category: The Essence
 of Composition", 2014) is this file made rigorous, and
 [Coq_StrongFunctor] packages, once and for every endofunctor, the
 canonical strength that Set-based accounts of effects leave implicit
 (Kock, "Strong functors and monoidal monads", Arch. Math. 23, 1972). 

 --------
 类型和函数作为集合类别：历史与应用

 nLab:   https://ncatlab.org/nlab/show/ETCS 
 nLab（类型理论与范畴论）：
 https://ncatlab.org/nlab/show/relation+between+type+theory+and+category+theory 
 博客：   https://math.andrej.com/2016/08/06/hask-is-not-a-category/ 

 将类型和函数视为一个类别的阅读实践体现了劳维尔在他直接公理化集合类别时所采用的结构立场——首先考虑对象和复合，成员关系是一个派生概念（Lawvere，《集合类别的一种初等理论》，PNAS 52, 1964，ETCS 的起源）。在这种观点下，一个集合就是任何可以组合的东西，而 [Coq] 是在 Type 宇宙中实现的立场，是经过机器验证的，而非假定的。这个实例是 Curry–Howard–Lambek 三者关系的一半。Lambek 的“演绎系统与范畴”系列（II, LNM 86, 1969；III, LNM 274, 1972）将演绎系统重新表述为范畴，第三部分将笛卡尔闭范畴与直觉主义命题演算和组合逻辑配对；类型化 λ 演算与笛卡尔闭范畴之间的精炼等价出现在 Lambek 和 Scott 的《高阶范畴逻辑导论》（CUP 1986）的第一部分。在树状结构中，这种对应关系是双向的：Instance/Lambda.v 构建了一个作为语法笛卡尔闭范畴的简单类型 λ 演算，而 Instance/Lambda/Sem.v 将该语法解释到这个范畴中——标准模型满足其自身的内部语言。在 Haskell 中所谓的民间传说在这里是一个定理：Bauer 观察到，对于所谓的 Haskell 类型和函数的范畴，从未有严格的态射等价被确定，并且在自然候选下，恒等律在 seq 下无法保持（Bauer，《Hask 不是一个范畴》，2016）。Coq 函数是全函数，上述标题正好确定了态射等价。在《Instance/Sets.v》中，劳动分工遵循了内涵类型理论中已知的断层线。Hofmann 表明，内涵的同一类型不能识别按点相等的函数，也不会产生商类型，并且 setoid 模型可以恢复二者（Hofmann，《内涵类型理论中的外延概念》，爱丁堡论文，1995）；因此，Rocq 标准库将 functional_extensionality_dep 作为公理而不是定理声明。这两个实例分别占据了那条线的两侧：Instance/Sets.v 在每个态射上以尊重的方式做簿记，但获得指数对象时不依赖公理（Instance/Sets/Cartesian/Closed.v）；而在这里，类别定律以及  [Coq_Terminal]、[Coq_Initial]、[Coq_Cartesian] 和 [Coq_Cocartesian] 的结构仅通过莱布尼茨重写就成立，并且正好只使用了一个公理，在 [Coq_Closed] 中，柯里化必须在 [exp_iso] 成为同类集同构之前尊重点对点等价。集合论一侧有其自身的边界：用于 Instance/Sets.v 的规范真值对象无法适应单一的宇宙层级——它的承载对象本身就是宇宙，而谓词型 Type 层级将其放在更高的一个层级上，宇宙约束图保持无环（Rocq 参考手册，排序）——因此 Instance/Sets/Classifier.v 处理跨宇宙的分类器定理。这里的收益是计算上的：组合字面上是 λ x, g (f x)，所以 [Coq] 上的一个范畴方程就是一个可运行的程序等价，而保持在指数外的发展保持无公理。Instance/Coq/Lists.v 证明了 list A 是其基础函子在逐点相等下的初始代数，仅用列表归纳；Theory/Coq/Monad/Proofs.v 定义了 Haskell 风格 Monad 类的合法性是由该范畴上的单子引起的。边界本身是机器检查的：Instance/Coq/Comonad/Store.v 显示，这里一个 store 函子所需要的尊重性字段已经隐含了函数外延性，并转而在 Instance/Sets.v 上承载 Store —— 这是 Leibniz 模型停止、集合等价模型接管的一个实时标志。应用程序通过笛卡尔闭结构运行。由于简单类型 λ 演算可以由任何笛卡尔闭范畴建模，因此针对该范畴编写的类型化程序可以在其他范畴中重新解释——Elliott 的方法，“编译到范畴”（PACMPL 1, ICFP 2017），在 Tools/Abstraction.v 中以树内的方式实践。面向程序员的类型作为对象、函数作为箭头（Milewski, “Category: The Essence of Composition”, 2014）的图景在此文件中得到了严格化，而 [Coq_StrongFunctor] 包，一次性为每个自函子提供了基于集合的效果处理账户所隐含的规范强度 (Kock, “Strong functors and monoidal monads”, Arch. Math. 23, 1972) 。
*)

#[export]
Program Instance Coq : Category := {
  obj     := Type;                                   (* objects are types / 对象是类型 *)
  hom     := λ A B : Type, A → B;                    (* morphisms are functions / 态射是函数 *)
  homset  := λ _ _, {| equiv := λ f g, ∀ x, f x = g x |};  (* pointwise equality / 逐点相等 *)
  id      := λ _ x, x;                               (* identity function / 恒等函数 *)
  compose := λ _ _ _ g f x, g (f x)                  (* function composition / 函数组合 *)
}.
Next Obligation. equivalence; congruence. Qed.
Next Obligation. proper; congruence. Qed.

(* Terminal object: the singleton `unit`, with the unique map `λ _, tt`. / 终对象：单例 `unit`，带有唯一映射 `λ _, tt`。 *)
#[export]
Program Instance Coq_Terminal : @Terminal Coq := {
  terminal_obj := unit : Type;       (* the terminal object 1 := unit / 终端对象 1 := 单位 *)
  one := λ _ a, tt                    (* the unique map x ~> unit / 唯一映射 x ~> 单位 *)
}.
Next Obligation. destruct (f x0), (g x0); reflexivity. Qed.

(* Products: the cartesian product of types `x * y`, with projections fst/snd and pairing ⟨f, g⟩ := λ x, (f x, g x). / 产品：类型 `x * y` 的笛卡尔积，带有投影 fst/snd 和配对 ⟨f, g⟩ := λ x, (f x, g x)。 *)
#[export]
Program Instance Coq_Cartesian : @Cartesian Coq := {
  product_obj := λ x y, x * y : Type;          (* product object x × y / 产品对象 x × y *)
  fork := λ _ _ _ f g x, (f x, g x);           (* pairing ⟨f, g⟩ / 配对 ⟨f, g⟩ *)
  exl  := λ _ _ p, fst p;                       (* first projection / 第一次投影 *)
  exr  := λ _ _ p, snd p                        (* second projection / 第二投影 *)
}.
Next Obligation. proper; congruence. Qed.
Next Obligation.
  intros; simplify; intros.
  - rewrite H; reflexivity.
  - rewrite H; reflexivity.
  - intros; simplify.
    rewrite <- H, <- H0.
    rewrite <- surjective_pairing; reflexivity.
Qed.

(* The cartesian monoidal structure: tensor := × with unit I := 1 (unit). / 笛卡尔幺半群结构：张量 := ×，单位元 I := 1（单位）。 *)
#[export]
Program Instance Coq_Monoidal : @Monoidal Coq :=
  @CC_Monoidal Coq Coq_Cartesian Coq_Terminal.

(*
 Exponentials: the function type `y^x := x → y` (Basics.arrow), making COQ
 cartesian closed. The defining isomorphism is curry/uncurry, exhibiting the
 adjunction `(- × x) ⊣ (x → -)` (hom(z × x, y) ≅ hom(z, x → y)). Establishing
 that to/from are mutually inverse invokes functional_extensionality. 

 --------
 指数函数：函数类型 `y^x := x → y`（Basics.arrow），使 COQ 成为笛卡尔闭合。定义的同构是 curry/uncurry，展示了伴随关系 `(- × x) ⊣ (x → -)`（hom(z × x, y) ≅ hom(z, x → y)）。证明 to/from 互为逆元需要使用函数外延性。
*)
#[export]
Program Instance Coq_Closed : @Closed Coq _ := {
  exponent_obj := Basics.arrow;                         (* exponential y^x := x → y / 指数 y^x := x → y *)
  exp_iso := λ _ _ _,
    {| to   := {| morphism := λ f a b, f (a, b) |}      (* curry *)
     ; from := {| morphism := λ f p, f (fst p) (snd p) |} |}  (* uncurry *)
}.
Next Obligation. proper; extensionality X0; congruence. Qed.
Next Obligation. proper; congruence. Qed.

(* The cartesian-closed structure read as a closed monoidal structure: the internal hom of the cartesian monoidal product is the exponential above. / 笛卡尔闭合结构读作闭单体结构：笛卡尔单体积的内部同态是上面的指数。 *)
#[export]
Program Instance Coq_ClosedMonoidal : @ClosedMonoidal Coq :=
  @CCC_ClosedMonoidal Coq Coq_Cartesian Coq_Terminal Coq_Closed.

(*
 Initial object: the empty type `False`, with the unique map out of it given
 by False_rect (the empty function). Because `Initial Coq` unfolds to
 `Terminal (Coq^op)` (initiality is terminality in the opposite category),
 the fields are spelled with the Terminal names `terminal_obj` and `one`. 

 --------
 初始对象：空类型 `False`，唯一的映射由 False_rect（空函数）给出。因为 `Initial Coq` 展开为 `Terminal (Coq^op)`（初始性在对偶范畴中是终端性），所以这些字段使用终端名称 `terminal_obj` 和 `one` 来表示。
*)
#[export]
Program Instance Coq_Initial : Initial Coq := {
  terminal_obj := False;             (* the initial object 0 := False / 初始对象 0 := False *)
  one := λ _ _, False_rect _ _       (* the unique map False ~> x / 唯一映射 False ~> x *)
}.
Next Obligation. contradiction. Qed.

(*
 Coproducts: the disjoint union (sum type) `x + y`, with injections inl/inr
 and copairing [f, g] by case analysis. Being cocartesian is being cartesian
 in Coq^op, so the fields reuse the Cartesian names: `product_obj` is the
 coproduct object, `fork` is the copairing, and `exl`/`exr` are the
 injections (the projections read in the opposite category). 

 --------
 余积：不相交的并（和类型） `x + y`，带有注入 inl/inr 和通过案例分析的共配对 [f, g]。成为余笛卡尔意味着在 Coq^op 中是笛卡尔的，因此这些字段重用了笛卡尔的名称：`product_obj` 是余积对象，`fork` 是共配对，`exl` / `exr` 是注入（在对偶范畴中读取的投影）。
*)
#[export]
Program Instance Coq_Cocartesian : @Cocartesian Coq := {
  product_obj := sum;                          (* coproduct object x + y / 余积对象 x + y *)
  fork := λ _ _ _ f g x,                        (* copairing [f, g] / 配对 [f, g] *)
            match x with
            | Datatypes.inl v => f v
            | Datatypes.inr v => g v
            end;
  exl  := λ _ _ p, Datatypes.inl p;            (* left injection inl / 左侧注射口 *)
  exr  := λ _ _ p, Datatypes.inr p             (* right injection inr / 右侧注射 INR *)
}.
Next Obligation.
  split; intros.
  - split; intros;
    rewrite H; reflexivity.
  - destruct x0; firstorder.
Qed.

(*
 nLab: https://ncatlab.org/nlab/show/tensorial+strength

 Every endofunctor on COQ carries a (unique) tensorial strength. This is the
 familiar fact that every Set-endofunctor is canonically strong, since over a
 cartesian closed category strength is equivalent to enrichment and every
 ordinary functor is automatically Set-enriched (Kock). The strength
 `x × F y ~> F (x × y)` is built by mapping the partial pairing `λ y, (x, y)`
 through F. 

 --------
 nLab：https://ncatlab.org/nlab/show/tensorial+strength

 COQ 上的每一个端函子都携带一个（唯一的）张量强度。这是一个熟悉的事实：每一个 Set 端函子都是典型的强函子，因为在笛卡尔闭范畴上，强度等价于加强，而每一个普通函子自动是 Set 加强的（Kock）。强度 `x × F y ~> F (x × y)` 是通过将部分配对 `λ y, (x, y)` 映射通过 F 构建的。
*)

#[export]
Program Instance Coq_StrongFunctor (F : Coq ⟶ Coq) : StrongFunctor F := {|
  strength := λ _ _ p, fmap[F] (λ y, (fst p, y)) (snd p)  (* x × F y ~> F (x × y) *)
|}.
Next Obligation.
  repeat srewrite_r (@fmap_comp _ _ F).
  f_equal.
Qed.
Next Obligation.
  repeat srewrite_r (@fmap_comp _ _ F).
  now srewrite (@fmap_id _ _ F).
Qed.
Next Obligation.
  repeat srewrite_r (@fmap_comp _ _ F).
  f_equal.
Qed.
