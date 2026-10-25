Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Monad.Kleisli.
Require Import Category.Comonad.Core.

Generalizable All Variables.

(** * The co-Kleisli category of a comonad / * 余范畴的共Kleisli范畴 *)

(*
nLab:      https://ncatlab.org/nlab/show/co-Kleisli+category
   Wikipedia: https://en.wikipedia.org/wiki/Kleisli_category

   The co-Kleisli category C_W of a comonad (W, extract, duplicate) =
   (W, ε, δ) on C has the same objects as C, while a co-Kleisli morphism
   x ⇸ y is an ordinary C-morphism W x ~> y.  The identity on x is the
   counit extract (ε_x), and the co-Kleisli composite of f : W y ~> z after
   g : W x ~> y is

       f ∘_W g  ≈  f ∘ fmap[W] g ∘ duplicate    (f ∘ W g ∘ δ),

   which is exactly f composed onto the extension of g (f ∘ extend g).

   Since [Comonad C W] is by definition [@Monad (C^op) (W^op)], the
   co-Kleisli category is obtained here as the opposite of the Kleisli
   category of that opposite monad, rather than by re-proving the category
   laws:

       CoKleisli := (Kleisli (C^op) (W^op))^op

   Because duality is built into this library so that C^op^op = C holds by
   reflexivity, the covariant components of this construction are
   definitionally the expected ones: the hom-sets are literally
   W x ~{C}~> y ([cokleisli_hom], which holds by reflexivity), the identity
   is literally [extract] ([cokleisli_id]), and the categorical composite
   [cokleisli_compose f g] (f after g) is literally f ∘ extend g.  The
   fish operators name this the other way round: [f =>= g] runs the LEFT
   operand first (Monad/Kleisli.v convention), so [f =>= g ≈ g ∘ extend f]
   ([cokleisli_compose_extend]).  The category laws, inherited from
   Monad/Kleisli.v by duality and re-read covariantly, are the co-Kleisli
   triple laws [extract_extend], [extend_extract] and [extend_comp] of
   Comonad/Core.v; they appear below as [comonad_id_left],
   [comonad_id_right] and [comonad_comp_assoc].

--------
nLab:      https://ncatlab.org/nlab/show/co-Kleisli+category
   Wikipedia: https://en.wikipedia.org/wiki/Kleisli_category

   范畴 C 上余单子 (W, extract, duplicate) = (W, ε, δ) 的 co-Kleisli 范畴 C_W 与 C
   有相同对象，而 co-Kleisli 态射 x ⇸ y 是普通 C-态射 W x ~> y。x 上的恒等是余单位
   extract（ε_x），f : W y ~> z 在 g : W x ~> y 之后的 co-Kleisli 复合是

       f ∘_W g  ≈  f ∘ fmap[W] g ∘ duplicate    (f ∘ W g ∘ δ),

   恰是 f 复合到 g 的扩展上（f ∘ extend g）。

   因 [Comonad C W] 按定义是 [@Monad (C^op) (W^op)]，co-Kleisli 范畴此处取为该对偶单子的
   Kleisli 范畴的对偶，而非重证范畴定律：

       CoKleisli := (Kleisli (C^op) (W^op))^op

   因对偶使 C^op^op = C 由 reflexivity 成立，此构造的共变分量定义上即所期望：hom 集字面上是
   W x ~{C}~> y（[cokleisli_hom]），恒等字面上是 [extract]，范畴复合 [cokleisli_compose f g]
   字面上是 f ∘ extend g。范畴定律由 Monad/Kleisli.v 经对偶继承，共变重读为 Comonad/Core.v
   的 co-Kleisli 三定律。
*)

(*
Context-dependent maps, dataflow, and linear logic

   nLab:  https://ncatlab.org/nlab/show/exponential+modality
   Paper: Uustalu, Vene, "The Essence of Dataflow Programming", APLAS
          2005, LNCS 3780, pp. 2-18
   Paper: Petricek, Orchard, Mycroft, "Coeffects: a calculus of
          context-dependent computation", ICFP 2014

   The co-Kleisli category is where the computational reading of a
   comonad becomes a category of programs.  A co-Kleisli morphism
   W x ~> y consumes not a bare x but an x in its W-context, and the
   composite of two such morphisms first promotes the earlier one to a
   context-preserving transformation ([extend]) so that the later one
   may read its result in context; arrows that observe their
   surroundings thereby compose as ordinary functions do.  The analogy
   with Kleisli categories runs in parallel throughout: as those model
   call-by-value languages, co-Kleisli categories model call-by-name,
   and for an idempotent comonad the construction collapses to the
   coreflective subcategory of the comonad's modal types.  Haskell's
   comonad package (Kmett) states the comonad laws in this vocabulary,
   with extract the identity of co-Kleisli composition, just as
   [comonad_id_left], [comonad_id_right] and [comonad_comp_assoc] do
   below.

   Dataflow programming supplies the motivating example.  Uustalu and
   Vene observed that both general and causal stream functions can be
   characterized as the co-Kleisli arrows of suitable stream comonads —
   causality meaning that the output at a given moment depends only on
   the input's past and present, which is to say on the input value in
   its history-context — and on that observation built a generic
   comonadic interpreter, recovering effects where needed through a
   distributive law of the comonad over a monad (APLAS 2005).  A
   co-Kleisli arrow of the stream comonad is a digital filter, and
   [extend] produces the filtered stream (Milewski, 2017).  The coeffect
   calculi of Petricek, Orchard and Mycroft (ICFP 2014) supply type
   systems for this class of programs; dataflow, implicit parameters,
   liveness and bounded usage are among their instances.

   Linear logic supplies the proof-theoretic example.  In models of
   linear logic the exponential modality ! is a comonad (Girard 1987,
   the comonadic reading developed by Seely 1989, de Paiva 1989, and
   Benton–Bierman–de Paiva–Hyland 1992): !A is A made freely duplicable
   and discardable.  When the linear category is closed symmetric
   monoidal, the co-Kleisli category of ! is cartesian closed — a
   categorical form of the translation of intuitionistic logic into
   linear logic (Seely) — and Benton (1995) showed that the !-comonad
   is induced by a monoidal adjunction between a cartesian monoidal and
   a symmetric monoidal category, the linear–non-linear adjunction.
   The category built below is the common shape behind both readings.

--------
上下文依赖的映射、数据流和线性逻辑

nLab：https://ncatlab.org/nlab/show/exponential+modality
   论文：Uustalu, Vene，《数据流编程的本质》，APLAS 2005，LNCS 3780，第2-18页
   论文：Petricek, Orchard, Mycroft，《共效应：上下文依赖计算的演算》，ICFP 2014

共-Kleisli 范畴是一个共单子的计算解读成为程序范畴的地方。一个共-Kleisli 态射 W x ~> y 不消耗裸 x，而是消耗处于 W 上下文中的 x，而两个这样的态射的复合首先将较早的态射提升为上下文保持的变换（[extend]），以便后一个态射可以在上下文中读取其结果；观察其周围环境的箭头因此像普通函数一样组合。与 Kleisli 范畴的类比在整个过程中是平行的：正如那些模型表示按值调用语言，共-Kleisli 范畴模型按名调用，并且对于幂等共单子，该构造会坍缩为共单子模态类型的核心反射子范畴。Haskell 的共单子包（Kmett）使用这种词汇陈述共单子定律，其中 extract 是共-Kleisli 组合的恒等，就像下面的 [comonad_id_left]、[comonad_id_right] 和 [comonad_comp_assoc] 一样。

数据流编程提供了一个激励性的例子。Uustalu 和 Vene 观察到，一般的和因果流函数都可以被描述为适当流余范畴的共 Kleisli 箭头——因果性意味着某一时刻的输出仅依赖于输入的过去和现在，也就是说依赖于输入在其历史上下文中的值——并且基于这一观察构建了一个通用的余范畴解释器，通过余范畴在幺半范畴上的分配律在需要时恢复效果（APLAS 2005）。流余范畴的共 Kleisli 箭头是一个数字滤波器，而 [extend] 生成被滤波的流（Milewski，2017）。Petricek、Orchard 和 Mycroft（ICFP 2014）的共效应演算为这一类程序提供了类型系统；数据流、隐式参数、活性和有界使用都是它们的实例。

线性逻辑提供了证明理论的例子。在线性逻辑的模型中，指数模态 ! 是一个余单子（Girard 1987，Seely 1989、de Paiva 1989 和 Benton–Bierman–de Paiva–Hyland 1992 发展了余单子解读）：!A 是可以自由复制和丢弃的 A。当线性范畴是封闭对称幺半群时，! 的 co-Kleisli 范畴是笛卡尔闭的——这是直觉主义逻辑翻译成线性逻辑的一种范畴形式（Seely）——Benton（1995）表明，!-余单子由笛卡尔幺半群范畴和对称幺半群范畴之间的幺半群伴随引入，称为线性-非线性伴随。下面构建的范畴是两种解读背后的共通结构。
*)

Section CoKleisli.

Context {C : Category} {W : C ⟶ C} {H : @Comonad C W}.

Definition CoKleisli : Category := (@Kleisli (C^op) (W^op) H)^op.

(**
The hom-sets of the co-Kleisli category are definitionally the
    covariant hom-sets [W x ~> y] of the base category.

--------
协 Kleisli 范畴的同态集在定义上是基范畴的协变同态集 [W x ~> y]。
*)
Lemma cokleisli_hom (x y : C) : (x ~{CoKleisli}~> y) = (W x ~{C}~> y).
Proof. reflexivity. Qed.

(** The identity at x is the counit ε_x. / 在 x 处的恒等映射是余单位 ε_x。 *)
Lemma cokleisli_id {x : C} : @id CoKleisli x ≈ @extract C W H x.
Proof. reflexivity. Qed.

Definition cokleisli_compose `(f : W b ~{C}~> c) `(g : W a ~{C}~> b) :
  W a ~{C}~> c := @compose CoKleisli a b c f g.

(*
Co-Kleisli composition operators, following the library's fish-operator
   convention (Monad/Kleisli.v [>=>]/[<=<]): in the right-pointing [=>=] the
   LEFT operand runs first, so [f =>= g] extends [f] and then applies [g]
   ([g ∘ extend f]).  Its transpose [f =<= g] runs the right operand first
   ([f ∘ extend g]) — the co-Kleisli dual of [<=<].  This matches the
   direction of [>=>] on the monad side rather than Haskell's Control.Comonad
   [=>=], whose right-pointing operator runs the right operand first.

--------
共Kleisli组合运算符，遵循库的鱼形运算符约定（Monad/Kleisli.v [>=>]/[<=<]）：在右指的 [=>=] 中，左操作数先运行，因此 [f =>= g] 扩展 [f] 然后应用 [g]（[g ∘ extend f]）。它的转置 [f =<= g] 先运行右操作数（[f ∘ extend g]）——这是 [<=<] 的共Kleisli对偶。这与单子一侧的 [>=>] 方向相匹配，而不是 Haskell 的 Control.Comonad [=>=]，其右指运算符先运行右操作数。
*)
Notation "f =>= g" :=
  (cokleisli_compose g f) (at level 40, left associativity) : morphism_scope.
Notation "f =<= g" :=
  (cokleisli_compose f g) (at level 40, left associativity) : morphism_scope.

(**
Co-Kleisli composition agrees with the extension operator [extend] of
    Comonad/Core.v; by the built-in duality the agreement is definitional.
    [f] on the left runs first, so [f =>= g ≈ g ∘ extend f].

--------
Co-Kleisli 组合与 Comonad/Core.v 中的扩展算子 [extend] 一致；根据内置的对偶性，这种一致性是定义上的。左边的 [f] 先运行，所以 [f =>= g ≈ g ∘ extend f]。
*)
Lemma cokleisli_compose_extend `(f : W a ~{C}~> b) `(g : W b ~{C}~> c) :
  f =>= g ≈ g ∘ extend f.
Proof. reflexivity. Qed.

Corollary cokleisli_compose_extend_flip
  `(f : W b ~{C}~> c) `(g : W a ~{C}~> b) :
  f =<= g ≈ f ∘ extend g.
Proof. reflexivity. Qed.

(*
The comonad laws, re-expressed in terms of this category: dually to the
   monoid reading in Monad/Kleisli.v, they exhibit [extract] as the unit of
   co-Kleisli composition, with associativity mediated by [extend].  Each is
   the corresponding category law of [CoKleisli], read across the definitional
   agreements above.

--------
用这个范畴重新表达的余单子定律：与 Monad/Kleisli.v 中单子的理解相对，它们展示了 [extract] 作为余 Kleisli 复合的单位，并且结合性由 [extend] 介导。每一个都是 [CoKleisli] 的对应范畴定律，通过上述定义协议进行理解。
*)

Corollary comonad_id_left `(f : W x ~{C}~> y) : extract =>= f ≈ f.
Proof. unfold cokleisli_compose; cat. Qed.

Corollary comonad_id_right `(f : W x ~{C}~> y) : f =>= extract ≈ f.
Proof. unfold cokleisli_compose; cat. Qed.

Corollary comonad_comp_assoc `(f : W x ~{C}~> y) `(g : W y ~{C}~> z)
  `(h : W z ~{C}~> w) : f =>= (g =>= h) ≈ (f =>= g) =>= h.
Proof. exact (@comp_assoc_sym CoKleisli x y z w h g f). Qed.

End CoKleisli.

Notation "f =>= g" :=
  (cokleisli_compose g f)
  (at level 40, left associativity) : morphism_scope.
Notation "f =<= g" :=
  (cokleisli_compose f g)
  (at level 40, left associativity) : morphism_scope.

(*
Explicit-endofunctor forms, the robust fallback when higher-order
   unification cannot infer [W] through the bare [=>=]/[=<=] holes
   (Monad/Kleisli.v exports the analogous [>=[ M ]=>]/[<=[ M ]=<]).

--------
显式endofunctor形式，当高阶统一无法通过裸[=>=]/[=<=]孔推断出[W]时，这是稳健的回退方案（Monad/Kleisli.v导出了类似的[>=[ M ]=>]/[<=[ M ]=<]）。
*)
Notation "f =>[ W ]=> g" := (@cokleisli_compose _ W _ _ _ g _ f)
  (at level 40, left associativity) : morphism_scope.
Notation "f =<[ W ]=< g" := (@cokleisli_compose _ W _ _ _ f _ g)
  (at level 40, left associativity) : morphism_scope.
