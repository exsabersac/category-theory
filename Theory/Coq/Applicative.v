Require Import Category.Lib.
Require Export Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Semigroup.
Require Import Category.Theory.Coq.Monoid.

Generalizable All Variables.

(** The Applicative type class (pure/ap), with its categorical reading / Applicative 类型类（pure/ap）及其范畴论解读 *)

(*
nLab: https://ncatlab.org/nlab/show/applicative+functor
   Wikipedia: https://en.wikipedia.org/wiki/Applicative_functor

   FP reading.  An applicative functor (in the Haskell sense) is a type
   constructor [F : Type → Type] equipped with [pure : x → F x], injecting a
   plain value, and [ap : F (x → y) → F x → F y] (Haskell's [<*>]), applying a
   wrapped function to a wrapped argument.  It is lawful when it satisfies the
   four applicative laws:
     identity      [pure id <*> v ≈ v];
     composition   [pure (∘) <*> u <*> v <*> w ≈ u <*> (v <*> w)];
     homomorphism  [pure f <*> pure x ≈ pure (f x)];
     interchange   [u <*> pure y ≈ pure (λ g, g y) <*> u].
   Every applicative is a functor, with [fmap f x = pure f <*> x] (see
   [Functor_Applicative] below).

   Categorical reading.  This is exactly a lax monoidal endofunctor (with
   tensorial strength) on the category of Coq types, taken with its cartesian
   monoidal structure (product [×], unit [unit]).  The two structure morphisms
   of a lax monoidal functor [F] are the unit [η : 1 → F 1] and the laxator
   (a natural transformation) [μ : F x ⊗ F y → F (x ⊗ y)].  Here [η] is
   recovered from [pure] (as [pure tt]) and [μ] from [ap] (as
   [λ '(u, v), liftA2 pair u v]); conversely [pure x = fmap (const x) (η tt)]
   and [ap f x = fmap (λ '(g, a), g a) (μ (f, x))].  The four applicative laws
   above are precisely the lax-monoidal coherence axioms (associativity of [μ]
   and the two unit constraints involving [η]).

   As is usual for these Coq/Haskell-style classes, the laws are NOT recorded
   as fields here; [Applicative] carries only [pure] and [ap], and lawfulness
   is an obligation discharged for each concrete instance.

--------
nLab：https://ncatlab.org/nlab/show/applicative+functor
维基百科：https://en.wikipedia.org/wiki/Applicative_functor

FP 阅读。一个应用函子（在 Haskell 的意义上）是一个类型构造器 [F : Type → Type]，配备了 [pure : x → F x]，用于注入一个普通值，以及 [ap : F (x → y) → F x → F y]（Haskell 的 [<*>]），用于将封装的函数应用于封装的参数。当它满足四条应用律时，它是合法的：
  恒等律      [pure id <*> v ≈ v]；
  组合律      [pure (∘) <*> u <*> v <*> w ≈ u <*> (v <*> w)]；
  同态律      [pure f <*> pure x ≈ pure (f x)]；
  交换律      [u <*> pure y ≈ pure (λ g, g y) <*> u]。
每个应用函子都是一个函子，带有 [fmap f x = pure f <*> x]（见下面的 [Functor_Applicative]）。

范畴论的解读。这正是 Coq 类型范畴上的一个松单数函子（带张量强度），其采用笛卡尔单数结构（积 [×]，单位 [unit]）。松单数函子的两个结构态射 [F] 分别是单位 [η : 1 → F 1] 和松算子（一个自然变换）[μ : F x ⊗ F y → F (x ⊗ y)]。在这里，[η] 从 [pure]（作为 [pure tt]）恢复，[μ] 从 [ap]（作为 [λ '(u, v), liftA2 pair u v]）恢复；反之亦然 [pure x = fmap (const x) (η tt)] 和 [ap f x = fmap (λ '(g, a), g a) (μ (f, x))]。上述四条应用规律正是松单数相干公理（[μ] 的结合律以及涉及 [η] 的两个单位约束）。

像这些 Coq/Haskell 风格的类通常一样，这里的定律并没有作为字段记录；[Applicative] 仅包含 [pure] 和 [ap]，而合法性是针对每个具体实例履行的义务。
*)

Class Applicative@{d c} {F : Type@{d} → Type@{c}} := {
  pure {x : Type@{d}} : x → F x;                       (* unit: injects a value (lax-monoidal η) / 单位：注入一个值（松单调 η） *)
  ap {x y : Type @{d}} : F (x → y) → F x → F y;         (* application derived from the laxator μ / 由松弛剂μ衍生的应用 *)
}.

Arguments Applicative : clear implicits.

(*
[liftA2] maps a binary function over two applicative arguments,
   [liftA2 f a b = pure f <*> a <*> b].  Categorically it is the curried form
   of the laxator [μ : F x ⊗ F y → F (x ⊗ y)] postcomposed with [fmap]: it is
   interdefinable with [ap], and [μ = liftA2 pair].

--------
[liftA2] 将一个二元函数映射到两个适用性参数 [liftA2 f a b = pure f <*> a <*> b] 上。 在范畴上，它是松弛算子 [μ : F x ⊗ F y → F (x ⊗ y)] 的柯里化形式，后接 [fmap]：它与 [ap] 和 [μ = liftA2 pair] 互相可定义。
*)
Definition liftA2 `{Applicative F} {x y z}
  (f : x → y → z) (a : F x) (b : F y) : F z :=
  ap (ap (pure f) a) b.

(*
nLab: https://ncatlab.org/nlab/show/distributive+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Monoid_(category_theory)

   The Alternative type class adds a monoid structure on each [F x] that is
   compatible with the applicative structure: [empty] is the neutral element
   and [choose] (Haskell's [<|>]) the binary operation.  As with the other
   classes here the monoid laws are NOT recorded as fields.

--------
nLab：https://ncatlab.org/nlab/show/distributive+monoidal+category
Wikipedia：https://en.wikipedia.org/wiki/Monoid_(category_theory)

Alternative 类型类为每个 [F x] 添加了一个幺半群结构，该结构与应用式结构兼容：[empty] 是单位元，[choose]（Haskell 的 [<|>]）是二元运算。与此处的其他类一样，幺半群定律并未作为字段记录。
*)
Class Alternative@{d c} {F : Type@{d} → Type@{c}} := {
  empty  {x : Type@{d}} : F x;                         (* neutral element of the [choose] monoid / [choose] 单元的中性元素 *)
  choose {x : Type@{d}} : F x → F x → F x;              (* binary [<|>] operation / 二元 [<|>] 运算 *)
}.

Arguments Alternative : clear implicits.

Module ApplicativeNotations.

Export FunctorNotations.

Notation "pure[ M ]" := (@pure M _ _)
  (at level 0, format "pure[ M ]").
Notation "pure[ M N ]" := (@pure (fun X => M (N X)) _ _)
  (at level 0, format "pure[ M  N ]").

Notation "ap[ M ]" := (@ap M _ _ _)
  (at level 0, format "ap[ M ]").
Notation "ap[ M N ]" := (@ap (fun X => M (N X)) _ _ _)
  (at level 0, format "ap[ M  N ]").
Notation "ap[ M N O ]" := (@ap (fun X => M (N (O X))) _ _ _)
  (at level 0, format "ap[ M  N  O ]").

Infix "<*>" := ap (at level 29, left associativity).
Infix "<*[ M ]>" := (@ap M _ _ _)
  (at level 29, left associativity, only parsing).

Notation "x <**> f" := (ap f x)
  (at level 29, left associativity, only parsing).
Notation "x <**[ M ]> f" := (@ap M _ _ _ f x)
  (at level 29, left associativity, only parsing).

Infix "*>" := (liftA2 (const id)) (at level 29, left associativity).
Infix "<*" := (liftA2 const) (at level 29, left associativity).

Notation "f <|> g" := (choose f g) (at level 29, left associativity).

End ApplicativeNotations.

Import ApplicativeNotations.

(*
The identity applicative [Id]: [pure = id] and [ap f x = f x].  As a lax
   monoidal functor it is the (strict) monoidal identity functor.

--------
同一性函子 [Id]：[pure = id] 和 [ap f x = f x]。作为一个松单体函子，它是（严格）单体同一函子。
*)
#[export]
Instance Identity_Applicative : Applicative id | 9 := {
  pure := λ _, id;
  ap := λ _ _ f x, f x;
}.

(*
The reader / function applicative [λ a, x → a] (Haskell's [(->) x]):
   [pure] is the constant function and [ap] threads the shared environment
   [r] through both the function and the argument.

--------
读者 / 函数函子 [λ a, x → a]（Haskell 的 [(->) x]）：
   [pure] 是常量函数，[ap] 将共享环境 [r] 贯穿于函数和参数中。
*)
#[export]
Instance arrow_Applicative x : Applicative (arrow x) := {
  pure := λ _ x _, x;
  ap := λ _ _ f x r, f r (x r);
}.

(*
The constant applicative [Const x] over a [Monoid x]: [pure] discards its
   value and returns [mempty]; [ap] combines the two accumulators with [⊗].
   This is the canonical example of a lax monoidal functor that is not a
   monad -- it is the lax monoidal functor [Types → Types] picking out the
   monoid [x], with [η = mempty] and [μ = (⊗)].

--------
常量函子 [Const x] 在 [Monoid x] 上的应用：[pure] 丢弃其值并返回 [mempty]；[ap] 使用 [⊗] 组合两个累加器。这是一个宽松幺半群函子不是单子（monad）的典型例子——它是宽松幺半群函子 [Types → Types]，选取幺半群 [x]，并具有 [η = mempty] 和 [μ = (⊗)]。
*)
#[export]
Instance Const_Applicative `{Monoid x} : Applicative (Const x) := {
  pure := λ _ _, mkConst mempty;
  ap := λ _ _ '(mkConst x) '(mkConst y), mkConst (x ⊗ y);
}.

(*
Applicatives are closed under composition: [F ∘ G] is again applicative
   (unlike monads).  [pure] is [pure[F] ∘ pure[G]], and [ap] uses [F]'s [ap]
   twice, first lifting [G]'s [ap] under [F] (via [pure ap[G]]) and then
   applying it.  Categorically this is the composite of the two laxators.

--------
应用函子在组合下是封闭的：[F ∘ G] 再次是应用函子（不像单子）。[pure] 是 [pure[F] ∘ pure[G]，而 [ap] 使用 [F] 的 [ap] 两次，首先在 [F] 下提升 [G] 的 [ap]（通过 [pure ap[G]），然后应用它。从范畴论的角度来看，这是两个松弛子（laxators）的复合。
*)
#[export]
Instance Compose_Applicative `{Applicative F} `{Applicative G} :
  Applicative (F ∘ G)  := {
  pure := λ _, pure[F] ∘ pure;
  ap   := λ _ _, ap[F] ∘ ap[F] (pure ap[G])
}.

(*
This is the standard Haskell-style [Alternative (Compose f g)]: it lifts F's
   Alternative structure pointwise over G, and does NOT use G's Alternative
   structure at all -- there is no canonical way to combine an [F (G x)] and
   [F (G x)] using G's choose without committing to a specific shape.

--------
这是标准的 Haskell 风格 [Alternative (Compose f g)]：它将 F 的 Alternative 结构逐点提升到 G 上，并且完全不使用 G 的 Alternative 结构——没有使用 G 的 choose 将 [F (G x)] 和 [F (G x)] 组合在一起的规范方法，而不需要指定具体的形状。
*)
#[export]
Instance Compose_Alternative `{Alternative F} `{Alternative G} :
  Alternative (F ∘ G) := {
  empty  := λ x, @empty F _ (G x);
  choose := λ x, @choose F _ (G x);
}.

(*
The Yoneda / co-Yoneda encoding of an applicative [F] is again applicative:
   the continuation-passing presentation [Yoneda F x = ∀ r, (x → r) → F r]
   transports [pure] and [ap] through the natural isomorphism [Yoneda F ≅ F].

--------
一个函子 [F] 的 Yoneda / co-Yoneda 编码再次是函子：
   连续传递表示 [Yoneda F x = ∀ r, (x → r) → F r]
   通过自然同构 [Yoneda F ≅ F] 传输 [pure] 和 [ap]。
*)
#[export]
Instance Yoneda_Applicative `{Applicative F} : Applicative (Yoneda F) := {
  pure := λ _ x, λ r k, pure (k x);
  ap := λ _ _ f x, λ r k, f _ (λ h, k ∘ h) <*> x _ id
}.

(*
Every applicative is a functor, recovering [fmap] from [pure] and [ap] by
   [fmap f x = pure f <*> x] (the standard [Applicative ⇒ Functor] derivation).
   Categorically: a lax monoidal functor is in particular a functor.

--------
每个应用函子都是一个范畴函子，通过 [fmap f x = pure f <*> x]（标准的 [Applicative ⇒ Functor] 推导）从 [pure] 和 [ap] 中恢复 [fmap]。  从范畴论的角度看：一个松单元函子尤其是一个函子。
*)
Section Instances.

Universe d c.
Context (F : Type@{d} -> Type@{c}).
Context `{Applicative F}.

#[export]  Instance Functor_Applicative@{} : Functor F | 9 := {
  fmap := λ _ _ f x, ap (pure f) x
}.

End Instances.
