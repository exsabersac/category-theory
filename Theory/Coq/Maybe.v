Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Applicative.
Require Import Category.Theory.Coq.Monad.
Require Import Category.Theory.Coq.Semigroup.
Require Import Category.Theory.Coq.Monoid.
Require Import Category.Theory.Coq.Traversable.

Generalizable All Variables.

(** The Maybe/option type [1 + a] as functor, applicative and monad / 作为函子、适用子和单子使用的 Maybe/option 类型 [1 + a] *)

(*
nLab: https://ncatlab.org/nlab/show/maybe+monad
   Wikipedia: https://en.wikipedia.org/wiki/Option_type

   FP reading.  [Maybe a] (Haskell) / [option a] (Coq, OCaml) adjoins a single
   distinguished value [Nothing] to [a], modelling an optional/partial result:
   [Just x] carries a value, [Nothing] signals its absence.  It is the standard
   way to track failure without exceptions or null references.  As a monad,
   failure short-circuits: [Nothing >>= f = Nothing] and [Just x >>= f = f x].

   Categorical reading.  [Maybe a = a + 1], the coproduct of [a] with the
   terminal object [1] (the unit type), with [Nothing = inr ()] the injection of
   [1] and [Just = inl] the injection of [a].  The endofunctor [a ↦ a + 1]
   carries the maybe (a.k.a. exception/partiality) monad: the unit [η] is [Just]
   and the multiplication [μ : (a + 1) + 1 → a + 1] (here [Maybe_join]) merges
   the two copies of [1].  Its Kleisli morphisms [a → b + 1] are precisely the
   partial functions [a ⇀ b], so the Kleisli category on [Set] is the category
   of sets and partial functions; its algebras are the pointed objects.

   Following the other [Theory/Coq] classes, the operations are recorded here
   without their laws; lawfulness is discharged per concrete use.

--------
nLab：https://ncatlab.org/nlab/show/maybe+monad
维基百科：https://en.wikipedia.org/wiki/Option_type

函数式编程阅读。[Maybe a]（Haskell）/ [option a]（Coq、OCaml）将一个单一的特殊值 [Nothing] 附加到 [a] 上，模拟可选/部分结果：[Just x] 承载一个值，[Nothing] 表示其缺失。它是跟踪失败而不使用异常或空引用的标准方法。作为一个单子，失败会短路：[Nothing >>= f = Nothing] 和 [Just x >>= f = f x]。

范畴论解读。[Maybe a = a + 1] 是 [a] 与终对象 [1]（单位类型）的余积，[Nothing = inr ()] 是 [1] 的注入，[Just = inl] 是 [a] 的注入。函子 [a ↦ a + 1] 携带了 maybe（又称异常/部分性）模范：单位 [η] 为 [Just]，乘法 [μ : (a + 1) + 1 → a + 1]（这里为 [Maybe_join]）合并了两份 [1]。它的 Kleisli 态射 [a → b + 1] 恰好是部分函数 [a ⇀ b]，因此 [Set] 上的 Kleisli 范畴是集合与部分函数的范畴；其代数是带尖点的对象。

继其他 [Theory/Coq] 类之后，这里的操作被记录下来，但没有附带它们的法律；合法性根据具体使用情况而定。
*)

Notation Maybe   := option.   (* the option type [Maybe a = a + 1] / 选项类型 [Maybe a = a + 1] *)
Notation Nothing := None.     (* [inr ()] : the absent/failure case / [inr ()]：缺席/失败情况 *)
Notation Just    := Some.     (* [inl]    : injection of a value / [inl] : 注入一个值 *)

Definition fromMaybe `(x : a) (my : Maybe a) : a :=
  match my with
  | Just z  => z
  | Nothing => x
  end.

(*
The maybe eliminator: the copairing [[const x, f] : a + 1 → b] out of the
   coproduct [Maybe a = a + 1], sending [Just z] to [f z] and [Nothing] to [x].

--------
可能的消除器：共配对 [[const x, f] : a + 1 → b] 从余积 [Maybe a = a + 1] 出发，将 [Just z] 发送到 [f z]，并将 [Nothing] 发送到 [x]。
*)
Definition maybe `(x : b) `(f : a → b) (my : Maybe a) : b :=
  match my with
  | Just z  => f z
  | Nothing => x
  end.

Definition Maybe_map `(f : X → Y) (x : Maybe X) : Maybe Y :=
  match x with
  | Nothing => Nothing
  | Just x' => Just (f x')
  end.

#[export]
Instance Maybe_Functor : Functor Maybe := {
  fmap := @Maybe_map
}.

Definition Maybe_apply {X Y} (f : Maybe (X → Y)) (x : Maybe X) : Maybe Y :=
  match f with
  | Nothing => Nothing
  | Just f' => match x with
    | Nothing => Nothing
    | Just x' => Just (f' x')
    end
  end.

#[export]
Instance Maybe_Applicative : Applicative Maybe := {
  pure := @Just;
  ap := @Maybe_apply
}.

(*
Monad multiplication [μ : (X + 1) + 1 → X + 1], collapsing the two copies of
   the unit [1] (both outer and inner [Nothing]) to a single [Nothing].

--------
单子乘法 [μ : (X + 1) + 1 → X + 1]，将单位 [1] 的两个副本（外部和内部的 [Nothing]）合并为一个 [Nothing]。
*)
Definition Maybe_join {X} (x : Maybe (Maybe X)) : Maybe X :=
  match x with
  | Nothing => Nothing
  | Just Nothing => Nothing
  | Just (Just x') => Just x'
  end.

Definition Maybe_bind {X Y} (m : Maybe X) (f : X → Maybe Y) : Maybe Y :=
  match m with
  | Nothing => Nothing
  | Just m' => f m'
  end.

#[export]
Instance Maybe_Monad : Monad Maybe := {
  ret := @Just;
  bind := @Maybe_bind;
}.

Definition isJust {a} (x : Maybe a) := if x then true else false.

(*
Left-biased choice: return the first [Just], else fall through to [y].
   This is the standard [Alternative] instance, with [empty = Nothing] the unit.

--------
偏向左的选择：返回第一个 [Just]，否则继续到 [y]。 这是标准的 [Alternative] 实例，单位是 [empty = Nothing]。
*)
Definition Maybe_choose {a} (x y : Maybe a) : Maybe a :=
  match x with
  | Nothing => y
  | Just _  => x
  end.

#[export]
Instance Maybe_Alternative : Alternative Maybe := {
  empty  := @Nothing;
  choose := @Maybe_choose
}.

Import MonadNotations.

(*
Lifting a semigroup on [a] to [Maybe a]: [Nothing] acts as a freely adjoined
   identity, and two [Just]s combine with the underlying [⊗].  This is the
   standard construction making [Maybe a] a monoid (unit [Nothing]) from any
   semigroup [a] -- i.e. freely adjoining a unit.

--------
将半群从 [a] 提升到 [Maybe a]：[Nothing] 作为一个自由加入的单位，而两个 [Just] 与底层的 [⊗] 结合。这是将 [Maybe a] 从任何半群 [a] 构造成幺半群（单位 [Nothing]）的标准构造——即自由地加入一个单位。
*)
Definition Maybe_append `{Semigroup a} (x y : Maybe a) : Maybe a :=
  match x, y with
  | Nothing, x     => x
  | x, Nothing     => x
  | Just x, Just y => Just (x ⊗ y)
  end.

#[export]
Program Instance Semigroup_Maybe `{Semigroup a} : Semigroup (Maybe a) := {
  mappend := Maybe_append
}.

(*
[Maybe a] is a monoid with unit [Nothing] (adjoined above).  Only a
   [Semigroup a] is needed for [mappend]; the [Monoid a] constraint here is
   stronger than strictly required (Haskell asks only for [Semigroup a]).

--------
[Maybe a] 是一个带有单位 [Nothing]（如上所示）的幺半群。只需 [Semigroup a] 就可以用于 [mappend]；这里的 [Monoid a] 约束比严格要求的要强（Haskell 只要求 [Semigroup a]）。
*)
#[export]
Program Instance Monoid_option `{Monoid a} : Monoid (Maybe a) := {
  mempty := None
}.

(*
Traversable: [sequence] commutes [Maybe] past an applicative [F], turning
   [Maybe (F x)] into [F (Maybe x)].  [Nothing] becomes [pure Nothing]; a
   [Just]-wrapped effect is run and re-wrapped with [fmap Just].

--------
可遍历：[sequence] 将 [Maybe] 经过一个应用型 [F] 进行换位，将 [Maybe (F x)] 转换为 [F (Maybe x)]。[Nothing] 变为 [pure Nothing]；一个被 [Just] 包裹的效果被运行，然后再用 [fmap Just] 重新包裹。
*)
#[export]
Instance Maybe_Traversable : Traversable Maybe := {
  sequence := λ _ _ _ x,
    match x with
    | Nothing => pure Nothing
    | Just x  => fmap Just x
    end
}.

#[export]
Instance Maybe_Tupersable {rep} : Tupersable rep Maybe := {
  sequenceT := fun A (s : rep) x =>
    match x with
    | Nothing => (s, Nothing)
    | Just (s', x)  => (s', Just x)
    end
}.
