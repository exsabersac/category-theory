Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Applicative.
Require Import Category.Theory.Coq.Monad.

Generalizable All Variables.

(** The Either/sum type [a + b] as bifunctor, and the error monad in [b] / 作为双函子的 Either/和类型 [a + b]，以及 [b] 中的错误单子 *)

(*
nLab: https://ncatlab.org/nlab/show/coproduct
   Wikipedia: https://en.wikipedia.org/wiki/Tagged_union

   FP reading.  [Either a b] (Haskell) / [sum a b], written [a + b] (Coq), is
   the canonical two-case tagged union: a value is either [Left x] carrying an
   [a] or [Right y] carrying a [b], with the tag recording which.  It is the
   standard way to return a result-or-error, [a] conventionally holding the
   error/exception and [b] the success value.  As a monad in its right argument
   (the exception/error monad), [Left] short-circuits and [Right] continues:
   [Left e >>= f = Left e] and [Right x >>= f = f x].

   Categorical reading.  [a + b] is the binary coproduct of [a] and [b], with
   [Left = inl : a → a + b] and [Right = inr : b → a + b] the coproduct
   injections.  Its universal property is the copairing: any [f : a → c] and
   [g : b → c] factor through a unique [[f, g] : a + b → c] (here [either])
   with [[f, g] ∘ inl = f] and [[f, g] ∘ inr = g].  The sum is a bifunctor
   [(+) : C × C → C]; fixing the left summand [E] gives the endofunctor
   [b ↦ E + b] (here [Either_Functor]), which carries the exception monad: the
   unit [η] is [Right] and the multiplication [μ : E + (E + b) → E + b] (here
   [Either_join]) collapses the two copies of [E].  [Maybe a = a + 1] is the
   special case [E = 1].

   Following the other [Theory/Coq] classes, the operations are recorded here
   without their laws; lawfulness is discharged per concrete use.

--------
nLab：https://ncatlab.org/nlab/show/coproduct
维基百科：https://en.wikipedia.org/wiki/Tagged_union

函数式编程阅读。[Either a b]（Haskell）/ [sum a b]，[a + b]（Coq）编写，是规范的两案例标记联合类型：一个值要么是[Left x]并携带一个[a]，要么是[Right y]并携带一个[b]，标签记录了是哪一种。这是返回结果或错误的标准方式，[a]通常保存错误/异常，[b]保存成功值。作为其右参数中的单子（异常/错误单子），[Left]会短路而[Right]会继续：[Left e >>= f = Left e]和[Right x >>= f = f x]。

范畴论阅读。[a + b] 是 [a] 和 [b] 的二元余积，其中 [Left = inl : a → a + b] 和 [Right = inr : b → a + b] 是余积注入。它的普遍性性质是共配对：任意 [f : a → c] 和 [g : b → c] 都可以通过唯一的 [[f, g] : a + b → c（这里是 [either]）因子分解，使得 [[f, g] ∘ inl = f 并且 [[f, g] ∘ inr = g。这个和是一个双函子 [(+) : C × C → C]；固定左边的加数 [E] 得到自函子 [b ↦ E + b]（这里是 [Either_Functor]），它承载异常单子：单位 [η] 是 [Right]，乘法 [μ : E + (E + b) → E + b]（这里是 [Either_join]）将两个 [E] 的副本合并。[Maybe a = a + 1] 是特殊情况 [E = 1]。

继其他 [Theory/Coq] 类之后，这里的操作被记录下来，但没有附带它们的法律；合法性根据具体使用情况而定。
*)

Notation Either := sum (only parsing).   (* [Either a b = a + b], the coproduct / [Either a b = a + b]，共同产品 *)
Notation Left   := inl (only parsing).    (* [inl : a → a + b], left injection / [inl : a → a + b]，左侧注射 *)
Notation Right  := inr (only parsing).    (* [inr : b → a + b], right injection / [inr : b → a + b]，正确注射 *)

Definition isLeft  `(x : a + b) : bool := if x then true else false.
Definition isRight `(x : a + b) : bool := if x then false else true.

(*
The copairing [[f, g] : a + b → c] out of the coproduct: the unique map
   with [[f, g] ∘ inl = f] and [[f, g] ∘ inr = g] (the eliminator for sums).

--------
余积中的共对 [[f, g] : a + b → c]：满足 [[f, g] ∘ inl = f] 且 [[f, g] ∘ inr = g] 的唯一映射（和的消去子）。
*)
Definition either `(f : a → c) `(g : b → c) (x : a + b) : c :=
  match x with
  | inl a => f a
  | inr b => g b
  end.

(*
The bifunctor's action on the LEFT summand: [f + id : a + b → c + b],
   rewriting [Left l] to [Left (f l)] and leaving [Right] fixed.  Contrast
   [Either_map] below, which acts on the right summand.

--------
双函子的作用在左半部：[f + id : a + b → c + b]，将 [Left l] 重写为 [Left (f l)] 并保持 [Right] 不变。对比下面的 [Either_map]，其作用于右半部。
*)
Definition mapLeft `(f : a → c) `(x : a + b) : c + b :=
  match x with
  | inl l => inl (f l)
  | inr r => inr r
  end.

(*
The functor [b ↦ E + b] (left summand [E] fixed): [fmap] maps over the
   [Right] value and propagates [Left e] unchanged.

--------
函子 [b ↦ E + b]（左加数 [E] 固定）：[fmap] 映射 [Right] 值并保持 [Left e] 不变。
*)
Definition Either_map {E X Y} (f : X → Y) (x : Either E X) : Either E Y :=
  match x with
  | Left e   => Left e
  | Right x' => Right (f x')
  end.

(*
Applicative [ap]: a [Left] in either the function or the argument
   short-circuits to that [Left] (the function's [Left] taking priority).

--------
应用程序 [ap]：在函数或参数中的 [Left] 会短路到该 [Left]（函数的 [Left] 优先）。
*)
Definition Either_ap {E X Y} (f : Either E (X → Y)) (x : Either E X)
  : Either E Y :=
  match f with
  | Left e   => Left e
  | Right f' => match x with
    | Left e   => Left e
    | Right x' => Right (f' x')
    end
  end.

(*
The monad multiplication [μ : E + (E + b) → E + b], collapsing the two
   copies of the error summand [E] (an outer or inner [Left] both yield [Left]).

--------
单子乘法 [μ : E + (E + b) → E + b]，合并错误项的两个副本 [E]（一个外部或内部的 [Left] 都会产生 [Left]）。
*)
Definition Either_join {E X} (x : Either E (Either E X)) : Either E X :=
  match x with
  | Left e           => Left e
  | Right (Left e)   => Left e
  | Right (Right x') => Right x'
  end.

(*
Monadic [bind] of the exception monad: [Left e] short-circuits (ignoring [f]),
   [Right x'] continues with [f x'].

--------
异常单子（exception monad）的单子化 [bind]：[Left e] 会短路（忽略 [f]），[Right x'] 会继续执行 [f x']。
*)
Definition Either_bind {E X Y} (x : Either E X) (f : X → Either E Y) :
  Either E Y :=
  match x with
  | Left e   => Left e
  | Right x' => f x'
  end.

(* The endofunctor [b ↦ E + b] on Coq types (left summand [E] fixed). / Coq 类型上的端函子 [b ↦ E + b]（左直和 [E] 固定）。 *)
#[export]
Instance Either_Functor {E} : Functor (Either E) := {
  fmap := @Either_map E
}.

(* Applicative structure; [pure = Right] injects a success value. / 应用结构；[pure = Right] 注入一个成功值。 *)
#[export]
Instance Either_Applicative {E} : Applicative (Either E) := {
  pure := @Right E;
  ap := @Either_ap E;
}.

(* The exception monad in the right argument; the unit [η = ret] is [Right]. / 右边参数中的异常单子；单元 [η = ret] 是 [Right]。 *)
#[export]
Instance Either_Monad {E} : Monad (Either E) := {
  ret := @Right E;
  bind := @Either_bind E;
}.
