Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Applicative.
Require Import Category.Theory.Coq.Monad.
Require Import Category.Theory.Coq.Semigroup.
Require Import Category.Theory.Coq.Monoid.

Generalizable All Variables.

(** The pair/tuple type [A * B], with its product (and writer-monad) reading / 成对/元组类型 [A * B]，以及它的乘积（和作家单子）读取 *)

(*
nLab: https://ncatlab.org/nlab/show/product
   nLab: https://ncatlab.org/nlab/show/writer+monad
   Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_product

   FP reading.  [Tuple] is just Coq's pair constructor [prod], i.e. the type
   [A * B].  Holding the first component fixed, [Tuple x = (x * −)] is a
   Functor whose [fmap] acts on the second component ([prod_map]); when the
   fixed component [x] carries a Monoid it becomes the writer monad, which
   threads (accumulates) a monoidal "log" alongside a value, with [ret]/[pure]
   seeding the empty log [mempty] and [bind]/[ap] combining logs with [⊗]
   (mappend).  [first]/[second] give the action of [prod] as a bifunctor on,
   respectively, the first and second components.

   Categorical reading.  [A * B] is the binary product of [A] and [B] in the
   category of Coq types: it comes with the two projections [fst : A * B → A]
   and [snd : A * B → B], and for any [f : Q → A], [g : Q → B] the pairing
   (tupling) map ⟨f, g⟩ = [λ q, (f q, g q)] is the unique mediating morphism
   with [fst ∘ ⟨f,g⟩ = f] and [snd ∘ ⟨f,g⟩ = g].  This is the Cartesian
   product of Set, here realized in Coq.  The associators below
   ([tuple_swap_*]) witness [A * (B * C) ≅ (A * B) * C]; [curry]/[uncurry]
   witness the product/exponential adjunction [(A * B) → C  ≅  A → (B → C)],
   the defining isomorphism of a closed structure.

   Equality on this data is plain Coq [=]: pairs are an inductive type with
   decidable structure, so no setoid [≈] is needed at this layer.

--------
nLab: https://ncatlab.org/nlab/show/product
nLab: https://ncatlab.org/nlab/show/writer+monad
维基百科: https://en.wikipedia.org/wiki/Product_(category_theory)
维基百科: https://en.wikipedia.org/wiki/Cartesian_product

FP 阅读。[Tuple] 只是 Coq 的对构造器 [prod]，即类型 [A * B]。固定第一个分量后，[Tuple x = (x * −)] 是一个函子，其 [fmap] 作用于第二个分量（[prod_map]）；当固定分量 [x] 携带一个幺半群时，它变成写入者单子，它沿着值线程（累积）一个幺半群“日志”，其中 [ret]/[pure] 初始化空日志 [mempty]，而 [bind]/[ap] 使用 [⊗]（mappend）组合日志。[first]/[second] 给出 [prod] 作为双函子分别在第一和第二分量上的作用。

范畴论解读。[A * B] 是 Coq 类型范畴中 [A] 和 [B] 的二元积：它带有两个投影 [fst : A * B → A] 和 [snd : A * B → B]，对于任意的 [f : Q → A]、[g : Q → B]，成对映射（元组映射） ⟨f, g⟩ = [λ q, (f q, g q)] 是唯一的中介态射，满足 [fst ∘ ⟨f,g⟩ = f] 和 [snd ∘ ⟨f,g⟩ = g]。这是 Set 的笛卡尔积，这里在 Coq 中实现。下面的联结子（[tuple_swap_*]）证明了 [A * (B * C) ≅ (A * B) * C]；[curry]/[uncurry] 证明了积/指数伴随 [(A * B) → C  ≅  A → (B → C)]，这是闭结构的定义同构。

在这些数据上，等式非常明显 Coq [=]：对是一个带有可判定结构的归纳类型，因此在这一层不需要集合论 [≈]。
*)

Notation Tuple := prod (only parsing).

(*
The two halves of the product associator [A * (B * C) ≅ (A * B) * C];
   [tuple_swap_a_bc_to_ab_c] and [tuple_swap_ab_c_to_a_bc] are mutually
   inverse and witness that the product is associative up to isomorphism.

--------
产品结合器 [A * (B * C) ≅ (A * B) * C] 的两个部分；[tuple_swap_a_bc_to_ab_c] 和 [tuple_swap_ab_c_to_a_bc] 互为逆，并且证明该乘积在同构意义下是结合的。
*)
Definition tuple_swap_a_bc_to_ab_c {A B C} (x : A * (B * C)) : A * B * C :=
  match x with (a, (b, c)) => ((a, b), c) end.

Definition tuple_swap_ab_c_to_a_bc {A B C} (x : A * B * C) : A * (B * C) :=
  match x with ((a, b), c) => (a, (b, c)) end.

(*
Pairing maps building a 3-fold product from three components, associated to
   the left ([(A * B) * C]) and to the right ([A * (B * C)]) respectively.

--------
配对映射从三个组件构建三重积，分别与左侧（[(A * B) * C]）和右侧（[A * (B * C)]）相关联。
*)
Definition left_triple {A B C} (x : A) (y : B) (z : C) : A * B * C :=
  ((x, y), z).

Definition right_triple {A B C} (x : A) (y : B) (z : C) : A * (B * C) :=
  (x, (y, z)).

(*
The bifunctorial action of [prod] on its first and second components:
   [first f] maps the left coordinate, [second f] the right one (Haskell's
   [first]/[second] from [Data.Bifunctor], here for the pair bifunctor).

--------
[prod] 在其第一个和第二个分量上的双函子作用：[first f] 映射左坐标，[second f] 映射右坐标（Haskell 的 [first]/[second] 来自 [Data.Bifunctor]，在这里用于对偶函子）。
*)
Definition first `(f : a -> b) `(x : a * z) : b * z :=
  match x with (a, z) => (f a, z) end.

Definition second `(f : a -> b) `(x : z * a) : z * b :=
  match x with (z, b) => (z, f b) end.

(*
[curry]/[uncurry] are the two directions of the product/exponential
   adjunction iso [(a * b) → c  ≅  a → (b → c)], the universal property of the
   exponential object (currying).

--------
[curry]/[uncurry] 是乘积/指数伴随同构 [(a * b) → c  ≅  a → (b → c)] 的两个方向，指数的泛性质（柯里化）。
*)
Definition curry `(f : a -> b -> c) (x : (a * b)) : c :=
  match x with (a, b) => f a b end.

Definition uncurry {X Y Z} (f : X -> Y -> Z) (xy : X * Y) : Z :=
  match xy with (x, y) => f x y end.

(*
[prod_map] is [fmap] for the second-argument functor [(C * −)]: it maps the
   second component and leaves the first untouched (= [second]).

--------
[prod_map] 是第二参数函子 [(C * −)] 的 [fmap]：它映射第二个分量而保持第一个分量不变（= [second]）。
*)
Definition prod_map {A B C : Type} (f : A -> B) (x : C * A) : C * B :=
  match x with (a, b) => (a, f b) end.

(*
[(x * −)] is a Functor (the endofunctor fixing the first component); its
   [fmap] maps the second component via [prod_map].

--------
[(x * −)] 是一个函子（固定第一个分量的自函子）；它的 [fmap] 通过 [prod_map] 映射第二个分量。
*)
#[export]
Instance Tuple_Functor x : Functor (Tuple x) := {
  fmap := λ _ _, prod_map   (* hom map: act on the second component only / 同调映射：只作用于第二个分量 *)
}.

(*
The writer monad as an Applicative, available when the fixed component [x]
   is a Monoid: [pure] seeds the empty log, [ap] runs both effects and joins
   their logs with [⊗] (mappend).

--------
当固定组件 [x] 是一个幺半群时，写入器单子可以作为 Applicative 使用：[pure] 生成空日志，[ap] 运行两个效果并使用 [⊗]（mappend）合并它们的日志。
*)
#[export]
Instance Tuple_Applicative x `{Monoid x} : Applicative (Tuple x) := {
  pure := λ _ y, (mempty, y);                         (* empty log [mempty], value [y] / 空日志 [mempty]，值 [y] *)
  ap := λ _ _ '(xf, f) '(xx, x), (xf ⊗ xx, f x);      (* combine logs, apply function / 合并日志，应用函数 *)
}.

(*
The writer monad: [ret] seeds the empty log; [bind] runs [f] on the held
   value and concatenates the incoming log [xm] with the produced log [xx].
   Lawful precisely because [x] is a Monoid (the monad laws follow from the
   monoid laws on [⊗]/[mempty]).

--------
写入者单子：[ret] 给空日志播种；[bind] 对持有的值运行 [f]，并将传入的日志 [xm] 与产生的日志 [xx] 连接起来。它合法的原因正是因为 [x] 是一个幺半群（单子律遵循 [⊗]/[mempty] 上的幺半群律）。
*)
#[export]
Instance Tuple_Monad x `{Monoid x} : Monad (Tuple x) := {
  ret := λ _ y, (mempty, y);                                          (* unit: empty log [mempty] / 单位：空日志 [mempty] *)
  bind := λ _ _ '(xm, m) f, let '(xx, x) := f m in (xm ⊗ xx, x)       (* concatenate logs via [⊗] / 通过 [⊗] 连接日志 *)
}.
