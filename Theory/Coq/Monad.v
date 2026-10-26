Require Import Category.Lib.
Require Export Category.Theory.Coq.Applicative.

Generalizable All Variables.

(** The Monad type class (bind/return), with its categorical reading / Monad 类型类（bind/return）及其范畴论解读 *)

(*
nLab: https://ncatlab.org/nlab/show/monad
   nLab: https://ncatlab.org/nlab/show/Kleisli+category
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(functional_programming)
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)

   FP reading.  A monad on the category of types is a type constructor
   [F : Type → Type] with [ret : x → F x] (Haskell's [return]/[pure]) and
   [bind : F x → (x → F y) → F y] (Haskell's [>>=]).  In Kleisli form the
   three monad laws are: left identity [ret a >>= f ≈ f a]; right identity
   [m >>= ret ≈ m]; and associativity
   [(m >>= f) >>= g ≈ m >>= (λ x, f x >>= g)].

   Categorical reading.  The same data is an endofunctor [F] equipped with
   two natural transformations: the unit [η : Id ⇒ F] (here [ret]) and the
   multiplication [μ : F ∘ F ⇒ F] (here [join m = bind m id]), subject to
   [μ ∘ Fη = μ ∘ ηF = id] (unit) and [μ ∘ Fμ = μ ∘ μF] (associativity).
   The two presentations are interdefinable by [bind m f = μ (fmap f m)]
   (= [join (liftM f m)] below) and conversely [join = bind _ id],
   [fmap f = liftM f = bind _ (ret ∘ f)].

   As is usual for these Coq/Haskell-style classes, the laws are NOT recorded
   as fields here; [Monad] carries only the operations, and lawfulness is an
   obligation discharged for each concrete instance.

--------
nLab: https://ncatlab.org/nlab/show/monad
nLab: https://ncatlab.org/nlab/show/Kleisli+category
维基百科: https://en.wikipedia.org/wiki/Monad_(functional_programming)
维基百科: https://en.wikipedia.org/wiki/Monad_(category_theory)

函数式编程阅读。类型范畴上的一个单子是一个类型构造器 [F : Type → Type]，带有 [ret : x → F x]（Haskell 的 [return]/[pure]）和 [bind : F x → (x → F y) → F y]（Haskell 的 [>>=]）。在 Kleisli 形式下，三个单子定律是：左单位律 [ret a >>= f ≈ f a]；右单位律 [m >>= ret ≈ m]；以及结合律 [(m >>= f) >>= g ≈ m >>= (λ x, f x >>= g)]。

范畴论的解读。相同的数据是一个端函子 [F]，配备两个自然变换：单位 [η : Id ⇒ F]（这里是 [ret]）和乘法 [μ : F ∘ F ⇒ F]（这里是 [join m = bind m id]），满足 [μ ∘ Fη = μ ∘ ηF = id]（单位）和 [μ ∘ Fμ = μ ∘ μF]（结合性）。这两种表示可以通过 [bind m f = μ (fmap f m)]（= 下文的 [join (liftM f m)]）相互定义，反之亦然 [join = bind _ id]，[fmap f = liftM f = bind _ (ret ∘ f)]。

像这些 Coq/Haskell 风格的类一样，这里的定律并未被记录为字段；[Monad] 只包含操作，而合法性是对每个具体实例履行的义务。
*)

Class Monad@{d c} {F : Type@{d} → Type@{c}} := {
  ret : ∀ {x : Type@{d}}, x → F x;          (* unit η : Id ⇒ F  (Haskell return/pure) / 单位 η : Id ⇒ F  （Haskell 的 return/pure） *)
  bind : ∀ {x y : Type@{d}}, F x → (x → F y) → F y;  (* Kleisli extension (Haskell >>=) / Kleisli 扩展（Haskell >>=） *)
}.

Arguments Monad : clear implicits.

Section Monad.

Universes d c.
Context {F : Type@{d} -> Type@{c}}.
Context `{Monad F}.

(*
[join] is the monad multiplication μ : F (F x) → F x.  It collapses one
   layer of structure; categorically μ = bind _ id, and FP-side
   [join m ≈ m >>= id].  nLab: https://ncatlab.org/nlab/show/monad

--------
[join] 是单子乘法 μ : F (F x) → F x。它会折叠一层结构；在范畴论中 μ = bind _ id，以及 FP 方面的 [join m ≈ m >>= id]。nLab: https://ncatlab.org/nlab/show/monad
*)
Definition join {x} (m : F (F x)) : F x := bind m id.

(*
Kleisli (fish) composition (>=>): the composition of the Kleisli category
   of [F], whose arrows x ⇒ y are functions x → F y and whose identity is
   [ret].  Categorically [(g ∘_Kl f) = μ ∘ F(g) ∘ f]; FP-side
   [(f >=> g) x ≈ f x >>= g].
   nLab: https://ncatlab.org/nlab/show/Kleisli+category

--------
Kleisli（鱼）组合 (>=>)：[F] 的 Kleisli 范畴的组合，其箭头 x ⇒ y 是函数 x → F y，其恒等映射为 [ret]。从范畴的角度看为 [(g ∘_Kl f) = μ ∘ F(g) ∘ f]；FP 方面为 [(f >=> g) x ≈ f x >>= g]。nLab: https://ncatlab.org/nlab/show/Kleisli+category
*)
Definition kleisli_compose {x y z : Type@{d}} `(f : x → F y) `(g : y → F z) :
  x → F z := λ x, bind (f x) g.

(*
[liftM] is the functorial action fmap of [F] expressed through the monad:
   [fmap f = liftM f = bind _ (ret ∘ f)], i.e. FP-side
   [liftM f m ≈ m >>= (ret ∘ f)] (= μ ∘ F(ret ∘ f) categorically).

--------
[liftM] 是通过单子表达的 [F] 的函子作用 fmap：
   [fmap f = liftM f = bind _ (ret ∘ f)]，即 FP 方面
   [liftM f m ≈ m >>= (ret ∘ f)]（= μ ∘ F(ret ∘ f) 在范畴上）。
*)
Definition liftM {x y : Type@{d}} (f : x → y) : F x → F y :=
  λ x, bind x (λ x, ret (f x)).

Definition liftM2 {x y z : Type@{d}} (f : x → y → z) : F x → F y → F z :=
  Eval cbv beta iota zeta delta [ liftM ] in
    λ x y, bind x (λ x, liftM (f x) y).

Definition liftM3 {x y z w : Type@{d}} (f : x → y → z → w) :
  F x → F y → F z → F w :=
  Eval cbv beta iota zeta delta [ liftM2 ] in
    λ x y z, bind x (λ x, liftM2 (f x) y z).

(*
[apM] is the applicative [ap] (<*>) derived from the monad:
   [apM fM aM ≈ fM >>= (λ f, liftM f aM)].  This is the canonical lax-monoidal
   structure every monad induces (see [Applicative_Monad] below).

--------
[apM] 是从单子 [apM fM aM ≈ fM >>= (λ f, liftM f aM)] 推导出的应用性 [ap] (<*>)。这是每个单子诱导的规范松单体结构（见下文的 [Applicative_Monad]）。
*)
Definition apM {x y : Type@{d}} (fM : F (x → y)) (aM : F x) : F y :=
  bind fM (λ f, liftM f aM).

(*
[when]/[unless] are the standard Haskell conditional combinators: run the
   effect [x] when (resp. unless) the guard holds, otherwise do nothing
   [ret tt].  No categorical content beyond [ret].

--------
[when]/[unless] 是标准的 Haskell 条件组合子：当守卫成立（或不成立）时执行效果 [x]，否则不执行 [ret tt]。除了 [ret] 外，没有其它范畴内容。
*)
Definition when (b : bool) (x : F unit) : F unit :=
  if b then x else ret tt.

Definition unless (b : bool) (x : F unit) : F unit :=
  if negb b then x else ret tt.

End Monad.

Module MonadNotations.

Export ApplicativeNotations.

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.
Bind Scope monad_scope with Monad.

Notation "ret[ M ]" := (@ret M _ _) (at level 9) : monad_scope.
Notation "ret[ M N ]" := (@ret (M ∘ N) _ _) (at level 9) : monad_scope.

Notation "bind[ M ]" := (@bind M _ _ _) (at level 9) : monad_scope.
Notation "bind[ M N ]" := (@bind (M ∘ N) _ _ _) (at level 9) : monad_scope.

Notation "join[ M ]" := (@join M _ _ _ _) (at level 9) : monad_scope.
Notation "join[ M N ]" := (@join (M ∘ N) _ _) (at level 9) : monad_scope.

Notation "m >>= f" := (bind m f)
  (at level 42, right associativity) : monad_scope.
Notation "m >>=[ M ] f" := (@bind M _ _ _ m f)
  (at level 42, right associativity, only parsing) : monad_scope.
Notation "f =<< m" := (bind m f)
  (at level 42, right associativity) : monad_scope.
Notation "f =<<[ M ] m" := (@bind M _ _ _ m f)
  (at level 42, right associativity, only parsing) : monad_scope.
Notation "a >> b" := (a >>= λ _, b)%monad
  (at level 81, right associativity) : monad_scope.
Notation "b << a" := (a >>= λ _, b)%monad
  (at level 81, right associativity) : monad_scope.

Infix ">=>" := kleisli_compose
  (at level 42, right associativity) : monad_scope.
Notation "f <=< g" :=
  (kleisli_compose g f) (at level 42, right associativity) : monad_scope.

Notation "f >=[ M ]=> g" := (@kleisli_compose M _ _ _ _ _ f _ g)
  (at level 42, right associativity) : monad_scope.
Notation "f <=[ M ]=< g" := (@kleisli_compose M _ _ _ _ _ g _ f)
  (at level 42, right associativity) : monad_scope.

(*
Haskell-style [do] notation: [x <- A ;; B] desugars to [A >>= λ x, B],
   sequencing the effect [A] and binding its result to [x] in [B].

--------
Haskell 风格的 [do] 表记法：[x <- A ;; B] 被解糖为 [A >>= λ x, B]，顺序执行效果 [A] 并将其结果绑定到 [x] 中的 [B]。
*)
Notation "x <- A ;; B" := (A >>= (λ x, B))%monad
  (at level 81, A at next level, right associativity) : monad_scope.

Notation "' pat <- A ;; B" := (A >>= (λ x, match x with pat => B end))%monad
  (at level 81, pat pattern, A at next level, right associativity) : monad_scope.

Notation "'let*' pat ':=' A 'in' B" := (@bind _ _ _ _ A (λ pat, B))
  (at level 81, pat as pattern, A at next level, right associativity) : monad_scope.

Notation "A ;; B" := (A >>= (λ _, B))%monad
  (at level 81, right associativity, only parsing) : monad_scope.

End MonadNotations.

(*
The identity monad: [F = id], with [ret] and [bind] trivial.  This is the
   initial object among monads and the unit of monad composition.

--------
恒等幺半群：[F = id]，[ret] 和 [bind] 是平凡的。这是在幺半群中最初的对象，也是幺半群组合的单位。
*)
#[export]
Instance Identity_Monad : Monad id | 9 := {
  ret := λ _ x, x;
  bind := λ _ _ m f, f m;
}.

(*
The reader monad [arrow x = (x → -)]: [ret] is the constant function and
   [bind] threads the shared environment [r] through both computations.  It is
   the monad of the [(x →) ⊣] currying adjunction (functions from a fixed [x]).
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(functional_programming)#Environment_monad

--------
读者单子 [arrow x = (x → -)]: [ret] 是常数函数，并且 [bind] 通过两个计算线程共享环境 [r]。它是固定 [x] 的函数的 [(x →) ⊣] 柯里化伴随的单子。维基百科：https://en.wikipedia.org/wiki/Monad_(functional_programming)#Environment_monad
*)
#[export]
Instance arrow_Monad x : Monad (arrow x) := {
  ret := λ _ x _, x;
  bind := λ _ _ m f r, f (m r) r;
}.

(*
[Monad_Distributes] packages the data needed to make the composite [M ∘ N]
   a monad: a swap/prod map [mprod : N (M (N x)) → M (N x)].  This is the
   half of a distributive law of [N] over [M] sufficient for [Compose_Monad];
   a full distributive law N ∘ M ⇒ M ∘ N (a [BeckDistributiveLaw]) is the
   structure that guarantees the composite is again a monad.
   nLab: https://ncatlab.org/nlab/show/distributive+law

--------
[Monad_Distributes] 打包了使复合 [M ∘ N] 成为单子所需的数据：一个交换/乘积映射 [mprod : N (M (N x)) → M (N x)]。这是 [N] 在 [M] 上的分配律的一半，足以用于 [Compose_Monad]；完整的分配律 N ∘ M ⇒ M ∘ N（一个 [BeckDistributiveLaw]）是保证复合再次成为单子的结构。nLab: https://ncatlab.org/nlab/show/distributive+law
*)
Class Monad_Distributes (M N : Type → Type) :=
  mprod : ∀ {x}, N (M (N x)) → M (N x).

Arguments mprod M N {_ x} _.

Import MonadNotations.

Open Scope monad_scope.

(*
The composite [M ∘ N] is a monad given a distributive law [Monad_Distributes]:
   [ret] is [ret[M] ∘ pure[N]] (both units stacked) and [bind] uses [mprod] to
   commute the inner [N] past the outer [M].  This is the standard
   “monad-on-monad via a distributive law” construction.
   nLab: https://ncatlab.org/nlab/show/distributive+law

--------
复合 [M ∘ N] 是一个由分配律 [Monad_Distributes] 给出的单子：
   [ret] 是 [ret[M] ∘ pure[N]]（两个单位堆叠）并且 [bind] 使用 [mprod] 来将内部 [N] 交换到外部 [M] 之前。这是标准的“通过分配律的单子上单子”构造。
   nLab: https://ncatlab.org/nlab/show/distributive+law
*)
#[export]
Instance Compose_Monad `{Monad M} `{Applicative N}
  `{@Monad_Distributes M N} : Monad (M ∘ N) := {
  ret := λ _ x, ret[M] (pure[N] x);
  bind := λ x y m f, m >>=[M] (mprod M N ∘ ap (@pure _ _ (x → M (N y)) f));
}.

(*
The Yoneda construction [Yoneda F] is monadic whenever [F] is: this is the
   continuation-passing presentation of [F], and the isomorphism
   [Yoneda F ≅ F] (the Yoneda lemma) is a monad isomorphism, with [ret] and
   [bind] transported across it ([join] here re-flattens after the CPS apply).
   nLab: https://ncatlab.org/nlab/show/Yoneda+lemma

--------
当 [F] 是幺范畴时，Yoneda 构造 [Yoneda F] 也是幺范畴：这是 [F] 的延续传递表示，并且同构 [Yoneda F ≅ F]（Yoneda 引理）是一个幺范畴同构，[ret] 和 [bind] 通过它传递（此处 [join] 在 CPS 应用后重新扁平化）。nLab: https://ncatlab.org/nlab/show/Yoneda+lemma
*)
#[export]
Instance Yoneda_Monad `{Monad F} : Monad (Yoneda F) := {
  ret := λ _ x, λ r k, ret (k x);
  bind := λ _ _ m f, λ r k, join (m _ (λ h, f h _ k));
}.

Section Instances.

Universe d c.
Context (F : Type@{d} -> Type@{c}).
Context `{Monad F}.

(*
Every monad is a functor, with [fmap = liftM] (= bind _ (ret ∘ f)).  This
   recovers the underlying endofunctor F of the categorical monad from the
   bind/return presentation.

--------
每个单子都是一个函子，具有 [fmap = liftM] (= bind _ (ret ∘ f))。这从 bind/return 表达中恢复了范畴单子的底层自函子 F。
*)
#[export]  Instance Functor_Monad@{} : Functor F | 9 := {
  fmap := @liftM _ _
}.

(*
Every monad is applicative, with [pure = ret] (the unit η) and [ap = apM]
   (sequential application via bind).  This is the canonical Monad ⇒
   Applicative ⇒ Functor tower.
   Wikipedia: https://en.wikipedia.org/wiki/Applicative_functor

--------
每个单子都是函子应用类，具有 [pure = ret]（单位 η）和 [ap = apM]（通过 bind 的顺序应用）。这是典型的 Monad ⇒ Applicative ⇒ Functor 层次。维基百科：https://en.wikipedia.org/wiki/Applicative_functor
*)
#[export] Instance Applicative_Monad@{} : Applicative F | 9 := {
  pure := @ret _ _;
  ap := @apM _ _;
}.

End Instances.
