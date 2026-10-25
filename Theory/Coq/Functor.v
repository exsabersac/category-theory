Require Import Category.Lib.

Generalizable All Variables.

(** The Functor type class (fmap), with its categorical reading / 函子类型类（fmap）及其范畴论解读 *)

(*
nLab: https://ncatlab.org/nlab/show/functor
   Wikipedia: https://en.wikipedia.org/wiki/Functor_(functional_programming)
   Wikipedia: https://en.wikipedia.org/wiki/Functor

   FP reading.  A functor (in the Haskell sense) is a type constructor
   [F : Type → Type] equipped with [fmap : (x → y) → F x → F y], lifting a
   function on elements to a function on the wrapped type.  It is lawful when
   it satisfies the two functor laws: identity [fmap id ≈ id] and composition
   [fmap (g ∘ f) ≈ fmap g ∘ fmap f].

   Categorical reading.  This is exactly an endofunctor on the category of
   Coq types (the "category of types", Haskell's Hask).  The object map is
   the type constructor [F] itself, and the morphism (hom) map is [fmap],
   sending a morphism [f : x → y] to [fmap f : F x → F y].  The two functor
   laws are precisely preservation of identities [F id = id] and of
   composition [F (g ∘ f) = F g ∘ F f].

   As is usual for these Coq/Haskell-style classes, the laws are NOT recorded
   as fields here; [Functor] carries only the [fmap] operation, and
   lawfulness is an obligation discharged for each concrete instance.

--------
nLab：https://ncatlab.org/nlab/show/functor
维基百科：https://en.wikipedia.org/wiki/Functor_(functional_programming)
维基百科：https://en.wikipedia.org/wiki/Functor

FP 读物。一个函子（在 Haskell 的意义上）是一个类型构造器 [F : Type → Type]，并配备了 [fmap : (x → y) → F x → F y]，将一个作用于元素的函数提升为作用于封装类型的函数。当它满足两个函子定律时，它是合法的：恒等 [fmap id ≈ id] 和组合 [fmap (g ∘ f) ≈ fmap g ∘ fmap f]。

范畴的理解。这正好是 Coq 类型范畴（“类型范畴”，Haskell 的 Hask）上的一个端函子。对象映射是类型构造器 [F] 本身，而态射（同态）映射是 [fmap]，将态射 [f : x → y] 发送为 [fmap f : F x → F y]。两个函子定律恰好是保持恒等 [F id = id] 和保持复合 [F (g ∘ f) = F g ∘ F f]。

像这些 Coq/Haskell 风格的类一样，这里的定律并没有作为字段记录；[Functor] 只包含 [fmap] 操作，而合法性是针对每个具体实例履行的义务。
*)

Class Functor@{d c} {F : Type@{d} → Type@{c}} := {
  fmap : ∀ {x y : Type@{d}}, (x → y) → F x → F y;  (* morphism map of the endofunctor F / 自函子 F 的态射映射 *)
}.

Arguments Functor : clear implicits.

(*
The coercion lets a [Functor F] be applied directly, as in [Fobj f],
   reading off its action [fmap] on morphisms.

--------
该强制转换允许直接应用 [Functor F]，就像在 [Fobj f] 中一样，读取其在态射上的作用 [fmap]。
*)
Coercion fmap : Functor >-> Funclass.

(*
nLab: https://ncatlab.org/nlab/show/contravariant+functor
   Wikipedia: https://en.wikipedia.org/wiki/Functor#Covariance_and_contravariance

   FP reading.  A contravariant functor equips [F : Type → Type] with
   [contramap : (x → y) → F y → F x], which reverses the direction of the
   mapped function.  The laws are again identity [contramap id ≈ id] and
   composition [contramap (g ∘ f) ≈ contramap f ∘ contramap g].

   Categorical reading.  This is an endofunctor [F : Types^op → Types],
   equivalently a functor out of the opposite category; [contramap f] is the
   image of [f] under that functor.  Presheaves are the paradigmatic
   example.

--------
nLab: https://ncatlab.org/nlab/show/contravariant+functor
   维基百科: https://en.wikipedia.org/wiki/Functor#Covariance_and_contravariance

   FP 阅读。一个逆变函子为 [F : Type → Type] 提供了 [contramap : (x → y) → F y → F x]，这会反转映射函数的方向。定律仍然是恒等 [contramap id ≈ id] 和组合 [contramap (g ∘ f) ≈ contramap f ∘ contramap g]。

范畴论阅读。这是一个自函子 [F : Types^op → Types]，相当于一个对偶范畴的函子；[contramap f] 是该函子下 [f] 的像。预层是典型示例。
*)
Class Contravariant@{d c} {F : Type@{d} → Type@{c}} :=
  contramap : ∀ {x y : Type@{d}}, (x → y) → F y → F x.  (* hom map reversing arrows / 家庭地图反向箭头 *)

Arguments Contravariant : clear implicits.

Coercion contramap : Contravariant >-> Funclass.

(*
If the same [F] is both covariant and contravariant, it must ignore its
   argument (it is a constant functor up to iso), so any [F x] can be moved to
   any [F y].  We route through [F False]: [contramap] with the unique map out
   of the initial type [False → x] sends [F x] to [F False], and [fmap] with
   [False → y] sends [F False] to [F y].  [False_rect : False → z] is the
   unique morphism from the initial object.

--------
如果同一个 [F] 既是协变的又是逆变的，它必须忽略它的参数（它是一个恒等函子到同构），所以任何 [F x] 都可以移动到任何 [F y]。我们通过 [F False] 路由：[contramap] 使用初始类型 [False → x] 的唯一映射将 [F x] 发送到 [F False]，而 [fmap] 使用 [False → y] 将 [F False] 发送到 [F y]。[False_rect : False → z] 是从初始对象到唯一态射。
*)
Definition coerce `{Functor F} `{Contravariant F} {x y} : F x → F y :=
  fmap (False_rect _) ∘ contramap (False_rect _).

(*
Haskell-style infix notation for [fmap]/[contramap].  [<$>] is Haskell's
   infix [fmap]; [<$] replaces all contents with a constant; [fmap[M N]]
   selects [fmap] for the composite functor [λ X, M (N X)].

--------
Haskell 风格的中缀表示法用于 [fmap]/[contramap]。[<$>] 是 Haskell 的中缀 [fmap]；[<$] 用一个常量替换所有内容；[fmap[M N] 为复合函子 [λ X, M (N X)] 选择 [fmap]。
*)
Module FunctorNotations.

Infix "<$>" := fmap
  (at level 29, left associativity, only parsing).
Infix "<$[ M ]>" := (@fmap M _ _ _)
  (at level 29, left associativity, only parsing).
Notation "x <$ m" := (fmap (const x) m)
  (at level 29, left associativity, only parsing).
Notation "x <&> f" := (fmap f x)
  (at level 29, left associativity, only parsing).

Notation "fmap[ M ]" := (@fmap M _ _ _)
  (at level 0, format "fmap[ M ]").
Notation "fmap[ M N ]" := (@fmap (λ X, M (N X)) _ _ _)
  (at level 0, format "fmap[ M  N ]").
Notation "fmap[ M N O ]" := (@fmap (λ X, M (N (O X))) _ _ _)
  (at level 0, format "fmap[ M  N  O ]").

Infix ">$<" := contramap (at level 29, left associativity, only parsing).
Notation "x >&< f" :=
  (contramap f x) (at level 29, left associativity, only parsing).

Notation "contramap[ M ]" := (@contramap M _ _ _)
  (at level 0, format "contramap[ M ]").
Notation "contramap[ M N ]" := (@contramap (λ X, M (N X)) _ _ _)
  (at level 0, format "contramap[ M  N ]").
Notation "contramap[ M N O ]" := (@contramap (λ X, M (N (O X))) _ _ _)
  (at level 0, format "contramap[ M  N  O ]").

End FunctorNotations.

(* The identity endofunctor [Id : Types → Types]; [fmap = id]. / 恒等endofunctor [Id : Types → Types]; [fmap = id]。 *)
#[export]
Instance Identity_Functor : Functor id | 9 := {
  fmap := λ _ _, id;
}.

(*
The reader / function functor [λ a, x → a] (Haskell's [(->) x]).  Mapping
   post-composes, [fmap f g = f ∘ g]; this is the covariant hom functor
   [Hom(x, −)].

--------
读者 / 函数函子 [λ a, x → a]（Haskell 的 [(->) x]）。映射在后面组合，[fmap f g = f ∘ g]；这是协变同态函子 [Hom(x, −)]。
*)
#[export]
Instance arrow_Functor x : Functor (arrow x) := {
  fmap := λ _ _ f x r, f (x r);
}.

(*
The constant functor [Const c], which sends every type to [c] and every
   morphism to the identity on [c]; [fmap] discards its function argument.

--------
常量函子 [Const c]，将每种类型发送到 [c]，并将每个态射发送到 [c] 上的恒等映射；[fmap] 丢弃其函数参数。
*)
Inductive Const (c a : Type) := | mkConst : c → Const.

Arguments mkConst {c a} _.

#[export]
Instance Const_Functor {x : Type} : Functor (Const x) := {
  fmap := λ _ _ _ '(mkConst x), mkConst x;
}.

Import FunctorNotations.

(*
Endofunctors are closed under composition: [G ∘ F] is again an endofunctor,
   with [fmap[G ∘ F] = fmap[G] ∘ fmap[F]].  (Here [F ∘ G] is function
   composition of the two type constructors.)

--------
端函子在组合下是封闭的：[G ∘ F] 仍然是一个端函子，[fmap[G ∘ F] = fmap[G] ∘ fmap[F]。 （这里 [F ∘ G] 是两个类型构造子的函数组合。）
*)
#[export]
Instance Compose_Functor `{Functor F} `{Functor G} : Functor (F ∘ G) := {
  fmap := λ _ _, fmap[F] ∘ fmap[G];
}.

(*
nLab: https://ncatlab.org/nlab/show/Yoneda+lemma
   Wikipedia: https://en.wikipedia.org/wiki/Yoneda_lemma

   The (covariant, "co-Yoneda") presentation of [F] at [x]: the type of
   natural transformations [Hom(x, −) ⇒ F].  By the Yoneda lemma this type is
   naturally isomorphic to [F x], a continuation-passing encoding of [F].

--------
nLab：https://ncatlab.org/nlab/show/Yoneda+lemma
Wikipedia：https://en.wikipedia.org/wiki/Yoneda_lemma

[F] 在 [x] 的（协变的，“co-Yoneda”）表示：自然变换 [Hom(x, −) ⇒ F] 的类型。根据 Yoneda 引理，这个类型自然同构于 [F x]，这是 [F] 的续延传递编码。
*)
Definition Yoneda@{d c u} (F : Type@{d} → Type@{c}) (x : Type@{u}) :=
  ∀ r : Type@{u}, (x → r) → F r.

(*
[Yoneda F] is itself a functor in [x], independently of whether [F] is one:
   [fmap g] precomposes the bundled continuation with [g].

--------
[Yoneda F] 本身是 [x] 中的函子，与 [F] 是否为函子无关：
   [fmap g] 将捆绑的连续操作与 [g] 进行前组合。
*)
#[export]
Instance Yoneda_Functor (F : Type → Type) : Functor (Yoneda F) := {
  fmap := λ _ _ g k _ h, k _ (h ∘ g)
}.
