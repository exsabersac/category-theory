Require Import Category.Lib.

Generalizable All Variables.

(** The Functor type class (fmap), with its categorical reading *)

(*
 nLab: https://ncatlab.org/nlab/show/functor
   Wikipedia: https://en.wikipedia.org/wiki/Functor_(functional_programming)
   Wikipedia: https://en.wikipedia.org/wiki/Functor

   本文件给出函子相关定义或实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Functor@{d c} {F : Type@{d} → Type@{c}} := {
  fmap : ∀ {x y : Type@{d}}, (x → y) → F x → F y;  (* morphism map of the endofunctor F *)
}.

Arguments Functor : clear implicits.

(* The coercion lets a [Functor F] be applied directly, as in [Fobj f],
   reading off its action [fmap] on morphisms. *)
Coercion fmap : Functor >-> Funclass.

(*
   nLab: https://ncatlab.org/nlab/show/contravariant+functor
   Wikipedia: https://en.wikipedia.org/wiki/Functor#Covariance_and_contravariance

   本节说明相关定义、性质与动机。 FP reading. A contravariant 函子 equips [F : Type → Type] [contramap : (x → y) → F y → F x], which reverses direction mapped function. The laws are again identity [contramap id ≈ id] 复合 [contramap (g ∘ f) ≈ contramap f ∘ contramap g].

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class Contravariant@{d c} {F : Type@{d} → Type@{c}} :=
  contramap : ∀ {x y : Type@{d}}, (x → y) → F y → F x.  (* hom map reversing arrows *)

Arguments Contravariant : clear implicits.

Coercion contramap : Contravariant >-> Funclass.

(*
   本节说明相关定义、性质与动机。 If same [F] is both covariant contravariant, it must ignore its. argument (it is constant 函子 up iso), so any [F x] can be moved any [F y].

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition coerce `{Functor F} `{Contravariant F} {x y} : F x → F y :=
  fmap (False_rect _) ∘ contramap (False_rect _).

(*
   本节说明相关定义、性质与动机。 Haskell-style infix notation [fmap]/[contramap]. [<$>] is Haskell's. infix [fmap]; [<$] replaces all contents constant;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
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

(* The identity endofunctor [Id : Types → Types]; [fmap = id]. *)
#[export]
Instance Identity_Functor : Functor id | 9 := {
  fmap := λ _ _, id;
}.

(* The reader / function functor [λ a, x → a] (Haskell's [(->) x]).  Mapping
   post-composes, [fmap f g = f ∘ g]; this is the covariant hom functor
   [Hom(x, −)]. *)
#[export]
Instance arrow_Functor x : Functor (arrow x) := {
  fmap := λ _ _ f x r, f (x r);
}.

(* The constant functor [Const c], which sends every type to [c] and every
   morphism to the identity on [c]; [fmap] discards its function argument. *)
Inductive Const (c a : Type) := | mkConst : c → Const.

Arguments mkConst {c a} _.

#[export]
Instance Const_Functor {x : Type} : Functor (Const x) := {
  fmap := λ _ _ _ '(mkConst x), mkConst x;
}.

Import FunctorNotations.

(* Endofunctors are closed under composition: [G ∘ F] is again an endofunctor,
   with [fmap[G ∘ F] = fmap[G] ∘ fmap[F]].  (Here [F ∘ G] is function
   composition of the two type constructors.) *)
#[export]
Instance Compose_Functor `{Functor F} `{Functor G} : Functor (F ∘ G) := {
  fmap := λ _ _, fmap[F] ∘ fmap[G];
}.

(*
   nLab: https://ncatlab.org/nlab/show/Yoneda+lemma
   Wikipedia: https://en.wikipedia.org/wiki/Yoneda_lemma

   本节说明相关定义、性质与动机。 The (covariant, "co-Yoneda") presentation [F] at [x]: type 自然变换 [Hom(x, −) ⇒ F].

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Yoneda@{d c u} (F : Type@{d} → Type@{c}) (x : Type@{u}) :=
  ∀ r : Type@{u}, (x → r) → F r.

(* [Yoneda F] is itself a functor in [x], independently of whether [F] is one:
   [fmap g] precomposes the bundled continuation with [g]. *)
#[export]
Instance Yoneda_Functor (F : Type → Type) : Functor (Yoneda F) := {
  fmap := λ _ _ g k _ h, k _ (h ∘ g)
}.
