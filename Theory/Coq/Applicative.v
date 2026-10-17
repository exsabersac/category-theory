Require Import Category.Lib.
Require Export Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Semigroup.
Require Import Category.Theory.Coq.Monoid.

Generalizable All Variables.

(** The Applicative type class (pure/ap), with its categorical reading *)

(*
 nLab: https://ncatlab.org/nlab/show/applicative+functor
   Wikipedia: https://en.wikipedia.org/wiki/Applicative_functor

   本文件给出 Applicative 相关结构及其范畴解读。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Applicative@{d c} {F : Type@{d} → Type@{c}} := {
  pure {x : Type@{d}} : x → F x;                       (* unit: injects a value (lax-monoidal η) *)
  ap {x y : Type @{d}} : F (x → y) → F x → F y;         (* application derived from the laxator μ *)
}.

Arguments Applicative : clear implicits.

(*
   本节说明 Applicative 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition liftA2 `{Applicative F} {x y z}
  (f : x → y → z) (a : F x) (b : F y) : F z :=
  ap (ap (pure f) a) b.

(*
   nLab: https://ncatlab.org/nlab/show/distributive+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Monoid_(category_theory)

   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class Alternative@{d c} {F : Type@{d} → Type@{c}} := {
  empty  {x : Type@{d}} : F x;                         (* neutral element of the [choose] monoid *)
  choose {x : Type@{d}} : F x → F x → F x;              (* binary [<|>] operation *)
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

(* The identity applicative [Id]: [pure = id] and [ap f x = f x].  As a lax
   monoidal functor it is the (strict) monoidal identity functor. *)
#[export]
Instance Identity_Applicative : Applicative id | 9 := {
  pure := λ _, id;
  ap := λ _ _ f x, f x;
}.

(*
   本节说明 Applicative 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export]
Instance arrow_Applicative x : Applicative (arrow x) := {
  pure := λ _ x _, x;
  ap := λ _ _ f x r, f r (x r);
}.

(*
   本节说明幺半结构、函子、单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export]
Instance Const_Applicative `{Monoid x} : Applicative (Const x) := {
  pure := λ _ _, mkConst mempty;
  ap := λ _ _ '(mkConst x) '(mkConst y), mkConst (x ⊗ y);
}.

(*
   本节说明单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export]
Instance Compose_Applicative `{Applicative F} `{Applicative G} :
  Applicative (F ∘ G)  := {
  pure := λ _, pure[F] ∘ pure;
  ap   := λ _ _, ap[F] ∘ ap[F] (pure ap[G])
}.

(*
   本节说明 Applicative 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export]
Instance Compose_Alternative `{Alternative F} `{Alternative G} :
  Alternative (F ∘ G) := {
  empty  := λ x, @empty F _ (G x);
  choose := λ x, @choose F _ (G x);
}.

(*
   本节说明Yoneda、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export]
Instance Yoneda_Applicative `{Applicative F} : Applicative (Yoneda F) := {
  pure := λ _ x, λ r k, pure (k x);
  ap := λ _ _ f x, λ r k, f _ (λ h, k ∘ h) <*> x _ id
}.

(* Every applicative is a functor, recovering [fmap] from [pure] and [ap] by
   [fmap f x = pure f <*> x] (the standard [Applicative ⇒ Functor] derivation).
   Categorically: a lax monoidal functor is in particular a functor. *)
Section Instances.

Universe d c.
Context (F : Type@{d} -> Type@{c}).
Context `{Applicative F}.

#[export]  Instance Functor_Applicative@{} : Functor F | 9 := {
  fmap := λ _ _ f x, ap (pure f) x
}.

End Instances.
