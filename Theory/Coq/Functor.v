Require Import Category.Lib.

Generalizable All Variables.

(** The Functor 类型类 (fmap), categorical reading （已译） *)

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

   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class Contravariant@{d c} {F : Type@{d} → Type@{c}} :=
  contramap : ∀ {x y : Type@{d}}, (x → y) → F y → F x.  (* hom map reversing arrows *)

Arguments Contravariant : clear implicits.

Coercion contramap : Contravariant >-> Funclass.

(*
   本节说明函子、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition coerce `{Functor F} `{Contravariant F} {x y} : F x → F y :=
  fmap (False_rect _) ∘ contramap (False_rect _).

(*
   本节说明函子相关定义、性质与动机。

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

(* The reader / function 函子 [λ a, x → a] (Haskell's [(->) x]). Mapping
 post-composes, [fmap f g = f ∘ g]; 这是 covariant hom 函子
 [Hom(x, −)]. （已译） *)
#[export]
Instance arrow_Functor x : Functor (arrow x) := {
  fmap := λ _ _ f x r, f (x r);
}.

(* The 常值 函子 [Const c], sends every type [c] every
 态射 恒等 [c]; [fmap] discards function 论元. （已译） *)
Inductive Const (c a : Type) := | mkConst : c → Const.

Arguments mkConst {c a} _.

#[export]
Instance Const_Functor {x : Type} : Functor (Const x) := {
  fmap := λ _ _ _ '(mkConst x), mkConst x;
}.

Import FunctorNotations.

(* Endofunctors closed under 复合: [G ∘ F] again 自函子,
 [fmap[G ∘ F] = fmap[G] ∘ fmap[F]]. (Here [F ∘ G] function
 复合 two type constructors.) （已译） *)
#[export]
Instance Compose_Functor `{Functor F} `{Functor G} : Functor (F ∘ G) := {
  fmap := λ _ _, fmap[F] ∘ fmap[G];
}.

(*
   nLab: https://ncatlab.org/nlab/show/Yoneda+lemma
   Wikipedia: https://en.wikipedia.org/wiki/Yoneda_lemma

   本节说明自然变换、Yoneda、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Yoneda@{d c u} (F : Type@{d} → Type@{c}) (x : Type@{u}) :=
  ∀ r : Type@{u}, (x → r) → F r.

(* [Yoneda F] itself 函子 [x], independently whether [F] one:
 [fmap g] precomposes bundled continuation [g]. （已译） *)
#[export]
Instance Yoneda_Functor (F : Type → Type) : Functor (Yoneda F) := {
  fmap := λ _ _ g k _ h, k _ (h ∘ g)
}.
