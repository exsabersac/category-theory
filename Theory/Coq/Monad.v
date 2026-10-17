Require Import Category.Lib.
Require Export Category.Theory.Coq.Applicative.

Generalizable All Variables.

(** The Monad type class (bind/return), with its categorical reading *)

(*
 nLab: https://ncatlab.org/nlab/show/monad
   nLab: https://ncatlab.org/nlab/show/Kleisli+category
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(functional_programming)
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)

   本文件给出单子相关定义或实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Monad@{d c} {F : Type@{d} → Type@{c}} := {
  ret : ∀ {x : Type@{d}}, x → F x;          (* unit η : Id ⇒ F  (Haskell return/pure) *)
  bind : ∀ {x y : Type@{d}}, F x → (x → F y) → F y;  (* Kleisli extension (Haskell >>=) *)
}.

Arguments Monad : clear implicits.

Section Monad.

Universes d c.
Context {F : Type@{d} -> Type@{c}}.
Context `{Monad F}.

(* [join] is the monad multiplication μ : F (F x) → F x.  It collapses one
   layer of structure; categorically μ = bind _ id, and FP-side
   [join m ≈ m >>= id].  nLab: https://ncatlab.org/nlab/show/monad *)
Definition join {x} (m : F (F x)) : F x := bind m id.

(*
   Kleisli (fish) 复合 (>=>): the 复合 of the Kleisli 范畴

   本节说明相关定义、性质与动机。 of [F], whose arrows x ⇒ y are functions x → F y whose identity is [ret]. Categorically [(g ∘_Kl f) = μ ∘ F(g) ∘ f]; FP-side [(f >=> g) x ≈ f x >>= g].

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition kleisli_compose {x y z : Type@{d}} `(f : x → F y) `(g : y → F z) :
  x → F z := λ x, bind (f x) g.

(* [liftM] is the functorial action fmap of [F] expressed through the monad:
   [fmap f = liftM f = bind _ (ret ∘ f)], i.e. FP-side
   [liftM f m ≈ m >>= (ret ∘ f)] (= μ ∘ F(ret ∘ f) categorically). *)
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
   [apM] is the applicative [ap] (<*>) derived from the 单子:

   本节说明相关定义、性质与动机。 [apM fM aM ≈ fM >>= (λ f, liftM f aM)]. This is canonical lax-幺半 structure every 单子 induces (see [Applicative_单子] below).

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition apM {x y : Type@{d}} (fM : F (x → y)) (aM : F x) : F y :=
  bind fM (λ f, liftM f aM).

(*
   本节说明相关定义、性质与动机。 [when]/[unless] are standard Haskell conditional combinators: run the. effect [x] when (resp. unless) guard holds, otherwise do nothing [ret tt].

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
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

(* Haskell-style [do] notation: [x <- A ;; B] desugars to [A >>= λ x, B],
   sequencing the effect [A] and binding its result to [x] in [B]. *)
Notation "x <- A ;; B" := (A >>= (λ x, B))%monad
  (at level 81, A at next level, right associativity) : monad_scope.

Notation "' pat <- A ;; B" := (A >>= (λ x, match x with pat => B end))%monad
  (at level 81, pat pattern, A at next level, right associativity) : monad_scope.

Notation "'let*' pat ':=' A 'in' B" := (@bind _ _ _ _ A (λ pat, B))
  (at level 81, pat as pattern, A at next level, right associativity) : monad_scope.

Notation "A ;; B" := (A >>= (λ _, B))%monad
  (at level 81, right associativity, only parsing) : monad_scope.

End MonadNotations.

(* The identity monad: [F = id], with [ret] and [bind] trivial.  This is the
   initial object among monads and the unit of monad composition. *)
#[export]
Instance Identity_Monad : Monad id | 9 := {
  ret := λ _ x, x;
  bind := λ _ _ m f, f m;
}.

(*
   The reader 单子 [arrow x = (x → -)]: [ret] is the constant function and

   本节说明相关定义、性质与动机。 [bind] threads shared environment [r] through both computations. It is 单子 [(x →) ⊣] currying 伴随 (functions from fixed [x]).

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export]
Instance arrow_Monad x : Monad (arrow x) := {
  ret := λ _ x _, x;
  bind := λ _ _ m f r, f (m r) r;
}.

(*
   [单子_Distributes] packages the data needed to make the 复合 [M ∘ N]

   本节：a 单子: swap/prod map [mprod : N (M (N x)) → M (N x)]. This is half 分配律 [N] over [M] sufficient [Compose_单子]; full 分配律 N ∘ M ⇒ M ∘ N (a [BeckDistributiveLaw]) is structure that guarantees 复合 is again 单子.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class Monad_Distributes (M N : Type → Type) :=
  mprod : ∀ {x}, N (M (N x)) → M (N x).

Arguments mprod M N {_ x} _.

Import MonadNotations.

Open Scope monad_scope.

(*
   The 复合 [M ∘ N] is a 单子 given a 分配律 [单子_Distributes]:

   本节说明相关定义、性质与动机。 [ret] is [ret[M] ∘ pure[N]] (both units stacked) [bind] uses [mprod] commute inner [N] past outer [M]. This is standard "单子-on-单子 via 分配律" construction.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export]
Instance Compose_Monad `{Monad M} `{Applicative N}
  `{@Monad_Distributes M N} : Monad (M ∘ N) := {
  ret := λ _ x, ret[M] (pure[N] x);
  bind := λ x y m f, m >>=[M] (mprod M N ∘ ap (@pure _ _ (x → M (N y)) f));
}.

(*
   本节说明相关定义、性质与动机。 The Yoneda construction [Yoneda F] is monadic whenever [F] is: this is the.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
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

(* Every monad is a functor, with [fmap = liftM] (= bind _ (ret ∘ f)).  This
   recovers the underlying endofunctor F of the categorical monad from the
   bind/return presentation. *)
#[export]  Instance Functor_Monad@{} : Functor F | 9 := {
  fmap := @liftM _ _
}.

(*
   Every 单子 is applicative, with [pure = ret] (the unit η) and [ap = apM]

   本节说明相关定义、性质与动机。 (sequential application via bind). This is canonical 单子 ⇒ Applicative ⇒ 函子 tower.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance Applicative_Monad@{} : Applicative F | 9 := {
  pure := @ret _ _;
  ap := @apM _ _;
}.

End Instances.
