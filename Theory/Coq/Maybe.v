Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Applicative.
Require Import Category.Theory.Coq.Monad.
Require Import Category.Theory.Coq.Semigroup.
Require Import Category.Theory.Coq.Monoid.
Require Import Category.Theory.Coq.Traversable.

Generalizable All Variables.

(** The Maybe/option type [1 + a] as functor, applicative and monad *)

(*
 nLab: https://ncatlab.org/nlab/show/maybe+monad
   Wikipedia: https://en.wikipedia.org/wiki/Option_type

   本文件给出 Maybe 上的范畴论结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Notation Maybe   := option.   (* the option type [Maybe a = a + 1] *)
Notation Nothing := None.     (* [inr ()] : the absent/failure case *)
Notation Just    := Some.     (* [inl]    : injection of a value *)

Definition fromMaybe `(x : a) (my : Maybe a) : a :=
  match my with
  | Just z  => z
  | Nothing => x
  end.

(* The maybe eliminator: the copairing [[const x, f] : a + 1 → b] out of the
   coproduct [Maybe a = a + 1], sending [Just z] to [f z] and [Nothing] to [x]. *)
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

(* Monad multiplication [μ : (X + 1) + 1 → X + 1], collapsing the two copies of
   the unit [1] (both outer and inner [Nothing]) to a single [Nothing]. *)
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

(* Left-biased choice: return the first [Just], else fall through to [y].
   This is the standard [Alternative] instance, with [empty = Nothing] the unit. *)
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
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
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
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export]
Program Instance Monoid_option `{Monoid a} : Monoid (Maybe a) := {
  mempty := None
}.

(* Traversable: [sequence] commutes [Maybe] past an applicative [F], turning
   [Maybe (F x)] into [F (Maybe x)].  [Nothing] becomes [pure Nothing]; a
   [Just]-wrapped effect is run and re-wrapped with [fmap Just]. *)
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
