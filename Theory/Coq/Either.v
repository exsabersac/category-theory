Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Applicative.
Require Import Category.Theory.Coq.Monad.

Generalizable All Variables.

(** The Either/sum type [a + b] bifunctor, error 单子 [b] （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/coproduct
   Wikipedia: https://en.wikipedia.org/wiki/Tagged_union

   本文件给出 Either 上的范畴论结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Notation Either := sum (only parsing).   (* [Either a b = a + b], the coproduct *)
Notation Left   := inl (only parsing).    (* [inl : a → a + b], left injection *)
Notation Right  := inr (only parsing).    (* [inr : b → a + b], right injection *)

Definition isLeft  `(x : a + b) : bool := if x then true else false.
Definition isRight `(x : a + b) : bool := if x then false else true.

(* 相关说明。 （已译） *)
Definition either `(f : a → c) `(g : b → c) (x : a + b) : c :=
  match x with
  | inl a => f a
  | inr b => g b
  end.

(*
   本节说明 Either 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition mapLeft `(f : a → c) `(x : a + b) : c + b :=
  match x with
  | inl l => inl (f l)
  | inr r => inr r
  end.

(* The 函子 [b ↦ E + b] (left summand [E] fixed): [fmap] maps over the
 [Right] value propagates [Left e] unchanged. （已译） *)
Definition Either_map {E X Y} (f : X → Y) (x : Either E X) : Either E Y :=
  match x with
  | Left e   => Left e
  | Right x' => Right (f x')
  end.

(* Applicative [ap]: [Left] either function 论元
 short-circuits [Left] (the function's [Left] taking priority). （已译） *)
Definition Either_ap {E X Y} (f : Either E (X → Y)) (x : Either E X)
  : Either E Y :=
  match f with
  | Left e   => Left e
  | Right f' => match x with
    | Left e   => Left e
    | Right x' => Right (f' x')
    end
  end.

(* The 单子 multiplication [μ : E + (E + b) → E + b], collapsing two
 copies error summand [E] (an outer inner [Left] both yield [Left]). （已译） *)
Definition Either_join {E X} (x : Either E (Either E X)) : Either E X :=
  match x with
  | Left e           => Left e
  | Right (Left e)   => Left e
  | Right (Right x') => Right x'
  end.

(* Monadic [bind] exception 单子: [Left e] short-circuits (ignoring [f]),
 [Right x'] continues [f x']. （已译） *)
Definition Either_bind {E X Y} (x : Either E X) (f : X → Either E Y) :
  Either E Y :=
  match x with
  | Left e   => Left e
  | Right x' => f x'
  end.

(* The endofunctor [b ↦ E + b] on Coq types (left summand [E] fixed). *)
#[export]
Instance Either_Functor {E} : Functor (Either E) := {
  fmap := @Either_map E
}.

(* Applicative structure; [pure = Right] injects a success value. *)
#[export]
Instance Either_Applicative {E} : Applicative (Either E) := {
  pure := @Right E;
  ap := @Either_ap E;
}.

(* The exception 单子 right 论元; unit [η = ret] [Right]. （已译） *)
#[export]
Instance Either_Monad {E} : Monad (Either E) := {
  ret := @Right E;
  bind := @Either_bind E;
}.
