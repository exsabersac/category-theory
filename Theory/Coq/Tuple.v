Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Applicative.
Require Import Category.Theory.Coq.Monad.
Require Import Category.Theory.Coq.Semigroup.
Require Import Category.Theory.Coq.Monoid.

Generalizable All Variables.

(** The pair/tuple type [A * B], product (and writer-单子) reading （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/product
   nLab: https://ncatlab.org/nlab/show/writer+monad
   Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_product

   本文件给出 Tuple 上的范畴论结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Notation Tuple := prod (only parsing).

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition tuple_swap_a_bc_to_ab_c {A B C} (x : A * (B * C)) : A * B * C :=
  match x with (a, (b, c)) => ((a, b), c) end.

Definition tuple_swap_ab_c_to_a_bc {A B C} (x : A * B * C) : A * (B * C) :=
  match x with ((a, b), c) => (a, (b, c)) end.

(* 相关说明。 （已译） *)
Definition left_triple {A B C} (x : A) (y : B) (z : C) : A * B * C :=
  ((x, y), z).

Definition right_triple {A B C} (x : A) (y : B) (z : C) : A * (B * C) :=
  (x, (y, z)).

(*
   本节说明 Tuple 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition first `(f : a -> b) `(x : a * z) : b * z :=
  match x with (a, z) => (f a, z) end.

Definition second `(f : a -> b) `(x : z * a) : z * b :=
  match x with (z, b) => (z, f b) end.

(* [curry]/[uncurry] two directions product/exponential
 伴随 iso [(a * b) → c ≅ → (b → c)], 普遍性质 the
 exponential 对象 (currying). （已译） *)
Definition curry `(f : a -> b -> c) (x : (a * b)) : c :=
  match x with (a, b) => f a b end.

Definition uncurry {X Y Z} (f : X -> Y -> Z) (xy : X * Y) : Z :=
  match xy with (x, y) => f x y end.

(* [prod_map] [fmap] second-论元 函子 [(C * −)]: it maps the
 second component leaves first untouched (= [second]). （已译） *)
Definition prod_map {A B C : Type} (f : A -> B) (x : C * A) : C * B :=
  match x with (a, b) => (a, f b) end.

(* [(x * −)] Functor (自函子 fixing first component); its
 [fmap] maps second component via [prod_map]. （已译） *)
#[export]
Instance Tuple_Functor x : Functor (Tuple x) := {
  fmap := λ _ _, prod_map   (* hom map: act on the second component only *)
}.

(* The writer 单子 Applicative, available fixed component [x]
 Monoid: [pure] seeds empty log, [ap] runs both effects joins
 logs [⊗] (mappend). （已译） *)
#[export]
Instance Tuple_Applicative x `{Monoid x} : Applicative (Tuple x) := {
  pure := λ _ y, (mempty, y);                         (* empty log [mempty], value [y] *)
  ap := λ _ _ '(xf, f) '(xx, x), (xf ⊗ xx, f x);      (* combine logs, apply function *)
}.

(*
   本节说明单子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export]
Instance Tuple_Monad x `{Monoid x} : Monad (Tuple x) := {
  ret := λ _ y, (mempty, y);                                          (* unit: empty log [mempty] *)
  bind := λ _ _ '(xm, m) f, let '(xx, x) := f m in (xm ⊗ xx, x)       (* concatenate logs via [⊗] *)
}.
