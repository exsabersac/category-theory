Require Import Category.Lib.

Generalizable All Variables.

(** The Foldable type class (foldr), with its categorical reading *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Fold_(higher-order_function)
   nLab: https://ncatlab.org/nlab/show/monoid

   本文件给出 Foldable 相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Foldable@{d c} {F : Type@{d} → Type@{c}} :=
  foldr : ∀ {x y : Type@{d}}, (x -> y -> y) -> y -> F x -> y.
                              (* combining step, seed, container, summary *)

Arguments Foldable : clear implicits.
