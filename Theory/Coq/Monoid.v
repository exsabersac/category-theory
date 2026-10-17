Require Import Category.Lib.
Require Import Category.Theory.Coq.Semigroup.

Generalizable All Variables.

(** The Monoid type class (mempty/mappend), with its categorical reading *)

(*
 nLab: https://ncatlab.org/nlab/show/monoid
   Wikipedia: https://en.wikipedia.org/wiki/Monoid

   本文件给出幺半范畴中的幺半群对象：乘法 μ、单位 η，以及结合律与左右单位律（插入结合子/单位子使态射可复合）。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Monoid `{Semigroup m} := {
  mempty : m                   (* the unit element, Haskell's [mempty] *)
}.

Arguments Monoid m {_}.
