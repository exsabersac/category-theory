Require Import Category.Lib.

Generalizable All Variables.

(** The Semigroup 类型类 (mappend/⊗), categorical reading （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/semigroup
   Wikipedia: https://en.wikipedia.org/wiki/Semigroup

   本文件给出半群对象结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Semigroup (m : Type) := {
  mappend : m -> m -> m       (* the associative binary operation, written [⊗] *)
}.

Arguments mappend {m _ } _ _.

Infix "⊗" := mappend (at level 40).
