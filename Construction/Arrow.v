Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Comma.

Generalizable All Variables.

(** The arrow category C^→ (also written Arr(C), C², or [2, C]). *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category

   本文件给出箭头范畴：对象为底范畴的态射，态射为交换方块。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab: https://ncatlab.org/nlab/show/weak+factorization+system
   nLab: https://ncatlab.org/nlab/show/orthogonal+factorization+system
   nLab: https://ncatlab.org/nlab/show/codomain+fibration
   nLab: https://ncatlab.org/nlab/show/display+map
   nLab: https://ncatlab.org/nlab/show/adjoint+string

   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Arrow {C : Category} : Category := (Id[C] ↓ Id[C]).

Notation "C ⃗" := (@Arrow C) (at level 90) : category_scope.
