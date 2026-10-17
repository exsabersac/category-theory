Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Wedge.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** * Ends and coends *)

(*
   nLab:      https://ncatlab.org/nlab/show/end
   Wikipedia: https://en.wikipedia.org/wiki/End_(category_theory)

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class End `(F : C^op ∏ C ⟶ D) := {
  end_wedge : Wedge F;                     (* the universal wedge `(e, ω)` *)

  (* the end UMP: every wedge `W` factors uniquely through `end_wedge`, with
     `u : W ~> end_wedge` mediating in `D` and `ω_x ∘ u ≈ wedge_map[W]` *)
  ump_ends : ∀ W : Wedge F, ∃! u : W ~> end_wedge, ∀ x : C,
    wedge_map[end_wedge] ∘ u ≈ @wedge_map _ _ _ W x
}.

Arguments End {_%_category _%_category} F%_functor.
Arguments end_wedge {_%_category _%_category} F%_functor {_}.

(* An end of `F` may be used directly as its apex object of `D` (and hence,
   transitively through `Wedge`'s own coercion, as that wedge). *)
Coercion wedge_obj `(F : C^op ∏ C ⟶ D) (E : End F) := @end_wedge _ _ _ E.

Require Import Category.Functor.Opposite.

(* The COEND `∫^c F(c,c)` is the universal (initial) cowedge, dual to the end.
   As with `Cowedge` in Structure/Wedge, it is obtained as an end in the
   opposite categories: a coend for `F` is literally an end for
   `F^op : (C^op)^op ∏ C^op ⟶ D^op`, so its legs `F (x, x) ~{D}~> d` are the
   reversed wedge legs and the UMP runs `d ~> x` out of the coend. *)
Definition Coend `(F : C^op ∏ C ⟶ D) := @End (C^op) (D^op) (F^op).
