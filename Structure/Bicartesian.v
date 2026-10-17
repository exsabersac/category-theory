Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

Section Bicartesian.

(*
   Wikipedia: none-exists (the term appears only within related articles such

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Context {C : Category}.
Context `{@Cartesian C}.     (* finite products:   x × y, terminal 1 *)
Context `{@Cocartesian C}.   (* finite coproducts: x + y, initial  0 *)

(* Interchange of fork (△) and merge (▽): copairing two pairings equals pairing
   two copairings. Reading the four morphisms as the entries of a 2×2 matrix,
   both sides assemble the same morphism (x + w) ~> (y × z), so this is the
   "matrix transpose" / middle-four interchange of the bicartesian structure.
   The proof reduces the merge of forks to a fork of merges using [fork_comp]
   and [merge_comp], appealing to [fork_respects] both in C and dually in C^op. *)
Corollary fork_merge {x y z w : C}
          (f : x ~> y) (g : x ~> z) (h : w ~> y) (i : w ~> z) :
  (f △ g) ▽ (h △ i) ≈ (f ▽ h) △ (g ▽ i).
Proof.
  rewrite <- id_left.
  rewrite <- fork_exl_exr.
  rewrite <- fork_comp.
  apply fork_respects;
  rewrite <- merge_comp; cat;
  apply (@fork_respects (C^op)); cat.
Qed.

End Bicartesian.
