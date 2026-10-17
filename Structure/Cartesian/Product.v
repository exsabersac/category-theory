Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Cartesian.
Require Import Category.Construction.Product.

Generalizable All Variables.

Section ProductCartesian.

Context {C : Category}.
Context {D : Category}.
Context `{@Cartesian C}.
Context `{@Cartesian D}.

(*
   nLab: https://ncatlab.org/nlab/show/functor+category
   Wikipedia: https://en.wikipedia.org/wiki/Product_category

   本文件给出积（分量）构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Instance Product_Cartesian : @Cartesian (C ∏ D) := {
  product_obj := fun x y => (fst x × fst y, snd x × snd y);  (* (c×c', d×d') *)

  fork := fun _ _ _ f g => (fst f △ fst g, snd f △ snd g);   (* pairing, componentwise *)
  exl  := fun x y => (exl, exl);                             (* left projection,  componentwise *)
  exr  := fun x y => (exr, exr)                              (* right projection, componentwise *)
}.
Next Obligation. proper; now rewrites. Qed.
Next Obligation.
  simplify; rewrites; cat;
  rewrite fork_comp; cat.
Qed.

End ProductCartesian.
