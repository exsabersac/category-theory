Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.

Generalizable All Variables.

(** * The category of cones over a diagram *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Cone_(category_theory)

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Cones `(F : J ⟶ C) : Category := {|
  obj     := Cone F;
  hom     := fun N L => { u : vertex_obj[N] ~> vertex_obj[L]
                              & ∀ j, vertex_map[L] ∘ u ≈ @vertex_map _ _ _ F
                                       (@coneFrom _ _ _ N) j };
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id      := fun x => (id; _);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; _);
|}.
Next Obligation.
  rewrite comp_assoc.
  rewrite X0; auto.
Qed.

(* The category of cocones over F is dually the category of cones over the
   opposite diagram F^op : J^op ⟶ C^op: its objects are the cocones over F
   (see [Cocone]), its arrows apex maps in C^op, and its TERMINAL object is
   the colimit of F -- "initial in the category of cocones" reads as terminal
   here because the arrows run in C^op (see Cones/Limit, [Cocones_Colimit]). *)
Definition Cocones `(F : J ⟶ C) := Cones (F^op).
