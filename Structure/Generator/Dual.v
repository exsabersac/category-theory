Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Generator.
Require Import Category.Adjunction.SAFT.

Generalizable All Variables.

(*
   nLab:  https://ncatlab.org/nlab/show/separator
   nLab:  https://ncatlab.org/nlab/show/cogenerator

   本文件给出对偶形式。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Dual.

Context {C : Category}.

(** ** A cogenerating family of C^op IS a generating family of C *)

Definition gen_of_cog (G : Cogenerator (C^op)) : Generator C :=
  @Build_Generator C (cog_index G) (cog_obj G)
    (fun x y f g H => @cog_separates (C^op) G y x f g H).

Definition cog_of_gen (G : Generator C) : Cogenerator (C^op) :=
  @Build_Cogenerator (C^op) (gen_index G) (gen_obj G)
    (fun x y f g H => @gen_separates C G y x f g H).

(* Both round trips are the identity on the nose. *)
Example gen_of_cog_of_gen (G : Generator C) :
  gen_of_cog (cog_of_gen G) = G := eq_refl.

Example cog_of_gen_of_cog (G : Cogenerator (C^op)) :
  cog_of_gen (gen_of_cog G) = G := eq_refl.

(** ** The reading the SAFT header states as prose, proved both ways *)

Definition cogenerator_jointly_faithful (G : Cogenerator C) :
  JointlyFaithful (fun j : cog_index G => [Hom ─, cog_obj G j]) :=
  fun x y f g H => cog_separates G f g (fun j k => H j k).

Definition jointly_faithful_cogenerator {J : Type} (F : J -> C)
  (H : JointlyFaithful (fun j : J => [Hom ─, F j])) : Cogenerator C :=
  @Build_Cogenerator C J F (fun x y f g Hk => H y x f g (fun j k => Hk j k)).

End Dual.

(* The same pair of bridges read at the other orientation, which costs
   nothing because C^op^op is C by conversion (Construction/Opposite.v,
   the duality discipline CLAUDE.md describes).  These sit OUTSIDE the
   section above: inside it the category is a section variable and the
   two bridges cannot be instantiated at C^op until it is discharged. *)
Definition gen_op_of_cog {C : Category} (G : Cogenerator C) :
  Generator (C^op) := @gen_of_cog (C^op) G.

Definition cog_of_gen_op {C : Category} (G : Generator (C^op)) :
  Cogenerator C := @cog_of_gen (C^op) G.
