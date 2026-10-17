Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Monoidal.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
   本文件为测试：ProbeSetsTerms1347。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The two constants *)

(* C1 *)
Example p1347_c1_id_right@{o h p} (x y : SetoidObject@{o p})
  (f : SetoidMorphism@{o h p} x y) :
  setoid_morphism_compose@{o h p} f (@setoid_morphism_id@{o h p} x) = f
  := eq_refl.

(* C2 *)
Example p1347_c2_id_left@{o h p} (x y : SetoidObject@{o p})
  (f : SetoidMorphism@{o h p} x y) :
  setoid_morphism_compose@{o h p} (@setoid_morphism_id@{o h p} y) f = f
  := eq_refl.

(* C3 *)
Example p1347_c3_assoc@{o h p} (w x y z : SetoidObject@{o p})
  (f : SetoidMorphism@{o h p} w x) (g : SetoidMorphism@{o h p} x y)
  (h : SetoidMorphism@{o h p} y z) :
  setoid_morphism_compose@{o h p} h (setoid_morphism_compose@{o h p} g f)
    = setoid_morphism_compose@{o h p} (setoid_morphism_compose@{o h p} h g) f
  := eq_refl.

(** ** The category [Sets] *)

(* C4 *)
Example p1347_c4_sets_id_right@{o so} (x y : Sets@{o so})
  (f : x ~{Sets@{o so}}~> y) : f ∘[Sets@{o so}] id = f := eq_refl.

(* C5 *)
Example p1347_c5_sets_id_left@{o so} (x y : Sets@{o so})
  (f : x ~{Sets@{o so}}~> y) : id ∘[Sets@{o so}] f = f := eq_refl.

(* C6 *)
Example p1347_c6_sets_assoc@{o so} (w x y z : Sets@{o so})
  (f : w ~{Sets@{o so}}~> x) (g : x ~{Sets@{o so}}~> y)
  (h : y ~{Sets@{o so}}~> z) :
  h ∘[Sets@{o so}] (g ∘[Sets@{o so}] f)
    = (h ∘[Sets@{o so}] g) ∘[Sets@{o so}] f := eq_refl.

(** ** The fields themselves *)

(* C7 *)
Example p1347_c7_id_field@{o h p} (x : SetoidObject@{o p}) (a b : x)
  (H : a ≈ b) :
  proper_morphism (@setoid_morphism_id@{o h p} x) a b H = H := eq_refl.

(* C8 *)
Example p1347_c8_compose_field@{o h p} (x y z : SetoidObject@{o p})
  (g : SetoidMorphism@{o h p} y z) (f : SetoidMorphism@{o h p} x y)
  (a b : x) (H : a ≈ b) :
  proper_morphism (setoid_morphism_compose@{o h p} g f) a b H
    = proper_morphism g _ _ (proper_morphism f a b H) := eq_refl.

(** ** The instrument *)

(* The instrument *)
Fail Example p1347_instrument@{o h p} (x : SetoidObject@{o p})
  (f : SetoidMorphism@{o h p} x x) :
  @setoid_morphism_id@{o h p} x = f := eq_refl.

(** ** Guard *)

Check Category.Instance.Sets.setoid_morphism_id.
Check Category.Instance.Sets.setoid_morphism_compose.

(* ------------------------------------------------------------------------ *)
(** ** Downstream: the free module's unit *)

(* Loaded here, after every other command, so that the modules below
   change the environment of this control alone.  They are the nine of
   Instance/Mod/Free.v's fourteen [Require] lines that the list above
   does not already load, in that file's order, and that target. *)
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.
Require Import Category.Instance.Mod.Free.

(* C9: the unit of the free-module adjunction IS the basis insertion, as
   a whole setoid morphism.  Instance/Mod/Free.v states it pointwise
   ([free_module_unit_is_insert]); the unit is the composite of
   [fmap[RMod_Forget R] id] with [fv_insert X], by that file's comment,
   and the whole equation is refused against the tree before #1347
   (measured as for C1 to C8, above). *)
Example p1347_c9_free_module_unit (R : RingObject) (X : Sets) :
  free_module_unit R X = fv_insert X := eq_refl.
