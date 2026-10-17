Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** * Semigroupoid (semicategory) *)

(*
 nLab: https://ncatlab.org/nlab/show/semicategory
   Wikipedia: https://en.wikipedia.org/wiki/Semigroupoid

   本文件给出半范畴相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Semigroupoid := {
  semi_obj : Type;                      (* collection of objects *)

  semi_uhom := Type : Type;             (* universe of hom-setoids *)
  semi_hom : semi_obj → semi_obj → semi_uhom;  (* morphisms x ~> y *)
  semi_homset : ∀ X Y, Setoid (semi_hom X Y);  (* hom is a setoid; equality is ≈ *)

  semi_compose {x y z} (f: semi_hom y z) (g : semi_hom x y) : semi_hom x z;
                                        (* composition f ∘ g (no identity) *)

  semi_compose_respects x y z :         (* compose respects ≈ (bifunctorial Proper) *)
    Proper (equiv ==> equiv ==> equiv) (@semi_compose x y z);

  semi_dom {x y} (f: semi_hom x y) := x;  (* domain (source) of a morphism *)
  semi_cod {x y} (f: semi_hom x y) := y;  (* codomain (target) of a morphism *)

  semi_comp_assoc {x y z w} (f : semi_hom z w) (g : semi_hom y z) (h : semi_hom x y) :
    semi_compose f (semi_compose g h) ≈ semi_compose (semi_compose f g) h;
                                        (* associativity *)
  semi_comp_assoc_sym {x y z w} (f : semi_hom z w) (g : semi_hom y z) (h : semi_hom x y) :
    semi_compose (semi_compose f g) h ≈ semi_compose f (semi_compose g h)
                                        (* associativity, dual form (built-in duality) *)
}.
#[export] Existing Instance semi_homset.
#[export] Existing Instance semi_compose_respects.

(* Every category is a semigroupoid: keep the objects, homs, composition and
   associativity, and simply discard the identities and unit laws. *)
Definition to_Semigroupoid (C : Category) : Semigroupoid := {|
  semi_obj              := obj;
  semi_hom              := hom;
  semi_homset           := homset;
  semi_compose          := @compose C;
  semi_compose_respects := @compose_respects C;
  semi_comp_assoc       := @comp_assoc C;
  semi_comp_assoc_sym   := @comp_assoc_sym C;
|}.

Coercion to_Semigroupoid : Category >-> Semigroupoid.
