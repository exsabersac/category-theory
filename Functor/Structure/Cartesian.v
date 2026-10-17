Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cartesian.

Generalizable All Variables.

(** Cartesian (product-preserving) functors. *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Limit_(category_theory)

   本文件给出笛卡尔结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CartesianFunctor.

Context `{F : C ⟶ D}.
Context `{@Cartesian C}.
Context `{@Cartesian D}.

Class CartesianFunctor := {
  (* the comparison iso F (x × y) ≅ F x × F y witnessing product preservation *)
  fobj_prod_iso {x y : C} : F (x × y) ≅ F x × F y;

  prod_in  := fun x y => from (@fobj_prod_iso x y);  (* φ⁻¹ : F x × F y ~> F (x × y) *)
  prod_out := fun x y => to   (@fobj_prod_iso x y);  (* φ   : F (x × y) ~> F x × F y *)

  fmap_exl {x y : C} : fmap (@exl C _ x y) ≈ exl ∘ prod_out _ _;  (* exl ∘ φ ≈ fmap exl *)
  fmap_exr {x y : C} : fmap (@exr C _ x y) ≈ exr ∘ prod_out _ _;  (* exr ∘ φ ≈ fmap exr *)

  (* F carries pairing to pairing up to φ⁻¹: fmap ⟨f, g⟩ ≈ φ⁻¹ ∘ ⟨fmap f, fmap g⟩ *)
  fmap_fork {x y z : C} (f : x ~> y) (g : x ~> z) :
    fmap (f △ g) ≈ prod_in _ _ ∘ fmap f △ fmap g
}.

Arguments prod_in {_ _ _} /.
Arguments prod_out {_ _ _} /.

Context `{@CartesianFunctor}.

Corollary prod_in_out (x y : C) :
  prod_in ∘ prod_out ≈ @id _ (F (x × y)).
Proof.
  intros.
  exact (iso_from_to fobj_prod_iso).
Qed.

#[local] Hint Rewrite @prod_in_out : functors.

Corollary prod_out_in (x y : C) :
  prod_out ∘ prod_in ≈ @id _ (F x × F y).
Proof.
  intros.
  exact (iso_to_from fobj_prod_iso).
Qed.

#[local] Hint Rewrite @prod_out_in : functors.

Corollary prod_in_inj {x y z : C} (f g : F x ~> F y × F z) :
  prod_in ∘ f ≈ prod_in ∘ g ↔ f ≈ g.
Proof.
  split; intros Hprod.
  - rewrite <- id_left.
    rewrite <- prod_out_in.
    rewrite <- comp_assoc.
    rewrite Hprod.
    rewrite comp_assoc.
    autorewrite with functors; cat.
  - subst.
    rewrite Hprod.
    reflexivity.
Qed.

Corollary prod_out_inj {x y z : C} (f g : F x ~> F (y × z)) :
  prod_out ∘ f ≈ prod_out ∘ g ↔ f ≈ g.
Proof.
  split; intros Hprod.
  - rewrite <- id_left.
    rewrite <- prod_in_out.
    rewrite <- comp_assoc.
    rewrite Hprod.
    rewrite comp_assoc.
    autorewrite with functors; cat.
  - subst.
    rewrite Hprod.
    reflexivity.
Qed.

End CartesianFunctor.

Arguments prod_in {_ _ _ _ _ _ _ _} /.
Arguments prod_out {_ _ _ _ _ _ _ _} /.

#[export] Hint Rewrite @prod_in_out : functors.
#[export] Hint Rewrite @prod_out_in : functors.

(*
   本节说明函子、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Notation "'CocartesianFunctor' F" := (@CartesianFunctor _ _ (F^op) _ _)
  (at level 9) : category_theory_scope.
Notation "@CocartesianFunctor C D F" :=
  (@CartesianFunctor (C^op) (D^op) (F^op) _ _)
  (at level 9) : category_theory_scope.
