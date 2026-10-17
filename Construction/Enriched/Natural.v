Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.
Require Import Category.Construction.Enriched.

Generalizable All Variables.

(** V-natural transformations between K-enriched functors. *)

(*
 nLab: https://ncatlab.org/nlab/show/enriched+natural+transformation

   本文件给出自然变换相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class EnrichedTransform {K : Category} `{@Monoidal K} {C D : Enriched K}
      (F G : EnrichedFunctor K C D) := {
  (* component at x: names the morphism F x ~> G x inside the hom-object *)
  etransform (x : C) :
    I ~{K}~> @ehom K _ D (@efobj K _ C D F x) (@efobj K _ C D G x);

  (* V-naturality: the F-then-σ and σ-then-G whiskerings agree, as an
     equality of K-morphisms (x ⟿ y) ~> (F x ⟿ G y).

     Left path : coerce (x ⟿ y) to I ⨂ (x ⟿ y) via unit_left⁻¹, then tensor
       σ_y : I ~> (F y ⟿ G y) with efmap F : (x ⟿ y) ~> (F x ⟿ F y), and
       compose in D to land in (F x ⟿ G y).
     Right path: coerce (x ⟿ y) to (x ⟿ y) ⨂ I via unit_right⁻¹, then tensor
       efmap G : (x ⟿ y) ~> (G x ⟿ G y) with σ_x : I ~> (F x ⟿ G x), and
       compose in D to land in (F x ⟿ G y). *)
  enaturality {x y : C} :
    ecompose ∘ (etransform y ⨂ @efmap K _ C D F x y) ∘ unit_left⁻¹
      << @ehom K _ C x y ~~>
         @ehom K _ D (@efobj K _ C D F x) (@efobj K _ C D G y) >>
    ecompose ∘ (@efmap K _ C D G x y ⨂ etransform x) ∘ unit_right⁻¹
}.

(** The componentwise setoid on V-natural transformations: two transformations
    are equal when all their components agree in K. *)

Program Definition EnrichedTransform_Setoid
        {K : Category} `{@Monoidal K} {C D : Enriched K}
        (F G : EnrichedFunctor K C D) :
  Setoid (EnrichedTransform F G) := {|
  equiv := fun σ τ =>
    ∀ x, @etransform K _ C D F G σ x ≈ @etransform K _ C D F G τ x
|}.
Next Obligation.
  constructor.
  - intros σ x; reflexivity.
  - intros σ τ Hστ x; symmetry; apply Hστ.
  - intros σ τ ρ Hστ Hτρ x;
    now transitivity (@etransform K _ C D F G τ x).
Qed.
