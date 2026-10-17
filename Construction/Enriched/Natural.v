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
  (* component at x: names 态射 F x ~> G x inside hom-对象 （已译） *)
  etransform (x : C) :
    I ~{K}~> @ehom K _ D (@efobj K _ C D F x) (@efobj K _ C D G x);

  (*
   本节说明 Natural 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  enaturality {x y : C} :
    ecompose ∘ (etransform y ⨂ @efmap K _ C D F x y) ∘ unit_left⁻¹
      << @ehom K _ C x y ~~>
         @ehom K _ D (@efobj K _ C D F x) (@efobj K _ C D G y) >>
    ecompose ∘ (@efmap K _ C D G x y ⨂ etransform x) ∘ unit_right⁻¹
}.

(** 本节：The componentwise setoid V-natural transformations: two transformations
 equal all components agree K. （已译） *)

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
