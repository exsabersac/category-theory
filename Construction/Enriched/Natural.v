Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.
Require Import Category.Construction.Enriched.

Generalizable All Variables.

(** V-natural transformations between K-enriched functors. / K-增强函子之间的 V-自然变换。 *)

(*
 nLab: https://ncatlab.org/nlab/show/enriched+natural+transformation

 Given two K-enriched functors F, G : C ⟶ D between K-categories, a
 K-enriched (or V-natural) transformation σ assigns to every object x of C
 a component σ_x : I ~> (F x ⟿ G x) in K, naming an element of the hom-object
 from F x to G x.  The naturality condition is the equality of two
 K-morphisms (x ⟿ y) ~> (F x ⟿ G y): whiskering σ_y after F and whiskering
 σ_x before G must agree.  The two composites are set up over the tensor unit
 using ecompose (the enriched composition of D), with the unitors of K
 supplying the coercions that make the sources match — mirroring the
 unit_left / unit_right plumbing of eid_left / eid_right in Enriched.v.

 Taking K = Set recovers ordinary natural transformations: σ_x : I ~> (F x ⟿
 G x) picks out a morphism component, and the naturality square becomes the
 usual commuting square. 

 --------
 nLab: https://ncatlab.org/nlab/show/enriched+natural+transformation

 给定两个 K-丰富函子 F, G : C ⟶ D（它们在 K-范畴之间），一个 K-丰富（或 V-自然）变换 σ 为 C 中的每个对象 x 分配一个分量 σ_x : I ~> (F x ⟿ G x) 在 K 中，表示从 F x 到 G x 的 Hom 对象的一个元素。自然性条件是两个 K-态射 (x ⟿ y) ~> (F x ⟿ G y) 的相等性：在 F 之后的 σ_y “卷绕” 与在 G 之前的 σ_x “卷绕” 必须一致。两个复合是基于张量单位通过 ecompose（D 的丰富复合）设定的，K 的单位元提供了使源匹配的强制转换——这反映了 Enriched.v 中 eid_left / eid_right 的 unit_left / unit_right 配置。取 K = Set 可以恢复普通的自然变换：σ_x : I ~> (F x ⟿ G x) 选出一个态射分量，自然性方块变为通常的交换方块。
*)

Class EnrichedTransform {K : Category} `{@Monoidal K} {C D : Enriched K}
      (F G : EnrichedFunctor K C D) := {
  (*
 component at x: names the morphism F x ~> G x inside the hom-object 

 --------
 在 x 处的分量：命名同态对象内的态射 F x ~> G x
*)
  etransform (x : C) :
    I ~{K}~> @ehom K _ D (@efobj K _ C D F x) (@efobj K _ C D G x);

  (*
 V-naturality: the F-then-σ and σ-then-G whiskerings agree, as an
 equality of K-morphisms (x ⟿ y) ~> (F x ⟿ G y).

 Left path : coerce (x ⟿ y) to I ⨂ (x ⟿ y) via unit_left⁻¹, then tensor
 σ_y : I ~> (F y ⟿ G y) with efmap F : (x ⟿ y) ~> (F x ⟿ F y), and
 compose in D to land in (F x ⟿ G y).
 Right path: coerce (x ⟿ y) to (x ⟿ y) ⨂ I via unit_right⁻¹, then tensor
 efmap G : (x ⟿ y) ~> (G x ⟿ G y) with σ_x : I ~> (F x ⟿ G x), and
 compose in D to land in (F x ⟿ G y). 

 --------
 V-自然性：F-然后-σ 和 σ-然后-G 的搅拌是一致的，作为 K-态射 (x ⟿ y) ~> (F x ⟿ G y) 的相等。

 左路径：通过 unit_left⁻¹ 将 (x ⟿ y) 强制转换为 I ⨂ (x ⟿ y)，然后将 σ_y : I ~> (F y ⟿ G y) 与 efmap F : (x ⟿ y) ~> (F x ⟿ F y) 张量，并在 D 中组合以得到 (F x ⟿ G y)。
 右路径：通过 unit_right⁻¹ 将 (x ⟿ y) 强制转换为 (x ⟿ y) ⨂ I，然后将 efmap G : (x ⟿ y) ~> (G x ⟿ G y) 与 σ_x : I ~> (F x ⟿ G x) 张量，并在 D 中组合以得到 (F x ⟿ G y)。
*)
  enaturality {x y : C} :
    ecompose ∘ (etransform y ⨂ @efmap K _ C D F x y) ∘ unit_left⁻¹
      << @ehom K _ C x y ~~>
         @ehom K _ D (@efobj K _ C D F x) (@efobj K _ C D G y) >>
    ecompose ∘ (@efmap K _ C D G x y ⨂ etransform x) ∘ unit_right⁻¹
}.

(*
   * The componentwise setoid on V-natural transformations: two transformations
   are equal when all their components agree in K. 

   --------
   * V-自然变换上的分量集合等价：当所有分量在 K 中都相同时，两个变换相等。
*)

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
