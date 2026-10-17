Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Semiadditive.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** * Biproducts give both a cartesian and a cocartesian structure *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Coproduct
   Book:      Mac Lane, "Categories for the Working Mathematician"

   本文件给出笛卡尔结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section BiproductCartesian.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{B : @HasBiproducts C Z}.

(** ** The cartesian structure *)

(* The product-side mediator, named so the [Cartesian] record below can be
   built as a literal rather than through [Program] obligations whose
   order is an elaboration detail. *)
Definition biproduct_fork {x y z : C} (f : x ~> y) (g : x ~> z) :
  x ~> biproduct_obj (biproduct y z) :=
  bi_pair (biproduct y z) f g.

Lemma biproduct_fork_respects (x y z : C) :
  Proper (equiv ==> equiv ==> equiv) (@biproduct_fork x y z).
Proof. apply bi_pair_respects. Qed.

(* The universal property: existence gives the two computation rules,
   uniqueness gives the converse. *)
Lemma biproduct_ump {x y z : C} (f : x ~> y) (g : x ~> z)
      (h : x ~> biproduct_obj (biproduct y z)) :
  h ≈ biproduct_fork f g
    ↔ (bi_exl (biproduct y z) ∘ h ≈ f)
    ∧ (bi_exr (biproduct y z) ∘ h ≈ g).
Proof.
  split.
  - intro Hh.
    split.
    + rewrite Hh.
      apply bi_exl_pair.
    + rewrite Hh.
      apply bi_exr_pair.
  - intros [Hl Hr].
    symmetry.
    now apply bi_pair_unique.
Qed.

(* The chosen biproduct object, its two projections and the product-side
   mediator [bi_pair] assemble into a [Cartesian] structure directly. *)
Definition biproduct_Cartesian : @Cartesian C := {|
  product_obj := fun x y => biproduct_obj (biproduct x y);
  fork := @biproduct_fork;
  exl := fun x y => bi_exl (biproduct x y);
  exr := fun x y => bi_exr (biproduct x y);
  fork_respects := biproduct_fork_respects;
  ump_products := @biproduct_ump
|}.

(** ** The cocartesian structure *)

(* Dually — and this is the half Mac Lane's roster is about — the SAME
   object with the two injections and the copairing [bi_copair] is a
   cocartesian structure.  Recall that [Cocartesian C] is notation for
   [@Cartesian (C^op)] (Structure/Cocartesian.v), so the field names
   below are the product ones read in the opposite category: [product_obj]
   is the coproduct x + y, [exl]/[exr] are [inl]/[inr], [fork] is the
   copairing ▽, and [ump_products] arrives with its composition order
   flipped, reading [h ∘ inl ≈ f] and [h ∘ inr ≈ g] in C. *)
Definition biproduct_merge {x y z : C} (f : y ~> x) (g : z ~> x) :
  biproduct_obj (biproduct y z) ~> x :=
  bi_copair (biproduct y z) f g.

Lemma biproduct_merge_respects (x y z : C) :
  Proper (equiv ==> equiv ==> equiv) (@biproduct_merge x y z).
Proof. apply bi_copair_respects. Qed.

Lemma biproduct_coump {x y z : C} (f : y ~> x) (g : z ~> x)
      (h : biproduct_obj (biproduct y z) ~> x) :
  h ≈ biproduct_merge f g
    ↔ (h ∘ bi_inl (biproduct y z) ≈ f)
    ∧ (h ∘ bi_inr (biproduct y z) ≈ g).
Proof.
  split.
  - intro Hh.
    split.
    + rewrite Hh.
      apply bi_copair_inl.
    + rewrite Hh.
      apply bi_copair_inr.
  - intros [Hl Hr].
    symmetry.
    now apply bi_copair_unique.
Qed.

(* TWO ELABORATION HAZARDS, both met and both worth recording.

   (1) A [{| … |}] literal ascribed to [@Cocartesian C] is checked field by
   field before the ascription has forced the implicit category, and
   [product_obj]'s type [obj → obj → obj] unifies that category with [C] on
   sight — [obj[C^op]] and [obj[C]] being definitionally equal but not
   syntactically so.  Every later field is then checked at [C], and [fork]
   fails with its arrows pointing the wrong way.  Naming the constructor
   and its category, [@Build_Cartesian (C^op) …], fixes the orientation.

   (2) With the orientation fixed, the OPPOSITE hazard appears in
   [product_obj]'s body: [biproduct_obj] and [biproduct] have their
   category implicit ([Arguments biproduct_obj {C Z x y} _] and
   [Arguments biproduct {C Z _} x y]), so writing them unannotated at an
   expected result type of [obj[C^op]] resolves them AT [C^op], and the
   [fork] field is then checked against a different family of biproducts
   from the one [biproduct_merge] was built over.  The two are printed
   identically — [biproduct_obj (biproduct y z)] either way — so the error
   message is unreadable.  Spelling [@biproduct_obj C Z] and
   [@biproduct C Z B] out is what pins the family. *)
Definition biproduct_Cocartesian : @Cocartesian C :=
  @Build_Cartesian (C^op)
    (fun x y => @biproduct_obj C Z x y (@biproduct C Z B x y))
    (@biproduct_merge)
    (fun x y => @bi_inl C Z x y (@biproduct C Z B x y))
    (fun x y => @bi_inr C Z x y (@biproduct C Z B x y))
    biproduct_merge_respects
    (@biproduct_coump).

(** ** Strict identifications *)

(* The product object IS the biproduct object, on the nose. *)
Example biproduct_product_obj (x y : C) :
  @product_obj C biproduct_Cartesian x y = biproduct_obj (biproduct x y) :=
  eq_refl.

(* And so is the coproduct object. *)
Example biproduct_coprod_obj (x y : C) :
  @Coprod C biproduct_Cocartesian x y = biproduct_obj (biproduct x y) :=
  eq_refl.

(* Hence the binary product and the binary coproduct are the SAME object
   — the defining feature of a biproduct, as a conversion rather than as
   prose or as a constructed isomorphism. *)
Example biproduct_prod_is_coprod (x y : C) :
  @product_obj C biproduct_Cartesian x y
    = @Coprod C biproduct_Cocartesian x y :=
  eq_refl.

(* The two mediators are the biproduct's own, definitionally. *)
Example biproduct_fork_is_pair {x y z : C} (f : x ~> y) (g : x ~> z) :
  @fork C biproduct_Cartesian x y z f g = bi_pair (biproduct y z) f g :=
  eq_refl.

Example biproduct_merge_is_copair {x y z : C} (f : y ~> x) (g : z ~> x) :
  @merge C biproduct_Cocartesian x y z f g
    = bi_copair (biproduct y z) f g :=
  eq_refl.

(* As are the four structural morphisms. *)
Example biproduct_exl_is_bi_exl (x y : C) :
  @exl C biproduct_Cartesian x y = bi_exl (biproduct x y) := eq_refl.

Example biproduct_exr_is_bi_exr (x y : C) :
  @exr C biproduct_Cartesian x y = bi_exr (biproduct x y) := eq_refl.

Example biproduct_inl_is_bi_inl (x y : C) :
  @inl C biproduct_Cocartesian x y = bi_inl (biproduct x y) := eq_refl.

Example biproduct_inr_is_bi_inr (x y : C) :
  @inr C biproduct_Cocartesian x y = bi_inr (biproduct x y) := eq_refl.

End BiproductCartesian.

(** ** The round trip against Structure/Semiadditive.v *)

(* Structure/Semiadditive.v turns a preadditive category with binary
   products into one with biproducts.  Feeding it the products this file
   derives returns the original biproduct object and the original
   projections on the nose; the injections are rebuilt as forks and are
   recovered only up to [≈]. *)
Section BiproductRoundTrip.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{P : @Preadditive C}.
Context `{B : @HasBiproducts C Z}.

Let Cart : @Cartesian C := biproduct_Cartesian.

Example biproduct_roundtrip_obj (x y : C) :
  biproduct_obj
    (@cartesian_biproduct C Z P Cart x y) = biproduct_obj (biproduct x y) :=
  eq_refl.

Example biproduct_roundtrip_exl (x y : C) :
  bi_exl (@cartesian_biproduct C Z P Cart x y) = bi_exl (biproduct x y) :=
  eq_refl.

Example biproduct_roundtrip_exr (x y : C) :
  bi_exr (@cartesian_biproduct C Z P Cart x y) = bi_exr (biproduct x y) :=
  eq_refl.

(* The injections come back only up to [≈]: the reconstruction defines
   them as [id △ 0] and [0 △ id], which are the original injections by the
   four interaction laws and product uniqueness, not by conversion. *)
Lemma biproduct_roundtrip_inl (x y : C) :
  bi_inl (@cartesian_biproduct C Z P Cart x y) ≈ bi_inl (biproduct x y).
Proof.
  exact (bi_pair_unique (biproduct x y) id zero_mor
           (bi_inl (biproduct x y))
           (bi_exl_inl (biproduct x y)) (bi_exr_inl (biproduct x y))).
Qed.

Lemma biproduct_roundtrip_inr (x y : C) :
  bi_inr (@cartesian_biproduct C Z P Cart x y) ≈ bi_inr (biproduct x y).
Proof.
  exact (bi_pair_unique (biproduct x y) zero_mor id
           (bi_inr (biproduct x y))
           (bi_exl_inr (biproduct x y)) (bi_exr_inr (biproduct x y))).
Qed.

End BiproductRoundTrip.
