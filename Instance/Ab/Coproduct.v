Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Biproduct.Cartesian.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Ab.
Require Import Coq.ZArith.ZArith.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.

Generalizable All Variables.

(** * The direct sum is the coproduct in Ab *)

(*
 Book: Awodey, "Category Theory" (1st ed., CMU pre-print, Sept 2005),
 Book: Riehl, "Category Theory in Context" (2nd ed.), §3.1,
 Wikipedia: https://en.wikipedia.org/wiki/Coproduct

   本文件给出余积实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The direct sum as an object of Ab *)

(* The underlying commutative monoid is [CMon_product]; all that is added
   is the componentwise negation. *)
Program Definition Ab_product (M N : AbObject) : AbObject := {|
  ab_cmon := CMon_product M N;
  ab_neg := fun p => (ab_neg M (fst p), ab_neg N (snd p))
|}.
Next Obligation.
  intros p q [H1 H2].
  split; simpl.
  - now rewrite H1.
  - now rewrite H2.
Qed.
Next Obligation.
  split; simpl; apply ab_neg_left.
Qed.

(** ** The four structural morphisms, inherited on the nose *)

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Ab_inl (M N : AbObject) : M ~{Ab}~> Ab_product M N :=
  CMon_inl M N.

Definition Ab_inr (M N : AbObject) : N ~{Ab}~> Ab_product M N :=
  CMon_inr M N.

Definition Ab_exl (M N : AbObject) : Ab_product M N ~{Ab}~> M :=
  CMon_exl M N.

Definition Ab_exr (M N : AbObject) : Ab_product M N ~{Ab}~> N :=
  CMon_exr M N.

(* The copairing (a, b) ↦ f a + g b — Awodey's formula — likewise. *)
Definition Ab_copair {M N P : AbObject}
  (f : M ~{Ab}~> P) (g : N ~{Ab}~> P) : Ab_product M N ~{Ab}~> P :=
  CMon_copair f g.

(** ** The zero morphism of Ab is CMon's *)

(*
   本节说明 Coproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example ab_zero_mor_is_cmon_zero_mor (M N : AbObject) :
  @zero_mor Ab Ab_Zero M N = @zero_mor CMon CMon_Zero M N := eq_refl.

(* Its value at a point, for readability at the use sites downstream. *)
Lemma ab_zero_mor_value (M N : AbObject) (a : carrier (cmon_setoid M)) :
  cmon_map (@zero_mor Ab Ab_Zero M N) a ≈ cmon_zero N.
Proof.
  simpl.
  apply (cmon_map_zero (Ab_zero_hom N)).
Qed.

(** ** The four interaction laws, all four inherited on the nose *)

Definition Ab_exl_inl (M N : AbObject) :
  Ab_exl M N ∘ Ab_inl M N ≈ id := CMon_exl_inl M N.

Definition Ab_exr_inr (M N : AbObject) :
  Ab_exr M N ∘ Ab_inr M N ≈ id := CMon_exr_inr M N.

Definition Ab_exl_inr (M N : AbObject) :
  Ab_exl M N ∘ Ab_inr M N ≈ @zero_mor Ab Ab_Zero N M := CMon_exl_inr M N.

Definition Ab_exr_inl (M N : AbObject) :
  Ab_exr M N ∘ Ab_inl M N ≈ @zero_mor Ab Ab_Zero M N := CMon_exr_inl M N.

(** ** Both universal properties, inherited on the nose *)

(*
   本节说明 Coproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Ab_is_product (M N P : AbObject)
  (f : P ~{Ab}~> M) (g : P ~{Ab}~> N) :
  ∃! h : P ~{Ab}~> Ab_product M N,
    (Ab_exl M N ∘ h ≈ f) ∧ (Ab_exr M N ∘ h ≈ g) :=
  CMon_bi_is_product M N P f g.

Definition Ab_is_coproduct (M N P : AbObject)
  (f : M ~{Ab}~> P) (g : N ~{Ab}~> P) :
  ∃! h : Ab_product M N ~{Ab}~> P,
    (h ∘ Ab_inl M N ≈ f) ∧ (h ∘ Ab_inr M N ≈ g) :=
  CMon_bi_is_coproduct M N P f g.

(** ** The biproduct, and with it the product and coproduct structures *)

Definition Ab_Biproduct (M N : AbObject) : @Biproduct Ab Ab_Zero M N :=
  @Build_Biproduct Ab Ab_Zero M N
    (Ab_product M N)
    (Ab_inl M N)
    (Ab_inr M N)
    (Ab_exl M N)
    (Ab_exr M N)
    (Ab_exl_inl M N)
    (Ab_exr_inr M N)
    (Ab_exl_inr M N)
    (Ab_exr_inl M N)
    (Ab_is_product M N)
    (Ab_is_coproduct M N).

#[export] Instance Ab_Biproducts : @HasBiproducts Ab Ab_Zero :=
  @Build_HasBiproducts Ab Ab_Zero Ab_Biproduct.

(* Mac Lane's roster entry.  [Cocartesian Ab] is the deliverable; the
   cartesian structure comes with it, from the same biproduct. *)
#[export] Instance Ab_Cartesian : @Cartesian Ab :=
  @biproduct_Cartesian Ab Ab_Zero Ab_Biproducts.

#[export] Instance Ab_Cocartesian : @Cocartesian Ab :=
  @biproduct_Cocartesian Ab Ab_Zero Ab_Biproducts.

(** ** Strict identifications *)

(* Awodey's Example 3.10 in one conversion: the coproduct of two abelian
   groups IS their product, the same object, not merely isomorphic to it. *)
Example Ab_coprod_is_prod (M N : AbObject) :
  @Coprod Ab Ab_Cocartesian M N = @product_obj Ab Ab_Cartesian M N :=
  eq_refl.

Example Ab_coprod_obj (M N : AbObject) :
  @Coprod Ab Ab_Cocartesian M N = Ab_product M N := eq_refl.

(* And the injections and the copairing are the concrete maps. *)
Example Ab_inl_is_pair_zero (M N : AbObject) :
  @inl Ab Ab_Cocartesian M N = CMon_inl M N := eq_refl.

Example Ab_inr_is_zero_pair (M N : AbObject) :
  @inr Ab Ab_Cocartesian M N = CMon_inr M N := eq_refl.

Example Ab_merge_is_copair (M N P : AbObject)
  (f : M ~{Ab}~> P) (g : N ~{Ab}~> P) :
  @merge Ab Ab_Cocartesian P M N f g = CMon_copair f g := eq_refl.

(* The underlying set of the coproduct is the PRODUCT of the underlying
   sets — the sentence Awodey uses to distinguish Ab from Grp. *)
Example Ab_coprod_carrier (M N : AbObject) :
  carrier (cmon_setoid (@Coprod Ab Ab_Cocartesian M N))
    = (carrier (cmon_setoid M) * carrier (cmon_setoid N))%type := eq_refl.

(** ** Non-vacuity over ℤ ⊕ ℤ *)

(*
   本节说明 Coproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ab_Z : AbObject := ring_ab Int_Ring.

(* The two injections are genuinely different maps: at the generator 1
   they land at (1, 0) and at (0, 1). *)
Lemma ab_coprod_injections_differ :
  cmon_map (@inl Ab Ab_Cocartesian ab_Z ab_Z) 1%Z
    ≈ cmon_map (@inr Ab Ab_Cocartesian ab_Z ab_Z) 1%Z → False.
Proof.
  intros [H _].
  simpl in H.
  discriminate H.
Qed.

(* And the copairing computes: with both legs the identity it is
   Awodey's (a, b) ↦ f a + g b, i.e. addition. *)
Example ab_coprod_merge_computes :
  cmon_map (@merge Ab Ab_Cocartesian ab_Z ab_Z ab_Z id id) (2%Z, 3%Z)
    = 5%Z := eq_refl.

(* The two summands are not collapsed by the copairing either: the
   projections separate them. *)
Example ab_coprod_exl_computes :
  cmon_map (Ab_exl ab_Z ab_Z) (2%Z, 3%Z) = 2%Z := eq_refl.

Example ab_coprod_exr_computes :
  cmon_map (Ab_exr ab_Z ab_Z) (2%Z, 3%Z) = 3%Z := eq_refl.
