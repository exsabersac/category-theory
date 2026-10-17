Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Hom.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Profunctor.

Generalizable All Variables.

(** Representable profunctors versus adjunctions. *)

(*
 nLab: https://ncatlab.org/nlab/show/profunctor
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   本文件给出伴随相关构造与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section RepresentableAdjunction.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

(*
   正向 direction: an 伴随 F ⊣ U transposes to a 自然 同构 of

   本节：the 可表 profunctors. Concretely we route universal-property 伴随 through 伴随_Universal_to_Hom obtain hom-bifunctor 同构 hom_adj, whose endpoints are Repr_left F Repr_right U.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition adjunction_to_repr_iso (A : F ⊣ U) :
  Repr_left F ≅[[D^op ∏ C, Sets]] Repr_right U :=
  @hom_adj C D F U (@Adjunction_Universal_to_Hom C D F U A).

(* Reverse direction: a natural isomorphism Repr_left F ≅ Repr_right U is exactly
   the datum of an Adjunction_Hom (its hom_adj field), which converts back to a
   universal-property adjunction through Adjunction_Hom_to_Universal. *)
Definition repr_iso_to_adjunction
  (iso : Repr_left F ≅[[D^op ∏ C, Sets]] Repr_right U) : F ⊣ U :=
  @Adjunction_Hom_to_Universal C D F U {| hom_adj := iso |}.

(* The representability criterion for adjunctions as a Type-valued iff (↔ is
   iffT here), bundling the two conversions above. *)
Definition representable_adjunction :
  (F ⊣ U) ↔ (Repr_left F ≅[[D^op ∏ C, Sets]] Repr_right U) :=
  (adjunction_to_repr_iso, repr_iso_to_adjunction).

End RepresentableAdjunction.
