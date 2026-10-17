Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Id.
Require Import Category.Functor.Structure.Monoidal.Compose.

Generalizable All Variables.

(** * Braided and symmetric monoidal functors *)

(*
   nLab: https://ncatlab.org/nlab/show/symmetric+monoidal+functor
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_functor

   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section BraidedMonoidalFunctor.

Context {C D : Category}.
Context `{BC : @BraidedMonoidal C}.
Context `{BD : @BraidedMonoidal D}.
Context {F : C ⟶ D}.

(* Lax variant: F β ∘ μ ≈ μ ∘ β over the lax tensor comparison. *)
Class BraidedLaxMonoidalFunctor : Type := {
  braided_is_lax : @LaxMonoidalFunctor C D _ _ F;

  lax_braid_compat {x y : C} :
    fmap[F] (@braid C _ x y) ∘ lax_ap
      ≈ lax_ap ∘ @braid D _ (F x) (F y)
}.
#[export] Existing Instance braided_is_lax.

Coercion braided_is_lax :
  BraidedLaxMonoidalFunctor >-> LaxMonoidalFunctor.

(* Strong variant: the same square over the invertible comparison. *)
Class BraidedMonoidalFunctor : Type := {
  braided_is_strong : @MonoidalFunctor C D _ _ F;

  braid_compat {x y : C} :
    fmap[F] (@braid C _ x y) ∘ to ap_iso
      ≈ to ap_iso ∘ @braid D _ (F x) (F y)
}.
#[export] Existing Instance braided_is_strong.

Coercion braided_is_strong :
  BraidedMonoidalFunctor >-> MonoidalFunctor.

(* A braided strong monoidal functor is in particular braided lax monoidal:
   forgetting invertibility of the comparisons preserves the compatibility
   square, since the lax comparison of [MonoidalFunctor_Is_Lax] is the [to]
   component of [ap_iso]. *)
Program Definition BraidedMonoidalFunctor_Is_Lax
  (S : BraidedMonoidalFunctor) : BraidedLaxMonoidalFunctor := {|
  braided_is_lax := MonoidalFunctor_Is_Lax braided_is_strong
|}.
Next Obligation. apply braid_compat. Qed.

End BraidedMonoidalFunctor.

Arguments BraidedLaxMonoidalFunctor {C D _ _} F.
Arguments BraidedMonoidalFunctor {C D _ _} F.

(* Over symmetric bases the braided compatibility IS the symmetric
   condition — a symmetric monoidal functor is just a braided monoidal
   functor between symmetric monoidal categories, with no new data or
   axioms (nLab: symmetric+monoidal+functor).  The braided structures are
   selected through the [symmetric_is_braided] instances. *)
Definition SymmetricMonoidalFunctor {C D : Category}
  `{@SymmetricMonoidal C} `{@SymmetricMonoidal D} (F : C ⟶ D) : Type :=
  @BraidedMonoidalFunctor C D _ _ F.

Definition SymmetricLaxMonoidalFunctor {C D : Category}
  `{@SymmetricMonoidal C} `{@SymmetricMonoidal D} (F : C ⟶ D) : Type :=
  @BraidedLaxMonoidalFunctor C D _ _ F.

(** ** The identity functor is braided monoidal *)

(* Both comparison maps of [Id_MonoidalFunctor] are identities, so the
   compatibility square degenerates to braid ∘ id ≈ id ∘ braid. *)

Section BraidedMonoidalId.

Context {C : Category}.
Context `{BC : @BraidedMonoidal C}.

#[export] Program Instance Id_BraidedMonoidalFunctor :
  BraidedMonoidalFunctor (Id[C]) := {
  braided_is_strong := Id_MonoidalFunctor
}.

#[export] Program Instance Id_BraidedLaxMonoidalFunctor :
  BraidedLaxMonoidalFunctor (Id[C]) := {
  braided_is_lax := Id_LaxMonoidalFunctor
}.

End BraidedMonoidalId.

(** ** Braided monoidal functors compose *)

(* The composite comparison of [Compose_MonoidalFunctor] is
   fmap[G] μ^F ∘ μ^G (G outer, F inner).  Its compatibility square is the
   pasting of the outer square (for G, at F x and F y) with the image
   under fmap[G] of the inner square (for F, at x and y). *)

Section BraidedMonoidalCompose.

Context {C D E : Category}.
Context `{BC : @BraidedMonoidal C}.
Context `{BD : @BraidedMonoidal D}.
Context `{BE : @BraidedMonoidal E}.
Context {G : D ⟶ E}.
Context {F : C ⟶ D}.

#[export] Program Instance Compose_BraidedMonoidalFunctor
  `{@BraidedMonoidalFunctor D E BD BE G}
  `{@BraidedMonoidalFunctor C D BC BD F} :
  BraidedMonoidalFunctor (G ◯ F) := {
  braided_is_strong := Compose_MonoidalFunctor braided_is_strong
                                               braided_is_strong
}.
Next Obligation.
  (* Goal: fmap[G] (fmap[F] braid) ∘ (fmap[G] μ^F ∘ μ^G)
             ≈ (fmap[G] μ^F ∘ μ^G) ∘ braid. *)
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  spose (@braid_compat C D BC BD F _ x y) as XF.
  rewrites.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  spose (@braid_compat D E BD BE G _ (F x) (F y)) as XG.
  rewrites.
  now rewrite comp_assoc.
Qed.

#[export] Program Instance Compose_BraidedLaxMonoidalFunctor
  `{@BraidedLaxMonoidalFunctor D E BD BE G}
  `{@BraidedLaxMonoidalFunctor C D BC BD F} :
  BraidedLaxMonoidalFunctor (G ◯ F) := {
  braided_is_lax := Compose_LaxMonoidalFunctor braided_is_lax
                                               braided_is_lax
}.
Next Obligation.
  unfold lax_ap; simpl.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  spose (@lax_braid_compat C D BC BD F _ x y) as XF.
  rewrites.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  spose (@lax_braid_compat D E BD BE G _ (F x) (F y)) as XG.
  rewrites.
  now rewrite comp_assoc.
Qed.

End BraidedMonoidalCompose.

(* The bridge packaging a symmetric (strong) monoidal functor that
   preserves the SCFA generators as a weakened Fong–Spivak hypergraph
   functor, [SymmetricMonoidalFunctor_HypergraphFunctor], lives in
   Functor/Structure/Monoidal/Hypergraph.v, keeping this class file
   independent of the Frobenius/hypergraph chain. *)
