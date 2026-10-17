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

(* * * Braided symmetric monoidal 函子 （已译） *)

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

(* 相关说明。 （已译） *)
Class BraidedMonoidalFunctor : Type := {
  braided_is_strong : @MonoidalFunctor C D _ _ F;

  braid_compat {x y : C} :
    fmap[F] (@braid C _ x y) ∘ to ap_iso
      ≈ to ap_iso ∘ @braid D _ (F x) (F y)
}.
#[export] Existing Instance braided_is_strong.

Coercion braided_is_strong :
  BraidedMonoidalFunctor >-> MonoidalFunctor.

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition BraidedMonoidalFunctor_Is_Lax
  (S : BraidedMonoidalFunctor) : BraidedLaxMonoidalFunctor := {|
  braided_is_lax := MonoidalFunctor_Is_Lax braided_is_strong
|}.
Next Obligation. apply braid_compat. Qed.

End BraidedMonoidalFunctor.

Arguments BraidedLaxMonoidalFunctor {C D _ _} F.
Arguments BraidedMonoidalFunctor {C D _ _} F.

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition SymmetricMonoidalFunctor {C D : Category}
  `{@SymmetricMonoidal C} `{@SymmetricMonoidal D} (F : C ⟶ D) : Type :=
  @BraidedMonoidalFunctor C D _ _ F.

Definition SymmetricLaxMonoidalFunctor {C D : Category}
  `{@SymmetricMonoidal C} `{@SymmetricMonoidal D} (F : C ⟶ D) : Type :=
  @BraidedLaxMonoidalFunctor C D _ _ F.

(* * ** The 恒等 函子 braided monoidal （已译） *)

(* 相关说明。 （已译） *)

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

(* * ** Braided monoidal 函子 compose （已译） *)

(*
   本节说明 Braided 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

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

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
