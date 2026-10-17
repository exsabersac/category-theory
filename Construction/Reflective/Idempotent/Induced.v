Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Comparison.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Idempotent.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Comonad.Core.
Require Import Category.Construction.Reflective.FixedPoints.

Generalizable All Variables.

(** * The reflection of an idempotent monad induces that monad *)

(*
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Book: Awodey, "Category Theory" (1st ed., CMU pre-print, Sept 2005),

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The unit of the induced monad is ret.  It reduces to [id ∘ ret x]. *)
Lemma idem_unit_agrees@{o h d s a | h < s +} {C : Category@{o h h}}
  {M : C ⟶ C} {MM : @Monad C M} {IM : @IdempotentMonad C M MM} (x : C) :
  @ret C _ (Adjunction_Induced_Monad
              (@idem_reflective_adj@{o h d a h s} C M MM IM)) x
    ≈ @ret C M MM x.
Proof. cbn. apply id_left. Qed.

(* The multiplication of the induced monad is join.  It reduces to
   [join x ∘ fmap[M] id]. *)
Lemma idem_join_agrees@{o h d s a | h < s +} {C : Category@{o h h}}
  {M : C ⟶ C} {MM : @Monad C M} {IM : @IdempotentMonad C M MM} (x : C) :
  @join C _ (Adjunction_Induced_Monad
               (@idem_reflective_adj@{o h d a h s} C M MM IM)) x
    ≈ @join C M MM x.
Proof. cbn. rewrite fmap_id. apply id_right. Qed.

(* The composite of the reflection is M, with identity components. *)
Theorem idem_Monad_agrees@{o h d s | h < s +} {C : Category@{o h h}}
  {M : C ⟶ C} {MM : @Monad C M} {IM : @IdempotentMonad C M MM} :
  Incl C (@MLocal_Subcategory C M MM)
    ◯ @idem_reflector@{o h d h h s} C M MM IM ≈ M.
Proof. exists (fun x => iso_id). intros x y f; cbn. cat. Qed.

(* ...and on objects it is M on the nose. *)
Example idem_factorisation_obj@{o h d s | h < s +} {C : Category@{o h h}}
  {M : C ⟶ C} {MM : @Monad C M} {IM : @IdempotentMonad C M MM} (x : C) :
  fobj[Incl C (@MLocal_Subcategory C M MM)
         ◯ @idem_reflector@{o h d h h s} C M MM IM] x = M x := eq_refl.

(* ...and on arrows: the functor equation is refused in the law fields
   alone. *)
Example idem_factorisation_fmap@{o h d s | h < s +} {C : Category@{o h h}}
  {M : C ⟶ C} {MM : @Monad C M} {IM : @IdempotentMonad C M MM} {x y : C}
  (f : x ~> y) :
  fmap[Incl C (@MLocal_Subcategory C M MM)
         ◯ @idem_reflector@{o h d h h s} C M MM IM] f = fmap[M] f := eq_refl.

(** ** The dual, as the three lemmas at C^op *)

(* The counit of the comonad induced by the coreflection is extract. *)
Definition idem_counit_agrees@{o h d s a | h < s +} {C : Category@{o h h}}
  {W : C ⟶ C} {H : @Comonad C W} {IH : IdempotentComonad W H} (x : C) :
  @ret (C^op) _ (Adjunction_Induced_Monad
                   (@idem_reflective_adj@{o h d a h s} (C^op) (W^op) H IH)) x
    ≈ @extract C W H x :=
  @idem_unit_agrees@{o h d s a} (C^op) (W^op) H IH x.

(* Its comultiplication is duplicate. *)
Definition idem_comult_agrees@{o h d s a | h < s +} {C : Category@{o h h}}
  {W : C ⟶ C} {H : @Comonad C W} {IH : IdempotentComonad W H} (x : C) :
  @join (C^op) _ (Adjunction_Induced_Monad
                    (@idem_reflective_adj@{o h d a h s} (C^op) (W^op) H IH)) x
    ≈ @duplicate C W H x :=
  @idem_join_agrees@{o h d s a} (C^op) (W^op) H IH x.

(* The composite of the coreflection is W^op, with identity components. *)
Definition idem_Comonad_agrees@{o h d s | h < s +} {C : Category@{o h h}}
  {W : C ⟶ C} {H : @Comonad C W} {IH : IdempotentComonad W H} :
  Incl (C^op) (@MLocal_Subcategory (C^op) (W^op) H)
    ◯ @idem_reflector@{o h d h h s} (C^op) (W^op) H IH ≈ W^op :=
  @idem_Monad_agrees@{o h d s} (C^op) (W^op) H IH.
