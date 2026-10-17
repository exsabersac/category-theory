Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Adjunction.Map.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Morphism.
Require Import Category.Monad.Morphism.Algebra.
Require Import Category.Monad.Monadicity.BeckObjects.
Require Import Category.Monad.Monadicity.Crude.
Require Import Category.Monad.Monadicity.Beck.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Monad.Comparison.Resolution.

Generalizable All Variables.

(** * Probe for issue #482: the strength boundaries of
      Monad/Comparison/Resolution.v and the controls of
      Instance/Fun/Action/Monad/Comparison.v *)

(*
   本文件为测试：ProbeResolution482。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** The instrument *)

(* The instrument *)
Fail Check p482_absent_name.

Section EMProbe.

Context {X A : Category} {F : X ⟶ A} {G : A ⟶ X} (Adj : F ⊣ G).

Local Notation T := (Adjunction_Induced_Monad Adj).

Example C1 (x : X) :
  `1 (fobj[EM_Comparison Adj ◯ F] x) = `1 (fobj[@EM_Free X (G ◯ F) T] x)
  := eq_refl.

Example C2 (x : X) :
  t_alg[`2 (fobj[EM_Comparison Adj ◯ F] x)]
    = t_alg[`2 (fobj[@EM_Free X (G ◯ F) T] x)] := eq_refl.

Fail Example R1 (x : X) :
  fobj[EM_Comparison Adj ◯ F] x = fobj[@EM_Free X (G ◯ F) T] x := eq_refl.

Example C3 (a : A) :
  `1 (fobj[EM_Comparison_via_Lemma Adj] a) = `1 (fobj[EM_Comparison Adj] a)
  := eq_refl.

Fail Example R2a (a : A) :
  t_alg[`2 (fobj[EM_Comparison_via_Lemma Adj] a)]
    = t_alg[`2 (fobj[EM_Comparison Adj] a)] := eq_refl.

Fail Example R2 (a : A) :
  fobj[EM_Comparison_via_Lemma Adj] a = fobj[EM_Comparison Adj] a := eq_refl.

Example C4 (a : A) :
  fobj[EM_Forget (G ◯ F) ◯ EM_Comparison_via_Lemma Adj] a = fobj[G] a
  := eq_refl.

Fail Example R3 (x : X) :
  fmap[EM_Forget (G ◯ F)] (to (`1 (EM_Comparison_Free Adj) x))
    ∘ from (`1 (EM_Comparison_Forget Adj) (F x))
    = transform[mh_transform (to (EM_Comparison_theta Adj))] x := eq_refl.

Example C5 (x : X) :
  fmap[EM_Forget (G ◯ F)] (to (`1 (EM_Comparison_Free Adj) x))
    ∘ from (`1 (EM_Comparison_Forget Adj) (F x))
    = id ∘ id := eq_refl.

(* Restatements. *)

Example C6 (x : X) :
  transform[mh_transform (to (EM_Comparison_theta Adj))] x = id := eq_refl.

Example C7 (a : A) :
  `1 (EM_Comparison_Forget Adj) a = iso_id := eq_refl.

Example C8 (x : X) :
  `1 (EM_Comparison_Free Adj) x = EM_Comparison_Free_iso Adj x := eq_refl.

End EMProbe.

Section MonadProbe.

Context {X : Category} (T : X ⟶ X) `{H : @Monad X T}.

Example C9 (x : X) :
  transform[mh_transform (to (@EM_Monad_iso X T H))] x = id := eq_refl.

Example C10 (x : X) :
  transform[mh_transform (from (@EM_Monad_iso X T H))] x = id := eq_refl.

End MonadProbe.

Section LemmaProbe.

(* The object and hom levels of [Monads X], kept apart as in the target. *)
Universes m1 m2.

Context {X : Category}.
Context {A : Category} {F : X ⟶ A} {G : A ⟶ X} (Adj : F ⊣ G).
Context {A' : Category} {F' : X ⟶ A'} {G' : A' ⟶ X} (Adj' : F' ⊣ G').
Context (θ : @Isomorphism (Monads@{_ _ m1 m2} X)
               (G' ◯ F'; Adjunction_Induced_Monad Adj')
               (G ◯ F; Adjunction_Induced_Monad Adj)).
Context (CR : CreatesUSplitCoequalizers G).
Context (P : Comparison Adj Adj' θ).

Example C11 :
  wsq_K (wmap_squares Adj' Adj (Comparison_map Adj Adj' θ P))
    = cmp_functor Adj Adj' θ P := eq_refl.

Example C12 :
  wsq_L (wmap_squares Adj' Adj (Comparison_map Adj Adj' θ P)) = Id[X]
  := eq_refl.

Example C13 (a : A') : `1 (fobj[Comparison_alg Adj Adj' θ] a) = G' a
  := eq_refl.

Example C14 (a : A') :
  t_alg[`2 (fobj[Comparison_alg Adj Adj' θ] a)]
    = fmap[G'] (@counit _ _ _ _ Adj' a)
        ∘ transform[mh_transform (from θ)] (G' a) := eq_refl.

Example C15 (a : A') :
  fobj[Comparison_functor Adj Adj' θ CR] a
    = beck_G_obj Adj CR (fobj[Comparison_alg Adj Adj' θ] a) := eq_refl.

Example C16 (a : A') :
  to (`1 (Comparison_right Adj Adj' θ CR) a)
    = beck_to Adj CR (fobj[Comparison_alg Adj Adj' θ] a) := eq_refl.

Example C17 (a : A') :
  from (`1 (Comparison_right Adj Adj' θ CR) a)
    = fmap[G] (beck_e Adj CR (fobj[Comparison_alg Adj Adj' θ] a))
        ∘ @unit _ _ _ _ Adj (G' a) := eq_refl.

End LemmaProbe.

(* ------------------------------------------------------------------------ *)
(** ** The positive controls of Instance/Fun/Action/Monad/Comparison.v *)

(*
   本节说明单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.Action.
Require Import Category.Instance.Fun.Action.Monad.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Morphism.
Require Import Category.Monad.Kleisli.
Require Import Category.Monad.Kleisli.Adjunction.
Require Import Category.Monad.Comparison.Resolution.
Require Import Category.Instance.Fun.Action.Monad.Comparison.

(* C18: at the adjunction of LZ-sets, [EM_Comparison] satisfies the first
   hypothesis that [bare_awodey_refuted] quantifies over. *)
Example C18 :
  EM_Forget (ActF LZ) ◯ EM_Comparison (MSet_adj LZ) ≈ MSet_Forget LZ :=
  EM_Comparison_Forget (MSet_adj LZ).

(* C19: and the second. *)
Example C19 :
  EM_Comparison (MSet_adj LZ) ◯ MSet_Free LZ ≈ EM_Free (ActF LZ) :=
  EM_Comparison_Free (MSet_adj LZ).

(* C20: a comparison over the identity identification exists there. *)
Definition C20 :
  Comparison (@EM_Adjunction Sets (ActF LZ) (ActMonad LZ)) (MSet_adj LZ)
    (EM_Comparison_theta (MSet_adj LZ)) :=
  EM_Comparison_Comparison (MSet_adj LZ).

(* C21: and the Lemma's uniqueness applies to it. *)
Definition C21 : cmp_functor _ _ _ C20 ≈ EM_Comparison (MSet_adj LZ) :=
  EM_Comparison_unique (MSet_adj LZ) C20.

(* C22: [K_forget_components] restated. *)
Example C22 (A : MSetoidAction LZ) : `1 K_forget A = iso_id := eq_refl.

(* C23: [theta_sigma_component] restated. *)
Example C23 (X : SetoidObject) :
  transform[mh_transform (to theta_sigma)] X = lz_swap_first X := eq_refl.
