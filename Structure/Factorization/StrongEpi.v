Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Orthogonality.

Generalizable All Variables.

(*
   nLab:      https://ncatlab.org/nlab/show/strong+epimorphism
   Wikipedia: https://en.wikipedia.org/wiki/Epimorphism

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record StrongEpi {C : Category} {x y : C} (f : x ~> y) := {
  strong_epic : Epic f;
  strong_lift {u v : C} (m : u ~> v) : Monic m → f ⫫ m
}.

(*
   本节说明 StrongEpi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma strong_epi_compose {C : Category} {x y z : C}
  (f : y ~> z) (g : x ~> y) :
  StrongEpi f → StrongEpi g → StrongEpi (f ∘ g).
Proof.
  intros [Hfe Hfl] [Hge Hgl].
  constructor.
  - exact (epi_compose Hfe Hge).
  - intros u v m Hm.
    apply ortho_left_compose.
    + exact (Hgl _ _ m Hm).
    + exact (Hfl _ _ m Hm).
Qed.

(*
   本节说明 StrongEpi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma strong_epi_cancel {C : Category} {x y z : C}
  (f : y ~> z) (g : x ~> y) :
  StrongEpi (f ∘ g) → StrongEpi f.
Proof.
  intros [He Hl].
  constructor.
  - (* Epic f: 这是 exactly [epic_cancel] (Theory/Morphisms.v), was
 long time inlined here nowhere exposed. （已译） *)
    exact (epic_cancel He).
  - (* f ⫫ m for every monomorphism m. *)
    intros u v m Hm.
    constructor.
    intros p q comm.
    (* 相关说明。 （已译） *)
    assert (comm' : m ∘ (p ∘ g) ≈ q ∘ (f ∘ g)). {
      rewrite !comp_assoc.
      rewrite comm.
      reflexivity.
    }
    pose proof (@ortho_lift _ _ _ _ _ (f ∘ g) m (Hl _ _ m Hm)
                  (p ∘ g) q comm') as U.
    destruct (unique_property U) as [Ue Um].
    unshelve refine {| unique_obj := unique_obj U |}.
    + split.
      * (* d ∘ f ≈ p, by cancelling the monomorphism m:
           m ∘ (d ∘ f) ≈ (m ∘ d) ∘ f ≈ q ∘ f ≈ m ∘ p. *)
        apply (@monic C u v m Hm).
        rewrite comp_assoc.
        rewrite Um.
        rewrite comm.
        reflexivity.
      * exact Um.
    + intros d' [Hd'f Hmd'].
      (* 相关说明。 （已译） *)
      apply (uniqueness U).
      split.
      * rewrite comp_assoc.
        rewrite Hd'f.
        reflexivity.
      * exact Hmd'.
Qed.

(*
   本节说明 StrongEpi 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma split_epi_strong {C : Category} {x y : C} (f : x ~> y) :
  Retraction f → StrongEpi f.
Proof.
  intros Hr.
  constructor.
  - exact (retractions_are_epic _ _ f Hr).
  - intros u v m Hm.
    constructor.
    intros p q comm.
    destruct Hr as [r rcomp].
    unshelve refine {| unique_obj := p ∘ r |}.
    + split.
      * (* (p ∘ r) ∘ f ≈ p, by cancelling m:
           m ∘ ((p ∘ r) ∘ f) ≈ ((q ∘ f) ∘ r) ∘ f ≈ q ∘ f ≈ m ∘ p. *)
        apply (@monic C u v m Hm).
        rewrite !comp_assoc.
        rewrite comm.
        rewrite <- (comp_assoc q f r).
        rewrite rcomp.
        rewrite id_right.
        reflexivity.
      * (* m ∘ (p ∘ r) ≈ (q ∘ f) ∘ r ≈ q ∘ id ≈ q *)
        rewrite comp_assoc.
        rewrite comm.
        rewrite <- comp_assoc.
        rewrite rcomp.
        apply id_right.
    + intros d' [Hd'f Hmd'].
      (* Fillers are unique because m is monic: m ∘ (p ∘ r) ≈ q ≈ m ∘ d'. *)
      apply (@monic C u v m Hm).
      rewrite Hmd'.
      rewrite comp_assoc.
      rewrite comm.
      rewrite <- comp_assoc.
      rewrite rcomp.
      apply id_right.
Qed.

(* A 态射 that is both 强 epimorphism monomorphism is an
 同构: lifting 恒等 square f ∘ id ≈ id ∘ f against f
 itself (which is monic hypothesis) produces two-sided inverse.（已译） *)
Lemma strong_epi_mono_is_iso {C : Category} {x y : C} (f : x ~> y) :
  StrongEpi f → Monic f → IsIsomorphism f.
Proof.
  intros [He Hl] Hm.
  assert (comm : f ∘ id ≈ id ∘ f). {
    cat.
  }
  pose proof (@ortho_lift _ _ _ _ _ f f (Hl _ _ f Hm) id id comm) as U.
  destruct (unique_property U) as [Ul Ur].
  (* Ul : unique_obj U ∘ f ≈ id (left inverse);
     Ur : f ∘ unique_obj U ≈ id (right inverse). *)
  exact {| two_sided_inverse := unique_obj U;
           is_right_inverse  := Ur;
           is_left_inverse   := Ul |}.
Qed.
