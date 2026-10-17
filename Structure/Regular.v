Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Orthogonality.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Factorization.StrongEpi.

Generalizable All Variables.

(*
   nLab:      https://ncatlab.org/nlab/show/regular+category
   Wikipedia: https://en.wikipedia.org/wiki/Regular_category

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The 核 pair f : x ~> y is 拉回 f along itself: an
 对象 x ×_y x projections p1, p2 : x ×_y x ~> x satisfying
 f ∘ p1 ≈ f ∘ p2, universal among such pairs.

 nLab: https://ncatlab.org/nlab/show/核+pair（已译） *)
Definition kernel_pair {C : Category} `{H : @HasPullbacks C} {x y : C}
  (f : x ~> y) : Pullback f f := pullback f f.

(*
   nLab: https://ncatlab.org/nlab/show/regular+epimorphism

   本节说明 Regular 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record RegularEpi {C : Category} {x y : C} (f : x ~> y) := {
  regepi_dom : C;
  regepi_p1 : regepi_dom ~> x;
  regepi_p2 : regepi_dom ~> x;
  regepi_is_coeq : IsCoequalizer regepi_p1 regepi_p2 y f
}.

(* A regular 范畴: 终 对象 all pullbacks (hence all
 有限 limits), coequalizers 核 pairs, 拉回-stability of
 regular epimorphisms. Stability is phrased chosen pullbacks:
 pulling regular epimorphism f : x ~> z back along any g : y ~> z
 yields regular epimorphism x ×_z y ~> y.（已译） *)
Class Regular (C : Category) := {
  regular_terminal  : @Terminal C;
  regular_pullbacks : @HasPullbacks C;

  (* every kernel pair has a coequalizer *)
  regular_coeq {x y : C} (f : x ~> y) :
    ∃ (q : C) (e : x ~> q),
      IsCoequalizer
        (pullback_fst f f (@kernel_pair C regular_pullbacks x y f))
        (pullback_snd f f (@kernel_pair C regular_pullbacks x y f))
        q e;

  (* regular epimorphisms are stable under pullback *)
  regular_stable {x y z : C} (f : x ~> z) (g : y ~> z) :
    RegularEpi f →
    RegularEpi (pullback_snd f g (@pullback C regular_pullbacks x y z f g))
}.

#[export] Existing Instance regular_terminal.
#[export] Existing Instance regular_pullbacks.

(* Every regular epimorphism is an epimorphism: coequalizing maps are epic
   (Wikipedia: "every coequalizer is an epimorphism"). *)
Lemma regular_epi_epic {C : Category} {x y : C} (f : x ~> y) :
  RegularEpi f → Epic f.
Proof.
  intros [d p1 p2 E].
  exact (coequalizer_epic p1 p2 E).
Qed.

(*
   本节说明 Regular 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma regular_epi_strong {C : Category} {x y : C} (f : x ~> y) :
  RegularEpi f → StrongEpi f.
Proof.
  intros [d p1 p2 E].
  constructor.
  - exact (coequalizer_epic p1 p2 E).
  - intros u v m Hm.
    constructor.
    intros a b comm.
    (* 相关说明。 （已译） *)
    assert (Ha : a ∘ p1 ≈ a ∘ p2). {
      apply (@monic C u v m Hm).
      rewrite !comp_assoc.
      rewrite comm.
      rewrite <- !comp_assoc.
      rewrite (cofork E).
      reflexivity.
    }
    pose proof (coeq_desc E a Ha) as U.
    unshelve refine {| unique_obj := unique_obj U |}.
    + split.
      * (* upper triangle: the descent equation d ∘ f ≈ a *)
        exact (unique_property U).
      * (* lower triangle m ∘ d ≈ b, by cancelling the epimorphism f:
           (m ∘ d) ∘ f ≈ m ∘ (d ∘ f) ≈ m ∘ a ≈ b ∘ f. *)
        apply (@epic C x y f (coequalizer_epic p1 p2 E) v
                 (m ∘ unique_obj U) b).
        rewrite <- comp_assoc.
        rewrite (unique_property U).
        exact comm.
    + intros d' [Hd'f Hmd'].
      (* any filler satisfies d' ∘ f ≈ a, so descent uniqueness applies *)
      apply (uniqueness U).
      exact Hd'f.
Qed.

(* In regular 范畴, coequalizing map supplied [regular_coeq]
 kernel pair f itself regular epimorphism: it manifestly
 coequalizes kernel-pair projections. （已译） *)
Definition regular_epi_of_kernel_coeq {C : Category} {R : Regular C}
  {x y : C} (f : x ~> y) :
  RegularEpi (`1 (`2 (regular_coeq f))) := {|
  regepi_dom := Pull f f (kernel_pair f);
  regepi_p1  := pullback_fst f f (kernel_pair f);
  regepi_p2  := pullback_snd f f (kernel_pair f);
  regepi_is_coeq := `2 (`2 (regular_coeq f))
|}.
