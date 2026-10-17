Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Classes.
Require Import Category.Theory.Orthogonality.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Factorization.
Require Import Category.Structure.Factorization.StrongEpi.
Require Import Category.Structure.Regular.

Generalizable All Variables.

(*
   nLab:      https://ncatlab.org/nlab/show/regular+category
   Wikipedia: https://en.wikipedia.org/wiki/Regular_category

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The class regular epimorphisms, 态射 class sense of
 Theory/Morphisms/Classes.v. （已译） *)
Definition RegularEpiClass {C : Category} : MorphismClass C :=
  fun _ _ f => RegularEpi f.

(* 相关说明。 （已译） *)
Lemma is_coequalizer_respects {C : Category} {x y q : C}
  (f g : x ~> y) (e e' : y ~> q) :
  e ≈ e' → IsCoequalizer f g q e → IsCoequalizer f g q e'.
Proof.
  intros Heq E.
  unshelve refine {| cofork := _; coeq_desc := _ |}.
  - (* e' absorbs the parallel pair because e does *)
    rewrite <- Heq.
    exact (cofork E).
  - intros z h Hh.
    pose proof (coeq_desc E h Hh) as U.
    unshelve refine {| unique_obj := unique_obj U |}.
    + (* the descent across e also descends across e' *)
      rewrite <- Heq.
      exact (unique_property U).
    + intros v Hv.
      apply (uniqueness U).
      rewrite Heq.
      exact Hv.
Qed.

(* 相关说明。 （已译） *)
Lemma regular_epi_respects {C : Category} {x y : C} (f g : x ~> y) :
  f ≈ g → RegularEpi f → RegularEpi g.
Proof.
  intros Heq H.
  destruct H as [d p1 p2 E].
  exact {| regepi_dom := d
         ; regepi_p1  := p1
         ; regepi_p2  := p2
         ; regepi_is_coeq := is_coequalizer_respects p1 p2 f g Heq E |}.
Qed.

(* Being a monomorphism transports along ≈: left cancellation of g reduces
   to left cancellation of f. *)
Lemma monic_respects {C : Category} {x y : C} (f g : x ~> y) :
  f ≈ g → Monic f → Monic g.
Proof.
  intros Heq Hm.
  constructor.
  intros z g1 g2 Hgg.
  apply (@monic C x y f Hm z g1 g2).
  rewrite Heq.
  exact Hgg.
Qed.

(* Every regular epimorphism is orthogonal every monomorphism: regular
 epimorphisms are 强 ([regular_epi_strong]), strength is exactly
 唯一 lifting 性质 against monomorphisms.（已译） *)
Lemma regular_epi_mono_orthogonal {C : Category} {a b u v : C}
  (e : a ~> b) (m : u ~> v) :
  RegularEpi e → Monic m → e ⫫ m.
Proof.
  intros He Hm.
  destruct (regular_epi_strong e He) as [Hepic Hlift].
  exact (Hlift u v m Hm).
Qed.

Section RegularFactorization.

Context {C : Category}.
Context (R : Regular C).

(* 相关说明。 （已译） *)
Definition image_kernel_pair {x y : C} (f : x ~> y) : Pullback f f :=
  @kernel_pair C (@regular_pullbacks C R) x y f.

(* The image 对象 f: coequalizer kernel pair. （已译） *)
Definition image_obj {x y : C} (f : x ~> y) : C :=
  `1 (@regular_coeq C R x y f).

(* 相关说明。 （已译） *)
Definition image_epi {x y : C} (f : x ~> y) : x ~> image_obj f :=
  `1 (`2 (@regular_coeq C R x y f)).

(* 相关说明。 （已译） *)
Definition image_is_coeq {x y : C} (f : x ~> y) :
  IsCoequalizer
    (pullback_fst f f (image_kernel_pair f))
    (pullback_snd f f (image_kernel_pair f))
    (image_obj f) (image_epi f) :=
  `2 (`2 (@regular_coeq C R x y f)).

(* 相关说明。 （已译） *)
Definition image_desc {x y : C} (f : x ~> y) :
  ∃! u : image_obj f ~> y, u ∘ image_epi f ≈ f :=
  coeq_desc (image_is_coeq f) f
    (pullback_commutes f f (image_kernel_pair f)).

(* The comparison 态射 image 进入 codomain. （已译） *)
Definition image_mor {x y : C} (f : x ~> y) : image_obj f ~> y :=
  unique_obj (image_desc f).

(* The factorization equation: m ∘ e ≈ f. *)
Definition image_commutes {x y : C} (f : x ~> y) :
  image_mor f ∘ image_epi f ≈ f :=
  unique_property (image_desc f).

(* 相关说明。 （已译） *)
Definition image_epi_regular {x y : C} (f : x ~> y) :
  RegularEpi (image_epi f) :=
  @regular_epi_of_kernel_coeq C R x y f.

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma image_comparison_monic {x y : C} (f : x ~> y) : Monic (image_mor f).
Proof using C R.
  constructor.
  intros T a b Hab.
  (* (i) pull e back along a; stability covers T by a regular epi pi1 *)
  pose (P1 := @pullback C (@regular_pullbacks C R) x T (image_obj f)
                (image_epi f) a).
  pose (s1 := pullback_fst (image_epi f) a P1).
  pose (pi1 := pullback_snd (image_epi f) a P1).
  assert (Hc1 : image_epi f ∘ s1 ≈ a ∘ pi1). {
    exact (pullback_commutes (image_epi f) a P1).
  }
  assert (Hpi1 : RegularEpi pi1). {
    exact (@regular_stable C R x T (image_obj f) (image_epi f) a
             (image_epi_regular f)).
  }
  (* (ii) pull e back along b ∘ pi1; stability covers P1 by a regular
     epi pi2 *)
  pose (P2 := @pullback C (@regular_pullbacks C R) x
                (Pull (image_epi f) a P1) (image_obj f)
                (image_epi f) (b ∘ pi1)).
  pose (s2 := pullback_fst (image_epi f) (b ∘ pi1) P2).
  pose (pi2 := pullback_snd (image_epi f) (b ∘ pi1) P2).
  assert (Hc2 : image_epi f ∘ s2 ≈ (b ∘ pi1) ∘ pi2). {
    exact (pullback_commutes (image_epi f) (b ∘ pi1) P2).
  }
  assert (Hpi2 : RegularEpi pi2). {
    exact (@regular_stable C R x (Pull (image_epi f) a P1) (image_obj f)
             (image_epi f) (b ∘ pi1) (image_epi_regular f)).
  }
  (* 相关说明。 （已译） *)
  assert (Hcone : f ∘ (s1 ∘ pi2) ≈ f ∘ s2). {
    transitivity ((image_mor f ∘ image_epi f) ∘ (s1 ∘ pi2)).
    - apply compose_respects.
      + symmetry.
        exact (image_commutes f).
      + reflexivity.
    - transitivity ((image_mor f ∘ image_epi f) ∘ s2).
      + rewrite <- !comp_assoc.
        rewrite Hc2.
        rewrite (comp_assoc (image_epi f) s1 pi2).
        rewrite Hc1.
        rewrite !comp_assoc.
        rewrite Hab.
        reflexivity.
      + apply compose_respects.
        * exact (image_commutes f).
        * reflexivity.
  }
  (* 相关说明。 （已译） *)
  pose proof (ump_pullbacks f f (image_kernel_pair f) _
                (s1 ∘ pi2) s2 Hcone) as Uw.
  destruct (unique_property Uw) as [Hw1 Hw2].
  (* 相关说明。 （已译） *)
  assert (Hes : image_epi f ∘ (s1 ∘ pi2) ≈ image_epi f ∘ s2). {
    transitivity
      (image_epi f
         ∘ (pullback_fst f f (image_kernel_pair f) ∘ unique_obj Uw)).
    - apply compose_respects.
      + reflexivity.
      + symmetry.
        exact Hw1.
    - transitivity
        (image_epi f
           ∘ (pullback_snd f f (image_kernel_pair f) ∘ unique_obj Uw)).
      + rewrite !comp_assoc.
        rewrite (cofork (image_is_coeq f)).
        reflexivity.
      + apply compose_respects.
        * reflexivity.
        * exact Hw2.
  }
  (* 相关说明。 （已译） *)
  assert (Hfinal : a ∘ (pi1 ∘ pi2) ≈ b ∘ (pi1 ∘ pi2)). {
    rewrite !comp_assoc.
    rewrite <- Hc1.
    rewrite <- (comp_assoc (image_epi f) s1 pi2).
    rewrite Hes.
    exact Hc2.
  }
  (* (v) the double cover is epic, so a ≈ b *)
  assert (Hepi : Epic (pi1 ∘ pi2)). {
    apply epi_compose.
    - exact (regular_epi_epic pi1 Hpi1).
    - exact (regular_epi_epic pi2 Hpi2).
  }
  apply (@epic C _ T (pi1 ∘ pi2) Hepi (image_obj f) a b).
  exact Hfinal.
Qed.

(* 相关说明。 （已译） *)
Definition regular_factorization {x y : C} (f : x ~> y) :
  Factorization f (@RegularEpiClass C) (@MonoClass C) := {|
  fact_mid  := image_obj f;
  fact_e    := image_epi f;
  fact_e_in := image_epi_regular f;
  fact_m    := image_mor f;
  fact_m_in := image_comparison_monic f;
  fact_comm := image_commutes f
|}.

(* The (regular epi, mono) orthogonal factorization system of a regular
   category. *)
Definition Regular_OFS : OFS (@RegularEpiClass C) (@MonoClass C) := {|
  ofs_e_respects := @regular_epi_respects C;
  ofs_m_respects := @monic_respects C;
  ofs_factor     := @regular_factorization;
  ofs_orth       := @regular_epi_mono_orthogonal C
|}.

End RegularFactorization.
