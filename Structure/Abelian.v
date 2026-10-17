Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Classes.
Require Import Category.Theory.Orthogonality.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Additive.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Kernel.
Require Import Category.Structure.Factorization.
Require Import Category.Structure.Factorization.StrongEpi.
Require Import Category.Structure.Regular.

Generalizable All Variables.

(** * Abelian categories *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Abelian_category

   本文件定义阿贝尔范畴：加性范畴中每个态射有核与余核，且每个单态射正规、每个满态射余正规。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   关于阿贝尔范畴的来源与用途

   nLab:      https://ncatlab.org/nlab/show/abelian+category
   Wikipedia: https://en.wikipedia.org/wiki/Grothendieck%27s_T%C3%B4hoku_paper

   本节说明阿贝尔范畴、函子、正合列相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Abelian (C : Category) := {
  abelian_additive : @Additive C;

  abelian_kernels :
    @HasKernels C (@additive_zero C abelian_additive);
  abelian_cokernels :
    @HasCokernels C (@additive_zero C abelian_additive);

  (* Every monomorphism is normal: a kernel of its chosen cokernel. *)
  abelian_monic_normal {x y : C} (f : x ~> y) :
    Monic f → IsKernel (`1 (`2 (cokernel f))) f;

  (* Every epimorphism is conormal: a cokernel of its chosen kernel. *)
  abelian_epic_normal {x y : C} (f : x ~> y) :
    Epic f → IsCokernel (`1 (`2 (kernel f))) f
}.

#[export] Existing Instance abelian_additive.
#[export] Existing Instance abelian_kernels.
#[export] Existing Instance abelian_cokernels.

Section AbelianFacts.

Context {C : Category}.
Context `{A : @Abelian C}.

(* 相关说明。 （已译） *)

(*
   本节说明 Abelian 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma monic_iff_kernel_pzero {x y : C} (f : x ~> y) :
  Monic f ↔ (∀ (z : C) (u : z ~> x), f ∘ u ≈ zero_mor → u ≈ zero_mor).
Proof.
  split.
  - intros Hm z u Hu.
    apply (@monic C x y f Hm z u zero_mor).
    rewrite Hu.
    symmetry.
    apply zero_mor_left.
  - intros H.
    constructor.
    intros z g1 g2 Hg.
    assert (Hd : f ∘ psub g1 g2 ≈ zero_mor).
    { unfold psub.
      rewrite compose_padd_left.
      rewrite compose_pneg_left.
      rewrite Hg.
      rewrite padd_pneg.
      apply pzero_zero_mor. }
    specialize (H z (psub g1 g2) Hd).
    unfold psub in H.
    apply (padd_cancel_right g1 g2 (pneg g2)).
    rewrite padd_pneg.
    rewrite H.
    symmetry.
    apply pzero_zero_mor.
Qed.

(* Dually, a morphism is epic exactly when its only vanishing test
   morphism out of its codomain is zero. *)
Lemma epic_iff_cokernel_pzero {x y : C} (f : x ~> y) :
  Epic f ↔ (∀ (z : C) (u : y ~> z), u ∘ f ≈ zero_mor → u ≈ zero_mor).
Proof.
  split.
  - intros He z u Hu.
    apply (@epic C x y f He z u zero_mor).
    rewrite Hu.
    symmetry.
    apply zero_mor_right.
  - intros H.
    constructor.
    intros z g1 g2 Hg.
    assert (Hd : psub g1 g2 ∘ f ≈ zero_mor).
    { unfold psub.
      rewrite compose_padd_right.
      rewrite compose_pneg_right.
      rewrite Hg.
      rewrite padd_pneg.
      apply pzero_zero_mor. }
    specialize (H z (psub g1 g2) Hd).
    unfold psub in H.
    apply (padd_cancel_right g1 g2 (pneg g2)).
    rewrite padd_pneg.
    rewrite H.
    symmetry.
    apply pzero_zero_mor.
Qed.

(* 相关说明。 （已译） *)

Definition abelian_coker_obj {x y : C} (f : x ~> y) : C :=
  `1 (cokernel f).

Definition abelian_coker {x y : C} (f : x ~> y) : y ~> abelian_coker_obj f :=
  `1 (`2 (cokernel f)).

Definition abelian_coker_is {x y : C} (f : x ~> y) :
  IsCokernel f (abelian_coker f) :=
  `2 (`2 (cokernel f)).

Definition abelian_kernel_obj {x y : C} (f : x ~> y) : C :=
  `1 (kernel f).

Definition abelian_kernel {x y : C} (f : x ~> y) :
  abelian_kernel_obj f ~> x :=
  `1 (`2 (kernel f)).

Definition abelian_kernel_is {x y : C} (f : x ~> y) :
  IsKernel f (abelian_kernel f) :=
  `2 (`2 (kernel f)).

(* 相关说明。 （已译） *)
Definition abelian_monic_is_kernel {x y : C} (f : x ~> y) (Hm : Monic f) :
  IsKernel (abelian_coker f) f :=
  abelian_monic_normal f Hm.

Definition abelian_epic_is_cokernel {x y : C} (f : x ~> y) (He : Epic f) :
  IsCokernel (abelian_kernel f) f :=
  abelian_epic_normal f He.

(* 相关说明。 （已译） *)
Definition abelian_image_obj {x y : C} (f : x ~> y) : C :=
  abelian_kernel_obj (abelian_coker f).

Definition abelian_image {x y : C} (f : x ~> y) :
  abelian_image_obj f ~> y :=
  abelian_kernel (abelian_coker f).

Definition abelian_image_is {x y : C} (f : x ~> y) :
  IsKernel (abelian_coker f) (abelian_image f) :=
  abelian_kernel_is (abelian_coker f).

Lemma abelian_image_monic {x y : C} (f : x ~> y) : Monic (abelian_image f).
Proof. exact (kernel_monic (abelian_image_is f)). Qed.

(* 相关说明。 （已译） *)
Definition abelian_image_med_ex {x y : C} (f : x ~> y) :
  ∃! w : x ~> abelian_image_obj f, abelian_image f ∘ w ≈ f :=
  kernel_desc (abelian_image_is f) f
    (cokernel_comp_zero (abelian_coker_is f)).

Definition abelian_image_med {x y : C} (f : x ~> y) :
  x ~> abelian_image_obj f :=
  unique_obj (abelian_image_med_ex f).

Lemma abelian_image_med_comm {x y : C} (f : x ~> y) :
  abelian_image f ∘ abelian_image_med f ≈ f.
Proof. exact (unique_property (abelian_image_med_ex f)). Qed.

(* 相关说明。 （已译） *)

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma image_mediator_epic_aux {x y : C} (f : x ~> y)
  {z : C} (t : abelian_image_obj f ~> z)
  {kt : C} (j : kt ~> abelian_image_obj f) (KJ : IsKernel t j)
  (u : x ~> kt) (Hu : j ∘ u ≈ abelian_image_med f)
  {c : C} (r : y ~> c)
  (CR : IsCokernel (abelian_image f ∘ j) r)
  (KN : IsKernel r (abelian_image f ∘ j)) :
  t ≈ zero_mor.
Proof.
  (* r absorbs f: f factors through abelian_image f ∘ j, which r
     coequalizes against zero. *)
  assert (Hrf : r ∘ f ≈ zero_mor).
  { rewrite <- (abelian_image_med_comm f).
    rewrite <- Hu.
    rewrite comp_assoc.
    rewrite comp_assoc.
    rewrite <- (comp_assoc r (abelian_image f) j).
    rewrite (cokernel_comp_zero CR).
    apply zero_mor_right. }
  (* hence r descends through the chosen cokernel of f *)
  pose proof (cokernel_desc (abelian_coker_is f) r Hrf) as S.
  (* r absorbs image 含入 well, across descent （已译） *)
  assert (Hrm : r ∘ abelian_image f ≈ zero_mor).
  { rewrite <- (unique_property S).
    rewrite <- comp_assoc.
    rewrite (kernel_comp_zero (abelian_image_is f)).
    apply zero_mor_left. }
  (* so image 含入 factors through kernel r, is
 abelian_image f ∘ j itself; cancelling monic 含入 splits j （已译） *)
  pose proof (kernel_desc KN (abelian_image f) Hrm) as V.
  assert (Hjv : j ∘ unique_obj V ≈ id).
  { apply (@monic C (abelian_image_obj f) y (abelian_image f)
             (abelian_image_monic f)).
    rewrite comp_assoc.
    rewrite (unique_property V).
    rewrite id_right.
    reflexivity. }
  (* finally, t is absorbed by its own kernel's splitting *)
  rewrite <- (id_right t).
  rewrite <- Hjv.
  rewrite comp_assoc.
  rewrite (kernel_comp_zero KJ).
  apply zero_mor_right.
Qed.

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma image_mediator_epic {x y : C} (f : x ~> y) :
  Epic (abelian_image_med f).
Proof.
  apply (snd (epic_iff_cokernel_pzero (abelian_image_med f))).
  intros z t Ht.
  destruct (kernel t) as [kt [j KJ]].
  pose proof (kernel_desc KJ (abelian_image_med f) Ht) as U.
  pose proof (monic_compose (abelian_image_monic f) (kernel_monic KJ))
    as Hmj.
  exact (image_mediator_epic_aux f t j KJ (unique_obj U)
           (unique_property U)
           (`1 (`2 (cokernel (abelian_image f ∘ j))))
           (`2 (`2 (cokernel (abelian_image f ∘ j))))
           (abelian_monic_normal (abelian_image f ∘ j) Hmj)).
Qed.

(** ** The epi–mono factorization *)

Theorem abelian_epi_mono_factorization {x y : C} (f : x ~> y) :
  ∃ (i : C) (e : x ~> i) (m : i ~> y),
    (Epic e) ∧ (Monic m) ∧ (m ∘ e ≈ f).
Proof using A C.
  exists (abelian_image_obj f), (abelian_image_med f), (abelian_image f).
  split.
  - exact (image_mediator_epic f).
  - split.
    + exact (abelian_image_monic f).
    + exact (abelian_image_med_comm f).
Qed.

(* 相关说明。 （已译） *)

(* Epimorphisms transport along ≈: rewrite inside the cancellation. *)
Lemma epic_respects_equiv {x y : C} (f g : x ~> y) :
  f ≈ g → Epic f → Epic g.
Proof.
  intros Hfg He.
  constructor.
  intros z g1 g2 Hg.
  apply (@epic C x y f He z g1 g2).
  rewrite Hfg.
  exact Hg.
Qed.

(* Monomorphisms transport along ≈, dually. *)
Lemma monic_respects_equiv {x y : C} (f g : x ~> y) :
  f ≈ g → Monic f → Monic g.
Proof.
  intros Hfg Hm.
  constructor.
  intros z g1 g2 Hg.
  apply (@monic C x y f Hm z g1 g2).
  rewrite Hfg.
  exact Hg.
Qed.

(* 相关说明。 （已译） *)
Definition abelian_factorization {x y : C} (f : x ~> y) :
  Factorization f (@EpiClass C) (@MonoClass C) := {|
  fact_mid  := abelian_image_obj f;
  fact_e    := abelian_image_med f;
  fact_e_in := image_mediator_epic f;
  fact_m    := abelian_image f;
  fact_m_in := abelian_image_monic f;
  fact_comm := abelian_image_med_comm f
|}.

(* Every epimorphism is strong: it is conormal, hence a regular
   epimorphism, hence a strong one — the Phase 8 bridge. *)
Lemma abelian_epic_strong {x y : C} (f : x ~> y) :
  Epic f → StrongEpi f.
Proof using A C.
  intros He.
  apply regular_epi_strong.
  exact (cokernel_regular_epi (abelian_epic_normal f He)).
Qed.

(* Epimorphisms lift uniquely against monomorphisms. *)
Lemma abelian_epi_mono_ortho {a b u v : C} (e : a ~> b) (m : u ~> v) :
  Epic e → Monic m → e ⫫ m.
Proof using A C.
  intros He Hm.
  destruct (abelian_epic_strong e He) as [He' Hlift].
  exact (Hlift _ _ m Hm).
Qed.

(* The (Epi, Mono) orthogonal factorization system on an abelian
   category. *)
Definition Abelian_OFS : OFS (@EpiClass C) (@MonoClass C) := {|
  ofs_e_respects := fun x y f g Hfg He => epic_respects_equiv f g Hfg He;
  ofs_m_respects := fun x y f g Hfg Hm => monic_respects_equiv f g Hfg Hm;
  ofs_factor     := fun x y f => abelian_factorization f;
  ofs_orth       := fun a b u v e m He Hm => abelian_epi_mono_ortho e m He Hm
|}.

End AbelianFacts.
