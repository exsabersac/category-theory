Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Braided.Proofs.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Structure.Monoidal.CopyDiscard.
Require Import Category.Structure.Monoidal.CopyDiscard.Proofs.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.CommutativeComonoid.
Require Import Category.Theory.Algebra.Comonoid.Hom.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

(*
    nLab:      https://ncatlab.org/nlab/show/Markov+category
    Reference: Cho & Jacobs, "Disintegration and Bayesian inversion via
    Reference: Fritz, "A synthetic approach to Markov kernels, conditional

   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------ *)

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section MidSwapCoherence.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

(* 相关说明。 （已译） *)
Lemma swap_inner_diag (x y : C) : swap_inner x x y y ≈ mid_swap_inv x y.
Proof. reflexivity. Qed.

Corollary mid_swap_inv_braid {x y : C} :
  mid_swap_inv y x ∘ braid
    ≈ (@braid C _ x y ⨂ @braid C _ x y) ∘ mid_swap_inv x y.
Proof.
  rewrite <- !swap_inner_diag.
  apply swap_inner_braid.
Qed.

Corollary mid_swap_inv_assoc {x y z : C} :
  mid_swap_inv x (y ⨂ z)
    ∘ ((id[(x ⨂ x)%object] ⨂ mid_swap_inv y z) ∘ to tensor_assoc)
    ≈ (to tensor_assoc ⨂ to tensor_assoc)
        ∘ (mid_swap_inv (x ⨂ y) z ∘ (mid_swap_inv x y ⨂ id[(z ⨂ z)%object])).
Proof.
  rewrite <- !swap_inner_diag.
  apply swap_inner_assoc.
Qed.

(* 相关说明。 （已译） *)
Corollary mid_swap_inv_unit_left {x : C} :
  (unit_left ⨂ unit_left) ∘ mid_swap_inv I x
    ∘ (unit_left⁻¹ ⨂ id[(x ⨂ x)%object])
    ≈ @unit_left C _ (x ⨂ x).
Proof.
  rewrite <- swap_inner_diag.
  apply swap_inner_unit_left.
Qed.

(* The unit coherence, right form. *)
Corollary mid_swap_inv_unit_right {x : C} :
  (unit_right ⨂ unit_right) ∘ mid_swap_inv x I
    ∘ (id[(x ⨂ x)%object] ⨂ unit_left⁻¹)
    ≈ @unit_right C _ (x ⨂ x).
Proof.
  rewrite <- swap_inner_diag.
  apply swap_inner_unit_right.
Qed.

End MidSwapCoherence.

(* ------------------------------------------------------------------ *)

(** ** Deterministic morphisms *)

Section Deterministic.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.
Context `{CD : @CopyDiscard C S}.

(* A 态射 is deterministic when it is comonoid 同态 between
 典范 copy/discard comonoids (deterministic sense of
 Fritz, Definition 10.1 arXiv:1908.07021, stated over Cho–Jacobs
 CD structure, Definition 2.2 arXiv:1709.00322).（已译） *)
Definition deterministic {x y : C} (f : x ~> y) : Type :=
  ComonoidHom (cd_comonoid x) (cd_comonoid y) f.

Lemma deterministic_id {x : C} : deterministic (id[x]).
Proof. apply ComonoidHom_id. Qed.

Lemma deterministic_comp {x y z : C} {f : y ~> z} {g : x ~> y} :
  deterministic f → deterministic g → deterministic (f ∘ g).
Proof. apply ComonoidHom_comp. Qed.

Lemma deterministic_equiv {x y : C} {f g : x ~> y} :
  f ≈ g → deterministic f → deterministic g.
Proof. apply ComonoidHom_equiv. Qed.

(*
   本节说明 Deterministic 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem copy_natural_on_deterministic {x y : C} (f : x ~> y) :
  deterministic f → copy[y] ∘ f ≈ (f ⨂ f) ∘ copy[x].
Proof. intro F. exact (@hom_delta _ _ _ _ _ _ _ F). Qed.

Theorem discard_natural_on_deterministic {x y : C} (f : x ~> y) :
  deterministic f → discard[y] ∘ f ≈ discard[x].
Proof. intro F. exact (@hom_epsilon _ _ _ _ _ _ _ F). Qed.

(* 相关说明。 （已译） *)
Lemma deterministic_tensor {x x' y y' : C} {f : x ~> y} {f' : x' ~> y'} :
  deterministic f → deterministic f' → deterministic (f ⨂ f').
Proof.
  intros [Fd Fe] [Fd' Fe'].
  split.
  - change (copy[(y ⨂ y')%object] ∘ (f ⨂ f')
              ≈ ((f ⨂ f') ⨂ (f ⨂ f')) ∘ copy[(x ⨂ x')%object]).
    rewrite !copy_tensor.
    rewrite <- comp_assoc.
    rewrite <- bimap_comp.
    rewrite Fd, Fd'.
    rewrite bimap_comp.
    rewrite comp_assoc.
    rewrite mid_swap_inv_natural.
    rewrite <- comp_assoc.
    reflexivity.
  - change (discard[(y ⨂ y')%object] ∘ (f ⨂ f')
              ≈ discard[(x ⨂ x')%object]).
    rewrite !discard_tensor.
    rewrite <- comp_assoc.
    rewrite <- bimap_comp.
    rewrite Fe, Fe'.
    reflexivity.
Qed.

(* The inverse of a deterministic isomorphism is deterministic. *)
Lemma deterministic_iso_from {x y : C} (i : x ≅ y) :
  deterministic (to i) → deterministic (i⁻¹).
Proof.
  intros [Fd Fe].
  split.
  - rewrite <- (id_left (delta[ccomon_comonoid] ∘ i⁻¹)).
    rewrite <- bimap_id_id.
    rewrite <- (iso_from_to i).
    rewrite bimap_comp.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (to i ⨂ to i)).
    rewrite <- Fd.
    rewrite <- !comp_assoc.
    rewrite iso_to_from, id_right.
    reflexivity.
  - rewrite <- Fe.
    rewrite <- comp_assoc.
    rewrite iso_to_from, id_right.
    reflexivity.
Qed.

(*
   本节说明 Deterministic 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Lemma copy_coassoc {x : C} :
  (copy[x] ⨂ id[x]) ∘ copy[x]
    ≈ tensor_assoc⁻¹ ∘ ((id[x] ⨂ copy[x]) ∘ copy[x]).
Proof.
  rewrite comp_assoc.
  exact (@delta_coassoc C _ x (cd_comonoid x)).
Qed.

(* 相关说明。 （已译） *)
Lemma copy_coassoc_to {x : C} :
  to tensor_assoc ∘ ((copy[x] ⨂ id[x]) ∘ copy[x])
    ≈ (id[x] ⨂ copy[x]) ∘ copy[x].
Proof.
  rewrite copy_coassoc.
  rewrite comp_assoc.
  now rewrite iso_to_from, id_left.
Qed.

Lemma copy_cocomm {x : C} : braid ∘ copy[x] ≈ copy[x].
Proof. exact (@delta_cocommutative_of_ccomon C S x (cd_comonoid x)). Qed.

Lemma copy_counit_left {x : C} :
  (discard[x] ⨂ id[x]) ∘ copy[x] ≈ unit_left⁻¹.
Proof. exact (@delta_counit_left C _ x (cd_comonoid x)). Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma copy_copy {x : C} :
  copy[(x ⨂ x)%object] ∘ copy[x] ≈ (copy[x] ⨂ copy[x]) ∘ copy[x].
Proof.
  rewrite copy_tensor.
  (* The α-normalized two-fold copy: all three copies pushed 进入
 right-hand nest. （已译） *)
  assert (Key : to (@tensor_assoc C _ x x (x ⨂ x)%object)
                  ∘ ((copy[x] ⨂ copy[x]) ∘ copy[x])
                  ≈ (id[x] ⨂ ((id[x] ⨂ copy[x]) ∘ copy[x])) ∘ copy[x]).
  { rewrite <- (bimap_id_left_right (copy x) (copy x)).
    rewrite <- (@bimap_id_id C C C (@tensor C _) x x).
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (to tensor_assoc)).
    rewrite <- to_tensor_assoc_natural.
    rewrite <- comp_assoc.
    rewrite copy_coassoc_to.
    rewrite comp_assoc.
    rewrite <- bimap_comp_id_left.
    reflexivity. }
  (* Its inverse form, for coming back down. *)
  assert (Key2 : (@tensor_assoc C _ x x (x ⨂ x)%object)⁻¹
                   ∘ ((id[x] ⨂ ((id[x] ⨂ copy[x]) ∘ copy[x])) ∘ copy[x])
                   ≈ (copy[x] ⨂ copy[x]) ∘ copy[x]).
  { rewrite bimap_comp_id_left.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (tensor_assoc⁻¹)).
    rewrite <- from_tensor_assoc_natural.
    rewrite bimap_id_id.
    rewrite <- comp_assoc.
    rewrite <- copy_coassoc.
    rewrite comp_assoc.
    rewrite bimap_id_left_right.
    reflexivity. }
  (* 相关说明。 （已译） *)
  assert (Inner : to (@tensor_assoc C _ x x x)
                    ∘ ((braid ⨂ id[x])
                         ∘ ((@tensor_assoc C _ x x x)⁻¹
                              ∘ ((id[x] ⨂ copy[x]) ∘ copy[x])))
                    ≈ (id[x] ⨂ copy[x]) ∘ copy[x]).
  { rewrite <- copy_coassoc.
    rewrite (comp_assoc (braid ⨂ id[x])).
    rewrite <- bimap_comp_id_right.
    rewrite copy_cocomm.
    apply copy_coassoc_to. }
  rewrite <- comp_assoc.
  unfold mid_swap_inv.
  rewrite <- !comp_assoc.
  rewrite Key.
  rewrite (comp_assoc (id[x] ⨂ (@tensor_assoc C _ x x x)⁻¹)).
  rewrite <- bimap_comp_id_left.
  rewrite (comp_assoc (id[x] ⨂ (braid ⨂ id[x]))).
  rewrite <- bimap_comp_id_left.
  rewrite (comp_assoc (id[x] ⨂ to (@tensor_assoc C _ x x x))).
  rewrite <- bimap_comp_id_left.
  rewrite Inner.
  apply Key2.
Qed.

(* 相关说明。 （已译） *)
Lemma discard_copy {x : C} :
  discard[(x ⨂ x)%object] ∘ copy[x] ≈ discard[x].
Proof.
  rewrite discard_tensor.
  rewrite <- (bimap_id_left_right (discard x) (discard x)).
  rewrite <- !comp_assoc.
  rewrite copy_counit_left.
  rewrite from_unit_left_natural.
  rewrite comp_assoc.
  rewrite iso_to_from, id_left.
  reflexivity.
Qed.

Theorem deterministic_copy {x : C} : deterministic (copy x).
Proof.
  split.
  - exact copy_copy.
  - exact discard_copy.
Qed.

(* 相关说明。 （已译） *)
Lemma copy_discard {x : C} :
  copy[I] ∘ discard[x] ≈ (discard[x] ⨂ discard[x]) ∘ copy[x].
Proof.
  rewrite copy_unit.
  rewrite <- (bimap_id_left_right (discard x) (discard x)).
  rewrite <- comp_assoc.
  rewrite copy_counit_left.
  rewrite from_unit_left_natural.
  reflexivity.
Qed.

(* 相关说明。 （已译） *)
Lemma discard_discard {x : C} :
  discard[I] ∘ discard[x] ≈ discard[x].
Proof.
  rewrite discard_unit.
  apply id_left.
Qed.

Theorem deterministic_discard {x : C} : deterministic (discard x).
Proof.
  split.
  - exact copy_discard.
  - exact discard_discard.
Qed.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)

Lemma copy_braid {x y : C} :
  copy[(y ⨂ x)%object] ∘ braid ≈ (braid ⨂ braid) ∘ copy[(x ⨂ y)%object].
Proof.
  rewrite !copy_tensor.
  rewrite <- !comp_assoc.
  rewrite bimap_braid.
  rewrite (comp_assoc (mid_swap_inv y x)).
  rewrite mid_swap_inv_braid.
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

Lemma discard_braid {x y : C} :
  discard[(y ⨂ x)%object] ∘ braid ≈ discard[(x ⨂ y)%object].
Proof.
  rewrite !discard_tensor.
  rewrite <- comp_assoc.
  rewrite bimap_braid.
  rewrite comp_assoc.
  rewrite braid_I_I.
  rewrite id_right.
  reflexivity.
Qed.

Theorem deterministic_braid {x y : C} : deterministic (@braid C _ x y).
Proof.
  split.
  - exact copy_braid.
  - exact discard_braid.
Qed.

(* Left unitor. *)

Lemma copy_unitor_left {x : C} :
  copy[x] ∘ unit_left
    ≈ (unit_left ⨂ unit_left) ∘ copy[(I ⨂ x)%object].
Proof.
  rewrite copy_tensor.
  rewrite copy_unit.
  rewrite to_unit_left_natural.
  rewrite <- (bimap_id_right_left ((@unit_left C _ I)⁻¹) (copy x)).
  rewrite !comp_assoc.
  comp_right.
  symmetry.
  apply mid_swap_inv_unit_left.
Qed.

Lemma discard_unitor_left {x : C} :
  discard[x] ∘ unit_left ≈ discard[(I ⨂ x)%object].
Proof.
  rewrite discard_tensor.
  rewrite discard_unit.
  rewrite to_unit_left_natural.
  reflexivity.
Qed.

Theorem deterministic_unit_left_to {x : C} :
  deterministic (to (@unit_left C _ x)).
Proof.
  split.
  - exact copy_unitor_left.
  - exact discard_unitor_left.
Qed.

Theorem deterministic_unit_left_from {x : C} :
  deterministic ((@unit_left C _ x)⁻¹).
Proof. exact (deterministic_iso_from _ deterministic_unit_left_to). Qed.

(* Right unitor. *)

Lemma copy_unitor_right {x : C} :
  copy[x] ∘ unit_right
    ≈ (unit_right ⨂ unit_right) ∘ copy[(x ⨂ I)%object].
Proof.
  rewrite copy_tensor.
  rewrite copy_unit.
  rewrite to_unit_right_natural.
  rewrite <- (bimap_id_left_right ((@unit_left C _ I)⁻¹) (copy x)).
  rewrite !comp_assoc.
  comp_right.
  symmetry.
  apply mid_swap_inv_unit_right.
Qed.

Lemma discard_unitor_right {x : C} :
  discard[x] ∘ unit_right ≈ discard[(x ⨂ I)%object].
Proof.
  rewrite discard_tensor.
  rewrite discard_unit.
  rewrite to_unit_right_natural.
  rewrite <- unit_identity.
  reflexivity.
Qed.

Theorem deterministic_unit_right_to {x : C} :
  deterministic (to (@unit_right C _ x)).
Proof.
  split.
  - exact copy_unitor_right.
  - exact discard_unitor_right.
Qed.

Theorem deterministic_unit_right_from {x : C} :
  deterministic ((@unit_right C _ x)⁻¹).
Proof. exact (deterministic_iso_from _ deterministic_unit_right_to). Qed.

(* 相关说明。 （已译） *)

Lemma copy_tensor_assoc {x y z : C} :
  copy[(x ⨂ (y ⨂ z))%object] ∘ to tensor_assoc
    ≈ (to tensor_assoc ⨂ to tensor_assoc) ∘ copy[((x ⨂ y) ⨂ z)%object].
Proof.
  rewrite !copy_tensor.
  assert (E1 : (copy x ⨂ (mid_swap_inv y z ∘ (copy y ⨂ copy z)))
                 ≈ (id[(x ⨂ x)%object] ⨂ mid_swap_inv y z)
                     ∘ (copy x ⨂ (copy y ⨂ copy z))).
  { rewrite <- bimap_comp.
    rewrite id_left.
    reflexivity. }
  rewrite E1; clear E1.
  assert (E2 : ((mid_swap_inv x y ∘ (copy x ⨂ copy y)) ⨂ copy z)
                 ≈ (mid_swap_inv x y ⨂ id[(z ⨂ z)%object])
                     ∘ ((copy x ⨂ copy y) ⨂ copy z)).
  { rewrite <- bimap_comp.
    rewrite id_left.
    reflexivity. }
  rewrite E2; clear E2.
  spose (to_tensor_assoc_natural (copy x) (copy y) (copy z)) as X.
  rewrite <- !comp_assoc.
  rewrite X; clear X.
  rewrite !comp_assoc.
  comp_right.
  rewrite <- !comp_assoc.
  apply mid_swap_inv_assoc.
Qed.

Lemma discard_tensor_assoc {x y z : C} :
  discard[(x ⨂ (y ⨂ z))%object] ∘ to tensor_assoc
    ≈ discard[((x ⨂ y) ⨂ z)%object].
Proof.
  rewrite !discard_tensor.
  assert (E1 : (discard x ⨂ (unit_left ∘ (discard y ⨂ discard z)))
                 ≈ (id[I] ⨂ to (@unit_left C _ I))
                     ∘ (discard x ⨂ (discard y ⨂ discard z))).
  { rewrite <- bimap_comp.
    rewrite id_left.
    reflexivity. }
  rewrite E1; clear E1.
  assert (E2 : ((unit_left ∘ (discard x ⨂ discard y)) ⨂ discard z)
                 ≈ (to (@unit_left C _ I) ⨂ id[I])
                     ∘ ((discard x ⨂ discard y) ⨂ discard z)).
  { rewrite <- bimap_comp.
    rewrite id_left.
    reflexivity. }
  rewrite E2; clear E2.
  spose (to_tensor_assoc_natural (discard x) (discard y) (discard z)) as X.
  rewrite <- !comp_assoc.
  rewrite X; clear X.
  rewrite !comp_assoc.
  comp_right.
  rewrite <- !comp_assoc.
  rewrite <- triangle_identity.
  rewrite <- unit_identity.
  reflexivity.
Qed.

Theorem deterministic_tensor_assoc_to {x y z : C} :
  deterministic (to (@tensor_assoc C _ x y z)).
Proof.
  split.
  - exact copy_tensor_assoc.
  - exact discard_tensor_assoc.
Qed.

Theorem deterministic_tensor_assoc_from {x y z : C} :
  deterministic ((@tensor_assoc C _ x y z)⁻¹).
Proof. exact (deterministic_iso_from _ deterministic_tensor_assoc_to). Qed.

(* 相关说明。 （已译） *)

Program Definition DeterministicSub : Subcategory C := {|
  sobj  := fun _ => poly_unit;
  shom  := fun x y _ _ f => deterministic f;
  scomp := fun _ _ _ _ _ _ _ _ df dg => deterministic_comp df dg;
  sid   := fun _ _ => deterministic_id
|}.

Definition Det : Category := Sub C DeterministicSub.

Lemma Det_wide : Wide C DeterministicSub.
Proof. intro x; exact ttt. Qed.

(* The 含入 Det ⟶ C generic (faithful) [Incl C DeterministicSub]
 Construction/Subcategory.v. （已译） *)

End Deterministic.
