Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Epi.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Theory.Universal.Element.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 nLab: https://ncatlab.org/nlab/show/isomorphism+theorem
 Wikipedia: https://en.wikipedia.org/wiki/Isomorphism_theorems

   本文件给出同构相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition ImageSub {G K : GrpObject} (h : G ~{Grp}~> K) : Subgroup K :=
  {| sub_mem := GrpImage h
   ; sub_resp := GrpImage_respects h
   ; sub_unit := GrpImage_unit h
   ; sub_mul := GrpImage_mul h
   ; sub_inv := GrpImage_inv h |}.

Definition ImageGrp {G K : GrpObject} (h : G ~{Grp}~> K) : GrpObject :=
  SubgroupGrp (ImageSub h).

(* 相关说明。 （已译） *)
Program Definition image_cores {G K : GrpObject} (h : G ~{Grp}~> K) :
  G ~{Grp}~> ImageGrp h := {|
  grp_map := {| morphism := fun a : carrier G =>
                  existT _ (grp_map h a) (existT _ a (reflexivity _)) |}
|}.
Next Obligation. intros G K h a b Hab; simpl; now rewrite Hab. Qed.
Next Obligation. intros G K h; simpl; apply (grp_map_unit h). Qed.
Next Obligation. intros G K h a b; simpl; apply (grp_map_mul h). Qed.

(* The 含入 image recovers h: triangle
 h = (im h ↪ K) ∘ (G ↠ im h) holds pointwise reflexivity, the
 corestriction changing no element. （已译） *)
Lemma image_factors {G K : GrpObject} (h : G ~{Grp}~> K) :
  sub_incl (ImageSub h) ∘ image_cores h ≈ h.
Proof. intro a; simpl; reflexivity. Qed.

(* The corestriction is surjective, by construction. *)
Lemma image_cores_surjective {G K : GrpObject} (h : G ~{Grp}~> K) :
  GrpSurjective (image_cores h).
Proof.
  intro p; simpl.
  exists (`1 (`2 p)).
  simpl.
  exact (`2 (`2 p)).
Qed.

(* A surjective homomorphism identifies its image with its codomain.  The
   inverse map sends b to b together with its preimage witness, which is
   DATA (Epi.v's [GrpImage] is a sigma), so nothing is chosen. *)
Program Definition surjective_image_iso {G K : GrpObject} (h : G ~{Grp}~> K)
  (Hs : GrpSurjective h) : ImageGrp h ≅[Grp] K := {|
  to := sub_incl (ImageSub h);
  from := {| grp_map := {| morphism := fun b : carrier K =>
               existT _ b (Hs b) |} |}
|}.
Next Obligation. intros G K h Hs a b Hab; exact Hab. Qed.
Next Obligation. intros G K h Hs; simpl; reflexivity. Qed.
Next Obligation. intros G K h Hs a b; simpl; reflexivity. Qed.
Next Obligation. intros G K h Hs a; simpl; reflexivity. Qed.
Next Obligation. intros G K h Hs a; simpl; reflexivity. Qed.

(* 相关说明。 （已译） *)

Section ImageUniversal.

Context {G K : GrpObject}.
Context (h : G ~{Grp}~> K).

(* 相关说明。 （已译） *)
Lemma image_cores_kills (a : carrier G) :
  sub_mem (KernelNS h) a →
  grp_map (image_cores h) a ≈ grp_unit (ImageGrp h).
Proof. intro Ha; simpl in *; exact Ha. Qed.

Definition image_elem : Kills (KernelNS h) (ImageGrp h) :=
  existT _ (image_cores h) image_cores_kills.

Section ImageMediator.

Context {K' : GrpObject}.
Context (x : Kills (KernelNS h) K').

(*
   本节说明 Isomorphism 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma image_med_wd (a b : carrier G) :
  grp_map h a ≈ grp_map h b → grp_map (`1 x) a ≈ grp_map (`1 x) b.
Proof.
  intro Hab.
  apply (kills_descends (KernelNS h) x).
  unfold quot_rel; simpl.
  rewrite (grp_map_mul h), (grp_map_inv h), Hab.
  apply (grp_mul_inv_r K).
Qed.

(* 相关说明。 （已译） *)
Program Definition image_med : ImageGrp h ~{Grp}~> K' := {|
  grp_map := {| morphism := fun p : carrier (ImageGrp h) =>
                  grp_map (`1 x) (`1 (`2 p)) |}
|}.
Next Obligation.
  intros p q Hpq; simpl in *.
  apply image_med_wd.
  rewrite (`2 (`2 p)), (`2 (`2 q)).
  exact Hpq.
Qed.
Next Obligation.
  simpl.
  transitivity (grp_map (`1 x) (grp_unit G)).
  - apply image_med_wd.
    rewrite (`2 (`2 (grp_unit (ImageGrp h)))).
    simpl.
    symmetry; apply (grp_map_unit h).
  - apply (grp_map_unit (`1 x)).
Qed.
Next Obligation.
  intros p q; simpl.
  transitivity (grp_map (`1 x)
                  (grp_mul G (`1 (`2 p)) (`1 (`2 q)))).
  - apply image_med_wd.
    rewrite (`2 (`2 (grp_mul (ImageGrp h) p q))).
    rewrite (grp_map_mul h).
    rewrite (`2 (`2 p)), (`2 (`2 q)).
    reflexivity.
  - apply (grp_map_mul (`1 x)).
Qed.

Lemma image_med_commutes : image_med ∘ image_cores h ≈ `1 x.
Proof. intro a; simpl; reflexivity. Qed.

Lemma image_med_unique (v : ImageGrp h ~{Grp}~> K')
  (Hv : v ∘ image_cores h ≈ `1 x) : image_med ≈ v.
Proof.
  intro p; simpl.
  transitivity (grp_map v (grp_map (image_cores h) (`1 (`2 p)))).
  - symmetry; exact (Hv (`1 (`2 p))).
  - apply proper_morphism; simpl.
    exact (`2 (`2 p)).
Qed.

End ImageMediator.

(* ⟨im h, corestriction⟩ is a universal element of the SAME functor of
   which ⟨G/ker h, projection⟩ is one. *)
Program Definition image_universal_element :
  AUniversalElement (KillsFunctor (KernelNS h)) (ImageGrp h) := {|
  aue_elem := image_elem
|}.
Next Obligation.
  intros K' x.
  unshelve refine {| unique_obj := image_med x |}.
  - exact (image_med_commutes x).
  - intros v Hv; simpl in *.
    exact (image_med_unique x v Hv).
Defined.

End ImageUniversal.

(** ** The first isomorphism theorem *)

(* Two universal elements of one functor: [universal_element_iso] does the
   rest.  Nothing here builds a map or checks a round trip. *)
Definition first_isomorphism_theorem {G K : GrpObject} (h : G ~{Grp}~> K) :
  QuotientGrp (KernelNS h) ≅[Grp] ImageGrp h :=
  universal_element_iso (quot_universal_element (KernelNS h))
                        (image_universal_element h).

(* 相关说明。 （已译） *)
Lemma first_isomorphism_triangle {G K : GrpObject} (h : G ~{Grp}~> K) :
  to (first_isomorphism_theorem h) ∘ quot_proj (KernelNS h)
    ≈ image_cores h.
Proof.
  exact (ue_med_commutes (quot_universal_element (KernelNS h))
                         (image_universal_element h)).
Qed.

(*
   本节说明 Isomorphism 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example first_isomorphism_to_is_quot_med {G K : GrpObject}
  (h : G ~{Grp}~> K) :
  to (first_isomorphism_theorem h) = quot_med (KernelNS h) (image_elem h).
Proof. reflexivity. Qed.

Example first_isomorphism_from_is_image_med {G K : GrpObject}
  (h : G ~{Grp}~> K) :
  from (first_isomorphism_theorem h) = image_med h (quot_elem (KernelNS h)).
Proof. reflexivity. Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem first_isomorphism_unique {G K : GrpObject} (h : G ~{Grp}~> K)
  (v : QuotientGrp (KernelNS h) ≅[Grp] ImageGrp h)
  (Hv : to v ∘ quot_proj (KernelNS h) ≈ image_cores h) :
  first_isomorphism_theorem h ≈ v.
Proof.
  exact (universal_element_iso_unique (quot_universal_element (KernelNS h))
                                      (image_universal_element h) v Hv).
Qed.

(* 相关说明。 （已译） *)

(* h = (im h ↪ K) ∘ (comparison) ∘ (G ↠ G/ker h), middle map an
 同构. The 证明 composes two triangles above. （已译） *)
Theorem factorization {G K : GrpObject} (h : G ~{Grp}~> K) :
  sub_incl (ImageSub h)
    ∘ to (first_isomorphism_theorem h)
    ∘ quot_proj (KernelNS h)
  ≈ h.
Proof.
  rewrite <- comp_assoc.
  rewrite (first_isomorphism_triangle h).
  apply image_factors.
Qed.

(* The left leg epic right leg monic, so 这是 epi-mono
 factorization literal sense. （已译） *)
Theorem factorization_epi {G K : GrpObject} (h : G ~{Grp}~> K) :
  Epic (quot_proj (KernelNS h)).
Proof. apply quot_proj_epic. Qed.

Theorem factorization_mono {G K : GrpObject} (h : G ~{Grp}~> K) :
  Monic (sub_incl (ImageSub h)).
Proof. apply sub_incl_monic. Qed.

(* Awodey's 推论 proper: h injective exactly kernel is
 trivial. Both directions elementary; forward one the
 observation unit already kernel. （已译） *)
Theorem injective_iff_kernel_trivial {G K : GrpObject} (h : G ~{Grp}~> K) :
  (∀ a b : carrier G, grp_map h a ≈ grp_map h b → a ≈ b)
    ↔ (∀ a : carrier G, sub_mem (KernelNS h) a → a ≈ grp_unit G).
Proof.
  split.
  - intros Hinj a Ha; simpl in Ha.
    apply Hinj.
    rewrite Ha.
    symmetry; apply (grp_map_unit h).
  - intros Htriv a b Hab.
    apply (grp_cancel_r G (grp_inv G b)).
    rewrite (grp_mul_inv_r G b).
    apply Htriv; simpl.
    rewrite (grp_map_mul h), (grp_map_inv h), Hab.
    apply (grp_mul_inv_r K).
Qed.

(* 相关说明。 （已译） *)
Theorem monic_iff_kernel_trivial {G K : GrpObject} (h : G ~{Grp}~> K) :
  Monic h ↔ (∀ a : carrier G, sub_mem (KernelNS h) a → a ≈ grp_unit G).
Proof.
  split.
  - intro Hm.
    apply (fst (injective_iff_kernel_trivial h)).
    exact (snd (Grp_injectivity_is_monic h) Hm).
  - intro Ht.
    apply (fst (Grp_injectivity_is_monic h)).
    exact (snd (injective_iff_kernel_trivial h) Ht).
Qed.

(** ** The third isomorphism theorem *)

Section Third.

Context {G : GrpObject}.
Context (M N : NormalSubgroup G).
Context (Hsub : ∀ a : carrier G, sub_mem M a → sub_mem N a).

(*
   本节说明 Isomorphism 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition NmodM : NormalSubgroup (QuotientGrp M) := {|
  ns_sub := {| sub_mem := fun a : carrier (QuotientGrp M) =>
                            inhabited (sub_mem N a) |}
|}.
Next Obligation.
  intros a b Hab Ha; simpl in *.
  destruct Hab as [Hab], Ha as [Ha]; constructor.
  (* b ≈ (a * b⁻¹)⁻¹ * a, and both factors lie in N *)
  apply (sub_at N (a := grp_mul G (grp_inv G (grp_mul G a (grp_inv G b))) a)).
  - rewrite (grp_inv_mul G a (grp_inv G b)).
    rewrite (grp_inv_inv G b).
    rewrite (grp_mul_assoc G b (grp_inv G a) a).
    rewrite (grp_mul_inv_l G a).
    apply (grp_mul_unit_r G).
  - exact (sub_mul N _ _ (sub_inv N _ (Hsub _ Hab)) Ha).
Qed.
Next Obligation. simpl; exact (inhabits (sub_unit N)). Qed.
Next Obligation.
  intros a b Ha Hb; simpl in *.
  destruct Ha as [Ha], Hb as [Hb]; exact (inhabits (sub_mul N _ _ Ha Hb)).
Qed.
Next Obligation.
  intros a Ha; simpl in *.
  destruct Ha as [Ha]; exact (inhabits (sub_inv N _ Ha)).
Qed.
Next Obligation.
  intros t a Ha; simpl in *.
  destruct Ha as [Ha]; exact (inhabits (ns_conj N t _ Ha)).
Qed.

(* The comparison G/M ↠ G/N: 恒等 function again, well defined
 because M ⊆ N. （已译） *)
Program Definition quot_step : QuotientGrp M ~{Grp}~> QuotientGrp N := {|
  grp_map := {| morphism := fun a : carrier (QuotientGrp M) => a |}
|}.
Next Obligation.
  intros a b Hab.
  change (inhabited (quot_rel M a b)) in Hab.
  change (inhabited (quot_rel N a b)).
  destruct Hab as [Hab]; exact (inhabits (Hsub _ Hab)).
Qed.
Next Obligation. simpl; constructor; apply quot_rel_refl. Qed.
Next Obligation. intros a b; simpl; constructor; apply quot_rel_refl. Qed.

(* 相关说明。 （已译） *)
Lemma quot_step_triangle : quot_step ∘ quot_proj M ≈ quot_proj N.
Proof. intro a; simpl; constructor; apply quot_rel_refl. Qed.

(* The comparison kills N/M. *)
Lemma quot_step_kills (a : carrier (QuotientGrp M)) :
  sub_mem NmodM a → grp_map quot_step a ≈ grp_unit (QuotientGrp N).
Proof.
  intro Ha; simpl in *.
  destruct Ha as [Ha]; constructor.
  exact (snd (quot_rel_unit_iff N a) Ha).
Qed.

Definition quot_step_elem : Kills NmodM (QuotientGrp N) :=
  existT _ quot_step quot_step_kills.

Section ThirdMediator.

Context {K : GrpObject}.
Context (x : Kills NmodM K).

(*
   本节说明 Isomorphism 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma third_precompose_kills (a : carrier G) :
  sub_mem N a → grp_map (`1 x ∘ quot_proj M) a ≈ grp_unit K.
Proof.
  intro Ha; simpl; unfold Basics.compose.
  exact (`2 x a (inhabits Ha)).
Qed.

Definition third_precompose : Kills N K :=
  existT _ (`1 x ∘ quot_proj M) third_precompose_kills.

(* From here 论元 chase. The mediator one G/N's
 普遍性质 produces k ∘ p_M. （已译） *)
Definition third_med : QuotientGrp N ~{Grp}~> K := quot_med N third_precompose.

(* 相关说明。 （已译） *)
Lemma third_med_commutes : third_med ∘ quot_step ≈ `1 x.
Proof.
  apply (epic (Epic := quot_proj_epic M)).
  rewrite <- comp_assoc.
  rewrite quot_step_triangle.
  exact (quot_med_commutes N third_precompose).
Qed.

Lemma third_med_unique (v : QuotientGrp N ~{Grp}~> K)
  (Hv : v ∘ quot_step ≈ `1 x) : third_med ≈ v.
Proof.
  apply (quot_med_unique N third_precompose).
  rewrite <- quot_step_triangle.
  rewrite comp_assoc.
  rewrite Hv.
  reflexivity.
Qed.

End ThirdMediator.

(* ⟨G/N, comparison⟩ universal element kills-(N/M) 函子 on
 G/M. Every step above used [quot_universal_element N], the
 epimorphism [quot_proj_epic M], triangle. （已译） *)
Program Definition quot_universal_N_over_M :
  AUniversalElement (KillsFunctor NmodM) (QuotientGrp N) := {|
  aue_elem := quot_step_elem
|}.
Next Obligation.
  intros K x.
  unshelve refine {| unique_obj := third_med x |}.
  - exact (third_med_commutes x).
  - intros v Hv; simpl in *.
    exact (third_med_unique x v Hv).
Defined.

(* Mac Lane §III.1 Exercise 4, third isomorphism theorem. *)
Definition third_isomorphism_theorem :
  QuotientGrp NmodM ≅[Grp] QuotientGrp N :=
  universal_element_iso (quot_universal_element NmodM) quot_universal_N_over_M.

Lemma third_isomorphism_triangle :
  to third_isomorphism_theorem ∘ quot_proj NmodM ≈ quot_step.
Proof.
  exact (ue_med_commutes (quot_universal_element NmodM)
                         quot_universal_N_over_M).
Qed.

(* Uniqueness, first 定理. （已译） *)
Theorem third_isomorphism_unique
  (v : QuotientGrp NmodM ≅[Grp] QuotientGrp N)
  (Hv : to v ∘ quot_proj NmodM ≈ quot_step) :
  third_isomorphism_theorem ≈ v.
Proof.
  exact (universal_element_iso_unique (quot_universal_element NmodM)
                                      quot_universal_N_over_M v Hv).
Qed.

End Third.

Arguments NmodM {G} M N Hsub.
Arguments quot_step {G} M N Hsub.
Arguments third_isomorphism_theorem {G} M N Hsub.
Arguments third_isomorphism_unique {G} M N Hsub.

(* * ** The second 同构 定理 （已译） *)

(*
   本节说明 Isomorphism 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma product_shuffle (G : GrpObject) (s n s' n' : carrier G) :
  grp_mul G (grp_mul G s n) (grp_mul G s' n')
  ≈ grp_mul G (grp_mul G s s')
      (grp_mul G (grp_mul G (grp_mul G (grp_inv G s') n) s') n').
Proof.
  rewrite !grp_mul_assoc.
  rewrite <- (grp_mul_assoc G s' (grp_inv G s')
                (grp_mul G n (grp_mul G s' n'))).
  rewrite (grp_mul_inv_r G s').
  rewrite (grp_mul_unit_l G).
  reflexivity.
Qed.

Lemma inverse_shuffle (G : GrpObject) (s n : carrier G) :
  grp_inv G (grp_mul G s n)
  ≈ grp_mul G (grp_inv G s)
      (grp_mul G (grp_mul G s (grp_inv G n)) (grp_inv G s)).
Proof.
  rewrite (grp_inv_mul G s n).
  rewrite !grp_mul_assoc.
  rewrite <- (grp_mul_assoc G (grp_inv G s) s
                (grp_mul G (grp_inv G n) (grp_inv G s))).
  rewrite (grp_mul_inv_l G s).
  rewrite (grp_mul_unit_l G).
  reflexivity.
Qed.

Section Second.

Context {G : GrpObject}.
Context (S : Subgroup G).
Context (N : NormalSubgroup G).

(*
   本节说明同构、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition in_product (x : carrier G) : Type :=
  { s : carrier G & { n : carrier G &
      ((sub_mem S s * sub_mem N n) * (x ≈ grp_mul G s n))%type } }.

Program Definition SubgroupProduct : Subgroup G := {|
  sub_mem := in_product
|}.
Next Obligation.
  intros a b Hab [s [n [Hsn Ha]]].
  exists s, n; split; [ exact Hsn | now rewrite <- Hab ].
Qed.
Next Obligation.
  exists (grp_unit G), (grp_unit G).
  split; [ split; [ exact (sub_unit S) | exact (sub_unit N) ] | ].
  symmetry; apply (grp_mul_unit_l G).
Qed.
Next Obligation.
  intros a b [s [n [[Hs Hn] Ha]]] [s' [n' [[Hs' Hn'] Hb]]].
  exists (grp_mul G s s').
  exists (grp_mul G
            (grp_mul G (grp_mul G (grp_inv G s') n) (grp_inv G (grp_inv G s')))
            n').
  split.
  - split.
    + exact (sub_mul S _ _ Hs Hs').
    + exact (sub_mul N _ _ (ns_conj N (grp_inv G s') _ Hn) Hn').
  - rewrite Ha, Hb.
    rewrite (grp_inv_inv G s').
    apply product_shuffle.
Qed.
Next Obligation.
  intros a [s [n [[Hs Hn] Ha]]].
  exists (grp_inv G s).
  exists (grp_mul G (grp_mul G s (grp_inv G n)) (grp_inv G s)).
  split.
  - split.
    + exact (sub_inv S _ Hs).
    + exact (ns_conj N s _ (sub_inv N _ Hn)).
  - rewrite Ha.
    apply inverse_shuffle.
Qed.

(* N sits inside SN, and is normal there. *)
Lemma N_in_product (n : carrier G) : sub_mem N n → sub_mem SubgroupProduct n.
Proof.
  intro Hn.
  exists (grp_unit G), n.
  split; [ split; [ exact (sub_unit S) | exact Hn ] | ].
  symmetry; apply (grp_mul_unit_l G).
Qed.

Program Definition NinSN : NormalSubgroup (SubgroupGrp SubgroupProduct) := {|
  ns_sub := {| sub_mem := fun p : carrier (SubgroupGrp SubgroupProduct) =>
                            sub_mem N (`1 p) |}
|}.
Next Obligation.
  intros a b Hab Ha; simpl in *.
  exact (sub_resp N _ _ Hab Ha).
Qed.
Next Obligation. simpl; exact (sub_unit N). Qed.
Next Obligation. intros a b Ha Hb; simpl in *; exact (sub_mul N _ _ Ha Hb). Qed.
Next Obligation. intros a Ha; simpl in *; exact (sub_inv N _ Ha). Qed.
Next Obligation. intros t a Ha; simpl in *; exact (ns_conj N _ _ Ha). Qed.

(* S sits inside SN too, as a homomorphism of groups. *)
Program Definition S_into_SN :
  SubgroupGrp S ~{Grp}~> SubgroupGrp SubgroupProduct := {|
  grp_map := {| morphism := fun p : carrier (SubgroupGrp S) =>
     existT _ (`1 p)
       (existT _ (`1 p) (existT _ (grp_unit G)
          (pair (pair (`2 p) (sub_unit N))
                (symmetry (grp_mul_unit_r G (`1 p)))))) |}
|}.
Next Obligation. intros p q Hpq; exact Hpq. Qed.
Next Obligation. simpl; reflexivity. Qed.
Next Obligation. intros p q; simpl; reflexivity. Qed.

(* The 复合 S ↪ SN ↠ SN/N, whose kernel S ∩ N is
 surjective. （已译） *)
Definition psi : SubgroupGrp S ~{Grp}~> QuotientGrp NinSN :=
  quot_proj NinSN ∘ S_into_SN.

(* ELEMENTWISE INPUT ONE: the kernel of ψ is S ∩ N -- as a biconditional
   on membership, not merely an inclusion. *)
(*
   本节说明 Isomorphism 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma psi_kernel_is_meet (p : carrier (SubgroupGrp S)) :
  sub_mem (KernelNS psi) p ↔ inhabited (sub_mem N (`1 p)).
Proof.
  split.
  - intro Hp; simpl in Hp.
    unfold quot_equiv in Hp.
    destruct Hp as [Hp]; constructor.
    apply (sub_at N (a := grp_mul G (`1 p) (grp_inv G (grp_unit G)))).
    + rewrite (grp_inv_unit G); apply (grp_mul_unit_r G).
    + exact Hp.
  - intro Hp; simpl.
    destruct Hp as [Hp]; constructor.
    unfold quot_rel; simpl.
    apply (sub_at N (a := `1 p)).
    + rewrite (grp_inv_unit G); symmetry; apply (grp_mul_unit_r G).
    + exact Hp.
Qed.

(* The direction keeps [Type]-valued 假设 whole. （已译） *)
Lemma psi_kernel_of_meet (p : carrier (SubgroupGrp S)) :
  sub_mem N (`1 p) → sub_mem (KernelNS psi) p.
Proof. intro Hp; exact (snd (psi_kernel_is_meet p) (inhabits Hp)). Qed.

(* 相关说明。 （已译） *)
Lemma psi_surjective : GrpSurjective psi.
Proof.
  intro q.
  destruct (`2 q) as [s [n [[Hs Hn] Hq]]].
  exists (existT _ s Hs).
  simpl.
  constructor.
  unfold quot_rel; simpl.
  (* s * (s n)⁻¹ lies in N *)
  apply (sub_at N (a := grp_mul G (grp_mul G s (grp_inv G n)) (grp_inv G s))).
  - rewrite Hq.
    rewrite (grp_inv_mul G s n).
    rewrite (grp_mul_assoc G s (grp_inv G n) (grp_inv G s)).
    reflexivity.
  - exact (ns_conj N s _ (sub_inv N _ Hn)).
Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition second_isomorphism_theorem :
  QuotientGrp (KernelNS psi) ≅[Grp] QuotientGrp NinSN :=
  iso_compose (surjective_image_iso psi psi_surjective)
              (first_isomorphism_theorem psi).

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明同构、核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition MeetNS : NormalSubgroup (SubgroupGrp S) := {|
  ns_sub := {| sub_mem := fun p : carrier (SubgroupGrp S) =>
                            inhabited (sub_mem N (`1 p)) |}
|}.
Next Obligation.
  intros a b Hab Ha; simpl in *.
  destruct Ha as [Ha]; constructor; exact (sub_resp N _ _ Hab Ha).
Qed.
Next Obligation. simpl; exact (inhabits (sub_unit N)). Qed.
Next Obligation.
  intros a b Ha Hb; simpl in *.
  destruct Ha as [Ha], Hb as [Hb]; constructor; exact (sub_mul N _ _ Ha Hb).
Qed.
Next Obligation.
  intros a Ha; simpl in *.
  destruct Ha as [Ha]; constructor; exact (sub_inv N _ Ha).
Qed.
Next Obligation.
  intros t a Ha; simpl in *.
  destruct Ha as [Ha]; constructor; exact (ns_conj N _ _ Ha).
Qed.

Definition second_isomorphism_theorem_literal :
  QuotientGrp MeetNS ≅[Grp] QuotientGrp NinSN :=
  iso_compose second_isomorphism_theorem
    (quot_congr MeetNS (KernelNS psi)
       (fun p Hp => snd (psi_kernel_is_meet p) Hp)
       (fun p Hp => fst (psi_kernel_is_meet p) Hp)).

End Second.

Arguments SubgroupProduct {G} S N.
Arguments MeetNS {G} S N.
Arguments NinSN {G} S N.
Arguments psi {G} S N.
Arguments second_isomorphism_theorem {G} S N.
Arguments second_isomorphism_theorem_literal {G} S N.

(*
   本节说明 Isomorphism 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明同构、核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma S3_proj_kernel_is_A3 (a : carrier S3) :
  sub_mem (KernelNS (quot_proj A3)) a ↔ inhabited (sub_mem A3 a).
Proof. exact (quot_proj_kernel A3 a). Qed.

(* The first isomorphism theorem instantiated: S3/ker(p) ≅ im(p). *)
Definition S3_first_iso :
  QuotientGrp (KernelNS (quot_proj A3)) ≅[Grp] ImageGrp (quot_proj A3) :=
  first_isomorphism_theorem (quot_proj A3).

(* 相关说明。 （已译） *)
(*
   本节说明 Isomorphism 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem S3_first_iso_nondegenerate :
  grp_map (image_cores (quot_proj A3)) S3_s
    ≈ grp_map (image_cores (quot_proj A3)) s3_unit → False.
Proof. intros [H]; simpl in H; discriminate. Qed.

(* The third 同构 定理 at M = trivial, N = A3: (S3/1)/(A3/1) ≅
 S3/A3. The 含入 假设 everything ≈-equal unit
 rotation. （已译） *)
Lemma trivial_in_A3 (a : carrier S3) : sub_mem (TrivialNS S3) a → sub_mem A3 a.
Proof. intro Ha; simpl in *; now subst. Qed.

Definition S3_third_iso :
  QuotientGrp (NmodM (TrivialNS S3) A3 trivial_in_A3)
    ≅[Grp] QuotientGrp A3 :=
  third_isomorphism_theorem (TrivialNS S3) A3 trivial_in_A3.

(* Nondegenerate: reflection still apart unit left
 同构. （已译） *)
Theorem S3_third_iso_nondegenerate :
  quot_rel (NmodM (TrivialNS S3) A3 trivial_in_A3) S3_s s3_unit → False.
Proof. intros [H]; simpl in H; discriminate. Qed.

(*
   本节说明同构、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition S3_second_iso :
  QuotientGrp (KernelNS (psi S3_refl_sub A3))
    ≅[Grp] QuotientGrp (NinSN S3_refl_sub A3) :=
  second_isomorphism_theorem S3_refl_sub A3.

(* 相关说明。 （已译） *)
Theorem S3_second_iso_nondegenerate :
  quot_rel (KernelNS (psi S3_refl_sub A3))
    (existT _ S3_s (eq_refl : fst S3_s = rot0))
    (grp_unit (SubgroupGrp S3_refl_sub))
  → False.
Proof. intros [H]; simpl in H; discriminate. Qed.

(* The literal form, whose left-hand side is S/(S ∩ N) rather than
   S/ker ψ. *)
Definition S3_second_iso_literal :
  QuotientGrp (MeetNS S3_refl_sub A3)
    ≅[Grp] QuotientGrp (NinSN S3_refl_sub A3) :=
  second_isomorphism_theorem_literal S3_refl_sub A3.

Theorem S3_second_iso_literal_nondegenerate :
  quot_rel (MeetNS S3_refl_sub A3)
    (existT _ S3_s (eq_refl : fst S3_s = rot0))
    (grp_unit (SubgroupGrp S3_refl_sub))
  → False.
Proof. intros [H]; simpl in H; discriminate. Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition S3_s_in_SN : carrier (SubgroupGrp (SubgroupProduct S3_refl_sub A3)).
Proof.
  refine (existT _ S3_s _).
  exists S3_s, s3_unit.
  split; [ split | ].
  - exact (eq_refl : fst S3_s = rot0).
  - exact (eq_refl : snd s3_unit = false).
  - vm_compute; reflexivity.
Defined.

Theorem S3_second_iso_codomain_nondegenerate :
  quot_rel (NinSN S3_refl_sub A3) S3_s_in_SN
    (grp_unit (SubgroupGrp (SubgroupProduct S3_refl_sub A3)))
  → False.
Proof. simpl; discriminate. Qed.
