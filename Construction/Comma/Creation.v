Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Parallel.

Set Universe Polymorphism.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/created+limit

   本文件给出极限/余极限的创造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明（余）极限、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Definition PreservesImageLimit_Continuous
  {C D : Category} {U : C ⟶ D} (H : @PreservesImageLimit C D U) :
  ContinuousFunctor U :=
  fun J K N HN => H J K (@Build_Limit J C K N HN).

Definition Continuous_PreservesImageLimit
  {C D : Category} {U : C ⟶ D} (H : ContinuousFunctor U) :
  @PreservesImageLimit C D U :=
  fun J K L => H J K (@limit_cone _ _ _ L) (limit_limitcone L).

(** ** The reflection clause *)

Section CommaReflect.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context (HU : @PreservesImageLimit C D U).
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma rbase_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[U] (fmap[comma_proj2 ◯ K] f) ∘ `2 (K x) ≈ `2 (K y).
Proof using Type.
  symmetry.
  transitivity (`2 (K y) ∘ id[d]).
  - rewrite id_right; reflexivity.
  - exact (`2 (fmap[K] f)).
Qed.

Definition rbase_cone : Cone (U ◯ (comma_proj2 ◯ K)) :=
  @Build_Cone J D (U ◯ (comma_proj2 ◯ K)) d
    (@Build_ACone J D d (U ◯ (comma_proj2 ◯ K))
       (fun j => `2 (K j)) (@rbase_coherence)).

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition comma_creates_reflect (M : Cone K)
  (HM : IsLimitCone (FCone comma_proj2 M)) : IsLimitCone M.
Proof using HU.
  intro N.
  pose (L := @Build_Limit J C (comma_proj2 ◯ K) (FCone comma_proj2 M) HM).
  destruct (HM (FCone comma_proj2 N)) as [w Hw Hwu].
  assert (Hsq : (`2 vertex_obj[M]) ∘ id[d]
                  ≈ fmap[U] w ∘ `2 vertex_obj[N]).
  { rewrite id_right.
    apply (limit_med_eq (image_is_alimit HU L) rbase_cone).
    - intro j.
      change (fmap[U] (cone_leg (FCone comma_proj2 M) j) ∘ (`2 vertex_obj[M])
                ≈ `2 (K j)).
      symmetry.
      exact (comma_square (cone_leg M j)).
    - intro j.
      change (fmap[U] (cone_leg (FCone comma_proj2 M) j)
                ∘ (fmap[U] w ∘ `2 vertex_obj[N]) ≈ `2 (K j)).
      rewrite comp_assoc, <- fmap_comp.
      rewrite (Hw j).
      symmetry.
      exact (comma_square (cone_leg N j)). }
  unshelve refine {| unique_obj := ((ttt, w); Hsq) |}.
  - intro j; split.
    + now destruct (fst (`1 (cone_leg N j))).
    + exact (Hw j).
  - intros [[u1 u2] Hu] Hv; split.
    + simpl; destruct u1; reflexivity.
    + apply Hwu.
      intro j.
      exact (snd (Hv j)).
Defined.

End CommaReflect.

(** ** The instance *)

Section CommaCreates.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context (HU : @PreservesImageLimit C D U).
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Context (L : Limit (Gdiag K)).

(* 相关说明。 （已译） *)

Definition comma_image_limitcone :
  IsLimitCone (FCone comma_proj2 (@limit_cone _ _ _ (comma_limit HU K L)))
  := fun N => @ump_limit _ _ _ _ (limit_is_alimit L) N.

Definition comma_CreatesLimit : CreatesLimit K comma_proj2.
Proof using HU L.
  unshelve refine
    {| creates_lift := fun _ _ => @limit_cone _ _ _ (comma_limit HU K L) |}.
  - intros N HN.
    exact (limitcone_iso comma_image_limitcone HN).
  - exact (comma_creates_reflect HU K).
Defined.

End CommaCreates.

(* 相关说明。 （已译） *)

(*
   本节说明（余）极限、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition comma_strict_apex {C D : Category} {U : C ⟶ D} {d : D}
  (HU : @PreservesImageLimit C D U)
  {J : Category} (K : J ⟶ (=(d) ↓ U)) (L : Limit (Gdiag K)) :
  comma_proj2 (vertex_obj[comma_limit HU K L]) = vertex_obj[L]
  := eq_refl.

Definition comma_strict_legs {C D : Category} {U : C ⟶ D} {d : D}
  (HU : @PreservesImageLimit C D U)
  {J : Category} (K : J ⟶ (=(d) ↓ U)) (L : Limit (Gdiag K)) (j : J) :
  fmap[comma_proj2] (cone_leg (comma_limit HU K L) j)
    = limit_leg (limit_is_alimit L) j := eq_refl.

(* * ** The same construction PER-DIAGRAM 假设 （已译） *)

(*
   本节说明（余）极限、等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CommaCreateAt.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).
Context (HK : PreservesLimitCone (Gdiag K) U).
Context (L : Limit (Gdiag K)).

Definition comma_at_image : IsALimit (U ◯ Gdiag K) (U L) :=
  @Build_IsALimit J D (U ◯ Gdiag K) (U L) (image_acone L)
    (HK (@limit_cone _ _ _ L) (limit_limitcone L)).

Definition comma_at_phi : d ~{D}~> U L :=
  limit_med comma_at_image (base_cone K).

Lemma comma_at_phi_commutes (j : J) :
  fmap[U] (limit_leg (limit_is_alimit L) j) ∘ comma_at_phi ≈ `2 (K j).
Proof. exact (limit_med_commutes comma_at_image (base_cone K) j). Qed.

Definition comma_at_apex_obj : (=(d) ↓ U) := ((ttt, vertex_obj[L]); comma_at_phi).

Definition comma_at_apex_leg (j : J) : comma_at_apex_obj ~{=(d) ↓ U}~> K j.
Proof.
  unshelve refine ((ttt, limit_leg (limit_is_alimit L) j); _).
  change (`2 (K j) ∘ id[d]
          ≈ fmap[U] (limit_leg (limit_is_alimit L) j) ∘ comma_at_phi).
  rewrite id_right.
  symmetry.
  exact (comma_at_phi_commutes j).
Defined.

Lemma comma_at_apex_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ comma_at_apex_leg x ≈ comma_at_apex_leg y.
Proof.
  split.
  - reflexivity.
  - exact (limit_leg_coherence (limit_is_alimit L) f).
Qed.

Definition comma_at_apex_cone : Cone K :=
  @Build_Cone J (=(d) ↓ U) K comma_at_apex_obj
    (@Build_ACone J (=(d) ↓ U) comma_at_apex_obj K comma_at_apex_leg
       (@comma_at_apex_coherence)).

Definition comma_at_med (N : Cone K) :
  vertex_obj[N] ~{=(d) ↓ U}~> comma_at_apex_obj.
Proof.
  unshelve refine ((ttt, wmed K L N); _).
  change (comma_at_phi ∘ id[d] ≈ fmap[U] (wmed K L N) ∘ `2 vertex_obj[N]).
  rewrite id_right.
  apply (limit_med_eq comma_at_image (base_cone K)).
  - exact (limit_med_commutes comma_at_image (base_cone K)).
  - intro j.
    change (fmap[U] (limit_leg (limit_is_alimit L) j)
              ∘ (fmap[U] (wmed K L N) ∘ `2 vertex_obj[N]) ≈ `2 (K j)).
    unfold wmed.
    rewrite comp_assoc, <- fmap_comp.
    rewrite (limit_med_commutes (limit_is_alimit L) (qcone K N) j).
    symmetry.
    exact (comma_square (cone_leg N j)).
Defined.

Definition comma_at_ump (N : Cone K) :
  ∃! u : vertex_obj[N] ~{=(d) ↓ U}~> comma_at_apex_obj,
    ∀ j : J, comma_at_apex_leg j ∘ u ≈ cone_leg N j.
Proof.
  unshelve refine {| unique_obj := comma_at_med N |}.
  - intro j; split.
    + now destruct (fst (`1 (cone_leg N j))).
    + exact (limit_med_commutes (limit_is_alimit L) (qcone K N) j).
  - intros v Hv; split.
    + now destruct (fst (`1 v)).
    + unfold wmed.
      apply (limit_med_unique (limit_is_alimit L) (qcone K N)).
      intro j.
      exact (snd (Hv j)).
Defined.

Definition comma_limit_at : Limit K :=
  @Build_Limit J (=(d) ↓ U) K comma_at_apex_cone comma_at_ump.

(* 相关说明。 （已译） *)

Definition comma_limit_at_apex :
  comma_proj2 (vertex_obj[comma_limit_at]) = vertex_obj[L] := eq_refl.

Definition comma_limit_at_legs (j : J) :
  fmap[comma_proj2] (cone_leg comma_limit_at j)
    = limit_leg (limit_is_alimit L) j := eq_refl.

End CommaCreateAt.

(* 相关说明。 （已译） *)

Section CommaReflectAt.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).
Context (HK : PreservesLimitCone (Gdiag K) U).

(* [comma_creates_reflect] above all-shapes [HU] weakened [HK];
 script 证明's, [image_is_alimit HU L] replaced by
 [comma_at_image K HK L]. （已译） *)

Definition comma_reflect_at (M : Cone K)
  (HM : IsLimitCone (FCone comma_proj2 M)) : IsLimitCone M.
Proof using HK.
  intro N.
  pose (L := @Build_Limit J C (comma_proj2 ◯ K) (FCone comma_proj2 M) HM).
  destruct (HM (FCone comma_proj2 N)) as [w Hw Hwu].
  assert (Hsq : (`2 vertex_obj[M]) ∘ id[d]
                  ≈ fmap[U] w ∘ `2 vertex_obj[N]).
  { rewrite id_right.
    apply (limit_med_eq (comma_at_image K HK L) (rbase_cone K)).
    - intro j.
      change (fmap[U] (cone_leg (FCone comma_proj2 M) j) ∘ (`2 vertex_obj[M])
                ≈ `2 (K j)).
      symmetry.
      exact (comma_square (cone_leg M j)).
    - intro j.
      change (fmap[U] (cone_leg (FCone comma_proj2 M) j)
                ∘ (fmap[U] w ∘ `2 vertex_obj[N]) ≈ `2 (K j)).
      rewrite comp_assoc, <- fmap_comp.
      rewrite (Hw j).
      symmetry.
      exact (comma_square (cone_leg N j)). }
  unshelve refine {| unique_obj := ((ttt, w); Hsq) |}.
  - intro j; split.
    + now destruct (fst (`1 (cone_leg N j))).
    + exact (Hw j).
  - intros [[u1 u2] Hu] Hv; split.
    + simpl; destruct u1; reflexivity.
    + apply Hwu.
      intro j.
      exact (snd (Hv j)).
Defined.

End CommaReflectAt.

(** ** Strict creation *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CommaStrictCreate.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).
Context (HK : PreservesLimitCone (Gdiag K) U).

Definition comma_strict_lift (N : Cone (comma_proj2 ◯ K)) (HN : IsLimitCone N) :
  StrictLift K comma_proj2 N :=
  @Build_StrictLift J (=(d) ↓ U) C K comma_proj2 N
    (comma_limit_at K HK (@Build_Limit J C (Gdiag K) N HN))
    eq_refl
    (fun x => reflexivity _).

Definition comma_StrictlyCreatesLimit : StrictlyCreatesLimit K comma_proj2.
Proof using HK.
  unshelve refine {| screates := comma_strict_lift |}.
  - intros N HN.
    exact (limit_limitcone
             (comma_limit_at K HK (@Build_Limit J C (Gdiag K) N HN))).
  - exact (comma_reflect_at K HK).
Defined.

(* Creation no [L] 论元 at all, lift over given
 cone rather than over chosen one. （已译） *)

Definition comma_CreatesLimit_at : CreatesLimit K comma_proj2 :=
  StrictlyCreatesLimit_CreatesLimit comma_StrictlyCreatesLimit.

End CommaStrictCreate.

(** ** Products, elementarily *)

(*
   本节说明（余）极限、等化子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CommaProducts.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context {A : Type}.
Context (F : A → (=(d) ↓ U)).

Definition comma_prod_fam (a : A) : C := comma_proj2 (F a).

Context (p : C).
Context (proj : ∀ a : A, p ~{C}~> comma_prod_fam a).
Context (HP : IsIndexedProduct comma_prod_fam p proj).

(* The per-shape preservation 假设 at most elementary: [U] carries
 THIS indexed product indexed product. （已译） *)
Context (HU : IsIndexedProduct (fun a => U (comma_prod_fam a)) (U p)
                (fun a => fmap[U] (proj a))).

Definition comma_prod_phi : d ~{D}~> U p :=
  unique_obj (iprod_desc HU (fun a => `2 (F a))).

Lemma comma_prod_phi_commutes (a : A) :
  fmap[U] (proj a) ∘ comma_prod_phi ≈ `2 (F a).
Proof using Type.
  exact (unique_property (iprod_desc HU (fun a => `2 (F a))) a).
Qed.

Definition comma_prod_apex : (=(d) ↓ U) := ((ttt, p); comma_prod_phi).

Definition comma_prod_proj (a : A) : comma_prod_apex ~{=(d) ↓ U}~> F a.
Proof using Type.
  unshelve refine ((ttt, proj a); _).
  change (`2 (F a) ∘ id[d] ≈ fmap[U] (proj a) ∘ comma_prod_phi).
  rewrite id_right.
  symmetry.
  exact (comma_prod_phi_commutes a).
Defined.

Definition comma_IsIndexedProduct :
  IsIndexedProduct F comma_prod_apex comma_prod_proj.
Proof using HP HU.
  constructor.
  intros c pi.
  destruct (iprod_desc HP (fun a => snd (`1 (pi a)))) as [w Hw Hwu].
  assert (Hsq : comma_prod_phi ∘ id[d] ≈ fmap[U] w ∘ `2 c).
  { rewrite id_right.
    unfold comma_prod_phi.
    apply (uniqueness (iprod_desc HU (fun a => `2 (F a)))).
    intro a.
    rewrite comp_assoc, <- fmap_comp, (Hw a).
    symmetry.
    exact (comma_square (pi a)). }
  unshelve refine {| unique_obj := ((ttt, w); Hsq) |}.
  - intro a; split.
    + now destruct (fst (`1 (pi a))).
    + exact (Hw a).
  - intros [[u1 u2] Hu] Hv; split.
    + simpl; destruct u1; reflexivity.
    + apply Hwu.
      intro a.
      exact (snd (Hv a)).
Defined.

Definition comma_prod_apex_strict : comma_proj2 comma_prod_apex = p := eq_refl.

Definition comma_prod_leg_strict (a : A) :
  fmap[comma_proj2] (comma_prod_proj a) = proj a := eq_refl.

End CommaProducts.

(** ** Equalizers *)

(*
   本节说明（余）极限、等化子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CommaEqualizers.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context (K : Parallel ⟶ (=(d) ↓ U)).
Context (HK : PreservesLimitCone (Gdiag K) U).
Context (E : Equalizer (Gdiag K)).

Definition comma_equalizer_at : Equalizer K := comma_limit_at K HK E.

Definition comma_equalizer_apex_strict :
  comma_proj2 (vertex_obj[comma_equalizer_at]) = vertex_obj[E] := eq_refl.

Definition comma_equalizer_leg_strict (j : Parallel) :
  fmap[comma_proj2] (cone_leg comma_equalizer_at j)
    = limit_leg (limit_is_alimit E) j := eq_refl.

Definition comma_StrictlyCreatesEqualizers :
  StrictlyCreatesLimit K comma_proj2 := comma_StrictlyCreatesLimit K HK.

End CommaEqualizers.

(* 相关说明。 （已译） *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition comma_CreatesAllLimits {C D : Category} {U : C ⟶ D} {d : D}
  (HU : @PreservesImageLimit C D U) :
  @CreatesAllLimits (=(d) ↓ U) C comma_proj2 :=
  fun J K => StrictlyCreatesLimit_CreatesLimit
               (comma_StrictlyCreatesLimit K
                  (fun N HN => HU _ (Gdiag K) (@Build_Limit _ _ (Gdiag K) N HN))).

Definition comma_CreatesProducts {C D : Category} {U : C ⟶ D} {d : D}
  (HU : @PreservesImageLimit C D U) :
  @CreatesProducts (=(d) ↓ U) C comma_proj2 :=
  CreatesAllLimits_CreatesProducts (comma_CreatesAllLimits HU).

(*
   本节说明伴随、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition comma_Complete_via_creation {C D : Category} {U : C ⟶ D} {d : D}
  (HU : @PreservesImageLimit C D U) (comp : @Complete C) :
  @Complete (=(d) ↓ U) :=
  creates_limits_Complete comma_proj2 comp (comma_CreatesAllLimits HU).

(* 相关说明。 （已译） *)

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition comma_proj_creates_limits {C D : Category} {U : C ⟶ D} {d : D}
  {J : Category} (K : J ⟶ (=(d) ↓ U))
  (HK : PreservesLimitCone (Gdiag K) U) :
  StrictlyCreatesLimit K comma_proj2 := comma_StrictlyCreatesLimit K HK.

Definition comma_creates_equalizers {C D : Category} {U : C ⟶ D} {d : D}
  (K : Parallel ⟶ (=(d) ↓ U)) (HK : PreservesLimitCone (Gdiag K) U)
  (E : Equalizer (Gdiag K)) : Equalizer K := comma_equalizer_at K HK E.

Definition comma_creates_products {C D : Category} {U : C ⟶ D} {d : D}
  {A : Type} (F : A → (=(d) ↓ U)) (p : C)
  (proj : ∀ a : A, p ~{C}~> comma_prod_fam F a)
  (HP : IsIndexedProduct (comma_prod_fam F) p proj)
  (HU : IsIndexedProduct (fun a => U (comma_prod_fam F a)) (U p)
          (fun a => fmap[U] (proj a))) :
  IsIndexedProduct F (comma_prod_apex F p proj HU) (comma_prod_proj F p proj HU)
  := comma_IsIndexedProduct F p proj HP HU.
