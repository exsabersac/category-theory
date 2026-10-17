Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Adjunction.Continuity.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Adjoint.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/equivalence+of+categories
   nLab: https://ncatlab.org/nlab/show/preserved+limit
   nLab: https://ncatlab.org/nlab/show/reflected+limit
   nLab: https://ncatlab.org/nlab/show/created+limit

   本文件给出极限相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)

Lemma cone_leg_coherence {J C : Category} {F : J ⟶ C} (N : Cone F)
  {x y : J} (f : x ~{J}~> y) :
  fmap[F] f ∘ cone_leg N x ≈ cone_leg N y.
Proof. exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f). Qed.

(* 相关说明。 （已译） *)

Definition isalimit_to_limit {J C : Category} {G : J ⟶ C} {c : C}
  (H : IsALimit G c) : Limit G :=
  @Build_Limit J C G
    (@Build_Cone J C G c (@limit_acone _ _ _ _ H))
    (@ump_limit _ _ _ _ H).

(* * ** Transport limits along natural 同构 diagrams （已译） *)

(*
   本节说明函子、（余）极限、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section DiagramIso.

Context {J : Category}.
Context {C : Category}.
Context {G G' : J ⟶ C}.
Context (e : G ≈ G').

(* Push cone over G across e: compose each leg forward
 component 同构 family. （已译） *)

Definition cone_transport_leg (N : Cone G) (x : J) :
  vertex_obj[N] ~{C}~> G' x :=
  to (`1 e x) ∘ cone_leg N x.

Lemma cone_transport_coherence (N : Cone G) {x y : J} (f : x ~{J}~> y) :
  fmap[G'] f ∘ cone_transport_leg N x ≈ cone_transport_leg N y.
Proof using e.
  unfold cone_transport_leg.
  rewrite comp_assoc.
  rewrite <- (fun_equiv_to_fmap e x y f).
  rewrite <- comp_assoc.
  now rewrite (cone_leg_coherence N f).
Qed.

Definition cone_transport (N : Cone G) : Cone G' :=
  @Build_Cone J C G' (vertex_obj[N])
    (@Build_ACone J C (vertex_obj[N]) G' (cone_transport_leg N)
       (fun x y f => cone_transport_coherence N f)).

(* Pull cone over G' back across e: compose each leg inverse
 component 同构 family. （已译） *)

Definition cone_transport_inv_leg (N : Cone G') (x : J) :
  vertex_obj[N] ~{C}~> G x :=
  from (`1 e x) ∘ cone_leg N x.

Lemma cone_transport_inv_coherence (N : Cone G') {x y : J}
  (f : x ~{J}~> y) :
  fmap[G] f ∘ cone_transport_inv_leg N x ≈ cone_transport_inv_leg N y.
Proof using e.
  unfold cone_transport_inv_leg.
  rewrite comp_assoc.
  rewrite (fun_equiv_fmap_from e x y f).
  rewrite <- comp_assoc.
  now rewrite (cone_leg_coherence N f).
Qed.

Definition cone_transport_inv (N : Cone G') : Cone G :=
  @Build_Cone J C G (vertex_obj[N])
    (@Build_ACone J C (vertex_obj[N]) G (cone_transport_inv_leg N)
       (fun x y f => cone_transport_inv_coherence N f)).

(* 相关说明。 （已译） *)

Lemma cone_transport_inv_leg_eq (N : Cone G') (x : J) :
  cone_leg (cone_transport_inv N) x ≈ from (`1 e x) ∘ cone_leg N x.
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)

Section TransportWitness.

Context {c : C}.
Context (HL : IsALimit G c).

Definition isalimit_transport_leg (x : J) : c ~{C}~> G' x :=
  to (`1 e x) ∘ limit_leg HL x.

Lemma isalimit_transport_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[G'] f ∘ isalimit_transport_leg x ≈ isalimit_transport_leg y.
Proof using e HL.
  unfold isalimit_transport_leg.
  rewrite comp_assoc.
  rewrite <- (fun_equiv_to_fmap e x y f).
  rewrite <- comp_assoc.
  now rewrite (limit_leg_coherence HL f).
Qed.

Definition isalimit_transport_acone : ACone c G' :=
  @Build_ACone J C c G' isalimit_transport_leg
    (fun x y f => isalimit_transport_coherence f).

(* 相关说明。 （已译） *)

Definition isalimit_transport_med (N : Cone G') :
  vertex_obj[N] ~{C}~> c :=
  limit_med HL (cone_transport_inv N).

Lemma isalimit_transport_med_commutes (N : Cone G') :
  ∀ x : J, isalimit_transport_leg x ∘ isalimit_transport_med N
             ≈ cone_leg N x.
Proof using e HL.
  intro x.
  unfold isalimit_transport_leg, isalimit_transport_med.
  rewrite <- comp_assoc.
  rewrite (limit_med_commutes HL (cone_transport_inv N) x).
  rewrite (cone_transport_inv_leg_eq N x).
  rewrite comp_assoc.
  rewrite iso_to_from.
  now rewrite id_left.
Qed.

Lemma isalimit_transport_med_unique (N : Cone G')
  (v : vertex_obj[N] ~{C}~> c) :
  (∀ x : J, isalimit_transport_leg x ∘ v ≈ cone_leg N x) →
  isalimit_transport_med N ≈ v.
Proof using e HL.
  intro Hv.
  unfold isalimit_transport_med.
  apply (limit_med_unique HL (cone_transport_inv N) v).
  intro x.
  rewrite (cone_transport_inv_leg_eq N x).
  rewrite <- (Hv x).
  unfold isalimit_transport_leg.
  rewrite !comp_assoc.
  rewrite iso_from_to.
  now rewrite id_left.
Qed.

Definition isalimit_transport_ump (N : Cone G') :
  ∃! u : vertex_obj[N] ~{C}~> c,
    ∀ x : J, isalimit_transport_leg x ∘ u ≈ cone_leg N x :=
  Build_Unique _ _ _ (isalimit_transport_med N)
    (isalimit_transport_med_commutes N)
    (isalimit_transport_med_unique N).

Definition isalimit_transport : IsALimit G' c :=
  @Build_IsALimit J C G' c isalimit_transport_acone isalimit_transport_ump.

End TransportWitness.

(* 相关说明。 （已译） *)

Definition limit_transport (L : Limit G) : Limit G' :=
  isalimit_to_limit (isalimit_transport (limit_is_alimit L)).

End DiagramIso.

(* * ** The image cone under 函子 （已译） *)

(* * ** Fully faithful 函子 reflect isomorphisms limits （已译） *)

Section FullyFaithful.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context `{HF : @Full C D F}.
Context `{HfF : @Faithful C D F}.

(* A 全忠实 函子 conservative: chosen inverse f
 [prefmap]-preimage inverse fmap[F] f, two
 inverse laws recovered faithfulness. （已译） *)

Definition ff_iso_inverse {x y : C} (f : x ~{C}~> y)
  (I : IsIsomorphism (fmap[F] f)) : y ~{C}~> x :=
  prefmap (@two_sided_inverse D _ _ _ I).

Lemma ff_iso_inverse_right {x y : C} (f : x ~{C}~> y)
  (I : IsIsomorphism (fmap[F] f)) :
  f ∘ ff_iso_inverse f I ≈ id.
Proof using HF HfF.
  apply fmap_inj.
  rewrite fmap_comp.
  unfold ff_iso_inverse.
  rewrite fmap_sur, fmap_id.
  exact (@is_right_inverse D _ _ _ I).
Qed.

Lemma ff_iso_inverse_left {x y : C} (f : x ~{C}~> y)
  (I : IsIsomorphism (fmap[F] f)) :
  ff_iso_inverse f I ∘ f ≈ id.
Proof using HF HfF.
  apply fmap_inj.
  rewrite fmap_comp.
  unfold ff_iso_inverse.
  rewrite fmap_sur, fmap_id.
  exact (@is_left_inverse D _ _ _ I).
Qed.

Definition ff_reflects_isos : ReflectsIsos F :=
  @Build_ReflectsIsos C D F
    (fun x y f I =>
       @Build_IsIsomorphism C x y f (ff_iso_inverse f I)
         (ff_iso_inverse_right f I)
         (ff_iso_inverse_left f I)).

(** *** Reflection of limits *)

Section ReflectLimit.

Context {J : Category}.
Context {G : J ⟶ C}.
Context (N : Cone G).
Context (HL : IsALimit (F ◯ G) (F (vertex_obj[N]))).
Context (Hlegs : ∀ x : J, limit_leg HL x ≈ fmap[F] (cone_leg N x)).

(* 相关说明。 （已译） *)

Definition ff_reflect_med (M : Cone G) :
  vertex_obj[M] ~{C}~> vertex_obj[N] :=
  prefmap (limit_med HL (FCone F M)).

Lemma ff_reflect_med_commutes (M : Cone G) :
  ∀ x : J, cone_leg N x ∘ ff_reflect_med M ≈ cone_leg M x.
Proof using HF HfF HL Hlegs.
  intro x.
  apply fmap_inj.
  rewrite fmap_comp.
  unfold ff_reflect_med.
  rewrite fmap_sur.
  rewrite <- (Hlegs x).
  rewrite (limit_med_commutes HL (FCone F M) x).
  exact (FCone_leg F M x).
Qed.

Lemma ff_reflect_med_unique (M : Cone G)
  (v : vertex_obj[M] ~{C}~> vertex_obj[N]) :
  (∀ x : J, cone_leg N x ∘ v ≈ cone_leg M x) →
  ff_reflect_med M ≈ v.
Proof using HF HfF HL Hlegs.
  intro Hv.
  apply fmap_inj.
  unfold ff_reflect_med.
  rewrite fmap_sur.
  apply (limit_med_unique HL (FCone F M) (fmap[F] v)).
  intro x.
  rewrite (FCone_leg F M x).
  rewrite (Hlegs x).
  rewrite <- (Hv x).
  rewrite fmap_comp.
  reflexivity.
Qed.

Definition ff_reflect_ump (M : Cone G) :
  ∃! u : vertex_obj[M] ~{C}~> vertex_obj[N],
    ∀ x : J, cone_leg N x ∘ u ≈ cone_leg M x :=
  Build_Unique _ _ _ (ff_reflect_med M)
    (ff_reflect_med_commutes M)
    (ff_reflect_med_unique M).

(* Full + faithful 函子 reflect limits: cone N, own leg
 family, limit G. （已译） *)

Definition ff_reflects_limit : IsALimit G (vertex_obj[N]) :=
  @Build_IsALimit J C G (vertex_obj[N]) (@coneFrom _ _ _ N) ff_reflect_ump.

End ReflectLimit.

End FullyFaithful.

(*
   本节说明函子、（余）极限、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition ff_ReflectsLimitCone {C D : Category} {F : C ⟶ D}
  `{HF : @Full C D F} `{HfF : @Faithful C D F} {J : Category} (K : J ⟶ C) :
  ReflectsLimitCone K F :=
  fun N H =>
    @ff_reflect_ump C D F HF HfF J K N (limitcone_isalimit H)
      (fun x => reflexivity _).

Definition ff_reflects_colimit {C D : Category} {F : C ⟶ D}
  `{HF : @Full C D F} `{HfF : @Faithful C D F} {J : Category} {G : J ⟶ C}
  (N : Cocone G)
  (HL : IsAColimit (F ◯ G) (F (vertex_obj[N])))
  (Hinjs : ∀ x : J, colimit_inj HL x ≈ fmap[F] (cocone_inj N x)) :
  IsAColimit G (vertex_obj[N]) :=
  @ff_reflects_limit (C^op) (D^op) (F^op) (Full_op HF) (Faithful_op HfF)
    (J^op) (G^op) N (isalimit_op_comp HL) (fun x => Hinjs x).

Definition ff_ReflectsColimitCocone {C D : Category} {F : C ⟶ D}
  `{HF : @Full C D F} `{HfF : @Faithful C D F} {J : Category} (K : J ⟶ C) :
  ReflectsColimitCocone K F :=
  fun N H =>
    @ff_ReflectsLimitCone (C^op) (D^op) (F^op) (Full_op HF) (Faithful_op HfF)
      (J^op) (K^op) N (islimitcone_op_comp H).

(** ** Equivalences and limits *)

Section EquivalenceLimit.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context (E : @EquivalenceOfCategories C D F).

(** *** Preservation *)

(* Swapping adjoint 等价 refined E exhibits F right
 adjoint (quasi_inverse ⊣ F); RAPL concludes. （已译） *)

Definition equivalence_preserves_limits : PreservesAllLimits F :=
  right_adjoint_preserves_limits
    (AdjointEquivalence_swap_adjunction
       (Equivalence_to_AdjointEquivalence E)).

Definition equivalence_preserves_limit {J : Category} (G : J ⟶ C) :
  PreservesLimit G F :=
  equivalence_preserves_limits J G.

(* Dually, F is the left adjoint of F ⊣ quasi_inverse; LAPC concludes. *)

Definition equivalence_preserves_colimits : PreservesAllColimits F :=
  left_adjoint_preserves_colimits (equiv_adjunction E).

Definition equivalence_preserves_colimit {J : Category} (G : J ⟶ C) :
  PreservesColimit G F :=
  equivalence_preserves_colimits J G.

(* Bundled forms of the preserved (co)limits. *)

Definition equivalence_preserved_limit {J : Category} (G : J ⟶ C)
  (L : Limit G) : Limit (F ◯ G) :=
  isalimit_to_limit
    (@preserves_limit J C G D F (equivalence_preserves_limit G) L).

Definition equivalence_preserved_colimit {J : Category} (G : J ⟶ C)
  (L : Colimit G) : Colimit (F ◯ G) :=
  isalimit_to_limit
    (preserves_colimit (equivalence_preserves_colimit G) L).

(** *** Reflection *)

(* Equivalences 全忠实 (Theory/Equivalence/FullFaithful.v),
 so fully-faithful reflection results specialize. （已译） *)

Definition equivalence_reflects_isos : ReflectsIsos F :=
  ff_reflects_isos
    (HF := Equivalence_Full E) (HfF := Equivalence_Faithful E).

Definition equivalence_reflects_limits {J : Category} {G : J ⟶ C}
  (N : Cone G)
  (HL : IsALimit (F ◯ G) (F (vertex_obj[N])))
  (Hlegs : ∀ x : J, limit_leg HL x ≈ fmap[F] (cone_leg N x)) :
  IsALimit G (vertex_obj[N]) :=
  ff_reflects_limit
    (HF := Equivalence_Full E) (HfF := Equivalence_Faithful E)
    N HL Hlegs.

(** *** Creation *)

(* The 复合 natural 同构 quasi_inverse ◯ (F ◯ G) ≈ G:
 reassociate cancel unit cell. （已译） *)

Definition equivalence_diagram_iso {J : Category} (G : J ⟶ C) :
  @quasi_inverse C D F E ◯ (F ◯ G) ≈ G.
Proof.
  rewrite (fun_equiv_comp_assoc (@quasi_inverse C D F E) F G).
  rewrite <- (@equivalence_unit C D F E).
  exact (fun_equiv_id_left G).
Defined.

(*
   本节说明伴随、（余）极限、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition equivalence_creates_limits {J : Category} (G : J ⟶ C)
  (L : Limit (F ◯ G)) : Limit G :=
  limit_transport (equivalence_diagram_iso G)
    (rapl_limit (equiv_adjunction E) (F ◯ G) L).

End EquivalenceLimit.

(* * ** The opposite 等价 范畴 （已译） *)

(*
   本节说明等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition equivalence_counit_op {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) :
  F^op ◯ (@quasi_inverse C D F E)^op ≈ Id[D^op].
Proof.
  exists (fun d =>
            Isomorphism_Opposite (`1 (@equivalence_counit C D F E) d)).
  intros x y f; simpl.
  rewrite comp_assoc.
  exact (`2 (@equivalence_counit C D F E) y x f).
Defined.

Definition equivalence_unit_op {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) :
  Id[C^op] ≈ (@quasi_inverse C D F E)^op ◯ F^op.
Proof.
  exists (fun x =>
            Isomorphism_Opposite (`1 (@equivalence_unit C D F E) x)).
  intros x y f; simpl.
  rewrite comp_assoc.
  exact (`2 (@equivalence_unit C D F E) y x f).
Defined.

Definition EquivalenceOfCategories_op {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) :
  @EquivalenceOfCategories (C^op) (D^op) (F^op) :=
  @Build_EquivalenceOfCategories (C^op) (D^op) (F^op)
    ((@quasi_inverse C D F E)^op)
    (equivalence_counit_op E)
    (equivalence_unit_op E).

(* 相关说明。 （已译） *)

Section EquivalenceColimit.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context (E : @EquivalenceOfCategories C D F).

(*
   本节说明（余）极限、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition equivalence_reflects_colimits {J : Category} {G : J ⟶ C}
  (N : Cocone G)
  (HL : IsAColimit (F ◯ G) (F (vertex_obj[N])))
  (Hinjs : ∀ x : J, colimit_inj HL x ≈ fmap[F] (cocone_inj N x)) :
  IsAColimit G (vertex_obj[N]) :=
  ff_reflects_limit
    (HF := Equivalence_Full (EquivalenceOfCategories_op E))
    (HfF := Equivalence_Faithful (EquivalenceOfCategories_op E))
    N (isalimit_op_comp HL)
    (fun x => Hinjs x).

(* Creation colimits: repackage given colimit limit of
 F^op ◯ G^op create through opposite 等价. （已译） *)

Definition equivalence_creates_colimits {J : Category} (G : J ⟶ C)
  (L : Colimit (F ◯ G)) : Colimit G :=
  equivalence_creates_limits (EquivalenceOfCategories_op E) (G^op)
    (isalimit_to_limit (isalimit_op_comp (limit_is_alimit L))).

End EquivalenceColimit.
