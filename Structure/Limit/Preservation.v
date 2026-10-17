Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   nLab:      https://ncatlab.org/nlab/show/continuous+functor
   nLab:      https://ncatlab.org/nlab/show/conservative+functor
   Wikipedia:

   本文件给出极限相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Preservation of limits *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class PreservesLimit `(G : J ⟶ C) `(F : C ⟶ D) := {
  preserves_limit (L : Limit G) : IsALimit (F ◯ G) (F L)
}.

(* 相关说明。 （已译） *)

(* The leg cone N at x, first-class function (the notation
 [vertex_map[N]] leaves diagram 对象 hole, so it resists
 explicit application). （已译） *)

Definition cone_leg `{F : J ⟶ C} (N : Cone F) (x : J) :
  vertex_obj[N] ~{C}~> F x :=
  @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x.

(* The legs of a limit witness at a fixed apex c. *)

Definition limit_leg `(H : @IsALimit J C F c) (x : J) : c ~{C}~> F x :=
  @vertex_map _ _ _ _ (@limit_acone _ _ _ _ H) x.

Lemma limit_leg_coherence `(H : @IsALimit J C F c) {x y : J} (f : x ~{J}~> y) :
  fmap[F] f ∘ limit_leg H x ≈ limit_leg H y.
Proof. exact (@cone_coherence _ _ _ _ (@limit_acone _ _ _ _ H) x y f). Qed.

(* The mediating 态射 competing cone 进入 limit apex, and
 defining properties. （已译） *)

Definition limit_med `(H : @IsALimit J C F c) (N : Cone F) :
  vertex_obj[N] ~{C}~> c :=
  unique_obj (@ump_limit _ _ _ _ H N).

Lemma limit_med_commutes `(H : @IsALimit J C F c) (N : Cone F) (x : J) :
  limit_leg H x ∘ limit_med H N ≈ cone_leg N x.
Proof. exact (unique_property (@ump_limit _ _ _ _ H N) x). Qed.

Lemma limit_med_unique `(H : @IsALimit J C F c) (N : Cone F)
  (v : vertex_obj[N] ~{C}~> c) :
  (∀ x : J, limit_leg H x ∘ v ≈ cone_leg N x) →
  limit_med H N ≈ v.
Proof. intro Hv. exact (uniqueness (@ump_limit _ _ _ _ H N) v Hv). Qed.

(* Two 态射 进入 limit apex agree every leg equal;
 useful identifying mediators without naming [limit_med]. （已译） *)

Lemma limit_med_eq `(H : @IsALimit J C F c) (N : Cone F)
  (u v : vertex_obj[N] ~{C}~> c) :
  (∀ x : J, limit_leg H x ∘ u ≈ cone_leg N x) →
  (∀ x : J, limit_leg H x ∘ v ≈ cone_leg N x) →
  u ≈ v.
Proof.
  intros Hu Hv.
  transitivity (limit_med H N).
  - symmetry. exact (limit_med_unique H N u Hu).
  - exact (limit_med_unique H N v Hv).
Qed.

(* A bundled limit, viewed as a limit witness pinned at its own apex. *)

Definition limit_is_alimit `(L : @Limit J C G) : IsALimit G L :=
  @Build_IsALimit _ _ G _
    (@coneFrom _ _ _ (@limit_cone _ _ _ L))
    (@ump_limits _ _ _ L).

(* 相关说明。 （已译） *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition IsLimitCone {J C : Category} {K : J ⟶ C} (N : Cone K) : Type :=
  ∀ M : Cone K, ∃! u : vertex_obj[M] ~{C}~> vertex_obj[N],
    ∀ x : J, cone_leg N x ∘ u ≈ cone_leg M x.

(* The four conversions against existing classes pure repackaging:
 every one term, no 证明 obligation. （已译） *)

Definition limitcone_isalimit {J C : Category} {K : J ⟶ C} {N : Cone K}
  (H : IsLimitCone N) : IsALimit K vertex_obj[N] :=
  @Build_IsALimit J C K vertex_obj[N] (@coneFrom _ _ _ N) H.

Definition isalimit_limitcone {J C : Category} {K : J ⟶ C} {c : C}
  (H : IsALimit K c) :
  @IsLimitCone J C K (@Build_Cone J C K c (@limit_acone _ _ _ _ H)) :=
  @ump_limit _ _ _ _ H.

Definition limit_limitcone {J C : Category} {K : J ⟶ C} (L : Limit K) :
  IsLimitCone (@limit_cone _ _ _ L) := @ump_limits _ _ _ L.

Definition limitcone_limit {J C : Category} {K : J ⟶ C} (N : Cone K)
  (H : IsLimitCone N) : Limit K := @Build_Limit J C K N H.

(** ** Isomorphism of cones *)

(* A cone 同构 同构 apexes commuting legs.
 It [sigT], hence data: comparison 态射 can projected and
 computed with. （已译） *)

Definition ConeIso {J C : Category} {K : J ⟶ C} (N M : Cone K) : Type :=
  { i : vertex_obj[N] ≅ vertex_obj[M]
  & ∀ x : J, cone_leg M x ∘ to i ≈ cone_leg N x }.

Section ConeIsoLemmas.

Context {J C : Category}.
Context {K : J ⟶ C}.

Lemma coneiso_from {N M : Cone K} (i : ConeIso N M) (x : J) :
  cone_leg N x ∘ from `1 i ≈ cone_leg M x.
Proof.
  destruct i as [i Hi]; simpl.
  rewrite <- (Hi x).
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  now rewrite id_right.
Qed.

Definition ConeIso_sym {N M : Cone K} (i : ConeIso N M) : ConeIso M N :=
  (iso_sym `1 i; coneiso_from i).

Definition ConeIso_id (N : Cone K) : ConeIso N N.
Proof.
  exists iso_id.
  intro x; simpl; now rewrite id_right.
Defined.

Definition ConeIso_comp {N M P : Cone K}
  (j : ConeIso M P) (i : ConeIso N M) : ConeIso N P.
Proof.
  exists (iso_compose `1 j `1 i).
  intro x; simpl.
  rewrite comp_assoc.
  rewrite (`2 j x).
  exact (`2 i x).
Defined.

(* Limit-ness is invariant under isomorphism of cones. *)

Lemma limitcone_transport {N M : Cone K} (i : ConeIso N M)
  (HN : IsLimitCone N) : IsLimitCone M.
Proof.
  intro P.
  unshelve refine {| unique_obj := to `1 i ∘ unique_obj (HN P) |}.
  - intro x.
    rewrite comp_assoc.
    rewrite (`2 i x).
    exact (unique_property (HN P) x).
  - intros v Hv.
    assert (Hfv : ∀ x : J, cone_leg N x ∘ (from `1 i ∘ v) ≈ cone_leg P x).
    { intro x.
      rewrite comp_assoc.
      rewrite (coneiso_from i x).
      exact (Hv x). }
    rewrite (uniqueness (HN P) _ Hfv).
    rewrite comp_assoc.
    rewrite iso_to_from.
    now rewrite id_left.
Defined.

(*
   本节说明（余）极限、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition limitcone_iso {N M : Cone K}
  (HN : IsLimitCone N) (HM : IsLimitCone M) : ConeIso N M.
Proof.
  unshelve refine ((_; _)).
  - unshelve refine {| to := unique_obj (HM N); from := unique_obj (HN M) |}.
    + transitivity (unique_obj (HM M)).
      * symmetry.
        apply (uniqueness (HM M)).
        intro x.
        rewrite comp_assoc.
        rewrite (unique_property (HM N) x).
        exact (unique_property (HN M) x).
      * apply (uniqueness (HM M)).
        intro x; now rewrite id_right.
    + transitivity (unique_obj (HN N)).
      * symmetry.
        apply (uniqueness (HN N)).
        intro x.
        rewrite comp_assoc.
        rewrite (unique_property (HN M) x).
        exact (unique_property (HM N) x).
      * apply (uniqueness (HN N)).
        intro x; now rewrite id_right.
  - exact (unique_property (HM N)).
Defined.

End ConeIsoLemmas.

(* * ** The image cone under 函子 （已译） *)

Section ImageCone.

Context {J C D : Category}.
Context (F : C ⟶ D).
Context {K : J ⟶ C}.

(*
   本节说明（余）极限、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma cone_leg_coh (N : Cone K) {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ cone_leg N x ≈ cone_leg N y.
Proof. exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f). Qed.

Definition fcone_leg (N : Cone K) (x : J) :
  F (vertex_obj[N]) ~{D}~> (F ◯ K) x := fmap[F] (cone_leg N x).

Lemma fcone_coherence (N : Cone K) {x y : J} (f : x ~{J}~> y) :
  fmap[F ◯ K] f ∘ fcone_leg N x ≈ fcone_leg N y.
Proof.
  unfold fcone_leg; simpl.
  rewrite <- fmap_comp.
  now rewrite (cone_leg_coh N f).
Qed.

Definition FCone (N : Cone K) : Cone (F ◯ K) :=
  @Build_Cone J D (F ◯ K) (F (vertex_obj[N]))
    (@Build_ACone J D (F (vertex_obj[N])) (F ◯ K) (fcone_leg N)
       (fun x y f => fcone_coherence N f)).

(* The legs [FCone N] ARE image legs, definitionally; 这是 what
 discharges leg side conditions reflection lemmas downstream. （已译） *)

Lemma FCone_leg (N : Cone K) (x : J) :
  cone_leg (FCone N) x ≈ fmap[F] (cone_leg N x).
Proof. reflexivity. Qed.

Definition FCone_iso {N M : Cone K} (i : ConeIso N M) :
  ConeIso (FCone N) (FCone M).
Proof.
  exists (fobj_iso F _ _ `1 i).
  intro x; simpl.
  change (fmap[F] (cone_leg M x) ∘ fmap[F] (to `1 i) ≈ fmap[F] (cone_leg N x)).
  rewrite <- fmap_comp.
  now rewrite (`2 i x).
Defined.

End ImageCone.

(* 相关说明。 （已译） *)

Definition PreservesLimitCone {J C D : Category} (K : J ⟶ C) (F : C ⟶ D)
  : Type := ∀ N : Cone K, IsLimitCone N → IsLimitCone (FCone F N).

Definition ReflectsLimitCone {J C D : Category} (K : J ⟶ C) (F : C ⟶ D)
  : Type := ∀ N : Cone K, IsLimitCone (FCone F N) → IsLimitCone N.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition PreservesLimitCone_PreservesLimit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (P : PreservesLimitCone K F) : PreservesLimit K F.
Proof.
  constructor.
  intro L.
  exact (limitcone_isalimit (P (@limit_cone _ _ _ L) (limit_limitcone L))).
Defined.

(* 相关说明。 （已译） *)

Section Comparison.

Context {J C D : Category}.
Context {K : J ⟶ C}.
Context (F : C ⟶ D).

Definition cone_comparison (N : Cone K) {M : Cone (F ◯ K)}
  (HM : IsLimitCone M) :
  F (vertex_obj[N]) ~{D}~> vertex_obj[M] :=
  unique_obj (HM (FCone F N)).

Lemma cone_comparison_commutes (N : Cone K) {M : Cone (F ◯ K)}
  (HM : IsLimitCone M) (x : J) :
  cone_leg M x ∘ cone_comparison N HM ≈ fmap[F] (cone_leg N x).
Proof. exact (unique_property (HM (FCone F N)) x). Qed.

Lemma cone_comparison_unique (N : Cone K) {M : Cone (F ◯ K)}
  (HM : IsLimitCone M) (v : F (vertex_obj[N]) ~{D}~> vertex_obj[M]) :
  (∀ x : J, cone_leg M x ∘ v ≈ fmap[F] (cone_leg N x)) →
  cone_comparison N HM ≈ v.
Proof. intro Hv. exact (uniqueness (HM (FCone F N)) v Hv). Qed.

(* Cone-level preservation IS invertibility of the comparison, both ways. *)

Definition LimitCone_comparison_iso (N : Cone K) {M : Cone (F ◯ K)}
  (HM : IsLimitCone M) (HN : IsLimitCone (FCone F N)) :
  IsIsomorphism (cone_comparison N HM) :=
  {| two_sided_inverse := from `1 (limitcone_iso HN HM);
     is_right_inverse  := iso_to_from `1 (limitcone_iso HN HM);
     is_left_inverse   := iso_from_to `1 (limitcone_iso HN HM) |}.

Definition comparison_iso_LimitCone (N : Cone K) {M : Cone (F ◯ K)}
  (HM : IsLimitCone M) (Hi : IsIsomorphism (cone_comparison N HM)) :
  IsLimitCone (FCone F N).
Proof.
  assert (ci : ConeIso (FCone F N) M).
  { exists (IsIsoToIso _ Hi).
    intro x; exact (cone_comparison_commutes N HM x). }
  exact (limitcone_transport (ConeIso_sym ci) HM).
Defined.

Definition PreservesLimitCone_of_comparison {M : Cone (F ◯ K)}
  (HM : IsLimitCone M)
  (H : ∀ N : Cone K, IsLimitCone N → IsIsomorphism (cone_comparison N HM)) :
  PreservesLimitCone K F :=
  fun N HN => comparison_iso_LimitCone N HM (H N HN).

Definition comparison_iso_of_PreservesLimitCone
  (P : PreservesLimitCone K F) {M : Cone (F ◯ K)} (HM : IsLimitCone M)
  (N : Cone K) (HN : IsLimitCone N) :
  IsIsomorphism (cone_comparison N HM) :=
  LimitCone_comparison_iso N HM (P N HN).

(*
   本节说明（余）极限、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition apex_iso_of_PreservesLimit (P : PreservesLimit K F) (L : Limit K)
  {M : Cone (F ◯ K)} (HM : IsLimitCone M) :
  F (vertex_obj[L]) ≅ vertex_obj[M] :=
  `1 (limitcone_iso (isalimit_limitcone (preserves_limit L)) HM).

(* 相关说明。 （已译） *)

Definition limit_comparison (L : Limit K) (M : Limit (F ◯ K)) :
  F (vertex_obj[L]) ~{D}~> vertex_obj[M] :=
  cone_comparison (@limit_cone _ _ _ L) (limit_limitcone M).

End Comparison.



(* * ** Repackagings across 函子-复合 associativity op （已译） *)

Section ConeAssoc.

Context {J C D E : Category}.
Context {K : J ⟶ C}.
Context {F : C ⟶ D}.
Context {G : D ⟶ E}.

(* 相关说明。 （已译） *)

Definition cone_assoc (N : Cone ((G ◯ F) ◯ K)) : Cone (G ◯ (F ◯ K)) :=
  @Build_Cone J E (G ◯ (F ◯ K)) (@vertex_obj _ _ _ N)
    (@Build_ACone J E (@vertex_obj _ _ _ N) (G ◯ (F ◯ K))
       (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)).

Definition cone_assoc_inv (N : Cone (G ◯ (F ◯ K))) : Cone ((G ◯ F) ◯ K) :=
  @Build_Cone J E ((G ◯ F) ◯ K) (@vertex_obj _ _ _ N)
    (@Build_ACone J E (@vertex_obj _ _ _ N) ((G ◯ F) ◯ K)
       (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)).

Definition islimitcone_assoc {N : Cone ((G ◯ F) ◯ K)} (H : IsLimitCone N) :
  IsLimitCone (cone_assoc N) := fun M => H (cone_assoc_inv M).

Definition islimitcone_assoc_inv {N : Cone (G ◯ (F ◯ K))}
  (H : IsLimitCone N) : IsLimitCone (cone_assoc_inv N) :=
  fun M => H (cone_assoc M).

End ConeAssoc.

(*
   本节说明（余）极限、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition cone_id_comp@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  (M : Cone K) : Cone (Id ◯ K) :=
  @Build_Cone J C (Id ◯ K) (@vertex_obj _ _ _ M)
    (@Build_ACone J C (@vertex_obj _ _ _ M) (Id ◯ K)
       (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ M) x)
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ M) x y f)).

(* Mac Lane §V.4 Exercise 1, per diagram: the image under G of an
   already-limiting image cone is limiting, so preservation composes. *)
Definition PreservesLimitCone_compose {J C D E : Category}
  {K : J ⟶ C} {F : C ⟶ D} {G : D ⟶ E}
  (PF : PreservesLimitCone K F) (PG : PreservesLimitCone (F ◯ K) G) :
  PreservesLimitCone K (G ◯ F).
Proof.
  intros N HN M.
  exact (PG (FCone F N) (PF N HN) (cone_assoc M)).
Defined.

Section OpComp.

Context {J C D : Category}.
Context {K : J ⟶ C}.
Context {F : C ⟶ D}.

Definition cone_op_comp (N : Cone ((F ◯ K)^op)) : Cone (F^op ◯ K^op) :=
  @Build_Cone (J^op) (D^op) (F^op ◯ K^op) (@vertex_obj _ _ _ N)
    (@Build_ACone (J^op) (D^op) (@vertex_obj _ _ _ N) (F^op ◯ K^op)
       (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)).

Definition cone_op_comp_inv (N : Cone (F^op ◯ K^op)) : Cone ((F ◯ K)^op) :=
  @Build_Cone (J^op) (D^op) ((F ◯ K)^op) (@vertex_obj _ _ _ N)
    (@Build_ACone (J^op) (D^op) (@vertex_obj _ _ _ N) ((F ◯ K)^op)
       (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)).

Definition islimitcone_op_comp {N : Cone ((F ◯ K)^op)} (H : IsLimitCone N) :
  IsLimitCone (cone_op_comp N) := fun M => H (cone_op_comp_inv M).

End OpComp.

(*
   本节说明函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition isalimit_op_comp {J C D : Category} {G : J ⟶ C} {F : C ⟶ D}
  {c : D} (H : IsALimit ((F ◯ G)^op) c) : IsALimit (F^op ◯ G^op) c :=
  @Build_IsALimit (J^op) (D^op) (F^op ◯ G^op) c
    (@Build_ACone (J^op) (D^op) c (F^op ◯ G^op)
       (fun x => @vertex_map _ _ _ _ (@limit_acone _ _ _ _ H) x)
       (fun x y f =>
          @cone_coherence _ _ _ _ (@limit_acone _ _ _ _ H) x y f))
    (fun N =>
       @ump_limit _ _ _ _ H
         (@Build_Cone (J^op) (D^op) ((F ◯ G)^op) (@vertex_obj _ _ _ N)
            (@Build_ACone (J^op) (D^op) (@vertex_obj _ _ _ N) ((F ◯ G)^op)
               (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
               (fun x y f =>
                  @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)))).


(* 相关说明。 （已译） *)

(* A cocone over F cone over F^op (Structure/Cone.v); legs run
 diagram 进入 apex. [cocone_inj] re-reads those legs
 covariantly, injections F x ~> N C. （已译） *)

Definition cocone_inj `{F : J ⟶ C} (N : Cocone F) (x : J) :
  F x ~{C}~> vertex_obj[N] :=
  @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x.

Lemma cocone_inj_coherence `{F : J ⟶ C} (N : Cocone F)
  {x y : J} (f : x ~{J}~> y) :
  cocone_inj N y ∘ fmap[F] f ≈ cocone_inj N x.
Proof. exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) y x f). Qed.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition IsAColimit `(F : J ⟶ C) (c : C) : Type := IsALimit (F^op) c.

(* 相关说明。 （已译） *)

Definition colimit_inj `(H : @IsAColimit J C F c) (x : J) : F x ~{C}~> c :=
  @vertex_map _ _ _ _ (@limit_acone _ _ _ _ H) x.

Lemma colimit_inj_coherence `(H : @IsAColimit J C F c) {x y : J}
  (f : x ~{J}~> y) :
  colimit_inj H y ∘ fmap[F] f ≈ colimit_inj H x.
Proof. exact (@cone_coherence _ _ _ _ (@limit_acone _ _ _ _ H) y x f). Qed.

(* Universal property, covariantly: every cocone N over F factors through
   the colimit apex by a unique mediating morphism out of c. Transparent,
   so downstream constructions can extract the mediator. *)

Definition ump_colimit `(H : @IsAColimit J C F c) (N : Cocone F) :
  ∃! u : c ~{C}~> vertex_obj[N],
    ∀ x : J, u ∘ colimit_inj H x ≈ cocone_inj N x.
Proof. exact (@ump_limit _ _ _ _ H N). Defined.

Definition colimit_med `(H : @IsAColimit J C F c) (N : Cocone F) :
  c ~{C}~> vertex_obj[N] :=
  unique_obj (ump_colimit H N).

Lemma colimit_med_commutes `(H : @IsAColimit J C F c) (N : Cocone F) (x : J) :
  colimit_med H N ∘ colimit_inj H x ≈ cocone_inj N x.
Proof. exact (unique_property (ump_colimit H N) x). Qed.

Lemma colimit_med_unique `(H : @IsAColimit J C F c) (N : Cocone F)
  (v : c ~{C}~> vertex_obj[N]) :
  (∀ x : J, v ∘ colimit_inj H x ≈ cocone_inj N x) →
  colimit_med H N ≈ v.
Proof. intro Hv. exact (uniqueness (ump_colimit H N) v Hv). Qed.

Lemma colimit_med_eq `(H : @IsAColimit J C F c) (N : Cocone F)
  (u v : c ~{C}~> vertex_obj[N]) :
  (∀ x : J, u ∘ colimit_inj H x ≈ cocone_inj N x) →
  (∀ x : J, v ∘ colimit_inj H x ≈ cocone_inj N x) →
  u ≈ v.
Proof.
  intros Hu Hv.
  transitivity (colimit_med H N).
  - symmetry. exact (colimit_med_unique H N u Hu).
  - exact (colimit_med_unique H N v Hv).
Qed.

(* The apex bundled colimit, read 对象 C, bundled
 colimit viewed colimit witness pinned at apex. （已译） *)

Definition colimit_apex `(L : @Colimit J C G) : C :=
  @vertex_obj _ _ _ (@limit_cone _ _ _ L).

Definition colimit_is_acolimit `(L : @Colimit J C G) :
  IsAColimit G (colimit_apex L) :=
  @Build_IsALimit _ _ (G^op) _
    (@coneFrom _ _ _ (@limit_cone _ _ _ L))
    (@ump_limits _ _ _ L).

(** ** Preservation of colimits *)

(* F preserves colimit G exactly F^op preserves limit of
 opposite diagram G^op; 这是 one-line dual 定义, the
 style [Colimit] itself. （已译） *)

Definition PreservesColimit `(G : J ⟶ C) `(F : C ⟶ D) : Type :=
  @PreservesLimit (J^op) (C^op) (G^op) (D^op) (F^op).

(*
   本节说明函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition preserves_colimit {J C D : Category} {G : J ⟶ C} {F : C ⟶ D}
  (P : PreservesColimit G F) (L : Colimit G) :
  IsAColimit (F ◯ G) (F (colimit_apex L)).
Proof.
  destruct (@preserves_limit _ _ _ _ _ P L) as [ac um].
  unshelve refine (@Build_IsALimit _ _ ((F ◯ G)^op) _ _ _).
  - exact (@Build_ACone _ _ _ ((F ◯ G)^op)
      (fun x => @vertex_map _ _ _ _ ac x)
      (fun x y f => @cone_coherence _ _ _ _ ac x y f)).
  - intro N.
    exact (um (@Build_Cone _ _ (F^op ◯ G^op)
      (@vertex_obj _ _ _ N)
      (@Build_ACone _ _ _ (F^op ◯ G^op)
         (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
         (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)))).
Defined.

(** ** Continuity and cocontinuity *)

(* A functor preserving the limits of all diagrams of all shapes
   (continuous), respectively all colimits (cocontinuous). These are plain
   Definitions: preservation of a class of limits is data to be supplied,
   never inferred. *)

Definition PreservesAllLimits {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (G : J ⟶ C), PreservesLimit G F.

Definition PreservesAllColimits {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (G : J ⟶ C), PreservesColimit G F.

(* 相关说明。 （已译） *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition ContinuousFunctor {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), PreservesLimitCone K F.

Definition Continuous_PreservesAllLimits {C D : Category} {F : C ⟶ D}
  (H : ContinuousFunctor F) : PreservesAllLimits F :=
  fun J K => PreservesLimitCone_PreservesLimit (H J K).

(* Riehl §3.4: preservation over all diagrams of a given shape, and over an
   arbitrary class of shapes. *)

Definition PreservesLimitConesOfShape (J : Category) {C D : Category}
  (F : C ⟶ D) : Type := ∀ K : J ⟶ C, PreservesLimitCone K F.

Definition PreservesLimitConesOver {C D : Category} (S : Category → Type)
  (F : C ⟶ D) : Type :=
  ∀ J : Category, S J → ∀ K : J ⟶ C, PreservesLimitCone K F.

Definition Continuous_PreservesLimitConesOver {C D : Category}
  {S : Category → Type} {F : C ⟶ D} (H : ContinuousFunctor F) :
  PreservesLimitConesOver S F := fun J _ K => H J K.

Definition Continuous_OfShape {C D : Category} {F : C ⟶ D}
  (H : ContinuousFunctor F) (J : Category) :
  PreservesLimitConesOfShape J F := H J.

(* Mac Lane §V.4 Exercise 1 at full strength. *)

Definition continuous_compose {C D E : Category} {F : C ⟶ D} {G : D ⟶ E}
  (PF : ContinuousFunctor F) (PG : ContinuousFunctor G) :
  ContinuousFunctor (G ◯ F) :=
  fun J K => PreservesLimitCone_compose (PF J K) (PG J (F ◯ K)).

(** ** Reflection of isomorphisms *)

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class ReflectsIsos {C D : Category} (F : C ⟶ D) := {
  reflects_iso {x y : C} (f : x ~> y) :
    IsIsomorphism (fmap[F] f) → IsIsomorphism f
}.

(* 相关说明。 （已译） *)

(*
   本节说明 Preservation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition IsColimitCocone {J C : Category} {K : J ⟶ C} (N : Cocone K) : Type :=
  @IsLimitCone (J^op) (C^op) (K^op) N.

Definition colimitcocone_ump {J C : Category} {K : J ⟶ C} {N : Cocone K}
  (H : IsColimitCocone N) (M : Cocone K) :
  ∃! u : vertex_obj[N] ~{C}~> vertex_obj[M],
    ∀ x : J, u ∘ cocone_inj N x ≈ cocone_inj M x := H M.

Definition colimitcocone_isacolimit {J C : Category} {K : J ⟶ C}
  {N : Cocone K} (H : IsColimitCocone N) : IsAColimit K vertex_obj[N] :=
  limitcone_isalimit H.

Definition colimit_colimitcocone {J C : Category} {K : J ⟶ C}
  (L : Colimit K) : IsColimitCocone (@limit_cone _ _ _ L) :=
  @ump_limits _ _ _ L.

Section ImageCocone.

Context {J C D : Category}.
Context (F : C ⟶ D).
Context {K : J ⟶ C}.

Definition fcocone_inj (N : Cocone K) (x : J) :
  (F ◯ K) x ~{D}~> F (vertex_obj[N]) := fmap[F] (cocone_inj N x).

Lemma fcocone_coherence (N : Cocone K) {x y : J} (f : x ~{J}~> y) :
  fcocone_inj N y ∘ fmap[F ◯ K] f ≈ fcocone_inj N x.
Proof.
  unfold fcocone_inj; simpl.
  rewrite <- fmap_comp.
  now rewrite (cocone_inj_coherence N f).
Qed.

Definition FCocone (N : Cocone K) : Cocone (F ◯ K).
Proof.
  unshelve refine (@Build_Cone (J^op) (D^op) ((F ◯ K)^op)
                     (F (vertex_obj[N])) _).
  unshelve refine (@Build_ACone (J^op) (D^op) (F (vertex_obj[N]))
                     ((F ◯ K)^op) (fcocone_inj N) _).
  intros x y f; exact (fcocone_coherence N f).
Defined.

Lemma FCocone_inj (N : Cocone K) (x : J) :
  cocone_inj (FCocone N) x ≈ fmap[F] (cocone_inj N x).
Proof. reflexivity. Qed.

Definition cocone_comparison (N : Cocone K) {M : Cocone (F ◯ K)}
  (HM : IsColimitCocone M) :
  vertex_obj[M] ~{D}~> F (vertex_obj[N]) :=
  unique_obj (HM (FCocone N)).

End ImageCocone.

(* The cocone twin [FCone_iso]: image cocone 同构 is
 one. Added #477, tree having had no cocone twin, with
 Structure/Limit/Absolute.v's binders. （已译） *)

Definition FCocone_iso@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}}
  {D : Category@{do ch ch}} (F : C ⟶ D) {K : J ⟶ C} {N M : Cocone K}
  (i : ConeIso N M) : ConeIso (FCocone F N) (FCocone F M).
Proof.
  exists (fobj_iso (F^op) _ _ `1 i).
  intro x.
  change (fmap[F] (to `1 i) ∘ fmap[F] (cocone_inj M x)
            ≈ fmap[F] (cocone_inj N x)).
  rewrite <- fmap_comp.
  apply fmap_respects.
  exact (`2 i x).
Defined.

Definition PreservesColimitCocone {J C D : Category}
  (K : J ⟶ C) (F : C ⟶ D) : Type :=
  ∀ N : Cocone K, IsColimitCocone N → IsColimitCocone (FCocone F N).

Definition ReflectsColimitCocone {J C D : Category}
  (K : J ⟶ C) (F : C ⟶ D) : Type :=
  ∀ N : Cocone K, IsColimitCocone (FCocone F N) → IsColimitCocone N.

Definition PreservesColimitCocone_PreservesColimit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (P : PreservesColimitCocone K F) :
  PreservesColimit K F.
Proof.
  constructor.
  intro L.
  exact (isalimit_op_comp
           (limitcone_isalimit
              (P (@limit_cone _ _ _ L) (limit_limitcone L)))).
Defined.

Section CoCompose.

Context {J C D E : Category}.
Context {K : J ⟶ C}.
Context {F : C ⟶ D}.
Context {G : D ⟶ E}.

Definition cocone_assoc (N : Cocone ((G ◯ F) ◯ K)) : Cocone (G ◯ (F ◯ K)) :=
  @Build_Cone (J^op) (E^op) ((G ◯ (F ◯ K))^op) (@vertex_obj _ _ _ N)
    (@Build_ACone (J^op) (E^op) (@vertex_obj _ _ _ N) ((G ◯ (F ◯ K))^op)
       (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)).

Definition PreservesColimitCocone_compose
  (PF : PreservesColimitCocone K F) (PG : PreservesColimitCocone (F ◯ K) G) :
  PreservesColimitCocone K (G ◯ F).
Proof.
  intros N HN M.
  exact (PG (FCocone F N) (PF N HN) (cocone_assoc M)).
Defined.

End CoCompose.

(* 相关说明。 （已译） *)

Definition cocone_assoc_inv@{jo co ch do eo +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}}
  {D : Category@{do ch ch}} {E : Category@{eo ch ch}}
  {K : J ⟶ C} {F : C ⟶ D} {G : D ⟶ E}
  (N : Cocone (G ◯ (F ◯ K))) : Cocone ((G ◯ F) ◯ K) :=
  @Build_Cone (J^op) (E^op) (((G ◯ F) ◯ K)^op) (@vertex_obj _ _ _ N)
    (@Build_ACone (J^op) (E^op) (@vertex_obj _ _ _ N) (((G ◯ F) ◯ K)^op)
       (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)).

Definition CocontinuousFunctor {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), PreservesColimitCocone K F.

Definition Cocontinuous_PreservesAllColimits {C D : Category} {F : C ⟶ D}
  (H : CocontinuousFunctor F) : PreservesAllColimits F :=
  fun J K => PreservesColimitCocone_PreservesColimit (H J K).

Definition PreservesColimitCoconesOfShape (J : Category) {C D : Category}
  (F : C ⟶ D) : Type := ∀ K : J ⟶ C, PreservesColimitCocone K F.

Definition cocontinuous_compose {C D E : Category} {F : C ⟶ D} {G : D ⟶ E}
  (PF : CocontinuousFunctor F) (PG : CocontinuousFunctor G) :
  CocontinuousFunctor (G ◯ F) :=
  fun J K => PreservesColimitCocone_compose (PF J K) (PG J (F ◯ K)).
