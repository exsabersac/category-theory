Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Discrete.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(* * * Creation limits colimits 函子 （已译） *)

(*
   nLab:      https://ncatlab.org/nlab/show/preserved+limit

   本文件给出极限/余极限的创造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

(*
   本节说明（余）极限、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class CreatesLimit {J C D : Category} (K : J ⟶ C) (F : C ⟶ D) := {
  creates_lift (N : Cone (F ◯ K)) (HN : IsLimitCone N) : Cone K;
  creates_lift_over (N : Cone (F ◯ K)) (HN : IsLimitCone N) :
    ConeIso (FCone F (creates_lift N HN)) N;
  creates_reflect (M : Cone K) : IsLimitCone (FCone F M) → IsLimitCone M
}.

(* 相关说明。 （已译） *)

Definition creates_limiting {J C D : Category} {K : J ⟶ C} {F : C ⟶ D}
  (CR : CreatesLimit K F) (N : Cone (F ◯ K)) (HN : IsLimitCone N) :
  IsLimitCone (creates_lift N HN) :=
  creates_reflect (creates_lift N HN)
    (limitcone_transport (ConeIso_sym (creates_lift_over N HN)) HN).

(*
   本节说明单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition creates_lift_unique {J C D : Category} {K : J ⟶ C} {F : C ⟶ D}
  (CR : CreatesLimit K F) (N : Cone (F ◯ K)) (HN : IsLimitCone N)
  (M : Cone K) (j : ConeIso (FCone F M) N) :
  ConeIso M (creates_lift N HN) :=
  limitcone_iso
    (creates_reflect M (limitcone_transport (ConeIso_sym j) HN))
    (creates_limiting CR N HN).

(* Creation entails reflection (Riehl §3.4, the remark following Definition
   3.4.1): here, definitionally. *)

Definition creates_reflects_limits {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (CR : CreatesLimit K F) : ReflectsLimitCone K F :=
  @creates_reflect J C D K F CR.

(* The existence half, bundled: a limit downstairs yields a limit upstairs. *)

Definition creates_limit_lift {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (CR : CreatesLimit K F) (L : Limit (F ◯ K)) :
  Limit K :=
  @Build_Limit J C K
    (creates_lift (@limit_cone _ _ _ L) (limit_limitcone L))
    (creates_limiting CR (@limit_cone _ _ _ L) (limit_limitcone L)).

(* 相关说明。 （已译） *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem creation_preserves_limit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (CR : CreatesLimit K F) (L : Limit (F ◯ K)) :
  PreservesLimitCone K F.
Proof.
  intros M HM.
  (* 相关说明。 （已译） *)
  pose (N := @limit_cone _ _ _ L).
  pose (HN := limit_limitcone L).
  pose (M' := creates_lift N HN).
  pose (HM' := creates_limiting CR N HN).
  (* 相关说明。 （已译） *)
  pose (i := limitcone_iso HM' HM).
  (* transport limit-ness along  N ≅ F M' ≅ F M *)
  exact (limitcone_transport
           (ConeIso_comp (FCone_iso F i)
              (ConeIso_sym (creates_lift_over N HN))) HN).
Defined.

(** ** Shape-quantified creation *)

Definition CreatesLimitsOfShape (J : Category) {C D : Category} (F : C ⟶ D)
  : Type := ∀ K : J ⟶ C, CreatesLimit K F.

Definition CreatesAllLimits {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), CreatesLimit K F.

(* "Creates products" is the discrete-shape case, over
   Instance/Discrete.v's [DiscreteCat], mirroring how
   Structure/Limit/Product.v reaches indexed products. *)

Definition CreatesProducts {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (A : Type) (K : DiscreteCat A ⟶ C), CreatesLimit K F.

Definition CreatesAllLimits_CreatesProducts {C D : Category} {F : C ⟶ D}
  (CR : CreatesAllLimits F) : CreatesProducts F :=
  fun A K => CR (DiscreteCat A) K.

(* 相关说明。 （已译） *)

(* Creation of all limits transports completeness ... *)

Definition creates_limits_Complete {C D : Category} (F : C ⟶ D)
  (HD : @Complete D) (CR : CreatesAllLimits F) : @Complete C :=
  fun J K => creates_limit_lift (CR J K) (HD J (F ◯ K)).

(* ... makes 函子 continuous, at cone level ... （已译） *)

Definition creates_limits_continuous {C D : Category} (F : C ⟶ D)
  (HD : @Complete D) (CR : CreatesAllLimits F) :
  ∀ (J : Category) (K : J ⟶ C), PreservesLimitCone K F :=
  fun J K => creation_preserves_limit (CR J K) (HD J (F ◯ K)).

(* 相关说明。 （已译） *)

Definition creates_limits_PreservesAllLimits {C D : Category} (F : C ⟶ D)
  (HD : @Complete D) (CR : CreatesAllLimits F) : PreservesAllLimits F :=
  fun J K => PreservesLimitCone_PreservesLimit
               (creates_limits_continuous F HD CR J K).

(* 相关说明。 （已译） *)

(* Transport 态射 along equality domain. Objects use
 [eq]; 态射 still compared [≈]. （已译） *)

Definition hom_rew {D : Category} {d d' : D} (p : d = d') {t : D}
  (f : d ~{D}~> t) : d' ~{D}~> t :=
  match p in _ = z return z ~{D}~> t with eq_refl => f end.

(* The 同构 induced equality 对象. Deliberately not
 named [iso_of_eq]: name taken Instance/StrictCat/ToCat.v,
 Structure-layer file must not import. （已译） *)

Definition obj_eq_iso {D : Category} {d d' : D} (p : d = d') : d ≅ d' :=
  match p in _ = z return d ≅ z with eq_refl => iso_id end.

Lemma hom_rew_obj_eq_iso {D : Category} {d d' : D} (p : d = d') {t : D}
  (f : d ~{D}~> t) (g : d' ~{D}~> t) :
  hom_rew p f ≈ g → g ∘ to (obj_eq_iso p) ≈ f.
Proof. destruct p; simpl; intro H. rewrite id_right. now symmetry. Qed.

(* 相关说明。 （已译） *)

Record StrictLift {J C D : Category} (K : J ⟶ C) (F : C ⟶ D)
  (N : Cone (F ◯ K)) := {
  slift_cone : Cone K;
  slift_eq   : F (vertex_obj[slift_cone]) = vertex_obj[N];
  slift_legs : ∀ x : J,
    hom_rew slift_eq (fmap[F] (cone_leg slift_cone x)) ≈ cone_leg N x
}.

Arguments slift_cone {J C D K F N} _.
Arguments slift_eq {J C D K F N} _.
Arguments slift_legs {J C D K F N} _ _.

Definition slift_iso {J C D : Category} {K : J ⟶ C} {F : C ⟶ D}
  {N : Cone (F ◯ K)} (L : StrictLift K F N) :
  F (vertex_obj[slift_cone L]) ≅ vertex_obj[N] := obj_eq_iso (slift_eq L).

Lemma slift_iso_legs {J C D : Category} {K : J ⟶ C} {F : C ⟶ D}
  {N : Cone (F ◯ K)} (L : StrictLift K F N) (x : J) :
  cone_leg N x ∘ to (slift_iso L) ≈ fmap[F] (cone_leg (slift_cone L) x).
Proof. exact (hom_rew_obj_eq_iso _ _ _ (slift_legs L x)). Qed.

(* Every cone upstairs is tautologically 严格 lift its own image.
 Provided reference: it has no consumer here, 唯一性 clause
 it was intended feed having become derived
 [screates_lift_unique] rather than field.（已译） *)

Definition self_lift {J C D : Category} {K : J ⟶ C} {F : C ⟶ D}
  (M : Cone K) : StrictLift K F (FCone F M) :=
  @Build_StrictLift J C D K F (FCone F M) M eq_refl (fun x => reflexivity _).

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class StrictlyCreatesLimit {J C D : Category} (K : J ⟶ C) (F : C ⟶ D) := {
  screates (N : Cone (F ◯ K)) (HN : IsLimitCone N) : StrictLift K F N;
  screates_limiting (N : Cone (F ◯ K)) (HN : IsLimitCone N) :
    IsLimitCone (slift_cone (screates N HN));
  screates_reflect (M : Cone K) : IsLimitCone (FCone F M) → IsLimitCone M
}.

Definition StrictlyCreatesLimit_CreatesLimit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (SC : StrictlyCreatesLimit K F) :
  CreatesLimit K F.
Proof.
  unshelve refine {| creates_lift := fun N HN => slift_cone (screates N HN) |}.
  - intros N HN.
    exists (slift_iso (screates N HN)).
    intro x.
    exact (slift_iso_legs (screates N HN) x).
  - exact screates_reflect.
Defined.

Definition screates_lift_unique {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (SC : StrictlyCreatesLimit K F)
  (N : Cone (F ◯ K)) (HN : IsLimitCone N)
  (M : Cone K) (j : ConeIso (FCone F M) N) :
  ConeIso M (slift_cone (screates N HN)) :=
  creates_lift_unique (StrictlyCreatesLimit_CreatesLimit SC) N HN M j.

Definition StrictlyCreatesLimitsOfShape (J : Category) {C D : Category}
  (F : C ⟶ D) : Type := ∀ K : J ⟶ C, StrictlyCreatesLimit K F.

Definition StrictlyCreatesLimits {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), StrictlyCreatesLimit K F.

(** ** Creation composes *)

Section Compose.

Context {J C D E : Category}.
Context {K : J ⟶ C}.
Context {F : C ⟶ D}.
Context {G : D ⟶ E}.

Definition CreatesLimit_compose
  (CF : CreatesLimit K F) (CG : CreatesLimit (F ◯ K) G) :
  CreatesLimit K (G ◯ F).
Proof.
  unshelve refine {| creates_lift := _ |}.
  - (* the two-stage lift *)
    intros N HN.
    exact (creates_lift
             (creates_lift (cone_assoc N) (islimitcone_assoc HN))
             (creates_limiting CG (cone_assoc N) (islimitcone_assoc HN))).
  - (* the comparison isomorphism *)
    intros N HN; simpl.
    set (mid := creates_lift (cone_assoc N) (islimitcone_assoc HN)).
    set (Hmid := creates_limiting CG (cone_assoc N) (islimitcone_assoc HN)).
    pose (iF := creates_lift_over mid Hmid).
    pose (iG := creates_lift_over (cone_assoc N) (islimitcone_assoc HN)).
    exists (iso_compose `1 iG (fobj_iso G _ _ `1 iF)).
    intro x.
    assert (H1 : cone_leg N x ∘ to `1 iG ≈ fmap[G] (cone_leg mid x))
      by exact (`2 iG x).
    transitivity ((cone_leg N x ∘ to `1 iG) ∘ fmap[G] (to `1 iF)).
    + apply comp_assoc.
    + rewrite H1.
      transitivity (fmap[G] (cone_leg mid x ∘ to `1 iF)).
      * exact (symmetry (@fmap_comp _ _ G _ _ _ (cone_leg mid x) (to `1 iF))).
      * exact (@fmap_respects _ _ G _ _ _ _ (`2 iF x)).
  - (* reflection, one stage at a time *)
    intros M H.
    apply (creates_reflect (F:=F)).
    apply (creates_reflect (F:=G)).
    exact (fun M0 => H (cone_assoc_inv M0)).
Defined.

End Compose.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)

Definition CreatesColimit `(K : J ⟶ C) `(F : C ⟶ D) : Type :=
  @CreatesLimit (J^op) (C^op) (D^op) (K^op) (F^op).

Definition StrictlyCreatesColimit `(K : J ⟶ C) `(F : C ⟶ D) : Type :=
  @StrictlyCreatesLimit (J^op) (C^op) (D^op) (K^op) (F^op).

Definition CreatesAllColimits {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), CreatesColimit K F.

Section Dual.

Context {J C D : Category}.
Context {K : J ⟶ C}.
Context {F : C ⟶ D}.

Definition colimit_op_comp (L : Colimit (F ◯ K)) : Limit (F^op ◯ K^op) :=
  @Build_Limit (J^op) (D^op) (F^op ◯ K^op)
    (cone_op_comp (@limit_cone _ _ _ L))
    (islimitcone_op_comp (limit_limitcone L)).

Definition creates_colimit_lift (CR : CreatesColimit K F)
  (L : Colimit (F ◯ K)) : Colimit K :=
  creates_limit_lift CR (colimit_op_comp L).

(* The dual of §V.4 Theorem 2's first half, stated in op form. *)

Definition creation_preserves_colimit (CR : CreatesColimit K F)
  (L : Colimit (F ◯ K)) : PreservesLimitCone (K^op) (F^op) :=
  creation_preserves_limit CR (colimit_op_comp L).

End Dual.

Definition creates_colimits_Cocomplete {C D : Category} (F : C ⟶ D)
  (HD : @Cocomplete D) (CR : CreatesAllColimits F) : @Cocomplete C :=
  fun J K => creates_colimit_lift (CR J K) (HD J (F ◯ K)).

(* 相关说明。 （已译） *)

(*
   本节说明函子、（余）极限、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class JointlyCreateLimit {J C : Category} (K : J ⟶ C)
  {I : Type} {D : I → Category} (F : ∀ i : I, C ⟶ D i) := {
  jcreates_lift (N : ∀ i : I, Cone (F i ◯ K))
    (HN : ∀ i : I, IsLimitCone (N i)) : Cone K;
  jcreates_lift_over (N : ∀ i : I, Cone (F i ◯ K))
    (HN : ∀ i : I, IsLimitCone (N i)) (i : I) :
    ConeIso (FCone (F i) (jcreates_lift N HN)) (N i);
  jcreates_reflect (M : Cone K) :
    (∀ i : I, IsLimitCone (FCone (F i) M)) → IsLimitCone M
}.

Definition jcreates_limiting {J C : Category} {K : J ⟶ C}
  {I : Type} {D : I → Category} {F : ∀ i : I, C ⟶ D i}
  (JC : JointlyCreateLimit K F)
  (N : ∀ i : I, Cone (F i ◯ K)) (HN : ∀ i : I, IsLimitCone (N i)) :
  IsLimitCone (jcreates_lift N HN) :=
  jcreates_reflect (jcreates_lift N HN)
    (fun i => limitcone_transport
                (ConeIso_sym (jcreates_lift_over N HN i)) (HN i)).

Definition jcreates_lift_unique {J C : Category} {K : J ⟶ C}
  {I : Type} {D : I → Category} {F : ∀ i : I, C ⟶ D i}
  (JC : JointlyCreateLimit K F)
  (N : ∀ i : I, Cone (F i ◯ K)) (HN : ∀ i : I, IsLimitCone (N i))
  (M : Cone K) (j : ∀ i : I, ConeIso (FCone (F i) M) (N i)) :
  ConeIso M (jcreates_lift N HN) :=
  limitcone_iso
    (jcreates_reflect M
       (fun i => limitcone_transport (ConeIso_sym (j i)) (HN i)))
    (jcreates_limiting JC N HN).

Definition jcreates_limit_lift {J C : Category} {K : J ⟶ C}
  {I : Type} {D : I → Category} {F : ∀ i : I, C ⟶ D i}
  (JC : JointlyCreateLimit K F) (L : ∀ i : I, Limit (F i ◯ K)) : Limit K :=
  @Build_Limit J C K
    (jcreates_lift (fun i => @limit_cone _ _ _ (L i))
       (fun i => limit_limitcone (L i)))
    (jcreates_limiting JC _ _).

(* A single 函子 one-member family, both ways. [unit] the
 index; reflection clause lift literally same data. （已译） *)

Definition JointlyCreateLimit_of_CreatesLimit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (CR : CreatesLimit K F) :
  JointlyCreateLimit K (fun _ : unit => F) := {|
  jcreates_lift := fun N HN => creates_lift (N tt) (HN tt);
  jcreates_lift_over := fun N HN i =>
    match i as u
      return ConeIso (FCone F (creates_lift (N tt) (HN tt))) (N u)
    with tt => creates_lift_over (N tt) (HN tt) end;
  jcreates_reflect := fun M H => creates_reflect M (H tt)
|}.

Definition CreatesLimit_of_JointlyCreateLimit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D}
  (JC : JointlyCreateLimit K (fun _ : unit => F)) : CreatesLimit K F := {|
  creates_lift := fun N HN => jcreates_lift (fun _ => N) (fun _ => HN);
  creates_lift_over := fun N HN =>
    jcreates_lift_over (fun _ => N) (fun _ => HN) tt;
  creates_reflect := fun M H => jcreates_reflect M (fun _ => H)
|}.
