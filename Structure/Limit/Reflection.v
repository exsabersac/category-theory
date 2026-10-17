Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.CokernelPair.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Parallel.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(** * Reflection of limits, colimits and coequalizers *)

(*
   Book:   Riehl, "Category Theory in Context", 2nd ed., §3.4:
   nLab:   https://ncatlab.org/nlab/show/reflected+limit
   nLab:   https://ncatlab.org/nlab/show/conservative+functor

   本文件给出极限相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Reflection over a shape, a class of shapes or diagrams, and all *)

Definition ReflectsLimitConesOfShape (J : Category) {C D : Category}
  (F : C ⟶ D) : Type := ∀ K : J ⟶ C, ReflectsLimitCone K F.

Definition ReflectsLimitConesOver {C D : Category} (S : Category → Type)
  (F : C ⟶ D) : Type :=
  ∀ J : Category, S J → ∀ K : J ⟶ C, ReflectsLimitCone K F.

(* Over a class of diagrams, Riehl's own quantifier: a predicate on the
   diagrams K of every shape J.  A class of shapes S is the class of all
   diagrams of those shapes, [fun J _ => S J], and the two forms agree up
   to the order of their arguments, by the two maps below, each the
   other's inverse at [eq_refl] (the probe, C23 and C24). *)

Definition ReflectsLimitConesOfClass {C D : Category}
  (S : ∀ J : Category, (J ⟶ C) → Type) (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), S J K → ReflectsLimitCone K F.

Definition ReflectsLimitConesOver_OfClass {C D : Category}
  {S : Category → Type} {F : C ⟶ D} (H : ReflectsLimitConesOver S F) :
  ReflectsLimitConesOfClass (fun J _ => S J) F :=
  fun J K HJ => H J HJ K.

Definition ReflectsLimitConesOfClass_Over {C D : Category}
  {S : Category → Type} {F : C ⟶ D}
  (H : ReflectsLimitConesOfClass (fun J _ => S J) F) :
  ReflectsLimitConesOver S F :=
  fun J HJ K => H J K HJ.

Definition ReflectsAllLimits {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), ReflectsLimitCone K F.

Definition ReflectsAllLimits_Over {C D : Category} {S : Category → Type}
  {F : C ⟶ D} (H : ReflectsAllLimits F) : ReflectsLimitConesOver S F :=
  fun J _ K => H J K.

Definition ReflectsColimitCoconesOfShape (J : Category) {C D : Category}
  (F : C ⟶ D) : Type := ∀ K : J ⟶ C, ReflectsColimitCocone K F.

Definition ReflectsColimitCoconesOver {C D : Category}
  (S : Category → Type) (F : C ⟶ D) : Type :=
  ∀ J : Category, S J → ∀ K : J ⟶ C, ReflectsColimitCocone K F.

Definition ReflectsColimitCoconesOfClass {C D : Category}
  (S : ∀ J : Category, (J ⟶ C) → Type) (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), S J K → ReflectsColimitCocone K F.

Definition ReflectsColimitCoconesOver_OfClass {C D : Category}
  {S : Category → Type} {F : C ⟶ D} (H : ReflectsColimitCoconesOver S F) :
  ReflectsColimitCoconesOfClass (fun J _ => S J) F :=
  fun J K HJ => H J HJ K.

Definition ReflectsColimitCoconesOfClass_Over {C D : Category}
  {S : Category → Type} {F : C ⟶ D}
  (H : ReflectsColimitCoconesOfClass (fun J _ => S J) F) :
  ReflectsColimitCoconesOver S F :=
  fun J HJ K => H J K HJ.

Definition ReflectsAllColimits {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), ReflectsColimitCocone K F.

Definition ReflectsAllColimits_Over {C D : Category} {S : Category → Type}
  {F : C ⟶ D} (H : ReflectsAllColimits F) : ReflectsColimitCoconesOver S F :=
  fun J _ K => H J K.

(** ** A conservative functor's opposite is conservative *)

(* An isomorphism of C^op is one of C with its two laws exchanged;
   Theory/Morphisms/CokernelPair.v's [IsIsomorphism_of_op] and
   [op_IsIsomorphism_of] read it across, in D and in C. *)

Definition ReflectsIsos_op {C D : Category} {F : C ⟶ D}
  (R : ReflectsIsos F) : ReflectsIsos (F^op) :=
  @Build_ReflectsIsos (C^op) (D^op) (F^op)
    (fun x y f I =>
       @op_IsIsomorphism_of C x y f
         (@reflects_iso C D F R y x f (IsIsomorphism_of_op (fmap[F] f) I))).

(** ** Creation gives reflection: the colimit side *)

(* The colimit twin of Structure/Limit/Creation.v's
   [creates_reflects_limits].  [CreatesColimit K F] is [CreatesLimit] of
   [K^op] along [F^op], whose reflection field asks for the image cone over
   [F^op ◯ K^op]; Structure/Limit/Preservation.v's [islimitcone_op_comp]
   reaches it from the image cocone over [(F ◯ K)^op]. *)

Definition creates_reflects_colimits {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (CR : CreatesColimit K F) :
  ReflectsColimitCocone K F :=
  fun N H =>
    @creates_reflect (J^op) (C^op) (D^op) (K^op) (F^op) CR N
      (islimitcone_op_comp H).

Definition creates_reflects_all_limits {C D : Category} {F : C ⟶ D}
  (CR : CreatesAllLimits F) : ReflectsAllLimits F :=
  fun J K => creates_reflects_limits (CR J K).

Definition creates_reflects_all_colimits {C D : Category} {F : C ⟶ D}
  (CR : CreatesAllColimits F) : ReflectsAllColimits F :=
  fun J K => creates_reflects_colimits (CR J K).

(** ** Mac Lane's creation, read literally *)

(* Mac Lane §V.1, the unnumbered Definition on p. 112: F creates the
   limit of K when every limiting cone N over F ◯ K has exactly one lift,
   an apex a with F a equal to N's apex and legs whose images are N's, and
   that lift is limiting.  The lift is Creation.v's [StrictLift] (the
   apex by [=], the legs by ≈ along it), and "exactly one" is equality
   with every other strict lift of N, the apex by [=] and the legs by ≈
   along it.  Creation.v declines that uniqueness as a FIELD of
   [CreatesLimit] (its UNIQUENESS OF THE LIFT); as a hypothesis it is
   what Mac Lane's Exercise 1 assumes. *)

Record MacLaneCreatesLimit {J C D : Category} (K : J ⟶ C) (F : C ⟶ D) := {
  mlc_lift (N : Cone (F ◯ K)) (HN : IsLimitCone N) : StrictLift K F N;
  mlc_limiting (N : Cone (F ◯ K)) (HN : IsLimitCone N) :
    IsLimitCone (slift_cone (mlc_lift N HN));
  mlc_unique (N : Cone (F ◯ K)) (HN : IsLimitCone N) (L : StrictLift K F N) :
    { p : vertex_obj[slift_cone L] = vertex_obj[slift_cone (mlc_lift N HN)]
    & ∀ x : J, cone_leg (slift_cone (mlc_lift N HN)) x ∘ to (obj_eq_iso p)
                 ≈ cone_leg (slift_cone L) x }
}.

Arguments mlc_lift {J C D K F} _ _ _.
Arguments mlc_limiting {J C D K F} _ _ _.
Arguments mlc_unique {J C D K F} _ _ _ _.

(* Reflection by Mac Lane's argument: a cone M upstairs whose image is
   limiting is a strict lift of that image (Creation.v's [self_lift]), so
   it is the lift, which is limiting.  The cone isomorphism is built with
   [exact], not as a pair term, which Coq 8.19 and 8.20 check by
   unification. *)

Definition maclane_creates_reflects {J C D : Category} {K : J ⟶ C}
  {F : C ⟶ D} (CR : MacLaneCreatesLimit K F) : ReflectsLimitCone K F.
Proof.
  intros M HM.
  refine (limitcone_transport (ConeIso_sym _)
            (mlc_limiting CR (FCone F M) HM)).
  unshelve eexists.
  - exact (obj_eq_iso (`1 (mlc_unique CR (FCone F M) HM (self_lift M)))).
  - exact (`2 (mlc_unique CR (FCone F M) HM (self_lift M))).
Defined.

(* So Mac Lane's creation is one of the tree's, whose reflection field is
   the theorem above. *)

Definition maclane_CreatesLimit {J C D : Category} {K : J ⟶ C}
  {F : C ⟶ D} (CR : MacLaneCreatesLimit K F) : CreatesLimit K F.
Proof.
  unshelve refine
    {| creates_lift := fun N HN => slift_cone (mlc_lift CR N HN);
       creates_reflect := maclane_creates_reflects CR |}.
  intros N HN.
  exists (slift_iso (mlc_lift CR N HN)).
  intro x.
  exact (slift_iso_legs (mlc_lift CR N HN) x).
Defined.

(* The same two clauses in the iso-invariant reading, a lift that is
   limiting and unique up to cone isomorphism, give reflection in one
   line; Creation.v's [creates_limiting] and [creates_lift_unique] derive
   them back from the reflection field and the lift's comparison. *)

Definition iso_unique_lift_reflects {J C D : Category} {K : J ⟶ C}
  {F : C ⟶ D}
  (lift : ∀ N : Cone (F ◯ K), IsLimitCone N → Cone K)
  (lift_limiting : ∀ N HN, IsLimitCone (lift N HN))
  (lift_unique : ∀ N HN (M : Cone K), ConeIso (FCone F M) N →
                   ConeIso M (lift N HN)) :
  ReflectsLimitCone K F :=
  fun M HM =>
    limitcone_transport (ConeIso_sym (lift_unique _ HM M (ConeIso_id _)))
      (lift_limiting _ HM).

(* The identity creates every limit in Mac Lane's sense: the lift of N is
   N itself, read over K, and a strict lift of N has N's apex. *)

Definition id_maclane_creates {J C : Category} (K : J ⟶ C) :
  MacLaneCreatesLimit K Id[C].
Proof.
  unshelve econstructor.
  - intros N HN.
    unshelve econstructor.
    + exact (@Build_Cone J C K vertex_obj[N]
               (@Build_ACone J C vertex_obj[N] K (fun x => cone_leg N x)
                  (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N)
                                  x y f))).
    + reflexivity.
    + intro x; reflexivity.
  - intros N HN; simpl.
    intro M.
    exact (HN (@Build_Cone J C (Id ◯ K) vertex_obj[M]
                 (@Build_ACone J C vertex_obj[M] (Id ◯ K)
                    (fun x => cone_leg M x)
                    (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ M)
                                    x y f)))).
  - intros N HN L; simpl.
    exists (slift_eq L).
    intro x.
    pose proof (slift_legs L x) as HL.
    destruct L as [L p HLs]; simpl in *.
    destruct N as [n acN]; simpl in *.
    destruct p; simpl in *.
    rewrite id_right.
    symmetry; exact HL.
Defined.

(* The colimit side, by the opposite, as Creation.v's [CreatesColimit]. *)

Definition MacLaneCreatesColimit {J C D : Category} (K : J ⟶ C)
  (F : C ⟶ D) : Type := MacLaneCreatesLimit (K^op) (F^op).

(** ** A conservative functor reflects the limits it preserves *)

(* Let M be a cone over K whose image is limiting, and u its mediator
   into L.  F u commutes with the image legs, so it is the comparison
   between the two limiting image cones, an isomorphism; F reflects it,
   so u is a cone isomorphism from M to L, and M is limiting. *)

Definition conservative_reflects_limit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (R : ReflectsIsos F)
  (L : Cone K) (HL : IsLimitCone L) (HFL : IsLimitCone (FCone F L)) :
  ReflectsLimitCone K F.
Proof.
  intros M HFM.
  pose (u := unique_obj (HL M)).
  assert (Hu : ∀ x : J, cone_leg L x ∘ u ≈ cone_leg M x)
    by exact (unique_property (HL M)).
  pose (i := limitcone_iso HFM HFL).
  assert (HFu : fmap[F] u ≈ to `1 i).
  { symmetry.
    apply (uniqueness (HFL (FCone F M))).
    intro x.
    change (fmap[F] (cone_leg L x) ∘ fmap[F] u ≈ fmap[F] (cone_leg M x)).
    rewrite <- fmap_comp.
    apply fmap_respects.
    exact (Hu x). }
  assert (IFu : IsIsomorphism (fmap[F] u)).
  { unshelve refine {| two_sided_inverse := from `1 i |}.
    - rewrite HFu.
      exact (iso_to_from `1 i).
    - rewrite HFu.
      exact (iso_from_to `1 i). }
  assert (ci : ConeIso M L).
  { exists (IsIsoToIso u (@reflects_iso C D F R _ _ u IFu)).
    exact Hu. }
  exact (limitcone_transport (ConeIso_sym ci) HL).
Defined.

Definition preserves_conservative_reflects_limit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (L : Limit K) (P : PreservesLimitCone K F)
  (R : ReflectsIsos F) : ReflectsLimitCone K F :=
  conservative_reflects_limit R (@limit_cone _ _ _ L) (limit_limitcone L)
    (P (@limit_cone _ _ _ L) (limit_limitcone L)).

Definition preserves_conservative_reflects_limits_of_shape (J : Category)
  {C D : Category} {F : C ⟶ D} (HL : ∀ K : J ⟶ C, Limit K)
  (P : PreservesLimitConesOfShape J F) (R : ReflectsIsos F) :
  ReflectsLimitConesOfShape J F :=
  fun K => preserves_conservative_reflects_limit (HL K) (P K) R.

Definition preserves_conservative_reflects_limits_over {C D : Category}
  (S : Category → Type) {F : C ⟶ D}
  (HL : ∀ J : Category, S J → ∀ K : J ⟶ C, Limit K)
  (P : PreservesLimitConesOver S F) (R : ReflectsIsos F) :
  ReflectsLimitConesOver S F :=
  fun J HJ K =>
    preserves_conservative_reflects_limit (HL J HJ K) (P J HJ K) R.

Definition preserves_conservative_reflects_limits_of_class {C D : Category}
  (S : ∀ J : Category, (J ⟶ C) → Type) {F : C ⟶ D}
  (HL : ∀ (J : Category) (K : J ⟶ C), S J K → Limit K)
  (P : ∀ (J : Category) (K : J ⟶ C), S J K → PreservesLimitCone K F)
  (R : ReflectsIsos F) : ReflectsLimitConesOfClass S F :=
  fun J K HS =>
    preserves_conservative_reflects_limit (HL J K HS) (P J K HS) R.

(* The colimit side, by op: [F^op] is conservative ([ReflectsIsos_op]),
   and both image cocones are read as image cones over [F^op ◯ K^op]. *)

Definition conservative_reflects_colimit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (R : ReflectsIsos F)
  (L : Cocone K) (HL : IsColimitCocone L)
  (HFL : IsColimitCocone (FCocone F L)) : ReflectsColimitCocone K F :=
  fun N HFN =>
    @conservative_reflects_limit (J^op) (C^op) (D^op) (K^op) (F^op)
      (ReflectsIsos_op R) L HL (islimitcone_op_comp HFL) N
      (islimitcone_op_comp HFN).

Definition preserves_conservative_reflects_colimit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (L : Colimit K) (P : PreservesColimitCocone K F)
  (R : ReflectsIsos F) : ReflectsColimitCocone K F :=
  conservative_reflects_colimit R (@limit_cone _ _ _ L)
    (colimit_colimitcocone L)
    (P (@limit_cone _ _ _ L) (colimit_colimitcocone L)).

Definition preserves_conservative_reflects_colimits_of_shape (J : Category)
  {C D : Category} {F : C ⟶ D} (HL : ∀ K : J ⟶ C, Colimit K)
  (P : PreservesColimitCoconesOfShape J F) (R : ReflectsIsos F) :
  ReflectsColimitCoconesOfShape J F :=
  fun K => preserves_conservative_reflects_colimit (HL K) (P K) R.

Definition preserves_conservative_reflects_colimits_over {C D : Category}
  (S : Category → Type) {F : C ⟶ D}
  (HL : ∀ J : Category, S J → ∀ K : J ⟶ C, Colimit K)
  (P : ∀ J : Category, S J → PreservesColimitCoconesOfShape J F)
  (R : ReflectsIsos F) : ReflectsColimitCoconesOver S F :=
  fun J HJ K =>
    preserves_conservative_reflects_colimit (HL J HJ K) (P J HJ K) R.

Definition preserves_conservative_reflects_colimits_of_class {C D : Category}
  (S : ∀ J : Category, (J ⟶ C) → Type) {F : C ⟶ D}
  (HL : ∀ (J : Category) (K : J ⟶ C), S J K → Colimit K)
  (P : ∀ (J : Category) (K : J ⟶ C), S J K → PreservesColimitCocone K F)
  (R : ReflectsIsos F) : ReflectsColimitCoconesOfClass S F :=
  fun J K HS =>
    preserves_conservative_reflects_colimit (HL J K HS) (P J K HS) R.

(** ** Riehl Exercise 3.4.iii: preservation and conservativity create *)

(* The lift of every limiting cone downstairs is the given limit upstairs,
   whose image is limiting by preservation and so isomorphic, as a cone,
   to any limiting cone downstairs; reflection is the theorem above. *)

Definition preserves_conservative_creates_limit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (L : Limit K) (P : PreservesLimitCone K F)
  (R : ReflectsIsos F) : CreatesLimit K F :=
  @Build_CreatesLimit J C D K F
    (fun N HN => @limit_cone _ _ _ L)
    (fun N HN =>
       limitcone_iso (P (@limit_cone _ _ _ L) (limit_limitcone L)) HN)
    (preserves_conservative_reflects_limit L P R).

Definition preserves_conservative_creates_limits_over {C D : Category}
  (S : Category → Type) {F : C ⟶ D}
  (HL : ∀ J : Category, S J → ∀ K : J ⟶ C, Limit K)
  (P : PreservesLimitConesOver S F) (R : ReflectsIsos F) :
  ∀ J : Category, S J → CreatesLimitsOfShape J F :=
  fun J HJ K =>
    preserves_conservative_creates_limit (HL J HJ K) (P J HJ K) R.

(* For a class of diagrams, as the exercise states it; the form over a
   class of shapes S above is this one at [fun J _ => S J], pointwise at
   [eq_refl] (the probe, C29). *)

Definition preserves_conservative_creates_limits_of_class {C D : Category}
  (S : ∀ J : Category, (J ⟶ C) → Type) {F : C ⟶ D}
  (HL : ∀ (J : Category) (K : J ⟶ C), S J K → Limit K)
  (P : ∀ (J : Category) (K : J ⟶ C), S J K → PreservesLimitCone K F)
  (R : ReflectsIsos F) :
  ∀ (J : Category) (K : J ⟶ C), S J K → CreatesLimit K F :=
  fun J K HS =>
    preserves_conservative_creates_limit (HL J K HS) (P J K HS) R.

Definition preserves_conservative_creates_colimit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (L : Colimit K) (P : PreservesColimitCocone K F)
  (R : ReflectsIsos F) : CreatesColimit K F :=
  @preserves_conservative_creates_limit (J^op) (C^op) (D^op) (K^op) (F^op)
    L (fun N HN => islimitcone_op_comp (P N HN)) (ReflectsIsos_op R).

Definition preserves_conservative_creates_colimits_of_class {C D : Category}
  (S : ∀ J : Category, (J ⟶ C) → Type) {F : C ⟶ D}
  (HL : ∀ (J : Category) (K : J ⟶ C), S J K → Colimit K)
  (P : ∀ (J : Category) (K : J ⟶ C), S J K → PreservesColimitCocone K F)
  (R : ReflectsIsos F) :
  ∀ (J : Category) (K : J ⟶ C), S J K → CreatesColimit K F :=
  fun J K HS =>
    preserves_conservative_creates_colimit (HL J K HS) (P J K HS) R.

(** ** Coequalizers: Mac Lane's "in particular" and Exercises 1 and 3 *)

(* Mac Lane's reflection of coequalizers, over the tree's elementary
   [IsCoequalizer]: a fork in C (e ∘ f ≈ e ∘ g) whose image is a
   coequalizer in D is a coequalizer in C. *)

Definition ReflectsCoequalizers@{co ch do dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D) : Type :=
  ∀ (x y : C) (f g : x ~{C}~> y) (q : C) (e : y ~{C}~> q),
    e ∘ f ≈ e ∘ g →
    IsCoequalizer (fmap[F] f) (fmap[F] g) (F q) (fmap[F] e) →
    IsCoequalizer f g q e.

(* Preservation in the same form: the dual of Structure/Limit/
   FromProducts.v's [PreservesEqualizers], and Monad/Monadicity/Crude.v's
   [PreservesReflexiveCoequalizers] without its reflexivity hypothesis.
   The binders of both predicates are written out: left to Rocq,
   minimization identified D's hom level with C's (measured), and the
   probe accepts both with D's strictly above (C6, C7). *)

Definition PreservesCoequalizers@{co ch do dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D) : Type :=
  ∀ (x y : C) (f g : x ~{C}~> y) (q : C) (e : y ~{C}~> q),
    IsCoequalizer f g q e →
    IsCoequalizer (fmap[F] f) (fmap[F] g) (F q) (fmap[F] e).

(* Creation of coequalizers: Structure/Limit/Creation.v's creation of the
   colimit of every diagram of parallel-pair shape. *)

Definition CreatesCoequalizers {C D : Category} (F : C ⟶ D) : Type :=
  ∀ K : Parallel ⟶ C, CreatesColimit K F.

(* The elementary and the cocone-level readings agree, both ways, through
   Structure/Coequalizer.v's conversions at a diagram of parallel-pair
   shape: an image cocone is a cocone over [F ◯ K], whose pair is the
   image pair and whose injection over [ParY] is the image injection, by
   conversion. *)

Definition ReflectsCoequalizers_ReflectsColimitCocones {C D : Category}
  {F : C ⟶ D} (R : ReflectsCoequalizers F) :
  ReflectsColimitCoconesOfShape Parallel F.
Proof.
  intros K N H.
  apply (parallel_cocone_coequalizer_colimit K N).
  apply R.
  - (* N coforks the pair: both composites are its injection over ParX *)
    transitivity (cocone_inj N ParX).
    + exact (cocone_inj_coherence N
               ((true; ParOne) : ParX ~{Parallel}~> ParY)).
    + symmetry.
      exact (cocone_inj_coherence N
               ((false; ParTwo) : ParX ~{Parallel}~> ParY)).
  - exact (parallel_colimit_coequalizer (F ◯ K) (FCocone F N) H).
Defined.

(* The two bridges from the cocone level to the elementary predicates use
   their hypothesis only at the diagrams [APair f g], so they are stated
   per parallel pair, and their forms over every diagram of parallel-pair
   shape are the restrictions. *)

Definition ReflectsColimitCocones_ReflectsCoequalizers_of_pairs
  {C D : Category} {F : C ⟶ D}
  (R : ∀ (x y : C) (f g : x ~> y), ReflectsColimitCocone (APair f g) F) :
  ReflectsCoequalizers F :=
  fun x y f g q e H E =>
    parallel_colimit_coequalizer (APair f g) (cofork_cocone f g e H)
      (R x y f g (cofork_cocone f g e H)
         (parallel_cocone_coequalizer_colimit (F ◯ APair f g)
            (FCocone F (cofork_cocone f g e H)) E)).

Definition ReflectsColimitCocones_ReflectsCoequalizers {C D : Category}
  {F : C ⟶ D} (R : ReflectsColimitCoconesOfShape Parallel F) :
  ReflectsCoequalizers F :=
  ReflectsColimitCocones_ReflectsCoequalizers_of_pairs
    (fun x y f g => R (APair f g)).

Definition PreservesCoequalizers_PreservesColimitCocones {C D : Category}
  {F : C ⟶ D} (P : PreservesCoequalizers F) :
  PreservesColimitCoconesOfShape Parallel F :=
  fun K N HN =>
    parallel_cocone_coequalizer_colimit (F ◯ K) (FCocone F N)
      (P _ _ _ _ _ _ (parallel_colimit_coequalizer K N HN)).

Definition PreservesColimitCocones_PreservesCoequalizers_of_pairs
  {C D : Category} {F : C ⟶ D}
  (P : ∀ (x y : C) (f g : x ~> y), PreservesColimitCocone (APair f g) F) :
  PreservesCoequalizers F :=
  fun x y f g q e E =>
    parallel_colimit_coequalizer (F ◯ APair f g)
      (FCocone F (parallel_cofork_cocone (APair f g) e (cofork E)))
      (P x y f g (parallel_cofork_cocone (APair f g) e (cofork E))
         (parallel_coequalizer_colimit (APair f g) E)).

Definition PreservesColimitCocones_PreservesCoequalizers {C D : Category}
  {F : C ⟶ D} (P : PreservesColimitCoconesOfShape Parallel F) :
  PreservesCoequalizers F :=
  PreservesColimitCocones_PreservesCoequalizers_of_pairs
    (fun x y f g => P (APair f g)).

(* Mac Lane §VI.7 Exercise 1, per parallel pair, as the book states it:
   under the tree's creation, where reflection is a field ... *)

Definition creates_reflects_coequalizers_of_pairs {C D : Category}
  {F : C ⟶ D}
  (CR : ∀ (x y : C) (f g : x ~> y), CreatesColimit (APair f g) F) :
  ReflectsCoequalizers F :=
  ReflectsColimitCocones_ReflectsCoequalizers_of_pairs
    (fun x y f g => creates_reflects_colimits (CR x y f g)).

(* ... and under Mac Lane's own, by his argument. *)

Definition maclane_creates_reflects_coequalizers {C D : Category}
  {F : C ⟶ D}
  (CR : ∀ (x y : C) (f g : x ~> y), MacLaneCreatesColimit (APair f g) F) :
  ReflectsCoequalizers F :=
  ReflectsColimitCocones_ReflectsCoequalizers_of_pairs
    (fun x y f g N H =>
       maclane_creates_reflects (CR x y f g) N (islimitcone_op_comp H)).

(* Over every diagram of parallel-pair shape, by restriction (C17). *)

Definition creates_reflects_coequalizers {C D : Category} {F : C ⟶ D}
  (CR : CreatesCoequalizers F) : ReflectsCoequalizers F :=
  creates_reflects_coequalizers_of_pairs (fun x y f g => CR (APair f g)).

(* Mac Lane §VI.7 Exercise 3. *)

Definition conservative_reflects_coequalizers {C D : Category}
  {F : C ⟶ D} (HC : HasCoequalizers C) (P : PreservesCoequalizers F)
  (R : ReflectsIsos F) : ReflectsCoequalizers F :=
  ReflectsColimitCocones_ReflectsCoequalizers
    (preserves_conservative_reflects_colimits_of_shape Parallel
       (HasCoequalizers_HasColimitsOfShape HC)
       (PreservesCoequalizers_PreservesColimitCocones P) R).
