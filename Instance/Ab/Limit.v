Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.

Generalizable All Variables.

(** * Limits of abelian groups are computed on underlying sets *)

(*
 nLab: https://ncatlab.org/nlab/show/limit#limits_in_categories_of_algebras
 nLab: https://ncatlab.org/nlab/show/Ab
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_abelian_groups

   本文件给出极限实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** * Joint monicity of limit legs in [Sets], elementwise *)

Section AbSetsExt.

Context {J : Category}.
Context {F : J ⟶ Sets}.
Context {c : Sets}.
Context (H : IsALimit F c).

Definition absets_pre {d : Sets} (u : d ~{Sets}~> c) : Cone F :=
  @Build_Cone J Sets F d
    (@Build_ACone J Sets d F (fun j => limit_leg H j ∘ u)
       (fun x y f =>
          transitivity (comp_assoc _ _ _)
            (@compose_respects Sets _ _ _ _ _ (limit_leg_coherence H f) _ _
               (reflexivity u)))).

Lemma absets_med_eq {d : Sets} (u v : d ~{Sets}~> c) :
  (∀ j : J, limit_leg H j ∘ u ≈ limit_leg H j ∘ v) → u ≈ v.
Proof.
  intro Huv.
  apply (limit_med_eq H (absets_pre u)).
  - intro j; reflexivity.
  - intro j; symmetry; apply Huv.
Qed.

Program Definition absets_const (x : carrier c) : c ~{Sets}~> c :=
  {| morphism := fun _ => x |}.

Lemma absets_limit_ext (x y : carrier c) :
  (∀ j : J, limit_leg H j x ≈ limit_leg H j y) → x ≈ y.
Proof.
  intro Hxy.
  exact (absets_med_eq (absets_const x) (absets_const y) (fun j a => Hxy j) x).
Qed.

End AbSetsExt.

(** * The created abelian-group structure on a limit of underlying sets *)

Section AbLift.

Context {J : Category}.
Context (K : J ⟶ Ab).
Context (L : Limit (Ab_Forget ◯ K)).

Definition alim_leg (j : J) :
  vertex_obj[L] ~{Sets}~> cmon_setoid (ab_cmon (K j)) :=
  limit_leg (limit_is_alimit L) j.

Lemma alim_leg_coherence {x y : J} (f : x ~{J}~> y)
  (a : carrier vertex_obj[L]) :
  cmon_map (fmap[K] f) (alim_leg x a) ≈ alim_leg y a.
Proof. exact (limit_leg_coherence (limit_is_alimit L) f a). Qed.

Lemma alim_ext (x y : carrier vertex_obj[L]) :
  (∀ j : J, alim_leg j x ≈ alim_leg j y) → x ≈ y.
Proof. exact (absets_limit_ext (limit_is_alimit L) x y). Qed.

(** ** The addition *)

Definition alim_pair : Sets :=
  {| carrier   := carrier vertex_obj[L] * carrier vertex_obj[L]
   ; is_setoid := prod_setoid |}.

Program Definition alim_plus_leg (j : J) :
  alim_pair ~{Sets}~> cmon_setoid (ab_cmon (K j)) :=
  {| morphism := fun p =>
       cmon_plus (K j) (alim_leg j (fst p)) (alim_leg j (snd p)) |}.
Next Obligation.
  intros p q Hpq.
  destruct Hpq as [H1 H2].
  now rewrite H1, H2.
Qed.

Lemma alim_plus_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Ab_Forget ◯ K] f ∘ alim_plus_leg x ≈ alim_plus_leg y.
Proof.
  intro p; simpl.
  rewrite cmon_map_plus.
  now rewrite !alim_leg_coherence.
Qed.

Definition alim_plus_cone : Cone (Ab_Forget ◯ K) :=
  @Build_Cone J Sets (Ab_Forget ◯ K) alim_pair
    (@Build_ACone J Sets alim_pair (Ab_Forget ◯ K)
       alim_plus_leg (@alim_plus_coherence)).

Definition alim_plus_map : alim_pair ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) alim_plus_cone.

Definition alim_plus (a b : carrier vertex_obj[L]) : carrier vertex_obj[L] :=
  alim_plus_map (a, b).

Lemma alim_plus_triangle (j : J) (a b : carrier vertex_obj[L]) :
  alim_leg j (alim_plus a b)
    ≈ cmon_plus (K j) (alim_leg j a) (alim_leg j b).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) alim_plus_cone j (a, b)).
Qed.

Lemma alim_plus_respects :
  Proper (equiv ==> equiv ==> equiv) alim_plus.
Proof.
  intros a a' Ha b b' Hb.
  exact (proper_morphism alim_plus_map (a, b) (a', b') (Ha, Hb)).
Qed.

(** ** The zero *)

Program Definition alim_zero_leg (j : J) :
  unit_setoid_object ~{Sets}~> cmon_setoid (ab_cmon (K j)) :=
  {| morphism := fun _ => cmon_zero (K j) |}.

Lemma alim_zero_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Ab_Forget ◯ K] f ∘ alim_zero_leg x ≈ alim_zero_leg y.
Proof. intro p; simpl; apply cmon_map_zero. Qed.

Definition alim_zero_cone : Cone (Ab_Forget ◯ K) :=
  @Build_Cone J Sets (Ab_Forget ◯ K) unit_setoid_object
    (@Build_ACone J Sets unit_setoid_object (Ab_Forget ◯ K)
       alim_zero_leg (@alim_zero_coherence)).

Definition alim_zero_map : unit_setoid_object ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) alim_zero_cone.

Definition alim_zero : carrier vertex_obj[L] := alim_zero_map ttt.

Lemma alim_zero_triangle (j : J) :
  alim_leg j alim_zero ≈ cmon_zero (K j).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) alim_zero_cone j ttt).
Qed.

(** ** The negation *)

Program Definition alim_neg_leg (j : J) :
  vertex_obj[L] ~{Sets}~> cmon_setoid (ab_cmon (K j)) :=
  {| morphism := fun a => ab_neg (K j) (alim_leg j a) |}.
Next Obligation. intros a b Hab; now rewrite Hab. Qed.

Lemma alim_neg_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Ab_Forget ◯ K] f ∘ alim_neg_leg x ≈ alim_neg_leg y.
Proof.
  intro a; simpl.
  rewrite ab_map_neg.
  now rewrite alim_leg_coherence.
Qed.

Definition alim_neg_cone : Cone (Ab_Forget ◯ K) :=
  @Build_Cone J Sets (Ab_Forget ◯ K) vertex_obj[L]
    (@Build_ACone J Sets vertex_obj[L] (Ab_Forget ◯ K)
       alim_neg_leg (@alim_neg_coherence)).

Definition alim_neg_map : vertex_obj[L] ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) alim_neg_cone.

Definition alim_neg (a : carrier vertex_obj[L]) : carrier vertex_obj[L] :=
  alim_neg_map a.

Lemma alim_neg_triangle (j : J) (a : carrier vertex_obj[L]) :
  alim_leg j (alim_neg a) ≈ ab_neg (K j) (alim_leg j a).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) alim_neg_cone j a).
Qed.

Lemma alim_neg_respects : Proper (equiv ==> equiv) alim_neg.
Proof.
  intros a a' Ha.
  exact (proper_morphism alim_neg_map a a' Ha).
Qed.

(** ** The abelian-group laws, by joint monicity of the legs *)

Lemma alim_assoc (a b c : carrier vertex_obj[L]) :
  alim_plus (alim_plus a b) c ≈ alim_plus a (alim_plus b c).
Proof.
  apply alim_ext; intro j.
  rewrite !alim_plus_triangle.
  apply cmon_plus_assoc.
Qed.

(* The one law with no counterpart in the group template, and it costs
   exactly what the others cost: joint monicity does not care what the law
   says. *)
Lemma alim_comm (a b : carrier vertex_obj[L]) :
  alim_plus a b ≈ alim_plus b a.
Proof.
  apply alim_ext; intro j.
  rewrite !alim_plus_triangle.
  apply cmon_plus_comm.
Qed.

Lemma alim_zero_l (a : carrier vertex_obj[L]) : alim_plus alim_zero a ≈ a.
Proof.
  apply alim_ext; intro j.
  rewrite alim_plus_triangle, alim_zero_triangle.
  apply cmon_plus_zero_l.
Qed.

Lemma alim_neg_l (a : carrier vertex_obj[L]) :
  alim_plus (alim_neg a) a ≈ alim_zero.
Proof.
  apply alim_ext; intro j.
  rewrite alim_plus_triangle, alim_neg_triangle, alim_zero_triangle.
  apply ab_neg_left.
Qed.

(** ** The vertex's equality is propositional *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition alim_prop : PropEquiv (is_setoid vertex_obj[L]) :=
  @PropEquiv_of_relation _ (is_setoid vertex_obj[L])
    (fun x y => forall j : J,
       @pequiv _ _ (cmon_prop (K j)) (alim_leg j x) (alim_leg j y))
    (fun x y H => alim_ext x y (fun j => pequiv_to _ _ (H j)))
    (fun x y H j => pequiv_from _ _ (proper_morphism (alim_leg j) x y H)).

(** ** The lifted abelian group *)

Definition LimitAb : AbObject :=
  {| ab_cmon :=
       {| cmon_setoid        := vertex_obj[L]
        ; cmon_zero          := alim_zero
        ; cmon_plus          := alim_plus
        ; cmon_plus_respects := alim_plus_respects
        ; cmon_plus_assoc    := alim_assoc
        ; cmon_plus_comm     := alim_comm
        ; cmon_plus_zero_l   := alim_zero_l
        ; cmon_prop          := alim_prop |}
   ; ab_neg          := alim_neg
   ; ab_neg_respects := alim_neg_respects
   ; ab_neg_left     := alim_neg_l |}.

(** ** The legs are homomorphisms *)

(* Only [cmon_map_zero] and [cmon_map_plus] are owed: [AbHom] IS [CMonHom]
   (Instance/Ab.v), and preservation of negation is the theorem
   [ab_map_neg] rather than a field. *)
Program Definition alim_hom (j : J) : AbHom LimitAb (K j) :=
  {| cmon_map := alim_leg j |}.
Next Obligation. apply alim_zero_triangle. Qed.
Next Obligation. apply alim_plus_triangle. Qed.

Lemma alim_hom_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ alim_hom x ≈ alim_hom y.
Proof. intro a; exact (alim_leg_coherence f a). Qed.

Definition alim_cone : Cone K :=
  @Build_Cone J Ab K LimitAb
    (@Build_ACone J Ab LimitAb K alim_hom (@alim_hom_coherence)).

(** ** Strictness: the lifted cone lies over [L] on the nose *)

Definition alim_over_obj : Ab_Forget LimitAb = vertex_obj[L] := eq_refl.

Definition alim_over_legs (j : J) :
  fmap[Ab_Forget] (cone_leg alim_cone j) = alim_leg j := eq_refl.

(** ** The lifted cone is limiting *)

Definition acar_med (N : Cone K) :
  cmon_setoid (ab_cmon vertex_obj[N]) ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) (FCone Ab_Forget N).

Lemma acar_med_commutes (N : Cone K) (j : J) (a : carrier vertex_obj[N]) :
  alim_leg j (acar_med N a) ≈ cmon_map (cone_leg N j) a.
Proof.
  exact (limit_med_commutes (limit_is_alimit L) (FCone Ab_Forget N) j a).
Qed.

Lemma acar_med_zero (N : Cone K) :
  acar_med N (cmon_zero vertex_obj[N]) ≈ alim_zero.
Proof.
  apply alim_ext; intro j.
  rewrite acar_med_commutes, alim_zero_triangle.
  apply cmon_map_zero.
Qed.

Lemma acar_med_plus (N : Cone K) (a b : carrier vertex_obj[N]) :
  acar_med N (cmon_plus vertex_obj[N] a b)
    ≈ alim_plus (acar_med N a) (acar_med N b).
Proof.
  apply alim_ext; intro j.
  rewrite acar_med_commutes, alim_plus_triangle, !acar_med_commutes.
  apply cmon_map_plus.
Qed.

Program Definition alim_med (N : Cone K) : vertex_obj[N] ~{Ab}~> LimitAb :=
  {| cmon_map := acar_med N |}.
Next Obligation. apply acar_med_zero. Qed.
Next Obligation. apply acar_med_plus. Qed.

Definition alim_created : IsALimit K LimitAb.
Proof.
  unshelve refine {| limit_acone := @coneFrom _ _ _ alim_cone |}.
  intro N.
  unshelve refine {| unique_obj := alim_med N |}.
  - intros j a.
    exact (acar_med_commutes N j a).
  - intros v Hv a.
    exact (limit_med_unique (limit_is_alimit L) (FCone Ab_Forget N)
             (cmon_map v) Hv a).
Defined.

(** ** Uniqueness of the lifted structure (Mac Lane's Theorem 2) *)

Lemma alim_zero_unique (e : carrier vertex_obj[L])
  (He : ∀ j : J, alim_leg j e ≈ cmon_zero (K j)) : e ≈ alim_zero.
Proof.
  apply alim_ext; intro j.
  now rewrite He, alim_zero_triangle.
Qed.

Lemma alim_plus_unique
  (m : carrier vertex_obj[L] → carrier vertex_obj[L] → carrier vertex_obj[L])
  (Hm : ∀ (j : J) a b,
     alim_leg j (m a b) ≈ cmon_plus (K j) (alim_leg j a) (alim_leg j b))
  (a b : carrier vertex_obj[L]) : m a b ≈ alim_plus a b.
Proof.
  apply alim_ext; intro j.
  now rewrite Hm, alim_plus_triangle.
Qed.

Lemma alim_neg_unique
  (n : carrier vertex_obj[L] → carrier vertex_obj[L])
  (Hn : ∀ (j : J) a, alim_leg j (n a) ≈ ab_neg (K j) (alim_leg j a))
  (a : carrier vertex_obj[L]) : n a ≈ alim_neg a.
Proof.
  apply alim_ext; intro j.
  now rewrite Hn, alim_neg_triangle.
Qed.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma alim_structure_unique
  (e : carrier vertex_obj[L])
  (m : carrier vertex_obj[L] → carrier vertex_obj[L] → carrier vertex_obj[L])
  (n : carrier vertex_obj[L] → carrier vertex_obj[L])
  (He : ∀ j : J, alim_leg j e ≈ cmon_zero (K j))
  (Hm : ∀ (j : J) a b,
     alim_leg j (m a b) ≈ cmon_plus (K j) (alim_leg j a) (alim_leg j b))
  (Hn : ∀ (j : J) a, alim_leg j (n a) ≈ ab_neg (K j) (alim_leg j a)) :
  (e ≈ alim_zero)
    * (∀ a b, m a b ≈ alim_plus a b)
    * (∀ a, n a ≈ alim_neg a).
Proof.
  split; [ split | ].
  - exact (alim_zero_unique e He).
  - exact (alim_plus_unique m Hm).
  - exact (alim_neg_unique n Hn).
Qed.

End AbLift.

(** * Reflection: a cone of abelian groups whose image is limiting is
      limiting *)

Section AbReflect.

Context {J : Category}.
Context (K : J ⟶ Ab).
Context (M : Cone K).
Context (HM : IsLimitCone (FCone Ab_Forget M)).

Definition arefl_med (N : Cone K) :
  cmon_setoid (ab_cmon vertex_obj[N]) ~{Sets}~>
    cmon_setoid (ab_cmon vertex_obj[M]) :=
  limit_med (limitcone_isalimit HM) (FCone Ab_Forget N).

Lemma arefl_med_commutes (N : Cone K) (j : J) (a : carrier vertex_obj[N]) :
  cmon_map (cone_leg M j) (arefl_med N a) ≈ cmon_map (cone_leg N j) a.
Proof using All.
  exact (limit_med_commutes (limitcone_isalimit HM) (FCone Ab_Forget N) j a).
Qed.

Lemma arefl_ext (x y : carrier vertex_obj[M]) :
  (∀ j : J, cmon_map (cone_leg M j) x ≈ cmon_map (cone_leg M j) y) → x ≈ y.
Proof using All. exact (absets_limit_ext (limitcone_isalimit HM) x y). Qed.

Lemma arefl_med_zero (N : Cone K) :
  arefl_med N (cmon_zero vertex_obj[N]) ≈ cmon_zero vertex_obj[M].
Proof using All.
  apply arefl_ext; intro j.
  rewrite arefl_med_commutes, !cmon_map_zero.
  reflexivity.
Qed.

Lemma arefl_med_plus (N : Cone K) (a b : carrier vertex_obj[N]) :
  arefl_med N (cmon_plus vertex_obj[N] a b)
    ≈ cmon_plus vertex_obj[M] (arefl_med N a) (arefl_med N b).
Proof using All.
  apply arefl_ext; intro j.
  rewrite arefl_med_commutes, !cmon_map_plus, !arefl_med_commutes.
  reflexivity.
Qed.

Program Definition arefl_hom (N : Cone K) :
  vertex_obj[N] ~{Ab}~> vertex_obj[M] := {| cmon_map := arefl_med N |}.
Next Obligation. apply arefl_med_zero. Qed.
Next Obligation. apply arefl_med_plus. Qed.

Definition ab_reflects : IsLimitCone M.
Proof using All.
  intro N.
  unshelve refine {| unique_obj := arefl_hom N |}.
  - intros j a.
    exact (arefl_med_commutes N j a).
  - intros v Hv a.
    exact (limit_med_unique (limitcone_isalimit HM) (FCone Ab_Forget N)
             (cmon_map v) Hv a).
Defined.

End AbReflect.

(** * [Ab_Forget] strictly creates every limit *)

Section AbStrictlyCreates.

Context {J : Category}.
Context (K : J ⟶ Ab).

Definition ab_strict_lift (N : Cone (Ab_Forget ◯ K)) (HN : IsLimitCone N) :
  StrictLift K Ab_Forget N :=
  @Build_StrictLift J Ab Sets K Ab_Forget N
    (alim_cone K (@Build_Limit J Sets (Ab_Forget ◯ K) N HN))
    eq_refl
    (fun x => reflexivity _).

Definition Ab_Forget_StrictlyCreatesLimit : StrictlyCreatesLimit K Ab_Forget.
Proof.
  unshelve refine {| screates := ab_strict_lift |}.
  - intros N HN.
    exact (@ump_limit _ _ _ _
             (alim_created K (@Build_Limit J Sets (Ab_Forget ◯ K) N HN))).
  - intros M HM.
    exact (ab_reflects K M HM).
Defined.

Definition Ab_Forget_CreatesLimit : CreatesLimit K Ab_Forget :=
  StrictlyCreatesLimit_CreatesLimit Ab_Forget_StrictlyCreatesLimit.

End AbStrictlyCreates.

Definition Ab_Forget_StrictlyCreatesLimits :
  StrictlyCreatesLimits Ab_Forget :=
  fun J K => Ab_Forget_StrictlyCreatesLimit K.

Definition Ab_Forget_creates_limits : CreatesAllLimits Ab_Forget :=
  fun J K => Ab_Forget_CreatesLimit K.

Definition Ab_Forget_reflects_limits {J : Category} (K : J ⟶ Ab) :
  ReflectsLimitCone K Ab_Forget :=
  creates_reflects_limits (Ab_Forget_CreatesLimit K).

(*
   本节说明 Limit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Ab_lift_cone_unique {J : Category} (K : J ⟶ Ab)
  (N : Cone (Ab_Forget ◯ K)) (HN : IsLimitCone N)
  (M : Cone K) (i : ConeIso (FCone Ab_Forget M) N) :
  ConeIso M (slift_cone (screates N HN)) :=
  screates_lift_unique (Ab_Forget_StrictlyCreatesLimit K) N HN M i.

(** * The image of a cone of abelian groups is the elementwise cone *)

Example ab_fcone_apex {J : Category} (K : J ⟶ Ab) (N : Cone K) :
  vertex_obj[FCone Ab_Forget N] = cmon_setoid (ab_cmon vertex_obj[N])
  := eq_refl.

Example ab_fcone_leg {J : Category} (K : J ⟶ Ab) (N : Cone K) (j : J) :
  cone_leg (FCone Ab_Forget N) j = cmon_map (cone_leg N j) := eq_refl.

(** * Mac Lane's Theorem 2: the lifting half *)

Definition Ab_Forget_lifts_limits {J : Category} (K : J ⟶ Ab)
  (L : Limit (Ab_Forget ◯ K)) : Limit K :=
  creates_limit_lift (Ab_Forget_CreatesLimit K) L.

Example ab_lift_apex {J : Category} (K : J ⟶ Ab)
  (L : Limit (Ab_Forget ◯ K)) :
  Ab_Forget (vertex_obj[Ab_Forget_lifts_limits K L]) = vertex_obj[L]
  := eq_refl.

Example ab_lift_legs {J : Category} (K : J ⟶ Ab)
  (L : Limit (Ab_Forget ◯ K)) (j : J) :
  fmap[Ab_Forget]
    (cone_leg (@limit_cone _ _ _ (Ab_Forget_lifts_limits K L)) j)
    = limit_leg (limit_is_alimit L) j
  := eq_refl.

(** * Corollaries: [Ab] is complete and [Ab_Forget] is continuous *)

Definition Ab_Complete : @Complete Ab :=
  creates_limits_Complete Ab_Forget Sets_Complete Ab_Forget_creates_limits.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Ab_Forget_creates_continuous : ContinuousFunctor Ab_Forget :=
  creates_limits_continuous Ab_Forget Sets_Complete Ab_Forget_creates_limits.

Definition Ab_Forget_PreservesAllLimits : PreservesAllLimits Ab_Forget :=
  creates_limits_PreservesAllLimits Ab_Forget Sets_Complete
    Ab_Forget_creates_limits.

(** * "Limits of abelian groups are computed on underlying sets", literally *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section AbComputed.

Context {J : Category}.
Context (K : J ⟶ Ab).

Example ab_complete_carrier :
  cmon_setoid (ab_cmon (vertex_obj[Ab_Complete J K]))
    = Sets_limit_obj (Ab_Forget ◯ K) := eq_refl.

Example ab_complete_plus
  (a b : carrier (Sets_limit_obj (Ab_Forget ◯ K))) (d : J) :
  `1 (cmon_plus (vertex_obj[Ab_Complete J K]) a b) d
    = cmon_plus (K d) (`1 a d) (`1 b d) := eq_refl.

Example ab_complete_zero (d : J) :
  `1 (cmon_zero (vertex_obj[Ab_Complete J K])) d = cmon_zero (K d) := eq_refl.

Example ab_complete_neg
  (a : carrier (Sets_limit_obj (Ab_Forget ◯ K))) (d : J) :
  `1 (ab_neg (vertex_obj[Ab_Complete J K]) a) d
    = ab_neg (K d) (`1 a d) := eq_refl.

Example ab_complete_leg (d : J) :
  cmon_map (cone_leg (@limit_cone _ _ _ (Ab_Complete J K)) d)
    = Sets_limit_leg (Ab_Forget ◯ K) d := eq_refl.

End AbComputed.
