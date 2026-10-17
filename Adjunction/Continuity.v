Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Opposite.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Adjoint (co)continuity: RAPL and LAPC *)

(* nLab: https://ncatlab.org/nlab/show/adjoints+preserve+(co-)limits
   Wikipedia:
   https://en.wikipedia.org/wiki/Adjoint_functors#Preservation_of_limits

   「伴随最重要的性质是其连续性：每个有左伴随的函子（因而是右伴随）连续
   （即与范畴意义下的极限交换）；每个有右伴随的函子（因而是左伴随）余连续
   （即与余极限交换）。」—— Wikipedia

   本文件对 [Theory/Adjunction.v] 的 hom-setoid 伴随证明两陈述，打包在
   [Structure/Limit/Preservation.v] 的保持词汇中。

   固定伴随 A : F ⊣ U，F : D ⟶ C 左伴随、U : C ⟶ D 右伴随，写 ⌊-⌋ : (F x ~> y) → (x ~> U y)
   为正向转置、⌈-⌉ 为其逆。给定图 G : J ⟶ C 的极限 L，对象 U L 被直接展示为 U ◯ G 的极限
   （[rapl_is_alimit]）：像锥的腿是对 L 的腿应用 fmap[U]；竞争锥经 ⌈-⌉ 逐腿转置；中介经 ⌊-⌋
   转回；唯一性由两转置在 ≈ 下互逆。右伴随连续性打包为 [right_adjoint_preserves_limits] :
   [PreservesAllLimits] U；对偶结果给出左伴随的余连续性。 *)

Section RAPL.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

Notation "⌊ f ⌋" := (to (@adj _ _ _ _ A _ _) f).
Notation "⌈ f ⌉" := (from (@adj _ _ _ _ A _ _) f).

Section Diagram.

Context {J : Category}.
Context (G : J ⟶ C).
Context (L : Limit G).

(** ** The image cone over [U L] *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition rapl_leg (x : J) : U L ~{D}~> U (G x) :=
  fmap[U] (limit_leg (limit_is_alimit L) x).

Lemma rapl_leg_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[U] (fmap[G] f) ∘ rapl_leg x ≈ rapl_leg y.
Proof using G L U.
  unfold rapl_leg.
  rewrite <- fmap_comp.
  now rewrite (limit_leg_coherence (limit_is_alimit L) f).
Qed.

Definition rapl_acone : ACone (U L) (U ◯ G) :=
  @Build_ACone J D (U L) (U ◯ G) rapl_leg (@rapl_leg_coherence).

(** ** Transposing a competing cone across the adjunction *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition rapl_transposed_leg (N : Cone (U ◯ G)) (x : J) :
  F (vertex_obj[N]) ~{C}~> G x := ⌈ cone_leg N x ⌉.

Lemma rapl_transposed_coherence (N : Cone (U ◯ G)) {x y : J}
  (f : x ~{J}~> y) :
  fmap[G] f ∘ rapl_transposed_leg N x ≈ rapl_transposed_leg N y.
Proof using A G.
  unfold rapl_transposed_leg.
  etransitivity.
  - symmetry.
    apply (@from_adj_nat_r C D F U A _ _ _ (fmap[G] f) (cone_leg N x)).
  - apply from_adj_respects.
    exact (@cone_coherence J D _ (U ◯ G) (@coneFrom _ _ _ N) x y f).
Qed.

Definition rapl_transposed_cone (N : Cone (U ◯ G)) : Cone G :=
  @Build_Cone J C G (F (vertex_obj[N]))
    (@Build_ACone J C (F (vertex_obj[N])) G
       (rapl_transposed_leg N) (@rapl_transposed_coherence N)).

(** ** The mediating morphism and the universal property *)

(* Mediate the transposed cone through L in C, then transpose the
   resulting morphism back along ⌊-⌋ to land in D. *)

Definition rapl_med (N : Cone (U ◯ G)) : vertex_obj[N] ~{D}~> U L :=
  ⌊ limit_med (limit_is_alimit L) (rapl_transposed_cone N) ⌋.

Lemma rapl_med_commutes (N : Cone (U ◯ G)) :
  ∀ x : J, rapl_leg x ∘ rapl_med N ≈ cone_leg N x.
Proof using A G L.
  intro x.
  unfold rapl_med, rapl_leg.
  etransitivity.
  - symmetry.
    apply (@to_adj_nat_r C D F U A _ _ _
             (limit_leg (limit_is_alimit L) x)
             (limit_med (limit_is_alimit L) (rapl_transposed_cone N))).
  - etransitivity.
    + apply to_adj_respects.
      apply (limit_med_commutes (limit_is_alimit L)
               (rapl_transposed_cone N) x).
    + apply from_adj_comp_law.
Qed.

Lemma rapl_med_unique (N : Cone (U ◯ G)) :
  ∀ v : vertex_obj[N] ~{D}~> U L,
    (∀ x : J, rapl_leg x ∘ v ≈ cone_leg N x) → rapl_med N ≈ v.
Proof using A G L.
  intros v Hv.
  unfold rapl_med.
  etransitivity.
  - apply to_adj_respects.
    apply (limit_med_unique (limit_is_alimit L) (rapl_transposed_cone N)
             ⌈ v ⌉).
    intro x.
    etransitivity.
    + symmetry.
      apply (@from_adj_nat_r C D F U A _ _ _
               (limit_leg (limit_is_alimit L) x) v).
    + apply from_adj_respects.
      exact (Hv x).
  - apply from_adj_comp_law.
Qed.

Definition rapl_ump (N : Cone (U ◯ G)) :
  ∃! u : vertex_obj[N] ~{D}~> U L,
    ∀ x : J, rapl_leg x ∘ u ≈ cone_leg N x :=
  Build_Unique _ _ _ (rapl_med N) (rapl_med_commutes N) (rapl_med_unique N).

(* RAPL for one diagram, apex-pinned: U L underlies a limit of U ◯ G. *)

Definition rapl_is_alimit : IsALimit (U ◯ G) (U L) :=
  @Build_IsALimit J D (U ◯ G) (U L) rapl_acone rapl_ump.

(* The bundled form of the same witness. *)

Definition rapl_cone : Cone (U ◯ G) :=
  @Build_Cone J D (U ◯ G) (U L) rapl_acone.

Definition rapl_limit : Limit (U ◯ G) :=
  @Build_Limit J D (U ◯ G) rapl_cone rapl_ump.

End Diagram.

(** ** Right adjoints preserve limiting CONES, not merely limit apexes *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition right_adjoint_PreservesLimitCone {J : Category} (G : J ⟶ C) :
  PreservesLimitCone G U :=
  fun N HN => rapl_ump G (@Build_Limit J C G N HN).

Definition right_adjoint_Continuous : ContinuousFunctor U :=
  fun J G => right_adjoint_PreservesLimitCone G.

(** ** Right adjoints preserve limits *)

Definition right_adjoint_preserves_limit {J : Category} (G : J ⟶ C) :
  PreservesLimit G U :=
  @Build_PreservesLimit J C G D U (rapl_is_alimit G).

Definition right_adjoint_preserves_limits : PreservesAllLimits U :=
  fun J G => right_adjoint_preserves_limit G.

End RAPL.

(** ** Left adjoints preserve colimits *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition left_adjoint_preserves_colimit
  {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U)
  {J : Category} (G : J ⟶ D) : PreservesColimit G F :=
  right_adjoint_preserves_limits (Opposite_Adjunction F U A)
    (Opposite J) (Opposite_Functor G).

Definition left_adjoint_preserves_colimits
  {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) :
  PreservesAllColimits F :=
  fun J G => left_adjoint_preserves_colimit A G.

(** ** Left adjoints preserve colimiting COCONES *)

Definition left_adjoint_PreservesColimitCocone
  {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U)
  {J : Category} (G : J ⟶ D) : PreservesColimitCocone G F.
Proof.
  intros N HN M.
  exact (right_adjoint_PreservesLimitCone (Opposite_Adjunction F U A)
           (Opposite_Functor G) N HN (cone_op_comp M)).
Defined.

Definition left_adjoint_Cocontinuous
  {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) :
  CocontinuousFunctor F :=
  fun J G => left_adjoint_PreservesColimitCocone A G.

(*
   本节说明伴随、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition lapc_is_acolimit
  {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U)
  {J : Category} {G : J ⟶ D} (L : Colimit G) :
  IsAColimit (F ◯ G) (F (colimit_apex L)) :=
  preserves_colimit (left_adjoint_preserves_colimit A G) L.
