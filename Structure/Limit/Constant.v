(** * Limits and colimits of a constant diagram *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Fun.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Cone.Const.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Limit.Components.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Theory.Connected.Components.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Instance.Zero.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Instance.Coq.
Require Import Category.Structure.Limit.Absolute.

(*
   本文件给出极限相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Open Scope category_scope.

Generalizable All Variables.

(*
   Book:      Mac Lane, "Categories for the Working Mathematician",
   nLab:      https://ncatlab.org/nlab/show/connected+category
   nLab:      https://ncatlab.org/nlab/show/constant+functor
   nLab:      https://ncatlab.org/nlab/show/diagonal+functor
   nLab:      https://ncatlab.org/nlab/show/limit
   nLab:      https://ncatlab.org/nlab/show/absolute+colimit

   本节说明函子、（余）极限、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The constant diagram, and the zig-zag closure that drives the file *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example const_fobj {J C : Category} (c : C) (x : J) :
  fobj[Δ[J](c)] x = c := eq_refl.

Example const_fmap {J C : Category} (c : C) {x y : J} (f : x ~{J}~> y) :
  fmap[Δ[J](c)] f = id[c] := eq_refl.

(*
   本节说明 Constant 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma leg_zigzag {J C : Category} {n c : C} (leg : ∀ x : J, n ~{C}~> c)
  (H : ∀ (x y : J) (f : x ~{J}~> y), leg x ≈ leg y)
  {x y : J} (s : ZigZag x y) : leg x ≈ leg y.
Proof.
  induction s as [w|x' y' z' f s' IH|x' y' z' f s' IH].
  - reflexivity.
  - now rewrite (H _ _ f).
  - now rewrite <- (H _ _ f).
Qed.

(** ** Part (a), the limit: the identity cone on c is limiting *)

Section ConstantLimit.

Context {J C : Category}.
Context (c : C).

(* No [Program], and no obligation: the coherence field is literally
   [id_left (id[c])]. *)

Definition const_acone : ACone c Δ[J](c) :=
  @Build_ACone J C c Δ[J](c) (fun _ => id[c]) (fun _ _ _ => id_left (id[c])).

Definition const_cone : Cone Δ[J](c) :=
  {| vertex_obj := c ; coneFrom := const_acone |}.

(* The single mathematical step: a cone over a constant diagram has legs
   that agree along every arrow of the shape. *)

Lemma const_cone_step (N : Cone Δ[J](c)) {x y : J} (f : x ~{J}~> y) :
  cone_leg N x ≈ cone_leg N y.
Proof.
  pose proof (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f) as Hc.
  unfold cone_leg. rewrite <- Hc. now rewrite id_left.
Qed.

Definition const_cone_zigzag (N : Cone Δ[J](c)) {x y : J} (s : ZigZag x y) :
  cone_leg N x ≈ cone_leg N y :=
  leg_zigzag (cone_leg N) (@const_cone_step N) s.

(*
   本节说明 Constant 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition const_IsALimit (K : ConnectedNonempty J) : IsALimit Δ[J](c) c.
Proof.
  unshelve econstructor.
  - exact const_acone.
  - intro N. unshelve econstructor.
    + exact (cone_leg N (cn_obj K)).
    + intro x. simpl. rewrite id_left.
      exact (const_cone_zigzag N (cn_zigzag K (cn_obj K) x)).
    + intros v Hv. specialize (Hv (cn_obj K)). simpl in Hv.
      rewrite id_left in Hv. symmetry. exact Hv.
Defined.

(* The cone-level and bundled readings cost nothing: Preservation.v's four
   conversions are proof-free, so both are [:=] with no tactic. *)

Definition const_IsLimitCone (K : ConnectedNonempty J) :
  IsLimitCone const_cone := @ump_limit _ _ _ _ (const_IsALimit K).

Definition const_Limit (K : ConnectedNonempty J) : Limit Δ[J](c) :=
  @Build_Limit J C Δ[J](c) const_cone
    (@ump_limit _ _ _ _ (const_IsALimit K)).

Example const_apex_strict : vertex_obj[const_cone] = c := eq_refl.

Example const_cone_leg_strict (x : J) : cone_leg const_cone x = id[c]
  := eq_refl.

Example const_leg_strict (K : ConnectedNonempty J) (x : J) :
  limit_leg (const_IsALimit K) x = id[c] := eq_refl.

Example const_med_strict (K : ConnectedNonempty J) (N : Cone Δ[J](c)) :
  limit_med (const_IsALimit K) N = cone_leg N (cn_obj K) := eq_refl.

End ConstantLimit.

(** ** Part (a), the colimit: built directly, not by op-instantiation *)

Section ConstantColimit.

Context {J C : Category}.
Context (c : C).

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example op_diag_fobj (x : J) :
  fobj[Opposite_Functor Δ[J](c)] x = fobj[@Diagonal (C^op) (J^op) c] x
  := eq_refl.

Example op_diag_fmap {x y : J^op} (f : x ~{J^op}~> y) :
  fmap[Opposite_Functor Δ[J](c)] f = fmap[@Diagonal (C^op) (J^op) c] f
  := eq_refl.

Fail Example op_diag_strict :
  Opposite_Functor Δ[J](c) = @Diagonal (C^op) (J^op) c := eq_refl.

Definition const_acocone :
  @ACone (J^op) (C^op) c (Opposite_Functor Δ[J](c)) :=
  @Build_ACone (J^op) (C^op) c (Opposite_Functor Δ[J](c))
    (fun _ => id[c]) (fun _ _ _ => id_left (id[c])).

Definition const_cocone : Cocone Δ[J](c) :=
  @Build_Cone (J^op) (C^op) (Opposite_Functor Δ[J](c)) c const_acocone.

Lemma const_cocone_step (N : Cocone Δ[J](c)) {x y : J} (f : x ~{J}~> y) :
  cone_leg N x ≈ cone_leg N y.
Proof.
  pose proof (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) y x f) as Hc.
  unfold cone_leg. rewrite <- Hc. symmetry. now rewrite id_left.
Qed.

(*
   本节说明 Constant 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition const_cocone_zigzag (N : Cocone Δ[J](c)) {x y : J}
  (s : ZigZag x y) : cone_leg N x ≈ cone_leg N y :=
  @leg_zigzag J (C^op) vertex_obj[N] c (cone_leg N)
    (@const_cocone_step N) x y s.

Definition const_IsAColimit (K : ConnectedNonempty J) : IsAColimit Δ[J](c) c.
Proof.
  unshelve econstructor.
  - exact const_acocone.
  - intro N. unshelve econstructor.
    + exact (cone_leg N (cn_obj K)).
    + intro x. simpl. rewrite id_right.
      exact (const_cocone_zigzag N (cn_zigzag K (cn_obj K) x)).
    + intros v Hv. specialize (Hv (cn_obj K)). simpl in Hv.
      rewrite id_right in Hv. symmetry. exact Hv.
Defined.

Definition const_IsColimitCocone (K : ConnectedNonempty J) :
  IsColimitCocone const_cocone := @ump_limit _ _ _ _ (const_IsAColimit K).

Definition const_Colimit (K : ConnectedNonempty J) : Colimit Δ[J](c) :=
  @Build_Limit (J^op) (C^op) (Opposite_Functor Δ[J](c)) const_cocone
    (@ump_limit _ _ _ _ (const_IsAColimit K)).

Example const_cocone_inj_strict (x : J) : cocone_inj const_cocone x = id[c]
  := eq_refl.

Example const_coinj_strict (K : ConnectedNonempty J) (x : J) :
  colimit_inj (const_IsAColimit K) x = id[c] := eq_refl.

Example const_comed_strict (K : ConnectedNonempty J) (N : Cocone Δ[J](c)) :
  colimit_med (const_IsAColimit K) N = cocone_inj N (cn_obj K) := eq_refl.

End ConstantColimit.

(** ** Part (d): these limits are absolute *)

(*
   本节说明函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition AbsoluteLimit {J C : Category} (G : J ⟶ C) (c : C) : Type :=
  ∀ (D : Category) (F : C ⟶ D), IsALimit (F ◯ G) (F c).

Definition AbsoluteColimit {J C : Category} (G : J ⟶ C) (c : C) : Type :=
  ∀ (D : Category) (F : C ⟶ D), IsAColimit (F ◯ G) (F c).

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition AbsoluteLimitCone_apex@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cone K} (A : AbsoluteLimitCone N) : AbsoluteLimit K vertex_obj[N] :=
  fun D F => limitcone_isalimit (A D F).

Definition AbsoluteColimitCocone_apex@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  {N : Cocone K} (A : AbsoluteColimitCocone N) :
  AbsoluteColimit K vertex_obj[N] :=
  fun D F => colimitcocone_isacolimit (A D F).

Section Absolute.

Context {J C : Category}.
Context (c : C).

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example const_image_fobj {D : Category} (F : C ⟶ D) (x : J) :
  fobj[F ◯ Δ[J](c)] x = fobj[Δ[J](F c)] x := eq_refl.

Fail Example const_image_fmap {D : Category} (F : C ⟶ D)
  {x y : J} (f : x ~{J}~> y) :
  fmap[F ◯ Δ[J](c)] f = fmap[Δ[J](F c)] f := eq_refl.

Lemma const_image_fmap_equiv {D : Category} (F : C ⟶ D)
  {x y : J} (f : x ~{J}~> y) :
  fmap[F ◯ Δ[J](c)] f ≈ fmap[Δ[J](F c)] f.
Proof. simpl. apply fmap_id. Qed.

Definition const_AbsoluteLimit (K : ConnectedNonempty J) :
  AbsoluteLimit Δ[J](c) c.
Proof.
  intros D F.
  unshelve econstructor.
  - unshelve econstructor.
    + intro x. exact (id[F c]).
    + intros x y f. simpl. rewrite fmap_id. now rewrite id_left.
  - intro N.
    assert (Hstep : ∀ (x y : J) (f : x ~{J}~> y),
              cone_leg N x ≈ cone_leg N y).
    { intros x y f.
      pose proof (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f) as Hc.
      unfold cone_leg. rewrite <- Hc. simpl.
      rewrite fmap_id. now rewrite id_left. }
    unshelve econstructor.
    + exact (cone_leg N (cn_obj K)).
    + intro x. simpl. rewrite id_left.
      exact (@leg_zigzag J D vertex_obj[N] (F c) (cone_leg N)
               Hstep _ _ (cn_zigzag K (cn_obj K) x)).
    + intros v Hv. specialize (Hv (cn_obj K)). simpl in Hv.
      rewrite id_left in Hv. symmetry. exact Hv.
Defined.

Definition const_AbsoluteColimit (K : ConnectedNonempty J) :
  AbsoluteColimit Δ[J](c) c.
Proof.
  intros D F.
  unshelve econstructor.
  - unshelve econstructor.
    + intro x. exact (id[F c]).
    + intros x y f. simpl. rewrite fmap_id. now rewrite id_left.
  - intro N.
    assert (Hstep : ∀ (x y : J) (f : x ~{J}~> y),
              @cone_leg (J^op) (D^op) _ N x ≈ @cone_leg (J^op) (D^op) _ N y).
    { intros x y f.
      pose proof (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) y x f) as Hc.
      unfold cone_leg. rewrite <- Hc. simpl.
      rewrite fmap_id. now rewrite id_right. }
    unshelve econstructor.
    + exact (@cone_leg (J^op) (D^op) _ N (cn_obj K)).
    + intro x. simpl. rewrite id_right.
      exact (@leg_zigzag J (D^op) vertex_obj[N] (F c)
               (@cone_leg (J^op) (D^op) _ N) Hstep _ _
               (cn_zigzag K (cn_obj K) x)).
    + intros v Hv. specialize (Hv (cn_obj K)). simpl in Hv.
      rewrite id_right in Hv. symmetry. exact Hv.
Defined.

Example const_absolute_leg_strict (K : ConnectedNonempty J)
  {D : Category} (F : C ⟶ D) (x : J) :
  limit_leg (const_AbsoluteLimit K D F) x = id[F c] := eq_refl.

Example const_absolute_coinj_strict (K : ConnectedNonempty J)
  {D : Category} (F : C ⟶ D) (x : J) :
  colimit_inj (const_AbsoluteColimit K D F) x = id[F c] := eq_refl.

End Absolute.

(** ** Part (b): the unit of Δ ⊣ lim is the mediating map, and invertible *)

Section LimitUnit.

Context {J C : Category}.
Context (L : HasLimitsOfShape J C).
Context (K : ConnectedNonempty J).
Context (c : C).

Definition const_unit : c ~{C}~> lim_obj L Δ[J](c) :=
  @unit ([J, C]) C (@Diagonal C J) (LimitFunctor L)
        (Diagonal_Limit_Adjunction L) c.

(* Both identifications are [eq_refl]: the unit IS the transpose of the
   identity, and IS the mediator out of the transposed cone. *)

Example const_unit_is_transpose :
  const_unit = lim_transpose_to L (@id ([J, C]) Δ[J](c)) := eq_refl.

Example const_unit_is_med :
  const_unit = lim_med L (lim_transpose_cone (@id ([J, C]) Δ[J](c)))
  := eq_refl.

Lemma lim_leg_const_agree (x y : J) :
  lim_leg L Δ[J](c) x ≈ lim_leg L Δ[J](c) y.
Proof using J C L K c.
  exact (@const_cone_zigzag J C c (@limit_cone J C Δ[J](c) (L Δ[J](c)))
           x y (cn_zigzag K x y)).
Qed.

(*
   本节说明 Constant 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma const_unit_section :
  lim_leg L Δ[J](c) (cn_obj K) ∘ const_unit ≈ id[c].
Proof.
  unfold const_unit.
  exact (lim_transpose_to_commutes L (@id ([J, C]) Δ[J](c)) (cn_obj K)).
Qed.

Lemma const_unit_retraction :
  const_unit ∘ lim_leg L Δ[J](c) (cn_obj K) ≈ id.
Proof.
  apply (lim_med_eq L (@limit_cone J C Δ[J](c) (L Δ[J](c)))); intro j.
  - transitivity (lim_leg L Δ[J](c) (cn_obj K)).
    + rewrite comp_assoc, (lim_leg_const_agree j (cn_obj K)).
      rewrite const_unit_section. now rewrite id_left.
    + exact (lim_leg_const_agree (cn_obj K) j).
  - now rewrite id_right.
Qed.

Definition const_unit_IsIsomorphism : IsIsomorphism const_unit :=
  {| two_sided_inverse := lim_leg L Δ[J](c) (cn_obj K)
   ; is_right_inverse  := const_unit_retraction
   ; is_left_inverse   := const_unit_section |}.

Definition const_unit_iso : c ≅ lim_obj L Δ[J](c) :=
  {| to := const_unit ; from := lim_leg L Δ[J](c) (cn_obj K)
   ; iso_to_from := const_unit_retraction
   ; iso_from_to := const_unit_section |}.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example const_unit_is_limit_unique_to_strict :
  const_unit = @limit_unique_to J C Δ[J](c) c (lim_obj L Δ[J](c))
                 (@const_IsALimit J C c K) (lim_alimit L Δ[J](c)) := eq_refl.

Example const_two_cones_same_legs (j : J) :
  cone_leg (lim_transpose_cone (@id ([J, C]) Δ[J](c))) j
    = cone_leg (alimit_cone (@const_IsALimit J C c K)) j := eq_refl.

Lemma const_unit_is_limit_unique_to :
  const_unit ≈ @limit_unique_to J C Δ[J](c) c (lim_obj L Δ[J](c))
                 (@const_IsALimit J C c K) (lim_alimit L Δ[J](c)).
Proof.
  symmetry.
  apply (lim_med_unique L (alimit_cone (@const_IsALimit J C c K))).
  intro j. unfold const_unit.
  exact (lim_transpose_to_commutes L (@id ([J, C]) Δ[J](c)) j).
Qed.

End LimitUnit.

(** ** Part (b), dually: the counit of colim ⊣ Δ is invertible *)

Section ColimitCounit.

Context {J C : Category}.
Context (M : HasColimitsOfShape J C).
Context (K : ConnectedNonempty J).
Context (c : C).

Definition const_counit : colim_obj M Δ[J](c) ~{C}~> c :=
  @counit C ([J, C]) (ColimitFunctor M) (@Diagonal C J)
          (Colimit_Diagonal_Adjunction M) c.

Example const_counit_is_transpose :
  const_counit = colim_transpose_from M (@id ([J, C]) Δ[J](c)) := eq_refl.

Lemma colim_inj_const_agree (x y : J) :
  colim_inj M Δ[J](c) x ≈ colim_inj M Δ[J](c) y.
Proof using J C M K c.
  exact (@const_cocone_zigzag J C c
           (@limit_cone (J^op) (C^op) _ (M Δ[J](c))) x y (cn_zigzag K x y)).
Qed.

Lemma const_counit_section :
  const_counit ∘ colim_inj M Δ[J](c) (cn_obj K) ≈ id[c].
Proof.
  unfold const_counit.
  exact (colim_transpose_from_commutes M (@id ([J, C]) Δ[J](c)) (cn_obj K)).
Qed.

Lemma const_counit_retraction :
  colim_inj M Δ[J](c) (cn_obj K) ∘ const_counit ≈ id.
Proof.
  apply (colim_med_eq M (@limit_cone (J^op) (C^op) _ (M Δ[J](c)))); intro j.
  - transitivity (colim_inj M Δ[J](c) (cn_obj K)).
    + rewrite <- comp_assoc, (colim_inj_const_agree j (cn_obj K)).
      rewrite const_counit_section. now rewrite id_right.
    + exact (colim_inj_const_agree (cn_obj K) j).
  - now rewrite id_left.
Qed.

Definition const_counit_IsIsomorphism : IsIsomorphism const_counit :=
  {| two_sided_inverse := colim_inj M Δ[J](c) (cn_obj K)
   ; is_right_inverse  := const_counit_section
   ; is_left_inverse   := const_counit_retraction |}.

Definition const_counit_iso : colim_obj M Δ[J](c) ≅ c :=
  {| to := const_counit ; from := colim_inj M Δ[J](c) (cn_obj K)
   ; iso_to_from := const_counit_section
   ; iso_from_to := const_counit_retraction |}.

End ColimitCounit.

(** ** Part (c): the diagonal is faithful on a point, full on a zig-zag *)

Section DiagonalFullyFaithful.

Context {J C : Category}.

(* Faithfulness costs only an OBJECT of J: two transformations agreeing
   everywhere agree at [j0], and their components at [j0] ARE the two
   morphisms. *)

Definition Diagonal_Faithful (j0 : J) : Faithful (@Diagonal C J).
Proof. construct. exact (X j0). Defined.

(* Naturality between two constant functors reads [id ∘ τx ≈ τy ∘ id], so
   the components agree along every arrow -- the transformation-level twin
   of [const_cone_step]. *)

Lemma const_transform_step {x y : C} (t : Δ[J](x) ⟹ Δ[J](y))
  {p q : J} (f : p ~{J}~> q) : transform[t] p ≈ transform[t] q.
Proof.
  pose proof (naturality[t] p q f) as Hn. simpl in Hn.
  rewrite id_left, id_right in Hn. exact Hn.
Qed.

Definition const_transform_zigzag {x y : C} (t : Δ[J](x) ⟹ Δ[J](y))
  {p q : J} (s : ZigZag p q) : transform[t] p ≈ transform[t] q :=
  leg_zigzag (fun j => transform[t] j) (@const_transform_step x y t) s.

Definition Diagonal_Full (K : ConnectedNonempty J) : Full (@Diagonal C J).
Proof.
  unshelve econstructor.
  - intros x y t. exact (transform[t] (cn_obj K)).
  - intros x y t j. simpl.
    exact (const_transform_zigzag t (cn_zigzag K (cn_obj K) j)).
Defined.

(* The same fullness read off part (a)'s mediator instead, through
   Structure/Cone/Const.v's [Cone_Natural_Transform]. *)

Definition Diagonal_Full_via_limit (K : ConnectedNonempty J) :
  Full (@Diagonal C J).
Proof.
  unshelve econstructor.
  - intros x y t.
    exact (limit_med (@const_IsALimit J C y K)
             {| vertex_obj := x
              ; coneFrom := fst (Cone_Natural_Transform Δ[J](y) x) t |}).
  - intros x y t j. simpl.
    pose proof (limit_med_commutes (@const_IsALimit J C y K)
      {| vertex_obj := x
       ; coneFrom := fst (Cone_Natural_Transform Δ[J](y) x) t |} j) as Hm.
    simpl in Hm. rewrite id_left in Hm. exact Hm.
Defined.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example Diagonal_Full_routes_agree (K : ConnectedNonempty J) (x y : C)
  (t : Δ[J](x) ⟹ Δ[J](y)) :
  @prefmap _ _ _ (Diagonal_Full_via_limit K) x y t
    = @prefmap _ _ _ (Diagonal_Full K) x y t := eq_refl.

End DiagonalFullyFaithful.

(** ** Inhabitedness is necessary: the empty shape computes a terminal
       object, not c *)

Definition zero_ACone {C : Category} (c n : C) : ACone n Δ[_0](c) :=
  @Build_ACone _0 C n Δ[_0](c)
    (fun x => match x with end) (fun x _ _ => match x with end).

Definition zero_Cone {C : Category} (c n : C) : Cone Δ[_0](c) :=
  {| vertex_obj := n ; coneFrom := zero_ACone c n |}.

(* Over [_0] a cone is a BARE APEX, so the universal property IS
   terminality -- proved in both directions. *)

Theorem zero_const_limit_IsTerminalObj {C : Category} {c : C} :
  IsALimit Δ[_0](c) c → IsTerminalObj c.
Proof.
  intros H d.
  destruct (@ump_limit _ _ _ _ H (zero_Cone c d)) as [u _ Hu].
  unshelve econstructor.
  - exact u.
  - exact I.
  - intros v _. apply Hu. intro x. destruct x.
Defined.

Theorem IsTerminalObj_zero_const_limit {C : Category} {c : C} :
  IsTerminalObj c → IsALimit Δ[_0](c) c.
Proof.
  intro T.
  unshelve econstructor.
  - exact (zero_ACone c c).
  - intro N. unshelve econstructor.
    + exact (unique_obj (T vertex_obj[N])).
    + intro x. destruct x.
    + intros v _. apply (uniqueness (T vertex_obj[N])). exact I.
Defined.

Theorem TwoX_not_terminal : IsTerminalObj (TwoX : _2) → False.
Proof.
  intro T. exact (TwoHom_Y_X_absurd (unique_obj (T (TwoY : _2)))).
Qed.

Theorem zero_const_limit_needs_inhabited :
  IsALimit Δ[_0]((TwoX : _2)) (TwoX : _2) → False.
Proof.
  intro H. exact (TwoX_not_terminal (zero_const_limit_IsTerminalObj H)).
Qed.

(* The bare in-tree [Connected] reading of part (a) is FALSE. *)

Theorem const_limit_not_from_bare_connected :
  (∀ (J C : Category) (c : C), Connected J → IsALimit Δ[J](c) c) → False.
Proof.
  intro H.
  exact (zero_const_limit_needs_inhabited
           (H _0 _2 (TwoX : _2) Zero_Connected)).
Qed.

Theorem Diagonal_Zero_not_Faithful : Faithful (@Diagonal Coq _0) → False.
Proof.
  intro F.
  assert (Hn : @id Coq bool ≈ negb).
  { apply (@fmap_inj _ _ _ F). intro x. destruct x. }
  exact (Bool.diff_true_false (Hn true)).
Qed.

(** ** Connectedness is necessary: a two-object discrete shape *)

Definition td_ACone {C : Category} {c d : C} (p q : d ~{C}~> c) :
  ACone d Δ[Two_Discrete](c).
Proof.
  unshelve econstructor.
  - intro x. destruct x; [ exact p | exact q ].
  - intros x y f. destruct f; simpl; cat.
Defined.

Definition td_Cone {C : Category} {c d : C} (p q : d ~{C}~> c) :
  Cone Δ[Two_Discrete](c) :=
  {| vertex_obj := d ; coneFrom := td_ACone p q |}.

Section TwoDiscreteRefutation.

Context (H : IsALimit Δ[Two_Discrete]((bool : Coq)) (bool : Coq)).

Definition tdX : bool → bool := limit_leg H TwoDX.
Definition tdY : bool → bool := limit_leg H TwoDY.

(* The EXISTENCE half of the universal property alone, at apex [unit] with
   constant legs, makes ⟨tdX, tdY⟩ : bool → bool × bool surjective. *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma td_surj (a b : bool) : { z : bool & (tdX z = a) * (tdY z = b) }.
Proof using H.
  destruct (@ump_limit _ _ _ _ H
              (@td_Cone Coq (bool : Coq) (poly_unit : Coq)
                 (fun _ => a) (fun _ => b))) as [u Hu _].
  exists (u ttt).
  exact (Hu TwoDX ttt, Hu TwoDY ttt).
Defined.

(* [False] mentions no section variable, so the [Proof using] is explicit;
   the Theory/Category/Monoid.v precedent. *)

Theorem td_const_not_limit : False.
Proof using H.
  destruct (td_surj true  true)  as [z1 [Ha1 Hb1]].
  destruct (td_surj true  false) as [z2 [Ha2 Hb2]].
  destruct (td_surj false true)  as [z3 [Ha3 Hb3]].
  destruct z1, z2, z3; congruence.
Qed.

End TwoDiscreteRefutation.

Definition two_discrete_const_not_limit :
  IsALimit Δ[Two_Discrete]((bool : Coq)) (bool : Coq) → False :=
  td_const_not_limit.

Theorem const_limit_not_from_point_alone :
  (∀ (J C : Category) (c : C), J → IsALimit Δ[J](c) c) → False.
Proof.
  intro H.
  exact (two_discrete_const_not_limit
           (H Two_Discrete Coq (bool : Coq) TwoDX)).
Qed.

(* What the disconnected shape computes INSTEAD: the binary product.  So
   what is refuted is quantitative, not existence. *)

Definition td_const_IsALimit_product {C : Category} `{@Cartesian C} (c : C) :
  IsALimit Δ[Two_Discrete](c) (c × c).
Proof.
  unshelve econstructor.
  - exact (td_ACone exl exr).
  - intro N. unshelve econstructor.
    + exact (cone_leg N TwoDX △ cone_leg N TwoDY).
    + intro x. destruct x; simpl; cat.
    + intros v Hv. symmetry.
      apply (snd (ump_products _ _ v)).
      split; [ exact (Hv TwoDX) | exact (Hv TwoDY) ].
Defined.

Lemma punit_irrel (a b : poly_unit) : a = b.
Proof. destruct a, b; reflexivity. Qed.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition td_const_IsALimit_at_unit :
  IsALimit Δ[Two_Discrete]((poly_unit : Coq)) (poly_unit : Coq).
Proof.
  unshelve econstructor.
  - exact (td_ACone (fun _ => ttt) (fun _ => ttt)).
  - intro N. unshelve econstructor.
    + exact (fun _ => ttt).
    + intros x y. apply punit_irrel.
    + intros v _ y. apply punit_irrel.
Defined.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition td_split :
  Δ[Two_Discrete]((bool : Coq)) ⟹ Δ[Two_Discrete]((bool : Coq)) := {|
  transform := fun j => match j with
                        | TwoDX => @id Coq bool
                        | TwoDY => negb
                        end
|}.
Next Obligation. destruct f; reflexivity. Qed.
Next Obligation. destruct f; reflexivity. Qed.

Theorem Diagonal_Two_Discrete_not_Full :
  Full (@Diagonal Coq Two_Discrete) → False.
Proof.
  intro F.
  pose proof (@fmap_sur _ _ _ F (bool : Coq) (bool : Coq) td_split) as Hs.
  pose proof (Hs TwoDX true) as H1.
  pose proof (Hs TwoDY true) as H2.
  simpl in H1, H2. congruence.
Qed.

(** ** Non-vacuity: the walking arrow *)

(* [Two_Connected] is Structure/Limit/Components.v, consumed rather
   than rebuilt. *)

Definition two_ConnectedNonempty : ConnectedNonempty _2 :=
  Build_ConnectedNonempty (TwoX : _2) Two_Connected.

Definition two_const_IsALimit {C : Category} (c : C) :
  IsALimit Δ[_2](c) c := @const_IsALimit _2 C c two_ConnectedNonempty.

Definition two_const_IsAColimit {C : Category} (c : C) :
  IsAColimit Δ[_2](c) c := @const_IsAColimit _2 C c two_ConnectedNonempty.

Definition two_const_AbsoluteLimit {C : Category} (c : C) :
  AbsoluteLimit Δ[_2](c) c :=
  @const_AbsoluteLimit _2 C c two_ConnectedNonempty.

(* The shape is not degenerate: two distinct objects, a crossing arrow, and
   provably NO arrow back -- so the zig-zag, not a single arrow, is what
   joins [TwoY] to [TwoX]. *)

Theorem two_objects_distinct : (TwoX : _2) = TwoY → False.
Proof. discriminate. Qed.

Definition two_crossing_arrow : TwoX ~{_2}~> TwoY := TwoXY.

Theorem two_no_arrow_back : (TwoY ~{_2}~> TwoX) → False.
Proof. intro f. inversion f. Qed.

Example two_const_leg_strict {C : Category} (c : C) (x : _2) :
  limit_leg (two_const_IsALimit c) x = id[c] := eq_refl.

Example two_const_med_strict {C : Category} (c : C) (N : Cone Δ[_2](c)) :
  limit_med (two_const_IsALimit c) N = cone_leg N TwoX := eq_refl.

(** ** Universe probe: the two identifications are the DONORS' *)

(*
   本节说明hom、（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UniverseProbe.

Universes jo jh jp co ch cp.
Constraint jh < jp.
Constraint jh < ch.

Context (Ju : Category@{jo jh jp}) (Cu : Category@{co ch cp}) (x : Cu).

Check (obj[Ju]).
Check (∀ a b : Ju, a ~{Ju}~> b).
Check (@ACone Ju Cu x).
Check (@Cone Ju Cu).

Fail Check (@Diagonal Cu Ju).
Fail Check (@IsALimit Ju Cu).

End UniverseProbe.
