(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.

Generalizable All Variables.

(** * Topological indistinguishability

    Two points are indistinguishable when every open tested holds of
    one exactly when it holds of the other.  The opens tested are
    those valued at the level [s], strictly below the space's own
    level [o]; see the header for why the unrestricted relation cannot
    be a space's `≈` in this library. *)

Definition SameOpens@{s o | s < o +} (X : TopSpace@{o}) (x y : X)
  : Type@{o} :=
  ∀ U : X → Type@{s}, IsOpen X U → (U x ↔ U y).

Lemma SameOpens_refl (X : TopSpace) (x : X) : SameOpens X x x.
Proof. intros U HU; split; exact (fun w => w). Defined.

Lemma SameOpens_sym (X : TopSpace) (x y : X) :
  SameOpens X x y → SameOpens X y x.
Proof.
  intros H U HU; destruct (H U HU) as [f g]; split; assumption.
Defined.

Lemma SameOpens_trans (X : TopSpace) (x y z : X) :
  SameOpens X x y → SameOpens X y z → SameOpens X x z.
Proof.
  intros Hxy Hyz U HU.
  destruct (Hxy U HU) as [f1 g1]; destruct (Hyz U HU) as [f2 g2].
  split; auto.
Defined.

(* Equivalent points are indistinguishable: this is [open_proper],
   used in both directions. *)
Lemma SameOpens_of_equiv (X : TopSpace) (x y : X) :
  x ≈ y → SameOpens X x y.
Proof.
  intros Hxy U HU; split.
  - exact (open_proper X U HU x y Hxy).
  - exact (open_proper X U HU y x (symmetry Hxy)).
Defined.

(** * Agreement on ALL opens

    The unrestricted relation.  It is a perfectly good predicate; what
    it cannot be, for the reason measured in the header, is the
    equivalence of a [SetoidObject@{o o}].  It is used only to state
    [Hausdorff_T0_nn]. *)

Definition SameOpensAll (X : TopSpace) (x y : X) : Type :=
  ∀ U : X → Type, IsOpen X U → (U x ↔ U y).

Lemma SameOpensAll_SameOpens (X : TopSpace) (x y : X) :
  SameOpensAll X x y → SameOpens X x y.
Proof. intros H U HU; exact (H U HU). Defined.

(** * T0 spaces

    Kolmogorov's axiom in its setoid reading: indistinguishable points
    are equal -- the same move Instance/Pos.v makes for
    antisymmetry ([pos_antisym : pos_le x y → pos_le y x → x ≈ y]),
    where the conclusion is the carrier's `≈` rather than Leibniz
    equality. *)

Definition IsT0 (X : TopSpace) : Type :=
  ∀ x y : X, SameOpens X x y → x ≈ y.

Definition T0_Subcategory : Subcategory Top :=
  @Build_Subcategory Top
    (fun X : Top => IsT0 X)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition T0Spaces : Category := Sub Top T0_Subcategory.

Lemma T0_Full :
  Category.Construction.Subcategory.Full Top T0_Subcategory.
Proof. intros x y ox oy g; exact I. Defined.

Lemma T0_Incl_Full : Functor.Full (Incl Top T0_Subcategory).
Proof.
  exact (Full_Implies_Full_Functor Top T0_Subcategory T0_Full).
Defined.

Lemma T0_Incl_Faithful : Functor.Faithful (Incl Top T0_Subcategory).
Proof. exact (Incl_Faithful Top T0_Subcategory). Defined.

(** * The Kolmogorov quotient

    Same carrier, coarser `≈`, and as opens exactly those opens of X
    that respect the coarser `≈`. *)

Definition kq_setoid (X : TopSpace) : SetoidObject :=
  {| carrier := top_carrier X
   ; is_setoid :=
       {| equiv := SameOpens X
        ; setoid_equiv :=
            Build_Equivalence _ (SameOpens_refl X)
              (SameOpens_sym X) (SameOpens_trans X) |} |}.

Definition kq_open (X : TopSpace) (V : top_carrier X → Type) : Type :=
  (IsOpen X V *
   (∀ x y : top_carrier X, SameOpens X x y → V x → V y))%type.

Lemma kq_respects (X : TopSpace) (U V : top_carrier X → Type) :
  (∀ x, U x ↔ V x) → kq_open X U → kq_open X V.
Proof.
  intros HUV [HU Hr]; split.
  - exact (open_respects X U V HUV HU).
  - intros x y Hxy Vx.
    exact (fst (HUV y) (Hr x y Hxy (snd (HUV x) Vx))).
Defined.

Lemma kq_proper (X : TopSpace) (V : top_carrier X → Type) :
  kq_open X V → ∀ x y : top_carrier X, SameOpens X x y → V x → V y.
Proof. intros [HV Hr]; exact Hr. Defined.

Lemma kq_union (X : TopSpace) (I : Type)
      (U : I → (top_carrier X → Type)) :
  (∀ i, kq_open X (U i)) →
  kq_open X (fun x => { i : I & U i x }).
Proof.
  intro HU; split.
  - exact (open_union X I U (fun i => fst (HU i))).
  - intros x y Hxy w.
    exact (projT1 w; snd (HU (projT1 w)) x y Hxy (projT2 w)).
Defined.

Lemma kq_whole (X : TopSpace) : kq_open X (fun _ => poly_unit).
Proof.
  split; [ exact (open_whole X) | intros x y _ w; exact w ].
Defined.

Lemma kq_inter (X : TopSpace) (U V : top_carrier X → Type) :
  kq_open X U → kq_open X V →
  kq_open X (fun x => U x ∧ V x).
Proof.
  intros [HU HrU] [HV HrV]; split.
  - exact (open_inter X U V HU HV).
  - intros x y Hxy w.
    exact (HrU x y Hxy (fst w), HrV x y Hxy (snd w)).
Defined.

Definition KolmogorovQuotient (X : TopSpace) : TopSpace :=
  {| top_carrier   := kq_setoid X
   ; IsOpen        := kq_open X
   ; open_respects := kq_respects X
   ; open_proper   := kq_proper X
   ; open_union    := kq_union X
   ; open_whole    := kq_whole X
   ; open_inter    := kq_inter X |}.

(* THE CRUX.  An open of [X] whose values lie at the level the
   indistinguishability relation tests respects that relation
   AUTOMATICALLY, because the relation says in so many words that x
   and y agree on it.  So every such open of X is still an open of the
   quotient, with no hypothesis, and that is what makes the definition
   of [SameOpens] and the definition of [kq_open] non-circular. *)
Lemma small_open_is_kq_open (X : TopSpace) (U : X → Type) :
  IsOpen X U → IsOpen (KolmogorovQuotient X) U.
Proof.
  intro HU; split; [ exact HU | ].
  intros a b Hab; exact (fst (Hab U HU)).
Defined.

Lemma KolmogorovQuotient_T0 (X : TopSpace) :
  IsT0 (KolmogorovQuotient X).
Proof.
  intros x y H U HU.
  exact (H U (small_open_is_kq_open X U HU)).
Defined.

Definition kq_proj_setoid (X : TopSpace) :
  SetoidMorphism (top_carrier X) (top_carrier (KolmogorovQuotient X)).
Proof.
  refine {| morphism := fun x : top_carrier X => x |}.
  intros x y Hxy; exact (SameOpens_of_equiv X x y Hxy).
Defined.

Lemma kq_proj_continuous (X : TopSpace) :
  Continuous X (KolmogorovQuotient X) (kq_proj_setoid X).
Proof. intros V HV; exact (fst HV). Defined.

Definition kolmogorov_proj (X : TopSpace)
  : X ~{Top}~> KolmogorovQuotient X :=
  Build_ContinuousMorphism X (KolmogorovQuotient X)
    (kq_proj_setoid X) (kq_proj_continuous X).

(** * The universal property *)

(* A continuous map into a T0 space cannot tell indistinguishable
   points apart: pulling back a level-[s] open of the target along f
   gives a level-[s] open of the source. *)
Definition kq_med_resp {X D : TopSpace} (HD : IsT0 D)
    (f : X ~{Top}~> D) (x y : top_carrier X) :
  SameOpens X x y → continuous_map f x ≈ continuous_map f y.
Proof.
  intro Hxy.
  apply HD.
  intros V HV.
  exact (Hxy (fun z => V (continuous_map f z)) (continuity f V HV)).
Defined.

Definition kq_med_setoid {X D : TopSpace} (HD : IsT0 D)
    (f : X ~{Top}~> D) :
  SetoidMorphism (top_carrier (KolmogorovQuotient X)) (top_carrier D).
Proof.
  refine {| morphism := fun x => continuous_map f x |}.
  intros x y Hxy; exact (kq_med_resp HD f x y Hxy).
Defined.

Lemma kq_med_continuous {X D : TopSpace} (HD : IsT0 D)
    (f : X ~{Top}~> D) :
  Continuous (KolmogorovQuotient X) D (kq_med_setoid HD f).
Proof.
  intros V HV; split.
  - exact (continuity f V HV).
  - intros x y Hxy Vfx.
    exact (open_proper D V HV _ _ (kq_med_resp HD f x y Hxy) Vfx).
Defined.

Definition kolmogorov_med {X D : TopSpace} (HD : IsT0 D)
    (f : X ~{Top}~> D) : KolmogorovQuotient X ~{Top}~> D :=
  Build_ContinuousMorphism (KolmogorovQuotient X) D
    (kq_med_setoid HD f) (kq_med_continuous HD f).

Definition KolmogorovT0 (X : TopSpace) : T0Spaces :=
  (KolmogorovQuotient X; KolmogorovQuotient_T0 X).

Theorem kolmogorov_universal (X : TopSpace) :
  ∀ (d : T0Spaces) (f : X ~{Top}~> Incl Top T0_Subcategory d),
    ∃! g : KolmogorovT0 X ~{T0Spaces}~> d,
      f ≈ fmap[Incl Top T0_Subcategory] g ∘ kolmogorov_proj X.
Proof.
  intros d f.
  unshelve eexists.
  - exact (kolmogorov_med `2 d f; I).
  - intro x; simpl; reflexivity.
  - intros g Hg x; simpl.
    exact (Hg x).
Defined.

Definition kolmogorov_universal_arrow (X : TopSpace)
  : @UniversalArrow Top T0Spaces X (Incl Top T0_Subcategory) :=
  @universal_arrow_from_UMP Top T0Spaces X (Incl Top T0_Subcategory)
    (KolmogorovT0 X) (kolmogorov_proj X) (kolmogorov_universal X).

Definition T0_reflector : Top ⟶ T0Spaces :=
  LeftAdjointFunctorFromUniversalArrows (Incl Top T0_Subcategory)
    kolmogorov_universal_arrow.

Definition T0_adj : T0_reflector ⊣ Incl Top T0_Subcategory :=
  AdjunctionFromUniversalArrows (Incl Top T0_Subcategory)
    kolmogorov_universal_arrow.

Definition T0_Reflective_in_Top : Reflective T0_Subcategory :=
  @Build_Reflective Top T0_Subcategory T0_Full T0_reflector T0_adj.

(** * Strict readbacks *)

Example kq_carrier_strict (X : TopSpace) :
  carrier (top_carrier (KolmogorovQuotient X)) = carrier (top_carrier X)
  := eq_refl.

Example kq_equiv_strict (X : TopSpace) (x y : top_carrier X) :
  @equiv _ (is_setoid (top_carrier (KolmogorovQuotient X))) x y
    = SameOpens X x y := eq_refl.

Example t0_reflector_obj (X : TopSpace) :
  `1 (fobj[T0_reflector] X) = KolmogorovQuotient X := eq_refl.

Example kolmogorov_arrow_is_proj (X : TopSpace) :
  @arrow Top T0Spaces X (Incl Top T0_Subcategory)
    (kolmogorov_universal_arrow X) = kolmogorov_proj X := eq_refl.

Example kolmogorov_arrow_obj (X : TopSpace) :
  @arrow_obj Top T0Spaces X (Incl Top T0_Subcategory)
    (kolmogorov_universal_arrow X) = KolmogorovT0 X := eq_refl.

Definition t0_unit (X : TopSpace)
  : X ~{Top}~> Incl Top T0_Subcategory (fobj[T0_reflector] X) :=
  @Category.Theory.Adjunction.unit _ _ _ _ T0_adj X.

Example t0_unit_is_proj (X : TopSpace) (x : X) :
  continuous_map (t0_unit X) x = continuous_map (kolmogorov_proj X) x
  := eq_refl.

Lemma t0_unit_is_proj_hom (X : TopSpace) :
  t0_unit X ≈ kolmogorov_proj X.
Proof. intro x; reflexivity. Defined.

(* A T0 space is its own Kolmogorov quotient, up to isomorphism in the
   subcategory: the counit of a full reflective subcategory. *)
Definition t0_reflect_iso (x : T0Spaces) :
  fobj[T0_reflector] (Incl Top T0_Subcategory x) ≅[T0Spaces] x :=
  reflective_counit_iso T0_Reflective_in_Top x.

(** * Hausdorff spaces

    What comes out is a DOUBLE NEGATION, against the unrestricted
    relation; see the header for the two independent reasons this does
    not give [IsT0]. *)

Lemma Hausdorff_T0_nn (X : TopSpace) (H : IsHausdorff X) (x y : X) :
  SameOpensAll X x y → ¬ ¬ (x ≈ y).
Proof.
  intros Hxy Hne.
  destruct (H x y Hne) as [U [V [[HU HV] [[Ux Vy] Hdisj]]]].
  exact (Hdisj y (fst (Hxy U HU) Ux) Vy).
Defined.

(** * Non-vacuity: the two-point discrete space is T0 *)

Lemma bool_point_open (x : bool_setoid_object) :
  IsOpen Bool_Discrete (fun z : bool_setoid_object => z = x).
Proof. intros a b Hab Ha; simpl in Hab; now subst. Defined.

Theorem Bool_Discrete_T0 : IsT0 Bool_Discrete.
Proof.
  intros x y H.
  symmetry.
  exact (fst (H (fun z : bool_setoid_object => z = x)
                (bool_point_open x)) eq_refl).
Defined.

Definition Bool_Discrete_T0Space : T0Spaces :=
  (Bool_Discrete; Bool_Discrete_T0).

Definition bool_reflect_iso :
  fobj[T0_reflector] (Incl Top T0_Subcategory Bool_Discrete_T0Space)
    ≅[T0Spaces] Bool_Discrete_T0Space :=
  t0_reflect_iso Bool_Discrete_T0Space.

(** * Non-vacuity: the two-point indiscrete space is not T0 *)

Lemma indiscrete_points_same_opens :
  SameOpens TwoPoint_Indiscrete true false.
Proof.
  intros U HU; split; intro w.
  - exact (HU true false w).
  - exact (HU false true w).
Defined.

Theorem TwoPoint_Indiscrete_not_T0 : IsT0 TwoPoint_Indiscrete → False.
Proof.
  intro H.
  pose proof (H true false indiscrete_points_same_opens) as Heq.
  simpl in Heq; discriminate.
Defined.

Example indiscrete_quot_identifies :
  @equiv _ (is_setoid (top_carrier
              (KolmogorovQuotient TwoPoint_Indiscrete))) true false
  := indiscrete_points_same_opens.

(** * Non-vacuity: a three-point space merging exactly one pair

    The opens are the predicates that cannot tell [Tri_l] from
    [Tri_r]; [Tri_pt] is separated from both by a [Prop]-valued
    open. *)

Inductive Tri : Set := Tri_l | Tri_r | Tri_pt.

Definition Tri_setoid : SetoidObject :=
  {| carrier := Tri; is_setoid := eq_Setoid Tri |}.

Definition tri_open (U : Tri_setoid → Type) : Type :=
  ((U Tri_l → U Tri_r) * (U Tri_r → U Tri_l))%type.

Lemma tri_respects (U V : Tri_setoid → Type) :
  (∀ x, U x ↔ V x) → tri_open U → tri_open V.
Proof.
  intros HUV [f g]; split; intro w.
  - exact (fst (HUV Tri_r) (f (snd (HUV Tri_l) w))).
  - exact (fst (HUV Tri_l) (g (snd (HUV Tri_r) w))).
Defined.

Lemma tri_proper (U : Tri_setoid → Type) :
  tri_open U → ∀ x y : Tri_setoid, x ≈ y → U x → U y.
Proof. intros _ x y Hxy Ux; simpl in Hxy; now subst. Defined.

Lemma tri_union (I : Type) (U : I → (Tri_setoid → Type)) :
  (∀ i, tri_open (U i)) →
  tri_open (fun x => { i : I & U i x }).
Proof.
  intro HU; split; intro w.
  - exact (projT1 w; fst (HU (projT1 w)) (projT2 w)).
  - exact (projT1 w; snd (HU (projT1 w)) (projT2 w)).
Defined.

Lemma tri_whole : tri_open (fun _ => poly_unit).
Proof. split; intro w; exact w. Defined.

Lemma tri_inter (U V : Tri_setoid → Type) :
  tri_open U → tri_open V → tri_open (fun x => U x ∧ V x).
Proof.
  intros [f1 g1] [f2 g2]; split; intro w.
  - exact (f1 (fst w), f2 (snd w)).
  - exact (g1 (fst w), g2 (snd w)).
Defined.

Definition Tri_Top : TopSpace :=
  {| top_carrier   := Tri_setoid
   ; IsOpen        := tri_open
   ; open_respects := tri_respects
   ; open_proper   := tri_proper
   ; open_union    := tri_union
   ; open_whole    := tri_whole
   ; open_inter    := tri_inter |}.

Lemma tri_pair_same_opens : SameOpens Tri_Top Tri_l Tri_r.
Proof. intros U HU; split; [ exact (fst HU) | exact (snd HU) ]. Defined.

Theorem Tri_Top_not_T0 : IsT0 Tri_Top → False.
Proof.
  intro H.
  pose proof (H Tri_l Tri_r tri_pair_same_opens) as Heq.
  simpl in Heq; discriminate.
Defined.

Lemma tri_point_open :
  IsOpen Tri_Top (fun z : Tri_setoid => z = Tri_pt).
Proof. split; intro w; discriminate w. Defined.

Theorem tri_point_apart : SameOpens Tri_Top Tri_l Tri_pt → False.
Proof.
  intro H.
  pose proof (snd (H (fun z : Tri_setoid => z = Tri_pt) tri_point_open)
                eq_refl) as Heq.
  discriminate Heq.
Defined.

Example tri_quot_merges :
  @equiv _ (is_setoid (top_carrier (KolmogorovQuotient Tri_Top)))
    Tri_l Tri_r := tri_pair_same_opens.

Theorem tri_quot_keeps_point_apart :
  @equiv _ (is_setoid (top_carrier (KolmogorovQuotient Tri_Top)))
    Tri_l Tri_pt → False.
Proof. exact tri_point_apart. Defined.

Definition Tri_T0 : T0Spaces := KolmogorovT0 Tri_Top.
