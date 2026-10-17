Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Product.Limit.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.Pullback.Wide.Complete.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Discrete.Reconstruct.

Generalizable All Variables.

(* * * Well-powered co-well-powered 范畴 （已译） *)

(*
   nLab:      https://ncatlab.org/nlab/show/subobject
   Wikipedia: https://en.wikipedia.org/wiki/Subobject

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record WellPoweredAt {C : Category} (x : C) := {
  wp_index   : Type;
  wp_to      : wp_index → SubObj x;
  wp_from    : SubObj x → wp_index;
  wp_to_from : ∀ u : SubObj x, wp_to (wp_from u) ≈ u
}.

Arguments wp_index {C x} _.
Arguments wp_to {C x} _ _.
Arguments wp_from {C x} _ _.
Arguments wp_to_from {C x} _ _.

(* 相关说明。 （已译） *)

Section Bijection.

Context {C : Category} {x : C} (W : WellPoweredAt x).

(* 相关说明。 （已译） *)
Definition wp_rel : crelation (wp_index W) :=
  fun i j => wp_to W i ≈ wp_to W j.

Lemma wp_rel_equiv : Equivalence wp_rel.
Proof.
  unfold wp_rel; constructor.
  - intro i; reflexivity.
  - intros i j H; symmetry; exact H.
  - intros i j k H1 H2; etransitivity; [exact H1 | exact H2].
Defined.

Definition wp_index_setoid : Setoid (wp_index W) :=
  {| equiv := wp_rel; setoid_equiv := wp_rel_equiv |}.

Lemma wp_to_resp (i j : wp_index W) :
  @equiv _ wp_index_setoid i j → wp_to W i ≈ wp_to W j.
Proof. intro H; exact H. Qed.

Lemma wp_from_resp (u v : SubObj x) :
  u ≈ v → @equiv _ wp_index_setoid (wp_from W u) (wp_from W v).
Proof.
  intro H; simpl; unfold wp_rel.
  etransitivity; [exact (wp_to_from W u)|].
  etransitivity; [exact H|].
  symmetry; exact (wp_to_from W v).
Qed.

Lemma wp_from_to (i : wp_index W) :
  @equiv _ wp_index_setoid (wp_from W (wp_to W i)) i.
Proof. exact (wp_to_from W (wp_to W i)). Qed.

End Bijection.

(** ** The pinned notion *)

(*
   本节说明hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition WellPowered@{o h w s t | w <= h, o <= s, h <= s, h < t +}
  (C : Category@{o h h}) :=
  ∀ x : C, WellPoweredAt@{w o s h t} x.

Definition CoWellPowered@{o h w s t | w <= h, o <= s, h <= s, h < t +}
  (C : Category@{o h h}) :=
  WellPowered@{o h w s t} (C^op).

(* * ** Co-well-powered well-powered over quotient 对象 （已译） *)

Section Quotients.

Context {C : Category} {x : C}.

Example quot_obj_is_sub_op : @QuotObj C x = @SubObj (C^op) x := eq_refl.

Example quot_setoid_is_sub_setoid_op :
  @QuotObj_Setoid C x = @SubObj_Setoid (C^op) x := eq_refl.

(* 相关说明。 （已译） *)
Lemma cowp_to_from (W : @WellPoweredAt (C^op) x) (q : QuotObj x) :
  @equiv _ (@QuotObj_Setoid C x) (wp_to W (wp_from W q)) q.
Proof. exact (wp_to_from W q). Qed.

End Quotients.

(* 相关说明。 （已译） *)

(* Adjoining top subobject family changes none its lower
 bounds, it gives index point ([None]), which Theory/Subobject/
 Lattice.v's [sub_wide_intersection] needs read wide 拉回 as a
 subobject.（已译） *)

Section SmallIntersections.

Context {C : Category} {x : C}.

Definition sub_opt_top {J : Type} (S : J → SubObj x) : option J → SubObj x :=
  fun o => match o with Some j => S j | None => sub_top end.

Lemma IsIntersection_drop_top {J : Type} (S : J → SubObj x) (w : SubObj x) :
  IsIntersection (sub_opt_top S) w → IsIntersection S w.
Proof.
  intros H; constructor.
  - intro j; exact (inter_le _ _ H (Some j)).
  - intros v Hv; apply (inter_greatest _ _ H).
    intros [j|]; [exact (Hv j) | exact (sub_top_greatest v)].
Defined.

End SmallIntersections.

(* The intersection ANY family indexed at below [Complete]'s
 shape-对象 universe, empty not, completeness alone. （已译） *)
Definition complete_intersection@{o h r so j +| so <= r, h <= r, j <= so +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C) {x : C}
  {J : Type@{j}} (S : J → SubObj x) : SubObj x :=
  sub_wide_intersection (sub_opt_top S) None
    (complete_wide_pullback comp
       (fun o => Subobject.sub_mono (sub_opt_top S o))).

Definition complete_intersection_IsIntersection@{o h r so j +|
    so <= r, h <= r, j <= so +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C) {x : C}
  {J : Type@{j}} (S : J → SubObj x) :
  IsIntersection@{o h j} S (complete_intersection comp S) :=
  IsIntersection_drop_top S _
    (sub_wide_intersection_IsIntersection (sub_opt_top S) None
       (complete_wide_pullback comp
          (fun o => Subobject.sub_mono (sub_opt_top S o)))).

(* 相关说明。 （已译） *)

(*
   本节说明拉回/推出、等价、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ClassIntersection.

Context {C : Category} {x : C}.
Context (W : WellPoweredAt x).
Context (P : SubObj x → Type).
Context (HP : ∀ m m' : SubObj x, m ≈ m' → P m → P m').

Definition wp_class_index : Type := { i : wp_index W & P (wp_to W i) }.

Definition wp_class_family (k : wp_class_index) : SubObj x := wp_to W (`1 k).

(*
   本节说明 WellPowered 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma IsIntersection_reindex (w : SubObj x) :
  IsIntersection wp_class_family w →
  IsIntersection (fun k : { m : SubObj x & P m } => `1 k) w.
Proof using HP.
  intros H; constructor.
  - intros [m p]; simpl.
    exact (sub_le_trans _ _ _
             (inter_le _ _ H
                (wp_from W m; HP m (wp_to W (wp_from W m))
                                (symmetry (wp_to_from W m)) p))
             (sub_le_of_equiv _ _ (wp_to_from W m))).
  - intros v Hv; apply (inter_greatest _ _ H).
    intros [i p]; exact (Hv (wp_to W i; p)).
Defined.

End ClassIntersection.

(* The per-object form: one object's well-poweredness datum suffices. *)
Definition wp_complete_class_intersection@{o h w s t r so p q +|
    h < t, o <= s, h <= s, so <= r, h <= r, w <= so, p <= so,
    o <= q, h <= q, p <= q +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C)
  {x : C} (W : WellPoweredAt@{w o s h t} x) (P : SubObj x → Type@{p})
  (HP : ∀ m m' : SubObj x, m ≈ m' → P m → P m') :
  { w : SubObj x &
    IsIntersection@{o h q} (fun k : { m : SubObj x & P m } => `1 k) w }.
Proof.
  exists (complete_intersection comp (wp_class_family W P)).
  exact (IsIntersection_reindex W P HP _
           (complete_intersection_IsIntersection comp _)).
Defined.

(* §V.8, as #451 reads it: a well-powered complete category has the
   intersection of every class of subobjects of every object. *)
Definition wellpowered_complete_has_intersections@{o h w s t r so p q +|
    w <= h, h < t, o <= s, h <= s, so <= r, h <= r, w <= so, p <= so,
    o <= q, h <= q, p <= q +}
  {C : Category@{o h h}}
  (WP : WellPowered@{o h w s t} C) (comp : @Complete@{r so h o} C) (x : C)
  (P : SubObj x → Type@{p}) (HP : ∀ m m' : SubObj x, m ≈ m' → P m → P m') :
  { w : SubObj x &
    IsIntersection@{o h q} (fun k : { m : SubObj x & P m } => `1 k) w } :=
  wp_complete_class_intersection comp (WP x) P HP.

(* 相关说明。 （已译） *)
Example wellpowered_intersection_is_small {C : Category}
  (WP : WellPowered C) (comp : @Complete C) (x : C)
  (P : SubObj x → Type) (HP : ∀ m m' : SubObj x, m ≈ m' → P m → P m') :
  `1 (wellpowered_complete_has_intersections WP comp x P HP)
    = complete_intersection comp (wp_class_family (WP x) P) := eq_refl.

(* 相关说明。 （已译） *)
Definition wellpowered_complete_has_intersections_prop@{o h w s t r so q +|
    w <= h, h < t, o <= s, h <= s, so <= r, h <= r, w <= so,
    o <= q, h <= q +}
  {C : Category@{o h h}}
  (WP : WellPowered@{o h w s t} C) (comp : @Complete@{r so h o} C) (x : C)
  (P : SubObj x → Prop) (HP : ∀ m m' : SubObj x, m ≈ m' → P m → P m') :
  { w : SubObj x &
    IsIntersection@{o h q} (fun k : { m : SubObj x & P m } => `1 k) w } :=
  wellpowered_complete_has_intersections WP comp x P HP.

(* 相关说明。 （已译） *)
Definition wellpowered_complete_intersection_all@{o h w s t r so q +|
    w <= h, h < t, o <= s, h <= s, so <= r, h <= r, w <= so,
    o <= q, h <= q +}
  {C : Category@{o h h}}
  (WP : WellPowered@{o h w s t} C) (comp : @Complete@{r so h o} C) (x : C) :
  { w : SubObj x & IsIntersection@{o h q} (fun m : SubObj x => m) w }.
Proof.
  pose (R := wellpowered_complete_has_intersections_prop
               WP comp x (fun _ => True) (fun _ _ _ t => t)).
  exists (`1 R); constructor.
  - intro m; exact (inter_le _ _ (`2 R) (m; I)).
  - intros v Hv; apply (inter_greatest _ _ (`2 R)).
    intros [m t]; exact (Hv m).
Defined.

(* ... which is the least subobject. *)
Definition wellpowered_complete_least_subobject@{o h w s t r so +|
    w <= h, h < t, o <= s, h <= s, so <= r, h <= r, w <= so +}
  {C : Category@{o h h}}
  (WP : WellPowered@{o h w s t} C) (comp : @Complete@{r so h o} C) (x : C) :
  { w : SubObj x & ∀ v : SubObj x, sub_le w v }.
Proof.
  exists (`1 (wellpowered_complete_intersection_all
                WP comp x)).
  exact (inter_le _ _
           (`2 (wellpowered_complete_intersection_all
                  WP comp x))).
Defined.

(* * ** The dual: cointersections classes quotient 对象 （已译） *)

Definition cowellpowered_cocomplete_has_cointersections@{o h w s t r so qo p q
    +| w <= h, h < t, o <= s, h <= s, so <= r, h <= r, w <= so, p <= so,
    o <= qo, h <= qo, qo <= q, p <= q +}
  {C : Category@{o h h}}
  (CWP : CoWellPowered@{o h w s t} C) (cocomp : @Cocomplete@{r so h o} C)
  (x : C) (P : QuotObj@{qo o h} x → Type@{p})
  (HP : ∀ q q' : QuotObj x, q ≈ q' → P q → P q') :
  { w : QuotObj@{qo o h} x &
    @IsIntersection@{o h q} (C^op) x _
      (fun k : { q : QuotObj x & P q } => `1 k) w } :=
  wellpowered_complete_has_intersections CWP
    (Complete_op_of_Cocomplete cocomp) x P HP.

(* 相关说明。 （已译） *)
Lemma cointersection_quot_le@{o h w s t r so qo p q +|
    w <= h, h < t, o <= s, h <= s, so <= r, h <= r, w <= so, p <= so,
    o <= qo, h <= qo, qo <= q, p <= q +}
  {C : Category@{o h h}}
  (CWP : CoWellPowered@{o h w s t} C) (cocomp : @Cocomplete@{r so h o} C)
  (x : C) (P : QuotObj@{qo o h} x → Type@{p})
  (HP : ∀ q q' : QuotObj x, q ≈ q' → P q → P q')
  (q : QuotObj x) (p : P q) :
  quot_le (`1 (cowellpowered_cocomplete_has_cointersections CWP cocomp x P HP))
    q.
Proof.
  exact (inter_le _ _
           (`2 (cowellpowered_cocomplete_has_cointersections CWP cocomp x P HP))
           (q; p)).
Defined.

(** ** Witnesses *)

(* The trivial datum: index is [SubObj x] itself. It exists at every
 对象 every 范畴, one universe too high be [WellPowered] in
 一般; [trivial_small] is case where it is not too high.（已译） *)
Definition wp_trivial@{o h w s t | o <= w, h <= w, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} (x : C) : WellPoweredAt@{w o s h t} x :=
  {| wp_index   := SubObj x;
     wp_to      := fun u => u;
     wp_from    := fun u => u;
     wp_to_from := fun u => Equivalence_Reflexive u |}.

(* A category whose objects sit at or below its homs is well-powered. *)
Definition trivial_small@{o h t | o <= h, h < t +}
  (C : Category@{o h h}) : WellPowered@{o h h h t} C :=
  fun x => wp_trivial x.

(* A 范畴 every arrow invertible (Structure/Groupoid.v's
 [IsGroupoid]) well-powered one-point index: every subobject
 top one. （已译） *)
Section Groupoid.

Context {C : Category}.
Context (G : IsGroupoid C).

Definition wp_groupoid (x : C) : WellPoweredAt x.
Proof using G.
  unshelve refine {| wp_index := Datatypes.unit;
                     wp_to    := fun _ => sub_top;
                     wp_from  := fun _ => tt |}.
  intro u.
  unshelve eexists.
  - exact (iso_sym (IsIsoToIso (Subobject.sub_mono u)
                                (G _ _ (Subobject.sub_mono u)))).
  - simpl; exact is_right_inverse.
Defined.

End Groupoid.

(* The pinned forms. The one-point index sits at [Set], below every hom
 universe, so no bound relates 对象 homs. （已译） *)
Definition Groupoid_WellPowered@{o h w s t | w <= h, o <= s, h <= s, h < t +}
  (C : Category@{o h h}) (G : IsGroupoid C) :
  WellPowered@{o h w s t} C :=
  fun x => wp_groupoid G x.

(* 相关说明。 （已译） *)
Definition Groupoid_CoWellPowered@{o h w s t | w <= h, o <= s, h <= s, h < t +}
  (C : Category@{o h h}) (G : IsGroupoid C) :
  CoWellPowered@{o h w s t} C :=
  Groupoid_WellPowered@{o h w s t} (C^op) (IsGroupoid_op G).

(* Discrete categories: every arrow is an equality proof, inverted by
   [eq_sym]. *)
Definition DiscreteCat_isos@{o h} (A : Type@{o})
  (a b : DiscreteCat@{o h h} A) (f : a ~> b) : IsIsomorphism f.
Proof.
  exists (eq_sym f); destruct f; reflexivity.
Defined.

Definition DiscreteCat_WellPowered@{o h w s t |
    w <= h, o <= s, h <= s, h < t +}
  (A : Type@{o}) : WellPowered@{o h w s t} (DiscreteCat@{o h h} A) :=
  Groupoid_WellPowered@{o h w s t} (DiscreteCat@{o h h} A) (DiscreteCat_isos A).

Definition DiscreteCat_CoWellPowered@{o h w s t |
    w <= h, o <= s, h <= s, h < t +}
  (A : Type@{o}) : CoWellPowered@{o h w s t} (DiscreteCat@{o h h} A) :=
  Groupoid_CoWellPowered@{o h w s t} (DiscreteCat@{o h h} A)
    (DiscreteCat_isos A).

(* The 对象 types [Type@{j}], one universe above homs,
 sit at [j]; index at [Set]. （已译） *)
Definition DiscreteCat_types_WellPowered@{j o t | j < o, j < t +} :
  WellPowered@{o j Set o t} (DiscreteCat@{o j j} Type@{j}) :=
  DiscreteCat_WellPowered@{o j Set o t} Type@{j}.

(* Indiscrete categories: every arrow is [tt], inverted by [tt]. *)
Definition Indiscrete_isos@{o h} (A : Type@{o})
  (a b : Indiscrete@{o h h} A) (f : a ~> b) : IsIsomorphism f.
Proof.
  exists (tt : @hom (Indiscrete@{o h h} A) b a); destruct f; reflexivity.
Defined.

Definition Indiscrete_WellPowered@{o h w s t |
    w <= h, o <= s, h <= s, h < t +}
  (A : Type@{o}) : WellPowered@{o h w s t} (Indiscrete@{o h h} A) :=
  Groupoid_WellPowered@{o h w s t} (Indiscrete@{o h h} A) (Indiscrete_isos A).

Definition Indiscrete_CoWellPowered@{o h w s t |
    w <= h, o <= s, h <= s, h < t +}
  (A : Type@{o}) : CoWellPowered@{o h w s t} (Indiscrete@{o h h} A) :=
  Groupoid_CoWellPowered@{o h w s t} (Indiscrete@{o h h} A)
    (Indiscrete_isos A).

(*
   本节说明拉回/推出、hom、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition wp_of_classifier {C : Category} `{T : @Terminal C}
  `{PB : @HasPullbacks C} `{S : @SubobjectClassifier C T} (x : C) :
  WellPoweredAt x :=
  {| wp_index   := x ~> Ω;
     wp_to      := fun f => sub_reindex f truth_subobject;
     wp_from    := fun u => char (Subobject.sub_mono u) (sub_is_monic u);
     wp_to_from := fun u => classifier_pullback_roundtrip u |}.

Definition Classifier_WellPowered@{o h s t | o <= s, h <= s, h < t +}
  (C : Category@{o h h}) `{T : @Terminal C} `{PB : @HasPullbacks C}
  `{S : @SubobjectClassifier C T} : WellPowered@{o h h s t} C :=
  fun x => wp_of_classifier x.

(* 相关说明。 （已译） *)

(* An inhabited indiscrete 范畴 complete: limit every diagram
 any 对象, possible legs. （已译） *)
Definition Indiscrete_Complete@{r so h o +| so <= r, h <= r +}
  {A : Type@{o}} (a : A) : @Complete@{r so h o} (Indiscrete@{o h h} A).
Proof.
  intros D F.
  unshelve refine {| limit_cone :=
    @Build_Cone D (Indiscrete A) F a
      (@Build_ACone D (Indiscrete A) a F (fun _ => tt) _) |}.
  - intros; reflexivity.
  - intro N.
    unshelve eapply Build_Unique.
    + exact tt.
    + intro y.
      destruct (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) y); reflexivity.
    + intros v _; destruct v; reflexivity.
Defined.

(* Both hypotheses [wellpowered_complete_has_intersections] at once, at a
 范畴 whose 对象, types [Type@{j}], sit one universe above
 its homs; trivial witness is out reach there.（已译） *)
Definition Indiscrete_types_has_intersections@{j o t q +|
    j < o, j < t, o <= q +}
  (x : Indiscrete@{o j j} Type@{j}) (P : SubObj x → Type@{j})
  (HP : ∀ m m' : SubObj x, m ≈ m' → P m → P m') :
  { w : SubObj x &
    IsIntersection@{o j q} (fun k : { m : SubObj x & P m } => `1 k) w } :=
  wellpowered_complete_has_intersections
    (Indiscrete_WellPowered@{o j Set o t} Type@{j})
    (Indiscrete_Complete@{j j j o} (Datatypes.unit : Type@{j})) x P HP.
