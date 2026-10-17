Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Classes.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Orthogonality.
Require Import Category.Theory.Subobject.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.BiCCC.
Require Import Category.Structure.Factorization.
Require Import Category.Structure.Regular.
Require Import Category.Structure.Regular.Factorization.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.Limit.Coproduct.

Generalizable All Variables.

(*
 nLab:  https://ncatlab.org/nlab/show/subobject
 nLab:  https://ncatlab.org/nlab/show/image
 nLab:  https://ncatlab.org/nlab/show/wide+pullback
 nLab:  https://ncatlab.org/nlab/show/well-powered+category

   本文件给出子对象格相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The order-theoretic vocabulary *)

Section SubobjectOrder.

Context {C : Category}.
Context {x : C}.

(* The top subobject: x itself along the identity. *)
Definition sub_top : SubObj x := {|
  sub_dom := x;
  sub_mono := id;
  sub_is_monic := id_monic x
|}.

Lemma sub_top_greatest (u : SubObj x) : sub_le u sub_top.
Proof. exists (sub_mono u); cat. Defined.

(*
   本节说明 Lattice 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record IsIntersection {J : Type} (S : J → SubObj x) (w : SubObj x) := {
  inter_le : ∀ j, sub_le w (S j);
  inter_greatest : ∀ v : SubObj x, (∀ j, sub_le v (S j)) → sub_le v w
}.

Record IsUnion {J : Type} (S : J → SubObj x) (w : SubObj x) := {
  union_ge : ∀ j, sub_le (S j) w;
  union_least : ∀ v : SubObj x, (∀ j, sub_le (S j) v) → sub_le w v
}.

(* A two-element family, for the binary cases. *)
Definition sub_pair (u v : SubObj x) : bool → SubObj x :=
  fun b => if b then u else v.

Definition IsMeet (u v w : SubObj x) : Type := IsIntersection (sub_pair u v) w.
Definition IsJoin (u v w : SubObj x) : Type := IsUnion (sub_pair u v) w.

(** *** Antisymmetry for the induced setoid *)

(* The half of [sub_equiv_iff_mutual] used everywhere below: mutual
   factorization IS equivalence of subobjects.  [SubObj x] has no Leibniz
   antisymmetry; this is its replacement. *)
Lemma sub_le_antisym (u v : SubObj x) : sub_le u v → sub_le v u → u ≈ v.
Proof.
  intros Huv Hvu.
  apply sub_equiv_iff_mutual.
  exact (Huv, Hvu).
Defined.

(* ... and the two projections of the other direction, as named lemmas, so
   that a transport along ≈ reads as one step. *)
Lemma sub_le_of_equiv (u v : SubObj x) : u ≈ v → sub_le u v.
Proof. intros H; exact (fst (fst (sub_equiv_iff_mutual u v) H)). Defined.

Lemma sub_ge_of_equiv (u v : SubObj x) : u ≈ v → sub_le v u.
Proof. intros H; exact (snd (fst (sub_equiv_iff_mutual u v) H)). Defined.

(** *** Uniqueness and transport of the two universal properties *)

(* Two greatest lower bounds of the same family agree: each is below every
   member, so each factors through the other by the other's maximality. *)
Lemma IsIntersection_unique {J : Type} (S : J → SubObj x) (w w' : SubObj x) :
  IsIntersection S w → IsIntersection S w' → w ≈ w'.
Proof.
  intros A B.
  apply sub_le_antisym.
  - exact (inter_greatest S w' B w (inter_le S w A)).
  - exact (inter_greatest S w A w' (inter_le S w' B)).
Defined.

Lemma IsUnion_unique {J : Type} (S : J → SubObj x) (w w' : SubObj x) :
  IsUnion S w → IsUnion S w' → w ≈ w'.
Proof.
  intros A B.
  apply sub_le_antisym.
  - exact (union_least S w A w' (union_ge S w' B)).
  - exact (union_least S w' B w (union_ge S w A)).
Defined.

(* Being the intersection transports along ≈ of the bound ... *)
Lemma IsIntersection_respects_w {J : Type} (S : J → SubObj x)
  (w w' : SubObj x) : w ≈ w' → IsIntersection S w → IsIntersection S w'.
Proof.
  intros Hw A.
  constructor.
  - intro j.
    exact (sub_le_trans _ _ _ (sub_ge_of_equiv _ _ Hw) (inter_le S w A j)).
  - intros v Hv.
    exact (sub_le_trans _ _ _ (inter_greatest S w A v Hv)
             (sub_le_of_equiv _ _ Hw)).
Defined.

(* ... and pointwise along ≈ of the family. *)
Lemma IsIntersection_respects_family {J : Type} (S S' : J → SubObj x)
  (w : SubObj x) : (∀ j, S j ≈ S' j) →
  IsIntersection S w → IsIntersection S' w.
Proof.
  intros HS A.
  constructor.
  - intro j.
    exact (sub_le_trans _ _ _ (inter_le S w A j) (sub_le_of_equiv _ _ (HS j))).
  - intros v Hv.
    apply (inter_greatest S w A).
    intro j.
    exact (sub_le_trans _ _ _ (Hv j) (sub_ge_of_equiv _ _ (HS j))).
Defined.

Lemma IsUnion_respects_w {J : Type} (S : J → SubObj x) (w w' : SubObj x) :
  w ≈ w' → IsUnion S w → IsUnion S w'.
Proof.
  intros Hw A.
  constructor.
  - intro j.
    exact (sub_le_trans _ _ _ (union_ge S w A j) (sub_le_of_equiv _ _ Hw)).
  - intros v Hv.
    exact (sub_le_trans _ _ _ (sub_ge_of_equiv _ _ Hw)
             (union_least S w A v Hv)).
Defined.

Lemma IsUnion_respects_family {J : Type} (S S' : J → SubObj x) (w : SubObj x) :
  (∀ j, S j ≈ S' j) → IsUnion S w → IsUnion S' w.
Proof.
  intros HS A.
  constructor.
  - intro j.
    exact (sub_le_trans _ _ _ (sub_ge_of_equiv _ _ (HS j)) (union_ge S w A j)).
  - intros v Hv.
    apply (union_least S w A).
    intro j.
    exact (sub_le_trans _ _ _ (sub_le_of_equiv _ _ (HS j)) (Hv j)).
Defined.

(** *** The two degenerate index shapes *)

(*
   本节说明拉回/推出、子对象、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma IsIntersection_empty {J : Type} (S : J → SubObj x) (Hempty : J → False) :
  IsIntersection S sub_top.
Proof.
  constructor.
  - intro j; destruct (Hempty j).
  - intros v _; exact (sub_top_greatest v).
Defined.

(* Dually the union of the empty family is the LEAST subobject, which has
   to be supplied: nothing in the bare preorder produces one.  The Bottom
   section below instantiates [b] at [sub_bot]. *)
Lemma IsUnion_empty_of_least {J : Type} (S : J → SubObj x) (b : SubObj x)
  (Hleast : ∀ u : SubObj x, sub_le b u) (Hempty : J → False) :
  IsUnion S b.
Proof.
  constructor.
  - intro j; destruct (Hempty j).
  - intros v _; exact (Hleast v).
Defined.

(* A one-member family is its own bound, on both sides. *)
Lemma IsIntersection_singleton (S : unit → SubObj x) :
  IsIntersection S (S tt).
Proof.
  constructor.
  - intro j; destruct j; exact (sub_le_refl _).
  - intros v Hv; exact (Hv tt).
Defined.

Lemma IsUnion_singleton (S : unit → SubObj x) : IsUnion S (S tt).
Proof.
  constructor.
  - intro j; destruct j; exact (sub_le_refl _).
  - intros v Hv; exact (Hv tt).
Defined.

End SubobjectOrder.

Arguments IsIntersection_unique {C x J} S {w w'} _ _.
Arguments IsUnion_unique {C x J} S {w w'} _ _.

(** ** Pushing a subobject forward along a mono *)

Section Compose.

Context {C : Category}.

(* A subobject of the domain of a subobject is a subobject of the ambient
   object: monos compose. *)
Definition sub_compose {x : C} (u : SubObj x) (w : SubObj (sub_dom u)) :
  SubObj x := {|
  sub_dom := sub_dom w;
  sub_mono := sub_mono u ∘ sub_mono w;
  sub_is_monic := monic_compose (sub_is_monic u) (sub_is_monic w)
|}.

End Compose.

(** ** Binary meets by pullback *)

Section Meet.

Context {C : Category}.
Context `{@HasPullbacks C}.
Context {x : C}.

(*
   本节说明拉回/推出、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sub_meet (u v : SubObj x) : SubObj x := {|
  sub_dom := Pull (sub_mono u) (sub_mono v)
               (pullback (sub_mono u) (sub_mono v));
  sub_mono := sub_mono u
              ∘ pullback_fst (sub_mono u) (sub_mono v)
                  (pullback (sub_mono u) (sub_mono v));
  sub_is_monic :=
    monic_compose (sub_is_monic u)
      (monic_pullback_stable (sub_mono u) (sub_mono v) (sub_is_monic v)
         (pullback (sub_mono u) (sub_mono v)))
|}.

(* Below the first factor, by the first projection: the mediating arrow IS
   [pullback_fst] and the triangle is the definition of [sub_meet]. *)
Lemma sub_meet_le_l (u v : SubObj x) : sub_le (sub_meet u v) u.
Proof.
  exists (pullback_fst (sub_mono u) (sub_mono v)
            (pullback (sub_mono u) (sub_mono v))).
  reflexivity.
Defined.

(* Below the second factor, by the second projection: here the triangle is
   the commuting square of the pullback, read backwards. *)
Lemma sub_meet_le_r (u v : SubObj x) : sub_le (sub_meet u v) v.
Proof.
  exists (pullback_snd (sub_mono u) (sub_mono v)
            (pullback (sub_mono u) (sub_mono v))).
  symmetry.
  exact (pullback_commutes (sub_mono u) (sub_mono v)
           (pullback (sub_mono u) (sub_mono v))).
Defined.

(*
   本节说明拉回/推出、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma sub_meet_is_glb (u v : SubObj x) :
  ∀ w : SubObj x, sub_le w u → sub_le w v → sub_le w (sub_meet u v).
Proof.
  intros w [k Hk] [l Hl].
  assert (Hsq : sub_mono u ∘ k ≈ sub_mono v ∘ l) by now rewrite Hk, Hl.
  pose proof (ump_pullbacks (sub_mono u) (sub_mono v)
                (pullback (sub_mono u) (sub_mono v)) (sub_dom w) k l Hsq)
    as U.
  exists (unique_obj U).
  simpl.
  rewrite <- comp_assoc.
  rewrite (fst (unique_property U)).
  exact Hk.
Defined.

(* Packaged as the order-theoretic predicate at the two-element family. *)
Lemma sub_meet_IsMeet (u v : SubObj x) : IsMeet u v (sub_meet u v).
Proof.
  constructor.
  - intro b; destruct b; simpl.
    + exact (sub_meet_le_l u v).
    + exact (sub_meet_le_r u v).
  - intros w Hw.
    exact (sub_meet_is_glb u v w (Hw true) (Hw false)).
Defined.

(*
   本节说明拉回/推出、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance sub_meet_respects :
  Proper (equiv ==> equiv ==> equiv) sub_meet.
Proof.
  intros u u' Hu v v' Hv.
  apply (IsIntersection_unique (sub_pair u' v')).
  - apply (IsIntersection_respects_family (sub_pair u v)).
    + intro b; destruct b; assumption.
    + exact (sub_meet_IsMeet u v).
  - exact (sub_meet_IsMeet u' v').
Defined.

(** *** The order laws, at ≈ *)

Lemma sub_meet_comm (u v : SubObj x) : sub_meet u v ≈ sub_meet v u.
Proof.
  apply sub_le_antisym.
  - apply sub_meet_is_glb; [ exact (sub_meet_le_r u v)
                           | exact (sub_meet_le_l u v) ].
  - apply sub_meet_is_glb; [ exact (sub_meet_le_r v u)
                           | exact (sub_meet_le_l v u) ].
Defined.

Lemma sub_meet_assoc (u v w : SubObj x) :
  sub_meet (sub_meet u v) w ≈ sub_meet u (sub_meet v w).
Proof.
  apply sub_le_antisym.
  - apply sub_meet_is_glb.
    + exact (sub_le_trans _ _ _ (sub_meet_le_l _ _) (sub_meet_le_l _ _)).
    + apply sub_meet_is_glb.
      * exact (sub_le_trans _ _ _ (sub_meet_le_l _ _) (sub_meet_le_r _ _)).
      * exact (sub_meet_le_r _ _).
  - apply sub_meet_is_glb.
    + apply sub_meet_is_glb.
      * exact (sub_meet_le_l _ _).
      * exact (sub_le_trans _ _ _ (sub_meet_le_r _ _) (sub_meet_le_l _ _)).
    + exact (sub_le_trans _ _ _ (sub_meet_le_r _ _) (sub_meet_le_r _ _)).
Defined.

Lemma sub_meet_idem (u : SubObj x) : sub_meet u u ≈ u.
Proof.
  apply sub_le_antisym.
  - exact (sub_meet_le_l u u).
  - exact (sub_meet_is_glb u u u (sub_le_refl u) (sub_le_refl u)).
Defined.

(* The top subobject is a unit for the meet. *)
Lemma sub_meet_top (u : SubObj x) : sub_meet u sub_top ≈ u.
Proof.
  apply sub_le_antisym.
  - exact (sub_meet_le_l u sub_top).
  - exact (sub_meet_is_glb u sub_top u (sub_le_refl u) (sub_top_greatest u)).
Defined.

(* "u ≤ v iff u ∧ v ≈ u", in two separate lemmas: [sub_le] is Type-valued
   data and the two directions carry different data, so they are not
   packaged as one ↔. *)
Lemma sub_meet_of_le (u v : SubObj x) : sub_le u v → sub_meet u v ≈ u.
Proof.
  intros Huv.
  apply sub_le_antisym.
  - exact (sub_meet_le_l u v).
  - exact (sub_meet_is_glb u v u (sub_le_refl u) Huv).
Defined.

Lemma sub_le_of_meet (u v : SubObj x) : sub_meet u v ≈ u → sub_le u v.
Proof.
  intros Hm.
  exact (sub_le_trans _ _ _ (sub_ge_of_equiv _ _ Hm) (sub_meet_le_r u v)).
Defined.

End Meet.

(** ** Wide intersections by wide pullback *)

Section WideIntersection.

Context {C : Category}.
Context {x : C}.
Context {J : Type}.
Context (S : J → SubObj x).

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma wide_pullback_proj_monic (W : WidePullback (fun j => sub_mono (S j)))
  (j : J) : Monic (wide_pullback_proj W j).
Proof.
  constructor; intros q g1 g2 Hg.
  apply (wide_pullback_jointly_monic (wide_pullback_is_pullback W)).
  intro i.
  apply (monic (Monic := sub_is_monic (S i))).
  rewrite !comp_assoc.
  rewrite (wide_pullback_commutes W i j).
  rewrite <- !comp_assoc.
  now rewrite Hg.
Qed.

(*
   本节说明拉回/推出、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sub_wide_intersection (j0 : J)
  (W : WidePullback (fun j => sub_mono (S j))) : SubObj x := {|
  sub_dom := WPull W;
  sub_mono := sub_mono (S j0) ∘ wide_pullback_proj W j0;
  sub_is_monic :=
    monic_compose (sub_is_monic (S j0)) (wide_pullback_proj_monic W j0)
|}.

(*
   本节说明拉回/推出、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem sub_wide_intersection_IsIntersection (j0 : J)
  (W : WidePullback (fun j => sub_mono (S j))) :
  IsIntersection S (sub_wide_intersection j0 W).
Proof.
  constructor.
  - (* below every member, by that member's projection *)
    intro j.
    exists (wide_pullback_proj W j).
    exact (wide_pullback_commutes W j j0).
  - (* maximal among the subobjects below every member *)
    intros v Hv.
    pose (q := fun j => `1 (Hv j)).
    assert (Hq : ∀ i j : J, sub_mono (S i) ∘ q i ≈ sub_mono (S j) ∘ q j).
    { intros i j; unfold q.
      rewrite (`2 (Hv i)), (`2 (Hv j)); reflexivity. }
    pose proof (ump_wide_pullbacks W (sub_dom v) q Hq) as U.
    exists (unique_obj U).
    simpl.
    rewrite <- comp_assoc.
    rewrite (unique_property U j0).
    exact (`2 (Hv j0)).
Defined.

(*
   本节说明等价、同构、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma sub_wide_intersection_index_irrelevant (j0 j1 : J)
  (W : WidePullback (fun j => sub_mono (S j))) :
  sub_wide_intersection j0 W ≈ sub_wide_intersection j1 W.
Proof.
  exists iso_id; simpl.
  rewrite id_right.
  exact (wide_pullback_commutes W j1 j0).
Defined.

End WideIntersection.

(** ** The binary meet as a wide intersection *)

Section MeetIsWide.

Context {C : Category}.
Context `{@HasPullbacks C}.
Context {x : C}.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem sub_meet_is_wide_intersection (u v : SubObj x)
  (W : WidePullback (fun b => sub_mono (sub_pair u v b))) :
  sub_meet u v ≈ sub_wide_intersection (sub_pair u v) true W.
Proof.
  apply (IsIntersection_unique (sub_pair u v)).
  - exact (sub_meet_IsMeet u v).
  - exact (sub_wide_intersection_IsIntersection (sub_pair u v) true W).
Defined.

End MeetIsWide.

(** ** The total form: all wide intersections at once *)

Section TotalIntersection.

Context {C : Category}.
Context `{@HasWidePullbacks C}.
Context {x : C}.

(* With every wide pullback chosen, the intersection of a family is a
   total operation -- still presented at an index, for the reason recorded
   in the header. *)
Definition sub_intersection {J : Type} (j0 : J) (S : J → SubObj x) :
  SubObj x :=
  sub_wide_intersection S j0 (wide_pullback (fun j => sub_mono (S j))).

Theorem sub_intersection_IsIntersection {J : Type} (j0 : J)
  (S : J → SubObj x) : IsIntersection S (sub_intersection j0 S).
Proof.
  exact (sub_wide_intersection_IsIntersection S j0
           (wide_pullback (fun j => sub_mono (S j)))).
Defined.

End TotalIntersection.

(** ** Images as subobjects, and joins by image of the copairing *)

Section Images.

Context {C : Category}.

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record ImageOf {y x : C} (f : y ~> x) := {
  im_sub : SubObj x;
  im_factor : y ~> sub_dom im_sub;
  im_commutes : sub_mono im_sub ∘ im_factor ≈ f;
  im_least : ∀ (w : SubObj x) (g : y ~> sub_dom w),
    sub_mono w ∘ g ≈ f → sub_le im_sub w
}.

Class HasImages := {
  image_of : ∀ {y x : C} (f : y ~> x), ImageOf f
}.

End Images.

Arguments im_sub {C y x f} _.
Arguments im_factor {C y x f} _.
Arguments im_commutes {C y x f} _.
Arguments im_least {C y x f} _ _ _ _.
Arguments HasImages C : clear implicits.
Arguments image_of {C _ y x} f.

Section Join.

Context {C : Category}.
Context `{@Cocartesian C}.
Context {x : C}.

(* The union of two subobjects: the image of the copairing of their monos
   out of the coproduct of their domains, given such an image. *)
Definition sub_join_via (u v : SubObj x)
  (I : ImageOf (merge (sub_mono u) (sub_mono v))) : SubObj x := im_sub I.

Definition sub_join `{@HasImages C} (u v : SubObj x) : SubObj x :=
  sub_join_via u v (image_of (merge (sub_mono u) (sub_mono v))).

(* Above the first factor: the mediating arrow is the image factorization
   precomposed with [inl], and the triangle is [inl_merge]
   (Structure/Cocartesian.v). *)
Lemma sub_join_via_le_l (u v : SubObj x)
  (I : ImageOf (merge (sub_mono u) (sub_mono v))) :
  sub_le u (sub_join_via u v I).
Proof.
  exists (im_factor I ∘ inl).
  unfold sub_join_via.
  rewrite comp_assoc.
  rewrite (im_commutes I).
  exact (inl_merge (sub_mono u) (sub_mono v)).
Defined.

(* ... and above the second, by [inr_merge] (Structure/Cocartesian.v). *)
Lemma sub_join_via_le_r (u v : SubObj x)
  (I : ImageOf (merge (sub_mono u) (sub_mono v))) :
  sub_le v (sub_join_via u v I).
Proof.
  exists (im_factor I ∘ inr).
  unfold sub_join_via.
  rewrite comp_assoc.
  rewrite (im_commutes I).
  exact (inr_merge (sub_mono u) (sub_mono v)).
Defined.

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma sub_join_via_is_lub (u v : SubObj x)
  (I : ImageOf (merge (sub_mono u) (sub_mono v))) (w : SubObj x) :
  sub_le u w → sub_le v w → sub_le (sub_join_via u v I) w.
Proof.
  intros [k Hk] [l Hl].
  apply (im_least I w (merge k l)).
  rewrite <- merge_comp.
  rewrite Hk, Hl.
  reflexivity.
Defined.

Lemma sub_join_via_IsJoin (u v : SubObj x)
  (I : ImageOf (merge (sub_mono u) (sub_mono v))) :
  IsJoin u v (sub_join_via u v I).
Proof.
  constructor.
  - intro b; destruct b; simpl.
    + exact (sub_join_via_le_l u v I).
    + exact (sub_join_via_le_r u v I).
  - intros w Hw.
    exact (sub_join_via_is_lub u v I w (Hw true) (Hw false)).
Defined.

End Join.

(** ** The join as a lattice operation, with images chosen *)

Section JoinLattice.

Context {C : Category}.
Context `{CC : @Cocartesian C}.
Context `{HI : @HasImages C}.
Context {x : C}.

Lemma sub_join_le_l (u v : SubObj x) : sub_le u (sub_join u v).
Proof. exact (sub_join_via_le_l u v _). Defined.

Lemma sub_join_le_r (u v : SubObj x) : sub_le v (sub_join u v).
Proof. exact (sub_join_via_le_r u v _). Defined.

Lemma sub_join_is_lub (u v : SubObj x) :
  ∀ w : SubObj x, sub_le u w → sub_le v w → sub_le (sub_join u v) w.
Proof. intros w Hu Hv; exact (sub_join_via_is_lub u v _ w Hu Hv). Defined.

Lemma sub_join_IsJoin (u v : SubObj x) : IsJoin u v (sub_join u v).
Proof. exact (sub_join_via_IsJoin u v _). Defined.

(* As with the meet: least upper bounds of pointwise-equivalent families
   agree, so the chosen image never has to be compared with itself. *)
#[export] Instance sub_join_respects :
  Proper (equiv ==> equiv ==> equiv) (@sub_join C CC x HI).
Proof.
  intros u u' Hu v v' Hv.
  apply (IsUnion_unique (sub_pair u' v')).
  - apply (IsUnion_respects_family (sub_pair u v)).
    + intro b; destruct b; assumption.
    + exact (sub_join_IsJoin u v).
  - exact (sub_join_IsJoin u' v').
Defined.

Lemma sub_join_comm (u v : SubObj x) : sub_join u v ≈ sub_join v u.
Proof.
  apply sub_le_antisym.
  - apply sub_join_is_lub; [ exact (sub_join_le_r v u)
                           | exact (sub_join_le_l v u) ].
  - apply sub_join_is_lub; [ exact (sub_join_le_r u v)
                           | exact (sub_join_le_l u v) ].
Defined.

Lemma sub_join_assoc (u v w : SubObj x) :
  sub_join (sub_join u v) w ≈ sub_join u (sub_join v w).
Proof.
  apply sub_le_antisym.
  - apply sub_join_is_lub.
    + apply sub_join_is_lub.
      * exact (sub_join_le_l _ _).
      * exact (sub_le_trans _ _ _ (sub_join_le_l _ _) (sub_join_le_r _ _)).
    + exact (sub_le_trans _ _ _ (sub_join_le_r _ _) (sub_join_le_r _ _)).
  - apply sub_join_is_lub.
    + exact (sub_le_trans _ _ _ (sub_join_le_l _ _) (sub_join_le_l _ _)).
    + apply sub_join_is_lub.
      * exact (sub_le_trans _ _ _ (sub_join_le_r _ _) (sub_join_le_l _ _)).
      * exact (sub_join_le_r _ _).
Defined.

Lemma sub_join_idem (u : SubObj x) : sub_join u u ≈ u.
Proof.
  apply sub_le_antisym.
  - exact (sub_join_is_lub u u u (sub_le_refl u) (sub_le_refl u)).
  - exact (sub_join_le_l u u).
Defined.

(* "u ≤ v iff u ∨ v ≈ v", again in two separate lemmas. *)
Lemma sub_join_of_le (u v : SubObj x) : sub_le u v → sub_join u v ≈ v.
Proof.
  intros Huv.
  apply sub_le_antisym.
  - exact (sub_join_is_lub u v v Huv (sub_le_refl v)).
  - exact (sub_join_le_r u v).
Defined.

Lemma sub_le_of_join (u v : SubObj x) : sub_join u v ≈ v → sub_le u v.
Proof.
  intros Hj.
  exact (sub_le_trans _ _ _ (sub_join_le_l u v) (sub_le_of_equiv _ _ Hj)).
Defined.

End JoinLattice.

(** ** Absorption: the two operations make a lattice on the setoid *)

Section Absorption.

Context {C : Category}.
Context `{@HasPullbacks C}.
Context `{CC : @Cocartesian C}.
Context `{HI : @HasImages C}.
Context {x : C}.

(* u ∧ (u ∨ v) ≈ u.  One direction is the meet's first projection, the
   other is the greatest-lower-bound property applied to u ≤ u and
   u ≤ u ∨ v. *)
Theorem sub_meet_absorb (u v : SubObj x) : sub_meet u (sub_join u v) ≈ u.
Proof.
  apply sub_le_antisym.
  - exact (sub_meet_le_l u (sub_join u v)).
  - exact (sub_meet_is_glb u (sub_join u v) u (sub_le_refl u)
             (sub_join_le_l u v)).
Defined.

(* u ∨ (u ∧ v) ≈ u, dually. *)
Theorem sub_join_absorb (u v : SubObj x) : sub_join u (sub_meet u v) ≈ u.
Proof.
  apply sub_le_antisym.
  - exact (sub_join_is_lub u (sub_meet u v) u (sub_le_refl u)
             (sub_meet_le_l u v)).
  - exact (sub_join_le_l u (sub_meet u v)).
Defined.

End Absorption.

(** ** Indexed joins *)

Section WideJoin.

Context {C : Category}.
Context {x : C}.
Context {J : Type}.
Context (S : J → SubObj x).

(* The union of a family: the image of the induced map out of an indexed
   coproduct of the domains, given such an image. *)
Definition sub_wide_join_via {p : C} {inj : ∀ j, sub_dom (S j) ~> p}
  (P : IsIndexedCoproduct (fun j => sub_dom (S j)) p inj)
  (I : ImageOf (unique_obj (icoprod_desc P (fun j => sub_mono (S j))))) :
  SubObj x := im_sub I.

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem sub_wide_join_via_IsUnion {p : C} {inj : ∀ j, sub_dom (S j) ~> p}
  (P : IsIndexedCoproduct (fun j => sub_dom (S j)) p inj)
  (I : ImageOf (unique_obj (icoprod_desc P (fun j => sub_mono (S j))))) :
  IsUnion S (sub_wide_join_via P I).
Proof.
  pose (D := icoprod_desc P (fun j => sub_mono (S j))).
  constructor.
  - (* the j-th member sits below the image *)
    intro j.
    exists (im_factor I ∘ inj j).
    unfold sub_wide_join_via.
    rewrite comp_assoc.
    rewrite (im_commutes I).
    exact (unique_property D j).
  - (* and the image is below every common upper bound *)
    intros v Hv.
    pose proof (icoprod_desc P (fun j => `1 (Hv j))) as E.
    apply (im_least I v (unique_obj E)).
    symmetry.
    apply (uniqueness D).
    intro j.
    rewrite <- comp_assoc.
    rewrite (unique_property E j).
    exact (`2 (Hv j)).
Defined.

End WideJoin.

(** ** The bottom subobject *)

Section Bottom.

Context {C : Category}.
Context `{I : @Initial C}.
Context {x : C}.

(* The least subobject, when the arrow out of the initial object is monic
   (it is whenever the initial object is strict). *)
Definition sub_bot (Hz : Monic (@zero C I x)) : SubObj x := {|
  sub_dom := 0;
  sub_mono := zero;
  sub_is_monic := Hz
|}.

Lemma sub_bot_least (Hz : Monic (@zero C I x)) (u : SubObj x) :
  sub_le (sub_bot Hz) u.
Proof. exists zero; apply zero_unique. Defined.

(*
   本节说明幺半群、同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma zero_monic_of_strict
  (Hstrict : ∀ (y : C) (f : y ~> 0), y ≅ 0) : Monic (@zero C I x).
Proof.
  constructor; intros w g1 g2 _.
  pose proof (Hstrict w g1) as i.
  assert (Hto : ∀ g : w ~> 0, g ≈ to i).
  { intro g.
    transitivity (g ∘ (from i ∘ to i)).
    - rewrite (iso_from_to i); cat.
    - rewrite comp_assoc.
      rewrite (@zero_unique C I 0 (g ∘ from i) id).
      cat. }
  now rewrite (Hto g1), (Hto g2).
Qed.

(* The empty union, at the least subobject. *)
Lemma IsUnion_empty_bot (Hz : Monic (@zero C I x)) {J : Type}
  (S : J → SubObj x) (Hempty : J → False) : IsUnion S (sub_bot Hz).
Proof.
  exact (IsUnion_empty_of_least S (sub_bot Hz) (sub_bot_least Hz) Hempty).
Defined.

End Bottom.

(** ** The bottom in a bicartesian closed category *)

Section BiCCCBottom.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Closed C _}.
Context `{I : @Initial C}.
Context {x : C}.

(*
   本节说明子对象、笛卡尔、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition biccc_zero_monic : Monic (@zero C I x) :=
  zero_monic_of_strict (fun y f => initial_strict f).

(* ... and the bottom subobject it names. *)
Definition biccc_sub_bot : SubObj x := sub_bot biccc_zero_monic.

End BiCCCBottom.

(** ** The bottom against the two operations *)

Section BottomMeet.

Context {C : Category}.
Context `{@HasPullbacks C}.
Context `{I : @Initial C}.
Context {x : C}.

(* ∅ ∩ X ≈ ∅. *)
Theorem sub_meet_bot (Hz : Monic (@zero C I x)) (u : SubObj x) :
  sub_meet (sub_bot Hz) u ≈ sub_bot Hz.
Proof.
  apply sub_le_antisym.
  - exact (sub_meet_le_l (sub_bot Hz) u).
  - exact (sub_bot_least Hz (sub_meet (sub_bot Hz) u)).
Defined.

End BottomMeet.

Section BottomJoin.

Context {C : Category}.
Context `{CC : @Cocartesian C}.
Context `{HI : @HasImages C}.
Context `{I : @Initial C}.
Context {x : C}.

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma sub_join_via_bot (Hz : Monic (@zero C I x)) (u : SubObj x)
  (Img : ImageOf (merge (sub_mono (sub_bot Hz)) (sub_mono u))) :
  sub_join_via (sub_bot Hz) u Img ≈ u.
Proof.
  apply sub_le_antisym.
  - exact (sub_join_via_is_lub (sub_bot Hz) u Img u (sub_bot_least Hz u)
             (sub_le_refl u)).
  - exact (sub_join_via_le_r (sub_bot Hz) u Img).
Defined.

Theorem sub_join_bot (Hz : Monic (@zero C I x)) (u : SubObj x) :
  sub_join (sub_bot Hz) u ≈ u.
Proof.
  exact (sub_join_via_bot Hz u
           (image_of (merge (sub_mono (sub_bot Hz)) (sub_mono u)))).
Defined.

End BottomJoin.

(** ** Images from an orthogonal factorization system *)

Section OFSImages.

Context {C : Category}.
Context {E : MorphismClass C}.

(* The mono leg of an (E, Mono) factorization, read as a subobject.  No
   transport is needed: Theory/Morphisms/Classes.v defines [MonoClass]
   as [fun _ _ f => Monic f], so [fact_m_in] IS the [sub_is_monic]
   field. *)
Definition ofs_image_sub (O : OFS E (@MonoClass C)) {y x : C} (f : y ~> x) :
  SubObj x := {|
  sub_dom := fact_mid (ofs_factor (OFS := O) f);
  sub_mono := fact_m (ofs_factor (OFS := O) f);
  sub_is_monic := fact_m_in (ofs_factor (OFS := O) f)
|}.

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ofs_image_least (O : OFS E (@MonoClass C)) {y x : C} (f : y ~> x)
  (w : SubObj x) (g : y ~> sub_dom w) (Hg : sub_mono w ∘ g ≈ f) :
  sub_le (ofs_image_sub O f) w.
Proof.
  pose proof (ofs_orth (OFS := O) (fact_e (ofs_factor (OFS := O) f))
                (sub_mono w) (fact_e_in (ofs_factor (OFS := O) f))
                (sub_is_monic w)) as Ho.
  assert (Hc : sub_mono w ∘ g
               ≈ fact_m (ofs_factor (OFS := O) f)
                   ∘ fact_e (ofs_factor (OFS := O) f)).
  { rewrite (fact_comm (ofs_factor (OFS := O) f)); exact Hg. }
  pose proof (ortho_lift (Orthogonal := Ho) Hc) as U.
  exists (unique_obj U).
  exact (snd (unique_property U)).
Defined.

(* Every (E, Mono) factorization system supplies images. *)
Definition ImageOf_of_OFS (O : OFS E (@MonoClass C)) {y x : C} (f : y ~> x) :
  ImageOf f := {|
  im_sub := ofs_image_sub O f;
  im_factor := fact_e (ofs_factor (OFS := O) f);
  im_commutes := fact_comm (ofs_factor (OFS := O) f);
  im_least := fun w g Hg => ofs_image_least O f w g Hg
|}.

Definition HasImages_of_OFS (O : OFS E (@MonoClass C)) : HasImages C :=
  {| image_of := fun y x f => ImageOf_of_OFS O f |}.

End OFSImages.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Regular_HasImages {C : Category} (R : Regular C) : HasImages C :=
  HasImages_of_OFS (@Regular_OFS C R).
