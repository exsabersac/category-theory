Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Idempotent.
Require Import Category.Monad.Comparison.
Require Import Category.Comonad.Core.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Opposite.

Generalizable All Variables.

(** * The fixed points of an adjunction *)

(*
   nLab:      https://ncatlab.org/nlab/show/adjoint+functor
   Wikipedia: https://en.wikipedia.org/wiki/Galois_connection
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Book:      Riehl, "Category Theory in Context", Dover 2016, SS 4.2,

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Three inverse-calculus lemmas, restated locally *)

(* Transport of invertibility along an equation between parallel arrows. *)
Definition fixed_IsIso_along {X : Category} {x y : X} {f g : x ~> y}
  (Hf : IsIsomorphism f) (E : f ≈ g) : IsIsomorphism g.
Proof.
  destruct Hf as [k Hr Hl].
  refine {| two_sided_inverse := k |}; now rewrite <- E.
Defined.

(* The forward leg of a bundled isomorphism is an invertible morphism. *)
Definition fixed_IsIso_of_iso {X : Category} {x y : X} (f : x ≅ y) :
  IsIsomorphism (to f) :=
  {| two_sided_inverse := from f
   ; is_right_inverse := iso_to_from f
   ; is_left_inverse := iso_from_to f |}.

(* A composite of invertible morphisms is invertible, via [iso_compose]. *)
Definition fixed_IsIso_comp {X : Category} {x y z : X}
  {f : x ~> y} {g : y ~> z}
  (Hf : IsIsomorphism f) (Hg : IsIsomorphism g) : IsIsomorphism (g ∘ f) :=
  fixed_IsIso_of_iso
    (iso_compose (@IsIsoToIso X _ _ g Hg) (@IsIsoToIso X _ _ f Hf)).

(** ** (A) The two fixed subcategories and the restricted equivalence *)

Section FixedPoints.

Context {C D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

(** *** The closure facts *)

(*
   本节说明 FixedPoints 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition counit_iso_of_unit_iso (x : D)
  (H : IsIsomorphism (@unit C D F U A x)) :
  IsIsomorphism (@counit C D F U A (F x)).
Proof.
  refine {| two_sided_inverse := fmap[F] (@unit C D F U A x) |}.
  - exact (@counit_fmap_unit C D F U A x).
  - destruct (fmap_IsIsomorphism F (@unit C D F U A x) H) as [k Hkr Hkl].
    assert (Hek : k ≈ @counit C D F U A (F x)).
    { rewrite <- (id_left k).
      rewrite <- (@counit_fmap_unit C D F U A x).
      rewrite <- comp_assoc, Hkr.
      now rewrite id_right. }
    now rewrite <- Hek.
Defined.

(* The mirror: an invertible counit at [c] gives an invertible unit at
   [U c], with [fmap[U] (counit c)] as inverse and [fmap_counit_unit] as
   the free law. *)
Definition unit_iso_of_counit_iso (c : C)
  (K : IsIsomorphism (@counit C D F U A c)) :
  IsIsomorphism (@unit C D F U A (U c)).
Proof.
  refine {| two_sided_inverse := fmap[U] (@counit C D F U A c) |}.
  - destruct (fmap_IsIsomorphism U (@counit C D F U A c) K) as [k Hkr Hkl].
    assert (Hek : k ≈ @unit C D F U A (U c)).
    { rewrite <- (id_right k).
      rewrite <- (@fmap_counit_unit C D F U A c).
      rewrite comp_assoc, Hkl.
      now rewrite id_left. }
    now rewrite <- Hek.
  - exact (@fmap_counit_unit C D F U A c).
Defined.

(** *** The subcategories *)

(* The full subcategory of D spanned by the objects at which the unit is
   invertible.  [shom] is the terminal predicate, following
   Construction/Reflective/Idempotent.v's [MLocal_Subcategory]. *)
Definition UnitFixed : Subcategory D :=
  {| sobj  := fun x => IsIsomorphism (@unit C D F U A x)
   ; shom  := fun _ _ _ _ _ => True
   ; scomp := fun _ _ _ _ _ _ _ _ _ _ => I
   ; sid   := fun _ _ => I |}.

(* Dually, in C, for the counit. *)
Definition CounitFixed : Subcategory C :=
  {| sobj  := fun c => IsIsomorphism (@counit C D F U A c)
   ; shom  := fun _ _ _ _ _ => True
   ; scomp := fun _ _ _ _ _ _ _ _ _ _ => I
   ; sid   := fun _ _ => I |}.

Definition UnitFixed_Full : Construction.Subcategory.Full D UnitFixed :=
  fun _ _ _ _ _ => I.

Definition CounitFixed_Full : Construction.Subcategory.Full C CounitFixed :=
  fun _ _ _ _ _ => I.

(** *** The restricted functors *)

Definition FixedL_fobj (x : Sub D UnitFixed) : Sub C CounitFixed :=
  (F `1 x; counit_iso_of_unit_iso `1 x `2 x).

Definition FixedL_fmap {x y : Sub D UnitFixed}
  (f : x ~{Sub D UnitFixed}~> y) :
  FixedL_fobj x ~{Sub C CounitFixed}~> FixedL_fobj y :=
  (fmap[F] `1 f; I).

Lemma FixedL_fmap_respects {x y : Sub D UnitFixed} (f g : x ~> y) :
  f ≈ g → FixedL_fmap f ≈ FixedL_fmap g.
Proof. intro E; simpl in *; now rewrite E. Qed.

Lemma FixedL_fmap_id {x : Sub D UnitFixed} :
  FixedL_fmap (@id (Sub D UnitFixed) x) ≈ id.
Proof. simpl; apply fmap_id. Qed.

Lemma FixedL_fmap_comp {x y z : Sub D UnitFixed} (f : y ~> z) (g : x ~> y) :
  FixedL_fmap (f ∘ g) ≈ FixedL_fmap f ∘ FixedL_fmap g.
Proof. simpl; apply fmap_comp. Qed.

Definition FixedL : Sub D UnitFixed ⟶ Sub C CounitFixed :=
  Build_Functor (Sub D UnitFixed) (Sub C CounitFixed)
    FixedL_fobj (@FixedL_fmap)
    (fun x y f g E => FixedL_fmap_respects f g E)
    (fun x => FixedL_fmap_id)
    (fun x y z f g => FixedL_fmap_comp f g).

Definition FixedR_fobj (y : Sub C CounitFixed) : Sub D UnitFixed :=
  (U `1 y; unit_iso_of_counit_iso `1 y `2 y).

Definition FixedR_fmap {x y : Sub C CounitFixed}
  (f : x ~{Sub C CounitFixed}~> y) :
  FixedR_fobj x ~{Sub D UnitFixed}~> FixedR_fobj y :=
  (fmap[U] `1 f; I).

Lemma FixedR_fmap_respects {x y : Sub C CounitFixed} (f g : x ~> y) :
  f ≈ g → FixedR_fmap f ≈ FixedR_fmap g.
Proof. intro E; simpl in *; now rewrite E. Qed.

Lemma FixedR_fmap_id {x : Sub C CounitFixed} :
  FixedR_fmap (@id (Sub C CounitFixed) x) ≈ id.
Proof. simpl; apply fmap_id. Qed.

Lemma FixedR_fmap_comp {x y z : Sub C CounitFixed}
  (f : y ~> z) (g : x ~> y) :
  FixedR_fmap (f ∘ g) ≈ FixedR_fmap f ∘ FixedR_fmap g.
Proof. simpl; apply fmap_comp. Qed.

Definition FixedR : Sub C CounitFixed ⟶ Sub D UnitFixed :=
  Build_Functor (Sub C CounitFixed) (Sub D UnitFixed)
    FixedR_fobj (@FixedR_fmap)
    (fun x y f g E => FixedR_fmap_respects f g E)
    (fun x => FixedR_fmap_id)
    (fun x y z f g => FixedR_fmap_comp f g).

(** *** The restricted adjunction *)

(* The transposition is the ambient one on carriers; the [shom] component
   of every morphism is [I], so nothing is transported. *)
Definition fixed_hom_to (x : Sub D UnitFixed) (y : Sub C CounitFixed)
  (f : FixedL x ~{Sub C CounitFixed}~> y) :
  x ~{Sub D UnitFixed}~> FixedR y :=
  (to (@adj C D F U A `1 x `1 y) `1 f; I).

Definition fixed_hom_from (x : Sub D UnitFixed) (y : Sub C CounitFixed)
  (g : x ~{Sub D UnitFixed}~> FixedR y) :
  FixedL x ~{Sub C CounitFixed}~> y :=
  (from (@adj C D F U A `1 x `1 y) `1 g; I).

Lemma fixed_hom_to_proper (x : Sub D UnitFixed) (y : Sub C CounitFixed) :
  Proper (equiv ==> equiv) (fixed_hom_to x y).
Proof. intros f g E; simpl in *; now rewrite E. Qed.

Lemma fixed_hom_from_proper (x : Sub D UnitFixed) (y : Sub C CounitFixed) :
  Proper (equiv ==> equiv) (fixed_hom_from x y).
Proof. intros f g E; simpl in *; now rewrite E. Qed.

#[local] Obligation Tactic := idtac.

Program Definition fixed_adj_iso
  (x : Sub D UnitFixed) (y : Sub C CounitFixed) :
  @Isomorphism Sets
    {| carrier := @hom (Sub C CounitFixed) (FixedL x) y
     ; is_setoid := @homset (Sub C CounitFixed) (FixedL x) y |}
    {| carrier := @hom (Sub D UnitFixed) x (FixedR y)
     ; is_setoid := @homset (Sub D UnitFixed) x (FixedR y) |} := {|
  to   := {| morphism := fixed_hom_to x y
           ; proper_morphism := fixed_hom_to_proper x y |};
  from := {| morphism := fixed_hom_from x y
           ; proper_morphism := fixed_hom_from_proper x y |}
|}.
Next Obligation.
  intros x y g; simpl.
  sapply (@iso_to_from Sets _ _ (@adj C D F U A `1 x `1 y)).
Qed.
Next Obligation.
  intros x y f; simpl.
  sapply (@iso_from_to Sets _ _ (@adj C D F U A `1 x `1 y)).
Qed.

#[local] Obligation Tactic := cat_simpl.

Definition fixed_adjunction : FixedL ⊣ FixedR.
Proof.
  apply (Build_Adjunction' fixed_adj_iso).
  - intros x y z f g; simpl; apply to_adj_nat_l.
  - intros x y z f g; simpl; apply to_adj_nat_r.
Defined.

(* The restricted unit and counit ARE the ambient ones, on the carrier and
   on the whole sigma. *)
Example fixed_unit_strict (x : Sub D UnitFixed) :
  `1 (@unit _ _ FixedL FixedR fixed_adjunction x)
    = @unit C D F U A `1 x := eq_refl.

Example fixed_counit_strict (y : Sub C CounitFixed) :
  `1 (@counit _ _ FixedL FixedR fixed_adjunction y)
    = @counit C D F U A `1 y := eq_refl.

Example fixed_unit_whole (x : Sub D UnitFixed) :
  @unit _ _ FixedL FixedR fixed_adjunction x
    = (@unit C D F U A `1 x; I) := eq_refl.

Example fixed_counit_whole (y : Sub C CounitFixed) :
  @counit _ _ FixedL FixedR fixed_adjunction y
    = (@counit C D F U A `1 y; I) := eq_refl.

(** *** Lemma 4.2.11 *)

(* The inverses of the restricted unit and counit are the ambient objects'
   own inverses, carried into the subcategory by the terminal [shom]. *)
Definition fixed_unit_inverse (x : Sub D UnitFixed) :
  FixedR (FixedL x) ~{Sub D UnitFixed}~> x :=
  (@two_sided_inverse D _ _ _ `2 x; I).

Definition fixed_counit_inverse (y : Sub C CounitFixed) :
  y ~{Sub C CounitFixed}~> FixedL (FixedR y) :=
  (@two_sided_inverse C _ _ _ `2 y; I).

Definition fixed_AdjointEquivalence : AdjointEquivalence FixedL FixedR.
Proof.
  unshelve refine {| adj_equivalence := fixed_adjunction |}.
  - intro x.
    refine {| two_sided_inverse := fixed_unit_inverse x |}; simpl.
    + exact (@is_right_inverse D _ _ _ `2 x).
    + exact (@is_left_inverse D _ _ _ `2 x).
  - intro y.
    refine {| two_sided_inverse := fixed_counit_inverse y |}; simpl.
    + exact (@is_right_inverse C _ _ _ `2 y).
    + exact (@is_left_inverse C _ _ _ `2 y).
Defined.

(* Riehl Lemma 4.2.11 / Exercise 4.2.iv, and the general half of Mac
   Lane's closing question. *)
Definition adjunction_fixed_point_equivalence :
  EquivalenceOfCategories FixedL :=
  AdjointEquivalence_to_Equivalence fixed_AdjointEquivalence.

Definition fixed_point_equivalence_swap :
  EquivalenceOfCategories FixedR :=
  AdjointEquivalence_to_Equivalence
    (AdjointEquivalence_swap fixed_AdjointEquivalence).

(** ** (B) The fixed objects are the essential image of the other adjoint *)

(*
   本节说明 FixedPoints 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma unit_iso_of_image (x : D) (c : C)
  (K : IsIsomorphism (@counit C D F U A c)) (phi : x ≅ U c) :
  IsIsomorphism (@unit C D F U A x).
Proof.
  destruct (fmap_IsIsomorphism U (fmap[F] (to phi))
              (fmap_IsIsomorphism F (to phi) (fixed_IsIso_of_iso phi)))
    as [k Hkr Hkl].
  unshelve refine
    (fixed_IsIso_along (f := k ∘ (@unit C D F U A (U c) ∘ to phi)) _ _).
  - refine (fixed_IsIso_comp
              (fixed_IsIso_comp (fixed_IsIso_of_iso phi)
                 (unit_iso_of_counit_iso c K)) _).
    refine {| two_sided_inverse := fmap[U] (fmap[F] (to phi))
            ; is_right_inverse := Hkl ; is_left_inverse := Hkr |}.
  - rewrite <- (adj_unit_naturality A (to phi)).
    rewrite comp_assoc, Hkl.
    now rewrite id_left.
Defined.

(* The mirror, through naturality of the counit. *)
Lemma counit_iso_of_image (c : C) (x : D)
  (H : IsIsomorphism (@unit C D F U A x)) (psi : c ≅ F x) :
  IsIsomorphism (@counit C D F U A c).
Proof.
  destruct (fmap_IsIsomorphism F (fmap[U] (from psi))
              (fmap_IsIsomorphism U (from psi)
                 (fixed_IsIso_of_iso (iso_sym psi))))
    as [k Hkr Hkl].
  unshelve refine
    (fixed_IsIso_along
       (f := (from psi ∘ @counit C D F U A (F x)) ∘ k) _ _).
  - refine (fixed_IsIso_comp _
              (fixed_IsIso_comp (counit_iso_of_unit_iso x H)
                 (fixed_IsIso_of_iso (iso_sym psi)))).
    refine {| two_sided_inverse := fmap[F] (fmap[U] (from psi))
            ; is_right_inverse := Hkl ; is_left_inverse := Hkr |}.
  - rewrite <- (adj_counit_naturality A (from psi)).
    rewrite <- comp_assoc, Hkr.
    now rewrite id_right.
Defined.

(* Mac Lane's "the closed elements are the image of R", categorified:
   the unit is invertible at [x] exactly when [x] lies in the essential
   image of U RESTRICTED to the counit-fixed objects. *)
Theorem unit_fixed_iff_image (x : D) :
  IsIsomorphism (@unit C D F U A x)
    ↔ ∃ c : C, IsIsomorphism (@counit C D F U A c) ∧ (x ≅ U c).
Proof.
  split.
  - intro H.
    exact (F x; (counit_iso_of_unit_iso x H,
                 @IsIsoToIso D _ _ (@unit C D F U A x) H)).
  - intros [c [K phi]]; exact (unit_iso_of_image x c K phi).
Defined.

Theorem counit_fixed_iff_image (c : C) :
  IsIsomorphism (@counit C D F U A c)
    ↔ ∃ x : D, IsIsomorphism (@unit C D F U A x) ∧ (c ≅ F x).
Proof.
  split.
  - intro K.
    exact (U c; (unit_iso_of_counit_iso c K,
                 iso_sym (@IsIsoToIso C _ _ (@counit C D F U A c) K))).
  - intros [x [H psi]]; exact (counit_iso_of_image c x H psi).
Defined.

End FixedPoints.

(** ** (C) The comonad side, and the bridge to the monad-side results *)

(*
   本节说明单子、余单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition IdempotentComonad {C : Category} (W : C ⟶ C)
  (H : @Comonad C W) : Type := @IdempotentMonad (C^op) (W^op) H.
Existing Class IdempotentComonad.

(* The W-colocal objects: those at which the comonad counit is invertible.
   Read through [op_subcategory], this is a subcategory of C itself. *)
Definition WLocal_Subcategory {C : Category} {W : C ⟶ C}
  (H : @Comonad C W) : Subcategory C :=
  op_subcategory (@MLocal_Subcategory (C^op) (W^op) H).

(*
   本节说明 FixedPoints 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example wlocal_op_involution {C : Category} (S : Subcategory C) :
  op_subcategory (op_subcategory S) = S := eq_refl.

(* The issue's first work item: the dual of [Idempotent_Reflective], with
   no tactic and no transport. *)
Definition Idempotent_Coreflective {C : Category} {W : C ⟶ C}
  (H : @Comonad C W) (IH : IdempotentComonad W H) :
  Coreflective (WLocal_Subcategory H) :=
  @Idempotent_Reflective (C^op) (W^op) H IH.

(*
   本节说明 FixedPoints 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Coreflective_IdempotentMonad_op {C : Category}
  {S : Subcategory C} (R : Coreflective S) :
  @IdempotentMonad (C^op) (Incl (C^op) (op_subcategory S) ◯ reflector R)
    (Reflective_Monad R) :=
  Reflective_IdempotentMonad R.

(* Membership in the colocal subcategory IS invertibility of the monad
   unit read in C^op, on the nose. *)
Example wlocal_sobj_strict {C : Category} {W : C ⟶ C} (H : @Comonad C W)
  (x : C) :
  sobj C (WLocal_Subcategory H) x
    = @IsIsomorphism (C^op) x (W x) (@extract C W H x) := eq_refl.

(*
   本节说明单子、余单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition wlocal_to_extract {C : Category} {W : C ⟶ C} (H : @Comonad C W)
  (x : C) (o : sobj C (WLocal_Subcategory H) x) :
  IsIsomorphism (@extract C W H x).
Proof.
  refine (@Build_IsIsomorphism C _ _ _
            (@two_sided_inverse (C^op) _ _ _ o) _ _).
  - exact (@is_left_inverse (C^op) _ _ _ o).
  - exact (@is_right_inverse (C^op) _ _ _ o).
Defined.

Definition extract_to_wlocal {C : Category} {W : C ⟶ C} (H : @Comonad C W)
  (x : C) (o : IsIsomorphism (@extract C W H x)) :
  sobj C (WLocal_Subcategory H) x.
Proof.
  refine (@Build_IsIsomorphism (C^op) _ _ _
            (@two_sided_inverse C _ _ _ o) _ _).
  - exact (@is_left_inverse C _ _ _ o).
  - exact (@is_right_inverse C _ _ _ o).
Defined.

Definition wlocal_obj_iff {C : Category} {W : C ⟶ C} (H : @Comonad C W)
  (x : C) :
  sobj C (WLocal_Subcategory H) x ↔ IsIsomorphism (@extract C W H x) :=
  (wlocal_to_extract H x, extract_to_wlocal H x).

Section FixedPointsBridge.

Context {C D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

(*
   本节说明伴随、单子、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example unit_fixed_is_mlocal :
  UnitFixed A
    = @MLocal_Subcategory D (U ◯ F) (Adjunction_Induced_Monad A) := eq_refl.

(* The issue's fifth work item, positive half: with idempotency the
   fixed subcategory is REFLECTIVE.  This is the one statement below that
   needs a hypothesis beyond the bare adjunction. *)
Definition unit_fixed_reflective_of_idempotent
  (IM : @IdempotentMonad D (U ◯ F) (Adjunction_Induced_Monad A)) :
  Reflective (UnitFixed A) :=
  @Idempotent_Reflective D (U ◯ F) (Adjunction_Induced_Monad A) IM.

(* The opposite adjunction's unit IS this adjunction's counit -- same
   term, same type, since a hom of C^op is a reversed hom of C. *)
Example fixed_op_unit_is_counit (c : C) :
  @unit (D^op) (C^op) (U^op) (F^op) (Opposite_Adjunction F U A) c
    = @counit C D F U A c := eq_refl.

(* Consequently the counit-fixed objects are the unit-fixed objects of the
   opposite adjunction, read in C^op. *)
Example counit_fixed_op_strict (c : C) :
  sobj (C^op) (UnitFixed (Opposite_Adjunction F U A)) c
    = @IsIsomorphism (C^op) c (F (U c)) (@counit C D F U A c) := eq_refl.

(*
   本节说明伴随、余单子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition counit_fixed_op_reflective_of_idempotent
  (IM : @IdempotentMonad (C^op) (F^op ◯ U^op)
          (Adjunction_Induced_Monad (Opposite_Adjunction F U A))) :
  Reflective (UnitFixed (Opposite_Adjunction F U A)) :=
  @Idempotent_Reflective (C^op) (F^op ◯ U^op)
    (Adjunction_Induced_Monad (Opposite_Adjunction F U A)) IM.

End FixedPointsBridge.
