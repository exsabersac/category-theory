Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Adjoint.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本文件给出伴随相关构造与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Fullness 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明伴随、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma split_inverses_agree {E : Category} {x y : E} (f : x ~> y)
      (s t : y ~> x) : s ∘ f ≈ id → f ∘ t ≈ id → s ≈ t.
Proof. intros Hs Ht. symmetry. exact (comp_inverse_unique f t s Ht Hs). Qed.

Section Fullness.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context `{A : F ⊣ U}.

Notation "'η' x" := (@unit C D F U A x)
  (at level 9, only parsing).
Notation "'ε' x" := (@counit C D F U A x)
  (at level 9, only parsing).

(* ** (A) The split-morphism core *)

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition counit_inv_of_full_right (HU : Full U) (a : C) : a ~> F (U a) :=
  @prefmap C D U HU a (F (U a)) (η (U a)).

Lemma counit_inv_of_full_right_fmap (HU : Full U) (a : C) :
  fmap[U] (counit_inv_of_full_right HU a) ≈ η (U a).
Proof. exact (@fmap_sur C D U HU a (F (U a)) (η (U a))). Qed.

(* Mac Lane §IV.3: G full makes every counit component a split mono.  The
   argument is naturality of ε at s, whose U-image is η, followed by one
   triangle identity. *)

Lemma counit_inv_of_full_right_comp (HU : Full U) (a : C) :
  counit_inv_of_full_right HU a ∘ ε a ≈ id.
Proof.
  rewrite <- (adj_counit_naturality A (counit_inv_of_full_right HU a)).
  rewrite counit_inv_of_full_right_fmap.
  exact (@counit_fmap_unit C D F U A (U a)).
Qed.

Definition counit_split_mono_of_full_right (HU : Full U) (a : C) :
  Section (ε a) :=
  {| section      := counit_inv_of_full_right HU a
   ; section_comp := counit_inv_of_full_right_comp HU a |}.

(* The dual, 左伴随: chosen F-preimage counit at
 F x right inverse η_x, so η_x split epi. （已译） *)

Definition unit_inv_of_full_left (HF : Full F) (x : D) : U (F x) ~> x :=
  @prefmap D C F HF (U (F x)) x (ε (F x)).

Lemma unit_inv_of_full_left_fmap (HF : Full F) (x : D) :
  fmap[F] (unit_inv_of_full_left HF x) ≈ ε (F x).
Proof. exact (@fmap_sur D C F HF (U (F x)) x (ε (F x))). Qed.

Lemma unit_inv_of_full_left_comp (HF : Full F) (x : D) :
  η x ∘ unit_inv_of_full_left HF x ≈ id.
Proof.
  rewrite <- (adj_unit_naturality A (unit_inv_of_full_left HF x)).
  rewrite unit_inv_of_full_left_fmap.
  exact (@fmap_counit_unit C D F U A (F x)).
Qed.

Definition unit_split_epi_of_full_left (HF : Full F) (x : D) :
  Retraction (η x) :=
  {| retract      := unit_inv_of_full_left HF x
   ; retract_comp := unit_inv_of_full_left_comp HF x |}.

(* ** (B) Exercise 6, componentwise *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma unit_fmap_counit_of_full_right (HU : Full U) (a : C) :
  η (U a) ∘ fmap[U] (ε a) ≈ id.
Proof.
  rewrite <- (counit_inv_of_full_right_fmap HU a).
  rewrite <- fmap_comp.
  rewrite counit_inv_of_full_right_comp.
  apply fmap_id.
Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma unit_fmap_counit_of_full_left (HF : Full F) (a : C) :
  η (U a) ∘ fmap[U] (ε a) ≈ id.
Proof.
  rewrite (split_inverses_agree (η (U a)) (fmap[U] (ε a))
             (unit_inv_of_full_left HF (U a))
             (@fmap_counit_unit C D F U A a)
             (unit_inv_of_full_left_comp HF (U a))).
  exact (unit_inv_of_full_left_comp HF (U a)).
Qed.

Definition unit_fmap_counit (H : Full F + Full U) (a : C) :
  η (U a) ∘ fmap[U] (ε a) ≈ id :=
  match H with
  | inl HF => unit_fmap_counit_of_full_left HF a
  | inr HU => unit_fmap_counit_of_full_right HU a
  end.

(* Exercise 6, componentwise: Uε_a is invertible with inverse η_{Ua}. *)

Definition fmap_counit_IsIsomorphism_of_full (H : Full F + Full U) (a : C) :
  IsIsomorphism (fmap[U] (ε a)) :=
  {| two_sided_inverse := η (U a)
   ; is_right_inverse  := @fmap_counit_unit C D F U A a
   ; is_left_inverse   := unit_fmap_counit H a |}.

(* ** (B) Exercise 6, other handedness, componentwise *)

(* Here roles two hypotheses swap: cheap one [Full F],
 because F η_x then F-image 复合 already known be
 恒等. （已译） *)

Lemma fmap_unit_counit_of_full_left (HF : Full F) (x : D) :
  fmap[F] (η x) ∘ ε (F x) ≈ id.
Proof.
  rewrite <- (unit_inv_of_full_left_fmap HF x).
  rewrite <- fmap_comp.
  rewrite unit_inv_of_full_left_comp.
  apply fmap_id.
Qed.

Lemma fmap_unit_counit_of_full_right (HU : Full U) (x : D) :
  fmap[F] (η x) ∘ ε (F x) ≈ id.
Proof.
  rewrite <- (split_inverses_agree (ε (F x))
                (counit_inv_of_full_right HU (F x)) (fmap[F] (η x))
                (counit_inv_of_full_right_comp HU (F x))
                (@counit_fmap_unit C D F U A x)).
  exact (counit_inv_of_full_right_comp HU (F x)).
Qed.

Definition fmap_unit_counit (H : Full F + Full U) (x : D) :
  fmap[F] (η x) ∘ ε (F x) ≈ id :=
  match H with
  | inl HF => fmap_unit_counit_of_full_left HF x
  | inr HU => fmap_unit_counit_of_full_right HU x
  end.

Definition counit_at_F_IsIsomorphism_of_full (H : Full F + Full U) (x : D) :
  IsIsomorphism (ε (F x)) :=
  {| two_sided_inverse := fmap[F] (η x)
   ; is_right_inverse  := @counit_fmap_unit C D F U A x
   ; is_left_inverse   := fmap_unit_counit H x |}.

(*
   本节说明自然变换相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition whiskered_counit : U ◯ F ◯ U ⟹ U := {|
  transform := fun a => fmap[U] (ε a)
|}.
Next Obligation.
  rewrite <- !fmap_comp.
  apply fmap_respects.
  now rewrite (adj_counit_naturality A f).
Qed.
Next Obligation.
  rewrite <- !fmap_comp.
  apply fmap_respects.
  now rewrite (adj_counit_naturality A f).
Qed.

Program Definition whiskered_unit : U ⟹ U ◯ F ◯ U := {|
  transform := fun a => η (U a)
|}.
Next Obligation. now rewrite (adj_unit_naturality A (fmap[U] f)). Qed.
Next Obligation. now rewrite (adj_unit_naturality A (fmap[U] f)). Qed.

(*
   本节说明 Fullness 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition whiskered_counit_iso_of_full (H : Full F + Full U) :
  @Isomorphism ([C, D]) (U ◯ F ◯ U) U := {|
  to   := whiskered_counit
; from := whiskered_unit
|}.
Next Obligation.
  rewrite fmap_id.
  exact (@fmap_counit_unit C D F U A x).
Qed.
Next Obligation.
  rewrite !fmap_id.
  exact (unit_fmap_counit H x).
Qed.

Definition whiskered_counit_iso_of_full_left (HF : Full F) :
  @Isomorphism ([C, D]) (U ◯ F ◯ U) U :=
  whiskered_counit_iso_of_full (inl HF).

Definition whiskered_counit_iso_of_full_right (HU : Full U) :
  @Isomorphism ([C, D]) (U ◯ F ◯ U) U :=
  whiskered_counit_iso_of_full (inr HU).

(* The other handedness, in [D, C]. *)

Program Definition whiskered_unit_F : F ◯ U ◯ F ⟹ F := {|
  transform := fun x => ε (F x)
|}.
Next Obligation. now rewrite (adj_counit_naturality A (fmap[F] f)). Qed.
Next Obligation. now rewrite (adj_counit_naturality A (fmap[F] f)). Qed.

Program Definition whiskered_counit_F : F ⟹ F ◯ U ◯ F := {|
  transform := fun x => fmap[F] (η x)
|}.
Next Obligation.
  rewrite <- !fmap_comp.
  apply fmap_respects.
  now rewrite (adj_unit_naturality A f).
Qed.
Next Obligation.
  rewrite <- !fmap_comp.
  apply fmap_respects.
  now rewrite (adj_unit_naturality A f).
Qed.

Program Definition whiskered_unit_iso_of_full (H : Full F + Full U) :
  @Isomorphism ([D, C]) (F ◯ U ◯ F) F := {|
  to   := whiskered_unit_F
; from := whiskered_counit_F
|}.
Next Obligation.
  rewrite fmap_id.
  exact (@counit_fmap_unit C D F U A x).
Qed.
Next Obligation.
  rewrite !fmap_id.
  exact (fmap_unit_counit H x).
Qed.

Definition whiskered_unit_iso_of_full_left (HF : Full F) :
  @Isomorphism ([D, C]) (F ◯ U ◯ F) F :=
  whiskered_unit_iso_of_full (inl HF).

Definition whiskered_unit_iso_of_full_right (HU : Full U) :
  @Isomorphism ([D, C]) (F ◯ U ◯ F) F :=
  whiskered_unit_iso_of_full (inr HU).

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma unit_at_UF_of_full_right (HU : Full U) (x : D) :
  η (U (F x)) ≈ fmap[U] (fmap[F] (η x)).
Proof.
  assert (Hr : fmap[U] (ε (F x)) ∘ fmap[U] (fmap[F] (η x)) ≈ id).
  { rewrite <- fmap_comp.
    rewrite (@counit_fmap_unit C D F U A x).
    apply fmap_id. }
  rewrite <- (id_right (η (U (F x)))).
  rewrite <- Hr.
  rewrite comp_assoc.
  rewrite (unit_fmap_counit_of_full_right HU (F x)).
  now rewrite id_left.
Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma unit_epic_of_full_monic (HU : Full U)
      (Hm : ∀ y : D, Monic (η y)) (x : D) : Epic (η x).
Proof.
  construct.
  apply (@monic D _ _ (η z) (Hm z)).
  rewrite <- !(adj_unit_naturality A).
  rewrite (unit_at_UF_of_full_right HU x).
  rewrite <- !fmap_comp.
  now rewrite X.
Qed.

(* ** (C) Exercise 3, LEFT adjoint full (the literal print)

 With LEFT adjoint full conclusion needs no monic 假设 at
 all, η_x being split epi outright. （已译） *)

Lemma unit_epic_of_full_left (HF : Full F) (x : D) : Epic (η x).
Proof. now apply retractions_are_epic, unit_split_epi_of_full_left. Qed.

(* ... monic 假设 then upgrades conclusion epi to
 invertible, sharpest statement reading supports. （已译） *)

Definition unit_iso_of_full_monic (HF : Full F)
           (Hm : ∀ y : D, Monic (η y)) (x : D) : IsIsomorphism (η x).
Proof.
  unshelve econstructor.
  - exact (unit_inv_of_full_left HF x).
  - exact (unit_inv_of_full_left_comp HF x).
  - apply (@monic D _ _ (η x) (Hm x)).
    rewrite comp_assoc.
    rewrite unit_inv_of_full_left_comp.
    now rewrite id_left, id_right.
Defined.

(* ** A by-product

 Under fullness either adjoint unit invertible at every 对象
 image U -- (B) read backwards, inverse being
 Uε_a. （已译） *)

Definition unit_at_U_IsIsomorphism_of_full (H : Full F + Full U) (a : C) :
  IsIsomorphism (η (U a)) :=
  {| two_sided_inverse := fmap[U] (ε a)
   ; is_right_inverse  := unit_fmap_counit H a
   ; is_left_inverse   := @fmap_counit_unit C D F U A a |}.

End Fullness.

(*
   本节说明 Fullness 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.

Example whiskered_counit_is_whisker_left
  {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) (a : C) :
  transform[@whiskered_counit C D F U A] a
    = transform[U ⊳ (@counit _ _ _ _ (@Adjunction_to_Transform C D F U A))] a.
Proof. reflexivity. Qed.

Example whiskered_unit_is_whisker_right
  {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) (a : C) :
  transform[@whiskered_unit C D F U A] a
    = transform[(@unit _ _ _ _ (@Adjunction_to_Transform C D F U A)) ⊲ U] a.
Proof. reflexivity. Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.

(*
   本节说明伴随、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Module HomSetAdj := Category.Theory.Adjunction.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition reflective_fmap_counit_IsIsomorphism {C : Category}
  {S : Subcategory C} (R : Reflective S) (x : Sub C S) :
  IsIsomorphism
    (fmap[Incl C S]
       (@HomSetAdj.counit (Sub C S) C (reflector R) (Incl C S)
                (reflective_adj R) x)) :=
  @fmap_counit_IsIsomorphism_of_full (Sub C S) C (reflector R) (Incl C S)
    (reflective_adj R)
    (inr (Full_Implies_Full_Functor C S (reflective_full R))) x.

(* 相关说明。 （已译） *)

Example reflective_fmap_counit_inverse {C : Category}
  {S : Subcategory C} (R : Reflective S) (x : Sub C S) :
  two_sided_inverse
    (IsIsomorphism := reflective_fmap_counit_IsIsomorphism R x)
    = @HomSetAdj.unit (Sub C S) C (reflector R) (Incl C S)
        (reflective_adj R) (Incl C S x)
  := eq_refl.

(*
   本节说明伴随、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Theory.Equivalence.

Definition equiv_fmap_counit_IsIsomorphism {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) (d : D) :
  IsIsomorphism
    (fmap[@quasi_inverse C D F E]
       (@HomSetAdj.counit D C F (@quasi_inverse C D F E)
          (equiv_adjunction E) d)) :=
  @fmap_counit_IsIsomorphism_of_full D C F (@quasi_inverse C D F E)
    (equiv_adjunction E) (inl (Equivalence_Full E)) d.

Example equiv_fmap_counit_inverse {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) (d : D) :
  two_sided_inverse
    (IsIsomorphism := equiv_fmap_counit_IsIsomorphism E d)
    = @HomSetAdj.unit D C F (@quasi_inverse C D F E) (equiv_adjunction E)
        (@quasi_inverse C D F E d)
  := eq_refl.

(* The donor's own counit 同构 about counit itself; its
 inverse, pushed through [quasi_inverse], agrees file's up to
 `≈` -- both inverse same arrow. （已译） *)

Lemma equiv_fmap_counit_inverse_agrees {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) (d : D) :
  @HomSetAdj.unit D C F (@quasi_inverse C D F E) (equiv_adjunction E)
      (@quasi_inverse C D F E d)
    ≈ fmap[@quasi_inverse C D F E]
        (two_sided_inverse
           (IsIsomorphism := equiv_adjunction_counit_iso E d)).
Proof.
  pose proof (@HomSetAdj.fmap_counit_unit D C F
                (@quasi_inverse C D F E) (equiv_adjunction E) d) as Ht.
  pose proof (@is_left_inverse D _ _ _
                (equiv_adjunction_counit_iso E d)) as Hk.
  rewrite <- (id_left (@HomSetAdj.unit D C F
                         (@quasi_inverse C D F E) (equiv_adjunction E)
                         (@quasi_inverse C D F E d))).
  rewrite <- fmap_id.
  rewrite <- Hk.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite Ht.
  now rewrite id_right.
Qed.

(*
   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Instance.One.
Require Import Category.Functor.Diagonal.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Instance.Sets.Pointed.

Definition Full_Erase_of_ZeroObject@{o h +} {C : Category@{o h h}}
  (Z : ZeroObject C) : Functor.Full (Erase C).
Proof.
  unshelve econstructor.
  - exact (fun x y _ => @zero_mor C Z x y).
  - intros x y g; destruct g; reflexivity.
Defined.

Definition zero_erase_adjunction {C : Category} (Z : ZeroObject C) :
  @Diagonal C _1 (@initial_obj C (@zero_initial C Z)) ⊣ Erase C :=
  Initial_Erase_Adjunction (@zero_initial C Z).

Definition zero_erase_fmap_counit_IsIsomorphism {C : Category}
  (Z : ZeroObject C) (a : C) :
  IsIsomorphism
    (fmap[Erase C]
       (@HomSetAdj.counit C _1
          (@Diagonal C _1 (@initial_obj C (@zero_initial C Z)))
          (Erase C) (zero_erase_adjunction Z) a)) :=
  @fmap_counit_IsIsomorphism_of_full C _1
    (@Diagonal C _1 (@initial_obj C (@zero_initial C Z)))
    (Erase C) (zero_erase_adjunction Z)
    (inr (Full_Erase_of_ZeroObject Z)) a.

(* [PointedSets] has zero 对象, so above applies it; there
 右伴随 provably NOT faithful. （已译） *)

Lemma Erase_PointedSets_not_Faithful :
  Faithful (Erase PointedSets) → False.
Proof.
  intros HF.
  assert (Hid : @id PointedSets PointedTwo
                  ≈ @pointed_const PointedTwo PointedTwo).
  { apply (@fmap_inj PointedSets _1 (Erase PointedSets) HF).
    reflexivity. }
  specialize (Hid (Datatypes.Some ttt)).
  simpl in Hid.
  contradiction.
Qed.

(* 相关说明。 （已译） *)

Lemma pointed_counit_not_IsIsomorphism :
  IsIsomorphism
    (@HomSetAdj.counit PointedSets _1
       (@Diagonal PointedSets _1
          (@initial_obj PointedSets (@zero_initial PointedSets
                                       PointedSets_Zero)))
       (Erase PointedSets) (zero_erase_adjunction PointedSets_Zero)
       PointedTwo) → False.
Proof.
  intros HI.
  pose proof (@is_right_inverse PointedSets _ _ _ HI) as Hr.
  rewrite (@zero_unique PointedSets
             (@zero_initial PointedSets PointedSets_Zero) PointedTwo
             _ (@pointed_const PointedOne PointedTwo)) in Hr.
  specialize (Hr (Datatypes.Some ttt)).
  simpl in Hr.
  contradiction.
Qed.
