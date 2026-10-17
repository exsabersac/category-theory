Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Size.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Structure.UniversalProperty.
Require Import Category.Structure.UniversalProperty.Terminal.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.Representability.Sets.

Generalizable All Variables.

(** * The solution set condition cannot be dropped *)

(*
   Book: Awodey, "Category Theory", 2nd ed., §9.8, Remark 9.30, printed
   nLab: https://ncatlab.org/nlab/show/adjoint+functor+theorem
   Wikipedia: https://en.wikipedia.org/wiki/Complete_Boolean_algebra

   本文件给出一般伴随函子定理相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The constant functor at the singleton, and its continuity *)

Section ConstOneContinuity.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Universes o h.
Context (C : Category@{o h h}).

(* Any two maps into the singleton agree.  This is the whole of the
   continuity proof: both the mediator and its uniqueness clause are
   instances of it. *)
Lemma ConstOne_hom_unique {x : C} {X : Sets}
  (f g : X ~{Sets}~> ConstOne C x) : f ≈ g.
Proof. intro a; destruct (f a), (g a); reflexivity. Qed.

Program Definition ConstOne_pt (x : C) (X : Sets) :
  X ~{Sets}~> ConstOne C x := {| morphism := fun _ => ttt |}.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ConstOne_continuous : ContinuousFunctor (ConstOne C).
Proof.
  intros J K N HN M.
  unshelve refine
    {| unique_obj := ConstOne_pt (vertex_obj[N]) (vertex_obj[M]) |}.
  - intro y; apply (ConstOne_hom_unique (x := K y)).
  - intros v Hv; apply (ConstOne_hom_unique (x := vertex_obj[N])).
Defined.

(* The same fact in the hypothesis shape that [GAFT] and
   [representability_theorem] consume. *)
Definition ConstOne_PreservesImageLimit :
  @PreservesImageLimit C Sets (ConstOne C) :=
  Continuous_PreservesImageLimit ConstOne_continuous.

End ConstOneContinuity.

(** ** Representability of [ConstOne C] is exactly initiality of [C] *)

Section ConstOneRepresentable.

Universes o h.
Context (C : Category@{o h h}).

(* Forward.  A representation names an object whose every hom-setoid is a
   singleton; [repr_to_initial] is that step, already in tree. *)
Definition initial_of_ConstOne_representable
  (R : Representable (ConstOne C)) : @Initial C :=
  Initial_from_IsInitialObj
    (repr_to_initial C (@repr_obj C (ConstOne C) R)
                       (@represented C (ConstOne C) R)).

(* Converse. *)
Definition ConstOne_representable_of_initial (I : @Initial C) :
  Representable (ConstOne C) :=
  {| repr_obj := @initial_obj C I
   ; represented :=
       initial_to_repr C (@initial_obj C I) (IsInitialObj_from_Initial I) |}.

(* The sharp form. *)
Theorem ConstOne_representable_iff_initial :
  Representable (ConstOne C) ↔ @Initial C.
Proof.
  split.
  - exact initial_of_ConstOne_representable.
  - exact ConstOne_representable_of_initial.
Defined.

Definition ConstOne_not_representable (Hno : @Initial C → False)
  (R : Representable (ConstOne C)) : False :=
  Hno (initial_of_ConstOne_representable R).

(* The representing object is the initial object, on the nose. *)
Example ConstOne_repr_obj (I : @Initial C) :
  @repr_obj C (ConstOne C) (ConstOne_representable_of_initial I)
    = @initial_obj C I := eq_refl.

End ConstOneRepresentable.

(** ** The limit of the identity functor is an initial object *)

Section LimitId.

Universes o h.
Context {C : Category@{o h h}}.
Context (L : Limit (@Id C)).

Definition lim_id_obj : C := vertex_obj[@limit_cone _ _ _ L].

Definition lim_id_leg (x : C) : lim_id_obj ~> x :=
  cone_leg (@limit_cone _ _ _ L) x.

(* Cone coherence at the identity diagram: every arrow out of the apex
   commutes with the legs. *)
Lemma lim_id_coh {x y : C} (f : x ~> y) : f ∘ lim_id_leg x ≈ lim_id_leg y.
Proof.
  exact (@cone_coherence _ _ _ _
           (@coneFrom _ _ _ (@limit_cone _ _ _ L)) x y f).
Qed.

(* The leg at the apex is the identity: it mediates the limit cone to
   itself, and so does [id], and the mediator is unique. *)
Lemma lim_id_leg_self : lim_id_leg lim_id_obj ≈ id.
Proof.
  pose proof (@ump_limits _ _ _ L (@limit_cone _ _ _ L)) as U.
  transitivity (unique_obj U).
  - symmetry; apply (uniqueness U); intro x; apply lim_id_coh.
  - apply (uniqueness U); intro x; apply id_right.
Qed.

(* ...hence every arrow out of the apex IS the leg. *)
Lemma lim_id_hom_unique {x : C} (f : lim_id_obj ~> x) : f ≈ lim_id_leg x.
Proof.
  rewrite <- (lim_id_coh f), lim_id_leg_self.
  now rewrite id_right.
Qed.

Definition Initial_of_limit_id : @Initial C :=
  @Build_Terminal (C^op) lim_id_obj (fun x => lim_id_leg x)
    (fun x f g => transitivity (lim_id_hom_unique f)
                    (symmetry (lim_id_hom_unique g))).

End LimitId.

(** ** Consequence: the library's [Complete] already carries an initial
       object, so "complete with no initial object" is an EMPTY hypothesis *)

Definition Complete_Initial {C : Category} (comp : @Complete C) : @Initial C :=
  Initial_of_limit_id (comp C Id).

Definition Complete_ConstOne_representable {C : Category}
  (comp : @Complete C) : Representable (ConstOne C) :=
  ConstOne_representable_of_initial C (Complete_Initial comp).

Definition Complete_no_initial_absurd {C : Category}
  (comp : @Complete C) (Hno : @Initial C → False) : False :=
  Hno (Complete_Initial comp).

(* ...and the initial object it produces IS the limit of the identity
   functor, on the nose. *)
Example Complete_Initial_obj {C : Category} (comp : @Complete C) :
  @initial_obj C (Complete_Initial comp) = lim_id_obj (comp C Id) := eq_refl.

(** ** Completeness for SMALL shapes, which is Mac Lane's hypothesis *)

Definition SmallShapeComplete (C : Category) : Type :=
  ∀ (D : Category), Small D → ∀ F : D ⟶ C, Limit F.

Definition Complete_SmallShapeComplete {C : Category} (comp : @Complete C) :
  SmallShapeComplete C := fun D _ F => comp D F.

(* Freyd's size boundary in the shape this file needs it: if the category
   is ITSELF small, small-shape completeness takes back the identity
   diagram and the initial object comes back. *)
Definition SmallShapeComplete_Initial_of_Small {C : Category}
  (SC : Small C) (HC : SmallShapeComplete C) : @Initial C :=
  Initial_of_limit_id (HC C SC Id).

(** ** The sharpness clause *)

(*
   本节说明 Necessity 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition RepresentabilityWithoutSolutionSet : Type :=
  ∀ (C : Category) (K : C ⟶ Sets),
    SmallShapeComplete C → LocallySmall C → ContinuousFunctor K →
    Representable K.

Theorem representability_without_solution_set_refuted (C : Category)
  (HC : SmallShapeComplete C) (Hno : @Initial C → False) :
  RepresentabilityWithoutSolutionSet → False.
Proof.
  intro H.
  exact (ConstOne_not_representable C Hno
           (H C (ConstOne C) HC (locally_small_ambient C)
              (ConstOne_continuous C))).
Qed.

(* Mac Lane §V.6 Theorem 2 (GAFT) with the solution set dropped. *)
Definition GAFTWithoutSolutionSet : Type :=
  ∀ (C D : Category) (U : C ⟶ D),
    SmallShapeComplete C → LocallySmall C → ContinuousFunctor U →
    { F : D ⟶ C & F ⊣ U }.

Theorem gaft_without_solution_set_refuted (C : Category)
  (HC : SmallShapeComplete C) (Hno : @Initial C → False) :
  GAFTWithoutSolutionSet → False.
Proof.
  intro H.
  destruct (H C Sets (ConstOne C) HC (locally_small_ambient C)
              (ConstOne_continuous C)) as [F A].
  exact (ConstOne_not_representable C Hno
           (representable_of_left_adjoint (ConstOne C) A)).
Qed.

(* Awodey §9.8's size clause, in the only direction this file can prove:
   a witness to the sharpness above is necessarily NOT small. *)
Theorem no_initial_not_Small (C : Category)
  (HC : SmallShapeComplete C) (Hno : @Initial C → False) : Small C → False.
Proof. intro SC; exact (Hno (SmallShapeComplete_Initial_of_Small SC HC)). Qed.

(** ** The complete-Boolean-algebra half, conditional on Solovay's theorem *)

Section Solovay.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Context (CBA : Category).
Context (U : CBA ⟶ Sets).
Context (Countable : Sets).
Context (solovay : UniversalArrow Countable U → False).

Theorem solovay_no_left_adjoint : { F : Sets ⟶ CBA & F ⊣ U } → False.
Proof using CBA Countable U solovay.
  intros [F A]; exact (solovay (universal_arrow_of_adjunction A Countable)).
Qed.

Context (HCBA : SmallShapeComplete CBA).
Context (HU : ContinuousFunctor U).

Theorem solovay_gaft_refuted : GAFTWithoutSolutionSet → False.
Proof using CBA Countable HCBA HU U solovay.
  intro H.
  exact (solovay_no_left_adjoint
           (H CBA Sets U HCBA (locally_small_ambient CBA) HU)).
Qed.

End Solovay.
