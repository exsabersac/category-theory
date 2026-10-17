Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Absolute.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Coequalizer.Contractible.
Require Import Category.Instance.Parallel.
Require Import Category.Construction.Lift.

Generalizable All Variables.

(** * Absolute coequalizers *)

(*
   Paper:  Paré, "On absolute colimits", J. Algebra 19 (1971) 80-95
   nLab:   https://ncatlab.org/nlab/show/absolute+colimit
   nLab:   https://ncatlab.org/nlab/show/split+coequalizer

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Definition AbsoluteCoequalizer@{co ch xo xh +}
  {C : Category@{co ch ch}} {x y : C} (f g : x ~> y) (q : C) (e : y ~> q) :
  Type :=
  ∀ (X : Category@{xo xh xh}) (T : C ⟶ X),
    IsCoequalizer (fmap[T] f) (fmap[T] g) (T q) (fmap[T] e).

Definition AbsoluteCoequalizer_IsCoequalizer@{co ch +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y} {q : C} {e : y ~> q}
  (A : AbsoluteCoequalizer f g q e) : IsCoequalizer f g q e :=
  A C Id.

(* 相关说明。 （已译） *)

Definition split_coequalizer_absolute@{co ch xo xh +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y}
  (S : SplitCoequalizer f g) :
  AbsoluteCoequalizer@{co ch xo xh _} f g (scoeq_obj S) (scoeq_e S) :=
  fun X T => split_coequalizer_preserved T f g S.

(* 相关说明。 （已译） *)

(*
   本节说明 Absolute 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition AbsoluteCoequalizer_IsCoequalizer_up@{co ch xo xh +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y} {q : C} {e : y ~> q}
  (A : AbsoluteCoequalizer@{co ch xo xh _} f g q e) :
  IsCoequalizer f g q e.
Proof.
  pose (E := A (LiftCat C) (Lift_in C)).
  unshelve econstructor.
  - exact (cofork E).
  - intros z h Hh.
    pose (U := coeq_desc E (z := z) h Hh).
    unshelve eapply Build_Unique.
    + exact (unique_obj U).
    + exact (unique_property U).
    + intros v Hv. exact (uniqueness U v Hv).
Defined.

(* Each instance implies every lower one: target X below the
 假设' levels read at them, [Lift_after T] replaces T. （已译） *)

Definition AbsoluteCoequalizer_down@{co ch xo xh yo yh +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y} {q : C} {e : y ~> q}
  (A : AbsoluteCoequalizer@{co ch yo yh _} f g q e) :
  AbsoluteCoequalizer@{co ch xo xh _} f g q e.
Proof.
  intros X T.
  pose (E := A (LiftCat X) (Lift_after T)).
  unshelve econstructor.
  - exact (cofork E).
  - intros z h Hh.
    pose (U := coeq_desc E (z := z) h Hh).
    unshelve eapply Build_Unique.
    + exact (unique_obj U).
    + exact (unique_property U).
    + intros v Hv. exact (uniqueness U v Hv).
Defined.

(* 相关说明。 （已译） *)

Example image_cofork_inj_ParX@{co ch xo +}
  {C : Category@{co ch ch}} {X : Category@{xo ch ch}} (T : C ⟶ X)
  {x y : C} {f g : x ~> y} {q : C} {e : y ~> q} (H : e ∘ f ≈ e ∘ g) :
  cocone_inj (FCocone T (cofork_cocone f g e H)) ParX = fmap[T] (e ∘ f)
  := eq_refl.

Example image_cofork_inj_ParY@{co ch xo +}
  {C : Category@{co ch ch}} {X : Category@{xo ch ch}} (T : C ⟶ X)
  {x y : C} {f g : x ~> y} {q : C} {e : y ~> q} (H : e ∘ f ≈ e ∘ g) :
  cocone_inj (FCocone T (cofork_cocone f g e H)) ParY = fmap[T] e
  := eq_refl.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition image_coequalizer_colimit@{co ch xo +}
  {C : Category@{co ch ch}} {X : Category@{xo ch ch}} (T : C ⟶ X)
  {x y : C} {f g : x ~> y} {q : C} {e : y ~> q} (H : e ∘ f ≈ e ∘ g)
  (E : IsCoequalizer (fmap[T] f) (fmap[T] g) (T q) (fmap[T] e)) :
  IsColimitCocone (FCocone T (cofork_cocone f g e H)).
Proof.
  refine (limitcone_transport _
            (parallel_coequalizer_colimit (T ◯ APair f g) E)).
  exists (@iso_id (X^op) (T q)).
  intro p; destruct p; simpl.
  - rewrite id_left.
    exact (fmap_comp e f).
  - apply id_left.
Defined.

Definition image_colimit_coequalizer@{co ch xo +}
  {C : Category@{co ch ch}} {X : Category@{xo ch ch}} (T : C ⟶ X)
  {x y : C} {f g : x ~> y} {q : C} {e : y ~> q} (H : e ∘ f ≈ e ∘ g)
  (HC : IsColimitCocone (FCocone T (cofork_cocone f g e H))) :
  IsCoequalizer (fmap[T] f) (fmap[T] g) (T q) (fmap[T] e) :=
  parallel_colimit_coequalizer (T ◯ APair f g) _ HC.

Example image_colimit_coequalizer_desc@{co ch xo +}
  {C : Category@{co ch ch}} {X : Category@{xo ch ch}} (T : C ⟶ X)
  {x y : C} {f g : x ~> y} {q : C} {e : y ~> q} (H : e ∘ f ≈ e ∘ g)
  (HC : IsColimitCocone (FCocone T (cofork_cocone f g e H)))
  {z : X} (h : T y ~{X}~> z) (Hh : h ∘ fmap[T] f ≈ h ∘ fmap[T] g) :
  unique_obj (coeq_desc (image_colimit_coequalizer T H HC) h Hh)
    = unique_obj (HC (parallel_cofork_cocone (T ◯ APair f g) h Hh))
  := eq_refl.

(* 相关说明。 （已译） *)


Definition AbsoluteCoequalizer_AbsoluteColimitCocone@{co ch +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y} {q : C} {e : y ~> q}
  (H : e ∘ f ≈ e ∘ g) (A : AbsoluteCoequalizer f g q e) :
  AbsoluteColimitCocone (cofork_cocone f g e H) :=
  fun D T => image_coequalizer_colimit T H (A D T).

Definition AbsoluteColimitCocone_AbsoluteCoequalizer@{co ch +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y} {q : C} {e : y ~> q}
  (H : e ∘ f ≈ e ∘ g) (A : AbsoluteColimitCocone (cofork_cocone f g e H)) :
  AbsoluteCoequalizer f g q e :=
  fun D T => image_colimit_coequalizer T H (A D T).

(* 相关说明。 （已译） *)

Definition split_cofork_AbsoluteColimitCocone@{co ch +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y}
  (S : SplitCoequalizer f g) :
  AbsoluteColimitCocone (cofork_cocone f g (scoeq_e S) (scoeq_law1 S)) :=
  AbsoluteCoequalizer_AbsoluteColimitCocone (scoeq_law1 S)
    (split_coequalizer_absolute S).

(* The cofork cocone of a split fork is colimiting by Mac Lane's Lemma,
   through Structure/Coequalizer.v's [is_coequalizer_cocone_ump]. *)

Definition split_coequalizer_PreservesColimitCocone@{co ch do +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y}
  (S : SplitCoequalizer f g) (D : Category@{do ch ch}) (F : C ⟶ D) :
  PreservesColimitCocone (APair f g) F :=
  AbsoluteColimitCocone_preserves
    ((fun N => is_coequalizer_cocone_ump f g
                 (split_coequalizer_is_coequalizer f g S) N)
       : IsColimitCocone (cofork_cocone f g (scoeq_e S) (scoeq_law1 S)))
    (split_cofork_AbsoluteColimitCocone S) D F.

(** ** Contractible pairs (#480) *)

(* Every coequalizer of a contractible pair is absolute: Structure/
   Coequalizer/Contractible.v's [contractible_coequalizer_split] splits
   it.  The instance is named, as for [split_coequalizer_absolute]. *)

Definition contractible_coequalizer_absolute@{co ch xo xh +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y}
  (P : ContractiblePair f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  AbsoluteCoequalizer@{co ch xo xh _} f g q e :=
  split_coequalizer_absolute (contractible_coequalizer_split P E).
