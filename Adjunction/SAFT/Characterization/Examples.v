Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Hom.Limit.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Instance.Adjoints.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Sets.WellPowered.
Require Import Category.Instance.Sets.Cogenerator.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Powerset.WellPowered.
Require Import Category.Adjunction.GAFT.Sets.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.SAFT.Sets.
Require Import Category.Adjunction.SAFT.WellPowered.
Require Import Category.Adjunction.SAFT.InitialObject.Examples.
Require Import Category.Adjunction.SAFT.Characterization.
Require Import Category.Adjunction.SAFT.Characterization.Cover.
Require Import Category.Adjunction.SAFT.Characterization.Corollaries.

Generalizable All Variables.

(** * The special adjoint functor theorem at [Sets], [Subsets] and [Indiscrete] *)

(*
   nLab:      https://ncatlab.org/nlab/show/well-powered+category

   本文件给出例子。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** [Sets] under [Untruncate]: the identity *)

Definition sets_id_saft@{o so +| Set < o, o < so +} (Un : Untruncate@{o}) :
  { F : Sets@{o so} ⟶ Sets@{o so} & F ⊣ @Id Sets@{o so} } :=
  SAFT_wellpowered (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit
    (Sets_Cogenerator_untruncate Un) (Sets_WellPowered_untruncate Un).

(* The same tuple through the GAFT route. *)
Definition sets_id_saft_cover@{o so +| Set < o, o < so +} (Un : Untruncate@{o}) :
  { F : Sets@{o so} ⟶ Sets@{o so} & F ⊣ @Id Sets@{o so} } :=
  SAFT_cover_wp (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit
    (Sets_Cogenerator_untruncate Un) (Sets_WellPowered_untruncate Un).

(** ** The separation: one tuple, the new cover inhabited, the old refuted *)

Definition sets_id_new_cover@{o so t +| Set < o, o < so, o < t +}
  (Un : Untruncate@{o}) (d : Sets@{o so}) :=
  saft_cover_at (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit
    (Sets_Cogenerator_untruncate Un) d
    (Sets_WellPowered_untruncate@{o so t} Un _).

Definition sets_id_old_cover_refuted@{o so t +| Set < o, o < so, o < t +}
  (Un : Untruncate@{o}) :=
  SubobjectCover_Id_Sets_absurd Sets_Complete (Sets_Cogenerator_untruncate Un)
    (WellPowered_SubobjectIndex (Sets_WellPowered_untruncate@{o so t} Un)).

(* Both halves in one statement, so that "the same completeness, cogenerator
   and well-powering" is read off the type. *)
Definition sets_id_cover_separation@{o so t +| Set < o, o < so, o < t +}
  (Un : Untruncate@{o}) :
  (∀ d : Sets@{o so},
     SubobjectCoverAt (@Id Sets@{o so}) Sets_Complete
       (Sets_Cogenerator_untruncate Un) d
       (Sets_WellPowered_untruncate@{o so t} Un _))
  * (SubobjectCover (@Id Sets@{o so}) Sets_Complete
       (Sets_Cogenerator_untruncate Un)
       (WellPowered_SubobjectIndex (Sets_WellPowered_untruncate@{o so t} Un))
     → False) :=
  (sets_id_new_cover Un, sets_id_old_cover_refuted Un).

(** ** [Sets] under [Untruncate]: a hom functor *)

Definition sets_hom_saft@{o so +| Set < o, o < so +} (Un : Untruncate@{o})
  (A : Sets@{o so}) :
  { F : Sets@{o so} ⟶ Sets@{o so} & F ⊣ @HomFrom Sets@{o so} A } :=
  SAFT_wellpowered (@HomFrom Sets@{o so} A) Sets_Complete
    (Continuous_PreservesImageLimit (hom_ContinuousFunctor A))
    (Sets_Cogenerator_untruncate Un) (Sets_WellPowered_untruncate Un).

(** ** The corollaries at [Sets] under [Untruncate] *)

Definition sets_id_repr_saft@{o so +| Set < o, o < so +} (Un : Untruncate@{o}) :
  Representable (@Id Sets@{o so}) :=
  continuous_Set_functor_representable (@Id Sets@{o so}) Sets_Complete
    Sets_Id_PreservesImageLimit (Sets_Cogenerator_untruncate Un)
    (Sets_WellPowered_untruncate Un).

Definition sets_hom_repr_saft@{o so +| Set < o, o < so +} (Un : Untruncate@{o})
  (A : Sets@{o so}) : Representable (@HomFrom Sets@{o so} A) :=
  continuous_Set_functor_representable (@HomFrom Sets@{o so} A) Sets_Complete
    (Continuous_PreservesImageLimit (hom_ContinuousFunctor A))
    (Sets_Cogenerator_untruncate Un) (Sets_WellPowered_untruncate Un).

Definition sets_saft_cocomplete@{o so +| Set < o, o < so +}
  (Un : Untruncate@{o}) : @Cocomplete Sets@{o so} :=
  saft_cocomplete Sets_Complete (Sets_Cogenerator_untruncate Un)
    (Sets_WellPowered_untruncate Un).

(** ** Thin and unconditional: the powerset lattices *)

Definition subsets_inverse_image_saft@{o so u +| Set < o, o < so, o <= u +}
  {X Y : SetoidObject@{o o}} (f : X ~{Sets@{o so}}~> Y) :
  { F : Subsets@{o u} X ⟶ Subsets@{o u} Y & F ⊣ InverseImage f } :=
  SAFT_wellpowered (InverseImage f) (Subsets_Complete_free Y)
    (right_adjoint_PreservesImageLimit (image_preimage_adjunction f))
    (Subsets_Cogenerator_empty Y) (Subsets_WellPowered Y).

(* Mac Lane's Theorem 2 at the same functor: every premise is inhabited,
   the wide pullbacks by [Complete_HasSubobjectWidePullbacks].  CIRCULAR:
   both preservation premises are read off [image_preimage_adjunction f],
   the adjunction whose left adjoint the theorem then builds, so this
   shows the premises satisfiable together, not a new adjoint. *)
Definition subsets_inverse_image_thm2@{o so u +| Set < o, o < so, o <= u +}
  {X Y : SetoidObject@{o o}} (f : X ~{Sets@{o so}}~> Y) :
  { F : Subsets@{o u} X ⟶ Subsets@{o u} Y & F ⊣ InverseImage f } :=
  SAFT_thm2 (InverseImage f) (Subsets_Complete_free Y)
    (right_adjoint_PreservesImageLimit (image_preimage_adjunction f))
    (Subsets_Cogenerator_empty Y)
    (Complete_HasSubobjectWidePullbacks (Subsets_Complete_free Y))
    (right_adjoint_PreservesWidePullbacks (image_preimage_adjunction f)).

Definition subsets_saft_cocomplete@{o u +| Set < o, o <= u +}
  (X : SetoidObject@{o o}) : @Cocomplete (Subsets@{o u} X) :=
  saft_cocomplete (Subsets_Complete_free X) (Subsets_Cogenerator_empty X)
    (Subsets_WellPowered X).

(** ** Degenerate and unconditional: an indiscrete category *)

(* Objects the types of [Type@{j}], one universe above the homs; the
   well-powering is indexed at [Set], strictly below the homs. *)
Definition indiscrete_saft@{j o +| j < o +} :
  { F : Indiscrete@{o j j} Type@{j} ⟶ Indiscrete@{o j j} Type@{j}
    & F ⊣ @Id (Indiscrete@{o j j} Type@{j}) } :=
  SAFT_wellpowered (@Id (Indiscrete@{o j j} Type@{j}))
    (Indiscrete_Complete (Datatypes.unit : Type@{j}))
    (right_adjoint_PreservesImageLimit
       (@adj_id (Indiscrete@{o j j} Type@{j})))
    (Indiscrete_Cogenerator_empty Type@{j})
    (Indiscrete_WellPowered@{o j Set o _} Type@{j}).

Definition indiscrete_saft_cocomplete@{j o +| j < o +} :
  @Cocomplete (Indiscrete@{o j j} Type@{j}) :=
  saft_cocomplete (Indiscrete_Complete (Datatypes.unit : Type@{j}))
    (Indiscrete_Cogenerator_empty Type@{j})
    (Indiscrete_WellPowered@{o j j o _} Type@{j}).

(** ** What the constructed adjoints are, up to isomorphism *)

(* At [Id] the left adjoint is the identity, by uniqueness of adjoints. *)
Definition sets_id_saft_iso@{o so +| Set < o, o < so +} (Un : Untruncate@{o}) :
  projT1 (sets_id_saft Un) ≈ @Id Sets@{o so} :=
  left_adjoint_iso (@Id Sets@{o so}) _ _ (projT2 (sets_id_saft Un)) adj_id.

(* At [InverseImage f] it is the direct image. *)
Definition subsets_inverse_image_saft_iso@{o so u +| Set < o, o < so, o <= u +}
  {X Y : SetoidObject@{o o}} (f : X ~{Sets@{o so}}~> Y) :
  projT1 (subsets_inverse_image_saft f
            : { F : Subsets@{o u} X ⟶ Subsets@{o u} Y
              & F ⊣ InverseImage@{o so u} f })
    ≈ DirectImage@{o so u} f :=
  left_adjoint_iso (InverseImage@{o so u} f) _ _
    (projT2 (subsets_inverse_image_saft f))
    (image_preimage_adjunction f).
