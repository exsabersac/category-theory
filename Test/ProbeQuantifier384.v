Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Props.
Require Import Category.Instance.Powerset.Quantifier.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(*
   本文件为测试：ProbeQuantifier384。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** Instrument check *)

(* [Fail] must be able to see a rejection at all.  Scope-free: no constant
   of the target occurs in it, so no rename can silence it. *)
Fail Check (probe_instrument_absent_384 : nat).

(* ------------------------------------------------------------------------ *)
(* * ** Controls: every 常值 negatives name, outside [Fail] （已译） *)

Check @Powerset_Prop_dual.
Check @Powerset_Prop_obj.
Check @Powerset_Prop_image.
Check @Powerset_Prop_preimage.
Check @DualImage.
Check @InverseImage.
Check @DirectImage.
Check @GaloisFunctor_l.
Check @GaloisFunctor_r.
Check @subset_le_preorder.
Check @preimage_dual_galois.
Check @substitution_forall_adjunction.
Check @exists_substitution_adjunction.
Check @image_preimage_adjunction.
Check @proj_exists.
Check @proj_forall.
Check @proj_fst.
Check @ProdSetoid.
Check @cylinder.
Check @cyl_reindex.
Check @quantifier_triple.
Check @forall_unit_incl.
Check @forall_counit_incl.
Check @proset_adjunction_at.
Check @gal_r_preserves_glb.
Check @gal_l_preserves_lub.
Check @carrier.
Check @is_setoid.
Check @subsets_one_Props.
Check @Delta_X.
Check @exists_X.
Check @forall_X.
Check @quant_one.
Check @quant_bang.
Check @exists_not_right_adjoint.
Check @forall_not_left_adjoint.
Check @dual_image_not_join_preserving.
Check @beck_chevalley_exists_mem.
Check @beck_chevalley_exists.

(* ------------------------------------------------------------------------ *)
(* * ** (1) The two preimage 函子 different RECORDS （已译） *)

Section GaloisFunctorRecord.

Universe o so u.
Constraint o < so.

Context {X Y : SetoidObject@{o o}}.
Context (f : X ~{Sets@{o so}}~> Y).

(* POSITIVE: 对象 actions agree nose ... （已译） *)
Example p384_fobj_agrees (T : carrier (Powerset_Prop_obj@{o} Y)) :
  fobj[GaloisFunctor_l (subset_le_preorder@{o} Y)
         (subset_le_preorder@{o} X) (preimage_dual_galois f)] T
    = fobj[InverseImage f] T := eq_refl.

(* ... and so do the arrow actions. *)
Example p384_fmap_agrees (T T' : carrier (Powerset_Prop_obj@{o} Y))
  (h : subset_le T T') :
  @fmap _ _ (GaloisFunctor_l (subset_le_preorder@{o} Y)
               (subset_le_preorder@{o} X) (preimage_dual_galois f)) T T' h
    = @fmap _ _ (InverseImage f) T T' h := eq_refl.

(* 相关说明。 （已译） *)
Fail Example p384_functor_records_agree :
  GaloisFunctor_l (subset_le_preorder@{o} Y) (subset_le_preorder@{o} X)
    (preimage_dual_galois f)
  = InverseImage f := eq_refl.

(* 相关说明。 （已译） *)
Fail Example p384_reversed_handedness :
  DualImage f ⊣ InverseImage f := substitution_forall_adjunction f.

(* POSITIVE: the pinned existential leg IS #382's adjunction. *)
Example p384_exists_leg_is_donor :
  exists_substitution_adjunction f = image_preimage_adjunction f := eq_refl.

(* 相关说明。 （已译） *)
Example p384_unit_is_incl (T : carrier (Powerset_Prop_obj@{o} Y)) :
  @unit _ _ (InverseImage f) (DualImage f)
    (substitution_forall_adjunction f) T = forall_unit_incl f T := eq_refl.

Example p384_counit_is_incl (S : carrier (Powerset_Prop_obj@{o} X)) :
  @counit _ _ (InverseImage f) (DualImage f)
    (substitution_forall_adjunction f) S = forall_counit_incl f S := eq_refl.

End GaloisFunctorRecord.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section ProjectionGrades.

Universe o so u.
Constraint o < so.

Context (U V : SetoidObject@{o o}).
Context (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))).

(* NEGATIVE 2 (CONVERSION). *)
Fail Example p384_exists_is_image_strict :
  @proj_exists@{o so} U V S
    = Powerset_Prop_image@{o} (proj_fst@{o so} U V) S := eq_refl.

(* NEGATIVE 3 (CONVERSION). *)
Fail Example p384_forall_is_dual_strict :
  @proj_forall@{o so} U V S
    = Powerset_Prop_dual@{o} (proj_fst@{o so} U V) S := eq_refl.

(* 相关说明。 （已译） *)
Check (proj_exists_is_image U V S).
Check (proj_forall_is_dual U V S).

(* 相关说明。 （已译） *)
Example p384_cylinder_is_preimage
  (Xs : carrier (Powerset_Prop_obj@{o} U)) :
  @cylinder@{o so} U V Xs
    = Powerset_Prop_preimage@{o} (proj_fst@{o so} U V) Xs := eq_refl.

End ProjectionGrades.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section BeckGrades.

Universe o so.
Constraint o < so.

Context (U U' V : SetoidObject@{o o}).
Context (g : U' ~{Sets@{o so}}~> U).
Context (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))).

(* POSITIVE: pointwise, at [eq_refl]. *)
Example p384_beck_pointwise (x : carrier U') :
  Powerset_Prop_preimage@{o} g (@proj_exists@{o so} U V S) x
    = @proj_exists@{o so} U' V
        (Powerset_Prop_preimage@{o} (cyl_reindex V g) S) x := eq_refl.

(*
   本节说明 ProbeQuantifier384 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example p384_beck_whole_subset :
  Powerset_Prop_preimage@{o} g (@proj_exists@{o so} U V S)
    = @proj_exists@{o so} U' V
        (Powerset_Prop_preimage@{o} (cyl_reindex V g) S) := eq_refl.

(* 相关说明。 （已译） *)
Check (beck_chevalley_exists_equiv U U' V g S).
Check (beck_chevalley_exists U U' V g S).

End BeckGrades.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section OmegaGrades.

Universe o so u.
Constraint o < so.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check subsets_one_Props.
Check subsets_one_Props_round.
Check Props_subsets_one_round.
Check (Subsets@{o u} quant_one@{o so}).
Check Props@{o u}.
Check (obj[Subsets@{o u} quant_one@{o so}]).
Check (obj[Props@{o u}]).

(*
   本节说明等价、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example p384_subsets_one_is_Props :
  obj[Subsets@{o u} quant_one@{o so}] = obj[Props@{o u}] := eq_refl.

End OmegaGrades.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section UniverseBoundary.

Universe po pr.
Constraint pr < po.

Context (A : SetoidObject@{po pr}).

(* POSITIVE controls at very same declared levels: 论元's
 carrier setoid structure both fine. （已译） *)
Check (carrier A).
Check (is_setoid A).
Check (A : Type@{po}).

(* NEGATIVE 6 (FORMABILITY).  [Powerset_Prop_obj@{o}] wants
   [SetoidObject@{o o}], one level for both. *)
Fail Check (Powerset_Prop_obj A).

End UniverseBoundary.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section RiehlChecks.

Universe o so u.
Constraint o < so.

Context (X : SetoidObject@{o o}).

Check (Delta_X X).
Check (exists_X X).
Check (forall_X X).
Check (riehl_exists_delta X).
Check (riehl_delta_forall X).
Check (riehl_adjoint_triple X).
Check (Delta_X_obj_mem X).

End RiehlChecks.

Check @subsets_one_to_Props.
Check @Props_to_subsets_one.
Check @subsets_one_Props_round.
Check @Props_subsets_one_round.
