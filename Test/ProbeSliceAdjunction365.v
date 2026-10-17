Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Slice.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cocartesian.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Slice.Adjunction.
Require Import Category.Instance.Cat.Pullback.

Generalizable All Variables.

(* Boundary probe for Construction/Slice/Adjunction.v (issue #365). *)

(*
   本文件为测试：ProbeSliceAdjunction365。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Fail Check (1 = true).

(* * ** Kind 1 — FORMABILITY: hom 证明 universes cannot split （已译） *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UniverseBoundary.

Universes uo uh up.
Constraint uh < up.

Context (Cu : Category@{uo uh up}).
Context (xu yu : Cu).

(* Controls: 范畴, hom-sets identities all elaborate
 two levels declared strictly apart. （已译） *)
Check Cu.
Check (xu ~> yu).
Check (id[xu]).

(* Negative 1 (formability): the slice construction. *)
Fail Check (@Slice Cu xu).

(* Negative 2 (formability): the coslice construction. *)
Fail Check (@Coslice Cu xu).

(* Negative 3 (formability): cartesian class -- hence also
 [Cocartesian], class read at opposite 范畴. （已译） *)
Fail Check (@Cartesian Cu).

(* Negative 4 (formability): the object-level terminality predicate. *)
Fail Check (@IsTerminalObj Cu xu).

(* Negative 5 (formability): its initial dual. *)
Fail Check (@IsInitialObj Cu xu).

(* Negative 6 (formability): target's own projection 函子, which
 inherits identification [Coslice] adds nothing. （已译） *)
Fail Check (@Coslice_Proj Cu xu).

End UniverseBoundary.

(** ** Kind 2 — CONVERSION *)

Section Conversion.

Context {C : Category}.
Context {CC : @Cocartesian C}.
Context {CA : @Cartesian C}.
Context (a : C).

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example ctrl_unit_residue (c : C) :
  @unit (@Coslice C a) C (Coslice_Coprod a) (Coslice_Proj a)
    (Coslice_Projection_Adjunction a) c
    = id ∘ @coslice_projection_unit C CC a c := eq_refl.

Check @coslice_unit_strict.
Check @coslice_unit_is_inr.
Check @coslice_projection_unit.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example neg_unit_is_inr (c : C) :
  @unit (@Coslice C a) C (Coslice_Coprod a) (Coslice_Proj a)
    (Coslice_Projection_Adjunction a) c
    = @coslice_projection_unit C CC a c := eq_refl.

(* Controls negative 8: slice counit carries 镜像-image
 residue, OTHER side. （已译） *)
Example ctrl_counit_residue (y : C) :
  @counit C (@Slice C a) (Slice_Proj a) (Slice_Prod a)
    (Slice_Projection_Adjunction a) y
    = @slice_projection_counit C CA a y ∘ id := eq_refl.

Check @slice_counit_strict.
Check @slice_counit_is_exl.
Check @slice_projection_counit.

(*
   本节说明 ProbeSliceAdjunction365 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example neg_counit_is_exl (y : C) :
  @counit C (@Slice C a) (Slice_Proj a) (Slice_Prod a)
    (Slice_Projection_Adjunction a) y
    = @slice_projection_counit C CA a y := eq_refl.

End Conversion.

Section Orientation.

Context {C : Category}.
Context (a : C).

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example ctrl_orientation_objects :
  obj[@Coslice C a] = obj[Opposite (@Slice (Opposite C) a)] := eq_refl.

Check @Coslice.
Check @Slice.
Check @Opposite.

(*
   本节说明始/终对象、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example neg_coslice_is_op_slice :
  @Coslice C a = Opposite (@Slice (Opposite C) a) := eq_refl.

End Orientation.

Section PriorArt.

Context {C : Category}.
Context (a : C).

(*
   本节说明函子、拉回/推出、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example ctrl_coslice_proj_fobj (x : @Coslice C a) :
  fobj[@Coslice_Proj C a] x = fobj[@Coslice_proj C a] x := eq_refl.

Example ctrl_coslice_proj_fmap (x y : @Coslice C a)
  (f : x ~{@Coslice C a}~> y) :
  fmap[@Coslice_Proj C a] f = fmap[@Coslice_proj C a] f := eq_refl.

Example ctrl_slice_proj_fobj (x : @Slice C a) :
  fobj[@Slice_Proj C a] x = fobj[@Slice_proj C a] x := eq_refl.

Example ctrl_slice_proj_fmap (x y : @Slice C a)
  (f : x ~{@Slice C a}~> y) :
  fmap[@Slice_Proj C a] f = fmap[@Slice_proj C a] f := eq_refl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example neg_coslice_proj_record :
  @Coslice_Proj C a = @Coslice_proj C a := eq_refl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition p365_via_comma : @Coslice C a ⟶ C :=
  comma_proj2 ◯ to (Comma_Coslice C a).

Check @p365_via_comma.
Check @comma_proj2.
Check @Comma_Coslice.

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example neg_via_comma_fobj (x : @Coslice C a) :
  fobj[p365_via_comma] x = `1 x := eq_refl.

End PriorArt.

(** ** Kind 3 — TYPING *)

Section Typing.

Context {C : Category}.
Context {CC : @Cocartesian C}.
Context (a : C).

(* Control: 伴随 has handedness exercise asks --
 coproduct 函子 LEFT, projection RIGHT. （已译） *)
Check (@Coslice_Projection_Adjunction C CC a
         : Coslice_Coprod a ⊣ Coslice_Proj a).

Check @Coslice_Coprod.
Check @Coslice_Projection_Adjunction.

(* 相关说明。 （已译） *)
Fail Check (@Coslice_Projection_Adjunction C CC a
              : Coslice_Proj a ⊣ Coslice_Coprod a).

End Typing.

(* * ** Controls naming every remaining delivered 常值 （已译） *)

Check @Cartesian.
(* [Cocartesian] is a NOTATION (Structure/Cocartesian.v), not a
   constant, so [Check @Cocartesian.] does not parse -- it reports a
   missing [term] after '@Cocartesian'.  It is named instead by the
   [Context {CC : @Cocartesian C}] lines above, which are succeeding
   commands and serve as its control. *)
Check @IsTerminalObj.
Check @IsInitialObj.
Check @unit.
Check @counit.
Check @Coslice_proj.
Check @Slice_proj.
Check @Coslice_Proj.
Check @Slice_Proj.
Check @Slice_Prod.
Check @Slice_Projection_Adjunction.
Check @coslice_fmap_is_cover.
Check @slice_fmap_is_split.
Check @coslice_transpose.
Check @slice_transpose.
Check @coslice_adj.
Check @slice_adj.
Check @coslice_projection_counit.
Check @slice_projection_unit.
Check @coslice_counit_strict.
Check @coslice_counit_is_merge.
Check @slice_unit_strict.
Check @slice_unit_is_fork.
Check @slice_id_obj.
Check @coslice_id_obj.
Check @slice_id_IsTerminalObj.
Check @coslice_id_IsInitialObj.
Check @slice_left_adjoint_terminal.
Check @slice_terminal_left_adjoint.
Check @slice_terminal_left_adjoint_adj.
Check @slice_proj_left_adjoint_iff_terminal.
Check @coslice_right_adjoint_initial.
Check @coslice_initial_right_adjoint.
Check @coslice_initial_right_adjoint_adj.
Check @coslice_proj_right_adjoint_iff_initial.
Check @Sets_Coslice_Projection_Adjunction.
Check @Sets_Slice_Projection_Adjunction.
Check @sets_bipoint.
Check @sets_bipoint_l.
Check @sets_bipoint_r.
Check @sets_bipoint_distinct.
Check @sets_point.
Check @sets_bipoint_const.
Check @sets_bipoint_not_terminal.
Check @sets_bipoint_not_initial.
Check @sets_slice_proj_no_left_adjoint.
Check @sets_coslice_proj_no_right_adjoint.
Check @sets_slice_proj_left_adjoint_at_terminal.
Check @sets_coslice_proj_right_adjoint_at_initial.
Check @sets_coslice_transpose_computes.
Check @sets_slice_transpose_is_fork.
Check @sets_slice_transpose_computes.
Check @sets_coslice_unit_not_iso.
Check @slice_terminal_adj.
Check @coslice_initial_adj.
Check @coslice_adj_to.
Check @coslice_adj_from.
Check @slice_adj_to.
Check @slice_adj_from.
