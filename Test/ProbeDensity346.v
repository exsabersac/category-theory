Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Elements.
Require Import Category.Construction.Elements.Kan.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Density.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本文件为测试：ProbeDensity346。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ProbeDensityConversion.

Context {C : Category}.
Context (P : C^op ⟶ Sets).

(* CONTROL: presheaf diagram nameable agrees 对象. （已译） *)
Check @PDensityDiagram.
Check (fun (c : C) (x : P c) =>
         PDensityDiagram P ((c; x) : PElements P)).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example probe_pdd_records :
  PDensityDiagram P = Curried_CoHom C ◯ PElements_proj P := eq_refl.

End ProbeDensityConversion.

Section ProbeDensityMediator.

Context {D : Category}.
Context (K : D ⟶ Sets).

(* 相关说明。 （已译） *)
Check @DensityDiagram.
Check @ElementsOp.
Check @density.
Example probe_ctrl_diag :
  DensityDiagram K = Curried_Hom D ◯ (Elements_proj K)^op := eq_refl.
Definition probe_ctrl_commutes (M : Cocone (DensityDiagram K))
  (j : ElementsOp K) :
  density_med K M ∘ density_inj K j ≈ cocone_inj M j
  := density_med_commutes K M j.

(*
   本节说明 ProbeDensity346 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example probe_med_strict (M : Cocone (DensityDiagram K))
  (j : ElementsOp K) :
  density_med K M ∘ density_inj K j = cocone_inj M j := eq_refl.

(* CONTROL negative 3: 复合 IS formable OPPOSITE of
 projection, what diagram uses. （已译） *)
Check (Curried_Hom D ◯ (Elements_proj K)^op).

(* NEGATIVE 3, TYPING -- the variance.  The diagram of representables
   cannot be indexed by [Elements K] covariantly, because [d ↦ [Hom d,─]]
   is contravariant.  Stripped: "Elements_proj K has type
   Elements K ⟶ D while it is expected to have type Elements K ⟶ D^op". *)
Fail Check (Curried_Hom D ◯ Elements_proj K).

End ProbeDensityMediator.

Section ProbeDensityUniverse.

Universe uo uh us.
Constraint uh < uo.
Constraint uh < us.

(*
   本节说明Yoneda相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) => ElementsOp K).
Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) => @yo_inj D K).

(*
   本节说明 ProbeDensity346 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) =>
              DensityDiagram K).

End ProbeDensityUniverse.

(* 相关说明。 （已译） *)
Fail Fail Check @density.
