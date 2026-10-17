Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Span.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Limit.
Require Import Category.Structure.Pushout.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Morphisms.CokernelPair.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Adjunction.Diagonal.Finite.

Generalizable All Variables.

(*
   本文件为测试：ProbeDiagonalFinite354。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)
Fail Fail Check Category.

(*
   本节说明伴随、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FiniteConversion.
Context {C : Category} (L : HasLimitsOfShape Parallel C).
Context (M : HasColimitsOfShape Parallel C).

(* NEGATIVE 1 — the equalizing arrow. *)
Fail Definition probe_eq_arrow (F : Parallel ⟶ C) :
  eq_arrow L F = lim_leg L F ParX := eq_refl.

(* CONTROL 1. *)
Definition probe_eq_arrow_id (F : Parallel ⟶ C) :
  eq_arrow L F = lim_leg L F ParX ∘ id := eq_refl.

(* NEGATIVE 2 — the coequalizing arrow, dual residue. *)
Fail Definition probe_coeq_arrow (F : Parallel ⟶ C) :
  coeq_arrow M F = colim_inj M F ParY := eq_refl.

(* 相关说明。 （已译） *)
Definition probe_coeq_arrow_id (F : Parallel ⟶ C) :
  coeq_arrow M F = id ∘ colim_inj M F ParY := eq_refl.

End FiniteConversion.

Section FiniteConversionRoof.
Context {C : Category} (P : HasLimitsOfShape (Opposite Roof) C).
Context (Q : HasColimitsOfShape Roof C).

(* NEGATIVE 3 — the pullback's first projection. *)
Fail Definition probe_pb_fst (F : Opposite Roof ⟶ C) :
  pb_fst P F = lim_leg P F RNeg := eq_refl.

(* CONTROL 3. *)
Definition probe_pb_fst_id (F : Opposite Roof ⟶ C) :
  pb_fst P F = lim_leg P F RNeg ∘ id := eq_refl.

(* NEGATIVE 4 — the pushout's first injection. *)
Fail Definition probe_po_in1 (F : Roof ⟶ C) :
  pushout_inj1 Q F = colim_inj Q F RNeg := eq_refl.

(* CONTROL 4. *)
Definition probe_po_in1_id (F : Roof ⟶ C) :
  pushout_inj1 Q F = id ∘ colim_inj Q F RNeg := eq_refl.

End FiniteConversionRoof.

(*
   本节说明 ProbeDiagonalFinite354 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UnitTyping.
Context {C : Category} (L : HasLimitsOfShape Parallel C) (x : C).

(*
   本节说明 ProbeDiagonalFinite354 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe_unit_is_id : dia_unit L x = id[x] := eq_refl.

(* CONTROL 5: unit IS nameable well-typed at real type, so the
 negative about 恒等, not about `dia_unit`. （已译） *)
Check (dia_unit L x).

End UnitTyping.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* NEGATIVE 6. *)
Fail Definition probe_roof_op : Opposite Roof = Roof := eq_refl.

(* NEGATIVE 7. *)
Fail Definition probe_parallel_op : Opposite Parallel = Parallel := eq_refl.

(* 相关说明。 （已译） *)
Check Roof.
Check Parallel.
Check (Opposite Roof).
Check (Opposite Parallel).

(*
   本节说明（余）极限、hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FormabilityHomProof.
Universes uo uh up.
Constraint uh < up.
Context (Cu : Category@{uo uh up}).

(* CONTROLS accepted hom 证明 declared strictly apart. （已译） *)
Check (fun x y : Cu => x ~{Cu}~> y).
Check (obj[Cu]).
Check (fun x : Cu => id[x]).

(* 相关说明。 （已译） *)
Check (@Cone Parallel Cu).

(*
   本节说明 ProbeDiagonalFinite354 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (@Limit Parallel Cu).
Fail Check (Opposite Cu).
Fail Check (@IsEqualizer Cu).
Fail Check (@IsPullback Cu).
Fail Check (@HasLimitsOfShape Parallel Cu).
Fail Check (@Diagonal Cu Parallel).
Fail Check ([Parallel, Cu]).
Fail Check (@IsCoequalizer Cu).
Fail Check (@IsPushoutSquare Cu).

End FormabilityHomProof.

(* * ** Controls naming every 常值 negatives depend on, OUTSIDE a
 [Fail], so rename breaks succeeding command rather than turning a
 negative vacuously green. （已译） *)

Check @eq_arrow.
Check @coeq_arrow.
Check @pb_fst.
Check @pb_snd.
Check @pushout_inj1.
Check @pushout_inj2.
Check @dia_unit.
Check @dia_counit.
Check @lim_leg.
Check @colim_inj.
Check @HasLimitsOfShape.
Check @HasColimitsOfShape.
Check @Limit.
Check @IsEqualizer.
Check @IsCoequalizer.
Check @IsPullback.
Check @IsPushoutSquare.
Check @Opposite.

Check @EqualizerFunctor.
Check @CoequalizerFunctor.
Check @PullbackFunctor.
Check @PushoutFunctor.
Check @Diagonal_Equalizer_Adjunction.
Check @Coequalizer_Diagonal_Adjunction.
Check @Diagonal_Pullback_Adjunction.
Check @Pushout_Diagonal_Adjunction.
Check @eq_counit_IsEqualizer.
Check @coeq_unit_IsCoequalizer.
Check @pb_counit_IsPullback.
Check @po_unit_IsPushoutSquare.
Check @ShapeLinked.
Check @dia_unit_iso.
Check @dia_counit_iso.
Check @Parallel_linked.
Check @Roof_linked.
