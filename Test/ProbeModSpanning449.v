Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Universal.Element.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Construction.Elements.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.SpanningArrow.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Mod.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Product.
Require Import Category.Instance.Mod.Representable.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Instance.Mod.Quotient.Isomorphism.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Mod.Bimodule.
Require Import Category.Instance.Mod.Spanning.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

(*
   本文件为测试：ProbeModSpanning449。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check *)

(*
   本节说明 ProbeModSpanning449 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check zzz_no_such_constant_spanning_449.

(** ** Positive controls: every library constant a negative names *)

Section Controls.

Context {R : RingObject}.
Context (V V' : RModObject R).

Check (RMod R).
Check (Bilin V V').
Check (RMod_HasWidePullbacks R).
Check (RMod_WidePullback (R:=R)).
Check (Bilin_PreservesWidePullbacks V V').
Check SetsOne.
Check (@SolutionSet (RMod R) Sets (Bilin V V')).
Check (@SpanningArrowsOutOf (RMod R) Sets (Bilin V V') SetsOne).
Check (@spanning_solution_set (RMod R) Sets (Bilin V V')).
Check (@ProdMod R).
Check (@SubObj (RMod R)).
Check (@sub_mono (RMod R)).
Check (@sub_dom (RMod R)).
Check (@Submodule R).
Check (@smod_mem R).
Check (@smod_subobj R).
Check (@subobj_smod R).
Check (@smod_round_iff R).
Check (@smod_round_to R).
Check (@smod_round_from R).
Check (@SubGenMod R).
Check (@rbilinear_spanning_iff R).
Check (@tensor_gen_spanning_categorical R).

(*
   本节说明 ProbeModSpanning449 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example c_esol_index (HWP : @HasWidePullbacks (RMod R)) :
  esol_index (@tensor_esols R V V' HWP)
    = SpanningArrowsOutOf (Bilin V V') SetsOne := eq_refl.

Example c_esol_obj (HWP : @HasWidePullbacks (RMod R))
  (i : SpanningArrowsOutOf (Bilin V V') SetsOne) :
  esol_obj (@tensor_esols R V V' HWP) i = `1 i := eq_refl.

Example c_esol_elem (HWP : @HasWidePullbacks (RMod R))
  (i : SpanningArrowsOutOf (Bilin V V') SetsOne) :
  esol_elem (@tensor_esols R V V' HWP) i = `1 (`2 i) ttt := eq_refl.

(* The two [eq_refl] readbacks of the submodule/subobject bridge that DO
   hold, as the controls NEGATIVE 1 sits beside. *)
Example c_subobj_dom (W : RModObject R) (S : Submodule W) :
  sub_dom (smod_subobj S) = SubmoduleMod S := eq_refl.

Example c_subobj_mono (W : RModObject R) (S : Submodule W) :
  sub_mono (smod_subobj S) = smod_incl S := eq_refl.

End Controls.

(*
   本节说明 ProbeModSpanning449 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section RoundTrip.

Context {R : RingObject}.
Context {W : RModObject R}.
Context (S : Submodule W).
Context (a : carrier (cmon_setoid W)).

Example c_round_iff : smod_mem (subobj_smod (smod_subobj S)) a
                        ↔ smod_mem S a := smod_round_iff S a.

Fail Example n1_round_trip_not_definitional :
  smod_mem (subobj_smod (smod_subobj S)) a = smod_mem S a := eq_refl.

End RoundTrip.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section AbstractHWP.

Context {R : RingObject}.
Context (V V' : RModObject R).
Context (HWP : @HasWidePullbacks (RMod R)).

Example c_solution_set_with_hypothesis :
  SolutionSet (Bilin V V') SetsOne :=
  @spanning_solution_set (RMod R) Sets (Bilin V V') HWP
    (Bilin_PreservesWidePullbacks V V') SetsOne.

End AbstractHWP.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SolutionSetRefused.

Context {R : RingObject}.
Context (V V' : RModObject R).

Fail Definition n2_exported_instance_refused :
  SolutionSet (Bilin V V') SetsOne :=
  @spanning_solution_set (RMod R) Sets (Bilin V V')
    (RMod_HasWidePullbacks R) (Bilin_PreservesWidePullbacks V V') SetsOne.

End SolutionSetRefused.

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ProdModDonor.

Context {R : RingObject}.

Example c_prodmod_at_a_type (I : Type) (A : I → obj[RMod R]) :
  obj[RMod R] := @ProdMod R I A.

Fail Definition n3_prodmod_at_subobj (W : obj[RMod R])
  (A : @SubObj (RMod R) W → obj[RMod R]) : obj[RMod R] :=
  @ProdMod R (@SubObj (RMod R) W) A.

End ProdModDonor.
