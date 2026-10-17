Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Limit.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Omega.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Skeleton.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Monoidal.

Require Import Coq.Vectors.Fin.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import Category.Instance.Fun.Closed.

Generalizable All Variables.

(** * Probe for Instance/Fun/Closed.v (issue #392) *)

(*
   本文件为测试：ProbeFunClosed392。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument *)

Fail Check p392_this_name_exists_nowhere.

(** ** Controls: every target constant, named outside any negative *)

Check @ccc_point.
Check @ccc_point_inj.
Check @fun_const_point.
Check @fun_const_point_inj.
Check @fun_hom_point.
Check @fun_hom_point_inj.
Check @nodup_map_inj.
Check @fin_no_nat_injection.
Check @FinSet_is_cartesian_closed.
Check @two_map.
Check @TwoFun.
Check @alpha_fam.
Check @alpha_fam_F1.
Check @Alpha.
Check @Alpha_distinct.
Check @finset_point_eq.
Check @exp_card.
Check @alpha_index.
Check @alpha_index_inj.
Check @fun_not_cartesian_closed.
Check @fun_pointwise_not_cartesian_closed.
Check @TwoOpInitial.
Check @PObj.
Check @PMap.
Check @PresheafP.
Check @two_elt.
Check @PresheafQ.
Check @PQNat.
Check @PQNat_distinct.
Check @pq_point.
Check @pq_point_distinct.
Check @objectwise_candidate.
Check @objectwise_candidate_subsingleton.
Check @awodey_pointwise_not_exponential.

(* Donor constants a negative names, guarded outside every negative. *)
Check @Omega.
Check @FinSet.
Check @Sets.
Check @_2.
Check @Opposite.
Check @Functor_Category_Cartesian.
Check @Functor_Category_Terminal.
Check @FinSet_Cartesian.
Check @FinSet_Terminal.
Check @Sets_Cartesian.
Check @Sets_Closed.
Check @Omega_Initial.
Check @exponent_obj.
Check @le_t.
Check TwoY.

(** ** Positive readbacks the negatives are measured against *)

(*
   本节说明函子、始/终对象、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example p392_Q_at_TwoX : fobj[PresheafQ] TwoX = two_elt := eq_refl.

(* Away from their own stages, two members of the family agree by
   computation; negative 6 is the same statement AT a stage. *)
Example p392_alpha_off_stage : alpha_fam 0 3 = alpha_fam 1 3 := eq_refl.

(* The initial object of [_2^op] IS [Two_Terminal], with no transport:
   [Initial C] is notation for [@Terminal (C^op)]. *)
Example p392_TwoOpInitial : TwoOpInitial = Two_Terminal := eq_refl.

(** ** Negative 1 (FORMABILITY): the binders on [TwoFun] are
       load-bearing *)

(* The same body as the target's, written WITHOUT universe binders.
   Universe minimization then pins [Omega]'s hom and proof universes to
   the literal [Set]. *)
Program Definition TwoFunUnann : Omega ⟶ FinSet := {|
  fobj := fun _ => 2%nat;
  fmap := fun _ _ f => two_map f
|}.
Next Obligation. now destruct f. Qed.

Section P392Binders.

Universes p392o p392h p392p.
Constraint Set < p392h.

(* Control: the shipped, annotated constant elaborates at levels where
   [Omega]'s hom universe is declared strictly above [Set]. *)
Check (TwoFun : @Functor Omega@{p392o p392h p392p} FinSet).

(* Negative 1. *)
Fail Check (TwoFunUnann : @Functor Omega@{p392o p392h p392p} FinSet).

End P392Binders.

(** ** Negative 2 (FORMABILITY): the [Set] pin on the presheaf ambient *)

Section P392SetsPin.

Universes p392co p392so.
Constraint Set < p392co.
Constraint p392co < p392so.

(* Controls: both factors exist separately at these levels. *)
Check (Sets@{p392co p392so}).
Check (_2^op).

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check ([_2^op, Sets@{p392co p392so}]).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check ([Omega@{p392co p392co p392co}, Sets@{p392co p392so}]).

End P392SetsPin.

(** ** Negative 3 (CONVERSION): the two presheaves differ at [TwoY] *)

Fail Definition p392_n3
  : fobj[PresheafP] TwoY = fobj[PresheafQ] TwoY := eq_refl.

(** ** Negative 4 (CONVERSION): the objectwise candidate is not the
       two-element setoid *)

(*
   本节说明 ProbeFunClosed392 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition p392_n4
  : @exponent_obj Sets Sets_Cartesian Sets_Closed
      (fobj[PresheafP] TwoY) (fobj[PresheafQ] TwoY) = two_elt := eq_refl.

(** ** Negative 5 (TYPING): the headline is about [Omega, FinSet] *)

(* Control: the headline accepts the pointwise cartesian structure on
   its own functor category. *)
Check (fun_not_cartesian_closed
         (Functor_Category_Cartesian Omega FinSet FinSet_Cartesian)).

(* Negative 5: and not one on a different functor category. *)
Fail Check (fun_not_cartesian_closed
              (Functor_Category_Cartesian (_2^op) Sets Sets_Cartesian)).

(** ** Negative 6 (CONVERSION): [alpha_fam] separates at its stage *)

Fail Definition p392_n6 : alpha_fam 0 1 = alpha_fam 1 1 := eq_refl.

(** ** Negative 7 (TYPING): the engine's second half is about the
       terminal object *)

(* Control: the constant exists and is applicable at these arguments. *)
Check (@fun_const_point Omega FinSet Omega_Initial FinSet_Terminal).

(* Negative 7: its argument must be a transformation OUT OF the
   pointwise terminal functor; an endotransformation of [TwoFun] is not
   one. *)
Fail Check (@fun_const_point Omega FinSet Omega_Initial FinSet_Terminal
              TwoFun (Alpha 0)).
