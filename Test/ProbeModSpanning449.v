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

(* A refusal expected around a name that is not there.  If the instrument
   were inert this line would pass silently and so would everything below
   it.  The message is "The reference
   zzz_no_such_constant_spanning_449 was not found in the current
   environment." *)
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

(* The three [eq_refl] readbacks of the conditional solution set, as
   controls.  [HWP] is passed EXPLICITLY throughout this file: the
   exported instance [RMod_HasWidePullbacks] would be found by resolution
   and then refused at the application, which is NEGATIVE 2. *)
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

(** ** NEGATIVE 1 (CONVERSION): the submodule round trip is not [eq_refl]

    [subobj_smod (smod_subobj S)] has the same members as [S] but is not
    the same [Type]: its membership is a sigma over the submodule's own
    carrier paired with a proof that the inclusion carries it to [a].
    Stripped and re-run in a copy of the whole file, the message is

      The term "eq_refl" has type
       "smod_mem (subobj_smod (smod_subobj S)) a =
        smod_mem (subobj_smod (smod_subobj S)) a"
      while it is expected to have type
       "smod_mem (subobj_smod (smod_subobj S)) a = smod_mem S a"
      (cannot unify "smod_mem (subobj_smod (smod_subobj S)) a" and
       "smod_mem S a")

    The control is [smod_round_iff], the inter-derivability the header
    claims and the only strength available. *)

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

(** ** POSITIVE CONTROL for NEGATIVE 2: the same application under an
       ABSTRACT wide-pullback hypothesis IS accepted

    This is Instance/Mod/Spanning.v's [tensor_solution_set] written out.
    It elaborates, so NEGATIVE 2 below is about the exported instance's
    universes and not about [spanning_solution_set] being unusable at
    [RMod R]. *)

Section AbstractHWP.

Context {R : RingObject}.
Context (V V' : RModObject R).
Context (HWP : @HasWidePullbacks (RMod R)).

Example c_solution_set_with_hypothesis :
  SolutionSet (Bilin V V') SetsOne :=
  @spanning_solution_set (RMod R) Sets (Bilin V V') HWP
    (Bilin_PreservesWidePullbacks V V') SetsOne.

End AbstractHWP.

(** ** NEGATIVE 2 (UNIVERSE): the exported wide-pullback instance does not
       discharge [spanning_solution_set]'s hypothesis

    Stripped and re-run in a copy of the whole file, the message is

      The term "RMod_HasWidePullbacks R" has type
       "HasWidePullbacks@{u_car u_car u_obj u_car}
          (RMod@{u_obj ...} R)"
      while it is expected to have type
       "HasWidePullbacks@{u_idx u_idx' u_obj' u_car}
          (RMod@{u_obj' ...} R)"
      (universe inconsistency: Cannot enforce u_car = u_idx because
       u_car < u1 <= u2 <= u_idx)

    -- the instance's index slot is the module CARRIER universe, while
    the application wants the universe [SubObj] lives at, one level up;
    the chain is three steps.  The positive control immediately above
    passes [HWP] abstractly and IS accepted. *)

Section SolutionSetRefused.

Context {R : RingObject}.
Context (V V' : RModObject R).

Fail Definition n2_exported_instance_refused :
  SolutionSet (Bilin V V') SetsOne :=
  @spanning_solution_set (RMod R) Sets (Bilin V V')
    (RMod_HasWidePullbacks R) (Bilin_PreservesWidePullbacks V V') SetsOne.

End SolutionSetRefused.

(** ** NEGATIVE 3 (UNIVERSE): the donor, one level down

    The obstruction is not the class's and not [Submodule]'s: it is
    [ProdMod]'s, whose carrier is the dependent function space
    [∀ i : I, carrier (cmon_setoid (A i))], so the index universe is at
    or below the carrier universe, while an object of [RMod R] has its
    carrier strictly below the object universe.  Indexing a [ProdMod] by
    the subobjects of a module is therefore already refused, with no
    solution set in sight.  Stripped and re-run in a copy of the whole
    file, the message is

      The term "ProdMod A" has type "RModObject R"
      while it is expected to have type "obj[RMod R]"
      (universe inconsistency: Cannot enforce u_prod = u_car because
       u_car < u1 <= u2 <= u3 <= u_prod)

    a four-step chain from the module carrier level up to the product's.
    The control is the same [ProdMod] indexed by a bare [Type], which is
    accepted. *)

Section ProdModDonor.

Context {R : RingObject}.

Example c_prodmod_at_a_type (I : Type) (A : I → obj[RMod R]) :
  obj[RMod R] := @ProdMod R I A.

Fail Definition n3_prodmod_at_subobj (W : obj[RMod R])
  (A : @SubObj (RMod R) W → obj[RMod R]) : obj[RMod R] :=
  @ProdMod R (@SubObj (RMod R) W) A.

End ProdModDonor.
