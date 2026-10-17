(*
   本文件为测试：ProbeFinSetLimit415。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Topos.
Require Import Category.Structure.Topos.Monadic.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Sets.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Limit.
Require Import Category.Instance.FinSet.Topos.
Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe415_absent_name.

(** ** A: the pullback route does not compute; the native route does *)

Definition p415_HasEqualizers_pb : HasEqualizers FinSet :=
  @HasEqualizers_of_HasPullbacks_Terminal FinSet FinSet_Terminal
    FinSet_Pullbacks.

Definition p415_FinitelyComplete_pb : @FinitelyComplete FinSet :=
  finitely_complete_of_pullbacks_terminal FinSet_Pullbacks FinSet_Terminal.

(* the topos-derived equalizer of FinSet IS the pullback-route term *)
Example p415_topos_route_is_pullback_route :
  @topos_HasEqualizers FinSet FinSet_Topos = p415_HasEqualizers_pb
  := eq_refl.

(* control: the native equalizer object at the example pair is [2] *)
Example p415_native_obj :
  `1 (@equalizer FinSet FinSet_HasEqualizers _ _
        finset_eq_example_f finset_eq_example_g) = 2%nat
  := eq_refl.

(* N1 CONVERSION *)
Fail Example p415_pb_obj :
  `1 (@equalizer FinSet p415_HasEqualizers_pb _ _
        finset_eq_example_f finset_eq_example_g) = 2%nat
  := eq_refl.

(* control: the native terminal object from the empty finite limit is [1] *)
Example p415_native_terminal :
  @terminal_obj FinSet (FinitelyComplete_Terminal FinSet_FinitelyComplete)
  = 1%nat
  := eq_refl.

(* N2 CONVERSION *)
Fail Example p415_pb_terminal :
  @terminal_obj FinSet (FinitelyComplete_Terminal p415_FinitelyComplete_pb)
  = 1%nat
  := eq_refl.

(* control: the two apexes agree up to isomorphism, by uniqueness *)
Definition p415_terminals_iso :
  @terminal_obj FinSet (FinitelyComplete_Terminal p415_FinitelyComplete_pb)
  ≅ @terminal_obj FinSet (FinitelyComplete_Terminal FinSet_FinitelyComplete)
  := terminal_unique (FinitelyComplete_Terminal p415_FinitelyComplete_pb)
                     (FinitelyComplete_Terminal FinSet_FinitelyComplete).

(** ** B: typing *)

(* N3 TYPING *)
Fail Check (FinSet_HasEqualizers : HasEqualizers Sets).

(* N4 TYPING *)
Fail Check (FinSet_FinitelyComplete : @Complete FinSet).

(* control: completeness would imply finite completeness *)
Check (@Complete_FinitelyComplete FinSet
       : @Complete FinSet → @FinitelyComplete FinSet).

(** ** C: universe *)

(* control *)
Check FinSet_HasEqualizers@{_ _ _ _ _}.

(* N5 UNIVERSE *)
Fail Check FinSet_HasEqualizers@{_ _ Set _ _}.

(** ** D: readbacks *)

Section Readbacks.
  Context {m n : nat} (f g : Fin.t m → Fin.t n).

  Example p415_obj_readback :
    `1 (@equalizer FinSet FinSet_HasEqualizers m n f g)
    = FinSet_equalizer_obj f g
    := eq_refl.

  Example p415_incl_readback :
    `1 (`2 (@equalizer FinSet FinSet_HasEqualizers m n f g))
    = FinSet_equalizer_incl f g
    := eq_refl.

  Example p415_ump_readback :
    `2 (`2 (@equalizer FinSet FinSet_HasEqualizers m n f g))
    = FinSet_IsEqualizer f g
    := eq_refl.

  (* the inclusion is a fork, at the setoid of FinSet *)
  Example p415_fork :
    f ∘[FinSet] FinSet_equalizer_incl f g
    ≈ g ∘[FinSet] FinSet_equalizer_incl f g
    := fork_eq (FinSet_IsEqualizer f g).
End Readbacks.

Example p415_finitely_complete_readback :
  FinSet_FinitelyComplete
  = finitely_complete_from_generators FinSet_Terminal FinSet_Cartesian
      FinSet_HasEqualizers
  := eq_refl.

(* a pair that never agrees has the empty equalizer *)
Example p415_disjoint :
  FinSet_equalizer_obj (fun _ : Fin.t 2 => (Fin.F1 : Fin.t 2))
                       (fun _ => Fin.FS Fin.F1) = 0%nat
  := eq_refl.

(* a pair of equal maps has the whole source as equalizer *)
Example p415_equal_maps :
  FinSet_equalizer_obj finset_eq_example_f finset_eq_example_f = 3%nat
  := eq_refl.

(** ** Guard block *)

Check @finset_eq_pred.
Check @FinSet_equalizer_obj.
Check @FinSet_equalizer_incl.
Check @finset_eq_pred_true.
Check @FinSet_equalizer_med.
Check @FinSet_IsEqualizer.
Check @FinSet_HasEqualizers.
Check @FinSet_FinitelyComplete.
Check @finset_eq_example_f.
Check @finset_eq_example_g.
Check @finset_eq_example_h.
Check @finset_eq_example_diagram.
Check @FinSet_FinitelyComplete_terminal_computes.
Check @FinSet_FinitelyComplete_parallel_computes.
Check @p415_HasEqualizers_pb.
Check @p415_FinitelyComplete_pb.
Check @HasEqualizers_of_HasPullbacks_Terminal.
Check @finitely_complete_of_pullbacks_terminal.
Check @FinitelyComplete_Terminal.
Check @Complete_FinitelyComplete.
Check @terminal_unique.
Check @Sets.
