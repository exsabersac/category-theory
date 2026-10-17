Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pushout.Split.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Pushout.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Coproduct.
Require Import Category.Instance.Top.Pushout.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本文件为测试：ProbePushoutGrpTop。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(* 相关说明。 （已译） *)

Section GrpConversion.

Context {A B C : GrpObject}.
Context (f : A ~{Grp}~> B) (g : A ~{Grp}~> C).
Context {Q : GrpObject}.
Context (q1 : B ~{Grp}~> Q) (q2 : C ~{Grp}~> Q).
Context (Hcomm : q1 ∘[Grp] f ≈ q2 ∘[Grp] g).

(* 相关说明。 （已译） *)
Definition ctl_grp_apex :
  pushout_apex (Grp_pushout f g) = AmalgamGrp f g := eq_refl.

Definition ctl_grp_in1 :
  pushout_in1 (Grp_pushout f g) = am_inj1 f g := eq_refl.

(* CONTROL 2. The mediator's own value three formers reduces --
 [am_eval] [Fixpoint], so 这是 where [am_med]'s homomorphism
 laws come from. （已译） *)
Definition ctl_grp_med_unit :
  grp_map (am_med f g q1 q2 Hcomm) am_one = grp_unit Q := eq_refl.

Definition ctl_grp_med_mul (u v : AmTerm B C) :
  grp_map (am_med f g q1 q2 Hcomm) (am_mul u v)
    = grp_mul Q (grp_map (am_med f g q1 q2 Hcomm) u)
                (grp_map (am_med f g q1 q2 Hcomm) v) := eq_refl.

(* CONTROL 2b.  [pushout_med] itself is named in a control, so that
   renaming it breaks this file rather than turning NEGATIVE 1 vacuously
   green -- [Fail] catches "reference not found" just as happily as it
   catches a unification failure.（标题）（已译） *)
Definition ctl_grp_med_typed
  : pushout_apex (Grp_pushout f g) ~{Grp}~> Q :=
  pushout_med (Grp_pushout f g) Hcomm.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition neg_grp_med :
  pushout_med (Grp_pushout f g) Hcomm = am_med f g q1 q2 Hcomm := eq_refl.

End GrpConversion.

Section TopConversion.

Context {A B C : TopSpace}.
Context (f : A ~{Top}~> B) (g : A ~{Top}~> C).
Context {Q : TopSpace}.
Context (q1 : B ~{Top}~> Q) (q2 : C ~{Top}~> Q).
Context (Hcomm : q1 ∘[Top] f ≈ q2 ∘[Top] g).

(* CONTROL 3.  Same reduction on the Top side. *)
Definition ctl_top_apex :
  pushout_apex (Top_pushout f g) = Pushout_Top f g := eq_refl.

Definition ctl_top_in1 :
  pushout_in1 (Top_pushout f g) = Top_po_in1 f g := eq_refl.

(* 相关说明。 （已译） *)
Definition ctl_top_med_typed
  : pushout_apex (Top_pushout f g) ~{Top}~> Q :=
  pushout_med (Top_pushout f g) Hcomm.

Definition ctl_top_med_named
  : Pushout_Top f g ~{Top}~> Q := Top_po_med f g q1 q2 Hcomm.

(* 相关说明。 （已译） *)
Fail Definition neg_top_med :
  pushout_med (Top_pushout f g) Hcomm = Top_po_med f g q1 q2 Hcomm := eq_refl.

End TopConversion.

Section TopEmptySpan.

Context (B C : TopSpace).

Notation Ef := (top_zero B).
Notation Eg := (top_zero C).

(* 相关说明。 （已译） *)
Definition ctl_top_points :
  carrier (top_carrier (Pushout_Top Ef Eg))
    = carrier (sum_carrier B C) := eq_refl.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition neg_top_carrier :
  top_carrier (Pushout_Top Ef Eg) = sum_carrier B C := eq_refl.

(* 相关说明。 （已译） *)
Definition ctl_top_sum_open (W : sum_carrier B C → Type)
  (H : IsOpen (Sum_Top B C) W) : IsOpen (Sum_Top B C) W := H.

(*
   本节说明 ProbePushoutGrpTop 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition neg_top_topology :
  IsOpen (Pushout_Top Ef Eg) = IsOpen (Sum_Top B C) := eq_refl.

End TopEmptySpan.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SetPin.

Universe bg.
Constraint Set < bg.

(* 相关说明。 （已译） *)
Check (fun (A B C : GrpObject@{bg bg bg})
           (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) => AmalgamGrp f g).

(* CONTROL 6.  So is the chosen pushout, hence [Grp_HasPushouts]. *)
Check (fun (A B C : GrpObject@{bg bg bg})
           (f : A ~{Grp}~> B) (g : A ~{Grp}~> C) =>
         pushout_apex (Grp_pushout f g)).

(*
   本节说明 ProbePushoutGrpTop 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (fun B C : GrpObject@{bg bg bg} => Grp_free_product B C).
Check (fun B C : GrpObject@{bg bg bg} => Grp_fp_inl B C).
Check (fun B C : GrpObject@{bg bg bg} => grp_const B C).

(* 相关说明。 （已译） *)
Check (Grp_zero_hom Z2).
Check (Grp_zero_hom_Section Z2).

(* CONTROL 9, formerly NEGATIVE 5 (formability).  Before #450,
   Instance/Grp.v's map out of the trivial group was NOT formable above
   [Set], and stripping the guard reported "Cannot enforce Set = bg".
   Since #450 it is formable at every carrier level.（标题）（已译） *)
Check (fun G : GrpObject@{bg bg bg} => Grp_zero_hom G).

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (fun G : GrpObject@{bg bg bg} => Grp_zero_hom_Section G).

End SetPin.
