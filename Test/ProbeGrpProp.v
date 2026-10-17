(*
   本文件为测试：ProbeGrpProp。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Groupoid.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pushout.Split.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Pushout.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Free.

Generalizable All Variables.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Fail Definition instrument_check : nat := true.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section AmEq.

Context {A B C : GrpObject}.
Context (f : A ~{Grp}~> B) (g : A ~{Grp}~> C).

(*
   本节说明 ProbeGrpProp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition am_eq_eliminates_into_Type
  (u v : AmTerm B C) (He : am_eq f g u v) : poly_unit :=
  ltac:(induction He).

(* CONTROL 1a.  Two constructors of [am_eq] carry a [Type]-valued `≈`
   premise, and both are still accepted verbatim: a [Prop] inductive MAY
   store [Type]-valued data, it simply may not be eliminated into [Type]. *)
Definition am_eq_stores_a_Type_premise (b b' : carrier B) (H : b ≈ b') :
  am_eq f g (am_l b) (am_l b') := ae_l_resp b b' H.

Definition am_eq_stores_a_Type_premise_r (c c' : carrier C) (H : c ≈ c') :
  am_eq f g (am_r c) (am_r c') := ae_r_resp c c' H.

(* CONTROL 1b. The 关系 IS amalgam's own `≈`, amalgam's
 [grp_prop] reads it back nose both directions. （已译） *)
Definition am_eq_is_the_amalgam_equality (u v : AmTerm B C) :
  @equiv _ (is_setoid (grp_setoid (AmalgamGrp f g))) u v = am_eq f g u v
  := eq_refl.

Definition am_eq_pequiv_to (u v : AmTerm B C)
  (H : @pequiv _ _ (grp_prop (AmalgamGrp f g)) u v) :
  @equiv _ (is_setoid (grp_setoid (AmalgamGrp f g))) u v :=
  pequiv_to u v H.

Definition am_eq_pequiv_from (u v : AmTerm B C)
  (H : @equiv _ (is_setoid (grp_setoid (AmalgamGrp f g))) u v) :
  @pequiv _ _ (grp_prop (AmalgamGrp f g)) u v :=
  pequiv_from u v H.

End AmEq.

(*
   本节说明 ProbeGrpProp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition am_med_applies
  {A B C : GrpObject} (f : A ~{Grp}~> B) (g : A ~{Grp}~> C)
  {Q : GrpObject} (q1 : B ~{Grp}~> Q) (q2 : C ~{Grp}~> Q)
  (Hcomm : q1 ∘[Grp] f ≈ q2 ∘[Grp] g) :
  AmalgamGrp f g ~{Grp}~> Q :=
  am_med f g q1 q2 Hcomm.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section Quot.

Context {G : GrpObject}.
Context (N : NormalSubgroup G).

(* The truncation, read back at [eq_refl]. *)
Definition quot_equiv_is_inhabited_quot_rel (a b : carrier G) :
  @equiv _ (is_setoid (grp_setoid (QuotientGrp N))) a b
    = inhabited (quot_rel N a b) := eq_refl.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition quot_equiv_yields_the_witness (a b : carrier G)
  (H : @equiv _ (is_setoid (grp_setoid (QuotientGrp N))) a b) :
  quot_rel N a b := ltac:(destruct H).

(* CONTROL 2a.  The [inhabited] route in: one [constructor]. *)
Definition quot_equiv_of_witness (a b : carrier G) (H : quot_rel N a b) :
  @equiv _ (is_setoid (grp_setoid (QuotientGrp N))) a b := inhabits H.

(* CONTROL 2b.  The [inhabited] route out, into a [Prop] goal. *)
Definition quot_equiv_into_Prop (a b : carrier G)
  (H : @equiv _ (is_setoid (grp_setoid (QuotientGrp N))) a b) :
  inhabited (quot_rel N a b) := H.

(*
   本节说明 ProbeGrpProp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition quot_equiv_through_pequiv {K : GrpObject} (p : Kills N K)
  (a b : carrier G)
  (H : @equiv _ (is_setoid (grp_setoid (QuotientGrp N))) a b) :
  grp_map (`1 p) a ≈ grp_map (`1 p) b.
Proof.
  apply (@pequiv_to _ _ (grp_prop K)).
  change (inhabited (quot_rel N a b)) in H.
  destruct H as [H].
  apply (@pequiv_from _ _ (grp_prop K)).
  exact (kills_descends N p a b H).
Defined.

(* CONTROL 2d, APPLIED.  The mediator itself still exists. *)
Definition quot_med_applies {K : GrpObject} (p : Kills N K) :
  QuotientGrp N ~{Grp}~> K := quot_med N p.

(* 相关说明。 （已译） *)
Definition sub_mem_is_still_data (a : carrier G) (H : sub_mem N a) :
  sub_mem N a := H.

End Quot.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section Free.

Context (X : SetoidObject).

(* The truncation, read back at [eq_refl]. *)
Definition fg_equiv_is_inhabited_hom_equiv (a b : FGWord X) :
  @equiv _ (is_setoid (grp_setoid (FreeGrpObject X))) a b
    = inhabited (@equiv _ (@homset (FreeGroupoid (PointQuiver X)) ttt ttt) a b)
  := eq_refl.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition free_equiv_yields_the_groupoid_equation (a b : FGWord X)
  (H : @equiv _ (is_setoid (grp_setoid (FreeGrpObject X))) a b) :
  @equiv _ (@homset (FreeGroupoid (PointQuiver X)) ttt ttt) a b
  := ltac:(destruct H).

(* CONTROL 3a.  The route in: one [inhabits]. *)
Definition free_equiv_of_groupoid_equation (a b : FGWord X)
  (H : @equiv _ (@homset (FreeGroupoid (PointQuiver X)) ttt ttt) a b) :
  @equiv _ (is_setoid (grp_setoid (FreeGrpObject X))) a b := inhabits H.

(* CONTROL 3b.  The route out, at a TARGET group, through [pequiv] -- which
   is how [free_grp_extend]'s respectfulness is proved.  Note what is NOT
   assumed: nothing about [X].  The witness comes from [H], which carries
   [grp_prop] as a field. *)
Definition free_equiv_through_pequiv {H : GrpObject}
  (h : X ~{Sets}~> Grp_Forget H) (a b : FGWord X)
  (Hab : @equiv _ (is_setoid (grp_setoid (FreeGrpObject X))) a b) :
  grp_map (free_grp_extend h) a ≈ grp_map (free_grp_extend h) b :=
  proper_morphism (grp_map (free_grp_extend h)) a b Hab.

End Free.

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition free_group_is_total (X : Sets) : GrpObject := FreeGrpObject X.

Definition free_universal_arrow_is_total (X : Sets) :
  UniversalArrow X Grp_Forget := free_group_universal_arrow X.

Definition free_functor_is_total : Sets ⟶ Grp := FreeGrp.

Definition free_adjunction_is_total : FreeGrp ⊣ Grp_Forget :=
  free_group_adjunction.

Definition free_universal_is_total (X : Sets) :
  ∀ (H : GrpObject) (h : X ~{Sets}~> Grp_Forget H),
    ∃! g : FreeGrpObject X ~{Grp}~> H,
      h ≈ fmap[Grp_Forget] g ∘ fg_insert X :=
  free_group_universal X.

(* ------------------------------------------------------------------------ *)
(** ** (4) What did NOT move *)

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* [Grp] locally propositional, what lets 函子-of-points
 constructions Structure/Group/Representable.v applied at [Grp]
 itself no manual 假设. （已译） *)
Definition Grp_is_locally_propositional : LocallyPropositional Grp :=
  Grp_LocallyPropositional.

Definition grp_hom_setoid_is_propositional (G H : GrpObject) :
  PropEquiv (@GrpHom_Setoid G H) := GrpHom_PropEquiv.
