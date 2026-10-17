Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Adj.
Require Import Category.Instance.Adj.Forgetful.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Two.
Require Import Category.Adjunction.Choice.

Generalizable All Variables.

(*
   本文件为测试：ProbeChoice397。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Fail Check p397_no_such_constant_anywhere.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check @RightAdjointFunctor.
Check @RAF_via.
Check @LI_via.
Check @LeftAdjSub.
Check @LeftAdjCat.
Check @SubToAdj.
Check @AdjToSub.
Check @ch_obj.
Check @ch_canonical.
Check @HasRightAdjoint.
Check @RightAdjChoice.
Check @Incl.
Check @Sub.
Check @Adj.
Check @AdjObj.
Check @Fun.
Check @Opposite.
Check @Opposite_Functor.
Check @Subcategory.
Check @conj_mate.
Check @adjobj_adj.
Check @adjobj_left.
Check @adjobj_right.
Check @nat_id.
Check @AdjForgetLeft.
Check @AdjForgetRight.
Check @fmap.
Check @Functor.
Check @Adjunction.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Conversions.

Context (C D : Category).

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition p397_raf_obj_control := raf_obj_via C D.
Definition p397_raf_map_control := raf_map_via C D.

Fail Example p397_raf_via_strict :
  RAF_via C D = RightAdjointFunctor C D := eq_refl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition p397_incl_obj_control := incl_obj_via C D.
Definition p397_incl_map_control := incl_map_via C D.

Fail Example p397_li_via_strict :
  LI_via C D = Incl ([D, C]) (LeftAdjSub C D) := eq_refl.

(*
   本节说明 ProbeChoice397 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition p397_rt_adj_obj_control := rt_adj_obj C D.

Fail Example p397_rt_adj_map_strict (x y : Adj C D) (f : x ~> y) :
  fmap[SubToAdj C D ◯ AdjToSub C D] f = f := eq_refl.

(*
   本节说明 ProbeChoice397 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition p397_rt_sub_obj_control := rt_sub_obj C D.

Fail Example p397_rt_sub_map_strict (x y : LeftAdjCat C D) (f : x ~> y) :
  fmap[AdjToSub C D ◯ SubToAdj C D] f = f := eq_refl.

(*
   本节说明hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition p397_leftadj_obj_control := leftadj_obj C D.
Definition p397_strict_iso_control := SubAdj_strict_iso C D.

Fail Example p397_cats_strict : LeftAdjCat C D = Adj C D := eq_refl.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition p397_ch_left_control := ch_canonical_left C D.
Definition p397_ch_right_control := ch_canonical_right C D.
Definition p397_ch_adj_control := ch_canonical_adj C D.

Fail Example p397_ch_canonical_strict (x : LeftAdjCat C D) :
  ch_obj (ch_canonical C D) x = (x : AdjObj C D) := eq_refl.

(*
   本节说明伴随、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition p397_inverse_weak_control := raf_choice_inverse C D.
Definition p397_choice_iso_control := choice_iso_in_Sub C D.
Definition p397_choice_to_control := raf_choice_iso_to C D.
Definition p397_choice_from_control := raf_choice_iso_from C D.

Fail Example p397_choice_inverse_strict
     (F : D ⟶ C) (p q : HasRightAdjoint F) :
  conj_mate (adjobj_adj ((F; q) : AdjObj C D))
            (adjobj_adj ((F; p) : AdjObj C D)) nat_id
    ∙ conj_mate (adjobj_adj ((F; p) : AdjObj C D))
                (adjobj_adj ((F; q) : AdjObj C D)) nat_id
  = nat_id := eq_refl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition p397_raf_type_control : Opposite (LeftAdjCat C D) ⟶ [C, D] :=
  RightAdjointFunctor C D.

Fail Definition p397_raf_covariant :
  LeftAdjCat C D ⟶ [C, D] := RightAdjointFunctor C D.

(* 相关说明。 （已译） *)
Definition p397_variance_control := raf_fmap_variance C D.
Definition p397_id_control := raf_id_is_conj_mate_id C D.

End Conversions.

(*
   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section HomEqualsProof.

Universes co ch cp.
Constraint ch < cp.

Context (Cu Du : Category@{co ch cp}).
Context (Fq : Du ⟶ Cu) (Uq : Cu ⟶ Du).

(* CONTROLS at the declared levels. *)
Check Cu.
Check Du.
Check Fq.
Check Uq.
Check (fun x y : Cu => x ~{Cu}~> y).
Check (fun x : Cu => @id Cu x).
Check (fun (x y : Cu) (g g' : x ~> y) => g ≈ g').
Check (Du ⟶ Cu).
Check (Cu ⟶ Du).

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Check (Opposite Cu).

(* 相关说明。 （已译） *)

Fail Check (Subcategory Cu).

(* * *** Negative 11 (FORMABILITY): 函子 CATEGORY alone

 [Du ⟶ Cu] accepted above, so 这是 [Fun]'s own shape not
 [Functor]'s. Stripped, same tail, reported [Du]. （已译） *)

Fail Check ([Du, Cu]).

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Check (Fq ⊣ Uq).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Check (RightAdjointFunctor Cu Du).

End HomEqualsProof.

(*
   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section TwoHomLevels.

Universes ao ah bo bh.
Constraint ah < bh.

Context (Au : Category@{ao ah ah}).
Context (Bu : Category@{bo bh bh}).

(* CONTROLS at the declared levels. *)
Check Au.
Check Bu.
Check (fun x y : Au => x ~{Au}~> y).
Check (fun x y : Bu => x ~{Bu}~> y).
Check (Au ⟶ Bu).

(* * *** Negative 14 (FORMABILITY): reverse 函子

 Stripped, error ends "universe inconsistency: Cannot enforce
 ah = <fresh> because ah < bh <= <fresh>". （已译） *)

Fail Check (Bu ⟶ Au).

(* * *** Negative 15 (FORMABILITY): 函子 范畴, independently

 No 函子 pair command. Stripped, error ends "universe
 inconsistency: Cannot enforce bh = ah because ah < bh". （已译） *)

Fail Check ([Au, Bu]).

(* * *** Negative 16 (FORMABILITY): delivered 函子 inherits it

 Not independent 14 15; pinned so change at either donor is
 visible here. Stripped, error ends "universe inconsistency:
 Cannot enforce ah = bh because ah < bh". （已译） *)

Fail Check (RightAdjointFunctor Bu Au).

End TwoHomLevels.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition p397_two_object := two_left_adjoint_object.
Definition p397_two_value := two_raf_value.
Definition p397_two_proper := two_left_adjoint_proper.
Definition p397_two_differ := two_const_functors_differ.
Definition p397_two_not_id := two_left_adjoint_not_identity.
Definition p397_two_adj := two_const_adj.
Definition p397_independence := choice_independence.
Definition p397_equivalence := SubToAdj_Equivalence.
Definition p397_full := LeftAdjSub_Full.
