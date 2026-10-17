Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cartesian.Closed.Natural.
Require Import Category.Structure.Cartesian.Closed.Adjunction.
Require Import Category.Functor.Product.Internal.
Require Import Category.Functor.Hom.Internal.
Require Import Category.Functor.Construction.Product.
Require Import Category.Structure.Wedge.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Adjunction.Right.
Require Import Category.Adjunction.Parameter.

Generalizable All Variables.

(*
   本文件为测试：ProbeParameter396。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Fail Check p396_no_such_constant_anywhere.

(* 相关说明。 （已译） *)

Section Theorem3Boundaries.

Context {X P A : Category}.
Context {F : X ∏ P ⟶ A}.
Context (PA : ParametrizedAdjunction F).
Context {p p' : P} (h : p' ~> p) (hop : p ~{P^op}~> p') (a : A).

(* CONTROLS. Every 常值 negatives section name. （已译） *)
Check @ParametrizedAdjunction.
Check @pa_right.
Check @pa_adj.
Check @pa_param_mate.
Check @pa_param_mate_universal.
Check @pa_square.
Check @parametrized_right_adjoint_bifunctor.
Check @pa_bifunctor_obj.
Check @pa_bifunctor_fmap.
Check @pa_bifunctor_fmap_param.
Check @pa_bifunctor_fmap_is_mate.
Check @pa_bifunctor_partial_r_obj.
Check @pa_bifunctor_partial_r_fmap_unfold.
Check @pa_bifunctor_partial_r_fmap.
Check @param_transform.
Check @Partial_l.
Check @Partial_r.
Check @conj_mate.
Check @conjugate_unique_right.
Check @unique_obj.
Check @unop.
Check @fmap.

(* 相关说明。 （已译） *)
Definition p396_hou_control (x : X) (b : A) (k : F (x, p) ~> b) :=
  to (@adj _ _ _ _ (pa_adj PA p) x b) k.

(* 相关说明。 （已译） *)
Definition p396_universal := pa_param_mate_universal PA h.
Definition p396_mate := pa_param_mate PA h.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition p396_universal_strict :
  unique_obj (pa_param_mate_universal PA h) = pa_param_mate PA h := eq_refl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition p396_partial_r_obj_control := pa_bifunctor_partial_r_obj PA p a.
Definition p396_partial_r_fmap_control {b : A} (k : a ~> b) :=
  pa_bifunctor_partial_r_fmap_unfold PA p k.

Fail Definition p396_partial_r_strict :
  Partial_r (parametrized_right_adjoint_bifunctor PA) p = pa_right PA p
  := eq_refl.

(*
   本节说明 ProbeParameter396 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition p396_fmap_param_control := pa_bifunctor_fmap_param PA hop a.
Definition p396_fmap_param_weak := pa_bifunctor_fmap_is_mate PA hop a.

Fail Definition p396_fmap_param_strict :
  fmap[parametrized_right_adjoint_bifunctor PA]
      ((hop, id[a]) : (p, a) ~{P^op ∏ A}~> (p', a))
    = pa_param_mate PA (unop hop) a := eq_refl.

End Theorem3Boundaries.

(* 相关说明。 （已译） *)

Section DualBoundaries.

Context {P A X : Category}.
Context {G : P^op ∏ A ⟶ X}.
Context (CA : CoParametrizedAdjunction G).
Context (p : P) (x : X) {p1 p2 : P} (k : p1 ~> p2).

(* CONTROLS. *)
Check @CoParametrizedAdjunction.
Check @pa_left.
Check @pa_coadj.
Check @copa_param_mate.
Check @parametrized_left_adjoint_bifunctor.
Check @copa_bifunctor_obj.
Check @copa_bifunctor_fmap.
Check @copa_bifunctor_fmap_param.
Check @copa_bifunctor_fmap_is_mate.
Check @copa_swap_obj.
Check @copa_swap_fmap.
Check @copa_swap_transport.
Check @copa_swap_route.
Check @Swap.
Check @Adjunction.

Definition p396_swap_obj_control (b : A) := @copa_swap_obj P A X G p b.
Definition p396_swap_fmap_control {b b' : A} (m : b ~> b') :=
  @copa_swap_fmap P A X G p b b' m.
Definition p396_swap_transport_control :=
  copa_swap_transport CA p (pa_coadj CA p).

(*
   本节说明 ProbeParameter396 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition p396_swap_strict :
  Partial_l (G ◯ @Swap A (P^op)) p = Partial_r G p := eq_refl.

(*
   本节说明伴随、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition p396_swap_ascribe :
  Partial_l (G ◯ @Swap A (P^op)) p ⊣ pa_left CA p := pa_coadj CA p.

(*
   本节说明 ProbeParameter396 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition p396_copa_fmap_param_control :=
  @copa_bifunctor_fmap_param P A X G CA x p1 p2 k.
Definition p396_copa_fmap_param_weak :=
  @copa_bifunctor_fmap_is_mate P A X G CA x p1 p2 k.

Fail Definition p396_copa_fmap_param_strict :
  fmap[parametrized_left_adjoint_bifunctor CA]
      ((id[x], k) : (x, p1) ~{X ∏ P}~> (x, p2))
    = copa_param_mate CA k x := eq_refl.

End DualBoundaries.

(* 相关说明。 （已译） *)

Section CurryingBoundaries.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Closed C _}.
Context {p p' : C} (h : p' ~> p) (a : C).
Context {x y : C} (f : x ~> y).

(* CONTROLS. *)
Check @curry_ParametrizedAdjunction.
Check @curry_pa_adj.
Check @curry_pa_right.
Check @curry_pa_to_is_curry.
Check @curry_pa_from_is_uncurry.
Check @curry_prod_functor_obj.
Check @curry_prod_functor_fmap.
Check @curry_param_mate_unfold.
Check @curry_param_mate_residue.
Check @curry_param_mate_is_closed_action.
Check @curry_param_mate_is_ihom.
Check @curry_param_mate_is_internal_hom.
Check @curry_internal_hom_fmap_unfold.
Check @curry_bifunctor_obj.
Check @curry_bifunctor_fmap.
Check @curry_natural_param.
Check @uncurry_natural_param.
Check @ihom_id_action.
Check @Prod_Functor.
Check @Exp_Functor.
Check @Curry_Adjunction.
Check @InternalHomFunctor.
Check @InternalProductFunctor.
Check @ihom.
Check @second.
Check @curry.
Check @eval.
Check @to_adj_nat_l.
Check @to_adj_nat_r.
Check @from_adj_nat_l.
Check @from_adj_nat_r.
Check @adj.
Check @Build_Adjunction.

Definition p396_curry_residue_control :=
  curry_param_mate_residue h a.
Definition p396_curry_closed_control :=
  curry_param_mate_is_closed_action h a.
Definition p396_curry_ihom_control := curry_param_mate_is_ihom h a.
Definition p396_curry_prod_obj_control := curry_prod_functor_obj p x.
Definition p396_curry_prod_fmap_control := curry_prod_functor_fmap p f.
Definition p396_curry_bifunctor_obj_control := curry_bifunctor_obj p a.
Definition p396_curry_adj_control :=
  @adj C C (Prod_Functor p) (Exp_Functor p) (Curry_Adjunction p).

(*
   本节说明 ProbeParameter396 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition p396_curry_mate_closed_strict :
  pa_param_mate curry_ParametrizedAdjunction h a
    = curry (eval ∘ second h) := eq_refl.

(*
   本节说明hom、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition p396_curry_mate_ihom_strict :
  pa_param_mate curry_ParametrizedAdjunction h a
    = @fmap _ _ (InternalHomFunctor C) (p, a) (p', a) (h, id[a])
  := eq_refl.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition p396_prod_functor_fmap_strict :
  fmap[Partial_l ×(C) p] f = fmap[Prod_Functor p] f := eq_refl.

(*
   本节说明 ProbeParameter396 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition p396_curry_field_copy :
  Partial_l ×(C) p ⊣ Exp_Functor p :=
  @Build_Adjunction C C (Partial_l ×(C) p) (Exp_Functor p)
    (fun u v => @adj C C (Prod_Functor p) (Exp_Functor p)
                  (Curry_Adjunction p) u v)
    (@to_adj_nat_l   C C (Prod_Functor p) (Exp_Functor p)
                     (Curry_Adjunction p))
    (@to_adj_nat_r   C C (Prod_Functor p) (Exp_Functor p)
                     (Curry_Adjunction p))
    (@from_adj_nat_l C C (Prod_Functor p) (Exp_Functor p)
                     (Curry_Adjunction p))
    (@from_adj_nat_r C C (Prod_Functor p) (Exp_Functor p)
                     (Curry_Adjunction p)).

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition p396_curry_bifunctor_fmap_strict {b : C} (k : a ~> b) :
  fmap[parametrized_right_adjoint_bifunctor curry_ParametrizedAdjunction]
      ((h, k) : (p, a) ~{C^op ∏ C}~> (p', b))
    = fmap[InternalHomFunctor C] ((h, k) : (p, a) ~{C^op ∏ C}~> (p', b))
  := eq_refl.

End CurryingBoundaries.

(* 相关说明。 （已译） *)

Section TransformBoundaries.

Context {X P A : Category}.
Context {F : X ∏ P ⟶ A}.
Context (PA : ParametrizedAdjunction F).
Context (p : P) (x : X) (a : A) (k : F (x, p) ~> a).

(* CONTROLS. *)
Check @ParametrizedAdjunctionTransform.
Check @pat_right.
Check @pat_adj.
Check @pat_of_pa.
Check @pa_of_pat.
Check @parametrized_adjunction_iff_transform.
Check @pa_pat_round_right.
Check @pat_unit_is_pa_unit.
Check @pat_counit_is_pa_counit.
Check @pa_pat_round_to.
Check @pa_pat_round_from.
Check @pa_to.
Check @pa_from.
Check @pa_unit.
Check @pa_counit.
Check @pa_triangle_left.
Check @pa_triangle_right.

Definition p396_round_right_control := pa_pat_round_right PA.
Definition p396_round_unit_control := pat_unit_is_pa_unit PA p x.
Definition p396_round_counit_control := pat_counit_is_pa_counit PA p a.
Definition p396_round_to_weak := pa_pat_round_to PA p x a k.

(*
   本节说明伴随、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition p396_pat_round_whole :
  pa_of_pat (pat_of_pa PA) = PA := eq_refl.

(*
   本节说明伴随、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition p396_pat_round_to_strict :
  pa_to (pa_of_pat (pat_of_pa PA)) p x a k = pa_to PA p x a k := eq_refl.

End TransformBoundaries.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section DinaturalShape.

Context {C D : Category}.

Program Definition p396_const_bifunctor (w : D) : C^op ∏ C ⟶ D := {|
  fobj := fun _ => w;
  fmap := fun _ _ _ => id[w]
|}.

Context (Hf : C^op ∏ C ⟶ D).
Context (w : D) (leg : ∀ z : C, w ~> Hf (z, z)).
Context {u v : C} (f : u ~> v).

(* CONTROLS. *)
Check @Wedge.
Check @wedge_obj.
Check @wedge_map.
Check @ump_wedges.
Check @bimap.
Check @op.
Check p396_const_bifunctor.

(* The wedge condition, in Structure/Wedge.v's own spelling. *)
Definition p396_wedge_cond : Type :=
  bimap[Hf] id f ∘ leg u ≈ bimap[Hf] (op f) id ∘ leg v.

(* The dinaturality hexagon, at 常值 source, whose two [bimap]
 factors 恒等 apex. （已译） *)
Definition p396_dinat_cond : Type :=
  bimap[Hf] (op f) id ∘ leg v ∘ bimap[p396_const_bifunctor w] id f
    ≈ bimap[Hf] id f ∘ leg u ∘ bimap[p396_const_bifunctor w] (op f) id.

(* 相关说明。 （已译） *)

Definition p396_wedge_to_dinat : p396_wedge_cond → p396_dinat_cond.
Proof.
  unfold p396_wedge_cond, p396_dinat_cond.
  intro E; simpl; rewrite !id_right; now symmetry.
Defined.

Definition p396_dinat_to_wedge : p396_dinat_cond → p396_wedge_cond.
Proof.
  unfold p396_wedge_cond, p396_dinat_cond.
  intro E; simpl in E; rewrite !id_right in E; now symmetry.
Defined.

(* 相关说明。 （已译） *)

Fail Definition p396_dinat_is_wedge :
  p396_dinat_cond = p396_wedge_cond := eq_refl.

End DinaturalShape.

(*
   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section HomEqualsProof.

Universes co ch cp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}).
Context (Fu Uu : Cu ⟶ Cu).

(* CONTROLS at the declared levels. *)
Check Cu.
Check Fu.
Check Uu.
Check (fun z : Cu => z).
Check (fun z w : Cu => z ~{Cu}~> w).
Check (fun z : Cu => id[z]).
Check (fun (z w : Cu) (g g' : z ~> w) => g ≈ g').
Check (@Functor Cu Cu).
Check @Product.
Check @Partial_l.

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Check (Cu ∏ Cu).

(*
   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Check (Fu ⊣ Uu).

End HomEqualsProof.

(*
   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section TwoHomLevels.

Universes xo xh ao ah.
Constraint xh < ah.

Context (Xu : Category@{xo xh xh}).
Context (Au : Category@{ao ah ah}).

(* CONTROLS at declared levels, including 函子 direction
 IS formable. （已译） *)
Check Xu.
Check Au.
Check (fun z w : Xu => z ~{Xu}~> w).
Check (fun z w : Au => z ~{Au}~> w).
Check (Xu ⟶ Au).

(* * *** Negative 17 (FORMABILITY): reverse 函子

 Stripped, error ends "universe inconsistency: Cannot enforce
 xh = ... because xh < ah <= ...". （已译） *)

Fail Check (Au ⟶ Xu).

End TwoHomLevels.

(*
   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ParameterCollapse.

Universes po ph ao2 ah2 xo xh2.
Constraint ph < xh2.

Context (Pu : Category@{po ph ph}).
Context (Au : Category@{ao2 ah2 ah2}).
Context (Xu : Category@{xo xh2 xh2}).
Context (Hf : (Pu^op ∏ Pu) ⟶ Xu).
Context (K : (Pu^op ∏ Pu) ⟶ (Pu^op ∏ Au)).
Context (L : (Pu^op ∏ Au) ⟶ Xu).

(* CONTROLS at declared levels: source, integrand's type, the
 integrand itself, both composable halves, formable direction of
 §H's 函子 pair. （已译） *)
Check Pu.
Check Au.
Check Xu.
Check (Pu^op ∏ Pu).
Check ((Pu^op ∏ Pu) ⟶ Xu).
Check Hf.
Check K.
Check L.
Check (Pu^op ⟶ Xu).
Check @AdjointOnTheRight.
Check @Compose.

(* 相关说明。 （已译） *)

Fail Check (@Wedge Pu Xu Hf).

(*
   本节说明 ProbeParameter396 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Check (L ◯ K).

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Check (Xu^op ⟶ Pu).

End ParameterCollapse.
