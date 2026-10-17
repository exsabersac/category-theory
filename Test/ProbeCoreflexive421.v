(*
   本文件为测试：ProbeCoreflexive421。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Image.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Structure.Equalizer.Coreflexive.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe421_absent_name.

(* 相关说明。 （已译） *)

Section OpDual.

Context {C : Category} {x y : C} (f g : x ~> y).

(* 相关说明。 （已译） *)
Example p421_field_converts (s : y ~> x) (H : s ∘ f ≈ id) :
  f ∘[C^op] s ≈ id := H.

(* 相关说明。 （已译） *)
Check (@corefl_op_round C x y f g).
Check (@op_corefl_round C x y f g).

(* 相关说明。 （已译） *)
Fail Example p421_pair_is_op :
  CoreflexivePair f g = @ReflexivePair (C^op) y x f g := eq_refl.

(* 相关说明。 （已译） *)
Fail Example p421_class_is_op :
  HasCoreflexiveEqualizers C = HasReflexiveCoequalizers (C^op) := eq_refl.

(* controls: both class directions are derivable *)
Check (@HasCoreflexiveEqualizers_of_op C).
Check (@op_HasReflexiveCoequalizers_of_Coreflexive C).

(* N3 CONVERSION: coreflexive equalizers are not all equalizers *)
Fail Example p421_class_is_HasEqualizers :
  HasCoreflexiveEqualizers C = HasEqualizers C := eq_refl.

(* control: 含入 other way instance （已译） *)
Check (fun H : @HasEqualizers C => @HasEqualizers_HasCoreflexiveEqualizers C H).

End OpDual.

(* * ** B: 恒等 index lives FULL arrow family only （已译） *)

Section GenFamily.

Context {C : Category} (HP : HasIndexedProducts C).
Context {J : Category} (F : J ⟶ C).
Context {I : Type} {idx_dom idx_cod : I → J}
  {idx_arr : ∀ i : I, idx_dom i ~{J}~> idx_cod i}
  (Hgen : Generates idx_arr).
Context (idx_id : J → I).

(* 相关说明。 （已译） *)
Fail Definition p421_gen_proj_at_x (x : J) :
  @pe_gen_product C HP J F I idx_cod ~> F x :=
  @pe_gen_proj C HP J F I idx_cod (idx_id x).

(* control: at the declared codomain it lands *)
Definition p421_gen_proj_at_cod (x : J) :
  @pe_gen_product C HP J F I idx_cod ~> F (idx_cod (idx_id x)) :=
  @pe_gen_proj C HP J F I idx_cod (idx_id x).

(*
   本节说明 ProbeCoreflexive421 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition p421_trap_gen_proj_at_x (x : J) :
  pe_gen_product HP F ~> F x := pe_gen_proj HP F (idx_id x).

(* 相关说明。 （已译） *)
Definition p421_full_proj_at_x (x : J) :
  pe_arrow_product HP F ~> F x :=
  pe_arrow_proj HP F (mk_arrow (@id J x)).

Check (@id_index_cod J).

(* readback: 恒等 index's codomain [x] nose （已译） *)
Example p421_id_index (x : J) : aix_cod (mk_arrow (@id J x)) = x := eq_refl.

End GenFamily.

(* 相关说明。 （已译） *)

Section SetsConverse.

Context {X Y : SetoidObject} (f g : X ~{Sets}~> Y).

(* N5 TYPING: choice function carried [diagonal_in_image] not by
 itself Sets 态射 — [proper_morphism] field missing （已译） *)
Fail Definition p421_bare_section (D : diagonal_in_image f g) : Y ~{Sets}~> X :=
  {| morphism := fun b => `1 (D b) |}.

(* control: properness 假设 it is （已译） *)
Check (fun (D : diagonal_in_image f g)
           (Hp : ∀ b b' : Y, b ≈ b' → `1 (D b) ≈ `1 (D b')) =>
         diagonal_section f g D Hp).

(* control: IMAGE-level reading needs no such 假设 either
 direction — image setoid compares codomain components only, so the
 bare choice function proper there （已译） *)
Check (fun D : diagonal_in_image f g =>
         fst (diagonal_in_image_iff_through_image f g) D).
Check (fun (d : Y ~{Sets}~> Sets_Image (f △ g))
           (Hd : Sets_Image_mono (f △ g) ∘ d ≈ id △ id) =>
         snd (diagonal_in_image_iff_through_image f g) (d; Hd)).

End SetsConverse.

(** ** D: readbacks and non-vacuity *)

Check (@mc_limit_apex).
Check (@mc_limit_leg).
Check (@id_index_dom).
Check (@id_index_arr).
Check (@Sets_Complete_via_Manes).
Check (fun (C : Category) (HP : HasIndexedProducts C) (HE : HasCoreflexiveEqualizers C) =>
         Complete_from_coreflexive_equalizers HP HE).

(** ** Guard block *)

Check @CoreflexivePair.
Check @corefl_retract.
Check @corefl_retract_f.
Check @corefl_retract_g.
Check @HasCoreflexiveEqualizers.
Check @coreflexive_eq.
Check @common_retraction_coreflexive.
Check @HasEqualizers_HasCoreflexiveEqualizers.
Check @functor_preserves_coreflexive.
Check @CoreflexivePair_of_op.
Check @op_ReflexivePair_of_Coreflexive.
Check @corefl_op_round.
Check @op_corefl_round.
Check @HasCoreflexiveEqualizers_of_op.
Check @op_HasReflexiveCoequalizers_of_Coreflexive.
Check @pe_retract.
Check @pe_retract_proj.
Check @pe_retract_s.
Check @pe_retract_t.
Check @pe_coreflexive.
Check @mc_equalizer.
Check @mc_apex.
Check @mc_incl.
Check @mc_IsEqualizer.
Check @mc_cone.
Check @mc_limiting.
Check @mc_limit.
Check @Complete_from_coreflexive_equalizers.
Check @fork_diagonal_of_reflexive.
Check @reflexive_of_fork_diagonal.
Check @ReflexivePair_of_diagonal_factors.
Check @diagonal_factors_of_ReflexivePair.
Check @ReflexivePair_iff_diagonal_factors.
Check @diagonal_in_image.
Check @diagonal_in_image_of_reflexive.
Check @diagonal_section.
Check @reflexive_of_diagonal_in_image.
Check @diagonal_through_image.
Check @diagonal_in_image_of_through_image.
Check @through_image_of_diagonal_in_image.
Check @diagonal_in_image_iff_through_image.
Check @Sets_HasCoreflexiveEqualizers.
Check @ReflexivePair.
Check @HasReflexiveCoequalizers.
Check @HasEqualizers.
Check @pe_gen_product.
Check @pe_gen_proj.
Check @pe_arrow_product.
Check @pe_arrow_proj.
Check @mk_arrow.
Check @Generates.
Check @id.
Check @morphism.
