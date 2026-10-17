(*
   本文件为测试：ProbeProjective429。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Orthogonality.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Regular.
Require Import Category.Instance.Two.
Require Import Category.Structure.Projective.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe429_absent_name.

(* * ** A: UNIVERSE — [Projective] identifies hom 证明, the
 identification [Epic]'s, not file's （已译） *)

Section ProbeUniverse.

Universes vo vh vp.
Constraint vh < vp.

Context (Cu : Category@{vo vh vp}) (x y : Cu) (f : x ~{Cu}~> y).

(* controls: 范畴, homs arrow all form here （已译） *)
Check Cu.
Check (x ~{Cu}~> y).
Check f.

(* 相关说明。 （已译） *)
Fail Check (@Epic Cu x y f).
Fail Check (@Monic Cu x y f).

(* 相关说明。 （已译） *)
Fail Check (@Projective Cu x).

End ProbeUniverse.

(* * ** B: CONVERSION — [Epic] [C^op] not [Monic] [C]; bridge
 [op_Epic_of_Monic] does real work, so [injective_extend] not an
 [eq_refl] readback [C^op] accessor's 假设 （已译） *)

Section ProbeBridge.

Context {C : Category} {a b : C} (m : a ~> b).

(* 相关说明。 （已译） *)
Check (@Epic (C^op) b a m).
Check (@Monic C a b m).
Check (@op_Epic_of_Monic C a b m).

(* N4 CONVERSION ("cannot unify"), N5 TYPING (a [Monic] 证明 offered where
 [Epic] one expected): two predicates distinct records （已译） *)
Fail Example p429_bridge_refl : @Epic (C^op) b a m = @Monic C a b m := eq_refl.
Fail Example p429_bridge_id (H : @Monic C a b m) : @Epic (C^op) b a m := H.

(* 相关说明。 （已译） *)
Example p429_op_op : (C^op)^op = C := eq_refl.
Example p429_hom_op : (b ~{C^op}~> a) = (a ~{C}~> b) := eq_refl.

End ProbeBridge.

(* 相关说明。 （已译） *)

Section ProbeExists.

Context {C : Category} {a b : C}.

(* controls: [∃] [exists] both [sigT]; Prop existential over a
 Prop 关系 forms （已译） *)
Example p429_exists_is_sigT :
  (∃ h : a ~> b, h ≈ h) = { h : a ~> b & h ≈ h } := eq_refl.
Example p429_keyword_exists_is_sigT :
  (exists h : a ~> b, h ≈ h) = { h : a ~> b & h ≈ h } := eq_refl.
Check (ex (fun n : nat => n = n)).

(* N6 TYPING: Prop-valued existential over [≈], Type-valued
 ([ex] unqualified: Prelude's 常值, whose module [Coq.] on
 8.19/8.20 [Corelib.] Rocq 9) （已译） *)
Fail Definition p429_prop_lift : Prop :=
  ex (fun h : a ~> b => h ≈ h).

End ProbeExists.

(* 相关说明。 （已译） *)

Definition Injective_placeholder : nat := 0.
Definition Initial_placeholder : nat := 0.

(* controls: without the [@] both resolve *)
Check Injective_placeholder.
Check Initial_placeholder.

(* N7, N8 PARSING *)
Fail Check @Injective_placeholder.
Fail Check @Initial_placeholder.

(** ** E: readbacks *)

Section Readbacks.

Context {C : Category} (p q : C).

Example p429_inj_is_op_proj : @Injective C q = @Projective (C^op) q := eq_refl.

Example p429_cohom_is_op_hom :
  @Curried_CoHom C q = @Curried_Hom (C^op) q := eq_refl.

Example p429_hom_fmap_is_postcomp {b c : C} (g : b ~> c) (h : p ~> b) :
  fmap[[Hom p ,─]] g h = g ∘ h := eq_refl.

Check (projective_iff_hom_preserves_epi p).
Check (injective_iff_cohom_preserves_mono q).
Check (@Coprod_Projective C).
Check (@IndexedCoprod_Projective C).
Check (@sets_all_projective_entails_LEM).
Check two_projective_not_all.

(* the witnesses' lifts COMPUTE: split epi lifts retraction, the
 始对象 lifts [zero] （已译） *)
Example p429_retraction_lift_is {b c : C} (g : b ~> c) (R : Retraction g)
  (f : p ~> c) : `1 (Retraction_lifts g R f) = retract ∘ f := eq_refl.

Example p429_initial_lift_is `{I : @Initial C} {b c : C} (g : b ~> c)
  (He : Epic g) (f : 0 ~> c) :
  `1 (@projective_lift C _ initial_obj_Projective b c g He f) = zero := eq_refl.

End Readbacks.

(* 相关说明。 （已译） *)
Example p429_leibniz_lift_is (T : Type) {b c : Sets} (g : b ~> c) (He : Epic g)
  (f : LeibnizSetoid T ~{Sets}~> c) (t : T) :
  `1 (@projective_lift Sets _ (Sets_Leibniz_Projective T) b c g He f) t
    = `1 (epic_implies_surjective g He (f t)) := eq_refl.

(** ** Guard block *)

Check @Projective.
Check @projective_lift.
Check @injective_extend.
Check @Epic.
Check @Monic.
Check @op_Epic_of_Monic.
Check @Curried_Hom.
Check @Curried_CoHom.
Check @Category.
Check @hom.
Check (fun C : Category => Initial C).
Check @zero.
Check Prop.
