Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cartesian.Closed.Natural.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Wedge.
Require Import Category.Structure.Coend.
Require Import Category.Construction.Enriched.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Structure.Cartesian.Closed.Composition.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本文件为测试：ProbeComposition391。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)
Fail Check no_such_constant_exists_in_this_development.

(* * ** Controls: every 常值 negative names, outside any rejection （已译） *)

Check @internal_compose.
Check @internal_id.
Check @internal_compose_assoc.
Check @internal_compose_dinatural.
Check @internal_compose_natural_a.
Check @internal_compose_natural_c.
Check @internal_compose_Wedge.
Check @CCC_Enriched.
Check @Sets_Enriched.
Check @ExpBase.
Check @expBase_fobj.
Check @ComposeSrcC.
Check @composeSrcC_fobj.
Check @sets_internal_compose.
Check @sets_internal_compose_underlying.
Check @sets_internal_compose_morphism.
Check @sets_internal_id.
Check @ihom.
Check @Cartesian.
Check @Closed.
Check @split.
Check @fobj.
Check Sets.

(* 相关说明。 （已译） *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example p391_ctrl_pointwise (a b c : Sets)
        (g : b ~{Sets}~> c) (f : a ~{Sets}~> b) (t : a) :
  @internal_compose Sets _ _ a b c (g, f) t = g (f t) := eq_refl.

Example p391_ctrl_underlying (a b c : Sets)
        (g : b ~{Sets}~> c) (f : a ~{Sets}~> b) :
  (fun t : a => @internal_compose Sets _ _ a b c (g, f) t)
    = (fun t : a => (g ∘[Sets] f) t) := eq_refl.

Example p391_ctrl_equiv (a b c : Sets)
        (g : b ~{Sets}~> c) (f : a ~{Sets}~> b) :
  @internal_compose Sets _ _ a b c (g, f) ≈[Sets] g ∘ f.
Proof. intro t; reflexivity. Qed.

Fail Example p391_neg1 (a b c : Sets)
        (g : b ~{Sets}~> c) (f : a ~{Sets}~> b) :
  (@internal_compose Sets _ _ a b c (g, f) : a ~{Sets}~> c) = g ∘ f
  := eq_refl.

Section ProbeGeneral.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Closed C _}.

(* 相关说明。 （已译） *)

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)
Example p391_ctrl_b_action (a c b1 b2 : C) (f : b1 ~{C}~> b2) :
  (c^b2 × b1^a) ~{C}~> (c^b1 × b2^a) :=
  split (ihom f id) (ihom id f).

(* The honest statement in [b], as a passing control. *)
Example p391_ctrl_dinatural (a c b1 b2 : C) (f : b1 ~{C}~> b2) :
  @internal_compose C _ _ a b1 c ∘ split (ihom f id) id
    ≈ @internal_compose C _ _ a b2 c ∘ split id (ihom id f)
  := internal_compose_dinatural f.

Fail Example p391_neg2 (a c b1 b2 : C) (f : b1 ~{C}~> b2) :
  (c^b1 × b1^a) ~{C}~> (c^b2 × b2^a) :=
  split (ihom f id) (ihom id f).

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)

Example p391_ctrl_type_refl (a c b1 b2 : C) :
  ((c^b2 × b1^a) ~{C}~> (c^b1 × b2^a))
    = ((c^b2 × b1^a) ~{C}~> (c^b1 × b2^a)) := eq_refl.

Fail Example p391_neg3 (a c b1 b2 : C) :
  ((c^b2 × b1^a) ~{C}~> (c^b1 × b2^a))
    = ((c^b1 × b1^a) ~{C}~> (c^b2 × b2^a)) := eq_refl.

(* 相关说明。 （已译） *)

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition NaiveExpBase (a : C) : C ⟶ C := {|
  fobj := fun c => c^a;
  fmap := fun _ _ g => ihom id g
|}.
Next Obligation. proper; now rewrites. Qed.
Next Obligation. apply ihom_id. Qed.
Next Obligation. rewrite ihom_comp; now rewrite id_left. Qed.

Program Definition NaiveComposeSrcC (a b : C) : C ⟶ C := {|
  fobj := fun c => c^b × b^a;
  fmap := fun _ _ g => first (ihom id g)
|}.
Next Obligation. proper; now rewrites. Qed.
Next Obligation. rewrite ihom_id; apply first_id. Qed.
Next Obligation.
  rewrite <- first_comp, ihom_comp; now rewrite id_left.
Qed.

(* The target's functor, which does reduce ... *)
Example p391_ctrl_fobj (a b c : C) :
  fobj[ComposeSrcC a b] c = c^b × b^a := eq_refl.

(* ... exponent-only naive 函子, does. （已译） *)
Example p391_ctrl_naive_exp (a c : C) :
  fobj[NaiveExpBase a] c = c^a := eq_refl.

Fail Example p391_neg4 (a b c : C) :
  fobj[NaiveComposeSrcC a b] c = c^b × b^a := eq_refl.

End ProbeGeneral.

(* * ** Negative 5 (FORMABILITY): [Cartesian] identifies hom 证明 （已译） *)

(*
   本节说明hom、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ProbeUniverses.

Universes co ch cp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}).

Check obj[Cu].
Check (fun x y : Cu => x ~{Cu}~> y).
Check (fun x : Cu => id[x]).
Check (fun (x y z : Cu) (f : y ~{Cu}~> z) (g : x ~{Cu}~> y) => f ∘ g).

Fail Check (@Cartesian Cu).

End ProbeUniverses.
