(*
   本文件为测试：ProbeAdditive349。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Opposite.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.AbCategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Semiadditive.
Require Import Category.Adjunction.Additive.

Generalizable All Variables.

Section ProbeTranspose.

Context {C D : Category}.
Context {AC : AbEnriched C}.
Context {AD : AbEnriched D}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).
Context (AU : @AdditiveFunctor C D AC AD U).

(* INSTRUMENT CHECK: scope-free, and it must fail. *)
Fail Definition instrument_check : True = False := eq_refl.

(* CONTROL: transpose additivity DOES hold at [≈]. *)
Example ctl_to_adj_padd {x : D} {y : C} (f g : F x ~{C}~> y) :
  to adj (padd f g) ≈ padd (to adj f) (to adj g)
  := @to_adj_padd C D AC AD F U A AU x y f g.

(* 相关说明。 （已译） *)
Fail Definition neg_to_adj_padd {x : D} {y : C} (f g : F x ~{C}~> y) :
  to adj (padd f g) = padd (to adj f) (to adj g) := eq_refl.

(* CONTROL: Theorem 3's own field holds at [≈]. *)
Example ctl_left_adjoint_fmap_padd {x y : D} (f g : x ~{D}~> y) :
  fmap[F] (padd f g) ≈ padd (fmap[F] f) (fmap[F] g)
  := @left_adjoint_fmap_padd C D AC AD F U A AU x y f g.

(* 相关说明。 （已译） *)
Fail Definition neg_left_adjoint_fmap_padd {x y : D} (f g : x ~{D}~> y) :
  fmap[F] (padd f g) = padd (fmap[F] f) (fmap[F] g) := eq_refl.

End ProbeTranspose.

Section ProbeBiproduct.

Context {C : Category}.
Context `{ZC : @ZeroObject C}.
Context {P : @Preadditive C}.

(* 相关说明。 （已译） *)
Example ctl_padd_copair_diag {a c : C} (B : Biproduct a a) (f g : a ~> c) :
  bi_copair B f g ∘ bi_diag B ≈ padd f g
  := @padd_copair_diag C ZC P a c B f g.

(* 相关说明。 （已译） *)
Fail Definition neg_padd_copair_diag {a c : C}
  (B : Biproduct a a) (f g : a ~> c) :
  bi_copair B f g ∘ bi_diag B = padd f g := eq_refl.

End ProbeBiproduct.

(*
   本节说明伴随、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ProbeUniverseDonors.

Universes ao ah bo bh.
Constraint bh < ah.

Context (Cu : Category@{ao ah ah}).
Context (Du : Category@{bo bh bh}).
Context (ZCu : @ZeroObject Cu) (ZDu : @ZeroObject Du).
Context (PCu : @Preadditive Cu) (PDu : @Preadditive Du).
Context (ACu : AbEnriched Cu) (ADu : AbEnriched Du).
Context (Gu : Du ⟶ Cu).

(* 相关说明。 （已译） *)
Check (@fmap_padd_of_preserved_coproduct Cu Du ZCu ZDu PCu PDu Gu).

(* CONTROL: naming a hom of each category at these levels is fine. *)
Check (fun (x y : Cu) => x ~{Cu}~> y).
Check (fun (x y : Du) => x ~{Du}~> y).

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (@AdditiveFunctor Du Cu ADu ACu Gu).

(* CONTROL: the functor we HAVE, D ⟶ C, is formable at these levels. *)
Check (Du ⟶ Cu).

(*
   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (Cu ⟶ Du).

(* NEGATIVE 6 (FORMABILITY) — donor (iii).  [Adjunction] itself. *)
Fail Check (@Adjunction Cu Du).

End ProbeUniverseDonors.

(* Names negatives depend must named OUTSIDE [Fail],
 rename would leave file 编译 guard green. （已译） *)
Check @to_adj_padd.
Check @left_adjoint_fmap_padd.
Check @padd_copair_diag.
Check @left_adjoint_additive.
Check @right_adjoint_additive.
Check @adj_hom_ab_iso.
Check @left_adjoint_additive_of_biproducts.
Check @hom_ab.
Check @fmap_padd_of_preserved_coproduct.
Check @AdditiveFunctor.
Check @AbEnriched_op.
Check @Preadditive_op.
