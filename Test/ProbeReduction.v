Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本文件为测试：ProbeReduction。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 ProbeReduction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(*
   本节说明 ProbeReduction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section DConversion.

Context {C : Category}.
Context `{@Cartesian C}.
Context {x y : C}.
Context (f g : x ~> y).

(* CONVERSION negative. Stripped, reports unification failure
 between two product 对象. （已译） *)
Fail Definition probe_ml_aw_codomain :
  (x × y)%object = (y × y)%object := eq_refl.

(*
   本节说明 ProbeReduction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition probe_pos_codomain_degenerate :
  (x × x)%object = (x × x)%object := eq_refl.

(* 相关说明。 （已译） *)
Fail Definition probe_equalizer_pullback_round {E : C} (e : E ~> x × y) :
  (exl ∘ e) △ (exr ∘ e) = e := eq_refl.

Fail Definition probe_pullback_equalizer_round {P : C}
     (p1 : P ~> x) (p2 : P ~> y) : exl ∘ (p1 △ p2) = p1 := eq_refl.

(* Positive control naming Reduction.v's own 常值: first round
 trip does hold at [≈]. If [equalizer_pullback_round] renamed or
 changes statement, line fails compile. （已译） *)
Definition probe_pos_round_up_to_equiv {E : C} (e : E ~> x × y) :
  (exl ∘ e) △ (exr ∘ e) ≈ e := equalizer_pullback_round E e.

End DConversion.

Section DFormability.

Context {C : Category}.
Context `{@Cartesian C}.
Context {x y : C}.
Context (f g : x ~> y).

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (@ml_left C _ x y f = @aw_pair C _ x y f g).

Fail Check (@ml_right C _ x y g = @aw_diag C _ y).

(*
   本节说明 ProbeReduction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (@ml_left C _ x y f = @ml_left C _ x y f).
Check (@aw_pair C _ x y f g = @aw_pair C _ x y f g).
Check (@ml_right C _ x y g = @ml_right C _ x y g).
Check (@aw_diag C _ y = @aw_diag C _ y).

(* 相关说明。 （已译） *)
Definition probe_pos_degenerate :
  @ml_left C _ x x id = @aw_diag C _ x := eq_refl.

End DFormability.

(*
   本节说明 ProbeReduction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FDuality.

Context {C : Category}.

(* CONVERSION negatives.  Stripped, the first reports that [eq_refl] has
   type [HasCoequalizers C = HasCoequalizers C] where
   [HasCoequalizers C = HasEqualizers C^op] was expected -- records are
   nominal.（标题）（已译） *)
Fail Definition probe_HasCoequalizers_is_op :
  HasCoequalizers C = HasEqualizers (C^op) := eq_refl.

Fail Definition probe_IsCoequalizer_is_op {x y : C} (f g : x ~> y)
     (q : C) (e : y ~> q) :
  IsCoequalizer f g q e = @IsEqualizer (C^op) y x f g q e := eq_refl.

(*
   本节说明 ProbeReduction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition probe_pos_cofork_is_fork_eq {x y : C} (f g : x ~> y)
        (q : C) (e : y ~> q) (Hyp : e ∘ f ≈ e ∘ g) :
  f ∘[C^op] e ≈ g ∘[C^op] e := Hyp.

(*
   本节说明 ProbeReduction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (HasCoequalizers C).
Check (HasEqualizers (C^op)).

(* Positive control naming Reduction.v's own bridge 常值, so rename
 bridge breaks file. （已译） *)
Definition probe_pos_bridge_exists {x y : C} (f g : x ~> y)
        (q : C) (e : y ~> q) (E : IsCoequalizer f g q e) :
  @IsEqualizer (C^op) y x f g q e := IsEqualizer_op_of_IsCoequalizer E.

End FDuality.

(*
   本节说明 ProbeReduction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section WideBinary.

Context {C : Category}.
Context {x y z : C}.
Context (fx : x ~> z) (fy : y ~> z).
Context {P : C} (p1 : P ~> x) (p2 : P ~> y).

(* CONVERSION negative on the whole record. *)
Fail Definition probe_wide_binary_round
     (Hb : IsPullback fx fy P p1 p2) :
  wide_pullback_binary (binary_wide_pullback Hb) = Hb := eq_refl.

(*
   本节说明 ProbeReduction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (fun (Hb : IsPullback fx fy P p1 p2) =>
         wide_pullback_binary (binary_wide_pullback Hb)).

End WideBinary.

(*
   本节说明 ProbeReduction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section WideHeadline.

Context {C : Category}.
Context `{@Terminal C}.
Context {I : Type} (A : I -> C).
Context {P : C} (proj : forall i, P ~> A i).

Check (fun (Hp : IsIndexedProduct A P proj) =>
         wide_pullback_product A P proj Hp).

Check (fun (Hw : IsWidePullback (fun _ : I => one) P proj) =>
         product_wide_pullback A P proj Hw).

End WideHeadline.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section WideUniverseIndexBelowObject.
  Universe uo ui uc.
  Constraint uo < ui.
  Constraint ui <= uc.
  Constraint uo <= uc.
  Check IsWidePullback@{ui uc uo uc}.
End WideUniverseIndexBelowObject.

Section WideUniverseObjectBelowIndex.
  Universe uo ui uc.
  Constraint ui < uo.
  Constraint ui <= uc.
  Constraint uo <= uc.
  Check IsWidePullback@{ui uc uo uc}.
End WideUniverseObjectBelowIndex.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section WideUniverseHomProof.
  Universe uh up.
  Constraint uh < up.

  Fail Check IsWidePullback@{uh uh uh up}.

  Fail Check IsIndexedProduct@{uh uh uh up}.

  Check (fun (C : Category@{uh uh up}) (x y : obj[C])
             (g h : x ~{C}~> y) => g ≈ h).
End WideUniverseHomProof.
