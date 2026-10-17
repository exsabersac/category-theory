(*
   本文件为测试：ProbeCoproduct。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Coq.ZArith.ZArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Semiadditive.
Require Import Category.Structure.Biproduct.Cartesian.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.CMon.Coproduct.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Coproduct.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Coproduct.
Require Import Category.Instance.Top.Homotopy.
Require Import Category.Instance.Top.Wedge.

Local Open Scope category_scope.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Check (fun (C : Category) (Z : @ZeroObject C)
           (B : @HasBiproducts C Z) (x y : C) =>
         @biproduct_product_obj C Z B x y).
Check (fun (C : Category) (Z : @ZeroObject C)
           (B : @HasBiproducts C Z) (x y : C) =>
         @biproduct_prod_is_coprod C Z B x y).

(* 相关说明。 （已译） *)
Check (fun M N : AbObject => (Ab_inl M N : M ~{Ab}~> Ab_product M N)).
Check (fun M N : AbObject => Ab_exl_inr M N).
Check (fun M N : AbObject => Ab_exr_inl M N).
Check (fun M N : AbObject => ab_zero_mor_is_cmon_zero_mor M N).

(*
   本节说明 ProbeCoproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (fun (R : RingObject) (M N : RModObject R) =>
         (eq_refl : rm_hom (RMod_inl M N) = Ab_inl M N)).
Check (fun (R : RingObject) (M N : RModObject R) =>
         (eq_refl : rm_hom (RMod_inr M N) = Ab_inr M N)).

(* 相关说明。 （已译） *)
Check (fun X Y : TopSpace => (Sum_Top X Y : TopSpace)).
Check (fun X Y : PointedTop => (Wedge_Top X Y : TopSpace)).
Check (fun X Y : PointedTop => (WedgeSum X Y : PointedTop)).
Check (fun X Y : PointedTop =>
         (eq_refl : wpoint X Y
                      = carrier (sum_carrier (ptop_space X)
                                             (ptop_space Y)))).

(** ** Conversion negatives *)

Section RoundTripNegatives.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{P : @Preadditive C}.
Context `{B : @HasBiproducts C Z}.

Let Cart : @Cartesian C := biproduct_Cartesian.

(* 相关说明。 （已译） *)
Check (fun x y : C => @biproduct_roundtrip_obj C Z P B x y).
Check (fun x y : C => @biproduct_roundtrip_exl C Z P B x y).
Check (fun x y : C => @biproduct_roundtrip_exr C Z P B x y).
Check (fun x y : C => @biproduct_roundtrip_inl C Z P B x y).
Check (fun x y : C => @biproduct_roundtrip_inr C Z P B x y).

(*
   本节说明 ProbeCoproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (fun x y : C =>
         (bi_inl (@cartesian_biproduct C Z P Cart x y),
          bi_inr (@cartesian_biproduct C Z P Cart x y),
          bi_inl (biproduct x y),
          bi_inr (biproduct x y))).

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition neg_roundtrip_inl (x y : C) :
  bi_inl (@cartesian_biproduct C Z P Cart x y) = bi_inl (biproduct x y)
  := eq_refl.

(* 相关说明。 （已译） *)
Fail Definition neg_roundtrip_record (x y : C) :
  @cartesian_biproduct C Z P Cart x y = biproduct x y := eq_refl.

End RoundTripNegatives.

(*
   本节说明 ProbeCoproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition neg_wedge_is_sum (X Y : PointedTop) :
  Wedge_Top X Y = Sum_Top (ptop_space X) (ptop_space Y) := eq_refl.

(* 相关说明。 （已译） *)

(*
   本节说明 ProbeCoproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SetPin.

Universe ua.
Constraint Set < ua.

(* 相关说明。 （已译） *)
Check (fun M N : AbObject@{ua ua ua} => Ab_product M N).
Check (fun (R : RingObject@{ua ua ua}) (M N : RModObject R) =>
         RMod_product M N).

(* NEGATIVE 4 (formability, universe inconsistency:
   "Cannot enforce Set = ua"). *)
Fail Check (fun M N : AbObject@{ua ua ua} => Ab_Biproduct M N).

(* NEGATIVE 5 (formability, universe inconsistency, same cause one layer
   up: [RMod_trivial] is built from [Ab_trivial]). *)
Fail Check (fun (R : RingObject@{ua ua ua}) (M N : RModObject R) =>
              RMod_Biproduct M N).

End SetPin.

(* 相关说明。 （已译） *)
Check (fun M N : AbObject => Ab_Biproduct M N).
Check (fun (R : RingObject) (M N : RModObject R) => RMod_Biproduct M N).

(* * ** Formability negatives: hom 证明 universes identified （已译） *)

(*
   本节说明hom、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SeparatedLevels.

Universe uo uh up.
Constraint uh < up.

(* Control: 范畴 itself, hom-sets, fine at these
 separated levels. （已译） *)
Check (fun (C : Category@{uo uh up}) (x y : obj[C]) => x ~{C}~> y).

(* NEGATIVE 6 (formability, universe inconsistency:
   "Cannot enforce up = uh"). *)
Fail Check (fun C : Category@{uo uh up} => @Cartesian C).

(* 相关说明。 （已译） *)
Fail Check (fun C : Category@{uo uh up} => @Terminal C).

End SeparatedLevels.

(* 相关说明。 （已译） *)
Check (fun C : Category => @Cartesian C).
Check (fun C : Category => @Terminal C).

(* 相关说明。 （已译） *)

(*
   本节说明 ProbeCoproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Control: at Ab the transfer is a term. *)
Check (fun (M N P : AbObject) (f : M ~{Ab}~> P) (g : N ~{Ab}~> P) =>
         (CMon_bi_is_coproduct M N P f g
            : ∃! h : Ab_product M N ~{Ab}~> P,
                (h ∘ Ab_inl M N ≈ f) ∧ (h ∘ Ab_inr M N ≈ g))).

(* Control naming the R-Mod side's own constants. *)
Check (fun (R : RingObject) (M N P : RModObject R)
           (f : M ~{RMod R}~> P) (g : N ~{RMod R}~> P) =>
         RMod_is_coproduct M N P f g).

(* NEGATIVE 8 (formability, typing error: "The term f has type
   M ~{RMod R}~> P while it is expected to have type M ~{CMon}~> P"). *)
Fail Check (fun (R : RingObject) (M N P : RModObject R)
                (f : M ~{RMod R}~> P) (g : N ~{RMod R}~> P) =>
              (CMon_bi_is_coproduct M N P f g
                 : ∃! h : RMod_product M N ~{RMod R}~> P,
                     (h ∘ RMod_inl M N ≈ f) ∧ (h ∘ RMod_inr M N ≈ g))).

(* 相关说明。 （已译） *)

(*
   本节说明 ProbeCoproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ProductTopology.

Universe o.
Context (X Y : TopSpace@{o}).

Definition probe_prod_carrier : SetoidObject@{o o} := {|
  carrier := (carrier (top_carrier X) * carrier (top_carrier Y))%type;
  is_setoid := prod_setoid
|}.

(* NEGATIVE 9 (formability, universe-level typing error: the body "has
   type Type@{o+1} while it is expected to have type Type@{o}"). *)
Fail Definition probe_prod_open (W : probe_prod_carrier → Type@{o}) :
  Type@{o} :=
  ∀ p : probe_prod_carrier, W p →
    { U : carrier (top_carrier X) → Type@{o} &
    { V : carrier (top_carrier Y) → Type@{o} &
      (IsOpen X U ∧ IsOpen Y V ∧ U (fst p) ∧ V (snd p)
         ∧ (∀ q : probe_prod_carrier,
              U (fst q) → V (snd q) → W q))%type } }.

(* 相关说明。 （已译） *)
Universe o2.
Constraint o < o2.

Definition probe_prod_open_up (W : probe_prod_carrier → Type@{o}) :
  Type@{o2} :=
  ∀ p : probe_prod_carrier, W p →
    { U : carrier (top_carrier X) → Type@{o} &
    { V : carrier (top_carrier Y) → Type@{o} &
      (IsOpen X U ∧ IsOpen Y V ∧ U (fst p) ∧ V (snd p)
         ∧ (∀ q : probe_prod_carrier,
              U (fst q) → V (snd q) → W q))%type } }.

(* 相关说明。 （已译） *)
Check (fun W : sum_carrier X Y → Type@{o} => (sum_open W : Type@{o})).

End ProductTopology.
