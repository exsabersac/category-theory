(*
   本文件为测试：ProbeYonedaNatural。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Sheaf.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Deloop.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Construction.Product.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Functor.Hom.Yoneda.Natural.

Generalizable All Variables.

(** ** (1) The inherited universe restriction

    A category whose object universe is declared STRICTLY BELOW its hom
    universe.  The two bifunctors reach it; the theorem does not. *)

Section ObjectsBelowHoms.

Universes uo uh.
Constraint uo < uh.

Context (C : Category@{uo uh uh}).

(* Positive controls: both bifunctors are formable here, and so is the
   partially applied evaluation functor... *)
Check (YoEval C).
Check (YoNat C).
Check (fun c : C => @YoEvalAt C c).

(* ...and so is an isomorphism between them in the functor category the
   theorem is stated in, so the packaging is not what is rejected. *)
Definition probe_iso_id_control :
  @Isomorphism ([([C, Sets] ∏ C), Sets]) (YoEval C) (YoEval C) := iso_id.

(* Negative 1: the theorem itself is not formable at this category. *)
Fail Check (yoneda_natural C).

(* Negatives 2 and 3: neither is its donor, in either variance — so the
   restriction is inherited and not introduced by this development. *)
Fail Check (fun (F : C ⟶ Sets) (A : C) => Covariant_Yoneda_Lemma C F A).
Fail Check (fun (F : C^op ⟶ Sets) (A : C) => Yoneda_Lemma C F A).

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (fun c : C => YoEvalAt_Representable C c).

End ObjectsBelowHoms.

(** ** (2) The conversion boundaries *)

Section Conversion.

Context (C : Category).
Context (x y : [C, Sets] ∏ C).
Context (tf : x ~> y).
Context (F : C^op ⟶ Sets).
Context (A : C).
Context (yv : F A).
Context (z : C).
Context (phi : z ~{C}~> A).

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe_nat_map_record :
  @fmap _ _ (YoNat C) x y tf = yo_nat_map tf := eq_refl.

Definition probe_nat_map_pointwise_control (a : fobj[YoNat C] x) :
  @fmap _ _ (YoNat C) x y tf a = yo_nat_map tf a := eq_refl.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe_derived_iso_record :
  Yoneda_Lemma_derived C F A = Yoneda_Lemma C F A := eq_refl.

Definition probe_derived_to_control (w : Presheaves [Hom ─,A] F) :
  to (Yoneda_Lemma_derived C F A) w = to (Yoneda_Lemma C F A) w := eq_refl.

(* Negative 7.  Nor are the two forward MORPHISMS equal as records, though
   they agree on every argument — the [proper_morphism] fields differ. *)
Fail Definition probe_derived_to_record :
  to (Yoneda_Lemma_derived C F A) = to (Yoneda_Lemma C F A) := eq_refl.

(*
   本节说明 ProbeYonedaNatural 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe_derived_from_value :
  from (Yoneda_Lemma_derived C F A) yv = from (Yoneda_Lemma C F A) yv
  := eq_refl.

Definition probe_derived_from_component_control :
  transform[from (Yoneda_Lemma_derived C F A) yv] z phi
    = transform[from (Yoneda_Lemma C F A) yv] z phi := eq_refl.

End Conversion.
