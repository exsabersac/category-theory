Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Construction.Product.
Require Import Category.Functor.Product.Internal.
Require Import Category.Functor.Diagonal.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.Diagonal.Product.

Set Universe Polymorphism.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本文件给出例子。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section GAFTExample.

Context `{C : Category}.
Context `{@Cartesian C}.

(*
   本节说明 Examples 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Obligation Tactic := idtac.

Program Definition diagonal_unique (d : C) (d' : C ∏ C)
  (f : d ~> InternalProductFunctor C d') :
  ∃! g : (d, d) ~{ C ∏ C }~> d',
    f ≈ fmap[InternalProductFunctor C] g ∘ (id[d] △ id[d]) :=
  {| unique_obj := (exl ∘ f, exr ∘ f) |}.
Next Obligation.
  (* 相关说明。 （已译） *)
  intros d d' f; simpl.
  assert (PFf : f ≈ (exl ∘ f) △ (exr ∘ f))
    by (apply ump_products; split; reflexivity).
  rewrite PFf at 1.
  symmetry.
  apply ump_products; split.
  - rewrite exl_fork_comp, <- comp_assoc, exl_fork, id_right; reflexivity.
  - rewrite exr_fork_comp, <- comp_assoc, exr_fork, id_right; reflexivity.
Qed.
Next Obligation.
  (* 相关说明。 （已译） *)
  intros d d' f [v1 v2] Hv.
  simpl in Hv.
  assert (Hf : f ≈ (v1 △ v2)).
  { rewrite Hv.
    apply ump_products; split.
    - rewrite exl_fork_comp, <- comp_assoc, exl_fork, id_right; reflexivity.
    - rewrite exr_fork_comp, <- comp_assoc, exr_fork, id_right; reflexivity. }
  simpl; split.
  - rewrite Hf, exl_fork; reflexivity.
  - rewrite Hf, exr_fork; reflexivity.
Qed.

(* Packaged as a [UniversalArrow], whose [arrow_initial] projection is exactly
   the comma-category initial object [GAFT_from_initials] wants. *)
Definition diagonal_UA (d : C) : UniversalArrow d (InternalProductFunctor C) :=
  universal_arrow_from_UMP d (InternalProductFunctor C) (d, d)
    (id[d] △ id[d]) (diagonal_unique d).

(*
   本节说明伴随、同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition diagonal_product_via_gaft :
  { F : C ⟶ C ∏ C & F ⊣ InternalProductFunctor C } :=
  GAFT_from_initials (InternalProductFunctor C)
    (fun d => arrow_initial (UniversalArrow := diagonal_UA d)).

(*
   本节说明伴随、函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition diagonal_product_via_gaft_is_diagonal :
  projT1 diagonal_product_via_gaft ≈ Diagonal_Product C :=
  left_adjoint_iso (InternalProductFunctor C)
    (projT1 diagonal_product_via_gaft) (Diagonal_Product C)
    (projT2 diagonal_product_via_gaft)
    (Diagonal_Product_Adjunction C).

End GAFTExample.
