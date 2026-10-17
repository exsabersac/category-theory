(*
   本文件为测试：ProbeNoAdjoint432。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.BiCCC.
Require Import Category.Functor.Structure.Terminal.
Require Import Category.Functor.Product.Fixed.
Require Import Category.Adjunction.Continuity.Finite.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cocartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.Sets.NoAdjoint.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe432_absent_name.

(* 相关说明。 （已译） *)

Section NotIdentity.

Context {C : Category}.
Context `{CC : @Cartesian C}.
Context `{T : @Terminal C}.

(* control: the adjoint exists at [X := 1] *)
Check (Id_adj_fixed_product (1 : C) iso_id : Id ⊣ fixed_product_functor 1).

(* N1 CONVERSION: [1 × −] is not [Id] as a functor record *)
Fail Example p432_fixed_product_one_not_Id :
  fixed_product_functor (1 : C) = Id := eq_refl.

End NotIdentity.

(* * ** B: TYPING — sides 范畴 （已译） *)

Section Sides.

Context {C : Category}.
Context `{CC : @Cartesian C}.
Context `{T : @Terminal C}.
Context (X : C) (HX : X ≅ 1).

(* control *)
Check (Id_adj_fixed_product X HX : Id ⊣ fixed_product_functor X).

(* N2 TYPING: 恒等 LEFT adjoint [X × −], not right
 adjoint （已译） *)
Fail Check (Id_adj_fixed_product X HX : fixed_product_functor X ⊣ Id).

End Sides.

(* control: Sets itself IS cartesian closed *)
Check (Sets_Closed : @Closed Sets Sets_Cartesian).
Check (Sets_op_not_cartesian_closed
         : ∀ CC : @Cartesian (Sets^op), @Closed (Sets^op) CC → False).

(* N3 TYPING: the refutation is about [Sets^op]; it does not ascribe at
   [Sets] *)
Fail Check (Sets_op_not_cartesian_closed
              : ∀ CC : @Cartesian Sets, @Closed Sets CC → False).

(* * ** C: UNIVERSE — 伴随 identifies two hom levels （已译） *)

Monomorphic Universe co ch do dh.
Monomorphic Constraint ch < dh.

Section HomLevels.

Context (Cw : Category@{co ch ch}).
Context (Dw : Category@{do dh dh}).

(* controls: two 范畴, 函子 UP hom levels （已译） *)
Check Cw.
Check Dw.
Check (Cw ⟶ Dw).

(*
   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (Dw ⟶ Cw).

End HomLevels.

(** ** D: readbacks *)

Example p432_op_initial_is_terminal :
  @initial_obj (Sets^op) Sets_op_Initial = @terminal_obj Sets Sets_Terminal
  := eq_refl.

Example p432_injections_apart : (pt_inl ttt ≈ pt_inr ttt) = False := eq_refl.

Example p432_fixed_product_fmap {C : Category} `{@Cartesian C}
  (X : C) {x y : C} (g : x ~> y) :
  fmap[fixed_product_functor X] g = second g := eq_refl.

(* the converse's transpose computes: it pairing 唯一箭头
 [X] — makes [Id_adj_fixed_product]'s [Defined] load-bearing （已译） *)
Example p432_transpose_is_pairing {C : Category} `{CC : @Cartesian C}
  `{T : @Terminal C} (X : C) (HX : X ≅ 1) (x y : C) (f : x ~> y) :
  to (@adj _ _ _ _ (Id_adj_fixed_product X HX) x y) f = to_X X HX x △ f
  := eq_refl.

Check @right_adjoint_preserves_terminal.
Check @right_adjoint_preserves_binary_products.
Check @left_adjoint_preserves_initial.
Check @left_adjoint_preserves_binary_coproducts.
Check @times_X_has_left_adjoint_iff_terminal.
Check @fixed_product_left_adjoint_iff_terminal.

(** ** Guard block *)

Check @fixed_product_functor.
Check @Id_adj_fixed_product.
Check @Sets_op_not_cartesian_closed.
Check @Sets_Closed.
Check @Sets_Cartesian.
Check @Sets_op_Initial.
Check @pt_inl.
Check @pt_inr.
Check @Closed.
Check @Cartesian.
Check @Terminal.
Check @Adjunction.
Check @Id.
Check @iso_id.
Check @Sets.
Check @Category.
Check @ttt.
