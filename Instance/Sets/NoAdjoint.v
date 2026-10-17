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

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/continuous+functor

   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** Mac Lane V.5 Exercise 1, any cartesian 范畴 terminal
 对象 （已译） *)

Section FixedProductAdjoint.

Context {C : Category}.
Context `{CC : @Cartesian C}.
Context `{T : @Terminal C}.

(* Forward: 左伴随 [X × −] makes [X × −] 右伴随, so it
 preserves 终对象, [1 ≅ X × 1]; [X × 1 ≅ X] 这是
 [X ≅ 1]. （已译） *)
Theorem fixed_product_left_adjoint_terminal
  (X : C) (L : C ⟶ C) (A : L ⊣ fixed_product_functor X) : X ≅ 1.
Proof.
  pose proof (@right_adjoint_preserves_terminal C C L
                (fixed_product_functor X) A T T) as HT.
  pose proof (@fobj_one_iso C C (fixed_product_functor X) T T HT) as Hi.
  simpl in Hi.
  transitivity (X × 1); [ symmetry; exact (@prod_one_r C CC T X) |].
  symmetry; exact Hi.
Qed.

Section Converse.

Context (X : C).
Context (HX : X ≅ 1).

(* Every object has exactly one arrow into an [X ≅ 1]. *)
Definition to_X (x : C) : x ~> X := from HX ∘ one.

Lemma to_X_unique {x : C} (f : x ~> X) : f ≈ to_X x.
Proof.
  unfold to_X.
  rewrite <- (id_left f), <- (iso_from_to HX), <- comp_assoc.
  apply compose_respects; [reflexivity |]; apply one_unique.
Qed.

(* 相关说明。 （已译） *)
Program Definition fp_adj_iso (x y : C) :
  @Isomorphism Sets
    {| carrier := @hom C (Id x) y; is_setoid := @homset C (Id x) y |}
    {| carrier := @hom C x (fixed_product_functor X y)
     ; is_setoid := @homset C x (fixed_product_functor X y) |} := {|
  to   := {| morphism := fun f => to_X x △ f |};
  from := {| morphism := fun g => exr ∘ g |}
|}.
Next Obligation. proper; now apply fork_respects. Qed.
Next Obligation.
  symmetry; apply (snd (ump_products _ _ _)); split;
    [ apply to_X_unique | reflexivity ].
Qed.

(* Converse: when [X ≅ 1], the identity is a left adjoint of [X × −].  Built
   directly (no adjunction is transported along [X × − ≈ Id]). *)
Definition Id_adj_fixed_product : Id ⊣ fixed_product_functor X.
Proof using C CC HX T X.
  unshelve eapply (@Build_Adjunction' C C Id (fixed_product_functor X)
                     fp_adj_iso).
  - intros x y z f g; simpl.
    rewrite <- fork_comp.
    apply fork_respects; [| reflexivity].
    symmetry; apply to_X_unique.
  - intros x y z f g; simpl.
    symmetry; apply second_fork.
Defined.

End Converse.

(* The exact characterisation: [X × −] has 左伴随 iff [X] is
 terminal ([∃] [sigT], so converse hands over adjoint). （已译） *)
Theorem fixed_product_left_adjoint_iff_terminal (X : C) :
  (∀ L : C ⟶ C, L ⊣ fixed_product_functor X → X ≅ 1)
  ∧ (X ≅ 1 → ∃ L : C ⟶ C, L ⊣ fixed_product_functor X).
Proof.
  split.
  - intros L A; exact (fixed_product_left_adjoint_terminal X L A).
  - intro HX; exists Id; exact (Id_adj_fixed_product X HX).
Qed.

End FixedProductAdjoint.

(** The exercise as stated, at Sets. *)
Definition times_X_has_left_adjoint_iff_terminal (X : Sets) :
  (∀ L : Sets ⟶ Sets, L ⊣ fixed_product_functor X → X ≅ 1)
  ∧ (X ≅ 1 → ∃ L : Sets ⟶ Sets, L ⊣ fixed_product_functor X) :=
  fixed_product_left_adjoint_iff_terminal X.

(* * ** Mac Lane V.5 Exercise 4: [Sets^op] not 笛卡尔闭 （已译） *)

(* The duality scaffolding conversion: [@Cocartesian Sets] IS
 [@Cartesian (Sets^op)] (Structure/Cocartesian.v), the
 终对象 Sets 始对象 [Sets^op]. （已译） *)
Definition Sets_op_Initial : @Initial (Sets^op) := Sets_Terminal.

Example Sets_op_Cartesian_is_coproducts :
  @Cartesian (Sets^op) = @Cocartesian Sets := eq_refl.

(* The point, two-point set [1 + 1] injections — kept
 polymorphic (a [bool]-carried two-point set would pin 对象 level
 [Set]). （已译） *)
Definition OnePt : Sets := @terminal_obj Sets Sets_Terminal.

Definition OnePlusOne : Sets :=
  @product_obj (Sets^op) Sets_Cocartesian OnePt OnePt.

Definition pt_inl : OnePt ~{Sets}~> OnePlusOne :=
  @exl (Sets^op) Sets_Cocartesian OnePt OnePt.

Definition pt_inr : OnePt ~{Sets}~> OnePlusOne :=
  @exr (Sets^op) Sets_Cocartesian OnePt OnePt.

(* 相关说明。 （已译） *)
Example pt_inl_inr_apart :
  (pt_inl ttt ≈ pt_inr ttt) = False := eq_refl.

(* If [Sets^op] were cartesian closed for ANY cartesian structure [CC],
   [prod_zero_r] would give [1 ×[CC] 0 ≅ 0] in [Sets^op] — in [Sets], a
   subterminal apex under both injections of [1 + 1] — forcing the two
   injections to agree. *)
Theorem Sets_op_not_cartesian_closed
  (CC : @Cartesian (Sets^op)) (CL : @Closed (Sets^op) CC) : False.
Proof.
  pose (Z := @initial_obj (Sets^op) Sets_op_Initial).
  pose proof (@prod_zero_r (Sets^op) CC CL Sets_op_Initial OnePt) as Hi.
  assert (Hsub : ∀ p q : carrier (@product_obj (Sets^op) CC OnePt Z), p ≈ q).
  { intros p q.
    pose proof (iso_from_to Hi p) as Hp.
    pose proof (iso_from_to Hi q) as Hq.
    assert (Hu : ∀ u v : carrier OnePt, to Hi u ≈ to Hi v)
      by (intros [] []; reflexivity).
    exact (transitivity (symmetry Hp) (transitivity (Hu _ _) Hq)). }
  assert (Hi12 : @exl (Sets^op) CC OnePt Z ≈ @exr (Sets^op) CC OnePt Z)
    by (intro u; apply Hsub).
  assert (Hbad : pt_inl ≈ pt_inr).
  { rewrite <- (@exl_fork (Sets^op) CC OnePlusOne OnePt Z pt_inl pt_inr) at 1.
    rewrite <- (@exr_fork (Sets^op) CC OnePlusOne OnePt Z pt_inl pt_inr) at 2.
    now rewrite Hi12. }
  exact (Hbad ttt).
Qed.
