(*
   本文件给出余积实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Product.
Require Import Category.Functor.Diagonal.

Generalizable All Variables.

(** ** The coproduct bifunctor *)

(** [+(C) : C ∏ C ⟶ C], the dual of Functor/Product/Internal.v's [×(C)].
    On a pair of morphisms it is the copairing of the two injections after
    each component. *)
#[export]
Program Instance InternalCoproductFunctor `(C : Category) `{@Cocartesian C} :
  C ∏ C ⟶ C := {
  fobj := fun p => fst p + snd p;
  fmap := fun _ _ p => (inl ∘ fst p) ▽ (inr ∘ snd p)
}.
Next Obligation.
  proper.
  simpl in *.
  rewrites.
  reflexivity.
Qed.
Next Obligation.
  (*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  simpl in *.
  rewrite <- merge_comp.
  rewrite !comp_assoc.
  rewrite inl_merge, inr_merge.
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

Notation "+( C )" := (@InternalCoproductFunctor C _)
  (at level 0, format "+( C )") : functor_scope.

(** ** The adjunction *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export]
Program Instance Diagonal_Coproduct_Adjunction (C : Category) `{@Cocartesian C} :
  +(C) ⊣ Diagonal_Product C := {
  adj := fun _ _ =>
    {| to   := {| morphism := fun f => (f ∘ inl, f ∘ inr) |}
     ; from := {| morphism := fun f => fst f ▽ snd f |} |}
}.
(* The inverse transpose respects the pairwise equivalence of [C ∏ C]
   (Construction/Product.v), by [merge_respects]
   (Structure/Cocartesian.v). *)
Next Obligation. proper; apply merge_respects; auto. Qed.
(* Round trip [(x ∘ inl) ▽ (x ∘ inr) ≈ x]: [merge_comp] factors [x] out,
   leaving [x ∘ (inl ▽ inr)], and [cat] finishes with [merge_inl_inr]
   (Structure/Cocartesian.v) and the identity law. *)
Next Obligation. rewrite merge_comp; cat. Qed.
(* Naturality in the [C ∏ C] argument: one equation per component, hence the
   [split], each an [inl_merge]/[inr_merge] step. *)
Next Obligation. split; unmerge. Qed.
(* [merge_comp] backwards on the right-hand side, then [comp_assoc] forward so
   that [inl_merge] and [inr_merge] apply under the composites. *)
Next Obligation.
  rewrite <- merge_comp, !comp_assoc, inl_merge, inr_merge; reflexivity.
Qed.
(* This square is [merge_comp] itself. *)
Next Obligation. apply merge_comp. Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** The unit at [p = (a, b)] is the pair of injections into [a + b]. *)
Definition coproduct_unit (C : Category) `{@Cocartesian C} (p : C ∏ C) :
  p ~{C ∏ C}~> Diagonal_Product C (fst p + snd p) := (inl, inr).

(** The counit at [x] is the folding map [x + x ~> x]. *)
Definition coproduct_counit (C : Category) `{@Cocartesian C} (x : C) :
  x + x ~{C}~> x := id ▽ id.

Lemma coproduct_unit_is_unit (C : Category) `{@Cocartesian C} (p : C ∏ C) :
  @unit _ _ +(C) (Diagonal_Product C) (Diagonal_Coproduct_Adjunction C) p
    ≈ coproduct_unit C p.
Proof. unfold coproduct_unit; simpl; split; cat. Qed.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma coproduct_unit_components (C : Category) `{@Cocartesian C}
      (p : C ∏ C) :
  fst (@unit _ _ +(C) (Diagonal_Product C)
         (Diagonal_Coproduct_Adjunction C) p) ≈ inl ∧
  snd (@unit _ _ +(C) (Diagonal_Product C)
         (Diagonal_Coproduct_Adjunction C) p) ≈ inr.
Proof. simpl; split; cat. Qed.

(*
   本节说明 Coproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma coproduct_counit_is_counit (C : Category) `{@Cocartesian C} (x : C) :
  @counit _ _ +(C) (Diagonal_Product C) (Diagonal_Coproduct_Adjunction C) x
    ≈ coproduct_counit C x.
Proof. unfold coproduct_counit; reflexivity. Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Instance.Coq.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cocartesian.

Example coq_coproduct_diagonal : +(Coq) ⊣ Diagonal_Product Coq :=
  Diagonal_Coproduct_Adjunction Coq.

Example sets_coproduct_diagonal : +(Sets) ⊣ Diagonal_Product Sets :=
  Diagonal_Coproduct_Adjunction Sets.
