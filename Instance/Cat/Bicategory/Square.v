Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Square.
Require Import Category.Adjunction.Compose.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Cat.
Require Import Category.Theory.Bicategory.
Require Import Category.Theory.Bicategory.Adjunction.
Require Import Category.Theory.Bicategory.Mates.
Require Import Category.Instance.Cat.Bicategory.
Require Import Category.Instance.Cat.Bicategory.Adjunction.

Generalizable All Variables.

(** * The adjoint-square mate is the mates mate, at Cat *)

(*
   本文件给出双范畴实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SquareMatesAtCat.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {C' D' : Category} {F' : D' ⟶ C'} {U' : C' ⟶ D'} (A' : F' ⊣ U').
Context (K : C ⟶ C') (L : D ⟶ D').

Definition SqBA  : BicatAdjunction (B:=Cat_Bicategory) F  U  :=
  Cat_Adjunction_BicatAdjunction A.
Definition SqBA' : BicatAdjunction (B:=Cat_Bicategory) F' U' :=
  Cat_Adjunction_BicatAdjunction A'.

Theorem sq_mate_is_mate (sg : F' ◯ L ⟹ K ◯ F) :
  SqMate A A' K L sg ≈ mate SqBA SqBA' sg.
Proof.
  intros a; simpl; unfold sq_mate.
  rewrite (to_adj_unit (H:=A')).
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite !fmap_id.
  rewrite ?id_left, ?id_right.
  reflexivity.
Qed.

Theorem sq_mate_inv_is_mate_inv (ta : L ◯ U ⟹ U' ◯ K) :
  SqMateInv A A' K L ta ≈ mate_inv SqBA SqBA' ta.
Proof.
  intros x; simpl; unfold sq_mate_inv.
  rewrite (from_adj_counit (H:=A')).
  rewrite !fmap_id.
  rewrite ?id_left, ?id_right.
  reflexivity.
Qed.

Theorem adjoint_square_iff_Cat_mate
  (sg : F' ◯ L ⟹ K ◯ F) (ta : L ◯ U ⟹ U' ◯ K) :
  AdjointSquareT A A' K L sg ta ↔ ta ≈ mate SqBA SqBA' sg.
Proof.
  split; intro H.
  - intro a.
    rewrite (SqMate_uniq A A' K L sg ta H a).
    exact (sq_mate_is_mate sg a).
  - apply (sq_mate_to_hom A A' K L _ _ (transform_SigmaNat K L sg)).
    intro a.
    rewrite (H a).
    symmetry; exact (sq_mate_is_mate sg a).
Qed.

Theorem adjoint_square_iff_Cat_mate_inv
  (sg : F' ◯ L ⟹ K ◯ F) (ta : L ◯ U ⟹ U' ◯ K) :
  AdjointSquareT A A' K L sg ta ↔ sg ≈ mate_inv SqBA SqBA' ta.
Proof.
  split; intro H.
  - intro x.
    rewrite (SqMateInv_uniq A A' K L sg ta H x).
    exact (sq_mate_inv_is_mate_inv ta x).
  - apply (sq_mate_inv_to_hom A A' K L _ _ (transform_TauNat K L ta)).
    intro x.
    rewrite (H x).
    symmetry; exact (sq_mate_inv_is_mate_inv ta x).
Qed.

End SquareMatesAtCat.
