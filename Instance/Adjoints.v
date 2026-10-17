Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** The category of adjunctions. *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors#Composition

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The identity functor is its own left and right adjoint: the transpose iso
   F x ~> y ≅ x ~> U y is the identity on hom-sets when F = U = Id. *)
#[export]
Program Instance adj_id {C : Category} : Id ⊣ Id := {
  adj := fun _ _ =>
    {| to   := {| morphism := _ |}
     ; from := {| morphism := _ |} |}
}.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition adj_comp
        {C : Category} {D : Category} {E : Category}
        (F : D ⟶ C) (U : C ⟶ D) (F' : E ⟶ D) (U' : D ⟶ E)
        (X : F ⊣ U) (Y : F' ⊣ U') :
  F ◯ F' ⊣ U' ◯ U := {|
  adj := fun a b =>
    {| to   := {| morphism := fun (f : F (F' a) ~> b) => to adj (to adj f) |}
     ; from := {| morphism := fun (f : a ~> U' (U b)) => adj⁻¹ (adj⁻¹ f) |} |}
|}.
Next Obligation. proper. rewrites; reflexivity. Qed.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation.
  srewrite (@iso_to_from _ _ _ (@adj C D F U X (F' a) b)).
  sapply (@iso_to_from _ _ _ (@adj D E F' U' Y a (U b))).
Qed.
Next Obligation.
  srewrite (@iso_from_to _ _ _ (@adj D E F' U' Y a (U b))).
  sapply (@iso_from_to _ _ _ (@adj C D F U X (F' a) b)).
Qed.
Next Obligation. rewrite <- !to_adj_nat_l; reflexivity. Qed.
Next Obligation. rewrite <- !to_adj_nat_r; reflexivity. Qed.
Next Obligation. rewrite <- !from_adj_nat_l; reflexivity. Qed.
Next Obligation. rewrite <- !from_adj_nat_r; reflexivity. Qed.

Notation "F ⊚ G" := (@adj_comp _ _ _ _ _ _ _ F G)
  (at level 30, right associativity) : category_scope.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record adj_morphism {C : Category} {D : Category} := {
  free_functor : D ⟶ C;                       (* the left adjoint  *)
  forgetful_functor : C ⟶ D;                  (* the right adjoint *)
  adjunction : free_functor ⊣ forgetful_functor
}.

Local Set Warnings "-intuition-auto-with-star".

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export]
Program Instance adj_morphism_setoid {C : Category} {D : Category} :
  Setoid (@adj_morphism C D) := {
  equiv := fun f g =>
              (free_functor f ≅[Fun] free_functor g) *
              (forgetful_functor f ≅[Fun] forgetful_functor g)
}.
(*
   本节说明等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Next Obligation.
  constructor.
  - intros f.
    split; reflexivity.
  - intros f g [Hfree Hforget].
    split; symmetry; assumption.
  - intros f g h [Hfree Hforget] [Hfree' Hforget'].
    split; etransitivity; eassumption.
Qed.

(* The category of Adjoints:

    objects                Categories
    arrows                 Adjunctions between categories
    identity               Id ⊣ Id
    composition            F ⊣ U → F' ⊣ U' → F ◯ F' ⊣ U' ◯ U *)

Program Definition Adjoints : Category := {|
  obj     := Category;
  hom     := @adj_morphism;
  homset  := @adj_morphism_setoid;
  id      := fun X => {| free_functor      := Id[X]
                  ; forgetful_functor := Id[X] |};
  compose := fun A B C f g =>
    {| adjunction :=
         @adj_comp A B C (free_functor g) (forgetful_functor g)
                   (free_functor f) (forgetful_functor f)
                   (adjunction g) (adjunction f) |}
|}.
Next Obligation.
  proper; simpl.
  - isomorphism; simpl.
    + transform; simpl; intros.
      * exact (fmap (transform[to X] _) ∘ transform[to X0] _).
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
    + transform; simpl; intros.
      * exact (fmap (transform[from X] _) ∘ transform[from X0] _).
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
    + simpl.
      rewrite naturality.
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (fmap (transform[to X] _))).
      rewrite <- fmap_comp.
      rewrite naturality.
      rewrite comp_assoc.
      destruct X; simpl in *.
      rewrite iso_to_from; cat.
      destruct X0; simpl in *.
      rewrite iso_to_from0; cat.
    + simpl.
      rewrite naturality.
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (fmap (transform[from X] _))).
      rewrite <- fmap_comp.
      rewrite naturality.
      rewrite comp_assoc.
      destruct X; simpl in *.
      rewrite iso_from_to; cat.
      destruct X0; simpl in *.
      rewrite iso_from_to0; cat.
  - isomorphism; simpl.
    + transform; simpl; intros.
      * exact (fmap (transform[to H] _) ∘ transform[to H0] _).
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
    + transform; simpl; intros.
      * exact (fmap (transform[from H] _) ∘ transform[from H0] _).
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
    + simpl.
      rewrite naturality.
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (fmap (transform[to H] _))).
      rewrite <- fmap_comp.
      rewrite naturality.
      rewrite comp_assoc.
      destruct H; simpl in *.
      rewrite iso_to_from; cat.
      destruct H0; simpl in *.
      rewrite iso_to_from0; cat.
    + simpl.
      rewrite naturality.
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (fmap (transform[from H] _))).
      rewrite <- fmap_comp.
      rewrite naturality.
      rewrite comp_assoc.
      destruct H; simpl in *.
      rewrite iso_from_to; cat.
      destruct H0; simpl in *.
      rewrite iso_from_to0; cat.
Qed.
Next Obligation.
  split; isomorphism;
  try (transform; simpl; intros; try exact id; cat); cat.
Qed.
Next Obligation.
  split; isomorphism;
  try (transform; simpl; intros; try exact id; cat); cat.
Qed.
Next Obligation.
  split; isomorphism;
  try (transform; simpl; intros; try exact id; cat); cat.
Qed.
Next Obligation.
  split; isomorphism;
  try (transform; simpl; intros; try exact id; cat); cat.
Qed.

(*
   https://homepages.inf.ed.ac.uk/cheunen/publications/2009/thesis/thesis.pdf

   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
