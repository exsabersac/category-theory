Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Theory.Bicategory.

Generalizable All Variables.

(*
   本文件给出双范畴实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子、双范畴相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Obligation Tactic := idtac.
Program Definition Cat_Hcompose {C D E : Category} :
  ([D, E] ∏ [C, D]) ⟶ [C, E] := {|
  fobj := fun p => fst p ◯ snd p;
  fmap := fun p q m => nat_hcompose (fst m) (snd m)
|}.
Next Obligation.
  intros C D E [P1 P2] [Q1 Q2] [α β] [α' β'] [Hα Hβ]; simpl; intro o.
  now rewrite (Hα (Q2 o)), (Hβ o).
Qed.
Next Obligation.
  intros C D E [P1 P2]; simpl; intros; cat.
Qed.
Next Obligation.
  intros C D E [P1 P2] [Q1 Q2] [R1 R2] [α β] [α' β']; simpl; intros.
  rewrite fmap_comp, !comp_assoc.
  apply compose_respects; [|reflexivity].
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  symmetry; apply naturality.
Qed.

(*
   本节说明函子、双范畴相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma Cat_hunit_left_natural (C D : Category) (f f' : C ⟶ D) (η : f ⟹ f') :
  nat_compose η (to (nat_ρ f))
  ≈ nat_compose (to (nat_ρ f')) (nat_hcompose (nat_id (F:=Id)) η).
Proof. simpl; intros; cat. Qed.

Lemma Cat_hunit_right_natural (C D : Category) (f f' : C ⟶ D) (η : f ⟹ f') :
  nat_compose η (to (nat_λ f))
  ≈ nat_compose (to (nat_λ f')) (nat_hcompose η (nat_id (F:=Id))).
Proof. simpl; intros; cat. Qed.

Lemma Cat_hassoc_natural (W X Y Z : Category)
  (h h' : Y ⟶ Z) (g g' : X ⟶ Y) (f f' : W ⟶ X)
  (θ : h ⟹ h') (γ : g ⟹ g') (η : f ⟹ f') :
  nat_compose (nat_hcompose θ (nat_hcompose γ η)) (from (nat_α f g h))
  ≈ nat_compose (from (nat_α f' g' h')) (nat_hcompose (nat_hcompose θ γ) η).
Proof. simpl; intros; rewrite !fmap_id, fmap_comp; cat. Qed.

Lemma Cat_triangle (X Y Z : Category) (g : Y ⟶ Z) (f : X ⟶ Y) :
  nat_hcompose (to (nat_λ g)) (nat_id (F:=f))
  ≈ nat_compose (nat_hcompose (nat_id (F:=g)) (to (nat_ρ f))) (from (nat_α f Id g)).
Proof. simpl; intros; cat. Qed.

Lemma Cat_pentagon (V W X Y Z : Category)
  (k : Y ⟶ Z) (h : X ⟶ Y) (g : W ⟶ X) (f : V ⟶ W) :
  nat_compose (nat_compose (nat_hcompose (nat_id (F:=k)) (from (nat_α f g h)))
                           (from (nat_α f (h ◯ g) k)))
              (nat_hcompose (from (nat_α g h k)) (nat_id (F:=f)))
  ≈ nat_compose (from (nat_α (g ◯ f) h k)) (from (nat_α f g (k ◯ h))).
Proof. simpl; intros; cat. Qed.

(*
   本节说明双范畴、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Cat_Bicategory : Bicategory :=
  Build_Bicategory
    Category
    (fun C D => @obj (@Fun C D))                 (* bi1cell   *)
    (fun C D => @hom (@Fun C D))                 (* bi2cell   *)
    (@Id)                                        (* bi1id     *)
    (fun C D => @homset (@Fun C D))              (* bi2homset *)
    (fun C D => @id (@Fun C D))                  (* bi2id     *)
    (fun C D => @compose (@Fun C D))             (* vcompose  *)
    (fun C D => @compose_respects (@Fun C D))    (* vcompose_respects *)
    (fun C D => @id_left (@Fun C D))             (* bi2id_left  *)
    (fun C D => @id_right (@Fun C D))            (* bi2id_right *)
    (fun C D => @comp_assoc (@Fun C D))          (* vcompose_assoc *)
    (fun C D => @comp_assoc_sym (@Fun C D))      (* vcompose_assoc_sym *)
    (@Cat_Hcompose)                              (* hcompose  *)
    (fun C D f => nat_ρ f)                        (* hunit_left  *)
    (fun C D f => nat_λ f)                        (* hunit_right *)
    (fun W X Y Z h g f => iso_sym (nat_α f g h))  (* hassoc *)
    Cat_hunit_left_natural
    Cat_hunit_right_natural
    Cat_hassoc_natural
    Cat_triangle
    Cat_pentagon.
