Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Theory.Bicategory.
Require Import Category.Theory.Bicategory.Pseudofunctor.
Require Import Category.Theory.Bicategory.Lax.

Generalizable All Variables.

(** Modifications between lax transformations, and the category they form. *)

(*
 nLab: https://ncatlab.org/nlab/show/modification
   Reference: Johnson–Yau, "2-Dimensional Categories", Definition 4.4.1.

   本文件给出修改（modification）。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class Modification {B B' : Bicategory} {F G : Pseudofunctor B B'}
      (σ τ : LaxTransformation F G) := {
  (* component 2-cells Γ_x : σ_x ⟹ τ_x *)
  md (x : @bi0cell B) :
    lt0 σ x ~{ @bicat B' (pf0 F x) (pf0 G x) }~> lt0 τ x;

  (* the modification axiom: the components commute with the naturators of σ
     and τ, whiskered by pf1[G] f on the source side and pf1[F] f on the
     target side. *)
  md_natural {x y : @bi0cell B} (f : @bicat B x y) :
    lt1 τ f ∘∘ hcomp2 (bi2id (a:=pf1[G] f)) (md x)
      ≈ hcomp2 (md y) (bi2id (a:=pf1[F] f)) ∘∘ lt1 σ f
}.

Arguments md {B B' F G σ τ} _ x.
Arguments md_natural {B B' F G σ τ} _ {x y} f.

(** The identity modification. *)

(*
   本节说明双范畴相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma id_modification_natural {B B' : Bicategory} {F G : Pseudofunctor B B'}
      (σ : LaxTransformation F G) {x y : @bi0cell B} (f : @bicat B x y) :
  lt1 σ f ∘∘ hcomp2 (bi2id (a:=pf1[G] f)) (bi2id (a:=lt0 σ x))
    ≈ hcomp2 (bi2id (a:=lt0 σ y)) (bi2id (a:=pf1[F] f)) ∘∘ lt1 σ f.
Proof.
  rewrite !hcomp2_id.
  rewrite bi2id_left, bi2id_right.
  reflexivity.
Qed.

Definition id_modification {B B' : Bicategory} {F G : Pseudofunctor B B'}
           (σ : LaxTransformation F G) : Modification σ σ :=
  {| md         := fun x => bi2id
   ; md_natural := fun x y f => id_modification_natural σ f |}.

(** The vertical composite of modifications. *)

(*
   本节说明 Modification 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma compose_modification_natural {B B' : Bicategory} {F G : Pseudofunctor B B'}
      {σ τ υ : LaxTransformation F G}
      (n : Modification τ υ) (m : Modification σ τ)
      {x y : @bi0cell B} (f : @bicat B x y) :
  lt1 υ f ∘∘ hcomp2 (bi2id (a:=pf1[G] f)) (md n x ∘∘ md m x)
    ≈ hcomp2 (md n y ∘∘ md m y) (bi2id (a:=pf1[F] f)) ∘∘ lt1 σ f.
Proof.
  rewrite hcomp2_comp_right.
  rewrite hcomp2_comp_left.
  rewrite vcompose_assoc.
  rewrite (md_natural n f).
  rewrite <- !vcompose_assoc.
  rewrite (md_natural m f).
  reflexivity.
Qed.

Definition compose_modification {B B' : Bicategory} {F G : Pseudofunctor B B'}
           {σ τ υ : LaxTransformation F G}
           (n : Modification τ υ) (m : Modification σ τ) : Modification σ υ :=
  {| md         := fun x => md n x ∘∘ md m x
   ; md_natural := fun x y f => compose_modification_natural n m f |}.

(* Reduction lemmas for the components of the identity and composite
   modifications, in `≈` form (each holds by conversion).  They keep the
   category-law proofs below free of unfolding. *)
Lemma md_id_modification {B B' : Bicategory} {F G : Pseudofunctor B B'}
      (σ : LaxTransformation F G) (x : @bi0cell B) :
  md (id_modification σ) x ≈ bi2id.
Proof. reflexivity. Qed.

Lemma md_compose_modification {B B' : Bicategory} {F G : Pseudofunctor B B'}
      {σ τ υ : LaxTransformation F G}
      (n : Modification τ υ) (m : Modification σ τ) (x : @bi0cell B) :
  md (compose_modification n m) x ≈ md n x ∘∘ md m x.
Proof. reflexivity. Qed.

(** The hom-setoid of modifications and the category of lax transformations. *)

#[local] Obligation Tactic := idtac.

(* Two modifications are equal when their components agree at every 0-cell.
   This is an equivalence relation because `≈` is one at each component. *)
Program Definition Modification_Setoid {B B' : Bicategory}
        {F G : Pseudofunctor B B'} (σ τ : LaxTransformation F G) :
  Setoid (Modification σ τ) := {|
  equiv := fun m n => ∀ x, md m x ≈ md n x
|}.
Next Obligation.
  constructor.
  - intros m x; reflexivity.
  - intros m n H x; symmetry; apply H.
  - intros m n p H1 H2 x; now rewrite H1, H2.
Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition LaxTransformation_Category {B B' : Bicategory}
           (F G : Pseudofunctor B B') : Category.
Proof.
  unshelve refine (Build_Category'
    (fun σ τ : LaxTransformation F G => Modification σ τ)  (* hom *)
    (fun σ => id_modification σ)                          (* id *)
    (fun σ τ υ n m => compose_modification n m)).         (* compose *)
  - (* homset *)
    exact (fun σ τ => Modification_Setoid σ τ).
  - (* compose respects component-wise equivalence *)
    intros σ τ υ n n' Hn m m' Hm x.
    cbv beta.
    rewrite !md_compose_modification.
    rewrite (Hn x), (Hm x).
    reflexivity.
  - (* left identity *)
    intros σ τ f x.
    cbv beta.
    rewrite md_compose_modification, md_id_modification.
    apply bi2id_left.
  - (* right identity *)
    intros σ τ f x.
    cbv beta.
    rewrite md_compose_modification, md_id_modification.
    apply bi2id_right.
  - (* associativity *)
    intros σ0 σ1 σ2 σ3 p q r x.
    cbv beta.
    rewrite !md_compose_modification.
    apply vcompose_assoc.
Defined.

(** Inhabitation witnesses. *)

(*
   本节说明双范畴、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Trivial_id_Modification :
  Modification Trivial_LaxTransformation Trivial_LaxTransformation :=
  id_modification Trivial_LaxTransformation.

Definition Trivial_compose_Modification :
  Modification Trivial_LaxTransformation Trivial_LaxTransformation :=
  compose_modification Trivial_id_Modification Trivial_id_Modification.
