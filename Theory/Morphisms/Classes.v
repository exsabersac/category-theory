Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/monomorphism
   Wikipedia: https://en.wikipedia.org/wiki/Morphism

   本文件给出态射类相关定义。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition MorphismClass (C : Category) := ∀ x y : C, (x ~> y) → Type.

(* The class of monomorphisms: left-cancellable morphisms. *)
Definition MonoClass {C : Category} : MorphismClass C :=
  fun _ _ f => Monic f.

(* The class of epimorphisms: right-cancellable morphisms. *)
Definition EpiClass {C : Category} : MorphismClass C :=
  fun _ _ f => Epic f.

(* The class isomorphisms: 态射 two-sided inverse. （已译） *)
Definition IsoClass {C : Category} : MorphismClass C :=
  fun _ _ f => IsIsomorphism f.

(* The class split monomorphisms: 态射 left inverse. （已译） *)
Definition SplitMonoClass {C : Category} : MorphismClass C :=
  fun _ _ f => Section f.

(* The class split epimorphisms: 态射 right inverse. （已译） *)
Definition SplitEpiClass {C : Category} : MorphismClass C :=
  fun _ _ f => Retraction f.

(* Every split monomorphism is a monomorphism. *)
Lemma split_mono_in_mono {C : Category} {x y : C} (f : x ~> y) :
  SplitMonoClass x y f → MonoClass x y f.
Proof.
  exact (sections_are_monic x y f).
Qed.

(* Every split epimorphism is an epimorphism. *)
Lemma split_epi_in_epi {C : Category} {x y : C} (f : x ~> y) :
  SplitEpiClass x y f → EpiClass x y f.
Proof.
  exact (retractions_are_epic x y f).
Qed.

(* An isomorphism is a split monomorphism: its two-sided inverse serves as a
   left inverse. *)
Lemma iso_in_split_mono {C : Category} {x y : C} (f : x ~> y) :
  IsoClass x y f → SplitMonoClass x y f.
Proof.
  intros iso.
  exact (@Build_Section C x y f
           (@two_sided_inverse C x y f iso)
           (@is_left_inverse C x y f iso)).
Qed.

(* An isomorphism is a split epimorphism: its two-sided inverse serves as a
   right inverse. *)
Lemma iso_in_split_epi {C : Category} {x y : C} (f : x ~> y) :
  IsoClass x y f → SplitEpiClass x y f.
Proof.
  intros iso.
  exact (@Build_Retraction C x y f
           (@two_sided_inverse C x y f iso)
           (@is_right_inverse C x y f iso)).
Qed.

(* Every isomorphism is a monomorphism, through its splitting. *)
Lemma iso_in_mono {C : Category} {x y : C} (f : x ~> y) :
  IsoClass x y f → MonoClass x y f.
Proof.
  intros iso.
  exact (split_mono_in_mono f (iso_in_split_mono f iso)).
Qed.

(* Every isomorphism is an epimorphism, through its splitting. *)
Lemma iso_in_epi {C : Category} {x y : C} (f : x ~> y) :
  IsoClass x y f → EpiClass x y f.
Proof.
  intros iso.
  exact (split_epi_in_epi f (iso_in_split_epi f iso)).
Qed.
