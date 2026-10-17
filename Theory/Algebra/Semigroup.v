Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.

Generalizable All Variables.

(** * Internal semigroups in a monoidal category, and the category Smgrp *)

(*
 nLab: https://ncatlab.org/nlab/show/semigroup
   nLab: https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,

   本文件给出半群对象结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Semigroup.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class Semigroup (X : C) : Type := {
  smu : X ⨂ X ~> X;             (* multiplication ν : X ⨂ X ~> X *)

  (* associativity: smu ∘ (smu ⨂ id) ≈ smu ∘ (id ⨂ smu) ∘ α *)
  smu_assoc :
    smu ∘ bimap smu id[X]
      ≈ smu ∘ bimap id[X] smu ∘ to tensor_assoc
}.

End Semigroup.

Arguments smu {C M X _}.

Notation "'smu[' Sg ]" := (@smu _ _ _ Sg)
  (at level 9, format "'smu[' Sg ]") : morphism_scope.

Section SemigroupHom.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class SemigroupHom {x y : C} (Sx : Semigroup x) (Sy : Semigroup y)
      (f : x ~> y) : Type := {
  (* f preserves multiplication: f ∘ smu[Sx] ≈ smu[Sy] ∘ (f ⨂ f) *)
  shom_mu : f ∘ smu[Sx] ≈ smu[Sy] ∘ (f ⨂ f)
}.

(* The identity is a semigroup homomorphism. *)
Lemma SemigroupHom_id {x} (Sx : Semigroup x) : SemigroupHom Sx Sx id.
Proof. constructor; cat. Qed.

(* Semigroup homomorphisms compose: paste the two preservation squares,
   fusing (f ⨂ f) ∘ (g ⨂ g) into (f ∘ g) ⨂ (f ∘ g) by [bimap_comp]. *)
Lemma SemigroupHom_comp {x y z} {Sx : Semigroup x} {Sy : Semigroup y}
      {Sz : Semigroup z} {f : y ~> z} {g : x ~> y} :
  SemigroupHom Sy Sz f → SemigroupHom Sx Sy g → SemigroupHom Sx Sz (f ∘ g).
Proof.
  intros F G.
  constructor.
  rewrite <- comp_assoc.
  rewrite (@shom_mu _ _ _ _ _ G).
  rewrite comp_assoc.
  rewrite (@shom_mu _ _ _ _ _ F).
  rewrite <- comp_assoc.
  now rewrite <- bimap_comp.
Qed.

(* Being a semigroup homomorphism transports along ≈. *)
Lemma SemigroupHom_equiv {x y} {Sx : Semigroup x} {Sy : Semigroup y}
      {f g : x ~> y} :
  f ≈ g → SemigroupHom Sx Sy f → SemigroupHom Sx Sy g.
Proof.
  intros E F.
  constructor.
  rewrite <- E.
  apply (@shom_mu _ _ _ _ _ F).
Qed.

(*
   The 范畴 Smgrp(C) of internal semigroups in C, packaged with sigma

   对象 homs exactly Theory/代数/幺半群/Hom.v packages Mon(C): 态射 等价 is 等价 underlying C-态射.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Smgrp : Category := {|
  obj     := { x : C & Semigroup x };
  hom     := fun X Y => { f : `1 X ~> `1 Y & SemigroupHom `2 X `2 Y f };
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id      := fun X => (id; SemigroupHom_id `2 X);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; SemigroupHom_comp `2 f `2 g)
|}.

(* The forgetful functor Smgrp(C) ⟶ C projects out the underlying object
   and morphism. *)
Program Definition Smgrp_Forget : Smgrp ⟶ C := {|
  fobj := fun X => `1 X;
  fmap := fun _ _ f => `1 f
|}.

(* Faithful by construction, as [Mon_Forget_Faithful] is. *)
#[export] Instance Smgrp_Forget_Faithful : Faithful Smgrp_Forget.
Proof.
  constructor.
  intros X Y f g E.
  exact E.
Qed.

(* Every internal monoid is an internal semigroup: forget the unit. *)
Definition Monoid_Semigroup {x : C} (Mx : Monoid x) : Semigroup x :=
  {| smu := mu[Mx]; smu_assoc := @mu_assoc _ _ _ Mx |}.

(* Every monoid homomorphism is a semigroup homomorphism. *)
Definition MonoidHom_SemigroupHom {x y : C} {Mx : Monoid x} {My : Monoid y}
           {f : x ~> y} (H : MonoidHom Mx My f) :
  SemigroupHom (Monoid_Semigroup Mx) (Monoid_Semigroup My) f :=
  @Build_SemigroupHom _ _ (Monoid_Semigroup Mx) (Monoid_Semigroup My) f
    (@hom_mu _ _ _ _ _ _ _ H).

(* The functor Mon(C) ⟶ Smgrp(C) that forgets the unit. *)
Program Definition Mon_Smgrp : Mon C ⟶ Smgrp := {|
  fobj := fun X => (`1 X; Monoid_Semigroup `2 X);
  fmap := fun _ _ f => (`1 f; MonoidHom_SemigroupHom `2 f)
|}.

(* Forgetting the unit and then the multiplication is forgetting both. *)
Example Mon_Smgrp_Forget_obj (X : Mon C) :
  fobj[Smgrp_Forget] (fobj[Mon_Smgrp] X) = fobj[Mon_Forget] X := eq_refl.

Example Mon_Smgrp_Forget_map {X Y : Mon C} (f : X ~> Y) :
  fmap[Smgrp_Forget] (fmap[Mon_Smgrp] f) = fmap[Mon_Forget] f := eq_refl.

End SemigroupHom.

Arguments Smgrp C {M}.
