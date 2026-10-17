Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(*
    nLab:      https://ncatlab.org/nlab/show/dagger+category
    Wikipedia: https://en.wikipedia.org/wiki/Dagger_category
    Book:      Mac Lane, "Categories for the Working Mathematician",
    Book:      Awodey, "Category Theory", 2nd ed., §1.9 Exercise 2
    Paper:     Selinger, "Dagger compact closed categories and

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class DaggerCategory (C : Category) := {
  dagger {x y : C} : (x ~> y) → (y ~> x);

  dagger_respects {x y : C} :
    Proper (equiv ==> equiv) (@dagger x y);

  dagger_involution {x y : C} (f : x ~> y) :
    dagger (dagger f) ≈ f;

  dagger_id {x : C} : dagger (@id C x) ≈ id;

  (* The anti-homomorphism law: reversal exchanges the order of
     composition. *)
  dagger_compose {x y z : C} (f : y ~> z) (g : x ~> y) :
    dagger (f ∘ g) ≈ dagger g ∘ dagger f
}.

#[export] Existing Instance dagger_respects.

Notation "f †" := (dagger f) (at level 30) : morphism_scope.
