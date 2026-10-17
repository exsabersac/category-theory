Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Comma.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** The slice (over) category C/c and coslice (under) category c/C. *)

(*
   nLab: https://ncatlab.org/nlab/show/under+category
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab: https://ncatlab.org/nlab/show/locally+cartesian+closed+category
   nLab: https://ncatlab.org/nlab/show/codomain+fibration
   nLab: https://ncatlab.org/nlab/show/fundamental+theorem+of+topos+theory
   nLab: https://ncatlab.org/nlab/show/coreader+comonad
   Wikipedia:
   https://en.wikipedia.org/wiki/Grothendieck%27s_relative_point_of_view

   本节说明函子、Lawvere 理论相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Slice `(C : Category) `(c : C) : Category := {|
  obj     := ∃ a : C, a ~> c;
  hom     := fun x y => ∃ f : (`1 x) ~> (`1 y), `2 y ∘ f ≈ `2 x;
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |} ;
  id      := fun _ => (id; _);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; _)
|}.
Next Obligation. rewrite comp_assoc; rewrites; reflexivity. Defined.

Notation "C  ̸ c" := (@Slice C c) (at level 90) : category_scope.

(* Although the encoding of Slice above is more convenient, theoretically it's
   the comma category (Id[C] ↓ Δ(c)). *)

#[local] Set Transparent Obligations.

#[export]
Program Instance Comma_Slice `(C : Category) `(c : C) :
  C ̸ c ≅[Cat] (Id ↓ =(c)) := {
  to   := {| fobj := _; fmap := _ |};
  from := {| fobj := _; fmap := _ |}
}.
Next Obligation.
  destruct p, p0; simpl.
  exists h.
  rewrites; cat.
Defined.
Next Obligation.
  proper; simpl.
  now destruct H0, H1, p; simpl.
Qed.
Next Obligation.
  now destruct p.
Qed.
Next Obligation.
  now destruct p, p0, p1, p2.
Qed.
Next Obligation.
  constructive; simplify; simpl in *; cat.
  - destruct H, H0; simpl; cat.
  - destruct H, H0; cat.
Qed.
Next Obligation.
  constructive; simplify; simpl in *; cat.
Qed.

Program Definition Coslice `(C : Category) `(c : C) : Category := {|
  obj     := ∃ a : C, c ~> a;
  hom     := fun x y => ∃ f : (`1 x) ~> (`1 y), `2 y ≈ f ∘ `2 x;
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |} ;
  id      := fun _ => (id; _);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; _)
|}.
Next Obligation. rewrite <- comp_assoc; rewrites; reflexivity. Defined.

Notation "c  ̸co C" := (@Coslice C c) (at level 90) : category_scope.

#[export]
Program Instance Comma_Coslice `(C : Category) `(c : C) :
  c ̸co C ≅[Cat] (=(c) ↓ Id) := {
  to   := {| fobj := _; fmap := _ |};
  from := {| fobj := _; fmap := _ |}
}.
Next Obligation.
  destruct p, p0; simpl.
  exists h.
  rewrites; cat.
Defined.
Next Obligation.
  proper; simpl.
  now destruct x0, x1, p; simpl.
Qed.
Next Obligation.
  now destruct p.
Qed.
Next Obligation.
  now destruct p, p0, p1, p2.
Qed.
Next Obligation.
  constructive; simplify; simpl in *; cat.
  - destruct x0, x1; simpl; cat.
  - destruct x0, x1; simpl; cat.
Qed.
Next Obligation.
  constructive; simplify; simpl in *; cat.
Qed.
