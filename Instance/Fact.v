Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** The factorization category Fact(f) of a morphism. *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Twisted_arrow_category

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Fact `(f : x ~{C}~> y) : Category := {|
  obj := ∃ d (p1 : x ~> d) (p2 : d ~> y), f ≈ p2 ∘ p1;
  hom := fun x y =>
    ∃ h : `1 x ~> `1 y, h ∘ `1 (`2 x) ≈ `1 (`2 y)
                    ∧ `1 (`2 (`2 y)) ∘ h ≈ `1 (`2 (`2 x));
  homset := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id  := fun x => (id[`1 x]; _);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; _)
|}.
Next Obligation.
  intros; simpl in *.
  split.
  - rewrite <- comp_assoc, e, e1; reflexivity.
  - rewrite comp_assoc, e2, e0; reflexivity.
Defined.

Program Definition Fact_Proj `(f : x ~{C}~> y) : Fact f ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ h => `1 h
|}.
