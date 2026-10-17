Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.

Generalizable All Variables.

(** The internal-hom functor [-,-] : C^op ∏ C ⟶ C. *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category
   Wikipedia: https://en.wikipedia.org/wiki/Exponential_object

   本文件给出 hom 形式的伴随/同态。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition InternalHomFunctor `(C : Category)
        {E : @Cartesian C} {O : @Closed C _} : C^op ∏ C ⟶ C := {|
  fobj := fun p => @exponent_obj C E O (fst p) (snd p);   (* (a, b) ↦ b ^ a *)
  (* (f, g) ↦ curry (g ∘ eval ∘ second f): pre-compose f, post-compose g *)
  fmap := fun x y '(f, g) => curry (g ∘ eval ∘ second (op f))
|}.
Next Obligation.
  proper; simpl.
  now rewrites.
Qed.
Next Obligation. unfork; cat. Qed.
Next Obligation.
  rewrite <- !comp_assoc.
  rewrite curry_comp.
  symmetry.
  rewrite curry_comp.
  rewrite <- comp_assoc.
  apply compose_respects.
  - reflexivity.
  - symmetry.
    rewrite curry_comp_l.
    rewrite <- !comp_assoc.
    rewrite <- first_second.
    rewrite !comp_assoc.
    rewrite ump_exponents.
    rewrite <- !comp_assoc.
    rewrite <- second_comp.
    reflexivity.
Qed.

(* Shorthand for the internal hom [a, b] = b ^ a as an object of C, with the
   ambient category inferred; this is the internal counterpart of the external
   hom-set Hom(a, b). *)
Notation "a ≈> b":= (InternalHomFunctor _ (a, b))
  (at level 89) : category_scope.
(* As above, but naming the category C explicitly when it cannot be inferred. *)
Notation "a ≈{ C }≈> b":= (InternalHomFunctor C (a, b))
  (at level 89) : category_scope.
