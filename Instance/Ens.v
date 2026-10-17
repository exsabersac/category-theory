Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Coq.
Require Import Coq.Sets.Ensembles.

Generalizable All Variables.

(** * The category of ensembles *)

(*
 nLab: https://ncatlab.org/nlab/show/category+of+sets
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_sets

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Cross-reference: Mac Lane's Ens_V — objects the members of a set V of sets,
   arrows ALL functions between them (CWM 2nd ed., §I.2, printed p. 11) — is a
   DIFFERENT construction from the two categories below, and it lives in
   Instance/EnsV.v. There an object is a code x : V decoded by El : V → Type,
   and a morphism x ~> y is an arbitrary function El x → El y with no side
   condition at all; here a morphism carries the constraint A = f⁻¹(B). Both are
   kept: [Ens] and [EnsT] record membership preservation-and-reflection, while
   [EnsV] records Mac Lane's set-sized sub-universe of the category of sets. *)

Program Definition Ens : Category := {|
  obj     := ∃ T : Type, Ensemble T;
  hom     := fun A B =>
    ∃ f : ``A → ``B, ∀ x : ``A, In _ (projT2 A) x ↔ In _ (projT2 B) (f x);
  homset  := fun P Q => {| equiv := fun f g => ∀ x, ``f x = ``g x |};
  id      := fun _ => (id; _);
  compose := fun _ _ _ f g =>  (λ x, ``f (``g x); _)
|}.
Next Obligation. equivalence; rewrite H, H0; reflexivity. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. proper; rewrite H, H0; reflexivity. Qed.

(* nLab: https://ncatlab.org/nlab/show/Set
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_sets

   [EnsT T] is the same construction restricted to a single fixed carrier type
   [T]: objects are the [Ensemble]s (subsets) of [T], and a morphism from [A] to
   [B] is an endofunction [f : T -> T] with [∀ x, x ∈ A ↔ f x ∈ B], i.e.
   [A = f⁻¹(B)]. As above this is membership preservation-and-reflection, not
   injectivity. Morphisms are compared pointwise on [T], with identity and
   composition the identity function and function composition. *)

Program Definition EnsT (T : Type) : Category := {|
  obj     := Ensemble T;
  hom     := fun A B =>
    ∃ f : T → T, ∀ x : T, In _ A x ↔ In _ B (f x);
  homset  := fun P Q => {| equiv := fun f g => ∀ x, ``f x = ``g x |};
  id      := fun _ => (id; _);
  compose := fun _ _ _ f g =>  (λ x, ``f (``g x); _)
|}.
Next Obligation. equivalence; rewrite H, H0; reflexivity. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. proper; rewrite H, H0; reflexivity. Qed.
