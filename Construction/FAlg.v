Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** * The category of F-algebras *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/F-algebra

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   关于the construction的来源与用途

   nLab:      https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor
   Wikipedia: https://en.wikipedia.org/wiki/Catamorphism
   Paper: Lambek, "A Fixpoint Theorem for Complete Categories",
   Paper: Adámek, "Free algebras and automata realizations in the
   Paper: Meijer, Fokkinga, Paterson, "Functional Programming with
   Paper: Rutten, "Universal coalgebra: a theory of systems",

   本节说明始/终对象、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class FAlgHom `(F : C ⟶ C) (a b : C)
      (α : FAlgebra F a) (β : FAlgebra F b) := {
  falg_hom : a ~> b;
  falg_commutes : falg_hom ∘ α ≈ β ∘ fmap[F] falg_hom
}.

Notation "falg_hom[ H ]" := (@falg_hom _ _ _ _ _ _ H)
  (at level 9, format "falg_hom[ H ]") : morphism_scope.

Program Definition FAlg `(F : C ⟶ C) : Category := {|
  obj     := ∃ a : C, FAlgebra F a;
  hom     := fun x y => FAlgHom F ``x ``y (`2 x) (`2 y);
  homset  := fun _ _ => {| equiv := fun f g => falg_hom[f] ≈ falg_hom[g] |};
  id      := fun _ => {| falg_hom := id |};
  compose := fun _ _ _ f g => {| falg_hom := falg_hom[f] ∘ falg_hom[g] |}
|}.
Next Obligation.
  (*
   本节说明单子、Eilenberg–Moore相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite <- falg_commutes.
  rewrite <- !comp_assoc.
  rewrite <- falg_commutes.
  reflexivity.
Qed.

(* The forgetful functor to the underlying category, dropping the structure. *)
Program Definition FAlg_Forget `(F : C ⟶ C) : FAlg F ⟶ C := {|
  fobj := fun x => ``x;
  fmap := fun x y f => falg_hom[f]
|}.
