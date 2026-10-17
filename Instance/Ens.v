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

(*
   本节说明 Ens 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

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

(*
   nLab: https://ncatlab.org/nlab/show/Set
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_sets

   本节说明 Ens 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

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
