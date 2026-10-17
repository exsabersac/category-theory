Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/funny+tensor+product

   本文件给出 hom 形式的伴随/同态。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition UFun (B E : Category) : Category := {|
  obj     := B ⟶ E;                    (* objects are functors B ⟶ E *)
  hom     := fun F G =>                 (* unnatural transformations: *)
    ∀ b : B, F b ~{E}~> G b;           (* components only, no square *)
  homset  := fun F G =>                 (* componentwise equivalence *)
    {| equiv := fun τ σ => ∀ b, τ b ≈ σ b |};
  id      := fun _ _ => id;             (* identity, componentwise *)
  compose := fun _ _ _ τ σ b => τ b ∘ σ b  (* composition, componentwise *)
|}.
Next Obligation.
  (* The componentwise equivalence relation; the remaining five obligations
     (properness of composition and the category laws, all componentwise in
     E) are discharged by the global [cat_simpl] obligation tactic once this
     setoid is in place. *)
  equivalence.
  now transitivity (y b).
Qed.

(* Level 0, like the repo's other closed-delimiter notations (e.g. [⟦ n ⟧]
   in Construction/PROP.v): a self-delimited production must be usable in
   function-argument position, which a level-90 production is not. *)
Notation "⟦ B , E ⟧" := (UFun B E)
  (at level 0, format "⟦ B ,  E ⟧") : category_scope.
