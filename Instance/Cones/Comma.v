Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Construction.Comma.
Require Import Category.Instance.Cones.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(* * * The 范畴 cones over F comma 范畴 (Δ ↓ F) （已译） *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Cone_(category_theory)

   本文件给出逗号范畴实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem Cones_to_Comma `(F : [J, C]) : Cones F ⟶ (Δ ↓ =(F)).
Proof.
  functor; simpl; intros.
  - exists (vertex_obj[X], ttt).
    transform; simpl; intros.
    + apply @vertex_map. exact (@coneFrom _ _ _ X).
    + abstract (rewrite id_right; apply cone_coherence).
    + abstract (rewrite id_right; symmetry; apply cone_coherence).
  - exists (`1 f, ttt); abstract (simpl; intros; cat).
  - abstract proper.
  - abstract cat.
  - abstract cat.
Defined.

Theorem Cones_from_Comma `(F : [J, C]) : (Δ ↓ =(F)) ⟶ Cones F.
Proof.
  functor; simpl; intros.
  - construct; simpl; intros.
    + exact (fst ``X).
    + exists (transform[`2 X]). abstract (intros; rewrite (naturality[`2 X]); cat).
  - destruct f; simpl in *.
    exists (fst x0); abstract (intros; rewrite e; cat).
  - abstract proper.
  - abstract cat.
  - abstract cat.
Defined.

(*
   nLab: https://ncatlab.org/nlab/show/comma+category
   Wikipedia: https://en.wikipedia.org/wiki/Cone_(category_theory)

   本节说明自然变换、函子、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem Cones_Comma `(F : [J, C]) : Cones F ≅[Cat] (Δ ↓ =(F)).
Proof.
  isomorphism; simpl; intros.
  - apply Cones_to_Comma.
  - apply Cones_from_Comma.
  - constructive.
    + exists (id, ttt); abstract cat.
    + exists (id, ttt); abstract cat.
    + abstract (simpl; cat).
    + abstract (simpl; cat).
    + abstract (simpl; cat).
  - constructive.
    + exists id; abstract (intros; cat).
    + exists id; abstract (intros; cat).
    + abstract (simpl; cat).
    + abstract (simpl; cat).
    + abstract (simpl; cat).
Qed.
