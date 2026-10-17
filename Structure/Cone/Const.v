Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Construction.Comma.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(*
   Wikipedia: https://en.wikipedia.org/wiki/Cone_(category_theory)
   nLab: https://ncatlab.org/nlab/show/diagonal+functor
   Wikipedia: "At first glance cones seem to be slightly abnormal

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma Cone_Natural_Transform `(F : [J, C]) :
  ∀ N : C, Δ[J](N) ⟹ F ↔ Cone[N] F.
Proof.
  split; intros.
  - construct; [ exact (X x) |].
    abstract(pose proof (naturality[X] _ _ f) as nat;
        simpl in nat;
        rewrite id_right in nat;
             now apply nat).
  - construct.
    + now apply X.
    + abstract(simpl; rewrite id_right; apply cone_coherence).
    + abstract(simpl; rewrite id_right; symmetry; apply cone_coherence).
Defined.

(* See Instance/Cones/Comma.v for the analogous statement upgraded to a
   functorial equivalence Cones F ≅[Cat] (Δ ↓ =(F)) between the whole category
   of cones and the comma category. *)

Lemma Cone_Comma `(F : [J, C]) : (Δ ↓ Δ(F)) ↔ Cone F.
Proof.
  split; simpl.
  - intros [[? ?] f].
    simplify; simpl in *.
    unshelve econstructor; [ exact o | unshelve econstructor ].
    + now apply f.
    + abstract(destruct f; simpl in *; intros x y f;
      rewrite <- (id_right (transform y));
      now apply naturality).
  - intros X.
    destruct X.
    exists (vertex_obj, vertex_obj).
    construct.
    + now apply vertex_map.
    + abstract(simpl;
               rewrite id_right;
               now apply cone_coherence).
    + abstract(simpl;
               rewrite id_right;
               symmetry;
               now apply cone_coherence).
Defined.
