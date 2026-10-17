Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Free.Quiver.
From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(* * * Two 函子 between free 范畴, agreeing 对象 （已译） *)

(*
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   nLab: https://ncatlab.org/nlab/show/free+category

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The two quivers *)

(* Two nodes, with decidable equality. *)
Inductive fs_node : Type := fs_dom | fs_cod.

Definition fs_node_eq_dec (x y : fs_node) : {x = y} + {x <> y}.
Proof.
  destruct x, y.
  - now left.
  - now right.
  - now right.
  - now left.
Defined.

(* One arrow from [fs_dom] to [fs_cod] ... *)
Inductive fs_one_edge : fs_node → fs_node → Type :=
  | fs_gen : fs_one_edge fs_dom fs_cod.

(* 相关说明。 （已译） *)
Inductive fs_two_edges : fs_node → fs_node → Type :=
  | fs_left  : fs_two_edges fs_dom fs_cod
  | fs_right : fs_two_edges fs_dom fs_cod.

Definition WalkingArrowQuiver : Quiver :=
  Build_Quiver_Standard_Eq fs_node fs_one_edge.

Definition ParallelPairQuiver : Quiver :=
  Build_Quiver_Standard_Eq fs_node fs_two_edges.

Definition FreeWalkingArrow : Category := FreeOnQuiver WalkingArrowQuiver.

Definition FreeParallelPair : Category := FreeOnQuiver ParallelPairQuiver.

(** ** The two functors *)

(* 相关说明。 （已译） *)
Definition free_pick_left_hom :
  QuiverHomomorphism WalkingArrowQuiver (QuiverOfCat FreeParallelPair).
Proof.
  unshelve notypeclasses refine
    (Build_QuiverHomomorphism WalkingArrowQuiver (QuiverOfCat FreeParallelPair)
       (fun n => n)
       (fun _ _ e => match e with fs_gen => tlist_singleton fs_left end) _).
  intros x y e e' He.
  rewrite He.
  reflexivity.
Defined.

(* ... or to the right one.  Nothing else changes. *)
Definition free_pick_right_hom :
  QuiverHomomorphism WalkingArrowQuiver (QuiverOfCat FreeParallelPair).
Proof.
  unshelve notypeclasses refine
    (Build_QuiverHomomorphism WalkingArrowQuiver (QuiverOfCat FreeParallelPair)
       (fun n => n)
       (fun _ _ e => match e with fs_gen => tlist_singleton fs_right end) _).
  intros x y e e' He.
  rewrite He.
  reflexivity.
Defined.

Definition FreePickLeft : FreeWalkingArrow ⟶ FreeParallelPair :=
  InducedFunctor WalkingArrowQuiver free_pick_left_hom.

Definition FreePickRight : FreeWalkingArrow ⟶ FreeParallelPair :=
  InducedFunctor WalkingArrowQuiver free_pick_right_hom.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma free_two_functors_same_objects :
  fobj[FreePickLeft] = fobj[FreePickRight].
Proof. reflexivity. Qed.

(* * ** The generator, where two 函子 send it （已译） *)

(* A 函子 induced quiver homomorphism sends one-edge path to
 chosen image edge: induction defining [InducedFunctor]
 contributes 恒等 empty tail. （已译） *)
Lemma fmap_free_singleton {G : Quiver} {C : Category}
  (F : QuiverHomomorphism G (QuiverOfCat C)) {x y : G} (e : edges x y) :
  fmap[InducedFunctor G F] (tlist_singleton e) ≈ @fedgemap _ _ F x y e.
Proof.
  simpl.
  apply id_left.
Qed.

Example free_pick_left_generator :
  fmap[FreePickLeft] (tlist_singleton fs_gen) ≈ tlist_singleton fs_left.
Proof. apply (fmap_free_singleton free_pick_left_hom fs_gen). Qed.

Example free_pick_right_generator :
  fmap[FreePickRight] (tlist_singleton fs_gen) ≈ tlist_singleton fs_right.
Proof. apply (fmap_free_singleton free_pick_right_hom fs_gen). Qed.

(** ** The separation *)

(* 相关说明。 （已译） *)
Lemma fs_singleton_distinct :
  @equiv _ (@homset FreeParallelPair fs_dom fs_cod)
    (tlist_singleton fs_left) (tlist_singleton fs_right) → False.
Proof.
  simpl.
  unfold tlist_quiver_equiv, tlist_singleton.
  simpl.
  intros [q Hedge _].
  rewrite (UIP_dec fs_node_eq_dec q eq_refl) in Hedge.
  assert (Hlr : fs_left = fs_right) by exact Hedge.
  discriminate.
Qed.

(* 相关说明。 （已译） *)
Theorem free_two_functors_differ_on_generator :
  fmap[FreePickLeft] (tlist_singleton fs_gen)
    ≈ fmap[FreePickRight] (tlist_singleton fs_gen) → False.
Proof.
  intro H.
  apply fs_singleton_distinct.
  rewrite <- free_pick_left_generator.
  rewrite <- free_pick_right_generator.
  exact H.
Qed.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem free_two_functors_distinct :
  @equiv _ (@Functor_StrictEq_Setoid FreeWalkingArrow FreeParallelPair)
    FreePickLeft FreePickRight → False.
Proof.
  intros [eq_on_obj coherent].
  pose proof (coherent fs_dom fs_cod (tlist_singleton fs_gen)) as Hc.
  rewrite (UIP_dec fs_node_eq_dec (eq_on_obj fs_dom) eq_refl),
          (UIP_dec fs_node_eq_dec (eq_on_obj fs_cod) eq_refl) in Hc.
  (* 相关说明。 （已译） *)
  apply free_two_functors_differ_on_generator.
  exact Hc.
Qed.
