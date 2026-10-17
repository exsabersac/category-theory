Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Bundled.
Require Import Category.Theory.Skeleton.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Instance.StrictCat.

Generalizable All Variables.

(* * * Skeletality separates 等价 同构 范畴 （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/skeleton
   nLab: https://ncatlab.org/nlab/show/principle+of+equivalence

   本文件给出骨架分离相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Small skeletal categories *)

Lemma One_Skeletal : Skeletal _1.
Proof. intros x y _; now destruct x, y. Qed.

(* 相关说明。 （已译） *)

Lemma Two_Skeletal : Skeletal _2.
Proof.
  intros [] [] i; try reflexivity.
  - destruct (TwoHom_Y_X_absurd (from i)).
  - destruct (TwoHom_Y_X_absurd (to i)).
Qed.

(* * ** The indiscrete 范畴 [bool] not skeletal （已译） *)

Program Definition Indiscrete_iso {A : Type} (x y : A) :
  @Isomorphism (Indiscrete A) x y := {| to := tt; from := tt |}.

Lemma Indiscrete_bool_not_Skeletal : Skeletal (Indiscrete bool) → False.
Proof.
  intro SK.
  pose proof (SK true false (Indiscrete_iso true false)) as H.
  discriminate.
Qed.

(* * ** ... yet it equivalent terminal 范畴 （已译） *)

Program Definition Pick : _1 ⟶ Indiscrete bool := {|
  fobj := fun _ => true;
  fmap := fun _ _ _ => tt
|}.

(* [poly_unit] has no definitional eta, so 单位 component is given a
 [match] rather than [fun _ => iso_id]. Both obligations end in
 [Defined] keep 等价 transparent; unlike
 [skeleton_inclusion_is_equivalence], whose [Defined] is what makes
 [skel_reflect_obj] hold [reflexivity], nothing here depends it.（已译） *)

Program Definition One_Indiscrete_Equivalence :
  EquivalenceOfCategories Pick := {| quasi_inverse := Erase (Indiscrete bool) |}.
Next Obligation.
  exists (fun x => Indiscrete_iso true x).
  intros x y f; now destruct f.
Defined.
Next Obligation.
  exists (fun x => match x as u return (Isomorphism (C:=_1) u ttt) with
                   | ttt => iso_id end).
  intros x y f; now destruct x, y, f.
Defined.

(* Awodey §7.10 Exercise 11, negative half. The statement mentions neither
 [Cat] nor [StrictCat] purpose: phrasing it 同构 [Cat]
 would bump universe level no gain. （已译） *)

Theorem skeletality_is_not_equivalence_invariant :
  { C : Category & { D : Category &
      ((C ≃ D) * Skeletal C * (Skeletal D → False))%type } }.
Proof.
  exists _1, (Indiscrete bool).
  split; [split|].
  - exact (Pick; One_Indiscrete_Equivalence).
  - exact One_Skeletal.
  - exact Indiscrete_bool_not_Skeletal.
Defined.

(* * ** Awodey §7.10 Exercise 12: skeleton non-skeletal 范畴 （已译） *)

Program Definition Indiscrete_bool_Sub : Subcategory (Indiscrete bool) := {|
  sobj := fun x => x = true;
  shom := fun x y ox oy f => True
|}.

Section IndiscreteWitness.
#[local] Obligation Tactic := idtac.

(* The uniqueness obligation needs no decidability [bool] equality: the
 based path space [y = true] contractible, so [destruct] the
 membership 证明 closes it. （已译） *)

Program Definition Indiscrete_bool_Skeleton : Skeleton (Indiscrete bool) := {|
  skel_sub  := Indiscrete_bool_Sub;
  skel_full := fun x y ox oy f => I;
  skel_rep  := fun _ => (true; @eq_refl bool true);
  skel_iso  := fun x => Indiscrete_iso x true;
  skel_uniq := _
|}.
Next Obligation.
  intros x a i; destruct a as [y b]; simpl in *; now destruct b.
Qed.

End IndiscreteWitness.

Example Indiscrete_bool_skeleton_has_one_object :
  ∀ X Y : skel_cat Indiscrete_bool_Skeleton, X = Y.
Proof. intros [x a] [y b]; simpl in *; destruct a, b; reflexivity. Qed.

(* The capstone: skeleton indiscrete 范畴 [bool] IS the
 point, nose — 同构 范畴, not merely an
 等价. （已译） *)

Definition Indiscrete_bool_skeleton_is_One :
  skel_cat Indiscrete_bool_Skeleton ≅[StrictCat] _1 :=
  let e : skel_cat Indiscrete_bool_Skeleton ≃ _1 :=
    Equivalence_trans (skeleton_equivalence Indiscrete_bool_Skeleton)
      (Equivalence_sym (Pick; One_Indiscrete_Equivalence)) in
  skeletal_equivalence_is_isomorphism
    (skeleton_is_skeletal Indiscrete_bool_Skeleton) One_Skeletal (`1 e) (`2 e).
