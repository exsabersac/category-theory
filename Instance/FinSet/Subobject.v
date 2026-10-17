Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.Topos.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Powerset.
Require Import Category.Instance.FinSet.Topos.


Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/image
 Wikipedia: https://en.wikipedia.org/wiki/Image_(category_theory)
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.
 Book:      Fong and Spivak, "Seven Sketches in Compositionality",

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Lemma FinSet_zero_monic (x : FinSet) : Monic (@zero FinSet FinSet_Initial x).
Proof.
  constructor; intros z g1 g2 _ i.
  exact (Fin.case0 (fun _ => g1 i = g2 i) (g1 i)).
Qed.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section FinSetImages.

Context {m n : nat}.
Context (f : Fin.t m → Fin.t n).

(*
   本节说明 Subobject 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition finset_hit : Fin.t n → bool :=
  fun k => fin_existsb (fun a : Fin.t m => fin_eqb (f a) k).

Definition finset_image_obj : nat := fin_countP finset_hit.

Definition finset_image_mono : Fin.t finset_image_obj → Fin.t n :=
  fin_select finset_hit.

Lemma finset_image_monic : Monic (finset_image_mono : _ ~{FinSet}~> _).
Proof.
  constructor; intros z g1 g2 Hg i.
  exact (fin_select_inj finset_hit (g1 i) (g2 i) (Hg i)).
Qed.

Definition finset_image_sub : @SubObj FinSet n :=
  @Build_SubObj FinSet n finset_image_obj finset_image_mono
    finset_image_monic.

Lemma finset_hit_value (a : Fin.t m) : finset_hit (f a) = true.
Proof.
  exact (fin_existsb_complete (fun b : Fin.t m => fin_eqb (f b) (f a)) a
           (fin_eqb_refl (f a))).
Qed.

Definition finset_image_factor : Fin.t m → Fin.t finset_image_obj :=
  fun a => fin_rank finset_hit (f a) (finset_hit_value a).

Lemma finset_image_commutes :
  (finset_image_mono : _ ~{FinSet}~> _) ∘ finset_image_factor ≈ f.
Proof. intro a; apply fin_select_rank. Qed.

(* 相关说明。 （已译） *)
Definition finset_image_witness (q : Fin.t finset_image_obj) : Fin.t m :=
  `1 (fin_existsb_sound
        (fun a : Fin.t m => fin_eqb (f a) (fin_select finset_hit q))
        (fin_select_sat finset_hit q)).

Lemma finset_image_witness_eq (q : Fin.t finset_image_obj) :
  f (finset_image_witness q) = fin_select finset_hit q.
Proof.
  apply fin_eqb_eq.
  exact (`2 (fin_existsb_sound
               (fun a : Fin.t m => fin_eqb (f a) (fin_select finset_hit q))
               (fin_select_sat finset_hit q))).
Qed.

Lemma finset_image_least (w : @SubObj FinSet n)
  (g : Fin.t m → Fin.t (sub_dom w)) (Hg : sub_mono w ∘ g ≈ f) :
  sub_le finset_image_sub w.
Proof.
  exists (fun q => g (finset_image_witness q)).
  intro q; simpl.
  transitivity (f (finset_image_witness q)).
  - exact (Hg (finset_image_witness q)).
  - exact (finset_image_witness_eq q).
Defined.

Definition FinSet_ImageOf : ImageOf (f : _ ~{FinSet}~> _) :=
  @Build_ImageOf FinSet m n f finset_image_sub finset_image_factor
    finset_image_commutes finset_image_least.

End FinSetImages.

#[export] Instance FinSet_HasImages : HasImages FinSet :=
  @Build_HasImages FinSet (@FinSet_ImageOf).

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Definition fin4_0 : Fin.t 4 := Fin.F1.
Definition fin4_1 : Fin.t 4 := Fin.FS Fin.F1.
Definition fin4_2 : Fin.t 4 := Fin.FS (Fin.FS Fin.F1).
Definition fin4_3 : Fin.t 4 := Fin.FS (Fin.FS (Fin.FS Fin.F1)).

(* {0,1} {1,2,3} inside 4-element ambient 对象, cut out by
 decidable predicates so [fin_select_inj] supplies monicity the
 domains counts REDUCE. （已译） *)
Definition ex11_u_pred : Fin.t 4 → bool :=
  fun i => (fin_eqb i fin4_0 || fin_eqb i fin4_1)%bool.

Definition ex11_v_pred : Fin.t 4 → bool :=
  fun i => (fin_eqb i fin4_1 || fin_eqb i fin4_2 || fin_eqb i fin4_3)%bool.

Lemma ex11_u_monic : Monic (fin_select ex11_u_pred : _ ~{FinSet}~> _).
Proof.
  constructor; intros z g1 g2 Hg i.
  exact (fin_select_inj ex11_u_pred (g1 i) (g2 i) (Hg i)).
Qed.

Lemma ex11_v_monic : Monic (fin_select ex11_v_pred : _ ~{FinSet}~> _).
Proof.
  constructor; intros z g1 g2 Hg i.
  exact (fin_select_inj ex11_v_pred (g1 i) (g2 i) (Hg i)).
Qed.

Definition ex11_u : @SubObj FinSet 4%nat :=
  @Build_SubObj FinSet 4%nat (fin_countP ex11_u_pred)
    (fin_select ex11_u_pred) ex11_u_monic.

Definition ex11_v : @SubObj FinSet 4%nat :=
  @Build_SubObj FinSet 4%nat (fin_countP ex11_v_pred)
    (fin_select ex11_v_pred) ex11_v_monic.

Example ex11_u_size : sub_dom ex11_u = 2%nat := eq_refl.
Example ex11_v_size : sub_dom ex11_v = 3%nat := eq_refl.

(* MERGING: union inside ambient 4-element 对象 has four
 elements. （已译） *)
Example ex11_union_four :
  sub_dom (sub_join ex11_u ex11_v) = 4%nat := eq_refl.

(* 相关说明。 （已译） *)
Example ex11_coproduct_five :
  @Coprod FinSet FinSet_Cocartesian 2%nat 3%nat = 5%nat := eq_refl.

(* The intersection has one element. *)
Example ex11_meet_one :
  sub_dom (sub_meet ex11_u ex11_v) = 1%nat := eq_refl.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Example finset_pow_three : @Pow FinSet FinSet_Topos 3%nat = 8%nat := eq_refl.

Example finset_product_two_three :
  @product_obj FinSet FinSet_Cartesian 2%nat 3%nat = 6%nat := eq_refl.

(* 相关说明。 （已译） *)

(*
   本节说明 Subobject 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example finpow_two_is_Pow : finpow 2%nat = @Pow FinSet FinSet_Topos 2%nat
  := eq_refl.

Definition powcode2_0 : Fin.t (finpow 2) := Fin.F1.
Definition powcode2_1 : Fin.t (finpow 2) := Fin.FS Fin.F1.
Definition powcode2_2 : Fin.t (finpow 2) := Fin.FS (Fin.FS Fin.F1).
Definition powcode2_3 : Fin.t (finpow 2) := Fin.FS (Fin.FS (Fin.FS Fin.F1)).

Definition fin2_0 : Fin.t 2 := Fin.F1.
Definition fin2_1 : Fin.t 2 := Fin.FS Fin.F1.

Example powcode2_0_at_0 : finpow_mem powcode2_0 fin2_0 = true  := eq_refl.
Example powcode2_0_at_1 : finpow_mem powcode2_0 fin2_1 = true  := eq_refl.
Example powcode2_1_at_0 : finpow_mem powcode2_1 fin2_0 = true  := eq_refl.
Example powcode2_1_at_1 : finpow_mem powcode2_1 fin2_1 = false := eq_refl.
Example powcode2_2_at_0 : finpow_mem powcode2_2 fin2_0 = false := eq_refl.
Example powcode2_2_at_1 : finpow_mem powcode2_2 fin2_1 = true  := eq_refl.
Example powcode2_3_at_0 : finpow_mem powcode2_3 fin2_0 = false := eq_refl.
Example powcode2_3_at_1 : finpow_mem powcode2_3 fin2_1 = false := eq_refl.
