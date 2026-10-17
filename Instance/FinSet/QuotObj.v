Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Pushout.
Require Import Category.Instance.FinSet.Regular.
Require Import Category.Instance.FinSet.Subobject.

Generalizable All Variables.

(* * * Quotient 对象 finite set: meet computes （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/coimage
 nLab:      https://ncatlab.org/nlab/show/FinSet
 Wikipedia: https://en.wikipedia.org/wiki/Quotient_object

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

(*
   本节说明 QuotObj 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition finset_quot_epi_surjective {m : nat} (q : @QuotObj FinSet m) :
  ∀ b : Fin.t (quot_cod q), ∃ a : Fin.t m, quot_epi q a = b :=
  snd (finset_epic_iff_surjective (quot_epi q)) (quot_is_epic q).

Definition finset_quot_of_surjection {m n : nat} (e : m ~{FinSet}~> n)
  (Hs : ∀ b : Fin.t n, ∃ a : Fin.t m, e a = b) : @QuotObj FinSet m :=
  mk_quot e (fst (finset_epic_iff_surjective e) Hs).

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition finset_no_quot_of_const :
  Epic ((fun _ => fin_true) : 1%nat ~{FinSet}~> 2%nat) → False :=
  finset_const_true_not_epic.

(* 相关说明。 （已译） *)

Section FinSetCoimages.

Context {m n : nat}.
Context (f : Fin.t m → Fin.t n).

(*
   本节说明拉回/推出、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma finset_coimage_epic :
  Epic (finset_image_factor f : m ~{FinSet}~> finset_image_obj f).
Proof.
  apply (fst (finset_epic_iff_surjective _)).
  intro q.
  exists (finset_image_witness f q).
  unfold finset_image_factor.
  transitivity (fin_rank (finset_hit f) (fin_select (finset_hit f) q)
                  (fin_select_sat (finset_hit f) q)).
  - apply fin_rank_resp.
    exact (finset_image_witness_eq f q).
  - apply fin_rank_select.
Qed.

Definition finset_coimage : @QuotObj FinSet m :=
  mk_quot (finset_image_factor f : m ~{FinSet}~> finset_image_obj f)
    finset_coimage_epic.

(* 相关说明。 （已译） *)
Lemma finset_coimage_commutes :
  sub_mono finset_coimage ∘[FinSet^op] (finset_image_mono f) ≈ f.
Proof. exact (finset_image_commutes f). Qed.

(*
   本节说明 QuotObj 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma finset_coimage_least (w : @QuotObj FinSet m)
  (g : n ~{FinSet^op}~> quot_cod w)
  (Hg : sub_mono w ∘[FinSet^op] g ≈ f) :
  @sub_le (FinSet^op) m finset_coimage w.
Proof.
  exists (fun p => finset_image_factor f
            (`1 (finset_quot_epi_surjective w p))).
  intro a; simpl.
  unfold finset_image_factor.
  apply fin_rank_resp.
  transitivity (g (quot_epi w (`1 (finset_quot_epi_surjective w
                                     (quot_epi w a))))).
  - symmetry; exact (Hg _).
  - rewrite (`2 (finset_quot_epi_surjective w (quot_epi w a))).
    exact (Hg a).
Qed.

Definition FinSet_CoimageOf : @ImageOf (FinSet^op) n m f :=
  @Build_ImageOf (FinSet^op) n m f finset_coimage (finset_image_mono f)
    finset_coimage_commutes finset_coimage_least.

End FinSetCoimages.

(* As at [Sets], anonymous record literal refused here the
 constructor named 范畴 论元 explicit. （已译） *)
#[export] Instance FinSet_HasCoimages : @HasImages (FinSet^op) :=
  @Build_HasImages (FinSet^op) (fun n m f => @FinSet_CoimageOf m n f).

(* 相关说明。 （已译） *)

(*
   本节说明（余）极限、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)
Definition finset_merge01 : Fin.t 4 → Fin.t 3 := fun i =>
  if fin_eqb i fin4_0 then Fin.F1
  else if fin_eqb i fin4_1 then Fin.F1
  else if fin_eqb i fin4_2 then Fin.FS Fin.F1
  else Fin.FS (Fin.FS Fin.F1).

(* 相关说明。 （已译） *)
Definition finset_merge12 : Fin.t 4 → Fin.t 3 := fun i =>
  if fin_eqb i fin4_0 then Fin.F1
  else if fin_eqb i fin4_1 then Fin.FS Fin.F1
  else if fin_eqb i fin4_2 then Fin.FS Fin.F1
  else Fin.FS (Fin.FS Fin.F1).

Lemma finset_merge01_surj :
  ∀ b : Fin.t 3, ∃ a : Fin.t 4, finset_merge01 a = b.
Proof.
  intro b; destruct (fin3_cases b) as [H|[H|H]]; subst.
  - exists fin4_0; reflexivity.
  - exists fin4_2; reflexivity.
  - exists fin4_3; reflexivity.
Qed.

Lemma finset_merge12_surj :
  ∀ b : Fin.t 3, ∃ a : Fin.t 4, finset_merge12 a = b.
Proof.
  intro b; destruct (fin3_cases b) as [H|[H|H]]; subst.
  - exists fin4_0; reflexivity.
  - exists fin4_1; reflexivity.
  - exists fin4_3; reflexivity.
Qed.

Definition finset_q01 : @QuotObj FinSet 4%nat :=
  finset_quot_of_surjection finset_merge01 finset_merge01_surj.

Definition finset_q12 : @QuotObj FinSet 4%nat :=
  finset_quot_of_surjection finset_merge12 finset_merge12_surj.

(* 相关说明。 （已译） *)
Definition finset_q_meet : @QuotObj FinSet 4%nat :=
  @quot_meet FinSet FinSet_HasPushouts 4%nat finset_q01 finset_q12.

(*
   本节说明 QuotObj 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example finset_quot_meet_two : quot_cod finset_q_meet = 2%nat := eq_refl.

(* 相关说明。 （已译） *)
Example finset_quot_meet_merges_0_2 :
  quot_epi finset_q_meet fin4_0 = quot_epi finset_q_meet fin4_2 := eq_refl.

Example finset_quot_meet_merges_1_2 :
  quot_epi finset_q_meet fin4_1 = quot_epi finset_q_meet fin4_2 := eq_refl.

(* 相关说明。 （已译） *)
Lemma finset_quot_meet_separates_0_3 :
  quot_epi finset_q_meet fin4_0 = quot_epi finset_q_meet fin4_3 → False.
Proof. intro H; discriminate H. Qed.

(* Neither factor alone has two elements, so the meet is a genuine
   coarsening of both. *)
Example finset_q01_three : quot_cod finset_q01 = 3%nat := eq_refl.
Example finset_q12_three : quot_cod finset_q12 = 3%nat := eq_refl.

(*
   本节说明 QuotObj 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example finset_coimage_merge01_three :
  quot_cod (finset_coimage finset_merge01) = 3%nat := eq_refl.

(* ... while map misses value has smaller coimage than its
 codomain: 常值 map 4 → 3 has one-element coimage. （已译） *)
Example finset_coimage_const_one :
  quot_cod (finset_coimage (fun _ : Fin.t 4 => (Fin.FS Fin.F1 : Fin.t 3)))
  = 1%nat := eq_refl.
