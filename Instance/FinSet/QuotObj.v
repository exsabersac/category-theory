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

(** * Quotient objects of a finite set: the meet that computes *)

(*
 nLab:      https://ncatlab.org/nlab/show/coimage
 nLab:      https://ncatlab.org/nlab/show/FinSet
 Wikipedia: https://en.wikipedia.org/wiki/Quotient_object

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** "Epis are onto" in the skeleton *)

(* Instance/FinSet/Classifier.v's biconditional, both legs.  Unlike
   [Grp], FinSet needs no stability hypothesis: the probe is the
   classifier's own characteristic map into Ω = 2 and the search over a
   finite set is decidable, so the preimage comes back as data. *)
Definition finset_quot_epi_surjective {m : nat} (q : @QuotObj FinSet m) :
  ∀ b : Fin.t (quot_cod q), ∃ a : Fin.t m, quot_epi q a = b :=
  snd (finset_epic_iff_surjective (quot_epi q)) (quot_is_epic q).

Definition finset_quot_of_surjection {m n : nat} (e : m ~{FinSet}~> n)
  (Hs : ∀ b : Fin.t n, ∃ a : Fin.t m, e a = b) : @QuotObj FinSet m :=
  mk_quot e (fst (finset_epic_iff_surjective e) Hs).

(* Not every map presents a quotient object.  Stated positively, because
   a refutation probe on [mk_quot f _] would report an uninstantiated
   evar and not the mathematical refusal: the constant map 1 → 2 is not epic
   (Instance/FinSet/Classifier.v).  This is a verbatim RE-EXPORT of
   that lemma under a name saying what it is used for here; it proves
   nothing new. *)
Definition finset_no_quot_of_const :
  Epic ((fun _ => fin_true) : 1%nat ~{FinSet}~> 2%nat) → False :=
  finset_const_true_not_epic.

(** ** Coimages: FinSet is balanced, so the coimage is the image *)

Section FinSetCoimages.

Context {m n : nat}.
Context (f : Fin.t m → Fin.t n).

(* Instance/FinSet/Subobject.v's [finset_image_factor] is surjective
   onto the image object: the q-th selected element has a preimage
   (that file's [finset_image_witness], with its defining equation), and
   ranking after selecting is the identity
   (Instance/FinSet/Pushout.v's [fin_rank_select]).  [fin_rank_resp]
   discharges the proof argument, so no proof irrelevance and no
   axiom is needed. *)
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

(* The triangle is Instance/FinSet/Subobject.v's
   [finset_image_commutes] VERBATIM: the image factorization read in
   [FinSet^op] is the coimage factorization, no transport. *)
Lemma finset_coimage_commutes :
  sub_mono finset_coimage ∘[FinSet^op] (finset_image_mono f) ≈ f.
Proof. exact (finset_image_commutes f). Qed.

(* Minimality.  A competing quotient e : m ↠ Q through which f factors
   is surjective, so a preimage of each of its points can be chosen; two
   preimages of the same point have the same f-value, hence the same
   rank, and [fin_rank_resp] turns that into the required equation. *)
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

(* As at [Sets], the anonymous record literal is refused here and the
   constructor is named with its category argument explicit. *)
#[export] Instance FinSet_HasCoimages : @HasImages (FinSet^op) :=
  @Build_HasImages (FinSet^op) (fun n m f => @FinSet_CoimageOf m n f).

(** ** Two quotients of the four-element set, and a meet that computes *)

(* The three-element codomain is written with bare [Fin] constructors:
   naming its elements [fin3_0], [fin3_1], [fin3_2] would collide with
   Structure/Limit/Power/Hom.v, and the exhaustive case analysis
   is Instance/FinSet/Regular.v's [fin3_cases], required rather than
   restated (it adds exactly ONE file to this file's closure, its own
   requirements being a subset of what is already here). *)

(* Identify 0 with 1, keeping 2 and 3 apart. *)
Definition finset_merge01 : Fin.t 4 → Fin.t 3 := fun i =>
  if fin_eqb i fin4_0 then Fin.F1
  else if fin_eqb i fin4_1 then Fin.F1
  else if fin_eqb i fin4_2 then Fin.FS Fin.F1
  else Fin.FS (Fin.FS Fin.F1).

(* ... and identify 1 with 2, keeping 0 and 3 apart. *)
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

(* The stub's [quot_meet] at FinSet, which is the PUSHOUT of the two
   epis (Instance/FinSet/Pushout.v, apex by union-find on the
   3 + 3 tagged elements over the four span edges). *)
Definition finset_q_meet : @QuotObj FinSet 4%nat :=
  @quot_meet FinSet FinSet_HasPushouts 4%nat finset_q01 finset_q12.

(* And it COMPUTES.  Merging {0,1} and merging {1,2} together merge
   {0,1,2}, leaving 3 alone: two classes, by [eq_refl] with no tactic.
   This is a statement about the DATA (a natural number), which is why
   Leibniz equality is the right relation here. *)
Example finset_quot_meet_two : quot_cod finset_q_meet = 2%nat := eq_refl.

(* The epi of the meet computes too, on elements of [Fin.t 4]. *)
Example finset_quot_meet_merges_0_2 :
  quot_epi finset_q_meet fin4_0 = quot_epi finset_q_meet fin4_2 := eq_refl.

Example finset_quot_meet_merges_1_2 :
  quot_epi finset_q_meet fin4_1 = quot_epi finset_q_meet fin4_2 := eq_refl.

(* ... and it does not collapse everything: 3 stays apart from 0. *)
Lemma finset_quot_meet_separates_0_3 :
  quot_epi finset_q_meet fin4_0 = quot_epi finset_q_meet fin4_3 → False.
Proof. intro H; discriminate H. Qed.

(* Neither factor alone has two elements, so the meet is a genuine
   coarsening of both. *)
Example finset_q01_three : quot_cod finset_q01 = 3%nat := eq_refl.
Example finset_q12_three : quot_cod finset_q12 = 3%nat := eq_refl.

(* The coimage of a collapsing map, computed: [finset_merge01] hits all
   three elements of its codomain, so its coimage has three elements and
   is the map itself up to the identification of the image with 3. *)
Example finset_coimage_merge01_three :
  quot_cod (finset_coimage finset_merge01) = 3%nat := eq_refl.

(* ... while a map that misses a value has a smaller coimage than its
   codomain: the constant map 4 → 3 has a one-element coimage. *)
Example finset_coimage_const_one :
  quot_cod (finset_coimage (fun _ : Fin.t 4 => (Fin.FS Fin.F1 : Fin.t 3)))
  = 1%nat := eq_refl.
