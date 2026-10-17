Require Import Coq.Vectors.Fin.
Require Import Coq.Logic.Eqdep_dec.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Bicartesian.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.Semiadditive.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Product.Finite.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(*
   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Set Default Proof Using "All".

(* * * Matrices 态射 between finite coproducts products （已译） *)

(*
   nLab:      https://ncatlab.org/nlab/show/biproduct
   nLab:      https://ncatlab.org/nlab/show/matrix+calculus
   Wikipedia: https://en.wikipedia.org/wiki/Biproduct

   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Entries *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition mat_entry@{uo uh up uj uk} {C : Category@{uo uh up}}
  {J : Type@{uj}} {K : Type@{uk}} {g : J → C} {fam : K → C} {q p : C}
  (inj : ∀ j : J, g j ~> q) (proj : ∀ k : K, p ~> fam k)
  (u : q ~> p) (j : J) (k : K) : g j ~> fam k :=
  proj k ∘ u ∘ inj j.

Example mat_entry_unfold {C : Category} {J K : Type} {g : J → C}
  {fam : K → C} {q p : C} (inj : ∀ j : J, g j ~> q)
  (proj : ∀ k : K, p ~> fam k) (u : q ~> p) (j : J) (k : K) :
  mat_entry inj proj u j k = proj k ∘ u ∘ inj j := eq_refl.

(* 相关说明。 （已译） *)

Section Matrix.

Context {C : Category}.
Context {J K : Type}.
Context {g : J → C}.
Context {fam : K → C}.
Context {q : C}.
Context {inj : ∀ j : J, g j ~> q}.
Context {p : C}.
Context {proj : ∀ k : K, p ~> fam k}.
Context (HQ : IsIndexedCoproduct g q inj).
Context (HP : IsIndexedProduct fam p proj).

(* Two 态射 进入 product agree all projections do: both
 factor same family through universal one. （已译） *)
Lemma iprod_ext {c : C} (a b : c ~> p) :
  (∀ k : K, proj k ∘ a ≈ proj k ∘ b) → a ≈ b.
Proof.
  intro H.
  pose proof (iprod_desc HP (fun k => proj k ∘ a)) as D.
  transitivity (unique_obj D).
  - symmetry.
    apply (uniqueness D).
    intro k; reflexivity.
  - apply (uniqueness D).
    intro k; symmetry; apply H.
Qed.

(* Dually 态射 out coproduct. （已译） *)
Lemma icoprod_ext {c : C} (a b : q ~> c) :
  (∀ j : J, a ∘ inj j ≈ b ∘ inj j) → a ≈ b.
Proof.
  intro H.
  pose proof (icoprod_desc HQ (fun j => a ∘ inj j)) as D.
  transitivity (unique_obj D).
  - symmetry.
    apply (uniqueness D).
    intro j; reflexivity.
  - apply (uniqueness D).
    intro j; symmetry; apply H.
Qed.

(*
   本节说明 Matrix 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem matrix_ext (u v : q ~> p) :
  (∀ (j : J) (k : K),
     mat_entry inj proj u j k ≈ mat_entry inj proj v j k) → u ≈ v.
Proof.
  intro H.
  apply icoprod_ext; intro j.
  apply iprod_ext; intro k.
  rewrite !comp_assoc.
  exact (H j k).
Qed.

Corollary matrix_determined (u v : q ~> p) :
  u ≈ v ↔ (∀ (j : J) (k : K),
             mat_entry inj proj u j k ≈ mat_entry inj proj v j k).
Proof.
  split.
  - intros Huv j k.
    unfold mat_entry.
    now rewrite Huv.
  - apply matrix_ext.
Qed.

(* 相关说明。 （已译） *)
Definition matrix_row (e : ∀ (j : J) (k : K), g j ~> fam k) (j : J) :
  g j ~> p := unique_obj (iprod_desc HP (e j)).

Lemma matrix_row_commutes (e : ∀ (j : J) (k : K), g j ~> fam k)
  (j : J) (k : K) : proj k ∘ matrix_row e j ≈ e j k.
Proof. exact (unique_property (iprod_desc HP (e j)) k). Qed.

(* The 态射 prescribed entries: cotuple rows. （已译） *)
Definition matrix_mor (e : ∀ (j : J) (k : K), g j ~> fam k) : q ~> p :=
  unique_obj (icoprod_desc HQ (matrix_row e)).

Lemma matrix_mor_inj (e : ∀ (j : J) (k : K), g j ~> fam k) (j : J) :
  matrix_mor e ∘ inj j ≈ matrix_row e j.
Proof. exact (unique_property (icoprod_desc HQ (matrix_row e)) j). Qed.

Theorem matrix_entry (e : ∀ (j : J) (k : K), g j ~> fam k)
  (j : J) (k : K) : mat_entry inj proj (matrix_mor e) j k ≈ e j k.
Proof.
  unfold mat_entry.
  rewrite <- comp_assoc.
  rewrite matrix_mor_inj.
  apply matrix_row_commutes.
Qed.

(* The correspondence one statement: matrices 态射. （已译） *)
Theorem matrix_ump (e : ∀ (j : J) (k : K), g j ~> fam k) :
  ∃! u : q ~> p, ∀ (j : J) (k : K), mat_entry inj proj u j k ≈ e j k.
Proof.
  unshelve eapply Build_Unique.
  - exact (matrix_mor e).
  - exact (matrix_entry e).
  - intros v Hv.
    apply matrix_ext; intros j k.
    rewrite matrix_entry.
    symmetry; apply Hv.
Defined.

(* The other round trip: reading 态射's entries rebuilding it
 returns it (up ≈; see header what refuted strictly). （已译） *)
Theorem matrix_mor_entry (u : q ~> p) :
  matrix_mor (mat_entry inj proj u) ≈ u.
Proof. apply matrix_ext; intros j k; apply matrix_entry. Qed.

End Matrix.

(** ** The Kronecker delta *)

Section KroneckerDelta.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context {A : Type}.
Context (fam : A → C).
Context (dec : ∀ a b : A, {a = b} + {a <> b}).

(*
   本节说明 Matrix 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition kron (j k : A) : fam j ~> fam k :=
  match dec j k with
  | Specif.left e  => eq_rect j (fun k' : A => fam j ~> fam k') id k e
  | Specif.right _ => zero_mor
  end.

(* Uniqueness of identity proofs on a type with decidable equality is
   Hedberg's theorem, [UIP_dec], which is axiom-free. *)
Lemma kron_diag (j : A) : kron j j ≈ id.
Proof.
  unfold kron.
  destruct (dec j j) as [e|ne].
  - now rewrite (UIP_dec dec e eq_refl).
  - now contradiction ne.
Qed.

Lemma kron_off (j k : A) : j <> k → kron j k ≈ zero_mor.
Proof.
  intro Hne.
  unfold kron.
  destruct (dec j k) as [e|ne].
  - contradiction.
  - reflexivity.
Qed.

End KroneckerDelta.

(*
   本节说明 Matrix 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example kron_off_computes {C : Category} `{Z : @ZeroObject C}
  (fam : Fin.t 2 → C) :
  kron fam Fin.eq_dec Fin.F1 (Fin.FS Fin.F1) = zero_mor := eq_refl.

(* * ** The 恒等 matrix canonical comparison （已译） *)

Section IdentityMatrix.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context {A : Type}.
Context (fam : A → C).
Context (dec : ∀ a b : A, {a = b} + {a <> b}).
Context {q : C}.
Context {inj : ∀ a : A, fam a ~> q}.
Context {p : C}.
Context {proj : ∀ a : A, p ~> fam a}.
Context (HQ : IsIndexedCoproduct fam q inj).
Context (HP : IsIndexedProduct fam p proj).

Definition can_matrix : q ~> p := matrix_mor HQ HP (kron fam dec).

Theorem can_matrix_diag (j : A) : mat_entry inj proj can_matrix j j ≈ id.
Proof.
  unfold can_matrix.
  rewrite matrix_entry.
  apply kron_diag.
Qed.

Theorem can_matrix_off (j k : A) :
  j <> k → mat_entry inj proj can_matrix j k ≈ zero_mor.
Proof.
  intro Hne.
  unfold can_matrix.
  rewrite matrix_entry.
  now apply kron_off.
Qed.

(* The 恒等 matrix determines comparison: any 态射 those
 entries it. （已译） *)
Theorem can_matrix_unique (u : q ~> p) :
  (∀ j : A, mat_entry inj proj u j j ≈ id) →
  (∀ j k : A, j <> k → mat_entry inj proj u j k ≈ zero_mor) →
  u ≈ can_matrix.
Proof.
  intros Hd Ho.
  apply (matrix_ext HQ HP); intros j k.
  destruct (dec j k) as [e|ne].
  - destruct e.
    rewrite can_matrix_diag.
    apply Hd.
  - rewrite (can_matrix_off _ _ ne).
    now apply Ho.
Qed.

Theorem can_matrix_ump :
  ∃! u : q ~> p,
    (∀ j : A, mat_entry inj proj u j j ≈ id) *
    (∀ j k : A, j <> k → mat_entry inj proj u j k ≈ zero_mor).
Proof.
  unshelve eapply Build_Unique.
  - exact can_matrix.
  - exact (can_matrix_diag, can_matrix_off).
  - intros v [Hd Ho].
    symmetry.
    now apply can_matrix_unique.
Defined.

End IdentityMatrix.

(* 相关说明。 （已译） *)

Section IndexedInjections.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context {A : Type}.
Context (fam : A → C).
Context (dec : ∀ a b : A, {a = b} + {a <> b}).
Context {q : C}.
Context {inj : ∀ a : A, fam a ~> q}.
Context (HQ : IsIndexedCoproduct fam q inj).

(* 相关说明。 （已译） *)
Definition inj_retract (j : A) : q ~> fam j :=
  unique_obj (icoprod_desc HQ (fun k => kron fam dec k j)).

Lemma inj_retract_commutes (j k : A) :
  inj_retract j ∘ inj k ≈ kron fam dec k j.
Proof.
  exact (unique_property
           (icoprod_desc HQ (fun k => kron fam dec k j)) k).
Qed.

Lemma inj_retract_id (j : A) : inj_retract j ∘ inj j ≈ id.
Proof.
  rewrite inj_retract_commutes.
  apply kron_diag.
Qed.

Definition indexed_inj_Section (j : A) : Section (inj j) :=
  {| section := inj_retract j; section_comp := inj_retract_id j |}.

Definition indexed_inj_SplitMono (j : A) : SplitMono (inj j) :=
  indexed_inj_Section j.

Definition indexed_inj_Monic (j : A) : Monic (inj j) :=
  sections_are_monic _ _ _ (indexed_inj_Section j).

End IndexedInjections.

(* 相关说明。 （已译） *)

Section CoproductInjections.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{CC : @Cocartesian C}.
Context (x y : C).

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition inl_Section : Section (@inl C CC x y) :=
  {| section := id ▽ zero_mor; section_comp := inl_merge id zero_mor |}.

Definition inr_Section : Section (@inr C CC x y) :=
  {| section := zero_mor ▽ id; section_comp := inr_merge zero_mor id |}.

Definition inl_SplitMono : SplitMono (@inl C CC x y) := inl_Section.
Definition inr_SplitMono : SplitMono (@inr C CC x y) := inr_Section.

Definition inl_Monic : Monic (@inl C CC x y) :=
  sections_are_monic _ _ _ inl_Section.

Definition inr_Monic : Monic (@inr C CC x y) :=
  sections_are_monic _ _ _ inr_Section.

End CoproductInjections.

(* 相关说明。 （已译） *)

(* The 对偶 [fin2_legs]: pair 态射 INTO common target,
 indexed over [Fin.t 2]. It is [fin2_legs] read C^op, which is why the
 binary 余积 实例 below is one-line instantiation.（已译） *)
Definition fin2_colegs {C : Category} {a x y : C} (f : x ~> a) (g : y ~> a) :
  ∀ i : Fin.t 2, fin2fam x y i ~> a :=
  @fin2_legs (C^op) a x y f g.

Definition binary_IsIndexedProduct {C : Category}
  (CP : @Cartesian C) (x y : C) :
  IsIndexedProduct (fin2fam x y) (x × y)%object (fin2_legs exl exr).
Proof.
  apply Build_IsIndexedProduct.
  intros c pi.
  unshelve eapply Build_Unique.
  - exact (pi Fin.F1 △ pi (Fin.FS Fin.F1)).
  - intro i.
    pattern i; apply (Fin.caseS' i); simpl.
    + apply exl_fork.
    + intro j.
      pattern j; apply (Fin.caseS' j); simpl.
      * apply exr_fork.
      * intro k; apply (Fin.case0 (fun _ => _) k).
  - intros v Hv.
    symmetry.
    apply (snd (ump_products _ _ _)).
    split.
    + exact (Hv Fin.F1).
    + exact (Hv (Fin.FS Fin.F1)).
Defined.

Definition binary_IsIndexedCoproduct {C : Category}
  (CC : @Cocartesian C) (x y : C) :
  IsIndexedCoproduct (fin2fam x y) (x + y)%object (fin2_colegs inl inr) :=
  @binary_IsIndexedProduct (C^op) CC x y.

(* * ** The 恒等 matrix at n = 2 IS Semiadditive's [can_comparison] （已译） *)

Section BinaryComparison.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{CP : @Cartesian C}.
Context `{CC : @Cocartesian C}.
Context (x y : C).

Definition binary_can : (x + y)%object ~> (x × y)%object :=
  can_matrix (fin2fam x y) Fin.eq_dec
    (binary_IsIndexedCoproduct CC x y) (binary_IsIndexedProduct CP x y).

(* 相关说明。 （已译） *)
Lemma binary_entry_diag (j : Fin.t 2) :
  mat_entry (fin2_colegs inl inr) (fin2_legs exl exr)
    (can_comparison x y) j j ≈ id.
Proof.
  pattern j; apply fin2fam_rect; unfold mat_entry; simpl.
  - apply exl_can_inl.
  - apply exr_can_inr.
Qed.

(* 相关说明。 （已译） *)
Lemma binary_entry_off (j k : Fin.t 2) :
  j <> k →
  mat_entry (fin2_colegs inl inr) (fin2_legs exl exr)
    (can_comparison x y) j k ≈ zero_mor.
Proof.
  revert k.
  pattern j; apply fin2fam_rect; intro k; pattern k; apply fin2fam_rect;
  intro Hne; unfold mat_entry; simpl.
  - now contradiction Hne.
  - apply exr_can_inl.
  - apply exl_can_inr.
  - now contradiction Hne.
Qed.

Theorem binary_can_is_can_comparison : can_comparison x y ≈ binary_can.
Proof.
  apply (can_matrix_unique (fin2fam x y) Fin.eq_dec
           (binary_IsIndexedCoproduct CC x y)
           (binary_IsIndexedProduct CP x y)).
  - exact binary_entry_diag.
  - exact binary_entry_off.
Qed.

End BinaryComparison.

(* 相关说明。 （已译） *)

Section FiniteMatrix.

Context {C : Category}.
Context `{CP : @Cartesian C}.
Context `{T : @Terminal C}.
Context (CC : @Cocartesian C).
Context (I : @Initial C).

Definition fin_matrix {m n : nat} (gs : Fin.t m → C) (fs : Fin.t n → C)
  (e : ∀ (j : Fin.t m) (k : Fin.t n), gs j ~> fs k) :
  fin_coprod CC I m gs ~> fin_prod n fs :=
  matrix_mor (fin_IsIndexedCoproduct CC I m gs) (fin_IsIndexedProduct n fs) e.

Theorem fin_matrix_entry {m n : nat} (gs : Fin.t m → C) (fs : Fin.t n → C)
  (e : ∀ (j : Fin.t m) (k : Fin.t n), gs j ~> fs k)
  (j : Fin.t m) (k : Fin.t n) :
  mat_entry (fin_inj CC I m gs) (fin_proj n fs)
    (fin_matrix gs fs e) j k ≈ e j k.
Proof. apply matrix_entry. Qed.

Theorem fin_matrix_ext {m n : nat} (gs : Fin.t m → C) (fs : Fin.t n → C)
  (u v : fin_coprod CC I m gs ~> fin_prod n fs) :
  (∀ (j : Fin.t m) (k : Fin.t n),
     mat_entry (fin_inj CC I m gs) (fin_proj n fs) u j k
       ≈ mat_entry (fin_inj CC I m gs) (fin_proj n fs) v j k) → u ≈ v.
Proof.
  apply (matrix_ext (fin_IsIndexedCoproduct CC I m gs)
                    (fin_IsIndexedProduct n fs)).
Qed.

(*
   本节说明 Matrix 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example matrix_row_at_fold {J : Type} {gs : J → C} {n : nat}
  (fs : Fin.t n → C) (e : ∀ (j : J) (k : Fin.t n), gs j ~> fs k) (j : J) :
  matrix_row (fin_IsIndexedProduct n fs) e j = fin_tuple n fs (gs j) (e j) :=
  eq_refl.

Example matrix_mor_at_fold {m n : nat} (gs : Fin.t m → C) (fs : Fin.t n → C)
  (e : ∀ (j : Fin.t m) (k : Fin.t n), gs j ~> fs k) :
  fin_matrix gs fs e
    = fin_cotuple CC I m gs (fin_prod n fs)
        (fun j => fin_tuple n fs (gs j) (e j)) := eq_refl.

End FiniteMatrix.

Section FiniteComparison.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{CP : @Cartesian C}.
Context `{T : @Terminal C}.
Context (CC : @Cocartesian C).
Context (I : @Initial C).

(*
   本节说明 Matrix 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition fin_can {n : nat} (fs : Fin.t n → C) :
  fin_coprod CC I n fs ~> fin_prod n fs :=
  can_matrix fs Fin.eq_dec
    (fin_IsIndexedCoproduct CC I n fs) (fin_IsIndexedProduct n fs).

Theorem fin_can_diag {n : nat} (fs : Fin.t n → C) (j : Fin.t n) :
  mat_entry (fin_inj CC I n fs) (fin_proj n fs) (fin_can fs) j j ≈ id.
Proof. apply can_matrix_diag. Qed.

Theorem fin_can_off {n : nat} (fs : Fin.t n → C) (j k : Fin.t n) :
  j <> k →
  mat_entry (fin_inj CC I n fs) (fin_proj n fs) (fin_can fs) j k
    ≈ zero_mor.
Proof. apply can_matrix_off. Qed.

Theorem fin_can_unique {n : nat} (fs : Fin.t n → C)
  (u : fin_coprod CC I n fs ~> fin_prod n fs) :
  (∀ j : Fin.t n,
     mat_entry (fin_inj CC I n fs) (fin_proj n fs) u j j ≈ id) →
  (∀ j k : Fin.t n, j <> k →
     mat_entry (fin_inj CC I n fs) (fin_proj n fs) u j k ≈ zero_mor) →
  u ≈ fin_can fs.
Proof. apply can_matrix_unique. Qed.

End FiniteComparison.

(* 相关说明。 （已译） *)

Section FiniteClassMatrix.

Context {C : Category}.
Context {HFP : HasFiniteProducts C}.
Context {HFC : HasFiniteCoproducts C}.

Definition finite_matrix {m n : nat} (gs : Fin.t m → C) (fs : Fin.t n → C)
  (e : ∀ (j : Fin.t m) (k : Fin.t n), gs j ~> fs k) :
  finite_coproduct gs ~> finite_product fs :=
  matrix_mor (finite_coproduct_ump gs) (finite_product_ump fs) e.

Theorem finite_matrix_entry {m n : nat} (gs : Fin.t m → C)
  (fs : Fin.t n → C) (e : ∀ (j : Fin.t m) (k : Fin.t n), gs j ~> fs k)
  (j : Fin.t m) (k : Fin.t n) :
  mat_entry (finite_coproduct_inj gs) (finite_product_proj fs)
    (finite_matrix gs fs e) j k ≈ e j k.
Proof. apply matrix_entry. Qed.

Theorem finite_matrix_ext {m n : nat} (gs : Fin.t m → C)
  (fs : Fin.t n → C) (u v : finite_coproduct gs ~> finite_product fs) :
  (∀ (j : Fin.t m) (k : Fin.t n),
     mat_entry (finite_coproduct_inj gs) (finite_product_proj fs) u j k
       ≈ mat_entry (finite_coproduct_inj gs) (finite_product_proj fs)
           v j k) → u ≈ v.
Proof.
  apply (matrix_ext (finite_coproduct_ump gs) (finite_product_ump fs)).
Qed.

End FiniteClassMatrix.

Section FiniteClassComparison.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context {HFP : HasFiniteProducts C}.
Context {HFC : HasFiniteCoproducts C}.

Definition finite_can {n : nat} (fs : Fin.t n → C) :
  finite_coproduct fs ~> finite_product fs :=
  can_matrix fs Fin.eq_dec
    (finite_coproduct_ump fs) (finite_product_ump fs).

Theorem finite_can_diag {n : nat} (fs : Fin.t n → C) (j : Fin.t n) :
  mat_entry (finite_coproduct_inj fs) (finite_product_proj fs)
    (finite_can fs) j j ≈ id.
Proof. apply can_matrix_diag. Qed.

Theorem finite_can_off {n : nat} (fs : Fin.t n → C) (j k : Fin.t n) :
  j <> k →
  mat_entry (finite_coproduct_inj fs) (finite_product_proj fs)
    (finite_can fs) j k ≈ zero_mor.
Proof. apply can_matrix_off. Qed.

Theorem finite_can_unique {n : nat} (fs : Fin.t n → C)
  (u : finite_coproduct fs ~> finite_product fs) :
  (∀ j : Fin.t n,
     mat_entry (finite_coproduct_inj fs) (finite_product_proj fs) u j j
       ≈ id) →
  (∀ j k : Fin.t n, j <> k →
     mat_entry (finite_coproduct_inj fs) (finite_product_proj fs) u j k
       ≈ zero_mor) →
  u ≈ finite_can fs.
Proof. apply can_matrix_unique. Qed.

End FiniteClassComparison.

(* 相关说明。 （已译） *)
Example finite_matrix_is_fin_matrix {C : Category} (CP : @Cartesian C)
  (T : @Terminal C) (CC : @Cocartesian C) (I : @Initial C)
  {m n : nat} (gs : Fin.t m → C) (fs : Fin.t n → C)
  (e : ∀ (j : Fin.t m) (k : Fin.t n), gs j ~> fs k) :
  @finite_matrix C (Cartesian_Terminal_HasFiniteProducts CP T)
    (Cocartesian_Initial_HasFiniteCoproducts CC I) m n gs fs e
  = @fin_matrix C CP T CC I m n gs fs e := eq_refl.

Example finite_can_is_fin_can {C : Category} `{Z : @ZeroObject C}
  (CP : @Cartesian C) (T : @Terminal C) (CC : @Cocartesian C)
  (I : @Initial C) {n : nat} (fs : Fin.t n → C) :
  @finite_can C Z (Cartesian_Terminal_HasFiniteProducts CP T)
    (Cocartesian_Initial_HasFiniteCoproducts CC I) n fs
  = @fin_can C Z CP T CC I n fs := eq_refl.

(* 相关说明。 （已译） *)

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition coq_succ_matrix :
  ∀ (j k : Fin.t 2), (fun _ : Fin.t 2 => nat : Coq) j
                       ~> (fun _ : Fin.t 2 => nat : Coq) k :=
  fun _ _ => fun x => S x.

Example coq_matrix_computes :
  fin_matrix Coq_Cocartesian Coq_Initial
    (fun _ : Fin.t 2 => nat : Coq) (fun _ : Fin.t 2 => nat : Coq)
    coq_succ_matrix (Datatypes.inl 3%nat) = (4%nat, (4%nat, tt)) := eq_refl.

Example coq_matrix_computes_right :
  fin_matrix Coq_Cocartesian Coq_Initial
    (fun _ : Fin.t 2 => nat : Coq) (fun _ : Fin.t 2 => nat : Coq)
    coq_succ_matrix (Datatypes.inr (Datatypes.inl 7%nat))
      = (8%nat, (8%nat, tt)) := eq_refl.
