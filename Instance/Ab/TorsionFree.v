(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,

   本文件给出阿贝尔群相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Instance.Ab.Monoidal.
Require Import Category.Instance.Ab.DirectedColimit.
Require Import Category.Instance.Ab.Character.Finite.
Require Import Category.Adjunction.Unitalization.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

(** * Torsion elements *)

Definition torsion_mem (A : AbObject) (a : carrier A) : Type :=
  { k : nat & ((0 < k)%nat * (nat_smul A k a ≈ cmon_zero A))%type }.

Definition torsion_resp (A : AbObject) (a b : carrier A) :
  a ≈ b → torsion_mem A a → torsion_mem A b.
Proof.
  intros Hab [k [Hk Hka]].
  exists k; split; [ exact Hk | ].
  rewrite <- (nat_smul_respects A k a b Hab).
  exact Hka.
Defined.

Definition torsion_zero (A : AbObject) : torsion_mem A (cmon_zero A).
Proof.
  exists 1%nat; split; [ lia | ].
  apply nat_smul_zero.
Defined.

Lemma torsion_scale (A : AbObject) (j k : nat) (a : carrier A) :
  nat_smul A k a ≈ cmon_zero A →
  nat_smul A (j * k) a ≈ cmon_zero A.
Proof.
  intro Hk.
  rewrite nat_smul_mul, Hk.
  apply nat_smul_zero.
Defined.

Definition torsion_plus (A : AbObject) (a b : carrier A) :
  torsion_mem A a → torsion_mem A b →
  torsion_mem A (cmon_plus A a b).
Proof.
  intros [k [Hk Hka]] [l [Hl Hlb]].
  exists (k * l)%nat; split; [ lia | ].
  assert (Ha : nat_smul A (k * l) a ≈ cmon_zero A).
  { rewrite (Nat.mul_comm k l).
    exact (torsion_scale A l k a Hka). }
  assert (Hb : nat_smul A (k * l) b ≈ cmon_zero A).
  { exact (torsion_scale A k l b Hlb). }
  rewrite nat_smul_plus, Ha, Hb.
  apply cmon_plus_zero_l.
Defined.

Definition torsion_neg (A : AbObject) (a : carrier A) :
  torsion_mem A a → torsion_mem A (ab_neg A a).
Proof.
  intros [k [Hk Hka]].
  exists k; split; [ exact Hk | ].
  rewrite nat_smul_neg, Hka.
  apply ab_neg_zero.
Defined.

Definition TorsionSub (A : AbObject) : AbSubgroup A := {|
  absub_mem   := torsion_mem A;
  absub_resp  := torsion_resp A;
  absub_zero  := torsion_zero A;
  absub_plus  := torsion_plus A;
  absub_neg   := torsion_neg A
|}.

Definition TorsionAb (A : AbObject) : AbObject :=
  AbSubgroupAb (TorsionSub A).

Definition torsion_incl (A : AbObject) : TorsionAb A ~{Ab}~> A :=
  absub_incl (TorsionSub A).

(** * Torsion-free groups *)

Definition TorsionFree (A : AbObject) : Type :=
  ∀ (a : carrier A) (k : nat),
    (0 < k)%nat → nat_smul A k a ≈ cmon_zero A → a ≈ cmon_zero A.

Definition TorsionFree_Sub : Subcategory Ab :=
  @Build_Subcategory Ab
    TorsionFree
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition TorsionFreeAb : Category := Sub Ab TorsionFree_Sub.

Lemma TorsionFree_Full :
  Category.Construction.Subcategory.Full Ab TorsionFree_Sub.
Proof. intros x y ox oy g; exact I. Defined.

Lemma TorsionFree_Incl_Full :
  Functor.Full (Incl Ab TorsionFree_Sub).
Proof. exact (Full_Implies_Full_Functor Ab TorsionFree_Sub
                TorsionFree_Full). Defined.

Lemma TorsionFree_Incl_Faithful :
  Functor.Faithful (Incl Ab TorsionFree_Sub).
Proof. exact (Incl_Faithful Ab TorsionFree_Sub). Defined.

(* 相关说明。 （已译） *)

Definition AbModTorsion (A : AbObject) : AbObject :=
  AbQuotient (torsion_incl A).

(*
   本节说明 TorsionFree 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example quot_zero_strict (A : AbObject) :
  cmon_zero (AbModTorsion A) = cmon_zero A := eq_refl.

Example quot_plus_strict (A : AbObject) (x y : carrier A) :
  cmon_plus (AbModTorsion A) x y = cmon_plus A x y := eq_refl.

Example nat_smul_quot_two (A : AbObject) (x : carrier A) :
  nat_smul (AbModTorsion A) 2 x = nat_smul A 2 x := eq_refl.

Lemma nat_smul_quot (A : AbObject) (k : nat) (x : carrier A) :
  nat_smul (AbModTorsion A) k x = nat_smul A k x.
Proof.
  induction k as [|j IH]; simpl; [ reflexivity | now rewrite IH ].
Qed.

Definition quot_eq_intro (A : AbObject) (x y t : carrier A)
    (Ht : torsion_mem A t) (H : x ≈ cmon_plus A y t) :
  @equiv (carrier (AbModTorsion A)) _ x y.
Proof. exists (existT _ t Ht); apply pequiv_from; exact H. Defined.

(*
   本节说明 TorsionFree 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition quot_eq_elim (A : AbObject) (x y : carrier A) (P : Prop)
  (H : @equiv (carrier (AbModTorsion A)) _ x y)
  (k : ∀ t : carrier A,
         torsion_mem A t → x ≈ cmon_plus A y t → P) : P.
Proof.
  destruct H as [[t Ht] Hxt].
  exact (k t Ht (pequiv_to _ _ Hxt)).
Defined.

Definition AbModTorsion_TorsionFree (A : AbObject) :
  TorsionFree (AbModTorsion A).
Proof.
  intros x k Hk Hx.
  rewrite nat_smul_quot in Hx.
  apply (@pequiv_to _ _ (cmon_prop (AbModTorsion A))).
  apply (quot_eq_elim A _ _ _ Hx); intros t [l [Hl Hlt]] Hxt.
  apply pequiv_from.
  apply (quot_eq_intro A x (cmon_zero A) x).
  - exists (l * k)%nat; split; [ lia | ].
    rewrite nat_smul_mul.
    assert (Hkx : nat_smul A k x ≈ t).
    { transitivity (cmon_plus A (cmon_zero A) t).
      - exact Hxt.
      - apply cmon_plus_zero_l. }
    rewrite Hkx, Hlt.
    reflexivity.
  - symmetry; apply cmon_plus_zero_l.
Defined.

Definition TorsionFreeMod (A : AbObject) : TorsionFreeAb :=
  (AbModTorsion A; AbModTorsion_TorsionFree A).

(** * The universal property *)

Definition torsion_kills {A B : AbObject} (HB : TorsionFree B)
    (f : A ~{Ab}~> B) (t : carrier A) :
  torsion_mem A t → cmon_map f t ≈ cmon_zero B.
Proof.
  intros [k [Hk Hkt]].
  apply (HB _ k Hk).
  rewrite <- nat_smul_hom, Hkt.
  apply cmon_map_zero.
Defined.

Program Definition torsion_med {A B : AbObject} (HB : TorsionFree B)
    (f : A ~{Ab}~> B) : AbModTorsion A ~{Ab}~> B :=
  {| cmon_map := {| morphism := fun x : carrier A => cmon_map f x |} |}.
Next Obligation.
  intros x y Hxy.
  apply (@pequiv_to _ _ (cmon_prop B)).
  apply (quot_eq_elim A x y _ Hxy); intros t Ht Hxt.
  apply pequiv_from.
  rewrite Hxt, cmon_map_plus, (torsion_kills HB f t Ht).
  apply cmon_plus_zero_r.
Qed.
Next Obligation. apply cmon_map_zero. Qed.
Next Obligation. apply cmon_map_plus. Qed.

Theorem torsion_universal (A : AbObject) :
  ∀ (d : TorsionFreeAb) (f : A ~{Ab}~> Incl Ab TorsionFree_Sub d),
    ∃! g : TorsionFreeMod A ~{TorsionFreeAb}~> d,
      f ≈ fmap[Incl Ab TorsionFree_Sub] g
             ∘ ab_quot_proj (torsion_incl A).
Proof.
  intros d f.
  unshelve eexists.
  - exact (torsion_med `2 d f; I).
  - intro a; simpl; reflexivity.
  - intros g Hg a; simpl.
    exact (Hg a).
Defined.

Definition torsion_universal_arrow (A : AbObject)
  : @UniversalArrow Ab TorsionFreeAb A (Incl Ab TorsionFree_Sub) :=
  @universal_arrow_from_UMP Ab TorsionFreeAb A (Incl Ab TorsionFree_Sub)
    (TorsionFreeMod A) (ab_quot_proj (torsion_incl A))
    (torsion_universal A).

Definition TorsionFree_reflector : Ab ⟶ TorsionFreeAb :=
  LeftAdjointFunctorFromUniversalArrows (Incl Ab TorsionFree_Sub)
    torsion_universal_arrow.

Definition TorsionFree_adj
  : TorsionFree_reflector ⊣ Incl Ab TorsionFree_Sub :=
  AdjunctionFromUniversalArrows (Incl Ab TorsionFree_Sub)
    torsion_universal_arrow.

Definition TorsionFree_Reflective : Reflective TorsionFree_Sub :=
  @Build_Reflective Ab TorsionFree_Sub TorsionFree_Full
    TorsionFree_reflector TorsionFree_adj.

(** * Strict readbacks *)

Example torsion_reflector_obj (A : AbObject) :
  `1 (fobj[TorsionFree_reflector] A) = AbModTorsion A := eq_refl.

Example torsion_arrow_is_proj (A : AbObject) :
  @arrow Ab TorsionFreeAb A (Incl Ab TorsionFree_Sub)
    (torsion_universal_arrow A)
    = ab_quot_proj (torsion_incl A) := eq_refl.

Example torsion_arrow_obj (A : AbObject) :
  @arrow_obj Ab TorsionFreeAb A (Incl Ab TorsionFree_Sub)
    (torsion_universal_arrow A)
    = TorsionFreeMod A := eq_refl.

Definition torsion_unit (A : AbObject)
  : A ~{Ab}~> Incl Ab TorsionFree_Sub (fobj[TorsionFree_reflector] A) :=
  @Category.Theory.Adjunction.unit _ _ _ _ TorsionFree_adj A.

Example torsion_unit_is_proj (A : AbObject) (a : carrier A) :
  cmon_map (torsion_unit A) a = cmon_map (ab_quot_proj (torsion_incl A)) a
  := eq_refl.

Lemma torsion_unit_is_proj_hom (A : AbObject) :
  torsion_unit A ≈ ab_quot_proj (torsion_incl A).
Proof. intro a; reflexivity. Defined.

(* 相关说明。 （已译） *)

Definition torsionfree_reflect_iso (x : TorsionFreeAb) :
  fobj[TorsionFree_reflector] (Incl Ab TorsionFree_Sub x)
    ≅[TorsionFreeAb] x :=
  reflective_counit_iso TorsionFree_Reflective x.

(** * Non-vacuity: the integers *)

Lemma nat_smul_ZAb (k : nat) (n : carrier ZAb) :
  nat_smul ZAb k n = Z.mul (Z.of_nat k) n.
Proof.
  induction k as [|j IH].
  - reflexivity.
  - change (nat_smul ZAb (S j) n) with (Z.add n (nat_smul ZAb j n)).
    rewrite IH; lia.
Qed.

(*
   本节说明 TorsionFree 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ZAb_torsionfree_elt (n : carrier ZAb) (k : nat) :
  (0 < k)%nat → Z.mul (Z.of_nat k) n = 0%Z → n = 0%Z.
Proof.
  intros Hk H.
  apply Z.mul_eq_0 in H.
  destruct H as [Hz|Hz]; [ lia | exact Hz ].
Qed.

Definition ZAb_TorsionFree : TorsionFree ZAb.
Proof.
  intros n k Hk H.
  assert (H' : Z.mul (Z.of_nat k) n = 0%Z).
  { rewrite <- nat_smul_ZAb; exact H. }
  exact (ZAb_torsionfree_elt n k Hk H').
Defined.

Lemma ZAb_torsion_trivial (n : carrier ZAb) :
  torsion_mem ZAb n → n = 0%Z.
Proof.
  intros [k [Hk Hkn]].
  exact (ZAb_TorsionFree n k Hk Hkn).
Qed.

Definition ZAb_TF : TorsionFreeAb := (ZAb; ZAb_TorsionFree).

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ZAb_reflect_iso :
  fobj[TorsionFree_reflector] (Incl Ab TorsionFree_Sub ZAb_TF)
    ≅[TorsionFreeAb] ZAb_TF :=
  torsionfree_reflect_iso ZAb_TF.

(* 相关说明。 （已译） *)

Definition ZMod2_all_torsion (b : carrier ZMod2) : torsion_mem ZMod2 b.
Proof.
  exists 2%nat; split; [ lia | ].
  destruct b; reflexivity.
Defined.

Lemma ZMod2_not_TorsionFree : TorsionFree ZMod2 → False.
Proof.
  intro H.
  destruct (ZMod2_all_torsion true) as [k [Hk Hkt]].
  assert (Hb : true = false) by exact (H true k Hk Hkt).
  discriminate.
Qed.

Example ZMod2_quot_collapses :
  @equiv (carrier (AbModTorsion ZMod2)) _ true false.
Proof.
  apply (quot_eq_intro ZMod2 true false true).
  - exact (ZMod2_all_torsion true).
  - reflexivity.
Defined.

(** * Non-vacuity: a mixed group *)

Definition MixedAb : AbObject := Ab_product ZAb ZMod2.

Definition mixed_tors : carrier MixedAb := (cmon_zero ZAb, true).
Definition mixed_gen : carrier MixedAb := (ZAb_one, false).

Definition mixed_tors_torsion : torsion_mem MixedAb mixed_tors.
Proof.
  exists 2%nat; split; [ lia | ].
  split; reflexivity.
Defined.

(* [mixed_tors] is a torsion element that is not zero, so [TorsionSub] is
   NONTRIVIAL at [MixedAb]; [mixed_gen_not_torsion] makes it PROPER. *)
Lemma mixed_tors_not_zero :
  @equiv (carrier MixedAb) _ mixed_tors (cmon_zero MixedAb) → False.
Proof.
  intros [_ H]; simpl in H; discriminate.
Qed.

Lemma mixed_gen_not_torsion : torsion_mem MixedAb mixed_gen → False.
Proof.
  intros [k [Hk Hkg]].
  assert (Hz : nat_smul ZAb k ZAb_one ≈ cmon_zero ZAb).
  { rewrite <- (nat_smul_hom (Ab_exl ZAb ZMod2) k mixed_gen).
    exact (fst Hkg). }
  rewrite nat_smul_int_one in Hz.
  assert (Hz' : Z.of_nat k = 0%Z) by exact Hz.
  lia.
Qed.

Example mixed_quot_merges :
  @equiv (carrier (AbModTorsion MixedAb)) _ mixed_tors
    (cmon_zero MixedAb).
Proof.
  apply (quot_eq_intro MixedAb mixed_tors (cmon_zero MixedAb) mixed_tors).
  - exact mixed_tors_torsion.
  - split; reflexivity.
Defined.

Lemma mixed_gen_not_quot_zero :
  @equiv (carrier (AbModTorsion MixedAb)) _ mixed_gen
    (cmon_zero MixedAb) → False.
Proof.
  intro H.
  (* 相关说明。 （已译） *)
  apply (quot_eq_elim MixedAb _ _ _ H); intros t Ht Hgt.
  apply mixed_gen_not_torsion.
  apply (torsion_resp MixedAb t mixed_gen).
  - rewrite Hgt; symmetry; apply cmon_plus_zero_l.
  - exact Ht.
Qed.
