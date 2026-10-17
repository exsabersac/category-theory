Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Functor.Structure.Terminal.
Require Import Category.Functor.Structure.Cartesian.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Fun.
Require Import Category.Construction.Subcategory.
Require Import Category.Theory.Lawvere.
Require Import Category.Theory.Lawvere.Model.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Lawvere.

Generalizable All Variables.

(*
 nLab:      https://ncatlab.org/nlab/show/Lawvere+theory
 Wikipedia: https://en.wikipedia.org/wiki/Lawvere_theory

   本文件给出集合相关实例或构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma prod_separates {C : Category} `{@Cartesian C} {x y z : C}
  (h k : x ~> y × z) :
  exl ∘ h ≈ exl ∘ k → exr ∘ h ≈ exr ∘ k → h ≈ k.
Proof.
  intros Hl Hr.
  rewrite (snd (ump_products (exl ∘ k) (exr ∘ k) h) (Hl, Hr)).
  symmetry.
  apply (snd (ump_products (exl ∘ k) (exr ∘ k) k)).
  split; reflexivity.
Qed.

(** ** The underlying-set functor *)

Section Ev1.

Context (T : LawvereTheory).

(*
   本节说明自然变换、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition ev1 : Models T Sets ⟶ Sets := {|
  fobj := fun M => `1 M (law_of_nat 1%nat);
  fmap := fun F G τ => transform (`1 τ) (law_of_nat 1%nat)
|}.
Next Obligation.
  simpl; intros.
  pose proof (@fmap_id _ _ x (law_of_nat 1%nat)) as HH.
  simpl in HH; apply HH.
Qed.

(*
   本节说明函子、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Context (reach : ∀ x : @law_cat T, { n : nat & law_of_nat n = x }).

Theorem ev1_Faithful : Faithful ev1.
Proof using T reach.
  construct.
  destruct x as [F [FC FT]], y as [G [GC GT]], f as [τ ?], g as [σ ?].
  simpl in X.
  change (transform τ (law_of_nat 1%nat) ≈ transform σ (law_of_nat 1%nat)) in X.
  assert (HA : ∀ A : @law_cat T, transform τ A ≈ transform σ A).
  { intro A.
    destruct (reach A) as [n e]; destruct e.
    rewrite <- (law_pow_one n).
    induction n as [|k IH].
    - (* n = 0: both components are maps into G 1 ≅ 1, hence equal *)
      simpl law_pow.
      pose proof (@one_unique Sets Sets_Terminal _
        (from (@fobj_one_iso _ _ G _ _ GT)
           ∘ transform τ (@terminal_obj _ (@law_terminal T)))
        (from (@fobj_one_iso _ _ G _ _ GT)
           ∘ transform σ (@terminal_obj _ (@law_terminal T)))) as Hone.
      rewrite <- (id_left (transform τ (@terminal_obj _ (@law_terminal T)))).
      rewrite <- (iso_to_from (@fobj_one_iso _ _ G _ _ GT)).
      rewrite <- comp_assoc.
      rewrite Hone.
      rewrite comp_assoc.
      rewrite (iso_to_from (@fobj_one_iso _ _ G _ _ GT)).
      exact (id_left (transform σ (@terminal_obj _ (@law_terminal T)))).
    - (* n = S k: compare through the product iso G (1 × pow k) ≅ G 1 × G (pow k) *)
      simpl law_pow.
      rewrite <- (id_left (transform τ
        (@product_obj _ (@law_cartesian T) (law_of_nat 1%nat) (law_pow k)))).
      rewrite <- (@prod_in_out _ _ G _ _ GC (law_of_nat 1%nat) (law_pow k)).
      rewrite <- comp_assoc.
      assert (Hout :
        @prod_out _ _ G _ _ GC (law_of_nat 1%nat) (law_pow k)
          ∘ transform τ
              (@product_obj _ (@law_cartesian T) (law_of_nat 1%nat) (law_pow k))
        ≈[Sets] @prod_out _ _ G _ _ GC (law_of_nat 1%nat) (law_pow k)
          ∘ transform σ
              (@product_obj _ (@law_cartesian T) (law_of_nat 1%nat) (law_pow k))).
      { apply prod_separates.
        - rewrite !comp_assoc.
          rewrite <- (@fmap_exl _ _ G _ _ GC (law_of_nat 1%nat) (law_pow k)).
          rewrite (naturality τ _ _
            (@exl _ (@law_cartesian T) (law_of_nat 1%nat) (law_pow k))).
          rewrite (naturality σ _ _
            (@exl _ (@law_cartesian T) (law_of_nat 1%nat) (law_pow k))).
          now rewrite X.
        - rewrite !comp_assoc.
          rewrite <- (@fmap_exr _ _ G _ _ GC (law_of_nat 1%nat) (law_pow k)).
          rewrite (naturality τ _ _
            (@exr _ (@law_cartesian T) (law_of_nat 1%nat) (law_pow k))).
          rewrite (naturality σ _ _
            (@exr _ (@law_cartesian T) (law_of_nat 1%nat) (law_pow k))).
          now rewrite IH. }
      rewrite Hout.
      rewrite comp_assoc.
      rewrite (@prod_in_out _ _ G _ _ GC (law_of_nat 1%nat) (law_pow k)).
      exact (id_left (transform σ
        (@product_obj _ (@law_cartesian T) (law_of_nat 1%nat) (law_pow k)))). }
  simpl in HA; apply HA.
Qed.

End Ev1.

(*
   本节说明Lawvere 理论相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition FinSetOp_reach :
  ∀ x : @law_cat FinSetOp_Lawvere, { n : nat & law_of_nat n = x } :=
  fun x => (x; eq_refl).
