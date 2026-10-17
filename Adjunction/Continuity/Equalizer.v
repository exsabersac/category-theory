Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Limit.FromProducts.

Generalizable All Variables.

(** * Right adjoints preserve equalizers, in the elementary form *)

(*
   nLab: https://ncatlab.org/nlab/show/adjoints+preserve+(co-)limits
   nLab: https://ncatlab.org/nlab/show/equalizer

   本文件给出等化子结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition right_adjoint_PreservesEqualizers@{co do h +}
  {C : Category@{co h h}} {D : Category@{do h h}}
  {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) : PreservesEqualizers U.
Proof.
  intros x y f g q e E.
  unshelve econstructor.
  - rewrite <- !fmap_comp. apply fmap_respects. exact (fork_eq E).
  - intros z h Hh.
    (* the transpose of h forks the pair in C *)
    assert (Hf : f ∘ from (@adj _ _ _ _ A z x) h
                   ≈ g ∘ from (@adj _ _ _ _ A z x) h).
    { rewrite <- !from_adj_nat_r. apply from_adj_respects. exact Hh. }
    destruct (eq_desc E _ Hf) as [u Hu Huniq].
    exists (to (@adj _ _ _ _ A z q) u).
    + rewrite <- to_adj_nat_r. rewrite Hu.
      apply from_adj_comp_law.
    + intros v Hv.
      rewrite <- (from_adj_comp_law (H := A) v).
      apply to_adj_respects.
      apply Huniq.
      rewrite <- from_adj_nat_r. rewrite Hv. reflexivity.
Defined.

Corollary not_PreservesEqualizers_no_left_adjoint@{co do h +}
  {C : Category@{co h h}} {D : Category@{do h h}} {U : C ⟶ D}
  {x y : C} (f g : x ~> y) (q : C) (e : q ~> x) (E : IsEqualizer f g q e)
  (N : IsEqualizer (fmap[U] f) (fmap[U] g) (U q) (fmap[U] e) → False)
  (F : D ⟶ C) (A : F ⊣ U) : False.
Proof. exact (N (right_adjoint_PreservesEqualizers A x y f g q e E)). Qed.
