Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Quotient.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   本文件给出划分相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Set Default Proof Using "All".

(** * The quotient as a set of parts *)

(*
   nLab:      https://ncatlab.org/nlab/show/partition
   nLab:      https://ncatlab.org/nlab/show/quotient+set
   Wikipedia: https://en.wikipedia.org/wiki/Equivalence_class
   Wikipedia: https://en.wikipedia.org/wiki/Partition_of_a_set

   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   Paper: Hofstra and Warren, "Combinatorial realizability models of type
   Paper: Barthe, Capretta, Pons, "Setoids in type theory", JFP 13(2) 2003

   本节说明 Partition 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Partition 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Partition.

Context {A : SetoidObject}.
Context (R : crelation (carrier A)).
Context (HR : Equivalence R).
Context (HC : SetoidCoarser R).

(* 相关说明。 （已译） *)

(*
   本节说明 Partition 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sets_part_pred (a : carrier A) : carrier (Powerset_Prop_obj A).
Proof.
  unshelve refine
    (@Build_SetoidMorphism (carrier A) (is_setoid A) Prop
       (is_setoid Powerset_Prop_truth)
       (fun x => Powerset_squash (R a x)) _).
  intros x x' Hxx'; split; intros H Q k; apply H; intro w; apply k.
  - transitivity x; [ exact w | exact (HC x x' Hxx') ].
  - transitivity x'; [ exact w | exact (HC x' x (symmetry Hxx')) ].
Defined.

(* 相关说明。 （已译） *)
Lemma sets_part_mem_self (a : carrier A) : sets_part_pred a a.
Proof. exact (Powerset_squash_intro (Equivalence_Reflexive a)). Qed.

Lemma sets_part_mem_of (a x : carrier A) (w : R a x) : sets_part_pred a x.
Proof. exact (Powerset_squash_intro w). Qed.

(*
   本节说明 Partition 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma sets_part_shared_elem (a b c : carrier A)
  (Ha : sets_part_pred a c) (Hb : sets_part_pred b c) :
  @equiv _ (Powerset_Prop_obj A) (sets_part_pred a) (sets_part_pred b).
Proof.
  intro x; split; intro H.
  - apply Ha; intro wac; apply Hb; intro wbc; apply H; intro wax; clear H.
    apply Powerset_squash_intro.
    transitivity a; [ | exact wax ].
    transitivity c; [ exact wbc | exact (symmetry wac) ].
  - apply Ha; intro wac; apply Hb; intro wbc; apply H; intro wbx; clear H.
    apply Powerset_squash_intro.
    transitivity b; [ | exact wbx ].
    transitivity c; [ exact wac | exact (symmetry wbc) ].
Qed.

(* Classes of R-related elements coincide. *)
Lemma sets_part_pred_respects (a b : carrier A) (w : R a b) :
  @equiv _ (Powerset_Prop_obj A) (sets_part_pred a) (sets_part_pred b).
Proof.
  exact (sets_part_shared_elem a b b (sets_part_mem_of a b w)
           (sets_part_mem_self b)).
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Partition 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sets_parts_carrier : Type :=
  { P : carrier (Powerset_Prop_obj A)
      & { a : carrier A & @equiv _ (Powerset_Prop_obj A) P (sets_part_pred a) } }.

Definition sets_parts_equiv : crelation sets_parts_carrier :=
  fun S T => @equiv _ (Powerset_Prop_obj A) (`1 S) (`1 T).

Lemma sets_parts_equivalence : Equivalence sets_parts_equiv.
Proof.
  unfold sets_parts_equiv; constructor.
  - intro S; reflexivity.
  - intros S T H; now symmetry.
  - intros S T U H1 H2; now transitivity (`1 T).
Qed.

Definition SetsParts : SetoidObject :=
  {| carrier := sets_parts_carrier ;
     is_setoid := {| equiv := sets_parts_equiv ;
                     setoid_equiv := sets_parts_equivalence |} |}.

(** ** The class map *)

(* Defined for an ARBITRARY [crelation]-valued R: no stability is needed
   to send an element to its class. *)
(* 相关说明。 （已译） *)
Definition sets_part_elt (a : carrier A) : sets_parts_carrier.
Proof.
  unshelve refine
    (existT (fun P : carrier (Powerset_Prop_obj A) =>
               { b : carrier A
                   & @equiv _ (Powerset_Prop_obj A) P (sets_part_pred b) })
       (sets_part_pred a)
       (existT (fun b : carrier A =>
                  @equiv _ (Powerset_Prop_obj A) (sets_part_pred a)
                    (sets_part_pred b)) a _)).
  reflexivity.
Defined.

Definition sets_part_of : SetsQuotient A R HR ~{Sets}~> SetsParts.
Proof.
  unshelve refine
    (@Build_SetoidMorphism (carrier A) (is_setoid (SetsQuotient A R HR))
       sets_parts_carrier (is_setoid SetsParts) sets_part_elt _).
  intros a b w; exact (sets_part_pred_respects a b w).
Defined.

(* 相关说明。 （已译） *)
Lemma sets_part_of_surjective (S : carrier SetsParts) :
  @equiv _ SetsParts (sets_part_of (`1 (`2 S))) S.
Proof.
  intro x; split; intro H.
  - exact (proj2 (`2 (`2 S) x) H).
  - exact (proj1 (`2 (`2 S) x) H).
Qed.

(*
   本节说明 Partition 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma sets_part_of_squash (a b : carrier A)
  (H : @equiv _ SetsParts (sets_part_of a) (sets_part_of b)) :
  Powerset_squash (R a b).
Proof.
  assert (Hba : Powerset_squash (R b a))
    by exact (proj1 (H a) (sets_part_mem_self a)).
  intros Q k; apply Hba; intro w; apply k; exact (symmetry w).
Qed.

(* * ** The 假设 closes gap, it conclusion （已译） *)

Definition SquashStable : Type :=
  ∀ x y : carrier A, Powerset_squash (R x y) → R x y.

(* A [Prop]-valued 关系 squash-stable: instantiate the
 impredicative quantifier at 命题 itself. （已译） *)
Lemma prop_rel_squash_stable (Rp : carrier A -> carrier A -> Prop)
  (HRel : ∀ x y : carrier A, R x y ↔ Rp x y) : SquashStable.
Proof.
  intros x y H.
  apply (snd (HRel x y)).
  exact (H (Rp x y) (fun w => fst (HRel x y) w)).
Qed.

(*
   本节说明 Partition 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma squash_stable_injective (HS : SquashStable) (a b : carrier A)
  (H : @equiv _ SetsParts (sets_part_of a) (sets_part_of b)) : R a b.
Proof. exact (HS a b (sets_part_of_squash a b H)). Qed.

(*
   本节说明 Partition 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma squash_rel_sym (x y : carrier A) (H : Powerset_squash (R x y)) :
  Powerset_squash (R y x).
Proof. intros Q k; apply H; intro w; apply k; exact (symmetry w). Qed.

Lemma squash_rel_shift (x y z : carrier A) (H : Powerset_squash (R x y))
  (Hz : Powerset_squash (R x z)) : Powerset_squash (R y z).
Proof.
  intros Q k; apply H; intro wxy; apply Hz; intro wxz; apply k.
  transitivity x; [ exact (symmetry wxy) | exact wxz ].
Qed.

Lemma injective_squash_stable
  (Hinj : ∀ a b : carrier A,
     @equiv _ SetsParts (sets_part_of a) (sets_part_of b) → R a b) :
  SquashStable.
Proof.
  intros x y H.
  apply Hinj.
  intro z; split; intro Hz.
  - exact (squash_rel_shift x y z H Hz).
  - exact (squash_rel_shift y x z (squash_rel_sym x y H) Hz).
Qed.

Theorem partition_stability_is_the_conclusion :
  SquashStable ↔
  (∀ a b : carrier A,
     @equiv _ SetsParts (sets_part_of a) (sets_part_of b) → R a b).
Proof.
  split.
  - exact squash_stable_injective.
  - exact injective_squash_stable.
Qed.

(* 相关说明。 （已译） *)

Definition sets_part_rep (HS : SquashStable) :
  SetsParts ~{Sets}~> SetsQuotient A R HR.
Proof.
  unshelve refine
    (@Build_SetoidMorphism sets_parts_carrier (is_setoid SetsParts)
       (carrier A) (is_setoid (SetsQuotient A R HR))
       (fun S => `1 (`2 S)) _).
  intros S T HST.
  apply (squash_stable_injective HS).
  assert (Hpred : @equiv _ (Powerset_Prop_obj A)
                    (sets_part_pred (`1 (`2 S))) (sets_part_pred (`1 (`2 T)))).
  { transitivity (`1 S); [ symmetry; exact (`2 (`2 S)) | ].
    transitivity (`1 T); [ exact HST | exact (`2 (`2 T)) ]. }
  exact Hpred.
Defined.

(* 相关说明。 （已译） *)
Definition sets_partition_iso (HS : SquashStable) :
  @Isomorphism Sets (SetsQuotient A R HR) SetsParts.
Proof.
  unshelve refine {| to := sets_part_of ; from := sets_part_rep HS |}.
  - intro S; exact (sets_part_of_surjective S).
  - intro a; exact (Equivalence_Reflexive a).
Defined.

(* The class map 同构's forward leg nose. （已译） *)
Example sets_partition_iso_to (HS : SquashStable) :
  to (sets_partition_iso HS) = sets_part_of.
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)
Example sets_partition_iso_from (HS : SquashStable) (S : carrier SetsParts) :
  from (sets_partition_iso HS) S = `1 (`2 S).
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Partition 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sets_parts_prop_carrier : Type :=
  { P : carrier (Powerset_Prop_obj A)
      & Powerset_squash
          { a : carrier A
              & @equiv _ (Powerset_Prop_obj A) P (sets_part_pred a) } }.

Definition sets_parts_prop_equiv : crelation sets_parts_prop_carrier :=
  fun S T => @equiv _ (Powerset_Prop_obj A) (`1 S) (`1 T).

Lemma sets_parts_prop_equivalence : Equivalence sets_parts_prop_equiv.
Proof.
  unfold sets_parts_prop_equiv; constructor.
  - intro S; reflexivity.
  - intros S T H; now symmetry.
  - intros S T U H1 H2; now transitivity (`1 T).
Qed.

Definition SetsPartsProp : SetoidObject :=
  {| carrier := sets_parts_prop_carrier ;
     is_setoid := {| equiv := sets_parts_prop_equiv ;
                     setoid_equiv := sets_parts_prop_equivalence |} |}.

(*
   本节说明 Partition 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sets_parts_forget : SetsParts ~{Sets}~> SetsPartsProp.
Proof.
  unshelve refine
    {| morphism := fun S : carrier SetsParts =>
         existT (fun P : carrier (Powerset_Prop_obj A) =>
                   Powerset_squash
                     { a : carrier A
                         & @equiv _ (Powerset_Prop_obj A) P
                             (sets_part_pred a) })
           (`1 S) (Powerset_squash_intro (`2 S)) |}.
  intros S T HST; exact HST.
Defined.

(* It 恒等 underlying subset, conversion. （已译） *)
Example sets_parts_forget_pred (S : carrier SetsParts) :
  `1 (sets_parts_forget S) = `1 S.
Proof. reflexivity. Qed.

(* The 复合 class map 进入 strict 对象. （已译） *)
Definition sets_part_of_prop : SetsQuotient A R HR ~{Sets}~> SetsPartsProp :=
  sets_parts_forget ∘ sets_part_of.

Lemma sets_part_of_prop_surjective (S : carrier SetsPartsProp) :
  Powerset_squash
    { a : carrier A & @equiv _ SetsPartsProp (sets_part_of_prop a) S }.
Proof.
  intros Q k; apply (`2 S); intros [a Ha]; apply k.
  exists a.
  assert (Hsym : @equiv _ (Powerset_Prop_obj A) (sets_part_pred a) (`1 S))
    by (symmetry; exact Ha).
  exact Hsym.
Qed.

End Partition.


(* 相关说明。 （已译） *)

(* Instance/Sets/Quotient.v's [nat_parity] [Prop]-valued (an equation
 booleans), so [prop_rel_squash_stable] discharges 假设
 同构 unconditional at it. （已译） *)
Definition nat_parity_stable : SquashStable nat_parity.
Proof.
  apply (prop_rel_squash_stable nat_parity nat_parity_Equivalence nat_parity_coarser
           (fun m n => Nat.even m = Nat.even n)).
  intros m n; split; intro H; exact H.
Qed.

Definition nat_parity_partition_iso :
  @Isomorphism Sets NatParity (SetsParts nat_parity nat_parity_Equivalence nat_parity_coarser) :=
  sets_partition_iso nat_parity nat_parity_Equivalence nat_parity_coarser
    nat_parity_stable.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma nat_parity_parts_merge :
  @equiv _ (SetsParts nat_parity nat_parity_Equivalence nat_parity_coarser)
    (sets_part_of nat_parity nat_parity_Equivalence nat_parity_coarser 0%nat)
    (sets_part_of nat_parity nat_parity_Equivalence nat_parity_coarser 2%nat).
Proof.
  exact (sets_part_pred_respects nat_parity nat_parity_Equivalence
           nat_parity_coarser 0%nat 2%nat eq_refl).
Qed.

Lemma nat_parity_parts_separate :
  @equiv _ (SetsParts nat_parity nat_parity_Equivalence nat_parity_coarser)
    (sets_part_of nat_parity nat_parity_Equivalence nat_parity_coarser 0%nat)
    (sets_part_of nat_parity nat_parity_Equivalence nat_parity_coarser 1%nat)
  → False.
Proof.
  intro H.
  pose proof (squash_stable_injective nat_parity nat_parity_Equivalence
                nat_parity_coarser nat_parity_stable 0%nat 1%nat H) as E.
  discriminate E.
Qed.
