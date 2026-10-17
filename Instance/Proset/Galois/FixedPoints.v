Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.FixedPoints.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Poset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Rep.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Instance.Grp.Galois.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Arith.PeanoNat.
From Coq Require Import Lia.

Generalizable All Variables.

(*
   本文件给出预序集相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Set Default Proof Using "All".

(* 相关说明。 （已译） *)

(*
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Book:      Riehl, "Category Theory in Context", Dover 2016, SS 4.2,
   Wikipedia: https://en.wikipedia.org/wiki/Galois_connection
   nLab:      https://ncatlab.org/nlab/show/idempotent+monad

   本节说明 FixedPoints 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** (E) The dictionary, 等价, Mac Lane's bijection （已译） *)

Section GaloisFixed.

Context {A B : Type}.
Context {RA : relation A} {RB : relation B}.
Context (PA : PreOrder RA) (PB : PreOrder RB).
Context (G : GaloisConnection RA RB).

Definition GAdj := GaloisAdjunction PA PB G.

(*
   本节说明hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma unit_fixed_iff_closed_r (a : A) :
  IsIsomorphism (@unit (Proset PB) (Proset PA) _ _ GAdj a)
    ↔ GalClosed_r G a.
Proof.
  split.
  - intro H; exact (@two_sided_inverse (Proset PA) _ _ _ H).
  - intro H.
    exact (@Build_IsIsomorphism (Proset PA) _ _ _ H I I).
Defined.

Lemma counit_fixed_iff_closed_l (b : B) :
  IsIsomorphism (@counit (Proset PB) (Proset PA) _ _ GAdj b)
    ↔ GalClosed_l G b.
Proof.
  split.
  - intro H; exact (@two_sided_inverse (Proset PB) _ _ _ H).
  - intro H.
    exact (@Build_IsIsomorphism (Proset PB) _ _ _ H I I).
Defined.

(* The exercise's closing question, answered at Galois connection by
 pure instantiation general 定理. （已译） *)
Definition galois_fixed_point_equivalence :
  EquivalenceOfCategories (FixedL GAdj) :=
  adjunction_fixed_point_equivalence GAdj.

Definition galois_fixed_point_equivalence_swap :
  EquivalenceOfCategories (FixedR GAdj) :=
  fixed_point_equivalence_swap GAdj.

(* 相关说明。 （已译） *)

Lemma gal_lrl_eq (antiB : @Antisymmetric B eq eq_equiv RB) (a : A) :
  gal_l G (gal_r G (gal_l G a)) = gal_l G a.
Proof.
  refine (mutual_le_to_eq PB antiB
            (x := gal_l G (gal_r G (gal_l G a))) (y := gal_l G a) _).
  exact (@Build_Isomorphism (Proset PB) _ _
           (gal_lrl_below PA G a) (gal_lrl_above PB G a) I I).
Qed.

Lemma gal_rlr_eq (antiA : @Antisymmetric A eq eq_equiv RA) (b : B) :
  gal_r G (gal_l G (gal_r G b)) = gal_r G b.
Proof.
  refine (mutual_le_to_eq PA antiA
            (x := gal_r G (gal_l G (gal_r G b))) (y := gal_r G b) _).
  exact (@Build_Isomorphism (Proset PA) _ _
           (gal_rlr_below PA G b) (gal_rlr_above PB G b) I I).
Qed.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Lemma closed_r_eq (antiA : @Antisymmetric A eq eq_equiv RA) (a : A) :
  GalClosed_r G a ↔ gal_r G (gal_l G a) = a.
Proof.
  split.
  - intro H.
    refine (mutual_le_to_eq PA antiA
              (x := gal_r G (gal_l G a)) (y := a) _).
    exact (@Build_Isomorphism (Proset PA) _ _ H (gal_unit G PB a) I I).
  - intro Heq; unfold GalClosed_r; rewrite Heq.
    exact (@reflexivity A RA (@PreOrder_Reflexive A RA PA) a).
Qed.

Lemma closed_l_eq (antiB : @Antisymmetric B eq eq_equiv RB) (b : B) :
  GalClosed_l G b ↔ gal_l G (gal_r G b) = b.
Proof.
  split.
  - intro H.
    refine (mutual_le_to_eq PB antiB
              (x := gal_l G (gal_r G b)) (y := b) _).
    exact (@Build_Isomorphism (Proset PB) _ _ (gal_counit G PA b) H I I).
  - intro Heq; unfold GalClosed_l; rewrite Heq.
    exact (@reflexivity B RB (@PreOrder_Reflexive B RB PB) b).
Qed.

(*
   本节说明 FixedPoints 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma closed_r_iff_image_eq (antiA : @Antisymmetric A eq eq_equiv RA)
  (a : A) : GalClosed_r G a ↔ ∃ b : B, a = gal_r G b.
Proof.
  split.
  - intro H.
    exact (gal_l G a; eq_sym (fst (closed_r_eq antiA a) H)).
  - intros [b Heq]; rewrite Heq.
    exact (gal_closed_r_image PA G b).
Qed.

Lemma closed_l_iff_image_eq (antiB : @Antisymmetric B eq eq_equiv RB)
  (b : B) : GalClosed_l G b ↔ ∃ a : A, b = gal_l G a.
Proof.
  split.
  - intro H.
    exact (gal_r G b; eq_sym (fst (closed_l_eq antiB b) H)).
  - intros [a Heq]; rewrite Heq.
    exact (gal_closed_l_image PB G a).
Qed.

(* 相关说明。 （已译） *)

Definition closed_r_to_l (p : ∃ a : A, GalClosed_r G a) :
  ∃ b : B, GalClosed_l G b :=
  (gal_l G `1 p; gal_closed_l_image PB G `1 p).

Definition closed_l_to_r (q : ∃ b : B, GalClosed_l G b) :
  ∃ a : A, GalClosed_r G a :=
  (gal_r G `1 q; gal_closed_r_image PA G `1 q).

(* Both round trips return underlying element nose. The whole
 sigma not compared: second component [Prop] no 证明
 irrelevance available. （已译） *)
Lemma closed_round_r (antiA : @Antisymmetric A eq eq_equiv RA)
  (p : ∃ a : A, GalClosed_r G a) :
  `1 (closed_l_to_r (closed_r_to_l p)) = `1 p.
Proof. exact (fst (closed_r_eq antiA `1 p) `2 p). Qed.

Lemma closed_round_l (antiB : @Antisymmetric B eq eq_equiv RB)
  (q : ∃ b : B, GalClosed_l G b) :
  `1 (closed_r_to_l (closed_l_to_r q)) = `1 q.
Proof. exact (fst (closed_l_eq antiB `1 q) `2 q). Qed.

End GaloisFixed.

(* 相关说明。 （已译） *)

Section PowersetFixed.

Context {X Y : SetoidObject}.
Context (f : X ~{Sets}~> Y).

(* "f(X) = f(f^{-1}(f(X)))", at the power set's own [≈]. *)
Lemma image_preimage_image (S : carrier (Powerset_Prop_obj X)) :
  Powerset_Prop_image f
      (Powerset_Prop_preimage f (Powerset_Prop_image f S))
    ≈ Powerset_Prop_image f S.
Proof.
  apply subset_le_antisym.
  - exact (gal_lrl_below (subset_le_preorder X)
             (image_preimage_galois f) S).
  - exact (gal_lrl_above (subset_le_preorder Y)
             (image_preimage_galois f) S).
Qed.

(* "f^{-1}(f(f^{-1}(Y))) = f^{-1}(Y)". *)
Lemma preimage_image_preimage (T : carrier (Powerset_Prop_obj Y)) :
  Powerset_Prop_preimage f
      (Powerset_Prop_image f (Powerset_Prop_preimage f T))
    ≈ Powerset_Prop_preimage f T.
Proof.
  apply subset_le_antisym.
  - exact (gal_rlr_below (subset_le_preorder X)
             (image_preimage_galois f) T).
  - exact (gal_rlr_above (subset_le_preorder Y)
             (image_preimage_galois f) T).
Qed.

(* 相关说明。 （已译） *)
Definition image_closed_l (S : carrier (Powerset_Prop_obj X)) :
  GalClosed_l (image_preimage_galois f) (Powerset_Prop_image f S) :=
  gal_closed_l_image (subset_le_preorder Y) (image_preimage_galois f) S.

Definition preimage_closed_r (T : carrier (Powerset_Prop_obj Y)) :
  GalClosed_r (image_preimage_galois f) (Powerset_Prop_preimage f T) :=
  gal_closed_r_image (subset_le_preorder X) (image_preimage_galois f) T.

End PowersetFixed.

(* 相关说明。 （已译） *)

(*
   本节说明 FixedPoints 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma nat_shift_closed_r_iff (k a : nat) :
  GalClosed_r (nat_shift_galois k) a ↔ Nat.le k a.
Proof.
  unfold GalClosed_r; simpl; split; intro H; lia.
Qed.

(* On the right-hand side every element is closed: [(b + k) - k] is [b]. *)
Lemma nat_shift_closed_l_all (k b : nat) :
  GalClosed_l (nat_shift_galois k) b.
Proof. unfold GalClosed_l; simpl; lia. Qed.

(* 相关说明。 （已译） *)
Example nat_shift_two_one_not_closed :
  GalClosed_r (nat_shift_galois 2%nat) 1%nat → False.
Proof. intro H; pose proof (fst (nat_shift_closed_r_iff 2 1) H); lia. Qed.

Definition nat_shift_five_closed :
  GalClosed_r (nat_shift_galois 2%nat) 5%nat :=
  snd (nat_shift_closed_r_iff 2%nat 5%nat) (ltac:(lia)).

Example nat_shift_gal_l_five :
  gal_l (nat_shift_galois 2%nat) 5%nat = 3%nat := eq_refl.

(* [5] 对象 unit-fixed subcategory shift
 伴随, restricted 左伴随's value there. （已译） *)
Definition nat_shift_five_fixed :
  obj[Sub (Proset Nat.le_preorder)
        (UnitFixed (nat_shift_adjunction 2%nat))] :=
  (5%nat; snd (unit_fixed_iff_closed_r Nat.le_preorder Nat.le_preorder
                 (nat_shift_galois 2%nat) 5%nat) nat_shift_five_closed).

Example nat_shift_FixedL_obj :
  `1 (fobj[FixedL (nat_shift_adjunction 2%nat)] nat_shift_five_fixed)
    = 3%nat := eq_refl.

(* 相关说明。 （已译） *)

(*
   本节说明 FixedPoints 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition group_action_fixed_point_equivalence
  (G : GrpObject) (A : MSetoidAction (grp_mon G)) :
  EquivalenceOfCategories (FixedL (group_action_adjunction G A)) :=
  adjunction_fixed_point_equivalence (group_action_adjunction G A).
