Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Group.

Generalizable All Variables.

(* * * Ring semiring 对象 cartesian 范畴 （已译） *)

(*
   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CartesianMonoid.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

Example bimap_is_split {x y z w : C} (f : x ~> y) (g : z ~> w) :
  @bimap C C C (@tensor C CC_Monoidal) _ _ _ _ f g = split f g := eq_refl.

Example unit_left_is_exr {x : C} :
  to (@unit_left C CC_Monoidal x) = exr := eq_refl.

Example unit_right_is_exl {x : C} :
  to (@unit_right C CC_Monoidal x) = exl := eq_refl.

Example tensor_assoc_is_fork {x y z : C} :
  to (@tensor_assoc C CC_Monoidal x y z)
    = (exl ∘ exl) △ ((exr ∘ exl) △ exr) := eq_refl.

Context {m : C}.
Context (M : Monoid m).

Lemma cartesian_monoid_unit_left :
  (mappend[M] : m × m ~> m) ∘ split (mempty[M] : 1 ~> m) id ≈ exr.
Proof. exact (@mempty_left _ _ _ M). Qed.

Lemma cartesian_monoid_unit_right :
  (mappend[M] : m × m ~> m) ∘ split id (mempty[M] : 1 ~> m) ≈ exl.
Proof. exact (@mempty_right _ _ _ M). Qed.

Lemma cartesian_monoid_assoc :
  (mappend[M] : m × m ~> m) ∘ split (mappend[M] : m × m ~> m) id
    ≈ (mappend[M] : m × m ~> m) ∘ split id (mappend[M] : m × m ~> m)
        ∘ ((exl ∘ exl) △ ((exr ∘ exl) △ exr)).
Proof. exact (@mappend_assoc _ _ _ M). Qed.

End CartesianMonoid.

Section Duplication.

Context {C : Category}.
Context `{@Cartesian C}.

Definition dup_left {x : C} : x × (x × x) ~> (x × x) × (x × x) :=
  second exl △ second exr.

Definition dup_right {x : C} : (x × x) × x ~> (x × x) × (x × x) :=
  first exl △ first exr.

Lemma dup_left_fork {x w : C} (a b c : w ~> x) :
  dup_left ∘ (a △ (b △ c)) ≈ (a △ b) △ (a △ c).
Proof. unfold dup_left; unfork; cat. Qed.

Lemma dup_right_fork {x w : C} (a b c : w ~> x) :
  dup_right ∘ ((a △ b) △ c) ≈ (a △ c) △ (b △ c).
Proof. unfold dup_right; unfork; cat. Qed.

Lemma prod_assoc_fork {x w : C} (a b c : w ~> x) :
  ((exl ∘ exl) △ ((exr ∘ exl) △ exr)) ∘ ((a △ b) △ c) ≈ a △ (b △ c).
Proof. unfork; cat. Qed.

End Duplication.

Section Internalize.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

Class InternalSemiring (r : C) := {
  isr_add : Monoid r;
  isr_mul : Monoid r;

  isr_add_comm :
    (mappend[isr_add] : r × r ~> r) ∘ swap ≈ mappend[isr_add];

  isr_distrib_l :
    (mappend[isr_mul] : r × r ~> r) ∘ second (mappend[isr_add] : r × r ~> r)
      ≈ (mappend[isr_add] : r × r ~> r)
          ∘ split (mappend[isr_mul] : r × r ~> r) mappend[isr_mul]
          ∘ dup_left;
  isr_distrib_r :
    (mappend[isr_mul] : r × r ~> r) ∘ first (mappend[isr_add] : r × r ~> r)
      ≈ (mappend[isr_add] : r × r ~> r)
          ∘ split (mappend[isr_mul] : r × r ~> r) mappend[isr_mul]
          ∘ dup_right;

  isr_annihilate_l :
    (mappend[isr_mul] : r × r ~> r) ∘ (((mempty[isr_add] : 1 ~> r) ∘ one) △ id)
      ≈ (mempty[isr_add] : 1 ~> r) ∘ one;
  isr_annihilate_r :
    (mappend[isr_mul] : r × r ~> r) ∘ (id △ ((mempty[isr_add] : 1 ~> r) ∘ one))
      ≈ (mempty[isr_add] : 1 ~> r) ∘ one
}.

Class InternalRing (r : C) := {
  ir_add : Monoid r;
  ir_mul : Monoid r;
  ir_neg : r ~> r;

  ir_add_comm :
    (mappend[ir_add] : r × r ~> r) ∘ swap ≈ mappend[ir_add];
  ir_neg_left :
    (mappend[ir_add] : r × r ~> r) ∘ (ir_neg △ id)
      ≈ (mempty[ir_add] : 1 ~> r) ∘ one;

  ir_distrib_l :
    (mappend[ir_mul] : r × r ~> r) ∘ second (mappend[ir_add] : r × r ~> r)
      ≈ (mappend[ir_add] : r × r ~> r)
          ∘ split (mappend[ir_mul] : r × r ~> r) mappend[ir_mul]
          ∘ dup_left;
  ir_distrib_r :
    (mappend[ir_mul] : r × r ~> r) ∘ first (mappend[ir_add] : r × r ~> r)
      ≈ (mappend[ir_add] : r × r ~> r)
          ∘ split (mappend[ir_mul] : r × r ~> r) mappend[ir_mul]
          ∘ dup_right
}.

End Internalize.

Section RingDerived.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context {r : C}.
Context `{R : @InternalRing C _ _ r}.

Lemma ring_neg_right :
  (mappend[ir_add] : r × r ~> r) ∘ (id △ ir_neg)
    ≈ (mempty[ir_add] : 1 ~> r) ∘ one.
Proof.
  rewrite <- (swap_fork ir_neg id).
  rewrite comp_assoc.
  rewrite ir_add_comm.
  apply ir_neg_left.
Qed.

Lemma ring_add_zero_left {x : C} (g : x ~> r) :
  (mappend[ir_add] : r × r ~> r)
      ∘ (((mempty[ir_add] : 1 ~> r) ∘ one[x]) △ g)
    ≈ g.
Proof.
  transitivity ((mappend[ir_add] : r × r ~> r)
                  ∘ split (mempty[ir_add] : 1 ~> r) id ∘ (one[x] △ g)).
  { rewrite <- comp_assoc, split_fork.
    now rewrite id_left. }
  rewrite cartesian_monoid_unit_left.
  now rewrite exr_fork.
Qed.

Lemma ring_cancel_idem {x : C} (k : x ~> r) :
  k ≈ (mappend[ir_add] : r × r ~> r) ∘ (k △ k) →
  k ≈ (mempty[ir_add] : 1 ~> r) ∘ one.
Proof.
  intro Hk.
  assert (HA : (mappend[ir_add] : r × r ~> r) ∘ ((ir_neg ∘ k) △ k)
                 ≈ (mempty[ir_add] : 1 ~> r) ∘ one[x]).
  { rewrite <- (id_left k) at 2.
    rewrite fork_comp, comp_assoc, ir_neg_left, <- comp_assoc.
    now rewrite one_comp. }
  assert (HB : (mappend[ir_add] : r × r ~> r)
                 ∘ (((mempty[ir_add] : 1 ~> r) ∘ one[x]) △ k)
                 ≈ (mempty[ir_add] : 1 ~> r) ∘ one[x]).
  { transitivity ((mappend[ir_add] : r × r ~> r)
                    ∘ split (mappend[ir_add] : r × r ~> r) id
                    ∘ (((ir_neg ∘ k) △ k) △ k)).
    { rewrite <- comp_assoc, split_fork, HA.
      now rewrite id_left. }
    rewrite cartesian_monoid_assoc.
    rewrite <- comp_assoc, prod_assoc_fork.
    rewrite <- comp_assoc, split_fork, id_left, <- Hk.
    exact HA. }
  now rewrite <- HB, ring_add_zero_left.
Qed.

Lemma ring_annihilate_l :
  (mappend[ir_mul] : r × r ~> r)
      ∘ (((mempty[ir_add] : 1 ~> r) ∘ one) △ id)
    ≈ (mempty[ir_add] : 1 ~> r) ∘ one.
Proof.
  apply ring_cancel_idem.
  symmetry.
  transitivity ((mappend[ir_mul] : r × r ~> r)
                  ∘ first (mappend[ir_add] : r × r ~> r)
                  ∘ (((((mempty[ir_add] : 1 ~> r) ∘ one[r])
                        △ ((mempty[ir_add] : 1 ~> r) ∘ one[r]))) △ id)).
  { rewrite ir_distrib_r.
    rewrite <- !comp_assoc, dup_right_fork.
    now rewrite split_fork. }
  rewrite <- comp_assoc, first_fork, ring_add_zero_left.
  reflexivity.
Qed.

Lemma ring_annihilate_r :
  (mappend[ir_mul] : r × r ~> r)
      ∘ (id △ ((mempty[ir_add] : 1 ~> r) ∘ one))
    ≈ (mempty[ir_add] : 1 ~> r) ∘ one.
Proof.
  apply ring_cancel_idem.
  symmetry.
  transitivity ((mappend[ir_mul] : r × r ~> r)
                  ∘ second (mappend[ir_add] : r × r ~> r)
                  ∘ (id △ ((((mempty[ir_add] : 1 ~> r) ∘ one[r])
                        △ ((mempty[ir_add] : 1 ~> r) ∘ one[r]))))).
  { rewrite ir_distrib_l.
    rewrite <- !comp_assoc, dup_left_fork.
    now rewrite split_fork. }
  rewrite <- comp_assoc, second_fork, ring_add_zero_left.
  reflexivity.
Qed.

Lemma ir_neg_left_split :
  (mappend[ir_add] : r × r ~> r) ∘ split ir_neg id ∘ (id △ id)
    ≈ (mempty[ir_add] : 1 ~> r) ∘ one[r].
Proof.
  rewrite <- comp_assoc, split_fork, id_left, id_right.
  apply ir_neg_left.
Qed.

Lemma ir_neg_right_split :
  (mappend[ir_add] : r × r ~> r) ∘ split id ir_neg ∘ (id △ id)
    ≈ (mempty[ir_add] : 1 ~> r) ∘ one[r].
Proof.
  rewrite <- comp_assoc, split_fork, id_left, id_right.
  apply ring_neg_right.
Qed.

(* [Structure/Group.v] declares [Notation "'inverse' [ G ]"], which makes
 [inverse] 记法 keyword: neither [@inverse] nor record-literal
 field assignment [inverse := _] parses. The group 对象 is therefore
 built constructor applied positionally.（已译） *)
Definition InternalRing_GroupObject :
  @GroupObject C CC_CartesianMonoidal r :=
  @Build_GroupObject C CC_CartesianMonoidal r ir_add ir_neg
    ir_neg_left_split ir_neg_right_split.

Program Definition InternalRing_InternalSemiring :
  @InternalSemiring C _ _ r := {|
  isr_add := ir_add;
  isr_mul := ir_mul
|}.
Next Obligation. exact ir_add_comm. Qed.
Next Obligation. exact ir_distrib_l. Qed.
Next Obligation. exact ir_distrib_r. Qed.
Next Obligation. exact ring_annihilate_l. Qed.
Next Obligation. exact ring_annihilate_r. Qed.

End RingDerived.

Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Section SetsInternal.

Program Definition Sets_Monoid@{o so p} (A : SetoidObject@{o o})
  (u : carrier A) (op : carrier A → carrier A → carrier A)
  (opP : Proper@{o p} (equiv ==> equiv ==> equiv) op)
  (op_assoc : ∀ a b c, op (op a b) c ≈ op a (op b c))
  (unit_l : ∀ a, op u a ≈ a)
  (unit_r : ∀ a, op a u ≈ a) : @Monoid Sets@{o so} _ _ A := {|
  mempty := {| morphism := fun _ => u |};
  mappend := {| morphism := fun p => op (fst p) (snd p) |}
|}.
Next Obligation. proper; simpl in *; now apply opP. Qed.

Program Definition Sets_InternalSemiring@{o so q} (R : RigObject@{o o q}) :
  @InternalSemiring Sets@{o so} _ _ (rig_setoid R) := {|
  isr_add := Sets_Monoid (rig_setoid R) (rig_zero R) (rig_add R)
               (rig_add_respects R) (rig_add_assoc R) (rig_add_zero_l R)
               (rig_add_zero_r R);
  isr_mul := Sets_Monoid (rig_setoid R) (rig_one R) (rig_mul R)
               (rig_mul_respects R) (rig_mul_assoc R) (rig_mul_one_l R)
               (rig_mul_one_r R)
|}.
Next Obligation. now rewrite rig_add_comm. Qed.
Next Obligation. now rewrite rig_distr_l. Qed.
Next Obligation. now rewrite rig_distr_r. Qed.
Next Obligation. now rewrite rig_mul_zero_l. Qed.
Next Obligation. now rewrite rig_mul_zero_r. Qed.

Program Definition Sets_InternalRing@{o so q} (R : RingObject@{o o q}) :
  @InternalRing Sets@{o so} _ _ (rig_setoid R) := {|
  ir_add := Sets_Monoid (rig_setoid R) (rig_zero R) (rig_add R)
              (rig_add_respects R) (rig_add_assoc R) (rig_add_zero_l R)
              (rig_add_zero_r R);
  ir_mul := Sets_Monoid (rig_setoid R) (rig_one R) (rig_mul R)
              (rig_mul_respects R) (rig_mul_assoc R) (rig_mul_one_l R)
              (rig_mul_one_r R);
  ir_neg := {| morphism := ring_neg R |}
|}.
Next Obligation. now rewrite rig_add_comm. Qed.
Next Obligation. now rewrite ring_neg_l. Qed.
Next Obligation. now rewrite rig_distr_l. Qed.
Next Obligation. now rewrite rig_distr_r. Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Rig_of_InternalSemiring@{o so} {A : SetoidObject@{o o}}
  {PA : PropEquiv@{o o} (is_setoid A)}
  (S : @InternalSemiring Sets@{o so} _ _ A) : RigObject@{o o o} := {|
  rig_setoid := A;
  rig_zero := (mempty[isr_add] : _ ~{Sets}~> _) ttt;
  rig_add  := fun a b => (mappend[isr_add] : _ ~{Sets}~> _) (a, b);
  rig_one  := (mempty[isr_mul] : _ ~{Sets}~> _) ttt;
  rig_mul  := fun a b => (mappend[isr_mul] : _ ~{Sets}~> _) (a, b);

  rig_prop := PA
|}.
Next Obligation. proper; apply proper_morphism; simpl; split; assumption. Qed.
Next Obligation. proper; apply proper_morphism; simpl; split; assumption. Qed.
Next Obligation.
  exact (cartesian_monoid_assoc (@isr_add _ _ _ _ S) ((a, b), c)).
Qed.
Next Obligation. exact (@isr_add_comm _ _ _ _ S (b, a)). Qed.
Next Obligation.
  exact (cartesian_monoid_unit_left (@isr_add _ _ _ _ S) (ttt, a)).
Qed.
Next Obligation.
  exact (cartesian_monoid_assoc (@isr_mul _ _ _ _ S) ((a, b), c)).
Qed.
Next Obligation.
  exact (cartesian_monoid_unit_left (@isr_mul _ _ _ _ S) (ttt, a)).
Qed.
Next Obligation.
  exact (cartesian_monoid_unit_right (@isr_mul _ _ _ _ S) (a, ttt)).
Qed.
Next Obligation. exact (@isr_distrib_l _ _ _ _ S (a, (b, c))). Qed.
Next Obligation. exact (@isr_distrib_r _ _ _ _ S ((a, b), c)). Qed.
Next Obligation. exact (@isr_annihilate_l _ _ _ _ S a). Qed.
Next Obligation. exact (@isr_annihilate_r _ _ _ _ S a). Qed.


Program Definition Ring_of_InternalRing@{o so} {A : SetoidObject@{o o}}
  {PA : PropEquiv@{o o} (is_setoid A)}
  (R : @InternalRing Sets@{o so} _ _ A) : RingObject@{o o o} := {|
  ring_rig := Rig_of_InternalSemiring
                (@InternalRing_InternalSemiring Sets _ _ A R);
  ring_neg := fun a => (ir_neg : _ ~{Sets}~> _) a
|}.
Next Obligation. proper; now apply proper_morphism. Qed.
Next Obligation. exact (@ir_neg_left _ _ _ _ R a). Qed.

End SetsInternal.

Section SetsRoundTrip.

Context (R : RigObject).

Example rig_round_setoid :
  rig_setoid (Rig_of_InternalSemiring (Sets_InternalSemiring R))
    = rig_setoid R := eq_refl.
Example rig_round_zero :
  rig_zero (Rig_of_InternalSemiring (Sets_InternalSemiring R))
    = rig_zero R := eq_refl.
Example rig_round_add :
  rig_add (Rig_of_InternalSemiring (Sets_InternalSemiring R))
    = rig_add R := eq_refl.
Example rig_round_one :
  rig_one (Rig_of_InternalSemiring (Sets_InternalSemiring R))
    = rig_one R := eq_refl.
Example rig_round_mul :
  rig_mul (Rig_of_InternalSemiring (Sets_InternalSemiring R))
    = rig_mul R := eq_refl.

Fail Example rig_round_record :
  (Rig_of_InternalSemiring (Sets_InternalSemiring R)) = R := eq_refl.

Context {A : SetoidObject}.
(*
   本节说明 Ring 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Context (PA : PropEquiv (is_setoid A)).
Context (S : @InternalSemiring Sets _ _ A).

Example semiring_round_add (a b : carrier A) :
  (mappend[@isr_add _ _ _ _
     (Sets_InternalSemiring (Rig_of_InternalSemiring S))] : _ ~{Sets}~> _)
    (a, b)
  = (mappend[@isr_add _ _ _ _ S] : _ ~{Sets}~> _) (a, b) := eq_refl.

Example semiring_round_zero :
  (mempty[@isr_add _ _ _ _
     (Sets_InternalSemiring (Rig_of_InternalSemiring S))] : _ ~{Sets}~> _) ttt
  = (mempty[@isr_add _ _ _ _ S] : _ ~{Sets}~> _) ttt := eq_refl.

Fail Example semiring_round_monoid :
  (@isr_add _ _ _ _ (Sets_InternalSemiring (Rig_of_InternalSemiring S)))
    = (@isr_add _ _ _ _ S) := eq_refl.

End SetsRoundTrip.

Section SetsWitness.

Definition Nat_ISemiring : @InternalSemiring Sets _ _ nat_setoid_object :=
  Sets_InternalSemiring Nat_Rig.

Definition Int_IRing : @InternalRing Sets _ _ (rig_setoid Int_Ring) :=
  Sets_InternalRing Int_Ring.

Example nat_zero_computes :
  (mempty[@isr_add _ _ _ _ Nat_ISemiring] : _ ~{Sets}~> _) ttt = 0%nat
  := eq_refl.
Example nat_one_computes :
  (mempty[@isr_mul _ _ _ _ Nat_ISemiring] : _ ~{Sets}~> _) ttt = 1%nat
  := eq_refl.
Example nat_add_computes :
  (mappend[@isr_add _ _ _ _ Nat_ISemiring] : _ ~{Sets}~> _) (2%nat, 3%nat)
    = 5%nat := eq_refl.
Example nat_mul_computes :
  (mappend[@isr_mul _ _ _ _ Nat_ISemiring] : _ ~{Sets}~> _) (2%nat, 3%nat)
    = 6%nat := eq_refl.

Lemma nat_semiring_nondegenerate :
  (mempty[@isr_add _ _ _ _ Nat_ISemiring] : _ ~{Sets}~> _) ttt
    <> (mempty[@isr_mul _ _ _ _ Nat_ISemiring] : _ ~{Sets}~> _) ttt.
Proof. discriminate. Qed.

Example int_neg_computes :
  (@ir_neg _ _ _ _ Int_IRing : _ ~{Sets}~> _) 7%Z = (-7)%Z := eq_refl.

Lemma int_ring_nondegenerate :
  (mempty[@ir_add _ _ _ _ Int_IRing] : _ ~{Sets}~> _) ttt
    <> (mempty[@ir_mul _ _ _ _ Int_IRing] : _ ~{Sets}~> _) ttt.
Proof. discriminate. Qed.

Definition int_annihilate_instance := @ring_annihilate_l Sets _ _ _ Int_IRing.

End SetsWitness.

Section LawsConstrain.

#[local] Ltac bool_crush :=
  repeat intro; simpl in *;
  repeat match goal with [ b : bool |- _ ] => destruct b end;
  simpl in *; congruence.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Bool_Or_Monoid : @Monoid Sets _ _ bool_setoid_object :=
  Sets_Monoid bool_setoid_object false orb _ _ _ _.
Next Obligation. bool_crush. Qed.
Next Obligation. bool_crush. Qed.

Lemma bool_or_comm :
  (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _) ∘ swap
    ≈ mappend[Bool_Or_Monoid].
Proof. intros [[|] [|]]; reflexivity. Qed.

Lemma bool_or_distrib_l :
  (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
      ∘ second (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
    ≈ (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
        ∘ split (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
                mappend[Bool_Or_Monoid]
        ∘ dup_left.
Proof. intros [[|] [[|] [|]]]; reflexivity. Qed.

Lemma bool_or_distrib_r :
  (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
      ∘ first (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
    ≈ (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
        ∘ split (mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
                mappend[Bool_Or_Monoid]
        ∘ dup_right.
Proof. intros [[[|] [|]] [|]]; reflexivity. Qed.

Lemma bool_or_not_annihilating :
  ((mappend[Bool_Or_Monoid] : _ × _ ~{Sets}~> _)
      ∘ (((mempty[Bool_Or_Monoid] : 1 ~{Sets}~> _) ∘ one) △ id)
    ≈ (mempty[Bool_Or_Monoid] : 1 ~{Sets}~> _) ∘ one) → False.
Proof. intro Hx; specialize (Hx true); discriminate. Qed.

Definition Nat_Plus_Monoid : @Monoid Sets _ _ nat_setoid_object :=
  @isr_add _ _ _ _ Nat_ISemiring.

Lemma nat_plus_not_distributive :
  ((mappend[Nat_Plus_Monoid] : _ × _ ~{Sets}~> _)
      ∘ second (mappend[Nat_Plus_Monoid] : _ × _ ~{Sets}~> _)
    ≈ (mappend[Nat_Plus_Monoid] : _ × _ ~{Sets}~> _)
        ∘ split (mappend[Nat_Plus_Monoid] : _ × _ ~{Sets}~> _)
                mappend[Nat_Plus_Monoid]
        ∘ dup_left) → False.
Proof. intro Hx; specialize (Hx (1%nat, (0%nat, 0%nat))); discriminate. Qed.

End LawsConstrain.
