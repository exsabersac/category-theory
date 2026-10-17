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

Generalizable All Variables.

(** * Lattice objects in a cartesian category *)

(*
   本文件给出子对象格相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Internalize.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

Example lat_bimap_is_split {x y z w : C} (f : x ~> y) (g : z ~> w) :
  @bimap C C C (@tensor C CC_Monoidal) _ _ _ _ f g = split f g := eq_refl.

Example lat_unit_left_is_exr {x : C} :
  to (@unit_left C CC_Monoidal x) = exr := eq_refl.

Class InternalSemilattice (x : C) := {
  isl_mon : Monoid x;

  isl_comm : (mappend[isl_mon] : x × x ~> x) ∘ swap ≈ mappend[isl_mon];
  isl_idem : (mappend[isl_mon] : x × x ~> x) ∘ (id △ id) ≈ id
}.

Class InternalLattice (x : C) := {
  il_join : Monoid x;
  il_meet : Monoid x;

  il_join_comm : (mappend[il_join] : x × x ~> x) ∘ swap ≈ mappend[il_join];
  il_meet_comm : (mappend[il_meet] : x × x ~> x) ∘ swap ≈ mappend[il_meet];

  il_absorb_meet :
    (mappend[il_meet] : x × x ~> x)
      ∘ (exl △ (mappend[il_join] : x × x ~> x)) ≈ exl;
  il_absorb_join :
    (mappend[il_join] : x × x ~> x)
      ∘ (exl △ (mappend[il_meet] : x × x ~> x)) ≈ exl
}.

End Internalize.

Section LatticeDerived.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context {x : C}.
Context `{L : @InternalLattice C _ _ x}.

Lemma lattice_join_idem :
  (mappend[il_join] : x × x ~> x) ∘ (id △ id) ≈ id.
Proof.
  assert (HI : (mappend[il_meet] : x × x ~> x)
                 ∘ (id △ ((mappend[il_join] : x × x ~> x) ∘ (id △ id)))
               ≈ id).
  { transitivity ((mappend[il_meet] : x × x ~> x)
                    ∘ (exl △ (mappend[il_join] : x × x ~> x))
                    ∘ (id △ id)).
    { rewrite <- comp_assoc, <- fork_comp.
      now rewrite exl_fork. }
    rewrite il_absorb_meet.
    now rewrite exl_fork. }
  transitivity ((mappend[il_join] : x × x ~> x)
                  ∘ (exl △ (mappend[il_meet] : x × x ~> x))
                  ∘ (id △ ((mappend[il_join] : x × x ~> x) ∘ (id △ id)))).
  { rewrite <- comp_assoc, <- fork_comp, exl_fork.
    now rewrite HI. }
  rewrite il_absorb_join.
  now rewrite exl_fork.
Qed.

Lemma lattice_meet_idem :
  (mappend[il_meet] : x × x ~> x) ∘ (id △ id) ≈ id.
Proof.
  assert (HI : (mappend[il_join] : x × x ~> x)
                 ∘ (id △ ((mappend[il_meet] : x × x ~> x) ∘ (id △ id)))
               ≈ id).
  { transitivity ((mappend[il_join] : x × x ~> x)
                    ∘ (exl △ (mappend[il_meet] : x × x ~> x))
                    ∘ (id △ id)).
    { rewrite <- comp_assoc, <- fork_comp.
      now rewrite exl_fork. }
    rewrite il_absorb_join.
    now rewrite exl_fork. }
  transitivity ((mappend[il_meet] : x × x ~> x)
                  ∘ (exl △ (mappend[il_join] : x × x ~> x))
                  ∘ (id △ ((mappend[il_meet] : x × x ~> x) ∘ (id △ id)))).
  { rewrite <- comp_assoc, <- fork_comp, exl_fork.
    now rewrite HI. }
  rewrite il_absorb_meet.
  now rewrite exl_fork.
Qed.

Lemma lattice_join_bot_left {w : C} (g : w ~> x) :
  (mappend[il_join] : x × x ~> x)
      ∘ (((mempty[il_join] : 1 ~> x) ∘ one[w]) △ g) ≈ g.
Proof.
  assert (Hu : (mappend[il_join] : x × x ~> x)
                 ∘ split (mempty[il_join] : 1 ~> x) id ≈ exr)
    by exact (@mempty_left _ _ _ il_join).
  transitivity ((mappend[il_join] : x × x ~> x)
                  ∘ split (mempty[il_join] : 1 ~> x) id ∘ (one[w] △ g)).
  { rewrite <- comp_assoc, split_fork.
    now rewrite id_left. }
  rewrite Hu.
  now rewrite exr_fork.
Qed.

Lemma lattice_meet_top_left {w : C} (g : w ~> x) :
  (mappend[il_meet] : x × x ~> x)
      ∘ (((mempty[il_meet] : 1 ~> x) ∘ one[w]) △ g) ≈ g.
Proof.
  assert (Hu : (mappend[il_meet] : x × x ~> x)
                 ∘ split (mempty[il_meet] : 1 ~> x) id ≈ exr)
    by exact (@mempty_left _ _ _ il_meet).
  transitivity ((mappend[il_meet] : x × x ~> x)
                  ∘ split (mempty[il_meet] : 1 ~> x) id ∘ (one[w] △ g)).
  { rewrite <- comp_assoc, split_fork.
    now rewrite id_left. }
  rewrite Hu.
  now rewrite exr_fork.
Qed.

(* The bottom element annihilates the meet: it is NOT a field, but a
   consequence of absorption together with the join unit law. *)
Lemma lattice_bot_meet :
  (mappend[il_meet] : x × x ~> x)
      ∘ (((mempty[il_join] : 1 ~> x) ∘ one) △ id)
    ≈ (mempty[il_join] : 1 ~> x) ∘ one.
Proof.
  transitivity ((mappend[il_join] : x × x ~> x)
                  ∘ ((((mempty[il_join] : 1 ~> x) ∘ one[x]))
                       △ ((mappend[il_meet] : x × x ~> x)
                            ∘ ((((mempty[il_join] : 1 ~> x) ∘ one[x]))
                                 △ id)))).
  { now rewrite lattice_join_bot_left. }
  transitivity ((mappend[il_join] : x × x ~> x)
                  ∘ (exl △ (mappend[il_meet] : x × x ~> x))
                  ∘ ((((mempty[il_join] : 1 ~> x) ∘ one[x])) △ id)).
  { rewrite <- comp_assoc, <- fork_comp.
    now rewrite exl_fork. }
  rewrite il_absorb_join.
  now rewrite exl_fork.
Qed.

(* Dually, the top element annihilates the join. *)
Lemma lattice_top_join :
  (mappend[il_join] : x × x ~> x)
      ∘ (((mempty[il_meet] : 1 ~> x) ∘ one) △ id)
    ≈ (mempty[il_meet] : 1 ~> x) ∘ one.
Proof.
  transitivity ((mappend[il_meet] : x × x ~> x)
                  ∘ ((((mempty[il_meet] : 1 ~> x) ∘ one[x]))
                       △ ((mappend[il_join] : x × x ~> x)
                            ∘ ((((mempty[il_meet] : 1 ~> x) ∘ one[x]))
                                 △ id)))).
  { now rewrite lattice_meet_top_left. }
  transitivity ((mappend[il_meet] : x × x ~> x)
                  ∘ (exl △ (mappend[il_join] : x × x ~> x))
                  ∘ ((((mempty[il_meet] : 1 ~> x) ∘ one[x])) △ id)).
  { rewrite <- comp_assoc, <- fork_comp.
    now rewrite exl_fork. }
  rewrite il_absorb_meet.
  now rewrite exl_fork.
Qed.

Program Definition InternalLattice_join_Semilattice :
  @InternalSemilattice C _ _ x := {| isl_mon := il_join |}.
Next Obligation. exact il_join_comm. Qed.
Next Obligation. exact lattice_join_idem. Qed.

Program Definition InternalLattice_meet_Semilattice :
  @InternalSemilattice C _ _ x := {| isl_mon := il_meet |}.
Next Obligation. exact il_meet_comm. Qed.
Next Obligation. exact lattice_meet_idem. Qed.

End LatticeDerived.

Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.

(** ** Bounded lattices on a setoid carrier *)

Record SetoidLattice := {
  sl_setoid :> SetoidObject;

  sl_bot  : carrier sl_setoid;
  sl_join : carrier sl_setoid → carrier sl_setoid → carrier sl_setoid;
  sl_top  : carrier sl_setoid;
  sl_meet : carrier sl_setoid → carrier sl_setoid → carrier sl_setoid;

  sl_join_respects : Proper (equiv ==> equiv ==> equiv) sl_join;
  sl_meet_respects : Proper (equiv ==> equiv ==> equiv) sl_meet;

  sl_join_assoc : ∀ a b c,
    sl_join (sl_join a b) c ≈ sl_join a (sl_join b c);
  sl_join_comm : ∀ a b, sl_join a b ≈ sl_join b a;
  sl_join_bot_l : ∀ a, sl_join sl_bot a ≈ a;

  sl_meet_assoc : ∀ a b c,
    sl_meet (sl_meet a b) c ≈ sl_meet a (sl_meet b c);
  sl_meet_comm : ∀ a b, sl_meet a b ≈ sl_meet b a;
  sl_meet_top_l : ∀ a, sl_meet sl_top a ≈ a;

  sl_absorb_meet : ∀ a b, sl_meet a (sl_join a b) ≈ a;
  sl_absorb_join : ∀ a b, sl_join a (sl_meet a b) ≈ a
}.

#[export] Existing Instance sl_join_respects.
#[export] Existing Instance sl_meet_respects.

Corollary sl_join_bot_r (L : SetoidLattice) (a : carrier (sl_setoid L)) :
  sl_join L a (sl_bot L) ≈ a.
Proof. rewrite sl_join_comm; apply sl_join_bot_l. Qed.

Corollary sl_meet_top_r (L : SetoidLattice) (a : carrier (sl_setoid L)) :
  sl_meet L a (sl_top L) ≈ a.
Proof. rewrite sl_meet_comm; apply sl_meet_top_l. Qed.

(* Idempotence is derived from the two absorption laws alone -- the
   set-level shadow of [lattice_join_idem] / [lattice_meet_idem]. *)
Corollary sl_join_idem (L : SetoidLattice) (a : carrier (sl_setoid L)) :
  sl_join L a a ≈ a.
Proof.
  rewrite <- (sl_absorb_meet L a (sl_join L a a)) at 2.
  now rewrite sl_absorb_join.
Qed.

Corollary sl_meet_idem (L : SetoidLattice) (a : carrier (sl_setoid L)) :
  sl_meet L a a ≈ a.
Proof.
  rewrite <- (sl_absorb_join L a (sl_meet L a a)) at 2.
  now rewrite sl_absorb_meet.
Qed.

Section SetsInternal.

(*
   本节说明 Lattice 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Sets_Monoid_on@{o so p} (A : SetoidObject@{o o})
  (u : carrier A) (op : carrier A → carrier A → carrier A)
  (opP : Proper@{o p} (equiv ==> equiv ==> equiv) op)
  (op_assoc : ∀ a b c, op (op a b) c ≈ op a (op b c))
  (unit_l : ∀ a, op u a ≈ a)
  (unit_r : ∀ a, op a u ≈ a) : @Monoid Sets@{o so} _ _ A := {|
  mempty := {| morphism := fun _ => u |};
  mappend := {| morphism := fun p => op (fst p) (snd p) |}
|}.
Next Obligation. proper; simpl in *; now apply opP. Qed.

Program Definition Sets_InternalLattice@{o so q} (L : SetoidLattice@{o o q}) :
  @InternalLattice Sets@{o so} _ _ (sl_setoid L) := {|
  il_join := Sets_Monoid_on (sl_setoid L) (sl_bot L) (sl_join L)
               (sl_join_respects L) (sl_join_assoc L) (sl_join_bot_l L)
               (sl_join_bot_r L);
  il_meet := Sets_Monoid_on (sl_setoid L) (sl_top L) (sl_meet L)
               (sl_meet_respects L) (sl_meet_assoc L) (sl_meet_top_l L)
               (sl_meet_top_r L)
|}.
Next Obligation. now rewrite sl_join_comm. Qed.
Next Obligation. now rewrite sl_meet_comm. Qed.
Next Obligation. now rewrite sl_absorb_meet. Qed.
Next Obligation. now rewrite sl_absorb_join. Qed.

Program Definition SetoidLattice_of_InternalLattice@{o so}
  {A : SetoidObject@{o o}} (L : @InternalLattice Sets@{o so} _ _ A) :
  SetoidLattice@{o o o} := {|
  sl_setoid := A;
  sl_bot  := (mempty[il_join] : _ ~{Sets}~> _) ttt;
  sl_join := fun a b => (mappend[il_join] : _ ~{Sets}~> _) (a, b);
  sl_top  := (mempty[il_meet] : _ ~{Sets}~> _) ttt;
  sl_meet := fun a b => (mappend[il_meet] : _ ~{Sets}~> _) (a, b)
|}.
Next Obligation. proper; apply proper_morphism; simpl; split; assumption. Qed.
Next Obligation. proper; apply proper_morphism; simpl; split; assumption. Qed.
Next Obligation.
  exact (@mappend_assoc _ _ _ (@il_join _ _ _ _ L) ((a, b), c)).
Qed.
Next Obligation. exact (@il_join_comm _ _ _ _ L (b, a)). Qed.
Next Obligation. exact (@mempty_left _ _ _ (@il_join _ _ _ _ L) (ttt, a)). Qed.
Next Obligation.
  exact (@mappend_assoc _ _ _ (@il_meet _ _ _ _ L) ((a, b), c)).
Qed.
Next Obligation. exact (@il_meet_comm _ _ _ _ L (b, a)). Qed.
Next Obligation. exact (@mempty_left _ _ _ (@il_meet _ _ _ _ L) (ttt, a)). Qed.
Next Obligation. exact (@il_absorb_meet _ _ _ _ L (a, b)). Qed.
Next Obligation. exact (@il_absorb_join _ _ _ _ L (a, b)). Qed.

End SetsInternal.

Section SetsRoundTrip.

Context (L : SetoidLattice).

Example lat_round_setoid :
  sl_setoid (SetoidLattice_of_InternalLattice (Sets_InternalLattice L))
    = sl_setoid L := eq_refl.
Example lat_round_bot :
  sl_bot (SetoidLattice_of_InternalLattice (Sets_InternalLattice L))
    = sl_bot L := eq_refl.
Example lat_round_join :
  sl_join (SetoidLattice_of_InternalLattice (Sets_InternalLattice L))
    = sl_join L := eq_refl.
Example lat_round_top :
  sl_top (SetoidLattice_of_InternalLattice (Sets_InternalLattice L))
    = sl_top L := eq_refl.
Example lat_round_meet :
  sl_meet (SetoidLattice_of_InternalLattice (Sets_InternalLattice L))
    = sl_meet L := eq_refl.

Fail Example lat_round_record :
  (SetoidLattice_of_InternalLattice (Sets_InternalLattice L)) = L := eq_refl.

Context {A : SetoidObject}.
Context (K : @InternalLattice Sets _ _ A).

Example ilattice_round_join (a b : carrier A) :
  (mappend[@il_join _ _ _ _
     (Sets_InternalLattice (SetoidLattice_of_InternalLattice K))]
     : _ ~{Sets}~> _) (a, b)
  = (mappend[@il_join _ _ _ _ K] : _ ~{Sets}~> _) (a, b) := eq_refl.

Example ilattice_round_bot :
  (mempty[@il_join _ _ _ _
     (Sets_InternalLattice (SetoidLattice_of_InternalLattice K))]
     : _ ~{Sets}~> _) ttt
  = (mempty[@il_join _ _ _ _ K] : _ ~{Sets}~> _) ttt := eq_refl.

Fail Example ilattice_round_monoid :
  (@il_join _ _ _ _
     (Sets_InternalLattice (SetoidLattice_of_InternalLattice K)))
    = (@il_join _ _ _ _ K) := eq_refl.

End SetsRoundTrip.

Section BoolWitness.

Definition bool_setoid_obj : SetoidObject := {|
  carrier := bool;
  is_setoid := {| equiv := @eq bool; setoid_equiv := eq_equivalence |}
|}.

#[local] Ltac bool_crush :=
  repeat intro; simpl in *;
  repeat match goal with [ b : bool |- _ ] => destruct b end;
  simpl in *; congruence.

Program Definition Bool_Lattice : SetoidLattice := {|
  sl_setoid := bool_setoid_obj;
  sl_bot  := false;
  sl_join := orb;
  sl_top  := true;
  sl_meet := andb
|}.
Next Obligation. bool_crush. Qed.
Next Obligation. bool_crush. Qed.
Next Obligation. bool_crush. Qed.
Next Obligation. bool_crush. Qed.
Next Obligation. bool_crush. Qed.
Next Obligation. bool_crush. Qed.

Definition Bool_ILattice : @InternalLattice Sets _ _ bool_setoid_obj :=
  Sets_InternalLattice Bool_Lattice.

Example bool_bot_computes :
  (mempty[@il_join _ _ _ _ Bool_ILattice] : _ ~{Sets}~> _) ttt = false
  := eq_refl.
Example bool_top_computes :
  (mempty[@il_meet _ _ _ _ Bool_ILattice] : _ ~{Sets}~> _) ttt = true
  := eq_refl.
Example bool_join_computes :
  (mappend[@il_join _ _ _ _ Bool_ILattice] : _ ~{Sets}~> _) (false, true)
    = true := eq_refl.
Example bool_meet_computes :
  (mappend[@il_meet _ _ _ _ Bool_ILattice] : _ ~{Sets}~> _) (false, true)
    = false := eq_refl.

Lemma bool_lattice_nondegenerate :
  (mempty[@il_join _ _ _ _ Bool_ILattice] : _ ~{Sets}~> _) ttt
    <> (mempty[@il_meet _ _ _ _ Bool_ILattice] : _ ~{Sets}~> _) ttt.
Proof. discriminate. Qed.

Definition Bool_Semilattice : @InternalSemilattice Sets _ _ bool_setoid_obj :=
  @InternalLattice_join_Semilattice Sets _ _ _ Bool_ILattice.

End BoolWitness.

Section LawsConstrain.

#[local] Ltac bool_crush :=
  repeat intro; simpl in *;
  repeat match goal with [ b : bool |- _ ] => destruct b end;
  simpl in *; congruence.

Definition Bool_Join_Monoid : @Monoid Sets _ _ bool_setoid_obj :=
  @il_join _ _ _ _ Bool_ILattice.

Lemma bool_join_comm :
  (mappend[Bool_Join_Monoid] : _ × _ ~{Sets}~> _) ∘ swap
    ≈ mappend[Bool_Join_Monoid].
Proof. exact (@il_join_comm _ _ _ _ Bool_ILattice). Qed.

Lemma bool_join_not_absorbing :
  ((mappend[Bool_Join_Monoid] : _ × _ ~{Sets}~> _)
      ∘ (exl △ (mappend[Bool_Join_Monoid] : _ × _ ~{Sets}~> _)) ≈ exl) → False.
Proof. intro Hx; specialize (Hx (false, true)); discriminate. Qed.

Program Definition Bool_Xor_Monoid : @Monoid Sets _ _ bool_setoid_obj :=
  Sets_Monoid_on bool_setoid_obj false xorb _ _ _ _.
Next Obligation. bool_crush. Qed.
Next Obligation. bool_crush. Qed.

Lemma bool_xor_comm :
  (mappend[Bool_Xor_Monoid] : _ × _ ~{Sets}~> _) ∘ swap
    ≈ mappend[Bool_Xor_Monoid].
Proof. intros [[|] [|]]; reflexivity. Qed.

Lemma bool_xor_not_idempotent :
  ((mappend[Bool_Xor_Monoid] : _ × _ ~{Sets}~> _) ∘ (id △ id) ≈ id) → False.
Proof. intro Hx; specialize (Hx true); discriminate. Qed.

End LawsConstrain.
