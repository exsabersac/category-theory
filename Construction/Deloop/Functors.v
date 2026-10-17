Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Opposite.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Deloop.Transform.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Matr.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The spine: functors out of a delooping pick an endomorphism
    monoid *)

Section Spine.

Context {M : MonObject}.
Context {C : Category}.

Program Definition functor_of_hom_monoid (c : C)
  (h : MonHom M (hom_monoid C c)) : Deloop M ⟶ C := {|
  fobj := fun _ => c;
  fmap := fun _ _ (g : carrier M) => mon_map h g
|}.
Next Obligation.
  intros c h x y f g Hfg; exact (mon_map_respects h _ _ Hfg).
Qed.
Next Obligation. intros c h x; exact (mon_map_unit h). Qed.
Next Obligation. intros c h x y z f g; exact (mon_map_op h f g). Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition hom_monoid_of_functor (F : Deloop M ⟶ C) :
  MonHom M (hom_monoid C (F ttt)) :=
  @Build_MonHom M (hom_monoid C (F ttt))
    (fun g : carrier M => @fmap _ _ F ttt ttt g)
    (@fmap_respects _ _ F ttt ttt)
    (@fmap_id _ _ F ttt)
    (fun a b => @fmap_comp _ _ F ttt ttt ttt a b).

(* Round trip on the homomorphism side: the same map, pointwise. *)
Lemma hom_monoid_round (c : C) (h : MonHom M (hom_monoid C c))
  (g : carrier M) :
  mon_map (hom_monoid_of_functor (functor_of_hom_monoid c h)) g
    ≈ mon_map h g.
Proof. reflexivity. Qed.

(* Round trip on the functor side: the same functor up to natural
   isomorphism, with identity components. *)
Lemma functor_round (F : Deloop M ⟶ C) :
  functor_of_hom_monoid (F ttt) (hom_monoid_of_functor F) ≈ F.
Proof.
  exists (fun x => match x as x0 return (F ttt ≅ F x0) with
                   | ttt => iso_id
                   end).
  intros [] [] g; simpl.
  rewrite id_left, id_right.
  reflexivity.
Qed.

End Spine.

(** ** Part (b): functors between deloopings are homomorphisms *)

(*
   本节说明 Functors 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section PartB.

Context {M N : MonObject}.

(*
   本节说明 Functors 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Deloop_map_spine (h : MonHom M N) :
  Deloop_map h ≈ functor_of_hom_monoid (C := Deloop N) ttt h.
Proof.
  exists (fun x => iso_id).
  intros [] [] g; simpl.
  now rewrite mon_op_unit_l, mon_op_unit_r.
Qed.

(* The functor-side round trip, at [Functor_Setoid] strength. *)
Lemma Deloop_functor_round (F : Deloop M ⟶ Deloop N) :
  Deloop_map (Deloop_unmap F) ≈ F.
Proof.
  unshelve eexists.
  { intro x.
    exact (@Build_Isomorphism (Deloop N) _ _
             (mon_unit : carrier N) (mon_unit : carrier N)
             (mon_op_unit_l mon_unit) (mon_op_unit_l mon_unit)). }
  intros [] [] g; simpl.
  now rewrite mon_op_unit_l, mon_op_unit_r.
Qed.

End PartB.

(** ** Part (c): permutation representations — actions on setoids *)

(* A monoid acting on a setoid; at a [GrpObject] this is a permutation
   representation / G-set (Riehl 1.3.9, left convention: the action law
   is act (g · h) = act g ∘ act h, matching Deloop's composition). *)
Record MSetoidAction (M : MonObject) := {
  act_setoid :> SetoidObject;
  act : carrier M → carrier act_setoid → carrier act_setoid;
  act_respects : Proper (equiv ==> equiv ==> equiv) act;
  act_unit : ∀ x, act mon_unit x ≈ x;
  act_op : ∀ g h x, act (mon_op g h) x ≈ act g (act h x)
}.

Arguments act_setoid {M} _.
Arguments act {M} _ _ _.
Arguments act_respects {M} _.
Arguments act_unit {M} _ _.
Arguments act_op {M} _ _ _ _.

#[export] Existing Instance act_respects.

Section PartC.

Context {M : MonObject}.

Program Definition action_of_functor (F : Deloop M ⟶ Sets) :
  MSetoidAction M := {|
  act_setoid := F ttt;
  act := fun g x => @fmap _ _ F ttt ttt g x;
  act_unit := fun x => @fmap_id _ _ F ttt x;
  act_op := fun g h x => @fmap_comp _ _ F ttt ttt ttt g h x
|}.
Next Obligation.
  intros F g g' Hg x x' Hx.
  rewrite (@fmap_respects _ _ F ttt ttt g g' Hg x).
  exact (proper_morphism (@fmap _ _ F ttt ttt g') _ _ Hx).
Qed.

Program Definition functor_of_action (A : MSetoidAction M) :
  Deloop M ⟶ Sets := {|
  fobj := fun _ => act_setoid A;
  fmap := fun _ _ (g : carrier M) =>
    {| morphism := act A g
     ; proper_morphism := act_respects A g g (Equivalence_Reflexive g) |}
|}.
Next Obligation.
  intros A0 x y f g Hfg p; simpl.
  exact (act_respects A0 f g Hfg p p (Equivalence_Reflexive p)).
Qed.
Next Obligation. intros A0 x p; apply act_unit. Qed.
Next Obligation. intros A0 x y z f g p; apply act_op. Qed.

Lemma action_round (A : MSetoidAction M) (g : carrier M)
  (x : carrier (act_setoid A)) :
  act (action_of_functor (functor_of_action A)) g x ≈ act A g x.
Proof. reflexivity. Qed.

Lemma action_functor_round (F : Deloop M ⟶ Sets) :
  functor_of_action (action_of_functor F) ≈ F.
Proof.
  exists (fun x => match x as x0 return (F ttt ≅ F x0) with
                   | ttt => iso_id
                   end).
  intros [] [] g x; simpl.
  reflexivity.
Qed.

End PartC.

(** ** Part (c): matrix representations *)

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition MatrixRep (M : MonObject) (R : RigObject) : Type :=
  { n : nat & MonHom M (hom_monoid (Matr R) n) }.

Definition functor_of_matrix_rep {M : MonObject} {R : RigObject}
  (ρ : MatrixRep M R) : Deloop M ⟶ Matr R :=
  functor_of_hom_monoid (C := Matr R) (`1 ρ) (`2 ρ).

(* The sigma's family is supplied explicitly rather than left to
   unification: inferring it requires unfolding [obj] at [Matr R],
   which Coq 8.19/8.20's unifier declines in evar problems (the same
   version split as Monotone.v's [nondecreasing_of_endo]). *)
Definition matrix_rep_of_functor {M : MonObject} {R : RigObject}
  (F : Deloop M ⟶ Matr R) : MatrixRep M R :=
  existT (fun n : nat => MonHom M (hom_monoid (Matr R) n))
    (F ttt : nat) (hom_monoid_of_functor (C := Matr R) F).

Lemma matrix_rep_dimension {M : MonObject} {R : RigObject}
  (F : Deloop M ⟶ Matr R) :
  `1 (matrix_rep_of_functor F) = F ttt.
Proof. reflexivity. Qed.

(** ** Right actions, along the opposite-monoid identification *)

Section RightActions.

Context {G : MonObject}.

(*
   本节说明函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition right_action_of_op_functor
  (F : (Deloop G)^op ⟶ Sets) : MSetoidAction (MonObject_op G) :=
  action_of_functor (F ◯ from (Deloop_op G)).

Definition op_functor_of_right_action
  (A : MSetoidAction (MonObject_op G)) : (Deloop G)^op ⟶ Sets :=
  functor_of_action A ◯ to (Deloop_op G).

End RightActions.

(** ** Riehl 1.3.10: each group element acts by an automorphism *)

Section Automorphism.

Context {G : GrpObject}.
Context {C : Category}.

(* The named instantiation of [fobj_iso] at the delooped group's
   isomorphisms: the action of g, as an isomorphism of the underlying
   object. *)
Definition action_automorphism (F : Deloop G ⟶ C) (g : carrier G) :
  F ttt ≅ F ttt :=
  fobj_iso F ttt ttt (Deloop_group_iso G ttt ttt g).

(* Its forward leg is the action of g... *)
Lemma action_automorphism_to (F : Deloop G ⟶ C) (g : carrier G) :
  to (action_automorphism F g) ≈ fmap[F] g.
Proof. reflexivity. Qed.

(* ...and its inverse is the action of the inverse of g. *)
Lemma action_automorphism_from (F : Deloop G ⟶ C) (g : carrier G) :
  from (action_automorphism F g) ≈ fmap[F] (grp_inv g).
Proof. reflexivity. Qed.

End Automorphism.

(** ** Awodey §7.1: the cocycle characterization *)

Section Cocycle.

Context {A : Type} {R : relation A} (P : RelationClasses.PreOrder R).
#[local] Existing Instance P.
Context (M : MonObject).

(*
   本节说明函子、hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record Cocycle := {
  cocycle : ∀ p q : A, R p q → carrier M;
  cocycle_irrel : ∀ p q (h h' : R p q), cocycle p q h ≈ cocycle p q h';
  cocycle_refl : ∀ p,
    cocycle p p (@RelationClasses.PreOrder_Reflexive A R P p) ≈ mon_unit;
  cocycle_trans : ∀ p q r (h : R p q) (k : R q r),
    mon_op (cocycle q r k) (cocycle p q h)
      ≈ cocycle p r
          (@RelationClasses.PreOrder_Transitive A R P p q r h k)
}.

Program Definition functor_of_cocycle (γ : Cocycle) :
  Proset P ⟶ Deloop M := {|
  fobj := fun _ => ttt;
  fmap := fun p q (h : R p q) => cocycle γ p q h
|}.
Next Obligation.
  intros γ p q f g T; exact (cocycle_irrel γ p q f g).
Qed.
Next Obligation. intros γ p; exact (cocycle_refl γ p). Qed.
Next Obligation.
  intros γ x y z g f; symmetry; exact (cocycle_trans γ x y z f g).
Qed.

Program Definition cocycle_of_functor (F : Proset P ⟶ Deloop M) :
  Cocycle := {|
  cocycle := fun p q (h : R p q) => @fmap _ _ F p q h
|}.
Next Obligation.
  intros F p q h h'; exact (@fmap_respects _ _ F p q h h' I).
Qed.
Next Obligation. intros F p; exact (@fmap_id _ _ F p). Qed.
Next Obligation.
  intros F p q r h k; symmetry; exact (@fmap_comp _ _ F p q r k h).
Qed.

Lemma cocycle_round (γ : Cocycle) (p q : A) (h : R p q) :
  cocycle (cocycle_of_functor (functor_of_cocycle γ)) p q h
    ≈ cocycle γ p q h.
Proof. reflexivity. Qed.

(*
   本节说明函子、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma cocycle_functor_round (F : Proset P ⟶ Deloop M) :
  functor_of_cocycle (cocycle_of_functor F) ≈ F.
Proof.
  exists (fun x =>
            match fobj[F] x as u
                  return (@Isomorphism (Deloop M) ttt u) with
            | ttt => iso_id
            end).
  intros p q h; simpl.
  destruct (fobj[F] p), (fobj[F] q); simpl.
  now rewrite mon_op_unit_l, mon_op_unit_r.
Qed.

End Cocycle.

(** ** The worked witness: (ℤ, ≤) into (ℤ, +) by differences *)

(* The additive group of the integers, as a [GrpObject] — Awodey's ℝ
   transposed to ℤ so the instance layer stays axiom-free (the same
   substitution Theory/Algebra/Rig.v makes for [Int_Ring]). *)
Program Definition Int_Plus : MonObject := {|
  mon_setoid := {| carrier := Z
                 ; is_setoid := {| Setoid.equiv := @eq Z |} |};
  mon_unit := 0%Z;
  mon_op := Z.add
|}.
Next Obligation. intros a b c; simpl; now rewrite Z.add_assoc. Qed.
Next Obligation. intros a; simpl; apply Z.add_0_l. Qed.
Next Obligation. intros a; simpl; apply Z.add_0_r. Qed.

Program Definition Int_Plus_Grp : GrpObject := {|
  grp_monoid := Int_Plus;
  grp_inv := Z.opp
|}.
Next Obligation. intros a; simpl; now rewrite Z.add_opp_diag_l. Qed.
Next Obligation. intros a; simpl; now rewrite Z.add_opp_diag_r. Qed.

(* Awodey's cocycle: g_{x,y} = y − x, with the unit condition x − x = 0
   and the composition condition (z − y) + (y − x) = z − x. *)
Program Definition translation_cocycle :
  Cocycle Z.le_preorder Int_Plus := {|
  cocycle := fun x y _ => (y - x)%Z
|}.
Next Obligation. intros p q h h'; reflexivity. Qed.
Next Obligation. intros p; simpl; now rewrite Z.sub_diag. Qed.
Next Obligation. intros p q r h k; simpl; lia. Qed.

Definition translation_functor :
  Proset Z.le_preorder ⟶ Deloop Int_Plus :=
  functor_of_cocycle Z.le_preorder Int_Plus translation_cocycle.

Example five_le_twelve : (5 <= 12)%Z.
Proof. lia. Qed.

Example translation_5_12 :
  @fmap _ _ translation_functor 5%Z 12%Z five_le_twelve = 7%Z
  := eq_refl.
