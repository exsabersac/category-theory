Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Displayed.
Require Import Category.Theory.Equivalence.
Require Import Category.Construction.Indexed.
Require Import Category.Construction.Grothendieck.

Generalizable All Variables.

(** * Fibre categories, and the fibres of the Grothendieck construction *)

(*
   nLab:      https://ncatlab.org/nlab/show/displayed+category
   nLab:      https://ncatlab.org/nlab/show/Grothendieck+construction
   Wikipedia: https://en.wikipedia.org/wiki/Fibred_category

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(* Conjugating by the identity isomorphism does nothing: the generic
   stripping step for equivalence cells whose isomorphism family is
   [iso_id] pointwise. *)
Lemma conjugate_iso_id {C : Category} {a b : C} (f : a ~> b) :
  from (@iso_id C b) ∘ f ∘ to (@iso_id C a) ≈ f.
Proof.
  simpl.
  now rewrite id_left, id_right.
Qed.

(** ** The fibre category of a displayed category *)

Section FiberCategory.

Context {C : Category}.
Context (D : Displayed C).
Context (x : C).

(*
   本节说明 Fiber 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Fiber_comp_assoc {da db dc dd : dobj x}
  (e1 e2 e3 e4 : @id C x ∘ @id C x ≈ @id C x)
  (ff : dhom dc dd id) (gg : dhom db dc id) (hh : dhom da db id) :
  dtransport e1 (dcomp ff (dtransport e2 (dcomp gg hh)))
    ≈ dtransport e3 (dcomp (dtransport e4 (dcomp ff gg)) hh).
Proof.
  rewrite (dtransport_comp_r e2
             (compose_respects id id (Equivalence_Reflexive id) _ _ e2)
             ff (dcomp gg hh)).
  rewrite (dtransport_comp_l e4
             (compose_respects _ _ e4 id id (Equivalence_Reflexive id))
             (dcomp ff gg) hh).
  rewrite !dtransport_trans.
  rewrite dcomp_assoc.
  rewrite dtransport_trans.
  apply dtransport_proof_irrel.
Qed.

(* The fibre of [D] over [x]: objects displayed over [x], morphisms
   displayed over [id[x]], composition recentred over [id] along the
   base unit law. *)
Program Definition Fiber : Category := {|
  obj := dobj x;
  hom := fun dx dy => dhom dx dy id;
  homset := fun dx dy => dhomset dx dy id;
  id := fun dx => did dx;
  compose := fun dx dy dz ff gg => dtransport (id_left id) (dcomp ff gg)
|}.
Next Obligation.
  (* composition respects ≈ in both arguments *)
  intros dx dy dz ff ff' Hf gg gg' Hg.
  now rewrite Hf, Hg.
Qed.
Next Obligation.
  (* left identity, over the base unit law *)
  intros dx dy ff.
  apply dtransport_did_left.
Qed.
Next Obligation.
  (* right identity, over the base unit law *)
  intros dx dy ff.
  apply dtransport_did_right.
Qed.
Next Obligation.
  (* associativity *)
  intros da db dc dd ff gg hh.
  apply Fiber_comp_assoc.
Qed.
Next Obligation.
  (* associativity, dual orientation *)
  intros da db dc dd ff gg hh.
  symmetry; apply Fiber_comp_assoc.
Qed.

End FiberCategory.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section GrothendieckFiber.

Context {B : Category}.
Context (A : IndexedCat B).
Context (x : B).

(* The from-side of the unit coherence [idx_unit_left] at [f := id]: the
   inverses of the mediator and compositor isos fuse into the inverse of
   the unit iso at the reindexed object. *)
Lemma Grothendieck_fiber_unit_left_inv (a : idx_fib A x) :
  from (idx_comp A id id a) ∘ from (idx_resp A (id_left (@id B x)) a)
    ≈ from (idx_id A (idx_map A (@id B x) a)).
Proof.
  exact (snd (to_equiv_implies_iso_equiv
    (iso_compose (idx_resp A (id_left (@id B x)) a) (idx_comp A id id a))
    (idx_id A (idx_map A (@id B x) a))
    (idx_unit_left A id a))).
Qed.

(* The from-side of [idx_unit_right] at [f := id], fused against the
   compositor/mediator tail of the Grothendieck fibre's composition: the
   whole composite cancels. *)
Lemma Grothendieck_fiber_unit_right_inv (a : idx_fib A x) :
  fmap[idx_map A (@id B x)] (to (idx_id A a))
      ∘ from (idx_comp A id id a)
      ∘ from (idx_resp A (id_left (@id B x)) a)
    ≈ id.
Proof.
  rewrite <- (idx_unit_right A id a).
  rewrite <- (comp_assoc (to (idx_resp A (id_right (@id B x)) a))).
  (* the rewrites below are pinned: the base identity [id ∘ id] also occurs
     inside the (dependent) implicit arguments of [idx_resp], where the
     generalized rewrite may not abstract *)
  rewrite (iso_to_from (idx_comp A (@id B x) (@id B x) a)).
  rewrite (id_right (to (idx_resp A (id_right (@id B x)) a))).
  rewrite (idx_resp_from_irrel A (id_left (@id B x)) (id_right (@id B x)) a).
  apply iso_to_from.
Qed.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Fiber_Grothendieck_To :
  Fiber (Grothendieck_Displayed A) x ⟶ idx_fib A x.
Proof.
  unshelve refine
    (Build_Functor (Fiber (Grothendieck_Displayed A) x) (idx_fib A x)
       (fun a => a)
       (fun a b ff =>
          (ff : idx_map A (@id B x) a ~{ idx_fib A x }~> b)
            ∘ from (idx_id A a))
       _ _ _).
  - (* fmap respects ≈ *)
    intros a b ff gg Hfg; simpl in *.
    now rewrite Hfg.
  - (* identities: the two sides of the unit iso cancel *)
    intros a; simpl.
    apply iso_to_from.
  - (* composition: the compositor/mediator tail is the inverted left unit
       law, and the unit iso is natural *)
    intros a b c ff gg; simpl.
    rewrite <- !comp_assoc.
    apply compose_respects; [ reflexivity |].
    rewrite (comp_assoc (from (idx_comp A id id a))).
    rewrite Grothendieck_fiber_unit_left_inv.
    rewrite !comp_assoc.
    now rewrite (idx_id_natural_from A gg).
Defined.

(* From the indexed fibre to the Grothendieck fibre: the identity on
   objects; on homs, precompose with the unit iso. *)
Definition Fiber_Grothendieck_From :
  idx_fib A x ⟶ Fiber (Grothendieck_Displayed A) x.
Proof.
  unshelve refine
    (Build_Functor (idx_fib A x) (Fiber (Grothendieck_Displayed A) x)
       (fun a => a)
       (fun a b k => (k ∘ to (idx_id A a)
                      : a ~{ Fiber (Grothendieck_Displayed A) x }~> b))
       _ _ _).
  - (* fmap respects ≈ *)
    intros a b k l Hkl; simpl in *.
    now rewrite Hkl.
  - (* identities *)
    intros a; simpl.
    apply id_left.
  - (* composition: the inverted right unit law cancels the tail, then the
       unit iso is natural *)
    intros a b c k l; simpl.
    symmetry.
    rewrite fmap_comp.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (fmap[idx_map A (@id B x)] (to (idx_id A a)))).
    rewrite Grothendieck_fiber_unit_right_inv.
    rewrite id_right.
    now rewrite <- (idx_id_natural A l).
Defined.

(* The counit cell: To ◯ From ≈ Id on the indexed fibre, with identity
   components. *)
Definition Grothendieck_fiber_counit :
  Fiber_Grothendieck_To ◯ Fiber_Grothendieck_From ≈ Id[idx_fib A x].
Proof.
  exists (fun a => iso_id).
  intros a b k; cbv beta.
  rewrite conjugate_iso_id; simpl.
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  apply id_right.
Defined.

(* The unit cell: Id on the Grothendieck fibre ≈ From ◯ To, with
   identity components. *)
Definition Grothendieck_fiber_unit :
  Id[Fiber (Grothendieck_Displayed A) x]
    ≈ Fiber_Grothendieck_From ◯ Fiber_Grothendieck_To.
Proof.
  exists (fun a => iso_id).
  intros a b ff; cbv beta.
  rewrite conjugate_iso_id; simpl.
  rewrite <- comp_assoc.
  rewrite iso_from_to.
  now rewrite id_right.
Defined.

(* The committed half of the round trip, packaged: the fibre of the
   Grothendieck construction of [A] at [x] is equivalent to the fibre
   [A] indexes at [x]. *)
Definition fiber_grothendieck_equiv :
  EquivalenceOfCategories Fiber_Grothendieck_To :=
  @Build_EquivalenceOfCategories
    (Fiber (Grothendieck_Displayed A) x) (idx_fib A x)
    Fiber_Grothendieck_To Fiber_Grothendieck_From
    Grothendieck_fiber_counit Grothendieck_fiber_unit.

End GrothendieckFiber.
