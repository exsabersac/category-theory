Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Adjoints.

Generalizable All Variables.

(*
   本文件为测试：Issue213。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Take the wide search away.  [intuition]'s default solver is
   [first [solve [auto] | tryif solve [auto with *] then <warn> else idtac]];
   stubbing it out with [idtac] leaves [intuition] its structural work (it
   still splits the pair) while denying it the [auto with *] leaf -- exactly
   the reach that the released Rocq versions still had and Rocq master lost. *)
Ltac Tauto.intuition_solver ::= idtac.

(* [equivalence]'s body without the deterministic pass and with no wide
   fallback: what the tactic amounts to once neither the explicit search nor
   [intuition]'s implicit one reaches [solve_crelation]. *)
Ltac equivalence_old :=
  constructor; repeat intro; simpl; try cat; intuition.

Section Issue213.

Context {C : Category}.
Context {D : Category}.

(* Verbatim the relation of [adj_morphism_setoid]. *)
Definition issue_213_rel (f g : @adj_morphism C D) : Type :=
  (free_functor f ≅[Fun] free_functor g) *
  (forgetful_functor f ≅[Fun] forgetful_functor g).

(* Confirmation of the reported failure mode.  Denied the wide search, the old
   tactic body leaves the two symmetry components open, so the old script's
   bullets no longer line up with the goals they were written for and no amount
   of [transitivity ...; assumption] closes them.  This is the state Rocq
   master reached; it is recorded here so that a future "simplification" back
   to the old script cannot pass unnoticed. *)
Example issue_213_old_script_needs_the_wide_search : Equivalence issue_213_rel.
Proof.
  unfold issue_213_rel.
  (* The negative half: the old script cannot close the goal here. *)
  assert_fails
    (equivalence_old;
     solve [ transitivity (free_functor y); assumption
           | transitivity (forgetful_functor y); assumption ]).
  (* The positive half, so this stays a live [Qed] rather than an aborted
     sketch: the relation is an equivalence, closed the deterministic way. *)
  constructor.
  - intros f.
    split; reflexivity.
  - intros f g [Hfree Hforget].
    split; symmetry; assumption.
  - intros f g h [Hfree Hforget] [Hfree' Hforget'].
    split; etransitivity; eassumption.
Qed.

(* The mechanism, isolated to the one law that went missing: denied the wide
   search, the old tactic body cannot close symmetry -- though symmetry does
   hold, and closes at once by hand. *)
Example issue_213_symmetry_is_the_missing_law : Symmetric issue_213_rel.
Proof.
  unfold issue_213_rel.
  assert_fails (solve [ repeat intro; simpl; try cat; intuition ]).
  intros f g [Hfree Hforget].
  split; symmetry; assumption.
Qed.

(* The repaired script, run in that same hostile environment: the three laws
   come from [iso_equivalence] componentwise, so no hint search of any width
   is consulted. *)
Example issue_213_equivalence_unaided : Equivalence issue_213_rel.
Proof.
  unfold issue_213_rel.
  constructor.
  - intros f.
    split; reflexivity.
  - intros f g [Hfree Hforget].
    split; symmetry; assumption.
  - intros f g h [Hfree Hforget] [Hfree' Hforget'].
    split; etransitivity; eassumption.
Qed.

(* And the library's own [equivalence] -- the real tactic, not a copy of it --
   still takes the very script that broke in Rocq CI.  This is a guard on
   [Lib/Tactics.v] and not merely on a transcript of it: [intuition]'s
   [auto with *] leaf is stubbed out above, and the tactic's remaining
   fallback is [auto with category_laws], a database that carries no hint
   closing [_ ≅ _].  So it is the tactic's own deterministic reflexivity /
   symmetry pass that discharges those two laws here, and deleting that pass
   fails this example. *)
Example issue_213_tactic_is_deterministic : Equivalence issue_213_rel.
Proof.
  unfold issue_213_rel.
  equivalence.
  - transitivity (free_functor y); assumption.
  - transitivity (forgetful_functor y); assumption.
Qed.

(* Finally, the instance the library actually exports really is an equivalence
   on [adj_morphism], and [≈] resolves to it. *)
Example issue_213_setoid_reflexive (f : @adj_morphism C D) : f ≈ f.
Proof. reflexivity. Qed.

Example issue_213_setoid_symmetric (f g : @adj_morphism C D) : f ≈ g → g ≈ f.
Proof. intros; symmetry; assumption. Qed.

Example issue_213_setoid_transitive (f g h : @adj_morphism C D) :
  f ≈ g → g ≈ h → f ≈ h.
Proof. intros; etransitivity; eassumption. Qed.

End Issue213.
