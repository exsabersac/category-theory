Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Morphisms.CokernelPair.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * The cokernel pair of [Sets] is a cokernel pair *)

(*
   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SetsCokernelPair.

Universes h p.
Context {A B : SetoidObject@{p p}}.
Context (f : A ~{Sets@{p h}}~> B).

(** ** The mediator *)

(* The copairing of two competing maps: on the left copy use q1, on the
   right copy use q2. *)
Definition sets_ck_fun {Q : SetoidObject@{p p}}
           (q1 q2 : B ~{Sets@{p h}}~> Q)
  : carrier (CKSetoid f) → carrier Q :=
  λ s, match s with
       | Datatypes.inl b => q1 b
       | Datatypes.inr b => q2 b
       end.

(* Respectfulness.  Three of the four cases are [proper_morphism] of q1 or
   q2; the two GLUING cases are the whole content, and they are where the
   coequalizing hypothesis is spent: the image witness names a preimage
   [a] with [f a ≈ x], at which [q1] and [q2] agree by hypothesis. *)
Lemma sets_ck_respects {Q : SetoidObject@{p p}}
      (q1 q2 : B ~{Sets@{p h}}~> Q)
      (Hc : q1 ∘[Sets@{p h}] f ≈ q2 ∘[Sets@{p h}] f)
      (s t : carrier (CKSetoid f)) :
  ckrel f s t → sets_ck_fun q1 q2 s ≈ sets_ck_fun q1 q2 t.
Proof.
  destruct s as [xs|xs], t as [xt|xt]; simpl.
  - intro E; now rewrite E.
  - intros [E [a Ha]].
    (* q1 xs ≈ q1 (f a) ≈ q2 (f a) ≈ q2 xs ≈ q2 xt *)
    transitivity (q1 (f a)); [ now rewrite Ha |].
    transitivity (q2 (f a)); [ exact (Hc a) |].
    rewrite Ha; now rewrite E.
  - intros [E [a Ha]].
    transitivity (q2 (f a)); [ now rewrite Ha |].
    transitivity (q1 (f a)); [ symmetry; exact (Hc a) |].
    rewrite Ha; now rewrite E.
  - intro E; now rewrite E.
Qed.

Program Definition sets_ck_med {Q : SetoidObject@{p p}}
        (q1 q2 : B ~{Sets@{p h}}~> Q)
        (Hc : q1 ∘[Sets@{p h}] f ≈ q2 ∘[Sets@{p h}] f)
  : CKSetoid f ~{Sets@{p h}}~> Q :=
  {| morphism := sets_ck_fun q1 q2 |}.
Next Obligation.
  repeat intro; now apply sets_ck_respects.
Qed.

(** ** The universal property *)

(* Both triangles are POINTWISE [reflexivity]: the mediator is defined by
   case analysis on the sum, and each leg lands in exactly one case. *)
Lemma sets_ck_med_left {Q : SetoidObject@{p p}}
      (q1 q2 : B ~{Sets@{p h}}~> Q)
      (Hc : q1 ∘[Sets@{p h}] f ≈ q2 ∘[Sets@{p h}] f) :
  sets_ck_med q1 q2 Hc ∘[Sets@{p h}] ck_left f ≈ q1.
Proof. intro b; reflexivity. Qed.

Lemma sets_ck_med_right {Q : SetoidObject@{p p}}
      (q1 q2 : B ~{Sets@{p h}}~> Q)
      (Hc : q1 ∘[Sets@{p h}] f ≈ q2 ∘[Sets@{p h}] f) :
  sets_ck_med q1 q2 Hc ∘[Sets@{p h}] ck_right f ≈ q2.
Proof. intro b; reflexivity. Qed.

Lemma sets_ck_ump (Q : SetoidObject@{p p})
      (q1 q2 : B ~{Sets@{p h}}~> Q)
      (Hc : q1 ∘[Sets@{p h}] f ≈ q2 ∘[Sets@{p h}] f) :
  ∃! u : CKSetoid f ~{Sets@{p h}}~> Q,
    u ∘[Sets@{p h}] ck_left f ≈ q1 ∧ u ∘[Sets@{p h}] ck_right f ≈ q2.
Proof.
  unshelve refine {| unique_obj := sets_ck_med q1 q2 Hc |}.
  - split; [ apply sets_ck_med_left | apply sets_ck_med_right ].
  - intros v [Hv1 Hv2] s.
    destruct s as [b|b]; simpl.
    + symmetry; exact (Hv1 b).
    + symmetry; exact (Hv2 b).
Qed.

(* Instance/Sets.v's construction IS a cokernel pair.  The commuting
   equation is that file's own [ck_agree], reused rather than reproved. *)
Definition sets_ck_IsCokernelPair
  : IsCokernelPair (C:=Sets@{p h}) f (CKSetoid f) (ck_left f) (ck_right f) :=
  @Build_IsPushoutSquare Sets@{p h} A B B f f
    (CKSetoid f) (ck_left f) (ck_right f) (ck_agree f) sets_ck_ump.

End SetsCokernelPair.

(** ** The two triangles hold on the nose on the underlying functions *)

(* The mediator's value at either injection is the corresponding competing
   map applied to the point — Leibniz, not merely [≈].  What is NOT strict
   is the equality of MORPHISMS (see Test/ProbeCokernelPair.v). *)
Example sets_ck_med_inl@{h p} {A B Q : SetoidObject@{p p}}
        (f : A ~{Sets@{p h}}~> B) (q1 q2 : B ~{Sets@{p h}}~> Q)
        (Hc : q1 ∘[Sets@{p h}] f ≈ q2 ∘[Sets@{p h}] f) (b : carrier B) :
  sets_ck_med f q1 q2 Hc (Datatypes.inl b) = q1 b := eq_refl.

Example sets_ck_med_inr@{h p} {A B Q : SetoidObject@{p p}}
        (f : A ~{Sets@{p h}}~> B) (q1 q2 : B ~{Sets@{p h}}~> Q)
        (Hc : q1 ∘[Sets@{p h}] f ≈ q2 ∘[Sets@{p h}] f) (b : carrier B) :
  sets_ck_med f q1 q2 Hc (Datatypes.inr b) = q2 b := eq_refl.

(** ** Non-vacuity, both ways *)

(* Instance/Sets.v's own witness pair between the singleton and the
   two-element setoid is used, so no new object is introduced. *)

(** *** The epic side: [collapse] is surjective, so its legs agree *)

Lemma sets_collapse_surjective :
  ∀ u : carrier unit_setoid_object, ∃ b, collapse b ≈ u.
Proof. intro u; exists true; destruct u; reflexivity. Qed.

Definition sets_collapse_epic : Epic collapse :=
  surjective_implies_epic collapse sets_collapse_surjective.

(* Its cokernel pair is trivial: the two legs of [CKSetoid collapse]
   coincide.  Obtained through the general theorem, not by computation. *)
Definition sets_collapse_ckp_trivial :
  ck_left collapse ≈ ck_right collapse :=
  fst (epic_iff_cokernel_pair_trivial (C:=Sets) collapse
         (is_pushout_square_pushout (sets_ck_IsCokernelPair collapse)))
      sets_collapse_epic.

(* And the identity square on it is a pushout. *)
Definition sets_collapse_pushout_square :
  IsPushoutSquare (C:=Sets) collapse collapse unit_setoid_object id id :=
  fst (epic_iff_pushout_square collapse) sets_collapse_epic.

(** *** The non-epic side: [pick_true] misses [false] *)

(* The two legs of [CKSetoid pick_true] are DISTINCT, proved by hand: at
   [false] the gluing relation would supply a preimage of [false] under
   [pick_true], i.e. a proof that [true = false]. *)
Lemma sets_pick_true_ckp_nontrivial :
  ck_left pick_true ≈ ck_right pick_true → False.
Proof.
  intro E.
  (* [E false] inhabits [ckrel pick_true (inl false) (inr false)], whose
     second component is the image witness. *)
  destruct (E false) as [_ [u Hu]].
  destruct u.
  exact (Bool.diff_true_false Hu).
Qed.

(* Hence the identity square on [pick_true] is NOT a pushout: were it one,
   [pick_true] would be epic and the legs would have to agree. *)
Lemma sets_pick_true_not_pushout_square :
  IsPushoutSquare (C:=Sets) pick_true pick_true bool_setoid_object id id
  → False.
Proof.
  intro H.
  apply sets_pick_true_ckp_nontrivial.
  exact (fst (epic_iff_cokernel_pair_trivial (C:=Sets) pick_true
                (is_pushout_square_pushout
                   (sets_ck_IsCokernelPair pick_true)))
             (snd (epic_iff_pushout_square pick_true) H)).
Qed.

(* Cross-check: Instance/Sets.v's [pick_true_not_epic] re-derived through
   the general characterization, by a route sharing no proof text with the
   original (that one probes with [id] against [pick_true ∘ collapse];
   this one goes through the cokernel pair). *)
Lemma sets_pick_true_not_epic_via_ckp : Epic pick_true → False.
Proof.
  intro E.
  apply sets_pick_true_ckp_nontrivial.
  exact (fst (epic_iff_cokernel_pair_trivial (C:=Sets) pick_true
                (is_pushout_square_pushout
                   (sets_ck_IsCokernelPair pick_true))) E).
Qed.
