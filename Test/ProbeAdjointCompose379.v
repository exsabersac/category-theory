Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.Compose.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Equivalence.Bundled.
Require Import Category.Theory.Equivalence.Strict.
Require Import Category.Instance.One.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Theory.Equivalence.Adjoint.Compose.

Generalizable All Variables.

(*
   本文件为测试：ProbeAdjointCompose379。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Instrument check: a name that exists nowhere must be rejected. *)
Fail Check probe379_no_such_constant_anywhere.

(** ** Guards: every constant a negative names, named outside a [Fail] *)

Check @AdjointEquivalence_Compose.
Check @AdjointEquivalence_Compose_via_equivalence.
Check @AdjointEquivalence_Compose_unit.
Check @AdjointEquivalence_Compose_counit.
Check @AdjointEquivalence_Compose_unit_transpose.
Check @AdjointEquivalence_Id.
Check @Id.
Check @adjoint_equivalence_compose_adj.
Check @assoc_left.
Check @assoc_right.
Check @indiscrete_square.
Check @indiscrete_swap.
Check @IsIso_id.
Check @IsIso_along.
Check @IsIso_comp.
Check @IsIso_fmap.
Check @adj_equivalence.
Check @Adjunction_Compose.
Check @unit.
Check @counit.
Check @AdjointEquivalence.
Check @Adjunction.
Check @Equivalence_to_AdjointEquivalence.
Check @EquivalenceOfCategories_Compose.
Check @AdjointEquivalence_to_Equivalence.
Check @AdjointEquivalence_swap.
Check IndT.
Check (Indiscrete bool).
Check @Erase.

(** ** Conversion negatives: the two routes are different *)

Section Routes.

Context {C D E : Category}.
Context {F : C ⟶ D} {U : D ⟶ C}.
Context {F' : D ⟶ E} {U' : E ⟶ D}.
Context (A : AdjointEquivalence F U).
Context (B : AdjointEquivalence F' U').

(* Positive control: both routes inhabit ONE type, so the negatives
   below are conversion questions and not typing ones. *)
Check (AdjointEquivalence_Compose A B
       : AdjointEquivalence (F' ◯ F) (U ◯ U')).
Check (AdjointEquivalence_Compose_via_equivalence A B
       : AdjointEquivalence (F' ◯ F) (U ◯ U')).

(* Negative 1 (CONVERSION): the refinement route is not the direct
   composite, on the whole record. *)
Fail Example probe379_neg1 :
  AdjointEquivalence_Compose_via_equivalence A B
    = AdjointEquivalence_Compose A B := eq_refl.

(* Negative 2 (CONVERSION): nor on the underlying adjunction. *)
Fail Example probe379_neg2 :
  @adj_equivalence _ _ _ _ (AdjointEquivalence_Compose_via_equivalence A B)
    = @adj_equivalence _ _ _ _ (AdjointEquivalence_Compose A B) := eq_refl.

(* Negative 3 (CONVERSION): nor on the unit components.  The direct
   route's unit DOES reduce -- that is the [eq_refl] control below,
   which is [AdjointEquivalence_Compose_unit_transpose] -- so the
   obstruction is on the refinement side. *)
Fail Example probe379_neg3 (x : C) :
  @unit _ _ _ _
    (@adj_equivalence _ _ _ _ (AdjointEquivalence_Compose_via_equivalence A B))
    x
  = @unit _ _ _ _
      (@adj_equivalence _ _ _ _ (AdjointEquivalence_Compose A B)) x := eq_refl.

Example probe379_ctrl_direct_reduces (x : C) :
  @unit _ _ _ _ (@adj_equivalence _ _ _ _ (AdjointEquivalence_Compose A B)) x
    = to (@adj _ _ _ _ (@adj_equivalence _ _ _ _ A) x (U' (F' (F x))))
         (@unit _ _ _ _ (@adj_equivalence _ _ _ _ B) (F x)) := eq_refl.

(* Negative 4 (CONVERSION): Mac Lane's whiskering formula for the unit
   is [~] and not [eq_refl].  The [~] form is the target's
   [AdjointEquivalence_Compose_unit], reproduced as the control. *)
Fail Example probe379_neg4 (x : C) :
  @unit _ _ _ _ (@adj_equivalence _ _ _ _ (AdjointEquivalence_Compose A B)) x
    = fmap[U] (@unit _ _ _ _ (@adj_equivalence _ _ _ _ B) (F x))
        ∘ @unit _ _ _ _ (@adj_equivalence _ _ _ _ A) x := eq_refl.

Example probe379_ctrl_unit_approx (x : C) :
  @unit _ _ _ _ (@adj_equivalence _ _ _ _ (AdjointEquivalence_Compose A B)) x
    ≈ fmap[U] (@unit _ _ _ _ (@adj_equivalence _ _ _ _ B) (F x))
        ∘ @unit _ _ _ _ (@adj_equivalence _ _ _ _ A) x :=
  AdjointEquivalence_Compose_unit A B x.

(* Negative 5 (CONVERSION): the same for the counit. *)
Fail Example probe379_neg5 (y : E) :
  @counit _ _ _ _ (@adj_equivalence _ _ _ _ (AdjointEquivalence_Compose A B)) y
    = @counit _ _ _ _ (@adj_equivalence _ _ _ _ B) y
        ∘ fmap[F'] (@counit _ _ _ _ (@adj_equivalence _ _ _ _ A) (U' y))
  := eq_refl.

Example probe379_ctrl_counit_approx (y : E) :
  @counit _ _ _ _ (@adj_equivalence _ _ _ _ (AdjointEquivalence_Compose A B)) y
    ≈ @counit _ _ _ _ (@adj_equivalence _ _ _ _ B) y
        ∘ fmap[F'] (@counit _ _ _ _ (@adj_equivalence _ _ _ _ A) (U' y)) :=
  AdjointEquivalence_Compose_counit A B y.

End Routes.

(** ** Typing negatives: the groupoid laws are not statable at the class *)

Section Laws.

Context {C1 C2 C3 C4 : Category}.
Context {F1 : C1 ⟶ C2} {U1 : C2 ⟶ C1}.
Context {F2 : C2 ⟶ C3} {U2 : C3 ⟶ C2}.
Context {F3 : C3 ⟶ C4} {U3 : C4 ⟶ C3}.
Context (A : AdjointEquivalence F1 U1).
Context (B : AdjointEquivalence F2 U2).
Context (G : AdjointEquivalence F3 U3).

(* Positive controls: each bracketing is formable, at ITS OWN type. *)
Check (assoc_left A B G
       : AdjointEquivalence (F3 ◯ (F2 ◯ F1)) ((U1 ◯ U2) ◯ U3)).
Check (assoc_right A B G
       : AdjointEquivalence ((F3 ◯ F2) ◯ F1) (U1 ◯ (U2 ◯ U3))).

(* Negative 6 (TYPING): the two bracketings do not inhabit a common
   type, so associativity is not statable at the level of the class.
   What IS statable, and holds by conversion, is the comparison of the
   units and counits -- the control below is the target's
   [AdjointEquivalence_Compose_assoc_unit]. *)
Fail Check (assoc_left A B G = assoc_right A B G).

Example probe379_ctrl_assoc_unit (x : C1) :
  @unit _ _ _ _ (@adj_equivalence _ _ _ _ (assoc_left A B G)) x
    = @unit _ _ _ _ (@adj_equivalence _ _ _ _ (assoc_right A B G)) x :=
  AdjointEquivalence_Compose_assoc_unit A B G x.

(* Negative 7 (TYPING): the same for the left identity law. *)
Fail Check (AdjointEquivalence_Compose (@AdjointEquivalence_Id C1) A = A).

Example probe379_ctrl_id_left_unit (x : C1) :
  @unit _ _ _ _
    (@adj_equivalence _ _ _ _
       (AdjointEquivalence_Compose (@AdjointEquivalence_Id C1) A)) x
    = @unit _ _ _ _ (@adj_equivalence _ _ _ _ A) x :=
  AdjointEquivalence_Compose_id_left_unit A x.

End Laws.

(* Negative 8 (TYPING): the witness is likewise not of identity type --
   its two functors move an object, so it does not even have the TYPE of
   an identity adjoint equivalence.  Control: the object is moved. *)
Example probe379_ctrl_witness_moves :
  (IndT ◯ Erase (Indiscrete bool)) false = true := eq_refl.

Fail Check (indiscrete_square = @AdjointEquivalence_Id (Indiscrete bool)).

(** ** Formability negatives: where the universe identifications come
       from *)

Section HomIsProof.

Universes co ch cp.
Constraint ch < cp.
Context (Cu : Category@{co ch cp}).
Context (G H : Cu ⟶ Cu).
Context (x y : Cu).

(* Controls, all accepted at these very levels: the category's homs and
   identity, a functor from the category to itself (so [Functor] is NOT
   a donor), the predicate [IsIsomorphism], and the target's own four
   [IsIso_*] constants, whose explicit universe binders keep hom and
   proof apart. *)
Check (x ~{Cu}~> y).
Check (@id Cu x).
Check (Cu ⟶ Cu).
Check (@IsIsomorphism Cu x y).
Check (@IsIso_id Cu x).
Check (@IsIso_along Cu x y).
Check (@IsIso_comp Cu x y).
Check (@IsIso_fmap Cu Cu G x y).

(* Negative 9 (FORMABILITY): the IDENTITY FUNCTOR alone identifies hom
   with proof.
   This is worth isolating, because it means a probe that writes
   [Id[Cu]] into an [Adjunction] is testing [Id] and not [Adjunction].
   The control immediately above -- an arbitrary endofunctor of the same
   category, accepted -- is what separates the two. *)
Fail Check (@Id Cu).

(* Negative 10 (FORMABILITY): [Adjunction] identifies hom with proof
   INDEPENDENTLY
   of that, probed here at two arbitrary endofunctors so that no [Id]
   occurs in the command. *)
Fail Check (@Adjunction Cu Cu G H).

(* Negative 11 (FORMABILITY): so does [AdjointEquivalence] -- but it
   CANNOT be
   tested apart from [Adjunction], its first field being [F -| U], so
   this is a second donor and NOT an independent cause. *)
Fail Check (@AdjointEquivalence Cu Cu G H).

(* Negative 12 (FORMABILITY): the target's own identity adjoint
   equivalence inherits the identification.  It has at least the two
   sufficient donors above -- [Id] occurs in its statement and
   [Adjunction] in its field -- and this negative isolates neither. *)
Fail Check (@AdjointEquivalence_Id Cu).

End HomIsProof.

Section HomLevelsApart.

Universes ao ah bo bh.
Constraint ah < bh.
Context (Au : Category@{ao ah ah}).
Context (Bu : Category@{bo bh bh}).

(* Control: a functor in one direction is formable. *)
Check (Au ⟶ Bu).

(* Negative 13 (FORMABILITY): the mere presence of a functor in the
   OTHER direction
   forces the two hom universes to agree, before any adjunction is
   formed.  This is where the composite's [u0 = u2 = u4] comes from. *)
Fail Check (Bu ⟶ Au).

End HomLevelsApart.
