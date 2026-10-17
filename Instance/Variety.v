Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Comp.

Generalizable All Variables.

(** * The category of algebras of a variety *)

(*
 nLab:      https://ncatlab.org/nlab/show/algebraic+theory
 Wikipedia: https://en.wikipedia.org/wiki/Variety_(universal_algebra)

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Instance/Comp.v's record fields [carrier], [eq] and [map] would shadow
   the library's if this module were imported, so it is aliased and
   qualified throughout — the same decision, for the same reason, as
   Instance/Roster.v. *)
Module UA := Category.Instance.Comp.UniversalAlgebra.

Section Variety.

Context (S : UA.OpSignature).
Context (E : UA.EqSignature S).

(** ** Satisfaction, and the full subcategory it cuts out *)

(* [Subcategory]'s [sobj] lands in [Type], so satisfaction is stated as a
   [Type]-valued ∀ whose body is a Leibniz equation between two elements of
   the carrier.  It is DEFINITIONALLY the [equations] field of
   Instance/Comp.v, which is what makes the two presentations
   reflexivity-inverse below.

   Every coercion is written out.  Instance/Comp.v declares [eq :> Type]
   and [carrier :> Type] inside [Module UniversalAlgebra], and a module
   ALIAS does not activate coercions — only an [Import] would, which is
   the thing Instance/Roster.v warns against because [eq], [carrier]
   and [map] would shadow the library's.  So [UA.eq S E] and
   [UA.carrier A] appear in full below wherever the coercion would
   otherwise fire. *)

Definition satisfies (A : UA.OpAlgebra S) : Type :=
  ∀ (e : UA.eq S E) (args : UA.eq_arity e → UA.carrier A),
    UA.lhs e args = UA.rhs e args.

Definition Variety_sub : Subcategory (@UA.Algs S) :=
  @Build_Subcategory (@UA.Algs S)
    satisfies
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition Variety : Category := Sub (@UA.Algs S) Variety_sub.

(* Full: every homomorphism between algebras that satisfy the laws is a
   morphism of the variety. *)
Definition Variety_Full : Full (@UA.Algs S) Variety_sub :=
  fun _ _ _ _ _ => I.

Definition Variety_Incl : Variety ⟶ @UA.Algs S := Incl (@UA.Algs S) Variety_sub.

Definition Variety_Incl_Faithful : Functor.Faithful Variety_Incl :=
  Incl_Faithful (@UA.Algs S) Variety_sub.

(* The inclusion is FULL as a functor, not merely full as a subcategory:
   Construction/Subcategory.v already turns the one into the other, and
   an audit pointed out that this costs one line. *)
Definition Variety_Incl_Full : Functor.Full Variety_Incl :=
  Full_Implies_Full_Functor (@UA.Algs S) Variety_sub Variety_Full.

(** ** The record presentation, and its round trips *)

Definition Variety_pack (A : UA.Algebra S E) : Variety :=
  (UA.alg S E A; UA.equations S E A).

Definition Variety_unpack (x : Variety) : UA.Algebra S E :=
  {| UA.alg := `1 x ; UA.equations := `2 x |}.

(* Propositional [=] on the packed OBJECT data — the sanctioned case; no
   morphism equality is asserted. *)

Lemma Variety_unpack_pack (A : UA.Algebra S E) :
  Variety_unpack (Variety_pack A) = A.
Proof. destruct A; reflexivity. Qed.

Lemma Variety_pack_unpack (x : Variety) :
  Variety_pack (Variety_unpack x) = x.
Proof. destruct x; reflexivity. Qed.

(** ** The forgetful functor to Sets

    Awodey's §9.8 asks for the category AND its forgetful functor.  The
    carrier is a bare type, so it lands on the DISCRETE setoid
    (Lib/Setoid.v's [eq_Setoid]); the functor is faithful, which is the
    concreteness the free-algebra theorem consumes. *)

Program Definition Variety_Forget : Variety ⟶ Sets := {|
  fobj := fun A => {| carrier   := UA.carrier (`1 A)
                    ; is_setoid := eq_Setoid (UA.carrier (`1 A)) |};
  fmap := fun _ _ f => {| morphism := UA.map (`1 f) |}
|}.

Lemma Variety_Forget_Faithful : Functor.Faithful Variety_Forget.
Proof. construct; simpl in *; auto. Qed.

End Variety.

(* The signature is recoverable from the equation signature at every use
   site, so it is implicit throughout — [Variety E], not [Variety S E].
   [Arguments] here rather than inside the section, because a section's
   [Context] binders are explicit on the constants it closes over. *)
Arguments satisfies {_} _ _.
Arguments Variety_sub {_} _.
Arguments Variety {_} _.
Arguments Variety_Full {_} _.
Arguments Variety_Incl {_} _.
Arguments Variety_Incl_Faithful {_} _.
Arguments Variety_pack {_ _} _.
Arguments Variety_unpack {_ _} _.
Arguments Variety_unpack_pack {_ _} _.
Arguments Variety_pack_unpack {_ _} _.
Arguments Variety_Forget {_} _.
Arguments Variety_Forget_Faithful {_} _.

(** ** The group variety

    The instantiation Mac Lane's §V.6 and the issue ask for, under a name
    that does NOT collide with Instance/Grp.v's [Grp] — there is exactly
    one [Grp] in this tree and it is that one.

    THIS CONSTANT CARRIES [functional_extensionality_dep], for the reason
    given in the header: it mentions [GroupEq], which is [Defined] using
    the axiom.  It is not gated; docs/AXIOMS.md records it. *)

Definition GroupVariety : Category := Variety UA.GroupEq.

(* ℤ/2 under exclusive or, the witness Instance/Comp.v already builds,
   as an OBJECT of the category rather than an inhabitant of a type. *)
Definition GroupVariety_Bool : GroupVariety := Variety_pack UA.Bool.

(** ** Where the axiom is not needed, exhibited twice

    First shape: REINDEXING bundles.  One binary operation, one law
    (commutativity), whose two naturality fields are [op_commute] itself
    at [args] and at [args ∘ comm_swap] — so no bundle is rebuilt and no
    extensionality is needed.  [Print Assumptions] on every constant in
    this block says "Closed under the global context", and all are
    gated. *)

Inductive magma_op : Set := magma_mul.

Definition MagmaOp : UA.OpSignature :=
  {| UA.operation := magma_op ; UA.arity := fun _ => UA.binary |}.

Inductive comm_eq : Set := comm_law.

Definition comm_swap (i : UA.binary) : UA.binary :=
  match i with UA.Fst => UA.Snd | UA.Snd => UA.Fst end.

Definition CommEq : UA.EqSignature MagmaOp.
Proof.
  refine {| UA.eq       := comm_eq
          ; UA.eq_arity := fun _ => UA.binary
          ; UA.lhs      := fun (A : UA.OpAlgebra MagmaOp) _ args =>
                             UA.op A magma_mul args
          ; UA.rhs      := fun (A : UA.OpAlgebra MagmaOp) _ args =>
                             UA.op A magma_mul (fun i => args (comm_swap i))
         |}.
  - intros A B f [] args; exact (UA.op_commute A B f magma_mul args).
  - intros A B f [] args;
      exact (UA.op_commute A B f magma_mul (fun i => args (comm_swap i))).
Defined.

Definition CommMagmaVariety : Category := Variety CommEq.

(** ** Second shape: CONSTANT bundles, at DEPTH 2, over [GroupOp] itself

    This is the sharper exhibit, and it is what refutes the depth
    diagnosis.  [inv (inv x) = x] is a depth-2 equation over the SAME
    signature whose group laws force the axiom, and it is axiom-free:
    both of its bundles are CONSTANT ([fun _ => args Only] and
    [fun _ => inv' (args Only)]), so the outer naturality step is
    [f_equal] against the constant-bundle former and the inner one is
    [op_commute].  Nothing about the depth of the term enters.

    Note what this does and does not say.  It does NOT give an axiom-free
    group variety: [InvInvVariety] imposes only this one law, and the
    group axioms proper each build a [mul] bundle of the mixed shape the
    header describes. *)

Inductive invinv_eq : Set := invinv.

Definition InvInvEq : UA.EqSignature UA.GroupOp.
Proof.
  refine {| UA.eq       := invinv_eq
          ; UA.eq_arity := fun _ => UA.unary
          ; UA.lhs      := fun (A : UA.OpAlgebra UA.GroupOp) _ args =>
                             UA.inv' (UA.inv' (args UA.Only))
          ; UA.rhs      := fun (A : UA.OpAlgebra UA.GroupOp) _ args =>
                             args UA.Only
         |}.
  - intros A B f [] args.
    unfold UA.inv'.
    rewrite UA.op_commute.
    apply (f_equal (fun z => UA.op B UA.inv (fun _ : UA.unary => z))).
    exact (UA.op_commute A B f UA.inv (fun _ => args UA.Only)).
  - intros A B f [] args; reflexivity.
Defined.

Definition InvInvVariety : Category := Variety InvInvEq.

(** ** The connection to Lawvere theories, stated and not proved

    Work item 3 of the issue asks that the connection to
    Theory/Lawvere/Model.v be RECORDED.  Here it is, as prose, because the
    proof is a separate development and is listed as not delivered.

    For a presentation ⟨S,E⟩ the associated Lawvere theory has [nat] for
    objects, the [E]-congruence classes of n-tuples of derived operators
    for morphisms m ~> n, and finite products given by addition; its
    [Models] in [Sets] (Theory/Lawvere/Model.v) ought to be equivalent
    to [Variety E].  Two things block the equivalence here and neither is
    incidental.  Building the theory needs the clone as a CATEGORY, with
    the congruence as its hom-setoid and the two propositional object
    equalities [law_zero_terminal] and [law_plus_product]
    (Theory/Lawvere.v).  And the comparison then meets the same wall as
    Instance/Variety/GroupComparison.v: [Models T Sets] has SETOID carriers where
    [Variety]'s are Leibniz types, so essential surjectivity needs
    quotients.  Instance/Variety/Clone.v supplies the derived operators and
    their substitution calculus, which is the first half of the first
    obstruction; the rest is filed as a follow-on. *)
