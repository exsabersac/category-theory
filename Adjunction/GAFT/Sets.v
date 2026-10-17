Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Adjunction.GAFT.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Adjoints.

Generalizable All Variables.

(** * The General Adjoint Functor Theorem, run at [Sets] *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functor_theorem

   本文件给出集合相关实例或构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The three premises *)

(* [Id] is a right adjoint -- to itself, by [adj_id] -- so the general bridge
   of Construction/Comma/Limit.v supplies its cone-level preservation. *)
Definition Sets_Id_PreservesImageLimit : @PreservesImageLimit Sets Sets Id :=
  right_adjoint_PreservesImageLimit (@adj_id Sets).

(* A solution set at [d] for [Id]: the one-member family whose single object
   is [d] and whose single arrow is [id[d]].  Every [h : d ~> c] factors as
   [fmap[Id] h ∘ id ≈ h], which is [id_right].

   [Build_SolutionSet] is applied with all four of its parameters written out.
   That is not stylistic: it was forced by a measured break.  A record literal
   [{| sol_arr := fun _ => id ; ... |}] elaborates its fields before the
   ascribed type has fixed [U] and [D], so [id] is elaborated against
   [?d ~{?D}~> fobj[?U] d].  Rocq 9.1 resolves that from the ascription; Coq
   8.19 and 8.20 do not, and report "The term id{?Category} ... is expected to
   have type ?d ~{?D}~> fobj[?U] d" (observed on both, through
   [nix build .#category-theory_8_19 .#category-theory_8_20]).  Naming the
   parameters removes the metavariables.  Closing the covering equation with
   [exact (id_right h)] rather than [apply id_right] is defensive against the
   same class of problem and was not separately measured: [exact] settles
   [fmap[Id] h ∘ id ≈ h] by CONVERSION, [fmap[Id]] beta-iota-reducing to the
   identity, instead of leaving that reduction to unification. *)
Definition Sets_Id_SolutionSet (d : Sets) : SolutionSet (@Id Sets) d.
Proof.
  unshelve refine (@Build_SolutionSet Sets Sets (@Id Sets) d
                     poly_unit
                     (fun _ : poly_unit => d)
                     (fun _ : poly_unit => @id Sets d)
                     _).
  intros c h.
  exists ttt.
  exists h.
  exact (id_right h).
Defined.

(** ** The application *)

(* [GAFT] at [Id : Sets ⟶ Sets], all three premises discharged by in-tree
   constructions.  An earlier revision of this comment pointed at "the [Set]
   pinning this inherits from [GAFT]'s frozen universe context"; that pinning
   was removed on 2026-09-17 and the header records the measurement. *)
Definition GAFT_at_Sets_Id : { F : Sets ⟶ Sets & F ⊣ Id } :=
  GAFT (@Id Sets) Sets_Complete
    Sets_Id_PreservesImageLimit Sets_Id_SolutionSet.

(* The produced left adjoint is naturally isomorphic to [Id], as it must be:
   left adjoints to a fixed functor are unique up to natural isomorphism
   ([left_adjoint_iso], Theory/Adjunction.v), and [adj_id] exhibits [Id]
   as a second left adjoint to [Id].  This is what makes the "toy" label
   above a proved statement rather than an editorial one. *)
Definition GAFT_at_Sets_Id_is_Id : projT1 GAFT_at_Sets_Id ≈ @Id Sets :=
  left_adjoint_iso (@Id Sets) (projT1 GAFT_at_Sets_Id) (@Id Sets)
    (projT2 GAFT_at_Sets_Id) (@adj_id Sets).

(** ** By-product: equalizers in [Sets] *)

(* Read off completeness by [Complete_HasEqualizers]; NOT the first and not
   the only inhabitant -- see the note below.  Kept a [Definition]. *)
Definition Sets_HasEqualizers : HasEqualizers Sets :=
  Complete_HasEqualizers Sets_Complete.

(* IT IS NOT THE ONLY ONE, IN EITHER SENSE.  THREE library files inhabit
   [HasEqualizers Sets]: this one, [SetsEqualizers]
   (Adjunction/CokernelPair.v, whose own comment calls its
   route "the cheapest of the three in-tree routes"), and
   [DiagSets_HasEqualizers] (Adjunction/Diagonal/Finite.v); all three
   are registered in _CoqProject.  Test/ProbeToposInstances404.v adds a
   fourth, CONDITIONAL one resting on [Untruncate].  None of the four is
   compared with any other: their types line up and no agreement proof is
   built.  An earlier revision of this note, and of the header sentence
   above, called this the only library-file inhabitant; that was false when
   written -- the other two predate it -- and is corrected here rather than
   amended away.  The note stays below the definition so that the line
   number of [Sets_HasEqualizers] does not move.  State the criterion, since
   the number moves with it: FIVE `.v` files cited that line number before
   this change, seven occurrences counting CLAUDE.md's two, and
   Instance/Sets/Cone.v is the sixth `.v` citation. *)

(** ** The characterization at [Sets], and that its reverse half is the
       application already here *)

(* #436's [GAFT_iff] read at [Id : Sets ⟶ Sets].  These are cross-checks,
   not new results: they demonstrate that the biconditional's reverse half
   IS [GAFT_at_Sets_Id] above, on the nose, and that the solution set the
   forward half manufactures out of an adjunction agrees with the
   hand-built [Sets_Id_SolutionSet] in index, member and arrow — while
   NOT being the same record, since the two [sol_covers] witnesses differ
   (Test/ProbeGAFTCharacterization436.v pins that). *)

Definition GAFT_iff_at_Sets_Id :
  { F : Sets ⟶ Sets & F ⊣ Id }
    ↔ (@PreservesImageLimit Sets Sets Id * (∀ d : Sets, SolutionSet (@Id Sets) d))
  := GAFT_iff (@Id Sets) Sets_Complete.

Definition Sets_Id_has_left : { F : Sets ⟶ Sets & F ⊣ Id } :=
  snd GAFT_iff_at_Sets_Id (Sets_Id_PreservesImageLimit, Sets_Id_SolutionSet).

Definition Sets_Id_has_left_is_GAFT_at_Sets_Id :
  Sets_Id_has_left = GAFT_at_Sets_Id := eq_refl.

(* The manufactured family at [Id], and its agreement with the hand-built
   one at each of the three data fields. *)

Definition Sets_Id_SolutionSet_of_adjunction (d : Sets) : SolutionSet (@Id Sets) d :=
  solution_set_of_adjunction (@adj_id Sets) d.

Definition Sets_Id_sols_index (d : Sets) :
  sol_index (Sets_Id_SolutionSet_of_adjunction d)
    = sol_index (Sets_Id_SolutionSet d) := eq_refl.

Definition Sets_Id_sols_obj (d : Sets) (i : poly_unit) :
  sol_obj (Sets_Id_SolutionSet_of_adjunction d) i
    = sol_obj (Sets_Id_SolutionSet d) i := eq_refl.

Definition Sets_Id_sols_arr (d : Sets) (i : poly_unit) :
  sol_arr (Sets_Id_SolutionSet_of_adjunction d) i
    = sol_arr (Sets_Id_SolutionSet d) i := eq_refl.
