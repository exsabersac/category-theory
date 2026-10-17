Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Generator.
Require Import Category.Structure.Generator.Concrete.
Require Import Category.Theory.Concrete.

Generalizable All Variables.

(*
 nLab:  https://ncatlab.org/nlab/show/separator
 nLab:  https://ncatlab.org/nlab/show/well-pointed+category

   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The singleton separates *)

(* A global element of [X], as a map out of the singleton setoid.  This is
   the same probe Instance/Sets.v's [injectivity_is_monic] uses to
   characterize monos as injections, and the same one
   Theory/Concrete.v's [Sets_point] uses out of the terminal object.

   It must stay TRANSPARENT, and that is measured: replacing this
   [Program Definition] by a tactic proof closed with [Qed], everything
   else unchanged, makes the next lemma's [exact] refuse with
   "The term "H (sets_elem x) ttt" has type "(f ∘ sets_elem x) ttt ≈
   (g ∘ sets_elem x) ttt" while it is expected to have type "f x ≈ g x"",
   a CONVERSION refusal: the whole proof is the reduction of the constant
   map at the unique inhabitant.  [sets_elem_term] below measures the
   same way, its message naming [1] where this one names
   [unit_setoid_object]. *)
Program Definition sets_elem@{o so+} {X : SetoidObject@{o o}}
  (x : carrier X) :
  unit_setoid_object@{o o} ~{Sets@{o so}}~> X := {| morphism := fun _ => x |}.

(* Global elements distinguish setoid maps.  Two maps agreeing after every
   arrow out of the singleton agree at every element, because the element
   [x] is recovered as [sets_elem x] applied to the unique inhabitant of
   the singleton. *)
Lemma Sets_unit_separates@{o so+} :
  @IsSeparator Sets@{o so} unit_setoid_object@{o o}.
Proof.
  intros X Y f g H x.
  exact (H (sets_elem x) ttt).
Qed.

(* Mac Lane's first example, as the one-object generating family. *)
Definition Sets_Generator@{o so+} : Generator Sets@{o so} :=
  @Generator_of_separator Sets@{o so} unit_setoid_object@{o o}
    Sets_unit_separates.

(** ** The terminal object separates *)

(* The same constant map, but out of [Sets_Terminal]'s object rather than
   out of [unit_setoid_object].  It has to be built separately: the two
   objects do not convert, as the header measures. *)
Program Definition sets_elem_term@{o so+} {X : SetoidObject@{o o}}
  (x : carrier X) :
  @terminal_obj Sets@{o so} Sets_Terminal@{so o} ~{Sets@{o so}}~> X :=
  {| morphism := fun _ => x |}.

(* Route 1, the delivered constant: the direct proof.  This is issue
   #447's pinned name. *)
Lemma Sets_terminal_separates@{o so+} :
  @IsSeparator Sets@{o so}
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}).
Proof.
  intros X Y f g H x.
  exact (H (sets_elem_term x) ttt).
Qed.

Definition Sets_terminal_Generator@{o so+} : Generator Sets@{o so} :=
  @Generator_of_separator Sets@{o so}
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
    Sets_terminal_separates.

(* The isomorphism the transport route needs.  Both components are the
   constant map at [ttt], and both triangle laws hold by case analysis on
   the unique inhabitant.  Kept [Defined] because it is DATA; closing it
   with [Qed] was measured to compile, nothing in this file needing it
   transparent, but opaque data blocks downstream conversion and
   Instance/Sets.v keeps its own coherence isomorphisms [Defined] for the
   same reason. *)
Definition Sets_terminal_unit_iso@{o so+} :
  @Isomorphism Sets@{o so}
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
    unit_setoid_object@{o o}.
Proof.
  unshelve refine {| to := _; from := _ |}.
  - unshelve refine {| morphism := fun _ => ttt |}; proper.
  - unshelve refine {| morphism := fun _ => ttt |}; proper.
  - intro u; now destruct u.
  - intro u; now destruct u.
Defined.

(* Route 2: transport along that isomorphism, in the direction
   [unit_setoid_object ≅ terminal_obj], through Structure/Generator.v's
   [separator_iso]. *)
Definition Sets_terminal_separates_by_transport@{o so+} :
  @IsSeparator Sets@{o so}
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) :=
  separator_iso Sets_unit_separates (iso_sym Sets_terminal_unit_iso).

(* Route 3: the prior art, unpacked through Structure/Generator/
   Concrete.v's bridge.  This constant exists so that the header's claim
   about Theory/Concrete.v is checked by the compiler rather than
   asserted. *)
Definition Sets_terminal_separates_from_Concrete@{o so+} :
  @IsSeparator Sets@{o so}
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) :=
  IsSeparator_of_Separator
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) Sets_Separator@{o so}.

(** ** The initial object does not separate *)

(* A theorem, not a refusal: the statement is well typed and has no
   inhabitant.  There is nothing to probe with out of the empty setoid,
   so the hypothesis is vacuous and would identify the identity of the
   two-element setoid with negation. *)
Lemma Sets_empty_not_separates@{o so+} :
  @IsSeparator Sets@{o so}
    (@terminal_obj (Sets@{o so}^op) Sets_Initial@{so o}) → False.
Proof.
  intro Hsep.
  apply Sets_two_arrows@{o so}.
  apply Hsep.
  intros k u; destruct u.
Qed.

(* The same theorem by the route issue #447 named, and pinned at object
   universe [Set] by its donors, as the header attributes. *)
Lemma Sets_empty_not_separates_pick@{so+} :
  @IsSeparator Sets@{Set so}
    (@terminal_obj (Sets@{Set so}^op) Sets_Initial@{so Set}) → False.
Proof.
  intro Hsep.
  apply Bool.diff_true_false.
  refine (Hsep unit_setoid_object@{Set Set} _ pick_true pick_false _ ttt).
  intros k u; destruct u.
Qed.
