Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Construction.ColouredPROP.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.
Require Import Category.Construction.ColouredPROP.Free.
Require Import Category.Construction.ColouredPROP.Cast.
Require Import Category.Construction.ColouredPROP.Monoidal.
Require Import Category.Construction.ColouredPROP.Braided.
Require Import Category.Construction.Quotient.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(** * The free coloured PROP, bundled: the library's first [ColouredPROP] *)

(*
   nLab: https://ncatlab.org/nlab/show/strict+monoidal+category
   nLab: https://ncatlab.org/nlab/show/free+category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FreeColouredPROP.

Context {Colour : Type}.
Context (S : CSignature Colour).
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).

(** ** Comparison lemmas

    Each states that a structural map of [CFreeCat_Monoidal S Cdec]
    equals the transported identity along the corresponding boundary
    equation.  Both sides are the same [match] on the same proof
    term, so each proof is [reflexivity]. *)

(** The associator [(x ++ y) ++ z ≅ x ++ (y ++ z)] is the transported
    identity along [eq_sym (app_assoc x y z)] — the orientation of
    [Cast.v]'s [to]. *)
Lemma CFreeCat_strict_assoc_to (x y z : list Colour) :
  to (@tensor_assoc (CFreeCat S) (CFreeCat_Monoidal S Cdec) x y z)
  ≈ match eq_sym (app_assoc x y z) in _ = T
      return ((x ++ y) ++ z ~{ CFreeCat S }~> T)
    with eq_refl => id end.
Proof. reflexivity. Qed.

(** The left unitor [[] ++ x ≅ x] is the transported identity along
    [app_nil_l x] (definitionally trivial: [app] is left-strict). *)
Lemma CFreeCat_strict_unit_left_to (x : list Colour) :
  to (@unit_left (CFreeCat S) (CFreeCat_Monoidal S Cdec) x)
  ≈ match app_nil_l x in _ = T
      return ([] ++ x ~{ CFreeCat S }~> T)
    with eq_refl => id end.
Proof. reflexivity. Qed.

(** The right unitor [x ++ [] ≅ x] is the transported identity along
    [app_nil_r x] (a genuinely propositional equation). *)
Lemma CFreeCat_strict_unit_right_to (x : list Colour) :
  to (@unit_right (CFreeCat S) (CFreeCat_Monoidal S Cdec) x)
  ≈ match app_nil_r x in _ = T
      return (x ++ [] ~{ CFreeCat S }~> T)
    with eq_refl => id end.
Proof. reflexivity. Qed.

(** ** The Strict instance over THE shared Monoidal record *)

Definition CFreeCat_Strict : @StrictMonoidal (CFreeCat S) := {|
  strict_is_monoidal    := CFreeCat_Monoidal S Cdec;  (* THE shared record *)
  strict_assoc_obj      := fun x y z => eq_sym (app_assoc x y z);
  strict_unit_left_obj  := fun x => app_nil_l x;
  strict_unit_right_obj := fun x => app_nil_r x;
  strict_assoc_to       := fun x y z => CFreeCat_strict_assoc_to x y z;
  strict_unit_left_to   := fun x => CFreeCat_strict_unit_left_to x;
  strict_unit_right_to  := fun x => CFreeCat_strict_unit_right_to x
|}.

(** ** The bundled instance

    All three structure fields name records that project to THE
    shared [CFreeCat_Monoidal S Cdec], so each equality field below
    is [eq_refl].  The record is an explicit [Build_ColouredPROP]
    application, so no inference is left to a record literal. *)

Definition FreeColouredPROP : ColouredPROP Colour :=
  Build_ColouredPROP Colour
    (CFreeCat S)
    CFreeCat_Strict
    (CFreeCat_Symmetric S Cdec)

    (* [strict_is_monoidal CFreeCat_Strict] and
       [braided_is_monoidal (symmetric_is_braided
        (CFreeCat_Symmetric S Cdec))] both reduce to the literal
       term [CFreeCat_Monoidal S Cdec]. *)
    eq_refl

    (* Objects of [CFreeCat S] are literally the colour words. *)
    (fun cs : list Colour => cs)

    (* [I] of [CFreeCat_Monoidal S Cdec] is the literal [[]]. *)
    eq_refl

    (* [fobj (CFreeCat_Tensor S) (cs, ds)] reduces to [cs ++ ds]. *)
    (fun cs ds : list Colour => eq_refl).

(** ** Side-condition instances for the interpretation files

    The hom-setoid equivalence of [CFreeCat S] is [CTermEq S] by
    delta/beta reduction of [CTerm_Setoid], and [CTermEq S] is
    already [Prop]-valued, so the [Prop] reflection is the identity
    in both directions. *)

#[export] Instance CFreeCat_HomEqProp : HomEqProp (CFreeCat S) :=
  Build_HomEqProp (CFreeCat S)
    (fun cs ds : list Colour => @CTermEq Colour S cs ds)
    (fun _ _ _ _ H => H)
    (fun _ _ _ _ H => H).

(** Objects of [CFreeCat S] are colour words, whose equality
    [list_eq_dec Cdec] decides.  A [Definition], not an [Instance]:
    it is [Cdec]-conditional (D2), and call sites pass it explicitly
    so that exactly one canonical decider circulates per colour
    type. *)

Definition CFreeCat_ObjDecEq : ObjDecEq (CFreeCat S) := list_eq_dec Cdec.

(** ** Machine-checked sanity

    Each [Example] holds by a closed proof term — all but the last by
    [eq_refl], witnessing that the corresponding field of
    [FreeColouredPROP] is definitional; the final cons decomposition
    instead pins the recorded [cprop_tensor_app] conversion between
    the object correspondence and the shared strict [Monoidal]
    path. *)

(** The coherence between the strict and symmetric [Monoidal] paths
    is the reflexivity proof itself — the "known limitation"
    discussed in [Construction/PROP.v] does not bite on the free
    coloured PROP. *)
Example FreeColouredPROP_coherence_is_refl :
  @cprop_monoidal_coherence Colour FreeColouredPROP = eq_refl := eq_refl.

(** The object correspondence is the identity on colour words. *)
Example FreeColouredPROP_of_list_id (cs : list Colour) :
  cprop_of_list (ColouredPROP := FreeColouredPROP) cs = cs := eq_refl.

(** The monoidal unit of THE shared record is the literal empty
    word. *)
Example FreeColouredPROP_I :
  @I (CFreeCat S) (CFreeCat_Monoidal S Cdec) = ([] : list Colour) := eq_refl.

(** The same unit, projected through the bundled instance — pinning
    that the instance path and the shared record agree on the
    nose. *)
Example FreeColouredPROP_I_instance :
  @I (CFreeCat S)
     (@strict_is_monoidal (CFreeCat S) (@cprop_strict Colour FreeColouredPROP))
  = ([] : list Colour) := eq_refl.

(** Tensor-on-objects is literally concatenation, with [eq_refl]
    proof. *)
Example FreeColouredPROP_tensor_app_is_refl (cs ds : list Colour) :
  cprop_tensor_app (ColouredPROP := FreeColouredPROP) cs ds = eq_refl
  := eq_refl.

(** The singleton wire object for colour [c] is the literal
    one-element word [[c]]. *)
Example FreeColouredPROP_wire (c : Colour) :
  wire (P := FreeColouredPROP) c = [c] := eq_refl.

(** Cons decomposition smoke test: prepending a colour to a word is
    the tensor of its wire with the tail, THROUGH the shared strict
    [Monoidal] path.  The proof term is not bare [eq_refl] but
    [eq_sym (cprop_tensor_app [c] cs)]: it exercises the recorded
    tensor/concatenation conversion at the definitional boundary
    [[c] ++ cs = c :: cs], the coloured analogue of the one-sorted
    donor's [FreePROP_of_nat_S_smoke] (Construction/PROP/Instance.v),
    and would catch any regression in the shared-record wiring that
    the identity-shaped [Example]s above cannot see. *)
Example FreeColouredPROP_cons_decomp (c : Colour) (cs : list Colour) :
  cprop_of_list (ColouredPROP := FreeColouredPROP) (c :: cs)
  = (wire (P := FreeColouredPROP) c
       ⨂[@strict_is_monoidal (CFreeCat S)
           (@cprop_strict Colour FreeColouredPROP)]
     cprop_of_list (ColouredPROP := FreeColouredPROP) cs)%object
  := eq_sym (cprop_tensor_app (ColouredPROP := FreeColouredPROP) [c] cs).

End FreeColouredPROP.

Arguments CFreeCat_Strict {Colour} S Cdec : assert.
Arguments FreeColouredPROP {Colour} S Cdec : assert.
Arguments CFreeCat_HomEqProp {Colour} S : assert.
(* [ObjDecEq] is a definitional (singleton) class, so the constant's
   argument list continues with the two objects being compared. *)
Arguments CFreeCat_ObjDecEq {Colour} S Cdec x y : assert.
