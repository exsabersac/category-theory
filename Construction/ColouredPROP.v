Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Structure.Monoidal.Hypergraph.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(** * Coloured PROPs *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ColouredPROP.

Context (Colour : Type).

Class ColouredPROP : Type := {
  cprop_cat : Category;

  cprop_strict : @StrictMonoidal cprop_cat;
  cprop_symmetric : @SymmetricMonoidal cprop_cat;

  (** Coherence between the two [Monoidal] paths — see the analogous
      [prop_monoidal_coherence] in [Construction/PROP.v] for
      motivation. *)
  cprop_monoidal_coherence :
    (@strict_is_monoidal cprop_cat cprop_strict)
    = (@braided_is_monoidal cprop_cat
         (@symmetric_is_braided cprop_cat cprop_symmetric));

  (** The canonical object correspondence: every list of colours names
      an object of [cprop_cat], with the empty list the monoidal unit
      and concatenation reflecting tensor. *)
  cprop_of_list : list Colour -> @obj cprop_cat;

  cprop_unit_nil :
    @I cprop_cat (@strict_is_monoidal cprop_cat cprop_strict)
    = cprop_of_list nil;

  cprop_tensor_app : forall (cs ds : list Colour),
    ((cprop_of_list cs) ⨂[@strict_is_monoidal cprop_cat cprop_strict]
     (cprop_of_list ds))%object
    = cprop_of_list (cs ++ ds)
}.

#[export] Existing Instance cprop_strict.
#[export] Existing Instance cprop_symmetric.

Coercion cprop_cat : ColouredPROP >-> Category.

End ColouredPROP.

Arguments ColouredPROP Colour : assert.
Arguments cprop_cat {Colour} _.
Arguments cprop_strict {Colour} _.
Arguments cprop_symmetric {Colour} _.
Arguments cprop_monoidal_coherence {Colour} _.
Arguments cprop_of_list {Colour _} _.
Arguments cprop_unit_nil {Colour _}.
Arguments cprop_tensor_app {Colour _} _ _.

(** ** Smart accessors *)

Section ColouredPROPLemmas.

Context {Colour : Type}.
Context (P : ColouredPROP Colour).

(** The Coloured-PROP-object indexed by colour list [cs]. *)
Notation "'⟦' cs '⟧c'" := (cprop_of_list (ColouredPROP := P) cs)
  (at level 0, format "⟦ cs ⟧c").

(** Sanity: the unit object of [P] is [⟦[]⟧c]. *)
Lemma cprop_I_eq_nil : @I P _ = ⟦nil⟧c.
Proof. exact (@cprop_unit_nil Colour P). Qed.

(** Sanity: tensor on objects is list concatenation. *)
Lemma cprop_tensor_eq_app (cs ds : list Colour) :
  (⟦cs⟧c ⨂ ⟦ds⟧c)%object = ⟦cs ++ ds⟧c.
Proof. exact (cprop_tensor_app cs ds). Qed.

(** Singleton-colour wire: [⟦[c]⟧c] is the canonical 1-colour object. *)
Definition wire (c : Colour) : @obj P := ⟦[c]⟧c.

End ColouredPROPLemmas.

Arguments wire {Colour P} c.

(** ** Hypergraph Coloured PROPs

    Analogous to [HypergraphPROP]: a [ColouredPROP] whose underlying
    symmetric monoidal category carries a [Hypergraph] instance.
    Every wire-list carries a special commutative Frobenius algebra
    coherent under concatenation. *)

Class HypergraphColouredPROP {Colour : Type} : Type := {
  hcprop : ColouredPROP Colour;

  hcprop_hyper : @Hypergraph
                   (@cprop_cat Colour hcprop)
                   (@cprop_symmetric Colour hcprop)
}.

Arguments HypergraphColouredPROP Colour : assert.

#[export] Existing Instance hcprop_hyper.

Coercion hcprop : HypergraphColouredPROP >-> ColouredPROP.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
