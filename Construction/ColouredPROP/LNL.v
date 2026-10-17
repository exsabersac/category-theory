Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.CopyDiscard.
Require Import Category.Structure.Monoidal.CopyDiscard.Deterministic.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.CommutativeComonoid.
Require Import Category.Theory.Algebra.Comonoid.Hom.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.ColouredPROP.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.Instance.
Require Import Category.Construction.ColouredPROP.Interp.
Require Import Category.Construction.ColouredPROP.Presentation.
Require Import Category.Construction.ColouredPROP.Linear.
Require Import Category.Construction.ColouredPROP.Supply.
Require Import Category.Construction.ColouredPROP.Supply.Instance.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(** * The linear/non-linear comonoid-supply bridge *)

(*
   nLab: https://ncatlab.org/nlab/show/copy-discard+category
   nLab: https://ncatlab.org/nlab/show/comonoid
   Reference: Benton, "A mixed linear and non-linear logic: proofs,
   Reference: Cho & Jacobs, "Disintegration and Bayesian inversion via
   Reference: Fong & Spivak, "Supplying bells and whistles in

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------ *)

(** ** The bridge: supplied objects and deterministic maps *)

Section LNLBridge.

Context {Colour : Type}.
Context (P : ColouredPROP Colour).
Context (copyable : Colour -> bool).
Context `{SS : @SelectiveSupply Colour P copyable}.

(** The coloured-PROP-object [⟦cs⟧c], as in
    [Construction/ColouredPROP.v] (whose notation is section-local
    there and must be re-declared per file). *)
Notation "⟦ cs ⟧c" := (@cprop_of_list Colour P cs)
  (at level 0, format "⟦ cs ⟧c").

(** Cho–Jacobs determinism at the derived boundary supplies: the two
    preservation squares

      scopy ds Hd ∘ f    ≈ (f ⨂ f) ∘ scopy cs Hc
      sdiscard ds Hd ∘ f ≈ sdiscard cs Hc

    packaged as the [ComonoidHom] they abbreviate — the bridge's
    export of [sel_deterministic] (Construction/ColouredPROP/
    Linear.v), stated directly at the derived supplies. *)
Definition SupplyDeterministic {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (f : ⟦cs⟧c ~{P}~> ⟦ds⟧c) : Type :=
  @ComonoidHom P (MBc P) ⟦cs⟧c ⟦ds⟧c
    (@ccomon_comonoid P (@cprop_symmetric Colour P) ⟦cs⟧c
       (supply_list cs Hc))
    (@ccomon_comonoid P (@cprop_symmetric Colour P) ⟦ds⟧c
       (supply_list ds Hd))
    f.

(** The bridge predicate IS Linear.v's determinism predicate, on the
    nose. *)
Example SupplyDeterministic_is_sel_deterministic
  {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (f : ⟦cs⟧c ~{P}~> ⟦ds⟧c) :
  SupplyDeterministic Hc Hd f = sel_deterministic Hc Hd f := eq_refl.

(** The embedding of the copyable colour class into the category of
    internal comonoids of [P] (at the symmetric-side monoidal
    structure [MBc P], where the derived supplies live): a boundary
    word together with its derived supply, sigma-packed as an object
    of [Comon].  Explicit pair, so both projections are
    definitional. *)
Definition supplied_obj (cs : list Colour)
  (H : all_copyable copyable cs) : @Comon (cprop_cat P) (MBc P) :=
  (⟦cs⟧c;
   @ccomon_comonoid P (@cprop_symmetric Colour P) ⟦cs⟧c
     (supply_list cs H)).

(** A supply-deterministic map lifts to a [Comon]-hom between the
    supplied objects: the sigma-pack of the map with its determinism
    witness. *)
Definition LNL_lift {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (f : ⟦cs⟧c ~{P}~> ⟦ds⟧c) (Hf : SupplyDeterministic Hc Hd f) :
  supplied_obj cs Hc ~{@Comon (cprop_cat P) (MBc P)}~> supplied_obj ds Hd :=
  (f; Hf).

(** The hom-sets of the embedding ARE the supply-deterministic maps —
    on the nose, not merely up to bijection: a [Comon]-hom between
    supplied objects is by definition a boundary map together with a
    [SupplyDeterministic] witness.  Machine-checked as a definitional
    equality of types. *)
Example LNL_hom_is_deterministic (cs ds : list Colour)
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds) :
  (supplied_obj cs Hc ~{@Comon (cprop_cat P) (MBc P)}~> supplied_obj ds Hd)
  = { f : ⟦cs⟧c ~{P}~> ⟦ds⟧c & SupplyDeterministic Hc Hd f }
  := eq_refl.

(** *** The round-trip lemma pair

    Forget after lift is the identity on the underlying map
    (reflexivity-grade), and — via faithfulness of [Comon_Forget] —
    any [Comon]-hom agreeing with [f] under the forgetful functor IS
    the lift of [f].  Together these exhibit the [Comon]-homs between
    supplied objects as exactly the deterministic maps. *)

Lemma LNL_forget_lift {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (f : ⟦cs⟧c ~{P}~> ⟦ds⟧c) (Hf : SupplyDeterministic Hc Hd f) :
  fmap[@Comon_Forget (cprop_cat P) (MBc P)] (LNL_lift Hc Hd f Hf) ≈ f.
Proof. reflexivity. Qed.

Lemma LNL_lift_unique {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (f : ⟦cs⟧c ~{P}~> ⟦ds⟧c) (Hf : SupplyDeterministic Hc Hd f)
  (u : supplied_obj cs Hc
         ~{@Comon (cprop_cat P) (MBc P)}~> supplied_obj ds Hd) :
  fmap[@Comon_Forget (cprop_cat P) (MBc P)] u ≈ f ->
  u ≈[@Comon (cprop_cat P) (MBc P)] LNL_lift Hc Hd f Hf.
Proof.
  intros Hu.
  apply (@fmap_inj _ _ _ (@Comon_Forget_Faithful (cprop_cat P) (MBc P)) _ _).
  rewrite LNL_forget_lift.
  exact Hu.
Qed.

(** The eta-form of uniqueness: every [Comon]-hom between supplied
    objects is the lift of its own underlying map, its determinism
    witness being its own second projection. *)
Corollary LNL_lift_eta {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (u : supplied_obj cs Hc
         ~{@Comon (cprop_cat P) (MBc P)}~> supplied_obj ds Hd) :
  u ≈[@Comon (cprop_cat P) (MBc P)]
  LNL_lift Hc Hd (fmap[@Comon_Forget (cprop_cat P) (MBc P)] u) `2 u.
Proof.
  apply LNL_lift_unique.
  reflexivity.
Qed.

(** *** Functoriality of the lift

    [LNL_lift] sends identities to identities and composites to
    composites.  Stated over an ARBITRARY determinism witness — the
    hom equivalence of [Comon] compares only the underlying maps, so
    the witness is irrelevant up to [≈]; [sel_deterministic_id] /
    [sel_deterministic_comp] of Linear.v provide the canonical
    witnesses. *)

Lemma LNL_lift_id (cs : list Colour) (Hc : all_copyable copyable cs)
  (Hid : SupplyDeterministic Hc Hc (@id P ⟦cs⟧c)) :
  LNL_lift Hc Hc id Hid ≈[@Comon (cprop_cat P) (MBc P)] id.
Proof.
  change (@id P ⟦cs⟧c ≈ @id P ⟦cs⟧c).
  reflexivity.
Qed.

Lemma LNL_lift_comp {cs ds es : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (He : all_copyable copyable es)
  (g : ⟦ds⟧c ~{P}~> ⟦es⟧c) (f : ⟦cs⟧c ~{P}~> ⟦ds⟧c)
  (Hg : SupplyDeterministic Hd He g) (Hf : SupplyDeterministic Hc Hd f)
  (Hgf : SupplyDeterministic Hc He (g ∘ f)) :
  LNL_lift Hc He (g ∘ f) Hgf
    ≈[@Comon (cprop_cat P) (MBc P)]
  LNL_lift Hd He g Hg ∘[@Comon (cprop_cat P) (MBc P)] LNL_lift Hc Hd f Hf.
Proof.
  change (g ∘ f ≈ g ∘ f).
  reflexivity.
Qed.

End LNLBridge.

(* ------------------------------------------------------------------ *)

(** ** Total-supply degeneration: [CopyDiscard] from a total supply

    When EVERY colour is copyable, the free supplied PROP collapses
    into the world of Structure/Monoidal/CopyDiscard.v: the derived
    boundary supplies assemble into an honest [CopyDiscard] structure.
    This is the degeneration test for the selective-supply design —
    dial the copyability predicate to [fun _ => true] and the
    [CopyDiscard] class is recovered on the nose.

    The four coherence obligations are [exact] applications of the
    Fong–Spivak coherence theorems [supply_app_delta] /
    [supply_app_epsilon] of Supply.v (tensor) and of the definitional
    collapse of the empty-boundary supply onto the unit comonoid
    (unit): at [SupplyPROP] the [ctensor_app_b] / [cunit_nil_b]
    mediation is [eq_refl] (the pinned Examples of Supply/Instance.v),
    so the [hom_cast] mediation of the theorems vanishes
    definitionally and no cast survives into the obligations.

    On class fit: [CopyDiscard] supplies a comonoid on EVERY object of
    the category, whereas a coloured-PROP supply covers only the image
    of [cprop_of_list]; in general the two differ by a surjectivity
    hypothesis.  At [SupplyPROP] the objects ARE the colour words and
    [cprop_of_list] is the identity, so the gap is empty — recorded as
    a non-defect of the class, not worked around. *)

Section TotalSupply.

Context {Colour : Type}.
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (S : CSignature Colour).

(** Every colour word is all-copyable for the total predicate: a
    computing fixpoint ([forallb (fun _ => true)] peels cons cells
    definitionally). *)
Fixpoint all_true (cs : list Colour) :
  all_copyable (fun _ : Colour => true) cs :=
  match cs with
  | [] => eq_refl
  | _ :: cs' => all_true cs'
  end.

Notation TotalPROP := (SupplyPROP Cdec S (fun _ : Colour => true)).
Notation TotalSS :=
  (SupplyPROP_SelectiveSupply Cdec S (fun _ : Colour => true)).

(** Decidable object equality for the presented supply PROP: objects
    are colour words (per the D2 discipline this is a definition fed
    the one canonical [Cdec], not an instance). *)
Definition TotalPROP_ObjDecEq : @ObjDecEq (cprop_cat TotalPROP) :=
  CFreeCat_ObjDecEq (SupplyExtSig S (fun _ : Colour => true)) Cdec.

(** The [CopyDiscard] instance: the comonoid on the word [X] is its
    derived supply.  Fully type-ascribed Program definition, keeping
    every obligation at the ascribed instance (the [CPresented_Strict]
    precedent of Presentation.v); the obligations are the class fields
    verbatim. *)
#[local] Obligation Tactic := intros.

Program Definition CopyDiscard_of_total_supply :
  @CopyDiscard (cprop_cat TotalPROP)
    (@cprop_symmetric Colour TotalPROP) := {|
  cd_comonoid := fun X : cprop_cat TotalPROP =>
    supply_list (P := TotalPROP) (SS := TotalSS) X (all_true X)
|}.
Next Obligation.
  (* cd_tensor_delta: [X ⨂ Y ≡ X ++ Y] definitionally, so this IS the
     coherence square at [all_true] evidence, its [hom_cast] mediation
     gone by conversion. *)
  exact (@supply_app_delta Colour TotalPROP TotalPROP_ObjDecEq
           (fun _ : Colour => true) TotalSS
           X Y (all_true X) (all_true Y) (all_true ((X ++ Y)%list))).
Qed.
Next Obligation.
  (* cd_tensor_epsilon: mirror. *)
  exact (@supply_app_epsilon Colour TotalPROP TotalPROP_ObjDecEq
           (fun _ : Colour => true) TotalSS
           X Y (all_true X) (all_true Y) (all_true ((X ++ Y)%list))).
Qed.
Next Obligation.
  (* cd_unit_delta: the supply on [I ≡ []] is the (untransported) unit
     comonoid, whose δ is the inverse left unitor on the nose. *)
  reflexivity.
Qed.
Next Obligation.
  (* cd_unit_epsilon: its ε is the identity on the nose. *)
  reflexivity.
Qed.

(** The copy and discard morphisms of the degenerate instance are the
    derived supply's, definitionally. *)
Example CopyDiscard_of_total_supply_copy (X : list Colour) :
  @copy (cprop_cat TotalPROP) (@cprop_symmetric Colour TotalPROP)
    CopyDiscard_of_total_supply X
  = scopy (P := TotalPROP) (SS := TotalSS) X (all_true X) := eq_refl.

Example CopyDiscard_of_total_supply_discard (X : list Colour) :
  @discard (cprop_cat TotalPROP) (@cprop_symmetric Colour TotalPROP)
    CopyDiscard_of_total_supply X
  = sdiscard (P := TotalPROP) (SS := TotalSS) X (all_true X) := eq_refl.

(** The degeneration also closes the vocabulary loop of the SCOPE
    CONTRACT: at the total supply — the one instance where a global
    [cd_comonoid] supply exists — the bridge predicate
    [SupplyDeterministic] IS [deterministic] of
    CopyDiscard/Deterministic.v at [CopyDiscard_of_total_supply], on
    the nose.  Machine-checked as a definitional equality of types, so
    any drift in the [cd_comonoid] choice above or in the
    [supply_list] mediation would be caught here. *)
Example SupplyDeterministic_is_deterministic (X Y : list Colour)
  (f : X ~{TotalPROP}~> Y) :
  SupplyDeterministic TotalPROP (fun _ : Colour => true)
    (SS := TotalSS) (all_true X) (all_true Y) f
  = @deterministic _ _ CopyDiscard_of_total_supply X Y f
  := eq_refl.

End TotalSupply.

(* ------------------------------------------------------------------ *)

(** ** The linear/cartesian characterization

    At the pure supply PROP — base signature [Empty_CSig], so the ONLY
    generators are the per-wire dup/del of copyable colours — the
    copyability predicate is characterised by the geometry of the
    hom-sets: a colour is linear exactly when its wire supports neither
    a commutative-comonoid supply nor a bare fan-out morphism, and
    copyable exactly when it supports both.  Fan-out at a linear wire is
    not disallowed by convention; it is UNINHABITED
    ([SupplyPROP_no_fanout] — even a supply is refuted through its own
    comultiplication), and conversely a copyable wire realises its
    supply syntactically ([supply_wire_comonoid], [SupplyPROP_fanout]).
    This is the categorical content of the fan-out linearity check. *)

Section Characterization.

Context {Colour : Type}.
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (copyable : Colour -> bool).

Notation PurePROP := (SupplyPROP Cdec Empty_CSig copyable).

Theorem linear_cartesian_characterization (c : Colour) :
  (LinearColour copyable c
     <-> ((@CommutativeComonoid (cprop_cat PurePROP)
             (@cprop_symmetric Colour PurePROP)
             (wire (P := PurePROP) c) -> False)
          /\ ((([c] : list Colour) ~{PurePROP}~> [c; c]) -> False)))
  /\ (copyable c = true
     <-> (inhabited (@CommutativeComonoid (cprop_cat PurePROP)
                       (@cprop_symmetric Colour PurePROP)
                       (wire (P := PurePROP) c))
          /\ inhabited (([c] : list Colour) ~{PurePROP}~> [c; c]))).
Proof.
  split.
  - (* linear <-> neither supply nor fan-out *)
    split.
    + intros Hlin.
      split.
      * (* no supply: its comultiplication would BE a fan-out *)
        intros M.
        exact (SupplyPROP_no_fanout Cdec Empty_CSig copyable c Hlin
                 (pure_base_conservative Cdec c)
                 (@ccomon_delta (cprop_cat PurePROP)
                    (@cprop_symmetric Colour PurePROP)
                    (wire (P := PurePROP) c) M)).
      * (* no fan-out *)
        exact (SupplyPROP_no_fanout Cdec Empty_CSig copyable c Hlin
                 (pure_base_conservative Cdec c)).
    + intros [HnoM _].
      destruct (copyable c) eqn:Hc.
      * exfalso.
        exact (HnoM (supply_wire_comonoid Cdec Empty_CSig copyable c Hc)).
      * exact Hc.
  - (* copyable <-> both supply and fan-out *)
    split.
    + intros Hc.
      split.
      * exact (inhabits
                 (supply_wire_comonoid Cdec Empty_CSig copyable c Hc)).
      * exact (inhabits (SupplyPROP_fanout Cdec Empty_CSig copyable c Hc)).
    + intros [_ [t]].
      destruct (copyable c) eqn:Hc.
      * reflexivity.
      * exfalso.
        exact (SupplyPROP_no_fanout Cdec Empty_CSig copyable c Hc
                 (pure_base_conservative Cdec c) t).
Qed.

End Characterization.
