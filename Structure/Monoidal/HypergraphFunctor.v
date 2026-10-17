Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.
Require Import Category.Structure.Monoidal.Hypergraph.

Generalizable All Variables.

(*
    Reference: Fong, "The Algebra of Open and Interconnected Systems"
    nLab:      https://ncatlab.org/nlab/show/hypergraph+category
    nLab:      https://ncatlab.org/nlab/show/monoidal+functor
    Wikipedia: no dedicated article for hypergraph categories or

   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section HypergraphFunctor.

Context {C : Category}.
Context `{SC : @SymmetricMonoidal C}.
Context `{HG_C : @Hypergraph C SC}.

Context {D : Category}.
Context `{SD : @SymmetricMonoidal D}.
Context `{HG_D : @Hypergraph D SD}.

(** A hypergraph functor [F : C ⟶ D] consists of an underlying functor
    together with *witnesses* that
      - tensor on objects is preserved up to a *fixed* iso [hf_tensor X Y :
        F X ⨂ F Y ≅ F (X ⨂ Y)];
      - the monoidal unit is preserved up to a *fixed* iso [hf_unit :
        I ≅ F I];
      - the SCFA generators on every [X] are preserved up to those
        transports (one equation per generator).

    The strict-on-the-nose case takes [hf_tensor X Y := id] and
    [hf_unit := id]; the SCFA preservation equations then reduce to the
    literature form [F (μ_X) ≈ μ_{F X}], etc.  We keep the iso
    parameterisation in the record because the standard library's
    [Functor] type does not record monoidality, so any concrete
    hypergraph-functor instance must supply these comparison iso's
    explicitly. *)

Record HypergraphFunctor : Type := {
  hf_functor :> C ⟶ D;

  (** Comparison isomorphisms (the lax-monoidal data on [hf_functor],
      packaged here since [Functor] does not record it). *)
  hf_unit_iso : @I D _ ≅ hf_functor (@I C _);
  hf_tensor_iso : forall (X Y : C),
    (hf_functor X ⨂ hf_functor Y)%object ≅ hf_functor (X ⨂ Y)%object;

  (** SCFA preservation: the four generators on every [X] are sent to
      the corresponding generators on [F X], up to transport along the
      comparison isomorphisms.

      For [mu]:
        F (μ_X)  ∘  hf_tensor_iso X X  ≈  μ_{F X}.
      For [delta]: the corresponding equation in the opposite direction.
      For [eta]: the unit-comparison transports the source.
      For [epsilon]: the unit-comparison transports the codomain. *)

  hf_preserves_mu : forall (X : C),
    fmap[hf_functor] (scfa_mu (scfa X)) ∘ to (hf_tensor_iso X X)
      ≈ scfa_mu (scfa (hf_functor X));

  hf_preserves_eta : forall (X : C),
    fmap[hf_functor] (scfa_eta (scfa X)) ∘ to hf_unit_iso
      ≈ scfa_eta (scfa (hf_functor X));

  hf_preserves_delta : forall (X : C),
    from (hf_tensor_iso X X) ∘ fmap[hf_functor] (scfa_delta (scfa X))
      ≈ scfa_delta (scfa (hf_functor X));

  hf_preserves_epsilon : forall (X : C),
    from hf_unit_iso ∘ fmap[hf_functor] (scfa_epsilon (scfa X))
      ≈ scfa_epsilon (scfa (hf_functor X))
}.

End HypergraphFunctor.

Arguments HypergraphFunctor {C SC} HG_C {D SD} HG_D.
Arguments hf_functor {C SC HG_C D SD HG_D} _.
Arguments hf_unit_iso {C SC HG_C D SD HG_D} _.
Arguments hf_tensor_iso {C SC HG_C D SD HG_D} _ _ _.
Arguments hf_preserves_mu {C SC HG_C D SD HG_D} _ _.
Arguments hf_preserves_eta {C SC HG_C D SD HG_D} _ _.
Arguments hf_preserves_delta {C SC HG_C D SD HG_D} _ _.
Arguments hf_preserves_epsilon {C SC HG_C D SD HG_D} _ _.

(** ** The identity hypergraph functor

    For any hypergraph category [(C, HG_C)], the identity functor
    [Id C : C ⟶ C] is canonically a hypergraph functor with
    [hf_unit_iso := iso_id] and [hf_tensor_iso X Y := iso_id].

    All four preservation equations follow from [fmap[Id] f = f] (the
    definitional equation of the identity functor), combined with
    [iso_id]'s components reducing to [id] under composition. *)

Section IdHypergraphFunctor.

Context {C : Category}.
Context `{SC : @SymmetricMonoidal C}.
Context `{HG_C : @Hypergraph C SC}.

Program Definition Id_HypergraphFunctor : HypergraphFunctor HG_C HG_C := {|
  hf_functor := Id[C] ;
  hf_unit_iso := iso_id ;
  hf_tensor_iso := fun X Y => iso_id
|}.

End IdHypergraphFunctor.

(** ** Discussion: the BlackBox / forget-decoration use case

    The forgetful "drop the decoration" functor from [DecoratedCospanCat F]
    to [CospanCat C] is a hypergraph functor: it acts as the identity on
    objects, projects out the cospan part of every morphism, and the SCFA
    on a cospan-category object is given by the [Cospan_Hypergraph]
    instance — which by definition is the SCFA the forgetful functor
    preserves on the nose.

    Fully packaging [forget_decoration] as a [HypergraphFunctor] requires
    [DecoratedCospanCat F] to be a [Category] record (the
    [Construction/DecoratedCospan.v] module exports the API, the [Setoid],
    identity, and composition; the full [Category] obligations are
    discharged at the cospan level by [Construction/Cospan/Category.v]
    and at the decoration level by the lax-monoidal functor coherences).

    See [Construction/Cospan/BlackBox.v] for the cospan-equivalence
    well-definedness lemmas that this record-form encapsulates. *)

(** ** Composition of hypergraph functors

    [HypergraphFunctor (HG_B, HG_C) -> HypergraphFunctor (HG_C, HG_D) ->
       HypergraphFunctor (HG_B, HG_D)]: composing the underlying functors,
    pairing the comparison iso's via [iso_compose] interleaved with
    [fmap]-transport, and combining the preservation equations.

    The composition law is mechanical but volumetric (each comparison
    iso composes through one [fmap], each preservation equation is the
    sum of the two component preservations).  We leave the explicit
    composition data to downstream sites that genuinely need it
    (the present library's main BlackBox use case only requires the
    identity instance and the literature pattern). *)
