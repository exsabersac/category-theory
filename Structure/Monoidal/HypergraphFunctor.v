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

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record HypergraphFunctor : Type := {
  hf_functor :> C ⟶ D;

  (** Comparison isomorphisms (the lax-monoidal data on [hf_functor],
      packaged here since [Functor] does not record it). *)
  hf_unit_iso : @I D _ ≅ hf_functor (@I C _);
  hf_tensor_iso : forall (X Y : C),
    (hf_functor X ⨂ hf_functor Y)%object ≅ hf_functor (X ⨂ Y)%object;

  (*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

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

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

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

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
