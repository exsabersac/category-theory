Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Braided.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Structure.Monoidal.HypergraphFunctor.

Generalizable All Variables.

(*
   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半结构、函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section HypergraphBridge.

Context {C : Category}.
Context `{SC : @SymmetricMonoidal C}.
Context `{HG_C : @Hypergraph C SC}.

Context {D : Category}.
Context `{SD : @SymmetricMonoidal D}.
Context `{HG_D : @Hypergraph D SD}.

Context {F : C ⟶ D}.

(* Over the symmetric bases SC and SD this hypothesis is precisely
   [SymmetricMonoidalFunctor F]. *)
Context `{S : @BraidedMonoidalFunctor C D _ _ F}.

Program Definition SymmetricMonoidalFunctor_HypergraphFunctor
  (preserves_mu : ∀ X : C,
     fmap[F] (scfa_mu (scfa X)) ∘ to ap_iso ≈ scfa_mu (scfa (F X)))
  (preserves_eta : ∀ X : C,
     fmap[F] (scfa_eta (scfa X)) ∘ to pure_iso ≈ scfa_eta (scfa (F X)))
  (preserves_delta : ∀ X : C,
     from ap_iso ∘ fmap[F] (scfa_delta (scfa X)) ≈ scfa_delta (scfa (F X)))
  (preserves_epsilon : ∀ X : C,
     from pure_iso ∘ fmap[F] (scfa_epsilon (scfa X))
       ≈ scfa_epsilon (scfa (F X))) :
  HypergraphFunctor HG_C HG_D := {|
  hf_functor := F;
  hf_unit_iso := @pure_iso C D _ _ F _;
  hf_tensor_iso := fun X Y => @ap_iso C D _ _ F _ X Y
|}.

End HypergraphBridge.
