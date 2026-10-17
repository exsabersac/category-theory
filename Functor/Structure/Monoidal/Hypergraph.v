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

(* Structure/Monoidal/HypergraphFunctor.v formalizes a deliberately weakened
   version of Fong–Spivak's hypergraph functors: raw comparison isomorphisms
   plus the four SCFA-preservation equations, WITHOUT the monoidal, unitor or
   braid coherences (see the "Known scoping limitation" caveat there — the
   weakened record is NOT in general a symmetric monoidal functor).  The
   coherence-complete literature notion is exactly: a strong symmetric
   monoidal functor — [SymmetricMonoidalFunctor] of
   Functor/Structure/Monoidal/Braided.v — whose comparison isomorphisms
   preserve the SCFA generators.

   The bridge below packages any such functor as a [HypergraphFunctor], with
   [pure_iso] and [ap_iso] as the comparison isomorphisms.  Only this
   forgetful direction is sound; the converse is false by that file's own
   caveat, since the record does not carry the coherences needed to
   reconstitute a monoidal functor.

   Be clear about how little is happening here: this is constructor
   repackaging and nothing more.  The four preservation hypotheses are
   literally the record's four hf_preserves_* fields, and the
   [HypergraphFunctor] record has no field that could receive [braid_compat]
   (nor the monoidal coherences), so the braided hypothesis [S] contributes
   no checked content to the constructed value — the definition would
   typecheck verbatim against a bare [MonoidalFunctor].  It is nevertheless
   stated against the symmetric hypothesis to name the literature notion the
   forgetting starts from.  In particular this bridge does NOT close
   HypergraphFunctor.v's coherence gap: forgetting into the record loses the
   coherences irrecoverably, and every consumer of the record remains
   subject to the caveat there. *)

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
