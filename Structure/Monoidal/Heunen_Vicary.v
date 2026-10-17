Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Export Category.Structure.Monoidal.Relevance.
Require Export Category.Structure.Monoidal.Semicartesian.

Generalizable All Variables.

Section CartesianMonoidal.

Context {C : Category}.

(*
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_monoidal_category
   Wikipedia: "Cartesian monoidal categories have a number of special and

   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class CartesianMonoidal := {
  cartesian_is_relevance     : @RelevanceMonoidal C;
  cartesian_is_semicartesian : @SemicartesianMonoidal C _;

  (* Fox's coherence: copying then discarding one copy is the identity. These
     two laws are precisely what upgrades the relevance + semicartesian data to
     a genuine product (tensor = ×), per the nLab characterisation above. *)
  proj_left_diagonal  {x} : proj_left  ∘ diagonal ≈ id[x];
  proj_right_diagonal {x} : proj_right ∘ diagonal ≈ id[x];

  (* Unit/braiding coherence λ ∘ σ ≈ ρ and ρ ∘ σ ≈ λ at the unit. In a
     symmetric monoidal category these are derivable from Mac Lane's coherence
     theorem rather than minimal; they are kept as explicit fields here because
     this library's SymmetricMonoidal does not expose that derivation, and
     downstream proofs (e.g. Heunen_Vicary/Proofs.v, Group/Proofs.v) rewrite with
     them directly. *)
  unit_left_braid  {x} : unit_left  ∘ @braid _ _ x I ≈ unit_right;
  unit_right_braid {x} : unit_right ∘ @braid _ _ I x ≈ unit_left
}.
#[export] Existing Instance cartesian_is_semicartesian.
#[export] Existing Instance cartesian_is_relevance.

Coercion cartesian_is_relevance : CartesianMonoidal >-> RelevanceMonoidal.
Coercion cartesian_is_semicartesian : CartesianMonoidal >-> SemicartesianMonoidal.

End CartesianMonoidal.
