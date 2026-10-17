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
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.
Require Import Category.Theory.Algebra.CommutativeFrobenius.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.
Require Import Category.Construction.PROP.

Generalizable All Variables.

(*
 nLab:      https://ncatlab.org/nlab/show/PROP
 nLab:      https://ncatlab.org/nlab/show/hypergraph+category
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   本文件为测试：HypergraphPROPResolution。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Open Scope nat_scope.

Section HypergraphPROPResolutionTests.

Context (P : HypergraphPROP).

(** The "tensor wire" — the canonical 1-arity PROP-object. *)
Notation T := (@prop_of_nat P 1).

(** [T] is an object of [P]. *)
Definition test_obj_resolves : @obj P := T.

(** Identity morphisms at [T] type-check. *)
Definition test_id : T ~> T := id.

(** Composition is found via the Category resolution. *)
Definition test_compose (f g : T ~> T) : T ~> T := g ∘ f.

(** Equivalence is found between two morphisms of the same hom-set. *)
Definition test_equiv (f g : T ~> T) : Type := f ≈ g.

(** The SCFA on T is found via the Hypergraph instance, and its flat
    [scfa_*] projections work. *)
Definition test_scfa_mu      := scfa_mu      (scfa T).
Definition test_scfa_eta     := scfa_eta     (scfa T).
Definition test_scfa_delta   := scfa_delta   (scfa T).
Definition test_scfa_epsilon := scfa_epsilon (scfa T).

(*
   本节说明幺半结构、hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition test_scfa_eta_compose := compose test_scfa_epsilon test_scfa_eta.

(*
   本节说明 HypergraphPROPResolution 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition test_scfa_special_law : Type :=
  scfa_mu (scfa T) ∘ scfa_delta (scfa T) ≈ id[T].

End HypergraphPROPResolutionTests.

Close Scope nat_scope.

(*
   本节说明幺半结构、（余）极限、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
