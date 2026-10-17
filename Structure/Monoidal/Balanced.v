Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Export Category.Structure.Monoidal.Braided.

Generalizable All Variables.

Section BalancedMonoidal.

Context {C : Category}.

(** Balanced monoidal category. *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Ribbon_category

   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class BalancedMonoidal := {
  balanced_is_braided : @BraidedMonoidal C;

  (* The twist theta : x ≅ x, a natural automorphism of the identity. *)
  twist {x} : x ≅ x;
  twist_natural : natural (@twist);

  (* Unit condition theta_I = id, in both isomorphism directions. *)
  balanced_to   : to   (@twist I) ≈ id;
  balanced_from : from (@twist I) ≈ id;

  (* Twist/braiding coherence: theta on x ⊗ y is the double braiding wrapping
     theta ⊗ theta (naturality-shifted form; see the header). *)
  balanced_to_commutes {x y} :
    braid ∘ twist ⨂ twist ∘ braid
      << x ⨂ y ~~> x ⨂ y >>
    twist;

  (* The same coherence for the inverse twist theta⁻¹. *)
  balanced_from_commutes {x y} :
    braid ∘ twist⁻¹ ⨂ twist⁻¹ ∘ braid
      << x ⨂ y ~~> x ⨂ y >>
    twist⁻¹;
}.
#[export] Existing Instance balanced_is_braided.

Coercion balanced_is_braided : BalancedMonoidal >-> BraidedMonoidal.

End BalancedMonoidal.
