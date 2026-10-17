Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Export Category.Structure.Monoidal.Symmetric.

Generalizable All Variables.

Section CommutativeMonoidal.

Context {C : Category}.
Context `{@SymmetricMonoidal C}.

(** Commutative monoidal category (self-braiding triviality). *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Symmetric_monoidal_category

   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class CommutativeMonoidal := {
  (* Self-braiding is trivial: β_{x,x} ≈ 1_{x ⨂ x} for every object x. *)
  commutative {x} : @braid _ _ x x ≈ id
}.

End CommutativeMonoidal.
