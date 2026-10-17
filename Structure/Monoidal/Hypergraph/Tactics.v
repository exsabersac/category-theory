Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.
Require Import Category.Theory.Algebra.CommutativeFrobenius.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Structure.Monoidal.Hypergraph.Spider.

Generalizable All Variables.

(*
   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export] Hint Rewrite
  @spider_collapse
  @spider_mu_unit_left
  @spider_mu_unit_right
  @spider_delta_counit_left
  @spider_delta_counit_right
  @spider_mu_commutative
  @spider_delta_cocommutative
  : hypergraph.

(*
   本节说明 Tactics 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Ltac solve_hypergraph :=
  repeat (autorewrite with hypergraph in *;
          autorewrite with categories in *);
  try (auto with category_laws);
  try reflexivity.

