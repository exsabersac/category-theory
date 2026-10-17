Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** Profunctors and representable profunctors. *)

(* nLab: https://ncatlab.org/nlab/show/profunctor
   Wikipedia: https://en.wikipedia.org/wiki/Profunctor

   从 C 到 D 的双函子 (profunctor)（也称 distributor 或 bimodule，写作 C ⇸ D）是函子

     C^op ∏ D ⟶ Sets,

   在第一变元反变、第二变元共变。它把对 (c, d) 送到「异态射」的 setoid P(c, d)，
   携带 C 的左作用与 D 的右作用（经复合）。因此处 hom 集是 setoid，双函子落在 setoid
   范畴 Sets。

   依本开发的绑定宇宙纪律，双函子保持为按对对象：C ⇸ D 的双函子是函子范畴
   [C^op ∏ D, Sets]（Instance/Fun.v）的对象，其态射是自然变换，对象等价 Prof_Setoid
   是自然同构（Functor_Setoid，Theory/Functor.v）。我们从不组装「所有范畴之间所有双函子」
   的单一范畴——那会抬高宇宙层级——故轻量双范畴式复合与连贯作为这些按对函子范畴中的
   引理存在（Construction/Profunctor 模块）。 *)

(*
   关于profunctors的来源与用途

   nLab: https://ncatlab.org/nlab/show/profunctor
   Paper: Bénabou, "Les distributeurs", Institut de Mathématique Pure
   Paper: Lawvere, "Metric Spaces, Generalized Logic, and Closed

   本节说明函子、profunctor、Lawvere 理论相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Profunctor (C D : Category) := (C^op ∏ D) ⟶ Sets.

Notation "C ⇸ D" := (Profunctor C D)
  (at level 90, right associativity) : category_scope.

(*
   本节说明函子、hom、profunctor相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Id_Profunctor (C : Category) : C ⇸ C := Hom C.

(*
   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Repr_left {C D : Category} (F : C ⟶ D) : C ⇸ D :=
  Hom D ◯ (F^op ∏⟶ (@Id D)).

Definition Repr_right {C D : Category} (U : D ⟶ C) : C ⇸ D :=
  Hom C ◯ ((@Id C)^op ∏⟶ U).

(*
   本节说明函子、等价、profunctor相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Prof_Setoid (C D : Category) : Setoid (C ⇸ D) :=
  @Functor_Setoid (C^op ∏ D) Sets.
