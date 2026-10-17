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
   Where profunctors 来源, and 用途

   本节说明相关定义、性质与动机。 nLab: https://ncatlab.org/nlab/show/profunctor Paper: Bénabou, "Les distributeurs", Institut de Mathématique Pure et Appliquée, Rapport 33, Univ. Cath. de Louvain (1973) Paper: Lawvere, "Metric Spaces, Generalized Logic, Closed 范畴", Rend. Sem. Mat. Fis.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Profunctor (C D : Category) := (C^op ∏ D) ⟶ Sets.

Notation "C ⇸ D" := (Profunctor C D)
  (at level 90, right associativity) : category_scope.

(*
   本节说明相关定义、性质与动机。 The identity profunctor C is hom-bifunctor Hom C : C^op ∏ C ⟶ Sets of. 函子/Hom.v, viewed at profunctor type C ⇸ C. On (c, c') it is hom-set C(c, c'), C acting both sides 复合;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Id_Profunctor (C : Category) : C ⇸ C := Hom C.

(*
   可表 profunctors. A 函子 F : C ⟶ D presents the profunctor

   本节说明相关定义、性质与动机。 Repr_left F : C ⇸ D, (c, d) ↦ D(F c, d), covariantly 可表 left, while 函子 U : D ⟶ C presents Repr_right U : C ⇸ D, (c, d) ↦ C(c, U d), 可表 right. Both are built from hom-bifunctor target (resp. source) precomposed F (resp.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Repr_left {C D : Category} (F : C ⟶ D) : C ⇸ D :=
  Hom D ◯ (F^op ∏⟶ (@Id D)).

Definition Repr_right {C D : Category} (U : D ⟶ C) : C ⇸ D :=
  Hom C ◯ ((@Id C)^op ∏⟶ U).

(*
   The 等价 of profunctors C ⇸ D is inherited from the 函子 范畴

   本节说明相关定义、性质与动机。 [C^op ∏ D, Sets]: two profunctors are equivalent 当且仅当 they are naturally isomorphic (函子_Setoid).

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Prof_Setoid (C D : Category) : Setoid (C ⇸ D) :=
  @Functor_Setoid (C^op ∏ D) Sets.
