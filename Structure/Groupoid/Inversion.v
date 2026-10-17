Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Groupoid.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Structure.Groupoid.

Generalizable All Variables.

(** * A groupoid is isomorphic to its opposite *)

(*
   nLab:      https://ncatlab.org/nlab/show/opposite+category
   Book:      Riehl, "Category Theory in Context", Example 1.3.14, clauses

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:  https://ncatlab.org/nlab/show/opposite+category
   Book:  Riehl, "Category Theory in Context", Example 1.2.2(iii)

   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The functor *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Inversion {C : Category} (G : IsGroupoid C) : C ⟶ C^op := {|
  fobj := fun x => x;
  fmap := fun x y f => ginv G f
|}.
Next Obligation. now apply ginv_respects. Qed.
Next Obligation. now apply ginv_id. Qed.
Next Obligation. now apply ginv_comp. Qed.

(* The functor is the identity on objects, literally: [fobj] is [fun x => x],
   so this [=] is an equality of objects holding by [eq_refl], not a claim
   about morphisms. *)
Example Inversion_identity_on_objects {C : Category} (G : IsGroupoid C)
  (x : C) : fobj[Inversion G] x = x := eq_refl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Inversion_op {C : Category} (G : IsGroupoid C) : C^op ⟶ C :=
  Inversion (IsGroupoid_op G).

(** ** The isomorphism *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Inversion_iso {C : Category} (G : IsGroupoid C) :
  C ≅[StrictCat] C^op := {|
  to   := Inversion G;
  from := Inversion_op G
|}.
Next Obligation.
  exists (fun x => eq_refl).
  intros x y f.
  exact (ginv_involutive G f).
Qed.
Next Obligation.
  exists (fun x => eq_refl).
  intros x y f.
  exact (ginv_involutive G f).
Qed.

(*
   本节说明函子、等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Inversion_Cat_iso {C : Category} (G : IsGroupoid C) :
  C ≅[Cat] C^op :=
  fobj_iso StrictCat_to_Cat C (C^op) (Inversion_iso G).

(** ** Instances *)

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Deloop_Inversion_iso (G : GrpObject) :
  Deloop G ≅[StrictCat] (Deloop G)^op :=
  Inversion_iso (Deloop_IsGroupoid G).

(*
   本节说明 Inversion 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Bool_Inversion_iso :
  Deloop Bool_Xor_Grp ≅[StrictCat] (Deloop Bool_Xor_Grp)^op :=
  Deloop_Inversion_iso Bool_Xor_Grp.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Z3_Inversion_iso :
  Deloop Z3_Grp ≅[StrictCat] (Deloop Z3_Grp)^op :=
  Deloop_Inversion_iso Z3_Grp.

(* The morphism map really moves the arrow [Z3_1].  Both [=]s are Leibniz
   equality on [Z3], which is exactly the `≈` of that carrier setoid, so
   nothing weaker is being claimed. *)
Example Z3_inversion_nontrivial :
  @fmap _ _ (Inversion deloop_Z3_groupoid) ttt ttt Z3_1 = Z3_2 := eq_refl.

Lemma Z3_inversion_not_identity :
  @fmap _ _ (Inversion deloop_Z3_groupoid) ttt ttt Z3_1 <> Z3_1.
Proof. discriminate. Qed.

(*
   本节说明 Inversion 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition core_Inversion_iso (C : Category) :
  Groupoid C ≅[StrictCat] (Groupoid C)^op :=
  Inversion_iso (core_is_groupoid C).
