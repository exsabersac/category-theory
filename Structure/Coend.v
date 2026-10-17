Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Wedge.
Require Import Category.Structure.End.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Coend

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:  https://ncatlab.org/nlab/show/coend
   Book:  Loregian, "(Co)end Calculus", London Math. Soc. Lecture Note
   Paper: Yoneda, "On Ext and exact sequences", J. Fac. Sci. Univ. Tokyo
   Book:  Mac Lane, "Categories for the Working Mathematician", Springer
   Paper: Day, "On closed categories of functors", Midwest Category

   本节说明函子、（余）极限、（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Coend.

Context {C : Category}.
Context {D : Category}.
Context {F : C^op ∏ C ⟶ D}.

(** The coend 对象 `∫^c F(c,c)` `D`: apex underlying end
 wedge, read 对象 `D` (对象 `D^op` 对象 `D`). （已译） *)
Definition coend_obj (E : Coend F) : D :=
  @Wedge_to_obj (C^op) (D^op) (F^op) (@end_wedge (C^op) (D^op) (F^op) E).

(** 本节：The injection `coend_inj_x : F (x, x) ~> coend_obj`: underlying wedge
 leg `wedge_obj ~{D^op}~> F^op (x, x)`, read reversed `D`. （已译） *)
Definition coend_inj (E : Coend F) {x : C} :
  F (x, x) ~{D}~> coend_obj E :=
  @wedge_map (C^op) (D^op) (F^op) (@end_wedge (C^op) (D^op) (F^op) E) x.

(*
   本节说明（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma coend_cowedge (E : Coend F) {x y : C} (f : x ~{C}~> y) :
  @coend_inj E x ∘ bimap[F] (op f) id ≈ @coend_inj E y ∘ bimap[F] id f.
Proof.
  symmetry.
  exact (@ump_wedges (C^op) (D^op) (F^op)
           (@end_wedge (C^op) (D^op) (F^op) E) y x (op f)).
Qed.

(*
   本节说明（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Cowedge_cond (w : D) (i : ∀ x : C, F (x, x) ~{D}~> w) : Type :=
  ∀ (x y : C) (f : x ~{C}~> y),
    i x ∘ bimap[F] (op f) id ≈ i y ∘ bimap[F] id f.

(*
   本节说明（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition covariant_cowedge (w : D)
  (i : ∀ x : C, F (x, x) ~{D}~> w) (cond : Cowedge_cond w i) :
  @Wedge (C^op) (D^op) (F^op).
Proof.
  unshelve refine (@Build_Wedge (C^op) (D^op) (F^op) w (fun x => i x) _).
  intros x y f.
  symmetry.
  exact (cond y x f).
Defined.

(*
   本节说明（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma coend_ump (E : Coend F)
  (w : D) (i : ∀ x : C, F (x, x) ~{D}~> w) (cond : Cowedge_cond w i) :
  ∃! u : coend_obj E ~{D}~> w, ∀ x : C, u ∘ coend_inj E ≈ i x.
Proof.
  exact (@ump_ends (C^op) (D^op) (F^op) E (covariant_cowedge w i cond)).
Qed.

(** The mediating morphism out of a coend into any cowedge. *)
Definition coend_med (E : Coend F) (w : D)
  (i : ∀ x : C, F (x, x) ~{D}~> w) (cond : Cowedge_cond w i) :
  coend_obj E ~{D}~> w :=
  unique_obj (coend_ump E w i cond).

(** 本节：The mediator recovers each leg target cowedge. （已译） *)
Lemma coend_med_inj (E : Coend F) (w : D)
  (i : ∀ x : C, F (x, x) ~{D}~> w) (cond : Cowedge_cond w i) (x : C) :
  coend_med E w i cond ∘ coend_inj E ≈ i x.
Proof.
  unfold coend_med.
  exact (unique_property (coend_ump E w i cond) x).
Qed.

(** Any 态射 factoring injections through same legs equals the
 mediator. （已译） *)
Lemma coend_med_unique (E : Coend F) (w : D)
  (i : ∀ x : C, F (x, x) ~{D}~> w) (cond : Cowedge_cond w i)
  (v : coend_obj E ~{D}~> w) :
  (∀ x : C, v ∘ coend_inj E ≈ i x) -> coend_med E w i cond ≈ v.
Proof.
  intro Hv.
  unfold coend_med.
  exact (uniqueness (coend_ump E w i cond) v Hv).
Qed.

(** 本节：Two mediators out coend agree every injection equal.
 This lets one prove `u ≈ v` without exhibiting `coend_med` explicitly. （已译） *)
Lemma coend_med_eq (E : Coend F) (w : D)
  (i : ∀ x : C, F (x, x) ~{D}~> w) (cond : Cowedge_cond w i)
  (u v : coend_obj E ~{D}~> w) :
  (∀ x : C, u ∘ coend_inj E ≈ i x) ->
  (∀ x : C, v ∘ coend_inj E ≈ i x) -> u ≈ v.
Proof.
  intros Hu Hv.
  transitivity (coend_med E w i cond).
  - symmetry.
    now apply coend_med_unique.
  - now apply coend_med_unique.
Qed.

(*
   本节说明（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Build_Coend (w : D)
  (i : ∀ x : C, F (x, x) ~{D}~> w) (cond : Cowedge_cond w i)
  (ump : ∀ (w' : D) (i' : ∀ x : C, F (x, x) ~{D}~> w')
           (cond' : Cowedge_cond w' i'),
           ∃! u : w ~{D}~> w', ∀ x : C, u ∘ i x ≈ i' x) :
  Coend F.
Proof.
  unshelve refine
    (@Build_End (C^op) (D^op) (F^op) (covariant_cowedge w i cond) _).
  intros W.
  refine (ump (@Wedge_to_obj (C^op) (D^op) (F^op) W)
              (fun x => @wedge_map (C^op) (D^op) (F^op) W x)
              (fun x y f => _)).
  symmetry.
  exact (@ump_wedges (C^op) (D^op) (F^op) W y x (op f)).
Defined.

End Coend.

Arguments coend_obj {C D F} E.
Arguments coend_inj {C D F} E {x}.
Arguments Cowedge_cond {C D} F w i.
Arguments coend_cowedge {C D F} E {x y} f.
Arguments coend_ump {C D F} E w i cond.
Arguments coend_med {C D F} E w i cond.
Arguments Build_Coend {C D F} w i cond ump.
