Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Instance.Discrete.

Generalizable All Variables.

(* * * Powers copowers single 对象 （已译） *)

(*
   nLab:      https://ncatlab.org/nlab/show/copower
   Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)

   本文件给出极限相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** The elementary universal properties, at 常值 family （已译） *)

(* A power [b] index [J]: 对象 [p] family [ev] of
 evaluation maps universal among such families. Mac Lane's [b^J];
 Riehl's [A^I] [ev_i] projections. （已译） *)
Definition IsPower {C : Category} {J : Type} (b p : C)
  (ev : ∀ _ : J, p ~> b) : Type :=
  IsIndexedProduct (fun _ : J => b) p ev.

(* A copower of [b] by [J]: dually, an object with a universal family of
   injections.  Mac Lane's [J · b]; Riehl's [I · A]. *)
Definition IsCopower {C : Category} {J : Type} (b p : C)
  (inj : ∀ _ : J, b ~> p) : Type :=
  @IsPower (C^op) J b p inj.

Example IsPower_is_IsIndexedProduct {C : Category} {J : Type} (b p : C)
  (ev : ∀ _ : J, p ~> b) :
  IsPower b p ev = IsIndexedProduct (fun _ : J => b) p ev := eq_refl.

Example IsCopower_is_IsIndexedCoproduct {C : Category} {J : Type} (b p : C)
  (inj : ∀ _ : J, b ~> p) :
  IsCopower b p inj = IsIndexedCoproduct (fun _ : J => b) p inj := eq_refl.

(* The 普遍性质, read arrows [C]. The copower form is
 covariant: no [^op] appears statement. （已译） *)
Definition power_desc {C : Category} {J : Type} {b p : C}
  {ev : ∀ _ : J, p ~> b} (H : IsPower b p ev)
  {c : C} (pi : ∀ _ : J, c ~> b) :
  ∃! u : c ~> p, ∀ j : J, ev j ∘ u ≈ pi j :=
  @iprod_desc C J (fun _ : J => b) p ev H c pi.

Definition copower_desc {C : Category} {J : Type} {b p : C}
  {inj : ∀ _ : J, b ~> p} (H : IsCopower b p inj)
  {c : C} (iota : ∀ _ : J, b ~> c) :
  ∃! u : p ~> c, ∀ j : J, u ∘ inj j ≈ iota j :=
  @icoprod_desc C J (fun _ : J => b) p inj H c iota.

(* 相关说明。 （已译） *)
Definition Build_IsPower {C : Category} {J : Type} (b p : C)
  (ev : ∀ _ : J, p ~> b)
  (desc : ∀ (c : C) (pi : ∀ _ : J, c ~> b),
            ∃! u : c ~> p, ∀ j : J, ev j ∘ u ≈ pi j) :
  IsPower b p ev :=
  @Build_IsIndexedProduct C J (fun _ : J => b) p ev desc.

Definition Build_IsCopower {C : Category} {J : Type} (b p : C)
  (inj : ∀ _ : J, b ~> p)
  (desc : ∀ (c : C) (iota : ∀ _ : J, b ~> c),
            ∃! u : p ~> c, ∀ j : J, u ∘ inj j ≈ iota j) :
  IsCopower b p inj :=
  @Build_IsIndexedCoproduct C J (fun _ : J => b) p inj desc.

(* 相关说明。 （已译） *)

Definition power {C : Category} {HP : @HasIndexedProducts C}
  (J : Type) (b : C) : C :=
  indexed_product (fun _ : J => b).

Definition power_ev {C : Category} {HP : @HasIndexedProducts C}
  (J : Type) (b : C) (j : J) : power J b ~> b :=
  indexed_product_proj (fun _ : J => b) j.

Definition power_ump {C : Category} {HP : @HasIndexedProducts C}
  (J : Type) (b : C) : IsPower b (power J b) (power_ev J b) :=
  indexed_product_ump (fun _ : J => b).

Definition copower {C : Category} {HC : @HasIndexedCoproducts C}
  (J : Type) (b : C) : C :=
  @power (C^op) HC J b.

Definition copower_inj {C : Category} {HC : @HasIndexedCoproducts C}
  (J : Type) (b : C) (j : J) : b ~> copower J b :=
  @power_ev (C^op) HC J b j.

Definition copower_ump {C : Category} {HC : @HasIndexedCoproducts C}
  (J : Type) (b : C) : IsCopower b (copower J b) (copower_inj J b) :=
  @power_ump (C^op) HC J b.

(*
   本节说明伴随、（余）极限、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition power_of_limit {C : Category} {J : Type} (b : C)
  (L : Limit (DiscreteCat_Functor (fun _ : J => b))) : C :=
  iprod (fun _ : J => b) L.

Definition power_ev_of_limit {C : Category} {J : Type} (b : C)
  (L : Limit (DiscreteCat_Functor (fun _ : J => b))) (j : J) :
  power_of_limit b L ~> b :=
  iprod_proj (fun _ : J => b) L j.

Definition power_ump_of_limit {C : Category} {J : Type} (b : C)
  (L : Limit (DiscreteCat_Functor (fun _ : J => b)))
  (c : C) (pi : ∀ _ : J, c ~> b) :
  ∃! u : c ~> power_of_limit b L, ∀ j : J, power_ev_of_limit b L j ∘ u ≈ pi j :=
  iprod_ump (fun _ : J => b) L c pi.

Definition limit_is_power {C : Category} {J : Type} (b : C)
  (L : Limit (DiscreteCat_Functor (fun _ : J => b))) :
  IsPower b (power_of_limit b L) (power_ev_of_limit b L) :=
  limit_is_indexed_product (fun _ : J => b) L.

Definition copower_of_colimit {C : Category} {J : Type} (b : C)
  (L : Limit (@DiscreteCat_Functor J (C^op) (fun _ : J => b))) : C :=
  @power_of_limit (C^op) J b L.

Definition copower_inj_of_colimit {C : Category} {J : Type} (b : C)
  (L : Limit (@DiscreteCat_Functor J (C^op) (fun _ : J => b))) (j : J) :
  b ~> copower_of_colimit b L :=
  @power_ev_of_limit (C^op) J b L j.

Definition copower_ump_of_colimit {C : Category} {J : Type} (b : C)
  (L : Limit (@DiscreteCat_Functor J (C^op) (fun _ : J => b)))
  (c : C) (iota : ∀ _ : J, b ~> c) :
  ∃! u : copower_of_colimit b L ~> c,
    ∀ j : J, u ∘ copower_inj_of_colimit b L j ≈ iota j :=
  @power_ump_of_limit (C^op) J b L c iota.

Definition colimit_is_copower {C : Category} {J : Type} (b : C)
  (L : Limit (@DiscreteCat_Functor J (C^op) (fun _ : J => b))) :
  IsCopower b (copower_of_colimit b L) (copower_inj_of_colimit b L) :=
  @limit_is_power (C^op) J b L.

(** ** Notation, opt-in *)

Declare Scope power_scope.
Delimit Scope power_scope with power.

Notation "J ⋔ b" := (power J b)
  (at level 30, right associativity) : power_scope.
Notation "J · b" := (copower J b)
  (at level 30, right associativity) : power_scope.
