Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Instance.Discrete.

Generalizable All Variables.

(* * * Indexed coproducts, indexed products opposite 范畴 （已译） *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Coproduct

   本文件给出余积实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition IsIndexedCoproduct {C : Category} {A : Type} (f : A → C)
  (p : C) (inj : ∀ a : A, f a ~> p) : Type :=
  @IsIndexedProduct (C^op) A f p inj.

Definition icoprod_desc {C : Category} {A : Type} {f : A → C} {p : C}
  {inj : ∀ a : A, f a ~> p} (H : IsIndexedCoproduct f p inj)
  {c : C} (iota : ∀ a : A, f a ~> c) :
  ∃! u : p ~> c, ∀ a : A, u ∘ inj a ≈ iota a :=
  @iprod_desc (C^op) A f p inj H c iota.

Definition Build_IsIndexedCoproduct {C : Category} {A : Type} (f : A → C)
  (p : C) (inj : ∀ a : A, f a ~> p)
  (desc : ∀ (c : C) (iota : ∀ a : A, f a ~> c),
            ∃! u : p ~> c, ∀ a : A, u ∘ inj a ≈ iota a) :
  IsIndexedCoproduct f p inj :=
  @Build_IsIndexedProduct (C^op) A f p inj desc.

Definition icoprod {C : Category} {A : Type} (f : A → C)
  (L : Limit (@DiscreteCat_Functor A (C^op) f)) : C :=
  @iprod (C^op) A f L.

Definition icoprod_inj {C : Category} {A : Type} (f : A → C)
  (L : Limit (@DiscreteCat_Functor A (C^op) f)) (a : A) : f a ~> icoprod f L :=
  @iprod_proj (C^op) A f L a.

Definition icoprod_ump {C : Category} {A : Type} (f : A → C)
  (L : Limit (@DiscreteCat_Functor A (C^op) f))
  (c : C) (iota : ∀ a : A, f a ~> c) :
  ∃! u : icoprod f L ~> c, ∀ a : A, u ∘ icoprod_inj f L a ≈ iota a :=
  @iprod_ump (C^op) A f L c iota.

Definition colimit_is_indexed_coproduct {C : Category} {A : Type} (f : A → C)
  (L : Limit (@DiscreteCat_Functor A (C^op) f)) :
  IsIndexedCoproduct f (icoprod f L) (icoprod_inj f L) :=
  @limit_is_indexed_product (C^op) A f L.

Definition HasIndexedCoproducts (C : Category) : Type :=
  @HasIndexedProducts (C^op).

Existing Class HasIndexedCoproducts.

Definition Build_HasIndexedCoproducts {C : Category}
  (cobj : ∀ A : Type, (A → C) → C)
  (cinj : ∀ (A : Type) (f : A → C) (a : A), f a ~> cobj A f)
  (cump : ∀ (A : Type) (f : A → C),
            IsIndexedCoproduct f (cobj A f) (cinj A f)) :
  HasIndexedCoproducts C :=
  @Build_HasIndexedProducts (C^op) cobj cinj cump.

Section IndexedCoproductAPI.

Context {C : Category}.
Context {H : HasIndexedCoproducts C}.

Definition indexed_coproduct {A : Type} (f : A → C) : C :=
  @indexed_product (C^op) H A f.

Definition indexed_coproduct_inj {A : Type} (f : A → C) (a : A) :
  f a ~> indexed_coproduct f :=
  @indexed_product_proj (C^op) H A f a.

Definition indexed_coproduct_ump {A : Type} (f : A → C) :
  IsIndexedCoproduct f (indexed_coproduct f) (indexed_coproduct_inj f) :=
  @indexed_product_ump (C^op) H A f.

End IndexedCoproductAPI.
