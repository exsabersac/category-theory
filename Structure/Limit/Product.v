Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Discrete.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)

   本文件给出积（分量）构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record IsIndexedProduct {C : Category} {A : Type} (f : A → C)
  (p : C) (proj : ∀ a : A, p ~> f a) := {
  (* 普遍性质: every family [pi] 进入 [f a] factors uniquely
 through projections （已译） *)
  iprod_desc {c : C} (pi : ∀ a, c ~> f a) :
    ∃! u : c ~> p, ∀ a, proj a ∘ u ≈ pi a
}.

Arguments iprod_desc {_ _ _ _ _} _ {_} _.

(* 相关说明。 （已译） *)

(*
   本节说明 Product 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma family_cone_coherence {C : Category} {A : Type} (f : A → C)
  (c : C) (pi : ∀ a, c ~> f a) :
  ∀ (x y : DiscreteCat A) (e : x ~{DiscreteCat A}~> y),
    fmap[DiscreteCat_Functor f] e ∘ pi x ≈ pi y.
Proof.
  intros x y e.
  destruct e.                   (* the only case is [eq_refl]; then [y := x] *)
  simpl.                        (* [fmap] of [eq_refl] computes to [id] *)
  apply id_left.
Qed.

(* The cone over [DiscreteCat_Functor f] induced by a plain family of legs. *)
Definition family_cone {C : Category} {A : Type} (f : A → C)
  (c : C) (pi : ∀ a, c ~> f a) : Cone (DiscreteCat_Functor f).
Proof.
  unshelve econstructor.
  - exact c.                                  (* apex *)
  - unshelve econstructor.
    + exact pi.                               (* legs *)
    + exact (family_cone_coherence f c pi).   (* coherence, vacuous here *)
Defined.

(* 相关说明。 （已译） *)

(* The product 对象: apex limit cone. （已译） *)
Definition iprod {C : Category} {A : Type} (f : A → C)
  (L : Limit (DiscreteCat_Functor f)) : C :=
  vertex_obj[L].

(* 相关说明。 （已译） *)
Definition iprod_proj {C : Category} {A : Type} (f : A → C)
  (L : Limit (DiscreteCat_Functor f)) (a : A) : iprod f L ~> f a :=
  limit_leg (limit_is_alimit L) a.

(* The 普遍性质: every competing family [pi] factors uniquely
 through projections, mediating 进入 limit cone the
 family induces. （已译） *)
Definition iprod_ump {C : Category} {A : Type} (f : A → C)
  (L : Limit (DiscreteCat_Functor f))
  (c : C) (pi : ∀ a, c ~> f a) :
  ∃! u : c ~> iprod f L, ∀ a, iprod_proj f L a ∘ u ≈ pi a.
Proof.
  unshelve eapply Build_Unique.
  - exact (limit_med (limit_is_alimit L) (family_cone f c pi)).
  - intros a.
    exact (limit_med_commutes (limit_is_alimit L) (family_cone f c pi) a).
  - intros v Hv.
    exact (limit_med_unique (limit_is_alimit L) (family_cone f c pi) v Hv).
Defined.

(* The limit, packaged as an elementary indexed product at its apex. *)
Definition limit_is_indexed_product {C : Category} {A : Type} (f : A → C)
  (L : Limit (DiscreteCat_Functor f)) :
  IsIndexedProduct f (iprod f L) (iprod_proj f L) :=
  {| iprod_desc := fun c pi => iprod_ump f L c pi |}.

(* A category has all indexed products when every family [f : A → C] over an
   arbitrary index [Type] carries an elementary indexed product.  This is the
   indexed-product analogue of [HasEqualizers] in
   [Structure/Equalizer/Fork.v]. *)
Class HasIndexedProducts (C : Category) := {
  indexed_product {A : Type} (f : A → C) : C;
  indexed_product_proj {A : Type} (f : A → C) (a : A) :
    indexed_product f ~> f a;
  indexed_product_ump {A : Type} (f : A → C) :
    IsIndexedProduct f (indexed_product f) (indexed_product_proj f)
}.
