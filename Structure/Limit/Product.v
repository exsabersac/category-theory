Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Discrete.

Generalizable All Variables.

(** * Indexed products as limits of discrete diagrams *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)

   本文件给出积（分量）构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The elementary universal property of an indexed product: the family [proj]
   of projections is universal, so every competing family [pi] factors
   uniquely across it.  This mirrors the [IsEqualizer] record of
   [Structure/Equalizer/Fork.v]. *)
Record IsIndexedProduct {C : Category} {A : Type} (f : A → C)
  (p : C) (proj : ∀ a : A, p ~> f a) := {
  (* universal property: every family [pi] into the [f a] factors uniquely
     through the projections *)
  iprod_desc {c : C} (pi : ∀ a, c ~> f a) :
    ∃! u : c ~> p, ∀ a, proj a ∘ u ≈ pi a
}.

Arguments iprod_desc {_ _ _ _ _} _ {_} _.

(** ** From a plain family to a cone over the discrete diagram *)

(* Cone coherence over the discrete diagram is vacuous: the only morphisms of
   [DiscreteCat A] are equality witnesses, and pushing a leg along [fmap] of
   an equality proof recovers the leg at the (necessarily equal) codomain.
   This statement is definitionally the [cone_coherence] field of an [ACone]
   over [DiscreteCat_Functor f]. *)
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

(** ** Reading a limit of the discrete diagram as an indexed product *)

(* The product object: the apex of the limit cone. *)
Definition iprod {C : Category} {A : Type} (f : A → C)
  (L : Limit (DiscreteCat_Functor f)) : C :=
  vertex_obj[L].

(* The projections: the limit legs, one for each index. *)
Definition iprod_proj {C : Category} {A : Type} (f : A → C)
  (L : Limit (DiscreteCat_Functor f)) (a : A) : iprod f L ~> f a :=
  limit_leg (limit_is_alimit L) a.

(* The universal property: every competing family [pi] factors uniquely
   through the projections, by mediating into the limit from the cone the
   family induces. *)
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
