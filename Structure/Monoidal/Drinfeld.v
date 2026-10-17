Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Braided.Proofs.

Generalizable All Variables.

(*
    nLab: https://ncatlab.org/nlab/show/Drinfeld+center
    Wikipedia: https://en.wikipedia.org/wiki/Center_(category_theory)

   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Drinfeld.

Context {C : Category}.
Context `{M : @Monoidal C}.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record HalfBraiding (z : C) := {
  half_braid (x : C) : z ⨂ x ≅ x ⨂ z;

  half_braid_natural {x y} (f : x ~> y) :
    to (half_braid y) ∘ (id[z] ⨂ f)
      << z ⨂ x ~~> y ⨂ z >>
    (f ⨂ id[z]) ∘ to (half_braid x);

  half_braid_tensor {x y} :
    to (half_braid (x ⨂ y))
      << z ⨂ (x ⨂ y) ~~> (x ⨂ y) ⨂ z >>
    tensor_assoc⁻¹
      ∘ (id[x] ⨂ to (half_braid y))
      ∘ to tensor_assoc
      ∘ (to (half_braid x) ⨂ id[y])
      ∘ tensor_assoc⁻¹
}.

Arguments half_braid {z} _ _.
Arguments half_braid_natural {z} _ {x y} _.
Arguments half_braid_tensor {z} _ {x y}.

(** A small helper: the tensor of two isomorphisms is an isomorphism. *)

Program Definition iso_bimap {a b c d : C} (i : a ≅ b) (j : c ≅ d) :
  (a ⨂ c) ≅ (b ⨂ d) := {|
  to   := to i ⨂ to j;
  from := from i ⨂ from j
|}.
Next Obligation.
  rewrite <- bimap_comp.
  rewrite !iso_to_from.
  now rewrite bimap_id_id.
Qed.
Next Obligation.
  rewrite <- bimap_comp.
  rewrite !iso_from_to.
  now rewrite bimap_id_id.
Qed.

(** ** The intertwining condition on morphisms

    A base morphism [f : z ~> z'] is a morphism of half-braided objects when
    it commutes with the two half-braidings against every object [x]. *)

Definition half_braiding_morphism {z z' : C}
           (σ : HalfBraiding z) (σ' : HalfBraiding z') (f : z ~> z') : Type :=
  ∀ x, to (half_braid σ' x) ∘ (f ⨂ id[x])
         << z ⨂ x ~~> x ⨂ z' >>
       (id[x] ⨂ f) ∘ to (half_braid σ x).

Lemma half_braiding_morphism_id {z : C} (σ : HalfBraiding z) :
  half_braiding_morphism σ σ (id[z]).
Proof.
  intro x.
  rewrite !bimap_id_id.
  rewrite id_left, id_right.
  reflexivity.
Qed.

Lemma half_braiding_morphism_comp {z z' z'' : C}
      {σ : HalfBraiding z} {σ' : HalfBraiding z'} {σ'' : HalfBraiding z''}
      {f : z' ~> z''} {g : z ~> z'} :
  half_braiding_morphism σ' σ'' f →
  half_braiding_morphism σ σ' g →
  half_braiding_morphism σ σ'' (f ∘ g).
Proof.
  intros pf pg x.
  rewrite bimap_comp_id_right.
  rewrite comp_assoc.
  rewrite pf.
  rewrite <- comp_assoc.
  rewrite pg.
  rewrite comp_assoc.
  rewrite bimap_comp_id_left.
  reflexivity.
Qed.

(** ** The Drinfeld centre as a category *)

Program Definition Drinfeld : Category := {|
  obj     := { z : C & HalfBraiding z };
  hom     := fun a b => { f : `1 a ~> `1 b
                            & half_braiding_morphism (`2 a) (`2 b) f };
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id      := fun a => (id[`1 a]; half_braiding_morphism_id (`2 a));
  compose := fun a b c f g =>
               (`1 f ∘ `1 g; half_braiding_morphism_comp (`2 f) (`2 g))
|}.

(** The forgetful functor to the base category, dropping the half-braiding. *)

Program Definition Drinfeld_Forget : Drinfeld ⟶ C := {|
  fobj := fun a => `1 a;
  fmap := fun _ _ f => `1 f
|}.

(** ** The half-braiding on the unit object

    On [I] the half-braiding is forced by the unitors: [I ⨂ x ≅ x ≅ x ⨂ I],
    i.e. [unit_right⁻¹ ∘ unit_left]. *)

Definition hb_unit_iso (x : C) : (I ⨂ x) ≅ (x ⨂ I) :=
  iso_compose (iso_sym (@unit_right C M x)) (@unit_left C M x).

Lemma hb_unit_to (x : C) :
  to (hb_unit_iso x) ≈ unit_right⁻¹ ∘ unit_left.
Proof. reflexivity. Qed.

Lemma hb_unit_natural {x y} (f : x ~> y) :
  to (hb_unit_iso y) ∘ (id[I] ⨂ f)
    ≈ (f ⨂ id[I]) ∘ to (hb_unit_iso x).
Proof.
  rewrite !hb_unit_to.
  rewrite comp_assoc.
  rewrite from_unit_right_natural.
  rewrite <- !comp_assoc.
  rewrite <- to_unit_left_natural.
  reflexivity.
Qed.

(** Triangle coherence in cons form, and the inverse right-unitor along the
    associator, which together collapse the unit hexagon. *)

Lemma tri_cons {a b w} (k : w ~> ((a ⨂ I) ⨂ b)%object) :
  (id[a] ⨂ unit_left) ∘ (to tensor_assoc ∘ k) ≈ (unit_right ⨂ id[b]) ∘ k.
Proof.
  rewrite comp_assoc.
  rewrite <- triangle_identity.
  reflexivity.
Qed.

Lemma tri_rho_inv {a b} :
  tensor_assoc⁻¹ ∘ (id[a] ⨂ (@unit_right C M b)⁻¹)
    ≈ (@unit_right C M (a ⨂ b))⁻¹.
Proof.
  apply (iso_to_monic (@unit_right C M (a ⨂ b))).
  rewrite (iso_to_from (@unit_right C M (a ⨂ b))).
  rewrite bimap_triangle_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to tensor_assoc)).
  rewrite iso_to_from, id_left.
  rewrite <- bimap_comp.
  rewrite iso_to_from, id_left, bimap_id_id.
  reflexivity.
Qed.

Lemma hb_unit_hexagon {x y} :
  to (hb_unit_iso (x ⨂ y))
    ≈ tensor_assoc⁻¹
        ∘ (id[x] ⨂ to (hb_unit_iso y))
        ∘ to tensor_assoc
        ∘ (to (hb_unit_iso x) ⨂ id[y])
        ∘ tensor_assoc⁻¹.
Proof.
  rewrite !hb_unit_to.
  rewrite bimap_comp_id_left, bimap_comp_id_right.
  rewrite <- !comp_assoc.
  (* collapse the right end (λx ⨂ id) ∘ α'  ==>  λ(x⨂y) *)
  rewrite <- bimap_triangle_left.
  (* middle triangle: (id ⨂ λy) ∘ (α ∘ ((ρ'x ⨂ id) ∘ λ(x⨂y))) *)
  rewrite tri_cons.
  (* cancel (ρx ⨂ id) ∘ (ρ'x ⨂ id) = id *)
  rewrite (comp_assoc (unit_right ⨂ id[y])).
  rewrite <- bimap_comp.
  rewrite iso_to_from, id_left, bimap_id_id, id_left.
  (* collapse the left end α'(x,y,I) ∘ (id ⨂ ρ'y) ==> ρ'(x⨂y) *)
  rewrite comp_assoc.
  rewrite tri_rho_inv.
  reflexivity.
Qed.

Definition hb_unit : HalfBraiding I := {|
  half_braid        := hb_unit_iso;
  half_braid_natural := @hb_unit_natural;
  half_braid_tensor  := @hb_unit_hexagon
|}.

(*
   本节说明 Drinfeld 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section HBTensor.

Context {z1 z2 : C}.
Context (σ1 : HalfBraiding z1) (σ2 : HalfBraiding z2).

Definition hb_tensor_iso (x : C) : ((z1 ⨂ z2) ⨂ x) ≅ (x ⨂ (z1 ⨂ z2)) :=
  iso_compose (@tensor_assoc C M x z1 z2)
    (iso_compose (iso_bimap (half_braid σ1 x) iso_id)
      (iso_compose (iso_sym (@tensor_assoc C M z1 x z2))
        (iso_compose (iso_bimap iso_id (half_braid σ2 x))
          (@tensor_assoc C M z1 z2 x)))).

Lemma hb_tensor_iso_to (x : C) :
  to (hb_tensor_iso x)
    ≈ to tensor_assoc
        ∘ ((to (half_braid σ1 x) ⨂ id[z2])
             ∘ (tensor_assoc⁻¹
                  ∘ ((id[z1] ⨂ to (half_braid σ2 x))
                       ∘ to tensor_assoc))).
Proof. reflexivity. Qed.

Lemma hb_tensor_natural {x y} (f : x ~> y) :
  to (hb_tensor_iso y) ∘ (id[(z1 ⨂ z2)%object] ⨂ f)
    ≈ (f ⨂ id[(z1 ⨂ z2)%object]) ∘ to (hb_tensor_iso x).
Proof.
  rewrite !hb_tensor_iso_to.
  rewrite <- !comp_assoc.
  (* Step 1: slide (id[z1⨂z2] ⨂ f) past the bottom associator α(z1,z2,·). *)
  spose (to_tensor_assoc_natural (id[z1]) (id[z2]) f) as S1.
  rewrite bimap_id_id in S1.
  rewrite <- S1; clear S1.
  (* Step 2: fuse under z1, apply σ2 naturality, split again. *)
  rewrite bimap_id_fuse_cons.
  rewrite (half_braid_natural σ2 f).
  rewrite bimap_id_split_cons.
  (* Step 3: slide (id[z1] ⨂ (f ⨂ id[z2])) past α(z1,·,z2)⁻¹. *)
  rewrite <- from_assoc_nat_cons.
  (* Step 4: fuse over z2, apply σ1 naturality, split again. *)
  rewrite bimap_fuse_cons.
  rewrite id_left.
  rewrite (half_braid_natural σ1 f).
  rewrite bimap_comp_id_right.
  rewrite <- comp_assoc.
  (* Step 5: slide ((f ⨂ id[z1]) ⨂ id[z2]) past the top associator α(·,z1,z2). *)
  rewrite <- to_assoc_nat_cons.
  rewrite bimap_id_id.
  reflexivity.
Qed.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Pentagon, solved for [(id ⨂ α') ∘ α] around a strand — the inverse of the
   inner-peel move. *)
Lemma P1 (u v p q : C) :
  (id[u] ⨂ (@tensor_assoc C M v p q)⁻¹) ∘ to (@tensor_assoc C M u v (p ⨂ q))
    ≈ to (@tensor_assoc C M u (v ⨂ p) q)
        ∘ ((to (@tensor_assoc C M u v p) ⨂ id[q])
             ∘ (@tensor_assoc C M (u ⨂ v) p q)⁻¹).
Proof.
  symmetry.
  rewrite pentagon_solved3_cons.
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

(* A five-associator loop around a strand collapses to the identity (inverse
   pentagon), and its cons form threading a continuation [k]. *)
Lemma assoc_loop (w x y v : C) :
  to (@tensor_assoc C M (w ⨂ x) y v)
    ∘ ((@tensor_assoc C M w x y)⁻¹ ⨂ id[v]
         ∘ ((@tensor_assoc C M w (x ⨂ y) v)⁻¹
              ∘ (id[w] ⨂ (@tensor_assoc C M x y v)⁻¹
                   ∘ to (@tensor_assoc C M w x (y ⨂ v))))) ≈ id.
Proof.
  transitivity (to (@tensor_assoc C M (w ⨂ x) y v)
                  ∘ (@tensor_assoc C M (w ⨂ x) y v)⁻¹).
  2: { rewrite iso_to_from; reflexivity. }
  f_equiv.
  rewrite !comp_assoc.
  rewrite inverse_pentagon_identity.
  rewrite <- comp_assoc.
  rewrite iso_from_to, id_right.
  reflexivity.
Qed.

Lemma assoc_loop_cons (w x y v u : C)
      (k : u ~> ((w ⨂ x) ⨂ (y ⨂ v))%object) :
  to (@tensor_assoc C M (w ⨂ x) y v)
    ∘ ((@tensor_assoc C M w x y)⁻¹ ⨂ id[v]
         ∘ ((@tensor_assoc C M w (x ⨂ y) v)⁻¹
              ∘ (id[w] ⨂ (@tensor_assoc C M x y v)⁻¹
                   ∘ (to (@tensor_assoc C M w x (y ⨂ v)) ∘ k)))) ≈ k.
Proof.
  rewrite (comp_assoc (id[w] ⨂ (@tensor_assoc C M x y v)⁻¹)).
  rewrite (comp_assoc (@tensor_assoc C M w (x ⨂ y) v)⁻¹).
  rewrite (comp_assoc ((@tensor_assoc C M w x y)⁻¹ ⨂ id[v])).
  rewrite (comp_assoc (to (@tensor_assoc C M (w ⨂ x) y v))).
  rewrite assoc_loop.
  rewrite id_left.
  reflexivity.
Qed.

(* [to i ∘ from i] cancellation in a single tensor slot, cons form. *)
Lemma bimap_id_tf_cons {h x y w : C} (i : x ≅ y) (kk : w ~> (h ⨂ y)%object) :
  (id[h] ⨂ to i) ∘ ((id[h] ⨂ i⁻¹) ∘ kk) ≈ kk.
Proof.
  rewrite comp_assoc, <- bimap_comp, iso_to_from, id_left, bimap_id_id, id_left.
  reflexivity.
Qed.

(*
   本节说明 Drinfeld 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma crux (a b : C) (P : z1 ⨂ a ~> a ⨂ z1) (S : z2 ⨂ b ~> b ⨂ z2)
      {u : C} (k : u ~> (((z1 ⨂ a) ⨂ z2) ⨂ b)%object) :
  to (@tensor_assoc C M a z1 (b ⨂ z2))
  ∘ (to (@tensor_assoc C M (a ⨂ z1) b z2)
     ∘ ((P ⨂ id[b]) ⨂ id[z2]
        ∘ ((@tensor_assoc C M z1 a b)⁻¹ ⨂ id[z2]
           ∘ ((@tensor_assoc C M z1 (a ⨂ b) z2)⁻¹
              ∘ (id[z1] ⨂ (@tensor_assoc C M a b z2)⁻¹
                 ∘ (id[z1] ⨂ (id[a] ⨂ S)
                    ∘ (to (@tensor_assoc C M z1 a (z2 ⨂ b))
                       ∘ (to (@tensor_assoc C M (z1 ⨂ a) z2 b) ∘ k))))))))
  ≈ id[a] ⨂ (id[z1] ⨂ S)
    ∘ (id[a] ⨂ to (@tensor_assoc C M z1 z2 b)
       ∘ (to (@tensor_assoc C M a (z1 ⨂ z2) b)
          ∘ (to (@tensor_assoc C M a z1 z2) ⨂ id[b]
             ∘ ((P ⨂ id[z2]) ⨂ id[b] ∘ k)))).
Proof.
  transitivity (to (@tensor_assoc C M a z1 (b ⨂ z2))
                  ∘ ((P ⨂ S)
                       ∘ (to (@tensor_assoc C M (z1 ⨂ a) z2 b) ∘ k))).
  - rewrite <- to_assoc_nat_id2_cons.
    rewrite <- to_assoc_nat_cons.
    rewrite assoc_loop_cons.
    rewrite bimap_id_id.
    rewrite bimap_fuse_cons.
    rewrite id_left, id_right.
    reflexivity.
  - symmetry.
    rewrite pentagon_solved3_cons.
    rewrite (bimap_id_tf_cons (@tensor_assoc C M z1 z2 b)).
    rewrite <- to_assoc_nat_cons.
    rewrite <- to_assoc_nat_id2_cons.
    rewrite bimap_id_id.
    rewrite bimap_fuse_cons.
    rewrite id_left, id_right.
    reflexivity.
Qed.

Lemma hb_tensor_hexagon {a b} :
  to (hb_tensor_iso (a ⨂ b))
    ≈ tensor_assoc⁻¹
        ∘ (id[a] ⨂ to (hb_tensor_iso b))
        ∘ to tensor_assoc
        ∘ (to (hb_tensor_iso a) ⨂ id[b])
        ∘ tensor_assoc⁻¹.
Proof.
  rewrite !hb_tensor_iso_to.
  rewrite (half_braid_tensor σ1), (half_braid_tensor σ2).
  rewrite !bimap_comp_id_right, !bimap_comp_id_left.
  rewrite <- !comp_assoc.
  (* Peel the outer associator scaffold (pentagon + associator naturality). *)
  rewrite pentagon_solved_cons.
  rewrite <- to_assoc_nat_cons.
  rewrite pentagon_solved3_cons.
  (* Peel the inner associator scaffold. *)
  rewrite P1.
  rewrite to_assoc_nat_cons.
  rewrite pentagon_solved2_cons.
  (* The remaining discrepancy is the independent-strand interchange. *)
  rewrite crux.
  reflexivity.
Qed.

Definition hb_tensor : HalfBraiding (z1 ⨂ z2) := {|
  half_braid        := hb_tensor_iso;
  half_braid_natural := @hb_tensor_natural;
  half_braid_tensor  := @hb_tensor_hexagon
|}.

End HBTensor.

(** The record-level unfolding of the tensor half-braiding. *)

Lemma hb_tensor_to {z1 z2} (σ1 : HalfBraiding z1) (σ2 : HalfBraiding z2)
      (x : C) :
  to (half_braid (hb_tensor σ1 σ2) x)
    ≈ to tensor_assoc
        ∘ ((to (half_braid σ1 x) ⨂ id[z2])
             ∘ (tensor_assoc⁻¹
                  ∘ ((id[z1] ⨂ to (half_braid σ2 x))
                       ∘ to tensor_assoc))).
Proof. exact (hb_tensor_iso_to σ1 σ2 x). Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma half_braiding_morphism_iso_from {z z' : C}
      (σ : HalfBraiding z) (σ' : HalfBraiding z') (i : z ≅ z') :
  half_braiding_morphism σ σ' (to i) →
  half_braiding_morphism σ' σ (from i).
Proof.
  intros H x.
  spose (H x) as Hx.
  symmetry.
  rewrite <- (id_right (bimap (id[x]) (from i) ∘ to (half_braid σ' x))).
  rewrite <- (bimap_cancel_right (iso_sym i)).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to (half_braid σ' x))).
  rewrite Hx.
  rewrite <- !comp_assoc.
  rewrite bimap_id_cancel_cons.
  reflexivity.
Qed.

Definition Drinfeld_lift_iso {A B : Drinfeld}
           (i : `1 A ≅ `1 B)
           (ci : half_braiding_morphism (`2 A) (`2 B) (to i)) : A ≅[Drinfeld] B :=
  @Build_Isomorphism Drinfeld A B
    (to i; ci)
    (from i; half_braiding_morphism_iso_from (`2 A) (`2 B) i ci)
    (iso_to_from i)
    (iso_from_to i).

(** ** Intertwining of the structural isomorphisms with the half-braidings *)

(* Splitting a [bimap] whose one component is a composite, in cons position. *)
Lemma bimap_split_right_cons {a b c d e w : C}
      (p : a ~> b) (u : c ~> d) (v : e ~> c) (k : w ~> (a ⨂ e)%object) :
  bimap p (u ∘ v) ∘ k ≈ bimap p u ∘ (bimap id[a] v ∘ k).
Proof.
  rewrite comp_assoc.
  rewrite <- bimap_comp.
  rewrite id_right.
  reflexivity.
Qed.

Lemma bimap_split_left_cons {a b c d e w : C}
      (u : c ~> d) (v : e ~> c) (p : a ~> b) (k : w ~> (e ⨂ a)%object) :
  bimap (u ∘ v) p ∘ k ≈ bimap u p ∘ (bimap v id[a] ∘ k).
Proof.
  rewrite comp_assoc.
  rewrite <- bimap_comp.
  rewrite id_right.
  reflexivity.
Qed.

Lemma hb_tensor_bimap_morphism
      {z1 z1' z2 z2' : C}
      {σ1 : HalfBraiding z1} {σ1' : HalfBraiding z1'}
      {σ2 : HalfBraiding z2} {σ2' : HalfBraiding z2'}
      {f : z1 ~> z1'} {g : z2 ~> z2'} :
  half_braiding_morphism σ1 σ1' f →
  half_braiding_morphism σ2 σ2' g →
  half_braiding_morphism (hb_tensor σ1 σ2) (hb_tensor σ1' σ2') (f ⨂ g).
Proof.
  intros pf pg x.
  rewrite !hb_tensor_to.
  rewrite <- !comp_assoc.
  (* Step 1: slide ((f ⨂ g) ⨂ id[x]) past the bottom associator. *)
  spose (to_tensor_assoc_natural f g (id[x])) as S1.
  rewrite <- S1; clear S1.
  (* Step 2: fuse under z1, apply σ2 intertwining (pg), split. *)
  rewrite bimap_fuse_cons, id_left, (pg x), bimap_split_right_cons.
  (* Step 3: slide (f ⨂ (id[x] ⨂ g)) past the inverse associator. *)
  rewrite <- from_assoc_nat_cons.
  (* Step 4: fuse over z2', apply σ1 intertwining (pf), split. *)
  rewrite bimap_fuse_cons, id_left, (pf x), bimap_split_left_cons.
  (* Step 5: slide ((id[x] ⨂ f) ⨂ g) past the top associator. *)
  rewrite <- to_assoc_nat_cons.
  reflexivity.
Qed.

(** The unit half-braiding read off its underlying record accessor, so the
    coherence rewrites below fire on [half_braid hb_unit] terms produced by
    [hb_tensor_to]. *)

Lemma hb_unit_field_to (x : C) :
  to (half_braid hb_unit x) ≈ unit_right⁻¹ ∘ unit_left.
Proof. exact (hb_unit_to x). Qed.

(*
   本节说明 Drinfeld 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma tri_left_cons {a b w} (k : w ~> (I ⨂ (a ⨂ b))%object) :
  (unit_left ⨂ id[b]) ∘ (tensor_assoc⁻¹ ∘ k) ≈ unit_left ∘ k.
Proof. rewrite comp_assoc, <- bimap_triangle_left; reflexivity. Qed.

Lemma tri_right_cons {a b w} (k : w ~> ((a ⨂ b) ⨂ I)%object) :
  (id[a] ⨂ unit_right) ∘ (to tensor_assoc ∘ k) ≈ unit_right ∘ k.
Proof. rewrite comp_assoc, <- bimap_triangle_right; reflexivity. Qed.

Lemma tri_right_inv_cons {a b w} (k : w ~> (a ⨂ (b ⨂ I))%object) :
  unit_right ∘ (tensor_assoc⁻¹ ∘ k) ≈ (id[a] ⨂ unit_right) ∘ k.
Proof. rewrite comp_assoc, <- triangle_identity_right; reflexivity. Qed.

Lemma ul_nat_cons {a b w} (g : a ~> b) (k : w ~> (I ⨂ a)%object) :
  unit_left ∘ ((id[I] ⨂ g) ∘ k) ≈ g ∘ (unit_left ∘ k).
Proof. rewrite comp_assoc, <- to_unit_left_natural, <- comp_assoc; reflexivity. Qed.

Lemma ur_nat_cons {a b w} (g : a ~> b) (k : w ~> (a ⨂ I)%object) :
  unit_right ∘ ((g ⨂ id[I]) ∘ k) ≈ g ∘ (unit_right ∘ k).
Proof. rewrite comp_assoc, <- to_unit_right_natural, <- comp_assoc; reflexivity. Qed.

(*
   本节说明 Drinfeld 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma bimap_to_from_cancel_cons {h x y z : C} (i : x ≅ y)
      (k : z ~> (y ⨂ h)%object) :
  (to i ⨂ id[h]) ∘ ((i⁻¹ ⨂ id[h]) ∘ k) ≈ k.
Proof.
  rewrite comp_assoc, <- bimap_comp, iso_to_from, id_left, bimap_id_id, id_left.
  reflexivity.
Qed.

Lemma bimap_id_to_from_cancel_cons {h x y z : C} (i : x ≅ y)
      (k : z ~> (h ⨂ y)%object) :
  (id[h] ⨂ to i) ∘ ((id[h] ⨂ i⁻¹) ∘ k) ≈ k.
Proof.
  rewrite comp_assoc, <- bimap_comp, iso_to_from, id_left, bimap_id_id, id_left.
  reflexivity.
Qed.

(*
   本节说明 Drinfeld 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma hb_left_unit_morphism {z : C} (σ : HalfBraiding z) :
  half_braiding_morphism (hb_tensor hb_unit σ) σ (to unit_left).
Proof.
  intro x.
  rewrite hb_tensor_to.
  rewrite hb_unit_field_to.
  rewrite bimap_comp_id_right.
  rewrite <- !comp_assoc.
  rewrite tri_cons.
  rewrite (bimap_to_from_cancel_cons unit_right).
  rewrite tri_left_cons.
  rewrite ul_nat_cons.
  rewrite <- triangle_identity_left.
  reflexivity.
Qed.

(*
   本节说明 Drinfeld 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma hb_right_unit_morphism {z : C} (σ : HalfBraiding z) :
  half_braiding_morphism (hb_tensor σ hb_unit) σ (to unit_right).
Proof.
  intro x.
  rewrite hb_tensor_to.
  rewrite hb_unit_field_to.
  rewrite bimap_comp_id_left.
  rewrite <- !comp_assoc.
  rewrite tri_right_cons.
  rewrite ur_nat_cons.
  rewrite tri_right_inv_cons.
  rewrite (bimap_id_to_from_cancel_cons unit_right).
  rewrite <- triangle_identity.
  reflexivity.
Qed.

(*
   本节说明 Drinfeld 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma pentagon_helperB {a b c e : C} :
  (id[a] ⨂ (@tensor_assoc C M b c e)⁻¹) ∘ to (@tensor_assoc C M a b (c ⨂ e))
    ≈ to (@tensor_assoc C M a (b ⨂ c) e)
        ∘ ((to (@tensor_assoc C M a b c) ⨂ id[e])
             ∘ (@tensor_assoc C M (a ⨂ b) c e)⁻¹).
Proof.
  apply (iso_to_epic (@tensor_assoc C M (a ⨂ b) c e)).
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  rewrite <- pentagon_a.
  rewrite bimap_id_cancel_cons.
  reflexivity.
Qed.

Lemma pentagon_helperB_cons {a b c e w : C}
      (k : w ~> ((a ⨂ b) ⨂ (c ⨂ e))%object) :
  (id[a] ⨂ (@tensor_assoc C M b c e)⁻¹) ∘ (to (@tensor_assoc C M a b (c ⨂ e)) ∘ k)
    ≈ to (@tensor_assoc C M a (b ⨂ c) e)
        ∘ ((to (@tensor_assoc C M a b c) ⨂ id[e])
             ∘ ((@tensor_assoc C M (a ⨂ b) c e)⁻¹ ∘ k)).
Proof.
  rewrite comp_assoc.
  rewrite pentagon_helperB.
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

(*
   本节说明 Drinfeld 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma to_assoc_nat_bid_cons {a a' b c w : C} (f : a ~> a')
      (k : w ~> ((a ⨂ b) ⨂ c)%object) :
  (f ⨂ id[(b ⨂ c)%object]) ∘ (to tensor_assoc ∘ k)
    ≈ to tensor_assoc ∘ (((f ⨂ id[b]) ⨂ id[c]) ∘ k).
Proof.
  spose (to_tensor_assoc_natural f (id[b]) (id[c])) as X.
  rewrite bimap_id_id in X.
  rewrite comp_assoc.
  rewrite X.
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma hb_assoc_morphism {za zb zd : C}
      (σa : HalfBraiding za) (σb : HalfBraiding zb) (σd : HalfBraiding zd) :
  half_braiding_morphism
    (hb_tensor (hb_tensor σa σb) σd)
    (hb_tensor σa (hb_tensor σb σd))
    (to tensor_assoc).
Proof.
  intro x.
  rewrite !hb_tensor_to.
  rewrite <- !comp_assoc.
  (* Distribute the inner tensor half-braid under [id[za] ⨂ -] and fold the
     three trailing associators of the LHS into the pentagon normal form. *)
  rewrite !bimap_comp_id_left.
  rewrite <- !comp_assoc.
  rewrite pentagon_a.
  (* Slide the [σd] strand into left-nested position. *)
  rewrite <- to_assoc_nat_id2_cons.
  (* Reframe the inverse associator around the [σb] strand. *)
  rewrite pentagon_helperB_cons.
  (* Slide the [σb] strand into left-nested position. *)
  rewrite to_assoc_nat_cons.
  (* Collapse the associator run left of the [σb] strand. *)
  rewrite pentagon_solved2_cons.
  (* The surviving [α⁻¹ ∘ α] cancels. *)
  rewrite (cancel_from_to_cons tensor_assoc).
  (* Slide the [σa] strand into left-nested position. *)
  rewrite to_assoc_nat_bid_cons.
  (* Fold the two leading associators back through the pentagon. *)
  rewrite <- pentagon_cons.
  (* Distribute the right-hand side's [β_{ab} ⨂ id[zd]] to meet the LHS comb. *)
  rewrite !bimap_comp_id_right.
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

(** ** The tensor bifunctor on the centre *)

Program Definition Drinfeld_Tensor : Drinfeld ∏ Drinfeld ⟶ Drinfeld := {|
  fobj := fun p =>
            ((`1 (fst p) ⨂ `1 (snd p))%object;
             hb_tensor (`2 (fst p)) (`2 (snd p)));
  fmap := fun p q fg =>
            (`1 (fst fg) ⨂ `1 (snd fg);
             hb_tensor_bimap_morphism (`2 (fst fg)) (`2 (snd fg)))
|}.
Next Obligation. proper; apply bimap_respects; assumption. Qed.
Next Obligation. apply bimap_comp. Qed.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Drinfeld_unit_left (A : Drinfeld) :
  Drinfeld_Tensor ((I; hb_unit), A) ≅[Drinfeld] A :=
  @Drinfeld_lift_iso (Drinfeld_Tensor ((I; hb_unit), A)) A
    (@unit_left C M (`1 A)) (hb_left_unit_morphism (`2 A)).

Definition Drinfeld_unit_right (A : Drinfeld) :
  Drinfeld_Tensor (A, (I; hb_unit)) ≅[Drinfeld] A :=
  @Drinfeld_lift_iso (Drinfeld_Tensor (A, (I; hb_unit))) A
    (@unit_right C M (`1 A)) (hb_right_unit_morphism (`2 A)).

Definition Drinfeld_tensor_assoc (A B D : Drinfeld) :
  Drinfeld_Tensor (Drinfeld_Tensor (A, B), D)
    ≅[Drinfeld] Drinfeld_Tensor (A, Drinfeld_Tensor (B, D)) :=
  @Drinfeld_lift_iso (Drinfeld_Tensor (Drinfeld_Tensor (A, B), D))
    (Drinfeld_Tensor (A, Drinfeld_Tensor (B, D)))
    (@tensor_assoc C M (`1 A) (`1 B) (`1 D))
    (hb_assoc_morphism (`2 A) (`2 B) (`2 D)).

Program Definition Drinfeld_Monoidal : @Monoidal Drinfeld := {|
  I            := (I; hb_unit);
  tensor       := Drinfeld_Tensor;
  unit_left    := Drinfeld_unit_left;
  unit_right   := Drinfeld_unit_right;
  tensor_assoc := Drinfeld_tensor_assoc
|}.
Next Obligation. apply to_unit_left_natural. Qed.
Next Obligation. apply from_unit_left_natural. Qed.
Next Obligation. apply to_unit_right_natural. Qed.
Next Obligation. apply from_unit_right_natural. Qed.
Next Obligation. apply to_tensor_assoc_natural. Qed.
Next Obligation. apply from_tensor_assoc_natural. Qed.
Next Obligation. apply triangle_identity. Qed.
Next Obligation. apply pentagon_identity. Qed.

(*
   本节说明 Drinfeld 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Naturality of a half-braiding in cons form. *)
Lemma hb_nat_cons {z : C} (σ : HalfBraiding z) {a b w : C} (f : a ~> b)
      (k : w ~> (z ⨂ a)%object) :
  to (half_braid σ b) ∘ ((id[z] ⨂ f) ∘ k)
    ≈ (f ⨂ id[z]) ∘ (to (half_braid σ a) ∘ k).
Proof.
  rewrite comp_assoc, (half_braid_natural σ f), <- comp_assoc.
  reflexivity.
Qed.

(*
   本节说明 Drinfeld 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma hb_braid_morphism {z z' : C} (σ : HalfBraiding z) (σ' : HalfBraiding z') :
  half_braiding_morphism (hb_tensor σ σ') (hb_tensor σ' σ) (to (half_braid σ z')).
Proof.
  intro x.
  transitivity (to (@tensor_assoc C M x z' z)
                  ∘ (to (half_braid σ (x ⨂ z'))
                       ∘ ((id[z] ⨂ to (half_braid σ' x))
                            ∘ to (@tensor_assoc C M z z' x)))).
  - (* LHS ≈ midpoint *)
    rewrite hb_tensor_to.
    symmetry.
    rewrite (hb_nat_cons σ (to (half_braid σ' x))).
    rewrite (half_braid_tensor σ).
    rewrite <- !comp_assoc.
    rewrite iso_from_to, id_right.
    reflexivity.
  - (* midpoint ≈ RHS *)
    rewrite hb_tensor_to.
    rewrite (half_braid_tensor σ).
    rewrite <- !comp_assoc.
    rewrite (cancel_to_from_cons (@tensor_assoc C M x z' z)).
    reflexivity.
Qed.

Definition Drinfeld_braid (A B : Drinfeld) :
  Drinfeld_Tensor (A, B) ~{Drinfeld}~> Drinfeld_Tensor (B, A) :=
  (to (half_braid (`2 A) (`1 B)); hb_braid_morphism (`2 A) (`2 B)).

Program Definition Drinfeld_Braided : @BraidedMonoidal Drinfeld := {|
  braided_is_monoidal := Drinfeld_Monoidal;
  braid := fun A B => Drinfeld_braid A B
|}.
Next Obligation.
  (* braid naturality: intertwine g by its centre-morphism proof, then slide
     h past the σ-half-braid by its naturality. *)
  rewrite <- !comp_assoc.
  rewrite <- (X2 z).
  rewrite <- (hb_nat_cons X3 h (g ⨂ id[z])).
  reflexivity.
Qed.
Next Obligation.
  (* first hexagon: expand [half_braid σa (zb⨂zd)] and cancel the two outer
     associators framing it. *)
  rewrite (half_braid_tensor X1).
  rewrite <- !comp_assoc.
  rewrite (cancel_to_from_cons (@tensor_assoc C M y z x)).
  rewrite iso_from_to, id_right.
  reflexivity.
Qed.
Next Obligation.
  (* second hexagon: the tensor half-braid is already expanded by [hb_tensor];
     cancel the two outer inverse associators. *)
  rewrite <- !comp_assoc.
  rewrite (cancel_from_to_cons (@tensor_assoc C M z x y)).
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

End Drinfeld.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Arguments Drinfeld C {M}.
Arguments Drinfeld_Forget C {M}.
Arguments Drinfeld_Monoidal C {M}.
Arguments Drinfeld_Braided C {M}.

