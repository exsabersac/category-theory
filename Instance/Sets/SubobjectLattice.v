Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Image.
Require Import Category.Instance.Sets.Cocartesian.
Require Import Category.Instance.Sets.Products.

Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(** * The subobject lattice of a setoid: bottom, images, wide pullbacks,
      and Fong and Spivak's increasing family *)

(*
 nLab:      https://ncatlab.org/nlab/show/image
 nLab:      https://ncatlab.org/nlab/show/wide+pullback
 Wikipedia: https://en.wikipedia.org/wiki/Image_(category_theory)
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.
 Book:      Riehl, "Category Theory in Context", 2nd ed., §4.7
 Book:      Fong and Spivak, "Seven Sketches in Compositionality",

   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** (a) The map out of the empty setoid is monic *)

Lemma Sets_zero_monic (x : Sets) : Monic (@zero Sets Sets_Initial x).
Proof.
  constructor; intros z g1 g2 _ w.
  destruct (g1 w).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** (b) Images *)

Section SetsImages.

Universe o so.
Constraint o < so.

Context {y x : SetoidObject@{o o}}.
Context (f : y ~{Sets@{o so}}~> x).

Definition Sets_im_sub : @SubObj Sets@{o so} x :=
  @Build_SubObj Sets@{o so} x
    (Sets_Image f) (Sets_Image_mono f) (Sets_Image_mono_monic f).

Lemma Sets_image_least_eq (w : @SubObj Sets@{o so} x)
  (g : y ~{Sets@{o so}}~> sub_dom w) (Hg : sub_mono w ∘ g ≈ f)
  (p : carrier (Sets_Image f)) :
  sub_mono w (g (`1 (`2 p))) ≈ `1 p.
Proof.
  transitivity (f (`1 (`2 p))).
  - exact (Hg (`1 (`2 p))).
  - exact (`2 (`2 p)).
Qed.

Definition Sets_image_least_map (w : @SubObj Sets@{o so} x)
  (g : y ~{Sets@{o so}}~> sub_dom w) (Hg : sub_mono w ∘ g ≈ f) :
  Sets_Image f ~{Sets@{o so}}~> sub_dom w.
Proof.
  unshelve refine {| morphism := fun p => g (`1 (`2 p)) |}.
  intros p q Hpq.
  apply (snd (injectivity_is_monic (sub_mono w)) (sub_is_monic w)).
  transitivity (`1 p); [ exact (Sets_image_least_eq w g Hg p) | ].
  transitivity (`1 q); [ exact Hpq | ].
  symmetry; exact (Sets_image_least_eq w g Hg q).
Defined.

Definition Sets_ImageOf : ImageOf f.
Proof.
  unshelve refine {| im_sub := Sets_im_sub
                   ; im_factor := Sets_Image_epi f |}.
  - exact (Sets_Image_comm f).
  - intros w g Hg.
    exact (existT _ (Sets_image_least_map w g Hg)
             (Sets_image_least_eq w g Hg)).
Defined.

End SetsImages.

#[export] Instance Sets_HasImages@{o so} : HasImages Sets@{o so} :=
  @Build_HasImages Sets@{o so} (@Sets_ImageOf@{o so}).

(* ------------------------------------------------------------------------ *)
(** ** (c) Wide pullbacks *)

Local Obligation Tactic := idtac.

Section SetsWidePullback.

Universe o so.
Constraint o < so.

Context {I : Type@{o}}.
Context {A : I → SetoidObject@{o o}}.
Context {z : SetoidObject@{o o}}.
Context (f : ∀ i : I, A i ~{Sets@{o so}}~> z).

Definition Sets_wpull_carrier : Type@{o} :=
  { a : ∀ i : I, carrier (A i) & ∀ i j : I, f i (a i) ≈ f j (a j) }.

Definition Sets_wpull_equiv : crelation@{o o} Sets_wpull_carrier :=
  fun p q => ∀ i : I, `1 p i ≈ `1 q i.

Program Definition Sets_wpull_obj : SetoidObject@{o o} := {|
  carrier   := Sets_wpull_carrier;
  is_setoid := {| equiv := Sets_wpull_equiv |}
|}.
Next Obligation.
  constructor.
  - intros p i; reflexivity.
  - intros p q Hpq i; symmetry; exact (Hpq i).
  - intros p q r Hpq Hqr i;
      transitivity (`1 q i); [exact (Hpq i) | exact (Hqr i)].
Qed.

Program Definition Sets_wpull_proj (i : I) :
  Sets_wpull_obj ~{Sets@{o so}}~> A i := {|
  morphism := fun p => `1 p i
|}.
Next Obligation. intros i p q Hpq; exact (Hpq i). Qed.

Program Definition Sets_wpull_tuple (Q : SetoidObject@{o o})
  (q : ∀ i : I, Q ~{Sets@{o so}}~> A i)
  (Hq : ∀ i j : I, f i ∘ q i ≈ f j ∘ q j) :
  Q ~{Sets@{o so}}~> Sets_wpull_obj := {|
  morphism := fun w => existT _ (fun i => q i w) (fun i j => Hq i j w)
|}.
Next Obligation.
  intros Q q Hq w w' Hw i; exact (proper_morphism (q i) _ _ Hw).
Qed.

Definition Sets_WidePullback : WidePullback f.
Proof.
  unshelve refine (@Build_WidePullback Sets@{o so} I A z f
                     Sets_wpull_obj Sets_wpull_proj _ _).
  - intros i j p; exact (`2 p i j).
  - intros Q q Hq.
    unshelve refine {| unique_obj := Sets_wpull_tuple Q q Hq |}.
    + intros i w; reflexivity.
    + intros v Hv w i; symmetry; exact (Hv i w).
Defined.

End SetsWidePullback.

#[export] Instance Sets_HasWidePullbacks@{o so} :
  HasWidePullbacks Sets@{o so} :=
  @Build_HasWidePullbacks Sets@{o so} (@Sets_WidePullback@{o so}).

Local Obligation Tactic := cat_simpl.

(* ------------------------------------------------------------------------ *)
(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** (e) Fong and Spivak Seven Sketches 1.2.1: the increasing family *)

Definition Sets_nat : obj[Sets] := Sets_discrete nat.

Definition seg_carrier (n : nat) : Type :=
  { k : nat & (1 <= k)%nat /\ (k <= n)%nat }.

Program Definition seg_obj (n : nat) : obj[Sets] := {|
  carrier   := seg_carrier n;
  is_setoid := {| equiv := fun a b : seg_carrier n => `1 a = `1 b |}
|}.

Program Definition seg_mono (n : nat) : seg_obj n ~{Sets}~> Sets_nat := {|
  morphism := fun a => `1 a
|}.

Definition seg_monic (n : nat) : Monic (seg_mono n) :=
  fst (injectivity_is_monic (seg_mono n)) (fun a b (Hab : `1 a = `1 b) => Hab).

Definition fs_seg (n : nat) : @SubObj Sets Sets_nat :=
  @Build_SubObj Sets Sets_nat (seg_obj n) (seg_mono n) (seg_monic n).

Definition pos_carrier : Type := { k : nat & (1 <= k)%nat }.

Program Definition pos_obj : obj[Sets] := {|
  carrier   := pos_carrier;
  is_setoid := {| equiv := fun a b : pos_carrier => `1 a = `1 b |}
|}.

Program Definition pos_mono : pos_obj ~{Sets}~> Sets_nat := {|
  morphism := fun a => `1 a
|}.

Definition pos_monic : Monic pos_mono :=
  fst (injectivity_is_monic pos_mono) (fun a b (Hab : `1 a = `1 b) => Hab).

Definition fs_pos : @SubObj Sets Sets_nat :=
  @Build_SubObj Sets Sets_nat pos_obj pos_mono pos_monic.

(** *** The union of the family is the positive naturals *)

Definition fs_coprod :
  IsIndexedCoproduct (fun j : nat => sub_dom (fs_seg j))
    (Sets_icoprod_obj (fun j : nat => sub_dom (fs_seg j)))
    (Sets_icoprod_inj (fun j : nat => sub_dom (fs_seg j))) :=
  Sets_IsIndexedCoproduct (fun j : nat => sub_dom (fs_seg j)).

Definition fs_desc :
  Sets_icoprod_obj (fun j : nat => sub_dom (fs_seg j)) ~{Sets}~> Sets_nat :=
  unique_obj (icoprod_desc fs_coprod (fun j : nat => sub_mono (fs_seg j))).

Definition fs_image : ImageOf fs_desc := image_of fs_desc.

Definition fs_union : @SubObj Sets Sets_nat :=
  sub_wide_join_via fs_seg fs_coprod fs_image.

Program Definition fs_union_to_pos :
  Sets_icoprod_obj (fun j : nat => sub_dom (fs_seg j)) ~{Sets}~> pos_obj := {|
  morphism := fun p => existT _ (`1 (`2 p)) (proj1 (`2 (`2 p)))
|}.
Next Obligation.
  intros [j a] [j' b] [e Hab]; simpl in *; destruct e; simpl in *.
  exact Hab.
Qed.

Lemma fs_union_to_pos_eq : sub_mono fs_pos ∘ fs_union_to_pos ≈ fs_desc.
Proof. intro p; reflexivity. Qed.

Definition fs_union_le_pos : sub_le fs_union fs_pos :=
  im_least fs_image fs_pos fs_union_to_pos fs_union_to_pos_eq.

Program Definition fs_pos_to_union :
  pos_obj ~{Sets}~> sub_dom fs_union := {|
  morphism := fun a =>
    existT _ (`1 a)
      (existT _ (existT _ (`1 a) (existT _ (`1 a)
                  (conj (`2 a) (Nat.le_refl (`1 a))))) eq_refl)
|}.

Definition fs_pos_le_union : sub_le fs_pos fs_union :=
  existT _ fs_pos_to_union (fun a => eq_refl).

Theorem fs_union_is_positives : fs_union ≈ fs_pos.
Proof.
  exact (snd (sub_equiv_iff_mutual fs_union fs_pos)
           (fs_union_le_pos, fs_pos_le_union)).
Qed.

(** *** The intersection of the family is the bottom subobject *)

Definition fs_wpull : WidePullback (fun j : nat => sub_mono (fs_seg j)) :=
  Sets_WidePullback (fun j : nat => sub_mono (fs_seg j)).

Definition fs_inter : @SubObj Sets Sets_nat :=
  sub_wide_intersection fs_seg 0%nat fs_wpull.

Definition fs_bot : @SubObj Sets Sets_nat :=
  sub_bot (Sets_zero_monic Sets_nat).

Lemma seg_zero_empty (a : carrier (sub_dom (fs_seg 0%nat))) : False.
Proof.
  destruct a as [k [H1 H2]].
  exact (Nat.nle_succ_0 0 (Nat.le_trans 1 k 0 H1 H2)).
Qed.

Program Definition fs_inter_to_bot :
  sub_dom fs_inter ~{Sets}~> sub_dom fs_bot := {|
  morphism := fun p => False_rect _ (seg_zero_empty (`1 p 0%nat))
|}.
Next Obligation.
  intros p q Hpq; destruct (seg_zero_empty (`1 p 0%nat)).
Qed.

Definition fs_inter_le_bot : sub_le fs_inter fs_bot.
Proof.
  exists fs_inter_to_bot.
  intro p; destruct (seg_zero_empty (`1 p 0%nat)).
Defined.

Theorem fs_inter_is_empty : fs_inter ≈ fs_bot.
Proof.
  exact (snd (sub_equiv_iff_mutual fs_inter fs_bot)
           (fs_inter_le_bot,
            sub_bot_least (Sets_zero_monic Sets_nat) fs_inter)).
Qed.

(** *** The unit law at a concrete subobject *)

Definition fs_bot_join_seg3 : @SubObj Sets Sets_nat :=
  sub_join_via (sub_bot (Sets_zero_monic Sets_nat)) (fs_seg 3%nat)
    (image_of (merge (sub_mono (sub_bot (Sets_zero_monic Sets_nat)))
                 (sub_mono (fs_seg 3%nat)))).

Example fs_join_bot_left_unit : fs_bot_join_seg3 ≈ fs_seg 3%nat :=
  sub_join_via_bot (Sets_zero_monic Sets_nat) (fs_seg 3%nat) _.
