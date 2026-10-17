Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Structure.Pullback.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Image.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/subobject
 nLab: https://ncatlab.org/nlab/show/image
 nLab: https://ncatlab.org/nlab/show/base+change

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(* * ** (A) The subobject preimage monotone, any 范畴 （已译） *)

Section ReindexMonotone.

Context {C : Category}.
Context `{@HasPullbacks C}.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma sub_reindex_monotone {x y : C} (f : y ~> x) {u v : SubObj x} :
  sub_le u v → sub_le (sub_reindex f u) (sub_reindex f v).
Proof.
  intros [k Hk].
  assert (Hsq : f ∘ pullback_fst f (sub_mono u) (pullback f (sub_mono u))
                  ≈ sub_mono v
                      ∘ (k ∘ pullback_snd f (sub_mono u)
                             (pullback f (sub_mono u)))).
  { rewrite comp_assoc, Hk.
    exact (pullback_commutes f (sub_mono u) (pullback f (sub_mono u))). }
  destruct (ump_pullbacks f (sub_mono v) (pullback f (sub_mono v))
              (Pull f (sub_mono u) (pullback f (sub_mono u)))
              (pullback_fst f (sub_mono u) (pullback f (sub_mono u)))
              (k ∘ pullback_snd f (sub_mono u) (pullback f (sub_mono u)))
              Hsq) as [w [Hw1 Hw2] _].
  exact (existT _ w Hw1).
Defined.

End ReindexMonotone.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section SubImage.

Universe o so.
Constraint o < so.

Context {A B : SetoidObject@{o o}}.
Context (f : A ~{Sets@{o so}}~> B).

(* The direct image subobject: image 复合 mono,
 Instance/Sets/Image.v's construction reused whole. （已译） *)
Definition sub_image (u : @SubObj Sets@{o so} A) : @SubObj Sets@{o so} B :=
  @Build_SubObj Sets@{o so} B
    (Sets_Image (f ∘ sub_mono u))
    (Sets_Image_mono (f ∘ sub_mono u))
    (Sets_Image_mono_monic (f ∘ sub_mono u)).

(*
   本节说明 Subobject 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma sub_image_witness {u v : @SubObj Sets@{o so} A}
  (k : sub_dom u ~{Sets@{o so}}~> sub_dom v)
  (Hk : sub_mono v ∘ k ≈ sub_mono u)
  (p : carrier (Sets_Image (f ∘ sub_mono u))) :
  f (sub_mono v (k (`1 (`2 p)))) ≈ `1 p.
Proof.
  transitivity (f (sub_mono u (`1 (`2 p)))).
  - exact (proper_morphism f _ _ (Hk (`1 (`2 p)))).
  - exact (`2 (`2 p)).
Qed.

Definition sub_image_map {u v : @SubObj Sets@{o so} A}
  (k : sub_dom u ~{Sets@{o so}}~> sub_dom v)
  (Hk : sub_mono v ∘ k ≈ sub_mono u) :
  sub_dom (sub_image u) ~{Sets@{o so}}~> sub_dom (sub_image v).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o} _ _ _ _
       (fun p => existT _ (`1 p)
                   (existT _ (k (`1 (`2 p))) (sub_image_witness k Hk p)))
       _).
  intros p q Hpq; exact Hpq.
Defined.

Lemma sub_image_monotone {u v : @SubObj Sets@{o so} A} :
  sub_le u v → sub_le (sub_image u) (sub_image v).
Proof.
  intros [k Hk].
  exists (sub_image_map k Hk).
  intro p; reflexivity.
Qed.

(* 相关说明。 （已译） *)
#[export] Instance sub_image_respects :
  Proper (equiv ==> equiv) sub_image.
Proof.
  intros u v [i Hi].
  assert (Hfrom : sub_mono u ∘ from i ≈ sub_mono v).
  { rewrite <- Hi, <- comp_assoc, iso_to_from; cat. }
  unshelve refine (existT _ _ _).
  - unshelve refine {| to := sub_image_map (to i) Hi
                     ; from := sub_image_map (from i) Hfrom |}.
    + intro p; simpl; reflexivity.
    + intro p; simpl; reflexivity.
  - intro p; simpl; reflexivity.
Qed.

End SubImage.

Arguments sub_image {A B} f u.
Arguments sub_image_monotone {A B} f {u v} H.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section SubTranspose.

Universe o so.
Constraint o < so.

Context {A B : SetoidObject@{o o}}.
Context (f : A ~{Sets@{o so}}~> B).

(* 相关说明。 （已译） *)
Lemma sub_image_transpose_to (u : @SubObj Sets@{o so} A)
  (v : @SubObj Sets@{o so} B) :
  sub_le (sub_image f u) v → sub_le u (sub_reindex f v).
Proof.
  intros [k Hk].
  assert (Hsq : f ∘ sub_mono u
                  ≈ sub_mono v ∘ (k ∘ Sets_Image_epi (f ∘ sub_mono u))).
  { rewrite comp_assoc, Hk.
    intro p; reflexivity. }
  destruct (ump_pullbacks f (sub_mono v) (pullback f (sub_mono v))
              (sub_dom u) (sub_mono u)
              (k ∘ Sets_Image_epi (f ∘ sub_mono u)) Hsq)
    as [w [Hw1 Hw2] _].
  exact (existT _ w Hw1).
Defined.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma sub_transpose_from_eq (u : @SubObj Sets@{o so} A)
  (v : @SubObj Sets@{o so} B)
  (k : sub_dom u ~{Sets@{o so}}~> sub_dom (sub_reindex f v))
  (Hk : sub_mono (sub_reindex f v) ∘ k ≈ sub_mono u)
  (p : carrier (Sets_Image (f ∘ sub_mono u))) :
  sub_mono v (pullback_snd f (sub_mono v) (pullback f (sub_mono v))
                (k (`1 (`2 p)))) ≈ `1 p.
Proof.
  transitivity (f (sub_mono u (`1 (`2 p)))).
  - symmetry.
    transitivity (f (pullback_fst f (sub_mono v) (pullback f (sub_mono v))
                       (k (`1 (`2 p))))).
    + symmetry; exact (proper_morphism f _ _ (Hk (`1 (`2 p)))).
    + exact (pullback_commutes f (sub_mono v) (pullback f (sub_mono v))
               (k (`1 (`2 p)))).
  - exact (`2 (`2 p)).
Qed.

(* 相关说明。 （已译） *)
Definition sub_transpose_from_map (u : @SubObj Sets@{o so} A)
  (v : @SubObj Sets@{o so} B)
  (k : sub_dom u ~{Sets@{o so}}~> sub_dom (sub_reindex f v))
  (Hk : sub_mono (sub_reindex f v) ∘ k ≈ sub_mono u) :
  sub_dom (sub_image f u) ~{Sets@{o so}}~> sub_dom v.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o} _ _ _ _
       (fun p => pullback_snd f (sub_mono v) (pullback f (sub_mono v))
                   (k (`1 (`2 p)))) _).
  intros p q Hpq.
  apply (snd (injectivity_is_monic (sub_mono v)) (sub_is_monic v)).
  transitivity (`1 p); [ exact (sub_transpose_from_eq u v k Hk p) | ].
  transitivity (`1 q); [ exact Hpq | ].
  symmetry; exact (sub_transpose_from_eq u v k Hk q).
Defined.

Lemma sub_image_transpose_from (u : @SubObj Sets@{o so} A)
  (v : @SubObj Sets@{o so} B) :
  sub_le u (sub_reindex f v) → sub_le (sub_image f u) v.
Proof.
  intros [k Hk].
  exact (existT _ (sub_transpose_from_map u v k Hk)
           (sub_transpose_from_eq u v k Hk)).
Defined.

Definition sub_image_reindex_iffT (u : @SubObj Sets@{o so} A)
  (v : @SubObj Sets@{o so} B) :
  sub_le (sub_image f u) v ↔ sub_le u (sub_reindex f v) :=
  (sub_image_transpose_to u v, sub_image_transpose_from u v).

End SubTranspose.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section Bridges.

Universe o so.
Constraint o < so.

Context {A B : SetoidObject@{o o}}.
Context (f : A ~{Sets@{o so}}~> B).

(* 相关说明。 （已译） *)
Lemma sub_image_is_Powerset_Prop_image
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  Powerset_subset_of_subobject@{o so}
      (sub_image f (Powerset_subobject_of_subset@{o so} S))
    ≈ Powerset_Prop_image@{o} f S.
Proof.
  intro b; split; intros Hb Q k.
  - refine (Hb Q _); intros [p Hp].
    apply k; exists (`1 (`1 (`2 p))); split.
    + exact (`2 (`1 (`2 p))).
    + transitivity (`1 p); [ exact (`2 (`2 p)) | exact Hp ].
  - refine (Hb Q _); intros [a [Ha Hfa]].
    apply k.
    unshelve refine (existT _ _ _).
    + exists b; exists (existT _ a Ha); exact Hfa.
    + reflexivity.
Qed.

(* ... and dually for the preimage. *)
Lemma sub_reindex_is_Powerset_Prop_preimage
  (T : carrier (Powerset_Prop_obj@{o} B)) :
  Powerset_subset_of_subobject@{o so}
      (sub_reindex f (Powerset_subobject_of_subset@{o so} T))
    ≈ Powerset_Prop_preimage@{o} f T.
Proof.
  intro a; split.
  - intro Ha.
    refine (Ha (T (f a)) _); intros [p Hp].
    refine (proj1 (@proper_morphism _ _ _ _ T (`1 (snd (`1 p))) (f a) _)
              (`2 (snd (`1 p)))).
    symmetry.
    transitivity (f (fst (`1 p))).
    + exact (proper_morphism f _ _ (symmetry Hp)).
    + exact (`2 p).
  - intro Ha.
    apply Powerset_squash_intro@{o}.
    unshelve refine (existT _ _ _).
    + unshelve refine (existT _ (a, existT _ (f a) Ha) _).
      reflexivity.
    + reflexivity.
Qed.

(* Consequently Type-valued subobject order maps Prop-valued
 subset order: factorization between subobjects yields 含入 of
 subsets they name. （已译） *)
Lemma subset_le_of_sub_le (u v : @SubObj Sets@{o so} A) :
  sub_le u v →
  ∀ a, Powerset_subset_of_subobject@{o so} u a
       → Powerset_subset_of_subobject@{o so} v a.
Proof.
  intros [k Hk] a Ha Q j.
  refine (Ha Q _); intros [p Hp].
  apply j; exists (k p).
  transitivity (sub_mono u p); [ exact (Hk p) | exact Hp ].
Qed.

End Bridges.
