Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Transformer.
Require Import Category.Monad.Morphism.

Generalizable All Variables.

(** * Monad transformers are morphisms of monads *)

(*
   nLab: https://ncatlab.org/nlab/show/monad+transformer
   nLab: https://ncatlab.org/nlab/show/monad (section "The 2-category of

   本文件给出单子相关定义或实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* [lift] is natural: [lift_bind] at ret ∘ g, then [lift_return]. *)

Lemma lift_natural@{o h | } {C : Category@{o h h}} {M : C ⟶ C}
  {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)} {HT : @Monad C (T M)}
  (L : @MonadTransformer C M HM T HT) {x y : C} (g : x ~> y) :
  fmap[T M] g ∘ @lift C M HM T HT L x ≈ @lift C M HM T HT L y ∘ fmap[M] g.
Proof.
  pose proof (@lift_bind C M HM T HT L x y (@ret C M HM y ∘ g)) as E.
  (* the right side of E is fmap[T M] g ∘ lift x *)
  symmetry in E.
  etransitivity; [ | etransitivity; [ exact E | ] ].
  - symmetry.
    apply compose_respects; [ | reflexivity ].
    etransitivity.
    { apply compose_respects; [ reflexivity | ].
      etransitivity; [ apply fmap_respects | ].
      - etransitivity; [ apply comp_assoc | ].
        apply compose_respects; [ apply lift_return | reflexivity ].
      - apply fmap_comp. }
    etransitivity; [ apply comp_assoc | ].
    etransitivity; [ apply compose_respects; [ apply join_fmap_ret | ];
                     reflexivity | ].
    apply id_left.
  - etransitivity.
    { apply compose_respects; [ reflexivity | apply fmap_comp ]. }
    etransitivity; [ apply comp_assoc_sym | ].
    apply compose_respects; [ reflexivity | ].
    etransitivity; [ apply comp_assoc | ].
    etransitivity; [ apply compose_respects; [ apply join_fmap_ret | ];
                     reflexivity | ].
    apply id_left.
Qed.

(** ** A transformer gives a morphism of monads M ⟶ T M *)

Definition transformer_hom@{o h | } {C : Category@{o h h}} {M : C ⟶ C}
  {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)} {HT : @Monad C (T M)}
  (L : @MonadTransformer C M HM T HT) : MonadHom@{o h} HM HT.
Proof.
  unshelve refine
    (@Build_MonadHom C M (T M) HM HT
       (Build_Transform'@{o h h o h h} (F:=M) (G:=T M)
          (fun x => @lift C M HM T HT L x)
          (fun x y g => lift_natural L g)) _ _).
  - intros x. exact (@lift_return C M HM T HT L x).
  - intros x; simpl.
    pose proof (@lift_bind C M HM T HT L (M x) x id) as E.
    etransitivity; [ | etransitivity; [ exact E | ] ].
    + symmetry.
      etransitivity; [ | apply id_right ].
      apply compose_respects; [ reflexivity | apply fmap_id ].
    + etransitivity; [ apply comp_assoc_sym | ].
      apply compose_respects; [ reflexivity | ].
      etransitivity; [ | apply lift_natural ].
      apply compose_respects; [ | reflexivity ].
      apply fmap_respects. apply id_right.
Defined.

(* Its components are [lift], on the nose. *)

Example transformer_hom_lift@{o h | +} {C : Category@{o h h}} {M : C ⟶ C}
  {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)} {HT : @Monad C (T M)}
  (L : @MonadTransformer C M HM T HT) (x : C) :
  mh_transform (transformer_hom@{o h} L) x = @lift C M HM T HT L x
  := eq_refl.

(** ** A morphism of monads M ⟶ T M satisfies the transformer laws *)

Definition hom_transformer@{o h | } {C : Category@{o h h}} {M : C ⟶ C}
  {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)} {HT : @Monad C (T M)}
  (θ : MonadHom@{o h} HM HT) : @MonadTransformer C M HM T HT.
Proof.
  unshelve refine
    (@Build_MonadTransformer C M HM T HT (fun x => mh_transform θ x) _ _).
  - intros a. exact (mh_ret θ).
  - intros a b f.
    etransitivity;
      [ apply compose_respects; [ apply (mh_join_nat θ b) | reflexivity ] | ].
    etransitivity; [ apply comp_assoc_sym | ].
    etransitivity; [ | apply comp_assoc ].
    apply compose_respects; [ reflexivity | ].
    etransitivity; [ apply comp_assoc_sym | ].
    etransitivity;
      [ apply compose_respects;
          [ reflexivity | symmetry; apply (naturality (mh_transform θ)) ] | ].
    etransitivity; [ apply comp_assoc | ].
    apply compose_respects; [ | reflexivity ].
    symmetry. apply fmap_comp.
Defined.

Example hom_transformer_lift@{o h | +} {C : Category@{o h h}} {M : C ⟶ C}
  {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)} {HT : @Monad C (T M)}
  (θ : MonadHom@{o h} HM HT) (x : C) :
  @lift C M HM T HT (hom_transformer@{o h} θ) x = mh_transform θ x
  := eq_refl.

(* The two round trips, on the component family. *)

Example transformer_round_trip@{o h | +} {C : Category@{o h h}}
  {M : C ⟶ C} {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)}
  {HT : @Monad C (T M)} (L : @MonadTransformer C M HM T HT) (x : C) :
  @lift C M HM T HT (hom_transformer@{o h} (transformer_hom@{o h} L)) x
    = @lift C M HM T HT L x := eq_refl.

Example hom_round_trip@{o h | +} {C : Category@{o h h}}
  {M : C ⟶ C} {HM : @Monad C M} {T : (C ⟶ C) → (C ⟶ C)}
  {HT : @Monad C (T M)} (θ : MonadHom@{o h} HM HT) (x : C) :
  mh_transform (transformer_hom@{o h} (hom_transformer@{o h} θ)) x
    = mh_transform θ x := eq_refl.
