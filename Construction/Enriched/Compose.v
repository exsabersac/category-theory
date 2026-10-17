Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Construction.Enriched.
Require Import Category.Construction.Enriched.Natural.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   本文件给出复合相关构造（伴随/函子/单子等的复合）。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** The 恒等 enriched 函子: 对象 map 恒等 each
 hom-对象 map 恒等 K-态射 id[x ⟿ y]. （已译） *)

Program Definition EnrichedId {K : Category} `{@Monoidal K}
        (C : Enriched K) : EnrichedFunctor K C C := {|
  efobj := fun x => x;
  efmap := fun x y => id
|}.
Next Obligation.
  (* preserves identity: id ∘ eid ≈ eid, by id_left *)
  intros.
  simpl.
  now rewrite id_left.
Qed.
Next Obligation.
  (* preserves 复合: ecompose ∘ id ⨂ id ≈ id ∘ ecompose.
 bimap id id ≈ id collapses left tensor, id_left right. （已译） *)
  intros.
  simpl.
  rewrite bimap_id_id.
  rewrite id_left, id_right.
  reflexivity.
Qed.

(** Composition enriched 函子 G ∘ F: compose 对象 maps compose
 hom-对象 maps K. （已译） *)

Program Definition EnrichedCompose {K : Category} `{@Monoidal K}
        {C D E : Enriched K}
        (G : EnrichedFunctor K D E) (F : EnrichedFunctor K C D) :
  EnrichedFunctor K C E := {|
  efobj := fun x => efobj (efobj x);
  efmap := fun x y => efmap ∘ efmap
|}.
Next Obligation.
  (* preserves identity: (efmap G ∘ efmap F) ∘ eid ≈ eid.
     Reassociate, apply F.efmap_id then G.efmap_id. *)
  intros.
  simpl.
  rewrite <- comp_assoc.
  rewrite (efmap_id (EnrichedFunctor := F)).
  rewrite (efmap_id (EnrichedFunctor := G)).
  reflexivity.
Qed.
Next Obligation.
  (* preserves 复合:
 ecompose ∘ (efmap G ∘ efmap F) ⨂ (efmap G ∘ efmap F)
 ≈ (efmap G ∘ efmap F) ∘ ecompose.
 Split tensor bimap_comp, then use G.efmap_comp and
 F.efmap_comp.（已译） *)
  intros.
  simpl.
  rewrite bimap_comp.
  rewrite comp_assoc.
  rewrite (efmap_comp (EnrichedFunctor := G)).
  rewrite <- comp_assoc.
  rewrite (efmap_comp (EnrichedFunctor := F)).
  rewrite comp_assoc.
  reflexivity.
Qed.

(** Left whiskering: given a V-natural transformation σ : F ⟹ G between
    F, G : C ⟶ D and an enriched functor H : D ⟶ E, produce a V-natural
    transformation H∘F ⟹ H∘G whose component at x is efmap H ∘ σ_x. *)

Program Definition EnrichedWhiskerLeft {K : Category} `{@Monoidal K}
        {C D E : Enriched K}
        {F G : EnrichedFunctor K C D}
        (H : EnrichedFunctor K D E)
        (σ : EnrichedTransform F G) :
  EnrichedTransform (EnrichedCompose H F) (EnrichedCompose H G) := {|
  etransform := fun x => efmap ∘ etransform x
|}.
Next Obligation.
  (*
   本节说明 Compose 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  intros.
  simpl.
  (* split each tensor of composites into a composite of tensors *)
  rewrite !bimap_comp.
  (* expose ecompose ∘ (efmap H ⨂ efmap H) on both sides and collapse it
     through H.efmap_comp into efmap H ∘ ecompose *)
  rewrite !comp_assoc.
  rewrite !(efmap_comp (EnrichedFunctor := H)).
  (* 相关说明。 （已译） *)
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  rewrite !comp_assoc.
  apply (enaturality (EnrichedTransform := σ)).
Qed.

(** Right whiskering: given σ : F ⟹ G between F, G : C ⟶ D and an enriched
    functor H : B ⟶ C, produce F∘H ⟹ G∘H whose component at x is σ_{H x}. *)

Program Definition EnrichedWhiskerRight {K : Category} `{@Monoidal K}
        {B C D : Enriched K}
        {F G : EnrichedFunctor K C D}
        (H : EnrichedFunctor K B C)
        (σ : EnrichedTransform F G) :
  EnrichedTransform (EnrichedCompose F H) (EnrichedCompose G H) := {|
  etransform := fun x => etransform (efobj x)
|}.
Next Obligation.
  (*
   本节说明 Compose 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  intros.
  simpl.
  (* pad each component transform 恒等 so tensor becomes a
 tensor composites, then split it （已译） *)
  rewrite <- (id_right (etransform (efobj y))).
  rewrite <- (id_right (etransform (efobj x))).
  rewrite !bimap_comp.
  (* 相关说明。 （已译） *)
  rewrite <- !comp_assoc.
  rewrite from_unit_left_natural.
  rewrite from_unit_right_natural.
  (* 相关说明。 （已译） *)
  rewrite !comp_assoc.
  apply compose_respects; [ | reflexivity ].
  apply (enaturality (EnrichedTransform := σ)).
Qed.
