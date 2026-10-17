Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Sheaf.
Require Import Coq.Vectors.Vector.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/category+of+sheaves
 Wikipedia: https://en.wikipedia.org/wiki/Sheaf_(mathematics)

   本文件给出范畴变体或层范畴等。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明层/筛相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ForallT_impl {A : Type} (P Q : A → Type)
  (h : ∀ a : A, P a → Q a) :
  ∀ {n : nat} (v : Vector.t A n), ForallT P v → ForallT Q v.
Proof.
  intros n v HP; induction HP; constructor; auto.
Qed.

Section SheafCategory.

Context (C : Category).
Context `{@Site C}.

(*
   本节说明自然变换、层/筛相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Sheaves_sub : Subcategory (@Presheaves C Sets) :=
  @Build_Subcategory (@Presheaves C Sets)
    (fun X : Presheaf C Sets => Sheaf X)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition Sheaves : Category := Sub (@Presheaves C Sets) Sheaves_sub.

(** The inclusion of sheaves into presheaves. *)
Definition Sheaves_Incl : Sheaves ⟶ @Presheaves C Sets :=
  Incl (@Presheaves C Sets) Sheaves_sub.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Sheaves_Full : Functor.Full Sheaves_Incl.
Proof.
  apply Full_Implies_Full_Functor.
  intros x y ox oy f; exact I.
Defined.

(** The inclusion is faithful: on hom-sets it is the first projection
    out of a sigma type, and the hom-setoid of [Sub] is equality of
    first projections, so injectivity is immediate. *)
Lemma Sheaves_Faithful : Functor.Faithful Sheaves_Incl.
Proof.
  constructor; simpl; intros x y f g Hfg; exact Hfg.
Qed.

(*
   本节说明层/筛、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem sheaf_iso_closed
  (X Y : Presheaf C Sets) (iso : X ≅[@Presheaves C Sets] Y) :
  Sheaf X → Sheaf Y.
Proof.
  intros HX.
  constructor; intro u.
  pose proof (@restriction C _ X HX u) as HR.
  revert HR.
  destruct (coverage u) as [n fam].
  apply ForallT_impl.
  intros [uᵢ fᵢ] Hglue yᵢ Hcompat.
  (* Pull the matching family for Y back along [from iso], obtaining a
     matching family for X at the pulled-back section. *)
  assert (HXc : ∀ (v : C) (g : v ~> uᵢ),
            ForallT (A := ∃ uⱼ, uⱼ ~> u)
              (λ '(uⱼ; fⱼ),
                ∀ h : v ~> uⱼ,
                  fᵢ ∘ g ≈ fⱼ ∘ h →
                  ∀ xⱼ : X uⱼ,
                    fmap[X] g (transform[from iso] uᵢ yᵢ) ≈ fmap[X] h xⱼ)
              fam).
  { intros v g.
    generalize (Hcompat v g).
    apply ForallT_impl.
    intros [uⱼ fⱼ] Hj h e xⱼ.
    (* Naturality of [from iso] at g and at h, plus the iso round
       trip at uⱼ, reduce the X-compatibility square to the given
       Y-compatibility square. *)
    pose proof (naturality (from iso) uᵢ v g yᵢ) as HA; simpl in HA.
    pose proof (naturality (from iso) uⱼ v h (transform[to iso] uⱼ xⱼ)) as HB;
      simpl in HB.
    pose proof (iso_from_to iso uⱼ xⱼ) as HC; simpl in HC.
    rewrite HA.
    rewrite (Hj h e (transform[to iso] uⱼ xⱼ)).
    rewrite <- HB.
    apply (proper_morphism (fmap[X] h)).
    rewrite HC.
    exact (@fmap_id _ _ X uⱼ xⱼ). }
  destruct (Hglue (transform[from iso] uᵢ yᵢ) HXc) as [x Hx Hun].
  unshelve econstructor.
  - (* the glued section for Y: push X's glued section forward *)
    exact (transform[to iso] u x).
  - (* it restricts correctly, by naturality of [to iso] *)
    pose proof (naturality (to iso) u uᵢ fᵢ x) as HN; simpl in HN.
    pose proof (iso_to_from iso uᵢ yᵢ) as HD; simpl in HD.
    rewrite HN, Hx, HD.
    exact (@fmap_id _ _ Y uᵢ yᵢ).
  - (* uniqueness: any other glued section for Y pulls back to a glued
       section for X, so it agrees with x, hence with [to iso u x] *)
    intros y' Hy'; simpl in Hy'.
    pose proof (naturality (from iso) u uᵢ fᵢ y') as HN; simpl in HN.
    assert (Hx' : x ≈ transform[from iso] u y'). {
      apply Hun.
      rewrite HN.
      now rewrite Hy'.
    }
    pose proof (iso_to_from iso u y') as HD; simpl in HD.
    rewrite Hx', HD.
    exact (@fmap_id _ _ Y u y').
Defined.

End SheafCategory.
