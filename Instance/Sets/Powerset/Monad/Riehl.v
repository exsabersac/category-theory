(** * Riehl's route to the naturality of the union *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Monad.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Instance.Powerset.

Generalizable All Variables.

(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 nLab: https://ncatlab.org/nlab/show/power+set
 nLab: https://ncatlab.org/nlab/show/adjoint+functor

   本文件给出单子相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** The union as a least upper bound *)

(* ⋃ SS is the least upper bound, under inclusion, of the family of its
   members, indexed by the members themselves. *)
Lemma Powerset_union_IsLUB@{o} {X : SetoidObject@{o o}}
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))) :
  IsLUB@{o o Set Set Set} (@subset_le@{o} X)
    (fun i : { S : carrier (Powerset_Prop_obj@{o} X) & SS S } => projT1 i)
    (Powerset_union_pred@{o} SS).
Proof.
  split.
  - intros [S HS] x Hx. exists S; split; assumption.
  - intros n Hn x [S [HS Hx]]. exact (Hn (S; HS) x Hx).
Qed.

(* The same union, as #382's canonical family union [subset_union]. *)
Lemma Powerset_union_family@{o} {X : SetoidObject@{o o}}
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))) :
  Powerset_union_pred@{o} SS
    ≈ subset_union@{o o o}
        (fun i : { S : carrier (Powerset_Prop_obj@{o} X) & SS S } => projT1 i).
Proof.
  intro x; split.
  - intros [S [HS Hx]]. exists (S; HS). exact Hx.
  - intros [[S HS] Hx]. exists S; split; assumption.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** The naturality of μ, through the direct image as a left adjoint *)

(* Through #382's [direct_image_preserves_joins]: the image of a least upper
   bound is the least upper bound of the images. *)
Lemma join_natural_via_image@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y)
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))) :
  Powerset_union_pred@{o} (Powerset_Prop_image@{o} (Powerset_Prop_map@{o} f) SS)
    ≈ Powerset_Prop_image@{o} f (Powerset_union_pred@{o} SS).
Proof.
  pose proof (direct_image_preserves_joins f _ _ (Powerset_union_IsLUB SS))
    as Hf.
  pose proof (Powerset_union_IsLUB
                (Powerset_Prop_image@{o} (Powerset_Prop_map@{o} f) SS)) as Hu.
  destruct Hf as [Hf_ub Hf_least].
  destruct Hu as [Hu_ub Hu_least].
  intro y; split.
  - apply Hu_least. intros [T HT] z Hz.
    apply HT; intros [S [HS E]].
    exact (Hf_ub (S; HS) z (proj2 (E z) Hz)).
  - apply Hf_least. intros [S HS] z Hz.
    refine (Hu_ub (existT _ (Powerset_Prop_image@{o} f S) _) z Hz).
    apply Powerset_squash_intro. exists S; split; [ exact HS | ].
    reflexivity.
Qed.

(* Through #382's [direct_image_preserves_joins_via_LAPC]: Riehl's Corollary
   4.6.3 read off the left adjoint's preservation of colimits, at the
   canonical union of the members. *)
Lemma join_natural_via_LAPC@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y)
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))) :
  Powerset_union_pred@{o} (Powerset_Prop_image@{o} (Powerset_Prop_map@{o} f) SS)
    ≈ Powerset_Prop_image@{o} f (Powerset_union_pred@{o} SS).
Proof.
  pose proof (direct_image_preserves_joins_via_LAPC f
                (fun i : { S : carrier (Powerset_Prop_obj@{o} X) & SS S } =>
                   projT1 i)) as Hf.
  destruct Hf as [Hf_ub Hf_least].
  pose proof (@proper_morphism _ _ _ _ (Powerset_Prop_map@{o} f) _ _
                (Powerset_union_family SS)) as E.
  intro y; split.
  - intros [T [HT Hy]]. apply (proj2 (E y)).
    apply HT; intros [S [HS ES]].
    exact (Hf_ub (S; HS) y (proj2 (ES y) Hy)).
  - intro Hy.
    refine (Hf_least (Powerset_union_pred@{o}
                        (Powerset_Prop_image@{o} (Powerset_Prop_map@{o} f) SS))
              _ y (proj1 (E y) Hy)).
    intros [S HS] z Hz. exists (Powerset_Prop_image@{o} f S); split;
      [ | exact Hz ].
    apply Powerset_squash_intro. exists S; split; [ exact HS | ].
    reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** The three proofs inhabit the monad's naturality field *)

(* The type of [Powerset_Monad]'s field [join_fmap_fmap] at f. *)
Definition Powerset_join_natural_statement@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) : Type@{o} :=
  @join _ _ Powerset_Monad@{o so} Y
    ∘ fmap[Powerset_Prop@{o so}] (fmap[Powerset_Prop@{o so}] f)
  ≈ fmap[Powerset_Prop@{o so}] f ∘ @join _ _ Powerset_Monad@{o so} X.

(* The field itself, the direct lemma, and both of Riehl's routes: the
   quadruple is well typed, so each route proves the field's statement. *)
Definition join_natural_routes_agree@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) :
  Powerset_join_natural_statement@{o so} f
  * Powerset_join_natural_statement@{o so} f
  * Powerset_join_natural_statement@{o so} f
  * Powerset_join_natural_statement@{o so} f :=
  (@join_fmap_fmap _ _ Powerset_Monad@{o so} X Y f,
   fun SS => Powerset_union_natural@{o} f SS,
   fun SS => join_natural_via_image f SS,
   fun SS => join_natural_via_LAPC f SS).
