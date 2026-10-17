Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Morphism.
Require Import Category.Monad.Morphism.Algebra.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Monad.
Require Import Category.Instance.Cat.
Require Import Category.Instance.SupLat.
Require Import Category.Instance.SupLat.Free.

Generalizable All Variables.

(* * * θ* between #466's two power-set 单子 （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/suplattice
 nLab: https://ncatlab.org/nlab/show/monad (section "The 2-category of

   本文件给出自由构造相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** θ : Powerset_Monad ⟶ SL_induced, 恒等 components （已译） *)

Definition SL_theta@{o so | Set < o, o < so +} :
  MonadHom@{so o} Powerset_Monad@{o so} SL_induced@{o so}.
Proof.
  unshelve refine
    (@Build_MonadHom Sets@{o so} Powerset_Prop@{o so}
       (SL_Forget@{o so} ◯ SL_Free@{o so})
       Powerset_Monad@{o so} SL_induced@{o so}
       (Build_Transform'@{so o o so o o}
          (F:=Powerset_Prop@{o so}) (G:=SL_Forget@{o so} ◯ SL_Free@{o so})
          (fun X => @id Sets@{o so} (fobj[Powerset_Prop@{o so}] X)) _) _ _).
  - intros X Y f S. reflexivity.
  - intros X x. reflexivity.
  - intros X SS.
    symmetry.
    etransitivity;
      [ exact (SL_induced_join_equiv X (fmap[Powerset_Prop@{o so}] id SS)) | ].
    apply (proper_morphism (@join _ _ Powerset_Monad@{o so} X)).
    exact (@Powerset_Prop_map_id@{o} (Powerset_Prop_obj@{o} X) SS).
Defined.

Example SL_theta_component@{o so | Set < o, o < so +} (X : SetoidObject@{o o}) :
  mh_transform SL_theta@{o so} X
    = @id Sets@{o so} (fobj[Powerset_Prop@{o so}] X) := eq_refl.

(* θ* on one algebra against [SL_induced_repack], as a function. *)

Example SL_theta_alg_fun@{o so | Set < o, o < so +} {X : SetoidObject@{o o}}
  (β : @TAlgebra Sets@{o so} (SL_Forget@{o so} ◯ SL_Free@{o so})
         SL_induced@{o so} X) :
  (fun S => @t_alg _ _ _ _ (mh_algebra SL_theta@{o so} β) S)
    = (fun S => @t_alg _ _ _ _ (SL_induced_repack@{o so} β) S) := eq_refl.

(* * ** θ⁻¹ : SL_induced ⟶ Powerset_Monad, 恒等 components （已译） *)

Definition SL_theta_inv@{o so | Set < o, o < so +} :
  MonadHom@{so o} SL_induced@{o so} Powerset_Monad@{o so}.
Proof.
  unshelve refine
    (@Build_MonadHom Sets@{o so} (SL_Forget@{o so} ◯ SL_Free@{o so})
       Powerset_Prop@{o so}
       SL_induced@{o so} Powerset_Monad@{o so}
       (Build_Transform'@{so o o so o o}
          (F:=SL_Forget@{o so} ◯ SL_Free@{o so}) (G:=Powerset_Prop@{o so})
          (fun X => @id Sets@{o so} (fobj[Powerset_Prop@{o so}] X)) _) _ _).
  - intros X Y f S. reflexivity.
  - intros X x. reflexivity.
  - intros X SS.
    etransitivity; [ exact (SL_induced_join_equiv X SS) | ].
    apply (proper_morphism (@join _ _ Powerset_Monad@{o so} X)).
    symmetry.
    exact (@Powerset_Prop_map_id@{o} (Powerset_Prop_obj@{o} X) SS).
Defined.

Example SL_theta_inv_component@{o so | Set < o, o < so +}
  (X : SetoidObject@{o o}) :
  mh_transform SL_theta_inv@{o so} X
    = @id Sets@{o so} (fobj[Powerset_Prop@{o so}] X) := eq_refl.

(* 相关说明。 （已译） *)

Definition SL_theta_iso@{o so m1 m2 |
  Set < o, o < so, o <= m1, o <= m2, so <= m1, so <= m2 +} :
  @Isomorphism (Monads@{so o m1 m2} Sets@{o so})
    (Powerset_Prop@{o so}; Powerset_Monad@{o so})
    (SL_Forget@{o so} ◯ SL_Free@{o so}; SL_induced@{o so}).
Proof.
  unshelve refine (@Build_Isomorphism (Monads@{so o m1 m2} Sets@{o so})
    (Powerset_Prop@{o so}; Powerset_Monad@{o so})
    (SL_Forget@{o so} ◯ SL_Free@{o so}; SL_induced@{o so})
    SL_theta@{o so} SL_theta_inv@{o so} _ _).
  - intros X S. reflexivity.
  - intros X S. reflexivity.
Defined.

(* * ** θ* : 函子 Free.v lists NOT DELIVERED （已译） *)

Definition SL_EM_theta@{o so | Set < o, o < so +} :
  @EilenbergMoore@{so so so o} Sets@{o so}
    (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}
  ⟶ @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
      Powerset_Monad@{o so} :=
  mh_EM@{so o so so} SL_theta@{o so}.

Example SL_EM_theta_carrier@{o so | Set < o, o < so +}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  `1 (fobj[SL_EM_theta@{o so}] x) = `1 x := eq_refl.

Example SL_EM_theta_alg_fun@{o so | Set < o, o < so +}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  (fun S => @t_alg _ _ _ _ (`2 (fobj[SL_EM_theta@{o so}] x)) S)
    = (fun S => @t_alg _ _ _ _ (SL_induced_repack@{o so} (`2 x)) S)
  := eq_refl.

(** ** [EM_induced_to_SupLat] 经 θ* 分解 *)

Example SL_factor_set@{o so | Set < o, o < so +}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  sl_set (fobj[EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}] x)
    = sl_set (fobj[EM_induced_to_SupLat@{o so}] x) := eq_refl.

Example SL_factor_le@{o so | Set < o, o < so +}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  sl_le (fobj[EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}] x)
    = sl_le (fobj[EM_induced_to_SupLat@{o so}] x) := eq_refl.

Example SL_factor_sup_fun@{o so | Set < o, o < so +}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  (fun S => sl_sup (fobj[EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}] x) S)
    = (fun S => sl_sup (fobj[EM_induced_to_SupLat@{o so}] x) S) := eq_refl.

Example SL_factor_map@{o so | Set < o, o < so +}
  (x y : @EilenbergMoore@{so so so o} Sets@{o so}
           (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so})
  (f : x ~> y) :
  slh_map (fmap[EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}] f)
    = slh_map (fmap[EM_induced_to_SupLat@{o so}] f) := eq_refl.

Definition SL_factor@{o so c | Set < o, o < so, o < c, so < c +} :
  @equiv _
    (@homset Cat@{c so so so o}
       (@EilenbergMoore@{so so so o} Sets@{o so}
          (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so})
       SupLat@{o so})
    (EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}) EM_induced_to_SupLat@{o so}.
Proof.
  unshelve eexists.
  - intros x.
    unshelve refine (@Build_Isomorphism _ _ _ _ _ _ _).
    + unshelve refine
        (@Build_SupLatHom@{o}
           (fobj[EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}] x)
           (fobj[EM_induced_to_SupLat@{o so}] x) (@id Sets@{o so} _) _).
      intros S.
      apply (proper_morphism (@t_alg _ _ _ _ (projT2 x))).
      symmetry. exact (@Powerset_Prop_map_id@{o} _ S).
    + unshelve refine
        (@Build_SupLatHom@{o}
           (fobj[EM_induced_to_SupLat@{o so}] x)
           (fobj[EM_to_SupLat@{o so} ◯ SL_EM_theta@{o so}] x)
           (@id Sets@{o so} _) _).
      intros S.
      apply (proper_morphism (@t_alg _ _ _ _ (projT2 x))).
      symmetry. exact (@Powerset_Prop_map_id@{o} _ S).
    + intros z. reflexivity.
    + intros z. reflexivity.
  - intros x y f z. reflexivity.
Defined.
