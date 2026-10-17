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
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.Action.Monad.
Require Import Category.Instance.Fun.Action.Monad.BG.

Generalizable All Variables.

(** * #464's two monads are isomorphic in the category of monads *)

(*
 Book: Riehl, "Category Theory in Context", 2nd ed., Exercise 5.5.iv,
 nLab: https://ncatlab.org/nlab/show/monad (section "The 2-category of

   本文件给出单子相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** θ : ActMonad M ⟶ BGMonad M, identity components *)

Definition BG_theta@{o so | o < so +} (M : MonObject@{o o o}) :
  MonadHom@{so o} (ActMonad@{o so} M) (BGMonad@{o so} M).
Proof.
  unshelve refine
    (@Build_MonadHom Sets@{o so} (ActF@{o so} M) (U_BG@{o so} M ◯ F_BG@{o so} M)
       (ActMonad@{o so} M) (BGMonad@{o so} M)
       (Build_Transform'@{so o o so o o}
          (F:=ActF@{o so} M) (G:=U_BG@{o so} M ◯ F_BG@{o so} M)
          (fun X => @id Sets@{o so} (act_prod M X)) _) _ _).
  - intros X Y f p. simpl. split; reflexivity.
  - intros X x. simpl.
    split; [ symmetry; exact (mon_op_unit_l mon_unit) | reflexivity ].
  - intros X p. simpl. split; reflexivity.
Defined.

Example BG_theta_component@{o so | o < so +} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) :
  mh_transform (BG_theta@{o so} M) X = @id Sets@{o so} (act_prod M X)
  := eq_refl.

(** ** θ⁻¹ : BGMonad M ⟶ ActMonad M, identity components *)

Definition BG_theta_inv@{o so | o < so +} (M : MonObject@{o o o}) :
  MonadHom@{so o} (BGMonad@{o so} M) (ActMonad@{o so} M).
Proof.
  unshelve refine
    (@Build_MonadHom Sets@{o so} (U_BG@{o so} M ◯ F_BG@{o so} M) (ActF@{o so} M)
       (BGMonad@{o so} M) (ActMonad@{o so} M)
       (Build_Transform'@{so o o so o o}
          (F:=U_BG@{o so} M ◯ F_BG@{o so} M) (G:=ActF@{o so} M)
          (fun X => @id Sets@{o so} (act_prod M X)) _) _ _).
  - intros X Y f p. simpl. split; reflexivity.
  - intros X x. simpl. split; [ exact (mon_op_unit_l mon_unit) | reflexivity ].
  - intros X p. simpl. split; reflexivity.
Defined.

Example BG_theta_inv_component@{o so | o < so +} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) :
  mh_transform (BG_theta_inv@{o so} M) X = @id Sets@{o so} (act_prod M X)
  := eq_refl.

(* The two are inverse in [Monads Sets]. *)

Definition BG_theta_iso@{o so m1 m2 |
  o < so, o <= m1, o <= m2, so <= m1, so <= m2 +} (M : MonObject@{o o o}) :
  @Isomorphism (Monads@{so o m1 m2} Sets@{o so})
    (ActF@{o so} M; ActMonad@{o so} M)
    (U_BG@{o so} M ◯ F_BG@{o so} M; BGMonad@{o so} M).
Proof.
  unshelve refine (@Build_Isomorphism (Monads@{so o m1 m2} Sets@{o so})
    (ActF@{o so} M; ActMonad@{o so} M)
    (U_BG@{o so} M ◯ F_BG@{o so} M; BGMonad@{o so} M)
    (BG_theta@{o so} M) (BG_theta_inv@{o so} M) _ _).
  - intros X p. simpl. split; reflexivity.
  - intros X p. simpl. split; reflexivity.
Defined.

(** ** θ* against #464's [BG_Act_EM] *)

Example BG_theta_EM_carrier@{o so | o < so +} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M)) :
  `1 (fobj[mh_EM@{so o so so} (BG_theta@{o so} M)] x)
    = `1 (fobj[BG_Act_EM@{o so} M] x) := eq_refl.

Example BG_theta_EM_alg_fun@{o so | o < so +} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M)) :
  (fun p => @t_alg _ _ _ _
              (`2 (fobj[mh_EM@{so o so so} (BG_theta@{o so} M)] x)) p)
    = (fun p => @t_alg _ _ _ _ (`2 (fobj[BG_Act_EM@{o so} M] x)) p)
  := eq_refl.

Example BG_theta_EM_hom@{o so | o < so +} (M : MonObject@{o o o})
  (x y : @EilenbergMoore@{so so so o} Sets@{o so}
           (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M))
  (f : x ~> y) :
  t_alg_hom[fmap[mh_EM@{so o so so} (BG_theta@{o so} M)] f]
    = t_alg_hom[fmap[BG_Act_EM@{o so} M] f] := eq_refl.

Definition BG_theta_EM@{o so c | o < so, o < c, so < c +}
  (M : MonObject@{o o o}) :
  @equiv _
    (@homset Cat@{c so so so o}
       (@EilenbergMoore@{so so so o} Sets@{o so}
          (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M))
       (@EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
          (ActMonad@{o so} M)))
    (mh_EM@{so o so so} (BG_theta@{o so} M)) (BG_Act_EM@{o so} M).
Proof.
  unshelve eexists.
  - intros x.
    unshelve refine (@Build_Isomorphism _ _ _ _ _ _ _).
    + unshelve refine
        (@Build_TAlgebraHom _ _ _ _ _ _ _ (@id Sets@{o so} _) _).
      intros [g z]. reflexivity.
    + unshelve refine
        (@Build_TAlgebraHom _ _ _ _ _ _ _ (@id Sets@{o so} _) _).
      intros [g z]. reflexivity.
    + intros z. reflexivity.
    + intros z. reflexivity.
  - intros x y f z. reflexivity.
Defined.

(** ** θ⁻¹* assembles #464's [Act_BG_alg] into a functor *)

Definition Act_BG_EM@{o so | o < so +} (M : MonObject@{o o o}) :
  @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M) (ActMonad@{o so} M)
  ⟶ @EilenbergMoore@{so so so o} Sets@{o so}
      (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M) :=
  mh_EM@{so o so so} (BG_theta_inv@{o so} M).

Example Act_BG_EM_carrier@{o so | o < so +} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) :
  `1 (fobj[Act_BG_EM@{o so} M] x) = `1 x := eq_refl.

Example Act_BG_EM_alg_fun@{o so | o < so +} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) :
  (fun p => @t_alg _ _ _ _ (`2 (fobj[Act_BG_EM@{o so} M] x)) p)
    = (fun p => @t_alg _ _ _ _ (Act_BG_alg@{o so} M (`1 x) (`2 x)) p)
  := eq_refl.
