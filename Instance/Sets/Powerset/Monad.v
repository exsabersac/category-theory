(* * * The covariant power-set 单子 [Sets] （已译） *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.

Generalizable All Variables.

(*
 Book: Awodey, "Category Theory", Carnegie Mellon pre-print, September
 Book: Riehl, "Category Theory in Context", 2nd ed., §5.1, Example
 nLab: https://ncatlab.org/nlab/show/power+set
 nLab: https://ncatlab.org/nlab/show/monad

   本文件给出单子相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** The union of a set of subsets *)

(* 相关说明。 （已译） *)
Definition Powerset_union_pred@{o} {X : SetoidObject@{o o}}
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))) :
  carrier (Powerset_Prop_obj@{o} X).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier X) (is_setoid X) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ x, ex (fun S : carrier (Powerset_Prop_obj@{o} X) => SS S /\ S x))
       _).
  intros x y Hxy; split; intros [S [HS Hx]]; exists S; split; try exact HS.
  - exact (proj1 (@proper_morphism _ _ _ _ S x y Hxy) Hx).
  - exact (proj2 (@proper_morphism _ _ _ _ S x y Hxy) Hx).
Defined.

(* The union respects 等价 sets subsets. （已译） *)
Lemma Powerset_union_respects@{o} {X : SetoidObject@{o o}}
  (SS TT : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X)))
  (H : SS ≈ TT) :
  Powerset_union_pred@{o} SS ≈ Powerset_union_pred@{o} TT.
Proof.
  intro x; split; intros [S [HS Hx]]; exists S; split; try exact Hx.
  - exact (proj1 (H S) HS).
  - exact (proj2 (H S) HS).
Qed.

(* μ_X : P(P X) → P X as an arrow of [Sets]. *)
Definition Powerset_union@{o} {X : SetoidObject@{o o}} :
  SetoidMorphism@{o o o} (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))
                         (Powerset_Prop_obj@{o} X) :=
  @Build_SetoidMorphism@{o o o}
    (carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X)))
    (is_setoid (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X)))
    (carrier (Powerset_Prop_obj@{o} X)) (is_setoid (Powerset_Prop_obj@{o} X))
    (λ SS, Powerset_union_pred@{o} SS) (@Powerset_union_respects@{o} X).

(* ------------------------------------------------------------------------ *)
(** ** The monad laws, pointwise *)

(* 相关说明。 （已译） *)
Lemma Powerset_union_assoc@{o} {X : SetoidObject@{o o}}
  (SSS : carrier (Powerset_Prop_obj@{o}
                    (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X)))) :
  Powerset_union_pred@{o} (Powerset_Prop_image@{o} Powerset_union@{o} SSS)
    ≈ Powerset_union_pred@{o} (Powerset_union_pred@{o} SSS).
Proof.
  intro x; split.
  - intros [S [HS Hx]]. hnf in HS. apply HS; intros [SS [HSS HSSS]].
    destruct (proj2 (HSSS x) Hx) as [T [HT HTx]].
    exists T; split; [ exists SS; split; assumption | exact HTx ].
  - intros [S [[SS [HSS HSS']] Hx]].
    exists (Powerset_union_pred@{o} SS); split.
    + apply Powerset_squash_intro. exists SS. split; [ exact HSS | ].
      reflexivity.
    + exists S; split; assumption.
Qed.

(* 相关说明。 （已译） *)
Lemma Powerset_union_image_singleton@{o} {X : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  Powerset_union_pred@{o}
    (Powerset_Prop_image@{o} (@Powerset_Prop_singleton_map@{o} X) S) ≈ S.
Proof.
  intro x; split.
  - intros [T [HT Hx]]. hnf in HT. apply HT; intros [y [Hy HyT]].
    assert (Hyx : Powerset_squash@{o} (@equiv _ (is_setoid X) y x))
      by exact (proj2 (HyT x) Hx).
    apply Hyx; intro E. exact (proj1 (@proper_morphism _ _ _ _ S y x E) Hy).
  - intro Hx. exists (Powerset_Prop_singleton_pred@{o} x); split.
    + apply Powerset_squash_intro. exists x; split; [ exact Hx | ].
      reflexivity.
    + apply Powerset_squash_intro; reflexivity.
Qed.

(* 相关说明。 （已译） *)
Lemma Powerset_union_singleton@{o} {X : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  Powerset_union_pred@{o} (Powerset_Prop_singleton_pred@{o} S) ≈ S.
Proof.
  intro x; split.
  - intros [T [HT Hx]]. hnf in HT. apply HT; intro E.
    exact (proj2 (E x) Hx).
  - intro Hx. exists S; split; [ apply Powerset_squash_intro | exact Hx ].
    reflexivity.
Qed.

(* 相关说明。 （已译） *)
Lemma Powerset_union_natural@{o} {X Y : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} X Y)
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))) :
  Powerset_union_pred@{o} (Powerset_Prop_image@{o} (Powerset_Prop_map@{o} f) SS)
    ≈ Powerset_Prop_image@{o} f (Powerset_union_pred@{o} SS).
Proof.
  intro y; split.
  - intros [T [HT Hy]]. hnf in HT. apply HT; intros [S [HS E]].
    assert (Hy' : Powerset_Prop_image@{o} f S y) by exact (proj2 (E y) Hy).
    hnf in Hy'. apply Hy'; intros [x [Hx Hfx]].
    apply Powerset_squash_intro.
    exists x; split; [ exists S; split; assumption | exact Hfx ].
  - intro H. hnf in H. apply H; intros [x [[S [HS Hx]] Hfx]].
    exists (Powerset_Prop_image@{o} f S); split.
    + apply Powerset_squash_intro. exists S; split; [ exact HS | ].
      reflexivity.
    + apply Powerset_squash_intro. exists x; split; assumption.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** The monad *)

Definition Powerset_Monad@{o so} : @Monad Sets@{o so} Powerset_Prop@{o so}.
Proof.
  unshelve refine
    (@Build_Monad Sets@{o so} Powerset_Prop@{o so}
       (fun X => @transform _ _ _ _ Powerset_Prop_Singleton@{o so} X)
       (fun X => @Powerset_union@{o} X) _ _ _ _ _).
  - intros X Y f.
    exact (@naturality_sym _ _ _ _ Powerset_Prop_Singleton@{o so} X Y f).
  - intros X SSS. exact (Powerset_union_assoc@{o} SSS).
  - intros X S. exact (Powerset_union_image_singleton@{o} S).
  - intros X S. exact (Powerset_union_singleton@{o} S).
  - intros X Y f SS. exact (Powerset_union_natural@{o} f SS).
Defined.

(* ------------------------------------------------------------------------ *)
(** ** Readbacks *)

Example Powerset_Monad_obj@{o so} (X : SetoidObject@{o o}) :
  fobj[Powerset_Prop@{o so}] X = Powerset_Prop_obj@{o} X := eq_refl.

Example Powerset_Monad_map@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) :
  fmap[Powerset_Prop@{o so}] f = Powerset_Prop_map@{o} f := eq_refl.

Example Powerset_Monad_ret@{o so} (X : SetoidObject@{o o}) :
  @ret _ _ Powerset_Monad@{o so} X
    = transform[Powerset_Prop_Singleton@{o so}] X := eq_refl.

Example Powerset_Monad_ret_map@{o so} (X : SetoidObject@{o o}) :
  @ret _ _ Powerset_Monad@{o so} X = @Powerset_Prop_singleton_map@{o} X
  := eq_refl.

Example Powerset_Monad_ret_at@{o so} (X : SetoidObject@{o o})
  (x : carrier X) :
  @ret _ _ Powerset_Monad@{o so} X x = Powerset_Prop_singleton_pred@{o} x
  := eq_refl.

Example Powerset_Monad_join@{o so} (X : SetoidObject@{o o}) :
  @join _ _ Powerset_Monad@{o so} X = @Powerset_union@{o} X := eq_refl.

Example Powerset_Monad_join_at@{o so} (X : SetoidObject@{o o})
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X)))
  (x : carrier X) :
  @join _ _ Powerset_Monad@{o so} X SS x
    = ex (fun S : carrier (Powerset_Prop_obj@{o} X) => SS S /\ S x)
  := eq_refl.

Example Powerset_Monad_map_at@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) (S : carrier (Powerset_Prop_obj@{o} X))
  (y : carrier Y) :
  fmap[Powerset_Prop@{o so}] f S y
    = Powerset_squash@{o}
        (∃ x : carrier X, S x ∧ @equiv _ (is_setoid Y) (f x) y) := eq_refl.

Example Powerset_Monad_ret_member@{o so} (X : SetoidObject@{o o})
  (x z : carrier X) :
  @ret _ _ Powerset_Monad@{o so} X x z
    = Powerset_squash@{o} (@equiv _ (is_setoid X) x z) := eq_refl.

(* The formability statement Instance/Sets/Powerset.v entered this
 单子 now inhabited, 单子 above. （已译） *)
Example Powerset_Monad_statement@{u so o} :
  Powerset_Prop_Monad_statement@{u so o} := Powerset_Monad@{o so}.
