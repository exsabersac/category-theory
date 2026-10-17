(** * Complete semilattices: the free ones, [Prop], and the chain 0 < 1 *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Monad.
Require Import Category.Instance.SupLat.
Require Import Category.Instance.SupLat.Free.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/suplattice
 nLab: https://ncatlab.org/nlab/show/weak+excluded+middle

   本文件给出实例例子。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** P X, the free complete semilattice *)

Example FreeSL_set@{o} (X : SetoidObject@{o o}) :
  sl_set (FreeSL@{o} X) = Powerset_Prop_obj@{o} X := eq_refl.

Example FreeSL_le@{o} (X : SetoidObject@{o o})
  (S T : carrier (Powerset_Prop_obj@{o} X)) :
  sl_le (FreeSL@{o} X) S T = (∀ z, S z → T z) := eq_refl.

Example FreeSL_sup@{o} (X : SetoidObject@{o o}) :
  sl_sup (FreeSL@{o} X) = @Powerset_union@{o} X := eq_refl.

(* (c) at P X has the structure map of the free algebra (P X, μ_X); as a
   whole algebra it is refused (E3 of Test/ProbeSupLat466.v). *)
Example FreeSL_alg@{o so} (X : SetoidObject@{o o}) :
  t_alg[projT2 (fobj[SupLat_to_EM@{o so}] (FreeSL@{o} X))]
    = t_alg[projT2 (fobj[@EM_Free Sets@{o so} Powerset_Prop@{o so}
                          Powerset_Monad@{o so}] X)] := eq_refl.

(* (b) at the free algebra: Mac Lane's order S ∪ T ≈ T is inclusion.  The
   free algebra's structure map is (c)'s at [FreeSL X] by conversion
   ([FreeSL_alg]) and the order reads only that map, so this is
   Instance/SupLat.v's [sl_talg_le_iff] there. *)
Lemma FreeSL_talg_le_iff@{o so} (X : SetoidObject@{o o})
  (S T : carrier (Powerset_Prop_obj@{o} X)) :
  iff (sl_le (fobj[EM_to_SupLat@{o so}]
                (fobj[@EM_Free Sets@{o so} Powerset_Prop@{o so}
                        Powerset_Monad@{o so}] X)) S T)
      (sl_le (FreeSL@{o} X) S T).
Proof. exact (sl_talg_le_iff@{o so} (FreeSL@{o} X) S T). Qed.

(* The universal property of P X, elementwise: a map ψ into a complete
   semilattice extends along the singletons, and uniquely so. *)
Lemma FreeSL_extend_singleton@{o so} {X : SetoidObject@{o o}}
  {A : SupLatObject@{o}} (ψ : X ~{Sets@{o so}}~> sl_set A) (x : carrier X) :
  @equiv _ (is_setoid (sl_set A))
    (slh_map (SL_extend@{o so} ψ) (Powerset_Prop_singleton_pred@{o} x)) (ψ x).
Proof. exact (@iso_to_from _ _ _ (SL_adj_iso@{o so} X A) ψ x). Qed.

Lemma FreeSL_extend_unique@{o so} {X : SetoidObject@{o o}}
  {A : SupLatObject@{o}} (φ : SupLatHom@{o} (FreeSL@{o} X) A)
  (ψ : X ~{Sets@{o so}}~> sl_set A)
  (H : ∀ x, @equiv _ (is_setoid (sl_set A))
              (slh_map φ (Powerset_Prop_singleton_pred@{o} x)) (ψ x))
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  @equiv _ (is_setoid (sl_set A)) (slh_map φ S)
    (slh_map (SL_extend@{o so} ψ) S).
Proof.
  transitivity (slh_map (SL_extend@{o so} (SL_restrict@{o so} φ)) S).
  - symmetry. exact (@iso_from_to _ _ _ (SL_adj_iso@{o so} X A) φ S).
  - exact (@proper_morphism _ _ _ _
             (@from _ _ _ (SL_adj_iso@{o so} X A))
             (SL_restrict@{o so} φ) ψ H S).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Prop, which is P 1 *)

(* sup S := ∃ Q ∈ S, Q. *)
Definition Prop_sup@{o} :
  SetoidMorphism@{o o o}
    (Powerset_Prop_obj@{o} Powerset_Prop_truth@{o}) Powerset_Prop_truth@{o}.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier (Powerset_Prop_obj@{o} Powerset_Prop_truth@{o}))
       (is_setoid (Powerset_Prop_obj@{o} Powerset_Prop_truth@{o}))
       Prop (is_setoid Powerset_Prop_truth@{o})
       (λ S, ex (fun Q : Prop => S Q /\ Q)) _).
  intros S T E; split; intros [Q [HQ q]]; exists Q; split; try exact q.
  - exact (proj1 (E Q) HQ).
  - exact (proj2 (E Q) HQ).
Defined.

(* Prop under implication, the complete semilattice of truth values. *)
Definition Prop_SupLat@{o} : SupLatObject@{o}.
Proof.
  unshelve refine
    (@Build_SupLatObject@{o} Powerset_Prop_truth@{o}
       (λ P Q : Prop, P → Q) _ _ _ _ Prop_sup@{o} _ _).
  - intros P p; exact p.
  - intros P Q R f g p; exact (g (f p)).
  - intros P P' Q Q' EP EQ f p. exact (proj1 EQ (f (proj2 EP p))).
  - intros P Q f g; split; assumption.
  - intros S P HP p. exists P; split; assumption.
  - intros S Q H [P [HP p]]. exact (H P HP p).
Defined.

Example Prop_SupLat_le@{o} (P Q : Prop) :
  sl_le Prop_SupLat@{o} P Q = (P → Q) := eq_refl.

Example Prop_SupLat_sup@{o}
  (S : carrier (Powerset_Prop_obj@{o} Powerset_Prop_truth@{o})) :
  sl_sup Prop_SupLat@{o} S = ex (fun Q : Prop => S Q /\ Q) := eq_refl.

(* Two comparable points that are not equal: False ≤ True. *)
Lemma Prop_SupLat_nontrivial@{o} :
  sl_le Prop_SupLat@{o} False True
  * (@equiv _ (is_setoid (sl_set Prop_SupLat@{o})) True False → False).
Proof.
  split.
  - intros f; destruct f.
  - intros [H _]. exact (H I).
Qed.

(* The one-point set, and the constant subsets on it. *)
Definition Prop_to_P1_pred@{o} (Q : Prop) :
  carrier (Powerset_Prop_obj@{o} unit_setoid_object@{o o}).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o} poly_unit@{o} unit_setoid@{o o}
       Prop (is_setoid Powerset_Prop_truth@{o}) (λ _, Q) _).
  intros u v _; split; intro q; exact q.
Defined.

Definition Prop_to_P1@{o} :
  SupLatHom@{o} Prop_SupLat@{o} (FreeSL@{o} unit_setoid_object@{o o}).
Proof.
  unshelve refine
    (@Build_SupLatHom@{o} Prop_SupLat@{o}
       (FreeSL@{o} unit_setoid_object@{o o})
       (@Build_SetoidMorphism@{o o o} Prop (is_setoid Powerset_Prop_truth@{o})
          (carrier (Powerset_Prop_obj@{o} unit_setoid_object@{o o}))
          (is_setoid (Powerset_Prop_obj@{o} unit_setoid_object@{o o}))
          Prop_to_P1_pred@{o} _) _).
  - intros P Q E u. exact E.
  - intros S u; split.
    + intros [Q [HQ q]]. exists (Prop_to_P1_pred@{o} Q); split; [ | exact q ].
      apply Powerset_squash_intro. exists Q; split; [ exact HQ | ].
      intro v; split; intro r; exact r.
    + intros [T [HT t]]. apply HT; intros [Q [HQ E]].
      exists Q; split; [ exact HQ | exact (proj2 (E u) t) ].
Defined.

Definition P1_to_Prop@{o} :
  SupLatHom@{o} (FreeSL@{o} unit_setoid_object@{o o}) Prop_SupLat@{o}.
Proof.
  unshelve refine
    (@Build_SupLatHom@{o} (FreeSL@{o} unit_setoid_object@{o o})
       Prop_SupLat@{o}
       (@Build_SetoidMorphism@{o o o}
          (carrier (Powerset_Prop_obj@{o} unit_setoid_object@{o o}))
          (is_setoid (Powerset_Prop_obj@{o} unit_setoid_object@{o o}))
          Prop (is_setoid Powerset_Prop_truth@{o})
          (λ T, T ttt) _) _).
  - intros S T E. exact (E ttt).
  - intros SS; split.
    + intros [T [HT t]]. exists (T ttt); split; [ | exact t ].
      apply Powerset_squash_intro. exists T; split; [ exact HT | ].
      split; intro r; exact r.
    + intros [Q [HQ q]]. apply HQ; intros [T [HT E]].
      exists T; split; [ exact HT | exact (proj2 E q) ].
Defined.

(* Prop = P 1, as an isomorphism of complete semilattices. *)
Definition Prop_P1_iso@{o so} :
  @Isomorphism SupLat@{o so} Prop_SupLat@{o}
    (FreeSL@{o} unit_setoid_object@{o o}).
Proof.
  unshelve refine
    (@Build_Isomorphism SupLat@{o so} Prop_SupLat@{o}
       (FreeSL@{o} unit_setoid_object@{o o}) Prop_to_P1@{o} P1_to_Prop@{o}
       _ _).
  - intros T u. destruct u.
    split; intro r; exact r.
  - intros Q. split; intro r; exact r.
Defined.

(* Q goes to the constant subset Q, and back to Q itself. *)
Example Prop_to_P1_at@{o} (Q : Prop) (u : poly_unit@{o}) :
  slh_map Prop_to_P1@{o} Q u = Q := eq_refl.

Example Prop_P1_round_trip@{o} (Q : Prop) :
  slh_map P1_to_Prop@{o} (slh_map Prop_to_P1@{o} Q) = Q := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Two comparable points decide ¬Q or ¬¬Q *)

(* The subset { x | Q ∧ x ≈ top }. *)
Definition two_points_probe@{o} (A : SupLatObject@{o})
  (top : carrier (sl_set A)) (Q : Prop) :
  carrier (Powerset_Prop_obj@{o} (sl_set A)).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier (sl_set A)) (is_setoid (sl_set A)) Prop
       (is_setoid Powerset_Prop_truth@{o})
       (λ x, Q /\ Powerset_squash@{o} (@equiv _ (is_setoid (sl_set A)) top x))
       _).
  intros x y E; split; intros [q H]; split; try exact q;
    intros R k; apply H; intro e; apply k.
  - now transitivity x.
  - transitivity y; [ exact e | now symmetry ].
Defined.

(* A complete semilattice with a decidable ≈ and two points bot ≤ top that
   are not equal decides, for every proposition Q, ¬Q or ¬¬Q: sup of the
   probe is top when Q holds and bot-or-below when it does not. *)
Theorem suplat_two_points_WLEM@{o} (A : SupLatObject@{o})
  (bot top : carrier (sl_set A)) (Hle : sl_le A bot top)
  (Hne : @equiv _ (is_setoid (sl_set A)) top bot → False)
  (Hdec : ∀ x y, @equiv _ (is_setoid (sl_set A)) x y
                 + (@equiv _ (is_setoid (sl_set A)) x y → False))
  (Q : Prop) : (~ Q) + (~ ~ Q).
Proof.
  destruct (Hdec (sl_sup A (two_points_probe@{o} A top Q)) top) as [E|N].
  - right. intro nQ. apply Hne. apply sl_antisym; [ | exact Hle ].
    apply (sl_le_respects A (sl_sup A (two_points_probe@{o} A top Q)) top
             bot bot E (reflexivity bot)).
    apply sl_sup_least. intros x [q _]. contradiction.
  - left. intro q. apply N. apply sl_antisym.
    + apply sl_sup_least. intros x [_ H]. apply H; intro e.
      exact (sl_le_respects A top x top top e (reflexivity top)
               (sl_le_refl A top)).
    + apply sl_sup_ub. split; [ exact q | ].
      exact (Powerset_squash_intro (reflexivity top)).
Qed.

(* Prop satisfies every hypothesis but the decidability of ≈, and with it
   the theorem gives informative weak excluded middle. *)
Corollary Prop_SupLat_decidable_WLEM@{o}
  (Hdec : ∀ P Q : Prop, @equiv _ (is_setoid (sl_set Prop_SupLat@{o})) P Q
                        + (@equiv _ (is_setoid (sl_set Prop_SupLat@{o})) P Q
                           → False))
  (Q : Prop) : (~ Q) + (~ ~ Q).
Proof.
  destruct Prop_SupLat_nontrivial@{o} as [Hle Hne].
  exact (suplat_two_points_WLEM@{o} Prop_SupLat@{o} False True Hle Hne Hdec Q).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** The chain false ≤ true on [bool] *)

(* The carrier is Instance/Sets.v's two-element setoid [bool_setoid_object],
   compared by [eq]. *)
Definition bool_chain_le@{} (b c : bool) : Prop := b = true → c = true.

(* The chain with a given supremum operator: its four order axioms, proved
   once for the two uses below. *)
Definition bool_chain_SupLat@{o}
  (sup : SetoidMorphism@{o o o}
           (Powerset_Prop_obj@{o} bool_setoid_object@{o o})
           bool_setoid_object@{o o})
  (ub : ∀ (S : carrier (Powerset_Prop_obj@{o} bool_setoid_object@{o o}))
          (x : bool), S x → bool_chain_le x (sup S))
  (least : ∀ (S : carrier (Powerset_Prop_obj@{o} bool_setoid_object@{o o}))
             (y : bool),
             (∀ x : bool, S x → bool_chain_le x y) → bool_chain_le (sup S) y) :
  SupLatObject@{o}.
Proof.
  unshelve refine
    (@Build_SupLatObject@{o} bool_setoid_object@{o o} bool_chain_le
       _ _ _ _ sup ub least).
  - intros x H; exact H.
  - intros x y z H1 H2 H; exact (H2 (H1 H)).
  - intros x x' y y' Ex Ey H. destruct Ex, Ey. exact H.
  - intros [|] [|] H1 H2; try reflexivity.
    + exact (eq_sym (H1 eq_refl)).
    + exact (H2 eq_refl).
Defined.

(* Any sup operator for this order on bool gives informative weak
   excluded middle. *)
Theorem bool_SupLat_WLEM@{o}
  (sup : SetoidMorphism@{o o o}
           (Powerset_Prop_obj@{o} bool_setoid_object@{o o})
           bool_setoid_object@{o o})
  (ub : ∀ (S : carrier (Powerset_Prop_obj@{o} bool_setoid_object@{o o}))
          (x : bool), S x → bool_chain_le x (sup S))
  (least : ∀ (S : carrier (Powerset_Prop_obj@{o} bool_setoid_object@{o o}))
             (y : bool),
             (∀ x : bool, S x → bool_chain_le x y) → bool_chain_le (sup S) y)
  (Q : Prop) : (~ Q) + (~ ~ Q).
Proof.
  unshelve refine
    (suplat_two_points_WLEM@{o} (bool_chain_SupLat@{o} sup ub least)
       false true _ _ _ Q).
  - intro H; discriminate H.
  - intro H; discriminate H.
  - intros [|] [|]; (left; reflexivity) || (right; intro H; discriminate H).
Qed.

(* Conversely, under informative weak excluded middle the chain IS a
   complete semilattice, with sup S = true exactly when ¬¬(true ∈ S). *)
Definition bool_chain_sup_fun@{o}
  (wlem : ∀ Q : Prop, (~ Q) + (~ ~ Q))
  (S : carrier (Powerset_Prop_obj@{o} bool_setoid_object@{o o})) : bool :=
  match wlem (S true) with inl _ => false | inr _ => true end.

Lemma bool_chain_sup_true@{o} (wlem : ∀ Q : Prop, (~ Q) + (~ ~ Q))
  (S : carrier (Powerset_Prop_obj@{o} bool_setoid_object@{o o})) :
  bool_chain_sup_fun@{o} wlem S = true → ~ ~ S true.
Proof.
  unfold bool_chain_sup_fun; destruct (wlem (S true)) as [n|n];
    [ intro H; discriminate H | intros _; exact n ].
Qed.

Lemma bool_chain_sup_false@{o} (wlem : ∀ Q : Prop, (~ Q) + (~ ~ Q))
  (S : carrier (Powerset_Prop_obj@{o} bool_setoid_object@{o o})) :
  bool_chain_sup_fun@{o} wlem S = false → ~ S true.
Proof.
  unfold bool_chain_sup_fun; destruct (wlem (S true)) as [n|n];
    [ intros _; exact n | intro H; discriminate H ].
Qed.

Definition bool_chain_sup@{o} (wlem : ∀ Q : Prop, (~ Q) + (~ ~ Q)) :
  SetoidMorphism@{o o o}
    (Powerset_Prop_obj@{o} bool_setoid_object@{o o})
    bool_setoid_object@{o o}.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o} _
       (is_setoid (Powerset_Prop_obj@{o} bool_setoid_object@{o o}))
       bool (is_setoid bool_setoid_object@{o o})
       (bool_chain_sup_fun@{o} wlem) _).
  intros S T E.
  destruct (bool_chain_sup_fun@{o} wlem S) eqn:HS,
           (bool_chain_sup_fun@{o} wlem T) eqn:HT; try reflexivity.
  - destruct (bool_chain_sup_true@{o} wlem S HS
                (fun s =>
                   bool_chain_sup_false@{o} wlem T HT (proj1 (E true) s))).
  - destruct (bool_chain_sup_true@{o} wlem T HT
                (fun t =>
                   bool_chain_sup_false@{o} wlem S HS (proj2 (E true) t))).
Defined.

Definition bool_SupLat@{o} (wlem : ∀ Q : Prop, (~ Q) + (~ ~ Q)) :
  SupLatObject@{o}.
Proof.
  unshelve refine (bool_chain_SupLat@{o} (bool_chain_sup@{o} wlem) _ _).
  - intros S [|] Hx Ht; [ | discriminate Ht ].
    change (bool_chain_sup_fun@{o} wlem S = true).
    destruct (bool_chain_sup_fun@{o} wlem S) eqn:HS; [ reflexivity | ].
    destruct (bool_chain_sup_false@{o} wlem S HS Hx).
  - intros S [|] Hub H; [ reflexivity | ].
    destruct (bool_chain_sup_true@{o} wlem S H
                (fun s => ltac:(discriminate (Hub true s eq_refl)))).
Defined.
