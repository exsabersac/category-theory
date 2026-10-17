Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Strong.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Eilenberg.Moore.Limit.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Limit.Terminal.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Sets.
Require Import Category.Instance.One.

Generalizable All Variables.

(** * A hypothesis-free instantiation of created limits *)

(*
   本文件给出例子。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition IdC : Coq ⟶ Coq := Id[Coq].

Definition Kempty : 0 ⟶ @EilenbergMoore Coq IdC (@Id_Monad Coq) :=
  From_0 _.

(* The terminal object of [Coq], read as the limit of the empty diagram. *)

Definition Lbelow : Limit (EM_Forget IdC ◯ Kempty) :=
  snd (Terminal_Limit Coq (EM_Forget IdC ◯ Kempty)) Coq_Terminal.

(* The created lift, and the fact that it is limiting. *)

Definition created_terminal_algebra :
  IsALimit Kempty (em_apex IdC Kempty Lbelow) :=
  em_created IdC Kempty Lbelow.

(* The carrier of the created algebra is the apex of the limit downstairs,
   definitionally: [EM_Forget]'s object map is the first projection. *)

Definition created_carrier :
  `1 (em_apex IdC Kempty Lbelow) = vertex_obj[Lbelow] := eq_refl.

(* Terminality upstairs, read back through the empty-diagram theorem. *)

Definition created_terminal :
  @Terminal (@EilenbergMoore Coq IdC (@Id_Monad Coq)) :=
  fst (Terminal_Limit _ Kempty)
    {| limit_cone := em_cone IdC Kempty Lbelow
     ; ump_limits := @ump_limit _ _ _ _ (em_created IdC Kempty Lbelow) |}.

(** ** Mac Lane's "exactly one pair", on the nose: refuted *)

(*
   本节说明单子、（余）极限、Eilenberg–Moore相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Bool2@{o p} : SetoidObject@{o p} :=
  {| carrier := bool
   ; is_setoid :=
       {| equiv := fun _ _ => True
        ; setoid_equiv :=
            {| Equivalence_Reflexive := fun _ => I
             ; Equivalence_Symmetric := fun _ _ _ => I
             ; Equivalence_Transitive := fun _ _ _ _ _ => I |} |} |}.

Definition IdS@{o so} : Sets@{o so} ⟶ Sets@{o so} := Id[Sets@{o so}].

Definition IdSM@{o so} : @Monad Sets@{o so} IdS@{o so}.
Proof.
  unshelve refine (@Build_Monad Sets@{o so} IdS@{o so}
    (fun _ => id) (fun _ => id) _ _ _ _ _);
    intros; intro; reflexivity.
Defined.

Definition EMS@{o so} : Category@{so o o} :=
  @EilenbergMoore Sets@{o so} IdS@{o so} IdSM@{o so}.

Definition alg_of@{o so} (f : bool → bool) :
  @TAlgebra Sets@{o so} IdS@{o so} IdSM@{o so}
    Bool2@{o o} :=
  @Build_TAlgebra Sets@{o so} IdS@{o so} IdSM@{o so}
    Bool2@{o o}
    (@Build_SetoidMorphism bool (is_setoid Bool2@{o o}) bool
       (is_setoid Bool2@{o o}) f (fun _ _ _ => I))
    (fun _ => I) (fun _ => I).

Definition A_id@{o so} : EMS@{o so} :=
  existT _ Bool2@{o o} (alg_of@{o so} (fun b => b)).

Definition A_true@{o so} : EMS@{o so} :=
  existT _ Bool2@{o o} (alg_of@{o so} (fun _ => true)).

Lemma A_id_ne_A_true@{o so} : A_id@{o so} = A_true@{o so} → False.
Proof.
  intro E.
  pose (P := fun a : EMS@{o so} => ∀ x : carrier (`1 a),
         (let f : SetoidMorphism (`1 a) (`1 a) := t_alg[`2 a] in f x) = x).
  assert (HP : P A_true) by (destruct E; intro x; reflexivity).
  specialize (HP false).
  change (@eq bool true false) in HP.
  discriminate HP.
Qed.

Definition K1@{j o so} : _1@{j o o} ⟶ EMS@{o so} :=
  @Build_Functor _1 EMS (fun _ => A_id) (fun _ _ _ => id)
    (fun _ _ _ _ _ _ => I) (fun _ _ => I) (fun _ _ _ _ _ _ => I).

Definition N1@{j o so} : Cone (EM_Forget IdS@{o so} ◯ K1@{j o so}) :=
  @Build_Cone _1 Sets (EM_Forget IdS ◯ K1) Bool2
    (@Build_ACone _1 Sets Bool2 (EM_Forget IdS ◯ K1) (fun _ => id)
       (fun _ _ _ _ => I)).

Definition N1_limiting@{l l0 j o so} : IsLimitCone@{l l0 j o so} N1@{j o so}.
Proof.
  intro M.
  unshelve refine (@Build_Unique _ _ _
    (@Build_SetoidMorphism _ _ _ (is_setoid Bool2) (fun _ => true)
       (fun _ _ _ => I)) _ _);
    repeat intro; exact I.
Defined.

Definition leg_id_from@{o so} (f : bool → bool) :
  existT _ Bool2@{o o} (alg_of@{o so} f) ~{EMS@{o so}}~> A_id@{o so} :=
  @Build_TAlgebraHom Sets IdS IdSM@{o so} Bool2 Bool2
    (alg_of f) (alg_of (fun b => b)) id (fun _ => I).

Definition lift1_at@{j o so} (a : EMS@{o so})
  (p : EM_Forget IdS a = vertex_obj[N1@{j o so}])
  (leg : a ~{EMS}~> A_id)
  (Hleg : hom_rew p (fmap[EM_Forget IdS] leg)
            ≈ (id : Bool2 ~{Sets}~> Bool2)) :
  StrictLift K1@{j o so} (EM_Forget IdS) N1@{j o so} :=
  @Build_StrictLift _1 EMS Sets K1 (EM_Forget IdS) N1
    (@Build_Cone _1 EMS K1 a
       (@Build_ACone _1 EMS a K1 (fun _ => leg) (fun _ _ _ _ => I)))
    p (fun _ => Hleg).

(*
   本节说明单子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition em_lift_alg_unique_Sets@{l l0 j o so} (f : bool → bool) :=
  em_lift_alg_unique@{so o j so so l l0} IdS K1 N1 N1_limiting@{l l0 j o so}
    (lift1_at (existT _ Bool2 (alg_of f)) eq_refl (leg_id_from f)
       (fun _ => I)).

Theorem em_lift_not_unique_leibniz@{l l0 j o so} :
  (∀ τ : Cone (EM_Forget IdS@{o so} ◯ K1@{j o so}),
     IsLimitCone@{l l0 j o so} τ →
     ∀ (σ σ' : Cone K1@{j o so})
       (p : EM_Forget IdS (vertex_obj[σ]) = vertex_obj[τ])
       (p' : EM_Forget IdS (vertex_obj[σ']) = vertex_obj[τ]),
       (∀ x, hom_rew p (fmap[EM_Forget IdS] (cone_leg σ x)) = cone_leg τ x) →
       (∀ x, hom_rew p' (fmap[EM_Forget IdS] (cone_leg σ' x))
               = cone_leg τ x) →
       vertex_obj[σ] = vertex_obj[σ']) → False.
Proof.
  intro U.
  apply A_id_ne_A_true.
  exact (U N1 N1_limiting
           (slift_cone (lift1_at A_id eq_refl (leg_id_from (fun b => b))
                          (fun _ => I)))
           (slift_cone (lift1_at A_true eq_refl (leg_id_from (fun _ => true))
                          (fun _ => I)))
           eq_refl eq_refl (fun _ => eq_refl) (fun _ => eq_refl)).
Qed.

Definition lift1_limiting@{l l0 j o so} (f : bool → bool) :
  IsLimitCone@{l l0 j o so}
    (slift_cone (lift1_at@{j o so} (existT _ Bool2 (alg_of f)) eq_refl
                   (leg_id_from f) (fun _ => I))).
Proof.
  intro M.
  unshelve refine (@Build_Unique _ _ _
    (@Build_TAlgebraHom Sets IdS IdSM@{o so} _ Bool2 _
       (alg_of f)
       (@Build_SetoidMorphism _ _ _ (is_setoid Bool2) (fun _ => true)
          (fun _ _ _ => I))
       (fun _ => I)) _ _);
    repeat intro; exact I.
Defined.

Theorem em_limiting_lift_not_unique_leibniz@{l l0 j o so} :
  (∀ τ : Cone (EM_Forget IdS@{o so} ◯ K1@{j o so}),
     IsLimitCone@{l l0 j o so} τ →
     ∀ (σ σ' : Cone K1@{j o so})
       (p : EM_Forget IdS (vertex_obj[σ]) = vertex_obj[τ])
       (p' : EM_Forget IdS (vertex_obj[σ']) = vertex_obj[τ]),
       (∀ x, hom_rew p (fmap[EM_Forget IdS] (cone_leg σ x)) = cone_leg τ x) →
       (∀ x, hom_rew p' (fmap[EM_Forget IdS] (cone_leg σ' x))
               = cone_leg τ x) →
       IsLimitCone@{l l0 j o so} σ → IsLimitCone@{l l0 j o so} σ' →
       vertex_obj[σ] = vertex_obj[σ']) → False.
Proof.
  intro U.
  apply A_id_ne_A_true.
  exact (U N1 N1_limiting
           (slift_cone (lift1_at A_id eq_refl (leg_id_from (fun b => b))
                          (fun _ => I)))
           (slift_cone (lift1_at A_true eq_refl (leg_id_from (fun _ => true))
                          (fun _ => I)))
           eq_refl eq_refl (fun _ => eq_refl) (fun _ => eq_refl)
           (lift1_limiting (fun b => b)) (lift1_limiting (fun _ => true))).
Qed.
