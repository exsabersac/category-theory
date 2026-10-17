(*
   本文件为测试：ProbeEMCreates467。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Monad.Eilenberg.Moore.Limit.
Require Import Category.Monad.Strong.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Limit.Terminal.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Sets.
Require Import Category.Instance.One.
Require Import Category.Monad.Eilenberg.Moore.Limit.Examples.

Generalizable All Variables.
(** ** The generic clauses *)

Example p467_c1_apex@{o h jo eo e l l0 s} {D : Category@{o h h}}
  (T : D ⟶ D) `{H : @Monad D T} {J : Category@{jo h h}}
  (K : J ⟶ EilenbergMoore@{eo o e h} T)
  (N : Cone (EM_Forget T ◯ K)) (HN : IsLimitCone@{l l0 jo h o} N) :
  EM_Forget T
    (vertex_obj[slift_cone (em_strict_lift@{o h jo h eo e l l0 s} T K N HN)])
    = vertex_obj[N] := eq_refl.

Example p467_c2_legs@{o h jo eo e l l0 s} {D : Category@{o h h}}
  (T : D ⟶ D) `{H : @Monad D T} {J : Category@{jo h h}}
  (K : J ⟶ EilenbergMoore@{eo o e h} T)
  (N : Cone (EM_Forget T ◯ K)) (HN : IsLimitCone@{l l0 jo h o} N) (j : J) :
  fmap[EM_Forget T]
    (cone_leg (slift_cone (em_strict_lift@{o h jo h eo e l l0 s} T K N HN)) j)
    = cone_leg N j := eq_refl.

Example p467_c2_legs_class@{o h jo eo e l l0 c c0} {D : Category@{o h h}}
  (T : D ⟶ D) `{H : @Monad D T} {J : Category@{jo h h}}
  (K : J ⟶ EilenbergMoore@{eo o e h} T)
  (N : Cone (EM_Forget T ◯ K)) (HN : IsLimitCone@{l l0 jo h o} N) (j : J) :
  fmap[EM_Forget T]
    (cone_leg (slift_cone (@screates _ _ _ _ _
       (em_forget_StrictlyCreatesLimit@{o h jo h eo e l l0 c c0} T K) N HN)) j)
    = cone_leg N j := eq_refl.

Example p467_c3_leg_family@{o h jo eo e l l0 s} {D : Category@{o h h}}
  (T : D ⟶ D) `{H : @Monad D T} {J : Category@{jo h h}}
  (K : J ⟶ EilenbergMoore@{eo o e h} T)
  (N : Cone (EM_Forget T ◯ K)) (HN : IsLimitCone@{l l0 jo h o} N) :
  (fun j => fmap[EM_Forget T]
     (cone_leg (slift_cone (em_strict_lift@{o h jo h eo e l l0 s} T K N HN))
        j))
    = (fun j => cone_leg N j) := eq_refl.

Example p467_c4_slift_eq@{o h jo eo e l l0 s} {D : Category@{o h h}}
  (T : D ⟶ D) `{H : @Monad D T} {J : Category@{jo h h}}
  (K : J ⟶ EilenbergMoore@{eo o e h} T)
  (N : Cone (EM_Forget T ◯ K)) (HN : IsLimitCone@{l l0 jo h o} N) :
  slift_eq (em_strict_lift@{o h jo h eo e l l0 s} T K N HN) = eq_refl
  := eq_refl.

Example p467_c5_structure@{o h jo eo e l} {D : Category@{o h h}}
  (T : D ⟶ D) `{H : @Monad D T} {J : Category@{jo h h}}
  (K : J ⟶ EilenbergMoore@{eo o e h} T)
  (L : Limit@{l jo h o} (EM_Forget T ◯ K)) :
  t_alg[`2 (em_apex T K L)]
    = limit_med (limit_is_alimit L) (em_act_cone T K L) := eq_refl.

Example p467_c6_iso_id@{o h jo eo e l l0 c c0} {D : Category@{o h h}}
  (T : D ⟶ D) `{H : @Monad D T} {J : Category@{jo h h}}
  (K : J ⟶ EilenbergMoore@{eo o e h} T)
  (N : Cone (EM_Forget T ◯ K)) (HN : IsLimitCone@{l l0 jo h o} N) :
  to `1 (@creates_lift_over _ _ _ _ _
           (em_forget_CreatesLimit@{o h jo h eo e l l0 c c0} T K) N HN)
    = id := eq_refl.

Example p467_c7_created_legs@{o h jo eo e l} {D : Category@{o h h}}
  (T : D ⟶ D) `{H : @Monad D T} {J : Category@{jo h h}}
  (K : J ⟶ EilenbergMoore@{eo o e h} T)
  (L : Limit@{l jo h o} (EM_Forget T ◯ K)) (j : J) :
  limit_leg (em_created T K L) j = em_leg T K L j := eq_refl.

Example p467_c8_record_but_coherence@{o h jo eo e l l0 s}
  {D : Category@{o h h}} (T : D ⟶ D) `{H : @Monad D T}
  {J : Category@{jo h h}} (K : J ⟶ EilenbergMoore@{eo o e h} T)
  (N : Cone (EM_Forget T ◯ K)) (HN : IsLimitCone@{l l0 jo h o} N) :
  @Build_Cone J D (EM_Forget T ◯ K)
    (vertex_obj[FCone (EM_Forget T)
       (slift_cone (em_strict_lift@{o h jo h eo e l l0 s} T K N HN))])
    (@Build_ACone J D _ (EM_Forget T ◯ K)
       (fun j => cone_leg (FCone (EM_Forget T)
          (slift_cone (em_strict_lift@{o h jo h eo e l l0 s} T K N HN))) j)
       (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N)))
    = N := eq_refl.

(* R1 *)
Fail Example p467_r1_fcone@{o h jo eo e l l0 s} {D : Category@{o h h}}
  (T : D ⟶ D) `{H : @Monad D T} {J : Category@{jo h h}}
  (K : J ⟶ EilenbergMoore@{eo o e h} T)
  (N : Cone (EM_Forget T ◯ K)) (HN : IsLimitCone@{l l0 jo h o} N) :
  FCone (EM_Forget T)
    (slift_cone (em_strict_lift@{o h jo h eo e l l0 s} T K N HN)) = N
  := eq_refl.

(** ** The counterexample *)

Example p467_e1_carriers@{o so} : `1 A_id@{o so} = `1 A_true@{o so}
  := eq_refl.

(* The instrument *)
Fail Example p467_instrument@{o so} : A_id@{o so} = A_true@{o so}
  := eq_refl.

Example p467_e2_legs@{o so} :
  fmap[EM_Forget IdS@{o so}] (leg_id_from@{o so} (fun _ => true))
    = fmap[EM_Forget IdS@{o so}] (leg_id_from@{o so} (fun b => b))
  := eq_refl.

Example p467_e3_lift_leg@{j o so} :
  hom_rew eq_refl
    (fmap[EM_Forget IdS@{o so}]
       (cone_leg (slift_cone (lift1_at@{j o so} A_true eq_refl
                                (leg_id_from (fun _ => true)) (fun _ => I)))
          ttt))
    = cone_leg N1@{j o so} ttt := eq_refl.

Example p467_e4_iso@{l l0 j o so} (f : bool → bool) :
  em_lift_alg_unique_Sets@{l l0 j o so} f
    = em_lift_alg_unique@{so o j so so l l0} IdS K1 N1
        N1_limiting@{l l0 j o so}
        (lift1_at (existT _ Bool2 (alg_of f)) eq_refl (leg_id_from f)
           (fun _ => I)) := eq_refl.

Example p467_e5_iso_id@{l l0 j o so} (f : bool → bool) :
  t_alg_hom[to `1 (em_lift_alg_unique_Sets@{l l0 j o so} f)] = id
  := eq_refl.

Example p467_e6_refutation@{l l0 j o so} :
  (∀ τ : Cone (EM_Forget IdS@{o so} ◯ K1@{j o so}),
     IsLimitCone@{l l0 j o so} τ →
     ∀ (σ σ' : Cone K1@{j o so})
       (p : EM_Forget IdS (vertex_obj[σ]) = vertex_obj[τ])
       (p' : EM_Forget IdS (vertex_obj[σ']) = vertex_obj[τ]),
       (∀ x, hom_rew p (fmap[EM_Forget IdS] (cone_leg σ x)) = cone_leg τ x) →
       (∀ x, hom_rew p' (fmap[EM_Forget IdS] (cone_leg σ' x))
               = cone_leg τ x) →
       vertex_obj[σ] = vertex_obj[σ']) → False
  := em_lift_not_unique_leibniz@{l l0 j o so}.

Example p467_e7_refutation_limiting@{l l0 j o so} :
  (∀ τ : Cone (EM_Forget IdS@{o so} ◯ K1@{j o so}),
     IsLimitCone@{l l0 j o so} τ →
     ∀ (σ σ' : Cone K1@{j o so})
       (p : EM_Forget IdS (vertex_obj[σ]) = vertex_obj[τ])
       (p' : EM_Forget IdS (vertex_obj[σ']) = vertex_obj[τ]),
       (∀ x, hom_rew p (fmap[EM_Forget IdS] (cone_leg σ x)) = cone_leg τ x) →
       (∀ x, hom_rew p' (fmap[EM_Forget IdS] (cone_leg σ' x))
               = cone_leg τ x) →
       IsLimitCone@{l l0 j o so} σ → IsLimitCone@{l l0 j o so} σ' →
       vertex_obj[σ] = vertex_obj[σ']) → False
  := em_limiting_lift_not_unique_leibniz@{l l0 j o so}.
