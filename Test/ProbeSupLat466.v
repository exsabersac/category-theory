(*
   本文件为测试：ProbeSupLat466。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Monad.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Equivalence.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Instance.Cat.
Require Import Category.Instance.SupLat.
Require Import Category.Theory.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Instance.SupLat.Free.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Instance.SupLat.Examples.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Sets.Powerset.Monad.Riehl.

Generalizable All Variables.

(* ------------------------------------------------------------------------ *)
(** ** The instrument *)

(* Control: the pair is commutative up to ≈. *)
Example p466_instrument_ctl@{o} {X : SetoidObject@{o o}} (x y : carrier X) :
  Powerset_Prop_pair@{o} x y ≈ Powerset_Prop_pair@{o} y x :=
  Powerset_Prop_pair_comm@{o} x y.

(* The instrument *)
Fail Example p466_instrument@{o} {X : SetoidObject@{o o}} (x y : carrier X) :
  Powerset_Prop_pair@{o} x y = Powerset_Prop_pair@{o} y x := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Instance/Sets/Powerset/Monad.v: the data *)

(* Controls: η is #227's singleton transformation and μ is the union. *)
Example p466_ret@{o so} (X : SetoidObject@{o o}) :
  @ret _ _ Powerset_Monad@{o so} X
    = transform[Powerset_Prop_Singleton@{o so}] X := eq_refl.

Example p466_join@{o so} (X : SetoidObject@{o o}) :
  @join _ _ Powerset_Monad@{o so} X = @Powerset_union@{o} X := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Instance/Sets/Powerset/Monad.v: the laws, at ≈ and not at eq_refl *)

(* Control: associativity at ≈. *)
Example p466_assoc_ctl@{o} {X : SetoidObject@{o o}}
  (SSS : carrier (Powerset_Prop_obj@{o}
                    (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X)))) :
  Powerset_union_pred@{o} (Powerset_Prop_image@{o} Powerset_union@{o} SSS)
    ≈ Powerset_union_pred@{o} (Powerset_union_pred@{o} SSS) :=
  Powerset_union_assoc@{o} SSS.

(* M3 *)
Fail Example p466_assoc_eq@{o} {X : SetoidObject@{o o}}
  (SSS : carrier (Powerset_Prop_obj@{o}
                    (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X)))) :
  Powerset_union_pred@{o} (Powerset_Prop_image@{o} Powerset_union@{o} SSS)
    = Powerset_union_pred@{o} (Powerset_union_pred@{o} SSS) := eq_refl.

(* Control: μ ∘ Pη ≈ id. *)
Example p466_unit_image_ctl@{o} {X : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  Powerset_union_pred@{o}
    (Powerset_Prop_image@{o} (@Powerset_Prop_singleton_map@{o} X) S) ≈ S :=
  Powerset_union_image_singleton@{o} S.

(* M4 *)
Fail Example p466_unit_image_eq@{o} {X : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  Powerset_union_pred@{o}
    (Powerset_Prop_image@{o} (@Powerset_Prop_singleton_map@{o} X) S) = S
  := eq_refl.

(* Control: μ ∘ ηP ≈ id. *)
Example p466_unit_singleton_ctl@{o} {X : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  Powerset_union_pred@{o} (Powerset_Prop_singleton_pred@{o} S) ≈ S :=
  Powerset_union_singleton@{o} S.

(* M5 *)
Fail Example p466_unit_singleton_eq@{o} {X : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  Powerset_union_pred@{o} (Powerset_Prop_singleton_pred@{o} S) = S
  := eq_refl.

(* Control: the naturality of η at a point, at ≈ (#227's field). *)
Example p466_ret_natural_ctl@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) (x : carrier X) :
  @ret _ _ Powerset_Monad@{o so} Y (f x)
    ≈ fmap[Powerset_Prop@{o so}] f (@ret _ _ Powerset_Monad@{o so} X x) :=
  @naturality_sym _ _ _ _ Powerset_Prop_Singleton@{o so} X Y f x.

(* M6 *)
Fail Example p466_ret_natural_eq@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) (x : carrier X) :
  @ret _ _ Powerset_Monad@{o so} Y (f x)
    = fmap[Powerset_Prop@{o so}] f (@ret _ _ Powerset_Monad@{o so} X x)
  := eq_refl.

(* Control: the naturality of μ at ≈. *)
Example p466_join_natural_ctl@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y)
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))) :
  @join _ _ Powerset_Monad@{o so} Y
      (fmap[Powerset_Prop@{o so}] (fmap[Powerset_Prop@{o so}] f) SS)
    ≈ fmap[Powerset_Prop@{o so}] f (@join _ _ Powerset_Monad@{o so} X SS)
  := Powerset_union_natural@{o} f SS.

(* M1 *)
Fail Example p466_join_natural_eq@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y)
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))) :
  @join _ _ Powerset_Monad@{o so} Y
      (fmap[Powerset_Prop@{o so}] (fmap[Powerset_Prop@{o so}] f) SS)
    = fmap[Powerset_Prop@{o so}] f (@join _ _ Powerset_Monad@{o so} X SS)
  := eq_refl.

(* M7 *)
Fail Example p466_join_natural_fun@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y)
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))) :
  (fun y => @join _ _ Powerset_Monad@{o so} Y
      (fmap[Powerset_Prop@{o so}] (fmap[Powerset_Prop@{o so}] f) SS) y)
    = (fun y => fmap[Powerset_Prop@{o so}] f
                  (@join _ _ Powerset_Monad@{o so} X SS) y)
  := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Instance/Sets/Powerset/Monad.v: the proof-relevant carrier *)

(* Control: the Prop-valued carrier's monad statement is formable. *)
Definition p466_prop_statement@{so o} : Type@{so} :=
  @Monad Sets@{o so} Powerset_Prop@{o so}.

(* M2 *)
Fail Definition p466_relevant_statement@{o so sso} : Type@{sso} :=
  @Monad Sets@{o so} Powerset@{o so sso}.

(* ------------------------------------------------------------------------ *)
(** ** Instance/SupLat.v: the round trip semilattice → algebra → semilattice *)

(* Controls: the carrier and the sup, at [eq_refl]; the order, logically. *)
Example p466_rt_set@{o so} (A : SupLatObject@{o}) :
  sl_set (fobj[EM_to_SupLat@{o so} ◯ SupLat_to_EM@{o so}] A) = sl_set A
  := eq_refl.

Example p466_rt_sup@{o so} (A : SupLatObject@{o}) :
  sl_sup (fobj[EM_to_SupLat@{o so} ◯ SupLat_to_EM@{o so}] A) = sl_sup A
  := eq_refl.

Example p466_rt_le_iff@{o so} (A : SupLatObject@{o})
  (x y : carrier (sl_set A)) :
  iff (sl_le (fobj[EM_to_SupLat@{o so} ◯ SupLat_to_EM@{o so}] A) x y)
      (sl_le A x y) := sl_talg_le_iff@{o so} A x y.

(* N1 *)
Fail Example p466_rt_obj@{o so} (A : SupLatObject@{o}) :
  fobj[EM_to_SupLat@{o so} ◯ SupLat_to_EM@{o so}] A = A := eq_refl.

(* N2 *)
Fail Example p466_rt_le@{o so} (A : SupLatObject@{o}) :
  sl_le (fobj[EM_to_SupLat@{o so} ◯ SupLat_to_EM@{o so}] A) = sl_le A
  := eq_refl.

(* N5b *)
Fail Example p466_rt_functor@{o so} :
  EM_to_SupLat@{o so} ◯ SupLat_to_EM@{o so} = Id[SupLat@{o so}] := eq_refl.

(* Controls: both fields of the hom round trip, at [eq_refl]. *)
Example p466_rt_hom_map@{o so} (A B : SupLatObject@{o})
  (f : SupLatHom@{o} A B) :
  slh_map (fmap[EM_to_SupLat@{o so} ◯ SupLat_to_EM@{o so}] f) = slh_map f
  := eq_refl.

Example p466_rt_hom_sup@{o so} (A B : SupLatObject@{o})
  (f : SupLatHom@{o} A B) :
  slh_sup (fmap[EM_to_SupLat@{o so} ◯ SupLat_to_EM@{o so}] f) = slh_sup f
  := eq_refl.

(* N6 *)
Fail Example p466_rt_hom@{o so} (A B : SupLatObject@{o})
  (f : SupLatHom@{o} A B) :
  fmap[EM_to_SupLat@{o so} ◯ SupLat_to_EM@{o so}] f = f := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Instance/SupLat.v: the round trip algebra → semilattice → algebra *)

(* Controls: the carrier and the structure map, at [eq_refl], at a
   variable object and at a named algebra. *)
Example p466_rt2_carrier@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) :
  projT1 (fobj[SupLat_to_EM@{o so} ◯ EM_to_SupLat@{o so}] x) = projT1 x
  := eq_refl.

Example p466_rt2_alg@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) :
  t_alg[projT2 (fobj[SupLat_to_EM@{o so} ◯ EM_to_SupLat@{o so}] x)]
    = t_alg[projT2 x] := eq_refl.

Example p466_alg_rt_data@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X) :
  t_alg[SupLat_TAlgebra@{o so} (TAlgebra_SupLat@{o so} α)] = t_alg[α]
  := eq_refl.

Example p466_rt2_hom@{o so}
  (x y : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
           Powerset_Monad@{o so}) (f : x ~> y) :
  t_alg_hom[fmap[SupLat_to_EM@{o so} ◯ EM_to_SupLat@{o so}] f]
    = t_alg_hom[f] := eq_refl.

(* N3 *)
Fail Example p466_rt2_obj@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) :
  fobj[SupLat_to_EM@{o so} ◯ EM_to_SupLat@{o so}] x = x := eq_refl.

(* N4 *)
Fail Example p466_rt2_t_id@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) :
  @t_id _ _ _ _ (projT2 (fobj[SupLat_to_EM@{o so} ◯ EM_to_SupLat@{o so}] x))
    = @t_id _ _ _ _ (projT2 x) := eq_refl.

(* N4b *)
Fail Example p466_rt2_t_action@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) :
  @t_action _ _ _ _
      (projT2 (fobj[SupLat_to_EM@{o so} ◯ EM_to_SupLat@{o so}] x))
    = @t_action _ _ _ _ (projT2 x) := eq_refl.

(* N5 *)
Fail Example p466_rt2_functor@{o so} :
  SupLat_to_EM@{o so} ◯ EM_to_SupLat@{o so}
    = Id[@EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
           Powerset_Monad@{o so}] := eq_refl.

(* N7 *)
Fail Example p466_alg_rt@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X) :
  SupLat_TAlgebra@{o so} (TAlgebra_SupLat@{o so} α) = α := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Variant L: two redundant law fields (scout B's t5) *)

(* The order-first record with the two algebra laws of the sup added as
   fields; not adopted, since the record is then no longer Mac Lane's
   definition. *)
Record p466_SupLatObjectL@{o} := {
  p466_sll_set : SetoidObject@{o o};
  p466_sll_le : carrier p466_sll_set → carrier p466_sll_set → Prop;
  p466_sll_le_refl x : p466_sll_le x x;
  p466_sll_le_trans x y z :
    p466_sll_le x y → p466_sll_le y z → p466_sll_le x z;
  p466_sll_le_respects x x' y y' :
    @equiv _ (is_setoid p466_sll_set) x x' →
    @equiv _ (is_setoid p466_sll_set) y y' →
    p466_sll_le x y → p466_sll_le x' y';
  p466_sll_antisym x y :
    p466_sll_le x y → p466_sll_le y x →
    @equiv _ (is_setoid p466_sll_set) x y;
  p466_sll_sup :
    SetoidMorphism@{o o o} (Powerset_Prop_obj@{o} p466_sll_set) p466_sll_set;
  p466_sll_sup_ub (S : carrier (Powerset_Prop_obj@{o} p466_sll_set)) x :
    S x → p466_sll_le x (p466_sll_sup S);
  p466_sll_sup_least (S : carrier (Powerset_Prop_obj@{o} p466_sll_set)) y :
    (∀ x, S x → p466_sll_le x y) → p466_sll_le (p466_sll_sup S) y;
  p466_sll_unit x :
    @equiv _ (is_setoid p466_sll_set)
      (p466_sll_sup (Powerset_Prop_singleton_pred@{o} x)) x;
  p466_sll_assoc
    (SS : carrier (Powerset_Prop_obj@{o}
                     (Powerset_Prop_obj@{o} p466_sll_set))) :
    @equiv _ (is_setoid p466_sll_set)
      (p466_sll_sup (Powerset_Prop_image@{o} p466_sll_sup SS))
      (p466_sll_sup (Powerset_union_pred@{o} SS))
}.

Definition p466_L_TAlgebra@{o so} (A : p466_SupLatObjectL@{o}) :
  @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so}
    (p466_sll_set A) :=
  @Build_TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so}
    (p466_sll_set A) (p466_sll_sup A) (p466_sll_unit A) (p466_sll_assoc A).

Definition p466_TAlgebra_L@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X) :
  p466_SupLatObjectL@{o} :=
  @Build_p466_SupLatObjectL@{o} X (talg_le@{o so} α)
    (talg_le_refl@{o so} α) (talg_le_trans@{o so} α)
    (talg_le_respects@{o so} α) (talg_antisym@{o so} α)
    t_alg[α] (talg_sup_ub@{o so} α) (talg_sup_least@{o so} α)
    (@t_id _ _ _ _ α) (@t_action _ _ _ _ α).

(* Controls: variant L's algebra round trip holds on the whole algebra,
   and on the whole EM object written (X; α). *)
Example p466_L_alg_rt@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X) :
  p466_L_TAlgebra@{o so} (p466_TAlgebra_L@{o so} α) = α := eq_refl.

Example p466_L_obj_rt@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so} X) :
  existT (fun Y => @TAlgebra Sets@{o so} Powerset_Prop@{o so}
                     Powerset_Monad@{o so} Y)
    X (p466_L_TAlgebra@{o so} (p466_TAlgebra_L@{o so} α))
  = existT _ X α := eq_refl.

(* N8 *)
Fail Example p466_L_var_rt@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} Powerset_Prop@{o so}
         Powerset_Monad@{o so}) :
  existT (fun Y => @TAlgebra Sets@{o so} Powerset_Prop@{o so}
                     Powerset_Monad@{o so} Y)
    (projT1 x) (p466_L_TAlgebra@{o so} (p466_TAlgebra_L@{o so} (projT2 x)))
  = x := eq_refl.

(* Control: variant L's semilattice round trip keeps the carrier. *)
Example p466_L_set_rt@{o so} (A : p466_SupLatObjectL@{o}) :
  p466_sll_set (p466_TAlgebra_L@{o so} (p466_L_TAlgebra@{o so} A))
    = p466_sll_set A := eq_refl.

(* N8b *)
Fail Example p466_L_le_rt@{o so} (A : p466_SupLatObjectL@{o}) :
  p466_sll_le (p466_TAlgebra_L@{o so} (p466_L_TAlgebra@{o so} A))
    = p466_sll_le A := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Variant A: the sup as a bare function *)

(* The properness of a sup, derived from the order.  Transparent, so that
   the comparison below is not stopped by opacity. *)
Definition p466_sup_respects@{o} (A : SupLatObject@{o})
  (S T : carrier (Powerset_Prop_obj@{o} (sl_set A))) (E : S ≈ T) :
  @equiv _ (is_setoid (sl_set A)) (sl_sup A S) (sl_sup A T).
Proof.
  apply sl_antisym; apply sl_sup_least; intros x Hx; apply sl_sup_ub.
  - exact (proj1 (E x) Hx).
  - exact (proj2 (E x) Hx).
Defined.

Definition p466_varA_alg@{o} (A : SupLatObject@{o}) :
  SetoidMorphism@{o o o} (Powerset_Prop_obj@{o} (sl_set A)) (sl_set A) :=
  @Build_SetoidMorphism@{o o o} _ _ _ _ (fun S => sl_sup A S)
    (p466_sup_respects@{o} A).

(* Control: the functions agree. *)
Example p466_varA_fun@{o} (A : SupLatObject@{o}) :
  (fun S => p466_varA_alg@{o} A S) = (fun S => sl_sup A S) := eq_refl.

(* N9 *)
Fail Example p466_varA_whole@{o} (A : SupLatObject@{o}) :
  p466_varA_alg@{o} A = sl_sup A := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** A Type-valued order *)

(* Control: with a Prop-valued order the unit law's inequality is formable
   (the order of [TAlgebra_SupLat], by [talg_sup_least]'s shape). *)
Example p466_proporder_unit@{o} (A : SupLatObject@{o})
  (x : carrier (sl_set A)) :
  ∀ z, Powerset_Prop_singleton_pred@{o} x z → sl_le A z x :=
  fun z Hz => Hz (sl_le A z x)
    (fun e => sl_le_respects A x z x x e (reflexivity x) (sl_le_refl A x)).

Section TypeOrder.
Universe o.
Constraint Set < o.
Context (X : SetoidObject@{o o}) (le : carrier X → carrier X → Type@{o}).
Context (le_respects : ∀ x x' y y', @equiv _ (is_setoid X) x x' →
          @equiv _ (is_setoid X) y y' → le x y → le x' y').
Context (le_refl : ∀ x, le x x).

(* N10 *)
Fail Definition p466_typeorder_unit (x : carrier X) :
  ∀ z, Powerset_Prop_singleton_pred@{o} x z → le z x :=
  fun z Hz => Hz (le z x)
    (fun e => le_respects x z x x e (reflexivity x) (le_refl x)).

End TypeOrder.

(* ------------------------------------------------------------------------ *)
(** ** Instance/SupLat/Free.v: the induced monad against [Powerset_Monad] *)

(* Controls: the object and arrow maps of the composite, as functions. *)
Example p466_ind_obj_fun@{o so} :
  (fun X => fobj[SL_Forget@{o so} ◯ SL_Free@{o so}] X)
    = (fun X => fobj[Powerset_Prop@{o so}] X) := eq_refl.

Example p466_ind_map_fun@{o so} (X Y : SetoidObject@{o o}) :
  (fun f : X ~{Sets@{o so}}~> Y =>
     fmap[SL_Forget@{o so} ◯ SL_Free@{o so}] f)
    = (fun f => fmap[Powerset_Prop@{o so}] f) := eq_refl.

(* Control: the unit as a function. *)
Example p466_ind_ret_fun@{o so} (X : SetoidObject@{o o}) :
  (fun x => @ret _ _ SL_induced@{o so} X x)
    = (fun x => @ret _ _ Powerset_Monad@{o so} X x) := eq_refl.

(* Control: the induced unit IS the identity composed with #227's
   singleton map. *)
Example p466_ind_ret_compose@{o so} (X : SetoidObject@{o o}) :
  @ret _ _ SL_induced@{o so} X
    = @setoid_morphism_compose@{o o o} _ _ _
        (@setoid_morphism_id@{o o o} (Powerset_Prop_obj@{o} X))
        (@Powerset_Prop_singleton_map@{o} X) := eq_refl.

(* F1 *)
Example p466_ind_ret_whole@{o so} (X : SetoidObject@{o o}) :
  @ret _ _ SL_induced@{o so} X = @ret _ _ Powerset_Monad@{o so} X
  := eq_refl.

(* Control: the unit at ≈. *)
Example p466_ind_ret_equiv@{o so} (X : SetoidObject@{o o}) :
  @ret _ _ SL_induced@{o so} X ≈ @ret _ _ Powerset_Monad@{o so} X :=
  SL_induced_ret_equiv@{o so} X.

(* Control: the induced join is ⋃ ∘ P id. *)
Example p466_ind_join_fun_ctl@{o so} (X : SetoidObject@{o o}) :
  (fun SS => @join _ _ SL_induced@{o so} X SS)
    = (fun SS => Powerset_union_pred@{o}
                   (Powerset_Prop_image@{o}
                      (@setoid_morphism_id@{o o o} (Powerset_Prop_obj@{o} X))
                      SS)) := eq_refl.

(* F2 *)
Fail Example p466_ind_join_fun@{o so} (X : SetoidObject@{o o}) :
  (fun SS => @join _ _ SL_induced@{o so} X SS)
    = (fun SS => @join _ _ Powerset_Monad@{o so} X SS) := eq_refl.

(* F2b *)
Fail Example p466_ind_join_at@{o so} (X : SetoidObject@{o o})
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))) :
  @join _ _ SL_induced@{o so} X SS = @join _ _ Powerset_Monad@{o so} X SS
  := eq_refl.

(* Control: the join at ≈. *)
Example p466_ind_join_equiv@{o so} (X : SetoidObject@{o o}) :
  @join _ _ SL_induced@{o so} X ≈ @join _ _ Powerset_Monad@{o so} X :=
  SL_induced_join_equiv@{o so} X.

(* F3 *)
Fail Example p466_ind_functor@{o so} :
  SL_Forget@{o so} ◯ SL_Free@{o so} = Powerset_Prop@{o so} := eq_refl.

(* Controls: the functor at ≈, with the identity isomorphism as its
   component. *)
Example p466_ind_functor_equiv@{o so} :
  SL_Forget@{o so} ◯ SL_Free@{o so} ≈ Powerset_Prop@{o so} :=
  SL_induced_functor_equiv@{o so}.

Example p466_ind_functor_component@{o so} (X : SetoidObject@{o o}) :
  projT1 SL_induced_functor_equiv@{o so} X
    = @iso_id Sets@{o so} (fobj[Powerset_Prop@{o so}] X) := eq_refl.

(* F4 *)
Fail Definition p466_ind_monad@{o so} :
  @Monad Sets@{o so} (SL_Forget@{o so} ◯ SL_Free@{o so}) :=
  Powerset_Monad@{o so}.

(* ------------------------------------------------------------------------ *)
(** ** Instance/SupLat/Free.v: the comparison round trips *)

(* Controls: identity components at a variable object, and the carrier. *)
Example p466_cmp_counit_component@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  t_alg_hom[to (projT1 (@equivalence_counit _ _ _
                           SL_comparison_equivalence@{o so}) x)]
    = @setoid_morphism_id@{o o o} (projT1 x) := eq_refl.

Example p466_cmp_unit_component@{o so} (A : SupLatObject@{o}) :
  slh_map (to (projT1 (@equivalence_unit _ _ _
                         SL_comparison_equivalence@{o so}) A))
    = @setoid_morphism_id@{o o o} (sl_set A) := eq_refl.

Example p466_cmp_carrier@{o so} (A : SupLatObject@{o}) :
  sl_set (fobj[EM_induced_to_SupLat@{o so} ◯ EM_Comparison SL_adj@{o so}] A)
  = sl_set A := eq_refl.

(* F5 *)
Fail Example p466_cmp_composite@{o so} :
  EM_Comparison SL_adj@{o so} ◯ EM_induced_to_SupLat@{o so}
  = Id[@EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}] := eq_refl.

(* F5b *)
Fail Example p466_cmp_composite_b@{o so} :
  EM_induced_to_SupLat@{o so} ◯ EM_Comparison SL_adj@{o so}
  = Id[SupLat@{o so}] := eq_refl.

(* F6 *)
Fail Example p466_cmp_obj@{o so} (A : SupLatObject@{o}) :
  fobj[EM_induced_to_SupLat@{o so} ◯ EM_Comparison SL_adj@{o so}] A = A
  := eq_refl.

(* F6b *)
Fail Example p466_cmp_obj_b@{o so}
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (SL_Forget@{o so} ◯ SL_Free@{o so}) SL_induced@{o so}) :
  fobj[EM_Comparison SL_adj@{o so} ◯ EM_induced_to_SupLat@{o so}] x = x
  := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Instance/SupLat/Examples.v: P X and P 1 *)

(* Controls: (b) at the free algebra has the carrier and the sup of
   [FreeSL X], and its order is inclusion logically. *)
Example p466_freesl_em_set@{o so} (X : SetoidObject@{o o}) :
  sl_set (fobj[EM_to_SupLat@{o so}]
            (fobj[@EM_Free Sets@{o so} Powerset_Prop@{o so}
                    Powerset_Monad@{o so}] X))
  = sl_set (FreeSL@{o} X) := eq_refl.

Example p466_freesl_em_sup@{o so} (X : SetoidObject@{o o}) :
  sl_sup (fobj[EM_to_SupLat@{o so}]
            (fobj[@EM_Free Sets@{o so} Powerset_Prop@{o so}
                    Powerset_Monad@{o so}] X))
  = sl_sup (FreeSL@{o} X) := eq_refl.

Example p466_freesl_em_le_iff@{o so} (X : SetoidObject@{o o})
  (S T : carrier (Powerset_Prop_obj@{o} X)) :
  iff (sl_le (fobj[EM_to_SupLat@{o so}]
                (fobj[@EM_Free Sets@{o so} Powerset_Prop@{o so}
                        Powerset_Monad@{o so}] X)) S T)
      (sl_le (FreeSL@{o} X) S T) :=
  sl_talg_le_iff@{o so} (FreeSL@{o} X) S T.

(* E1 *)
Fail Example p466_freesl_em_obj@{o so} (X : SetoidObject@{o o}) :
  fobj[EM_to_SupLat@{o so}]
    (fobj[@EM_Free Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so}] X)
  = FreeSL@{o} X := eq_refl.

(* E1b *)
Fail Example p466_freesl_em_le@{o so} (X : SetoidObject@{o o}) :
  sl_le (fobj[EM_to_SupLat@{o so}]
           (fobj[@EM_Free Sets@{o so} Powerset_Prop@{o so}
                   Powerset_Monad@{o so}] X))
  = sl_le (FreeSL@{o} X) := eq_refl.

(* Control: (c) at P X has the free algebra's carrier at [eq_refl]; its
   structure map is Instance/SupLat/Examples.v's [FreeSL_alg]. *)
Example p466_freealg_carrier@{o so} (X : SetoidObject@{o o}) :
  projT1 (fobj[SupLat_to_EM@{o so}] (FreeSL@{o} X))
    = projT1 (fobj[@EM_Free Sets@{o so} Powerset_Prop@{o so}
                    Powerset_Monad@{o so}] X) := eq_refl.

(* E3 *)
Fail Example p466_freealg_whole@{o so} (X : SetoidObject@{o o}) :
  projT2 (fobj[SupLat_to_EM@{o so}] (FreeSL@{o} X))
    = projT2 (fobj[@EM_Free Sets@{o so} Powerset_Prop@{o so}
                    Powerset_Monad@{o so}] X) := eq_refl.

(* E3b *)
Fail Example p466_freealg_obj@{o so} (X : SetoidObject@{o o}) :
  fobj[SupLat_to_EM@{o so}] (FreeSL@{o} X)
    = fobj[@EM_Free Sets@{o so} Powerset_Prop@{o so} Powerset_Monad@{o so}] X
  := eq_refl.

(* Controls: the P 1 round trip at the point, and the Prop round trip. *)
Example p466_prop_p1_rt_at@{o}
  (T : carrier (Powerset_Prop_obj@{o} unit_setoid_object@{o o})) :
  slh_map Prop_to_P1@{o} (slh_map P1_to_Prop@{o} T) ttt = T ttt := eq_refl.

Example p466_p1_prop_rt@{o} (Q : Prop) :
  slh_map P1_to_Prop@{o} (slh_map Prop_to_P1@{o} Q) = Q := eq_refl.

(* E2 *)
Fail Example p466_prop_p1_rt@{o}
  (T : carrier (Powerset_Prop_obj@{o} unit_setoid_object@{o o})) :
  slh_map Prop_to_P1@{o} (slh_map P1_to_Prop@{o} T) = T := eq_refl.

(* Control: the two-point theorem at its stated type. *)
Definition p466_two_points@{o} (A : SupLatObject@{o})
  (bot top : carrier (sl_set A)) (Hle : sl_le A bot top)
  (Hne : @equiv _ (is_setoid (sl_set A)) top bot → False)
  (Hdec : ∀ x y, @equiv _ (is_setoid (sl_set A)) x y
                 + (@equiv _ (is_setoid (sl_set A)) x y → False)) :
  ∀ Q : Prop, (~ Q) + (~ ~ Q) :=
  suplat_two_points_WLEM@{o} A bot top Hle Hne Hdec.

(* Control: the chain's carrier is Instance/Sets.v's two-element setoid. *)
Example p466_chain_carrier@{o}
  (wlem : ∀ Q : Prop, (~ Q) + (~ ~ Q)) :
  sl_set (bool_SupLat@{o} wlem) = bool_setoid_object@{o o} := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Instance/Sets/Powerset/Monad/Riehl.v: the routes prove the field *)

(* Control: Riehl's route through the left adjoint proves the statement of
   [Powerset_Monad]'s naturality field, as stated. *)
Definition p466_riehl_lapc@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) : Powerset_join_natural_statement@{o so} f :=
  fun SS => join_natural_via_LAPC f SS.

(* ------------------------------------------------------------------------ *)
(** ** Closure: readbacks, not refutations *)

Print Assumptions Powerset_Monad.
Print Assumptions SupLat_EM_iso.
Print Assumptions SupLat_EM_equivalence.
Print Assumptions talg_PropEquiv.
Print Assumptions sl_PropEquiv.
Print Assumptions SL_adj.
Print Assumptions SL_Forget_Monadic.
Print Assumptions SL_induced.
Print Assumptions suplat_two_points_WLEM.
Print Assumptions bool_SupLat_WLEM.
Print Assumptions bool_SupLat.
Print Assumptions Prop_P1_iso.
Print Assumptions join_natural_routes_agree.

(* ------------------------------------------------------------------------ *)
(** ** Guard: every constant of the five targets, by its full name *)

Check @Category.Instance.Sets.Powerset.Monad.Powerset_union_pred.
Check @Category.Instance.Sets.Powerset.Monad.Powerset_union_respects.
Check @Category.Instance.Sets.Powerset.Monad.Powerset_union.
Check @Category.Instance.Sets.Powerset.Monad.Powerset_union_assoc.
Check @Category.Instance.Sets.Powerset.Monad.Powerset_union_image_singleton.
Check @Category.Instance.Sets.Powerset.Monad.Powerset_union_singleton.
Check @Category.Instance.Sets.Powerset.Monad.Powerset_union_natural.
Check @Category.Instance.Sets.Powerset.Monad.Powerset_Monad.
Check @Category.Instance.Sets.Powerset.Monad.Powerset_Monad_obj.
Check @Category.Instance.Sets.Powerset.Monad.Powerset_Monad_map.
Check @Category.Instance.Sets.Powerset.Monad.Powerset_Monad_ret.
Check @Category.Instance.Sets.Powerset.Monad.Powerset_Monad_ret_map.
Check @Category.Instance.Sets.Powerset.Monad.Powerset_Monad_ret_at.
Check @Category.Instance.Sets.Powerset.Monad.Powerset_Monad_join.
Check @Category.Instance.Sets.Powerset.Monad.Powerset_Monad_join_at.
Check @Category.Instance.Sets.Powerset.Monad.Powerset_Monad_map_at.
Check @Category.Instance.Sets.Powerset.Monad.Powerset_Monad_ret_member.
Check @Category.Instance.Sets.Powerset.Monad.Powerset_Monad_statement.
Check @Category.Instance.SupLat.Powerset_Prop_pair.
Check @Category.Instance.SupLat.Powerset_Prop_pair_respects.
Check @Category.Instance.SupLat.Powerset_Prop_pair_comm.
Check @Category.Instance.SupLat.Powerset_Prop_singleton_sub.
Check @Category.Instance.SupLat.Powerset_union_pair_sub.
Check @Category.Instance.SupLat.Powerset_Prop_least_family.
Check @Category.Instance.SupLat.SupLatObject.
Check @Category.Instance.SupLat.Build_SupLatObject.
Check @Category.Instance.SupLat.sl_set.
Check @Category.Instance.SupLat.sl_le.
Check @Category.Instance.SupLat.sl_le_refl.
Check @Category.Instance.SupLat.sl_le_trans.
Check @Category.Instance.SupLat.sl_le_respects.
Check @Category.Instance.SupLat.sl_antisym.
Check @Category.Instance.SupLat.sl_sup.
Check @Category.Instance.SupLat.sl_sup_ub.
Check @Category.Instance.SupLat.sl_sup_least.
Check @Category.Instance.SupLat.SupLatHom.
Check @Category.Instance.SupLat.Build_SupLatHom.
Check @Category.Instance.SupLat.slh_map.
Check @Category.Instance.SupLat.slh_sup.
Check @Category.Instance.SupLat.SupLatHom_Setoid.
Check @Category.Instance.SupLat.SupLat_id.
Check @Category.Instance.SupLat.SupLat_compose.
Check @Category.Instance.SupLat.SupLat.
Check @Category.Instance.SupLat.sl_sup_pair_le.
Check @Category.Instance.SupLat.SupLatHom_monotone.
Check @Category.Instance.SupLat.sl_PropEquiv.
Check @Category.Instance.SupLat.SupLat_TAlgebra.
Check @Category.Instance.SupLat.talg_singleton.
Check @Category.Instance.SupLat.talg_unsquash.
Check @Category.Instance.SupLat.talg_pair.
Check @Category.Instance.SupLat.talg_mono.
Check @Category.Instance.SupLat.talg_le.
Check @Category.Instance.SupLat.talg_le_iff.
Check @Category.Instance.SupLat.talg_le_refl.
Check @Category.Instance.SupLat.talg_sup_ub.
Check @Category.Instance.SupLat.talg_sup_least.
Check @Category.Instance.SupLat.talg_le_trans.
Check @Category.Instance.SupLat.talg_le_respects.
Check @Category.Instance.SupLat.talg_antisym.
Check @Category.Instance.SupLat.TAlgebra_SupLat.
Check @Category.Instance.SupLat.talg_PropEquiv.
Check @Category.Instance.SupLat.sl_talg_le_iff.
Check @Category.Instance.SupLat.EM_to_SupLat.
Check @Category.Instance.SupLat.SupLat_to_EM.
Check @Category.Instance.SupLat.SupLat_EM_counit_iso.
Check @Category.Instance.SupLat.SupLat_EM_unit_iso.
Check @Category.Instance.SupLat.SupLat_EM_equivalence.
Check @Category.Instance.SupLat.SupLat_EM_iso.
Check @Category.Instance.SupLat.SupLat_EM_iso_to.
Check @Category.Instance.SupLat.SupLat_EM_iso_from.
Check @Category.Instance.SupLat.EM_to_SupLat_carrier.
Check @Category.Instance.SupLat.EM_to_SupLat_sup.
Check @Category.Instance.SupLat.EM_to_SupLat_le.
Check @Category.Instance.SupLat.SupLat_to_EM_carrier.
Check @Category.Instance.SupLat.SupLat_to_EM_alg.
Check @Category.Instance.SupLat.EM_to_SupLat_map.
Check @Category.Instance.SupLat.SupLat_to_EM_map.
Check @Category.Instance.SupLat.SupLat_EM_rt_carrier.
Check @Category.Instance.SupLat.SupLat_EM_rt_alg.
Check @Category.Instance.SupLat.SupLat_EM_rt_set.
Check @Category.Instance.SupLat.SupLat_EM_rt_sup.
Check @Category.Instance.SupLat.SupLat_EM_rt_hom.
Check @Category.Instance.SupLat.SupLat_EM_rt_alg_hom.
Check @Category.Instance.SupLat.SupLat_EM_counit_component.
Check @Category.Instance.SupLat.SupLat_EM_unit_component.
Check @Category.Instance.SupLat.SupLat_EM_counit_component_from.
Check @Category.Instance.SupLat.SupLat_EM_unit_component_from.
Check @Category.Instance.SupLat.SupLat_EM_iso_to_from_component.
Check @Category.Instance.SupLat.SupLat_EM_iso_from_to_component.
Check @Category.Instance.SupLat.SupLat_EM_iso_to_from_component_from.
Check @Category.Instance.SupLat.SupLat_EM_iso_from_to_component_from.
Check @Category.Instance.SupLat.Free.FreeSL.
Check @Category.Instance.SupLat.Free.SL_Free.
Check @Category.Instance.SupLat.Free.SL_Forget.
Check @Category.Instance.SupLat.Free.SL_extend.
Check @Category.Instance.SupLat.Free.SL_restrict.
Check @Category.Instance.SupLat.Free.SL_adj_iso.
Check @Category.Instance.SupLat.Free.SL_adj.
Check @Category.Instance.SupLat.Free.SL_induced.
Check @Category.Instance.SupLat.Free.SL_induced_obj.
Check @Category.Instance.SupLat.Free.SL_induced_map.
Check @Category.Instance.SupLat.Free.SL_induced_ret_fun.
Check @Category.Instance.SupLat.Free.SL_induced_join_fun.
Check @Category.Instance.SupLat.Free.SL_induced_ret_equiv.
Check @Category.Instance.SupLat.Free.SL_induced_join_equiv.
Check @Category.Instance.SupLat.Free.SL_induced_functor_equiv.
Check @Category.Instance.SupLat.Free.SL_induced_functor_component.
Check @Category.Instance.SupLat.Free.SL_induced_repack.
Check @Category.Instance.SupLat.Free.EM_induced_to_SupLat.
Check @Category.Instance.SupLat.Free.SL_comparison_counit_iso.
Check @Category.Instance.SupLat.Free.SL_comparison_unit_iso.
Check @Category.Instance.SupLat.Free.SL_comparison_equivalence.
Check @Category.Instance.SupLat.Free.SL_Forget_Monadic.
Check @Category.Instance.SupLat.Free.SL_comparison_counit_component.
Check @Category.Instance.SupLat.Free.SL_comparison_counit_component_from.
Check @Category.Instance.SupLat.Free.SL_comparison_unit_component.
Check @Category.Instance.SupLat.Free.SL_comparison_unit_component_from.
Check @Category.Instance.SupLat.Examples.FreeSL_set.
Check @Category.Instance.SupLat.Examples.FreeSL_le.
Check @Category.Instance.SupLat.Examples.FreeSL_sup.
Check @Category.Instance.SupLat.Examples.FreeSL_alg.
Check @Category.Instance.SupLat.Examples.FreeSL_talg_le_iff.
Check @Category.Instance.SupLat.Examples.FreeSL_extend_singleton.
Check @Category.Instance.SupLat.Examples.FreeSL_extend_unique.
Check @Category.Instance.SupLat.Examples.Prop_sup.
Check @Category.Instance.SupLat.Examples.Prop_SupLat.
Check @Category.Instance.SupLat.Examples.Prop_SupLat_le.
Check @Category.Instance.SupLat.Examples.Prop_SupLat_sup.
Check @Category.Instance.SupLat.Examples.Prop_SupLat_nontrivial.
Check @Category.Instance.SupLat.Examples.Prop_to_P1_pred.
Check @Category.Instance.SupLat.Examples.Prop_to_P1.
Check @Category.Instance.SupLat.Examples.P1_to_Prop.
Check @Category.Instance.SupLat.Examples.Prop_P1_iso.
Check @Category.Instance.SupLat.Examples.Prop_to_P1_at.
Check @Category.Instance.SupLat.Examples.Prop_P1_round_trip.
Check @Category.Instance.SupLat.Examples.two_points_probe.
Check @Category.Instance.SupLat.Examples.suplat_two_points_WLEM.
Check @Category.Instance.SupLat.Examples.Prop_SupLat_decidable_WLEM.
Check @Category.Instance.SupLat.Examples.bool_chain_le.
Check @Category.Instance.SupLat.Examples.bool_chain_SupLat.
Check @Category.Instance.SupLat.Examples.bool_SupLat_WLEM.
Check @Category.Instance.SupLat.Examples.bool_chain_sup_fun.
Check @Category.Instance.SupLat.Examples.bool_chain_sup_true.
Check @Category.Instance.SupLat.Examples.bool_chain_sup_false.
Check @Category.Instance.SupLat.Examples.bool_chain_sup.
Check @Category.Instance.SupLat.Examples.bool_SupLat.
Check @Category.Instance.Sets.Powerset.Monad.Riehl.Powerset_union_IsLUB.
Check @Category.Instance.Sets.Powerset.Monad.Riehl.Powerset_union_family.
Check @Category.Instance.Sets.Powerset.Monad.Riehl.join_natural_via_image.
Check @Category.Instance.Sets.Powerset.Monad.Riehl.join_natural_via_LAPC.
Check @Category.Instance.Sets.Powerset.Monad.Riehl.Powerset_join_natural_statement.
Check @Category.Instance.Sets.Powerset.Monad.Riehl.join_natural_routes_agree.
