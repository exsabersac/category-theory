(*
   本文件为测试：ProbeGroupAction464。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.Beck.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Group.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Action.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.Fun.Action.Monad.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Instance.Fun.Eval.
Require Import Category.Instance.Fun.Action.Monad.BG.

Generalizable All Variables.

(** ** Instrument: a false statement is refused *)

(* CONTROL: Mac Lane's μ at a triple, in his order. *)
Example p464_instrument_ctl@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) (g1 g2 : carrier M) (x : carrier X) :
  (@join _ _ (ActMonad@{o so} M) X) (g1, (g2, x)) = (mon_op g1 g2, x) :=
  eq_refl.

(* The instrument *)
Fail Example p464_instrument@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) (g1 g2 : carrier M) (x : carrier X) :
  (@join _ _ (ActMonad@{o so} M) X) (g1, (g2, x)) = (mon_op g2 g1, x) :=
  eq_refl.

(** ** Instance/Fun/Action/Monad.v: the monad and the two Cat isomorphisms *)

(* CONTROL: η at a point and μ as a function, on the nose; the [to] legs
   of the two Cat isomorphisms. *)
Example p464_ret@{o so} (M : MonObject@{o o o}) (X : SetoidObject@{o o})
  (x : carrier X) :
  (@ret _ _ (ActMonad@{o so} M) X) x = (mon_unit, x) := eq_refl.

Example p464_join_fun@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) :
  (fun p => (@join _ _ (ActMonad@{o so} M) X) p)
  = (fun p : carrier M * (carrier M * carrier X) =>
       (mon_op (fst p) (fst (snd p)), snd (snd p))) := eq_refl.

Example p464_to@{o so c} (M : MonObject@{o o o}) :
  to (EM_MSet_iso@{o so c} M) = EM_Comparison (MSet_adj@{o so} M) := eq_refl.

Example p464_beck_to@{o so c} (M : MonObject@{o o o}) :
  to (EM_MSet_iso_beck@{o so c} M) = to (EM_MSet_iso@{o so c} M) := eq_refl.

(** ** Instance/Fun/Action/Monad.v: the round trip M-set → algebra → M-set *)

(* CONTROL: the carrier and the action as a function, on the nose. *)
Example p464_rt_setoid@{o so} {M : MonObject@{o o o}}
  (A : MSetoidAction@{o o o o o o o o} M) :
  act_setoid (fobj[EM_to_MSet@{o so} M ◯ EM_Comparison (MSet_adj@{o so} M)] A)
  = act_setoid A := eq_refl.

Example p464_rt_act@{o so} {M : MonObject@{o o o}}
  (A : MSetoidAction@{o o o o o o o o} M) :
  act (fobj[EM_to_MSet@{o so} M ◯ EM_Comparison (MSet_adj@{o so} M)] A)
  = act A := eq_refl.

(* CONTROL (the cause of N3): the [act_respects] field of the round trip
   is [act_respects A] with its last argument passed through the identity
   map's properness proof, and without that proof it is [act_respects A]
   by eta. *)
Example p464_rt_respects_isolate@{o so} {M : MonObject@{o o o}}
  (A : MSetoidAction@{o o o o o o o o} M) :
  act_respects
    (fobj[EM_to_MSet@{o so} M ◯ EM_Comparison (MSet_adj@{o so} M)] A)
  = (fun g g' Hg a a' Ha =>
       act_respects A g g' Hg a a'
         (@proper_morphism _ _ _ _
            (@setoid_morphism_id@{o o o} (act_setoid A)) a a' Ha)) :=
  eq_refl.

Example p464_rt_respects_eta@{o so} {M : MonObject@{o o o}}
  (A : MSetoidAction@{o o o o o o o o} M) :
  (fun g g' Hg a a' Ha => act_respects A g g' Hg a a' Ha) = act_respects A :=
  eq_refl.

(* N1 *)
Fail Example p464_rt_op@{o so} {M : MonObject@{o o o}}
  (A : MSetoidAction@{o o o o o o o o} M) :
  act_op (fobj[EM_to_MSet@{o so} M ◯ EM_Comparison (MSet_adj@{o so} M)] A)
  = act_op A := eq_refl.

(* N2 *)
Fail Example p464_rt_unit@{o so} {M : MonObject@{o o o}}
  (A : MSetoidAction@{o o o o o o o o} M) :
  act_unit (fobj[EM_to_MSet@{o so} M ◯ EM_Comparison (MSet_adj@{o so} M)] A)
  = act_unit A := eq_refl.

(* N3 *)
Example p464_rt_respects@{o so} {M : MonObject@{o o o}}
  (A : MSetoidAction@{o o o o o o o o} M) :
  act_respects
    (fobj[EM_to_MSet@{o so} M ◯ EM_Comparison (MSet_adj@{o so} M)] A)
  = act_respects A := eq_refl.

(* N4 *)
Fail Example p464_rt_obj@{o so} {M : MonObject@{o o o}}
  (A : MSetoidAction@{o o o o o o o o} M) :
  fobj[EM_to_MSet@{o so} M ◯ EM_Comparison (MSet_adj@{o so} M)] A = A :=
  eq_refl.

(* N5 *)
Fail Example p464_rt_functor@{o so} {M : MonObject@{o o o}} :
  EM_to_MSet@{o so} M ◯ EM_Comparison (MSet_adj@{o so} M)
  = Id[MSet@{so so o o o o o o} M] := eq_refl.

(** ** Instance/Fun/Action/Monad.v: the round trip algebra → M-set →
    algebra *)

(* CONTROL: the carrier, the structure map at each pair, and the
   structure map as the function p ↦ h (fst p, snd p), on the nose. *)
Example p464_rt2_carrier@{o so} {M : MonObject@{o o o}}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) :
  `1 (fobj[EM_Comparison (MSet_adj@{o so} M) ◯ EM_to_MSet@{o so} M] x)
  = `1 x := eq_refl.

Example p464_rt2_pointwise@{o so} {M : MonObject@{o o o}}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) (g : carrier M) (a : carrier (`1 x)) :
  t_alg[`2 (fobj[EM_Comparison (MSet_adj@{o so} M) ◯ EM_to_MSet@{o so} M] x)]
    (g, a) = t_alg[`2 x] (g, a) := eq_refl.

Example p464_rt2_eta@{o so} {M : MonObject@{o o o}}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) :
  (fun p => t_alg[`2 (fobj[EM_Comparison (MSet_adj@{o so} M)
                          ◯ EM_to_MSet@{o so} M] x)] p)
  = (fun p => t_alg[`2 x] (fst p, snd p)) := eq_refl.

(* N6 *)
Fail Example p464_rt2_functor@{o so} {M : MonObject@{o o o}} :
  EM_Comparison (MSet_adj@{o so} M) ◯ EM_to_MSet@{o so} M
  = Id[@EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)] := eq_refl.

(* N7 *)
Fail Example p464_rt2_fun@{o so} {M : MonObject@{o o o}}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) :
  (fun p => t_alg[`2 (fobj[EM_Comparison (MSet_adj@{o so} M)
                          ◯ EM_to_MSet@{o so} M] x)] p)
  = (fun p => t_alg[`2 x] p) := eq_refl.

(* N8 *)
Fail Example p464_rt2_obj@{o so} {M : MonObject@{o o o}}
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) :
  fobj[EM_Comparison (MSet_adj@{o so} M) ◯ EM_to_MSet@{o so} M] x = x :=
  eq_refl.

(** ** Instance/Fun/Action/Monad.v: Beck's route against the direct one *)

(* CONTROL: Beck's quasi-inverse keeps the carrier and acts through η. *)
Example p464_beck_carrier@{o so} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) :
  act_setoid (fobj[@quasi_inverse _ _ _ (MSet_beck_equivalence@{o so} M)] x)
  = `1 x := eq_refl.

Example p464_beck_act@{o so} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) (g : carrier M) (z : carrier (`1 x)) :
  act (fobj[@quasi_inverse _ _ _ (MSet_beck_equivalence@{o so} M)] x) g z
  = t_alg[`2 x] (mon_op g mon_unit, z) := eq_refl.

(* N9 *)
Fail Example p464_beck_qi@{o so} (M : MonObject@{o o o}) :
  @quasi_inverse _ _ _ (MSet_beck_equivalence@{o so} M) = EM_to_MSet@{o so} M
  := eq_refl.

(* N10 *)
Fail Example p464_beck_act_strict@{o so} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
         (ActMonad@{o so} M)) (g : carrier M) (z : carrier (`1 x)) :
  act (fobj[@quasi_inverse _ _ _ (MSet_beck_equivalence@{o so} M)] x) g z
  = t_alg[`2 x] (g, z) := eq_refl.

(* N11 *)
Fail Example p464_monadic_same@{o so} (M : MonObject@{o o o}) :
  MSet_Forget_Monadic@{o so} M = MSet_Forget_Monadic_direct@{o so} M :=
  eq_refl.

(** ** Instance/Fun/Action/Monad.v: the hand-built functor G × (−) *)

(* The functor G × (−) built by hand, which the file does not keep. *)
Definition p464_ActF_hand@{o so} (M : MonObject@{o o o}) :
  Sets@{o so} ⟶ Sets@{o so}.
Proof.
  unshelve refine
    (@Build_Functor Sets@{o so} Sets@{o so} (fun X => act_prod M X)
       (fun X Y f => act_prod_map@{o so} M f) _ _ _).
  - intros X Y f f' Hf p. split; [ reflexivity | exact (Hf (snd p)) ].
  - intros X p. split; reflexivity.
  - intros X Y Z f g p. split; reflexivity.
Defined.

(* CONTROL: the same object and arrow maps as [ActF M], and ≈ to it with
   identity components. *)
Example p464_hand_obj@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) :
  fobj[p464_ActF_hand@{o so} M] X = fobj[ActF@{o so} M] X := eq_refl.

Example p464_hand_map@{o so} (M : MonObject@{o o o})
  (X Y : SetoidObject@{o o}) (f : X ~{Sets@{o so}}~> Y) :
  fmap[p464_ActF_hand@{o so} M] f = fmap[ActF@{o so} M] f := eq_refl.

Definition p464_hand_equiv@{o so} (M : MonObject@{o o o}) :
  p464_ActF_hand@{o so} M ≈ ActF@{o so} M.
Proof.
  exists (fun X => iso_id). intros X Y f p. split; reflexivity.
Defined.

(* N12 *)
Fail Example p464_hand_is_composite@{o so} (M : MonObject@{o o o}) :
  p464_ActF_hand@{o so} M = ActF@{o so} M := eq_refl.

(** ** Instance/Fun/Action/Monad/BG.v: the two monads *)

(* CONTROL: the literal unit reads (u u, x); the two monads have the same
   object and arrow maps, the same multiplication at every p and the same
   underlying multiplication function; the [to] leg of [BG_EM_iso]. *)
Example p464_bg_ret@{o so} (M : MonObject@{o o o}) (X : SetoidObject@{o o})
  (x : carrier X) :
  (@ret _ _ (BGMonad@{o so} M) X) x = (mon_op mon_unit mon_unit, x) :=
  eq_refl.

Example p464_bg_T_obj@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) :
  fobj[U_BG@{o so} M ◯ F_BG@{o so} M] X = fobj[ActF@{o so} M] X := eq_refl.

Example p464_bg_T_map@{o so} (M : MonObject@{o o o})
  (X Y : SetoidObject@{o o}) (f : X ~{Sets@{o so}}~> Y) :
  fmap[U_BG@{o so} M ◯ F_BG@{o so} M] f = fmap[ActF@{o so} M] f := eq_refl.

Example p464_bg_join_pointwise@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) (p : carrier M * (carrier M * carrier X)) :
  (@join _ _ (BGMonad@{o so} M) X) p = (@join _ _ (ActMonad@{o so} M) X) p :=
  eq_refl.

Example p464_bg_join_morphism@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) :
  @morphism _ _ _ _ (@join _ _ (BGMonad@{o so} M) X)
  = @morphism _ _ _ _ (@join _ _ (ActMonad@{o so} M) X) := eq_refl.

Example p464_bg_EM_to@{o so c} (M : MonObject@{o o o}) :
  to (BG_EM_iso@{o so c} M) = EM_Comparison (BG_adj@{o so} M) := eq_refl.

(* N13 *)
Fail Example p464_bg_ret_strict@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) (x : carrier X) :
  (@ret _ _ (BGMonad@{o so} M) X) x = (mon_unit, x) := eq_refl.

(* N14 *)
Fail Example p464_bg_T_is_ActF@{o so} (M : MonObject@{o o o}) :
  U_BG@{o so} M ◯ F_BG@{o so} M = ActF@{o so} M := eq_refl.

(* N15 *)
Fail Example p464_bg_join_fun@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) :
  @join _ _ (BGMonad@{o so} M) X = @join _ _ (ActMonad@{o so} M) X :=
  eq_refl.

(** ** Instance/Fun/Action/Monad/BG.v: evaluation *)

(* CONTROL: evaluation against [MSet_to] followed by [MSet_Forget], in
   both data fields. *)
Example p464_bg_U_obj@{o so} (M : MonObject@{o o o}) (P : SetBG@{o so} M) :
  fobj[U_BG@{o so} M] P = fobj[MSet_Forget@{o so} M ◯ MSet_to@{so o} M] P :=
  eq_refl.

Example p464_bg_U_map@{o so} (M : MonObject@{o o o}) (P Q : SetBG@{o so} M)
  (η : P ~{SetBG@{o so} M}~> Q) :
  fmap[U_BG@{o so} M] η = fmap[MSet_Forget@{o so} M ◯ MSet_to@{so o} M] η :=
  eq_refl.

(* N16 *)
Fail Example p464_bg_U_is_composite@{o so} (M : MonObject@{o o o}) :
  U_BG@{o so} M = MSet_Forget@{o so} M ◯ MSet_to@{so o} M := eq_refl.

(** ** Instance/Fun/Action/Monad/BG.v: the hom level of Set^BG *)

(* The functor category of BG.v with its hom level raised from o to so;
   Instance/Fun.v's block allows any hom level at least o. *)
Definition p464_SetBG_h@{o so} (M : MonObject@{o o o}) : Category@{so so so} :=
  @Fun@{o o so o so so so} (Deloop@{o o} M) Sets@{o so}.

(* CONTROL: functors into the raised category are formable, and
   Instance/Fun/Action.v's [MSet_from] lands there; [MSet_Free] alone. *)
Definition p464_bg_up@{o so} (M : MonObject@{o o o}) : Type@{so} :=
  Sets@{o so} ⟶ p464_SetBG_h@{o so} M.

Definition p464_bg_from_h@{o so} (M : MonObject@{o o o}) :
  MSet@{so so o o o o o o} M ⟶ p464_SetBG_h@{o so} M :=
  MSet_from@{so so o so o} M.

Definition p464_bg_free@{o so} (M : MonObject@{o o o}) :
  Sets@{o so} ⟶ MSet@{so so o o o o o o} M := MSet_Free@{o so} M.

(* N17 *)
Fail Definition p464_bg_down_h@{o so} (M : MonObject@{o o o}) : Type@{so} :=
  p464_SetBG_h@{o so} M ⟶ Sets@{o so}.

(* N18 *)
Fail Definition p464_bg_F_h@{o so} (M : MonObject@{o o o}) :
  Sets@{o so} ⟶ p464_SetBG_h@{o so} M :=
  MSet_from@{so so o so o} M ◯ MSet_Free@{o so} M.

(** ** Instance/Fun/Action/Monad/BG.v: the tie *)

(* CONTROL: the [to] leg of [Fun_EM_iso] is the comparison functor of
   [MSet_adj] after [MSet_to], on the nose; θ* after this file's
   comparison functor agrees with it on carriers and on structure maps as
   functions. *)
Example p464_fun_em_to@{o so c} (M : MonObject@{o o o}) :
  to (Fun_EM_iso@{o so c} M)
  = EM_Comparison (MSet_adj@{o so} M) ◯ MSet_to@{so o} M := eq_refl.

Example p464_tie_carrier@{o so c} (M : MonObject@{o o o})
  (P : SetBG@{o so} M) :
  `1 (fobj[BG_Act_EM@{o so} M ◯ EM_Comparison (BG_adj@{o so} M)] P)
  = `1 (fobj[to (Fun_EM_iso@{o so c} M)] P) := eq_refl.

Example p464_tie_alg@{o so c} (M : MonObject@{o o o}) (P : SetBG@{o so} M) :
  (fun p => @t_alg _ _ _ _
     (`2 (fobj[BG_Act_EM@{o so} M ◯ EM_Comparison (BG_adj@{o so} M)] P)) p)
  = (fun p => @t_alg _ _ _ _ (`2 (fobj[to (Fun_EM_iso@{o so c} M)] P)) p) :=
  eq_refl.

(* N19 *)
Fail Example p464_tie_obj@{o so c} (M : MonObject@{o o o})
  (P : SetBG@{o so} M) :
  fobj[BG_Act_EM@{o so} M ◯ EM_Comparison (BG_adj@{o so} M)] P
  = fobj[to (Fun_EM_iso@{o so c} M)] P := eq_refl.

(* CONTROL: the [morphism] field of the tie's structure map, on the nose. *)
Example p464_tie_alg_morphism@{o so c} (M : MonObject@{o o o})
  (P : SetBG@{o so} M) :
  @morphism _ _ _ _
    (@t_alg _ _ _ _
       (`2 (fobj[BG_Act_EM@{o so} M ◯ EM_Comparison (BG_adj@{o so} M)] P)))
  = @morphism _ _ _ _
      (@t_alg _ _ _ _ (`2 (fobj[to (Fun_EM_iso@{o so c} M)] P))) := eq_refl.

(* N20 *)
Fail Example p464_tie_alg_proper@{o so c} (M : MonObject@{o o o})
  (P : SetBG@{o so} M) :
  @proper_morphism _ _ _ _
    (@t_alg _ _ _ _
       (`2 (fobj[BG_Act_EM@{o so} M ◯ EM_Comparison (BG_adj@{o so} M)] P)))
  = @proper_morphism _ _ _ _
      (@t_alg _ _ _ _ (`2 (fobj[to (Fun_EM_iso@{o so c} M)] P))) := eq_refl.

(** ** Closure: a readback, not a refutation *)

Print Assumptions ActMonad.
Print Assumptions EM_MSet_iso.
Print Assumptions MSet_Forget_Monadic.
Print Assumptions U_BG_Monadic.
Print Assumptions tie.

(** ** Guard: the constants of the two targets *)

(* Instance/Fun/Action/Monad.v *)
Check @Category.Instance.Fun.Action.Monad.ActF.
Check @Category.Instance.Fun.Action.Monad.ActF_map.
Check @Category.Instance.Fun.Action.Monad.ActF_obj.
Check @Category.Instance.Fun.Action.Monad.ActMonad.
Check @Category.Instance.Fun.Action.Monad.ActMonad_join.
Check @Category.Instance.Fun.Action.Monad.ActMonad_join_fun.
Check @Category.Instance.Fun.Action.Monad.ActMonad_ret.
Check @Category.Instance.Fun.Action.Monad.ActMonad_ret_fun.
Check @Category.Instance.Fun.Action.Monad.CreatedAct.
Check @Category.Instance.Fun.Action.Monad.CreatedE.
Check @Category.Instance.Fun.Action.Monad.CreatedE_is_coeq.
Check @Category.Instance.Fun.Action.Monad.EM_MSet_iso.
Check @Category.Instance.Fun.Action.Monad.EM_MSet_iso_beck.
Check @Category.Instance.Fun.Action.Monad.EM_MSet_iso_beck_to.
Check @Category.Instance.Fun.Action.Monad.EM_MSet_iso_from.
Check @Category.Instance.Fun.Action.Monad.EM_MSet_iso_to.
Check @Category.Instance.Fun.Action.Monad.EM_act.
Check @Category.Instance.Fun.Action.Monad.EM_act_is_action.
Check @Category.Instance.Fun.Action.Monad.EM_to_MSet.
Check @Category.Instance.Fun.Action.Monad.FreeAct.
Check @Category.Instance.Fun.Action.Monad.Fun_EM_iso.
Check @Category.Instance.Fun.Action.Monad.GAct_Monad.
Check @Category.Instance.Fun.Action.Monad.GAct_Monad_GroupObject.
Check @Category.Instance.Fun.Action.Monad.GAct_Monad_Grp.
Check @Category.Instance.Fun.Action.Monad.GSet_Forget_Monadic.
Check @Category.Instance.Fun.Action.Monad.GSet_Forget_Monadic_GroupObject.
Check @Category.Instance.Fun.Action.Monad.GSet_Forget_Monadic_Grp.
Check @Category.Instance.Fun.Action.Monad.MSet_Forget.
Check @Category.Instance.Fun.Action.Monad.MSet_Forget_Monadic.
Check @Category.Instance.Fun.Action.Monad.MSet_Forget_Monadic_direct.
Check @Category.Instance.Fun.Action.Monad.MSet_Forget_creates.
Check @Category.Instance.Fun.Action.Monad.MSet_Forget_reflects.
Check @Category.Instance.Fun.Action.Monad.MSet_Free.
Check @Category.Instance.Fun.Action.Monad.MSet_adj.
Check @Category.Instance.Fun.Action.Monad.MSet_adj_iso.
Check @Category.Instance.Fun.Action.Monad.MSet_beck_equivalence.
Check @Category.Instance.Fun.Action.Monad.MSet_comparison_equivalence.
Check @Category.Instance.Fun.Action.Monad.MSet_counit_iso.
Check @Category.Instance.Fun.Action.Monad.MSet_extend.
Check @Category.Instance.Fun.Action.Monad.MSet_restrict.
Check @Category.Instance.Fun.Action.Monad.MSet_unit_iso.
Check @Category.Instance.Fun.Action.Monad.Reflected_is_coeq.
Check @Category.Instance.Fun.Action.Monad.act_prod.
Check @Category.Instance.Fun.Action.Monad.act_prod_map.
Check @Category.Instance.Fun.Action.Monad.beck_act.
Check @Category.Instance.Fun.Action.Monad.beck_carrier.
Check @Category.Instance.Fun.Action.Monad.beck_direct_to.
Check @Category.Instance.Fun.Action.Monad.beck_vs_direct.
Check @Category.Instance.Fun.Action.Monad.beck_vs_direct_iso.
Check @Category.Instance.Fun.Action.Monad.comparison_alg_fun.
Check @Category.Instance.Fun.Action.Monad.comparison_alg_is_action.
Check @Category.Instance.Fun.Action.Monad.created_absorb.
Check @Category.Instance.Fun.Action.Monad.created_act.
Check @Category.Instance.Fun.Action.Monad.mset_created_action.
Check @Category.Instance.Fun.Action.Monad.mset_created_arrow.
Check @Category.Instance.Fun.Action.Monad.mset_created_carrier.
Check @Category.Instance.Fun.Action.Monad.mset_created_iso.
Check @Category.Instance.Fun.Action.Monad.split_absorb.

(* Instance/Fun/Action/Monad/BG.v *)
Check @Category.Instance.Fun.Action.Monad.BG.Act_BG_alg.
Check @Category.Instance.Fun.Action.Monad.BG.BGCreatedE.
Check @Category.Instance.Fun.Action.Monad.BG.BGCreatedE_is_coeq.
Check @Category.Instance.Fun.Action.Monad.BG.BGMonad.
Check @Category.Instance.Fun.Action.Monad.BG.BG_Act_EM.
Check @Category.Instance.Fun.Action.Monad.BG.BG_Act_EM_alg.
Check @Category.Instance.Fun.Action.Monad.BG.BG_Act_EM_carrier.
Check @Category.Instance.Fun.Action.Monad.BG.BG_Act_EM_forget_map.
Check @Category.Instance.Fun.Action.Monad.BG.BG_Act_EM_forget_obj.
Check @Category.Instance.Fun.Action.Monad.BG.BG_Act_alg.
Check @Category.Instance.Fun.Action.Monad.BG.BG_EM_iso.
Check @Category.Instance.Fun.Action.Monad.BG.BG_EM_iso_to.
Check @Category.Instance.Fun.Action.Monad.BG.BG_T_ActF.
Check @Category.Instance.Fun.Action.Monad.BG.BG_T_map.
Check @Category.Instance.Fun.Action.Monad.BG.BG_T_obj.
Check @Category.Instance.Fun.Action.Monad.BG.BG_adj.
Check @Category.Instance.Fun.Action.Monad.BG.BG_adj_iso.
Check @Category.Instance.Fun.Action.Monad.BG.BG_beck_equivalence.
Check @Category.Instance.Fun.Action.Monad.BG.BG_extend.
Check @Category.Instance.Fun.Action.Monad.BG.BG_join.
Check @Category.Instance.Fun.Action.Monad.BG.BG_join_ActMonad.
Check @Category.Instance.Fun.Action.Monad.BG.BG_join_fun.
Check @Category.Instance.Fun.Action.Monad.BG.BG_restrict.
Check @Category.Instance.Fun.Action.Monad.BG.BG_ret.
Check @Category.Instance.Fun.Action.Monad.BG.BG_ret_ActMonad.
Check @Category.Instance.Fun.Action.Monad.BG.BG_ret_fun.
Check @Category.Instance.Fun.Action.Monad.BG.F_BG.
Check @Category.Instance.Fun.Action.Monad.BG.GSet_BG_Monadic.
Check @Category.Instance.Fun.Action.Monad.BG.GSet_BG_Monadic_GroupObject.
Check @Category.Instance.Fun.Action.Monad.BG.GSet_BG_Monadic_Grp.
Check @Category.Instance.Fun.Action.Monad.BG.MSet_to_reflects_coeq.
Check @Category.Instance.Fun.Action.Monad.BG.SetBG.
Check @Category.Instance.Fun.Action.Monad.BG.U_BG.
Check @Category.Instance.Fun.Action.Monad.BG.U_BG_Monadic.
Check @Category.Instance.Fun.Action.Monad.BG.U_BG_creates.
Check @Category.Instance.Fun.Action.Monad.BG.U_BG_map.
Check @Category.Instance.Fun.Action.Monad.BG.U_BG_obj.
Check @Category.Instance.Fun.Action.Monad.BG.U_BG_reflects.
Check @Category.Instance.Fun.Action.Monad.BG.bg_created_action.
Check @Category.Instance.Fun.Action.Monad.BG.bg_created_arrow.
Check @Category.Instance.Fun.Action.Monad.BG.bg_created_carrier.
Check @Category.Instance.Fun.Action.Monad.BG.bg_created_iso.
Check @Category.Instance.Fun.Action.Monad.BG.tie.
Check @Category.Instance.Fun.Action.Monad.BG.tie_alg.
Check @Category.Instance.Fun.Action.Monad.BG.tie_alg_fun.
Check @Category.Instance.Fun.Action.Monad.BG.tie_carrier.
