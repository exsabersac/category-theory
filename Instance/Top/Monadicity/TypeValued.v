Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.BeckObjects.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.

Generalizable All Variables.

(** * The underlying-set functor of the Type-valued [Top] is not monadic *)

(*
 nLab: https://ncatlab.org/nlab/show/monadic+functor

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The identity of [bool], continuous from the discrete space to the
   indiscrete one (Instance/Top.v's [into_indiscrete_continuous]). *)
Definition top_bool_to_indisc@{o h | o < h +} :
  Bool_Discrete@{o} ~{Top@{h o}}~> TwoPoint_Indiscrete@{o} :=
  @Build_ContinuousMorphism Bool_Discrete@{o} TwoPoint_Indiscrete@{o}
    setoid_morphism_id
    (into_indiscrete_continuous Bool_Discrete@{o} bool_setoid_object@{o o}
       setoid_morphism_id).

(* No continuous map back is the identity on points: it would make the
   identity continuous, which Instance/Top.v's
   [indiscrete_to_discrete_id_not_continuous] refutes. *)
Lemma no_top_indisc_to_bool@{o h | o < h +}
  (g : TwoPoint_Indiscrete@{o} ~{Top@{h o}}~> Bool_Discrete@{o}) :
  (∀ b : bool, continuous_map g b = b) → False.
Proof.
  intros Hg.
  apply (@indiscrete_to_discrete_id_not_continuous@{h o}).
  intros U HU.
  apply (open_respects TwoPoint_Indiscrete@{o}
           (fun x => U (continuous_map g x))).
  - intro x; simpl. rewrite (Hg x). split; intro u; exact u.
  - exact (continuity g U HU).
Qed.

Lemma Top_Forget_not_Monadic@{o h so m m0 m1 m3 m6 |
  o < h, h < so, h < m0, so <= m, h <= m1, so <= m3, m1 <= m, m3 <= m +} :
  Monadic@{m m0 m1 h m3 h so m6} Top_Forget@{o h so} → False.
Proof.
  intros [F [A E]].
  pose proof (Equivalence_Full E) as HF.
  lazymatch type of E with
  | @EquivalenceOfCategories _ ?EM ?K =>
    assert (If : @IsIsomorphism Sets@{h so} _ _
                   (fmap[EM_Forget _] (fmap[K] top_bool_to_indisc@{o h})))
  end.
  { unshelve econstructor; [ exact setoid_morphism_id | intro b; reflexivity
                            | intro b; reflexivity ]. }
  destruct (@reflects_iso _ _ _ (em_forget_reflects_isos _) _ _ _ If)
    as [g Hr Hl].
  apply (no_top_indisc_to_bool
           (@prefmap _ _ _ HF TwoPoint_Indiscrete@{o} Bool_Discrete@{o} g)).
  intro b. transitivity (t_alg_hom[g] b).
  - exact (@fmap_sur _ _ _ HF TwoPoint_Indiscrete@{o} Bool_Discrete@{o} g b).
  - exact (Hr b).
Qed.
