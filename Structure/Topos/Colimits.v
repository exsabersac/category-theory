Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Terminal.
Require Import Category.Theory.Equivalence.Pullback.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.Topos.
Require Import Category.Structure.Topos.Power.
Require Import Category.Structure.Topos.Monadic.
Require Import Category.Functor.Hom.Internal.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
   本文件给出 topos 结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Open Scope category_scope.

(*
   nLab:      https://ncatlab.org/nlab/show/topos
   nLab:      https://ncatlab.org/nlab/show/Pare%27s+theorem
   Wikipedia: https://en.wikipedia.org/wiki/Topos
   Paper:     Paré, "Colimits in topoi", Bulletin of the American

   本节说明（余）极限、topos相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ToposColimits.

Context {C : Category}.
Context `{H : @ElementaryTopos C}.

Local Notation TT := (PowF ◯ Opposite_Functor PowF).
Local Notation EMT := (@EilenbergMoore C TT pow_monad).

(*
   本节说明单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Existing Instance pow_monad.

(** ** (A) The terminal algebra *)

(* The 终对象 C carries unique algebra structure, every
 algebra map it unique, both [one_unique]. （已译） *)
Program Definition EM_Terminal : @Terminal EMT := {|
  terminal_obj := (@terminal_obj C _; _)
|}.
Next Obligation.
  unshelve refine {| t_alg := one |}; apply one_unique.
Defined.
Next Obligation.
  unshelve refine {| t_alg_hom := one |}; apply one_unique.
Defined.
Next Obligation.
  destruct f, g; simpl; apply one_unique.
Qed.

(* 相关说明。 （已译） *)

Section EMPullback.

Context {xa ya za : EMT}.
Context (FF : xa ~{EMT}~> za) (GG : ya ~{EMT}~> za).

Definition em_pb : Pullback (t_alg_hom[FF]) (t_alg_hom[GG]) :=
  @pullback C _ _ _ _ (t_alg_hom[FF]) (t_alg_hom[GG]).

Definition em_pb_carrier : C := Pull _ _ em_pb.
Definition em_pb_p1 : em_pb_carrier ~> ``xa := pullback_fst _ _ em_pb.
Definition em_pb_p2 : em_pb_carrier ~> ``ya := pullback_snd _ _ em_pb.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma em_pb_cone :
  t_alg_hom[FF] ∘ (t_alg[projT2 xa] ∘ fmap[TT] em_pb_p1)
    ≈ t_alg_hom[GG] ∘ (t_alg[projT2 ya] ∘ fmap[TT] em_pb_p2).
Proof.
  rewrite !comp_assoc.
  rewrite !t_alg_hom_commutes.
  rewrite <- !comp_assoc, <- !fmap_comp.
  apply compose_respects; [reflexivity|].
  apply fmap_respects.
  exact (pullback_commutes _ _ em_pb).
Qed.

Definition em_pb_action : TT em_pb_carrier ~> em_pb_carrier :=
  unique_obj (ump_pullbacks _ _ em_pb _
                (t_alg[projT2 xa] ∘ fmap[TT] em_pb_p1)
                (t_alg[projT2 ya] ∘ fmap[TT] em_pb_p2)
                em_pb_cone).

Lemma em_pb_action_1 :
  em_pb_p1 ∘ em_pb_action ≈ t_alg[projT2 xa] ∘ fmap[TT] em_pb_p1.
Proof.
  exact (fst (unique_property
    (ump_pullbacks _ _ em_pb _ _ _ em_pb_cone))).
Qed.

Lemma em_pb_action_2 :
  em_pb_p2 ∘ em_pb_action ≈ t_alg[projT2 ya] ∘ fmap[TT] em_pb_p2.
Proof.
  exact (snd (unique_property
    (ump_pullbacks _ _ em_pb _ _ _ em_pb_cone))).
Qed.

(* 相关说明。 （已译） *)
Lemma em_pb_t_id : em_pb_action ∘ ret ≈ id.
Proof.
  apply (is_pullback_jointly_monic (pullback_is_pullback _ _ em_pb)).
  - rewrite comp_assoc, em_pb_action_1, <- comp_assoc, <- fmap_ret,
            comp_assoc, t_id, id_left, id_right.
    reflexivity.
  - rewrite comp_assoc, em_pb_action_2, <- comp_assoc, <- fmap_ret,
            comp_assoc, t_id, id_left, id_right.
    reflexivity.
Qed.

Lemma em_pb_t_action :
  em_pb_action ∘ fmap[TT] em_pb_action ≈ em_pb_action ∘ join.
Proof.
  apply (is_pullback_jointly_monic (pullback_is_pullback _ _ em_pb)).
  - rewrite !comp_assoc, em_pb_action_1, <- !comp_assoc, <- fmap_comp,
            em_pb_action_1, fmap_comp, comp_assoc, t_action,
            <- !comp_assoc, join_fmap_fmap, !comp_assoc.
    reflexivity.
  - rewrite !comp_assoc, em_pb_action_2, <- !comp_assoc, <- fmap_comp,
            em_pb_action_2, fmap_comp, comp_assoc, t_action,
            <- !comp_assoc, join_fmap_fmap, !comp_assoc.
    reflexivity.
Qed.

Definition em_pb_algebra : TAlgebra TT em_pb_carrier := {|
  t_alg    := em_pb_action ;
  t_id     := em_pb_t_id ;
  t_action := em_pb_t_action
|}.

Definition em_pb_alg_obj : EMT := (em_pb_carrier; em_pb_algebra).

Definition em_pb_fst : em_pb_alg_obj ~{EMT}~> xa.
Proof.
  unshelve refine {| t_alg_hom := em_pb_p1 |}.
  exact em_pb_action_1.
Defined.

Definition em_pb_snd : em_pb_alg_obj ~{EMT}~> ya.
Proof.
  unshelve refine {| t_alg_hom := em_pb_p2 |}.
  exact em_pb_action_2.
Defined.

(* 相关说明。 （已译） *)
Lemma em_pb_med_commutes (q : EMT) (q1 : q ~{EMT}~> xa)
      (q2 : q ~{EMT}~> ya)
      (Hq : t_alg_hom[FF] ∘ t_alg_hom[q1] ≈ t_alg_hom[GG] ∘ t_alg_hom[q2]) :
  unique_obj (ump_pullbacks _ _ em_pb _ (t_alg_hom[q1]) (t_alg_hom[q2]) Hq)
    ∘ t_alg[projT2 q]
  ≈ em_pb_action ∘ fmap[TT]
      (unique_obj (ump_pullbacks _ _ em_pb _ (t_alg_hom[q1])
                     (t_alg_hom[q2]) Hq)).
Proof.
  pose proof (unique_property
    (ump_pullbacks _ _ em_pb _ (t_alg_hom[q1]) (t_alg_hom[q2]) Hq))
    as [M1 M2].
  apply (is_pullback_jointly_monic (pullback_is_pullback _ _ em_pb)).
  - rewrite comp_assoc.
    change (pullback_fst _ _ em_pb) with em_pb_p1.
    rewrite M1, (t_alg_hom_commutes (TAlgebraHom := q1)).
    rewrite comp_assoc, em_pb_action_1, <- !comp_assoc, <- !fmap_comp.
    now rewrite M1.
  - rewrite comp_assoc.
    change (pullback_snd _ _ em_pb) with em_pb_p2.
    rewrite M2, (t_alg_hom_commutes (TAlgebraHom := q2)).
    rewrite comp_assoc, em_pb_action_2, <- !comp_assoc, <- !fmap_comp.
    now rewrite M2.
Qed.

(* 相关说明。 （已译） *)
Definition EM_Pullback : Pullback FF GG.
Proof.
  unshelve refine {| Pull         := em_pb_alg_obj
                   ; pullback_fst := em_pb_fst
                   ; pullback_snd := em_pb_snd |}.
  - (* 相关说明。 （已译） *)
    exact (pullback_commutes _ _ em_pb).
  - (* the universal property: the carrier mediator, made an algebra map
       by [em_pb_med_commutes]; uniqueness is the carrier's, since a
       morphism of EMT is determined by its underlying arrow *)
    intros q q1 q2 Hq.
    unshelve refine {| unique_obj := _ |}.
    + unshelve refine {| t_alg_hom := unique_obj
        (ump_pullbacks _ _ em_pb _ t_alg_hom[q1] t_alg_hom[q2] Hq) |}.
      apply em_pb_med_commutes.
    + exact (unique_property
        (ump_pullbacks _ _ em_pb _ t_alg_hom[q1] t_alg_hom[q2] Hq)).
    + intros v Hv.
      exact (uniqueness
        (ump_pullbacks _ _ em_pb _ t_alg_hom[q1] t_alg_hom[q2] Hq)
        t_alg_hom[v] Hv).
Defined.

End EMPullback.

Definition EM_HasPullbacks : @HasPullbacks EMT :=
  {| pullback := fun x y z F G => EM_Pullback F G |}.

(* 相关说明。 （已译） *)

(* The equivalence read backwards: EM(P ◯ P^op) ≃ C^op. *)
Definition pow_equivalence_sym :
  @EquivalenceOfCategories EMT (C^op)
    (@quasi_inverse (C^op) EMT (EM_Comparison pow_adjunction)
       pow_equivalence) :=
  @EquivalenceOfCategories_sym (C^op) EMT (EM_Comparison pow_adjunction)
    pow_equivalence.

(* [@Initial C] IS [@Terminal (C^op)], so terminal algebra transports
 straight 始对象 topos. （已译） *)
Definition topos_Initial : @Initial C :=
  Terminal_transport pow_equivalence_sym EM_Terminal.

Definition topos_HasPullbacks_op : @HasPullbacks (C^op) :=
  HasPullbacks_transport pow_equivalence_sym EM_HasPullbacks.

(* [@Cocartesian C] IS [@Cartesian (C^op)], 终对象 of
 C^op 始对象 just built. （已译） *)
Definition topos_Cocartesian : @Cocartesian C :=
  @Cartesian_of_HasPullbacks_Terminal (C^op) topos_Initial
    topos_HasPullbacks_op.

Definition topos_HasEqualizers_op : @HasEqualizers (C^op) :=
  @HasEqualizers_of_HasPullbacks_Terminal (C^op) topos_Initial
    topos_HasPullbacks_op.

Definition topos_HasCoequalizers : @HasCoequalizers C :=
  @HasCoequalizers_of_HasEqualizers_op C topos_HasEqualizers_op.

Definition topos_HasPushouts : @HasPushouts C :=
  HasPushouts_of_HasPullbacks_op topos_HasPullbacks_op.

(* MAC LANE §IV.10 REMARK 2, at generator level: initial object, binary
   coproducts, coequalizers, pushouts. *)
Definition topos_has_finite_colimits :
  @Initial C * @Cocartesian C * @HasCoequalizers C * @HasPushouts C :=
  (topos_Initial, topos_Cocartesian, topos_HasCoequalizers,
   topos_HasPushouts).

(** ** (D) Readbacks *)

(* The 始对象 IS quasi-inverse's image terminal
 algebra, terminal algebra's carrier IS 终对象 of
 topos -- both nose. （已译） *)
Example topos_Initial_obj :
  @initial_obj C topos_Initial
    = @quasi_inverse (C^op) EMT (EM_Comparison pow_adjunction)
        pow_equivalence (@terminal_obj EMT EM_Terminal) := eq_refl.

Example EM_Terminal_carrier :
  ``(@terminal_obj EMT EM_Terminal) = @terminal_obj C _ := eq_refl.

(* 相关说明。 （已译） *)
Example EM_Pullback_carrier {xa ya za : EMT}
        (FF : xa ~{EMT}~> za) (GG : ya ~{EMT}~> za) :
  ``(Pull FF GG (EM_Pullback FF GG)) = em_pb_carrier FF GG := eq_refl.

Example EM_Pullback_fst {xa ya za : EMT}
        (FF : xa ~{EMT}~> za) (GG : ya ~{EMT}~> za) :
  t_alg_hom[pullback_fst FF GG (EM_Pullback FF GG)]
    = em_pb_p1 FF GG := eq_refl.

Example EM_Pullback_snd {xa ya za : EMT}
        (FF : xa ~{EMT}~> za) (GG : ya ~{EMT}~> za) :
  t_alg_hom[pullback_snd FF GG (EM_Pullback FF GG)]
    = em_pb_p2 FF GG := eq_refl.

(* 相关说明。 （已译） *)
Example topos_HasPushouts_is_op {x y z : C} (f : x ~> y) (g : x ~> z) :
  @pushout C topos_HasPushouts x y z f g
    = @pullback (C^op) topos_HasPullbacks_op y z x f g := eq_refl.

(* 相关说明。 （已译） *)
Example topos_has_finite_colimits_fst :
  fst (fst (fst topos_has_finite_colimits)) = topos_Initial := eq_refl.

Example topos_has_finite_colimits_snd :
  snd (fst (fst topos_has_finite_colimits)) = topos_Cocartesian := eq_refl.

Example topos_has_finite_colimits_thd :
  snd (fst topos_has_finite_colimits) = topos_HasCoequalizers := eq_refl.

Example topos_has_finite_colimits_fth :
  snd topos_has_finite_colimits = topos_HasPushouts := eq_refl.

End ToposColimits.
