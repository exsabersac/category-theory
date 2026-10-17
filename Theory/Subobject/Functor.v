Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Structure.Pullback.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/subobject

   本文件给出函子相关定义或实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SubFunctor.

Context {C : Category}.
Context `{@HasPullbacks C}.

(* 相关说明。 （已译） *)
Definition sub_reindex {x y : C} (f : y ~> x) (u : SubObj x) : SubObj y := {|
  sub_dom  := Pull f (sub_mono u) (pullback f (sub_mono u));
  sub_mono := pullback_fst f (sub_mono u) (pullback f (sub_mono u));
  sub_is_monic := monic_pullback_stable f (sub_mono u) (sub_is_monic u)
                    (pullback f (sub_mono u))
|}.

(*
   本节说明拉回/推出、同构、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma sub_reindex_transport {x y : C} (f : y ~> x) (u : SubObj x)
      (v : SubObj y) (p2 : sub_dom v ~> sub_dom u)
      (HP : IsPullback f (sub_mono u) (sub_dom v) (sub_mono v) p2) :
  sub_reindex f u ≈ v.
Proof.
  pose proof (pullback_transport (pullback f (sub_mono u))
                                 (is_pullback_pullback HP)) as T.
  exists (transport_iso T).
  exact (transport_fst T).
Qed.

(* Reindexing respects the SubObj setoid: if u ≈ v via a domain isomorphism
   i, then the chosen pullback of v along f, corrected by i, is itself a
   pullback square for sub_mono u along f; sub_reindex_transport concludes. *)
#[export] Instance sub_reindex_respects {x y : C} (f : y ~> x) :
  Proper (equiv ==> equiv) (@sub_reindex x y f).
Proof.
  intros u v [i Hi].
  apply (sub_reindex_transport
           f u (sub_reindex f v)
           (from i ∘ pullback_snd f (sub_mono v) (pullback f (sub_mono v)))).
  constructor; simpl.
  - (* the corrected square commutes *)
    rewrite (pullback_commutes f (sub_mono v) (pullback f (sub_mono v))).
    rewrite <- Hi.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (to i)).
    rewrite iso_to_from; cat.
  - intros Q q1 q2 Hq.
    (* transport cone across i mediate 进入 chosen pullback （已译） *)
    assert (Hq' : f ∘ q1 ≈ sub_mono v ∘ (to i ∘ q2)).
    { rewrite Hq, <- Hi.
      now rewrite comp_assoc. }
    pose proof (ump_pullbacks f (sub_mono v) (pullback f (sub_mono v))
                              Q q1 (to i ∘ q2) Hq') as W.
    destruct (unique_property W) as [W1 W2].
    unshelve refine {| unique_obj := unique_obj W |}.
    + split.
      * exact W1.
      * rewrite <- comp_assoc.
        rewrite W2.
        rewrite comp_assoc.
        rewrite iso_from_to; cat.
    + intros w [Hw1 Hw2].
      apply (uniqueness W); split.
      * exact Hw1.
      * rewrite <- Hw2.
        rewrite !comp_assoc.
        rewrite iso_to_from; cat.
Qed.

(* A pullback square is stable under replacing the left leg of its cospan by
   an ≈-equal morphism; both fields transport by rewriting. *)
Lemma is_pullback_respects_left {x y z : C} {f f' : x ~> z} {g : y ~> z}
      {P : C} {p1 : P ~> x} {p2 : P ~> y} (Hf : f ≈ f') :
  IsPullback f g P p1 p2 → IsPullback f' g P p1 p2.
Proof.
  intros [Hc Hu].
  constructor.
  - now rewrite <- Hf.
  - intros Q q1 q2 Hq.
    apply Hu.
    now rewrite Hf.
Qed.

(* Reindexing along ≈-equal morphisms yields equivalent subobjects: the
   chosen pullback along f is also a pullback square along f'. *)
Lemma sub_reindex_respects_mor {x y : C} (f f' : y ~> x) (Hf : f ≈ f')
      (u : SubObj x) :
  sub_reindex f u ≈ sub_reindex f' u.
Proof.
  symmetry.
  apply (sub_reindex_transport
           f' u (sub_reindex f u)
           (pullback_snd f (sub_mono u) (pullback f (sub_mono u)))).
  apply (is_pullback_respects_left Hf).
  apply pullback_is_pullback.
Qed.

(* 相关说明。 （已译） *)
Lemma is_pullback_along_id {x y : C} (m : y ~> x) :
  IsPullback id m y m id.
Proof.
  constructor.
  - cat.
  - intros Q q1 q2 Hq.
    rewrite id_left in Hq.
    unshelve refine {| unique_obj := q2 |}.
    + split.
      * now rewrite <- Hq.
      * cat.
    + intros w [Hw1 Hw2].
      now rewrite <- Hw2; cat.
Qed.

(* Reindexing along 恒等 恒等 subobjects. （已译） *)
Lemma sub_reindex_id {x : C} (u : SubObj x) : sub_reindex id u ≈ u.
Proof.
  apply (sub_reindex_transport id u u id).
  apply is_pullback_along_id.
Qed.

(* Reindexing along 复合 g ∘ f reindexing along g then along
 f: pasting two chosen squares exhibits double pullback one
 pullback square 复合. （已译） *)
Lemma sub_reindex_comp {x y z : C} (g : y ~> x) (f : z ~> y)
      (u : SubObj x) :
  sub_reindex (g ∘ f) u ≈ sub_reindex f (sub_reindex g u).
Proof.
  apply (sub_reindex_transport
           (g ∘ f) u (sub_reindex f (sub_reindex g u))
           (pullback_snd g (sub_mono u) (pullback g (sub_mono u))
              ∘ pullback_snd f (sub_mono (sub_reindex g u))
                  (pullback f (sub_mono (sub_reindex g u))))).
  apply (pullback_paste
           (pullback_is_pullback g (sub_mono u) (pullback g (sub_mono u)))
           (pullback_is_pullback f (sub_mono (sub_reindex g u))
              (pullback f (sub_mono (sub_reindex g u))))).
Qed.

(*
   本节说明函子、拉回/推出、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Local Obligation Tactic := simpl; intros.

Program Definition Sub : C^op ⟶ Sets := {|
  fobj := fun x : C => {| carrier   := SubObj x
                        ; is_setoid := @SubObj_Setoid C x |};
  fmap := fun x y (f : x ~{C^op}~> y) =>
            {| morphism := sub_reindex (unop f)
             ; proper_morphism := sub_reindex_respects (unop f) |}
|}.
Next Obligation.
  repeat intro.
  apply sub_reindex_respects_mor.
  exact X.
Qed.
Next Obligation.
  apply sub_reindex_id.
Qed.
Next Obligation.
  apply sub_reindex_comp.
Qed.

End SubFunctor.
