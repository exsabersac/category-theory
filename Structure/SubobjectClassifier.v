Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
   nLab:      https://ncatlab.org/nlab/show/subobject+classifier
   Wikipedia: https://en.wikipedia.org/wiki/Subobject_classifier

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SubobjectClassifier.

Context {C : Category}.
Context `{HT : @Terminal C}.
Context `{HP : @HasPullbacks C}.

Class SubobjectClassifier := {
  Ω : C;                                (* the object of truth values *)
  truth : 1 ~> Ω;                       (* the generic subobject *)

  (* the characteristic morphism of a mono m : u ~> x *)
  char {u x : C} (m : u ~> x) (M : Monic m) : x ~> Ω;

  (* the classifying square is a pullback of truth along char m *)
  char_pullback {u x : C} (m : u ~> x) (M : Monic m) :
    IsPullback (char m M) truth u m one;

  (* and char m unique 态射 property （已译） *)
  char_unique {u x : C} (m : u ~> x) (M : Monic m) (h : x ~> Ω) :
    IsPullback h truth u m one → h ≈ char m M
}.

Context `{HS : SubobjectClassifier}.

(* truth is monic, trivially: its domain is terminal, so any two morphisms
   z ~> 1 already agree by one_unique, before truth is even applied. *)
Lemma truth_monic : Monic truth.
Proof.
  constructor.
  intros z g1 g2 _.
  apply one_unique.
Qed.

(* The generic subobject: truth as a subobject of Ω. *)
Definition truth_subobject : SubObj Ω := {|
  sub_dom      := 1;
  sub_mono     := truth;
  sub_is_monic := truth_monic
|}.

(* A 拉回 square is stable under replacing its second projection an
 ≈-equal 态射; both fields transport rewriting. Companion to
 [is_pullback_respects_left] Theory/Subobject/Functor.v, used below to
 trade chosen projection into 1 典范 [one].（已译） *)
Lemma is_pullback_respects_snd {x y z : C} {f : x ~> z} {g : y ~> z}
      {P : C} {p1 : P ~> x} {p2 p2' : P ~> y} (Hp : p2 ≈ p2') :
  IsPullback f g P p1 p2 → IsPullback f g P p1 p2'.
Proof.
  intros [Hc Hu].
  constructor.
  - now rewrite <- Hp.
  - intros Q q1 q2 Hq.
    pose proof (Hu Q q1 q2 Hq) as U.
    destruct (unique_property U) as [U1 U2].
    unshelve refine {| unique_obj := unique_obj U |}.
    + split.
      * exact U1.
      * now rewrite <- Hp.
    + intros v [Hv1 Hv2].
      apply (uniqueness U); split.
      * exact Hv1.
      * now rewrite Hp.
Qed.

(*
   本节说明函子、拉回/推出、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma is_pullback_precompose_iso {A B Z : C} {f : A ~> Z} {g : B ~> Z}
      {P P' : C} {p1 : P ~> A} {p2 : P ~> B} (i : P' ≅ P)
      {p1' : P' ~> A} {p2' : P' ~> B}
      (H1 : p1 ∘ to i ≈ p1') (H2 : p2 ∘ to i ≈ p2') :
  IsPullback f g P p1 p2 → IsPullback f g P' p1' p2'.
Proof.
  intros Hpb.
  assert (E1 : p1' ∘ from i ≈ p1).
  { rewrite <- H1, <- comp_assoc, iso_to_from; cat. }
  assert (E2 : p2' ∘ from i ≈ p2).
  { rewrite <- H2, <- comp_assoc, iso_to_from; cat. }
  constructor.
  - rewrite <- H1, <- H2, !comp_assoc.
    now rewrite (is_pullback_commutes Hpb).
  - intros Q q1 q2 Hq.
    pose proof (is_pullback_ump Hpb Q q1 q2 Hq) as U.
    destruct (unique_property U) as [U1 U2].
    unshelve refine {| unique_obj := from i ∘ unique_obj U |}.
    + split.
      * now rewrite comp_assoc, E1.
      * now rewrite comp_assoc, E2.
    + intros v [Hv1 Hv2].
      assert (Hvw : unique_obj U ≈ to i ∘ v).
      { apply (uniqueness U); split;
          [ now rewrite comp_assoc, H1
          | now rewrite comp_assoc, H2 ]. }
      rewrite Hvw, comp_assoc, iso_from_to.
      now rewrite id_left.
Qed.

(*
   本节说明等价、同构、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma char_respects {u u' x : C} (m : u ~> x) (M : Monic m)
      (m' : u' ~> x) (M' : Monic m') :
  {| sub_dom := u; sub_mono := m; sub_is_monic := M |}
    ≈ {| sub_dom := u'; sub_mono := m'; sub_is_monic := M' |}
  → char m M ≈ char m' M'.
Proof.
  intros [i Hi]; simpl in Hi.
  symmetry.
  apply char_unique.
  apply (is_pullback_precompose_iso i Hi (one_unique (one ∘ to i) one)).
  exact (char_pullback m' M').
Qed.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma classifier_char_roundtrip {x : C} (h : x ~> Ω) :
  char (sub_mono (sub_reindex h truth_subobject))
       (sub_is_monic (sub_reindex h truth_subobject)) ≈ h.
Proof.
  symmetry.
  apply char_unique.
  apply (is_pullback_respects_snd
           (one_unique (pullback_snd h truth (pullback h truth)) one)).
  exact (pullback_is_pullback h truth (pullback h truth)).
Qed.

(* Round trip (ii): pulling truth back along char m recovers subobject
 (u, m) up SubObj 等价, since classifying square is
 itself 拉回 truth along char m; any two pullbacks one cospan
 agree, via sub_reindex_transport.（已译） *)
Lemma classifier_pullback_roundtrip {x : C} (s : SubObj x) :
  sub_reindex (char (sub_mono s) (sub_is_monic s)) truth_subobject ≈ s.
Proof.
  apply (sub_reindex_transport _ truth_subobject s one).
  apply char_pullback.
Qed.

(*
   本节说明拉回/推出、等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem classifier_classifies (x : C) :
  @Isomorphism Sets {| carrier := SubObj x |} {| carrier := x ~> Ω |}.
Proof using Type HP.
  unshelve econstructor.
  - (* to: classify a subobject by its characteristic morphism *)
    simpl.
    unshelve refine {| morphism := fun s : SubObj x =>
                         char (sub_mono s) (sub_is_monic s) |}.
    (* respects the SubObj equivalence *)
    intros s s' Hs.
    destruct s, s'.
    now apply char_respects.
  - (* from: pull truth back along h *)
    simpl.
    unshelve refine {| morphism := fun h : x ~> Ω =>
                         sub_reindex h truth_subobject |}.
    (* the HasPullbacks instance hole left by refine *)
    1: typeclasses eauto.
    (* respects ≈ of characteristic morphisms *)
    intros h h' Hh.
    now apply sub_reindex_respects_mor.
  - (* to ∘ from ≈ id, pointwise *)
    intro h; simpl.
    apply classifier_char_roundtrip.
  - (* from ∘ to ≈ id, pointwise *)
    intro s; simpl.
    apply classifier_pullback_roundtrip.
Defined.

End SubobjectClassifier.
