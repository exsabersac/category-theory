Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Regular.

Generalizable All Variables.

(** * Interdefinability of the finite (co)limit constructions *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Limit_(category_theory)

   本文件给出拉回相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ====================================================================== *)
(** * (A) Cartesian + equalizers give pullbacks                           *)

Section PullbackFromEqualizer.

Context {C : Category}.
Context `{@Cartesian C}.

(* maclane:III.4:ex7, forward; awodey:5.2:prop7, forward.  The two legs
   of the cospan are shifted onto the product and their equalizer taken:
   an element of x × y equalizing f ∘ exl and g ∘ exr is exactly a pair
   whose two components agree over z.  The projections of the resulting
   pullback square are the two components of the equalizing map. *)
Lemma pullback_of_equalizer {x y z : C} (f : x ~> z) (g : y ~> z)
      {E : C} {e : E ~> x × y}
      (Eq : IsEqualizer (f ∘ exl) (g ∘ exr) E e) :
  IsPullback f g E (exl ∘ e) (exr ∘ e).
Proof.
  constructor.
  - rewrite !comp_assoc.
    exact (fork_eq Eq).
  - intros Q q1 q2 Hq.
    assert (Hh : (f ∘ exl) ∘ (q1 △ q2) ≈ (g ∘ exr) ∘ (q1 △ q2)).
    { rewrite <- !comp_assoc, exl_fork, exr_fork.
      exact Hq. }
    destruct (eq_desc Eq (q1 △ q2) Hh) as [u Hu Huniq].
    unshelve eapply Build_Unique.
    + exact u.
    + split.
      * rewrite <- comp_assoc, Hu.
        apply exl_fork.
      * rewrite <- comp_assoc, Hu.
        apply exr_fork.
    + intros v [Hv1 Hv2].
      apply Huniq.
      apply ump_products; split.
      * rewrite comp_assoc.
        exact Hv1.
      * rewrite comp_assoc.
        exact Hv2.
Qed.

End PullbackFromEqualizer.

Definition HasPullbacks_of_Cartesian_HasEqualizers {C : Category}
           `{@Cartesian C} (E : @HasEqualizers C) : @HasPullbacks C.
Proof.
  constructor.
  intros x y z f g.
  destruct (@equalizer C E (x × y)%object z (f ∘ exl) (g ∘ exr))
    as [q [e Eq]].
  exact (is_pullback_pullback (pullback_of_equalizer f g Eq)).
Defined.

(* ====================================================================== *)
(** * (B) The converse: a pullback square is an equalizer                 *)

Section EqualizerFromPullback.

Context {C : Category}.
Context `{@Cartesian C}.

Lemma equalizer_of_pullback {x y z : C} {f : x ~> z} {g : y ~> z}
      {P : C} {p1 : P ~> x} {p2 : P ~> y}
      (HP : IsPullback f g P p1 p2) :
  IsEqualizer (f ∘ exl) (g ∘ exr) P (p1 △ p2).
Proof.
  constructor.
  - rewrite <- !comp_assoc, exl_fork, exr_fork.
    exact (is_pullback_commutes HP).
  - intros Q h Hh.
    assert (Hq : f ∘ (exl ∘ h) ≈ g ∘ (exr ∘ h)).
    { rewrite !comp_assoc.
      exact Hh. }
    destruct (is_pullback_ump HP Q (exl ∘ h) (exr ∘ h) Hq)
      as [u [Hu1 Hu2] Huniq].
    unshelve eapply Build_Unique.
    + exact u.
    + rewrite <- fork_comp.
      symmetry.
      apply ump_products; split.
      * symmetry; exact Hu1.
      * symmetry; exact Hu2.
    + intros v Hv.
      apply Huniq; split.
      * rewrite <- Hv.
        now rewrite exl_fork_comp.
      * rewrite <- Hv.
        now rewrite exr_fork_comp.
Qed.

(** ** The two passages round-trip, up to [≈] but not on the nose *)

(* Starting from an equalizer [e : E ~> x × y] of the shifted pair, (A)
   produces the projections exl ∘ e and exr ∘ e, and (B) pairs them back
   up.  The result is [e] again -- but only up to [≈]: [fork_exl_exr] is a
   [≈]-law, not a conversion, so the strict form is refuted (see the
   probes at the end of the file). *)
Lemma equalizer_pullback_round {x y : C} (E : C) (e : E ~> x × y) :
  (exl ∘ e) △ (exr ∘ e) ≈ e.
Proof.
  now rewrite fork_comp, fork_exl_exr, id_left.
Qed.

(* The other composite, on each projection separately; this is exactly
   [exl_fork]/[exr_fork], i.e. again a [≈]-law and not a conversion. *)
Lemma pullback_equalizer_round_fst {x y : C} {P : C}
      (p1 : P ~> x) (p2 : P ~> y) : exl ∘ (p1 △ p2) ≈ p1.
Proof. apply exl_fork. Qed.

Lemma pullback_equalizer_round_snd {x y : C} {P : C}
      (p1 : P ~> x) (p2 : P ~> y) : exr ∘ (p1 △ p2) ≈ p2.
Proof. apply exr_fork. Qed.

End EqualizerFromPullback.

(* ====================================================================== *)
(** * (C) The kernel pair as an equalizer                                 *)

Section KernelPair.

Context {C : Category}.
Context `{@Cartesian C}.

(* maclane:III.4:ex7, second clause.  The kernel pair of f is the
   pullback of f along ITSELF, so this is (B) read at g := f and carries
   no new proof content -- the whole statement is [equalizer_of_pullback]
   instantiated, and it is written that way rather than reproved. *)
Lemma kernel_pair_of_IsPullback {x y : C} {f : x ~> y}
      {P : C} {p1 p2 : P ~> x} (HP : IsPullback f f P p1 p2) :
  IsEqualizer (f ∘ exl) (f ∘ exr) P (p1 △ p2).
Proof. exact (equalizer_of_pullback HP). Qed.

(* The tie to the tree's existing notion.  Structure/Regular.v already
   defines [kernel_pair f := pullback f f] under [HasPullbacks], and the
   statements below are about THAT constant -- no parallel notion of a
   kernel pair is introduced here.  The identification is definitional
   ([kernel_pair_is_pullback_along_itself], by [eq_refl]). *)
Context `{HPB : @HasPullbacks C}.

Definition kernel_pair_fst {x y : C} (f : x ~> y) :
  Pull f f (kernel_pair f) ~> x := pullback_fst f f (kernel_pair f).

Definition kernel_pair_snd {x y : C} (f : x ~> y) :
  Pull f f (kernel_pair f) ~> x := pullback_snd f f (kernel_pair f).

Lemma kernel_pair_IsEqualizer {x y : C} (f : x ~> y) :
  IsEqualizer (f ∘ exl) (f ∘ exr) (Pull f f (kernel_pair f))
              (kernel_pair_fst f △ kernel_pair_snd f).
Proof.
  exact (kernel_pair_of_IsPullback
           (pullback_is_pullback f f (kernel_pair f))).
Qed.

Example kernel_pair_is_pullback_along_itself {x y : C} (f : x ~> y) :
  kernel_pair f = pullback f f := eq_refl.

End KernelPair.

(* ====================================================================== *)
(** * (D) Pullbacks give equalizers: two genuinely different squares      *)

Section EqualizerFromPullbackSquares.

Context {C : Category}.
Context `{@Cartesian C}.
Context {x y : C}.
Context (f g : x ~> y).

(** ** Mac Lane's square (maclane:III.4:ex9) *)

Definition ml_left  : x ~> x × y := id △ f.
Definition ml_right : x ~> x × y := id △ g.

Lemma ml_projections_agree {E : C} {p1 p2 : E ~> x}
      (HP : IsPullback ml_left ml_right E p1 p2) : p1 ≈ p2.
Proof.
  pose proof (is_pullback_commutes HP) as Hc.
  assert (Hl : exl ∘ (ml_left ∘ p1) ≈ exl ∘ (ml_right ∘ p2))
    by now rewrite Hc.
  unfold ml_left, ml_right in Hl.
  rewrite !comp_assoc, !exl_fork, !id_left in Hl.
  exact Hl.
Qed.

Lemma equalizer_of_pullback_maclane {E : C} {p1 p2 : E ~> x}
      (HP : IsPullback ml_left ml_right E p1 p2) :
  IsEqualizer f g E p1.
Proof.
  pose proof (is_pullback_commutes HP) as Hc.
  pose proof (ml_projections_agree HP) as Hp.
  assert (Hr : f ∘ p1 ≈ g ∘ p2).
  { assert (Hr' : exr ∘ (ml_left ∘ p1) ≈ exr ∘ (ml_right ∘ p2))
      by now rewrite Hc.
    unfold ml_left, ml_right in Hr'.
    rewrite !comp_assoc, !exr_fork in Hr'.
    exact Hr'. }
  constructor.
  - rewrite Hr.
    now rewrite Hp.
  - intros Q h Hh.
    assert (Hcomm : ml_left ∘ h ≈ ml_right ∘ h).
    { unfold ml_left, ml_right.
      rewrite <- !fork_comp, !id_left.
      now rewrite Hh. }
    destruct (is_pullback_ump HP Q h h Hcomm) as [u [Hu1 Hu2] Huniq].
    unshelve eapply Build_Unique.
    + exact u.
    + exact Hu1.
    + intros v Hv.
      apply Huniq; split.
      * exact Hv.
      * now rewrite <- Hp.
Qed.

(** ** Awodey's and Riehl's square (awodey:5:ex3, riehl:3.5:lem16) *)

Definition aw_diag : y ~> y × y := id △ id.
Definition aw_pair : x ~> y × y := f △ g.

Lemma equalizer_of_pullback_awodey {E : C} {p1 : E ~> x} {p2 : E ~> y}
      (HP : IsPullback aw_pair aw_diag E p1 p2) :
  IsEqualizer f g E p1.
Proof.
  pose proof (is_pullback_commutes HP) as Hc.
  assert (Hl : f ∘ p1 ≈ p2).
  { assert (H' : exl ∘ (aw_pair ∘ p1) ≈ exl ∘ (aw_diag ∘ p2))
      by now rewrite Hc.
    unfold aw_pair, aw_diag in H'.
    rewrite !comp_assoc, !exl_fork, id_left in H'.
    exact H'. }
  assert (Hr : g ∘ p1 ≈ p2).
  { assert (H' : exr ∘ (aw_pair ∘ p1) ≈ exr ∘ (aw_diag ∘ p2))
      by now rewrite Hc.
    unfold aw_pair, aw_diag in H'.
    rewrite !comp_assoc, !exr_fork, id_left in H'.
    exact H'. }
  constructor.
  - now rewrite Hl, Hr.
  - intros Q h Hh.
    assert (Hcomm : aw_pair ∘ h ≈ aw_diag ∘ (f ∘ h)).
    { unfold aw_pair, aw_diag.
      rewrite <- !fork_comp, !id_left.
      now rewrite Hh. }
    destruct (is_pullback_ump HP Q h (f ∘ h) Hcomm) as [u [Hu1 Hu2] Huniq].
    unshelve eapply Build_Unique.
    + exact u.
    + exact Hu1.
    + intros v Hv.
      apply Huniq; split.
      * exact Hv.
      * rewrite <- Hl, <- comp_assoc.
        now rewrite Hv.
Qed.

(** ** Comparing the two squares

    The two cospans are not the same square.  They do not share a
    codomain (x × y against y × y), and their legs are not even parallel:
    Mac Lane's two legs both issue from x, Awodey's from x and from y.
    Those are refuted at the end of the file, the leg comparisons being
    FORMABILITY negatives (ill-typed when x and y differ) rather than
    conversion negatives.

    The difference is not merely syntactic, and the FOUR lemmas below
    bear on it: BOTH of Mac Lane's legs are split monic, with the single
    common retraction exl, whereas [exl ∘ aw_pair] is f, which is not an
    identity FOR GENERAL f.  Read that hedge strictly.  It does NOT say
    Awodey's leg is never split -- at f := id it is, by [ml_right_split]
    -- and an earlier draft of this comment concluded "so no relabelling
    of objects can turn one cospan into the other", which is REFUTED by
    this file's own [maclane_awodey_degenerate_left]/[_right], where at
    f := id the two cospans are the same two morphisms.  No non-existence
    of a cospan isomorphism is proved anywhere here.  What is true is
    that the two vertices are canonically
    isomorphic, both being equalizers of the same parallel pair, and that
    the comparison commutes with the two equalizing maps. *)

Lemma ml_left_split : exl ∘ ml_left ≈ id.
Proof. unfold ml_left. apply exl_fork. Qed.

Lemma ml_right_split : exl ∘ ml_right ≈ id.
Proof. unfold ml_right. apply exl_fork. Qed.

Lemma aw_diag_split : exl ∘ aw_diag ≈ id.
Proof. unfold aw_diag. apply exl_fork. Qed.

(* Awodey's other leg retracts to f.  NOTE THE NAME: an earlier draft
   called this [aw_pair_not_split], which asserted more than it proves and
   more than is true -- at f := id this very statement makes [aw_pair]
   split, discharged by [ml_right_split] above.  All that is proved is the
   retraction identity. *)
Lemma aw_pair_retracts_to_f : exl ∘ aw_pair ≈ f.
Proof. unfold aw_pair. apply exl_fork. Qed.

Lemma maclane_awodey_iso {E F : C} {p1 p2 : E ~> x} {r1 : F ~> x} {r2 : F ~> y}
      (HE : IsPullback ml_left ml_right E p1 p2)
      (HF : IsPullback aw_pair aw_diag F r1 r2) : E ≅ F.
Proof.
  exact (equalizer_unique f g (equalizer_of_pullback_maclane HE)
                              (equalizer_of_pullback_awodey HF)).
Defined.

Lemma maclane_awodey_iso_commutes {E F : C} {p1 p2 : E ~> x}
      {r1 : F ~> x} {r2 : F ~> y}
      (HE : IsPullback ml_left ml_right E p1 p2)
      (HF : IsPullback aw_pair aw_diag F r1 r2) :
  r1 ∘ to (maclane_awodey_iso HE HF) ≈ p1
    ∧ p1 ∘ from (maclane_awodey_iso HE HF) ≈ r1.
Proof.
  split; simpl.
  - exact (unique_property
             (eq_desc (equalizer_of_pullback_awodey HF) p1
                (fork_eq (equalizer_of_pullback_maclane HE)))).
  - exact (unique_property
             (eq_desc (equalizer_of_pullback_maclane HE) r1
                (fork_eq (equalizer_of_pullback_awodey HF)))).
Qed.

End EqualizerFromPullbackSquares.

(** The two cospans coincide, up to swapping the two legs, exactly in the
    degenerate case f = id.  Both sides are checked at Leibniz equality. *)

Example maclane_awodey_degenerate_left {C : Category} `{@Cartesian C}
        {x : C} : @ml_left C _ x x id = @aw_diag C _ x := eq_refl.

Example maclane_awodey_degenerate_right {C : Category} `{@Cartesian C}
        {x : C} (g : x ~> x) :
  @ml_right C _ x x g = @aw_pair C _ x x id g := eq_refl.

(* ====================================================================== *)
(** * (E) Pullbacks and a terminal object give products and equalizers    *)

Section ProductFromPullback.

Context {C : Category}.
Context `{T : @Terminal C}.
Context {x y : C}.
Context {P : C} {p1 : P ~> x} {p2 : P ~> y}.
Context (HP : IsPullback (one : x ~> 1) (one : y ~> 1) P p1 p2).

(* maclane:III.4:ex10; awodey:5.4:prop16; riehl:3.5:lem15, binary case.
   Pulling back over the terminal object imposes no condition -- the
   square commutes automatically, by [one_unique] -- so the pullback of
   x --!--> 1 <--!-- y is the product, and its universal property is the
   product's with the commutation hypothesis discharged rather than
   assumed.  The conclusion is stated at [IsCartesianProduct], the
   apex-pinned form, before any class is packaged. *)
Definition pb_fork {a : C} (u : a ~> x) (v : a ~> y) : a ~> P :=
  unique_obj (is_pullback_ump HP a u v (one_unique _ _)).

Lemma pb_fork_fst {a : C} (u : a ~> x) (v : a ~> y) :
  p1 ∘ pb_fork u v ≈ u.
Proof.
  unfold pb_fork.
  now destruct (unique_property (is_pullback_ump HP a u v (one_unique _ _))).
Qed.

Lemma pb_fork_snd {a : C} (u : a ~> x) (v : a ~> y) :
  p2 ∘ pb_fork u v ≈ v.
Proof.
  unfold pb_fork.
  now destruct (unique_property (is_pullback_ump HP a u v (one_unique _ _))).
Qed.

Lemma pb_fork_unique {a : C} (u : a ~> x) (v : a ~> y) (h : a ~> P) :
  p1 ∘ h ≈ u → p2 ∘ h ≈ v → pb_fork u v ≈ h.
Proof.
  intros H1 H2.
  exact (uniqueness (is_pullback_ump HP a u v (one_unique _ _)) h
           (H1, H2)).
Qed.

Definition product_of_pullback : @IsCartesianProduct C x y P.
Proof using All.
  unshelve econstructor.
  - exact (@pb_fork).
  - exact p1.
  - exact p2.
  - intros a u u' Hu v v' Hv.
    apply pb_fork_unique.
    + now rewrite pb_fork_fst.
    + now rewrite pb_fork_snd.
  - intros a u v h; split.
    + intros Hh; split.
      * rewrite Hh.
        apply pb_fork_fst.
      * rewrite Hh.
        apply pb_fork_snd.
    + intros [H1 H2].
      symmetry.
      now apply pb_fork_unique.
Defined.

End ProductFromPullback.

Section CartesianFromPullbacks.

Context {C : Category}.
Context `{T : @Terminal C}.
Context (HPB : @HasPullbacks C).

(* The chosen pullback of the terminal cospan a --!--> 1 <--!-- b. *)
Definition pb_chosen (a b : C) : Pullback (one : a ~> 1) (one : b ~> 1) :=
  @pullback C HPB a b 1%object one one.

Definition pb_prod (a b : C) : C := Pull _ _ (pb_chosen a b).

Definition pb_prod_IsCartesianProduct (a b : C) :
  @IsCartesianProduct C a b (pb_prod a b) :=
  product_of_pullback (pullback_is_pullback one one (pb_chosen a b)).

Definition Cartesian_of_HasPullbacks_Terminal : @Cartesian C := {|
  product_obj := pb_prod ;
  fork := fun a b c u v =>
            @fork' C b c (pb_prod b c) (pb_prod_IsCartesianProduct b c) a u v ;
  exl := fun a b => @exl' C a b (pb_prod a b)
                      (pb_prod_IsCartesianProduct a b) ;
  exr := fun a b => @exr' C a b (pb_prod a b)
                      (pb_prod_IsCartesianProduct a b) ;
  fork_respects := fun a b c =>
    @fork'_respects C b c (pb_prod b c) (pb_prod_IsCartesianProduct b c) a ;
  ump_products := fun a b c =>
    @ump_product C b c (pb_prod b c) (pb_prod_IsCartesianProduct b c) a
|}.

(* Combining (E) with (D): the Awodey square is now available, so a
   category with pullbacks and a terminal object has all equalizers. *)
Definition HasEqualizers_of_HasPullbacks_Terminal : @HasEqualizers C.
Proof using All.
  pose (CC := Cartesian_of_HasPullbacks_Terminal).
  constructor.
  intros a b f g.
  exists (Pull _ _ (@pullback C HPB a b (@product_obj C CC b b)
                      (@aw_pair C CC a b f g) (@aw_diag C CC b))).
  exists (pullback_fst _ _ _).
  exact (@equalizer_of_pullback_awodey C CC a b f g _ _ _
           (pullback_is_pullback _ _ _)).
Defined.

End CartesianFromPullbacks.

(* ====================================================================== *)
(** * (F) The dual: cocartesian + coequalizers give pushouts              *)

Section Duality.

Context {C : Category}.

Definition IsEqualizer_op_of_IsCoequalizer {x y : C} {f g : x ~> y}
           {q : C} {e : y ~> q} (E : IsCoequalizer f g q e) :
  @IsEqualizer (C^op) y x f g q e :=
  @Build_IsEqualizer (C^op) y x f g q e (cofork E)
    (fun z h Hh => coeq_desc E h Hh).

Definition IsCoequalizer_of_IsEqualizer_op {x y : C} {f g : x ~> y}
           {q : C} {e : y ~> q} (E : @IsEqualizer (C^op) y x f g q e) :
  IsCoequalizer f g q e :=
  @Build_IsCoequalizer C x y f g q e (fork_eq E)
    (fun z h Hh => eq_desc E h Hh).

Example IsCoequalizer_op_round {x y : C} {f g : x ~> y}
        {q : C} {e : y ~> q} (E : IsCoequalizer f g q e) :
  IsCoequalizer_of_IsEqualizer_op (IsEqualizer_op_of_IsCoequalizer E) = E
  := eq_refl.

Example IsEqualizer_op_round {x y : C} {f g : x ~> y}
        {q : C} {e : y ~> q} (E : @IsEqualizer (C^op) y x f g q e) :
  IsEqualizer_op_of_IsCoequalizer (IsCoequalizer_of_IsEqualizer_op E) = E
  := eq_refl.

Definition HasEqualizers_op_of_HasCoequalizers
           (E : @HasCoequalizers C) : @HasEqualizers (C^op).
Proof.
  constructor.
  intros x y f g.
  destruct (@coeq C E y x f g) as [q [e Eq]].
  exists q, e.
  exact (IsEqualizer_op_of_IsCoequalizer Eq).
Defined.

Definition HasCoequalizers_of_HasEqualizers_op
           (E : @HasEqualizers (C^op)) : @HasCoequalizers C.
Proof.
  constructor.
  intros x y f g.
  destruct (@equalizer (C^op) E y x f g) as [q [e Eq]].
  exists q, e.
  exact (IsCoequalizer_of_IsEqualizer_op Eq).
Defined.

End Duality.

Section PushoutFromCoequalizer.

Context {C : Category}.
Context `{O : @Cocartesian C}.

(* The coproduct vocabulary of Structure/Cocartesian.v is the product
   vocabulary of C^op ON THE NOSE, which is what lets (A) be instantiated
   below with no translation step at all. *)
Example Coprod_is_op_product (a b : C) :
  @Coprod C O a b = @product_obj (C^op) O a b := eq_refl.

Example inl_is_op_exl {a b : C} :
  (@inl C O a b) = @exl (C^op) O a b := eq_refl.

Example inr_is_op_exr {a b : C} :
  (@inr C O a b) = @exr (C^op) O a b := eq_refl.

Lemma pushout_of_coequalizer {x y z : C} (f : x ~> y) (g : x ~> z)
      {E : C} {e : y + z ~> E}
      (Eq : IsCoequalizer (inl ∘ f) (inr ∘ g) E e) :
  @IsPullback (C^op) y z x f g E (e ∘ inl) (e ∘ inr).
Proof.
  exact (@pullback_of_equalizer (C^op) O y z x f g E e
           (IsEqualizer_op_of_IsCoequalizer Eq)).
Qed.

(* Read through the covariant accessors of Structure/Pushout.v.  The apex
   and both injections compute: no transport, no [≈]-step. *)
Definition IsPushout_of_coequalizer {x y z : C} (f : x ~> y) (g : x ~> z)
      {E : C} {e : y + z ~> E}
      (Eq : IsCoequalizer (inl ∘ f) (inr ∘ g) E e) : IsPushout f g :=
  is_pullback_pullback (pushout_of_coequalizer f g Eq).

Example IsPushout_of_coequalizer_apex {x y z : C} (f : x ~> y) (g : x ~> z)
      {E : C} {e : y + z ~> E}
      (Eq : IsCoequalizer (inl ∘ f) (inr ∘ g) E e) :
  pushout_apex (IsPushout_of_coequalizer f g Eq) = E := eq_refl.

Example IsPushout_of_coequalizer_in1 {x y z : C} (f : x ~> y) (g : x ~> z)
      {E : C} {e : y + z ~> E}
      (Eq : IsCoequalizer (inl ∘ f) (inr ∘ g) E e) :
  pushout_in1 (IsPushout_of_coequalizer f g Eq) = e ∘ inl := eq_refl.

Example IsPushout_of_coequalizer_in2 {x y z : C} (f : x ~> y) (g : x ~> z)
      {E : C} {e : y + z ~> E}
      (Eq : IsCoequalizer (inl ∘ f) (inr ∘ g) E e) :
  pushout_in2 (IsPushout_of_coequalizer f g Eq) = e ∘ inr := eq_refl.

End PushoutFromCoequalizer.

Definition HasPushouts_of_Cocartesian_HasCoequalizers {C : Category}
           `{O : @Cocartesian C} (E : @HasCoequalizers C) : @HasPushouts C :=
  HasPushouts_of_HasPullbacks_op
    (@HasPullbacks_of_Cartesian_HasEqualizers (C^op) O
       (HasEqualizers_op_of_HasCoequalizers E)).

(* ====================================================================== *)
(** * Measured negatives

    Every strengthening attempted and refused, recorded as a [Fail] so a
    later change to a donor breaks this file loudly rather than silently
    invalidating a prose claim.  The two KINDS are kept apart, and the
    split is measured rather than guessed: negatives 2 and 3 are
    FORMABILITY failures -- the two legs do not live in a common hom-set,
    so the equation cannot be stated -- while negatives 1, 4, 5, 6 and 7
    are CONVERSION failures, where both sides are well typed and [eq_refl]
    is refused.  Positive controls sit beside them.

    These are measurements made in this file, not a substitute for a
    guarded probe file with an instrument check. *)

Section Negatives.

Context {C : Category}.
Context `{@Cartesian C}.
Context {x y : C}.
Context (f g : x ~> y).

(* 1. The two cospans of section (D) do not share a codomain. *)
Fail Example neg_ml_aw_codomain :
  (x × y)%object = (y × y)%object := eq_refl.

(* positive control: the degenerate instantiation y := x does. *)
Example pos_ml_aw_codomain_degenerate :
  (x × x)%object = (x × x)%object := eq_refl.

(* 2, 3. Nor are the legs parallel: these are ill-typed, not merely
   inconvertible. *)
Fail Example neg_ml_left_is_aw_pair :
  @ml_left C _ x y f = @aw_pair C _ x y f g := eq_refl.

Fail Example neg_ml_right_is_aw_diag :
  @ml_right C _ x y g = @aw_diag C _ y := eq_refl.

(* positive control: at f := id the legs DO coincide, up to swapping the
   two sides of the cospan -- this is [maclane_awodey_degenerate_*]. *)
Example pos_ml_aw_degenerate :
  @ml_left C _ x x id = @aw_diag C _ x := eq_refl.

(* 4. The (A)/(B) round trip on the equalizing map is [≈], not [=]. *)
Fail Example neg_equalizer_pullback_round {E : C} (e : E ~> x × y) :
  (exl ∘ e) △ (exr ∘ e) = e := eq_refl.

(* 5. Nor is the reverse composite strict on the projections. *)
Fail Example neg_pullback_equalizer_round {P : C}
     (p1 : P ~> x) (p2 : P ~> y) : exl ∘ (p1 △ p2) = p1 := eq_refl.

(* positive control for 4 and 5: both hold at [≈]. *)
Example pos_rounds_up_to_equiv {E : C} (e : E ~> x × y) :
  (exl ∘ e) △ (exr ∘ e) ≈ e := equalizer_pullback_round E e.

End Negatives.

Section NegativesDuality.

Context {C : Category}.

(* 6, 7. The duality of section (F) is NOT definitional: [IsCoequalizer]
   and [IsEqualizer] are distinct record types, so neither the predicates
   nor the classes are related by [eq_refl], however convertible their
   fields are. *)
Fail Example neg_HasCoequalizers_is_op :
  HasCoequalizers C = HasEqualizers (C^op) := eq_refl.

Fail Example neg_IsCoequalizer_is_op {x y : C} (f g : x ~> y)
     (q : C) (e : y ~> q) :
  IsCoequalizer f g q e = @IsEqualizer (C^op) y x f g q e := eq_refl.

(* positive control: the FIELD types are convertible, which is exactly
   why the bridge below needs no tactic. *)
Example pos_cofork_is_fork_eq {x y : C} (f g : x ~> y)
        (q : C) (e : y ~> q) (Hyp : e ∘ f ≈ e ∘ g) :
  f ∘[C^op] e ≈ g ∘[C^op] e := Hyp.

End NegativesDuality.
