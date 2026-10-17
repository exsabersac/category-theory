Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.SubobjectClassifier.Natural.
Require Import Category.Structure.Topos.
Require Import Category.Structure.Topos.Power.
Require Import Category.Functor.Hom.Internal.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.Crude.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* See the note in Structure/Topos/Power.v: [Category.Functor.Opposite]
   opens [functor_scope], so [category_scope] is reopened here. *)
Open Scope category_scope.

(*
   nLab:      https://ncatlab.org/nlab/show/Pare%27s+theorem
   nLab:      https://ncatlab.org/nlab/show/monadicity+theorem
   Wikipedia: https://en.wikipedia.org/wiki/Beck%27s_monadicity_theorem
   Paper:     Paré, "Colimits in topoi", Bulletin of the American

   本文件给出 topos 结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ToposMonadic.

Context {C : Category}.
Context `{H : @ElementaryTopos C}.

#[local] Set Default Proof Using "All".

(* 相关说明。 （已译） *)

(*
   本节说明（余）极限、拉回/推出、等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition topos_HasEqualizers : @HasEqualizers C :=
  HasEqualizers_of_HasPullbacks_Terminal topos_pullbacks.

(*
   本节说明（余）极限、拉回/推出、等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition topos_finitely_complete :
  @Terminal C * @Cartesian C * @HasPullbacks C * @HasEqualizers C :=
  (topos_terminal, topos_cartesian, topos_pullbacks, topos_HasEqualizers).

(*
   本节说明等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition op_HasCoequalizers : @HasCoequalizers (C^op) :=
  @HasCoequalizers_of_HasEqualizers_op (C^op) topos_HasEqualizers.

Definition op_HasReflexiveCoequalizers : HasReflexiveCoequalizers (C^op) :=
  @HasCoequalizers_HasReflexiveCoequalizers (C^op) op_HasCoequalizers.

(*
   本节说明伴随、单子、topos相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition pow_monad : @Monad C (PowF ◯ Opposite_Functor PowF) :=
  @Adjunction_Induced_Monad (C^op) C (Opposite_Functor PowF) PowF
    pow_adjunction.

(* 相关说明。 （已译） *)

(* A topos balanced. The classifying square MONIC epi forces its
 characteristic map down [truth ∘ one], after 恒等
 lies over truth factors through f. （已译） *)
Theorem topos_balanced {x y : C} (f : x ~> y) (Mf : Monic f) (Ef : Epic f) :
  IsIsomorphism f.
Proof.
  pose proof (char_pullback f Mf) as PB.
  assert (Hc : char f Mf ≈ truth ∘ one).
  { apply (epic (Epic := Ef)).
    rewrite (is_pullback_commutes PB).
    rewrite <- comp_assoc.
    now rewrite (one_unique (one ∘ f) one). }
  destruct (is_pullback_ump PB y id one) as [u [Hu1 Hu2] Huniq].
  { rewrite id_right, Hc; reflexivity. }
  unshelve refine {| two_sided_inverse := u |}.
  - exact Hu1.
  - apply (monic (Monic := Mf)).
    rewrite comp_assoc, Hu1, id_left, id_right.
    reflexivity.
Qed.

Definition topos_diag (x : C) : x ~> x × x := id △ id.

Lemma diag_Monic (x : C) : Monic (topos_diag x).
Proof.
  apply sections_are_monic.
  unshelve refine {| section := exl |}.
  unfold topos_diag; cat.
Qed.

(* 相关说明。 （已译） *)
Definition sing (x : C) : x ~> Pow x :=
  curry (char (topos_diag x) (diag_Monic x)).

Lemma sing_Monic (x : C) : Monic (sing x).
Proof.
  constructor; intros z u v Huv.
  pose proof (char_pullback (topos_diag x) (diag_Monic x)) as PB.
  assert (Hun : char (topos_diag x) (diag_Monic x) ∘ first u
                ≈ char (topos_diag x) (diag_Monic x) ∘ first v).
  { unfold sing in Huv.
    apply curry_inj.
    rewrite <- !curry_comp_l.
    exact Huv. }
  assert (Hq : char (topos_diag x) (diag_Monic x) ∘ (v △ u) ≈ truth ∘ one).
  { transitivity (char (topos_diag x) (diag_Monic x) ∘ (u △ u)).
    - rewrite <- (id_right (v △ u)).
      transitivity ((char (topos_diag x) (diag_Monic x) ∘ first v)
                      ∘ (id △ u)).
      + rewrite <- comp_assoc.
        apply compose_respects; [reflexivity|].
        unfold first; unfork.
      + rewrite <- Hun, <- comp_assoc.
        apply compose_respects; [reflexivity|].
        unfold first; unfork.
    - transitivity (char (topos_diag x) (diag_Monic x)
                      ∘ (topos_diag x ∘ u)).
      + apply compose_respects; [reflexivity|].
        unfold topos_diag; unfork.
      + rewrite comp_assoc, (is_pullback_commutes PB), <- comp_assoc.
        now rewrite (one_unique (one ∘ u) one). }
  destruct (is_pullback_ump PB z (v △ u) one Hq) as [w [Hw1 _] _].
  transitivity w.
  - rewrite <- (exr_fork v u), <- Hw1.
    unfold topos_diag; unfork.
  - rewrite <- (exl_fork v u), <- Hw1.
    unfold topos_diag; unfork.
Qed.

(* The diagonal SYMMETRIC 关系, so characteristic map is
 invariant under [swap]; hence singleton own [flip]. （已译） *)
Lemma char_diag_swap (x : C) :
  char (topos_diag x) (diag_Monic x) ∘ swap
    ≈ char (topos_diag x) (diag_Monic x).
Proof.
  apply char_unique.
  pose proof (char_pullback (topos_diag x) (diag_Monic x)) as PB.
  assert (Hsd : swap ∘ topos_diag x ≈ topos_diag x)
    by (unfold topos_diag; unfork).
  constructor.
  - rewrite <- comp_assoc, Hsd.
    exact (is_pullback_commutes PB).
  - intros Q q1 q2 Hq.
    destruct (is_pullback_ump PB Q (swap ∘ q1) q2) as [w [Hw1 Hw2] Hwu].
    { rewrite comp_assoc; exact Hq. }
    unshelve refine {| unique_obj := w |}.
    + split; [| exact Hw2].
      rewrite <- (id_left q1), <- swap_invol, <- comp_assoc, <- Hw1.
      rewrite comp_assoc, Hsd; reflexivity.
    + intros v [Hv1 Hv2].
      apply Hwu; split; [| exact Hv2].
      rewrite <- Hv1, comp_assoc, Hsd; reflexivity.
Qed.

Lemma flip_sing (x : C) : flip (sing x) ≈ sing x.
Proof.
  unfold flip, sing.
  rewrite uncurry_curry.
  now rewrite char_diag_swap.
Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance PowF_Faithful : Faithful PowF.
Proof.
  constructor; intros a0 b0 f g Hfg.
  apply (monic (Monic := sing_Monic a0)).
  assert (Ef : sing a0 ∘ f ≈ flip (fmap[PowF] f ∘ sing a0))
    by (rewrite flip_pow_comp, flip_sing; reflexivity).
  assert (Eg : sing a0 ∘ g ≈ flip (fmap[PowF] g ∘ sing a0))
    by (rewrite flip_pow_comp, flip_sing; reflexivity).
  rewrite Ef, Eg.
  unfold flip.
  now rewrite Hfg.
Defined.

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition IsIso_of_op {a b : C} (h : b ~> a)
  (I : @IsIsomorphism (C^op) a b h) : @IsIsomorphism C b a h :=
  @Build_IsIsomorphism C b a h
    (@two_sided_inverse (C^op) a b h I)
    (@is_left_inverse (C^op) a b h I)
    (@is_right_inverse (C^op) a b h I).

Definition op_IsIso_of {a b : C} (h : b ~> a)
  (I : @IsIsomorphism C b a h) : @IsIsomorphism (C^op) a b h :=
  @Build_IsIsomorphism (C^op) a b h
    (@two_sided_inverse C b a h I)
    (@is_left_inverse C b a h I)
    (@is_right_inverse C b a h I).

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance PowF_ReflectsIsos : ReflectsIsos PowF.
Proof.
  constructor; intros a0 b0 f Hiso.
  pose proof (iso_to_monic (IsIsoToIso _ Hiso)) as Mi.
  pose proof (iso_to_epic  (IsIsoToIso _ Hiso)) as Ei.
  simpl in Mi, Ei.
  pose proof (faithful_reflects_monic PowF f Mi) as Mf.
  pose proof (faithful_reflects_epic  PowF f Ei) as Ef.
  apply op_IsIso_of.
  apply topos_balanced.
  - exact (@Monic_of_op_Epic C b0 a0 f Ef).
  - exact (@Epic_of_op_Monic C b0 a0 f Mf).
Qed.

(* 相关说明。 （已译） *)

(* [second] of a mono is a mono: read both components off the product. *)
Lemma second_Monic {u x z : C} (m : u ~> x) (M : Monic m) :
  Monic (@second C _ u x z m).
Proof.
  constructor; intros w p q Hpq.
  assert (H1 : exl ∘ p ≈ exl ∘ q).
  { rewrite <- (exl_second (z:=z) m), <- !comp_assoc, Hpq; reflexivity. }
  assert (H2 : exr ∘ p ≈ exr ∘ q).
  { apply (monic (Monic := M)).
    rewrite !comp_assoc, <- !(exr_second m), <- !comp_assoc, Hpq;
      reflexivity. }
  rewrite <- (id_left p), <- (id_left q), <- fork_exl_exr,
          <- !fork_comp, H1, H2; reflexivity.
Qed.

(* 相关说明。 （已译） *)
Definition sub_push {x y : C} (n : y ~> x) (N : Monic n) (s : SubObj y)
  : SubObj x :=
  {| sub_dom := sub_dom s
   ; sub_mono := n ∘ sub_mono s
   ; sub_is_monic := monic_compose N (sub_is_monic s) |}.

Lemma sub_push_respects {x y : C} (n : y ~> x) (N : Monic n)
      (s s' : SubObj y) (Hs : s ≈ s') :
  sub_push n N s ≈ sub_push n N s'.
Proof.
  destruct Hs as [i Hi].
  exists i; simpl.
  rewrite <- comp_assoc.
  now rewrite Hi.
Qed.

(* Reindexing a pushed subobject along the same mono returns it. *)
Lemma sub_reindex_push {x y : C} (n : y ~> x) (N : Monic n) (s : SubObj y) :
  sub_reindex n (sub_push n N s) ≈ s.
Proof.
  apply (sub_reindex_transport n (sub_push n N s) s id).
  constructor.
  - simpl; cat.
  - simpl; intros Q q1 q2 Hq.
    unshelve refine {| unique_obj := q2 |}.
    + split; [| cat].
      apply (monic (Monic := N)).
      rewrite Hq, comp_assoc; reflexivity.
    + intros w [Hw1 Hw2]; simpl in *.
      now rewrite <- Hw2; cat.
Qed.

(* 相关说明。 （已译） *)
Definition pow_mem (x : C) : SubObj (Pow x × x) :=
  sub_reindex eval truth_subobject.

Lemma char_mem (x : C) : char_sub (pow_mem x) ≈ eval.
Proof. exact (classifier_char_roundtrip eval). Qed.

(* 相关说明。 （已译） *)
Lemma char_sub_inj {x : C} (s s' : SubObj x) :
  char_sub s ≈ char_sub s' → s ≈ s'.
Proof.
  intros Hc.
  transitivity (sub_reindex (char_sub s) truth_subobject).
  - symmetry; apply classifier_pullback_roundtrip.
  - transitivity (sub_reindex (char_sub s') truth_subobject).
    + apply sub_reindex_respects_mor; exact Hc.
    + apply classifier_pullback_roundtrip.
Qed.

(* Evaluation intertwines P-image m left m the
 right: substitution law membership 关系. （已译） *)
Lemma eval_pow_square {u x : C} (m : u ~> x) :
  eval ∘ first (fmap[PowF] m) ≈ eval ∘ second m.
Proof.
  rewrite eval_first.
  simpl.
  rewrite uncurry_curry, id_left.
  reflexivity.
Qed.

(* The same square one level up, on membership subobjects. *)
Lemma mem_pow_square {u x : C} (m : u ~> x) :
  sub_reindex (first (fmap[PowF] m)) (pow_mem u)
    ≈ sub_reindex (second m) (pow_mem x).
Proof.
  apply char_sub_inj.
  rewrite !char_reindex, !char_mem.
  apply eval_pow_square.
Qed.

(* THE DIRECT IMAGE along mono m: classify pushed membership
 关系 transpose. （已译） *)
Definition ex_mono {u x : C} (m : u ~> x) (M : Monic m) : Pow u ~> Pow x :=
  curry (char_sub (sub_push (second m) (second_Monic m M) (pow_mem u))).

(* 相关说明。 （已译） *)
Theorem pow_ex_mono {u x : C} (m : u ~> x) (M : Monic m) :
  fmap[PowF] m ∘ ex_mono m M ≈ id.
Proof.
  unfold ex_mono.
  rewrite pow_precompose.
  rewrite <- char_reindex.
  rewrite (char_sub_respects _ _
             (sub_reindex_push (second m) (second_Monic m M) (pow_mem u))).
  rewrite char_mem.
  apply curry_eval.
Qed.

(* 相关说明。 （已译） *)

Lemma IsPullback_sym {x y z : C} {f : x ~> z} {g : y ~> z}
      {P : C} {p1 : P ~> x} {p2 : P ~> y} :
  IsPullback f g P p1 p2 → IsPullback g f P p2 p1.
Proof.
  intros HP; constructor.
  - symmetry; exact (is_pullback_commutes HP).
  - intros Q q1 q2 Hq.
    destruct (is_pullback_ump HP Q q2 q1 (symmetry Hq)) as [u [U1 U2] Uu].
    unshelve refine {| unique_obj := u |}.
    + split; assumption.
    + intros v [V1 V2]; apply Uu; split; assumption.
Qed.

(* A pullback square multiplied on the left by a fixed object stays a
   pullback. *)
Lemma second_pullback {b a k : C} {f g : b ~> a} {p1 p2 : k ~> b}
      (HP : IsPullback f g k p1 p2) (z : C) :
  IsPullback (@second C _ b a z f) (@second C _ b a z g)
             (z × k) (second p1) (second p2).
Proof.
  constructor.
  - rewrite <- !second_comp.
    now rewrite (is_pullback_commutes HP).
  - intros Q q1 q2 Hq.
    assert (Hl : exl ∘ q1 ≈ exl ∘ q2).
    { transitivity (exl ∘ (second f ∘ q1)).
      - rewrite comp_assoc, exl_second; reflexivity.
      - rewrite Hq, comp_assoc, exl_second; reflexivity. }
    assert (Hr : f ∘ (exr ∘ q1) ≈ g ∘ (exr ∘ q2)).
    { transitivity (exr ∘ (second f ∘ q1)).
      - rewrite !comp_assoc, exr_second; reflexivity.
      - rewrite Hq, !comp_assoc, exr_second; reflexivity. }
    destruct (is_pullback_ump HP Q (exr ∘ q1) (exr ∘ q2) Hr)
      as [v [V1 V2] Vu].
    unshelve refine {| unique_obj := (exl ∘ q1) △ v |}.
    + split; unfold second.
      * rewrite <- fork_comp; cat.
        rewrite <- comp_assoc; cat.
        rewrite V1.
        rewrite <- (id_left q1) at 3.
        now rewrite <- fork_exl_exr, <- fork_comp.
      * rewrite <- fork_comp; cat.
        rewrite <- comp_assoc; cat.
        rewrite V2, Hl.
        rewrite <- (id_left q2) at 3.
        now rewrite <- fork_exl_exr, <- fork_comp.
    + intros w [W1 W2].
      assert (Ew : exr ∘ w ≈ v).
      { symmetry; apply Vu; split.
        - rewrite <- W1, !comp_assoc, exr_second; reflexivity.
        - rewrite <- W2, !comp_assoc, exr_second; reflexivity. }
      assert (El : exl ∘ w ≈ exl ∘ q1).
      { rewrite <- W1, !comp_assoc, exl_second; reflexivity. }
      rewrite <- (id_left w), <- fork_exl_exr, <- fork_comp, El, Ew.
      reflexivity.
Qed.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma first_second_pullback {z w u x : C} (phi : z ~> w) (m : u ~> x) :
  IsPullback (@first C _ z w x phi) (@second C _ u x w m)
             (z × u) (@second C _ u x z m) (@first C _ z w u phi).
Proof.
  constructor.
  - unfold first, second; unfork.
  - intros Q q1 q2 Hq.
    assert (Hl : phi ∘ (exl ∘ q1) ≈ exl ∘ q2).
    { transitivity (exl ∘ (first phi ∘ q1)).
      - rewrite !comp_assoc, exl_first; reflexivity.
      - rewrite Hq, comp_assoc, exl_second; reflexivity. }
    assert (Hr : exr ∘ q1 ≈ m ∘ (exr ∘ q2)).
    { transitivity (exr ∘ (first phi ∘ q1)).
      - rewrite comp_assoc, exr_first; reflexivity.
      - rewrite Hq, !comp_assoc, exr_second; reflexivity. }
    unshelve refine {| unique_obj := (exl ∘ q1) △ (exr ∘ q2) |}.
    + split.
      * unfold second.
        rewrite <- fork_comp; cat.
        rewrite <- comp_assoc; cat.
        rewrite <- Hr.
        rewrite <- (id_left q1) at 3.
        now rewrite <- fork_exl_exr, <- fork_comp.
      * unfold first.
        rewrite <- fork_comp; cat.
        rewrite <- comp_assoc; cat.
        rewrite Hl.
        rewrite <- (id_left q2) at 3.
        now rewrite <- fork_exl_exr, <- fork_comp.
    + intros v [V1 V2].
      assert (El : exl ∘ v ≈ exl ∘ q1).
      { rewrite <- V1, comp_assoc, exl_second; reflexivity. }
      assert (Er : exr ∘ v ≈ exr ∘ q2).
      { rewrite <- V2, comp_assoc, exr_first; reflexivity. }
      rewrite <- (id_left v), <- fork_exl_exr, <- fork_comp, El, Er.
      reflexivity.
Qed.

(*
   本节说明拉回/推出、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma bc_mono {X Y Z K : C} {F : X ~> Z} {G : Y ~> Z}
      {p1 : K ~> X} {p2 : K ~> Y}
      (HP : IsPullback F G K p1 p2) (MF : Monic F) (M2 : Monic p2)
      (R : SubObj X) :
  sub_reindex G (sub_push F MF R) ≈ sub_push p2 M2 (sub_reindex p1 R).
Proof.
  apply (sub_reindex_transport G (sub_push F MF R)
           (sub_push p2 M2 (sub_reindex p1 R))
           (pullback_snd p1 (sub_mono R) (pullback p1 (sub_mono R)))).
  apply IsPullback_sym.
  exact (pullback_paste HP
           (IsPullback_sym
              (pullback_is_pullback p1 (sub_mono R)
                 (pullback p1 (sub_mono R))))).
Qed.

(*
   本节说明拉回/推出、等化子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma coreflexive_equalizer_pullback {a b k : C} {f g : b ~> a}
      {r : a ~> b} (Hf : r ∘ f ≈ id) (Hg : r ∘ g ≈ id)
      {e : k ~> b} (HE : IsEqualizer f g k e) :
  IsPullback f g k e e.
Proof.
  constructor.
  - exact (fork_eq HE).
  - intros Q q1 q2 Hq.
    assert (Hq12 : q1 ≈ q2).
    { rewrite <- (id_left q1), <- Hf, <- comp_assoc, Hq,
              comp_assoc, Hg, id_left; reflexivity. }
    assert (Hfork : f ∘ q1 ≈ g ∘ q1).
    { rewrite Hq, Hq12; reflexivity. }
    destruct (eq_desc HE q1 Hfork) as [u Hu Huniq].
    unshelve refine {| unique_obj := u |}.
    + split.
      * exact Hu.
      * rewrite Hu; exact Hq12.
    + intros v [V1 V2]; apply Huniq; exact V1.
Qed.

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem pow_bc {a b k : C} {f g : b ~> a} {e : k ~> b}
      (Mf : Monic f) (Me : Monic e) (HP : IsPullback f g k e e) :
  fmap[PowF] g ∘ ex_mono f Mf ≈ ex_mono e Me ∘ fmap[PowF] e.
Proof.
  unfold ex_mono.
  rewrite pow_precompose.
  transitivity (curry (char_sub (sub_push (second e) (second_Monic e Me)
                                   (pow_mem k)) ∘ first (fmap[PowF] e))).
  - apply curry_respects.
    rewrite <- !char_reindex.
    apply char_sub_respects.
    transitivity (sub_push (second e) (second_Monic e Me)
                    (sub_reindex (second e) (pow_mem b))).
    + exact (bc_mono (second_pullback HP (Pow b))
               (second_Monic f Mf) (second_Monic e Me) (pow_mem b)).
    + transitivity (sub_push (second e) (second_Monic e Me)
                      (sub_reindex (first (fmap[PowF] e)) (pow_mem k))).
      * apply sub_push_respects.
        symmetry.
        apply mem_pow_square.
      * symmetry.
        exact (bc_mono
                 (IsPullback_sym (first_second_pullback (fmap[PowF] e) e))
                 (second_Monic e Me) (second_Monic e Me) (pow_mem k)).
  - symmetry.
    apply curry_comp_l.
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma pow_fmap_comp {a b k : C} (f : b ~> a) (e : k ~> b) :
  fmap[PowF] e ∘ fmap[PowF] f ≈ fmap[PowF] (f ∘ e).
Proof. symmetry; exact (@fmap_comp (C^op) C PowF a b k e f). Qed.

(*
   本节说明函子、拉回/推出、等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition pow_split_coequalizer
  {a b k : C} {f g : b ~> a} {r : a ~> b}
  (Hf : r ∘ f ≈ id) (Hg : r ∘ g ≈ id)
  {e : k ~> b} (HE : IsEqualizer f g k e) :
  SplitCoequalizer (fmap[PowF] f) (fmap[PowF] g).
Proof.
  unshelve refine {| scoeq_obj := Pow k
                   ; scoeq_e   := fmap[PowF] e
                   ; scoeq_s   := ex_mono e (equalizer_monic f g HE)
                   ; scoeq_t   := ex_mono f (@sections_are_monic C b a f
                                    {| section := r
                                     ; section_comp := Hf |}) |}.
  - (* law1: P e coforks the image pair *)
    rewrite !pow_fmap_comp.
    now rewrite (fork_eq HE).
  - (* law2: ∃_e splits P e *)
    apply pow_ex_mono.
  - (* law3: ∃_f splits P f *)
    apply pow_ex_mono.
  - (* law4: Beck-Chevalley *)
    apply (pow_bc _ _ (coreflexive_equalizer_pullback Hf Hg HE)).
Defined.

(*
   本节说明单子、等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition pow_PreservesReflexiveCoequalizers :
  PreservesReflexiveCoequalizers PowF :=
  fun a b f g RP k e HC =>
    split_coequalizer_is_coequalizer _ _
      (pow_split_coequalizer (refl_section_f RP) (refl_section_g RP)
         (@IsEqualizer_op_of_IsCoequalizer (C^op) a b f g k e HC)).

(* The 等价 C^op ≃ EM(P ◯ P^op), CONSUMED Crude.v. （已译） *)
Definition pow_equivalence :
  EquivalenceOfCategories (EM_Comparison pow_adjunction) :=
  crude_monadicity pow_adjunction op_HasReflexiveCoequalizers
    pow_PreservesReflexiveCoequalizers PowF_ReflectsIsos.

(* PARÉ'S THEOREM: the power-object functor is monadic. *)
Definition power_object_monadic : Monadic PowF :=
  (Opposite_Functor PowF; (pow_adjunction; pow_equivalence)).

End ToposMonadic.
