Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.
Require Import Category.Construction.Comma.Diagram.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Parallel.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Theory.Morphisms.CokernelPair.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* * * The cokernel pair 左伴随 equalizer （已译） *)

(*
   nLab:      https://ncatlab.org/nlab/show/equalizer
   nLab:      https://ncatlab.org/nlab/show/regular+monomorphism
   nLab:      https://ncatlab.org/nlab/show/arrow+category
   Wikipedia: https://en.wikipedia.org/wiki/Equaliser_(mathematics)

   本文件给出余核对相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** Reading two endpoint 范畴 （已译） *)

Section Endpoints.

Context {C : Category}.

(*
   本节说明 CokernelPair 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition ar_dom (A : @Arrow C) : C := fst (`1 A).
Definition ar_cod (A : @Arrow C) : C := snd (`1 A).
Definition ar_mor (A : @Arrow C) : ar_dom A ~> ar_cod A := `2 A.

Definition ar_fst {A B : @Arrow C} (u : A ~> B) : ar_dom A ~> ar_dom B :=
  fst (`1 u).
Definition ar_snd {A B : @Arrow C} (u : A ~> B) : ar_cod A ~> ar_cod B :=
  snd (`1 u).

Lemma ar_square {A B : @Arrow C} (u : A ~> B) :
  ar_mor B ∘ ar_fst u ≈ ar_snd u ∘ ar_mor A.
Proof. exact (`2 u). Qed.

(* The two legs parallel pair 函子 out [Parallel] names. （已译） *)

Definition parallel_leg1 (G : Parallel ⟶ C) : G ParX ~> G ParY :=
  fmap[G] (true; ParOne).
Definition parallel_leg2 (G : Parallel ⟶ C) : G ParX ~> G ParY :=
  fmap[G] (false; ParTwo).

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma par_hom_id_X (k : ParX ~{Parallel}~> ParX) : k ≈ id.
Proof.
  destruct k as [[|] k]; simpl.
  - reflexivity.
  - destruct (ParHom_Id_false_absurd _ k).
Qed.

Lemma par_hom_id_Y (k : ParY ~{Parallel}~> ParY) : k ≈ id.
Proof.
  destruct k as [[|] k]; simpl.
  - reflexivity.
  - destruct (ParHom_Id_false_absurd _ k).
Qed.

Lemma par_fmap_idX (G : Parallel ⟶ C) (k : ParX ~{Parallel}~> ParX) :
  fmap[G] k ≈ id.
Proof. rewrite (par_hom_id_X k); apply fmap_id. Qed.

Lemma par_fmap_idY (G : Parallel ⟶ C) (k : ParY ~{Parallel}~> ParY) :
  fmap[G] k ≈ id.
Proof. rewrite (par_hom_id_Y k); apply fmap_id. Qed.

End Endpoints.

(** ** The cokernel-pair functor *)

Section CokernelPairFunctor.

Context {C : Category}.
Context `{HP : @HasPushouts C}.

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition ckp_of (A : @Arrow C) : IsPushout (ar_mor A) (ar_mor A) :=
  cokernel_pair (ar_mor A).

Definition ckp_u (A : @Arrow C) : ar_cod A ~> ckp_obj (ckp_of A) :=
  ckp_left (ckp_of A).
Definition ckp_v (A : @Arrow C) : ar_cod A ~> ckp_obj (ckp_of A) :=
  ckp_right (ckp_of A).

Definition ckp_pair (A : @Arrow C) : Parallel ⟶ C :=
  APair (ckp_u A) (ckp_v A).

Lemma ckp_uv_commutes (A : @Arrow C) :
  ckp_u A ∘ ar_mor A ≈ ckp_v A ∘ ar_mor A.
Proof. exact (ckp_commutes (ckp_of A)). Qed.

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma ckp_fmap_cocone {A B : @Arrow C} (u : A ~> B) :
  (ckp_u B ∘ ar_snd u) ∘ ar_mor A ≈ (ckp_v B ∘ ar_snd u) ∘ ar_mor A.
Proof.
  rewrite <- !comp_assoc.
  rewrite <- !(ar_square u).
  rewrite !comp_assoc.
  now rewrite (ckp_commutes (ckp_of B)).
Qed.

Definition ckp_fmap_Y {A B : @Arrow C} (u : A ~> B)
  : ckp_obj (ckp_of A) ~> ckp_obj (ckp_of B) :=
  ckp_med (ckp_of A) (ckp_fmap_cocone u).

Lemma ckp_fmap_Y_left {A B : @Arrow C} (u : A ~> B) :
  ckp_fmap_Y u ∘ ckp_u A ≈ ckp_u B ∘ ar_snd u.
Proof. exact (ckp_med_left (ckp_of A) (ckp_fmap_cocone u)). Qed.

Lemma ckp_fmap_Y_right {A B : @Arrow C} (u : A ~> B) :
  ckp_fmap_Y u ∘ ckp_v A ≈ ckp_v B ∘ ar_snd u.
Proof. exact (ckp_med_right (ckp_of A) (ckp_fmap_cocone u)). Qed.

Lemma ckp_fmap_Y_unique {A B : @Arrow C} (u : A ~> B)
      (w : ckp_obj (ckp_of A) ~> ckp_obj (ckp_of B)) :
  w ∘ ckp_u A ≈ ckp_u B ∘ ar_snd u ->
  w ∘ ckp_v A ≈ ckp_v B ∘ ar_snd u -> ckp_fmap_Y u ≈ w.
Proof. exact (ckp_med_unique (ckp_of A) (ckp_fmap_cocone u) w). Qed.

Definition ckp_comp {A B : @Arrow C} (u : A ~> B) (z : ParObj)
  : fobj[ckp_pair A] z ~> fobj[ckp_pair B] z :=
  match z with
  | ParX => ar_snd u
  | ParY => ckp_fmap_Y u
  end.

(*
   本节说明 CokernelPair 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma ckp_natural {A B : @Arrow C} (u : A ~> B) (z w : ParObj)
      (k : z ~{Parallel}~> w) :
  fmap[ckp_pair B] k ∘ ckp_comp u z ≈ ckp_comp u w ∘ fmap[ckp_pair A] k.
Proof.
  destruct z, w; simpl.
  - now rewrite id_left, id_right.
  - destruct k as [[|] k]; simpl.
    + now rewrite ckp_fmap_Y_left.
    + now rewrite ckp_fmap_Y_right.
  - destruct (ParHom_Y_X_absurd _ (projT2 k)).
  - now rewrite id_left, id_right.
Qed.

Definition ckp_transform {A B : @Arrow C} (u : A ~> B)
  : ckp_pair A ⟹ ckp_pair B :=
  @Build_Transform' Parallel C (ckp_pair A) (ckp_pair B)
                    (ckp_comp u) (@ckp_natural A B u).

#[local] Obligation Tactic := idtac.

(* All three obligations are proved, none defaulted: [fmap_respects],
   [fmap_id] and [fmap_comp] each reduce at [ParX] to a component
   equation and at [ParY] to one appeal to [ckp_fmap_Y_unique].（标题）（已译） *)

Program Definition CokernelPairFunctor : @Arrow C ⟶ [Parallel, C] := {|
  fobj := ckp_pair ;
  fmap := fun A B u => ckp_transform u
|}.
Next Obligation.
  intros A B u v [Hd Hc] z; destruct z; simpl.
  - exact Hc.
  - apply ckp_fmap_Y_unique.
    + now rewrite ckp_fmap_Y_left, Hc.
    + now rewrite ckp_fmap_Y_right, Hc.
Qed.
Next Obligation.
  intros A z; destruct z; simpl.
  - reflexivity.
  - apply ckp_fmap_Y_unique; now rewrite id_left, id_right.
Qed.
Next Obligation.
  intros A B D u v z; destruct z; simpl.
  - reflexivity.
  - apply ckp_fmap_Y_unique.
    + unfold ar_snd; simpl.
      rewrite <- comp_assoc.
      rewrite ckp_fmap_Y_left.
      rewrite comp_assoc.
      rewrite ckp_fmap_Y_left.
      unfold ar_snd; simpl.
      now rewrite <- comp_assoc.
    + unfold ar_snd; simpl.
      rewrite <- comp_assoc.
      rewrite ckp_fmap_Y_right.
      rewrite comp_assoc.
      rewrite ckp_fmap_Y_right.
      unfold ar_snd; simpl.
      now rewrite <- comp_assoc.
Qed.

End CokernelPairFunctor.

(* * ** The equalizer 函子 进入 arrow 范畴 （已译） *)

Section EqualizerArrowFunctor.

Context {C : Category}.
Context `{HE : @HasEqualizers C}.

(* The chosen equalizer parallel pair 函子 names, unpacked
 [HasEqualizers]' sigma. （已译） *)

Definition eqa_data (G : Parallel ⟶ C) :=
  equalizer (parallel_leg1 G) (parallel_leg2 G).

Definition eqa_obj (G : Parallel ⟶ C) : C := `1 (eqa_data G).
Definition eqa_arr (G : Parallel ⟶ C) : eqa_obj G ~> G ParX :=
  `1 (`2 (eqa_data G)).
Definition eqa_wit (G : Parallel ⟶ C)
  : IsEqualizer (parallel_leg1 G) (parallel_leg2 G) (eqa_obj G) (eqa_arr G)
  := `2 (`2 (eqa_data G)).

(* The equalizing arrow, read 对象 arrow 范畴. （已译） *)

Definition eqa_ob (G : Parallel ⟶ C) : @Arrow C :=
  ((eqa_obj G, fobj[G] ParX); eqa_arr G).

Example eqa_ob_dom (G : Parallel ⟶ C) : ar_dom (eqa_ob G) = eqa_obj G
  := eq_refl.
Example eqa_ob_cod (G : Parallel ⟶ C) : ar_cod (eqa_ob G) = fobj[G] ParX
  := eq_refl.
Example eqa_ob_mor (G : Parallel ⟶ C) : ar_mor (eqa_ob G) = eqa_arr G
  := eq_refl.

(* The comma square 态射 [eqa_ob G], read [eqa_arr G]
 place [ar_mor (eqa_ob G)]. The two same term, so this
 [ar_square] accepted conversion. （已译） *)
Lemma ar_square_eqa {A : @Arrow C} {G : Parallel ⟶ C}
      (w : A ~{@Arrow C}~> eqa_ob G) :
  eqa_arr G ∘ ar_fst w ≈ ar_snd w ∘ ar_mor A.
Proof. exact (ar_square w). Qed.

Lemma eqa_fork {G : Parallel ⟶ C} {z : C} (h : z ~> G ParX)
      (Hh : parallel_leg1 G ∘ h ≈ parallel_leg2 G ∘ h) :
  eqa_arr G ∘ unique_obj (eq_desc (eqa_wit G) h Hh) ≈ h.
Proof. exact (unique_property (eq_desc (eqa_wit G) h Hh)). Qed.

Lemma eqa_uniq {G : Parallel ⟶ C} {z : C} (h : z ~> G ParX)
      (Hh : parallel_leg1 G ∘ h ≈ parallel_leg2 G ∘ h)
      (w : z ~> eqa_obj G) :
  eqa_arr G ∘ w ≈ h -> unique_obj (eq_desc (eqa_wit G) h Hh) ≈ w.
Proof. intro Hw; exact (uniqueness (eq_desc (eqa_wit G) h Hh) w Hw). Qed.

(*
   本节说明等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma eqa_fmap_cond {G G' : Parallel ⟶ C} (t : G ⟹ G') :
  parallel_leg1 G' ∘ (transform[t] ParX ∘ eqa_arr G)
    ≈ parallel_leg2 G' ∘ (transform[t] ParX ∘ eqa_arr G).
Proof.
  unfold parallel_leg1, parallel_leg2.
  rewrite !comp_assoc.
  rewrite !(naturality t).
  rewrite <- !comp_assoc.
  now rewrite (fork_eq (eqa_wit G)).
Qed.

Definition eqa_fmap1 {G G' : Parallel ⟶ C} (t : G ⟹ G')
  : eqa_obj G ~> eqa_obj G' :=
  unique_obj (eq_desc (eqa_wit G') (transform[t] ParX ∘ eqa_arr G)
                      (eqa_fmap_cond t)).

Lemma eqa_fmap1_commutes {G G' : Parallel ⟶ C} (t : G ⟹ G') :
  eqa_arr G' ∘ eqa_fmap1 t ≈ transform[t] ParX ∘ eqa_arr G.
Proof. exact (eqa_fork _ (eqa_fmap_cond t)). Qed.

Lemma eqa_fmap1_unique {G G' : Parallel ⟶ C} (t : G ⟹ G')
      (w : eqa_obj G ~> eqa_obj G') :
  eqa_arr G' ∘ w ≈ transform[t] ParX ∘ eqa_arr G -> eqa_fmap1 t ≈ w.
Proof. exact (eqa_uniq _ (eqa_fmap_cond t) w). Qed.

Definition eqa_fmap {G G' : Parallel ⟶ C} (t : G ⟹ G')
  : eqa_ob G ~{@Arrow C}~> eqa_ob G' :=
  ((eqa_fmap1 t, transform[t] ParX); eqa_fmap1_commutes t).

#[local] Obligation Tactic := idtac.

(* 相关说明。 （已译） *)

Program Definition EqualizerArrowFunctor : [Parallel, C] ⟶ @Arrow C := {|
  fobj := eqa_ob ;
  fmap := fun G G' t => eqa_fmap t
|}.
Next Obligation.
  intros G G' s t Hst; split; simpl.
  - apply eqa_fmap1_unique.
    rewrite eqa_fmap1_commutes.
    now rewrite (Hst ParX).
  - exact (Hst ParX).
Qed.
Next Obligation.
  intros G; split; simpl.
  - apply eqa_fmap1_unique.
    unfold nat_id; simpl.
    now rewrite fmap_id, id_left, id_right.
  - unfold nat_id; simpl.
    now rewrite fmap_id.
Qed.
Next Obligation.
  intros G G' G'' t s; split; simpl.
  - apply eqa_fmap1_unique.
    rewrite comp_assoc, eqa_fmap1_commutes.
    rewrite <- comp_assoc, eqa_fmap1_commutes.
    now rewrite comp_assoc.
  - reflexivity.
Qed.

(* 相关说明。 （已译） *)

Definition eqa_dom_functor : [Parallel, C] ⟶ C :=
  Arrow_dom ◯ EqualizerArrowFunctor.

Example eqa_dom_functor_obj (G : Parallel ⟶ C) :
  fobj[eqa_dom_functor] G = eqa_obj G := eq_refl.

End EqualizerArrowFunctor.

(** ** The adjunction *)

Section CokernelPairAdjunction.

Context {C : Category}.
Context `{HP : @HasPushouts C}.
Context `{HE : @HasEqualizers C}.

(* 相关说明。 （已译） *)

Example ckp_pair_one (A : @Arrow C) :
  fmap[ckp_pair A] (true; ParOne) = ckp_u A := eq_refl.
Example ckp_pair_two (A : @Arrow C) :
  fmap[ckp_pair A] (false; ParTwo) = ckp_v A := eq_refl.

(*
   本节说明 CokernelPair 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma ckpadj_fork {A : @Arrow C} {G : Parallel ⟶ C} (t : ckp_pair A ⟹ G) :
  parallel_leg1 G ∘ (transform[t] ParX ∘ ar_mor A)
    ≈ parallel_leg2 G ∘ (transform[t] ParX ∘ ar_mor A).
Proof.
  unfold parallel_leg1, parallel_leg2.
  rewrite !comp_assoc.
  rewrite !(naturality t).
  rewrite ckp_pair_one, ckp_pair_two.
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | apply ckp_uv_commutes ].
Qed.

Lemma ckpadj_cocone {A : @Arrow C} {G : Parallel ⟶ C}
      (w : A ~{@Arrow C}~> eqa_ob G) :
  (parallel_leg1 G ∘ ar_snd w) ∘ ar_mor A
    ≈ (parallel_leg2 G ∘ ar_snd w) ∘ ar_mor A.
Proof.
  rewrite <- !comp_assoc.
  rewrite <- !(ar_square_eqa w).
  rewrite (comp_assoc (parallel_leg1 G) (eqa_arr G) (ar_fst w)).
  rewrite (comp_assoc (parallel_leg2 G) (eqa_arr G) (ar_fst w)).
  now rewrite (fork_eq (eqa_wit G)).
Qed.

(* Right: equalizer descent [ParX] component along the
 arrow A, 与…配对 component. （已译） *)

Definition ckpadj_to {A : @Arrow C} {G : Parallel ⟶ C}
           (t : ckp_pair A ⟹ G) : A ~{@Arrow C}~> eqa_ob G :=
  ((unique_obj (eq_desc (eqa_wit G) (transform[t] ParX ∘ ar_mor A)
                        (ckpadj_fork t)),
    transform[t] ParX);
   eqa_fork _ (ckpadj_fork t)).

(* 相关说明。 （已译） *)

Definition ckpadj_from_Y {A : @Arrow C} {G : Parallel ⟶ C}
           (w : A ~{@Arrow C}~> eqa_ob G)
  : ckp_obj (ckp_of A) ~> fobj[G] ParY :=
  ckp_med (ckp_of A) (ckpadj_cocone w).

Definition ckpadj_from_comp {A : @Arrow C} {G : Parallel ⟶ C}
           (w : A ~{@Arrow C}~> eqa_ob G) (z : ParObj)
  : fobj[ckp_pair A] z ~> fobj[G] z :=
  match z with
  | ParX => ar_snd w
  | ParY => ckpadj_from_Y w
  end.

Lemma ckpadj_from_natural {A : @Arrow C} {G : Parallel ⟶ C}
      (w : A ~{@Arrow C}~> eqa_ob G) (z z' : ParObj)
      (k : z ~{Parallel}~> z') :
  fmap[G] k ∘ ckpadj_from_comp w z
    ≈ ckpadj_from_comp w z' ∘ fmap[ckp_pair A] k.
Proof.
  destruct z, z'; simpl.
  - rewrite (par_fmap_idX G k).
    now rewrite id_left, id_right.
  - destruct k as [[|] k]; simpl;
      [ pose proof (ParHom_inv true ParX ParY k) as Hk
      | pose proof (ParHom_inv false ParX ParY k) as Hk ];
      simpl in Hk; subst k.
    + symmetry; exact (ckp_med_left (ckp_of A) (ckpadj_cocone w)).
    + symmetry; exact (ckp_med_right (ckp_of A) (ckpadj_cocone w)).
  - destruct (ParHom_Y_X_absurd _ (projT2 k)).
  - rewrite (par_fmap_idY G k).
    now rewrite id_left, id_right.
Qed.

Definition ckpadj_from {A : @Arrow C} {G : Parallel ⟶ C}
           (w : A ~{@Arrow C}~> eqa_ob G) : ckp_pair A ⟹ G :=
  @Build_Transform' Parallel C (ckp_pair A) G
                    (ckpadj_from_comp w) (@ckpadj_from_natural A G w).

(* Both round trips one appeal uniqueness clause each: the
 comma square equalizer side, 自然性 the
 cokernel-pair side. （已译） *)

Lemma ckpadj_to_from {A : @Arrow C} {G : Parallel ⟶ C}
      (w : A ~{@Arrow C}~> eqa_ob G) : ckpadj_to (ckpadj_from w) ≈ w.
Proof.
  split; simpl.
  - apply eqa_uniq.
    exact (ar_square_eqa w).
  - reflexivity.
Qed.

Lemma ckpadj_from_to {A : @Arrow C} {G : Parallel ⟶ C}
      (t : ckp_pair A ⟹ G) : ckpadj_from (ckpadj_to t) ≈ t.
Proof.
  intro z; destruct z; simpl.
  - reflexivity.
  - apply (ckp_med_unique (ckp_of A) (ckpadj_cocone (ckpadj_to t))).
    + symmetry; exact (naturality t ParX ParY (true; ParOne)).
    + symmetry; exact (naturality t ParX ParY (false; ParTwo)).
Qed.

#[local] Obligation Tactic := idtac.

Program Definition ckpadj_iso (A : @Arrow C) (G : Parallel ⟶ C) :
  @Isomorphism Sets
    {| carrier   := @hom ([Parallel, C]) (ckp_pair A) G
     ; is_setoid := @homset ([Parallel, C]) (ckp_pair A) G |}
    {| carrier   := @hom (@Arrow C) A (eqa_ob G)
     ; is_setoid := @homset (@Arrow C) A (eqa_ob G) |} := {|
  to   := {| morphism := ckpadj_to |};
  from := {| morphism := ckpadj_from |}
|}.
Next Obligation.
  intros A G t t' Ht; split; simpl.
  - apply eqa_uniq.
    rewrite eqa_fork.
    now rewrite (Ht ParX).
  - exact (Ht ParX).
Qed.
Next Obligation.
  intros A G w w' Hw z; destruct z; simpl.
  - exact (snd Hw).
  - apply (ckp_med_unique (ckp_of A) (ckpadj_cocone w)).
    + rewrite (ckp_med_left (ckp_of A) (ckpadj_cocone w')).
      now rewrite (snd Hw).
    + rewrite (ckp_med_right (ckp_of A) (ckpadj_cocone w')).
      now rewrite (snd Hw).
Qed.
Next Obligation. intros A G w; apply ckpadj_to_from. Qed.
Next Obligation. intros A G t; apply ckpadj_from_to. Qed.

(* Mac Lane §IV.2 Exercise 10. [Build_Adjunction'] takes the
 hom-setoid 同构 plus two forward 自然性 clauses and
 derives two inverse-transpose ones. （已译） *)

Program Definition CokernelPair_Equalizer_Adjunction
  : CokernelPairFunctor ⊣ EqualizerArrowFunctor :=
  @Build_Adjunction' ([Parallel, C]) (@Arrow C)
                     CokernelPairFunctor EqualizerArrowFunctor
                     ckpadj_iso _ _.
Next Obligation.
  intros x y z f g; split; simpl.
  - apply eqa_uniq.
    rewrite (comp_assoc (eqa_arr z) _ (ar_fst g)).
    rewrite eqa_fork.
    rewrite (comp_assoc_sym (transform[f] ParX) (ar_mor y) (ar_fst g)).
    rewrite (ar_square g).
    now rewrite (comp_assoc (transform[f] ParX) (ar_snd g) (ar_mor x)).
  - reflexivity.
Qed.
Next Obligation.
  intros x y z f g; split; simpl.
  - apply eqa_uniq.
    rewrite (comp_assoc (eqa_arr z) (eqa_fmap1 f) _).
    rewrite eqa_fmap1_commutes.
    rewrite (comp_assoc_sym (transform[f] ParX) (eqa_arr y) _).
    rewrite eqa_fork.
    now rewrite (comp_assoc (transform[f] ParX) (transform[g] ParX)
                            (ar_mor x)).
  - reflexivity.
Qed.

(* 相关说明。 （已译） *)

(* Mac Lane's comparison f 进入 equalizer cokernel pair:
 descent [ar_mor A] across equalizer, 与…配对 the
 恒等. （已译） *)

Definition ckp_unit_med (A : @Arrow C)
  : ar_dom A ~> eqa_obj (ckp_pair A) :=
  unique_obj (eq_desc (eqa_wit (ckp_pair A)) (ar_mor A)
                      (ckp_uv_commutes A)).

Lemma ckp_unit_med_commutes (A : @Arrow C) :
  eqa_arr (ckp_pair A) ∘ ckp_unit_med A ≈ ar_mor A.
Proof.
  exact (eqa_fork (G:=ckp_pair A) (ar_mor A) (ckp_uv_commutes A)).
Qed.

Lemma ckp_unit_med_unique (A : @Arrow C)
      (w : ar_dom A ~> eqa_obj (ckp_pair A)) :
  eqa_arr (ckp_pair A) ∘ w ≈ ar_mor A -> ckp_unit_med A ≈ w.
Proof.
  exact (eqa_uniq (G:=ckp_pair A) (ar_mor A) (ckp_uv_commutes A) w).
Qed.

Program Definition cokernel_pair_unit (A : @Arrow C)
  : A ~{@Arrow C}~> eqa_ob (ckp_pair A) :=
  ((ckp_unit_med A, id[ar_cod A]); _).
Next Obligation.
  intros A.
  simpl.
  rewrite id_left.
  exact (ckp_unit_med_commutes A).
Qed.

(* The coequalizing comparison: 恒等, together the
 cokernel-pair mediator two legs G, whose cocone condition
 [fork_eq] chosen equalizer G. （已译） *)

Definition ckpc_comp (G : Parallel ⟶ C) (z : ParObj)
  : fobj[ckp_pair (eqa_ob G)] z ~> fobj[G] z :=
  match z with
  | ParX => id[fobj[G] ParX]
  | ParY => ckp_med (ckp_of (eqa_ob G)) (fork_eq (eqa_wit G))
  end.

Lemma ckpc_natural (G : Parallel ⟶ C) (z z' : ParObj)
      (k : z ~{Parallel}~> z') :
  fmap[G] k ∘ ckpc_comp G z ≈ ckpc_comp G z' ∘ fmap[ckp_pair (eqa_ob G)] k.
Proof.
  destruct z, z'; simpl.
  - rewrite (par_fmap_idX G k).
    now rewrite id_left, id_right.
  - destruct k as [[|] k]; simpl;
      [ pose proof (ParHom_inv true ParX ParY k) as Hk
      | pose proof (ParHom_inv false ParX ParY k) as Hk ];
      simpl in Hk; subst k; rewrite id_right.
    + symmetry.
      exact (ckp_med_left (ckp_of (eqa_ob G)) (fork_eq (eqa_wit G))).
    + symmetry.
      exact (ckp_med_right (ckp_of (eqa_ob G)) (fork_eq (eqa_wit G))).
  - destruct (ParHom_Y_X_absurd _ (projT2 k)).
  - rewrite (par_fmap_idY G k).
    now rewrite id_left, id_right.
Qed.

Definition cokernel_pair_counit (G : Parallel ⟶ C)
  : ckp_pair (eqa_ob G) ⟹ G :=
  @Build_Transform' Parallel C (ckp_pair (eqa_ob G)) G
                    (ckpc_comp G) (ckpc_natural G).

(* 相关说明。 （已译） *)

Definition ckp_class_unit (A : @Arrow C) :=
  @unit ([Parallel, C]) (@Arrow C) CokernelPairFunctor
        EqualizerArrowFunctor CokernelPair_Equalizer_Adjunction A.

Definition ckp_class_counit (G : Parallel ⟶ C) :=
  @counit ([Parallel, C]) (@Arrow C) CokernelPairFunctor
          EqualizerArrowFunctor CokernelPair_Equalizer_Adjunction G.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example ckp_unit_snd_strict (A : @Arrow C) :
  snd `1 (ckp_class_unit A) = snd `1 (cokernel_pair_unit A) := eq_refl.

Example ckp_counit_X_strict (G : Parallel ⟶ C) :
  transform[ckp_class_counit G] ParX
    = transform[cokernel_pair_counit G] ParX := eq_refl.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example ckp_unit_fst_strict (A : @Arrow C) :
  fst `1 (ckp_class_unit A) = fst `1 (cokernel_pair_unit A) := eq_refl.

Fail Example ckp_counit_Y_strict (G : Parallel ⟶ C) :
  transform[ckp_class_counit G] ParY
    = transform[cokernel_pair_counit G] ParY := eq_refl.

Theorem ckp_class_unit_agrees (A : @Arrow C) :
  ckp_class_unit A ≈ cokernel_pair_unit A.
Proof.
  split; simpl.
  - apply eqa_uniq.
    simpl.
    rewrite id_left.
    exact (ckp_unit_med_commutes A).
  - reflexivity.
Qed.

Theorem ckp_class_counit_agrees (G : Parallel ⟶ C) :
  ckp_class_counit G ≈ cokernel_pair_counit G.
Proof.
  intro z; destruct z; simpl.
  - reflexivity.
  - apply (ckp_med_unique (ckp_of (eqa_ob G))
                          (ckpadj_cocone (@id (@Arrow C) (eqa_ob G)))).
    + rewrite (ckp_med_left (ckp_of (eqa_ob G)) (fork_eq (eqa_wit G))).
      now rewrite id_right.
    + rewrite (ckp_med_right (ckp_of (eqa_ob G)) (fork_eq (eqa_wit G))).
      now rewrite id_right.
Qed.

End CokernelPairAdjunction.

(* * ** When unit 同构 （已译） *)

(*
   本节说明等化子、核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Regularity.

Context {C : Category}.
Context `{HP : @HasPushouts C}.
Context `{HE : @HasEqualizers C}.

(* An equalizer transported along an isomorphism of its apex is again
   one.  Stated for an arbitrary parallel pair; nothing about cokernel
   pairs enters. *)

Lemma IsEqualizer_along_iso {x y q d : C} {u v : x ~> y} {e : q ~> x}
      (E : IsEqualizer u v q e) (k : d ~> q) (K : IsIsomorphism k)
      {m : d ~> x} (Hm : e ∘ k ≈ m) : IsEqualizer u v d m.
Proof.
  construct.
  - rewrite <- Hm.
    rewrite !comp_assoc.
    now rewrite (fork_eq E).
  - exists (two_sided_inverse ∘ unique_obj (eq_desc E h Hh)).
    + rewrite comp_assoc.
      rewrite <- Hm.
      rewrite (comp_assoc_sym e k two_sided_inverse).
      rewrite is_right_inverse, id_right.
      exact (unique_property (eq_desc E h Hh)).
    + intros w Hw.
      rewrite <- (id_left w).
      rewrite <- is_left_inverse.
      rewrite (comp_assoc_sym two_sided_inverse k w).
      apply compose_respects; [ reflexivity | ].
      apply (uniqueness (eq_desc E h Hh)).
      rewrite (comp_assoc e k w), Hm.
      exact Hw.
Qed.

Definition RegularCokernelPair (A : @Arrow C) : Type :=
  IsEqualizer (ckp_u A) (ckp_v A) (ar_dom A) (ar_mor A).

Theorem unit_med_iso_regular (A : @Arrow C)
        (K : IsIsomorphism (ckp_unit_med A)) : RegularCokernelPair A.
Proof.
  exact (IsEqualizer_along_iso (eqa_wit (ckp_pair A)) (ckp_unit_med A) K
                               (ckp_unit_med_commutes A)).
Qed.

Corollary unit_med_iso_Monic (A : @Arrow C)
          (K : IsIsomorphism (ckp_unit_med A)) : Monic (ar_mor A).
Proof. exact (equalizer_monic _ _ (unit_med_iso_regular A K)). Qed.

Theorem regular_unit_med_iso (A : @Arrow C) (E : RegularCokernelPair A)
  : IsIsomorphism (ckp_unit_med A).
Proof.
  unshelve econstructor.
  - exact (unique_obj (eq_desc E (eqa_arr (ckp_pair A))
                               (fork_eq (eqa_wit (ckp_pair A))))).
  - apply (equalizer_monic _ _ (eqa_wit (ckp_pair A))).
    rewrite (comp_assoc (eqa_arr (ckp_pair A))).
    rewrite ckp_unit_med_commutes.
    rewrite (unique_property (eq_desc E (eqa_arr (ckp_pair A))
                                     (fork_eq (eqa_wit (ckp_pair A))))).
    now rewrite id_right.
  - apply (equalizer_monic _ _ E).
    rewrite (comp_assoc (ar_mor A)).
    rewrite (unique_property (eq_desc E (eqa_arr (ckp_pair A))
                                     (fork_eq (eqa_wit (ckp_pair A))))).
    rewrite ckp_unit_med_commutes.
    now rewrite id_right.
Qed.

(*
   本节说明 CokernelPair 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma arrow_iso_fst {A B : @Arrow C} {w : A ~{@Arrow C}~> B}
      (K : IsIsomorphism w) : IsIsomorphism (ar_fst w).
Proof.
  unshelve econstructor.
  - exact (ar_fst (@two_sided_inverse (@Arrow C) A B w K)).
  - exact (fst (@is_right_inverse (@Arrow C) A B w K)).
  - exact (fst (@is_left_inverse (@Arrow C) A B w K)).
Qed.

#[local] Obligation Tactic := idtac.

Program Definition unit_iso_of_med_iso (A : @Arrow C)
        (K : IsIsomorphism (ckp_unit_med A))
  : IsIsomorphism (cokernel_pair_unit A) :=
  {| two_sided_inverse :=
       ((@two_sided_inverse C _ _ (ckp_unit_med A) K, id[ar_cod A]); _) |}.
Next Obligation.
  intros A K; simpl.
  rewrite id_left.
  rewrite <- (ckp_unit_med_commutes A).
  rewrite (comp_assoc_sym (eqa_arr (ckp_pair A)) (ckp_unit_med A) _).
  now rewrite is_right_inverse, id_right.
Qed.
Next Obligation.
  intros A K; split; simpl.
  - exact is_right_inverse.
  - now rewrite id_left.
Qed.
Next Obligation.
  intros A K; split; simpl.
  - exact is_left_inverse.
  - now rewrite id_left.
Qed.

Theorem unit_iso_iff_regular (A : @Arrow C) :
  IsIsomorphism (cokernel_pair_unit A) ↔ RegularCokernelPair A.
Proof.
  split.
  - intro K; exact (unit_med_iso_regular A (arrow_iso_fst K)).
  - intro E; exact (unit_iso_of_med_iso A (regular_unit_med_iso A E)).
Qed.

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma split_retract_cocone {A : @Arrow C} {r : ar_cod A ~> ar_dom A}
      (Hr : r ∘ ar_mor A ≈ id) :
  id[ar_cod A] ∘ ar_mor A ≈ (ar_mor A ∘ r) ∘ ar_mor A.
Proof.
  rewrite id_left.
  rewrite (comp_assoc_sym (ar_mor A) r (ar_mor A)).
  now rewrite Hr, id_right.
Qed.

Definition split_retract_med {A : @Arrow C} {r : ar_cod A ~> ar_dom A}
           (Hr : r ∘ ar_mor A ≈ id) : ckp_obj (ckp_of A) ~> ar_cod A :=
  ckp_med (ckp_of A) (split_retract_cocone Hr).

Theorem split_mono_regular {A : @Arrow C} {r : ar_cod A ~> ar_dom A}
        (Hr : r ∘ ar_mor A ≈ id) : RegularCokernelPair A.
Proof.
  construct.
  - exact (ckp_uv_commutes A).
  - exists (r ∘ h).
    + rewrite (comp_assoc (ar_mor A) r h).
      rewrite <- (ckp_med_right (ckp_of A) (split_retract_cocone Hr)).
      rewrite (comp_assoc_sym (split_retract_med Hr) (ckp_v A) h).
      rewrite <- Hh.
      rewrite (comp_assoc (split_retract_med Hr) (ckp_u A) h).
      rewrite (ckp_med_left (ckp_of A) (split_retract_cocone Hr)).
      now rewrite id_left.
    + intros w Hw.
      rewrite <- Hw.
      rewrite (comp_assoc r (ar_mor A) w).
      now rewrite Hr, id_left.
Qed.

Corollary split_mono_unit_iso {A : @Arrow C} {r : ar_cod A ~> ar_dom A}
          (Hr : r ∘ ar_mor A ≈ id)
  : IsIsomorphism (cokernel_pair_unit A).
Proof.
  exact (unit_iso_of_med_iso A (regular_unit_med_iso A
                                 (split_mono_regular Hr))).
Qed.

End Regularity.

(** ** Non-vacuity at Sets *)

Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Pushout.

Section SetsWitness.

(*
   本节说明 CokernelPair 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition SetsEqualizers : @HasEqualizers Sets :=
  @HasEqualizers_of_HasPullbacks_Terminal Sets Sets_Terminal
                                          Sets_HasPullbacks.

#[local] Existing Instance SetsEqualizers.

(* Instance/Sets.v's two-element one-element setoids,
 with
 collapse onto point 含入 point. Neither
 对象 nor arrow rebuilt here. （已译） *)

Definition ArrCollapse : @Arrow Sets :=
  ((bool_setoid_object, unit_setoid_object); collapse).

Definition ArrPick : @Arrow Sets :=
  ((unit_setoid_object, bool_setoid_object); pick_true).

Example sets_arr_collapse_mor : ar_mor ArrCollapse = collapse := eq_refl.
Example sets_arr_pick_mor : ar_mor ArrPick = pick_true := eq_refl.

(*
   本节说明拉回/推出、等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem sets_collapse_unit_not_iso :
  IsIsomorphism (cokernel_pair_unit ArrCollapse) -> False.
Proof.
  intro K.
  apply collapse_not_monic.
  exact (unit_med_iso_Monic ArrCollapse (arrow_iso_fst K)).
Qed.

(* POSITIVE. The 含入 point split collapse
 (Instance/Sets.v's [collapse_pick]), hence regular, hence its
 unit invertible. （已译） *)

Theorem sets_pick_regular : RegularCokernelPair ArrPick.
Proof. exact (split_mono_regular (A:=ArrPick) (r:=collapse) collapse_pick). Qed.

Theorem sets_pick_unit_iso :
  IsIsomorphism (cokernel_pair_unit ArrPick).
Proof. exact (snd (unit_iso_iff_regular ArrPick) sets_pick_regular). Qed.

(* And positive case not degenerate: arrow itself not an
 同构, since it misses [false] so not epic
 (Instance/Sets.v). （已译） *)

Theorem sets_pick_not_iso : IsIsomorphism pick_true -> False.
Proof.
  intro K.
  apply pick_true_not_epic.
  exact (iso_to_epic (IsIsoToIso pick_true K)).
Qed.

End SetsWitness.

(** ** Universe probe *)

(*
   本节说明hom、（余）端、核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UniverseProbe.

Universes co ch cp.
Constraint ch < cp.
Context {Cu : Category@{co ch cp}}.
Context (cx cy : Cu).

(* Controls: hom type 恒等 DO elaborate at these
 levels, so rejections below about four donors. （已译） *)
Check (cx ~{Cu}~> cy).
Check (@id Cu cx).

(* 相关说明。 （已译） *)
Fail Check (@Arrow Cu).
Fail Check ([Parallel, Cu]).
Fail Check (@HasPushouts Cu).
Fail Check (@HasEqualizers Cu).

End UniverseProbe.

(* 相关说明。 （已译） *)
Fail Check ckp_no_such_constant.
