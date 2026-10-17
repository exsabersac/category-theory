(* 相关说明。 （已译） *)

(*
   nLab:      https://ncatlab.org/nlab/show/coequalizer
   nLab:      https://ncatlab.org/nlab/show/pullback
   nLab:      https://ncatlab.org/nlab/show/pushout
   nLab:      https://ncatlab.org/nlab/show/diagonal+functor
   Wikipedia: https://en.wikipedia.org/wiki/Equaliser_(mathematics)
   Wikipedia: https://en.wikipedia.org/wiki/Pullback_(category_theory)

   本文件给出有限情形。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明伴随、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Finite 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Span.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Limit.
Require Import Category.Structure.Pushout.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Morphisms.CokernelPair.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Adjunction.Diagonal.Limit.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本节说明 Finite 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Respects.

Context {C : Category}.

Lemma IsEqualizer_respects {x y q : C} {f g : x ~> y} {e e' : q ~> x} :
  IsEqualizer f g q e → e ≈ e' → IsEqualizer f g q e'.
Proof.
  intros E He.
  unshelve econstructor.
  - rewrite <- He; exact (fork_eq E).
  - intros z h Hh.
    unshelve eapply Build_Unique.
    + exact (unique_obj (eq_desc E h Hh)).
    + rewrite <- He; exact (unique_property (eq_desc E h Hh)).
    + intros v Hv.
      apply (uniqueness (eq_desc E h Hh)).
      rewrite He; exact Hv.
Defined.

Lemma IsCoequalizer_respects {x y q : C} {f g : x ~> y} {e e' : y ~> q} :
  IsCoequalizer f g q e → e ≈ e' → IsCoequalizer f g q e'.
Proof.
  intros E He.
  unshelve econstructor.
  - rewrite <- He; exact (cofork E).
  - intros z h Hh.
    unshelve eapply Build_Unique.
    + exact (unique_obj (coeq_desc E h Hh)).
    + rewrite <- He; exact (unique_property (coeq_desc E h Hh)).
    + intros v Hv.
      apply (uniqueness (coeq_desc E h Hh)).
      rewrite He; exact Hv.
Defined.

Lemma IsPullback_respects {x y z P : C} {f : x ~> z} {g : y ~> z}
  {p1 p1' : P ~> x} {p2 p2' : P ~> y} :
  IsPullback f g P p1 p2 → p1 ≈ p1' → p2 ≈ p2' →
  IsPullback f g P p1' p2'.
Proof.
  intros H H1 H2.
  unshelve econstructor.
  - rewrite <- H1, <- H2; exact (is_pullback_commutes H).
  - intros Q q1 q2 Hc.
    unshelve eapply Build_Unique.
    + exact (unique_obj (is_pullback_ump H Q q1 q2 Hc)).
    + split.
      * rewrite <- H1.
        exact (fst (unique_property (is_pullback_ump H Q q1 q2 Hc))).
      * rewrite <- H2.
        exact (snd (unique_property (is_pullback_ump H Q q1 q2 Hc))).
    + intros v [Hv1 Hv2].
      apply (uniqueness (is_pullback_ump H Q q1 q2 Hc)).
      split.
      * rewrite H1; exact Hv1.
      * rewrite H2; exact Hv2.
Defined.

End Respects.

(* The pushout square [IsPullback] opposite 范畴, the
 two hom-setoids agree there, so transport primal one read at
 [C^op]: [:=] no tactic. （已译） *)
Definition IsPushoutSquare_respects {C : Category} {x y z P : C}
  {f : x ~> y} {g : x ~> z} {i1 i1' : y ~> P} {i2 i2' : z ~> P} :
  IsPushoutSquare f g P i1 i2 → i1 ≈ i1' → i2 ≈ i2' →
  IsPushoutSquare f g P i1' i2' :=
  @IsPullback_respects (C^op) y z x P f g i1 i1' i2 i2'.

(* 相关说明。 （已译） *)

(*
   本节说明 Finite 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ShapeLinked {J : Category} (j0 : J) : Type :=
  ∀ j : J, (j0 ~{J}~> j) + (j ~{J}~> j0).

Section ConstantLimit.

Context {J C : Category}.
Context (L : HasLimitsOfShape J C).

Lemma lim_const_legs (x : C) (j0 : J) (Hl : ShapeLinked j0) (j : J) :
  lim_leg L (Δ[J](x)) j ≈ lim_leg L (Δ[J](x)) j0.
Proof.
  destruct (Hl j) as [k | k].
  - transitivity (fmap[Δ[J](x)] k ∘ lim_leg L (Δ[J](x)) j0).
    + symmetry; exact (lim_leg_coherence L (Δ[J](x)) k).
    + apply id_left.
  - transitivity (fmap[Δ[J](x)] k ∘ lim_leg L (Δ[J](x)) j).
    + symmetry; apply id_left.
    + exact (lim_leg_coherence L (Δ[J](x)) k).
Qed.

(* The unit of Δ ⊣ lim, named. *)
Definition dia_unit (x : C) : x ~{C}~> lim_obj L (Δ[J](x)) :=
  @unit ([J, C]) C (@Diagonal C J) (LimitFunctor L)
        (Diagonal_Limit_Adjunction L) x.

(* The unit IS transpose 恒等, nose. （已译） *)
Example dia_unit_strict (x : C) :
  dia_unit x = lim_transpose_to L (@id ([J, C]) (Δ[J](x))) := eq_refl.

Lemma dia_unit_leg (x : C) (j : J) :
  lim_leg L (Δ[J](x)) j ∘ dia_unit x ≈ id[x].
Proof.
  exact (lim_transpose_to_commutes L
           (@id ([J, C]) (Δ[J](x))) j).
Qed.

(*
   本节说明（余）极限、拉回/推出、等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition dia_unit_iso (j0 : J) (Hl : ShapeLinked j0) (x : C) :
  x ≅ lim_obj L (Δ[J](x)) := {|
  to   := dia_unit x;
  from := lim_leg L (Δ[J](x)) j0
|}.
Next Obligation.
  refine (lim_med_eq L (@limit_cone J C (Δ[J](x)) (L (Δ[J](x)))) _ _ _ _);
  intro j.
  - rewrite comp_assoc, dia_unit_leg, id_left.
    symmetry; exact (lim_const_legs x j0 Hl j).
  - apply id_right.
Qed.
Next Obligation. apply dia_unit_leg. Qed.

End ConstantLimit.

Section ConstantColimit.

Context {J C : Category}.
Context (M : HasColimitsOfShape J C).

Lemma colim_const_injs (x : C) (j0 : J) (Hl : ShapeLinked j0) (j : J) :
  colim_inj M (Δ[J](x)) j ≈ colim_inj M (Δ[J](x)) j0.
Proof.
  destruct (Hl j) as [k | k].
  - transitivity (colim_inj M (Δ[J](x)) j ∘ fmap[Δ[J](x)] k).
    + symmetry; apply id_right.
    + exact (colim_inj_coherence M (Δ[J](x)) k).
  - transitivity (colim_inj M (Δ[J](x)) j0 ∘ fmap[Δ[J](x)] k).
    + symmetry; exact (colim_inj_coherence M (Δ[J](x)) k).
    + apply id_right.
Qed.

(* The counit of colim ⊣ Δ, named. *)
Definition dia_counit (x : C) : colim_obj M (Δ[J](x)) ~{C}~> x :=
  @counit C ([J, C]) (ColimitFunctor M) (@Diagonal C J)
          (Colimit_Diagonal_Adjunction M) x.

Example dia_counit_strict (x : C) :
  dia_counit x = colim_transpose_from M (@id ([J, C]) (Δ[J](x)))
  := eq_refl.

Lemma dia_counit_inj (x : C) (j : J) :
  dia_counit x ∘ colim_inj M (Δ[J](x)) j ≈ id[x].
Proof.
  exact (colim_transpose_from_commutes M
           (@id ([J, C]) (Δ[J](x))) j).
Qed.

Program Definition dia_counit_iso (j0 : J) (Hl : ShapeLinked j0) (x : C) :
  colim_obj M (Δ[J](x)) ≅ x := {|
  to   := dia_counit x;
  from := colim_inj M (Δ[J](x)) j0
|}.
Next Obligation. apply dia_counit_inj. Qed.
Next Obligation.
  refine (colim_med_eq M (@limit_cone (J^op) (C^op) ((Δ[J](x))^op)
                            (M (Δ[J](x)))) _ _ _ _);
  intro j.
  - rewrite <- comp_assoc, dia_counit_inj, id_right.
    symmetry; exact (colim_const_injs x j0 Hl j).
  - apply id_left.
Qed.

End ConstantColimit.

(* 相关说明。 （已译） *)

Definition Parallel_linked : @ShapeLinked Parallel ParX.
Proof.
  intro j; destruct j.
  - left; exact ((true; ParIdX) : ParX ~{Parallel}~> ParX).
  - left; exact ((true; ParOne) : ParX ~{Parallel}~> ParY).
Defined.

Definition Roof_linked : @ShapeLinked Roof RZero.
Proof.
  intro j; destruct j.
  - left; exact ZeroNeg.
  - left; exact IdZero.
  - left; exact ZeroPos.
Defined.

Definition Roofop_linked : @ShapeLinked (Roof^op) RZero.
Proof.
  intro j; destruct j.
  - right; exact ZeroNeg.
  - left; exact IdZero.
  - right; exact ZeroPos.
Defined.

(* * * Row 1: equalizers 右伴随 Δ[Parallel] （已译） *)

Section EqualizerRow.

Context {C : Category}.
Context (L : HasLimitsOfShape Parallel C).

Definition EqualizerFunctor : [Parallel, C] ⟶ C := LimitFunctor L.

Definition Diagonal_Equalizer_Adjunction :
  @Diagonal C Parallel ⊣ EqualizerFunctor := Diagonal_Limit_Adjunction L.

Definition eq_counit (F : Parallel ⟶ C) : Δ[Parallel](lim_obj L F) ⟹ F :=
  lim_counit L F.

(* 相关说明。 （已译） *)
Definition eq_arrow (F : Parallel ⟶ C) : lim_obj L F ~{C}~> F ParX :=
  transform[eq_counit F] ParX.

Example eq_arrow_strict (F : Parallel ⟶ C) :
  eq_arrow F = lim_leg L F ParX ∘ id := eq_refl.

Lemma eq_leg_is_arrow (F : Parallel ⟶ C) :
  lim_leg L F ParX ≈ eq_arrow F.
Proof. symmetry; exact (lim_counit_is_limit_leg L F ParX). Qed.

(* 相关说明。 （已译） *)
Definition eq_counit_IsEqualizer {x y : C} (f g : x ~> y) :
  IsEqualizer f g (lim_obj L (APair f g)) (eq_arrow (APair f g)) :=
  IsEqualizer_respects (equalizer_is_equalizer f g (L (APair f g)))
    (eq_leg_is_arrow (APair f g)).

Definition HasLimitsOfShape_HasEqualizers : HasEqualizers C :=
  {| equalizer := fun x y f g =>
       (lim_obj L (APair f g);
         (eq_arrow (APair f g); eq_counit_IsEqualizer f g)) |}.

(* Mac Lane's unit entry: 恒等, precise sense the
 unit invertible limiting leg inverse. （已译） *)
Definition eq_unit_iso (x : C) : x ≅ lim_obj L (Δ[Parallel](x)) :=
  dia_unit_iso L ParX Parallel_linked x.

End EqualizerRow.

(* * * Row 2: coequalizers 左伴随 Δ[Parallel] （已译） *)

Section CoequalizerRow.

Context {C : Category}.
Context (M : HasColimitsOfShape Parallel C).

Definition CoequalizerFunctor : [Parallel, C] ⟶ C := ColimitFunctor M.

Definition Coequalizer_Diagonal_Adjunction :
  CoequalizerFunctor ⊣ @Diagonal C Parallel := Colimit_Diagonal_Adjunction M.

Definition coeq_unit (F : Parallel ⟶ C) : F ⟹ Δ[Parallel](colim_obj M F) :=
  colim_unit M F.

(* 相关说明。 （已译） *)
Definition coeq_arrow (F : Parallel ⟶ C) : F ParY ~{C}~> colim_obj M F :=
  transform[coeq_unit F] ParY.

Example coeq_arrow_strict (F : Parallel ⟶ C) :
  coeq_arrow F = id ∘ colim_inj M F ParY := eq_refl.

Lemma coeq_inj_is_arrow (F : Parallel ⟶ C) :
  colim_inj M F ParY ≈ coeq_arrow F.
Proof. symmetry; exact (colim_unit_is_colimit_inj M F ParY). Qed.

Definition coeq_unit_IsCoequalizer {x y : C} (f g : x ~> y) :
  IsCoequalizer f g (colim_obj M (APair f g)) (coeq_arrow (APair f g)) :=
  IsCoequalizer_respects (coequalizer_is_coequalizer f g (M (APair f g)))
    (coeq_inj_is_arrow (APair f g)).

Definition HasColimitsOfShape_HasCoequalizers : HasCoequalizers C :=
  {| coeq := fun x y f g =>
       (colim_obj M (APair f g);
         (coeq_arrow (APair f g); coeq_unit_IsCoequalizer f g)) |}.

Definition coeq_counit_iso (x : C) : colim_obj M (Δ[Parallel](x)) ≅ x :=
  dia_counit_iso M ParX Parallel_linked x.

End CoequalizerRow.

(* * * Row 3: pullbacks 右伴随 Δ[Roof^op] （已译） *)

Section PullbackRow.

Context {C : Category}.
Context (L : HasLimitsOfShape (Roof^op) C).

(* The two legs of a cospan, read covariantly in C. *)
Definition cospan_left (F : Roof^op ⟶ C) : F RNeg ~{C}~> F RZero :=
  fmap[F] (ZeroNeg : RNeg ~{Roof^op}~> RZero).

Definition cospan_right (F : Roof^op ⟶ C) : F RPos ~{C}~> F RZero :=
  fmap[F] (ZeroPos : RPos ~{Roof^op}~> RZero).

Definition PullbackFunctor : [Roof^op, C] ⟶ C := LimitFunctor L.

Definition Diagonal_Pullback_Adjunction :
  @Diagonal C (Roof^op) ⊣ PullbackFunctor := Diagonal_Limit_Adjunction L.

Definition pb_counit (F : Roof^op ⟶ C) : Δ[Roof^op](lim_obj L F) ⟹ F :=
  lim_counit L F.

(* 相关说明。 （已译） *)
Definition pb_fst (F : Roof^op ⟶ C) : lim_obj L F ~{C}~> F RNeg :=
  transform[pb_counit F] RNeg.

Definition pb_snd (F : Roof^op ⟶ C) : lim_obj L F ~{C}~> F RPos :=
  transform[pb_counit F] RPos.

Example pb_fst_strict (F : Roof^op ⟶ C) :
  pb_fst F = lim_leg L F RNeg ∘ id := eq_refl.

Example pb_snd_strict (F : Roof^op ⟶ C) :
  pb_snd F = lim_leg L F RPos ∘ id := eq_refl.

Lemma pb_leg_is_fst (F : Roof^op ⟶ C) : lim_leg L F RNeg ≈ pb_fst F.
Proof. symmetry; exact (lim_counit_is_limit_leg L F RNeg). Qed.

Lemma pb_leg_is_snd (F : Roof^op ⟶ C) : lim_leg L F RPos ≈ pb_snd F.
Proof. symmetry; exact (lim_counit_is_limit_leg L F RPos). Qed.

(*
   本节说明（余）极限、拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition pb_leg_IsPullback (F : Roof^op ⟶ C) :
  IsPullback (cospan_left F) (cospan_right F) (lim_obj L F)
             (lim_leg L F RNeg) (lim_leg L F RPos) :=
  pullback_is_pullback _ _ (Pullback_to_Universal F (L F)).

(* 相关说明。 （已译） *)
Definition pb_counit_IsPullback (F : Roof^op ⟶ C) :
  IsPullback (cospan_left F) (cospan_right F) (lim_obj L F)
             (pb_fst F) (pb_snd F) :=
  IsPullback_respects (pb_leg_IsPullback F)
    (pb_leg_is_fst F) (pb_leg_is_snd F).

(* A cospan in C, as a diagram of shape Roof^op. *)
Definition ACospan {x y z : C} (f : x ~> z) (g : y ~> z) : Roof^op ⟶ C :=
  (@ASpan (C^op) z x y f g)^op.

Example acospan_left {x y z : C} (f : x ~> z) (g : y ~> z) :
  cospan_left (ACospan f g) = f := eq_refl.

Example acospan_right {x y z : C} (f : x ~> z) (g : y ~> z) :
  cospan_right (ACospan f g) = g := eq_refl.

Definition HasLimitsOfShape_HasPullbacks : HasPullbacks C :=
  {| pullback := fun x y z f g =>
       is_pullback_pullback (pb_counit_IsPullback (ACospan f g)) |}.

Definition pb_unit_iso (x : C) : x ≅ lim_obj L (Δ[Roof^op](x)) :=
  dia_unit_iso L RZero Roofop_linked x.

End PullbackRow.

(* * * Row 4: pushouts 左伴随 Δ[Roof] （已译） *)

Section PushoutRow.

Context {C : Category}.
Context (M : HasColimitsOfShape Roof C).

Definition span_left (F : Roof ⟶ C) : F RZero ~{C}~> F RNeg :=
  fmap[F] ZeroNeg.

Definition span_right (F : Roof ⟶ C) : F RZero ~{C}~> F RPos :=
  fmap[F] ZeroPos.

Definition PushoutFunctor : [Roof, C] ⟶ C := ColimitFunctor M.

Definition Pushout_Diagonal_Adjunction :
  PushoutFunctor ⊣ @Diagonal C Roof := Colimit_Diagonal_Adjunction M.

Definition po_unit (F : Roof ⟶ C) : F ⟹ Δ[Roof](colim_obj M F) :=
  colim_unit M F.

(* 相关说明。 （已译） *)
Definition pushout_inj1 (F : Roof ⟶ C) : F RNeg ~{C}~> colim_obj M F :=
  transform[po_unit F] RNeg.

Definition pushout_inj2 (F : Roof ⟶ C) : F RPos ~{C}~> colim_obj M F :=
  transform[po_unit F] RPos.

Example po_in1_strict (F : Roof ⟶ C) :
  pushout_inj1 F = id ∘ colim_inj M F RNeg := eq_refl.

Example po_in2_strict (F : Roof ⟶ C) :
  pushout_inj2 F = id ∘ colim_inj M F RPos := eq_refl.

Lemma po_inj_is_in1 (F : Roof ⟶ C) : colim_inj M F RNeg ≈ pushout_inj1 F.
Proof. symmetry; exact (colim_unit_is_colimit_inj M F RNeg). Qed.

Lemma po_inj_is_in2 (F : Roof ⟶ C) : colim_inj M F RPos ≈ pushout_inj2 F.
Proof. symmetry; exact (colim_unit_is_colimit_inj M F RPos). Qed.

(* The colimiting square of a span commutes. *)
Lemma po_inj_commutes (F : Roof ⟶ C) :
  colim_inj M F RNeg ∘ span_left F ≈ colim_inj M F RPos ∘ span_right F.
Proof.
  transitivity (colim_inj M F RZero).
  - exact (colim_inj_coherence M F (ZeroNeg : RZero ~{Roof}~> RNeg)).
  - symmetry.
    exact (colim_inj_coherence M F (ZeroPos : RZero ~{Roof}~> RPos)).
Qed.

(* Every hom-setoid of [Roof] is trivially true, so a functor out of it
   carries any two parallel arrows to [≈]-equal morphisms; the identity
   arrows go to identities.  These two facts discharge every case of the
   cocone coherence below. *)
Lemma roof_fmap_any (F : Roof ⟶ C) {a b : Roof} (k k' : a ~{Roof}~> b) :
  fmap[F] k ≈ fmap[F] k'.
Proof. apply fmap_respects; exact I. Qed.

Lemma roof_fmap_id (F : Roof ⟶ C) (a : Roof) (k : a ~{Roof}~> a) :
  fmap[F] k ≈ id.
Proof.
  rewrite (roof_fmap_any F k (id[a])).
  apply fmap_id.
Qed.

(* The cocone under span determined competing 交换方块:
 leg at apex RZero forced common 复合. （已译） *)
Definition po_legs (F : Roof ⟶ C) (Q : C)
  (q1 : F RNeg ~> Q) (q2 : F RPos ~> Q) (j : Roof) : F j ~{C}~> Q :=
  match j return F j ~{C}~> Q with
  | RNeg  => q1
  | RZero => q1 ∘ span_left F
  | RPos  => q2
  end.

Lemma po_legs_coherence (F : Roof ⟶ C) (Q : C)
  (q1 : F RNeg ~> Q) (q2 : F RPos ~> Q)
  (Hc : q1 ∘ span_left F ≈ q2 ∘ span_right F) :
  ∀ (a b : Roof) (k : a ~{Roof}~> b),
    po_legs F Q q1 q2 b ∘ fmap[F] k ≈ po_legs F Q q1 q2 a.
Proof.
  intros a b k.
  destruct a, b; simpl in k; auto with roof_laws; simpl.
  - rewrite (roof_fmap_id F RNeg k); apply id_right.
  - rewrite (roof_fmap_any F k (ZeroNeg : RZero ~{Roof}~> RNeg)).
    reflexivity.
  - rewrite (roof_fmap_id F RZero k); apply id_right.
  - rewrite (roof_fmap_any F k (ZeroPos : RZero ~{Roof}~> RPos)).
    symmetry; exact Hc.
  - rewrite (roof_fmap_id F RPos k); apply id_right.
Qed.

Definition po_cocone (F : Roof ⟶ C) (Q : C)
  (q1 : F RNeg ~> Q) (q2 : F RPos ~> Q)
  (Hc : q1 ∘ span_left F ≈ q2 ∘ span_right F) : Cocone F :=
  @Cocone_of Roof C F Q (po_legs F Q q1 q2) (po_legs_coherence F Q q1 q2 Hc).

Lemma po_inj_ump (F : Roof ⟶ C) (Q : C)
  (q1 : F RNeg ~> Q) (q2 : F RPos ~> Q)
  (Hc : q1 ∘ span_left F ≈ q2 ∘ span_right F) :
  ∃! u : colim_obj M F ~> Q,
    u ∘ colim_inj M F RNeg ≈ q1 ∧ u ∘ colim_inj M F RPos ≈ q2.
Proof.
  unshelve eapply Build_Unique.
  - exact (colim_med M (po_cocone F Q q1 q2 Hc)).
  - split.
    + exact (colim_med_commutes M (po_cocone F Q q1 q2 Hc) RNeg).
    + exact (colim_med_commutes M (po_cocone F Q q1 q2 Hc) RPos).
  - intros v [Hv1 Hv2].
    apply (colim_med_unique M (po_cocone F Q q1 q2 Hc)).
    intro j; destruct j.
    + exact Hv1.
    + rewrite <- (colim_inj_coherence M F
                    (ZeroNeg : RZero ~{Roof}~> RNeg)).
      now rewrite comp_assoc, Hv1.
    + exact Hv2.
Qed.

(* 相关说明。 （已译） *)
Definition po_inj_IsPushoutSquare (F : Roof ⟶ C) :
  IsPushoutSquare (span_left F) (span_right F) (colim_obj M F)
                  (colim_inj M F RNeg) (colim_inj M F RPos) :=
  Build_IsPushoutSquare (po_inj_commutes F) (po_inj_ump F).

(* 相关说明。 （已译） *)
Definition po_unit_IsPushoutSquare (F : Roof ⟶ C) :
  IsPushoutSquare (span_left F) (span_right F) (colim_obj M F)
                  (pushout_inj1 F) (pushout_inj2 F) :=
  IsPushoutSquare_respects (po_inj_IsPushoutSquare F)
    (po_inj_is_in1 F) (po_inj_is_in2 F).

Example aspan_left {S x y : C} (f : S ~> x) (g : S ~> y) :
  span_left (ASpan f g) = f := eq_refl.

Example aspan_right {S x y : C} (f : S ~> x) (g : S ~> y) :
  span_right (ASpan f g) = g := eq_refl.

Definition HasColimitsOfShape_HasPushouts : HasPushouts C :=
  {| pushout := fun x y z f g =>
       is_pushout_square_pushout (po_unit_IsPushoutSquare (ASpan f g)) |}.

Definition po_counit_iso (x : C) : colim_obj M (Δ[Roof](x)) ≅ x :=
  dia_counit_iso M RZero Roof_linked x.

End PushoutRow.

(* 相关说明。 （已译） *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Degenerate.

Context {C : Category}.

(* A pair whose two legs agree equalized 同构 onto the
 common domain: 恒等 forks such pair, equalizing
 arrow monic. （已译） *)
Definition equalizer_of_equal_pair {x y : C} (f : x ~> y) {q : C}
  {e : q ~> x} (E : IsEqualizer f f q e) : q ≅ x.
Proof.
  assert (Hf : f ∘ id[x] ≈ f ∘ id[x]) by reflexivity.
  pose proof (eq_desc E (id[x]) Hf) as D.
  unshelve refine {| to := e; from := unique_obj D |}.
  - exact (unique_property D).
  - apply (@monic _ _ _ e (equalizer_monic f f E)).
    rewrite comp_assoc, (unique_property D), id_left, id_right.
    reflexivity.
Defined.

(* Dually, a pair whose two legs agree is coequalized by an isomorphism
   onto the common codomain. *)
Definition coequalizer_of_equal_pair {x y : C} (f : x ~> y) {q : C}
  {e : y ~> q} (E : IsCoequalizer f f q e) : q ≅ y.
Proof.
  assert (Hf : id[y] ∘ f ≈ id[y] ∘ f) by reflexivity.
  pose proof (coeq_desc E (id[y]) Hf) as D.
  unshelve refine {| to := unique_obj D; from := e |}.
  - exact (unique_property D).
  - apply (@epic _ _ _ e (coequalizer_epic f f E)).
    rewrite <- comp_assoc, (unique_property D), id_left, id_right.
    reflexivity.
Defined.

(* The pullback cospan one whose legs 恒等 the
 domain other leg, projected second projection. （已译） *)
Definition pullback_of_identity {y z P : C} (g : y ~> z)
  {p1 : P ~> z} {p2 : P ~> y} (H : IsPullback (id[z]) g P p1 p2) : P ≅ y.
Proof.
  assert (Hc : id[z] ∘ g ≈ g ∘ id[y]).
  { rewrite id_left, id_right; reflexivity. }
  pose proof (is_pullback_ump H y g (id[y]) Hc) as D.
  pose proof (is_pullback_ump H P p1 p2 (is_pullback_commutes H)) as DP.
  unshelve refine {| to := p2; from := unique_obj D |}.
  - exact (snd (unique_property D)).
  - transitivity (unique_obj DP).
    + symmetry.
      apply (uniqueness DP); split.
      * rewrite comp_assoc, (fst (unique_property D)).
        rewrite <- (is_pullback_commutes H).
        apply id_left.
      * rewrite comp_assoc, (snd (unique_property D)).
        apply id_left.
    + apply (uniqueness DP); split; apply id_right.
Defined.

(* Dually, pushout span one whose legs 恒等 the
 codomain other leg, injected second injection. （已译） *)
Definition pushout_of_identity {x z P : C} (g : x ~> z)
  {i1 : x ~> P} {i2 : z ~> P} (H : IsPushoutSquare (id[x]) g P i1 i2) :
  P ≅ z.
Proof.
  assert (Hc : g ∘ id[x] ≈ id[z] ∘ g).
  { rewrite id_left, id_right; reflexivity. }
  pose proof (is_pushout_square_ump H z g (id[z]) Hc) as D.
  pose proof (is_pushout_square_ump H P i1 i2
                (is_pushout_square_commutes H)) as DP.
  unshelve refine {| to := unique_obj D; from := i2 |}.
  - exact (snd (unique_property D)).
  - transitivity (unique_obj DP).
    + symmetry.
      apply (uniqueness DP); split.
      * rewrite <- comp_assoc, (fst (unique_property D)).
        rewrite <- (is_pushout_square_commutes H).
        apply id_right.
      * rewrite <- comp_assoc, (snd (unique_property D)).
        apply id_right.
    + apply (uniqueness DP); split; apply id_left.
Defined.

End Degenerate.

(* 相关说明。 （已译） *)

Definition SetsEq : HasLimitsOfShape Parallel Sets :=
  Sets_HasLimitsOfShape Parallel.

Definition SetsParallelColim : HasColimitsOfShape Parallel Sets :=
  Sets_HasColimitsOfShape Parallel.

Definition SetsPb : HasLimitsOfShape (Roof^op) Sets :=
  Sets_HasLimitsOfShape (Roof^op).

Definition SetsPo : HasColimitsOfShape Roof Sets :=
  Sets_HasColimitsOfShape Roof.

Definition Sets_Diagonal_Equalizer_Adjunction :
  @Diagonal Sets Parallel ⊣ EqualizerFunctor SetsEq :=
  Diagonal_Equalizer_Adjunction SetsEq.

Definition Sets_Coequalizer_Diagonal_Adjunction :
  CoequalizerFunctor SetsParallelColim ⊣ @Diagonal Sets Parallel :=
  Coequalizer_Diagonal_Adjunction SetsParallelColim.

Definition Sets_Diagonal_Pullback_Adjunction :
  @Diagonal Sets (Roof^op) ⊣ PullbackFunctor SetsPb :=
  Diagonal_Pullback_Adjunction SetsPb.

Definition Sets_Pushout_Diagonal_Adjunction :
  PushoutFunctor SetsPo ⊣ @Diagonal Sets Roof :=
  Pushout_Diagonal_Adjunction SetsPo.

(* 相关说明。 （已译） *)

Definition DiagSets_HasEqualizers : HasEqualizers Sets :=
  HasLimitsOfShape_HasEqualizers SetsEq.

Definition DiagSets_HasCoequalizers : HasCoequalizers Sets :=
  HasColimitsOfShape_HasCoequalizers SetsParallelColim.

Definition Sets_HasPullbacks_of_shape : HasPullbacks Sets :=
  HasLimitsOfShape_HasPullbacks SetsPb.

Definition Sets_HasPushouts_of_shape : HasPushouts Sets :=
  HasColimitsOfShape_HasPushouts SetsPo.

(* * ** A concrete, non-常值 diagram （已译） *)

(* The 常值 map at [true] two-element discrete setoid. Nothing
 below 常值 DIAGRAM: [SetsConstTrue] not 恒等, which
 what [sets_const_true_not_id] records. （已译） *)
Program Definition SetsConstTrue : DiagBoolSet ~{Sets}~> DiagBoolSet := {|
  morphism := fun _ => true
|}.

Lemma sets_const_true_not_id : SetsConstTrue ≈ id[DiagBoolSet] → False.
Proof. intro H; discriminate (H false). Qed.

Definition SetsPairDiagram : Parallel ⟶ Sets :=
  APair SetsConstTrue SetsConstTrue.

Lemma SetsPairDiagram_not_constant :
  fmap[SetsPairDiagram] ((true; ParOne) : ParX ~{Parallel}~> ParY)
    ≈ id[DiagBoolSet] → False.
Proof. exact sets_const_true_not_id. Qed.

Definition SetsCospanDiagram : Roof^op ⟶ Sets :=
  ACospan (id[DiagBoolSet]) SetsConstTrue.

Lemma SetsCospanDiagram_not_constant :
  fmap[SetsCospanDiagram] (ZeroPos : RPos ~{Roof^op}~> RZero)
    ≈ id[DiagBoolSet] → False.
Proof. exact sets_const_true_not_id. Qed.

Definition SetsSpanDiagram : Roof ⟶ Sets :=
  ASpan (id[DiagBoolSet]) SetsConstTrue.

Lemma SetsSpanDiagram_not_constant :
  fmap[SetsSpanDiagram] (ZeroPos : RZero ~{Roof}~> RPos)
    ≈ id[DiagBoolSet] → False.
Proof. exact sets_const_true_not_id. Qed.

(* * ** The four 对象 computed, each proved not subsingleton （已译） *)

Lemma sets_two_elements_of_iso {X : Sets} (i : X ≅ DiagBoolSet) :
  { a : carrier X & { b : carrier X & a ≈ b → False } }.
Proof.
  exists (from i true).
  exists (from i false).
  intro H.
  pose proof (iso_to_from i true) as H1.
  pose proof (iso_to_from i false) as H2.
  simpl in H1, H2.
  assert (Hb : (true : carrier DiagBoolSet) ≈ false).
  { transitivity (to i (from i true)).
    - symmetry; exact H1.
    - transitivity (to i (from i false)).
      + apply (proper_morphism (to i)); exact H.
      + exact H2. }
  discriminate Hb.
Qed.

Definition sets_equalizer_iso :
  lim_obj SetsEq SetsPairDiagram ≅ DiagBoolSet :=
  equalizer_of_equal_pair SetsConstTrue
    (eq_counit_IsEqualizer SetsEq SetsConstTrue SetsConstTrue).

Definition sets_coequalizer_iso :
  colim_obj SetsParallelColim SetsPairDiagram ≅ DiagBoolSet :=
  coequalizer_of_equal_pair SetsConstTrue
    (coeq_unit_IsCoequalizer SetsParallelColim SetsConstTrue SetsConstTrue).

Definition sets_pullback_iso :
  lim_obj SetsPb SetsCospanDiagram ≅ DiagBoolSet :=
  pullback_of_identity SetsConstTrue
    (pb_counit_IsPullback SetsPb SetsCospanDiagram).

Definition sets_pushout_iso :
  colim_obj SetsPo SetsSpanDiagram ≅ DiagBoolSet :=
  pushout_of_identity SetsConstTrue
    (po_unit_IsPushoutSquare SetsPo SetsSpanDiagram).

Definition sets_equalizer_two_elements :
  { a : carrier (lim_obj SetsEq SetsPairDiagram)
  & { b : carrier (lim_obj SetsEq SetsPairDiagram) & a ≈ b → False } } :=
  sets_two_elements_of_iso sets_equalizer_iso.

Definition sets_coequalizer_two_elements :
  { a : carrier (colim_obj SetsParallelColim SetsPairDiagram)
  & { b : carrier (colim_obj SetsParallelColim SetsPairDiagram)
    & a ≈ b → False } } :=
  sets_two_elements_of_iso sets_coequalizer_iso.

Definition sets_pullback_two_elements :
  { a : carrier (lim_obj SetsPb SetsCospanDiagram)
  & { b : carrier (lim_obj SetsPb SetsCospanDiagram) & a ≈ b → False } } :=
  sets_two_elements_of_iso sets_pullback_iso.

Definition sets_pushout_two_elements :
  { a : carrier (colim_obj SetsPo SetsSpanDiagram)
  & { b : carrier (colim_obj SetsPo SetsSpanDiagram) & a ≈ b → False } } :=
  sets_two_elements_of_iso sets_pushout_iso.

(* 相关说明。 （已译） *)

Example sets_pair_arrow_strict :
  fmap[SetsPairDiagram] ((true; ParOne) : ParX ~{Parallel}~> ParY)
    = SetsConstTrue := eq_refl.

Example sets_cospan_arrow_strict :
  fmap[SetsCospanDiagram] (ZeroPos : RPos ~{Roof^op}~> RZero)
    = SetsConstTrue := eq_refl.

Example sets_span_arrow_strict :
  fmap[SetsSpanDiagram] (ZeroPos : RZero ~{Roof}~> RPos)
    = SetsConstTrue := eq_refl.

(* * * Readbacks four rows against 伴随 （已译） *)

Section Readbacks.

Context {C : Category}.

Example eq_row_counit (L : HasLimitsOfShape Parallel C)
  (F : Parallel ⟶ C) :
  @counit ([Parallel, C]) C (@Diagonal C Parallel) (EqualizerFunctor L)
          (Diagonal_Equalizer_Adjunction L) F = eq_counit L F := eq_refl.

Example coeq_row_unit (M : HasColimitsOfShape Parallel C)
  (F : Parallel ⟶ C) :
  @unit C ([Parallel, C]) (CoequalizerFunctor M) (@Diagonal C Parallel)
        (Coequalizer_Diagonal_Adjunction M) F = coeq_unit M F := eq_refl.

Example pb_row_counit (L : HasLimitsOfShape (Roof^op) C)
  (F : Roof^op ⟶ C) :
  @counit ([Roof^op, C]) C (@Diagonal C (Roof^op)) (PullbackFunctor L)
          (Diagonal_Pullback_Adjunction L) F = pb_counit L F := eq_refl.

Example po_row_unit (M : HasColimitsOfShape Roof C) (F : Roof ⟶ C) :
  @unit C ([Roof, C]) (PushoutFunctor M) (@Diagonal C Roof)
        (Pushout_Diagonal_Adjunction M) F = po_unit M F := eq_refl.

(* The four 函子' 对象 actions four (co)limit 对象. （已译） *)

Example EqualizerFunctor_obj (L : HasLimitsOfShape Parallel C)
  {x y : C} (f g : x ~> y) :
  fobj[EqualizerFunctor L] (APair f g) = lim_obj L (APair f g) := eq_refl.

Example CoequalizerFunctor_obj (M : HasColimitsOfShape Parallel C)
  {x y : C} (f g : x ~> y) :
  fobj[CoequalizerFunctor M] (APair f g) = colim_obj M (APair f g) := eq_refl.

Example PullbackFunctor_obj (L : HasLimitsOfShape (Roof^op) C)
  {x y z : C} (f : x ~> z) (g : y ~> z) :
  fobj[PullbackFunctor L] (ACospan f g) = lim_obj L (ACospan f g) := eq_refl.

Example PushoutFunctor_obj (M : HasColimitsOfShape Roof C)
  {S x y : C} (f : S ~> x) (g : S ~> y) :
  fobj[PushoutFunctor M] (ASpan f g) = colim_obj M (ASpan f g) := eq_refl.

(* The chosen (co)limit elementary classes built above the
 (co)limit 对象 corresponding diagram, nose. （已译） *)

Example HasEqualizers_apex (L : HasLimitsOfShape Parallel C)
  {x y : C} (f g : x ~> y) :
  projT1 (@equalizer C (HasLimitsOfShape_HasEqualizers L) x y f g)
    = lim_obj L (APair f g) := eq_refl.

Example HasCoequalizers_apex (M : HasColimitsOfShape Parallel C)
  {x y : C} (f g : x ~> y) :
  projT1 (@coeq C (HasColimitsOfShape_HasCoequalizers M) x y f g)
    = colim_obj M (APair f g) := eq_refl.

Example HasPullbacks_apex (L : HasLimitsOfShape (Roof^op) C)
  {x y z : C} (f : x ~> z) (g : y ~> z) :
  Pull f g (@pullback C (HasLimitsOfShape_HasPullbacks L) x y z f g)
    = lim_obj L (ACospan f g) := eq_refl.

Example HasPushouts_apex (M : HasColimitsOfShape Roof C)
  {x y z : C} (f : x ~> y) (g : x ~> z) :
  pushout_apex (@pushout C (HasColimitsOfShape_HasPushouts M) x y z f g)
    = colim_obj M (ASpan f g) := eq_refl.

End Readbacks.

(* 相关说明。 （已译） *)

Section Biconditionals.

Context (C : Category).

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition equalizers_iff_diagonal_right_adjoint :
  HasLimitsOfShape Parallel C
    ↔ { R : [Parallel, C] ⟶ C & @Diagonal C Parallel ⊣ R } :=
  limits_iff_diagonal_right_adjoint Parallel C.

Definition coequalizers_iff_diagonal_left_adjoint :
  HasColimitsOfShape Parallel C
    ↔ { K : [Parallel, C] ⟶ C & K ⊣ @Diagonal C Parallel } :=
  colimits_iff_diagonal_left_adjoint Parallel C.

Definition pullbacks_iff_diagonal_right_adjoint :
  HasLimitsOfShape (Roof^op) C
    ↔ { R : [Roof^op, C] ⟶ C & @Diagonal C (Roof^op) ⊣ R } :=
  limits_iff_diagonal_right_adjoint (Roof^op) C.

Definition pushouts_iff_diagonal_left_adjoint :
  HasColimitsOfShape Roof C
    ↔ { K : [Roof, C] ⟶ C & K ⊣ @Diagonal C Roof } :=
  colimits_iff_diagonal_left_adjoint Roof C.

(*
   本节说明函子、（余）极限、拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example cospan_is_pullback_shape : obj[[Roof^op, C]] = Cospan C := eq_refl.

Example span_is_pushout_shape : obj[[Roof, C]] = Span C := eq_refl.

Example pullback_shape_hypothesis :
  HasLimitsOfShape (Roof^op) C = (∀ F : Cospan C, Pullback_Limit F)
  := eq_refl.

Example pushout_shape_hypothesis :
  HasColimitsOfShape Roof C = (∀ F : Span C, Pushout_Limit F) := eq_refl.

(* The two Parallel rows likewise land on Structure/Equalizer.v's own
   aliases. *)

Example equalizer_shape_hypothesis :
  HasLimitsOfShape Parallel C = (∀ F : Parallel ⟶ C, Equalizer F) := eq_refl.

Example coequalizer_shape_hypothesis :
  HasColimitsOfShape Parallel C = (∀ F : Parallel ⟶ C, Coequalizer F)
  := eq_refl.

End Biconditionals.
