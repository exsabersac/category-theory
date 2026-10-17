Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Equalizer.
Require Import Category.Instance.Parallel.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Coequaliser

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The elementary 普遍性质: e coforks pair f, g at q, and
 every coforking map h out y descends uniquely across e. （已译） *)
Record IsCoequalizer {C : Category} {x y : C} (f g : x ~> y)
  (q : C) (e : y ~> q) := {
  (* 相关说明。 （已译） *)
  cofork : e ∘ f ≈ e ∘ g;

  (* universal property: every coforking map h descends uniquely through e *)
  coeq_desc {z} (h : y ~> z) (Hh : h ∘ f ≈ h ∘ g) :
    ∃! u : q ~> z, u ∘ e ≈ h
}.

Arguments cofork {_ _ _ _ _ _ _} _.
Arguments coeq_desc {_ _ _ _ _ _ _} _ {_} _ _.

(* A 范畴 has all (binary) coequalizers every parallel pair
 carries elementary coequalizer. This coequalizer analogue of
 [HasPullbacks] [Structure/Pullback.v]. （已译） *)
Class HasCoequalizers (C : Category) := {
  coeq {x y : C} (f g : x ~> y) : ∃ (q : C) (e : y ~> q), IsCoequalizer f g q e
}.

Section CoequalizerColimit.

Context {C : Category}.
Context {x y : C}.
Context (f g : x ~> y).

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Lemma coequalizer_epic {q : C} {e : y ~> q} (E : IsCoequalizer f g q e) :
  Epic e.
Proof.
  constructor.
  intros z g1 g2 Hg.
  assert (Hfork : (g1 ∘ e) ∘ f ≈ (g1 ∘ e) ∘ g).
  { rewrite <- !comp_assoc.
    rewrite (cofork E).
    reflexivity. }
  transitivity (unique_obj (coeq_desc E (g1 ∘ e) Hfork)).
  - symmetry.
    apply (uniqueness (coeq_desc E (g1 ∘ e) Hfork)).
    reflexivity.
  - apply (uniqueness (coeq_desc E (g1 ∘ e) Hfork)).
    symmetry.
    exact Hg.
Qed.

(* * ** Coequalizers unique up 同构 （已译） *)

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma coequalizer_unique {q1 q2 : C} {e1 : y ~> q1} {e2 : y ~> q2}
  (E1 : IsCoequalizer f g q1 e1) (E2 : IsCoequalizer f g q2 e2) :
  q1 ≅ q2.
Proof.
  pose proof (coeq_desc E1 e2 (cofork E2)) as D12.
  pose proof (coeq_desc E2 e1 (cofork E1)) as D21.
  pose proof (coeq_desc E1 e1 (cofork E1)) as D11.
  pose proof (coeq_desc E2 e2 (cofork E2)) as D22.
  unshelve refine {| to := unique_obj D12; from := unique_obj D21 |}.
  - (* to ∘ from ≈ id[q2], by uniqueness of descent against D22 *)
    transitivity (unique_obj D22).
    + symmetry.
      apply (uniqueness D22).
      rewrite <- comp_assoc.
      rewrite (unique_property D21).
      exact (unique_property D12).
    + apply (uniqueness D22).
      apply id_left.
  - (* from ∘ to ≈ id[q1], by uniqueness of descent against D11 *)
    transitivity (unique_obj D11).
    + symmetry.
      apply (uniqueness D11).
      rewrite <- comp_assoc.
      rewrite (unique_property D12).
      exact (unique_property D21).
    + apply (uniqueness D11).
      apply id_left.
Qed.

(* 相关说明。 （已译） *)

(* The legs cocone induced coforking map h: leg over ParX
 common 复合 h ∘ f, leg over ParY h itself. （已译） *)
Definition cofork_legs {z : C} (h : y ~> z) (p : ParObj) :
  APair f g p ~{C}~> z :=
  match p return (APair f g p ~{C}~> z) with
  | ParX => h ∘ f
  | ParY => h
  end.

(*
   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma cofork_legs_coherence {z : C} (h : y ~> z) (Hh : h ∘ f ≈ h ∘ g) :
  ∀ (a b : ParObj) (k : b ~{Parallel}~> a),
    cofork_legs h a ∘ fmap[APair f g] k ≈ cofork_legs h b.
Proof.
  intros a b k.
  destruct a, b.
  - (* identity arrow on ParX *)
    simpl.
    apply id_right.
  - (* an arrow ParY ~> ParX: refuted *)
    destruct k as [bb hk].
    destruct (ParHom_Y_X_absurd _ hk).
  - (* 相关说明。 （已译） *)
    destruct k as [bb hk].
    destruct bb.
    + (* (true; ParOne), sent to f *)
      reflexivity.
    + (* (false; ParTwo), sent to g *)
      symmetry.
      exact Hh.
  - (* identity arrow on ParY *)
    simpl.
    apply id_right.
Qed.

(* The cocone over APair f g induced by a coforking map. *)
Definition cofork_cocone {z : C} (h : y ~> z) (Hh : h ∘ f ≈ h ∘ g) :
  Cocone (APair f g) :=
  @Build_Cone (Parallel^op) (C^op) ((APair f g)^op) z
    (@Build_ACone (Parallel^op) (C^op) z ((APair f g)^op)
       (cofork_legs h) (cofork_legs_coherence h Hh)).

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Lemma colimit_coequalizes (L : Coequalizer (APair f g)) :
  colimit_inj (colimit_is_acolimit L) ParY ∘ f
    ≈ colimit_inj (colimit_is_acolimit L) ParY ∘ g.
Proof.
  transitivity (colimit_inj (colimit_is_acolimit L) ParX).
  - exact (colimit_inj_coherence (colimit_is_acolimit L)
             ((true; ParOne) : ParX ~{Parallel}~> ParY)).
  - symmetry.
    exact (colimit_inj_coherence (colimit_is_acolimit L)
             ((false; ParTwo) : ParX ~{Parallel}~> ParY)).
Qed.

(* Descent through colimit apex: mediate out colimit 进入
 cocone induced coforking map. （已译） *)
Lemma colimit_coequalizer_desc (L : Coequalizer (APair f g))
  {z : C} (h : y ~> z) (Hh : h ∘ f ≈ h ∘ g) :
  ∃! u : colimit_apex L ~> z,
    u ∘ colimit_inj (colimit_is_acolimit L) ParY ≈ h.
Proof.
  unshelve eapply Build_Unique.
  - exact (colimit_med (colimit_is_acolimit L) (cofork_cocone h Hh)).
  - exact (colimit_med_commutes
             (colimit_is_acolimit L) (cofork_cocone h Hh) ParY).
  - intros v Hv.
    refine (colimit_med_unique
              (colimit_is_acolimit L) (cofork_cocone h Hh) v _).
    intros p.
    destruct p.
    + (* 相关说明。 （已译） *)
      rewrite <- (colimit_inj_coherence (colimit_is_acolimit L)
                    ((true; ParOne) : ParX ~{Parallel}~> ParY)).
      rewrite comp_assoc.
      rewrite Hv.
      reflexivity.
    + exact Hv.
Qed.

(* A colimit of APair f g is an elementary coequalizer at its apex. *)
Definition coequalizer_is_coequalizer (L : Coequalizer (APair f g)) :
  IsCoequalizer f g (colimit_apex L)
    (colimit_inj (colimit_is_acolimit L) ParY) :=
  {| cofork    := colimit_coequalizes L
   ; coeq_desc := fun z h Hh => colimit_coequalizer_desc L h Hh |}.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition is_coequalizer_cocone {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) : Cocone (APair f g) :=
  cofork_cocone e (cofork E).

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma is_coequalizer_cocone_ump {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) (N : Cocone (APair f g)) :
  ∃! u : q ~> vertex_obj[N],
    ∀ p : ParObj, u ∘ cofork_legs e p ≈ cocone_inj N p.
Proof.
  assert (HX1 : cocone_inj N ParY ∘ f ≈ cocone_inj N ParX).
  { exact (cocone_inj_coherence N
             ((true; ParOne) : ParX ~{Parallel}~> ParY)). }
  assert (HX2 : cocone_inj N ParY ∘ g ≈ cocone_inj N ParX).
  { exact (cocone_inj_coherence N
             ((false; ParTwo) : ParX ~{Parallel}~> ParY)). }
  assert (Hfg : cocone_inj N ParY ∘ f ≈ cocone_inj N ParY ∘ g).
  { rewrite HX1.
    rewrite HX2.
    reflexivity. }
  unshelve eapply Build_Unique.
  - exact (unique_obj (coeq_desc E (cocone_inj N ParY) Hfg)).
  - intros p.
    destruct p.
    + (* leg over ParX: u ∘ (e ∘ f) ≈ nX via the ParY triangle *)
      simpl.
      rewrite comp_assoc.
      rewrite (unique_property (coeq_desc E (cocone_inj N ParY) Hfg)).
      exact HX1.
    + exact (unique_property (coeq_desc E (cocone_inj N ParY) Hfg)).
  - intros v Hv.
    apply (uniqueness (coeq_desc E (cocone_inj N ParY) Hfg)).
    exact (Hv ParY).
Qed.

(* 相关说明。 （已译） *)
Definition is_coequalizer_colimit {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) : Coequalizer (APair f g) :=
  {| limit_cone := is_coequalizer_cocone E
   ; ump_limits := fun N => is_coequalizer_cocone_ump E N |}.

End CoequalizerColimit.

(* 相关说明。 （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ParallelDiagram.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Universes co ch po.
Context {C : Category@{co ch ch}}.
Context (K : Parallel@{po ch} ⟶ C).

(* 相关说明。 （已译） *)

Local Notation par1 := (fmap[K] ((true; ParOne) : ParX ~{Parallel}~> ParY)).
Local Notation par2 := (fmap[K] ((false; ParTwo) : ParX ~{Parallel}~> ParY)).

Definition parallel_cofork_legs {z : C} (h : K ParY ~> z) (p : ParObj) :
  K p ~> z :=
  match p return (K p ~> z) with
  | ParX => h ∘ par1
  | ParY => h
  end.

Lemma parallel_cofork_legs_coherence {z : C} (h : K ParY ~> z)
  (Hh : h ∘ par1 ≈ h ∘ par2) :
  ∀ (a b : ParObj) (k : b ~{Parallel}~> a),
    parallel_cofork_legs h a ∘ fmap[K] k ≈ parallel_cofork_legs h b.
Proof.
  intros a b k.
  destruct a, b.
  - (* an endomorphism of ParX: the identity *)
    destruct k as [[|] hk].
    + transitivity (parallel_cofork_legs h ParX ∘ id).
      * apply compose_respects; [reflexivity|].
        rewrite <- fmap_id.
        apply fmap_respects.
        reflexivity.
      * apply id_right.
    + destruct (ParHom_Id_false_absurd _ hk).
  - (* an arrow ParY ~> ParX: refuted *)
    destruct k as [bb hk].
    destruct (ParHom_Y_X_absurd _ hk).
  - (* the two arrows ParX ~> ParY *)
    destruct k as [[|] hk]; simpl.
    + apply compose_respects; [reflexivity|].
      apply fmap_respects.
      reflexivity.
    + symmetry.
      rewrite Hh.
      apply compose_respects; [reflexivity|].
      apply fmap_respects.
      reflexivity.
  - (* an endomorphism of ParY: the identity *)
    destruct k as [[|] hk].
    + transitivity (parallel_cofork_legs h ParY ∘ id).
      * apply compose_respects; [reflexivity|].
        rewrite <- fmap_id.
        apply fmap_respects.
        reflexivity.
      * apply id_right.
    + destruct (ParHom_Id_false_absurd _ hk).
Qed.

(* 相关说明。 （已译） *)

Definition parallel_cofork_cocone {z : C} (h : K ParY ~> z)
  (Hh : h ∘ par1 ≈ h ∘ par2) : Cocone K :=
  @Build_Cone (Parallel^op) (C^op) (K^op) z
    (@Build_ACone (Parallel^op) (C^op) z (K^op)
       (parallel_cofork_legs h) (parallel_cofork_legs_coherence h Hh)).

(* An elementary coequalizer of the pair is a colimiting cocone over K. *)

Definition parallel_coequalizer_colimit {q : C} {e : K ParY ~> q}
  (E : IsCoequalizer par1 par2 q e) :
  IsColimitCocone (parallel_cofork_cocone e (cofork E)).
Proof.
  intro M.
  assert (HX1 : cocone_inj M ParY ∘ par1 ≈ cocone_inj M ParX).
  { exact (cocone_inj_coherence M
             ((true; ParOne) : ParX ~{Parallel}~> ParY)). }
  assert (HX2 : cocone_inj M ParY ∘ par2 ≈ cocone_inj M ParX).
  { exact (cocone_inj_coherence M
             ((false; ParTwo) : ParX ~{Parallel}~> ParY)). }
  assert (Hfg : cocone_inj M ParY ∘ par1 ≈ cocone_inj M ParY ∘ par2).
  { rewrite HX1, HX2.
    reflexivity. }
  unshelve eapply Build_Unique.
  - exact (unique_obj (coeq_desc E (cocone_inj M ParY) Hfg)).
  - intro p; destruct p.
    + (* the injection over ParX is e ∘ par1 *)
      change (unique_obj (coeq_desc E (cocone_inj M ParY) Hfg) ∘ (e ∘ par1)
                ≈ cocone_inj M ParX).
      rewrite comp_assoc.
      rewrite (unique_property (coeq_desc E (cocone_inj M ParY) Hfg)).
      exact HX1.
    + exact (unique_property (coeq_desc E (cocone_inj M ParY) Hfg)).
  - intros v Hv.
    apply (uniqueness (coeq_desc E (cocone_inj M ParY) Hfg)).
    exact (Hv ParY).
Defined.

(* ANY colimiting cocone over K is an elementary coequalizer of the pair
   at its apex, coequalized by its injection over ParY. *)

Definition parallel_colimit_coequalizer (N : Cocone K)
  (HN : IsColimitCocone N) :
  IsCoequalizer par1 par2 vertex_obj[N] (cocone_inj N ParY).
Proof.
  unshelve econstructor.
  - (* 相关说明。 （已译） *)
    transitivity (cocone_inj N ParX).
    + exact (cocone_inj_coherence N
               ((true; ParOne) : ParX ~{Parallel}~> ParY)).
    + symmetry.
      exact (cocone_inj_coherence N
               ((false; ParTwo) : ParX ~{Parallel}~> ParY)).
  - intros z h Hh.
    pose (U := colimitcocone_ump HN (parallel_cofork_cocone h Hh)).
    unshelve eapply Build_Unique.
    + exact (unique_obj U).
    + exact (unique_property U ParY).
    + intros v Hv.
      apply (uniqueness U).
      intro p; destruct p.
      * (* 相关说明。 （已译） *)
        change (v ∘ cocone_inj N ParX ≈ h ∘ par1).
        rewrite <- (cocone_inj_coherence N
                      ((true; ParOne) : ParX ~{Parallel}~> ParY)).
        rewrite comp_assoc, Hv.
        reflexivity.
      * exact Hv.
Defined.

(*
   本节说明（余）极限、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition parallel_cocone_coequalizer_colimit (N : Cocone K)
  (E : IsCoequalizer par1 par2 vertex_obj[N] (cocone_inj N ParY)) :
  IsColimitCocone N.
Proof.
  refine (limitcone_transport _ (parallel_coequalizer_colimit E)).
  exists (@iso_id (C^op) vertex_obj[N]).
  intro p; destruct p.
  - (* over ParX, by coherence *)
    change (id ∘ cocone_inj N ParX ≈ cocone_inj N ParY ∘ par1).
    rewrite id_left.
    symmetry.
    exact (cocone_inj_coherence N
             ((true; ParOne) : ParX ~{Parallel}~> ParY)).
  - (* over ParY, one arrow *)
    change (id ∘ cocone_inj N ParY ≈ cocone_inj N ParY).
    apply id_left.
Defined.

End ParallelDiagram.

(*
   本节说明伴随、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition HasCoequalizers_HasColimitsOfShape {C : Category}
  (HC : HasCoequalizers C) : ∀ F : Parallel ⟶ C, Colimit F :=
  fun F =>
    let P := coeq (fmap[F] ((true; ParOne) : ParX ~{Parallel}~> ParY))
                  (fmap[F] ((false; ParTwo) : ParX ~{Parallel}~> ParY)) in
    {| limit_cone := parallel_cofork_cocone F (`1 (`2 P)) (cofork (`2 (`2 P)));
       ump_limits := parallel_coequalizer_colimit F (`2 (`2 P)) |}.
