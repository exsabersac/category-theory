Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Construction.Product.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.One.

Generalizable All Variables.

(*
    nLab: https://ncatlab.org/nlab/show/Kan+extension

   本文件给出 Kan 扩张相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(* 相关说明。 （已译） *)

Section PointwiseRan.

Context {A : Category}.
Context {B : Category}.
Context {F : A ⟶ B}.
Context {C : Category}.
Context (X : A ⟶ C).

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ran_comma_diagram (b : B) : (=(b) ↓ F) ⟶ C :=
  X ◯ @comma_proj2 _ _ _ =(b) F.

(* The pointwise hypothesis: each comma diagram has a limit. *)
Context (lim : ∀ b : B, Limit (ran_comma_diagram b)).

Definition ran_obj (b : B) : C := vertex_obj[(@limit_cone _ _ _ (lim b))].

Definition ran_leg {b : B} (x : =(b) ↓ F) :
  ran_obj b ~{C}~> ran_comma_diagram b x :=
  @vertex_map _ _ _ _ (@coneFrom _ _ _ ((@limit_cone _ _ _ (lim b)))) x.

Lemma ran_leg_coherence {b : B} {x y : =(b) ↓ F} (f : x ~{=(b) ↓ F}~> y) :
  fmap[ran_comma_diagram b] f ∘ ran_leg x ≈ ran_leg y.
Proof.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ ((@limit_cone _ _ _ (lim b)))) x y f).
Qed.

(* Legs transport along ≈-equality comma component: (id, id) a
 comma 态射 (a, f) ~> (a, f') whenever f ≈ f', diagram sends
 it fmap[X] id ≈ id. （已译） *)
Lemma ran_leg_transport {b : B} (t : (1 ∏ A)%category) (f f' : b ~> F (snd t)) :
  f ≈ f' →
  ran_leg (existT _ t f) ≈ ran_leg (existT _ t f').
Proof.
  intro Hf.
  assert (sq : f' ∘ fmap[=(b)] (@id 1 (fst t)) ≈ fmap[F] (@id A (snd t)) ∘ f).
  { simpl.
    rewrite fmap_id, id_left, id_right.
    now symmetry. }
  rewrite <- (ran_leg_coherence
                ((((ttt, @id A (snd t)); sq))
                   : existT (fun p : (1 ∏ A)%category => b ~> F (snd p)) t f
                       ~{=(b) ↓ F}~> existT _ t f')).
  simpl.
  now rewrite fmap_id, id_left.
Qed.

(* 相关说明。 （已译） *)
Program Definition ran_probe_cone {b : B} {c : C} (u : c ~> ran_obj b) :
  Cone (ran_comma_diagram b) :=
  @Build_Cone (=(b) ↓ F) C (ran_comma_diagram b) c
    (@Build_ACone (=(b) ↓ F) C c (ran_comma_diagram b)
       (fun x => ran_leg x ∘ u) _).
Next Obligation.
  intros b c u x y f; simpl.
  rewrite comp_assoc.
  now rewrite (ran_leg_coherence f).
Qed.

Lemma ran_jointly_monic {b : B} {c : C} (u v : c ~> ran_obj b) :
  (∀ x : =(b) ↓ F, ran_leg x ∘ u ≈ ran_leg x ∘ v) →
  u ≈ v.
Proof.
  intro H.
  destruct (@ump_limits _ _ _ (lim b) (ran_probe_cone u)) as [w Hw Huniq].
  transitivity w.
  - symmetry; apply Huniq; intro x; reflexivity.
  - apply Huniq; intro x; symmetry; apply H.
Qed.

(* * *** Reindexing, extension 函子 （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition ran_reindex {b b' : B} (g : b ~> b') :
  (=(b') ↓ F) ⟶ (=(b) ↓ F) := {|
  fobj := fun x => existT _ (`1 x) (`2 x ∘ g);
  fmap := fun x y f => (`1 f; _)
|}.
Next Obligation.
  intros b b' g x y f.
  destruct f as [[u v] sq]; simpl in *.
  rewrite id_right in sq.
  rewrite id_right.
  rewrite comp_assoc.
  now rewrite <- sq.
Qed.
Next Obligation.
  intros b b' g x y f f' [e1 e2]; simpl.
  split; assumption.
Qed.
Next Obligation.
  intros b b' g x; simpl.
  split; reflexivity.
Qed.
Next Obligation.
  intros b b' g x y z f f'; simpl.
  split; reflexivity.
Qed.

(* The restricted cone: b-limit's legs at reindexed 对象 form a
 cone over b'-diagram (the two composites agree definitionally). （已译） *)
Program Definition ran_restrict_cone {b b' : B} (g : b ~> b') :
  Cone (ran_comma_diagram b') :=
  @Build_Cone (=(b') ↓ F) C (ran_comma_diagram b') (ran_obj b)
    (@Build_ACone (=(b') ↓ F) C (ran_obj b) (ran_comma_diagram b')
       (fun x => ran_leg (ran_reindex g x)) _).
Next Obligation.
  intros b b' g x y f; simpl.
  exact (ran_leg_coherence (fmap[ran_reindex g] f)).
Qed.

Definition ran_fmap {b b' : B} (g : b ~> b') : ran_obj b ~> ran_obj b' :=
  unique_obj (@ump_limits _ _ _ (lim b') (ran_restrict_cone g)).

Lemma ran_fmap_leg {b b' : B} (g : b ~> b') (x : =(b') ↓ F) :
  ran_leg x ∘ ran_fmap g ≈ ran_leg (ran_reindex g x).
Proof.
  exact (unique_property (@ump_limits _ _ _ (lim b') (ran_restrict_cone g)) x).
Qed.

Program Definition Pointwise_Ran : B ⟶ C := {|
  fobj := ran_obj;
  fmap := fun b b' g => ran_fmap g
|}.
Next Obligation.
  intros b b' g g' Hg.
  apply ran_jointly_monic; intro x.
  etransitivity; [ exact (ran_fmap_leg g x) |].
  etransitivity; [| symmetry; exact (ran_fmap_leg g' x) ].
  destruct x as [t f]; simpl.
  apply ran_leg_transport.
  now rewrite Hg.
Qed.
Next Obligation.
  intro b.
  apply ran_jointly_monic; intro x.
  etransitivity; [ exact (ran_fmap_leg id x) |].
  etransitivity; [| symmetry; apply id_right ].
  destruct x as [t f]; simpl.
  apply ran_leg_transport.
  apply id_right.
Qed.
Next Obligation.
  intros b b' b'' g' g.
  apply ran_jointly_monic; intro x.
  etransitivity; [ exact (ran_fmap_leg (g' ∘ g) x) |].
  symmetry.
  etransitivity; [ apply comp_assoc |].
  etransitivity.
  { apply compose_respects; [ exact (ran_fmap_leg g' x) | reflexivity ]. }
  etransitivity; [ exact (ran_fmap_leg g (ran_reindex g' x)) |].
  destruct x as [t f]; simpl.
  apply ran_leg_transport.
  symmetry; apply comp_assoc.
Qed.

(* * *** The counit, local 普遍性质 （已译） *)

(* The 恒等 对象 (a, id[F a]) comma 范畴 at F a. （已译） *)
Definition ran_id_obj (a : A) : =(F a) ↓ F :=
  existT (fun p : 1 ∏ A => F a ~> F (snd p)) (ttt, a) id.

(* The counit component at limit-cone leg at 恒等 —
 Mac Lane's ε_a = λ_{1_{F a}}, Riehl's display (6.2.3). （已译） *)
Definition ran_counit_component (a : A) :
  Pointwise_Ran (F a) ~> X a := ran_leg (ran_id_obj a).

Program Definition ran_counit : Pointwise_Ran ◯ F ⟹ X :=
  Build_Transform' (F := Pointwise_Ran ◯ F) (G := X)
    ran_counit_component _.
Next Obligation.
  intros a a' v; simpl.
  unfold ran_counit_component.
  (* left side: coherence along comma 态射 (ttt, v) (a, id)
 (a', F v) (=(F a) ↓ F) （已译） *)
  assert (sq : fmap[F] v ∘ fmap[=(F a)] (@id 1 ttt)
                 ≈ fmap[F] v ∘ @id B (F a)).
  { simpl; reflexivity. }
  etransitivity.
  { exact (ran_leg_coherence
             ((((ttt, v); sq))
                : ran_id_obj a
                    ~{=(F a) ↓ F}~>
                  existT (fun p : (1 ∏ A)%category => F a ~> F (snd p))
                    (ttt, a') (fmap[F] v))). }
  (* right side: the reindexing property of ran_fmap at (a', id) *)
  symmetry.
  etransitivity.
  { exact (ran_fmap_leg (fmap[F] v) (ran_id_obj a')). }
  change (ran_leg (existT (fun p : (1 ∏ A)%category => F a ~> F (snd p))
            (ttt, a') (@id B (F a') ∘ fmap[F] v))
            ≈ ran_leg (existT (fun p : (1 ∏ A)%category => F a ~> F (snd p))
                (ttt, a') (fmap[F] v))).
  apply ran_leg_transport.
  apply id_left.
Qed.

(* The mediating cone 普遍性质: transformation
 μ : M ◯ F ⟹ X spreads over comma 范畴 cone legs
 μ_a ∘ M f at (a, f). （已译） *)
Program Definition ran_ump_cone (M : B ⟶ C) (μ : M ◯ F ⟹ X) (b : B) :
  Cone (ran_comma_diagram b) :=
  @Build_Cone (=(b) ↓ F) C (ran_comma_diagram b) (M b)
    (@Build_ACone (=(b) ↓ F) C (M b) (ran_comma_diagram b)
       (fun x => transform[μ] (snd `1 x) ∘ fmap[M] (`2 x)) _).
Next Obligation.
  intros M μ b x y f; simpl.
  destruct x as [[tx ax] fx], y as [[ty ay] fy], f as [[u v] sq];
    simpl in *.
  rewrite id_right in sq.
  etransitivity; [ apply comp_assoc |].
  srewrite (@naturality _ _ _ _ μ _ _ v).
  etransitivity; [ symmetry; apply comp_assoc |].
  apply compose_respects; [ reflexivity |].
  etransitivity; [ symmetry; apply fmap_comp |].
  apply fmap_respects.
  now rewrite <- sq.
Qed.

Definition ran_ump_delta (M : B ⟶ C) (μ : M ◯ F ⟹ X) (b : B) :
  M b ~> ran_obj b :=
  unique_obj (@ump_limits _ _ _ (lim b) (ran_ump_cone M μ b)).

Lemma ran_ump_delta_leg (M : B ⟶ C) (μ : M ◯ F ⟹ X) (b : B)
  (x : =(b) ↓ F) :
  ran_leg x ∘ ran_ump_delta M μ b
    ≈ transform[μ] (snd `1 x) ∘ fmap[M] (`2 x).
Proof.
  exact (unique_property (@ump_limits _ _ _ (lim b) (ran_ump_cone M μ b)) x).
Qed.

Program Definition ran_ump_transform (M : B ⟶ C) (μ : M ◯ F ⟹ X) :
  M ⟹ Pointwise_Ran :=
  Build_Transform' (F := M) (G := Pointwise_Ran)
    (ran_ump_delta M μ) _.
Next Obligation.
  intros M μ b b' g; simpl.
  apply ran_jointly_monic; intro x.
  etransitivity.
  { etransitivity; [ apply comp_assoc |].
    apply compose_respects; [ exact (ran_fmap_leg g x) | reflexivity ]. }
  etransitivity; [ exact (ran_ump_delta_leg M μ b (ran_reindex g x)) |].
  change (transform[μ] (snd `1 x) ∘ fmap[M] (`2 x ∘ g)
            ≈ ran_leg x ∘ (ran_ump_delta M μ b' ∘ fmap[M] g)).
  symmetry.
  etransitivity; [ apply comp_assoc |].
  etransitivity.
  { apply compose_respects; [ exact (ran_ump_delta_leg M μ b' x) | reflexivity ]. }
  etransitivity; [ symmetry; apply comp_assoc |].
  apply compose_respects; [ reflexivity |].
  symmetry; exact (@fmap_comp _ _ M _ _ _ (`2 x) g).
Qed.

#[export] Program Instance Pointwise_LocalRightKan : LocalRightKan F X := {|
  LocalRan := Pointwise_Ran;
  ran_transform := ran_counit
|}.
Next Obligation.
  intros M μ.
  unshelve refine {| unique_obj := ran_ump_transform M μ |}.
  - (* factorization: μ_a ≈ ε_a ∘ δ_{F a} *)
    intro a; simpl.
    unfold ran_counit_component.
    symmetry.
    etransitivity; [ exact (ran_ump_delta_leg M μ (F a) (ran_id_obj a)) |].
    simpl.
    now rewrite fmap_id, id_right.
  - (* uniqueness *)
    intros v Hv b.
    apply ran_jointly_monic; intro x.
    etransitivity; [ exact (ran_ump_delta_leg M μ b x) |].
    destruct x as [[t a] f]; destruct t; simpl.
    (* μ_a ∘ M f ≈ ran_leg ((ttt,a); f) ∘ v_b, through factorization
 假设, 自然性 v, leg at 恒等 （已译） *)
    etransitivity.
    { apply compose_respects; [ exact (Hv a) | reflexivity ]. }
    etransitivity; [ symmetry; apply comp_assoc |].
    etransitivity.
    { apply compose_respects; [ reflexivity |].
      symmetry; exact (@naturality _ _ _ _ v _ _ f). }
    etransitivity; [ apply comp_assoc |].
    symmetry.
    apply compose_respects; [| reflexivity ].
    unfold ran_counit_component.
    etransitivity.
    { apply (ran_leg_transport (ttt, a) f (id ∘ f)).
      now rewrite id_left. }
    symmetry.
    exact (ran_fmap_leg f (ran_id_obj a)).
Qed.

(* * *** Acceptance: counit leg at 恒等, nose （已译） *)

Example ran_counit_is_identity_leg (a : A) :
  transform[@ran_transform _ _ _ _ _ Pointwise_LocalRightKan] a
    = ran_leg (ran_id_obj a) := eq_refl.

Example ran_extension_is_pointwise_limit (b : B) :
  @LocalRan _ _ F _ X Pointwise_LocalRightKan b
    = vertex_obj[(@limit_cone _ _ _ (lim b))] := eq_refl.

End PointwiseRan.

(* 相关说明。 （已译） *)

Section PointwiseLan.

Context {A : Category}.
Context {B : Category}.
Context {F : A ⟶ B}.
Context {C : Category}.
Context (X : A ⟶ C).

(* The diagram whose colimit computes extension at b: comma
 范畴 (F ↓ =(b)) pairs (a, f : F ~> b), projected A and
 followed X. （已译） *)
Definition lan_comma_diagram (b : B) : (F ↓ =(b)) ⟶ C :=
  X ◯ @comma_proj1 _ _ _ F =(b).

Context (colim : ∀ b : B, Colimit (lan_comma_diagram b)).

Definition lan_obj (b : B) : C :=
  vertex_obj[@limit_cone _ _ _ (colim b)].

(* 相关说明。 （已译） *)
Definition lan_inj {b : B} (x : F ↓ =(b)) :
  lan_comma_diagram b x ~{C}~> lan_obj b :=
  cocone_inj (@limit_cone _ _ _ (colim b)) x.

Lemma lan_inj_coherence {b : B} {x y : F ↓ =(b)} (f : x ~{F ↓ =(b)}~> y) :
  lan_inj y ∘ fmap[lan_comma_diagram b] f ≈ lan_inj x.
Proof.
  exact (cocone_inj_coherence (@limit_cone _ _ _ (colim b)) f).
Qed.

Lemma lan_inj_transport {b : B} (t : (A ∏ 1)%category) (f f' : F (fst t) ~> b) :
  f ≈ f' →
  lan_inj (existT _ t f) ≈ lan_inj (existT _ t f').
Proof.
  intro Hf.
  assert (sq : f' ∘ fmap[F] (@id A (fst t)) ≈ fmap[=(b)] (@id 1 (snd t)) ∘ f).
  { simpl.
    rewrite fmap_id, id_left, id_right.
    now symmetry. }
  rewrite <- (lan_inj_coherence
                ((((@id A (fst t), ttt); sq))
                   : existT (fun p : (A ∏ 1)%category => F (fst p) ~> b) t f
                       ~{F ↓ =(b)}~> existT _ t f')).
  simpl.
  now rewrite fmap_id, id_right.
Qed.

(* 相关说明。 （已译） *)
Program Definition lan_probe_cocone {b : B} {c : C} (u : lan_obj b ~> c) :
  Cocone (lan_comma_diagram b) :=
  @Build_Cone ((F ↓ =(b))^op) (C^op) ((lan_comma_diagram b)^op) c
    (@Build_ACone ((F ↓ =(b))^op) (C^op) c ((lan_comma_diagram b)^op)
       (fun x => u ∘ lan_inj x) _).
Next Obligation.
  intros b c u x y f; simpl.
  rewrite <- comp_assoc.
  now rewrite (lan_inj_coherence f).
Qed.

Lemma lan_jointly_epic {b : B} {c : C} (u v : lan_obj b ~> c) :
  (∀ x : F ↓ =(b), u ∘ lan_inj x ≈ v ∘ lan_inj x) →
  u ≈ v.
Proof.
  intro H.
  pose proof (colimitcocone_ump
                (colimit_colimitcocone (colim b)) (lan_probe_cocone u)) as U.
  transitivity (unique_obj U).
  - symmetry; apply (uniqueness U); intro x; reflexivity.
  - apply (uniqueness U); intro x; symmetry; apply H.
Qed.

(* * *** Reindexing, extension 函子 （已译） *)

(* g : b ~> b' postcomposes the comma component: (a, f : F a ~> b) becomes
   (a, g ∘ f : F a ~> b'). *)
Program Definition lan_reindex {b b' : B} (g : b ~> b') :
  (F ↓ =(b)) ⟶ (F ↓ =(b')) := {|
  fobj := fun x => existT _ (`1 x) (g ∘ `2 x);
  fmap := fun x y f => (`1 f; _)
|}.
Next Obligation.
  intros b b' g x y f.
  destruct f as [[u v] sq]; simpl in *.
  rewrite id_left in sq.
  rewrite id_left.
  rewrite <- comp_assoc.
  now rewrite sq.
Qed.
Next Obligation.
  intros b b' g x y f f' [e1 e2]; simpl.
  split; assumption.
Qed.
Next Obligation.
  intros b b' g x; simpl.
  split; reflexivity.
Qed.
Next Obligation.
  intros b b' g x y z f f'; simpl.
  split; reflexivity.
Qed.

(* The restricted cocone: b'-injections at reindexed 对象 form a
 cocone over b-diagram. （已译） *)
Program Definition lan_restrict_cocone {b b' : B} (g : b ~> b') :
  Cocone (lan_comma_diagram b) :=
  @Build_Cone ((F ↓ =(b))^op) (C^op) ((lan_comma_diagram b)^op)
    (lan_obj b')
    (@Build_ACone ((F ↓ =(b))^op) (C^op) (lan_obj b')
       ((lan_comma_diagram b)^op)
       (fun x => lan_inj (lan_reindex g x)) _).
Next Obligation.
  intros b b' g x y f; simpl.
  exact (lan_inj_coherence (fmap[lan_reindex g] f)).
Qed.

Definition lan_fmap {b b' : B} (g : b ~> b') : lan_obj b ~> lan_obj b' :=
  unique_obj (colimitcocone_ump (colimit_colimitcocone (colim b))
                (lan_restrict_cocone g)).

Lemma lan_fmap_inj {b b' : B} (g : b ~> b') (x : F ↓ =(b)) :
  lan_fmap g ∘ lan_inj x ≈ lan_inj (lan_reindex g x).
Proof.
  exact (unique_property
           (colimitcocone_ump (colimit_colimitcocone (colim b))
              (lan_restrict_cocone g)) x).
Qed.

Program Definition Pointwise_Lan : B ⟶ C := {|
  fobj := lan_obj;
  fmap := fun b b' g => lan_fmap g
|}.
Next Obligation.
  intros b b' g g' Hg.
  apply lan_jointly_epic; intro x.
  etransitivity; [ exact (lan_fmap_inj g x) |].
  etransitivity; [| symmetry; exact (lan_fmap_inj g' x) ].
  destruct x as [t f]; simpl.
  apply lan_inj_transport.
  now rewrite Hg.
Qed.
Next Obligation.
  intro b.
  apply lan_jointly_epic; intro x.
  etransitivity; [ exact (lan_fmap_inj id x) |].
  etransitivity; [| symmetry; apply id_left ].
  destruct x as [t f]; simpl.
  apply lan_inj_transport.
  apply id_left.
Qed.
Next Obligation.
  intros b b' b'' g' g.
  apply lan_jointly_epic; intro x.
  etransitivity; [ exact (lan_fmap_inj (g' ∘ g) x) |].
  symmetry.
  etransitivity; [ symmetry; apply comp_assoc |].
  etransitivity.
  { apply compose_respects; [ reflexivity | exact (lan_fmap_inj g x) ]. }
  etransitivity; [ exact (lan_fmap_inj g' (lan_reindex g x)) |].
  destruct x as [t f]; simpl.
  apply lan_inj_transport.
  apply comp_assoc.
Qed.

(* * *** The unit, local 普遍性质 （已译） *)

Definition lan_id_obj (a : A) : F ↓ =(F a) :=
  existT (fun p : A ∏ 1 => F (fst p) ~> F a) (a, ttt) id.

(* The unit component at colimit injection at 恒等 —
 Riehl's display (6.2.2). （已译） *)
Definition lan_unit_component (a : A) :
  X a ~> Pointwise_Lan (F a) := lan_inj (lan_id_obj a).

Program Definition lan_unit : X ⟹ Pointwise_Lan ◯ F :=
  Build_Transform' (F := X) (G := Pointwise_Lan ◯ F)
    lan_unit_component _.
Next Obligation.
  intros a a' v; simpl.
  unfold lan_unit_component.
  (* left side: reindexing property lan_fmap at (a, id); right
 side: coherence along comma 态射 (v, ttt) (a, F v) to
 (a', id) (F ↓ =(F a')) （已译） *)
  assert (sq : @id B (F a') ∘ fmap[F] v
                 ≈ fmap[=(F a')] (@id 1 ttt) ∘ fmap[F] v).
  { simpl; reflexivity. }
  etransitivity; [ exact (lan_fmap_inj (fmap[F] v) (lan_id_obj a)) |].
  symmetry.
  etransitivity.
  { exact (lan_inj_coherence
             ((((v, ttt); sq))
                : existT (fun p : (A ∏ 1)%category => F (fst p) ~> F a')
                    (a, ttt) (fmap[F] v)
                    ~{F ↓ =(F a')}~> lan_id_obj a')). }
  change (lan_inj (existT (fun p : (A ∏ 1)%category => F (fst p) ~> F a')
            (a, ttt) (fmap[F] v))
            ≈ lan_inj (existT (fun p : (A ∏ 1)%category => F (fst p) ~> F a')
                (a, ttt) (fmap[F] v ∘ @id B (F a)))).
  apply lan_inj_transport.
  now rewrite id_right.
Qed.

(* The mediating cocone 普遍性质: transformation
 ε : X ⟹ M ◯ F spreads over comma 范畴 cocone legs
 M f ∘ ε_a at (a, f). （已译） *)
Program Definition lan_ump_cocone (M : B ⟶ C) (ε : X ⟹ M ◯ F) (b : B) :
  Cocone (lan_comma_diagram b) :=
  @Build_Cone ((F ↓ =(b))^op) (C^op) ((lan_comma_diagram b)^op) (M b)
    (@Build_ACone ((F ↓ =(b))^op) (C^op) (M b) ((lan_comma_diagram b)^op)
       (fun x => fmap[M] (`2 x) ∘ transform[ε] (fst `1 x)) _).
Next Obligation.
  intros M ε b x y f; simpl.
  destruct x as [[ax tx] fx], y as [[ay ty] fy], f as [[u v] sq];
    simpl in *.
  rewrite id_left in sq.
  etransitivity; [ symmetry; apply comp_assoc |].
  srewrite_r (@naturality _ _ _ _ ε _ _ u).
  etransitivity; [ apply comp_assoc |].
  apply compose_respects; [| reflexivity ].
  etransitivity; [ symmetry; exact (@fmap_comp _ _ M _ _ _ fx (fmap[F] u)) |].
  apply fmap_respects.
  now rewrite sq.
Qed.

Definition lan_ump_delta (M : B ⟶ C) (ε : X ⟹ M ◯ F) (b : B) :
  lan_obj b ~> M b :=
  unique_obj (colimitcocone_ump (colimit_colimitcocone (colim b))
                (lan_ump_cocone M ε b)).

Lemma lan_ump_delta_inj (M : B ⟶ C) (ε : X ⟹ M ◯ F) (b : B)
  (x : F ↓ =(b)) :
  lan_ump_delta M ε b ∘ lan_inj x
    ≈ fmap[M] (`2 x) ∘ transform[ε] (fst `1 x).
Proof.
  exact (unique_property
           (colimitcocone_ump (colimit_colimitcocone (colim b))
              (lan_ump_cocone M ε b)) x).
Qed.

Program Definition lan_ump_transform (M : B ⟶ C) (ε : X ⟹ M ◯ F) :
  Pointwise_Lan ⟹ M :=
  Build_Transform' (F := Pointwise_Lan) (G := M)
    (lan_ump_delta M ε) _.
Next Obligation.
  intros M ε b b' g; simpl.
  apply lan_jointly_epic; intro x.
  etransitivity; [ symmetry; apply comp_assoc |].
  etransitivity.
  { apply compose_respects; [ reflexivity | exact (lan_ump_delta_inj M ε b x) ]. }
  etransitivity; [ apply comp_assoc |].
  etransitivity.
  { apply compose_respects;
      [ symmetry; exact (@fmap_comp _ _ M _ _ _ g (`2 x)) | reflexivity ]. }
  symmetry.
  etransitivity; [ symmetry; apply comp_assoc |].
  etransitivity.
  { apply compose_respects; [ reflexivity | exact (lan_fmap_inj g x) ]. }
  etransitivity; [ exact (lan_ump_delta_inj M ε b' (lan_reindex g x)) |].
  reflexivity.
Qed.

#[export] Program Instance Pointwise_LocalLeftKan : LocalLeftKan F X := {|
  LocalLan := Pointwise_Lan;
  lan_transform := lan_unit
|}.
Next Obligation.
  intros M ε.
  unshelve refine {| unique_obj := lan_ump_transform M ε |}.
  - (* factorization: ε_a ≈ δ_{F a} ∘ η_a *)
    intro a; simpl.
    unfold lan_unit_component.
    symmetry.
    etransitivity; [ exact (lan_ump_delta_inj M ε (F a) (lan_id_obj a)) |].
    simpl.
    now rewrite fmap_id, id_left.
  - (* uniqueness *)
    intros v Hv b.
    apply lan_jointly_epic; intro x.
    etransitivity; [ exact (lan_ump_delta_inj M ε b x) |].
    destruct x as [[a t] f]; destruct t; simpl.
    (* M f ∘ ε_a ≈ v_b ∘ lan_inj ((a,ttt); f), through factorization
 假设, 自然性 v, injection at 恒等 （已译） *)
    symmetry.
    etransitivity.
    { apply compose_respects; [ reflexivity |].
      etransitivity.
      { apply (lan_inj_transport (a, ttt) f (f ∘ id)).
        now rewrite id_right. }
      symmetry.
      exact (lan_fmap_inj f (lan_id_obj a)). }
    etransitivity; [ apply comp_assoc |].
    etransitivity.
    { apply compose_respects;
        [ symmetry; exact (@naturality _ _ _ _ v _ _ f) | reflexivity ]. }
    etransitivity; [ symmetry; apply comp_assoc |].
    apply compose_respects; [ reflexivity |].
    symmetry; exact (Hv a).
Qed.

(* * *** Acceptance: unit injection at 恒等, nose （已译） *)

Example lan_unit_is_identity_inj (a : A) :
  transform[@lan_transform _ _ _ _ _ Pointwise_LocalLeftKan] a
    = lan_inj (lan_id_obj a) := eq_refl.

Example lan_extension_is_pointwise_colimit (b : B) :
  @LocalLan _ _ F _ X Pointwise_LocalLeftKan b
    = vertex_obj[@limit_cone _ _ _ (colim b)] := eq_refl.

End PointwiseLan.
