Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.

Generalizable All Variables.

(** * Limits of rings are computed on underlying sets *)

(*
 nLab: https://ncatlab.org/nlab/show/limit#limits_in_categories_of_algebras
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_rings

   本文件给出极限实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** * Joint monicity of limit legs in [Sets], elementwise *)

Section RngSetsExt.

Context {J : Category}.
Context {F : J ⟶ Sets}.
Context {c : Sets}.
Context (H : IsALimit F c).

Definition rng_sets_pre {d : Sets} (u : d ~{Sets}~> c) : Cone F :=
  @Build_Cone J Sets F d
    (@Build_ACone J Sets d F (fun j => limit_leg H j ∘ u)
       (fun x y f =>
          transitivity (comp_assoc _ _ _)
            (@compose_respects Sets _ _ _ _ _ (limit_leg_coherence H f) _ _
               (reflexivity u)))).

Lemma rng_sets_med_eq {d : Sets} (u v : d ~{Sets}~> c) :
  (∀ j : J, limit_leg H j ∘ u ≈ limit_leg H j ∘ v) → u ≈ v.
Proof.
  intro Huv.
  apply (limit_med_eq H (rng_sets_pre u)).
  - intro j; reflexivity.
  - intro j; symmetry; apply Huv.
Qed.

Program Definition rng_sets_const (x : carrier c) : c ~{Sets}~> c :=
  {| morphism := fun _ => x |}.

Lemma rng_sets_limit_ext (x y : carrier c) :
  (∀ j : J, limit_leg H j x ≈ limit_leg H j y) → x ≈ y.
Proof.
  intro Hxy.
  exact (rng_sets_med_eq (rng_sets_const x) (rng_sets_const y)
           (fun j a => Hxy j) x).
Qed.

End RngSetsExt.

(** * The created ring structure on a limit of underlying sets *)

Section RngLift.

Context {J : Category}.
Context (K : J ⟶ Rng).
Context (L : Limit (Rng_Forget ◯ K)).

Definition rlim_leg (j : J) : vertex_obj[L] ~{Sets}~> rig_setoid (K j) :=
  limit_leg (limit_is_alimit L) j.

Lemma rlim_leg_coherence {x y : J} (f : x ~{J}~> y)
  (a : carrier vertex_obj[L]) :
  rig_map (fmap[K] f) (rlim_leg x a) ≈ rlim_leg y a.
Proof. exact (limit_leg_coherence (limit_is_alimit L) f a). Qed.

Lemma rlim_ext (x y : carrier vertex_obj[L]) :
  (∀ j : J, rlim_leg j x ≈ rlim_leg j y) → x ≈ y.
Proof. exact (rng_sets_limit_ext (limit_is_alimit L) x y). Qed.

(** ** The addition *)

Definition rlim_pair : Sets :=
  {| carrier   := carrier vertex_obj[L] * carrier vertex_obj[L]
   ; is_setoid := prod_setoid |}.

Program Definition rlim_add_leg (j : J) :
  rlim_pair ~{Sets}~> rig_setoid (K j) :=
  {| morphism := fun p =>
       rig_add (K j) (rlim_leg j (fst p)) (rlim_leg j (snd p)) |}.
Next Obligation.
  intros p q Hpq.
  destruct Hpq as [H1 H2].
  now rewrite H1, H2.
Qed.

Lemma rlim_add_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Rng_Forget ◯ K] f ∘ rlim_add_leg x ≈ rlim_add_leg y.
Proof.
  intro p; simpl.
  rewrite rig_map_add.
  now rewrite !rlim_leg_coherence.
Qed.

Definition rlim_add_cone : Cone (Rng_Forget ◯ K) :=
  @Build_Cone J Sets (Rng_Forget ◯ K) rlim_pair
    (@Build_ACone J Sets rlim_pair (Rng_Forget ◯ K)
       rlim_add_leg (@rlim_add_coherence)).

Definition rlim_add_map : rlim_pair ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) rlim_add_cone.

Definition rlim_add (a b : carrier vertex_obj[L]) : carrier vertex_obj[L] :=
  rlim_add_map (a, b).

Lemma rlim_add_triangle (j : J) (a b : carrier vertex_obj[L]) :
  rlim_leg j (rlim_add a b) ≈ rig_add (K j) (rlim_leg j a) (rlim_leg j b).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) rlim_add_cone j (a, b)).
Qed.

Lemma rlim_add_respects :
  Proper (equiv ==> equiv ==> equiv) rlim_add.
Proof.
  intros a a' Ha b b' Hb.
  exact (proper_morphism rlim_add_map (a, b) (a', b') (Ha, Hb)).
Qed.

(** ** The multiplication *)

Program Definition rlim_mul_leg (j : J) :
  rlim_pair ~{Sets}~> rig_setoid (K j) :=
  {| morphism := fun p =>
       rig_mul (K j) (rlim_leg j (fst p)) (rlim_leg j (snd p)) |}.
Next Obligation.
  intros p q Hpq.
  destruct Hpq as [H1 H2].
  now rewrite H1, H2.
Qed.

Lemma rlim_mul_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Rng_Forget ◯ K] f ∘ rlim_mul_leg x ≈ rlim_mul_leg y.
Proof.
  intro p; simpl.
  rewrite rig_map_mul.
  now rewrite !rlim_leg_coherence.
Qed.

Definition rlim_mul_cone : Cone (Rng_Forget ◯ K) :=
  @Build_Cone J Sets (Rng_Forget ◯ K) rlim_pair
    (@Build_ACone J Sets rlim_pair (Rng_Forget ◯ K)
       rlim_mul_leg (@rlim_mul_coherence)).

Definition rlim_mul_map : rlim_pair ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) rlim_mul_cone.

Definition rlim_mul (a b : carrier vertex_obj[L]) : carrier vertex_obj[L] :=
  rlim_mul_map (a, b).

Lemma rlim_mul_triangle (j : J) (a b : carrier vertex_obj[L]) :
  rlim_leg j (rlim_mul a b) ≈ rig_mul (K j) (rlim_leg j a) (rlim_leg j b).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) rlim_mul_cone j (a, b)).
Qed.

Lemma rlim_mul_respects :
  Proper (equiv ==> equiv ==> equiv) rlim_mul.
Proof.
  intros a a' Ha b b' Hb.
  exact (proper_morphism rlim_mul_map (a, b) (a', b') (Ha, Hb)).
Qed.

(** ** The additive unit *)

Program Definition rlim_zero_leg (j : J) :
  unit_setoid_object ~{Sets}~> rig_setoid (K j) :=
  {| morphism := fun _ => rig_zero (K j) |}.

Lemma rlim_zero_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Rng_Forget ◯ K] f ∘ rlim_zero_leg x ≈ rlim_zero_leg y.
Proof. intro p; simpl; apply rig_map_zero. Qed.

Definition rlim_zero_cone : Cone (Rng_Forget ◯ K) :=
  @Build_Cone J Sets (Rng_Forget ◯ K) unit_setoid_object
    (@Build_ACone J Sets unit_setoid_object (Rng_Forget ◯ K)
       rlim_zero_leg (@rlim_zero_coherence)).

Definition rlim_zero_map : unit_setoid_object ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) rlim_zero_cone.

Definition rlim_zero : carrier vertex_obj[L] := rlim_zero_map ttt.

Lemma rlim_zero_triangle (j : J) :
  rlim_leg j rlim_zero ≈ rig_zero (K j).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) rlim_zero_cone j ttt).
Qed.

(** ** The multiplicative unit *)

Program Definition rlim_one_leg (j : J) :
  unit_setoid_object ~{Sets}~> rig_setoid (K j) :=
  {| morphism := fun _ => rig_one (K j) |}.

Lemma rlim_one_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Rng_Forget ◯ K] f ∘ rlim_one_leg x ≈ rlim_one_leg y.
Proof. intro p; simpl; apply rig_map_one. Qed.

Definition rlim_one_cone : Cone (Rng_Forget ◯ K) :=
  @Build_Cone J Sets (Rng_Forget ◯ K) unit_setoid_object
    (@Build_ACone J Sets unit_setoid_object (Rng_Forget ◯ K)
       rlim_one_leg (@rlim_one_coherence)).

Definition rlim_one_map : unit_setoid_object ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) rlim_one_cone.

Definition rlim_one : carrier vertex_obj[L] := rlim_one_map ttt.

Lemma rlim_one_triangle (j : J) :
  rlim_leg j rlim_one ≈ rig_one (K j).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) rlim_one_cone j ttt).
Qed.

(** ** The additive inverse *)

Program Definition rlim_neg_leg (j : J) :
  vertex_obj[L] ~{Sets}~> rig_setoid (K j) :=
  {| morphism := fun a => ring_neg (K j) (rlim_leg j a) |}.
Next Obligation. intros a b Hab; now rewrite Hab. Qed.

Lemma rlim_neg_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Rng_Forget ◯ K] f ∘ rlim_neg_leg x ≈ rlim_neg_leg y.
Proof.
  intro a; simpl.
  rewrite RigHom_neg.
  now rewrite rlim_leg_coherence.
Qed.

Definition rlim_neg_cone : Cone (Rng_Forget ◯ K) :=
  @Build_Cone J Sets (Rng_Forget ◯ K) vertex_obj[L]
    (@Build_ACone J Sets vertex_obj[L] (Rng_Forget ◯ K)
       rlim_neg_leg (@rlim_neg_coherence)).

Definition rlim_neg_map : vertex_obj[L] ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) rlim_neg_cone.

Definition rlim_neg (a : carrier vertex_obj[L]) : carrier vertex_obj[L] :=
  rlim_neg_map a.

Lemma rlim_neg_triangle (j : J) (a : carrier vertex_obj[L]) :
  rlim_leg j (rlim_neg a) ≈ ring_neg (K j) (rlim_leg j a).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) rlim_neg_cone j a).
Qed.

Lemma rlim_neg_respects : Proper (equiv ==> equiv) rlim_neg.
Proof. intros a b Hab; exact (proper_morphism rlim_neg_map a b Hab). Qed.

(** ** The eleven laws, each by joint monicity of the legs *)

Lemma rlim_add_assoc (a b c : carrier vertex_obj[L]) :
  rlim_add (rlim_add a b) c ≈ rlim_add a (rlim_add b c).
Proof.
  apply rlim_ext; intro j.
  rewrite !rlim_add_triangle.
  apply rig_add_assoc.
Qed.

Lemma rlim_add_comm (a b : carrier vertex_obj[L]) :
  rlim_add a b ≈ rlim_add b a.
Proof.
  apply rlim_ext; intro j.
  rewrite !rlim_add_triangle.
  apply rig_add_comm.
Qed.

Lemma rlim_add_zero_l (a : carrier vertex_obj[L]) :
  rlim_add rlim_zero a ≈ a.
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_add_triangle, rlim_zero_triangle.
  apply rig_add_zero_l.
Qed.

Lemma rlim_mul_assoc (a b c : carrier vertex_obj[L]) :
  rlim_mul (rlim_mul a b) c ≈ rlim_mul a (rlim_mul b c).
Proof.
  apply rlim_ext; intro j.
  rewrite !rlim_mul_triangle.
  apply rig_mul_assoc.
Qed.

Lemma rlim_mul_one_l (a : carrier vertex_obj[L]) :
  rlim_mul rlim_one a ≈ a.
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_mul_triangle, rlim_one_triangle.
  apply rig_mul_one_l.
Qed.

Lemma rlim_mul_one_r (a : carrier vertex_obj[L]) :
  rlim_mul a rlim_one ≈ a.
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_mul_triangle, rlim_one_triangle.
  apply rig_mul_one_r.
Qed.

Lemma rlim_distr_l (a b c : carrier vertex_obj[L]) :
  rlim_mul a (rlim_add b c)
    ≈ rlim_add (rlim_mul a b) (rlim_mul a c).
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_add_triangle, !rlim_mul_triangle, rlim_add_triangle.
  apply rig_distr_l.
Qed.

Lemma rlim_distr_r (a b c : carrier vertex_obj[L]) :
  rlim_mul (rlim_add a b) c
    ≈ rlim_add (rlim_mul a c) (rlim_mul b c).
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_add_triangle, !rlim_mul_triangle, rlim_add_triangle.
  apply rig_distr_r.
Qed.

Lemma rlim_mul_zero_l (a : carrier vertex_obj[L]) :
  rlim_mul rlim_zero a ≈ rlim_zero.
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_mul_triangle, !rlim_zero_triangle.
  apply rig_mul_zero_l.
Qed.

Lemma rlim_mul_zero_r (a : carrier vertex_obj[L]) :
  rlim_mul a rlim_zero ≈ rlim_zero.
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_mul_triangle, !rlim_zero_triangle.
  apply rig_mul_zero_r.
Qed.

Lemma rlim_neg_l (a : carrier vertex_obj[L]) :
  rlim_add (rlim_neg a) a ≈ rlim_zero.
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_add_triangle, rlim_neg_triangle, rlim_zero_triangle.
  apply ring_neg_l.
Qed.

(** ** The vertex's equality is propositional *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition rlim_prop : PropEquiv (is_setoid vertex_obj[L]) :=
  @PropEquiv_of_relation _ (is_setoid vertex_obj[L])
    (fun x y => forall j : J,
       @pequiv _ _ (rig_prop (K j)) (rlim_leg j x) (rlim_leg j y))
    (fun x y H => rlim_ext x y (fun j => pequiv_to _ _ (H j)))
    (fun x y H j => pequiv_from _ _ (proper_morphism (rlim_leg j) x y H)).

(** ** The lifted rig and the lifted ring *)

Definition LimitRig : RigObject :=
  {| rig_setoid       := vertex_obj[L]
   ; rig_zero         := rlim_zero
   ; rig_add          := rlim_add
   ; rig_one          := rlim_one
   ; rig_mul          := rlim_mul
   ; rig_add_respects := rlim_add_respects
   ; rig_mul_respects := rlim_mul_respects
   ; rig_add_assoc    := rlim_add_assoc
   ; rig_add_comm     := rlim_add_comm
   ; rig_add_zero_l   := rlim_add_zero_l
   ; rig_mul_assoc    := rlim_mul_assoc
   ; rig_mul_one_l    := rlim_mul_one_l
   ; rig_mul_one_r    := rlim_mul_one_r
   ; rig_distr_l      := rlim_distr_l
   ; rig_distr_r      := rlim_distr_r
   ; rig_mul_zero_l   := rlim_mul_zero_l
   ; rig_mul_zero_r   := rlim_mul_zero_r
   ; rig_prop         := rlim_prop |}.

Definition LimitRing : RingObject :=
  {| ring_rig          := LimitRig
   ; ring_neg          := rlim_neg
   ; ring_neg_respects := rlim_neg_respects
   ; ring_neg_l        := rlim_neg_l |}.

(** ** The legs are ring homomorphisms *)

Program Definition rlim_hom (j : J) : RigHom LimitRing (K j) :=
  {| rig_map := rlim_leg j |}.
Next Obligation. apply rlim_zero_triangle. Qed.
Next Obligation. apply rlim_add_triangle. Qed.
Next Obligation. apply rlim_one_triangle. Qed.
Next Obligation. apply rlim_mul_triangle. Qed.

Lemma rlim_hom_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ rlim_hom x ≈ rlim_hom y.
Proof. intro a; exact (rlim_leg_coherence f a). Qed.

Definition rlim_cone : Cone K :=
  @Build_Cone J Rng K LimitRing
    (@Build_ACone J Rng LimitRing K rlim_hom (@rlim_hom_coherence)).

(** ** Strictness: the lifted cone lies over [L] on the nose *)

Definition rlim_over_obj : Rng_Forget LimitRing = vertex_obj[L] := eq_refl.

Definition rlim_over_legs (j : J) :
  fmap[Rng_Forget] (cone_leg rlim_cone j) = rlim_leg j := eq_refl.

(** ** The lifted cone is limiting *)

Definition rlim_car_med (N : Cone K) :
  rig_setoid vertex_obj[N] ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) (FCone Rng_Forget N).

Lemma rlim_car_med_commutes (N : Cone K) (j : J)
  (a : carrier (rig_setoid vertex_obj[N])) :
  rlim_leg j (rlim_car_med N a) ≈ rig_map (cone_leg N j) a.
Proof.
  exact (limit_med_commutes (limit_is_alimit L) (FCone Rng_Forget N) j a).
Qed.

Lemma rlim_car_med_zero (N : Cone K) :
  rlim_car_med N (rig_zero vertex_obj[N]) ≈ rlim_zero.
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_car_med_commutes, rlim_zero_triangle.
  apply rig_map_zero.
Qed.

Lemma rlim_car_med_add (N : Cone K)
  (a b : carrier (rig_setoid vertex_obj[N])) :
  rlim_car_med N (rig_add vertex_obj[N] a b)
    ≈ rlim_add (rlim_car_med N a) (rlim_car_med N b).
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_car_med_commutes, rlim_add_triangle, !rlim_car_med_commutes.
  apply rig_map_add.
Qed.

Lemma rlim_car_med_one (N : Cone K) :
  rlim_car_med N (rig_one vertex_obj[N]) ≈ rlim_one.
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_car_med_commutes, rlim_one_triangle.
  apply rig_map_one.
Qed.

Lemma rlim_car_med_mul (N : Cone K)
  (a b : carrier (rig_setoid vertex_obj[N])) :
  rlim_car_med N (rig_mul vertex_obj[N] a b)
    ≈ rlim_mul (rlim_car_med N a) (rlim_car_med N b).
Proof.
  apply rlim_ext; intro j.
  rewrite rlim_car_med_commutes, rlim_mul_triangle, !rlim_car_med_commutes.
  apply rig_map_mul.
Qed.

Program Definition rlim_med (N : Cone K) : vertex_obj[N] ~{Rng}~> LimitRing :=
  {| rig_map := rlim_car_med N |}.
Next Obligation. apply rlim_car_med_zero. Qed.
Next Obligation. apply rlim_car_med_add. Qed.
Next Obligation. apply rlim_car_med_one. Qed.
Next Obligation. apply rlim_car_med_mul. Qed.

Definition rlim_created : IsALimit K LimitRing.
Proof.
  unshelve refine {| limit_acone := @coneFrom _ _ _ rlim_cone |}.
  intro N.
  unshelve refine {| unique_obj := rlim_med N |}.
  - intros j a.
    exact (rlim_car_med_commutes N j a).
  - intros v Hv a.
    exact (limit_med_unique (limit_is_alimit L) (FCone Rng_Forget N)
             (rig_map v) Hv a).
Defined.

(** ** Uniqueness of the lifted structure (Mac Lane's Theorem 2) *)

Lemma rlim_zero_unique (z : carrier vertex_obj[L])
  (Hz : ∀ j : J, rlim_leg j z ≈ rig_zero (K j)) : z ≈ rlim_zero.
Proof.
  apply rlim_ext; intro j.
  now rewrite Hz, rlim_zero_triangle.
Qed.

Lemma rlim_one_unique (e : carrier vertex_obj[L])
  (He : ∀ j : J, rlim_leg j e ≈ rig_one (K j)) : e ≈ rlim_one.
Proof.
  apply rlim_ext; intro j.
  now rewrite He, rlim_one_triangle.
Qed.

Lemma rlim_add_unique
  (p : carrier vertex_obj[L] → carrier vertex_obj[L] → carrier vertex_obj[L])
  (Hp : ∀ (j : J) a b,
     rlim_leg j (p a b) ≈ rig_add (K j) (rlim_leg j a) (rlim_leg j b))
  (a b : carrier vertex_obj[L]) : p a b ≈ rlim_add a b.
Proof.
  apply rlim_ext; intro j.
  now rewrite Hp, rlim_add_triangle.
Qed.

Lemma rlim_mul_unique
  (m : carrier vertex_obj[L] → carrier vertex_obj[L] → carrier vertex_obj[L])
  (Hm : ∀ (j : J) a b,
     rlim_leg j (m a b) ≈ rig_mul (K j) (rlim_leg j a) (rlim_leg j b))
  (a b : carrier vertex_obj[L]) : m a b ≈ rlim_mul a b.
Proof.
  apply rlim_ext; intro j.
  now rewrite Hm, rlim_mul_triangle.
Qed.

Lemma rlim_neg_unique
  (n : carrier vertex_obj[L] → carrier vertex_obj[L])
  (Hn : ∀ (j : J) a, rlim_leg j (n a) ≈ ring_neg (K j) (rlim_leg j a))
  (a : carrier vertex_obj[L]) : n a ≈ rlim_neg a.
Proof.
  apply rlim_ext; intro j.
  now rewrite Hn, rlim_neg_triangle.
Qed.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma rlim_structure_unique
  (z e : carrier vertex_obj[L])
  (p m : carrier vertex_obj[L] → carrier vertex_obj[L] →
           carrier vertex_obj[L])
  (n : carrier vertex_obj[L] → carrier vertex_obj[L])
  (Hz : ∀ j : J, rlim_leg j z ≈ rig_zero (K j))
  (He : ∀ j : J, rlim_leg j e ≈ rig_one (K j))
  (Hp : ∀ (j : J) a b,
     rlim_leg j (p a b) ≈ rig_add (K j) (rlim_leg j a) (rlim_leg j b))
  (Hm : ∀ (j : J) a b,
     rlim_leg j (m a b) ≈ rig_mul (K j) (rlim_leg j a) (rlim_leg j b))
  (Hn : ∀ (j : J) a, rlim_leg j (n a) ≈ ring_neg (K j) (rlim_leg j a)) :
  (((z ≈ rlim_zero) * (e ≈ rlim_one))
     * ((∀ a b, p a b ≈ rlim_add a b) * (∀ a b, m a b ≈ rlim_mul a b)))
    * (∀ a, n a ≈ rlim_neg a).
Proof.
  split; [ split; [ split | split ] | ].
  - exact (rlim_zero_unique z Hz).
  - exact (rlim_one_unique e He).
  - exact (rlim_add_unique p Hp).
  - exact (rlim_mul_unique m Hm).
  - exact (rlim_neg_unique n Hn).
Qed.

End RngLift.

(** * Reflection: a cone of rings whose image is limiting is limiting *)

Section RngReflect.

Context {J : Category}.
Context (K : J ⟶ Rng).
Context (M : Cone K).
Context (HM : IsLimitCone (FCone Rng_Forget M)).

Definition rrefl_med (N : Cone K) :
  rig_setoid vertex_obj[N] ~{Sets}~> rig_setoid vertex_obj[M] :=
  limit_med (limitcone_isalimit HM) (FCone Rng_Forget N).

Lemma rrefl_med_commutes (N : Cone K) (j : J)
  (a : carrier (rig_setoid vertex_obj[N])) :
  rig_map (cone_leg M j) (rrefl_med N a) ≈ rig_map (cone_leg N j) a.
Proof using All.
  exact (limit_med_commutes (limitcone_isalimit HM) (FCone Rng_Forget N) j a).
Qed.

Lemma rrefl_ext (x y : carrier (rig_setoid vertex_obj[M])) :
  (∀ j : J, rig_map (cone_leg M j) x ≈ rig_map (cone_leg M j) y) → x ≈ y.
Proof using All. exact (rng_sets_limit_ext (limitcone_isalimit HM) x y). Qed.

Lemma rrefl_med_zero (N : Cone K) :
  rrefl_med N (rig_zero vertex_obj[N]) ≈ rig_zero vertex_obj[M].
Proof using All.
  apply rrefl_ext; intro j.
  rewrite rrefl_med_commutes, !rig_map_zero.
  reflexivity.
Qed.

Lemma rrefl_med_add (N : Cone K)
  (a b : carrier (rig_setoid vertex_obj[N])) :
  rrefl_med N (rig_add vertex_obj[N] a b)
    ≈ rig_add vertex_obj[M] (rrefl_med N a) (rrefl_med N b).
Proof using All.
  apply rrefl_ext; intro j.
  rewrite rrefl_med_commutes, !rig_map_add, !rrefl_med_commutes.
  reflexivity.
Qed.

Lemma rrefl_med_one (N : Cone K) :
  rrefl_med N (rig_one vertex_obj[N]) ≈ rig_one vertex_obj[M].
Proof using All.
  apply rrefl_ext; intro j.
  rewrite rrefl_med_commutes, !rig_map_one.
  reflexivity.
Qed.

Lemma rrefl_med_mul (N : Cone K)
  (a b : carrier (rig_setoid vertex_obj[N])) :
  rrefl_med N (rig_mul vertex_obj[N] a b)
    ≈ rig_mul vertex_obj[M] (rrefl_med N a) (rrefl_med N b).
Proof using All.
  apply rrefl_ext; intro j.
  rewrite rrefl_med_commutes, !rig_map_mul, !rrefl_med_commutes.
  reflexivity.
Qed.

Program Definition rrefl_hom (N : Cone K) :
  vertex_obj[N] ~{Rng}~> vertex_obj[M] := {| rig_map := rrefl_med N |}.
Next Obligation. apply rrefl_med_zero. Qed.
Next Obligation. apply rrefl_med_add. Qed.
Next Obligation. apply rrefl_med_one. Qed.
Next Obligation. apply rrefl_med_mul. Qed.

Definition rng_reflects : IsLimitCone M.
Proof using All.
  intro N.
  unshelve refine {| unique_obj := rrefl_hom N |}.
  - intros j a.
    exact (rrefl_med_commutes N j a).
  - intros v Hv a.
    exact (limit_med_unique (limitcone_isalimit HM) (FCone Rng_Forget N)
             (rig_map v) Hv a).
Defined.

End RngReflect.

(** * [Rng_Forget] strictly creates every limit *)

Section RngStrictlyCreates.

Context {J : Category}.
Context (K : J ⟶ Rng).

Definition rng_strict_lift (N : Cone (Rng_Forget ◯ K)) (HN : IsLimitCone N) :
  StrictLift K Rng_Forget N :=
  @Build_StrictLift J Rng Sets K Rng_Forget N
    (rlim_cone K (@Build_Limit J Sets (Rng_Forget ◯ K) N HN))
    eq_refl
    (fun x => reflexivity _).

Definition Rng_Forget_StrictlyCreatesLimit : StrictlyCreatesLimit K Rng_Forget.
Proof.
  unshelve refine {| screates := rng_strict_lift |}.
  - intros N HN.
    exact (@ump_limit _ _ _ _
             (rlim_created K (@Build_Limit J Sets (Rng_Forget ◯ K) N HN))).
  - intros M HM.
    exact (rng_reflects K M HM).
Defined.

Definition Rng_Forget_CreatesLimit : CreatesLimit K Rng_Forget :=
  StrictlyCreatesLimit_CreatesLimit Rng_Forget_StrictlyCreatesLimit.

End RngStrictlyCreates.

Definition Rng_Forget_StrictlyCreatesLimits :
  StrictlyCreatesLimits Rng_Forget :=
  fun J K => Rng_Forget_StrictlyCreatesLimit K.

Definition Rng_Forget_creates_limits : CreatesAllLimits Rng_Forget :=
  fun J K => Rng_Forget_CreatesLimit K.

Definition Rng_Forget_reflects_limits {J : Category} (K : J ⟶ Rng) :
  ReflectsLimitCone K Rng_Forget :=
  creates_reflects_limits (Rng_Forget_CreatesLimit K).

(*
   本节说明 Limit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Rng_lift_cone_unique {J : Category} (K : J ⟶ Rng)
  (N : Cone (Rng_Forget ◯ K)) (HN : IsLimitCone N)
  (M : Cone K) (i : ConeIso (FCone Rng_Forget M) N) :
  ConeIso M (slift_cone (screates N HN)) :=
  screates_lift_unique (Rng_Forget_StrictlyCreatesLimit K) N HN M i.

(** * The image of a cone of rings is the elementwise cone *)

Example rng_fcone_apex {J : Category} (K : J ⟶ Rng) (N : Cone K) :
  vertex_obj[FCone Rng_Forget N] = rig_setoid vertex_obj[N] := eq_refl.

Example rng_fcone_leg {J : Category} (K : J ⟶ Rng) (N : Cone K) (j : J) :
  cone_leg (FCone Rng_Forget N) j = rig_map (cone_leg N j) := eq_refl.

(** * Mac Lane's Theorem 2: the lifting half *)

Definition Rng_Forget_lifts_limits {J : Category} (K : J ⟶ Rng)
  (L : Limit (Rng_Forget ◯ K)) : Limit K :=
  creates_limit_lift (Rng_Forget_CreatesLimit K) L.

Example rng_lift_apex {J : Category} (K : J ⟶ Rng)
  (L : Limit (Rng_Forget ◯ K)) :
  Rng_Forget (vertex_obj[Rng_Forget_lifts_limits K L]) = vertex_obj[L]
  := eq_refl.

Example rng_lift_legs {J : Category} (K : J ⟶ Rng)
  (L : Limit (Rng_Forget ◯ K)) (j : J) :
  fmap[Rng_Forget]
    (cone_leg (@limit_cone _ _ _ (Rng_Forget_lifts_limits K L)) j)
    = limit_leg (limit_is_alimit L) j
  := eq_refl.

(** * Corollaries: [Rng] is complete and [Rng_Forget] is continuous *)

Definition Rng_Complete : @Complete Rng :=
  creates_limits_Complete Rng_Forget Sets_Complete Rng_Forget_creates_limits.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Rng_Forget_continuous : ContinuousFunctor Rng_Forget :=
  creates_limits_continuous Rng_Forget Sets_Complete Rng_Forget_creates_limits.

Definition Rng_Forget_PreservesAllLimits : PreservesAllLimits Rng_Forget :=
  creates_limits_PreservesAllLimits Rng_Forget Sets_Complete
    Rng_Forget_creates_limits.

(** * "Limits of rings are computed on underlying sets", literally *)

Section RngComputed.

Context {J : Category}.
Context (K : J ⟶ Rng).

Example rng_complete_carrier :
  rig_setoid (vertex_obj[Rng_Complete J K]) = Sets_limit_obj (Rng_Forget ◯ K)
  := eq_refl.

Example rng_complete_add
  (a b : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (rig_add (vertex_obj[Rng_Complete J K]) a b) d
    = rig_add (K d) (`1 a d) (`1 b d) := eq_refl.

Example rng_complete_zero (d : J) :
  `1 (rig_zero (vertex_obj[Rng_Complete J K])) d = rig_zero (K d) := eq_refl.

Example rng_complete_mul
  (a b : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (rig_mul (vertex_obj[Rng_Complete J K]) a b) d
    = rig_mul (K d) (`1 a d) (`1 b d) := eq_refl.

Example rng_complete_one (d : J) :
  `1 (rig_one (vertex_obj[Rng_Complete J K])) d = rig_one (K d) := eq_refl.

Example rng_complete_neg
  (a : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (ring_neg (vertex_obj[Rng_Complete J K]) a) d
    = ring_neg (K d) (`1 a d) := eq_refl.

Example rng_complete_leg (d : J) :
  rig_map (cone_leg (@limit_cone _ _ _ (Rng_Complete J K)) d)
    = Sets_limit_leg (Rng_Forget ◯ K) d := eq_refl.

End RngComputed.
