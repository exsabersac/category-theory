(*
   本文件给出 Grothendieck 相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Ab.Coproduct.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* * ** The 函子 forgetting inverses （已译） *)

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Ab_to_CMon : Ab ⟶ CMon := {|
  fobj := fun A => ab_cmon A;
  fmap := fun _ _ f => f
|}.
Next Obligation. intros A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros A a; simpl; reflexivity. Qed.
Next Obligation. intros A B C f g a; simpl; reflexivity. Qed.

(* Both actions are strict. *)
Example Ab_to_CMon_obj (A : AbObject) :
  fobj[Ab_to_CMon] A = ab_cmon A := eq_refl.

Example Ab_to_CMon_fmap (A B : AbObject) (f : A ~{Ab}~> B) :
  fmap[Ab_to_CMon] f = f := eq_refl.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma groth_sub_cross (A : AbObject)
  (x y u v : carrier (cmon_setoid A)) :
  cmon_plus A x v ≈ cmon_plus A u y →
  ab_sub A x y ≈ ab_sub A u v.
Proof.
  intro H.
  apply (ab_cancel_l A (cmon_plus A y v)).
  transitivity (cmon_plus A x v).
  { rewrite (cmon_plus_assoc A y v (ab_sub A x y)).
    rewrite (cmon_plus_comm A v (ab_sub A x y)).
    rewrite <- (cmon_plus_assoc A y (ab_sub A x y) v).
    now rewrite (ab_add_sub_cancel A x y). }
  transitivity (cmon_plus A u y); [ exact H |].
  symmetry.
  rewrite (cmon_plus_comm A y v).
  rewrite (cmon_plus_assoc A v y (ab_sub A u v)).
  rewrite (cmon_plus_comm A y (ab_sub A u v)).
  rewrite <- (cmon_plus_assoc A v (ab_sub A u v) y).
  now rewrite (ab_add_sub_cancel A u v).
Qed.

(* * ** The group completion commutative 幺半群 （已译） *)

Section Grothendieck.

Context (M : CMonObject).

Local Notation "x ⊞ y" := (cmon_plus M x y)
  (at level 50, left associativity).

Local Notation "'MC'" := (carrier (cmon_setoid M)).

(* 相关说明。 （已译） *)
Definition GrothPair : Type := (MC * MC)%type.

(*
   本节说明 Grothendieck 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition groth_rel (p q : GrothPair) : Prop :=
  ex (fun k : MC =>
        @pequiv _ _ (cmon_prop M)
          (fst p ⊞ snd q ⊞ k) (fst q ⊞ snd p ⊞ k)).

(* The slack-free 关系, necessity 论元 below. （已译） *)
Definition groth_naive (p q : GrothPair) : Type :=
  fst p ⊞ snd q ≈ fst q ⊞ snd p.

Lemma groth_rel_refl (p : GrothPair) : groth_rel p p.
Proof. exists (cmon_zero M); apply pequiv_from; reflexivity. Qed.

Lemma groth_rel_sym (p q : GrothPair) : groth_rel p q → groth_rel q p.
Proof.
  intros [k Hk]; apply pequiv_to in Hk.
  exists k; apply pequiv_from; now symmetry.
Qed.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma groth_ac1 (a d k f l : MC) :
  a ⊞ f ⊞ (d ⊞ k ⊞ l) ≈ a ⊞ d ⊞ k ⊞ (f ⊞ l).
Proof.
  rewrite (cmon_plus_interchange M a f (d ⊞ k) l).
  now rewrite <- (cmon_plus_assoc M a d k).
Qed.

Lemma groth_ac2 (c b k f l : MC) :
  c ⊞ b ⊞ k ⊞ (f ⊞ l) ≈ c ⊞ f ⊞ l ⊞ (b ⊞ k).
Proof.
  rewrite (cmon_plus_assoc M c b k).
  rewrite (cmon_plus_interchange M c (b ⊞ k) f l).
  rewrite (cmon_plus_comm M (b ⊞ k) l).
  now rewrite <- (cmon_plus_assoc M (c ⊞ f) l (b ⊞ k)).
Qed.

Lemma groth_ac3 (e d l b k : MC) :
  e ⊞ d ⊞ l ⊞ (b ⊞ k) ≈ e ⊞ b ⊞ (d ⊞ k ⊞ l).
Proof.
  rewrite (cmon_plus_assoc M e d l).
  rewrite (cmon_plus_interchange M e (d ⊞ l) b k).
  rewrite (cmon_plus_assoc M d l k).
  rewrite (cmon_plus_comm M l k).
  now rewrite <- (cmon_plus_assoc M d k l).
Qed.

(* The transitivity computation. The produced witness [d ⊞ k ⊞ l];
 [d] what cancellative 幺半群 would let one drop. （已译） *)
Lemma groth_rel_trans (p q r : GrothPair) :
  groth_rel p q → groth_rel q r → groth_rel p r.
Proof.
  destruct p as [a b], q as [c d], r as [e f].
  intros [k Hk] [l Hl].
  apply pequiv_to in Hk; apply pequiv_to in Hl; simpl in Hk, Hl.
  exists (d ⊞ k ⊞ l); apply pequiv_from; simpl.
  rewrite (groth_ac1 a d k f l).
  rewrite Hk.
  rewrite (groth_ac2 c b k f l).
  rewrite Hl.
  apply (groth_ac3 e d l b k).
Qed.

#[local] Instance groth_rel_Equivalence : Equivalence groth_rel.
Proof.
  constructor.
  - exact groth_rel_refl.
  - exact groth_rel_sym.
  - exact groth_rel_trans.
Qed.

Definition groth_setoid : SetoidObject := {|
  carrier   := GrothPair;
  is_setoid := {| equiv := groth_rel;
                  setoid_equiv := groth_rel_Equivalence |}
|}.

(** *** The group operations *)

Definition groth_zero : GrothPair := (cmon_zero M, cmon_zero M).

Definition groth_plus (p q : GrothPair) : GrothPair :=
  (fst p ⊞ fst q, snd p ⊞ snd q).

Definition groth_neg (p : GrothPair) : GrothPair := (snd p, fst p).

Lemma groth_plus_respects :
  Proper (groth_rel ==> groth_rel ==> groth_rel) groth_plus.
Proof.
  (*
   本节说明 Grothendieck 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  intros [a b] [a' b'] Hab [c d] [c' d'] Hcd; simpl in Hab, Hcd |- *.
  destruct Hab as [k Hk], Hcd as [l Hl].
  apply pequiv_to in Hk; apply pequiv_to in Hl; simpl in Hk, Hl.
  exists (k ⊞ l); apply pequiv_from; simpl.
  rewrite (cmon_plus_interchange M a c b' d').
  rewrite (cmon_plus_interchange M (a ⊞ b') (c ⊞ d') k l).
  rewrite Hk, Hl.
  rewrite (cmon_plus_interchange M (a' ⊞ b) k (c' ⊞ d) l).
  now rewrite (cmon_plus_interchange M a' b c' d).
Qed.

Lemma groth_neg_respects : Proper (groth_rel ==> groth_rel) groth_neg.
Proof.
  intros [a b] [a' b'] Hab; simpl in Hab |- *.
  destruct Hab as [k Hk]; apply pequiv_to in Hk; simpl in Hk.
  exists k; apply pequiv_from; simpl.
  rewrite (cmon_plus_comm M b a').
  rewrite (cmon_plus_comm M b' a).
  now symmetry.
Qed.

Lemma groth_plus_assoc (p q r : GrothPair) :
  groth_rel (groth_plus (groth_plus p q) r) (groth_plus p (groth_plus q r)).
Proof.
  destruct p as [a b], q as [c d], r as [e f].
  exists (cmon_zero M); apply pequiv_from; simpl.
  now rewrite !cmon_plus_assoc.
Qed.

Lemma groth_plus_comm (p q : GrothPair) :
  groth_rel (groth_plus p q) (groth_plus q p).
Proof.
  destruct p as [a b], q as [c d].
  exists (cmon_zero M); apply pequiv_from; simpl.
  now rewrite (cmon_plus_comm M a c), (cmon_plus_comm M b d).
Qed.

Lemma groth_plus_zero_l (p : GrothPair) :
  groth_rel (groth_plus groth_zero p) p.
Proof.
  destruct p as [a b].
  exists (cmon_zero M); apply pequiv_from; simpl.
  now rewrite !cmon_plus_zero_l.
Qed.

Lemma groth_neg_left (p : GrothPair) :
  groth_rel (groth_plus (groth_neg p) p) groth_zero.
Proof.
  destruct p as [a b].
  exists (cmon_zero M); apply pequiv_from; simpl.
  rewrite !cmon_plus_zero_r.
  rewrite cmon_plus_zero_l.
  apply cmon_plus_comm.
Qed.

Definition GrothCMon : CMonObject := {|
  cmon_setoid        := groth_setoid;
  cmon_zero          := groth_zero;
  cmon_plus          := groth_plus;
  cmon_plus_respects := groth_plus_respects;
  cmon_plus_assoc    := groth_plus_assoc;
  cmon_plus_comm     := groth_plus_comm;
  cmon_plus_zero_l   := groth_plus_zero_l;
  (* [groth_rel] IS a [Prop] relation, so it is its own [Prop] mirror. *)
  cmon_prop          :=
    @PropEquiv_of_relation _ (is_setoid groth_setoid) groth_rel
      (fun _ _ h => h) (fun _ _ h => h)
|}.

(* The completion. [ab_neg] swap, so 对象 abelian by
 construction -- fact item (2) header's second-form
 discussion turns on. （已译） *)
Definition GrothendieckObject : AbObject := {|
  ab_cmon         := GrothCMon;
  ab_neg          := groth_neg;
  ab_neg_respects := groth_neg_respects;
  ab_neg_left     := groth_neg_left
|}.

(** *** The insertion *)

Program Definition groth_insert :
  M ~{CMon}~> Ab_to_CMon GrothendieckObject := {|
  cmon_map := {| morphism := fun a : MC => (a, cmon_zero M) |}
|}.
Next Obligation.
  intros a b Hab; simpl; exists (cmon_zero M); apply pequiv_from; simpl.
  now rewrite Hab.
Qed.
Next Obligation. simpl; apply groth_rel_refl. Qed.
Next Obligation.
  intros a b; simpl; exists (cmon_zero M); apply pequiv_from; simpl.
  now rewrite !cmon_plus_zero_l, !cmon_plus_zero_r.
Qed.

(** *** The universal property *)

Section Extend.

Context (A : AbObject).
Context (h : M ~{CMon}~> Ab_to_CMon A).

(* The mediator: a formal difference goes to an actual difference. *)
Definition groth_med (p : GrothPair) : carrier (cmon_setoid A) :=
  ab_sub A (cmon_map h (fst p)) (cmon_map h (snd p)).

Lemma groth_med_respects : Proper (groth_rel ==> equiv) groth_med.
Proof.
  (*
   本节说明 Grothendieck 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  intros [a b] [c d] Hpq.
  apply (@pequiv_to _ _ (cmon_prop A)).
  destruct Hpq as [k Hk].
  apply pequiv_from.
  apply pequiv_to in Hk.
  unfold groth_med; simpl in *.
  (*
   本节说明 Grothendieck 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  assert (Hh : cmon_plus A
                 (cmon_plus A (cmon_map h a) (cmon_map h d))
                 (cmon_map h k)
               ≈ cmon_plus A
                   (cmon_plus A (cmon_map h c) (cmon_map h b))
                   (cmon_map h k)).
  { rewrite <- !(cmon_map_plus h).
    now rewrite Hk. }
  assert (Hcan : cmon_plus A (cmon_map h a) (cmon_map h d)
                 ≈ cmon_plus A (cmon_map h c) (cmon_map h b)).
  { apply (ab_cancel_l A (cmon_map h k)
             (cmon_plus A (cmon_map h a) (cmon_map h d))
             (cmon_plus A (cmon_map h c) (cmon_map h b))).
    rewrite (cmon_plus_comm A (cmon_map h k)
               (cmon_plus A (cmon_map h a) (cmon_map h d))).
    rewrite (cmon_plus_comm A (cmon_map h k)
               (cmon_plus A (cmon_map h c) (cmon_map h b))).
    exact Hh. }
  apply groth_sub_cross.
  exact Hcan.
Qed.

Program Definition groth_extend : GrothendieckObject ~{Ab}~> A := {|
  cmon_map := {| morphism := groth_med |}
|}.
Next Obligation. exact groth_med_respects. Qed.
Next Obligation.
  unfold groth_med; simpl.
  rewrite (cmon_map_zero h).
  apply ab_sub_self.
Qed.
Next Obligation.
  intros [a b] [c d]; unfold groth_med; simpl.
  rewrite !(cmon_map_plus h).
  symmetry; apply ab_sub_plus.
Qed.

(* The triangle: restricting mediator 嵌入 recovers h. （已译） *)
Lemma groth_extend_insert (a : MC) :
  cmon_map groth_extend (cmon_map groth_insert a) ≈ cmon_map h a.
Proof.
  simpl; unfold groth_med; simpl.
  rewrite (cmon_map_zero h).
  apply ab_sub_zero_r.
Qed.

(*
   本节说明 Grothendieck 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma groth_pair_is_difference (a b : MC) :
  groth_rel (a, b)
    (ab_sub GrothendieckObject
       (cmon_map groth_insert a) (cmon_map groth_insert b)).
Proof.
  unfold ab_sub; simpl.
  exists (cmon_zero M); apply pequiv_from; simpl.
  now rewrite !cmon_plus_zero_l, !cmon_plus_zero_r.
Qed.

Lemma groth_extend_unique (g : GrothendieckObject ~{Ab}~> A)
  (Hg : ∀ a : MC, cmon_map g (cmon_map groth_insert a) ≈ cmon_map h a)
  (p : GrothPair) :
  cmon_map g p ≈ cmon_map groth_extend p.
Proof.
  destruct p as [a b].
  rewrite (proper_morphism (cmon_map g) _ _
             (groth_pair_is_difference a b)).
  rewrite (ab_map_sub g).
  rewrite (Hg a), (Hg b).
  simpl; unfold groth_med; reflexivity.
Qed.

End Extend.

Arguments groth_med {A} h p.
Arguments groth_extend {A} h.
Arguments groth_extend_insert {A} h a.
Arguments groth_extend_unique {A} h g Hg p.

(* The 普遍映射性质 shape [universal_arrow_from_UMP]
 wants: every [h : M ~> Ab_to_CMon A] factors uniquely through the
 嵌入. （已译） *)
Lemma groth_universal (A : Ab) (h : M ~{CMon}~> Ab_to_CMon A) :
  ∃! g : GrothendieckObject ~{Ab}~> A,
    h ≈ fmap[Ab_to_CMon] g ∘ groth_insert.
Proof.
  unshelve eexists.
  - exact (groth_extend h).
  - intro a; simpl; symmetry; exact (groth_extend_insert h a).
  - intros g Hg p; simpl.
    symmetry; apply (groth_extend_unique h g).
    intro a; symmetry; exact (Hg a).
Qed.

End Grothendieck.

(* 相关说明。 （已译） *)
Arguments groth_med {M A} h p.
Arguments groth_extend {M A} h.
Arguments groth_extend_insert {M A} h a.
Arguments groth_extend_unique {M A} h g Hg p.

Arguments GrothPair M : clear implicits.
Arguments groth_rel {M} p q.
Arguments groth_naive {M} p q.
Arguments groth_zero M : clear implicits.
Arguments groth_plus {M} p q.
Arguments groth_neg {M} p.

(** ** Strict readings of the data *)

Example groth_carrier (M : CMonObject) :
  carrier (cmon_setoid (GrothendieckObject M))
    = (carrier (cmon_setoid M) * carrier (cmon_setoid M))%type := eq_refl.

Example groth_zero_computes (M : CMonObject) :
  cmon_zero (GrothendieckObject M) = (cmon_zero M, cmon_zero M) := eq_refl.

Example groth_plus_computes (M : CMonObject)
  (a b c d : carrier (cmon_setoid M)) :
  cmon_plus (GrothendieckObject M) (a, b) (c, d)
    = (cmon_plus M a c, cmon_plus M b d) := eq_refl.

Example groth_neg_computes (M : CMonObject)
  (a b : carrier (cmon_setoid M)) :
  ab_neg (GrothendieckObject M) (a, b) = (b, a) := eq_refl.

Example groth_insert_computes (M : CMonObject)
  (a : carrier (cmon_setoid M)) :
  cmon_map (groth_insert M) a = (a, cmon_zero M) := eq_refl.

Example groth_extend_computes (M : CMonObject) (A : AbObject)
  (h : M ~{CMon}~> Ab_to_CMon A) (a b : carrier (cmon_setoid M)) :
  cmon_map (groth_extend h) (a, b)
    = ab_sub A (cmon_map h a) (cmon_map h b) := eq_refl.

(* * ** The 泛箭头, 左伴随 伴随 （已译） *)

Definition groth_universal_arrow (M : CMon)
  : UniversalArrow M Ab_to_CMon :=
  universal_arrow_from_UMP M Ab_to_CMon (GrothendieckObject M)
    (groth_insert M) (groth_universal M).

(* The same content direct encoding, where universal 对象 is
 named rather than projected out comma 范畴. （已译） *)
Program Definition groth_AUniversalArrow (M : CMon)
  : AUniversalArrow M Ab_to_CMon (GrothendieckObject M) := {|
  universal_arrow := groth_insert M
|}.
Next Obligation.
  intros M A h.
  unshelve eexists.
  - exact (groth_extend h).
  - intro a; simpl; exact (groth_extend_insert h a).
  - intros g Hg p; simpl.
    (* 相关说明。 （已译） *)
    symmetry; apply (groth_extend_unique h g).
    intro a; exact (Hg a).
Qed.

(* The 函子 伴随 come out generic machinery with
 no further 证明. （已译） *)
Definition GrothLeft : CMon ⟶ Ab :=
  LeftAdjointFunctorFromUniversalArrows Ab_to_CMon groth_universal_arrow.

Definition grothendieck_adjunction : GrothLeft ⊣ Ab_to_CMon :=
  AdjunctionFromUniversalArrows Ab_to_CMon groth_universal_arrow.

Example GrothLeft_obj (M : CMon) :
  GrothLeft M = GrothendieckObject M := eq_refl.

(* [universal_arrow_from_UMP] stores supplied 态射 second
 projection comma 对象 it builds, so 泛箭头 is
 嵌入 nose. （已译） *)
Example groth_arrow_is_insert (M : CMon) :
  @arrow _ _ M Ab_to_CMon (groth_universal_arrow M) = groth_insert M
  := eq_refl.

(* 相关说明。 （已译） *)

Definition groth_unit (M : CMon)
  : M ~{CMon}~> Ab_to_CMon (GrothLeft M) :=
  @Category.Theory.Adjunction.unit _ _ _ _ grothendieck_adjunction M.

Example groth_unit_is_insert (M : CMon) (a : carrier (cmon_setoid M)) :
  cmon_map (groth_unit M) a = (a, cmon_zero M) := eq_refl.

Definition groth_counit (A : Ab)
  : GrothLeft (Ab_to_CMon A) ~{Ab}~> A :=
  @Category.Theory.Adjunction.counit _ _ _ _ grothendieck_adjunction A.

(* 相关说明。 （已译） *)
Lemma groth_counit_generator (A : Ab)
  (a : carrier (cmon_setoid (Ab_to_CMon A))) :
  cmon_map (groth_counit A) (a, cmon_zero A) ≈ a.
Proof.
  exact (@to_adj_counit _ _ _ _ grothendieck_adjunction A a).
Qed.

Theorem groth_counit_evaluates (A : Ab)
  (p : GrothPair (Ab_to_CMon A)) :
  cmon_map (groth_counit A) p
    ≈ ab_sub A (fst p) (snd p).
Proof.
  destruct p as [a b].
  transitivity (cmon_map (groth_extend (@id CMon (Ab_to_CMon A)))
                  (a, b)).
  - apply (groth_extend_unique (@id CMon (Ab_to_CMon A))
             (groth_counit A)).
    intro x; exact (groth_counit_generator A x).
  - simpl; reflexivity.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition groth_map {M N : CMonObject} (f : M ~{CMon}~> N)
  : GrothendieckObject M ~{Ab}~> GrothendieckObject N := {|
  cmon_map := {| morphism := fun p : GrothPair M =>
                   (cmon_map f (fst p), cmon_map f (snd p)) |}
|}.
Next Obligation.
  intros M N f [a b] [c d] Hpq; simpl in Hpq |- *.
  destruct Hpq as [k Hk]; apply pequiv_to in Hk; simpl in Hk.
  exists (cmon_map f k); apply pequiv_from; simpl.
  rewrite <- !(cmon_map_plus f).
  now rewrite Hk.
Qed.
Next Obligation.
  intros M N f; simpl.
  exists (cmon_zero N); apply pequiv_from; simpl.
  now rewrite !(cmon_map_zero f).
Qed.
Next Obligation.
  intros M N f [a b] [c d]; simpl.
  exists (cmon_zero N); apply pequiv_from; simpl.
  now rewrite !(cmon_map_plus f).
Qed.

Program Definition GrothendieckFunctor : CMon ⟶ Ab := {|
  fobj := GrothendieckObject;
  fmap := @groth_map
|}.
Next Obligation.
  intros M N f g Hfg [a b]; simpl.
  exists (cmon_zero N); apply pequiv_from; simpl.
  now rewrite (Hfg a), (Hfg b).
Qed.
Next Obligation.
  intros M [a b]; simpl.
  exists (cmon_zero M); apply pequiv_from; simpl; reflexivity.
Qed.
Next Obligation.
  intros M N P f g [a b]; simpl.
  exists (cmon_zero P); apply pequiv_from; simpl; reflexivity.
Qed.

Example groth_functor_obj_agrees (M : CMon) :
  fobj[GrothendieckFunctor] M = fobj[GrothLeft] M := eq_refl.

Example groth_map_computes {M N : CMonObject} (f : M ~{CMon}~> N)
  (a b : carrier (cmon_setoid M)) :
  cmon_map (groth_map f) (a, b) = (cmon_map f a, cmon_map f b) := eq_refl.

(* 相关说明。 （已译） *)
Lemma groth_fmap_agrees {M N : CMon} (f : M ~{CMon}~> N) :
  fmap[GrothLeft] f ≈ fmap[GrothendieckFunctor] f.
Proof.
  (*
   本节说明 Grothendieck 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  apply (uniqueness (ump_universal_arrows (groth_universal_arrow M)
           (@arrow _ _ N Ab_to_CMon (groth_universal_arrow N) ∘ f))).
  intro a; simpl.
  exists (cmon_zero N); apply pequiv_from; simpl.
  now rewrite (cmon_map_zero f).
Qed.

(*
   本节说明 Grothendieck 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example groth_counit_not_strict (A : Ab)
  (a : carrier (cmon_setoid (Ab_to_CMon A))) :
  cmon_map (groth_counit A) (a, cmon_zero A) = a := eq_refl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example groth_fmap_not_strict (M N : CMon) (f : M ~{CMon}~> N) :
  fmap[GrothLeft] f = fmap[GrothendieckFunctor] f := eq_refl.

(*
   本节说明 Grothendieck 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example groth_difference_not_strict (M : CMonObject)
  (a b : carrier (cmon_setoid M)) :
  (a, b) = ab_sub (GrothendieckObject M)
             (cmon_map (groth_insert M) a) (cmon_map (groth_insert M) b)
  := eq_refl.

(* 相关说明。 （已译） *)
Fail Example groth_instrument_check : true = false := eq_refl.

(*
   本节说明 Grothendieck 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition groth_bool : CMonObject := rig_cmon Bool_Rig.

Theorem groth_naive_not_transitive :
  (∀ p q r : GrothPair groth_bool,
      @groth_naive groth_bool p q → @groth_naive groth_bool q r →
      @groth_naive groth_bool p r) → False.
Proof.
  intro Htrans.
  assert (H1 : @groth_naive groth_bool (false, false) (true, true)).
  { unfold groth_naive; simpl; reflexivity. }
  assert (H2 : @groth_naive groth_bool (true, true) (true, false)).
  { unfold groth_naive; simpl; reflexivity. }
  pose proof (Htrans _ _ _ H1 H2) as H3.
  unfold groth_naive in H3; simpl in H3.
  discriminate H3.
Qed.

(* And price: slack term, completion 幺半群 is
 trivial -- every two pairs related, taking [k := true]. （已译） *)
Theorem groth_bool_trivial (p q : GrothPair groth_bool) :
  @groth_rel groth_bool p q.
Proof.
  destruct p as [a b], q as [c d].
  exists true; apply pequiv_from; simpl.
  now rewrite !Bool.orb_true_r.
Qed.

Theorem groth_bool_insert_collapses :
  cmon_map (groth_insert groth_bool) true
    ≈ cmon_map (groth_insert groth_bool) false.
Proof. apply groth_bool_trivial. Qed.

(* 相关说明。 （已译） *)

Definition groth_nat : CMonObject := rig_cmon Nat_Rig.

(* The truncation 恒等 drives everything below: every
 integer, difference two truncations integer. （已译） *)
Lemma groth_Z_split (x : Z) :
  (Z.of_nat (Z.to_nat x) - Z.of_nat (Z.to_nat (- x)))%Z = x.
Proof.
  destruct x as [| p | p]; simpl.
  - reflexivity.
  - rewrite positive_nat_Z; lia.
  - rewrite positive_nat_Z; lia.
Qed.

Program Definition nat_to_Z : groth_nat ~{CMon}~> Ab_to_CMon ab_Z := {|
  cmon_map := {| morphism := fun n : nat => Z.of_nat n |}
|}.
(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Next Obligation. reflexivity. Qed.
Next Obligation. intros a b; simpl; apply Nat2Z.inj_add. Qed.

Definition groth_nat_to_Z
  : GrothendieckObject groth_nat ~{Ab}~> ab_Z :=
  groth_extend nat_to_Z.

Program Definition groth_Z_to_nat
  : ab_Z ~{Ab}~> GrothendieckObject groth_nat := {|
  cmon_map := {| morphism := fun n : Z => (Z.to_nat n, Z.to_nat (- n)) |}
|}.
(* 相关说明。 （已译） *)
Next Obligation. simpl; apply groth_rel_refl. Qed.
Next Obligation.
  intros m n; simpl.
  exists 0%nat; simpl.
  apply Nat2Z.inj.
  rewrite !Nat2Z.inj_add.
  pose proof (groth_Z_split m) as Hm.
  pose proof (groth_Z_split n) as Hn.
  pose proof (groth_Z_split (m + n)%Z) as Hmn.
  simpl; lia.
Qed.

(* The ℕ-level 恒等 behind section: stated separately so the
 同构 below closes conversion rather than hoping [simpl]
 exposes right term. （已译） *)
Lemma groth_Z_to_nat_section (a b : nat) :
  (Z.to_nat (Z.of_nat a - Z.of_nat b) + b + 0
     = a + Z.to_nat (- (Z.of_nat a - Z.of_nat b)) + 0)%nat.
Proof.
  rewrite !Nat.add_0_r.
  apply Nat2Z.inj.
  rewrite !Nat2Z.inj_add.
  pose proof (groth_Z_split (Z.of_nat a - Z.of_nat b)%Z) as Hs.
  lia.
Qed.

Theorem groth_nat_Z_iso : GrothendieckObject groth_nat ≅[Ab] ab_Z.
Proof.
  unshelve eexists.
  - exact groth_nat_to_Z.
  - exact groth_Z_to_nat.
  - intro n; simpl; unfold groth_med, ab_sub; simpl.
    pose proof (groth_Z_split n) as Hn.
    unfold Z_eqT; lia.
  - intros [a b]; simpl.
    exists 0%nat.
    apply pequiv_from.
    exact (groth_Z_to_nat_section a b).
Qed.

(* 相关说明。 （已译） *)

(* ℕ cancellative, so slack term buys nothing there the
 嵌入 injective -- completion does NOT collapse. （已译） *)
Theorem groth_nat_insert_injective (a b : nat) :
  cmon_map (groth_insert groth_nat) a
    ≈ cmon_map (groth_insert groth_nat) b → a = b.
Proof.
  intros [k Hk]; apply pequiv_to in Hk; simpl in Hk.
  lia.
Qed.

Theorem groth_nat_nontrivial :
  cmon_map (groth_insert groth_nat) 0%nat
    ≈ cmon_map (groth_insert groth_nat) 1%nat → False.
Proof.
  intro H.
  pose proof (groth_nat_insert_injective 0 1 H) as Heq.
  discriminate Heq.
Qed.

(* 相关说明。 （已译） *)
Example groth_nat_to_Z_computes (a b : nat) :
  cmon_map groth_nat_to_Z (a, b)
    = (Z.of_nat a - Z.of_nat b)%Z := eq_refl.

Theorem groth_nat_sign_separates :
  @groth_rel groth_nat (0%nat, 1%nat) (1%nat, 0%nat) → False.
Proof.
  intro H.
  pose proof (proper_morphism (cmon_map groth_nat_to_Z) _ _ H) as HZ.
  unfold Z_eqT in HZ; simpl in HZ.
  discriminate HZ.
Qed.
