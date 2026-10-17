Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Discrete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.

From Coq Require Import Eqdep_dec.

Generalizable All Variables.

Import EqNotations.

(* * * Reconstructing discrete 范畴 set 对象 （已译） *)

(*
 Reference: Saunders Mac Lane, "Categories for the Working Mathematician",
 Reference: Michael Hedberg, "A coherence theorem for Martin-Löf's type

   本文件给出离散范畴实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明伴随、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Transported identities *)

(* Composing transported identities transports along concatenated 证明. （已译） *)
Lemma rew_id_trans {C : Category} {x y z : C} (H : x = y) (H' : y = z) :
  rew H' in id ∘ rew H in id ≈ rew (eq_trans H H') in id.
Proof. destruct H, H'; cat. Qed.

(* A transported 恒等 invertible, inverse being 恒等
 transported along reversed 证明. （已译） *)
Lemma rew_id_iso_to {C : Category} {x y : C} (H : x = y) :
  rew (eq_sym H) in id ∘ rew H in id ≈ id.
Proof. destruct H; cat. Qed.

Lemma rew_id_iso_from {C : Category} {x y : C} (H : x = y) :
  rew H in id ∘ rew (eq_sym H) in id ≈ id.
Proof. destruct H; cat. Qed.

(** ** The comparison functor *)

(*
   本节说明 Reconstruct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Discrete_Compare@{o h p} (C : Category@{o h p}) :
  DiscreteCat@{o h p} C ⟶ C.
Proof.
  unshelve refine (@Build_Functor@{o h p o h p} (DiscreteCat@{o h p} C) C
    (fun x : C => x)
    (fun (x y : C) (e : x = y) => rew [fun z : C => x ~{C}~> z] e in id)
    _ _ _).
  (* [≈] on the source is [eq]; [rew eq_refl in id] is [id] *)
  - intros x y; proper; destruct X; reflexivity.
  - intros x; reflexivity.
  - intros x y z H H'; symmetry; apply rew_id_trans.
Defined.

(* The action 态射, [rew] shape used Structure/Discrete.v. （已译） *)
Lemma fmap_Discrete_Compare {C : Category} {x y : C} (e : x = y) :
  fmap[Discrete_Compare C] e ≈ rew e in id.
Proof. reflexivity. Qed.

(* Fullness exactly [Discrete] predicate: witness it produces an
 arrow [g] preimage [g] under [fmap]. No further 假设. （已译） *)
Program Definition Discrete_Compare_Full (C : Category) (D : Discrete C) :
  Full (Discrete_Compare C) := {|
  prefmap := fun x y g => `1 (D x y g)
|}.
Next Obligation. symmetry; exact (`2 (D x y g)). Qed.

(* * ** Rigidity: faithfulness comparison 函子 （已译） *)

(* The reconstruction 假设: equality 证明 recoverable the
 恒等 it transports. Equivalently (see below) comparison 函子 is
 faithful. （已译） *)
Definition DiscreteRigid (C : Category) : Type :=
  ∀ (x y : C) (H H' : x = y),
    fmap[Discrete_Compare C] H ≈ fmap[Discrete_Compare C] H' → H = H'.

(* The same condition spelled out without 函子. （已译） *)
Lemma DiscreteRigid_elementary (C : Category) :
  DiscreteRigid C ↔
    (∀ (x y : C) (H H' : x = y),
       (rew H in id : x ~> y) ≈ rew H' in id → H = H').
Proof. split; intros r x y H H'; exact (r x y H H'). Qed.

(* And in the library's vocabulary. *)
Lemma DiscreteRigid_Faithful (C : Category) :
  DiscreteRigid C ↔ Faithful (Discrete_Compare C).
Proof.
  split; intro r.
  - constructor; intros x y f g e; exact (r x y f g e).
  - intros x y H H' e; exact (@fmap_inj _ _ _ r x y H H' e).
Qed.

(* Uniqueness 恒等 proofs 对象 one sufficient condition:
 under it 假设 rigidity discarded outright. （已译） *)
Definition DiscreteRigid_UIP (C : Category)
  (uip : ∀ (x y : C) (H H' : x = y), H = H') : DiscreteRigid C :=
  fun x y H H' _ => uip x y H H'.

(* Decidable object equality is another, through Hedberg's theorem. *)
Definition DiscreteRigid_dec (C : Category)
  (dec : ∀ x y : C, {x = y} + {x <> y}) : DiscreteRigid C :=
  DiscreteRigid_UIP C (@UIP_dec (obj[C]) dec).

(* On discrete 范畴 comparison 函子 acts 恒等 on
 态射, since there [rew H id] reduces [H] itself. （已译） *)
Lemma DiscreteCat_rew_id {A : Type} {x y : A} (H : x = y) :
  fmap[Discrete_Compare (DiscreteCat A)] H = H.
Proof. destruct H; reflexivity. Qed.

(* Hence every [DiscreteCat A] rigid, every [A], no 假设 —
 gain over phrasing 定理 UIP. （已译） *)
Lemma DiscreteCat_Rigid (A : Type) : DiscreteRigid (DiscreteCat A).
Proof.
  intros x y H H' e.
  rewrite <- (DiscreteCat_rew_id H), <- (DiscreteCat_rew_id H').
  exact e.
Qed.

(* * ** The reconstruction 函子 correspondence （已译） *)

Section Reconstruction.

Context {C : Category}.
Context (Dis : Discrete C).
Context (rigid : DiscreteRigid C).

(* The equality 证明 [Discrete] attaches arrow. （已译） *)
Definition disc_eq {x y : C} (f : x ~> y) : x = y := `1 (Dis x y f).

(* ... and its defining property, in comparison-functor form. *)
Lemma disc_eq_spec {x y : C} (f : x ~> y) :
  f ≈ fmap[Discrete_Compare C] (disc_eq f).
Proof. exact (`2 (Dis x y f)). Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Discrete_Reconstruct : C ⟶ DiscreteCat C.
Proof using C Dis rigid.
  unshelve refine (@Build_Functor C (DiscreteCat C)
    (fun x : C => x) (fun (x y : C) (f : x ~> y) => disc_eq f) _ _ _).
  - intros x y; proper.
    apply rigid.
    now rewrite <- !disc_eq_spec.
  - intros x.
    apply rigid.
    rewrite <- disc_eq_spec.
    now rewrite fmap_id.
  - intros x y z f g.
    apply rigid.
    rewrite fmap_comp.
    now rewrite <- !disc_eq_spec.
Defined.

(*
   本节说明 Reconstruct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Discrete_iso : C ≅[StrictCat] DiscreteCat C.
Proof using C Dis rigid.
  unshelve refine (@Build_Isomorphism StrictCat C (DiscreteCat C)
    Discrete_Reconstruct (Discrete_Compare C) _ _).
  - exists (fun _ => eq_refl).
    intros x y f; simpl.
    apply rigid.
    now rewrite <- disc_eq_spec.
  - exists (fun _ => eq_refl).
    intros x y f.
    symmetry; exact (disc_eq_spec f).
Defined.

(*
   本节说明函子、同构、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Discrete_iso_Cat : C ≅[Cat] DiscreteCat C :=
  @Build_Isomorphism Cat C (DiscreteCat C)
    Discrete_Reconstruct (Discrete_Compare C)
    (strict_equiv_implies_fun_equiv _ _ (iso_to_from Discrete_iso))
    (strict_equiv_implies_fun_equiv _ _ (iso_from_to Discrete_iso)).

End Reconstruction.

(** ** The iso-robust restatement *)

(* Every arrow of a discrete category is invertible; no hypothesis needed. *)
Lemma Discrete_invertible (C : Category) (D : Discrete C)
  (x y : C) (f : x ~> y) :
  ∃ g : y ~> x, (f ∘ g ≈ id) ∧ (g ∘ f ≈ id).
Proof.
  destruct (D x y f) as [H Hf].
  exists (rew [fun z : C => y ~{C}~> z] (eq_sym H) in id).
  split; rewrite Hf.
  - apply rew_id_iso_from.
  - apply rew_id_iso_to.
Qed.

(* The 等价-respecting reading discreteness: hom-setoids are
 subsingletons every arrow invertible. No 对象 equality appears. （已译） *)
Definition DiscreteUpToIso (C : Category) : Type :=
  (∀ (x y : C) (f g : x ~> y), f ≈ g)
    ∧ (∀ (x y : C) (f : x ~> y), ∃ g : y ~> x, (f ∘ g ≈ id) ∧ (g ∘ f ≈ id)).

(* [Discrete] implies restatement once 对象 have UIP: two
 witnesses attached two parallel arrows then same 证明. （已译） *)
Theorem Discrete_DiscreteUpToIso (C : Category) (D : Discrete C)
  (uip : ∀ (x y : C) (H H' : x = y), H = H') : DiscreteUpToIso C.
Proof.
  split.
  - intros x y f g.
    destruct (D x y f) as [H Hf], (D x y g) as [H' Hg].
    rewrite Hf, Hg, (uip x y H H').
    reflexivity.
  - apply Discrete_invertible, D.
Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem DiscreteUpToIso_DiscreteCat (A : Type) :
  DiscreteUpToIso (DiscreteCat A) ↔ (∀ (x y : A) (p q : x = y), p = q).
Proof.
  split.
  - intros [sub _] x y p q; exact (sub x y p q).
  - intros uip; split.
    + intros x y f g; exact (uip x y f g).
    + intros x y f.
      exists (eq_sym f).
      split; destruct f; reflexivity.
Qed.

(*
   本节说明 Reconstruct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Discrete_DiscreteUpToIso_forces_UIP
  (K : ∀ C : Category, Discrete C → DiscreteUpToIso C) :
  ∀ (A : Type) (x y : A) (p q : x = y), p = q.
Proof.
  intro A.
  apply (fst (DiscreteUpToIso_DiscreteCat A)).
  apply K, DiscreteCat_Discrete.
Qed.

(* * ** The indiscrete 范畴 separates two predicates （已译） *)

(* One arrow between any two 对象; codiscrete/indiscrete 右伴随
 underlying-set 函子, included here separating
 witness. （已译） *)
(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Blurry (A : Type) : Category := {|
  obj     := A;
  hom     := fun x y => x = y;
  homset  := fun x y => {| equiv := fun _ _ => True |};
  id      := fun x => eq_refl;
  compose := fun x y z (g : y = z) (f : x = y) => eq_trans f g
|}.

Lemma Blurry_Discrete (A : Type) : Discrete (Blurry A).
Proof. intros x y f. exists f. exact I. Qed.

Lemma Blurry_Rigid_is_UIP (A : Type) :
  DiscreteRigid (Blurry A) → ∀ (x y : A) (p q : x = y), p = q.
Proof. intros r x y p q. exact (r x y p q I). Qed.

Theorem Discrete_DiscreteRigid_forces_UIP
  (K : ∀ C : Category, Discrete C → DiscreteRigid C) :
  ∀ (A : Type) (x y : A) (p q : x = y), p = q.
Proof.
  intros A. apply Blurry_Rigid_is_UIP. apply K, Blurry_Discrete.
Qed.

(*
   本节说明（余）极限、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Indiscrete@{o h p} (A : Type@{o}) : Category@{o h p} := {|
  obj     := A;
  hom     := fun _ _ => unit;
  homset  := fun x y => Morphism_equality@{o h p} x y;
  id      := fun _ => tt;
  compose := fun _ _ _ _ _ => tt
|}.
(* All 范畴 laws equations [unit] discharged default
 obligation tactic. （已译） *)

(* 相关说明。 （已译） *)
Lemma Indiscrete_DiscreteUpToIso (A : Type) : DiscreteUpToIso (Indiscrete A).
Proof.
  split.
  - intros x y f g; now destruct f, g.
  - intros x y f; exists tt; split; reflexivity.
Qed.

(*
   本节说明 Reconstruct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Indiscrete_bool_Discrete_absurd : Discrete (Indiscrete bool) → False.
Proof. intro D; destruct (D true false tt) as [H _]; discriminate. Qed.
