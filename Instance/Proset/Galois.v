(*
   本文件给出预序集相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Poset.
Require Import Category.Instance.Sets.

(* 相关说明。 （已译） *)
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Arith.PeanoNat.
From Coq Require Import Lia.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Thin (C : Category) : Type :=
  ∀ (x y : C) (f g : x ~> y), f ≈ g.

(** Every [Proset] is thin, by construction: its hom-setoid relates everything. *)
Lemma proset_thin {A : Type} {R : relation A} (P : PreOrder R)
  : Thin (Proset P).
Proof. intros x y f g; exact I. Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma thin_side_condition {C : Category} (H : Thin C) {x y : C} (f g : x ~> y) :
  f ≈ g.
Proof. apply H. Qed.

Corollary proset_side_conditions_vacuous {A : Type} {R : relation A}
  (P : PreOrder R) {x y : Proset P} (f g : x ~{Proset P}~> y) : f ≈ g.
Proof. exact I. Qed.

(*
   本节说明伴随、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Galois connections *)

(*
   本节说明 Galois 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record GaloisConnection {A B : Type} (RA : relation A) (RB : relation B) := {
  gal_l : A → B;
  gal_r : B → A;

  gal_mono_l : ∀ a a', RA a a' → RB (gal_l a) (gal_l a');
  gal_mono_r : ∀ b b', RB b b' → RA (gal_r b) (gal_r b');

  gal_to   : ∀ a b, RB (gal_l a) b → RA a (gal_r b);
  gal_from : ∀ a b, RA a (gal_r b) → RB (gal_l a) b
}.

Arguments gal_l {A B RA RB} _ _.
Arguments gal_r {A B RA RB} _ _.
Arguments gal_mono_l {A B RA RB} _ {a a'} _.
Arguments gal_mono_r {A B RA RB} _ {b b'} _.
Arguments gal_to {A B RA RB} _ a b _.
Arguments gal_from {A B RA RB} _ a b _.

(* * ** The bridge, forward: Galois connection yields 伴随 （已译） *)

Section Galois.

Context {A B : Type}.
Context {RA : relation A} {RB : relation B}.
Context (PA : PreOrder RA) (PB : PreOrder RB).
Context (G : GaloisConnection RA RB).

Program Definition GaloisFunctor_l : Proset PA ⟶ Proset PB := {|
  fobj := gal_l G;
  fmap := fun a a' h => gal_mono_l G h
|}.

Program Definition GaloisFunctor_r : Proset PB ⟶ Proset PA := {|
  fobj := gal_r G;
  fmap := fun b b' h => gal_mono_r G h
|}.

(*
   本节说明hom、同构、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition galois_adj_iso (a : Proset PA) (b : Proset PB) :
  @Isomorphism Sets
    {| carrier := @hom (Proset PB) (gal_l G a) b
     ; is_setoid := @homset (Proset PB) (gal_l G a) b |}
    {| carrier := @hom (Proset PA) a (gal_r G b)
     ; is_setoid := @homset (Proset PA) a (gal_r G b) |} := {|
  to   := {| morphism := gal_to G a b |};
  from := {| morphism := gal_from G a b |}
|}.

(** The 伴随. Every remaining field side condition thin
 范畴, so whole coherence burden discharged uniformly. （已译） *)
Program Definition GaloisAdjunction :
  @Adjunction (Proset PB) (Proset PA) GaloisFunctor_l GaloisFunctor_r := {|
  adj := galois_adj_iso
|}.

End Galois.

(* * ** The bridge, backward: 伴随 between preorders Galois connection （已译） *)

Section Ungalois.

Context {A B : Type}.
Context {RA : relation A} {RB : relation B}.
Context (PA : PreOrder RA) (PB : PreOrder RB).
Context (F : Proset PA ⟶ Proset PB) (U : Proset PB ⟶ Proset PA).
Context (Adj : F ⊣ U).

Definition GaloisOfAdjunction : GaloisConnection RA RB :=
  {| gal_l := fobj[F]
   ; gal_r := fobj[U]
     (* [fmap]'s 对象 arguments given explicitly: leaving them implicit
 strands them evars, since record field's own arguments were made
 implicit above. （已译） *)
   ; gal_mono_l := fun a a' h => @fmap _ _ F a a' h
   ; gal_mono_r := fun b b' h => @fmap _ _ U b b' h
   ; gal_to   := fun a b h => to   (@adj _ _ _ _ Adj a b) h
   ; gal_from := fun a b h => from (@adj _ _ _ _ Adj a b) h |}.

End Ungalois.

(* * ** Poset: same 范畴, what costs （已译） *)

(** Instance/Poset.v defines [Poset] [Proset] antisymmetry
 论元 discarded, so two SAME 范畴 -- definitionally. （已译） *)
Lemma poset_is_proset {A : Type} {R : relation A}
  (P : PreOrder R) (AS : @Antisymmetric A eq eq_equiv R) :
  @Poset A R P AS = @Proset A R P.
Proof. reflexivity. Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma mutual_le_to_eq {A : Type} {R : relation A} (P : PreOrder R)
  (AS : @Antisymmetric A eq eq_equiv R) {x y : Proset P}
  (i : x ≅[Proset P] y) : x = y.
Proof. exact (AS x y (to i) (from i)). Qed.

(* 相关说明。 （已译） *)

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma galois_round_trip {A B : Type} {RA : relation A} {RB : relation B}
  (PA : PreOrder RA) (PB : PreOrder RB) (G : GaloisConnection RA RB) :
  gal_l (GaloisOfAdjunction PA PB _ _ (GaloisAdjunction PA PB G)) = gal_l G
  ∧ gal_r (GaloisOfAdjunction PA PB _ _ (GaloisAdjunction PA PB G)) = gal_r G.
Proof. split; reflexivity. Qed.

(*
   本节说明伴随、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition nat_shift_galois (k : nat)
  : GaloisConnection Nat.le Nat.le := {|
  gal_l := fun n => Nat.sub n k;
  gal_r := fun m => Nat.add m k
|}.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.

Definition nat_shift_adjunction (k : nat) : _ :=
  GaloisAdjunction Nat.le_preorder Nat.le_preorder (nat_shift_galois k).

(** The witness not degenerate: two maps genuinely differ [k > 0],
 so 这是 not 恒等 connection wearing disguise. （已译） *)
(* The two maps genuinely different functions, so 这是 not 恒等
 connection disguise. [%nat] needed: library's own scopes shadow
 numeral notation. （已译） *)
Example nat_shift_differ :
  gal_l (nat_shift_galois 1%nat) 3%nat = 2%nat := eq_refl.
Example nat_shift_differ_r :
  gal_r (nat_shift_galois 1%nat) 3%nat = 4%nat := eq_refl.

(* 相关说明。 （已译） *)

(*
   本节说明 Galois 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UnitCounit.

Context {A B : Type}.
Context {RA : relation A} {RB : relation B}.
Context (G : GaloisConnection RA RB).

Definition gal_unit (PB : PreOrder RB) (a : A) : RA a (gal_r G (gal_l G a)) :=
  gal_to G a (gal_l G a) (@reflexivity B RB (@PreOrder_Reflexive B RB PB) _).

Definition gal_counit (PA : PreOrder RA) (b : B) : RB (gal_l G (gal_r G b)) b :=
  gal_from G (gal_r G b) b (@reflexivity A RA (@PreOrder_Reflexive A RA PA) _).

End UnitCounit.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition galois_of_unit_counit {A B : Type}
  {RA : relation A} {RB : relation B}
  (PA : PreOrder RA) (PB : PreOrder RB)
  (l : A → B) (r : B → A)
  (ml : ∀ a a', RA a a' → RB (l a) (l a'))
  (mr : ∀ b b', RB b b' → RA (r b) (r b'))
  (unit   : ∀ a, RA a (r (l a)))
  (counit : ∀ b, RB (l (r b)) b)
  : GaloisConnection RA RB :=
  {| gal_l := l
   ; gal_r := r
   ; gal_mono_l := ml
   ; gal_mono_r := mr
     (* f a ⊑ b  gives  a ≤ r (f a) ≤ r b *)
   ; gal_to := fun a b h =>
       @transitivity A RA (@PreOrder_Transitive A RA PA) _ _ _
         (unit a) (mr _ _ h)
     (* a ≤ r b  gives  f a ⊑ f (r b) ⊑ b *)
   ; gal_from := fun a b h =>
       @transitivity B RB (@PreOrder_Transitive B RB PB) _ _ _
         (ml _ _ h) (counit b) |}.

(* 相关说明。 （已译） *)

(* * Seven Sketches §1.4.3 exercise 1.110: two left adjoints of the same map
    agree, and dually.  In an order "agree" is mutual comparability -- which is
    equality only under antisymmetry, so both forms are given.（标题）（已译） *)
Lemma gal_left_unique {A B : Type} {RA : relation A} {RB : relation B}
  (PB : PreOrder RB)
  (G G' : GaloisConnection RA RB)
  (Hr : ∀ b, gal_r G b = gal_r G' b) (a : A)
  : RB (gal_l G a) (gal_l G' a) * RB (gal_l G' a) (gal_l G a).
Proof.
  split.
  - apply (gal_from G a (gal_l G' a)).
    rewrite Hr. exact (gal_unit G' PB a).
  - apply (gal_from G' a (gal_l G a)).
    rewrite <- Hr. exact (gal_unit G PB a).
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition NatSucc : Proset Nat.le_preorder ⟶ Proset Nat.le_preorder := {|
  fobj := S;
  fmap := fun x y (h : Nat.le x y) => _
|}.
Next Obligation. lia. Qed.

Theorem succ_not_self_adjoint :
  @Adjunction (Proset Nat.le_preorder) (Proset Nat.le_preorder) NatSucc NatSucc
    → False.
Proof.
  intro Adj.
  (* to (adj 0 0) turns [S 0 ≤ 0] into [0 ≤ S 0]; the reverse direction turns
     [0 ≤ S 0] into [S 0 ≤ 0], which is absurd. *)
  pose proof (from (@adj _ _ _ _ Adj 0%nat 0%nat)) as H.
  simpl in H.
  assert (Nat.le 0 (S 0)) as H0 by lia.
  pose proof (H H0) as Hbad.
  simpl in Hbad.
  lia.
Qed.
