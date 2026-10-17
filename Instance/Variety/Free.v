Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Comp.
Require Import Category.Instance.Variety.

Generalizable All Variables.

(* * * The free-algebra 伴随 variety （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/free+object
 Wikipedia: https://en.wikipedia.org/wiki/Free_object

   本文件给出自由构造相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Module UA := Category.Instance.Comp.UniversalAlgebra.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Obligation Tactic := idtac.

(* 相关说明。 （已译） *)

Section SetoidAlgs.

Context (S : UA.OpSignature).

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record SetoidOpAlgebra := {
  soa_obj : SetoidObject;
  soa_op  : ∀ o : UA.operation S, (UA.arity o → soa_obj) → soa_obj;
  soa_op_respects : ∀ (o : UA.operation S) (k1 k2 : UA.arity o → soa_obj),
    (∀ j, k1 j ≈ k2 j) → soa_op o k1 ≈ soa_op o k2;
  soa_prop : PropEquiv (is_setoid soa_obj)
}.

(* 相关说明。 （已译） *)
Definition soa_alg (A : SetoidOpAlgebra) : UA.OpAlgebra S :=
  UA.Build_OpAlgebra S (carrier (soa_obj A)) (soa_op A).

Record SAlgHom (A B : SetoidOpAlgebra) := {
  salg_map :> soa_obj A → soa_obj B;
  salg_respects : Proper (equiv ==> equiv) salg_map;
  salg_commute : ∀ (o : UA.operation S) (args : UA.arity o → soa_obj A),
    salg_map (soa_op A o args) ≈ soa_op B o (fun i => salg_map (args i))
}.

Arguments salg_map {_ _} _ _.
Arguments salg_respects {_ _} _.
Arguments salg_commute {_ _} _ _ _.

Program Definition SAlgHom_Setoid (A B : SetoidOpAlgebra) : Setoid (SAlgHom A B) := {|
  equiv := fun f g => ∀ x, salg_map f x ≈ salg_map g x
|}.
Next Obligation.
  intros A B; constructor; repeat intro.
  - reflexivity.
  - symmetry; auto.
  - transitivity (salg_map y x0); auto.
Qed.

Program Definition SAlg_id (A : SetoidOpAlgebra) : SAlgHom A A := {|
  salg_map := fun x => x
|}.
Next Obligation. intros A; repeat intro; auto. Qed.
Next Obligation. intros A o args; simpl; reflexivity. Qed.

Program Definition SAlg_comp (A B C : SetoidOpAlgebra)
  (f : SAlgHom B C) (g : SAlgHom A B) : SAlgHom A C := {|
  salg_map := fun x => salg_map f (salg_map g x)
|}.
Next Obligation.
  intros A B C f g x y Hxy.
  apply (salg_respects f), (salg_respects g), Hxy.
Qed.
(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Next Obligation.
  intros A B C f g o args; simpl.
  transitivity (salg_map f (soa_op B o (fun i => salg_map g (args i)))).
  - apply (salg_respects f), (salg_commute g).
  - apply (salg_commute f).
Qed.

Program Definition SetoidAlgs : Category := {|
  obj     := SetoidOpAlgebra;
  hom     := SAlgHom;
  homset  := SAlgHom_Setoid;
  id      := SAlg_id;
  compose := SAlg_comp
|}.
(* 相关说明。 （已译） *)
Next Obligation.
  simpl; intros A B C f f' Hf g g' Hg z.
  transitivity (salg_map f (salg_map g' z)).
  - apply (salg_respects f), Hg.
  - apply Hf.
Qed.
Next Obligation. repeat intro; simpl; reflexivity. Qed.
Next Obligation. repeat intro; simpl; reflexivity. Qed.
Next Obligation. repeat intro; simpl; reflexivity. Qed.
Next Obligation. repeat intro; simpl; reflexivity. Qed.

End SetoidAlgs.

Arguments soa_obj {_} _.
Arguments soa_op {_} _ _ _.
Arguments soa_op_respects {_} _ _ _ _ _.
Arguments soa_prop {_} _.
Arguments soa_alg {_} _.
Arguments salg_map {_ _ _} _ _.
Arguments salg_respects {_ _ _} _.
Arguments salg_commute {_ _ _} _ _ _.


(** ** Block B: the setoid variety *)

Section SVariety.

Context {S : UA.OpSignature}.
Context (E : UA.EqSignature S).

(* 相关说明。 （已译） *)
Definition ssatisfies (A : SetoidOpAlgebra S) : Type :=
  ∀ (e : UA.eq S E) (args : UA.eq_arity e → carrier (soa_obj A)),
    @UA.lhs S E (soa_alg A) e args ≈ @UA.rhs S E (soa_alg A) e args.

Definition SVariety_sub : Subcategory (SetoidAlgs S) :=
  @Build_Subcategory (SetoidAlgs S)
    ssatisfies
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition SVariety : Category := Sub (SetoidAlgs S) SVariety_sub.

Definition SVariety_Full : Full (SetoidAlgs S) SVariety_sub :=
  fun _ _ _ _ _ => I.

Definition SVariety_Incl : SVariety ⟶ SetoidAlgs S :=
  Incl (SetoidAlgs S) SVariety_sub.

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition SVariety_Forget : SVariety ⟶ Sets := {|
  fobj := fun A => soa_obj (`1 A);
  fmap := fun _ _ f => {| morphism := salg_map (`1 f) |}
|}.
Next Obligation. intros A B f; apply (salg_respects (`1 f)). Qed.
Next Obligation. repeat intro; simpl; auto. Qed.
Next Obligation. repeat intro; simpl; reflexivity. Qed.
Next Obligation. repeat intro; simpl; reflexivity. Qed.

Lemma SVariety_Forget_Faithful : Functor.Faithful SVariety_Forget.
Proof. construct; simpl in *; auto. Qed.

End SVariety.

Arguments ssatisfies {_} _ _.
Arguments SVariety {_} _.
Arguments SVariety_sub {_} _.
Arguments SVariety_Full {_} _.
Arguments SVariety_Incl {_} _.
Arguments SVariety_Forget {_} _.
Arguments SVariety_Forget_Faithful {_} _.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FreeVariety.

Context {S : UA.OpSignature}.
Context (E : UA.EqSignature S).
Context (X : SetoidObject).

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive tree_equiv : UA.Tree S X → UA.Tree S X → Prop :=
  | tc_gen : ∀ x y : X, x ≈ y →
      tree_equiv (UA.generator S X x) (UA.generator S X y)
  | tc_op : ∀ (o : UA.operation S) (k1 k2 : UA.arity o → UA.Tree S X),
      (∀ j, tree_equiv (k1 j) (k2 j)) →
      tree_equiv (UA.node S X o k1) (UA.node S X o k2)
  | tc_law : ∀ (e : UA.eq S E) (args : UA.eq_arity e → UA.Tree S X),
      tree_equiv (@UA.lhs S E (UA.Free S X) e args)
                 (@UA.rhs S E (UA.Free S X) e args)
  | tc_sym : ∀ t u, tree_equiv t u → tree_equiv u t
  | tc_trans : ∀ t u v, tree_equiv t u → tree_equiv u v → tree_equiv t v.

(* 相关说明。 （已译） *)
Fixpoint tc_refl (t : UA.Tree S X) : tree_equiv t t :=
  match t with
  | UA.generator _ _ x => tc_gen x x (reflexivity x)
  | UA.node _ _ o k    => tc_op o k k (fun j => tc_refl (k j))
  end.

Program Definition Tree_Setoid : Setoid (UA.Tree S X) := {|
  equiv := tree_equiv
|}.
Next Obligation.
  constructor.
  - exact tc_refl.
  - exact tc_sym.
  - exact tc_trans.
Qed.

Definition FreeSOA : SetoidOpAlgebra S := {|
  soa_obj := {| carrier := UA.Tree S X ; is_setoid := Tree_Setoid |};
  soa_op  := UA.node S X;
  soa_op_respects := tc_op;
  soa_prop := @PropEquiv_of_relation _ Tree_Setoid tree_equiv
                (fun _ _ h => h) (fun _ _ h => h)
|}.

(* The laws hold free algebra BY CONSTRUCTION — [tc_law] is
 literally satisfaction 证明, sense the
 congruence "generated E". （已译） *)
Definition FreeSOA_satisfies : ssatisfies E FreeSOA := tc_law.

Definition Free_Variety : SVariety E := (FreeSOA; FreeSOA_satisfies).

End FreeVariety.

Arguments tree_equiv {_} _ _ _ _.
Arguments tc_refl {_ _ _} _.
Arguments Tree_Setoid {_} _ _.
Arguments FreeSOA {_} _ _.
Arguments FreeSOA_satisfies {_} _ _.
Arguments Free_Variety {_} _ _.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FreeUP.

Context {S : UA.OpSignature}.
Context (E : UA.EqSignature S).
Context (X : SetoidObject).
Context (A : SVariety E).
Context (h : X ~{Sets}~> soa_obj (`1 A)).

Definition free_alg_ext : UA.Tree S X → soa_obj (`1 A) :=
  UA.induced_map S X (soa_alg (`1 A)) h.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma free_alg_ext_respects (t u : UA.Tree S X) :
  tree_equiv E X t u → free_alg_ext t ≈ free_alg_ext u.
Proof.
  intro D.
  apply (@pequiv_to _ _ (soa_prop (`1 A))).
  induction D as [ x y Hxy | o k1 k2 Hk IH | e args | t u D IH | t u v D1 IH1 D2 IH2 ].
  - apply pequiv_from; exact (proper_morphism h x y Hxy).
  - apply pequiv_from; apply (soa_op_respects (`1 A) o);
      intro j; exact (pequiv_to _ _ (IH j)).
  - apply pequiv_from; unfold free_alg_ext.
    (*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
    assert (HL : UA.induced_map S X (soa_alg (`1 A)) h
                   (@UA.lhs S E (UA.Free S X) e args)
                 = @UA.lhs S E (soa_alg (`1 A)) e
                     (fun i => UA.induced_map S X (soa_alg (`1 A)) h (args i)))
      by exact (@UA.lhs_natural S E (UA.Free S X) (soa_alg (`1 A))
                  (UA.induced_hom S X (soa_alg (`1 A)) h) e args).
    assert (HR : UA.induced_map S X (soa_alg (`1 A)) h
                   (@UA.rhs S E (UA.Free S X) e args)
                 = @UA.rhs S E (soa_alg (`1 A)) e
                     (fun i => UA.induced_map S X (soa_alg (`1 A)) h (args i)))
      by exact (@UA.rhs_natural S E (UA.Free S X) (soa_alg (`1 A))
                  (UA.induced_hom S X (soa_alg (`1 A)) h) e args).
    rewrite HL, HR.
    exact (`2 A e (fun i => UA.induced_map S X (soa_alg (`1 A)) h (args i))).
  - symmetry; exact IH.
  - transitivity (free_alg_ext u); assumption.
Qed.

Program Definition free_alg_hom : Free_Variety E X ~{SVariety E}~> A :=
  ({| salg_map := free_alg_ext |}; I).
Next Obligation. repeat intro; apply free_alg_ext_respects; assumption. Qed.
Next Obligation. intros o args; simpl; reflexivity. Qed.

(* 相关说明。 （已译） *)
Theorem free_alg_hom_unique (f g : Free_Variety E X ~{SVariety E}~> A) :
  (∀ x : X, salg_map (`1 f) (UA.generator S X x)
              ≈ salg_map (`1 g) (UA.generator S X x)) →
  f ≈ g.
Proof.
  intros Hgen t.
  induction t as [ x | o k IH ]; simpl.
  - exact (Hgen x).
  - transitivity (soa_op (`1 A) o (fun j => salg_map (`1 f) (k j))).
    + exact (salg_commute (`1 f) o k).
    + transitivity (soa_op (`1 A) o (fun j => salg_map (`1 g) (k j))).
      * apply (soa_op_respects (`1 A) o); exact IH.
      * symmetry; exact (salg_commute (`1 g) o k).
Qed.

End FreeUP.

Arguments free_alg_ext {_ _ _} _ _ _.
Arguments free_alg_hom {_ _ _} _ _.
(* 相关说明。 （已译） *)
Arguments free_alg_hom_unique {_ _ _} _ _ _ _.

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FreeAdjunction.

Context {S : UA.OpSignature}.
Context (E : UA.EqSignature S).

(* 相关说明。 （已译） *)
Program Definition free_unit (X : Sets) :
  X ~{Sets}~> SVariety_Forget E (Free_Variety E X) := {|
  morphism := UA.generator S X
|}.
Next Obligation. intros X x y Hxy; exact (tc_gen E X x y Hxy). Qed.

Definition FreeUA (X : Sets) : @UniversalArrow Sets (SVariety E) X (SVariety_Forget E).
Proof.
  unshelve eapply (universal_arrow_from_UMP X (SVariety_Forget E)
                     (Free_Variety E X) (free_unit X)).
  intros A h.
  unshelve econstructor.
  - exact (free_alg_hom A h).
  - simpl; intro x; reflexivity.
  - simpl; intros g Hg.
    (* 相关说明。 （已译） *)
    exact (free_alg_hom_unique A (free_alg_hom A h) g (fun x => Hg x)).
Defined.

Definition Free_Variety_Functor : Sets ⟶ SVariety E :=
  LeftAdjointFunctorFromUniversalArrows (SVariety_Forget E) FreeUA.

Definition Free_Variety_adjunction :
  Free_Variety_Functor ⊣ SVariety_Forget E :=
  AdjunctionFromUniversalArrows (SVariety_Forget E) FreeUA.

End FreeAdjunction.

Arguments free_unit {_} _ _.
Arguments FreeUA {_} _ _.
Arguments Free_Variety_Functor {_} _.
Arguments Free_Variety_adjunction {_} _.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Products.

Context {S : UA.OpSignature}.
Context (E : UA.EqSignature S).

Program Definition soa_prod_setoid (A B : SetoidOpAlgebra S) :
  Setoid (carrier (soa_obj A) * carrier (soa_obj B)) := {|
  equiv := fun p q => (fst p ≈ fst q) * (snd p ≈ snd q)
|}.
Next Obligation.
  intros A B; constructor; repeat intro.
  - split; reflexivity.
  - split; symmetry; apply X.
  - split; [ transitivity (fst y) | transitivity (snd y) ]; first [ apply X | apply X0 ].
Qed.

Definition soa_prod (A B : SetoidOpAlgebra S) : SetoidOpAlgebra S := {|
  soa_obj := {| carrier := carrier (soa_obj A) * carrier (soa_obj B)
              ; is_setoid := soa_prod_setoid A B |};
  soa_op  := fun o k => (soa_op A o (fun i => fst (k i)),
                         soa_op B o (fun i => snd (k i)));
  soa_op_respects := fun o k1 k2 H =>
    (soa_op_respects A o _ _ (fun j => fst (H j)),
     soa_op_respects B o _ _ (fun j => snd (H j)));
  soa_prop := @PropEquiv_of_relation _ (soa_prod_setoid A B)
    (fun p q => @pequiv _ _ (soa_prop A) (fst p) (fst q)
                /\ @pequiv _ _ (soa_prop B) (snd p) (snd q))
    (fun p q h => (pequiv_to _ _ (proj1 h), pequiv_to _ _ (proj2 h)))
    (fun p q h => conj (pequiv_from _ _ (fst h)) (pequiv_from _ _ (snd h)))
|}.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition soa_prod_exl (A B : SetoidOpAlgebra S) :
  UA.AlgHom (soa_alg (soa_prod A B)) (soa_alg A) := {| UA.map := fst |}.
Next Obligation. intros A B o args; reflexivity. Qed.

Program Definition soa_prod_exr (A B : SetoidOpAlgebra S) :
  UA.AlgHom (soa_alg (soa_prod A B)) (soa_alg B) := {| UA.map := snd |}.
Next Obligation. intros A B o args; reflexivity. Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem soa_prod_satisfies (A B : SetoidOpAlgebra S) :
  ssatisfies E A → ssatisfies E B → ssatisfies E (soa_prod A B).
Proof.
  intros HA HB e args.
  split.
  - assert (HL : fst (@UA.lhs S E (soa_alg (soa_prod A B)) e args)
                 = @UA.lhs S E (soa_alg A) e (fun i => fst (args i)))
      by exact (@UA.lhs_natural S E (soa_alg (soa_prod A B)) (soa_alg A)
                  (soa_prod_exl A B) e args).
    assert (HR : fst (@UA.rhs S E (soa_alg (soa_prod A B)) e args)
                 = @UA.rhs S E (soa_alg A) e (fun i => fst (args i)))
      by exact (@UA.rhs_natural S E (soa_alg (soa_prod A B)) (soa_alg A)
                  (soa_prod_exl A B) e args).
    rewrite HL, HR.
    exact (HA e (fun i => fst (args i))).
  - assert (HL : snd (@UA.lhs S E (soa_alg (soa_prod A B)) e args)
                 = @UA.lhs S E (soa_alg B) e (fun i => snd (args i)))
      by exact (@UA.lhs_natural S E (soa_alg (soa_prod A B)) (soa_alg B)
                  (soa_prod_exr A B) e args).
    assert (HR : snd (@UA.rhs S E (soa_alg (soa_prod A B)) e args)
                 = @UA.rhs S E (soa_alg B) e (fun i => snd (args i)))
      by exact (@UA.rhs_natural S E (soa_alg (soa_prod A B)) (soa_alg B)
                  (soa_prod_exr A B) e args).
    rewrite HL, HR.
    exact (HB e (fun i => snd (args i))).
Qed.

End Products.

Arguments soa_prod_setoid {_} _ _.
Arguments soa_prod_exl {_} _ _.
Arguments soa_prod_exr {_} _ _.
Arguments soa_prod {_} _ _.
Arguments soa_prod_satisfies {_} _ _ _ _ _ _ _.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem not_equationally_definable {S : UA.OpSignature}
  (P : SetoidOpAlgebra S → Type) (A B : SetoidOpAlgebra S)
  (HA : P A) (HB : P B) (Hprod : P (soa_prod A B) → False) :
  ∀ E : UA.EqSignature S,
    (∀ C : SetoidOpAlgebra S, P C → ssatisfies E C) →
    (∀ C : SetoidOpAlgebra S, ssatisfies E C → P C) →
    False.
Proof.
  intros E Hsound Hcomplete.
  apply Hprod, Hcomplete.
  exact (soa_prod_satisfies E A B (Hsound A HA) (Hsound B HB)).
Qed.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition CommMagmaFree (X : Sets) : SVariety CommEq := Free_Variety CommEq X.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CommMagmaFree_adjunction :
  Free_Variety_Functor CommEq ⊣ SVariety_Forget CommEq :=
  Free_Variety_adjunction CommEq.

Definition SGroupVariety : Category := SVariety UA.GroupEq.

Definition FreeGroupOn (X : Sets) : SGroupVariety := Free_Variety UA.GroupEq X.

Definition FreeGroup_adjunction :
  Free_Variety_Functor UA.GroupEq ⊣ SVariety_Forget UA.GroupEq :=
  Free_Variety_adjunction UA.GroupEq.

(* Every Leibniz algebra is a setoid algebra on the discrete setoid, so
   #440's objects embed here — but the passage costs the axiom, because
   [soa_op_respects] at [eq_Setoid] is exactly what extensionality
   supplies. *)
Definition leibniz_soa {S : UA.OpSignature} (A : UA.OpAlgebra S) :
  SetoidOpAlgebra S := {|
  soa_obj := {| carrier := UA.carrier A ; is_setoid := eq_Setoid (UA.carrier A) |};
  soa_op  := UA.op A;
  soa_op_respects := fun o k1 k2 H =>
    f_equal (UA.op A o) (functional_extensionality_dep k1 k2 H);
  soa_prop := eq_PropEquiv (UA.carrier A)
|}.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Inductive ring_op : Set := rzero | rone | radd | rmul.

Definition RingOp : UA.OpSignature := {|
  UA.operation := ring_op;
  UA.arity := fun o => match o with
                       | rzero | rone => UA.nullary
                       | radd | rmul  => UA.binary
                       end
|}.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition F2_op (o : UA.operation RingOp) : (UA.arity o → bool) → bool :=
  match o as o0 return (@UA.arity RingOp o0 → bool) → bool with
  | rzero => fun _ => false
  | rone  => fun _ => true
  | radd  => fun k => xorb (k UA.Fst) (k UA.Snd)
  | rmul  => fun k => andb (k UA.Fst) (k UA.Snd)
  end.

(* 相关说明。 （已译） *)
Program Definition F2 : SetoidOpAlgebra RingOp := {|
  soa_obj := {| carrier := bool ; is_setoid := eq_Setoid bool |};
  soa_op  := F2_op;
  soa_prop := eq_PropEquiv bool
|}.
Next Obligation.
  intros o k1 k2 H; destruct o as [ | | | ]; simpl in *; try reflexivity;
    rewrite (H UA.Fst), (H UA.Snd); reflexivity.
Qed.

Definition r_zero (A : SetoidOpAlgebra RingOp) : carrier (soa_obj A) :=
  soa_op A rzero (fun i => match i return carrier (soa_obj A) with end).

Definition r_one (A : SetoidOpAlgebra RingOp) : carrier (soa_obj A) :=
  soa_op A rone (fun i => match i return carrier (soa_obj A) with end).

Definition r_mul (A : SetoidOpAlgebra RingOp)
  (x y : carrier (soa_obj A)) : carrier (soa_obj A) :=
  soa_op A rmul (fun i => match i with UA.Fst => x | UA.Snd => y end).

Definition r_add (A : SetoidOpAlgebra RingOp)
  (x y : carrier (soa_obj A)) : carrier (soa_obj A) :=
  soa_op A radd (fun i => match i with UA.Fst => x | UA.Snd => y end).

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition HasDivision (A : SetoidOpAlgebra RingOp) : Type :=
  ∀ x : carrier (soa_obj A),
    (x ≈ r_zero A → False) → { y : carrier (soa_obj A) & r_mul A x y ≈ r_one A }.

Definition F2_HasDivision : HasDivision F2.
Proof.
  intros x Hx.
  destruct x.
  - exists true; reflexivity.
  - destruct (Hx eq_refl).
Defined.

(* 相关说明。 （已译） *)
Definition F2xF2_no_division : HasDivision (soa_prod F2 F2) → False.
Proof.
  intro HF.
  destruct (HF (true, false)) as [y Hy].
  - intro Hz; destruct Hz as [H1 H2]; simpl in H1; discriminate H1.
  - destruct Hy as [H1 H2]; simpl in H2; discriminate H2.
Defined.

Definition division_is_not_equationally_definable :
  ∀ E : UA.EqSignature RingOp,
    (∀ C : SetoidOpAlgebra RingOp, HasDivision C → ssatisfies E C) →
    (∀ C : SetoidOpAlgebra RingOp, ssatisfies E C → HasDivision C) →
    False :=
  not_equationally_definable HasDivision F2 F2
    F2_HasDivision F2_HasDivision F2xF2_no_division.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition IsField (A : SetoidOpAlgebra RingOp) : Type :=
  (((∀ x y z, r_add A (r_add A x y) z ≈ r_add A x (r_add A y z)) *
    (∀ x y, r_add A x y ≈ r_add A y x) *
    (∀ x, r_add A x (r_zero A) ≈ x) *
    (∀ x, { y & r_add A x y ≈ r_zero A }) *
    (∀ x y z, r_mul A (r_mul A x y) z ≈ r_mul A x (r_mul A y z)) *
    (∀ x y, r_mul A x y ≈ r_mul A y x) *
    (∀ x, r_mul A x (r_one A) ≈ x) *
    (∀ x y z, r_mul A x (r_add A y z) ≈ r_add A (r_mul A x y) (r_mul A x z)) *
    ((r_one A ≈ r_zero A) → False))
   * HasDivision A)%type.

Definition F2_IsField : IsField F2.
Proof.
  unfold IsField, HasDivision; simpl.
  refine ((((((((( _ , _ ) , _ ) , _ ) , _ ) , _ ) , _ ) , _ ) , _ ) , _ );
    try solve [ intros; repeat match goal with [ x : bool |- _ ] => destruct x end;
                simpl; reflexivity ].
  all: try solve [ intro x; exists x; destruct x; reflexivity ].
  all: try solve [ intro H; discriminate H ].
  all: try solve [ intros x Hx; destruct x;
                   [ exists true; reflexivity | destruct (Hx eq_refl) ] ].
Defined.

Definition F2xF2_not_field : IsField (soa_prod F2 F2) → False :=
  fun HF => F2xF2_no_division (snd HF).

Definition fields_are_not_a_variety :
  ∀ E : UA.EqSignature RingOp,
    (∀ C : SetoidOpAlgebra RingOp, IsField C → ssatisfies E C) →
    (∀ C : SetoidOpAlgebra RingOp, ssatisfies E C → IsField C) →
    False :=
  not_equationally_definable IsField F2 F2 F2_IsField F2_IsField F2xF2_not_field.
