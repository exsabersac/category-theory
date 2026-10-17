Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.End.
Require Import Category.Structure.Coend.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Coends in [Sets] *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Coend

   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SetsCoend.

Context {C : Category}.
Context (F : C^op ∏ C ⟶ Sets).

(** Elements: one summand per object [x], namely [F (x, x)]. *)
Inductive coend_sum : Type :=
  | ci : forall x : C, F (x, x) -> coend_sum.

(*
   本节说明等价、（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive coend_eq : coend_sum -> coend_sum -> Type :=
  | ce_point : forall (x : C) (a b : F (x, x)),
      a ≈ b -> coend_eq (ci x a) (ci x b)
  | ce_glue  : forall (x y : C) (f : x ~{C}~> y) (a : F (y, x)),
      coend_eq (ci x (bimap[F] (op f) id a)) (ci y (bimap[F] id f a))
  | ce_sym   : forall s t : coend_sum, coend_eq s t -> coend_eq t s
  | ce_trans : forall s t u : coend_sum,
      coend_eq s t -> coend_eq t u -> coend_eq s u.

(** Reflexivity comes from [ce_point] applied to the fibre setoid's own
    reflexivity. *)
Lemma coend_eq_refl (s : coend_sum) : coend_eq s s.
Proof.
  destruct s as [x a].
  apply ce_point; reflexivity.
Qed.

(** The coend apex as a [SetoidObject]. *)
Program Definition coend_apex_setoid : SetoidObject :=
  {| carrier := coend_sum;
     is_setoid := {| equiv := coend_eq; setoid_equiv := _ |} |}.
Next Obligation.
  constructor.
  - intros s. apply coend_eq_refl.
  - intros s t H. apply ce_sym; exact H.
  - intros s t u H1 H2. eapply ce_trans; [ exact H1 | exact H2 ].
Qed.

(** The injection leg at [x]: send [a : F (x, x)] to [ci x a].  It respects
    the fibre equivalence by [ce_point]. *)
Program Definition coend_inj_mor (x : C) :
  SetoidMorphism (F (x, x)) coend_apex_setoid :=
  {| morphism := fun a => ci x a |}.
Next Obligation.
  unfold Proper, respectful; intros a b Hab.
  apply ce_point; exact Hab.
Qed.

(** The universal cowedge condition of the injections is exactly [ce_glue],
    read pointwise. *)
Lemma coend_apex_cowedge :
  Cowedge_cond F coend_apex_setoid coend_inj_mor.
Proof.
  intros x y f a.
  exact (ce_glue x y f a).
Qed.

(** The underlying function of the mediator into a competing cowedge [(Q, i')]:
    send [ci x a] to [i' x a]. *)
Definition coend_med_fun {Q : SetoidObject}
  (i' : forall x : C, SetoidMorphism (F (x, x)) Q) (s : coend_sum) : Q :=
  match s with ci x a => i' x a end.

(*
   本节说明等价、（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma coend_med_respects {Q : SetoidObject}
  (i' : forall x : C, SetoidMorphism (F (x, x)) Q)
  (cond' : Cowedge_cond F Q i')
  (s t : coend_sum) (H : coend_eq s t) :
  coend_med_fun i' s ≈ coend_med_fun i' t.
Proof.
  induction H as
    [ x a b Hab
    | x y f a
    | s1 s2 Hs IH
    | s1 s2 s3 Hs1 IH1 Hs2 IH2 ].
  - simpl. apply proper_morphism; exact Hab.
  - exact (cond' x y f a).
  - symmetry; exact IH.
  - transitivity (coend_med_fun i' s2); [ exact IH1 | exact IH2 ].
Qed.

(** The mediator as a setoid map [coend_apex ~> Q]. *)
Program Definition coend_mediator {Q : SetoidObject}
  (i' : forall x : C, SetoidMorphism (F (x, x)) Q)
  (cond' : Cowedge_cond F Q i') :
  SetoidMorphism coend_apex_setoid Q :=
  {| morphism := coend_med_fun i' |}.
Next Obligation.
  unfold Proper, respectful; intros s t Hst.
  exact (coend_med_respects i' cond' s t Hst).
Qed.

(*
   本节说明（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition SetsCoend : Coend F.
Proof.
  unshelve refine
    (@Build_Coend C Sets F coend_apex_setoid coend_inj_mor coend_apex_cowedge _).
  intros Q i' cond'.
  unshelve refine
    (Build_Unique _ _ _ (coend_mediator i' cond') _ _).
  - intros x a. reflexivity.
  - intros v Hv s.
    destruct s as [x a].
    symmetry.
    exact (Hv x a).
Defined.

End SetsCoend.

Arguments coend_sum {C} F.
Arguments coend_eq {C} F _ _.
Arguments coend_apex_setoid {C} F.
Arguments coend_inj_mor {C} F x.
Arguments coend_med_fun {C} F {Q} i' s.
Arguments coend_mediator {C} F {Q} i' cond'.
Arguments SetsCoend {C} F.
