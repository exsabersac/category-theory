(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.

Generalizable All Variables.

(** ** Objects *)

(** A poset over setoid carrier: 关系 respects [≈], reflexive
 transitive, antisymmetric UP TO [≈]. （已译） *)
Record PosetObject := {
  pos_setoid :> SetoidObject;

  pos_le : carrier pos_setoid → carrier pos_setoid → Prop;

  pos_le_respects : Proper (equiv ==> equiv ==> iff) pos_le;

  pos_refl    : ∀ x, pos_le x x;
  pos_trans   : ∀ x y z, pos_le x y → pos_le y z → pos_le x z;
  pos_antisym : ∀ x y, pos_le x y → pos_le y x → x ≈ y
}.

#[export] Existing Instance pos_le_respects.

(** ** Morphisms *)

(** A monotone map: setoid 态射 preserving order. Respect [≈]
 comes [SetoidMorphism]; monotonicity added field. （已译） *)
Record MonoHom (P Q : PosetObject) := {
  mono_fn :> SetoidMorphism (pos_setoid P) (pos_setoid Q);
  mono_le : ∀ x y, pos_le P x y → pos_le Q (mono_fn x) (mono_fn y)
}.

Arguments mono_fn {P Q} _.
Arguments mono_le {P Q} _ _ _ _.

#[local] Obligation Tactic := idtac.

(** 本节：Monotone maps compared pointwise up codomain's [≈], in
 Instance/CMon.v Instance/Sets.v -- never Leibniz equality. （已译） *)
#[export]
Program Instance MonoHom_Setoid {P Q : PosetObject} : Setoid (MonoHom P Q) := {|
  equiv := fun f g => ∀ a, mono_fn f a ≈ mono_fn g a
|}.
Next Obligation.
  intros P Q. constructor.
  - intros f a; reflexivity.
  - intros f g Hfg a; symmetry; apply Hfg.
  - intros f g h Hfg Hgh a; transitivity (mono_fn g a); [apply Hfg|apply Hgh].
Qed.

(** Awodey's two closure facts: 恒等 monotone, composites of
 monotone maps monotone. Both [Next Obligation]s below, so they
 proved rather than assumed. （已译） *)
Program Definition mono_hom_id {P : PosetObject} : MonoHom P P := {|
  mono_fn := setoid_morphism_id
|}.
Next Obligation. intros P x y H; exact H. Qed.

Program Definition mono_hom_compose {P Q R : PosetObject}
        (g : MonoHom Q R) (f : MonoHom P Q) : MonoHom P R := {|
  mono_fn := setoid_morphism_compose (mono_fn g) (mono_fn f)
|}.
Next Obligation.
  intros P Q R g f x y H; simpl.
  apply (mono_le g), (mono_le f); exact H.
Qed.

Program Instance mono_hom_compose_respects {P Q R : PosetObject} :
  Proper (equiv ==> equiv ==> equiv) (@mono_hom_compose P Q R).
Next Obligation.
  intros P Q R g g' Hg f f' Hf a; simpl.
  transitivity (mono_fn g (mono_fn f' a)).
  - apply proper_morphism, Hf.
  - apply Hg.
Qed.

(** ** The category *)

Program Definition Pos : Category := {|
  obj     := PosetObject;
  hom     := MonoHom;
  homset  := @MonoHom_Setoid;
  id      := @mono_hom_id;
  compose := @mono_hom_compose;
  compose_respects := @mono_hom_compose_respects
|}.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.

(** The underlying-set 函子, forgetting order. （已译） *)
Program Definition Pos_Forget : Pos ⟶ Sets := {|
  fobj := fun P => pos_setoid P;
  fmap := fun _ _ f => mono_fn f
|}.
Next Obligation. intros P Q f g Hfg a; simpl; exact (Hfg a). Qed.
Next Obligation. intros P a; simpl; reflexivity. Qed.
Next Obligation. intros P Q R f g a; simpl; reflexivity. Qed.

(* 相关说明。 （已译） *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition pos_preorder (P : PosetObject)
  : RelationClasses.PreOrder (pos_le P).
Proof.
  constructor.
  - exact (pos_refl P).
  - intros x y z f g; exact (pos_trans P x y z f g).
Defined.

Definition PosetAsCategory (P : PosetObject) : Category :=
  Proset (pos_preorder P).

(** A monotone map induces a functor between the thin categories: on objects it
    is the map, on morphisms it is monotonicity, and every law is an equation
    between parallel morphisms in a thin target, hence free. *)
Program Definition MonotoneAsFunctor {P Q : PosetObject} (f : MonoHom P Q)
  : PosetAsCategory P ⟶ PosetAsCategory Q := {|
  fobj := fun x => mono_fn f x;
  fmap := fun x y h => mono_le f x y h
|}.
(* The file sets [Obligation Tactic := idtac] above, so these discharged
 explicitly rather than silently. All three equations between parallel
 态射 thin target, hence [I]. （已译） *)
Next Obligation. intros P Q f x y g h Hgh; exact I. Qed.
Next Obligation. intros P Q f x; exact I. Qed.
Next Obligation. intros P Q f x y z g h; exact I. Qed.

(** Sanity: induced 函子's 对象 action IS underlying map. （已译） *)
Example monotone_functor_fobj {P Q : PosetObject} (f : MonoHom P Q)
  (x : carrier (pos_setoid P)) :
  fobj[MonotoneAsFunctor f] x = mono_fn f x := eq_refl.
