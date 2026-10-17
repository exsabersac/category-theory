Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Par.
Require Import Category.Instance.Sets.Pointed.

Generalizable All Variables.

(** * Partial maps and pointed sets *)

(*
 nLab:      https://ncatlab.org/nlab/show/pointed+set
 Wikipedia: https://en.wikipedia.org/wiki/Partial_function

   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Part_Pointed_obj (A : SetoidObject) : PointedSetoid := {|
  pointed_setoid := {| carrier   := option (carrier A)
                     ; is_setoid := @option_setoid _ (is_setoid A) |};
  pt := Datatypes.None
|}.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition part_pointed_fun {A B : SetoidObject} (f : A ~{Part}~> B)
  (o : option (carrier A)) : option (carrier B) :=
  match o with
  | Datatypes.Some a => f a
  | Datatypes.None => Datatypes.None
  end.

Program Definition Part_Pointed_map {A B : SetoidObject} (f : A ~{Part}~> B) :
  SetoidMorphism (pointed_setoid (Part_Pointed_obj A))
                 (pointed_setoid (Part_Pointed_obj B)) := {|
  morphism := part_pointed_fun f
|}.
Next Obligation.
  intros A B f; simpl; intros o o' Hoo.
  unfold part_pointed_fun.
  destruct o as [a|], o' as [a'|]; simpl in *; try contradiction.
  - exact (proper_morphism f _ _ Hoo).
  - exact Hoo.
Qed.

Definition Part_Pointed_fmap {A B : SetoidObject} (f : A ~{Part}~> B) :
  Part_Pointed_obj A ~{PointedSets}~> Part_Pointed_obj B.
Proof.
  refine (Build_PointedMorphism _ _ (Part_Pointed_map f) _).
  reflexivity.
Defined.

Program Definition Part_to_Pointed : Part ⟶ PointedSets := {|
  fobj := Part_Pointed_obj;
  fmap := fun A B f => Part_Pointed_fmap f
|}.
Next Obligation.
  intros A B f g Hfg o.
  destruct o as [a|].
  - exact (Hfg a).
  - reflexivity.
Qed.
Next Obligation.
  intros A o.
  destruct o as [a|]; reflexivity.
Qed.
Next Obligation.
  intros A B C f g o.
  destruct o as [a|]; reflexivity.
Qed.

(* Faithfulness: two partial maps inducing the same pointed map already agree
   at every [Some a]. *)
Theorem Part_to_Pointed_Faithful : Faithful Part_to_Pointed.
Proof.
  constructor; intros A B f g Hfg a.
  exact (Hfg (Datatypes.Some a)).
Qed.

(* 相关说明。 （已译） *)
Program Definition Part_prefmap {A B : SetoidObject}
  (g : Part_Pointed_obj A ~{PointedSets}~> Part_Pointed_obj B) :
  A ~{Part}~> B := {|
  morphism := fun a => g (Datatypes.Some a)
|}.
Next Obligation.
  intros A B g; simpl; intros a a' Haa.
  exact (proper_morphism (pointed_map g)
           (Datatypes.Some a) (Datatypes.Some a') Haa).
Qed.

Program Definition Part_to_Pointed_Full : Full Part_to_Pointed := {|
  prefmap := fun A B g => Part_prefmap g
|}.
Next Obligation.
  intros A B g o.
  destruct o as [a|].
  - reflexivity.
  - symmetry.
    exact (preserves_pt g).
Qed.

(* * ** Essential surjectivity, 等价 （已译） *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PointedDecidablePt : Type := ∀ Z : PointedSetoid, DecidablePt Z.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Apart (Z : PointedSetoid) : SetoidObject := {|
  carrier   := ∃ z : carrier Z, ¬ (z ≈ pt Z);
  is_setoid := {| equiv := fun u v => `1 u ≈ `1 v |}
|}.
Next Obligation.
  intros Z.
  constructor.
  - intros u.
    reflexivity.
  - intros u v Huv.
    now symmetry.
  - intros u v w Huv Hvw.
    now transitivity (`1 v).
Qed.

Definition apart_to_fun (Z : PointedSetoid)
  (o : option (carrier (Apart Z))) : carrier Z :=
  match o with
  | Datatypes.Some u => `1 u
  | Datatypes.None => pt Z
  end.

Definition apart_from_fun (dec : PointedDecidablePt) (Z : PointedSetoid)
  (z : carrier Z) : option (carrier (Apart Z)) :=
  match dec Z z with
  | Datatypes.inl _ => Datatypes.None
  | Datatypes.inr n => Datatypes.Some (z; n)
  end.

Program Definition apart_to_map (Z : PointedSetoid) :
  SetoidMorphism (pointed_setoid (Part_Pointed_obj (Apart Z)))
                 (pointed_setoid Z) := {|
  morphism := apart_to_fun Z
|}.
Next Obligation.
  intros Z; simpl; intros o o' Hoo.
  unfold apart_to_fun.
  destruct o as [u|], o' as [u'|]; simpl in *; try contradiction.
  - exact Hoo.
  - reflexivity.
Qed.

Program Definition apart_from_map (dec : PointedDecidablePt) (Z : PointedSetoid) :
  SetoidMorphism (pointed_setoid Z)
                 (pointed_setoid (Part_Pointed_obj (Apart Z))) := {|
  morphism := apart_from_fun dec Z
|}.
Next Obligation.
  intros dec Z; simpl; intros z z' Hzz.
  unfold apart_from_fun.
  destruct (dec Z z) as [p|n], (dec Z z') as [p'|n'].
  - reflexivity.
  - destruct (n' (transitivity (symmetry Hzz) p)).
  - destruct (n (transitivity Hzz p')).
  - exact Hzz.
Qed.

Lemma apart_to_pt (Z : PointedSetoid) :
  apart_to_fun Z Datatypes.None ≈ pt Z.
Proof. reflexivity. Qed.

Lemma apart_from_pt (dec : PointedDecidablePt) (Z : PointedSetoid) :
  @equiv _ (@option_setoid _ (is_setoid (Apart Z)))
    (apart_from_fun dec Z (pt Z)) Datatypes.None.
Proof.
  unfold apart_from_fun.
  destruct (dec Z (pt Z)) as [p|n].
  - reflexivity.
  - refine (False_rect _ (n _)).
    reflexivity.
Qed.

Definition apart_to (Z : PointedSetoid) :
  Part_to_Pointed (Apart Z) ~{PointedSets}~> Z :=
  Build_PointedMorphism _ _ (apart_to_map Z) (apart_to_pt Z).

Definition apart_from (dec : PointedDecidablePt) (Z : PointedSetoid) :
  Z ~{PointedSets}~> Part_to_Pointed (Apart Z) :=
  Build_PointedMorphism _ _ (apart_from_map dec Z) (apart_from_pt dec Z).

Lemma apart_to_from (dec : PointedDecidablePt) (Z : PointedSetoid) :
  apart_to Z ∘ apart_from dec Z ≈ id.
Proof.
  intro z; simpl.
  unfold apart_from_fun.
  destruct (dec Z z) as [p|n]; simpl.
  - now symmetry.
  - reflexivity.
Qed.

Lemma apart_from_to (dec : PointedDecidablePt) (Z : PointedSetoid) :
  apart_from dec Z ∘ apart_to Z ≈ id.
Proof.
  intro o.
  destruct o as [u|]; simpl; unfold apart_from_fun.
  - destruct u as [z n]; simpl.
    destruct (dec Z z) as [p|n'].
    + refine (False_rect _ (n p)).
    + simpl.
      reflexivity.
  - destruct (dec Z (pt Z)) as [p|n].
    + reflexivity.
    + refine (False_rect _ (n _)).
      reflexivity.
Qed.

Definition apart_iso (dec : PointedDecidablePt) (Z : PointedSetoid) :
  Part_to_Pointed (Apart Z) ≅[PointedSets] Z :=
  @Build_Isomorphism PointedSets _ _ (apart_to Z) (apart_from dec Z)
    (apart_to_from dec Z) (apart_from_to dec Z).

Definition Part_to_Pointed_ESO (dec : PointedDecidablePt) :
  EssentiallySurjective Part_to_Pointed :=
  @Build_EssentiallySurjective Part PointedSets Part_to_Pointed
    Apart (apart_iso dec).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition pointed_part_equivalence (dec : PointedDecidablePt) :
  EquivalenceOfCategories Part_to_Pointed :=
  @FF_ESO_Equivalence Part PointedSets Part_to_Pointed
    Part_to_Pointed_Full Part_to_Pointed_Faithful (Part_to_Pointed_ESO dec).
