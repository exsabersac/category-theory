Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.ZeroObject.

Generalizable All Variables.

(** * The category of pointed sets *)

(*
 nLab:      https://ncatlab.org/nlab/show/pointed+object
 Wikipedia: https://en.wikipedia.org/wiki/Pointed_set
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Book:      Awodey, "Category Theory", 2nd ed., OUP 2010, §1.6 Example 1.8
 Book:      Awodey, "Category Theory", 1st ed., OUP 2006, §7.9 Example 7.26

   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:      https://ncatlab.org/nlab/show/axiom+of+choice
   nLab:      https://ncatlab.org/nlab/show/split+epimorphism
   Wikipedia: https://en.wikipedia.org/wiki/Axiom_of_choice

   本节说明 Pointed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* A pointed setoid: a Bishop set together with a distinguished element. *)
Record PointedSetoid := {
  pointed_setoid :> SetoidObject;
  pt : carrier pointed_setoid
}.

(* 相关说明。 （已译） *)
Record PointedMorphism (X Y : PointedSetoid) := {
  pointed_map :> SetoidMorphism (pointed_setoid X) (pointed_setoid Y);
  preserves_pt : pointed_map (pt X) ≈ pt Y
}.

Arguments pointed_map {X Y} _.
Arguments preserves_pt {X Y} _.

#[local] Obligation Tactic := idtac.

(* The hom-setoid: two pointed maps agree when their underlying setoid maps
   agree pointwise, exactly as in [Sets]. *)
#[export]
Program Instance PointedMorphism_Setoid {X Y : PointedSetoid} :
  Setoid (PointedMorphism X Y) := {|
  equiv := fun f g => ∀ x, pointed_map f x ≈ pointed_map g x
|}.
Next Obligation.
  intros X Y.
  constructor.
  - intros f x.
    reflexivity.
  - intros f g Hfg x.
    symmetry.
    apply Hfg.
  - intros f g h Hfg Hgh x.
    transitivity (pointed_map g x).
    + apply Hfg.
    + apply Hgh.
Qed.

(* The identity pointed map. *)
Program Definition pointed_id {X : PointedSetoid} : PointedMorphism X X := {|
  pointed_map := setoid_morphism_id
|}.
Next Obligation.
  intros X; simpl.
  reflexivity.
Qed.

(* Composition of pointed maps: the basepoint travels through both. *)
Program Definition pointed_compose {X Y Z : PointedSetoid}
        (f : PointedMorphism Y Z) (g : PointedMorphism X Y) :
  PointedMorphism X Z := {|
  pointed_map := setoid_morphism_compose (pointed_map f) (pointed_map g)
|}.
Next Obligation.
  intros X Y Z f g; simpl.
  unfold Basics.compose.
  rewrite (preserves_pt g).
  apply (preserves_pt f).
Qed.

Lemma pointed_compose_respects {X Y Z : PointedSetoid} :
  Proper (equiv ==> equiv ==> equiv) (@pointed_compose X Y Z).
Proof.
  intros f f' Hf g g' Hg x; simpl.
  unfold Basics.compose.
  rewrite (Hg x).
  apply Hf.
Qed.

(* The category of pointed sets, Mac Lane's Set_*.

       objects: pointed setoids            (a Bishop set with a basepoint)
        arrows: basepoint-preserving maps  (f (pt X) ≈ pt Y)
      identity: the identity setoid map
   composition: composition of setoid maps *)
Program Definition PointedSets : Category := {|
  obj     := PointedSetoid;
  hom     := PointedMorphism;
  homset  := @PointedMorphism_Setoid;
  id      := @pointed_id;
  compose := @pointed_compose;

  compose_respects := @pointed_compose_respects
|}.
Next Obligation. intros X Y f x; simpl; reflexivity. Qed.
Next Obligation. intros X Y f x; simpl; reflexivity. Qed.
Next Obligation. intros X Y Z W f g h x; simpl; reflexivity. Qed.
Next Obligation. intros X Y Z W f g h x; simpl; reflexivity. Qed.

(* * ** The zero 对象: single point, both initial terminal （已译） *)

(* The one-point pointed set: [poly_unit] under `=`, pointed at its only
   element.  It plays both universal roles below. *)
Definition PointedOne : PointedSetoid := {|
  pointed_setoid := {| carrier := poly_unit |};
  pt := ttt
|}.

(*
   本节说明 Pointed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition const_pt_map (X Y : PointedSetoid) :
  SetoidMorphism (pointed_setoid X) (pointed_setoid Y) := {|
  morphism := fun _ => pt Y
|}.
Next Obligation. intros X Y; proper. Qed.

Definition pointed_const {X Y : PointedSetoid} : PointedMorphism X Y.
Proof.
  refine (Build_PointedMorphism X Y (const_pt_map X Y) _).
  simpl.
  reflexivity.
Defined.

(* Into one-point set there exactly one map: everything goes the
 element, 对象's basepoint. （已译） *)
Definition pointed_one {X : PointedSetoid} : PointedMorphism X PointedOne :=
  @pointed_const X PointedOne.

Lemma pointed_one_unique {X : PointedSetoid}
  (f g : PointedMorphism X PointedOne) : f ≈ g.
Proof.
  intro x.
  (* 相关说明。 （已译） *)
  simpl.
  destruct (pointed_map f x), (pointed_map g x).
  reflexivity.
Qed.

Definition PointedSets_Terminal : @Terminal PointedSets :=
  @Build_Terminal PointedSets PointedOne
    (fun X => @pointed_one X) (fun X => @pointed_one_unique X).

(*
   本节说明始/终对象、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition pointed_zero {X : PointedSetoid} : PointedMorphism PointedOne X :=
  @pointed_const PointedOne X.

Lemma pointed_zero_unique {X : PointedSetoid}
  (f g : PointedMorphism PointedOne X) : f ≈ g.
Proof.
  intro u.
  simpl.
  destruct u.
  transitivity (pt X).
  - exact (preserves_pt f).
  - symmetry.
    exact (preserves_pt g).
Qed.

Definition PointedSets_Initial : @Initial PointedSets :=
  @Build_Terminal (PointedSets^op) PointedOne
    (fun X => @pointed_zero X) (fun X => @pointed_zero_unique X).

(*
   本节说明hom、同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance PointedSets_Zero : ZeroObject PointedSets :=
  @Build_ZeroObject PointedSets PointedSets_Terminal PointedSets_Initial iso_id.

(* 相关说明。 （已译） *)

(* [f] is injective when it separates points up to `≈`. *)
Definition PointedInjective {X Y : PointedSetoid}
  (f : PointedMorphism X Y) : Type :=
  ∀ a b : carrier X, f a ≈ f b → a ≈ b.

(* 相关说明。 （已译） *)
Definition InImage {X Y : PointedSetoid}
  (f : PointedMorphism X Y) (y : carrier Y) : Type :=
  ∃ x : carrier X, f x ≈ y.

(* [f] is surjective when every point of the codomain is in its image. *)
Definition PointedSurjective {X Y : PointedSetoid}
  (f : PointedMorphism X Y) : Type :=
  ∀ b : carrier Y, InImage f b.

(* 相关说明。 （已译） *)
Lemma InImage_respects {X Y : PointedSetoid} (f : PointedMorphism X Y)
  {y y' : carrier Y} : y ≈ y' → InImage f y → InImage f y'.
Proof.
  intros Hyy [x Hx].
  exists x.
  now rewrite Hx.
Qed.

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma InImage_pt {X Y : PointedSetoid} (f : PointedMorphism X Y) :
  InImage f (pt Y).
Proof.
  exists (pt X).
  apply preserves_pt.
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Pointed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PointedTwo : PointedSetoid := {|
  pointed_setoid := {| carrier := option poly_unit |};
  pt := Datatypes.None
|}.

Program Definition probe_map {X : PointedSetoid} (x : carrier X) :
  SetoidMorphism (pointed_setoid PointedTwo) (pointed_setoid X) := {|
  morphism := fun o => match o with
                       | Datatypes.Some _ => x
                       | Datatypes.None => pt X
                       end
|}.
Next Obligation.
  intros X x; simpl; intros a b Hab.
  destruct a, b; simpl in *; try contradiction; reflexivity.
Qed.

(* The probe at [x]: basepoint to basepoint, free point to [x]. *)
Definition pointed_probe {X : PointedSetoid} (x : carrier X) :
  PointedMorphism PointedTwo X.
Proof.
  refine (Build_PointedMorphism PointedTwo X (probe_map x) _).
  simpl.
  reflexivity.
Defined.

(*
   本节说明 Pointed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem pointed_monic_iff {X Y : PointedSetoid}
  (f : X ~{PointedSets}~> Y) : PointedInjective f ↔ Monic f.
Proof.
  split.
  - intros Hinj.
    constructor; intros Z g1 g2 Hg z; simpl in *.
    apply Hinj.
    exact (Hg z).
  - intros [Hmonic] a b Hab.
    specialize (Hmonic PointedTwo (pointed_probe a) (pointed_probe b)).
    simpl in Hmonic.
    refine (Hmonic _ (Datatypes.Some ttt)).
    intros [u|]; simpl.
    + exact Hab.
    + reflexivity.
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CP_rel {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (u v : carrier Y + carrier Y) : Type :=
  match u, v with
  | Datatypes.inl a, Datatypes.inl b => a ≈ b
  | Datatypes.inr a, Datatypes.inr b => a ≈ b
  | Datatypes.inl a, Datatypes.inr b => (a ≈ b) ∧ InImage f a
  | Datatypes.inr a, Datatypes.inl b => (a ≈ b) ∧ InImage f a
  end.

Program Definition CP_setoid {X Y : PointedSetoid} (f : PointedMorphism X Y) :
  Setoid (carrier Y + carrier Y) := {|
  equiv := CP_rel f
|}.
Next Obligation.
  intros X Y f.
  constructor.
  - intros [a|a]; simpl; reflexivity.
  - intros [a|a] [b|b]; simpl; intros H.
    + now symmetry.
    + destruct H as [Hab Him].
      split.
      * now symmetry.
      * exact (InImage_respects f Hab Him).
    + destruct H as [Hab Him].
      split.
      * now symmetry.
      * exact (InImage_respects f Hab Him).
    + now symmetry.
  - intros [a|a] [b|b] [c|c]; simpl; intros H1 H2.
    (* inl a ~ inl b ~ inl c *)
    + now transitivity b.
    (* inl a ~ inl b ~ inr c: the image membership travels back along H1 *)
    + destruct H2 as [Hbc Him].
      split.
      * now transitivity b.
      * exact (InImage_respects f (symmetry H1) Him).
    (* inl a ~ inr b ~ inl c *)
    + destruct H1 as [Hab _], H2 as [Hbc _].
      now transitivity b.
    (* inl a ~ inr b ~ inr c *)
    + destruct H1 as [Hab Him].
      split; [ now transitivity b | exact Him ].
    (* inr a ~ inl b ~ inl c *)
    + destruct H1 as [Hab Him].
      split; [ now transitivity b | exact Him ].
    (* inr a ~ inl b ~ inr c *)
    + destruct H1 as [Hab _], H2 as [Hbc _].
      now transitivity b.
    (* inr a ~ inr b ~ inl c *)
    + destruct H2 as [Hbc Him].
      split.
      * now transitivity b.
      * exact (InImage_respects f (symmetry H1) Him).
    (* inr a ~ inr b ~ inr c *)
    + now transitivity b.
Qed.

Definition PointedCP {X Y : PointedSetoid} (f : PointedMorphism X Y) :
  PointedSetoid := {|
  pointed_setoid := {| carrier := carrier Y + carrier Y
                     ; is_setoid := CP_setoid f |};
  pt := Datatypes.inl (pt Y)
|}.

(* 相关说明。 （已译） *)
Program Definition CP_left_map {X Y : PointedSetoid} (f : PointedMorphism X Y) :
  SetoidMorphism (pointed_setoid Y) (pointed_setoid (PointedCP f)) := {|
  morphism := fun y => Datatypes.inl y
|}.
Next Obligation. intros X Y f; simpl; intros a b Hab; exact Hab. Qed.

Program Definition CP_right_map {X Y : PointedSetoid} (f : PointedMorphism X Y) :
  SetoidMorphism (pointed_setoid Y) (pointed_setoid (PointedCP f)) := {|
  morphism := fun y => Datatypes.inr y
|}.
Next Obligation. intros X Y f; simpl; intros a b Hab; exact Hab. Qed.

Definition CP_left {X Y : PointedSetoid} (f : PointedMorphism X Y) :
  Y ~{PointedSets}~> PointedCP f.
Proof.
  refine (Build_PointedMorphism Y (PointedCP f) (CP_left_map f) _).
  simpl.
  reflexivity.
Defined.

Definition CP_right {X Y : PointedSetoid} (f : PointedMorphism X Y) :
  Y ~{PointedSets}~> PointedCP f.
Proof.
  refine (Build_PointedMorphism Y (PointedCP f) (CP_right_map f) _).
  simpl.
  split.
  - reflexivity.
  - apply InImage_pt.
Defined.

(* The two legs agree after [f]: every point form [f x] image
 定义, exactly gluing condition. （已译） *)
Lemma CP_coequalizes {X Y : PointedSetoid} (f : X ~{PointedSets}~> Y) :
  CP_left f ∘ f ≈ CP_right f ∘ f.
Proof.
  intro x; simpl.
  split.
  - reflexivity.
  - exists x.
    reflexivity.
Qed.

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem pointed_epic_surjective {X Y : PointedSetoid}
  (f : X ~{PointedSets}~> Y) : Epic f → PointedSurjective f.
Proof.
  intros [Hepic] b.
  spose (Hepic (PointedCP f) (CP_left f) (CP_right f) (CP_coequalizes f) b)
    as Hb.
  exact (snd Hb).
Qed.

(* 相关说明。 （已译） *)
Theorem pointed_epic_iff {X Y : PointedSetoid} (f : X ~{PointedSets}~> Y) :
  PointedSurjective f ↔ Epic f.
Proof.
  split.
  - intros Hsurj.
    constructor; intros Z g1 g2 Hg b; simpl in *.
    destruct (Hsurj b) as [a Ha].
    rewrite <- Ha.
    exact (Hg a).
  - apply pointed_epic_surjective.
Qed.

(* 相关说明。 （已译） *)

(* The easy halves, valid any 范畴 proved here pointwise: a
 态射 left inverse monic, one right inverse epic. （已译） *)

Corollary pointed_split_monic_is_monic {X Y : PointedSetoid}
  (f : X ~{PointedSets}~> Y) : Section f → Monic f.
Proof.
  intros [r Hr].
  constructor; intros Z g1 g2 Hg z; simpl in *.
  transitivity (r (f (g1 z))).
  - symmetry.
    exact (Hr (g1 z)).
  - rewrite (Hg z).
    exact (Hr (g2 z)).
Qed.

Corollary pointed_split_epic_is_epic {X Y : PointedSetoid}
  (f : X ~{PointedSets}~> Y) : Retraction f → Epic f.
Proof.
  intros [s Hs].
  constructor; intros Z g1 g2 Hg b; simpl in *.
  transitivity (g1 (f (s b))).
  - now rewrite (Hs b).
  - rewrite (Hg (s b)).
    now rewrite (Hs b).
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Pointed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ImageDecidable {X Y : PointedSetoid}
  (f : PointedMorphism X Y) : Type :=
  ∀ b : carrier Y, InImage f b + ¬ InImage f b.

(*
   本节说明 Pointed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition pointed_retract_fun {X Y : PointedSetoid}
  (f : PointedMorphism X Y) (dec : ImageDecidable f) (b : carrier Y) :
  carrier X :=
  match dec b with
  | Datatypes.inl w => `1 w
  | Datatypes.inr _ => pt X
  end.

Program Definition pointed_retract_map {X Y : PointedSetoid}
  (f : PointedMorphism X Y) (Hinj : PointedInjective f)
  (dec : ImageDecidable f) :
  SetoidMorphism (pointed_setoid Y) (pointed_setoid X) := {|
  morphism := pointed_retract_fun f dec
|}.
Next Obligation.
  intros X Y f Hinj dec; simpl; intros b b' Hbb.
  unfold pointed_retract_fun.
  destruct (dec b) as [[a Ha]|n], (dec b') as [[a' Ha']|n']; simpl.
  - apply Hinj.
    rewrite Ha, Ha'.
    exact Hbb.
  - destruct (n' (InImage_respects f Hbb (a; Ha))).
  - destruct (n (InImage_respects f (symmetry Hbb) (a'; Ha'))).
  - reflexivity.
Qed.

Definition pointed_retract {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (Hinj : PointedInjective f) (dec : ImageDecidable f) :
  Y ~{PointedSets}~> X.
Proof.
  refine (Build_PointedMorphism Y X (pointed_retract_map f Hinj dec) _).
  simpl.
  unfold pointed_retract_fun.
  destruct (dec (pt Y)) as [[a Ha]|n]; simpl.
  - apply Hinj.
    rewrite Ha.
    symmetry.
    exact (preserves_pt f).
  - destruct (n (InImage_pt f)).
Defined.

(*
   本节说明 Pointed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem pointed_monic_split {X Y : PointedSetoid} (f : X ~{PointedSets}~> Y)
  (dec : ImageDecidable f) : Monic f → Section f.
Proof.
  intros Hm.
  pose proof (snd (pointed_monic_iff f) Hm) as Hinj.
  refine (@Build_Section PointedSets X Y f (pointed_retract f Hinj dec) _).
  intro a; simpl.
  unfold pointed_retract_fun.
  destruct (dec (f a)) as [[a' Ha']|n]; simpl.
  - now apply Hinj.
  - refine (False_rect _ (n _)).
    exists a.
    reflexivity.
Defined.

(* 相关说明。 （已译） *)

(*
   本节说明 Pointed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition pointed_inverse_map {X Y : PointedSetoid}
  (f : PointedMorphism X Y) (Hinj : PointedInjective f)
  (Hsurj : PointedSurjective f) :
  SetoidMorphism (pointed_setoid Y) (pointed_setoid X) := {|
  morphism := fun b => `1 (Hsurj b)
|}.
Next Obligation.
  intros X Y f Hinj Hsurj; simpl; intros b b' Hbb.
  apply Hinj.
  rewrite (`2 (Hsurj b)), (`2 (Hsurj b')).
  exact Hbb.
Qed.

Definition pointed_inverse {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (Hinj : PointedInjective f) (Hsurj : PointedSurjective f) :
  Y ~{PointedSets}~> X.
Proof.
  refine (Build_PointedMorphism Y X (pointed_inverse_map f Hinj Hsurj) _).
  simpl.
  apply Hinj.
  rewrite (`2 (Hsurj (pt Y))).
  symmetry.
  exact (preserves_pt f).
Defined.

(*
   本节说明 Pointed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem pointed_balanced {X Y : PointedSetoid} (f : X ~{PointedSets}~> Y) :
  IsIsomorphism f ↔ (Monic f ∧ Epic f).
Proof.
  split.
  - intros [g Hfg Hgf].
    split.
    + apply (pointed_split_monic_is_monic f).
      exact (@Build_Section PointedSets X Y f g Hgf).
    + apply (pointed_split_epic_is_epic f).
      exact (@Build_Retraction PointedSets X Y f g Hfg).
  - intros [Hm He].
    pose proof (snd (pointed_monic_iff f) Hm) as Hinj.
    pose proof (pointed_epic_surjective f He) as Hsurj.
    refine (@Build_IsIsomorphism PointedSets X Y f
              (pointed_inverse f Hinj Hsurj) _ _).
    + intro b; simpl.
      exact (`2 (Hsurj b)).
    + intro a; simpl.
      apply Hinj.
      exact (`2 (Hsurj (f a))).
Qed.

(* 相关说明。 （已译） *)

(* Decidability of `≈` on a pointed setoid. *)
Definition DecidableEquiv (Y : PointedSetoid) : Type :=
  ∀ y y' : carrier Y, (y ≈ y') + ¬ (y ≈ y').

(* Decidability "is basepoint?", weaker 假设 needed by
 essential-surjectivity 论元 Instance/Sets/Pointed/Part.v. （已译） *)
Definition DecidablePt (Z : PointedSetoid) : Type :=
  ∀ z : carrier Z, (z ≈ pt Z) + ¬ (z ≈ pt Z).

(* 相关说明。 （已译） *)
Fixpoint InSetoid {X : PointedSetoid}
  (x : carrier X) (l : list (carrier X)) : Type :=
  match l with
  | Datatypes.nil => False
  | Datatypes.cons a l' => (a ≈ x) + InSetoid x l'
  end.

(* An enumeration pointed setoid: list meeting every `≈`-class. This
 finiteness 假设; [bool] witness of
 Instance/Sets/Pointed/Finite.v satisfies it. （已译） *)
Record PointedEnumeration (X : PointedSetoid) := {
  enum_list : list (carrier X);
  enum_covers : ∀ x : carrier X, InSetoid x enum_list
}.

Arguments enum_list {X} _.
Arguments enum_covers {X} _ _.

(*
   本节说明 Pointed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fixpoint pointed_search {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (deq : DecidableEquiv Y) (l : list (carrier X)) (b : carrier Y) :
  option (carrier X) :=
  match l with
  | Datatypes.nil => Datatypes.None
  | Datatypes.cons a l' =>
    match deq (f a) b with
    | Datatypes.inl _ => Datatypes.Some a
    | Datatypes.inr _ => pointed_search f deq l' b
    end
  end.

Lemma pointed_search_respects {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (deq : DecidableEquiv Y) (l : list (carrier X)) (b b' : carrier Y) :
  b ≈ b' → pointed_search f deq l b = pointed_search f deq l b'.
Proof.
  intro Hbb.
  induction l as [|a l IH]; simpl.
  - reflexivity.
  - destruct (deq (f a) b) as [p|n], (deq (f a) b') as [p'|n'].
    + reflexivity.
    + destruct (n' (transitivity p Hbb)).
    + destruct (n (transitivity p' (symmetry Hbb))).
    + exact IH.
Qed.

Lemma pointed_search_correct {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (deq : DecidableEquiv Y) (l : list (carrier X)) (b : carrier Y)
  (a : carrier X) :
  pointed_search f deq l b = Datatypes.Some a → f a ≈ b.
Proof.
  induction l as [|a0 l IH]; simpl.
  - intro H; discriminate.
  - destruct (deq (f a0) b) as [p|n].
    + intro H.
      injection H; intro Ha; subst.
      exact p.
    + exact IH.
Qed.

Lemma pointed_search_complete {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (deq : DecidableEquiv Y) (l : list (carrier X)) (b : carrier Y)
  (a : carrier X) :
  InSetoid a l → f a ≈ b → pointed_search f deq l b <> Datatypes.None.
Proof.
  induction l as [|a0 l IH]; simpl.
  - intros [].
  - intros [Hh|Ht] Hfa; destruct (deq (f a0) b) as [p|n].
    + discriminate.
    + refine (False_rect _ (n _)).
      rewrite Hh.
      exact Hfa.
    + discriminate.
    + exact (IH Ht Hfa).
Qed.

(*
   本节说明 Pointed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition pointed_section_fun {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (deq : DecidableEquiv Y) (E : PointedEnumeration X) (b : carrier Y) :
  carrier X :=
  match deq b (pt Y) with
  | Datatypes.inl _ => pt X
  | Datatypes.inr _ =>
    match pointed_search f deq (enum_list E) b with
    | Datatypes.Some a => a
    | Datatypes.None => pt X
    end
  end.

Program Definition pointed_section_map {X Y : PointedSetoid}
  (f : PointedMorphism X Y) (deq : DecidableEquiv Y)
  (E : PointedEnumeration X) :
  SetoidMorphism (pointed_setoid Y) (pointed_setoid X) := {|
  morphism := pointed_section_fun f deq E
|}.
Next Obligation.
  intros X Y f deq E; simpl; intros b b' Hbb.
  unfold pointed_section_fun.
  destruct (deq b (pt Y)) as [p|n], (deq b' (pt Y)) as [p'|n'].
  - reflexivity.
  - destruct (n' (transitivity (symmetry Hbb) p)).
  - destruct (n (transitivity Hbb p')).
  - rewrite (pointed_search_respects f deq (enum_list E) b b' Hbb).
    reflexivity.
Qed.

Definition pointed_section {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (deq : DecidableEquiv Y) (E : PointedEnumeration X) :
  Y ~{PointedSets}~> X.
Proof.
  refine (Build_PointedMorphism Y X (pointed_section_map f deq E) _).
  simpl.
  unfold pointed_section_fun.
  destruct (deq (pt Y) (pt Y)) as [p|n].
  - reflexivity.
  - refine (False_rect _ (n _)).
    reflexivity.
Defined.

(*
   本节说明 Pointed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem pointed_epic_split {X Y : PointedSetoid} (f : X ~{PointedSets}~> Y)
  (deq : DecidableEquiv Y) (E : PointedEnumeration X) :
  Epic f → Retraction f.
Proof.
  intros He.
  pose proof (pointed_epic_surjective f He) as Hsurj.
  refine (@Build_Retraction PointedSets X Y f (pointed_section f deq E) _).
  intro b; simpl.
  unfold pointed_section_fun.
  destruct (deq b (pt Y)) as [p|n].
  - rewrite (preserves_pt f).
    now symmetry.
  - destruct (pointed_search f deq (enum_list E) b) as [a|] eqn:Hs.
    + exact (pointed_search_correct f deq (enum_list E) b a Hs).
    + destruct (Hsurj b) as [a Ha].
      destruct (pointed_search_complete f deq (enum_list E) b a
                  (enum_covers E a) Ha Hs).
Defined.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明 Pointed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition InformativeEM := ∀ P : Prop, P + ¬ P.

Section Necessity.

(* The monic side: `option P` based at `None`, 映射 two-point set
 forgetting 证明. It injective every P, hence monic. （已译） *)

Definition optP_rel (P : Prop) (u v : option P) : Type :=
  match u, v with
  | Datatypes.Some _, Datatypes.Some _ => True
  | Datatypes.None,   Datatypes.None   => True
  | _, _ => False
  end.

Definition optP_setoid (P : Prop) : Setoid (option P).
Proof.
  refine {| equiv := optP_rel P |}.
  constructor.
  - intros x; destruct x; exact I.
  - intros x y H; destruct x, y; try exact I; exact H.
  - intros x y z H1 H2; destruct x, y, z; try exact I; contradiction.
Defined.

Definition OptP (P : Prop) : PointedSetoid := {|
  pointed_setoid := {| carrier := option P ; is_setoid := optP_setoid P |};
  pt := Datatypes.None
|}.

Definition optP_fun (P : Prop) (u : option P) : option poly_unit :=
  match u with
  | Datatypes.Some _ => Datatypes.Some ttt
  | Datatypes.None   => Datatypes.None
  end.

Definition optP_map (P : Prop) :
  SetoidMorphism (pointed_setoid (OptP P)) (pointed_setoid PointedTwo).
Proof.
  refine {| morphism := optP_fun P |}.
  intros x y H; destruct x, y; simpl in *; try contradiction; try reflexivity;
    try exact I.
Defined.

Definition optP_f (P : Prop) : OptP P ~{PointedSets}~> PointedTwo :=
  Build_PointedMorphism _ _ (optP_map P) I.

Lemma optP_injective (P : Prop) : PointedInjective (optP_f P).
Proof. intros x y H; destruct x, y; simpl in *; try exact I; contradiction. Qed.

Definition optP_monic (P : Prop) : Monic (optP_f P) :=
  fst (pointed_monic_iff (optP_f P)) (optP_injective P).

(* Dropping [ImageDecidable] [pointed_monic_split] decides every
 命题: retraction's value at free point says whether P
 holds. （已译） *)
Theorem unconditional_monic_split_gives_IEM :
  (∀ (X Y : PointedSetoid) (g : X ~{PointedSets}~> Y), Monic g → Section g)
  → InformativeEM.
Proof.
  intros H P.
  destruct (H _ _ (optP_f P) (optP_monic P)) as [r Hr].
  destruct (pointed_map r (Datatypes.Some ttt)) as [p|] eqn:Heq.
  - left; exact p.
  - right; intro p.
    pose proof (Hr (Datatypes.Some p)) as Hp; simpl in Hp.
    change (optP_fun P (Datatypes.Some p)) with (Datatypes.Some ttt) in Hp.
    rewrite Heq in Hp.
    exact Hp.
Qed.

(* The epic side: two-point set two points glued exactly P
 holds. The 恒等 carrier map it surjective, hence epic. （已译） *)

Definition glueP_rel (P : Prop) (u v : option poly_unit) : Type :=
  match u, v with
  | Datatypes.Some _, Datatypes.Some _ => True
  | Datatypes.None,   Datatypes.None   => True
  | _, _ => P
  end.

Definition glueP_setoid (P : Prop) : Setoid (option poly_unit).
Proof.
  refine {| equiv := glueP_rel P |}.
  constructor.
  - intros x; destruct x; exact I.
  - intros x y H; destruct x, y; try exact I; exact H.
  - intros x y z H1 H2; destruct x, y, z; try exact I;
      first [ exact H1 | exact H2 ].
Defined.

Definition GlueP (P : Prop) : PointedSetoid := {|
  pointed_setoid := {| carrier := option poly_unit
                     ; is_setoid := glueP_setoid P |};
  pt := Datatypes.None
|}.

Definition glueP_map (P : Prop) :
  SetoidMorphism (pointed_setoid PointedTwo) (pointed_setoid (GlueP P)).
Proof.
  refine {| morphism := fun u : option poly_unit => u |}.
  intros x y H; destruct x, y; simpl in *; try contradiction; try reflexivity;
    try exact I.
Defined.

Definition glueP_f (P : Prop) : PointedTwo ~{PointedSets}~> GlueP P :=
  Build_PointedMorphism _ _ (glueP_map P) I.

Lemma glueP_surjective (P : Prop) : PointedSurjective (glueP_f P).
Proof. intro b; exists b; destruct b; exact I. Qed.

Definition glueP_epic (P : Prop) : Epic (glueP_f P) :=
  fst (pointed_epic_iff (glueP_f P)) (glueP_surjective P).

(*
   本节说明 Pointed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem unconditional_epic_split_gives_IEM :
  (∀ (X Y : PointedSetoid) (g : X ~{PointedSets}~> Y), Epic g → Retraction g)
  → InformativeEM.
Proof.
  intros H P.
  destruct (H _ _ (glueP_f P) (glueP_epic P)) as [s Hs].
  pose proof (preserves_pt s) as Hpt; simpl in Hpt.
  destruct (pointed_map s Datatypes.None) as [v|] eqn:Heq2;
    [ simpl in Hpt; contradiction | ].
  destruct (pointed_map s (Datatypes.Some ttt)) as [u|] eqn:Heq.
  - right; intro p.
    pose proof (proper_morphism (pointed_map s)
                  (Datatypes.Some ttt) Datatypes.None p) as Hresp.
    rewrite Heq, Heq2 in Hresp.
    exact Hresp.
  - left.
    pose proof (Hs (Datatypes.Some ttt)) as Hp; simpl in Hp.
    rewrite Heq in Hp.
    exact Hp.
Qed.

End Necessity.
