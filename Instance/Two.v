Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** The interval category 2 (the "walking arrow"). *)

(*
 nLab:      https://ncatlab.org/nlab/show/walking+structure (walking morphism)
 Wikipedia: https://en.wikipedia.org/wiki/Posetal_category

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:      https://ncatlab.org/nlab/show/diagram
   nLab:      https://ncatlab.org/nlab/show/walking+morphism
   nLab:      https://ncatlab.org/nlab/show/walking+structure
   Paper:     Lawvere, "Metric spaces, generalized logic, and closed
   Paper:     Foltz, Lair, Kelly, "Algebraic categories with few

   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Inductive TwoObj : Set := TwoX | TwoY.

Inductive TwoHom : TwoObj → TwoObj → Set :=
  | TwoIdX : TwoHom TwoX TwoX
  | TwoIdY : TwoHom TwoY TwoY
  | TwoXY  : TwoHom TwoX TwoY.

Definition TwoHom_inv_t : ∀ x y, TwoHom x y → Prop.
Proof.
  intros [] [] f.
  - exact (f = TwoIdX).
  - exact (f = TwoXY).
  - exact False.          (* Unused, any Prop is ok here *)
  - exact (f = TwoIdY).
Defined.

Corollary TwoHom_inv x y f : TwoHom_inv_t x y f.
Proof. destruct f; reflexivity. Qed.

Lemma TwoHom_Y_X_absurd : TwoHom TwoY TwoX → False.
Proof. inversion 1. Qed.

#[export] Hint Extern 4 => contradiction TwoHom_Y_X_absurd : two_laws.

Local Set Warnings "-intuition-auto-with-star".

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition _2 : Category := {|
  obj     := TwoObj;
  hom     := TwoHom;
  homset  := Morphism_equality;
  id      := fun x => match x with
    | TwoX => TwoIdX
    | TwoY => TwoIdY
    end;
  compose := fun x y z (f : TwoHom y z) (g : TwoHom x y) =>
    match x, y, z with
    | TwoX, TwoX, TwoX => TwoIdX
    | TwoY, TwoY, TwoY => TwoIdY
    | TwoX, TwoX, TwoY => TwoXY
    | TwoX, TwoY, TwoY => TwoXY
    | _,    _,    _    => _
    end
|}.
Next Obligation. destruct x, y, z; intuition; auto with *. Qed.
Next Obligation.
  destruct x, y, z; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation.
  destruct x, y, z; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation.
  destruct x, y, z; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation. destruct f; auto. Qed.
Next Obligation. destruct f; auto. Qed.
Next Obligation. destruct x, y, z, w; auto with two_laws; intuition; auto with *. Qed.
Next Obligation. destruct x, y, z, w; auto with two_laws; intuition. Qed.

(* ------------------------------------------------------------------------ *)
(** ** A bimorphism that is not an isomorphism *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.

(* Any two parallel arrows of 2 agree: the category is thin. *)
Lemma Two_thin {x y : TwoObj} (f g : x ~{_2}~> y) : f ≈ g.
Proof.
  destruct x, y.
  - now rewrite (TwoHom_inv _ _ f), (TwoHom_inv _ _ g).
  - now rewrite (TwoHom_inv _ _ f), (TwoHom_inv _ _ g).
  - contradiction (TwoHom_Y_X_absurd f).
  - now rewrite (TwoHom_inv _ _ f), (TwoHom_inv _ _ g).
Qed.

Definition TwoXY_monic : @Monic _2 TwoX TwoY TwoXY.
Proof. constructor; intros z g1 g2 _; apply Two_thin. Qed.

Definition TwoXY_epic : @Epic _2 TwoX TwoY TwoXY.
Proof. constructor; intros z g1 g2 _; apply Two_thin. Qed.

Definition TwoXY_bimorphic : @Bimorphic _2 TwoX TwoY TwoXY :=
  (TwoXY_epic, TwoXY_monic).

(* But it has no inverse: an inverse would be an arrow TwoY ~> TwoX. *)
Lemma TwoXY_not_iso : @IsIsomorphism _2 TwoX TwoY TwoXY → False.
Proof. intros [g _ _]; exact (TwoHom_Y_X_absurd g). Qed.

(* The exercise, packaged: 2 is not balanced. *)
Definition two_bimorphic_not_iso :
  @Bimorphic _2 TwoX TwoY TwoXY * (@IsIsomorphism _2 TwoX TwoY TwoXY → False) :=
  (TwoXY_bimorphic, TwoXY_not_iso).


(*
   本节说明 Two 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma TwoXY_not_regular : @RegularMorphism _2 TwoX TwoY TwoXY → False.
Proof. intros [g _]; exact (TwoHom_Y_X_absurd g). Qed.

(* Both one-sided splittings are ruled out through regularity, rather than by
   repeating the argument: a section or a retraction is regular. *)
Lemma TwoXY_not_retraction : @Retraction _2 TwoX TwoY TwoXY → False.
Proof. intro R; exact (TwoXY_not_regular (regular_of_retraction _ R)). Qed.

Lemma TwoXY_not_section : @Section _2 TwoX TwoY TwoXY → False.
Proof. intro S; exact (TwoXY_not_regular (regular_of_section _ S)). Qed.

(* Packaged: an arrow that is epic, does not split, and is not regular. *)
Definition two_epic_not_regular :
  @Epic _2 TwoX TwoY TwoXY
  * (@Retraction _2 TwoX TwoY TwoXY → False)
  * (@RegularMorphism _2 TwoX TwoY TwoXY → False) :=
  (TwoXY_epic, TwoXY_not_retraction, TwoXY_not_regular).


Require Import Category.Instance.Sets.

(* A functor 2 ⟶ Sets is precisely a morphism of Sets; this one picks out the
   unique map (the empty function) from False to True, sending TwoXY there. *)

Program Definition _2_as_Set : _2 ⟶ Sets := {|
  fobj := fun x =>
    match x with
    | TwoX => {| carrier := False |}
    | TwoY => {| carrier := True |}
    end;
  fmap := fun x y f =>
    match x, y with
    | TwoY, TwoY => _
    | _, _       => _
    end
|}.
Next Obligation.
  construct.
  - repeat intro.
    contradiction.
  - equivalence.
Defined.
Next Obligation.
  construct.
  - repeat intro.
    exact True.
  - equivalence.
Defined.
Next Obligation.
  construct; auto.
Defined.
Next Obligation.
  construct; auto.
  - destruct x, y; simpl in *; auto with two_laws.
  - proper.
    destruct x, y; simpl in *; auto with two_laws.
Qed.
Next Obligation.
  destruct x; simpl in *; auto with two_laws.
  contradiction.
Qed.
Next Obligation.
  destruct x, y, z; simpl in *; auto with two_laws.
  contradiction.
Qed.
