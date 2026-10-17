Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Thin.
Require Import Category.Construction.Product.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Presented.
Require Import Category.Instance.Two.
Require Import Category.Instance.Ordinal.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Instance.Square.

Require Import Coq.Lists.List.

Generalizable All Variables.

#[local] Existing Instance edgeset.

(*
 Book: Riehl, Category Theory in Context, Dover 2016, §1.6,
 Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,

   本文件给出积相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Thinness of the product shape *)

(** The walking arrow thin. Its hom-setoid [Morphism_equality],
 so [≈] Leibniz [=] 这是 [ord_two_thin]
 ([Instance/Ordinal.v]) verbatim; it cited rather than reproved. （已译） *)
Lemma Two_Thin : Thin _2.
Proof. intros x y f g; exact (ord_two_thin f g). Qed.

Lemma Two2_Thin : Thin (_2 ∏ _2).
Proof. exact (Thin_Product Two_Thin Two_Thin). Qed.

(* 相关说明。 （已译） *)
Definition sq22_node (a b : TwoObj) : SquareNode :=
  match a, b with
  | TwoX, TwoX => Sq_A
  | TwoY, TwoX => Sq_B
  | TwoX, TwoY => Sq_C
  | TwoY, TwoY => Sq_D
  end.

Definition sq22_obj (x : TwoObj * TwoObj) : SquareNode :=
  sq22_node (fst x) (snd x).

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sq22_map {a b c d : TwoObj} (u : TwoHom a c) (v : TwoHom b d) :
  sq22_node a b ~{Square}~> sq22_node c d :=
  match u in TwoHom a0 c0, v in TwoHom b0 d0
    return sq22_node a0 b0 ~{Square}~> sq22_node c0 d0 with
  | TwoIdX, TwoIdX => id
  | TwoIdX, TwoIdY => id
  | TwoIdY, TwoIdX => id
  | TwoIdY, TwoIdY => id
  | TwoXY,  TwoIdX => square_f
  | TwoIdX, TwoXY  => square_g
  | TwoIdY, TwoXY  => square_h
  | TwoXY,  TwoIdY => square_k
  | TwoXY,  TwoXY  => square_diagonal
  end.

(** All three functor laws are equations between parallel arrows of
    [Square], hence instances of [Square_Thin]. *)
Definition Square_of_22 : (_2 ∏ _2) ⟶ Square :=
  Build_Functor (_2 ∏ _2) Square
    sq22_obj
    (fun x y f => sq22_map (fst f) (snd f))
    (fun x y f g _ => Square_Thin _ _ _ _)
    (fun x => Square_Thin _ _ _ _)
    (fun x y z f g => Square_Thin _ _ _ _).

(* * ** From square 2 × 2

 The evident commutative square 2 × 2, 函子 the
 普遍性质 [Square] makes it. （已译） *)
Definition sq22_commuting : CommutingSquare (_2 ∏ _2) :=
  @Build_CommutingSquare (_2 ∏ _2)
    (TwoX, TwoX) (TwoY, TwoX) (TwoX, TwoY) (TwoY, TwoY)
    (TwoXY, TwoIdX) (TwoIdX, TwoXY) (TwoIdY, TwoXY) (TwoXY, TwoIdY)
    (Two2_Thin _ _ _ _).

Definition Square_to_22 : Square ⟶ (_2 ∏ _2) := SquareFunctor sq22_commuting.

(** Its object action, on the nose. *)
Example Square_to_22_A : fobj[Square_to_22] Sq_A = (TwoX, TwoX) := eq_refl.
Example Square_to_22_B : fobj[Square_to_22] Sq_B = (TwoY, TwoX) := eq_refl.
Example Square_to_22_C : fobj[Square_to_22] Sq_C = (TwoX, TwoY) := eq_refl.
Example Square_to_22_D : fobj[Square_to_22] Sq_D = (TwoY, TwoY) := eq_refl.

(*
   本节说明 Product 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma square_22_node_round (n : SquareNode) :
  sq22_obj (fobj[Square_to_22] n) = n.
Proof. destruct n; reflexivity. Qed.

Lemma square_22_obj_round (x : TwoObj * TwoObj) :
  fobj[Square_to_22] (sq22_obj x) = x.
Proof. destruct x as [a b]; destruct a, b; reflexivity. Qed.

(* * ** The identification

 Both round trips at [Functor_StrictEq_Setoid] strength: Leibniz on
 对象, 态射 [hom_cast] conjugation thinness
 discharges outright either side. （已译） *)
Lemma Square_22_round : @equiv _ (@Functor_StrictEq_Setoid Square Square)
  (Square_of_22 ◯ Square_to_22) (Id[Square]).
Proof.
  apply (strict_of_hom_cast (Square_of_22 ◯ Square_to_22) (Id[Square])
           square_22_node_round).
  intros x y p; exact (Square_Thin _ _ _ _).
Qed.

Lemma Square_22_round' :
  @equiv _ (@Functor_StrictEq_Setoid (_2 ∏ _2) (_2 ∏ _2))
    (Square_to_22 ◯ Square_of_22) (Id[_2 ∏ _2]).
Proof.
  apply (strict_of_hom_cast (Square_to_22 ◯ Square_of_22) (Id[_2 ∏ _2])
           square_22_obj_round).
  intros x y p; exact (Two2_Thin _ _ _ _).
Qed.

(** Riehl §1.6 Example 1.6.6: the walking commutative square IS 2 × 2 —
    an isomorphism of categories, not merely an equivalence. *)
Definition Square_2x2_iso : Square ≅[StrictCat] (_2 ∏ _2) :=
  @Build_Isomorphism StrictCat Square (_2 ∏ _2)
    Square_to_22 Square_of_22 Square_22_round' Square_22_round.

(*
   本节说明函子、hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Square_2x2_Cat_iso : Square ≅[Cat] (_2 ∏ _2) :=
  @Build_Isomorphism Cat Square (_2 ∏ _2)
    Square_to_22 Square_of_22
    (strict_equiv_implies_fun_equiv _ _ Square_22_round')
    (strict_equiv_implies_fun_equiv _ _ Square_22_round).

(*
   本节说明 Product 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** 本节：The walking arrow has three arrows: [TwoHom] inhabited except at
 (Y, X), then exactly one element. （已译） *)
Definition two_homcount (a b : TwoObj) : nat :=
  match a, b with
  | TwoY, TwoX => 0
  | _, _ => 1
  end.

Lemma two_hom_empty (f : TwoHom TwoY TwoX) : False.
Proof. exact (TwoHom_Y_X_absurd f). Qed.

Lemma two_hom_inhabited (a b : TwoObj) :
  two_homcount a b = 1%nat → TwoHom a b.
Proof.
  destruct a, b; simpl; intro H;
    solve [ exact TwoIdX | exact TwoIdY | exact TwoXY | discriminate ].
Qed.

Definition two_objs : list TwoObj := TwoX :: TwoY :: nil.

Definition two_pairs : list (TwoObj * TwoObj) := list_prod two_objs two_objs.

Definition two_arrow_total : nat :=
  fold_right (fun q n => two_homcount (fst q) (snd q) + n)%nat 0%nat two_pairs.

Theorem two_arrow_total_3 : two_arrow_total = 3%nat.
Proof. reflexivity. Qed.

(** 本节：In product, hom-set at pair endpoint pairs the
 product two component hom-sets, so count product
 two counts. （已译） *)
Definition prod22_homcount (x y : TwoObj * TwoObj) : nat :=
  (two_homcount (fst x) (fst y) * two_homcount (snd x) (snd y))%nat.

Definition prod22_pairs : list ((TwoObj * TwoObj) * (TwoObj * TwoObj)) :=
  list_prod two_pairs two_pairs.

Example prod22_pairs_16 : length prod22_pairs = 16%nat := eq_refl.

Definition prod22_arrow_total : nat :=
  fold_right (fun q n => prod22_homcount (fst q) (snd q) + n)%nat 0%nat
    prod22_pairs.

Theorem prod22_arrow_total_9 : prod22_arrow_total = 9%nat.
Proof. reflexivity. Qed.

Definition prod22_identity_total : nat :=
  fold_right (fun x n => prod22_homcount x x + n)%nat 0%nat two_pairs.

Theorem prod22_identity_total_4 : prod22_identity_total = 4%nat.
Proof. reflexivity. Qed.

Definition prod22_nonidentity_total : nat :=
  (prod22_arrow_total - prod22_identity_total)%nat.

Theorem prod22_nonidentity_total_5 : prod22_nonidentity_total = 5%nat.
Proof. reflexivity. Qed.

(*
   本节说明hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem prod22_homcount_empty (x y : TwoObj * TwoObj) :
  prod22_homcount x y = 0%nat → (x ~{_2 ∏ _2}~> y) → False.
Proof.
  destruct x as [a b], y as [c d]; destruct a, b, c, d; simpl;
    solve [ intros H _; discriminate H
          | intros _ [u v]; solve [ exact (two_hom_empty u)
                                  | exact (two_hom_empty v) ] ].
Qed.

Theorem prod22_homcount_inhabited (x y : TwoObj * TwoObj) :
  prod22_homcount x y = 1%nat → x ~{_2 ∏ _2}~> y.
Proof.
  destruct x as [a b], y as [c d]; destruct a, b, c, d; simpl; intro H;
    solve [ discriminate H
          | exact (TwoIdX, TwoIdX) | exact (TwoIdX, TwoIdY)
          | exact (TwoIdX, TwoXY)  | exact (TwoIdY, TwoIdX)
          | exact (TwoIdY, TwoIdY) | exact (TwoIdY, TwoXY)
          | exact (TwoXY, TwoIdX)  | exact (TwoXY, TwoIdY)
          | exact (TwoXY, TwoXY) ].
Qed.

(** The cross-check two presentations owe each other: Mac Lane's
 count Riehl's agree, arrow arrow, 恒等 恒等. （已译） *)
Theorem square_22_counts_agree :
  ((square_arrow_total = prod22_arrow_total) *
   (square_identity_total = prod22_identity_total) *
   (square_nonidentity_total = prod22_nonidentity_total))%type.
Proof. repeat split; reflexivity. Qed.

(** ...and 9 = 3 × 3, whole Riehl's 论元. （已译） *)
Example square_count_is_three_squared :
  square_arrow_total = (two_arrow_total * two_arrow_total)%nat := eq_refl.
