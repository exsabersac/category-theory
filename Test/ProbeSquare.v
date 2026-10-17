(*
   本文件为测试：ProbeSquare。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Presented.
Require Import Category.Instance.Two.
Require Import Category.Instance.Ordinal.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Square.
Require Import Category.Instance.Square.Product.
Require Import Category.Instance.Square.Rectangle.

Local Open Scope category_scope.

(** ** (1) The donor pin is gone

    A target category whose three universes are declared strictly above
    [Set].  Before the lift described above, forming [SquareFunctor] at
    such a target was a universe inconsistency; it now typechecks. *)

Section BigTarget.

Universes bo bh bp.
Constraint Set < bo.
Constraint Set < bh.
Constraint Set < bp.
Constraint bh <= bp.

Context (D : Category@{bo bh bp}).
Context (S : CommutingSquare D).

(** The universal property of the presented square, applied above
    [Set].  This is the guard on the [Build_Quiver_Standard_Eq]
    generalisation. *)
Check (SquareFunctor S : Square ⟶ D).

(** ...and its action on the generators, so the guard covers the
    theorems and not only the construction. *)
Check (SquareFunctor_f S).
Check (square_universal S).

(** The reverse direction was never pinned, and still is not. *)
Context (F : Square ⟶ D).

Check (CommutingSquareOfFunctor F : CommutingSquare D).
Check (square_functor_round_strict F).

End BigTarget.

(** ** (2) The 2 × 2 identification is an isomorphism, not an equality

    Positive control: the isomorphism in [StrictCat] — the strong
    reading, [≅[Cat]] in this library being an equivalence of
    categories. *)
Check (Square_2x2_iso : Square ≅[StrictCat] (_2 ∏ _2)).
Check (Square_2x2_Cat_iso : Square ≅[Cat] (_2 ∏ _2)).

(** Negative: the two categories are not Leibniz-equal, their object
    types being distinct inductives.  (With the [Fail] stripped this
    reports that [Square] and [_2 ∏ _2] cannot be unified.) *)
Fail Check (eq_refl : Square = (_2 ∏ _2)).

(** Nor are their object types.  (With the [Fail] stripped: cannot
    unify [SquareNode] with [TwoObj * TwoObj].) *)
Fail Check (eq_refl : SquareNode = (TwoObj * TwoObj)%type).

(** The instrument is not a no-op: a [Fail] on a succeeding command
    aborts compilation with "The command has not failed!".  The
    following line, uncommented, would do exactly that — it is left as
    a comment because a passing build cannot contain it.

      Fail Check (Square_2x2_iso : Square ≅[StrictCat] (_2 ∏ _2)).

    The controls above are the standing check that the [Fail]s are not
    passing for the wrong reason. *)

(** ** (3) The rectangle: forward unpinned, converse pinned at [Set] *)

Section BigRectangle.

Universes ro rh rp.
Constraint Set < ro.
Constraint Set < rh.
Constraint Set < rp.
Constraint rh <= rp.

Context (E : Category@{ro rh rp}).

(** Forward half: the accessors and every commutativity statement
    typecheck at a target above [Set]. *)
Context (F : Rect ⟶ E).

Check (rect_u F).
Check (rect_left_commutes F).
Check (rect_right_commutes F).
Check (rect_outer_commutes F).
Check (rect_outer_two_ways F).
Check (rect_long_through_left F).
Check (rect_long_through_right F).

(** The pasting principle carries no pin whatever — it mentions no
    shape category. *)
Check (@paste_squares E).

(** Negative half: the converse does not reach here.  (With the [Fail]
    stripped this reports a universe inconsistency, [Set] against the
    declared [rh].) *)
Context (R : CommutingRectangle E).

Fail Check (RectFunctor R : Rect ⟶ E).

End BigRectangle.

(** Positive control for the converse: at a target whose hom and proof
    universes ARE [Set] it builds, and recovers all seven generators. *)
Section SmallRectangle.

Universe so.

Context (E : Category@{so Set Set}).
Context (R : CommutingRectangle E).

Check (RectFunctor R : Rect ⟶ E).
Check (RectFunctor_u R).
Check (RectFunctor_p R).
Check (RectFunctor_r R).

End SmallRectangle.
