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

(* * ** (1) The donor pin gone

 A target 范畴 whose three universes declared strictly above
 [Set]. Before lift described above, forming [SquareFunctor] at
 such target was universe inconsistency; it now typechecks. （已译） *)

Section BigTarget.

Universes bo bh bp.
Constraint Set < bo.
Constraint Set < bh.
Constraint Set < bp.
Constraint bh <= bp.

Context (D : Category@{bo bh bp}).
Context (S : CommutingSquare D).

(** The 普遍性质 presented square, applied above
 [Set]. This guard [Build_Quiver_Standard_Eq]
 generalisation. （已译） *)
Check (SquareFunctor S : Square ⟶ D).

(** 本节：...and action generators, so guard covers the
 theorems not construction. （已译） *)
Check (SquareFunctor_f S).
Check (square_universal S).

(** 本节：The reverse direction was never pinned, still not. （已译） *)
Context (F : Square ⟶ D).

Check (CommutingSquareOfFunctor F : CommutingSquare D).
Check (square_functor_round_strict F).

End BigTarget.

(*
   本节说明等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (Square_2x2_iso : Square ≅[StrictCat] (_2 ∏ _2)).
Check (Square_2x2_Cat_iso : Square ≅[Cat] (_2 ∏ _2)).

(*
   本节说明 ProbeSquare 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (eq_refl : Square = (_2 ∏ _2)).

(** Nor 对象 types. (With [Fail] stripped: cannot
 unify [SquareNode] [TwoObj * TwoObj].) （已译） *)
Fail Check (eq_refl : SquareNode = (TwoObj * TwoObj)%type).

(*
   本节说明 ProbeSquare 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Section BigRectangle.

Universes ro rh rp.
Constraint Set < ro.
Constraint Set < rh.
Constraint Set < rp.
Constraint rh <= rp.

Context (E : Category@{ro rh rp}).

(** 本节：Forward half: accessors every commutativity statement
 typecheck at target above [Set]. （已译） *)
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

(** 本节：Negative half: converse does not reach here. (With [Fail]
 stripped reports universe inconsistency, [Set] against the
 declared [rh].) （已译） *)
Context (R : CommutingRectangle E).

Fail Check (RectFunctor R : Rect ⟶ E).

End BigRectangle.

(** Positive control converse: at target whose hom 证明
 universes ARE [Set] it builds, recovers all seven generators. （已译） *)
Section SmallRectangle.

Universe so.

Context (E : Category@{so Set Set}).
Context (R : CommutingRectangle E).

Check (RectFunctor R : Rect ⟶ E).
Check (RectFunctor_u R).
Check (RectFunctor_p R).
Check (RectFunctor_r R).

End SmallRectangle.
