Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Cartesian.
Require Import Category.Instance.Two.

Generalizable All Variables.

(*
   本文件给出幺半结构实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma two_thin {x y : TwoObj} (f g : TwoHom x y) : f = g.
Proof. exact (Two_thin f g). Qed.

(* The binary meet (product object): TwoX is the bottom, TwoY the top. *)
Definition two_meet (x y : TwoObj) : TwoObj :=
  match x with
  | TwoX => TwoX
  | TwoY => y
  end.

(* First projection  meet x y ~> x. *)
Definition two_exl (x y : TwoObj) : TwoHom (two_meet x y) x :=
  match x as x0 return TwoHom (two_meet x0 y) x0 with
  | TwoX => TwoIdX
  | TwoY => match y as y0 return TwoHom (two_meet TwoY y0) TwoY with
            | TwoX => TwoXY
            | TwoY => TwoIdY
            end
  end.

(* Second projection  meet x y ~> y. *)
Definition two_exr (x y : TwoObj) : TwoHom (two_meet x y) y :=
  match x as x0 return TwoHom (two_meet x0 y) y with
  | TwoX => match y as y0 return TwoHom (two_meet TwoX y0) y0 with
            | TwoX => TwoIdX
            | TwoY => TwoXY
            end
  | TwoY => match y as y0 return TwoHom (two_meet TwoY y0) y0 with
            | TwoX => TwoIdX
            | TwoY => TwoIdY
            end
  end.

(* Pairing  x ~> meet y z, given x ~> y and x ~> z. *)
Definition two_fork (x y z : TwoObj)
  (f : TwoHom x y) (g : TwoHom x z) : TwoHom x (two_meet y z).
Proof.
  destruct x.
  - destruct (two_meet y z); [ exact TwoIdX | exact TwoXY ].
  - destruct y.
    + exact (False_rect _ (TwoHom_Y_X_absurd f)).
    + destruct z.
      * exact (False_rect _ (TwoHom_Y_X_absurd g)).
      * exact TwoIdY.
Defined.

(* Binary products on 2 given by meets. *)
Program Instance Two_Cartesian : @Cartesian _2 := {|
  product_obj := two_meet;
  fork := two_fork;
  exl := two_exl;
  exr := two_exr
|}.
Next Obligation.
  split; intros; try split; apply two_thin.
Qed.

(* The unique morphism  x ~> TwoY  into the top object. *)
Definition two_one (x : TwoObj) : TwoHom x TwoY :=
  match x with
  | TwoX => TwoXY
  | TwoY => TwoIdY
  end.

(* TwoY is terminal in 2. *)
Program Instance Two_Terminal : @Terminal _2 := {|
  terminal_obj := TwoY;
  one := two_one
|}.
Next Obligation. apply two_thin. Qed.

(* The cartesian monoidal structure on 2: tensor := meet, unit := TwoY. *)
Definition Two_Monoidal : @Monoidal _2 :=
  @Cartesian_Monoidal _2 Two_Cartesian Two_Terminal.
