Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Cartesian.
Require Import Category.Instance.Two.

Generalizable All Variables.

(*
   * * Cartesian monoidal structure on the walking arrow 2.

   The interval category [_2] is thin (posetal): at most one morphism between
   any two objects, with hom-setoids under strict equality [Morphism_equality].
   Regarded as the ordinal {TwoX < TwoY}, it has all finite meets, hence finite
   products, and the top element TwoY is terminal.  Feeding the resulting
   [Cartesian] + [Terminal] data to the cartesian-to-monoidal bridge
   [Cartesian_Monoidal] (tensor := ×, unit := 1) yields the cartesian monoidal
   structure [Two_Monoidal].

   Every coherence law is an equation between parallel morphisms of a thin
   category; [two_thin] below says any two such morphisms coincide, so each
   obligation is discharged uniformly. 

   --------
   * * 在行走箭头 2 上的笛卡尔单体结构。

   间隔范畴 [_2] 是薄的（序数的）：任意两个对象之间最多有一个态射，其同态集在严格相等下为 [Morphism_equality]。 作为序数 {TwoX < TwoY} 来看，它具有所有有限交，因此具有有限积，并且顶部元素 TwoY 是终对象。 将生成的 [Cartesian] + [Terminal] 数据输入笛卡尔到单体的桥 [Cartesian_Monoidal]（张量 := ×，单位 := 1）得到笛卡尔单体结构 [Two_Monoidal]。

   每条相容律都是薄范畴中平行态射之间的方程；下方的 [two_thin] 表示任意两个这样的态射都相同，因此每个义务都统一地完成。
*)

(*
 Any two parallel morphisms of [_2] are equal: the category is thin.  The
 argument now lives upstream as [Two_thin] in Instance/Two.v, where the
 bimorphism witness needs it; this name is kept so existing callers here are
 undisturbed.  [_2]'s homset IS [Morphism_equality], i.e. [eq], so the two
 statements coincide. 

 --------
 [_2] 的任意两个平行态射都是相等的：该范畴是稀薄的。这个论证现在在 Instance/Two.v 中以上游形式作为 [Two_thin] 存在，其中双态射的证据需要它；这个名称被保留下来，以便这里的现有调用不受影响。[_2] 的同态集合是 [Morphism_equality]，即 [eq]，因此这两个陈述是一致的。
*)
Lemma two_thin {x y : TwoObj} (f g : TwoHom x y) : f = g.
Proof. exact (Two_thin f g). Qed.

(* The binary meet (product object): TwoX is the bottom, TwoY the top. / 二元积（乘积对象）：TwoX 是底部，TwoY 是顶部。 *)
Definition two_meet (x y : TwoObj) : TwoObj :=
  match x with
  | TwoX => TwoX
  | TwoY => y
  end.

(* First projection meet x y ~> x. / 第一个投影 见 x y ~> x. *)
Definition two_exl (x y : TwoObj) : TwoHom (two_meet x y) x :=
  match x as x0 return TwoHom (two_meet x0 y) x0 with
  | TwoX => TwoIdX
  | TwoY => match y as y0 return TwoHom (two_meet TwoY y0) TwoY with
            | TwoX => TwoXY
            | TwoY => TwoIdY
            end
  end.

(* Second projection meet x y ~> y. / 第二投影 见 x y ~> y。 *)
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

(* Pairing x ~> meet y z, given x ~> y and x ~> z. / 配对 x ~> 遇见 y z，给定 x ~> y 和 x ~> z。 *)
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

(* Binary products on 2 given by meets. / 二元运算由交给定于2上的积 *)
Program Instance Two_Cartesian : @Cartesian _2 := {|
  product_obj := two_meet;
  fork := two_fork;
  exl := two_exl;
  exr := two_exr
|}.
Next Obligation.
  split; intros; try split; apply two_thin.
Qed.

(* The unique morphism x ~> TwoY into the top object. / 唯一的态射 x ~> TwoY 到达顶对象。 *)
Definition two_one (x : TwoObj) : TwoHom x TwoY :=
  match x with
  | TwoX => TwoXY
  | TwoY => TwoIdY
  end.

(* TwoY is terminal in 2. / TwoY 在 2 终止。 *)
Program Instance Two_Terminal : @Terminal _2 := {|
  terminal_obj := TwoY;
  one := two_one
|}.
Next Obligation. apply two_thin. Qed.

(* The cartesian monoidal structure on 2: tensor := meet, unit := TwoY. / 在2上的笛卡尔单范畴结构：张量 := 交集，单位 := TwoY。 *)
Definition Two_Monoidal : @Monoidal _2 :=
  @Cartesian_Monoidal _2 Two_Cartesian Two_Terminal.
