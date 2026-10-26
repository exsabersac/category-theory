Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Roof.

Generalizable All Variables.

(*
 A span in C is a diagram of shape `x ← s → y`: two morphisms sharing a
 common domain (the apex, or “roof”) s. Equivalently, it is a functor from
 the shape category Roof = (RNeg ← RZero → RPos) into C, so that a span is
 just an element of [Roof ⟶ C]. A span generalizes a morphism: there is no
 longer any asymmetry between source and target.

 nLab:      https://ncatlab.org/nlab/show/span
 Wikipedia: https://en.wikipedia.org/wiki/Span_(category_theory)

 The apex RZero carries the shared domain, and the two legs out of RZero
 become the morphisms of the span:

 s = RZero
 /         \
 f /           \ g
 v             v
 x = RNeg     y = RPos

 --------
 C 中的跨度是形状为 `x ← s → y` 的图：两个共享公共对象（顶点或“屋顶”）s 的态射。等价地，它是从形状范畴 Roof = (RNeg ← RZero → RPos) 到 C 的函子，因此一个跨度只是 [Roof ⟶ C] 的一个元素。跨度推广了态射：源和目标之间不再存在任何不对称性。

 nLab: https://ncatlab.org/nlab/show/span 
 Wikipedia: https://en.wikipedia.org/wiki/Span_(category_theory) 

 顶点 RZero 承载共享对象，RZero 的两条箭腿变为跨度的态射：

 s = RZero
 /         \
 f /           \ g
 v             v
 x = RNeg     y = RPos
*)
Definition Span (C : Category) := Roof ⟶ C.

(*
 A cospan is the dual notion: a span in the opposite category, i.e. a
 diagram of shape `x → s ← y` (two morphisms sharing a common codomain).
 It is a functor out of the opposite shape category Roof^op.

 nLab:      https://ncatlab.org/nlab/show/cospan
 Wikipedia: https://en.wikipedia.org/wiki/Span_(category_theory)#Cospans 

 --------
 余跨（cospan）是对偶的概念：在对立范畴中的跨，即形状为 `x → s ← y` 的图（两个态射共享一个共同的余域）。它是从对立形状范畴 Roof^op 出发的一个函子。

 nLab:       https://ncatlab.org/nlab/show/cospan
 Wikipedia:  https://en.wikipedia.org/wiki/Span_(category_theory)#Cospans
*)
Definition Cospan (C : Category) := Roof^op ⟶ C.

(*
 [ASpan f g] packages a concrete span `x ← S → y` from its apex S and its
 two legs [f : S ~> x] and [g : S ~> y] as a functor [Roof ⟶ C]. The
 object part sends the apex RZero to S and the feet RNeg, RPos to x, y; the
 morphism part sends the two non-identity Roof arrows ZeroNeg, ZeroPos to
 the legs f and g (all other arrows being identities). 

 --------
 [ASpan f g] 将一个具体的跨度 `x ← S → y` 从它的顶点 S 及其两条边 [f : S ~> x] 和 [g : S ~> y] 打包为一个函子 [Roof ⟶ C]。对象部分将顶点 RZero 发送到 S，将底点 RNeg、RPos 发送到 x、y；态射部分将两个非恒等的 Roof 箭头 ZeroNeg、ZeroPos 发送到边 f 和 g（所有其他箭头为恒等箭头）。
*)

Program Definition ASpan {C : Category} {S x y : C} (f : S ~> x) (g : S ~> y) :
  Roof ⟶ C := {|
  fobj := fun z => match z with
    | RNeg  => x          (* left foot / 左脚 *)
    | RZero => S          (* apex       *)
    | RPos  => y          (* right foot / 右脚 *)
    end;
  fmap := fun z w _ => match z, w with
    | RNeg,  RNeg  => id[x]   (* IdNeg   *)
    | RZero, RNeg  => f       (* left leg S ~> x / 左腿 S ~> x *)
    | RZero, RZero => id[S]   (* IdZero  *)
    | RZero, RPos  => g       (* right leg S ~> y / 右腿 S ~> y *)
    | RPos,  RPos  => id[y]   (* IdPos   *)
    | _,      _      => _       (* no other Roof arrows exist / 没有其他屋顶箭头存在 *)
    end
|}.
Next Obligation.
  destruct z, w; simpl; intuition idtac; auto with roof_laws.
Defined.
Next Obligation. intuition idtac; discriminate. Qed.
Next Obligation. intuition idtac; discriminate. Qed.
Next Obligation. intuition idtac; discriminate. Qed.
Next Obligation. intuition idtac; discriminate. Qed.
Next Obligation.
  proper.
  destruct x0, y0; simpl; auto with roof_laws; reflexivity.
Qed.
Next Obligation.
  destruct x0; reflexivity.
Qed.
Next Obligation.
  destruct x0, y0, z; simpl; auto with roof_laws;
  rewrite ?id_left, ?id_right;
  reflexivity.
Qed.
