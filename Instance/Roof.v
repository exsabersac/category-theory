Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** The walking span (span shape category). / 行走跨度（跨度形状类别）。 *)

(*
 The category of three objects and two non-identity arrows, both pointing
 from the apex RZero to the other two objects (plus the three identities):

 RZero
 /     \
 ZeroNeg/       \ZeroPos
 /         \
 v           v
 RNeg         RPos

 This is the span shape `RNeg ← RZero → RPos`, i.e. the indexing category
 whose functors out of it are spans: a functor [Roof ⟶ C] is a span in C,
 and a functor out of the opposite [Roof^op ⟶ C] is a cospan in C (see
 [Structure/Span.v]). A colimit over a span is a pushout; dually, a limit
 over a cospan (a functor out of [Roof^op]) is a pullback (see
 [Structure/Pullback/Limit.v]).

 nLab:      https://ncatlab.org/nlab/show/span
 Wikipedia: https://en.wikipedia.org/wiki/Span_(category_theory) 

 --------
 由三个对象和两个非单位元箭头组成的范畴，它们都指向
 从顶点RZero到另外两个对象（加上三个恒等式）：

 RZero
 /     \
 零负/ \零零
 /         \
 V v
 RNeg RPos

 这就是张成形状`RNeg ← RZero → RPos`，即指标范畴
 其中的函子是张成：函子[Roof ⟶ C]是C中的一个张成，
 而来自相反[Roof^op ⟶ C]的函子则是 C 中的共span（参见
 [Structure/Span.v]）。跨度上的余极限是推出;对偶地，是极限
 在一个余跨（[Roof^op] 的函子）上，是一个拉回（参见
 [Structure/Pullback/Limit.v]）。

 nLab：https://ncatlab.org/nlab/show/span
 维基百科：https://en.wikipedia.org/wiki/Span_(category_theory)
*)

Inductive RoofObj : Set := RNeg | RZero | RPos.

Inductive RoofHom : RoofObj → RoofObj → Set :=
  | IdNeg   : RoofHom RNeg  RNeg
  | ZeroNeg : RoofHom RZero RNeg
  | IdZero  : RoofHom RZero RZero
  | ZeroPos : RoofHom RZero RPos
  | IdPos   : RoofHom RPos  RPos.

Definition RoofHom_inv_t : ∀ x y, RoofHom x y → Prop.
Proof.
  intros [] [] f.
  - exact (f = IdNeg).
  - exact False.          (* Unused, any Prop is ok here / 未使用，这里任何道具都可以 *)
  - exact False.          (* Unused, any Prop is ok here / 未使用，这里任何道具都可以 *)
  - exact (f = ZeroNeg).
  - exact (f = IdZero).
  - exact (f = ZeroPos).
  - exact False.          (* Unused, any Prop is ok here / 未使用，这里任何道具都可以 *)
  - exact False.          (* Unused, any Prop is ok here / 未使用，这里任何道具都可以 *)
  - exact (f = IdPos).
Defined.

Corollary RoofHom_inv x y f : RoofHom_inv_t x y f.
Proof. destruct f; reflexivity. Qed.

Lemma RNeg_RNeg_id (f : RoofHom RNeg RNeg) : f = IdNeg.
Proof. exact (RoofHom_inv _ _ f). Qed.

Lemma RZero_RPos_id (f : RoofHom RZero RPos) : f = ZeroPos.
Proof. exact (RoofHom_inv _ _ f). Qed.

Lemma RNeg_RZero_absurd : RoofHom RNeg RZero → False.
Proof. inversion 1. Qed.

#[export] Hint Extern 4 => contradiction RNeg_RZero_absurd : roof_laws.

Lemma RPos_RZero_absurd : RoofHom RPos RZero → False.
Proof. inversion 1. Qed.

#[export] Hint Extern 4 => contradiction RPos_RZero_absurd : roof_laws.

Lemma RNeg_RPos_absurd : RoofHom RNeg RPos → False.
Proof. inversion 1. Qed.

#[export] Hint Extern 4 => contradiction RNeg_RPos_absurd : roof_laws.

Lemma RPos_RNeg_absurd : RoofHom RPos RNeg → False.
Proof. inversion 1. Qed.

#[export] Hint Extern 4 => contradiction RPos_RNeg_absurd : roof_laws.

Program Definition Roof : Category := {|
  obj    := RoofObj;
  hom    := RoofHom;
  (*
 Each homset is a subsingleton (at most one arrow between any two
 objects), so the trivial relation True is already an equivalence and
 respects composition; any two parallel arrows are interchangeable. 

 --------
 每个同态集都是子单元（任意两个对象之间最多只有一个箭头），因此平凡关系 True 已经是一个等价关系并且满足组合；任意两个平行箭头是可互换的。
*)
  homset := fun x y => {| equiv := fun (f g : RoofHom x y) => True |};
  id     := fun x => match x return RoofHom x x with
    | RNeg  => IdNeg
    | RZero => IdZero
    | RPos  => IdPos
    end
|}.
Next Obligation.
  destruct x, y, z;
  try constructor;
  try inversion f;
  try inversion g.
Defined.
