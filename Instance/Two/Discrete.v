Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** The discrete category on two objects. / 在两个对象上的离散范畴。 *)

(*
 nLab:      https://ncatlab.org/nlab/show/discrete+category
 Wikipedia: https://en.wikipedia.org/wiki/Discrete_category

 The discrete category on a set has that set as objects and only identity
 morphisms; equivalently |hom(x, y)| is 1 when x = y and 0 when x ≠ y.  Here
 the object set is the two-element {TwoDX, TwoDY}, so the only arrows are the
 identities TwoDIdX, TwoDIdY.  Unlike the interval category 2 of
 [Instance/Two.v] (the “walking arrow”, which carries one non-identity arrow
 TwoX ~> TwoY), there is NO arrow between the two distinct objects in either
 direction (hence both TwoDHom_X_Y_absurd and TwoDHom_Y_X_absurd below).

 A functor Two_Discrete ⟶ C is exactly an ordered pair of objects of C (the
 images of TwoDX and TwoDY); see [Pick_Two].  Two_Discrete is therefore the
 shape category for binary products and coproducts: the limit of a diagram of
 shape Two_Discrete is a binary product, and the colimit is a binary
 coproduct (see [Structure/Limit/Cartesian.v]). 

 --------
 nLab:       https://ncatlab.org/nlab/show/discrete+category 
 Wikipedia:  https://en.wikipedia.org/wiki/Discrete_category 

 集合上的离散范畴，其对象就是该集合，且只有恒等态射；等价地，当 x = y 时 |hom(x, y)| 为 1，当 x ≠ y 时为 0。这里的对象集合是两元素集合 {TwoDX, TwoDY}，因此唯一的箭头是恒等箭头 TwoDIdX 和 TwoDIdY。与 [Instance/Two.v] 的区间范畴 2（“行走箭头”，它携带一个非恒等箭头 TwoX ~> TwoY）不同，在两个不同对象之间的任意方向上都不存在箭头（因此下面有 TwoDHom_X_Y_absurd 和 TwoDHom_Y_X_absurd）。函子 Two_Discrete ⟶ C 恰好是 C 的一对有序对象（TwoDX 和 TwoDY 的像）；参见 [Pick_Two]。因此，Two_Discrete 是二元积和二元余积的形状范畴：一个形状为 Two_Discrete 的图的极限是二元积，余极限是二元余积（参见 [Structure/Limit/Cartesian.v]）。
*)

Inductive TwoDObj : Set := TwoDX | TwoDY.

Inductive TwoDHom : TwoDObj → TwoDObj → Set :=
  | TwoDIdX : TwoDHom TwoDX TwoDX
  | TwoDIdY : TwoDHom TwoDY TwoDY.

Definition TwoDHom_inv_t : ∀ x y, TwoDHom x y → Prop.
Proof.
  intros [] [] f.
  - exact (f = TwoDIdX).
  - exact False.          (* Unused, any Prop is ok here / 未使用，这里任何道具都可以 *)
  - exact False.          (* Unused, any Prop is ok here / 未使用，这里任何道具都可以 *)
  - exact (f = TwoDIdY).
Defined.

Corollary TwoDHom_inv x y f : TwoDHom_inv_t x y f.
Proof. destruct f; reflexivity. Qed.

Lemma TwoDHom_X_Y_absurd : TwoDHom TwoDX TwoDY → False.
Proof. inversion 1. Qed.

#[export] Hint Extern 4 => contradiction TwoDHom_X_Y_absurd : two_laws.

Lemma TwoDHom_Y_X_absurd : TwoDHom TwoDY TwoDX → False.
Proof. inversion 1. Qed.

#[export] Hint Extern 4 => contradiction TwoDHom_Y_X_absurd : two_laws.

Local Set Warnings "-intuition-auto-with-star".

(* The discrete category 2 has two objects and their identity morphisms. / 离散范畴2有两个对象及它们的恒等态射。 *)

Program Definition Two_Discrete : Category := {|
  obj     := TwoDObj;
  hom     := TwoDHom;
  homset  := Morphism_equality;
  id      := fun x => match x with
    | TwoDX => TwoDIdX
    | TwoDY => TwoDIdY
    end;
  compose := fun x y z (f : TwoDHom y z) (g : TwoDHom x y) =>
    match x, y, z with
    | TwoDX, TwoDX, TwoDX => TwoDIdX
    | TwoDY, TwoDY, TwoDY => TwoDIdY
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
Next Obligation.
  destruct x, y, z; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation.
  destruct x, y; auto with two_laws;
  symmetry; exact (TwoDHom_inv _ _ f).
Qed.
Next Obligation.
  destruct x, y; auto with two_laws;
  symmetry; exact (TwoDHom_inv _ _ f).
Qed.
Next Obligation.
  destruct x, y, z, w; auto with two_laws; intuition.
Qed.
Next Obligation.
  destruct x, y, z, w; auto with two_laws; intuition.
Qed.

(*
 A functor Two_Discrete ⟶ C is exactly a choice of two objects of C.  Given
 a and b, Pick_Two is the functor sending TwoDX to a and TwoDY to b; the only
 arrows are identities, so fmap sends each to id (the off-diagonal cases are
 uninhabited).  This presents the pair (a, b) as a discrete diagram, used to
 build binary (co)products as (co)limits. 

 --------
 函子 Two_Discrete ⟶ C 恰好是对 C 中两个对象的选择。给定 a 和 b，Pick_Two 是将 TwoDX 映射到 a、TwoDY 映射到 b 的函子；唯一的箭头是恒等箭头，因此 fmap 将每个箭头映射为 id（非对角情况是不存在的）。这将对 (a, b) 表示为一个离散图，用于构建二元（余）积作为（余）极限。
*)

Program Definition Pick_Two {C : Category} (a b : C) :
  Two_Discrete ⟶ C := {|
  fobj := λ x,
    match x with
    | TwoDX => a
    | TwoDY => b
    end;
  fmap := λ x y _,
    match x, y with
    | TwoDX, TwoDX => id
    | TwoDY, TwoDY => id
    | _,    _      => !
    end
|}.
Next Obligation.
  destruct x, y; auto with two_laws.
Qed.
Next Obligation.
  destruct x, y; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation.
  destruct x, y; auto with two_laws;
  intuition; discriminate.
Qed.
Next Obligation.
  destruct x; auto with two_laws; cat.
Qed.
Next Obligation.
  destruct x, y, z; auto with two_laws; cat.
Qed.
