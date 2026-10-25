Require Import Category.Lib.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Cocartesian.

Generalizable All Variables.

(* * * Coproducts of setoids (disjoint union) / * * 集合等价类的积余（不相交并） *)

(*
 nLab: https://ncatlab.org/nlab/show/coproduct
 Wikipedia: https://en.wikipedia.org/wiki/Coproduct

 The coproduct of two setoids in [Sets] is their disjoint union. The carrier
 is the sum type [carrier x + carrier y], and two elements are equivalent
 exactly when they sit in the same summand and are equivalent there: [inl z]
 and [inl w] agree iff [z ≈ w] in [x], [inr z] and [inr w] agree iff [z ≈ w]
 in [y], and elements drawn from different summands are never identified (the
 cross cases reduce to [False]). The injections are the constructors
 [inl : x ~> x + y] and [inr : y ~> x + y].

 The universal property is witnessed by copairing: given [f : x ~> z] and
 [g : y ~> z], the case-split map [fun s => match s with inl a => f a
 | inr b => g b end] is the unique morphism [x + y ~> z] with [fork f g ∘ inl
 ≈ f] and [fork f g ∘ inr ≈ g]. (Here [fork], [exl], [exr] are the
 product-of-[C^op] fields through which [Cocartesian] is defined, so they
 supply the coproduct's copairing and injections with arrows reversed.) 

 --------
 nLab:  https://ncatlab.org/nlab/show/coproduct 
 维基百科:  https://en.wikipedia.org/wiki/Coproduct 

 在 [Sets] 中，两个集合体的余积是它们的不相交并集。载体是和类型 [carrier x + carrier y] ，两个元素恰好当它们位于同一个求和项并在该处相等时才相等：[inl z] 和 [inl w] 相等当且仅当 [z ≈ w] 在 [x] 中，[inr z] 和 [inr w] 相等当且仅当 [z ≈ w] 在 [y] 中，并且来自不同求和项的元素永远不会被识别（交叉情况归约到 [False]）。注入是构造函数 [inl : x ~> x + y] 和 [inr : y ~> x + y]。通过共配对可以证明这个泛性质：给定 [f : x ~> z] 和 [g : y ~> z]，case 分裂映射 [fun s => match s with inl a => f a | inr b => g b end] 是唯一的态射 [x + y ~> z]，满足 [fork f g ∘ inl ≈ f] 和 [fork f g ∘ inr ≈ g]。（这里 [fork]、[exl]、[exr] 是 [C^op] 的积字段，通过它们定义了 [Cocartesian]，因此它们为余积的共配对和注入提供了箭头方向相反的态射。）
*)

#[export]
Program Instance Sets_Cocartesian : @Cocartesian Sets := {
  product_obj := fun x y =>
    {| carrier := (carrier x + carrier y)%type
     ; is_setoid :=
         {| equiv := fun z w =>
              match z with
              | Datatypes.inl z =>
                match w with
                | Datatypes.inl w => @equiv _ x z w
                | Datatypes.inr _ => False
                end
              | Datatypes.inr z =>
                match w with
                | Datatypes.inl _ => False
                | Datatypes.inr w => @equiv _ y z w
                end
              end
          ; setoid_equiv := _
          |} |};
  fork := fun _ _ _ f g =>
    {| morphism := fun x =>
         match x with
         | Datatypes.inl x => f x
         | Datatypes.inr x => g x
         end |};
  exl := fun _ _ => {| morphism := Datatypes.inl |};
  exr := fun _ _ => {| morphism := Datatypes.inr |}
}.
Next Obligation.
  proper.
  destruct f, g; intuition.
  destruct y, x; intuition;
  destruct z; intuition.
Qed.
Next Obligation.
  proper.
  destruct x2; intuition.
Qed.
Next Obligation.
  simplify; intuition;
  now match goal with
    [ H : ∀ _ : _ + _, _ ≈ _ |- _ ] => rewrite H
  end.
Qed.
