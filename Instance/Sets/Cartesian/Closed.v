Require Import Category.Lib.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.

Generalizable All Variables.

Local Set Warnings "-intuition-auto-with-star".

(** * Cartesian closure of [Sets] / * [Sets] 的笛卡尔闭包 *)

(*
 nLab: https://ncatlab.org/nlab/show/cartesian+closed+category
 nLab: https://ncatlab.org/nlab/show/exponential+object
 Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category
 Wikipedia: https://en.wikipedia.org/wiki/Exponential_object

 [Sets] is the category of setoids (Bishop sets: a carrier type with an
 equivalence relation ≈), and it is cartesian closed.  The exponential
 z^y = [exponent_obj y z] is the setoid SetoidMorphism y z of ≈-respecting
 maps y → z, equipped with the pointwise equivalence f ≈ g ⟺ ∀x, f x ≈ g x
 (the function setoid, via [SetoidMorphism_Setoid]).

 The CCC adjunction (- × y) ⊣ (- ^ y) is witnessed by [exp_iso], the
 bijection Hom(x × y, z) ≅ Hom(x, z^y): the forward (curry) direction sends
 f : x × y → z to λx.λy. f (x, y), and the inverse (uncurry) direction sends
 g : x → z^y to λp. g (fst p) (snd p).  Evaluation z^y × y → z is the image
 of the identity under uncurry, namely λp. (fst p) (snd p).

 This construction is fully constructive: the function setoid and currying
 require no choice, so [Sets] is cartesian closed in plain intuitionistic
 logic.

 This instance must appear in a separate file, because the Closed structure
 makes use of isomorphisms in [Sets]. 

 --------
 nLab：https://ncatlab.org/nlab/show/cartesian+closed+category
 nLab：https://ncatlab.org/nlab/show/exponential+object
 维基百科：https://en.wikipedia.org/wiki/Cartesian_closed_category
 维基百科：https://en.wikipedia.org/wiki/Exponential_object

 [Sets] 是集合类（Bishop 集：具有等价关系 ≈ 的载体类型）的范畴，并且它是笛卡尔闭的。指数对象 z^y = [exponent_obj y z] 是集合类 SetoidMorphism y z 的 ≈-保持映射 y → z，配备了逐点等价 f ≈ g ⟺ ∀x, f x ≈ g x（函数集合类，依据 [SetoidMorphism_Setoid]）。

 CCC 的伴随 (- × y) ⊣ (- ^ y) 由 [exp_iso] 体现，同态 Hom(x × y, z) ≅ Hom(x, z^y)：正向（柯里化）将 f : x × y → z 变为 λx.λy. f (x, y)，逆向（反柯里化）将 g : x → z^y 变为 λp. g (fst p) (snd p)。评估 z^y × y → z 是反柯里化下恒等映射的像，即 λp. (fst p) (snd p)。这个构造是完全构造性的：函数等价关系和柯里化不需要选择，因此  [Sets] 在普通直觉逻辑中是笛卡尔闭合的。

 这个实例必须出现在单独的文件中，因为闭合结构使用了 [Sets] 中的同构。
*)

#[export]
Program Instance Sets_Closed : @Closed Sets _ := {
  exponent_obj := fun x y =>
    {| carrier := SetoidMorphism x y
     ; is_setoid := @SetoidMorphism_Setoid x y |};

  exp_iso := fun _ _ _ =>
    {| to   := {| morphism := fun f =>
                    {| morphism := fun x =>
                         {| morphism := fun y => f (x, y) |} |} |}
     ; from := {| morphism := fun f =>
                    {| morphism := fun p => f (fst p) (snd p) |} |} |}
}.
Next Obligation.
  proper; destruct f; simpl.
  apply proper_morphism.
  split; simpl; intuition; auto with *.
Qed.
Next Obligation.
  proper; destruct f; simpl.
  apply proper_morphism.
  split; simpl; intuition; auto with *.
Qed.
Next Obligation.
  proper; simpl in *.
  destruct f; simpl in *.
  unfold Proper, respectful, SetoidMorphism_equiv in proper_morphism.
  rewrite (proper_morphism _ _ X).
  destruct (morphism y).
  apply proper_morphism0; assumption.
Qed.
