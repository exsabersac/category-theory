Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.

Generalizable All Variables.

(** The internal-hom functor [-,-] : C^op ∏ C ⟶ C.  / 内部 hom 函子 [-,-] ： C^op ∏ C ⟶ C。*)

(*
nLab: https://ncatlab.org/nlab/show/internal+hom
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category
   Wikipedia: https://en.wikipedia.org/wiki/Exponential_object

   In a closed (here cartesian-closed) category C the hom is internalized:
   instead of the Set-valued external hom Hom(-,-) : C^op ∏ C ⟶ Sets, the
   exponential object provides an object [a, b] = b ^ a of C itself, so the
   internal hom is a bifunctor

       [-,-] : C^op ∏ C ⟶ C,   [a, b] := exponent_obj a b = b ^ a.

   It is contravariant in its first argument and covariant in its second:
   given (f, g) : (a, b) ~> (a', b') in C^op ∏ C — that is, f : a' ~{C}~> a
   (an arrow a ~{C^op}~> a') and g : b ~{C}~> b' — the action is

       [f, g] := curry (g ∘ eval ∘ second f) : b ^ a ~> b' ^ a',

   which pre-composes by f in the exponent and post-composes by g in the base.
   (Here [op f] only re-reads the C^op arrow f as the underlying C-morphism
   a' ~{C}~> a; the hom-sets are definitionally equal.)

   The exponential b ^ a is right adjoint to (- × a) — the tensor-hom (here
   product-hom) adjunction Hom(x × a, b) ≅ Hom(x, b ^ a) of [Closed] — and
   [eval : b ^ a × a ~> b] is its counit. So this functor is the internal
   counterpart of Functor/Hom.v, with the cartesian product playing the role
   of the monoidal tensor. 

--------
nLab：https://ncatlab.org/nlab/show/internal+hom
 维基百科：https://en.wikipedia.org/wiki/Cartesian_closed_category
 维基百科：https://en.wikipedia.org/wiki/Exponential_object

在封闭（这里是笛卡尔封闭）类别 C 中，hom 被内化：
 而不是集值外部 hom Hom(-,-) ： C^op ∏ C ⟶ 集合，
 指数提供了 C 本身的对象 [a, b] = b ^ a，因此
 内部 hom 是一个双函子

[-,-] : C^op ∏ C ⟶ C，[a, b] := exponent_obj a b = b ^ a。

它的第一个参数是逆变的，第二个参数是协变的：
 给定 C^op ∏ C 中的 (f, g) : (a, b) ~> (a', b') — 即 f : a' ~{C}~> a
 （箭头 a ~{C^op}~> a'）和 g : b ~{C}~> b' — 动作是

[f, g] := curry (g ∘ eval ∘ 第二个 f) : b ^ a ~> b' ^ a',

它由指数中的 f 预先组成，并由基数中的 g 进行后组成。 
（这里 [op f] 仅重新读取 C^op 箭头 f 作为底层 C 态射
 a' ~{C}~> a; hom 集在定义上是相等的。）

指数 b ^ a 右邻 (- × a) — 张量 hom（此处
 乘积 hom) [Closed] 的附加 Hom(x × a, b) ≅ Hom(x, b ^ a) — 并且
 [eval : b ^ a × a ~> b] 是它的单位。 所以这个函子是内部
 Functor/Hom.v 的对应部分，其中笛卡尔积发挥作用
 的幺半群张量。 
*)

Program Definition InternalHomFunctor `(C : Category)
        {E : @Cartesian C} {O : @Closed C _} : C^op ∏ C ⟶ C := {|
  fobj := fun p => @exponent_obj C E O (fst p) (snd p);   (* (a, b) ↦ b ^ a *)
  (* (f, g) ↦ curry (g ∘ eval ∘ second f): pre-compose f, post-compose g  / (f, g) ↦ curry (g ∘ eval ∘ 第二个 f)：预合成 f，后合成 g*)
  fmap := fun x y '(f, g) => curry (g ∘ eval ∘ second (op f))
|}.
Next Obligation.
  proper; simpl.
  now rewrites.
Qed.
Next Obligation. unfork; cat. Qed.
Next Obligation.
  rewrite <- !comp_assoc.
  rewrite curry_comp.
  symmetry.
  rewrite curry_comp.
  rewrite <- comp_assoc.
  apply compose_respects.
  - reflexivity.
  - symmetry.
    rewrite curry_comp_l.
    rewrite <- !comp_assoc.
    rewrite <- first_second.
    rewrite !comp_assoc.
    rewrite ump_exponents.
    rewrite <- !comp_assoc.
    rewrite <- second_comp.
    reflexivity.
Qed.

(*
Shorthand for the internal hom [a, b] = b ^ a as an object of C, with the
   ambient category inferred; this is the internal counterpart of the external
   hom-set Hom(a, b). 

--------
内部 hom [a, b] = b ^ a 的简写作为 C 的对象，其中
 推断环境类别； 这是外部的内部对应部分
 hom-设置 Hom(a, b)。 
*)
Notation "a ≈> b":= (InternalHomFunctor _ (a, b))
  (at level 89) : category_scope.
(* As above, but naming the category C explicitly when it cannot be inferred.  / 如上所述，但在无法推断时明确命名类别 C。*)
Notation "a ≈{ C }≈> b":= (InternalHomFunctor C (a, b))
  (at level 89) : category_scope.
