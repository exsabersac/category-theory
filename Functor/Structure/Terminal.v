Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Terminal.

Generalizable All Variables.

(** Terminal-object-preserving functors.  / 终端对象保留函子。*)

(*
nLab: https://ncatlab.org/nlab/show/terminal+object
   Wikipedia: https://en.wikipedia.org/wiki/Initial_and_terminal_objects

   A terminal functor F : C ⟶ D between categories with terminal objects
   preserves the terminal object (the nullary, or empty, product). The
   terminal object is the limit of the empty diagram, so any limit-preserving
   functor carries it to a terminal object; a functor preserves it exactly
   when the canonical comparison between F 1 and 1 is an isomorphism.

   The comparison is recorded as the field [fobj_one_iso : 1 ≅ F 1], oriented
   in the lax direction so that its forward map [to fobj_one_iso : 1 ~> F 1]
   is the unit comparison η : I → F I of a (lax/strong) monoidal functor for
   the cartesian monoidal structure (tensor = ×, unit = the terminal object).
   The canonical map F 1 ~> 1 — the unique morphism into the terminal object
   1 of D — is then its inverse [from fobj_one_iso]; preservation means that
   unique map is invertible. This orientation matches [pure_iso : I ≅ F I] in
   Functor/Structure/Monoidal/Pure.v.

   This is the nullary-product half of a cartesian (strong monoidal) functor;
   the binary-product half F (x × y) ≅ F x × F y is the separate concern
   [CartesianFunctor] in the sibling file, and the two together give the full
   cartesian functor. The dual notion, a functor preserving the initial
   object, is named [InitialFunctor] below via the opposite functor F^op,
   following the library's built-in duality. 

--------
nLab：https://ncatlab.org/nlab/show/terminal+object
 维基百科：https://en.wikipedia.org/wiki/Initial_and_terminal_objects

具有终端对象的类别之间的终端函子 F : C ⟶ D
 保留最终对象（无效的或空的产品）。 的
 终端对象是空图的极限，因此任何保留极限的
 函子将其传递给终端对象； 函子准确地保留了它
 当 F 1 和 1 之间的规范比较是同构时。

比较记录为字段[fobj_one_iso : 1 ≅ F 1]，面向
 在宽松的方向上，使其向前映射 [to fobj_one_iso : 1 ~> F 1]
 是（松/强）幺半群函子的单位比较 η : I → F I
 笛卡尔幺半群结构（张量 = ×，单位 = 终端对象）。 
规范映射 F 1 ~> 1 — 终端对象的唯一态射
 D — 的 1 则为其逆 [from fobj_one_iso]； 保存意味着
 独特的地图是可逆的。 该方向与 [pure_iso : I ≅ F I] 相匹配
 函子/结构/Monoidal/Pure.v.

这是笛卡尔（强幺半群）函子的零积一半；
 二元乘积的一半 F (x × y) ≅ F x × F y 是单独的关注点
 [CartesianFunctor] 在同级文件中，两者一起给出了完整的
 笛卡尔函子。 对偶概念，保留初始值的函子
 对象，通过相反的函子 F^op 在下面被命名为 [InitialFunctor]，
 遵循库的内置二元性。 
*)

Section TerminalFunctor.

Context `{F : C ⟶ D}.
Context `{@Terminal C}.
Context `{@Terminal D}.

Class TerminalFunctor := {
  (* the comparison iso 1 ≅ F 1 witnessing terminal-object preservation  / 比较 iso 1 ≅ F 1 见证终端对象保存*)
  fobj_one_iso : 1 ≅ F 1;

  (* F carries the unique map up to η: fmap ! ≈ η ∘ ! (with η = to fobj_one_iso)  / F 携带直到 η 的唯一映射：fmap ！ ≈ η ∘ ! （其中 η = fobj_one_iso）*)
  fmap_one {X : C} : fmap one ≈ to fobj_one_iso ∘ @one _ _ (F X)
}.

End TerminalFunctor.

(*
An initial functor preserves the initial object. Rather than restate the
   dual class, it is defined by reusing [TerminalFunctor] on the opposite
   functor F^op (the initial object of C is the terminal object of C^op),
   exploiting the library's built-in duality. The first notation infers the
   categories; the second names them explicitly, requiring C, D and F at
   object level. 

--------
初始函子保留初始对象。 而不是重述
 双类，它是通过在相反的位置重用 [TerminalFunctor] 来定义的
 函子 F^op （C 的初始对象是 C^op 的终端对象），
 利用库的内置二元性。 第一个符号推断
 类别； 第二个明确地命名它们，要求 C、D 和 F 位于
 对象级别。 
*)
Notation "'InitialFunctor' F" := (@TerminalFunctor _ _ (F^op) _ _)
  (at level 9) : category_theory_scope.
Notation "@InitialFunctor C D F" := (@TerminalFunctor (C^op) (D^op) (F^op) _ _)
  (at level 9) : category_theory_scope.
