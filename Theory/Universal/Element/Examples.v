Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Coq.Nat.
Require Import Category.Theory.Universal.Element.
Require Import Category.Theory.Universal.Element.Elements.

Generalizable All Variables.

(** * Non-vacuity: the natural numbers as a universal element / * 非空性：自然数作为一种通用元素 *)

(*
The class of Theory/Universal/Element.v is inhabited, and by the object
   the tree already computes with.  Instance/Coq/Nat.v exhibits
   [nat_succ_Representable : Representable Endos_Forget] -- the pair
   ⟨(nat, S), 0⟩ representing the forgetful functor from sets-with-an-endomap
   -- and separately checks by [reflexivity] that the image of the identity
   under its representing isomorphism is [O] ([nat_universal_element]).
   That check is the SPECIAL CASE, for one functor, of the general equation
   [ue_of_repr_elem]; here the general class is run at that representation and
   the same [O] comes back out, by [eq_refl].

   This is what makes the file's central claim non-vacuous in the strong
   sense the brief asks for: the general definition is not merely inhabited,
   it RECOVERS the concrete criterion the tree had computed by hand.

   WHAT IS AND IS NOT RECOVERED.  What is: the universal element itself, on
   the nose, and -- through Theory/Universal/Element/Elements.v -- the
   initial object of the category of elements that Riehl's Proposition 2.4.8
   produces from it.  What is NOT: Instance/Coq/Nat.v's [repr_initial]
   proper.  That lands in [FAlg NatF], and the passage from
   [Elements Endos_Forget] to [FAlg NatF] is a comparison of categories the
   tree does not carry (Nat.v builds the object-level dictionary
   [alg_of_triple] / [alg_hom_clauses] but no functor).  So [repr_initial] is
   NOT re-derived, NOT made redundant, and NOT claimed to follow; what is
   shown is that the general machine produces the same universal element and
   an initial object of the general elements category.

--------
Theory/Universal/Element.v 的类是有对象的，并且通过该对象，树已经可以进行计算。Instance/Coq/Nat.v 展示了 [nat_succ_Representable : Representable Endos_Forget] —— 对 ⟨(nat, S), 0⟩，表示从带有自映射的集合到集合的遗忘函子 —— 并且通过 [reflexivity] 单独检查其表示同构下的恒等映射的像是 [O] ([nat_universal_element])。该检查是一般方程 [ue_of_repr_elem] 的特殊情况，对于一个函子而言；在该表示下运行一般类，同样的 [O] 会被返回，依据 [eq_refl]。

这就是使文件的核心主张在摘要要求的强意义上非空洞的原因：一般定义不仅仅是被使用的，它还恢复了树手工计算出的具体标准。

什么是已恢复的，什么是不恢复的。什么是：普遍元素本身，在鼻子上，并且——通过 Theory/Universal/Element/Elements.v ——Riehl 的命题 2.4.8 从中生成的元素范畴的初始对象。什么不是：Instance/Coq/Nat.v 的 [repr_initial] 本体。那会进入 [FAlg NatF]，而从 [Elements Endos_Forget] 到 [FAlg NatF] 的过渡是范畴的比较，树结构没有携带（Nat.v 构建了对象级字典 [alg_of_triple] / [alg_hom_clauses]，但没有函子）。因此 [repr_initial] 并未重新推导、并未变得多余、也未被声称随之而来；所展示的是通用机器生成相同的普遍元素以及通用元素范畴的初始对象。
*)

(*
The universal element of [Endos_Forget], produced by the general class
   from the representation Instance/Coq/Nat.v builds.

--------
由表示 Instance/Coq/Nat.v 构建的通用类生成的 [Endos_Forget] 的通用元素。
*)
Definition nat_UniversalElement : UniversalElement Endos_Forget :=
  UniversalElement_of_Representable nat_succ_Representable.

(* Its object is the representing object, by conversion. / 它的对象是通过转换表示的对象。 *)
Example nat_ue_obj : @ue_obj Endos Endos_Forget nat_UniversalElement = NatSucc.
Proof. reflexivity. Qed.

(*
... and its element is [O] -- Instance/Coq/Nat.v's
   [nat_universal_element], obtained here through the general definition
   rather than checked for this one functor.  Note the type: an element of
   [Endos_Forget NatSucc] IS a [nat].

--------
... 它的元素是 [O] -- 来自 Instance/Coq/Nat.v 的 [nat_universal_element]，通过通用定义获得，而不是针对这个函子单独检查。注意类型：[Endos_Forget NatSucc] 的一个元素是一个 [nat]。
*)
Example nat_ue_elem : @ue_elem Endos Endos_Forget nat_UniversalElement = O.
Proof. reflexivity. Qed.

(*
The general equation of which Nat.v's check is the instance, at this
   representation: the universal element is the image of the identity.

--------
这条 Nat.v 检查所示的通用方程，在这个表示中：通用元素是恒等映射的像。
*)
Example nat_ue_is_image_of_id :
  @ue_elem Endos Endos_Forget nat_UniversalElement
    = transform (to nat_succ_represents) NatSucc (id{Endos}).
Proof. reflexivity. Qed.

(*
Mac Lane's unique-factorization clause, at this instance: every element n
   of every [Endos]-object is reached from [O] by a unique endomorphism-
   preserving map out of (nat, S) -- which is iteration.  The general class
   supplies it; nothing here is proved.

--------
Mac Lane 独特分解条款，在此实例中：每个 [Endos] 对象的每个元素 n 都可以通过来自 (nat, S) 的唯一保持自同态的映射从 [O] 达到——这就是迭代。一般类提供它；这里没有任何被证明。
*)
Definition nat_ue_factor (y : Endos) (n : Endos_Forget y)
  : NatSucc ~{Endos}~> y :=
  unique_obj (@ue_universal Endos Endos_Forget nat_UniversalElement y n).

Example nat_ue_factor_at_zero (y : Endos) (n : Endos_Forget y) :
  fmap[Endos_Forget] (nat_ue_factor y n) O ≈ n.
Proof. exact (unique_property (@ue_universal _ _ nat_UniversalElement y n)). Qed.

(*
And Riehl's Proposition 2.4.8 at this instance: the pair ⟨(nat, S), 0⟩ is
   an initial object of the category of elements of [Endos_Forget].  This is
   the general form of Instance/Coq/Nat.v's [repr_initial]; see the header on
   what is and is not claimed about the relation between the two.

--------
并且 Riehl 的命题 2.4.8 在此情况下：对 ⟨(nat, S), 0⟩ 是 [Endos_Forget] 元素范畴的初始对象。这是 Instance/Coq/Nat.v 中 [repr_initial] 的一般形式；请参阅头部说明关于两者关系的声明与非声明内容。
*)
Definition nat_Elements_Initial : @Initial (Elements Endos_Forget) :=
  Elements_Initial Endos_Forget
    (AUniversalElement_of_UniversalElement nat_UniversalElement).

Example nat_Elements_Initial_obj :
  `1 (@initial_obj (Elements Endos_Forget) nat_Elements_Initial) = NatSucc.
Proof. reflexivity. Qed.

Example nat_Elements_Initial_elem :
  `2 (@initial_obj (Elements Endos_Forget) nat_Elements_Initial) = O.
Proof. reflexivity. Qed.
