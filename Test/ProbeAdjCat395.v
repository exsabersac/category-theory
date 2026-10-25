(*
Boundary probe for Instance/Adj.v and Instance/Adj/Forgetful.v.

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.7,
   book p. 101: the category of adjunctions, whose arrows are the conjugate
   pairs <sigma, tau>.  His display puts sigma FORWARD on the left adjoints
   and tau BACKWARD on the right adjoints.

   THE ONE DESIGN DECISION OF Instance/Adj.v IS THAT VARIANCE, and it is
   expressed by the ORDER of the two adjunction arguments handed to
   [Conjugate]: the hom x -> y is [Conjugate (adjobj_adj y) (adjobj_adj x)].
   Nothing in a type checker complains if that order is flipped -- the
   result is simply a different, and wrong, category.  This file pins it.

   Each negative below was stripped one at a time and compiled alone.  A
   negative that passes prints nothing, so reading its error text requires
   stripping it first.

   These facts were measured while Instance/Adj.v was built but could be
   pinned nowhere at the time; this file is where they are pinned.

--------
用于 Instance/Adj.v 和 Instance/Adj/Forgetful.v 的边界探测器。

麦克·莱恩，《为在职数学家准备的范畴》，第二版，第 IV.7 节，第 101 页：伴随范畴，其箭头是共轭对 <sigma, tau>。他的展示把 sigma 放在左伴随的前向，而 tau 放在右伴随的后向。

Instance/Adj.v 的唯一设计决策是方差，它通过传递给 [Conjugate] 的两个陪集参数的顺序来表示：同态 x -> y 是 [Conjugate (adjobj_adj y) (adjobj_adj x)]。如果交换这个顺序，类型检查器不会报错——结果只是一个不同的、错误的类别。这个文件固定了它。

下面的每一个否定项都是一次剥离并单独编译的。一个通过的否定项不会打印任何内容，因此要读取其错误文本，必须先剥离它。

这些事实是在 Instance/Adj.v 构建时测量的，但当时无法固定；这个文件是它们被固定的地方。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Instance.Adj.
Require Import Category.Instance.Adj.Forgetful.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(*
Instrument: this file's negatives are only as good as the harness.  A
   name that exists nowhere must be refused.

--------
工具：这个文件的底片的好坏仅取决于马具。一个不存在的名称必须被拒绝。
*)
Fail Check p395_no_such_constant_anywhere.

Section Variance.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D} (A  : F  ⊣ U).
Context {F' : D ⟶ C} {U' : C ⟶ D} (A' : F' ⊣ U').

(*
CONTROLS.  The constants the negative names must appear outside it, or a
   rename would leave the negative vacuously green.

--------
控制。负常数名称必须出现在它之外，否则重命名会使负数毫无意义地呈现绿色。
*)
Check @Conjugate.
Check A.
Check A'.
Check (fun (x : D) => F x).
Check (fun (a : C) => U a).

(*
POSITIVE: with the adjunction arguments SWAPPED, Mac Lane's labelling
   typechecks -- sigma forward on the left adjoints, tau backward on the
   right adjoints.

--------
积极的：在交换了附加参数后，Mac Lane 的标记类型检查通过——左附加的 sigma 向前，右附加的 tau 向后。
*)
Check (fun (s : F ⟹ F') (t : U' ⟹ U) => Conjugate A' A s t).

(*
NEGATIVE 1 (TYPING).  The OTHER labelling does not fit the same slots.
   Stripped, this reports a plain "has type ... while it is expected to have
   type ...", with no universe clause: [Conjugate A' A] demands its third
   argument at [F ⟹ F'], so handing it [F' ⟹ F] is a type mismatch and
   not a unification complaint about universes.

--------
负 1（输入类型）。其他标记不适用于相同的槽。剥离后，这会报告一个简单的“具有类型...而预期具有类型...”，没有宇宙条款：[Conjugate A' A] 在 [F ⟹ F'] 处需要它的第三个参数，因此传递 [F' ⟹ F] 是类型不匹配，而不是关于宇宙的统一投诉。
*)
Fail Check (fun (s : F' ⟹ F) (t : U ⟹ U') => Conjugate A' A s t).

End Variance.

Section HomShape.

Context {C D : Category}.

(* CONTROLS for the names the next negative mentions. / 控制下一个消极提及的名称。 *)
Check @ConjPair.
Check @conj_left.
Check @conj_right.
Check @conj_pair_law.
Check @adjobj_adj.

(* The hom of [Adj C D] IS the conjugate-pair record, on the nose. / [Adj C D] 的 hom 是共轭对记录，正中要点。 *)
Example adj_hom_is_conjpair (x y : AdjObj C D) :
  (x ~{Adj C D}~> y) = @ConjPair C D x y := eq_refl.

(*
And the law field is the SWAPPED application, which is the variance the
   negative above guards.

--------
而法律领域是被交换的应用，这就是上述负面防护的差异。
*)
Example adj_law_is_swapped (x y : AdjObj C D) (f : x ~{Adj C D}~> y) :
  Conjugate (adjobj_adj y) (adjobj_adj x) (conj_left f) (conj_right f)
  := conj_pair_law f.

End HomShape.

Section ForgetfulShape.

(* CONTROLS. / 控制。 *)
Check @AdjForgetLeft.
Check @AdjForgetRight.

(*
The left forgetful functor is covariant onto the left adjoints; the
   right one is displayed on the OPPOSITE category, which is how Mac Lane's
   [A^(adj)X]^op -> X^A is rendered.  Both types are pinned here so that a
   later change of variance breaks this file rather than passing quietly.

--------
左忘记函子是协变的，作用于左伴随；右边的在对偶范畴上展示，这就是 Mac Lane 的 [A^(adj)X]^op -> X^A 的呈现方式。两种类型都在这里被固定，以便稍后的变异更改会破坏此文件，而不是悄无声息地通过。
*)
Example adj_forget_left_type (C D : Category) :
  AdjForgetLeft C D = AdjForgetLeft C D := eq_refl.

Check (fun C D : Category => AdjForgetLeft C D : Adj C D ⟶ [D, C]).
Check (fun C D : Category => AdjForgetRight C D : (Adj C D)^op ⟶ [C, D]).

(*
NEGATIVE 2 (TYPING).  The right forgetful functor is NOT covariant on
   [Adj C D]; ascribing it there is refused.  This is the contravariance,
   pinned.

--------
负 2（输入）。右忘记函子在 [Adj C D] 上不是协变的；在此处赋值会被拒绝。这就是变逆性，已固定。
*)
Fail Check (fun C D : Category => AdjForgetRight C D : Adj C D ⟶ [C, D]).

End ForgetfulShape.
