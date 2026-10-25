Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Limit.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Omega.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Skeleton.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Monoidal.

Require Import Coq.Vectors.Fin.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import Category.Instance.Fun.Closed.

Generalizable All Variables.

(** * Probe for Instance/Fun/Closed.v (issue #392) / * 探测实例/Fun/Closed.v（问题 #392） *)

(*
Mac Lane §IV.6 Exercise 5 ([maclane:IV.6:ex5]) and Awodey §8.7
   ([awodey:8.7:remark-pointwise-exponential-fails]).  Everything the
   target MEASURES and does not itself state is pinned here, from
   OUTSIDE that file, so that renaming a target constant breaks this
   probe rather than silently turning a guard green.  The [Require] list
   above mirrors the target's exactly, plus the target itself.

   SEVEN negatives of THREE kinds, told apart by the error text:

     1  FORMABILITY  the universe binders on [TwoFun] are load-bearing:
                     the same body without them is not an object of
                     [Omega, FinSet] at levels where the annotated one is
     2  FORMABILITY  [_2^op, Sets] elaborates only at a [Sets] whose
                     carrier universe IS [Set]
     3  CONVERSION   the presheaf P and the presheaf Q take different
                     values at [TwoY]
     4  CONVERSION   the objectwise candidate at [TwoY] is not the
                     two-element setoid, which is the value the naive
                     reading of the formula would want
     5  TYPING       the headline is about [Omega, FinSet]; it does not
                     apply to a cartesian structure on another category
     6  CONVERSION   [alpha_fam] separates exactly at its own stage
     7  TYPING       the engine's second half is about the TERMINAL
                     object of the functor category, not an arbitrary
                     source

   TWO formability, THREE conversion, TWO typing.  Each was stripped one
   at a time (its [Fail] removed, the file compiled alone) and the whole
   error read, since a passing [Fail] prints nothing.  The two
   formability ones end "universe inconsistency: Cannot enforce Set =
   ..."; the three conversion ones end "cannot unify" between two terms
   of ONE type; the two typing ones are a plain "has type ... while it
   is expected to have type ..." with NO "cannot unify" and no universe
   clause.  Every constant named inside a [Fail] is also named in a
   passing command outside every [Fail], below.

   ONE instrument check comes first, on a name that exists nowhere, so
   that [Fail] is known to be live in this file.

--------
Mac Lane §IV.6 练习 5 ([maclane:IV.6:ex5]) 和 Awodey §8.7 ([awodey:8.7:remark-pointwise-exponential-fails])。 目标测量的所有内容，如果它自己没有说明的，都被固定在这里，从该文件之外，以便重命名目标常量会破坏这个探针，而不是悄悄地使保护变为绿色。上面的 [Require] 列表完全对应目标列表，加上目标本身。

三种类型的七个阴性，通过错误文本区分：

1  可形成性  [TwoFun] 上的宇宙绑定器是承重的：
                     没有它们的相同主体在注释的层级下不属于 [Omega, FinSet]
     2  可形成性  [_2^op, Sets] 仅在载体宇宙为 [Set] 的 [Sets] 上展开
     3  转换   预层 P 和预层 Q 在 [TwoY] 取不同的值
     4  转换   [TwoY] 上的逐对象候选不是两元素等价类集合，这是公式朴素阅读想要的值
     5  TYPING       标题是关于 [Omega, FinSet] 的；它不适用于另一类别上的笛卡尔结构
6  转换       [alpha_fam] 恰好在其自身阶段分离
7  TYPING       引擎的后半部分是关于函子类别的 TERMINAL 对象，而不是任意源对象

两个可形成性，三个转换，两个类型。每个都是一次剥离（其 [Fail] 被移除，单独编译文件）并读取整个错误，因为通过的 [Fail] 什么也不打印。两个可形成性错误以“universe inconsistency: Cannot enforce Set = ...”结尾；三个转换错误以“cannot unify”在两个相同类型的项之间结尾；两个类型错误只是“has type ... while it is expected to have type ...”，没有“cannot unify”也没有宇宙条款。[Fail] 中命名的每个常量也在下方每个 [Fail] 外通过的命令中被命名。

首先进行一次仪表检查，检查一个不存在的名字，以便确认 [Fail] 在此文件中是活动的。
*)

(** ** Instrument / ** 乐器 *)

Fail Check p392_this_name_exists_nowhere.

(** ** Controls: every target constant, named outside any negative / ** 控制：每个目标常数，命名在任何否定之外 *)

Check @ccc_point.
Check @ccc_point_inj.
Check @fun_const_point.
Check @fun_const_point_inj.
Check @fun_hom_point.
Check @fun_hom_point_inj.
Check @nodup_map_inj.
Check @fin_no_nat_injection.
Check @FinSet_is_cartesian_closed.
Check @two_map.
Check @TwoFun.
Check @alpha_fam.
Check @alpha_fam_F1.
Check @Alpha.
Check @Alpha_distinct.
Check @finset_point_eq.
Check @exp_card.
Check @alpha_index.
Check @alpha_index_inj.
Check @fun_not_cartesian_closed.
Check @fun_pointwise_not_cartesian_closed.
Check @TwoOpInitial.
Check @PObj.
Check @PMap.
Check @PresheafP.
Check @two_elt.
Check @PresheafQ.
Check @PQNat.
Check @PQNat_distinct.
Check @pq_point.
Check @pq_point_distinct.
Check @objectwise_candidate.
Check @objectwise_candidate_subsingleton.
Check @awodey_pointwise_not_exponential.

(* Donor constants a negative names, guarded outside every negative. / 捐赠者将负常量命名为负名称，每个负数之外都受到保护。 *)
Check @Omega.
Check @FinSet.
Check @Sets.
Check @_2.
Check @Opposite.
Check @Functor_Category_Cartesian.
Check @Functor_Category_Terminal.
Check @FinSet_Cartesian.
Check @FinSet_Terminal.
Check @Sets_Cartesian.
Check @Sets_Closed.
Check @Omega_Initial.
Check @exponent_obj.
Check @le_t.
Check TwoY.

(** ** Positive readbacks the negatives are measured against / ** 正面回读作为衡量负面情况的标准 *)

(*
The two presheaves agree at [TwoX] on the nose: [PresheafQ] is a
   constant functor, and [PresheafP] takes [TwoX] to the terminal
   setoid, which is NOT the two-element one -- see negative 3 for the
   value at [TwoY], where they part company for the reason that drives
   the theorem.

--------
这两个预层在 [TwoX] 上完全一致：[PresheafQ] 是一个恒等函子，而 [PresheafP] 将 [TwoX] 映射到终端集体，并不是二元集体——在 [TwoY] 处的值请参见 -3，这也是它们分歧的原因，从而推动了定理的成立。
*)
Example p392_Q_at_TwoX : fobj[PresheafQ] TwoX = two_elt := eq_refl.

(*
Away from their own stages, two members of the family agree by
   computation; negative 6 is the same statement AT a stage.

--------
远离他们自己的舞台，家族的两名成员通过计算达成一致；负六在一个舞台上是相同的陈述。
*)
Example p392_alpha_off_stage : alpha_fam 0 3 = alpha_fam 1 3 := eq_refl.

(*
The initial object of [_2^op] IS [Two_Terminal], with no transport:
   [Initial C] is notation for [@Terminal (C^op)].

--------
[_2^op] 的初始对象是 [Two_Terminal]，没有传输：
   [Initial C] 是 [@Terminal (C^op)] 的表示法。
*)
Example p392_TwoOpInitial : TwoOpInitial = Two_Terminal := eq_refl.

(**
** Negative 1 (FORMABILITY): the binders on [TwoFun] are
       load-bearing

--------
** 负1（成型性）：[TwoFun]上的粘合剂是承重的
*)

(*
The same body as the target's, written WITHOUT universe binders.
   Universe minimization then pins [Omega]'s hom and proof universes to
   the literal [Set].

--------
与目标相同的主体，编写时不包含宇宙绑定器。然后宇宙最小化将 [Omega] 的本体和证明宇宙固定到字面上的 [Set]。
*)
Program Definition TwoFunUnann : Omega ⟶ FinSet := {|
  fobj := fun _ => 2%nat;
  fmap := fun _ _ f => two_map f
|}.
Next Obligation. now destruct f. Qed.

Section P392Binders.

Universes p392o p392h p392p.
Constraint Set < p392h.

(*
Control: the shipped, annotated constant elaborates at levels where
   [Omega]'s hom universe is declared strictly above [Set].

--------
控制：已发货的带注释常量在声明 [Omega] 的同类宇宙严格高于 [Set] 的级别处展开。
*)
Check (TwoFun : @Functor Omega@{p392o p392h p392p} FinSet).

(* Negative 1. / 负一。 *)
Fail Check (TwoFunUnann : @Functor Omega@{p392o p392h p392p} FinSet).

End P392Binders.

(** ** Negative 2 (FORMABILITY): the [Set] pin on the presheaf ambient / ** 负 2（可成形性）：预层环境上的 [Set] 引脚 *)

Section P392SetsPin.

Universes p392co p392so.
Constraint Set < p392co.
Constraint p392co < p392so.

(* Controls: both factors exist separately at these levels. / 控制：这两个因素在这些水平上分别存在。 *)
Check (Sets@{p392co p392so}).
Check (_2^op).

(*
Negative 2: but they cannot be assembled into a functor category,
   because [_2]'s homs are the literal [Set], [Fun] identifies its
   source and target hom universes, and [Sets]'s hom universe IS its
   carrier universe.

--------
负面 2：但是它们无法组装成函子范畴，因为 [_2] 的同态是字面上的 [Set]，[Fun] 将其源与目标同态范畴识别为相同，且 [Sets] 的同态范畴就是其承载范畴。
*)
Fail Check ([_2^op, Sets@{p392co p392so}]).

(*
Discriminating control: with the polymorphic [Omega] in place of
   [_2^op] the same [Sets] instance IS admissible, so [_2] is a
   NECESSARY donor.  This control varies only [_2], so it establishes
   nothing about [Fun], and [Fun] is in fact a SECOND necessary donor:
   measured out of tree and NOT pinned here, the bare functor TYPE
   [@Functor (_2^op) Sets] is formable at these very levels while the
   CATEGORY [[_2^op, Sets]] is not, so the two are co-necessary and
   neither alone suffices.  [Sets] is measured NOT to be a donor.

--------
鉴别控制：用多态的 [Omega] 代替 [_2^op] 时，相同的 [Sets] 实例是可允许的，因此 [_2] 是一个必要的供体。此控制仅变化 [_2]，因此它对 [Fun] 无任何建立作用，而 [Fun] 实际上是第二个必要的供体：在树外测量且未在此固定时，裸函子类型 [@Functor (_2^op) Sets] 可在这些层次上形成，而类别 [[_2^op, Sets] 则不可以，因此两者是共同必要的，且单独存在不足以支持。测量显示 [Sets] 并不是供体。
*)
Check ([Omega@{p392co p392co p392co}, Sets@{p392co p392so}]).

End P392SetsPin.

(** ** Negative 3 (CONVERSION): the two presheaves differ at [TwoY] / ** 负 3（转换）：这两个预层在 [TwoY] 处不同 *)

Fail Definition p392_n3
  : fobj[PresheafP] TwoY = fobj[PresheafQ] TwoY := eq_refl.

(**
** Negative 4 (CONVERSION): the objectwise candidate is not the
       two-element setoid

--------
** 负4（转换）：按对象候选的不是二元素集合化对象
*)

(*
The objectwise formula would read the exponential at [TwoY] as
   Q(TwoY)^{P(TwoY)}.  That object is computable in tree, and it is NOT
   [two_elt]; the target proves separately, at [~], that all of its
   points coincide, whereas the true value has two distinct ones.

--------
逐对象公式将在 [TwoY] 处读取指数为 Q(TwoY)^{P(TwoY)}。该对象在树中是可计算的，并且它不是 [two_elt]；目标在 [~] 处分别证明其所有点重合，而真实值有两个不同的点。
*)
Fail Definition p392_n4
  : @exponent_obj Sets Sets_Cartesian Sets_Closed
      (fobj[PresheafP] TwoY) (fobj[PresheafQ] TwoY) = two_elt := eq_refl.

(** ** Negative 5 (TYPING): the headline is about [Omega, FinSet] / ** 负5（打字中）：标题是关于[Omega, FinSet] *)

(*
Control: the headline accepts the pointwise cartesian structure on
   its own functor category.

--------
控制：这个标题在它自身函子范畴上接受逐点笛卡尔结构。
*)
Check (fun_not_cartesian_closed
         (Functor_Category_Cartesian Omega FinSet FinSet_Cartesian)).

(* Negative 5: and not one on a different functor category. / 负五：并且没有一个在不同的函子范畴上。 *)
Fail Check (fun_not_cartesian_closed
              (Functor_Category_Cartesian (_2^op) Sets Sets_Cartesian)).

(** ** Negative 6 (CONVERSION): [alpha_fam] separates at its stage / ** 负 6（转换）：[alpha_fam] 在其阶段分离 *)

Fail Definition p392_n6 : alpha_fam 0 1 = alpha_fam 1 1 := eq_refl.

(**
** Negative 7 (TYPING): the engine's second half is about the
       terminal object

--------
** 负7（打字中）：引擎的后半部分关于终端对象
*)

(* Control: the constant exists and is applicable at these arguments. / 控制：该常量存在并适用于这些参数。 *)
Check (@fun_const_point Omega FinSet Omega_Initial FinSet_Terminal).

(*
Negative 7: its argument must be a transformation OUT OF the
   pointwise terminal functor; an endotransformation of [TwoFun] is not
   one.

--------
负 7：它的参数必须是从逐点终端函子出的变换；[TwoFun] 的自变换不是这样的变换。
*)
Fail Check (@fun_const_point Omega FinSet Omega_Initial FinSet_Terminal
              TwoFun (Alpha 0)).
