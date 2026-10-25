(**
* Boundary probes for Instance/Sets/Pullback.v (issue #333)

    Mac Lane CWM 2nd ed. §III.4 Exercises 1 and 6, book p. 72; Awodey §5.2;
    Riehl §3.2 Example 3.2.9.

    This file exists mainly to pin ONE measurement the target CANNOT pin
    itself.  The target's central design decision -- build the pullback
    DIRECTLY rather than read it off issue #326's
    [HasPullbacks_of_Cartesian_HasEqualizers] -- rests on the claim that
    the DERIVED apex is not the agreement pair-set.  Stating that claim
    requires [Adjunction/GAFT/Sets.v] (for [Sets_HasEqualizers]), and
    requiring it from the target would put the whole GAFT closure behind
    every consumer of [Sets] pullbacks.  A probe pays that cost once, for
    nobody downstream.  That is what Negative 1 is.

    THERE ARE NOW FOUR NEGATIVES, of TWO kinds.  An earlier revision
    shipped only two, both CONVERSION, and justified that by saying "there
    is no formability boundary to pin".  The formability half of that is
    true and stays true -- [Sets_HasPullbacks@{u u0}] carries only [Sets]'
    own [u0 < u], with no identification and no [Set] -- but it was the
    wrong conclusion to draw: a TYPING-kind negative was one line away and
    is now Negative 4.  An earlier revision also left the target's FIRST
    refutation ([exl ∘ sets_pb_pair] against [sets_pb_fst]) pinned
    NOWHERE while the header called it measured; it is now Negative 3.

    The three CONVERSION negatives differ in CAUSE, not kind:

      * Negative 1 -- the derived apex reduces to the compatible-family
        setoid over the walking parallel pair, so an element is a
        dependent function plus a constraint quantified over every arrow
        of [Parallel], NOT a pair.  Stripped, the error is
          cannot unify "DerObj" and "sets_pb_obj f g".
        The derivation is TRANSPARENT, not opaque -- it reduces, just to
        the wrong description -- which is why the target could not simply
        take it and then state the kernel-pair, preimage and equalizer
        identifications on top.

      * Negative 2 -- the pairing does not round-trip strictly, because
        stdlib [prod] has no definitional eta.  Nothing about [Sets].

    Every negative is paired with a positive control NAMING ITS OWN
    CONSTANTS.  The measured rename-simulation score is at the end, over
    the constants the NEGATIVES name and no others.

--------
* Instance/Sets/Pullback.v 的边界探针（问题 #333）

Mac Lane《CWM》第2版 §III.4 练习题 1 和 6，书第72页；Awodey §5.2；Riehl §3.2 例 3.2.9。

这个文件的存在主要是为了固定一个目标自身无法固定的测量。目标的核心设计决策——直接构建回拉，而不是从问题 #326 的 [HasPullbacks_of_Cartesian_HasEqualizers] 中读取——依赖于这样的主张：派生的顶点并不是协议对集。陈述这一主张需要 [Adjunction/GAFT/Sets.v]（用于 [Sets_HasEqualizers]），而如果要求目标提供它，会让整个 GAFT 闭包在每个 [Sets] 回拉的使用者面前都变得复杂。一项探测只需承担一次这个成本，而下游没有人需要承担。这就是负一的含义。

现在有四个负面情况，分为两种类型。之前的一个修订版本只包含两个，都是CONVERSION类型，并且为此辩解说“没有可成形性边界可钉”。其中关于可成形性的一半是正确的并且仍然正确——[Sets_HasPullbacks@{u u0}] 仅携带 [Sets] 自己的 [u0 < u]，没有标识也没有 [Set]——但是这是错误的结论：一种 TYPING 类型的负面情况就在一行之外，现在是负面 4。之前的一个修订版本还留下了目标的第一次驳斥（[exl ∘ sets_pb_pair] 针对 [sets_pb_fst]）完全未固定，而标题却称其已被测量；现在它是负面 3。

这三种转换否定在原因上不同，而不是种类上不同：

* 负 1 -- 推导出的顶点简化为在行走平行对上的兼容族集合，因此一个元素是一个依赖函数加上一个约束，在每个 [Parallel] 的箭头上量化，而不是一个对。剥离后，错误为：
  无法统一 “DerObj” 和 “sets_pb_obj f g”。
推导是透明的，而非不透明——它可以简化，只是简化成了错误的描述——这就是为什么目标不能简单地接收它然后在其上声明核对、原像和平衡器的识别。

* 负 2 -- 配对不能严格地来回转换，因为 stdlib [prod] 没有定义的 eta。关于 [Sets] 没有任何信息。

每个阴性都与一个阳性对照配对，并命名其自身的常数。测量的重命名模拟分数在最后，作用于阴性命名的常数，而不作用于其他常数。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Regular.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Adjunction.GAFT.Sets.
Require Import Category.Instance.Sets.Pullback.

(**
** Instrument check

    A [Fail] that never fails would make every negative below vacuous.

--------
** 仪器检查

    一个永不失败的 [Fail] 会使下面的每个负面都变得无效。
*)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(**
** Negative 1 (CONVERSION): the #326 derivation gives the WRONG apex

    This is the target's design decision, made checkable.

--------
** 负 1（转换）：#326 推导给出了错误的顶点

这是目标的设计决策，可进行检查。
*)

Section DerivationRoute.

Context (x y z : Sets) (f : x ~> z) (g : y ~> z).

Definition Derived : HasPullbacks Sets :=
  @HasPullbacks_of_Cartesian_HasEqualizers Sets _ Sets_HasEqualizers.

Definition DerObj := Pull f g (@pullback Sets Derived _ _ _ f g).

Fail Definition probe_derived_is_pair :
  DerObj = sets_pb_obj f g := eq_refl.

(*
Positive controls naming the negative's own constants.  The derivation
   IS formable -- it is the DESCRIPTION that differs, not the term's
   existence -- and the directly-built apex is independently well-formed.

--------
正向控制命名负向自身的常数。导出是可形成的——区别在于描述，而不是术语的存在——直接构建的顶点是独立良构的。
*)
Check Derived.
Check DerObj.
Check (sets_pb_obj f g).
Check (@HasPullbacks_of_Cartesian_HasEqualizers Sets).
Check Sets_HasEqualizers.
Check (@pullback Sets Derived _ _ _ f g).

End DerivationRoute.

(** ** Negative 2 (CONVERSION, different cause): prod has no eta / ** 负2（转换，不同原因）：生产没有预计时间 *)

Section PairEta.

Context (x y z : Sets) (f : x ~> z) (g : y ~> z) (u : sets_pb_obj f g).

Fail Definition probe_pair_eta :
  sets_pb_pair f g u = `1 u := eq_refl.

(*
Positive controls.  The pairing exists and the projections DO compute;
   only the surjective-pairing step is missing.

--------
阳性对照。配对存在，并且投影确实可以计算；只有满射配对步骤缺失。
*)
Check (sets_pb_pair f g u).
Check (sets_pb_fst f g).
Check (sets_pb_snd f g).

End PairEta.

(**
** Negative 3 (CONVERSION): the equalizer round trip, as MORPHISMS

    The target's header records this and an earlier revision of this probe
    pinned it nowhere.  The two [SetoidMorphism] records agree on their
    underlying functions -- that is the POINTWISE [eq_refl] the target
    ships -- and differ in the rebuilt [proper_morphism] certificate.

--------
** 负3（转换）：均衡器往返，如同态

目标的头记录了这一点，以及该探针的早期修订版
未固定在任何位置。两个[SetoidMorphism]记录在其
底层功能上是一致的——也就是目标
提供的逐点[eq_refl]——并且在重建的[proper_morphism]证书中有所不同。
*)

Section RoundTripMorphism.

Context (x y z : Sets) (f : x ~> z) (g : y ~> z).

Fail Definition probe_round_fst :
  exl ∘ sets_pb_pair f g = sets_pb_fst f g := eq_refl.

(*
Positive controls: the POINTWISE forms ARE proved in the target, and
   every constant in the rejected equation is well-formed here.

--------
阳性对照：在目标中证明了 POINTWISE 形式，并且被拒绝方程中的每个常数在这里都是良构的。
*)
Check sets_equalizer_round_fst_pointwise.
Check (sets_pb_pair f g).
Check (sets_pb_fst f g).
Check (@exl Sets _ x y).

End RoundTripMorphism.

(**
** Negative 4 (TYPING): the bundled Pullback record is not applicable

    A DIFFERENT KIND from 1-3.  [Pullback f g] is a [Type] carrying its
    apex as DATA, so it cannot be applied to an apex and two legs the way
    the apex-pinned [IsPullback] can.  Stripped, the error is
    "Illegal application (Non-functional construction)".  This is a DONOR
    fact -- Theory/Morphisms/CokernelPair.v already pins the pushout dual
    -- and is repeated here only so this file carries two kinds.

--------
** 负 4（打字）：捆绑的回撤记录不适用

    与 1-3 不同。[Pullback f g] 是携带其顶点作为数据的 [Type]，因此它不能像顶点固定的 [IsPullback] 那样应用于一个顶点和两条边。剥离后，错误信息为“非法应用（非功能性构造）”。这是一个捐赠者事实——Theory/Morphisms/CokernelPair.v 已经固定了推出的对偶——这里重复只是为了使该文件包含两种类型。
*)

Section BundledNotApplicable.

Context (x y z : Sets) (f : x ~> z) (g : y ~> z).

Fail Check (Pullback f g (sets_pb_obj f g)
              (sets_pb_fst f g) (sets_pb_snd f g)).

(*
Positive controls: the BUNDLED form takes only the cospan, and the
   APEX-PINNED form is the one that takes apex and legs.

--------
阳性对照：捆绑形式只采用顶盖，而APEX-PINNED形式则采用顶点和支腿。
*)
Check (Pullback f g).
Check Sets_Pullback.
Check Sets_IsPullback.
Check (@IsPullback Sets).

End BundledNotApplicable.

(** ** Controls for the delivered results / ** 已交付结果的控制 *)

Check Sets_HasPullbacks.
Check Sets_Pullback.
Check Sets_IsPullback.
Check sets_pb_med.
Check sets_ker.
Check sets_ker_fst.
Check sets_ker_snd.
Check sets_kernel_pair_obj.
Check sets_kernel_pair_fst.
Check sets_kernel_pair_snd.
Check sets_ker_refl.
Check sets_ker_sym.
Check sets_ker_trans.
Check sets_pullback_is_equalizer.
Check sets_equalizer_is_pullback.
Check SubsetOf.
Check sub_obj.
Check sub_incl.
Check sub_incl_Monic.
Check sets_preimage.
Check sets_preimage_IsPullback.
Check sets_preimage_criterion.

(** ** Non-vacuity controls / ** 非空性控制 *)

Check even_ker_not_diagonal.
Check even_med_is_ump.
Check constThree_does_not_factor.

(**
** MEASURED RENAME-SIMULATION SCORE

    The constants the NEGATIVES name:

      Negative 1: [HasPullbacks_of_Cartesian_HasEqualizers],
                  [Sets_HasEqualizers], [Pull], [pullback], [sets_pb_obj]
      Negative 2: [sets_pb_pair]
      Negative 3: [exl], [sets_pb_fst]
      Negative 4: [Pullback], [sets_pb_snd]

    That is TEN, and the denominator is not padded with control-only
    names.  All ten are named by a positive control above, so renaming any
    one breaks this file rather than turning its negative vacuously green.
    Score: 10/10, counted rather than recalled.

--------
** 测量重命名模拟得分

    负面名称的常量：

      负面 1：[HasPullbacks_of_Cartesian_HasEqualizers]，
                  [Sets_HasEqualizers], [Pull], [pullback], [sets_pb_obj]
      负面 2：[sets_pb_pair]
      负面 3：[exl], [sets_pb_fst]
      负面 4：[Pullback], [sets_pb_snd]

    总共有十个，分母没有用仅控制名称填充。十个名称都由上述阳性控制命名，因此重命名其中任何一个都会破坏此文件，而不是让其负面结果形式上变为绿色。
    得分：10/10，按计数而非回忆。
*)
