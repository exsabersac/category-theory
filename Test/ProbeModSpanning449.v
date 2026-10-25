Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Universal.Element.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Construction.Elements.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.SpanningArrow.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Mod.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Product.
Require Import Category.Instance.Mod.Representable.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Instance.Mod.Quotient.Isomorphism.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Mod.Bimodule.
Require Import Category.Instance.Mod.Spanning.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

(**
* Probe for issue #449: spanning bilinear maps and the solution set
      for the tensor product (Mac Lane §V.7, book p. 128)

    The import list above is Instance/Mod/Spanning.v's own 25 requires,
    verbatim and in its order, plus that file itself; a shorter prefix
    is what makes a probe pass for no reason.

    DISCIPLINE.  Quoted refusals below have their generated universe
    names replaced by readable ones ([u_car] for the module carrier
    level, [u_obj] for the level [RModObject R] itself lives at, and so
    on): the generated names are file-name dependent and would not
    survive a rename.  Everything else in a quoted message is verbatim.
    Every negative is paired with a positive control naming the same
    library constants, the instrument was checked, and each negative was
    re-run alone with its guard stripped IN A COPY OF THIS WHOLE FILE so
    that the refusal kind could be read off the message rather than
    guessed -- a preamble-only scratch would drop the Section variables
    and misclassify the refusal.  The kinds recorded are UNIVERSE (two)
    and CONVERSION (one), beside the instrument check, whose refusal is a
    missing NAME.  The rubric is Test/ProbeModLimit449.v's:

      CONVERSION  - "cannot unify A and B" parenthetical present.
      TYPING      - the "has type X while it is expected to have type Y"
                    opener with NO such parenthetical.
      UNIVERSE    - "universe inconsistency".

    WHAT THE TWO UNIVERSE NEGATIVES PIN.  Instance/Mod/Spanning.v's
    [RMod_HasWidePullbacks] is a genuine wide pullback in [RMod R], but
    its class INDEX universe is instantiated at the module CARRIERS,
    strictly below the universe [RModObject R] itself lives at, because
    the apex is a submodule of Instance/Mod/Product.v's [ProdMod] and a
    dependent product over an index type forces that index at or below
    the carrier.  [spanning_solution_set] indexes its wide pullback by
    [FactoringFamily], a sigma over [SubObj a], which lives one level up.
    So the exported instance does not discharge the hypothesis, and the
    solution set of section 7 of that file stays a conditional over an
    abstract [HasWidePullbacks (RMod R)].  NEGATIVE 2 pins the refusal at
    the application and NEGATIVE 3 pins the donor one level down, at
    [ProdMod] itself.  Neither says the wall is unavoidable; both say it
    is there and where it comes from.

    WHAT THE CONVERSION NEGATIVE PINS.  The submodule round trip
    [subobj_smod (smod_subobj S)] is NOT [S] on the nose -- its
    membership is a sigma over the submodule's own carrier, so it is a
    different [Type] from [smod_mem S] -- and the header claims only
    inter-derivability, [smod_round_iff].  NEGATIVE 1 pins that the
    stronger [eq_refl] reading is not available.

--------
* 探讨问题 #449：跨双线性映射与张量积的解集（Mac Lane §V.7，书籍第128页）

上面的导入列表是 Instance/Mod/Spanning.v 自身的 25 个 requires，逐字且按其顺序，加上该文件本身；一个较短的前缀会无缘无故地让探测通过。

纪律。下面引用的拒绝信息中，生成的宇宙名称已被可读名称替换（[u_car] 表示模块承载级别，[u_obj] 表示 [RModObject R] 本身所在的级别，依此类推）：生成的名称依赖于文件名，重命名后将无法保留。引用消息中的其他内容均为逐字内容。每个负例都有一个配对的正例，用以命名相同的库常量，仪器已检查，并且每个负例都在剥离保护的整个文件副本中单独重新运行，以便可以从消息中读取拒绝类型，而不是猜测——仅使用前言的草稿会丢失 Section 变量并导致拒绝分类错误。记录的类型为 UNIVERSE（两个）和 CONVERSION（一个），此外还有仪器检查，其拒绝类型为缺失的 NAME。评定标准为 Test/ProbeModLimit449.v 的:

转换 - “无法统一 A 和 B”的括号出现。
类型 - “具有类型 X 而期望具有类型 Y”的开头，没有这样的括号。
宇宙 - “宇宙不一致”。

两个宇宙的负数固定。Instance/Mod/Spanning.v 中的 [RMod_HasWidePullbacks] 是 [RMod R] 中的一个真正的宽回撤，但它的类 INDEX 宇宙在模块 CARRIERS 中实例化，严格低于 [RModObject R] 所在的宇宙，因为顶点是 Instance/Mod/Product.v 中 [ProdMod] 的子模块，并且依赖索引类型的产品会强制该索引位于或低于承载体。[spanning_solution_set] 通过 [FactoringFamily] 对其宽回撤进行索引，[FactoringFamily] 是位于上一层的 [SubObj a] 的 sigma。因此，导出的实例未能解除假设，该文件第 7 节的解集仍然是对抽象 [HasWidePullbacks (RMod R)] 的条件。NEGATIVE 2 将拒绝固定在应用上，而 NEGATIVE 3 将捐赠者固定在下一层，即 [ProdMod] 本身。两者都未说明障碍不可避免；只是指出它存在以及它的来源。

转换负引脚是什么。子模块往返 [subobj_smod (smod_subobj S)] 并不是正对着的 [S] —— 它的成员是对子模块自身载体的求和，所以它是与 [smod_mem S] 不同的 [Type] —— 且头文件只声明了可互派生性 [smod_round_iff]。负 1 指出更强的 [eq_refl] 读数不可用。
*)

(** ** Instrument check / ** 仪表检查 *)

(*
A refusal expected around a name that is not there.  If the instrument
   were inert this line would pass silently and so would everything below
   it.  The message is "The reference
   zzz_no_such_constant_spanning_449 was not found in the current
   environment."

--------
预计会因为一个不存在的名字而被拒绝。如果该工具是惰性的，这一行会悄无声息地通过，下面的所有内容也会如此。消息是“在当前环境中未找到引用 zzz_no_such_constant_spanning_449。”
*)
Fail Check zzz_no_such_constant_spanning_449.

(** ** Positive controls: every library constant a negative names / ** 阳性对照：每个文库的常数一个阴性名称 *)

Section Controls.

Context {R : RingObject}.
Context (V V' : RModObject R).

Check (RMod R).
Check (Bilin V V').
Check (RMod_HasWidePullbacks R).
Check (RMod_WidePullback (R:=R)).
Check (Bilin_PreservesWidePullbacks V V').
Check SetsOne.
Check (@SolutionSet (RMod R) Sets (Bilin V V')).
Check (@SpanningArrowsOutOf (RMod R) Sets (Bilin V V') SetsOne).
Check (@spanning_solution_set (RMod R) Sets (Bilin V V')).
Check (@ProdMod R).
Check (@SubObj (RMod R)).
Check (@sub_mono (RMod R)).
Check (@sub_dom (RMod R)).
Check (@Submodule R).
Check (@smod_mem R).
Check (@smod_subobj R).
Check (@subobj_smod R).
Check (@smod_round_iff R).
Check (@smod_round_to R).
Check (@smod_round_from R).
Check (@SubGenMod R).
Check (@rbilinear_spanning_iff R).
Check (@tensor_gen_spanning_categorical R).

(*
The three [eq_refl] readbacks of the conditional solution set, as
   controls.  [HWP] is passed EXPLICITLY throughout this file: the
   exported instance [RMod_HasWidePullbacks] would be found by resolution
   and then refused at the application, which is NEGATIVE 2.

--------
条件解集的三个 [eq_refl] 回读作为控制。[HWP] 在整个文件中被明确传递：通过解析可以找到导出的实例 [RMod_HasWidePullbacks]，然后在应用程序中被拒绝，这是负 2。
*)
Example c_esol_index (HWP : @HasWidePullbacks (RMod R)) :
  esol_index (@tensor_esols R V V' HWP)
    = SpanningArrowsOutOf (Bilin V V') SetsOne := eq_refl.

Example c_esol_obj (HWP : @HasWidePullbacks (RMod R))
  (i : SpanningArrowsOutOf (Bilin V V') SetsOne) :
  esol_obj (@tensor_esols R V V' HWP) i = `1 i := eq_refl.

Example c_esol_elem (HWP : @HasWidePullbacks (RMod R))
  (i : SpanningArrowsOutOf (Bilin V V') SetsOne) :
  esol_elem (@tensor_esols R V V' HWP) i = `1 (`2 i) ttt := eq_refl.

(*
The two [eq_refl] readbacks of the submodule/subobject bridge that DO
   hold, as the controls NEGATIVE 1 sits beside.

--------
子模块/子对象桥的两个 [eq_refl] 回读确实有效，因为控制 NEGATIVE 1 位于旁边。
*)
Example c_subobj_dom (W : RModObject R) (S : Submodule W) :
  sub_dom (smod_subobj S) = SubmoduleMod S := eq_refl.

Example c_subobj_mono (W : RModObject R) (S : Submodule W) :
  sub_mono (smod_subobj S) = smod_incl S := eq_refl.

End Controls.

(**
** NEGATIVE 1 (CONVERSION): the submodule round trip is not [eq_refl]

    [subobj_smod (smod_subobj S)] has the same members as [S] but is not
    the same [Type]: its membership is a sigma over the submodule's own
    carrier paired with a proof that the inclusion carries it to [a].
    Stripped and re-run in a copy of the whole file, the message is

      The term "eq_refl" has type
       "smod_mem (subobj_smod (smod_subobj S)) a =
        smod_mem (subobj_smod (smod_subobj S)) a"
      while it is expected to have type
       "smod_mem (subobj_smod (smod_subobj S)) a = smod_mem S a"
      (cannot unify "smod_mem (subobj_smod (smod_subobj S)) a" and
       "smod_mem S a")

    The control is [smod_round_iff], the inter-derivability the header
    claims and the only strength available.

--------
** 负面 1（转换）：子模块往返不是 [eq_refl]

    [subobj_smod (smod_subobj S)] 与 [S] 的成员相同，但不是相同的 [Type]：它的成员是子模块自身载体上的一个 sigma，并附有一个证明，证明包含将其带到 [a]。
    在整个文件的副本中去掉并重新运行后，消息为

      术语 "eq_refl" 的类型是
       "smod_mem (subobj_smod (smod_subobj S)) a =
        smod_mem (subobj_smod (smod_subobj S)) a"
      而它预期的类型是
       "smod_mem (subobj_smod (smod_subobj S)) a = smod_mem S a"
      （无法统一 "smod_mem (subobj_smod (smod_subobj S)) a" 和
       "smod_mem S a"）

    控制是 [smod_round_iff]，标题所声称的可互导性以及唯一可用的强度。
*)

Section RoundTrip.

Context {R : RingObject}.
Context {W : RModObject R}.
Context (S : Submodule W).
Context (a : carrier (cmon_setoid W)).

Example c_round_iff : smod_mem (subobj_smod (smod_subobj S)) a
                        ↔ smod_mem S a := smod_round_iff S a.

Fail Example n1_round_trip_not_definitional :
  smod_mem (subobj_smod (smod_subobj S)) a = smod_mem S a := eq_refl.

End RoundTrip.

(**
** POSITIVE CONTROL for NEGATIVE 2: the same application under an
       ABSTRACT wide-pullback hypothesis IS accepted

    This is Instance/Mod/Spanning.v's [tensor_solution_set] written out.
    It elaborates, so NEGATIVE 2 below is about the exported instance's
    universes and not about [spanning_solution_set] being unusable at
    [RMod R].

--------
** 针对 NEGATIVE 2 的阳性对照：在抽象的广泛回退假设下，相同的应用是被接受的

这是 Instance/Mod/Spanning.v 中的 [tensor_solution_set] 的完整写出。它进行了说明，因此下面的 NEGATIVE 2 是关于导出实例的宇宙，而不是关于 [spanning_solution_set] 在 [RMod R] 不可用。
*)

Section AbstractHWP.

Context {R : RingObject}.
Context (V V' : RModObject R).
Context (HWP : @HasWidePullbacks (RMod R)).

Example c_solution_set_with_hypothesis :
  SolutionSet (Bilin V V') SetsOne :=
  @spanning_solution_set (RMod R) Sets (Bilin V V') HWP
    (Bilin_PreservesWidePullbacks V V') SetsOne.

End AbstractHWP.

(**
** NEGATIVE 2 (UNIVERSE): the exported wide-pullback instance does not
       discharge [spanning_solution_set]'s hypothesis

    Stripped and re-run in a copy of the whole file, the message is

      The term "RMod_HasWidePullbacks R" has type
       "HasWidePullbacks@{u_car u_car u_obj u_car}
          (RMod@{u_obj ...} R)"
      while it is expected to have type
       "HasWidePullbacks@{u_idx u_idx' u_obj' u_car}
          (RMod@{u_obj' ...} R)"
      (universe inconsistency: Cannot enforce u_car = u_idx because
       u_car < u1 <= u2 <= u_idx)

    -- the instance's index slot is the module CARRIER universe, while
    the application wants the universe [SubObj] lives at, one level up;
    the chain is three steps.  The positive control immediately above
    passes [HWP] abstractly and IS accepted.

--------
** 负面 2（宇宙）：导出的宽回退实例无法满足 [spanning_solution_set] 的假设

在整个文件的副本中剥离并重新运行，消息为：

“RMod_HasWidePullbacks R” 的类型是
"HasWidePullbacks@{u_car u_car u_obj u_car} 
   (RMod@{u_obj ...} R)"
而它预期的类型是
"HasWidePullbacks@{u_idx u_idx' u_obj' u_car} 
   (RMod@{u_obj' ...} R)"
（宇宙不一致：无法强制 u_car = u_idx，因为 u_car < u1 <= u2 <= u_idx）

——该实例的索引槽属于模块 CARRIER 的宇宙，而应用程序希望 [SubObj] 所在的宇宙在上一级；
链条为三步。正面控制正好在上方抽象地传递 [HWP]，并被接受。
*)

Section SolutionSetRefused.

Context {R : RingObject}.
Context (V V' : RModObject R).

Fail Definition n2_exported_instance_refused :
  SolutionSet (Bilin V V') SetsOne :=
  @spanning_solution_set (RMod R) Sets (Bilin V V')
    (RMod_HasWidePullbacks R) (Bilin_PreservesWidePullbacks V V') SetsOne.

End SolutionSetRefused.

(**
** NEGATIVE 3 (UNIVERSE): the donor, one level down

    The obstruction is not the class's and not [Submodule]'s: it is
    [ProdMod]'s, whose carrier is the dependent function space
    [∀ i : I, carrier (cmon_setoid (A i))], so the index universe is at
    or below the carrier universe, while an object of [RMod R] has its
    carrier strictly below the object universe.  Indexing a [ProdMod] by
    the subobjects of a module is therefore already refused, with no
    solution set in sight.  Stripped and re-run in a copy of the whole
    file, the message is

      The term "ProdMod A" has type "RModObject R"
      while it is expected to have type "obj[RMod R]"
      (universe inconsistency: Cannot enforce u_prod = u_car because
       u_car < u1 <= u2 <= u3 <= u_prod)

    a four-step chain from the module carrier level up to the product's.
    The control is the same [ProdMod] indexed by a bare [Type], which is
    accepted.

--------
** 负3（宇宙）：捐赠者，下一级

阻碍不是类的，也不是 [Submodule] 的：它是 [ProdMod] 的，其承载者是依赖函数空间 [∀ i : I, carrier (cmon_setoid (A i))]，因此索引的宇宙位于或低于承载者宇宙，而 [RMod R] 的对象的承载者严格低于对象宇宙。因此，通过模块的子对象对 [ProdMod] 进行索引已经被拒绝，且没有可见的解决方案。在整个文件的副本中去掉并重新运行，消息是

术语 "ProdMod A" 的类型是 "RModObject R"
      而预期类型是 "obj[RMod R]"
      （宇宙不一致：无法强制 u_prod = u_car，因为
       u_car < u1 <= u2 <= u3 <= u_prod）

从模块载体级别到产品级别的四步链。控制使用相同的 [ProdMod]，由一个裸的 [Type] 索引，这是被接受的。
*)

Section ProdModDonor.

Context {R : RingObject}.

Example c_prodmod_at_a_type (I : Type) (A : I → obj[RMod R]) :
  obj[RMod R] := @ProdMod R I A.

Fail Definition n3_prodmod_at_subobj (W : obj[RMod R])
  (A : @SubObj (RMod R) W → obj[RMod R]) : obj[RMod R] :=
  @ProdMod R (@SubObj (RMod R) W) A.

End ProdModDonor.
