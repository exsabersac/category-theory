Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Span.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Limit.
Require Import Category.Structure.Pushout.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Morphisms.CokernelPair.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Adjunction.Diagonal.Finite.

Generalizable All Variables.

(**
* Probe: the boundaries Adjunction/Diagonal/Finite.v measures

   That file records its rejections and carries no [Fail] of its own. A
   measurement is not a guard. This file pins them beside controls that
   must SUCCEED.

   The import list is the target's own, in its order, with the target
   appended. A probe on a shorter prefix can fail for a missing-reference
   reason and read as a mathematical rejection.

   TWO PROBE HAZARDS THIS FILE WAS WRITTEN AROUND, both of which cost a
   FALSE PASS when first attempted and are recorded here so the next
   reader does not repeat them:

   (1) A [Fail] that succeeds PRINTS NOTHING under this repo's [coqc]. You
       cannot read a negative's reason from the compile log; every one must
       be stripped and run on its own. That is how each was classified.

   (2) **[Roof^op = Roof] IS A FALSE PASS.** `Functor/Opposite.v` opens
       `functor_scope`, and inside an [eq] argument there is no expected
       type for the category scope to win on, so `^op` parses as the
       FUNCTOR opposite and the command fails with
       "The term "Roof" has type "Category" while it is expected to have
       type "?C ⟶ ?D"" — NOTATION, not mathematics. Written that
       way the negative certifies nothing. Both are therefore spelled
       [Opposite Roof] and [Opposite Parallel] below. (Measured: the
       `^op` spelling really does fail with that message.)

   KINDS, separated by the error TEXT:
     CONVERSION  ends `(cannot unify "X" and "Y")`
     TYPING      reports a type mismatch with no `cannot unify` clause
     FORMABILITY ends `(universe inconsistency: Cannot enforce ...)`

--------
* 探针：边界 附加/对角/有限.v 测量

该文件记录其拒绝，并且没有自己的 [Fail]。测量不是保护。该文件将它们固定在必须成功的控制旁边。

导入列表是目标自身的，按其顺序排列，并附加目标。对较短前缀的探查可能因缺少引用而失败，并被视为数学上的拒绝。

这个文件是围绕两个探针危险编写的，这两个危险在首次尝试时都会导致一个错误通过，并在此记录，以便下一个读者不重复它们：

(1) 一个在此仓库的 [coqc] 下成功的 [Fail] 什么都不打印。你无法从编译日志中读取一个否定的原因；每一个都必须被剥离并单独运行。这就是每一个被分类的方式。

(2) **[Roof^op = Roof] 是一个错误的通过。** `Functor/Opposite.v` 打开 `functor_scope`，在 [eq] 参数内部没有期望类型供类别作用域获胜，因此 `^op` 被解析为 FUNCTOR 的对立操作，并且该命令失败，报错信息为 “术语 'Roof' 的类型为 'Category'，但预期类型为 '?C ⟶ ?D'” —— 是符号问题，而不是数学问题。以这种方式书写并不能证明负面结论。因此下面两个均被写作 [Opposite Roof] 和 [Opposite Parallel]。（测量结果：`^op` 这种写法确实会报出该消息失败。）

类型，按错误文本分开：
     转换 以 `(cannot unify "X" and "Y")` 结束
     类型 检查报告类型不匹配但没有 `cannot unify` 条款
     可形成性 以 `(universe inconsistency: Cannot enforce ...)` 结束
*)

(** ** Instrument check — must ERROR ("The command has not failed!"). / ** 仪器检查 — 必须错误（“命令没有失败！”）。 *)
Fail Fail Check Category.

(**
** CONVERSION — the four elementary arrows are the adjunction's
    unit/counit components only up to a residual identity.

    Each control is the SAME statement with the residue restored, which is
    what locates the difference at a `∘ id` (limit side) or `id ∘`
    (colimit side) rather than at the leg.

--------
** 转换——这四个基本箭头仅仅是伴随的单位/余单位分量，带有剩余的恒等映射。

每个控制都是相同的语句，只是恢复了剩余部分，这就是为何差异位于 `∘ id`（极限侧）或 `id ∘`（余极限侧），而不是位于腿上。
*)

Section FiniteConversion.
Context {C : Category} (L : HasLimitsOfShape Parallel C).
Context (M : HasColimitsOfShape Parallel C).

(* NEGATIVE 1 — the equalizing arrow. / 负1 — 平衡之箭。 *)
Fail Definition probe_eq_arrow (F : Parallel ⟶ C) :
  eq_arrow L F = lim_leg L F ParX := eq_refl.

(* CONTROL 1. *)
Definition probe_eq_arrow_id (F : Parallel ⟶ C) :
  eq_arrow L F = lim_leg L F ParX ∘ id := eq_refl.

(* NEGATIVE 2 — the coequalizing arrow, dual residue. / 负二 — 平等化箭头，双重残留。 *)
Fail Definition probe_coeq_arrow (F : Parallel ⟶ C) :
  coeq_arrow M F = colim_inj M F ParY := eq_refl.

(*
CONTROL 2 — note the residue is on the OTHER side, which is the
   handedness the colimit rows carry throughout.

--------
控制 2 — 注意残留物在另一侧，这就是 colimit 行始终保持的手性。
*)
Definition probe_coeq_arrow_id (F : Parallel ⟶ C) :
  coeq_arrow M F = id ∘ colim_inj M F ParY := eq_refl.

End FiniteConversion.

Section FiniteConversionRoof.
Context {C : Category} (P : HasLimitsOfShape (Opposite Roof) C).
Context (Q : HasColimitsOfShape Roof C).

(* NEGATIVE 3 — the pullback's first projection. / 负3 — 回调的第一个预测。 *)
Fail Definition probe_pb_fst (F : Opposite Roof ⟶ C) :
  pb_fst P F = lim_leg P F RNeg := eq_refl.

(* CONTROL 3. *)
Definition probe_pb_fst_id (F : Opposite Roof ⟶ C) :
  pb_fst P F = lim_leg P F RNeg ∘ id := eq_refl.

(* NEGATIVE 4 — the pushout's first injection. / 阴性 4 — 推出物的第一次注射。 *)
Fail Definition probe_po_in1 (F : Roof ⟶ C) :
  pushout_inj1 Q F = colim_inj Q F RNeg := eq_refl.

(* CONTROL 4. *)
Definition probe_po_in1_id (F : Roof ⟶ C) :
  pushout_inj1 Q F = id ∘ colim_inj Q F RNeg := eq_refl.

End FiniteConversionRoof.

(**
** TYPING — "the unit is the identity" is not merely false, it does not
    typecheck, and that is the sharper statement.

    For `Δ ⊣ lim` the unit at x is `x ~> lim (Δ[J](x))`: a morphism between
    two DIFFERENT objects. So the exercise's "unit the identity" cannot be
    read literally. What the target delivers instead is invertibility under
    a sufficient connectedness condition on the shape.

--------
** 打字 —— “单位是恒等式”不仅仅是错误的，它无法通过类型检查，这才是更尖锐的说法。

对于 `Δ ⊣ lim`，x 处的单位是 `x ~> lim (Δ[J](x))`：这是两个不同对象之间的态射。因此，练习中所说的“单位是恒等式”不能字面理解。目标所传达的意思是，在形状满足足够连通性条件下，单位具有可逆性。
*)

Section UnitTyping.
Context {C : Category} (L : HasLimitsOfShape Parallel C) (x : C).

(*
NEGATIVE 5. Stripped, this reports a TYPE MISMATCH with NO `cannot
   unify` clause and no universe clause:
     The term "id" has type "x ~> x" while it is expected to have type
     "x ~> lim_obj L (fobj[Diagonal Parallel] x)".

--------
负面 5. 去掉后，这报告了一个类型不匹配，没有 `cannot unify` 条款，也没有宇宙条款：
    术语 "id" 的类型是 "x ~> x"，而预期的类型是 "x ~> lim_obj L (fobj[Diagonal Parallel] x)"。
*)
Fail Definition probe_unit_is_id : dia_unit L x = id[x] := eq_refl.

(*
CONTROL 5: the unit IS nameable and well-typed at its real type, so the
   negative is about the identity, not about `dia_unit`.

--------
控制 5：该单元可以命名，并且在其真实类型下类型良好，所以否定是关于身份的，而不是关于 `dia_unit` 的。
*)
Check (dia_unit L x).

End UnitTyping.

(**
** CONVERSION — neither walking shape is its own opposite

    This is why the pushout row is CONSTRUCTED rather than read off the
    pullback row, and why `Δ[Roof^op]` appears on the pullback side. Both
    are spelled with `Opposite` by name; see hazard (2) above.

--------
** 转换 — 两种行走形态都不是它自身的对立面

    这就是为什么推出行是构建的而不是从拉回行读取的，以及为什么 `Δ[Roof^op]` 出现在拉回侧。两者在名称上都用了 `Opposite`；参见上文的危险（2）。
*)

(* NEGATIVE 6. / 负 6。 *)
Fail Definition probe_roof_op : Opposite Roof = Roof := eq_refl.

(* NEGATIVE 7. / 负七。 *)
Fail Definition probe_parallel_op : Opposite Parallel = Parallel := eq_refl.

(* CONTROLS: both shapes are nameable and `Opposite` applies to each. / CONTROLS: both shapes are nameable and `Opposite` applies to each. / 控制：两种形状都可以命名，并且“相反”适用于每一种。 *)
Check Roof.
Check Parallel.
Check (Opposite Roof).
Check (Opposite Parallel).

(**
** FORMABILITY — hom and proof are identified, and the CONE RECORD IS
    NOT THE CAUSE.

    The target measures nine donors each rejected ALONE at these levels,
    and all nine are pinned below, together with the discriminating
    control: `Cone` is ACCEPTED at the very levels where every one of the
    nine is rejected, so "the cone vocabulary" would be the wrong
    attribution.

    Read "nine" as nine DONORS, not nine independent causes:
    `HasLimitsOfShape` is defined as `∀ F, Limit F`, so it cannot be
    rejected for a reason of its own, and no claim of independence is
    made for it.  The control has to be APPLIED to discriminate --
    `Check @Cone.` alone succeeds, but so does `Check @Limit.`, a
    polymorphic constant with no argument never meeting `Cu`; it is
    `@Cone Parallel Cu` against `@Limit Parallel Cu` that separates.

--------
** 可成形性——hom 和 proof 已被识别，且 CONE 记录 **不是原因**。

目标测量了在这些水平上单独被拒绝的九个捐赠者，所有九个都如图所示固定，同时附有区分用的控制：`Cone` 在每一个九个捐赠者都被拒绝的那些水平上被接受，因此“圆锥词汇”将是错误的归因。

将“九”理解为九个捐赠者，而不是九个独立的原因：`HasLimitsOfShape` 被定义为 `∀ F, Limit F`，所以它不能因自身原因而被拒绝，也没有任何独立性的声明。必须应用控制以进行区分——仅 `Check @Cone.` 就能成功，但 `Check @Limit.` 也能成功，它是一个多态常量，没有参数从未满足 `Cu`；正是 `@Cone Parallel Cu` 与 `@Limit Parallel Cu` 的对比才将两者区分开。
*)

Section FormabilityHomProof.
Universes uo uh up.
Constraint uh < up.
Context (Cu : Category@{uo uh up}).

(* CONTROLS accepted with hom and proof declared strictly apart. / 控制在 hom 和证明严格分开时被接受。 *)
Check (fun x y : Cu => x ~{Cu}~> y).
Check (obj[Cu]).
Check (fun x : Cu => id[x]).

(* THE DISCRIMINATING CONTROL: the cone RECORD is formable here. / 区分控制：锥形记录在这里是可形成的。 *)
Check (@Cone Parallel Cu).

(*
NEGATIVES 8-16, each rejected on its own.  Each was stripped and run
   alone, and each reports exactly

       (universe inconsistency: Cannot enforce up = uh because uh < up)

   so all nine are FORMABILITY and none is a conversion failure in
   disguise.  Nine donors, not four: an earlier revision of this file
   measured all nine in the target's header but pinned only the first
   four, which by this file's own rule ("a measurement is not a guard")
   left five unguarded.  They are pinned here.

--------
NEGATIVES 8-16，每个都单独被拒绝。每个都被剥离并单独运行，每个都报告完全相同的结果

       (宇宙不一致：无法强制 up = uh 因为 uh < up)

所以所有九个都是可形成性问题，而没有一个是伪装的转换失败。九个提供者，而不是四个：此文件的早期修订在目标的头部测量了所有九个，但只固定了前四个，根据此文件自己的规则（“测量不是保护”）留下了五个未被保护的。它们在这里被固定。
*)
Fail Check (@Limit Parallel Cu).
Fail Check (Opposite Cu).
Fail Check (@IsEqualizer Cu).
Fail Check (@IsPullback Cu).
Fail Check (@HasLimitsOfShape Parallel Cu).
Fail Check (@Diagonal Cu Parallel).
Fail Check ([Parallel, Cu]).
Fail Check (@IsCoequalizer Cu).
Fail Check (@IsPushoutSquare Cu).

End FormabilityHomProof.

(**
** Controls naming every constant the negatives depend on, OUTSIDE a
    [Fail], so a rename breaks a succeeding command rather than turning a
    negative vacuously green.

--------
** 控制命名每个负值依赖的常量，在 [Fail] 之外，因此重命名会破坏随后的命令，而不是使负值变为虚假的绿色。
*)

Check @eq_arrow.
Check @coeq_arrow.
Check @pb_fst.
Check @pb_snd.
Check @pushout_inj1.
Check @pushout_inj2.
Check @dia_unit.
Check @dia_counit.
Check @lim_leg.
Check @colim_inj.
Check @HasLimitsOfShape.
Check @HasColimitsOfShape.
Check @Limit.
Check @IsEqualizer.
Check @IsCoequalizer.
Check @IsPullback.
Check @IsPushoutSquare.
Check @Opposite.

Check @EqualizerFunctor.
Check @CoequalizerFunctor.
Check @PullbackFunctor.
Check @PushoutFunctor.
Check @Diagonal_Equalizer_Adjunction.
Check @Coequalizer_Diagonal_Adjunction.
Check @Diagonal_Pullback_Adjunction.
Check @Pushout_Diagonal_Adjunction.
Check @eq_counit_IsEqualizer.
Check @coeq_unit_IsCoequalizer.
Check @pb_counit_IsPullback.
Check @po_unit_IsPushoutSquare.
Check @ShapeLinked.
Check @dia_unit_iso.
Check @dia_counit_iso.
Check @Parallel_linked.
Check @Roof_linked.
