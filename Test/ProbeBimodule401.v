Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Adjunction.Parameter.
Require Import Category.Adjunction.Additive.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Continuity.
Require Import Category.Adjunction.Right.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Structure.AbCategory.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Mod.Bimodule.

Generalizable All Variables.

(** * Probe for Instance/Mod/Bimodule.v / * 探测实例/模块/双模块.v *)

(*
Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.8
   Exercise 3, book p. 104; catalog id maclane:IV.8:ex3.  The page is
   quoted verbatim in the header of Instance/Mod/Bimodule.v and is not
   repeated here.

   This file guards the strict claims of that header.  Every command
   below that is said to be refuted was STRIPPED into its own scratch
   copy carrying this file's whole prefix, compiled ALONE, and its
   complete error read; under this repo's coqc a passing [Fail] prints
   nothing, so a whole-file rc=0 alone would establish only THAT each
   command does not typecheck and never WHY.  Each negative is
   classified by the error TEXT, not by expectation:

     CONVERSION  - the message carries a "cannot unify A and B" clause
                   and no universe clause.
     TYPING      - a plain "The term T has type X while it is expected
                   to have type Y"; NO "cannot unify", no universe
                   clause.
     FORMABILITY - "(universe inconsistency: Cannot enforce ...)",
                   naming the levels the enclosing section declares.

   ** TALLY

   18 [Fail] commands = 1 instrument check + 17 negatives, in three
   kinds: SIX conversion (N1, N2, N10, N11, N16, N17), NINE typing
   (N3-N9, N12, N13) and TWO formability (N14, N15).

   ** TWO NEGATIVES MEASURE THEIR ARGUMENT AND NOT THEIR SUBJECT

   N15 names [hom_ab], and its first argument is an [AbEnriched Cu],
   which N14 has just shown is itself unformable at the declared
   levels; stripped, its error is N14's but for the line-derived level
   names, and fires on [Cu].  So [hom_ab] CANNOT be tested apart from
   [AbEnriched], and whether it identifies anything of its own is
   UNKNOWN, not refuted.  N9 is in the same position with respect to
   [Build_Bimodule]: stripped, its error fires on [M], the argument,
   and is character for character N8's, so what it establishes is
   that
   a right R-module cannot be the [bm_left] of a (ℤ,R)-bimodule — which
   is the claim — and NOT anything about [Build_Bimodule] itself.  This
   is the trap recorded for [MonoidObject] under issue #340, and it is
   stated here rather than glossed.

   ** GUARD COVERAGE, MEASURED MECHANICALLY

   Comments stripped and the file split into commands at a period
   followed by whitespace: 191 commands, of which 18 begin with [Fail];
   they mention 50 distinct identifiers, of which 40 also occur in a
   command that is NOT a [Fail].  The ten that do not are,
   exhaustively: the keyword [Fail]; [AC], bound inside N15 itself; the
   seven names of the refuted declarations ([p401_n1], [p401_n2],
   [p401_n7], [p401_n10], [p401_n11], [p401_n16], [p401_n17]), which
   never enter the environment because the commands that would have
   declared them do not typecheck; and [p401_no_such_constant_anywhere],
   the instrument's deliberately absent name.  No CONSTANT that a negative
   names is unguarded.

   ** RENAME SIMULATION

   Five constants of Instance/Mod/Bimodule.v are named inside a
   negative: [TensorWith], [HomS], [BimodTensorBimod], [RTensor] and
   [btb_left].  Each was renamed in a SCRATCH COPY of that file alone
   (the copy still compiling, zero errors) and a copy of this file
   requiring the scratch module instead was compiled.  ALL FIVE broke
   it, every one at a [Check] line of the guard block and NONE inside a
   [Fail]: [TensorWith], [HomS], [BimodTensorBimod], [RTensor] and
   [btb_left], each at its own [Check] guard.  So 5/5, with zero vacuous
   guards.

   ** THE HAZARD OF STAGE 1's FINDING 8, AND WHY IT IS BOTH

   [@TensorMod (Ring_op R) N (bimodule_right_RMod F)] TYPECHECKS for
   [F : Bimodule S R] — that is the control [p401_hazard_accepted] — and
   is the tensor of two RIGHT R-modules, balancing (n ⊲ r) ⊗ e against
   n ⊗ (e ⊲ r).  It is therefore NOT the object Exercise 3 asks for, and
   the honest refutation is of its RING: N7 shows it cannot be read as an
   object of [ModR S], where the exercise's N ⊗_R E lives.  No refutation
   of its BALANCE RULE is offered: at the only concrete ring in the tree
   the two rules coincide, ℤ being commutative, so a balance-level
   negative would not fire for the reason its comment claimed.

   ** THE VERBATIM ERROR TAILS

   (Transcribed with [o] for the composition circle, [-|] for the
   adjunction sign, [(x)] for the product of categories and [-->] for
   the functor arrow, so that this comment carries none of the glyphs
   the sources use.)

   N1  CONVERSION  (cannot unify "Ring_op (Ring_op R)" and "R").
   N2  CONVERSION  (cannot unify "ModR (Ring_op R)" and "RMod R").
   N3  TYPING      The term "bm_left E" has type "RModObject R" while it
                   is expected to have type "RModObject (Ring_op R)".
   N4  TYPING      The term "N" has type "RModObject (Ring_op R)" while
                   it is expected to have type "RModObject R".
   N5  TYPING      as N3.
   N6  TYPING      as N3.
   N7  TYPING      The term "TensorMod N (bimodule_right_RMod F)" has
                   type "RModObject (Ring_op R)" while it is expected to
                   have type "RModObject (Ring_op S)".
   N8  TYPING      The term "M" has type "RModObject (Ring_op R)" while
                   it is expected to have type "RModObject Int_Ring".
   N9  TYPING      as N8, fired at N9's ARGUMENT.
   N10 CONVERSION  (cannot unify "TensorWith E1 o TensorWith E" and
                   "TensorWith (BimodTensorBimod E E1)").
   N11 CONVERSION  (cannot unify "HomS E o HomS E1" and
                   "HomS (BimodTensorBimod E E1)").
   N12 TYPING      The term "RTensor E1 (RTensor E N)" has type
                   "RModObject (Ring_op T)" while it is expected to have
                   type "RModObject (Ring_op S)". [see the note below]
   N13 TYPING      The term "btb_left E E1" has type
                   "RModObject R" while it is expected to have type
                   "RModObject (Ring_op T)".
   N14 FORMABILITY (universe inconsistency: Cannot enforce up = uh ...).
   N15 FORMABILITY as N14, fired at N15's ARGUMENT.
   N16 CONVERSION  (cannot unify "bac_unit E E1 N" and
                   "fmap[HomS E] unit o unit").
   N17 CONVERSION  (cannot unify "bac_counit E E1 M" and
                   "counit o fmap[TensorWith E1] counit").

   N12's note: the two objects of part (c)'s comparison do NOT share a
   type at the SECOND ring, so the comparison cannot be an equality even
   before conversion is consulted; at the THIRD ring they do, and that
   reading is the [Check] beside N10, an accepted control, whose
   [eq_refl] is then refuted by N10's functor-level twin.

   ** WHAT THIS FILE DOES NOT DO

   It proves nothing new.  It contains no proof hole of any kind, no
   [Axiom], no [Parameter] and no aborted sketch; every positive control
   is a term or a [Check], never a tactic script, so nothing here can
   drift by a change in the automation.

--------
Mac Lane，《为实际数学家准备的范畴论》，第二版，第 IV.8 节  
   练习 3，第 104 页；目录编号 maclane:IV.8:ex3。该页面原文引用于 Instance/Mod/Bimodule.v 的页眉，此处不再重复。

该文件保护了该头文件的严格声明。下面每个被说成已被驳回的命令都被剥离到它自己的临时副本中，携带这个文件的整个前缀，单独编译，并读取其完整错误；在这个仓库的 coqc 下，一个通过的 [Fail] 不会打印任何信息，因此单独的整个文件 rc=0 只能证明每个命令不进行类型检查，而永远不能说明原因。每个负面情况都是根据错误文本进行分类的，而不是根据预期：

转换 - 消息包含“无法统一 A 和 B”条款，并且没有宇宙条款。
类型 - 一个简单的“项 T 的类型为 X，而期望的类型为 Y”；没有“无法统一”，没有宇宙条款。
可构造性 - “（宇宙不一致：无法强制 ...）”，命名封闭部分声明的级别。

** 记账

18 个 [Fail] 命令 = 1 个仪器检查 + 17 个阴性，分为三类：六个转换（N1、N2、N10、N11、N16、N17）、九个分型（N3-N9、N12、N13）和两个可成型性（N14、N15）。

** 两个否定衡量的是他们的论点，而不是他们的主题

N15 被命名为 [hom_ab]，它的第一个参数是一个 [AbEnriched Cu]，N14 刚刚展示过，它自身在声明的级别上是不可形成的；剥离后，它的错误属于 N14，但针对行衍生的级别名称，并且在 [Cu] 上触发。因此，[hom_ab] 无法脱离 [AbEnriched] 进行测试，并且它是否识别自己的任何内容是未知的，并未被否定。N9 就 [Build_Bimodule] 也处于同样的情况：剥离后，其错误在参数 [M] 上触发，并且逐字与 N8 相同，所以它所确立的是一个右 R-模不能是一个 (ℤ,R)-双模的 [bm_left]——这就是所主张的——而与 [Build_Bimodule] 本身无关。这是记录在问题 #340 下 [MonoidObject] 的陷阱，这里陈述出来而不是省略。

** 机械测量的护罩覆盖

去掉了注释，并将文件按句点后跟空格分割成命令：共有191条命令，其中18条以[Fail]开头；它们提到50个不同的标识符，其中40个也出现在非[Fail]命令中。剩下不出现的十个是：关键字[Fail]；[AC]，它本身绑定在N15内部；七个被否定声明的名称（[p401_n1]、[p401_n2]、[p401_n7]、[p401_n10]、[p401_n11]、[p401_n16]、[p401_n17]），由于声明它们的命令类型检查不通过，因此从未进入环境；以及[p401_no_such_constant_anywhere]，即该工具故意缺失的名称。没有任何负面命名的常量是未受保护的。

** 重命名模拟

在 Instance/Mod/Bimodule.v 中，五个常量在一个负面中被命名：[TensorWith]、[HomS]、[BimodTensorBimod]、[RTensor] 和 [btb_left]。每个常量在该文件的一个 SCRATCH COPY 中被重命名（该副本仍可编译，没有错误），然后编译了一个需要该 scratch 模块的该文件副本。全部五个都导致编译失败，每一个都在 guard 块的 [Check] 行上，没有一个在 [Fail] 内：[TensorWith]、[HomS]、[BimodTensorBimod]、[RTensor] 和 [btb_left]，每个都位于其自己的 [Check] guard 上。因此 5/5，guard 完全没有空值。

** 阶段 1 的发现 8 的危害，以及它为何如此

[@TensorMod (Ring_op R) N (bimodule_right_RMod F)] 对 [F : Bimodule S R] 类型检查——也就是控制 [p401_hazard_accepted]——并且是两个右 R 模的张量，将 (n ⊲ r) ⊗ e 与 n ⊗ (e ⊲ r) 平衡。因此，它不是习题 3 所要求的对象，诚实的反驳是它的环：N7 显示它不能被读取为 [ModR S] 的对象，而习题中的 N ⊗_R E 就存在于那里。没有提供对其平衡规则的反驳：在树中唯一的具体环上，两条规则是相同的，因为 ℤ 是交换的，所以平衡层面的否定不会因为它的注释声称的原因而发生。

**逐字错误尾

(使用 [o] 转录作曲圈，[-|] 转录附加符号，[(x)] 转录范畴的积，[-->] 转录函子箭头，因此此评论不包含来源使用的任何字形。)

N1  转换  （无法统一 "Ring_op (Ring_op R)" 和 "R"）。 N2  转换  （无法统一 "ModR (Ring_op R)" 和 "RMod R"）。 N3  类型检查  术语 "bm_left E" 的类型是 "RModObject R"，而预期类型是 "RModObject (Ring_op R)"。 N4  类型检查  术语 "N" 的类型是 "RModObject (Ring_op R)"，而预期类型是 "RModObject R"。 N5  类型检查  同 N3。 N6  类型检查  同 N3。 N7  类型检查  术语 "TensorMod N (bimodule_right_RMod F)" 的类型是 "RModObject (Ring_op R)"，而预期类型是 "RModObject (Ring_op S)"。 N8  类型检查  术语 "M" 的类型是 "RModObject (Ring_op R)"，而预期类型是 "RModObject Int_Ring"。 N9  类型检查  同 N8，在 N9 的参数处触发。
N10 转换（无法统一 "TensorWith E1 o TensorWith E" 与 "TensorWith (BimodTensorBimod E E1)"）。N11 转换（无法统一 "HomS E o HomS E1" 与 "HomS (BimodTensorBimod E E1)"）。N12 类型检查 术语 "RTensor E1 (RTensor E N)" 的类型为 "RModObject (Ring_op T)"，而预计的类型为 "RModObject (Ring_op S)"。[see the note below]
N13 类型检查 术语 "btb_left E E1" 的类型为 "RModObject R"，而预计的类型为 "RModObject (Ring_op T)"。N14 可形成性（宇宙不一致：无法强制 up = uh ...）。N15 可形成性，如 N14，在 N15 的参数处触发。N16 转换（无法统一 "bac_unit E E1 N" 与 "fmap[HomS E] unit o unit"）。
N17 转换（无法统一 "bac_counit E E1 M" 和 "counit o fmap[TensorWith E1] counit"）。

N12的注释：部分(c)比较的两个对象在第二层环上没有共享类型，因此即使在考虑转换之前，该比较也不能是相等的；在第三层环上它们共享类型，而该读数是位于N10旁边的[Check]，这是一个被接受的对照，其[eq_refl]随后被N10的函子级双胞所驳斥。

** 本文件不做的事情

这没有证明任何新东西。它不包含任何类型的漏洞，没有 [Axiom]，没有 [Parameter]，也没有中止的草图；每个阳性对照都是一个术语或 [Check]，从来不是策略脚本，所以这里没有什么会因为自动化的变化而偏移。
*)

(* --------------------------------------------------------------- *)
(* INSTRUMENT.  A passing [Fail] prints nothing under this repo's / INSTRUMENT.  A passing [Fail] prints nothing under this repo's / 工具。一个经过的 [Fail] 在这个仓库下不打印任何内容    *)
(* coqc, so this command establishes that [Fail] does anything. / coqc，所以这个命令确定了 [Fail] 做了任何事情。      *)
(* --------------------------------------------------------------- *)

Fail Check p401_no_such_constant_anywhere.

(* --------------------------------------------------------------- *)
(* GUARD BLOCK.  Every constant that any negative below names is / 防护块。以下任何负数所对应的每个常量是     *)
(* named here OUTSIDE every [Fail], so that renaming one of them / 在每个 [Fail] 外部命名，以便重命名其中一个     *)
(* breaks this file at a [Check] line rather than turning a negative / 在 [Check] 行处中断此文件，而不是转成负数 *)
(* vacuously green. / 空洞地绿色。                                                  *)
(* --------------------------------------------------------------- *)

Check @Category.
Check @Functor.
Check @Adjunction.
Check @Isomorphism.
Check @eq.
Check @obj.
Check @hom.
Check @id.
Check @compose.
Check @Compose.

Check @RingObject.
Check @Ring_op.
Check @RModObject.
Check @RModHom.
Check @RMod.
Check @ModR.
Check @Bimodule.
Check @Build_Bimodule.
Check @bm_left.
Check @bimodule_right_RMod.
Check @rm_ab.
Check @rm_smul.
Check @Int_Ring.
Check @Int_Bimodule.
Check @Ring_RMod.
Check @TensorMod.
Check @RBilinear.
Check @AbEnriched.
Check @hom_ab.
Check @Ab_AbEnriched.

Check @BalTensor.
Check @BalBiadditive.
Check @bs_gen.
Check @be_balance.
Check @bal_med.
Check @bal_hom_ext.
Check @RTensor.
Check @TensorWith.
Check @HomSObj.
Check @HomS.
Check @bimodule_tensor_hom_adjunction.
Check @BimodCat.
Check @BimodHom.
Check @BimodTensor.
Check @bimodule_parametrized_adjunction.
Check @bimodule_hom_bifunctor.
Check @RMod_AbEnriched.

Check @LTensor.
Check @LTensorWith.
Check @LHomSObj.
Check @LHomS.
Check @bimodule_left_tensor_hom_adjunction.
Check @bimodule_left_tensor_preserves_colimits.
Check @bimodule_tensor_preserves_colimits.
Check @PreservesAllColimits.

Check @BimodTensorBimod.
Check @btb_left.
Check @btb_right.
Check @bimodule_adjunction_composite.
Check @tensor_assoc_iso.
Check @ta_to.
Check @ta_from.
Check @ta_iso.
Check @adjunction_along_left_iso.
Check @aali_cell.
Check @bimodule_tensor_bimod_adjunction.
Check @bimodule_hom_composite_iso.

Check @HomAbBimod.
Check @HomAbFunctor.
Check @hab_partial_adj.
Check @bimodule_mirror_family.
Check @bimodule_two_variable_adjunction.
Check @bimodule_third_leg.
Check @mr_left.
Check @mr_right.
Check @mirror_family.
Check @mutually_right_adjoint.
Check @AdjointOnTheRight.
Check @Swap.
Check @Partial_r.
Check @Partial_l.

Check @ZRight.
Check @int_mult_bal.
Check @int_tensor_separates.

(* ================================================================= *)
(* (1) N1-N2.  [Ring_op] is not strictly involutive, so the two / (1) N1-N2。[Ring_op] 并非严格的自反运算，所以两者       *)
(*     readings of a right module are not interchangeable on the / 右模块的读数在...上不可互换      *)
(*     nose.  Both are CONVERSION. / 鼻子。两者都是转换。                                    *)
(* ================================================================= *)

Section P401RingOp.

Context (R : RingObject).

(* CONTROLS: all six DATA fields of the double opposite DO agree. / 控制：双重相反 DO 的所有六个数据字段都同意。 *)
Example p401_op_setoid :
  rig_setoid (ring_rig (Ring_op (Ring_op R))) = rig_setoid (ring_rig R)
  := eq_refl.
Example p401_op_add :
  rig_add (ring_rig (Ring_op (Ring_op R))) = rig_add (ring_rig R)
  := eq_refl.
Example p401_op_one :
  rig_one (ring_rig (Ring_op (Ring_op R))) = rig_one (ring_rig R)
  := eq_refl.
Example p401_op_zero :
  rig_zero (ring_rig (Ring_op (Ring_op R))) = rig_zero (ring_rig R)
  := eq_refl.
Example p401_op_mul :
  rig_mul (ring_rig (Ring_op (Ring_op R))) = rig_mul (ring_rig R)
  := eq_refl.
Example p401_op_neg :
  ring_neg (Ring_op (Ring_op R)) = ring_neg R := eq_refl.

(* -- N1 (CONVERSION) -- *)
Fail Example p401_n1 : Ring_op (Ring_op R) = R := eq_refl.

(* -- N2 (CONVERSION) -- *)
Fail Example p401_n2 : ModR (Ring_op R) = RMod R := eq_refl.

(* CONTROL: what IS true on the nose. / 控制：什么是准确的。 *)
Example p401_modR_unfold : ModR R = RMod (Ring_op R) := eq_refl.

End P401RingOp.

(* ================================================================= *)
(* (2) N3-N7.  Instance/Mod/Tensor.v's [TensorMod] serves NEITHER / (2) N3-N7。Instance/Mod/Tensor.v 的 [TensorMod] 两者都不提供     *)
(*     handedness of Exercise 3, and the one term that DOES typecheck / handedness of Exercise 3, and the one term that DOES typecheck / 练习3的惯用手，以及唯一一个可以类型检查的项 *)
(*     computes the wrong object.  All TYPING. / 计算错误的对象。全是 TYPING。                        *)
(* ================================================================= *)

Section P401TensorMod.

Context (R S : RingObject).
Context (E : Bimodule R S).
Context (F : Bimodule S R).
Context (N : RModObject (Ring_op R)).

(* -- N3 (TYPING) -- *)
Fail Check (TensorMod N (bm_left E)).

(* -- N4 (TYPING) -- *)
Fail Check (@TensorMod R N (bm_left E)).

(* -- N5 (TYPING) -- *)
Fail Check (@TensorMod (Ring_op R) N (bm_left E)).

(* -- N6 (TYPING) -- *)
Fail Check (RBilinear N (bm_left E) (bm_left E)).

(*
CONTROLS: [TensorMod] is fine when both factors are modules over ONE
   ring on the SAME side.

--------
控制：当两个因子都是同一个环在同一侧的模时，[TensorMod] 是没问题的。
*)
Check (@TensorMod R (bm_left E) (bm_left E)).
Check (@TensorMod (Ring_op R) N N).

(* CONTROL, and the HAZARD: this one IS accepted. / 控制与危险：这个是被接受的。 *)
Definition p401_hazard_accepted : RModObject (Ring_op R) :=
  @TensorMod (Ring_op R) N (bimodule_right_RMod F).

(*
-- N7 (TYPING).  It is a right R-module, so it is not an object of
      [ModR S], which is where Exercise 3's N ⊗_R E lives. --

--------
-- N7（打字）。它是一个右R模，因此它不是[ModR S]的对象，而Exercise 3的N ⊗_R E就在[ModR S]中。--
*)
Fail Definition p401_n7 : RModObject (Ring_op S) :=
  @TensorMod (Ring_op R) N (bimodule_right_RMod F).

(* CONTROL: the object Exercise 3 does produce, at the same [N]. / 控制：对象 Exercise 3 确实在相同的 [N] 下产生。 *)
Check (RTensor E N : RModObject (Ring_op S)).

End P401TensorMod.

(* ================================================================= *)
(* (3) N8-N9.  Riehl's general three-ring form is closed off: a right / (3) N8-N9。Riehl 的通用三环形式是封闭的：一个右边 *)
(*     R-module is not a (ℤ,R)-bimodule in this tree.  Both TYPING. / 在此树中，R 模块不是一个 (ℤ, R)-双模。 两者都是 TYPING。   *)
(* ================================================================= *)

Section P401Integers.

Context (R : RingObject).
Context (M : RModObject (Ring_op R)).

(* -- N8 (TYPING) -- *)
Fail Check (M : RModObject Int_Ring).

(* -- N9 (TYPING) -- *)
Fail Check (@Build_Bimodule Int_Ring R M).

(* CONTROLS: ℤ's own bimodule, and the module reading that DOES hold. / 控件：ℤ 自己的双模，以及确实有效的模块读取。 *)
Check (Int_Bimodule : Bimodule Int_Ring Int_Ring).
Check (bm_left Int_Bimodule : RModObject Int_Ring).
Check (M : RModObject (Ring_op R)).

End P401Integers.

(* ================================================================= *)
(* (4) N10-N13.  Part (c)'s comparison is an isomorphism and NOTHING / (4) N10-N13。部分 (c) 的比较是同构，并且什么都没有  *)
(*     stronger: the two functors are different records, the two / 更强：这两个函子是不同的记录，两个      *)
(*     objects are different records, and the two module structures / 对象是不同的记录，以及两个模块结构   *)
(*     on the tensor of two bimodules do not even share a type. / 在两个双模上的张量甚至不共享类型。       *)
(* ================================================================= *)

Section P401PartC.

Context (R S T : RingObject).
Context (E : Bimodule R S).
Context (E1 : Bimodule S T).
Context (N : RModObject (Ring_op R)).

(* CONTROLS: the comparison exists, and its two sides DO share a type. / 控制：比较存在，其两边确实共享一种类型。 *)
Check (tensor_assoc_iso E E1
  : (TensorWith E1 ◯ TensorWith E : ModR R ⟶ ModR T)
      ≈ TensorWith (BimodTensorBimod E E1)).
Check ((RTensor E1 (RTensor E N) : RModObject (Ring_op T))
         = RTensor (BimodTensorBimod E E1) N).

(* -- N10 (CONVERSION) -- *)
Fail Example p401_n10 :
  (TensorWith E1 ◯ TensorWith E : ModR R ⟶ ModR T)
    = TensorWith (BimodTensorBimod E E1) := eq_refl.

(* -- N11 (CONVERSION) -- *)
Fail Example p401_n11 :
  (HomS E ◯ HomS E1 : ModR T ⟶ ModR R)
    = HomS (BimodTensorBimod E E1) := eq_refl.

(*
-- N16 (CONVERSION) -- Mac Lane's whiskered description of the
   composite's unit holds at ≈ ([bac_unit_whiskered]) and NOT on the nose:
   Adjunction/Compose.v is a [Qed] corollary proved by rewriting.

--------
-- N16（转换）-- Mac Lane 对复合体单位的带须描述在 ≈ ([bac_unit_whiskered]) 处成立，而不是精确成立：
Adjunction/Compose.v 是通过重写证明的 [Qed] 推论。
*)
Fail Example p401_n16 :
  bac_unit E E1 N
    = fmap[HomS E]
        (@unit (ModR T) (ModR S) (TensorWith E1) (HomS E1)
           (bimodule_tensor_hom_adjunction E1) (RTensor E N))
      ∘ @unit (ModR S) (ModR R) (TensorWith E) (HomS E)
          (bimodule_tensor_hom_adjunction E) N := eq_refl.

(*
-- N17 (CONVERSION) -- the counit's twin ([bac_counit_whiskered],
   Adjunction/Compose.v).

--------
-- N17（转换）-- 单元的孪生（[bac_counit_whiskered]，Adjunction/Compose.v）。
*)
Fail Example p401_n17 (M : RModObject (Ring_op T)) :
  bac_counit E E1 M
    = @counit (ModR T) (ModR S) (TensorWith E1) (HomS E1)
        (bimodule_tensor_hom_adjunction E1) M
      ∘ fmap[TensorWith E1]
          (@counit (ModR S) (ModR R) (TensorWith E) (HomS E)
             (bimodule_tensor_hom_adjunction E) (HomSObj E1 M)) := eq_refl.

(* CONTROLS for N16/N17: the ≈ forms are theorems of the target. / N16/N17 的控制：≈ 形式是目标的定理。 *)
Check (bac_unit_whiskered E E1 N).
Check (fun (M : RModObject (Ring_op T)) => bac_counit_whiskered E E1 M).
Check @bac_unit.
Check @bac_counit.
Check @unit.
Check @counit.
Check @fmap.

(* CONTROL: what the file DOES deliver in place of N11. / 控制：该文件提供的内容代替了N11。 *)
Check (bimodule_hom_composite_iso E E1
  : (HomS E ◯ HomS E1 : ModR T ⟶ ModR R)
      ≈ HomS (BimodTensorBimod E E1)).

(*
-- N12 (TYPING).  Read at the SECOND ring the two sides of the
      comparison are not even of one type. --

--------
-- N12（打字）。在第二环读数时，比较的两边甚至不是同一类型。--
*)
Fail Check (RTensor E1 (RTensor E N) : RModObject (Ring_op S)).

(*
-- N13 (TYPING).  The two module structures the tensor of two
      bimodules carries are over DIFFERENT rings. --

--------
-- N13（打字）。两个模结构在两个双模上的张量承载的是不同环上的结构。--
*)
Fail Check (btb_left E E1 : RModObject (Ring_op T)).

(* CONTROLS: each on its own ring, and the ONE group they share. / CONTROLS: each on its own ring, and the ONE group they share. / 控制：每个在自己的环上，以及它们共享的那个单一组。 *)
Check (btb_left E E1 : RModObject R).
Check (btb_right E E1 : RModObject (Ring_op T)).
Example p401_btb_same_group :
  rm_ab (btb_left E E1) = rm_ab (btb_right E E1) := eq_refl.

End P401PartC.

(* ================================================================= *)
(* (5) N14-N15.  The hom-group's enrichment demands a category whose / (5) N14-N15。hom-群的增广需要一个其  *)
(*     hom and proof universes coincide. / hom 和 proof 宇宙重合。                              *)
(* ================================================================= *)

Section P401Univ.

Universes uo uh up.
Constraint uh < up.

Context (Cu : Category@{uo uh up}).

(* CONTROLS at the DECLARED levels. / 在申报水平上的控制。 *)
Check (fun (x y : Cu) => x ~{Cu}~> y).
Check (fun (x : Cu) => @id Cu x).
Check (fun (x y z : Cu) (f : y ~> z) (g : x ~> y) => f ∘ g).

(* -- N14 (FORMABILITY) -- *)
Fail Check (AbEnriched Cu).

(* -- N15 (FORMABILITY, fired at its ARGUMENT) -- / -- N15（可成形性，在其论点上被驳火）-- *)
Fail Check (fun (AC : AbEnriched Cu) (x y : Cu) => hom_ab AC x y).

End P401Univ.

(* ================================================================= *)
(* (6) POSITIVE CONTROLS for the three headline artifacts of stage 2. / (6) 阶段2三个主要实验样本的阳性对照。 *)
(* ================================================================= *)

Section P401Positives.

Context (R S T : RingObject).
Context (E : Bimodule R S).
Context (E1 : Bimodule S T).

Check (bimodule_adjunction_composite E E1
  : (TensorWith E1 ◯ TensorWith E) ⊣ (HomS E ◯ HomS E1)).

Check (bimodule_left_tensor_hom_adjunction E
  : LTensorWith E ⊣ LHomS E).

Check (bimodule_tensor_preserves_colimits E
  : PreservesAllColimits (TensorWith E)).

Check (fun (M : RModObject (Ring_op S)) (N : RModObject (Ring_op R)) =>
  bimodule_third_leg M E N
    : @Isomorphism Sets
        {| carrier := E ~{@BimodCat R S}~> HomAbBimod N M;
           is_setoid := @homset (@BimodCat R S) E (HomAbBimod N M) |}
        {| carrier := N ~{ModR R}~> HomSObj E M;
           is_setoid := @homset (ModR R) N (HomSObj E M) |}).

End P401Positives.
