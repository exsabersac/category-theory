Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Universal.Element.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Construction.Elements.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Adjunction.SpanningArrow.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Ab.DirectedColimit.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Mod.Bimodule.
Require Import Category.Instance.Mod.Limit.
Require Import Category.Instance.Mod.Spanning.
Require Import Category.Instance.Mod.TensorAFT.
Require Import Category.Theory.Algebra.Rig.
(*
Beyond the target's own list: [Adjunction.GAFT] and [GAFT.Resize] for
   the [SolutionSet]/[SmallUpToIso] vocabulary section 10 of the target
   uses, and [Instance.Rng] for [Q_Ring], the SECOND concrete ring the
   payoff section below instantiates at.

--------
超出目标自身的列表：[Adjunction.GAFT] 和 [GAFT.Resize] 用于目标使用的 [SolutionSet]/[SmallUpToIso] 词汇第10部分，以及 [Instance.Rng] 用于 [Q_Ring]，下面的支付部分在第二个具体环中实例化。
*)
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.GAFT.Resize.
Require Import Category.Instance.Rng.

(**
* Probe for issue #449: the tensor product from the adjoint functor
      theorem (Mac Lane §V.7, book p. 128)

    The import list above is Instance/Mod/TensorAFT.v's own, verbatim, plus
    that file itself; a shorter prefix is what makes a probe pass for no
    reason.

    DISCIPLINE.  Quoted refusals below have their generated universe names
    replaced by readable ones ([u_obj], [u_Sets], [u_obj'], [u_Sets'],
    [u]): the real messages carry names like [S165.1055] that are
    file-name dependent and would not survive a rename.  The substitution
    is positional and everything else in a quoted message is verbatim.
    Every negative below is paired with a positive control
    naming the same library constants, the instrument was checked (a
    refusal expected around a command that succeeds stops the file), and
    each negative was re-run alone with its guard stripped IN A COPY OF THE
    WHOLE FILE so that the refusal kind could be read off the message
    rather than guessed.  The refusal kinds recorded are UNIVERSE (four),
    CONVERSION (two) and ARGUMENT NAME (one), beside the instrument check,
    whose refusal is a missing NAME.

    WHAT THE UNIVERSE NEGATIVES PIN.  Mac Lane's covering family -- the
    bilinear maps that span their target -- is a sigma over the OBJECTS of
    [RMod R], and [representability_theorem] demands an index at the ring's
    CARRIER universe.  Since a module's carrier sits strictly below the
    universe its objects live at, the two cannot meet.  That is a wall of
    the same FAMILY as the one Instance/Grp/FreeAFT.v reports at [Grp],
    whose donor is a universe-minimization artifact of
    Instance/Discrete.v's [DiscreteCat_Functor] and whose repair is filed
    as #1309 -- but it is NOT the same wall, and #1309 is measured not to
    lift it: applying that repair removed the literal [Set] from the
    refusals below and left the refusals themselves standing, as the
    index-universe = carrier-universe identification.
    Instance/Mod/TensorAFT.v's section 2 records that measurement.

    RECORDED CORRECTION, PR "algebraic carriers are sets" (2026-09-17).
    Two clauses of the paragraph above were true when written and are not
    now.  (i) "which it also pins to [Set]" -- the literal [Set] went with
    the annotation of [DiscreteCat_Functor], and every quoted refusal
    below has been re-measured without it.  (ii) The heading said FOUR
    universe negatives; there are now THREE, NEGATIVE 4 having become a
    positive control, plus the NEW negative 8 below, which pins the side
    condition the unconditional construction introduces.

    AND WHAT THE WALL DOES NOT STOP, which is the point of this PR.  The
    wall is about ONE index -- the sigma over objects.  A DIFFERENT
    solution set for the same functor, indexed by the [Prop]-valued
    congruences on the term module, sits AT the carrier universe and the
    theorem accepts it.  So [tensor_via_AFT] is now unconditional, and the
    payoff section below exhibits it at [Int_Ring], at [Q_Ring] and at the
    opposite ring.  NEGATIVES 1-3 are unaffected: they are statements
    about the object-indexed family, which nothing here moves.

--------
* 针对问题 #449 的探讨：从伴随定理得到的张量积（Mac Lane §V.7，书籍第128页）

上面的导入列表是 Instance/Mod/TensorAFT.v 自己的，逐字的，加上那个文件本身；更短的前缀会让探针无缘无故地通过。

纪律。下面引用的拒绝信息中，生成的宇宙名称已被可读名称（[u_obj]、[u_Sets]、[u_obj']、[u_Sets']、[u]）替换：真实消息中包含的名称类似 [S165.1055]，这取决于文件名，重命名后将无法保留。替换是按位置进行的，引用消息中的其他内容完全保持原样。下面的每个负面情况都与一个正面对照配对，正面对照使用相同的库常量，仪器已被检查（通常在命令成功停止文件时会产生拒绝），并且每个负面情况都单独在整个文件的副本中运行，去掉其保护，以便可以从消息中读取拒绝类型，而不是猜测。记录的拒绝类型包括 UNIVERSE（四次）、CONVERSION（两次）和 ARGUMENT NAME（一次），此外还有仪器检查，其拒绝类型是缺失的 NAME。

宇宙否定针。Mac Lane 的覆盖族——生成其目标的双线性映射——是在 [RMod R] 的对象上的 σ，而 [representability_theorem] 要求在环的承载宇宙上有一个索引。由于模块的承载严格低于其对象所在的宇宙，两者无法相遇。这是一堵与 Instance/Grp/FreeAFT.v 在 [Grp] 报告的同一家族的墙，其捐赠者是 Instance/Discrete.v 的 [DiscreteCat_Functor] 的宇宙最小化工件，其修复记录为 #1309 ——但它不是同一堵墙，并且 #1309 被测量为无法提升它：应用该修复移除了下方拒绝中的字面 [Set]，但拒绝本身仍然存在，作为索引宇宙 = 承载宇宙的识别。Instance/Mod/TensorAFT.v 的第 2 节记录了该测量。

已记录更正，PR “代数承载体是集合”（2026-09-17）。上述段落的两条条款在写作时为真，而现在不再如此。(i) “它也固定到 [Set] 上”——字面上的 [Set] 与 [DiscreteCat_Functor] 的注释相关联，下面每个引用的拒绝意见都已在没有它的情况下重新测量。(ii) 标题写着四个宇宙负数；现在有三个，NEGATIVE 4 已变为正控制，加上下面的新负数 8，它固定了无条件构造引入的附加条件。

以及这堵墙无法阻止的，这就是该公关的重点。墙大约是一个索引——即对象的σ。针对同一个函子的一组不同解集，由[Prop]值的同余在项模上索引，位于承载宇宙，并且定理接受它。因此[tensor_via_AFT]现在是无条件的，下方的收益部分在[Int_Ring]、[Q_Ring]以及对面环上展示了它。负数1-3不受影响：它们是关于对象索引族的陈述，这里没有任何东西会改变它们。
*)

(** ** Instrument check / ** 仪表检查 *)

(*
A refusal expected around a name that is not there.  If the instrument
   were inert this line would pass silently and so would everything below
   it.

--------
对一个不存在的名字的拒绝是预料之中的。如果该工具是惰性的，这一行将静默通过，其下面的所有内容也将如此。
*)
Fail Check zzz_no_such_constant_449.

(** ** Positive controls: every library constant a negative names / ** 阳性对照：每个文库的常数一个阴性名称 *)

Section Controls.

Context {R : RingObject}.
Context (V V' : RModObject R).

Check (RMod_Complete R).
Check (Bilin_continuous V V').
Check (Bilin_PreservesImageLimit V V').
Check (tensor_esols_direct V V').
Check (tensor_esols_from_tensor V V').
Check (Bilin_PreservesWidePullbacks V V').
Check (RMod_HasWidePullbacks R).
Check (TensorMod V V').
Check (@tensor_gen R V V').
Check (tensor_repr_of_UE V V').
Check (preserves_image_of_representable (tensor_repr_of_UE V V')).
Check (@SpanningArrowsOutOf (RMod R) Sets (Bilin V V') SetsOne).

(* The three [eq_refl] readbacks of the direct solution set, as controls. / 直接解集的三个 [eq_refl] 读取作为对照。 *)
Example c_esol_index :
  esol_index (tensor_esols_direct V V')
    = SpanningArrowsOutOf (Bilin V V') SetsOne := eq_refl.

Example c_esol_obj (i : SpanningArrowsOutOf (Bilin V V') SetsOne) :
  esol_obj (tensor_esols_direct V V') i = `1 i := eq_refl.

Example c_esol_elem (i : SpanningArrowsOutOf (Bilin V V') SetsOne) :
  esol_elem (tensor_esols_direct V V') i = `1 (`2 i) ttt := eq_refl.

(*
The conditional solution set of Instance/Mod/Spanning.v shares that
   index on the nose.  [HWP] is passed EXPLICITLY: the exported instance
   [RMod_HasWidePullbacks] would be found by resolution and then refused at
   the application, for the universe reason that file records.

--------
实例/模块/生成.v 的条件解集合正好共享那个索引。[HWP] 是显式传递的：导出的实例 [RMod_HasWidePullbacks] 会通过解析找到，然后在应用时被拒绝，这是由于文件记录的通用原因。
*)
Example c_same_index (HWP : @HasWidePullbacks (RMod R)) :
  esol_index (@tensor_esols R V V' HWP)
    = esol_index (tensor_esols_direct V V') := eq_refl.

(*
The representation read off the explicit tensor keeps [TensorMod] as its
   representing object at [eq_refl] -- the control the CONVERSION negative
   below is measured against.

--------
从显式张量读取的表示将 [TensorMod] 保持为其在 [eq_refl] 的表示对象 —— 下面的 CONVERSION 负值的控制是以此为衡量的。
*)
Example c_repr_of_UE_obj :
  @repr_obj (RMod R) (Bilin V V') (tensor_repr_of_UE V V') = TensorMod V V'
  := eq_refl.

End Controls.

Section AbControls.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

Check (BalBiadd N M).
Check (BalBiadd_continuous N M).
Check (BalBiadd_PreservesImageLimit N M).
Check (bal_esols_direct N M).
Check (bal_esols_from_tensor N M).
Check Ab_Complete.
Check (BalTensor N M).
Check (@bal_gen X N M).

Example c_bal_ue_obj :
  @ue_obj Ab (BalBiadd N M) (bal_UniversalElement N M) = BalTensor N M
  := eq_refl.

Example c_bal_ue_elem :
  @ue_elem Ab (BalBiadd N M) (bal_UniversalElement N M) = @bal_gen X N M
  := eq_refl.

Example c_bal_esol_index :
  esol_index (bal_esols_direct N M)
    = SpanningArrowsOutOf (BalBiadd N M) SetsOne := eq_refl.

End AbControls.

(*
The two applications the negatives below sit beside, at an unconstrained
   ring: these ARE accepted, so the negatives are about the argument, not
   about the theorem being unusable.

--------
下面的两个应用程序的否定位于一个无约束的环旁：这些是被接受的，所以否定是关于论点的，而不是关于定理无法使用。
*)
Check (fun (R : RingObject) (V V' : RModObject R) => tensor_via_AFT V V').
Check (fun (R : RingObject) (V V' : RModObject R) =>
         module_tensor_universal V V').
(* the issue's verification name IS the AFT universal element, by definition / 根据定义，该问题的验证名称是AFT通用元素 *)
Example c_alias_is_ue : @module_tensor_universal = @tensor_AFT_ue := eq_refl.
Check (fun (R : RingObject) (V V' : RModObject R) =>
         tensor_via_AFT_from_tensor V V').
Check (fun (X : RingObject) (N : RModObject (Ring_op X))
           (M : RModObject X) => bal_tensor_via_AFT N M).

(**
** THE PAYOFF: the construction is unconditional, and here it is at
       three named rings

    RECORDED CORRECTION.  Every [Check] in this section would have been
    ill-typed before the PR "algebraic carriers are sets" (2026-09-17):
    [tensor_via_AFT] took a solution set as an argument, and the only
    in-tree inhabitants of that argument were the two CIRCULAR ones.  The
    file's own "NOT DELIVERED (5) NO CONCRETE WITNESS" said so.  These
    lines are what makes the removal of that clause checkable: if the
    hypothesis ever comes back, they stop compiling.

--------
** 回报：该构造是无条件的，这里它存在于三个命名环中

记录更正。本节中的每个 [Check] 在 PR“代数承载体是集合”（2026-09-17）之前都是类型错误的：[tensor_via_AFT] 以解集作为参数，而该参数的树内唯一居民是两个循环的。该文件自身的“未交付（5）无具体证据”也说明了这一点。这些行使得删除该条款可检查：如果假设再次出现，它们会阻止编译。
*)

Section UnconditionalPayoff.

(*
The tensor product of the integers with themselves as a Z-module,
   obtained from the adjoint functor theorem with NO hypothesis.

--------
作为 Z-模的整数自身的张量积，是从伴随定理获得的，无需假设。
*)
Check (tensor_via_AFT Int_RMod Int_RMod).
Check (module_tensor_universal Int_RMod Int_RMod).
Check (tensor_AFT_iso Int_RMod Int_RMod).
Check (tensor_AFT_ue Int_RMod Int_RMod).

(*
Mac Lane's OWN p. 128 family, resized by his Lemma 2 (section 10 of the
   target), at the same ring: the second, book-faithful route.

--------
Mac Lane 自身第128页的族，由他的引理2（目标的第10节）调整大小，在同一个环上：第二条，忠于书本的路径。
*)
Check (tensor_via_AFT_maclane Int_RMod Int_RMod).
Check (tensor_spanning_SmallUpToIso Int_RMod Int_RMod).
Check (tensor_esols_resized Int_RMod Int_RMod).

(* A SECOND ring, and a genuinely different one: the rationals. / 第二个环，并且是真正不同的一个：有理数环。 *)
Definition p449_QMod : RModObject Q_Ring := Ring_RMod Q_Ring.
Check (tensor_via_AFT p449_QMod p449_QMod).
Check (tensor_via_AFT_maclane p449_QMod p449_QMod).

(*
A THIRD: the opposite ring of the integers, which is what Exercise 3's
   balanced tensor needs on the left.

--------
第三：整数的对立环，这正是练习3中平衡张量在左侧所需要的。
*)
Definition p449_OpMod : RModObject (Ring_op Int_Ring) :=
  Ring_RMod (Ring_op Int_Ring).
Check (tensor_via_AFT p449_OpMod p449_OpMod).

(* Exercise 3 at the integers, also unconditional. / 整数上的练习3，也是无条件的。 *)
Check (bal_tensor_via_AFT p449_OpMod Int_RMod).
Check (bal_AFT_iso p449_OpMod Int_RMod).
Check (bal_AFT_ue p449_OpMod Int_RMod).
Check (bal_esols_prop p449_OpMod Int_RMod).

End UnconditionalPayoff.

(**
** The two indices, read back at [eq_refl]

    The whole repair is one inequality between two index universes, and
    these pin WHICH two types the indices are.  The measured universe
    readbacks that go with them, [About] under [Set Printing Universes],
    are in Instance/Mod/TensorAFT.v's section 3A: the congruence index
    takes [u4 := u0], the ring's carrier universe, while
    [tensor_esols_direct]'s gives [u0 < u12].  An [About] is not a
    command a probe can guard, so the types are pinned here and the
    universes are pinned by NEGATIVE 1 (the direct family is refused) and
    by the payoff section above (the congruence family is not).

--------
** 这两个索引，在 [eq_refl] 处读取回来。

整个修复是两个索引宇宙之间的不等式，并且这些限定了索引是哪两种类型。 与它们对应的测量宇宙读回值，[About] 在 [Set Printing Universes] 下，位于 Instance/Mod/TensorAFT.v 的 3A 节：同余索引采用 [u4 := u0]，即环的承载宇宙，而 [tensor_esols_direct] 的给出 [u0 < u12]。[About] 不是探针可以保护的命令，因此类型在这里被固定，并且宇宙通过负 1（直接族被拒绝）和上面的奖励部分（同余族不被拒绝）被固定。
*)

Section IndexReadbacks.

Context {R : RingObject}.
Context (V V' : obj[RMod R]).

Example p449_prop_index :
  esol_index (tensor_esols_prop V V') = CongIdx V V' := eq_refl.

Example p449_prop_obj (i : CongIdx V V') :
  esol_obj (tensor_esols_prop V V') i = QMod (`1 i) (`2 i) := eq_refl.

Example p449_prop_elem (i : CongIdx V V') :
  esol_elem (tensor_esols_prop V V') i = QMod_gen (`1 i) (`2 i) := eq_refl.

(*
Mac Lane's Lemma 2: the SMALL index of the resized family is the same
   congruence type.

--------
Mac Lane 的引理 2：调整大小后的族的 SMALL 指数具有相同的同余类型。
*)
Example p449_maclane_small_index :
  si_carrier (tensor_spanning_SmallUpToIso V V') = CongIdx V V' := eq_refl.

Example p449_resized_index :
  esol_index (tensor_esols_resized V V') = CongIdx V V' := eq_refl.

(*
And the direct family's index is still the sigma over objects -- the
   one NEGATIVE 1 refuses.

--------
而直系家族的索引仍然是对象上的西格玛——那个负一拒绝的。
*)
Example p449_direct_index :
  esol_index (tensor_esols_direct V V')
    = SpanningArrowsOutOf (Bilin V V') SetsOne := eq_refl.

End IndexReadbacks.

Section BalIndexReadbacks.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

Example p449_bal_prop_index :
  esol_index (bal_esols_prop N M) = BalCongIdx N M := eq_refl.

Example p449_bal_prop_obj (i : BalCongIdx N M) :
  esol_obj (bal_esols_prop N M) i = QBal (`1 i) (`2 i) := eq_refl.

End BalIndexReadbacks.

(**
** NEGATIVE 1 (UNIVERSE): Mac Lane's covering family is refused

    RE-MEASURED 2026-09-17, after [DiscreteCat_Functor] was annotated
    (Instance/Discrete.v, PR "algebraic carriers are sets").  Stripped
    and re-run in a copy of the whole file, the message is now

      The term "tensor_esols_direct V V'" has type
       "ElementSolutionSet@{u_idx u_carrier u_Sets u_idx} (Bilin ... V V')"
      while it is expected to have type
       "ElementSolutionSet@{u_idx' u_carrier u_Sets' u_carrier}
          (Bilin ... V V')"
      (universe inconsistency: Cannot enforce u_idx' = u_carrier because
       u_carrier < u_idx')

    (the generated universe names are rewritten to readable ones; the
    shape, the slots and the final clause are verbatim).

    RECORDED CORRECTION.  An earlier revision quoted this as

      "ElementSolutionSet@{u_obj Set u_Sets u_obj}" against
      "ElementSolutionSet@{u_obj' Set u_Sets' Set}"
      (universe inconsistency: Cannot enforce Set = u_obj' because
       Set < u_obj')

    and glossed it "the INDEX slot (fourth) must be [Set], the ring's
    carrier universe".  THE LITERAL [Set] IS GONE; the gloss was right
    about everything else and is now stated without it: the index slot
    must be the RING'S CARRIER universe, while the index actually supplied
    is a sigma over the objects of [RMod R], one level up.  This is why
    [tensor_via_AFT] takes its solution set as a hypothesis, and the
    reason is a carrier-versus-index wall, not a [Set] floor.

--------
** 否定 1（宇宙）：Mac Lane 的覆盖族被拒绝

2026-09-17 重新测量，在 [DiscreteCat_Functor] 被注释之后（实例/Discrete.v，PR “代数载体是集合”）。在整个文件的副本中剥离并重新运行，现在消息是

术语 “tensor_esols_direct V V'” 的类型为
       “ElementSolutionSet@{u_idx u_carrier u_Sets u_idx} (Bilin ... V V')”
      而期望的类型为
       “ElementSolutionSet@{u_idx' u_carrier u_Sets' u_carrier} (Bilin ... V V')”
      （宇宙不一致：无法强制 u_idx' = u_carrier 因为 u_carrier < u_idx'）

（生成的宇宙名称被重写为可读名称；形状、插槽和最终条款是逐字的）。

已记录的更正。早期版本引用了这个内容为

"ElementSolutionSet@{u_obj 集 u_Sets u_obj}" 与
      "ElementSolutionSet@{u_obj' 集 u_Sets' 集}"
      （宇宙不一致：无法强制 Set = u_obj' 因为
       Set < u_obj'）

并且注释为“索引槽（第四个）必须是 [Set]，环的承载宇宙”。LITERAL [Set] 已经消失；除了它之外，注释对其他所有内容都是正确的，现在省略了它：索引槽必须是环的承载宇宙，而实际提供的索引是 [RMod R] 对象的西格玛，高一层。 这就是为什么 [tensor_via_AFT] 将其解集作为假设，其原因是承载与索引之间的壁，而不是 [Set] 的地板。
*)

Fail Definition n1_direct_esols_refused {R : RingObject}
  (V V' : RModObject R) : Representable (Bilin V V') :=
  representability_theorem (Bilin V V') (RMod_Complete R)
    (Bilin_PreservesImageLimit V V') (tensor_esols_direct V V').

(**
** NEGATIVE 2 (UNIVERSE): the spanning-arrow route is refused too

    RE-MEASURED 2026-09-17, a SECOND time, after [Section GAFTFromSpanning]
    was widened off [Set] in the PR "algebraic carriers are sets".
    Stripped and re-run in a copy of this whole file, the message is now

      The term "RMod R" has type "Category@{u_obj u_hom u_hom}"
      while it is expected to have type "Category@{u_obj' u_hom' u_hom'}"
      (universe inconsistency: Cannot enforce u_hom = u_hom' because
       u_hom < u_obj <= u_hom')

    -- NO literal [Set] anywhere, and a longer chain in the final clause.

    TWO RECORDED CORRECTIONS, in the order they happened.

    (a) The FIRST revision of this probe quoted

      The term "RMod_Complete R" has type
       "Complete.Complete@{Set Set Set u}"
      while it is expected to have type
       "Complete.Complete@{u_obj u_obj Set u_obj}"
      (universe inconsistency: Cannot enforce Set = u_obj because
       Set < u_obj)

    and the refusal then moved EARLIER, to the ambient category argument,
    when [DiscreteCat_Functor] was annotated (Instance/Discrete.v).

    (b) The SECOND revision quoted the category refusal with the expected
    type written "Category@{u_obj' Set Set}" and the clause "Cannot
    enforce u_obj = u_obj' because u_obj' < u_obj", and attributed that
    remaining [Set] to [GAFT_from_spanning]'s OWN section annotation.  THE
    ATTRIBUTION WAS CORRECT AND THE ANNOTATION IS NOW GONE: the section is
    declared over bare categories and the theorem reads
    [Category@{u u0 u0}] / [Category@{u1 u2 u2}] with [u <= u0].  The
    refusal SURVIVES the widening, and the new clause says exactly why --
    the widened theorem wants objects at or below homs, and [RMod R] has
    homs strictly below objects.

    The gloss stands, with the [Set] dropped from it: [spanning_solution_
    set]'s index is at the object universe, so the discrete shape [GAFT]
    takes a limit over is too, while [RMod R]'s homs are below its
    objects.  [GAFT_from_spanning] is therefore still NOT applicable at
    [RMod R], and Instance/Mod/TensorAFT.v still delivers no adjunction --
    what it now delivers unconditionally is a REPRESENTATION, through
    [representability_theorem] and a different solution set.

--------
** 负 2（宇宙）：跨越箭头路线也被拒绝

2026-09-17，经过第二次重新测量，在 [Section GAFTFromSpanning] 从 [Set] 扩展后，在 PR “代数承载体是集合” 中。已在该文件的副本中剥离并重新运行，现在的消息是

术语“RMod R”的类型是“Category@{u_obj u_hom u_hom}”，而预期的类型是“Category@{u_obj' u_hom' u_hom'}”（宇宙不一致：无法强制 u_hom = u_hom' 因为 u_hom < u_obj <= u_hom'）

-- 最后一句中不要出现任何字面上的 [Set]，并且链条更长。

两个记录的更正，按发生的顺序。

(a) 该探测器的第一次修订引用

术语 "RMod_Complete R" 的类型为
       "Complete.Complete@{Set Set Set u}"
      而期望的类型为
       "Complete.Complete@{u_obj u_obj Set u_obj}"
      （宇宙不一致：无法强制 Set = u_obj 因为
       Set < u_obj）

然后拒绝移动得更早，到了环境类别参数，当 [DiscreteCat_Functor] 被标注时（Instance/Discrete.v）。

(b) 第二次修订引用了类别拒绝，期望类型写为 "Category@{u_obj' Set Set}"，并且包含子句 "Cannot enforce u_obj = u_obj' because u_obj' < u_obj"，并将剩余的 [Set] 归因于 [GAFT_from_spanning] 的自有章节注释。归因是正确的，而且注释现在已经消失：该章节声明的是裸类别，定理为 [Category@{u u0 u0}] / [Category@{u1 u2 u2}] 并含 [u <= u0]。拒绝在扩展中仍然存在，而新子句确切说明了原因——扩展后的定理要求对象位于或低于同态，而 [RMod R] 的同态严格低于对象。

这个注释仍然有效，其中的 [Set] 已被去除：[spanning_solution_set] 的索引处于对象宇宙，因此离散形状 [GAFT] 所取的极限也在其中，而 [RMod R] 的 Hom 在其对象之下。因此，[GAFT_from_spanning] 在 [RMod R] 处仍然不可应用，而 Instance/Mod/TensorAFT.v 仍然没有提供伴随——它现在无条件提供的是一个 REPRESENTATION，通过 [representability_theorem] 和一个不同的解集。
*)

Fail Definition n2_gaft_from_spanning_refused {R : RingObject}
  (V V' : RModObject R) (HWP : @HasWidePullbacks (RMod R)) :=
  @GAFT_from_spanning (RMod R) Sets (Bilin V V') HWP
    (Bilin_PreservesWidePullbacks V V') (RMod_Complete R)
    (Bilin_PreservesImageLimit V V').

(**
** NEGATIVE 3 (UNIVERSE): the same at [Ab], for Exercise 3

    RE-MEASURED 2026-09-17, by stripping this section's [Fail] in a copy of
    this WHOLE file and reading the first error.  The message is now

      The term "bal_esols_direct N M" has type
       "ElementSolutionSet@{u_idx u_carrier u_Sets u_idx}
          (BalBiadd ... N M)"
      while it is expected to have type
       "ElementSolutionSet@{u_a u_b u_Sets' u_b} (BalBiadd ... N M)"
      (universe inconsistency: Cannot enforce u_a = u_b because
       u_b < u_a)

    Six generated universes appear, and the substitution above is
    positional and injective: [u_idx]/[u_carrier]/[u_Sets] are the three
    distinct levels of the ACTUAL type (the first and fourth slots share
    [u_idx]), and [u_a]/[u_b]/[u_Sets'] the three of the EXPECTED type (the
    second and fourth share [u_b]).  The third slot is its own universe on
    both sides and takes no part in the clause.

    RECORDED CORRECTIONS, both to earlier revisions of this paragraph.
    First, the expected type was once quoted as
    "ElementSolutionSet@{u_obj' Set u_obj' Set}" and the clause as
    "Cannot enforce Set = u_obj' because Set < u_obj'".  The literal [Set]
    is gone -- it was Instance/Discrete.v's minimization, repaired in the
    PR "algebraic carriers are sets" (2026-09-17).  Second, a revision of
    that repair mapped two distinct universes onto one readable name in
    each type and glossed the refusal as "the first and third slots want
    the same level as the second and fourth".  As measured that gloss is
    false: the inconsistency is between the FIRST slot and the level
    filling the second and fourth, the supplied index sitting strictly
    above it.  The refusal is unchanged in substance either way.

    So Exercise 3's AFT clause is conditional for exactly the reason the
    commutative one is.

--------
** 否定 3（宇宙）：与 [Ab] 相同，用于练习 3

重新测量 2026-09-17，通过在本整个文件的副本中剥离本节的 [Fail] 并读取第一个错误。消息现在是

术语 "bal_esols_direct N M" 的类型为
       "ElementSolutionSet@{u_idx u_carrier u_Sets u_idx} (BalBiadd ... N M)"
      而其预期类型为
       "ElementSolutionSet@{u_a u_b u_Sets' u_b} (BalBiadd ... N M)"
      （宇宙不一致：无法强制 u_a = u_b 因为 u_b < u_a）

六个生成的宇宙出现，上述替换是位置性的且单射的：[u_idx]/[u_carrier]/[u_Sets] 是 ACTUAL 类型的三个不同层次（第一个和第四个位置共享 [u_idx]），[u_a]/[u_b]/[u_Sets'] 是 EXPECTED 类型的三个层次（第二个和第四个位置共享 [u_b]）。第三个位置在双方都是它自己的宇宙，并且不参与该子句。

已记录的更正，针对本段的早期修订。
首先，预期类型曾被引用为“ElementSolutionSet@{u_obj' Set u_obj' Set}”，条款为“无法强制 Set = u_obj' 因为 Set < u_obj'”。字面上的 [Set] 已不存在——它是 Instance/Discrete.v 的最小化内容，在 PR “代数载体是集合”（2026-09-17）中已修复。其次，对该修复的修改将两个不同的宇宙映射到每种类型中的一个可读名称，并将拒绝解释为 “第一和第三槽希望与第二和第四槽相同的级别”。根据测量，该解释是错误的：不一致在于第一槽与填充第二和第四槽的级别之间，所提供的索引严格高于它。无论哪种方式，拒绝在实质上没有改变。

所以练习3的AFT条款是有条件的，原因正是交换条款的原因。
*)

Fail Definition n3_bal_direct_esols_refused {X : RingObject}
  (N : RModObject (Ring_op X)) (M : RModObject X) :
  Representable (BalBiadd N M) :=
  bal_tensor_via_AFT_of_esols N M (bal_esols_direct N M).

(**
** Former NEGATIVE 4: the [Set] pin on the ring's carrier, now lifted

    RECORDED CORRECTION.  An earlier revision read: "NEGATIVE 4
    (UNIVERSE): the [Set] pin on the ring's carrier.  [tensor_via_AFT]
    elaborates only with the ring's carrier universe at [Set].  A ring
    declared strictly above [Set] is refused; the control immediately
    below, at an unconstrained ring, is accepted.  Stripped and re-run,
    the message is

      The term "Vu" has type "RModObject@{... pra prb prc} Ru"
      while it is expected to have type
       "RModObject@{... Set Set ... Set ...} ?R"
      (universe inconsistency: Cannot enforce Set = pra)"

    That [Set] was a universe-minimization artifact of Instance/Discrete.v's
    unannotated [DiscreteCat_Functor], reaching [representability_theorem]
    through [Complete] and [Limit].  Annotated in the PR "algebraic
    carriers are sets" (2026-09-17), Instance/Discrete.v, it is gone,
    and [tensor_via_AFT] elaborates over a ring whose carrier universe is
    declared strictly above [Set].  The line is kept as a positive control
    at exactly the levels that used to refuse it, and the declaration is
    made on the CARRIER slot -- [RingObject]'s second, as the note on the
    section below measures -- so that it is the positive half of the side
    condition NEGATIVE 8 refuses, and not a weaker statement about the
    record's own level.

    THE WALL OF NEGATIVES 1-3 IS NOT LIFTED BY THIS.  Those three are
    carrier-versus-index refusals, and they survive with the literal [Set]
    removed from their messages; their quoted texts above were re-measured
    after the annotation by stripping each [Fail] in a copy of this whole
    file.

--------
** 前负极4：环形载体上的[Set]引脚，现在已移除

已记录更正。早期的修订版本写道：“负4（宇宙）：环载体上的 [Set] 引脚。[tensor_via_AFT] 仅在 [Set] 的环载体宇宙中展开。严格声明高于 [Set] 的环会被拒绝；紧接在下方的、在无约束环上的控制会被接受。剥离后重新运行，消息为

术语“Vu”的类型为“RModObject@{... pra prb prc} Ru”，而期望的类型为“RModObject@{... Set Set ... Set ...} ?R”（宇宙不一致：无法强制 Set = pra）

那个 [Set] 是 Instance/Discrete.v 中未注释的 [DiscreteCat_Functor] 的宇宙最小化工件，通过 [Complete] 和 [Limit] 到达 [representability_theorem]。在 PR “代数载体是集合”（2026-09-17）的 Instance/Discrete.v 中进行了注释，它已经消失，而 [tensor_via_AFT] 在一个载体宇宙声明严格高于 [Set] 的环上进行了详细说明。该行被保留作为正向控制，正好在以前拒绝它的级别上，并且声明是在 CARRIER 插槽上进行的——正如下面部分的注释所测量的，这是 [RingObject] 的第二次——以便它成为侧条件 NEGATIVE 8 拒绝的正向一半，而不是关于记录自身级别的较弱声明。

消极障碍1-3并未因此解除。这三者是承运人与索引的拒绝，即使去掉他们信息中的字面[Set]也依然存在；上面引用的文本是在标注之后重新测量的，通过在该整份文件的副本中去掉每一个[Fail]。
*)

Section SetPin.

Universes pra prb prc.

(*
The CARRIER is [RingObject]'s SECOND slot, not its first: measured with
   [Context (Rr : RingObject@{pa pb pc})] and
   [Definition t : Type := carrier (rig_setoid Rr)], whose block is
   [pb <= pa / pb <= u / pc <= pa] -- so the carrier's level is [pb] and
   the first slot is the record's own.  An earlier revision of this section
   declared [Constraint Set < pra] and the prose below called that the
   carrier; [Set < pra] is a strictly WEAKER declaration, and is implied by
   the one made here ([tensor_via_AFT] carries carrier <= record).  Fixed in
   the PR "algebraic carriers are sets" (2026-09-17), so that this positive
   control and NEGATIVE 8's [Constraint pb = Set] speak about the same
   slot.

--------
载体是 [RingObject] 的第二个槽，而不是第一个槽：通过 [Context (Rr : RingObject@{pa pb pc})] 和 [Definition t : Type := carrier (rig_setoid Rr)] 测量，其块是 [pb <= pa / pb <= u / pc <= pa] ——因此载体的级别是 [pb]，第一个槽是记录本身。此部分的早期版本声明了 [Constraint Set < pra]，下面的文字称其为载体；[Set < pra] 是一个严格较弱的声明，并且可以通过此处所作的声明（[tensor_via_AFT] 携带载体 <= 记录）推导出。在 PR “代数载体是集合”（2026-09-17）中已修复，因此这个正向控制和 NEGATIVE 8 的 [Constraint pb = Set] 指的是同一个槽。
*)
Constraint Set < prb.

Context (Ru : RingObject@{pra prb prc}).
Context (Vu Vu' : RModObject Ru).

Check (tensor_via_AFT Vu Vu').

End SetPin.

Check (fun (Ru : RingObject) (V V' : RModObject Ru) => tensor_via_AFT V V').

(**
** NEGATIVE 5 (CONVERSION): the object comparison is `≅`, not [eq_refl]

    The adjoint functor theorem builds its representing object as a limit
    inside the comma category; [TensorMod] is a quotient of formal terms.
    [tensor_AFT_iso] compares them at `≅`, and that is all that holds.  The
    control is [c_repr_of_UE_obj] above, which IS [eq_refl].

--------
** 负五（转换）：对象比较是 `≅`，不是 [eq_refl]

伴随定理将其表示对象构建为逗号范畴中的一个极限；[TensorMod] 是形式项的一个商。[tensor_AFT_iso] 在 `≅` 下比较它们，这就是全部成立的内容。上面的控制是 [c_repr_of_UE_obj]，它就是 [eq_refl]。
*)

Fail Example n5_aft_object_not_definitional {R : RingObject}
  (V V' : RModObject R) (E : ElementSolutionSet (Bilin V V')) :
  @repr_obj (RMod R) (Bilin V V') (tensor_via_AFT_of_esols V V' E)
    = TensorMod V V' := eq_refl.

(**
** NEGATIVE 6 (CONVERSION): the circular continuity term is not the one
       delivered

    [preserves_image_of_representable (tensor_repr_of_UE V V')]
    (Adjunction/Representability/Sets.v) inhabits the same type as
    [Bilin_PreservesImageLimit], and is checked as a control above -- but it
    derives the theorem's hypothesis from the very tensor the theorem is
    meant to construct, which is the circularity Instance/Ab/Limit.v
    and Instance/Grp/FreeAFT.v name.  The delivered term is a
    DIFFERENT one, built elementwise over the created limits of
    Instance/Mod/Limit.v, and this pins that the two are not the same
    term.

--------
** 负数 6（转换）：圆形连续项不是交付的项

[preserves_image_of_representable (tensor_repr_of_UE V V')]（Adjunction/Representability/Sets.v）属于与 [Bilin_PreservesImageLimit] 相同的类型，并且在上面的控制中已经检查过——但是它是从定理要构造的张量本身推导出定理的假设的，这是循环的 Instance/Ab/Limit.v 和 Instance/Grp/FreeAFT.v 名称。交付的项是不同的一个，是在 Instance/Mod/Limit.v 创建的极限上逐元素构建的，这说明两者不是相同的项。
*)

Fail Example n6_circular_route_is_a_different_term {R : RingObject}
  (V V' : RModObject R) :
  @Bilin_PreservesImageLimit R V V'
    = preserves_image_of_representable (tensor_repr_of_UE V V') := eq_refl.

(**
** NEGATIVE 7 (ARGUMENT NAME): [MGen]'s predicate is positional

    Instance/Mod/Spanning.v's [MGen] takes its predicate as an EXPLICIT
    section variable, so the constructors do not answer to it by name.  The
    control is the same application written positionally.

--------
** 负 7（参数名称）：[MGen] 的谓词是位置性的

    Instance/Mod/Spanning.v 的 [MGen] 将其谓词作为显式段变量，因此构造函数不会按名称响应它。控制是相同的应用，只是以位置方式编写。
*)

Section GenArgumentName.

Context {R : RingObject}.
Context (V V' : RModObject R).

Check (fun (a : carrier (cmon_setoid (TensorMod V V')))
           (Ha : rbl_image (@tensor_gen R V V') a) =>
         mgen_base (rbl_image (@tensor_gen R V V')) a Ha).

Fail Check (fun (a : carrier (cmon_setoid (TensorMod V V')))
                (Ha : rbl_image (@tensor_gen R V V') a) =>
              mgen_base (P := rbl_image (@tensor_gen R V V')) a Ha).

End GenArgumentName.

(**
** NEGATIVE 8 (UNIVERSE): the new side condition, [Set < carrier]

    THE ONE PRICE THE UNCONDITIONAL CONSTRUCTION PAYS, and it is pinned
    here rather than only stated.  The index is a sigma over a
    [Prop]-valued relation; the sort of [Prop] is [Set+1]; identifying the
    index universe with the ring's carrier universe therefore puts the
    carrier strictly above [Set].  A ring whose carrier universe IS [Set]
    is refused by the unconditional form and ACCEPTED by the conditional
    one, which is what makes this a side condition of the new solution set
    and not of the theorem.

    Measured, [About] under [Set Printing Universes], side by side:

      tensor_via_AFT@{…} : ∀ {R : RingObject@{u10 u2 u11}} …
      (* … Set < u2 / u2 < u0 / u2 < u1 …

--------
** 负 8（宇宙）：新的附加条件，[Set < carrier]

    无条件构造所付出的唯一代价，并且它在这里被固定，而不仅仅是陈述。索引是一个 [Prop] 值关系上的 sigma；[Prop] 的类型是 [Set+1]；因此将索引宇宙与环的承载宇宙认同，会将承载层严格置于 [Set] 之上。一个承载宇宙为 [Set] 的环会被无条件形式拒绝，而被有条件形式接受，这就是为什么这是新解集的附加条件，而不是定理的附加条件。

    在 [Set Printing Universes] 下测量的 [About]，并排比较：

      tensor_via_AFT@{…} : ∀ {R : RingObject@{u10 u2 u11}} …
      (* … Set < u2 / u2 < u0 / u2 < u1 …
*)

      tensor_via_AFT_of_esols@{…} : ∀ {R : RingObject@{u13 u2 u14}} …
      (* … Set < u0 / Set < u11 / u2 < u0 / u2 < u1 / u2 < u11 … *)

    -- [u2] is the ring's carrier slot in both, and only the unconditional
    form bounds it.  Stripped and re-run in a copy of this whole file, the
    refusal is

      The term "Vs" has type "RModObject Rs" while it is expected to have
      type "obj[RMod ?R]"
      (universe inconsistency: Cannot enforce u_carrier = u_index because
       u_carrier < u_index)

    with [u_carrier] the section's own [Set]-identified universe.

    AT [Ab], EXERCISE 3 PAYS NOTHING NEW, measured the same way: the
    constraint block of [bal_tensor_via_AFT] gains exactly one line over
    [bal_tensor_via_AFT_of_esols]'s, [Set < Projections.u0], a bound on a
    stdlib constant, and NO new bound on the ring's carrier slot.  The
    [Set < u0] the two share is one the conditional already carried.  The
    asymmetry is real and is not explained here. *)

Section SetCarrierPin.

Universes pa pb pc.
Constraint pb = Set.

Context (Rs : RingObject@{pa pb pc}).
Context (Vs Vs' : RModObject Rs).

(* THE CONTROL: the conditional form elaborates at this very ring. / 控制：条件形式就在这个环节展开。 *)
Definition p449_cond_at_set_carrier
  (E : ElementSolutionSet (Bilin Vs Vs')) : Representable (Bilin Vs Vs') :=
  tensor_via_AFT_of_esols Vs Vs' E.

(* THE NEGATIVE: the unconditional one does not. / 消极面：无条件的人不会。 *)
Fail Definition p449_uncond_at_set_carrier :
  Representable (Bilin Vs Vs') := tensor_via_AFT Vs Vs'.

End SetCarrierPin.
