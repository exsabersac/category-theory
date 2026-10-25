Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.

Generalizable All Variables.

(** * Probe: the strength boundaries of the (co)limit reductions / * 探测：(余)极限约化的强度边界 *)

(*
Guard file for Structure/Pullback/Reduction.v and
   Structure/Pullback/Wide.v, in the Test/ProbeFunnyPoly.v convention.

   Both target files carry measurements of their own; this file is what
   makes those measurements GUARDS.  The distinction matters and is the
   reason this file exists: Reduction.v states seven negatives in-file,
   but an in-file [Fail] with no instrument check and no control can go
   vacuously green after a rename -- it then reports "still refuted" when
   what actually happened is that the statement stopped elaborating for an
   unrelated reason.  Wide.v ships NO [Fail] at all; its refutations and
   its universe measurements were reported by measurement only, and are
   pinned here.

   Every negative below is paired with a positive control that NAMES ITS
   OWN CONSTANTS.  The pairing was verified by RENAME SIMULATION: each
   negative was copied to a scratch file with one constant renamed, and
   the scratch file was confirmed to STOP COMPILING -- so a rename breaks
   this file loudly instead of turning a [Fail] vacuously green.

   THAT GUARANTEE WAS NOT TRUE WHEN THIS FILE WAS FIRST WRITTEN, and the
   failure is recorded here rather than quietly repaired.  The original
   simulation covered only the nine constants the controls happened to
   name; an independent audit re-ran it over the constants appearing in
   the NEGATIVES and found [ml_right], [HasCoequalizers] and
   [HasEqualizers] occurring in no control at all, so renaming any of them
   left this file compiling and the corresponding negative vacuously
   green.  Controls for all three were added below.  This is the same
   defect family that two earlier probe files in this tree shipped with.

   The import list is the UNION of the two targets' import lists, in
   dependency order.  A short prefix is what makes a probe pass for the
   wrong reason.

   The two KINDS of negative are kept lexically apart, because they fail
   for different reasons and must not be read as one thing:

     - CONVERSION negatives ([Fail Definition ... := eq_refl]) -- the two
       sides are well-typed and simply do not convert.
     - FORMABILITY negatives ([Fail Check ...]) -- the equation cannot be
       STATED at all, because the two sides do not even have the same
       type.

   Each negative was stripped of its [Fail] once and the resulting message
   inspected; the kind recorded beside it is what the compiler actually
   said, not what was expected.

--------
用于 Structure/Pullback/Reduction.v 和 Structure/Pullback/Wide.v 的守护文件，遵循 Test/ProbeFunnyPoly.v 的约定。

两个目标文件各自都携带自己的测量；这个文件就是使这些测量成为守卫的原因。这个区别很重要，也是这个文件存在的原因：Reduction.v 在文件中声明了七个否定，但一个文件内的 [Fail] 没有仪器检查也没有控制，在重命名后可以徒然变成绿色——它随后报告“仍被驳斥”，而实际上发生的是该语句因无关原因停止了展开。Wide.v 根本没有提供任何 [Fail]；它的驳斥和它的宇宙测量都是仅通过测量报告的，并且在这里固定。

下面的每个负样本都配有一个正对照，正对照会命名其自身的常量。配对通过重命名模拟进行了验证：每个负样本都被复制到一个临时文件中，并重命名了一个常量，确认临时文件无法编译——因此重命名会明显破坏该文件，而不会让 [Fail] 空泛地显示为通过。

当这个文件最初编写时，这个保证并不真实，并且故障被记录在这里，而不是悄悄修复。最初的模拟仅覆盖了控件碰巧命名的九个常量；独立审计在NEGATIVES中出现的常量上重新运行后，发现[ml_right]、[HasCoequalizers]和[HasEqualizers]根本没有出现在任何控件中，因此重命名其中任何一个都不会影响此文件的编译，相应的负结果也显得无条件为绿色。下面添加了针对这三个的控件。这与该树中两个早期探测文件中的缺陷系列相同。

导入列表是两个目标的导入列表的联合，按依赖顺序排列。短前缀是使探测因错误原因通过的原因。

这两种否定在词汇上是分开的，因为它们失败的原因不同，不能被视为一回事：

- 转换负例 ([Fail Definition ... := eq_refl]) —— 两边类型正确，但就是无法转换。
- 可形成性负例 ([Fail Check ...]) —— 等式根本无法表示，因为两边的类型甚至不相同。

每个负面都被去掉了它的 [Fail]，然后检查了生成的消息；记录在旁边的类型是编译器实际的输出，而不是预期的结果。
*)

(**
** Instrument check

    A [Fail] that must itself fail.  Without this, a globally broken
    [Fail] vernacular would silently green every negative below.  This is
    the INSTRUMENT, not one of the eight negatives -- an earlier draft
    counted it as a ninth.

--------
** 仪器检查

    一个必须本身失效的 [Fail]。没有它，一个全球破损的
    [Fail] 术语将默默地让下面的每个否定都通过。 这是
    仪器，不是八个否定之一——早期草稿将其算作第九个。
*)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(**
** Section (D): Mac Lane's and Awodey's squares are DIFFERENT

    Issue #326's body asserts that Mac Lane's Exercise 9 and the
    Awodey/Riehl construction are "the same square read the other way".
    They are not, and these probes are what pin that.  Mac Lane pulls back
    [⟨id,f⟩] and [⟨id,g⟩], both issuing from [x], over [x × y]; Awodey and
    Riehl pull the diagonal [y ~> y × y] back along [⟨f,g⟩ : x ~> y × y].
    Different codomain, and legs from different objects.

    What IS true -- and is proved in Reduction.v, not merely probed here
    -- is the weaker statement that the two vertices are canonically
    isomorphic AS EQUALIZERS ([maclane_awodey_iso],
    [maclane_awodey_iso_commutes]).  These negatives bound that result
    from below; they do NOT assert that no cospan isomorphism exists at
    particular [f] and [g], which is a question this file does not
    settle.

--------
** 第（D）节：Mac Lane 的方图与 Awodey 的方图是不同的

第 #326 号议题的正文断言 Mac Lane 的练习 9 与 Awodey/Riehl 的构造是“同一个方图只是读法不同”。它们并不是相同的，这些探针正是证明这一点的工具。Mac Lane 将 [x] 发出的 [⟨id,f⟩] 和 [⟨id,g⟩] 拉回至 [x × y] 上；而 Awodey 和 Riehl 则将对角线 [y ~> y × y] 沿 [⟨f,g⟩ : x ~> y × y] 拉回。目标对象不同，且边来自不同的对象。

真正正确的——并且在 Reduction.v 中得到了证明，而不仅仅是在此探查——是一个较弱的陈述，即这两个顶点作为等化器（[maclane_awodey_iso]、[maclane_awodey_iso_commutes]）是典型同构的。这些否定结果从下方限定了该结论；它们并没有断言在特定的 [f] 和 [g] 上不存在共跨同构，这个文件没有解决这个问题。
*)

Section DConversion.

Context {C : Category}.
Context `{@Cartesian C}.
Context {x y : C}.
Context (f g : x ~> y).

(*
CONVERSION negative.  Stripped, this reports a unification failure
   between the two product objects.

--------
转换失败。简化后，这报告了两个产品对象之间的统一失败。
*)
Fail Definition probe_ml_aw_codomain :
  (x × y)%object = (y × y)%object := eq_refl.

(*
Positive control, naming its own constants: the degenerate
   instantiation DOES convert, so the negative above is about the two
   codomains and not about [%object] notation failing to elaborate.

--------
正控制，自行命名其常量：退化实例化确实会转换，因此上述否定是关于两个余域的，而不是关于 [%object] 记法无法展开。
*)
Definition probe_pos_codomain_degenerate :
  (x × x)%object = (x × x)%object := eq_refl.

(*
CONVERSION negatives on the (A)/(B) round trips: both hold at [≈] and
   neither at [=].

--------
(A)/(B) 往返转换的负面情况：两者都保持在 [≈]，而都不保持在 [=]。
*)
Fail Definition probe_equalizer_pullback_round {E : C} (e : E ~> x × y) :
  (exl ∘ e) △ (exr ∘ e) = e := eq_refl.

Fail Definition probe_pullback_equalizer_round {P : C}
     (p1 : P ~> x) (p2 : P ~> y) : exl ∘ (p1 △ p2) = p1 := eq_refl.

(*
Positive control naming Reduction.v's own constant: the first round
   trip does hold at [≈].  If [equalizer_pullback_round] is renamed or
   changes statement, this line fails to compile.

--------
正向控制命名 Reduction.v 自己的常量：第一轮往返在 [≈] 上有效。如果 [equalizer_pullback_round] 被重命名或改变语句，该行将无法编译。
*)
Definition probe_pos_round_up_to_equiv {E : C} (e : E ~> x × y) :
  (exl ∘ e) △ (exr ∘ e) ≈ e := equalizer_pullback_round E e.

End DConversion.

Section DFormability.

Context {C : Category}.
Context `{@Cartesian C}.
Context {x y : C}.
Context (f g : x ~> y).

(*
FORMABILITY negatives -- a DIFFERENT KIND from the conversion ones
   above, and the sharper half of the (D) finding.  Stripped, these do not
   report a failed unification of two terms; they report a TYPE MISMATCH,
   e.g. that [aw_pair f g] has type [x ~> y × y] where [x ~> x × y] was
   expected.  The comparison cannot be stated, so "these squares are not
   convertible" understates the situation.

--------
可塑性否定 —— 与上面提到的转换类型不同，是（D）发现中更尖锐的一部分。去掉修饰后，这些并不报告两个项的统一失败；它们报告的是类型不匹配，例如 [aw_pair f g] 的类型是 [x ~> y × y]，而预期类型是 [x ~> x × y]。无法进行比较，因此“这些平方不可转换”低估了实际情况。
*)
Fail Check (@ml_left C _ x y f = @aw_pair C _ x y f g).

Fail Check (@ml_right C _ x y g = @aw_diag C _ y).

(*
Positive controls naming their own constants: each leg IS statable
   against itself, so the failures above are about the two constructions
   and not about [ml_left]/[aw_pair] being unusable names.  [ml_right] and
   [aw_diag] get their own controls too -- an earlier version of this file
   named them ONLY inside the [Fail Check] above, so a rename of either
   would have turned that negative vacuously green.  An independent audit
   caught it; the two lines below are the repair.

--------
正向控制为其自身常量命名：每条腿都可以对自己进行说明，因此上面的失败是关于这两种构造的，而不是关于 [ml_left]/[aw_pair] 是不可用名称。[ml_right] 和 [aw_diag] 也有它们自己的控制——该文件的早期版本只在上面的 [Fail Check] 中命名它们，因此重命名其中任何一个都会使那个负向测试虚假变绿。独立审计发现了这个问题；下面的两行是修复。
*)
Check (@ml_left C _ x y f = @ml_left C _ x y f).
Check (@aw_pair C _ x y f g = @aw_pair C _ x y f g).
Check (@ml_right C _ x y g = @ml_right C _ x y g).
Check (@aw_diag C _ y = @aw_diag C _ y).

(*
Positive control for the one genuine coincidence: at [f := id] the two
   legs DO agree definitionally.  This is [maclane_awodey_degenerate_left]
   restated at the probe level.

--------
对一个真正的巧合的阳性对照：在 [f := id]，两个部分在定义上确实一致。这是在探针层面上重新表述的 [maclane_awodey_degenerate_left]。
*)
Definition probe_pos_degenerate :
  @ml_left C _ x x id = @aw_diag C _ x := eq_refl.

End DFormability.

(**
** Section (F): the duality is not definitional

    [IsCoequalizer] and [IsEqualizer] are distinct record types, so
    neither the predicates nor the classes are related by [eq_refl] --
    however convertible their FIELDS are.  That field convertibility is
    exactly why Reduction.v's bridges need no tactic, so the negative and
    its control together are the whole content of the measurement.

--------
** （F）部分：二元性不是定义性的

[IsCoequalizer] 和 [IsEqualizer] 是不同的记录类型，因此
无论其 FIELDS 能否转换，谓词和类都不通过 [eq_refl] 相关联。 这种字段可转换性正是 Reduction.v 的桥接不需要策略的原因，因此负面及其控制共同构成了测量的全部内容。
*)

Section FDuality.

Context {C : Category}.

(*
CONVERSION negatives.  Stripped, the first reports that [eq_refl] has
   type [HasCoequalizers C = HasCoequalizers C] where
   [HasCoequalizers C = HasEqualizers C^op] was expected -- records are
   nominal.

--------
转换负数。去掉后，最初的报告显示 [eq_refl] 的类型是 [HasCoequalizers C = HasCoequalizers C]，而预期是 [HasCoequalizers C = HasEqualizers C^op] ——记录是名义上的。
*)
Fail Definition probe_HasCoequalizers_is_op :
  HasCoequalizers C = HasEqualizers (C^op) := eq_refl.

Fail Definition probe_IsCoequalizer_is_op {x y : C} (f g : x ~> y)
     (q : C) (e : y ~> q) :
  IsCoequalizer f g q e = @IsEqualizer (C^op) y x f g q e := eq_refl.

(*
Positive control: the FIELD types ARE convertible.  This is what makes
   the bridge a plain [:=], and it is why the negatives above are a fact
   about record nominality rather than about the mathematics.

--------
阳性对照：字段类型是可转换的。这就是使桥接成为一个普通的 [:=] 的原因，也是为什么上面的否定是关于记录名义性而不是关于数学的事实。
*)
Definition probe_pos_cofork_is_fork_eq {x y : C} (f g : x ~> y)
        (q : C) (e : y ~> q) (Hyp : e ∘ f ≈ e ∘ g) :
  f ∘[C^op] e ≈ g ∘[C^op] e := Hyp.

(*
Positive controls naming the two CLASSES themselves.  As with the legs
   above, they previously occurred only inside the [Fail Definition], so a
   rename would have greened that negative vacuously.

--------
阳性对照命名这两个类别本身。与上面的腿一样，它们以前只出现在 [Fail Definition] 内，因此重命名会使那个阴性虚空地变为绿色。
*)
Check (HasCoequalizers C).
Check (HasEqualizers (C^op)).

(*
Positive control naming Reduction.v's own bridge constant, so a rename
   of the bridge breaks this file.

--------
正控制命名 Reduction.v 自身的桥常数，因此重命名桥会导致此文件损坏。
*)
Definition probe_pos_bridge_exists {x y : C} (f g : x ~> y)
        (q : C) (e : y ~> q) (E : IsCoequalizer f g q e) :
  @IsEqualizer (C^op) y x f g q e := IsEqualizer_op_of_IsCoequalizer E.

End FDuality.

(**
** Wide.v: the binary round trip is refuted on the whole record

    Wide.v ships no [Fail] of its own; this is the first place its
    refutation is pinned.  The obstruction is LOCALIZED rather than
    guessed: the [is_pullback_commutes] field DOES convert (the [∀ i j]
    condition iota-reduces at the two literals), so [is_pullback_ump]
    alone blocks the record equality, being rebuilt through a fresh
    [Build_Unique].

--------
** Wide.v：在整个记录上反驳了二进制往返转换

Wide.v 自身不包含任何 [Fail]；这是其反驳首次被固定的位置。阻碍是局部化的，而不是猜测：[is_pullback_commutes] 字段确实会转换（[∀ i j] 条件在两个字面量上进行 iota 简化），因此仅 [is_pullback_ump] 阻止了记录相等，该字段通过新的 [Build_Unique] 重建。
*)

Section WideBinary.

Context {C : Category}.
Context {x y z : C}.
Context (fx : x ~> z) (fy : y ~> z).
Context {P : C} (p1 : P ~> x) (p2 : P ~> y).

(* CONVERSION negative on the whole record. / 整个记录上的转换为阴性。 *)
Fail Definition probe_wide_binary_round
     (Hb : IsPullback fx fy P p1 p2) :
  wide_pullback_binary (binary_wide_pullback Hb) = Hb := eq_refl.

(*
Positive control naming Wide.v's own constants: the round trip IS
   formable and the commuting field does convert, so the negative is
   about [is_pullback_ump] and not about the round trip being ill-typed.

--------
正向控制命名 Wide.v 自身的常量：往返是可形成的，且交换字段确实会转换，所以否定是关于 [is_pullback_ump] 的，而不是关于往返类型错误的。
*)
Check (fun (Hb : IsPullback fx fy P p1 p2) =>
         wide_pullback_binary (binary_wide_pullback Hb)).

End WideBinary.

(**
** Wide.v: the headline is not vacuous

    A positive control for [wide_pullback_product] naming its own
    constant, so that a rename or a statement change breaks this file
    rather than silently leaving the negatives above as the only mention
    of Wide.v.

--------
** Wide.v：标题不是空洞的

[wide_pullback_product] 为其自身命名常量的阳性对照，这样重命名或更改语句会破坏此文件，而不是默默地让上面的反例成为 Wide.v 的唯一提及。
*)

Section WideHeadline.

Context {C : Category}.
Context `{@Terminal C}.
Context {I : Type} (A : I -> C).
Context {P : C} (proj : forall i, P ~> A i).

Check (fun (Hp : IsIndexedProduct A P proj) =>
         wide_pullback_product A P proj Hp).

Check (fun (Hw : IsWidePullback (fun _ : I => one) P proj) =>
         product_wide_pullback A P proj Hw).

End WideHeadline.

(**
** Wide.v's universe claims, shipped as probes

    Wide.v's header states three universe measurements.  They were TRUE
    when written -- an independent audit reproduced all three -- but no
    probe section existed anywhere in the tree, so they were MEASURED and
    not GUARDED, which is precisely the distinction this file exists to
    enforce.  They are shipped here.

    (i) and (ii): the index universe and the OBJECT universe are
    independent.  A single unannotated probe would prove nothing, since
    minimization collapses the levels; these declare them SEPARATELY and
    impose a STRICT inequality in EACH direction, so neither ordering is
    forced.

--------
** Wide.v 的宇宙声明，以探针形式发送

Wide.v 的头部列出了三个宇宙测量值。在编写时它们是真实的——独立审核重现了所有三个——但树中任何地方都不存在探针部分，所以它们是被测量的而非被保护的，这正是该文件存在的意义所在。它们以此方式发送。

(i) 和 (ii)：索引宇宙和 OBJECT 宇宙是独立的。单个未注释的探针无法证明任何事情，因为最小化会将层级折叠；这些测量值分别声明它们，并在每个方向上施加严格不等式，因此不会强制任何排序。
*)

Section WideUniverseIndexBelowObject.
  Universe uo ui uc.
  Constraint uo < ui.
  Constraint ui <= uc.
  Constraint uo <= uc.
  Check IsWidePullback@{ui uc uo uc}.
End WideUniverseIndexBelowObject.

Section WideUniverseObjectBelowIndex.
  Universe uo ui uc.
  Constraint ui < uo.
  Constraint ui <= uc.
  Constraint uo <= uc.
  Check IsWidePullback@{ui uc uo uc}.
End WideUniverseObjectBelowIndex.

(**
(iii) The hom=proof identification is REAL but INHERITED, not
    introduced by Wide.v.  The negative rejects [IsWidePullback] under a
    strict hom<proof constraint -- and the FIRST control shows the DONOR
    [IsIndexedProduct] is rejected just as flatly at the same levels,
    which is what makes "inherited" a measurement rather than an excuse.
    The SECOND control shows a bare hom-setoid statement IS accepted
    there, so the rejection is not an artifact of the constraint block
    being unsatisfiable.

--------
(iii) 同源证明识别是真实的，但属于继承的，而不是由 Wide.v 引入的。负面情况在严格的同源<证明约束下拒绝 [IsWidePullback] —— 而第一次控制显示，供体 [IsIndexedProduct] 在相同级别上也被同样明确地拒绝，这使得“继承”成为一种测量而非借口。第二次控制显示 một 个裸同源集合陈述在那里是被接受的，因此拒绝并不是约束块不可满足的产物。
*)

Section WideUniverseHomProof.
  Universe uh up.
  Constraint uh < up.

  Fail Check IsWidePullback@{uh uh uh up}.

  Fail Check IsIndexedProduct@{uh uh uh up}.

  Check (fun (C : Category@{uh uh up}) (x y : obj[C])
             (g h : x ~{C}~> y) => g ≈ h).
End WideUniverseHomProof.
