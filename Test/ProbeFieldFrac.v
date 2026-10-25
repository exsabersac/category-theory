Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Frac.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Field.
Require Import Category.Instance.Field.Frac.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.

(**
* Boundary probe: what is and is not definitional in the field of
      quotients as a universal arrow

    Companion to Instance/Field/Frac.v (Mac Lane §III.1).  That file
    makes several strength claims — some things hold at Leibniz [=] by
    [eq_refl], one deliberately holds only up to [≈] — and a strength
    claim that lives only in a header is a claim nothing in the build
    would notice losing.  This file pins the boundary in the manner of
    Test/ProbeModTensor.v: **if the [Fail] commands here stop failing,
    this file breaks the build.**

    Both sides are pinned deliberately.  A [Fail] alone proves very
    little — it passes just as happily when the term is ill-typed for
    some unrelated reason, or when a name has been renamed out from
    under it.  So each negative probe is paired with a positive control
    which must SUCCEED, and the controls are the claims themselves.

    The instrument was checked before being trusted: wrapping [Fail]
    around a command that succeeds reports "The command has not
    failed!" and aborts compilation, so [Fail] here is not a no-op.
    Each negative below was also run with the [Fail] stripped and the
    error confirmed to be a genuine unification or typing error rather
    than a syntax, scope or coercion error; the diagnoses are recorded
    beside each probe.  That check earned its keep: the first two
    negatives, run in a file that did not import Instance/Sets, aborted
    with "Illegal application (Non-functional construction)" — the
    [SetoidMorphism]-to-function coercion was simply absent — which
    would have been a FALSE PASS under [Fail].  The import list above
    is therefore the one Instance/Field/Frac.v itself uses.

    The four negatives and their causes:

      - THE EXTENSION'S COMPUTED VALUE IS PINNED.  The extension of
        ℤ ↪ ℚ carries the fraction 1/2 to the rational [1 # 2] at
        Leibniz equality.  The first negative replaces the value with
        [1 # 3], which is simply wrong, and confirms that the [eq_refl]
        in the positive control discriminates at all rather than being
        absorbed by some coercion.

      - AND IT IS PINNED AT LEIBNIZ STRENGTH, NOT UP TO [Qeq].  The
        second negative replaces the value with [2 # 4], which IS [Qeq]
        -equal to the true answer — [q_probe_qeq] proves it, by
        [eq_refl] no less — and is NOT Leibniz-equal to it
        ([q_probe_not_leibniz]).  So this negative is a genuine
        strength boundary and not a second wrong-value probe: it is
        exactly the difference between "the extension computes to the
        rational one half" and "it computes to something equivalent to
        one half", and Instance/Field/Frac.v claims the former.

      - THE TWO FORGETFUL FUNCTORS AGREE ONLY UP TO [≈] ON MORPHISMS.
        [Field_IntDom stab] and [StableField_IntDom] send a morphism of
        [StableField] to [DomHom]s with the SAME underlying map but
        DIFFERENT injectivity proofs — [stab F] against the object's
        own stability datum — and [DomHom] carries that proof as a
        record field, so the two records are distinct terms.  The
        positive control is the [≈] statement, which holds because
        [IntDom]'s hom-setoid compares underlying maps pointwise and
        ignores the proof.  This is the one place in that file where
        strictness was attempted and rejected.

      - ...WHICH IS NOT A GENERIC FACT ABOUT [DomHom] RECORDS.  The
        third positive control is the SAME SHAPE of comparison for
        [IntDom_Dom ◯ StableField_IntDom] against [StableField_Dom],
        and that one IS strict, by [eq_refl]: [IntDom_Dom] forgets
        exactly the injectivity field that was just supplied, so the
        composite reduces to the underlying map on the nose.  Without
        this control the previous negative would say only "records with
        proof fields are rarely convertible"; with it, it says the
        proofs genuinely differ in that one case and not in this one.

      - THE TWO DOMAIN CATEGORIES DIFFER AT THE LEVEL OF TYPES.
        Reduction mod 2 is a morphism of [Dom] (positive control) and
        is not even well-typed as a morphism of [IntDom] (fourth
        negative), [IntDom]'s homs being [DomHom]s, which bundle an
        injectivity datum, and not bare [RigHom]s.  The probe records
        the TYPING half only; the mathematical half — that no [DomHom]
        from ℤ to F₂ exists at all, so the hom-set is empty rather than
        merely differently packaged — is PROVED in
        Instance/Field/Frac.v as [no_DomHom_Z_F2], and a probe would be
        the weaker statement.

--------
* 边界探针：在作为通用箭头的商领域中，什么是定义性的，什么不是

Companion to Instance/Field/Frac.v（Mac Lane §III.1）。该文件提出了几个强度声明——一些内容在 Leibniz [=] 通过 [eq_refl] 成立，有一项故意仅在 [≈] 前成立——而仅存在于头文件中的强度声明是构建过程中不会注意到其丢失的声明。这个文件以 Test/ProbeModTensor.v 的方式固定了边界：**如果这里的 [Fail] 命令不再失败，这个文件将破坏构建。**

双方都是故意固定的。单靠 [Fail] 本身几乎没有什么证明作用——当某个术语由于某种无关的原因类型错误时，或者当某个名称被重新命名而失效时，它同样能顺利通过。因此，每个负面探针都与一个必须成功的正向控制配对，而这些控制就是这些声明本身。

在信任该工具之前已经进行了检查：将 [Fail] 包裹在一个成功的命令周围会报出“命令未失败！”并中止编译，因此这里的 [Fail] 并非无操作。以下每一个负测试也都在去掉 [Fail] 的情况下运行，并确认错误确实是合一或类型错误，而非语法、作用域或强制转换错误；每个探测旁边记录了诊断结果。此检查证明其价值：前两个负测试，在未导入 Instance/Sets 的文件中运行时，以“非法应用（非函数构造）”中止——[SetoidMorphism] 到函数的强制转换根本不存在——如果使用 [Fail]，本应是错误通过。上述导入列表因此为 Instance/Field/Frac.v 自身使用的列表。

四种消极及其原因：

- 扩展的计算值已固定。ℤ ↪ ℚ 的扩展将分数 1/2 带到莱布尼茨等式下的有理数 [1 # 2]。第一个负号将值替换为 [1 # 3]，这是完全错误的，并且证实了在阳性对照中 [eq_refl] 确实能够进行辨别，而不是被某种强制转换吸收。

- 并且它固定在莱布尼茨强度，而不是 [Qeq]。第二个负值将值替换为 [2 # 4]，这就是 [Qeq]——等于真实答案——[q_probe_qeq] 通过 [eq_refl] 证明了这一点——并且并不与其莱布尼茨相等（[q_probe_not_leibniz]）。因此，这个负值是一个真正的强度边界，而不是第二个错误值探测器：它正是“扩展计算为有理的一半”和“它计算为与一半等价的某个值”之间的区别，而 Instance/Field/Frac.v 声称的是前者。

- 这两个健忘函子在态射上仅到 [≈] 一致。[Field_IntDom stab] 和 [StableField_IntDom] 将一个 [StableField] 的态射发送到具有相同底层映射但不同单射性证明的 [DomHom] — [stab F] 针对对象自身的稳定性数据 — 并且 [DomHom] 将该证明作为记录字段，因此这两个记录是不同的项。正控制是 [≈] 语句，它成立，因为 [IntDom] 的同态集族逐点比较底层映射并忽略证明。这是该文件中唯一尝试严格性但被拒绝的地方。

- …这不是关于 [DomHom] 记录的一般性事实。第三个阳性对照是 [IntDom_Dom ◯ StableField_IntDom] 与 [StableField_Dom] 比较的相同形式，而那个对照是严格的，由 [eq_refl] 控制：[IntDom_Dom] 会忘记刚刚提供的注入性字段，因此复合映射精确地归约到基础映射上。没有这个对照，以前的阴性结果只会说“带有证明字段的记录很少可转换”；有了它，它会说明在一种情况下证明确实不同，而在这种情况下则不不同。

- 两个范畴在类型层面上不同。  
  对 2 取模是 [Dom]（正控制）的一个同态，但作为 [IntDom]（第四个负控制）的同态甚至不是良类型的，[IntDom] 的 Hom 是 [DomHom]，它们绑定了一个单射性数据，而不是简单的 [RigHom]。探针只记录类型一半；数学另一半——即不存在从 ℤ 到 F₂ 的 [DomHom]，因此 Hom 集为空，而不仅仅是打包方式不同——在 Instance/Field/Frac.v 中被证明为 [no_DomHom_Z_F2]，探针只会陈述一个较弱的命题。
*)

(** ** The extension's computed value / ** 扩展的计算值 *)

(* Positive control: the claim itself. / 阳性对照：声明本身。 *)
Example frac_extend_half_control :
  rig_map (frac_extend Int_Dom Q_Field ZtoQ_Dom)
    (mk_frac Int_Dom 1%Z 2%Z two_nonzero) = (1 # 2)%Q := eq_refl.

(*
Negative 1 — a wrong value.  Stripped of [Fail] this reports
   "cannot unify" between the extension's value and [1 # 3].

--------
负 1 —— 一个错误的值。去掉 [Fail] 后，这将报告扩展的值与 [1 # 3] 之间“无法统一”。
*)
Fail Example frac_extend_half_wrong :
  rig_map (frac_extend Int_Dom Q_Field ZtoQ_Dom)
    (mk_frac Int_Dom 1%Z 2%Z two_nonzero) = (1 # 3)%Q := eq_refl.

(*
The two controls that make the next negative a strength boundary
   rather than a second wrong value: [2 # 4] is [Qeq]-equal to the true
   answer and is not Leibniz-equal to it.

--------
使下一个负值成为强度边界而不是第二个错误值的两个控制：[2 # 4] 等于 [Qeq]，即等于真实答案，并且不等于莱布尼茨等式下的答案。
*)
Example q_probe_qeq : ((2 # 4) == (1 # 2))%Q := eq_refl.

Example q_probe_not_leibniz : (2 # 4)%Q = (1 # 2)%Q → False.
Proof. discriminate. Qed.

(*
Negative 2 — a [Qeq]-equal but not Leibniz-equal value.  Stripped of
   [Fail] this reports "cannot unify" between the extension's value and
   [2 # 4].

--------
负2 — 一个与 [Qeq] 相等但与莱布尼茨不相等的值。去掉 [Fail] 后，这会报告扩展的值与 [2 # 4] 之间“无法统一”。
*)
Fail Example frac_extend_half_only_up_to_Qeq :
  rig_map (frac_extend Int_Dom Q_Field ZtoQ_Dom)
    (mk_frac Int_Dom 1%Z 2%Z two_nonzero) = (2 # 4)%Q := eq_refl.

(** ** The two forgetful functors into [IntDom] / ** 两个忘记型函子到 [IntDom] *)

(* Positive control: agreement up to ≈ on morphisms. / 阳性对照：关于态射的协议最多≈。 *)
Example field_intdom_agrees_up_to_equiv
  (stab : ∀ F : FieldObject, FieldStableAtZero F) (F K : StableField)
  (f : F ~{StableField}~> K) :
  fmap[Field_IntDom stab] (fmap[Incl Field StableField_Sub] f)
    ≈ fmap[StableField_IntDom] f.
Proof. intro a; simpl; reflexivity. Qed.

(*
Negative 3 — the same agreement at Leibniz equality.  Stripped of
   [Fail] this reports "cannot unify" between the two [DomHom]s, whose
   [dom_map_inj] fields are built from different stability data.

--------
负3——在莱布尼茨等式上相同的协议。去除[Fail]后，这报告了两个[DomHom]之间“无法统一”，它们的[dom_map_inj]字段是由不同的稳定性数据构建的。
*)
Fail Example field_intdom_agrees_strictly
  (stab : ∀ F : FieldObject, FieldStableAtZero F) (F K : StableField)
  (f : F ~{StableField}~> K) :
  fmap[Field_IntDom stab] (fmap[Incl Field StableField_Sub] f)
    = fmap[StableField_IntDom] f := eq_refl.

(*
Positive control: the SAME shape of comparison, one functor along,
   IS strict — so the negative above is not a generic fact about
   proof-carrying records.

--------
阳性对照：比较的相同形状，一个函子沿着进行，严格 — 所以上面的负面并不是关于携带证明的记录的通用事实。
*)
Example intdom_dom_agrees_strictly (F K : StableField)
  (f : F ~{StableField}~> K) :
  fmap[IntDom_Dom] (fmap[StableField_IntDom] f) = fmap[StableField_Dom] f
  := eq_refl.

(** ** Reduction mod 2 lives in [Dom] and not in [IntDom] / ** 模 2 的约简存在于 [Dom] 中，而不在 [IntDom] 中 *)

(* Positive control. / 阳性对照。 *)
Example ZtoF2_is_a_Dom_morphism :
  Int_Dom ~{Dom}~> Field_Dom F2_Field := ZtoF2.

(*
Negative 4 — the same term as a morphism of [IntDom].  Stripped of
   [Fail] this reports that [ZtoF2] has type [Int_Ring ~{Rng}~> F2_Ring]
   while a [DomHom] is expected: a typing error, not a proof obligation.
   That no [DomHom] exists there AT ALL is the theorem
   [no_DomHom_Z_F2].

--------
负 4 —— 与 [IntDom] 的同态项相同。去掉 [Fail] 后，这报告 [ZtoF2] 的类型为 [Int_Ring ~{Rng}~> F2_Ring]，而期望为 [DomHom]：一个类型错误，而非证明义务。那里根本不存在 [DomHom]，这是定理 [no_DomHom_Z_F2]。
*)
Fail Definition ZtoF2_is_not_an_IntDom_morphism :
  Int_Dom ~{IntDom}~> field_dom F2_Field := ZtoF2.
