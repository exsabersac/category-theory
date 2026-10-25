(**
* Boundary probe: what is and is not definitional in the tensor
      product of modules

    Companion to Instance/Mod/Tensor.v and Instance/Vect/Tensor.v (Mac
    Lane §III.1, Riehl §2.3).  Those files make several strength claims —
    some things hold at Leibniz [=] or by [eq_refl], others only up to
    [≈] — and a strength claim that lives only in a header is a claim
    nothing in the build would notice losing.  This file pins the
    boundary in the manner of Test/ProbeFreeVect.v: **if the [Fail]
    commands here stop failing, this file breaks the build.**

    Both sides are pinned deliberately.  A [Fail] alone proves very
    little — it passes just as happily when the term is ill-typed for
    some unrelated reason, or when a name has been renamed out from under
    it.  So each negative probe is paired with a positive control which
    must SUCCEED, and the controls are the claims themselves.

    The instrument was checked before being trusted: wrapping [Fail]
    around a command that succeeds reports "The command has not failed!"
    and aborts compilation, so [Fail] here is not a no-op.  Each negative
    below was also run with the [Fail] stripped, and the error confirmed
    to be a genuine unification error rather than a syntax, scope or
    universe error; the diagnoses are recorded beside each probe.

    The four negatives and their causes:

      - THE QUOTIENT IS GENUINE.  Commutativity of a formal sum is a step
        of the generated congruence [mt_eq] and not a definitional
        equality of the underlying inductive: the two formal sums are
        distinct terms of [MTerm].  The positive control is [mte_comm].
        This is what makes the setoid presentation a quotient rather than
        a renaming, and it is why the mediator needs
        [tensor_med_respects] before it is a morphism at all.

      - THE BALANCED LAW IS NOT DEFINITIONAL EITHER.  (r·v) ⊗ w and
        v ⊗ (r·w) are distinct terms even at closed ℤ scalars, where both
        sides' scalar products reduce to numerals; they are identified
        only by [tensor_balanced], which composes the two action rules
        through the formal scalar.  Since it is exactly this law that
        makes the canonical map bilinear in the two-sided sense, the
        probe records that the whole of bilinearity in the second
        variable is quotient content, not computation.

      - THE FACTORIZATION'S VALUE IS ONLY UP TO [≈] WHEN THE TARGET'S
        SETOID SAYS SO.  Over ℤ the mediator's value at a closed
        generator IS a numeral, by [eq_refl] ([probe_med_computes]).
        Over ℚ it is not: [Qmult (1#2) (4#1)] reduces to the
        term [4#2], which is [Qeq]-equal to [2] and not Leibniz-equal to
        it.  The two probes together locate the boundary precisely — it
        is the SCALAR SETOID, not the mediator, that decides.

      - THE TRIANGLE IS AN EQUATION OF SETOIDS, NOT OF RECORDS.
        [fmap[Bilin] (tensor_med β) tensor_gen] and β agree at every
        argument, by [eq_refl] on the VALUE ([probe_triangle_value]), but
        the two [RBilinear] records are not the same term: postcomposition
        rebuilds the four law fields from [Program] obligations, which
        are [Qed]-opaque.  So the universal element's [unique_property]
        is stated, and can only be stated, in the hom-setoid of [Sets].

    Two strict successes ABOUT THE CLASS are pinned as well, because
    they are the unusual ones and a later refactor could silently lose
    them: the universal element's element IS [tensor_gen]
    ([probe_universal_element_is_gen]), and the mediator extracted from
    the class IS the fixpoint [tensor_med] ([probe_factor_is_med]).  Contrast
    Test/ProbeFreeVect.v, where the corresponding data (the counit, the
    free functor's action on arrows) does NOT compute, [ump_universal_arrows]
    being opaque; here the [Unique] record is built directly, so
    [unique_obj] reduces.

--------
* 边界探针：张量积中模块的定义性内容与非定义性内容

这是 Instance/Mod/Tensor.v 和 Instance/Vect/Tensor.v 的配套文件（Mac Lane §III.1，Riehl §2.3）。这些文件提出了几个强度声明——有些内容在 Leibniz [=] 下或者通过 [eq_refl] 成立，其他的则只在 [≈] 下成立——而仅存在于头文件中的强度声明是构建中没人会注意到失效的声明。这个文件以 Test/ProbeFreeVect.v 的方式固定了边界：**如果这里的 [Fail] 命令停止失败，这个文件将破坏构建。**

双方都是故意固定的。单靠 [Fail] 本身几乎证明不了什么——当术语因某些无关原因类型错误，或当名称被重命名而无法识别时，它依然能够顺利通过。因此，每个负面探测都配有一个必须成功的阳性对照，而对照就是这些声明本身。

在被信任之前，该仪器已经过检查：将 [Fail] 包裹在一个成功的命令周围会报告“命令未失败！”并中止编译，因此这里的 [Fail] 不是无操作。下面的每个负面测试也都在去掉 [Fail] 的情况下运行，并确认错误是一个真正的归一化错误，而不是语法、作用域或宇宙错误；每个探测旁边都记录了诊断结果。

四种消极及其原因：

- 商是有效的。形式和的交换性是生成同余 [mt_eq] 的一步，而不是底层归纳的定义性等式：这两个形式和是 [MTerm] 的不同项。正对照是 [mte_comm]。这就是使得集合论展示成为商而不是重命名的原因，也正因如此，中介在成为态射之前需要 [tensor_med_respects]。

- 平衡律也不是定义性的。(r·v) ⊗ w 和 v ⊗ (r·w) 即使在封闭的 ℤ 标量下也是不同的项，这时两边的标量积都化为数字；它们仅通过 [tensor_balanced] 被识别，该规则通过形式标量组合了两个作用规则。由于恰恰是这条律使得典型映射在双边意义下是双线性的，探针记录表明第二变量的整个双线性是商内容，而非计算。

- 因式分解的值仅在目标的集合等价类允许时才达到 [≈]。在 ℤ 上，封闭生成元处中介的值是一个数值，由 [eq_refl]（[probe_med_computes]）给出。在 ℚ 上则不是：[Qmult (1#2) (4#1)] 归约为项 [4#2]，它在 [Qeq] 下等于 [2]，但不与它在莱布尼茨意义下等价。两个探针共同精确定位了边界——决定的是标量集合等价类，而不是中介。

- 三角形是集合同构的方程，而不是记录的方程。  
[fmap[Bilin]（张量_med β）tensor_gen] 和 β 在每一个参数上都一致，根据 [eq_refl] 在 VALUE（[probe_triangle_value]）上，但是两个 [RBilinear] 记录并不是相同的项：后合成通过 [Program] 的义务重建四个律字段，这些义务是 [Qed] 不透明的。所以普遍元素的 [unique_property] 被陈述，并且只能在 [Sets] 的同态集合中陈述。

关于该类的两个严格成功同样被标记，因为它们是不同寻常的，之后的重构可能会悄悄丢失它们：通用元素的元素是 [tensor_gen]（[probe_universal_element_is_gen]），从类中提取的中介者是固定点 [tensor_med]（[probe_factor_is_med]）。对比 Test/ProbeFreeVect.v，其中相应的数据（余单位，自由函子在箭头上的作用）不会计算，[ump_universal_arrows] 是不透明的；这里 [Unique] 记录是直接构建的，所以 [unique_obj] 可以化简。
*)

Require Import Coq.QArith.QArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Universal.Element.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Vect.Tensor.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(*
Index arguments supplied once, as NOTATIONS (so each unfolds to the
   constructor itself) — the device Instance/Mod/Free.v uses for its own
   witnesses; [Local Notation] does not cross files.

--------
索引参数提供一次，作为符号 (因此每个展开为构造函数本身) — 设备 Instance/Mod/Free.v 用于其自身证据的方式；[Local Notation] 不跨文件。
*)
Local Notation zgen  := (@mt_gen Int_Ring Int_RMod Int_RMod).
Local Notation zplus := (@mt_plus Int_Ring Int_RMod Int_RMod).
Local Notation qgen  := (@mt_gen (field_ring Q_Field) Q_Vct Q_Vct).

(**
** Positive control: the mediator computes over ℤ

    [tensor_med] is a [Fixpoint] on formal expressions, so its value on a
    closed expression reduces all the way to a value of the target
    module's carrier.

--------
** 阳性对照：中介在 ℤ 上进行计算

[tensor_med] 是形式表达式上的 [Fixpoint]，因此它在封闭表达式上的值会完全化简为目标模块载体的值。
*)
Example probe_med_computes :
  cmon_map (rm_hom (tensor_med Int_mul_bilinear)) (zgen 2%Z 3%Z) = 6%Z
  := eq_refl.

(**
** Positive control: the class's mediator IS the fixpoint

    [tensor_factor] is [unique_obj] of the [Unique] record supplied to
    [tensor_universal_element], and that record is built directly rather
    than extracted from an opaque proof, so the projection reduces.

--------
** 阳性对照：该类的中介者是不动点

[tensor_factor] 是提供给 [tensor_universal_element] 的 [Unique] 记录的 [unique_obj]，并且该记录是直接构建的，而不是从不透明的证明中提取的，因此投影会化简。
*)
Example probe_factor_is_med :
  tensor_factor Int_mul_bilinear = tensor_med Int_mul_bilinear := eq_refl.

(** ** Positive control: the universal element's element IS ⊗ / ** 阳性对照：通用元素的元素是 ⊗ *)
Example probe_universal_element_is_gen :
  @aue_elem (RMod Int_Ring) (Bilin Int_RMod Int_RMod)
    (TensorMod Int_RMod Int_RMod)
    (tensor_universal_element Int_RMod Int_RMod) = tensor_gen := eq_refl.

(**
** Positive control: the triangle's VALUE computes

    Paired with the fourth negative below: what does not hold at Leibniz
    equality is the equation of RECORDS, not the equation of values.

--------
** 阳性对照：三角形的值进行计算

与下面的第四个阴性配对：在莱布尼茨处不成立的不是数值的等式，而是记录的等式。
*)
Example probe_triangle_value (v w : carrier (cmon_setoid Int_RMod)) :
  rbl_map (fmap[Bilin Int_RMod Int_RMod]
             (tensor_med Int_mul_bilinear) tensor_gen) v w
    = rbl_map Int_mul_bilinear v w := eq_refl.

(**
** Negative: commutativity of a formal sum is not definitional

    The carrier is a plain inductive; commutativity is a constructor of
    the quotienting relation, which is the positive control.

--------
** 负面：形式和的交换性不是定义性的

载体是一个普通的归纳类型；交换性是商关系的一个构造器，这是正面的控制。
*)
Fail Example probe_plus_comm_definitional :
  zplus (zgen 1%Z 1%Z) (zgen 2%Z 2%Z)
    = zplus (zgen 2%Z 2%Z) (zgen 1%Z 1%Z) := eq_refl.

Example probe_plus_comm_up_to_equiv :
  mt_eq (zplus (zgen 1%Z 1%Z) (zgen 2%Z 2%Z))
        (zplus (zgen 2%Z 2%Z) (zgen 1%Z 1%Z)) :=
  mte_comm _ _.

(**
** Negative: the balanced law is not definitional

    3·2 and 3·1 both reduce to numerals here, so the two sides are the
    closed terms 6 ⊗ 1 and 2 ⊗ 3 — distinct constructors' arguments, and
    identified only by [tensor_balanced].

--------
** 否定：平衡律不是定义性的

3·2 和 3·1 在这里都简化为数字，因此两边是封闭项 6 ⊗ 1 和 2 ⊗ 3 —— 不同构造函数的参数，并且仅由 [tensor_balanced] 标识。
*)
Fail Example probe_balanced_definitional :
  zgen 6%Z 1%Z = zgen 2%Z 3%Z := eq_refl.

Example probe_balanced_up_to_equiv :
  mt_eq (zgen 6%Z 1%Z) (zgen 2%Z 3%Z) :=
  @tensor_balanced Int_Ring Int_RMod Int_RMod 3%Z 2%Z 1%Z.

(**
** Negative: over ℚ the mediator's value is only [Qeq]-equal

    [Qmult (1#2) (4#1)] reduces to [4#2].  The scalar setoid, not the
    mediator, is what makes this weaker than the ℤ case above.

--------
** 否定：在 ℚ 上，中介者的值仅为 [Qeq]-相等

[Qmult (1#2) (4#1)] 化简为 [4#2]。是标量集合，而不是中介者，使得这比上面的 ℤ 情况更弱。
*)
Fail Example probe_q_med_definitional :
  cmon_map (rm_hom (tensor_med Q_mul_bilinear)) (qgen (1#2) (4#1)) = 2
  := eq_refl.

Example probe_q_med_up_to_equiv :
  cmon_map (rm_hom (tensor_med Q_mul_bilinear)) (qgen (1#2) (4#1)) ≈ 2.
Proof. exact q_tensor_med_computes. Qed.

(**
** Negative: the triangle is not an equality of records

    Postcomposition rebuilds [RBilinear]'s four law fields from
    [Program] obligations, which are [Qed]-opaque, so the two records
    are distinct terms with equal values.

--------
** 否定：该三角形不是记录的等式

后组合使用 [Program] 义务从 [Qed] 不透明的 [RBilinear] 的四个法律字段重建，因此这两条记录是具有相等值的不同条款。
*)
Fail Example probe_triangle_definitional :
  fmap[Bilin Int_RMod Int_RMod] (tensor_med Int_mul_bilinear) tensor_gen
    = Int_mul_bilinear := eq_refl.

Example probe_triangle_up_to_equiv :
  fmap[Bilin Int_RMod Int_RMod] (tensor_med Int_mul_bilinear) tensor_gen
    ≈ Int_mul_bilinear.
Proof.
  exact (unique_property
           (@aue_universal (RMod Int_Ring) (Bilin Int_RMod Int_RMod)
              (TensorMod Int_RMod Int_RMod)
              (tensor_universal_element Int_RMod Int_RMod)
              Int_RMod Int_mul_bilinear)).
Qed.
