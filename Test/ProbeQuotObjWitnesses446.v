Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.Pushout.
Require Import Category.Instance.Sets.QuotObj.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Epi.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Quotient.Isomorphism.
Require Import Category.Instance.Grp.QuotObj.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Pushout.
Require Import Category.Instance.FinSet.Regular.
Require Import Category.Instance.FinSet.Subobject.
Require Import Category.Instance.FinSet.QuotObj.

Generalizable All Variables.

(**
* Probe for the three quotient-object witness files

    Mac Lane, "Categories for the Working Mathematician", 2nd ed., §V.7
    Definition 3, printed p. 126.  Issue #446, witness half.  The targets
    are Instance/Sets/QuotObj.v, Instance/Grp/QuotObj.v and
    Instance/FinSet/QuotObj.v.

    The import list above is the UNION of the three targets' own import
    lists, unabbreviated.  A short prefix is what makes a probe pass
    vacuously, so nothing is trimmed even where a require is redundant.

    Each statement asserted below to be refuted has been STRIPPED of its
    refutation keyword in a copy of this WHOLE file, compiled alone, and
    its complete error read: this repo's coqc prints nothing for a
    refutation that holds, so a whole-file rc=0 would establish only THAT
    each command is rejected and never WHY.  Every negative here is
    classified CONVERSION -- "The term eq_refl has type X while it is
    expected to have type Y", with a trailing "(cannot unify A and B)".
    The parenthetical is rendered with the short names in scope, so the
    same refusal prints differently under a different import list.

    The instrument check comes first: a name that does not exist,
    refused for a reason unrelated to any boundary.  Every constant a
    negative names then appears in a positive control outside any
    refutation command, so that a rename cannot leave a negative refused
    for reference-not-found and therefore vacuously green.

--------
* 探查三个商-对象证明文件

Mac Lane，《为工作的数学家准备的范畴论》，第二版，第V.7节，第126页印刷版。问题#446，见证的一半。目标是 Instance/Sets/QuotObj.v、Instance/Grp/QuotObj.v 和 Instance/FinSet/QuotObj.v。

上面的导入列表是三个目标自身导入列表的并集，未缩写。 一个短前缀是让探针无条件通过的原因，因此即使某个 require 多余，也不会进行任何裁剪。

下面每一个被断言为需要驳斥的声明，都在本文件的一个完整副本中被删除了其驳斥关键词，并完整地阅读了其错误：这个仓库的 coqc 对于一个成立的驳斥什么也不打印，所以整个文件的 rc=0 只能说明每条命令都被拒绝，但永远无法说明原因。这里的每一个否定都被归类为 CONVERSION——“项 eq_refl 的类型为 X，而它被期望的类型为 Y”，后面跟着“(cannot unify A and B)”。括号中的内容使用了当前作用域中的简短名称，因此在不同的导入列表下同样的拒绝打印方式可能不同。

仪器检查首先进行：一个不存在的名称，被拒绝的原因与任何边界无关。然后每一个恒定的负名称出现在任何反驳命令之外的正控制中，因此重命名不能使由于未找到引用而被拒绝的负名称留下，因此在形式上是绿色的。
*)

(** ** Instrument check / ** 仪表检查 *)

Fail Check quot_obj_446_no_such_constant.

(** ** Positive controls: every constant the negatives name / ** 阳性对照：每个阴性命名的常数 *)

Check @QuotObj.
Check @SubObj.
Check @SetoidObject.
Check @Sets.
Check @Isomorphism.
Check @to.
Check @quot_cod.
Check @quot_epi.
Check @quot_le.
Check @quot_is_epic.
Check @mk_quot.
Check @quot_meet.
Check @sub_meet.
Check @Sets_HasPushouts.
Check @NatDiscrete.
Check @Sets_Q_parity.
Check @Sets_Q_mod3.
Check @Sets_Q_total.
Check @Sets_quot_epi_surjective.
Check @Sets_quot_of_surjection.
Check @SetsQuotient_QuotObj.
Check @Sets_coimage.
Check @Sets_CoimageOf.
Check @Sets_HasCoimages.
Check @Sets_quot_meet_parity_mod3.
Check @grp_quot_of_normal.
Check @grp_quot_is_quot_by_kernel.
Check @grp_quot_le_of_included.
Check @finset_quot_epi_surjective.
Check @finset_quot_of_surjection.
Check @finset_coimage.
Check @FinSet_CoimageOf.
Check @FinSet_HasCoimages.
Check @finset_merge01.
Check @finset_merge12.
Check @finset_q01.
Check @finset_q12.
Check @finset_q_meet.
Check @fin4_0.
Check @fin4_2.
Check @fin4_3.

(** ** Positive controls for the computing readbacks themselves / ** 用于计算回读本身的阳性对照 *)

(*
The pushout of "identify {0,1}" and "identify {1,2}" over the
   four-element set has TWO classes, by [eq_refl].

--------
"通过 [eq_refl]，将‘identify {0,1}’和‘identify {1,2}’在四元素集合上的推挤有两个类。"
*)
Example p446_meet_two : quot_cod finset_q_meet = 2%nat := eq_refl.

Example p446_meet_merges :
  quot_epi finset_q_meet fin4_0 = quot_epi finset_q_meet fin4_2 := eq_refl.

Example p446_coimage_three :
  quot_cod (finset_coimage finset_merge01) = 3%nat := eq_refl.

(** ** N1 -- the meet has two classes and not three (CONVERSION) / ** N1 -- 比赛有两个组别，而不是三个（转换） *)

(*
Guards [finset_quot_meet_two].  A probe against the right number
   alone would pass for a construction that did not reduce at all; this
   one pins that the number is computed and is 2.

--------
守卫 [finset_quot_meet_two]。仅针对正确的数字进行探测可能被认为是一个根本没有减少的构造；这个探测表明该数字是经过计算的，并且是 2。
*)
Fail Example p446_n1 : quot_cod finset_q_meet = 3%nat := eq_refl.

(** ** N2 -- the meet does not collapse everything (CONVERSION) / ** N2 -- 会面不会使一切塌陷（转换） *)

(*
Guards [finset_quot_meet_separates_0_3] at the strongest reading: 0
   and 3 are not identified even up to conversion.

--------
在最强读数下，守卫 [finset_quot_meet_separates_0_3]：0 和 3 即使经过转换也无法识别。
*)
Fail Example p446_n2 :
  quot_epi finset_q_meet fin4_0 = quot_epi finset_q_meet fin4_3 := eq_refl.

(**
** N3 -- a coimage is smaller than the codomain it is read in
       (CONVERSION)

--------
** N3 -- 共像比它所读的值域小
       （转换）
*)

(*
Guards [finset_coimage_merge01_three]: the coimage of a 4 ↠ 3 map is
   3 and not 4, so the construction is not silently the domain.

--------
Guards [finset_coimage_merge01_three]：4 ↠ 3 映射的余像是 3 而不是 4，所以该构造并不是静默的定义域。
*)
Fail Example p446_n3 :
  quot_cod (finset_coimage finset_merge01) = 4%nat := eq_refl.

Section SetsBoundaries.

Universe o so.
Constraint o < so.

(**
** N4 -- the quotient-object meet is an ≈ and NOT a Leibniz equality
       (CONVERSION)

--------
** N4 -- 商对象的交是一个≈，而不是莱布尼茨等式（转换）
*)

(*
Guards the strength of [Sets_quot_meet_parity_mod3].  [QuotObj]
   inherits [SubObj]'s setoid (Theory/Subobject.v) and has no
   antisymmetry, so the theorem holds at ≈ and the same statement at `=`
   is refused.

--------
保护 [Sets_quot_meet_parity_mod3] 的强度。[QuotObj] 继承了 [SubObj] 的集合（Theory/Subobject.v）并且没有反对称性，所以该定理在 ≈ 下成立，而在 `=` 下相同的陈述被拒绝。
*)
Fail Example p446_n4 :
  @quot_meet Sets@{o so} Sets_HasPushouts NatDiscrete@{o}
    Sets_Q_parity Sets_Q_mod3 = Sets_Q_total := eq_refl.

(** ** N5 -- a quotient object of C is not a subobject of C (CONVERSION) / ** N5 -- C 的商对象不是 C 的子对象（转换） *)

(*
[@QuotObj (C^op) x = @SubObj C x] holds by [eq_refl], C^op^op being C
   on the nose.  Dropping the [^op] must NOT: that is the whole content
   of the definition.

--------
[@QuotObj (C^op) x = @SubObj C x] 由 [eq_refl] 保持，C^op^op 刚好就是 C。删除 [^op] **不得**：这就是定义的全部内容。
*)
Fail Example p446_n5 (X : SetoidObject@{o o}) :
  @QuotObj Sets@{o so} X = @SubObj Sets@{o so} X := eq_refl.

(**
** N6 -- the covariant reading of the setoid is a LEMMA, not a
       conversion (CONVERSION)

--------
** N6 -- 集合的协变读法是一个引理，而不是一个转换
*)

(*
The order [quot_le] unfolds covariantly on the nose, but the SETOID
   does not: [SubObj_Setoid] at [C^op] asks for an isomorphism IN
   [C^op], whose [to] runs the other way.  The covariant spelling below
   is well FORMED at a concrete category -- it elaborates, and the
   refusal is of the [eq_refl] and not of the statement -- so a
   covariant characterization has to be proved, which is what
   Theory/Subobject/Quotient.v's [quot_equiv_iff_iso] does, with its
   corollary [quot_equiv_of_cod_iso] (first proved in the Grp witness
   and lifted at integration) in the direction the Grp witness needs.

--------
序 [quot_le] 在表面上是协变展开的，但 SETOID 并不是：在 [C^op] 处的 [SubObj_Setoid] 需要一个在 [C^op] 中的同构，其 [to] 的方向相反。下面的协变拼写在具体范畴中是良构的——它会展开，而且拒绝的是 [eq_refl] 而不是陈述本身——因此需要证明一个协变的刻画，这正是 Theory/Subobject/Quotient.v 的 [quot_equiv_iff_iso] 所做的，并且它的推论 [quot_equiv_of_cod_iso]（最初在 Grp 证据中被证明，并在集成时提升）是 Grp 证据所需的方向。
*)
Fail Example p446_n6 (X : SetoidObject@{o o})
  (q r : @QuotObj Sets@{o so} X) :
  (q ≈ r) = { i : quot_cod q ≅ quot_cod r & to i ∘ quot_epi q ≈ quot_epi r }
  := eq_refl.

End SetsBoundaries.
